use crate::analysis::{
    GraphColoring, Node, ParNodes, SingleNode, StateType, StaticFSM,
};
use crate::traversal::{
    Action, ConstructVisitor, Named, ParseVal, PassOpt, VisResult, Visitor,
};
use calyx_ir::{self as ir, Nothing, PortParent};
use calyx_ir::{guard, structure, GetAttributes};
use calyx_utils::{CalyxResult, Error};
use core::panic;
use ir::{build_assignments, RRC};
use itertools::Itertools;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::ops::Not;
use std::rc::Rc;

/// Compiles Static Islands
pub struct CompileStatic {
    /// maps original static group names to the corresponding group that has an FSM that reset early
    reset_early_map: HashMap<ir::Id, ir::Id>,
    /// maps group that has an FSM that resets early to its dynamic "wrapper" group name.
    wrapper_map: HashMap<ir::Id, ir::Id>,
    /// maps fsm names to their corresponding signal_reg
    signal_reg_map: HashMap<ir::Id, ir::Id>,
    /// maps reset_early_group names to (fsm == 0, final_fsm_state);
    fsm_info_map:
        HashMap<ir::Id, (ir::Id, ir::Guard<Nothing>, ir::Guard<Nothing>)>,

    /// Command line arguments:
    /// cutoff for one hot encoding
    one_hot_cutoff: u64,
    offload_pause: bool,
}

impl Named for CompileStatic {
    fn name() -> &'static str {
        "compile-static"
    }

    fn description() -> &'static str {
        "compiles static sub-programs into a dynamic group"
    }

    fn opts() -> Vec<PassOpt> {
        vec![PassOpt::new(
            "one-hot-cutoff",
            "The upper limit on the number of states the static FSM must have before we pick binary \
            encoding over one-hot. Defaults to 0 (i.e., always choose binary encoding)",
            ParseVal::Num(0),
            PassOpt::parse_num,
        ),
        PassOpt::new(
            "offload-pause",
            "Whether to pause the static FSM when offloading",
            ParseVal::Bool(false),
            PassOpt::parse_bool,
        )

        ]
    }
}

impl ConstructVisitor for CompileStatic {
    fn from(ctx: &ir::Context) -> CalyxResult<Self> {
        let opts = Self::get_opts(ctx);

        Ok(CompileStatic {
            one_hot_cutoff: opts["one-hot-cutoff"].pos_num().unwrap(),
            offload_pause: opts["offload-pause"].bool(),
            reset_early_map: HashMap::new(),
            wrapper_map: HashMap::new(),
            signal_reg_map: HashMap::new(),
            fsm_info_map: HashMap::new(),
        })
    }

    fn clear_data(&mut self) {
        self.reset_early_map = HashMap::new();
        self.wrapper_map = HashMap::new();
        self.signal_reg_map = HashMap::new();
        self.fsm_info_map = HashMap::new();
    }
}

impl CompileStatic {
    /// Builds a wrapper group for group named group_name using fsm and
    /// and a signal_reg.
    /// Both the group and FSM (and the signal_reg) should already exist.
    /// `add_resetting_logic` is a bool; since the same FSM/signal_reg pairing
    /// may be used for multiple static islands, and we only add resetting logic
    /// for the signal_reg once.
    fn build_wrapper_group(
        fsm_eq_0: ir::Guard<Nothing>,
        fsm_final_state: ir::Guard<Nothing>,
        group_name: &ir::Id,
        signal_reg: ir::RRC<ir::Cell>,
        builder: &mut ir::Builder,
        add_reseting_logic: bool,
    ) -> ir::RRC<ir::Group> {
        // Get the group and fsm necessary to build the wrapper group.
        let early_reset_group = builder
            .component
            .get_groups()
            .find(*group_name)
            .unwrap_or_else(|| {
                unreachable!(
                    "called build_wrapper_group with {}, which is not a group",
                    group_name
                )
            });

        // fsm.out == 0
        structure!( builder;
            let signal_on = constant(1, 1);
            let signal_off = constant(0, 1);
        );
        // Making the rest of the guards guards:
        // signal_reg.out
        let signal_reg_guard: ir::Guard<ir::Nothing> =
            guard!(signal_reg["out"]);
        // !signal_reg.out
        let not_signal_reg = signal_reg_guard.clone().not();
        // fsm.out == 0 & signal_reg.out
        let eq_0_and_signal = fsm_eq_0.clone() & signal_reg_guard;
        // fsm.out == 0 & ! signal_reg.out
        let final_state_not_signal = fsm_final_state & not_signal_reg;
        // create the wrapper group for early_reset_group
        let mut wrapper_name = group_name.clone().to_string();
        wrapper_name.insert_str(0, "wrapper_");
        let g = builder.add_group(wrapper_name);
        let group_assigns = build_assignments!(
          builder;
          // early_reset_group[go] = 1'd1
          early_reset_group["go"] = ? signal_on["out"];
          // when fsm == 0, and !signal_reg, then set signal_reg to high
          signal_reg["write_en"] = final_state_not_signal ? signal_on["out"];
          signal_reg["in"] =  final_state_not_signal ? signal_on["out"];
          // group[done] = fsm.out == 0 & signal_reg.out ? 1'd1
          g["done"] = eq_0_and_signal ? signal_on["out"];
        );
        if add_reseting_logic {
            // continuous assignments to reset signal_reg back to 0 when the wrapper is done
            let continuous_assigns = build_assignments!(
                builder;
                // when (fsm == 0 & signal_reg is high), which is the done condition of the wrapper,
                // reset the signal_reg back to low
                signal_reg["write_en"] = eq_0_and_signal ? signal_on["out"];
                signal_reg["in"] =  eq_0_and_signal ? signal_off["out"];
            );
            builder.add_continuous_assignments(continuous_assigns.to_vec());
        }
        g.borrow_mut().assignments = group_assigns.to_vec();
        g.borrow_mut().attributes =
            early_reset_group.borrow().attributes.clone();
        g
    }

    /// compile `while` whose body is `static` control such that at the end of each
    /// iteration, the checking of condition does not incur an extra cycle of
    /// latency.
    /// We do this by wrapping the early reset group of the body with
    /// another wrapper group, which sets the go signal of the early reset group
    /// high, and is done when at the 0th cycle of each iteration, the condtion
    /// port is done.
    /// Note: this only works if the port for the while condition is `@stable`.
    fn build_wrapper_group_while(
        &self,
        fsm_first_state: ir::Guard<Nothing>,
        group_name: &ir::Id,
        port: RRC<ir::Port>,
        builder: &mut ir::Builder,
    ) -> RRC<ir::Group> {
        let reset_early_group = builder
            .component
            .find_group(*group_name)
            .unwrap_or_else(|| {
                unreachable!(
                    "called build_wrapper_group with {}, which is not a group",
                    group_name
                )
            });

        let wrapper_group =
            builder.add_group(format!("while_wrapper_{}", group_name));

        structure!(
            builder;
            let one = constant(1, 1);
        );

        let port_parent = port.borrow().cell_parent();
        let port_name = port.borrow().name;
        let done_guard = guard!(port_parent[port_name]).not() & fsm_first_state;

        let assignments = build_assignments!(
            builder;
            reset_early_group["go"] = ? one["out"];
            wrapper_group["done"] = done_guard ? one["out"];
        );

        wrapper_group.borrow_mut().assignments.extend(assignments);
        wrapper_group
    }

    // Get early reset group name from static control (we assume the static control
    // is an enable).
    fn get_reset_group_name(&self, sc: &mut ir::StaticControl) -> &ir::Id {
        // assume that there are only static enables left.
        // if there are any other type of static control, then error out.
        let ir::StaticControl::Enable(s) = sc else {
            unreachable!("Non-Enable Static Control should have been compiled away. Run {} to do this", crate::passes::StaticInliner::name());
        };

        let sgroup = s.group.borrow_mut();
        let sgroup_name = sgroup.name();
        // get the "early reset group". It should exist, since we made an
        // early_reset group for every static group in the component
        let early_reset_name =
            self.reset_early_map.get(&sgroup_name).unwrap_or_else(|| {
                unreachable!(
                    "group {} not in self.reset_early_map",
                    sgroup_name
                )
            });

        early_reset_name
    }
}

// These are the functions used to allocate FSMs to static islands
impl CompileStatic {
    // Given a list of `static_groups`, find the group named `name`.
    // If there is no such group, then there is an unreachable! error.
    fn find_static_group(
        name: &ir::Id,
        static_groups: &[ir::RRC<ir::StaticGroup>],
    ) -> ir::RRC<ir::StaticGroup> {
        Rc::clone(
            static_groups
                .iter()
                .find(|static_group| static_group.borrow().name() == name)
                .unwrap_or_else(|| {
                    unreachable!("couldn't find static group {name}")
                }),
        )
    }

    // Gets all of the triggered static groups within `c`, and adds it to `cur_names`.
    // Relies on sgroup_uses_map to take into account groups that are triggered through
    // their `go` hole.
    fn get_used_sgroups(c: &ir::Control, cur_names: &mut HashSet<ir::Id>) {
        match c {
            ir::Control::Empty(_)
            | ir::Control::Enable(_)
            | ir::Control::Invoke(_) => (),
            ir::Control::Static(sc) => {
                let ir::StaticControl::Enable(s) = sc else {
                    unreachable!("Non-Enable Static Control should have been compiled away. Run {} to do this", crate::passes::StaticInliner::name());
                };
                let group_name = s.group.borrow().name();
                cur_names.insert(group_name);
            }
            ir::Control::Par(ir::Par { stmts, .. })
            | ir::Control::Seq(ir::Seq { stmts, .. }) => {
                for stmt in stmts {
                    Self::get_used_sgroups(stmt, cur_names);
                }
            }
            ir::Control::Repeat(ir::Repeat { body, .. })
            | ir::Control::While(ir::While { body, .. }) => {
                Self::get_used_sgroups(body, cur_names);
            }
            ir::Control::If(if_stmt) => {
                Self::get_used_sgroups(&if_stmt.tbranch, cur_names);
                Self::get_used_sgroups(&if_stmt.fbranch, cur_names);
            }
        }
    }

    /// XXX(Caleb): Todo.
    fn add_par_conflicts(
        c: &ir::Control,
        fsm_trees: &Vec<Node>,
        conflict_graph: &mut GraphColoring<ir::Id>,
    ) {
        match c {
            ir::Control::Empty(_)
            | ir::Control::Enable(_)
            | ir::Control::Invoke(_)
            | ir::Control::Static(_) => (),
            ir::Control::Seq(seq) => {
                for stmt in &seq.stmts {
                    Self::add_par_conflicts(stmt, fsm_trees, conflict_graph);
                }
            }
            ir::Control::Repeat(ir::Repeat { body, .. })
            | ir::Control::While(ir::While { body, .. }) => {
                Self::add_par_conflicts(body, fsm_trees, conflict_graph)
            }
            ir::Control::If(if_stmt) => {
                Self::add_par_conflicts(
                    &if_stmt.tbranch,
                    fsm_trees,
                    conflict_graph,
                );
                Self::add_par_conflicts(
                    &if_stmt.fbranch,
                    fsm_trees,
                    conflict_graph,
                );
            }
            ir::Control::Par(par) => {
                // sgroup_conflict_vec is a vec of HashSets.
                // Each entry of the vec corresponds to a par thread, and holds
                // all of the groups executed in that thread.
                let mut sgroup_conflict_vec = Vec::new();
                for stmt in &par.stmts {
                    let mut used_sgroups = HashSet::new();
                    Self::get_used_sgroups(stmt, &mut used_sgroups);
                    sgroup_conflict_vec.push(used_sgroups);
                }
                for (thread1_sgroups, thread2_sgroups) in
                    sgroup_conflict_vec.iter().tuple_combinations()
                {
                    for static_enable1 in thread1_sgroups {
                        for static_enable2 in thread2_sgroups {
                            let tree1 = fsm_trees
                                .iter()
                                .find(|tree| {
                                    tree.get_group_name() == static_enable1
                                })
                                .expect("couldn't find FSM tree");
                            let tree2 = fsm_trees
                                .iter()
                                .find(|tree| {
                                    tree.get_group_name() == static_enable2
                                })
                                .expect("couldn't find tree");
                            for sgroup1 in tree1.get_all_nodes() {
                                for sgroup2 in tree2.get_all_nodes() {
                                    conflict_graph
                                        .insert_conflict(&sgroup1, &sgroup2)
                                }
                            }
                        }
                    }
                }
                // Necessary to add conflicts between nested pars
                for stmt in &par.stmts {
                    Self::add_par_conflicts(stmt, fsm_trees, conflict_graph);
                }
            }
        }
    }

    fn get_max_num_repeats(sgroup: ir::Id, tree_objects: &Vec<Node>) -> u64 {
        let mut cur_max = 1;
        for tree in tree_objects {
            cur_max = std::cmp::max(
                cur_max,
                tree.get_max_value(&sgroup, &(|tree| tree.num_repeats)),
            )
        }
        cur_max
    }
    fn get_max_num_states(sgroup: ir::Id, tree_objects: &Vec<Node>) -> u64 {
        let mut cur_max = 1;
        for tree in tree_objects {
            cur_max = std::cmp::max(
                cur_max,
                tree.get_max_value(&sgroup, &(|tree| tree.num_states)),
            )
        }
        cur_max
    }

    pub fn get_coloring(
        tree_objects: &Vec<Node>,
        sgroups: &[ir::RRC<ir::StaticGroup>],
        control: &mut ir::Control,
    ) -> HashMap<ir::Id, ir::Id> {
        let mut conflict_graph: GraphColoring<ir::Id> =
            GraphColoring::from(sgroups.iter().map(|g| g.borrow().name()));
        // Necessary conflicts to ensure correctness
        Self::add_par_conflicts(control, tree_objects, &mut conflict_graph);
        for tree in tree_objects {
            tree.add_conflicts(&mut conflict_graph);
        }
        // Optional conflicts to improve QoR
        // for (sgroup1, sgroup2) in sgroups.iter().tuple_combinations() {
        //     let max_num_states1 =
        //         Self::get_max_num_states(sgroup1.borrow().name(), tree_objects);
        //     let max_num_repeats1 = Self::get_max_num_repeats(
        //         sgroup1.borrow().name(),
        //         tree_objects,
        //     );
        //     let max_num_states2 =
        //         Self::get_max_num_states(sgroup2.borrow().name(), tree_objects);
        //     let max_num_repeats2 = Self::get_max_num_repeats(
        //         sgroup2.borrow().name(),
        //         tree_objects,
        //     );
        //     if ((max_num_states1 == 1) != (max_num_states2 == 1))
        //         || ((max_num_repeats1) != (max_num_repeats2))
        //     {
        //         conflict_graph.insert_conflict(
        //             &sgroup1.borrow().name(),
        //             &sgroup2.borrow().name(),
        //         );
        //     }
        // }

        conflict_graph.color_greedy(None, true)
    }

    pub fn get_color_max_values(
        coloring: &HashMap<ir::Id, ir::Id>,
        tree_objects: &Vec<Node>,
    ) -> HashMap<ir::Id, (u64, u64)> {
        let mut colors_to_sgroups: HashMap<ir::Id, Vec<ir::Id>> =
            HashMap::new();
        for (group_name, color) in coloring {
            colors_to_sgroups
                .entry(*color)
                .or_default()
                .push(*group_name);
        }
        colors_to_sgroups
            .into_iter()
            .map(|(name, colors_sgroups)| {
                let max_num_states = colors_sgroups
                    .iter()
                    .map(|gname| Self::get_max_num_states(*gname, tree_objects))
                    .max()
                    .expect("color is empty");
                let max_num_repeats = colors_sgroups
                    .iter()
                    .map(|gname| {
                        Self::get_max_num_repeats(*gname, tree_objects)
                    })
                    .max()
                    .expect("color is empty");
                (name, (max_num_states, max_num_repeats))
            })
            .collect()
    }
}

impl CompileStatic {
    fn get_interval_from_guard(
        g: &ir::Guard<ir::StaticTiming>,
        lat: u64,
        id: &ir::Id,
    ) -> Option<(u64, u64)> {
        match g {
            calyx_ir::Guard::Info(static_timing_interval) => {
                Some(static_timing_interval.get_interval())
            }
            calyx_ir::Guard::Not(_)
            | calyx_ir::Guard::CompOp(_, _, _)
            | calyx_ir::Guard::Port(_)
            | calyx_ir::Guard::True => Some((0, lat)),
            calyx_ir::Guard::And(l, r) => {
                match (
                    Self::get_interval_from_guard(l, lat, id),
                    Self::get_interval_from_guard(r, lat, id),
                ) {
                    (None, Some(x)) | (Some(x), None) => Some(x),
                    (None, None) => {
                        panic!("neither option")
                    }
                    (Some((beg1, end1)), Some((beg2, end2))) => {
                        assert!(end1 - beg1 == lat || end2 - beg2 == lat);
                        if end1 - beg1 == lat {
                            Some((beg2, end2))
                        } else {
                            Some((beg1, end1))
                        }
                    }
                }
            }
            ir::Guard::Or(_, _) => None,
        }
    }

    fn build_tree_object(
        name: ir::Id,
        static_groups: &Vec<ir::RRC<ir::StaticGroup>>,
        num_repeats: u64,
    ) -> Node {
        // Find the group that will serve as the root of the tree.
        let target_group = static_groups
            .iter()
            .find(|sgroup| sgroup.borrow().name() == name)
            .unwrap();
        let mut children_vec = vec![];
        let target_group_ref = target_group.borrow();
        for assign in &target_group_ref.assignments {
            // Looking for static_group[go] = %[i:j] ? 1'd1; to build children.
            match &assign.dst.borrow().parent {
                PortParent::Cell(_) => {
                    if target_group_ref.attributes.has(ir::BoolAttr::ParCtrl) {
                        panic!("")
                    }
                }
                PortParent::Group(_) => panic!(""),
                PortParent::StaticGroup(sgroup) => {
                    assert!(assign.src.borrow().is_constant(1, 1));
                    let x = Self::get_interval_from_guard(
                        &assign.guard,
                        target_group.borrow().get_latency(),
                        &name,
                    );
                    let (beg, end) =
                        x.expect("couldn't get interval from guard");
                    let name: calyx_ir::Id =
                        sgroup.upgrade().borrow().name().clone();
                    let target_child_latency =
                        Self::get_sgroup_latency(name, static_groups);
                    let child_execution_time = end - beg;
                    assert!(
                        child_execution_time % target_child_latency == 0,
                        ""
                    );
                    let child_num_repeats =
                        child_execution_time / target_child_latency;
                    children_vec.push((
                        Self::build_tree_object(
                            name,
                            static_groups,
                            child_num_repeats,
                        ),
                        (beg, end),
                    ));
                }
            }
        }

        if target_group_ref.attributes.has(ir::BoolAttr::ParCtrl) {
            assert!(children_vec.iter().all(|(_, (beg, _))| *beg == 0));
            Node::Par(ParNodes {
                group_name: name,
                threads: children_vec,
                latency: target_group_ref.latency,
                num_repeats: num_repeats,
            })
        } else {
            children_vec.sort_by_key(|(_, interval)| *interval);
            assert!(Self::are_ranges_non_overlapping(&children_vec));
            let mut cur_num_states = 0;
            let mut cur_lat = 0;
            let mut fsm_schedule = BTreeMap::new();
            for (_, (beg, end)) in &children_vec {
                if cur_lat != *beg {
                    fsm_schedule.insert(
                        (cur_lat, *beg),
                        StateType::Normal((
                            cur_num_states,
                            cur_num_states + (beg - cur_lat),
                        )),
                    );
                    cur_num_states += beg - cur_lat;
                    // cur_lat = *beg; assignment is unnecessary
                }
                fsm_schedule
                    .insert((*beg, *end), StateType::Offload(cur_num_states));
                cur_lat = *end;
                cur_num_states += 1;
            }
            if cur_lat != target_group_ref.latency {
                fsm_schedule.insert(
                    (cur_lat, target_group_ref.latency),
                    StateType::Normal((
                        cur_num_states,
                        cur_num_states + (target_group_ref.latency - cur_lat),
                    )),
                );
                cur_num_states += target_group_ref.latency - cur_lat;
            }
            Node::Single(SingleNode {
                latency: target_group_ref.latency,
                fsm_cell: None,
                iter_count_cell: None,
                root: (name, vec![]),
                fsm_schedule: fsm_schedule,
                children: children_vec,
                num_repeats: num_repeats,
                num_states: cur_num_states,
            })
        }
    }
    fn get_sgroup_latency(
        name: ir::Id,
        static_groups: &[ir::RRC<ir::StaticGroup>],
    ) -> u64 {
        static_groups
            .iter()
            .find(|sgroup| sgroup.borrow().name() == name)
            .unwrap()
            .borrow()
            .get_latency()
    }
    fn are_ranges_non_overlapping(ranges: &Vec<(Node, (u64, u64))>) -> bool {
        if ranges.len() == 0 {
            return true;
        }
        for i in 0..ranges.len() - 1 {
            let (_, (_, end1)) = ranges[i];
            let (_, (start2, _)) = ranges[i + 1];
            // Ensure that the current range's end is less than or equal to the next range's start
            if end1 > start2 {
                return false;
            }
        }
        true
    }

    fn get_static_enables(ctrl: &ir::Control) -> Vec<ir::Id> {
        match ctrl {
            ir::Control::Seq(ir::Seq { stmts, .. })
            | ir::Control::Par(ir::Par { stmts, .. }) => stmts
                .iter()
                .flat_map(|stmt| Self::get_static_enables(stmt))
                .collect_vec(),
            ir::Control::Empty(_)
            | ir::Control::Enable(_)
            | ir::Control::Invoke(_) => vec![],
            ir::Control::If(c) => {
                let mut tbranch_res = Self::get_static_enables(&*c.tbranch);
                let fbranch_res = Self::get_static_enables(&*c.fbranch);
                tbranch_res.extend(fbranch_res);
                tbranch_res
            }
            ir::Control::Repeat(ir::Repeat { body, .. })
            | ir::Control::While(ir::While { body, .. }) => {
                Self::get_static_enables(&*body)
            }
            ir::Control::Static(sc) => {
                let ir::StaticControl::Enable(s) = sc else {
                    panic!("")
                };
                vec![s.group.borrow().name()]
            }
        }
    }
}

// These are the functions used to compile for the static *component* interface
impl CompileStatic {
    // Used for guards in a one cycle static component.
    // Replaces %0 with comp.go.
    fn make_guard_dyn_one_cycle_static_comp(
        guard: ir::Guard<ir::StaticTiming>,
        comp_sig: RRC<ir::Cell>,
    ) -> ir::Guard<ir::Nothing> {
        match guard {
        ir::Guard::Or(l, r) => {
            let left =
                Self::make_guard_dyn_one_cycle_static_comp(*l, Rc::clone(&comp_sig));
            let right = Self::make_guard_dyn_one_cycle_static_comp(*r, Rc::clone(&comp_sig));
            ir::Guard::or(left, right)
        }
        ir::Guard::And(l, r) => {
            let left = Self::make_guard_dyn_one_cycle_static_comp(*l, Rc::clone(&comp_sig));
            let right = Self::make_guard_dyn_one_cycle_static_comp(*r, Rc::clone(&comp_sig));
            ir::Guard::and(left, right)
        }
        ir::Guard::Not(g) => {
            let f = Self::make_guard_dyn_one_cycle_static_comp(*g, Rc::clone(&comp_sig));
            ir::Guard::Not(Box::new(f))
        }
        ir::Guard::Info(t) => {
            match t.get_interval() {
                (0, 1) => guard!(comp_sig["go"]),
                _ => unreachable!("This function is implemented for 1 cycle static components, only %0 can exist as timing guard"),

            }
        }
        ir::Guard::CompOp(op, l, r) => ir::Guard::CompOp(op, l, r),
        ir::Guard::Port(p) => ir::Guard::Port(p),
        ir::Guard::True => ir::Guard::True,
    }
    }

    // Used for assignments in a one cycle static component.
    // Replaces %0 with comp.go in the assignment's guard.
    fn make_assign_dyn_one_cycle_static_comp(
        assign: ir::Assignment<ir::StaticTiming>,
        comp_sig: RRC<ir::Cell>,
    ) -> ir::Assignment<ir::Nothing> {
        ir::Assignment {
            src: assign.src,
            dst: assign.dst,
            attributes: assign.attributes,
            guard: Box::new(Self::make_guard_dyn_one_cycle_static_comp(
                *assign.guard,
                comp_sig,
            )),
        }
    }

    // Makes `done` signal for promoted static<n> component.
    fn make_done_signal_for_promoted_component(
        fsm_tree: &mut Node,
        builder: &mut ir::Builder,
        comp_sig: RRC<ir::Cell>,
    ) -> Vec<ir::Assignment<ir::Nothing>> {
        let first_state_guard = fsm_tree.query_between((0, 1), builder);
        structure!(builder;
          let sig_reg = prim std_reg(1);
          let one = constant(1, 1);
          let zero = constant(0, 1);
        );
        let go_guard = guard!(comp_sig["go"]);
        let not_go_guard = !guard!(comp_sig["go"]);
        let comp_done_guard =
            first_state_guard.clone().and(guard!(sig_reg["out"]));
        let assigns = build_assignments!(builder;
          // Only write to sig_reg when fsm == 0
          sig_reg["write_en"] = first_state_guard ? one["out"];
          // If fsm == 0 and comp.go is high, it means we are starting an execution,
          // so we set signal_reg to high. Note that this happens regardless of
          // whether comp.done is high.
          sig_reg["in"] = go_guard ? one["out"];
          // Otherwise, we set `sig_reg` to low.
          sig_reg["in"] = not_go_guard ? zero["out"];
          // comp.done is high when FSM == 0 and sig_reg is high,
          // since that means we have just finished an execution.
          comp_sig["done"] = comp_done_guard ? one["out"];
        );
        assigns.to_vec()
    }

    // Makes a done signal for a one-cycle static component.
    // Essentially you just have to use a one-cycle delay register that
    // takes the `go` signal as input.
    fn make_done_signal_for_promoted_component_one_cycle(
        builder: &mut ir::Builder,
        comp_sig: RRC<ir::Cell>,
    ) -> Vec<ir::Assignment<ir::Nothing>> {
        structure!(builder;
          let sig_reg = prim std_reg(1);
          let one = constant(1, 1);
          let zero = constant(0, 1);
        );
        let go_guard = guard!(comp_sig["go"]);
        let not_go = !guard!(comp_sig["go"]);
        let signal_on_guard = guard!(sig_reg["out"]);
        let assigns = build_assignments!(builder;
          // For one cycle components, comp.done is just whatever comp.go
          // was during the previous cycle.
          // signal_reg serves as a forwarding register that delays
          // the `go` signal for one cycle.
          sig_reg["in"] = go_guard ? one["out"];
          sig_reg["in"] = not_go ? zero["out"];
          sig_reg["write_en"] = ? one["out"];
          comp_sig["done"] = signal_on_guard ? one["out"];
        );
        assigns.to_vec()
    }

    // Compiles `sgroup` according to the static component interface.
    // The assignments are removed from `sgroup` and placed into
    // `builder.component`'s continuous assignments.
    fn compile_static_interface(
        &mut self,
        fsm_tree: &mut Node,
        static_groups: &mut Vec<ir::RRC<ir::StaticGroup>>,
        group_rewrites: &mut HashMap<ir::Canonical, ir::RRC<ir::Port>>,
        coloring: &HashMap<ir::Id, ir::Id>,
        colors_to_max_values: &HashMap<ir::Id, (u64, u64)>,
        colors_to_fsm: &mut HashMap<
            ir::Id,
            (Option<ir::RRC<StaticFSM>>, Option<ir::RRC<StaticFSM>>),
        >,
        builder: &mut ir::Builder,
    ) -> calyx_utils::CalyxResult<()> {
        if fsm_tree.get_latency() > 1 {
            let sgroup = Self::find_static_group(
                &fsm_tree.get_root_name(),
                static_groups,
            );
            for assign in &mut sgroup.borrow_mut().assignments {
                Node::preprocess_static_interface_assigns(
                    assign,
                    Rc::clone(&builder.component.signature),
                );
            }

            let comp_go = ir::Guard::port(
                builder
                    .component
                    .signature
                    .borrow()
                    .find_unique_with_attr(ir::NumAttr::Go)?
                    .unwrap(),
            );
            // Build a StaticSchedule object, realize it and add assignments
            // as continuous assignments.
            fsm_tree.instantiate_fsms(
                builder,
                coloring,
                colors_to_max_values,
                colors_to_fsm,
                self.one_hot_cutoff,
            );
            fsm_tree.count_to_n(builder, Some(comp_go));
            fsm_tree.realize(
                static_groups,
                &mut self.reset_early_map,
                &mut self.fsm_info_map,
                group_rewrites,
                builder,
            );
            builder.component.continuous_assignments.extend(
                fsm_tree.take_root_assigns().into_iter().filter(|assign| {
                    let dst = assign.dst.borrow();
                    match dst.parent {
                        PortParent::Cell(_) => true,
                        PortParent::Group(_) => dst.name != "done",
                        PortParent::StaticGroup(_) => true,
                    }
                }),
            );
            let comp_sig = Rc::clone(&builder.component.signature);
            if builder.component.attributes.has(ir::BoolAttr::Promoted) {
                // If necessary, add the logic to produce a done signal.
                let done_assigns =
                    Self::make_done_signal_for_promoted_component(
                        fsm_tree, builder, comp_sig,
                    );
                builder
                    .component
                    .continuous_assignments
                    .extend(done_assigns);
            }
        } else {
            // Handle components with latency == 1.
            // In this case, we don't need an FSM; we just guard the assignments
            // with comp.go.
            let sgroup = Self::find_static_group(
                &fsm_tree.get_root_name(),
                static_groups,
            );
            for (child, _) in fsm_tree.get_children() {
                child.convert_assignments_type(
                    static_groups,
                    &mut self.reset_early_map,
                    group_rewrites,
                    builder,
                )
            }
            let assignments =
                std::mem::take(&mut sgroup.borrow_mut().assignments);
            for mut assign in assignments {
                let comp_sig = Rc::clone(&builder.component.signature);
                assign.guard.update(|g| g.and(guard!(comp_sig["go"])));
                builder.component.continuous_assignments.push(
                    Self::make_assign_dyn_one_cycle_static_comp(
                        assign, comp_sig,
                    ),
                );
            }
            if builder.component.attributes.has(ir::BoolAttr::Promoted) {
                let comp_sig = Rc::clone(&builder.component.signature);
                let done_assigns =
                    Self::make_done_signal_for_promoted_component_one_cycle(
                        builder, comp_sig,
                    );
                builder
                    .component
                    .continuous_assignments
                    .extend(done_assigns);
            };
        };
        Ok(())
    }
}

impl Visitor for CompileStatic {
    fn start(
        &mut self,
        comp: &mut ir::Component,
        sigs: &ir::LibrarySignatures,
        _comps: &[ir::Component],
    ) -> VisResult {
        // Drain static groups of component
        let mut sgroups: Vec<ir::RRC<ir::StaticGroup>> =
            comp.get_static_groups_mut().drain().collect();

        let mut builder = ir::Builder::new(comp, sigs);
        // Get a vec of all groups that are enabled in comp's control.
        let static_enable_ids =
            Self::get_static_enables(&*builder.component.control.borrow());
        // Build one tree object per static enable.
        let mut tree_objects = static_enable_ids
            .iter()
            .map(|id| Self::build_tree_object(*id, &sgroups, 1))
            .collect_vec();

        // The first thing is to assign FSMs -> static islands.
        // We sometimes assign the same FSM to different static islands
        // to reduce register usage. We do this by getting greedy coloring.
        let coloring: HashMap<ir::Id, ir::Id> = Self::get_coloring(
            &tree_objects,
            &sgroups,
            &mut builder.component.control.borrow_mut(),
        );
        let colors_to_max_values =
            Self::get_color_max_values(&coloring, &tree_objects);
        let mut colors_to_fsms: HashMap<
            ir::Id,
            (Option<ir::RRC<StaticFSM>>, Option<ir::RRC<StaticFSM>>),
        > = HashMap::new();

        // Map so we can rewrite `static_group[go]` to `early_reset_group[go]`
        let mut group_rewrites = ir::rewriter::PortRewriteMap::default();
        // Static components have a different interface than static groups.
        // If we have a static component, we have to compile the top-level
        // island (this island should be a group by now and corresponds
        // to the the entire control of the component) differently.
        // This island might invoke other static groups-- these static groups
        // should still follow the group interface.
        let top_level_sgroup = if builder.component.is_static() {
            let comp_control = builder.component.control.borrow();
            match &*comp_control {
                ir::Control::Static(ir::StaticControl::Enable(sen)) => {
                    Some(sen.group.borrow().name())
                }
                _ => return Err(Error::malformed_control(format!("Non-Enable Static Control should have been compiled away. Run {} to do this", crate::passes::StaticInliner::name()))),
            }
        } else {
            None
        };
        // Make each tree count to n.
        for tree in &mut tree_objects {
            // Check whether we are compiling the top level static island.
            let static_component_interface = match top_level_sgroup {
                None => false,
                // For the top level group, sch.static_groups should really only
                // have one group--the top level group.
                Some(top_level_group) => {
                    tree.get_group_name() == top_level_group
                }
            };
            // Static component/groups have different interfaces
            if static_component_interface {
                // Compile top level static group differently.
                // We know that the top level static island has its own
                // unique FSM so we can do `.pop().unwrap()`
                self.compile_static_interface(
                    tree,
                    &mut sgroups,
                    &mut group_rewrites,
                    &coloring,
                    &colors_to_max_values,
                    &mut colors_to_fsms,
                    &mut builder,
                )?;
            } else {
                tree.instantiate_fsms(
                    &mut builder,
                    &coloring,
                    &colors_to_max_values,
                    &mut colors_to_fsms,
                    self.one_hot_cutoff,
                );
                tree.count_to_n(&mut builder, None);
                tree.realize(
                    &sgroups,
                    &mut self.reset_early_map,
                    &mut self.fsm_info_map,
                    &mut group_rewrites,
                    &mut builder,
                );
            }
        }

        // Rewrite static_group[go] to early_reset_group[go]
        // don't have to worry about writing static_group[done] b/c static
        // groups don't have done holes.
        comp.for_each_assignment(|assign| {
            assign.for_each_port(|port| {
                group_rewrites
                    .get(&port.borrow().canonical())
                    .map(Rc::clone)
            })
        });

        // Add the static groups back to the component.
        comp.get_static_groups_mut().append(sgroups.into_iter());

        Ok(Action::Continue)
    }

    /// Executed after visiting the children of a [ir::Static] node.
    fn start_static_control(
        &mut self,
        sc: &mut ir::StaticControl,
        comp: &mut ir::Component,
        sigs: &ir::LibrarySignatures,
        _comps: &[ir::Component],
    ) -> VisResult {
        // No need to build wrapper for static component interface
        if comp.is_static() {
            return Ok(Action::Continue);
        }
        // Assume that there are only static enables left.
        // If there are any other type of static control, then error out.
        let ir::StaticControl::Enable(s) = sc else {
            return Err(Error::malformed_control(format!("Non-Enable Static Control should have been compiled away. Run {} to do this", crate::passes::StaticInliner::name())));
        };

        let sgroup = s.group.borrow_mut();
        let sgroup_name = sgroup.name();
        // get the "early reset group". It should exist, since we made an
        // early_reset group for every static group in the component
        let early_reset_name =
            self.reset_early_map.get(&sgroup_name).unwrap_or_else(|| {
                unreachable!(
                    "{}'s early reset group has not been created",
                    sgroup_name
                )
            });
        // check if we've already built the wrapper group for early_reset_group
        // if so, we can just use that, otherwise, we must build the wrapper group
        let group_choice = match self.wrapper_map.get(early_reset_name) {
            None => {
                // create the builder/cells that we need to create wrapper group
                let mut builder = ir::Builder::new(comp, sigs);
                let (fsm_name, fsm_eq_0, fsm_final_state) = self.fsm_info_map.get(early_reset_name).unwrap_or_else(|| unreachable!("group {} has no correspondoing fsm in self.fsm_map", early_reset_name));
                // If we've already made a wrapper for a group that uses the same
                // FSM, we can reuse the signal_reg. Otherwise, we must
                // instantiate a new signal_reg.
                let wrapper = match self.signal_reg_map.get(fsm_name) {
                    None => {
                        // Need to build the signal_reg and the continuous
                        // assignment that resets the signal_reg
                        structure!( builder;
                            let signal_reg = prim std_reg(1);
                        );
                        self.signal_reg_map
                            .insert(*fsm_name, signal_reg.borrow().name());
                        Self::build_wrapper_group(
                            fsm_eq_0.clone(),
                            fsm_final_state.clone(),
                            early_reset_name,
                            signal_reg,
                            &mut builder,
                            true,
                        )
                    }
                    Some(reg_name) => {
                        // Already_built the signal_reg.
                        // We don't need to add continuous assignments
                        // that resets signal_reg.
                        let signal_reg = builder
                            .component
                            .find_cell(*reg_name)
                            .unwrap_or_else(|| {
                                unreachable!("signal reg {reg_name} found")
                            });
                        Self::build_wrapper_group(
                            fsm_eq_0.clone(),
                            fsm_final_state.clone(),
                            early_reset_name,
                            signal_reg,
                            &mut builder,
                            false,
                        )
                    }
                };
                self.wrapper_map
                    .insert(*early_reset_name, wrapper.borrow().name());
                wrapper
            }
            Some(name) => comp.find_group(*name).unwrap(),
        };

        let mut e = ir::Control::enable(group_choice);
        let attrs = std::mem::take(&mut s.attributes);
        *e.get_mut_attributes() = attrs;
        Ok(Action::Change(Box::new(e)))
    }

    /// If while body is static, then we want to make sure that the while
    /// body does not take the extra cycle incurred by the done condition
    /// So we replace the while loop with `enable` of a wrapper group
    /// that sets the go signal of the static group in the while loop body high
    /// (all static control should be compiled into static groups by
    /// `static_inliner` now). The done signal of the wrapper group should be
    /// the condition that the fsm of the while body is %0 and the port signal
    /// is 1'd0.
    /// For example, we replace
    /// ```
    /// wires {
    /// static group A<1> {
    ///     ...
    ///   }
    ///    ...
    /// }
    /// control {
    ///   while l.out {
    ///     A;
    ///   }
    /// }
    /// ```
    /// with
    /// ```
    /// wires {
    ///  group early_reset_A {
    ///     ...
    ///        }
    ///
    /// group while_wrapper_early_reset_A {
    ///       early_reset_A[go] = 1'd1;
    ///       while_wrapper_early_reset_A[done] = !l.out & fsm.out == 1'd0 ? 1'd1;
    ///     }
    ///   }
    ///   control {
    ///     while_wrapper_early_reset_A;
    ///   }
    /// ```
    fn start_while(
        &mut self,
        s: &mut ir::While,
        comp: &mut ir::Component,
        sigs: &ir::LibrarySignatures,
        _comps: &[ir::Component],
    ) -> VisResult {
        if s.cond.is_none() {
            if let ir::Control::Static(sc) = &mut *(s.body) {
                let mut builder = ir::Builder::new(comp, sigs);
                let reset_group_name = self.get_reset_group_name(sc);

                // Get fsm for reset_group
                let (_, fsm_eq_0, _) = self.fsm_info_map.get(reset_group_name).unwrap_or_else(|| unreachable!("group {} has no correspondoing fsm in self.fsm_map", reset_group_name));
                let wrapper_group = self.build_wrapper_group_while(
                    fsm_eq_0.clone(),
                    reset_group_name,
                    Rc::clone(&s.port),
                    &mut builder,
                );
                let c = ir::Control::enable(wrapper_group);
                return Ok(Action::change(c));
            }
        }

        Ok(Action::Continue)
    }

    fn finish(
        &mut self,
        comp: &mut ir::Component,
        _sigs: &ir::LibrarySignatures,
        _comps: &[ir::Component],
    ) -> VisResult {
        // make sure static groups have no assignments, since
        // we should have already drained the assignments in static groups
        // for g in comp.get_static_groups() {
        //     if !g.borrow().assignments.is_empty() {
        //         unreachable!("Should have converted all static groups to dynamic. {} still has assignments in it. It's possible that you may need to run {} to remove dead groups and get rid of this error.", g.borrow().name(), crate::passes::DeadGroupRemoval::name());
        //     }
        // }
        // remove all static groups
        comp.get_static_groups_mut().retain(|_| false);

        // Remove control if static component
        if comp.is_static() {
            comp.control = ir::rrc(ir::Control::empty())
        }

        Ok(Action::Continue)
    }
}
