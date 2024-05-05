use crate::passes::math_utilities::get_bit_width_from;
use crate::traversal::Named;
use calyx_ir::{self as ir};
use calyx_ir::{build_assignments, Nothing};
use calyx_ir::{guard, structure};
use ir::Guard;
use itertools::Itertools;
use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;

use super::GraphColoring;

#[derive(Debug, Clone, Copy)]
// Define an FSMEncoding Enum
enum FSMEncoding {
    Binary,
    OneHot,
}

#[derive(Debug)]
enum FSMImplementationType {
    Single,
    // How many duplicates
    _Duplicate(u64),
    // How many times to split
    _Split(u64),
}

#[derive(Debug)]
// Define an enum called FSMType
enum FSMImplementation {
    // Default option: just a single register
    Single(ir::RRC<ir::Cell>),
    // Duplicate the register to reduce fanout when querying
    // (all FSMs in this vec still have all of the states)
    _Duplicate(Vec<ir::RRC<ir::Cell>>),
    // Split the FSM to reduce fanout when querying.
    // (the FSMs partition the states exactly).
    // Each FSM has fewer bits but I suspect the logic might be more complicated.
    _Split(Vec<ir::RRC<ir::Cell>>),
}

impl FSMImplementation {
    fn get_single_cell(&self) -> ir::RRC<ir::Cell> {
        match self {
            FSMImplementation::Single(cell) => Rc::clone(cell),
            _ => unreachable!(
                "called function on non-single FSM implementation "
            ),
        }
    }
}

#[derive(Debug)]
pub struct StaticFSM {
    _num_states: u64,
    _encoding: FSMEncoding,
    // The fsm's bitwidth (this redundant information bc  we have `cell`)
    // but makes it easier if we easily have access to this.
    bitwidth: u64,
    // The actual register(s) used to implement the FSM
    implementation: FSMImplementation,
}
impl StaticFSM {
    // Builds a static_fsm from: num_states and encoding type.
    fn from_basic_info(
        num_states: u64,
        encoding: FSMEncoding,
        _implementation: FSMImplementationType,
        queries: &HashSet<(u64, u64)>,
        builder: &mut ir::Builder,
    ) -> Self {
        let fsm_size = match encoding {
            /* represent 0..latency */
            FSMEncoding::Binary => get_bit_width_from(num_states + 1),
            FSMEncoding::OneHot => num_states,
        };

        let fsm = FSMImplementation::Single(builder.add_primitive(
            "fsm",
            "std_reg",
            &[fsm_size],
        ));

        // need to add a couple structures to extract query bits from state if OHE used
        if let FSMEncoding::OneHot = encoding {
            let fsm_cell = fsm.get_single_cell();

            for (lb, ub) in queries {
                // add a splitter to take specific parts of the FSM state bit string
                let in_width = num_states;
                let start_index = lb.clone();
                let end_index = ub - 1; // slice requires inclusive indexing
                let out_width = ub - lb;
                structure!(builder; let slicer = prim std_bit_slice(in_width, start_index, end_index, out_width););

                // Extend the continuous assignmments to include this particular query for FSM state;
                // To be used in a guard later
                let assigns = build_assignments!(builder;
                    slicer["in"] = ? fsm_cell["out"];
                )
                .to_vec();

                builder.add_continuous_assignments(assigns);
            }
        };

        StaticFSM {
            _num_states: num_states,
            _encoding: encoding,
            bitwidth: fsm_size,
            implementation: fsm,
        }
    }

    // Returns assignments that make the current fsm count to n
    // and then reset back to 0.
    // `incr_condition`` is an optional guard: if it is none, then the fsm will
    // unconditionally increment.
    // If it actually holds a `guard`, then we will only start counting once
    // the condition holds.
    // (NOTE: if the guard is true while we are counting up we will just
    // ignore that guard and keep on counting-- we don't reset or anything.
    // The guard is just there to make sure we only go from 0->1 when appropriate.)
    pub fn count_to_n(
        &self,
        builder: &mut ir::Builder,
        n: u64,
        incr_condition: Option<Guard<Nothing>>,
    ) -> Vec<ir::Assignment<Nothing>> {
        match self._encoding {
            FSMEncoding::Binary => {
                assert!(matches!(
                    self.implementation,
                    FSMImplementation::Single(_)
                ));
                // Add assignments to increment the fsm by one unconditionally.
                structure!( builder;
                    // done hole will be undefined bc of early reset
                    let signal_on = constant(1,1);
                    let adder = prim std_add(self.bitwidth);
                    let const_one = constant(1, self.bitwidth);
                    let first_state = constant(0, self.bitwidth);
                    let final_state = constant(n, self.bitwidth);
                );
                let fsm_cell = self.implementation.get_single_cell();
                let final_state_guard: ir::Guard<Nothing> =
                    guard!(fsm_cell["out"] == final_state["out"]);
                match incr_condition {
                    None => {
                        // "Normal" logic to increment FSM by one.
                        let not_final_state_guard: ir::Guard<ir::Nothing> =
                            guard!(fsm_cell["out"] != final_state["out"]);
                        build_assignments!(
                          builder;
                          // increments the fsm
                          adder["left"] = ? fsm_cell["out"];
                          adder["right"] = ? const_one["out"];
                          fsm_cell["write_en"] = ? signal_on["out"];
                          fsm_cell["in"] =  not_final_state_guard ? adder["out"];
                           // resets the fsm early
                           fsm_cell["in"] = final_state_guard ? first_state["out"];
                        )
                        .to_vec()
                    }
                    Some(condition_guard) => {
                        let first_state_guard: ir::Guard<Nothing> =
                            guard!(fsm_cell["out"] == first_state["out"]);
                        let cond_and_first_state =
                            ir::Guard::and(condition_guard, first_state_guard);
                        let not_first_state: ir::Guard<Nothing> =
                            guard!(fsm_cell["out"] != first_state["out"]);
                        let not_last_state: ir::Guard<Nothing> =
                            guard!(fsm_cell["out"] != final_state["out"]);
                        let in_between_guard =
                            ir::Guard::and(not_first_state, not_last_state);
                        build_assignments!(
                          builder;
                          // Incrementsthe fsm
                          adder["left"] = ? fsm_cell["out"];
                          adder["right"] = ? const_one["out"];
                          // Always write into fsm.
                          fsm_cell["write_en"] = ? signal_on["out"];
                          // If fsm == 0 and cond is high, then we start an execution.
                          fsm_cell["in"] = cond_and_first_state ? const_one["out"];
                          // If 1 < fsm < n - 1, then we unconditionally increment the fsm.
                          fsm_cell["in"] = in_between_guard ? adder["out"];
                          // If fsm == n -1 , then we reset the FSM.
                          fsm_cell["in"] = final_state_guard ? first_state["out"];
                          // Otherwise the FSM is not assigned to, so it defaults to 0.
                          // If we want, we could add an explicit assignment here that sets it
                          // to zero.
                        )
                        .to_vec()
                    }
                }
            }
            FSMEncoding::OneHot => {
                let _a: Vec<ir::Assignment<Nothing>> = Vec::new();
                panic!("not implemented")
            }
        }
    }

    // Returns a guard that takes a (beg, end) `query`, and returns the equivalent
    // guard to `beg <= fsm.out < end`.
    pub fn query_between(
        &self,
        builder: &mut ir::Builder,
        query: (u64, u64),
    ) -> Box<ir::Guard<Nothing>> {
        let (beg, end) = query;

        assert!(matches!(self.implementation, FSMImplementation::Single(_)));

        let fsm_cell = self.implementation.get_single_cell();
        if beg + 1 == end {
            // if beg + 1 == end then we only need to check if fsm == beg

            match self._encoding {
                FSMEncoding::Binary => {
                    let interval_const =
                        builder.add_constant(beg, self.bitwidth);
                    let g = guard!(fsm_cell["out"] == interval_const["out"]);
                    Box::new(g)
                }
                FSMEncoding::OneHot => {
                    // let one_hot_state = fsm_cell["out"];

                    match beg {
                        0 => {
                            // if 0, forced to check all bits by 0 |-> 000 convention
                            let const_zero =
                                builder.add_constant(0, self.bitwidth);
                            let g =
                                guard!(fsm_cell["out"] == const_zero["out"]);
                            Box::new(g)
                        }
                        n => {
                            let signal_on = builder.add_constant(1, 1);

                            // if checking non-zero equality, need only check one bit by OHE convention
                            structure!(builder;
                                let extract_bit = prim std_bit_slice(
                                    self.bitwidth, // input width size
                                    n-1,           // start index
                                    n-1,           // end index (read exactly nth bit)
                                    1              // read only 1 bit
                                );
                                let equality_check = prim std_reg(1);
                            );
                            // put the output of single-bit equality check inside a register
                            let _assigns: [ir::Assignment<Nothing>; 3] = build_assignments!(builder;
                                extract_bit["in"] = ? fsm_cell["out"];
                                equality_check["write_en"] = ? signal_on["out"];
                                equality_check["in"] = ? extract_bit["out"];
                            );
                            // create a guard based on the output of this register
                            let g = guard!(
                                equality_check["out"] & signal_on["out"]
                            );
                            Box::new(g)
                        }
                    }
                }
            }
        } else if beg == 0 {
            // if beg == 0, then we only need to check if fsm < end
            let end_const = builder.add_constant(end, self.bitwidth);
            let lt: ir::Guard<Nothing> =
                guard!(fsm_cell["out"] < end_const["out"]);
            Box::new(lt)
        } else {
            // otherwise, check if fsm >= beg & fsm < end
            let beg_const = builder.add_constant(beg, self.bitwidth);
            let end_const = builder.add_constant(end, self.bitwidth);
            let beg_guard: ir::Guard<Nothing> =
                guard!(fsm_cell["out"] >= beg_const["out"]);
            let end_guard: ir::Guard<Nothing> =
                guard!(fsm_cell["out"] < end_const["out"]);
            Box::new(ir::Guard::And(Box::new(beg_guard), Box::new(end_guard)))
        }
    }

    // Return a unique id (i.e., get_unique_id for each FSM in the same component
    // will be different).
    pub fn get_unique_id(&self) -> ir::Id {
        assert!(matches!(self.implementation, FSMImplementation::Single(_)));
        self.implementation.get_single_cell().borrow().name()
    }

    // Return the bitwidth of an FSM object
    pub fn get_bitwidth(&self) -> u64 {
        assert!(matches!(self.implementation, FSMImplementation::Single(_)));
        self.bitwidth
    }
}

/// Represents a static schedule.
#[derive(Debug, Default)]
pub struct StaticSchedule {
    /// Number of states for the FSM
    /// (this is just the latency of the static island-- or that of the largest
    /// static island, if there are multiple islands)
    num_states: u64,
    /// The queries that the FSM needs to support.
    /// E.g., `lhs = %[2:3] ? rhs` corresponds to (2,3).
    queries: HashSet<(u64, u64)>,
    /// The static groups the FSM will schedule. It is a vec because sometimes
    /// the same FSM will handle two different static islands.
    pub static_groups: Vec<ir::RRC<ir::StaticGroup>>,
}

impl From<Vec<ir::RRC<ir::StaticGroup>>> for StaticSchedule {
    /// Builds a StaticSchedule object from a vec of static groups.
    fn from(static_groups: Vec<ir::RRC<ir::StaticGroup>>) -> Self {
        let mut schedule = StaticSchedule {
            static_groups,
            ..Default::default()
        };
        schedule.num_states = 0;
        for static_group in &schedule.static_groups {
            // Getting self.queries
            for static_assign in &static_group.borrow().assignments {
                for query in Self::queries_from_guard(&static_assign.guard) {
                    schedule.queries.insert(query);
                }
            }
            // Getting self.num_states
            schedule.num_states = std::cmp::max(
                schedule.num_states,
                static_group.borrow().get_latency(),
            );
        }
        schedule
    }
}

impl StaticSchedule {
    /// Given a guard, returns the queries that the static FSM (i.e., counter)
    /// will make.
    fn queries_from_guard(
        guard: &ir::Guard<ir::StaticTiming>,
    ) -> Vec<(u64, u64)> {
        match guard {
            ir::Guard::Or(l, r) | ir::Guard::And(l, r) => {
                let mut lvec = Self::queries_from_guard(l);
                let rvec = Self::queries_from_guard(r);
                lvec.extend(rvec);
                lvec
            }
            ir::Guard::Not(g) => Self::queries_from_guard(g),
            ir::Guard::Port(_)
            | ir::Guard::CompOp(_, _, _)
            | ir::Guard::True => vec![],
            ir::Guard::Info(static_timing) => {
                vec![static_timing.get_interval()]
            }
        }
    }

    /// Realizes a StaticSchedule (i.e., instantiates the FSMs)
    /// If `self.static_groups = vec![group1, group2, group3, ...]``
    /// Then `realize_schedule()` returns vecdeque![a1, a2, a3]
    /// Where a1 are the assignments for group1, a2 are the assignments
    /// to group2, etc.
    /// It also returns the StaticFSM object.
    ///
    /// We also have a bool argument `static_component_interface`.
    /// If you are the entire control of a static component, it is slightly different,
    /// because we need to separate the first cycle (%[0:n] -> %0 | [%1:n]) and
    /// replace %0 with `comp.go & %0`. (We do `comp.go & %0` rather than `%0` bc
    /// we want the clients to be able to assert `go` for n cycles and the
    /// component still works as expected).
    pub fn realize_schedule(
        &mut self,
        builder: &mut ir::Builder,
        static_component_interface: bool,
        one_hot_cutoff: u64,
    ) -> (VecDeque<Vec<ir::Assignment<Nothing>>>, StaticFSM) {
        // Choose encoding based on one-hot cutoff.
        let encoding = if self.num_states > one_hot_cutoff {
            FSMEncoding::Binary
        } else {
            FSMEncoding::OneHot
        };

        // First build the fsm we will use to realize the schedule.
        let fsm_object = StaticFSM::from_basic_info(
            self.num_states,
            encoding,
            FSMImplementationType::Single,
            &self.queries,
            builder,
        );

        // Instantiate the vecdeque.
        let mut res = VecDeque::new();
        for static_group in &mut self.static_groups {
            let mut static_group_ref = static_group.borrow_mut();
            // Separate the first cycle (if necessary) and then realize the
            // static timing guards (e.g., %[2:3] -> 2 <= fsm < 3).
            let group_assigns =
                static_group_ref.assignments.drain(..).collect_vec();
            let static_assigns = if static_component_interface {
                group_assigns
                    .into_iter()
                    .map(|assign| {
                        if static_component_interface {
                            Self::handle_static_interface(
                                assign,
                                Rc::clone(&builder.component.signature),
                            )
                        } else {
                            assign
                        }
                    })
                    .collect_vec()
            } else {
                group_assigns
            };
            let mut assigns: Vec<ir::Assignment<Nothing>> = static_assigns
                .into_iter()
                .map(|static_assign| {
                    Self::make_assign_dyn(static_assign, &fsm_object, builder)
                })
                .collect();
            // For static components, we don't unconditionally start counting.
            // We must only start counting when `comp.go` is high.
            let fsm_incr_condition = if static_component_interface {
                let comp_sig = Rc::clone(&builder.component.signature);
                let g = guard!(comp_sig["go"]);
                Some(g)
            } else {
                None
            };
            // We need to add assignments that makes the FSM count to n.
            assigns.extend(fsm_object.count_to_n(
                builder,
                static_group_ref.get_latency() - 1,
                fsm_incr_condition,
            ));

            res.push_back(assigns);
        }
        (res, fsm_object)
    }

    // Takes in a static guard `guard`, and returns equivalent dynamic guard
    // The only thing that actually changes is the Guard::Info case
    // We need to turn static_timing to dynamic guards using `fsm`.
    // E.g.: %[2:3] gets turned into fsm.out >= 2 & fsm.out < 3
    // is_static_comp is necessary becasue it ...
    fn make_guard_dyn(
        guard: ir::Guard<ir::StaticTiming>,
        fsm_object: &StaticFSM,
        builder: &mut ir::Builder,
    ) -> Box<ir::Guard<Nothing>> {
        match guard {
            ir::Guard::Or(l, r) => Box::new(ir::Guard::Or(
                Self::make_guard_dyn(*l, fsm_object, builder),
                Self::make_guard_dyn(*r, fsm_object, builder),
            )),
            ir::Guard::And(l, r) => Box::new(ir::Guard::And(
                Self::make_guard_dyn(*l, fsm_object, builder),
                Self::make_guard_dyn(*r, fsm_object, builder),
            )),
            ir::Guard::Not(g) => Box::new(ir::Guard::Not(
                Self::make_guard_dyn(*g, fsm_object, builder),
            )),
            ir::Guard::CompOp(op, l, r) => {
                Box::new(ir::Guard::CompOp(op, l, r))
            }
            ir::Guard::Port(p) => Box::new(ir::Guard::Port(p)),
            ir::Guard::True => Box::new(ir::Guard::True),
            ir::Guard::Info(static_timing) => {
                fsm_object.query_between(builder, static_timing.get_interval())
            }
        }
    }

    // Takes in static assignment `assign` and returns a dynamic assignments
    // Mainly transforms the guards from %[2:3] -> fsm.out >= 2 & fsm.out <= 3
    fn make_assign_dyn(
        assign: ir::Assignment<ir::StaticTiming>,
        fsm_object: &StaticFSM,
        builder: &mut ir::Builder,
    ) -> ir::Assignment<Nothing> {
        ir::Assignment {
            src: assign.src,
            dst: assign.dst,
            attributes: assign.attributes,
            guard: Self::make_guard_dyn(*assign.guard, fsm_object, builder),
        }
    }

    // Looks recursively thru guard to transform %[0:n] into %0 | %[1:n].
    fn handle_static_interface_guard(
        guard: ir::Guard<ir::StaticTiming>,
        comp_sig: ir::RRC<ir::Cell>,
    ) -> ir::Guard<ir::StaticTiming> {
        match guard {
            ir::Guard::Info(st) => {
                let (beg, end) = st.get_interval();
                if beg == 0 {
                    // Replace %[0:n] -> (%0 & comp.go) | %[1:n]
                    // Cannot just do comp.go | %[1:n] because we want
                    // clients to be able to assert `comp.go` even after the first
                    // cycle w/o affecting correctness.
                    let first_cycle =
                        ir::Guard::Info(ir::StaticTiming::new((0, 1)));
                    let comp_go = guard!(comp_sig["go"]);
                    let first_and_go = ir::Guard::and(comp_go, first_cycle);
                    if end == 1 {
                        return first_and_go;
                    } else {
                        let after =
                            ir::Guard::Info(ir::StaticTiming::new((1, end)));
                        let cong = ir::Guard::or(first_and_go, after);
                        return cong;
                    }
                }
                guard
            }
            ir::Guard::And(l, r) => {
                let left = Self::handle_static_interface_guard(
                    *l,
                    Rc::clone(&comp_sig),
                );
                let right = Self::handle_static_interface_guard(*r, comp_sig);
                ir::Guard::and(left, right)
            }
            ir::Guard::Or(l, r) => {
                let left = Self::handle_static_interface_guard(
                    *l,
                    Rc::clone(&comp_sig),
                );
                let right = Self::handle_static_interface_guard(*r, comp_sig);
                ir::Guard::or(left, right)
            }
            ir::Guard::Not(g) => {
                let a = Self::handle_static_interface_guard(*g, comp_sig);
                ir::Guard::Not(Box::new(a))
            }
            _ => guard,
        }
    }

    // Looks recursively thru assignment's guard to %[0:n] into %0 | %[1:n].
    fn handle_static_interface(
        assign: ir::Assignment<ir::StaticTiming>,
        comp_sig: ir::RRC<ir::Cell>,
    ) -> ir::Assignment<ir::StaticTiming> {
        ir::Assignment {
            src: assign.src,
            dst: assign.dst,
            attributes: assign.attributes,
            guard: Box::new(Self::handle_static_interface_guard(
                *assign.guard,
                comp_sig,
            )),
        }
    }
}

pub struct FSMAllocator;
// These are the functions/methods used to assign FSMs to static islands
// (Currently we use greedy coloring).
impl FSMAllocator {
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

    // Given an input static_group `sgroup`, finds the names of all of the groups
    // that it triggers through their go hole.
    // E.g., if `sgroup` has assignments that write to `sgroup1[go]` and `sgroup2[go]`
    // then return `{sgroup1, sgroup2}`
    // Assumes that static groups will only write the go holes of other static
    // groups, and never dynamic groups (which seems like a reasonable assumption).
    fn get_go_writes(sgroup: &ir::RRC<ir::StaticGroup>) -> HashSet<ir::Id> {
        let mut uses = HashSet::new();
        for asgn in &sgroup.borrow().assignments {
            let dst = asgn.dst.borrow();
            if dst.is_hole() && dst.name == "go" {
                uses.insert(dst.get_parent_name());
            }
        }
        uses
    }

    // Gets all of the triggered static groups within `c`, and adds it to `cur_names`.
    // Relies on sgroup_uses_map to take into account groups that are triggered through
    // their `go` hole.
    fn get_used_sgroups(
        c: &ir::Control,
        cur_names: &mut HashSet<ir::Id>,
        sgroup_uses_map: &HashMap<ir::Id, HashSet<ir::Id>>,
    ) {
        match c {
            ir::Control::Empty(_)
            | ir::Control::Enable(_)
            | ir::Control::Invoke(_) => (),
            ir::Control::Static(sc) => {
                let ir::StaticControl::Enable(s) = sc else {
                    unreachable!("Non-Enable Static Control should have been compiled away. Run {} to do this", crate::passes::StaticInliner::name());
                };
                let group_name = s.group.borrow().name();
                if let Some(sgroup_uses) = sgroup_uses_map.get(&group_name) {
                    cur_names.extend(sgroup_uses);
                }
                cur_names.insert(group_name);
            }
            ir::Control::Par(ir::Par { stmts, .. })
            | ir::Control::Seq(ir::Seq { stmts, .. }) => {
                for stmt in stmts {
                    Self::get_used_sgroups(stmt, cur_names, sgroup_uses_map);
                }
            }
            ir::Control::Repeat(ir::Repeat { body, .. })
            | ir::Control::While(ir::While { body, .. }) => {
                Self::get_used_sgroups(body, cur_names, sgroup_uses_map);
            }
            ir::Control::If(if_stmt) => {
                Self::get_used_sgroups(
                    &if_stmt.tbranch,
                    cur_names,
                    sgroup_uses_map,
                );
                Self::get_used_sgroups(
                    &if_stmt.fbranch,
                    cur_names,
                    sgroup_uses_map,
                );
            }
        }
    }

    /// Given control `c`, adds conflicts to `conflict_graph` between all
    /// static groups that are executed in separate threads of the same par block.
    /// `sgroup_uses_map` maps:
    /// static group names -> all of the static groups that it triggers the go ports
    /// of (even recursively).
    /// Example: group A {B[go] = 1;} group B {C[go] = 1} group C{}
    /// Would map: A -> {B,C} and B -> {C}
    fn add_par_conflicts(
        c: &ir::Control,
        sgroup_uses_map: &HashMap<ir::Id, HashSet<ir::Id>>,
        conflict_graph: &mut GraphColoring<ir::Id>,
    ) {
        match c {
            ir::Control::Empty(_)
            | ir::Control::Enable(_)
            | ir::Control::Invoke(_)
            | ir::Control::Static(_) => (),
            ir::Control::Seq(seq) => {
                for stmt in &seq.stmts {
                    Self::add_par_conflicts(
                        stmt,
                        sgroup_uses_map,
                        conflict_graph,
                    );
                }
            }
            ir::Control::Repeat(ir::Repeat { body, .. })
            | ir::Control::While(ir::While { body, .. }) => {
                Self::add_par_conflicts(body, sgroup_uses_map, conflict_graph)
            }
            ir::Control::If(if_stmt) => {
                Self::add_par_conflicts(
                    &if_stmt.tbranch,
                    sgroup_uses_map,
                    conflict_graph,
                );
                Self::add_par_conflicts(
                    &if_stmt.fbranch,
                    sgroup_uses_map,
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
                    Self::get_used_sgroups(
                        stmt,
                        &mut used_sgroups,
                        sgroup_uses_map,
                    );
                    sgroup_conflict_vec.push(used_sgroups);
                }
                for (thread1_sgroups, thread2_sgroups) in
                    sgroup_conflict_vec.iter().tuple_combinations()
                {
                    for sgroup1 in thread1_sgroups {
                        for sgroup2 in thread2_sgroups {
                            conflict_graph.insert_conflict(sgroup1, sgroup2);
                        }
                    }
                }
                // Necessary to add conflicts between nested pars
                for stmt in &par.stmts {
                    Self::add_par_conflicts(
                        stmt,
                        sgroup_uses_map,
                        conflict_graph,
                    );
                }
            }
        }
    }

    /// Given an `sgroup_uses_map`, which maps:
    /// static group names -> all of the static groups that it triggers the go ports
    /// of (even recursively).
    /// Example: group A {B[go] = 1;} group B {C[go] = 1} group C{}
    /// Would map: A -> {B,C} and B -> {C}
    /// Adds conflicts between any groups triggered at the same time based on
    /// `go` port triggering.
    fn add_go_port_conflicts(
        sgroup_uses_map: &HashMap<ir::Id, HashSet<ir::Id>>,
        conflict_graph: &mut GraphColoring<ir::Id>,
    ) {
        for (sgroup, sgroup_uses) in sgroup_uses_map {
            for sgroup_use in sgroup_uses {
                conflict_graph.insert_conflict(sgroup_use, sgroup);
            }
            // If multiple groups are triggered by the same group, then
            // we conservatively add a conflict between such groups
            for (sgroup_use1, sgroup_use2) in
                sgroup_uses.iter().tuple_combinations()
            {
                conflict_graph.insert_conflict(sgroup_use1, sgroup_use2);
            }
        }
    }

    // helper to `build_sgroup_uses_map`
    // `parent_group` is the group that we are "currently" analyzing
    // `full_group_ancestry` is the "ancestry of the group we are analyzing"
    // Example: group A {B[go] = 1;} group B {C[go] = 1} group C{}, and `parent_group`
    // is B, then ancestry would be B and A.
    // `cur_mapping` is the current_mapping for `sgroup_uses_map`
    // `group_names` is a vec of group_names. Once we analyze a group, we should
    // remove it from group_names
    // `sgroups` is a vec of static groups.
    fn update_sgroup_uses_map(
        parent_group: &ir::Id,
        full_group_ancestry: &mut HashSet<ir::Id>,
        cur_mapping: &mut HashMap<ir::Id, HashSet<ir::Id>>,
        group_names: &mut HashSet<ir::Id>,
        sgroups: &Vec<ir::RRC<ir::StaticGroup>>,
    ) {
        let group_uses = Self::get_go_writes(&Self::find_static_group(
            parent_group,
            sgroups,
        ));
        for group_use in group_uses {
            for ancestor in full_group_ancestry.iter() {
                cur_mapping.entry(*ancestor).or_default().insert(group_use);
            }
            full_group_ancestry.insert(group_use);
            Self::update_sgroup_uses_map(
                &group_use,
                full_group_ancestry,
                cur_mapping,
                group_names,
                sgroups,
            );
            full_group_ancestry.remove(&group_use);
        }
        group_names.remove(parent_group);
    }

    /// Builds an `sgroup_uses_map`, which maps:
    /// static group names -> all of the static groups that it triggers the go ports
    /// of (even recursively).
    /// Example: group A {B[go] = 1;} group B {C[go] = 1} group C{}
    /// Would map: A -> {B,C} and B -> {C}
    fn build_sgroup_uses_map(
        sgroups: &Vec<ir::RRC<ir::StaticGroup>>,
    ) -> HashMap<ir::Id, HashSet<ir::Id>> {
        let mut names: HashSet<ir::Id> = sgroups
            .iter()
            .map(|sgroup| sgroup.borrow().name())
            .collect();
        let mut cur_mapping = HashMap::new();
        while !names.is_empty() {
            let random_group = *names.iter().next().unwrap();
            Self::update_sgroup_uses_map(
                &random_group,
                &mut HashSet::from([random_group]),
                &mut cur_mapping,
                &mut names,
                sgroups,
            )
        }
        cur_mapping
    }

    pub fn get_coloring(
        sgroups: &Vec<ir::RRC<ir::StaticGroup>>,
        control: &ir::Control,
    ) -> HashMap<ir::Id, ir::Id> {
        // `sgroup_uses_map` builds a mapping of static groups -> groups that
        // it (even indirectly) triggers the `go` port of.
        let sgroup_uses_map = Self::build_sgroup_uses_map(&sgroups);
        // Build conflict graph and get coloring.
        let mut conflict_graph: GraphColoring<ir::Id> =
            GraphColoring::from(sgroups.iter().map(|g| g.borrow().name()));
        Self::add_par_conflicts(
            &control,
            &sgroup_uses_map,
            &mut conflict_graph,
        );
        Self::add_go_port_conflicts(&sgroup_uses_map, &mut conflict_graph);
        let coloring = conflict_graph.color_greedy(None, true);
        coloring
    }
}
