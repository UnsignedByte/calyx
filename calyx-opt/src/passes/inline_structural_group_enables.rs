use std::{collections::HashMap};

use crate::traversal::{Action, ConstructVisitor, Named, VisResult, Visitor};
use calyx_ir::{self as ir, Guard};

// Removes structural enables by inlining callee into caller group.
// Used by the profiler.
pub struct InlineStructuralGroupEnables {}

impl Named for InlineStructuralGroupEnables {
    fn name() -> &'static str {
        "inline-structural-group-enables"
    }

    fn description() -> &'static str {
        "Squash all structural group enables"
    }
}

impl ConstructVisitor for InlineStructuralGroupEnables {
    fn from(_ctx: &calyx_ir::Context) -> calyx_utils::CalyxResult<Self>
    where
        Self: Sized + Named,
    {
        Ok(InlineStructuralGroupEnables {})
    }

    fn clear_data(&mut self) {}
}

impl InlineStructuralGroupEnables {}

impl Visitor for InlineStructuralGroupEnables {
    fn start(
        &mut self,
        comp: &mut calyx_ir::Component,
        sigs: &calyx_ir::LibrarySignatures,
        _comps: &[calyx_ir::Component],
    ) -> VisResult {
        let group_names = comp
            .groups
            .iter()
            .map(|g| g.borrow().name())
            .collect::<Vec<_>>();
        let mut builder = ir::Builder::new(comp, sigs);
        // make cells for all groups preemptively and get dead-cell-removal to remove them. lol
        let mut group_names_to_cells = HashMap::new();
        for group_name in group_names.iter() {
            let group_go_cell_name = format!("{}_enable_go", group_name);
            let group_done_cell_name = format!("{}_enable_done", group_name);
            let group_go_cell =
                builder.add_primitive(group_go_cell_name, "std_wire", &[1]);
            let group_done_cell =
                builder.add_primitive(group_done_cell_name, "std_wire", &[1]);
            group_names_to_cells
                .insert(group_name, (group_go_cell, group_done_cell));
        }
        // look for structural enables
        for group_ref in comp.groups.iter() {
            let mut group = group_ref.borrow_mut();
            let mut asgns_to_add = Vec::new();
            let mut child_groups = Vec::new();
            let mut keep_asgn = Vec::new();
            for assignment_ref in group.assignments.iter() {
                let dst_borrow = assignment_ref.dst.borrow();
                if let ir::PortParent::Group(child_group_ref) =
                    &dst_borrow.parent
                {
                    if dst_borrow.name == "go" {
                        keep_asgn.push(false);
                        // structural enable!
                        let child_group_go_guard = assignment_ref.guard.clone();
                        child_groups.push(child_group_ref.upgrade().borrow().name());
                        // child_go_cell
                        let child_go_cell_opt =
                            group_names_to_cells.get(&child_group_ref.upgrade().borrow().name());
                        let child_go_cell = 
                        match child_go_cell_opt {
                            Some((go, _)) => go,
                            None => panic!("Pass-specific cells for the group {} should exist!", child_group_ref.upgrade().borrow().name())
                        };
                        let mut new_asgn = assignment_ref.clone();
                        new_asgn.dst = (*child_go_cell).borrow().get("in");
                        asgns_to_add.push(new_asgn);
                        for child_asgn in child_group_ref
                            .upgrade()
                            .borrow()
                            .assignments
                            .iter()
                        {
                            let mut child_modified_asgn = child_asgn.clone();
                            child_modified_asgn.guard = Box::new(Guard::and(
                                Guard::port(child_go_cell.borrow().get("out")),
                                *child_asgn.guard.clone(),
                            ));
                            let child_dst_borrow = child_asgn.dst.borrow();
                            if let ir::PortParent::Group(_) =
                                &child_dst_borrow.parent
                            {
                                if child_dst_borrow.name == "done" {
                                    let child_done_cell = 
                                    match group_names_to_cells.get(&child_group_ref.upgrade().borrow().name()) {
                                        Some((_, done)) => done,
                                        None => panic!("Pass-specific cells for the group {} should exist!", child_group_ref.upgrade().borrow().name())
                                    };
                                    child_modified_asgn.dst = child_done_cell.borrow().get("in");
                                    asgns_to_add.push(child_modified_asgn);
                                }
                            } else {
                                asgns_to_add.push(child_modified_asgn);
                            }
                        }
                    } else {
                        keep_asgn.push(true);
                    }
                } else {
                    keep_asgn.push(true);
                }
            }
            let mut idx = 0;
            // second iteration to modify all uses of any child's done signal
            for assignment_ref in group.assignments.iter() {
                // cases where the source is the child's done signal
                let src_borrow = assignment_ref.src.borrow();
                let child_done_cell_opt = 
                if let ir::PortParent::Group(child_group_ref) =
                    &src_borrow.parent
                {
                    match group_names_to_cells.get(&child_group_ref.upgrade().borrow().name()) {
                        Some((_, done)) => Some(done),
                        None => panic!("Pass-specific cells for the group {} should exist!", child_group_ref.upgrade().borrow().name())
                    }
                } else {
                    // the source isn't a child done.
                    None
                };
                match child_done_cell_opt {
                    Some(child_done_cell) => {
                        let mut parent_modified_asgn = assignment_ref.clone();
                        parent_modified_asgn.src = child_done_cell.borrow().get("out");
                        keep_asgn[idx] = false;
                        asgns_to_add.push(parent_modified_asgn);
                    },
                    None => ()
                }                
                // cases where the guard uses childrens' done signal
                let mut modified_guard = assignment_ref.guard.clone();
                let mut replaced_guard = false;
                for child_group_name in
                    child_groups.clone().into_iter()
                {
                    let child_done_cell = 
                    match group_names_to_cells.get(&child_group_name) {
                        Some((_, done)) => done,
                        None => panic!("Pass-specific cells for the group {} should exist!", child_group_name)
                    };
                    let child_done_cell_port = Guard::port(child_done_cell.borrow().get("out"));
                    replaced_guard |= modified_guard.search_replace_group_done(
                        child_group_name,
                        &child_done_cell_port,
                    );
                }
                if replaced_guard {
                    keep_asgn[idx] = false;
                    let mut modified_asgn = assignment_ref.clone();
                    modified_asgn.guard = modified_guard;
                    asgns_to_add.push(modified_asgn);
                }
                // increment idx to update keep_asgn
                idx += 1;
            }
            debug_assert_eq!(keep_asgn.len(), group.assignments.len());
            let mut keep_iter = keep_asgn.into_iter();
            group.assignments.retain(|_| keep_iter.next().unwrap());
            for asgn_to_add in asgns_to_add.into_iter() {
                group.assignments.push(asgn_to_add);
            }
            // iterate a second time to catch all of the assignments we need to modify (guards that use child groups' go and done conditions)
        }

        Ok(Action::Continue)
    }
}
