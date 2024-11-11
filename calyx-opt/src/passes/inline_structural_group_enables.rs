use std::collections::HashMap;

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
        let mut builder = ir::Builder::new(comp, sigs);
        let one = builder.add_constant(1, 1);
        // look for structural enables
        let mut done_guards: HashMap<
            calyx_ir::Id,
            Box<Guard<calyx_ir::Nothing>>,
        > = HashMap::new();
        for group_ref in comp.groups.iter() {
            let mut group = group_ref.borrow_mut();
            let mut port_processed_asgns = Vec::new();
            // first, we will keep an assignment if neither the src or the dst is a child's port. We will modify guards everywhere later.
            for assignment_ref in group.assignments.iter() {
                let mut converted_assignment = assignment_ref.clone();
                let src_borrow = assignment_ref.src.borrow();
                if let ir::PortParent::Group(child_group_ref) =
                    &src_borrow.parent
                {
                    // assignment gets transformed into
                    // dst = guard & *child[done]* : 1
                    match &done_guards
                        .get(&child_group_ref.upgrade().borrow().name())
                    {
                        Some(child_done_guard) => {
                            converted_assignment.src = one.borrow().get("out");
                            converted_assignment.guard = Box::new(Guard::and(
                                (*assignment_ref.guard).clone(),
                                *(*child_done_guard).clone(),
                            ));
                        }
                        None => panic!(
                            "Child group ({})'s done guard should be in done_guards map",
                            child_group_ref.upgrade().borrow().name()
                        ),
                    }
                }
                let dst_borrow = converted_assignment.dst.borrow();
                if let ir::PortParent::Group(child_group_ref) =
                    &dst_borrow.parent
                {
                    if dst_borrow.name == "done" {
                        // should be our current group's done.
                        // FIXME: should I assert for the above?
                        // copy guard & source into done_guards
                        done_guards.insert(
                            group.name(),
                            Box::new(Guard::and(
                                *converted_assignment.guard.clone(),
                                Guard::port(ir::rrc(
                                    converted_assignment.src.borrow().clone(),
                                )),
                            )),
                        );
                    }
                    if dst_borrow.name == "go" {
                        // structural enable!
                        let child_group_go_guard =
                            converted_assignment.guard.clone();
                        for child_asgn in child_group_ref
                            .upgrade()
                            .borrow()
                            .assignments
                            .iter()
                        {
                            let mut child_modified_asgn = child_asgn.clone();
                            let child_dst_borrow = child_asgn.dst.borrow();
                            if let ir::PortParent::Group(_) =
                                &child_dst_borrow.parent
                            {
                                // ignore child's done assignment
                            } else {
                                child_modified_asgn.guard =
                                    Box::new(Guard::and(
                                        *child_group_go_guard.clone(),
                                        *child_asgn.guard.clone(),
                                    ));
                                port_processed_asgns.push(child_modified_asgn);
                            }
                        }
                        continue; // do NOT add an assignment with go!!!!
                    }
                }
                port_processed_asgns.push(converted_assignment.clone());
            }
            // iterate through all of the created assignments and modify all guards that refer to child enable
            let mut guard_fixed_assignments = Vec::new();
            for assignment_ref in port_processed_asgns.iter() {
                // cases where the guard uses childrens' done signal
                let mut modified_guard = assignment_ref.guard.clone();
                let mut replaced_guard = false;
                for (child_group, child_group_guard) in
                    done_guards.clone().into_iter()
                {
                    replaced_guard |= modified_guard.search_replace_group_done(
                        child_group,
                        &child_group_guard,
                    );
                }
                if replaced_guard {
                    let mut modified_asgn = assignment_ref.clone();
                    modified_asgn.guard = modified_guard;
                    guard_fixed_assignments.push(modified_asgn);
                } else {
                    guard_fixed_assignments.push(assignment_ref.clone());
                }
            }
            group.assignments = guard_fixed_assignments;
        }

        Ok(Action::Continue)
    }
}
