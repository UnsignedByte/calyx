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
        // get all groups in a map for easy access?
        // let mut group_name_to_ref = HashMap::new();
        // for group_ref in comp.groups.iter() {
        //     group_name_to_ref.insert(group_ref.borrow().name(), group_ref);
        // }
        // look for structural enables
        for group_ref in comp.groups.iter() {
            let mut group = group_ref.borrow_mut();
            let mut asgns_to_add = Vec::new();
            let mut done_guards = HashMap::new();
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
                        // let done_port_ref =
                        //     parent_group_ref.upgrade().borrow().get("done");
                        for child_asgn in child_group_ref
                            .upgrade()
                            .borrow()
                            .assignments
                            .iter()
                        {
                            // FIXME: it isn't as easy as just copying over all of the assignments?
                            // (1) can't copy over the done port assignment, but we need to keep the guard for that.
                            // within the rest of this group, need to iterate over all uses of child[done] and replace
                            // with the guard for the done. (iterate until saturation?)
                            let mut child_modified_asgn = child_asgn.clone();
                            child_modified_asgn.guard = Box::new(Guard::And(
                                child_group_go_guard.clone(),
                                child_asgn.guard.clone(),
                            ));

                            let child_dst_borrow = child_asgn.dst.borrow();
                            if let ir::PortParent::Group(_) =
                                &child_dst_borrow.parent
                            {
                                if child_dst_borrow.name == "done" {
                                    let child_done_source =
                                        child_asgn.src.borrow();
                                    // child group's done condition. need to collect the guard to done
                                    let child_group_done_guard =
                                        child_asgn.guard.clone();
                                    done_guards.insert(
                                        child_group_ref
                                            .upgrade()
                                            .borrow()
                                            .name(),
                                        Box::new(Guard::And(
                                            child_group_done_guard.clone(),
                                            Box::new(Guard::Port(ir::rrc(
                                                child_done_source.clone(),
                                            ))),
                                        )),
                                    );
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
                if let ir::PortParent::Group(child_group_ref) =
                    &src_borrow.parent
                {
                    // assignment gets transformed into
                    // dst = guard & *child[done]* : 1
                    let done_guards_clone = done_guards.clone();
                    match &done_guards_clone
                        .get(&child_group_ref.upgrade().borrow().name())
                    {
                        Some(child_done_guard) => {
                            let mut parent_modified_asgn =
                                assignment_ref.clone();
                            parent_modified_asgn.src = one.borrow().get("out");
                            parent_modified_asgn.guard = Box::new(Guard::And(
                                assignment_ref.guard.clone(),
                                (*child_done_guard).clone(),
                            ));
                            // FIXME: remove original assignment
                            keep_asgn[idx] = false;
                            // add new assignment
                            asgns_to_add.push(parent_modified_asgn);
                        }
                        None => panic!(
                            "Child group ({})'s done guard should be in map",
                            child_group_ref.upgrade().borrow().name()
                        ),
                    }
                }
                // cases where the guard uses a child's done signal (there can be multiple children though)
                let mut guard = assignment_ref.guard.clone();
                for (child_group, child_group_guard) in done_guards.into_iter()
                {
                    guard.search_replace_group_done(
                        child_group,
                        &child_group_guard,
                    );
                }

                // let new_guard = self.replace_guard(guard);
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
