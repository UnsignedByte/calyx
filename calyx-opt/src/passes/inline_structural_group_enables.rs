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
        // NOTE: going to work on a three step process.
        // (1) iterate solely to get each child and their go and done guards, and assignments. If go's src is a port then we need to & the port.
        // (2) iterate through original assignments, replace/remove all assignments that refer to children.
        // look for structural enables
        let mut done_guards: HashMap<
            calyx_ir::Id,
            Box<Guard<calyx_ir::Nothing>>,
        > = HashMap::new();
        for group_ref in comp.groups.iter() {
            let mut group = group_ref.borrow_mut();
            let mut new_group_asgns = Vec::new();
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
                            // add new assignment
                            // asgns_to_add.push(parent_modified_asgn);
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
                        // let src_borrow = converted_assignment.src.borrow();
                        // println!("Getting port {:?}", src_borrow);
                        // let child_group_go_guard =
                        //     if let ir::PortParent::Group(_) = &src_borrow.parent
                        //     {
                        //         Box::new(Guard::and(
                        //             *assignment_ref.guard.clone(),
                        //             Guard::port(ir::rrc(src_borrow.clone())),
                        //         ))
                        //     } else {
                        //         assignment_ref.guard.clone()
                        //     };
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

                                // if child_dst_borrow.name == "done" {
                                //     let child_done_source =
                                //         child_asgn.src.borrow();
                                //     // child group's done condition. need to collect the guard to done
                                //     let child_group_done_guard =
                                //         child_asgn.guard.clone();
                                //     done_guards.insert(
                                //         child_group_ref
                                //             .upgrade()
                                //             .borrow()
                                //             .name(),
                                //         Box::new(Guard::and(
                                //             *(child_group_done_guard).clone(),
                                //             Guard::port(ir::rrc(
                                //                 child_done_source.clone(),
                                //             )),
                                //         )),
                                //     );
                                // }
                            } else {
                                child_modified_asgn.guard =
                                    Box::new(Guard::and(
                                        *child_group_go_guard.clone(),
                                        *child_asgn.guard.clone(),
                                    ));
                                new_group_asgns.push(child_modified_asgn);
                            }
                        }
                        continue; // do NOT add an assignment with go!!!!
                    }
                }
                new_group_asgns.push(converted_assignment.clone());
            }
            // println!("PRINTING DONE GUARDS");
            // for (dg_name, dg_val) in done_guards.clone().into_iter() {
            //     println!("name: {}, value: {:?}", dg_name, dg_val);
            // }
            // iterate through all of the created assignments and modify all guards that refer to child enable
            let mut guard_fixed_assignments = Vec::new();
            for assignment_ref in new_group_asgns.iter() {
                // cases where the guard uses childrens' done signal
                let mut modified_guard = assignment_ref.guard.clone();
                let mut replaced_guard = false;
                for (child_group, child_group_guard) in
                    done_guards.clone().into_iter()
                {
                    println!(
                        "child group name: {}, guard: {:?}",
                        child_group, child_group_guard
                    );
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

            // let mut idx = 0;
            // // let mut all_assignments =
            // // second iteration to modify all uses of any child's done signal
            // for assignment_ref in group.assignments.iter() {
            //     // cases where the source is the child's done signal
            //     let src_borrow = assignment_ref.src.borrow();
            //     if keep_asgn[idx] == false {
            //         // skip any assignments that we already know are true
            //         idx += 1;
            //         continue;
            //     }
            //     if let ir::PortParent::Group(child_group_ref) =
            //         &src_borrow.parent
            //     {
            //         // assignment gets transformed into
            //         // dst = guard & *child[done]* : 1
            //         match &done_guards
            //             .get(&child_group_ref.upgrade().borrow().name())
            //         {
            //             Some(child_done_guard) => {
            //                 let mut parent_modified_asgn =
            //                     assignment_ref.clone();
            //                 parent_modified_asgn.src = one.borrow().get("out");
            //                 parent_modified_asgn.guard = Box::new(Guard::and(
            //                     (*assignment_ref.guard).clone(),
            //                     *(*child_done_guard).clone(),
            //                 ));
            //                 keep_asgn[idx] = false;
            //                 // add new assignment
            //                 new_group_asgns.push(parent_modified_asgn);
            //             }
            //             None => panic!(
            //                 "Child group ({})'s done guard should be in map",
            //                 child_group_ref.upgrade().borrow().name()
            //             ),
            //         }
            //     }
            //     // cases where the guard uses childrens' done signal
            //     let mut modified_guard = assignment_ref.guard.clone();
            //     let mut replaced_guard = false;
            //     for (child_group, child_group_guard) in
            //         done_guards.clone().into_iter()
            //     {
            //         println!(
            //             "child group name: {}, guard: {:?}",
            //             child_group, child_group_guard
            //         );
            //         replaced_guard |= modified_guard.search_replace_group_done(
            //             child_group,
            //             &child_group_guard,
            //         );
            //     }
            //     if replaced_guard {
            //         keep_asgn[idx] = false;
            //         let mut modified_asgn = assignment_ref.clone();
            //         modified_asgn.guard = modified_guard;
            //         new_group_asgns.push(modified_asgn);
            //     }
            //     // increment idx to update keep_asgn
            //     idx += 1;
            // }
            // debug_assert_eq!(keep_asgn.len(), group.assignments.len());
            // println!("vec: {:?}", keep_asgn);
            // let mut keep_iter = keep_asgn.into_iter();
            // group.assignments.retain(|_| keep_iter.next().unwrap());
            // println!("Size of assignments: {}", group.assignments.len());
            // for asgn_to_add in new_group_asgns.into_iter() {
            //     group.assignments.push(asgn_to_add);
            // }

            // iterate a second time to catch all of the assignments we need to modify (guards that use child groups' go and done conditions)
        }

        Ok(Action::Continue)
    }
}
