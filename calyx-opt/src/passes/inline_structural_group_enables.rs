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
        for group_ref in comp.groups.iter() {
            let mut group = group_ref.borrow_mut();
            let mut asgns_to_add = Vec::new();
            let mut child_group_to_asgns = HashMap::new();
            let mut done_guards = HashMap::new();
            let mut keep_asgn = Vec::new(); // tracker to see whether assignment from original group should be preserved
            for assignment_ref in group.assignments.iter() {
                let dst_borrow = assignment_ref.dst.borrow();
                if let ir::PortParent::Group(child_group_ref) =
                    &dst_borrow.parent
                {
                    if dst_borrow.name == "go" {
                        keep_asgn.push(false);
                        println!("Pushing false for {:?}", assignment_ref);
                        // structural enable!
                        // if the src is a port, then we want to and it to the guard.
                        let src_borrow = assignment_ref.src.borrow();
                        println!("Getting port {:?}", src_borrow);
                        let child_group_go_guard =
                            if let ir::PortParent::Group(_) = &src_borrow.parent
                            {
                                Box::new(Guard::and(
                                    *assignment_ref.guard.clone(),
                                    Guard::port(ir::rrc(src_borrow.clone())),
                                ))
                            } else {
                                assignment_ref.guard.clone()
                            };
                        let mut child_modified_asgns = Vec::new();
                        for child_asgn in child_group_ref
                            .upgrade()
                            .borrow()
                            .assignments
                            .iter()
                        {
                            let mut child_modified_asgn = child_asgn.clone();
                            child_modified_asgn.guard = Box::new(Guard::and(
                                *child_group_go_guard.clone(),
                                *child_asgn.guard.clone(),
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
                                        Box::new(Guard::and(
                                            *(child_group_done_guard).clone(),
                                            Guard::port(ir::rrc(
                                                child_done_source.clone(),
                                            )),
                                        )),
                                    );
                                }
                            } else {
                                child_modified_asgns
                                    .push(child_modified_asgn.clone());
                                asgns_to_add.push(child_modified_asgn);
                            }
                        }
                        child_group_to_asgns.insert(
                            child_group_ref.upgrade().borrow().name(),
                            child_modified_asgns,
                        );
                    } else {
                        keep_asgn.push(true);
                    }
                } else {
                    keep_asgn.push(true);
                }
            }
            println!("PRINTING DONE GUARDS");
            for (dg_name, dg_val) in done_guards.clone().into_iter() {
                println!("name: {}, value: {:?}", dg_name, dg_val);
            }
            let mut idx = 0;
            let mut all_assignments = 
            // second iteration to modify all uses of any child's done signal
            for assignment_ref in group.assignments.iter() {
                // cases where the source is the child's done signal
                let src_borrow = assignment_ref.src.borrow();
                if keep_asgn[idx] == false {
                    // skip any assignments that we already know are true
                    idx += 1;
                    continue;
                }
                if let ir::PortParent::Group(child_group_ref) =
                    &src_borrow.parent
                {
                    // assignment gets transformed into
                    // dst = guard & *child[done]* : 1
                    match &done_guards
                        .get(&child_group_ref.upgrade().borrow().name())
                    {
                        Some(child_done_guard) => {
                            let mut parent_modified_asgn =
                                assignment_ref.clone();
                            parent_modified_asgn.src = one.borrow().get("out");
                            parent_modified_asgn.guard = Box::new(Guard::and(
                                (*assignment_ref.guard).clone(),
                                *(*child_done_guard).clone(),
                            ));
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
                    keep_asgn[idx] = false;
                    let mut modified_asgn = assignment_ref.clone();
                    modified_asgn.guard = modified_guard;
                    asgns_to_add.push(modified_asgn);
                }
                // increment idx to update keep_asgn
                idx += 1;
            }
            debug_assert_eq!(keep_asgn.len(), group.assignments.len());
            println!("vec: {:?}", keep_asgn);
            let mut keep_iter = keep_asgn.into_iter();
            group.assignments.retain(|_| keep_iter.next().unwrap());
            println!("Size of assignments: {}", group.assignments.len());
            for asgn_to_add in asgns_to_add.into_iter() {
                group.assignments.push(asgn_to_add);
            }

            // iterate a second time to catch all of the assignments we need to modify (guards that use child groups' go and done conditions)
        }

        Ok(Action::Continue)
    }
}
