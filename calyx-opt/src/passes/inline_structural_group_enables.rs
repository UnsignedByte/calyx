use std::collections::{HashMap, HashSet};

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

impl Visitor for InlineStructuralGroupEnables {
    fn start(
        &mut self,
        comp: &mut calyx_ir::Component,
        _sigs: &calyx_ir::LibrarySignatures,
        _comps: &[calyx_ir::Component],
    ) -> VisResult {
        // get all groups in a map for easy access?
        let mut group_name_to_ref = HashMap::new();
        for group_ref in comp.groups.iter() {
            group_name_to_ref.insert(group_ref.borrow().name(), group_ref);
        }
        // look for structural enables
        for group_ref in comp.groups.iter() {
            let group = &group_ref.borrow();
            let mut asgns_to_add = Vec::new();
            for assignment_ref in group.assignments.iter() {
                let dst_borrow = assignment_ref.dst.borrow();
                if let ir::PortParent::Group(child_group_ref) =
                    &dst_borrow.parent
                {
                    if dst_borrow.name == "go" {
                        // structural enable!
                        let child_group_go_guard = assignment_ref.guard.clone();
                        // let done_port_ref =
                        //     parent_group_ref.upgrade().borrow().get("done");
                        for asgn in child_group_ref
                            .upgrade()
                            .borrow()
                            .assignments
                            .iter()
                        {
                            // FIXME: it isn't as easy as just copying over all of the assignments?
                            // (1) can't copy over the done port assignment, but we need to keep the guard for that.
                            // within the rest of this group, need to iterate over all uses of child[done] and replace
                            // with the guard for the done. (iterate until saturation?)
                            let mut modified_asgn = asgn.clone();
                            modified_asgn.guard = Box::new(Guard::And(
                                child_group_go_guard.clone(),
                                asgn.guard.clone(),
                            ));
                            asgns_to_add.push(modified_asgn);
                        }
                    }
                }
            }
        }

        Ok(Action::Continue)
    }
}
