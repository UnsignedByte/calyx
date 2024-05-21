use crate::traversal::{Action, Named, VisResult, Visitor};
use calyx_ir::{self as ir, LibrarySignatures};

/// Places @new_fsm attributes at key locations during traversal of dynamic control
/// For example, transforming the following:
/// ```
/// control {
///     seq {G_1; G_2; ... ; G_n;}
/// }
/// ```
/// into:
/// ```
/// control {
///     seq {
///         @new_fsm seq {G_1; G_2; ... ; G_{n/2};};
///         @new_fsm seq {G_{n/2 + 1}; ...; G_n};
///     }
/// }
/// ```

const APPROX_ENABLE_SIZE: u64 = 1;
const APPROX_IF_SIZE: u64 = 3;
const APPROX_WHILE_REPEAT_SIZE: u64 = 3;

#[derive(Default)]
pub struct NewFSMs {
    /// threshold number of invokations at which to assign new FSM
    threshold: u64,
}

impl Named for NewFSMs {
    fn name() -> &'static str {
        "new-fsm"
    }

    fn description() -> &'static str {
        "Allocate new FSMs within a dynamic group"
    }
}

impl Visitor for NewFSMs {
    fn start_seq(
        &mut self,
        s: &mut ir::Seq,
        _comp: &mut ir::Component,
        _sigs: &LibrarySignatures,
        _comps: &[ir::Component],
    ) -> VisResult {
        // Decide where to split based on the total number of Invoke Control objects we find.
        // Store approx sizes of each statement so we know where to split
        let mut statement_sizes: Vec<u64> = Vec::new();
        let mut total_size: u64 = 0;

        for stmt in s.stmts.iter() {
            let approx_stmt_size = ir::Control::approx_size(
                stmt,
                APPROX_ENABLE_SIZE,
                APPROX_WHILE_REPEAT_SIZE,
                APPROX_IF_SIZE,
            );
            statement_sizes.push(approx_stmt_size);
            total_size = total_size + approx_stmt_size;
        }

        // exit out if threshold for splitting exceeds the estimated total size
        if total_size >= self.threshold {
            return Ok(Action::Continue);
        }

        // logic to find the index of the seq which yields the best split
        let (min_indx_opt, _, _): (Option<u64>, Option<u64>, u64) =
            statement_sizes
                .iter()
                .map(|size| ((*size).abs_diff(total_size.abs_diff(*size))))
                .fold(
                    (None, None, 0),
                    |(min_indx_opt, min_diff_opt, curr_indx), curr_diff| match (
                        min_indx_opt,
                        min_diff_opt,
                    ) {
                        (None, Some(..)) | (Some(..), None) => {
                            unreachable!()
                        }
                        (None, None) => {
                            (Some(curr_indx), Some(curr_diff), curr_indx + 1)
                        }
                        (Some(min_indx), Some(min_diff)) => {
                            if curr_diff < min_diff {
                                (
                                    Some(curr_indx),
                                    Some(curr_diff),
                                    curr_indx + 1,
                                )
                            } else {
                                (Some(min_indx), Some(min_diff), curr_indx + 1)
                            }
                        }
                    },
                );

        let (fst_stmts, snd_stmts) = match min_indx_opt {
            // a case against finding an initial min diff that is too low; can do better, first shot
            None => unreachable!(),

            // split up to and including index `indx`
            Some(min_indx) => {
                let mut fst: Vec<ir::Control> = Vec::new();
                let mut snd: Vec<ir::Control> = Vec::new();

                for (i, c) in s.stmts.drain(..).enumerate() {
                    if i < (min_indx as usize) {
                        fst.push(c)
                    } else {
                        snd.push(c)
                    }
                }

                (fst, snd)
            }
        };

        // place @new_fsm attribute at parent seq
        s.attributes.insert(ir::BoolAttr::NewFSM, 1);

        // give first child seq @new_fsm attribute as well
        let fst_seq = ir::Control::Seq(ir::Seq {
            stmts: fst_stmts,
            attributes: s.attributes.clone(),
        });

        // same for second child seq
        let snd_seq = ir::Control::Seq(ir::Seq {
            stmts: snd_stmts,
            attributes: s.attributes.clone(),
        });

        // change parent statements to have exactly two children seqs according to split
        s.stmts = vec![fst_seq, snd_seq];

        return Ok(Action::Continue);
    }
}
