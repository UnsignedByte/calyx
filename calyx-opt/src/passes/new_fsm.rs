use crate::traversal::{
    Action, ConstructVisitor, Named, ParseVal, PassOpt, VisResult, Visitor,
};
use calyx_ir::{self as ir, LibrarySignatures};
use calyx_utils::CalyxResult;

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

pub struct NewFSMs {
    threshold: u64,
}

impl Named for NewFSMs {
    fn name() -> &'static str {
        "new-fsm"
    }

    fn description() -> &'static str {
        "Allocate new FSMs within a dynamic group"
    }

    fn opts() -> Vec<PassOpt> {
        vec![
            PassOpt::new(
                "new-fsm-threshold",
                "Seq blocks with a size larger than this threshold get split into two different FSMs",
                ParseVal::Num(i64::MAX),
                PassOpt::parse_num,
            )
        ]
    }
}

impl ConstructVisitor for NewFSMs {
    fn from(ctx: &ir::Context) -> CalyxResult<Self>
    where
        Self: Sized + Named,
    {
        let opts = Self::get_opts(ctx);
        Ok(NewFSMs {
            threshold: opts[&"new-fsm-threshold"]
                .pos_num()
                .expect("requires non-negative threshold parameter"),
        })
    }
    fn clear_data(&mut self) {
        /* keep threshold across components */
    }
}

impl Visitor for NewFSMs {
    fn finish_seq(
        &mut self,
        s: &mut ir::Seq,
        _comp: &mut ir::Component,
        _sigs: &LibrarySignatures,
        _comps: &[ir::Component],
    ) -> VisResult {
        // Decide where to split based on the total number of Invoke Control objects we find.
        // Store approx sizes of each statement so we know where to split

        // stores an approx size of each statement in the Seq block
        let mut statement_sizes: Vec<u64> = Vec::new();

        // element i stores size_1 + ... + size_i
        let mut total_sizes: Vec<u64> = Vec::new();

        // stores total approx size of the Seq block
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
            total_sizes.push(total_size);
        }

        // exit out if threshold for splitting exceeds the estimated total size
        if total_size < self.threshold {
            return Ok(Action::Continue);
        }

        // logic to find the index of the seq which yields the best split
        let (min_indx_opt, _, _) = total_sizes
            .iter()
            .map(|sub_total| {
                (*sub_total).abs_diff(total_size.abs_diff(*sub_total))
            })
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
                            (Some(curr_indx), Some(curr_diff), curr_indx + 1)
                        } else {
                            (Some(min_indx), Some(min_diff), curr_indx + 1)
                        }
                    }
                },
            );

        // at best split, split seq into first and second sub-seq blocks, each of which get @new_fsm
        match min_indx_opt {
            None => Ok(Action::Continue), // unreachable
            Some(min_indx) => {
                let (fst_stmts, snd_stmts) = {
                    let mut fst: Vec<ir::Control> = Vec::new();
                    let mut snd: Vec<ir::Control> = Vec::new();

                    for (i, c) in s.stmts.drain(..).enumerate() {
                        if i <= (min_indx as usize) {
                            fst.push(c)
                        } else {
                            snd.push(c)
                        }
                    }

                    (fst, snd)
                };

                // place @new_fsm attribute at children seq
                let mut child_attrs = s.attributes.clone();
                child_attrs.insert(ir::BoolAttr::NewFSM, 1);

                // give first child seq @new_fsm attribute as well
                let fst_seq = ir::Control::Seq(ir::Seq {
                    stmts: fst_stmts,
                    attributes: child_attrs.clone(),
                });

                // same for second child seq
                let snd_seq = ir::Control::Seq(ir::Seq {
                    stmts: snd_stmts,
                    attributes: child_attrs.clone(),
                });

                // change parent statements to have exactly two children seqs according to split, along with old attributes
                let parent_seq = ir::Control::Seq(ir::Seq {
                    stmts: vec![fst_seq, snd_seq],
                    attributes: s.attributes.clone(),
                });
                let split_seqs = Action::change(parent_seq);

                Ok(split_seqs)
            }
        }
    }
}
