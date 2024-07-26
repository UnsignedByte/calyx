use crate::traversal::{
    Action, ConstructVisitor, Named, ParseVal, PassOpt, VisResult, Visitor,
};
use calyx_ir::{self as ir, LibrarySignatures};
use calyx_utils::CalyxResult;
use std::collections::HashMap;

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
    num_children: u64,
}

impl NewFSMs {
    fn compute_opts_aux(
        lst: &Vec<u64>,
        map: &mut HashMap<(u64, u64), (u64, Option<u64>)>,
        avg: u64,
        (t, l): (u64, u64),
    ) -> u64 {
        let opt = (l..=t)
            .map(|i| {
                let sub_query = (i - 1, l - 1);
                let t_next_usize: usize = sub_query.0.try_into().unwrap();
                let subprob_opt = match (map.get(&sub_query), l == 1, i == l) {
                    (Some((v, _)), ..) => *v,
                    (None, true, _) => {
                        avg.abs_diff(lst[0..=t_next_usize].iter().sum())
                    }
                    (None, _, true) => lst[0..=t_next_usize]
                        .iter()
                        .map(|v| avg.abs_diff(*v))
                        .sum(),
                    (None, false, false) => {
                        Self::compute_opts_aux(lst, map, avg, sub_query)
                    }
                };
                let curr_addition = avg.abs_diff(
                    lst[i.try_into().unwrap()..=t.try_into().unwrap()]
                        .iter()
                        .sum(),
                );
                map.insert((i - 1, l - 1), (subprob_opt, Some(curr_addition)));
                subprob_opt + curr_addition
            })
            .min_by(u64::cmp)
            .expect("seq block has no statments");
        map.insert((t, l), (opt, None));
        opt
    }

    fn backtrack(
        map: &HashMap<(u64, u64), (u64, Option<u64>)>,
        (mut t, mut l): (u64, u64),
    ) {
        let mut splits: Vec<u64> = Vec::new();
        while l > 0 {
            let ((opt, _), mut split) = (map.get(&(t, l)).unwrap(), 0);
            for i in (l..=t) {}
        }
    }

    fn compute_opts(
        lst: &Vec<u64>,
        num_splits: u64,
    ) -> (u64, HashMap<(u64, u64), u64>) {
        let spots_to_split: u64 = lst.len().try_into().unwrap();
        let mut opt_values: HashMap<(u64, u64), u64> = HashMap::new();

        for k in 0..(num_splits + 1) {
            for t in 0..(spots_to_split + 1) {
                // check if base cases have been memoized
                // if let None = opt_values.get(&(t,k)) &
                if k == t || k == 0 {
                    match opt_values.get(&(t, k)) {
                        // compute base cases
                        None => match k {
                            0 => {}
                            _ => {}
                        },
                        Some(opt) => (),
                    }
                } else {
                    let find_min: Vec<u64> = Vec::new();
                    match opt_values.get(&(t, k)) {
                        None => (),
                        Some(opt) => (),
                    }
                }
            }
        }
        (1, HashMap::new())
    }
}

impl Named for NewFSMs {
    fn name() -> &'static str {
        "new-fsm"
    }

    fn description() -> &'static str {
        "Change a sequential dynamic schedule to read from two smaller FSMs"
    }

    fn opts() -> Vec<PassOpt> {
        vec![
            PassOpt::new(
                "new-fsm-threshold",
                "Seq blocks with a size larger than this threshold get split into two different FSMs",
                ParseVal::Num(i64::MAX),
                PassOpt::parse_num,
            ),
            PassOpt::new(
                "num-children", 
                "Number of children to seq's to split parent seq. into", 
                ParseVal::Num(0),
                PassOpt::parse_num
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
            num_children: opts[&"num-children"]
                .pos_num()
                .expect("requires non-negative num. children parameter"),
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
            let approx_stmt_size: u64 = ir::Control::approx_size(
                stmt,
                APPROX_ENABLE_SIZE,
                APPROX_WHILE_REPEAT_SIZE,
                APPROX_IF_SIZE,
            );

            statement_sizes.push(approx_stmt_size);
            total_size += approx_stmt_size;
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
                    _ => unreachable!(),
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
