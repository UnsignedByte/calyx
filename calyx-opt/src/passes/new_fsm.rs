use crate::traversal::{
    Action, ConstructVisitor, Named, ParseVal, PassOpt, VisResult, Visitor,
};
use calyx_ir::{self as ir, LibrarySignatures};
use calyx_utils::CalyxResult;
use std::collections::{HashMap, VecDeque};

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
    /// Helper function for the dynamic programming problem.
    /// Taking the left-hand `t+1` elements of a list,
    /// this function fills a map from the tuple (`t`: # of spots to split , `l`: # splitters left) to
    /// the minimum possible cost of splitting these numbers `l` times.
    fn compute_opts(
        lst: &Vec<u64>,
        map: &mut HashMap<(u64, u64), u64>,
        avg: u64,
        (t, l): (u64, u64),
    ) -> u64 {
        let opt = (l..=t)
            .map(|i| {
                let (sub_query, t_next_usize) =
                    ((i - 1, l - 1), (i - 1).try_into().unwrap());
                let (memoized, subprob_opt) = match map.get(&sub_query) {
                    // if memoized, use cached val. instead of recomputing
                    Some(v) => (true, *v),
                    None => match (l == 1, i == l) {
                        (true, _) => (
                            // base case where sub_query :- (_, 0)
                            false,
                            avg.abs_diff(lst[0..=t_next_usize].iter().sum()),
                        ),
                        (_, true) => (
                            // base case where sub_query :- (n, n)
                            false,
                            lst[0..=t_next_usize]
                                .iter()
                                .map(|v| avg.abs_diff(*v))
                                .sum(),
                        ),
                        (false, false) => (
                            // inductive case; break into smaller sub-problems
                            false,
                            Self::compute_opts(lst, map, avg, sub_query),
                        ),
                    },
                };
                // save insert time if alr. memoized
                if !memoized {
                    map.insert((i - 1, l - 1), subprob_opt);
                }
                // return sub-prob opt. value + cost of putting splitter at ith slot
                subprob_opt
                    + avg.abs_diff(
                        lst[i.try_into().unwrap()..=t.try_into().unwrap()]
                            .iter()
                            .sum(),
                    )
            })
            .min_by(u64::cmp)
            .expect("seq block has no statments");
        map.insert((t, l), opt);
        opt
    }

    /// Helper function for the dynamic programming problem. Given a filled map
    /// from values (`t`: # of spots to split , `l`: # splitters left) to minimum costs,
    /// finds a backward path of indices to optimally split the list and fills these
    /// indices into a list `splits`.
    fn backtrack(
        map: &HashMap<(u64, u64), u64>,
        lst: &Vec<u64>,
        splits: &mut VecDeque<u64>,
        avg: u64,
        (t, l): (u64, u64),
    ) {
        let opt = map.get(&(t, l)).unwrap();
        for i in l..=t {
            let sp_opt = map.get(&(i - 1, l - 1)).unwrap();
            if *opt
                == sp_opt
                    + avg.abs_diff(
                        lst[i.try_into().unwrap()..=t.try_into().unwrap()]
                            .iter()
                            .sum(),
                    )
            {
                splits.push_front(i - 1);
                if l > 1 {
                    Self::backtrack(map, lst, splits, avg, (i - 1, l - 1));
                }
                break;
            }
        }
    }
    /// This function solves the problem:
    /// Given a number of groups to create `k` and a list of `n` integers `lst`,
    /// how do we optimally partition the list such that:
    ///
    /// 1. All groups are non-empty
    /// 2. All formed groups are contiguous w.r.t. original ordering in `lst`
    /// 3. The sum of the elements in each group are as close as possible to the
    ///    sum of all `n` elements in `lst` divided by the number of groups `k`
    fn compute_split_indices(lst: &Vec<u64>, num_groups: u64) -> Vec<u64> {
        let (mut map, mut splits) = (HashMap::new(), VecDeque::new());
        let (sum, len): (u64, u64) =
            (lst.iter().sum(), lst.len().try_into().unwrap());
        let (query, avg) = ((len - 1, num_groups - 1), sum / num_groups);
        Self::compute_opts(lst, &mut map, avg, query);
        Self::backtrack(&map, lst, &mut splits, avg, query);
        Vec::<u64>::from(splits)
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
