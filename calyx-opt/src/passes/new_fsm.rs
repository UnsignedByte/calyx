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
    /// Helper function for the dynamic programming problem. Taking the left-hand
    /// `t+1` elements of a list, this function fills a map from the tuple
    /// (`t`: # of spots to split ,`l`: # splitters left) to the minimum
    /// possible cost of splitting these numbers `l` times.
    fn compute_opts(
        lst: &Vec<u64>,
        map: &mut HashMap<(u64, u64), u64>,
        avg: u64,
        (num_spots, num_splitters): (u64, u64),
    ) -> u64 {
        match map.get(&(num_spots, num_splitters)) {
            Some(v) => *v,
            None => {
                let spots = num_spots.try_into().unwrap();
                let opt_value = match (num_spots, num_splitters) {
                    (_, 0) => avg.abs_diff(lst[0..=spots].iter().sum()),
                    (t, l) => (l..=t)
                        .map(|i| {
                            Self::compute_opts(lst, map, avg, (i - 1, l - 1))
                                + avg.abs_diff(
                                    lst[i.try_into().unwrap()..=spots]
                                        .iter()
                                        .sum(),
                                )
                        })
                        .min_by(u64::cmp)
                        .expect("seq block has no statments"),
                };
                map.insert((num_spots, num_splitters), opt_value);
                opt_value
            }
        }
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
    ///
    /// Returns a list of inclusive ranges, whose bounds represent the groups
    fn compute_split_indices(
        lst: &Vec<u64>,
        num_groups: u64,
    ) -> Vec<(u64, u64)> {
        // compute constants
        let avg = lst.iter().sum::<u64>() / num_groups;
        let len: u64 = lst.len().try_into().unwrap();

        // map of optimal values
        let mut map = HashMap::new();

        // contains indices at which to split
        let mut splits = VecDeque::new();
        splits.push_front(len - 1);

        // solve dp problem
        Self::compute_opts(lst, &mut map, avg, (len - 1, num_groups - 1));
        Self::backtrack(&map, lst, &mut splits, avg, (len - 1, num_groups - 1));

        // compute range of groups from split indices
        let mut prev_index = 0;
        splits
            .iter()
            .map(|i| {
                let range = (prev_index, *i);
                prev_index = *i + 1;
                range
            })
            .collect()
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
        // Stores an approx size of each statement in the Seq block
        let stmt_sizes: Vec<u64> = s
            .stmts
            .iter()
            .map(|stmt| {
                stmt.approx_size(
                    APPROX_ENABLE_SIZE,
                    APPROX_WHILE_REPEAT_SIZE,
                    APPROX_IF_SIZE,
                )
            })
            .collect();

        // Exit out if threshold for splitting exceeds the estimated total size
        // or if we want more children seq's than we have statements
        let total_size = stmt_sizes.iter().sum();
        if total_size < self.threshold || self.num_children > total_size {
            return Ok(Action::Continue);
        }

        // Split the `seq` block into children `seq`s controlled by a parent
        let parent_seq = ir::Control::Seq(ir::Seq {
            stmts: Self::compute_split_indices(&stmt_sizes, self.num_children)
                .iter()
                .map(|(l, u)| {
                    let mut child_attrs = s.attributes.clone();
                    child_attrs.insert(ir::BoolAttr::NewFSM, 1);
                    ir::Control::Seq(ir::Seq {
                        stmts: s
                            .stmts
                            .drain(0..=(u - l).try_into().unwrap())
                            .collect(),
                        attributes: child_attrs,
                    })
                })
                .collect(),
            attributes: s.attributes.clone(),
        });
        Ok(Action::change(parent_seq))
    }
}
