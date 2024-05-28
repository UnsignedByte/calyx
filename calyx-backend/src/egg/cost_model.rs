use egglog::{ast::Literal, util::IndexMap, Term, TermDag};
use egraph_serialize::{ClassId, EGraph, NodeId};
use itertools::Itertools;
use std::collections::{HashMap, HashSet};

pub fn get_bit_width_from(states: u64) -> u64 {
    if states == 0_u64 || states == 1_u64 {
        return states;
    }
    for index in 0u8..63 {
        let x = (63 - index) as u64;
        if states & (1u64 << x) != 0 {
            // If n is a power of two, return x. Otherwise, x + 1.
            return if (states & (states - 1)) == 0u64 {
                x
            } else {
                x + 1
            };
        }
    }
    panic!();
}

type Cost = i128;

fn emit_list(expr: &egglog::Term, termdag: &TermDag) -> Vec<Term> {
    let mut control = vec![];

    let mut list = expr.clone();

    loop {
        egglog::match_term_app!(list.clone(); {
            ("Cons", [x, xs]) => {
                let head = termdag.get(*x);
                control.push(head);
                list = termdag.get(*xs);
            }
            ("Nil", []) => return control,
            _ => panic!("unexpected")
        });
    }
}

fn emit_attribute(
    expr: &egglog::Term,
    termdag: &TermDag,
) -> HashMap<String, i64> {
    let mut attributes = HashMap::<String, i64>::new();
    let mut mapping = expr.clone();
    'outer: loop {
        egglog::match_term_app!(mapping.clone();
        {
            ("AttributeMap", children) => {
                // ["promotable", 1, ...] => [("promotable", 1), ...]
                let (ks, vs): (Vec<_>, Vec<_>) = children
                    .iter()
                    .enumerate()
                    .partition(|(i, _)| { i % 2 == 0});
                let ks: Vec<_> = ks.iter().map(|(_, v)| { v }).collect();
                let vs: Vec<_> = vs.iter().map(|(_, v)| { v }).collect();

                // Parse these properly.
                for (k, v) in  ks.iter().zip(vs.iter()) {
                    if let egglog::Term::Lit(egglog::ast::Literal::String(key)) = &termdag.get(***k) {
                        if let egglog::Term::Lit(egglog::ast::Literal::Int(value)) = &termdag.get(***v) {
                            attributes.insert(key.to_string(), *value);
                        }
                    }
                }
                break 'outer;
            }
            ("Attributes", [map]) => {
                mapping = termdag.get(*map);
            }
            _ => {
                break 'outer;
            }
        });
    }
    attributes
}

pub(crate) struct EgraphAnalysis<'a> {
    pub(crate) egraph: &'a EGraph,
    pub(crate) termdag: &'a mut egglog::TermDag,
}

impl<'a> EgraphAnalysis<'a> {
    pub fn new(
        egraph: &'a EGraph,
        termdag: &'a mut TermDag,
    ) -> EgraphAnalysis<'a> {
        EgraphAnalysis { egraph, termdag }
    }
}

#[derive(Clone, Debug)]
pub struct CostPoint {
    pub total: i128,
    pub costs: HashMap<ClassId, Cost>,
    pub term: Term,
}

pub(crate) struct Extractor<'a> {
    analysis: &'a mut EgraphAnalysis<'a>,
}

impl<'a> Extractor<'a> {
    fn new(analysis: &'a mut EgraphAnalysis<'a>) -> Extractor<'a> {
        Extractor { analysis }
    }

    fn egraph(&self) -> &'a EGraph {
        self.analysis.egraph
    }

    fn parent_index(&self) -> IndexMap<ClassId, Vec<NodeId>> {
        let mut parents = IndexMap::<ClassId, Vec<NodeId>>::default();

        for class in self.egraph().classes().values() {
            parents.insert(class.id.clone(), Vec::new());
        }

        for class in self.egraph().classes().values() {
            for node in &class.nodes {
                for child_node in &self.egraph()[node].children {
                    let cid = self.egraph().nid_to_cid(child_node);
                    parents[cid].push(node.clone());
                }
            }
        }
        parents
    }

    fn cost(
        &mut self,
        nid: &NodeId,
        children: &[CostPoint],
        costs: &mut HashMap<ClassId, CostPoint>,
    ) -> Option<i128> {
        let node = &self.egraph()[nid];
        let leaves = &node.children;

        let calculate = |rs: Vec<u64>| rs.iter().sum::<u64>() as i128;

        // TODO(cgyurgyik): Take sharing into account...
        let mut registers = vec![];
        match node.op.as_str() {
            "Seq" => {
                let attributes = children.first().unwrap();
                let attributes =
                    emit_attribute(&attributes.term, self.analysis.termdag);
                if let Some(latency) = attributes.get("static") {
                    // The register size is equivalent to log2(latency)
                    registers.push(get_bit_width_from(*latency as u64));
                } else {
                    let children = children.last().unwrap();
                    // This is dynamic. The register size is equivalent to the log2(N),
                    // where N is the number of "states" in the FSM. Additional
                    let length =
                        emit_list(&children.term, self.analysis.termdag).len();
                    registers.push(get_bit_width_from(length as u64));
                }
                Some(calculate(registers))
            }
            "Par" => {
                let attributes = children.first().unwrap();
                let attributes =
                    emit_attribute(&attributes.term, self.analysis.termdag);
                if let Some(latency) = attributes.get("static") {
                    // The register size is equivalent to log2(latency)
                    registers.push(get_bit_width_from(*latency as u64));
                } else {
                    let children = children.last().unwrap();
                    // Every non-enalbe is considered a state.
                    let list = emit_list(&children.term, self.analysis.termdag);
                    let mut length = list
                        .iter()
                        .filter(|term| {
                            if let Term::App(op, _) = term {
                                return op.as_str() != "Enable";
                            }
                            true
                        })
                        .collect_vec()
                        .len();
                    if list.len() != length {
                        length += 1; // ...for any enables that will be compiled together.
                    }
                    registers.push(get_bit_width_from(length as u64));
                }
                Some(calculate(registers))
            }
            "Repeat" => {
                let attributes = children.first().unwrap();
                let attributes =
                    emit_attribute(&attributes.term, self.analysis.termdag);
                if let Some(latency) = attributes.get("static") {
                    // The register size is equivalent to log2(latency)
                    registers.push(get_bit_width_from(*latency as u64));
                } else {
                    // A dynamic repeat is compiled into `while { seq { ... } }`.
                    let child = leaves.last().unwrap();
                    return Some(
                        self.calculate_cost_point(child.clone(), costs).total,
                    );
                }
                // let repeat = children.get(1).unwrap();
                // if let Term::Lit(Literal::Int(N)) = repeat.term {}
                Some(calculate(registers))
            }
            "Cons" => Some(0),
            "Nil" => Some(0),
            "Enable" => {
                // let point = children.last().unwrap();
                // let attributes =
                //     emit_attribute(&point.term, self.analysis.termdag);
                // if let Some(latency) = attributes.get("promotable") {
                //     return Some(*latency as i128);
                // }
                Some(0)
            }
            _ => None,
        }
    }

    fn calculate_cost_point(
        &mut self,
        nid: NodeId,
        costs: &mut HashMap<ClassId, CostPoint>,
    ) -> CostPoint {
        let node = &self.egraph()[&nid];
        let cid = self.egraph().nid_to_cid(&nid);
        let op = &node.op;

        let child_classes = node
            .children
            .iter()
            .map(|n| self.egraph().nid_to_cid(n).clone())
            .collect_vec();

        let child_costs: Vec<_> = child_classes
            .iter()
            .map(|n| costs.get(n).unwrap().clone())
            .collect();

        if child_costs
            .iter()
            .any(|point| point.costs.contains_key(cid))
        {
            // Cycle.
            return CostPoint {
                costs: Default::default(),
                total: i128::max_value(),
                term: self.analysis.termdag.app(op.into(), vec![]),
            };
        }

        self.get_node_cost(nid, &child_costs, costs)
    }

    fn get_node_cost(
        &mut self,
        nid: NodeId,
        child_costs: &Vec<CostPoint>,
        costs: &mut HashMap<ClassId, CostPoint>,
    ) -> CostPoint {
        let node = &self.egraph()[&nid];
        let cid = self.egraph().nid_to_cid(&nid);
        let op = &node.op;

        let term = self.get_term(op, child_costs);
        let node_cost = self.cost(&nid, child_costs, costs);
        if node_cost.is_none() {
            return CostPoint {
                total: 0,
                costs: [(cid.clone(), 0)].into(),
                term,
            };
        }

        let mut costs = HashMap::<ClassId, Cost>::new();
        let mut total: i128 = node_cost.unwrap();
        for child in child_costs {
            for (ccid, ccost) in &child.costs {
                if let Some(existing) = costs.insert(ccid.clone(), *ccost) {
                    // Verify we only select one e-node from each e-graph.
                    assert_eq!(existing, *ccost);
                } else {
                    total += ccost;
                }
            }
        }

        CostPoint { total, costs, term }
    }

    fn get_term(&mut self, op: &String, child_costs: &Vec<CostPoint>) -> Term {
        if child_costs.is_empty() {
            // Parse string modulo the delimiters.
            if op.starts_with('\"') {
                return self
                    .analysis
                    .termdag
                    .lit(Literal::String(op[1..op.len() - 1].into()));
            }
            if let Ok(n) = op.parse::<i64>() {
                return self.analysis.termdag.lit(Literal::Int(n));
            }
        }
        self.analysis.termdag.app(
            op.into(),
            child_costs.iter().map(|point| point.term.clone()).collect(),
        )
    }
}

pub fn extract(
    identifier: &str,
    egraph: &mut egglog::EGraph,
    termdag: &mut egglog::TermDag,
) -> (egglog::Term, Cost) {
    // Serialize the egraph.
    let mut configuration = egglog::SerializeConfig::default();
    let (_, value) = egraph
        .eval_expr(&egglog::ast::Expr::Var((), identifier.into()))
        .unwrap_or_else(|_| {
            panic!(
                "unexpected failure of e-graph extraction for component: {}.",
                identifier
            )
        });

    // Push the root e-class before serializing.
    configuration.root_eclasses.push(value);
    let serialized_egraph = egraph.serialize(configuration);

    log::warn!("--- root_eclasses: {:?}", serialized_egraph.root_eclasses);

    let mut analysis = EgraphAnalysis::new(&serialized_egraph, termdag);
    let mut extractor = Extractor::new(&mut analysis);
    let parent_index = extractor.parent_index();
    let mut costs = HashMap::<ClassId, CostPoint>::with_capacity_and_hasher(
        extractor.egraph().classes().len(),
        Default::default(),
    );

    let mut worklist = UniqueQueue::default();
    // Insert all the leaves.
    for class in extractor.egraph().classes().values() {
        for nid in &class.nodes {
            if extractor.egraph()[nid].is_leaf() {
                worklist.insert(nid.clone())
            }
        }
    }

    while let Some(nid) = worklist.pop() {
        let cid = extractor.egraph().nid_to_cid(&nid);
        let node = &extractor.egraph()[&nid];

        if node
            .children
            .iter()
            .all(|n| costs.contains_key(extractor.egraph().nid_to_cid(n)))
        {
            let previous_cost: i128 = if let Some(cost) = costs.get(cid) {
                cost.total
            } else {
                i128::max_value()
            };
            let cost_point =
                extractor.calculate_cost_point(nid.clone(), &mut costs);
            if cost_point.total < previous_cost {
                if previous_cost != i128::max_value() {
                    log::warn!(
                        "cost: {} less than previous: {}",
                        cost_point.total,
                        previous_cost
                    );
                }
                costs.insert(cid.clone(), cost_point);
                for parent in &parent_index[cid] {
                    worklist.insert(parent.clone());
                }
            }
        }
    }

    let mut root_eclasses = serialized_egraph.root_eclasses.clone();
    root_eclasses.sort();
    root_eclasses.dedup();

    let cost = root_eclasses
        .iter()
        .max_by(|c1, c2| costs[c1].total.cmp(&costs[c2].total))
        .map(|cid| &costs[cid])
        .unwrap();
    log::warn!("selected: {:?}", cost);
    (cost.term.clone(), cost.total)
}

#[derive(Clone, Debug)]
pub(crate) struct UniqueQueue<T>
where
    T: Eq + std::hash::Hash + Clone,
{
    set: HashSet<T>,
    queue: std::collections::VecDeque<T>,
}

impl<T> Default for UniqueQueue<T>
where
    T: Eq + std::hash::Hash + Clone,
{
    fn default() -> Self {
        UniqueQueue {
            set: Default::default(),
            queue: std::collections::VecDeque::new(),
        }
    }
}

impl<T> UniqueQueue<T>
where
    T: Eq + std::hash::Hash + Clone,
{
    pub fn insert(&mut self, t: T) {
        if self.set.insert(t.clone()) {
            self.queue.push_back(t);
        }
    }

    pub fn pop(&mut self) -> Option<T> {
        let res = self.queue.pop_front();
        res.as_ref().map(|t| self.set.remove(t));
        res
    }
}
