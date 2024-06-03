mod lia_generic;
mod polyeq;
mod reflexivity;
mod reordering;
mod resolution;
mod transitivity;
mod uncrowding;

use crate::{ast::*, CheckerError};
use indexmap::IndexSet;
use polyeq::PolyeqElaborator;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct Config {
    /// Controls the granularity of the elaboration of resolution steps.
    pub resolution_granularity: ResolutionGranularity,

    /// If `Some`, enables the elaboration of `lia_generic` steps using an external solver. When
    /// checking a proof, this means calling the solver to solve the linear integer arithmetic
    /// problem, checking the proof, and discarding it. When elaborating, the proof will instead be
    /// inserted in the place of the `lia_generic` step. See [`LiaGenericOptions`] for more details.
    pub lia_options: Option<LiaGenericOptions>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ResolutionGranularity {
    Pivots,
    Uncrowd,
    Reordering,
}

impl Default for ResolutionGranularity {
    fn default() -> Self {
        Self::Reordering
    }
}

pub enum ElaborationStep {
    Polyeq,
    LiaGeneric,
    Local,
    Uncrowd,
    Reordering,
}

/// The options that control how `lia_generic` steps are elaborated using an external solver.
#[derive(Debug, Clone)]
pub struct LiaGenericOptions {
    /// The external solver path. The solver should be a binary that can read SMT-LIB from stdin and
    /// output an Alethe proof to stdout.
    pub solver: Box<str>,

    /// The arguments to pass to the solver.
    pub arguments: Vec<Box<str>>,
}

pub fn default_pipeline() -> Vec<ElaborationStep> {
    use ElaborationStep::*;
    vec![Polyeq, LiaGeneric, Local, Uncrowd, Reordering]
}

pub fn elaborate(
    pool: &mut PrimitivePool,
    premises: &IndexSet<Rc<Term>>,
    prelude: &ProblemPrelude,
    root: &Rc<ProofNode>,
    config: Config,
    pipeline: Vec<ElaborationStep>,
) -> Rc<ProofNode> {
    let mut current = root.clone();
    for step in pipeline {
        current = match step {
            ElaborationStep::Polyeq => elaborate_polyeq(pool, premises, &current),
            ElaborationStep::LiaGeneric => mutate(&current, |_, node| match node.as_ref() {
                ProofNode::Step(s) if s.rule == "lia_generic" => {
                    lia_generic::lia_generic(pool, s, prelude, config.lia_options.as_ref().unwrap())
                        .unwrap_or_else(|| node.clone())
                }
                _ => node.clone(),
            }),
            ElaborationStep::Local => elaborate_local(pool, &current),
            ElaborationStep::Uncrowd => mutate(&current, |_, node| match node.as_ref() {
                ProofNode::Step(s)
                    if (s.rule == "resolution" || s.rule == "th_resolution")
                        && !s.args.is_empty() =>
                {
                    uncrowding::uncrowd_resolution(pool, s)
                }
                _ => node.clone(),
            }),
            ElaborationStep::Reordering => reordering::remove_reorderings(&current),
        };
    }
    current
}

fn elaborate_polyeq(
    pool: &mut PrimitivePool,
    premises: &IndexSet<Rc<Term>>,
    root: &Rc<ProofNode>,
) -> Rc<ProofNode> {
    mutate(root, |context, node| {
        match node.as_ref() {
            ProofNode::Assume { id, depth, term }
                if context.is_empty() && !premises.contains(term) =>
            {
                elaborate_assume(pool, premises, id, *depth, term)
            }
            ProofNode::Step(s) if s.rule == "refl" => {
                reflexivity::refl(pool, context, s).unwrap() // TODO: add proper error handling
            }
            _ => node.clone(),
        }
    })
}

fn elaborate_local(pool: &mut PrimitivePool, root: &Rc<ProofNode>) -> Rc<ProofNode> {
    fn get_elaboration_function(rule: &str) -> Option<ElaborationFunc> {
        Some(match rule {
            "eq_transitive" => transitivity::eq_transitive,
            "trans" => transitivity::trans,
            "resolution" | "th_resolution" => resolution::resolution,
            _ => return None,
        })
    }

    mutate(root, |context, node| {
        match node.as_ref() {
            ProofNode::Step(s) => {
                if let Some(func) = get_elaboration_function(&s.rule) {
                    return func(pool, context, s).unwrap(); // TODO: add proper error handling
                }
            }
            ProofNode::Subproof(_) => unreachable!(),
            ProofNode::Assume { .. } => (),
        }
        node.clone()
    })
}

fn elaborate_assume(
    pool: &mut dyn TermPool,
    premises: &IndexSet<Rc<Term>>,
    id: &str,
    depth: usize,
    term: &Rc<Term>,
) -> Rc<ProofNode> {
    let mut found = None;
    let mut polyeq_time = std::time::Duration::ZERO;
    for p in premises {
        if polyeq_mod_nary(term, p, &mut polyeq_time) {
            found = Some(p.clone());
            break;
        }
    }
    let premise = found.expect("trying to elaborate assume, but it is invalid!");

    let new_assume = Rc::new(ProofNode::Assume {
        id: id.to_owned(),
        depth,
        term: premise.clone(),
    });

    let mut ids = IdHelper::new(id);
    let equality_step = PolyeqElaborator::new(&mut ids, depth, false).elaborate(
        pool,
        premise.clone(),
        term.clone(),
    );

    let equiv1_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth,
        clause: vec![build_term!(pool, (not {premise.clone()})), term.clone()],
        rule: "equiv1".to_owned(),
        premises: vec![equality_step],
        ..Default::default()
    }));

    Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth,
        clause: vec![term.clone()],
        rule: "resolution".to_owned(),
        premises: vec![new_assume, equiv1_step],
        args: vec![ProofArg::Term(premise), ProofArg::Term(pool.bool_true())],
        ..Default::default()
    }))
}

pub fn add_refl_step(
    pool: &mut dyn TermPool,
    a: Rc<Term>,
    b: Rc<Term>,
    id: String,
    depth: usize,
) -> Rc<ProofNode> {
    Rc::new(ProofNode::Step(StepNode {
        id,
        depth,
        clause: vec![build_term!(pool, (= {a} {b}))],
        rule: "refl".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
        discharge: Vec::new(),
        previous_step: None,
    }))
}

type ElaborationFunc =
    fn(&mut PrimitivePool, &mut ContextStack, &StepNode) -> Result<Rc<ProofNode>, CheckerError>;

fn mutate<F>(root: &Rc<ProofNode>, mut mutate_func: F) -> Rc<ProofNode>
where
    F: FnMut(&mut ContextStack, &Rc<ProofNode>) -> Rc<ProofNode>,
{
    let mut cache: HashMap<&Rc<ProofNode>, Rc<ProofNode>> = HashMap::new();
    let mut did_outbound: HashSet<&Rc<ProofNode>> = HashSet::new();
    let mut todo = vec![(root, false)];

    let mut outbound_premises_stack = vec![IndexSet::new()];
    let mut context = ContextStack::new();

    while let Some((node, is_done)) = todo.pop() {
        if cache.contains_key(node) {
            continue;
        }

        let mutated = match node.as_ref() {
            ProofNode::Assume { .. } => mutate_func(&mut context, node),
            ProofNode::Step(s) if !is_done => {
                todo.push((node, true));

                let all_premises = s
                    .premises
                    .iter()
                    .chain(&s.discharge)
                    .chain(&s.previous_step)
                    .rev();
                todo.extend(
                    all_premises.filter_map(|p| (!cache.contains_key(p)).then_some((p, false))),
                );

                continue;
            }
            ProofNode::Step(s) => {
                let premises: Vec<_> = s.premises.iter().map(|p| cache[p].clone()).collect();
                let discharge: Vec<_> = s.discharge.iter().map(|p| cache[p].clone()).collect();
                let previous_step = s.previous_step.as_ref().map(|p| cache[p].clone());

                let new_node = Rc::new(ProofNode::Step(StepNode {
                    premises,
                    discharge,
                    previous_step,
                    ..s.clone()
                }));
                mutate_func(&mut context, &new_node)
            }
            ProofNode::Subproof(s) if !is_done => {
                assert!(
                    node.depth() == outbound_premises_stack.len() - 1,
                    "all outbound premises should have already been dealt with!"
                );

                if !did_outbound.contains(node) {
                    did_outbound.insert(node);
                    todo.push((node, false));
                    todo.extend(s.outbound_premises.iter().map(|premise| (premise, false)));
                    continue;
                }

                todo.push((node, true));
                todo.push((&s.last_step, false));
                outbound_premises_stack.push(IndexSet::new());
                context.push(&s.args);
                continue;
            }
            ProofNode::Subproof(s) => {
                context.pop();
                let outbound_premises =
                    outbound_premises_stack.pop().unwrap().into_iter().collect();
                Rc::new(ProofNode::Subproof(SubproofNode {
                    last_step: cache[&s.last_step].clone(),
                    args: s.args.clone(),
                    outbound_premises,
                }))
            }
        };
        outbound_premises_stack
            .last_mut()
            .unwrap()
            .extend(mutated.get_outbound_premises());
        cache.insert(node, mutated);
    }
    assert!(outbound_premises_stack.len() == 1 && outbound_premises_stack[0].is_empty());
    cache[root].clone()
}

struct IdHelper {
    root: String,
    stack: Vec<usize>,
}

impl IdHelper {
    fn new(root: &str) -> Self {
        Self {
            root: root.to_owned(),
            stack: vec![0],
        }
    }

    fn next_id(&mut self) -> String {
        use std::fmt::Write;

        let mut current = self.root.clone();
        for i in &self.stack {
            write!(&mut current, ".t{}", i + 1).unwrap();
        }
        *self.stack.last_mut().unwrap() += 1;
        current
    }

    fn push(&mut self) {
        self.stack.push(0);
    }

    fn pop(&mut self) {
        assert!(self.stack.len() >= 2, "can't pop last frame from the stack");
        self.stack.pop();
    }
}
