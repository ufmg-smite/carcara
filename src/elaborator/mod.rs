//! An elaborator for Alethe proofs

pub mod error;
mod hole;
mod local;
mod polyeq;
mod reordering;
mod sat_refutation;
mod uncrowding;

use crate::{
    Error,
    ast::{
        ContextStack, Polyeq, Problem, ProofNode, ProofNodeForest, Rc, StepNode, SubproofNode,
        Term, build_term, match_term, pool::Pool,
    },
    external::{ExternalTool, SatTools},
};
use carcara_macros::GenerateSetters;
use error::{ElaborationError, ElaborationErrorAtStep};
use indexmap::IndexSet;
use polyeq::PolyeqElaborator;
use std::{
    collections::{HashMap, HashSet},
    path::Path,
    time::{Duration, Instant},
};

/// Configuration options for [`Elaborator`].
#[derive(Debug, Default, Clone, GenerateSetters)]
pub struct Config {
    /// If `Some`, enables the elaboration of `lia_generic` steps using an external solver.
    ///
    /// This involves calling the solver to solve the linear integer arithmetic problem, checking
    /// the proof, and inserting it in the place of the `lia_generic` step.
    lia_solver: Option<ExternalTool>,

    /// Enables an optimization that reorders premises when uncrowding resolution steps, in order to
    /// further minimize the number of `contraction` steps added.
    uncrowd_rotation: bool,

    /// If `Some`, enables the elaboration of `all_simplify` and `rare_rewrite` steps using an
    /// external solver, inserting the solver's proof in the place of those steps.
    hole_solver: Option<ExternalTool>,

    /// The external tools used to elaborate `sat_refutation` steps.
    sat_ref_tools: Option<SatTools>,
}

impl Config {
    /// Constructs a new `Config`, with default settings.
    pub fn new() -> Self {
        Self::default()
    }
}

/// An elaboration pass, to be applied to a proof.
#[derive(Debug, Clone, Copy)]
pub enum ElaborationPass {
    /// Elaborates away all uses of polyequality in the proof.
    Polyeq,
    /// Fills holes in the proof using an external solver.
    Hole,
    /// Performs small local elaborations.
    ///
    /// Currently, this affects the rules:
    /// - `eq_transitive`
    /// - `trans`
    /// - `resolution`
    /// - `cong`
    /// - `eq_congruent`
    /// - `eq_congruent_pred`
    /// - `bounded_farkas`
    /// - `eq_mp`
    Local,
    /// Uncrowds `resolution` steps, removing the implicit removal of duplicates by adding
    /// `contraction` steps.
    Uncrowd,
    /// Removes `reordering` steps from the proof, recomputing the conclusions of order-sensitive
    /// steps when necessary.
    Reordering,
    /// Elaborates `sat_refutation` steps using an external SAT solver.
    SatRefutation,
}

/// A proof elaborator for Alethe.
pub struct Elaborator<'e> {
    pool: &'e mut Pool,
    problem: &'e Problem,
    config: Config,
}

impl<'e> Elaborator<'e> {
    /// Constructs a new [`Elaborator`] with the given `pool`, `problem`, and `config`.
    pub fn new(pool: &'e mut Pool, problem: &'e Problem, config: Config) -> Self {
        Self { pool, problem, config }
    }

    /// Elaborates a proof, applying the default pipeline of passes.
    pub fn elaborate_with_default_pipeline(
        &mut self,
        proof: ProofNodeForest,
        proof_filename: &Path,
    ) -> Result<ProofNodeForest, Error> {
        use ElaborationPass::*;
        let pipeline = vec![Polyeq, Hole, Local, Uncrowd, Reordering];
        self.elaborate(proof, proof_filename, pipeline)
    }

    /// Elaborates a proof, applying the given `pipeline` of passes, in order.
    pub fn elaborate(
        &mut self,
        proof: ProofNodeForest,
        proof_filename: &Path,
        pipeline: Vec<ElaborationPass>,
    ) -> Result<ProofNodeForest, Error> {
        Ok(self
            .elaborate_with_stats(proof, proof_filename, pipeline)?
            .0)
    }

    /// Elaborates a proof, applying the given `pipeline` of passes in order, and returns the
    /// elaborated proof together with the time spent on each pass.
    pub fn elaborate_with_stats(
        &mut self,
        proof: ProofNodeForest,
        proof_filename: &Path,
        pipeline: Vec<ElaborationPass>,
    ) -> Result<(ProofNodeForest, Vec<Duration>), Error> {
        let mut durations = Vec::new();
        let mut current = proof;
        for pass in pipeline {
            let time = Instant::now();
            let result = match pass {
                ElaborationPass::Polyeq => self.elaborate_polyeq(current),
                ElaborationPass::Hole => self.elaborate_hole(current),
                ElaborationPass::Local => self.elaborate_local(current),
                ElaborationPass::Uncrowd => current.mutate(|_, node, _| match node.as_ref() {
                    ProofNode::Step(s)
                        if (s.rule == "resolution" || s.rule == "th_resolution")
                            && !s.args.is_empty() =>
                    {
                        uncrowding::uncrowd_resolution(self.pool, s, self.config.uncrowd_rotation)
                            .map_err(|e| e.at(s))
                    }
                    _ => Ok(node.clone()),
                }),
                ElaborationPass::Reordering => reordering::remove_reorderings(current),
                ElaborationPass::SatRefutation => {
                    if self.config.sat_ref_tools.is_some() {
                        current.mutate(|_, node, _| match node.as_ref() {
                            ProofNode::Step(s) if (s.rule == "sat_refutation") => {
                                // TODO: proper error handling
                                Ok(sat_refutation::sat_refutation(self, s)
                                    .unwrap_or_else(|| node.clone()))
                            }
                            _ => Ok(node.clone()),
                        })
                    } else {
                        Ok(current)
                    }
                }
            };
            current = result.map_err(|e| e.at(proof_filename, pass))?;
            durations.push(time.elapsed());
        }
        Ok((current, durations))
    }

    fn elaborate_polyeq(
        &mut self,
        proof: ProofNodeForest,
    ) -> Result<ProofNodeForest, ElaborationErrorAtStep> {
        fn get_elaboration_function(rule: &str) -> Option<ElaborationFunc> {
            Some(match rule {
                "refl" => polyeq::reflexivity::refl,
                "forall_inst" => polyeq::quantifiers::forall_inst,
                "subproof" => polyeq::subproof::subproof,
                "ite_intro" => polyeq::tautology::ite_intro,
                "bfun_elim" => polyeq::clausification::bfun_elim,
                _ => return None,
            })
        }

        proof.mutate(|context, node, _| match node.as_ref() {
            ProofNode::Assume { id, depth, term }
                if context.is_empty() && !self.problem.premises.contains(term) =>
            {
                Ok(self.elaborate_assume(id, *depth, term))
            }
            ProofNode::Step(s) => {
                if let Some(func) = get_elaboration_function(&s.rule) {
                    func(self.pool, context, s).map_err(|e| e.at(s))
                } else {
                    Ok(node.clone())
                }
            }
            _ => Ok(node.clone()),
        })
    }

    fn elaborate_hole(
        &mut self,
        proof: ProofNodeForest,
    ) -> Result<ProofNodeForest, ElaborationErrorAtStep> {
        // Skip `mutate` in the common case where neither option was given
        if self.config.hole_solver.is_none() && self.config.lia_solver.is_none() {
            return Ok(proof);
        }

        proof.mutate(|_, node, _| match node.as_ref() {
            ProofNode::Step(s)
                if self.config.hole_solver.is_some()
                    && (s.rule == "all_simplify" || s.rule == "rare_rewrite") =>
            {
                hole::hole(self, s).map_err(|e| e.at(s))
            }
            ProofNode::Step(s) if self.config.lia_solver.is_some() && s.rule == "lia_generic" => {
                hole::lia_generic(self, s).map_err(|e| e.at(s))
            }
            _ => Ok(node.clone()),
        })
    }

    fn elaborate_local(
        &mut self,
        proof: ProofNodeForest,
    ) -> Result<ProofNodeForest, ElaborationErrorAtStep> {
        fn get_elaboration_function(rule: &str) -> Option<ElaborationFunc> {
            Some(match rule {
                "eq_transitive" => local::transitivity::eq_transitive,
                "trans" => local::transitivity::trans,
                "resolution" | "th_resolution" => local::resolution::resolution,
                "cong" => local::congruence::cong,
                "eq_congruent" => local::congruence::eq_congruent,
                "eq_congruent_pred" => local::congruence::eq_congruent_pred,
                "bounded_farkas" => local::farkas::bounded_farkas,
                "eq_mp" => local::eq_mp::eq_mp,
                _ => return None,
            })
        }

        proof.mutate(|context, node, _| {
            match node.as_ref() {
                ProofNode::Step(s) => {
                    if let Some(func) = get_elaboration_function(&s.rule) {
                        return func(self.pool, context, s).map_err(|e| e.at(s));
                    }
                }
                ProofNode::Subproof(_) => unreachable!(),
                ProofNode::Assume { .. } => (),
            }
            Ok(node.clone())
        })
    }

    fn elaborate_assume(&mut self, id: &str, depth: usize, term: &Rc<Term>) -> Rc<ProofNode> {
        let mut found = None;
        for p in &self.problem.premises {
            if Polyeq::new()
                .mod_reordering(true)
                .mod_nary(true)
                .eq(term, p)
            {
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
            self.pool,
            premise.clone(),
            term.clone(),
        );

        let equiv1_step = Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth,
            clause: vec![
                build_term!(self.pool, (not {premise.clone()})),
                term.clone(),
            ],
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
            args: vec![premise, self.pool.bool_true()],
            ..Default::default()
        }))
    }
}

fn add_refl_step(
    pool: &mut Pool,
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

fn add_symm_step(pool: &mut Pool, node: &Rc<ProofNode>, id: String) -> Rc<ProofNode> {
    assert_eq!(node.clause().len(), 1);
    let (a, b) = match_term!((= a b) = node.clause()[0]).unwrap();
    let clause = vec![build_term!(pool, (= {b.clone()} {a.clone()}))];
    Rc::new(ProofNode::Step(StepNode {
        id,
        depth: node.depth(),
        clause,
        rule: "symm".into(),
        premises: vec![node.clone()],
        args: Vec::new(),
        discharge: Vec::new(),
        previous_step: None,
    }))
}

fn add_trans_step(
    pool: &mut Pool,
    nodes: impl IntoIterator<Item = Rc<ProofNode>>,
    id: String,
) -> Rc<ProofNode> {
    let premises: Vec<_> = nodes.into_iter().collect();
    let depth = premises.first().unwrap().depth();
    let (a, _) =
        match_term!((= a b) = premises.first().unwrap().clause().first().unwrap()).unwrap();
    let (_, b) = match_term!((= a b) = premises.last().unwrap().clause().first().unwrap()).unwrap();
    Rc::new(ProofNode::Step(StepNode {
        id,
        depth,
        clause: vec![build_term!(pool, (= {a.clone()} {b.clone()}))],
        rule: "trans".to_owned(),
        premises,
        ..StepNode::default()
    }))
}

type ElaborationFunc =
    fn(&mut Pool, &mut ContextStack, &StepNode) -> Result<Rc<ProofNode>, ElaborationError>;

/// A proof that can be mutated by applying a function to each of its nodes.
///
/// The function is applied to the nodes in a bottom-up order, so that the premises of a step are
/// always processed before the step itself. Shared nodes are only processed once.
pub trait Mutate: Sized {
    /// Applies `mutate_func` to every node of the proof, returning the new proof.
    ///
    /// `mutate_func` receives the current context, the node, and whether the node's premises were
    /// modified, and returns the new node.
    fn mutate<F, E>(self, mutate_func: F) -> Result<Self, E>
    where
        F: FnMut(&mut ContextStack, &Rc<ProofNode>, bool) -> Result<Rc<ProofNode>, E>;
}

impl Mutate for ProofNodeForest {
    fn mutate<F, E>(self, mut mutate_func: F) -> Result<Self, E>
    where
        F: FnMut(&mut ContextStack, &Rc<ProofNode>, bool) -> Result<Rc<ProofNode>, E>,
    {
        let mut cache = HashMap::new();
        self.0
            .into_iter()
            .map(|node| mutate_impl(&node, &mut cache, &mut mutate_func))
            .collect::<Result<Vec<_>, E>>()
            .map(ProofNodeForest)
    }
}

impl Mutate for Rc<ProofNode> {
    fn mutate<F, E>(self, mutate_func: F) -> Result<Self, E>
    where
        F: FnMut(&mut ContextStack, &Rc<ProofNode>, bool) -> Result<Rc<ProofNode>, E>,
    {
        let mut cache = HashMap::new();
        mutate_impl(&self, &mut cache, mutate_func)
    }
}

fn mutate_impl<F, E>(
    root: &Rc<ProofNode>,
    cache: &mut HashMap<Rc<ProofNode>, Rc<ProofNode>>,
    mut mutate_func: F,
) -> Result<Rc<ProofNode>, E>
where
    F: FnMut(&mut ContextStack, &Rc<ProofNode>, bool) -> Result<Rc<ProofNode>, E>,
{
    let mut did_outbound: HashSet<&Rc<ProofNode>> = HashSet::new();
    let mut todo = vec![(root, false)];

    let mut outbound_premises_stack = vec![IndexSet::new()];
    let mut context = ContextStack::new();

    while let Some((node, is_done)) = todo.pop() {
        if cache.contains_key(node) {
            continue;
        }

        let mutated = match node.as_ref() {
            ProofNode::Assume { .. } => mutate_func(&mut context, node, false)?,
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
                let changed = s
                    .premises
                    .iter()
                    .chain(s.discharge.iter())
                    .chain(s.previous_step.iter())
                    .any(|p| *p != cache[p]);

                let new_node = Rc::new(ProofNode::Step(StepNode {
                    premises,
                    discharge,
                    previous_step,
                    ..s.clone()
                }));
                mutate_func(&mut context, &new_node, changed)?
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
                todo.extend(s.extra_steps.iter().rev().map(|node| (node, false)));
                outbound_premises_stack.push(IndexSet::new());
                context.push(&s.args);
                continue;
            }
            ProofNode::Subproof(s) => {
                context.pop();
                let outbound_premises =
                    outbound_premises_stack.pop().unwrap().into_iter().collect();
                let extra_steps = s
                    .extra_steps
                    .iter()
                    .map(|node| cache[node].clone())
                    .collect();
                Rc::new(ProofNode::Subproof(SubproofNode {
                    last_step: cache[&s.last_step].clone(),
                    args: s.args.clone(),
                    outbound_premises,
                    extra_steps,
                }))
            }
        };
        outbound_premises_stack
            .last_mut()
            .unwrap()
            .extend(mutated.get_outbound_premises());
        cache.insert(node.clone(), mutated);
    }
    assert!(outbound_premises_stack.len() == 1 && outbound_premises_stack[0].is_empty());
    Ok(cache[root].clone())
}

/// A helper for generating unique step IDs from a root ID, by appending numeric suffixes to it.
pub struct IdHelper {
    root: String,
    stack: Vec<usize>,
}

impl IdHelper {
    /// Constructs a new [`IdHelper`] for the given root ID.
    pub fn new(root: &str) -> Self {
        Self {
            root: root.to_owned(),
            stack: vec![0],
        }
    }

    /// Returns the next generated ID, and advances the internal counter.
    pub fn next_id(&mut self) -> String {
        use std::fmt::Write;

        let mut current = self.root.clone();
        for i in &self.stack {
            write!(&mut current, ".t{}", i + 1).unwrap();
        }
        *self.stack.last_mut().unwrap() += 1;
        current
    }

    /// Starts a new nesting level.
    ///
    /// That is, if the current ID is `t5.t3`, `push` will use that as the root for the next ids,
    /// such that the following ID will be `t5.t3.t1`. This is reverted by [`IdHelper::pop`].
    pub fn push(&mut self) {
        self.stack.push(0);
    }

    /// Ends the current nesting level.
    pub fn pop(&mut self) {
        assert!(self.stack.len() >= 2, "can't pop last frame from the stack");
        self.stack.pop();
    }
}
