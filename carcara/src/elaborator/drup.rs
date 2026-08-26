use super::{error::ElaborationError, IdHelper};
use crate::{
    ast::{match_term, ContextStack, PrimitivePool, ProofNode, Rc, StepNode, Term, TermPool},
    drup::{check_drup, hash_term, DRupProofAction},
    CheckerError,
};
use indexmap::IndexSet;
use std::collections::HashMap;

type Literal = (bool, Rc<Term>);

fn clause_from_literals(pool: &mut dyn TermPool, literals: &IndexSet<Literal>) -> Vec<Rc<Term>> {
    literals
        .iter()
        .map(|(polarity, term)| {
            if *polarity {
                term.clone()
            } else {
                build_term!(pool, (not {term.clone()}))
            }
        })
        .collect()
}

fn resolve(
    clause1: &IndexSet<Literal>,
    clause2: &IndexSet<Literal>,
    pivot: &Rc<Term>,
) -> IndexSet<Literal> {
    clause1
        .union(clause2)
        .filter(|literal| &literal.1 != pivot)
        .cloned()
        .collect()
}

fn finish_goal(
    ids: &mut IdHelper,
    depth: usize,
    current_literals: &IndexSet<Literal>,
    current_proof: Rc<ProofNode>,
    goal_literals: &IndexSet<Literal>,
    goal_clause: Vec<Rc<Term>>,
) -> Rc<ProofNode> {
    let current_clause = current_proof.clause();
    if current_clause == goal_clause {
        return current_proof;
    }

    if current_literals == goal_literals {
        return Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth,
            clause: goal_clause,
            rule: "reordering".to_owned(),
            premises: vec![current_proof],
            ..Default::default()
        }));
    }

    let mut weakened_clause = current_clause.to_vec();
    for term in &goal_clause {
        let literal = term.remove_all_negations_with_polarity();
        let literal = (literal.0, literal.1.clone());
        if !current_literals.contains(&literal) {
            weakened_clause.push(term.clone());
        }
    }

    let weakened = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth,
        clause: weakened_clause.clone(),
        rule: "weakening".to_owned(),
        premises: vec![current_proof],
        ..Default::default()
    }));

    if weakened_clause == goal_clause {
        weakened
    } else {
        Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth,
            clause: goal_clause,
            rule: "reordering".to_owned(),
            premises: vec![weakened],
            ..Default::default()
        }))
    }
}

pub fn elaborate_drup(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let premise_terms: Vec<_> = step
        .premises
        .iter()
        .map(|premise| build_term!(pool, (cl[premise.clause().to_vec()])))
        .collect();
    let conclusion = build_term!(pool, (cl[step.clause.clone()]));
    let trace = check_drup(pool, conclusion.clone(), &premise_terms, &step.args, false)
        .map_err(CheckerError::from)?;

    let mut proofs: HashMap<u64, Rc<ProofNode>> = premise_terms
        .iter()
        .zip(&step.premises)
        .map(|(clause, premise)| (hash_term(pool, clause.clone()), premise.clone()))
        .collect();
    let mut ids = IdHelper::new(&step.id);

    for (action, argument) in trace.into_iter().zip(&step.args) {
        let DRupProofAction::RupStory(goal_literals, history) = action else {
            continue;
        };
        let goal_clause = match_term!((cl ...) = argument)
            .ok_or(ElaborationError::InvalidDrupTrace(
                "addition argument is not a clause",
            ))?
            .to_vec();

        let (final_literals, _, final_hash) = history
            .last()
            .ok_or(ElaborationError::InvalidDrupTrace("RUP history is empty"))?;
        let mut current_literals = final_literals.clone();
        let mut current_proof = proofs
            .get(final_hash)
            .ok_or(ElaborationError::DrupMissingClause(*final_hash))?
            .clone();

        for (source_literals, pivot, source_hash) in history[..history.len() - 1].iter().rev() {
            if current_literals.is_subset(&goal_literals) {
                break;
            }

            let pivot = pivot.as_ref().ok_or(ElaborationError::InvalidDrupTrace(
                "a non-final RUP entry has no pivot",
            ))?;
            if !current_literals.contains(&(!pivot.0, pivot.1.clone())) {
                continue;
            }

            let source_proof = proofs
                .get(source_hash)
                .ok_or(ElaborationError::DrupMissingClause(*source_hash))?
                .clone();
            current_literals = resolve(source_literals, &current_literals, &pivot.1);
            let clause = clause_from_literals(pool, &current_literals);
            current_proof = Rc::new(ProofNode::Step(StepNode {
                id: ids.next_id(),
                depth: step.depth,
                clause,
                rule: "resolution".to_owned(),
                premises: vec![source_proof, current_proof],
                args: vec![pivot.1.clone(), pool.bool_constant(pivot.0)],
                ..Default::default()
            }));
        }

        if !current_literals.is_subset(&goal_literals) {
            return Err(ElaborationError::InvalidDrupTrace(
                "RUP trace reaches a goal assumption before deriving the goal",
            ));
        }

        let proof = finish_goal(
            &mut ids,
            step.depth,
            &current_literals,
            current_proof,
            &goal_literals,
            goal_clause,
        );
        proofs.insert(hash_term(pool, argument.clone()), proof);
    }

    proofs
        .get(&hash_term(pool, conclusion))
        .cloned()
        .ok_or(ElaborationError::InvalidDrupTrace(
            "the conclusion has no reconstructed proof",
        ))
}
