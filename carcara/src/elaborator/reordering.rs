use super::*;
use crate::{checker::error::CheckerError, resolution::ResolutionError, utils::DedupIterator};

pub fn remove_reorderings(proof: ProofNodeForest) -> Result<ProofNodeForest, crate::Error> {
    proof.mutate(|_, node, premises_changed| {
        let Some(step) = node.as_step() else {
            return Ok(node.clone());
        };

        // For reordering steps, we remove the step and return its only premise
        if step.rule == "reordering" {
            return Ok(step.premises[0].clone());
        }

        // If the rule is order-sensitive, and any premise was modified, we recompute the conclusion
        if let Some(recompute) = get_recomputation_func(&step.rule) {
            if premises_changed {
                let new = Rc::new(ProofNode::Step(StepNode {
                    clause: recompute(step).map_err(|e| e.at(step))?,
                    ..step.clone()
                }));
                return Ok(new);
            }
        }

        // Otherwise the node is unchanged
        Ok(node.clone())
    })
}

type RecomputationFunc = fn(&StepNode) -> Result<Vec<Rc<Term>>, ElaborationError>;

fn get_recomputation_func(rule: &str) -> Option<RecomputationFunc> {
    Some(match rule {
        // Weakening and contraction recomputation is infallibe, so we have to wrap in `Ok`
        "weakening" => |step| Ok(recompute_weakening(step)),
        "contraction" => |step| Ok(recompute_contraction(step)),
        "resolution" | "th_resolution" | "strict_resolution" => recompute_resolution,
        _ => return None,
    })
}

fn recompute_weakening(step: &StepNode) -> Vec<Rc<Term>> {
    let mut new = step.clause.clone();
    let premise = step.premises[0].clause();
    new[..premise.len()].clone_from_slice(premise);
    new
}

fn recompute_contraction(step: &StepNode) -> Vec<Rc<Term>> {
    let new: Vec<_> = step.premises[0].clause().iter().dedup().cloned().collect();
    new
}

fn recompute_resolution(step: &StepNode) -> Result<Vec<Rc<Term>>, ElaborationError> {
    if step.premises.len() < 2 {
        return Err(CheckerError::WrongNumberOfPremises((2..).into(), step.premises.len()).into());
    }
    let num_args = 2 * (step.premises.len() - 1);
    if step.args.len() != num_args {
        return Err(CheckerError::WrongNumberOfArgs(num_args.into(), step.args.len()).into());
    }

    let premise_clauses: Vec<_> = step.premises.iter().map(|p| p.clause()).collect();
    let pivots: Vec<_> = step
        .args
        .chunks(2)
        .map(|chunk| {
            let pivot = &chunk[0];
            let polarity = chunk[1].is_bool_true();
            (pivot, polarity)
        })
        .collect();
    Ok(apply_naive_resolution(&premise_clauses, &pivots)?)
}

fn apply_naive_resolution(
    premises: &[&[Rc<Term>]],
    pivots: &[(&Rc<Term>, bool)],
) -> Result<Vec<Rc<Term>>, ResolutionError> {
    let mut current = premises[0].to_vec();

    for (&premise, &(pivot, polarity)) in premises[1..].iter().zip(pivots) {
        let is_pivot = |x: &Rc<Term>, is_current: bool| {
            if is_current == polarity {
                x == pivot
            } else {
                x.remove_negation() == Some(pivot)
            }
        };

        let pos = current
            .iter()
            .position(|x| is_pivot(x, true))
            .ok_or_else(|| ResolutionError::PivotNotFound(pivot.clone()))?;
        current.remove(pos);

        let mut found = false;
        for t in premise {
            if !found && is_pivot(t, false) {
                found = true;
            } else {
                current.push(t.clone());
            }
        }
        if !found {
            return Err(ResolutionError::PivotNotFound(pivot.clone()));
        }
    }

    Ok(current)
}
