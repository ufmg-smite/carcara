use rapidhash::{HashSetExt, RapidHashSet};

use super::*;
use crate::{
    checker::error::CheckerError,
    resolution::ResolutionError,
    utils::{MultiSet, MultiSetDifference},
};

pub fn remove_reorderings(
    proof: ProofNodeForest,
) -> Result<ProofNodeForest, ElaborationErrorAtStep> {
    proof.mutate(|_, node, premises_changed| {
        let Some(step) = node.as_step() else {
            return Ok(node.clone());
        };

        // For reordering steps, we remove the step and return its only premise
        if step.rule == "reordering" {
            return Ok(step.premises[0].clone());
        }

        // If the rule is order-sensitive, and any premise was modified, we recompute the conclusion
        if let Some(recompute) = get_recomputation_func(&step.rule)
            && premises_changed
        {
            let new = Rc::new(ProofNode::Step(StepNode {
                clause: recompute(step).map_err(|e| e.at(step))?,
                ..step.clone()
            }));
            return Ok(new);
        }

        // Otherwise the node is unchanged
        Ok(node.clone())
    })
}

type RecomputationFunc = fn(&StepNode) -> Result<Vec<Rc<Term>>, ElaborationError>;

fn get_recomputation_func(rule: &str) -> Option<RecomputationFunc> {
    Some(match rule {
        // Weakening and contraction recomputation is infallible, so we have to wrap in `Ok`
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
    // Doing this is slightly faster than using `.iter().dedup().collect()`
    let mut seen = RapidHashSet::new();
    let mut new = step.premises[0].clause().to_vec();
    new.retain(|elem| seen.insert(elem.clone()));
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
    let result = apply_naive_resolution(&premise_clauses, &pivots)?;

    // If the step relies on implicit contraction, the naive result will have more terms than the
    // original conclusion. Since `resolution` doesn't care about the order of the terms in the
    // conclusion, we can just keep the original conclusion in that case. This ensures that the
    // recomputed conclusion is always a permutation of the original one.
    //
    // This is only relevant if the uncrowding pass was not applied before this one, which is not
    // the case for the default elaboration pipeline
    let [result_set, conclusion_set] =
        [&result, &step.clause].map(|c| c.iter().collect::<MultiSet<_>>());
    match result_set.symmetric_difference(&conclusion_set) {
        MultiSetDifference::None => Ok(result),
        _ => Ok(step.clause.clone()),
    }
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
