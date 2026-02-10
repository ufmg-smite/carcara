use super::{
    assert_clause_len, assert_eq, assert_is_bool_constant, assert_num_args, assert_num_premises,
    CheckerError, Premise, RuleArgs, RuleResult,
};
use crate::{ast::*, resolution::*, utils::MultiSet};
use indexmap::IndexSet;

pub fn resolution(rule_args: RuleArgs) -> RuleResult {
    if !rule_args.args.is_empty() {
        // If the rule was given arguments, we redirect to the variant of "resolution" that takes
        // the pivots as arguments
        return resolution_with_args(rule_args);
    }
    let RuleArgs { conclusion, premises, pool, .. } = rule_args;

    // In some cases, this rule is used with a single premise `(not true)` to justify an empty
    // conclusion clause
    if conclusion.is_empty() && premises.len() == 1 {
        if let [t] = premises[0].clause {
            if match_term!((not true) = t).is_some() {
                return Ok(());
            }
        }
    }
    // Aside from this special case, all resolution steps must be between at least two clauses
    assert_num_premises(premises, 2..)?;

    let premise_clauses: Vec<_> = premises.iter().map(|p| p.clause).collect();

    greedy_resolution(conclusion, &premise_clauses, pool, false)
        .map(|_| ())
        .or_else(|greedy_error| {
            if rup_resolution(conclusion, premises) {
                Ok(())
            } else {
                // If RUP resolution also fails, we return the error originally returned by the greedy
                // algorithm
                Err(greedy_error.into())
            }
        })
}

fn rup_resolution(conclusion: &[Rc<Term>], premises: &[Premise]) -> bool {
    let mut clauses: Vec<IndexSet<(bool, &Rc<Term>)>> = premises
        .iter()
        .map(|p| {
            p.clause
                .iter()
                .map(Rc::remove_all_negations_with_polarity)
                .collect()
        })
        .collect();
    clauses.extend(conclusion.iter().map(|t| {
        let (p, t) = t.remove_all_negations_with_polarity();
        let mut clause = IndexSet::new();
        clause.insert((!p, t));
        clause
    }));

    loop {
        if clauses.is_empty() {
            return false;
        }
        let smallest = clauses.iter().min_by_key(|c| c.len()).unwrap();
        match smallest.len() {
            0 => return true,
            1 => {
                let literal = *smallest.iter().next().unwrap();
                let negated_literal = (!literal.0, literal.1);

                // Remove all clauses that contain the literal
                clauses.retain(|c| !c.contains(&literal));

                // Remove the negated literal from all clauses that contain it
                for c in &mut clauses {
                    c.swap_remove(&negated_literal);
                }
            }
            _ => return false,
        }
    }
}

pub fn resolution_with_args(
    RuleArgs {
        conclusion, premises, args, pool, ..
    }: RuleArgs,
) -> RuleResult {
    let resolution_result = apply_generic_resolution::<IndexSet<_>>(premises, args, pool)?;

    let conclusion: IndexSet<_> = conclusion.iter().map(Rc::remove_all_negations).collect();

    if let Some(extra) = conclusion.difference(&resolution_result).next() {
        let extra = literal_to_term(pool, *extra);
        return Err(ResolutionError::ExtraTermInConclusion(extra).into());
    }
    if let Some(missing) = resolution_result.difference(&conclusion).next() {
        let missing = literal_to_term(pool, *missing);
        return Err(ResolutionError::MissingTermInConclusion(missing).into());
    }
    Ok(())
}

pub fn strict_resolution(
    RuleArgs {
        conclusion, premises, args, pool, ..
    }: RuleArgs,
) -> RuleResult {
    use std::cmp::Ordering;

    let resolution_result = apply_generic_resolution::<Vec<_>>(premises, args, pool)?;

    match conclusion.len().cmp(&resolution_result.len()) {
        Ordering::Less => {
            let missing = literal_to_term(pool, resolution_result[conclusion.len()]);
            Err(ResolutionError::MissingTermInConclusion(missing).into())
        }
        Ordering::Greater => {
            let extra = conclusion[resolution_result.len()].clone();
            Err(ResolutionError::ExtraTermInConclusion(extra).into())
        }
        Ordering::Equal => {
            for (t, u) in resolution_result.into_iter().zip(conclusion) {
                if t != u.remove_all_negations() {
                    assert_eq(&literal_to_term(pool, t), u)?;
                }
            }
            Ok(())
        }
    }
}

fn apply_generic_resolution<'a, C: ClauseCollection<'a>>(
    premises: &'a [Premise],
    args: &'a [Rc<Term>],
    pool: &mut dyn TermPool,
) -> Result<C, CheckerError> {
    assert_num_premises(premises, 2..)?;
    let num_steps = premises.len() - 1;
    assert_num_args(args, num_steps * 2)?;

    let args: Vec<_> = args
        .chunks(2)
        .map(|chunk| {
            let pivot = chunk[0].remove_all_negations();
            let polarity = chunk[1].clone();
            let polarity = if polarity.is_bool_true() {
                true
            } else if polarity.is_bool_false() {
                false
            } else {
                return Err(CheckerError::ExpectedAnyBoolConstant(polarity.clone()));
            };
            Ok((pivot, polarity))
        })
        .collect::<Result<_, _>>()?;

    let mut current = premises[0]
        .clause
        .iter()
        .map(Rc::remove_all_negations)
        .collect();

    for (premise, (pivot, polarity)) in premises[1..].iter().zip(args) {
        binary_resolution(pool, &mut current, premise.clause, pivot, polarity)?;
    }

    Ok(current)
}

fn binary_resolution<'a, C: ClauseCollection<'a>>(
    pool: &mut dyn TermPool,
    current: &mut C,
    next: &'a [Rc<Term>],
    pivot: Literal<'a>,
    is_pivot_in_current: bool,
) -> Result<(), ResolutionError> {
    let negated_pivot = (pivot.0 + 1, pivot.1);
    let (pivot_in_current, pivot_in_next) = if is_pivot_in_current {
        (pivot, negated_pivot)
    } else {
        (negated_pivot, pivot)
    };
    if !current.remove_term(&pivot_in_current) {
        let p = literal_to_term(pool, pivot_in_current);
        return Err(ResolutionError::PivotNotFound(p));
    }

    let mut found = false;
    for t in next {
        let t = t.remove_all_negations();
        if !found && t == pivot_in_next {
            found = true;
        } else {
            current.insert_term(t);
        }
    }
    if !found {
        let p = literal_to_term(pool, pivot_in_next);
        return Err(ResolutionError::PivotNotFound(p));
    }
    Ok(())
}

pub fn tautology(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;
    assert_is_bool_constant(&conclusion[0], true)?;

    let premise = premises[0].clause;
    let mut seen = IndexSet::with_capacity(premise.len());
    let with_negations_removed = premise.iter().map(Rc::remove_all_negations_with_polarity);
    for (polarity, term) in with_negations_removed {
        if seen.contains(&(!polarity, term)) {
            return Ok(());
        }
        seen.insert((polarity, term));
    }
    Err(ResolutionError::TautologyFailed.into())
}

pub fn contraction(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;

    let premise_set: MultiSet<_> = premises[0].clause.iter().collect();
    let conclusion_set: MultiSet<_> = conclusion.iter().collect();
    for (&t, &count) in &premise_set.0 {
        let got = conclusion_set.get(&t);
        if got == 0 {
            return Err(CheckerError::ContractionMissingTerm(t.clone()));
        } else if got > count {
            return Err(CheckerError::ContractionExtraTerm(t.clone()));
        }
    }
    for (t, count) in conclusion_set.0 {
        if premise_set.get(&t) < count {
            return Err(CheckerError::ContractionExtraTerm(t.clone()));
        }
    }
    Ok(())
}
