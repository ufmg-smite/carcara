use super::{
    assert_clause_len, assert_eq, assert_is_bool_constant, assert_is_expected, assert_num_args,
    assert_num_premises, CheckerError, Premise, RuleArgs, RuleResult,
};
use crate::{
    ast::*,
    checker::{error::ResolutionError, Elaborator},
    utils::DedupIterator,
};
use ahash::{AHashMap, AHashSet};
use std::{collections::hash_map::Entry, iter::FromIterator};

type ResolutionTerm<'a> = (u32, &'a Rc<Term>);

/// A collection that can be used as a clause during resolution.
trait ClauseCollection<'a>: FromIterator<ResolutionTerm<'a>> {
    fn insert_term(&mut self, item: ResolutionTerm<'a>);

    fn remove_term(&mut self, item: &ResolutionTerm<'a>) -> bool;
}

impl<'a> ClauseCollection<'a> for Vec<ResolutionTerm<'a>> {
    fn insert_term(&mut self, item: ResolutionTerm<'a>) {
        self.push(item);
    }

    fn remove_term(&mut self, item: &ResolutionTerm<'a>) -> bool {
        if let Some(pos) = self.iter().position(|x| x == item) {
            self.remove(pos);
            true
        } else {
            false
        }
    }
}

impl<'a> ClauseCollection<'a> for AHashSet<ResolutionTerm<'a>> {
    fn insert_term(&mut self, item: ResolutionTerm<'a>) {
        self.insert(item);
    }

    fn remove_term(&mut self, item: &ResolutionTerm<'a>) -> bool {
        self.remove(item)
    }
}

/// Undoes the transformation done by `Rc<Term>::remove_all_negations`.
fn unremove_all_negations(pool: &mut TermPool, (n, term): ResolutionTerm) -> Rc<Term> {
    let mut term = term.clone();
    for _ in 0..n {
        term = build_term!(pool, (not { term }));
    }
    term
}

pub fn resolution(rule_args: RuleArgs) -> RuleResult {
    if !rule_args.args.is_empty() {
        // If the rule was given arguments, we redirect to the variant of "resolution" that takes
        // the pivots as arguments
        return resolution_with_args(rule_args);
    }
    let RuleArgs { conclusion, premises, pool, .. } = rule_args;

    greedy_resolution(conclusion, premises, pool, false)
        .map(|_| ())
        .or_else(|greedy_error| {
            if rup_resolution(conclusion, premises) {
                Ok(())
            } else {
                // If RUP resolution also fails, we return the error originally returned by the greedy
                // algorithm
                Err(greedy_error)
            }
        })
}

struct ResolutionTrace {
    not_not_added: bool,
    pivot_trace: Vec<(Rc<Term>, bool)>,
}

fn greedy_resolution(
    conclusion: &[Rc<Term>],
    premises: &[Premise],
    pool: &mut TermPool,
    tracing: bool,
) -> Result<ResolutionTrace, CheckerError> {
    // If we are elaborating, we record which pivot was found for each binary resolution step, so we
    // can add them all as arguments later
    let mut pivot_trace = Vec::new();

    // In some cases, this rule is used with a single premise `(not true)` to justify an empty
    // conclusion clause
    if conclusion.is_empty() && premises.len() == 1 {
        if let [t] = premises[0].clause {
            if match_term!((not true) = t).is_some() {
                return Ok(ResolutionTrace { not_not_added: false, pivot_trace });
            }
        }
    }

    // When checking this rule, we must look at what the conclusion clause looks like in order to
    // determine the pivots. The reason for that is because there is no other way to know which
    // terms should be removed in a given binary resolution step. Consider the following example,
    // adapted from an actual generated proof:
    //
    //     (step t1 (cl (not q) (not (not p)) (not p)) :rule irrelevant)
    //     (step t2 (cl (not (not (not p))) p) :rule irrelevant)
    //     (step t3 (cl (not q) p (not p)) :rule resolution :premises (t1 t2))
    //
    // Without looking at the conclusion, it is unclear if the (not p) term should be removed by the
    // p term, or if the (not (not p)) should be removed by the (not (not (not p))). We can only
    // determine this by looking at the conclusion and using it to derive the pivots.
    let conclusion: AHashSet<_> = conclusion
        .iter()
        .map(Rc::remove_all_negations)
        .map(|(n, t)| (n as i32, t))
        .collect();

    // The working clause contains the terms from the conclusion clause that we already encountered
    let mut working_clause = AHashSet::new();

    // The pivots are the encountered terms that are not present in the conclusion clause, and so
    // should be removed. After being used to eliminate a term, a pivot can still be used to
    // eliminate other terms. Because of that, we represent the pivots as a hash map to a boolean,
    // which represents if the pivot was already eliminated or not. At the end, this boolean should
    // be true for all pivots
    let mut pivots = AHashMap::new();

    for premise in premises {
        // Only one pivot may be eliminated per clause. This restriction is required so logically
        // unsound proofs like this one are not considered valid:
        //
        //     (step t1 (cl (= false true) (not false) (not true)) :rule equiv_neg1)
        //     (step t2 (cl (= false true) false true) :rule equiv_neg2)
        //     (step t3 (cl (= false true)) :rule resolution :premises (t1 t2))
        let mut eliminated_clause_pivot = false;
        for term in premise.clause {
            let (n, inner) = term.remove_all_negations();
            let n = n as i32;

            // There are two possible negations of a term, with one leading negation added, or with
            // one leading negation removed (if the term had any in the first place)
            let below = (n - 1, inner);
            let above = (n + 1, inner);

            // First, if the encountered term should be in the conclusion, but is not yet in the
            // working clause, we insert it and don't try to remove it with a pivot
            if conclusion.contains(&(n, inner)) && !working_clause.contains(&(n, inner)) {
                working_clause.insert((n, inner));
                continue;
            }

            // If the negation of the encountered term is present in the pivots set, we simply
            // eliminate it. Otherwise, we insert the encountered term in the working clause or the
            // pivots set, depending on whether it is present in the conclusion clause or not
            let mut try_eliminate = |pivot| match pivots.entry(pivot) {
                Entry::Occupied(mut e) => {
                    e.insert(true);
                    true
                }
                Entry::Vacant(_) => false,
            };

            // Only one pivot may be eliminated per clause, so if we already found this clauses'
            // pivot, we don't try to eliminate the term. If we are elaborating, we add the pivot
            // found to the pivot trace.
            let eliminated = if eliminated_clause_pivot {
                false
            } else if try_eliminate(below) {
                if tracing {
                    pivot_trace.push((unremove_all_negations(pool, (n as u32 - 1, inner)), true));
                }
                true
            } else if try_eliminate(above) {
                if tracing {
                    pivot_trace.push((term.clone(), false));
                }
                true
            } else {
                false
            };

            if eliminated {
                eliminated_clause_pivot = true;
            } else if conclusion.contains(&(n, inner)) {
                working_clause.insert((n, inner));
            } else {
                // If the term is not in the conclusion clause, it must be a pivot. If it was
                // not already in the pivots set, we insert `false`, to indicate that it was
                // not yet eliminated
                pivots.entry((n, inner)).or_insert(false);
            }
        }
    }

    // There are some special cases in the resolution rules that are valid, but leave a pivot
    // remaining
    let mut remaining_pivots = pivots.iter().filter(|&(_, eliminated)| !eliminated);

    if let Some(((i, pivot), _)) = remaining_pivots.next() {
        if remaining_pivots.next().is_none() {
            // There is a special case in the resolution rules that is valid, but leaves a pivot
            // remaining: when the result of the resolution is just the boolean constant `false`, it
            // may be implicitly eliminated. For example:
            //     (step t1 (cl p q false) :rule hole)
            //     (step t2 (cl (not p)) :rule hole)
            //     (step t3 (cl (not q)) :rule hole)
            //     (step t4 (cl) :rule resolution :premises (t1 t2 t3))
            if conclusion.is_empty() && *i == 0 && pivot.is_bool_false() {
                return Ok(ResolutionTrace { not_not_added: false, pivot_trace });
            }

            // There is another, similar, special case: when the result of the resolution is just
            // one term, it may appear in the conclusion clause with an even number of leading
            // negations added to it. The following is an example of this, adapted from a generated
            // proof:
            //     (step t1 (cl (not e)) :rule hole)
            //     (step t2 (cl (= (not e) (not (not f)))) :rule hole)
            //     (step t3 (cl (not (= (not e) (not (not f)))) e f) :rule hole)
            //     (step t4 (cl (not (not f))) :rule resolution :premises (t1 t2 t3))
            // Usually, we would expect the clause in the t4 step to be (cl f). This behavior may
            // be a bug in veriT, but it is still logically sound and happens often enough that it
            // is useful to support it here.
            if conclusion.len() == 1 {
                let (j, conclusion) = conclusion.into_iter().next().unwrap();
                if conclusion == *pivot && (i % 2) == (j % 2) {
                    return Ok(ResolutionTrace { not_not_added: true, pivot_trace });
                }
            }
        }
        let pivot = unremove_all_negations(pool, (*i as u32, pivot));
        Err(ResolutionError::RemainingPivot(pivot).into())
    } else {
        // This is the general case, where all pivots have been eliminated. In this case, the
        // working clause should be equal to the conclusion clause
        for (i, t) in conclusion {
            // By construction, the working clause is a subset of the conclusion. Therefore, we
            // only need to check that all terms in the conclusion are also in the working clause
            if !working_clause.contains(&(i, t)) {
                let t = unremove_all_negations(pool, (i as u32, t));
                return Err(ResolutionError::ExtraTermInConclusion(t).into());
            }
        }
        Ok(ResolutionTrace { not_not_added: false, pivot_trace })
    }
}

fn rup_resolution(conclusion: &[Rc<Term>], premises: &[Premise]) -> bool {
    let mut clauses: Vec<AHashSet<(bool, &Rc<Term>)>> = premises
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
        let mut clause = AHashSet::new();
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
                    c.remove(&negated_literal);
                }
            }
            _ => return false,
        }
    }
}

fn resolution_with_args(
    RuleArgs {
        conclusion, premises, args, pool, ..
    }: RuleArgs,
) -> RuleResult {
    let resolution_result = apply_generic_resolution::<AHashSet<_>>(premises, args, pool)?;

    let conclusion: AHashSet<_> = conclusion.iter().map(Rc::remove_all_negations).collect();

    if let Some(extra) = conclusion.difference(&resolution_result).next() {
        let extra = unremove_all_negations(pool, *extra);
        return Err(ResolutionError::ExtraTermInConclusion(extra).into());
    }
    if let Some(missing) = resolution_result.difference(&conclusion).next() {
        let missing = unremove_all_negations(pool, *missing);
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
            let missing = unremove_all_negations(pool, resolution_result[conclusion.len()]);
            Err(ResolutionError::MissingTermInConclusion(missing).into())
        }
        Ordering::Greater => {
            let extra = conclusion[resolution_result.len()].clone();
            Err(ResolutionError::ExtraTermInConclusion(extra).into())
        }
        Ordering::Equal => {
            for (t, u) in resolution_result.into_iter().zip(conclusion) {
                if t != u.remove_all_negations() {
                    assert_eq(&unremove_all_negations(pool, t), u)?;
                }
            }
            Ok(())
        }
    }
}

fn apply_generic_resolution<'a, C: ClauseCollection<'a>>(
    premises: &'a [Premise],
    args: &'a [ProofArg],
    pool: &mut TermPool,
) -> Result<C, CheckerError> {
    assert_num_premises(premises, 1..)?;
    let num_steps = premises.len() - 1;
    assert_num_args(args, num_steps * 2)?;

    let args: Vec<_> = args
        .chunks(2)
        .map(|chunk| {
            let pivot = chunk[0].as_term()?.remove_all_negations();
            let polarity = chunk[1].as_term()?;
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
    pool: &mut TermPool,
    current: &mut C,
    next: &'a [Rc<Term>],
    pivot: ResolutionTerm<'a>,
    is_pivot_in_current: bool,
) -> Result<(), ResolutionError> {
    let negated_pivot = (pivot.0 + 1, pivot.1);
    let (pivot_in_current, pivot_in_next) = if is_pivot_in_current {
        (pivot, negated_pivot)
    } else {
        (negated_pivot, pivot)
    };
    if !current.remove_term(&pivot_in_current) {
        let p = unremove_all_negations(pool, pivot_in_current);
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
        let p = unremove_all_negations(pool, pivot_in_next);
        return Err(ResolutionError::PivotNotFound(p));
    }
    Ok(())
}

pub fn elaborate_resolution(
    RuleArgs { conclusion, premises, pool, .. }: RuleArgs,
    command_id: String,
    elaborator: &mut Elaborator,
) -> RuleResult {
    let mut premises = premises.to_vec();
    let ResolutionTrace { not_not_added, pivot_trace } =
        greedy_resolution(conclusion, &premises, pool, true).or_else(|_| {
            premises.reverse();
            greedy_resolution(conclusion, &premises, pool, true)
        })?;

    let pivots = pivot_trace
        .into_iter()
        .flat_map(|(pivot, polarity)| [pivot, pool.bool_constant(polarity)])
        .map(ProofArg::Term)
        .collect();

    let premises: Vec<_> = premises
        .iter()
        .map(|p| elaborator.map_index(p.index))
        .collect();

    let mut resolution_step = ProofStep {
        id: command_id.clone(),
        clause: conclusion.to_vec(),
        rule: "resolution".to_owned(),
        premises,
        args: pivots,
        discharge: Vec::new(),
    };

    if not_not_added {
        // In this case, where the solver added a double negation implicitly to the concluded term,
        // we remove it from the resolution conclusion, and then add a series of steps to
        // reconstruct it again. More precisely, if the conclusion of the resolution step should
        // have been `c`, but was instead `(not (not c))`, we will have:
        //
        // ```
        // (step t1 (cl (not (not c))) :rule resolution :premises ...)
        // ```
        //
        // which will become:
        //
        // ```
        // (step t1 (cl c) :rule resolution :premises ...)
        // (step t1.t2 (cl (not (not (not (not c)))) (not c)) :rule not_not)
        // (step t1.t3 (cl (not (not (not (not (not c))))) (not (not c))) :rule not_not)
        // (step t1.t4 (cl (not (not c))) :rule resolution :premises (t1 t1.t2 t1.t3)
        //     :args (c true (not (not (not (not c)))) true))
        // ```

        assert!(resolution_step.clause.len() == 1);
        let original_conclusion = resolution_step.clause;
        let double_not_c = original_conclusion[0].clone();
        let single_not_c = double_not_c.remove_negation().unwrap().clone();
        let c = single_not_c.remove_negation().unwrap().clone();
        let quadruple_not_c = build_term!(pool, (not (not {double_not_c.clone()})));
        let quintuple_not_c = build_term!(pool, (not {quadruple_not_c.clone()}));

        // First, we change the conclusion of the resolution step
        resolution_step.clause = vec![c.clone()];
        let resolution_step = elaborator.add_new_step(resolution_step);

        // Then we add the two `not_not` steps
        let id = elaborator.get_new_id(&command_id);
        let first_not_not_step = elaborator.add_new_step(ProofStep {
            id,
            clause: vec![quadruple_not_c.clone(), single_not_c],
            rule: "not_not".to_owned(),
            premises: Vec::new(),
            args: Vec::new(),
            discharge: Vec::new(),
        });
        let id = elaborator.get_new_id(&command_id);
        let second_not_not_step = elaborator.add_new_step(ProofStep {
            id,
            clause: vec![quintuple_not_c, double_not_c.clone()],
            rule: "not_not".to_owned(),
            premises: Vec::new(),
            args: Vec::new(),
            discharge: Vec::new(),
        });

        // Finally, we add a new resolution step, refering to the preivous three, and concluding the
        // original resolution step's conclusion
        let args = [c, pool.bool_true(), quadruple_not_c, pool.bool_true()]
            .into_iter()
            .map(ProofArg::Term)
            .collect();
        let id = elaborator.get_new_id(&command_id);
        elaborator.push_elaborated_step(ProofStep {
            id,
            clause: vec![double_not_c],
            rule: "resolution".to_owned(),
            premises: vec![resolution_step, first_not_not_step, second_not_not_step],
            args,
            discharge: Vec::new(),
        });
    } else {
        elaborator.push_elaborated_step(resolution_step);
    }
    Ok(())
}

pub fn tautology(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;
    assert_is_bool_constant(&conclusion[0], true)?;

    let premise = premises[0].clause;
    let mut seen = AHashSet::with_capacity(premise.len());
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

    let expected: Vec<_> = premises[0].clause.iter().dedup().collect();
    assert_clause_len(conclusion, expected.len())?;

    for (t, u) in conclusion.iter().zip(expected) {
        assert_is_expected(t, u.clone())?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn resolution() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
                (declare-fun t () Bool)
                (declare-fun u () Bool)
            ",
            "Simple working examples" {
                "(assume h1 (not p))
                (step t2 (cl p q) :rule hole)
                (step t3 (cl q) :rule resolution :premises (h1 t2))": true,

                "(step t1 (cl (not p) (not q) (not r)) :rule hole)
                (step t2 (cl p) :rule hole)
                (step t3 (cl q) :rule hole)
                (step t4 (cl r) :rule hole)
                (step t5 (cl) :rule resolution :premises (t1 t2 t3 t4))": true,
            }
            "Missing term in final clause" {
                "(assume h1 (not p))
                (step t2 (cl p q r) :rule hole)
                (step t3 (cl q) :rule resolution :premises (h1 t2))": false,
            }
            "Term appears in final clause with wrong polarity" {
                "(assume h1 (not p))
                (step t2 (cl p q r) :rule hole)
                (step t3 (cl (not q) r) :rule resolution :premises (h1 t2))": false,
            }
            "Duplicate term in final clause" {
                "(step t1 (cl q (not p)) :rule hole)
                (step t2 (cl p q r) :rule hole)
                (step t3 (cl q q r) :rule resolution :premises (t1 t2))": true,
            }
            "Terms with leading negations" {
                "(assume h1 (not p))
                (assume h2 (not (not p)))
                (assume h3 (not (not (not p))))
                (assume h4 (not (not (not (not p)))))
                (step t5 (cl) :rule resolution :premises (h1 h2))
                (step t6 (cl) :rule resolution :premises (h2 h3))
                (step t7 (cl (not p) (not (not (not p)))) :rule resolution :premises (h1 h3))
                (step t8 (cl (not p) (not (not (not (not p)))))
                    :rule resolution :premises (h1 h4))": true,
            }
            "Must use correct pivots" {
                "(step t1 (cl (not q) (not (not p)) (not p)) :rule hole)
                (step t2 (cl (not (not (not p))) p) :rule hole)
                (step t3 (cl (not q) p (not p)) :rule resolution :premises (t1 t2))": true,

                "(step t1 (cl (not q) (not (not p)) (not p)) :rule hole)
                (step t2 (cl (not (not (not p))) p) :rule hole)
                (step t3 (cl (not q) (not (not (not p))) (not (not p)))
                    :rule resolution :premises (t1 t2))": true,

                "(step t1 (cl (not q) (not (not p)) (not p)) :rule hole)
                (step t2 (cl (not (not (not p))) p) :rule hole)
                (step t3 (cl (not q) p (not p) (not (not (not p))) (not (not p)))
                    :rule resolution :premises (t1 t2))": true,
            }
            "Weird behaviour where leading negations sometimes are added to conclusion" {
                "(assume h1 (not p))
                (step t2 (cl p q) :rule hole)
                (step t3 (cl (not (not q))) :rule resolution :premises (h1 t2))": true,
            }
            "Premise is \"(not true)\" and leads to empty conclusion clause" {
                "(step t1 (cl (not true)) :rule hole)
                (step t2 (cl) :rule th_resolution :premises (t1))": true,
            }
            "Repeated premises" {
                "(step t1 (cl (not r)) :rule hole)
                (step t2 (cl p q r s) :rule hole)
                (step t3 (cl p q s) :rule th_resolution :premises (t1 t2 t2))": true,
            }
            "Implicit elimination of \"(cl false)\"" {
                "(step t1 (cl p q false) :rule hole)
                (step t2 (cl (not p)) :rule hole)
                (step t3 (cl (not q)) :rule hole)
                (step t4 (cl) :rule resolution :premises (t1 t2 t3))": true,

                // This implicit elimination is allowed, but not required
                "(step t1 (cl p q false) :rule hole)
                (step t2 (cl (not p)) :rule hole)
                (step t3 (cl (not q)) :rule hole)
                (step t4 (cl false) :rule resolution :premises (t1 t2 t3))": true,
            }
            "Pivots given in arguments" {
                "(step t1 (cl p q r) :rule hole)
                (step t2 (cl (not q) s) :rule hole)
                (step t3 (cl p r s) :rule resolution :premises (t1 t2) :args (q true))": true,

                "(step t1 (cl p (not q) r) :rule hole)
                (step t2 (cl (not r) s q) :rule hole)
                (step t3 (cl p r (not r) s)
                    :rule resolution :premises (t1 t2) :args (q false))": true,

                "(step t1 (cl p q) :rule hole)
                (step t2 (cl (not q) (not r)) :rule hole)
                (step t3 (cl (not s) (not (not r)) t) :rule hole)
                (step t4 (cl s (not t) u) :rule hole)
                (step t5 (cl p t (not t) u)
                    :rule resolution
                    :premises (t1 t2 t3 t4)
                    :args (q true (not r) true s false))": true,
            }
            "Only one pivot eliminated per clause" {
                "(step t1 (cl p q r) :rule hole)
                (step t2 (cl (not q) (not r)) :rule hole)
                (step t3 (cl p) :rule resolution :premises (t1 t2))": false,
            }
            "`th_resolution` may receive premises in wrong order" {
                "(step t1 (cl (not p) (not q) (not r)) :rule hole)
                (step t2 (cl p) :rule hole)
                (step t3 (cl q) :rule hole)
                (step t4 (cl r) :rule hole)
                (step t5 (cl) :rule th_resolution :premises (t4 t3 t2 t1))": true,

                "(step t1 (cl (not p) (not q) (not r)) :rule hole)
                (step t2 (cl p) :rule hole)
                (step t3 (cl q) :rule hole)
                (step t4 (cl r) :rule hole)
                (step t5 (cl) :rule th_resolution :premises (t1 t2 t3 t4))": true,
            }
        }
    }

    #[test]
    fn strict_resolution() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
                (declare-fun t () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl p q r) :rule hole)
                (step t2 (cl s (not r) t) :rule hole)
                (step t3 (cl p q s t)
                    :rule strict_resolution
                    :premises (t1 t2)
                    :args (r true))": true,
            }
            "No implicit reordering" {
                "(step t1 (cl p q r) :rule hole)
                (step t2 (cl s (not r) t) :rule hole)
                (step t3 (cl t s q p)
                    :rule strict_resolution
                    :premises (t1 t2)
                    :args (r true))": false,

                "(step t1 (cl p q) :rule hole)
                (step t2 (cl r (not q) s) :rule hole)
                (step t3 (cl (not r) t) :rule hole)
                (step t4 (cl p t s)
                    :rule strict_resolution
                    :premises (t1 t2 t3)
                    :args (q true r true))": false,
            }
            "No implicit removal of duplicates" {
                "(step t1 (cl p q r) :rule hole)
                (step t2 (cl (not q) s) :rule hole)
                (step t3 (cl (not r) s) :rule hole)
                (step t4 (cl p s s)
                    :rule strict_resolution
                    :premises (t1 t2 t3)
                    :args (q true r true))": true,

                "(step t1 (cl p q r) :rule hole)
                (step t2 (cl (not q) s) :rule hole)
                (step t3 (cl (not r) s) :rule hole)
                (step t4 (cl p s)
                    :rule strict_resolution
                    :premises (t1 t2 t3)
                    :args (q true r true))": false,

                // Duplicates also can't be implicitly introduced
                "(step t1 (cl p q r) :rule hole)
                (step t2 (cl s (not r) t) :rule hole)
                (step t3 (cl p q s t s)
                    :rule strict_resolution
                    :premises (t1 t2)
                    :args (r true))": false,
            }
        }
    }

    #[test]
    fn tautology() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (not p) p) :rule hole)
                (step t2 (cl true) :rule tautology :premises (t1))": true,

                "(step t1 (cl p q (not q) r s) :rule hole)
                (step t2 (cl true) :rule tautology :premises (t1))": true,

                "(step t1 (cl p (not (not s)) q r (not (not (not s)))) :rule hole)
                (step t2 (cl true) :rule tautology  :premises (t1))": true,
            }
            "Conclusion is not \"true\"" {
                "(step t1 (cl p q (not q) r s) :rule hole)
                (step t2 (cl false) :rule tautology :premises (t1))": false,

                "(step t1 (cl p q (not q) r s) :rule hole)
                (step t2 (cl) :rule tautology :premises (t1))": false,
            }
            "Premise is not a tautology" {
                "(step t1 (cl p) :rule hole)
                (step t2 (cl true) :rule tautology :premises (t1))": false,

                "(step t1 (cl p (not (not s)) q r s) :rule hole)
                (step t2 (cl true) :rule tautology :premises (t1))": false,
            }
        }
    }

    #[test]
    fn contraction() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl p q q r s s) :rule hole)
                (step t2 (cl p q r s) :rule contraction :premises (t1))": true,

                "(step t1 (cl p p p q q r s s s) :rule hole)
                (step t2 (cl p q r s) :rule contraction :premises (t1))": true,

                "(step t1 (cl p q r s) :rule hole)
                (step t2 (cl p q r s) :rule contraction :premises (t1))": true,
            }
            "Number of premises != 1" {
                "(step t1 (cl p q) :rule contraction)": false,

                "(assume h1 q)
                (assume h2 p)
                (step t3 (cl p q) :rule contraction :premises (h1 h2))": false,
            }
            "Premise is not a \"step\" command" {
                "(assume h1 q)
                (step t2 (cl q) :rule contraction :premises (h1))": true,
            }
            "Encountered wrong term" {
                "(step t1 (cl p p q) :rule hole)
                (step t2 (cl p r) :rule contraction :premises (t1))": false,
            }
            "Terms are not in correct order" {
                "(step t1 (cl p q q r) :rule hole)
                (step t2 (cl p r q) :rule contraction :premises (t1))": false,
            }
            "Conclusion is missing terms" {
                "(step t1 (cl p q q r) :rule hole)
                (step t2 (cl p r) :rule contraction :premises (t1))": false,

                "(step t1 (cl p p q r) :rule hole)
                (step t2 (cl p q) :rule contraction :premises (t1))": false,
            }
            "Conclusion has extra term at the end" {
                "(step t1 (cl p p q) :rule hole)
                (step t2 (cl p q r s) :rule contraction :premises (t1))": false,
            }
        }
    }
}
