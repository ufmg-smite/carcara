use super::{
    assert_clause_len, assert_eq, assert_is_bool_constant, CheckerError, EqualityError, RuleArgs,
    RuleResult,
};
use crate::{ast::*, utils::DedupIterator};
use ahash::{AHashMap, AHashSet};
use num_rational::BigRational;
use num_traits::{One, Zero};

/// A macro to define the possible transformations for a "simplify" rule.
macro_rules! simplify {
    // This is a recursive macro that expands to a series of nested `match` expressions. For
    // example:
    //      simplify!(term {
    //          (or a b): (bind_a, bind_b) => foo,
    //          (not c): (bind_c) if pred(bind_c) => bar,
    //      })
    // becomes:
    //      match match_term!((or a b) = term) {
    //          Some((bind_a, bind_b)) => foo,
    //          _ => match match_term!((not c) = term) {
    //              Some(bind_c) if pred(bind_c) => bar,
    //              _ => None,
    //          }
    //      }
    ($term:ident {}) => { None };
    ($term:ident {
        $pat:tt: $idens:tt $(if $guard:expr)? => $res:expr,
        $($rest:tt)*
     }) => {
        match match_term!($pat = $term) {
            Some($idens) $(if $guard)? => Some($res),
            _ => simplify!($term { $($rest)* }),
        }
    };
}

fn generic_simplify_rule(
    conclusion: &[Rc<Term>],
    pool: &mut TermPool,
    simplify_function: fn(&Term, &mut TermPool) -> Option<Rc<Term>>,
) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let mut simplify_until_fixed_point =
        |term: &Rc<Term>, goal: &Rc<Term>| -> Result<Rc<Term>, CheckerError> {
            let mut current = term.clone();
            let mut seen = AHashSet::new();
            loop {
                if !seen.insert(current.clone()) {
                    return Err(CheckerError::CycleInSimplification(current.clone()));
                }
                match simplify_function(&current, pool) {
                    Some(next) => {
                        if next == *goal {
                            return Ok(next);
                        }
                        current = next;
                    }
                    None => return Ok(current),
                }
            }
        };

    let (left, right) = match_term_err!((= phi psi) = &conclusion[0])?;

    // Since equalities can be implicitly flipped, we have to check both possiblities. We store the
    // result of the first simplification to use in the error if both of them fail.
    let result = simplify_until_fixed_point(left, right)?;
    let got = result == *right || simplify_until_fixed_point(right, left)? == *left;
    rassert!(
        got,
        CheckerError::SimplificationFailed {
            original: left.clone(),
            result,
            target: right.clone(),
        },
    );
    Ok(())
}

pub fn ite_simplify(args: RuleArgs) -> RuleResult {
    generic_simplify_rule(args.conclusion, args.pool, |term, pool| {
        simplify!(term {
            // ite true t_1 t_2 => t_1
            (ite true t_1 t_2): (_, t_1, _) => t_1.clone(),

            // ite false t_1 t_2 => t_2
            (ite false t_1 t_2): (_, _, t_2) => t_2.clone(),

            // ite phi t t => t
            (ite phi t t): (_, t_1, t_2) if t_1 == t_2 => t_1.clone(),

            // ite psi true false => psi
            (ite psi true false): (psi, _, _) => psi.clone(),

            // ite psi false true => ¬psi
            (ite psi false true): (psi, _, _) => build_term!(pool, (not {psi.clone()})),

            // ite ¬phi t_1 t_2 => ite phi t_2 t_1
            (ite (not phi) t_1 t_2): (phi, t_1, t_2) => {
                build_term!(pool, (ite {phi.clone()} {t_2.clone()} {t_1.clone()}))
            },

            // ite phi (ite phi t_1 t_2) t_3 => ite phi t_1 t_3
            (ite phi (ite phi t_1 t_2) t_3): (phi_1, (phi_2, t_1, _), t_3) if phi_1 == phi_2 => {
                build_term!(pool, (ite {phi_1.clone()} {t_1.clone()} {t_3.clone()}))
            },

            // ite phi t_1 (ite phi t_2 t_3) => ite phi t_1 t_3
            (ite phi t_1 (ite phi t_2 t_3)): (phi_1, t_1, (phi_2, _, t_3)) if phi_1 == phi_2 => {
                build_term!(pool, (ite {phi_1.clone()} {t_1.clone()} {t_3.clone()}))
            },

            // ite psi true phi => psi v phi
            (ite psi true phi): (psi, _, phi) => {
                build_term!(pool, (or {psi.clone()} {phi.clone()}))
            },

            // ite psi phi false => psi ^ phi
            (ite psi phi false): (psi, phi, _) => {
                build_term!(pool, (and {psi.clone()} {phi.clone()}))
            },

            // ite psi false phi => ¬psi ^ phi
            (ite psi false phi): (psi, _, phi) => {
                build_term!(pool, (and (not {psi.clone()}) {phi.clone()}))
            },

            // ite psi phi true => ¬psi v phi
            (ite psi phi true): (psi, phi, _) => {
                build_term!(pool, (or (not {psi.clone()}) {phi.clone()}))
            },
        })
    })
}

pub fn eq_simplify(args: RuleArgs) -> RuleResult {
    generic_simplify_rule(args.conclusion, args.pool, |term, pool| {
        simplify!(term {
            // t = t => true
            (= t t): (t1, t2) if t1 == t2 => pool.bool_true(),

            // t_1 = t_2 => false, if t_1 and t_2 are different numerical constants
            (= t t): (t1, t2) if {
                let t1 = t1.as_signed_number();
                let t2 = t2.as_signed_number();
                t1.is_some() && t2.is_some() && t1 != t2
            } => pool.bool_false(),

            // ¬(t = t) => false, if t is a numerical constant
            (not (= t t)): (t1, t2) if t1 == t2 && t1.is_signed_number() => pool.bool_false(),
        })
    })
}

/// Used for both the `and_simplify` and `or_simplify` rules, depending on `rule_kind`. `rule_kind`
/// has to be either `Operator::And` or `Operator::Or`.
fn generic_and_or_simplify(
    pool: &mut TermPool,
    conclusion: &[Rc<Term>],
    rule_kind: Operator,
) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    // The "skip term" is the term that represents the empty conjunction or disjunction, and can be
    // skipped. This is `false` for conjunctions and `true` disjunctions
    let skip_term = match rule_kind {
        Operator::And => true,
        Operator::Or => false,
        _ => unreachable!(),
    };

    // The "short-circuit term" is the term that can short-circuit the conjunction or disjunction.
    // This is `true` for conjunctions and `false` disjunctions
    let short_circuit_term = !skip_term;

    let (phis, result_term) = match_term_err!((= phi psi) = &conclusion[0])?;
    let mut phis = match rule_kind {
        Operator::And => match_term_err!((and ...) = phis),
        Operator::Or => match_term_err!((or ...) = phis),
        _ => unreachable!(),
    }?
    .to_vec();
    let result_args = match result_term.as_ref() {
        Term::Op(op, args) if *op == rule_kind => args,
        _ => std::slice::from_ref(result_term),
    };

    // Sometimes, the `and_simplify` and `or_simplify` rules are used on a nested application of
    // the rule operator, where the outer operation only has one argument, e.g. `(and (and p q r)`.
    // If we encounter this, we remove the outer application
    if phis.len() == 1 {
        match phis[0].as_ref() {
            Term::Op(op, args) if *op == rule_kind => phis = args.clone(),
            _ => (),
        }
    }

    // First, we remove all "skip term"s from the arguments. If at this point we already found the
    // result, we return true. While doing this before the main loop requires an additional
    // allocation for the `phis` vector, it allows us to exit early in some cases, which overall
    // improves performance significantly. More importantly, it is necessary in some examples,
    // where not all steps of the simplification are applied
    phis.retain(|t| !t.is_bool_constant(skip_term));
    if result_args.iter().eq(&phis) {
        return Ok(());
    }

    // Then, we remove all duplicate terms. We do this in place to avoid another allocation.
    // Similarly to the step that removes the "skip term", we check if we already found the result
    // after this step. This is also necessary in some examples
    let mut seen = AHashSet::with_capacity(phis.len());
    phis.retain(|t| seen.insert(t.clone()));
    if result_args.iter().eq(&phis) {
        return Ok(());
    }

    // Finally, we check to see if the result was short-circuited
    let seen: AHashSet<(bool, &Rc<Term>)> = phis
        .iter()
        .map(|t| t.remove_all_negations_with_polarity())
        .collect();
    for term in &phis {
        // If the term is the "short-circuit term", or is the negation of a term previously
        // encountered, the result is short-circuited
        let (polarity, inner) = term.remove_all_negations_with_polarity();
        if seen.contains(&(!polarity, inner)) || term.is_bool_constant(short_circuit_term) {
            return if result_args.len() == 1 {
                assert_is_bool_constant(&result_args[0], short_circuit_term)
            } else {
                Err(CheckerError::ExpectedBoolConstant(
                    short_circuit_term,
                    result_term.clone(),
                ))
            };
        }
    }

    if phis.is_empty() {
        // If the filtered conjunction or disjunction is empty, the expected result is just the
        // "skip term", which represents an empty conjunction or disjunction
        if result_args.len() == 1 {
            assert_is_bool_constant(&result_args[0], skip_term)
        } else {
            Err(CheckerError::ExpectedBoolConstant(
                skip_term,
                result_term.clone(),
            ))
        }
    } else if result_args.iter().eq(&phis) {
        Ok(())
    } else {
        let expected = pool.add_term(Term::Op(rule_kind, phis));
        Err(EqualityError::ExpectedToBe { expected, got: result_term.clone() }.into())
    }
}

pub fn and_simplify(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    generic_and_or_simplify(pool, conclusion, Operator::And)
}

pub fn or_simplify(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    generic_and_or_simplify(pool, conclusion, Operator::Or)
}

pub fn not_simplify(args: RuleArgs) -> RuleResult {
    generic_simplify_rule(args.conclusion, args.pool, |term, pool| {
        simplify!(term {
            // ¬(¬phi) => phi
            (not (not phi)): phi => phi.clone(),

            // ¬false => true
            (not false): _ => pool.bool_true(),

            // ¬true => false
            (not true): _ => pool.bool_false(),
        })
    })
}

pub fn implies_simplify(args: RuleArgs) -> RuleResult {
    generic_simplify_rule(args.conclusion, args.pool, |term, pool| {
        simplify!(term {
            // ¬phi_1 -> ¬phi_2 => phi_2 -> phi_1
            (=> (not phi_1) (not phi_2)): (phi_1, phi_2) => {
                build_term!(pool, (=> {phi_2.clone()} {phi_1.clone()}))
            },

            // false -> phi => true
            (=> false phi): _ => pool.bool_true(),

            // phi -> true => true
            (=> phi true): _ => pool.bool_true(),

            // true -> phi => phi
            (=> true phi): (_, phi) => phi.clone(),

            // phi -> false => ¬phi
            (=> phi false): (phi, _) => build_term!(pool, (not {phi.clone()})),

            // phi -> phi => true
            (=> phi phi): (phi_1, phi_2) if phi_1 == phi_2 => pool.bool_true(),

            // ¬phi -> phi => phi
            // phi -> ¬phi => ¬phi
            (=> phi_1 phi_2): (phi_1, phi_2) if {
                phi_1.remove_negation() == Some(phi_2) || phi_2.remove_negation() == Some(phi_1)
            } => phi_2.clone(),

            // (phi_1 -> phi_2) -> phi_2 => phi_1 v phi_2
            (=> (=> phi_1 phi_2) phi_3): ((phi_1, phi_2), phi_3) if phi_2 == phi_3 => {
                build_term!(pool, (or {phi_1.clone()} {phi_2.clone()}))
            },
        })
    })
}

pub fn equiv_simplify(args: RuleArgs) -> RuleResult {
    generic_simplify_rule(args.conclusion, args.pool, |term, pool| {
        simplify!(term {
            // ¬phi_1 = ¬phi_2 => phi_1 = phi_2
            (= (not phi_1) (not phi_2)): (phi_1, phi_2) => {
                build_term!(pool, (= {phi_1.clone()} {phi_2.clone()}))
            },

            // phi = phi => true
            (= phi_1 phi_2): (phi_1, phi_2) if phi_1 == phi_2 => pool.bool_true(),

            // phi = ¬phi => false
            (= phi_1 (not phi_2)): (phi_1, phi_2) if phi_1 == phi_2 => pool.bool_false(),

            // ¬phi = phi => false
            (= (not phi_1) phi_2): (phi_1, phi_2) if phi_1 == phi_2 => pool.bool_false(),

            // true = phi => phi
            (= true phi_1): (_, phi_1) => phi_1.clone(),

            // phi = true => phi
            (= phi_1 true): (phi_1, _) => phi_1.clone(),

            // false = phi => ¬phi
            (= false phi_1): (_, phi_1) => build_term!(pool, (not {phi_1.clone()})),

            // phi = false => ¬phi
            (= phi_1 false): (phi_1, _) => build_term!(pool, (not {phi_1.clone()})),
        })
    })
}

pub fn bool_simplify(args: RuleArgs) -> RuleResult {
    generic_simplify_rule(args.conclusion, args.pool, |term, pool| {
        simplify!(term {
            // ¬(phi_1 -> phi_2) => (phi_1 ^ ¬phi_2)
            (not (=> phi_1 phi_2)): (phi_1, phi_2) => {
                build_term!(pool, (and {phi_1.clone()} (not {phi_2.clone()})))
            },

            // ¬(phi_1 v phi_2) => (¬phi_1 ^ ¬phi_2)
            (not (or phi_1 phi_2)): (phi_1, phi_2) => {
                build_term!(pool, (and (not {phi_1.clone()}) (not {phi_2.clone()})))
            },

            // ¬(phi_1 ^ phi_2) => (¬phi_1 v ¬phi_2)
            (not (and phi_1 phi_2)): (phi_1, phi_2) => {
                build_term!(pool, (or (not {phi_1.clone()}) (not {phi_2.clone()})))
            },

            // (phi_1 -> (phi_2 -> phi_3)) => ((phi_1 ^ phi_2) -> phi_3)
            (=> phi_1 (=> phi_2 phi_3)): (phi_1, (phi_2, phi_3)) => {
                build_term!(pool, (=> (and {phi_1.clone()} {phi_2.clone()}) {phi_3.clone()}))
            },

            // ((phi_1 -> phi_2) -> phi_2) => (phi_1 v phi_2)
            (=> (=> phi_1 phi_2) phi_3): ((phi_1, phi_2), phi_3) if phi_2 == phi_3 => {
                build_term!(pool, (or {phi_1.clone()} {phi_2.clone()}))
            },

            // (phi_1 ^ (phi_1 -> phi_2)) => (phi_1 ^ phi_2)
            (and phi_1 (=> phi_2 phi_3)): (phi_1, (phi_2, phi_3)) if phi_1 == phi_2 => {
                build_term!(pool, (and {phi_1.clone()} {phi_3.clone()}))
            },

            // ((phi_1 -> phi_2) ^ phi_1) => (phi_1 ^ phi_2)
            (and (=> phi_1 phi_2) phi_3): ((phi_1, phi_2), phi_3) if phi_1 == phi_3 => {
                build_term!(pool, (and {phi_1.clone()} {phi_2.clone()}))
            },
        })
    })
}

pub fn qnt_simplify(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;
    let (_, _, inner) = left.unwrap_quant_err()?;
    rassert!(
        inner.is_bool_false() || inner.is_bool_true(),
        CheckerError::ExpectedAnyBoolConstant(inner.clone())
    );
    assert_eq(right, inner)?;
    Ok(())
}

pub fn div_simplify(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;
    let (t_1, t_2) = match match_term!((div n d) = left) {
        Some(v) => Ok(v),
        None => match_term_err!((/ n d) = left),
    }?;

    if t_1 == t_2 {
        rassert!(
            right.as_signed_number_err()?.is_one(),
            CheckerError::ExpectedNumber(BigRational::one(), right.clone())
        );
        Ok(())
    } else if t_2.as_number().map_or(false, |n| n.is_one()) {
        assert_eq(right, t_1)
    } else {
        let expected = t_1.as_signed_number_err()? / t_2.as_signed_number_err()?;
        rassert!(
            right.as_fraction_err()? == expected,
            CheckerError::ExpectedNumber(expected, right.clone())
        );
        Ok(())
    }
}

/// Used for both the `sum_simplify` and `prod_simplify` rules, depending on `rule_kind`.
/// `rule_kind` has to be either `Operator::Add` or `Operator::Mult`.
fn generic_sum_prod_simplify_rule(
    pool: &mut TermPool,
    ts: &Rc<Term>,
    u: &Rc<Term>,
    rule_kind: Operator,
) -> RuleResult {
    let identity_value = match rule_kind {
        Operator::Add => BigRational::zero(),
        Operator::Mult => BigRational::one(),
        _ => unreachable!(),
    };

    // Check if the u term is valid and extract from it the leading constant and the remaining
    // arguments
    let (u_constant, u_args) = match u.as_ref() {
        Term::Op(op, args) if *op == rule_kind => {
            // We check if there are any constants in u (aside from the leading constant). If there
            // are any, we know this u term is invalid
            if args[1..].iter().any(|t| t.as_fraction().is_some()) {
                None
            } else {
                match args[0].as_fraction() {
                    // If the leading constant is the identity value, it should have been omitted
                    Some(constant) if constant == identity_value => None,
                    Some(constant) => Some((constant, &args[1..])),
                    None => Some((identity_value.clone(), args.as_slice())),
                }
            }
        }

        // If u is not an application of the operator, we consider it a product/sum of a single
        // term. That term might be a regular term or the leading constant, depending on if u
        // is a constant or not
        _ => Some(match u.as_fraction() {
            Some(u) => (u, &[] as &[_]),
            None => (identity_value.clone(), std::slice::from_ref(u)),
        }),
    }
    .ok_or_else(|| CheckerError::SumProdSimplifyInvalidConclusion(u.clone()))?;

    let ts = match rule_kind {
        Operator::Add => match_term_err!((+ ...) = ts),
        Operator::Mult => match_term_err!((* ...) = ts),
        _ => unreachable!(),
    }?;

    let mut result = Vec::with_capacity(ts.len());
    let mut constant_total = identity_value.clone();

    // First, we go through the t_i terms, adding/multiplying all the constants we find together,
    // and push the non-constant terms to the `result` vector
    for t in ts {
        match (t.as_fraction(), rule_kind) {
            (Some(r), Operator::Add) => constant_total += r,
            (Some(r), Operator::Mult) => constant_total *= r,
            (Some(_), _) => unreachable!(),
            (None, _) => {
                result.push(t);
                continue; // Since `constant_total` didn't change, we can skip the check
            }
        }
        // If the rule kind is `prod_simplify` and we find a zero, we can leave the loop early. We
        // also clear the `result` vector because we expect the u term to be just the zero constant
        if rule_kind == Operator::Mult && constant_total == BigRational::zero() {
            result.clear();
            break;
        }
    }

    // This covers a tricky edge case that happens when the only non-constant term in `ts` is also a
    // valid application of the rule operator. For example:
    //     (step t1 (cl
    //         (= (* 1 (* 2 x)) (* 2 x))
    //     ) :rule prod_simplify)
    // In this step, the term `(* 2 x)` on the right-hand side should be interpreted as an atom,
    // but since it is a valid `u` term, it is unwrapped such that `u_constant` is 2 and `u_args`
    // is `x`. To handle this, we first check if the expected result is just one term, and try to
    // interpret `u` as that term.
    if result.len() == 1 && constant_total == identity_value && u == result[0] {
        return Ok(());
    }

    // Finally, we verify that the constant and the remaining arguments are what we expect
    rassert!(u_constant == constant_total && u_args.iter().eq(result), {
        let expected = {
            let mut expected_args =
                vec![pool.add_term(Term::Terminal(Terminal::Real(constant_total)))];
            expected_args.extend(u_args.iter().cloned());
            pool.add_term(Term::Op(rule_kind, expected_args))
        };
        EqualityError::ExpectedToBe { expected, got: u.clone() }
    });
    Ok(())
}

pub fn prod_simplify(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (first, second) = match_term_err!((= first second) = &conclusion[0])?;

    // Since the equality may be flipped, we need to test both possibilities. We first test the
    // "reversed" one to make the error messages more reasonable in case both fail
    if generic_sum_prod_simplify_rule(pool, second, first, Operator::Mult).is_ok() {
        return Ok(());
    }
    generic_sum_prod_simplify_rule(pool, first, second, Operator::Mult)
}

pub fn minus_simplify(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    // Despite being separate rules in the documentation, this rule is used to do the job of both
    // the `minus_simplify` and the `unary_minus_simplify` rules
    fn try_unary_minus_simplify(t: &Rc<Term>, u: &Rc<Term>) -> bool {
        // First case of `unary_minus_simplify`
        if match_term!((-(-t)) = t).map_or(false, |t| t == u) {
            return true;
        }

        // Second case of `unary_minus_simplify`
        match (t.as_signed_number(), u.as_signed_number()) {
            (Some(t), Some(u)) if t == u => return true,
            _ => (),
        }

        false
    }

    fn check(t_1: &Rc<Term>, t_2: &Rc<Term>, u: &Rc<Term>) -> RuleResult {
        if t_1 == t_2 {
            rassert!(
                u.as_number_err()?.is_zero(),
                CheckerError::ExpectedNumber(BigRational::one(), u.clone()),
            );
            return Ok(());
        }
        match (t_1.as_signed_number(), t_2.as_signed_number()) {
            (_, Some(z)) if z.is_zero() => assert_eq(u, t_1),
            (Some(z), _) if z.is_zero() => assert_eq(match_term_err!((-t) = u)?, t_2),
            (Some(t_1), Some(t_2)) => {
                let expected = t_1 - t_2;
                rassert!(
                    u.as_signed_number_err()? == expected,
                    CheckerError::ExpectedNumber(expected, u.clone())
                );
                Ok(())
            }

            // We expect at least one of the terms to be a number
            _ => Err(CheckerError::ExpectedAnyNumber(t_2.clone())),
        }
    }

    assert_clause_len(conclusion, 1)?;
    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;

    if try_unary_minus_simplify(left, right) || try_unary_minus_simplify(right, left) {
        return Ok(());
    }

    // The equality in the conclusion may be flipped, but one of the terms in it must be of the
    // form '(- t_1 t_2)'. We first check assuming that 't' is in the right. If that fails, we
    // check the other case and return any error it finds
    if let Some((t_1, t_2)) = match_term!((- t_1 t_2) = right) {
        if check(t_1, t_2, left).is_ok() {
            return Ok(());
        }
    }
    let (t_1, t_2) = match_term_err!((- t_1 t_2) = left)?;
    check(t_1, t_2, right)
}

pub fn sum_simplify(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (first, second) = match_term_err!((= first second) = &conclusion[0])?;

    // Since the equality may be flipped, we need to test both possibilities. We first test the
    // "reversed" one to make the error messages more reasonable in case both fail
    if generic_sum_prod_simplify_rule(pool, second, first, Operator::Add).is_ok() {
        return Ok(());
    }
    generic_sum_prod_simplify_rule(pool, first, second, Operator::Add)
}

pub fn comp_simplify(args: RuleArgs) -> RuleResult {
    generic_simplify_rule(args.conclusion, args.pool, |term, pool| {
        simplify!(term {
            (< t_1 t_2): (t_1, t_2) => {
                if let (Some(t_1), Some(t_2)) =
                    (t_1.as_signed_number(), t_2.as_signed_number())
                {
                    // t_1 < t_2 => phi, where t_1 and t_2 are numerical constants
                    pool.bool_constant(t_1 < t_2)
                } else if t_1 == t_2 {
                    // t < t => false
                    pool.bool_false()
                } else {
                    // t_1 < t_2 => ¬(t_2 <= t_1)
                    build_term!(pool, (not (<= {t_2.clone()} {t_1.clone()})))
                }
            },
            (<= t_1 t_2): (t_1, t_2) => {
                if let (Some(t_1), Some(t_2)) =
                    (t_1.as_signed_number(), t_2.as_signed_number())
                {
                    // t_1 <= t_2 => phi, where t_1 and t_2 are numerical constants
                    pool.bool_constant(t_1 <= t_2)
                } else if t_1 == t_2 {
                    // t <= t => true
                    pool.bool_true()
                } else {
                    return None
                }
            },

            // t_1 >= t_2 => t_2 <= t_1
            (>= t_1 t_2): (t_1, t_2) => build_term!(pool, (<= {t_2.clone()} {t_1.clone()})),

            // t_1 > t_2 => ¬(t_1 <= t_2)
            (> t_1 t_2): (t_1, t_2) => build_term!(pool, (not (<= {t_1.clone()} {t_2.clone()}))),
        })
    })
}

struct AcSimp<'a> {
    pool: &'a mut TermPool,
    equality_cache: AHashSet<(Rc<Term>, Rc<Term>)>,
    flattening_cache: AHashMap<Rc<Term>, Rc<Term>>,
}

impl<'a> AcSimp<'a> {
    fn new(pool: &'a mut TermPool) -> Self {
        Self {
            pool,
            equality_cache: AHashSet::new(),
            flattening_cache: AHashMap::new(),
        }
    }

    fn flatten_operation(&mut self, term: &Rc<Term>) -> Rc<Term> {
        if let Some(t) = self.flattening_cache.get(term) {
            return t.clone();
        }
        let result = match term.as_ref() {
            Term::Op(op @ (Operator::And | Operator::Or), args) => {
                let args: Vec<_> = args
                    .iter()
                    .flat_map(|term| {
                        let term = self.flatten_operation(term);
                        match term.as_ref() {
                            Term::Op(inner_op, inner_args) if inner_op == op => inner_args.clone(),
                            _ => vec![term.clone()],
                        }
                    })
                    .dedup()
                    .collect();
                if args.len() == 1 {
                    return args[0].clone();
                } else {
                    Term::Op(*op, args)
                }
            }
            Term::Op(op, args) => {
                let args = args
                    .iter()
                    .map(|term| self.flatten_operation(term))
                    .collect();
                Term::Op(*op, args)
            }
            Term::App(func, args) => {
                let args = args
                    .iter()
                    .map(|term| self.flatten_operation(term))
                    .collect();
                Term::App(func.clone(), args)
            }
            Term::Quant(q, bindings, inner) => {
                Term::Quant(*q, bindings.clone(), self.flatten_operation(inner))
            }
            Term::Let(binding, inner) => Term::Let(binding.clone(), self.flatten_operation(inner)),
            _ => return term.clone(),
        };
        let result = self.pool.add_term(result);
        self.flattening_cache.insert(term.clone(), result.clone());
        result
    }

    fn eq_args(&mut self, a: &[Rc<Term>], b: &[Rc<Term>]) -> bool {
        a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| self.eq(a, b))
    }

    fn eq(&mut self, a: &Rc<Term>, b: &Rc<Term>) -> bool {
        if a == b || self.equality_cache.contains(&(a.clone(), b.clone())) {
            return true;
        }

        let result = match (a.as_ref(), b.as_ref()) {
            (Term::App(f_a, args_a), Term::App(f_b, args_b)) => {
                self.eq(f_a, f_b) && self.eq_args(args_a, args_b)
            }
            (Term::Op(Operator::And | Operator::Or, _), _)
                if {
                    let a_flattened = self.flatten_operation(a);
                    &a_flattened == b
                } =>
            {
                true
            }
            (Term::Op(op_a, args_a), Term::Op(op_b, args_b)) => {
                op_a == op_b && self.eq_args(args_a, args_b)
            }
            (Term::Quant(q_a, binds_a, a), Term::Quant(q_b, binds_b, b)) => {
                q_a == q_b && binds_a == binds_b && self.eq(a, b)
            }
            (Term::Let(binds_a, a), Term::Let(binds_b, b)) => binds_a == binds_b && self.eq(a, b),
            _ => false,
        };
        if result {
            self.equality_cache.insert((a.clone(), b.clone()));
        }
        result
    }
}

pub fn ac_simp(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (original, flattened) = match_term_err!((= psi phis) = &conclusion[0])?;
    rassert!(
        AcSimp::new(pool).eq(original, flattened),
        CheckerError::AcSimpFailed(original.clone(), flattened.clone())
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn ite_simplify() {
        test_cases! {
            definitions = "
                (declare-fun a () Bool)
                (declare-fun b () Bool)
                (declare-fun c () Bool)
                (declare-fun d () Bool)
            ",
            "Transformation #1" {
                "(step t1 (cl (= (ite true a b) a)) :rule ite_simplify)": true,
            }
            "Transformation #2" {
                "(step t1 (cl (= (ite false a b) b)) :rule ite_simplify)": true,
            }
            "Transformation #3" {
                "(step t1 (cl (= (ite a b b) b)) :rule ite_simplify)": true,
            }
            "Transformation #4" {
                "(step t1 (cl (= (ite (not a) b c) (ite a c b))) :rule ite_simplify)": true,
            }
            "Transformation #5" {
                "(step t1 (cl (= (ite a (ite a b c) d) (ite a b d))) :rule ite_simplify)": true,
            }
            "Transformation #6" {
                "(step t1 (cl (= (ite a b (ite a c d)) (ite a b d))) :rule ite_simplify)": true,
            }
            "Transformation #7" {
                "(step t1 (cl (= (ite a true false) a)) :rule ite_simplify)": true,
            }
            "Transformation #8" {
                "(step t1 (cl (= (ite a false true) (not a))) :rule ite_simplify)": true,
            }
            "Transformation #9" {
                "(step t1 (cl (= (ite a true b) (or a b))) :rule ite_simplify)": true,
            }
            "Transformation #10" {
                "(step t1 (cl (= (ite a b false) (and a b))) :rule ite_simplify)": true,
            }
            "Transformation #11" {
                "(step t1 (cl (= (ite a false b) (and (not a) b))) :rule ite_simplify)": true,
            }
            "Transformation #12" {
                "(step t1 (cl (= (ite a b true) (or (not a) b))) :rule ite_simplify)": true,
            }
            "Multiple transformations" {
                "(step t1 (cl (= (ite (not a) false true) (not (not a)))) :rule ite_simplify)": true,
                "(step t1 (cl (= (ite a (ite a d c) d) d)) :rule ite_simplify)": true,
                "(step t1 (cl (= (ite a (ite true b c) (ite true b c)) b))
                    :rule ite_simplify)": true,
            }
        }
    }

    #[test]
    fn eq_simplify() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun a () Int)
                (declare-fun b () Int)
            ",
            "Transformation #1" {
                "(step t1 (cl (= (= a a) true)) :rule eq_simplify)": true,
                "(step t1 (cl (= (= (and p q) (and p q)) true)) :rule eq_simplify)": true,
                "(step t1 (cl (= (= a b) true)) :rule eq_simplify)": false,
            }
            "Transformation #2" {
                "(step t1 (cl (= (= 0 1) false)) :rule eq_simplify)": true,
                "(step t1 (cl (= (= 0.0 0.01) false)) :rule eq_simplify)": true,
                "(step t1 (cl (= (= 1 (- 1)) false)) :rule eq_simplify)": true,
                "(step t1 (cl (= (= 0 1) true)) :rule eq_simplify)": false,
                "(step t1 (cl (= (= 0.0 0.0) false)) :rule eq_simplify)": false,
            }
            "Transformation #3" {
                "(step t1 (cl (= (not (= 0.0 0.0)) false)) :rule eq_simplify)": true,
                "(step t1 (cl (= (not (= (- 1) (- 1))) false)) :rule eq_simplify)": true,
                "(step t1 (cl (= (not (= 0 0)) true)) :rule eq_simplify)": false,
                "(step t1 (cl (= (not (= 0 1)) false)) :rule eq_simplify)": false,
                "(step t1 (cl (= (not (= a a)) false)) :rule eq_simplify)": false,
            }
        }
    }

    #[test]
    fn and_simplify() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
            ",
            "Transformation #1" {
                "(step t1 (cl (= (and true true true) true)) :rule and_simplify)": true,
                "(step t1 (cl (= (and true true true) (and true))) :rule and_simplify)": true,
                "(step t1 (cl (= (and true) true)) :rule and_simplify)": true,

                "(step t1 (cl (= (and true p true) true)) :rule and_simplify)": false,
                "(step t1 (cl (= (and true true) false)) :rule and_simplify)": false,
            }
            "Transformation #2" {
                "(step t1 (cl (= (and p true q) (and p q))) :rule and_simplify)": true,
                "(step t1 (cl (= (and p true q r true true) (and p q r))) :rule and_simplify)": true,
                "(step t1 (cl (= (and true q true true) q)) :rule and_simplify)": true,
                "(step t1 (cl (= (and true q true true) (and q))) :rule and_simplify)": true,

                "(step t1 (cl (= (and p true q true) (and p true q))) :rule and_simplify)": false,
                "(step t1 (cl (= (and p true q r true true) (and p r))) :rule and_simplify)": false,
            }
            "Transformation #3" {
                "(step t1 (cl (= (and p p q q q r) (and p q r))) :rule and_simplify)": true,
                "(step t1 (cl (= (and p p) (and p))) :rule and_simplify)": true,
                "(step t1 (cl (= (and p p) p)) :rule and_simplify)": true,

                "(step t1 (cl (= (and p p q q q r) (and p q q r))) :rule and_simplify)": false,
                "(step t1 (cl (= (and p p q q q) (and p q r))) :rule and_simplify)": false,
            }
            "Transformation #4" {
                "(step t1 (cl (= (and p q false r) false)) :rule and_simplify)": true,
                "(step t1 (cl (= (and p q false r) (and false))) :rule and_simplify)": true,
                "(step t1 (cl (= (and false true) false)) :rule and_simplify)": true,

                "(step t1 (cl (= (and p q false r) (and p q r))) :rule and_simplify)": false,
                "(step t1 (cl (= (and p q false r) true)) :rule and_simplify)": false,
            }
            "Transformation #5" {
                "(step t1 (cl (= (and p q (not q) r) false)) :rule and_simplify)": true,
                "(step t1 (cl (= (and p q (not q) r) (and false))) :rule and_simplify)": true,
                "(step t1 (cl (= (and p (not (not q)) (not q) r) false)) :rule and_simplify)": true,
                "(step t1 (cl (= (and p (not (not (not p))) (not p)) false))
                    :rule and_simplify)": true,

                "(step t1 (cl (= (and p (not (not p)) (not q) r) false)) :rule and_simplify)": false,
                "(step t1 (cl (= (and q (not r)) false)) :rule and_simplify)": false,
                "(step t1 (cl (= (and r (not r)) true)) :rule and_simplify)": false,
            }
            "Multiple transformations" {
                "(step t1 (cl (= (and p p true q q true q r) (and p q r)))
                    :rule and_simplify)": true,
                "(step t1 (cl (= (and p p (not p) q q true q r) false)) :rule and_simplify)": true,
                "(step t1 (cl (= (and p false p (not p) q true q r) false))
                    :rule and_simplify)": true,
            }
            "Nested \"and\" term" {
                "(step t1 (cl (= (and (and p p true q q true q r)) (and p q r)))
                    :rule and_simplify)": true,
            }
        }
    }

    #[test]
    fn or_simplify() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
            ",
            "Transformation #1" {
                "(step t1 (cl (= (or false false false) false)) :rule or_simplify)": true,
                "(step t1 (cl (= (or false false false) (or false))) :rule or_simplify)": true,
                "(step t1 (cl (= (or false) false)) :rule or_simplify)": true,

                "(step t1 (cl (= (or false p false) false)) :rule or_simplify)": false,
                "(step t1 (cl (= (or false false) true)) :rule or_simplify)": false,
            }
            "Transformation #2" {
                "(step t1 (cl (= (or p false q) (or p q))) :rule or_simplify)": true,
                "(step t1 (cl (= (or p false q r false false) (or p q r))) :rule or_simplify)": true,
                "(step t1 (cl (= (or false q false false) q)) :rule or_simplify)": true,
                "(step t1 (cl (= (or false q false false) (or q))) :rule or_simplify)": true,

                "(step t1 (cl (= (or p false q false) (or p false q))) :rule or_simplify)": false,
                "(step t1 (cl (= (or p false q r false false) (or p r))) :rule or_simplify)": false,
            }
            "Transformation #3" {
                "(step t1 (cl (= (or p p q q q r) (or p q r))) :rule or_simplify)": true,
                "(step t1 (cl (= (or p p) (or p))) :rule or_simplify)": true,
                "(step t1 (cl (= (or p p) p)) :rule or_simplify)": true,

                "(step t1 (cl (= (or p p q q q r) (or p q q r))) :rule or_simplify)": false,
                "(step t1 (cl (= (or p p q q q) (or p q r))) :rule or_simplify)": false,
            }
            "Transformation #4" {
                "(step t1 (cl (= (or p q true r) true)) :rule or_simplify)": true,
                "(step t1 (cl (= (or p q true r) (or true))) :rule or_simplify)": true,
                "(step t1 (cl (= (or true false) true)) :rule or_simplify)": true,

                "(step t1 (cl (= (or p q true r) (or p q r))) :rule or_simplify)": false,
                "(step t1 (cl (= (or p q true r) false)) :rule or_simplify)": false,
            }
            "Transformation #5" {
                "(step t1 (cl (= (or p q (not q) r) true)) :rule or_simplify)": true,
                "(step t1 (cl (= (or p q (not q) r) (or true))) :rule or_simplify)": true,
                "(step t1 (cl (= (or p (not (not q)) (not q) r) true)) :rule or_simplify)": true,
                "(step t1 (cl (= (or p (not (not (not p))) (not p)) true)) :rule or_simplify)": true,

                "(step t1 (cl (= (or p (not (not p)) (not q) r) true)) :rule or_simplify)": false,
                "(step t1 (cl (= (or q (not r)) true)) :rule or_simplify)": false,
                "(step t1 (cl (= (or r (not r)) false)) :rule or_simplify)": false,
            }
            "Multiple transformations" {
                "(step t1 (cl (= (or p p false q q false q r) (or p q r))) :rule or_simplify)": true,
                "(step t1 (cl (= (or p p (not p) q q false q r) true)) :rule or_simplify)": true,
                "(step t1 (cl (= (or p true p (not p) q false q r) true)) :rule or_simplify)": true,
            }
            "Nested \"or\" term" {
                "(step t1 (cl (= (or (or p p false q q false q r)) (or p q r)))
                    :rule or_simplify)": true,
            }
        }
    }

    #[test]
    fn not_simplify() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
            ",
            "Transformation #1" {
                "(step t1 (cl (= (not (not p)) p)) :rule not_simplify)": true,
                "(step t1 (cl (= (not (not (not (not p)))) p)) :rule not_simplify)": true,
                "(step t1 (cl (= (not (not (not (and p q)))) (and p q))) :rule not_simplify)": false,
            }
            "Transformation #2" {
                "(step t1 (cl (= (not false) true)) :rule not_simplify)": true,
                "(step t1 (cl (= (not false) false)) :rule not_simplify)": false,
            }
            "Transformation #3" {
                "(step t1 (cl (= (not true) false)) :rule not_simplify)": true,
                "(step t1 (cl (= (not true) true)) :rule not_simplify)": false,
            }
            "Multiple transformations" {
                "(step t1 (cl (= (not (not (not false))) true)) :rule not_simplify)": true,
                "(step t1 (cl (= (not (not (not true))) false)) :rule not_simplify)": true,
            }
        }
    }

    #[test]
    fn implies_simplify() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
            ",
            "Transformation #1" {
                "(step t1 (cl (= (=> (not p) (not q)) (=> q p))) :rule implies_simplify)": true,
                "(step t1 (cl (= (=> (not (not p)) (not (not q))) (=> p q)))
                    :rule implies_simplify)": true,
                "(step t1 (cl (= (=> (not (not p)) (not (not q))) (=> (not q) (not p))))
                    :rule implies_simplify)": true,
            }
            "Transformation #2" {
                "(step t1 (cl (= (=> false p) true)) :rule implies_simplify)": true,
                "(step t1 (cl (= (=> false false) true)) :rule implies_simplify)": true,
            }
            "Transformation #3" {
                "(step t1 (cl (= (=> p true) true)) :rule implies_simplify)": true,
                "(step t1 (cl (= (=> false true) true)) :rule implies_simplify)": true,
            }
            "Transformation #4" {
                "(step t1 (cl (= (=> true p) p)) :rule implies_simplify)": true,
                "(step t1 (cl (= (=> true false) false)) :rule implies_simplify)": true,
            }
            "Transformation #5" {
                "(step t1 (cl (= (=> p false) (not p))) :rule implies_simplify)": true,
                "(step t1 (cl (= (=> false false) (not false))) :rule implies_simplify)": false,
                "(step t1 (cl (= (=> true false) (not true))) :rule implies_simplify)": false,
            }
            "Transformation #6" {
                "(step t1 (cl (= (=> p p) true)) :rule implies_simplify)": true,
            }
            "Transformation #7" {
                "(step t1 (cl (= (=> (not p) p) p)) :rule implies_simplify)": true,
                "(step t1 (cl (= (=> p (not p)) (not p))) :rule implies_simplify)": true,
            }
            "Transformation #8" {
                "(step t1 (cl (= (=> (=> p q) q) (or p q))) :rule implies_simplify)": true,
                "(step t1 (cl (= (=> (=> p q) q) (or q p))) :rule implies_simplify)": false,
                "(step t1 (cl (= (=> (=> q p) q) (or p q))) :rule implies_simplify)": false,
            }
            "Multiple transformations" {
                "(step t1 (cl (= (=> (not p) (not true)) p)) :rule implies_simplify)": true,
                "(step t1 (cl (= (=> (not (not p)) (not p)) (not p))) :rule implies_simplify)": true,
                "(step t1 (cl (= (=> (not q) (not (=> p q))) (or p q)))
                    :rule implies_simplify)": true,
            }
        }
    }

    #[test]
    fn equiv_simplify() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
            ",
            "Transformation #1" {
                "(step t1 (cl (= (= (not p) (not q)) (= p q))) :rule equiv_simplify)": true,
                "(step t1 (cl (= (= (not (not p)) (not q)) (= (not p) q)))
                    :rule equiv_simplify)": true,
            }
            "Transformation #2" {
                "(step t1 (cl (= (= p p) true)) :rule equiv_simplify)": true,
                "(step t1 (cl (= (= (and p q) (and p q)) true)) :rule equiv_simplify)": true,
            }
            "Transformation #3" {
                "(step t1 (cl (= (= p (not p)) false)) :rule equiv_simplify)": true,
            }
            "Transformation #4" {
                "(step t1 (cl (= (= (not p) p) false)) :rule equiv_simplify)": true,
            }
            "Transformation #5" {
                "(step t1 (cl (= (= true p) p)) :rule equiv_simplify)": true,
                "(step t1 (cl (= (= true (and q p)) (and q p))) :rule equiv_simplify)": true,
            }
            "Transformation #6" {
                "(step t1 (cl (= (= p true) p)) :rule equiv_simplify)": true,
                "(step t1 (cl (= (= (and q p) true) (and q p))) :rule equiv_simplify)": true,
            }
            "Transformation #7" {
                "(step t1 (cl (= (= false p) (not p))) :rule equiv_simplify)": true,
                "(step t1 (cl (= (= false (and q p)) (not (and q p)))) :rule equiv_simplify)": true,
            }
            "Transformation #8" {
                "(step t1 (cl (= (= p false) (not p))) :rule equiv_simplify)": true,
                "(step t1 (cl (= (= (and q p) false) (not (and q p)))) :rule equiv_simplify)": true,
            }
            "Multiple transformations" {
                "(step t1 (cl (= (= (not (not p)) (not p)) false)) :rule equiv_simplify)": true,
                "(step t1 (cl (= (= (not (not false)) (not (not p))) (not p)))
                    :rule equiv_simplify)": true,
            }
        }
    }

    #[test]
    fn bool_simplify() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
            ",
            "Transformation #1" {
                "(step t1 (cl (=
                    (not (=> p q)) (and p (not q))
                )) :rule bool_simplify)": true,

                "(step t1 (cl (=
                    (not (=> p q)) (and (not q) p)
                )) :rule bool_simplify)": false,

                "(step t1 (cl (=
                    (not (=> p (not q))) (and p q)
                )) :rule bool_simplify)": false,
            }
            "Transformation #2" {
                "(step t1 (cl (=
                    (not (or p q)) (and (not p) (not q))
                )) :rule bool_simplify)": true,

                "(step t1 (cl (=
                    (not (or (not p) (not q))) (and p q)
                )) :rule bool_simplify)": false,
            }
            "Transformation #3" {
                "(step t1 (cl (=
                    (not (and p q)) (or (not p) (not q))
                )) :rule bool_simplify)": true,

                "(step t1 (cl (=
                    (not (and (not p) (not q))) (or p q)
                )) :rule bool_simplify)": false,
            }
            "Transformation #4" {
                "(step t1 (cl (=
                    (=> p (=> q r)) (=> (and p q) r)
                )) :rule bool_simplify)": true,

                "(step t1 (cl (=
                    (=> p (=> q r)) (=> (and q p) r)
                )) :rule bool_simplify)": false,
            }
            "Transformation #5" {
                "(step t1 (cl (=
                    (=> (=> p q) q) (or p q)
                )) :rule bool_simplify)": true,

                "(step t1 (cl (=
                    (=> (=> p q) r) (or p q)
                )) :rule bool_simplify)": false,
            }
            "Transformation #6" {
                "(step t1 (cl (=
                    (and p (=> p q)) (and p q)
                )) :rule bool_simplify)": true,

                "(step t1 (cl (=
                    (and p (=> r q)) (and p q)
                )) :rule bool_simplify)": false,
            }
            "Transformation #7" {
                "(step t1 (cl (=
                    (and (=> p q) p) (and p q)
                )) :rule bool_simplify)": true,

                "(step t1 (cl (=
                    (and (=> p q) r) (and p q)
                )) :rule bool_simplify)": false,
            }
            // TODO: Add tests that combine more than one transformation
        }
    }

    #[test]
    fn qnt_simplify() {
        test_cases! {
            definitions = "",
            "Simple working examples" {
                "(step t1 (cl (= (forall ((x Int)) false) false)) :rule qnt_simplify)": true,
                "(step t1 (cl (= (forall ((x Int) (p Bool)) true) true)) :rule qnt_simplify)": true,
            }
            "Quantifier is not \"forall\"" {
                "(step t1 (cl (= (exists ((x Int)) false) false)) :rule qnt_simplify)": true,
            }
            "Inner term is not boolean constant" {
                "(step t1 (cl (= (forall ((x Int)) (not false)) true)) :rule qnt_simplify)": false,
            }
            "Left and right terms don't match" {
                "(step t1 (cl (= (forall ((x Int)) false) true)) :rule qnt_simplify)": false,
            }
        }
    }

    #[test]
    fn div_simplify() {
        test_cases! {
            definitions = "
                (declare-fun n () Int)
                (declare-fun x () Real)
            ",
            "Transformation #1" {
                "(step t1 (cl (= (div 1 1) 1)) :rule div_simplify)": true,
                "(step t1 (cl (= (div n n) 1)) :rule div_simplify)": true,
                "(step t1 (cl (= (/ x x) 1.0)) :rule div_simplify)": true,
                "(step t1 (cl (= (/ x x) (/ x x))) :rule div_simplify)": false,
            }
            "Transformation #2" {
                "(step t1 (cl (= (div 2 1) 2)) :rule div_simplify)": true,
                "(step t1 (cl (= (div n 1) n)) :rule div_simplify)": true,
                "(step t1 (cl (= (/ x 1.0) x)) :rule div_simplify)": true,
            }
            "Transformation #3" {
                "(step t1 (cl (= (div 4 2) 2)) :rule div_simplify)": true,
                "(step t1 (cl (= (div 27 9) 3)) :rule div_simplify)": true,
                "(step t1 (cl (= (/ 1.0 2.0) 0.5)) :rule div_simplify)": true,
                "(step t1 (cl (= (/ 2.0 20.0) (/ 1.0 10.0))) :rule div_simplify)": true,
            }
        }
    }

    #[test]
    fn prod_simplify() {
        test_cases! {
            definitions = "
                (declare-fun i () Int)
                (declare-fun j () Int)
                (declare-fun k () Int)
                (declare-fun x () Real)
                (declare-fun y () Real)
                (declare-fun z () Real)
            ",
            "Transformation #1" {
                "(step t1 (cl (= (* 2 3 5 7) 210)) :rule prod_simplify)": true,
                "(step t1 (cl (= 0.555 (* 1.5 3.7 0.1))) :rule prod_simplify)": true,
                "(step t1 (cl (= (* 1 1 1) 1)) :rule prod_simplify)": true,

                "(step t1 (cl (= (* 1 2 4) 6)) :rule prod_simplify)": false,
                "(step t1 (cl (= (* 1.0 2.0 1.0) 4.0)) :rule prod_simplify)": false,
            }
            "Transformation #2" {
                "(step t1 (cl (= (* 2 3 0 7) 0)) :rule prod_simplify)": true,
                "(step t1 (cl (= (* 1.5 3.7 0.0) 0.0)) :rule prod_simplify)": true,
                "(step t1 (cl (= 0 (* i 2 k 3 0 j))) :rule prod_simplify)": true,
                "(step t1 (cl (= (* i j 0 k) 0)) :rule prod_simplify)": true,
                "(step t1 (cl (= (* x y 1.0 2.0 z 0.0 z) 0.0)) :rule prod_simplify)": true,

                "(step t1 (cl (= (* 2 4 0 3) 24)) :rule prod_simplify)": false,
                "(step t1 (cl (= (* 1 1 2 3) 0)) :rule prod_simplify)": false,
                "(step t1 (cl (= (* i j 0 k) (* i j k))) :rule prod_simplify)": false,
            }
            "Transformation #3" {
                "(step t1 (cl (= (* 30 i k j) (* i 2 k 3 5 j))) :rule prod_simplify)": true,
                "(step t1 (cl (= (* i k 6 j) (* 6 i k j))) :rule prod_simplify)": true,
                "(step t1 (cl (= (* 6.0 x y z z) (* x y 1.0 2.0 z 3.0 z)))
                    :rule prod_simplify)": true,
                "(step t1 (cl (= (* x y 2.0 z z) (* 2.0 x y z z))) :rule prod_simplify)": true,

                "(step t1 (cl (= (* i 2 k 3 5 j) (* 60 i k j))) :rule prod_simplify)": false,
                "(step t1 (cl (= (* i k 6 j) (* i k 6 j))) :rule prod_simplify)": false,
                "(step t1 (cl (= (* x y 1.0 2.0 z 3.0 z) (* 4.0 x y z z)))
                    :rule prod_simplify)": false,
                "(step t1 (cl (= (* x y 1.0 2.0 z 3.0 z) (* x y z z))) :rule prod_simplify)": false,
            }
            "Transformation #4" {
                "(step t1 (cl (= (* i k 1 j) (* i k j))) :rule prod_simplify)": true,
                "(step t1 (cl (= (* i 1 1 k 1 j) (* i k j))) :rule prod_simplify)": true,
                "(step t1 (cl (= (* x y z z) (* x y 1.0 z z))) :rule prod_simplify)": true,
                "(step t1 (cl (= (* x y 5.0 1.0 z 0.2 z) (* x y z z))) :rule prod_simplify)": true,

                "(step t1 (cl (= (* i k 1 j) (* 1 i k j))) :rule prod_simplify)": false,
                "(step t1 (cl (= (* x y 5.0 1.0 z 0.2 z) (* 1.0 x y z z)))
                    :rule prod_simplify)": false,
            }
        }
    }

    #[test]
    fn minus_simplify() {
        test_cases! {
            definitions = "
                (declare-fun x () Real)
                (declare-fun a () Int)
                (declare-fun b () Int)
            ",
            "Transformation #1" {
                "(step t1 (cl (= (- x x) 0.0)) :rule minus_simplify)": true,
                "(step t1 (cl (= (- (+ a b) (+ a b)) 0)) :rule minus_simplify)": true,
                "(step t1 (cl (= 0 (- a a))) :rule minus_simplify)": true,
                "(step t1 (cl (= 0 (- a b))) :rule minus_simplify)": false,
            }
            "Transformation #2" {
                "(step t1 (cl (= (- 4.5 2.0) 2.5)) :rule minus_simplify)": true,
                "(step t1 (cl (= (- 5 7) (- 2))) :rule minus_simplify)": true,
                "(step t1 (cl (= 4 (- 2 3))) :rule minus_simplify)": false,
            }
            "Transformation #3" {
                "(step t1 (cl (= (- x 0.0) x)) :rule minus_simplify)": true,
                "(step t1 (cl (= (- a 0) a)) :rule minus_simplify)": true,
                "(step t1 (cl (= (- 0.0 x) x)) :rule minus_simplify)": false,
            }
            "Transformation #4" {
                "(step t1 (cl (= (- 0.0 x) (- x))) :rule minus_simplify)": true,
                "(step t1 (cl (= (- 0 a) (- a))) :rule minus_simplify)": true,
                "(step t1 (cl (= (- a) (- 0 a))) :rule minus_simplify)": true,
                "(step t1 (cl (= (- a) (- a 0))) :rule minus_simplify)": false,
            }
            "Transformation #1 from \"unary_minus_simplify\"" {
                "(step t1 (cl (= (- (- x)) x)) :rule minus_simplify)": true,
                "(step t1 (cl (= x (- (- x)))) :rule minus_simplify)": true,
                "(step t1 (cl (= (- (- (+ a b))) (+ a b))) :rule minus_simplify)": true,
            }
            "Transformation #2 from \"unary_minus_simplify\"" {
                "(step t1 (cl (= (- 5.0) (- 5.0))) :rule minus_simplify)": true,
                "(step t1 (cl (= (- 0) 0)) :rule minus_simplify)": true,
                "(step t1 (cl (= 0.0 (- 0.0))) :rule minus_simplify)": true,
            }
        }
    }

    #[test]
    fn sum_simplify() {
        test_cases! {
            definitions = "
                (declare-fun i () Int)
                (declare-fun j () Int)
                (declare-fun k () Int)
                (declare-fun x () Real)
                (declare-fun y () Real)
                (declare-fun z () Real)
            ",
            "Transformation #1" {
                "(step t1 (cl (= (+ 1 2 3 4) 10)) :rule sum_simplify)": true,
                "(step t1 (cl (= 5.5 (+ 1.5 3.5 0.5))) :rule sum_simplify)": true,
                "(step t1 (cl (= (+ 0 0 0) 0)) :rule sum_simplify)": true,

                "(step t1 (cl (= (+ 1 2 4) 6)) :rule sum_simplify)": false,
                "(step t1 (cl (= (+ 1.0 2.0 1.0) 2.0)) :rule sum_simplify)": false,
            }
            "Transformation #2" {
                "(step t1 (cl (= (+ 10 i k j) (+ i 2 k 3 5 j))) :rule sum_simplify)": true,
                "(step t1 (cl (= (+ i k 6 j) (+ 6 i k j))) :rule sum_simplify)": true,
                "(step t1 (cl (= (+ 6.0 x y z z) (+ x y 1.0 2.0 z 3.0 z)))
                    :rule sum_simplify)": true,
                "(step t1 (cl (= (+ x y 2.0 z z) (+ 2.0 x y z z))) :rule sum_simplify)": true,

                "(step t1 (cl (= (+ i 2 k 3 5 j) (+ 20 i k j))) :rule sum_simplify)": false,
                "(step t1 (cl (= (+ i k 6 j) (+ i k 6 j))) :rule sum_simplify)": false,
                "(step t1 (cl (= (+ x y 1.0 2.0 z 3.0 z) (+ 4.0 x y z z)))
                    :rule sum_simplify)": false,
                "(step t1 (cl (= (+ x y 1.0 2.0 z 3.0 z) (+ x y z z))) :rule sum_simplify)": false,
            }
            "Transformation #3" {
                "(step t1 (cl (= (+ i k 0 j) (+ i k j))) :rule sum_simplify)": true,
                "(step t1 (cl (= (+ i 0 0 k 0 j) (+ i k j))) :rule sum_simplify)": true,
                "(step t1 (cl (= (+ x y z z) (+ x y 0.0 z z))) :rule sum_simplify)": true,
                "(step t1 (cl (= (+ x y 0.0 0.0 z z) (+ x y z z))) :rule sum_simplify)": true,

                "(step t1 (cl (= (+ i k 0 j) (+ 0 i k j))) :rule sum_simplify)": false,
                "(step t1 (cl (= (+ x y 0.0 0.0 z z) (+ 0.0 x y z z))) :rule sum_simplify)": false,
            }
        }
    }

    #[test]
    fn comp_simplify() {
        test_cases! {
            definitions = "
                (declare-fun a () Int)
                (declare-fun b () Int)
            ",
            "Transformation #1" {
                "(step t1 (cl (= (< 1 2) true)) :rule comp_simplify)": true,
                "(step t1 (cl (= (< 1.0 1.0) false)) :rule comp_simplify)": true,
                "(step t1 (cl (= (< 0.0 (- 1.0)) true)) :rule comp_simplify)": false,
            }
            "Transformation #2" {
                "(step t1 (cl (= (< a a) false)) :rule comp_simplify)": true,
                "(step t1 (cl (= (< (+ 1 2) (+ 1 2)) true)) :rule comp_simplify)": false,
            }
            "Transformation #3" {
                "(step t1 (cl (= (<= 1 2) true)) :rule comp_simplify)": true,
                "(step t1 (cl (= (<= 1.0 1.0) true)) :rule comp_simplify)": true,
                "(step t1 (cl (= (<= 0.0 (- 1.0)) true)) :rule comp_simplify)": false,
            }
            "Transformation #4" {
                "(step t1 (cl (= (<= a a) true)) :rule comp_simplify)": true,
                "(step t1 (cl (= (<= (+ 1 2) (+ 1 2)) false)) :rule comp_simplify)": false,
            }
            "Transformation #5" {
                "(step t1 (cl (= (>= a b) (<= b a))) :rule comp_simplify)": true,
                "(step t1 (cl (= (>= 1 a) (<= 1 a))) :rule comp_simplify)": false,
            }
            "Transformation #6" {
                "(step t1 (cl (= (< a b) (not (<= b a)))) :rule comp_simplify)": true,
                "(step t1 (cl (= (< a b) (> b a))) :rule comp_simplify)": false,
            }
            "Transformation #7" {
                "(step t1 (cl (= (> a b) (not (<= a b)))) :rule comp_simplify)": true,
                "(step t1 (cl (= (> a b) (not (>= b a)))) :rule comp_simplify)": false,
                "(step t1 (cl (= (> a b) (< b a))) :rule comp_simplify)": false,
            }
            "Multiple transformations" {
                "(step t1 (cl (= (>= a a) true)) :rule comp_simplify)": true,
                "(step t1 (cl (= (>= 5.0 8.0) false)) :rule comp_simplify)": true,
            }
        }
    }

    #[test]
    fn ac_simp() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (= (and (and p q) (and r s)) (and p q r s))) :rule ac_simp)": true,
                "(step t1 (cl (= (or (or (or p q) r) s) (or p q r s))) :rule ac_simp)": true,
            }
            "Mixed operators" {
                "(step t1 (cl (= (or (and (and p q) r) s (or p q)) (or (and p q r) s p q)))
                    :rule ac_simp)": true,

                "(step t1 (cl (= (or (= (and (and p q) r) s) (or p q)) (or (= (and p q r) s) p q)))
                    :rule ac_simp)": true,

                "(step t1 (cl (= (or (= (and (and p q) r) s) (or p q))
                    (or (= (and (and p q) r) s) p q))) :rule ac_simp)": false,

                "(step t1 (cl (= (xor (xor (xor p q) r) s) (xor p q r s))) :rule ac_simp)": false,

                "(step t1 (cl (= (forall ((p Bool) (q Bool)) (and (and p q) p))
                    (forall ((p Bool) (q Bool)) (and p q)))) :rule ac_simp)": true,
            }
            "Removing duplicates" {
                "(step t1 (cl (= (or p p q r s) (or p q r s))) :rule ac_simp)": true,
                "(step t1 (cl (= (and (and p q) (and q r)) (and p q r))) :rule ac_simp)": true,
                "(step t1 (cl (= (and (and p q) (and q r)) (and p q q r))) :rule ac_simp)": false,
            }
        }
    }
}
