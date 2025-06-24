use super::{
    assert_clause_len, assert_eq, assert_is_bool_constant, CheckerError, EqualityError, RuleArgs,
    RuleResult,
};
use crate::{ast::*, utils::DedupIterator};
use indexmap::{IndexMap, IndexSet};
use rug::Rational;

/// A macro to define the possible transformations for a "simplify" rule.
macro_rules! simplify {
    // This is a recursive macro that expands to a series of nested `match` expressions. For
    // example:
    // ```
    //      simplify!(term {
    //          (or a b): (bind_a, bind_b) => foo,
    //          (not c): (bind_c) if pred(bind_c) => bar,
    //      })
    // ```
    // becomes
    // ```
    //      match match_term!((or a b) = term) {
    //          Some((bind_a, bind_b)) => foo,
    //          _ => match match_term!((not c) = term) {
    //              Some(bind_c) if pred(bind_c) => bar,
    //              _ => None,
    //          }
    //      }
    // ```
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
    pool: &mut dyn TermPool,
    simplify_function: fn(&Term, &mut dyn TermPool) -> Option<Rc<Term>>,
) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let mut simplify_until_fixed_point =
        |term: &Rc<Term>, goal: &Rc<Term>| -> Result<Rc<Term>, CheckerError> {
            let mut current = term.clone();
            let mut seen = IndexSet::new();
            loop {
                if !seen.insert(current.clone()) {
                    return Err(CheckerError::CycleInSimplification(current));
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

    // Since equalities can be implicitly flipped, we have to check both possibilities. We store the
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
    pool: &mut dyn TermPool,
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
    // This is `true` for conjunctions and `false` for disjunctions
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
    // the rule operator, where the outer operation only has one argument, e.g. `(and (and p q r))`.
    // If we encounter this, we remove the outer application
    if phis.len() == 1 {
        match phis[0].as_ref() {
            #[allow(clippy::assigning_clones)]
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
    let mut seen = IndexSet::with_capacity(phis.len());
    phis.retain(|t| seen.insert(t.clone()));
    if result_args.iter().eq(&phis) {
        return Ok(());
    }

    // Finally, we check to see if the result was short-circuited
    let seen: IndexSet<(bool, &Rc<Term>)> = phis
        .iter()
        .map(Rc::remove_all_negations_with_polarity)
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
        let expected = pool.add(Term::Op(rule_kind, phis));
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
    let (_, _, inner) = left.as_quant_err()?;
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

    // in the case l is (/ c1 c2), this term will have been parsed to
    // a rational constant. So we check that l is the same as r in
    // this case
    if left.is_const() {
        if let Term::Const(Constant::Real(_)) = right.as_ref() {
            return assert_eq(left, right);
        }
        return Err(CheckerError::ExpectedNumber(Rational::new(), right.clone()));
    }

    let ((numer, denom), is_int_div) = match match_term!((div n d) = left) {
        Some(v) => (v, true),
        None => (match_term_err!((/ n d) = left)?, false),
    };

    if numer == denom {
        rassert!(
            right.as_signed_number_err()? == 1,
            CheckerError::ExpectedNumber(Rational::new(), right.clone())
        );
        Ok(())
    } else if denom.as_number().is_some_and(|n| n == 1) {
        assert_eq(right, numer)
    } else {
        let denom = denom.as_signed_number_err()?;
        if denom.is_zero() {
            return Err(CheckerError::DivOrModByZero);
        }
        let numer = numer.as_signed_number_err()?;
        let expected = if is_int_div {
            assert!(numer.is_integer() && denom.is_integer()); // This is guaranteed by the Alethe typing rules
            let [numer, denom] = [numer, denom].map(|n| n.into_numer_denom().0);
            Rational::from(numer.div_rem_euc(denom).0)
        } else {
            numer / denom
        };
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
    pool: &mut dyn TermPool,
    ts: &Rc<Term>,
    u: &Rc<Term>,
    rule_kind: Operator,
) -> RuleResult {
    let identity_value = match rule_kind {
        Operator::Add => Rational::new(),
        Operator::Mult => Rational::from(1),
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
        if rule_kind == Operator::Mult && constant_total == 0 {
            result.clear();
            break;
        }
    }

    // This covers a tricky edge case that happens when the only non-constant term in `ts` is also a
    // valid application of the rule operator. For example:
    // ```
    //     (step t1 (cl
    //         (= (* 1 (* 2 x)) (* 2 x))
    //     ) :rule prod_simplify)
    // ```
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
            let mut expected_args = vec![pool.add(Term::new_real(constant_total))];
            expected_args.extend(u_args.iter().cloned());
            pool.add(Term::Op(rule_kind, expected_args))
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
        if match_term!((-(-t)) = t) == Some(u) {
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
                u.as_number_err()? == 0,
                CheckerError::ExpectedNumber(Rational::from(1), u.clone()),
            );
            return Ok(());
        }
        match (t_1.as_signed_number(), t_2.as_signed_number()) {
            (_, Some(z)) if z == 0 => assert_eq(u, t_1),
            (Some(z), _) if z == 0 => assert_eq(match_term_err!((-t) = u)?, t_2),
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
                    (t_1.as_fraction(), t_2.as_fraction())
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
                    (t_1.as_fraction(), t_2.as_fraction())
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

fn apply_ac_simp(
    pool: &mut dyn TermPool,
    cache: &mut IndexMap<Rc<Term>, Rc<Term>>,
    term: &Rc<Term>,
) -> Rc<Term> {
    if let Some(t) = cache.get(term) {
        return t.clone();
    }
    let result = match term.as_ref() {
        Term::Op(op @ (Operator::And | Operator::Or), args) => {
            let args: Vec<_> = args
                .iter()
                .flat_map(|term| {
                    let term = apply_ac_simp(pool, cache, term);
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
                .map(|term| apply_ac_simp(pool, cache, term))
                .collect();
            Term::Op(*op, args)
        }
        Term::App(func, args) => {
            let args = args
                .iter()
                .map(|term| apply_ac_simp(pool, cache, term))
                .collect();
            Term::App(func.clone(), args)
        }
        Term::Binder(q, bindings, inner) => {
            Term::Binder(*q, bindings.clone(), apply_ac_simp(pool, cache, inner))
        }
        Term::Let(binding, inner) => Term::Let(binding.clone(), apply_ac_simp(pool, cache, inner)),
        _ => return term.clone(),
    };
    let result = pool.add(result);
    cache.insert(term.clone(), result.clone());
    result
}

pub fn ac_simp(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (original, flattened) = match_term_err!((= psi phis) = &conclusion[0])?;
    assert_eq(
        flattened,
        &apply_ac_simp(pool, &mut IndexMap::new(), original),
    )
}
