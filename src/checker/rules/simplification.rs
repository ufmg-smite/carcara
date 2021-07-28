use super::{to_option, RuleArgs};
use crate::{ast::*, utils::DedupIterator};
use num_rational::BigRational;
use num_traits::{One, Zero};
use std::collections::HashSet;

/// A macro to define the possible transformations for a "simplify" rule.
macro_rules! simplify {
    // This is a recursive macro that expands to a series of nested `match` expressions. For
    // example:
    //      simplify!(term {
    //          (or a b): (bind_a, bind_b) => foo,
    //          (not c): (bind_c) if pred(bind_c) => bar,
    //      })
    // becomes:
    //      match match_term!((or a b) = term, RETURN_RCS) {
    //          Some((bind_a, bind_b)) => foo,
    //          _ => match match_term!((not c) = term, RETURN_RCS) {
    //              Some(bind_c) if pred(bind_c) => bar,
    //              _ => None,
    //          }
    //      }
    ($term:ident {}) => { None };
    ($term:ident {
        $pat:tt: $idens:tt $(if $guard:expr)? => $res:expr,
        $($rest:tt)*
     }) => {
        match match_term!($pat = $term, RETURN_RCS) {
            Some($idens) $(if $guard)? => Some($res),
            _ => simplify!($term { $($rest)* }),
        }
    };
}

fn generic_simplify_rule(
    conclusion: &[ByRefRc<Term>],
    pool: &mut TermPool,
    simplify_function: fn(&Term, &mut TermPool) -> Option<ByRefRc<Term>>,
) -> Option<()> {
    rassert!(conclusion.len() == 1);

    let (current, goal) = match_term!((= phi psi) = conclusion[0].as_ref(), RETURN_RCS)?;
    let mut current = current.clone();
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(current.clone()) {
            panic!("Cycle detected in simplification rule!")
        }
        if let Some(next) = simplify_function(&current, pool) {
            if next == *goal {
                return Some(());
            }
            current = next;
        } else {
            return None;
        }
    }
}

pub fn eq_simplify(args: RuleArgs) -> Option<()> {
    generic_simplify_rule(args.conclusion, args.pool, |term, pool| {
        simplify!(term {
            // t = t => true
            (= t t): (t1, t2) if t1 == t2 => pool.bool_true(),

            // t_1 = t_2 => false, if t_1 and t_2 are different numerical constants
            (= t t): (t1, t2) if {
                let t1 = t1.try_as_signed_ratio();
                let t2 = t2.try_as_signed_ratio();
                t1.is_some() && t2.is_some() && t1 != t2
            } => pool.bool_false(),

            // ¬(t = t) => false, if t is a numerical constant
            (not (= t t)): (t1, t2) if t1 == t2 && t1.is_signed_constant() => pool.bool_false(),
        })
    })
}

/// Used for both the "and_simplify" and "or_simplify" rules, depending on `rule_kind`. `rule_kind`
/// has to be either `Operator::And` or `Operator::Or`.
fn generic_and_or_simplify(conclusion: &[ByRefRc<Term>], rule_kind: Operator) -> Option<()> {
    rassert!(conclusion.len() == 1);

    // The "skip term" is the term that represents the empty conjunction or disjunction, and can be
    // skipped. This is "false" for conjunctions and "true" disjunctions
    let is_skip_term = match rule_kind {
        Operator::And => Term::is_bool_true,
        Operator::Or => Term::is_bool_false,
        _ => unreachable!(),
    };

    // The "short-circuit term" is the term that can short-circuit the conjunction or disjunction.
    // This is "true" for conjunctions and "false" disjunctions
    let is_short_ciruit_term = match rule_kind {
        Operator::And => Term::is_bool_false,
        Operator::Or => Term::is_bool_true,
        _ => unreachable!(),
    };

    let (phis, result) = match_term!((= phi psi) = conclusion[0], RETURN_RCS)?;
    let phis = match phis.as_ref() {
        Term::Op(op, args) if *op == rule_kind => args,
        _ => return None,
    };
    let result = match result.as_ref() {
        Term::Op(op, args) if *op == rule_kind => args,
        _ => std::slice::from_ref(result),
    };

    let mut seen = HashSet::with_capacity(phis.len());
    let mut expected = Vec::with_capacity(phis.len());

    for term in phis {
        if is_skip_term(term) {
            continue; // Skip term if it is the "skip term"
        }

        // If the term is the "short-circuit term", or is the negation of a term previously
        // encountered, the result is short-circuited
        let (polarity, inner) = term.remove_all_negations_with_polarity();
        if seen.contains(&(!polarity, inner)) || is_short_ciruit_term(term) {
            return to_option(result.len() == 1 && is_short_ciruit_term(&result[0]));
        }

        let is_new = seen.insert((polarity, inner));
        if is_new {
            expected.push(term)
        }
    }

    to_option(if expected.is_empty() {
        // If the filtered conjunction or disjunction is empty, the expected result is just the
        // "skip term", which represents an empty conjunction or disjunction
        result.len() == 1 && is_skip_term(&result[0])
    } else {
        result.iter().eq(expected)
    })
}

pub fn and_simplify(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    generic_and_or_simplify(conclusion, Operator::And)
}

pub fn or_simplify(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    generic_and_or_simplify(conclusion, Operator::Or)
}

pub fn not_simplify(args: RuleArgs) -> Option<()> {
    generic_simplify_rule(args.conclusion, args.pool, |term, pool| {
        simplify!(term {
            // ¬(¬phi) => phi
            (not (not phi)): phi => phi.clone(),

            // ¬false => true
            (not lit): lit if lit.is_bool_false() => pool.bool_true(),

            // ¬true => false
            (not lit): lit if lit.is_bool_true() => pool.bool_false(),
        })
    })
}

pub fn implies_simplify(args: RuleArgs) -> Option<()> {
    generic_simplify_rule(args.conclusion, args.pool, |term, pool| {
        simplify!(term {
            // ¬phi_1 -> ¬phi_2 => phi_2 -> phi_1
            (=> (not phi_1) (not phi_2)): (phi_1, phi_2) => {
                build_term!(pool, (=> {phi_2.clone()} {phi_1.clone()}))
            },

            // false -> phi => true
            (=> f phi): (f, _) if f.is_bool_false() => pool.bool_true(),

            // phi -> true => true
            (=> phi t): (_, t) if t.is_bool_true() => pool.bool_true(),

            // true -> phi => phi
            (=> t phi): (t, phi) if t.is_bool_true() => phi.clone(),

            // phi -> false => ¬phi
            (=> phi f): (phi, f) if f.is_bool_false() => build_term!(pool, (not {phi.clone()})),

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

pub fn equiv_simplify(args: RuleArgs) -> Option<()> {
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
            (= t phi_1): (t, phi_1) if t.is_bool_true() => phi_1.clone(),

            // phi = true => phi
            (= phi_1 t): (phi_1, t) if t.is_bool_true() => phi_1.clone(),

            // false = phi => ¬phi
            (= f phi_1): (f, phi_1) if f.is_bool_false() => build_term!(pool, (not {phi_1.clone()})),

            // phi = false => ¬phi
            (= phi_1 f): (phi_1, f) if f.is_bool_false() => build_term!(pool, (not {phi_1.clone()})),
        })
    })
}

pub fn bool_simplify(args: RuleArgs) -> Option<()> {
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

pub fn prod_simplify(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    /// Checks if the u term is valid and extracts from it the leading constant and the remaining
    /// arguments.
    fn unwrap_u_term(u: &ByRefRc<Term>) -> Option<(BigRational, &[ByRefRc<Term>])> {
        Some(match match_term!((* ...) = u) {
            Some([] | [_]) => unreachable!(),

            Some(args) => {
                // We check if there are any constants in u (aside from the leading constant). If
                // there are any, we know this u term is invalid, so we can return `None`
                if args[1..].iter().any(|t| t.is_constant()) {
                    return None;
                }
                match args[0].try_as_ratio() {
                    // If the leading constant is 1, it should have been omitted
                    Some(constant) if constant.is_one() => return None,
                    Some(constant) => (constant, &args[1..]),
                    None => (BigRational::one(), args),
                }
            }

            // If u is not a product, we consider it a product of a single term. That term might be
            // a regular term or the leading constant, depending on if u is a constant or not
            None => match u.try_as_ratio() {
                Some(u) => (u, &[]),
                None => (BigRational::one(), std::slice::from_ref(u)),
            },
        })
    }

    rassert!(conclusion.len() == 1);

    let (first, second) = match_term!((= first second) = conclusion[0].as_ref(), RETURN_RCS)?;
    let (ts, (u_constant, u_args)) = {
        // Since the ts and u terms may be in either order, we have to try to validate both options
        // to find out which term is which
        let try_order = |ts, u| {
            let ts = match_term!((* ...) = ts)?;
            Some((ts, unwrap_u_term(u)?))
        };
        try_order(first, second).or_else(|| try_order(second, first))?
    };

    let mut result = Vec::with_capacity(ts.len());
    let mut constant_total = BigRational::one();

    // First, we go through the t_i terms, multiplying all the constants we find together, and push
    // the non-constant terms to the `result` vector
    for t in ts {
        match t.as_ref() {
            Term::Terminal(Terminal::Real(r)) => constant_total *= r,
            Term::Terminal(Terminal::Integer(i)) => constant_total *= i,
            t => {
                result.push(t);
                continue; // Since `constant_total` didn't change, we can skip the check
            }
        }
        // If we find a zero, we can leave the loop early. We also clear the `result` vector
        // because we expect the u term to be just the zero constant
        if constant_total == BigRational::zero() {
            result.clear();
            break;
        }
    }

    // Finally, we verify that the constant and the remaining arguments are what we expect
    to_option(u_constant == constant_total && u_args.iter().map(ByRefRc::as_ref).eq(result))
}

pub fn ac_simp(
    RuleArgs {
        conclusion, pool, ..
    }: RuleArgs,
) -> Option<()> {
    fn flatten_operation(term: &ByRefRc<Term>, pool: &mut TermPool) -> ByRefRc<Term> {
        let term = match term.as_ref() {
            Term::Op(op @ (Operator::And | Operator::Or), args) => {
                let args: Vec<_> = args
                    .iter()
                    .flat_map(|term| {
                        let term = flatten_operation(term, pool);
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
                    .map(|term| flatten_operation(term, pool))
                    .collect();
                Term::Op(*op, args)
            }
            Term::App(func, args) => {
                let args = args
                    .iter()
                    .map(|term| flatten_operation(term, pool))
                    .collect();
                Term::App(func.clone(), args)
            }
            Term::Quant(q, bindings, inner) => {
                Term::Quant(*q, bindings.clone(), flatten_operation(inner, pool))
            }
            Term::Choice(binding, inner) => {
                Term::Choice(binding.clone(), flatten_operation(inner, pool))
            }
            Term::Let(binding, inner) => Term::Let(binding.clone(), flatten_operation(inner, pool)),
            _ => return term.clone(),
        };
        pool.add_term(term)
    }
    rassert!(conclusion.len() == 1);
    let (original, flattened) = match_term!((= psi phis) = conclusion[0], RETURN_RCS)?;
    to_option(flatten_operation(original, pool) == *flattened)
}

#[cfg(test)]
mod tests {
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
                "(step t1 (cl (= (and p (not (not (not p))) (not p)) false)) :rule and_simplify)": true,

                "(step t1 (cl (= (and p (not (not p)) (not q) r) false)) :rule and_simplify)": false,
                "(step t1 (cl (= (and q (not r)) false)) :rule and_simplify)": false,
                "(step t1 (cl (= (and r (not r)) true)) :rule and_simplify)": false,
            }
            "Multiple transformations" {
                "(step t1 (cl (= (and p p true q q true q r) (and p q r))) :rule and_simplify)": true,
                "(step t1 (cl (= (and p p (not p) q q true q r) false)) :rule and_simplify)": true,
                "(step t1 (cl (= (and p false p (not p) q true q r) false)) :rule and_simplify)": true,
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
