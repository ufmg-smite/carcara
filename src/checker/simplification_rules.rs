use super::to_option;

use crate::ast::*;

use num_rational::BigRational;
use num_traits::{One, Zero};

/// A macro to define the possible transformations for a "simplify" rule.
macro_rules! simplify {
        // This is a recursive macro that expands to a series of nested `match` expressions. For
        // example:
        //      simplify!(term {
        //          (or a b): (bind_a, bind_b) => { foo },
        //          (not c): (bind_c) if pred(bind_c) => { bar },
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
            $pat:tt: $idens:tt $(if $guard:expr)? => { $res:expr },
            $($rest:tt)*
         }) => {
            match match_term!($pat = $term, RETURN_RCS) {
                Some($idens) $(if $guard)? => Some($res),
                _ => simplify!($term { $($rest)* }),
            }
        };
    }

fn bool_simplify_once(term: &Term) -> Option<Term> {
    simplify!(term {
        // ¬(phi_1 -> phi_2) => (phi_1 ^ ¬phi_2)
        (not (=> phi_1 phi_2)): (phi_1, phi_2) => {
            build_term!(and {phi_1.clone()} (not {phi_2.clone()}))
        },

        // ¬(phi_1 v phi_2) => (¬phi_1 ^ ¬phi_2)
        (not (or phi_1 phi_2)): (phi_1, phi_2) => {
            build_term!(and (not {phi_1.clone()}) (not {phi_2.clone()}))
        },

        // ¬(phi_1 ^ phi_2) => (¬phi_1 v ¬phi_2)
        (not (and phi_1 phi_2)): (phi_1, phi_2) => {
            build_term!(or (not {phi_1.clone()}) (not {phi_2.clone()}))
        },

        // (phi_1 -> (phi_2 -> phi_3)) => ((phi_1 ^ phi_2) -> phi_3)
        (=> phi_1 (=> phi_2 phi_3)): (phi_1, (phi_2, phi_3)) => {
            build_term!(=> (and {phi_1.clone()} {phi_2.clone()}) {phi_3.clone()})
        },

        // ((phi_1 -> phi_2) -> phi_2) => (phi_1 v phi_2)
        (=> (=> phi_1 phi_2) phi_3): ((phi_1, phi_2), phi_3) if phi_2 == phi_3 => {
            build_term!(or {phi_1.clone()} {phi_2.clone()})
        },

        // (phi_1 ^ (phi_1 -> phi_2)) => (phi_1 ^ phi_2)
        (and phi_1 (=> phi_2 phi_3)): (phi_1, (phi_2, phi_3)) if phi_1 == phi_2 => {
            build_term!(and {phi_1.clone()} {phi_3.clone()})
        },

        // ((phi_1 -> phi_2) ^ phi_1) => (phi_1 ^ phi_2)
        (and (=> phi_1 phi_2) phi_3): ((phi_1, phi_2), phi_3) if phi_1 == phi_3 => {
            build_term!(and {phi_1.clone()} {phi_2.clone()})
        },
    })
}

pub fn bool_simplify(
    clause: &[ByRefRc<Term>],
    _: Vec<&ProofCommand>,
    _: &[ProofArg],
) -> Option<()> {
    if clause.len() != 1 {
        return None;
    }
    let (current, goal) = match_term!((= phi psi) = clause[0].as_ref())?;
    let mut current = current.clone();
    loop {
        if let Some(next) = bool_simplify_once(&current) {
            // TODO: Detect cycles in the simplification rules
            if DeepEq::eq(&next, goal) {
                return Some(());
            } else {
                current = next;
            }
        } else {
            return None;
        }
    }
}

pub fn prod_simplify(
    clause: &[ByRefRc<Term>],
    _: Vec<&ProofCommand>,
    _: &[ProofArg],
) -> Option<()> {
    fn get_ratio_from_term(term: &Term) -> Option<BigRational> {
        match term {
            Term::Terminal(Terminal::Real(r)) => Some(r.clone()),
            Term::Terminal(Terminal::Integer(i)) => Some(BigRational::from_integer(i.clone())),
            _ => None,
        }
    }
    if clause.len() != 1 {
        return None;
    }
    let (ts, u) = match_term!((= (* ...) u) = clause[0].as_ref())?;
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

    // Extract from the u term the leading constant and the remaining arguments
    let (u_constant, u_args) = match match_term!((* ...) = u) {
        Some([]) | Some([_]) => unreachable!(),
        // If `constant_total` is one, we expect there to be no leading constant in u
        Some(args) if constant_total == BigRational::one() => (BigRational::one(), args),
        Some([constant, rest @ ..]) => (get_ratio_from_term(constant)?, rest),
        // If u is not a product, we take the term as whole as the leading constant, with no
        // remaining arguments
        None => (get_ratio_from_term(u)?, &[] as &[_]),
    };

    // Finally, we verify that the constant and the remaining arguments are what we expect
    to_option(u_constant == constant_total && u_args.iter().map(ByRefRc::as_ref).eq(result))
}
