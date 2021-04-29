use crate::ast::*;

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
