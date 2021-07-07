use super::{get_single_term_from_command, to_option, RuleArgs};
use crate::ast::*;
use std::collections::HashSet;

pub fn subproof(
    RuleArgs {
        conclusion,
        subproof_commands,
        ..
    }: RuleArgs,
) -> Option<()> {
    // TODO: We should get the series of assumptions from the ":discharge" attribute, but currently
    // we just take the first `conclusion.len() - 1` steps in the subproof.
    let assumptions = &subproof_commands[..conclusion.len() - 1];

    rassert!(conclusion.len() == assumptions.len() + 1); // Currently, this is always true

    for (assumption, term) in assumptions.iter().zip(conclusion) {
        let assumption = get_single_term_from_command(assumption)?;
        rassert!(assumption.as_ref() == term.remove_negation()?)
    }

    let previous_command = &subproof_commands[subproof_commands.len() - 2];
    let phi = get_single_term_from_command(previous_command)?;

    to_option(conclusion.last().unwrap() == phi)
}

pub fn bind(
    RuleArgs {
        conclusion,
        pool,
        context,
        subproof_commands,
        ..
    }: RuleArgs,
) -> Option<()> {
    rassert!(subproof_commands.len() >= 2 && conclusion.len() == 1);

    // The last command in the subproof is the one we are currently checking, so we look at the one
    // before that
    let previous_command = &subproof_commands[subproof_commands.len() - 2];
    let (phi, phi_prime) =
        match_term!((= p q) = get_single_term_from_command(previous_command)?, RETURN_RCS)?;

    let (left, right) = match_term!((= l r) = conclusion[0])?;

    // While the documentation indicates this rule is only called with "forall" quantifiers, in
    // some of the tests examples it is also called with the "exists" quantifier
    let (l_quant, l_bindings, left) = left.unwrap_quant()?;
    let (r_quant, r_bindings, right) = right.unwrap_quant()?;
    rassert!(l_quant == r_quant);

    let l_bindings: HashSet<_> = l_bindings.iter().map(|(var, _)| var.as_str()).collect();
    let r_bindings: HashSet<_> = r_bindings.iter().map(|(var, _)| var.as_str()).collect();

    // The terms in the quantifiers must be phi and phi'
    rassert!(left == phi && right == phi_prime);

    // None of the bindings in the right side can appear as free variables in phi
    let free_vars = pool.free_vars(phi);
    rassert!(r_bindings
        .difference(&l_bindings)
        .all(|&y| !free_vars.contains(y)));

    // Since we are closing a subproof, we only care about the substitutions that were introduced
    // in it
    let context = context.last()?;

    // The quantifier binders must be the xs and ys of the context substitutions
    let (xs, ys): (HashSet<_>, HashSet<_>) = context
        .substitutions
        .iter()
        // We skip terms which are not simply variables
        .filter_map(|(x, y)| Some((x.try_as_var()?, y.try_as_var()?)))
        .chain(
            // Sometimes, the context bindings also appear as bindings in the quantifiers, so we
            // include them in the "xs" and "ys"
            context
                .bindings
                .iter()
                .map(|(var, _)| (var.as_str(), var.as_str())),
        )
        .unzip();
    to_option(
        l_bindings.len() == r_bindings.len()
            && l_bindings.is_subset(&xs)
            && r_bindings.is_subset(&ys),
    )
}

pub fn r#let(
    RuleArgs {
        conclusion,
        context,
        premises,
        pool,
        subproof_commands,
        ..
    }: RuleArgs,
) -> Option<()> {
    rassert!(conclusion.len() == 1);

    // Since we are closing a subproof, we only care about the substitutions that were introduced
    // in it
    let substitutions = &context.last()?.substitutions;

    let (let_term, u_prime) = match_term!((= l u) = conclusion[0], RETURN_RCS)?;
    let (let_bindigns, u) = match let_term.as_ref() {
        Term::Let(b, t) => (b, t),
        _ => return None,
    };

    // The u and u' in the conclusion must match the u and u' in the previous command in the
    // subproof
    let previous_term =
        get_single_term_from_command(&subproof_commands[subproof_commands.len() - 2])?;
    let (previous_u, previous_u_prime) = match_term!((= u u_prime) = previous_term, RETURN_RCS)?;
    rassert!(u == previous_u && u_prime == previous_u_prime);

    rassert!(let_bindigns.len() == substitutions.len());

    let mut premises = premises.iter();
    for (x, t) in let_bindigns {
        let x_term = terminal!(var x; pool.add_term(t.sort().clone()));
        let s = substitutions.get(&pool.add_term(x_term))?;
        if s != t {
            let premise = premises.next()?;
            let premise_equality = match_term!((= a b) = get_single_term_from_command(premise)?)?;
            rassert!(premise_equality == (s, t) || premise_equality == (t, s));
        }
    }
    to_option(premises.next().is_none())
}

pub fn onepoint(
    RuleArgs {
        conclusion,
        context,
        pool,
        subproof_commands,
        ..
    }: RuleArgs,
) -> Option<()> {
    rassert!(conclusion.len() == 1);
    let (left, right) = match_term!((= l r) = conclusion[0], RETURN_RCS)?;
    let (l_quant, l_bindings, left) = left.unwrap_quant()?;
    let (r_bindings, right) = match right.unwrap_quant() {
        Some((q, b, t)) => {
            rassert!(q == l_quant);
            (b.as_slice(), t)
        }
        // If the right-hand side term is not a quantifier, that possibly means all quantifier
        // bindings were removed, so we consider it a quantifier with an empty list of bindings
        None => (&[] as &[_], right),
    };

    let previous_term =
        get_single_term_from_command(&subproof_commands[subproof_commands.len() - 2])?;
    let previous_equality = match_term!((= p q) = previous_term, RETURN_RCS)?;
    rassert!(previous_equality == (left, right) || previous_equality == (right, left));

    let context = context.last()?;
    rassert!(
        context.bindings.len() == r_bindings.len()
            && r_bindings.iter().all(|b| context.bindings.contains(b))
    );

    let l_bindings: HashSet<_> = l_bindings
        .iter()
        .map(|var| pool.add_term(var.clone().into()))
        .collect();
    let r_bindings: HashSet<_> = r_bindings
        .iter()
        .map(|var| pool.add_term(var.clone().into()))
        .collect();
    let substitution_vars: HashSet<_> = context
        .substitutions
        .iter()
        .map(|(k, _)| k.clone())
        .collect();

    to_option(l_bindings == &r_bindings | &substitution_vars)
}

#[cfg(test)]
mod tests {
    #[test]
    fn subproof() {
        // TODO: When the ":discharge" attribute is properly implemented, change the examples to
        // use it
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
            ",
            "Simple working examples" {
                "(anchor :step t1)
                (assume t1.h1 p)
                (step t1.t2 (cl q) :rule trust_me)
                (step t1 (cl (not p) q) :rule subproof)": true,

                "(anchor :step t1)
                (assume t1.h1 p)
                (assume t1.h2 q)
                (step t1.t3 (cl (= r s)) :rule trust_me)
                (step t1 (cl (not p) (not q) (= r s)) :rule subproof)": true,
            }
            "Missing assumption" {
                "(anchor :step t1)
                (assume t1.h1 p)
                (step t1.t2 (cl (= r s)) :rule trust_me)
                (step t1 (cl (not p) (not q) (= r s)) :rule subproof)": false,
            }
            "Assumption terms don't match" {
                "(anchor :step t1)
                (assume t1.h1 p)
                (assume t1.h2 q)
                (step t1.t3 (cl (= r s)) :rule trust_me)
                (step t1 (cl (not q) (not p) (= r s)) :rule subproof)": false,

                "(anchor :step t1)
                (assume t1.h1 (or p q))
                (assume t1.h2 (= p q))
                (step t1.t3 (cl (= r s)) :rule trust_me)
                (step t1 (cl (not (and p q)) (not (= q p)) (= r s)) :rule subproof)": false,
            }
            "Conclusion terms don't match" {
                "(anchor :step t1)
                (assume t1.h1 p)
                (assume t1.h2 q)
                (step t1.t3 (cl (= r s)) :rule trust_me)
                (step t1 (cl (not p) (not q) (= s r)) :rule subproof)": false,
            }
        }
    }

    #[test]
    fn bind() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
                (declare-fun y () Real)
            ",
            "Simple working examples" {
                "(anchor :step t1 :args ((:= (x Real) y)))
                (step t1.t1 (cl (= p q)) :rule trust_me)
                (step t1 (cl (= (forall ((x Real)) p) (forall ((y Real)) q))) :rule bind)": true,

                "(anchor :step t1 :args ((:= (x1 Real) y1) (:= (x2 Real) y2)))
                (step t1.t1 (cl (= (= x1 x2) (= y1 y2))) :rule trust_me)
                (step t1 (cl (= (forall ((x1 Real) (x2 Real)) (= x1 x2))
                    (forall ((y1 Real) (y2 Real)) (= y1 y2)))) :rule bind)": true,
            }
            "Examples with binding arguments" {
                "(anchor :step t1 :args ((z Real) (:= (x Real) y)))
                (step t1.t1 (cl (= p q)) :rule trust_me)
                (step t1 (cl (= (forall ((x Real) (z Real)) p)
                    (forall ((y Real) (z Real)) q))) :rule bind)": true,
            }
            "y_i appears in phi as a free variable" {
                "(anchor :step t1 :args ((:= (x Real) y)))
                (step t1.t1 (cl (= (= y x) (= y y))) :rule trust_me)
                (step t1 (cl (= (forall ((x Real)) (= y x))
                    (forall ((y Real)) (= y y)))) :rule bind)": false,

                "(anchor :step t1 :args ((z Real) (:= (x Real) y)))
                (step t1.t1 (cl (= (= y x) (= y y))) :rule trust_me)
                (step t1 (cl (= (forall ((z Real) (x Real)) (= y z))
                    (forall ((z Real) (y Real)) (= y z)))) :rule bind)": false,
            }
            "Terms in conclusion clause don't match terms in previous command" {
                "(anchor :step t1 :args ((:= (x Real) y)))
                (step t1.t1 (cl (= p q)) :rule trust_me)
                (step t1.t2 (cl (= r s)) :rule trust_me) ; This step shouldn't be here!
                (step t1 (cl (= (forall ((x Real)) p) (forall ((y Real)) q))) :rule bind)": false,

                "(anchor :step t1 :args ((:= (x Real) y)))
                (step t1.t1 (cl (= p q)) :rule trust_me)
                (step t1 (cl (= (forall ((x Real)) q) (forall ((y Real)) p))) :rule bind)": false,
            }
            "Context substitutions don't match quantifier bindings" {
                "(anchor :step t1 :args ((:= (x Real) y)))
                (step t1.t1 (cl (= p q)) :rule trust_me)
                (step t1 (cl (= (forall ((y Real)) p) (forall ((x Real)) q))) :rule bind)": false,

                "(anchor :step t1 :args ((:= (x1 Real) y1) (:= (x2 Real) y2)))
                (step t1.t1 (cl (= (= x1 x2) (= y1 y2))) :rule trust_me)
                (step t1 (cl (= (forall ((x2 Real)) (= x1 x2))
                    (forall ((y1 Real) (y2 Real)) (= y1 y2)))) :rule bind)": false,
            }
        }
    }

    #[test]
    fn r#let() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun i () Int)
                (declare-fun j () Int)
                (declare-fun k () Int)
            ",
            "Simple working examples" {
                "(anchor :step t1 :args ((:= (a Int) x)))
                (step t1.t1 (cl (= i x)) :rule trust_me)
                (step t1.t2 (cl (= p q)) :rule trust_me)
                (step t1 (cl (= (let ((a i)) p) q)) :rule let :premises (t1.t1))": true,

                "(anchor :step t1 :args (
                    (:= (a Int) x) (:= (b Int) y) (:= (c Int) z)
                ))
                (step t1.t1 (cl (= i x)) :rule trust_me)
                (step t1.t2 (cl (= k z)) :rule trust_me)
                (step t1.t3 (cl (= p q)) :rule trust_me)
                (step t1 (cl (= (let ((a i) (b y) (c k)) p) q))
                    :rule let :premises (t1.t1 t1.t2))": true,
            }
            "Premise equalities may be flipped" {
                "(anchor :step t1 :args ((:= (a Int) x)))
                (step t1.t1 (cl (= x i)) :rule trust_me)
                (step t1.t2 (cl (= p q)) :rule trust_me)
                (step t1 (cl (= (let ((a i)) p) q)) :rule let :premises (t1.t1))": true,
            }
            "Wrong number of premises" {
                "(anchor :step t1 :args (
                    (:= (a Int) x) (:= (b Int) y) (:= (c Int) z)
                ))
                (step t1.t1 (cl (= i x)) :rule trust_me)
                (step t1.t2 (cl (= p q)) :rule trust_me)
                (step t1 (cl (= (let ((a i) (b y) (c k)) p) q))
                    :rule let :premises (t1.t1))": false,

                "(anchor :step t1 :args (
                    (:= (a Int) x) (:= (b Int) y) (:= (c Int) z)
                ))
                (step t1.t1 (cl (= i x)) :rule trust_me)
                (step t1.t2 (cl (= y y)) :rule trust_me)
                (step t1.t3 (cl (= k z)) :rule trust_me)
                (step t1.t4 (cl (= p q)) :rule trust_me)
                (step t1 (cl (= (let ((a i) (b y) (c k)) p) q))
                    :rule let :premises (t1.t1 t1.t2))": false,
            }
            "Number of bindings is `let` term doesn't match number of substitutions in context" {
                "(anchor :step t1 :args (
                    (:= (a Int) x) (:= (b Int) y) (:= (c Int) z)
                ))
                (step t1.t1 (cl (= i x)) :rule trust_me)
                (step t1.t2 (cl (= j y)) :rule trust_me)
                (step t1.t3 (cl (= p q)) :rule trust_me)
                (step t1 (cl (= (let ((a i) (b j)) p) q)) :rule let :premises (t1.t1 t1.t2))": false,
            }
            "u and u' don't match equality in previous command" {
                "(anchor :step t1 :args ((:= (a Int) x)))
                (step t1.t1 (cl (= i x)) :rule trust_me)
                (step t1.t2 (cl (= p (= i j))) :rule trust_me)
                (step t1 (cl (= (let ((a i)) p) q)) :rule let :premises (t1.t1))": false,
            }
        }
    }
}
