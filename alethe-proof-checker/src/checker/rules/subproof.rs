use super::{get_single_term_from_command, to_option, RuleArgs};
use crate::ast::*;
use ahash::{AHashMap, AHashSet};

pub fn subproof(RuleArgs { conclusion, subproof_commands, .. }: RuleArgs) -> Option<()> {
    // TODO: We should get the series of assumptions from the ":discharge" attribute, but currently
    // we just take the first `conclusion.len() - 1` steps in the subproof.
    let assumptions = &subproof_commands?[..conclusion.len() - 1];

    rassert!(conclusion.len() == assumptions.len() + 1); // Currently, this is always true

    for (assumption, term) in assumptions.iter().zip(conclusion) {
        match assumption {
            ProofCommand::Assume(t) => rassert!(t.as_ref() == term.remove_negation()?),
            _ => return None,
        };
    }

    let previous_command = &subproof_commands?[subproof_commands?.len() - 2];
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
    rassert!(subproof_commands?.len() >= 2 && conclusion.len() == 1);

    // The last command in the subproof is the one we are currently checking, so we look at the one
    // before that
    let previous_command = &subproof_commands?[subproof_commands?.len() - 2];
    let (phi, phi_prime) =
        match_term!((= p q) = get_single_term_from_command(previous_command)?, RETURN_RCS)?;

    let (left, right) = match_term!((= l r) = conclusion[0])?;

    // While the documentation indicates this rule is only called with "forall" quantifiers, in
    // some of the tests examples it is also called with the "exists" quantifier
    let (l_quant, l_bindings, left) = left.unwrap_quant()?;
    let (r_quant, r_bindings, right) = right.unwrap_quant()?;
    rassert!(l_quant == r_quant);

    let l_bindings: AHashSet<_> = l_bindings.iter().map(|(var, _)| var.as_str()).collect();
    let r_bindings: AHashSet<_> = r_bindings.iter().map(|(var, _)| var.as_str()).collect();

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
    let (xs, ys): (AHashSet<_>, AHashSet<_>) = context
        .substitutions
        .iter()
        // We skip terms which are not simply variables
        .filter_map(|(x, y)| Some((x.as_var()?, y.as_var()?)))
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
    let (let_bindings, u) = match let_term.as_ref() {
        Term::Let(b, t) => (b, t),
        _ => return None,
    };

    // The u and u' in the conclusion must match the u and u' in the previous command in the
    // subproof
    let previous_term =
        get_single_term_from_command(&subproof_commands?[subproof_commands?.len() - 2])?;
    let (previous_u, previous_u_prime) = match_term!((= u u_prime) = previous_term, RETURN_RCS)?;
    rassert!(u == previous_u && u_prime == previous_u_prime);

    rassert!(let_bindings.len() == substitutions.len());

    let mut premises = premises.iter();
    for (x, t) in let_bindings {
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

fn extract_points(quant: Quantifier, term: &Term) -> AHashSet<(Rc<Term>, Rc<Term>)> {
    fn find_points(acc: &mut AHashSet<(Rc<Term>, Rc<Term>)>, polarity: bool, term: &Term) {
        // This does not make use of a cache, so there may be performance issues
        // TODO: Measure the performance of this function, and see if a cache is needed

        if let Some(inner) = term.remove_negation() {
            return find_points(acc, !polarity, inner);
        }
        if let Some((_, _, inner)) = term.unwrap_quant() {
            return find_points(acc, polarity, inner);
        }
        match polarity {
            true => {
                if let Some((x, t)) = match_term!((= x t) = term, RETURN_RCS) {
                    acc.insert((x.clone(), t.clone()));
                } else if let Some(args) = match_term!((and ...) = term, RETURN_RCS) {
                    for a in args {
                        find_points(acc, true, a.as_ref())
                    }
                }
            }
            false => {
                if let Some((p, q)) = match_term!((=> p q) = term, RETURN_RCS) {
                    find_points(acc, true, p);
                    find_points(acc, false, q);
                } else if let Some(args) = match_term!((or ...) = term, RETURN_RCS) {
                    for a in args {
                        find_points(acc, false, a.as_ref())
                    }
                }
            }
        }
    }

    let mut result = AHashSet::new();
    find_points(&mut result, quant == Quantifier::Exists, term);
    result
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
    let (quant, l_bindings, left) = left.unwrap_quant()?;
    let (r_bindings, right) = match right.unwrap_quant() {
        Some((q, b, t)) => {
            rassert!(q == quant);
            (b.as_slice(), t)
        }
        // If the right-hand side term is not a quantifier, that possibly means all quantifier
        // bindings were removed, so we consider it a quantifier with an empty list of bindings
        None => (&[] as &[_], right),
    };

    let previous_term =
        get_single_term_from_command(&subproof_commands?[subproof_commands?.len() - 2])?;
    let previous_equality = match_term!((= p q) = previous_term, RETURN_RCS)?;
    rassert!(previous_equality == (left, right) || previous_equality == (right, left));

    let context = context.last()?;
    rassert!(
        context.bindings.len() == r_bindings.len()
            && r_bindings.iter().all(|b| context.bindings.contains(b))
    );

    let l_bindings: AHashSet<_> = l_bindings
        .iter()
        .map(|var| pool.add_term(var.clone().into()))
        .collect();
    let r_bindings: AHashSet<_> = r_bindings
        .iter()
        .map(|var| pool.add_term(var.clone().into()))
        .collect();
    let substitution_vars: AHashSet<_> = context
        .substitutions
        .iter()
        .map(|(k, _)| k.clone())
        .collect();

    let points = extract_points(quant, left);

    // We clone the substitutions so we don't pollute the hash map when applying the substitutions
    // to `points`
    let substitutions_clone = context.substitutions_until_fixed_point.clone();

    // Since a substitution may use a varibale introduced in a previous substitution, we apply the
    // substitutions to the points in order to these variables. We also create a duplicate of every
    // point in the reverse order, since the order of equalities may be flipped
    let points: AHashSet<_> = points
        .into_iter()
        .flat_map(|(x, t)| {
            let new_t = pool.apply_substitutions(&t, &substitutions_clone);
            let new_x = pool.apply_substitutions(&x, &substitutions_clone);
            [(x, new_t), (t, new_x)]
        })
        .collect();

    // For each substitution (:= x t) in the context, the equality (= x t) must appear in phi
    rassert!(context
        .substitutions
        .iter()
        .all(|(k, v)| points.contains(&(k.clone(), v.clone()))));

    to_option(l_bindings == &r_bindings | &substitution_vars)
}

fn generic_skolemization_rule(
    rule_type: Quantifier,
    RuleArgs {
        conclusion,
        pool,
        context,
        subproof_commands,
        ..
    }: RuleArgs,
) -> Option<()> {
    rassert!(conclusion.len() == 1);

    let (left, psi) = match_term!((= l r) = conclusion[0])?;

    let (quant, bindings, phi) = left.unwrap_quant()?;
    rassert!(quant == rule_type);

    let previous_term =
        get_single_term_from_command(&subproof_commands?[subproof_commands?.len() - 2])?;
    let previous_equality = match_term!((= p q) = previous_term)?;
    rassert!(previous_equality == (phi, psi));

    let mut current_phi = phi.clone();
    // I have to extract the length into a separate variable (instead of just using it directly in
    // the slice index) to please the borrow checker
    let n = context.len();
    for c in &context[..n - 1] {
        // Based on the test examples, we must first apply all previous context substitutions to
        // phi, before applying the substitutions present in the current context
        current_phi = pool.apply_substitutions(&current_phi, &c.substitutions);
    }

    let substitutions = &context.last()?.substitutions_until_fixed_point;
    for (i, x) in bindings.iter().enumerate() {
        let x_term = pool.add_term(Term::from(x.clone()));
        let t = substitutions.get(&x_term)?;
        let (t_choice_var, t_bindings, t_inner) = match t.as_ref() {
            Term::Choice(var, inner) => {
                // If the rule is "sko_forall", the predicate in the choice term is negated
                let inner = if rule_type == Quantifier::Forall {
                    match_term!((not t) = inner, RETURN_RCS)?
                } else {
                    inner
                };
                // If this is the last binding, all bindings were skolemized, so we don't need to
                // unwrap any quantifier
                if i == bindings.len() - 1 {
                    (var, &[] as &[_], inner)
                } else {
                    let (q, b, t) = inner.unwrap_quant()?;
                    rassert!(q == rule_type);
                    (var, b.as_slice(), t)
                }
            }
            _ => return None,
        };
        rassert!(t_choice_var == x);
        rassert!(t_bindings == &bindings[i + 1..]);
        rassert!(DeepEq::eq_modulo_reordering(t_inner, &current_phi));

        // For every binding we skolemize, we must apply another substitution to phi
        let mut s = AHashMap::new();
        s.insert(x_term, t.clone());
        current_phi = pool.apply_substitutions(&current_phi, &s);
    }
    Some(())
}

pub fn sko_ex(args: RuleArgs) -> Option<()> {
    generic_skolemization_rule(Quantifier::Exists, args)
}

pub fn sko_forall(args: RuleArgs) -> Option<()> {
    generic_skolemization_rule(Quantifier::Forall, args)
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
                (declare-fun x () Int)
                (declare-fun y () Int)
                (declare-fun z () Int)
            ",
            "Simple working examples" {
                "(step t1 (cl (= i x)) :rule trust_me)
                (anchor :step t2 :args ((:= (a Int) x)))
                (step t2.t1 (cl (= p q)) :rule trust_me)
                (step t2 (cl (= (let ((a i)) p) q)) :rule let :premises (t1))": true,

                "(step t1 (cl (= i x)) :rule trust_me)
                (step t2 (cl (= k z)) :rule trust_me)
                (anchor :step t3 :args ((:= (a Int) x) (:= (b Int) y) (:= (c Int) z)))
                (step t3.t1 (cl (= p q)) :rule trust_me)
                (step t3 (cl (= (let ((a i) (b y) (c k)) p) q)) :rule let :premises (t1 t2))": true,
            }
            "Premise equalities may be flipped" {
                "(step t1 (cl (= x i)) :rule trust_me)
                (anchor :step t2 :args ((:= (a Int) x)))
                (step t2.t1 (cl (= p q)) :rule trust_me)
                (step t2 (cl (= (let ((a i)) p) q)) :rule let :premises (t1))": true,
            }
            "Wrong number of premises" {
                "(step t1 (cl (= i x)) :rule trust_me)
                (anchor :step t2 :args ((:= (a Int) x) (:= (b Int) y) (:= (c Int) z)))
                (step t2.t1 (cl (= p q)) :rule trust_me)
                (step t2 (cl (= (let ((a i) (b y) (c k)) p) q)) :rule let :premises (t1))": false,

                "(step t1 (cl (= i x)) :rule trust_me)
                (step t2 (cl (= y y)) :rule trust_me)
                (step t3 (cl (= k z)) :rule trust_me)
                (anchor :step t4 :args ((:= (a Int) x) (:= (b Int) y) (:= (c Int) z)))
                (step t4.t1 (cl (= p q)) :rule trust_me)
                (step t4 (cl (= (let ((a i) (b y) (c k)) p) q)) :rule let :premises (t1 t2))": false,
            }
            "Number of bindings is `let` term doesn't match number of substitutions in context" {
                "(step t1 (cl (= i x)) :rule trust_me)
                (step t2 (cl (= j y)) :rule trust_me)
                (anchor :step t3 :args ((:= (a Int) x) (:= (b Int) y) (:= (c Int) z)))
                (step t3.t1 (cl (= p q)) :rule trust_me)
                (step t3 (cl (= (let ((a i) (b j)) p) q)) :rule let :premises (t1 t2))": false,
            }
            "u and u' don't match equality in previous command" {
                "(step t1 (cl (= i x)) :rule trust_me)
                (anchor :step t2 :args ((:= (a Int) x)))
                (step t2.t1 (cl (= p (= i j))) :rule trust_me)
                (step t2 (cl (= (let ((a i)) p) q)) :rule let :premises (t1))": false,
            }
        }
    }

    #[test]
    fn onepoint() {
        test_cases! {
            definitions = "(declare-fun p () Bool)",
            "Simple working examples" {
                "(anchor :step t1 :args ((:= (x Int) t)))
                (step t1.t1 (cl (= (=> (= x t) p) (=> (= t t) p))) :rule trust_me)
                (step t1 (cl (= (forall ((x Int)) (=> (= x t) p)) (=> (= t t) p)))
                    :rule onepoint)": true,

                "(anchor :step t1 :args ((:= (x Int) t)))
                (step t1.t1 (cl (= (or (not (= x t)) p) (or (not (= t t)) p))) :rule trust_me)
                (step t1 (cl (= (forall ((x Int)) (or (not (= x t)) p)) (or (not (= t t)) p)))
                    :rule onepoint)": true,

                "(anchor :step t1 :args ((:= (x Int) t)))
                (step t1.t1 (cl (= (and (= x t) p) (and (= t t) p))) :rule trust_me)
                (step t1 (cl (= (exists ((x Int)) (and (= x t) p)) (and (= t t) p)))
                    :rule onepoint)": true,
            }
            "Multiple quantifier bindings" {
                "(anchor :step t1 :args ((x Int) (y Int) (:= (z Int) t)))
                (step t1.t1 (cl (= (=> (= z t) (= (+ x y) (+ z t)))
                                   (=> (= t t) (= (+ x y) (+ t t))))) :rule trust_me)
                (step t1 (cl (=
                    (forall ((x Int) (y Int) (z Int)) (=> (= z t) (= (+ x y) (+ z t))))
                    (forall ((x Int) (y Int))         (=> (= t t) (= (+ x y) (+ t t))))
                )) :rule onepoint)": true,

                "(anchor :step t1 :args ((x Int) (y Int) (:= (z Int) t)))
                (step t1.t1 (cl (= (and (= z t) (= (+ x y) (+ z t)))
                                   (and (= t t) (= (+ x y) (+ t t))))) :rule trust_me)
                (step t1 (cl (=
                    (exists ((x Int) (y Int) (z Int)) (and (= z t) (= (+ x y) (+ z t))))
                    (exists ((x Int) (y Int))         (and (= t t) (= (+ x y) (+ t t))))
                )) :rule onepoint)": true,
            }
            "Multiple quantifier bindings eliminated" {
                "(anchor :step t1 :args ((:= (x Int) t) (:= (y Int) u) (:= (z Int) v)))
                (step t1.t1 (cl (= (=> (= x t) (=> (= y u) (=> (= z v) p)))
                                   (=> (= t t) (=> (= u u) (=> (= v v) p))))) :rule trust_me)
                (step t1 (cl (=
                    (forall ((x Int) (y Int) (z Int)) (=> (= x t) (=> (= y u) (=> (= z v) p))))
                    (=> (= t t) (=> (= u u) (=> (= v v) p)))
                )) :rule onepoint)": true,

                "(anchor :step t1 :args ((:= (x Int) t) (:= (y Int) u) (:= (z Int) v)))
                (step t1.t1 (cl (= (or (not (= x t)) (or (not (= y u)) (or (not (= z v)) p)))
                                   (or (not (= t t)) (or (not (= u u)) (or (not (= v v)) p)))
                )) :rule trust_me)
                (step t1 (cl (=
                    (forall ((x Int) (y Int) (z Int))
                        (or (not (= x t)) (or (not (= y u)) (or (not (= z v)) p))))
                    (or (not (= t t)) (or (not (= u u)) (or (not (= v v)) p)))
                )) :rule onepoint)": true,

                "(anchor :step t1 :args ((:= (x Int) t) (:= (y Int) u) (:= (z Int) v)))
                (step t1.t1 (cl (= (=> (and (= x t) (and (= y u) (= z v))) p)
                                   (=> (and (= t t) (and (= u u) (= v v))) p))) :rule trust_me)
                (step t1 (cl (=
                    (forall ((x Int) (y Int) (z Int)) (=> (and (= x t) (and (= y u) (= z v))) p))
                    (=> (and (= t t) (and (= u u) (= v v))) p)
                )) :rule onepoint)": true,

                "(anchor :step t1 :args ((:= (x Int) t) (:= (y Int) u) (:= (z Int) v)))
                (step t1.t1 (cl (= (and (= x t) (and (= y u) (and (= z v) p)))
                                   (and (= t t) (and (= u u) (and (= v v) p))))) :rule trust_me)
                (step t1 (cl (=
                    (exists ((x Int) (y Int) (z Int)) (and (= x t) (and (= y u) (and (= z v) p))))
                    (and (= t t) (and (= u u) (and (= v v) p)))
                )) :rule onepoint)": true,
            }
        }
    }

    #[test]
    fn sko_ex() {
        test_cases! {
            definitions = "
                (declare-fun p (Int) Bool)
                (declare-fun q (Int) Bool)
            ",
            "Simple working examples" {
                "(anchor :step t1 :args ((:= (x Int) (choice ((x Int)) (p x)))))
                (step t1.t1 (cl (= (p x) (p (choice ((x Int)) (p x))))) :rule trust_me)
                (step t1 (cl (= (exists ((x Int)) (p x)) (p (choice ((x Int)) (p x)))))
                    :rule sko_ex)": true,

                "(anchor :step t1 :args (
                    (:= (x Int) (choice ((x Int)) (exists ((y Int)) (= x y))))
                    (:= (y Int)
                        (choice ((y Int)) (= (choice ((x Int)) (exists ((y Int)) (= x y))) y)))
                ))
                (step t1.t1 (cl (=
                    (= x y)
                    (= (choice ((x Int)) (exists ((y Int)) (= x y)))
                       (choice ((y Int)) (= (choice ((x Int)) (exists ((y Int)) (= x y))) y)))
                )) :rule trust_me)
                (step t1 (cl (=
                    (exists ((x Int) (y Int)) (= x y))
                    (= (choice ((x Int)) (exists ((y Int)) (= x y)))
                       (choice ((y Int)) (= (choice ((x Int)) (exists ((y Int)) (= x y))) y)))
                )) :rule sko_ex)": true,
            }
        }
    }

    #[test]
    fn sko_forall() {
        test_cases! {
            definitions = "
                (declare-fun p (Int) Bool)
                (declare-fun q (Int) Bool)
            ",
            "Simple working examples" {
                "(anchor :step t1 :args ((:= (x Int) (choice ((x Int)) (not (p x))))))
                (step t1.t1 (cl (= (p x) (p (choice ((x Int)) (not (p x)))))) :rule trust_me)
                (step t1 (cl (= (forall ((x Int)) (p x)) (p (choice ((x Int)) (not (p x))))))
                    :rule sko_forall)": true,

                "(anchor :step t1 :args (
                    (:= (x Int) (choice ((x Int)) (not (forall ((y Int)) (= x y)))))
                    (:= (y Int)
                        (choice ((y Int))
                            (not (= (choice ((x Int)) (not (forall ((y Int)) (= x y)))) y))))
                ))
                (step t1.t1 (cl (=
                    (= x y)
                    (= (choice ((x Int)) (not (forall ((y Int)) (= x y))))
                        (choice ((y Int))
                            (not (= (choice ((x Int)) (not (forall ((y Int)) (= x y)))) y))))
                )) :rule trust_me)
                (step t1 (cl (=
                    (forall ((x Int) (y Int)) (= x y))
                    (= (choice ((x Int)) (not (forall ((y Int)) (= x y))))
                        (choice ((y Int))
                            (not (= (choice ((x Int)) (not (forall ((y Int)) (= x y)))) y))))
                )) :rule sko_forall)": true,
            }
        }
    }
}
