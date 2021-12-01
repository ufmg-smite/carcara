use super::{
    assert_clause_len, assert_eq, assert_is_expected, assert_is_expected_modulo_reordering,
    assert_num_premises, assert_num_steps_in_subproof, get_clause_from_command, get_premise_term,
    CheckerError, EqualityError, RuleArgs, RuleResult,
};
use crate::{ast::*, checker::error::SubproofError};
use ahash::AHashSet;

pub fn subproof(
    RuleArgs {
        conclusion, pool, subproof_commands, ..
    }: RuleArgs,
) -> RuleResult {
    let subproof_commands = subproof_commands.ok_or(CheckerError::MustBeLastStepInSubproof)?;

    // TODO: We should get the series of assumptions from the ":discharge" attribute, but currently
    // we just take the first `conclusion.len() - 1` steps in the subproof.
    assert_clause_len(conclusion, 1..)?;
    let assumptions = &subproof_commands[..conclusion.len() - 1];

    assert_clause_len(conclusion, assumptions.len() + 1)?; // Currently, this is always true

    for (assumption, t) in assumptions.iter().zip(conclusion) {
        match assumption {
            ProofCommand::Assume { index: _, term } => {
                let t = t.remove_negation_err()?;
                assert_eq(term, t)?;
            }
            other => {
                return Err(SubproofError::DischargeMustBeAssume(other.index().to_string()).into())
            }
        }
    }

    let previous_command = &subproof_commands[subproof_commands.len() - 2];
    let phi = match get_clause_from_command(previous_command) {
        // If the last command has an empty clause as it's conclusion, we expect `phi` to be the
        // boolean constant `false`
        [] => pool.bool_false(),
        [t] => t.clone(),
        other => {
            return Err(CheckerError::WrongLengthOfPremiseClause(
                previous_command.index().to_string(),
                (..2).into(),
                other.len(),
            ))
        }
    };

    assert_eq(conclusion.last().unwrap(), &phi)
}

pub fn bind(
    RuleArgs {
        conclusion,
        pool,
        context,
        subproof_commands,
        ..
    }: RuleArgs,
) -> RuleResult {
    let subproof_commands = subproof_commands.ok_or(CheckerError::MustBeLastStepInSubproof)?;

    assert_clause_len(conclusion, 1)?;
    assert_num_steps_in_subproof(subproof_commands, 2..)?;

    // The last command in the subproof is the one we are currently checking, so we look at the one
    // before that
    let previous_command = &subproof_commands[subproof_commands.len() - 2];
    let (phi, phi_prime) = match_term_err!((= p q) = get_premise_term(previous_command)?)?;

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;

    // While the documentation indicates this rule is only called with "forall" quantifiers, in
    // some of the tests examples it is also called with the "exists" quantifier
    let (l_quant, l_bindings, left) = left.unwrap_quant_err()?;
    let (r_quant, r_bindings, right) = right.unwrap_quant_err()?;
    assert_eq(&l_quant, &r_quant)?;

    let l_bindings: AHashSet<_> = l_bindings.iter().map(|(var, _)| var.as_str()).collect();
    let r_bindings: AHashSet<_> = r_bindings.iter().map(|(var, _)| var.as_str()).collect();

    // The terms in the quantifiers must be phi and phi'
    assert_eq(left, phi)?;
    assert_eq(right, phi_prime)?;

    // None of the bindings in the right side can appear as free variables in phi
    let free_vars = pool.free_vars(phi);
    if let Some(y) = r_bindings
        .iter()
        .find(|&&y| free_vars.contains(y) && !l_bindings.contains(y))
    {
        return Err(SubproofError::BindBindingIsFreeVarInPhi(y.to_string()).into());
    }

    // Since we are closing a subproof, we only care about the substitutions that were introduced
    // in it
    let context = context.last().unwrap();

    // The quantifier binders must be the xs and ys of the context substitution
    let (xs, ys): (AHashSet<_>, AHashSet<_>) = context
        .substitution
        .map
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

    rassert!(
        l_bindings.len() == r_bindings.len(),
        SubproofError::BindDifferentNumberOfBindings(l_bindings.len(), r_bindings.len())
    );

    // `l_bindings` should be a subset of `xs` and `r_bindigns` should be a subset of `ys`
    if let Some(x) = l_bindings.iter().find(|&&x| !xs.contains(x)) {
        return Err(SubproofError::BindingIsNotInContext(x.to_string()).into());
    }
    if let Some(y) = r_bindings.iter().find(|&&y| !ys.contains(y)) {
        return Err(SubproofError::BindingIsNotInContext(y.to_string()).into());
    }
    Ok(())
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
) -> RuleResult {
    let subproof_commands = subproof_commands.ok_or(CheckerError::MustBeLastStepInSubproof)?;

    assert_clause_len(conclusion, 1)?;

    // Since we are closing a subproof, we only care about the substitutions that were introduced
    // in it
    let substitution = &context.last().unwrap().substitution;

    let (let_term, u_prime) = match_term_err!((= l u) = &conclusion[0])?;
    let (let_bindings, u) = match let_term.as_ref() {
        Term::Let(b, t) => (b, t),
        _ => return Err(CheckerError::TermOfWrongForm("(let ...)", let_term.clone())),
    };

    // The u and u' in the conclusion must match the u and u' in the previous command in the
    // subproof
    let previous_term = get_premise_term(&subproof_commands[subproof_commands.len() - 2])?;

    let (previous_u, previous_u_prime) = match_term_err!((= u u_prime) = previous_term)?;
    assert_eq(u, previous_u)?;
    assert_eq(u_prime, previous_u_prime)?;

    rassert!(
        let_bindings.len() == substitution.map.len(),
        SubproofError::WrongNumberOfLetBindings(substitution.map.len(), let_bindings.len())
    );

    let mut pairs: Vec<_> = let_bindings
        .iter()
        .map(|(x, t)| {
            let sort = pool.add_term(Term::Sort(t.sort().clone()));
            let x_term = pool.add_term((x.clone(), sort).into());
            let s = substitution
                .map
                .get(&x_term)
                .ok_or_else(|| SubproofError::BindingIsNotInContext(x.clone()))?;
            Ok((s, t))
        })
        .collect::<Result<_, CheckerError>>()?;
    pairs.retain(|(s, t)| s != t); // The pairs where s == t don't need a premise to justify them

    assert_num_premises(&premises, pairs.len())?;

    for (premise, (s, t)) in premises.iter().zip(pairs) {
        let (a, b) = match_term_err!((= a b) = get_premise_term(premise)?)?;
        rassert!(
            (a, b) == (s, t) || (a, b) == (t, s),
            SubproofError::PremiseDoesntJustifyLet {
                substitution: (s.clone(), t.clone()),
                premise: (a.clone(), b.clone()),
            }
        );
    }
    Ok(())
}

fn extract_points(quant: Quantifier, term: &Rc<Term>) -> AHashSet<(Rc<Term>, Rc<Term>)> {
    fn find_points(acc: &mut AHashSet<(Rc<Term>, Rc<Term>)>, polarity: bool, term: &Rc<Term>) {
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
                if let Some((x, t)) = match_term!((= x t) = term) {
                    acc.insert((x.clone(), t.clone()));
                } else if let Some(args) = match_term!((and ...) = term) {
                    for a in args {
                        find_points(acc, true, a)
                    }
                }
            }
            false => {
                if let Some((p, q)) = match_term!((=> p q) = term) {
                    find_points(acc, true, p);
                    find_points(acc, false, q);
                } else if let Some(args) = match_term!((or ...) = term) {
                    for a in args {
                        find_points(acc, false, a)
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
) -> RuleResult {
    let subproof_commands = subproof_commands.ok_or(CheckerError::MustBeLastStepInSubproof)?;

    assert_clause_len(conclusion, 1)?;

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;
    let (quant, l_bindings, left) = left.unwrap_quant_err()?;
    let (r_bindings, right) = match right.unwrap_quant() {
        Some((q, b, t)) => {
            assert_eq(&q, &quant)?;
            (b, t)
        }
        // If the right-hand side term is not a quantifier, that possibly means all quantifier
        // bindings were removed, so we consider it a quantifier with an empty list of bindings
        None => (BindingList::EMPTY, right),
    };

    let previous_term = get_premise_term(&subproof_commands[subproof_commands.len() - 2])?;
    let previous_equality = match_term_err!((= p q) = previous_term)?;
    rassert!(
        previous_equality == (left, right) || previous_equality == (right, left),
        EqualityError::ExpectedToBe {
            expected: previous_term.clone(),
            got: conclusion[0].clone()
        }
    );

    let context = context.last_mut().unwrap();

    if let Some((var, _)) = r_bindings.iter().find(|b| !context.bindings.contains(b)) {
        return Err(SubproofError::BindingIsNotInContext(var.clone()).into());
    }

    let l_bindings_set: AHashSet<_> = l_bindings
        .iter()
        .map(|var| pool.add_term(var.clone().into()))
        .collect();
    let r_bindings_set: AHashSet<_> = r_bindings
        .iter()
        .map(|var| pool.add_term(var.clone().into()))
        .collect();
    let substitution_vars: AHashSet<_> = context
        .substitution
        .map
        .iter()
        .map(|(k, _)| k.clone())
        .collect();

    let points = extract_points(quant, left);

    // Since a substitution may use a varibale introduced in a previous substitution, we apply the
    // substitution to the points in order to replace these variables by their value. We also
    // create a duplicate of every point in the reverse order, since the order of equalities may be
    // flipped
    let points: AHashSet<_> = points
        .into_iter()
        .flat_map(|(x, t)| [(x.clone(), t.clone()), (t, x)])
        .map(|(x, t)| {
            let new_t = context.substitution_until_fixed_point.apply(pool, &t)?;
            Ok((x, new_t))
        })
        .collect::<Result<_, CheckerError>>()?;

    // For each substitution (:= x t) in the context, the equality (= x t) must appear in phi
    if let Some((k, v)) = context
        .substitution
        .map
        .iter()
        .find(|&(k, v)| !points.contains(&(k.clone(), v.clone())))
    {
        return Err(SubproofError::NoPointForSubstitution(k.clone(), v.clone()).into());
    }

    rassert!(l_bindings_set == &r_bindings_set | &substitution_vars, {
        let expected: Vec<_> = l_bindings
            .iter()
            .filter(|&v| {
                let t: Term = v.clone().into();
                !context.substitution.map.contains_key(&pool.add_term(t))
            })
            .cloned()
            .collect();
        SubproofError::OnePointWrongBindings(BindingList(expected))
    });
    Ok(())
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
) -> RuleResult {
    let subproof_commands = subproof_commands.ok_or(CheckerError::MustBeLastStepInSubproof)?;

    assert_clause_len(conclusion, 1)?;

    let (left, psi) = match_term_err!((= l r) = &conclusion[0])?;

    let (quant, bindings, phi) = left.unwrap_quant_err()?;
    assert_is_expected(&quant, rule_type)?;

    let previous_term = get_premise_term(&subproof_commands[subproof_commands.len() - 2])?;
    let previous_equality = match_term_err!((= p q) = previous_term)?;
    assert_eq(previous_equality.0, phi)?;
    assert_eq(previous_equality.1, psi)?;

    let mut current_phi = phi.clone();
    // I have to extract the length into a separate variable (instead of just using it directly in
    // the slice index) to please the borrow checker
    let n = context.len();
    for c in &mut context[..n - 1] {
        // Based on the test examples, we must first apply all previous context substitutions to
        // phi, before applying the substitution present in the current context
        current_phi = c.substitution.apply(pool, &current_phi)?;
    }

    let substitution = &context.last().unwrap().substitution_until_fixed_point;
    for (i, x) in bindings.iter().enumerate() {
        let x_term = pool.add_term(Term::from(x.clone()));
        let t = substitution
            .map
            .get(&x_term)
            .ok_or_else(|| SubproofError::BindingIsNotInContext(x.0.clone()))?;

        // To check that `t` is of the correct form, we construct the expected term and compare
        // them
        let expected = {
            let mut inner = current_phi.clone();

            // If this is the last binding, all bindings were skolemized, so we don't need to wrap
            // the term in a quantifier
            if i < bindings.len() - 1 {
                inner = pool.add_term(Term::Quant(
                    rule_type,
                    BindingList(bindings.0[i + 1..].to_vec()),
                    inner,
                ))
            }

            // If the rule is "sko_forall", the predicate in the choice term should be negated
            if rule_type == Quantifier::Forall {
                inner = build_term!(pool, (not { inner }));
            }
            pool.add_term(Term::Choice(x.clone(), inner))
        };
        assert_is_expected_modulo_reordering(t, expected)?;

        // For every binding we skolemize, we must apply another substitution to phi
        let mut s = Substitution::single(pool, x_term, t.clone())?;
        current_phi = s.apply(pool, &current_phi)?;
    }
    Ok(())
}

pub fn sko_ex(args: RuleArgs) -> RuleResult {
    generic_skolemization_rule(Quantifier::Exists, args)
}

pub fn sko_forall(args: RuleArgs) -> RuleResult {
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
                (step t1.t2 (cl q) :rule trust)
                (step t1 (cl (not p) q) :rule subproof)": true,

                "(anchor :step t1)
                (assume t1.h1 p)
                (assume t1.h2 q)
                (step t1.t3 (cl (= r s)) :rule trust)
                (step t1 (cl (not p) (not q) (= r s)) :rule subproof)": true,
            }
            "Missing assumption" {
                "(anchor :step t1)
                (assume t1.h1 p)
                (step t1.t2 (cl (= r s)) :rule trust)
                (step t1 (cl (not p) (not q) (= r s)) :rule subproof)": false,
            }
            "Assumption terms don't match" {
                "(anchor :step t1)
                (assume t1.h1 p)
                (assume t1.h2 q)
                (step t1.t3 (cl (= r s)) :rule trust)
                (step t1 (cl (not q) (not p) (= r s)) :rule subproof)": false,

                "(anchor :step t1)
                (assume t1.h1 (or p q))
                (assume t1.h2 (= p q))
                (step t1.t3 (cl (= r s)) :rule trust)
                (step t1 (cl (not (and p q)) (not (= q p)) (= r s)) :rule subproof)": false,
            }
            "Conclusion terms don't match" {
                "(anchor :step t1)
                (assume t1.h1 p)
                (assume t1.h2 q)
                (step t1.t3 (cl (= r s)) :rule trust)
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
                (step t1.t1 (cl (= p q)) :rule trust)
                (step t1 (cl (= (forall ((x Real)) p) (forall ((y Real)) q))) :rule bind)": true,

                "(anchor :step t1 :args ((:= (x1 Real) y1) (:= (x2 Real) y2)))
                (step t1.t1 (cl (= (= x1 x2) (= y1 y2))) :rule trust)
                (step t1 (cl (= (forall ((x1 Real) (x2 Real)) (= x1 x2))
                    (forall ((y1 Real) (y2 Real)) (= y1 y2)))) :rule bind)": true,
            }
            "Examples with binding arguments" {
                "(anchor :step t1 :args ((z Real) (:= (x Real) y)))
                (step t1.t1 (cl (= p q)) :rule trust)
                (step t1 (cl (= (forall ((x Real) (z Real)) p)
                    (forall ((y Real) (z Real)) q))) :rule bind)": true,
            }
            "y_i appears in phi as a free variable" {
                "(anchor :step t1 :args ((:= (x Real) y)))
                (step t1.t1 (cl (= (= y x) (= y y))) :rule trust)
                (step t1 (cl (= (forall ((x Real)) (= y x))
                    (forall ((y Real)) (= y y)))) :rule bind)": false,

                "(anchor :step t1 :args ((z Real) (:= (x Real) y)))
                (step t1.t1 (cl (= (= y x) (= y y))) :rule trust)
                (step t1 (cl (= (forall ((z Real) (x Real)) (= y z))
                    (forall ((z Real) (y Real)) (= y z)))) :rule bind)": false,
            }
            "Terms in conclusion clause don't match terms in previous command" {
                "(anchor :step t1 :args ((:= (x Real) y)))
                (step t1.t1 (cl (= p q)) :rule trust)
                (step t1.t2 (cl (= r s)) :rule trust) ; This step shouldn't be here!
                (step t1 (cl (= (forall ((x Real)) p) (forall ((y Real)) q))) :rule bind)": false,

                "(anchor :step t1 :args ((:= (x Real) y)))
                (step t1.t1 (cl (= p q)) :rule trust)
                (step t1 (cl (= (forall ((x Real)) q) (forall ((y Real)) p))) :rule bind)": false,
            }
            "Context substitutions don't match quantifier bindings" {
                "(anchor :step t1 :args ((:= (x Real) y)))
                (step t1.t1 (cl (= p q)) :rule trust)
                (step t1 (cl (= (forall ((y Real)) p) (forall ((x Real)) q))) :rule bind)": false,

                "(anchor :step t1 :args ((:= (x1 Real) y1) (:= (x2 Real) y2)))
                (step t1.t1 (cl (= (= x1 x2) (= y1 y2))) :rule trust)
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
                "(step t1 (cl (= i x)) :rule trust)
                (anchor :step t2 :args ((:= (a Int) x)))
                (step t2.t1 (cl (= p q)) :rule trust)
                (step t2 (cl (= (let ((a i)) p) q)) :rule let :premises (t1))": true,

                "(step t1 (cl (= i x)) :rule trust)
                (step t2 (cl (= k z)) :rule trust)
                (anchor :step t3 :args ((:= (a Int) x) (:= (b Int) y) (:= (c Int) z)))
                (step t3.t1 (cl (= p q)) :rule trust)
                (step t3 (cl (= (let ((a i) (b y) (c k)) p) q)) :rule let :premises (t1 t2))": true,
            }
            "Premise equalities may be flipped" {
                "(step t1 (cl (= x i)) :rule trust)
                (anchor :step t2 :args ((:= (a Int) x)))
                (step t2.t1 (cl (= p q)) :rule trust)
                (step t2 (cl (= (let ((a i)) p) q)) :rule let :premises (t1))": true,
            }
            "Wrong number of premises" {
                "(step t1 (cl (= i x)) :rule trust)
                (anchor :step t2 :args ((:= (a Int) x) (:= (b Int) y) (:= (c Int) z)))
                (step t2.t1 (cl (= p q)) :rule trust)
                (step t2 (cl (= (let ((a i) (b y) (c k)) p) q)) :rule let :premises (t1))": false,

                "(step t1 (cl (= i x)) :rule trust)
                (step t2 (cl (= y y)) :rule trust)
                (step t3 (cl (= k z)) :rule trust)
                (anchor :step t4 :args ((:= (a Int) x) (:= (b Int) y) (:= (c Int) z)))
                (step t4.t1 (cl (= p q)) :rule trust)
                (step t4 (cl (= (let ((a i) (b y) (c k)) p) q)) :rule let :premises (t1 t2))": false,
            }
            "Number of bindings is `let` term doesn't match number of substitutions in context" {
                "(step t1 (cl (= i x)) :rule trust)
                (step t2 (cl (= j y)) :rule trust)
                (anchor :step t3 :args ((:= (a Int) x) (:= (b Int) y) (:= (c Int) z)))
                (step t3.t1 (cl (= p q)) :rule trust)
                (step t3 (cl (= (let ((a i) (b j)) p) q)) :rule let :premises (t1 t2))": false,
            }
            "u and u' don't match equality in previous command" {
                "(step t1 (cl (= i x)) :rule trust)
                (anchor :step t2 :args ((:= (a Int) x)))
                (step t2.t1 (cl (= p (= i j))) :rule trust)
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
                (step t1.t1 (cl (= (=> (= x t) p) (=> (= t t) p))) :rule trust)
                (step t1 (cl (= (forall ((x Int)) (=> (= x t) p)) (=> (= t t) p)))
                    :rule onepoint)": true,

                "(anchor :step t1 :args ((:= (x Int) t)))
                (step t1.t1 (cl (= (or (not (= x t)) p) (or (not (= t t)) p))) :rule trust)
                (step t1 (cl (= (forall ((x Int)) (or (not (= x t)) p)) (or (not (= t t)) p)))
                    :rule onepoint)": true,

                "(anchor :step t1 :args ((:= (x Int) t)))
                (step t1.t1 (cl (= (and (= x t) p) (and (= t t) p))) :rule trust)
                (step t1 (cl (= (exists ((x Int)) (and (= x t) p)) (and (= t t) p)))
                    :rule onepoint)": true,
            }
            "Multiple quantifier bindings" {
                "(anchor :step t1 :args ((x Int) (y Int) (:= (z Int) t)))
                (step t1.t1 (cl (= (=> (= z t) (= (+ x y) (+ z t)))
                                   (=> (= t t) (= (+ x y) (+ t t))))) :rule trust)
                (step t1 (cl (=
                    (forall ((x Int) (y Int) (z Int)) (=> (= z t) (= (+ x y) (+ z t))))
                    (forall ((x Int) (y Int))         (=> (= t t) (= (+ x y) (+ t t))))
                )) :rule onepoint)": true,

                "(anchor :step t1 :args ((x Int) (y Int) (:= (z Int) t)))
                (step t1.t1 (cl (= (and (= z t) (= (+ x y) (+ z t)))
                                   (and (= t t) (= (+ x y) (+ t t))))) :rule trust)
                (step t1 (cl (=
                    (exists ((x Int) (y Int) (z Int)) (and (= z t) (= (+ x y) (+ z t))))
                    (exists ((x Int) (y Int))         (and (= t t) (= (+ x y) (+ t t))))
                )) :rule onepoint)": true,
            }
            "Multiple quantifier bindings eliminated" {
                "(anchor :step t1 :args ((:= (x Int) t) (:= (y Int) u) (:= (z Int) v)))
                (step t1.t1 (cl (= (=> (= x t) (=> (= y u) (=> (= z v) p)))
                                   (=> (= t t) (=> (= u u) (=> (= v v) p))))) :rule trust)
                (step t1 (cl (=
                    (forall ((x Int) (y Int) (z Int)) (=> (= x t) (=> (= y u) (=> (= z v) p))))
                    (=> (= t t) (=> (= u u) (=> (= v v) p)))
                )) :rule onepoint)": true,

                "(anchor :step t1 :args ((:= (x Int) t) (:= (y Int) u) (:= (z Int) v)))
                (step t1.t1 (cl (= (or (not (= x t)) (or (not (= y u)) (or (not (= z v)) p)))
                                   (or (not (= t t)) (or (not (= u u)) (or (not (= v v)) p)))
                )) :rule trust)
                (step t1 (cl (=
                    (forall ((x Int) (y Int) (z Int))
                        (or (not (= x t)) (or (not (= y u)) (or (not (= z v)) p))))
                    (or (not (= t t)) (or (not (= u u)) (or (not (= v v)) p)))
                )) :rule onepoint)": true,

                "(anchor :step t1 :args ((:= (x Int) t) (:= (y Int) u) (:= (z Int) v)))
                (step t1.t1 (cl (= (=> (and (= x t) (and (= y u) (= z v))) p)
                                   (=> (and (= t t) (and (= u u) (= v v))) p))) :rule trust)
                (step t1 (cl (=
                    (forall ((x Int) (y Int) (z Int)) (=> (and (= x t) (and (= y u) (= z v))) p))
                    (=> (and (= t t) (and (= u u) (= v v))) p)
                )) :rule onepoint)": true,

                "(anchor :step t1 :args ((:= (x Int) t) (:= (y Int) u) (:= (z Int) v)))
                (step t1.t1 (cl (= (and (= x t) (and (= y u) (and (= z v) p)))
                                   (and (= t t) (and (= u u) (and (= v v) p))))) :rule trust)
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
                (step t1.t1 (cl (= (p x) (p (choice ((x Int)) (p x))))) :rule trust)
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
                )) :rule trust)
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
                (step t1.t1 (cl (= (p x) (p (choice ((x Int)) (not (p x)))))) :rule trust)
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
                )) :rule trust)
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
