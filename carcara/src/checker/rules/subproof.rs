use super::{
    assert_clause_len, assert_eq, assert_is_expected, assert_num_premises, get_premise_term,
    CheckerError, EqualityError, RuleArgs, RuleResult,
};
use crate::{ast::*, checker::error::SubproofError};
use indexmap::{IndexMap, IndexSet};

pub fn subproof(
    RuleArgs {
        conclusion,
        pool,
        previous_command,
        discharge,
        ..
    }: RuleArgs,
) -> RuleResult {
    let previous_command = previous_command.ok_or(CheckerError::MustBeLastStepInSubproof)?;

    assert_clause_len(conclusion, discharge.len() + 1)?;

    for (assumption, t) in discharge.iter().zip(conclusion) {
        match assumption {
            ProofCommand::Assume { id: _, term } => {
                let t = t.remove_negation_err()?;
                assert_eq(term, t)?;
            }
            other => return Err(SubproofError::DischargeMustBeAssume(other.id().to_owned()).into()),
        }
    }

    let phi = match previous_command.clause {
        // If the last command has an empty clause as it's conclusion, we expect `phi` to be the
        // boolean constant `false`
        [] => pool.bool_false(),
        [t] => t.clone(),
        other => {
            return Err(CheckerError::WrongLengthOfPremiseClause(
                previous_command.id.to_owned(),
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
        previous_command,
        ..
    }: RuleArgs,
) -> RuleResult {
    let previous_command = previous_command.ok_or(CheckerError::MustBeLastStepInSubproof)?;

    assert_clause_len(conclusion, 1)?;

    let (phi, phi_prime) = match_term_err!((= p q) = get_premise_term(&previous_command)?)?;

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;

    // While the documentation indicates this rule is only called with `forall` quantifiers, in
    // some of the tests examples it is also called with the `exists` quantifier
    let (l_quant, l_bindings, left) = left.as_quant_err()?;
    let (r_quant, r_bindings, right) = right.as_quant_err()?;
    assert_eq(&l_quant, &r_quant)?;

    let [l_bindings, r_bindings] = [l_bindings, r_bindings].map(|b| {
        b.iter()
            .map(|var| pool.add(var.clone().into()))
            .collect::<IndexSet<_>>()
    });

    // The terms in the quantifiers must be phi and phi'
    assert_eq(left, phi)?;
    assert_eq(right, phi_prime)?;

    // None of the bindings in the right side can appear as free variables in phi
    let free_vars = pool.free_vars(phi);
    if let Some(y) = r_bindings
        .iter()
        .find(|&y| free_vars.contains(y) && !l_bindings.contains(y))
    {
        let y = y.as_var().unwrap().to_owned();
        return Err(SubproofError::BindBindingIsFreeVarInPhi(y).into());
    }

    // Since we are closing a subproof, we only care about the substitutions that were introduced
    // in it
    let context = context.last().unwrap();
    let context = context.as_ref().unwrap();

    // The quantifier binders must be the xs and ys of the context substitution
    let (xs, ys): (IndexSet<_>, IndexSet<_>) = context
        .mappings
        .iter()
        // We skip terms which are not simply variables
        .filter(|&(x, y)| x.is_var() && y.is_var())
        .map(|(x, y)| (x.clone(), y.clone()))
        .chain(
            // Sometimes, the context bindings also appear as bindings in the quantifiers, so we
            // include them in the `xs` and `ys`
            context.bindings.iter().map(|var| {
                let term = pool.add(var.clone().into());
                (term.clone(), term)
            }),
        )
        .unzip();

    rassert!(
        l_bindings.len() == r_bindings.len(),
        SubproofError::BindDifferentNumberOfBindings(l_bindings.len(), r_bindings.len())
    );

    // `l_bindings` should be a subset of `xs` and `r_bindigns` should be a subset of `ys`
    if let Some(x) = l_bindings.iter().find(|&x| !xs.contains(x)) {
        let x = x.as_var().unwrap().to_owned();
        return Err(SubproofError::BindingIsNotInContext(x).into());
    }
    if let Some(y) = r_bindings.iter().find(|&y| !ys.contains(y)) {
        let y = y.as_var().unwrap().to_owned();
        return Err(SubproofError::BindingIsNotInContext(y).into());
    }
    Ok(())
}

pub fn r#let(
    RuleArgs {
        conclusion,
        context,
        premises,
        pool,
        previous_command,
        ..
    }: RuleArgs,
) -> RuleResult {
    let previous_command = previous_command.ok_or(CheckerError::MustBeLastStepInSubproof)?;

    assert_clause_len(conclusion, 1)?;

    // Since we are closing a subproof, we only care about the substitutions that were introduced
    // in it
    let substitution: IndexMap<Rc<Term>, Rc<Term>> = context
        .last()
        .unwrap()
        .as_ref()
        .unwrap()
        .mappings
        .iter()
        .cloned()
        .collect();

    let (let_term, u_prime) = match_term_err!((= l u) = &conclusion[0])?;
    let Term::Let(let_bindings, u) = let_term.as_ref() else {
        return Err(CheckerError::TermOfWrongForm("(let ...)", let_term.clone()));
    };

    // The u and u' in the conclusion must match the u and u' in the previous command in the
    // subproof
    let previous_term = get_premise_term(&previous_command)?;

    let (previous_u, previous_u_prime) = match_term_err!((= u u_prime) = previous_term)?;
    assert_eq(u, previous_u)?;
    assert_eq(u_prime, previous_u_prime)?;

    rassert!(
        let_bindings.len() == substitution.len(),
        SubproofError::WrongNumberOfLetBindings(substitution.len(), let_bindings.len())
    );

    let mut pairs: Vec<_> = let_bindings
        .iter()
        .map(|(x, t)| {
            let sort = pool.sort(t);
            let x_term = pool.add((x.clone(), sort).into());
            let s = substitution
                .get(&x_term)
                .ok_or_else(|| SubproofError::BindingIsNotInContext(x.clone()))?;
            Ok((s, t))
        })
        .collect::<Result<_, CheckerError>>()?;
    pairs.retain(|(s, t)| s != t); // The pairs where s == t don't need a premise to justify them

    assert_num_premises(premises, pairs.len())?;

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

fn extract_points(quant: Quantifier, term: &Rc<Term>) -> IndexSet<(Rc<Term>, Rc<Term>)> {
    fn find_points(acc: &mut IndexSet<(Rc<Term>, Rc<Term>)>, polarity: bool, term: &Rc<Term>) {
        // This does not make use of a cache, so there may be performance issues
        // TODO: Measure the performance of this function, and see if a cache is needed

        if let Some(inner) = term.remove_negation() {
            return find_points(acc, !polarity, inner);
        }
        if let Some((_, _, inner)) = term.as_quant() {
            return find_points(acc, polarity, inner);
        }
        match polarity {
            true => {
                if let Some((x, t)) = match_term!((= x t) = term) {
                    acc.insert((x.clone(), t.clone()));
                } else if let Some(args) = match_term!((and ...) = term) {
                    for a in args {
                        find_points(acc, true, a);
                    }
                }
            }
            false => {
                if let Some((p, q)) = match_term!((=> p q) = term) {
                    find_points(acc, true, p);
                    find_points(acc, false, q);
                } else if let Some(args) = match_term!((or ...) = term) {
                    for a in args {
                        find_points(acc, false, a);
                    }
                }
            }
        }
    }

    let mut result = IndexSet::new();
    find_points(&mut result, quant == Quantifier::Exists, term);
    result
}

pub fn onepoint(
    RuleArgs {
        conclusion,
        context,
        pool,
        previous_command,
        ..
    }: RuleArgs,
) -> RuleResult {
    let previous_command = previous_command.ok_or(CheckerError::MustBeLastStepInSubproof)?;

    assert_clause_len(conclusion, 1)?;

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;
    let (quant, l_bindings, left) = left.as_quant_err()?;
    let (r_bindings, right) = match right.as_quant() {
        Some((q, b, t)) => {
            assert_eq(&q, &quant)?;
            (b, t)
        }
        // If the right-hand side term is not a quantifier, that possibly means all quantifier
        // bindings were removed, so we consider it a quantifier with an empty list of bindings
        None => (BindingList::EMPTY, right),
    };

    let previous_term = get_premise_term(&previous_command)?;
    let previous_equality = match_term_err!((= p q) = previous_term)?;
    rassert!(
        previous_equality == (left, right) || previous_equality == (right, left),
        EqualityError::ExpectedToBe {
            expected: previous_term.clone(),
            got: conclusion[0].clone()
        }
    );

    let last_context = context.last().unwrap();
    if let Some((var, _)) = {
        let last_context = last_context.as_ref().unwrap();
        r_bindings
            .iter()
            .find(|&b| !last_context.bindings.contains(b))
    } {
        return Err(SubproofError::BindingIsNotInContext(var.clone()).into());
    }

    let l_bindings_set: IndexSet<_> = l_bindings
        .iter()
        .map(|var| pool.add(var.clone().into()))
        .collect();
    let r_bindings_set: IndexSet<_> = r_bindings
        .iter()
        .map(|var| pool.add(var.clone().into()))
        .collect();
    let substitution_vars: IndexSet<_> = last_context
        .as_ref()
        .unwrap()
        .mappings
        .iter()
        .map(|(k, _)| k.clone())
        .collect();
    drop(last_context);

    let points = extract_points(quant, left);

    // Since a substitution may use a variable introduced in a previous substitution, we apply the
    // substitution to the points in order to replace these variables by their value. We also
    // create a duplicate of every point in the reverse order, since the order of equalities may be
    // flipped
    let points: IndexSet<_> = points
        .into_iter()
        .flat_map(|(x, t)| [(x.clone(), t.clone()), (t, x)])
        .map(|(x, t)| (x, context.apply(pool, &t)))
        .collect();

    let last_context = context.last().unwrap();
    let last_context = last_context.as_ref().unwrap();
    // For each substitution (:= x t) in the context, the equality (= x t) must appear in phi
    if let Some((k, v)) = last_context
        .mappings
        .iter()
        .find(|(k, v)| !points.contains(&(k.clone(), v.clone())))
    {
        return Err(SubproofError::NoPointForSubstitution(k.clone(), v.clone()).into());
    }

    rassert!(l_bindings_set == &r_bindings_set | &substitution_vars, {
        let expected: Vec<_> = l_bindings
            .iter()
            .filter(|&v| {
                let t = pool.add(v.clone().into());
                !last_context.mappings.iter().any(|(k, _)| *k == t)
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
        previous_command,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    let previous_command = previous_command.ok_or(CheckerError::MustBeLastStepInSubproof)?;

    assert_clause_len(conclusion, 1)?;

    let (left, psi) = match_term_err!((= l r) = &conclusion[0])?;

    let (quant, bindings, phi) = left.as_quant_err()?;
    assert_is_expected(&quant, rule_type)?;

    let previous_term = get_premise_term(&previous_command)?;
    let previous_equality = match_term_err!((= p q) = previous_term)?;
    assert_eq(previous_equality.0, phi)?;
    assert_eq(previous_equality.1, psi)?;

    let mut current_phi = phi.clone();
    if context.len() >= 2 {
        current_phi = context.apply_previous(pool, &current_phi);
    }

    let substitution: IndexMap<Rc<Term>, Rc<Term>> = context
        .last()
        .unwrap()
        .as_ref()
        .unwrap()
        .mappings
        .iter()
        .cloned()
        .collect();
    for (i, x) in bindings.iter().enumerate() {
        let x_term = pool.add(Term::from(x.clone()));
        let t = substitution
            .get(&x_term)
            .ok_or_else(|| SubproofError::BindingIsNotInContext(x.0.clone()))?;

        // To check that `t` is of the correct form, we construct the expected term and compare
        // them
        let expected = {
            let mut inner = current_phi.clone();

            // If this is the last binding, all bindings were skolemized, so we don't need to wrap
            // the term in a quantifier
            if i < bindings.len() - 1 {
                inner = pool.add(Term::Quant(
                    rule_type,
                    BindingList(bindings.0[i + 1..].to_vec()),
                    inner,
                ));
            }

            // If the rule is `sko_forall`, the predicate in the choice term should be negated
            if rule_type == Quantifier::Forall {
                inner = build_term!(pool, (not { inner }));
            }
            pool.add(Term::Choice(x.clone(), inner))
        };
        if !alpha_equiv(t, &expected, polyeq_time) {
            return Err(EqualityError::ExpectedEqual(t.clone(), expected).into());
        }

        // For every binding we skolemize, we must apply another substitution to phi
        let mut s = Substitution::single(pool, x_term, t.clone())?;
        current_phi = s.apply(pool, &current_phi);
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
                (step t1.t2 (cl q) :rule hole)
                (step t1 (cl (not p) q) :rule subproof :discharge (t1.h1))": true,

                "(anchor :step t1)
                (assume t1.h1 p)
                (step t1.t2 (cl) :rule hole)
                (assume t1.h3 q)
                (step t1.t4 (cl (= r s)) :rule hole)
                (step t1 (cl (not p) (not q) (= r s))
                    :rule subproof :discharge (t1.h1 t1.h3))": true,
            }
            "Missing assumption" {
                "(anchor :step t1)
                (assume t1.h1 p)
                (step t1.t2 (cl (= r s)) :rule hole)
                (step t1 (cl (not p) (not q) (= r s)) :rule subproof :discharge (t1.h1))": false,
            }
            "Assumption terms don't match" {
                "(anchor :step t1)
                (assume t1.h1 p)
                (assume t1.h2 q)
                (step t1.t3 (cl (= r s)) :rule hole)
                (step t1 (cl (not q) (not p) (= r s))
                    :rule subproof :discharge (t1.h1 t1.h2))": false,

                "(anchor :step t1)
                (assume t1.h1 (or p q))
                (assume t1.h2 (= p q))
                (step t1.t3 (cl (= r s)) :rule hole)
                (step t1 (cl (not (and p q)) (not (= q p)) (= r s))
                    :rule subproof :discharge (t1.h1 t1.h2))": false,
            }
            "Conclusion terms don't match" {
                "(anchor :step t1)
                (assume t1.h1 p)
                (assume t1.h2 q)
                (step t1.t3 (cl (= r s)) :rule hole)
                (step t1 (cl (not p) (not q) (= s r))
                    :rule subproof :discharge (t1.h1 t1.h2))": false,
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
                "(anchor :step t1 :args ((y Real) (:= x y)))
                (step t1.t1 (cl (= p q)) :rule hole)
                (step t1 (cl (= (forall ((x Real)) p) (forall ((y Real)) q))) :rule bind)": true,

                "(anchor :step t1 :args ((y1 Real) (y2 Real) (:= x1 y1) (:= x2 y2)))
                (step t1.t1 (cl (= (= x1 x2) (= y1 y2))) :rule hole)
                (step t1 (cl (= (forall ((x1 Real) (x2 Real)) (= x1 x2))
                    (forall ((y1 Real) (y2 Real)) (= y1 y2)))) :rule bind)": true,
            }
            "Examples with binding arguments" {
                "(anchor :step t1 :args ((y Real) (z Real) (:= x y)))
                (step t1.t1 (cl (= p q)) :rule hole)
                (step t1 (cl (= (forall ((x Real) (z Real)) p)
                    (forall ((y Real) (z Real)) q))) :rule bind)": true,
            }
            "y_i appears in phi as a free variable" {
                "(anchor :step t1 :args ((y Real) (:= x y)))
                (step t1.t1 (cl (= (= y x) (= y y))) :rule hole)
                (step t1 (cl (= (forall ((x Real)) (= y x))
                    (forall ((y Real)) (= y y)))) :rule bind)": false,

                "(anchor :step t1 :args ((y Real) (z Real) (:= x y)))
                (step t1.t1 (cl (= (= y x) (= y y))) :rule hole)
                (step t1 (cl (= (forall ((z Real) (x Real)) (= y z))
                    (forall ((z Real) (y Real)) (= y z)))) :rule bind)": false,
            }
            "Terms in conclusion clause don't match terms in previous command" {
                "(anchor :step t1 :args ((y Real) (:= x y)))
                (step t1.t1 (cl (= p q)) :rule hole)
                (step t1.t2 (cl (= r s)) :rule hole) ; This step shouldn't be here!
                (step t1 (cl (= (forall ((x Real)) p) (forall ((y Real)) q))) :rule bind)": false,

                "(anchor :step t1 :args ((y Real) (:= x y)))
                (step t1.t1 (cl (= p q)) :rule hole)
                (step t1 (cl (= (forall ((x Real)) q) (forall ((y Real)) p))) :rule bind)": false,
            }
            "Context substitutions don't match quantifier bindings" {
                "(anchor :step t1 :args ((y Real) (:= x y)))
                (step t1.t1 (cl (= p q)) :rule hole)
                (step t1 (cl (= (forall ((y Real)) p) (forall ((x Real)) q))) :rule bind)": false,

                "(anchor :step t1 :args ((y1 Real) (y2 Real) (:= x1 y1) (:= x2 y2)))
                (step t1.t1 (cl (= (= x1 x2) (= y1 y2))) :rule hole)
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
                "(step t1 (cl (= i x)) :rule hole)
                (anchor :step t2 :args ((x Int) (:= a x)))
                (step t2.t1 (cl (= p q)) :rule hole)
                (step t2 (cl (= (let ((a i)) p) q)) :rule let :premises (t1))": true,

                "(step t1 (cl (= i x)) :rule hole)
                (step t2 (cl (= k z)) :rule hole)
                (anchor :step t3 :args ((x Int) (y Int) (z Int) (:= a x) (:= b y) (:= c z)))
                (step t3.t1 (cl (= p q)) :rule hole)
                (step t3 (cl (= (let ((a i) (b y) (c k)) p) q)) :rule let :premises (t1 t2))": true,
            }
            "Premise equalities may be flipped" {
                "(step t1 (cl (= x i)) :rule hole)
                (anchor :step t2 :args ((x Int) (:= a x)))
                (step t2.t1 (cl (= p q)) :rule hole)
                (step t2 (cl (= (let ((a i)) p) q)) :rule let :premises (t1))": true,
            }
            "Wrong number of premises" {
                "(step t1 (cl (= i x)) :rule hole)
                (anchor :step t2 :args ((x Int) (y Int) (z Int) (:= a x) (:= b y) (:= c z)))
                (step t2.t1 (cl (= p q)) :rule hole)
                (step t2 (cl (= (let ((a i) (b y) (c k)) p) q)) :rule let :premises (t1))": false,

                "(step t1 (cl (= i x)) :rule hole)
                (step t2 (cl (= y y)) :rule hole)
                (step t3 (cl (= k z)) :rule hole)
                (anchor :step t4 :args ((x Int) (y Int) (z Int) (:= a x) (:= b y) (:= c z)))
                (step t4.t1 (cl (= p q)) :rule hole)
                (step t4 (cl (= (let ((a i) (b y) (c k)) p) q)) :rule let :premises (t1 t2))": false,
            }
            "Number of bindings is `let` term doesn't match number of substitutions in context" {
                "(step t1 (cl (= i x)) :rule hole)
                (step t2 (cl (= j y)) :rule hole)
                (anchor :step t3 :args ((x Int) (y Int) (z Int) (:= a x) (:= b y) (:= c z)))
                (step t3.t1 (cl (= p q)) :rule hole)
                (step t3 (cl (= (let ((a i) (b j)) p) q)) :rule let :premises (t1 t2))": false,
            }
            "u and u' don't match equality in previous command" {
                "(step t1 (cl (= i x)) :rule hole)
                (anchor :step t2 :args ((x Int) (:= a x)))
                (step t2.t1 (cl (= p (= i j))) :rule hole)
                (step t2 (cl (= (let ((a i)) p) q)) :rule let :premises (t1))": false,
            }
        }
    }

    #[test]
    fn onepoint() {
        test_cases! {
            definitions = "(declare-fun p () Bool)",
            "Simple working examples" {
                "(anchor :step t1 :args ((t Int) (:= x t)))
                (step t1.t1 (cl (= (=> (= x t) p) (=> (= t t) p))) :rule hole)
                (step t1 (cl (= (forall ((x Int)) (=> (= x t) p)) (=> (= t t) p)))
                    :rule onepoint)": true,

                "(anchor :step t1 :args ((t Int) (:= x t)))
                (step t1.t1 (cl (= (or (not (= x t)) p) (or (not (= t t)) p))) :rule hole)
                (step t1 (cl (= (forall ((x Int)) (or (not (= x t)) p)) (or (not (= t t)) p)))
                    :rule onepoint)": true,

                "(anchor :step t1 :args ((t Int) (:= x t)))
                (step t1.t1 (cl (= (and (= x t) p) (and (= t t) p))) :rule hole)
                (step t1 (cl (= (exists ((x Int)) (and (= x t) p)) (and (= t t) p)))
                    :rule onepoint)": true,
            }
            "Multiple quantifier bindings" {
                "(anchor :step t1 :args ((x Int) (y Int) (t Int) (:= z t)))
                (step t1.t1 (cl (= (=> (= z t) (= (+ x y) (+ z t)))
                                   (=> (= t t) (= (+ x y) (+ t t))))) :rule hole)
                (step t1 (cl (=
                    (forall ((x Int) (y Int) (z Int)) (=> (= z t) (= (+ x y) (+ z t))))
                    (forall ((x Int) (y Int))         (=> (= t t) (= (+ x y) (+ t t))))
                )) :rule onepoint)": true,

                "(anchor :step t1 :args ((x Int) (y Int) (t Int) (:= z t)))
                (step t1.t1 (cl (= (and (= z t) (= (+ x y) (+ z t)))
                                   (and (= t t) (= (+ x y) (+ t t))))) :rule hole)
                (step t1 (cl (=
                    (exists ((x Int) (y Int) (z Int)) (and (= z t) (= (+ x y) (+ z t))))
                    (exists ((x Int) (y Int))         (and (= t t) (= (+ x y) (+ t t))))
                )) :rule onepoint)": true,
            }
            "Multiple quantifier bindings eliminated" {
                "(anchor :step t1 :args ((t Int) (u Int) (v Int) (:= x t) (:= y u) (:= z v)))
                (step t1.t1 (cl (= (=> (= x t) (=> (= y u) (=> (= z v) p)))
                                   (=> (= t t) (=> (= u u) (=> (= v v) p))))) :rule hole)
                (step t1 (cl (=
                    (forall ((x Int) (y Int) (z Int)) (=> (= x t) (=> (= y u) (=> (= z v) p))))
                    (=> (= t t) (=> (= u u) (=> (= v v) p)))
                )) :rule onepoint)": true,

                "(anchor :step t1 :args ((t Int) (u Int) (v Int) (:= x t) (:= y u) (:= z v)))
                (step t1.t1 (cl (= (or (not (= x t)) (or (not (= y u)) (or (not (= z v)) p)))
                                   (or (not (= t t)) (or (not (= u u)) (or (not (= v v)) p)))
                )) :rule hole)
                (step t1 (cl (=
                    (forall ((x Int) (y Int) (z Int))
                        (or (not (= x t)) (or (not (= y u)) (or (not (= z v)) p))))
                    (or (not (= t t)) (or (not (= u u)) (or (not (= v v)) p)))
                )) :rule onepoint)": true,

                "(anchor :step t1 :args ((t Int) (u Int) (v Int) (:= x t) (:= y u) (:= z v)))
                (step t1.t1 (cl (= (=> (and (= x t) (and (= y u) (= z v))) p)
                                   (=> (and (= t t) (and (= u u) (= v v))) p))) :rule hole)
                (step t1 (cl (=
                    (forall ((x Int) (y Int) (z Int)) (=> (and (= x t) (and (= y u) (= z v))) p))
                    (=> (and (= t t) (and (= u u) (= v v))) p)
                )) :rule onepoint)": true,

                "(anchor :step t1 :args ((t Int) (u Int) (v Int) (:= x t) (:= y u) (:= z v)))
                (step t1.t1 (cl (= (and (= x t) (and (= y u) (and (= z v) p)))
                                   (and (= t t) (and (= u u) (and (= v v) p))))) :rule hole)
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
                "(anchor :step t1 :args ((:= x (choice ((x Int)) (p x)))))
                (step t1.t1 (cl (= (p x) (p (choice ((x Int)) (p x))))) :rule hole)
                (step t1 (cl (= (exists ((x Int)) (p x)) (p (choice ((x Int)) (p x)))))
                    :rule sko_ex)": true,

                "(anchor :step t1 :args (
                    (:= x (choice ((x Int)) (exists ((y Int)) (= x y))))
                    (:= y (choice ((y Int)) (= (choice ((x Int)) (exists ((y Int)) (= x y))) y)))
                ))
                (step t1.t1 (cl (=
                    (= x y)
                    (= (choice ((x Int)) (exists ((y Int)) (= x y)))
                       (choice ((y Int)) (= (choice ((x Int)) (exists ((y Int)) (= x y))) y)))
                )) :rule hole)
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
                "(anchor :step t1 :args ((:= x (choice ((x Int)) (not (p x))))))
                (step t1.t1 (cl (= (p x) (p (choice ((x Int)) (not (p x)))))) :rule hole)
                (step t1 (cl (= (forall ((x Int)) (p x)) (p (choice ((x Int)) (not (p x))))))
                    :rule sko_forall)": true,

                "(anchor :step t1 :args (
                    (:= x (choice ((x Int)) (not (forall ((y Int)) (= x y)))))
                    (:= y
                        (choice ((y Int))
                            (not (= (choice ((x Int)) (not (forall ((y Int)) (= x y)))) y))))
                ))
                (step t1.t1 (cl (=
                    (= x y)
                    (= (choice ((x Int)) (not (forall ((y Int)) (= x y))))
                        (choice ((y Int))
                            (not (= (choice ((x Int)) (not (forall ((y Int)) (= x y)))) y))))
                )) :rule hole)
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
