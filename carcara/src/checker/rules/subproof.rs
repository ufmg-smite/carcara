use super::{
    assert_clause_len, assert_eq, assert_is_expected, assert_num_premises, assert_polyeq,
    get_premise_term, CheckerError, EqualityError, RuleArgs, RuleResult,
};
use crate::{ast::*, checker::error::SubproofError};
use indexmap::{IndexMap, IndexSet};
use std::collections::{HashMap, HashSet};

pub fn subproof(
    RuleArgs {
        conclusion,
        pool,
        previous_command,
        discharge,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    let previous_command = previous_command.ok_or(CheckerError::MustBeLastStepInSubproof)?;

    assert_clause_len(conclusion, discharge.len() + 1)?;

    for (assumption, t) in discharge.iter().zip(conclusion) {
        match assumption {
            ProofCommand::Assume { id: _, term } => {
                let t = t.remove_negation_err()?;
                assert_polyeq(term, t, polyeq_time)?;
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

    assert_polyeq(conclusion.last().unwrap(), &phi, polyeq_time)
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

    let (l_binder, l_bindings, left) = left.as_binder_err()?;
    let (r_binder, r_bindings, right) = right.as_binder_err()?;
    assert_eq(&l_binder, &r_binder)?;

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

    let (xs, ys): (IndexSet<_>, IndexSet<_>) = {
        let (mut xs, mut ys) = (IndexSet::new(), IndexSet::new());
        for arg in &context.args {
            match arg {
                AnchorArg::Variable((name, _)) if !xs.is_empty() => {
                    return Err(SubproofError::BindUnexpectedVarArgument(name.clone()).into());
                }
                AnchorArg::Variable(var) => {
                    ys.insert(pool.add(var.clone().into()));
                }
                AnchorArg::Assign(var, _) => {
                    xs.insert(pool.add(var.clone().into()));
                }
            }
        }
        (xs, ys)
    };

    rassert!(
        l_bindings.len() == r_bindings.len(),
        SubproofError::BindDifferentNumberOfBindings(l_bindings.len(), r_bindings.len())
    );

    let (l_bindings, r_bindings): (IndexSet<_>, IndexSet<_>) = (
        l_bindings.difference(&r_bindings).cloned().collect(),
        r_bindings.difference(&r_bindings).cloned().collect(),
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

    // Since we are closing a subproof, we only care about the mappings that were introduced in it
    let context = context.last().unwrap();
    let args = &context.as_ref().unwrap().args;
    let mappings: IndexMap<Rc<Term>, Rc<Term>> = args
        .iter()
        .filter_map(|arg| {
            let (name, value) = arg.as_assign()?;
            let var = Term::new_var(name, pool.sort(value));
            Some((pool.add(var), value.clone()))
        })
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
        let_bindings.len() == mappings.len(),
        SubproofError::WrongNumberOfLetBindings(mappings.len(), let_bindings.len())
    );

    let mut pairs: Vec<_> = let_bindings
        .iter()
        .map(|(x, t)| {
            let sort = pool.sort(t);
            let x_term = pool.add((x.clone(), sort).into());
            let s = mappings
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

fn extract_points(quant: Binder, term: &Rc<Term>) -> HashSet<(String, Rc<Term>)> {
    fn find_points(
        acc: &mut HashSet<(String, Rc<Term>)>,
        seen: &mut HashSet<(Rc<Term>, bool)>,
        polarity: bool,
        term: &Rc<Term>,
    ) {
        let key = (term.clone(), polarity);
        if seen.contains(&key) {
            return;
        }
        seen.insert(key);

        if let Some(inner) = term.remove_negation() {
            return find_points(acc, seen, !polarity, inner);
        }
        if let Some((_, _, inner)) = term.as_quant() {
            return find_points(acc, seen, polarity, inner);
        }
        match polarity {
            true => {
                if let Some((a, b)) = match_term!((= a b) = term) {
                    if let Some(a) = a.as_var() {
                        acc.insert((a.to_owned(), b.clone()));
                    }
                    if let Some(b) = b.as_var() {
                        acc.insert((b.to_owned(), a.clone()));
                    }
                } else if let Some(args) = match_term!((and ...) = term) {
                    for a in args {
                        find_points(acc, seen, true, a);
                    }
                }
            }
            false => {
                if let Some((p, q)) = match_term!((=> p q) = term) {
                    find_points(acc, seen, true, p);
                    find_points(acc, seen, false, q);
                } else if let Some(args) = match_term!((or ...) = term) {
                    for a in args {
                        find_points(acc, seen, false, a);
                    }
                }
            }
        }
    }

    let mut result = HashSet::new();
    let mut seen = HashSet::new();
    find_points(&mut result, &mut seen, quant == Binder::Exists, term);
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

    let points = extract_points(quant, left);

    // Since a substitution may use a variable introduced in a previous substitution, we apply the
    // substitution to the points in order to replace these variables by their value.
    let points: HashSet<_> = points
        .into_iter()
        .map(|(x, t)| (x, context.apply(pool, &t)))
        .collect();

    let context = context.last().unwrap();
    let context = context.as_ref().unwrap();
    let mut mappings = context.args.iter().filter_map(AnchorArg::as_assign);

    // For each substitution (:= x t) in the context, the equality (= x t) must appear in phi
    if let Some((k, v)) = mappings.find(|&(k, v)| !points.contains(&(k.clone(), v.clone()))) {
        return Err(SubproofError::NoPointForSubstitution(k.clone(), v.clone()).into());
    }

    // Here we check that the right variables were eliminated. Using the notation in the
    // specification, we have that:
    //
    // - `var_args` are the x_k_1, ..., x_k_m variables that appear as the variable arguments to the
    // anchor
    // - `point_vars` are the x_j_1, ..., x_j_o variables that appear as the left-hand side of the
    // assign arguments in the anchor
    // - `l_bindings` are the x_1, ..., x_n variables in the binding list of the left-hand
    // quantifier
    // - `r_bindings` are the x_k_1, ..., x_k_m variables in the binding list of the right-hand
    // quantifier
    //
    // We must then make sure that `var_args == r_bindings`, and that
    // `union(var_args, point_vars) == l_bindings`.
    let var_args: Vec<_> = context
        .args
        .iter()
        .filter_map(AnchorArg::as_variable)
        .cloned()
        .collect();

    let mappings = context.args.iter().filter_map(AnchorArg::as_assign);
    let point_vars: Vec<_> = mappings
        .map(|(name, value)| (name.clone(), pool.sort(value)))
        .collect();
    let point_vars: HashSet<_> = point_vars.iter().collect();

    if var_args != r_bindings.as_ref() {
        return Err(SubproofError::OnepointWrongRightBindings(BindingList(var_args)).into());
    }

    let l_bindings: HashSet<_> = l_bindings.iter().collect();

    // Convert `var_args` into a set so we can do union operation
    let var_args: HashSet<_> = var_args.iter().collect();

    let expected = &var_args | &point_vars;
    if l_bindings != expected {
        let expected: Vec<_> = expected.into_iter().cloned().collect();
        return Err(SubproofError::OnepointWrongLeftBindings(BindingList(expected)).into());
    }

    Ok(())
}

fn generic_skolemization_rule(
    rule_type: Binder,
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

    let context = context.last().unwrap();
    let args = context.as_ref().unwrap().args.iter();

    let substitution: HashMap<Rc<Term>, Rc<Term>> = args
        .filter_map(AnchorArg::as_assign)
        .map(|(k, v)| {
            let var = Term::new_var(k, pool.sort(v));
            (pool.add(var), v.clone())
        })
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
                inner = pool.add(Term::Binder(
                    rule_type,
                    BindingList(bindings.0[i + 1..].to_vec()),
                    inner,
                ));
            }

            // If the rule is `sko_forall`, the predicate in the choice term should be negated
            if rule_type == Binder::Forall {
                inner = build_term!(pool, (not { inner }));
            }
            let binding_list = BindingList(vec![x.clone()]);
            pool.add(Term::Binder(Binder::Choice, binding_list, inner))
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
    generic_skolemization_rule(Binder::Exists, args)
}

pub fn sko_forall(args: RuleArgs) -> RuleResult {
    generic_skolemization_rule(Binder::Forall, args)
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
                (step t1 (cl (not p) (not q) (not (= r s)))
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
                "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
                (step t1.t1 (cl (= p q)) :rule hole)
                (step t1 (cl (= (forall ((x Real)) p) (forall ((y Real)) q))) :rule bind)": true,

                "(anchor :step t1 :args ((y1 Real) (y2 Real) (:= (x1 Real) y1) (:= (x2 Real) y2)))
                (step t1.t1 (cl (= (= x1 x2) (= y1 y2))) :rule hole)
                (step t1 (cl (= (forall ((x1 Real) (x2 Real)) (= x1 x2))
                    (forall ((y1 Real) (y2 Real)) (= y1 y2)))) :rule bind)": true,
            }
            "Examples with binding arguments" {
                "(anchor :step t1 :args ((y Real) (z Real) (:= (x Real) y)))
                (step t1.t1 (cl (= p q)) :rule hole)
                (step t1 (cl (= (forall ((x Real) (z Real)) p)
                    (forall ((y Real) (z Real)) q))) :rule bind)": true,
            }
            "Out-of-place variable argument in anchor" {
                "(anchor :step t1 :args ((y1 Real) (:= (x1 Real) y1) (y2 Real) (:= (x2 Real) y2)))
                (step t1.t1 (cl (= (= x1 x2) (= y1 y2))) :rule hole)
                (step t1 (cl (= (forall ((x1 Real) (x2 Real)) (= x1 x2))
                    (forall ((y1 Real) (y2 Real)) (= y1 y2)))) :rule bind)": false,
            }
            "Binding `lambda` and `choice` terms" {
                "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
                (step t1.t1 (cl (= x y)) :rule hole)
                (step t1 (cl (= (lambda ((x Real)) x) (lambda ((y Real)) y))) :rule bind)": true,

                "(anchor :step t1 :args ((y Int) (:= (x Int) y)))
                (step t1.t1 (cl (= p q)) :rule hole)
                (step t1 (cl (= (choice ((x Int)) p) (choice ((y Int)) q))) :rule bind)": true,
            }
            "y_i appears in phi as a free variable" {
                "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
                (step t1.t1 (cl (= (= y x) (= y y))) :rule hole)
                (step t1 (cl (= (forall ((x Real)) (= y x))
                    (forall ((y Real)) (= y y)))) :rule bind)": false,

                "(anchor :step t1 :args ((y Real) (z Real) (:= (x Real) y)))
                (step t1.t1 (cl (= (= y x) (= y y))) :rule hole)
                (step t1 (cl (= (forall ((z Real) (x Real)) (= y z))
                    (forall ((z Real) (y Real)) (= y z)))) :rule bind)": false,
            }
            "Terms in conclusion clause don't match terms in previous command" {
                "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
                (step t1.t1 (cl (= p q)) :rule hole)
                (step t1.t2 (cl (= r s)) :rule hole) ; This step shouldn't be here!
                (step t1 (cl (= (forall ((x Real)) p) (forall ((y Real)) q))) :rule bind)": false,

                "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
                (step t1.t1 (cl (= p q)) :rule hole)
                (step t1 (cl (= (forall ((x Real)) q) (forall ((y Real)) p))) :rule bind)": false,
            }
            "Context substitutions don't match quantifier bindings" {
                "(anchor :step t1 :args ((y Real) (:= (x Real) y)))
                (step t1.t1 (cl (= p q)) :rule hole)
                (step t1 (cl (= (forall ((y Real)) p) (forall ((x Real)) q))) :rule bind)": false,

                "(anchor :step t1 :args ((y1 Real) (y2 Real) (:= (x1 Real) y1) (:= (x2 Real) y2)))
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
                (anchor :step t2 :args ((x Int) (:= (a Int) x)))
                (step t2.t1 (cl (= p q)) :rule hole)
                (step t2 (cl (= (let ((a i)) p) q)) :rule let :premises (t1))": true,

                "(step t1 (cl (= i x)) :rule hole)
                (step t2 (cl (= k z)) :rule hole)
                (anchor :step t3 :args ((x Int) (y Int) (z Int) (:= (a Int) x) (:= (b Int) y) (:= (c Int) z)))
                (step t3.t1 (cl (= p q)) :rule hole)
                (step t3 (cl (= (let ((a i) (b y) (c k)) p) q)) :rule let :premises (t1 t2))": true,
            }
            "Premise equalities may be flipped" {
                "(step t1 (cl (= x i)) :rule hole)
                (anchor :step t2 :args ((x Int) (:= (a Int) x)))
                (step t2.t1 (cl (= p q)) :rule hole)
                (step t2 (cl (= (let ((a i)) p) q)) :rule let :premises (t1))": true,
            }
            "Wrong number of premises" {
                "(step t1 (cl (= i x)) :rule hole)
                (anchor :step t2 :args ((x Int) (y Int) (z Int) (:= (a Int) x) (:= (b Int) y) (:= (c Int) z)))
                (step t2.t1 (cl (= p q)) :rule hole)
                (step t2 (cl (= (let ((a i) (b y) (c k)) p) q)) :rule let :premises (t1))": false,

                "(step t1 (cl (= i x)) :rule hole)
                (step t2 (cl (= y y)) :rule hole)
                (step t3 (cl (= k z)) :rule hole)
                (anchor :step t4 :args ((x Int) (y Int) (z Int) (:= (a Int) x) (:= (b Int) y) (:= (c Int) z)))
                (step t4.t1 (cl (= p q)) :rule hole)
                (step t4 (cl (= (let ((a i) (b y) (c k)) p) q)) :rule let :premises (t1 t2))": false,
            }
            "Number of bindings is `let` term doesn't match number of substitutions in context" {
                "(step t1 (cl (= i x)) :rule hole)
                (step t2 (cl (= j y)) :rule hole)
                (anchor :step t3 :args ((x Int) (y Int) (z Int) (:= (a Int) x) (:= (b Int) y) (:= (c Int) z)))
                (step t3.t1 (cl (= p q)) :rule hole)
                (step t3 (cl (= (let ((a i) (b j)) p) q)) :rule let :premises (t1 t2))": false,
            }
            "u and u' don't match equality in previous command" {
                "(step t1 (cl (= i x)) :rule hole)
                (anchor :step t2 :args ((x Int) (:= (a Int) x)))
                (step t2.t1 (cl (= p (= i j))) :rule hole)
                (step t2 (cl (= (let ((a i)) p) q)) :rule let :premises (t1))": false,
            }
        }
    }

    #[test]
    fn onepoint() {
        test_cases! {
            definitions = "
                (declare-const p Bool)
                (declare-const t Int)
                (declare-const u Int)
                (declare-const v Int)
            ",
            "Simple working examples" {
                "(anchor :step t1 :args ((:= (x Int) t)))
                (step t1.t1 (cl (= (=> (= x t) p) (=> (= t t) p))) :rule hole)
                (step t1 (cl (= (forall ((x Int)) (=> (= x t) p)) (=> (= t t) p)))
                    :rule onepoint)": true,

                "(anchor :step t1 :args ((:= (x Int) t)))
                (step t1.t1 (cl (= (or (not (= x t)) p) (or (not (= t t)) p))) :rule hole)
                (step t1 (cl (= (forall ((x Int)) (or (not (= x t)) p)) (or (not (= t t)) p)))
                    :rule onepoint)": true,

                "(anchor :step t1 :args ((:= (x Int) t)))
                (step t1.t1 (cl (= (and (= x t) p) (and (= t t) p))) :rule hole)
                (step t1 (cl (= (exists ((x Int)) (and (= x t) p)) (and (= t t) p)))
                    :rule onepoint)": true,
            }
            "Multiple quantifier bindings" {
                "(anchor :step t1 :args ((x Int) (y Int) (:= (z Int) t)))
                (step t1.t1 (cl (= (=> (= z t) (= (+ x y) (+ z t)))
                                   (=> (= t t) (= (+ x y) (+ t t))))) :rule hole)
                (step t1 (cl (=
                    (forall ((x Int) (y Int) (z Int)) (=> (= z t) (= (+ x y) (+ z t))))
                    (forall ((x Int) (y Int))         (=> (= t t) (= (+ x y) (+ t t))))
                )) :rule onepoint)": true,

                "(anchor :step t1 :args ((x Int) (y Int) (:= (z Int) t)))
                (step t1.t1 (cl (= (and (= z t) (= (+ x y) (+ z t)))
                                   (and (= t t) (= (+ x y) (+ t t))))) :rule hole)
                (step t1 (cl (=
                    (exists ((x Int) (y Int) (z Int)) (and (= z t) (= (+ x y) (+ z t))))
                    (exists ((x Int) (y Int))         (and (= t t) (= (+ x y) (+ t t))))
                )) :rule onepoint)": true,
            }
            "Multiple quantifier bindings eliminated" {
                "(anchor :step t1 :args ((:= (x Int) t) (:= (y Int) u) (:= (z Int) v)))
                (step t1.t1 (cl (= (=> (= x t) (=> (= y u) (=> (= z v) p)))
                                   (=> (= t t) (=> (= u u) (=> (= v v) p))))) :rule hole)
                (step t1 (cl (=
                    (forall ((x Int) (y Int) (z Int)) (=> (= x t) (=> (= y u) (=> (= z v) p))))
                    (=> (= t t) (=> (= u u) (=> (= v v) p)))
                )) :rule onepoint)": true,

                "(anchor :step t1 :args ((:= (x Int) t) (:= (y Int) u) (:= (z Int) v)))
                (step t1.t1 (cl (= (or (not (= x t)) (or (not (= y u)) (or (not (= z v)) p)))
                                   (or (not (= t t)) (or (not (= u u)) (or (not (= v v)) p)))
                )) :rule hole)
                (step t1 (cl (=
                    (forall ((x Int) (y Int) (z Int))
                        (or (not (= x t)) (or (not (= y u)) (or (not (= z v)) p))))
                    (or (not (= t t)) (or (not (= u u)) (or (not (= v v)) p)))
                )) :rule onepoint)": true,

                "(anchor :step t1 :args ((:= (x Int) t) (:= (y Int) u) (:= (z Int) v)))
                (step t1.t1 (cl (= (=> (and (= x t) (and (= y u) (= z v))) p)
                                   (=> (and (= t t) (and (= u u) (= v v))) p))) :rule hole)
                (step t1 (cl (=
                    (forall ((x Int) (y Int) (z Int)) (=> (and (= x t) (and (= y u) (= z v))) p))
                    (=> (and (= t t) (and (= u u) (= v v))) p)
                )) :rule onepoint)": true,

                "(anchor :step t1 :args ((:= (x Int) t) (:= (y Int) u) (:= (z Int) v)))
                (step t1.t1 (cl (= (and (= x t) (and (= y u) (and (= z v) p)))
                                   (and (= t t) (and (= u u) (and (= v v) p))))) :rule hole)
                (step t1 (cl (=
                    (exists ((x Int) (y Int) (z Int)) (and (= x t) (and (= y u) (and (= z v) p))))
                    (and (= t t) (and (= u u) (and (= v v) p)))
                )) :rule onepoint)": true,
            }
            "Multiple occurrences with different polarity" {
                // This test reproduces a bug that existed where the cache didn't take into account
                // the polarity of a seen term.
                "(anchor :step t3 :args ((:= (?x Int) 0)))
                (step t3.t8 (cl (=
                    (=> (not (= 0 ?x)) (=> (= 2 2) (=> (= 0 ?x) (= 1 2))))
                    (=> (not (= 0 0)) (=> (= 2 2) (=> (= 0 0) (= 1 2))))
                )) :rule hole)
                (step t3 (cl (=
                    (forall ((?x Int)) (=> (not (= 0 ?x)) (=> (= 2 2) (=> (= 0 ?x) (= 1 2)))))
                    (=> (not (= 0 0)) (=> (= 2 2) (=> (= 0 0) (= 1 2))))
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
                (step t1.t1 (cl (= (p x) (p (choice ((x Int)) (p x))))) :rule hole)
                (step t1 (cl (= (exists ((x Int)) (p x)) (p (choice ((x Int)) (p x)))))
                    :rule sko_ex)": true,

                "(anchor :step t1 :args (
                    (:= (x Int) (choice ((x Int)) (exists ((y Int)) (= x y))))
                    (:= (y Int) (choice ((y Int)) (= (choice ((x Int)) (exists ((y Int)) (= x y))) y)))
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
                "(anchor :step t1 :args ((:= (x Int) (choice ((x Int)) (not (p x))))))
                (step t1.t1 (cl (= (p x) (p (choice ((x Int)) (not (p x)))))) :rule hole)
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
