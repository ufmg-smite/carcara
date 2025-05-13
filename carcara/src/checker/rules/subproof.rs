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
