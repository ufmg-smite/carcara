use super::{
    CheckerError, EqualityError, RuleArgs, RuleResult, assert_clause_len, assert_eq,
    assert_is_expected, assert_num_premises, assert_polyeq, get_premise_term,
};
use crate::{
    ast::{pool::Pool, *},
    checker::error::{err, rassert},
    utils::MultiSet,
};
use indexmap::{IndexMap, IndexSet};
use std::collections::{HashMap, HashSet};

pub fn subproof(
    RuleArgs {
        conclusion,
        pool,
        context,
        previous_command,
        discharge,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    let previous_command = previous_command.ok_or(CheckerError::MustBeLastStepInSubproof)?;

    // This rule doesn't account for any variables or substitutions introduced by the anchor, so it
    // can only close subproofs whose anchor has no arguments
    rassert!(
        context.last().unwrap().args.is_empty(),
        "'subproof' rule can't close a subproof whose anchor has arguments"
    );

    assert_clause_len(conclusion, discharge.len() + 1)?;

    for (assumption, t) in discharge.iter().zip(conclusion) {
        match assumption {
            ProofCommand::Assume { id: _, term } => {
                let t = t.remove_negation_err()?;
                assert_polyeq(term, t, polyeq_time)?;
            }
            other => return err!("discharge must be 'assume' command: '{}'", other.id()),
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
            ));
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

    rassert!(
        l_bindings.len() == r_bindings.len(),
        "right and left quantifiers have different number of bindings: {} and {}",
        l_bindings.len(),
        r_bindings.len(),
    );

    let [l_bindings, r_bindings] = [l_bindings, r_bindings].map(|b| {
        b.iter()
            .map(|var| pool.add(var.clone().into()))
            .collect::<Vec<_>>()
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
        let y = y.as_var().unwrap();
        return err!("binding '{y}' appears as free variable in phi");
    }

    let args = &context.last().unwrap().args;
    check_renaming_anchor(pool, args, &l_bindings, &r_bindings)
}

/// Checks that the arguments of the anchor closed by a `bind` or `bind_let` step rename each
/// variable in `xs` to the variable in the same position in `ys`.
///
/// The anchor must fix every `y_i`, and its substitution must map each `x_i` to `y_i`. It may also
/// fix the `x_i` variables, but it can't fix or assign any other variable.
pub(super) fn check_renaming_anchor(
    pool: &mut Pool,
    args: &[AnchorArg],
    xs: &[Rc<Term>],
    ys: &[Rc<Term>],
) -> RuleResult {
    let mut fixed = IndexSet::new();

    // The context composes assignments in order, so a value that was renamed by an earlier
    // assignment is renamed again. For example, `(:= x y) (:= y x)` maps both `x` and `y` to `y`
    let mut substitution: IndexMap<Rc<Term>, Rc<Term>> = IndexMap::new();

    for arg in args {
        match arg {
            AnchorArg::Variable((name, _)) if !substitution.is_empty() => {
                return err!("unexpected anchor argument: '{name}'");
            }
            AnchorArg::Variable(var) => {
                let var = pool.add(var.clone().into());
                // TODO: maybe optimize these `contains` by converting into a hash set?
                rassert!(
                    xs.contains(&var) || ys.contains(&var),
                    "anchor fixes variable '{var}', which is not a binding",
                );
                fixed.insert(var);
            }
            AnchorArg::Assign(var, value) => {
                let var = pool.add(var.clone().into());
                rassert!(
                    xs.contains(&var),
                    "anchor assigns variable '{var}', which is not a left-hand binding",
                );
                let value = substitution.get(value).unwrap_or(value).clone();
                substitution.insert(var, value);
            }
        }
    }

    for (x, y) in xs.iter().zip(ys) {
        if !fixed.contains(y) {
            let y = y.as_var().unwrap().to_owned();
            return Err(CheckerError::BindingIsNotInContext(y));
        }
        let value = substitution.get(x).unwrap_or(x);
        rassert!(
            value == y,
            "anchor maps '{x}' to '{value}' instead of '{y}'"
        );
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
    let args = &context.last().unwrap().args;
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
        "expected {} bindings in 'let' term, got {}",
        mappings.len(),
        let_bindings.len(),
    );

    let mut pairs: Vec<_> = let_bindings
        .iter()
        .map(|(x, t)| {
            let sort = pool.sort(t);
            let x_term = pool.add((x.clone(), sort).into());
            let Some(s) = mappings.get(&x_term) else {
                return Err(CheckerError::BindingIsNotInContext(x.clone()));
            };
            Ok((s, t))
        })
        .collect::<Result<_, CheckerError>>()?;
    pairs.retain(|(s, t)| s != t); // The pairs where s == t don't need a premise to justify them

    assert_num_premises(premises, pairs.len())?;

    for (premise, (s, t)) in premises.iter().zip(pairs) {
        let (a, b) = match_term_err!((= a b) = get_premise_term(premise)?)?;
        rassert!(
            (a, b) == (s, t) || (a, b) == (t, s),
            "premise '(= {a} {b})' doesn't justify substitution of '{s}' for '{t}'",
        );
    }
    Ok(())
}

fn extract_points(pool: &mut Pool, quant: Binder, term: &Rc<Term>) -> HashSet<(String, Rc<Term>)> {
    fn find_points(
        pool: &mut Pool,
        acc: &mut HashSet<(String, Rc<Term>)>,
        seen: &mut HashSet<(Rc<Term>, bool)>,
        shadowed: &mut MultiSet<String>,
        polarity: bool,
        term: &Rc<Term>,
    ) {
        let key = (term.clone(), polarity);
        if seen.contains(&key) {
            return;
        }
        seen.insert(key);

        if let Some(inner) = term.remove_negation() {
            return find_points(pool, acc, seen, shadowed, !polarity, inner);
        }
        if let Some((_, bindings, inner)) = term.as_quant() {
            // When entering a nested quantifier, all variables it binds are shadowed, so we don't
            // count its points as points for the outer variable
            shadowed.extend(bindings.iter().map(|(var, _)| var.clone()));

            // The bindings also invalidate the seen cache, so we must use a fresh one
            find_points(pool, acc, &mut HashSet::new(), shadowed, polarity, inner);

            for (var, _) in bindings {
                shadowed.remove(var);
            }
            return;
        }

        // An equality (= x t) cannot be a point if it contains a shadowed variable. That could
        // either be `x` itself, or a free variable in `t`.
        let mut contains_shadowed_var = |a: &str, b: &Rc<Term>| {
            shadowed.contains(a)
                || pool
                    .free_vars(b)
                    .iter()
                    .any(|v| shadowed.contains(v.as_var().unwrap()))
        };
        match polarity {
            true => {
                if let Some((a, b)) = match_term!((= a b) = term) {
                    if let Some(a) = a.as_var()
                        && !contains_shadowed_var(a, b)
                    {
                        acc.insert((a.to_owned(), b.clone()));
                    }
                    if let Some(b) = b.as_var()
                        && !contains_shadowed_var(b, a)
                    {
                        acc.insert((b.to_owned(), a.clone()));
                    }
                } else if let Some(args) = match_term!((and ...) = term) {
                    for a in args {
                        find_points(pool, acc, seen, shadowed, true, a);
                    }
                }
            }
            false => {
                if let Some((p, q)) = match_term!((=> p q) = term) {
                    find_points(pool, acc, seen, shadowed, true, p);
                    find_points(pool, acc, seen, shadowed, false, q);
                } else if let Some(args) = match_term!((or ...) = term) {
                    for a in args {
                        find_points(pool, acc, seen, shadowed, false, a);
                    }
                }
            }
        }
    }

    let mut result = HashSet::new();
    find_points(
        pool,
        &mut result,
        &mut HashSet::new(),
        &mut MultiSet::new(),
        quant == Binder::Exists,
        term,
    );
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

    let points = extract_points(pool, quant, left);

    // Since a substitution may use a variable introduced in a previous substitution, we apply the
    // substitution to the points in order to replace these variables by their value.
    let points: HashSet<_> = points
        .into_iter()
        .map(|(x, t)| (x, context.apply(pool, &t)))
        .collect();

    let context = context.last().unwrap();
    let mut mappings = context.args.iter().filter_map(AnchorArg::as_assign);

    // For each substitution (:= x t) in the context, the equality (= x t) must appear in phi
    if let Some((k, v)) = mappings.find(|&(k, v)| !points.contains(&(k.clone(), v.clone()))) {
        return err!("substitution '(:= {k} {v})' doesn't appear as a point in phi");
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
        return err!(
            "expected binding list in right-hand side to be '{}'",
            BindingList(var_args),
        );
    }

    let l_bindings: HashSet<_> = l_bindings.iter().collect();

    // Convert `var_args` into a set so we can do union operation
    let var_args: HashSet<_> = var_args.iter().collect();

    let expected = &var_args | &point_vars;
    if l_bindings != expected {
        let expected: Vec<_> = expected.into_iter().cloned().collect();
        return err!(
            "expected binding list in left-hand side to be '{}'",
            BindingList(expected),
        );
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

    let args = context.last().unwrap().args.iter();

    let substitution: HashMap<Rc<Term>, Rc<Term>> = args
        .filter_map(AnchorArg::as_assign)
        .map(|(k, v)| {
            let var = Term::new_var(k, pool.sort(v));
            (pool.add(var), v.clone())
        })
        .collect();

    for (i, x) in bindings.iter().enumerate() {
        let x_term = pool.add(Term::from(x.clone()));
        let Some(t) = substitution.get(&x_term) else {
            return Err(CheckerError::BindingIsNotInContext(x.0.clone()));
        };

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
