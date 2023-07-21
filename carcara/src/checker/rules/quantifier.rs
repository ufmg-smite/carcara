use super::{
    assert_clause_len, assert_eq, assert_is_expected, assert_num_args, assert_polyeq_expected,
    CheckerError, RuleArgs, RuleResult,
};
use crate::{ast::*, checker::error::QuantifierError, utils::DedupIterator};
use ahash::{AHashMap, AHashSet};

pub fn forall_inst(
    RuleArgs {
        conclusion, args, pool, polyeq_time, ..
    }: RuleArgs,
) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let ((bindings, original), substituted) =
        match_term_err!((or (not (forall ... original)) result) = &conclusion[0])?;

    assert_num_args(args, bindings.len())?;

    // Since the bindings and arguments may not be in the same order, we collect the bindings into
    // a hash set, and remove each binding from it as we find the associated argument
    let mut bindings: AHashSet<_> = bindings.iter().cloned().collect();
    let substitution: AHashMap<_, _> = args
        .iter()
        .map(|arg| {
            let (arg_name, arg_value) = arg.as_assign()?;
            let arg_sort = pool.sort(arg_value).clone();
            rassert!(
                bindings.remove(&(arg_name.clone(), arg_sort.clone())),
                QuantifierError::NoBindingMatchesArg(arg_name.clone())
            );

            let ident_term = (arg_name.clone(), arg_sort).into();
            Ok((pool.add(ident_term), arg_value.clone()))
        })
        .collect::<Result<_, CheckerError>>()?;
    let mut substitution = Substitution::new(pool, substitution)?;

    // All bindings were accounted for in the arguments
    rassert!(
        bindings.is_empty(),
        QuantifierError::NoArgGivenForBinding(bindings.iter().next().unwrap().0.clone())
    );

    // Equalities may be reordered in the final term, so we need to compare for polyequality here
    let expected = substitution.apply(pool, original);
    assert_polyeq_expected(substituted, expected, polyeq_time)
}

pub fn qnt_join(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;

    let (q_1, bindings_1, left) = left.as_quant_err()?;
    let (q_2, bindings_2, left) = left.as_quant_err()?;
    let (q_3, bindings_3, right) = right.as_quant_err()?;

    assert_eq(&q_1, &q_2)?;
    assert_eq(&q_2, &q_3)?;
    assert_eq(left, right)?;

    let combined = bindings_1.iter().chain(bindings_2).dedup();
    rassert!(
        bindings_3.iter().eq(combined),
        QuantifierError::JoinFailed {
            left_outer: bindings_1.clone(),
            left_inner: bindings_2.clone(),
            right: bindings_3.clone()
        }
    );
    Ok(())
}

pub fn qnt_rm_unused(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;
    let (q_1, bindings_1, phi_1) = left.as_quant_err()?;

    let (bindings_2, phi_2) = match right.as_quant() {
        Some((q_2, b, t)) => {
            assert_eq(&q_1, &q_2)?;
            (b, t)
        }

        // If the right-hand side term is not a quantifier, we consider it a quantifier with an
        // empty list of bindings
        None => (BindingList::EMPTY, right),
    };
    assert_eq(phi_1, phi_2)?;

    // Cloning here may be unnecessary
    // TODO: Remove the clone from similar situations
    let free_vars = pool.free_vars(phi_1).clone();

    let expected: Vec<_> = bindings_1
        .iter()
        .filter(|&var| {
            let var = pool.add(var.clone().into());
            free_vars.contains(&var)
        })
        .cloned()
        .collect();

    assert_is_expected(bindings_2, BindingList(expected))
}

/// Converts a term into negation normal form, expanding all connectives.
fn negation_normal_form(
    pool: &mut dyn TPool,
    term: &Rc<Term>,
    polarity: bool,
    cache: &mut AHashMap<(Rc<Term>, bool), Rc<Term>>,
) -> Rc<Term> {
    if let Some(v) = cache.get(&(term.clone(), polarity)) {
        return v.clone();
    }

    let result = if let Some(inner) = match_term!((not t) = term) {
        negation_normal_form(pool, inner, !polarity, cache)
    } else if let Term::Op(op @ (Operator::And | Operator::Or), args) = term.as_ref() {
        let op = match (op, polarity) {
            (op, true) => *op,
            (Operator::And, false) => Operator::Or,
            (Operator::Or, false) => Operator::And,
            (_, false) => unreachable!(),
        };
        let args = args
            .iter()
            .map(|a| negation_normal_form(pool, a, polarity, cache))
            .collect();
        pool.add(Term::Op(op, args))
    } else if let Some((p, q)) = match_term!((=> p q) = term) {
        let a = negation_normal_form(pool, p, !polarity, cache);
        let b = negation_normal_form(pool, q, polarity, cache);

        match polarity {
            true => build_term!(pool, (or {a} {b})),
            false => build_term!(pool, (and {a} {b})),
        }
    } else if let Some((p, q, r)) = match_term!((ite p q r) = term) {
        let a = negation_normal_form(pool, p, !polarity, cache);
        let b = negation_normal_form(pool, q, polarity, cache);
        let c = negation_normal_form(pool, p, polarity, cache);
        let d = negation_normal_form(pool, r, polarity, cache);

        match polarity {
            true => build_term!(pool, (and (or {a} {b}) (or {c} {d}))),
            false => build_term!(pool, (or (and {a} {b}) (and {c} {d}))),
        }
    } else if let Some((quant, bindings, inner)) = term.as_quant() {
        let quant = if polarity { quant } else { !quant };
        let inner = negation_normal_form(pool, inner, polarity, cache);
        pool.add(Term::Quant(quant, bindings.clone(), inner))
    } else {
        match match_term!((= p q) = term) {
            Some((left, right)) if pool.sort(left).as_sort().unwrap() == &Sort::Bool => {
                let a = negation_normal_form(pool, left, !polarity, cache);
                let b = negation_normal_form(pool, right, polarity, cache);
                let c = negation_normal_form(pool, right, !polarity, cache);
                let d = negation_normal_form(pool, left, polarity, cache);
                match polarity {
                    true => build_term!(pool, (and (or {a} {b}) (or {c} {d}))),
                    false => build_term!(pool, (or (and {a} {b}) (and {c} {d}))),
                }
            }
            _ => match polarity {
                true => term.clone(),
                false => build_term!(pool, (not {term.clone()})),
            },
        }
    };
    cache.insert((term.clone(), polarity), result.clone());
    result
}

/// This represents a formula in conjunctive normal form, that is, it is a conjunction of clauses,
/// which are disjunctions of literals
type CnfFormula = Vec<Vec<Rc<Term>>>;

/// Applies the distribution rules into a disjunction of formulas in conjunctive normal form. More
/// precisely, this takes the disjunction `P v Q v R v ...`, where
/// ```text
///     P = P_1 ^ P_2 ^ P_3 ^ ...
///     Q = Q_1 ^ Q_2 ^ Q_3 ^ ...
///     R = R_1 ^ R_2 ^ R_3 ^ ...
///     ...
/// ```
/// and returns the conjunction of all `(P_i v Q_j v R_k v ...)`, for every combination of `i`,
/// `j`, `k`, etc.
fn distribute(formulas: &[CnfFormula]) -> CnfFormula {
    match formulas {
        // This function is never called with an empty slice of formulas, so to avoid unnecessary
        // allocations we use the case with just one formula as the base case for the recursion
        [formula] => formula.clone(),
        [] => unreachable!(),

        [head, tail @ ..] => {
            // We recursively apply the distribution rules to the tail, and, for every combination
            // of a clause in the tail formula and a clause in the head formula, we append the two
            // clauses and push the result to the final formula
            let tail = distribute(tail);
            let mut acc = Vec::with_capacity(head.len() * tail.len());
            for head_clause in head {
                for tail_clause in &tail {
                    let mut result = Vec::with_capacity(head_clause.len() + tail_clause.len());
                    result.extend(head_clause.iter().cloned());
                    result.extend(tail_clause.iter().cloned());
                    acc.push(result);
                }
            }
            acc
        }
    }
}

/// Prenex all universal quantifiers in a term. This doesn't prenex existential quantifiers. This
/// assumes the term is in negation normal form.
fn prenex_forall<C>(pool: &mut dyn TPool, acc: &mut C, term: &Rc<Term>) -> Rc<Term>
where
    C: Extend<SortedVar>,
{
    match term.as_ref() {
        // This function assumes that the term is already in negation normal form, so any term
        // other than a conjunction, disjunction, or a universal quantifier is considered a literal
        Term::Op(op @ (Operator::And | Operator::Or), args) => {
            let args = args.iter().map(|a| prenex_forall(pool, acc, a)).collect();
            pool.add(Term::Op(*op, args))
        }
        Term::Quant(Quantifier::Forall, bindings, inner) => {
            acc.extend(bindings.iter().cloned());
            prenex_forall(pool, acc, inner)
        }
        _ => term.clone(),
    }
}

/// Converts a term into a formula in conjunctive normal form. This assumes the term is already in
/// negation normal form.
fn conjunctive_normal_form(term: &Rc<Term>) -> CnfFormula {
    match term.as_ref() {
        Term::Op(Operator::And, args) => {
            // If the term is a conjunction, we just convert every argument into conjunctive normal
            // form, and flatten the result
            args.iter().flat_map(conjunctive_normal_form).collect()
        }
        Term::Op(Operator::Or, args) => {
            // If the term is a disjunction, we have to convert every argument into conjunctive
            // normal form and then apply the distribution rules
            let args: Vec<_> = args.iter().map(conjunctive_normal_form).collect();
            distribute(&args)
        }
        // Every other term is considered a literal
        _ => vec![vec![term.clone()]],
    }
}

pub fn qnt_cnf(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let (l_bindings, phi, r_bindings, phi_prime) = {
        let (l, r) = match_term_err!((or (not l) r) = &conclusion[0])?;
        let (l_q, l_b, phi) = l.as_quant_err()?;
        let (r_q, r_b, phi_prime) = r.as_quant_err()?;

        // We expect both quantifiers to be `forall`
        assert_is_expected(&l_q, Quantifier::Forall)?;
        assert_is_expected(&r_q, Quantifier::Forall)?;

        (l_b, phi, r_b, phi_prime)
    };

    let r_bindings = r_bindings.iter().cloned().collect::<AHashSet<_>>();
    let mut new_bindings = l_bindings.iter().cloned().collect::<AHashSet<_>>();
    let clauses: Vec<_> = {
        let nnf = negation_normal_form(pool, phi, true, &mut AHashMap::new());
        let prenexed = prenex_forall(pool, &mut new_bindings, &nnf);
        let cnf = conjunctive_normal_form(&prenexed);
        cnf.into_iter()
            .map(|c| match c.as_slice() {
                [] => unreachable!(),
                [term] => term.clone(),
                _ => pool.add(Term::Op(Operator::Or, c)),
            })
            .collect()
    };

    // `new_bindings` contains all bindings that existed in the original term, plus all bindings
    // added by the prenexing step. All bindings in the right side must be in this set
    if let Some((var, _)) = r_bindings.iter().find(|b| !new_bindings.contains(b)) {
        return Err(CheckerError::Quant(
            QuantifierError::CnfNewBindingIntroduced(var.clone()),
        ));
    }

    let selected_clause = clauses
        .iter()
        .find(|&clause| clause == phi_prime)
        .ok_or_else(|| QuantifierError::ClauseDoesntAppearInCnf(phi_prime.clone()))?;

    // Cloning here may be unnecessary
    let free_vars = pool.free_vars(selected_clause).clone();

    // While all bindings in `r_bindings` must also be in `new_bindings`, the same is not true in
    // the opposite direction. That is because some variables from the set may be omitted in the
    // right-hand side quantifier if they don't appear in `phi_prime` as free variables.  If there
    // is a binding in the left side that is a free variable in the selected clause, but doesn't
    // appear in the right-hand side bindings, we must return an error
    let found = new_bindings
        .into_iter()
        .find(|var| !r_bindings.contains(var) && free_vars.contains(&pool.add(var.clone().into())));
    if let Some((var, _)) = found {
        return Err(QuantifierError::CnfBindingIsMissing(var).into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn forall_inst() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun a () Real)
                (declare-fun b () Real)
                (declare-fun x () Real)
            ",
            "Simple working examples" {
                "(step t1 (cl (or (not (forall ((p Bool)) p)) q))
                    :rule forall_inst :args ((:= p q)))": true,

                "(step t1 (cl (or (not (forall ((x Real) (y Real)) (= x y))) (= a b)))
                    :rule forall_inst :args ((:= x a) (:= y b)))": true,

                "(step t1 (cl (or (not (forall ((x Real)) (= x a))) (= a a)))
                    :rule forall_inst :args ((:= x a)))": true,

                "(step t1 (cl (or (not (forall ((p Bool)) p)) (ite q (= a b) (and (= a 0.0) true))))
                    :rule forall_inst :args ((:= p (ite q (= a b) (and (= a 0.0) true)))))": true,
            }
            "Equalities may be flipped" {
                "(step t1 (cl (or (not (forall ((x Real) (y Real)) (and (= x y) (= 1 0))))
                    (and (= b a) (= 1 0)))) :rule forall_inst :args ((:= x a) (:= y b)))": true,
            }
            "Argument is not in quantifier bindings" {
                "(step t1 (cl (or (not (forall ((x Real)) (= x a))) (= b 0.0)))
                    :rule forall_inst :args ((:= x b) (:= a 0.0)))": false,
            }
            "Binding has no associated substitution" {
                "(step t1 (cl (or (not (forall ((x Real) (y Real)) (= x x))) (= a a)))
                    :rule forall_inst :args ((:= x a)))": false,
            }
            "Substitution was not applied" {
                "(step t1 (cl (or (not (forall ((x Real) (y Real)) (= x y))) (= x b)))
                    :rule forall_inst :args ((:= x a) (:= y b)))": false,
            }
            "Applied substitution was not passed as argument" {
                "(step t1 (cl (or (not (forall ((x Real) (y Real)) (= x y))) (= a b)))
                    :rule forall_inst :args ((:= x a)))": false,
            }
            "Wrong type of rule argument" {
                "(step t1 (cl (or (not (forall ((x Real) (y Real)) (= x y))) (= a b)))
                    :rule forall_inst :args ((:= x a) b))": false,
            }
        }
    }

    #[test]
    fn qnt_join() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun a () Real)
                (declare-fun b () Real)
                (declare-fun x () Real)
            ",
            "Simple working examples" {
                "(step t1 (cl (=
                    (forall ((x Real)) (forall ((y Real)) (= x y)))
                    (forall ((x Real) (y Real)) (= x y))
                )) :rule qnt_join)": true,

                "(step t1 (cl (=
                    (forall ((x Real) (y Real)) (forall ((z Real) (w Real)) (= (+ x y) (+ z w))))
                    (forall ((x Real) (y Real) (z Real) (w Real)) (= (+ x y) (+ z w)))
                )) :rule qnt_join)": true,
            }
            "Bindings in wrong order" {
                "(step t1 (cl (=
                    (forall ((x Real)) (forall ((y Real)) (= x y)))
                    (forall ((y Real) (x Real)) (= x y))
                )) :rule qnt_join)": false,

                "(step t1 (cl (=
                    (forall ((x Real) (y Real)) (forall ((z Real) (w Real)) (= (+ x y) (+ z w))))
                    (forall ((z Real) (y Real) (w Real) (x Real)) (= (+ x y) (+ z w)))
                )) :rule qnt_join)": false,
            }
            "Removing duplicates" {
                "(step t1 (cl (=
                    (forall ((p Bool)) (forall ((p Bool)) p))
                    (forall ((p Bool)) p)
                )) :rule qnt_join)": true,

                "(step t1 (cl (=
                    (forall ((x Real) (y Real)) (forall ((y Real) (z Real)) (distinct x y z)))
                    (forall ((x Real) (y Real) (z Real)) (distinct x y z))
                )) :rule qnt_join)": true,

                "(step t1 (cl (=
                    (forall ((x Real) (y Real)) (forall ((x Real) (y Real)) (= x y)))
                    (forall ((x Real) (y Real)) (= x y))
                )) :rule qnt_join)": true,

                "(step t1 (cl (=
                    (forall ((x Real) (y Real)) (forall ((z Real) (x Real)) (distinct x y z)))
                    (forall ((x Real) (y Real) (z Real) (x Real)) (distinct x y z))
                )) :rule qnt_join)": false,
            }
        }
    }

    #[test]
    fn qnt_rm_unused() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun a () Real)
                (declare-fun b () Real)
                (declare-fun x () Real)
            ",
            "Simple working examples" {
                "(step t1 (cl (=
                    (forall ((x Real) (y Real) (z Real)) (= x z))
                    (forall ((x Real) (z Real)) (= x z))
                )) :rule qnt_rm_unused)": true,

                "(step t1 (cl (=
                    (forall ((x Real) (y Real) (z Real) (w Real)) (= y y))
                    (forall ((y Real)) (= y y))
                )) :rule qnt_rm_unused)": true,
            }
            "Bindings in wrong order" {
                "(step t1 (cl (=
                    (forall ((x Real) (y Real) (z Real)) (= x z))
                    (forall ((z Real) (x Real)) (= x z))
                )) :rule qnt_rm_unused)": false,
            }
            "Not all unused bindings were removed" {
                "(step t1 (cl (=
                    (forall ((x Real) (y Real) (z Real) (w Real)) (= y y))
                    (forall ((y Real) (w Real)) (= y y))
                )) :rule qnt_rm_unused)": false,
            }
        }
    }

    #[test]
    fn conjunctive_normal_form() {
        use super::*;
        use crate::parser::tests::*;

        fn to_cnf_term(pool: &mut dyn TPool, term: &Rc<Term>) -> Rc<Term> {
            let nnf = negation_normal_form(pool, term, true, &mut AHashMap::new());
            let mut bindings = Vec::new();
            let prenexed = prenex_forall(pool, &mut bindings, &nnf);
            let cnf = conjunctive_normal_form(&prenexed);
            let mut clauses: Vec<_> = cnf
                .into_iter()
                .map(|c| match c.as_slice() {
                    [] => unreachable!(),
                    [term] => term.clone(),
                    _ => pool.add(Term::Op(Operator::Or, c)),
                })
                .collect();

            let conjunctions = if clauses.len() == 1 {
                clauses.pop().unwrap()
            } else {
                pool.add(Term::Op(Operator::And, clauses))
            };

            if bindings.is_empty() {
                conjunctions
            } else {
                pool.add(Term::Quant(
                    Quantifier::Forall,
                    BindingList(bindings),
                    conjunctions,
                ))
            }
        }

        fn run_tests(definitions: &str, cases: &[(&str, &str)]) {
            for &(term, expected) in cases {
                let mut pool = crate::ast::pool::advanced::LocalPool::new();
                let [term, expected] = parse_terms(&mut pool, definitions, [term, expected]);
                let got = to_cnf_term(&mut pool, &term);
                assert_eq!(expected, got);
            }
        }

        let definitions = "
            (declare-fun p () Bool)
            (declare-fun q () Bool)
            (declare-fun r () Bool)
            (declare-fun s () Bool)
            (declare-fun a () Real)
            (declare-fun b () Real)
        ";
        let cases = [
            // Cases that only need the negation normal form to be computed
            ("(not (and p q r))", "(or (not p) (not q) (not r))"),
            ("(not (not p))", "p"),
            ("(=> p q)", "(or (not p) q)"),
            ("(not (=> p q))", "(and p (not q))"),
            ("(= p q)", "(and (or (not p) q) (or (not q) p))"),
            ("(ite p q r)", "(and (or (not p) q) (or p r))"),
            // Cases that require prenexing
            (
                "(or (forall ((x Int)) (= 0 x)) (forall ((y Int)) (= 1 y)))",
                "(forall ((x Int) (y Int)) (or (= 0 x) (= 1 y)))",
            ),
            (
                "(and (exists ((x Int)) (= 0 x)) (forall ((y Int)) (= 1 y)))",
                "(forall ((y Int)) (and (exists ((x Int)) (= 0 x)) (= 1 y)))",
            ),
            (
                "(=> (exists ((x Int)) (= x x)) p)",
                "(forall ((x Int)) (or (not (= x x)) p))",
            ),
            // Cases where the distribution rules must be applied
            ("(or p (and q r))", "(and (or p q) (or p r))"),
            (
                "(or (and p q) (and r s))",
                "(and (or p r) (or p s) (or q r) (or q s))",
            ),
            ("(or p (or q r) s)", "(or p q r s)"),
            ("(and p (and q r) s)", "(and p q r s)"),
            (
                "(not (and
                    (=> (forall ((x Int)) (= x 0)) p)
                    (or q (not (not r)))
                    (or s (not (exists ((y Int)) (< y 0))))
                ))",
                "(forall ((x Int)) (and
                    (or (= x 0) (not q) (not s))
                    (or (= x 0) (not q) (exists ((y Int)) (< y 0)))
                    (or (= x 0) (not r) (not s))
                    (or (= x 0) (not r) (exists ((y Int)) (< y 0)))
                    (or (not p) (not q) (not s))
                    (or (not p) (not q) (exists ((y Int)) (< y 0)))
                    (or (not p) (not r) (not s))
                    (or (not p) (not r) (exists ((y Int)) (< y 0)))
                ))",
            ),
        ];
        run_tests(definitions, &cases);
    }

    #[test]
    fn qnt_cnf() {
        test_cases! {
            definitions = "",
            "Simple working examples" {
                "(step t1 (cl (or (not (forall ((p Bool)) p)) (forall ((p Bool)) p)))
                    :rule qnt_cnf)": true,

                "(step t1 (cl (or
                    (not (forall ((p Bool) (q Bool)) (not (and p q))))
                    (forall ((p Bool) (q Bool)) (or (not p) (not q)))
                )) :rule qnt_cnf)": true,
            }
            "Selecting only one clause from conjunction" {
                "(step t1 (cl (or
                    (not (forall ((p Bool) (q Bool)) (or (and p true) (and q false))))
                    (forall ((p Bool) (q Bool)) (or true q))
                )) :rule qnt_cnf)": true,

                "(step t1 (cl (or
                    (not (forall ((p Bool) (q Bool))
                        (not (and (=> p q) (or q (not (not p))) (or true false (not q))))
                    ))
                    (forall ((p Bool) (q Bool)) (or p (not q) (not true)))
                )) :rule qnt_cnf)": true,
            }
            "Quantifier bindings added due to prenexing" {
                "(step t1 (cl (or
                    (not (forall ((p Bool)) (forall ((q Bool)) (or p q))))
                    (forall ((p Bool) (q Bool)) (or p q))
                )) :rule qnt_cnf)": true,

                "(step t1 (cl (or
                    (not (forall ((p Bool)) (not (exists ((q Bool)) (and p q)))))
                    (forall ((p Bool) (q Bool)) (or (not p) (not q)))
                )) :rule qnt_cnf)": true,

                "(step t1 (cl (or
                    (not (forall ((p Bool)) (or p (and false (forall ((q Bool)) q)))))
                    (forall ((p Bool)) (or p false))
                )) :rule qnt_cnf)": true,
            }
        }
    }
}
