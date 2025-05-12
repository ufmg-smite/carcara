use super::{
    assert_clause_len, assert_eq, assert_is_expected, assert_num_args, assert_num_premises,
    assert_operation_len, assert_polyeq_expected, get_premise_term, CheckerError, EqualityError,
    RuleArgs, RuleResult,
};
use crate::ast::*;
use indexmap::IndexMap;

pub fn distinct_elim(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let (distinct_args, second_term) = match_term_err!((= (distinct ...) second) = &conclusion[0])?;
    match distinct_args {
        [] | [_] => unreachable!(),
        [a, b] => {
            let got = match_term_err!((not (= x y)) = second_term)?;
            if got == (a, b) || got == (b, a) {
                Ok(())
            } else {
                let expected = build_term!(pool, (not (= {a.clone()} {b.clone()})));
                Err(EqualityError::ExpectedToBe { expected, got: second_term.clone() }.into())
            }
        }
        // If there are more than two boolean arguments to the distinct operator, the
        // second term must be `false`
        args if pool.sort(&args[0]).as_sort().unwrap() == &Sort::Bool => {
            if second_term.is_bool_false() {
                Ok(())
            } else {
                Err(CheckerError::ExpectedBoolConstant(
                    false,
                    second_term.clone(),
                ))
            }
        }

        args => {
            let n = args.len();
            let and_args = match_term_err!((and ...) = second_term)?;
            assert_operation_len(Operator::And, and_args, n * (n - 1) / 2)?;

            let mut k = 0;
            for i in 0..n {
                for j in (i + 1)..n {
                    let (a, b) = (&args[i], &args[j]);
                    let got = match_term_err!((not (= x y)) = &and_args[k])?;
                    if !(got == (a, b) || got == (b, a)) {
                        let expected = build_term!(pool, (not (= {a.clone()} {b.clone()})));
                        return Err(EqualityError::ExpectedToBe {
                            expected,
                            got: and_args[k].clone(),
                        }
                        .into());
                    }
                    k += 1;
                }
            }
            Ok(())
        }
    }
}

pub fn and(RuleArgs { conclusion, premises, args, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_num_args(args, 1)?;
    assert_clause_len(conclusion, 1)?;

    let and_term = get_premise_term(&premises[0])?;
    let and_contents = match_term_err!((and ...) = and_term)?;
    let i = args[0].as_usize_err()?;

    if i >= and_contents.len() {
        return Err(CheckerError::NoIthChildInTerm(i, and_term.clone()));
    }

    assert_eq(&conclusion[0], &and_contents[i])
}

pub fn not_or(RuleArgs { conclusion, premises, args, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_num_args(args, 1)?;
    assert_clause_len(conclusion, 1)?;

    let or_term = get_premise_term(&premises[0])?;
    let or_contents = match_term_err!((not (or ...)) = or_term)?;
    let conclusion = conclusion[0].remove_negation_err()?;
    let i = args[0].as_usize_err()?;

    if i >= or_contents.len() {
        return Err(CheckerError::NoIthChildInTerm(i, or_term.clone()));
    }

    assert_eq(conclusion, &or_contents[i])
}

pub fn or(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;

    let or_term = get_premise_term(&premises[0])?;
    let or_contents = match_term_err!((or ...) = or_term)?;

    assert_clause_len(conclusion, or_contents.len())?;
    for (t, u) in or_contents.iter().zip(conclusion) {
        assert_eq(t, u)?;
    }
    Ok(())
}

pub fn not_and(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;

    let and_term = get_premise_term(&premises[0])?;
    let and_contents = match_term_err!((not (and ...)) = and_term)?;

    assert_clause_len(conclusion, and_contents.len())?;
    for (t, u) in and_contents.iter().zip(conclusion) {
        let u = u.remove_negation_err()?;
        assert_eq(t, u)?;
    }
    Ok(())
}

pub fn xor1(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;

    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2) = match_term_err!((xor phi_1 phi_2) = premise_term)?;

    assert_eq(phi_1, &conclusion[0])?;
    assert_eq(phi_2, &conclusion[1])
}

pub fn xor2(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;

    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2) = match_term_err!((xor phi_1 phi_2) = premise_term)?;

    assert_eq(phi_1, conclusion[0].remove_negation_err()?)?;
    assert_eq(phi_2, conclusion[1].remove_negation_err()?)
}

pub fn not_xor1(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;

    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2) = match_term_err!((not (xor phi_1 phi_2)) = premise_term)?;

    assert_eq(phi_1, &conclusion[0])?;
    assert_eq(phi_2, conclusion[1].remove_negation_err()?)
}

pub fn not_xor2(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;

    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2) = match_term_err!((not (xor phi_1 phi_2)) = premise_term)?;

    assert_eq(phi_1, conclusion[0].remove_negation_err()?)?;
    assert_eq(phi_2, &conclusion[1])
}

pub fn implies(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 2)?;

    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, phi_2) = match_term_err!((=> phi_1 phi_2) = premise_term)?;

    assert_eq(phi_1, conclusion[0].remove_negation_err()?)?;
    assert_eq(phi_2, &conclusion[1])
}

pub fn not_implies1(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let premise_term = get_premise_term(&premises[0])?;
    let (phi_1, _) = match_term_err!((not (=> phi_1 phi_2)) = premise_term)?;

    assert_eq(phi_1, &conclusion[0])
}

pub fn not_implies2(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let premise_term = get_premise_term(&premises[0])?;
    let (_, phi_2) = match_term_err!((not (=> phi_1 phi_2)) = premise_term)?;

    assert_eq(phi_2, conclusion[0].remove_negation_err()?)
}

pub fn nary_elim(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    /// The three possible cases for n-ary operators: chainable, right associative and left
    /// associative
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Case {
        Chainable,
        RightAssoc,
        LeftAssoc,
    }

    /// A function to expand terms that fall in the right or left associative cases. For example,
    /// the term `(=> p q r s)` will be expanded into the term `(=> p (=> q (=> r s)))`.
    fn expand_assoc(
        pool: &mut dyn TermPool,
        op: Operator,
        args: &[Rc<Term>],
        case: Case,
    ) -> Rc<Term> {
        let (head, tail) = match args {
            [] => unreachable!(),
            [t] => return t.clone(),

            // The "head" term will be the first or last term in `args`, depending on if the
            // operator is right or left associative
            [first, rest @ ..] if case == Case::RightAssoc => (first, rest),
            [rest @ .., last] => (last, rest),
        };

        // Note: if the argument list if very long, this may overflow the stack
        let nested = expand_assoc(pool, op, tail, case);

        let new_args = match case {
            Case::RightAssoc => vec![head.clone(), nested],
            Case::LeftAssoc => vec![nested, head.clone()],
            Case::Chainable => unreachable!(),
        };
        pool.add(Term::Op(op, new_args))
    }

    assert_clause_len(conclusion, 1)?;

    let (original, result) = match_term_err!((= o r) = &conclusion[0])?;

    let (op, args) = match original.as_ref() {
        Term::Op(op, args) if args.len() >= 2 => (op, args),
        _ => return Err(CheckerError::NotValidNaryTerm(original.clone())),
    };

    let case = match op {
        Operator::Equals => Case::Chainable,
        Operator::Add | Operator::Sub | Operator::Mult => Case::LeftAssoc,
        Operator::Implies => Case::RightAssoc,
        _ => return Err(CheckerError::NotValidNaryTerm(original.clone())),
    };

    let expected = match case {
        Case::Chainable => {
            let and_args: Vec<_> = args
                .windows(2)
                .map(|args| pool.add(Term::Op(*op, args.to_vec())))
                .collect();
            pool.add(Term::Op(Operator::And, and_args))
        }
        assoc_case => expand_assoc(pool, *op, args, assoc_case),
    };
    assert_is_expected(result, expected)
}

/// The first simplification step for `bfun_elim`, that expands quantifiers over boolean variables.
fn bfun_elim_first_step(
    pool: &mut dyn TermPool,
    bindigns: &[SortedVar],
    term: &Rc<Term>,
    acc: &mut Vec<Rc<Term>>,
) -> Result<(), SubstitutionError> {
    let var = match bindigns {
        [.., var] if var.1.as_sort() == Some(&Sort::Bool) => pool.add(var.clone().into()),
        [rest @ .., _] => return bfun_elim_first_step(pool, rest, term, acc),
        [] => {
            acc.push(term.clone());
            return Ok(());
        }
    };
    for value in [pool.bool_false(), pool.bool_true()] {
        let mut substitution = Substitution::single(pool, var.clone(), value)?;
        let term = substitution.apply(pool, term);
        bfun_elim_first_step(pool, &bindigns[..bindigns.len() - 1], &term, acc)?;
    }
    Ok(())
}

/// The second simplification step for `bfun_elim`, that expands function applications over
/// non-constant boolean arguments into `ite` terms.
fn bfun_elim_second_step(
    pool: &mut dyn TermPool,
    func: &Rc<Term>,
    args: &[Rc<Term>],
    processed: usize,
) -> Rc<Term> {
    for i in processed..args.len() {
        if pool.sort(&args[i]).as_sort().unwrap() == &Sort::Bool
            && !args[i].is_bool_false()
            && !args[i].is_bool_true()
        {
            let mut ite_args = Vec::with_capacity(3);
            ite_args.push(args[i].clone());

            for bool_constant in [pool.bool_true(), pool.bool_false()] {
                let mut new_args = args.to_vec();
                new_args[i] = bool_constant;
                let inner_term = bfun_elim_second_step(pool, func, &new_args, i + 1);
                ite_args.push(inner_term);
            }
            return pool.add(Term::Op(Operator::Ite, ite_args));
        }
    }

    // If there were no non-constant boolean arguments we don't need to expand the term into an ite
    // term. So we just construct the original application term and return it.
    pool.add(Term::App(func.clone(), args.to_vec()))
}

/// Applies the simplification steps for the `bfun_elim` rule.
fn apply_bfun_elim(
    pool: &mut dyn TermPool,
    term: &Rc<Term>,
    cache: &mut IndexMap<Rc<Term>, Rc<Term>>,
) -> Result<Rc<Term>, SubstitutionError> {
    if let Some(v) = cache.get(term) {
        return Ok(v.clone());
    }

    let result = match term.as_ref() {
        Term::App(f, args) => {
            let args: Vec<_> = args
                .iter()
                .map(|a| apply_bfun_elim(pool, a, cache))
                .collect::<Result<_, _>>()?;
            bfun_elim_second_step(pool, f, &args, 0)
        }
        Term::Op(op, args) => {
            let args = args
                .iter()
                .map(|a| apply_bfun_elim(pool, a, cache))
                .collect::<Result<_, _>>()?;
            pool.add(Term::Op(*op, args))
        }
        Term::Binder(b, bindings, inner) => {
            let op = match b {
                Binder::Forall => Operator::And,
                Binder::Exists => Operator::Or,
                Binder::Choice | Binder::Lambda => {
                    let inner = apply_bfun_elim(pool, inner, cache)?;
                    let result = pool.add(Term::Binder(*b, bindings.clone(), inner));
                    cache.insert(term.clone(), result.clone());
                    return Ok(result);
                }
            };
            let mut args = Vec::with_capacity(2usize.pow(bindings.len() as u32));
            bfun_elim_first_step(pool, bindings.as_slice(), inner, &mut args)?;

            let op_term = if args.len() == 1 {
                args.pop().unwrap()
            } else {
                pool.add(Term::Op(op, args))
            };
            let op_term = apply_bfun_elim(pool, &op_term, cache)?;

            let new_bindings: Vec<_> = bindings
                .iter()
                .filter(|(_, sort)| *sort.as_sort().unwrap() != Sort::Bool)
                .cloned()
                .collect();
            if new_bindings.is_empty() {
                op_term
            } else {
                pool.add(Term::Binder(*b, BindingList(new_bindings), op_term))
            }
        }
        Term::Let(bindings, inner) => {
            let inner = apply_bfun_elim(pool, inner, cache)?;
            pool.add(Term::Let(bindings.clone(), inner))
        }
        _ => term.clone(),
    };

    cache.insert(term.clone(), result.clone());
    Ok(result)
}

pub fn bfun_elim(
    RuleArgs {
        conclusion,
        premises,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let psi = get_premise_term(&premises[0])?;

    let expected = apply_bfun_elim(pool, psi, &mut IndexMap::new())?;
    assert_polyeq_expected(&conclusion[0], expected, polyeq_time)
}
