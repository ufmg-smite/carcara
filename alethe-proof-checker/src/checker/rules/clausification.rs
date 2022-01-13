use super::{
    assert_clause_len, assert_eq, assert_is_expected, assert_is_expected_modulo_reordering,
    assert_num_premises, assert_operation_len, get_premise_term, CheckerError, EqualityError,
    RuleArgs, RuleResult,
};
use crate::ast::*;
use ahash::AHashMap;

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
        args if *pool.sort(&args[0]) == Sort::Bool => {
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

pub fn and(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let and_term = get_premise_term(&premises[0])?;
    let and_contents = match_term_err!((and ...) = and_term)?;

    if !and_contents.contains(&conclusion[0]) {
        return Err(CheckerError::TermDoesntApperInOp(
            Operator::And,
            conclusion[0].clone(),
        ));
    }
    Ok(())
}

pub fn not_or(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let or_term = get_premise_term(&premises[0])?;
    let or_contents = match_term_err!((not (or ...)) = or_term)?;
    let conclusion = conclusion[0].remove_negation_err()?;

    if !or_contents.contains(conclusion) {
        return Err(CheckerError::TermDoesntApperInOp(
            Operator::Or,
            conclusion.clone(),
        ));
    }
    Ok(())
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
    fn expand_assoc(pool: &mut TermPool, op: Operator, args: &[Rc<Term>], case: Case) -> Rc<Term> {
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
            _ => unreachable!(),
        };
        pool.add_term(Term::Op(op, new_args))
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
                .map(|args| pool.add_term(Term::Op(*op, args.to_vec())))
                .collect();
            pool.add_term(Term::Op(Operator::And, and_args))
        }
        assoc_case => expand_assoc(pool, *op, args, assoc_case),
    };
    assert_is_expected(result, expected)
}

/// The first simplification step for `bfun_elim`, that expands quantifiers over boolean variables.
fn bfun_elim_first_step(
    pool: &mut TermPool,
    bindigns: &[SortedVar],
    term: &Rc<Term>,
    acc: &mut Vec<Rc<Term>>,
) -> Result<(), SubstitutionError> {
    let var = match bindigns {
        [.., var] if var.1.as_sort() == Some(&Sort::Bool) => pool.add_term(var.clone().into()),
        [rest @ .., _] => return bfun_elim_first_step(pool, rest, term, acc),
        [] => {
            acc.push(term.clone());
            return Ok(());
        }
    };
    for value in [pool.bool_false(), pool.bool_true()] {
        let mut substitution = Substitution::single(pool, var.clone(), value)?;
        let term = substitution.apply(pool, term)?;
        bfun_elim_first_step(pool, &bindigns[..bindigns.len() - 1], &term, acc)?
    }
    Ok(())
}

/// The second simplification step for `bfun_elim`, that expands function applications over
/// non-constant boolean arguments into `ite` terms.
fn bfun_elim_second_step(
    pool: &mut TermPool,
    func: &Rc<Term>,
    args: &[Rc<Term>],
    processed: usize,
) -> Rc<Term> {
    for i in processed..args.len() {
        if *pool.sort(&args[i]) == Sort::Bool && !args[i].is_bool_false() && !args[i].is_bool_true()
        {
            let mut ite_args = Vec::with_capacity(3);
            ite_args.push(args[i].clone());

            for bool_constant in [pool.bool_true(), pool.bool_false()] {
                let mut new_args = args.to_vec();
                new_args[i] = bool_constant;
                let inner_term = bfun_elim_second_step(pool, func, &new_args, i + 1);
                ite_args.push(inner_term)
            }
            return pool.add_term(Term::Op(Operator::Ite, ite_args));
        }
    }

    // If there were no non-constant boolean arguments we don't need to expand the term into an ite
    // term. So we just contruct the original application term and return it.
    pool.add_term(Term::App(func.clone(), args.to_vec()))
}

/// Applies the simplification steps for the `bfun_elim` rule.
fn apply_bfun_elim(
    pool: &mut TermPool,
    term: &Rc<Term>,
    cache: &mut AHashMap<Rc<Term>, Rc<Term>>,
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
            pool.add_term(Term::Op(*op, args))
        }
        Term::Quant(q, bindings, inner) => {
            let op = match q {
                Quantifier::Forall => Operator::And,
                Quantifier::Exists => Operator::Or,
            };
            let mut args = Vec::with_capacity(2usize.pow(bindings.len() as u32));
            bfun_elim_first_step(pool, bindings.as_slice(), inner, &mut args)?;

            let op_term = if args.len() == 1 {
                args.pop().unwrap()
            } else {
                pool.add_term(Term::Op(op, args))
            };
            let op_term = apply_bfun_elim(pool, &op_term, cache)?;

            let new_bindings: Vec<_> = bindings
                .iter()
                .cloned()
                .filter(|(_, sort)| *sort.as_sort().unwrap() != Sort::Bool)
                .collect();
            if new_bindings.is_empty() {
                op_term
            } else {
                pool.add_term(Term::Quant(*q, BindingList(new_bindings), op_term))
            }
        }
        Term::Choice(var, inner) => {
            let inner = apply_bfun_elim(pool, inner, cache)?;
            pool.add_term(Term::Choice(var.clone(), inner))
        }
        Term::Let(bindings, inner) => {
            let inner = apply_bfun_elim(pool, inner, cache)?;
            pool.add_term(Term::Let(bindings.clone(), inner))
        }
        Term::Lambda(bindings, inner) => {
            let inner = apply_bfun_elim(pool, inner, cache)?;
            pool.add_term(Term::Lambda(bindings.clone(), inner))
        }
        _ => term.clone(),
    };

    cache.insert(term.clone(), result.clone());
    Ok(result)
}

pub fn bfun_elim(RuleArgs { conclusion, premises, pool, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let psi = get_premise_term(&premises[0])?;

    let expected = apply_bfun_elim(pool, psi, &mut AHashMap::new())?;
    assert_is_expected_modulo_reordering(&conclusion[0], expected)
}

#[cfg(test)]
mod tests {
    #[test]
    fn distinct_elim() {
        test_cases! {
            definitions = "
                (declare-sort T 0)
                (declare-fun a () T)
                (declare-fun b () T)
                (declare-fun c () T)
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (= (distinct a b) (not (= a b)))) :rule distinct_elim)": true,

                "(step t1 (cl (= (distinct a b c) (and
                    (not (= a b))
                    (not (= a c))
                    (not (= b c))
                ))) :rule distinct_elim)": true,
            }
            "Inequality terms in different orders" {
                "(step t1 (cl (= (distinct a b) (not (= b a)))) :rule distinct_elim)": true,

                "(step t1 (cl (= (distinct a b c) (and
                    (not (= b a))
                    (not (= a c))
                    (not (= c b))
                ))) :rule distinct_elim)": true,
            }
            "Conjunction terms in wrong order" {
                "(step t1 (cl (= (distinct a b c) (and
                    (not (= b c))
                    (not (= a b))
                    (not (= a c))
                ))) :rule distinct_elim)": false,
            }
            "\"distinct\" on more than two booleans should be \"false\"" {
                "(step t1 (cl (= (distinct p q r) false)) :rule distinct_elim)": true,

                "(step t1 (cl (= (distinct p q r) (and
                    (not (= p q))
                    (not (= p r))
                    (not (= q r))
                ))) :rule distinct_elim)": false,
            }
        }
    }

    #[test]
    fn and() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
            ",
            "Simple working examples" {
                "(assume h1 (and p q))
                (step t2 (cl q) :rule and :premises (h1))": true,

                "(assume h1 (and p q r s))
                (step t2 (cl p) :rule and :premises (h1))": true,

                "(assume h1 (and p q r s))
                (step t2 (cl s) :rule and :premises (h1))": true,
            }
            "Number of premises != 1" {
                "(step t1 (cl p) :rule and)": false,

                "(assume h1 (and p q))
                (assume h2 (and r s))
                (step t2 (cl r) :rule and :premises (h1 h2))": false,
            }
            "Premise clause has more than one term" {
                "(step t1 (cl (and p q) (and r s)) :rule trust)
                (step t2 (cl p) :rule and :premises (t1))": false,
            }
            "Conclusion clause does not have exactly one term" {
                "(assume h1 (and p q r s))
                (step t2 (cl q s) :rule and :premises (h1))": false,

                "(assume h1 (and p q))
                (step t2 (cl) :rule and :premises (h1))": false,
            }
            "Premise is not an \"and\" operation" {
                "(assume h1 (or p q r s))
                (step t2 (cl r) :rule and :premises (h1))": false,
            }
            "Conclusion term is not in premise" {
                "(assume h1 (and p q r))
                (step t2 (cl s) :rule and :premises (h1))": false,
            }
        }
    }

    #[test]
    fn not_or() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
            ",
            "Simple working examples" {
                "(assume h1 (not (or p q)))
                (step t2 (cl (not q)) :rule not_or :premises (h1))": true,

                "(assume h1 (not (or p q r s)))
                (step t2 (cl (not p)) :rule not_or :premises (h1))": true,
            }
            "Conclusion clause is of the wrong form" {
                "(assume h1 (not (or p q r s)))
                (step t2 (cl (not q) (not s)) :rule not_or :premises (h1))": false,

                "(assume h1 (not (or p q)))
                (step t2 (cl q) :rule not_or :premises (h1))": false,
            }
            "Premise is of the wrong form" {
                "(assume h1 (not (and p q r s)))
                (step t2 (cl (not r)) :rule not_or :premises (h1))": false,

                "(assume h1 (or p q r s))
                (step t2 (cl (not r)) :rule not_or :premises (h1))": false,
            }
            "Conclusion term is not in premise" {
                "(assume h1 (not (or p q r)))
                (step t2 (cl (not s)) :rule not_or :premises (h1))": false,
            }
        }
    }

    #[test]
    fn or() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
            ",
            "Simple working examples" {
                "(assume h1 (or p q))
                (step t2 (cl p q) :rule or :premises (h1))": true,

                "(assume h1 (or p q r s))
                (step t2 (cl p q r s) :rule or :premises (h1))": true,
            }
            "Number of premises != 1" {
                "(step t1 (cl p q r) :rule or)": false,

                "(assume h1 (or p q))
                (assume h2 (or q r))
                (step t3 (cl p q r) :rule or :premises (h1 h2))": false,
            }
            "Premise clause has more than one term" {
                "(assume h1 (or p (or q r)))
                (step t2 (cl p (or q r)) :rule or :premises (h1))
                (step t3 (cl p q) :rule or :premises (t2))": false,
            }
            "Premise is not an \"or\" operation" {
                "(assume h1 (and p q))
                (step t2 (cl p q) :rule or :premises (h1))": false,
            }
            "Premise and clause contents are different" {
                "(assume h1 (or p q))
                (step t2 (cl r s) :rule or :premises (h1))": false,

                "(assume h1 (or p q r))
                (step t2 (cl p q) :rule or :premises (h1))": false,

                "(assume h1 (or q p))
                (step t2 (cl p q) :rule or :premises (h1))": false,
            }
        }
    }

    #[test]
    fn not_and() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
            ",
            "Simple working examples" {
                "(assume h1 (not (and p q)))
                (step t2 (cl (not p) (not q)) :rule not_and :premises (h1))": true,

                "(assume h1 (not (and p q r s)))
                (step t2 (cl (not p) (not q) (not r) (not s)) :rule not_and :premises (h1))": true,
            }
            "Premise is of the wrong form" {
                "(assume h1 (and p q))
                (step t2 (cl (not p) (not q)) :rule not_and :premises (h1))": false,

                "(assume h1 (not (or p q)))
                (step t2 (cl (not p) (not q)) :rule not_and :premises (h1))": false,
            }
            "Premise and clause contents are different" {
                "(assume h1 (not (and p q)))
                (step t2 (cl (not r) (not s)) :rule not_and :premises (h1))": false,

                "(assume h1 (not (and p q r)))
                (step t2 (cl (not p) (not q)) :rule not_and :premises (h1))": false,

                "(assume h1 (not (and q p)))
                (step t2 (cl (not p) (not q)) :rule not_and :premises (h1))": false,
            }
        }
    }

    #[test]
    fn implies() {
        test_cases! {
            definitions = "
                (declare-fun a () Bool)
                (declare-fun b () Bool)
            ",
            "Simple working examples" {
                "(assume h1 (=> a b))
                (step t2 (cl (not a) b) :rule implies :premises (h1))": true,

                "(assume h1 (=> (not a) b))
                (step t2 (cl (not (not a)) b) :rule implies :premises (h1))": true,
            }
            "Premise term is not an \"implies\" term" {
                "(assume h1 (= a b))
                (step t2 (cl (not a) b) :rule implies :premises (h1))": false,
            }
            "Conclusion clause is of the wrong form" {
                "(assume h1 (=> a b))
                (step t2 (cl b (not a)) :rule implies :premises (h1))": false,

                "(assume h1 (=> a b))
                (step t2 (cl a (not b)) :rule implies :premises (h1))": false,

                "(assume h1 (=> (not a) b))
                (step t2 (cl a b) :rule implies :premises (h1))": false,
            }
        }
    }

    #[test]
    fn not_implies1() {
        test_cases! {
            definitions = "
                (declare-fun a () Bool)
                (declare-fun b () Bool)
            ",
            "Simple working examples" {
                "(assume h1 (not (=> a b)))
                (step t2 (cl a) :rule not_implies1 :premises (h1))": true,

                "(assume h1 (not (=> (not a) b)))
                (step t2 (cl (not a)) :rule not_implies1 :premises (h1))": true,
            }
            "Premise term is of the wrong form" {
                "(assume h1 (=> a b))
                (step t2 (cl a) :rule not_implies1 :premises (h1))": false,

                "(assume h1 (not (= a b)))
                (step t2 (cl a) :rule not_implies1 :premises (h1))": false,
            }
            "Conclusion clause is of the wrong form" {
                "(assume h1 (not (=> a b)))
                (step t2 (cl (not a)) :rule not_implies1 :premises (h1))": false,

                "(assume h1 (not (=> a b)))
                (step t2 (cl b) :rule not_implies1 :premises (h1))": false,
            }
        }
    }

    #[test]
    fn not_implies2() {
        test_cases! {
            definitions = "
                (declare-fun a () Bool)
                (declare-fun b () Bool)
            ",
            "Simple working examples" {
                "(assume h1 (not (=> a b)))
                (step t2 (cl (not b)) :rule not_implies2 :premises (h1))": true,

                "(assume h1 (not (=> a (not b))))
                (step t2 (cl (not (not b))) :rule not_implies2 :premises (h1))": true,
            }
            "Premise term is of the wrong form" {
                "(assume h1 (=> a b))
                (step t2 (cl (not b)) :rule not_implies2 :premises (h1))": false,

                "(assume h1 (not (= a b)))
                (step t2 (cl (not b)) :rule not_implies2 :premises (h1))": false,
            }
            "Conclusion clause is of the wrong form" {
                "(assume h1 (not (=> a b)))
                (step t2 (cl b) :rule not_implies2 :premises (h1))": false,

                "(assume h1 (not (=> a b)))
                (step t2 (cl (not a)) :rule not_implies2 :premises (h1))": false,
            }
        }
    }

    #[test]
    fn nary_elim() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
                (declare-fun a () Int)
                (declare-fun b () Int)
                (declare-fun c () Int)
                (declare-fun d () Int)
            ",
            "Chainable operators" {
                "(step t1 (cl (= (= a b c d) (and (= a b) (= b c) (= c d)))) :rule nary_elim)": true,
                "(step t1 (cl (= (= a b) (and (= a b)))) :rule nary_elim)": true,
                "(step t1 (cl (= (= a b c) (and (= b c) (= a b)))) :rule nary_elim)": false,
                "(step t1 (cl (= (= a b c d) (and (= a b) (= c d)))) :rule nary_elim)": false,
            }
            "Left associative operators" {
                "(step t1 (cl (= (+ a b c d) (+ (+ (+ a b) c) d))) :rule nary_elim)": true,
                "(step t1 (cl (= (* a b) (* a b))) :rule nary_elim)": true,
                "(step t1 (cl (= (- a b c d) (- a (- b (- c d))))) :rule nary_elim)": false,
                "(step t1 (cl (= (+ a b c d) (+ (+ (+ d c) b) a))) :rule nary_elim)": false,
            }
            "Right associative operators" {
                "(step t1 (cl (= (=> p q r s) (=> p (=> q (=> r s))))) :rule nary_elim)": true,
                "(step t1 (cl (= (=> p q) (=> p q))) :rule nary_elim)": true,
                "(step t1 (cl (= (=> p q r s) (=> (=> (=> p q) r) s))) :rule nary_elim)": false,
            }
            "Clause term is not of the correct form" {
                "(step t1 (cl (= (or p q r s) (or (or (or p q) r) s))) :rule nary_elim)": false,
                "(step t1 (cl (= (- a) (- a))) :rule nary_elim)": false,
                "(step t1 (cl (= (=> p (=> q (=> r s))) (=> p q r s))) :rule nary_elim)": false,
            }
        }
    }

    #[test]
    fn bfun_elim() {
        test_cases! {
            definitions = "
                (declare-fun f (Bool) Bool)
                (declare-fun g (Bool Bool Bool) Bool)
                (declare-fun h (Int Bool Real) Bool)
                (declare-fun a () Bool)
                (declare-fun b () Bool)
                (declare-fun c () Bool)
            ",
            "First step" {
                "(assume h1 (forall ((x Bool)) (f x)))
                (step t1 (cl (and (f false) (f true))) :rule bfun_elim :premises (h1))": true,

                "(assume h1 (exists ((x Int) (y Bool)) (f y)))
                (step t1 (cl (exists ((x Int)) (or (f false) (f true))))
                    :rule bfun_elim :premises (h1))": true,

                "(assume h1 (exists ((x Bool) (y Bool) (z Bool)) (g x y z)))
                (step t1 (cl (or
                    (g false false false)
                    (g true false false)
                    (g false true false)
                    (g true true false)
                    (g false false true)
                    (g true false true)
                    (g false true true)
                    (g true true true)
                )) :rule bfun_elim :premises (h1))": true,
            }
            "Second step" {
                "(assume h1 (f a))
                (step t1 (cl (ite a (f true) (f false))) :rule bfun_elim :premises (h1))": true,

                "(assume h1 (h 1 a 0.0))
                (step t1 (cl (ite a (h 1 true 0.0) (h 1 false 0.0)))
                    :rule bfun_elim :premises (h1))": true,

                "(assume h1 (g a b c))
                (step t1 (cl (ite a
                    (ite b
                        (ite c (g true true true) (g true true false))
                        (ite c (g true false true) (g true false false)))
                    (ite b
                        (ite c (g false true true) (g false true false))
                        (ite c (g false false true) (g false false false)))
                )) :rule bfun_elim :premises (h1))": true,
            }
            "Both steps" {
                "(assume h1 (exists ((x Bool)) (and x (f a))))
                (step t1 (cl (or
                    (and false (ite a (f true) (f false)))
                    (and true (ite a (f true) (f false)))
                )) :rule bfun_elim :premises (h1))": true,

                "(assume h1 (forall ((x Bool) (y Bool)) (g x a y)))
                (step t1 (cl (and
                    (ite a (g false true false) (g false false false))
                    (ite a (g true true false) (g true false false))
                    (ite a (g false true true) (g false false true))
                    (ite a (g true true true) (g true false true))
                )) :rule bfun_elim :premises (h1))": true,
            }
        }
    }
}
