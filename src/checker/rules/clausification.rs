use super::{get_single_term_from_command, to_option, RuleArgs};
use crate::ast::*;
use ahash::AHashMap;

pub fn distinct_elim(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    rassert!(conclusion.len() == 1);

    let (distinct_args, second_term) = match_term!((= (distinct ...) second) = conclusion[0])?;
    match distinct_args {
        [] | [_] => unreachable!(),
        [a, b] => {
            let got: (&Term, &Term) = match_term!((not (= x y)) = second_term)?;
            to_option(got == (a, b) || got == (b, a))
        }
        args => {
            if args[0].sort() == Term::BOOL_SORT {
                // If there are more than two boolean arguments to the distinct operator, the
                // second term must be "false"
                return to_option(second_term.is_bool_false());
            }
            let got = match_term!((and ...) = second_term)?;
            let mut k = 0;
            for i in 0..args.len() {
                for j in i + 1..args.len() {
                    let (a, b) = (args[i].as_ref(), args[j].as_ref());
                    let got = match_term!((not (= x y)) = got[k])?;
                    to_option(got == (a, b) || got == (b, a))?;
                    k += 1;
                }
            }
            Some(())
        }
    }
}

pub fn and(RuleArgs { conclusion, premises, .. }: RuleArgs) -> Option<()> {
    rassert!(premises.len() == 1 && conclusion.len() == 1);

    let and_term = get_single_term_from_command(premises[0])?;
    let and_contents = match_term!((and ...) = and_term)?;

    to_option(and_contents.iter().any(|t| t == &conclusion[0]))
}

pub fn not_or(RuleArgs { conclusion, premises, .. }: RuleArgs) -> Option<()> {
    rassert!(premises.len() == 1 && conclusion.len() == 1);

    let or_term = get_single_term_from_command(premises[0])?;
    let or_contents = match_term!((not (or ...)) = or_term)?;
    let conclusion = conclusion[0].remove_negation()?;

    to_option(or_contents.iter().any(|t| t.as_ref() == conclusion))
}

pub fn or(RuleArgs { conclusion, premises, .. }: RuleArgs) -> Option<()> {
    rassert!(premises.len() == 1);

    let or_term = get_single_term_from_command(premises[0])?;
    let or_contents = match_term!((or ...) = or_term)?;

    to_option(or_contents == conclusion)
}

pub fn not_and(RuleArgs { conclusion, premises, .. }: RuleArgs) -> Option<()> {
    rassert!(premises.len() == 1);

    let and_term = get_single_term_from_command(premises[0])?;
    let and_contents = match_term!((not (and ...)) = and_term)?;
    to_option(
        conclusion
            .iter()
            .map(|t| t.remove_negation())
            .eq(and_contents.iter().map(|t| Some(t.as_ref()))),
    )
}

pub fn implies(RuleArgs { conclusion, premises, .. }: RuleArgs) -> Option<()> {
    rassert!(premises.len() == 1 && conclusion.len() == 2);
    let premise_term = get_single_term_from_command(premises[0])?;
    let (phi_1, phi_2) = match_term!((=> phi_1 phi_2) = premise_term)?;
    to_option(phi_1 == conclusion[0].remove_negation()? && phi_2 == conclusion[1].as_ref())
}

pub fn not_implies1(RuleArgs { conclusion, premises, .. }: RuleArgs) -> Option<()> {
    rassert!(premises.len() == 1 && conclusion.len() == 1);
    let premise_term = get_single_term_from_command(premises[0])?;
    let (phi_1, _) = match_term!((not (=> phi_1 phi_2)) = premise_term)?;
    to_option(phi_1 == conclusion[0].as_ref())
}

pub fn not_implies2(RuleArgs { conclusion, premises, .. }: RuleArgs) -> Option<()> {
    rassert!(premises.len() == 1 && conclusion.len() == 1);
    let premise_term = get_single_term_from_command(premises[0])?;
    let (_, phi_2) = match_term!((not (=> phi_1 phi_2)) = premise_term)?;
    to_option(phi_2 == conclusion[0].remove_negation()?)
}

pub fn nary_elim(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    // The three possible cases for n-ary operators: chainable, right associative and left
    // associative
    #[derive(Debug, PartialEq, Eq)]
    enum Case {
        Chainable,
        RightAssoc,
        LeftAssoc,
    }

    // A function to check the right and left associative cases. Consider as an example the
    // term (=> p q r s) being transformed into the term (=> p (=> q (=> r s))). This function
    // checks that the operators match, checks that the head argument "p" matches the left-hand
    // argument in the result term (as the operator is right associative) and then calls itself
    // recursively passing the "tail" (=> q r s) and the right-hand argument (=> q (=> r s)).
    // If the operator was right associative, the "head" argument would be the last, and the
    // nested term would be the left-hand arugment of the result term. In the base case, the
    // function will be called with the terms (=> s) and s, and it only needs to compare the
    // two "s"s
    fn check_assoc(
        op: Operator,
        args: &[ByRefRc<Term>],
        result_term: &Term,
        is_right: bool,
    ) -> bool {
        let (head, tail) = match args {
            [] => return false,
            [t] => return t.as_ref() == result_term,

            // The "head" term will be the first or last term in `args`, depending on if the
            // operator is right or left associative
            [first, rest @ ..] if is_right => (first, rest),
            [rest @ .., last] => (last, rest),
        };
        if let Term::Op(got_op, got_args) = result_term {
            // The result term must have only two arguments, and which of them is the nested
            // operation depends on if the operator is right or left associative
            let (got_head, nested) = match got_args.as_slice() {
                [a, b] if is_right => (a, b),
                [a, b] => (b, a),
                _ => return false,
            };

            // Check that the operator and the "head" term match, and call the function
            // recursively on the remaining terms and the nested operation term
            *got_op == op && got_head == head && check_assoc(op, tail, nested, is_right)
        } else {
            false
        }
    }

    rassert!(conclusion.len() == 1);

    let (original, result) = match_term!((= o r) = conclusion[0].as_ref())?;
    if let Term::Op(op, args) = original {
        let case = match op {
            Operator::Equals => Case::Chainable,
            Operator::Add | Operator::Sub | Operator::Mult => Case::LeftAssoc,
            Operator::Implies => Case::RightAssoc,
            _ => return None,
        };
        to_option(match case {
            Case::Chainable => {
                // For every term in the chain, check that the operator is the correct one, and
                // extract its arguments
                let chain = match_term!((and ...) = result)?.iter().map(|chain_term| {
                    if let Term::Op(got_op, got_args) = chain_term.as_ref() {
                        if got_op == op {
                            return Some(got_args.as_slice());
                        }
                    }
                    None
                });
                // The terms in the chain should be the operation applied to every two adjacent
                // terms in the original term's arguments. `args.windows(2)` returns an
                // iterator over the pairs of adjacent terms
                args.windows(2).map(Some).eq(chain)
            }
            assoc_case => check_assoc(*op, args, result, assoc_case == Case::RightAssoc),
        })
    } else {
        None
    }
}

/// Applies the simplification steps for the "bfun_elim" rule.
fn apply_bfun_elim(pool: &mut TermPool, term: &ByRefRc<Term>) -> ByRefRc<Term> {
    /// The first simplification step, that expands quantifiers over boolean variables.
    fn first_step(
        pool: &mut TermPool,
        bindigns: &[SortedVar],
        term: &ByRefRc<Term>,
        acc: &mut Vec<ByRefRc<Term>>,
    ) {
        let var = match bindigns {
            [.., var] if var.1.as_ref() == Term::BOOL_SORT => pool.add_term(var.clone().into()),
            [rest @ .., _] => return first_step(pool, rest, term, acc),
            [] => {
                acc.push(term.clone());
                return;
            }
        };
        for value in [pool.bool_false(), pool.bool_true()] {
            let mut subs = AHashMap::new();
            subs.insert(var.clone(), value);
            let term = pool.apply_substitutions(term, &mut subs);
            first_step(pool, &bindigns[..bindigns.len() - 1], &term, acc)
        }
    }

    /// The second simplification step, that expands function applications over non-constant boolean
    /// arguments into "ite" terms.
    fn second_step(pool: &mut TermPool, term: &ByRefRc<Term>, processed: usize) -> ByRefRc<Term> {
        if let Term::App(f, args) = term.as_ref() {
            for i in processed..args.len() {
                if args[i].sort() == Term::BOOL_SORT
                    && !args[i].is_bool_false()
                    && !args[i].is_bool_true()
                {
                    let mut ite_args = Vec::with_capacity(3);
                    ite_args.push(args[i].clone());
                    for bool_constant in [pool.bool_true(), pool.bool_false()] {
                        let mut new_args = args.clone();
                        new_args[i] = bool_constant;
                        let inner_term = pool.add_term(Term::App(f.clone(), new_args));
                        let inner_term = second_step(pool, &inner_term, i + 1);
                        ite_args.push(inner_term)
                    }
                    return pool.add_term(Term::Op(Operator::Ite, ite_args));
                }
            }
            term.clone()
        } else {
            unreachable!()
        }
    }

    match term.as_ref() {
        Term::App(f, args) => {
            let args = args.iter().map(|a| apply_bfun_elim(pool, a)).collect();
            let new_term = pool.add_term(Term::App(f.clone(), args));
            second_step(pool, &new_term, 0)
        }
        Term::Op(op, args) => {
            let args = args.iter().map(|a| apply_bfun_elim(pool, a)).collect();
            pool.add_term(Term::Op(*op, args))
        }
        Term::Quant(q, bindings, inner) => {
            let op = match q {
                Quantifier::Forall => Operator::And,
                Quantifier::Exists => Operator::Or,
            };
            let mut args = Vec::with_capacity(2usize.pow(bindings.len() as u32));
            first_step(pool, bindings, inner, &mut args);

            let op_term = if args.len() == 1 {
                args.pop().unwrap()
            } else {
                pool.add_term(Term::Op(op, args))
            };
            let op_term = apply_bfun_elim(pool, &op_term);

            let new_bindings: Vec<_> = bindings
                .iter()
                .cloned()
                .filter(|(_, sort)| sort.as_ref() != Term::BOOL_SORT)
                .collect();
            if new_bindings.is_empty() {
                op_term
            } else {
                pool.add_term(Term::Quant(*q, new_bindings, op_term))
            }
        }
        Term::Choice(var, inner) => {
            let inner = apply_bfun_elim(pool, inner);
            pool.add_term(Term::Choice(var.clone(), inner))
        }
        Term::Let(bindings, inner) => {
            let inner = apply_bfun_elim(pool, inner);
            pool.add_term(Term::Let(bindings.clone(), inner))
        }
        _ => term.clone(),
    }
}

pub fn bfun_elim(RuleArgs { conclusion, premises, pool, .. }: RuleArgs) -> Option<()> {
    rassert!(premises.len() == 1 && conclusion.len() == 1);
    let psi = get_single_term_from_command(premises[0])?;
    to_option(conclusion[0] == apply_bfun_elim(pool, psi))
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
                "(step t1 (cl (and p q) (and r s)) :rule trust_me)
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
