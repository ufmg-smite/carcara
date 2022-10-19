//! This module contains rules that are not yet in the specification for the Alethe format.

use super::{
    assert_clause_len, assert_eq, assert_num_premises, get_premise_term, CheckerError,
    EqualityError, RuleArgs, RuleResult,
};
use crate::{ast::*, checker::rules::assert_operation_len};
use ahash::AHashSet;

pub fn reordering(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;

    let premise = premises[0].clause;
    assert_clause_len(conclusion, premise.len())?;

    let premise_set: AHashSet<_> = premise.iter().collect();
    let conclusion_set: AHashSet<_> = conclusion.iter().collect();
    if let Some(&t) = premise_set.difference(&conclusion_set).next() {
        Err(CheckerError::ReorderingMissingTerm(t.clone()))
    } else if let Some(&t) = conclusion_set.difference(&premise_set).next() {
        Err(CheckerError::ReorderingExtraTerm(t.clone()))
    } else {
        Ok(())
    }
}

pub fn symm(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let premise = get_premise_term(&premises[0])?;
    let (p_1, q_1) = match_term_err!((= p q) = premise)?;
    let (q_2, p_2) = match_term_err!((= q p) = &conclusion[0])?;
    assert_eq(p_1, p_2)?;
    assert_eq(q_1, q_2)
}

pub fn not_symm(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let premise = get_premise_term(&premises[0])?;
    let (p_1, q_1) = match_term_err!((not (= p q)) = premise)?;
    let (q_2, p_2) = match_term_err!((not (= q p)) = &conclusion[0])?;
    assert_eq(p_1, p_2)?;
    assert_eq(q_1, q_2)
}

pub fn eq_symmetric(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 2)?;
    let (t_1, u_1) = match_term_err!((not (= t u)) = &conclusion[0])?;
    let (u_2, t_2) = match_term_err!((= u t) = &conclusion[1])?;
    assert_eq(t_1, t_2)?;
    assert_eq(u_1, u_2)
}

pub fn or_intro(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    let premise = premises[0].clause;
    assert_clause_len(conclusion, premise.len()..)?;
    for (t, u) in premise.iter().zip(conclusion) {
        assert_eq(t, u)?;
    }
    Ok(())
}

pub fn bind_let(
    RuleArgs {
        conclusion,
        premises,
        previous_command,
        ..
    }: RuleArgs,
) -> RuleResult {
    let previous_command = previous_command.ok_or(CheckerError::MustBeLastStepInSubproof)?;

    assert_clause_len(conclusion, 1)?;

    let (phi, phi_prime) = match_term_err!((= p q) = get_premise_term(&previous_command)?)?;

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;

    let (l_bindings, left) = left.unwrap_let_err()?;
    let (r_bindings, right) = right.unwrap_let_err()?;

    if l_bindings.len() != r_bindings.len() {
        return Err(EqualityError::ExpectedEqual(l_bindings.clone(), r_bindings.clone()).into());
    }

    let mut premises_iter = premises
        .iter()
        .map(|p| match_term_err!((= t u) = get_premise_term(p)?))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter();
    for (left, right) in l_bindings.iter().zip(r_bindings) {
        if left.0 != right.0 {
            return Err(
                EqualityError::ExpectedEqual(l_bindings.clone(), r_bindings.clone()).into(),
            );
        }

        // This will consume premises until it finds one that justifies the needed equality, so
        // unnecessary premises are just ignored
        if left.1 != right.1 && !premises_iter.any(|p| p == (&left.1, &right.1)) {
            return Err(EqualityError::ExpectedEqual(left.1.clone(), right.1.clone()).into());
        }
    }

    assert_eq(left, phi)?;
    assert_eq(right, phi_prime)
}

pub fn la_mult_pos(args: RuleArgs) -> RuleResult {
    la_mult_generic(args.conclusion, true)
}

pub fn la_mult_neg(args: RuleArgs) -> RuleResult {
    la_mult_generic(args.conclusion, false)
}

fn la_mult_generic(conclusion: &[Rc<Term>], is_pos: bool) -> RuleResult {
    use rug::Rational;

    fn match_comparison_term(
        op: Operator,
        term: &Rc<Term>,
    ) -> Result<(&Rc<Term>, &Rc<Term>), CheckerError> {
        match op {
            Operator::Equals => match_term_err!((= a b) = term),
            Operator::LessThan => match_term_err!((< a b) = term),
            Operator::GreaterThan => match_term_err!((> a b) = term),
            Operator::LessEq => match_term_err!((<= a b) = term),
            Operator::GreaterEq => match_term_err!((>= a b) = term),
            _ => unreachable!(),
        }
    }

    assert_clause_len(conclusion, 1)?;
    let ((m_comparison, original), scaled) =
        match_term_err!((=> (and m_comparison original) scaled) = &conclusion[0])?;
    let (m, zero) = if is_pos {
        match_term_err!((> m zero) = m_comparison)
    } else {
        match_term_err!((< m zero) = m_comparison)
    }?;
    let m = m.as_fraction_err()?;
    rassert!(
        zero.as_number_err()? == 0,
        CheckerError::ExpectedNumber(Rational::new(), zero.clone())
    );

    let (op, args) = original.unwrap_op_err()?;
    assert_operation_len(op, args, 2)?;
    let (l, r) = (&args[0], &args[1]);

    let op = if is_pos {
        op
    } else {
        match op {
            Operator::Equals => Operator::Equals,
            Operator::LessThan => Operator::GreaterThan,
            Operator::GreaterThan => Operator::LessThan,
            Operator::LessEq => Operator::GreaterEq,
            Operator::GreaterEq => Operator::LessEq,
            _ => unreachable!(),
        }
    };

    let (ml, mr) = match_comparison_term(op, scaled)?;
    let ((m_1, l_1), (m_2, r_2)) = (
        match_term_err!((* m l) = ml)?,
        match_term_err!((* m r) = mr)?,
    );
    rassert!(
        m_1.as_fraction_err()? == m,
        CheckerError::ExpectedNumber(m.clone(), m_1.clone())
    );
    rassert!(
        m_2.as_fraction_err()? == m,
        CheckerError::ExpectedNumber(m, m_2.clone())
    );
    assert_eq(l, l_1)?;
    assert_eq(r, r_2)
}

#[cfg(test)]
mod tests {
    #[test]
    fn reordering() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl p q r s) :rule hole)
                (step t2 (cl r q p s) :rule reordering :premises (t1))": true,

                "(step t1 (cl p q q p r s) :rule hole)
                (step t2 (cl r q p p s q) :rule reordering :premises (t1))": true,

                "(step t1 (cl) :rule hole)
                (step t2 (cl) :rule reordering :premises (t1))": true,
            }
        }
    }

    #[test]
    fn symm() {
        test_cases! {
            definitions = "
                (declare-sort T 0)
                (declare-fun a () T)
                (declare-fun b () T)
            ",
            "Simple working examples" {
                "(assume h1 (= a b))
                (step t1 (cl (= b a)) :rule symm :premises (h1))": true,
            }
            "Failing examples" {
                "(assume h1 (not (= a b)))
                (step t1 (cl (not (= b a))) :rule symm :premises (h1))": false,
            }
        }
    }

    #[test]
    fn not_symm() {
        test_cases! {
            definitions = "
                (declare-sort T 0)
                (declare-fun a () T)
                (declare-fun b () T)
            ",
            "Simple working examples" {
                "(assume h1 (not (= a b)))
                (step t1 (cl (not (= b a))) :rule not_symm :premises (h1))": true,
            }
            "Failing examples" {
                "(assume h1 (= a b))
                (step t1 (cl (= b a)) :rule not_symm :premises (h1))": false,
            }
        }
    }

    #[test]
    fn eq_symmetric() {
        test_cases! {
            definitions = "
                (declare-sort T 0)
                (declare-fun a () T)
                (declare-fun b () T)
            ",
            "Simple working examples" {
                "(step t1 (cl (not (= b a)) (= a b)) :rule eq_symmetric)": true,
                "(step t1 (cl (not (= a a)) (= a a)) :rule eq_symmetric)": true,
            }
            "Failing examples" {
                "(step t1 (cl (not (= a b)) (= a b)) :rule eq_symmetric)": false,
                "(step t1 (cl (not (= a b)) (not (= b a))) :rule eq_symmetric)": false,
            }
        }
    }

    #[test]
    fn or_intro() {
        test_cases! {
            definitions = "
                (declare-fun a () Bool)
                (declare-fun b () Bool)
                (declare-fun c () Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl a b) :rule hole)
                (step t2 (cl a b c) :rule or_intro :premises (t1))": true,

                "(step t1 (cl) :rule hole)
                (step t2 (cl a b) :rule or_intro :premises (t1))": true,
            }
            "Failing examples" {
                "(step t1 (cl a b) :rule hole)
                (step t2 (cl a c b) :rule or_intro :premises (t1))": false,

                "(step t1 (cl a b c) :rule hole)
                (step t2 (cl a b) :rule or_intro :premises (t1))": false,
            }
        }
    }

    #[test]
    fn bind_let() {
        test_cases! {
            definitions = "",
            "Simple working examples" {
                "(anchor :step t1 :args ((x Int) (y Int)))
                (step t1.t1 (cl (= x y)) :rule hole)
                (step t1 (cl (= (let ((a 0)) x) (let ((a 0)) y))) :rule bind_let)": true,
            }
            "Premise is of the wrong form" {
                "(anchor :step t1 :args ((x Int) (y Int)))
                (step t1.t1 (cl (< (+ x y) 0)) :rule hole)
                (step t1 (cl (= (let ((a 0)) x) (let ((a 0)) y))) :rule bind_let)": false,
            }
            "Premise doesn't justify inner terms' equality" {
                "(anchor :step t1 :args ((x Int) (y Int)))
                (step t1.t1 (cl (= x y)) :rule hole)
                (step t1 (cl (= (let ((a 0)) a) (let ((a 0)) 0))) :rule bind_let)": false,

                "(anchor :step t1 :args ((x Int) (y Int)))
                (step t1.t1 (cl (= x y)) :rule hole)
                (step t1 (cl (= (let ((a 0)) y) (let ((a 0)) x))) :rule bind_let)": false,
            }
            "Bindings can't be renamed" {
                "(anchor :step t1 :args ((x Int) (y Int)))
                (step t1.t1 (cl (= x y)) :rule hole)
                (step t1 (cl (= (let ((a 0)) x) (let ((b 0)) y))) :rule bind_let)": false,
            }
            "Deep equality in variable values" {
                "(anchor :step t1 :args ((x Int) (y Int)))
                (step t1.t1 (cl (= (= 0 1) (= 1 0))) :rule hole)
                (step t1.t2 (cl (= x y)) :rule hole)
                (step t1 (cl (= (let ((a (= 0 1))) x) (let ((a (= 1 0))) y)))
                    :rule bind_let :premises (t1.t1))": true,
            }
        }
    }

    #[test]
    fn la_mult_pos() {
        test_cases! {
            definitions = "
                (declare-fun a () Int)
                (declare-fun b () Int)
                (declare-fun x () Real)
                (declare-fun y () Real)
            ",
            "Simple working examples" {
                "(step t1 (cl (=> (and (> 2 0) (> a b)) (> (* 2 a) (* 2 b))))
                    :rule la_mult_pos)": true,
                "(step t1 (cl (=>
                    (and (> (/ 10.0 13.0) 0.0) (= x y))
                    (= (* (/ 10.0 13.0) x) (* (/ 10.0 13.0) y)))
                ) :rule la_mult_pos)": true,
            }
        }
    }

    #[test]
    fn la_mult_neg() {
        test_cases! {
            definitions = "
                (declare-fun a () Int)
                (declare-fun b () Int)
                (declare-fun x () Real)
                (declare-fun y () Real)
            ",
            "Simple working examples" {
                "(step t1 (cl (=> (and (< (- 2) 0) (>= a b)) (<= (* (- 2) a) (* (- 2) b))))
                    :rule la_mult_neg)": true,
                "(step t1 (cl (=>
                    (and (< (/ (- 1.0) 13.0) 0.0) (= x y))
                    (= (* (/ (- 1.0) 13.0) x) (* (/ (- 1.0) 13.0) y)))
                ) :rule la_mult_neg)": true,
            }
        }
    }
}
