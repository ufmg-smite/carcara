//! This module contains rules that are not yet in the specification for the Alethe format.

use super::{
    assert_clause_len, assert_eq, assert_num_premises, get_premise_term, CheckerError,
    EqualityError, RuleArgs, RuleResult,
};
use crate::{
    ast::*,
    checker::{error::CongruenceError, rules::assert_operation_len},
    utils::{MultiSet, MultiSetDifference},
};

pub fn reordering(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;

    let premise = premises[0].clause;
    assert_clause_len(conclusion, premise.len())?;

    let premise_set: MultiSet<_> = premise.iter().collect();
    let conclusion_set: MultiSet<_> = conclusion.iter().collect();
    match conclusion_set.symmetric_difference(&premise_set) {
        MultiSetDifference::None => Ok(()),
        MultiSetDifference::Missing(t) => Err(CheckerError::ContractionMissingTerm((*t).clone())),
        MultiSetDifference::Extra(t) => Err(CheckerError::ContractionExtraTerm((*t).clone())),
    }
}

pub fn shuffle(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;
    let (left_args, right_args) = {
        let ((l_op, l), (r_op, r)) = (left.as_op_err()?, right.as_op_err()?);
        if l_op != r_op {
            return Err(CongruenceError::DifferentOperators(l_op, r_op).into());
        }
        match l_op {
            Operator::Add | Operator::Mult | Operator::And | Operator::Or => (l, r),
            other => return Err(CheckerError::OperatorNotCommutative(other)),
        }
    };

    let left_multiset: MultiSet<_> = left_args.iter().collect();
    let right_multiset: MultiSet<_> = right_args.iter().collect();
    if left_multiset != right_multiset {
        return Err(CheckerError::ShuffleArgsNotEqual);
    }
    Ok(())
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
    assert_clause_len(conclusion, 1)?;
    let ((t_1, u_1), (u_2, t_2)) = match_term_err!((= (= t u) (= u t)) = &conclusion[0])?;
    assert_eq(t_1, t_2)?;
    assert_eq(u_1, u_2)
}

pub fn weakening(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
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

    let (l_bindings, left) = left.as_let_err()?;
    let (r_bindings, right) = right.as_let_err()?;

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
    rassert!(
        zero.as_number_err()? == 0,
        CheckerError::ExpectedNumber(Rational::new(), zero.clone())
    );

    let (op, args) = original.as_op_err()?;
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
    assert_eq(m, m_1)?;
    assert_eq(m, m_2)?;

    assert_eq(l, l_1)?;
    assert_eq(r, r_2)
}

pub fn mod_simplify(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;
    let (t1, t2) = match_term_err!((mod t1 t2) = left)?;

    let [a, b] = [t1, t2].map(|term| {
        let value = term.as_signed_number_err()?;
        if !value.is_integer() {
            return Err(CheckerError::ExpectedAnyInteger(term.clone()));
        }
        Ok(value.into_numer_denom().0)
    });
    // I wouldn't need to do this if `array_try_map` was stable:
    // https://github.com/rust-lang/rust/issues/79711
    let [a, b] = [a?, b?];

    let result = right.as_signed_number_err()?;

    if b.is_zero() {
        return Err(CheckerError::DivOrModByZero);
    }

    let expected = a.modulo(&b);
    rassert!(
        result == expected,
        CheckerError::ExpectedNumber(expected.into(), right.clone())
    );
    Ok(())
}

pub fn evaluate(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (term, value) = match_term_err!((= term value) = &conclusion[0])?;
    assert_eq(&term.evaluate(pool), value)
}
