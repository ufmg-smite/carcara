use super::{assert_clause_len, assert_eq, CheckerError, Elaborator, RuleArgs, RuleResult};
use crate::ast::*;

pub fn eq_reflexive(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (a, b) = match_term_err!((= a b) = &conclusion[0])?;
    assert_eq(a, b)
}

pub fn refl(
    RuleArgs {
        conclusion,
        pool,
        context,
        deep_eq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;

    // If the two terms are directly identical, we don't need to do any more work. We make sure to
    // do this check before we try to get the context substitution, because `refl` can be used
    // outside of any subproof
    if are_alpha_equivalent(left, right, deep_eq_time) {
        return Ok(());
    }

    if context.is_empty() {
        return Err(CheckerError::ReflexivityFailed(left.clone(), right.clone()));
    }

    // In some cases, the substitution is only applied to the left or the right term, and in some
    // cases it is applied to both. To cover all cases, we must check all three possibilities. We
    // don't compute the new left and right terms until they are needed, to avoid doing unnecessary
    // work
    let new_left = context.apply(pool, left);
    let result = are_alpha_equivalent(&new_left, right, deep_eq_time) || {
        let new_right = context.apply(pool, right);
        are_alpha_equivalent(left, &new_right, deep_eq_time)
            || are_alpha_equivalent(&new_left, &new_right, deep_eq_time)
    };
    rassert!(
        result,
        CheckerError::ReflexivityFailed(left.clone(), right.clone()),
    );
    Ok(())
}

fn elaborate_equality(
    elaborator: &mut Elaborator,
    pool: &mut TermPool,
    left: &Rc<Term>,
    right: &Rc<Term>,
    id: &str,
    deep_eq_time: &mut std::time::Duration,
) -> (usize, usize) {
    let is_alpha_equivalence = !timed_deep_eq_modulo_reordering(left, right, deep_eq_time);
    elaborator.elaborate_deep_eq(pool, id, left.clone(), right.clone(), is_alpha_equivalence)
}

pub fn elaborate_refl(
    RuleArgs {
        conclusion,
        pool,
        context,
        deep_eq_time,
        ..
    }: RuleArgs,
    command_id: String,
    elaborator: &mut Elaborator,
) -> RuleResult {
    // TODO: Add support for cases where context application is needed

    assert_clause_len(conclusion, 1)?;

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;

    let new_left = context.apply(pool, left);
    let new_right = context.apply(pool, right);

    if left == right || new_left == *right || new_left == new_right {
        elaborator.unchanged(conclusion);
        return Ok(());
    }

    // There are three cases to consider when elaborating a `refl` step. In the simpler case, no
    // context application is needed, and we can prove the equivalence of the left and right terms
    // directly. In the second case, we need to first apply the context to the left term, using a
    // `refl` step, and then prove the equivalence of the new left term with the right term. In the
    // third case, we also need to apply the context to the right term, using another `refl` step.
    if are_alpha_equivalent(left, right, deep_eq_time) {
        let equality_step =
            elaborate_equality(elaborator, pool, left, right, &command_id, deep_eq_time);
        let id = elaborator.get_new_id(&command_id);

        // TODO: Elaborating the deep equality will add new commands to the accumulator, but
        // currently we can't push them as the elaborated step directly, so we need to add this
        // dummy `reordering` step.
        elaborator.push_elaborated_step(ProofStep {
            id,
            clause: conclusion.to_vec(),
            rule: "reordering".to_owned(),
            premises: vec![equality_step],
            args: Vec::new(),
            discharge: Vec::new(),
        });
    } else {
        let id = elaborator.get_new_id(&command_id);
        let first_step = elaborator.add_refl_step(pool, left.clone(), new_left.clone(), id);

        let second_step = elaborate_equality(
            elaborator,
            pool,
            &new_left,
            right,
            &command_id,
            deep_eq_time,
        );

        if are_alpha_equivalent(&new_left, right, deep_eq_time) {
            let id = elaborator.get_new_id(&command_id);
            elaborator.push_elaborated_step(ProofStep {
                id,
                clause: conclusion.to_vec(),
                rule: "trans".to_owned(),
                premises: vec![first_step, second_step],
                args: Vec::new(),
                discharge: Vec::new(),
            });
        } else if are_alpha_equivalent(&new_left, &new_right, deep_eq_time) {
            let id = elaborator.get_new_id(&command_id);
            let third_step = elaborator.add_refl_step(pool, new_right.clone(), right.clone(), id);

            let id = elaborator.get_new_id(&command_id);
            elaborator.push_elaborated_step(ProofStep {
                id,
                clause: conclusion.to_vec(),
                rule: "trans".to_owned(),
                premises: vec![first_step, second_step, third_step],
                args: Vec::new(),
                discharge: Vec::new(),
            });
        } else {
            return Err(CheckerError::ReflexivityFailed(left.clone(), right.clone()));
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn eq_reflexive() {
        test_cases! {
            definitions = "
                (declare-fun a () Int)
                (declare-fun b () Int)
                (declare-fun f (Int Int) Int)
            ",
            "Simple working examples" {
                "(step t1 (cl (= a a)) :rule eq_reflexive)": true,
                "(step t1 (cl (= false false)) :rule eq_reflexive)": true,
                "(step t1 (cl (= (f a b) (f a b))) :rule eq_reflexive)": true,
                "(step t1 (cl (= (+ b a) (+ b a))) :rule eq_reflexive)": true,
            }
            "Number of terms in clause != 1" {
                "(step t1 (cl) :rule eq_reflexive)": false,
                "(step t1 (cl (= a a) (= b b)) :rule eq_reflexive)": false,
            }
            "Term is not an equality" {
                "(step t1 (cl (not (= b b))) :rule eq_reflexive)": false,
                "(step t1 (cl (and (= a a) (= b b))) :rule eq_reflexive)": false,
            }
            "Terms in equality aren't equal" {
                "(step t1 (cl (= a b)) :rule eq_reflexive)": false,
                "(step t1 (cl (= (f a b) (f b a))) :rule eq_reflexive)": false,
                "(step t1 (cl (= (+ a b) (+ b a))) :rule eq_reflexive)": false,
            }
        }
    }

    #[test]
    fn refl() {
        test_cases! {
            definitions = "
                (declare-fun f (Real) Real)
                (declare-fun g (Real) Real)
                (declare-fun z () Real)
            ",
            "Simple working examples" {
                "(anchor :step t1 :args ((y Real) (:= x y)))
                (step t1 (cl (= x y)) :rule refl)": true,

                "(anchor :step t1) (step t1 (cl (= z z)) :rule refl)": true,

            }
            "Multiple substitutions in sequence" {
                "(anchor :step t1 :args ((z Real) (:= y z) (:= x y)))
                (step t1 (cl (= x z)) :rule refl)": true,
            }
            "Nested subproofs" {
                // Since an inner subproof cannot end an outer subproof, we need to have a dummy
                // step to the end the outer subproofs in these examples

                "(anchor :step t1 :args ((z Real) (:= x z)))
                (anchor :step t1.t1 :args ((z Real) (:= y z)))
                (step t1.t1 (cl (= x y)) :rule refl)
                (step t1 (cl) :rule hole)": true,

                "(anchor :step t1 :args ((y Real) (:= x y)))
                (anchor :step t1.t1 :args ((z Real) (:= y z)))
                (step t1.t1 (cl (= x z)) :rule refl)
                (step t1 (cl) :rule hole)": true,
            }
            "Terms aren't equal after applying context substitution" {
                "(anchor :step t1 :args ((y Real) (:= x y)))
                (step t1 (cl (= x z)) :rule refl)": false,
            }
        }
    }
}
