use super::{to_option, RuleArgs};
use crate::{ast::*, checker::Context};

pub fn eq_reflexive(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    rassert!(conclusion.len() == 1);
    let (a, b) = match_term!((= a b) = conclusion[0])?;
    to_option(a == b)
}

pub fn refl(
    RuleArgs {
        conclusion,
        pool,
        context,
        ..
    }: RuleArgs,
) -> Option<()> {
    fn apply_all_context_substitutions(
        pool: &mut TermPool,
        term: ByRefRc<Term>,
        context: &mut [Context],
    ) -> ByRefRc<Term> {
        let mut current = term;
        for c in context {
            current = pool.apply_substitutions(&current, &mut c.substitutions_until_fixed_point);
        }
        current
    }
    rassert!(conclusion.len() == 1);

    let (left, right) = match_term!((= l r) = conclusion[0], RETURN_RCS)?;

    let new_left = apply_all_context_substitutions(pool, left.clone(), context);
    let new_right = apply_all_context_substitutions(pool, right.clone(), context);

    // In some cases, the substitution is only applied to the left or the right term, and in some
    // cases it is applied to both. To cover all cases, we must check all three possibilities
    to_option(new_left == *right || *left == new_right || new_left == new_right)
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
                "(anchor :step t1 :args ((:= (x Real) y)))
                (step t1 (cl (= x y)) :rule refl)": true,

                "(anchor :step t1) (step t1 (cl (= z z)) :rule refl)": true,

            }
            "Multiple substitutions in sequence" {
                "(anchor :step t1 :args ((:= (x Real) y) (:= (y Real) z)))
                (step t1 (cl (= x z)) :rule refl)": true,
            }
            "Nested subproofs" {
                "(anchor :step t1 :args ((:= (x Real) z)))
                (anchor :step t1.t1 :args ((:= (y Real) z)))
                (step t1.t1 (cl (= x y)) :rule refl)": true,

                "(anchor :step t1 :args ((:= (x Real) y)))
                (anchor :step t1.t1 :args ((:= (y Real) z)))
                (step t1.t1 (cl (= x z)) :rule refl)": true,
            }
            "Terms aren't equal after applying context substitutions" {
                "(anchor :step t1 :args ((:= (x Real) y)))
                (step t1 (cl (= x z)) :rule refl)": false,
            }
        }
    }
}
