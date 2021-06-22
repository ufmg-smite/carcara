use super::{to_option, RuleArgs};
use crate::ast::*;

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
    rassert!(conclusion.len() == 1);

    let (left, right) = match_term!((= l r) = conclusion[0], RETURN_RCS)?;

    let new_left = pool.apply_context_substitutions(&left, context);
    let new_right = pool.apply_context_substitutions(&right, context);

    to_option(new_left == new_right)
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
                "(anchor :step t1 :args ((:= (x Real) (y Real))))
                (step t1 (cl (= x y)) :rule refl)": true,

                "(anchor :step t1) (step t1 (cl (= z z)) :rule refl)": true,

                "(anchor :step t1 :args ((:= (x Real) (y Real))))
                (step t1 (cl (= (f x) (f y))) :rule refl)": true,
            }
            "Nested subproofs" {
                "(anchor :step t1 :args ((:= (x Real) (y Real))))
                (anchor :step t1.t1 :args ((:= (a Real) (b Real))))
                (step t1.t1 (cl (= (+ x a) (+ y b))) :rule refl)": true,

                "(anchor :step t1 :args ((:= (x Real) (y Real))))
                (anchor :step t1.t1 :args ((:= (y Real) (z Real))))
                (step t1.t1 (cl (= x z)) :rule refl)": true,
            }
            "Terms aren't equal after applying context substitutions" {
                "(anchor :step t1 :args ((:= (x Real) (y Real))))
                (step t1 (cl (= x z)) :rule refl)": false,

                "(anchor :step t1 :args ((:= (x Real) (y Real))))
                (step t1 (cl (= (f x) (g y))) :rule refl)": false,
            }
        }
    }
}
