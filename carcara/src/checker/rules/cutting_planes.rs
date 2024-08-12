use crate::checker::error::CheckerError;

use super::{
    assert_clause_len, assert_eq, assert_num_args, assert_num_premises, RuleArgs, RuleResult,
};
use rug::Integer;

/*
(step t1 (cl
            (>=
                (+ (* 2 x1) (* 4 x2) (* 2 x3))
                4)
            )
    :rule cp_multiplication
    :premises (c1)
)
(step t2 (cl
            (>=
                (+ (* 3 x1) (* 6 x2) (* 6 x3) (* 2 x4))
                9)
            )
    :rule cp_addition
    :premises (t1 c2)
)
(step t3 (cl
            (>=
                (* 2 (- 1 x4))
                0)
            )
    :rule cp_multiplication
    :premises (c3)
)
(step t4 (cl
             (>=
                (+ (* 3 x1) (* 6 x2) (* 6 x3))
                7)
            )
    :rule cp_addition
    :premises (t2 t3)
)
(step t5 (cl
             (>=
                (+ x1 (* 2 x2) (* 2 x3))
                3)
            )
    :rule cp_division
    :premises (t4)
)
*/

pub fn cp_addition(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("Addition");
    assert_num_premises(premises, 2)?;
    assert_num_args(args, 0)?;
    assert_clause_len(conclusion, 1)?;
    Ok(())
}

pub fn cp_multiplication(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    // Check there is exactly one premise
    assert_num_premises(premises, 1)?;
    // TODO: change assert fn
    assert_eq!(premises[0].clause.len(), 1);
    let clause = &premises[0].clause[0];

    // Check there is exactly one arg
    assert_num_args(args, 1)?;
    let scalar: Integer = args[0].as_term()?.as_integer_err()?;

    // Check there is exactly one conclusion
    assert_clause_len(conclusion, 1)?;
    let conclusion = &conclusion[0];

    // Unwrap the premise inequality
    let (pbsum_p, constant_p) = match_term_err!((>= (+ ...) constant) = clause)?;
    let constant_p = constant_p.as_integer_err()?;

    // Unwarp the conclusion inequality
    let (pbsum_c, constant_c) = match_term_err!((>= (+ ...) constant_c) = conclusion)?;
    let constant_c = constant_c.as_integer_err()?;

    // Verify constants match
    // TODO: change assert fn
    assert_eq!(&scalar * constant_p, constant_c);

    // Verify pseudo-boolean sums match
    for i in 0..(pbsum_c.len() - 1) {
        // println!("{}: {} * {} == {}", i, &scalar, pbsum_p[i], pbsum_c[i]);
        let (a_p, l_p) = match_term_err!((* a_p l_p) = &pbsum_p[i])?;
        let (a_c, l_c) = match_term_err!((* a_c l_c) = &pbsum_c[i])?;
        assert_eq(l_p, l_c)?;
        let a_p = a_p.as_integer_err()?;
        let a_c = a_c.as_integer_err()?;
        // TODO: change assert fn
        rassert!(
            scalar * a_p == a_c,
            CheckerError::ExpectedInteger(scalar * a_p, pbsum_c[i].clone())
        );
    }

    Ok(())
}

pub fn cp_division(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("Division");
    assert_num_premises(premises, 1)?;
    assert_num_args(args, 1)?;
    assert_clause_len(conclusion, 1)?;
    Ok(())
}

pub fn cp_saturation(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("Saturation");
    assert_num_premises(premises, 1)?;
    assert_num_args(args, 0)?;
    assert_clause_len(conclusion, 1)?;
    Ok(())
}

mod tests {
    #[test]
    fn cp_addition() {
        test_cases! {
           definitions = "
                (declare-fun x1 () Int)
                ",
            "Simple working examples" {
                r#"(assume c1 (>= x1 1))
                   (step t1 (cl (>= (* 2 x1) 2)) :rule cp_addition :premises (c1 c1))"#: true,
            }

        }
    }
    #[test]
    fn cp_multiplication() {
        test_cases! {
            definitions = "
                (declare-fun x1 () Int)
                (declare-fun x2 () Int)
                (declare-fun x3 () Int)
                ",
            "Simple working examples" {
                r#"(assume c1 (>= (+ (* 1 x1) 0) 1))
                   (step t1 (cl (>= (+ (* 2 x1) 0) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: true,
                // ? other alternative, without trailing zero
                // r#"(assume c1 (>= (* 1 x1) 1))
                //    (step t1 (cl (>= (* 2 x1) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: true,
                r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2) 0) 1))
                   (step t1 (cl (>= (+ (* 2 x1) (* 4 x2) 0) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: true,
                r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2) (* 3 x3) 0) 1))
                   (step t1 (cl (>= (+ (* 2 x1) (* 4 x2) (* 6 x3) 0) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: true,

            }
            "Wrong number of premises" {
                r#"(assume c1 (>= x1 1))
                   (step t1 (cl (>= (* 2 x1) 2)) :rule cp_multiplication :args (2))"#: false,
                r#"(assume c1 (>= x1 1))
                   (step t1 (cl (>= (* 2 x1) 2)) :rule cp_multiplication :premises (c1 c1) :args (2))"#: false,
            }
            "Wrong number of args" {
                r#"(assume c1 (>= x1 1))
                   (step t1 (cl (>= (* 2 x1) 2)) :rule cp_multiplication :premises (c1))"#: false,
                r#"(assume c1 (>= x1 1))
                   (step t1 (cl (>= (* 2 x1) 2)) :rule cp_multiplication :premises (c1) :args (2 3))"#: false,
            }
            // TODO: "Wrong number of clauses in the conclusion"
            "Wrong product" {
                r#"(assume c1 (>= (+ (* 1 x1) 0) 1))
                   (step t1 (cl (>= (+ (* 3 x1) 0) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: false,
                r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2) 0) 1))
                   (step t1 (cl (>= (+ (* 1 x1) (* 4 x2) 0) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: false,
                r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2) (* 3 x3) 0) 1))
                   (step t1 (cl (>= (+ (* 2 x1) (* 4 x2) (* 3 x3) 0) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: false,
            }
        }
    }
    #[test]
    fn cp_division() {
        test_cases! {
            definitions = "
                (declare-fun x1 () Int)
                ",
            "Simple working examples" {
                r#"(assume c1 (>= (* 2 x1) 2))
                   (step t1 (cl (>= x1 1)) :rule cp_division :premises (c1) :args (2) )"#: true,
            }
        }
    }
    #[test]
    fn cp_saturation() {
        test_cases! {
            definitions = "
                (declare-fun x1 () Int)
                ",
            "Simple working examples" {
                r#"(assume c1 (>= (* 2 x1) 1))
                   (step t1 (cl (>= x1 1)) :rule cp_division :premises (c1))"#: true,
            }
        }
    }
}
