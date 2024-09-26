use super::{assert_clause_len, assert_num_args, assert_num_premises, RuleArgs, RuleResult, Term};
use crate::checker::error::CheckerError;
use crate::checker::Rc;
use rug::Integer;
use std::collections::HashMap;

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

fn get_pb_hashmap(pbsum: &[Rc<Term>]) -> Result<HashMap<String, Integer>, CheckerError> {
    let mut hm = HashMap::new();
    let n = pbsum.len() - 1;
    for term in pbsum.iter().take(n) {
        let (coeff, literal) = match_term_err!((* coeff literal) = term)?;
        let coeff = coeff.as_integer_err()?;
        let literal = literal.to_string();
        hm.insert(literal, coeff);
    }
    Ok(hm)
}

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
    assert_clause_len(premises[0].clause, 1)?;
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
    let pbsum_p = get_pb_hashmap(pbsum_p)?;

    // Unwrap the conclusion inequality
    let (pbsum_c, constant_c) = match_term_err!((>= (+ ...) constant_c) = conclusion)?;
    let constant_c = constant_c.as_integer_err()?;
    let pbsum_c = get_pb_hashmap(pbsum_c)?;

    // Verify constants match
    rassert!(
        scalar.clone() * constant_p.clone() == constant_c,
        CheckerError::ExpectedInteger(scalar.clone() * constant_p, conclusion.clone())
    );

    // Verify pseudo-boolean sums match
    for (literal, coeff_p) in pbsum_p {
        if let Some(coeff_c) = pbsum_c.get(&literal) {
            let expected = &scalar * coeff_p;
            rassert!(
                &expected == coeff_c,
                CheckerError::ExpectedInteger(expected, conclusion.clone())
            );
        }
    }

    Ok(())
}

pub fn cp_division(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    let clause = &premises[0].clause[0];

    // Check there is exactly one arg
    assert_num_args(args, 1)?;
    let divisor: Integer = args[0].as_term()?.as_integer_err()?;

    // Check there is exacly one conclusion
    assert_clause_len(conclusion, 1)?;
    let conclusion = &conclusion[0];

    // Unwrap the premise inequality
    let (pbsum_p, constant_p) = match_term_err!((>= (+ ...) constant) = clause)?;
    let constant_p = constant_p.as_integer_err()?;
    let pbsum_p = get_pb_hashmap(pbsum_p)?;

    // Unwrap the conclusion inequality
    let (pbsum_c, constant_c) = match_term_err!((>= (+ ...) constant_c) = conclusion)?;
    let constant_c = constant_c.as_integer_err()?;
    let pbsum_c = get_pb_hashmap(pbsum_c)?;

    // Verify constants match
    // TODO: CeilDiv
    rassert!(
        constant_p.clone() / divisor.clone() == constant_c,
        CheckerError::ExpectedInteger(constant_p / divisor.clone(), conclusion.clone())
    );

    // Verify pseudo-boolean sums match
    for (literal, coeff_p) in pbsum_p {
        if let Some(coeff_c) = pbsum_c.get(&literal) {
            // TODO: CeilDiv
            let expected = coeff_p / &divisor;
            rassert!(
                &expected == coeff_c,
                CheckerError::ExpectedInteger(expected, conclusion.clone())
            );
        }
    }

    Ok(())
}

pub fn cp_saturation(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_num_args(args, 0)?;
    let clause = &premises[0].clause[0];

    // Check there is exacly one conclusion
    assert_clause_len(conclusion, 1)?;
    let conclusion = &conclusion[0];

    // Unwrap the premise inequality
    let (pbsum_p, constant_p) = match_term_err!((>= (+ ...) constant) = clause)?;
    let constant_p = constant_p.as_integer_err()?;
    let pbsum_p = get_pb_hashmap(pbsum_p)?;

    // Unwrap the conclusion inequality
    let (pbsum_c, constant_c) = match_term_err!((>= (+ ...) constant_c) = conclusion)?;
    let constant_c = constant_c.as_integer_err()?;
    let pbsum_c = get_pb_hashmap(pbsum_c)?;

    // Verify constants match
    rassert!(
        constant_p == constant_c,
        CheckerError::ExpectedInteger(constant_p.clone(), conclusion.clone())
    );

    // Verify saturation of variables match
    for (literal, coeff_p) in pbsum_p {
        if let Some(coeff_c) = pbsum_c.get(&literal) {
            let expected = Ord::min(&constant_p, &coeff_p);
            rassert!(
                expected == coeff_c,
                CheckerError::ExpectedInteger(expected.clone(), conclusion.clone())
            );
        }
    }

    Ok(())
}

mod tests {
    #[test]
    fn cp_addition() {
        test_cases! {
           definitions = "
                (declare-fun x1 () Int)
                (declare-fun x2 () Int)
                (declare-fun x3 () Int)
                ",
            "Simple working examples" {
                r#"(assume c1 (>= (+ (* 1 x1) 0) 1))
                   (step t1 (cl (>= (* 2 x1) 2)) :rule cp_addition :premises (c1 c1))"#: true,

                r#"(assume c1 (>= (+ (* 1 x1) 0) 1))
                   (assume c2 (>= (+ (* 1 x2) 0) 1))
                   (step t1 (cl (>= (+ (* 1 x1) (* 1 x2) 0) 2)) :rule cp_addition :premises (c1 c2))"#: true,

                r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2) 0) 1))
                   (assume c2 (>= (+ (* 1 x2) (* 1 x1) 0) 1))
                   (step t1 (cl (>= (+ (* 2 x1) (* 3 x2) 0) 2)) :rule cp_addition :premises (c1 c2))"#: true,

            }
            "Missing Terms" {
                r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2) (* 1 x3) 0) 1))
                   (assume c2 (>= (+ (* 1 x2) (* 1 x1) 0) 1))
                   (step t1 (cl (>= (+ (* 2 x1) (* 3 x2) 0) 2)) :rule cp_addition :premises (c1 c2))"#: false,
            }
            "Wrong Addition" {
                r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2) 0) 1))
                   (assume c2 (>= (+ (* 1 x2) (* 1 x1) 0) 1))
                   (step t1 (cl (>= (+ (* 2 x1) (* 2 x2) 0) 2)) :rule cp_addition :premises (c1 c2))"#: false,

                r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2) 0) 1))
                   (assume c2 (>= (+ (* 1 x2) (* 1 x1) 0) 1))
                   (step t1 (cl (>= (+ (* 2 x1) (* 3 x2) 0) 3)) :rule cp_addition :premises (c1 c2))"#: false,
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
                r#"(assume c1 (>= (+ (* 2 x1) 0) 2))
                   (step t1 (cl (>= (+ (* 1 x1) 0) 1)) :rule cp_division :premises (c1) :args (2) )"#: true,
            }
            "Wrong division" {
                r#"(assume c1 (>= (+ (* 2 x1) 0) 2))
                   (step t1 (cl (>= (+ (* 2 x1) 0) 1)) :rule cp_division :premises (c1) :args (2) )"#: false,
                r#"(assume c1 (>= (+ (* 2 x1) 0) 2))
                   (step t1 (cl (>= (+ (* 1 x1) 0) 2)) :rule cp_division :premises (c1) :args (2) )"#: false,
            }
        }
    }
    #[test]
    fn cp_saturation() {
        test_cases! {
            definitions = "
                (declare-fun x1 () Int)
                (declare-fun x2 () Int)
                (declare-fun x3 () Int)
                ",
            "Simple working examples" {
                r#"(assume c1 (>= (+ (* 2 x1) 0) 1))
                   (step t1 (cl (>= (+ (* 1 x1) 0) 1)) :rule cp_saturation :premises (c1))"#: true,

                r#"(assume c1 (>= (+ (* 2 x1) (* 5 x2) (* 3 x3) 0) 3))
                   (step t1 (cl (>= (+ (* 2 x1) (* 3 x2) (* 3 x3) 0) 3)) :rule cp_saturation :premises (c1))"#: true,

            }
        }
    }
}
