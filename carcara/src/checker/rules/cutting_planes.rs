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

// TODO: How to represent NEGATED literals
/*
    (>= (+ (* 1 (- 1 x3)) 0) 1) == ~x3 >= 1

    PbHash: (literal:String) -> (pos:Integer,neg:Integer)
    * Confusion when accessing a single literal
    * Easy to bind positive and negated variables, needed by cp_addition

    PbHash: (literal:String) -> (coeff:Integer)
    * Easy access to single literal
    * Must implement a relation between positive and negated variables, needed by cp_addtion

*/

type PbHash = HashMap<String, Integer>;

trait NegatedLiterals {
    fn get_negated(&self, lit: &str) -> Option<&Integer>;
}

impl NegatedLiterals for PbHash {
    fn get_negated(&self, lit: &str) -> Option<&Integer> {
        if let Some(plain_lit) = lit.strip_prefix('~') {
            self.get(plain_lit)
        } else {
            self.get(&format!("~{}", lit))
        }
    }
}

fn get_pb_hashmap(pbsum: &[Rc<Term>]) -> Result<PbHash, CheckerError> {
    let mut hm = HashMap::new();
    let n = pbsum.len() - 1;

    for term in pbsum.iter().take(n) {
        let (coeff, literal) =
            // Negated literal  (* c x1)
            if let Some((coeff, (_, literal))) = match_term!((* coeff (- one literal)) = term) {
                (coeff, literal)
            // Plain literal    (* c (- 1 x1))
            } else if let Some((coeff, literal)) = match_term!((* coeff literal) = term) {
                (coeff, literal)
            } else {
                return Err(CheckerError::Unspecified);
            };

        let coeff = coeff.as_integer_err()?;
        let literal = literal.to_string();
        hm.insert(literal, coeff);
    }
    Ok(hm)
}

fn unwrap_pseudoboolean_inequality(clause: &Rc<Term>) -> Result<(PbHash, Integer), CheckerError> {
    let (pbsum, constant) = match_term_err!((>= (+ ...) constant) = clause)?;
    let constant = constant.as_integer_err()?;
    let pbsum = get_pb_hashmap(pbsum)?;
    Ok((pbsum, constant))
}

/// Checks that every key in ``pbsum_a`` is present in ``pbsum_b``
/// ha ⊆ hb
fn assert_pbsum_subset_keys(pbsum_a: &PbHash, pbsum_b: &PbHash) -> Result<(), CheckerError> {
    for key in pbsum_a.keys() {
        if pbsum_b.get(key).is_none() {
            return Err(CheckerError::Unspecified);
        }
    }
    Ok(())
}

fn assert_pbsum_same_keys(pbsum_a: &PbHash, pbsum_b: &PbHash) -> Result<(), CheckerError> {
    // All keys in A are in B
    assert_pbsum_subset_keys(pbsum_a, pbsum_b)?;

    // All keys in B are in A
    assert_pbsum_subset_keys(pbsum_b, pbsum_a)?;

    Ok(())
}

pub fn cp_addition(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    // Check there is exactly two premises
    assert_num_premises(premises, 2)?;

    assert_clause_len(premises[0].clause, 1)?;
    let left_clause = &premises[0].clause[0];

    assert_clause_len(premises[1].clause, 1)?;
    let right_clause = &premises[1].clause[0];

    // Check there are no args
    assert_num_args(args, 0)?;

    // Check there is exactly one conclusion
    assert_clause_len(conclusion, 1)?;
    let conclusion = &conclusion[0];

    // Unwrap the premise inequality
    let (pbsum_l, constant_l) = unwrap_pseudoboolean_inequality(left_clause)?;
    let (pbsum_r, constant_r) = unwrap_pseudoboolean_inequality(right_clause)?;

    // Unwrap the conclusion inequality
    let (pbsum_c, constant_c) = unwrap_pseudoboolean_inequality(conclusion)?;

    // Verify constants match
    rassert!(
        constant_l.clone() + constant_r.clone() == constant_c,
        CheckerError::ExpectedInteger(constant_l.clone() + constant_r.clone(), conclusion.clone())
    );

    // Verify keys in pbsum_c = pbsum_l ∪ pbsum_r
    // C = L ∪ R
    // ==> (L ⊆ C) ∧ (R ⊆ C) ∧ ¬∃ x, (x ∈ C) ∧ ¬(x ∈ L) ∧ ¬(x ∈ R)
    // All keys of pbsum_l are in pubsum_c
    // L ⊆ C
    assert_pbsum_subset_keys(&pbsum_l, &pbsum_c)?;

    // All keys of pbsum_r are in pbsum_c
    // R ⊆ C
    assert_pbsum_subset_keys(&pbsum_r, &pbsum_c)?;

    // TODO:
    // lr := l + r
    // (lr',slack) := reduction(lr)
    // assert lr' == c && constant_c == slack + constant_l + constant_r

    // Verify pseudo-boolean sums match
    for (literal, coeff_c) in &pbsum_c {
        match (pbsum_l.get(literal), pbsum_r.get(literal)) {
            (Some(coeff_l), Some(coeff_r)) => {
                let expected = coeff_l.clone() + coeff_r.clone();
                rassert!(
                    &expected == coeff_c,
                    CheckerError::ExpectedInteger(expected, conclusion.clone())
                );
            }
            (Some(coeff_l), _) => {
                rassert!(
                    coeff_l == coeff_c,
                    CheckerError::ExpectedInteger(coeff_l.clone(), conclusion.clone())
                );
            }
            (_, Some(coeff_r)) => {
                rassert!(
                    coeff_r == coeff_c,
                    CheckerError::ExpectedInteger(coeff_r.clone(), conclusion.clone())
                );
            }
            // ¬∃ x, (x ∈ C) ∧ ¬(x ∈ L) ∧ ¬(x ∈ R)
            _ => {
                // TODO: appropriate error type
                return Err(CheckerError::Unspecified);
            }
        }
    }

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
    let (pbsum_p, constant_p) = unwrap_pseudoboolean_inequality(clause)?;

    // Unwrap the conclusion inequality
    let (pbsum_c, constant_c) = unwrap_pseudoboolean_inequality(conclusion)?;

    // Verify constants match
    rassert!(
        scalar.clone() * constant_p.clone() == constant_c,
        CheckerError::ExpectedInteger(scalar.clone() * constant_p, conclusion.clone())
    );

    // Verify premise and conclusion share same keys
    assert_pbsum_same_keys(&pbsum_p, &pbsum_c)?;

    // Verify pseudo-boolean sums match
    for (literal, coeff_p) in pbsum_p {
        if let Some(coeff_c) = pbsum_c.get(&literal) {
            let expected = &scalar * coeff_p;
            rassert!(
                &expected == coeff_c,
                CheckerError::ExpectedInteger(expected.clone(), conclusion.clone())
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
    let (pbsum_p, constant_p) = unwrap_pseudoboolean_inequality(clause)?;

    // Unwrap the conclusion inequality
    let (pbsum_c, constant_c) = unwrap_pseudoboolean_inequality(conclusion)?;

    // Verify constants match ceil(c/d) == (c+d-1)/d
    rassert!(
        (constant_p.clone() + divisor.clone() - 1) / divisor.clone() == constant_c,
        CheckerError::ExpectedInteger(constant_p / divisor.clone(), conclusion.clone())
    );

    // Verify premise and conclusion share same keys
    assert_pbsum_same_keys(&pbsum_p, &pbsum_c)?;

    // Verify pseudo-boolean sums match
    for (literal, coeff_p) in pbsum_p {
        if let Some(coeff_c) = pbsum_c.get(&literal) {
            let expected: Integer = (coeff_p + &divisor - 1) / &divisor;
            rassert!(
                &expected == coeff_c,
                CheckerError::ExpectedInteger(expected.clone(), conclusion.clone())
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
    let (pbsum_p, constant_p) = unwrap_pseudoboolean_inequality(clause)?;

    // Unwrap the conclusion inequality
    let (pbsum_c, constant_c) = unwrap_pseudoboolean_inequality(conclusion)?;

    // Verify constants match
    rassert!(
        constant_p == constant_c,
        CheckerError::ExpectedInteger(constant_p.clone(), conclusion.clone())
    );

    // Verify premise and conclusion share same keys
    assert_pbsum_same_keys(&pbsum_p, &pbsum_c)?;

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
            // "Addition with Reduction" {
            //     r#"(assume c1 (>= (+ (* 2 x1) 0) 1))
            //        (assume c2 (>= (+ (* 1 (- 1 x1)) 0) 1))
            //        (step t1 (cl (>= (+ (* 1 x1) 0) 2)) :rule cp_addition :premises (c1 c2))"#: true,
            // }
            "Simple working examples" {
                r#"(assume c1 (>= (+ (* 1 x1) 0) 1))
                   (step t1 (cl (>= (+ (* 2 x1) 0) 2)) :rule cp_addition :premises (c1 c1))"#: true,

                r#"(assume c1 (>= (+ (* 1 x1) 0) 1))
                   (assume c2 (>= (+ (* 1 x2) 0) 1))
                   (step t1 (cl (>= (+ (* 1 x1) (* 1 x2) 0) 2)) :rule cp_addition :premises (c1 c2))"#: true,

                r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2) 0) 1))
                   (assume c2 (>= (+ (* 1 x2) (* 1 x1) 0) 1))
                   (step t1 (cl (>= (+ (* 2 x1) (* 3 x2) 0) 2)) :rule cp_addition :premises (c1 c2))"#: true,

            }
            "Missing Terms" {
                r#"(assume c1 (>= (+ (* 1 x1) 0) 1))
                   (assume c2 (>= (+ (* 1 x2) 0) 1))
                   (step t1 (cl (>= (+ (* 1 x1) 0) 2)) :rule cp_addition :premises (c1 c2))"#: false,

                r#"(assume c1 (>= (+ (* 1 x1) 0) 1))
                   (assume c2 (>= (+ (* 1 x2) 0) 1))
                   (step t1 (cl (>= (+ (* 1 x2) 0) 2)) :rule cp_addition :premises (c1 c2))"#: false,

                r#"(assume c1 (>= (+ (* 1 x1) 0) 1))
                   (assume c2 (>= (+ (* 1 x2) 0) 1))
                   (step t1 (cl (>= (+ (* 1 x1) (* 1 x2) (* 1 x3) 0) 2)) :rule cp_addition :premises (c1 c2))"#: false,

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
                r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2) 0) 1))
                   (step t1 (cl (>= (+ (* 2 x1) (* 4 x2) 0) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: true,
                r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2) (* 3 x3) 0) 1))
                   (step t1 (cl (>= (+ (* 2 x1) (* 4 x2) (* 6 x3) 0) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: true,
                r#"(assume c1 (>= (+ (* 1 x1) (* 2 (- 1 x2)) (* 3 x3) 0) 1))
                   (step t1 (cl (>= (+ (* 2 x1) (* 4 (- 1 x2)) (* 6 x3) 0) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: true,
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
            "Wrong number of clauses in the conclusion" {
                r#"(assume c1 (>= (+ (* 1 x1) 0) 1))
                   (step t1 (cl (>= (+ (* 2 x1) (* 2 x2) 0) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: false,

                r#"(assume c1 (>= (+ (* 1 x1) (* 2 x2) 0) 1))
                   (step t1 (cl (>= (+ (* 2 x1) 0) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: false,
            }
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
                (declare-fun x2 () Int)
                ",
            "Simple working examples" {
                r#"(assume c1 (>= (+ (* 2 x1) 0) 2))
                   (step t1 (cl (>= (+ (* 1 x1) 0) 1)) :rule cp_division :premises (c1) :args (2) )"#: true,
                r#"(assume c1 (>= (+ (* 2 (- 1 x1)) 0) 2))
                   (step t1 (cl (>= (+ (* 1 (- 1 x1)) 0) 1)) :rule cp_division :premises (c1) :args (2) )"#: true,
            }
            "Wrong division" {
                r#"(assume c1 (>= (+ (* 2 x1) 0) 2))
                   (step t1 (cl (>= (+ (* 2 x1) 0) 1)) :rule cp_division :premises (c1) :args (2) )"#: false,
                r#"(assume c1 (>= (+ (* 2 x1) 0) 2))
                   (step t1 (cl (>= (+ (* 1 x1) 0) 2)) :rule cp_division :premises (c1) :args (2) )"#: false,
            }
            "Ceiling of Division" {
                r#"(assume c1 (>= (+ (* 3 x1) 0) 2))
                   (step t1 (cl (>= (+ (* 2 x1) 0) 1)) :rule cp_division :premises (c1) :args (2) )"#: true,
                r#"(assume c1 (>= (+ (* 3 x1) 0) 2))
                   (step t1 (cl (>= (+ (* 1 x1) 0) 1)) :rule cp_division :premises (c1) :args (2) )"#: false,

                r#"(assume c1 (>= (+ (* 7 x1) 0) 2))
                   (step t1 (cl (>= (+ (* 4 x1) 0) 1)) :rule cp_division :premises (c1) :args (2) )"#: true,
                r#"(assume c1 (>= (+ (* 7 x1) 0) 2))
                   (step t1 (cl (>= (+ (* 3 x1) 0) 1)) :rule cp_division :premises (c1) :args (2) )"#: false,

                r#"(assume c1 (>= (+ (* 9 x1) 0) 2))
                   (step t1 (cl (>= (+ (* 5 x1) 0) 1)) :rule cp_division :premises (c1) :args (2) )"#: true,
                r#"(assume c1 (>= (+ (* 9 x1) 0) 2))
                   (step t1 (cl (>= (+ (* 4 x1) 0) 1)) :rule cp_division :premises (c1) :args (2) )"#: false,

                r#"(assume c1 (>= (+ (* 10 x1) 0) 3))
                   (step t1 (cl (>= (+ (* 4 x1) 0) 1)) :rule cp_division :premises (c1) :args (3) )"#: true,
                r#"(assume c1 (>= (+ (* 10 x1) 0) 3))
                   (step t1 (cl (>= (+ (* 3 x1) 0) 1)) :rule cp_division :premises (c1) :args (3) )"#: false,
           }
           "Missing terms" {
                r#"(assume c1 (>= (+ (* 2 x1) (* 1 x2) 0) 2))
                   (step t1 (cl (>= (+ (* 1 x1) 0) 1)) :rule cp_division :premises (c1) :args (2) )"#: false,

                 r#"(assume c1 (>= (+ (* 2 x1) 0) 2))
                   (step t1 (cl (>= (+ (* 1 x1) (* 1 x2) 0) 1)) :rule cp_division :premises (c1) :args (2) )"#: false,

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

                r#"(assume c1 (>= (+ (* 3 x1) (* 4 x2) (* 5 x3) 0) 3))
                   (step t1 (cl (>= (+ (* 3 x1) (* 3 x2) (* 3 x3) 0) 3)) :rule cp_saturation :premises (c1))"#: true,

                r#"(assume c1 (>= (+ (* 3 x1) (* 4 x2) (* 5 (- 1 x3)) 0) 3))
                   (step t1 (cl (>= (+ (* 3 x1) (* 3 x2) (* 3 (- 1 x3)) 0) 3)) :rule cp_saturation :premises (c1))"#: true,

            }
            "Wrong saturation" {
                r#"(assume c1 (>= (+ (* 2 x1) 0) 1))
                   (step t1 (cl (>= (+ (* 2 x1) 0) 1)) :rule cp_saturation :premises (c1))"#: false,

                r#"(assume c1 (>= (+ (* 2 x1) 0) 1))
                   (step t1 (cl (>= (+ (* 0 x1) 0) 1)) :rule cp_saturation :premises (c1))"#: false,

                r#"(assume c1 (>= (+ (* 3 x1) (* 4 x2) (* 5 x3) 0) 3))
                   (step t1 (cl (>= (+ (* 3 x1) (* 3 x2) (* 2 x3) 0) 3)) :rule cp_saturation :premises (c1))"#: false,

            }
            "Missing terms" {
                r#"(assume c1 (>= (+ (* 3 x1) (* 4 x2) (* 5 x3) 0) 3))
                   (step t1 (cl (>= (+ (* 3 x1) (* 3 x2) 0) 3)) :rule cp_saturation :premises (c1))"#: false,

                r#"(assume c1 (>= (+ (* 3 x1) (* 4 x2) 0) 3))
                   (step t1 (cl (>= (+ (* 3 x1) (* 3 x2) (* 3 x3) 0) 3)) :rule cp_saturation :premises (c1))"#: false,
            }

        }
    }
}
