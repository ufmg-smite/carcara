use super::Term;
use crate::checker::error::CheckerError;
use crate::checker::rules::{assert_clause_len, assert_num_args, assert_num_premises};
use crate::checker::Rc;
use rug::Integer;
use std::collections::HashMap;

use super::{RuleArgs, RuleResult};

type PbHash = HashMap<String, Integer>;

fn equals_integer_err(term: &Rc<Term>, expected: &Integer) -> Result<(), CheckerError> {
    let n = term.as_integer_err()?;
    rassert!(
        &n == expected,
        CheckerError::ExpectedInteger(n.clone(), term.clone())
    );
    Ok(())
}

fn get_pb_hashmap(pbsum: &[Rc<Term>]) -> Result<PbHash, CheckerError> {
    let mut hm = HashMap::new();
    let n = pbsum.len() - 1;

    for term in pbsum.iter().take(n) {
        let (coeff, literal) =
            // Negated literal  (* c (- 1 x1))
            if let Some((coeff, (one, literal))) = match_term!((* coeff (- one literal)) = term) {
                equals_integer_err(one,&Integer::from(1))?;
                (coeff, format!("~{}",literal))
            // Plain literal    (* c x1)
            } else if let Some((coeff, literal)) = match_term!((* coeff literal) = term) {
                (coeff, format!("{}",literal))
            } else {
                return Err(CheckerError::Explanation(format!("Term is neither plain nor negated: {}",term)));
            };

        let coeff = coeff.as_integer_err()?;
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

fn add_pbsums(pbsum_a: &PbHash, pbsum_b: &PbHash) -> PbHash {
    let mut res = pbsum_a.clone();

    for (lit, cb) in pbsum_b {
        res.entry(lit.clone())
            .and_modify(|ca| *ca += cb)
            .or_insert(cb.clone());
    }

    res
}

fn is_negated_literal(lit: &str) -> bool {
    lit.starts_with('~')
}

trait NegatedLiterals {
    fn get_opposite(&self, lit: &str) -> Option<&Integer>;
}

impl NegatedLiterals for PbHash {
    fn get_opposite(&self, lit: &str) -> Option<&Integer> {
        if let Some(plain_lit) = lit.strip_prefix('~') {
            self.get(plain_lit)
        } else {
            self.get(&format!("~{}", lit))
        }
    }
}

/// Cancel out opposite coefficients
fn reduce_pbsum(pbsum: &PbHash) -> (PbHash, Integer) {
    let mut slack = Integer::from(0);
    let mut res = pbsum.clone();
    let mut changes: Vec<(String, Integer)> = Vec::new();

    for lit in res.keys() {
        if is_negated_literal(lit) {
            continue;
        }
        let pos = res.get(lit);
        let neg = res.get_opposite(lit);
        if neg.is_none() {
            continue;
        }

        let pos = pos.unwrap();
        let neg = neg.unwrap();

        slack += Ord::min(pos, neg);

        if pos > neg {
            let diff = pos.clone() - neg;
            changes.push((lit.clone(), diff)); // Update lit to diff
            changes.push((format!("~{lit}"), Integer::from(0))); // Set ~lit to 0
        } else {
            let diff = neg.clone() - pos;
            changes.push((lit.clone(), Integer::from(0))); // Set lit to 0
            changes.push((format!("~{lit}"), diff)); // Update ~lit to neg - pos
        }
    }

    // Apply all changes after the loop
    for (lit, value) in changes {
        res.insert(lit, value);
    }

    (res, slack)
}

/// Checks that every key in ``pbsum_a`` is present in ``pbsum_b``
/// ha ⊆ hb
fn assert_pbsum_subset_keys(pbsum_a: &PbHash, pbsum_b: &PbHash) -> Result<(), CheckerError> {
    for key in pbsum_a.keys() {
        let val = pbsum_a.get(key).unwrap();

        // Zero coefficient is ignored.
        if val == &Integer::from(0) {
            continue;
        }

        if pbsum_b.get(key).is_none() {
            return Err(CheckerError::Explanation(format!(
                "Key {} of {:?} not found in {:?}",
                key, pbsum_b, pbsum_a
            )));
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

    // Add both sides regardless of negation
    let pbsum_lr = add_pbsums(&pbsum_l, &pbsum_r);

    // Apply reduction to cancel out opposite coefficients
    let (pbsum_lr_reduced, slack) = reduce_pbsum(&pbsum_lr);

    // Verify constants match (with slack)
    rassert!(
        constant_l.clone() + constant_r.clone() == constant_c + slack.clone(),
        CheckerError::ExpectedInteger(constant_l.clone() + constant_r.clone(), conclusion.clone())
    );

    // Verify premise and conclusion share same keys
    assert_pbsum_same_keys(&pbsum_lr_reduced, &pbsum_c)?;

    // Verify pseudo-boolean sums match
    for (literal, coeff_c) in &pbsum_c {
        if *coeff_c == 0 {
            continue;
        }
        match pbsum_lr_reduced.get(literal) {
            Some(coeff_lr_reduced) => {
                rassert!(
                    coeff_lr_reduced == coeff_c,
                    CheckerError::ExpectedInteger(coeff_lr_reduced.clone(), conclusion.clone())
                );
            }
            // ¬∃ x, (x ∈ C) ∧ ¬(x ∈ L) ∧ ¬(x ∈ R)
            _ => {
                return Err(CheckerError::Explanation(format!(
                    "Literal of the conclusion not present in either premises: {}",
                    literal
                )));
            }
        }
    }

    Ok(())
}

pub fn cp_multiplication(RuleArgs { .. }: RuleArgs) -> RuleResult {
    Err(CheckerError::Unspecified)
}

pub fn cp_division(RuleArgs { .. }: RuleArgs) -> RuleResult {
    Err(CheckerError::Unspecified)
}

pub fn cp_saturation(RuleArgs { .. }: RuleArgs) -> RuleResult {
    Err(CheckerError::Unspecified)
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
            "Addition with Reduction" {
                r#"(assume c1 (>= (+ (* 1 (- 1 x1)) 0) 1))
                   (assume c2 (>= (+ (* 2 x1) 0) 1))
                   (step t1 (cl (>= (+ (* 1 x1) (* 0 x2) 0) 1)) :rule cp_addition :premises (c1 c2))"#: true,

                r#"(assume c1 (>= (+ (* 2 x1) 0) 1))
                   (assume c2 (>= (+ (* 1 (- 1 x1)) 0) 1))
                   (step t1 (cl (>= (+ (* 1 x1) 0) 1)) :rule cp_addition :premises (c1 c2))"#: true,

                r#"(assume c1 (>= (+ (* 2 x1) (* 3 x2) 0) 2))
                   (assume c2 (>= (+ (* 1 (- 1 x1)) (* 3 (- 1 x2)) 0) 4))
                   (step t1 (cl (>= (+ (* 1 x1) 0) 2)) :rule cp_addition :premises (c1 c2))"#: true,
            }
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
    fn cp_multiplication() {}

    #[test]
    fn cp_division() {}

    #[test]
    fn cp_saturation() {}
}
