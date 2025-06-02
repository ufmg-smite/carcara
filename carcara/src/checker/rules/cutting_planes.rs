use super::{
    assert_clause_len, assert_eq, assert_num_args, assert_num_premises, RuleArgs, RuleResult, Term,
};
use crate::ast::{Constant, Operator, TermPool};
use crate::checker::error::CheckerError;
use crate::checker::Rc;
use rug::Integer;
use std::collections::HashMap;

type PbHash = HashMap<String, Integer>;

fn split_sum(sum_term: &Rc<Term>) -> &[Rc<Term>] {
    if let Some(summation) = match_term!((+ ...) = sum_term) {
        summation
    } else {
        std::slice::from_ref(sum_term)
    }
}

fn get_pb_hashmap(pbsum: &Rc<Term>) -> Result<PbHash, CheckerError> {
    let mut hm = HashMap::new();
    let pbsum = split_sum(pbsum);

    //  Special case: single 0
    if pbsum.len() == 1 {
        if let Some(constant) = pbsum[0].as_integer() {
            if constant == 0 {
                return Ok(hm);
            }
            return Err(CheckerError::ExpectedInteger(
                Integer::from(0),
                pbsum[0].clone(),
            ));
        }
    }

    for term in pbsum {
        let (coeff, literal) =
            // Negated literal  (* c (- 1 x1))
            if let Some((coeff, (_, literal))) = match_term!((* coeff (- 1 literal)) = term) {
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
    let (pbsum, constant) = match_term_err!((>= pbsum constant) = clause)?;
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
        constant_l.clone() + constant_r.clone() == constant_c.clone() + slack.clone(),
        CheckerError::Explanation(format!(
            "Expected {} + {} == {} + {} ",
            constant_l.clone(),
            constant_r.clone(),
            constant_c.clone(),
            slack.clone()
        ))
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

pub fn cp_multiplication(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    // Check there is exactly one premise
    assert_num_premises(premises, 1)?;
    assert_clause_len(premises[0].clause, 1)?;
    let clause = &premises[0].clause[0];

    // Check there is exactly one arg
    assert_num_args(args, 1)?;
    let scalar: Integer = args[0].as_integer_err()?;

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
    let divisor: Integer = args[0].as_integer_err()?;

    // Rule only allows for positive integer arguments
    if divisor <= 0 {
        return Err(if divisor == 0 {
            CheckerError::DivOrModByZero
        } else {
            CheckerError::ExpectedNonnegInteger(args[0].clone())
        });
    }

    // Check there is exactly one conclusion
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

    // Check there is exactly one conclusion
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

pub fn cp_literal(RuleArgs { pool, args, conclusion, .. }: RuleArgs) -> RuleResult {
    assert_num_args(args, 1)?;
    // TODO: Set args type to FF 2

    if let Some(((c, (_, l)), _)) = match_term!((>= (* c (- 1 l)) 0) = &conclusion[0]) {
        rassert!(
            c.as_integer_err()? == 1,
            CheckerError::ExpectedInteger(1.into(), c.clone()),
        );
        let neg_l = build_term!(pool,(- 1 {l.clone()}));
        return assert_eq(&neg_l, &args[0]);
    }
    if let Some(((c, l), _)) = match_term!((>= (* c l) 0) = &conclusion[0]) {
        rassert!(
            c.as_integer_err()? == 1,
            CheckerError::ExpectedInteger(1.into(), c.clone()),
        );
        return assert_eq(l, &args[0]);
    }
    if let Some(((_, l), _)) = match_term!((>= (- 1 l) 0) = &conclusion[0]) {
        let neg_l = build_term!(pool,(- 1 {l.clone()}));
        return assert_eq(&neg_l, &args[0]);
    }
    if let Some((l, _)) = match_term!((>= l 0) = &conclusion[0]) {
        return assert_eq(l, &args[0]);
    }
    Err(CheckerError::Explanation(
        "No valid pattern was found".into(),
    ))
}

fn negate_term(t: &Rc<Term>, pool: &mut dyn TermPool) -> Result<Rc<Term>, CheckerError> {
    match t.as_ref() {
        Term::Op(Operator::Mult, args) => {
            if let [c, l] = &args[..] {
                let c = c.as_integer_err()?;
                // Check if already negative
                if c < 0 {
                    Ok(l.clone())
                } else {
                    let c_term = pool.add(Term::Const(Constant::Integer(-c)));
                    let negated_l = build_term!(pool,(* {c_term} {l.clone()}));
                    Ok(negated_l)
                }
            } else {
                Err(CheckerError::Explanation(
                    "Expected multiplication on 2 arguments".into(),
                ))
            }
        }
        _ => {
            // Arbitrary term gets negated
            let minus_one_term = pool.add(Term::Const(Constant::Integer((-1).into())));
            let negated_t = build_term!(pool,(* {minus_one_term} {t.clone()}));
            Ok(negated_t)
        }
    }
}

fn negate_sum(sum: &Vec<Rc<Term>>, pool: &mut dyn TermPool) -> Result<Vec<Rc<Term>>, CheckerError> {
    let mut ans: Vec<Rc<Term>> = vec![];
    // ? What about using a map...
    for t in sum {
        let neg_t = negate_term(t, pool)?;
        ans.push(neg_t);
    }
    Ok(ans)
}

pub fn cp_normalize(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let (lhs, rhs) = match_term_err!((= lhs rhs) = &conclusion[0])?;

    // Checking the left-hand-side is a supported relation
    let (rel, a, b) = match lhs.as_ref() {
        Term::Op(op, args) => {
            // It's a valid relation
            if !["=", ">", "<", ">=", "<="].contains(&op.to_string().as_str()) {
                return Err(CheckerError::Explanation(format!(
                    "Operator {op} is not a valid relation"
                )));
            }
            // Over two arguments
            let (a, b) = match &args[..] {
                [a, b] => Ok((a, b)),
                _ => Err(CheckerError::Explanation(format!(
                    "Expected two arguments of {op}, got {args:?}"
                ))),
            }?;
            Ok((op.to_string(), a, b))
        }
        _ => Err(CheckerError::Explanation(
            "Expected relation operator".into(),
        )),
    }?;

    let debug = rel == "<=";

    // Split `a` and `b` into list of added terms
    let a = split_sum(a);
    let b = split_sum(b);

    let mut vars: Vec<Rc<Term>> = vec![];
    let mut constant: Integer = 0.into();

    if debug {
        println!("\t\t\t\t\t\t\ta:{a:?}");
        println!("\t\t\t\t\t\t\tb:{b:?}");
    }
    // Separate the variables from constants
    for t in a {
        match t.as_ref() {
            Term::Const(Constant::Integer(k)) => constant -= k,
            _ => vars.push(t.clone()),
        }
    }
    for t in b {
        match t.as_ref() {
            Term::Const(Constant::Integer(k)) => constant += k,
            _ => {
                // Negation of the generic term
                let neg_t = negate_term(t, pool)?;
                vars.push(neg_t);
            }
        }
    }

    if debug {
        println!("VARS:\t\t\t\t\t\t\t{vars:?}");
        println!("CONSTANT:\t\t\t\t\t\t{constant:?}");
    }

    // Special variables when "=" uses two constraints
    let mut vars2: Vec<Rc<Term>> = vec![];
    let mut constant2: Integer = 0.into();

    // Eliminate other relations
    match rel.as_str() {
        ">" => constant += 1,
        "<" => {
            vars = negate_sum(&vars, pool)?;
            constant = 1 - constant;
        }
        "<=" => {
            vars = negate_sum(&vars, pool)?;
            constant = -constant;
        }
        "=" => {
            vars2 = negate_sum(&vars, pool)?;
            constant2 = -constant.clone();
        }
        _ => (),
    }

    if debug {
        println!("VARS AFTER ELIM:\t\t\t\t\t\t\t{vars:?}");
        println!("CONSTANT AFTER ELIM:\t\t\t\t\t\t{constant:?}");
        println!("VARS2 AFTER ELIM:\t\t\t\t\t\t\t{vars2:?}");
        println!("CONSTANT2 AFTER ELIM:\t\t\t\t\t\t{constant2:?}");
    }

    // TODO: Push Negations
    Ok(())
}
