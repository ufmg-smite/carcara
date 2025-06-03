use super::{
    assert_clause_len, assert_eq, assert_num_args, assert_num_premises, RuleArgs, RuleResult, Term,
};
use crate::ast::{Constant, Operator, TermPool};
use crate::checker::error::CheckerError;
use crate::checker::Rc;
use rug::Integer;
use std::collections::HashMap;

type PbHash = HashMap<String, Integer>;

// Helper to unwrap a summation list
pub fn split_summation(sum_term: &Rc<Term>) -> &[Rc<Term>] {
    if let Some(summation) = match_term!((+ ...) = sum_term) {
        summation
    } else {
        std::slice::from_ref(sum_term)
    }
}

fn get_pb_hashmap(pbsum: &Rc<Term>) -> Result<PbHash, CheckerError> {
    let mut hm = HashMap::new();
    let pbsum = split_summation(pbsum);

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

// -ci li + ψ >= k ==> ci neg_li + ψ >= k + ci
fn push_negation(
    vars: &mut Vec<Rc<Term>>,
    constant: &mut Integer,
    pool: &mut dyn TermPool,
) -> RuleResult {
    for t in vars {
        if let Some((c, l)) = match_term!((* c l) = t) {
            let c = c.as_integer_err()?;
            if c >= 0 {
                continue;
            }
            // Negate the PB `l`
            let neg_l: Rc<Term> = if let Some((_, x)) = match_term!((- 1 x) = l) {
                x.clone()
            } else {
                build_term!(pool,(- 1 {l.clone()}))
            };
            let c = -c; // Now c is strictly positive
            *constant += c.clone();
            *t = build_term!(pool, (* (const c) {neg_l.clone()}));
        };
    }
    Ok(())
}

fn flatten_mul(x: &Rc<Term>, pool: &mut dyn TermPool) -> Result<Rc<Term>, CheckerError> {
    let flat_x = if let Some((c, l)) = match_term!((* c l) = x) {
        let c = c.as_integer_err()?;
        if c == 1 {
            l.clone()
        } else if c == -1 {
            build_term!(pool,(- 1 {l.clone()}))
        } else {
            x.clone()
        }
    } else {
        x.clone()
    };
    Ok(flat_x)
}

fn pack_summation(vars: Vec<Rc<Term>>, pool: &mut dyn TermPool) -> Result<Rc<Term>, CheckerError> {
    if vars.len() > 1 {
        let args: Result<Vec<Rc<Term>>, CheckerError> =
            vars.iter().map(|x| flatten_mul(x, pool)).collect();
        Ok(pool.add(Term::Op(Operator::Add, args?)))
    } else {
        flatten_mul(&vars[0], pool)
    }
}

fn check_equivalent_inequalities(
    pool: &mut dyn TermPool,
    mut general_vars: Vec<Rc<Term>>,
    mut general_constant: Integer,
    normalized_vars: Vec<Rc<Term>>,
    normalized_constant: Integer,
) -> RuleResult {
    push_negation(&mut general_vars, &mut general_constant, pool)?;
    let general_vars = pack_summation(general_vars, pool)?;
    let normalized_vars = pack_summation(normalized_vars, pool)?;
    rassert!(
        general_constant == normalized_constant,
        CheckerError::Explanation(format!(
            "Mismatched constants {general_constant} != {normalized_constant}"
        ))
    );
    assert_eq(&general_vars, &normalized_vars)
}

// Transform a general summation relation to the normalized form
pub fn cp_normalize(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    let (general_relation, normalized_relation) =
        match_term_err!((= general_relation normalized_relation) = &conclusion[0])?;

    // Checking the left-hand-side is a supported relation operator
    let (relation_operator, general_arg_left, general_arg_right) = match general_relation.as_ref() {
        Term::Op(op, args) => {
            // It's a valid relation
            if !["=", ">", "<", ">=", "<="].contains(&op.to_string().as_str()) {
                Err(CheckerError::Explanation(format!(
                    "Operator {op} is not a valid relation"
                )))?;
            }
            // Over two arguments
            let (general_arg_left, general_arg_right) = match &args[..] {
                [general_arg_left, general_arg_right] => Ok((general_arg_left, general_arg_right)),
                _ => Err(CheckerError::Explanation(format!(
                    "Expected two arguments of {op}, got {args:?}"
                ))),
            }?;
            Ok((op.to_string(), general_arg_left, general_arg_right))
        }
        _ => Err(CheckerError::Explanation(
            "Expected relation operator".into(),
        )),
    }?;

    // Split general args into list of added terms
    let general_arg_left = split_summation(general_arg_left);
    let general_arg_right = split_summation(general_arg_right);

    let mut general_vars: Vec<Rc<Term>> = vec![];
    let mut general_constant: Integer = 0.into();

    // Separate the variables from constants
    // TODO: These lists are not "flat" enough, we still have (- (+ a b) (+ c d)) happening
    for left_term in general_arg_left {
        match left_term.as_ref() {
            Term::Const(Constant::Integer(k)) => general_constant -= k,
            _ => general_vars.push(left_term.clone()),
        }
    }
    for right_term in general_arg_right {
        match right_term.as_ref() {
            Term::Const(Constant::Integer(k)) => general_constant += k,
            _ => {
                // Negation of the generic term
                let neg_t = negate_term(right_term, pool)?;
                general_vars.push(neg_t);
            }
        }
    }

    // Special variables when "=" uses two constraints
    let mut general_vars_2: Vec<Rc<Term>> = vec![];
    let mut general_constant_2: Integer = 0.into();

    let mut negate_sum = |sum: &[Rc<Term>]| -> Result<Vec<Rc<Term>>, CheckerError> {
        sum.iter().map(|t| negate_term(t, pool)).collect()
    };

    // Eliminate other relations
    match relation_operator.as_str() {
        ">" => general_constant += 1,
        "<" => {
            general_vars = negate_sum(&general_vars)?;
            general_constant = 1 - general_constant;
        }
        "<=" => {
            general_vars = negate_sum(&general_vars)?;
            general_constant = -general_constant;
        }
        "=" => {
            general_vars_2 = negate_sum(&general_vars)?;
            general_constant_2 = -general_constant.clone();
        }
        ">=" => (), /* Nothing to be done */
        _ => {
            // Should be impossible to get here
            Err(CheckerError::Explanation(format!(
                "Invalid relation operator: {relation_operator}"
            )))?;
        }
    }

    if relation_operator == "=" {
        let ((normalized_vars, normalized_constant), (normalized_vars_2, normalized_constant_2)) =
            match_term_err!((and (>= normalized_vars normalized_constant) (>= normalized_vars_2 normalized_constant_2)) = normalized_relation)?;

        check_equivalent_inequalities(
            pool,
            general_vars,
            general_constant,
            split_summation(normalized_vars).to_vec(),
            normalized_constant.as_integer_err()?,
        )?;
        check_equivalent_inequalities(
            pool,
            general_vars_2,
            general_constant_2,
            split_summation(normalized_vars_2).to_vec(),
            normalized_constant_2.as_integer_err()?,
        )
    } else {
        let (normalized_vars, normalized_constant) =
            match_term_err!((>= normalized_vars normalized_constant) = normalized_relation)?;

        check_equivalent_inequalities(
            pool,
            general_vars,
            general_constant,
            split_summation(normalized_vars).to_vec(),
            normalized_constant.as_integer_err()?,
        )
    }
}
