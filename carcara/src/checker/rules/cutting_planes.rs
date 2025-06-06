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

/// Matches against a supported boolean relation ⋈ ∈ {≥,≤,=,>,<}.
fn match_supported_relation_err(
    term: &Rc<Term>,
) -> Result<(String, &Rc<Term>, &Rc<Term>), CheckerError> {
    match term.as_ref() {
        Term::Op(op, args) => {
            if !["=", ">", "<", ">=", "<="].contains(&op.to_string().as_str()) {
                Err(CheckerError::Explanation(format!(
                    "Operator {op} is not a valid relation"
                )))
            } else if let [lhs, rhs] = &args[..] {
                Ok((op.to_string(), lhs, rhs))
            } else {
                Err(CheckerError::WrongNumberOfArgs(2.into(), args.len()))
            }
        }
        _ => Err(CheckerError::Explanation(
            "Expected relation operator".into(),
        )),
    }
}

/// Negate an integer term, in general
/// a => (* -1 a)
/// When term has a coefficient, negates the coefficient
/// (* c l) => (* -c l)
fn negate_term(t: &Rc<Term>, pool: &mut dyn TermPool) -> Result<Rc<Term>, CheckerError> {
    match t.as_ref() {
        Term::Op(Operator::Mult, args) => {
            if let [c, l] = &args[..] {
                let c = -c.as_integer_err()?;
                let negated_l = build_term!(pool,(* (const c) {l.clone()}));
                Ok(negated_l)
            } else {
                Err(CheckerError::WrongNumberOfArgs(2.into(), args.len()))
            }
        }
        _ => {
            // Arbitrary term gets negated
            // TODO: How to fit `-1` into build_term ?
            let minus_one_term = pool.add(Term::Const(Constant::Integer((-1).into())));
            let negated_t = build_term!(pool,(* {minus_one_term} {t.clone()}));
            Ok(negated_t)
        }
    }
}

/// Maps a sum, as a list of terms, to the negation of each element
fn negate_sum(sum: &[Rc<Term>], pool: &mut dyn TermPool) -> Result<Vec<Rc<Term>>, CheckerError> {
    sum.iter().map(|t| negate_term(t, pool)).collect()
}

/// Collect the added or subtracted terms into a vector
/// (- (+ a b) (+ c d)) ==> [a,b,(* -1 c),(* -1 d)]
/// Accumulate constants into a Integer
/// (- (+ a 2) (+ 1 d)) ==> [a,(* -1 d)], 1
fn flatten_addition_tree(
    term: &Rc<Term>,
    pool: &mut dyn TermPool,
) -> Result<(Vec<Rc<Term>>, Integer), CheckerError> {
    match term.as_ref() {
        Term::Op(Operator::Add, args) => {
            let mut ans = vec![];
            let mut cnt = 0.into();
            for arg in args {
                let (va, ca) = flatten_addition_tree(arg, pool)?;
                ans.extend(va);
                cnt += ca;
            }
            Ok((ans, cnt))
        }
        Term::Op(Operator::Sub, args) => {
            if let [a, b] = &args[..] {
                let (va, ca) = flatten_addition_tree(a, pool)?;
                let (vb, cb) = flatten_addition_tree(b, pool)?;
                Ok(([&va[..], &(negate_sum(&vb, pool)?)[..]].concat(), ca - cb))
            } else {
                Err(CheckerError::WrongNumberOfArgs(2.into(), args.len()))
            }
        }
        Term::Const(Constant::Integer(k)) => Ok((vec![], k.clone())),
        _ => Ok((vec![term.clone()], 0.into())),
    }
}

/// Changes the list `vars` and Integer `constant` to avoid negative coefficients
/// `-ci li + ψ >= k` ==> `ci neg_li + ψ >= k + ci`
/// where `neg_li` is the opposite pseudo boolean variable, noted as `(- 1 li)`
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

/// Check that pseudo boolean inequalities are equivalent
/// `(>= vars_l kl)`, `(>= vars_r kr)`
/// Prerequisite: All variables are multiplied by **non-negative** coefficients
fn check_pb_inequalities(
    vars_l: &[Rc<Term>],
    kl: &Integer,
    vars_r: &[Rc<Term>],
    kr: &Integer,
) -> RuleResult {
    let remove_multiplication_by_1 = |t| {
        if let Some((_, l)) = match_term!((* 1 l) = t) {
            l
        } else {
            t
        }
    };

    for (var_l, var_r) in vars_l.iter().zip(vars_r) {
        let var_l = remove_multiplication_by_1(var_l);
        let var_r = remove_multiplication_by_1(var_r);
        assert_eq(var_l, var_r)?;
    }

    // TODO: Better error type. Is there a checker error for two Integers ?
    rassert!(
        kl == kr,
        CheckerError::Explanation(format!("Expected equal constants {kl} != {kr}"))
    );
    Ok(())
}

/// Transform a general summation relation to the normalized form
pub fn cp_normalize(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    // (⋈ a b) = (>= sum k)
    let (general_relation, normalized_relation) =
        match_term_err!((= general_relation normalized_relation) = &conclusion[0])?;

    // Checking the general relation is a supported relation operator
    // i.e. ⋈ ∈ {≥,≤,=,>,<}. in (⋈ a b)
    let (relation_operator, left_addition_tree, right_addition_tree) =
        match_supported_relation_err(general_relation)?;

    // Split general args into list of added terms
    let (left_vars, left_constant) = flatten_addition_tree(left_addition_tree, pool)?;
    let (right_vars, right_constant) = flatten_addition_tree(right_addition_tree, pool)?;

    // Create General Vars and Constant
    // TODO: Better concatenation?
    let mut general_vars: Vec<Rc<Term>> =
        [&left_vars[..], &negate_sum(&right_vars, pool)?[..]].concat();
    let mut general_constant: Integer = right_constant - left_constant;

    if relation_operator == "=" {
        // • 𝜑 = 𝑘 ⇒ (𝜑 ≥ 𝑘) ∧ (¬𝜑 ≥ −𝑘)
        let ((sum_l, kl), (sum_r, kr)) =
            match_term_err!((and (>= sum_l kl) (>= sum_r kr)) = normalized_relation)?;

        // Check (𝜑 ≥ 𝑘)
        push_negation(&mut general_vars, &mut general_constant, pool)?;

        let sum_l = split_summation(sum_l).to_vec();
        let kl = kl.as_integer_err()?;

        check_pb_inequalities(&general_vars, &general_constant, &sum_l, &kl)?;

        // Check (¬𝜑 ≥ −𝑘)
        let mut general_vars_neg = negate_sum(&general_vars, pool)?;
        let mut general_constant_neg = -general_constant.clone();
        push_negation(&mut general_vars_neg, &mut general_constant_neg, pool)?;

        let sum_r = split_summation(sum_r).to_vec();
        let kr = kr.as_integer_err()?;

        check_pb_inequalities(&general_vars_neg, &general_constant_neg, &sum_r, &kr)
    } else {
        let (normalized_vars, normalized_constant) =
            match_term_err!((>= normalized_vars normalized_constant) = normalized_relation)?;

        // Eliminate other relations
        match relation_operator.as_str() {
            // • 𝜑 > 𝑘 ⇒ 𝜑 ≥ 𝑘 + 1
            ">" => general_constant += 1,
            // • 𝜑 < 𝑘 ⇒ ¬𝜑 ≥ −𝑘 + 1
            "<" => {
                general_vars = negate_sum(&general_vars, pool)?;
                general_constant = 1 - general_constant;
            }
            // • 𝜑 ≤ 𝑘 ⇒ ¬𝜑 ≥ −𝑘
            "<=" => {
                general_vars = negate_sum(&general_vars, pool)?;
                general_constant = -general_constant;
            }
            ">=" => (), /* Nothing to be done */
            _ => {
                // Should be impossible to get here
                Err(CheckerError::Explanation(format!(
                    "Invalid relation operator: {relation_operator}"
                )))?;
            }
        }

        push_negation(&mut general_vars, &mut general_constant, pool)?;

        let normalized_vars = split_summation(normalized_vars).to_vec();

        let normalized_constant = normalized_constant.as_integer_err()?;

        check_pb_inequalities(
            &general_vars,
            &general_constant,
            &normalized_vars,
            &normalized_constant,
        )
    }
}
