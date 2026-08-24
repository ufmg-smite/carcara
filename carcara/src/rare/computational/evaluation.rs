use std::sync::Arc;

use crate::rare::language::EggStatement;
use egglog::{
    ast::{Span, Symbol},
    constraint::{SimpleTypeConstraint, TypeConstraint},
    sort::{BigRatSort, FromSort, I64Sort},
    ArcSort, EGraph, PrimitiveLike, Value,
};
use num::{rational::BigRational, ToPrimitive};

struct BigRatFloorI64;

impl PrimitiveLike for BigRatFloorI64 {
    fn name(&self) -> Symbol {
        Symbol::from("bigrat_floor_i64")
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        SimpleTypeConstraint::new(
            self.name(),
            vec![Arc::new(BigRatSort), Arc::new(I64Sort)],
            span.clone(),
        )
        .into_box()
    }

    fn apply(
        &self,
        values: &[Value],
        _sorts: (&[ArcSort], &ArcSort),
        _egraph: Option<&mut EGraph>,
    ) -> Option<Value> {
        if values.len() != 1 {
            return None;
        }

        let value = BigRational::load(&BigRatSort, &values[0]);
        value.floor().to_i64().map(Value::from)
    }
}

pub fn evaluation_rules() -> Vec<EggStatement> {
    // Include the egglog file content at compile time
    let egglog_content = include_str!("evaluation.egglog");
    vec![EggStatement::Raw(egglog_content.to_owned())]
}

pub fn register_evaluation_primitives(egraph: &mut EGraph) {
    egraph.add_primitive(BigRatFloorI64);
}

/// Test module for evaluation rules debugging using the engine
#[cfg(test)]
pub mod tests {
    use crate::ast::pool::PrimitivePool;
    use crate::ast::rare_rules::RareStatements;
    use crate::ast::{ProofNode, Rc, StepNode};
    use crate::parser::{parse_instance_with_pool, Config, Parser};
    use crate::rare::engine::{run_egglog, RunEgglogOptions};

    /// Returns true if debug-egglog feature is enabled
    /// Run with: cargo test --features debug-egglog <`test_name`> -- --nocapture
    fn debug_egglog() -> bool {
        cfg!(feature = "debug-egglog")
    }

    const DEFINITIONS: &str = r#"
        (declare-fun x () Bool)
        (declare-fun y () Bool)
        (declare-fun z () Bool)
        (declare-fun a () Int)
        (declare-fun b () Int)
    "#;

    const ROUND_RETRY_DEFINITIONS: &str = r#"
        (declare-fun f () Bool)
    "#;

    const DEEP_ROUND_RETRY_DEFINITIONS: &str = r#"
        (declare-fun f () Bool)
    "#;

    const ROUND_RETRY_RULES: &str = r#"
        (declare-rare-rule late-eval ()
          :args ()
          :conclusion (= f (or false true))
        )
    "#;

    const DEEP_ROUND_RETRY_RULES: &str = r#"
        (declare-rare-rule late-eval ()
          :args ()
          :conclusion (= f (or false (or false (or false (or false (or false (or false (or false (or false true)))))))))
        )
    "#;

    /// Parse a term from a string with boolean/arithmetic definitions
    fn parse_term(pool: &mut PrimitivePool, term_str: &str) -> Rc<crate::ast::Term> {
        parse_term_with_definitions(pool, DEFINITIONS, term_str)
    }

    fn parse_term_with_definitions(
        pool: &mut PrimitivePool,
        definitions: &str,
        term_str: &str,
    ) -> Rc<crate::ast::Term> {
        let config = Config {
            apply_function_defs: true,
            expand_lets: false,
            allow_int_real_subtyping: false,
            strict: false,
            parse_hole_args: false,
        };
        let mut parser = Parser::new(pool, config, definitions).expect("parser error");
        parser.parse_problem().expect("parse problem error");
        parser.reset(term_str).expect("reset error");
        parser.parse_term().expect("parse term error")
    }

    /// Create an empty Rules database (evaluation rules are hardcoded in egglog)
    fn empty_rules() -> RareStatements {
        RareStatements::default()
    }

    fn parse_rare_rules(
        pool: &mut PrimitivePool,
        definitions: &str,
        source: &str,
    ) -> RareStatements {
        let config = Config {
            apply_function_defs: true,
            expand_lets: false,
            allow_int_real_subtyping: false,
            strict: false,
            parse_hole_args: false,
        };
        let (_, _, rules) = parse_instance_with_pool(definitions, "", Some(source), config, pool)
            .expect("rare rules parse error");
        rules
    }

    /// Create a minimal proof node with no premises
    fn dummy_proof_node(
        pool: &mut PrimitivePool,
        conclusion: Rc<crate::ast::Term>,
    ) -> Rc<ProofNode> {
        dummy_proof_node_with_id(pool, "test", conclusion)
    }

    fn dummy_proof_node_with_id(
        _pool: &mut PrimitivePool,
        id: &str,
        conclusion: Rc<crate::ast::Term>,
    ) -> Rc<ProofNode> {
        let step = StepNode {
            id: id.to_owned(),
            depth: 0,
            clause: vec![conclusion],
            rule: "hole".to_owned(),
            premises: vec![],
            args: vec![],
            discharge: vec![],
            previous_step: None,
        };
        Rc::new(ProofNode::Step(step))
    }

    /// Try to elaborate a conclusion term using `run_egglog`
    /// Set `DEBUG_EGGLOG=1` env var to print generated egglog code
    fn try_elaborate(conclusion_str: &str) -> Result<(), String> {
        try_elaborate_with_debug(conclusion_str, debug_egglog())
    }

    /// Try to elaborate with explicit debug flag
    fn try_elaborate_with_debug(conclusion_str: &str, debug: bool) -> Result<(), String> {
        let mut pool = PrimitivePool::new();
        let conclusion = parse_term(&mut pool, conclusion_str);
        let rules = empty_rules();
        let root = dummy_proof_node(&mut pool, conclusion.clone());
        let (result, code) = run_egglog(
            &mut pool,
            (conclusion, &root),
            &rules,
            RunEgglogOptions::default(),
        );
        if debug {
            println!(
                "\n=== Generated egglog code ===\n{}\n=== End egglog code ===\n",
                code
            );
        }
        result.map(|_| ())
    }

    fn try_elaborate_with_rules_and_options(
        definitions: &str,
        conclusion_str: &str,
        rules_source: &str,
        options: RunEgglogOptions,
        debug: bool,
    ) -> Result<(), String> {
        let mut pool = PrimitivePool::new();
        let conclusion = parse_term_with_definitions(&mut pool, definitions, conclusion_str);
        let rules = parse_rare_rules(&mut pool, definitions, rules_source);
        let root = dummy_proof_node(&mut pool, conclusion.clone());
        let (result, code) = run_egglog(&mut pool, (conclusion, &root), &rules, options);
        if debug {
            println!(
                "\n=== Generated egglog code ===\n{}\n=== End egglog code ===\n",
                code
            );
        }
        result.map(|_| ())
    }

    fn try_elaborate_with_rules_and_options_and_code(
        definitions: &str,
        conclusion_str: &str,
        rules_source: &str,
        options: RunEgglogOptions,
        debug: bool,
    ) -> (Result<(), String>, String) {
        let mut pool = PrimitivePool::new();
        let conclusion = parse_term_with_definitions(&mut pool, definitions, conclusion_str);
        let rules = parse_rare_rules(&mut pool, definitions, rules_source);
        let root = dummy_proof_node(&mut pool, conclusion.clone());
        let (result, code) = run_egglog(&mut pool, (conclusion, &root), &rules, options);
        if debug {
            println!(
                "\n=== Generated egglog code ===\n{}\n=== End egglog code ===\n",
                code
            );
        }
        (result.map(|_| ()), code)
    }

    fn goal_schedule_round_count(code: &str) -> usize {
        code.lines()
            .filter(|line| line.contains("(run list-ruleset)))"))
            .count()
    }

    /// Just print the generated egglog code without running it
    #[allow(dead_code)]
    fn print_egglog_code(conclusion_str: &str) {
        let mut pool = PrimitivePool::new();
        let conclusion = parse_term(&mut pool, conclusion_str);
        let rules = empty_rules();
        let root = dummy_proof_node(&mut pool, conclusion.clone());
        let (_, code) = run_egglog(
            &mut pool,
            (conclusion, &root),
            &rules,
            RunEgglogOptions::default(),
        );
        println!(
            "\n=== Generated egglog code for: {} ===\n{}\n=== End ===\n",
            conclusion_str, code
        );
    }

    #[test]
    fn test_goal_schedule_retry_rounds() {
        let one_round = try_elaborate_with_rules_and_options(
            ROUND_RETRY_DEFINITIONS,
            "(= f true)",
            ROUND_RETRY_RULES,
            RunEgglogOptions {
                max_goal_schedule_rounds: 1,
                ..RunEgglogOptions::default()
            },
            debug_egglog(),
        );
        assert!(
            one_round.is_err(),
            "single goal schedule round unexpectedly succeeded"
        );

        let retried = try_elaborate_with_rules_and_options(
            ROUND_RETRY_DEFINITIONS,
            "(= f true)",
            ROUND_RETRY_RULES,
            RunEgglogOptions::default(),
            debug_egglog(),
        );
        assert!(
            retried.is_ok(),
            "goal schedule retries failed: {:?}",
            retried.err()
        );
    }

    #[test]
    fn test_continous_saturation_retries_one_run_until_success() {
        let bounded = try_elaborate_with_rules_and_options(
            DEEP_ROUND_RETRY_DEFINITIONS,
            "(= f true)",
            DEEP_ROUND_RETRY_RULES,
            RunEgglogOptions {
                max_goal_schedule_rounds: 1,
                ..RunEgglogOptions::default()
            },
            debug_egglog(),
        );
        assert!(
            bounded.is_err(),
            "single bounded goal schedule round unexpectedly succeeded"
        );

        let (result, code) = try_elaborate_with_rules_and_options_and_code(
            DEEP_ROUND_RETRY_DEFINITIONS,
            "(= f true)",
            DEEP_ROUND_RETRY_RULES,
            RunEgglogOptions {
                continuous_saturation: true,
                ..RunEgglogOptions::default()
            },
            debug_egglog(),
        );
        assert!(
            result.is_ok(),
            "continuous goal schedule failed: {:?}",
            result.err()
        );
        assert!(
            goal_schedule_round_count(&code) > 1,
            "expected more than one one-run round, got:\n{}",
            code
        );
        assert!(
            !code.contains("(run-schedule (repeat 2 (run list-ruleset)))")
                && !code.contains("(run-schedule (repeat 3 (run list-ruleset)))"),
            "continuous saturation should run one iteration per round, got:\n{}",
            code
        );
    }

    // ============ Boolean Operations Tests ============

    /// Test not true = false
    #[test]
    fn test_not_true() {
        let result = try_elaborate("(= (not true) false)");
        assert!(result.is_ok(), "not true failed: {:?}", result.err());
    }

    /// Test not false = true
    #[test]
    fn test_not_false() {
        let result = try_elaborate("(= (not false) true)");
        assert!(result.is_ok(), "not false failed: {:?}", result.err());
    }

    /// Test and true true = true
    #[test]
    fn test_and_true_true() {
        let result = try_elaborate("(= (and true true) true)");
        assert!(result.is_ok(), "and true true failed: {:?}", result.err());
    }

    /// Test and true false = false
    #[test]
    fn test_and_true_false() {
        let result = try_elaborate("(= (and true false) false)");
        assert!(result.is_ok(), "and true false failed: {:?}", result.err());
    }

    /// Test or false false = false
    #[test]
    fn test_or_false_false() {
        let result = try_elaborate("(= (or false false) false)");
        assert!(result.is_ok(), "or false false failed: {:?}", result.err());
    }

    /// Test or true false = true
    #[test]
    fn test_or_true_false() {
        let result = try_elaborate("(= (or true false) true)");
        assert!(result.is_ok(), "or true false failed: {:?}", result.err());
    }

    /// Test xor true true = false
    #[test]
    fn test_xor_true_true() {
        let result = try_elaborate("(= (xor true true) false)");
        assert!(result.is_ok(), "xor true true failed: {:?}", result.err());
    }

    /// Test xor true false = true
    #[test]
    fn test_xor_true_false() {
        let result = try_elaborate("(= (xor true false) true)");
        assert!(result.is_ok(), "xor true false failed: {:?}", result.err());
    }

    /// Test implies: true => false = false
    #[test]
    fn test_implies_true_false() {
        let result = try_elaborate("(= (=> true false) false)");
        assert!(
            result.is_ok(),
            "implies true false failed: {:?}",
            result.err()
        );
    }

    /// Test implies: false => true = true
    #[test]
    fn test_implies_false_true() {
        let result = try_elaborate("(= (=> false true) true)");
        assert!(
            result.is_ok(),
            "implies false true failed: {:?}",
            result.err()
        );
    }

    /// Test ite: ite true x y = x
    #[test]
    fn test_ite_true() {
        let result = try_elaborate("(= (ite true x y) x)");
        assert!(result.is_ok(), "ite true failed: {:?}", result.err());
    }

    /// Test ite: ite false x y = y
    #[test]
    fn test_ite_false() {
        let result = try_elaborate("(= (ite false x y) y)");
        assert!(result.is_ok(), "ite false failed: {:?}", result.err());
    }

    // ============ Equality Tests ============

    /// Test integer equality: 5 = 5
    #[test]
    fn test_int_equality_same() {
        let result = try_elaborate("(= (= 5 5) true)");
        assert!(
            result.is_ok(),
            "int equality same failed: {:?}",
            result.err()
        );
    }

    /// Test integer inequality: 3 = 5
    #[test]
    fn test_int_equality_diff() {
        let result = try_elaborate("(= (= 3 5) false)");
        assert!(
            result.is_ok(),
            "int equality diff failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_bitvector_literal_reflexivity() {
        let result = try_elaborate("(= (_ bv1 8) (_ bv1 8))");
        assert!(
            result.is_ok(),
            "bit-vector literal reflexivity failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_bitvector_literals_are_lowered_losslessly() {
        let result = try_elaborate("(= (_ bv0 65) (_ bv18446744073709551616 65))");
        assert!(
            result.is_err(),
            "distinct large bit-vector literals were incorrectly equated"
        );
    }

    // ============ Additional Tests ============

    /// Test double negation: not (not true) = true
    #[test]
    fn test_double_negation() {
        let result = try_elaborate("(= (not (not true)) true)");
        assert!(result.is_ok(), "double negation failed: {:?}", result.err());
    }

    /// Test and false false = false
    #[test]
    fn test_and_false_false() {
        let result = try_elaborate("(= (and false false) false)");
        assert!(result.is_ok(), "and false false failed: {:?}", result.err());
    }

    /// Test or true true = true
    #[test]
    fn test_or_true_true() {
        let result = try_elaborate("(= (or true true) true)");
        assert!(result.is_ok(), "or true true failed: {:?}", result.err());
    }

    /// Test xor false false = false
    #[test]
    fn test_xor_false_false() {
        let result = try_elaborate("(= (xor false false) false)");
        assert!(result.is_ok(), "xor false false failed: {:?}", result.err());
    }

    /// Test implies true true = true
    #[test]
    fn test_implies_true_true() {
        let result = try_elaborate("(= (=> true true) true)");
        assert!(
            result.is_ok(),
            "implies true true failed: {:?}",
            result.err()
        );
    }

    /// Test implies false false = true
    #[test]
    fn test_implies_false_false() {
        let result = try_elaborate("(= (=> false false) true)");
        assert!(
            result.is_ok(),
            "implies false false failed: {:?}",
            result.err()
        );
    }

    /// Test boolean equality: true = true
    #[test]
    fn test_bool_equality_same() {
        let result = try_elaborate("(= (= true true) true)");
        assert!(
            result.is_ok(),
            "bool equality same failed: {:?}",
            result.err()
        );
    }

    /// Test boolean equality: true = false
    #[test]
    fn test_bool_equality_diff() {
        let result = try_elaborate("(= (= true false) false)");
        assert!(
            result.is_ok(),
            "bool equality diff failed: {:?}",
            result.err()
        );
    }

    /// Test nested: and (or true false) true = true
    #[test]
    fn test_nested_and_or() {
        let result = try_elaborate("(= (and (or true false) true) true)");
        assert!(result.is_ok(), "nested and or failed: {:?}", result.err());
    }

    /// Test nested: or (and false true) false = false
    #[test]
    fn test_nested_or_and() {
        let result = try_elaborate("(= (or (and false true) false) false)");
        assert!(result.is_ok(), "nested or and failed: {:?}", result.err());
    }

    // ============ Arithmetic Comparisons Tests ============

    /// Test less than: 3 < 5 = true
    #[test]
    fn test_less_than_true() {
        let result = try_elaborate("(= (< 3 5) true)");
        assert!(result.is_ok(), "less than true failed: {:?}", result.err());
    }

    /// Test less than: 5 < 3 = false
    #[test]
    fn test_less_than_false() {
        let result = try_elaborate("(= (< 5 3) false)");
        assert!(result.is_ok(), "less than false failed: {:?}", result.err());
    }

    /// Test less than: 3 < 3 = false (equal case)
    #[test]
    fn test_less_than_equal() {
        let result = try_elaborate("(= (< 3 3) false)");
        assert!(result.is_ok(), "less than equal failed: {:?}", result.err());
    }

    /// Test less than or equal: 3 <= 5 = true
    #[test]
    fn test_leq_true() {
        let result = try_elaborate("(= (<= 3 5) true)");
        assert!(result.is_ok(), "leq true failed: {:?}", result.err());
    }

    /// Test less than or equal: 5 <= 3 = false
    #[test]
    fn test_leq_false() {
        let result = try_elaborate("(= (<= 5 3) false)");
        assert!(result.is_ok(), "leq false failed: {:?}", result.err());
    }

    /// Test less than or equal: 3 <= 3 = true (equal case)
    #[test]
    fn test_leq_equal() {
        let result = try_elaborate("(= (<= 3 3) true)");
        assert!(result.is_ok(), "leq equal failed: {:?}", result.err());
    }

    /// Test greater than: 5 > 3 = true
    #[test]
    fn test_greater_than_true() {
        let result = try_elaborate("(= (> 5 3) true)");
        assert!(
            result.is_ok(),
            "greater than true failed: {:?}",
            result.err()
        );
    }

    /// Test greater than: 3 > 5 = false
    #[test]
    fn test_greater_than_false() {
        let result = try_elaborate("(= (> 3 5) false)");
        assert!(
            result.is_ok(),
            "greater than false failed: {:?}",
            result.err()
        );
    }

    /// Test greater than: 3 > 3 = false (equal case)
    #[test]
    fn test_greater_than_equal() {
        let result = try_elaborate("(= (> 3 3) false)");
        assert!(
            result.is_ok(),
            "greater than equal failed: {:?}",
            result.err()
        );
    }

    /// Test greater than or equal: 5 >= 3 = true
    #[test]
    fn test_geq_true() {
        let result = try_elaborate("(= (>= 5 3) true)");
        assert!(result.is_ok(), "geq true failed: {:?}", result.err());
    }

    /// Test greater than or equal: 3 >= 5 = false
    #[test]
    fn test_geq_false() {
        let result = try_elaborate("(= (>= 3 5) false)");
        assert!(result.is_ok(), "geq false failed: {:?}", result.err());
    }

    /// Test greater than or equal: 3 >= 3 = true (equal case)
    #[test]
    fn test_geq_equal() {
        let result = try_elaborate("(= (>= 3 3) true)");
        assert!(result.is_ok(), "geq equal failed: {:?}", result.err());
    }

    /// Test negative numbers: -5 < 3 = true
    #[test]
    fn test_less_than_negative() {
        let result = try_elaborate("(= (< (- 0 5) 3) true)");
        assert!(
            result.is_ok(),
            "less than negative failed: {:?}",
            result.err()
        );
    }

    /// Test negative numbers: 3 > -5 = true
    #[test]
    fn test_greater_than_negative() {
        let result = try_elaborate("(= (> 3 (- 0 5)) true)");
        assert!(
            result.is_ok(),
            "greater than negative failed: {:?}",
            result.err()
        );
    }

    // ============ Arithmetic Operations Tests ============

    /// Test addition: 3 + 5 = 8
    #[test]
    fn test_add_integers() {
        let result = try_elaborate("(= (+ 3 5) 8)");
        assert!(result.is_ok(), "add integers failed: {:?}", result.err());
    }

    /// Test subtraction: 10 - 3 = 7
    #[test]
    fn test_sub_integers() {
        let result = try_elaborate("(= (- 10 3) 7)");
        assert!(result.is_ok(), "sub integers failed: {:?}", result.err());
    }

    /// Test unary negation: -(5) = -5
    #[test]
    fn test_unary_neg() {
        let result = try_elaborate("(= (- 5) (- 0 5))");
        assert!(result.is_ok(), "unary neg failed: {:?}", result.err());
    }

    /// Test multiplication: 3 * 4 = 12
    #[test]
    fn test_mult_integers() {
        let result = try_elaborate("(= (* 3 4) 12)");
        assert!(result.is_ok(), "mult integers failed: {:?}", result.err());
    }

    /// Real multiplication that exceeds egglog i64 capacity should evaluate through `BigRat`.
    #[test]
    fn test_real_multiplication_overflow_uses_bigrat() {
        let result = try_elaborate("(= (* 3037000500.0 3037000500.0) 9223372037000250000.0)");
        assert!(
            result.is_ok(),
            "overflowing real multiplication failed: {:?}",
            result.err()
        );
    }

    /// Real addition whose result exceeds i64 should evaluate through `BigRat`.
    #[test]
    fn test_real_addition_overflow_uses_bigrat() {
        let result = try_elaborate("(= (+ 9223372036854775800.0 10.0) 9223372036854775810.0)");
        assert!(
            result.is_ok(),
            "overflowing real addition failed: {:?}",
            result.err()
        );
    }

    /// Real subtraction whose result exceeds i64 should evaluate through `BigRat`.
    #[test]
    fn test_real_subtraction_overflow_uses_bigrat() {
        let result =
            try_elaborate("(= (- (- 9223372036854775800.0) 10.0) (- 9223372036854775810.0))");
        assert!(
            result.is_ok(),
            "overflowing real subtraction failed: {:?}",
            result.err()
        );
    }

    /// Real division whose cross-product exceeds i64 should evaluate through `BigRat`.
    #[test]
    fn test_real_division_overflow_uses_bigrat() {
        let result =
            try_elaborate("(= (/ 3037000500.0 (/ 1.0 3037000500.0)) 9223372037000250000.0)");
        assert!(
            result.is_ok(),
            "overflowing real division failed: {:?}",
            result.err()
        );
    }

    /// Real comparison whose cross-product exceeds i64 should evaluate through `BigRat`.
    #[test]
    fn test_real_comparison_overflow_uses_bigrat() {
        let result = try_elaborate("(= (not (< 3037000500.0 (/ 1.0 3037000500.0))) true)");
        assert!(
            result.is_ok(),
            "overflowing real comparison failed: {:?}",
            result.err()
        );
    }

    /// Test integer division: 10 div 3 = 3
    #[test]
    fn test_div_integers() {
        let result = try_elaborate("(= (div 10 3) 3)");
        assert!(result.is_ok(), "div integers failed: {:?}", result.err());
    }

    /// Test modulo: 10 mod 3 = 1
    #[test]
    fn test_mod_integers() {
        let result = try_elaborate("(= (mod 10 3) 1)");
        assert!(result.is_ok(), "mod integers failed: {:?}", result.err());
    }

    // Note: div_total and mod_total are not standard SMT-LIB operators

    /// Test combined arithmetic: (3 + 5) * 2 = 16
    #[test]
    fn test_combined_arith() {
        let result = try_elaborate("(= (* (+ 3 5) 2) 16)");
        assert!(result.is_ok(), "combined arith failed: {:?}", result.err());
    }

    /// Test subtraction with negatives: 3 - 5 = -2
    #[test]
    fn test_sub_negative_result() {
        let result = try_elaborate("(= (- 3 5) (- 0 2))");
        assert!(
            result.is_ok(),
            "sub negative result failed: {:?}",
            result.err()
        );
    }

    // ============ Arithmetic Conversions & Predicates Tests ============
    // Note: to_int, is_int, to_real need language.rs mapping to work

    /// Test abs on positive integer
    #[test]
    fn test_abs_positive() {
        let result = try_elaborate("(= (abs 5) 5)");
        assert!(result.is_ok(), "abs positive failed: {:?}", result.err());
    }

    /// Test abs on negative integer: abs(-5) = 5
    #[test]
    fn test_abs_negative() {
        let result = try_elaborate("(= (abs (- 0 5)) 5)");
        assert!(result.is_ok(), "abs negative failed: {:?}", result.err());
    }

    /// Test abs on zero
    #[test]
    fn test_abs_zero() {
        let result = try_elaborate("(= (abs 0) 0)");
        assert!(result.is_ok(), "abs zero failed: {:?}", result.err());
    }

    /// Test `to_int` on real: floor(5.0) = 5
    #[test]
    fn test_to_int_real() {
        let result = try_elaborate("(= (to_int 5.0) 5)");
        assert!(result.is_ok(), "to_int real failed: {:?}", result.err());
    }

    /// Test `to_int` on a negative non-integral real: floor(-1/4) = -1
    #[test]
    fn test_to_int_negative_fraction() {
        let result = try_elaborate("(= (to_int (- 1/4)) (- 0 1))");
        assert!(
            result.is_ok(),
            "to_int negative fraction failed: {:?}",
            result.err()
        );
    }

    /// Test `is_int` on real 5.0: true (5.0 is an integer)
    #[test]
    fn test_is_int_real_true() {
        let result = try_elaborate("(= (is_int 5.0) true)");
        assert!(
            result.is_ok(),
            "is_int real true failed: {:?}",
            result.err()
        );
    }

    /// Test `is_int` on real 5.5: false (5.5 is not an integer)
    #[test]
    fn test_is_int_real_false() {
        let result = try_elaborate("(= (is_int 5.5) false)");
        assert!(
            result.is_ok(),
            "is_int real false failed: {:?}",
            result.err()
        );
    }
}
