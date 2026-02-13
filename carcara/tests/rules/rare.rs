use carcara::{ast::ProofCommand, checker, parser};
use std::io::Cursor;

// Custom rare rules for testing
const RARE_RULES: &str = r#"
; Equality symmetry rule - rewrites (= x y) to (= y x)
(declare-rare-rule eq-symm (
    (x Bool)
    (y Bool)
)
    :args (x y)
    :premises ()
    :conclusion (= (= x y) (= y x)))

; Double negation elimination
(declare-rare-rule double-neg-elim (
    (x Bool)
)
    :args (x)
    :premises ()
    :conclusion (= (not (not x)) x))

; Boolean simplification: or with true
(declare-rare-rule or-true-simp (
    (x Bool)
)
    :args (x)
    :premises ()
    :conclusion (= (or x true) true))

; Boolean simplification: and with false
(declare-rare-rule and-false-simp (
    (x Bool)
)
    :args (x)
    :premises ()
    :conclusion (= (and x false) false))

; Implication expansion
(declare-rare-rule implies-expand (
    (x Bool)
    (y Bool)
)
    :args (x y)
    :premises ()
    :conclusion (= (=> x y) (or (not x) y)))
"#;

const SMALL_RARE_RULES: &str = r#"
(declare-rare-rule bv-concat-extract-merge ((xs1 (_ BitVec 1) :list) (s1 (_ BitVec 8)) (ys1 (_ BitVec 1) :list))
  :premises ((= 2 (+ 1 1)))
  :args (xs1 s1 ys1)
  :conclusion (= (concat xs1 ((_ extract 7 2) s1) ((_ extract 1 1) s1) ys1) (concat xs1 ((_ extract 7 1) s1) ys1))
)

(declare-rare-rule bool-and-de-morgan ((x1 Bool) (y1 Bool))
  :args (x1 y1)
  :conclusion (= (not (and x1 y1)) (or (not x1) (not y1)))
)
"#;

const BV_CONCAT_EXTRACT_MERGE_SMT2: &str = r#"
; EXPECT: unsat
(set-logic ALL)

(declare-fun x () (_ BitVec 8))

(assert
  (and
    (= 2 (+ 1 1))
    (not
      (=
        (concat ((_ extract 0 0) x) ((_ extract 7 2) x) ((_ extract 1 1) x) ((_ extract 0 0) x))
        (concat ((_ extract 0 0) x) ((_ extract 7 1) x) ((_ extract 0 0) x))))))

(check-sat)
"#;

const BV_CONCAT_EXTRACT_MERGE_ALETHE: &str = r#"
(assume a0
  (and
    (= 2 (+ 1 1))
    (not
      (=
        (concat ((_ extract 0 0) x) ((_ extract 7 2) x) ((_ extract 1 1) x) ((_ extract 0 0) x))
        (concat ((_ extract 0 0) x) ((_ extract 7 1) x) ((_ extract 0 0) x))))))

(step t0 (cl (= 2 (+ 1 1)))
  :rule and
  :premises (a0)
  :args (0))

(step t1 (cl (not (=
                    (concat ((_ extract 0 0) x) ((_ extract 7 2) x) ((_ extract 1 1) x) ((_ extract 0 0) x))
                    (concat ((_ extract 0 0) x) ((_ extract 7 1) x) ((_ extract 0 0) x)))))
  :rule and
  :premises (a0)
  :args (1))

(step t2 (cl (=
              (concat ((_ extract 0 0) x) ((_ extract 7 2) x) ((_ extract 1 1) x) ((_ extract 0 0) x))
              (concat ((_ extract 0 0) x) ((_ extract 7 1) x) ((_ extract 0 0) x))))
  :rule rare_rewrite
  :premises (t0)
  :args ("bv-concat-extract-merge" ((_ extract 0 0) x) x ((_ extract 0 0) x)))

(step t3 (cl)
  :rule resolution
  :premises (t2 t1))
"#;

const DD_CHECK_CC_BVXOR_XSIMP_SMT2: &str = r#"
; EXPECT: unsat
(set-logic ALL)
(declare-const _x (_ BitVec 1))
(declare-const s (_ BitVec 64))
(declare-const t (_ BitVec 64))
(assert (distinct (= (bvxor s t) (bvand (bvxor s t) ((_ zero_extend 63) _x))) (exists ((x (_ BitVec 64))) (and (= t (bvxor x s)) (= x (bvand x ((_ zero_extend 63) _x)))))))
(check-sat)
"#;

const DD_CHECK_CC_BVXOR_XSIMP_ALETHE: &str = r#"
(anchor :step t38 :args ((x (_ BitVec 64)) (:= (x (_ BitVec 64)) x)))
(step t38.t0 (cl (= (not (and (= t (bvxor s x)) (= x (concat (_ bv0 63) (bvand _x ((_ extract 0 0) x)))))) (or (not (= t (bvxor s x))) (not (= x (concat (_ bv0 63) (bvand _x ((_ extract 0 0) x)))))))) :rule rare_rewrite :args ("bool-and-de-morgan" (= t (bvxor s x)) (= x (concat (_ bv0 63) (bvand _x ((_ extract 0 0) x))))))
(step t38 (cl (= (forall ((x (_ BitVec 64))) (not (and (= t (bvxor s x)) (= x (concat (_ bv0 63) (bvand _x ((_ extract 0 0) x))))))) (forall ((x (_ BitVec 64))) (or (not (= t (bvxor s x))) (not (= x (concat (_ bv0 63) (bvand _x ((_ extract 0 0) x))))))))) :rule bind)
(step t73 (cl) :rule hole)
"#;

fn run_rare_tests(test_name: &str, definitions: &str, cases: &[(&str, bool)]) {
    for (i, (proof, expected)) in cases.iter().enumerate() {
        let (mut problem, mut proof, rare_rules, mut pool) = parser::parse_instance(
            Cursor::new(definitions),
            Cursor::new(proof),
            Some(Cursor::new(RARE_RULES)),
            parser::Config {
                apply_function_defs: true,
                ..Default::default()
            },
        )
        .unwrap_or_else(|e| panic!("parser error during test \"{}\": {}", test_name, e));

        // Add all assumed terms as problem premises
        problem.premises = proof
            .commands
            .iter()
            .filter_map(|c| match c {
                ProofCommand::Assume { term, .. } => Some(term.clone()),
                _ => None,
            })
            .collect();

        // Add dummy end step
        use carcara::ast::ProofStep;
        proof.commands.push(ProofCommand::Step(ProofStep {
            id: "end".into(),
            clause: Vec::new(),
            rule: "hole".into(),
            premises: Vec::new(),
            args: Vec::new(),
            discharge: Vec::new(),
        }));

        let mut checker =
            checker::ProofChecker::new(&mut pool, &rare_rules, checker::Config::new());
        let check_result = checker.check(&problem, &proof);

        let error_message = match &check_result {
            Ok(_) => String::new(),
            Err(e) => format!("{}", e),
        };

        let got = check_result.is_ok();

        if *expected != got {
            use colored::{Color, Colorize};
            let (color, expectation) = if *expected {
                (Color::Red, "expected to PASS but FAILED".red())
            } else {
                (Color::Yellow, "expected to FAIL but PASSED".yellow())
            };

            panic!(
                "{}\nTest '{}' case {}: {}\nOUTCOME: {}",
                "TEST FAILURE".bold().color(color),
                test_name.bold(),
                i.to_string().bold(),
                expectation,
                error_message
            );
        }
    }
}

fn run_rare_file_test(
    test_name: &str,
    problem: &str,
    proof: &str,
    rare_rules: &str,
    expected_holey: bool,
) {
    let (problem, proof, rare_rules, mut pool) = parser::parse_instance(
        Cursor::new(problem),
        Cursor::new(proof),
        Some(Cursor::new(rare_rules)),
        parser::Config {
            apply_function_defs: true,
            expand_lets: true,
            allow_int_real_subtyping: true,
            parse_hole_args: true,
            ..Default::default()
        },
    )
    .unwrap_or_else(|e| panic!("parser error during test \"{}\": {}", test_name, e));

    let mut checker = checker::ProofChecker::new(&mut pool, &rare_rules, checker::Config::new());
    let check_result = checker.check(&problem, &proof);

    match check_result {
        Ok(is_holey) => assert_eq!(
            is_holey, expected_holey,
            "test '{}' expected holey={} but got holey={}",
            test_name, expected_holey, is_holey
        ),
        Err(e) => panic!("checker error during test \"{}\": {}", test_name, e),
    }
}

macro_rules! rare_test_cases {
    (
        definitions = $defs:expr,
        $($name:literal { $($proof:literal: $exp:literal,)* } )*
    ) => {{
        let definitions: &str = $defs;
        $({
            let name: &str = $name;
            let cases = [ $(($proof, $exp),)* ];
            run_rare_tests(name, definitions, &cases);
        })*
    }};
}

#[test]
fn rare_rewrite() {
    rare_test_cases! {
        definitions = "
            (declare-const p Bool)
            (declare-const q Bool)
            (declare-const r Bool)
        ",
        "Equality symmetry" {
            "(step t1 (cl (= (= p q) (= q p))) :rule rare_rewrite :args (\"eq-symm\" p q))": true,

            "(step t1 (cl (= (= p q) (= p q))) :rule rare_rewrite :args (\"eq-symm\" p q))": false,

            "(step t1 (cl (= (= r q) (= q r))) :rule rare_rewrite :args (\"eq-symm\" r q))": true,
        }

        "Double negation elimination" {
            "(step t1 (cl (= (not (not p)) p)) :rule rare_rewrite :args (\"double-neg-elim\" p))": true,

            "(step t1 (cl (= (not (not p)) q)) :rule rare_rewrite :args (\"double-neg-elim\" p))": false,

            "(step t1 (cl (= (not (not q)) q)) :rule rare_rewrite :args (\"double-neg-elim\" q))": true,
        }

        "Boolean simplifications" {
            "(step t1 (cl (= (or p true) true)) :rule rare_rewrite :args (\"or-true-simp\" p))": true,

            "(step t1 (cl (= (or q true) true)) :rule rare_rewrite :args (\"or-true-simp\" q))": true,

            "(step t1 (cl (= (and p false) false)) :rule rare_rewrite :args (\"and-false-simp\" p))": true,

            "(step t1 (cl (= (or p true) false)) :rule rare_rewrite :args (\"or-true-simp\" p))": false,
        }

        "Implication expansion" {
            "(step t1 (cl (= (=> p q) (or (not p) q))) :rule rare_rewrite :args (\"implies-expand\" p q))": true,

            "(step t1 (cl (= (=> r q) (or (not r) q))) :rule rare_rewrite :args (\"implies-expand\" r q))": true,

            "(step t1 (cl (= (=> p q) (or p q))) :rule rare_rewrite :args (\"implies-expand\" p q))": false,
        }
    }
}

#[test]
fn encoded_rare_examples() {
    run_rare_file_test(
        "bv-concat-extract-merge",
        BV_CONCAT_EXTRACT_MERGE_SMT2,
        BV_CONCAT_EXTRACT_MERGE_ALETHE,
        SMALL_RARE_RULES,
        false,
    );

    run_rare_file_test(
        "dd_check_cc_bvxor_xsimp",
        DD_CHECK_CC_BVXOR_XSIMP_SMT2,
        DD_CHECK_CC_BVXOR_XSIMP_ALETHE,
        SMALL_RARE_RULES,
        true,
    );
}
