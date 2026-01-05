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
