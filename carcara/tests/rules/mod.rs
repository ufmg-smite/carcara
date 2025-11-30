use carcara::{
    ast::{ProofCommand, ProofStep},
    checker, parser,
};
use colored::{Color, Colorize};
use std::io::Cursor;

fn run_tests(test_name: &str, definitions: &str, cases: &[(&str, bool)]) {
    for (i, (proof, expected)) in cases.iter().enumerate() {
        // This parses the definitions again for every case, which is not ideal
        let (mut problem, mut proof, rare_rules, mut pool) = parser::parse_instance(
            Cursor::new(definitions),
            Cursor::new(proof),
            None,
            parser::Config {
                apply_function_defs: true,
                ..Default::default()
            },
        )
        .unwrap_or_else(|e| panic!("parser error during test \"{}\": {}", test_name, e));

        // Since rule tests often use `assume` commands to introduce premises, we search the proof
        // for all `assume`d terms and retroactively add them as the problem premises, to avoid
        // checker errors on the `assume`s
        problem.premises = proof
            .commands
            .iter()
            .filter_map(|c| match c {
                ProofCommand::Assume { term, .. } => Some(term.clone()),
                _ => None,
            })
            .collect();

        // All proofs must eventually reach the empty clause, so to avoid having to add a dummy
        // `(step end (cl) :rule hole)` to every rule test, we add this dummy step here
        proof.commands.push(ProofCommand::Step(ProofStep {
            id: "end".into(),
            clause: Vec::new(),
            rule: "hole".into(),
            premises: Vec::new(),
            args: Vec::new(),
            discharge: Vec::new(),
        }));

        let mut checker = checker::ProofChecker::new(&mut pool, &rare_rules, checker::Config::new());
        let check_result = checker.check(&problem, &proof);

        // Extract error message, if any
        let error_message = match &check_result {
            Ok(_) => String::new(),
            Err(e) => format!("{}", e),
        };

        let got = check_result.is_ok();

        if *expected == got {
            println!("{} \"{}\"", "PASSED".bold().color(Color::Green), test_name);
        } else {
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

macro_rules! test_cases {
    (
        definitions = $defs:expr,
        $($name:literal { $($proof:literal: $exp:literal,)* } )*
    ) => {{
        let definitions: &str = $defs;
        $({
            let name: &str = $name;
            let cases = [ $(($proof, $exp),)* ];
            $crate::rules::run_tests(name, definitions, &cases);
        })*
    }};
}

pub(super) mod bitvectors;
pub(super) mod clausification;
pub(super) mod congruence;
pub(super) mod cutting_planes;
pub(super) mod drup;
pub(super) mod extras;
pub(super) mod linear_arithmetic;
pub(super) mod pb_blasting;
pub(super) mod quantifier;
pub(super) mod rare;
pub(super) mod reflexivity;
pub(super) mod resolution;
pub(super) mod simplification;
pub(super) mod strings;
pub(super) mod subproof;
pub(super) mod tautology;
pub(super) mod transitivity;
