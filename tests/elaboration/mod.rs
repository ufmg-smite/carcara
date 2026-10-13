use carcara::{
    ast::{
        Problem, Proof, ProofCommand, ProofNodeForest, ProofStep, pool::Pool,
        printer::DisplayOptions, rare_rules::Rules,
    },
    checker, elaborator, parser,
};

struct TestCase {
    problem: &'static str,
    proof: &'static str,
    expected: &'static str,
}

fn check_proof(
    pool: &mut Pool,
    problem: &Problem,
    commands: &[ProofCommand],
    elaborated: bool,
) -> Result<(), carcara::Error> {
    // Since the tests often use `assume` commands to introduce premises, we add all `assume`d terms
    // to the problem premises
    let mut problem = problem.clone();
    problem
        .premises
        .extend(commands.iter().filter_map(|c| match c {
            ProofCommand::Assume { term, .. } => Some(term.clone()),
            _ => None,
        }));

    // All proofs must eventually reach the empty clause, so we add a dummy step to conclude it
    let mut commands = commands.to_vec();
    commands.push(ProofCommand::Step(ProofStep {
        id: "end".into(),
        clause: Vec::new(),
        rule: "hole".into(),
        premises: Vec::new(),
        args: Vec::new(),
        discharge: Vec::new(),
    }));
    let proof = Proof {
        constant_definitions: Vec::new(),
        commands,
        filename: "<test-proof>".into(),
    };

    let rules = Rules { rules: Default::default() };
    let config = checker::Config::new().elaborated(elaborated);
    checker::Checker::new(pool, &rules, config)
        .check(&problem, &proof)
        .map(|_| ())
}

fn run_tests(
    config: elaborator::Config,
    pipeline: Vec<elaborator::ElaborationPass>,
    name: &str,
    cases: &[TestCase],
) -> bool {
    let mut result = true;
    let parser_config = parser::Config::new().apply_function_defs(true);
    for (i, case) in cases.iter().enumerate() {
        let (problem, proof, _, mut pool) = parser::parse(
            carcara::Input {
                problem: case.problem.into(),
                proof: case.proof.into(),
                rare_rules: None,
            },
            parser_config,
        )
        .unwrap();

        // The input proof must be valid, otherwise the test is exercising an unreachable path
        if let Err(e) = check_proof(&mut pool, &problem, &proof.commands, false) {
            println!(
                "Test '{}' case {} failed, input proof is invalid: {}",
                name, i, e
            );
            result = false;
            continue;
        }

        let mut elab = elaborator::Elaborator::new(&mut pool, &problem, config.clone());
        let elaborated = elab
            .elaborate(
                ProofNodeForest::from_commands(proof.commands.clone()),
                &proof.filename,
                pipeline.clone(),
            )
            .expect("elaboration error")
            .into_commands();

        let (_, expected, _) = parser::parse_with_pool(
            carcara::Input {
                problem: case.problem.into(),
                proof: case.expected.into(),
                rare_rules: None,
            },
            parser_config,
            &mut pool,
        )
        .unwrap();

        if expected.commands != elaborated {
            println!("Test '{}' case {} failed, got proof:", name, i);
            let proof = Proof {
                constant_definitions: Vec::new(),
                commands: elaborated.clone(),
                filename: "dummy".into(),
            };
            let options = DisplayOptions::new().use_sharing(false);
            println!("{}", proof.display(options));
            result = false
        }

        // The elaborated proof must be valid, with elaborated granularity
        if let Err(e) = check_proof(&mut pool, &problem, &elaborated, true) {
            println!(
                "Test '{}' case {} failed, elaborated proof is invalid: {}",
                name, i, e
            );
            result = false;
        }
    }
    result
}

macro_rules! test_cases {
    (
        pipeline = $($step:ident)*,
        $(uncrowd_rotate = $uncrowd_rotate:literal,)?
        problem = $problem:literal,
        $($name:literal { $($proof:literal -> $expected:literal,)* } )*
    ) => {{
        let pipeline = vec![ $(carcara::elaborator::ElaborationPass::$step,)* ];
        let config = carcara::elaborator::Config::new().uncrowd_rotation(
            $($uncrowd_rotate ||)? false
        );
        let mut success = true;
        $({
            let cases = [ $(
                $crate::elaboration::TestCase {
                    problem: $problem,
                    proof: $proof,
                    expected: $expected,
                },
            )* ];
            let got =
                $crate::elaboration::run_tests(config.clone(), pipeline.clone(), $name, &cases);
            success = success && got;
        })*
        if !success {
            panic!()
        }
    }};
}

mod congruence;
mod eq_mp;
mod polyeq;
mod reordering;
mod resolution;
mod transitivity;
mod uncrowding;
