use carcara::{
    ast::{Proof, ProofNodeForest, printer::DisplayOptions},
    elaborator, parser,
};

struct TestCase {
    problem: &'static str,
    proof: &'static str,
    expected: &'static str,
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
        let (problem, proof, _, mut pool) =
            parser::parse_instance(case.problem.into(), case.proof.into(), None, parser_config)
                .unwrap();

        let mut elab = elaborator::Elaborator::new(&mut pool, &problem, config.clone());
        let elaborated = elab
            .elaborate(
                ProofNodeForest::from_commands(proof.commands.clone()),
                &proof.filename,
                pipeline.clone(),
            )
            .expect("elaboration error")
            .into_commands();

        let (_, expected, _) = parser::parse_instance_with_pool(
            case.problem.into(),
            case.expected.into(),
            None,
            parser_config,
            &mut pool,
        )
        .unwrap();

        if expected.commands != elaborated {
            println!("Test '{}' case {} failed, got proof:", name, i);
            let proof = Proof {
                constant_definitions: Vec::new(),
                commands: elaborated,
                filename: "dummy".into(),
            };
            let options = DisplayOptions::new().use_sharing(false);
            println!("{}", proof.display(options));
            result = false
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
