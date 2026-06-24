use super::*;
use crate::external::insert_solver_proof;
use crate::{checker, parser, CarcaraResult};
use std::{
    io::{self, BufRead, Write},
    process::{Command, Stdio},
};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum HoleError {
    #[error("failed to spawn solver process")]
    FailedSpawnSolver(io::Error),

    #[error("failed to write to solver stdin")]
    FailedWriteToSolverStdin(io::Error),

    #[error("error while waiting for solver to exit")]
    FailedWaitForSolver(io::Error),

    #[error("solver gave invalid output")]
    SolverGaveInvalidOutput,

    #[error("solver output not unsat")]
    OutputNotUnsat,

    #[error("solver timed out when solving problem")]
    SolverTimeout,

    #[error(
        "solver returned non-zero exit code: {}",
        if let Some(i) = .0 { format!("{}", i) } else { "none".to_owned() }
    )]
    NonZeroExitCode(Option<i32>),

    #[error("error in inner proof: {0}")]
    InnerProofError(Box<crate::Error>),

    #[error("proof returned by solver is holey")]
    InnerProofHoley,
}

fn get_problem_string(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    conclusion: &[Rc<Term>],
) -> String {
    use std::fmt::Write;

    let mut problem = String::new();
    writeln!(&mut problem, "(set-option :produce-proofs true)").unwrap();
    write!(&mut problem, "{}", prelude).unwrap();

    let mut bytes = Vec::new();
    printer::write_lia_smt_instance(pool, prelude, &mut bytes, conclusion, false).unwrap();
    write!(&mut problem, "{}", String::from_utf8(bytes).unwrap()).unwrap();

    writeln!(&mut problem, "(check-sat)").unwrap();
    writeln!(&mut problem, "(get-proof)").unwrap();
    writeln!(&mut problem, "(exit)").unwrap();

    problem
}

pub fn hole(
    elaborator: &mut Elaborator,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let prelude = elaborator.problem.prelude.clone();
    let prelude = if prelude.logic.as_deref() == Some("QF_LIA") {
        ProblemPrelude {
            logic: Some("QF_LIRA".into()),
            ..prelude
        }
    } else {
        prelude
    };
    let problem = get_problem_string(elaborator.pool, &prelude, &step.clause);
    let options = elaborator.config.hole_options.as_ref().unwrap();
    let commands =
        get_solver_proof(elaborator.pool, problem.clone(), options).and_then(|(cs, holey)| {
            if holey {
                Err(HoleError::InnerProofHoley)
            } else {
                Ok(cs)
            }
        })?;

    Ok(insert_solver_proof(
        elaborator.pool,
        commands,
        &step.clause,
        &step.id,
        step.depth,
    ))
}

fn get_solver_proof(
    pool: &mut PrimitivePool,
    problem: String,
    options: &HoleOptions,
) -> Result<(Vec<ProofCommand>, bool), HoleError> {
    let mut process = Command::new(options.solver.as_ref())
        .args(options.arguments.iter().map(AsRef::as_ref))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(HoleError::FailedSpawnSolver)?;

    process
        .stdin
        .take()
        .expect("failed to open solver stdin")
        .write_all(problem.as_bytes())
        .map_err(HoleError::FailedWriteToSolverStdin)?;

    let output = process
        .wait_with_output()
        .map_err(HoleError::FailedWaitForSolver)?;

    if !output.status.success() {
        if let Ok(s) = std::str::from_utf8(&output.stderr) {
            if s.contains("interrupted by timeout.") {
                return Err(HoleError::SolverTimeout);
            }
        }
        return Err(HoleError::NonZeroExitCode(output.status.code()));
    }

    let mut proof = output.stdout.as_slice();
    let mut first_line = String::new();

    proof
        .read_line(&mut first_line)
        .map_err(|_| HoleError::SolverGaveInvalidOutput)?;

    if first_line.trim_end() != "unsat" {
        return Err(HoleError::OutputNotUnsat);
    }

    let proof = str::from_utf8(proof).map_err(|_| HoleError::SolverGaveInvalidOutput)?;
    parse_and_check_solver_proof(pool, &problem, proof)
        .map_err(|e| HoleError::InnerProofError(Box::new(e)))
}

fn parse_and_check_solver_proof(
    pool: &mut PrimitivePool,
    problem: &str,
    proof: &str,
) -> CarcaraResult<(Vec<ProofCommand>, bool)> {
    let config = parser::Config {
        apply_function_defs: false,
        expand_lets: true,
        allow_int_real_subtyping: true,
        strict: false,
        parse_hole_args: false,
    };

    let (problem, proof, rules) =
        parser::parse_instance_with_pool(problem, proof, None, config, pool)?;

    let config = checker::Config::new();
    let res = checker::ProofChecker::new(pool, &rules, config).check(&problem, &proof)?;
    Ok((proof.commands, res))
}
