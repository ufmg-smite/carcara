use super::*;
use crate::{checker::error::LiaGenericError, parser};
use std::{
    io::{BufRead, Write},
    process::{Command, Stdio},
};

fn get_problem_string(conclusion: &[Rc<Term>], prelude: &ProblemPrelude) -> String {
    use std::fmt::Write;

    let mut problem = String::new();
    write!(&mut problem, "{}", prelude).unwrap();

    let mut bytes = Vec::new();
    printer::write_lia_smt_instance(&mut bytes, conclusion).unwrap();
    write!(&mut problem, "{}", String::from_utf8(bytes).unwrap()).unwrap();

    writeln!(&mut problem, "(check-sat)").unwrap();
    writeln!(&mut problem, "(get-proof)").unwrap();
    writeln!(&mut problem, "(exit)").unwrap();

    problem
}

pub fn lia_generic(
    conclusion: &[Rc<Term>],
    prelude: &ProblemPrelude,
) -> Result<(), LiaGenericError> {
    let problem = get_problem_string(conclusion, prelude);

    let mut cvc5 = Command::new("cvc5")
        .args([
            "--tlimit=10000",
            "--produce-proofs",
            "--proof-format-mode=alethe",
            "--proof-granularity=theory-rewrite",
        ])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(LiaGenericError::FailedSpawnCvc5)?;

    cvc5.stdin
        .take()
        .expect("failed to open cvc5 stdin")
        .write_all(problem.as_bytes())
        .map_err(LiaGenericError::FailedWriteToCvc5Stdin)?;

    let output = cvc5
        .wait_with_output()
        .map_err(LiaGenericError::FailedWaitForCvc5)?;

    if !output.status.success() {
        let code = output.status.code();
        return if code == Some(134) {
            Err(LiaGenericError::Cvc5Timeout)
        } else {
            Err(LiaGenericError::Cvc5NonZeroExitCode(code))
        };
    }

    let mut proof = output.stdout.as_slice();
    let mut first_line = String::new();

    proof
        .read_line(&mut first_line)
        .map_err(|_| LiaGenericError::Cvc5GaveInvalidOutput)?;

    if first_line.trim_end() != "unsat" {
        return Err(LiaGenericError::Cvc5OutputNotUnsat);
    }

    let (prelude, proof, mut pool) = parser::parse_instance(problem.as_bytes(), proof, false)
        .map_err(|e| LiaGenericError::InnerProofError(Box::new(e)))?;

    let config = Config {
        skip_unknown_rules: false,
        is_running_test: false,
        statistics: None,
        check_lia_generic_using_cvc5: false,
    };
    ProofChecker::new(&mut pool, config, prelude)
        .check(&proof)
        .map_err(|e| LiaGenericError::InnerProofError(Box::new(e)))?;

    Ok(())
}
