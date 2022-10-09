use super::*;
use crate::parser;
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

// TODO: Add proper error handling
pub fn lia_generic(conclusion: &[Rc<Term>], prelude: &ProblemPrelude) -> RuleResult {
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
        .expect("failed to spawn cvc5");

    cvc5.stdin
        .take()
        .expect("failed to open cvc5 stdin")
        .write_all(problem.as_bytes())
        .expect("failed to write to cvc5 stdin");

    let output = cvc5
        .wait_with_output()
        .map_err(|_| CheckerError::Unspecified)?;

    let mut proof = output.stdout.as_slice();
    let mut first_line = String::new();

    proof
        .read_line(&mut first_line)
        .expect("failed to read cvc5 output");

    assert!(&first_line[..5] == "unsat", "cvc5 output not unsat");

    let (prelude, proof, mut pool) = parser::parse_instance(problem.as_bytes(), proof, false)
        .expect("parsing inner proof failed");

    let config = Config {
        skip_unknown_rules: false,
        is_running_test: false,
        statistics: None,
        check_lia_generic_using_cvc5: false,
    };
    ProofChecker::new(&mut pool, config, prelude)
        .check(&proof)
        .expect("checking inner proof failed");

    Ok(())
}
