use super::*;
use crate::{checker::error::LiaGenericError, parser};
use ahash::AHashMap;
use std::{
    io::{BufRead, Write},
    process::{Command, Stdio},
};

fn get_problem_string(conclusion: &[Rc<Term>], prelude: &ProblemPrelude) -> String {
    use std::fmt::Write;

    let mut problem = String::new();
    write!(&mut problem, "(set-option :produce-proofs true)").unwrap();
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
    pool: &mut TermPool,
    conclusion: &[Rc<Term>],
    prelude: &ProblemPrelude,
    elaborator: Option<&mut Elaborator>,
    root_id: &str,
) -> bool {
    let problem = get_problem_string(conclusion, prelude);
    let commands = match get_cvc5_proof(pool, problem) {
        Ok(c) => c,
        Err(e) => {
            log::warn!("failed to check `lia_generic` step using cvc5: {}", e);
            if let Some(elaborator) = elaborator {
                elaborator.unchanged(conclusion);
            }
            return true;
        }
    };

    if let Some(elaborator) = elaborator {
        insert_cvc5_proof(pool, elaborator, commands, conclusion, root_id);
    }
    false
}

fn get_cvc5_proof(
    pool: &mut TermPool,
    problem: String,
) -> Result<Vec<ProofCommand>, LiaGenericError> {
    let mut cvc5 = Command::new("cvc5")
        .args([
            "--tlimit=10000",
            "--lang=smt2",
            "--proof-format-mode=alethe",
            "--proof-granularity=theory-rewrite",
        ])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
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
        if let Ok(s) = std::str::from_utf8(&output.stderr) {
            if s.contains("cvc5 interrupted by timeout.") {
                return Err(LiaGenericError::Cvc5Timeout);
            }
        }
        return Err(LiaGenericError::Cvc5NonZeroExitCode(output.status.code()));
    }

    let mut proof = output.stdout.as_slice();
    let mut first_line = String::new();

    proof
        .read_line(&mut first_line)
        .map_err(|_| LiaGenericError::Cvc5GaveInvalidOutput)?;

    if first_line.trim_end() != "unsat" {
        return Err(LiaGenericError::Cvc5OutputNotUnsat);
    }

    parse_and_check_cvc5_proof(pool, problem.as_bytes(), proof)
        .map_err(|e| LiaGenericError::InnerProofError(Box::new(e)))
}

fn parse_and_check_cvc5_proof(
    pool: &mut TermPool,
    problem: &[u8],
    proof: &[u8],
) -> AletheResult<Vec<ProofCommand>> {
    let mut parser = parser::Parser::new(pool, problem, true, true)?;
    let (prelude, premises) = parser.parse_problem()?;
    parser.reset(proof)?;
    let commands = parser.parse_proof()?;
    let proof = Proof { premises, commands };

    let config = Config {
        strict: false,
        skip_unknown_rules: false,
        is_running_test: false,
        statistics: None,
        check_lia_generic_using_cvc5: false,
    };
    ProofChecker::new(pool, config, prelude).check(&proof)?;
    Ok(proof.commands)
}

fn update_premises(
    commands: &mut [ProofCommand],
    depth_delta: usize,
    index_delta: usize,
    root_id: &str,
) {
    for c in commands {
        match c {
            ProofCommand::Assume { id, .. } => {
                *id = format!("{}.{}", root_id, id);
            }
            ProofCommand::Step(s) => {
                s.id = format!("{}.{}", root_id, s.id);
                for p in &mut s.premises {
                    p.0 += depth_delta;
                    p.1 += index_delta;
                }
            }
            ProofCommand::Subproof(s) => {
                update_premises(&mut s.commands, depth_delta, 0, root_id);
            }
        }
    }
}

fn insert_missing_assumes(
    pool: &mut TermPool,
    elaborator: &mut Elaborator,
    conclusion: &[Rc<Term>],
    proof: &[ProofCommand],
    root_id: &str,
) -> (Vec<Rc<Term>>, usize) {
    let mut count_map: AHashMap<&Rc<Term>, usize> = AHashMap::new();
    for c in conclusion {
        *count_map.entry(c).or_default() += 1;
    }

    let proof_premises: Vec<_> = proof
        .iter()
        .filter_map(|c| {
            if let ProofCommand::Assume { term, .. } = c {
                Some(term.remove_negation().unwrap().clone())
            } else {
                None
            }
        })
        .collect();
    for p in &proof_premises {
        *count_map.get_mut(p).unwrap() -= 1;
    }

    let mut all = Vec::new();
    for (t, mut count) in count_map {
        while count > 0 {
            let id = elaborator.get_new_id(root_id);
            all.push(t.clone());
            let term = build_term!(pool, (not {t.clone()}));
            elaborator.add_new_command(ProofCommand::Assume { id, term }, true);
            count -= 1;
        }
    }
    let num_added = all.len();
    all.extend(proof_premises);
    (all, num_added)
}

fn insert_cvc5_proof(
    pool: &mut TermPool,
    elaborator: &mut Elaborator,
    mut commands: Vec<ProofCommand>,
    conclusion: &[Rc<Term>],
    root_id: &str,
) {
    let subproof_id = elaborator.get_new_id(root_id);
    elaborator.open_accumulator_subproof();

    let (all_premises, num_added) = insert_missing_assumes(
        pool,
        elaborator,
        conclusion,
        &commands,
        // This is a bit ugly, but we have to add the ".added" to avoid colliding with the first few
        // steps in the cvc5 proof
        &format!("{}.added", root_id),
    );

    let (mut clause, discharge): (Vec<_>, Vec<_>) = all_premises
        .iter()
        .enumerate()
        .map(|(i, t)| {
            let term = build_term!(pool, (not (not {t.clone()})));
            (term, (1usize, i))
        })
        .unzip();
    clause.push(pool.bool_false());

    update_premises(&mut commands, 1, num_added, &subproof_id);
    for c in commands {
        elaborator.add_new_command(c, true);
    }

    let subproof = elaborator.close_accumulator_subproof(
        Vec::new(),
        Vec::new(),
        ProofStep {
            id: subproof_id,
            clause: clause.clone(),
            rule: "subproof".to_owned(),
            premises: Vec::new(),
            args: Vec::new(),
            discharge,
        },
        root_id,
    );

    let not_not_steps: Vec<_> = clause[..clause.len() - 1]
        .iter()
        .map(|term| {
            let clause = vec![
                build_term!(pool, (not {term.clone()})),
                term.remove_negation()
                    .unwrap()
                    .remove_negation()
                    .unwrap()
                    .clone(),
            ];
            let id = elaborator.get_new_id(root_id);
            elaborator.add_new_step(ProofStep {
                id,
                clause,
                rule: "not_not".to_owned(),
                premises: Vec::new(),
                args: Vec::new(),
                discharge: Vec::new(),
            })
        })
        .collect();
    let id = elaborator.get_new_id(root_id);
    let false_step = elaborator.add_new_step(ProofStep {
        id,
        clause: vec![build_term!(pool, (not {pool.bool_false()}))],
        rule: "false".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
        discharge: Vec::new(),
    });

    let mut premises = vec![subproof];
    premises.extend(not_not_steps);
    premises.push(false_step);

    let id = elaborator.get_new_id(root_id);
    elaborator.push_elaborated_step(ProofStep {
        id,
        clause: conclusion.to_vec(),
        rule: "resolution".to_owned(),
        premises,
        args: Vec::new(),
        discharge: Vec::new(),
    });
}
