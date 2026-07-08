use super::*;
use crate::{
    ast::*,
    checker,
    elaborator::{IdHelper, Mutate},
    parser, CarcaraResult,
};
use std::{
    borrow::ToOwned,
    collections::{HashMap, HashSet},
    convert::Infallible,
    fmt, fs,
    io::{BufRead, Write},
    process::{Command, Output, Stdio},
    str::FromStr,
};
use thiserror::Error;

#[derive(Debug, Clone)]
pub struct SatTools {
    pub sat_solver: ExternalTool,
    pub drat_checker: ExternalTool,
    pub smt_solver: ExternalTool,
}

#[derive(Debug, Clone)]
pub struct ExternalTool {
    pub command: String,
    pub args: Vec<String>,
}

impl fmt::Display for ExternalTool {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.command)?;
        for a in &self.args {
            write!(f, " {}", a)?;
        }
        Ok(())
    }
}

impl FromStr for ExternalTool {
    type Err = Infallible;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::new(s))
    }
}

impl ExternalTool {
    pub fn new(s: &str) -> Self {
        let mut iter = s.split_whitespace();
        let command = iter.next().unwrap().to_owned();
        let args = iter.map(ToOwned::to_owned).collect();
        Self { command, args }
    }

    pub fn call(&self, stdin: &[u8]) -> Result<Output, ExternalError> {
        self.call_with_extra_args([], stdin)
    }

    pub fn call_with_extra_args<'a>(
        &'a self,
        extra_args: impl IntoIterator<Item = &'a str>,
        stdin: &[u8],
    ) -> Result<Output, ExternalError> {
        let mut process = Command::new(&self.command)
            .args(self.args.iter().map(String::as_str).chain(extra_args))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(ExternalError::FailedSpawn)?;

        if !stdin.is_empty() {
            process
                .stdin
                .take()
                .expect("failed to open solver stdin")
                .write_all(stdin)
                .map_err(ExternalError::FailedWriteToStdin)?;
        }

        process
            .wait_with_output()
            .map_err(ExternalError::FailedWait)
    }
}

#[derive(Debug, Error)]
pub enum ExternalError {
    #[error("failed to spawn external tool process")]
    FailedSpawn(io::Error),

    #[error("failed to open external tool stdin")]
    FailedOpenStdin(io::Error),

    #[error("failed to write to external tool stdin")]
    FailedWriteToStdin(io::Error),

    #[error("error while waiting for external tool to exit")]
    FailedWait(io::Error),

    #[error("external tool gave invalid output")]
    InvalidOutput,

    #[error("external tool output not unsat")]
    OutputNotUnsat,

    #[error("external tool timed out")]
    Timeout,

    #[error("error in inner proof: {0}")]
    InnerProofError(Box<crate::Error>),

    #[error("proof returned by external tool is holey")]
    InnerProofHoley,

    #[error("couldn't check lemma: '{0}'")]
    LemmaNotChecked(Rc<Term>),
}

pub fn get_problem_string<'a, I: IntoIterator<Item = &'a Rc<Term>>>(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    assertions: I,
) -> String {
    use std::fmt::Write;

    let mut problem = String::new();
    writeln!(&mut problem, "(set-option :produce-proofs true)").unwrap();
    write!(&mut problem, "{}", prelude).unwrap();

    let mut bytes = Vec::new();
    printer::write_asserts(pool, prelude, &mut bytes, assertions, false).unwrap();
    write!(&mut problem, "{}", String::from_utf8(bytes).unwrap()).unwrap();
    writeln!(&mut problem, "(check-sat)").unwrap();
    writeln!(&mut problem, "(get-proof)").unwrap();
    writeln!(&mut problem, "(exit)").unwrap();

    problem
}

pub fn parse_and_check_solver_proof(
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
    let config = checker::Config::new().ignore_unknown_rules(true);
    let res = checker::ProofChecker::new(pool, &rules, config).check(&problem, &proof)?;
    Ok((proof.commands, res))
}

pub fn get_solver_proof(
    pool: &mut PrimitivePool,
    problem: String,
    solver: &ExternalTool,
) -> Result<(Vec<ProofCommand>, bool), ExternalError> {
    let output = solver.call(problem.as_bytes())?;
    if !output.status.success() {
        if let Ok(s) = std::str::from_utf8(&output.stderr) {
            if s.contains("interrupted by timeout.") {
                return Err(ExternalError::Timeout);
            }
        }
        return Err(ExternalError::InvalidOutput);
    }

    let mut proof = output.stdout.as_slice();
    let mut first_line = String::new();

    proof
        .read_line(&mut first_line)
        .map_err(|_| ExternalError::InvalidOutput)?;

    if first_line.trim_end() != "unsat" {
        return Err(ExternalError::OutputNotUnsat);
    }

    let proof = str::from_utf8(proof).map_err(|_| ExternalError::InvalidOutput)?;
    parse_and_check_solver_proof(pool, &problem, proof)
        .map_err(|e| ExternalError::InnerProofError(Box::new(e)))
}

/// Given an integer returns a pair with the polarity (true if no leading minus) and the absolute value
pub fn get_pol_var(lit: i32) -> (bool, i32) {
    if lit < 0 {
        (false, lit.abs())
    } else {
        (true, lit)
    }
}

pub fn gen_dimacs<'a>(
    premise_clauses: &'a [Vec<Rc<Term>>],
    clause_id_to_lemma: &HashMap<usize, Rc<Term>>,
    sat_clause_to_lemma: &mut HashMap<Vec<i32>, Rc<Term>>,
    term_to_var: &mut HashMap<&'a Rc<Term>, i32>,
    mark_lemmas: bool,
) -> String {
    use std::fmt::Write;

    let mut clauses: String = "".to_owned();
    let mut max_var = 0;
    let mut lemma_id = 0;

    for i in 0..premise_clauses.len() {
        let is_lemma = clause_id_to_lemma.contains_key(&i);
        if mark_lemmas && is_lemma {
            clauses += &format!("@l{} ", lemma_id).to_owned();
            lemma_id += 1;
        }
        let mut clause_lits = Vec::new();
        premise_clauses[i].iter().for_each(|lit| {
            let (pol, term) = lit.remove_all_negations_with_polarity();
            if !term_to_var.contains_key(term) {
                term_to_var.insert(term, max_var + 1);
                max_var += 1;
            }
            clause_lits.push(if !pol {
                -term_to_var[term]
            } else {
                term_to_var[term]
            });
            clauses += &format!("{} ", clause_lits[clause_lits.len() - 1]).to_owned();
        });
        if is_lemma {
            clause_lits.sort();
            sat_clause_to_lemma.insert(clause_lits.clone(), clause_id_to_lemma[&i].clone());
        }
        writeln!(&mut clauses, "0").unwrap();
    }
    let mut dimacs = String::new();
    writeln!(&mut dimacs, "p cnf {} {}", max_var, premise_clauses.len()).unwrap();
    write!(&mut dimacs, "{}", clauses).unwrap();
    let cnf_path = "proof.cnf".to_owned();
    log::info!("[sat_refutation check] Print CNF {}", cnf_path);
    write!(fs::File::create(cnf_path.clone()).unwrap(), "{}", dimacs).unwrap();

    cnf_path
}

pub fn collect_premise_clauses(
    pool: &mut PrimitivePool,
    premise_steps: &Vec<&ProofCommand>,
    lemmas_to_th_ids: &mut HashMap<Rc<Term>, String>,
    lemmas_to_step_ids: &mut HashMap<Rc<Term>, String>,
    clause_id_to_lemma: &mut HashMap<usize, Rc<Term>>,
    choice_terms: &mut HashSet<Rc<Term>>,
) -> Vec<Vec<Rc<Term>>> {
    let mut premise_clauses: Vec<Vec<_>> = Vec::new();
    let mut _or_lits: Vec<Rc<Term>> = Vec::new();
    premise_steps.iter().for_each(|p| {
        match p {
            ProofCommand::Step(step) => {
                // holes are assumed to be theory lemmas, where if they
                // are OR nodes then they are non-unit, otherwise
                // unities. If they are not singleton clauses, we add the
                // whole clause as a clause
                if step.rule == "hole" {
                    let th_id = if step.args.len() == 2
                        && step.args[0].as_string().unwrap() == "THEORY_LEMMA"
                    {
                        step.args[1].as_string().unwrap()
                    } else {
                        "none".to_owned()
                    };
                    let lemma_opt = match &step.clause[..] {
                        [term] => match term.as_ref() {
                            Term::Op(Operator::Or, or_args) => {
                                let lemma = pool.add(Term::Op(Operator::RareList, or_args.clone()));
                                if !lemmas_to_step_ids.contains_key(&lemma) {
                                    lemmas_to_step_ids.insert(lemma.clone(), step.id.clone());
                                    lemmas_to_th_ids.insert(lemma.clone(), th_id);
                                    premise_clauses.push(or_args.clone());
                                    Some(lemma)
                                } else {
                                    None
                                }
                            }
                            _ => {
                                let lemma =
                                    pool.add(Term::Op(Operator::RareList, vec![term.clone()]));
                                if !lemmas_to_step_ids.contains_key(&lemma) {
                                    lemmas_to_step_ids.insert(lemma.clone(), step.id.clone());
                                    lemmas_to_th_ids.insert(lemma.clone(), th_id);
                                    premise_clauses.push(vec![term.clone()]);
                                    Some(lemma)
                                } else {
                                    None
                                }
                            }
                        },
                        _ => {
                            let lemma = pool.add(Term::Op(Operator::RareList, step.clause.clone()));
                            if !lemmas_to_step_ids.contains_key(&lemma) {
                                lemmas_to_step_ids.insert(lemma.clone(), step.id.clone());
                                lemmas_to_th_ids.insert(lemma.clone(), th_id);
                                premise_clauses.push(step.clause.clone());
                                Some(lemma)
                            } else {
                                None
                            }
                        }
                    };
                    if let Some(lemma_opt) = lemma_opt {
                        clause_id_to_lemma.insert(premise_clauses.len() - 1, lemma_opt.clone());
                    }
                } else {
                    match &step.clause[..] {
                        // singletons are always added as unities and as clauses, if OR nodes
                        [term] => {
                            if let Term::Op(Operator::Or, or_args) = term.as_ref() {
                                // add as a non-singleton clause
                                premise_clauses.push(or_args.clone());
                            }
                            premise_clauses.push(vec![term.clone()]);
                        }
                        _ => {
                            premise_clauses.push(step.clause.clone());
                        }
                    }
                }
            }
            ProofCommand::Subproof(_) => {}
            ProofCommand::Assume { term, .. } => {
                // if OR, collect as clause, but also always generate as
                // literal
                if let Term::Op(Operator::Or, or_args) = term.as_ref() {
                    premise_clauses.push(or_args.clone());
                }
                premise_clauses.push(vec![term.clone()]);
            }
        }
    });
    premise_clauses.iter().for_each(|c| {
        c.iter().for_each(|l| {
            let choices_l = pool.collect_binders(l, Binder::Choice);
            choices_l.iter().for_each(|l_cs| {
                choice_terms.insert(l_cs.clone());
            });
        });
    });
    log::debug!(
        "\t[collecting premises] Collected choices {:?}",
        choice_terms
    );
    premise_clauses
}

pub fn get_core_lemmas(
    cnf_path: &str,
    sat_clause_to_lemma: &HashMap<Vec<i32>, Rc<Term>>,
    cadical: &ExternalTool,
    drat_trim: &ExternalTool,
) -> Result<Vec<Vec<Rc<Term>>>, ExternalError> {
    // not gonna pass input via stdin because in that case
    // CaDiCaL gets confused with receiving the name of the
    // proof file as an argument. If we could get the proof in
    // stdout then there would be no need to write a CNF file nor a DRAT file
    let output = cadical.call_with_extra_args([cnf_path, "proof.drat", "--no-binary"], &[])?;

    log::info!("[get_core_lemmas] Checking CNF {} with CaDiCaL", cnf_path);

    // CaDiCaL's exit code when successful is 10/20 (for
    // sat/unsat), so this will not lead to a successful
    // output according to Rust. So the test here directly
    // checks stdout to see if the problem is found unsat.
    if let Ok(stdout) = std::str::from_utf8(&output.stdout) {
        if !stdout.contains("s UNSATISFIABLE") {
            return Err(ExternalError::OutputNotUnsat);
        }
    } else {
        return Err(ExternalError::InvalidOutput);
    }
    // pass cnf + proof to drat-trim
    let drat_trim_output = drat_trim.call_with_extra_args(
        [
            cnf_path,
            "proof.drat",
            "-c",
            "proof.core",
            "-L",
            "proof.lrat",
        ],
        &[],
    )?;

    if !drat_trim_output.status.success() {
        return Err(ExternalError::OutputNotUnsat);
    }

    let mut core_lemmas: Vec<Vec<Rc<Term>>> = Vec::new();
    fs::read_to_string("proof.core")
        .unwrap() // panic on possible file-reading errors
        .lines() // split the string into an iterator of string slices
        .skip(1)
        .for_each(|l| {
            let mut sat_clause_lits: Vec<i32> = String::from(l)
                .split(" ")
                .filter_map(|lit| match lit.parse::<i32>() {
                    Ok(lit) if lit != 0 => Some(lit),
                    _ => None,
                })
                .collect();
            sat_clause_lits.sort();
            if let Some(lemma) = sat_clause_to_lemma.get(&sat_clause_lits) {
                if let Some((Operator::RareList, lemma_lits)) = lemma.as_op() {
                    core_lemmas.push(lemma_lits.to_vec().clone());
                }
            }
        });
    log::info!("[get_core_lemmas] {} lemmas in core", core_lemmas.len());
    Ok(core_lemmas)
}

fn increase_subproof_depth(proof: Rc<ProofNode>, delta: usize, prefix: &str) -> Rc<ProofNode> {
    let Ok(node) = proof.mutate(
        // I'd rather use the never type (!) than `Infallible`, but it's still unstable
        |_, node, _| -> Result<Rc<ProofNode>, std::convert::Infallible> {
            let node = match node.as_ref().clone() {
                ProofNode::Assume { id, depth, term } => ProofNode::Assume {
                    id: format!("{}.{}", prefix, id),
                    depth: depth + delta,
                    term,
                },
                ProofNode::Step(mut s) => {
                    s.id = format!("{}.{}", prefix, s.id);
                    s.depth += delta;
                    ProofNode::Step(s)
                }
                ProofNode::Subproof(_) => unreachable!(),
            };
            Ok(Rc::new(node))
        },
    );
    node
}

pub fn insert_solver_proof(
    pool: &mut PrimitivePool,
    commands: Vec<ProofCommand>,
    conclusion: &[Rc<Term>],
    root_id: &str,
    depth: usize,
) -> Rc<ProofNode> {
    let proof = ProofNodeForest::from_commands(commands)
        .0
        .into_iter()
        .find(|node| node.clause().is_empty())
        .expect("solver proof does not conclude empty clause");

    let mut ids = IdHelper::new(root_id);
    let subproof_id = ids.next_id();

    let mut clause: Vec<_> = conclusion
        .iter()
        .map(|l| build_term!(pool, (not (not {l.clone()}))))
        .collect();

    clause.push(pool.bool_false());

    let proof = increase_subproof_depth(proof, depth + 1, &subproof_id);
    let term_to_subproof_assumption: HashMap<Rc<Term>, Rc<ProofNode>> = proof
        .get_assumptions_of_depth(depth + 1)
        .iter()
        .map(|p| {
            if let Some((_, _, term)) = p.as_assume() {
                (term.clone(), p.clone())
            } else {
                unreachable!();
            }
        })
        .collect();

    let last_assumption_id_prefix = format!("{}.a", subproof_id);

    // We use the length of the clause to guarantee this id will not clash with
    // the id of some existing assumption. It does not suffice to get the number
    // of assumptions in `term_to_subproof_assumption` as a baseline because we
    // may have fewer assumptions there than the total number of literals in
    // clause however some of them may be with a higher index (e.g. 3
    // assumptions there, but one of them has id "...a5").
    let mut next_assumption_id = clause.len() + 1;

    // we have to make sure the assumptions are given in the right order as the conclusion
    let discharge = (0..clause.len() - 1)
        .map(|i| {
            let Some(t) = match_term!((not t) = &clause[i]) else {
                unreachable!()
            };

            if let Some(a) = term_to_subproof_assumption.get(t) {
                return a.clone();
            }

            // No assumption from the subproof matches this term directly. We will check if this
            // term could have matched modulo polyeq with any of the assumptions. Only if that fails
            // we create a new assumption
            let mut assumption_opt: Option<Rc<ProofNode>> = None;
            term_to_subproof_assumption.iter().for_each(|(assume, pf)| {
                // TODO: is this actually doing anything if mod_reordering is false?
                if Polyeq::new().mod_reordering(false).eq(t, assume) {
                    assumption_opt = Some(pf.clone());
                }
            });
            if let Some(assumption_opt) = assumption_opt {
                return assumption_opt;
            }
            // this marks the case in which the assumption corresponding to this literal
            // was not necessary for deriving unsat, i.e., the validity of the initial
            // clause does not depend on it. Regardless, to produce the necessary clause
            // as conclusion, so the whole proof is properly connected, we must generate an
            // assumption for this literal
            let assumption = Rc::new(ProofNode::Assume {
                id: format!("{}{}", last_assumption_id_prefix, next_assumption_id),
                depth: depth + 1,
                term: t.clone(),
            });
            next_assumption_id += 1;
            assumption
        })
        .collect();

    let last_step = Rc::new(ProofNode::Step(StepNode {
        id: subproof_id,
        depth: depth + 1,
        clause: clause.clone(),
        rule: "subproof".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
        discharge,
        previous_step: Some(proof),
    }));

    let subproof = Rc::new(ProofNode::Subproof(SubproofNode {
        last_step,
        args: Vec::new(),
        // Since the subproof was inserted from the solver proof, it cannot reference anything
        // outside of it.
        outbound_premises: Vec::new(),
        extra_steps: Vec::new(),
    }));

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
            Rc::new(ProofNode::Step(StepNode {
                id: ids.next_id(),
                depth,
                clause,
                rule: "not_not".to_owned(),
                ..Default::default()
            }))
        })
        .collect();

    let false_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth,
        clause: vec![build_term!(pool, (not {pool.bool_false()}))],
        rule: "false".to_owned(),
        ..Default::default()
    }));

    let mut premises = vec![subproof];
    premises.extend(not_not_steps);
    premises.push(false_step);

    Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth,
        clause: conclusion.to_vec(),
        rule: "resolution".to_owned(),
        premises,
        ..Default::default()
    }))
}
