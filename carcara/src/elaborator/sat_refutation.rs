use super::*;
use crate::external::*;
use std::collections::HashMap;
use std::fs;

fn proof_node_to_command(node: &Rc<ProofNode>) -> ProofCommand {
    match node.as_ref() {
        ProofNode::Assume { id, term, .. } => {
            ProofCommand::Assume { id: id.clone(), term: term.clone() }
        }
        ProofNode::Step(s) => ProofCommand::Step(ProofStep {
            id: s.id.clone(),
            clause: s.clause.clone(),
            rule: s.rule.clone(),
            premises: Vec::new(),
            args: s.args.clone(),
            discharge: Vec::new(),
        }),
        ProofNode::Subproof(s) => proof_node_to_command(&s.last_step),
    }
}

fn build_res_step(
    clause_id: usize,
    res_steps: &HashMap<usize, (Vec<Rc<Term>>, Vec<usize>)>,
    ids: &mut IdHelper,
    clause_id_to_proof: &mut HashMap<usize, Rc<ProofNode>>,
) -> Rc<ProofNode> {
    if let Some(res_step) = &res_steps.get(&clause_id) {
        // DRAT-trim may generate weakening steps
        let rule = if res_step.1.len() == 1 {
            "weakening".to_owned()
        } else {
            "resolution".to_owned()
        };
        let premises: Vec<Rc<ProofNode>> = res_step
            .1
            .iter()
            .map(|i| {
                if let Some(pf) = clause_id_to_proof.get(i) {
                    pf.clone()
                } else {
                    let pf = build_res_step(*i, res_steps, ids, clause_id_to_proof);
                    clause_id_to_proof.insert(*i, pf.clone());
                    pf.clone()
                }
            })
            .collect();
        Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth: 0,
            clause: res_step.0.clone(),
            rule,
            premises,
            ..Default::default()
        }))
    } else {
        log::error!("Could not find id {} in res_steps", clause_id);
        unreachable!();
    }
}

fn get_resolution_refutation(
    pool: &mut PrimitivePool,
    step: &StepNode,
    premise_to_proof: &HashMap<Rc<Term>, Rc<ProofNode>>,
    cnf_path: String,
    term_to_var: &HashMap<&Rc<Term>, i32>,
) -> Rc<ProofNode> {
    let var_to_term: HashMap<i32, &Rc<Term>> = term_to_var.iter().map(|(k, v)| (*v, *k)).collect();
    let mut id = 0;
    let mut ids = IdHelper::new(&step.id);
    // First we will parse the CNF that we got an LRAT proof for from DRAT-trim when getting the
    // core lemmas, so that we can have the IDs in the clauses of the CNF mapped to the proofs
    // coming from the original step's premises. Note that we must use the LRAT from DRAT-trim so
    // that we start from the same core.
    let mut clause_id_to_proof: HashMap<usize, Rc<ProofNode>> = fs::read_to_string(cnf_path)
        .unwrap()
        .lines()
        .skip(1)
        .filter_map(|l| {
            id += 1;
            let sat_clause_lits: Vec<Rc<Term>> = String::from(l)
                .split(" ")
                .filter_map(|lit| match lit.parse::<i32>() {
                    Ok(lit) if lit != 0 => {
                        let (pol, var) = get_pol_var(lit);
                        let term = var_to_term[&var].clone();
                        Some(if pol {
                            term
                        } else {
                            build_term!(pool, (not { term }))
                        })
                    }
                    _ => None,
                })
                .collect();
            // We *must* find a proof for this clause in `premise_to_proof`. The
            // one detail are the singleton clauses that we may have
            // introduced. Also, the lemmas will be clauses in the SAT proof but
            // OR nodes. So we must search for both.
            match &sat_clause_lits[..] {
                [term] => {
                    let cl = pool.add(Term::Op(Operator::RareList, vec![term.clone()]));
                    Some((id, premise_to_proof[&cl].clone()))
                }
                _ => {
                    let cl = pool.add(Term::Op(Operator::RareList, sat_clause_lits.clone()));
                    if let Some(pf) = premise_to_proof.get(&cl) {
                        Some((id, pf.clone()))
                    } else {
                        // we will try to find a proof then for (rare-list (or ...)), and we will
                        // need to add an OR step between that premise and the resolution proof. If
                        // we do not find it, it means this is a lemma that does not show up in the
                        // core
                        let or = pool.add(Term::Op(Operator::Or, sat_clause_lits.clone()));
                        let or_cl = pool.add(Term::Op(Operator::RareList, vec![or.clone()]));
                        premise_to_proof.get(&or_cl).map(|pf| {
                            (
                                id,
                                Rc::new(ProofNode::Step(StepNode {
                                    id: ids.next_id(),
                                    depth: 0,
                                    clause: sat_clause_lits.clone(),
                                    rule: "or".to_owned(),
                                    premises: vec![pf.clone()],
                                    ..Default::default()
                                })),
                            )
                        })
                    }
                }
            }
        })
        .collect();
    // We traverse the LRAT proof in reverse. Since it is comming from DRAT-trim, all clauses must
    // be useful, which should be guaranteed by the construction downstream of the proof for the
    // empty clause.
    let mut empty_clause_id = 0;
    let res_steps: HashMap<usize, (Vec<Rc<Term>>, Vec<usize>)> = fs::read_to_string("proof.lrat")
        .unwrap()
        .lines()
        .rev()
        .filter_map(|l| {
            let string = String::from(l);
            let strings: Vec<&str> = string.split(" ").collect();
            let id = strings[0].parse::<usize>().unwrap();
            // ignore deletion
            if strings[1] == "d" {
                return None;
            }
            let mut i = 1;
            let mut sat_clause_lits: Vec<Rc<Term>> = Vec::new();
            // parse clause
            loop {
                let sat_lit = strings[i].parse::<i32>().unwrap();
                if sat_lit == 0 {
                    break;
                }
                let (pol, var) = get_pol_var(sat_lit);
                let term = var_to_term[&var].clone();
                let lit = if pol {
                    term
                } else {
                    build_term!(pool, (not { term }))
                };
                sat_clause_lits.push(lit);
                i += 1;
            }
            if sat_clause_lits.is_empty() {
                empty_clause_id = id;
                sat_clause_lits.push(pool.bool_false());
            }
            // parse premises
            let premises: Vec<usize> = strings
                .iter()
                .skip(i)
                .filter_map(|premise| match premise.parse::<usize>() {
                    Ok(premise) if premise != 0 => Some(premise),
                    _ => None,
                })
                .collect();
            Some((id, (sat_clause_lits, premises)))
        })
        .collect();

    log::info!(
        "[sat_refutation elab] Collected {} resolutions from DRAT-trim's LRAT",
        res_steps.len()
    );

    build_res_step(
        empty_clause_id,
        &res_steps,
        &mut ids,
        &mut clause_id_to_proof,
    )
}

pub fn sat_refutation(elaborator: &mut Elaborator, step: &StepNode) -> Option<Rc<ProofNode>> {
    // Get commands out of step children. See proof_node_to_list
    let mut commands: Vec<ProofCommand> = Vec::new();

    step.premises.iter().for_each(|premise| {
        commands.push(proof_node_to_command(premise));
    });
    let command_refs = commands.iter().collect();
    log::info!("[sat_refutation elab] Start elaboration");

    let mut lemmas_to_th_ids: HashMap<Rc<Term>, String> = HashMap::new();
    let mut lemmas_to_step_ids: HashMap<Rc<Term>, String> = HashMap::new();
    let mut clause_id_to_lemma: HashMap<usize, Rc<Term>> = HashMap::new();
    let mut choice_terms: HashSet<Rc<Term>> = HashSet::new();
    let premise_clauses = collect_premise_clauses(
        elaborator.pool,
        &command_refs,
        &mut lemmas_to_th_ids,
        &mut lemmas_to_step_ids,
        &mut clause_id_to_lemma,
        &mut choice_terms,
    );

    let mut sat_clause_to_lemma: HashMap<Vec<i32>, Rc<Term>> = HashMap::new();
    let mut term_to_var: HashMap<&Rc<Term>, i32> = HashMap::new();
    let cnf_path = gen_dimacs(
        &premise_clauses,
        &clause_id_to_lemma,
        &mut sat_clause_to_lemma,
        &mut term_to_var,
        false,
    );
    let tools = elaborator.config.sat_ref_tools.as_ref().unwrap();

    if let Ok(core_lemmas) = get_core_lemmas(
        cnf_path.as_str(),
        &sat_clause_to_lemma,
        &tools.sat_solver,
        &tools.drat_checker,
    ) {
        log::info!(
            "[sat_refutation elab] Get proofs for {} core lemmas",
            core_lemmas.len()
        );
        let mut step_id_to_lemma_proof: HashMap<String, Option<Rc<ProofNode>>> = lemmas_to_step_ids
            .values()
            .map(|id| (id.clone(), None))
            .collect();

        // for each core lemma, we will run cvc5, parse the proof in, and check it
        for (i, li) in core_lemmas.iter().enumerate() {
            let asserts: Vec<_> = li
                .iter()
                .map(|l| build_term!(elaborator.pool, (not {l.clone()})))
                .collect();
            let problem = get_problem_string(
                elaborator.pool,
                &elaborator.problem.prelude.clone(),
                &asserts,
            );
            log::debug!("\tGet proof for lemma {}", i);

            let solver_proof_commands =
                match get_solver_proof(elaborator.pool, problem.clone(), &tools.smt_solver) {
                    Ok((c, _)) => c,
                    Err(e) => {
                        log::warn!("\t\tfailed to elaborate theory lemma {:?}: {}", li, e);
                        return None;
                    }
                };
            let lemma = elaborator
                .pool
                .add(Term::Op(Operator::RareList, li.clone()));
            let step_id = &lemmas_to_step_ids[&lemma];
            let proof_node =
                insert_solver_proof(elaborator.pool, solver_proof_commands, li, step_id, 0);
            step_id_to_lemma_proof.insert(step_id.clone(), Some(proof_node));
        }
        // map premise clauses to their proof nodes, already replacing the theory lemma hole by the found proof
        let premise_to_proof: HashMap<Rc<Term>, Rc<ProofNode>> = step
            .premises
            .iter()
            .filter_map(|premise| {
                let id = premise.id();
                if !step_id_to_lemma_proof.contains_key(id) {
                    // println!("Storing proof for {}", elaborator
                    //         .pool
                    //         .add(Term::Op(Operator::RareList, premise.clause().to_vec())));
                    Some((
                        elaborator
                            .pool
                            .add(Term::Op(Operator::RareList, premise.clause().to_vec())),
                        premise.clone(),
                    ))
                } else if let Some(proof) = &step_id_to_lemma_proof[id] {
                    // println!("Storing proof for {}", elaborator
                    //         .pool
                    //         .add(Term::Op(Operator::RareList, proof.clause().to_vec())));
                    Some((
                        elaborator
                            .pool
                            .add(Term::Op(Operator::RareList, proof.clause().to_vec())),
                        proof.clone(),
                    ))
                } else {
                    None
                }
            })
            .collect();
        log::info!("[sat_refutation elab] Elaborate propositional proof");
        let pf = get_resolution_refutation(
            elaborator.pool,
            step,
            &premise_to_proof,
            cnf_path,
            &term_to_var,
        );
        log::info!("[sat_refutation elab] Finished elaboration.");
        Some(pf)
    } else {
        None
    }
}
