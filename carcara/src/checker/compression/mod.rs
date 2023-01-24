use crate::{ast::*};
use std::collections::{HashMap, hash_map::Entry};
use ahash::{AHashMap, AHashSet};
use std::collections::VecDeque;
use crate::checker::rules::resolution::{binary_resolution};
use crate::checker::rules::Premise;
use super::RuleResult;


// Set the node as visited and if it was visited for the second time, push it onto the the unit_nodes
fn visit(idx: usize, visited: &mut HashMap<usize, i32>, unit_nodes: &mut Vec<usize>) -> (){
    if !visited.contains_key(&idx) {
        visited.insert(idx, 0);
    }
    else if visited[&idx] == 0 {
        unit_nodes.push(idx);
        *visited.get_mut(&idx).unwrap() = 1;
    }
}

// Perform a DFS through the prrof and get all unit nodes
fn collect_units(proof : &Proof) -> Vec<usize> {
    let mut curr = proof.commands.len() - 1;
    let mut queue = VecDeque::new();
    let mut visited = HashMap::new();
    let mut unit_nodes = Vec::new();
    queue.push_back(curr);

    // Bottom up dfs to go through the proof
    while queue.len() > 0 {
        curr = queue[0];
        queue.pop_front();

        match &proof.commands[curr] {
            ProofCommand::Step(step) => {
                // If the command has premises, add them to the queue
                for i in 0..step.premises.len(){
                    queue.push_front(step.premises[i].1);
                }

                // If it is a unit clause, then visit it
                if step.clause.len() == 1{
                    visit(curr, &mut visited, &mut unit_nodes);
                }
            }
            ProofCommand::Assume {id: _, term} => {
                match &**term {
                    // If it is a terminal, it is a unit clause
                    Term::Terminal(_) => {
                        visit(curr, &mut visited, &mut unit_nodes);
                    }
                    Term::Op(_operator, terms) => {
                        // Only visit it if it is a unit clause
                        if terms.len() == 1{
                            visit(curr, &mut visited, &mut unit_nodes);
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    return unit_nodes;
}

// Get the node that replaced i (the answer can be i itself) using path compression
fn find(i: usize, actual: &mut[usize]) -> usize {
    if actual[i] == i {
        return i;
    }
    actual[i] = find(actual[i], actual);
    return actual[i];
}

// Find out which nodes were replaced and by who
fn fix_proof(curr: usize, proof: &Proof, unit_nodes: &[usize], dnm: &[bool], actual : &mut[usize]){
    if dnm[curr] {
        return;
    }

    match &proof.commands[curr] {
        ProofCommand::Step(step) => {
            //if the command has premises, process them
            for i in 0..step.premises.len(){
                fix_proof(step.premises[i].1, proof, unit_nodes, dnm, actual);
            }

            //if some parent is a dnm, it must be replaced by other parent
            let mut dnm_parents = Vec::new();
            for i in 0..step.premises.len(){
                let parent = step.premises[i].1;
                if dnm[parent] {
                    dnm_parents.push(parent);
                }
            }

            // have to replace the current node for its non deleted parent
            if dnm_parents.len() > 0 {
                for i in 0..step.premises.len(){
                    let parent = step.premises[i].1;
                    if !dnm[parent] {
                        actual[curr] = find(parent, actual);
                    }
                }
            }
        }
        _ => {}
    }
}


fn fix_proof_2(proof: &Proof, _actual : &mut[usize], pool : &mut TermPool){

    let mut current = Vec::new();

    match &proof.commands[4] {
        ProofCommand::Step(step_q) => {
            println!("o step 4 é {:?}", step_q);
            
            for i in 0..step_q.clause.len(){
                current.push(step_q.clause[i].remove_all_negations());
            }

            match &proof.commands[6] {
                ProofCommand::Step(step_s) => {
                    println!("o step 6 é {:?}", step_s);
                    let mut next = step_s.clause[1].remove_all_negations();
                    next.0 = 0 as u32;
                    println!("Antes eh {:?} \t {:?} \t {:?}", current, &step_s.clause, next);
                    binary_resolution(pool, &mut current, &step_s.clause, next, true);
                    println!("Depois eh {:?} \t {:?} \t {:?}", current, &step_s.clause, next);
                }
                _ => {}
            }
        }
        ProofCommand::Assume {id: _, term: _} => {
            println!("É um Assume");
        }
        _ => {}
    }
}


// Given the premises and conclusion of a resolution rule, find out which were the pivots used
fn get_pivots<'a>(
    conclusion: &'a [Rc<Term>],
    premises: &'a [Premise],
    pool: &'a mut TermPool,
) -> AHashMap<(i32, &'a Rc<Term>), bool> {
    // In some cases, this rule is used with a single premise `(not true)` to justify an empty
    // conclusion clause
    if conclusion.is_empty() && premises.len() == 1 {
        println!("Caiu no primeiro if");
        if let [t] = premises[0].clause {
            if match_term!((not true) = t).is_some() {
                return AHashMap::new();
            }
        }
    }

    // When checking this rule, we must look at what the conclusion clause looks like in order to
    // determine the pivots. The reason for that is because there is no other way to know which
    // terms should be removed in a given binary resolution step. Consider the following example,
    // adapted from an actual generated proof:
    //
    //     (step t1 (cl (not q) (not (not p)) (not p)) :rule irrelevant)
    //     (step t2 (cl (not (not (not p))) p) :rule irrelevant)
    //     (step t3 (cl (not q) p (not p)) :rule resolution :premises (t1 t2))
    //
    // Without looking at the conclusion, it is unclear if the (not p) term should be removed by the
    // p term, or if the (not (not p)) should be removed by the (not (not (not p))). We can only
    // determine this by looking at the conlcusion and using it to derive the pivots.
    let conclusion: AHashSet<_> = conclusion
        .iter()
        .map(Rc::remove_all_negations)
        .map(|(n, t)| (n as i32, t))
        .collect();

    // The working clause contains the terms from the conclusion clause that we already encountered
    let mut working_clause = AHashSet::new();

    // The pivots are the encountered terms that are not present in the conclusion clause, and so
    // should be removed. After being used to eliminate a term, a pivot can still be used to
    // eliminate other terms. Because of that, we represent the pivots as a hash map to a boolean,
    // which represents if the pivot was already eliminated or not. At the end, this boolean should
    // be true for all pivots
    let mut pivots = AHashMap::new();

    for premise in premises {
        // Only one pivot may be eliminated per clause. This restriction is required so logically
        // unsound proofs like this one are not considered valid:
        //
        //     (step t1 (cl (= false true) (not false) (not true)) :rule equiv_neg1)
        //     (step t2 (cl (= false true) false true) :rule equiv_neg2)
        //     (step t3 (cl (= false true)) :rule resolution :premises (t1 t2))
        let mut eliminated_clause_pivot = false;
        for term in premise.clause {
            let (n, inner) = term.remove_all_negations();
            let n = n as i32;

            // There are two possible negations of a term, with one leading negation added, or with
            // one leading negation removed (if the term had any in the first place)
            let below = (n - 1, inner);
            let above = (n + 1, inner);

            // First, if the encountered term should be in the conclusion, but is not yet in the
            // working clause, we insert it and don't try to remove it with a pivot
            if conclusion.contains(&(n, inner)) && !working_clause.contains(&(n, inner)) {
                working_clause.insert((n, inner));
                continue;
            }

            // If the negation of the encountered term is present in the pivots set, we simply
            // eliminate it. Otherwise, we insert the encountered term in the working clause or the
            // pivots set, depending on wether it is present in the conclusion clause or not
            let mut try_eliminate = |pivot| match pivots.entry(pivot) {
                Entry::Occupied(mut e) => {
                    e.insert(true);
                    true
                }
                Entry::Vacant(_) => false,
            };

            // Only one pivot may be elminated per clause, so if we already found this clauses'
            // pivot, we don't try to eliminate the term
            let eliminated =
                !eliminated_clause_pivot && (try_eliminate(below) || try_eliminate(above));

            if eliminated {
                eliminated_clause_pivot = true;
            } else if conclusion.contains(&(n, inner)) {
                working_clause.insert((n, inner));
            } else {
                // If the term is not in the conclusion clause, it must be a pivot. If it was
                // not already in the pivots set, we insert `false`, to indicate that it was
                // not yet eliminated
                pivots.entry((n, inner)).or_insert(false);
            }
        }
    }
    pivots
}

// Compress the proof using the Lower Units algorithm
pub fn compress_proof(proof: &Proof, pool : &mut TermPool){
    let unit_nodes = collect_units(&proof);
    
    let mut dnm = Vec::new();
    dnm.resize(proof.commands.len(), false);
    for i in &unit_nodes{
        dnm[*i] = true;
    }
    let curr = proof.commands.len() - 1;
    let mut actual = Vec::new();
    for i in 0..dnm.len(){
        actual.push(i as usize);
    }

    fix_proof(curr, proof, &unit_nodes, &dnm, &mut actual);

    for i in 0..actual.len() {
        println!("{:?} agora é {:?}", i, find(i, &mut actual));
    }

    fix_proof_2(proof, &mut actual, pool);
    
    // Como encontrar o pivo que foi usado numa aplicação de resolution
    // let pr = [Premise::new((0, 11), &proof.commands[11]), Premise::new((0, 9), &proof.commands[9])];
    // let tam = proof.commands.len();
    // match &proof.commands[tam-1] {
    //     ProofCommand::Step(step_s) => {
    //         println!("{:?}", get_pivots(&step_s.clause, &pr, pool));
    //     }
    //     _ => {}
    // }

    // Como criar uma nova prova
    // As premissas eu posso colocar assim
    // println!("{:?}", proof.premises);
    // let mut new_premises = AHashSet::new();
    // for i in &proof.premises{
    //     println!("{:?}", i);
    //     new_premises.insert(Rc::clone(i));
    // }

    // Os comandos podem ser assim
    // let mut new_commands = Vec::new();
    // let mut command = ProofCommand::Step(ProofStep{ id       : String::from("t10"),
    //                                                 clause   : Vec::from(proof.commands[10].clause()),
    //                                                 rule     : String::from("resolution"),
    //                                                 premises : vec![(0, 5), (0, 9)],
    //                                                 args     : vec![],
    //                                                 discharge: vec![]});
    // new_commands.push(command);

    // E a prova fica assim
    // let new_proof = Proof{premises : new_premises, commands : new_commands};
}