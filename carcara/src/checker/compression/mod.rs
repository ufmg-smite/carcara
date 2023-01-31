use crate::{ast::*};
use std::collections::{HashMap, hash_map::Entry};
use ahash::{AHashMap, AHashSet};
use std::collections::VecDeque;
use crate::checker::rules::resolution::{binary_resolution, unremove_all_negations};
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


// Given the premises and conclusion of a resolution rule, find out which were the pivots used
fn get_pivots<'a>(
    conclusion: &'a [Rc<Term>],
    premises: &'a [Premise],
    pool: &'a mut TermPool,
) -> (&'a mut TermPool, (u32, &'a Rc<Term>)) {
    if conclusion.is_empty() && premises.len() == 1 {
        println!("Caiu no primeiro if");
        if let [t] = premises[0].clause {
            if match_term!((not true) = t).is_some() {
                panic!("Cannot determine the pivots");
            }
        }
    }

    let conclusion: AHashSet<_> = conclusion
        .iter()
        .map(Rc::remove_all_negations)
        .map(|(n, t)| (n as i32, t))
        .collect();
    let mut working_clause = AHashSet::new();
    let mut pivots = AHashMap::new();

    for premise in premises {
        let mut eliminated_clause_pivot = false;
        for term in premise.clause {
            let (n, inner) = term.remove_all_negations();
            let n = n as i32;

            let below = (n - 1, inner);
            let above = (n + 1, inner);

            if conclusion.contains(&(n, inner)) && !working_clause.contains(&(n, inner)) {
                working_clause.insert((n, inner));
                continue;
            }

            let mut try_eliminate = |pivot| match pivots.entry(pivot) {
                Entry::Occupied(mut e) => {
                    e.insert(true);
                    true
                }
                Entry::Vacant(_) => false,
            };

            let eliminated =
                !eliminated_clause_pivot && (try_eliminate(below) || try_eliminate(above));

            if eliminated {
                eliminated_clause_pivot = true;
            } else if conclusion.contains(&(n, inner)) {
                working_clause.insert((n, inner));
            } else {
                pivots.entry((n, inner)).or_insert(false);
            }
        }
    }

    println!("Pivots are {:?}", pivots);

    for i in pivots{
        if i.1{
            return (pool, (i.0.0 as u32, i.0.1));
        }
    }
    panic!("Cannot determine the pivots");
}

fn binary_resolution_from_old(
    pool : &mut TermPool,
    left_parent : usize,
    right_parent : usize,
    new_commands : Vec<ProofCommand>,
    curr_step : &ProofStep,
) -> Vec<Rc<Term>>{
//){
    let mut current = Vec::new();
    match &new_commands[left_parent] {
        ProofCommand::Step(step_l) => {
            println!("o step_l é {:?}", step_l);

            for i in 0..step_l.clause.len(){
                current.push(step_l.clause[i].remove_all_negations());
            }

            match &new_commands[right_parent] {
                ProofCommand::Step(step_r) => {
                    println!("o step_r é {:?}", step_r);

                    let premises = [Premise::new((0 as usize, left_parent), &new_commands[left_parent]),
                                    Premise::new((0 as usize, right_parent),&new_commands[right_parent])];

                    let (pool, mut pivot) = get_pivots(&curr_step.clause, &premises, pool);
                    pivot.0 = 0;
                    println!("I got {:?} as pivot", pivot);

                    let mut is_pivot_in_current = true;
                    for i in 0..current.len(){
                        if pivot.1 == current[i].1 && current[i].0 % 2 == 1{
                            is_pivot_in_current = false;
                        }
                    }
                    
                    println!("Parameters were {:?} {:?} {:?}", current, step_r.clause, pivot);
                    binary_resolution(pool, &mut current, &step_r.clause, pivot, is_pivot_in_current);
                    println!("Parameters  are {:?} {:?} {:?}", current, step_r.clause, pivot);
                    let mut new_clause = Vec::new();
                    for i in 0..(current.len() / 2){
                        new_clause.push(unremove_all_negations(pool, current[i]));
                    }
                    println!("New clause {:?}", new_clause);
                    return new_clause;
                    
                }
                _ => {}
            }
        }
        ProofCommand::Assume {id: _, term: _} => {
            println!("É um Assume");
        }
        _ => {}
    }
    panic!("Was not able to compute the resolution");
}

fn add_node(curr: usize,
            old_proof : &Proof,
            actual : &[usize],
            new_commands :  &mut Vec<ProofCommand>,
            pool : &mut TermPool,
//            added: &mut Vec<Option<usize>>
) -> usize{
    println!("Estou tentando adicionar o {:?}", old_proof.commands[curr]);
    match &old_proof.commands[curr] {
        ProofCommand::Step(step) => {
            println!("Currently in {:?}", step);

            //if the command has premises, process them
            let mut new_premises = Vec::new();
            for i in 0..step.premises.len(){
                new_premises.push((0 as usize, add_node(actual[step.premises[i].1], old_proof, actual, new_commands, pool) - 1));
            }
            
            //agora tem que fazer as cláusulas
            let mut new_clause;
            if step.rule == "resolution"{
                println!("Passo de resolution");
                new_clause = binary_resolution_from_old(pool, new_premises[0].1, new_premises[1].1, new_commands.to_vec(), step);
                //new_clause = Vec::from(old_proof.commands[10].clause());
            }
            else{
                new_clause = Vec::from(old_proof.commands[curr].clause());
            }
            println!("{:?}", new_clause);

            let mut new_id = (new_commands.len() + 1).to_string();
            let mut command = ProofCommand::Step(ProofStep{ id       : String::from("t") + &new_id,
                                                            clause   : new_clause,
                                                            rule     : step.rule.clone(),
                                                            premises : new_premises,
                                                            args     : vec![],
                                                            discharge: vec![]});
            new_commands.push(command);

        }
        ProofCommand::Assume {id, term} => {
            println!("It is not a step, it is {:?} and {:?}", id, term);
            let mut new_id = (new_commands.len() + 1).to_string();
            let mut command = ProofCommand::Assume{id : String::from("h") + &new_id, term : Rc::clone(term)};
            new_commands.push(command);
        }
        _ => {}
    }
    return new_commands.len();
}


fn dummy_resolution(proof: &Proof, _actual : &mut[usize], pool : &mut TermPool){
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
                    println!("next: {:?}", next);
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

    //dummy_resolution(proof, &mut actual, pool);
    let mut new_proof_commands = Vec::new();
    //let mut added: Vec<Option<usize>> = vec![None; proof.commands.len()];
    //println!("Added: {:?}", added);
    add_node(proof.commands.len() - 1, proof, &actual, &mut new_proof_commands, pool);
    
    // Agora eu tenho que adicionar cada um dos unit_nodes e
    // depois fazer a binary resolution deles com o último nó da prova
    for i in unit_nodes{
        //println!("Vai adicionar o {:?}", proof.commands[i]);
        add_node(i, proof, &actual, &mut new_proof_commands, pool);
    }

    println!("\n\nNew proof commands are:");
    for i in new_proof_commands{
        println!("{:?}", i);
    }


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