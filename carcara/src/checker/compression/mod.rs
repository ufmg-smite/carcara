#![allow(unused_must_use)]
#![allow(unused_variables)]

use crate::{ast::*};
use std::collections::{HashMap, hash_map::Entry};
use ahash::{AHashMap, AHashSet};
use std::collections::VecDeque;
use crate::checker::rules::resolution::{binary_resolution, unremove_all_negations};
use crate::checker::rules::Premise;
use crate::ast::printer::print_proof;


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
            // If the command has premises, process them
            for i in 0..step.premises.len(){
                fix_proof(step.premises[i].1, proof, unit_nodes, dnm, actual);
            }

            // If some parent is a dnm, it must be replaced by other parent
            let mut dnm_parents = Vec::new();
            for i in 0..step.premises.len(){
                let parent = step.premises[i].1;
                if dnm[parent] {
                    dnm_parents.push(parent);
                }
            }

            // Have to replace the current node for its non deleted parent
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
    let mut current_vec = Vec::new();
    let mut current = AHashSet::new();
    match &new_commands[left_parent] {
        ProofCommand::Step(step_l) => {
            for i in 0..step_l.clause.len(){
                current_vec.push(step_l.clause[i].remove_all_negations());
                current.insert(step_l.clause[i].remove_all_negations());
            }
        }
        ProofCommand::Assume {id: _, term: term_l} => {
            current_vec.push(term_l.remove_all_negations());
            current.insert(term_l.remove_all_negations());
        }
        _ => {}
    }
    
    let premises = [Premise::new((0 as usize, left_parent), &new_commands[left_parent]),
                    Premise::new((0 as usize, right_parent),&new_commands[right_parent])];

    let (pool, mut pivot) = get_pivots(&curr_step.clause, &premises, pool);
    pivot.0 = 0;

    let mut is_pivot_in_current = true;
    for i in 0..current_vec.len(){
        if pivot.1 == current_vec[i].1 && current_vec[i].0 % 2 == 1{
            is_pivot_in_current = false;
        }
    }

    match &new_commands[right_parent] {
        ProofCommand::Step(step_r) => {
            binary_resolution(pool, &mut current, &step_r.clause, pivot, is_pivot_in_current);
            let mut new_clause = Vec::new();
            for i in current{
                new_clause.push(unremove_all_negations(pool, i))
            }
            return new_clause;
        }
        ProofCommand::Assume {id: _, term: term_r} => {
            let new_clause = [Rc::clone(term_r)];
            binary_resolution(pool, &mut current, &new_clause[..], pivot, is_pivot_in_current);
            let mut new_clause = Vec::new();
            for i in current{
                new_clause.push(unremove_all_negations(pool, i))
            }
            return new_clause;
        }
        _ => {}
    }
    panic!("Was not able to compute the resolution");
}

fn add_node<'a>(curr: usize,
            old_proof : &Proof,
            actual : &[usize],
            new_commands :  &'a mut Vec<ProofCommand>,
            pool : &mut TermPool,
            added: &mut Vec<Option<usize>>
) -> (usize, &'a mut Vec<ProofCommand>){
    match added[curr] {
        Some(idx) => return (idx, new_commands),
        _ => (),
    }

    match &old_proof.commands[curr] {
        ProofCommand::Step(step) => {
            // If the command has premises, process them
            let mut new_premises = Vec::new();
            for i in 0..step.premises.len(){
                let (added, mut _new_commands) = add_node(actual[step.premises[i].1], old_proof, actual, new_commands, pool, added);
                new_premises.push((0 as usize, added));
            }
            
            let new_clause;
            if step.rule == "resolution" || step.rule == "th_resolution"{
                new_clause = binary_resolution_from_old(pool, new_premises[0].1, new_premises[1].1, new_commands.to_vec(), step);
            }
            else{
                new_clause = Vec::from(old_proof.commands[curr].clause());
            }
            
            let new_id = (new_commands.len() + 1).to_string();
            let command = ProofCommand::Step(ProofStep{ id       : String::from("t") + &new_id,
                                                            clause   : new_clause,
                                                            rule     : step.rule.clone(),
                                                            premises : new_premises,
                                                            args     : vec![],
                                                            discharge: vec![]});
            new_commands.push(command);

        }
        ProofCommand::Assume {id: _, term} => {
            let new_id = (new_commands.len() + 1).to_string();
            let command = ProofCommand::Assume{id : String::from("h") + &new_id, term : Rc::clone(term)};
            new_commands.push(command);
        }
        _ => {}
    }

    let idx = new_commands.len() - 1;
    added[curr] = Some(idx);
    return (idx, new_commands);
}


// The right_parent is always a unit_node
fn binary_resolution_with_unit(
    pool : &mut TermPool,
    left_parent : usize,
    right_parent : usize,
    new_commands : Vec<ProofCommand>,
) -> Vec<Rc<Term>>{
    let mut current_vec = Vec::new();
    let mut current = AHashSet::new();
    match &new_commands[left_parent] {
        ProofCommand::Step(step_l) => {
            for i in 0..step_l.clause.len(){
                current.insert(step_l.clause[i].remove_all_negations());
                current_vec.push(step_l.clause[i].remove_all_negations());
            }
        }
        ProofCommand::Assume {id: _, term: term_l} => {
            current.insert(term_l.remove_all_negations());
            current_vec.push(term_l.remove_all_negations());
        }
        _ => {}
    }

    match &new_commands[right_parent] {
        ProofCommand::Step(step_r) => {
            let mut pivot = step_r.clause[0].remove_all_negations();
            pivot.0 = 0;
            let mut is_pivot_in_current = true;
            for i in 0..current_vec.len(){
                if pivot.1 == current_vec[i].1 && current_vec[i].0 > 0{
                    is_pivot_in_current = false;
                }
            }
            binary_resolution(pool, &mut current, &step_r.clause, pivot, is_pivot_in_current);
            let mut new_clause = Vec::new();
            for i in current{
                new_clause.push(unremove_all_negations(pool, i));
            }
            return new_clause;
        }
        ProofCommand::Assume {id: _, term: term_r} => {
            let new_clause = [Rc::clone(term_r)];
            let mut pivot = term_r.remove_all_negations();
            pivot.0 = 0;
            let mut is_pivot_in_current = true;
            for i in 0..current_vec.len(){
                if pivot.1 == current_vec[i].1 && current_vec[i].0 > 0{
                    is_pivot_in_current = false;
                }
            }
            binary_resolution(pool, &mut current, &new_clause[..], pivot, is_pivot_in_current);
            let mut new_clause = Vec::new();
            for i in current{
                new_clause.push(unremove_all_negations(pool, i));
            }
            return new_clause;
        }
        _ => {}
    }

    panic!("Could not match the unit node");
}

// Compress the proof using the Lower Units algorithm
pub fn compress_proof(proof: &Proof, pool : &mut TermPool){
    let unit_nodes = collect_units(&proof);

    if unit_nodes.len() == 0{
        print_proof(&proof.commands, false);
        return;
    }
    
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

    let mut new_proof_commands = Vec::new();
    let mut added: Vec<Option<usize>> = vec![None; proof.commands.len()];
    let (_, mut new_proof_commands) = add_node(proof.commands.len() - 1, proof, &actual, &mut new_proof_commands, pool, &mut added);

    // Agora eu tenho que adicionar cada um dos unit_nodes e
    // depois fazer a binary resolution deles com o último nó da prova
    for i in unit_nodes{
        let previous_last_node = new_proof_commands.len() - 1;
        let (_, new_proof_commands) = add_node(i, proof, &actual, &mut new_proof_commands, pool, &mut added);

        //Aqui eu tenho que fazer o binary resolution com o atual último nó da prova
        let current_last_node = new_proof_commands.len() - 1;
        let new_premises = [(0 as usize, previous_last_node), (0 as usize, current_last_node)];
        let new_clause = binary_resolution_with_unit(pool, previous_last_node, current_last_node, new_proof_commands.to_vec());

        let new_id = (new_proof_commands.len() + 1).to_string();
        let command = ProofCommand::Step(ProofStep{ id       : String::from("t") + &new_id,
                                                        clause   : new_clause,
                                                        rule     : String::from("resolution"),
                                                        premises : new_premises.to_vec(),
                                                        args     : vec![],
                                                        discharge: vec![]});
        new_proof_commands.push(command);
    }

    print_proof(new_proof_commands, false);

}