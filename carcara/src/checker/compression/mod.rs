#![allow(unused_must_use)]
#![allow(unused_variables)]

use crate::{ast::*};
use std::collections::{HashMap, hash_map::Entry};
use ahash::{AHashMap, AHashSet};
use std::collections::VecDeque;
use crate::checker::rules::resolution::{binary_resolution, unremove_all_negations};
use crate::checker::rules::Premise;
use crate::ast::printer::print_proof;


// Set the node as visited and, if it was visited for the second time, push it onto the the unit_nodes
fn visit(idx: usize, visited: &mut HashMap<usize, i32>, unit_nodes: &mut Vec<usize>) -> (){
    if !visited.contains_key(&idx) {
        visited.insert(idx, 0);
    }
    else if visited[&idx] == 0 {
        unit_nodes.push(idx);
        *visited.get_mut(&idx).unwrap() = 1;
    }
}

// Perform a DFS through the proof and get all unit nodes
fn collect_units(proof : &Proof) -> Vec<usize> {
    let mut curr = proof.commands.len() - 1;        // store the current node in the DFS
    let mut queue = VecDeque::new();      // the next nodes that are going to be visited
    let mut visited = HashMap::new(); // the nodes that were already visited
    let mut unit_nodes = Vec::new();           // the unit nodes that were visited more than once
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

// Find out which nodes were replaced and by who by performing a recursive DFS
fn fix_proof(curr: usize, proof: &Proof, unit_nodes: &[usize], dnm: &[bool], actual : &mut[usize]){
    if dnm[curr] {
        return;
    }

    // Visit the current node
    match &proof.commands[curr] {
        ProofCommand::Step(step) => {
            // If the command has premises, process them
            for i in 0..step.premises.len(){
                fix_proof(step.premises[i].1, proof, unit_nodes, dnm, actual);
            }

            // If one parent is a DNM, it must be replaced by other parent
            let mut dnm_parents = Vec::new(); // Store all parents that were deleted
            for i in 0..step.premises.len(){
                let parent = step.premises[i].1;
                if dnm[parent] {
                    dnm_parents.push(parent);
                }
            }

            // Replace the current node for its non deleted parent if it has a DNM parent
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
    // In some cases, this rule is used with a single premise `(not true)` to justify an empty
    // conclusion clause
    if conclusion.is_empty() && premises.len() == 1 {
        if let [t] = premises[0].clause {
            if match_term!((not true) = t).is_some() {
                panic!("Cannot determine the pivots");
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
    // determine this by looking at the conclusion and using it to derive the pivots.
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
            // pivots set, depending on whether it is present in the conclusion clause or not
            let mut try_eliminate = |pivot| match pivots.entry(pivot) {
                Entry::Occupied(mut e) => {
                    e.insert(true);
                    true
                }
                Entry::Vacant(_) => false,
            };

            // Only one pivot may be eliminated per clause, so if we already found this clauses'
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

    // If we find a pivot that was set as true, then it is a valid pivot and we return it
    for i in pivots{
        if i.1{
            return (pool, (i.0.0 as u32, i.0.1));
        }
    }
    panic!("Cannot determine the pivots");
}

// Receives two parents and the resolution conclusion. From this, computes another resolution between the replaced parents
fn binary_resolution_from_old(
    pool : &mut TermPool,
    left_parent : usize,
    right_parent : usize,
    new_commands : Vec<ProofCommand>,
    curr_step : &ProofStep,
) -> Vec<Rc<Term>>{
    let mut current_vec = Vec::new(); //stores all the variables of the left clause with removed negations
    let mut current = AHashSet::new(); //stores all the variables of the left clause with removed negations
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
    
    //create the premises necessary to decide the pivots of the resolution
    let premises = [Premise::new((0 as usize, left_parent), &new_commands[left_parent]),
                    Premise::new((0 as usize, right_parent),&new_commands[right_parent])];

    let (pool, mut pivot) = get_pivots(&curr_step.clause, &premises, pool);
    pivot.0 = 0;

    //find out if the is_pivot_in_current should be true or false
    let mut is_pivot_in_current = true;
    for i in 0..current_vec.len(){
        if pivot.1 == current_vec[i].1 && current_vec[i].0 % 2 == 1{
            is_pivot_in_current = false;
        }
    }

    //perform the binary resolution step with the right clause and return the result
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

//given a node from the old proof, add all of its ancestors and then it to a new proof
fn add_node<'a>(curr: usize,
            old_proof : &Proof,
            actual : &[usize],
            new_commands :  &'a mut Vec<ProofCommand>,
            pool : &mut TermPool,
            added: &mut Vec<Option<usize>>
) -> (usize, &'a mut Vec<ProofCommand>){
    //if it was already added, do not do anything
    match added[curr] {
        Some(idx) => return (idx, new_commands),
        _ => (),
    }

    match &old_proof.commands[curr] {
        ProofCommand::Step(step) => {
            // If the command has premises, add them
            let mut new_premises = Vec::new();
            for i in 0..step.premises.len(){
                let (added, mut _new_commands) = add_node(actual[step.premises[i].1], old_proof, actual, new_commands, pool, added);
                new_premises.push((0 as usize, added));
            }
            
            let new_clause;
            // If it is a resolution, then perform the resolution step again because the parents may have changed
            if step.rule == "resolution" || step.rule == "th_resolution"{
                new_clause = binary_resolution_from_old(pool, new_premises[0].1, new_premises[1].1, new_commands.to_vec(), step);
            }
            // If it is not a resolution, then do not replace it, insert the exact same node
            else{
                new_clause = Vec::from(old_proof.commands[curr].clause());
            }
            
            // Put the new term in the new_commands vec with the right format
            let new_id = (new_commands.len() + 1).to_string();
            let command = ProofCommand::Step(ProofStep{ id       : String::from("t") + &new_id,
                                                            clause   : new_clause,
                                                            rule     : step.rule.clone(),
                                                            premises : new_premises,
                                                            args     : vec![],
                                                            discharge: vec![]});
            new_commands.push(command);

        }
        // If it is an Assume, just replace the id
        ProofCommand::Assume {id: _, term} => {
            let new_id = (new_commands.len() + 1).to_string();
            let command = ProofCommand::Assume{id : String::from("h") + &new_id, term : Rc::clone(term)};
            new_commands.push(command);
        }
        _ => {}
    }

    // Return the new position on the commands vec (and the new_commands vec itself to abide to the ownership rules)
    let idx = new_commands.len() - 1;
    added[curr] = Some(idx);
    return (idx, new_commands);
}


// Perform a resolution step assuming that the right parent is a unit node
fn binary_resolution_with_unit(
    pool : &mut TermPool,
    left_parent : usize,
    right_parent : usize,
    new_commands : Vec<ProofCommand>,
) -> Vec<Rc<Term>>{
    // Stores all the variables of the left clause with removed negations
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

    // Get the pivot from the right parent and perform the resolution step
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

    // If there are no unit nodes, the algorithm cannot do anything
    if unit_nodes.len() == 0{
        print_proof(&proof.commands, false);
        return;
    }
    
    let mut dnm = Vec::new(); // dnm[i] is true if node i was deleted and false otherwise
    dnm.resize(proof.commands.len(), false);
    for i in &unit_nodes{
        dnm[*i] = true;
    }

    // actual[i] is going to be the node that has replaced node i (it is i if it was not replaced)
    let mut actual = Vec::new();
    for i in 0..dnm.len(){
        actual.push(i as usize);
    }

    // fix_proof is the function that sets actual to the true values
    let curr = proof.commands.len() - 1;
    fix_proof(curr, proof, &unit_nodes, &dnm, &mut actual);

    let mut new_proof_commands = Vec::new(); // the proof commands of the compressed proofs
    let mut added: Vec<Option<usize>> = vec![None; proof.commands.len()]; // vec with all the nodes that have already been added
    
    // Add the last node of the original proof and all of its ancestors
    let (_, mut new_proof_commands) = add_node(proof.commands.len() - 1, proof, &actual, &mut new_proof_commands, pool, &mut added);

    // Add each unit node (and its ancestors) and then perform binary resolution between them and the current last node of the proof
    for i in unit_nodes{
        let previous_last_node = new_proof_commands.len() - 1;
        let (_, new_proof_commands) = add_node(i, proof, &actual, &mut new_proof_commands, pool, &mut added);

        // Perform the binary resolution step
        let current_last_node = new_proof_commands.len() - 1;
        let new_premises = [(0 as usize, previous_last_node), (0 as usize, current_last_node)];
        let new_clause = binary_resolution_with_unit(pool, previous_last_node, current_last_node, new_proof_commands.to_vec());

        // Add the new clause to the proof
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