use crate::{ast::*};
use std::collections::HashMap;
use std::collections::VecDeque;
use crate::checker::rules::resolution::binary_resolution;

fn visit(idx: usize, visited: &mut HashMap<usize, i32>, unit_nodes: &mut Vec<usize>) -> (){
    if !visited.contains_key(&idx) {
        visited.insert(idx, 0);
    }
    else if visited[&idx] == 0 {
        unit_nodes.push(idx);
        *visited.get_mut(&idx).unwrap() = 1;
    }
}

fn collect_units(proof : &Proof) -> Vec<usize> {
    let mut curr = proof.commands.len() - 1;
    let mut queue = VecDeque::new();
    let mut visited = HashMap::new();
    let mut unit_nodes = Vec::new();
    queue.push_back(curr);

    //bottom up dfs to go through the proof
    while queue.len() > 0 {
        curr = queue[0];
        queue.pop_front();

        match &proof.commands[curr] {
            ProofCommand::Step(step) => {
                //if the command has premises, add them to the queue
                print!("Os pais de {} são ", curr);
                for i in 0..step.premises.len(){
                    print!("{} ", step.premises[i].1);
                    queue.push_front(step.premises[i].1);
                }
                println!("");

                //if it is a unit clause, then visit it
                if step.clause.len() == 1{
                    visit(curr, &mut visited, &mut unit_nodes);
                }
            }
            ProofCommand::Assume {id: _, term} => {
                match &**term {
                    //if it is a terminal, then it is a unit clause
                    Term::Terminal(_) => {
                        visit(curr, &mut visited, &mut unit_nodes);
                    }
                    Term::Op(_operator, terms) => {
                        //only visit it if it is a unit clause
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

    println!("unit_nodes: {:?}", unit_nodes);
    println!("visited: {:?}", visited);
    return unit_nodes;
}

fn find(i: usize, actual: &mut[usize]) -> usize {
    if actual[i] == i {
        return i;
    }
    actual[i] = find(actual[i], actual);
    return actual[i];
}

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
}