use crate::{ast::*};
use std::collections::HashMap;
use std::collections::VecDeque;

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
                for i in 0..step.premises.len(){
                    queue.push_front(step.premises[i].1);
                }

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

fn fix_proof(proof: &Proof, unit_nodes: Vec<usize>){
    let mut dnm = Vec::new();
    dnm.resize(proof.commands.len(), 0);
    for i in unit_nodes{
        dnm[i] = 1;
    }

}

pub fn compress_proof(proof: &Proof){
    let unit_nodes = collect_units(&proof);
    fix_proof(proof, unit_nodes)
}