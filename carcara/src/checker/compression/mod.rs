use crate::{ast::*};
use std::collections::VecDeque;
use std::collections::HashSet;

fn visit(id : String, idx : usize, visited_nodes: &mut HashSet<String>, unit_nodes : &mut Vec<(String, usize)>, inserted : &mut HashSet<String>) -> (){
    if visited_nodes.contains(&id) && !inserted.contains(&id) {
        let cpy = id.clone();
        unit_nodes.push((id, idx));
        inserted.insert(cpy);
    }
    else {
        visited_nodes.insert(id);
    }
}

fn collect_units(proof : &Proof) -> Vec<(String, usize)> {
    let mut curr = proof.commands.len() - 1;
    let mut queue = VecDeque::new();
    let mut visited_nodes = HashSet::new();
    let mut unit_nodes = Vec::new();
    let mut inserted = HashSet::new();
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
                    let id = step.id.clone();
                    visit(id, curr, &mut visited_nodes, &mut unit_nodes, &mut inserted);
                }
            }
            ProofCommand::Assume {id: _, term} => {
                match &**term {
                    //if it is a terminal, then it is a unit clause
                    Term::Terminal(_) => {
                        let id = format!("{:?}", term);
                        visit(id, curr, &mut visited_nodes, &mut unit_nodes, &mut inserted);
                    }
                    Term::Op(_operator, terms) => {
                        //only visit it if it is a unit clause
                        if terms.len() == 1{
                            let id = format!("{:?}", term);
                            visit(id, curr, &mut visited_nodes, &mut unit_nodes, &mut inserted);
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



pub fn compress_proof(proof : &Proof){
    let _unit_nodes = collect_units(&proof);
}