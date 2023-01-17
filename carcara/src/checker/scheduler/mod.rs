use crate::ast::{Proof, ProofCommand, ProofIter};
use std::{cmp::Ordering, collections::BinaryHeap};

// Represents the remaining load for an specific worker. Implements Ord for heap.
// 0: Remaing load | 1: worker index at the vector of remaining loads
#[derive(Eq)]
struct RemainLoad(usize, usize);

impl Ord for RemainLoad {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.0 > other.0 {
            return Ordering::Greater;
        } else if self.0 < other.0 {
            return Ordering::Less;
        }
        return Ordering::Equal;
    }
}

impl PartialOrd for RemainLoad {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for RemainLoad {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

//
#[derive(Clone)]
pub struct Schedule {
    vec: Vec<ProofCommand>,
}

impl Schedule {
    pub fn new() -> Self {
        Schedule { vec: Vec::new() }
    }

    pub fn push(&mut self, cmd: ProofCommand) {
        self.vec.push(cmd);
    }

    /// Returns an iterator over the proof commands. See [`ProofIter`].
    pub fn iter(&self) -> ProofIter {
        ProofIter::new(&self.vec)
    }
}

#[allow(unused_assignments)]
pub struct Scheduler {
    pub loads: Vec<Schedule>,
}

impl Scheduler {
    pub fn new(num_workers: usize, proof: &Proof) -> Self {
        let cmds = &proof.commands;
        let mut loads = vec![Schedule::new(); num_workers];

        let (mut num_assumes, mut num_steps, mut num_subproofs, mut total) = (0, 0, 0, 0);
        let mut subproofs_ids = vec![];

        // Pre process the proof and slice subproofs from the other types of proof cmds
        let mut i = 0;
        for cmd in cmds {
            match cmd {
                ProofCommand::Assume { .. } => {
                    total += 1;
                    num_assumes += 1;
                }
                ProofCommand::Step(_) => {
                    total += 1;
                    num_steps += 1;
                }
                ProofCommand::Subproof(s) => {
                    num_subproofs += 1;
                    subproofs_ids.push(i);
                    total += s.commands.len();
                }
            }
            i += 1;
        }

        // Defines the total number of steps for each worker
        let mut steps_per_schedule = vec![total / num_workers; num_workers];
        {
            // for _ in 0.. {
            //     steps_per_schedule.push();
            // }
            let remain_to_dist = total - (total / num_workers) * num_workers;
            for i in 0..remain_to_dist {
                steps_per_schedule[i] += 1;
            }
        }

        let mut heap = BinaryHeap::new();
        for i in 0..num_workers {
            heap.push(RemainLoad { 0: steps_per_schedule[i], 1: i });
        }

        // Assign the subproofs for each worker
        i = 0;
        for id in subproofs_ids {
            let mut biggest = heap.pop().unwrap();
            loads[i].push(cmds[id].clone());

            if let ProofCommand::Subproof(s) = &cmds[id] {
                steps_per_schedule[biggest.1] -= s.commands.len();
                biggest.0 -= s.commands.len();

                heap.push(biggest);
            }

            i = (i + 1) % num_workers;
        }

        // Assign the other proof cmds
        for cmd in cmds {
            match cmd {
                ProofCommand::Assume { .. } => {
                    let mut biggest = heap.pop().unwrap();
                    loads[biggest.1].push(cmd.clone());

                    /* TODO: change from weight 1 to an custom weight based in the rule */
                    steps_per_schedule[biggest.1] -= 1;
                    biggest.0 -= 1;

                    heap.push(biggest);
                }
                ProofCommand::Step(_) => {
                    let mut biggest = heap.pop().unwrap();
                    loads[biggest.1].push(cmd.clone());

                    /* TODO: change from weight 1 to an custom weight based in the rule */
                    steps_per_schedule[biggest.1] -= 1;
                    biggest.0 -= 1;

                    heap.push(biggest);
                }
                _ => {}
            }
        }

        Scheduler { loads }
    }
}
