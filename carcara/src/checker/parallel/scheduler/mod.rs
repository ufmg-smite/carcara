pub(crate) mod iter;
pub(crate) mod weights;

use crate::ast::{Proof, ProofCommand};
use iter::ScheduleIter;
use std::{
    cmp::Ordering,
    collections::{BinaryHeap, HashSet},
};
use weights::get_step_weight;

/// Struct responsible for storing a thread work schedule.
///
/// Here, each step from the original proof is represented as a tuple:
/// (depth, subproof index). The first element is the subproof nesting `depth`
/// (in the subproof stack) and `subproof index` is the index where this step is
/// located in the subproof vector.
#[derive(Clone)]
pub struct Schedule {
    steps: Vec<(usize, usize)>,
}

impl Schedule {
    pub fn new() -> Self {
        Schedule { steps: vec![] }
    }

    /// Inserts a new step into the end of the schedule steps vector
    pub fn push(&mut self, cmd: (usize, usize)) {
        self.steps.push(cmd);
    }

    /// Removes the last step from the end of the steps vector
    pub fn pop(&mut self) {
        self.steps.pop();
    }

    /// Returns the last schedule step
    pub fn last(&self) -> Option<&(usize, usize)> {
        self.steps.last()
    }

    /// Returns an iterator over the proof commands. See [`ProofIter`].
    pub fn iter<'a>(&'a self, proof: &'a [ProofCommand]) -> ScheduleIter {
        ScheduleIter::new(proof, &self.steps)
    }
}

// =============================================================================

/// Represents the current load assigned for an specific schedule.
/// `0`: Current work load
/// `1`: Schedule index
#[derive(Eq)]
struct AssignedLoad(u64, usize);

impl Ord for AssignedLoad {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.0 > other.0 {
            return Ordering::Less;
        } else if self.0 < other.0 {
            return Ordering::Greater;
        }
        return Ordering::Equal;
    }
}

impl PartialOrd for AssignedLoad {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for AssignedLoad {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

/// Represents a level in the proof stack. It holds the subproof itself,
/// its prerequisite step (anchor) and which schedules used any step inside
/// this layer
struct StackLevel<'a> {
    id: usize,
    cmds: &'a [ProofCommand],
    pre_req: Option<(usize, usize)>,
    used_by: HashSet<usize>,
}

impl<'a> StackLevel<'a> {
    pub fn new(id: usize, cmds: &'a [ProofCommand], pre_req: Option<(usize, usize)>) -> Self {
        Self {
            id,
            cmds,
            pre_req,
            used_by: HashSet::new(),
        }
    }
}

/// Struct that stores the schedules for each thread.
pub struct Scheduler {
    pub loads: Vec<Schedule>,
}

impl Scheduler {
    /// Creates a thread scheduler for this proof using a specific number of
    /// workers. This scheduler is responsible for balancing the load (the
    /// proof steps have different costs to be checked) aiming the minimum
    /// amount of async overhead
    pub fn new(num_workers: usize, proof: &Proof) -> (Self, Vec<usize>) {
        // Initializes the control and result variables
        let cmds = &proof.commands;
        let mut loads = vec![Schedule::new(); num_workers];
        let mut stack = vec![StackLevel::new(0, cmds, None)];
        let mut pq = BinaryHeap::<AssignedLoad>::new();
        let mut context_usage = vec![];
        for i in 0..num_workers {
            pq.push(AssignedLoad { 0: 0, 1: i });
        }

        loop {
            // Pop the finished subproofs
            while stack.len() != 0 && {
                let top = stack.last().unwrap();
                top.id == top.cmds.len()
            } {
                for schedule_id in &stack.last().unwrap().used_by {
                    let last = loads[*schedule_id].last().unwrap();
                    // If it's an useless context insertion
                    if last.0 <= stack.len() - 1
                        && matches!(stack[last.0].cmds[last.1], ProofCommand::Subproof(_))
                    {
                        // Make sure this context usage count is reduced
                        let subproof_id = match &stack[last.0].cmds[last.1] {
                            ProofCommand::Subproof(s) => s.context_id,
                            _ => unreachable!(),
                        };
                        context_usage[subproof_id] -= 1;

                        loads[*schedule_id].pop();
                    }
                    // Creates a closing step for each schedule that used this subproof
                    else {
                        loads[*schedule_id].push((stack.len() - 1, usize::MAX));
                    }
                }
                stack.pop();
            }
            if stack.len() == 0 {
                break;
            }
            //
            let AssignedLoad { 0: mut load, 1: load_index } = pq.pop().unwrap();
            {
                let top = stack.last().unwrap();
                let step_weight = get_step_weight(&top.cmds[top.id]);
                assert!(u64::MAX - step_weight >= load, "Weight balancing overflow!");
                load += step_weight;
                pq.push(AssignedLoad { 0: load, 1: load_index });
            }

            let depth = stack.len() - 1;
            let (mut i, initial_layer) = (1, {
                let tmp = loads[load_index].last().unwrap_or_else(|| &(0, 0));
                if tmp.1 == usize::MAX {
                    tmp.0 - 1
                } else {
                    tmp.0
                }
            });
            // If this step needs the context of the subproof oppening step
            // but it was not assigned to this schedule yet
            while initial_layer + i <= depth {
                let subproof_oppening = stack[initial_layer + i].pre_req.unwrap();
                let last_inserted = *loads[load_index].last().unwrap_or_else(|| &(usize::MAX, 0));

                if last_inserted != subproof_oppening {
                    loads[load_index].push(subproof_oppening);
                    stack[subproof_oppening.0].used_by.insert(load_index);

                    // Now this subproof is used by another schedule
                    let subproof_id = match &stack[subproof_oppening.0].cmds[subproof_oppening.1] {
                        ProofCommand::Subproof(s) => s.context_id,
                        _ => unreachable!(),
                    };
                    context_usage[subproof_id] += 1;
                }
                i += 1;
            }

            let top = stack.last_mut().unwrap();
            // Assign a step to some Schedule
            loads[load_index].push((depth, top.id));
            top.used_by.insert(load_index);

            // Go to next step
            let last_id = top.id;
            top.id += 1;
            if let ProofCommand::Subproof(s) = &top.cmds[last_id] {
                stack.push(StackLevel::new(0, &s.commands, Some((depth, last_id))));
                stack.last_mut().unwrap().used_by.insert(load_index);
                // First schedule using this subproof
                context_usage.push(1);
            }
        }
        (Scheduler { loads }, context_usage)
    }
}
