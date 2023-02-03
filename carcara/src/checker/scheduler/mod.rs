pub(crate) mod iter;

pub mod Schedule {
    #![allow(non_snake_case)]
    use super::iter::ScheduleIter;
    use crate::ast::ProofCommand;

    /// Struct responsible for storing a thread work schedule. Each schedule
    /// will store the original proof steps in the following format: (depth, subproof index)
    #[derive(Clone)]
    pub struct Schedule<'a> {
        proof_cmds: &'a [ProofCommand],
        steps: Vec<(usize, usize)>,
    }

    impl<'a> Schedule<'a> {
        pub fn new(proof_cmds: &'a [ProofCommand]) -> Self {
            Schedule {
                proof_cmds: proof_cmds,
                steps: vec![],
            }
        }

        /// Inserts a new step into the end of the schedule steps
        pub fn push(&mut self, cmd: (usize, usize)) {
            self.steps.push(cmd);
        }

        /// Returns the last schedule step
        pub fn last(&mut self) -> Option<&(usize, usize)> {
            self.steps.last()
        }

        /// Returns an iterator over the proof commands. See [`ProofIter`].
        pub fn iter(&self) -> ScheduleIter {
            ScheduleIter::new(self.proof_cmds, &self.steps)
        }
    }
}

pub mod Scheduler {
    #![allow(non_snake_case)]
    use super::Schedule::Schedule;
    use crate::ast::{Proof, ProofCommand};
    use std::{cmp::Ordering, collections::hash_set::HashSet};

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

    /// Represents a level in the proof stacks. It holds the subproof itself,
    /// its prerequisite step (anchor) and which schedules used any step of
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

    pub struct Scheduler<'a> {
        pub loads: Vec<Schedule<'a>>,
    }

    impl<'a> Scheduler<'a> {
        /// Creates a thread scheduler for this proof using a specific number of
        /// workers. This scheduler is responsible for balancing the load of this
        /// proof aiming the minimum amount of sync overhead
        pub fn new(num_workers: usize, proof: &'a Proof) -> Self {
            let cmds = &proof.commands;
            let mut loads = vec![Schedule::new(cmds); num_workers];
            let mut stack = vec![StackLevel::new(0, cmds, None)];
            let mut load_index = 0;

            loop {
                // Pop the finished subproofs
                while stack.len() != 0 && {
                    let top = stack.last().unwrap();
                    top.id == top.cmds.len()
                } {
                    // Creates a closing step for each schedule that used this subproof
                    for schedule_id in &stack.last().unwrap().used_by {
                        loads[*schedule_id].push((stack.len() - 1, usize::MAX));
                    }
                    stack.pop();
                }
                if stack.len() == 0 {
                    break;
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
                    let last_inserted =
                        *loads[load_index].last().unwrap_or_else(|| &(usize::MAX, 0));

                    if last_inserted != subproof_oppening {
                        loads[load_index].push(subproof_oppening);
                        stack[subproof_oppening.0].used_by.insert(load_index);
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
                }

                load_index = (load_index + 1) % num_workers;
            }
            Scheduler { loads }
        }
    }
}
