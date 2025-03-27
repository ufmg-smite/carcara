use crate::ast::{Proof, ProofCommand};
use std::{
    cmp::Ordering,
    collections::{BinaryHeap, HashSet},
};

/// Struct responsible for storing a thread work schedule.
///
/// Here, each step from the original proof is represented as a tuple:
/// (depth, subproof index). The first element is the subproof nesting `depth`
/// (in the subproof stack) and `subproof index` is the index where this step is
/// located in the subproof vector.
#[derive(Clone, Default)]
pub struct Schedule {
    steps: Vec<(usize, usize)>,
}

impl Schedule {
    pub fn new() -> Self {
        Self::default()
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

    /// Returns an iterator over the proof commands. See [`ScheduleIter`].
    pub fn iter<'a>(&'a self, proof: &'a [ProofCommand]) -> ScheduleIter<'a> {
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
        other.0.cmp(&self.0)
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
    /// proof steps have different costs to be checked) aiming for minimum
    /// amount of async overhead.
    ///
    /// Returns a scheduler itself and context usage info (a vector holding
    /// how many threads are going to use each of the contexts. This vector maps
    /// the contexts based in the subproof hashing value (i.e. `subproof_id`)
    /// created in the parser).
    pub fn new(num_workers: usize, proof: &Proof) -> (Self, Vec<usize>) {
        // Initializes the control and result variables
        let cmds = &proof.commands;
        let mut loads = vec![Schedule::new(); num_workers];
        let mut stack = vec![StackLevel::new(0, cmds, None)];
        let mut pq = BinaryHeap::<AssignedLoad>::new();
        let mut context_usage = vec![];
        for i in 0..num_workers {
            pq.push(AssignedLoad(0, i));
        }

        loop {
            // Pop the finished subproofs
            while !stack.is_empty() && {
                let top = stack.last().unwrap();
                top.id == top.cmds.len()
            } {
                for schedule_id in &stack.last().unwrap().used_by {
                    let last = loads[*schedule_id].last().unwrap();
                    // If it's an useless context insertion
                    if last.0 < stack.len()
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
            if stack.is_empty() {
                break;
            }
            //
            let AssignedLoad(mut load, load_index) = pq.pop().unwrap();
            {
                let top = stack.last().unwrap();
                let step_weight = get_step_weight(&top.cmds[top.id]);
                load = load
                    .checked_add(step_weight)
                    .expect("Weight balancing overflow!");
                pq.push(AssignedLoad(load, load_index));
            }

            let depth = stack.len() - 1;
            let mut i = 1;
            let initial_layer = {
                let tmp = loads[load_index].last().unwrap_or(&(0, 0));
                if tmp.1 == usize::MAX {
                    tmp.0 - 1
                } else {
                    tmp.0
                }
            };
            // If this step needs the context of the subproof oppening step
            // but it was not assigned to this schedule yet
            while initial_layer + i <= depth {
                let subproof_oppening = stack[initial_layer + i].pre_req.unwrap();
                let last_inserted = *loads[load_index].last().unwrap_or(&(usize::MAX, 0));

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

/// Iterates through schedule steps
pub struct ScheduleIter<'a> {
    proof_stack: Vec<&'a [ProofCommand]>,
    steps: &'a Vec<(usize, usize)>,
    step_id: usize,
}

impl<'a> ScheduleIter<'a> {
    pub fn new(proof_commands: &'a [ProofCommand], steps: &'a Vec<(usize, usize)>) -> Self {
        Self {
            proof_stack: vec![proof_commands],
            steps,
            step_id: 0,
        }
    }

    /// Returns the current nesting depth of the iterator, or more precisely,
    /// the nesting depth of the last step that was returned. This depth starts
    /// at zero, for steps in the root proof.
    pub fn depth(&self) -> usize {
        self.proof_stack.len() - 1
    }

    /// Returns `true` if the iterator is currently in a subproof, that is, if
    /// its depth is greater than zero.
    pub fn is_in_subproof(&self) -> bool {
        self.depth() > 0
    }

    /// Returns a slice to the commands of the inner-most open subproof.
    pub fn current_subproof(&self) -> Option<&[ProofCommand]> {
        self.is_in_subproof()
            .then(|| *self.proof_stack.last().unwrap())
    }

    /// Returns `true` if the most recently returned step is the last step of
    /// the current subproof.
    pub fn is_end_step(&self) -> bool {
        self.is_in_subproof()
            && self.steps[self.step_id - 1].1 == self.proof_stack.last().unwrap().len() - 1
    }

    /// Returns the command referenced by a premise index of the form (depth, index in subproof).
    /// This method may panic if the premise index does not refer to a valid command.
    pub fn get_premise(&self, (depth, index): (usize, usize)) -> &ProofCommand {
        &self.proof_stack[depth][index]
    }
}

impl<'a> Iterator for ScheduleIter<'a> {
    type Item = &'a ProofCommand;

    fn next(&mut self) -> Option<Self::Item> {
        // If it is the end of the steps
        if self.step_id >= self.steps.len() {
            return None;
        }

        // If current step is an closing subproof step
        while let (_, usize::MAX) = self.steps[self.step_id] {
            self.proof_stack.pop();
            self.step_id += 1;
            // If reached the last closing step of the whole proof
            if self.step_id == self.steps.len() {
                return None;
            }
        }
        let cur_step = self.steps[self.step_id];
        self.step_id += 1;

        let top = self.proof_stack.last().unwrap();
        let command = &top[cur_step.1];
        // Opens a new subproof
        if let ProofCommand::Subproof(subproof) = command {
            self.proof_stack.push(&subproof.commands);
        }
        Some(command)
    }
}

/// Function that returns a weight associated with a specific rule. These
/// weights are directly correlated to carcara (Single Thread/previous version)
/// median performance while solving each of those rules.
///
/// Even though subproofs should have a weight (since it has a high cost to be
/// computed), it's for better of scheduler architecture that subproofs have a
/// null weight.
///
/// If you're interested in these weight values, take a look at [Carcara's
/// paper](https://hanielbarbosa.com/papers/tacas2023.pdf)
/// published at TACAS in April 2023 and its benchmark data.
///
/// The rules with null weight are rules that we had no info about the median
/// performance, since the solver used in the paper dataset does not generate
/// these rules.
pub fn get_step_weight(step: &ProofCommand) -> u64 {
    match step {
        ProofCommand::Assume { .. } => 230,
        ProofCommand::Subproof(_) => 0,
        ProofCommand::Step(s) => {
            match &s.rule as &str {
                "assume" => 230,
                "true" => 0, //-1
                "false" => 263,
                "not_not" => 574,
                "and_pos" => 361,
                "and_neg" => 607,
                "or_pos" => 640,
                "or_neg" => 460,
                "xor_pos1" => 763,
                "xor_pos2" => 345,
                "xor_neg1" => 0, //-1
                "xor_neg2" => 0, //-1
                "implies_pos" => 394,
                "implies_neg1" => 214,
                "implies_neg2" => 287,
                "equiv_pos1" => 763,
                "equiv_pos2" => 541,
                "equiv_neg1" => 434,
                "equiv_neg2" => 476,
                "ite_pos1" => 804,
                "ite_pos2" => 344,
                "ite_neg1" => 566,
                "ite_neg2" => 542,
                "eq_reflexive" => 451,
                "eq_transitive" => 780,
                "eq_congruent" => 722,
                "eq_congruent_pred" => 632,
                "distinct_elim" => 812,
                "la_rw_eq" => 1091,
                "la_generic" => 87564,
                "la_disequality" => 919,
                "la_totality" => 0, //-1
                "la_tautology" => 4291,
                "forall_inst" => 7877,
                "qnt_join" => 2347,
                "qnt_rm_unused" => 3659,
                "resolution" => 7491,
                "th_resolution" => 2462,
                "refl" => 1305,
                "trans" => 575,
                "cong" => 984,
                "ho_cong" => 0, //-1
                "and" => 493,
                "tautology" => 0, //-1
                "not_or" => 476,
                "or" => 426,
                "not_and" => 927,
                "xor1" => 0,     //-1
                "xor2" => 0,     //-1
                "not_xor1" => 0, //-1
                "not_xor2" => 0, //-1
                "implies" => 788,
                "not_implies1" => 402,
                "not_implies2" => 484,
                "equiv1" => 837,
                "equiv2" => 812,
                "not_equiv1" => 418,
                "not_equiv2" => 451,
                "ite1" => 509,
                "ite2" => 493,
                "not_ite1" => 722,
                "not_ite2" => 476,
                "ite_intro" => 3192,
                "contraction" => 1731,
                "connective_def" => 705,
                "ite_simplify" => 1797,
                "eq_simplify" => 845,
                "and_simplify" => 1165,
                "or_simplify" => 1133,
                "not_simplify" => 787,
                "implies_simplify" => 1231,
                "equiv_simplify" => 1337,
                "bool_simplify" => 1436,
                "qnt_simplify" => 517,
                "div_simplify" => 2117,
                "prod_simplify" => 2527,
                "unary_minus_simplify" => 0, //-1
                "minus_simplify" => 1059,
                "sum_simplify" => 2248,
                "comp_simplify" => 1781,
                "nary_elim" => 0, //-1
                "ac_simp" => 9781,
                "bfun_elim" => 8558,
                "bind" => 5924,
                "qnt_cnf" => 14244,
                "subproof" => 262,
                "let" => 4718,
                "onepoint" => 7787,
                "sko_ex" => 9321,
                "sko_forall" => 12242,
                "reordering" => 1452,
                "symm" => 682,
                "not_symm" => 0, //-1
                "eq_symmetric" => 673,
                "weakening" => 508,
                "bind_let" => 2324,
                "la_mult_pos" => 1446,
                "la_mult_neg" => 1447,
                "hole" => 185,  //Debug only
                "trust" => 185, //Debug only
                "strict_resolution" => 1276,

                _ => 0,
            }
        }
    }
}
