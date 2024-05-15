use super::*;

/// An alternative, graph-based representation for an Alethe proof.
///
/// Instead of storing steps in a vector like [[Proof]], steps in this representaion are nodes in a
/// directed acyclic graph, and each step holds a reference-counted pointer to each of its premises.
///
/// By definition, this representation implicitly prunes the proof of unused steps. Since we
/// generally want to check all proof steps, even if they are not used to reach the proof's
/// conclusion, this representation is not appropriate for proof checking. Instead, it is better
/// suited for elaboration and other kinds of proof manipulation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofNode {
    /// An `assume` command.
    Assume {
        id: String,
        depth: usize,
        term: Rc<Term>,
    },

    /// A `step` command.
    Step(StepNode),

    /// A subproof.
    Subproof(SubproofNode),
}

impl ProofNode {
    /// Returns the unique id of this command.
    ///
    /// For subproofs, this is the id of the last step in the subproof.
    pub fn id(&self) -> &str {
        match self {
            ProofNode::Assume { id, .. } => id,
            ProofNode::Step(s) => &s.id,
            ProofNode::Subproof(s) => s.last_step.id(),
        }
    }

    /// Returns an integer representing this node's "depth", that is, the number of nested subproofs
    /// that surround it.
    pub fn depth(&self) -> usize {
        match self {
            ProofNode::Assume { depth, .. } => *depth,
            ProofNode::Step(s) => s.depth,
            ProofNode::Subproof(s) => s.last_step.depth() - 1,
        }
    }

    /// Returns the clause of this command.
    ///
    /// For `assume` commands, this is a unit clause containing the assumed term; for steps, it's
    /// the conclusion clause; and for subproofs, it's the conclusion clause of the last step in the
    /// subproof.
    pub fn clause(&self) -> &[Rc<Term>] {
        match self {
            ProofNode::Assume { term, .. } => std::slice::from_ref(term),
            ProofNode::Step(StepNode { clause, .. }) => clause,
            ProofNode::Subproof(s) => s.last_step.clause(),
        }
    }

    /// Returns `true` if the node is an `assume` command.
    pub fn is_assume(&self) -> bool {
        matches!(self, ProofNode::Assume { .. })
    }

    /// Returns `true` if the node is a `step` command.
    pub fn is_step(&self) -> bool {
        matches!(self, ProofNode::Step(_))
    }

    /// Returns `true` if the node is a subproof.
    pub fn is_subproof(&self) -> bool {
        matches!(self, ProofNode::Subproof(_))
    }
}

/// A `step` command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StepNode {
    /// The step id.
    pub id: String,

    /// The step's depth.
    pub depth: usize,

    /// The conclusion clause.
    pub clause: Vec<Rc<Term>>,

    /// The rule used by the step.
    pub rule: String,

    /// The premises of the step, given via the `:premises` attribute.
    pub premises: Vec<Rc<ProofNode>>,

    /// The step arguments, given via the `:args` attribute.
    pub args: Vec<ProofArg>,

    /// The local premises that this step discharges, given via the `:discharge` attribute.
    pub discharge: Vec<Rc<ProofNode>>,

    /// If this step is the last step in a subproof, this holds the (implicitly referenced) previous
    /// step in the subproof.
    pub previous_step: Option<Rc<ProofNode>>,
}

/// A subproof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubproofNode {
    /// The last step in the subproof.
    pub last_step: Rc<ProofNode>,

    /// The arguments of the subproof.
    ///
    /// They can be either a variable declaration, of the form `(<symbol> <sort>)`, or an
    /// assignment, of the form `(:= <symbol> <term>)`.
    pub args: Vec<AnchorArg>,

    /// The outbound premises of a subproof, that is, the premises from steps in the subproof that
    /// refer to steps outside it.
    pub outbound_premises: Vec<Rc<ProofNode>>,
}

/// Converts a list of proof commands into a `ProofNode`.
pub fn proof_list_to_node(commands: Vec<ProofCommand>) -> Rc<ProofNode> {
    use indexmap::IndexSet;

    struct Frame {
        commands: std::vec::IntoIter<ProofCommand>,
        accumulator: Vec<Rc<ProofNode>>,
        args: Vec<AnchorArg>,
        outbound_premises: IndexSet<Rc<ProofNode>>,
    }

    let mut stack: Vec<Frame> = vec![Frame {
        commands: commands.into_iter(),
        accumulator: Vec::new(),
        args: Vec::new(),
        outbound_premises: IndexSet::new(),
    }];

    let new_root_proof = loop {
        let next = stack.last_mut().unwrap().commands.next();
        let node = match next {
            Some(ProofCommand::Assume { id, term }) => {
                ProofNode::Assume { id, depth: stack.len() - 1, term }
            }
            Some(ProofCommand::Step(s)) => {
                let premises: Vec<_> = s
                    .premises
                    .into_iter()
                    .map(|(depth, index)| stack[depth].accumulator[index].clone())
                    .collect();
                let discharge: Vec<_> = s
                    .discharge
                    .into_iter()
                    .map(|(depth, index)| stack[depth].accumulator[index].clone())
                    .collect();

                for p in &premises {
                    if p.depth() < stack.len() - 1 {
                        let frame = stack.last_mut().unwrap();
                        frame.outbound_premises.insert(p.clone());
                    }
                }

                let previous_step = if stack.len() > 1 && stack.last().unwrap().commands.len() == 0
                {
                    Some(stack.last().unwrap().accumulator.last().unwrap().clone())
                } else {
                    None
                };

                ProofNode::Step(StepNode {
                    id: s.id,
                    depth: stack.len() - 1,
                    clause: s.clause,
                    rule: s.rule,
                    premises,
                    args: s.args,
                    discharge,
                    previous_step,
                })
            }
            Some(ProofCommand::Subproof(s)) => {
                let frame = Frame {
                    commands: s.commands.into_iter(),
                    accumulator: Vec::new(),
                    args: s.args,
                    outbound_premises: IndexSet::new(),
                };
                stack.push(frame);
                continue;
            }

            // We reached the end of the current subproof
            None => {
                let mut frame = stack.pop().unwrap();
                if stack.is_empty() {
                    break frame.accumulator;
                }

                for p in &frame.outbound_premises {
                    if p.depth() < stack.len() - 1 {
                        let frame = stack.last_mut().unwrap();
                        frame.outbound_premises.insert(p.clone());
                    }
                }

                ProofNode::Subproof(SubproofNode {
                    last_step: frame.accumulator.pop().unwrap(),
                    args: frame.args,
                    outbound_premises: frame.outbound_premises.into_iter().collect(),
                })
            }
        };
        stack.last_mut().unwrap().accumulator.push(Rc::new(node));
    };

    new_root_proof
        .into_iter()
        .find(|node| node.clause().is_empty())
        .unwrap()
}

/// Converts a `ProofNode` into a list of proof commands.
pub fn proof_node_to_list(root: &Rc<ProofNode>) -> Vec<ProofCommand> {
    use std::collections::{HashMap, HashSet};

    let mut stack: Vec<Vec<ProofCommand>> = vec![Vec::new()];

    let mut seen: HashMap<&Rc<ProofNode>, (usize, usize)> = HashMap::new();
    let mut todo: Vec<(&Rc<ProofNode>, bool)> = vec![(root, false)];
    let mut did_outbound: HashSet<&Rc<ProofNode>> = HashSet::new();

    loop {
        let Some((node, is_done)) = todo.pop() else {
            assert!(stack.len() == 1);
            return stack.pop().unwrap();
        };
        if !is_done && seen.contains_key(&node) {
            continue;
        }

        let command = match node.as_ref() {
            ProofNode::Assume { id, term, .. } => {
                ProofCommand::Assume { id: id.clone(), term: term.clone() }
            }
            ProofNode::Step(s) if !is_done => {
                todo.push((node, true));

                if let Some(previous) = &s.previous_step {
                    todo.push((previous, false));
                }

                let premises_and_discharge = s.premises.iter().chain(s.discharge.iter()).rev();
                todo.extend(premises_and_discharge.map(|node| (node, false)));
                continue;
            }
            ProofNode::Step(s) => {
                let premises: Vec<_> = s.premises.iter().map(|node| seen[node]).collect();
                let discharge: Vec<_> = s.discharge.iter().map(|node| seen[node]).collect();
                ProofCommand::Step(ProofStep {
                    id: s.id.clone(),
                    clause: s.clause.clone(),
                    rule: s.rule.clone(),
                    premises,
                    args: s.args.clone(),
                    discharge,
                })
            }
            ProofNode::Subproof(s) if !is_done => {
                assert!(
                    node.depth() == stack.len() - 1,
                    "all outbound premises should have already been dealt with!"
                );

                // First, we add all of the subproof's outbound premises if he haven't already
                if !did_outbound.contains(&node) {
                    did_outbound.insert(node);
                    todo.push((node, false));
                    todo.extend(s.outbound_premises.iter().map(|premise| (premise, false)));
                    continue;
                }

                todo.push((node, true));
                todo.push((&s.last_step, false));
                stack.push(Vec::new());
                continue;
            }
            ProofNode::Subproof(s) => {
                let commands = stack.pop().unwrap();
                if stack.is_empty() {
                    return commands;
                }
                assert!(commands.len() >= 2, "malformed subproof!");
                ProofCommand::Subproof(Subproof {
                    commands,
                    args: s.args.clone(),
                    context_id: 0,
                })
            }
        };
        let d = node.depth();
        let index = stack[d].len();
        seen.insert(node, (d, index));
        stack[d].push(command);
    }
}
