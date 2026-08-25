pub mod dsu;
pub mod operations;
pub mod parser;
pub mod utils;

use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;
use std::hash::Hash;

use crate::ast::{Constant, Operator, Rc, Term, TermPool};
use crate::automata::utils::{has_overlapping_ranges, missing_ranges};
use crate::checker::error::{CheckerError, StringError};

/// Type alias representing the index of a state within an [`Automaton`]'s state vector.
pub type StateId = usize;

/// Condition under which a transition is enabled.
///
/// A trigger may either consume no input (epsilon transition) or
/// consume a single input symbol whose value lies within a given range.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Trigger {
    /// Epsilon transition (does not consume input).
    Epsilon,

    /// Transition enabled by any input symbol in the inclusive range [l, r].
    Range((u32, u32)),
}

impl Trigger {
    /// Returns `true` if `self` subsumes or fully covers the trigger condition of `other`.
    pub fn contains(&self, other: &Trigger) -> bool {
        match (self, other) {
            (Trigger::Epsilon, Trigger::Epsilon) => true,
            (Trigger::Range((a_start, a_end)), Trigger::Range((b_start, b_end))) => {
                a_start <= b_start && b_end <= a_end
            }
            (Trigger::Range((_, _)), Trigger::Epsilon) => false,
            (Trigger::Epsilon, Trigger::Range((_, _))) => false,
        }
    }
}

impl fmt::Display for Trigger {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Epsilon => write!(f, "ε"),
            Self::Range((l, r)) if l == r => write!(f, "{}", l),
            Self::Range((l, r)) => write!(f, "{}, {}", l, r),
        }
    }
}

/// Represents a state in the automaton.
///
/// A state is identified by a symbolic identifier, may be marked as accepting,
/// and defines a set of outgoing transitions labeled by triggers.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct State {
    /// State symbolic name.
    id: String,

    /// Indicates whether this is an accepting (final) state.
    accept: bool,

    /// Set of outgoing transitions.
    transitions: BTreeSet<Transition>,
}

impl State {
    fn new(id: &str, accept: bool) -> State {
        State {
            id: id.to_owned(),
            accept,
            transitions: BTreeSet::new(),
        }
    }
}

/// Represents a transition between automaton states.
///
/// A transition leads from the enclosing source state to a destination state
/// and is labeled by a trigger describing which input symbols enable it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Transition {
    /// Identifier of the destination state.
    to: StateId,

    /// Label of the transition, describing the consumed input.
    trigger: Trigger,
}

impl Ord for Transition {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.trigger.cmp(&other.trigger) {
            core::cmp::Ordering::Equal => self.to.cmp(&other.to),
            ord => ord,
        }
    }
}

impl PartialOrd for Transition {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Transition {
    fn new(state_id: StateId, trigger: Trigger) -> Transition {
        Transition { to: state_id, trigger }
    }
}

/// Represents a finite automaton.
///
/// An `Automaton` value defines the structure of a (possibly nondeterministic)
/// finite automaton with epsilon transitions. It consists of:
///
///  - a symbolic name identifying the automaton;
///  - a finite set of states, stored in `all_states`;
///  - a distinguished initial state, identified by `initial_state`.
///
/// States are indexed by their position in `all_states`. Transitions refer to
/// destination states via these indices (`StateId`), forming a directed graph.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Automaton {
    /// Automaton symbolic name.
    name: String,

    /// Finite collection of states forming the automaton.
    all_states: Vec<State>,

    /// Identifier of the initial state.
    initial_state: StateId,
}

impl Automaton {
    // Helper to obtain the existing StateId or create a new one
    fn get_or_create_state<'a>(
        id: &'a str,
        state_map: &mut HashMap<&'a str, StateId>,
        all_states: &mut Vec<State>,
        accepting_states: &HashSet<&str>,
    ) -> StateId {
        if let Some(&index) = state_map.get(id) {
            index
        } else {
            let index = all_states.len();
            all_states.push(State::new(id, accepting_states.contains(id)));
            state_map.insert(id, index);
            index
        }
    }

    // Construct an automaton based on the automaton name, initial state id, the complete set of
    // transitions (from, to, range), and the set of accepting states
    fn new(
        automaton_name: &str,
        initial_state_id: &str,
        transitions: Vec<(&str, &str, (u32, u32))>,
        accepting_states: Vec<&str>,
    ) -> Automaton {
        let accepting_states: HashSet<_> = accepting_states.into_iter().collect();
        let mut all_states: Vec<State> = Vec::new();
        let mut state_map: HashMap<&str, StateId> = HashMap::new();

        let initial_state = Self::get_or_create_state(
            initial_state_id,
            &mut state_map,
            &mut all_states,
            &accepting_states,
        );

        for (from, to, trigger) in transitions {
            let from_id =
                Self::get_or_create_state(from, &mut state_map, &mut all_states, &accepting_states);
            let to_id =
                Self::get_or_create_state(to, &mut state_map, &mut all_states, &accepting_states);
            all_states[from_id]
                .transitions
                .insert(Transition::new(to_id, Trigger::Range(trigger)));
        }

        Automaton {
            name: automaton_name.to_owned(),
            initial_state,
            all_states,
        }
    }

    pub fn empty_automaton() -> Automaton {
        Automaton {
            name: "empty_automaton".to_owned(),
            initial_state: 0,
            all_states: vec![State::new("initial", false)],
        }
    }

    /// Checks whether the automaton is non-deterministic (contains epsilon transitions,
    /// overlapping ranges, or incomplete symbol coverage).
    pub fn is_nfa(&self) -> bool {
        for state in &self.all_states {
            let mut ranges = Vec::new();
            for transition in &state.transitions {
                match transition.trigger {
                    Trigger::Range(range) => {
                        ranges.push(range);
                    }
                    Trigger::Epsilon => {
                        return true;
                    }
                };
            }
            // NFA if the automaton has overlapping ranges on transitions outgoing the same state
            // (non-determinism)
            if has_overlapping_ranges(ranges.clone()) {
                return true;
            }
            // NFA if the automaton does not have transitions for every range from 0 to u16::MAX
            if !missing_ranges(&ranges, 0, u32::MAX).is_empty() {
                return true;
            }
        }
        false
    }

    /// Returns a reference to the state with the given `state_id`.
    pub fn get_state(&self, state_id: StateId) -> &State {
        &self.all_states[state_id]
    }

    /// Returns a set of outgoing transitions from the specified state.
    pub fn get_state_transitions(&self, state_id: StateId) -> BTreeSet<Transition> {
        let state = &self.all_states[state_id];
        state.transitions.clone()
    }

    /// Returns all accepting states in the automaton.
    pub fn get_accepting_states(&self) -> Vec<State> {
        let mut states = Vec::new();
        for state in &self.all_states {
            if state.accept {
                states.push(state.clone());
            }
        }
        states
    }

    /// Returns an iterator over all transitions as `(source_state, destination_state, trigger)` triples.
    pub fn get_all_transitions(&self) -> impl Iterator<Item = (State, State, Trigger)> + use<'_> {
        self.all_states.iter().flat_map(|state| {
            state.transitions.iter().map(|transition| {
                (
                    state.clone(),
                    self.get_state(transition.to).clone(),
                    transition.trigger.clone(),
                )
            })
        })
    }

    /// Returns a copy of the automaton's initial state.
    pub fn get_initial_state(&self) -> State {
        self.get_state(self.initial_state).clone()
    }

    // Returns the set of states the can be reached by every state in the automaton following any
    // number of Epsilon transitions
    fn epsilon_closure(start: &BTreeSet<StateId>, a: &Automaton) -> BTreeSet<StateId> {
        let mut stack: Vec<StateId> = start.iter().copied().collect();
        let mut closure = start.clone();

        while let Some(s) = stack.pop() {
            for t in &a.all_states[s].transitions {
                if t.trigger == Trigger::Epsilon && !closure.contains(&t.to) {
                    closure.insert(t.to);
                    stack.push(t.to);
                }
            }
        }

        closure
    }

    fn partition_ranges(edges: &Vec<(u32, u32, StateId)>) -> Vec<((u32, u32), BTreeSet<StateId>)> {
        if edges.is_empty() {
            return Vec::new();
        }

        let mut points: Vec<u64> = Vec::new();

        for (l, r, _) in edges {
            points.push(*l as u64);
            points.push(*r as u64 + 1);
        }

        points.sort();
        points.dedup();

        let mut result = Vec::new();

        for w in points.windows(2) {
            let a = w[0] as u32;
            let b = (w[1] - 1) as u32;

            let mut dests = BTreeSet::new();

            for (l, r, to) in edges {
                if *l <= a && *r >= b {
                    dests.insert(*to);
                }
            }
            if !dests.is_empty() {
                result.push(((a, b), dests));
            }
        }

        result
    }

    /// Converts a nondeterministic finite automaton (NFA) into an equivalent complete DFA
    /// using subset construction.
    pub fn determinize(nfa: &Automaton) -> Automaton {
        let mut new_states: Vec<State> = Vec::new();
        let mut state_map: HashMap<BTreeSet<StateId>, StateId> = HashMap::new();
        let mut queue = VecDeque::new();

        let mut init = BTreeSet::new();
        init.insert(nfa.initial_state);
        let init_closure = Automaton::epsilon_closure(&init, nfa);

        let init_accept = init_closure.iter().any(|&s| nfa.all_states[s].accept);

        new_states.push(State {
            id: "D0".to_owned(),
            accept: init_accept,
            transitions: BTreeSet::new(),
        });

        state_map.insert(init_closure.clone(), 0);
        queue.push_back(init_closure);

        // Subset construction
        while let Some(current_set) = queue.pop_front() {
            let current_id = state_map[&current_set];
            let mut edges: Vec<(u32, u32, StateId)> = Vec::new();

            for s in &current_set {
                for t in &nfa.all_states[*s].transitions {
                    if let Trigger::Range((l, r)) = t.trigger {
                        edges.push((l, r, t.to));
                    }
                }
            }

            let parts = Automaton::partition_ranges(&edges);

            for ((l, r), dests) in parts {
                let closure = Automaton::epsilon_closure(&dests, nfa);

                let dest_id = if let Some(id) = state_map.get(&closure) {
                    *id
                } else {
                    let new_id = new_states.len();
                    let accept = closure.iter().any(|&s| nfa.all_states[s].accept);

                    new_states.push(State {
                        id: format!("D{}", new_id),
                        accept,
                        transitions: BTreeSet::new(),
                    });

                    state_map.insert(closure.clone(), new_id);
                    queue.push_back(closure);
                    new_id
                };

                new_states[current_id].transitions.insert(Transition {
                    to: dest_id,
                    trigger: Trigger::Range((l, r)),
                });
            }
        }

        // Sink state and complete transitions
        let sink_id = new_states.len();

        new_states.push(State {
            id: format!("D{}", sink_id),
            accept: false,
            transitions: BTreeSet::new(),
        });

        for state in new_states.iter_mut().take(sink_id) {
            let covered: Vec<(u32, u32)> = state
                .transitions
                .iter()
                .filter_map(|t| match t.trigger {
                    Trigger::Range(range) => Some(range),
                    Trigger::Epsilon => None,
                })
                .collect();

            for (l, r) in missing_ranges(&covered, 0, u32::MAX) {
                state.transitions.insert(Transition {
                    to: sink_id,
                    trigger: Trigger::Range((l, r)),
                });
            }
        }

        // Sink loop
        new_states[sink_id].transitions.insert(Transition {
            to: sink_id,
            trigger: Trigger::Range((0, u32::MAX)),
        });

        Automaton {
            name: format!("{}_dfa", nfa.name),
            all_states: new_states,
            initial_state: 0,
        }
    }

    /// Returns an equivalent automaton without epsilon transitions: each state
    /// takes over the range transitions and acceptance of its epsilon closure.
    pub fn epsilon_eliminate(&self) -> Automaton {
        let closures = self.state_closures();
        let all_states = self
            .all_states
            .iter()
            .enumerate()
            .map(|(i, state)| {
                let mut accept = false;
                let mut transitions = BTreeSet::new();
                for &c in &closures[i] {
                    accept |= self.all_states[c].accept;
                    for t in &self.all_states[c].transitions {
                        if let Trigger::Range(_) = t.trigger {
                            transitions.insert(t.clone());
                        }
                    }
                }
                State {
                    id: state.id.clone(),
                    accept,
                    transitions,
                }
            })
            .collect();

        Automaton {
            name: self.name.clone(),
            all_states,
            initial_state: self.initial_state,
        }
    }

    // The transition sets are rebuilt from scratch: removing and re-inserting
    // transitions one at a time can collapse a shifted transition with a
    // not-yet-shifted one, losing it
    fn shift_states(states: Vec<State>, shift: usize) -> Vec<State> {
        let mut new_states = states;
        for state in &mut new_states {
            state.transitions = state
                .transitions
                .iter()
                .map(|t| Transition {
                    to: t.to + shift,
                    trigger: t.trigger.clone(),
                })
                .collect();
        }
        new_states
    }

    /// Constructs an automaton from an AST regular expression term.
    pub fn create_from_regex_operators(
        pool: &mut dyn TermPool,
        t: &Rc<Term>,
    ) -> Result<Automaton, CheckerError> {
        match t.as_ref() {
            Term::Op(Operator::ReKleeneClosure, r) => {
                let r = r.first().unwrap();
                let a = Self::create_from_regex_operators(pool, r)?;
                let mut states = a.clone().all_states;

                let new_init_id = states.len();

                // handle initial state
                states.push(State {
                    id: "new_init".to_owned(),
                    accept: true,
                    transitions: BTreeSet::from([Transition {
                        to: a.initial_state,
                        trigger: Trigger::Epsilon,
                    }]),
                });

                // handle accepting states
                for state in states.iter_mut().take(a.all_states.len()) {
                    if state.accept {
                        state.transitions.insert(Transition {
                            to: a.initial_state,
                            trigger: Trigger::Epsilon,
                        });
                    }
                }

                Ok(Automaton {
                    name: "re_kleene_closure".to_owned(),
                    all_states: states,
                    initial_state: new_init_id,
                })
            }
            Term::Op(Operator::ReKleeneCross, r) => {
                let r = r.first().unwrap();
                let kleene_closure = pool.add(Term::Op(Operator::ReKleeneClosure, vec![r.clone()]));
                let equiv = pool.add(Term::Op(
                    Operator::ReConcat,
                    vec![r.clone(), kleene_closure],
                ));
                Ok(Self::create_from_regex_operators(pool, &equiv)?)
            }
            Term::Op(Operator::ReOption, r) => {
                // (re.opt r) = (re.union r (str.to_re ""))
                let r = r.first().unwrap();
                let empty_string = pool.add(Term::new_string(""));
                let empty_re = pool.add(Term::Op(Operator::StrToRe, vec![empty_string]));
                let equiv = pool.add(Term::Op(Operator::ReUnion, vec![r.clone(), empty_re]));
                Ok(Self::create_from_regex_operators(pool, &equiv)?)
            }
            Term::Op(Operator::ReDiff, args) if args.len() >= 2 => {
                // (re.diff a b c ...) = (re.inter a (re.comp b) (re.comp c) ...)
                let mut inter_args = vec![args[0].clone()];
                for b in &args[1..] {
                    inter_args.push(pool.add(Term::Op(Operator::ReComplement, vec![b.clone()])));
                }
                let equiv = pool.add(Term::Op(Operator::ReIntersection, inter_args));
                Ok(Self::create_from_regex_operators(pool, &equiv)?)
            }
            Term::Op(Operator::ReConcat, r) => {
                let mut automatons: Vec<Automaton> = Vec::new();
                for regex in r {
                    let a = Self::create_from_regex_operators(pool, regex)?;
                    if !operations::has_reachable_accepting_state(&a) {
                        // A component with an empty language makes the whole
                        // concatenation empty
                        return Ok(Automaton {
                            name: "re_concat".to_owned(),
                            all_states: vec![State {
                                id: "init".to_owned(),
                                accept: false,
                                transitions: BTreeSet::new(),
                            }],
                            initial_state: 0,
                        });
                    }
                    automatons.push(a);
                }

                let mut automatons = automatons.into_iter();
                let mut result = automatons.next().unwrap();

                for next in automatons {
                    let offset = result.all_states.len();
                    let next_states = Self::shift_states(next.all_states, offset);
                    for state in &mut result.all_states {
                        if state.accept {
                            state.accept = false;
                            state.transitions.insert(Transition {
                                to: next.initial_state + offset,
                                trigger: Trigger::Epsilon,
                            });
                        }
                    }
                    result.all_states.extend(next_states);
                }

                result.name = "re_concat".to_owned();
                Ok(result)
            }
            Term::Op(Operator::StrToRe, s) => {
                let s = s.first().unwrap();
                let Term::Const(Constant::String(s)) = s.as_ref() else {
                    return Err(StringError::ExpectedStringConstantInsideStrToRe(s.clone()).into());
                };

                let characters: Vec<char> = s.chars().collect();
                if characters.is_empty() {
                    return Ok(Automaton {
                        name: "str_to_re".to_owned(),
                        all_states: vec![State {
                            id: "init".to_owned(),
                            accept: true,
                            transitions: BTreeSet::new(),
                        }],
                        initial_state: 0,
                    });
                }

                let first_char = characters.first().unwrap();
                let offset = 1;

                let mut states: Vec<State> = Vec::new();
                states.push(State {
                    id: "init".to_owned(),
                    accept: false,
                    transitions: BTreeSet::from([Transition {
                        to: 1,
                        trigger: Trigger::Range((*first_char as u32, *first_char as u32)),
                    }]),
                });

                for (index, c) in characters.iter().enumerate() {
                    let mut transitions = BTreeSet::new();
                    if index != characters.len() - 1 {
                        let next_char = characters[index + 1];
                        transitions.insert(Transition {
                            to: index + offset + 1,
                            trigger: Trigger::Range((next_char as u32, next_char as u32)),
                        });
                    }
                    states.push(State {
                        id: c.to_string(),
                        accept: index == characters.len() - 1,
                        transitions,
                    });
                }

                Ok(Automaton {
                    name: "str_to_re".to_owned(),
                    all_states: states,
                    initial_state: 0,
                })
            }
            Term::Op(Operator::ReAllChar, _) => Ok(Automaton {
                name: "re_allchar".to_owned(),
                all_states: vec![
                    State {
                        id: "init".to_owned(),
                        accept: false,
                        transitions: BTreeSet::from([Transition {
                            to: 1,
                            trigger: Trigger::Range((0, u32::MAX)),
                        }]),
                    },
                    State {
                        id: "accept".to_owned(),
                        accept: true,
                        transitions: BTreeSet::new(),
                    },
                ],
                initial_state: 0,
            }),
            Term::Op(Operator::ReAll, _) => Ok(Automaton {
                name: "re_all".to_owned(),
                all_states: vec![State {
                    id: "init".to_owned(),
                    accept: true,
                    transitions: BTreeSet::from([Transition {
                        to: 0,
                        trigger: Trigger::Range((0, u32::MAX)),
                    }]),
                }],
                initial_state: 0,
            }),
            Term::Op(Operator::ReComplement, r) => {
                let r = r.first().unwrap();
                let a = Self::create_from_regex_operators(pool, r)?;
                // complementation genuinely requires a (complete) DFA
                let dfa = if a.is_nfa() {
                    Automaton::determinize(&a)
                } else {
                    a
                };
                Ok(operations::complement(dfa))
            }
            Term::Op(Operator::ReRange, args) => {
                let c1_term = &args[0];
                let c2_term = &args[1];
                let Term::Const(Constant::String(s1)) = c1_term.as_ref() else {
                    unreachable!()
                };
                let Term::Const(Constant::String(s2)) = c2_term.as_ref() else {
                    unreachable!()
                };
                let mut s1_chars = s1.chars();
                let mut s2_chars = s2.chars();
                let (Some(c1), None) = (s1_chars.next(), s1_chars.next()) else {
                    return Ok(Automaton::empty_automaton());
                };
                let (Some(c2), None) = (s2_chars.next(), s2_chars.next()) else {
                    return Ok(Automaton::empty_automaton());
                };
                if c1 > c2 {
                    return Ok(Automaton::empty_automaton());
                }
                Ok(Automaton {
                    name: "re_range".to_owned(),
                    all_states: vec![
                        State {
                            id: "init".to_owned(),
                            accept: false,
                            transitions: BTreeSet::from([Transition {
                                to: 1,
                                trigger: Trigger::Range((c1 as u32, c2 as u32)),
                            }]),
                        },
                        State {
                            id: "accept".to_owned(),
                            accept: true,
                            transitions: BTreeSet::new(),
                        },
                    ],
                    initial_state: 0,
                })
            }
            Term::Op(Operator::ReNone, _) => Ok(Automaton {
                name: "re_none".to_owned(),
                all_states: vec![State {
                    id: "init".to_owned(),
                    accept: false,
                    transitions: BTreeSet::from([Transition {
                        to: 0,
                        trigger: Trigger::Range((0, u32::MAX)),
                    }]),
                }],
                initial_state: 0,
            }),
            Term::Op(Operator::ReIntersection, inter) => {
                // the product construction works directly on NFAs once
                // their epsilon transitions are eliminated, so the
                // components need not be determinized
                let mut components = Vec::new();
                for re in inter {
                    let nfa = Self::create_from_regex_operators(pool, re)?;
                    components.push(nfa.epsilon_eliminate());
                }
                let mut components = components.into_iter();
                let mut res = components.next().unwrap();
                for comp in components {
                    res = operations::intersection(res, comp)?;
                }
                Ok(res)
            }
            Term::Op(Operator::ReUnion, uni) => {
                let mut automata: Vec<Automaton> = Vec::new();
                for re in uni {
                    automata.push(Self::create_from_regex_operators(pool, re)?);
                }

                let mut states: Vec<State> = Vec::new();
                let mut transitions: BTreeSet<Transition> = BTreeSet::new();
                let mut index = 1;
                for automaton in automata {
                    states.extend(Self::shift_states(
                        automaton.all_states.clone(),
                        states.len() + 1,
                    ));
                    transitions.insert(Transition {
                        // the initial state need not be the automaton's first
                        // state (e.g. Kleene closures append theirs last)
                        to: index + automaton.initial_state,
                        trigger: Trigger::Epsilon,
                    });
                    index += automaton.all_states.len();
                }

                states.insert(
                    0,
                    State {
                        id: "init".to_owned(),
                        accept: false,
                        transitions,
                    },
                );

                Ok(Automaton {
                    name: "re_union".to_owned(),
                    all_states: states,
                    initial_state: 0,
                })
            }
            Term::Const(Constant::RegLan(_, a)) => Ok(a.clone()),
            _ => Err(StringError::UnexpectedTermOnAutomatonConversion(t.clone()).into()),
        }
    }

    /// Computes the epsilon closure of every state, as sorted state lists.
    fn state_closures(&self) -> Vec<Vec<StateId>> {
        let n = self.all_states.len();
        // stamped with the state whose closure is being computed, so it needs
        // no clearing between states
        let mut visited = vec![usize::MAX; n];
        (0..n)
            .map(|start| {
                let mut closure = vec![start];
                visited[start] = start;
                let mut i = 0;
                while i < closure.len() {
                    let s = closure[i];
                    i += 1;
                    for t in &self.all_states[s].transitions {
                        if t.trigger == Trigger::Epsilon && visited[t.to] != start {
                            visited[t.to] = start;
                            closure.push(t.to);
                        }
                    }
                }
                closure.sort_unstable();
                closure
            })
            .collect()
    }

    /// Advances the reachable-state set by one input symbol, epsilon-closing
    /// the result through the precomputed per-state closures.
    fn step(&self, current: &[StateId], symbol: u32, closures: &[Vec<StateId>]) -> Vec<StateId> {
        let mut next = Vec::new();
        for &state in current {
            for t in &self.all_states[state].transitions {
                if let Trigger::Range((l, r)) = t.trigger {
                    if symbol >= l && symbol <= r {
                        next.extend_from_slice(&closures[t.to]);
                    }
                }
            }
        }
        next.sort_unstable();
        next.dedup();
        next
    }

    /// Checks membership by simulating the NFA directly: the set of reachable
    /// states (kept as a sorted list, so we only store the active states
    /// representing the possible paths for the current input prefix, rather than
    /// a bitset whose size scales with the total number of states) is advanced per
    /// input character and epsilon-closed using per-state closures computed once.
    /// This avoids the potentially exponential subset construction of
    /// determinization.
    ///
    /// Transitions are memoized per (state set, symbol class), where the
    /// classes partition the alphabet by the range endpoints occurring in the
    /// automaton — a lazy DFA that only materializes reachable subsets, making
    /// long inputs cost a hash lookup per character.
    pub fn accepts(&self, s: &str) -> bool {
        // bounds the total number of state ids stored in the memo table
        const MEMO_ELEMS_LIMIT: usize = 1 << 20;

        let closures = self.state_closures();

        // Symbols between two consecutive boundaries trigger exactly the same
        // transitions in every state
        let bounds: BTreeSet<u64> = self
            .all_states
            .iter()
            .flat_map(|state| state.transitions.iter())
            .filter_map(|t| match t.trigger {
                Trigger::Range((l, r)) => Some([l as u64, r as u64 + 1]),
                Trigger::Epsilon => None,
            })
            .flatten()
            .collect();

        let mut memo: HashMap<(Vec<StateId>, usize), Vec<StateId>> = HashMap::new();
        let mut memo_elems = 0;

        let mut current = closures[self.initial_state].clone();
        for c in s.chars() {
            let symbol = c as u32;
            let class = bounds.range(..=symbol as u64).count();
            let next = if let Some(n) = memo.get(&(current.clone(), class)) {
                n.clone()
            } else {
                let computed = self.step(&current, symbol, &closures);
                if memo_elems < MEMO_ELEMS_LIMIT {
                    memo_elems += current.len() + computed.len();
                    memo.insert((current, class), computed.clone());
                }
                computed
            };
            if next.is_empty() {
                return false;
            }
            current = next;
        }

        current.iter().any(|&s| self.all_states[s].accept)
    }
}

impl fmt::Display for Automaton {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "automaton {} {{", self.name)?;
        writeln!(f, "  init {};", self.all_states[self.initial_state].id)?;
        for state in &self.all_states {
            for transition in &state.transitions {
                let target = &self.all_states[transition.to];
                match &transition.trigger {
                    Trigger::Epsilon => {
                        writeln!(f, "  {} -> {} [ε];", state.id, target.id)?;
                    }
                    Trigger::Range((l, r)) => {
                        writeln!(f, "  {} -> {} [{}, {}];", state.id, target.id, l, r)?;
                    }
                }
            }
        }
        for state in &self.all_states {
            if state.accept {
                writeln!(f, "  accepting {};", state.id)?;
            }
        }
        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    fn make_state(id: StateId, transitions: &[(StateId, Trigger)], accept: bool) -> State {
        State {
            id: id.to_string(),
            accept,
            transitions: transitions
                .iter()
                .cloned()
                .map(|(to, trigger)| Transition { to, trigger })
                .collect(),
        }
    }

    fn make_aut(states: Vec<State>) -> Automaton {
        Automaton {
            name: "test".to_owned(),
            all_states: states,
            initial_state: 0,
        }
    }

    fn set(v: &[usize]) -> BTreeSet<usize> {
        v.iter().copied().collect()
    }

    #[test]
    fn test_epsilon_closure_single_state_no_epsilon() {
        let s0 = make_state(0, &[], false);

        let aut = make_aut(vec![s0]);

        let start = set(&[0]);
        let res = Automaton::epsilon_closure(&start, &aut);

        assert_eq!(res, set(&[0]));
    }

    #[test]
    fn test_epsilon_closure_simple_epsilon() {
        let s0 = make_state(0, &[(1, Trigger::Epsilon)], false);
        let s1 = make_state(1, &[], false);

        let aut = make_aut(vec![s0, s1]);

        let start = set(&[0]);
        let res = Automaton::epsilon_closure(&start, &aut);

        assert_eq!(res, set(&[0, 1]));
    }

    #[test]
    fn test_epsilon_closure_chain() {
        let s0 = make_state(0, &[(1, Trigger::Epsilon)], false);
        let s1 = make_state(1, &[(2, Trigger::Epsilon)], false);
        let s2 = make_state(2, &[], false);

        let aut = make_aut(vec![s0, s1, s2]);

        let start = set(&[0]);
        let res = Automaton::epsilon_closure(&start, &aut);

        assert_eq!(res, set(&[0, 1, 2]));
    }

    #[test]
    fn test_epsilon_closure_cycle() {
        let s0 = make_state(0, &[(1, Trigger::Epsilon)], false);
        let s1 = make_state(1, &[(0, Trigger::Epsilon)], false);

        let aut = make_aut(vec![s0, s1]);

        let start = set(&[0]);
        let res = Automaton::epsilon_closure(&start, &aut);

        assert_eq!(res, set(&[0, 1]));
    }

    #[test]
    fn test_epsilon_closure_branching() {
        let s0 = make_state(0, &[(1, Trigger::Epsilon), (2, Trigger::Epsilon)], false);
        let s1 = make_state(1, &[], false);
        let s2 = make_state(2, &[], false);

        let aut = make_aut(vec![s0, s1, s2]);

        let start = set(&[0]);
        let res = Automaton::epsilon_closure(&start, &aut);

        assert_eq!(res, set(&[0, 1, 2]));
    }

    #[test]
    fn epsilon_closure_multiple_start_states() {
        let s0 = make_state(0, &[(2, Trigger::Epsilon)], false);
        let s1 = make_state(1, &[(3, Trigger::Epsilon)], false);
        let s2 = make_state(2, &[], false);
        let s3 = make_state(3, &[], false);

        let aut = make_aut(vec![s0, s1, s2, s3]);

        let start = set(&[0, 1]);
        let res = Automaton::epsilon_closure(&start, &aut);

        assert_eq!(res, set(&[0, 1, 2, 3]));
    }

    #[test]
    fn test_epsilon_closure_ignores_non_epsilon() {
        let s0 = make_state(
            0,
            &[(1, Trigger::Epsilon), (2, Trigger::Range((0, 10)))],
            false,
        );
        let s1 = make_state(1, &[], false);
        let s2 = make_state(2, &[], false);

        let aut = make_aut(vec![s0, s1, s2]);

        let start = set(&[0]);
        let res = Automaton::epsilon_closure(&start, &aut);

        assert_eq!(res, set(&[0, 1]));
    }

    #[test]
    fn test_epsilon_closure_complex_graph() {
        // 0 ->ε 1 ->ε 3
        // 0 ->ε 2 ->ε 3
        // 3 ->ε 4
        let s0 = make_state(0, &[(1, Trigger::Epsilon), (2, Trigger::Epsilon)], false);
        let s1 = make_state(1, &[(3, Trigger::Epsilon)], false);
        let s2 = make_state(2, &[(3, Trigger::Epsilon)], false);
        let s3 = make_state(3, &[(4, Trigger::Epsilon)], false);
        let s4 = make_state(4, &[], false);

        let aut = make_aut(vec![s0, s1, s2, s3, s4]);

        let start = set(&[0]);
        let res = Automaton::epsilon_closure(&start, &aut);

        assert_eq!(res, set(&[0, 1, 2, 3, 4]));
    }

    #[test]
    fn test_is_nfa_by_epsilon_transition() {
        let s0 = make_state(
            0,
            &[(1, Trigger::Range((0, 255))), (2, Trigger::Epsilon)],
            false,
        );
        let s1 = make_state(1, &[(3, Trigger::Range((0, 255)))], false);
        let s2 = make_state(2, &[(3, Trigger::Range((0, 255)))], false);
        let s3 = make_state(3, &[(3, Trigger::Range((0, 255)))], false);
        let a = Automaton {
            name: "a".into(),
            all_states: vec![s0, s1, s2, s3],
            initial_state: 0,
        };
        assert!(a.is_nfa());
    }

    #[test]
    fn test_is_nfa_by_incomplete_transition_table() {
        let a = Automaton::new(
            "a",
            "q0",
            vec![
                ("q0", "q1", (98, 98)),
                ("q0", "q3", (0, 97)),
                ("q0", "q3", (100, 255)),
                ("q1", "q3", (0, 255)),
                ("q3", "q3", (0, 255)),
            ],
            vec!["q1"],
        );
        assert!(a.is_nfa());
    }

    #[test]
    fn test_is_nfa_by_overlapping_transitions() {
        let a = Automaton::new(
            "a",
            "q0",
            vec![
                ("q0", "q1", (98, 98)),
                ("q0", "q2", (99, 99)),
                ("q0", "q3", (0, 97)),
                ("q0", "q3", (99, 255)),
                ("q1", "q3", (0, 255)),
                ("q2", "q3", (0, 255)),
                ("q3", "q3", (0, 255)),
            ],
            vec!["q1"],
        );
        assert!(a.is_nfa());
    }

    #[test]
    fn test_is_dfa() {
        let a = Automaton::new(
            "a",
            "q0",
            vec![
                ("q0", "q1", (98, 98)),
                ("q0", "q3", (0, 97)),
                ("q0", "q3", (99, u32::MAX)),
                ("q1", "q3", (0, u32::MAX)),
                ("q3", "q3", (0, u32::MAX)),
            ],
            vec!["q1"],
        );
        assert!(!a.is_nfa());
    }

    #[test]
    fn test_determinize_simple_conversion() {
        let s0 = make_state(0, &[(1, Trigger::Range((97, 97)))], false);
        let s1 = make_state(1, &[(2, Trigger::Range((98, 98)))], false);
        let s2 = make_state(2, &[(3, Trigger::Range((99, 99)))], false);
        let s3 = make_state(3, &[], true);
        let nfa = Automaton {
            name: "nfa".into(),
            all_states: vec![s0, s1, s2, s3],
            initial_state: 0,
        };

        let dfa = Automaton::determinize(&nfa);

        assert!(!dfa.is_nfa());
    }

    #[test]
    fn test_determinize_remove_epsilon_transitions() {
        let s0 = make_state(0, &[(1, Trigger::Epsilon)], false);
        let s1 = make_state(1, &[(2, Trigger::Range((97, 98)))], false);
        let s2 = make_state(
            2,
            &[(3, Trigger::Range((97, 98))), (1, Trigger::Range((98, 99)))],
            false,
        );
        let s3 = make_state(3, &[], false);
        let nfa = Automaton {
            name: "nfa".into(),
            all_states: vec![s0, s1, s2, s3],
            initial_state: 0,
        };

        let dfa = Automaton::determinize(&nfa);

        assert!(!dfa.is_nfa());
    }

    #[test]
    fn test_determinize_add_sink_state_for_missing_ranges() {
        let s0 = make_state(0, &[(1, Trigger::Range((97, 97)))], false);
        let s1 = make_state(1, &[(2, Trigger::Range((98, 98)))], false);
        let s2 = make_state(2, &[(3, Trigger::Range((99, 99)))], false);
        let s3 = make_state(3, &[], false);
        let nfa = Automaton {
            name: "nfa".into(),
            all_states: vec![s0, s1, s2, s3],
            initial_state: 0,
        };

        let dfa = Automaton::determinize(&nfa);

        assert!(!dfa.is_nfa());
    }

    #[test]
    fn test_determinize_handle_overlapping_ranges() {
        let s0 = make_state(
            0,
            &[
                (3, Trigger::Range((0, 96))),
                (1, Trigger::Range((97, 98))),
                (2, Trigger::Range((98, 99))),
                (3, Trigger::Range((100, 255))),
            ],
            false,
        );
        let s1 = make_state(1, &[(3, Trigger::Range((0, 255)))], false);
        let s2 = make_state(2, &[(3, Trigger::Range((0, 255)))], false);
        let s3 = make_state(3, &[(3, Trigger::Range((0, 255)))], false);
        let nfa = Automaton {
            name: "nfa".into(),
            all_states: vec![s0, s1, s2, s3],
            initial_state: 0,
        };

        let dfa = Automaton::determinize(&nfa);

        assert!(!dfa.is_nfa());
    }

    #[test]
    fn test_accepts() {
        let s0 = make_state(0, &[(1, Trigger::Range((97, 97)))], false);
        let s1 = make_state(1, &[(2, Trigger::Range((98, 98)))], false);
        let s2 = make_state(2, &[(3, Trigger::Range((99, 99)))], false);
        let s3 = make_state(3, &[], true);
        let aut = Automaton {
            name: "test_accepts".into(),
            all_states: vec![s0, s1, s2, s3],
            initial_state: 0,
        };

        assert!(aut.accepts("abc"));
        assert!(!aut.accepts("ab"));
        assert!(!aut.accepts("abcd"));
        assert!(!aut.accepts(""));
    }

    fn accepts_regex(regex: &str, s: &str) -> bool {
        use crate::{ast::pool::PrimitivePool, parser::tests::parse_term};
        let mut pool = PrimitivePool::new();
        let term = parse_term(&mut pool, regex);
        let aut = Automaton::create_from_regex_operators(&mut pool, &term).unwrap();
        aut.accepts(s)
    }

    #[test]
    fn test_create_from_regex_operators_concat() {
        // concatenations with more than two components
        assert!(accepts_regex(
            r#"(re.++ (str.to_re "a") (str.to_re "b") (str.to_re "c"))"#,
            "abc"
        ));
        // a union or star in a non-first position of a concatenation
        assert!(accepts_regex(
            r#"(re.++ (str.to_re "a") (re.union (str.to_re "b") (str.to_re "c")))"#,
            "ab"
        ));
        assert!(accepts_regex(
            r#"(re.++ (str.to_re "a") (re.union (str.to_re "b") (str.to_re "c")))"#,
            "ac"
        ));
        assert!(!accepts_regex(
            r#"(re.++ (str.to_re "a") (re.union (str.to_re "b") (str.to_re "c")))"#,
            "ad"
        ));
        assert!(accepts_regex(
            r#"(re.++ (str.to_re "a") (re.* (str.to_re "x")) (str.to_re "b"))"#,
            "ab"
        ));
        assert!(accepts_regex(
            r#"(re.++ (str.to_re "a") (re.* (str.to_re "x")) (str.to_re "b"))"#,
            "axxb"
        ));
        assert!(!accepts_regex(
            r#"(re.++ (str.to_re "a") (re.* (str.to_re "x")) (str.to_re "b"))"#,
            "axx"
        ));
        // a component with an empty language empties the whole concatenation
        assert!(!accepts_regex(
            r#"(re.++ (str.to_re "a") re.none (str.to_re "b"))"#,
            "ab"
        ));
    }

    #[test]
    fn test_accepts_without_determinization() {
        // pathological cases for subset construction, cheap for direct
        // simulation: chains of re.allchar and unions of overlapping ranges
        let allchar_chain = format!("(re.++ {})", "re.allchar ".repeat(20));
        assert!(accepts_regex(&allchar_chain, &"x".repeat(20)));
        assert!(!accepts_regex(&allchar_chain, &"x".repeat(19)));
        assert!(!accepts_regex(&allchar_chain, ""));

        let union_star = r#"(re.* (re.union (re.range "0" "9") (re.range "A" "Z") (re.range "a" "z") (str.to_re "-")))"#;
        assert!(accepts_regex(union_star, &"a0-Z".repeat(500)));
        assert!(!accepts_regex(union_star, "a0_Z"));
    }

    #[test]
    fn test_create_from_regex_operators_union_of_composites() {
        // union components whose initial state is not their first state
        let regex = r#"(re.union (re.* (str.to_re "x")) (str.to_re "y"))"#;
        assert!(accepts_regex(regex, ""));
        assert!(accepts_regex(regex, "xx"));
        assert!(accepts_regex(regex, "y"));
        assert!(!accepts_regex(regex, "xy"));
    }

    #[test]
    fn test_create_from_regex_operators_inter_and_comp() {
        // intersection of NFAs with epsilon transitions (stars), without
        // determinizing the components
        let inter = r#"(re.inter (re.* (str.to_re "ab")) (re.++ (str.to_re "a") (re.* (str.to_re "ba")) (str.to_re "b")))"#;
        assert!(accepts_regex(inter, "ab"));
        assert!(accepts_regex(inter, "abab"));
        assert!(!accepts_regex(inter, "aba"));
        assert!(!accepts_regex(inter, ""));

        let empty = r#"(re.inter (str.to_re "a") (str.to_re "b"))"#;
        assert!(!accepts_regex(empty, "a"));
        assert!(!accepts_regex(empty, "b"));

        let comp = r#"(re.comp (re.* (str.to_re "a")))"#;
        assert!(accepts_regex(comp, "b"));
        assert!(accepts_regex(comp, "ab"));
        assert!(!accepts_regex(comp, ""));
        assert!(!accepts_regex(comp, "aaa"));
    }

    #[test]
    fn test_create_from_regex_operators_opt_and_diff() {
        let opt = r#"(re.++ (str.to_re "a") (re.opt (str.to_re "x")) (str.to_re "b"))"#;
        assert!(accepts_regex(opt, "ab"));
        assert!(accepts_regex(opt, "axb"));
        assert!(!accepts_regex(opt, "axxb"));

        let diff = r#"(re.diff (re.* (str.to_re "a")) (str.to_re "aa"))"#;
        assert!(accepts_regex(diff, "a"));
        assert!(!accepts_regex(diff, "aa"));
        assert!(accepts_regex(diff, "aaa"));
    }

    #[test]
    fn test_create_from_regex_operators_range() {
        // valid ranges
        assert!(accepts_regex(r#"(re.range "a" "c")"#, "a"));
        assert!(accepts_regex(r#"(re.range "a" "c")"#, "b"));
        assert!(accepts_regex(r#"(re.range "a" "c")"#, "c"));
        assert!(!accepts_regex(r#"(re.range "a" "c")"#, "d"));
        assert!(!accepts_regex(r#"(re.range "a" "c")"#, ""));
        assert!(!accepts_regex(r#"(re.range "a" "c")"#, "ab"));

        // empty range: c1 > c2
        assert!(!accepts_regex(r#"(re.range "z" "a")"#, "a"));
        assert!(!accepts_regex(r#"(re.range "z" "a")"#, "z"));
        assert!(!accepts_regex(r#"(re.range "z" "a")"#, ""));

        // empty range: non-singleton arguments
        assert!(!accepts_regex(r#"(re.range "" "a")"#, "a"));
        assert!(!accepts_regex(r#"(re.range "a" "")"#, "a"));
        assert!(!accepts_regex(r#"(re.range "ab" "c")"#, "a"));
        assert!(!accepts_regex(r#"(re.range "a" "bc")"#, "a"));
    }
}
