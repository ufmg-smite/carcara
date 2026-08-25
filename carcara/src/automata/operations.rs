use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use crate::{
    automata::{utils::totalize, State, Transition, Trigger},
    checker::error::CheckerError,
};

use super::{dsu::DSU, utils::intersect_ranges, Automaton, StateId};

/// Determines whether the automaton contains at least one accepting state reachable
/// from the initial state using a breadth-first search (BFS).
pub fn has_reachable_accepting_state(a: &Automaton) -> bool {
    let accepting_states: Vec<_> = a
        .all_states
        .iter()
        .enumerate()
        .filter(|(_, state)| state.accept)
        .collect();
    // Has accepting states? If no, the intersection is empty
    if accepting_states.is_empty() {
        return false;
    }

    // Checking reachability with a BFS. States are marked visited when
    // enqueued, so each is enqueued at most once regardless of how many
    // transitions lead to it
    let mut visited: Vec<bool> = vec![false; a.all_states.len()];
    let mut queue: VecDeque<StateId> = VecDeque::new();

    visited[a.initial_state] = true;
    queue.push_back(a.initial_state);

    while let Some(state) = queue.pop_front() {
        for transition in &a.all_states[state].transitions {
            let next = transition.to;
            if !visited[next] {
                visited[next] = true;
                queue.push_back(next);
            }
        }
    }

    for (state_id, _) in accepting_states {
        if visited[state_id] {
            return true;
        }
    }

    false
}

/// Computes the intersection automaton of two automata `a1` and `a2` using product construction.
pub fn intersection(a1: Automaton, a2: Automaton) -> Result<Automaton, CheckerError> {
    let mut new_states = Vec::new();
    let mut state_map = HashMap::new();
    let mut queue = VecDeque::new();

    let initial_pair = (a1.initial_state, a2.initial_state);
    state_map.insert(initial_pair, 0);
    queue.push_back(initial_pair);

    new_states.push(State {
        id: format!("{:?}", initial_pair),
        accept: a1.get_state(a1.initial_state).accept && a2.get_state(a2.initial_state).accept,
        transitions: BTreeSet::new(),
    });

    while let Some((s1, s2)) = queue.pop_front() {
        let curr_id = state_map[&(s1, s2)];

        for t1 in &a1.get_state(s1).transitions {
            for t2 in &a2.get_state(s2).transitions {
                if let Some(range) = intersect_ranges(t1.trigger.clone(), t2.trigger.clone())? {
                    let dest = (t1.to, t2.to);
                    let next_id = *state_map.entry(dest).or_insert_with(|| {
                        let id = new_states.len();
                        new_states.push(State {
                            id: format!("{:?}", dest),
                            accept: a1.all_states[t1.to].accept && a2.all_states[t2.to].accept,
                            transitions: BTreeSet::new(),
                        });
                        queue.push_back(dest);
                        id
                    });
                    new_states[curr_id]
                        .transitions
                        .insert(Transition::new(next_id, Trigger::Range(range)));
                }
            }
        }
    }

    Ok(Automaton {
        name: format!("({} ∩ {})", a1.name, a2.name),
        all_states: new_states,
        initial_state: 0,
    })
}

/// Tests whether two deterministic finite automata (DFAs) are language-equivalent
/// using the Hopcroft-Karp algorithm.
///
/// Adapted for testing the equivalence of deterministic finite automata (DFAs), as described
/// in the paper "A Linear Algorithm for Testing Equivalence of Finite Automata".
pub fn is_equivalent(a1: Automaton, a2: Automaton) -> bool {
    let offset = a1.all_states.len();

    let accepting_states: Vec<StateId> = a1
        .all_states
        .iter()
        .enumerate()
        .filter_map(|(i, state)| state.accept.then_some(i))
        .chain(
            a2.all_states
                .iter()
                .enumerate()
                .filter_map(|(i, state)| state.accept.then_some(offset + i)),
        )
        .collect();

    // DSU work with StateId's
    let mut dsu = DSU::new(a1.all_states.len() + a2.all_states.len());

    // Stack work with StateId's
    let mut stack: VecDeque<(StateId, StateId)> = VecDeque::new();
    stack.push_front((a1.initial_state, a2.initial_state + offset));

    while let Some((s1, s2)) = stack.pop_front() {
        if accepting_states.contains(&s1) != accepting_states.contains(&s2) {
            return false;
        }

        let s1_transitions = a1.get_state_transitions(s1);
        let s2_transitions = a2.get_state_transitions(s2 - offset);

        // Every symbol in Σ (ranges)
        let ranges: HashSet<_> = HashSet::from_iter(
            s1_transitions
                .iter()
                .map(|t| t.trigger.clone())
                .chain(s2_transitions.iter().map(|t| t.trigger.clone()))
                .collect::<Vec<_>>(),
        );
        for range in &ranges {
            let s1_to: Option<StateId> = s1_transitions
                .iter()
                .find(|t| t.trigger == *range)
                .map(|t| t.to);
            let s2_to: Option<StateId> = s2_transitions
                .iter()
                .find(|t| t.trigger == *range)
                .map(|t| t.to);

            // Both states have transitions for this range
            if !(s1_to.is_some() && s2_to.is_some()) {
                return false;
            }

            let s1_to_dsu_class = dsu.find(s1_to.unwrap());
            let s2_to_dsu_class = dsu.find(s2_to.unwrap() + offset);
            if s1_to_dsu_class != s2_to_dsu_class {
                dsu.union(s1_to_dsu_class, s2_to_dsu_class);
                stack.push_front((s1_to.unwrap(), s2_to.unwrap() + offset));
            }
        }
    }

    true
}

/// Constructs the complement automaton of `a` by making it total and inverting state acceptance.
pub fn complement(a: Automaton) -> Automaton {
    let mut totalized_states = if a.is_nfa() {
        totalize(a.all_states)
    } else {
        a.all_states
    };

    for state in &mut totalized_states {
        state.accept = !state.accept;
    }

    Automaton {
        name: format!("{}_complement", a.name),
        all_states: totalized_states,
        initial_state: a.initial_state,
    }
}

/// Checks whether automaton `p` is a **syntactic subautomaton** of automaton `q`,
/// taking into account **trigger containment (ranges and ε-transitions)**.
///
/// # Definition
/// `p` is considered a subautomaton of `q` if all structural components of `p`
/// are contained in `q`, with transitions compared using **trigger containment**.
///
/// Formally:
/// - `Q_p ⊆ Q_q` (states)
/// - `F_p ⊆ F_q` (accepting states)
/// - `q0_p = q0_q` (initial state)
/// - For every transition `(s, t, α)` in `p`, there exists a transition
///   `(s, t, β)` in `q` such that `β.contains(α)`
///
/// # Important
/// - This is a **syntactic/structural check**, NOT language inclusion.
/// - ε-transitions are treated explicitly and only match other ε-transitions.
/// - Ranges are compared via interval containment.
///
/// # Returns
/// - `true` if `p` is a subautomaton of `q`
/// - `false` otherwise
pub fn is_subautomaton(p: Automaton, q: Automaton) -> bool {
    // Check if states of p are subset of states of q
    let p_states: HashSet<String> = p.all_states.iter().map(|state| state.id.clone()).collect();
    let q_states: HashSet<String> = q.all_states.iter().map(|state| state.id.clone()).collect();
    if !p_states.is_subset(&q_states) {
        return false;
    }

    // Check if accepting states of p are subset of accepting states of q
    let p_accepting_states: HashSet<String> = p
        .get_accepting_states()
        .iter()
        .map(|state| state.id.clone())
        .collect();
    let q_accepting_states: HashSet<String> = q
        .get_accepting_states()
        .iter()
        .map(|state| state.id.clone())
        .collect();
    if !p_accepting_states.is_subset(&q_accepting_states) {
        return false;
    }

    // Check if initial state of p is equal to the initial state of q
    if p.get_initial_state().id != q.get_initial_state().id {
        return false;
    }

    // Check if transitions of p are subset of transitions of q
    let mut q_index: HashMap<(String, String), Vec<Trigger>> = HashMap::new();
    for (s1, s2, trigger) in q.get_all_transitions() {
        q_index
            .entry((s1.id.clone(), s2.id.clone()))
            .or_default()
            .push(trigger.clone());
    }

    // For every transition in p, check if it is covered in q
    for (p_s1, p_s2, p_trig) in p.get_all_transitions() {
        let key = (p_s1.id.clone(), p_s2.id.clone());

        // There must be at least one transition with same (src, dst)
        let Some(q_trigs) = q_index.get(&key) else {
            return false;
        };

        // Check if any trigger in q covers the trigger in p
        let covered = q_trigs.iter().any(|q_trig| q_trig.contains(&p_trig));
        if !covered {
            return false;
        }
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;

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

    #[test]
    fn test_automata_intersection() {
        // a1 accepts only 'a'
        let a1 = Automaton::determinize(&Automaton::new(
            "a1",
            "q0",
            vec![("q0", "q1", (97, 97))],
            vec!["q1"],
        ));
        // a2 accepts 'a' and 'b'
        let a2 = Automaton::determinize(&Automaton::new(
            "a2",
            "p0",
            vec![("p0", "p1", (97, 98))],
            vec!["p1"],
        ));

        let intersection = intersection(a1, a2).unwrap();
        assert!(has_reachable_accepting_state(&intersection));
    }

    #[test]
    fn test_automata_intersection_empty() {
        // accepts only 'a'
        let a1 = Automaton::determinize(&Automaton::new(
            "a1",
            "q0",
            vec![("q0", "q1", (97, 97))],
            vec!["q1"],
        ));
        // accepts only 'b'
        let a2 = Automaton::determinize(&Automaton::new(
            "a2",
            "p0",
            vec![("p0", "p1", (98, 98))],
            vec!["p1"],
        ));

        let intersection = intersection(a1, a2).unwrap();
        assert!(!has_reachable_accepting_state(&intersection));
    }

    #[test]
    fn test_automata_intersection_with_partial_overlap() {
        // accepts a-f
        let a1 = Automaton::determinize(&Automaton::new(
            "a1",
            "q0",
            vec![("q0", "q1", (97, 102))],
            vec!["q1"],
        ));
        // accepts d-z
        let a2 = Automaton::determinize(&Automaton::new(
            "a2",
            "p0",
            vec![("p0", "p1", (100, 122))],
            vec!["p1"],
        ));

        let intersection = intersection(a1, a2).unwrap();
        assert!(has_reachable_accepting_state(&intersection));
    }

    #[test]
    fn test_equiv_automatas() {
        // <a1> -'a'-> a2 -'a'-> [a3] -'a'-> a4 -'a'-> a5 -'a'-> [a6] -\
        //                                 |                           |
        //                                 \------------'a'------------/
        let a1 = Automaton::new(
            "a1",
            "a1",
            vec![
                ("a1", "a2", (97, 97)),
                ("a2", "a3", (97, 97)),
                ("a3", "a4", (97, 97)),
                ("a4", "a5", (97, 97)),
                ("a5", "a6", (97, 97)),
                ("a6", "a4", (97, 97)),
            ],
            vec!["a3", "a6"],
        );

        // > <b1> -'a'-> b2 -'a'-> [b3] -\
        // |                             |
        // \-------------'a'-------------/
        let a2 = Automaton::new(
            "a2",
            "b1",
            vec![
                ("b1", "b2", (97, 97)),
                ("b2", "b3", (97, 97)),
                ("b3", "b1", (97, 97)),
            ],
            vec!["b3"],
        );

        assert!(is_equivalent(a1, a2));
    }

    #[test]
    fn test_unequiv_automatas() {
        // Language: b*a(a ∪ b)*
        let a1 = Automaton::new(
            "a1",
            "q0",
            vec![
                ("q0", "q1", (97, 97)),
                ("q0", "q0", (98, 98)),
                ("q1", "q1", (97, 97)),
                ("q1", "q1", (98, 98)),
            ],
            vec!["q1"],
        );

        // Language: (a ∪ b)*a(a ∪ b)*
        let a2 = Automaton::new(
            "a2",
            "p0",
            vec![
                ("p0", "p1", (97, 97)),
                ("p0", "p0", (98, 98)),
                ("p1", "p1", (97, 97)),
                ("p1", "p0", (98, 98)),
            ],
            vec!["p1"],
        );

        assert!(!is_equivalent(a1, a2));
    }

    // is_subautomaton tests
    #[test]
    fn test_identical_automata() {
        let p = Automaton::new("p", "q0", vec![("q0", "q1", (97, 97))], vec!["q1"]);
        let q = Automaton::new("q", "q0", vec![("q0", "q1", (97, 97))], vec!["q1"]);
        assert!(is_subautomaton(p, q));
    }

    #[test]
    fn test_proper_subautomaton() {
        let p = Automaton::new("p", "q0", vec![("q0", "q1", (97, 97))], vec!["q1"]);
        let q = Automaton::new(
            "q",
            "q0",
            vec![("q0", "q1", (97, 97)), ("q1", "q2", (98, 98))],
            vec!["q1", "q2"],
        );
        assert!(is_subautomaton(p, q));
    }

    #[test]
    fn test_range_in_q_covers_p() {
        let p = Automaton::new(
            "p",
            "q0",
            vec![("q0", "q1", (99, 101))], // c-e
            vec![],
        );

        let q = Automaton::new(
            "q",
            "q0",
            vec![("q0", "q1", (97, 122))], // a-z
            vec![],
        );

        assert!(is_subautomaton(p, q));
    }

    #[test]
    fn test_multiple_transitions_cover() {
        let p = Automaton::new(
            "p",
            "q0",
            vec![("q0", "q1", (105, 105))], // 'i'
            vec![],
        );
        let q = Automaton::new(
            "q",
            "q0",
            vec![
                ("q0", "q1", (97, 100)),  // a-d
                ("q0", "q1", (101, 110)), // e-n (cobre)
            ],
            vec![],
        );
        assert!(is_subautomaton(p, q));
    }

    #[test]
    fn test_epsilon_matches() {
        let s0 = make_state(0, &[(1, Trigger::Epsilon)], false);
        let s1 = make_state(1, &[], false);

        let p = Automaton {
            name: "p".into(),
            all_states: vec![s0.clone(), s1.clone()],
            initial_state: 0,
        };

        let q = Automaton {
            name: "q".into(),
            all_states: vec![s0, s1],
            initial_state: 0,
        };

        assert!(is_subautomaton(p, q));
    }

    #[test]
    fn test_state_not_subset() {
        let p = Automaton::new("p", "q0", vec![("q0", "qX", (97, 97))], vec![]);
        let q = Automaton::new("q", "q0", vec![], vec![]);
        assert!(!is_subautomaton(p, q));
    }

    #[test]
    fn test_accepting_not_subset() {
        let p = Automaton::new("p", "q0", vec![], vec!["q0"]);
        let q = Automaton::new("q", "q0", vec![], vec![]);
        assert!(!is_subautomaton(p, q));
    }

    #[test]
    fn test_different_initial_state() {
        let p = Automaton::new("p", "q0", vec![], vec![]);
        let q = Automaton::new("q", "q1", vec![], vec![]);
        assert!(!is_subautomaton(p, q));
    }

    #[test]
    fn test_transition_not_covered() {
        let p = Automaton::new(
            "p",
            "q0",
            vec![("q0", "q1", (100, 105))], // d-h
            vec![],
        );

        let q = Automaton::new(
            "q",
            "q0",
            vec![("q0", "q1", (97, 99))], // a-c
            vec![],
        );

        assert!(!is_subautomaton(p, q));
    }

    #[test]
    fn test_epsilon_not_covered_by_range() {
        let s0_p = make_state(0, &[(1, Trigger::Epsilon)], false);
        let s1_p = make_state(1, &[], false);

        let p = Automaton {
            name: "p".into(),
            all_states: vec![s0_p, s1_p],
            initial_state: 0,
        };

        let s0_q = make_state(0, &[(1, Trigger::Range((0, 255)))], false);
        let s1_q = make_state(1, &[], false);

        let q = Automaton {
            name: "q".into(),
            all_states: vec![s0_q, s1_q],
            initial_state: 0,
        };

        assert!(!is_subautomaton(p, q));
    }

    #[test]
    fn test_range_not_covered_by_epsilon() {
        let s0_p = make_state(0, &[(1, Trigger::Range((97, 97)))], false);
        let s1_p = make_state(1, &[], false);

        let p = Automaton {
            name: "p".into(),
            all_states: vec![s0_p, s1_p],
            initial_state: 0,
        };

        let s0_q = make_state(0, &[(1, Trigger::Epsilon)], false);
        let s1_q = make_state(1, &[], false);

        let q = Automaton {
            name: "q".into(),
            all_states: vec![s0_q, s1_q],

            initial_state: 0,
        };

        assert!(!is_subautomaton(p, q));
    }
}
