use crate::{
    automata::{State, Transition, Trigger},
    checker::error::{CheckerError, StringError},
};

/// Computes the intersection range of two range triggers, returning `None` if they are disjoint.
pub fn intersect_ranges(r1: Trigger, r2: Trigger) -> Result<Option<(u32, u32)>, CheckerError> {
    match (r1.clone(), r2.clone()) {
        (Trigger::Range(r1), Trigger::Range(r2)) => {
            let start = r1.0.max(r2.0);
            let end = r1.1.min(r2.1);
            if start <= end {
                Ok(Some((start, end)))
            } else {
                Ok(None)
            }
        }
        _ => Err(StringError::ExpectedRangesToCalculateTheIntersection(r1, r2).into()),
    }
}

fn normalize_ranges(mut ranges: Vec<(u32, u32)>) -> Vec<(u32, u32)> {
    if ranges.is_empty() {
        return ranges;
    }

    ranges.sort_by(|a, b| a.0.cmp(&b.0));

    let mut result = vec![ranges[0]];

    for (l, r) in ranges.into_iter().skip(1) {
        let last = result.last_mut().unwrap();
        if l <= last.1.saturating_add(1) {
            last.1 = last.1.max(r);
        } else {
            result.push((l, r));
        }
    }
    result
}

/// Finds missing character ranges (gaps) within `[min_symbol, max_symbol]` given an existing list of ranges.
pub fn missing_ranges(
    existing: &[(u32, u32)],
    min_symbol: u32,
    max_symbol: u32,
) -> Vec<(u32, u32)> {
    let normalized = normalize_ranges(existing.to_vec());
    let mut holes = Vec::new();

    let mut cursor = min_symbol;

    for (l, r) in normalized {
        if cursor < l {
            holes.push((cursor, l - 1));
        }
        if r == u32::MAX {
            return holes;
        }
        cursor = r + 1;
    }

    if cursor <= max_symbol {
        holes.push((cursor, max_symbol));
    }

    holes
}

/// Returns `true` if any ranges in the provided collection overlap with each other.
pub fn has_overlapping_ranges(ranges: Vec<(u32, u32)>) -> bool {
    if ranges.len() < 2 {
        return false;
    }

    let mut prev_end = ranges[0].1;
    for &(start, end) in &ranges[1..] {
        // Intersection
        if start <= prev_end {
            return true;
        }

        // Update the highest end until now
        prev_end = prev_end.max(end);
    }

    false
}

/// Completes a set of states by introducing a dead/sink state and adding transitions
/// for all unhandled input symbol ranges.
pub fn totalize(states: Vec<State>) -> Vec<State> {
    let mut new_states = states.clone();

    let sink_id = states.len();
    let mut sink_state = State::new("sink", false);
    sink_state
        .transitions
        .insert(Transition::new(sink_id, Trigger::Range((0, u32::MAX))));
    new_states.push(sink_state);

    for state in &mut new_states[..sink_id] {
        let mut existing_ranges = Vec::new();
        for t in &state.transitions {
            if let Trigger::Range((l, r)) = t.trigger {
                existing_ranges.push((l, r));
            }
        }

        let holes = missing_ranges(&existing_ranges, 0, u32::MAX);

        for (l, r) in holes {
            state
                .transitions
                .insert(Transition::new(sink_id, Trigger::Range((l, r))));
        }
    }

    new_states
}

#[cfg(test)]
mod tests {
    use super::*;

    // Auxiliar functions
    fn range_to_sink(state: &State, sink_id: usize) -> Vec<(u32, u32)> {
        state
            .transitions
            .iter()
            .filter_map(|t| {
                if t.to == sink_id {
                    if let Trigger::Range(r) = t.trigger {
                        Some(r)
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect()
    }

    fn all_ranges(state: &State) -> Vec<(u32, u32)> {
        state
            .transitions
            .iter()
            .filter_map(|t| {
                if let Trigger::Range(r) = t.trigger {
                    Some(r)
                } else {
                    None
                }
            })
            .collect()
    }

    #[test]
    fn intersect_ranges_should_return_intersection() {
        let r1 = Trigger::Range((1, 10));
        let r2 = Trigger::Range((5, 15));

        let result = intersect_ranges(r1, r2).unwrap();

        assert_eq!(result, Some((5, 10)));
    }

    #[test]
    fn intersect_ranges_should_return_none_when_disjoint() {
        let r1 = Trigger::Range((1, 5));
        let r2 = Trigger::Range((10, 15));

        let result = intersect_ranges(r1, r2).unwrap();

        assert_eq!(result, None);
    }

    #[test]
    fn missing_ranges_should_find_holes() {
        let ranges = vec![(10, 20), (30, 40)];
        let result = missing_ranges(&ranges, 0, 50);
        assert_eq!(result, vec![(0, 9), (21, 29), (41, 50)]);
    }

    #[test]
    fn has_overlapping_ranges_should_detect_overlap() {
        let ranges = vec![(1, 10), (5, 15)];
        assert!(has_overlapping_ranges(ranges));
    }

    #[test]
    fn has_overlapping_ranges_should_return_false_when_no_overlap() {
        let ranges = vec![(1, 5), (6, 10)];
        assert!(!has_overlapping_ranges(ranges));
    }

    #[test]
    fn test_totalize_adds_sink_state() {
        let s0 = State::new("q0", false);
        let states = vec![s0];

        let totalized = totalize(states);

        assert_eq!(totalized.len(), 2);

        let sink = &totalized[1];
        assert_eq!(sink.id, "sink");
        assert!(!sink.accept);
    }

    #[test]
    fn test_sink_has_self_loop_over_full_alphabet() {
        let s0 = State::new("q0", false);
        let totalized = totalize(vec![s0]);

        let sink = &totalized[1];
        let ranges = all_ranges(sink);

        assert!(missing_ranges(&ranges, 0, u32::MAX).is_empty());
    }

    #[test]
    fn test_state_with_full_coverage_gets_no_sink_transitions() {
        let mut s0 = State::new("q0", false);
        s0.transitions
            .insert(Transition::new(0, Trigger::Range((0, u32::MAX))));

        let totalized = totalize(vec![s0]);
        let q0 = &totalized[0];

        let sink_ranges = range_to_sink(q0, 1);
        assert!(sink_ranges.is_empty());
    }

    #[test]
    fn test_state_with_missing_ranges_gets_sink_transitions() {
        let mut s0 = State::new("q0", false);
        s0.transitions
            .insert(Transition::new(0, Trigger::Range((0, 9))));
        s0.transitions
            .insert(Transition::new(0, Trigger::Range((20, 29))));

        let totalized = totalize(vec![s0]);
        let q0 = &totalized[0];

        let sink_ranges = range_to_sink(q0, 1);
        let mut sorted_ranges = sink_ranges.clone();
        sorted_ranges.sort_unstable_by_key(|(start, _)| *start);

        assert_eq!(sorted_ranges, vec![(10, 19), (30, u32::MAX)]);
    }

    #[test]
    fn test_overlapping_ranges_are_normalized_before_totalizing() {
        let mut s0 = State::new("q0", false);
        s0.transitions
            .insert(Transition::new(0, Trigger::Range((0, 10))));
        s0.transitions
            .insert(Transition::new(0, Trigger::Range((5, 20))));

        let totalized = totalize(vec![s0]);
        let q0 = &totalized[0];

        let sink_ranges = range_to_sink(q0, 1);
        assert_eq!(sink_ranges, vec![(21, u32::MAX)]);
    }

    #[test]
    fn test_adjacent_ranges_are_merged_before_holes() {
        let mut s0 = State::new("q0", false);
        s0.transitions
            .insert(Transition::new(0, Trigger::Range((0, 9))));
        s0.transitions
            .insert(Transition::new(0, Trigger::Range((10, 19))));

        let totalized = totalize(vec![s0]);
        let q0 = &totalized[0];

        let sink_ranges = range_to_sink(q0, 1);
        assert_eq!(sink_ranges, vec![(20, u32::MAX)]);
    }

    #[test]
    fn test_totalized_state_covers_entire_alphabet() {
        let mut s0 = State::new("q0", false);
        s0.transitions
            .insert(Transition::new(0, Trigger::Range((10, 20))));

        let totalized = totalize(vec![s0]);
        let q0 = &totalized[0];

        let mut all = all_ranges(q0);
        all.sort();

        let normalized = normalize_ranges(all);
        assert_eq!(normalized, vec![(0, u32::MAX)]);
    }

    #[test]
    fn test_multiple_states_all_get_totalized() {
        let mut s0 = State::new("q0", false);
        s0.transitions
            .insert(Transition::new(0, Trigger::Range((0, 10))));

        let mut s1 = State::new("q1", true);
        s1.transitions
            .insert(Transition::new(1, Trigger::Range((20, 30))));

        let totalized = totalize(vec![s0, s1]);

        let sink_id = 2;

        let sink_ranges_q0 = range_to_sink(&totalized[0], sink_id);
        let sink_ranges_q1 = range_to_sink(&totalized[1], sink_id);

        assert!(!sink_ranges_q0.is_empty());
        assert!(!sink_ranges_q1.is_empty());
    }
}
