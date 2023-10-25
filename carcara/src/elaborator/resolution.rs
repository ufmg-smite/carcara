use std::collections::{HashMap, HashSet};

use super::*;
use crate::ast::*;

type Literal<'a> = (u32, &'a Rc<Term>);

fn apply_naive_resolution<'a>(
    premises: &[Vec<Literal<'a>>],
    pivots: &[(Literal, bool)],
) -> Vec<Literal<'a>> {
    assert!(premises.len() >= 2);
    assert_eq!(pivots.len(), premises.len() - 1);

    let mut current = premises[0].clone();

    for (premise, &(pivot, polarity)) in premises[1..].iter().zip(pivots) {
        let negated_pivot = (pivot.0 + 1, pivot.1);
        let (pivot_in_current, pivot_in_next) = if polarity {
            (pivot, negated_pivot)
        } else {
            (negated_pivot, pivot)
        };

        let pos = current.iter().position(|x| x == &pivot_in_current).unwrap();
        current.remove(pos);

        let mut found = false;
        for &t in premise {
            if !found && t == pivot_in_next {
                found = true;
            } else {
                current.push(t);
            }
        }
        assert!(found);
    }

    current
}

#[allow(unused)]
pub fn elaborate_resolution(
    pool: &mut dyn TermPool,
    elaborator: &mut Elaborator,
    step: &ProofStep,
    premises: Vec<&[Rc<Term>]>,
) {
    let premises: Vec<Vec<_>> = premises
        .iter()
        .map(|c| c.iter().map(Rc::remove_all_negations).collect())
        .collect();
    let pivots: Vec<_> = step
        .args
        .chunks(2)
        .map(|chunk| {
            let pivot = chunk[0].as_term().unwrap().remove_all_negations();
            let polarity = chunk[1].as_term().unwrap().is_bool_true();
            (pivot, polarity)
        })
        .collect();
    let naive_conclusion = apply_naive_resolution(&premises, &pivots);
    let target_conclusion = step.clause.iter().map(Rc::remove_all_negations).collect();

    let _ = find_needed_contractions(naive_conclusion, target_conclusion, premises, &pivots);

    todo!()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CrowdingLiteralInfo {
    last_inclusion: usize,
    eliminator: usize,
}

fn find_crowding_literals<'a>(
    naive_conclusion: Vec<Literal<'a>>,
    target_conclusion: Vec<Literal<'a>>,
    premises: Vec<Vec<Literal<'a>>>,
    pivots: &[(Literal<'a>, bool)],
) -> HashMap<Literal<'a>, CrowdingLiteralInfo> {
    let mut crowding_lits: HashMap<Literal, CrowdingLiteralInfo> = {
        let target_conclusion: HashSet<_> = target_conclusion.iter().collect();
        naive_conclusion
            .iter()
            .filter(|lit| !target_conclusion.contains(lit))
            .map(|&l| (l, CrowdingLiteralInfo { last_inclusion: 0, eliminator: 0 }))
            .collect()
    };
    for (i, clause) in premises.iter().enumerate() {
        for lit in clause {
            if let Some(info) = crowding_lits.get_mut(lit) {
                info.last_inclusion = i;
            }
        }
    }
    for (i, &(pivot, polarity)) in pivots.iter().enumerate() {
        let pivot_in_current = if polarity {
            pivot
        } else {
            (pivot.0 + 1, pivot.1)
        };
        if let Some(info) = crowding_lits.get_mut(&pivot_in_current) {
            if i + 1 > info.last_inclusion {
                info.eliminator = i + 1;
            }
        }
    }
    crowding_lits
}

fn find_needed_contractions(
    naive_conclusion: Vec<Literal>,
    target_conclusion: Vec<Literal>,
    premises: Vec<Vec<Literal>>,
    pivots: &[(Literal, bool)],
) -> Vec<usize> {
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    enum Event {
        Elimination,
        LastInclusion,
    }

    let crowding_lits =
        find_crowding_literals(naive_conclusion, target_conclusion, premises, pivots);

    let mut events: Vec<_> = crowding_lits
        .iter()
        .flat_map(|(lit, info)| {
            [
                (*lit, Event::LastInclusion, info.last_inclusion),
                (*lit, Event::Elimination, info.eliminator),
            ]
        })
        .collect();

    // If there are multiple events at the same index, we must process eliminations first
    events.sort_unstable_by(|(_, a_event, a_index), (_, b_event, b_index)| {
        match a_index.cmp(b_index) {
            std::cmp::Ordering::Equal => a_event.cmp(b_event),
            other => other,
        }
    });

    let mut contractions = Vec::new();
    let mut need_to_contract = HashSet::new();
    for (lit, event, index) in events {
        match event {
            Event::LastInclusion => {
                need_to_contract.insert(lit);
            }
            Event::Elimination => {
                if need_to_contract.contains(&lit) {
                    contractions.push(index);
                    need_to_contract.clear();
                }
            }
        }
    }
    contractions
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::tests::*;

    fn parse_premises(
        pool: &mut PrimitivePool,
        definitions: &str,
        premises: Vec<Vec<&str>>,
    ) -> Vec<Vec<Rc<Term>>> {
        premises
            .into_iter()
            .map(|c| {
                c.into_iter()
                    .map(|t| {
                        let [t] = parse_terms(pool, definitions, [t]);
                        t
                    })
                    .collect()
            })
            .collect()
    }

    fn premises_to_literals(premises: &[Vec<Rc<Term>>]) -> Vec<Vec<Literal>> {
        premises
            .iter()
            .map(|c| c.iter().map(Rc::remove_all_negations).collect())
            .collect()
    }

    #[test]
    fn test_find_needed_contractions() {
        let mut pool = PrimitivePool::new();
        let premises = vec![
            vec!["x", "a", "b"],
            vec!["(not x)", "y", "a", "c"],
            vec!["(not y)", "z", "b"],
            vec!["(not a)"],
            vec!["(not z)", "c"],
            vec!["d", "(not b)"],
            vec!["d", "(not c)"],
            vec!["(not d)"],
        ];
        let definitions = "
            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const c Bool)
            (declare-const d Bool)
            (declare-const x Bool)
            (declare-const y Bool)
            (declare-const z Bool)
        ";
        let premises = parse_premises(&mut pool, definitions, premises);
        let premises = premises_to_literals(&premises);
        let [a, b, c, d, x, y, z] = [
            premises[1][2],
            premises[0][2],
            premises[1][3],
            premises[5][0],
            premises[0][0],
            premises[1][1],
            premises[2][1],
        ];
        let pivots = [x, y, a, z, b, c, d].map(|lit| (lit, true));

        let naive_conclusion = apply_naive_resolution(&premises, &pivots);
        let target_conclusion = Vec::new();

        let crowding_literals = find_crowding_literals(
            naive_conclusion.clone(),
            target_conclusion.clone(),
            premises.clone(),
            &pivots,
        );

        let expected = [
            (a, CrowdingLiteralInfo { last_inclusion: 1, eliminator: 3 }),
            (b, CrowdingLiteralInfo { last_inclusion: 2, eliminator: 5 }),
            (c, CrowdingLiteralInfo { last_inclusion: 4, eliminator: 6 }),
            (d, CrowdingLiteralInfo { last_inclusion: 6, eliminator: 7 }),
        ]
        .into_iter()
        .collect();
        assert_eq!(crowding_literals, expected);

        assert_eq!(
            find_needed_contractions(naive_conclusion, target_conclusion, premises, &pivots),
            [3, 6, 7]
        );
    }
}
