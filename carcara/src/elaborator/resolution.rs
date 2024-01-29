use std::collections::{HashMap, HashSet};

use super::*;
use crate::{
    ast::*,
    checker::{RuleArgs, RuleResult},
    utils::DedupIterator,
};

type Literal<'a> = (u32, &'a Rc<Term>);

fn literal_to_term(pool: &mut dyn TermPool, (n, term): Literal) -> Rc<Term> {
    let mut term = term.clone();
    for _ in 0..n {
        term = build_term!(pool, (not { term }));
    }
    term
}

fn literals_to_clause(pool: &mut dyn TermPool, clause: &[Literal]) -> Vec<Rc<Term>> {
    clause.iter().map(|l| literal_to_term(pool, *l)).collect()
}

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
#[allow(clippy::unnecessary_wraps)]
pub fn uncrowd_resolution(
    RuleArgs {
        conclusion, premises, args, pool, ..
    }: RuleArgs,
    command_id: String,
    elaborator: &mut Elaborator,
) -> RuleResult {
    let target_conclusion: HashSet<_> = conclusion.iter().map(Rc::remove_all_negations).collect();

    let premise_clauses: Vec<Vec<_>> = premises
        .iter()
        .map(|p| p.clause.iter().map(Rc::remove_all_negations).collect())
        .collect();
    let pivots: Vec<_> = args
        .chunks(2)
        .map(|chunk| {
            let pivot = chunk[0].as_term().unwrap().remove_all_negations();
            let polarity = chunk[1].as_term().unwrap().is_bool_true();
            (pivot, polarity)
        })
        .collect();
    let naive_conclusion = apply_naive_resolution(&premise_clauses, &pivots);

    let crowding_literals = find_crowding_literals(
        &naive_conclusion,
        &target_conclusion,
        &premise_clauses,
        &pivots,
    );
    let mut contractions = find_needed_contractions(crowding_literals);
    if contractions.last() != Some(&premises.len()) {
        contractions.push(premises.len());
    }

    let mut previous_cut = 0;
    let mut previous_index = None;
    let mut previous_clause = None;
    let mut pivots = pivots.into_iter();

    for cut in contractions {
        let premise_indices: Vec<_> = previous_index
            .into_iter()
            .chain(
                premises[previous_cut..cut]
                    .iter()
                    .map(|p| elaborator.map_index(p.index)),
            )
            .collect();
        let clauses: Vec<_> = previous_clause
            .into_iter()
            .chain(premise_clauses[previous_cut..cut].iter().cloned())
            .collect();
        let pivots: Vec<_> = (&mut pivots).take(premise_indices.len() - 1).collect();
        let (index, clause) = add_partial_resolution_step(
            pool,
            &command_id,
            elaborator,
            premise_indices,
            clauses,
            pivots,
        );
        previous_cut = cut;
        previous_index = Some(index);
        previous_clause = Some(clause);
    }

    let final_step = ProofStep {
        id: elaborator.get_new_id(&command_id),
        clause: literals_to_clause(pool, &previous_clause.unwrap()),
        rule: "reordering".to_owned(),
        premises: vec![previous_index.unwrap()],
        args: Vec::new(),
        discharge: Vec::new(),
    };
    elaborator.push_elaborated_step(final_step);
    Ok(())
}

fn add_partial_resolution_step<'a>(
    pool: &mut dyn TermPool,
    command_id: &str,
    elaborator: &mut Elaborator,
    premise_indices: Vec<(usize, usize)>,
    premise_clauses: Vec<Vec<Literal<'a>>>,
    pivots: Vec<(Literal<'a>, bool)>,
) -> ((usize, usize), Vec<Literal<'a>>) {
    let conclusion = apply_naive_resolution(&premise_clauses, &pivots);
    let contracted_conclusion = conclusion.iter().dedup().copied().collect();

    let args = pivots
        .into_iter()
        .flat_map(|(literal, polarity)| {
            [literal_to_term(pool, literal), pool.bool_constant(polarity)]
        })
        .map(ProofArg::Term)
        .collect();

    let clause = literals_to_clause(pool, &conclusion);
    let contracted_clause = clause.iter().dedup().cloned().collect();

    let resolution_step = ProofStep {
        id: elaborator.get_new_id(command_id),
        clause,
        rule: "resolution".to_owned(),
        premises: premise_indices,
        args,
        discharge: Vec::new(),
    };
    let resolution_step = elaborator.add_new_step(resolution_step);

    let contraction_step = ProofStep {
        id: elaborator.get_new_id(command_id),
        clause: contracted_clause,
        rule: "contraction".to_owned(),
        premises: vec![resolution_step],
        args: Vec::new(),
        discharge: Vec::new(),
    };
    (
        elaborator.add_new_step(contraction_step),
        contracted_conclusion,
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CrowdingLiteralInfo {
    last_inclusion: usize,
    eliminator: usize,
}

fn find_crowding_literals<'a>(
    naive_conclusion: &[Literal<'a>],
    target_conclusion: &HashSet<Literal<'a>>,
    premises: &[Vec<Literal<'a>>],
    pivots: &[(Literal<'a>, bool)],
) -> HashMap<Literal<'a>, CrowdingLiteralInfo> {
    let mut crowding_lits: HashMap<Literal, CrowdingLiteralInfo> = naive_conclusion
        .iter()
        .filter(|lit| !target_conclusion.contains(lit))
        .map(|&l| (l, CrowdingLiteralInfo { last_inclusion: 0, eliminator: 0 }))
        .collect();

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
    crowding_literals: HashMap<Literal, CrowdingLiteralInfo>,
) -> Vec<usize> {
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    enum Event {
        Elimination,
        LastInclusion,
    }

    let mut events: Vec<_> = crowding_literals
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
    use crate::{
        checker::Premise,
        parser::{self, parse_instance, parse_instance_with_pool, tests::*},
    };

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
        let target_conclusion = HashSet::new();

        let crowding_literals =
            find_crowding_literals(&naive_conclusion, &target_conclusion, &premises, &pivots);

        let expected = [
            (a, CrowdingLiteralInfo { last_inclusion: 1, eliminator: 3 }),
            (b, CrowdingLiteralInfo { last_inclusion: 2, eliminator: 5 }),
            (c, CrowdingLiteralInfo { last_inclusion: 4, eliminator: 6 }),
            (d, CrowdingLiteralInfo { last_inclusion: 6, eliminator: 7 }),
        ]
        .into_iter()
        .collect();
        assert_eq!(crowding_literals, expected);

        assert_eq!(find_needed_contractions(crowding_literals), [3, 6, 7]);
    }

    #[test]
    fn test_uncrowd_resolution() {
        // This triggers a false positive in clippy, so we have to disable this lint
        #[allow(clippy::redundant_type_annotations)]
        let problem: &[u8] = b"
            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const c Bool)
            (declare-const d Bool)
            (declare-const x Bool)
            (declare-const y Bool)
            (declare-const z Bool)
        ";
        let proof = b"
            (step t1 (cl x a b) :rule hole)
            (step t2 (cl (not x) y a c) :rule hole)
            (step t3 (cl (not y) z b) :rule hole)
            (step t4 (cl (not a)) :rule hole)
            (step t5 (cl (not z) c) :rule hole)
            (step t6 (cl d (not b)) :rule hole)
            (step t7 (cl d (not c)) :rule hole)
            (step t8 (cl (not d)) :rule hole)
            (step t9 (cl)
                :rule resolution
                :premises (t1 t2 t3 t4 t5 t6 t7 t8)
                :args (x true y true a true z true b true c true d true))
        ";
        let (_, proof, mut pool) = parse_instance(problem, proof, parser::Config::new()).unwrap();

        let mut elab = Elaborator::new();
        let ProofCommand::Step(step) = proof.commands.last().unwrap() else {
            unreachable!()
        };
        let premises: Vec<_> = step
            .premises
            .iter()
            .map(|&p| {
                let command = &proof.commands[p.1];
                Premise::new(p, command)
            })
            .collect();

        for s in &proof.commands[..8] {
            elab.unchanged(s.clause());
        }

        #[allow(const_item_mutation)] // We don't care about `poly_eq_time`
        let args = RuleArgs {
            conclusion: &step.clause,
            premises: &premises,
            args: &step.args,
            pool: &mut pool,
            context: &mut ContextStack::new(),
            previous_command: None,
            discharge: &Vec::new(),
            polyeq_time: &mut std::time::Duration::ZERO,
        };
        uncrowd_resolution(args, "t9".to_owned(), &mut elab).unwrap();
        let got = elab.end(proof.commands);

        let expected = b"
            (step t1 (cl x a b) :rule hole)
            (step t2 (cl (not x) y a c) :rule hole)
            (step t3 (cl (not y) z b) :rule hole)
            (step t4 (cl (not a)) :rule hole)
            (step t5 (cl (not z) c) :rule hole)
            (step t6 (cl d (not b)) :rule hole)
            (step t7 (cl d (not c)) :rule hole)
            (step t8 (cl (not d)) :rule hole)
            (step t9.t1 (cl a b a c z b) :rule resolution :premises (t1 t2 t3)
                :args (x true y true))
            (step t9.t2 (cl a b c z) :rule contraction :premises (t9.t1))
            (step t9.t3 (cl c c d) :rule resolution :premises (t9.t2 t4 t5 t6)
                :args (a true z true b true))
            (step t9.t4 (cl c d) :rule contraction :premises (t9.t3))
            (step t9.t5 (cl d d) :rule resolution :premises (t9.t4 t7) :args (c true))
            (step t9.t6 (cl d) :rule contraction :premises (t9.t5))
            (step t9.t7 (cl) :rule resolution :premises (t9.t6 t8) :args (d true))
        ";
        let (_, expected) =
            parse_instance_with_pool(problem, expected, parser::Config::new(), &mut pool).unwrap();
        assert_eq!(expected.commands, got);
    }
}
