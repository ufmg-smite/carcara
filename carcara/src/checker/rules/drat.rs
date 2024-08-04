use core::panic;
use std::borrow::{Borrow, BorrowMut};
use std::hash::{DefaultHasher, Hash, Hasher};

use super::{CheckerError, RuleArgs, RuleResult};
use crate::checker::error::DratFormatError;
use crate::checker::ProofArg;
use crate::{ast::*, checker::error::ResolutionError};
use indexmap::IndexSet;
use std::collections::HashMap;
use std::fmt;

#[derive(Debug)]
enum Implied<T> {
    Pivot(T),
    Bottom(),
    NotUnsat(),
}

// PRECONDITION : For each schema in clauses,
// If schema.0 is None, |clause| = 0
// If schema.1 is not None, so schema.0 is not None
// If schema.1 is None, |clause| = 1
// If schema.0 and schema.1 is not None, so |clause| >= 2
fn get_implied_clause<'a>(
    clauses: &'a HashMap<
        u64,
        (
            (Option<(bool, &Rc<Term>)>, Option<(bool, &Rc<Term>)>),
            IndexSet<(bool, &Rc<Term>)>,
        ),
    >,
    env: &HashMap<(bool, Rc<Term>), bool>,
) -> Implied<(bool, Rc<Term>)> {
    for (key, schema) in clauses {
        match schema.0 {
            (None, None) => return Implied::Bottom(),
            (Some((b, t)), None) | (None, Some((b, t))) => match (env.get(&(b, t.clone()))) {
                Some(true) => return Implied::Pivot((b, t.clone())),
                Some(false) => return Implied::Bottom(),
                None => continue,
            },
            (Some((b, t)), Some((b0, t0))) => {
                let count_true_clauses = schema
                    .1
                    .iter()
                    .filter(|(b, t)| Some(true) == env.get(&(*b, (*t).clone())).copied())
                    .count();
                match (env.get(&(b, t.clone())), env.get(&(b0, t0.clone()))) {
                    (None, _) | (_, None) => continue,
                    (Some(true), Some(true)) => continue,
                    (Some(true), Some(false)) => {
                        if count_true_clauses == 1 {
                            return Implied::Pivot((b, t.clone()));
                        } else {
                            continue;
                        }
                    }
                    (Some(false), Some(true)) => {
                        if count_true_clauses == 1 {
                            return Implied::Pivot((b0, t0.clone()));
                        } else {
                            continue;
                        }
                    }
                    (Some(false), Some(false)) => {
                        if count_true_clauses == 0 {
                            return Implied::Bottom();
                        } else if count_true_clauses == 1 {
                            // This case should not exists, since we always pushing the watchers literals to the their schemas
                            // But for the sake of completness of this function we catch the first value avaliable on the clause
                            let (b1, t1) = schema.1.iter().next().unwrap();
                            return Implied::Pivot((*b1, (*t1).clone()));
                        } else {
                            continue;
                        }
                    }
                }
            }
        }
    }
    Implied::NotUnsat()
}

fn fix_watchers_vars<'a>(
    clauses: &mut HashMap<
        u64,
        (
            (Option<(bool, &'a Rc<Term>)>, Option<(bool, &'a Rc<Term>)>),
            IndexSet<(bool, &'a Rc<Term>)>,
        ),
    >,
    pivot: &(bool, Rc<Term>),
    pivot_clauses: &[u64],
    env: &mut HashMap<(bool, Rc<Term>), bool>,
) {
    for pivot_clause in pivot_clauses {
        let clause: &mut (
            (Option<(bool, &Rc<Term>)>, Option<(bool, &Rc<Term>)>),
            IndexSet<(bool, &Rc<Term>)>,
        ) = clauses.get_mut(&pivot_clause).unwrap();
        print!("lançou {:?}\n", *pivot);
        match clause.0 {
            (Some((b, t)), Some((b0, t0))) => {
                if (b, t.clone()) == *pivot {
                    let other_pivot = clause
                        .1
                        .iter()
                        .filter(|(b1, t1)| env.get(&(*b1, (*t1).clone())) == None);
                    print!("eita {:?}\n", *pivot);

                    let mut new_watched_literal =
                        other_pivot.clone().filter(|(b1, t1)| (*b1, *t1) != (b0, t0));
            
                    match new_watched_literal.next() {
                        Some(p) => {
                            (*clause).0 = (Some(*p), clause.0 .1);
                        }
                        None => (),
                    }

                    // If there only one unassigned literal and the other ones are false, so this pivot must be true
                    let positive_literals = clause
                        .1
                        .iter()
                        .filter(|(b1, t1)| env.get(&(*b1, (*t1).clone())) == Some(&true));

                    let mut pivots = other_pivot.take(2);
                    let unit = pivots.next();

                    print!("UNIT {:?}", unit);

                    if pivots.count() == 0 && positive_literals.count() == 0 && unit != None {
                       let unit = unit.unwrap();
                       env.insert((unit.0, unit.1.clone()), true);
                    }
                    
                } else if (b0, t0.clone()) == *pivot {
                    let other_pivot = clause
                        .1
                        .iter()
                        .filter(|(b1, t1)| env.get(&(*b1, (*t1).clone())) == None);
                    print!("eita {:?}\n", *pivot);

                    let mut new_watched_literal =
                        other_pivot.clone().filter(|(b1, t1)| (*b1, *t1) != (b, t));
            
                    match new_watched_literal.next() {
                        Some(p) => {
                            (*clause).0 = (Some(*p), clause.0 .1);
                        }
                        None => (),
                    }
        
                    // If there only one unassigned literal and the other ones are false, so this pivot must be true
                    let positive_literals = clause
                        .1
                        .iter()
                        .filter(|(b1, t1)| env.get(&(*b1, (*t1).clone())) == Some(&true));

                    let mut pivots = other_pivot.take(2);
                    let unit = pivots.next();

                    if pivots.count() == 0 && positive_literals.count() == 0 && unit != None {
                       let unit = unit.unwrap();
                       env.insert((unit.0, unit.1.clone()), true);
                    }

                }
            }
            _ => continue,
        }
    }
}

fn rup(
    drat_clauses: &HashMap<u64, IndexSet<(bool, &Rc<Term>)>>,
    goal_hash: u64,
    goal: &[Rc<Term>],
) -> bool {
    // PREPARE THE ENV BY SELECTING FOR EACH CLAUSE TWO LITERALS
    // EACH LITERAL HAS A WATCHED LIST
    // USE A RANK TO SELECT THE WATCHED LITERALS, USE THE MOST OFTEN LITERALS IN ALL CLAUSES
    // SELECT A UNIT LITERAL BY LOOKING FOR EACH WATCHED LITERAL ITS WATCHED LIST, IF WATCHED LIST LITERAL SIZE IS 1
    // IF SO, USE BCP AND CONTINUE, UPDATE THE SIZE OF WATCHED LIST
    // IF THERE IS NOT UNIT CLAUSE, RETURN FALSE
    let mut clauses: HashMap<
        u64,
        (
            (Option<(bool, &Rc<Term>)>, Option<(bool, &Rc<Term>)>),
            IndexSet<(bool, &Rc<Term>)>,
        ),
    > = HashMap::new();

    let mut literals: HashMap<(bool, Rc<Term>), Vec<u64>> = HashMap::new();
    let mut env: HashMap<(bool, Rc<Term>), bool> = HashMap::new();

    for term in goal {
        let mut clause: IndexSet<(bool, &Rc<Term>)> = IndexSet::new();
        let (p, regular_term) = term.remove_all_negations_with_polarity();
        clause.insert((!p, regular_term));
        clauses.insert(goal_hash, ((Some((!p, regular_term)), None), clause));
    }

    for (key, clause) in drat_clauses {
        if clause.len() == 1 {
            let unit_clause = clause.iter().next().unwrap();
            env.insert((unit_clause.0, unit_clause.1.clone()), true);
        }

        for literal in clause.iter() {
            match literals.get_mut(&(literal.0, literal.1.clone())) {
                Some(lits) => {
                    lits.push(*key);
                }
                None => {
                    literals.insert((literal.0, literal.1.clone()), vec![*key]);
                }
            }
        }

        let mut watched_literals = clause.iter().take(2);
        clauses.insert(
            *key,
            (
                (
                    watched_literals.next().copied(),
                    watched_literals.next().copied(),
                ),
                clause.clone(),
            ),
        );
    }

    loop {
        if clauses.is_empty() {
            return false;
        }

        let unit = get_implied_clause(&clauses, env.borrow());

        print!("{:?}\n", unit);

        for c in &env {
            print!("{:?} ", c);
        }
        print!("\n");
        for (_, (p, v)) in clauses.borrow() {
            print!("Watched literals {:?}\n", p);
            for c in v {
                print!("{:?}\n", c);
            }
            println!("")
        }
        match unit {
            Implied::Bottom() => return true,
            Implied::Pivot(literal) => {
                // Remove all clauses that contain the literal
                // We can do this on O(log n)*? by using literals[p], by let Implied::Pivot(p) = unit

                // We do not needs this
                env.insert(literal.clone(), true);

                let true_clauses = literals.get(literal.borrow()).unwrap();
                for true_clause_key in true_clauses {
                    clauses.remove(true_clause_key);
                }

                literals.remove(literal.borrow());

                // Remove the negated literal from all clauses that contain it
                // TODO : THIS can not exist becuase it is O(n), we only have to save &literal is false somewhere
                let negated_literal = (!literal.0, literal.1.clone());
                env.insert(negated_literal.clone(), false);

                fix_watchers_vars(
                    &mut clauses,
                    negated_literal.borrow(),
                    literals.get(&negated_literal).unwrap_or(&vec![]),
                    &mut env,
                );
            }
            Implied::NotUnsat() => return false,
        }
    }
}

pub fn drat(RuleArgs { conclusion, premises, args, .. }: RuleArgs) -> RuleResult {
    let mut premises: HashMap<u64, _> = premises
        .iter()
        .map(|p| p.clause)
        .map(|p| {
            let mut s = DefaultHasher::new();
            p.hash(&mut s);
            (
                s.finish(),
                p.iter()
                    .map(Rc::remove_all_negations_with_polarity)
                    .collect::<IndexSet<_>>(),
            )
        })
        .collect();

    for arg in args {
        match arg {
            ProofArg::Term(t) => {
                match match_term!((delete (cl ...)) = &t) {
                    Some(terms) => {
                        let mut s = DefaultHasher::new();
                        terms.hash(&mut s);
                        premises.remove(&s.finish());
                        continue;
                    }
                    None => (),
                }

                let terms = match match_term!((cl ...) = &t) {
                    Some(terms) => terms,
                    None => panic!("Invalid clause term"),
                };

                let mut s = DefaultHasher::new();
                terms.hash(&mut s);
                let hash_term = s.finish();

                if !rup(premises.borrow(), hash_term, terms) {
                    return Err(CheckerError::Resolution(ResolutionError::TautologyFailed));
                }

                premises.insert(
                    hash_term,
                    terms
                        .iter()
                        .map(Rc::remove_all_negations_with_polarity)
                        .collect::<IndexSet<_>>(),
                );
            }
            ProofArg::Assign(_, _) => panic!("A invalid term was found while solving drat terms"),
        }
    }

    let mut s = DefaultHasher::new();
    conclusion.hash(&mut s);

    if !premises.contains_key(&s.finish()) {
        return Err(CheckerError::DratFormatError(
            DratFormatError::NoConclusionInPremise,
        ));
    }

    Ok(())
}
