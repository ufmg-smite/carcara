use super::{CheckerError, Elaborator, RuleArgs, RuleResult};
use crate::checker::error::DratFormatError;
use crate::checker::ProofArg;
use crate::{ast::*, checker::error::ResolutionError};
use core::panic;
use indexmap::IndexSet;
use std::borrow::{Borrow, BorrowMut};
use std::collections::HashMap;
use std::hash::{DefaultHasher, Hash, Hasher};

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
fn get_implied_clause(
    clauses: &mut Vec<(
        (Option<(bool, Rc<Term>)>, Option<(bool, Rc<Term>)>),
        IndexSet<(bool, &Rc<Term>)>,
    )>,
    env: &HashMap<(bool, Rc<Term>), bool>,
) -> Implied<(bool, Rc<Term>)> {
    if clauses.is_empty() {
        return Implied::NotUnsat();
    }

    for (schema, lits) in clauses {
        match schema {
            (None, None) => return Implied::Bottom(),

            (Some((b, t)), None) | (None, Some((b, t))) => match (env.get(&(*b, (*t).clone()))) {
                Some(false) => {
                    assert_eq!(lits.len(), 1);
                    return Implied::Bottom();
                }
                Some(true) => continue,
                None => {
                    assert_eq!(lits.len(), 1);
                    return Implied::Pivot((*b, (*t).clone()));
                }
            },

            (Some((b, t)), Some((b0, t0))) => {
                match (env.get(&(*b, (*t).clone())), env.get(&(*b0, (*t0).clone()))) {
                    (Some(true), _) => continue,
                    (_, Some(true)) => continue,
                    (None, None) => continue,
                    (_, _) => {
                        let mut unset_literal = None;
                        let mut true_clause_found = false;

                        for (b1, t1) in lits.iter() {
                            let assign_state = env.get(&(*b1, (*t1).clone()));

                            match assign_state {
                                None => {
                                    let literal = Some((*b1, (*t1).clone()));
                                    if schema.0 != literal && schema.1 != literal {
                                        if schema.0 != None {
                                            schema.0 = literal;
                                        } else if schema.1 != None {
                                            schema.1 = literal;
                                        }
                                    }

                                    if unset_literal.is_some() {
                                        continue;
                                    }

                                    unset_literal = Some((b1, (*t1).clone()));
                                }
                                Some(true) => {
                                    // Set the true clause as a watched literal to avoid searching O(n) in this "deleted" clause
                                    let literal = Some((*b1, (*t1).clone()));
                                    if schema.0 != literal && schema.1 != literal {
                                        if schema.0 != None {
                                            schema.0 = literal;
                                        } else if schema.1 != None {
                                            schema.1 = literal;
                                        }
                                    }

                                    true_clause_found = true;
                                    continue;
                                }
                                Some(false) => (),
                            }
                        }

                        if true_clause_found {
                            continue;
                        }

                        return match unset_literal {
                            Some((p, polarity)) => Implied::Pivot((*p, polarity.clone())),
                            _ => Implied::Bottom(),
                        };
                    }
                }
            }
        }
    }
    Implied::NotUnsat()
}

fn rup(
    drat_clauses: &HashMap<u64, IndexSet<(bool, &Rc<Term>)>>,
    goal_hash: u64,
    goal: &[Rc<Term>],
) -> bool {
    // PREPARE THE ENV BY SELECTING FOR EACH CLAUSE TWO LITERALS
    // EACH LITERAL HAS A WATCHED LIST
    // USE A RANK TO SELECT THE WATCHED LITERALS, USE THE MOST FTEN LITERALS IN ALL CLAUSES
    // SELECT A UNIT LITERAL BY LOOKING FOR EACH WATCHED LITERAL ITS WATCHED LIST, IF WATCHED LIST LITERAL SIZE IS 1
    // IF SO, USE BCP AND CONTINUE, UPDATE THE SIZE OF WATCHED LIST
    // IF THERE IS NOT UNIT CLAUSE, RETURN FALSE

    let mut drat_clauses: HashMap<u64, IndexSet<(bool, &Rc<Term>)>> = drat_clauses.clone();

    let mut clauses: Vec<(
        (Option<(bool, Rc<Term>)>, Option<(bool, Rc<Term>)>),
        IndexSet<(bool, &Rc<Term>)>,
    )> = vec![];

    let mut env: HashMap<(bool, Rc<Term>), bool> = HashMap::new();

    for term in goal {
        let mut clause: IndexSet<(bool, &Rc<Term>)> = IndexSet::new();
        let (p, regular_term) = term.remove_all_negations_with_polarity();
        clause.insert((!p, regular_term));
        drat_clauses.insert(goal_hash, clause);
    }

    for (_, clause) in drat_clauses {
        let mut watched_literals = clause.iter().take(2);
        clauses.push((
            (
                watched_literals.next().map(|v| (v.0, (*v.1).clone())),
                watched_literals.next().map(|v| (v.0, (*v.1).clone())),
            ),
            clause.clone(),
        ));
    }

    loop {
        // for (p, v) in clauses.clone() {
        //     print!("Watched literals {:?}\n", p);
        //     for c in v {
        //         print!("{:?} --> {:?}\n", c, env.get(&(c.0, c.1.clone())));
        //     }
        //     println!("")
        // }

        let unit = get_implied_clause(clauses.borrow_mut(), env.borrow());
        // print!("UNIT {:?}\n", unit);

        match unit {
            Implied::Bottom() => return true,
            Implied::Pivot(literal) => {
                env.insert(literal.clone(), true);

                // Remove the negated literal from all clauses that contain it
                // TODO : THIS can not exist becuase it is O(n), we only have to save &literal is false somewhere
                let negated_literal = (!literal.0, literal.1.clone());
                env.insert(negated_literal.clone(), false);
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

pub fn elaborate_drat(
    RuleArgs { premises, args, .. }: RuleArgs,
    command_id: String,
    elaborator: &mut Elaborator,
) -> RuleResult {

    let premises: &mut HashMap<u64, _> = &mut premises
    .iter()
    .map(|p| {
        let mut s = DefaultHasher::new();
        p.clause.hash(&mut s);
        (s.finish(), elaborator.map_index(p.index))
    })
    .collect();

    let mut current_id: Box<String> = Box::new(command_id);

    for (i, arg) in args.iter().enumerate() {
        let clause = match arg {
            ProofArg::Term(t) => t,
            ProofArg::Assign(_, _) => panic!("A invalid term was found while solving drat terms"),
        };

        let mut action = |x| {
            if i != args.len() - 1 {
                elaborator.add_new_step(x)
            } else {
                elaborator.push_elaborated_step(x)
            }
        };

        if let Some(terms) = match_term!((cl ...) = &clause) {
            let mut s = DefaultHasher::new();
            terms.hash(&mut s);
            premises.insert(s.finish(), action(ProofStep {
                id: (*current_id).clone(),
                clause: terms.to_vec(),
                rule: "resolution".to_owned(),
                premises: premises.values().map(|x| *x).collect(),
                args: Vec::new(),
                discharge: Vec::new(),
            }));
        }

        if let Some(terms) = match_term!((delete (cl ...)) = &clause) {
            let mut s = DefaultHasher::new();
            terms.hash(&mut s);
            let hash = s.finish();
            premises.remove(&hash);
        }

        if i != args.len() - 1 {
            current_id = Box::new(elaborator.get_new_id(current_id.as_ref()));
        }
    }

    return Ok(());
}
