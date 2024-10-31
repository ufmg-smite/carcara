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
enum Implied<T, X> {
    Pivot(T, X),
    Bottom(X),
    NotUnsat(),
}

type RupAdition<'a> = Vec<(
    IndexSet<(bool, &'a Rc<Term>)>,
    Option<(bool, Rc<Term>)>,
    u64,
)>;

enum DRupProofAction<'a> {
    RupStory(&'a [Rc<Term>], RupAdition<'a>),
    Delete(&'a [Rc<Term>]),
}

type DRupStory<'a> = Vec<DRupProofAction<'a>>;

// PRECONDITION : For each schema in clauses,
// If schema.0 is None, |clause| = 0
// If schema.1 is not None, so schema.0 is not None
// If schema.1 is None, |clause| = 1
// If schema.0 and schema.1 is not None, so |clause| >= 2
fn get_implied_clause<'a>(
    clauses: &mut Vec<(
        (Option<(bool, Rc<Term>)>, Option<(bool, Rc<Term>)>),
        (IndexSet<(bool, &'a Rc<Term>)>, u64),
    )>,
    env: &HashMap<(bool, Rc<Term>), bool>,
) -> Implied<(bool, Rc<Term>), (IndexSet<(bool, &'a Rc<Term>)>, u64)> {
    if clauses.is_empty() {
        return Implied::NotUnsat();
    }

    for (schema, (lits, key)) in clauses {
        match schema {
            (None, None) => return Implied::Bottom(((*lits).clone(), *key)),

            (Some((b, t)), None) | (None, Some((b, t))) => match (env.get(&(*b, (*t).clone()))) {
                Some(false) => {
                    assert_eq!(lits.len(), 1);
                    return Implied::Bottom(((*lits).clone(), *key));
                }
                Some(true) => continue,
                None => {
                    assert_eq!(lits.len(), 1);
                    return Implied::Pivot((*b, (*t).clone()), ((*lits).clone(), *key));
                }
            },

            (Some((b, t)), Some((b0, t0))) => {
                match (env.get(&(*b, (*t).clone())), env.get(&(*b0, (*t0).clone()))) {
                    (Some(true), _) => continue,
                    (_, Some(true)) => continue,
                    (None, None) => continue,
                    (_, _) => {
                        let mut unset_literal = None;
                        let mut not_unit = false;

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
                                        not_unit = true;
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

                                    not_unit = true;
                                    continue;
                                }
                                Some(false) => (),
                            }
                        }

                        if not_unit {
                            continue;
                        }

                        return match unset_literal {
                            Some((p, polarity)) => {
                                Implied::Pivot((*p, polarity.clone()), ((*lits).clone(), *key))
                            }
                            _ => Implied::Bottom(((*lits).clone(), *key)),
                        };
                    }
                }
            }
        }
    }
    Implied::NotUnsat()
}

fn rup<'a>(
    drat_clauses: &HashMap<u64, IndexSet<(bool, &'a Rc<Term>)>>,
    goal: &'a [Rc<Term>],
) -> Option<RupAdition<'a>> {
    // PREPARE THE ENV BY SELECTING FOR EACH CLAUSE TWO LITERALS
    // EACH LITERAL HAS A WATCHED LIST
    // USE A RANK TO SELECT THE WATCHED LITERALS, USE THE MOST FTEN LITERALS IN ALL CLAUSES
    // SELECT A UNIT LITERAL BY LOOKING FOR EACH WATCHED LITERAL ITS WATCHED LIST, IF WATCHED LIST LITERAL SIZE IS 1
    // IF SO, USE BCP AND CONTINUE, UPDATE THE SIZE OF WATCHED LIST
    // IF THERE IS NOT UNIT CLAUSE, RETURN FALSE

    let mut drat_clauses: HashMap<u64, IndexSet<(bool, &'a Rc<Term>)>> = drat_clauses.clone();
    let mut unit_story: RupAdition<'a> = vec![];

    let mut clauses: Vec<(
        (Option<(bool, Rc<Term>)>, Option<(bool, Rc<Term>)>),
        (IndexSet<(bool, &'a Rc<Term>)>, u64),
    )> = vec![];

    let mut env: HashMap<(bool, Rc<Term>), bool> = HashMap::new();

    for term in goal {
        let mut clause: IndexSet<(bool, &Rc<Term>)> = IndexSet::new();
        let mut s = DefaultHasher::new();
        term.hash(&mut s);
        let (p, regular_term) = term.remove_all_negations_with_polarity();
        clause.insert((!p, regular_term));
        drat_clauses.insert(s.finish(), clause);
    }

    for (key, clause) in drat_clauses {
        let mut watched_literals = clause.iter().take(2);
        clauses.push((
            (
                watched_literals.next().map(|v| (v.0, (*v.1).clone())),
                watched_literals.next().map(|v| (v.0, (*v.1).clone())),
            ),
            (clause.clone(), key),
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
        print!("{:?}\n", unit);
        match unit {
            Implied::Bottom(clause) => {
                unit_story.push((clause.0, None, clause.1));
                return Some(unit_story);
            }
            Implied::Pivot(literal, clause) => {
                env.insert(literal.clone(), true);
                // Remove the negated literal from all clauses that contain it
                // TODO : THIS can not exist becuase it is O(n), we only have to save &literal is false somewhere
                let negated_literal = (!literal.0, literal.1.clone());
                env.insert(negated_literal.clone(), false);
                unit_story.push((clause.0, Some((literal.0, literal.1)), clause.1));
            }
            Implied::NotUnsat() => return None,
        }
    }
}

fn check_drup(
    RuleArgs { conclusion, premises, args, .. }: RuleArgs,
) -> Result<DRupStory, CheckerError> {
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

    let mut drup_history: DRupStory = vec![];
    for arg in args {
        match arg {
            ProofArg::Term(t) => {
                match match_term!((delete (cl ...)) = &t) {
                    Some(terms) => {
                        let mut s = DefaultHasher::new();
                        terms.hash(&mut s);
                        premises.remove(&s.finish());
                        drup_history.push(DRupProofAction::Delete(terms));
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

                let unit_history = rup(premises.borrow(), terms);

                if unit_history == None {
                    return Err(CheckerError::Resolution(ResolutionError::TautologyFailed));
                }

                drup_history.push(DRupProofAction::RupStory(terms, unit_history.unwrap()));

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

    Ok(drup_history)
}

pub fn drup(args: RuleArgs) -> RuleResult {
    check_drup(args).map(|_| ())
}

pub fn elaborate_drat(
    rule_args: RuleArgs,
    command_id: String,
    elaborator: &mut Elaborator,
) -> RuleResult {
    #[derive(Debug)]
    enum ResolutionStep<'a> {
        Resolvent(u64, u64, (Vec<Rc<Term>>, u64)),
        UnChanged(IndexSet<(bool, &'a Rc<Term>)>, u64),
    }

    fn resolve<'a>(
        clause1: &IndexSet<(bool, &'a Rc<Term>)>,
        clause2: &IndexSet<(bool, &'a Rc<Term>)>,
        pivot: (bool, &Rc<Term>),
    ) -> IndexSet<(bool, &'a Rc<Term>)> {
        let mut resolvent = IndexSet::new();
        for literal in clause1.union(clause2) {
            if literal.1 == pivot.1 {
                continue;
            }

            resolvent.insert(*literal);
        }

        return resolvent;
    }

    let RuleArgs { premises, args, .. } = rule_args;

    let trace = check_drup(rule_args);

    if let Err(err) = trace {
        return Err(err);
    }

    let premises: &mut HashMap<u64, _> = &mut premises
        .iter()
        .map(|p| {
            let mut s = DefaultHasher::new();
            p.clause.hash(&mut s);
            (s.finish(), elaborator.map_index(p.index))
        })
        .collect();

    let mut current_id: Box<String> = Box::new(command_id);
    let trace = trace.unwrap();

    for (arg_index, rup_story) in trace.iter().enumerate() {
        match rup_story {
            DRupProofAction::RupStory(rup_clause, rup_history) => {
                let mut rup: Vec<(IndexSet<(bool, &Rc<Term>)>, u64)> = rup_history
                    .iter()
                    .map(|(vec, _, key)| (vec.clone(), *key))
                    .collect();
                let pivots: Vec<_> = rup_history.iter().map(|(_, term, _)| term).collect();

                let mut resolutions = vec![];
                for i in (0..rup_history.len() - 1).rev() {
                    let pivot = pivots[i].as_ref().unwrap();

                    if rup[i + 1].0.contains(&(!pivot.0, &pivot.1)) {
                        let resolvent_indexset: IndexSet<(bool, &Rc<Term>)> =
                            resolve(&rup[i].0, &rup[i + 1].0, (pivot.0, &pivot.1));
                        let resolvent: Vec<Rc<Term>> = resolvent_indexset
                            .iter()
                            .map(|(polarity, term)| {
                                if *polarity {
                                    (*term).clone()
                                } else {
                                    Rc::new(Term::Op(Operator::Not, vec![(*term).clone()]))
                                }
                            })
                            .collect();
                        let mut s = DefaultHasher::new();
                        resolvent.hash(&mut s);
                        let resolvent_hash = s.finish();
                        // print!("{} {:?}\n", rup[i].1, rup[i].0);

                        resolutions.push(ResolutionStep::Resolvent(
                            rup[i].1,
                            rup[i + 1].1,
                            (resolvent, resolvent_hash),
                        ));

                        rup[i] = (resolvent_indexset, resolvent_hash);
                    } else {
                        rup[i] = (rup[i + 1].0.clone(), rup[i + 1].1);
                        resolutions.push(ResolutionStep::UnChanged(rup[i + 1].0.clone(), rup[i].1));
                    }
                }

                match &resolutions[resolutions.len() - 1] {
                    ResolutionStep::Resolvent(_, _, (resolvent, _)) =>  {
                        if resolvent.len() > 0 {
                            return Err(CheckerError::DratFormatError(DratFormatError::NoFinalBottomInDrup))
                        }
                    }
                    ResolutionStep::UnChanged(resolvent, _) =>  {
                        if resolvent.len() > 0 {
                            return Err(CheckerError::DratFormatError(DratFormatError::NoFinalBottomInDrup))
                        }                    
                    }
                }

                resolutions.retain(|step| match step {
                    ResolutionStep::Resolvent(_, _, (resolvent, _)) => resolvent.len() > 0 || rup_clause.len() == 0,
                    ResolutionStep::UnChanged(_, _) => false // Since unchanged are trivally avaliable we can ignore them
                });

                print!("{:?}\n", resolutions);

                for (i, resolution_step) in resolutions.iter().enumerate() {
                    let mut action = |x| {
                        if i != resolutions.len() - 1 || arg_index != trace.len() - 1 {
                            elaborator.add_new_step(x)
                        } else {
                            elaborator.push_elaborated_step(x)
                        }
                    };

                    match resolution_step {
                        ResolutionStep::Resolvent(c, d, (resolvent, resolvent_hash)) => {


                            // We check if there is a subsemed clause, in case so, we do the weak
                            let ids = action(ProofStep {
                                id: (*current_id).clone(),
                                clause: resolvent.clone(),
                                rule: "resolution".to_owned(),
                                premises: vec![premises.get(c), premises.get(d)]
                                    .iter()
                                    .flatten()
                                    .map(|x| **x)
                                    .collect(),
                                args: Vec::new(),
                                discharge: Vec::new(),
                            });

                            if i != resolutions.len() - 1 || arg_index != trace.len() - 1 {
                                current_id = Box::new(elaborator.get_new_id(current_id.as_ref()));
                            }
                            premises.insert(*resolvent_hash, ids);
                        }

                        ResolutionStep::UnChanged(_, _) => unreachable!()
                    }
                }
            }

            DRupProofAction::Delete(_) => (),
        }
    }

    // let premises: &mut HashMap<u64, _> = &mut premises
    // .iter()
    // .map(|p| {
    //     let mut s = DefaultHasher::new();
    //     p.clause.hash(&mut s);
    //     (s.finish(), elaborator.map_index(p.index))
    // })
    // .collect();

    // let mut current_id: Box<String> = Box::new(command_id);
    // for (i, arg) in args.iter().enumerate() {
    //     let clause = match arg {
    //         ProofArg::Term(t) => t,
    //         ProofArg::Assign(_, _) => panic!("A invalid term was found while solving drat terms"),
    //     };

    //     let mut action = |x| {
    //         if i != args.len() - 1 {
    //             elaborator.add_new_step(x)
    //         } else {
    //             elaborator.push_elaborated_step(x)
    //         }
    //     };

    //     if let Some(terms) = match_term!((cl ...) = &clause) {
    //         let mut s = DefaultHasher::new();
    //         terms.hash(&mut s);
    //         premises.insert(s.finish(), action(ProofStep {
    //             id: (*current_id).clone(),
    //             clause: terms.to_vec(),
    //             rule: "resolution".to_owned(),
    //             premises: premises.values().map(|x| *x).collect(),
    //             args: Vec::new(),
    //             discharge: Vec::new(),
    //         }));
    //     }

    //     if let Some(terms) = match_term!((delete (cl ...)) = &clause) {
    //         let mut s = DefaultHasher::new();
    //         terms.hash(&mut s);
    //         let hash = s.finish();
    //         premises.remove(&hash);
    //     }

    //     if i != args.len() - 1 {
    //         current_id = Box::new(elaborator.get_new_id(current_id.as_ref()));
    //     }
    // }

    return Ok(());
}
