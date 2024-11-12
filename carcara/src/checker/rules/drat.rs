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
    RupStory(IndexSet<(bool, &'a Rc<Term>)>, RupAdition<'a>),
    Delete(&'a [Rc<Term>]),
}

type DRupStory<'a> = Vec<DRupProofAction<'a>>;

fn hash_term<T: Borrow<Rc<Term>>>(term: &[T]) -> u64 {
    let mut term = term
        .iter()
        .map(
            |literal| {
                let (p, regular_term) : (bool, &Rc<Term>) = (literal.borrow()).remove_all_negations_with_polarity();
                if p {
                    return regular_term.clone()
                } else {
                    return Rc::new(Term::Op(Operator::Not, vec![(*regular_term).clone()]))
                };
            },
        )
        .collect::<Vec<_>>();

    term.sort_by(|x, y| {
        let mut s = DefaultHasher::new();
        let mut s2 = DefaultHasher::new();
        x.to_string().hash(&mut s);
        y.to_string().hash(&mut s2);

        return s.finish().cmp(&s2.finish());
    });

    let mut s = DefaultHasher::new();
    for literal in term {
        literal.to_string().hash(&mut s);
    }

    let hash = s.finish();
    return hash;
}

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

    let mut unit_story: RupAdition<'a> = vec![];

    let mut clauses: Vec<(
        (Option<(bool, Rc<Term>)>, Option<(bool, Rc<Term>)>),
        (IndexSet<(bool, &'a Rc<Term>)>, u64),
    )> = vec![];

    let mut env: HashMap<(bool, Rc<Term>), bool> = HashMap::new();

    for term in goal {
        let (p, regular_term) = term.remove_all_negations_with_polarity();
        let mut clause: IndexSet<(bool, &Rc<Term>)> = IndexSet::new();
        clause.insert((!p, regular_term));
        clauses.push(((Some((!p, regular_term.clone())), None), (clause, hash_term(vec![term].as_slice()))));
    }

    for (key, clause) in drat_clauses {
        let mut watched_literals = clause.iter().take(2);
        clauses.push((
            (
                watched_literals.next().map(|v| (v.0, (*v.1).clone())),
                watched_literals.next().map(|v| (v.0, (*v.1).clone())),
            ),
            (clause.clone(), *key),
        ));
    }

    loop {
        let unit = get_implied_clause(clauses.borrow_mut(), env.borrow());
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
            (
                hash_term(p),
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
                        premises.remove(&hash_term(terms));
                        drup_history.push(DRupProofAction::Delete(terms));
                        continue;
                    }
                    None => (),
                }

                let terms = match match_term!((cl ...) = &t) {
                    Some(terms) => terms,
                    None => panic!("Invalid clause term"),
                };
;
                let unit_history = rup(premises.borrow(), terms);

                if unit_history == None {
                    return Err(CheckerError::Resolution(ResolutionError::TautologyFailed));
                }

                let terms_indexed_set = terms
                    .iter()
                    .map(Rc::remove_all_negations_with_polarity)
                    .collect::<IndexSet<_>>();

                drup_history.push(DRupProofAction::RupStory(
                    terms_indexed_set.clone(),
                    unit_history.unwrap(),
                ));

                premises.insert(hash_term(terms), terms_indexed_set);
            }
            ProofArg::Assign(_, _) => panic!("A invalid term was found while solving drat terms"),
        }
    }


    if !premises.contains_key(&hash_term(conclusion)) {
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
        Resolvent(
            u64,
            u64,
            (Vec<Rc<Term>>, IndexSet<(bool, &'a Rc<Term>)>, u64),
        ),
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

    let RuleArgs { premises, .. } = rule_args;

    let trace = check_drup(rule_args);

    if let Err(err) = trace {
        return Err(err);
    }

    let premises2: &mut HashMap<u64, _> = &mut premises
        .iter()
        .map(|p| {
            print!("{:?}={:?}\n", hash_term(p.clause), p.clause);
            (hash_term(p.clause), elaborator.map_index(p.index))
        })
        .collect();

    let premises: &mut HashMap<u64, _> = &mut premises
        .iter()
        .map(|p| {
            print!("{:?}={:?}\n", hash_term(p.clause), p.clause);
            (hash_term(p.clause), elaborator.map_index(p.index))
        })
        .collect();

    let mut current_id: String = command_id;
    let mut trace = trace.unwrap();
    trace.retain(|x| match x {
        DRupProofAction::Delete(_) => false,
        _ => true,
    });

    for (arg_index, rup_story) in trace.iter().enumerate() {
        match rup_story {
            DRupProofAction::RupStory(rup_clause, rup_history) => {
                let mut rup: Vec<(IndexSet<(bool, &Rc<Term>)>, u64)> = rup_history
                    .iter()
                    .map(|(vec, _, key)| (vec.clone(), *key))
                    .collect();
                let pivots: Vec<_> = rup_history.iter().map(|(_, term, _)| term).collect();

                // print!("Solving {:?}\n", rup_clause);
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

                        let resolvent_hash = hash_term(resolvent.as_slice());
                        print!("needs {:?} = {:?}\n", resolvent, resolvent_hash);

                        // print!(
                        //     "{:?}={:?}\n{:?}={:?}\n",
                        //     rup[i].1,
                        //     rup[i].0.clone(),
                        //     rup[i + 1].1,
                        //     rup[i + 1].0.clone()
                        // );
                        resolutions.push(ResolutionStep::Resolvent(
                            rup[i].1,
                            rup[i + 1].1,
                            (resolvent, resolvent_indexset.clone(), resolvent_hash),
                        ));

                        print!(
                            "{:?} = {:?} \n{:?} = {:?}\n",
                            rup[i].0,
                            rup[i].1,
                            rup[i + 1].0,
                            rup[i + 1].1
                        );

                        rup[i] = (resolvent_indexset, resolvent_hash);
                    } else {
                        rup[i] = (rup[i + 1].0.clone(), rup[i + 1].1);
                        resolutions.push(ResolutionStep::UnChanged(rup[i + 1].0.clone(), rup[i].1));
                    }
                }

                match &resolutions[resolutions.len() - 1] {
                    ResolutionStep::Resolvent(_, _, (resolvent, _, _)) => {
                        if resolvent.len() > 0 {
                            return Err(CheckerError::DratFormatError(
                                DratFormatError::NoFinalBottomInDrup,
                            ));
                        }
                    }
                    ResolutionStep::UnChanged(resolvent, _) => {
                        if resolvent.len() > 0 {
                            return Err(CheckerError::DratFormatError(
                                DratFormatError::NoFinalBottomInDrup,
                            ));
                        }
                    }
                }

                resolutions.retain(|step| match step {
                    ResolutionStep::Resolvent(_, _, (resolvent, _, _)) => {
                        resolvent.len() > 0 || rup_clause.len() == 0
                    }
                    ResolutionStep::UnChanged(_, _) => false, // Since unchanged are trivally avaliable we can ignore them
                });

                for (i, resolution_step) in resolutions.iter().enumerate() {
                    let mut action = |x| {
                        if i != resolutions.len() - 1 || arg_index != trace.len() - 1 {
                            elaborator.add_new_step(x)
                        } else {
                            elaborator.push_elaborated_step(x)
                        }
                    };

                    match resolution_step {
                        ResolutionStep::Resolvent(
                            c,
                            d,
                            (resolvent, resolvent_indexset, resolvent_hash),
                        ) => {
                            print!(
                                "{:?} = {:?} {:?} x {:?} {:?}\n",
                                resolvent,
                                c,
                                premises.get(c),
                                d,
                                premises.get(d)
                            );
                            print!("{:?}\n", premises);

                            let mut clause = resolvent.clone();
                            let mut hash = *resolvent_hash;

                            // TODO: This is something that I have to ask @Haniel
                            // if !premises.contains_key(c) || !premises.contains_key(d) {
                            //     return Err(CheckerError::DratFormatError(
                            //         DratFormatError::PotentialNoDrupFormat,
                            //     ));
                            // }

                            if i == resolutions.len() - 1
                                && resolvent_indexset.is_subset(rup_clause)
                            {
                                clause = rup_clause
                                    .iter()
                                    .map(|(polarity, term)| {
                                        if *polarity {
                                            (*term).clone()
                                        } else {
                                            Rc::new(Term::Op(Operator::Not, vec![(*term).clone()]))
                                        }
                                    })
                                    .collect();
                                hash = hash_term(clause.as_slice());
                            }

                            let ids = action(ProofStep {
                                id: current_id.clone(),
                                clause: clause,
                                rule: "resolution".to_owned(),
                                premises: vec![
                                    *premises.get(c).unwrap(),
                                    *premises.get(d).unwrap(),
                                ],
                                args: Vec::new(),
                                discharge: Vec::new(),
                            });

                            if i != resolutions.len() - 1 || arg_index != trace.len() - 1 {
                                current_id = elaborator.get_new_id(current_id.as_ref());
                            }

                            premises.insert(hash, ids);
                            print!("{:?} new {:?}\n", hash, resolvent);
                        }

                        ResolutionStep::UnChanged(_, _) => unreachable!(),
                    }
                }
            }

            DRupProofAction::Delete(_) => unreachable!(),
        }
    }

    return Ok(());
}
