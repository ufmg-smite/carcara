use core::panic;
use std::borrow::{Borrow};
use std::hash::{DefaultHasher, Hash, Hasher};

use super::{CheckerError, RuleArgs, RuleResult};
use crate::checker::error::DratFormatError;
use crate::checker::ProofArg;
use crate::{ast::*, checker::error::ResolutionError};
use indexmap::IndexSet;
use std::collections::HashMap;

fn rup(
    clauses: &HashMap<u64, IndexSet<(bool, &Rc<Term>)>>,
    goal_hash: u64,
    goal: &[Rc<Term>],
) -> bool {
    let mut clauses: HashMap<u64, IndexSet<(bool, &Rc<Term>)>> = clauses.clone();

    for term in goal {
        let mut clause: IndexSet<(bool, &Rc<Term>)> = IndexSet::new();
        let (p, regular_term) = term.remove_all_negations_with_polarity();
        clause.insert((!p, regular_term));
        clauses.insert(goal_hash, clause);
    }

    loop {
        if clauses.is_empty() {
            return false;
        }
        let smallest = clauses.iter().min_by_key(|c| c.1.len()).unwrap();
        match smallest.1.len() {
            0 => return true,
            1 => {
                println!("Before");
                for (_, index_set) in  clauses.clone() {
                    for clause in index_set {
                        print!("{1}({0}) ", clause.1, if clause.0 {""} else {"not"});
                    }
                    println!("");
                }
                println!("");

                let literal = *smallest.1.iter().next().unwrap();
                let negated_literal = (!literal.0, literal.1);

                print!("Propagating {0} {1}\n", literal.1, literal.0);

                // Remove all clauses that contain the literal
                clauses.retain(|_, v| !v.contains(&literal));

                // Remove the negated literal from all clauses that contain it
                for c in &mut clauses {
                    c.1.remove(&negated_literal);
                }
                println!("After");

                for (_, index_set) in clauses.clone() {
                    if index_set.is_empty() {
                     print!("!Bottom");
                     continue;   
                    }

                    for clause in index_set {
                        print!("{1}({0}) ", clause.1, if clause.0 {""} else {"not"});
                    }
                    println!("");
                }
                println!("");
            }
            _ => return false,
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
                // print!("Checking {0}\n", t);
                match match_term!((delete (cl ...)) = &t) {
                    Some(terms) => {
                        // print!(
                        //     "Delete {0}\n",
                        //     terms
                        //         .iter()
                        //         .map(|x| x.to_string())
                        //         .collect::<Vec<String>>()
                        //         .join(" | ")
                        // );
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
        return Err(CheckerError::DratFormatError(DratFormatError::NoConclusionInPremise));
    }

    Ok(())
}
