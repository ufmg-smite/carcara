use core::panic;
use std::borrow::BorrowMut;
use std::hash::{DefaultHasher, Hash, Hasher};

use super::{CheckerError, RuleArgs, RuleResult};
use crate::checker::ProofArg;
use crate::{ast::*, checker::error::ResolutionError};
use indexmap::IndexSet;
use std::collections::{HashMap};

fn rup(clauses: HashMap<u64, IndexSet<(bool, &Rc<Term>)>>) -> bool {
    let mut clauses: HashMap<u64, IndexSet<(bool, &Rc<Term>)>> = clauses.clone();

    loop {
        if clauses.is_empty() {
            return false;
        }
        let smallest = clauses.iter().min_by_key(|c| c.1.len()).unwrap();
        match smallest.1.len() {
            0 => return true,
            1 => {
                let literal = *smallest.1.iter().next().unwrap();
                let negated_literal = (!literal.0, literal.1);

                // Remove all clauses that contain the literal
                let filtered : Vec<_> = clauses.iter().filter(|c| c.1.contains(&literal)).map(|(k, _)| k.clone()).collect();
                for key in filtered {
                    clauses.remove(&key);
                }

                // Remove the negated literal from all clauses that contain it
                for c in &mut clauses {
                    c.1.remove(&negated_literal);
                }
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

    let mut conclusion: Vec<Vec<Rc<Term>>> = Vec::new();

    for arg in args {
        match arg {
            ProofArg::Term(t) => {
                print!("Checking {0}\n", t);
                match match_term!((delete (cl ...)) = &t) {
                    Some(terms) => {
                        print!(
                            "Delete {0}\n",
                            terms
                                .iter()
                                .map(|x| x.to_string())
                                .collect::<Vec<String>>()
                                .join(" | ")
                        );
                        let mut s = DefaultHasher::new();
                        terms.hash(&mut s);
                        premises.remove(&s.finish());
                        continue;
                    }
                    None => (),
                }

                let mut clauses = premises.clone();
                let terms = match match_term!((cl ...) = &t) {
                    Some(terms) => terms,
                    None => panic!("Invalid clause term"),
                };

                let mut s = DefaultHasher::new();
                terms.hash(&mut s);
                let hash_term = s.finish();

                for term in terms {
                    let mut clause: IndexSet<(bool, &Rc<Term>)> = IndexSet::new();
                    let (p, regular_term) = term.remove_all_negations_with_polarity();
                    clause.insert((!p, regular_term));
                    clauses.insert(hash_term, clause);
                }

                for clause in &clauses {
                    print!("\n");
                    for c in clause.1 {
                        print!("Clause {0}\n", c.1);
                    }
                }

                if !rup(clauses) {
                    return Err(CheckerError::Resolution(ResolutionError::TautologyFailed));
                }

                for term in terms {
                    conclusion.push(vec![term.clone()]);
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

    // - the initial clause set is the premises (build it as what is
    //   expected in the above function)
    // - for each argument:
    //   - if it is *not* a deletion, then show that you can conclude
    //     the respective clause from the current clause set via
    //     RUP. Add the argument to the clause set.
    //   - if it is a deletion: delete that clause from the clause_set
    // - Once all arguments have been processed, you are done as long
    //   as the empty clause has been added to the clause set.
    Ok(())
}
