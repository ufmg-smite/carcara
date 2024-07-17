use core::panic;

use super::{CheckerError, RuleArgs, RuleResult};
use crate::checker::ProofArg;
use crate::{ast::*, checker::error::ResolutionError};
use indexmap::IndexSet;

fn rup(clauses_set: &Vec<IndexSet<(bool, &Rc<Term>)>>) -> bool {
    let mut clauses = clauses_set.clone();

    loop {
        if clauses.is_empty() {
            return false;
        }
        let smallest = clauses.iter().min_by_key(|c| c.len()).unwrap();
        match smallest.len() {
            0 => return true,
            1 => {
                let literal = *smallest.iter().next().unwrap();
                let negated_literal = (!literal.0, literal.1);

                // Remove all clauses that contain the literal
                clauses.retain(|c| !c.contains(&literal));

                // Remove the negated literal from all clauses that contain it
                for c in &mut clauses {
                    c.remove(&negated_literal);
                }
            }
            _ => return false,
        }
    }
}

pub fn drat(RuleArgs { conclusion, premises, args, .. }: RuleArgs) -> RuleResult {
    let mut premises: Vec<&[Rc<Term>]> = premises
        .iter()
        .map(|p| p.clause)
        .collect::<Vec<&[Rc<Term>]>>();
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

                        premises.retain(|clause| {
                            for term in terms {
                                if !clause.contains(term) {
                                    return true;
                                }
                            }
                            return clause.len() != terms.len();
                        });
                        continue;
                    }
                    None => (),
                }

                let mut premises = premises.clone();
                for clause in &conclusion {
                    premises.push(clause.as_ref());
                }
                
                let mut clauses: Vec<IndexSet<(bool, &Rc<Term>)>> = premises
                    .iter()
                    .map(|p| {
                        p.iter()
                            .map(Rc::remove_all_negations_with_polarity)
                            .collect()
                    })
                    .collect();

                let terms = match match_term!((cl ...) = &t) {
                    Some(terms) => terms,
                    None => panic!("Invalid clause term"),
                };

                for term in terms {
                    let mut clause: IndexSet<(bool, &Rc<Term>)> = IndexSet::new();
                    let (p, regular_term) = term.remove_all_negations_with_polarity();
                    clause.insert((!p, regular_term));
                    clauses.push(clause);
                }

                for clause in &clauses {
                    print!("\n");
                    for c in clause {
                        print!("Clause {0}\n", c.1);
                    }
                }

                if !rup(&clauses) {
                    return Err(CheckerError::Resolution(ResolutionError::TautologyFailed));
                }

                for term in terms {
                    conclusion.push(vec![term.clone()]);
                }
        
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
