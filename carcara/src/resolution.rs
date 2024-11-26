use crate::ast::*;
use indexmap::{map::Entry, IndexMap, IndexSet};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ResolutionError {
    #[error("couldn't find tautology in clause")]
    TautologyFailed,

    #[error("pivot was not eliminated: '{0}'")]
    RemainingPivot(Rc<Term>),

    #[error("term in conclusion was not produced by resolution: '{0}'")]
    ExtraTermInConclusion(Rc<Term>),

    #[error("term produced by resolution is missing in conclusion: '{0}'")]
    MissingTermInConclusion(Rc<Term>),

    #[error("pivot was not found in clause: '{0}'")]
    PivotNotFound(Rc<Term>),
}

pub type Literal<'a> = (u32, &'a Rc<Term>);

/// A collection that can be used as a clause during resolution.
pub trait ClauseCollection<'a>: FromIterator<Literal<'a>> {
    fn insert_term(&mut self, item: Literal<'a>);

    fn remove_term(&mut self, item: &Literal<'a>) -> bool;
}

impl<'a> ClauseCollection<'a> for Vec<Literal<'a>> {
    fn insert_term(&mut self, item: Literal<'a>) {
        self.push(item);
    }

    fn remove_term(&mut self, item: &Literal<'a>) -> bool {
        if let Some(pos) = self.iter().position(|x| x == item) {
            self.remove(pos);
            true
        } else {
            false
        }
    }
}

impl<'a> ClauseCollection<'a> for IndexSet<Literal<'a>> {
    fn insert_term(&mut self, item: Literal<'a>) {
        self.insert(item);
    }

    fn remove_term(&mut self, item: &Literal<'a>) -> bool {
        self.remove(item)
    }
}

/// Transformas a `Literal` into an `Rc<Term>`, by undoing the transformation done by
/// `Rc<Term>::remove_all_negations`.
pub fn literal_to_term(pool: &mut dyn TermPool, (n, term): Literal) -> Rc<Term> {
    let mut term = term.clone();
    for _ in 0..n {
        term = build_term!(pool, (not { term }));
    }
    term
}

pub struct ResolutionTrace {
    pub not_not_added: bool,
    pub pivot_trace: Vec<(Rc<Term>, bool)>,
}

pub fn greedy_resolution(
    conclusion: &[Rc<Term>],
    premises: &[&[Rc<Term>]],
    pool: &mut dyn TermPool,
    tracing: bool,
) -> Result<ResolutionTrace, ResolutionError> {
    // If we are elaborating, we record which pivot was found for each binary resolution step, so we
    // can add them all as arguments later
    let mut pivot_trace = Vec::new();

    // When checking this rule, we must look at what the conclusion clause looks like in order to
    // determine the pivots. The reason for that is because there is no other way to know which
    // terms should be removed in a given binary resolution step. Consider the following example,
    // adapted from an actual generated proof:
    //
    //     (step t1 (cl (not q) (not (not p)) (not p)) :rule irrelevant)
    //     (step t2 (cl (not (not (not p))) p) :rule irrelevant)
    //     (step t3 (cl (not q) p (not p)) :rule resolution :premises (t1 t2))
    //
    // Without looking at the conclusion, it is unclear if the (not p) term should be removed by the
    // p term, or if the (not (not p)) should be removed by the (not (not (not p))). We can only
    // determine this by looking at the conclusion and using it to derive the pivots.
    let conclusion: IndexSet<_> = conclusion
        .iter()
        .map(Rc::remove_all_negations)
        .map(|(n, t)| (n as i32, t))
        .collect();

    // The working clause contains the terms from the conclusion clause that we already encountered
    let mut working_clause = IndexSet::new();

    // The pivots are the encountered terms that are not present in the conclusion clause, and so
    // should be removed. After being used to eliminate a term, a pivot can still be used to
    // eliminate other terms. Because of that, we represent the pivots as a hash map to a boolean,
    // which represents if the pivot was already eliminated or not. At the end, this boolean should
    // be true for all pivots
    let mut pivots = IndexMap::new();

    for &premise in premises {
        // Only one pivot may be eliminated per clause. This restriction is required so logically
        // unsound proofs like this one are not considered valid:
        //
        //     (step t1 (cl (= false true) (not false) (not true)) :rule equiv_neg1)
        //     (step t2 (cl (= false true) false true) :rule equiv_neg2)
        //     (step t3 (cl (= false true)) :rule resolution :premises (t1 t2))
        let mut eliminated_clause_pivot = false;
        for term in premise {
            let (n, inner) = term.remove_all_negations();
            let n = n as i32;

            // There are two possible negations of a term, with one leading negation added, or with
            // one leading negation removed (if the term had any in the first place)
            let below = (n - 1, inner);
            let above = (n + 1, inner);

            // First, if the encountered term should be in the conclusion, but is not yet in the
            // working clause, we insert it and don't try to remove it with a pivot
            if conclusion.contains(&(n, inner)) && !working_clause.contains(&(n, inner)) {
                working_clause.insert((n, inner));
                continue;
            }

            // If the negation of the encountered term is present in the pivots set, we simply
            // eliminate it. Otherwise, we insert the encountered term in the working clause or the
            // pivots set, depending on whether it is present in the conclusion clause or not
            let mut try_eliminate = |pivot| match pivots.entry(pivot) {
                Entry::Occupied(mut e) => {
                    e.insert(true);
                    true
                }
                Entry::Vacant(_) => false,
            };

            // Only one pivot may be eliminated per clause, so if we already found this clauses'
            // pivot, we don't try to eliminate the term. If we are elaborating, we add the pivot
            // found to the pivot trace.
            let eliminated = if eliminated_clause_pivot {
                false
            } else if try_eliminate(below) {
                if tracing {
                    pivot_trace.push((literal_to_term(pool, (n as u32 - 1, inner)), true));
                }
                true
            } else if try_eliminate(above) {
                if tracing {
                    pivot_trace.push((term.clone(), false));
                }
                true
            } else {
                false
            };

            if eliminated {
                eliminated_clause_pivot = true;
            } else if conclusion.contains(&(n, inner)) {
                working_clause.insert((n, inner));
            } else {
                // If the term is not in the conclusion clause, it must be a pivot. If it was
                // not already in the pivots set, we insert `false`, to indicate that it was
                // not yet eliminated
                pivots.entry((n, inner)).or_insert(false);
            }
        }
    }

    // There are some special cases in the resolution rules that are valid, but leave a pivot
    // remaining
    let mut remaining_pivots = pivots.iter().filter(|&(_, eliminated)| !eliminated);

    if let Some(((i, pivot), _)) = remaining_pivots.next() {
        if remaining_pivots.next().is_none() {
            // There is a special case in the resolution rules that is valid, but leaves a pivot
            // remaining: when the result of the resolution is just the boolean constant `false`, it
            // may be implicitly eliminated. For example:
            //     (step t1 (cl p q false) :rule hole)
            //     (step t2 (cl (not p)) :rule hole)
            //     (step t3 (cl (not q)) :rule hole)
            //     (step t4 (cl) :rule resolution :premises (t1 t2 t3))
            if conclusion.is_empty() && *i == 0 && pivot.is_bool_false() {
                return Ok(ResolutionTrace { not_not_added: false, pivot_trace });
            }

            // There is another, similar, special case: when the result of the resolution is just
            // one term, it may appear in the conclusion clause with an even number of leading
            // negations added to it. The following is an example of this, adapted from a generated
            // proof:
            //     (step t1 (cl (not e)) :rule hole)
            //     (step t2 (cl (= (not e) (not (not f)))) :rule hole)
            //     (step t3 (cl (not (= (not e) (not (not f)))) e f) :rule hole)
            //     (step t4 (cl (not (not f))) :rule resolution :premises (t1 t2 t3))
            // Usually, we would expect the clause in the t4 step to be (cl f). This behavior may
            // be a bug in veriT, but it is still logically sound and happens often enough that it
            // is useful to support it here.
            if conclusion.len() == 1 {
                let (j, conclusion) = conclusion.into_iter().next().unwrap();
                if conclusion == *pivot && (i % 2) == (j % 2) {
                    return Ok(ResolutionTrace { not_not_added: true, pivot_trace });
                }
            }
        }
        let pivot = literal_to_term(pool, (*i as u32, pivot));
        Err(ResolutionError::RemainingPivot(pivot))
    } else {
        // This is the general case, where all pivots have been eliminated. In this case, the
        // working clause should be equal to the conclusion clause
        for (i, t) in conclusion {
            // By construction, the working clause is a subset of the conclusion. Therefore, we
            // only need to check that all terms in the conclusion are also in the working clause
            if !working_clause.contains(&(i, t)) {
                let t = literal_to_term(pool, (i as u32, t));
                return Err(ResolutionError::ExtraTermInConclusion(t));
            }
        }
        Ok(ResolutionTrace { not_not_added: false, pivot_trace })
    }
}
