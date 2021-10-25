use super::{get_single_term_from_command, RuleArgs};
use crate::ast::*;

/// Function to find a transitive chain given a conclusion equality and a series of premise
/// equalities.
fn find_chain(
    conclusion: (&Rc<Term>, &Rc<Term>),
    premises: &mut [(&Rc<Term>, &Rc<Term>)],
) -> Option<()> {
    // When the conclusion is of the form (= a a), it is trivially valid
    if conclusion.0 == conclusion.1 {
        return Some(());
    }

    // Find in the premises, if it exists, an equality such that one of its terms is equal to the
    // first term in the conclusion. Possibly reorder this equality so the matching term is the
    // first one
    let (index, eq) = premises.iter().enumerate().find_map(|(i, &(t, u))| {
        if t == conclusion.0 {
            Some((i, (t, u)))
        } else if u == conclusion.0 {
            Some((i, (u, t)))
        } else {
            None
        }
    })?;

    // We remove the found equality by swapping it with the first element in `premises`.  The new
    // premises will then be all elements after the first
    premises.swap(0, index);

    // The new conclusion will be the terms in the conclusion and the found equality that didn't
    // match. For example, if the conclusion was (= a d) and we found in the premises (= a b), the
    // new conclusion will be (= b d)
    find_chain((eq.1, conclusion.1), &mut premises[1..])
}

pub fn eq_transitive(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    if conclusion.len() < 3 {
        return None;
    }

    // The last term in the conclusion clause should be an equality, and it will be the conclusion
    // of the transitive chain
    let chain_conclusion = match_term!((= t u) = conclusion.last().unwrap())?;

    // The first `conclusion.len()` - 1 terms in the conclusion clause must be a sequence of
    // inequalites, and they will be the premises of the transitive chain
    let mut premises = Vec::with_capacity(conclusion.len() - 1);
    for term in &conclusion[..conclusion.len() - 1] {
        let (t, u) = match_term!((not (= t u)) = term)?;
        premises.push((t, u));
    }

    find_chain(chain_conclusion, &mut premises)
}

pub fn trans(RuleArgs { conclusion, premises, .. }: RuleArgs) -> Option<()> {
    if conclusion.len() != 1 {
        return None;
    }

    let conclusion = match_term!((= t u) = conclusion[0])?;
    let mut premises: Vec<_> = premises
        .into_iter()
        .map(|command| {
            let term = get_single_term_from_command(command)?;
            match_term!((= t u) = term)
        })
        .collect::<Option<_>>()?;

    find_chain(conclusion, &mut premises)
}

#[cfg(test)]
mod tests {
    #[test]
    fn eq_transitive() {
        test_cases! {
            definitions = "
                (declare-sort T 0)
                (declare-fun a () T)
                (declare-fun b () T)
                (declare-fun c () T)
                (declare-fun d () T)
                (declare-fun e () T)
            ",
            "Simple working examples" {
                "(step t1 (cl (not (= a b)) (not (= b c)) (= a c)) :rule eq_transitive)": true,

                "(step t1 (cl (not (= a b)) (not (= b c)) (not (= c d)) (= a d))
                    :rule eq_transitive)": true,

                "(step t1 (cl (not (= a a)) (not (= a a)) (= a a)) :rule eq_transitive)": true,
            }
            "Inequality terms in different orders" {
                "(step t1 (cl (not (= a b)) (not (= c b)) (not (= c d)) (= d a))
                    :rule eq_transitive)": true,

                "(step t1 (cl (not (= b a)) (not (= c b)) (not (= d c)) (= a d))
                    :rule eq_transitive)": true,
            }
            "Clause term is not an inequality" {
                "(step t1 (cl (= a b) (not (= b c)) (= a c)) :rule eq_transitive)": false,

                "(step t1 (cl (not (= a b)) (= b c) (= a c)) :rule eq_transitive)": false,
            }
            "Final term is not an equality" {
                "(step t1 (cl (not (= a b)) (not (= b c)) (not (= a c)))
                    :rule eq_transitive)": false,
            }
            "Clause is too small" {
                "(step t1 (cl (not (= a b)) (= a b)) :rule eq_transitive)": false,
            }
            "Clause terms in different orders" {
                "(step t1 (cl (not (= a b)) (not (= c d)) (not (= b c)) (= a d))
                    :rule eq_transitive)": true,

                "(step t1 (cl (not (= c d)) (not (= b c)) (not (= a b)) (= a d))
                    :rule eq_transitive)": true,
            }
            "Clause doesn't form transitive chain" {
                "(step t1 (cl (not (= a b)) (not (= c d)) (= a d)) :rule eq_transitive)": false,

                "(step t1 (cl (not (= a b)) (not (= b b)) (not (= c d)) (= a d))
                    :rule eq_transitive)": false,

                "(step t1 (cl (not (= a b)) (not (= b c)) (not (= c d)) (= a e))
                    :rule eq_transitive)": false,

                "(step t1 (cl (not (= a b)) (not (= b e)) (not (= b c)) (= a c))
                    :rule eq_transitive)": false,
            }
        }
    }

    #[test]
    fn trans() {
        test_cases! {
            definitions = "
                (declare-sort T 0)
                (declare-fun a () T)
                (declare-fun b () T)
                (declare-fun c () T)
                (declare-fun d () T)
                (declare-fun e () T)
            ",
            "Simple working examples" {
                "(assume h1 (= a b)) (assume h2 (= b c))
                (step t3 (cl (= a c)) :rule trans :premises (h1 h2))": true,

                "(assume h1 (= a b)) (assume h2 (= b c)) (assume h3 (= c d))
                (step t4 (cl (= a d)) :rule trans :premises (h1 h2 h3))": true,

                "(assume h1 (= a a))
                (step t2 (cl (= a a)) :rule trans :premises (h1))": true,
            }
            "Premises in different orders" {
                "(assume h1 (= a b)) (assume h2 (= c d)) (assume h3 (= b c))
                (step t4 (cl (= a d)) :rule trans :premises (h1 h2 h3))": true,

                "(assume h1 (= c d)) (assume h2 (= b c)) (assume h3 (= a b))
                (step t4 (cl (= a d)) :rule trans :premises (h1 h2 h3))": true,
            }
            "Prmise term is not an equality" {
                "(assume h1 (= a b)) (assume h2 (not (= b c))) (assume h3 (= c d))
                (step t4 (cl (= a d)) :rule trans :premises (h1 h2 h3))": false,
            }
            "Conclusion clause is of the wrong form" {
                "(assume h1 (= a b)) (assume h2 (= b c))
                (step t3 (cl (not (= a c))) :rule trans :premises (h1 h2))": false,

                "(assume h1 (= a b)) (assume h2 (= b c))
                (step t3 (cl (= a c) (= c a)) :rule trans :premises (h1 h2))": false,
            }
        }
    }
}
