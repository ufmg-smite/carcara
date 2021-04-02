mod tests;

use std::rc::Rc;

use crate::parser::ast::*;

pub type Rule = fn(&[Rc<Term>], Vec<&ProofCommand>, &[ProofArg]) -> bool;

pub struct ProofChecker {
    proof: Proof,
}

impl ProofChecker {
    pub fn new(proof: Proof) -> Self {
        ProofChecker { proof }
    }

    pub fn check(self) -> bool {
        for step in &self.proof.0 {
            if let ProofCommand::Step {
                clause,
                rule,
                premises,
                args,
            } = step
            {
                let rule = Self::get_rule(rule);
                let premises = premises.iter().map(|&i| &self.proof.0[i]).collect();
                if !rule(&clause, premises, &args) {
                    return false;
                }
            }
        }
        true
    }

    fn get_rule(rule_name: &str) -> Rule {
        match rule_name {
            "or" => rules::or,
            "eq_transitive" => rules::eq_transitive,
            "eq_congruent" => rules::eq_congruent,
            "resolution" | "th_resolution" => rules::resolution,
            _ => todo!(),
        }
    }
}

/// A macro to help deconstruct operation terms. Since a term holds references to other terms in
/// `Vec`s and `Rc`s, pattern matching a complex term can be difficult and verbose. This macro
/// helps with that.
macro_rules! match_op {
    ($bind:ident = $var:expr) => {
        Some($var)
    };
    (($op:tt $($args:tt)+) = $var:expr) => {{
        let _: &Term = $var;
        if let Term::Op(match_op!(@GET_VARIANT $op), args) = $var {
            match_op!(@ARGS ($($args)+) = args.as_slice())
        } else {
            None
        }
    }};
    (@ARGS ($arg:tt) = $var:expr) => {
        if let [arg] = $var {
            match_op!($arg = arg.as_ref())
        } else {
            None
        }
    };
    (@ARGS ($arg1:tt $arg2:tt) = $var:expr) => {
        if let [arg1, arg2] = $var {
            match (match_op!($arg1 = arg1.as_ref()), match_op!($arg2 = arg2.as_ref())) {
                (Some(arg1), Some(arg2)) => Some((arg1, arg2)),
                _ => None,
            }
        } else {
            None
        }
    };
    (@GET_VARIANT not) => { Operator::Not };
    (@GET_VARIANT =) => { Operator::Eq };
}

// Macros can only be used after they're declared, so we can't put this test in the "tests" module,
// as that module is declared in the top of the file. Instead of moving the module delcaration to
// after the macro declaration, it's easier to just bring this single test here.
#[cfg(test)]
#[test]
fn test_match_op() {
    use crate::parser::tests::parse_term;

    let true_term = parse_term("true");
    let false_term = parse_term("false");
    let term = parse_term("(= (= (not false) (= true false)) (not true))");
    assert_eq!(
        match_op!((= (= (not a) (= b c)) (not d)) = &term),
        Some(((&false_term, (&true_term, &false_term)), &true_term)),
    );
}

mod rules {
    use super::*;
    use std::collections::HashSet;

    pub fn or(clause: &[Rc<Term>], premises: Vec<&ProofCommand>, _: &[ProofArg]) -> bool {
        if premises.len() != 1 {
            return false;
        }
        let or_term = match premises[0] {
            ProofCommand::Assume(cl) => cl,
            ProofCommand::Step { clause, .. } => {
                if clause.len() == 1 {
                    &clause[0]
                } else {
                    return false;
                }
            }
        };
        let or_contents = if let Term::Op(Operator::Or, args) = or_term.as_ref() {
            args
        } else {
            return false;
        };

        or_contents == clause
    }

    pub fn eq_transitive(clause: &[Rc<Term>], _: Vec<&ProofCommand>, _: &[ProofArg]) -> bool {
        /// Recursive function to find a transitive chain given a conclusion equality and a series
        /// of premise equalities.
        fn find_chain(conclusion: (&Term, &Term), premises: &mut [(&Term, &Term)]) -> bool {
            // When the conclusion is of the form (= a a), it is trivially valid
            if conclusion.0 == conclusion.1 {
                return true;
            }

            // Find in the premises, if it exists, an equality such that one of its terms is equal
            // to the first term in the conclusion. Possibly reorder this equality so the matching
            // term is the first one
            let found = premises.iter().enumerate().find_map(|(i, &(t, u))| {
                if t == conclusion.0 {
                    Some((i, (t, u)))
                } else if u == conclusion.0 {
                    Some((i, (u, t)))
                } else {
                    None
                }
            });

            if let Some((index, eq)) = found {
                // We remove the found equality by swapping it with the first element in
                // `premises`. The new premises will then be all elements after the first
                premises.swap(0, index);

                // The new conclusion will be the terms in the conclusion and the found equality
                // that didn't match. For example, if the conclusion was (= a d) and we found in
                // the premises (= a b), the new conclusion will be (= b d)
                find_chain((eq.1, conclusion.1), &mut premises[1..])
            } else {
                false
            }
        }

        if clause.len() < 3 {
            return false;
        }

        // The last term in clause should be an equality, and it will be the conclusion of the
        // transitive chain
        let last_term = clause.last().unwrap().as_ref();
        let conclusion = if let Some(equality) = match_op!((= t u) = last_term) {
            equality
        } else {
            return false;
        };

        // The first `clause.len()` - 1 terms in the clause must be a sequence of inequalites, and
        // they will be the premises of the transitive chain
        let mut premises = Vec::with_capacity(clause.len() - 1);
        for term in &clause[..clause.len() - 1] {
            if let Some((t, u)) = match_op!((not (= t u)) = term.as_ref()) {
                premises.push((t, u));
            } else {
                return false;
            }
        }

        find_chain(conclusion, &mut premises)
    }

    pub fn eq_congruent(clause: &[Rc<Term>], _: Vec<&ProofCommand>, _: &[ProofArg]) -> bool {
        if clause.len() < 2 {
            return false;
        }

        // The first `clause.len()` - 1 terms in the clause must be a sequence of inequalites
        let mut ts = Vec::new();
        let mut us = Vec::new();
        for term in &clause[..clause.len() - 1] {
            if let Some((t, u)) = match_op!((not (= t u)) = term.as_ref()) {
                ts.push(t);
                us.push(u);
            } else {
                return false;
            }
        }

        // The final term in the clause must be an equality of two function applications, whose
        // arguments are the terms in the previous inequalities
        match match_op!((= f g) = clause.last().unwrap().as_ref()) {
            Some((Term::App(f, f_args), Term::App(g, g_args))) => {
                if f != g || f_args.len() != ts.len() {
                    return false;
                }
                for i in 0..ts.len() {
                    if f_args[i].as_ref() != ts[i] || g_args[i].as_ref() != us[i] {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }

    pub fn resolution(clause: &[Rc<Term>], premises: Vec<&ProofCommand>, _: &[ProofArg]) -> bool {
        /// Removes all leading negations in a term and returns how many there were.
        fn remove_negations(mut term: &Term) -> (u32, &Term) {
            let mut n = 0;
            while let Some(t) = match_op!((not t) = term) {
                term = t;
                n += 1;
            }
            (n, term)
        }

        // This set represents the current working clause, where (n, t) represents the term t with
        // n leading negations.
        let mut working_clause: HashSet<(u32, &Term)> = HashSet::new();

        // For every term t in each premise, we check if (not t) is in the working clause, and if
        // it is, we remove it. If t is of the form (not u), we do the same for u. If neither one
        // was removed, we insert t into the working clause.
        for command in premises.into_iter() {
            let premise_clause = match command {
                // "assume" premises are interpreted as a clause with a single term
                ProofCommand::Assume(term) => std::slice::from_ref(term),
                ProofCommand::Step { clause, .. } => &clause,
            };
            for term in premise_clause {
                let (n, inner) = remove_negations(term.as_ref());

                // Remove the entry for (n - 1, inner) if it exists
                if !(n > 0 && working_clause.remove(&(n - 1, inner))) {
                    // If it didn't exist, try the same for (n + 1, inner)
                    if !working_clause.remove(&(n + 1, inner)) {
                        // If neither entry exists, insert (n, inner)
                        working_clause.insert((n, inner));
                    }
                }
            }
        }

        // At the end, we expect the working clause to be equal to the conclusion clause
        if clause.len() != working_clause.len() {
            return false;
        }
        for term in clause {
            if !working_clause.contains(&remove_negations(term.as_ref())) {
                return false;
            }
        }

        true
    }
}
