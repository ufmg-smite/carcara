mod tests;

use crate::ast::*;

pub type Rule = fn(&[ByRefRc<Term>], Vec<&ProofCommand>, &[ProofArg]) -> Option<()>;

pub enum CheckerError<'a> {
    UnknownRule(&'a str),
    FailedOnRule(&'a str),
}

pub struct ProofChecker {
    proof: Proof,
}

impl ProofChecker {
    pub fn new(proof: Proof) -> Self {
        ProofChecker { proof }
    }

    pub fn check(&self) -> Result<(), CheckerError> {
        for step in &self.proof.0 {
            if let ProofCommand::Step {
                clause,
                rule: rule_name,
                premises,
                args,
            } = step
            {
                let rule = Self::get_rule(rule_name).ok_or(CheckerError::UnknownRule(rule_name))?;
                let premises = premises.iter().map(|&i| &self.proof.0[i]).collect();
                if rule(&clause, premises, &args).is_none() {
                    return Err(CheckerError::FailedOnRule(rule_name));
                }
            }
        }
        Ok(())
    }

    pub fn get_rule(rule_name: &str) -> Option<Rule> {
        Some(match rule_name {
            "not_not" => rules::not_not,
            "equiv_pos1" => rules::equiv_pos1,
            "equiv_pos2" => rules::equiv_pos2,
            "eq_reflexive" => rules::eq_reflexive,
            "eq_transitive" => rules::eq_transitive,
            "eq_congruent" => rules::eq_congruent,
            "eq_congruent_pred" => rules::eq_congruent_pred,
            "distinct_elim" => rules::distinct_elim,
            "th_resolution" | "resolution" => rules::resolution,
            "and" => rules::and,
            "or" => rules::or,
            "implies" => rules::implies,
            "ite1" => rules::ite1,
            "ite2" => rules::ite2,
            "ite_intro" => rules::ite_intro,
            "contraction" => rules::contraction,
            _ => return None,
        })
    }
}

mod rules {
    use super::*;
    use std::collections::HashSet;

    /// Converts a `bool` into an `Option<()>`.
    fn to_option(b: bool) -> Option<()> {
        match b {
            true => Some(()),
            false => None,
        }
    }

    fn get_single_term_from_command(command: &ProofCommand) -> Option<&ByRefRc<Term>> {
        match command {
            ProofCommand::Assume(term) => Some(term),
            ProofCommand::Step { clause, .. } if clause.len() == 1 => Some(&clause[0]),
            _ => None,
        }
    }

    pub fn not_not(clause: &[ByRefRc<Term>], _: Vec<&ProofCommand>, _: &[ProofArg]) -> Option<()> {
        if clause.len() != 2 {
            return None;
        }
        let p = match_term!((not (not (not p))) = clause[0].as_ref())?;
        let q = clause[1].as_ref();
        to_option(p == q)
    }

    pub fn equiv_pos1(
        clause: &[ByRefRc<Term>],
        _: Vec<&ProofCommand>,
        _: &[ProofArg],
    ) -> Option<()> {
        if clause.len() != 3 {
            return None;
        }
        let (phi_1, phi_2) = match_term!((not (= phi_1 phi_2)) = clause[0].as_ref())?;
        to_option(
            phi_1 == clause[1].as_ref() && phi_2 == match_term!((not phi_2) = clause[2].as_ref())?,
        )
    }

    pub fn equiv_pos2(
        clause: &[ByRefRc<Term>],
        _: Vec<&ProofCommand>,
        _: &[ProofArg],
    ) -> Option<()> {
        if clause.len() != 3 {
            return None;
        }
        let (phi_1, phi_2) = match_term!((not (= phi_1 phi_2)) = clause[0].as_ref())?;
        to_option(
            phi_1 == match_term!((not phi_1) = clause[1].as_ref())? && phi_2 == clause[2].as_ref(),
        )
    }

    pub fn eq_reflexive(
        clause: &[ByRefRc<Term>],
        _: Vec<&ProofCommand>,
        _: &[ProofArg],
    ) -> Option<()> {
        if clause.len() == 1 {
            let (a, b) = match_term!((= a b) = clause[0].as_ref())?;
            to_option(a == b)
        } else {
            None
        }
    }

    pub fn eq_transitive(
        clause: &[ByRefRc<Term>],
        _: Vec<&ProofCommand>,
        _: &[ProofArg],
    ) -> Option<()> {
        /// Recursive function to find a transitive chain given a conclusion equality and a series
        /// of premise equalities.
        fn find_chain(conclusion: (&Term, &Term), premises: &mut [(&Term, &Term)]) -> Option<()> {
            // When the conclusion is of the form (= a a), it is trivially valid
            if conclusion.0 == conclusion.1 {
                return Some(());
            }

            // Find in the premises, if it exists, an equality such that one of its terms is equal
            // to the first term in the conclusion. Possibly reorder this equality so the matching
            // term is the first one
            let (index, eq) = premises.iter().enumerate().find_map(|(i, &(t, u))| {
                if t == conclusion.0 {
                    Some((i, (t, u)))
                } else if u == conclusion.0 {
                    Some((i, (u, t)))
                } else {
                    None
                }
            })?;

            // We remove the found equality by swapping it with the first element in `premises`.
            // The new premises will then be all elements after the first
            premises.swap(0, index);

            // The new conclusion will be the terms in the conclusion and the found equality that
            // didn't match. For example, if the conclusion was (= a d) and we found in the
            // premises (= a b), the new conclusion will be (= b d)
            find_chain((eq.1, conclusion.1), &mut premises[1..])
        }

        if clause.len() < 3 {
            return None;
        }

        // The last term in clause should be an equality, and it will be the conclusion of the
        // transitive chain
        let last_term = clause.last().unwrap().as_ref();
        let conclusion = match_term!((= t u) = last_term)?;

        // The first `clause.len()` - 1 terms in the clause must be a sequence of inequalites, and
        // they will be the premises of the transitive chain
        let mut premises = Vec::with_capacity(clause.len() - 1);
        for term in &clause[..clause.len() - 1] {
            let (t, u) = match_term!((not (= t u)) = term.as_ref())?;
            premises.push((t, u));
        }

        find_chain(conclusion, &mut premises)
    }

    pub fn eq_congruent(
        clause: &[ByRefRc<Term>],
        _: Vec<&ProofCommand>,
        _: &[ProofArg],
    ) -> Option<()> {
        if clause.len() < 2 {
            return None;
        }
        let premises = clause[..clause.len() - 1]
            .iter()
            .map(|t| match_term!((not t) = t.as_ref()));
        let conclusion = match_term!((= f g) = clause.last().unwrap().as_ref())?;

        generic_congruent_rule(premises, conclusion)
    }

    pub fn eq_congruent_pred(
        clause: &[ByRefRc<Term>],
        _: Vec<&ProofCommand>,
        _: &[ProofArg],
    ) -> Option<()> {
        if clause.len() < 3 {
            return None;
        }
        let premises = clause[..clause.len() - 2]
            .iter()
            .map(|t| match_term!((not t) = t.as_ref()));
        let conclusion = (
            match_term!((not t) = clause[clause.len() - 2].as_ref())?,
            clause[clause.len() - 1].as_ref(),
        );

        generic_congruent_rule(premises, conclusion)
    }

    /// A function to check congruency. Useful for the "eq_congruent", "eq_congruent_pred" and
    /// "cong" rules. `premises` should be an iterator over the argument equalities, and
    /// `conclusion` should be the two function applications.
    fn generic_congruent_rule<'a, T>(premises: T, conclusion: (&Term, &Term)) -> Option<()>
    where
        T: Iterator<Item = Option<&'a Term>>,
    {
        let mut ts = Vec::new();
        let mut us = Vec::new();
        for term in premises {
            let (t, u) = match_term!((= t u) = term.as_ref()?)?;
            ts.push(t);
            us.push(u);
        }

        match conclusion {
            (Term::App(f, f_args), Term::App(g, g_args)) => {
                if f != g || f_args.len() != ts.len() {
                    return None;
                }
                for i in 0..ts.len() {
                    let expected = (f_args[i].as_ref(), g_args[i].as_ref());
                    if expected != (ts[i], us[i]) && expected != (us[i], ts[i]) {
                        return None;
                    }
                }
                Some(())
            }
            _ => None,
        }
    }

    pub fn distinct_elim(
        clause: &[ByRefRc<Term>],
        _: Vec<&ProofCommand>,
        _: &[ProofArg],
    ) -> Option<()> {
        if clause.len() != 1 {
            return None;
        }

        let (distinct_term, second_term) = match_term!((= a b) = clause[0].as_ref())?;
        let distinct_args = match distinct_term {
            Term::Op(Operator::Distinct, args) => args,
            _ => return None,
        };
        match distinct_args.as_slice() {
            [] | [_] => unreachable!(),
            [a, b] => {
                let got: (&Term, &Term) = match_term!((not (= x y)) = second_term)?;
                to_option(got == (a, b) || got == (b, a))
            }
            args => {
                if args[0].sort() == Term::BOOL_SORT {
                    // If there are more than two boolean arguments to the distinct operator, the
                    // second term must be "false"
                    return match second_term {
                        Term::Terminal(Terminal::Var(Identifier::Simple(s), _)) if s == "false" => {
                            Some(())
                        }
                        _ => None,
                    };
                }
                let got = match second_term {
                    Term::Op(Operator::And, args) => args,
                    _ => return None,
                };
                let mut k = 0;
                for i in 0..args.len() {
                    for j in i + 1..args.len() {
                        let (a, b) = (args[i].as_ref(), args[j].as_ref());
                        let got: (&Term, &Term) = match_term!((not (= x y)) = got[k].as_ref())?;
                        to_option(got == (a, b) || got == (b, a))?;
                        k += 1;
                    }
                }
                Some(())
            }
        }
    }

    pub fn resolution(
        clause: &[ByRefRc<Term>],
        premises: Vec<&ProofCommand>,
        _: &[ProofArg],
    ) -> Option<()> {
        /// Removes all leading negations in a term and returns how many there were.
        fn remove_negations(mut term: &Term) -> (u32, &Term) {
            let mut n = 0;
            while let Some(t) = match_term!((not t) = term) {
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
        let clause: HashSet<_> = clause
            .iter()
            .map(|t| remove_negations(t.as_ref()))
            .collect();

        to_option(working_clause == clause)
    }

    pub fn and(
        clause: &[ByRefRc<Term>],
        premises: Vec<&ProofCommand>,
        _: &[ProofArg],
    ) -> Option<()> {
        if premises.len() != 1 || clause.len() != 1 {
            return None;
        }
        let and_term = get_single_term_from_command(premises[0])?;
        let and_contents = match and_term.as_ref() {
            Term::Op(Operator::And, args) => args,
            _ => return None,
        };

        to_option(and_contents.iter().any(|t| t == &clause[0]))
    }

    pub fn or(
        clause: &[ByRefRc<Term>],
        premises: Vec<&ProofCommand>,
        _: &[ProofArg],
    ) -> Option<()> {
        if premises.len() != 1 {
            return None;
        }
        let or_term = get_single_term_from_command(premises[0])?;
        let or_contents = match or_term.as_ref() {
            Term::Op(Operator::Or, args) => args,
            _ => return None,
        };

        to_option(or_contents == clause)
    }

    pub fn implies(
        clause: &[ByRefRc<Term>],
        premises: Vec<&ProofCommand>,
        _: &[ProofArg],
    ) -> Option<()> {
        if premises.len() != 1 || clause.len() != 2 {
            return None;
        }
        let premise_term = get_single_term_from_command(premises[0])?;
        let (phi_1, phi_2) = match_term!((=> phi_1 phi_2) = premise_term.as_ref())?;

        to_option(
            phi_1 == match_term!((not phi_1) = clause[0].as_ref())? && phi_2 == clause[1].as_ref(),
        )
    }

    pub fn ite1(
        clause: &[ByRefRc<Term>],
        premises: Vec<&ProofCommand>,
        _: &[ProofArg],
    ) -> Option<()> {
        if premises.len() != 1 || clause.len() != 2 {
            return None;
        }
        let premise_term = get_single_term_from_command(premises[0])?;
        let (psi_1, _, psi_3) = match_term!((ite psi_1 psi_2 psi_3) = premise_term.as_ref())?;

        to_option(psi_1 == clause[0].as_ref() && psi_3 == clause[1].as_ref())
    }

    pub fn ite2(
        clause: &[ByRefRc<Term>],
        premises: Vec<&ProofCommand>,
        _: &[ProofArg],
    ) -> Option<()> {
        if premises.len() != 1 || clause.len() != 2 {
            return None;
        }
        let premise_term = get_single_term_from_command(premises[0])?;
        let (psi_1, psi_2, _) = match_term!((ite psi_1 psi_2 psi_3) = premise_term.as_ref())?;

        to_option(
            psi_1 == match_term!((not psi_1) = clause[0].as_ref())? && psi_2 == clause[1].as_ref(),
        )
    }

    pub fn ite_intro(
        clause: &[ByRefRc<Term>],
        _: Vec<&ProofCommand>,
        _: &[ProofArg],
    ) -> Option<()> {
        if clause.len() != 1 {
            return None;
        }
        let (root_term, us) = match_term!((= t us) = clause[0].as_ref())?;
        let ite_terms: Vec<_> = root_term
            .subterms()
            .iter()
            .filter_map(|term| match_term!((ite a b c) = term))
            .collect();

        // "us" must be a conjunction where the first term is the root term
        let us = match us {
            Term::Op(Operator::And, args) => args,
            _ => return None,
        };
        if ite_terms.len() != us.len() - 1 || !DeepEq::eq(us[0].as_ref(), root_term) {
            return None;
        }

        // We assume that the "ite" terms appear in the conjunction in the same order as they
        // appear as subterms of the root term
        for (s_i, u_i) in ite_terms.iter().zip(&us[1..]) {
            let (cond, (a, b), (c, d)) = match_term!((ite cond (= a b) (= c d)) = u_i.as_ref())?;

            // Since the (= r_1 s_1) and (= r_2 s_2) equalities may be flipped, we have to check
            // all four possibilities: neither are flipped, either one is flipped, or both are
            // flipped
            let is_valid = |r_1, s_1, r_2, s_2: &Term| {
                // s_i == s_1 == s_2 == (ite cond r_1 r_2)
                s_1 == s_2
                    && (cond, r_1, r_2) == *s_i
                    && match_term!((ite a b c) = s_1) == Some(*s_i)
            };
            let is_valid = is_valid(a, b, c, d)
                || is_valid(b, a, c, d)
                || is_valid(a, b, d, c)
                || is_valid(b, a, d, c);

            if !is_valid {
                return None;
            }
        }
        Some(())
    }

    pub fn contraction(
        clause: &[ByRefRc<Term>],
        premises: Vec<&ProofCommand>,
        _: &[ProofArg],
    ) -> Option<()> {
        if premises.len() != 1 {
            return None;
        }

        let premise_clause: &[_] = match premises[0] {
            ProofCommand::Step { clause, .. } => &clause,
            _ => return None,
        };

        // This set will be populated with the terms we enconter as we iterate through the premise
        let mut encountered = HashSet::<&Term>::with_capacity(premise_clause.len());
        let mut clause_iter = clause.iter();

        for t in premise_clause {
            // `HashSet::insert` returns true if the inserted element was not in the set
            let is_new_term = encountered.insert(t.as_ref());

            // If the term in the premise clause has not been encountered before, we advance the
            // conclusion clause iterator, and check if its next term is the encountered term
            if is_new_term && clause_iter.next() != Some(t) {
                return None;
            }
        }

        // At the end, the conclusion clause iterator must be empty, meaning all terms in the
        // conclusion are in the premise
        to_option(clause_iter.next().is_none())
    }
}
