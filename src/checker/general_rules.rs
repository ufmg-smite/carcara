use super::{get_single_term_from_command, to_option};

use crate::ast::*;

use std::collections::HashSet;

pub fn not_not(clause: &[ByRefRc<Term>], _: Vec<&ProofCommand>, _: &[ProofArg]) -> Option<()> {
    if clause.len() != 2 {
        return None;
    }
    let p = match_term!((not (not (not p))) = clause[0])?;
    let q = clause[1].as_ref();
    to_option(p == q)
}

pub fn and_pos(clause: &[ByRefRc<Term>], _: Vec<&ProofCommand>, _: &[ProofArg]) -> Option<()> {
    if clause.len() != 2 {
        return None;
    }
    let and_contents = match_term!((not (and ...)) = clause[0])?;
    and_contents.iter().find(|&t| *t == clause[1]).map(|_| ())
}

pub fn and_neg(clause: &[ByRefRc<Term>], _: Vec<&ProofCommand>, _: &[ProofArg]) -> Option<()> {
    if clause.len() < 2 {
        return None;
    }
    let and_contents = match_term!((and ...) = clause[0])?
        .iter()
        .map(|t| Some(t.as_ref()));
    let remaining = clause[1..].iter().map(|t| t.remove_negation());
    to_option(and_contents.eq(remaining))
}

pub fn or_pos(clause: &[ByRefRc<Term>], _: Vec<&ProofCommand>, _: &[ProofArg]) -> Option<()> {
    if clause.len() < 2 {
        return None;
    }
    let or_contents = match_term!((not (or ...)) = clause[0])?;
    to_option(or_contents.iter().eq(&clause[1..]))
}

pub fn or_neg(clause: &[ByRefRc<Term>], _: Vec<&ProofCommand>, _: &[ProofArg]) -> Option<()> {
    if clause.len() < 2 {
        return None;
    }
    let or_contents = match_term!((or ...) = clause[0])?;
    let other = clause[1].remove_negation()?;
    or_contents
        .iter()
        .find(|&t| t.as_ref() == other)
        .map(|_| ())
}

pub fn equiv_pos1(clause: &[ByRefRc<Term>], _: Vec<&ProofCommand>, _: &[ProofArg]) -> Option<()> {
    if clause.len() != 3 {
        return None;
    }
    let (phi_1, phi_2) = match_term!((not (= phi_1 phi_2)) = clause[0])?;
    to_option(phi_1 == clause[1].as_ref() && phi_2 == clause[2].remove_negation()?)
}

pub fn equiv_pos2(clause: &[ByRefRc<Term>], _: Vec<&ProofCommand>, _: &[ProofArg]) -> Option<()> {
    if clause.len() != 3 {
        return None;
    }
    let (phi_1, phi_2) = match_term!((not (= phi_1 phi_2)) = clause[0])?;
    to_option(phi_1 == clause[1].remove_negation()? && phi_2 == clause[2].as_ref())
}

pub fn eq_reflexive(clause: &[ByRefRc<Term>], _: Vec<&ProofCommand>, _: &[ProofArg]) -> Option<()> {
    if clause.len() == 1 {
        let (a, b) = match_term!((= a b) = clause[0])?;
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
    let conclusion = match_term!((= t u) = clause.last().unwrap())?;

    // The first `clause.len()` - 1 terms in the clause must be a sequence of inequalites, and
    // they will be the premises of the transitive chain
    let mut premises = Vec::with_capacity(clause.len() - 1);
    for term in &clause[..clause.len() - 1] {
        let (t, u) = match_term!((not (= t u)) = term)?;
        premises.push((t, u));
    }

    find_chain(conclusion, &mut premises)
}

pub fn eq_congruent(clause: &[ByRefRc<Term>], _: Vec<&ProofCommand>, _: &[ProofArg]) -> Option<()> {
    if clause.len() < 2 {
        return None;
    }
    let premises = clause[..clause.len() - 1]
        .iter()
        .map(|t| t.remove_negation());
    let conclusion = match_term!((= f g) = clause.last().unwrap())?;

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
        .map(|t| t.remove_negation());
    let conclusion = (
        clause[clause.len() - 2].remove_negation()?,
        clause[clause.len() - 1].as_ref(),
    );

    generic_congruent_rule(premises, conclusion)
}

/// A function to check congruency. Useful for the "eq_congruent" and "eq_congruent_pred"
/// rules. `premises` should be an iterator over the argument equalities, and `conclusion`
/// should be the two function applications.
fn generic_congruent_rule<'a, T>(premises: T, conclusion: (&Term, &Term)) -> Option<()>
where
    T: Iterator<Item = Option<&'a Term>>,
{
    let mut ts = Vec::new();
    let mut us = Vec::new();
    for term in premises {
        let (t, u) = match_term!((= t u) = term?)?;
        ts.push(t);
        us.push(u);
    }

    let (f_args, g_args) = match conclusion {
        (Term::App(f, f_args), Term::App(g, g_args)) if f == g => (f_args, g_args),
        (Term::Op(f, f_args), Term::Op(g, g_args)) if f == g => (f_args, g_args),
        _ => return None,
    };
    if f_args.len() != g_args.len() || f_args.len() != ts.len() {
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

pub fn distinct_elim(
    clause: &[ByRefRc<Term>],
    _: Vec<&ProofCommand>,
    _: &[ProofArg],
) -> Option<()> {
    if clause.len() != 1 {
        return None;
    }

    let (distinct_args, second_term) = match_term!((= (distinct ...) second) = clause[0])?;
    match distinct_args {
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
            let got = match_term!((and ...) = second_term)?;
            let mut k = 0;
            for i in 0..args.len() {
                for j in i + 1..args.len() {
                    let (a, b) = (args[i].as_ref(), args[j].as_ref());
                    let got = match_term!((not (= x y)) = got[k])?;
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
        while let Some(t) = term.remove_negation() {
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

pub fn cong(clause: &[ByRefRc<Term>], premises: Vec<&ProofCommand>, _: &[ProofArg]) -> Option<()> {
    /// Since the semantics of this rule is slighty different from that of "eq_congruent" and
    /// "eq_congruent_pred", we cannot just use the `generic_congruent_rule` function
    fn check_cong<'a>(
        premises: &[Option<(&'a Term, &'a Term)>],
        f_args: &[ByRefRc<Term>],
        g_args: &[ByRefRc<Term>],
    ) -> bool {
        let mut premises = premises.iter().peekable();
        for (f_arg, g_arg) in f_args.iter().zip(g_args) {
            let expected = (f_arg.as_ref(), g_arg.as_ref());
            match premises.peek() {
                // If the next premise can justify that the arguments are equal, we consume it. We
                // prefer consuming the premise even if the arguments are directly equal
                Some(Some((t, u))) if expected == (t, u) || expected == (u, t) => {
                    premises.next();
                }
                // If there are no more premises, or the next premise does not match the current
                // arguments, the arguments need to be directly equal
                None | Some(Some(_)) => {
                    if f_arg != g_arg {
                        return false;
                    }
                }
                // If the inner option is `None`, it means the premise was of the wrong form
                Some(None) => return false,
            }
        }

        // At the end, all premises must have been consumed
        premises.next().is_none()
    }

    if premises.is_empty() || clause.len() != 1 {
        return None;
    }

    let premises: Vec<_> = premises
        .into_iter()
        .map(|command| {
            get_single_term_from_command(command).and_then(|term| match_term!((= t u) = term))
        })
        .collect();

    let (f_args, g_args) = match match_term!((= f g) = clause[0].as_ref())? {
        // Because of the way veriT handles equality terms, when the "cong" rule is called with two
        // equalities of two terms, the order of their arguments may be flipped. Because of that,
        // we have to treat this special case separately
        (Term::Op(Operator::Eq, f_args), Term::Op(Operator::Eq, g_args))
            if f_args.len() == 2 && g_args.len() == 2 =>
        {
            // We have to test all four possibilites: neither f nor g are flipped, only f is
            // flipped, only g is flipped, or both f and g are flipped
            let f_args_flipped = [f_args[1].clone(), f_args[0].clone()];
            let g_args_flipped = [g_args[1].clone(), g_args[0].clone()];
            return to_option(
                check_cong(&premises, f_args, g_args)
                    || check_cong(&premises, &f_args_flipped, g_args)
                    || check_cong(&premises, f_args, &g_args_flipped)
                    || check_cong(&premises, &f_args_flipped, &g_args_flipped),
            );
        }

        (Term::App(f, f_args), Term::App(g, g_args)) if f == g => (f_args, g_args),
        (Term::Op(f, f_args), Term::Op(g, g_args)) if f == g => (f_args, g_args),
        _ => return None,
    };
    if f_args.len() != g_args.len() {
        return None;
    }
    to_option(check_cong(&premises, f_args, g_args))
}

pub fn and(clause: &[ByRefRc<Term>], premises: Vec<&ProofCommand>, _: &[ProofArg]) -> Option<()> {
    if premises.len() != 1 || clause.len() != 1 {
        return None;
    }
    let and_term = get_single_term_from_command(premises[0])?;
    let and_contents = match_term!((and ...) = and_term)?;

    to_option(and_contents.iter().any(|t| t == &clause[0]))
}

pub fn or(clause: &[ByRefRc<Term>], premises: Vec<&ProofCommand>, _: &[ProofArg]) -> Option<()> {
    if premises.len() != 1 {
        return None;
    }
    let or_term = get_single_term_from_command(premises[0])?;
    let or_contents = match_term!((or ...) = or_term)?;

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
    let (phi_1, phi_2) = match_term!((=> phi_1 phi_2) = premise_term)?;

    to_option(phi_1 == clause[0].remove_negation()? && phi_2 == clause[1].as_ref())
}

pub fn ite1(clause: &[ByRefRc<Term>], premises: Vec<&ProofCommand>, _: &[ProofArg]) -> Option<()> {
    if premises.len() != 1 || clause.len() != 2 {
        return None;
    }
    let premise_term = get_single_term_from_command(premises[0])?;
    let (phi_1, _, phi_3) = match_term!((ite phi_1 phi_2 phi_3) = premise_term)?;

    to_option(phi_1 == clause[0].as_ref() && phi_3 == clause[1].as_ref())
}

pub fn ite2(clause: &[ByRefRc<Term>], premises: Vec<&ProofCommand>, _: &[ProofArg]) -> Option<()> {
    if premises.len() != 1 || clause.len() != 2 {
        return None;
    }
    let premise_term = get_single_term_from_command(premises[0])?;
    let (phi_1, phi_2, _) = match_term!((ite phi_1 phi_2 phi_3) = premise_term)?;

    to_option(phi_1 == clause[0].remove_negation()? && phi_2 == clause[1].as_ref())
}

pub fn ite_intro(clause: &[ByRefRc<Term>], _: Vec<&ProofCommand>, _: &[ProofArg]) -> Option<()> {
    if clause.len() != 1 {
        return None;
    }
    let (root_term, us) = match_term!((= t (and ...)) = clause[0])?;
    let ite_terms: Vec<_> = root_term
        .subterms()
        .iter()
        .filter_map(|term| match_term!((ite a b c) = term))
        .collect();

    // "us" must be a conjunction where the first term is the root term
    if ite_terms.len() != us.len() - 1 || !DeepEq::eq_modulo_reordering(us[0].as_ref(), root_term) {
        return None;
    }

    // We assume that the "ite" terms appear in the conjunction in the same order as they
    // appear as subterms of the root term
    for (s_i, u_i) in ite_terms.iter().zip(&us[1..]) {
        let (cond, (a, b), (c, d)) = match_term!((ite cond (= a b) (= c d)) = u_i)?;

        // Since the (= r_1 s_1) and (= r_2 s_2) equalities may be flipped, we have to check
        // all four possibilities: neither are flipped, either one is flipped, or both are
        // flipped
        let is_valid = |r_1, s_1, r_2, s_2: &Term| {
            // s_i == s_1 == s_2 == (ite cond r_1 r_2)
            s_1 == s_2 && (cond, r_1, r_2) == *s_i && match_term!((ite a b c) = s_1) == Some(*s_i)
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

pub fn nary_elim(clause: &[ByRefRc<Term>], _: Vec<&ProofCommand>, _: &[ProofArg]) -> Option<()> {
    // The three possible cases for n-ary operators: chainable, right associative and left
    // associative
    #[derive(Debug, PartialEq, Eq)]
    enum Case {
        Chainable,
        RightAssoc,
        LeftAssoc,
    }

    // A function to check the right and left associative cases. Consider as an example the
    // term (=> p q r s) being transformed into the term (=> p (=> q (=> r s))). This function
    // checks that the operators match, checks that the head argument "p" matches the left-hand
    // argument in the result term (as the operator is right associative) and then calls itself
    // recursively passing the "tail" (=> q r s) and the right-hand argument (=> q (=> r s)).
    // If the operator was right associative, the "head" argument would be the last, and the
    // nested term would be the left-hand arugment of the result term. In the base case, the
    // function will be called with the terms (=> s) and s, and it only needs to compare the
    // two "s"s
    fn check_assoc(
        op: Operator,
        args: &[ByRefRc<Term>],
        result_term: &Term,
        is_right: bool,
    ) -> bool {
        let (head, tail) = match args {
            [] => return false,
            [t] => return t.as_ref() == result_term,

            // The "head" term will be the first or last term in `args`, depending on if the
            // operator is right or left associative
            [first, rest @ ..] if is_right => (first, rest),
            [rest @ .., last] => (last, rest),
        };
        if let Term::Op(got_op, got_args) = result_term {
            // The result term must have only two arguments, and which of them is the nested
            // operation depends on if the operator is right or left associative
            let (got_head, nested) = match got_args.as_slice() {
                [a, b] if is_right => (a, b),
                [a, b] => (b, a),
                _ => return false,
            };

            // Check that the operator and the "head" term match, and call the function
            // recursively on the remaining terms and the nested operation term
            *got_op == op && got_head == head && check_assoc(op, tail, nested, is_right)
        } else {
            false
        }
    }

    if clause.len() != 1 {
        return None;
    }
    let (original, result) = match_term!((= o r) = clause[0].as_ref())?;
    if let Term::Op(op, args) = original {
        let case = match op {
            Operator::Eq => Case::Chainable,
            Operator::Add | Operator::Sub | Operator::Mult => Case::LeftAssoc,
            Operator::Implies => Case::RightAssoc,
            _ => return None,
        };
        to_option(match case {
            Case::Chainable => {
                // For every term in the chain, check that the operator is the correct one, and
                // extract its arguments
                let chain = match_term!((and ...) = result)?.iter().map(|chain_term| {
                    if let Term::Op(got_op, got_args) = chain_term.as_ref() {
                        if got_op == op {
                            return Some(got_args.as_slice());
                        }
                    }
                    None
                });
                // The terms in the chain should be the operation applied to every two adjacent
                // terms in the original term's arguments. `args.windows(2)` returns an
                // iterator over the pairs of adjacent terms
                args.windows(2).map(Some).eq(chain)
            }
            assoc_case => check_assoc(*op, &args, result, assoc_case == Case::RightAssoc),
        })
    } else {
        None
    }
}