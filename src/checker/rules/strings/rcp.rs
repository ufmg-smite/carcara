use super::{
    RuleArgs, RuleResult, assert_clause_len, assert_eq, assert_num_premises, get_premise_term,
};

use crate::{
    ast::{Operator, Rc, Term, match_term_err},
    automata::{
        Automaton,
        operations::{self, has_reachable_accepting_state, is_subautomaton},
    },
    checker::{
        error::{CheckerError, StringError},
        rules::strings::make_automaton_from_string,
    },
};

pub fn re_convert(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 2)?;
    let (w1, a1) = match_term_err!((not (strinre w a1)) = &conclusion[0])?;
    let (w2, a2) = match_term_err!((strinre w a2) = &conclusion[1])?;

    assert_eq(w1, w2)?;

    let a1 = Automaton::determinize(&Automaton::create_from_regex_operators(pool, a1)?);
    let a2 = Automaton::determinize(a2.as_automaton_err()?);

    if !operations::is_equivalent(&a1, &a2) {
        return Err(StringError::ExpectedEquivalentAutomata(a1, a2).into());
    }

    Ok(())
}

pub fn re_empty_intersection(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 2)?;
    let (w1, a1) = match_term_err!((not (strinre w a1)) = &conclusion[0])?;
    let (w2, a2) = match_term_err!((not (strinre w a2)) = &conclusion[1])?;

    assert_eq(w1, w2)?;

    let a1 = a1.as_automaton_err()?;
    let a2 = a2.as_automaton_err()?;

    if !has_reachable_accepting_state(&a1) || !has_reachable_accepting_state(&a2) {
        return Ok(());
    }

    let a1 = Automaton::determinize(&a1);
    let a2 = Automaton::determinize(&a2);
    let intersection = operations::intersection(a1.clone(), a2.clone())?;

    if has_reachable_accepting_state(&intersection) {
        return Err(StringError::ExpectedAutomataEmptyIntersection(intersection, a1, a2).into());
    }

    Ok(())
}

pub fn re_intersection(RuleArgs { premises, conclusion, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 2..)?;
    assert_clause_len(conclusion, 1)?;

    let (w_conc, conc_automaton) = match_term_err!(
        (strinre w a) = &conclusion[0]
    )?;
    let conc_automaton = conc_automaton.as_automaton_err()?;

    let mut has_empty_premise = false;
    let mut premise_automatas: Vec<Automaton> = Vec::with_capacity(premises.len());

    for premise in premises {
        let term = get_premise_term(premise)?;
        let (w, a) = match_term_err!((strinre w a1) = term)?;
        assert_eq(w, w_conc)?;

        let a = a.as_automaton_err()?;
        if !has_reachable_accepting_state(&a) {
            has_empty_premise = true;
        }

        if !has_empty_premise {
            premise_automatas.push(a.clone());
        }
    }

    if has_empty_premise {
        if !has_reachable_accepting_state(&conc_automaton) {
            return Ok(());
        } else {
            let expected = Automaton::empty_automaton();
            return Err(StringError::ExpectedEquivalentAutomata(
                expected,
                Automaton::determinize(&conc_automaton),
            )
            .into());
        }
    }

    let mut expected = Automaton::determinize(&premise_automatas[0]);
    for automaton in &premise_automatas[1..] {
        let det_a = Automaton::determinize(automaton);
        expected = operations::intersection(expected, det_a)?;
        if !has_reachable_accepting_state(&expected) {
            break;
        }
    }

    let conc_is_empty = !has_reachable_accepting_state(&conc_automaton);
    let expected_is_empty = !has_reachable_accepting_state(&expected);
    if conc_is_empty && expected_is_empty {
        return Ok(());
    }

    let conc_automaton = Automaton::determinize(&conc_automaton);
    if !operations::is_equivalent(&expected, &conc_automaton) {
        return Err(StringError::ExpectedEquivalentAutomata(expected, conc_automaton).into());
    }

    Ok(())
}

pub fn re_forward_prop(RuleArgs { premises, conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 2..)?;
    assert_clause_len(conclusion, 1)?;

    let (s, conc_automaton) = match_term_err!(
        (strinre s a) = &conclusion[0]
    )?;

    let mut premise_automatas: Vec<(Rc<Term>, Rc<Term>)> = Vec::new();
    for premise in premises {
        let term = get_premise_term(premise)?;
        let (w, a) = match_term_err!((strinre w a) = term)?;
        premise_automatas.push((w.clone(), a.clone()));
    }

    let expected = Automaton::determinize(&make_automaton_from_string(pool, s, premise_automatas)?);
    let conc_automaton = Automaton::determinize(conc_automaton.as_automaton_err()?);

    if !operations::is_equivalent(&expected, &conc_automaton) {
        return Err(
            StringError::ExpectedEquivalentAutomata(expected, conc_automaton.clone()).into(),
        );
    }

    Ok(())
}

pub fn concat_bwd_propagation(RuleArgs { premises, conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1..)?;

    let p1 = get_premise_term(&premises[0])?;
    let p2 = get_premise_term(&premises[1])?;

    let (x1, ws) = match_term_err!((= x1 (strconcat ...)) = p1)?;
    let (x2, a) = match_term_err!((strinre x2 a) = p2)?;

    assert_eq(x1, x2)?;

    let a = Automaton::determinize(&Automaton::create_from_regex_operators(pool, a)?);

    for and_term in conclusion {
        let ands = match_term_err!((and ...) = and_term)?;
        if ws.len() != ands.len() {
            return Err(StringError::ConcatTermsNumberDiffersFromPremiseTermsNumber(
                ws.len(),
                ands.len(),
            )
            .into());
        }

        let mut automata = Vec::new();
        for (idx, term) in ands.iter().enumerate() {
            let (w, re) = match_term_err!((strinre w re) = term)?;
            assert_eq(&ws[idx], w)?;
            automata.push(re.clone());
        }

        let re = pool.add(Term::Op(Operator::ReConcat, automata));
        let computed = Automaton::determinize(&Automaton::create_from_regex_operators(pool, &re)?);

        let intersection = operations::intersection(a.clone(), computed.clone())?;
        if !operations::has_reachable_accepting_state(&intersection) {
            return Err(
                StringError::ExpectedAutomataIntersection(a.clone(), computed.clone()).into(),
            );
        }
    }

    Ok(())
}

pub fn concat_aut_bwd_propagation(RuleArgs { premises, conclusion, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1..)?;

    let p1 = get_premise_term(&premises[0])?;
    let p2 = get_premise_term(&premises[1])?;

    let (x2, a) = match_term_err!((strinre x2 a) = p1)?;
    let (x1, ws) = match_term_err!((= x1 (strconcat ...)) = p2)?;

    assert_eq(x1, x2)?;

    let a = a.as_automaton_err()?;

    for and_term in conclusion {
        let ands = match_term_err!((and ...) = and_term)?;
        if ws.len() != ands.len() {
            return Err(StringError::ConcatTermsNumberDiffersFromPremiseTermsNumber(
                ws.len(),
                ands.len(),
            )
            .into());
        }

        for (idx, term) in ands.iter().enumerate() {
            let (w, aut) = match_term_err!((strinre w aut) = term)?;
            assert_eq(&ws[idx], w)?;

            let aut = aut.as_automaton_err()?;
            if !is_subautomaton(&aut, &a) {
                return Err(StringError::ExpectedSubautomaton(aut.clone(), a.clone()).into());
            }
        }
    }

    Ok(())
}

pub fn str_concat_len(RuleArgs { premises, conclusion, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let premise = get_premise_term(&premises[0])?;
    let (s1, ts) = match_term_err!((= s1 (strconcat ...)) = premise)?;
    let (s2, t_lens) = match_term_err!((= (strlen s2) (+ ...)) = &conclusion[0])?;

    assert_eq(s1, s2)?;

    if ts.len() != t_lens.len() {
        return Err(CheckerError::TermOfWrongForm(
            "(= (str.len s) (+ (str.len a_1) ... (str.len a_n)))",
            conclusion[0].clone(),
        ));
    }

    for (t1, t2) in std::iter::zip(ts, t_lens) {
        let inner = match_term_err!((strlen inner) = t2)?;
        assert_eq(t1, inner)?;
    }

    Ok(())
}
