pub mod cpc;
pub mod normalization;
pub mod rcp;
pub mod utils;

pub use normalization::NormalizedConcat;
pub use utils::*;

use super::{
    RuleArgs, RuleResult, assert_clause_len, assert_eq, assert_num_args, assert_num_premises,
    assert_polyeq, get_premise_term,
};

use crate::{ast::match_term_err, checker::error::StringError};
use rug::Integer;

pub fn str_indexof_re_eval(
    RuleArgs {
        premises,
        conclusion,
        pool,
        automata_cache,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 0)?;
    assert_clause_len(conclusion, 1)?;

    let (s, r, n, m) = match_term_err!((= (indexofre s r n) m) = &conclusion[0])?;

    let s = s.as_string_err()?;
    let dfa = cached_automaton(pool, automata_cache, r)?;
    let n = n.as_signed_integer_err()?;
    let m = m.as_signed_integer_err()?;

    let chars: Vec<char> = s.chars().collect();
    let len = chars.len();

    let expected: Integer = if n < 0 || n > len {
        Integer::from(-1)
    } else if dfa.accepts("") {
        n.clone()
    } else {
        let start_idx = n.to_usize().unwrap();
        let mut match_pos = None;
        'outer: for i in start_idx..len {
            for j in (i + 1)..=len {
                let substring: String = chars[i..j].iter().collect();
                if dfa.accepts(&substring) {
                    match_pos = Some(i);
                    break 'outer;
                }
            }
        }
        match match_pos {
            Some(i) => Integer::from(i),
            None => Integer::from(-1),
        }
    };

    if expected != m {
        return Err(StringError::RegexIndexOfFailed {
            s,
            regex: r.clone(),
            index: n,
            expected: m,
            got: expected,
        }
        .into());
    }

    Ok(())
}

pub fn str_replace_re_eval(
    RuleArgs {
        premises,
        conclusion,
        pool,
        automata_cache,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 0)?;
    assert_clause_len(conclusion, 1)?;

    let (s, r, t, u) = match_term_err!((= (replacere s r t) u) = &conclusion[0])?;

    let s = s.as_string_err()?;
    let t = t.as_string_err()?;
    let u = u.as_string_err()?;

    let dfa = cached_automaton(pool, automata_cache, r)?;

    let expected = if dfa.accepts("") {
        format!("{}{}", t, s)
    } else {
        let chars: Vec<char> = s.chars().collect();
        let n = chars.len();
        let mut match_found = None;

        'outer: for i in 0..n {
            for j in (i + 1)..=n {
                let substring: String = chars[i..j].iter().collect();
                if dfa.accepts(&substring) {
                    match_found = Some((i, j));
                    break 'outer;
                }
            }
        }

        if let Some((i, j)) = match_found {
            let prefix: String = chars[0..i].iter().collect();
            let suffix: String = chars[j..n].iter().collect();
            format!("{}{}{}", prefix, t, suffix)
        } else {
            s.clone()
        }
    };

    if expected != u {
        return Err(StringError::RegexReplaceFailed {
            s,
            regex: r.clone(),
            replacement: t,
            expected: u,
            got: expected,
        }
        .into());
    }

    Ok(())
}

pub fn str_replace_re_all_eval(
    RuleArgs {
        premises,
        conclusion,
        pool,
        automata_cache,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 0)?;
    assert_clause_len(conclusion, 1)?;

    let (s, r, t, u) = match_term_err!((= (replacereall s r t) u) = &conclusion[0])?;

    let s = s.as_string_err()?;
    let t = t.as_string_err()?;
    let u = u.as_string_err()?;

    let dfa = cached_automaton(pool, automata_cache, r)?;

    let chars: Vec<char> = s.chars().collect();
    let n = chars.len();
    let mut result = String::new();
    let mut index = 0;

    while index < n {
        let mut match_found = None;
        'outer: for i in index..n {
            for j in (i + 1)..=n {
                let substring: String = chars[i..j].iter().collect();
                if dfa.accepts(&substring) {
                    match_found = Some((i, j));
                    break 'outer;
                }
            }
        }

        if let Some((i, j)) = match_found {
            let prefix: String = chars[index..i].iter().collect();
            result.push_str(&prefix);
            result.push_str(&t);
            index = j;
        } else {
            let suffix: String = chars[index..n].iter().collect();
            result.push_str(&suffix);
            break;
        }
    }

    if result != u {
        return Err(StringError::RegexReplaceFailed {
            s,
            regex: r.clone(),
            replacement: t.clone(),
            expected: u,
            got: result,
        }
        .into());
    }

    Ok(())
}

pub fn str_in_re_eval(
    RuleArgs {
        premises,
        conclusion,
        pool,
        automata_cache,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 0)?;
    assert_clause_len(conclusion, 1)?;

    let (s, r, c) = match_term_err!((= (strinre s r) c) = &conclusion[0])?;

    let s = s.as_string_err()?;
    let c = c.as_bool_err()?;

    let aut = cached_automaton(pool, automata_cache, r)?;
    let accepts = aut.accepts(&s);

    if accepts != c {
        return Err(StringError::RegexMatchFailed { s, regex: r.clone(), expected: c }.into());
    }

    Ok(())
}
