use super::assert_eq;

use std::sync::Arc;

use indexmap::IndexMap;

use crate::{
    ast::{Constant, Operator, Rc, Term, build_term, pool::TermPool},
    automata::Automaton,
    checker::error::{CheckerError, StringError},
};

// CPC utils
/// Orientation for string operations that distinguish between prefix and suffix.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Orientation {
    Prefix,
    Suffix,
}

/// Extension trait for [`TermPool`] providing helper methods to build common
/// string theory terms (prefixes, suffixes, remainder suffixes, and Skolem unification splits).
pub trait StringTermBuilder {
    /// Builds a term representing the prefix of `u` of length `n`:
    /// `(str.substr u 0 n)`
    fn build_str_prefix(&mut self, u: &Rc<Term>, n: &Rc<Term>) -> Rc<Term>;

    /// Builds a term representing the remainder suffix of `u` after dropping `n` characters:
    /// `(str.substr u n (- (str.len u) n))`
    fn build_str_suffix_rem(&mut self, u: &Rc<Term>, n: &Rc<Term>) -> Rc<Term>;

    /// Builds a term representing the suffix of `u` of length `n`:
    /// `(str.substr u (- (str.len u) n) n)`
    fn build_str_suffix(&mut self, u: &Rc<Term>, n: &Rc<Term>) -> Rc<Term>;

    /// Builds a Skolem term for unification splitting between `t` and `s`.
    ///
    /// - If `orientation` is `Orientation::Prefix`:
    ///   If `(str.len t) >= (str.len s)`, extracts remainder suffix of `t` after length `(str.len s)`;
    ///   otherwise, extracts remainder suffix of `s` after length `(str.len t)`.
    /// - If `orientation` is `Orientation::Suffix`:
    ///   If `(str.len t) >= (str.len s)`, extracts prefix of `t` of length `(- (str.len t) (str.len s))`;
    ///   otherwise, extracts prefix of `s` of length `(- (str.len s) (str.len t))`.
    fn build_str_unify_split(
        &mut self,
        t: &Rc<Term>,
        s: &Rc<Term>,
        orientation: Orientation,
    ) -> Rc<Term>;

    /// Builds a prefix unification splitting term between `t` and `s`.
    fn build_str_unify_split_prefix(&mut self, t: &Rc<Term>, s: &Rc<Term>) -> Rc<Term> {
        self.build_str_unify_split(t, s, Orientation::Prefix)
    }

    /// Builds a suffix unification splitting term between `t` and `s`.
    fn build_str_unify_split_suffix(&mut self, t: &Rc<Term>, s: &Rc<Term>) -> Rc<Term> {
        self.build_str_unify_split(t, s, Orientation::Suffix)
    }
}

impl<T: TermPool + ?Sized> StringTermBuilder for T {
    fn build_str_prefix(&mut self, u: &Rc<Term>, n: &Rc<Term>) -> Rc<Term> {
        build_term!(self, (strsubstr {u.clone()} 0 {n.clone()}))
    }

    fn build_str_suffix_rem(&mut self, u: &Rc<Term>, n: &Rc<Term>) -> Rc<Term> {
        build_term!(self, (strsubstr {u.clone()} {n.clone()} (- (strlen {u.clone()}) {n.clone()})))
    }

    fn build_str_suffix(&mut self, u: &Rc<Term>, n: &Rc<Term>) -> Rc<Term> {
        build_term!(self, (strsubstr {u.clone()} (- (strlen {u.clone()}) {n.clone()}) {n.clone()}))
    }

    fn build_str_unify_split(
        &mut self,
        t: &Rc<Term>,
        s: &Rc<Term>,
        orientation: Orientation,
    ) -> Rc<Term> {
        let t_len = self.add(Term::Op(Operator::StrLen, vec![t.clone()]));
        let s_len = self.add(Term::Op(Operator::StrLen, vec![s.clone()]));

        let (true_branch, false_branch) = match orientation {
            Orientation::Prefix => (
                self.build_str_suffix_rem(t, &s_len),
                self.build_str_suffix_rem(s, &t_len),
            ),
            Orientation::Suffix => {
                let n_t = build_term!(self, (- {t_len.clone()} {s_len.clone()}));
                let n_s = build_term!(self, (- {s_len.clone()} {t_len.clone()}));
                (
                    self.build_str_prefix(t, &n_t),
                    self.build_str_prefix(s, &n_s),
                )
            }
        };
        build_term!(self, (ite (>= (strlen {t.clone()}) (strlen {s.clone()})) {true_branch} {false_branch}))
    }
}

/// A function to calculate the fixed length of a regular expression `r` (size of strings that
/// match that RE) if it can be inferred.
///
/// It takes an `Rc<Term>` and recursively match over the regular expression operators whose length
/// can be inferred. It throws an error if the term length cannot be evaluated, i.e., if the length
/// of the term itself or one of its arguments cannot be inferred.
pub fn str_fixed_len_re(r: &Rc<Term>) -> Result<usize, CheckerError> {
    fn has_same_length(
        args: &[Rc<Term>],
        r: &Rc<Term>,
        ignore: Operator,
    ) -> Result<usize, CheckerError> {
        let should_ignore = |term: &Term| term.as_op().is_some_and(|(op, _)| op == ignore);
        let mut iter = args
            .iter()
            .filter(|a| !should_ignore(a))
            .map(str_fixed_len_re);
        let Some(first) = iter.next() else {
            return Err(CheckerError::LengthCannotBeEvaluated(r.clone()));
        };
        let first = first?;
        for size in iter {
            let size = size?;
            if size != first {
                return Err(CheckerError::LengthCannotBeEvaluated(r.clone()));
            }
        }
        Ok(first)
    }

    match r.as_ref() {
        Term::Op(Operator::ReConcat, args) => {
            let mut lengths = args.iter().map(str_fixed_len_re);
            lengths.try_fold(0, |acc, x| Ok(acc + x?))
        }
        Term::Op(Operator::ReAllChar, _) => Ok(1),
        Term::Op(Operator::ReRange, _) => Ok(1),
        Term::Op(Operator::StrToRe, args) => {
            let s_1 = args.first().unwrap();
            match s_1.as_ref() {
                Term::Const(Constant::String(s)) => Ok(s.len()),
                _ => Err(CheckerError::LengthCannotBeEvaluated(r.clone())),
            }
        }
        Term::Op(Operator::ReUnion, args) => has_same_length(args, r, Operator::ReNone),
        Term::Op(Operator::ReIntersection, args) => has_same_length(args, r, Operator::ReAll),
        _ => Err(CheckerError::LengthCannotBeEvaluated(r.clone())),
    }
}

/// A function that takes a list of regular expressions and returns the term corresponding to the
/// application of the concatenation operator to them.
///
/// If the list contains only one regular expression, it returns it directly.
pub fn singleton_elim(pool: &mut dyn TermPool, r_list: &[Rc<Term>]) -> Rc<Term> {
    match r_list {
        [single] => single.clone(),
        _ => pool.add(Term::Op(Operator::ReConcat, r_list.to_vec())),
    }
}

// RCP utils
/// Builds the automaton for a regex term, reusing the per-proof cache: proofs
/// commonly apply many regex-eval steps to the same (hash-consed) regex.
pub fn cached_automaton(
    pool: &mut dyn TermPool,
    cache: &mut IndexMap<Rc<Term>, Arc<Automaton>>,
    regex: &Rc<Term>,
) -> Result<Arc<Automaton>, CheckerError> {
    if let Some(a) = cache.get(regex) {
        return Ok(a.clone());
    }
    let a = Arc::new(Automaton::create_from_regex_operators(pool, regex)?);
    cache.insert(regex.clone(), a.clone());
    Ok(a)
}

/// Constructs an automaton for a string term `t` by combining the automata from the rule premises.
///
/// For a concatenation term `(str.++ s_0 ... s_n)`, it verifies that each component `s_i` matches
/// its corresponding premise `(str.in_re s_i A_i)` and builds the concatenated regular expression
/// automaton `(re.++ A_0 ... A_n)`.
pub fn make_automaton_from_string(
    pool: &mut dyn TermPool,
    t: &Rc<Term>,
    premise_automatas: Vec<(Rc<Term>, Rc<Term>)>,
) -> Result<Automaton, CheckerError> {
    match t.as_ref() {
        Term::Op(Operator::StrConcat, ss) => {
            if ss.len() != premise_automatas.len() {
                return Err(StringError::ConcatTermsNumberDiffersFromPremiseTermsNumber(
                    ss.len(),
                    premise_automatas.len(),
                )
                .into());
            }

            let mut components: Vec<Rc<Term>> = Vec::new();
            for (index, w) in ss.iter().enumerate() {
                let premise_a = premise_automatas[index].clone();
                assert_eq(w, &premise_a.0)?;
                components.push(premise_a.1.clone());
            }

            let regex_a = pool.add(Term::Op(Operator::ReConcat, components));
            Ok(Automaton::create_from_regex_operators(pool, &regex_a)?)
        }
        // TODO: add other forwadable functions
        // Term::Op(Operator::Replace, _) => {}
        // Term::Op(Operator::ReplaceAll, _) => {}
        _ => Err(StringError::NotBackwardableOperator(t.clone()).into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{match_term, pool::PrimitivePool};

    #[test]
    fn test_build_str_prefix() {
        let mut pool = PrimitivePool::new();
        let str_sort = pool.add_sort(crate::ast::Sort::String);
        let int_sort = pool.add_sort(crate::ast::Sort::Int);
        let u = pool.add(Term::new_var("u", str_sort));
        let n = pool.add(Term::new_var("n", int_sort));

        let term = pool.build_str_prefix(&u, &n);
        let expected = build_term!(pool, (strsubstr {u} 0 {n}));
        assert_eq!(term, expected);
    }

    #[test]
    fn test_build_str_suffix() {
        let mut pool = PrimitivePool::new();
        let str_sort = pool.add_sort(crate::ast::Sort::String);
        let int_sort = pool.add_sort(crate::ast::Sort::Int);
        let u = pool.add(Term::new_var("u", str_sort));
        let n = pool.add(Term::new_var("n", int_sort));

        let term = pool.build_str_suffix(&u, &n);
        let expected = build_term!(pool, (strsubstr {u.clone()} (- (strlen {u}) {n.clone()}) {n}));
        assert_eq!(term, expected);
    }

    #[test]
    fn test_build_str_suffix_rem() {
        let mut pool = PrimitivePool::new();
        let str_sort = pool.add_sort(crate::ast::Sort::String);
        let int_sort = pool.add_sort(crate::ast::Sort::Int);
        let u = pool.add(Term::new_var("u", str_sort));
        let n = pool.add(Term::new_var("n", int_sort));

        let term = pool.build_str_suffix_rem(&u, &n);
        let expected = build_term!(pool, (strsubstr {u.clone()} {n.clone()} (- (strlen {u}) {n})));
        assert_eq!(term, expected);
    }

    #[test]
    fn test_build_str_unify_split_prefix_and_suffix() {
        let mut pool = PrimitivePool::new();
        let str_sort = pool.add_sort(crate::ast::Sort::String);
        let t = pool.add(Term::new_var("t", str_sort.clone()));
        let s = pool.add(Term::new_var("s", str_sort));

        let pref_term = pool.build_str_unify_split(&t, &s, Orientation::Prefix);
        let suff_term = pool.build_str_unify_split(&t, &s, Orientation::Suffix);

        assert!(
            match_term!(
                (ite (>= (strlen ...) (strlen ...)) (strsubstr ...) (strsubstr ...)) = &pref_term
            )
            .is_some()
        );
        assert!(
            match_term!(
                (ite (>= (strlen ...) (strlen ...)) (strsubstr ...) (strsubstr ...)) = &suff_term
            )
            .is_some()
        );
        assert_ne!(pref_term, suff_term);
    }

    #[test]
    fn test_cached_automaton() {
        let mut pool = PrimitivePool::new();
        let mut cache = IndexMap::new();

        let a = pool.add(Term::new_string("a"));
        let re_a = pool.add(Term::Op(Operator::StrToRe, vec![a]));

        let auto1 = cached_automaton(&mut pool, &mut cache, &re_a).unwrap();
        let auto2 = cached_automaton(&mut pool, &mut cache, &re_a).unwrap();

        assert!(Arc::ptr_eq(&auto1, &auto2));
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_make_automaton_from_string_success() {
        let mut pool = PrimitivePool::new();
        let s1 = pool.add(Term::new_string("a"));
        let s2 = pool.add(Term::new_string("b"));
        let concat = pool.add(Term::Op(Operator::StrConcat, vec![s1.clone(), s2.clone()]));

        let re1 = pool.add(Term::Op(Operator::StrToRe, vec![s1.clone()]));
        let re2 = pool.add(Term::Op(Operator::StrToRe, vec![s2.clone()]));

        let premises = vec![(s1, re1), (s2, re2)];
        let automaton = make_automaton_from_string(&mut pool, &concat, premises);
        assert!(automaton.is_ok());
    }

    #[test]
    fn test_make_automaton_from_string_mismatch() {
        let mut pool = PrimitivePool::new();
        let s1 = pool.add(Term::new_string("a"));
        let s2 = pool.add(Term::new_string("b"));
        let concat = pool.add(Term::Op(Operator::StrConcat, vec![s1.clone(), s2.clone()]));

        let re1 = pool.add(Term::Op(Operator::StrToRe, vec![s1.clone()]));
        let premises = vec![(s1, re1)]; // Wrong number of premises

        let result = make_automaton_from_string(&mut pool, &concat, premises);
        assert!(result.is_err());
    }

    #[test]
    fn test_make_automaton_from_string_invalid_operator() {
        let mut pool = PrimitivePool::new();
        let s = pool.add(Term::new_string("a"));
        let result = make_automaton_from_string(&mut pool, &s, vec![]);
        assert!(result.is_err());
    }
}
