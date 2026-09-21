//! A parser for the SMT-LIB and Alethe formats.

mod datatypes;
mod error;
mod lexer;
mod rare;
pub(crate) mod tests;

use crate::{
    CarcaraResult, Error,
    ast::{
        AnchorArg, Binder, BindingList, Constant, Operator, ParamOperator, Problem, ProblemPrelude,
        Proof, ProofCommand, ProofStep, QualifiedOperator, Rc, Sort, SortSubstitution, SortedVar,
        Subproof, Substitution, Term, build_term,
        pool::{PrimitivePool, TermPool},
        rare_rules::{RareStatements, Rules},
    },
    automata::parser::parse_automaton,
    utils::{HashCache, HashMapStack},
};
use carcara_macros::GenerateSetters;
use error::{assert_indexed_op_args_value, assert_num_args, check_relation_sort, check_set_sort};
use indexmap::{IndexMap, IndexSet};
use rapidhash::{HashMapExt, RapidHashMap};
use rug::{Integer, Rational};
use std::{iter::Iterator, path::Path, str::FromStr};

pub use error::{ParserError, SortError};
pub use lexer::{Position, Reserved, Token};

/// A code source for [`Parser`], with a name and contents.
pub struct Source<'s> {
    name: &'s Path,
    contents: &'s str,
}

impl<'s> Source<'s> {
    /// Constructs a new `Source` from `name` and `contents` strings.
    pub fn new(name: &'s Path, contents: &'s str) -> Self {
        Self { name, contents }
    }

    /// Constructs a new `Source` by reading the contents of a file.
    ///
    /// Since `Source` does not own its `contents` string, this must take a buffer in which to store
    /// the file contents.
    pub fn file(path: &'s Path, buf: &'s mut String) -> CarcaraResult<Self> {
        use std::io::Read;

        std::fs::File::open(path)
            .and_then(|mut f| f.read_to_string(buf))
            .map_err(|e| Error::Io {
                inner: e,
                file: path.to_str().unwrap().into(),
            })?;
        Ok(Self { name: path, contents: buf })
    }
}

impl<'s> From<&'s str> for Source<'s> {
    fn from(value: &'s str) -> Self {
        Self {
            name: Path::new("<str>"),
            contents: value,
        }
    }
}

/// Configuration for [`Parser`].
#[derive(Debug, Clone, Copy, Default, GenerateSetters)]
#[const_setters]
pub struct Config {
    /// If `true`, the parser will automatically expand function definitions introduced by
    /// `define-fun` commands in the SMT problem. If `false`, those `define-fun`s are instead
    /// interpreted as a function declaration and an `assert` command that defines the function
    /// as equal to its body (or to a lambda term, if it contains arguments). Note that function
    /// definitions in the proof are always expanded.
    apply_function_defs: bool,

    /// If `true`, the parser will eliminate `let` bindings from terms during parsing. This is done
    /// by replacing any occurrence of a variable bound in the `let` binding with its corresponding
    /// value.
    expand_lets: bool,

    /// If `true`, this relaxes the type checking rules in Carcara to allow `Int`-`Real` subtyping.
    /// That is, terms of sort `Int` will be allowed in arithmetic operations where a `Real` term
    /// was expected. Note that this only applies to predefined operators --- passing an `Int` term
    /// to a function that expects a `Real` will still be an error.
    allow_int_real_subtyping: bool,

    /// Enables "strict" parsing. If `true`:
    /// - Unary `and`, `or` and `xor` terms are not allowed
    /// - Anchor arguments using the old syntax (i.e., `(:= <symbol> <term>)`) are not allowed
    strict: bool,

    /// If `true`, the parser will parse arguments to the `hole` rule, expecting them to be valid
    /// terms.
    parse_hole_args: bool,

    /// If `true`, allow indexed operators (usually used like so: `((_ <op> <op_args>...)
    /// <args>...)`) to be used in "higher-order" fashion, that is, by omitting the `_` construction
    /// and passing the operator arguments and regular arguments together: `(<op> <op_args>...
    /// <args>...)`.
    allow_higher_order_indexed_ops: bool,

    /// If `true`, allow local sort parameters declared with a leading `@` character (e.g. `@T`) to
    /// also be referenced with the `@` omitted (i.e., both `T` or `@T` are accepted).
    ///
    /// This behaviour is seen in some legacy rare files.
    implicit_at_sort_alias: bool,

    /// If `true`, allow old (SMT-LIB versions < 2.6) syntax for datatype testers, namely `is-cons`
    /// instead of `(_ is cons)`.
    allow_legacy_tester_syntax: bool,
}

impl Config {
    /// Constructs a new `Config`, with default settings.
    pub const fn new() -> Self {
        // I can't just call `default()` because it is not const :/
        Self {
            apply_function_defs: false,
            expand_lets: false,
            allow_int_real_subtyping: false,
            strict: false,
            parse_hole_args: false,
            allow_higher_order_indexed_ops: false,
            implicit_at_sort_alias: false,
            allow_legacy_tester_syntax: false,
        }
    }
}

/// Parses an SMT problem instance (in the SMT-LIB format) and its associated proof (in the Alethe
/// format). If the optional argument `rules` is provided, also parses a set of Rare rewrite rules.
///
/// This returns the parsed problem, proof, and rules, as well as the `TermPool` used in parsing.
pub fn parse_instance<'s>(
    problem: Source<'s>,
    proof: Source<'s>,
    rules: Option<Source<'s>>,
    config: Config,
) -> CarcaraResult<(Problem, Proof, Rules, PrimitivePool)> {
    let mut pool = PrimitivePool::new();
    parse_instance_with_pool(problem, proof, rules, config, &mut pool)
        .map(|(prelude, proof, rules)| (prelude, proof, rules, pool))
}

/// Given an existing [`PrimitivePool`], parses an SMT problem instance (in the SMT-LIB format) and
/// its associated proof (in the Alethe format). If the optional argument `rules` is provided, also
/// parses a set of Rare rewrite rules.
///
/// This returns the parsed problem, proof, and rules.
pub fn parse_instance_with_pool<'s>(
    problem: Source<'s>,
    proof: Source<'s>,
    rules: Option<Source<'s>>,
    config: Config,
    pool: &mut PrimitivePool,
) -> CarcaraResult<(Problem, Proof, Rules)> {
    let mut parser = Parser::new(pool, config, problem)?;
    let problem = parser.parse_problem()?;
    parser.reset(proof)?;
    let proof = parser.parse_proof()?;
    if let Some(rules) = rules {
        parser.reset(rules)?;
        parser.config.allow_higher_order_indexed_ops = true;
        let rules = parser.parse_rare();
        let rules = match rules {
            Ok(t) => Ok(t),
            Err(v) => Err(v),
        }?;
        return Ok((problem, proof, rules));
    }
    Ok((problem, proof, RareStatements { rules: IndexMap::new() }))
}

/// A function definition, from a `define-fun` command.
struct FunctionDef {
    params: Vec<SortedVar>,
    body: Rc<Term>,
}

impl FunctionDef {
    fn apply(&self, p: &mut PrimitivePool, args: Vec<Rc<Term>>) -> Result<Rc<Term>, ParserError> {
        assert_num_args(&args, self.params.len())?;
        if args.is_empty() {
            return Ok(self.body.clone());
        }

        for (arg, (_, expected)) in args.iter().zip(self.params.iter()) {
            let got = p.sort(arg);

            if !expected.is_compatible(got.as_ref()) {
                return Err(SortError {
                    expected: vec![expected.clone()].into_boxed_slice(),
                    got,
                }
                .into());
            }
        }

        // Build a hash map of all the parameter names and the values they will
        // take
        let substitution = self
            .params
            .iter()
            .zip(args)
            .map(|((n, s), arg)| (p.add(Term::new_var(n, s.clone())), arg))
            .collect();

        // Since we already checked the sorts of the arguments, creating this substitution
        // can never fail
        let result = Substitution::new(p, substitution)
            .unwrap()
            .apply(p, &self.body);
        Ok(result)
    }
}

/// A sort definition, from a `define-sort` command.
#[derive(Debug)]
struct SortDef {
    params: Vec<String>,
    body: Rc<Sort>,
}

/// The state of the parser.
///
/// This holds all the function, constant or sort declarations and definitions, as well as the term
/// pool used by the parser.
#[derive(Default)]
struct ParserState {
    symbol_table: HashMapStack<HashCache<String>, Rc<Sort>>,
    function_defs: RapidHashMap<String, FunctionDef>,
    sort_declarations: RapidHashMap<String, usize>,
    datatype_declarations: HashMapStack<String, usize>,
    sort_defs: RapidHashMap<String, SortDef>,
    step_ids: HashMapStack<HashCache<String>, usize>,
}

/// A parser for the Alethe proof format.
pub struct Parser<'p, 's> {
    pool: &'p mut PrimitivePool,
    config: Config,
    lexer: lexer::Lexer<'s>,
    current_token: Token,
    current_position: Position,
    state: ParserState,
    is_real_only_logic: bool,
    problem: Option<Problem>,
}

impl<'p, 's> Parser<'p, 's> {
    /// Constructs a new `Parser` from a [`Source`].
    ///
    /// This operation can fail if there is an IO or lexer error on the first token.
    pub fn new(
        pool: &'p mut PrimitivePool,
        config: Config,
        input: Source<'s>,
    ) -> CarcaraResult<Self> {
        let mut lexer = lexer::Lexer::new(input);
        let (current_token, current_position) = lexer.next_token()?;
        Ok(Parser {
            pool,
            config,
            lexer,
            current_token,
            current_position,
            state: ParserState::default(),
            is_real_only_logic: false,
            problem: None,
        })
    }

    /// Resets the parser position and sets its input to `input`. This keeps the parser state,
    /// including all function, constant and sort declarations.
    pub fn reset(&mut self, input: Source<'s>) -> CarcaraResult<()> {
        let mut lexer = lexer::Lexer::new(input);
        let (current_token, current_position) = lexer.next_token()?;
        self.lexer = lexer;
        self.current_token = current_token;
        self.current_position = current_position;
        Ok(())
    }

    /// Wraps a `ParserError` into a crate level error, by adding the given position and the current
    /// source name.
    fn err(&self, inner: impl Into<ParserError>, pos: Position) -> Error {
        Error::Parser(inner.into(), pos, self.lexer.source_name.into())
    }

    /// Advances the parser one token, and returns the previous `current_token`.
    fn next_token(&mut self) -> CarcaraResult<(Token, Position)> {
        use std::mem::replace;

        let (new_token, new_position) = self.lexer.next_token()?;
        let old_token = replace(&mut self.current_token, new_token);
        let old_position = replace(&mut self.current_position, new_position);
        Ok((old_token, old_position))
    }

    /// Inserts a new symbol into the parser symbol table, with the provided sort.
    fn declare_symbol(&mut self, symbol: String, sort: Rc<Sort>) {
        self.state.symbol_table.insert(HashCache::new(symbol), sort);
    }

    /// Searches the symbol table for a symbol, and, if found, returns its sort.
    fn get_symbol(&mut self, symbol: &str) -> Option<&Rc<Sort>> {
        let cached = HashCache::new(symbol.to_owned());
        self.state.symbol_table.get(&cached)
    }

    /// Returns `true` if the symbol table has a symbol with that name, and its sort is
    /// `Sort::Type`.
    fn has_sort_symbol(&mut self, symbol: &str) -> bool {
        self.get_symbol(symbol)
            .is_some_and(|sort| *sort.as_ref() == Sort::Type)
    }

    /// Returns a sort error if `got` does not equal `expected`.
    fn check_sort_eq(&mut self, expected: &Sort, got: &Rc<Sort>) -> Result<(), SortError> {
        if expected.is_compatible(got) {
            Ok(())
        } else {
            let expected = self.pool.add_sort(expected.clone());
            Err(SortError {
                expected: vec![expected].into_boxed_slice(),
                got: got.clone(),
            })
        }
    }

    /// Makes sure all terms in `sequence` are equal to each other, otherwise returns an error.
    fn check_sort_all_eq(&mut self, sequence: &[Rc<Sort>]) -> Result<(), SortError> {
        // TODO: we are just checking if each sort is compatible with the previous. We could be more
        // strict here, and check that they are all collectively compatible. That would reject sort
        // sequences like (Real, (par (x) x), Int), which is currently accepted.
        for i in 1..sequence.len() {
            self.check_sort_eq(&sequence[i - 1], &sequence[i])?;
        }
        Ok(())
    }

    /// Returns a sort error if `got` is not one of `possibilities`.
    fn check_sort_one_of(
        &mut self,
        possibilities: &[Sort],
        got: &Rc<Sort>,
    ) -> Result<(), SortError> {
        if possibilities.iter().any(|p| p.is_compatible(got)) {
            Ok(())
        } else {
            let expected: Vec<_> = possibilities
                .iter()
                .map(|s| self.pool.add_sort(s.clone()))
                .collect();

            Err(SortError {
                expected: expected.into_boxed_slice(),
                got: got.clone(),
            })
        }
    }

    /// Makes sure `got` is a valid `Array` sort, with the given key and value sorts.
    fn check_array_sort(
        &mut self,
        key: Option<&Rc<Sort>>,
        value: Option<&Rc<Sort>>,
        got: &Rc<Sort>,
    ) -> Result<(), SortError> {
        let any = self.pool.add_sort(Sort::Atom("?".into(), Box::new([])));

        let expected = {
            let [key, value] = [key, value].map(|s| s.cloned().unwrap_or_else(|| any.clone()));
            vec![self.pool.add_sort(Sort::Array(key, value))].into_boxed_slice()
        };
        let Sort::Array(got_key, got_value) = got.as_ref() else {
            return Err(SortError { expected, got: got.clone() });
        };
        if key.is_some_and(|k| !got_key.is_compatible(k))
            || value.is_some_and(|v| !got_value.is_compatible(v))
        {
            return Err(SortError { expected, got: got.clone() });
        }
        Ok(())
    }

    /// Shortcut for `self.problem.as_mut().unwrap().prelude`
    fn prelude(&mut self) -> &mut ProblemPrelude {
        &mut self.problem.as_mut().unwrap().prelude
    }

    /// Shortcut for `self.problem.as_mut().unwrap().premises`
    fn premises(&mut self) -> &mut IndexSet<Rc<Term>> {
        &mut self.problem.as_mut().unwrap().premises
    }

    /// Constructs and sort checks a variable term.
    fn make_var(&mut self, iden: String) -> Result<Rc<Term>, ParserError> {
        let cached = HashCache::new(iden);
        let sort = match self.state.symbol_table.get(&cached) {
            Some(s) => s.clone(),
            None => return Err(ParserError::UndefinedIden(cached.unwrap())),
        };
        Ok(self.pool.add(Term::Var(cached.unwrap(), sort)))
    }

    /// Return whether we should interpret integer constants as `Real`s.
    ///
    /// If we are working with a logic that contains reals but does not contain integers, and if we
    /// are parsing the problem and not the poof, this will be true.
    fn interpret_ints_as_reals(&self) -> bool {
        self.is_real_only_logic && self.problem.is_some()
    }

    /// Constructs and sort checks an operation term.
    fn make_op(&mut self, op: Operator, args: Vec<Rc<Term>>) -> Result<Rc<Term>, ParserError> {
        let sorts: Vec<_> = args.iter().map(|t| self.pool.sort(t)).collect();

        match op {
            Operator::True | Operator::False => assert_num_args(&args, 0)?,
            Operator::Not => {
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::Bool, &sorts[0])?;
            }
            Operator::Implies => {
                assert_num_args(&args, 2..)?;
                for s in sorts {
                    self.check_sort_eq(&Sort::Bool, &s)?;
                }
            }
            Operator::Or | Operator::And | Operator::Xor => {
                // If we are not in "strict" parsing mode, we allow these operators to be called
                // with just one argument
                assert_num_args(&args, if self.config.strict { 2.. } else { 1.. })?;
                for s in sorts {
                    self.check_sort_eq(&Sort::Bool, &s)?;
                }
            }
            Operator::Equals | Operator::Distinct => {
                assert_num_args(&args, 2..)?;
                self.check_sort_all_eq(&sorts)?;
            }
            Operator::Ite => {
                assert_num_args(&args, 3)?;
                self.check_sort_eq(&Sort::Bool, &sorts[0])?;
                self.check_sort_eq(sorts[1].as_ref(), &sorts[2])?;
            }
            Operator::Add | Operator::Sub | Operator::Mult => {
                // The `-` operator, in particular, can be called with only one argument, in which
                // case it means negation instead of subtraction
                if op == Operator::Sub {
                    assert_num_args(&args, 1..)?;
                } else {
                    assert_num_args(&args, 2..)?;
                }

                // All the arguments must be either Int or Real. Also, if we are not allowing
                // Int/Real subtyping, all arguments must have the same sort
                if self.config.allow_int_real_subtyping {
                    for s in sorts {
                        self.check_sort_one_of(&[Sort::Int, Sort::Real], &s)?;
                    }
                } else {
                    self.check_sort_one_of(&[Sort::Int, Sort::Real], &sorts[0])?;
                    self.check_sort_all_eq(&sorts)?;
                }
            }
            Operator::IntDiv => {
                assert_num_args(&args, 2..)?;
                self.check_sort_eq(&Sort::Int, &sorts[0])?;
                self.check_sort_all_eq(&sorts)?;
            }
            Operator::RealDiv => {
                assert_num_args(&args, 2..)?;

                // Normally, the `/` operator may only receive Real arguments, but if we are
                // allowing Int/Real subtyping, it may also receive Ints
                if self.config.allow_int_real_subtyping {
                    for s in sorts {
                        self.check_sort_one_of(&[Sort::Int, Sort::Real], &s)?;
                    }
                } else {
                    self.check_sort_eq(&Sort::Real, &sorts[0])?;
                    self.check_sort_all_eq(&sorts)?;
                }

                if let Some(r) = self.interpret_div_as_real_lit(&args[0], &args[1]) {
                    return Ok(r);
                }
            }
            Operator::Mod => {
                assert_num_args(&args, 2)?;
                self.check_sort_eq(&Sort::Int, &sorts[0])?;
                self.check_sort_eq(&Sort::Int, &sorts[1])?;
            }
            Operator::Abs => {
                assert_num_args(&args, 1)?;
                // The argument must be Int unless we are allowing Int/Real subtyping
                if self.config.allow_int_real_subtyping {
                    self.check_sort_one_of(&[Sort::Int, Sort::Real], &sorts[0])?;
                } else {
                    self.check_sort_eq(&Sort::Int, &sorts[0])?;
                }
            }
            Operator::LessThan | Operator::GreaterThan | Operator::LessEq | Operator::GreaterEq => {
                assert_num_args(&args, 2..)?;
                // All the arguments must be either Int or Real sorted, but they don't need to all
                // have the same sort
                for s in sorts {
                    self.check_sort_one_of(&[Sort::Int, Sort::Real], &s)?;
                }
            }
            Operator::ToReal => {
                assert_num_args(&args, 1)?;
                // If the logic contains reals but not integers, integer constants are interpreted
                // as reals, so the argument might have sort Real instead of the expected Int
                self.check_sort_one_of(&[Sort::Int, Sort::Real], &sorts[0])?;
            }
            Operator::ToInt | Operator::IsInt => {
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::Real, &sorts[0])?;
            }
            Operator::Select => {
                assert_num_args(&args, 2)?;
                self.check_array_sort(Some(&sorts[1]), None, &sorts[0])?;
            }
            Operator::Store => {
                assert_num_args(&args, 3)?;
                self.check_array_sort(Some(&sorts[1]), Some(&sorts[2]), &sorts[0])?;
            }
            Operator::StrConcat => {
                assert_num_args(&args, 2..)?;
                for s in sorts {
                    self.check_sort_eq(&Sort::String, &s)?;
                }
            }
            Operator::StrLen | Operator::StrIsDigit | Operator::StrToCode | Operator::StrToInt => {
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
            }
            Operator::StrLessThan
            | Operator::StrLessEq
            | Operator::PrefixOf
            | Operator::SuffixOf
            | Operator::Contains
            | Operator::ReRange => {
                assert_num_args(&args, 2)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
                self.check_sort_eq(&Sort::String, &sorts[1])?;
            }
            Operator::CharAt => {
                assert_num_args(&args, 2)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
                self.check_sort_eq(&Sort::Int, &sorts[1])?;
            }
            Operator::Substring => {
                assert_num_args(&args, 3)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
                self.check_sort_eq(&Sort::Int, &sorts[1])?;
                self.check_sort_eq(&Sort::Int, &sorts[2])?;
            }
            Operator::IndexOf => {
                assert_num_args(&args, 3)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
                self.check_sort_eq(&Sort::String, &sorts[1])?;
                self.check_sort_eq(&Sort::Int, &sorts[2])?;
            }
            Operator::IndexOfRe => {
                assert_num_args(&args, 3)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
                self.check_sort_eq(&Sort::RegLan, &sorts[1])?;
                self.check_sort_eq(&Sort::Int, &sorts[2])?;
            }
            Operator::Replace | Operator::ReplaceAll => {
                assert_num_args(&args, 3)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
                self.check_sort_eq(&Sort::String, &sorts[1])?;
                self.check_sort_eq(&Sort::String, &sorts[2])?;
            }
            Operator::ReFromAutomaton => {
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
                if let Term::Const(Constant::String(s)) = args[0].as_ref() {
                    let automata = match parse_automaton(s.trim()) {
                        Ok((remaining, automata)) => {
                            if !remaining.is_empty() {
                                return Err(ParserError::InvalidAutomatonDeclaration(s.clone()));
                            }
                            Ok(automata)
                        }
                        Err(_) => Err(ParserError::InvalidAutomatonDeclaration(s.clone())),
                    }?;
                    return Ok(self
                        .pool
                        .add(Term::Const(Constant::RegLan(s.to_owned(), automata))));
                } else {
                    return Err(ParserError::ExpectedAnAutomatonDeclaration(args[0].clone()));
                }
            }
            Operator::StrFromCode | Operator::StrFromInt => {
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::Int, &sorts[0])?;
            }
            Operator::StrToRe => {
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
            }
            Operator::StrInRe => {
                assert_num_args(&args, 2)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
                self.check_sort_eq(&Sort::RegLan, &sorts[1])?;
            }
            Operator::ReNone | Operator::ReAll | Operator::ReAllChar => {
                assert_num_args(&args, 0)?;
            }
            Operator::ReConcat
            | Operator::ReUnion
            | Operator::ReIntersection
            | Operator::ReDiff => {
                assert_num_args(&args, 2..)?;
                for s in sorts {
                    self.check_sort_eq(&Sort::RegLan, &s)?;
                }
            }
            Operator::ReKleeneClosure
            | Operator::ReComplement
            | Operator::ReKleeneCross
            | Operator::ReOption => {
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::RegLan, &sorts[0])?;
            }
            Operator::ReplaceRe | Operator::ReplaceReAll => {
                assert_num_args(&args, 3)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
                self.check_sort_eq(&Sort::RegLan, &sorts[1])?;
                self.check_sort_eq(&Sort::String, &sorts[2])?;
            }
            Operator::BvNot | Operator::BvNeg => {
                assert_num_args(&args, 1)?;
                for s in sorts {
                    if !s.is_bitvec() {
                        return Err(ParserError::ExpectedBvSort(s));
                    }
                }
            }
            Operator::BvSize | Operator::UBvToInt | Operator::SBvToInt => {
                assert_num_args(&args, 1)?;
                if !sorts[0].is_bitvec() {
                    return Err(ParserError::ExpectedBvSort(sorts[0].clone()));
                }
            }
            Operator::BvBbTerm => {
                assert_num_args(&args, 1..)?;
                self.check_sort_eq(&Sort::Bool, &sorts[0])?;
                self.check_sort_all_eq(&sorts)?;
            }
            Operator::BvPBbTerm => {
                assert_num_args(&args, 1..)?;
                self.check_sort_eq(&Sort::Int, &sorts[0])?;
                self.check_sort_all_eq(&sorts)?;
            }
            Operator::BvConst => {
                assert_num_args(&args, 2)?;
                self.check_sort_eq(&Sort::Int, &sorts[0])?;
                self.check_sort_eq(&Sort::Int, &sorts[1])?;
            }
            Operator::BvConcat => {
                assert_num_args(&args, 2..)?;
                for s in sorts {
                    if !s.is_bitvec() {
                        return Err(ParserError::ExpectedBvSort(s));
                    }
                }
            }
            Operator::Cl => {}
            Operator::Delete => {
                self.check_sort_eq(&Sort::Bool, &sorts[0])?;
                assert_num_args(&args, 1)?;
            }
            Operator::BvAdd
            | Operator::BvMul
            | Operator::BvAnd
            | Operator::BvOr
            | Operator::BvXor => {
                assert_num_args(&args, 2..)?;
                if !sorts[0].is_bitvec() {
                    return Err(ParserError::ExpectedBvSort(sorts[0].clone()));
                }
                self.check_sort_all_eq(&sorts)?;
            }
            Operator::BvUDiv
            | Operator::BvURem
            | Operator::BvShl
            | Operator::BvLShr
            | Operator::BvULt
            | Operator::BvNAnd
            | Operator::BvNOr
            | Operator::BvXNor
            | Operator::BvComp
            | Operator::BvSub
            | Operator::BvSDiv
            | Operator::BvSRem
            | Operator::BvSMod
            | Operator::BvAShr
            | Operator::BvULe
            | Operator::BvUGt
            | Operator::BvUGe
            | Operator::BvSLt
            | Operator::BvSLe
            | Operator::BvSGt
            | Operator::BvSGe => {
                assert_num_args(&args, 2)?;
                if !sorts[0].is_bitvec() {
                    return Err(ParserError::ExpectedBvSort(sorts[0].clone()));
                }
                self.check_sort_all_eq(&sorts)?;
            }
            Operator::BvIte => {
                assert_num_args(&args, 3)?;
                self.check_sort_eq(&Sort::BitVec(1), &sorts[0])?;
                self.check_sort_all_eq(&sorts[1..])?;
            }
            Operator::RareList => (),
            Operator::Pow2 | Operator::Log2 | Operator::IsPow2 => {
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::Int, &sorts[0])?;
            }
            Operator::RealPi => assert_num_args(&args, 0)?,
            Operator::Sqrt
            | Operator::Exp
            | Operator::Sin
            | Operator::Cos
            | Operator::Tan
            | Operator::Csc
            | Operator::Sec
            | Operator::Cot
            | Operator::Arcsin
            | Operator::Arccos
            | Operator::Arctan
            | Operator::Arccsc
            | Operator::Arcsec
            | Operator::Arccot => {
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::Real, &sorts[0])?;
            }
            Operator::SetUnion | Operator::SetInter | Operator::SetMinus | Operator::SetSubset => {
                assert_num_args(&args, 2)?;
                self.check_sort_all_eq(&sorts)?;
                for sort in sorts {
                    check_set_sort(&sort)?;
                }
            }
            Operator::SetMember => {
                assert_num_args(&args, 2)?;
                let expected = self.pool.add_sort(Sort::Set(sorts[0].clone()));
                self.check_sort_eq(&expected, &sorts[1])?;
            }
            Operator::SetSingleton => {
                assert_num_args(&args, 1)?;
            }
            Operator::SetIsEmpty
            | Operator::SetIsSingleton
            | Operator::SetCard
            | Operator::SetComplement => {
                assert_num_args(&args, 1)?;
                check_set_sort(&sorts[0])?;
            }
            Operator::SetInsert => {
                assert_num_args(&args, 2..)?;
                self.check_sort_all_eq(&sorts[..sorts.len() - 1])?;
                let expected = self.pool.add_sort(Sort::Set(sorts[0].clone()));
                self.check_sort_eq(&expected, sorts.last().unwrap())?;
            }
            Operator::Tuple => {
                assert_num_args(&args, 1..)?;
            }
            Operator::TupleUnit => {
                assert_num_args(&args, 0)?;
            }
            Operator::RelTranspose => {
                assert_num_args(&args, 1)?;
                check_relation_sort(&sorts[0])?;
            }
            Operator::RelTclosure => {
                assert_num_args(&args, 1)?;
                check_relation_sort(&sorts[0])?;
                let Sort::Set(tuple) = sorts[0].as_ref() else {
                    unreachable!()
                };
                let Sort::Tuple(elems) = tuple.as_ref() else {
                    unreachable!()
                };
                if elems.len() != 2 {
                    // Hacky way to print an error saying the relation should be binary
                    let any = self.pool.add_sort(Sort::Var("?".into()));
                    let tuple = self.pool.add_sort(Sort::Tuple(vec![any.clone(), any]));
                    let expected = vec![self.pool.add_sort(Sort::Set(tuple))].into_boxed_slice();
                    return Err(SortError { expected, got: sorts[0].clone() }.into());
                }
            }
            Operator::RelJoin => {
                assert_num_args(&args, 2)?;
                check_relation_sort(&sorts[0])?;
                check_relation_sort(&sorts[1])?;
                // TODO: check properly
            }
            Operator::RelProduct => {
                assert_num_args(&args, 2)?;
                check_relation_sort(&sorts[0])?;
                check_relation_sort(&sorts[1])?;
            }
        }
        Ok(self.pool.add(Term::Op(op, args)))
    }

    fn interpret_div_as_real_lit(&mut self, a: &Rc<Term>, b: &Rc<Term>) -> Option<Rc<Term>> {
        // If the term is a division between two positive integer constants, and their GCD is 1,
        // then it should be interpreted as a rational literal. The only exception to this is the
        // term '(/ 1 1)', which is still interpreted as a division term.

        let [a, b] = [a, b].map(|t| match t.as_ref() {
            Term::Const(Constant::Integer(i)) => Some(i),
            Term::Const(Constant::Real(r)) if self.interpret_ints_as_reals() && r.is_integer() => {
                Some(r.numer())
            }
            _ => None,
        });
        let [a, b] = [a?, b?];

        if *a > 0 && *b > 0 && !(*a == 1 && *b == 1) && a.clone().gcd(b) == 1 {
            Some(self.pool.add(Term::new_real(Rational::from((a, b)))))
        } else {
            None
        }
    }

    /// Constructs and sort checks an application term.
    fn make_app(
        &mut self,
        function: Rc<Term>,
        args: Vec<Rc<Term>>,
    ) -> Result<Rc<Term>, ParserError> {
        let sort = self.pool.sort(&function);
        let mut param_function = false;
        let sorts = {
            if let Sort::Function(sorts) = sort.as_ref() {
                sorts
            } else if let Sort::Par(_, p_sort) = sort.as_ref() {
                if let Sort::Function(sorts) = p_sort.as_ref() {
                    param_function = true;
                    sorts
                } else {
                    // Parametric function does not have function sort
                    return Err(ParserError::NotAFunction(p_sort.clone()));
                }
            } else {
                // Function does not have function sort
                return Err(ParserError::NotAFunction(sort.clone()));
            }
        };
        // We allow partial application
        assert_num_args(&args, 1..sorts.len())?;
        let mut map = RapidHashMap::new();
        for i in 0..args.len() {
            let arg_sort_i = self.pool.sort(&args[i]);
            if param_function {
                if !sorts[i].is_compatible_with_map(&arg_sort_i, &mut map) {
                    return Err(ParserError::IncompatibleSorts(
                        sorts[i].clone(),
                        arg_sort_i.clone(),
                    ));
                }
                continue;
            };
            self.check_sort_eq(&sorts[i], &arg_sort_i)?;
        }
        Ok(self.pool.add(Term::App(function, args)))
    }

    /// Consumes the current token if it equals `expected`. Returns an error otherwise.
    fn expect_token(&mut self, expected: Token) -> CarcaraResult<()> {
        let (got, pos) = self.next_token()?;
        if got == expected {
            Ok(())
        } else {
            Err(self.err(ParserError::UnexpectedToken(got), pos))
        }
    }

    /// Consumes the current token if it is a symbol, and returns the inner `String`. Returns an
    /// error otherwise.
    fn expect_symbol(&mut self) -> CarcaraResult<String> {
        match self.next_token()? {
            (Token::Symbol(s), _) => Ok(s),
            (other, pos) => Err(self.err(ParserError::UnexpectedToken(other), pos)),
        }
    }

    /// Consumes the current token if it is a keyword, and returns the inner `String`. Returns an
    /// error otherwise.
    fn expect_keyword(&mut self) -> CarcaraResult<String> {
        match self.next_token()? {
            (Token::Keyword(s), _) => Ok(s),
            (other, pos) => Err(self.err(ParserError::UnexpectedToken(other), pos)),
        }
    }

    /// Consumes the current token if it is a numeral, and returns the inner `Integer`. Returns an
    /// error otherwise.
    fn expect_numeral(&mut self) -> CarcaraResult<Integer> {
        match self.next_token()? {
            (Token::Numeral(n), _) => Ok(n),
            (other, pos) => Err(self.err(ParserError::UnexpectedToken(other), pos)),
        }
    }

    /// Calls `parse_func` repeatedly until a closing parenthesis is reached.
    ///
    /// If `non_empty` is true, empty sequences will result in an error. This method consumes the
    /// ending `)` token.
    fn parse_sequence<T, F>(&mut self, mut parse_func: F, non_empty: bool) -> CarcaraResult<Vec<T>>
    where
        F: FnMut(&mut Self) -> CarcaraResult<T>,
    {
        let mut result = Vec::new();
        while self.current_token != Token::CloseParen {
            result.push(parse_func(self)?);
        }
        if non_empty && result.is_empty() {
            Err(self.err(ParserError::EmptySequence, self.current_position))
        } else {
            self.next_token()?; // Consume `)` token
            Ok(result)
        }
    }

    /// Reads tokens until the matching closing parenthesis is reached.
    fn read_until_close_parens(&mut self) -> CarcaraResult<Vec<Token>> {
        let mut result = Vec::new();
        let mut parens_depth = 1;
        while parens_depth > 0 {
            let token = self.next_token()?;
            parens_depth += match token {
                (Token::OpenParen, _) => 1,
                (Token::CloseParen, _) => -1,
                (Token::Eof, pos) => {
                    return Err(self.err(ParserError::UnexpectedToken(Token::Eof), pos));
                }
                _ => 0,
            };
            result.push(token.0);
        }
        Ok(result)
    }

    /// Consumes and drops tokens until the matching closing parenthesis is reached.
    fn ignore_until_close_parens(&mut self) -> CarcaraResult<()> {
        self.read_until_close_parens()?;
        Ok(())
    }

    /// Consumes and ignores attributes and their values until a closing parenthesis is reached.
    fn ignore_remaining_attributes(&mut self) -> CarcaraResult<()> {
        while let Token::Keyword(_) = self.current_token {
            self.next_token()?;
            match self.current_token {
                // If we reached the closing parenthesis or the end of the file, we stop
                Token::CloseParen | Token::Eof => break,

                // If there is no value for this attribute, we may encounter the next attribute, in
                // which case we must continue without consuming the keyword token
                Token::Keyword(_) => (),

                // If there is a single token as a value we consume it
                Token::Symbol(_)
                | Token::Numeral(_)
                | Token::Decimal(_)
                | Token::Bitvector(_, _)
                | Token::String(_)
                | Token::ReservedWord(_) => {
                    self.next_token()?;
                }

                // And if the value is an s-expression we read tokens until it's closed
                Token::OpenParen => {
                    self.next_token()?;
                    self.ignore_until_close_parens()?;
                }
            }
            if self.current_token == Token::CloseParen {
                break;
            }
        }
        Ok(())
    }

    /// Reads an SMT-LIB script and parses the assertions, declarations and definitions.
    ///
    /// The following commands are parsed:
    ///
    /// - `assert`
    /// - `declare-const`
    /// - `declare-fun`
    /// - `declare-sort`
    /// - `define-fun`
    /// - `set-logic`
    ///
    /// All other commands are ignored. This method returns a hash set containing the premises
    /// introduced in `assert` commands.
    pub fn parse_problem(&mut self) -> CarcaraResult<Problem> {
        self.problem = Some(Problem::new());

        while self.current_token != Token::Eof {
            self.expect_token(Token::OpenParen)?;
            match self.next_token()?.0 {
                Token::ReservedWord(Reserved::DeclareFun) => {
                    let (name, sort) = self.parse_declare_fun()?;
                    self.declare_symbol(name.clone(), sort.clone());
                    self.prelude().function_declarations.push((name, sort));
                }
                Token::ReservedWord(Reserved::DeclareConst) => {
                    let name = self.expect_symbol()?;
                    let sort = self.parse_sort()?;
                    self.expect_token(Token::CloseParen)?;
                    self.declare_symbol(name.clone(), sort.clone());
                    self.prelude().function_declarations.push((name, sort));
                }
                Token::ReservedWord(Reserved::DeclareSort) => {
                    let (name, arity) = self.parse_declare_sort()?;

                    self.prelude().sort_declarations.push((name.clone(), arity));

                    // User declared sorts are represented with the `Atom` sort kind, and an
                    // argument which is a string terminal representing the sort name.
                    self.state.sort_declarations.insert(name, arity);
                }
                Token::ReservedWord(Reserved::DeclareDatatype) => self.parse_declare_datatype()?,
                Token::ReservedWord(Reserved::DeclareDatatypes) => {
                    self.parse_declare_datatypes()?;
                }
                Token::ReservedWord(Reserved::DefineFun) => {
                    let (name, func_def) = self.parse_define_fun()?;

                    if self.config.apply_function_defs {
                        self.state.function_defs.insert(name, func_def);
                    } else {
                        // If `self.apply_function_defs` is false, we instead add the function name
                        // to the symbol table, and add a new premise that defines the function
                        let lambda_term = if func_def.params.is_empty() {
                            func_def.body
                        } else {
                            self.pool.add(Term::Binder(
                                Binder::Lambda,
                                BindingList(func_def.params),
                                func_def.body,
                            ))
                        };
                        let sort = self.pool.sort(&lambda_term);
                        self.declare_symbol(name.clone(), sort.clone());
                        let var_term = self.pool.add((name, sort).into());
                        let assertion_term = self
                            .pool
                            .add(Term::Op(Operator::Equals, vec![var_term, lambda_term]));
                        self.premises().insert(assertion_term);
                    }
                }
                Token::ReservedWord(Reserved::DefineFunRec) => self.parse_define_fun_rec(false)?,
                Token::ReservedWord(Reserved::DefineFunsRec) => self.parse_define_fun_rec(true)?,
                Token::ReservedWord(Reserved::DefineSort) => {
                    let (name, def) = self.parse_define_sort()?;
                    self.state.sort_defs.insert(name, def);
                }
                Token::ReservedWord(Reserved::Assert) => {
                    let term = self.parse_term()?;
                    self.expect_token(Token::CloseParen)?;
                    self.premises().insert(term);
                }
                Token::ReservedWord(Reserved::CheckSatAssuming) => {
                    self.expect_token(Token::OpenParen)?;
                    let terms = self.parse_sequence(Self::parse_term, true)?;
                    self.expect_token(Token::CloseParen)?;
                    self.premises().extend(terms);
                }
                Token::ReservedWord(Reserved::SetLogic) => {
                    let logic = self.expect_symbol()?;
                    self.expect_token(Token::CloseParen)?;
                    self.prelude().logic = Some(logic.clone());

                    // When the problem's logic contains real numbers but not integers, integer
                    // literals should be parsed as reals. For instance, `1` should be interpreted
                    // as `1.0`. We must be careful to avoid false positives with non-standard
                    // logics like "HORN".
                    self.is_real_only_logic =
                        (logic.contains("LRA") || logic.contains("NRA") || logic.contains("RDL"))
                            && !logic.contains('I');
                }
                _ => {
                    // If the command is not one of the commands we care about, we just ignore it.
                    // We do that by reading tokens until the command parenthesis is closed
                    self.ignore_until_close_parens()?;
                }
            }
        }
        Ok(self.problem.take().unwrap())
    }

    /// Parses a proof in the Alethe format. All function, constant and sort declarations needed
    /// should already be in the parser state. Note that the `premises` field in the proof will not
    /// be set.
    pub fn parse_proof(&mut self) -> CarcaraResult<Proof> {
        // To avoid stack overflows in proofs with many nested subproofs, we parse the subproofs
        // iteratively, instead of recursively. Therefore, we need to manually keep a stack.
        //
        // Each frame of the stack stores the subproof that is being constructed, the id of the
        // step that will end it, and a bool representing whether a `step` has been issued yet.
        // The first frame of the stack represents the root proof, so every
        // field except for the subproof commands is irrelevant.
        let mut stack: Vec<(Subproof, String, bool)> =
            vec![(Subproof::default(), String::new(), false)];

        let mut next_subproof_context_id = 0;

        let mut constant_definitions = Vec::new();

        // Some proofs may include an extra set of surrounding parentheses around the whole proof
        let mut has_extra_surrounding_parens = false;
        let mut read_first_token = false;

        // Some solvers print the satisfiability result (unsat) together with the proof. To save the
        // user from having to remove this, we consume this first "unsat" token if it exists
        if self.current_token == Token::Symbol("unsat".into()) {
            self.next_token()?;
        }

        while self.current_token != Token::Eof && self.current_token != Token::CloseParen {
            self.expect_token(Token::OpenParen)?;

            if !read_first_token && self.current_token == Token::OpenParen
                || self.current_token == Token::CloseParen
            {
                has_extra_surrounding_parens = true;
                read_first_token = true;
                continue;
            }
            read_first_token = true;

            let (token, position) = self.next_token()?;

            let (id, command) = match token {
                Token::ReservedWord(Reserved::Assume) => {
                    let (id, term) = self.parse_assume_command()?;

                    // Check whether the assume appears after a step.
                    if stack.last().unwrap().2 {
                        // It is permissible but weird if it happens at the top level.
                        if stack.len() == 1 {
                            log::warn!("`assume` command '{}' appears after `step` commands", &id);
                        }
                        // It is disallowed within subproofs.
                        else {
                            return Err(
                                self.err(ParserError::AssumeAfterStepInSubproof(id), position)
                            );
                        }
                    }

                    (id.clone(), ProofCommand::Assume { id, term })
                }
                Token::ReservedWord(Reserved::Step) => {
                    stack.last_mut().unwrap().2 = true;
                    let step = self.parse_step_command()?;
                    (step.id.clone(), ProofCommand::Step(step))
                }
                Token::ReservedWord(Reserved::DefineFun) => {
                    let (name, func_def) = self.parse_define_fun()?;
                    if func_def.params.is_empty() {
                        constant_definitions.push((name.clone(), func_def.body.clone()));
                    }
                    self.state.function_defs.insert(name, func_def);
                    continue;
                }
                Token::ReservedWord(Reserved::Anchor) => {
                    let (end_step_id, args) = self.parse_anchor_command()?;

                    // When we encounter an `anchor` command, we push a new scope into the step ids
                    // symbol table, a fresh commands vector into the commands stack for the
                    // subproof to fill, and the `anchor` data (end step and arguments) into their
                    // respective stacks. All of this will be popped off at the end of the subproof.
                    // We don't need to push a new scope into the symbol table because
                    // `Parser::parse_anchor_command` already does that for us
                    self.state.step_ids.push_scope();
                    let subproof = Subproof {
                        commands: Vec::new(),
                        args,
                        context_id: next_subproof_context_id,
                    };
                    stack.push((subproof, end_step_id, false));
                    next_subproof_context_id += 1;
                    continue;
                }
                _ => {
                    return Err(self.err(ParserError::UnexpectedToken(token), position));
                }
            };
            let id = HashCache::new(id);
            if self.state.step_ids.get(&id).is_some() {
                return Err(self.err(ParserError::RepeatedStepId(id.unwrap()), position));
            }

            let (top_subproof, top_end_step, _) = stack.last_mut().unwrap();
            top_subproof.commands.push(command);
            if top_end_step == id.as_ref() {
                // If this is the last step in a subproof, we need to pop all the subproof data off
                // of the stacks and build the subproof command with it
                self.state.symbol_table.pop_scope();
                self.state.step_ids.pop_scope();
                let (subproof, _, _) = stack.pop().unwrap();

                // The subproof must contain at least two commands: the end step and the previous
                // command it implicitly references
                if subproof.commands.len() < 2 {
                    return Err(self.err(ParserError::EmptySubproof(id.unwrap()), position));
                }

                // We also need to make sure that the last command is in fact a `step`
                if !subproof.commands.last().unwrap().is_step() {
                    return Err(self.err(
                        ParserError::LastSubproofStepIsNotStep(id.unwrap()),
                        position,
                    ));
                }

                let (outer, _, _) = stack.last_mut().unwrap();
                outer.commands.push(ProofCommand::Subproof(subproof));
            }
            let index = stack.last().unwrap().0.commands.len() - 1;
            self.state.step_ids.insert(id, index);
        }

        if has_extra_surrounding_parens {
            self.expect_token(Token::CloseParen)?;
        }
        self.expect_token(Token::Eof)?;

        let commands = match stack.len() {
            0 => unreachable!(),
            1 => stack.pop().unwrap().0.commands,

            // If there is more than one layer in the stack, we are inside a subproof that should be
            // closed before the outer proof is finished
            _ => {
                return Err(self.err(
                    ParserError::UnclosedSubproof(stack.pop().unwrap().1),
                    self.current_position,
                ));
            }
        };
        Ok(Proof {
            constant_definitions,
            commands,
            filename: self.lexer.source_name.into(),
        })
    }

    /// Parses an `assume` proof command. This method assumes that the `(` and `assume` tokens were
    /// already consumed.
    fn parse_assume_command(&mut self) -> CarcaraResult<(String, Rc<Term>)> {
        let id = self.expect_symbol()?;
        let term = self.parse_term_expecting_sort(&Sort::Bool)?;
        self.ignore_remaining_attributes()?;
        self.expect_token(Token::CloseParen)?;
        Ok((id, term))
    }

    /// Parses a `step` proof command. This method assumes that the `(` and `step` tokens were
    /// already consumed.
    fn parse_step_command(&mut self) -> CarcaraResult<ProofStep> {
        let id = self.expect_symbol()?;
        let clause = self.parse_clause()?;
        self.expect_token(Token::Keyword("rule".into()))?;
        let rule = match self.next_token()? {
            (Token::Symbol(s), _) => s,
            (Token::ReservedWord(r), _) => format!("{}", r),
            (other, pos) => {
                return Err(self.err(ParserError::UnexpectedToken(other), pos));
            }
        };

        let premises = if self.current_token == Token::Keyword("premises".into()) {
            self.next_token()?;
            self.expect_token(Token::OpenParen)?;
            self.parse_sequence(Self::parse_step_premise, true)?
        } else {
            Vec::new()
        };

        let args = if self.current_token == Token::Keyword("args".into()) {
            self.next_token()?;
            self.expect_token(Token::OpenParen)?;

            if rule == "hole" && !self.config.parse_hole_args {
                let marker = match &self.current_token {
                    Token::String(marker) => Some(self.pool.add(Term::new_string(marker.clone()))),
                    _ => None,
                };
                self.ignore_until_close_parens()?;
                marker.into_iter().collect()
            } else {
                self.parse_sequence(Self::parse_term, true)?
            }
        } else {
            Vec::new()
        };

        // For some rules (notably the `subproof` rule), there is also a `:discharge` attribute that
        // takes a series of command ids, in addition to the regular premises
        let discharge = if self.current_token == Token::Keyword("discharge".into()) {
            self.next_token()?;
            self.expect_token(Token::OpenParen)?;
            self.parse_sequence(|p| p.parse_discharge_premise(&id), true)?
        } else {
            Vec::new()
        };

        self.ignore_remaining_attributes()?;
        self.expect_token(Token::CloseParen)?;

        Ok(ProofStep {
            id,
            clause,
            rule,
            premises,
            args,
            discharge,
        })
    }

    /// Parses a premise for a `step` command. This already converts it into the depth and command
    /// index used to reference commands in the AST.
    fn parse_step_premise(&mut self) -> CarcaraResult<(usize, usize)> {
        let position = self.current_position;
        let id = HashCache::new(self.expect_symbol()?);
        self.state
            .step_ids
            .get_with_depth(&id)
            .map(|(d, &i)| (d, i))
            .ok_or_else(|| self.err(ParserError::UndefinedStepId(id.unwrap()), position))
    }

    /// Parses an argument for the `:discharge` attribute.
    ///
    /// Due to a bug in veriT, commands local to the current subproof are passed by their "relative"
    /// id. That is, the command `t5.t4.h2` is passed as simply `h2`. This behavior is not present
    /// in other SMT solvers, like cvc5. To work around that, this function tries to find the
    /// command considering both possibilities.
    fn parse_discharge_premise(&mut self, root_id: &str) -> CarcaraResult<(usize, usize)> {
        let position = self.current_position;
        let id = self.expect_symbol()?;
        let absolute_id = format!("{}.{}", root_id, &id);
        let id = HashCache::new(id);
        let absolute_id = HashCache::new(absolute_id);
        self.state
            .step_ids
            .get_with_depth(&absolute_id)
            .or_else(|| self.state.step_ids.get_with_depth(&id))
            .map(|(d, &i)| (d, i))
            .ok_or_else(|| self.err(ParserError::UndefinedStepId(id.unwrap()), position))
    }

    /// Parses an `anchor` proof command. This method assumes that the `(` and `anchor` tokens were
    /// already consumed.
    ///
    /// In order to parse the subproof arguments, this method pushes a new scope into the symbol
    /// table which must be removed after parsing the subproof.
    fn parse_anchor_command(&mut self) -> CarcaraResult<(String, Vec<AnchorArg>)> {
        self.expect_token(Token::Keyword("step".into()))?;
        let end_step_id = self.expect_symbol()?;

        // We have to push a new scope into the symbol table in order to parse the subproof
        // arguments
        self.state.symbol_table.push_scope();

        let args = if self.current_token == Token::Keyword("args".into()) {
            self.next_token()?;
            self.expect_token(Token::OpenParen)?;
            self.parse_sequence(Parser::parse_anchor_argument, true)?
        } else {
            Vec::new()
        };
        self.ignore_remaining_attributes()?;
        self.expect_token(Token::CloseParen)?;
        Ok((end_step_id, args))
    }

    /// Parses an argument for an `anchor` proof command. This can be either a variable binding of
    /// the form `(<symbol> <sort>)` or an assignment, of the form `(:= (<symbol> <sort>) <term>)`.
    fn parse_anchor_argument(&mut self) -> CarcaraResult<AnchorArg> {
        self.expect_token(Token::OpenParen)?;
        Ok(if self.current_token == Token::Keyword("=".into()) {
            self.next_token()?;

            // To make Carcara more robust to recent changes in the Alethe format, we support
            // parsing the two versions of assign-style anchor arguments:
            // - the old version, without the sort hint: `(:= <symbol> <term>)`
            // - and the new version, with the sort hint: `(:= (<symbol> <sort>) <term>)`
            // However, if "strict" parsing is enabled, we only allow the new version
            let (var, value, sort) =
                if !self.config.strict && matches!(self.current_token, Token::Symbol(_)) {
                    let var = self.expect_symbol()?;
                    let value = self.parse_term()?;
                    let sort = self.pool.sort(&value);
                    (var, value, sort)
                } else {
                    let (var, sort) = self.parse_sorted_var()?;
                    let value = self.parse_term_expecting_sort(&sort)?;
                    (var, value, sort)
                };
            self.declare_symbol(var.clone(), sort.clone());
            self.expect_token(Token::CloseParen)?;
            AnchorArg::Assign((var, sort), value)
        } else {
            let symbol = self.expect_symbol()?;
            let sort = self.parse_sort()?;
            self.declare_symbol(symbol.clone(), sort.clone());
            self.expect_token(Token::CloseParen)?;
            AnchorArg::Variable((symbol, sort))
        })
    }

    /// Parses a `declare-fun` proof command. Returns the function name and its sort. This method
    /// assumes that the `(` and `declare-fun` tokens were already consumed.
    fn parse_declare_fun(&mut self) -> CarcaraResult<(String, Rc<Sort>)> {
        let name = self.expect_symbol()?;
        let sort = {
            self.expect_token(Token::OpenParen)?;
            let mut sorts = self.parse_sequence(Parser::parse_sort, false)?;
            sorts.push(self.parse_sort()?);
            if sorts.len() == 1 {
                sorts.into_iter().next().unwrap()
            } else {
                self.pool.add_sort(Sort::Function(sorts))
            }
        };
        self.expect_token(Token::CloseParen)?;
        Ok((name, sort))
    }

    /// Parses a declare-sort proof command. Returns the sort name and its arity. This method
    /// assumes that the `(` and `declare-sort` tokens were already consumed.
    fn parse_declare_sort(&mut self) -> CarcaraResult<(String, usize)> {
        let name = self.expect_symbol()?;
        let arity_pos = self.current_position;
        let arity = self.expect_numeral()?;
        self.expect_token(Token::CloseParen)?;
        let arity = arity
            .to_usize()
            .ok_or(self.err(ParserError::InvalidSortArity(arity), arity_pos))?;
        Ok((name, arity))
    }

    /// Parses a function declaration, of the form `(<symbol> (<sorted var>*) <sort>)`. If the
    /// parameter `consume_parens` is `false`, the opening and closing parentheses are not consumed
    fn parse_function_dec(
        &mut self,
        consume_parens: bool,
    ) -> CarcaraResult<(String, Vec<SortedVar>, Rc<Sort>)> {
        if consume_parens {
            self.expect_token(Token::OpenParen)?;
        }
        let name = self.expect_symbol()?;
        self.expect_token(Token::OpenParen)?;
        let params = self.parse_sequence(Self::parse_sorted_var, false)?;
        let return_sort = self.parse_sort()?;
        if consume_parens {
            self.expect_token(Token::CloseParen)?;
        }
        Ok((name, params, return_sort))
    }

    /// Parses a `define-fun` proof command. Returns the function name and its definition. This
    /// method assumes that the `(` and `define-fun` tokens were already consumed.
    fn parse_define_fun(&mut self) -> CarcaraResult<(String, FunctionDef)> {
        let (name, params, return_sort) = self.parse_function_dec(false)?;

        // In order to correctly parse the function body, we push a new scope to the symbol table
        // and add the functions arguments to it.
        self.state.symbol_table.push_scope();
        for (var, sort) in &params {
            self.declare_symbol(var.clone(), sort.clone());
        }
        let body = self.parse_term_expecting_sort(&return_sort)?;
        self.state.symbol_table.pop_scope();

        self.expect_token(Token::CloseParen)?;

        Ok((name, FunctionDef { params, body }))
    }

    /// Adds the premise corresponding to a `define-fun-rec` function definition.
    fn add_define_fun_rec_premise(&mut self, name: String, params: Vec<SortedVar>, body: Rc<Term>) {
        let application = {
            let cached = HashCache::new(name);
            let func_sort = self.state.symbol_table.get(&cached).unwrap();
            let name = cached.unwrap();
            let func_term = self.pool.add((name, func_sort.clone()).into());
            if params.is_empty() {
                func_term
            } else {
                let args = params
                    .iter()
                    .map(|var| self.pool.add(var.clone().into()))
                    .collect();
                self.pool.add(Term::App(func_term, args))
            }
        };
        let equality_term = build_term!(self.pool, (= {application} {body}));
        let premise = if params.is_empty() {
            equality_term
        } else {
            let bindings = BindingList(params);
            self.pool
                .add(Term::Binder(Binder::Forall, bindings, equality_term))
        };
        self.premises().insert(premise);
    }

    /// Parses a `define-fun-rec`/`define-funs-rec` command. Inserts the function names into the
    /// symbol table, and adds the appropriate premises. This method assumes the `(` and
    /// `define-fun-rec`/`define-funs-rec` tokens were already consumed.
    fn parse_define_fun_rec(&mut self, is_multiple: bool) -> CarcaraResult<()> {
        let declarations = if is_multiple {
            self.expect_token(Token::OpenParen)?;
            self.parse_sequence(|p| p.parse_function_dec(true), true)?
        } else {
            vec![self.parse_function_dec(false)?]
        };

        for (name, params, return_sort) in &declarations {
            let sort = if params.is_empty() {
                return_sort.clone()
            } else {
                let mut param_sorts: Vec<_> = params.iter().map(|(_, sort)| sort.clone()).collect();
                param_sorts.push(return_sort.clone());
                self.pool.add_sort(Sort::Function(param_sorts))
            };
            self.declare_symbol(name.clone(), sort);
        }

        if is_multiple {
            self.expect_token(Token::OpenParen)?;
        }
        for (name, params, return_sort) in declarations {
            self.state.symbol_table.push_scope();
            for (var, sort) in &params {
                self.declare_symbol(var.clone(), sort.clone());
            }
            let body = self.parse_term_expecting_sort(&return_sort)?;
            self.state.symbol_table.pop_scope();

            self.add_define_fun_rec_premise(name, params, body);
        }
        if is_multiple {
            self.expect_token(Token::CloseParen)?;
        }
        self.expect_token(Token::CloseParen)?;

        Ok(())
    }

    /// Parses a `define-sort` proof command. Returns the sort name and its definition. This method
    /// assumes that the `(` and `define-sort` tokens were already consumed.
    fn parse_define_sort(&mut self) -> CarcaraResult<(String, SortDef)> {
        let name = self.expect_symbol()?;
        self.expect_token(Token::OpenParen)?;
        let params = self.parse_sequence(Self::expect_symbol, false)?;

        // In order to correctly parse the sort definition, we push a new scope to the symbol table
        // and add the sort parameters to it.
        self.state.symbol_table.push_scope();
        for s in &params {
            let sort = self.pool.add_sort(Sort::Type);
            self.declare_symbol(s.clone(), sort);
        }
        let body = self.parse_sort()?;
        self.state.symbol_table.pop_scope();

        self.expect_token(Token::CloseParen)?;

        Ok((name, SortDef { params, body }))
    }

    /// Parses a clause of the form `(cl <term>*)`.
    fn parse_clause(&mut self) -> CarcaraResult<Vec<Rc<Term>>> {
        self.expect_token(Token::OpenParen)?;
        self.expect_token(Token::ReservedWord(Reserved::Cl))?;
        self.parse_sequence(|p| p.parse_term_expecting_sort(&Sort::Bool), false)
    }

    /// Parses a sorted variable of the form `(<symbol> <sort>)`.
    fn parse_sorted_var(&mut self) -> CarcaraResult<SortedVar> {
        self.expect_token(Token::OpenParen)?;
        let symbol = self.expect_symbol()?;
        let sort = self.parse_sort()?;
        self.expect_token(Token::CloseParen)?;
        Ok((symbol, sort))
    }

    /// Parses a term.
    pub fn parse_term(&mut self) -> CarcaraResult<Rc<Term>> {
        let term = match self.next_token()? {
            (Token::Bitvector(value, width), _) => Term::new_bv(value, width),
            (Token::Numeral(n), _) if self.interpret_ints_as_reals() => Term::new_real(n),
            (Token::Numeral(n), _) => Term::new_int(n),
            (Token::Decimal(r), _) => Term::new_real(r),
            (Token::String(s), _) => Term::new_string(s),
            (Token::Symbol(s), pos) => {
                // Check to see if there is a nullary function defined with this name
                return if let Some(func) = self.state.function_defs.get(&s) {
                    func.apply(self.pool, Vec::new())
                        .map_err(|err| self.err(err, pos))
                } else if let Ok(op) = Operator::from_str(&s) {
                    let args = Vec::new();

                    self.make_op(op, args).map_err(|err| self.err(err, pos))
                } else {
                    self.make_var(s).map_err(|err| self.err(err, pos))
                };
            }
            (Token::OpenParen, _) => return self.parse_application(),
            (other, pos) => {
                return Err(self.err(ParserError::UnexpectedToken(other), pos));
            }
        };
        Ok(self.pool.add(term))
    }

    /// Parses a term and checks that its sort matches the expected sort. If not, returns an error.
    fn parse_term_expecting_sort(&mut self, expected_sort: &Sort) -> CarcaraResult<Rc<Term>> {
        let pos = self.current_position;
        let term = self.parse_term()?;
        self.check_sort_eq(expected_sort, &self.pool.sort(&term))
            .map_err(|e| self.err(e, pos))?;
        Ok(term)
    }

    /// Parses a binder term. This method assumes that the `(` and binder tokens were
    /// already consumed.
    fn parse_binder(&mut self, binder: Binder) -> CarcaraResult<Rc<Term>> {
        self.expect_token(Token::OpenParen)?;
        self.state.symbol_table.push_scope();
        let bindings = if binder == Binder::Choice {
            let (var, sort) = self.parse_sorted_var()?;
            self.declare_symbol(var.clone(), sort.clone());
            self.expect_token(Token::CloseParen)?;
            BindingList(vec![(var, sort)])
        } else {
            BindingList(self.parse_sequence(
                |p| {
                    let (var, sort) = p.parse_sorted_var()?;
                    p.declare_symbol(var.clone(), sort.clone());
                    Ok((var, sort))
                },
                true,
            )?)
        };
        let term = match binder {
            Binder::Lambda => self.parse_term()?,
            _ => self.parse_term_expecting_sort(&Sort::Bool)?,
        };
        self.state.symbol_table.pop_scope();
        self.expect_token(Token::CloseParen)?;
        Ok(self.pool.add(Term::Binder(binder, bindings, term)))
    }

    /// Parses a `let` term. This method assumes that the `(` and `let` tokens were already
    /// consumed.
    fn parse_let_term(&mut self) -> CarcaraResult<Rc<Term>> {
        self.expect_token(Token::OpenParen)?;

        // Since the let binding semantics is *simultaneous*, we first parse all bindings, and only
        // then add them to the symbol table.
        let bindings = self.parse_sequence(
            |p| {
                p.expect_token(Token::OpenParen)?;
                let name = p.expect_symbol()?;
                let value = p.parse_term()?;
                p.expect_token(Token::CloseParen)?;
                Ok((name, value))
            },
            true,
        )?;

        self.state.symbol_table.push_scope();
        for (name, value) in &bindings {
            let sort = self.pool.sort(value);
            self.declare_symbol(name.clone(), sort);
        }

        let inner = self.parse_term()?;
        self.expect_token(Token::CloseParen)?;

        self.state.symbol_table.pop_scope();

        if self.config.expand_lets {
            let substitution = bindings
                .into_iter()
                .map(|(name, value)| {
                    let var = Term::new_var(name, self.pool.sort(&value));
                    (self.pool.add(var), value)
                })
                .collect();

            let result = Substitution::new(self.pool, substitution)
                .unwrap()
                .apply(self.pool, &inner);

            Ok(result)
        } else {
            Ok(self.pool.add(Term::Let(BindingList(bindings), inner)))
        }
    }

    /// Parses an annotated term, of the form `(! <term> <attribute>+)`. This method assumes that
    /// the `(` and `!` tokens were already consumed.
    ///
    /// The two supported attributes are `:named` and `:pattern`, though the latter is ignored. If
    /// any other attribute is present, an error will be returned.
    fn parse_annotated_term(&mut self) -> CarcaraResult<Rc<Term>> {
        let inner = self.parse_term()?;
        self.parse_sequence(
            |p| {
                let attribute = p.expect_keyword()?;
                match attribute.as_str() {
                    "named" => {
                        // If the term has a `:named` attribute, we introduce a new nullary function
                        // definition that maps the name to the term
                        let name = p.expect_symbol()?;
                        let func_def = FunctionDef {
                            params: Vec::new(),
                            body: inner.clone(),
                        };
                        p.state.function_defs.insert(name, func_def);
                        Ok(())
                    }

                    // We allow unknown attributes, and just ignore them
                    _ => match p.current_token {
                        // If the argument is a list, we consume it until the `)` token
                        Token::OpenParen => {
                            p.next_token()?;
                            p.ignore_until_close_parens()
                        }

                        // If the attribute has no argument, we don't do anything
                        Token::Keyword(_) | Token::CloseParen | Token::Eof => Ok(()),

                        // If the argument is a single token, we consume it
                        _ => {
                            p.next_token()?;
                            Ok(())
                        }
                    },
                }
            },
            true,
        )?;
        Ok(inner)
    }

    fn parse_indexed_operator(&mut self) -> CarcaraResult<(ParamOperator, Vec<Rc<Term>>)> {
        let op_symbol = self.expect_symbol()?;

        if let Some(value) = op_symbol.strip_prefix("bv") {
            let parsed_value = value.parse::<Integer>().unwrap();
            let args = self.parse_sequence(Self::parse_term, true)?;
            let mut constant_args = Vec::new();
            for arg in args {
                if let Some(i) = arg.as_signed_integer() {
                    constant_args.push(self.pool.add(Term::Const(Constant::Integer(i))));
                } else {
                    return Err(self.err(
                        ParserError::ExpectedIntegerConstant(arg.clone()),
                        self.current_position,
                    ));
                }
            }
            constant_args.insert(
                0,
                self.pool.add(Term::Const(Constant::Integer(parsed_value))),
            );
            return Ok((ParamOperator::BvConst, constant_args));
        }
        let op = ParamOperator::from_str(op_symbol.as_str()).map_err(|_| {
            self.err(
                ParserError::InvalidIndexedOp(op_symbol),
                self.current_position,
            )
        })?;
        if op == ParamOperator::Tester {
            let cons = self.parse_term()?;
            self.expect_token(Token::CloseParen)?;
            let args = vec![cons.clone()];
            return Ok((op, args));
        }
        let args = self.parse_sequence(Self::parse_term, true)?;
        let mut constant_args = Vec::new();
        for arg in args {
            if let Some(i) = arg.as_signed_integer() {
                constant_args.push(self.pool.add(Term::Const(Constant::Integer(i))));
            } else {
                return Err(self.err(
                    ParserError::ExpectedIntegerConstant(arg.clone()),
                    self.current_position,
                ));
            }
        }
        Ok((op, constant_args))
    }

    /// Constructs, check operation arguments and sort checks an indexed operation term.
    fn make_indexed_op(
        &mut self,
        op: ParamOperator,
        op_args: Vec<Rc<Term>>,
        args: Vec<Rc<Term>>,
    ) -> Result<Rc<Term>, ParserError> {
        let sorts: Vec<_> = args.iter().map(|t| self.pool.sort(t)).collect();
        let op_sorts: Vec<_> = op_args.iter().map(|t| self.pool.sort(t)).collect();
        match &op {
            ParamOperator::BvConst => {
                assert_num_args(&op_args, 2)?;
                assert_num_args(&args, 0)?;
                let value = op_args[0].as_integer().unwrap();
                let width_value = op_args[1].as_integer().unwrap();

                if value < 0 {
                    return Err(ParserError::WrongValueOfArgs((0..).into(), value));
                }
                let width = width_value.to_usize().ok_or_else(|| {
                    ParserError::WrongValueOfArgs((1..).into(), width_value.clone())
                })?;
                if width == 0 {
                    return Err(ParserError::WrongValueOfArgs((1..).into(), width_value));
                }
                return Ok(self.pool.add(Term::Const(Constant::BitVec(value, width))));
            }
            ParamOperator::BvExtract => {
                /*
                ((_ extract i j) (_ BitVec m) (_ BitVec n))

                where
                - i, j, m, n are numerals
                - m > i ≥ j ≥ 0,
                - n = i - j + 1
                 */
                assert_num_args(&op_args, 2)?;
                assert_num_args(&args, 1)?;
                if !sorts[0].is_bitvec() {
                    return Err(ParserError::ExpectedBvSort(sorts[0].clone()));
                }

                for s in &op_sorts {
                    self.check_sort_eq(&Sort::Int, s)?;
                }

                assert_indexed_op_args_value(&op_args, 0..)?;
                let i = op_args[0].as_integer().as_ref().and_then(Integer::to_usize);
                let j = op_args[1].as_integer().as_ref().and_then(Integer::to_usize);

                // j >= 0 is ensured by the parser. We need to ensure that m > i && i >= j, if they
                // are all statically known
                if let (Some(i), Some(j), Sort::BitVec(m)) = (i, j, sorts[0].as_ref())
                    && !(*m > i && i >= j)
                {
                    return Err(ParserError::InvalidExtractArgs(i, j, *m));
                }
            }
            ParamOperator::IntToBv => {
                assert_num_args(&op_args, 1)?;
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::Int, &op_sorts[0])?;
                self.check_sort_eq(&Sort::Int, &sorts[0])?;
            }
            ParamOperator::BvBitOf
            | ParamOperator::BvIntOf
            | ParamOperator::ZeroExtend
            | ParamOperator::SignExtend
            | ParamOperator::RotateLeft
            | ParamOperator::RotateRight
            | ParamOperator::Repeat => {
                assert_num_args(&op_args, 1)?;
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::Int, &op_sorts[0])?;
                if !sorts[0].is_bitvec() {
                    return Err(ParserError::ExpectedBvSort(sorts[0].clone()));
                }
                assert_indexed_op_args_value(&op_args, 0..)?;
            }
            ParamOperator::RePower => {
                assert_num_args(&op_args, 1)?;
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::Int, &op_sorts[0])?;
                self.check_sort_eq(&Sort::RegLan, &sorts[0])?;
                assert_indexed_op_args_value(&op_args, 0..)?;
            }
            ParamOperator::ReLoop => {
                assert_num_args(&op_args, 2)?;
                assert_num_args(&args, 1)?;
                for s in &op_sorts {
                    self.check_sort_eq(&Sort::Int, s)?;
                }
                self.check_sort_eq(&Sort::RegLan, &sorts[0])?;
                assert_indexed_op_args_value(&op_args, 0..)?;
            }
            ParamOperator::Tester => {} // TODO
            ParamOperator::TupleSelect => {
                assert_num_args(&op_args, 1)?;
                assert_num_args(&args, 1)?;
                if op_args[0]
                    .as_integer()
                    .as_ref()
                    .and_then(Integer::to_usize)
                    .is_none()
                {
                    return Err(ParserError::ExpectedIntegerConstant(op_args[0].clone()));
                }
                let Sort::Tuple(elems) = sorts[0].as_ref() else {
                    return Err(ParserError::ExpectedTupleSort(sorts[0].clone()));
                };
                assert_indexed_op_args_value(&op_args, ..elems.len())?;
            }
        }
        Ok(self.pool.add(Term::ParamOp { op, op_args, args }))
    }

    /// Constructs and sort checks a qualified operation term
    fn make_qualified_op(
        &mut self,
        op: QualifiedOperator,
        sort: Rc<Sort>,
        args: Vec<Rc<Term>>,
    ) -> Result<Rc<Term>, ParserError> {
        let sorts: Vec<_> = args.iter().map(|t| self.pool.sort(t)).collect();
        match op {
            QualifiedOperator::Const => {
                assert_num_args(&args, 1)?;
                self.check_array_sort(None, Some(&sorts[0]), &sort)?;
            }
            QualifiedOperator::SetEmpty | QualifiedOperator::SetUniverse => {
                assert_num_args(&args, 0)?;
                check_set_sort(&sort)?;
            }
        }
        Ok(self.pool.add(Term::AsOp(op, sort, args)))
    }

    /// Parses any term that starts with `(`, that is, any term that is not a constant or a
    /// variable. This method assumes that the `(` token was already consumed.
    fn parse_application(&mut self) -> CarcaraResult<Rc<Term>> {
        let head_pos = self.current_position;
        match &self.current_token {
            &Token::ReservedWord(reserved) => {
                self.next_token()?;
                match reserved {
                    Reserved::Underscore => {
                        let (op, op_args) = self.parse_indexed_operator()?;
                        self.make_indexed_op(op, op_args, Vec::new())
                            .map_err(|err| self.err(err, head_pos))
                    }
                    Reserved::As => {
                        let op_symbol = self.expect_symbol()?;
                        if let Ok(op) = QualifiedOperator::from_str(op_symbol.as_str()) {
                            let sort = self.parse_sort()?;
                            self.expect_token(Token::CloseParen)?;
                            self.make_qualified_op(op, sort, Vec::new())
                                .map_err(|err| self.err(err, head_pos))
                        } else {
                            let var = self
                                .make_var(op_symbol.clone())
                                .map_err(|err| self.err(err, self.current_position))?;
                            let var_sort = self.pool.sort(&var);
                            if var_sort.is_par() {
                                let sort = self.parse_sort()?;
                                self.expect_token(Token::CloseParen)?;
                                // TODO test unification
                                // if types are unifiable, create variable with sort
                                Ok(self.pool.add(Term::new_var(op_symbol, sort)))
                            } else {
                                Err(self.err(
                                    ParserError::InvalidQualifiedOp(op_symbol),
                                    self.current_position,
                                ))
                            }
                        }
                    }
                    Reserved::Match => self.parse_match(),
                    Reserved::Exists => self.parse_binder(Binder::Exists),
                    Reserved::Forall => self.parse_binder(Binder::Forall),
                    Reserved::Choice => self.parse_binder(Binder::Choice),
                    Reserved::Lambda => self.parse_binder(Binder::Lambda),
                    Reserved::Bang => self.parse_annotated_term(),
                    Reserved::Let => self.parse_let_term(),
                    Reserved::Cl => {
                        let args = self.parse_sequence(Self::parse_term, false)?;
                        self.make_op(Operator::Cl, args)
                            .map_err(|err| self.err(err, head_pos))
                    }
                    _ => Err(self.err(
                        ParserError::UnexpectedToken(Token::ReservedWord(reserved)),
                        head_pos,
                    )),
                }
            }
            // Here, I would like to use an `if let` guard, like:
            //
            //     Token::Symbol(s) if let Ok(operator) = Operator::from_str(s) => { ... }
            //
            // However, `if let` guards are still nightly only. For more info, see:
            // https://github.com/rust-lang/rust/issues/51114
            Token::Symbol(s) if Operator::from_str(s).is_ok() => {
                let operator = Operator::from_str(s).unwrap();
                self.next_token()?;
                let args = self.parse_sequence(Self::parse_term, true)?;
                self.make_op(operator, args)
                    .map_err(|err| self.err(err, head_pos))
            }
            Token::Symbol(s)
                if ParamOperator::from_str(s).is_ok()
                    && self.config.allow_higher_order_indexed_ops =>
            {
                let op = ParamOperator::from_str(s).unwrap();
                self.next_token()?;
                let mut op_args = self.parse_sequence(Self::parse_term, true)?;
                let args = op_args.split_off(op.num_op_args());
                self.make_indexed_op(op, op_args, args)
                    .map_err(|err| self.err(err, head_pos))
            }
            Token::Symbol(s) if s == "eo" => {
                // "Let" constructions unfold
                self.expect_token(Token::Symbol("eo".to_owned()))?;
                self.expect_keyword()?;
                self.expect_token(Token::Keyword("define".to_owned()))?;
                self.expect_token(Token::OpenParen)?;
                let args = self.parse_sequence(
                    |parser| {
                        parser.expect_token(Token::OpenParen)?;
                        let let_arg = parser.expect_symbol()?;
                        let body = parser.parse_term()?;
                        parser.expect_token(Token::CloseParen)?;
                        Ok((let_arg, body))
                    },
                    true,
                )?;

                self.state.symbol_table.push_scope();
                for (name, value) in &args {
                    let sort = self.pool.sort(value);
                    self.declare_symbol(name.clone(), sort);
                }

                let inner = self.parse_term()?;
                self.expect_token(Token::CloseParen)?;

                self.state.symbol_table.pop_scope();
                let substitution = args
                    .into_iter()
                    .map(|(name, value)| {
                        let var = Term::new_var(name, self.pool.sort(&value));
                        (self.pool.add(var), value)
                    })
                    .collect();

                let result = Substitution::new(self.pool, substitution)
                    .unwrap()
                    .apply(self.pool, &inner);

                Ok(result)
            }
            Token::Symbol(s) if self.state.function_defs.contains_key(s) => {
                let head_pos = self.current_position;
                let func_name = self.expect_symbol()?;
                let args = self.parse_sequence(Self::parse_term, true)?;
                let func = &self.state.function_defs[&func_name];

                func.apply(self.pool, args)
                    .map_err(|err| self.err(err, head_pos))
            }
            Token::OpenParen => {
                self.next_token()?;
                match self.current_token {
                    Token::ReservedWord(Reserved::Underscore) => {
                        self.next_token()?;
                        let (op, op_args) = self.parse_indexed_operator()?;
                        let args = self.parse_sequence(Self::parse_term, true)?;
                        self.make_indexed_op(op, op_args, args)
                            .map_err(|err| self.err(err, head_pos))
                    }
                    Token::ReservedWord(Reserved::As) => {
                        self.next_token()?;
                        let op_symbol = self.expect_symbol()?;
                        if let Ok(op) = QualifiedOperator::from_str(op_symbol.as_str()) {
                            let sort = self.parse_sort()?;
                            self.expect_token(Token::CloseParen)?;
                            let args = self.parse_sequence(Self::parse_term, true)?;
                            self.make_qualified_op(op, sort, args)
                                .map_err(|err| self.err(err, head_pos))
                        } else {
                            let var = self
                                .make_var(op_symbol.clone())
                                .map_err(|err| self.err(err, self.current_position))?;
                            let var_sort = self.pool.sort(&var);
                            if let Sort::Par(_, f_sort) = var_sort.as_ref()
                                && let Sort::Function(sorts) = f_sort.as_ref()
                            {
                                let sort = self.parse_sort()?;
                                self.expect_token(Token::CloseParen)?;
                                // unify return sort with as_sort
                                let ret_sort = sorts.last().unwrap();
                                let mut map = RapidHashMap::new();
                                if !ret_sort.is_compatible_with_map(&sort, &mut map) {
                                    return Err(self.err(
                                        ParserError::IncompatibleSorts(
                                            ret_sort.clone(),
                                            sort.clone(),
                                        ),
                                        self.current_position,
                                    ));
                                }
                                // if types are unifiable, create variable with sort after applying the substitution
                                let result = SortSubstitution::new(map).apply(self.pool, &var_sort);
                                let func = self.pool.add(Term::new_var(op_symbol, result));
                                // now apply it to args
                                let args = self.parse_sequence(Self::parse_term, true)?;
                                return self
                                    .make_app(func, args)
                                    .map_err(|err| self.err(err, head_pos));
                            }
                            Err(self.err(
                                ParserError::InvalidQualifiedOp(op_symbol),
                                self.current_position,
                            ))
                        }
                    }
                    _ => {
                        let func = self.parse_application()?;
                        let args = self.parse_sequence(Self::parse_term, true)?;
                        self.make_app(func, args)
                            .map_err(|err| self.err(err, head_pos))
                    }
                }
            }
            _ => {
                let func = self.parse_term()?;
                let args = self.parse_sequence(Self::parse_term, true)?;
                self.make_app(func, args)
                    .map_err(|err| self.err(err, head_pos))
            }
        }
    }

    fn make_sort(&mut self, name: String, args: Vec<Rc<Sort>>) -> Result<Rc<Sort>, ParserError> {
        let sort = match name.as_str() {
            "->" => Sort::Function(args),
            "Bool" | "Int" | "Real" | "String" | "RegLan" | "Type" if !args.is_empty() => {
                return Err(ParserError::WrongNumberOfArgs(0.into(), args.len()));
            }
            "Bool" => Sort::Bool,
            "Int" => Sort::Int,
            "Real" => Sort::Real,
            "String" => Sort::String,
            "RegLan" => Sort::RegLan,
            "Type" => Sort::Type,
            "Array" => match args.as_slice() {
                [x, y] => Sort::Array(x.clone(), y.clone()),
                _ => return Err(ParserError::WrongNumberOfArgs(2.into(), args.len())),
            },
            "rare-list" | "RareList" => match args.as_slice() {
                [] => Sort::Var("?".to_owned()),
                [s] => return Ok(s.clone()),
                _ => return Err(ParserError::WrongNumberOfArgs(1.into(), args.len())),
            },

            // From sets and relations extension
            "Set" => {
                assert_num_args(&args, 1)?;
                Sort::Set(args[0].clone())
            }
            "Tuple" => {
                assert_num_args(&args, 1..)?;
                Sort::Tuple(args)
            }
            "UnitTuple" => {
                assert_num_args(&args, 0)?;
                Sort::Tuple(Vec::new())
            }
            "Relation" => {
                assert_num_args(&args, 1..)?;
                Sort::Set(self.pool.add_sort(Sort::Tuple(args)))
            }

            // Local sort parameter
            other if self.has_sort_symbol(other) => Sort::Var(other.to_owned()),

            // Local sort parameter, but with leading `@` implicitly removed
            other
                if self.config.implicit_at_sort_alias
                    && self.has_sort_symbol(&format!("@{}", other)) =>
            {
                Sort::Var(other.to_owned())
            }

            // Sort definition, from `define-sort`
            other if self.state.sort_defs.contains_key(other) => {
                let def = &self.state.sort_defs[other];
                return if def.params.len() != args.len() {
                    Err(ParserError::WrongNumberOfArgs(
                        def.params.len().into(),
                        args.len(),
                    ))
                } else if def.params.is_empty() {
                    Ok(def.body.clone())
                } else {
                    let substitution = def.params.iter().cloned().zip(args).collect();
                    let result = SortSubstitution::new(substitution).apply(self.pool, &def.body);
                    Ok(result)
                };
            }

            // Datatype sort, from `declare-datatype(s)`
            other if self.state.datatype_declarations.get(other).is_some() => {
                let arity = self.state.datatype_declarations.get(other).unwrap();
                if *arity == args.len() {
                    Sort::Datatype { name: name.into_boxed_str(), args }
                } else {
                    return Err(ParserError::WrongNumberOfArgs((*arity).into(), args.len()));
                }
            }

            // Sort declaration, from `declare-sort`
            other if self.state.sort_declarations.contains_key(other) => {
                let arity = &self.state.sort_declarations[other];
                if *arity == args.len() {
                    Sort::Atom(name.into_boxed_str(), args.into_boxed_slice())
                } else {
                    return Err(ParserError::WrongNumberOfArgs((*arity).into(), args.len()));
                }
            }

            // Unknown
            _ => return Err(ParserError::UndefinedSort(name)),
        };
        Ok(self.pool.add_sort(sort))
    }

    fn make_indexed_sort(
        &mut self,
        name: String,
        args: Vec<Rc<Term>>,
    ) -> Result<Rc<Sort>, ParserError> {
        match name.as_str() {
            "BitVec" => {
                if args.len() != 1 {
                    return Err(ParserError::WrongNumberOfArgs(1.into(), args.len()));
                }
                let sort = if let Some(width) = args[0].as_integer() {
                    Sort::BitVec(width.to_usize().unwrap())
                } else {
                    // TODO: used to be an error. maybe still should be an error outside rare files
                    Sort::ParamBitVec
                };
                Ok(self.pool.add_sort(sort))
            }
            _ => Err(ParserError::UndefinedSort(name)),
        }
    }

    /// Parses a sort.
    fn parse_sort(&mut self) -> CarcaraResult<Rc<Sort>> {
        let pos = self.current_position;
        let (name, args) = match self.next_token()?.0 {
            Token::Symbol(s) => (s, Vec::new()),
            Token::OpenParen if self.current_token == Token::ReservedWord(Reserved::Underscore) => {
                self.next_token()?;
                let name = self.expect_symbol()?;
                let args = self.parse_sequence(Self::parse_term, true)?;
                return self
                    .make_indexed_sort(name, args)
                    .map_err(|e| self.err(e, pos));
            }
            Token::OpenParen => {
                let name = self.expect_symbol()?;

                // Currently `BitVec` is the only indexed/dependently typed sort
                if name == "BitVec" && self.config.allow_higher_order_indexed_ops {
                    let args = self.parse_sequence(Self::parse_term, true)?;
                    return self
                        .make_indexed_sort(name, args)
                        .map_err(|e| self.err(e, pos));
                }
                let args = self.parse_sequence(Parser::parse_sort, true)?;
                (name, args)
            }
            other => {
                return Err(self.err(ParserError::UnexpectedToken(other), pos));
            }
        };
        self.make_sort(name, args).map_err(|e| self.err(e, pos))
    }
}
