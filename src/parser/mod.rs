//! A parser for the veriT Proof Format.

pub mod error;
pub mod lexer;
pub mod tests;

use crate::{ast::*, utils::Either};
use ahash::AHashMap;
use error::*;
use lexer::*;
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use std::{hash::Hash, io::BufRead, str::FromStr};

pub fn parse_problem_proof<T: BufRead>(problem: T, proof: T) -> ParserResult<(Proof, TermPool)> {
    let mut problem_parser = Parser::new(problem)?;
    problem_parser.parse_problem()?;

    Parser::with_state(proof, problem_parser.state)?.parse_proof()
}

type AnchorCommand = (String, Vec<(String, ByRefRc<Term>)>, Vec<SortedVar>);
type StepCommand = (Vec<ByRefRc<Term>>, String, Vec<String>, Vec<ProofArg>);

struct SymbolTable<K, V> {
    scopes: Vec<AHashMap<K, V>>,
}

impl<K, V> SymbolTable<K, V> {
    fn new() -> Self {
        Self { scopes: vec![AHashMap::new()] }
    }

    fn push_scope(&mut self) {
        self.scopes.push(AHashMap::new());
    }

    fn pop_scope(&mut self) {
        match self.scopes.len() {
            0 => unreachable!(),
            1 => panic!("cannot pop last scope in symbol table"),
            _ => {
                self.scopes.pop().expect("no scopes in symbol table");
            }
        }
    }
}

impl<K: Eq + Hash, V> SymbolTable<K, V> {
    fn get(&self, key: &K) -> Option<&V> {
        self.scopes.iter().rev().find_map(|scope| scope.get(key))
    }

    fn insert(&mut self, key: K, value: V) {
        self.scopes
            .last_mut()
            .expect("no scopes in symbol table")
            .insert(key, value);
    }
}

impl<K, V> Default for SymbolTable<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Default)]
struct ParserState {
    sorts_symbol_table: SymbolTable<Identifier, ByRefRc<Term>>,
    function_defs: AHashMap<String, FunctionDef>,
    term_pool: TermPool,
    sort_declarations: AHashMap<String, (u64, ByRefRc<Term>)>,
    step_indices: SymbolTable<String, usize>,
}

/// A parser for the veriT Proof Format. The parser makes use of hash consing to reduce memory usage
/// by sharing identical terms in the AST.
pub struct Parser<R> {
    lexer: Lexer<R>,
    current_token: Token,
    state: ParserState,
}

impl<R: BufRead> Parser<R> {
    /// Constructs a new `Parser` from a type that implements `BufRead`. This operation can fail if
    /// there is an IO or lexer error on the first token.
    pub fn new(input: R) -> ParserResult<Self> {
        let mut state = ParserState::default();
        let builtins = vec![("true", Term::BOOL_SORT), ("false", Term::BOOL_SORT)];
        for (iden, sort) in builtins {
            let iden = Identifier::Simple(iden.into());
            let sort = state.term_pool.add_term(sort.clone());
            state.sorts_symbol_table.insert(iden, sort);
        }
        Parser::with_state(input, state)
    }

    /// Constructs a new `Parser` using an existing `ParserState`. This operation can fail if there
    /// is an IO or lexer error on the first token.
    fn with_state(input: R, state: ParserState) -> ParserResult<Self> {
        let mut lexer = Lexer::new(input)?;
        let current_token = lexer.next_token()?;
        Ok(Parser { lexer, current_token, state })
    }

    /// Advances the parser one token, and returns the previous `current_token`.
    fn next_token(&mut self) -> ParserResult<Token> {
        let new = self.lexer.next_token()?;
        Ok(std::mem::replace(&mut self.current_token, new))
    }

    /// Helper method to build a parser error with the current lexer position.
    fn err(&self, err: ErrorKind) -> ParserError {
        ParserError(err, Some(self.lexer.position))
    }

    /// Shortcut for `self.state.term_pool.add_term`.
    fn add_term(&mut self, term: Term) -> ByRefRc<Term> {
        self.state.term_pool.add_term(term)
    }

    /// Shortcut for `self.state.term_pool.add_all`.
    fn add_all(&mut self, term: Vec<Term>) -> Vec<ByRefRc<Term>> {
        self.state.term_pool.add_all(term)
    }

    /// Helper method to insert a `SortedVar` into the parser symbol table.
    fn insert_sorted_var(&mut self, (symbol, sort): SortedVar) {
        self.state
            .sorts_symbol_table
            .insert(Identifier::Simple(symbol), sort)
    }

    /// Helper method to build a `ErrorKind::UnexpectedToken` error.
    fn unexpected_token(&self, got: Token) -> ParserError {
        self.err(ErrorKind::UnexpectedToken(got))
    }

    /// Constructs and sort checks a variable term.
    fn make_var(&mut self, iden: Identifier) -> Result<Term, ErrorKind> {
        let sort = self
            .state
            .sorts_symbol_table
            .get(&iden)
            .ok_or_else(|| ErrorKind::UndefinedIden(iden.clone()))?;
        Ok(Term::Terminal(Terminal::Var(iden, sort.clone())))
    }

    /// Constructs and sort checks an operation term.
    fn make_op(&mut self, op: Operator, args: Vec<Term>) -> Result<Term, ErrorKind> {
        let sorts: Vec<_> = args.iter().map(Term::sort).collect();
        match op {
            Operator::Not => {
                ErrorKind::assert_num_of_args(&args, 1)?;
                SortError::assert_eq(Term::BOOL_SORT, sorts[0])?;
            }
            Operator::Implies => {
                ErrorKind::assert_num_of_args_range(&args, 2..)?;
                for s in sorts {
                    SortError::assert_eq(Term::BOOL_SORT, s)?;
                }
            }
            Operator::Or | Operator::And | Operator::Xor => {
                // These operators can be called with only one argument
                ErrorKind::assert_num_of_args_range(&args, 1..)?;
                for s in sorts {
                    SortError::assert_eq(Term::BOOL_SORT, s)?;
                }
            }
            Operator::Equals | Operator::Distinct => {
                ErrorKind::assert_num_of_args_range(&args, 2..)?;
                SortError::assert_all_eq(&sorts)?;
            }
            Operator::Ite => {
                ErrorKind::assert_num_of_args(&args, 3)?;
                SortError::assert_eq(Term::BOOL_SORT, sorts[0])?;
                SortError::assert_eq(sorts[1], sorts[2])?;
            }
            Operator::Add | Operator::Mult | Operator::Div => {
                ErrorKind::assert_num_of_args_range(&args, 2..)?;

                // All the arguments must have the same sort, and it must be either Int or Real
                SortError::assert_one_of(&[Term::INT_SORT, Term::REAL_SORT], sorts[0])?;
                SortError::assert_all_eq(&sorts)?;
            }
            Operator::Sub => {
                // The "-" operator, in particular, can be called with only one argument, in which
                // case it means negation instead of subtraction
                ErrorKind::assert_num_of_args_range(&args, 1..)?;
                SortError::assert_one_of(&[Term::INT_SORT, Term::REAL_SORT], sorts[0])?;
                SortError::assert_all_eq(&sorts)?;
            }
            Operator::LessThan | Operator::GreaterThan | Operator::LessEq | Operator::GreaterEq => {
                ErrorKind::assert_num_of_args_range(&args, 2..)?;
                // All the arguments must be either Int or Real sorted, but they don't need to all
                // have the same sort
                SortError::assert_one_of(&[Term::INT_SORT, Term::REAL_SORT], sorts[0])?;
            }
        }
        let args = self.add_all(args);
        Ok(Term::Op(op, args))
    }

    /// Constructs and sort checks an application term.
    fn make_app(&mut self, function: Term, args: Vec<Term>) -> Result<Term, ErrorKind> {
        let sorts = {
            let function_sort = function.sort();
            if let Term::Sort(SortKind::Function, sorts) = function_sort {
                sorts
            } else {
                // Function does not have function sort
                return Err(ErrorKind::SortError(SortError::Expected {
                    expected: Term::Sort(SortKind::Function, Vec::new()),
                    got: function_sort.clone(),
                }));
            }
        };
        ErrorKind::assert_num_of_args(&args, sorts.len() - 1)?;
        for i in 0..args.len() {
            SortError::assert_eq(sorts[i].as_ref(), args[i].sort())?;
        }
        let function = self.add_term(function);
        let args = self.add_all(args);
        Ok(Term::App(function, args))
    }

    /// Consumes the current token if it equals `expected`. Returns an error otherwise.
    fn expect_token(&mut self, expected: Token) -> ParserResult<()> {
        let got = self.next_token()?;
        if got == expected {
            Ok(())
        } else {
            Err(self.unexpected_token(got))
        }
    }

    /// Consumes the current token if it is a symbol, and returns the inner `String`. Returns an
    /// error otherwise.
    fn expect_symbol(&mut self) -> ParserResult<String> {
        match self.next_token()? {
            Token::Symbol(s) => Ok(s),
            other => Err(self.unexpected_token(other)),
        }
    }

    /// Consumes the current token if it is a keyword, and returns the inner `String`. Returns an
    /// error otherwise.
    fn expect_keyword(&mut self) -> ParserResult<String> {
        match self.next_token()? {
            Token::Keyword(s) => Ok(s),
            other => Err(self.unexpected_token(other)),
        }
    }

    /// Consumes the current token if it is a numeral, and returns the inner `u64`. Returns an
    /// error otherwise.
    fn expect_numeral(&mut self) -> ParserResult<BigInt> {
        match self.next_token()? {
            Token::Numeral(n) => Ok(n),
            other => Err(self.unexpected_token(other)),
        }
    }

    /// Calls `parse_func` repeatedly until a closing parenthesis is reached. If `non_empty` is
    /// true, empty sequences will result in an error. This method consumes the ending ")" token.
    fn parse_sequence<T, F>(&mut self, mut parse_func: F, non_empty: bool) -> ParserResult<Vec<T>>
    where
        F: FnMut(&mut Self) -> ParserResult<T>,
    {
        let mut result = Vec::new();
        while self.current_token != Token::CloseParen {
            result.push(parse_func(self)?);
        }
        if non_empty && result.is_empty() {
            Err(self.err(ErrorKind::EmptySequence))
        } else {
            self.next_token()?; // Consume ")" token
            Ok(result)
        }
    }

    /// Reads an SMT-LIB script and parses the declarations and definitions. Ignores all other
    /// SMT-LIB script commands.
    pub fn parse_problem(&mut self) -> ParserResult<()> {
        while self.current_token != Token::Eof {
            self.expect_token(Token::OpenParen)?;
            match self.next_token()? {
                Token::ReservedWord(Reserved::DeclareFun) => {
                    let (name, sort) = self.parse_declare_fun()?;
                    self.insert_sorted_var((name, sort));
                    continue;
                }
                Token::ReservedWord(Reserved::DeclareSort) => {
                    let (name, arity) = self.parse_declare_sort()?;
                    // User declared sorts are represented with the `Atom` sort kind, and an
                    // argument which is a string terminal representing the sort name.
                    let sort = {
                        let arg = self.add_term(terminal!(string name.clone()));
                        self.add_term(Term::Sort(SortKind::Atom, vec![arg]))
                    };
                    self.state.sort_declarations.insert(name, (arity, sort));
                    continue;
                }
                Token::ReservedWord(Reserved::DefineFun) => {
                    let (name, func_def) = self.parse_define_fun()?;
                    self.state.function_defs.insert(name, func_def);
                    continue;
                }
                _ => {
                    // If the command is not a declaration or definition, we just ignore it. We do
                    // that by reading tokens until the command parenthesis is closed
                    let mut parens_depth = 1;
                    while parens_depth > 0 {
                        parens_depth += match self.next_token()? {
                            Token::OpenParen => 1,
                            Token::CloseParen => -1,
                            Token::Eof => return Err(self.unexpected_token(Token::Eof)),
                            _ => 0,
                        };
                    }
                }
            }
        }
        Ok(())
    }

    /// Parses a proof.
    pub fn parse_proof(mut self) -> ParserResult<(Proof, TermPool)> {
        // To avoid stack overflows in proofs with many nested subproofs, we parse the subproofs
        // iteratively, instead of recursively
        let mut commands_stack = vec![Vec::new()];
        let mut end_step_stack = Vec::new();
        let mut subproof_args_stack = Vec::new();

        while self.current_token != Token::Eof {
            self.expect_token(Token::OpenParen)?;
            let (index, command) = match self.next_token()? {
                Token::ReservedWord(Reserved::Assume) => self.parse_assume_command()?,
                Token::ReservedWord(Reserved::Step) => {
                    let (index, (clause, rule, premises, args)) = self.parse_step_command()?;

                    // If this is the last step in the subproof, we pop the top scope off of the
                    // step indices symbol table before converting the premises into indices. We
                    // must do this here because if the last step of a subproof has premises, they
                    // refer to the outer scope, and not inside the subproof
                    if end_step_stack.last() == Some(&index) {
                        self.state.step_indices.pop_scope();
                    }

                    // For every premise index symbol, find the associated `usize` in the
                    // `step_indices` hash map, or return an error
                    let premises: Vec<_> = premises
                        .into_iter()
                        .map(|index| {
                            self.state
                                .step_indices
                                .get(&index)
                                .copied()
                                .ok_or_else(|| self.err(ErrorKind::UndefinedStepIndex(index)))
                        })
                        .collect::<Result<_, _>>()?;

                    let step = ProofStep {
                        index: index.clone(),
                        clause,
                        rule,
                        premises,
                        args,
                    };
                    (index, ProofCommand::Step(step))
                }
                Token::ReservedWord(Reserved::DefineFun) => {
                    let (name, func_def) = self.parse_define_fun()?;
                    self.state.function_defs.insert(name, func_def);
                    continue;
                }
                Token::ReservedWord(Reserved::Anchor) => {
                    let (end_step_index, assignment_args, variable_args) =
                        self.parse_anchor_command()?;

                    // When we encounter an "anchor" command, we push a new scope into the step
                    // indices symbol table, a fresh commands vector into the commands stack for
                    // the subproof to fill, and the "anchor" data (end step and arguments) into
                    // their respective stacks. All of this will be popped off at the end of the
                    // subproof. We don't need to push a new scope into the sorts symbol table
                    // because `Parser::parse_anchor_command` already does that for us
                    self.state.step_indices.push_scope();
                    commands_stack.push(Vec::new());
                    end_step_stack.push(end_step_index);
                    subproof_args_stack.push((assignment_args, variable_args));
                    continue;
                }
                other => return Err(self.unexpected_token(other)),
            };
            if self.state.step_indices.get(&index).is_some() {
                return Err(self.err(ErrorKind::RepeatedStepIndex(index)));
            }

            commands_stack.last_mut().unwrap().push(command);
            if end_step_stack.last() == Some(&index) {
                // If this is the last step in a subproof, we need to pop all the subproof data off
                // of the stacks and build the subproof command with it. We don't need to pop off
                // the scope added to the step indices symbol table because that is done when the
                // last step is being parsed. We just need to make sure that the last command is in
                // fact a "step"
                let commands = commands_stack.pop().unwrap();
                match commands.last() {
                    Some(ProofCommand::Step(_)) => (),
                    _ => return Err(self.err(ErrorKind::LastSubproofStepIsNotStep)),
                };
                end_step_stack.pop().unwrap();
                let (assignment_args, variable_args) = subproof_args_stack.pop().unwrap();
                self.state.sorts_symbol_table.pop_scope();
                commands_stack
                    .last_mut()
                    .unwrap()
                    .push(ProofCommand::Subproof {
                        commands,
                        assignment_args,
                        variable_args,
                    })
            }
            self.state
                .step_indices
                .insert(index, commands_stack.last().unwrap().len() - 1);
        }
        match commands_stack.len() {
            0 => unreachable!(),
            1 => Ok((Proof(commands_stack.pop().unwrap()), self.state.term_pool)),

            // If there is more than one vector in the commands stack, we are inside a subproof
            // that should be closed before the outer proof is finished
            _ => Err(self.err(ErrorKind::UnexpectedToken(Token::Eof))),
        }
    }

    /// Parses an "assume" proof command. This method assumes that the "(" and "assume" tokens were
    /// already consumed.
    fn parse_assume_command(&mut self) -> ParserResult<(String, ProofCommand)> {
        let index = self.expect_symbol()?;
        let term = self.parse_term()?;
        SortError::assert_eq(Term::BOOL_SORT, term.sort()).map_err(|err| self.err(err.into()))?;
        let term = self.add_term(term);
        self.expect_token(Token::CloseParen)?;
        Ok((index, ProofCommand::Assume(term)))
    }

    /// Parses a "step" proof command. This method assumes that the "(" and "step" tokens were
    /// already consumed.
    fn parse_step_command(&mut self) -> ParserResult<(String, StepCommand)> {
        let step_index = self.expect_symbol()?;
        let clause = self.parse_clause()?;
        self.expect_token(Token::Keyword("rule".into()))?;
        let rule = match self.next_token()? {
            Token::Symbol(s) => s,
            Token::ReservedWord(r) => format!("{:?}", r),
            other => return Err(self.unexpected_token(other)),
        };

        let premises = if self.current_token == Token::Keyword("premises".into()) {
            self.next_token()?;
            self.expect_token(Token::OpenParen)?;
            self.parse_sequence(Self::expect_symbol, true)?
        } else {
            Vec::new()
        };

        let args = if self.current_token == Token::Keyword("args".into()) {
            self.next_token()?;
            self.expect_token(Token::OpenParen)?;
            self.parse_sequence(Self::parse_proof_arg, true)?
        } else {
            Vec::new()
        };

        // In some steps (notably those with the "subproof" rule) a ":discharge" attribute appears,
        // with an assumption index as its value. While the checker already has support this rule,
        // it still can't parse and interpret the ":discharge" attributes values properly, so we
        // are simply consuming and ignoring the attribute if it appears
        if self.current_token == Token::Keyword("discharge".into()) {
            self.next_token()?;
            self.expect_token(Token::OpenParen)?;
            self.expect_symbol()?;
            self.expect_token(Token::CloseParen)?;
        }

        self.expect_token(Token::CloseParen)?;

        Ok((step_index, (clause, rule, premises, args)))
    }

    /// Parses an "anchor" proof command. This method assumes that the "(" and "anchor" tokens were
    /// already consumed. In order to parse the subproof arguments, this method pushes a new scope
    /// into the sorts symbol table which must be removed after parsing the subproof. This method
    /// returns the index of the step that will end the subproof, as well as the subproof
    /// assignment and variable arguments.
    fn parse_anchor_command(&mut self) -> ParserResult<AnchorCommand> {
        self.expect_token(Token::Keyword("step".into()))?;
        let end_step_index = self.expect_symbol()?;

        // We have to push a new scope into the sorts symbol table in order to parse the subproof
        // arguments
        self.state.sorts_symbol_table.push_scope();

        let mut assignment_args = Vec::new();
        let mut variable_args = Vec::new();
        if self.current_token == Token::Keyword("args".into()) {
            self.next_token()?;
            self.expect_token(Token::OpenParen)?;
            let args = self.parse_sequence(Parser::parse_anchor_argument, true)?;
            for a in args {
                match a {
                    Either::Left(((a, _), b)) => {
                        assignment_args.push((a.clone(), b));
                    }
                    Either::Right(var) => variable_args.push(var.clone()),
                }
            }
        }
        self.expect_token(Token::CloseParen)?;
        Ok((end_step_index, assignment_args, variable_args))
    }

    fn parse_anchor_argument(
        &mut self,
    ) -> ParserResult<Either<(SortedVar, ByRefRc<Term>), SortedVar>> {
        self.expect_token(Token::OpenParen)?;
        Ok(if self.current_token == Token::Keyword("=".into()) {
            self.next_token()?;
            let (a, sort) = self.parse_sorted_var()?;
            self.insert_sorted_var((a.clone(), sort.clone()));

            let b = match &self.current_token {
                // If we encounter a symbol as the value of the assignment, we must check if there
                // are any function definitions with that symbol. If there are, we consider the
                // value a term insetad of a new variable
                Token::Symbol(s) if !self.state.function_defs.contains_key(s) => {
                    let var = self.expect_symbol()?;
                    self.insert_sorted_var((var.clone(), sort.clone()));
                    let iden = Identifier::Simple(var);
                    Term::Terminal(Terminal::Var(iden, sort.clone()))
                }
                _ => {
                    let term = self.parse_term()?;
                    SortError::assert_eq(term.sort(), sort.as_ref())
                        .map_err(|err| self.err(err.into()))?;
                    term
                }
            };
            let b = self.add_term(b);

            self.expect_token(Token::CloseParen)?;
            Either::Left(((a, sort), b))
        } else {
            let symbol = self.expect_symbol()?;
            let sort = self.parse_sort()?;
            let var = (symbol, self.add_term(sort));
            self.insert_sorted_var(var.clone());
            self.expect_token(Token::CloseParen)?;
            Either::Right(var)
        })
    }

    /// Parses a "declare-fun" proof command. Returns the function name and a term representing its
    /// sort. This method assumes that the "(" and "declare-fun" tokens were already consumed.
    fn parse_declare_fun(&mut self) -> ParserResult<(String, ByRefRc<Term>)> {
        let name = self.expect_symbol()?;
        let sort = {
            self.expect_token(Token::OpenParen)?;
            let mut sorts = self.parse_sequence(Self::parse_sort, false)?;
            sorts.push(self.parse_sort()?);
            let sorts = self.add_all(sorts);
            if sorts.len() == 1 {
                sorts.into_iter().next().unwrap()
            } else {
                self.add_term(Term::Sort(SortKind::Function, sorts))
            }
        };
        self.expect_token(Token::CloseParen)?;
        Ok((name, sort))
    }

    /// Parses a declare-sort proof command. Returns the sort name and its arity. This method
    /// assumes that the "(" and "declare-sort" tokens were already consumed.
    fn parse_declare_sort(&mut self) -> ParserResult<(String, u64)> {
        let name = self.expect_symbol()?;
        let arity = self.expect_numeral()?;
        self.expect_token(Token::CloseParen)?;
        let arity = arity
            .to_u64()
            .ok_or_else(|| self.err(ErrorKind::InvalidSortArity(arity)))?;
        Ok((name, arity))
    }

    /// Parses a "define-fun" proof command. Returns the function name and its definition. This
    /// method assumes that the "(" and "define-fun" tokens were already consumed.
    fn parse_define_fun(&mut self) -> ParserResult<(String, FunctionDef)> {
        let name = self.expect_symbol()?;
        self.expect_token(Token::OpenParen)?;
        let params = self.parse_sequence(Self::parse_sorted_var, false)?;
        let return_sort = self.parse_sort()?;

        // In order to correctly parse the function body, we push a new scope to the symbol table
        // and add the functions arguments to it.
        self.state.sorts_symbol_table.push_scope();
        for var in &params {
            self.insert_sorted_var(var.clone());
        }
        let body = self.parse_term()?;
        self.state.sorts_symbol_table.pop_scope();

        self.expect_token(Token::CloseParen)?;

        SortError::assert_eq(&return_sort, body.sort()).map_err(|err| self.err(err.into()))?;
        let body = self.add_term(body);
        Ok((name, FunctionDef { params, body }))
    }

    /// Parses a clause of the form "(cl <term>*)".
    fn parse_clause(&mut self) -> ParserResult<Vec<ByRefRc<Term>>> {
        self.expect_token(Token::OpenParen)?;
        self.expect_token(Token::ReservedWord(Reserved::Cl))?;
        let terms = self
            .parse_sequence(Self::parse_term, false)?
            .into_iter()
            .map(|term| -> ParserResult<ByRefRc<Term>> {
                SortError::assert_eq(Term::BOOL_SORT, term.sort())
                    .map_err(|err| self.err(err.into()))?;
                Ok(self.add_term(term))
            })
            .collect::<Result<_, _>>()?;
        Ok(terms)
    }

    /// Parses an argument for a "step" command.
    fn parse_proof_arg(&mut self) -> ParserResult<ProofArg> {
        if self.current_token == Token::OpenParen {
            self.next_token()?; // Consume "(" token

            // If we encounter a "(" token, this could be an assignment argument of the form
            // "(:= <symbol> <term>)", or a regular term that starts with "(". Note that the
            // lexer reads ":=" as a keyword with contents "=".
            if self.current_token == Token::Keyword("=".into()) {
                self.next_token()?; // Consume ":=" token
                let name = self.expect_symbol()?;
                let value = self.parse_term()?;
                self.expect_token(Token::CloseParen)?;
                Ok(ProofArg::Assign(name, self.add_term(value)))
            } else {
                // If the first token is not ":=", this argument is just a regular term. Since
                // we already consumed the "(" token, we have to call `parse_application`
                // instead of `parse_term`.
                let term = self.parse_application()?;
                Ok(ProofArg::Term(self.add_term(term)))
            }
        } else {
            let term = self.parse_term()?;
            Ok(ProofArg::Term(self.add_term(term)))
        }
    }

    /// Parses a sorted variable of the form "(<symbol> <sort>)".
    fn parse_sorted_var(&mut self) -> ParserResult<SortedVar> {
        self.expect_token(Token::OpenParen)?;
        let symbol = self.expect_symbol()?;
        let sort = self.parse_sort()?;
        self.expect_token(Token::CloseParen)?;
        Ok((symbol, self.add_term(sort)))
    }

    /// Parses a term.
    pub fn parse_term(&mut self) -> ParserResult<Term> {
        match self.next_token()? {
            Token::Numeral(n) => Ok(terminal!(int n)),
            Token::Decimal(r) => Ok(terminal!(real r)),
            Token::String(s) => Ok(terminal!(string s)),
            Token::Symbol(s) => {
                // Check to see if there is a nullary function defined with this name
                if let Some(func_def) = self.state.function_defs.get(&s) {
                    if func_def.params.is_empty() {
                        // This has to clone the function body term, even though it is already
                        // added to the term pool
                        Ok(func_def.body.as_ref().clone())
                    } else {
                        Err(self.err(ErrorKind::WrongNumberOfArgs(func_def.params.len(), 0)))
                    }
                } else {
                    self.make_var(Identifier::Simple(s))
                        .map_err(|err| self.err(err))
                }
            }
            Token::OpenParen => self.parse_application(),
            other => Err(self.unexpected_token(other)),
        }
    }

    fn parse_quantifier(&mut self, quantifier: Quantifier) -> ParserResult<Term> {
        self.expect_token(Token::OpenParen)?;
        self.state.sorts_symbol_table.push_scope();
        let bindings = self.parse_sequence(
            |p| {
                let var = p.parse_sorted_var()?;
                p.insert_sorted_var(var.clone());
                Ok(var)
            },
            true,
        )?;
        let term = self.parse_term()?;
        SortError::assert_eq(Term::BOOL_SORT, term.sort()).map_err(|e| self.err(e.into()))?;
        let term = self.add_term(term);
        self.state.sorts_symbol_table.pop_scope();
        self.expect_token(Token::CloseParen)?;
        Ok(Term::Quant(quantifier, bindings, term))
    }

    fn parse_choice_term(&mut self) -> ParserResult<Term> {
        self.expect_token(Token::OpenParen)?;
        let var = self.parse_sorted_var()?;
        self.insert_sorted_var(var.clone());
        self.expect_token(Token::CloseParen)?;
        let inner = self.parse_term()?;
        self.expect_token(Token::CloseParen)?;
        Ok(Term::Choice(var, self.add_term(inner)))
    }

    fn parse_let_term(&mut self) -> ParserResult<Term> {
        self.expect_token(Token::OpenParen)?;
        self.state.sorts_symbol_table.push_scope();
        let bindings = self.parse_sequence(
            |p| {
                p.expect_token(Token::OpenParen)?;
                let name = p.expect_symbol()?;
                let value = p.parse_term()?;
                let value = p.add_term(value);
                let sort = p.add_term(value.sort().clone());
                p.insert_sorted_var((name.clone(), sort));
                p.expect_token(Token::CloseParen)?;
                Ok((name, value))
            },
            true,
        )?;
        let inner = self.parse_term()?;
        self.expect_token(Token::CloseParen)?;
        let inner = self.add_term(inner);
        self.state.sorts_symbol_table.pop_scope();
        Ok(Term::Let(bindings, inner))
    }

    fn parse_annotated_term(&mut self) -> ParserResult<Term> {
        let inner = self.parse_term()?;
        let inner = self.add_term(inner);
        self.parse_sequence(
            |p| {
                let attribute = p.expect_keyword()?;
                if attribute.as_str() == "named" {
                    // If the term has a "named" attribute, we introduce a new nullary function
                    // definition that maps the name to the term
                    let name = p.expect_symbol()?;
                    p.state.function_defs.insert(
                        name,
                        FunctionDef {
                            params: Vec::new(),
                            body: inner.clone(),
                        },
                    );
                } else if let Token::Symbol(_) = p.current_token {
                    p.next_token()?;
                }
                Ok(())
            },
            true,
        )?;
        Ok(inner.as_ref().clone())
    }

    fn parse_application(&mut self) -> ParserResult<Term> {
        match &self.current_token {
            &Token::ReservedWord(reserved) => {
                self.next_token()?;
                match reserved {
                    Reserved::Exists => self.parse_quantifier(Quantifier::Exists),
                    Reserved::Forall => self.parse_quantifier(Quantifier::Forall),
                    Reserved::Choice => self.parse_choice_term(),
                    Reserved::Bang => self.parse_annotated_term(),
                    Reserved::Let => self.parse_let_term(),
                    _ => Err(self.err(ErrorKind::NotYetImplemented)),
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
                self.make_op(operator, args).map_err(|err| self.err(err))
            }
            Token::Symbol(s) if self.state.function_defs.get(s).is_some() => {
                let func_name = self.expect_symbol()?;
                let args = self.parse_sequence(Self::parse_term, true)?;
                let func = self.state.function_defs.get(&func_name).unwrap();

                // If there is a function definition with this function name, we sort check
                // the arguments and apply the definition by performing a beta reduction.
                ErrorKind::assert_num_of_args(&args, func.params.len())
                    .map_err(|err| self.err(err))?;
                for (arg, param) in args.iter().zip(func.params.iter()) {
                    SortError::assert_eq(param.1.as_ref(), arg.sort())
                        .map_err(|err| self.err(err.into()))?;
                }

                // Build a hash map of all the parameter names and the values they will
                // take
                let mut substitutions = {
                    // We have to take a reference to the term pool here, so the closure in
                    // the `map` call later on doesn't have to capture all of `self`, and
                    // can just capture the term pool. We need this to please the borrow
                    // checker
                    let pool = &mut self.state.term_pool;
                    func.params
                        .iter()
                        .zip(args)
                        .map(|((name, sort), arg)| {
                            let k = pool.add_term(terminal!(var name; sort.clone()));
                            let v = pool.add_term(arg);
                            (k, v)
                        })
                        .collect()
                };

                // Since `apply_substitutions` returns a `ByRefRc<Term>`, we have to go
                // into the inner term and clone it, even though it is already added to the
                // term pool
                Ok(self
                    .state
                    .term_pool
                    .apply_substitutions(&func.body, &mut substitutions)
                    .as_ref()
                    .clone())
            }
            _ => {
                let func = self.parse_term()?;
                let args = self.parse_sequence(Self::parse_term, true)?;
                self.make_app(func, args).map_err(|err| self.err(err))
            }
        }
    }

    /// Parses a sort.
    fn parse_sort(&mut self) -> ParserResult<Term> {
        match self.next_token()? {
            Token::Symbol(s) => match s.as_ref() {
                "Bool" => Ok(Term::BOOL_SORT.clone()),
                "Int" => Ok(Term::INT_SORT.clone()),
                "Real" => Ok(Term::REAL_SORT.clone()),
                "String" => Ok(Term::STRING_SORT.clone()),
                other => {
                    if let Some((_, sort)) = self.state.sort_declarations.get(other) {
                        Ok((**sort).clone())
                    } else {
                        Err(self.err(ErrorKind::UndefinedSort(other.into())))
                    }
                }
            },
            other => Err(self.unexpected_token(other)),
        }
    }
}
