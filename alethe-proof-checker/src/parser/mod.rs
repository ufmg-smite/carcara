//! A parser for the Alethe proof format.

mod error;
mod lexer;
pub(crate) mod tests;

pub use error::{ParserError, SortError};
pub use lexer::{Lexer, Position, Reserved, Token};

use crate::{
    ast::*,
    utils::{Either, SymbolTable},
    AletheResult, Error,
};
use ahash::{AHashMap, AHashSet};
use error::assert_num_args;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::ToPrimitive;
use std::{io::BufRead, str::FromStr};

/// Parses an SMT problem instance (in the SMT-LIB format) and its associated proof (in the Alethe
/// format). Returns the parsed proof, as well as the `TermPool` used in parsing. Can take any type
/// that implements `BufRead`.
pub fn parse_instance<T: BufRead>(
    problem: T,
    proof: T,
    apply_function_defs: bool,
) -> AletheResult<(Proof, TermPool)> {
    let mut parser = Parser::new(problem, apply_function_defs)?;
    let premises = parser.parse_problem()?;
    parser.reset(proof)?;
    let commands = parser.parse_proof()?;

    let proof = Proof { premises, commands };
    Ok((proof, parser.term_pool()))
}

/// Represents a "raw" `anchor` command. This is only used while parsing, and does not appear in
/// the final AST.
struct AnchorCommand {
    end_step_id: String,
    assignment_args: Vec<(String, Rc<Term>)>,
    variable_args: Vec<SortedVar>,
}

/// The state of the parser. This holds all the function, constant or sort declarations and
/// definitions, as well as the term pool used by the parser.
#[derive(Default)]
struct ParserState {
    symbol_table: SymbolTable<Identifier, Rc<Term>>,
    function_defs: AHashMap<String, FunctionDef>,
    term_pool: TermPool,
    sort_declarations: AHashMap<String, usize>,
    step_ids: SymbolTable<String, usize>,
}

/// A parser for the Alethe proof format.
pub struct Parser<R> {
    lexer: Lexer<R>,
    current_token: Token,
    current_position: Position,
    state: ParserState,
    interpret_integers_as_reals: bool,
    apply_function_defs: bool,
    premises: Option<AHashSet<Rc<Term>>>,
}

impl<R: BufRead> Parser<R> {
    /// Constructs a new `Parser` from a type that implements `BufRead`. This operation can fail if
    /// there is an IO or lexer error on the first token.
    pub fn new(input: R, apply_function_defs: bool) -> AletheResult<Self> {
        let mut state = ParserState::default();
        let bool_sort = state.term_pool.add_term(Term::Sort(Sort::Bool));
        for iden in ["true", "false"] {
            let iden = Identifier::Simple(iden.to_owned());
            state.symbol_table.insert(iden, bool_sort.clone());
        }
        let mut lexer = Lexer::new(input)?;
        let (current_token, current_position) = lexer.next_token()?;
        Ok(Parser {
            lexer,
            current_token,
            current_position,
            state,
            interpret_integers_as_reals: false,
            apply_function_defs,
            premises: None,
        })
    }

    /// Resets the parser position and sets its input to `input`. This keeps the parser state,
    /// including all function, constant and sort declarations.
    pub fn reset(&mut self, input: R) -> AletheResult<()> {
        let mut lexer = Lexer::new(input)?;
        let (current_token, current_position) = lexer.next_token()?;
        self.lexer = lexer;
        self.current_token = current_token;
        self.current_position = current_position;
        Ok(())
    }

    /// Takes the term pool used in parsing. This permanently moves the parser, so it cannot be
    /// used after calling this method.
    pub fn term_pool(self) -> TermPool {
        self.state.term_pool
    }

    /// Returns `true` if the parser is currently parsing a SMT-LIB problem, and `false` otherwise.
    fn is_parsing_problem(&self) -> bool {
        self.premises.is_some()
    }

    /// Advances the parser one token, and returns the previous `current_token`.
    fn next_token(&mut self) -> AletheResult<(Token, Position)> {
        use std::mem::replace;

        let (new_token, new_position) = self.lexer.next_token()?;
        let old_token = replace(&mut self.current_token, new_token);
        let old_position = replace(&mut self.current_position, new_position);
        Ok((old_token, old_position))
    }

    /// Shortcut for `self.state.term_pool.add_term`.
    fn add_term(&mut self, term: Term) -> Rc<Term> {
        self.state.term_pool.add_term(term)
    }

    /// Shortcut for `self.state.term_pool.add_all`.
    fn add_all(&mut self, terms: Vec<Term>) -> Vec<Rc<Term>> {
        self.state.term_pool.add_all(terms)
    }

    /// Shortcut for `self.state.term_pool.sort`.
    fn sort(&self, term: &Rc<Term>) -> &Sort {
        self.state.term_pool.sort(term)
    }

    /// Helper method to insert a `SortedVar` into the parser symbol table.
    fn insert_sorted_var(&mut self, (symbol, sort): SortedVar) {
        self.state
            .symbol_table
            .insert(Identifier::Simple(symbol), sort);
    }

    /// Adds a new function definition. If we are parsing the problem and
    /// `self.apply_function_defs` is `false`, this instead adds the function name to the symbol
    /// table and adds a new premise that defines the function.
    fn add_function_def(&mut self, name: String, func_def: FunctionDef) {
        if self.is_parsing_problem() && !self.apply_function_defs {
            let lambda_term = if func_def.params.is_empty() {
                func_def.body
            } else {
                self.add_term(Term::Lambda(BindingList(func_def.params), func_def.body))
            };
            let sort = self.add_term(Term::Sort(self.sort(&lambda_term).clone()));
            let var = (name, sort);
            self.insert_sorted_var(var.clone());
            let var_term = self.add_term(var.into());
            let assertion_term =
                self.add_term(Term::Op(Operator::Equals, vec![var_term, lambda_term]));
            self.premises.as_mut().unwrap().insert(assertion_term);
        } else {
            self.state.function_defs.insert(name, func_def);
        }
    }

    /// Constructs and sort checks a variable term.
    fn make_var(&mut self, iden: Identifier) -> Result<Rc<Term>, ParserError> {
        let sort = self
            .state
            .symbol_table
            .get(&iden)
            .ok_or_else(|| ParserError::UndefinedIden(iden.clone()))?
            .clone();
        Ok(self.add_term(Term::Terminal(Terminal::Var(iden, sort))))
    }

    /// Constructs and sort checks an operation term.
    fn make_op(&mut self, op: Operator, args: Vec<Rc<Term>>) -> Result<Rc<Term>, ParserError> {
        let sorts: Vec<_> = args.iter().map(|t| self.sort(t)).collect();
        match op {
            Operator::Not => {
                assert_num_args(&args, 1)?;
                SortError::assert_eq(&Sort::Bool, sorts[0])?;
            }
            Operator::Implies => {
                assert_num_args(&args, 2..)?;
                for s in sorts {
                    SortError::assert_eq(&Sort::Bool, s)?;
                }
            }
            Operator::Or | Operator::And | Operator::Xor => {
                // These operators can be called with only one argument
                assert_num_args(&args, 1..)?;
                for s in sorts {
                    SortError::assert_eq(&Sort::Bool, s)?;
                }
            }
            Operator::Equals | Operator::Distinct => {
                assert_num_args(&args, 2..)?;
                SortError::assert_all_eq(&sorts)?;
            }
            Operator::Ite => {
                assert_num_args(&args, 3)?;
                SortError::assert_eq(&Sort::Bool, sorts[0])?;
                SortError::assert_eq(sorts[1], sorts[2])?;
            }
            Operator::Add | Operator::Mult | Operator::IntDiv | Operator::RealDiv => {
                assert_num_args(&args, 2..)?;

                // All the arguments must have the same sort, and it must be either Int or Real
                SortError::assert_one_of(&[Sort::Int, Sort::Real], sorts[0])?;
                SortError::assert_all_eq(&sorts)?;
            }
            Operator::Sub => {
                // The `-` operator, in particular, can be called with only one argument, in which
                // case it means negation instead of subtraction
                assert_num_args(&args, 1..)?;
                SortError::assert_one_of(&[Sort::Int, Sort::Real], sorts[0])?;
                SortError::assert_all_eq(&sorts)?;
            }
            Operator::LessThan | Operator::GreaterThan | Operator::LessEq | Operator::GreaterEq => {
                assert_num_args(&args, 2..)?;
                // All the arguments must be either Int or Real sorted, but they don't need to all
                // have the same sort
                for s in sorts {
                    SortError::assert_one_of(&[Sort::Int, Sort::Real], s)?;
                }
            }
            Operator::Select => {
                assert_num_args(&args, 2)?;
                match sorts[0] {
                    Sort::Array(_, _) => (),
                    got => {
                        // Instead of creating some special case for sort errors with parametric
                        // sorts, we just create a sort `Y` to represent the sort parameter. We
                        // infer the `X` sort from the second operator argument. This may be
                        // changed later
                        let got = got.clone();
                        let x = sorts[1].clone();
                        let x = self.add_term(Term::Sort(x));
                        let y = self.add_term(Term::Sort(Sort::Atom("Y".to_owned(), Vec::new())));
                        return Err(SortError {
                            expected: vec![Sort::Array(x, y)],
                            got,
                        }
                        .into());
                    }
                }
            }
            Operator::Store => {
                assert_num_args(&args, 3)?;
                match sorts[0] {
                    Sort::Array(x, y) => {
                        SortError::assert_eq(x.as_sort().unwrap(), sorts[1])?;
                        SortError::assert_eq(y.as_sort().unwrap(), sorts[2])?;
                    }
                    got => {
                        let got = got.clone();
                        let [x, y] = [sorts[0], sorts[1]].map(|s| Term::Sort(s.clone()));
                        return Err(SortError {
                            expected: vec![Sort::Array(self.add_term(x), self.add_term(y))],
                            got,
                        }
                        .into());
                    }
                }
            }
        }
        Ok(self.add_term(Term::Op(op, args)))
    }

    /// Constructs and sort checks an application term.
    fn make_app(
        &mut self,
        function: Rc<Term>,
        args: Vec<Rc<Term>>,
    ) -> Result<Rc<Term>, ParserError> {
        let sorts = {
            let function_sort = self.sort(&function);
            if let Sort::Function(sorts) = function_sort {
                sorts
            } else {
                // Function does not have function sort
                return Err(ParserError::NotAFunction(function_sort.clone()));
            }
        };
        assert_num_args(&args, sorts.len() - 1)?;
        for i in 0..args.len() {
            SortError::assert_eq(sorts[i].as_sort().unwrap(), self.sort(&args[i]))?;
        }
        Ok(self.add_term(Term::App(function, args)))
    }

    /// Consumes the current token if it equals `expected`. Returns an error otherwise.
    fn expect_token(&mut self, expected: Token) -> AletheResult<()> {
        let (got, pos) = self.next_token()?;
        if got == expected {
            Ok(())
        } else {
            Err(Error::Parser(ParserError::UnexpectedToken(got), pos))
        }
    }

    /// Consumes the current token if it is a symbol, and returns the inner `String`. Returns an
    /// error otherwise.
    fn expect_symbol(&mut self) -> AletheResult<String> {
        match self.next_token()? {
            (Token::Symbol(s), _) => Ok(s),
            (other, pos) => Err(Error::Parser(ParserError::UnexpectedToken(other), pos)),
        }
    }

    /// Consumes the current token if it is a keyword, and returns the inner `String`. Returns an
    /// error otherwise.
    fn expect_keyword(&mut self) -> AletheResult<String> {
        match self.next_token()? {
            (Token::Keyword(s), _) => Ok(s),
            (other, pos) => Err(Error::Parser(ParserError::UnexpectedToken(other), pos)),
        }
    }

    /// Consumes the current token if it is a numeral, and returns the inner `BigInt`. Returns an
    /// error otherwise.
    fn expect_numeral(&mut self) -> AletheResult<BigInt> {
        match self.next_token()? {
            (Token::Numeral(n), _) => Ok(n),
            (other, pos) => Err(Error::Parser(ParserError::UnexpectedToken(other), pos)),
        }
    }

    /// Calls `parse_func` repeatedly until a closing parenthesis is reached. If `non_empty` is
    /// true, empty sequences will result in an error. This method consumes the ending `)` token.
    fn parse_sequence<T, F>(&mut self, mut parse_func: F, non_empty: bool) -> AletheResult<Vec<T>>
    where
        F: FnMut(&mut Self) -> AletheResult<T>,
    {
        let mut result = Vec::new();
        while self.current_token != Token::CloseParen {
            result.push(parse_func(self)?);
        }
        if non_empty && result.is_empty() {
            Err(Error::Parser(
                ParserError::EmptySequence,
                self.current_position,
            ))
        } else {
            self.next_token()?; // Consume `)` token
            Ok(result)
        }
    }

    /// Consumes tokens until the matching closing parenthesis is reached.
    fn read_until_close_parens(&mut self) -> AletheResult<()> {
        let mut parens_depth = 1;
        while parens_depth > 0 {
            parens_depth += match self.next_token()? {
                (Token::OpenParen, _) => 1,
                (Token::CloseParen, _) => -1,
                (Token::Eof, pos) => {
                    return Err(Error::Parser(ParserError::UnexpectedToken(Token::Eof), pos))
                }
                _ => 0,
            };
        }
        Ok(())
    }

    /// Reads an SMT-LIB script and parses the assertions, declarations and definitions. The
    /// following commands are parsed:
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
    pub fn parse_problem(&mut self) -> AletheResult<AHashSet<Rc<Term>>> {
        self.premises = Some(AHashSet::new());

        while self.current_token != Token::Eof {
            self.expect_token(Token::OpenParen)?;
            match self.next_token()?.0 {
                Token::ReservedWord(Reserved::DeclareFun) => {
                    let (name, sort) = self.parse_declare_fun()?;
                    self.insert_sorted_var((name, sort));
                    continue;
                }
                Token::ReservedWord(Reserved::DeclareConst) => {
                    let name = self.expect_symbol()?;
                    let sort = self.parse_sort()?;
                    let sort = self.add_term(sort);
                    self.expect_token(Token::CloseParen)?;
                    self.insert_sorted_var((name, sort));
                    continue;
                }
                Token::ReservedWord(Reserved::DeclareSort) => {
                    let (name, arity) = self.parse_declare_sort()?;
                    // User declared sorts are represented with the `Atom` sort kind, and an
                    // argument which is a string terminal representing the sort name.
                    self.state.sort_declarations.insert(name, arity);
                    continue;
                }
                Token::ReservedWord(Reserved::DefineFun) => {
                    let (name, func_def) = self.parse_define_fun()?;
                    self.add_function_def(name, func_def);
                    continue;
                }
                Token::ReservedWord(Reserved::Assert) => {
                    let term = self.parse_term()?;
                    self.expect_token(Token::CloseParen)?;
                    self.premises.as_mut().unwrap().insert(term);
                }
                Token::ReservedWord(Reserved::SetLogic) => {
                    let logic = self.expect_symbol()?;
                    self.expect_token(Token::CloseParen)?;

                    // When the problem's logic contains real numbers but not integers, integer
                    // literals should be parsed as reals. For instance, `1` should be interpreted
                    // as `1.0`.
                    self.interpret_integers_as_reals = logic.contains('R') && !logic.contains('I');
                }
                _ => {
                    // If the command is not one of the commands we care about, we just ignore it.
                    // We do that by reading tokens until the command parenthesis is closed
                    self.read_until_close_parens()?;
                }
            }
        }
        Ok(self.premises.take().unwrap())
    }

    /// Parses a proof in the Alethe format. All function, constant and sort declarations needed
    /// should already be in the parser state.
    pub fn parse_proof(&mut self) -> AletheResult<Vec<ProofCommand>> {
        // To avoid stack overflows in proofs with many nested subproofs, we parse the subproofs
        // iteratively, instead of recursively
        let mut commands_stack = vec![Vec::new()];
        let mut end_step_stack = Vec::new();
        let mut subproof_args_stack = Vec::new();

        while self.current_token != Token::Eof {
            self.expect_token(Token::OpenParen)?;
            let (token, position) = self.next_token()?;
            let (id, command) = match token {
                Token::ReservedWord(Reserved::Assume) => {
                    let (id, term) = self.parse_assume_command()?;
                    (id.clone(), ProofCommand::Assume { id, term })
                }
                Token::ReservedWord(Reserved::Step) => {
                    let step = self.parse_step_command()?;
                    (step.id.clone(), ProofCommand::Step(step))
                }
                Token::ReservedWord(Reserved::DefineFun) => {
                    let (name, func_def) = self.parse_define_fun()?;
                    self.add_function_def(name, func_def);
                    continue;
                }
                Token::ReservedWord(Reserved::Anchor) => {
                    let anchor = self.parse_anchor_command()?;

                    // When we encounter an `anchor` command, we push a new scope into the step ids
                    // symbol table, a fresh commands vector into the commands stack for the
                    // subproof to fill, and the `anchor` data (end step and arguments) into their
                    // respective stacks. All of this will be popped off at the end of the subproof.
                    // We don't need to push a new scope into the symbol table because
                    // `Parser::parse_anchor_command` already does that for us
                    self.state.step_ids.push_scope();
                    commands_stack.push(Vec::new());
                    end_step_stack.push(anchor.end_step_id);
                    subproof_args_stack.push((anchor.assignment_args, anchor.variable_args));
                    continue;
                }
                _ => return Err(Error::Parser(ParserError::UnexpectedToken(token), position)),
            };
            if self.state.step_ids.get(&id).is_some() {
                return Err(Error::Parser(ParserError::RepeatedStepIndex(id), position));
            }

            commands_stack.last_mut().unwrap().push(command);
            if end_step_stack.last() == Some(&id) {
                // If this is the last step in a subproof, we need to pop all the subproof data off
                // of the stacks and build the subproof command with it
                self.state.symbol_table.pop_scope();
                self.state.step_ids.pop_scope();
                let commands = commands_stack.pop().unwrap();
                end_step_stack.pop().unwrap();
                let (assignment_args, variable_args) = subproof_args_stack.pop().unwrap();

                // We also need to make sure that the last command is in fact a `step`
                match commands.last() {
                    Some(ProofCommand::Step(_)) => (),
                    _ => {
                        return Err(Error::Parser(
                            ParserError::LastSubproofStepIsNotStep(id),
                            position,
                        ))
                    }
                };

                commands_stack
                    .last_mut()
                    .unwrap()
                    .push(ProofCommand::Subproof(Subproof {
                        commands,
                        assignment_args,
                        variable_args,
                    }));
            }
            self.state
                .step_ids
                .insert(id, commands_stack.last().unwrap().len() - 1);
        }
        match commands_stack.len() {
            0 => unreachable!(),
            1 => Ok(commands_stack.pop().unwrap()),

            // If there is more than one vector in the commands stack, we are inside a subproof
            // that should be closed before the outer proof is finished
            _ => Err(Error::Parser(
                ParserError::UnclosedSubproof(end_step_stack.pop().unwrap()),
                self.current_position,
            )),
        }
    }

    /// Parses an `assume` proof command. This method assumes that the `(` and `assume` tokens were
    /// already consumed.
    fn parse_assume_command(&mut self) -> AletheResult<(String, Rc<Term>)> {
        let id = self.expect_symbol()?;
        let term = self.parse_term_expecting_sort(&Sort::Bool)?;
        self.expect_token(Token::CloseParen)?;
        Ok((id, term))
    }

    /// Parses a `step` proof command. This method assumes that the `(` and `step` tokens were
    /// already consumed.
    fn parse_step_command(&mut self) -> AletheResult<ProofStep> {
        let id = self.expect_symbol()?;
        let clause = self.parse_clause()?;
        self.expect_token(Token::Keyword("rule".into()))?;
        let rule = match self.next_token()? {
            (Token::Symbol(s), _) => s,
            (Token::ReservedWord(r), _) => format!("{}", r),
            (other, pos) => return Err(Error::Parser(ParserError::UnexpectedToken(other), pos)),
        };

        // If the rule is `trust`, we read the rest of the `step` command, ignoring all arguments
        // and premises
        if rule == "trust" {
            self.read_until_close_parens()?;
            return Ok(ProofStep {
                id,
                clause,
                rule,
                premises: Vec::new(),
                args: Vec::new(),
                discharge: Vec::new(),
            });
        }

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
            self.parse_sequence(Self::parse_proof_arg, true)?
        } else {
            Vec::new()
        };

        // For some rules (notable the `subproof` rule), there is also a `:discharge` attribute that
        // takes a series of command ids, in addition to the regular premises
        let discharge = if self.current_token == Token::Keyword("discharge".into()) {
            self.next_token()?;
            self.expect_token(Token::OpenParen)?;
            self.parse_sequence(|p| p.parse_discharge_premise(&id), true)?
        } else {
            Vec::new()
        };

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
    fn parse_step_premise(&mut self) -> AletheResult<(usize, usize)> {
        let position = self.current_position;
        let id = self.expect_symbol()?;
        self.state
            .step_ids
            .get_with_depth(&id)
            .map(|(d, &i)| (d, i))
            .ok_or(Error::Parser(ParserError::UndefinedStepIndex(id), position))
    }

    /// Parses an argument for the `:discharge` attribute. Due to a bug in veriT, commands local to
    /// the current subproof are passed by their "relative" id. That is, the command `t5.t4.h2` is
    /// passed as simply `h2`. This behaviour is not present in other SMT solvers, like cvc5. To
    /// work around that, this function tries to find the command considering both possibilities.
    fn parse_discharge_premise(&mut self, root_id: &str) -> AletheResult<(usize, usize)> {
        let position = self.current_position;
        let id = self.expect_symbol()?;
        let absolute_id = format!("{}.{}", root_id, &id);
        self.state
            .step_ids
            .get_with_depth(&absolute_id)
            .or_else(|| self.state.step_ids.get_with_depth(&id))
            .map(|(d, &i)| (d, i))
            .ok_or(Error::Parser(ParserError::UndefinedStepIndex(id), position))
    }

    /// Parses an `anchor` proof command. This method assumes that the `(` and `anchor` tokens were
    /// already consumed. In order to parse the subproof arguments, this method pushes a new scope
    /// into the symbol table which must be removed after parsing the subproof.
    fn parse_anchor_command(&mut self) -> AletheResult<AnchorCommand> {
        self.expect_token(Token::Keyword("step".into()))?;
        let end_step_id = self.expect_symbol()?;

        // We have to push a new scope into the symbol table in order to parse the subproof
        // arguments
        self.state.symbol_table.push_scope();

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
        Ok(AnchorCommand {
            end_step_id,
            assignment_args,
            variable_args,
        })
    }

    /// Parses an argument for an `anchor` proof command. This can be either a variable binding of
    /// the form `(<symbol> <sort>)` or an assignment, of the form `(:= (<symbol> <sort>) <term>)`.
    fn parse_anchor_argument(&mut self) -> AletheResult<Either<(SortedVar, Rc<Term>), SortedVar>> {
        self.expect_token(Token::OpenParen)?;
        Ok(if self.current_token == Token::Keyword("=".into()) {
            self.next_token()?;
            let (a, sort) = self.parse_sorted_var()?;
            self.insert_sorted_var((a.clone(), sort.clone()));

            let b = match &self.current_token {
                // If we encounter a symbol as the value of the assignment, we must check if there
                // are any function definitions with that symbol. If there are, we consider the
                // value a term instead of a new variable
                Token::Symbol(s) if !self.state.function_defs.contains_key(s) => {
                    let var = self.expect_symbol()?;
                    self.insert_sorted_var((var.clone(), sort.clone()));
                    let iden = Identifier::Simple(var);
                    self.add_term(Term::Terminal(Terminal::Var(iden, sort.clone())))
                }
                _ => self.parse_term_expecting_sort(sort.as_sort().unwrap())?,
            };

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

    /// Parses a `declare-fun` proof command. Returns the function name and a term representing its
    /// sort. This method assumes that the `(` and `declare-fun` tokens were already consumed.
    fn parse_declare_fun(&mut self) -> AletheResult<(String, Rc<Term>)> {
        let name = self.expect_symbol()?;
        let sort = {
            self.expect_token(Token::OpenParen)?;
            let mut sorts = self.parse_sequence(Self::parse_sort, false)?;
            sorts.push(self.parse_sort()?);
            let sorts = self.add_all(sorts);
            if sorts.len() == 1 {
                sorts.into_iter().next().unwrap()
            } else {
                self.add_term(Term::Sort(Sort::Function(sorts)))
            }
        };
        self.expect_token(Token::CloseParen)?;
        Ok((name, sort))
    }

    /// Parses a declare-sort proof command. Returns the sort name and its arity. This method
    /// assumes that the `(` and `declare-sort` tokens were already consumed.
    fn parse_declare_sort(&mut self) -> AletheResult<(String, usize)> {
        let name = self.expect_symbol()?;
        let arity_pos = self.current_position;
        let arity = self.expect_numeral()?;
        self.expect_token(Token::CloseParen)?;
        let arity = arity.to_usize().ok_or(Error::Parser(
            ParserError::InvalidSortArity(arity),
            arity_pos,
        ))?;
        Ok((name, arity))
    }

    /// Parses a `define-fun` proof command. Returns the function name and its definition. This
    /// method assumes that the `(` and `define-fun` tokens were already consumed.
    fn parse_define_fun(&mut self) -> AletheResult<(String, FunctionDef)> {
        let name = self.expect_symbol()?;
        self.expect_token(Token::OpenParen)?;
        let params = self.parse_sequence(Self::parse_sorted_var, false)?;
        let return_sort = self.parse_sort()?;

        // In order to correctly parse the function body, we push a new scope to the symbol table
        // and add the functions arguments to it.
        self.state.symbol_table.push_scope();
        for var in &params {
            self.insert_sorted_var(var.clone());
        }
        let body = self.parse_term_expecting_sort(return_sort.as_sort().unwrap())?;
        self.state.symbol_table.pop_scope();

        self.expect_token(Token::CloseParen)?;

        Ok((name, FunctionDef { params, body }))
    }

    /// Parses a clause of the form `(cl <term>*)`.
    fn parse_clause(&mut self) -> AletheResult<Vec<Rc<Term>>> {
        self.expect_token(Token::OpenParen)?;
        self.expect_token(Token::ReservedWord(Reserved::Cl))?;
        self.parse_sequence(|p| p.parse_term_expecting_sort(&Sort::Bool), false)
    }

    /// Parses an argument for a `step` command.
    fn parse_proof_arg(&mut self) -> AletheResult<ProofArg> {
        if self.current_token == Token::OpenParen {
            self.next_token()?; // Consume `(` token

            // If we encounter a `(` token, this could be an assignment argument of the form
            // `(:= <symbol> <term>)`, or a regular term that starts with `(`. Note that the
            // lexer reads `:=` as a keyword with contents `=`.
            if self.current_token == Token::Keyword("=".into()) {
                self.next_token()?; // Consume `:=` token
                let name = self.expect_symbol()?;
                let value = self.parse_term()?;
                self.expect_token(Token::CloseParen)?;
                Ok(ProofArg::Assign(name, value))
            } else {
                // If the first token is not `:=`, this argument is just a regular term. Since
                // we already consumed the `(` token, we have to call `parse_application`
                // instead of `parse_term`.
                let term = self.parse_application()?;
                Ok(ProofArg::Term(term))
            }
        } else {
            let term = self.parse_term()?;
            Ok(ProofArg::Term(term))
        }
    }

    /// Parses a sorted variable of the form `(<symbol> <sort>)`.
    fn parse_sorted_var(&mut self) -> AletheResult<SortedVar> {
        self.expect_token(Token::OpenParen)?;
        let symbol = self.expect_symbol()?;
        let sort = self.parse_sort()?;
        self.expect_token(Token::CloseParen)?;
        Ok((symbol, self.add_term(sort)))
    }

    /// Parses a term.
    pub fn parse_term(&mut self) -> AletheResult<Rc<Term>> {
        let term = match self.next_token()? {
            (Token::Numeral(n), _) if self.interpret_integers_as_reals => {
                terminal!(real BigRational::from_integer(n))
            }
            (Token::Numeral(n), _) => terminal!(int n),
            (Token::Decimal(r), _) => terminal!(real r),
            (Token::String(s), _) => terminal!(string s),
            (Token::Symbol(s), pos) => {
                // Check to see if there is a nullary function defined with this name
                return Ok(if let Some(func_def) = self.state.function_defs.get(&s) {
                    if func_def.params.is_empty() {
                        func_def.body.clone()
                    } else {
                        return Err(Error::Parser(
                            ParserError::WrongNumberOfArgs(func_def.params.len().into(), 0),
                            pos,
                        ));
                    }
                } else {
                    self.make_var(Identifier::Simple(s))
                        .map_err(|err| Error::Parser(err, pos))?
                });
            }
            (Token::OpenParen, _) => return self.parse_application(),
            (other, pos) => return Err(Error::Parser(ParserError::UnexpectedToken(other), pos)),
        };
        Ok(self.add_term(term))
    }

    /// Parses a term and checks that its sort matches the expected sort. If not, returns an error.
    fn parse_term_expecting_sort(&mut self, expected_sort: &Sort) -> AletheResult<Rc<Term>> {
        let pos = self.current_position;
        let term = self.parse_term()?;
        SortError::assert_eq(expected_sort, self.sort(&term))
            .map_err(|e| Error::Parser(e.into(), pos))?;
        Ok(term)
    }

    /// Parses a quantifier term. This method assumes that the `(` and quantifier tokens were
    /// already consumed.
    fn parse_quantifier(&mut self, quantifier: Quantifier) -> AletheResult<Rc<Term>> {
        self.expect_token(Token::OpenParen)?;
        self.state.symbol_table.push_scope();
        let bindings = self.parse_sequence(
            |p| {
                let var = p.parse_sorted_var()?;
                p.insert_sorted_var(var.clone());
                Ok(var)
            },
            true,
        )?;
        let term = self.parse_term_expecting_sort(&Sort::Bool)?;
        self.state.symbol_table.pop_scope();
        self.expect_token(Token::CloseParen)?;
        Ok(self.add_term(Term::Quant(quantifier, BindingList(bindings), term)))
    }

    /// Parses a `choice` term. This method assumes that the `(` and `choice` tokens were already
    /// consumed.
    fn parse_choice_term(&mut self) -> AletheResult<Rc<Term>> {
        self.expect_token(Token::OpenParen)?;
        let var = self.parse_sorted_var()?;
        self.insert_sorted_var(var.clone());
        self.expect_token(Token::CloseParen)?;
        let inner = self.parse_term()?;
        self.expect_token(Token::CloseParen)?;
        Ok(self.add_term(Term::Choice(var, inner)))
    }

    /// Parses a `lambda` term. This method assumes that the `(` and `let` tokens were already
    /// consumed.
    fn parse_lambda_term(&mut self) -> AletheResult<Rc<Term>> {
        self.expect_token(Token::OpenParen)?;
        self.state.symbol_table.push_scope();
        let bindings = self.parse_sequence(
            |p| {
                let var = p.parse_sorted_var()?;
                p.insert_sorted_var(var.clone());
                Ok(var)
            },
            true,
        )?;
        let body = self.parse_term()?;
        self.state.symbol_table.pop_scope();
        self.expect_token(Token::CloseParen)?;
        Ok(self.add_term(Term::Lambda(BindingList(bindings), body)))
    }

    /// Parses a `let` term. This method assumes that the `(` and `let` tokens were already
    /// consumed.
    fn parse_let_term(&mut self) -> AletheResult<Rc<Term>> {
        self.expect_token(Token::OpenParen)?;
        self.state.symbol_table.push_scope();
        let bindings = self.parse_sequence(
            |p| {
                p.expect_token(Token::OpenParen)?;
                let name = p.expect_symbol()?;
                let value = p.parse_term()?;
                let sort = p.add_term(Term::Sort(p.sort(&value).clone()));
                p.insert_sorted_var((name.clone(), sort));
                p.expect_token(Token::CloseParen)?;
                Ok((name, value))
            },
            true,
        )?;
        let inner = self.parse_term()?;
        self.expect_token(Token::CloseParen)?;
        self.state.symbol_table.pop_scope();
        Ok(self.add_term(Term::Let(BindingList(bindings), inner)))
    }

    /// Parses an annotated term, of the form `(! <term> <attribute>+)`. The two supported
    /// attributes are `:named` and `:pattern`, though the latter is ignored. If any other
    /// attribute is present, an error will be returned. This method assumes that the `(` and `!`
    /// tokens were already consumed.
    fn parse_annotated_term(&mut self) -> AletheResult<Rc<Term>> {
        let inner = self.parse_term()?;
        self.parse_sequence(
            |p| {
                let attribute_pos = p.current_position;
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
                        p.add_function_def(name, func_def);
                        Ok(())
                    }
                    "pattern" => {
                        // We just ignore the values of `:pattern` attributes
                        p.expect_token(Token::OpenParen)?;
                        p.parse_sequence(Parser::parse_term, true)?;
                        Ok(())
                    }
                    _ => Err(Error::Parser(
                        ParserError::UnknownAttribute(attribute),
                        attribute_pos,
                    )),
                }
            },
            true,
        )?;
        Ok(inner)
    }

    /// Parses any term that starts with `(`, that is, any term that is not a constant or a
    /// variable. This method assumes that the `(` token was already consumed.
    fn parse_application(&mut self) -> AletheResult<Rc<Term>> {
        let head_pos = self.current_position;
        match &self.current_token {
            &Token::ReservedWord(reserved) => {
                self.next_token()?;
                match reserved {
                    Reserved::Exists => self.parse_quantifier(Quantifier::Exists),
                    Reserved::Forall => self.parse_quantifier(Quantifier::Forall),
                    Reserved::Choice => self.parse_choice_term(),
                    Reserved::Lambda => self.parse_lambda_term(),
                    Reserved::Bang => self.parse_annotated_term(),
                    Reserved::Let => self.parse_let_term(),
                    _ => Err(Error::Parser(
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
                    .map_err(|err| Error::Parser(err, head_pos))
            }
            Token::Symbol(s) if self.state.function_defs.get(s).is_some() => {
                let head_pos = self.current_position;
                let func_name = self.expect_symbol()?;
                let args = self.parse_sequence(Self::parse_term, true)?;
                let func = self.state.function_defs.get(&func_name).unwrap();

                // If there is a function definition with this function name, we sort check
                // the arguments and apply the definition by performing a beta reduction.
                assert_num_args(&args, func.params.len())
                    .map_err(|err| Error::Parser(err, head_pos))?;
                for (arg, param) in args.iter().zip(func.params.iter()) {
                    SortError::assert_eq(param.1.as_sort().unwrap(), self.sort(arg))
                        .map_err(|err| Error::Parser(err.into(), head_pos))?;
                }

                // Build a hash map of all the parameter names and the values they will
                // take
                let substitution = {
                    // We have to take a reference to the term pool here, so the closure in
                    // the `map` call later on doesn't have to capture all of `self`, and
                    // can just capture the term pool. We need this to please the borrow
                    // checker
                    let pool = &mut self.state.term_pool;
                    func.params
                        .iter()
                        .zip(args)
                        .map(|((name, sort), arg)| {
                            (pool.add_term(terminal!(var name; sort.clone())), arg)
                        })
                        .collect()
                };

                // Since we already checked the sorts of the arguments, creating this substitution
                // can never fail
                let result = Substitution::new(&mut self.state.term_pool, substitution)
                    .unwrap()
                    .apply(&mut self.state.term_pool, &func.body);

                Ok(result)
            }
            _ => {
                let func = self.parse_term()?;
                let args = self.parse_sequence(Self::parse_term, true)?;
                self.make_app(func, args)
                    .map_err(|err| Error::Parser(err, head_pos))
            }
        }
    }

    /// Parses a sort.
    fn parse_sort(&mut self) -> AletheResult<Term> {
        let pos = self.current_position;
        let (name, args) = match self.next_token()?.0 {
            Token::Symbol(s) => (s, Vec::new()),
            Token::OpenParen => {
                let name = self.expect_symbol()?;
                let args = self.parse_sequence(Parser::parse_sort, true)?;
                (name, self.add_all(args))
            }
            other => return Err(Error::Parser(ParserError::UnexpectedToken(other), pos)),
        };

        let sort = match name.as_str() {
            "Bool" | "Int" | "Real" | "String" if !args.is_empty() => Err(Error::Parser(
                ParserError::WrongNumberOfArgs(0.into(), args.len()),
                pos,
            )),
            "Bool" => Ok(Sort::Bool),
            "Int" => Ok(Sort::Int),
            "Real" => Ok(Sort::Real),
            "String" => Ok(Sort::String),

            "Array" => match args.as_slice() {
                [x, y] => Ok(Sort::Array(x.clone(), y.clone())),
                _ => Err(Error::Parser(
                    ParserError::WrongNumberOfArgs(2.into(), args.len()),
                    pos,
                )),
            },
            _ => match self.state.sort_declarations.get(&name) {
                Some(arity) if *arity == args.len() => Ok(Sort::Atom(name, args)),
                Some(arity) => Err(Error::Parser(
                    ParserError::WrongNumberOfArgs((*arity).into(), args.len()),
                    pos,
                )),
                None => Err(Error::Parser(ParserError::UndefinedSort(name), pos)),
            },
        }?;
        Ok(Term::Sort(sort))
    }
}
