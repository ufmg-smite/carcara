//! A parser for the veriT Proof Format.

pub mod ast;
pub mod error;
pub mod lexer;

use crate::terminal;
use ast::*;
use error::*;
use lexer::*;
use std::collections::{hash_map::Entry, HashMap};
use std::io::BufRead;
use std::rc::Rc;
use std::str::FromStr;

/// A parser for the veriT Proof Format. The parser makes use of hash consing to reduce memory usage
/// by sharing identical terms in the AST.
pub struct Parser<R> {
    lexer: Lexer<R>,
    current_token: Token,
    state: ParserState,
    symbol_table: HashMap<Identifier, Rc<Term>>,
}

#[derive(Default)]
struct ParserState {
    function_defs: HashMap<String, FunctionDef>,
    terms_map: HashMap<Term, Rc<Term>>,
    sort_declarations: HashMap<String, (u64, Rc<Term>)>,
}

impl<R: BufRead> Parser<R> {
    /// Constructs a new `Parser` from a type that implements `BufRead`. This operation can fail if
    /// there is an IO or lexer error on the first token.
    pub fn new(input: R) -> ParserResult<Self> {
        let mut lexer = Lexer::new(input)?;
        let current_token = lexer.next_token()?;
        let mut parser = Parser {
            lexer,
            current_token,
            state: Default::default(),
            symbol_table: Default::default(),
        };
        parser.add_builtins();
        Ok(parser)
    }

    fn add_builtins(&mut self) {
        let builtins = vec![("true", Term::bool()), ("false", Term::bool())];
        for (iden, sort) in builtins {
            let iden = Identifier::Simple(iden.into());
            let sort = self.add_term(sort);
            self.symbol_table.insert(iden, sort);
        }
    }

    /// Advances the parser one token, and returns the previous `current_token`.
    fn next_token(&mut self) -> ParserResult<Token> {
        let new = self.lexer.next_token()?;
        Ok(std::mem::replace(&mut self.current_token, new))
    }

    /// Consumes the current token if it equals `expected`. Returns an error otherwise.
    fn expect_token(&mut self, expected: Token) -> ParserResult<()> {
        let got = self.next_token()?;
        if got == expected {
            Ok(())
        } else {
            Err(ParserError::UnexpectedToken(got))
        }
    }

    /// Consumes the current token if it is a symbol, and returns the inner `String`. Returns an
    /// error otherwise.
    fn expect_symbol(&mut self) -> ParserResult<String> {
        match self.next_token()? {
            Token::Symbol(s) => Ok(s),
            other => Err(ParserError::UnexpectedToken(other)),
        }
    }

    fn expect_numeral(&mut self) -> ParserResult<u64> {
        match self.next_token()? {
            Token::Numeral(n) => Ok(n),
            other => Err(ParserError::UnexpectedToken(other)),
        }
    }

    /// Takes a term and returns an `Rc` referencing it. If the term was not originally in the
    /// terms hash map, it is added to it.
    fn add_term(&mut self, term: Term) -> Rc<Term> {
        match self.state.terms_map.entry(term.clone()) {
            Entry::Occupied(occupied_entry) => occupied_entry.get().clone(),
            Entry::Vacant(vacant_entry) => vacant_entry.insert(Rc::new(term)).clone(),
        }
    }

    fn make_var(&mut self, iden: Identifier) -> ParserResult<Term> {
        let sort = self
            .symbol_table
            .get(&iden)
            .ok_or_else(|| ParserError::UndefinedIden(iden.clone()))?;
        Ok(Term::Terminal(Terminal::Var(iden, sort.clone())))
    }

    /// Constructs and sort checks an operation term.
    fn make_op(&mut self, op: Operator, args: Vec<Term>) -> ParserResult<Term> {
        let sorts: Vec<_> = args.iter().map(Term::sort).collect();
        match op {
            Operator::Add | Operator::Sub | Operator::Mult | Operator::Div => {
                ParserError::assert_num_of_args(&args, 2)?;
                SortError::expect_one_of(&[Term::int(), Term::real()], &sorts[0])?;
                SortError::expect_eq(&sorts[0], &sorts[1])?;
            }
            Operator::Eq => {
                ParserError::assert_num_of_args(&args, 2)?;
                SortError::expect_eq(&sorts[0], &sorts[1])?;
            }
            Operator::Or | Operator::And => {
                ParserError::assert_num_of_args(&args, 2)?;
                for s in sorts {
                    SortError::expect_eq(&Term::bool(), &s)?;
                }
            }
            Operator::Not => {
                ParserError::assert_num_of_args(&args, 1)?;
                SortError::expect_eq(&Term::bool(), &sorts[0])?;
            }
        }
        let args = args.into_iter().map(|arg| self.add_term(arg)).collect();
        Ok(Term::Op(op, args))
    }

    /// Constructs and sort checks an application term.
    fn make_app(&mut self, function: Term, args: Vec<Term>) -> ParserResult<Term> {
        let sorts = {
            let function_sort = function.sort();
            if let Term::Sort(SortKind::Function, sorts) = function_sort {
                sorts
            } else {
                // Function does not have function sort
                return Err(ParserError::SortError(SortError::Expected {
                    expected: Term::Sort(SortKind::Function, Vec::new()),
                    got: function_sort,
                }));
            }
        };
        ParserError::assert_num_of_args(&args, sorts.len() - 1)?;
        for i in 0..args.len() {
            SortError::expect_eq(sorts[i].as_ref(), &args[i])?;
        }
        let function = self.add_term(function);
        let args: Vec<_> = args.into_iter().map(|term| self.add_term(term)).collect();
        Ok(Term::App(function, args))
    }

    /// Calls `parse_func` repeatedly until a closing parenthesis is reached. If `non_empty` is
    /// true, empty sequences will result in an error. This method consumes the ending ")" token.
    fn parse_sequence<T, F>(&mut self, parse_func: F, non_empty: bool) -> ParserResult<Vec<T>>
    where
        F: Fn(&mut Self) -> ParserResult<T>,
    {
        let mut result = Vec::new();
        while self.current_token != Token::CloseParen {
            result.push(parse_func(self)?);
        }
        if non_empty && result.is_empty() {
            Err(ParserError::EmptySequence)
        } else {
            self.next_token()?; // Consume ")" token
            Ok(result)
        }
    }

    /// Parses a proof.
    pub fn parse_proof(&mut self) -> ParserResult<Proof> {
        let mut commands = Vec::new();
        while self.current_token != Token::Eof {
            self.expect_token(Token::OpenParen)?;
            let command = match self.next_token()? {
                Token::ReservedWord(Reserved::Assume) => self.parse_assume_command(),
                Token::ReservedWord(Reserved::Step) => self.parse_step_command(),
                Token::ReservedWord(Reserved::DeclareFun) => {
                    let (name, sort) = self.parse_declare_fun()?;
                    self.symbol_table.insert(Identifier::Simple(name), sort);
                    continue;
                }
                Token::ReservedWord(Reserved::DeclareSort) => {
                    let (name, arity) = self.parse_declare_sort()?;
                    // User declared sorts are represented with the `UserDeclared` sort kind, and an
                    // argument which is a string terminal representing the sort name.
                    let sort = {
                        let arg = self.add_term(terminal!(string name.clone()));
                        self.add_term(Term::Sort(SortKind::UserDeclared, vec![arg]))
                    };
                    self.state.sort_declarations.insert(name, (arity, sort));
                    continue;
                }
                Token::ReservedWord(Reserved::DefineFun) => {
                    let (name, func_def) = self.parse_define_fun()?;
                    self.state.function_defs.insert(name, func_def);
                    continue;
                }
                Token::ReservedWord(Reserved::Anchor) => todo!(),
                other => Err(ParserError::UnexpectedToken(other)),
            };
            commands.push(command?);
        }
        Ok(Proof(commands))
    }

    /// Parses an "assume" proof command. This method assumes that the "(" and "assume" tokens were
    /// already consumed.
    fn parse_assume_command(&mut self) -> ParserResult<ProofCommand> {
        let symbol = self.expect_symbol()?;
        let term = self.parse_term()?;
        SortError::expect_eq(&Term::bool(), &term.sort())?;
        let term = self.add_term(term);
        self.expect_token(Token::CloseParen)?;
        Ok(ProofCommand::Assume(symbol, term))
    }

    /// Parses a "step" proof command. This method assumes that the "(" and "step" tokens were
    /// already consumed.
    fn parse_step_command(&mut self) -> ParserResult<ProofCommand> {
        let step_name = self.expect_symbol()?;
        let clause = self.parse_clause()?;
        self.expect_token(Token::Keyword("rule".into()))?;
        let rule = self.expect_symbol()?;

        let premises = if self.current_token == Token::Keyword("premises".into()) {
            self.next_token()?;
            self.expect_token(Token::OpenParen)?;
            self.parse_sequence(Self::expect_symbol, true)?
        } else {
            Vec::new()
        };

        let args = if self.current_token == Token::Keyword("args".into()) {
            self.next_token()?;
            self.parse_proof_args()?
        } else {
            Vec::new()
        };

        self.expect_token(Token::CloseParen)?;

        Ok(ProofCommand::Step {
            step_name,
            clause,
            rule,
            premises,
            args,
        })
    }

    /// Parses a "declare-fun" proof command. Returns the function name and a term representing its
    /// sort. This method assumes that the "(" and "declare-fun" tokens were already consumed.
    fn parse_declare_fun(&mut self) -> ParserResult<(String, Rc<Term>)> {
        let name = self.expect_symbol()?;
        let sort = {
            self.expect_token(Token::OpenParen)?;
            let mut sorts = self.parse_sequence(Self::parse_sort, false)?;
            sorts.push(self.parse_sort()?);
            let sorts: Vec<_> = sorts.into_iter().map(|term| self.add_term(term)).collect();
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
        Ok((name, arity))
    }

    /// Parses a "define-fun" proof command. Returns the function name and its definition. This
    /// method assumes that the "(" and "define-fun" tokens were already consumed.
    fn parse_define_fun(&mut self) -> ParserResult<(String, FunctionDef)> {
        let name = self.expect_symbol()?;
        self.expect_token(Token::OpenParen)?;
        let args = self.parse_sequence(Self::parse_sorted_var, false)?;
        let return_sort = self.parse_sort()?;
        let body = self.parse_term()?;
        self.expect_token(Token::CloseParen)?;
        Ok((
            name,
            FunctionDef {
                args,
                return_sort,
                body,
            },
        ))
    }

    /// Parses a clause of the form "(cl <term>*)".
    fn parse_clause(&mut self) -> ParserResult<Vec<Rc<Term>>> {
        self.expect_token(Token::OpenParen)?;
        self.expect_token(Token::ReservedWord(Reserved::Cl))?;
        let terms = self
            .parse_sequence(Self::parse_term, false)?
            .into_iter()
            .map(|term| -> ParserResult<Rc<Term>> {
                SortError::expect_eq(&Term::bool(), &term.sort())?;
                Ok(self.add_term(term))
            })
            .collect::<Result<_, _>>()?;
        Ok(terms)
    }

    fn parse_proof_args(&mut self) -> ParserResult<Vec<Rc<Term>>> {
        // TODO: parse args of the form "(<symbol> <term>)"
        self.expect_token(Token::OpenParen)?;
        Ok(self
            .parse_sequence(Self::parse_term, true)?
            .into_iter()
            .map(|term| self.add_term(term))
            .collect())
    }

    /// Parses a sorted variable of the form "(<symbol> <sort>)".
    fn parse_sorted_var(&mut self) -> ParserResult<(String, Rc<Term>)> {
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
            Token::Symbol(s) => self.make_var(Identifier::Simple(s)),
            Token::OpenParen => self.parse_application(),
            other => Err(ParserError::UnexpectedToken(other)),
        }
    }

    fn parse_application(&mut self) -> ParserResult<Term> {
        match self.next_token()? {
            Token::Symbol(s) => {
                if let Ok(operator) = Operator::from_str(&s) {
                    let args = self.parse_sequence(Self::parse_term, true)?;
                    self.make_op(operator, args)
                } else {
                    let func = self.make_var(Identifier::Simple(s))?;
                    let args = self.parse_sequence(Self::parse_term, true)?;
                    self.make_app(func, args)
                }
            }
            _ => todo!(),
        }
    }

    /// Parses a sort.
    fn parse_sort(&mut self) -> ParserResult<Term> {
        // TODO: since every sort is a valid term, maybe use `parse_term` to parse sorts
        match self.next_token()? {
            Token::Symbol(s) => match s.as_ref() {
                "Bool" => Ok(Term::bool()),
                "Int" => Ok(Term::int()),
                "Real" => Ok(Term::real()),
                "String" => Ok(Term::string()),
                other => {
                    if let Some((_, sort)) = self.state.sort_declarations.get(other) {
                        Ok((**sort).clone())
                    } else {
                        Err(ParserError::UndefinedIden(Identifier::Simple(other.into())))
                    }
                }
            },
            other => Err(ParserError::UnexpectedToken(other)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io;

    fn parse_term(input: &str) -> Term {
        Parser::new(io::Cursor::new(input))
            .and_then(|mut p| p.parse_term())
            .expect("parser error during test")
    }

    fn parse_term_err(input: &str) -> ParserError {
        Parser::new(io::Cursor::new(input))
            .and_then(|mut p| p.parse_term())
            .expect_err("expected error")
    }

    #[test]
    fn test_hash_consing() {
        let input = "(-
            (-
                (+ 1 2)
                (/ (+ 1 2) (+ 1 2))
            )
            (* 2 2)
        )";
        let mut parser = Parser::new(io::Cursor::new(input)).unwrap();
        parser.parse_term().unwrap();

        // We expect this input to result in 6 unique terms after parsing:
        //   1
        //   2
        //   (+ 1 2)
        //   (/ (+ 1 2) (+ 1 2))
        //   (- (+ 1 2) (/ ...))
        //   (* 2 2)
        // Note that the outer term (- (- ...) (* 2 2)) is not added to the hash map
        let expected = [
            terminal!(int 1),
            terminal!(int 2),
            parse_term("(+ 1 2)"),
            parse_term("(/ (+ 1 2) (+ 1 2))"),
            parse_term("(- (+ 1 2) (/ (+ 1 2) (+ 1 2)))"),
            parse_term("(* 2 2)"),
        ];
        for e in &expected {
            assert!(parser.state.terms_map.contains_key(e))
        }
    }

    #[test]
    fn test_constant_terms() {
        assert_eq!(terminal!(int 42), parse_term("42"));
        assert_eq!(terminal!(real 3 / 2), parse_term("1.5"));
        assert_eq!(terminal!(string "foo"), parse_term("\"foo\""));
    }

    #[test]
    fn test_arithmetic_ops() {
        assert_eq!(
            Term::Op(
                Operator::Add,
                vec![Rc::new(terminal!(int 2)), Rc::new(terminal!(int 3))]
            ),
            parse_term("(+ 2 3)"),
        );

        assert!(matches!(
            parse_term_err("(+ (- 1 2) (* 3.0 4.2))"),
            ParserError::SortError(SortError::Expected { .. }),
        ));
    }

    #[test]
    fn test_logic_ops() {
        assert_eq!(
            Term::Op(
                Operator::And,
                vec![
                    Rc::new(terminal!(var "true"; Rc::new(Term::bool()))),
                    Rc::new(terminal!(var "false"; Rc::new(Term::bool()))),
                ]
            ),
            parse_term("(and true false)"),
        );

        assert_eq!(
            Term::Op(
                Operator::Eq,
                vec![Rc::new(terminal!(int 2)), Rc::new(terminal!(int 3))]
            ),
            parse_term("(= 2 3)"),
        );

        assert_eq!(
            Term::Op(
                Operator::Not,
                vec![Rc::new(terminal!(var "false"; Rc::new(Term::bool())))]
            ),
            parse_term("(not false)"),
        );

        assert!(matches!(
            parse_term_err("(or true 1.2)"),
            ParserError::SortError(SortError::Expected {
                expected: Term::Sort(SortKind::Bool, _),
                ..
            }),
        ));
        assert!(matches!(
            parse_term_err("(= 10 10.0)"),
            ParserError::SortError(SortError::Expected { .. }),
        ));
        assert_eq!(
            ParserError::WrongNumberOfArgs(1, 3),
            parse_term_err("(not 1 2 3)"),
        );
        assert_eq!(
            ParserError::WrongNumberOfArgs(2, 1),
            parse_term_err("(or true)"),
        );
    }
}
