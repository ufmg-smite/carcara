pub mod ast;
pub mod lexer;

use ast::*;
use lexer::*;
use std::collections::{hash_map::Entry, HashMap};
use std::io::{self, BufRead};
use std::rc::Rc;
use std::str::FromStr;

#[derive(Debug, PartialEq)]
pub enum ParserError {
    Io(ParserIoError),
    UnexpectedChar {
        expected: &'static [char],
        got: Option<char>,
    },
    LeadingZero(String),
    BackslashInQuotedSymbol,
    EofInQuotedSymbol,
    EofInString,
    UnexpectedToken(Token),
    EmptySequence,
    TypeError,
    WrongNumberOfArgs(usize, usize),
}

impl From<io::Error> for ParserError {
    fn from(e: io::Error) -> Self {
        ParserError::Io(ParserIoError(e))
    }
}

/// A simple wrapper of io::Error so ParserError can derive PartialEq
#[derive(Debug)]
pub struct ParserIoError(io::Error);

impl PartialEq for ParserIoError {
    fn eq(&self, other: &Self) -> bool {
        self.0.kind() == other.0.kind()
    }
}

type ParserResult<T> = Result<T, ParserError>;

#[derive(Default)]
pub struct ParserState {
    function_defs: HashMap<String, FunctionDef>,
    terms_map: HashMap<Term, Rc<Term>>,
}

pub struct Parser<R> {
    lexer: Lexer<R>,
    current_token: Token,
    state: ParserState,
    symbol_table: HashMap<Identifier, Rc<Term>>,
}

impl<R: BufRead> Parser<R> {
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

    fn next_token(&mut self) -> ParserResult<Token> {
        let new = self.lexer.next_token()?;
        Ok(std::mem::replace(&mut self.current_token, new))
    }

    fn expect_token(&mut self, expected: Token) -> ParserResult<Token> {
        let got = self.next_token()?;
        if got == expected {
            Ok(got)
        } else {
            Err(ParserError::UnexpectedToken(got))
        }
    }

    fn expect_symbol(&mut self) -> ParserResult<String> {
        match self.next_token()? {
            Token::Symbol(s) => Ok(s),
            other => Err(ParserError::UnexpectedToken(other)),
        }
    }

    fn add_term(&mut self, term: Term) -> Rc<Term> {
        match self.state.terms_map.entry(term.clone()) {
            Entry::Occupied(occupied_entry) => occupied_entry.get().clone(),
            Entry::Vacant(vacant_entry) => vacant_entry.insert(Rc::new(term)).clone(),
        }
    }

    fn get_sort(&self, term: &Term) -> Option<Term> {
        match term {
            Term::Terminal(t) => match t {
                Terminal::Integer(_) => Some(Term::int()),
                Terminal::Real(_) => Some(Term::real()),
                Terminal::String(_) => Some(Term::string()),
                Terminal::Var(iden) => self.symbol_table.get(iden).map(|t| (**t).clone()),
            },
            Term::Op(op, args) => match op {
                Operator::Add | Operator::Sub | Operator::Mult | Operator::Div => {
                    self.get_sort(args[0].as_ref())
                }
                Operator::Eq | Operator::Or | Operator::And | Operator::Not => Some(Term::bool()),
            },
            _ => todo!(),
        }
    }

    fn make_op(&mut self, op: Operator, args: Vec<Term>) -> ParserResult<Term> {
        let sorts: Vec<_> = args
            .iter()
            .map(|term| self.get_sort(term))
            .collect::<Option<_>>()
            .ok_or(ParserError::TypeError)?;
        match op {
            Operator::Add | Operator::Sub | Operator::Mult | Operator::Div => {
                Parser::expect_num_of_args(&args, 2)?;
                if (sorts[0] != Term::int() && sorts[0] != Term::real()) || sorts[0] != sorts[1] {
                    return Err(ParserError::TypeError);
                }
            }
            Operator::Eq => {
                Parser::expect_num_of_args(&args, 2)?;
                if sorts[0] != sorts[1] {
                    return Err(ParserError::TypeError);
                }
            }
            Operator::Or | Operator::And => {
                Parser::expect_num_of_args(&args, 2)?;
                if sorts.iter().any(|s| s != &Term::bool()) {
                    return Err(ParserError::TypeError);
                }
            }
            Operator::Not => {
                Parser::expect_num_of_args(&args, 1)?;
                if sorts[0] != Term::bool() {
                    return Err(ParserError::TypeError);
                }
            }
        }
        let args = args.into_iter().map(|arg| self.add_term(arg)).collect();
        Ok(Term::Op(op, args))
    }

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
                Token::ReservedWord(Reserved::DeclareSort) => todo!(),
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

    fn parse_assume_command(&mut self) -> ParserResult<ProofCommand> {
        let symbol = self.expect_symbol()?;
        let term = self.parse_term()?;
        let term = self.add_term(term);
        self.expect_token(Token::CloseParen)?;
        Ok(ProofCommand::Assume(symbol, term))
    }

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

    fn parse_clause(&mut self) -> ParserResult<Clause> {
        self.expect_token(Token::OpenParen)?;
        self.expect_token(Token::ReservedWord(Reserved::Cl))?;
        let terms = self
            .parse_sequence(Self::parse_term, false)?
            .into_iter()
            .map(|term| self.add_term(term))
            .collect();
        Ok(Clause(terms))
    }

    fn parse_proof_args(&mut self) -> ParserResult<Vec<Rc<Term>>> {
        self.expect_token(Token::OpenParen)?;
        Ok(self
            .parse_sequence(Self::parse_term, true)?
            .into_iter()
            .map(|term| self.add_term(term))
            .collect())
    }

    fn parse_sorted_var(&mut self) -> ParserResult<(String, Rc<Term>)> {
        self.expect_token(Token::OpenParen)?;
        let symbol = self.expect_symbol()?;
        let sort = self.parse_sort()?;
        self.expect_token(Token::CloseParen)?;
        Ok((symbol, self.add_term(sort)))
    }

    pub fn parse_term(&mut self) -> ParserResult<Term> {
        match self.next_token()? {
            Token::Numeral(n) => Ok(Term::Terminal(Terminal::Integer(n))),
            Token::Decimal(r) => Ok(Term::Terminal(Terminal::Real(r))),
            Token::String(s) => Ok(Term::Terminal(Terminal::String(s))),
            Token::Symbol(s) => Ok(Term::Terminal(Terminal::Var(Identifier::Simple(s)))),
            Token::OpenParen => self.parse_application(),
            other => Err(ParserError::UnexpectedToken(other)),
        }
    }

    fn parse_application(&mut self) -> ParserResult<Term> {
        match self.current_token {
            Token::Symbol(ref s) => {
                if let Ok(operator) = Operator::from_str(s) {
                    self.next_token()?;
                    let args = self.parse_sequence(Self::parse_term, true)?;
                    self.make_op(operator, args)
                } else {
                    todo!()
                }
            }
            _ => todo!(),
        }
    }

    fn parse_sort(&mut self) -> ParserResult<Term> {
        // TODO: since every sort is a valid term, maybe use `parse_term` to parse sorts
        match self.next_token()? {
            Token::Symbol(s) => match s.as_ref() {
                "Bool" => Ok(Term::bool()),
                "Int" => Ok(Term::int()),
                "Real" => Ok(Term::real()),
                "String" => Ok(Term::string()),
                _ => todo!(),
            },
            other => Err(ParserError::UnexpectedToken(other)),
        }
    }
}

impl Parser<()> {
    fn expect_num_of_args<T>(sequence: &[T], expected: usize) -> ParserResult<()> {
        let got = sequence.len();
        if got != expected {
            Err(ParserError::WrongNumberOfArgs(expected, got))
        } else {
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! terminal {
        (int $e:literal) => {
            Term::Terminal(Terminal::Integer($e))
        };
        (real $num:literal / $denom:literal) => {
            Term::Terminal(Terminal::Real(num_rational::Ratio::new($num, $denom)))
        };
        (string $e:literal) => {
            Term::Terminal(Terminal::String($e.into()))
        };
        (var $e:literal) => {
            Term::Terminal(Terminal::Var(Identifier::Simple($e.into())))
        };
    }

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
    fn test_identifier_terms() {
        assert_eq!(terminal!(var "foo"), parse_term("foo"));
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

        assert_eq!(
            ParserError::TypeError,
            parse_term_err("(+ (- 1 2) (* 3.0 4.2))"),
        );
    }

    #[test]
    fn test_logic_ops() {
        assert_eq!(
            Term::Op(
                Operator::And,
                vec![
                    Rc::new(terminal!(var "true")),
                    Rc::new(terminal!(var "false")),
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
            Term::Op(Operator::Not, vec![Rc::new(terminal!(var "false"))]),
            parse_term("(not false)"),
        );

        assert_eq!(ParserError::TypeError, parse_term_err("(or true 1.2)"));
        assert_eq!(ParserError::TypeError, parse_term_err("(= 10 10.0)"));
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
