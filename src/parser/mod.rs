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

pub struct Parser<R> {
    lexer: Lexer<R>,
    current_token: Token,
    terms_map: HashMap<Term, Rc<Term>>,
    symbol_table: HashMap<Identifier, Sort>,
}

impl<R: BufRead> Parser<R> {
    pub fn new(input: R) -> ParserResult<Self> {
        let mut lexer = Lexer::new(input)?;
        let current_token = lexer.next_token()?;
        Ok(Parser {
            lexer,
            current_token,
            terms_map: HashMap::new(),
            symbol_table: Parser::new_symbol_table(),
        })
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
        match self.terms_map.entry(term.clone()) {
            Entry::Occupied(occupied_entry) => occupied_entry.get().clone(),
            Entry::Vacant(vacant_entry) => vacant_entry.insert(Rc::new(term)).clone(),
        }
    }

    fn get_sort(&self, term: &Term) -> Option<Sort> {
        match term {
            Term::Terminal(t) => match t {
                Terminal::Integer(_) => Some(Sort::int()),
                Terminal::Real(_) => Some(Sort::real()),
                Terminal::String(_) => Some(Sort::string()),
                Terminal::Var(iden) => self.symbol_table.get(iden).cloned(),
            },
            Term::Op(op, args) => match op {
                Operator::Add | Operator::Sub | Operator::Mult | Operator::Div => {
                    self.get_sort(args[0].as_ref())
                }
                Operator::Eq | Operator::Or | Operator::And | Operator::Not => Some(Sort::bool()),
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
                if (sorts[0] != Sort::int() && sorts[0] != Sort::real()) || sorts[0] != sorts[1] {
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
                if sorts.iter().any(|s| s != &Sort::bool()) {
                    return Err(ParserError::TypeError);
                }
            }
            Operator::Not => {
                Parser::expect_num_of_args(&args, 1)?;
                if sorts[0] != Sort::bool() {
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
            commands.push(self.parse_proof_command()?);
        }
        Ok(Proof(commands))
    }

    pub fn parse_proof_command(&mut self) -> ParserResult<ProofCommand> {
        self.expect_token(Token::OpenParen)?;
        match self.next_token()? {
            Token::ReservedWord(Reserved::Assume) => {
                let symbol = self.expect_symbol()?;
                let term = self.parse_term()?;
                let term = self.add_term(term);
                self.expect_token(Token::CloseParen)?;
                Ok(ProofCommand::Assume(symbol, term))
            }
            Token::ReservedWord(Reserved::Step) => {
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
            Token::ReservedWord(Reserved::Anchor) => todo!(),
            Token::ReservedWord(Reserved::DefineFun) => todo!(),
            other => Err(ParserError::UnexpectedToken(other)),
        }
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

    fn new_symbol_table() -> HashMap<Identifier, Sort> {
        let builtins = vec![("true", Sort::bool()), ("false", Sort::bool())];
        builtins
            .into_iter()
            .map(|(iden, sort)| (Identifier::Simple(iden.into()), sort))
            .collect()
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
        assert_eq!(parser.terms_map.len(), 6);
        let expected = [
            terminal!(int 1),
            terminal!(int 2),
            parse_term("(+ 1 2)"),
            parse_term("(/ (+ 1 2) (+ 1 2))"),
            parse_term("(- (+ 1 2) (/ (+ 1 2) (+ 1 2)))"),
            parse_term("(* 2 2)"),
        ];
        for e in &expected {
            assert!(parser.terms_map.contains_key(e))
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
