pub mod ast;
pub mod lexer;

use ast::*;
use lexer::*;
use std::io::{self, BufRead};

#[derive(Debug)]
pub enum ParserError {
    Io(io::Error),
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
}

impl From<io::Error> for ParserError {
    fn from(e: io::Error) -> Self {
        ParserError::Io(e)
    }
}

type ParserResult<T> = Result<T, ParserError>;

pub struct Parser<R> {
    lexer: Lexer<R>,
    current_token: Token,
}

impl<R: BufRead> Parser<R> {
    pub fn new(input: R) -> ParserResult<Self> {
        let mut lexer = Lexer::new(input)?;
        let current_token = lexer.next_token()?;
        Ok(Parser {
            lexer,
            current_token,
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
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_term(input: &str) -> Term {
        Parser::new(io::Cursor::new(input))
            .and_then(|mut p| p.parse_term())
            .expect("parser error during test")
    }

    #[test]
    fn test_constant_terms() {
        assert_eq!(Term::Terminal(Terminal::Integer(42)), parse_term("42"));
        assert_eq!(
            Term::Terminal(Terminal::Real(num_rational::Ratio::new(3, 2))),
            parse_term("1.5")
        );
        assert_eq!(
            Term::Terminal(Terminal::String("foo".into())),
            parse_term("\"foo\"")
        );
    }

    #[test]
    fn test_identifier_terms() {
        assert_eq!(
            Term::Terminal(Terminal::Var(Identifier::Simple("foo".into()))),
            parse_term("foo")
        );
    }
}
