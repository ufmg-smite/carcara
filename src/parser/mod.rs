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
}

impl From<io::Error> for ParserError {
    fn from(e: io::Error) -> Self {
        ParserError::Io(e)
    }
}

pub struct Parser<R> {
    lexer: Lexer<R>,
    current_token: Token,
}

impl<R: BufRead> Parser<R> {
    pub fn new(input: R) -> Result<Self, ParserError> {
        let mut lexer = Lexer::new(input)?;
        let current_token = lexer.next_token()?;
        Ok(Parser {
            lexer,
            current_token,
        })
    }

    fn next_token(&mut self) -> Result<Token, ParserError> {
        let new = self.lexer.next_token()?;
        Ok(std::mem::replace(&mut self.current_token, new))
    }

    pub fn parse_term(&mut self) -> Result<Term, ParserError> {
        match self.next_token()? {
            Token::Numeral(n) => Ok(Term::Constant(Constant::Numeral(n))),
            Token::Decimal(r) => Ok(Term::Constant(Constant::Decimal(r))),
            Token::String(s) => Ok(Term::Constant(Constant::String(s))),
            Token::Symbol(s) => Ok(Term::Identifier(QualifiedIdentifier {
                identifier: Identifier::Simple(s),
                sort: None,
            })),
            _ => todo!(),
        }
    }
}
