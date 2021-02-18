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
            Token::OpenParen => self.parse_application(),
            _ => todo!(),
        }
    }

    fn parse_application(&mut self) -> Result<Term, ParserError> {
        match self.current_token {
            Token::ReservedWord(Reserved::As) => {
                Ok(Term::Identifier(self.parse_identifier_with_sort()?))
            }
            Token::ReservedWord(Reserved::Underscore) => {
                Ok(Term::Identifier(QualifiedIdentifier {
                    identifier: self.parse_indexed_identifier()?,
                    sort: None,
                }))
            }
            _ => todo!(),
        }
    }

    fn parse_qualified_identifier(&mut self) -> Result<QualifiedIdentifier, ParserError> {
        match self.next_token()? {
            Token::Symbol(s) => Ok(QualifiedIdentifier {
                identifier: Identifier::Simple(s),
                sort: None,
            }),
            Token::OpenParen => match self.current_token {
                Token::ReservedWord(Reserved::As) => self.parse_identifier_with_sort(),
                Token::ReservedWord(Reserved::Underscore) => Ok(QualifiedIdentifier {
                    identifier: self.parse_indexed_identifier()?,
                    sort: None,
                }),
                _ => todo!(),
            },
            _ => todo!(),
        }
    }

    fn parse_identifier_with_sort(&mut self) -> Result<QualifiedIdentifier, ParserError> {
        // TODO: parse qualified identifiers of the form "(as <identifier> <sort>)"
        todo!()
    }

    fn parse_identifier(&mut self) -> Result<Identifier, ParserError> {
        match self.next_token()? {
            Token::Symbol(s) => Ok(Identifier::Simple(s)),
            Token::OpenParen => self.parse_indexed_identifier(),
            _ => todo!(),
        }
    }

    fn parse_indexed_identifier(&mut self) -> Result<Identifier, ParserError> {
        self.next_token()?; // Consume "_" token
        let symbol = match self.next_token()? {
            Token::Symbol(s) => s,
            _ => todo!(),
        };
        let mut indexes = Vec::new();
        while self.current_token != Token::CloseParen {
            indexes.push(self.parse_index()?);
        }
        if indexes.is_empty() {
            todo!()
        }
        Ok(Identifier::Indexed(symbol, indexes))
    }

    fn parse_index(&mut self) -> Result<Index, ParserError> {
        match self.next_token()? {
            Token::Numeral(n) => Ok(Index::Numeral(n)),
            Token::Symbol(s) => Ok(Index::Symbol(s)),
            _ => todo!(),
        }
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
        assert_eq!(Term::Constant(Constant::Numeral(42)), parse_term("42"));
        assert_eq!(
            Term::Constant(Constant::Decimal(num_rational::Ratio::new(3, 2))),
            parse_term("1.5")
        );
        assert_eq!(
            Term::Constant(Constant::String("foo".into())),
            parse_term("\"foo\"")
        );
    }

    #[test]
    fn test_identifier_terms() {
        assert_eq!(
            Term::Identifier(QualifiedIdentifier {
                identifier: Identifier::Simple("foo".into()),
                sort: None,
            }),
            parse_term("foo")
        );

        let identifier = Identifier::Indexed(
            "bar".into(),
            vec![
                Index::Numeral(0),
                Index::Symbol("baz".into()),
                Index::Numeral(42),
            ],
        );
        assert_eq!(
            Term::Identifier(QualifiedIdentifier {
                identifier,
                sort: None,
            }),
            parse_term("(_ bar 0 baz 42)")
        );
    }
}
