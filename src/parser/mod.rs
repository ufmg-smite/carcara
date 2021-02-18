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
            Token::Numeral(n) => Ok(Term::Constant(Constant::Numeral(n))),
            Token::Decimal(r) => Ok(Term::Constant(Constant::Decimal(r))),
            Token::String(s) => Ok(Term::Constant(Constant::String(s))),
            Token::Symbol(s) => Ok(Term::Identifier(QualifiedIdentifier {
                identifier: Identifier::Simple(s),
                sort: None,
            })),
            Token::OpenParen => self.parse_application(),
            other => Err(ParserError::UnexpectedToken(other)),
        }
    }

    fn parse_application(&mut self) -> ParserResult<Term> {
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

    fn parse_qualified_identifier(&mut self) -> ParserResult<QualifiedIdentifier> {
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
                _ => Err(ParserError::UnexpectedToken(self.next_token()?)),
            },
            other => Err(ParserError::UnexpectedToken(other)),
        }
    }

    fn parse_identifier_with_sort(&mut self) -> ParserResult<QualifiedIdentifier> {
        // TODO: parse qualified identifiers of the form "(as <identifier> <sort>)"
        todo!()
    }

    fn parse_identifier(&mut self) -> ParserResult<Identifier> {
        match self.next_token()? {
            Token::Symbol(s) => Ok(Identifier::Simple(s)),
            Token::OpenParen => self.parse_indexed_identifier(),
            other => Err(ParserError::UnexpectedToken(other)),
        }
    }

    fn parse_indexed_identifier(&mut self) -> ParserResult<Identifier> {
        self.next_token()?; // Consume "_" token
        let symbol = self.expect_symbol()?;
        let indexes = self.parse_sequence(Parser::<R>::parse_index, true)?;
        Ok(Identifier::Indexed(symbol, indexes))
    }

    fn parse_index(&mut self) -> ParserResult<Index> {
        match self.next_token()? {
            Token::Numeral(n) => Ok(Index::Numeral(n)),
            Token::Symbol(s) => Ok(Index::Symbol(s)),
            other => Err(ParserError::UnexpectedToken(other)),
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
