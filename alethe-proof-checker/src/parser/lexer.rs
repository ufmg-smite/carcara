use super::error::ParserError;
use crate::{AletheResult, Error};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Num;
use std::{
    fmt,
    io::{self, BufRead},
    str::FromStr,
};

#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    OpenParen,
    CloseParen,
    Symbol(String),
    Keyword(String),
    Numeral(BigInt),
    Decimal(BigRational),
    String(String),
    ReservedWord(Reserved),
    Eof,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::OpenParen => write!(f, "("),
            Token::CloseParen => write!(f, ")"),
            Token::Symbol(s) => write!(f, "{}", s),
            Token::Keyword(k) => write!(f, ":{}", k),
            Token::Numeral(n) => write!(f, "{}", n),
            Token::Decimal(r) => write!(f, "{}", r),
            Token::String(s) => write!(f, "\"{}\"", s),
            Token::ReservedWord(r) => write!(f, "{}", r),
            Token::Eof => write!(f, "EOF"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reserved {
    Underscore,   // _
    Bang,         // !
    As,           // as
    Let,          // let
    Exists,       // exists
    Forall,       // forall
    Match,        // match
    Choice,       // choice
    Cl,           // cl
    Assume,       // assume
    Step,         // step
    Anchor,       // anchor
    DeclareFun,   // declare-fun
    DeclareConst, // declare-const
    DeclareSort,  // declare-sort
    DefineFun,    // define-fun
    Assert,       // assert
}

impl_str_conversion_traits!(Reserved {
    Underscore: "_",
    Bang: "!",
    As: "as",
    Let: "let",
    Exists: "exists",
    Forall: "forall",
    Match: "match",
    Choice: "choice",
    Cl: "cl",
    Assume: "assume",
    Step: "step",
    Anchor: "anchor",
    DeclareFun: "declare-fun",
    DeclareConst: "declare-const",
    DeclareSort: "declare-sort",
    DefineFun: "define-fun",
    Assert: "assert",
});

pub type Position = (usize, usize);

pub struct Lexer<R> {
    input: R,
    current_line: Option<std::vec::IntoIter<char>>,
    current_char: Option<char>,
    position: Position,
}

impl<R: BufRead> Lexer<R> {
    pub fn new(mut input: R) -> io::Result<Self> {
        let mut buf = String::new();
        let read = input.read_line(&mut buf)?;
        if read == 0 {
            Ok(Lexer {
                input,
                current_line: None,
                current_char: None,
                position: (0, 0),
            })
        } else {
            let mut line = buf.chars().collect::<Vec<_>>().into_iter();
            let current_char = line.next();
            Ok(Lexer {
                input,
                current_line: Some(line),
                current_char,
                position: (1, 1),
            })
        }
    }

    fn next_char(&mut self) -> io::Result<Option<char>> {
        // If there are no more characters in the current line, go to the next line
        if let Some(line) = &self.current_line {
            if line.as_slice().is_empty() {
                self.next_line()?;
            }
        }

        let new = if let Some(line) = &mut self.current_line {
            self.position.1 += 1;
            line.next()
        } else {
            None
        };
        let old = std::mem::replace(&mut self.current_char, new);
        Ok(old)
    }

    fn next_line(&mut self) -> io::Result<()> {
        let mut buf = String::new();
        let read = self.input.read_line(&mut buf)?;
        if read == 0 {
            self.current_line = None;
        } else {
            let line = buf.chars().collect::<Vec<_>>().into_iter();
            self.current_line = Some(line);
            self.position.0 += 1;
            self.position.1 = 0;
        }
        Ok(())
    }

    fn read_chars_while<P: Fn(char) -> bool>(&mut self, predicate: P) -> io::Result<String> {
        let mut result = String::new();
        while let Some(c) = self.current_char {
            if !predicate(c) {
                break;
            }
            result.push(c);
            self.next_char()?;
        }
        Ok(result)
    }

    /// Specialized function to drop whitespace characters. Similar to calling
    /// `self.read_chars_while(char::is_whitespace)`, but doesn't allocate a string to store the
    /// result.
    fn drop_while_whitespace(&mut self) -> io::Result<()> {
        while let Some(c) = self.current_char {
            if !c.is_whitespace() {
                break;
            }
            self.next_char()?;
        }
        Ok(())
    }

    fn consume_whitespace(&mut self) -> io::Result<()> {
        self.drop_while_whitespace()?;
        while self.current_char == Some(';') {
            self.next_line()?;
            self.next_char()?;
            self.drop_while_whitespace()?;
        }
        Ok(())
    }

    pub fn next_token(&mut self) -> AletheResult<(Token, Position)> {
        self.consume_whitespace()?;
        let start_position = self.position;
        let token = match self.current_char {
            Some('(') => {
                self.next_char()?;
                Ok(Token::OpenParen)
            }
            Some(')') => {
                self.next_char()?;
                Ok(Token::CloseParen)
            }
            Some('"') => self.read_string(),
            Some('|') => self.read_quoted_symbol(),
            Some(':') => self.read_keyword(),
            Some('#') => self.read_number_with_base(),
            Some(c) if c.is_ascii_digit() => self.read_number(),
            Some(c) if Lexer::is_symbol_character(c) => self.read_simple_symbol(),
            None => Ok(Token::Eof),
            Some(other) => Err(Error::Parser(
                ParserError::UnexpectedChar(other),
                self.position,
            )),
        }?;
        Ok((token, start_position))
    }

    fn read_simple_symbol(&mut self) -> AletheResult<Token> {
        let symbol = self.read_chars_while(Lexer::is_symbol_character)?;
        if let Ok(reserved) = Reserved::from_str(&symbol) {
            Ok(Token::ReservedWord(reserved))
        } else {
            Ok(Token::Symbol(symbol))
        }
    }

    fn read_quoted_symbol(&mut self) -> AletheResult<Token> {
        self.next_char()?; // Consume '|'
        let symbol = self.read_chars_while(|c| c != '|' && c != '\\')?;
        match self.current_char {
            Some('\\') => Err(Error::Parser(
                ParserError::BackslashInQuotedSymbol,
                self.position,
            )),
            None => Err(Error::Parser(ParserError::EofInQuotedSymbol, self.position)),
            Some('|') => {
                self.next_char()?;
                Ok(Token::Symbol(symbol))
            }
            _ => unreachable!(),
        }
    }

    fn read_keyword(&mut self) -> AletheResult<Token> {
        self.next_char()?; // Consume ':'
        let symbol = self.read_chars_while(Lexer::is_symbol_character)?;
        Ok(Token::Keyword(symbol))
    }

    fn read_number_with_base(&mut self) -> AletheResult<Token> {
        self.next_char()?; // Consume '#'
        let base = match self.next_char()? {
            Some('b') => 2,
            Some('x') => 16,
            None => return Err(Error::Parser(ParserError::EofInNumeral, self.position)),
            Some(other) => {
                return Err(Error::Parser(
                    ParserError::UnexpectedChar(other),
                    self.position,
                ))
            }
        };
        let s = self.read_chars_while(|c| c.is_digit(base))?;
        Ok(Token::Numeral(BigInt::from_str_radix(&s, base).unwrap()))
    }

    fn read_number(&mut self) -> AletheResult<Token> {
        let int_part = self.read_chars_while(|c| c.is_ascii_digit())?;

        if int_part.len() > 1 && int_part.starts_with('0') {
            return Err(Error::Parser(
                ParserError::LeadingZero(int_part),
                self.position,
            ));
        }

        if self.current_char == Some('.') {
            self.next_char()?;
            let frac_part = self.read_chars_while(|c| c.is_ascii_digit())?;
            let denom = BigInt::from(10).pow(frac_part.len() as u32);
            let numer = (int_part + &frac_part).parse::<BigInt>().unwrap();
            let r = BigRational::new(numer, denom);
            Ok(Token::Decimal(r))
        } else {
            Ok(Token::Numeral(int_part.parse().unwrap()))
        }
    }

    fn read_string(&mut self) -> AletheResult<Token> {
        self.next_char()?; // Consume '"'
        let mut result = String::new();
        loop {
            result += &self.read_chars_while(|c| c != '"')?;
            if self.current_char.is_none() {
                return Err(Error::Parser(ParserError::EofInString, self.position));
            }
            self.next_char()?; // Consume '"'
            if self.current_char == Some('"') {
                self.next_char()?;
                result.push('"');
            } else {
                break;
            }
        }
        Ok(Token::String(result))
    }
}

impl Lexer<()> {
    fn is_symbol_character(ch: char) -> bool {
        match ch {
            ch if ch.is_ascii_alphanumeric() => true,
            '+' | '-' | '/' | '*' | '=' | '%' | '?' | '!' | '.' | '$' | '_' | '~' | '&' | '^'
            | '<' | '>' | '@' => true,
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex_one(input: &str) -> AletheResult<Token> {
        let mut lex = Lexer::new(std::io::Cursor::new(input))?;
        lex.next_token().map(|(tk, _)| tk)
    }

    fn lex_all(input: &str) -> Vec<Token> {
        let mut lex = Lexer::new(std::io::Cursor::new(input)).expect("lexer error during test");
        let mut result = Vec::new();
        loop {
            let tk = lex.next_token().expect("lexer error during test").0;
            if tk == Token::Eof {
                break;
            }
            result.push(tk);
        }
        result
    }

    #[test]
    fn test_empty_input() {
        assert_eq!(lex_all(""), vec![]);
        assert_eq!(lex_all("   \n  \n\n "), vec![]);
        assert_eq!(lex_all("; comment\n"), vec![]);
    }

    #[test]
    fn test_comments() {
        assert_eq!(
            lex_all("; comment\n symbol\n ; comment"),
            vec![Token::Symbol("symbol".into())]
        );
        assert_eq!(
            lex_all(";\n;\nsymbol ;\n symbol"),
            vec![
                Token::Symbol("symbol".into()),
                Token::Symbol("symbol".into())
            ]
        );
    }

    #[test]
    fn test_simple_symbols_and_keywords() {
        let input = "foo123 :foo123 :a:b +-/*=%?!.$_~&^<>@";
        let expected = vec![
            Token::Symbol("foo123".into()),
            Token::Keyword("foo123".into()),
            Token::Keyword("a".into()),
            Token::Keyword("b".into()),
            Token::Symbol("+-/*=%?!.$_~&^<>@".into()),
        ];
        assert_eq!(expected, lex_all(input));
    }

    #[test]
    fn test_quoted_symbols() {
        let input = "|abc| abc |:abc| || |\n\t |";
        let expected = vec![
            Token::Symbol("abc".into()),
            Token::Symbol("abc".into()),
            Token::Symbol(":abc".into()),
            Token::Symbol("".into()),
            Token::Symbol("\n\t ".into()),
        ];
        assert_eq!(expected, lex_all(input));

        assert!(matches!(
            lex_one("|\\|"),
            Err(Error::Parser(ParserError::BackslashInQuotedSymbol, _))
        ));

        assert!(matches!(
            lex_one("|"),
            Err(Error::Parser(ParserError::EofInQuotedSymbol, _))
        ));
    }

    #[test]
    fn test_numerals_and_decimals() {
        let input = "42 3.14159 #b101010 #x0ff";
        let expected = vec![
            Token::Numeral(42.into()),
            Token::Decimal(BigRational::new(314_159.into(), 100_000.into())),
            Token::Numeral(42.into()),
            Token::Numeral(255.into()),
        ];
        assert_eq!(expected, lex_all(input));

        assert!(matches!(
            lex_one("0123"),
            Err(Error::Parser(ParserError::LeadingZero(_), _))
        ));

        assert!(matches!(
            lex_one("#o123"),
            Err(Error::Parser(ParserError::UnexpectedChar('o'), _)),
        ));

        assert!(matches!(
            lex_one("#"),
            Err(Error::Parser(ParserError::EofInNumeral, _)),
        ));
    }

    #[test]
    fn test_strings() {
        let input = r#" "string" "escaped quote: """ """" """""" "#;
        let expected = vec![
            Token::String("string".into()),
            Token::String("escaped quote: \"".into()),
            Token::String("\"".into()),
            Token::String("\"\"".into()),
        ];
        assert_eq!(expected, lex_all(input));

        assert!(matches!(
            lex_one("\""),
            Err(Error::Parser(ParserError::EofInString, _))
        ));
    }

    #[test]
    fn test_reserved_words() {
        let input = "_ ! as let exists |_| |!| |as| |let| |exists|";
        let expected = vec![
            Token::ReservedWord(Reserved::Underscore),
            Token::ReservedWord(Reserved::Bang),
            Token::ReservedWord(Reserved::As),
            Token::ReservedWord(Reserved::Let),
            Token::ReservedWord(Reserved::Exists),
            Token::Symbol("_".into()),
            Token::Symbol("!".into()),
            Token::Symbol("as".into()),
            Token::Symbol("let".into()),
            Token::Symbol("exists".into()),
        ];
        assert_eq!(expected, lex_all(input));
    }
}
