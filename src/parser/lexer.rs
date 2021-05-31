use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Num;

use std::{
    fmt::Debug,
    io::{self, BufRead},
    str::FromStr,
};

use super::error::*;

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

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Reserved {
    Underscore,  // _
    Bang,        // !
    As,          // as
    Let,         // let
    Exists,      // exists
    Forall,      // forall
    Match,       // match
    Choice,      // choice
    Cl,          // cl
    Assume,      // assume
    Step,        // step
    Anchor,      // anchor
    DeclareFun,  // declare-fun
    DeclareSort, // declare-sort
    DefineFun,   // define-fun
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
    DeclareSort: "declare-sort",
    DefineFun: "define-fun",
});

pub type Position = (usize, usize);

pub struct Lexer<R> {
    input: R,
    current_line: Option<std::vec::IntoIter<char>>,
    current_char: Option<char>,
    pub position: Position,
}

impl<R: BufRead> Lexer<R> {
    pub fn new(mut input: R) -> Result<Self, io::Error> {
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

    fn next_char(&mut self) -> Result<Option<char>, (io::Error, Position)> {
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

    fn next_line(&mut self) -> Result<(), (io::Error, Position)> {
        let mut buf = String::new();
        let read = self
            .input
            .read_line(&mut buf)
            .map_err(|io_err| (io_err, self.position))?;
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

    fn read_chars_while<P>(&mut self, predicate: P) -> Result<String, (io::Error, Position)>
    where
        P: Fn(char) -> bool,
    {
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

    fn consume_whitespace(&mut self) -> Result<(), (io::Error, Position)> {
        self.read_chars_while(char::is_whitespace)?;
        while self.current_char == Some(';') {
            self.next_line()?;
            self.next_char()?;
            self.read_chars_while(char::is_whitespace)?;
        }
        Ok(())
    }

    pub fn next_token(&mut self) -> ParserResult<Token> {
        self.consume_whitespace()?;
        match self.current_char {
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
            other => Err(ParserError(ErrorKind::UnexpectedChar(other), self.position)),
        }
    }

    fn read_simple_symbol(&mut self) -> Result<Token, ParserError> {
        let symbol = self.read_chars_while(Lexer::is_symbol_character)?;
        if let Ok(reserved) = Reserved::from_str(&symbol) {
            Ok(Token::ReservedWord(reserved))
        } else {
            Ok(Token::Symbol(symbol))
        }
    }

    fn read_quoted_symbol(&mut self) -> Result<Token, ParserError> {
        self.next_char()?; // Consume '|'
        let symbol = self.read_chars_while(|c| c != '|' && c != '\\')?;
        match self.current_char {
            Some('\\') => Err(ParserError(
                ErrorKind::BackslashInQuotedSymbol,
                self.position,
            )),
            None => Err(ParserError(ErrorKind::EofInQuotedSymbol, self.position)),
            Some('|') => {
                self.next_char()?;
                Ok(Token::Symbol(symbol))
            }
            _ => unreachable!(),
        }
    }

    fn read_keyword(&mut self) -> Result<Token, ParserError> {
        self.next_char()?; // Consume ':'
        let symbol = self.read_chars_while(Lexer::is_symbol_character)?;
        Ok(Token::Keyword(symbol))
    }

    fn read_number_with_base(&mut self) -> Result<Token, ParserError> {
        self.next_char()?; // Consume '#'
        let base = match self.next_char()? {
            Some('b') => 2,
            Some('x') => 16,
            other => return Err(ParserError(ErrorKind::UnexpectedChar(other), self.position)),
        };
        let s = self.read_chars_while(|c| c.is_digit(base))?;
        Ok(Token::Numeral(BigInt::from_str_radix(&s, base).unwrap()))
    }

    fn read_number(&mut self) -> Result<Token, ParserError> {
        let int_part = self.read_chars_while(|c| c.is_ascii_digit())?;

        if int_part.len() > 1 && int_part.starts_with('0') {
            return Err(ParserError(ErrorKind::LeadingZero(int_part), self.position));
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

    fn read_string(&mut self) -> Result<Token, ParserError> {
        self.next_char()?; // Consume '"'
        let mut result = String::new();
        loop {
            result += &self.read_chars_while(|c| c != '"')?;
            if self.current_char.is_none() {
                return Err(ParserError(ErrorKind::EofInString, self.position));
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

    fn lex_one(input: &str) -> ParserResult<Token> {
        let mut lex = Lexer::new(std::io::Cursor::new(input)).map_err(|err| (err, (0, 0)))?;
        lex.next_token()
    }

    fn lex_all(input: &str) -> Vec<Token> {
        let mut lex = Lexer::new(std::io::Cursor::new(input)).expect("lexer error during test");
        let mut result = Vec::new();
        loop {
            let tk = lex.next_token().expect("lexer error during test");
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
            Err(ParserError(ErrorKind::BackslashInQuotedSymbol, _))
        ));

        assert!(matches!(
            lex_one("|"),
            Err(ParserError(ErrorKind::EofInQuotedSymbol, _))
        ));
    }

    #[test]
    fn test_numerals_and_decimals() {
        let input = "42 3.14159 #b101010 #x0ff";
        let expected = vec![
            Token::Numeral(42.into()),
            Token::Decimal(BigRational::new(314159.into(), 100_000.into())),
            Token::Numeral(42.into()),
            Token::Numeral(255.into()),
        ];
        assert_eq!(expected, lex_all(input));

        assert!(matches!(
            lex_one("0123"),
            Err(ParserError(ErrorKind::LeadingZero(_), _))
        ));

        assert!(matches!(
            lex_one("#o123"),
            Err(ParserError(ErrorKind::UnexpectedChar(Some('o')), _)),
        ));

        assert!(matches!(
            lex_one("#"),
            Err(ParserError(ErrorKind::UnexpectedChar(None), _)),
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
            Err(ParserError(ErrorKind::EofInString, _))
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
