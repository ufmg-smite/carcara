//! A lexer for the SMT-LIB and Alethe formats.

use crate::{parser::ParserError, utils::is_symbol_character, CarcaraResult, Error};
use rug::{ops::Pow, Integer, Rational};
use std::{
    io::{self, BufRead},
    str::FromStr,
};

/// A token in the SMT-LIB and Alethe formats.
#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    /// The `(` token.
    OpenParen,

    /// The `)` token.
    CloseParen,

    /// A symbol, that can be either simple or quoted. A simple symbol is a non-empty sequence of
    /// letters, digits, or any of these characters: `+`, `-`, `/`, `*`, `=`, `%`, `?`, `!`, `.`,
    /// `$`, `_`, `~`, `&`, `^`, `<`, `>`, or `@`. A quoted symbol is any sequence of characters
    /// that starts and ends with `|`, and does not contain `|` or `\`.
    Symbol(String),

    /// A keyword, which is a simple symbol preceded by `:`. This has the leading `:` character
    /// removed.
    Keyword(String),

    /// An integer numeral literal.
    Numeral(Integer),

    /// A decimal numeral literal.
    Decimal(Rational),

    /// A bitvector literal.
    Bitvector { value: Integer, width: u64 },

    /// A string literal.
    String(String),

    /// A reserved word.
    ReservedWord(Reserved),

    /// A signal token to indicate the end of the input.
    Eof,
}

/// A reserved word in the SMT-LIB and Alethe lexicon.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reserved {
    /// The `_` reserved word.
    Underscore,

    /// The `!` reserved word.
    Bang,

    /// The `as` reserved word.
    As,

    /// The `let` reserved word.
    Let,

    /// The `exists` reserved word.
    Exists,

    /// The `forall` reserved word.
    Forall,

    /// The `match` reserved word.
    Match,

    /// The `choice` reserved word.
    Choice,

    /// The `lambda` reserved word.
    Lambda,

    /// The `cl` reserved word.
    Cl,

    /// The `assume` reserved word.
    Assume,

    /// The `step` reserved word.
    Step,

    /// The `anchor` reserved word.
    Anchor,

    /// The `declare-fun` reserved word.
    DeclareFun,

    /// The `declare-const` reserved word.
    DeclareConst,

    /// The `declare-sort` reserved word.
    DeclareSort,

    /// The `define-fun` reserved word.
    DefineFun,

    /// The `define-sort` reserved word.
    DefineSort,

    /// The `assert` reserved word.
    Assert,

    /// The `check-sat-assuming` reserved word.
    CheckSatAssuming,

    /// The `set-logic` reserved word.
    SetLogic,
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
    Lambda: "lambda",
    Cl: "cl",
    Assume: "assume",
    Step: "step",
    Anchor: "anchor",
    DeclareFun: "declare-fun",
    DeclareConst: "declare-const",
    DeclareSort: "declare-sort",
    DefineFun: "define-fun",
    DefineSort: "define-sort",
    Assert: "assert",
    CheckSatAssuming: "check-sat-assuming",
    SetLogic: "set-logic",
});

/// Represents a position (line and column numbers) in the source input.
pub type Position = (usize, usize);

/// A lexer for the SMT-LIB and Alethe formats.
pub struct Lexer<R> {
    input: R,
    current_line: Option<std::vec::IntoIter<char>>,
    current_char: Option<char>,
    position: Position,
}

impl<R: BufRead> Lexer<R> {
    /// Constructs a new `Lexer` from a type that implements `BufRead`.
    ///
    /// This operation can fail if there is an IO error on the first token.
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

    /// Advances the lexer by one character, and returns the previous `current_char`.
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

    /// Advances the lexer by one line, discarding the remaining contents of the current line.
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

    /// Reads characters while the given predicate returns `true`, and stores them in a `String`.
    ///
    /// At the end, all characters in the returned string will satisfy the predicate, and
    /// `self.current_char` will be the first character that didn't satisfy the predicate.
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

    /// Reads and drops characters until a non-whitespace character is encountered.
    ///
    /// This is similar to calling `self.read_chars_while(char::is_whitespace)`, but this method
    /// doesn't allocate a string to store the result.
    fn drop_while_whitespace(&mut self) -> io::Result<()> {
        while let Some(c) = self.current_char {
            if !c.is_whitespace() {
                break;
            }
            self.next_char()?;
        }
        Ok(())
    }

    /// Consumes all leading whitespace and comments in the input source.
    fn consume_whitespace(&mut self) -> io::Result<()> {
        self.drop_while_whitespace()?;
        while self.current_char == Some(';') {
            self.next_line()?;
            self.next_char()?;
            self.drop_while_whitespace()?;
        }
        Ok(())
    }

    /// Reads a token from the input source.
    pub fn next_token(&mut self) -> CarcaraResult<(Token, Position)> {
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
            Some('#') => self.read_bitvector(),
            Some('-') => {
                // If we encounter the '-' character, the token can either be a GMP-style numerical
                // literal (e.g. '-5'), or a symbol that starts with '-' (e.g. the '-' operator
                // itself)
                self.next_char()?;
                if self.current_char.as_ref().is_some_and(char::is_ascii_digit) {
                    self.read_number(true)
                } else {
                    // This assumes that the symbol is never a reserved a word.
                    let mut symbol = self.read_chars_while(is_symbol_character)?;
                    symbol.insert(0, '-');
                    Ok(Token::Symbol(symbol))
                }
            }
            Some(c) if c.is_ascii_digit() => self.read_number(false),
            Some(c) if is_symbol_character(c) => self.read_simple_symbol(),
            None => Ok(Token::Eof),
            Some(other) => Err(Error::Parser(
                ParserError::UnexpectedChar(other),
                self.position,
            )),
        }?;
        Ok((token, start_position))
    }

    /// Reads a simple symbol from the input source.
    fn read_simple_symbol(&mut self) -> CarcaraResult<Token> {
        let symbol = self.read_chars_while(is_symbol_character)?;
        if let Ok(reserved) = Reserved::from_str(&symbol) {
            Ok(Token::ReservedWord(reserved))
        } else {
            Ok(Token::Symbol(symbol))
        }
    }

    /// Reads a quoted symbol from the input source.
    fn read_quoted_symbol(&mut self) -> CarcaraResult<Token> {
        self.next_char()?; // Consume `|`
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

    /// Reads a keyword from the input source.
    fn read_keyword(&mut self) -> CarcaraResult<Token> {
        self.next_char()?; // Consume `:`
        let symbol = self.read_chars_while(is_symbol_character)?;
        Ok(Token::Keyword(symbol))
    }

    /// Reads a binary or hexadecimal bitvector literal, e.g. `#b0110` or `#x01Ab`.
    ///
    /// Returns an error if any character other than `b` or `x` is encountered after the `#`, or if
    /// no digits are provided.
    fn read_bitvector(&mut self) -> CarcaraResult<Token> {
        self.next_char()?; // Consume `#`
        let (base, bits_per_char) = match self.next_char()? {
            Some('b') => (2, 1),
            Some('x') => (16, 4),
            None => return Err(Error::Parser(ParserError::EmptyBitvector, self.position)),
            Some(other) => {
                return Err(Error::Parser(
                    ParserError::UnexpectedChar(other),
                    self.position,
                ))
            }
        };
        let s = self.read_chars_while(|c| c.is_digit(base as u32))?;
        if s.is_empty() {
            return Err(Error::Parser(ParserError::EmptyBitvector, self.position));
        }

        let width = s.len() as u64 * bits_per_char;
        let value = Integer::from_str_radix(&s, base).unwrap();
        Ok(Token::Bitvector { value, width })
    }

    /// Reads an integer or decimal numerical literal.
    fn read_number(&mut self, negated: bool) -> CarcaraResult<Token> {
        let first_part = self.read_chars_while(|c| c.is_ascii_digit())?;

        if first_part.len() > 1 && first_part.starts_with('0') {
            return Err(Error::Parser(
                ParserError::LeadingZero(first_part),
                self.position,
            ));
        }

        if let Some(delimiter @ ('/' | '.')) = self.current_char {
            self.next_char()?;
            let second_part = self.read_chars_while(|c| c.is_ascii_digit())?;
            if let Some('/' | '.') = self.current_char {
                // A number can have only one delimiter
                let e = ParserError::UnexpectedChar(self.current_char.unwrap());
                return Err(Error::Parser(e, self.position));
            }
            let r = match delimiter {
                '/' => {
                    let [numer, denom] =
                        [first_part, second_part].map(|s| s.parse::<Integer>().unwrap());
                    if denom.is_zero() {
                        let e = ParserError::DivisionByZeroInLiteral(format!("{numer}/{denom}"));
                        return Err(Error::Parser(e, self.position));
                    }
                    Rational::from((numer, denom))
                }
                '.' => {
                    let denom = Integer::from(10u32).pow(second_part.len() as u32);
                    let numer = (first_part + &second_part).parse::<Integer>().unwrap();
                    Rational::from((numer, denom))
                }
                _ => unreachable!(),
            };
            Ok(Token::Decimal(if negated { -r } else { r }))
        } else {
            let i: Integer = first_part.parse().unwrap();
            Ok(Token::Numeral(if negated { -i } else { i }))
        }
    }

    /// Reads a string literal from the input source.
    fn read_string(&mut self) -> CarcaraResult<Token> {
        self.next_char()?; // Consume `"`
        let mut result = String::new();
        loop {
            result += &self.read_chars_while(|c| c != '"')?;
            if self.current_char.is_none() {
                return Err(Error::Parser(ParserError::EofInString, self.position));
            }
            self.next_char()?; // Consume `"`
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

#[cfg(test)]
mod tests {
    use super::*;

    fn lex_one(input: &str) -> CarcaraResult<Token> {
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
        let input = "foo123 :foo123 :a:b +-/*=%?!.$_~&^<>@ -starts-with-dash --double-dash";
        let expected = vec![
            Token::Symbol("foo123".into()),
            Token::Keyword("foo123".into()),
            Token::Keyword("a".into()),
            Token::Keyword("b".into()),
            Token::Symbol("+-/*=%?!.$_~&^<>@".into()),
            Token::Symbol("-starts-with-dash".into()),
            Token::Symbol("--double-dash".into()),
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
        let input = "42 3.14159 -137 8/3 -5/2 1/1 0/2";
        let expected = vec![
            Token::Numeral(42.into()),
            Token::Decimal((314_159, 100_000).into()),
            Token::Numeral((-137).into()),
            Token::Decimal((8, 3).into()),
            Token::Decimal((-5, 2).into()),
            Token::Decimal(1.into()),
            Token::Decimal(0.into()),
        ];
        assert_eq!(expected, lex_all(input));

        assert!(matches!(
            lex_one("0123"),
            Err(Error::Parser(ParserError::LeadingZero(_), _))
        ));
        assert!(matches!(
            lex_one("1.2.3"),
            Err(Error::Parser(ParserError::UnexpectedChar(_), _))
        ));
        assert!(matches!(
            lex_one("1/2.3"),
            Err(Error::Parser(ParserError::UnexpectedChar(_), _))
        ));
        assert!(matches!(
            lex_one("1.2/3"),
            Err(Error::Parser(ParserError::UnexpectedChar(_), _))
        ));
        assert!(matches!(
            lex_one("1/0"),
            Err(Error::Parser(ParserError::DivisionByZeroInLiteral(_), _))
        ));
    }

    #[test]
    fn test_bitvectors() {
        let input = "#b101010 #xdeadbeef #b1 #x0";
        let expected = vec![
            Token::Bitvector { value: 42.into(), width: 6 },
            Token::Bitvector {
                value: 0xdeadbeefu64.into(),
                width: 32,
            },
            Token::Bitvector { value: 1.into(), width: 1 },
            Token::Bitvector { value: 0.into(), width: 4 },
        ];
        assert_eq!(expected, lex_all(input));

        assert!(matches!(
            lex_one("#o123"),
            Err(Error::Parser(ParserError::UnexpectedChar('o'), _)),
        ));

        assert!(matches!(
            lex_one("#"),
            Err(Error::Parser(ParserError::EmptyBitvector, _)),
        ));

        assert!(matches!(
            lex_one("#b"),
            Err(Error::Parser(ParserError::EmptyBitvector, _)),
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
