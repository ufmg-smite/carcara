//! A lexer for the SMT-LIB and Alethe formats.

use crate::{
    CarcaraResult, Error,
    ast::impl_str_conversion_traits,
    parser::{ParserError, Source},
    utils::is_symbol_character,
};
use rug::{Integer, Rational, ops::Pow};
use std::{borrow::Cow, str::FromStr};

/// A token in the SMT-LIB and Alethe formats.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token<'a> {
    /// The `(` token.
    OpenParen,

    /// The `)` token.
    CloseParen,

    /// A symbol, that can be either simple or quoted.
    ///
    /// A simple symbol is a non-empty sequence of letters, digits, or any of these characters: `+`,
    /// `-`, `/`, `*`, `=`, `%`, `?`, `!`, `.`, `$`, `_`, `~`, `&`, `^`, `<`, `>`, or `@`. A quoted
    /// symbol is any sequence of characters that starts and ends with `|`, and does not contain `|`
    /// or `\`.
    Symbol(&'a str),

    /// A keyword, which is a simple symbol preceded by `:`. This has the leading `:` character
    /// removed.
    Keyword(&'a str),

    /// An integer numeral literal.
    Numeral(Integer),

    /// A decimal numeral literal.
    Decimal(Rational),

    /// A bitvector literal, represented by its integer value and width.
    Bitvector(Integer, u32),

    /// A string literal.
    String(Cow<'a, str>),

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

    /// The `declare-datatype` reserved word.
    DeclareDatatype,

    /// The `declare-datatypes` reserved word.
    DeclareDatatypes,

    /// The `par` reserved word.
    Par,

    /// The `define-fun` reserved word.
    DefineFun,

    /// The `define-fun-rec` reserved word.
    DefineFunRec,

    /// The `define-funs-rec` reserved word.
    DefineFunsRec,

    /// The `define-sort` reserved word.
    DefineSort,

    /// The `assert` reserved word.
    Assert,

    /// The `check-sat-assuming` reserved word.
    CheckSatAssuming,

    /// The `set-logic` reserved word.
    SetLogic,

    /// The `declare-rare-rule` reserved word.
    DeclareRareRule,
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
    DeclareDatatype: "declare-datatype",
    DeclareDatatypes: "declare-datatypes",
    Par: "par",
    DeclareConst: "declare-const",
    DeclareSort: "declare-sort",
    DefineFun: "define-fun",
    DefineFunRec: "define-fun-rec",
    DefineFunsRec: "define-funs-rec",
    DefineSort: "define-sort",
    Assert: "assert",
    CheckSatAssuming: "check-sat-assuming",
    SetLogic: "set-logic",
    DeclareRareRule: "declare-rare-rule"
});

/// Represents a position (line and column numbers) in the source input.
pub type Position = (usize, usize);

/// A lexer for the SMT-LIB, Alethe and Rare lexicons.
pub struct Lexer<'s> {
    pub source: Source<'s>,

    /// The remaining contents of the source, starting at the current character.
    rest: &'s str,
}

impl<'s> Lexer<'s> {
    /// Constructs a new `Lexer` that reads from `source`.
    pub fn new(source: Source<'s>) -> Self {
        Self { source, rest: source.contents }
    }

    /// Returns the byte offset of the current character in the source contents.
    fn offset(&self) -> usize {
        self.source.contents.len() - self.rest.len()
    }

    /// Wraps a `ParserError` into a crate level error, by adding the current position and the
    /// current source name.
    fn err(&self, inner: impl Into<ParserError>) -> Error {
        Error::Parser(
            inner.into(),
            self.offset_to_position(self.offset()),
            self.source.name.into(),
        )
    }

    /// Advances the lexer by one character, and returns the previous `current_char`.
    fn next_char(&mut self) -> Option<char> {
        let mut chars = self.rest.chars();
        let got = chars.next()?;
        self.rest = chars.as_str();
        Some(got)
    }

    /// Advances the lexer by one line, discarding the remaining contents of the current line.
    fn next_line(&mut self) {
        // Read characters until line end
        self.read_chars_while(|c| c != '\n');
        // Then read the \n char itself
        if self.current() == Some('\n') {
            self.next_char();
        }
    }

    /// Returns the current character.
    ///
    /// If the lexer is at the end of the input, returns `None`.
    fn current(&self) -> Option<char> {
        self.rest.chars().next()
    }

    /// Converts a byte offset into a `Position` in the source.
    ///
    /// This must scan the entire source contents upto the given offset, so should be avoided.
    pub fn offset_to_position(&self, offset: usize) -> Position {
        let before = &self.source.contents[..offset];
        let line_start = before.rfind('\n').map(|n| n + 1).unwrap_or_default();
        (before.matches('\n').count() + 1, offset - line_start + 1)
    }

    /// Reads characters while the given predicate returns `true`, and returns them as a slice of
    /// the source contents.
    ///
    /// At the end, all characters in the returned slice will satisfy the predicate, and
    /// `self.current()` will be the first character that didn't satisfy the predicate.
    fn read_chars_while<P: Fn(char) -> bool>(&mut self, predicate: P) -> &'s str {
        let mut len = self.rest.len();
        for (i, c) in self.rest.char_indices() {
            if !predicate(c) {
                len = i;
                break;
            }
        }
        let (read, rest) = self.rest.split_at(len);
        self.rest = rest;
        read
    }

    /// Reads and drops characters until a non-whitespace character is encountered.
    fn drop_while_whitespace(&mut self) {
        self.read_chars_while(char::is_whitespace);
    }

    /// Consumes all leading whitespace and comments in the input source.
    fn consume_whitespace(&mut self) {
        self.drop_while_whitespace();
        while self.current() == Some(';') {
            self.next_line();
            self.drop_while_whitespace();
        }
    }

    /// Reads a token from the input source.
    pub fn next_token(&mut self) -> CarcaraResult<(Token<'s>, usize)> {
        self.consume_whitespace();
        let start_offset = self.offset();
        let token = match self.current() {
            Some('(') => {
                self.next_char();
                Token::OpenParen
            }
            Some(')') => {
                self.next_char();
                Token::CloseParen
            }
            Some('"') => self.read_string()?,
            Some('|') => self.read_quoted_symbol()?,
            Some(':') => self.read_keyword(),
            Some('#') => self.read_bitvector()?,
            Some('-') => {
                // If we encounter the '-' character, the token can either be a GMP-style numerical
                // literal (e.g. '-5'), or a symbol that starts with '-' (e.g. the '-' operator
                // itself)
                self.next_char();
                if self.current().as_ref().is_some_and(char::is_ascii_digit) {
                    self.read_number(true)?
                } else {
                    // This assumes that the symbol is never a reserved a word.
                    self.read_chars_while(is_symbol_character);
                    let slice = &self.source.contents[start_offset..self.offset()];
                    Token::Symbol(slice)
                }
            }
            Some(c) if c.is_ascii_digit() => self.read_number(false)?,
            Some(c) if is_symbol_character(c) => self.read_simple_symbol(),
            None => Token::Eof,
            Some(other) => return Err(self.err(ParserError::UnexpectedChar(other))),
        };
        Ok((token, start_offset))
    }

    /// Reads a simple symbol from the input source.
    fn read_simple_symbol(&mut self) -> Token<'s> {
        let symbol = self.read_chars_while(is_symbol_character);
        if let Ok(reserved) = Reserved::from_str(symbol) {
            Token::ReservedWord(reserved)
        } else {
            Token::Symbol(symbol)
        }
    }

    /// Reads a quoted symbol from the input source.
    fn read_quoted_symbol(&mut self) -> CarcaraResult<Token<'s>> {
        self.next_char(); // Consume `|`
        let symbol = self.read_chars_while(|c| c != '|' && c != '\\');
        match self.current() {
            Some('\\') => Err(self.err(ParserError::BackslashInQuotedSymbol)),
            None => Err(self.err(ParserError::EofInQuotedSymbol)),
            Some('|') => {
                self.next_char();
                Ok(Token::Symbol(symbol))
            }
            _ => unreachable!(),
        }
    }

    /// Reads a keyword from the input source.
    fn read_keyword(&mut self) -> Token<'s> {
        self.next_char(); // Consume `:`
        let symbol = self.read_chars_while(is_symbol_character);
        Token::Keyword(symbol)
    }

    /// Reads a binary or hexadecimal bitvector literal, e.g. `#b0110` or `#x01Ab`.
    ///
    /// Returns an error if any character other than `b` or `x` is encountered after the `#`, or if
    /// no digits are provided.
    fn read_bitvector(&mut self) -> CarcaraResult<Token<'s>> {
        self.next_char(); // Consume `#`
        let (base, bits_per_char) = match self.next_char() {
            Some('b') => (2, 1),
            Some('x') => (16, 4),
            None => return Err(self.err(ParserError::EmptyBitvector)),
            Some(other) => return Err(self.err(ParserError::UnexpectedChar(other))),
        };
        let s = self.read_chars_while(|c| c.is_digit(base as u32));
        if s.is_empty() {
            return Err(self.err(ParserError::EmptyBitvector));
        }

        if let Some(width) = s
            .len()
            .checked_mul(bits_per_char)
            .and_then(|w| w.try_into().ok())
        {
            let value = Integer::from_str_radix(s, base).unwrap();
            Ok(Token::Bitvector(value, width))
        } else {
            let width = Integer::from(s.len()) * bits_per_char;
            Err(self.err(ParserError::InvalidBvWidth(width)))
        }
    }

    /// Reads an integer or decimal numerical literal.
    fn read_number(&mut self, negated: bool) -> CarcaraResult<Token<'s>> {
        let first_part = self.read_chars_while(|c| c.is_ascii_digit());

        if first_part.len() > 1 && first_part.starts_with('0') {
            return Err(self.err(ParserError::LeadingZero(first_part.to_owned())));
        }

        if let Some(delimiter @ ('/' | '.')) = self.current() {
            self.next_char();
            let second_part = self.read_chars_while(|c| c.is_ascii_digit());
            if let Some('/' | '.') = self.current() {
                // A number can have only one delimiter
                let e = ParserError::UnexpectedChar(self.current().unwrap());
                return Err(self.err(e));
            }
            let r = match delimiter {
                '/' => {
                    if second_part.is_empty() {
                        let e = ParserError::MissingDenominatorInLiteral(first_part.to_owned());
                        return Err(self.err(e));
                    }
                    let [numer, denom] =
                        [first_part, second_part].map(|s| s.parse::<Integer>().unwrap());
                    if denom.is_zero() {
                        let e = ParserError::DivisionByZeroInLiteral(format!("{numer}/{denom}"));
                        return Err(self.err(e));
                    }
                    Rational::from((numer, denom))
                }
                '.' => {
                    let denom = Integer::from(10u32).pow(second_part.len() as u32);
                    let numer = (first_part.to_owned() + second_part)
                        .parse::<Integer>()
                        .unwrap();
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
    fn read_string(&mut self) -> CarcaraResult<Token<'s>> {
        self.next_char(); // Consume `"`

        // First, we check for the easy case, where the string does not have any escape sequences,
        // and we can just return a string slice of the contents
        let first_chunk = self.read_chars_while(|c| c != '"' && c != '\\');
        let mut result = if self.current() == Some('"') {
            self.next_char();
            if self.current() == Some('"') {
                // handle the use of `""` to mean a single `"`
                self.next_char();
                format!("{first_chunk}\"")
            } else {
                return Ok(Token::String(Cow::Borrowed(first_chunk)));
            }
        } else {
            first_chunk.to_owned()
        };

        // If we didn't exit by now, we have either an escape sequence or an EOF in the string, so
        // we do the general case where we return `Cow::Owned`
        loop {
            let Some(c) = self.current() else {
                return Err(self.err(ParserError::EofInString));
            };
            if c == '"' {
                self.next_char();
                if self.current() == Some('"') {
                    result.push('"');
                    self.next_char();
                } else {
                    break;
                }
            } else if c == '\\' {
                self.next_char();
                if self.current() == Some('u') {
                    self.next_char();
                    self.read_unicode_escape_sequence(&mut result)?;
                } else {
                    result.push('\\');
                }
            } else {
                result.push(c);
                self.next_char();
            }
        }
        Ok(Token::String(Cow::Owned(result)))
    }

    /// Reads a unicode escape sequence encountered in a string literal, denoted by `\uXXXX` or
    /// `\u{...}`.
    fn read_unicode_escape_sequence(&mut self, result: &mut String) -> CarcaraResult<()> {
        // At this point, '\' and 'u' have already been read
        match self.current() {
            Some('{') => {
                self.next_char();
                // Read the contents inside the {} braces, up to five hex characters
                let mut contents = String::new();
                for _ in 0..5 {
                    let Some(c) = self.current() else {
                        return Err(self.err(ParserError::EofInString));
                    };
                    if c == '}' || !c.is_ascii_hexdigit() {
                        break;
                    }
                    contents.push(c);
                    self.next_char();
                }
                if self.current() == Some('}') {
                    self.next_char();
                } else {
                    // If the contents are not up to 5 hex digits followed by '}', this is not a
                    // well-formed unicode escape sequence, so we abort
                    result.push_str("\\u{");
                    result.push_str(&contents);
                    return Ok(());
                }
                if contents.is_empty() {
                    // Handle "\u{}" edge case
                    result.push_str("\\u{}");
                    return Ok(());
                }
                let code = u32::from_str_radix(&contents, 16).unwrap();

                // In the SMT-LIB unicode escape syntax, only the planes 0 to 2 of Unicode are
                // allowed, meaning values up to 0x2FFFF. For values beyond that, we treat the
                // escape sequence as a literal string.
                if code > 0x2FFFF {
                    result.push_str("\\u{");
                    result.push_str(&contents);
                    result.push('}');
                    return Ok(());
                }

                // While the previous check ensures that the codepoint is not out-of-bounds for
                // Unicode, it might still lie in the Unicode High Surrogate Area (0xD800 to
                // 0xDFFF), which is also considered invalid. Therefore `char::from_u32` may still
                // fail.
                let c = char::from_u32(code)
                    .ok_or_else(|| self.err(ParserError::InvalidUnicode(contents)))?;
                result.push(c);
                Ok(())
            }
            Some(_) => {
                let mut contents = String::new();
                for _ in 0..4 {
                    let Some(c) = self.current() else {
                        return Err(self.err(ParserError::EofInString));
                    };
                    if !c.is_ascii_hexdigit() {
                        break;
                    }
                    contents.push(c);
                    self.next_char();
                }
                if contents.len() != 4 {
                    // If the contents are not exactly 4 hex digits, this is not a well-formed
                    // unicode escape sequence, so we abort
                    result.push_str("\\u");
                    result.push_str(&contents);
                    return Ok(());
                }
                let code = u32::from_str_radix(&contents, 16).unwrap();
                let c = char::from_u32(code)
                    .ok_or_else(|| self.err(ParserError::InvalidUnicode(contents)))?;
                result.push(c);
                Ok(())
            }
            None => Err(self.err(ParserError::EofInString)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex_one<'s>(input: &'s str) -> CarcaraResult<Token<'s>> {
        Lexer::new(input.into()).next_token().map(|(tk, _)| tk)
    }

    fn lex_all(input: &str) -> Vec<Token<'_>> {
        let mut lex = Lexer::new(input.into());
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
            vec![Token::Symbol("symbol")]
        );
        assert_eq!(
            lex_all(";\n;\nsymbol ;\n symbol"),
            vec![Token::Symbol("symbol"), Token::Symbol("symbol")]
        );
    }

    #[test]
    fn test_simple_symbols_and_keywords() {
        let input = "foo123 :foo123 :a:b +-/*=%?!.$_~&^<>@ -starts-with-dash --double-dash";
        let expected = vec![
            Token::Symbol("foo123"),
            Token::Keyword("foo123"),
            Token::Keyword("a"),
            Token::Keyword("b"),
            Token::Symbol("+-/*=%?!.$_~&^<>@"),
            Token::Symbol("-starts-with-dash"),
            Token::Symbol("--double-dash"),
        ];
        assert_eq!(expected, lex_all(input));
    }

    #[test]
    fn test_quoted_symbols() {
        let input = "|abc| abc |:abc| || |\n\t |";
        let expected = vec![
            Token::Symbol("abc"),
            Token::Symbol("abc"),
            Token::Symbol(":abc"),
            Token::Symbol(""),
            Token::Symbol("\n\t "),
        ];
        assert_eq!(expected, lex_all(input));

        assert!(matches!(
            lex_one("|\\|"),
            Err(Error::Parser(ParserError::BackslashInQuotedSymbol, _, _))
        ));

        assert!(matches!(
            lex_one("|"),
            Err(Error::Parser(ParserError::EofInQuotedSymbol, _, _))
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
            Err(Error::Parser(ParserError::LeadingZero(_), _, _))
        ));
        assert!(matches!(
            lex_one("1.2.3"),
            Err(Error::Parser(ParserError::UnexpectedChar(_), _, _))
        ));
        assert!(matches!(
            lex_one("1/2.3"),
            Err(Error::Parser(ParserError::UnexpectedChar(_), _, _))
        ));
        assert!(matches!(
            lex_one("1.2/3"),
            Err(Error::Parser(ParserError::UnexpectedChar(_), _, _))
        ));
        assert!(matches!(
            lex_one("1/0"),
            Err(Error::Parser(ParserError::DivisionByZeroInLiteral(_), _, _))
        ));
        assert!(matches!(
            lex_one("5/"),
            Err(Error::Parser(
                ParserError::MissingDenominatorInLiteral(_),
                _,
                _
            ))
        ));
    }

    #[test]
    fn test_bitvectors() {
        let input = "#b101010 #xdeadbeef #b1 #x0";
        let expected = vec![
            Token::Bitvector(42.into(), 6),
            Token::Bitvector(0xdeadbeefu64.into(), 32),
            Token::Bitvector(1.into(), 1),
            Token::Bitvector(0.into(), 4),
        ];
        assert_eq!(expected, lex_all(input));

        assert!(matches!(
            lex_one("#o123"),
            Err(Error::Parser(ParserError::UnexpectedChar('o'), _, _)),
        ));

        assert!(matches!(
            lex_one("#"),
            Err(Error::Parser(ParserError::EmptyBitvector, _, _)),
        ));

        assert!(matches!(
            lex_one("#b"),
            Err(Error::Parser(ParserError::EmptyBitvector, _, _)),
        ));
    }

    #[test]
    fn test_strings() {
        let input = r#" "string" "escaped quote: """ """" """""" "\u0061" "\u{0061}" "#;
        let expected = vec![
            Token::String("string".into()),
            Token::String("escaped quote: \"".into()),
            Token::String("\"".into()),
            Token::String("\"\"".into()),
            Token::String("a".into()),
            Token::String("a".into()),
        ];
        assert_eq!(expected, lex_all(input));

        assert!(matches!(
            lex_one("\""),
            Err(Error::Parser(ParserError::EofInString, _, _))
        ));
        assert!(matches!(
            lex_one("\"\\u{de01}\""),
            Err(Error::Parser(ParserError::InvalidUnicode(_), _, _))
        ));
    }

    #[test]
    fn test_weird_unicode_escape_sequences() {
        let input = r#"
            "\u{61}" "\u{00061}" "\u{000061}" "\u00061" "\u61"
            "\u" "\u{12x4}" "\u{123" "\u{}" "\u{30000}" "#;
        let expected = [
            "a",
            "a",
            "\\u{000061}",
            "\u{0006}1",
            "\\u61",
            "\\u",
            "\\u{12x4}",
            "\\u{123",
            "\\u{}",
            "\\u{30000}",
        ]
        .map(Cow::Borrowed)
        .map(Token::String);
        assert_eq!(expected.as_slice(), lex_all(input));
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
            Token::Symbol("_"),
            Token::Symbol("!"),
            Token::Symbol("as"),
            Token::Symbol("let"),
            Token::Symbol("exists"),
        ];
        assert_eq!(expected, lex_all(input));
    }
}
