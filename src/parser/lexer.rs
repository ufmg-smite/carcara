use num_rational::Ratio;
use std::io::{self, BufRead};

use super::ParserError;

#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    OpenParen,
    CloseParen,
    Symbol(String),
    Keyword(String),
    Numeral(u64),
    Decimal(Ratio<u64>),
    Eof,
}

pub struct Lexer<R> {
    input: R,
    current_line: Option<std::vec::IntoIter<char>>,
    current_char: Option<char>,
    position: (usize, usize),
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

    fn next_char(&mut self) -> Result<Option<char>, io::Error> {
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

    fn next_line(&mut self) -> Result<(), io::Error> {
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

    fn read_chars_while<P: Fn(char) -> bool>(&mut self, predicate: P) -> Result<String, io::Error> {
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

    fn consume_whitespace(&mut self) -> Result<(), io::Error> {
        self.read_chars_while(char::is_whitespace)?;
        Ok(())
    }

    pub fn next_token(&mut self) -> Result<Token, ParserError> {
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
            Some(':') => self.read_keyword(),
            Some('#') => self.read_number_with_base(),
            Some(c) if c.is_ascii_digit() => self.read_number(),
            Some(c) if Lexer::is_symbol_character(c) => self.read_simple_symbol(),
            Some(_) => todo!(),
            None => Ok(Token::Eof),
        }
    }

    fn read_simple_symbol(&mut self) -> Result<Token, ParserError> {
        let symbol = self.read_chars_while(Lexer::is_symbol_character)?;
        Ok(Token::Symbol(symbol))
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
            other => return Err(ParserError::UnexpectedChar {
                expected: &['b', 'x'],
                got: other,
            }),
        };
        let s = self.read_chars_while(|c| c.is_digit(base))?;
        Ok(Token::Numeral(u64::from_str_radix(&s, base).unwrap()))
    }

    fn read_number(&mut self) -> Result<Token, ParserError> {
        let int_part = self.read_chars_while(|c| c.is_ascii_digit())?;

        if int_part.len() > 1 && int_part.starts_with('0') {
            return Err(ParserError::LeadingZero(int_part));
        }

        if self.current_char == Some('.') {
            self.next_char()?;
            let frac_part = self.read_chars_while(|c| c.is_ascii_digit())?;
            let denom = 10u64.pow(frac_part.len() as u32);
            let numer = (int_part + &frac_part).parse::<u64>().unwrap();
            let r = Ratio::new(numer, denom);
            Ok(Token::Decimal(r))
        } else {
            Ok(Token::Numeral(int_part.parse().unwrap()))
        }
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

    fn lex_one(input: &str) -> Result<Token, ParserError> {
        let mut lex = Lexer::new(std::io::Cursor::new(input))?;
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
    }

    #[test]
    fn test_basic_tokens() {
        let input = "() foo123 :foo123 :a:b +-/*=%?!.$_~&^<>@";
        let expected = vec![
            Token::OpenParen,
            Token::CloseParen,
            Token::Symbol("foo123".into()),
            Token::Keyword("foo123".into()),
            Token::Keyword("a".into()),
            Token::Keyword("b".into()),
            Token::Symbol("+-/*=%?!.$_~&^<>@".into()),
        ];
        let got = lex_all(input);
        assert_eq!(expected, got);
    }

    #[test]
    fn test_number_parsing() {
        let input = "42 3.14159 #b101010 #x0ff";
        let expected = vec![
            Token::Numeral(42),
            Token::Decimal(Ratio::new(314159, 100_000)),
            Token::Numeral(42),
            Token::Numeral(255),
        ];
        let got = lex_all(input);
        assert_eq!(expected, got);

        assert!(matches!(lex_one("0123"), Err(ParserError::LeadingZero(_))));

        assert!(matches!(
            lex_one("#o123"),
            Err(ParserError::UnexpectedChar {
                expected: &['b', 'x'],
                got: Some('o'),
            })
        ));

        assert!(matches!(
            lex_one("#"),
            Err(ParserError::UnexpectedChar {
                expected: &['b', 'x'],
                got: None,
            })
        ));
    }
}
