use super::{Parser, ParserError, Reserved, SortDef, Token};
use crate::ast::*;
use crate::CarcaraResult;
use crate::{ast::rare_rules::*, Error};
use std::io::BufRead;

#[derive(Debug, Clone)]
enum Body {
    Conclusion(Rc<Term>),
    Premise(Vec<Rc<Term>>),
    Args(Vec<String>),
}

struct BodyDefinition<'a> {
    args: &'a Vec<String>,
    premises: &'a Vec<Rc<Term>>,
    conclusion: Option<Rc<Term>>,
}

impl<'a, R: BufRead> Parser<'a, R> {
    fn parse_parameters(&mut self) -> CarcaraResult<(String, TypeParameter)> {
        self.expect_token(Token::OpenParen)?;
        let name = self.expect_symbol()?;
        let term = self.parse_sort(true)?;

        self.insert_sorted_var((name.clone(), term.clone()));
        self.state.sort_defs.insert(
            name.clone(),
            SortDef {
                body: term.clone(),
                params: Vec::default(),
            },
        );

        match self.current_token.clone() {
            Token::CloseParen => {
                self.expect_token(Token::CloseParen)?;
                Ok((
                    name,
                    TypeParameter {
                        term,
                        attribute: AttributeParameters::None,
                    },
                ))
            }
            Token::Keyword(_) => {
                let kind_of_arg = self.expect_keyword()?;
                self.expect_token(Token::CloseParen)?;
                if kind_of_arg == "list" {
                    Ok((
                        name,
                        TypeParameter {
                            term,
                            attribute: AttributeParameters::List,
                        },
                    ))
                } else {
                    Err(Error::Parser(
                        ParserError::InvalidRareArgAttribute(kind_of_arg),
                        self.current_position,
                    ))
                }
            }
            token => Err(Error::Parser(
                ParserError::UnexpectedToken(token),
                self.current_position,
            )),
        }
    }

    fn parse_body(&mut self) -> CarcaraResult<Body> {
        let qualified_arg: Vec<char> = self.expect_keyword()?.chars().collect();
        println!("Parsing rare body: {:?}", qualified_arg);
        match qualified_arg.as_slice() {
            ['c', 'o', 'n', 'c', 'l', 'u', 's', 'i', 'o', 'n', ..] => {
                let rewrite_term = self.parse_term()?;
                Ok(Body::Conclusion(rewrite_term))
            }
            ['a', 'r', 'g', 's', ..] => {
                self.expect_token(Token::OpenParen)?;
                let args = self.parse_sequence(Self::expect_symbol, false)?;
                Ok(Body::Args(args))
            }
            ['p', 'r', 'e', 'm', 'i', 's', 'e', 's', ..] => {
                self.expect_token(Token::OpenParen)?;
                let terms = self.parse_sequence(|parser| parser.parse_term(), false)?;
                Ok(Body::Premise(terms))
            }
            attribute => Err(Error::Parser(
                ParserError::InvalidRareFunctionAttribute(attribute.iter().collect()),
                self.current_position,
            )),
        }
    }

    fn parse_rule(&mut self) -> CarcaraResult<RuleDefinition> {
        self.expect_token(Token::OpenParen)?;
        self.expect_token(Token::ReservedWord(Reserved::DeclareRareRule))?;
        let name = self.expect_symbol()?;
        self.expect_token(Token::OpenParen)?;
        let parameters = self.parse_sequence(Self::parse_parameters, false)?;

        let body_definitions = BodyDefinition {
            args: &vec![],
            premises: &vec![],
            conclusion: None,
        };

        let body = self.parse_sequence(Self::parse_body, false)?;
        let body = body.iter().fold(body_definitions, |mut body, x| {
            match x {
                Body::Conclusion(term) => body.conclusion = Some((*term).clone()),
                Body::Premise(term) => body.premises = term,
                Body::Args(args) => body.args = args,
            }
            body
        });

        if body.conclusion.is_none() {
            return Err(Error::Parser(
                ParserError::UndefinedRareConclusion(name),
                self.current_position,
            ));
        }

        Ok(RuleDefinition {
            name,
            parameters: parameters.iter().cloned().collect(),
            arguments: body.args.clone(),
            premises: body.premises.clone(),
            conclusion: body.conclusion.unwrap(),
        })
    }

    pub(crate) fn parse_rare(&mut self) -> CarcaraResult<Rules> {
        let mut rules = vec![];
        while self.current_token != Token::Eof {
            rules.push(self.parse_rule()?);
        }

        Ok(rules
            .iter()
            .map(|x| (x.name.clone(), (*x).clone()))
            .collect())
    }
}
