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
        let base_term = self.parse_sort(true)?;

        let attribute = match self.current_token.clone() {
            Token::CloseParen => {
                self.expect_token(Token::CloseParen)?;
                AttributeParameters::None
            }
            Token::Keyword(_) => {
                let kind_of_arg = self.expect_keyword()?;
                self.expect_token(Token::CloseParen)?;
                if kind_of_arg == "list" {
                    AttributeParameters::List
                } else {
                    return Err(Error::Parser(
                        ParserError::InvalidRareArgAttribute(kind_of_arg),
                        self.current_position,
                    ));
                }
            }
            token => {
                return Err(Error::Parser(
                    ParserError::UnexpectedToken(token),
                    self.current_position,
                ));
            }
        };

        let term = if attribute == AttributeParameters::List {
            self.pool.add(Term::Sort(Sort::RareList(base_term.clone())))
        } else {
            base_term.clone()
        };

        let binding_sort = if attribute == AttributeParameters::List {
            base_term.clone()
        } else {
            term.clone()
        };

        self.insert_sorted_var((name.clone(), binding_sort.clone()));
        self.state.sort_defs.insert(
            name.clone(),
            SortDef {
                body: binding_sort,
                params: Vec::default(),
            },
        );

        Ok((name, TypeParameter { term, attribute }))
    }

    fn parse_body(&mut self) -> CarcaraResult<Body> {
        let qualified_arg = self.expect_keyword()?;
        match qualified_arg.as_str() {
            "conclusion" => {
                let rewrite_term = self.parse_term()?;
                Ok(Body::Conclusion(rewrite_term))
            }
            "args" => {
                fn parse_args<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<Vec<String>> {
                    parser.expect_token(Token::OpenParen)?;
                    parser.parse_sequence(super::Parser::expect_symbol, false)
                }
                let args = parse_args(self)?;
                Ok(Body::Args(args))
            }
            "premises" => {
                self.expect_token(Token::OpenParen)?;
                let terms = self.parse_sequence(
                    |parser| {
                        let term = parser.parse_term()?;
                        Ok(term)
                    },
                    false,
                )?;
                Ok(Body::Premise(terms))
            }
            _ => Err(Error::Parser(
                ParserError::InvalidRareFunctionAttribute(qualified_arg),
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
            is_elaborated: false,
        })
    }

    pub(crate) fn parse_rare(&mut self) -> CarcaraResult<Rules> {
        let mut rules = vec![];
        while self.current_token != Token::Eof {
            rules.push(self.parse_rule()?);
        }

        Ok(RareStatements {
            rules: rules
                .iter()
                .map(|x| (x.name.clone(), (*x).clone()))
                .collect(),
        })
    }
}
