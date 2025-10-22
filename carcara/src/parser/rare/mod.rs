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

fn parse_parameters<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<(String, TypeParameter)> {
    parser.expect_token(Token::OpenParen)?;
    let name = parser.expect_symbol()?;
    let term = parser.parse_sort(true)?;

    parser.insert_sorted_var((name.clone(), term.clone()));
    parser.state.sort_defs.insert(
        name.clone(),
        SortDef {
            body: term.clone(),
            params: Vec::default(),
        },
    );
    let current_token = &parser.current_token;
    match current_token {
        Token::CloseParen => {
            parser.expect_token(Token::CloseParen)?;
            Ok((
                name,
                TypeParameter {
                    term,
                    attribute: AttributeParameters::None,
                },
            ))
        }
        Token::Keyword(_) => {
            let kind_of_arg = parser.expect_keyword()?;
            parser.expect_token(Token::CloseParen)?;
            if kind_of_arg == "list" {
                return Ok((
                    name,
                    TypeParameter {
                        term,
                        attribute: AttributeParameters::List,
                    },
                ));
            }
            Err(Error::Parser(
                ParserError::InvalidRareArgAttribute(kind_of_arg),
                parser.current_position,
            ))
        }
        _ => Err(Error::Parser(
            ParserError::UnexpectedToken(current_token.clone()),
            parser.current_position,
        )),
    }
}

fn parse_body<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<Body> {
    let qualified_arg: Vec<char> = parser.expect_keyword()?.chars().collect();
    match qualified_arg.as_slice() {
        ['c', 'o', 'n', 'c', 'l', 'u', 's', 'i', 'o', 'n', ..] => {
            let rewrite_term = parser.parse_term()?;
            Ok(Body::Conclusion(rewrite_term))
        }
        ['a', 'r', 'g', 's', ..] => {
            fn parse_args<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<Vec<String>> {
                parser.expect_token(Token::OpenParen)?;
                parser.parse_sequence(super::Parser::expect_symbol, false)
            }
            let args = parse_args(parser)?;
            Ok(Body::Args(args))
        }
        ['p', 'r', 'e', 'm', 'i', 's', 'e', 's', ..] => {
            parser.expect_token(Token::OpenParen)?;
            let terms = parser.parse_sequence(
                |parser| {
                    let term = parser.parse_term()?;
                    Ok(term)
                },
                false,
            )?;
            Ok(Body::Premise(terms))
        }
        attribute => Err(Error::Parser(
            ParserError::InvalidRareFunctionAttribute(attribute.iter().collect()),
            parser.current_position,
        )),
    }
}

struct BodyDefinition<'a> {
    args: &'a Vec<String>,
    premises: &'a Vec<Rc<Term>>,
    conclusion: Option<Rc<Term>>,
}

pub fn parse_rule<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<RuleDefinition> {
    parser.expect_token(Token::OpenParen)?;
    parser.expect_token(Token::ReservedWord(Reserved::DeclareRareRule))?;
    let name = parser.expect_symbol()?;
    parser.expect_token(Token::OpenParen)?;
    let parameters = parser.parse_sequence(|parser| parse_parameters(parser), false)?;

    let body_definitions = BodyDefinition {
        args: &vec![],
        premises: &vec![],
        conclusion: None,
    };

    let body = parser.parse_sequence(|parser| parse_body(parser), false)?;
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
            parser.current_position,
        ));
    }

    return Ok(RuleDefinition {
        name,
        parameters: parameters.iter().cloned().collect(),
        arguments: body.args.clone(),
        premises: body.premises.clone(),
        conclusion: body.conclusion.unwrap(),
    });
}

pub fn parse_rare<'a, 'b, R: BufRead>(parser: &mut Parser<'a, R>) -> CarcaraResult<Rules>
where
    'a: 'b,
{
    let mut rules = vec![];
    let mut current = &parser.current_token;
    while *current != Token::Eof {
        rules.push(parse_rule(parser)?);
        current = &parser.current_token;
    }

    return Ok(rules
        .iter()
        .map(|x| (x.name.clone(), (*x).clone()))
        .collect());
}
