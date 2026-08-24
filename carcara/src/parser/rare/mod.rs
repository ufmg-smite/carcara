use super::{Parser, ParserError, Reserved, SortDef, Token};
use crate::{
    ast::{rare_rules::*, *},
    CarcaraResult, Error,
};
use indexmap::IndexMap;

#[derive(Debug, Clone)]
enum Body {
    Conclusion(Rc<Term>),
    Premises(Vec<Rc<Term>>),
    Args(Vec<String>),
}

fn parse_parameter(parser: &mut Parser<'_, '_>) -> CarcaraResult<(String, TypeParameter)> {
    parser.expect_token(Token::OpenParen)?;
    let name = parser.expect_symbol()?;
    let base_sort = parser.parse_sort(true)?;

    let attribute = match &parser.current_token {
        Token::CloseParen => {
            parser.expect_token(Token::CloseParen)?;
            AttributeParameters::None
        }
        Token::Keyword(_) => {
            let attribute = parser.expect_keyword()?;
            parser.expect_token(Token::CloseParen)?;
            if attribute != "list" {
                return Err(Error::Parser(
                    ParserError::InvalidRareArgAttribute(attribute),
                    parser.current_position,
                ));
            }
            AttributeParameters::List
        }
        token => {
            return Err(Error::Parser(
                ParserError::UnexpectedToken(token.clone()),
                parser.current_position,
            ));
        }
    };

    let parameter_sort = if attribute == AttributeParameters::List {
        parser
            .pool
            .add(Term::Sort(Sort::RareList(base_sort.clone())))
    } else {
        base_sort.clone()
    };

    // A list parameter may also occur where a single element is expected, so bind its local
    // variable to the element sort while retaining the list sort in the rule metadata.
    parser.insert_sorted_var((name.clone(), base_sort.clone()));
    parser.state.sort_defs.insert(
        name.clone(),
        SortDef {
            body: base_sort.clone(),
            params: Vec::new(),
        },
    );

    // Accept both `T` and `@T` references for rare type parameters declared as `Type`.
    if matches!(base_sort.as_sort(), Some(Sort::Type)) {
        let alias = if let Some(stripped) = name.strip_prefix('@') {
            stripped.to_owned()
        } else {
            format!("@{name}")
        };
        parser
            .state
            .sort_defs
            .entry(alias)
            .or_insert_with(|| SortDef {
                body: parser.pool.add(Term::Sort(Sort::Type)),
                params: Vec::new(),
            });
    }

    Ok((name, TypeParameter { term: parameter_sort, attribute }))
}

fn parse_body(parser: &mut Parser<'_, '_>) -> CarcaraResult<Body> {
    let attribute = parser.expect_keyword()?;
    match attribute.as_str() {
        "conclusion" => Ok(Body::Conclusion(parser.parse_term()?)),
        "args" => {
            parser.expect_token(Token::OpenParen)?;
            Ok(Body::Args(
                parser.parse_sequence(Parser::expect_symbol, false)?,
            ))
        }
        "premises" => {
            parser.expect_token(Token::OpenParen)?;
            Ok(Body::Premises(
                parser.parse_sequence(Parser::parse_term, false)?,
            ))
        }
        _ => Err(Error::Parser(
            ParserError::InvalidRareFunctionAttribute(attribute),
            parser.current_position,
        )),
    }
}

#[derive(Default)]
struct BodyDefinition {
    args: Vec<String>,
    premises: Vec<Rc<Term>>,
    conclusion: Option<Rc<Term>>,
}

fn parse_rule(parser: &mut Parser<'_, '_>) -> CarcaraResult<RuleDefinition> {
    parser.expect_token(Token::ReservedWord(Reserved::DeclareRareRule))?;
    let name = parser.expect_symbol()?;

    parser.state.symbol_table.push_scope();
    let result = (|| {
        parser.expect_token(Token::OpenParen)?;
        let parameters = parser.parse_sequence(parse_parameter, false)?;

        let mut body = BodyDefinition::default();
        for item in parser.parse_sequence(parse_body, false)? {
            match item {
                Body::Conclusion(term) => body.conclusion = Some(term),
                Body::Premises(premises) => body.premises = premises,
                Body::Args(args) => body.args = args,
            }
        }

        let conclusion = body.conclusion.ok_or_else(|| {
            Error::Parser(
                ParserError::UndefinedRareConclusion(name.clone()),
                parser.current_position,
            )
        })?;
        if !matches!(
            conclusion.as_ref(),
            Term::Op(Operator::Equals, args) if args.len() == 2
        ) {
            return Err(Error::Parser(
                ParserError::InvalidRareConclusion(name.clone()),
                parser.current_position,
            ));
        }
        if body.premises.iter().any(|premise| {
            !matches!(
                premise.as_ref(),
                Term::Op(Operator::Equals | Operator::Distinct, args) if args.len() == 2
            )
        }) {
            return Err(Error::Parser(
                ParserError::InvalidRarePremise(name.clone()),
                parser.current_position,
            ));
        }

        let parameters: IndexMap<_, _> = parameters.into_iter().collect();
        if let Some(argument) = body
            .args
            .iter()
            .find(|argument| !parameters.contains_key(*argument))
        {
            return Err(Error::Parser(
                ParserError::UndeclaredRareArgument(name.clone(), argument.clone()),
                parser.current_position,
            ));
        }

        Ok(RuleDefinition {
            name,
            parameters,
            arguments: body.args,
            premises: body.premises,
            conclusion,
            is_elaborated: false,
        })
    })();
    parser.state.symbol_table.pop_scope();
    result
}

impl<'p, 's> Parser<'p, 's> {
    pub(crate) fn parse_rare(&mut self) -> CarcaraResult<Rules> {
        let mut rules = Vec::new();
        while self.current_token != Token::Eof {
            self.expect_token(Token::OpenParen)?;
            match self.current_token {
                Token::ReservedWord(Reserved::DeclareRareRule) => {
                    rules.push(parse_rule(self)?);
                }
                _ => {
                    return Err(Error::Parser(
                        ParserError::UnexpectedToken(self.current_token.clone()),
                        self.current_position,
                    ));
                }
            }
        }

        Ok(RareStatements {
            rules: rules
                .into_iter()
                .map(|rule| (rule.name.clone(), rule))
                .collect(),
        })
    }
}
