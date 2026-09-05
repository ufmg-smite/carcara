use super::{Parser, ParserError, Reserved, Token};
use crate::{
    CarcaraResult,
    ast::{rare_rules::*, *},
};
use indexmap::IndexMap;

#[derive(Debug, Clone)]
enum Body {
    Conclusion(Rc<Term>),
    Premises(Vec<Rc<Term>>),
    Args(Vec<String>),
}

#[derive(Default)]
struct BodyDefinition {
    args: Vec<String>,
    premises: Vec<Rc<Term>>,
    conclusion: Option<Rc<Term>>,
}

impl<'p, 's> Parser<'p, 's> {
    fn parse_rare_parameter(&mut self) -> CarcaraResult<(String, TypeParameter)> {
        self.expect_token(Token::OpenParen)?;
        let name = self.expect_symbol()?;
        let sort = self.parse_sort()?;

        let attribute = if let Token::Keyword(_) = self.current_token {
            let attribute = self.expect_keyword()?;
            if attribute == "list" {
                AttributeParameters::List
            } else {
                return Err(self.err(
                    ParserError::InvalidRareArgAttribute(attribute),
                    self.current_position,
                ));
            }
        } else {
            AttributeParameters::None
        };
        self.expect_token(Token::CloseParen)?;

        // A list parameter may occur where an individual element is expected, so its local
        // binding retains the element sort. The `:list` attribute is kept in the rule metadata.
        self.declare_symbol(name.clone(), sort.clone());

        // Accept both `T` and `@T` references for RARE type parameters declared as `Type`.
        if matches!(sort.as_ref(), Sort::Type) {
            let alias = if let Some(stripped) = name.strip_prefix('@') {
                stripped.to_owned()
            } else {
                format!("@{name}")
            };
            self.declare_symbol(alias, sort.clone());
        }

        Ok((name, TypeParameter { sort, attribute }))
    }

    fn parse_rare_body(&mut self) -> CarcaraResult<Body> {
        let attribute = self.expect_keyword()?;
        match attribute.as_str() {
            "conclusion" => Ok(Body::Conclusion(self.parse_term()?)),
            "args" => {
                self.expect_token(Token::OpenParen)?;
                Ok(Body::Args(
                    self.parse_sequence(Parser::expect_symbol, false)?,
                ))
            }
            "premises" => {
                self.expect_token(Token::OpenParen)?;
                Ok(Body::Premises(
                    self.parse_sequence(Parser::parse_term, false)?,
                ))
            }
            _ => Err(self.err(
                ParserError::InvalidRareRuleAttribute(attribute),
                self.current_position,
            )),
        }
    }

    fn parse_rare_rule(&mut self) -> CarcaraResult<RuleDefinition> {
        self.expect_token(Token::OpenParen)?;
        self.expect_token(Token::ReservedWord(Reserved::DeclareRareRule))?;
        let name = self.expect_symbol()?;

        self.state.symbol_table.push_scope();
        let result = (|| {
            self.expect_token(Token::OpenParen)?;
            let parameters = self.parse_sequence(Parser::parse_rare_parameter, false)?;

            let mut body = BodyDefinition::default();
            for item in self.parse_sequence(Parser::parse_rare_body, false)? {
                match item {
                    Body::Conclusion(term) => body.conclusion = Some(term),
                    Body::Premises(premises) => body.premises = premises,
                    Body::Args(args) => body.args = args,
                }
            }

            let conclusion = body.conclusion.ok_or_else(|| {
                self.err(
                    ParserError::UndefinedRareConclusion(name.clone()),
                    self.current_position,
                )
            })?;
            if !matches!(
                conclusion.as_ref(),
                Term::Op(Operator::Equals, args) if args.len() == 2
            ) {
                return Err(self.err(
                    ParserError::InvalidRareConclusion(name.clone()),
                    self.current_position,
                ));
            }
            if body.premises.iter().any(|premise| {
                !matches!(
                    premise.as_ref(),
                    Term::Op(Operator::Equals | Operator::Distinct, args) if args.len() == 2
                )
            }) {
                return Err(self.err(
                    ParserError::InvalidRarePremise(name.clone()),
                    self.current_position,
                ));
            }

            let parameters: IndexMap<_, _> = parameters.into_iter().collect();
            if let Some(argument) = body
                .args
                .iter()
                .find(|argument| !parameters.contains_key(*argument))
            {
                return Err(self.err(
                    ParserError::UndeclaredRareArgument(name.clone(), argument.clone()),
                    self.current_position,
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
        self.state.symbol_table.pop_scope();
        result
    }

    pub(crate) fn parse_rare(&mut self) -> CarcaraResult<Rules> {
        let mut rules = Vec::new();
        while self.current_token != Token::Eof {
            rules.push(self.parse_rare_rule()?);
        }

        Ok(RareStatements {
            rules: rules
                .into_iter()
                .map(|rule| (rule.name.clone(), rule))
                .collect(),
        })
    }
}
