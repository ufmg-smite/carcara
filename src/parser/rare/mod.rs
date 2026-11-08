use super::{Parser, ParserError, Reserved, Token};
use crate::CarcaraResult;
use crate::ast::{rare_rules::*, *};

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

impl<'p, 's> Parser<'p, 's> {
    fn parse_rare_parameters(&mut self) -> CarcaraResult<(String, TypeParameter)> {
        self.expect_token(Token::OpenParen)?;
        let name = self.expect_symbol()?;
        let sort = self.parse_sort()?;

        let attribute = if let Token::Keyword(_) = self.current_token {
            let attribute = self.expect_any_keyword()?;
            if attribute == "list" {
                Ok(AttributeParameters::List)
            } else {
                Err(self.err(
                    ParserError::InvalidRareArgAttribute(attribute.to_owned()),
                    self.current_position,
                ))
            }
        } else {
            Ok(AttributeParameters::None)
        }?;
        self.expect_token(Token::CloseParen)?;

        self.declare_symbol(name, sort.clone());

        Ok((name.to_owned(), TypeParameter { sort, attribute }))
    }

    fn parse_body(&mut self) -> CarcaraResult<Body> {
        match self.expect_any_keyword()? {
            "conclusion" => {
                let rewrite_term = self.parse_term()?;
                Ok(Body::Conclusion(rewrite_term))
            }
            "args" => {
                self.expect_token(Token::OpenParen)?;
                let args = self.parse_sequence(|p| Ok(p.expect_symbol()?.to_owned()), false)?;
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
            other => Err(self.err(
                ParserError::InvalidRareRuleAttribute(other.to_owned()),
                self.current_position,
            )),
        }
    }

    fn parse_rule(&mut self) -> CarcaraResult<RuleDefinition> {
        self.expect_token(Token::OpenParen)?;
        self.expect_token(Token::ReservedWord(Reserved::DeclareRareRule))?;
        let name = self.expect_symbol()?.to_owned();
        self.expect_token(Token::OpenParen)?;
        let parameters = self.parse_sequence(Self::parse_rare_parameters, false)?;

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
            return Err(self.err(
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

        Ok(RareStatements {
            rules: rules
                .iter()
                .map(|x| (x.name.clone(), (*x).clone()))
                .collect(),
        })
    }
}
