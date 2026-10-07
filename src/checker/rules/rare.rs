use rapidhash::{HashMapExt, RapidHashMap};

use crate::{
    ast::{Constant, Substitution, Term},
    checker::{
        error::CheckerError,
        rules::{assert_num_args, assert_num_premises, get_premise_term},
    },
    rare::{get_rules, rewrite_meta_terms},
};

use super::{RuleArgs, RuleResult};

pub fn check_rare(
    RuleArgs {
        premises,
        conclusion,
        pool,
        args,
        rare_rules,
        ..
    }: RuleArgs,
) -> RuleResult {
    let Some(rule_literal) = args.first() else {
        return Err(CheckerError::RareNotSpecifiedRule);
    };

    if let Term::Const(Constant::String(v)) = &**rule_literal {
        let Some(rare_term) = rare_rules.rules.get(v) else {
            return Err(CheckerError::RareRuleNotFound(v.clone()));
        };
        // The first argument is the rule name
        assert_num_args(args, rare_term.arguments.len() + 1)?;
        assert_num_premises(premises, rare_term.premises.len())?;

        if conclusion.is_empty() || conclusion.len() > 1 {
            return Err(CheckerError::RareConclusionNumberInvalid);
        }

        let mut arguments = args.iter().rev();
        let mut map = RapidHashMap::new();

        for arg in rare_term.arguments.iter().rev() {
            let arg_sort = rare_term.parameters.get(arg).unwrap();
            let value = arguments.next().unwrap().clone();
            let variable = pool.add(Term::Var(arg.clone(), arg_sort.sort.clone()));
            map.insert(variable, value);
        }

        let mut rare_premises = rare_term.premises.iter();
        let mut subst = Substitution::new(pool, map.clone())?;

        for premise in premises {
            let premise = get_premise_term(premise)?;
            let rare_premise = rare_premises.next().unwrap();
            let rare_premise = subst.apply(pool, rare_premise);
            let rare_premise = rewrite_meta_terms(pool, rare_premise, get_rules());

            if *premise != rare_premise {
                return Err(CheckerError::RarePremiseAreNotEqual(
                    premise.clone(),
                    rare_premise.clone(),
                ));
            }
        }

        let got = subst.apply(pool, &rare_term.conclusion);
        for premise in premises {
            let premise = get_premise_term(premise)?;
            let premise_rare = rewrite_meta_terms(pool, premise.clone(), get_rules());
            if *premise != premise_rare {
                return Err(CheckerError::RarePremiseAreNotEqual(
                    premise.clone(),
                    premise_rare,
                ));
            }
        }

        let rule_conclusion = rewrite_meta_terms(pool, got, get_rules());
        if rule_conclusion != conclusion[0] {
            return Err(CheckerError::RareConclusionAreNotEqual(
                rule_conclusion,
                conclusion[0].clone(),
            ));
        }

        return Ok(());
    }

    Err(CheckerError::RareRuleExpectedLiteral(rule_literal.clone()))
}
