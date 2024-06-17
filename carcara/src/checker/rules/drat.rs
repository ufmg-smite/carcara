use super::{
    assert_clause_len, assert_eq, assert_is_bool_constant, assert_num_args, assert_num_premises,
    CheckerError, Premise, RuleArgs, RuleResult,
};

pub fn resolution(rule_args: RuleArgs) -> RuleResult {
    let RuleArgs { conclusion, premises, .. } = rule_args;

}