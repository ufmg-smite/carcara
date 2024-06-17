use super::{
    assert_clause_len, assert_eq, assert_is_bool_constant, assert_num_args, assert_num_premises,
    CheckerError, Premise, RuleArgs, RuleResult,
};

fn rup(conclusion: &[Rc<Term>], clause_set: Vec<IndexSet<(bool, &Rc<Term>)>>) -> bool {
  // TODO
}

pub fn drat( RuleArgs { conclusion, premises, args, .. } : RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 0)?;
    // - the initial clause set is the premises (build it as what is
    //   expected in the above function)
    // - for each argument:
    //   - if it is *not* a deletion, then show that you can conclude
    //     the respective clause from the current clause set via
    //     RUP. Add the argument to the clause set.
    //   - if it is a deletion: delete that clause from the clause_set
    // - Once all arguments have been processed, you are done as long
    //   as the empty clause has been added to the clause set.
    Ok(())
}
