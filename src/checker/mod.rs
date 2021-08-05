mod rules;

use crate::ast::*;
use rules::{Rule, RuleArgs};
use std::collections::{HashMap, HashSet};

#[derive(Debug)]
pub enum CheckerError {
    UnknownRule(String),
    LastSubproofStepIsNotStep,
}

/// Represents the correctness of a proof or a proof step.
#[must_use]
#[derive(Debug)]
pub enum Correctness {
    True,          // The proof/step is valid
    False(String), // The proof/step is invalid, and checking failed on the given rule
}

impl Correctness {
    fn as_bool(&self) -> bool {
        match self {
            Correctness::True => true,
            Correctness::False(_) => false,
        }
    }
}

type CheckerResult = Result<Correctness, CheckerError>;

struct Context {
    substitutions: HashMap<ByRefRc<Term>, ByRefRc<Term>>,
    substitutions_until_fixed_point: HashMap<ByRefRc<Term>, ByRefRc<Term>>,
    bindings: HashSet<SortedVar>,
}

pub struct ProofChecker {
    pool: TermPool,
    skip_unknown_rules: bool,
    allow_test_rule: bool,
    context: Vec<Context>,
}

impl ProofChecker {
    pub fn new(pool: TermPool, skip_unknown_rules: bool, allow_test_rule: bool) -> Self {
        ProofChecker {
            pool,
            skip_unknown_rules,
            allow_test_rule,
            context: Vec::new(),
        }
    }

    pub fn check(&mut self, proof: &Proof) -> CheckerResult {
        self.check_subproof(&proof.0)
    }

    fn check_subproof(&mut self, commands: &[ProofCommand]) -> CheckerResult {
        for step in commands {
            let correctness = self.check_command(step, commands)?;
            if !correctness.as_bool() {
                return Ok(correctness);
            }
        }
        Ok(Correctness::True)
    }

    fn check_command(
        &mut self,
        command: &ProofCommand,
        all_commands: &[ProofCommand],
    ) -> CheckerResult {
        match command {
            ProofCommand::Step(step) => self.check_step(step, all_commands, None),
            ProofCommand::Subproof {
                commands: inner_commands,
                assignment_args,
                variable_args,
            } => {
                let new_context = self.build_context(assignment_args, variable_args);
                self.context.push(new_context);
                let subproof_correctness =
                    self.check_subproof(&inner_commands[..inner_commands.len() - 1])?;
                if !subproof_correctness.as_bool() {
                    return Ok(subproof_correctness);
                }
                let last_step = match inner_commands.last().unwrap() {
                    ProofCommand::Step(s) => s,
                    _ => return Err(CheckerError::LastSubproofStepIsNotStep),
                };
                let correctness = self.check_step(last_step, all_commands, Some(inner_commands))?;
                self.context.pop();
                Ok(correctness)
            }
            ProofCommand::Assume(_) => Ok(Correctness::True),
        }
    }

    fn check_step<'a>(
        &mut self,
        ProofStep {
            clause,
            rule: rule_name,
            premises,
            args,
        }: &'a ProofStep,
        all_commands: &'a [ProofCommand],
        subproof_commands: Option<&'a [ProofCommand]>,
    ) -> CheckerResult {
        let rule = match Self::get_rule(rule_name, self.allow_test_rule) {
            Some(r) => r,
            None if self.skip_unknown_rules => return Ok(Correctness::True),
            None => return Err(CheckerError::UnknownRule(rule_name.to_string())),
        };
        let premises = premises.iter().map(|&i| &all_commands[i]).collect();
        let rule_args = RuleArgs {
            conclusion: clause,
            premises,
            args,
            pool: &mut self.pool,
            context: &mut self.context,
            subproof_commands,
        };
        Ok(match rule(rule_args) {
            Some(()) => Correctness::True,
            None => Correctness::False(rule_name.clone()),
        })
    }

    fn build_context(
        &mut self,
        assignment_args: &[(String, ByRefRc<Term>)],
        variable_args: &[SortedVar],
    ) -> Context {
        // Since some rules (like "refl") need to apply substitutions until a fixed point, we
        // precompute these substitutions into a separate hash map. This assumes that the assignment
        // arguments are in the correct order.
        let mut substitutions = HashMap::new();
        let mut substitutions_until_fixed_point = HashMap::new();

        // We build the `substitutions_until_fixed_point` hash map from the bottom up, by using the
        // substitutions already introduced to transform the result of a new substitution before
        // inserting it into the hash map. So for instance, if the substitutions are "(:= y z)" and
        // "(:= x (f y))", we insert the first substitution, and then, when introducing the second,
        // we use the current state of the hash map to transform "(f y)" into "(f z)". The
        // resulting hash map will then contain "(:= y z)" and "(:= x (f z))". However, the
        // arguments are given in the opposite order, that is, "(:= x (f y))" would come first,
        // followed by "(:= y z)". Because of that, we traverse the assignment arguments slice in
        // reverse.
        for (var, value) in assignment_args.iter().rev() {
            let var_term = terminal!(var var; self.pool.add_term(value.sort().clone()));
            let var_term = self.pool.add_term(var_term);
            substitutions.insert(var_term.clone(), value.clone());

            let new_value = self
                .pool
                .apply_substitutions(value, &mut substitutions_until_fixed_point);
            substitutions_until_fixed_point.insert(var_term, new_value);
        }

        let bindings = variable_args.iter().cloned().collect();
        Context {
            substitutions,
            substitutions_until_fixed_point,
            bindings,
        }
    }

    pub fn get_rule(rule_name: &str, allow_test_rule: bool) -> Option<Rule> {
        use rules::*;
        Some(match rule_name {
            "true" => tautology::r#true,
            "false" => tautology::r#false,
            "not_not" => tautology::not_not,
            "and_pos" => tautology::and_pos,
            "and_neg" => tautology::and_neg,
            "or_pos" => tautology::or_pos,
            "or_neg" => tautology::or_neg,
            "implies_pos" => tautology::implies_pos,
            "implies_neg1" => tautology::implies_neg1,
            "implies_neg2" => tautology::implies_neg2,
            "equiv_pos1" => tautology::equiv_pos1,
            "equiv_pos2" => tautology::equiv_pos2,
            "equiv_neg1" => tautology::equiv_neg1,
            "equiv_neg2" => tautology::equiv_neg2,
            "ite_pos1" => tautology::ite_pos1,
            "ite_pos2" => tautology::ite_pos2,
            "eq_reflexive" => reflexivity::eq_reflexive,
            "eq_transitive" => transitivity::eq_transitive,
            "eq_congruent" => congruence::eq_congruent,
            "eq_congruent_pred" => congruence::eq_congruent_pred,
            "distinct_elim" => clausification::distinct_elim,
            "la_rw_eq" => linear_arithmetic::la_rw_eq,
            "la_generic" => linear_arithmetic::la_generic,
            "la_disequality" => linear_arithmetic::la_disequality,
            "forall_inst" => quantifier::forall_inst,
            "qnt_join" => quantifier::qnt_join,
            "qnt_rm_unused" => quantifier::qnt_rm_unused,
            "th_resolution" | "resolution" => resolution::resolution,
            "refl" => reflexivity::refl,
            "trans" => transitivity::trans,
            "cong" => congruence::cong,
            "and" => clausification::and,
            "tautology" => resolution::tautology,
            "not_or" => clausification::not_or,
            "or" => clausification::or,
            "not_and" => clausification::not_and,
            "implies" => clausification::implies,
            "equiv1" => tautology::equiv1,
            "equiv2" => tautology::equiv2,
            "not_equiv1" => tautology::not_equiv1,
            "not_equiv2" => tautology::not_equiv2,
            "ite1" => tautology::ite1,
            "ite2" => tautology::ite2,
            "ite_intro" => tautology::ite_intro,
            "contraction" => resolution::contraction,
            "connective_def" => tautology::connective_def,
            "eq_simplify" => simplification::eq_simplify,
            "and_simplify" => simplification::and_simplify,
            "or_simplify" => simplification::or_simplify,
            "not_simplify" => simplification::not_simplify,
            "implies_simplify" => simplification::implies_simplify,
            "equiv_simplify" => simplification::equiv_simplify,
            "bool_simplify" => simplification::bool_simplify,
            "prod_simplify" => simplification::prod_simplify,
            "minus_simplify" => simplification::minus_simplify,
            "comp_simplify" => simplification::comp_simplify,
            "nary_elim" => clausification::nary_elim,
            "ac_simp" => simplification::ac_simp,
            "bfun_elim" => clausification::bfun_elim,
            "bind" => subproof::bind,
            "qnt_cnf" => quantifier::qnt_cnf,
            "subproof" => subproof::subproof,
            "let" => subproof::r#let,
            "onepoint" => subproof::onepoint,
            "sko_ex" => subproof::sko_ex,
            "sko_forall" => subproof::sko_forall,
            "trust_me" if allow_test_rule => |_| Some(()),
            _ => return None,
        })
    }
}
