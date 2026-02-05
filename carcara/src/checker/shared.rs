use crate::{
    ast::*,
    benchmarking::CollectResults,
    checker::{
        rules::{rare::check_rare, RuleArgs, RuleResult},
        CheckerStatistics, Config,
    },
};
use indexmap::IndexSet;
use std::time::{Duration, Instant};

/// Shared logic for checking assume commands that both single-threaded and parallel
/// implementations can use. Returns true if the assume is valid.
pub fn check_assume_shared<CR: CollectResults + Send + Default>(
    id: &str,
    term: &Rc<Term>,
    premises: &IndexSet<Rc<Term>>,
    config: &Config,
    is_in_subproof: bool,
    stats: &mut Option<&mut CheckerStatistics<CR>>,
) -> bool {
    let time = Instant::now();

    // Some subproofs contain `assume` commands inside them. These don't refer to the original
    // problem premises, but are instead local assumptions that are discharged by the subproof's
    // final step, so we ignore the `assume` command if it is inside a subproof.
    if is_in_subproof {
        return true;
    }

    // Check for exact match first
    if premises.contains(term) {
        let total_time = time.elapsed();
        if let Some(s) = stats {
            s.assume_time += total_time;
            s.results
                .add_assume_measurement(s.file_name, id, true, total_time);
        }
        return true;
    }

    // If elaborated mode, no polyeq checking allowed
    if config.elaborated {
        return false;
    }

    // Perform polyeq checking
    let mut found = false;
    let mut polyeq_time = Duration::ZERO;
    let mut core_time = Duration::ZERO;

    for p in premises {
        let mut this_polyeq_time = Duration::ZERO;

        let mut comp = Polyeq::new().mod_reordering(true).mod_nary(true);
        let result = comp.eq_with_time(term, p, &mut this_polyeq_time);
        let depth = comp.max_depth();

        polyeq_time += this_polyeq_time;

        if let Some(s) = &mut *stats {
            s.results.add_polyeq_depth(depth);
        }
        if result {
            core_time = this_polyeq_time;
            found = true;
            break;
        }
    }

    let total_time = time.elapsed();

    if let Some(s) = stats {
        s.assume_time += total_time;
        s.assume_core_time += core_time;
        s.polyeq_time += polyeq_time;
        s.results
            .add_assume_measurement(s.file_name, id, false, total_time);
    }

    found
}

/// Context information for step checking
pub struct StepCheckContext<'a> {
    pub config: &'a Config,
    pub is_end_step: bool,
    pub current_subproof: Option<&'a [ProofCommand]>,
    pub subproof_depth: usize,
    pub is_holey: &'a mut bool,
}

/// Shared core logic for checking a proof step. This contains all the rule validation
/// and execution logic that's identical between single-threaded and parallel implementations.
pub fn check_step_core<CR: CollectResults + Send + Default>(
    step: &ProofStep,
    rule_args: RuleArgs,
    context: StepCheckContext,
    stats: &mut Option<&mut CheckerStatistics<CR>>,
) -> RuleResult {
    let time = Instant::now();

    if context.config.allowed_rules.contains(&step.rule) {
        *context.is_holey = true;
        return Ok(());
    }

    if !step.discharge.is_empty() && step.rule != "subproof" {
        use crate::checker::error::{CheckerError, SubproofError};
        return Err(CheckerError::Subproof(SubproofError::DischargeInWrongRule));
    }

    let rule = match get_rule_shared(&step.rule, context.config.elaborated) {
        Some(r) => r,
        None if context.config.ignore_unknown_rules => {
            *context.is_holey = true;
            return Ok(());
        }
        None => {
            use crate::checker::error::CheckerError;
            return Err(CheckerError::UnknownRule);
        }
    };

    if step.rule == "hole" || step.rule == "lia_generic" {
        *context.is_holey = true;
    }

    // Execute the rule with the provided arguments
    rule(rule_args)?;

    if context.is_end_step {
        if let Some(subproof) = context.current_subproof {
            check_discharge_shared(subproof, context.subproof_depth, &step.discharge)?;
        }
    }

    if let Some(s) = stats {
        let elapsed = time.elapsed();
        s.results
            .add_step_measurement(s.file_name, &step.id, &step.rule, elapsed);
        // Note: polyeq_time is updated via the rule_args.polyeq_time reference
    }
    Ok(())
}

/// Shared discharge checking logic
pub fn check_discharge_shared(
    subproof: &[ProofCommand],
    depth: usize,
    discharge: &[(usize, usize)],
) -> RuleResult {
    use crate::checker::error::{CheckerError, SubproofError};

    let discharge: IndexSet<_> = discharge.iter().collect();
    if let Some((_, not_discharged)) = subproof
        .iter()
        .enumerate()
        .find(|&(i, command)| command.is_assume() && !discharge.contains(&(depth, i)))
    {
        Err(CheckerError::Subproof(
            SubproofError::LocalAssumeNotDischarged(not_discharged.id().to_owned()),
        ))
    } else {
        Ok(())
    }
}

pub fn get_rule_shared(rule_name: &str, elaborated: bool) -> Option<crate::checker::rules::Rule> {
    use crate::checker::rules::*;

    Some(match rule_name {
        "true" => tautology::r#true,
        "false" => tautology::r#false,
        "not_not" => tautology::not_not,
        "and_pos" => tautology::and_pos,
        "and_neg" => tautology::and_neg,
        "or_pos" => tautology::or_pos,
        "or_neg" => tautology::or_neg,
        "xor_pos1" => tautology::xor_pos1,
        "xor_pos2" => tautology::xor_pos2,
        "xor_neg1" => tautology::xor_neg1,
        "xor_neg2" => tautology::xor_neg2,
        "implies_pos" => tautology::implies_pos,
        "implies_neg1" => tautology::implies_neg1,
        "implies_neg2" => tautology::implies_neg2,
        "equiv_pos1" => tautology::equiv_pos1,
        "equiv_pos2" => tautology::equiv_pos2,
        "equiv_neg1" => tautology::equiv_neg1,
        "equiv_neg2" => tautology::equiv_neg2,
        "ite_pos1" => tautology::ite_pos1,
        "ite_pos2" => tautology::ite_pos2,
        "ite_neg1" => tautology::ite_neg1,
        "ite_neg2" => tautology::ite_neg2,
        "eq_reflexive" => reflexivity::eq_reflexive,
        "eq_transitive" => transitivity::eq_transitive,
        "eq_congruent" => congruence::eq_congruent,
        "eq_congruent_pred" => congruence::eq_congruent_pred,
        "distinct_elim" => clausification::distinct_elim,
        "la_rw_eq" => linear_arithmetic::la_rw_eq,
        "la_generic" => linear_arithmetic::la_generic,
        "la_disequality" => linear_arithmetic::la_disequality,
        "la_totality" => linear_arithmetic::la_totality,
        "la_tautology" => linear_arithmetic::la_tautology,
        "arith_poly_norm" => linear_arithmetic::arith_poly_norm,
        "forall_inst" => quantifier::forall_inst,
        "qnt_join" => quantifier::qnt_join,
        "qnt_rm_unused" => quantifier::qnt_rm_unused,
        "resolution" | "th_resolution" if elaborated => resolution::resolution_with_args,
        "resolution" | "th_resolution" => resolution::resolution,
        "refl" if elaborated => reflexivity::strict_refl,
        "refl" => reflexivity::refl,
        "trans" => transitivity::trans,
        "cong" => congruence::cong,
        "ho_cong" => congruence::ho_cong,
        "and" => clausification::and,
        "tautology" => resolution::tautology,
        "not_or" => clausification::not_or,
        "or" => clausification::or,
        "not_and" => clausification::not_and,
        "xor1" => clausification::xor1,
        "xor2" => clausification::xor2,
        "not_xor1" => clausification::not_xor1,
        "not_xor2" => clausification::not_xor2,
        "implies" => clausification::implies,
        "not_implies1" => clausification::not_implies1,
        "not_implies2" => clausification::not_implies2,
        "equiv1" => tautology::equiv1,
        "equiv2" => tautology::equiv2,
        "not_equiv1" => tautology::not_equiv1,
        "not_equiv2" => tautology::not_equiv2,
        "ite1" => tautology::ite1,
        "ite2" => tautology::ite2,
        "not_ite1" => tautology::not_ite1,
        "not_ite2" => tautology::not_ite2,
        "ite_intro" => tautology::ite_intro,
        "contraction" => resolution::contraction,
        "connective_def" => tautology::connective_def,
        "ite_simplify" => simplification::ite_simplify,
        "eq_simplify" => simplification::eq_simplify,
        "and_simplify" => simplification::and_simplify,
        "or_simplify" => simplification::or_simplify,
        "not_simplify" => simplification::not_simplify,
        "implies_simplify" => simplification::implies_simplify,
        "equiv_simplify" => simplification::equiv_simplify,
        "bool_simplify" => simplification::bool_simplify,
        "qnt_simplify" => simplification::qnt_simplify,
        "div_simplify" => simplification::div_simplify,
        "prod_simplify" => simplification::prod_simplify,
        // Despite being separate rules in the specification, proofs generated by veriT don't
        // differentiate between `unary_minus_simplify` and `minus_simplify`. To account for
        // that, `simplification::minus_simplify` implements both rules in the same function.
        "unary_minus_simplify" | "minus_simplify" => simplification::minus_simplify,
        "sum_simplify" => simplification::sum_simplify,
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
        "reordering" => extras::reordering,
        "shuffle" => extras::shuffle,
        "symm" => extras::symm,
        "not_symm" => extras::not_symm,
        "eq_symmetric" => extras::eq_symmetric,
        "weakening" => extras::weakening,
        "bind_let" => extras::bind_let,
        "la_mult_pos" => extras::la_mult_pos,
        "la_mult_neg" => extras::la_mult_neg,
        "mod_simplify" => extras::mod_simplify,
        "evaluate" => extras::evaluate,

        "bitblast_extract" => bitvectors::extract,
        "bitblast_bvadd" => bitvectors::add,
        "bitblast_ult" => bitvectors::ult,

        "concat_eq" => strings::concat_eq,
        "concat_unify" => strings::concat_unify,
        "concat_conflict" => strings::concat_conflict,
        "concat_csplit_prefix" => strings::concat_csplit_prefix,
        "concat_csplit_suffix" => strings::concat_csplit_suffix,
        "concat_split_prefix" => strings::concat_split_prefix,
        "concat_split_suffix" => strings::concat_split_suffix,
        "concat_lprop_prefix" => strings::concat_lprop_prefix,
        "concat_lprop_suffix" => strings::concat_lprop_suffix,
        "concat_cprop_prefix" => strings::concat_cprop_prefix,
        "concat_cprop_suffix" => strings::concat_cprop_suffix,

        // pseudo-boolean bitblasting
        "pbblast_bveq" => pb_blasting::pbblast_bveq,
        "pbblast_bvult" => pb_blasting::pbblast_bvult,
        "pbblast_bvugt" => pb_blasting::pbblast_bvugt,
        "pbblast_bvuge" => pb_blasting::pbblast_bvuge,
        "pbblast_bvule" => pb_blasting::pbblast_bvule,
        "pbblast_bvslt" => pb_blasting::pbblast_bvslt,
        "pbblast_bvsgt" => pb_blasting::pbblast_bvsgt,
        "pbblast_bvsge" => pb_blasting::pbblast_bvsge,
        "pbblast_bvsle" => pb_blasting::pbblast_bvsle,
        "pbblast_pbbvar" => pb_blasting::pbblast_pbbvar,
        "pbblast_pbbconst" => pb_blasting::pbblast_pbbconst,
        "pbblast_bvxor" => pb_blasting::pbblast_bvxor,
        "pbblast_bvand" => pb_blasting::pbblast_bvand,
        "pbblast_bvxor_ith_bit" => pb_blasting::pbblast_bvxor_ith_bit,
        "pbblast_bvand_ith_bit" => pb_blasting::pbblast_bvand_ith_bit,

        // cutting planes rules
        "cp_addition" => cutting_planes::cp_addition,
        "cp_multiplication" => cutting_planes::cp_multiplication,
        "cp_division" => cutting_planes::cp_division,
        "cp_saturation" => cutting_planes::cp_saturation,
        "cp_literal" => cutting_planes::cp_literal,
        "cp_normalize" => cutting_planes::cp_normalize,

        "string_decompose" => strings::string_decompose,
        "string_length_pos" => strings::string_length_pos,
        "string_length_non_empty" => strings::string_length_non_empty,

        "re_inter" => strings::re_inter,
        "re_kleene_star_unfold_pos" => strings::re_kleene_star_unfold_pos,
        "re_concat_unfold_pos" => strings::re_concat_unfold_pos,
        "re_unfold_neg" => strings::re_unfold_neg,
        "re_unfold_neg_concat_fixed_prefix" => strings::re_unfold_neg_concat_fixed_prefix,
        "re_unfold_neg_concat_fixed_suffix" => strings::re_unfold_neg_concat_fixed_suffix,
        // Drup format rules
        "drup" => |x| crate::checker::rules::drup::drup(false, x),
        // Drat format rules
        "drat" => |x| crate::checker::rules::drup::drup(true, x),

        // Special rules that always check as valid, and are used to indicate holes in the
        // proof.
        "hole" => |_| Ok(()),
        "lia_generic" => |_| {
            log::warn!("encountered \"lia_generic\" rule, ignoring");
            Ok(())
        },

        // The Alethe specification does not yet describe how this more strict version of the
        // resolution rule will be called. Until that is decided and added to the specification,
        // we define a new specialized rule that calls it
        "strict_resolution" => resolution::strict_resolution,
        "rare_rewrite" => check_rare,
        _ => return None,
    })
}
