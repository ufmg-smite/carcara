use super::{
    ContextStack,
    error::{CheckerError, EqualityError},
};
use crate::{
    ast::{Operator, ProofCommand, Rc, Term, alpha_equiv, polyeq, pool::Pool, rare_rules::Rules},
    utils::{Range, TypeName},
};
use std::time::Duration;

pub type RuleResult = Result<(), CheckerError>;

pub type Rule = fn(RuleArgs) -> RuleResult;

pub struct RuleArgs<'a> {
    pub(super) conclusion: &'a [Rc<Term>],
    pub(super) premises: &'a [Premise<'a>],
    pub(super) args: &'a [Rc<Term>],
    pub(super) pool: &'a mut Pool,
    pub(super) context: &'a mut ContextStack,
    pub(super) rare_rules: &'a Rules,

    // For rules that end a subproof, we need to pass the previous command in the subproof that it
    // is closing, because it may be implicitly referenced, and it is not given as premises. If a
    // rule is not ending a subproof, this should be `None`.
    pub(super) previous_command: Option<Premise<'a>>,
    pub(super) discharge: &'a [&'a ProofCommand],

    pub(super) polyeq_time: &'a mut Duration,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Premise<'a> {
    pub id: &'a str,
    pub clause: &'a [Rc<Term>],
    pub index: (usize, usize),
}

impl<'a> Premise<'a> {
    pub fn new(index: (usize, usize), command: &'a ProofCommand) -> Self {
        Self {
            id: command.id(),
            clause: command.clause(),
            index,
        }
    }
}

/// Helper function to get a single term from a premise, or return a
/// `CheckerError::WrongLengthOfPremiseClause` error if it doesn't succeed.
fn get_premise_term<'a>(premise: &Premise<'a>) -> Result<&'a Rc<Term>, CheckerError> {
    match premise.clause {
        [t] => Ok(t),
        cl => Err(CheckerError::WrongLengthOfPremiseClause(
            premise.id.to_owned(),
            1.into(),
            cl.len(),
        )),
    }
}

/// Asserts that the first argument is true, and returns the error specified by the second argument
/// otherwise.
macro_rules! rassert {
    ($arg:expr, $err:expr $(,)?) => {
        match $arg {
            true => Ok(()),
            false => Err($err),
        }?
    };
}

fn assert_num_premises<T: Into<Range>>(premises: &[Premise], range: T) -> RuleResult {
    let range = range.into();
    if !range.contains(premises.len()) {
        return Err(CheckerError::WrongNumberOfPremises(range, premises.len()));
    }
    Ok(())
}

fn assert_clause_len<T: Into<Range>>(clause: &[Rc<Term>], range: T) -> RuleResult {
    let range = range.into();
    if !range.contains(clause.len()) {
        return Err(CheckerError::WrongLengthOfClause(range, clause.len()));
    }
    Ok(())
}

fn assert_num_args<T: Into<Range>>(args: &[Rc<Term>], range: T) -> RuleResult {
    let range = range.into();
    if !range.contains(args.len()) {
        return Err(CheckerError::WrongNumberOfArgs(range, args.len()));
    }
    Ok(())
}

fn assert_operation_len<T: Into<Range>>(op: Operator, args: &[Rc<Term>], range: T) -> RuleResult {
    let range = range.into();
    if !range.contains(args.len()) {
        return Err(CheckerError::WrongNumberOfTermsInOp(op, range, args.len()));
    }
    Ok(())
}

fn assert_eq<T>(a: &T, b: &T) -> RuleResult
where
    T: Eq + Clone + TypeName,
    EqualityError<T>: Into<CheckerError>,
{
    if a != b {
        return Err(EqualityError::ExpectedEqual(a.clone(), b.clone()).into());
    }
    Ok(())
}

fn assert_is_expected<T>(got: &T, expected: T) -> RuleResult
where
    T: Eq + Clone + TypeName,
    EqualityError<T>: Into<CheckerError>,
{
    if *got != expected {
        return Err(EqualityError::ExpectedToBe { expected, got: got.clone() }.into());
    }
    Ok(())
}

fn assert_polyeq(a: &Rc<Term>, b: &Rc<Term>, time: &mut Duration) -> Result<(), CheckerError> {
    if !polyeq(a, b, time) {
        return Err(EqualityError::ExpectedEqual(a.clone(), b.clone()).into());
    }
    Ok(())
}

fn assert_polyeq_expected(got: &Rc<Term>, expected: Rc<Term>, time: &mut Duration) -> RuleResult {
    if !polyeq(got, &expected, time) {
        return Err(EqualityError::ExpectedToBe { expected, got: got.clone() }.into());
    }
    Ok(())
}

fn assert_alpha_equiv_expected(
    got: &Rc<Term>,
    expected: Rc<Term>,
    time: &mut Duration,
) -> RuleResult {
    if !alpha_equiv(got, &expected, time) {
        return Err(EqualityError::ExpectedToBe { expected, got: got.clone() }.into());
    }
    Ok(())
}

fn assert_is_bool_constant(got: &Rc<Term>, expected: bool) -> RuleResult {
    if !got.is_bool_constant(expected) {
        return Err(CheckerError::ExpectedBoolConstant(expected, got.clone()));
    }
    Ok(())
}

pub fn get_rule(rule_name: &str, elaborated: bool, prefer_rup: bool) -> Option<Rule> {
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
        "bounded_farkas" => linear_arithmetic::bounded_farkas,
        "la_disequality" => linear_arithmetic::la_disequality,
        "la_totality" => linear_arithmetic::la_totality,
        "la_tautology" => linear_arithmetic::la_tautology,
        "poly_simp" => polynomial::poly_simp,
        "poly_simp_rel" => polynomial::poly_simp_rel,
        "forall_inst" => quantifier::forall_inst,
        "qnt_join" => quantifier::qnt_join,
        "qnt_rm_unused" => quantifier::qnt_rm_unused,
        "resolution" | "th_resolution" if elaborated => resolution::resolution_with_args,
        "resolution" | "th_resolution" if prefer_rup => resolution::rup_resolution,
        "resolution" | "th_resolution" => resolution::resolution,
        "refl" if elaborated => reflexivity::strict_refl,
        "refl" => reflexivity::refl,
        "strict_refl" => reflexivity::strict_refl,
        "trans" => transitivity::trans,
        "cong" => congruence::cong,
        "ho_cong" => congruence::ho_cong,
        "and_intro" => extras::and_intro,
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
        "aci_simp" => simplification::aci_simp,
        "bfun_elim" => clausification::bfun_elim,
        "bind" => subproof::bind,
        "qnt_cnf" => quantifier::qnt_cnf,
        "miniscope_distribute" => quantifier::miniscope_distribute,
        "miniscope_split" => quantifier::miniscope_split,
        "miniscope_ite" => quantifier::miniscope_ite,
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
        "eq_mp" => extras::eq_mp,
        "weakening" => extras::weakening,
        "bind_let" => extras::bind_let,
        "la_mult_pos" => extras::la_mult_pos,
        "la_mult_neg" => extras::la_mult_neg,
        "la_mult_sign" => extras::la_mult_sign,
        "la_mult_abs_comparison" => extras::la_mult_abs_comparison,
        "mod_simplify" => extras::mod_simplify,
        "evaluate" => extras::evaluate,
        "beta_equiv" => extras::beta_equiv,
        "div_intro" => extras::div_intro,
        "log2_intro" => extras::log2_intro,
        "to_int_intro" => extras::to_int_intro,

        "bitblast_const" => bitvectors::value,
        "bitblast_var" => bitvectors::var,
        "bitblast_and" => bitvectors::and,
        "bitblast_or" => bitvectors::or,
        "bitblast_xor" => bitvectors::xor,
        "bitblast_xnor" => bitvectors::xnor,
        "bitblast_not" => bitvectors::not,
        "bitblast_comp" => bitvectors::comp,
        "bitblast_ult" => bitvectors::ult,
        "bitblast_slt" => bitvectors::slt,
        "bitblast_add" => bitvectors::add,
        "bitblast_mult" => bitvectors::mult,
        "bitblast_neg" => bitvectors::neg,
        "bitblast_equal" => bitvectors::equality,
        "bitblast_extract" => bitvectors::extract,
        "bitblast_concat" => bitvectors::concat,
        "bitblast_sign_extend" => bitvectors::sign_extend,
        "bitblast_shl" => bitvectors::shl,
        "bitblast_lshr" => bitvectors::lshr,
        "bitblast_ashr" => bitvectors::ashr,
        "bitblast_udiv" => bitvectors::udiv,
        "bitblast_urem" => bitvectors::urem,
        "bv_bitwise_slicing" => bitvectors::bitwise_slicing,

        // array rules
        "arrays_idx" => arrays::idx,
        "arrays_row" => arrays::row,
        "arrays_row_contra" => arrays::row_contra,
        "arrays_ext" => arrays::ext,

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
        "rare_rewrite" => rare::check_rare,
        _ => return None,
    })
}

// Since the rule submodules use the `rassert!` macro, we have to declare them here, after the
// macro is declared
pub(super) mod arrays;
pub(super) mod bitvectors;
pub(super) mod clausification;
pub(super) mod congruence;
pub(super) mod cutting_planes;
pub(super) mod drup;
pub(super) mod extras;
pub(super) mod linear_arithmetic;
pub(super) mod pb_blasting;
pub(super) mod polynomial;
pub(super) mod quantifier;
pub(super) mod rare;
pub(super) mod reflexivity;
pub(super) mod resolution;
pub(super) mod simplification;
pub(super) mod strings;
pub(super) mod subproof;
pub(super) mod tautology;
pub(super) mod transitivity;
