use crate::ast::ProofCommand;

/// Function that returns a weight associated with a specific rule. These
/// weights are directly correlated to carcara (Single Thread/previous version)
/// median performance while solving each of those rules.
///
/// Even though subproofs should have a weight (since it has a high cost to be
/// computed), it's for better of scheduler architecture that subproofs have a
/// null weight.
///
/// If you're interested in these weight values, take a look at Carcara's paper
/// published at TACAS in April 2023
/// (https://hanielbarbosa.com/papers/tacas2023.pdf) and its benchmark data.
///
/// The rules with null weight are rules that we had no info about the median
/// performance, since the solver used in the paper dataset does not generate
/// these rules.
pub fn get_step_weight(step: &ProofCommand) -> u64 {
    match step {
        ProofCommand::Assume { .. } => 230,
        ProofCommand::Subproof(_) => 0,
        ProofCommand::Step(s) => {
            match &s.rule as &str {
                "assume" => 230,
                "true" => 0, //-1
                "false" => 263,
                "not_not" => 574,
                "and_pos" => 361,
                "and_neg" => 607,
                "or_pos" => 640,
                "or_neg" => 460,
                "xor_pos1" => 763,
                "xor_pos2" => 345,
                "xor_neg1" => 0, //-1
                "xor_neg2" => 0, //-1
                "implies_pos" => 394,
                "implies_neg1" => 214,
                "implies_neg2" => 287,
                "equiv_pos1" => 763,
                "equiv_pos2" => 541,
                "equiv_neg1" => 434,
                "equiv_neg2" => 476,
                "ite_pos1" => 804,
                "ite_pos2" => 344,
                "ite_neg1" => 566,
                "ite_neg2" => 542,
                "eq_reflexive" => 451,
                "eq_transitive" => 780,
                "eq_congruent" => 722,
                "eq_congruent_pred" => 632,
                "distinct_elim" => 812,
                "la_rw_eq" => 1091,
                "la_generic" => 87564,
                "la_disequality" => 919,
                "la_totality" => 0, //-1
                "la_tautology" => 4291,
                "forall_inst" => 7877,
                "qnt_join" => 2347,
                "qnt_rm_unused" => 3659,
                "resolution" => 7491,
                "th_resolution" => 2462,
                "refl" => 1305,
                "trans" => 575,
                "cong" => 984,
                "ho_cong" => 0, //-1
                "and" => 493,
                "tautology" => 0, //-1
                "not_or" => 476,
                "or" => 426,
                "not_and" => 927,
                "xor1" => 0,     //-1
                "xor2" => 0,     //-1
                "not_xor1" => 0, //-1
                "not_xor2" => 0, //-1
                "implies" => 788,
                "not_implies1" => 402,
                "not_implies2" => 484,
                "equiv1" => 837,
                "equiv2" => 812,
                "not_equiv1" => 418,
                "not_equiv2" => 451,
                "ite1" => 509,
                "ite2" => 493,
                "not_ite1" => 722,
                "not_ite2" => 476,
                "ite_intro" => 3192,
                "contraction" => 1731,
                "connective_def" => 705,
                "ite_simplify" => 1797,
                "eq_simplify" => 845,
                "and_simplify" => 1165,
                "or_simplify" => 1133,
                "not_simplify" => 787,
                "implies_simplify" => 1231,
                "equiv_simplify" => 1337,
                "bool_simplify" => 1436,
                "qnt_simplify" => 517,
                "div_simplify" => 2117,
                "prod_simplify" => 2527,
                "unary_minus_simplify" => 0, //-1
                "minus_simplify" => 1059,
                "sum_simplify" => 2248,
                "comp_simplify" => 1781,
                "nary_elim" => 0, //-1
                "ac_simp" => 9781,
                "bfun_elim" => 8558,
                "bind" => 5924,
                "qnt_cnf" => 14244,
                "subproof" => 262,
                "let" => 4718,
                "onepoint" => 7787,
                "sko_ex" => 9321,
                "sko_forall" => 12242,
                "reordering" => 1452,
                "symm" => 682,
                "not_symm" => 0, //-1
                "eq_symmetric" => 673,
                "or_intro" => 508,
                "bind_let" => 2324,
                "la_mult_pos" => 1446,
                "la_mult_neg" => 1447,
                "hole" => 185,  //Debug only
                "trust" => 185, //Debug only
                "strict_resolution" => 1276,

                _ => 0,
            }
        }
    }
}