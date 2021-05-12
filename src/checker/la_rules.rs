use super::to_option;

use crate::ast::*;

pub fn la_rw_eq(clause: &[ByRefRc<Term>], _: Vec<&ProofCommand>, _: &[ProofArg]) -> Option<()> {
    if clause.len() != 1 {
        return None;
    }
    let ((t_1, u_1), ((t_2, u_2), (u_3, t_3))) = match_term!(
        (= (= t u) (and (<= t u) (<= u t))) = clause[0]
    )?;
    to_option(t_1 == t_2 && t_2 == t_3 && u_1 == u_2 && u_2 == u_3)
}

pub fn la_disequality(
    clause: &[ByRefRc<Term>],
    _: Vec<&ProofCommand>,
    _: &[ProofArg],
) -> Option<()> {
    if clause.len() != 1 {
        return None;
    }
    let ((t1_1, t2_1), (t1_2, t2_2), (t2_3, t1_3)) = match_term!(
        (or (= t1 t2) (not (<= t1 t2)) (not (<= t2 t1))) = clause[0]
    )?;
    to_option(t1_1 == t1_2 && t1_2 == t1_3 && t2_1 == t2_2 && t2_2 == t2_3)
}
