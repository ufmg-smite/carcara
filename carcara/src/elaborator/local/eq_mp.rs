use crate::{
    ast::*,
    elaborator::{error::ElaborationError, IdHelper},
};

/// Elaborates an `eq_mp` step into a `resolution` step taking the
/// original premises and a new `equiv_pos2` step.
///
/// That is, a step of the form
/// ```text
/// (step t3 (cl F2) :rule eq_mp :premises (t1 t2))
/// ```
/// where `t1` concludes `F1` and `t2` concludes `(= F1 F2)`, becomes
/// ```text
/// (step t3.t1 (cl (not (= F1 F2)) (not F1) F2) :rule equiv_pos2)
/// (step t3 (cl F2) :rule resolution :premises (t3.t1 t2 t1) :args ((= F1 F2) false F1 false))
/// ```
///
/// If `F2` is the negation of `F1`, the last two literals of the `equiv_pos2` step are the same, so
/// the resolution would conclude the empty clause. It can conclude `F2` however if the resolution is
/// just with `t2`.
pub fn eq_mp(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    assert_eq!(step.clause.len(), 1);
    assert_eq!(step.premises.len(), 2);
    let (phi_1_step, equiv_step) = (&step.premises[0], &step.premises[1]);
    assert_eq!(equiv_step.clause().len(), 1);

    let equivalence = equiv_step.clause()[0].clone();
    let (phi_1, phi_2) = match_term_err!((= phi_1 phi_2) = &equivalence)?;
    let (phi_1, phi_2) = (phi_1.clone(), phi_2.clone());
    let special_case = match_term!((not phi) = &phi_2) == Some(&phi_1);

    let mut ids = IdHelper::new(&step.id);
    // The resolution that will be introduced in the special case relies on
    // duplicate removal. In the `uncrowd` pass, if that is active, a
    // `contraction` step would be added. To avoid clashing of ids, we make sure
    // that equiv_pos2 is one step deeper.
    if special_case {
        ids.push();
    }
    let equiv_pos2_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        clause: vec![
            build_term!(pool, (not {equivalence.clone()})),
            build_term!(pool, (not {phi_1.clone()})),
            phi_2,
        ],
        rule: "equiv_pos2".to_owned(),
        ..Default::default()
    }));
    let f = pool.bool_false();
    let mut premises = vec![equiv_pos2_step, equiv_step.clone()];
    let mut args = vec![equivalence, f.clone()];
    if !special_case {
        premises.push(phi_1_step.clone());
        args.extend([phi_1, f]);
    }

    Ok(Rc::new(ProofNode::Step(StepNode {
        rule: "resolution".to_owned(),
        premises,
        args,
        ..step.clone()
    })))
}
