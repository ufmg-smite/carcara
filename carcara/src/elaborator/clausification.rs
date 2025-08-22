use super::{IdHelper, PolyeqElaborator};
use crate::{
    ast::*,
    checker::{apply_bfun_elim, error::CheckerError},
};
use indexmap::IndexMap;

pub fn bfun_elim(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, CheckerError> {
    assert_eq!(step.premises.len(), 1);
    assert_eq!(step.clause.len(), 1);
    let psi = &step.premises[0].clause()[0];
    let expected = apply_bfun_elim(pool, psi, &mut IndexMap::new())?;
    let got = &step.clause[0];

    if *got == expected {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }

    let mut ids = IdHelper::new(&step.id);
    let polyeq_step = PolyeqElaborator::new(&mut ids, step.depth, false).elaborate(
        pool,
        expected.clone(),
        got.clone(),
    );
    let equiv1_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        clause: vec![build_term!(pool, (not {expected.clone()})), got.clone()],
        rule: "equiv1".to_owned(),
        premises: vec![polyeq_step],
        ..StepNode::default()
    }));
    let new_bfun_elim_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        clause: vec![expected.clone()],
        rule: "bfun_elim".to_owned(),
        premises: step.premises.clone(),
        ..StepNode::default()
    }));
    let resolution_step = Rc::new(ProofNode::Step(StepNode {
        id: step.id.clone(),
        depth: step.depth,
        clause: step.clause.clone(),
        rule: "resolution".to_owned(),
        premises: vec![equiv1_step, new_bfun_elim_step],
        args: vec![expected, pool.bool_false()],
        ..StepNode::default()
    }));
    Ok(resolution_step)
}
