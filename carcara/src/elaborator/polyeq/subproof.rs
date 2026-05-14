use super::*;
use crate::{ast::*, checker::error::CheckerError};

pub fn subproof(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, CheckerError> {
    let unchanged = || Ok(Rc::new(ProofNode::Step(step.clone())));

    let previous_step = &step.previous_step.as_ref().unwrap().as_step().unwrap();

    let [previous] = previous_step.clause.as_slice() else {
        return unchanged();
    };
    let last_term = step.clause.last().unwrap();
    if last_term == previous {
        return unchanged();
    }

    let mut ids = IdHelper::new(&step.id);
    let polyeq_step = PolyeqElaborator::new(&mut ids, step.depth, false).elaborate(
        pool,
        previous.clone(),
        last_term.clone(),
    );
    let equiv1_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        clause: vec![
            build_term!(pool, (not {previous.clone()})),
            last_term.clone(),
        ],
        rule: "equiv1".to_owned(),
        premises: vec![polyeq_step],
        ..StepNode::default()
    }));
    let resolution_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        clause: vec![last_term.clone()],
        rule: "resolution".to_owned(),
        premises: vec![equiv1_step, step.previous_step.clone().unwrap()],
        args: vec![previous.clone(), pool.bool_false()],
        ..StepNode::default()
    }));
    let mut new_step = step.clone();
    new_step.previous_step = Some(resolution_step);
    Ok(Rc::new(ProofNode::Step(new_step)))
}
