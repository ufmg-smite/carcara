use super::*;
use crate::{ast::*, checker::error::CheckerError};

fn elaborate_equality(
    pool: &mut dyn TermPool,
    l: &Rc<Term>,
    r: &Rc<Term>,
    ids: &mut IdHelper,
    depth: usize,
    polyeq_time: &mut std::time::Duration,
) -> Rc<ProofNode> {
    let is_alpha_equivalence = !polyeq(l, r, polyeq_time);
    PolyeqElaborator::new(ids, depth, is_alpha_equivalence).elaborate(pool, l.clone(), r.clone())
}

pub fn refl(
    pool: &mut PrimitivePool,
    context: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, CheckerError> {
    assert_eq!(step.clause.len(), 1);

    let (left, right) = match_term_err!((= l r) = &step.clause[0])?;

    if left == right {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }

    // We don't compute the new left and right terms until they are needed
    let new_left = context.apply(pool, left);
    if new_left == *right {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }
    let new_right = context.apply(pool, right);
    if *left == new_right || new_left == new_right {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }

    #[allow(const_item_mutation)]
    let polyeq_time = &mut std::time::Duration::ZERO; // TODO

    let mut ids = IdHelper::new(&step.id);
    let depth = step.depth;

    // There are three cases to consider when elaborating a `refl` step. In the simpler case, no
    // context application is needed, and we can prove the equivalence of the left and right terms
    // directly. In the second case, we need to first apply the context to the left term, using a
    // `refl` step, and then prove the equivalence of the new left term with the right term. In the
    // third case, we also need to apply the context to the right term, using another `refl` step.
    if alpha_equiv(left, right, polyeq_time) {
        let equality_step = elaborate_equality(pool, left, right, &mut ids, depth, polyeq_time);
        Ok(equality_step)
    } else {
        let first_step = add_refl_step(pool, left.clone(), new_left.clone(), ids.next_id(), depth);

        if alpha_equiv(&new_left, right, polyeq_time) {
            let second_step =
                elaborate_equality(pool, &new_left, right, &mut ids, depth, polyeq_time);

            Ok(Rc::new(ProofNode::Step(StepNode {
                id: ids.next_id(),
                depth,
                clause: step.clause.clone(),
                rule: "trans".to_owned(),
                premises: vec![first_step, second_step],
                ..Default::default()
            })))
        } else if alpha_equiv(&new_left, &new_right, polyeq_time) {
            let second_step =
                elaborate_equality(pool, &new_left, right, &mut ids, depth, polyeq_time);

            let third_step =
                add_refl_step(pool, new_right.clone(), right.clone(), ids.next_id(), depth);

            Ok(Rc::new(ProofNode::Step(StepNode {
                id: ids.next_id(),
                depth,
                clause: step.clause.clone(),
                rule: "trans".to_owned(),
                premises: vec![first_step, second_step, third_step],
                ..Default::default()
            })))
        } else {
            Err(CheckerError::ReflexivityFailed(left.clone(), right.clone()))
        }
    }
}
