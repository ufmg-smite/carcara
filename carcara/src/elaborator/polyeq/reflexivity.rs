use super::*;
use crate::{ast::*, checker::error::CheckerError};

fn polyeq(a: &Rc<Term>, b: &Rc<Term>) -> bool {
    Polyeq::new().mod_reordering(true).eq(a, b)
}

fn alpha_equiv(a: &Rc<Term>, b: &Rc<Term>) -> bool {
    Polyeq::new()
        .mod_reordering(true)
        .alpha_equiv(true)
        .eq(a, b)
}

fn elaborate_equality(
    pool: &mut PrimitivePool,
    l: &Rc<Term>,
    r: &Rc<Term>,
    ids: &mut IdHelper,
    depth: usize,
) -> Rc<ProofNode> {
    let is_alpha_equivalence = !polyeq(l, r);
    PolyeqElaborator::new(ids, depth, is_alpha_equivalence).elaborate(pool, l.clone(), r.clone())
}

pub fn refl(
    pool: &mut PrimitivePool,
    context: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, CheckerError> {
    assert_eq!(step.clause.len(), 1);

    let (left, right) = match_term_err!((= l r) = &step.clause[0])?;

    // This elaboration has the goal of fixing two problems we see in real world proofs: the need
    // for polyequality reasoning, and the need for applying the context to the right-hand term.
    //
    // In the most trivial case, no context application and no polyequality is needed.
    if left == right {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }

    // In the case where we only need to apply the context to the left-hand term, no elaboration
    // is needed also.
    let new_left = context.apply(pool, left);
    if new_left == *right {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }

    // The remaining cases actually require elaboration
    let mut ids = IdHelper::new(&step.id);
    let depth = step.depth;

    // First, we will handle the cases where no polyequality is needed, and we just need to sort out
    // the context application.
    //
    // If the substitution needs to be applied on the right term, we flip the `refl` equality and
    // add a `symm` step to flip it back.
    let new_right = context.apply(pool, right);
    if *left == new_right {
        let flipped = add_refl_step(pool, right.clone(), new_right, ids.next_id(), depth);
        return Ok(add_symm_step(pool, &flipped, step.id.clone()));
    }

    // If it needs to be applied to both sides, we split it into two `refl` steps, and add a `symm`
    // and `trans` to stitch them together.
    if new_left == new_right {
        let left_refl = add_refl_step(pool, left.clone(), new_left, ids.next_id(), depth);
        let right_refl = add_refl_step(pool, right.clone(), new_right, ids.next_id(), depth);
        let right_symm = add_symm_step(pool, &right_refl, ids.next_id());

        return Ok(add_trans_step(
            pool,
            [left_refl, right_symm],
            step.id.clone(),
        ));
    }

    // Now for the cases where we might also need polyequality. These mostly mirror the previous
    // cases
    if alpha_equiv(left, right) {
        // First, the case where no context application is needed, only polyequality reasoning
        Ok(elaborate_equality(pool, left, right, &mut ids, depth))
    } else if alpha_equiv(&new_left, right) {
        // Next, the one where we only need to apply the context on the left
        let left_refl = add_refl_step(pool, left.clone(), new_left.clone(), ids.next_id(), depth);
        let polyeq = elaborate_equality(pool, &new_left, right, &mut ids, depth);
        Ok(add_trans_step(pool, [left_refl, polyeq], step.id.clone()))
    } else if alpha_equiv(left, &new_right) {
        // Next, when we need to apply the context on the right
        let polyeq = elaborate_equality(pool, left, &new_right, &mut ids, depth);
        let right_refl = add_refl_step(pool, right.clone(), new_right, ids.next_id(), depth);
        let right_symm = add_symm_step(pool, &right_refl, ids.next_id());
        Ok(add_trans_step(pool, [polyeq, right_symm], step.id.clone()))
    } else if alpha_equiv(&new_left, &new_right) {
        // And finally, the case where we need to apply it to both sides
        let left_refl = add_refl_step(pool, left.clone(), new_left.clone(), ids.next_id(), depth);
        let polyeq = elaborate_equality(pool, &new_left, &new_right, &mut ids, depth);
        let right_refl = add_refl_step(pool, right.clone(), new_right, ids.next_id(), depth);
        let right_symm = add_symm_step(pool, &right_refl, ids.next_id());
        Ok(add_trans_step(
            pool,
            [left_refl, polyeq, right_symm],
            step.id.clone(),
        ))
    } else {
        // If no case matches, this step is not valid!
        Err(CheckerError::ReflexivityFailed(left.clone(), right.clone()))
    }
}
