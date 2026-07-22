use crate::{ast::*, checker::la_generic_partial, elaborator::error::ElaborationError};

pub fn bounded_farkas(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let mut trace = Some(Vec::new());
    la_generic_partial(&step.clause, &step.args, &mut trace)?;

    let inferred = trace
        .unwrap()
        .into_iter()
        .map(|a| pool.add(Term::new_real(a)));
    let new_args: Vec<_> = step.args.iter().cloned().chain(inferred).collect();

    Ok(Rc::new(ProofNode::Step(StepNode {
        args: new_args,
        rule: "la_generic".to_owned(),
        ..step.clone()
    })))
}
