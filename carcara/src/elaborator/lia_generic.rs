use super::*;
use crate::external;

pub fn lia_generic(
    elaborator: &mut Elaborator,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let asserts: Vec<_> = step
        .clause
        .iter()
        .map(|l| build_term!(elaborator.pool, (not {l.clone()})))
        .collect();
    let problem =
        external::get_problem_string(elaborator.pool, &elaborator.problem.prelude, &asserts);
    let options = elaborator.config.lia_options.as_ref().unwrap();
    let (commands, _) = external::get_solver_proof(
        elaborator.pool,
        problem,
        &options.solver,
        &options.arguments,
    )?;

    Ok(external::insert_solver_proof(
        elaborator.pool,
        commands,
        &step.clause,
        &step.id,
        step.depth,
    ))
}
