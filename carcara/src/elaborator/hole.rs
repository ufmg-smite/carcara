use super::*;
use crate::external::{self, ExternalError};

pub fn hole(
    elaborator: &mut Elaborator,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let prelude = elaborator.problem.prelude.clone();
    let prelude = if prelude.logic.as_deref() == Some("QF_LIA") {
        ProblemPrelude {
            logic: Some("QF_LIRA".into()),
            ..prelude
        }
    } else {
        prelude
    };
    let asserts: Vec<_> = step
        .clause
        .iter()
        .map(|l| build_term!(elaborator.pool, (not {l.clone()})))
        .collect();
    let problem = external::get_problem_string(elaborator.pool, &prelude, &asserts);
    let solver = elaborator.config.hole_solver.as_ref().unwrap();
    let (commands, holey) = external::get_solver_proof(elaborator.pool, problem.clone(), solver)?;
    if holey {
        return Err(ExternalError::InnerProofHoley.into());
    }

    Ok(external::insert_solver_proof(
        elaborator.pool,
        commands,
        &step.clause,
        &step.id,
        step.depth,
    ))
}

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
    let solver = elaborator.config.lia_solver.as_ref().unwrap();
    let (commands, _) = external::get_solver_proof(elaborator.pool, problem, solver)?;

    Ok(external::insert_solver_proof(
        elaborator.pool,
        commands,
        &step.clause,
        &step.id,
        step.depth,
    ))
}
