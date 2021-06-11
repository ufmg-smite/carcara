use super::{get_single_term_from_command, to_option, RuleArgs};
use crate::ast::*;
use std::collections::HashSet;

pub fn bind(
    RuleArgs {
        conclusion,
        context,
        subproof_commands,
        ..
    }: RuleArgs,
) -> Option<()> {
    if subproof_commands.len() < 2 || conclusion.len() != 1 {
        return None;
    }

    // The last command in the subproof is the one we are currently checking, so we look at the one
    // before that
    let previous_command = &subproof_commands[subproof_commands.len() - 2];
    let (phi, phi_prime) = match_term!((= p q) = get_single_term_from_command(previous_command)?)?;

    // Since we are closing a subproof, we only care about the substitutions that were introduced
    // in it
    let substitutions = context.last()?;

    // None of y_1, ..., y_n can appear as free variables in phi
    let mut ys = substitutions.values().map(|t| t.try_as_var());
    let free_vars = phi.free_vars();
    if ys.any(|y| y.map(|var| free_vars.contains(var)).unwrap_or(true)) {
        return None;
    }

    let (left, right) = match_term!((= l r) = conclusion[0])?;
    let ((l_bindings, left), (r_bindings, right)) = match (left, right) {
        // While the documentation indicates this rule is only called with "forall" quantifiers, in
        // some of the tests examples it is also called with the "exists" quantifier
        (Term::Quant(_, l_binds, l_term), Term::Quant(_, r_binds, r_term)) => {
            ((l_binds, l_term.as_ref()), (r_binds, r_term.as_ref()))
        }
        _ => return None,
    };

    // The terms in the quantifiers must be phi and phi'
    if left != phi || right != phi_prime {
        return None;
    }

    // And the quantifier binders must be the xs and ys of the context substitutions
    let substitutions: Vec<_> = substitutions
        .iter()
        .filter(|&(k, v)| k != v) // We ignore symmetric substitutions like (:= x x)
        .map(|(x, y)| Some((x.try_as_var()?, y.try_as_var()?)))
        .collect::<Option<_>>()?;
    let (xs, ys): (HashSet<_>, HashSet<_>) = substitutions.into_iter().unzip();

    let l_bindings: HashSet<_> = l_bindings.iter().map(|(var, _)| var.as_str()).collect();
    let r_bindings: HashSet<_> = r_bindings.iter().map(|(var, _)| var.as_str()).collect();

    to_option(l_bindings == xs && r_bindings == ys)
}
