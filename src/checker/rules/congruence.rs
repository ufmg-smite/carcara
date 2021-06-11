use super::{get_single_term_from_command, to_option, RuleArgs};
use crate::ast::*;

pub fn eq_congruent(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    if conclusion.len() < 2 {
        return None;
    }
    let premises = conclusion[..conclusion.len() - 1]
        .iter()
        .map(|t| t.remove_negation());
    let conclusion = match_term!((= f g) = conclusion.last().unwrap())?;

    generic_congruent_rule(premises, conclusion)
}

pub fn eq_congruent_pred(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    if conclusion.len() < 3 {
        return None;
    }
    let premises = conclusion[..conclusion.len() - 2]
        .iter()
        .map(|t| t.remove_negation());

    let (p, q) = (
        &conclusion[conclusion.len() - 2],
        &conclusion[conclusion.len() - 1],
    );
    let conclusion = match p.remove_negation() {
        Some(p) => (p, q.as_ref()),
        None => (p.as_ref(), q.remove_negation()?),
    };

    generic_congruent_rule(premises, conclusion)
}

/// A function to check congruency. Useful for the "eq_congruent" and "eq_congruent_pred"
/// rules. `premises` should be an iterator over the argument equalities, and `conclusion`
/// should be the two function applications.
fn generic_congruent_rule<'a, T>(premises: T, conclusion: (&Term, &Term)) -> Option<()>
where
    T: Iterator<Item = Option<&'a Term>>,
{
    let mut ts = Vec::new();
    let mut us = Vec::new();
    for term in premises {
        let (t, u) = match_term!((= t u) = term?)?;
        ts.push(t);
        us.push(u);
    }

    let (f_args, g_args) = match conclusion {
        (Term::App(f, f_args), Term::App(g, g_args)) if f == g => (f_args, g_args),
        (Term::Op(f, f_args), Term::Op(g, g_args)) if f == g => (f_args, g_args),
        _ => return None,
    };
    if f_args.len() != g_args.len() || f_args.len() != ts.len() {
        return None;
    }
    for i in 0..ts.len() {
        let expected = (f_args[i].as_ref(), g_args[i].as_ref());
        if expected != (ts[i], us[i]) && expected != (us[i], ts[i]) {
            return None;
        }
    }
    Some(())
}

pub fn cong(
    RuleArgs {
        conclusion,
        premises,
        ..
    }: RuleArgs,
) -> Option<()> {
    /// Since the semantics of this rule is slighty different from that of "eq_congruent" and
    /// "eq_congruent_pred", we cannot just use the `generic_congruent_rule` function
    fn check_cong<'a>(
        premises: &[Option<(&'a Term, &'a Term)>],
        f_args: &[ByRefRc<Term>],
        g_args: &[ByRefRc<Term>],
    ) -> bool {
        let mut premises = premises.iter().peekable();
        for (f_arg, g_arg) in f_args.iter().zip(g_args) {
            let expected = (f_arg.as_ref(), g_arg.as_ref());
            match premises.peek() {
                // If the next premise can justify that the arguments are equal, we consume it. We
                // prefer consuming the premise even if the arguments are directly equal
                Some(Some((t, u))) if expected == (t, u) || expected == (u, t) => {
                    premises.next();
                }
                // If there are no more premises, or the next premise does not match the current
                // arguments, the arguments need to be directly equal
                None | Some(Some(_)) => {
                    if f_arg != g_arg {
                        return false;
                    }
                }
                // If the inner option is `None`, it means the premise was of the wrong form
                Some(None) => return false,
            }
        }

        // At the end, all premises must have been consumed
        premises.next().is_none()
    }

    if premises.is_empty() || conclusion.len() != 1 {
        return None;
    }

    let premises: Vec<_> = premises
        .into_iter()
        .map(|command| {
            get_single_term_from_command(command).and_then(|term| match_term!((= t u) = term))
        })
        .collect();

    let (f_args, g_args) = match match_term!((= f g) = conclusion[0].as_ref())? {
        // Because of the way veriT handles equality terms, when the "cong" rule is called with two
        // equalities of two terms, the order of their arguments may be flipped. Because of that,
        // we have to treat this special case separately
        (Term::Op(Operator::Eq, f_args), Term::Op(Operator::Eq, g_args))
            if f_args.len() == 2 && g_args.len() == 2 =>
        {
            // We have to test all four possibilites: neither f nor g are flipped, only f is
            // flipped, only g is flipped, or both f and g are flipped
            let f_args_flipped = [f_args[1].clone(), f_args[0].clone()];
            let g_args_flipped = [g_args[1].clone(), g_args[0].clone()];
            return to_option(
                check_cong(&premises, f_args, g_args)
                    || check_cong(&premises, &f_args_flipped, g_args)
                    || check_cong(&premises, f_args, &g_args_flipped)
                    || check_cong(&premises, &f_args_flipped, &g_args_flipped),
            );
        }

        (Term::App(f, f_args), Term::App(g, g_args)) if f == g => (f_args, g_args),
        (Term::Op(f, f_args), Term::Op(g, g_args)) if f == g => (f_args, g_args),
        _ => return None,
    };
    if f_args.len() != g_args.len() {
        return None;
    }
    to_option(check_cong(&premises, f_args, g_args))
}
