use super::{
    assert_clause_len, assert_num_premises, get_premise_term, CheckerError, RuleArgs, RuleResult,
};
use crate::{ast::*, checker::error::CongruenceError};

pub fn eq_congruent(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 2..)?;

    let premises = conclusion[..conclusion.len() - 1]
        .iter()
        .map(Rc::remove_negation_err);
    let conclusion = match_term_err!((= f g) = conclusion.last().unwrap())?;

    generic_congruent_rule(premises, conclusion)
}

pub fn eq_congruent_pred(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 3..)?;

    let premises = conclusion[..conclusion.len() - 2]
        .iter()
        .map(Rc::remove_negation_err);

    let (p, q) = (
        &conclusion[conclusion.len() - 2],
        &conclusion[conclusion.len() - 1],
    );
    let conclusion = match p.remove_negation() {
        Some(p) => (p, q),
        None => (p, q.remove_negation_err()?),
    };

    generic_congruent_rule(premises, conclusion)
}

/// A function to check congruence. Useful for the `eq_congruent` and `eq_congruent_pred`
/// rules. `premises` should be an iterator over the argument equalities, and `conclusion`
/// should be the two function applications.
fn generic_congruent_rule<'a, T>(premises: T, conclusion: (&Rc<Term>, &Rc<Term>)) -> RuleResult
where
    T: Iterator<Item = Result<&'a Rc<Term>, CheckerError>>,
{
    let premises: Vec<_> = premises
        .map(|term| match_term_err!((= t u) = term?))
        .collect::<Result<_, _>>()?;

    let (p, q) = conclusion;
    let (f_args, g_args) = match (p.as_ref(), q.as_ref()) {
        (Term::App(f, f_args), Term::App(g, g_args)) => match f == g {
            true => Ok((f_args, g_args)),
            false => Err(CongruenceError::DifferentFunctions(f.clone(), g.clone())),
        },
        (Term::Op(f, f_args), Term::Op(g, g_args)) => match f == g {
            true => Ok((f_args, g_args)),
            false => Err(CongruenceError::DifferentOperators(*f, *g)),
        },
        (Term::Op(..) | Term::App(..), _) => {
            Err(CongruenceError::NotApplicationOrOperation(q.clone()))
        }
        _ => Err(CongruenceError::NotApplicationOrOperation(p.clone())),
    }?;
    rassert!(
        f_args.len() == g_args.len(),
        CongruenceError::DifferentNumberOfArguments(f_args.len(), g_args.len())
    );
    {
        // We check the number of premises in two steps, because the error is different if there
        // too many or too few premises
        let n = premises.len();
        rassert!(n <= f_args.len(), CongruenceError::TooManyPremises);
        rassert!(
            n == f_args.len(),
            CongruenceError::MissingPremise(f_args[n].clone(), g_args[n].clone())
        );
    }

    for (i, (t, u)) in premises.into_iter().enumerate() {
        let (f, g) = (&f_args[i], &g_args[i]);
        rassert!(
            (f, g) == (t, u) || (f, g) == (u, t),
            CongruenceError::PremiseDoesntJustifyArgs {
                args: (f.clone(), g.clone()),
                premise: (t.clone(), u.clone())
            }
        );
    }
    Ok(())
}

/// Since the semantics of the `cong` rule is slightly different from that of `eq_congruent` and
/// `eq_congruent_pred`, we cannot just use the `generic_congruent_rule` function
fn check_cong<'a, I>(premises: &[(&'a Rc<Term>, &'a Rc<Term>)], f_args: I, g_args: I) -> RuleResult
where
    I: IntoIterator<Item = &'a Rc<Term>>,
{
    let mut premises = premises.iter().peekable();
    for (f_arg, g_arg) in f_args.into_iter().zip(g_args) {
        let expected = (f_arg.as_ref(), g_arg.as_ref());
        match premises.peek() {
            // If the next premise can justify that the arguments are equal, we consume it. We
            // prefer consuming the premise even if the arguments are directly equal
            Some((t, u)) if expected == (t, u) || expected == (u, t) => {
                premises.next();
            }

            // If the arguments are directly equal, we simply continue to the next pair of
            // arguments
            _ if f_arg == g_arg => (),

            // If the arguments are not directly equal, we needed a premise that can justify
            // their equality, so now we return an error
            None => {
                return Err(CongruenceError::MissingPremise(f_arg.clone(), g_arg.clone()).into());
            }
            Some((t, u)) => {
                return Err(CongruenceError::PremiseDoesntJustifyArgs {
                    args: (f_arg.clone(), g_arg.clone()),
                    premise: ((*t).clone(), (*u).clone()),
                }
                .into());
            }
        }
    }

    // At the end, all premises must have been consumed
    if premises.next().is_none() {
        Ok(())
    } else {
        Err(CongruenceError::TooManyPremises.into())
    }
}

pub fn cong(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    assert_num_premises(premises, 1..)?;

    let premises: Vec<_> = premises
        .iter()
        .map(|premise| match_term_err!((= t u) = get_premise_term(premise)?))
        .collect::<Result<_, _>>()?;

    let (f, g) = match_term_err!((= f g) = &conclusion[0])?;
    let (f_args, g_args) = match (f.as_ref(), g.as_ref()) {
        // Because of the way veriT handles equality terms, when the `cong` rule is called with two
        // equalities of two terms, the order of their arguments may be flipped. Because of that,
        // we have to treat this special case separately
        (Term::Op(Operator::Equals, f_args), Term::Op(Operator::Equals, g_args))
            if f_args.len() == 2 && g_args.len() == 2 =>
        {
            // We have to test all four possibilities: neither f nor g are flipped, only f is
            // flipped, only g is flipped, or both f and g are flipped
            let f_args_flipped: &[_] = &[f_args[1].clone(), f_args[0].clone()];
            let g_args_flipped: &[_] = &[g_args[1].clone(), g_args[0].clone()];

            // We store the result of the first possibility (when neither arguments are flipped),
            // because, if the checking fails in the end, we use it to get more sensible error
            // messages
            let original_result = check_cong(&premises, f_args, g_args);
            let any_valid = original_result.is_ok()
                || check_cong(&premises, f_args_flipped, g_args.as_slice()).is_ok()
                || check_cong(&premises, f_args.as_slice(), g_args_flipped).is_ok()
                || check_cong(&premises, f_args_flipped, g_args_flipped).is_ok();
            return if any_valid { Ok(()) } else { original_result };
        }

        (Term::App(f, f_args), Term::App(g, g_args)) => match f == g {
            true => Ok((f_args, g_args)),
            false => Err(CongruenceError::DifferentFunctions(f.clone(), g.clone())),
        },
        (Term::Op(f, f_args), Term::Op(g, g_args)) => match f == g {
            true => Ok((f_args, g_args)),
            false => Err(CongruenceError::DifferentOperators(*f, *g)),
        },
        (
            Term::ParamOp {
                op: f_op,
                op_args: f_op_args,
                args: f_args,
            },
            Term::ParamOp {
                op: g_op,
                args: g_args,
                op_args: g_op_args,
            },
        ) => {
            if f_op != g_op || f_op_args != g_op_args {
                Err(CongruenceError::DifferentIndexedOperators(
                    (*f_op, f_op_args.clone()),
                    (*g_op, g_op_args.clone()),
                ))
            } else {
                Ok((f_args, g_args))
            }
        }
        (Term::Op(..) | Term::App(..), _) => {
            // Note: this error also triggers when `f` is an operation and `g` an application, or
            // vice-versa. This means the error message may be a bit confusing
            Err(CongruenceError::NotApplicationOrOperation(g.clone()))
        }
        _ => Err(CongruenceError::NotApplicationOrOperation(f.clone())),
    }?;
    rassert!(
        f_args.len() == g_args.len(),
        CongruenceError::DifferentNumberOfArguments(f_args.len(), g_args.len())
    );
    check_cong(&premises, f_args, g_args)
}

pub fn ho_cong(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    use std::iter::once;

    assert_clause_len(conclusion, 1)?;
    assert_num_premises(premises, 1..)?;

    let premises: Vec<_> = premises
        .iter()
        .map(|premise| match_term_err!((= t u) = get_premise_term(premise)?))
        .collect::<Result<_, _>>()?;

    let (f, g) = match_term_err!((= f g) = &conclusion[0])?;
    let (f_args, g_args) = match (f.as_ref(), g.as_ref()) {
        (Term::App(f, f_args), Term::App(g, g_args)) => {
            rassert!(
                f_args.len() == g_args.len(),
                CongruenceError::DifferentNumberOfArguments(f_args.len(), g_args.len())
            );
            Ok((once(f).chain(f_args.iter()), once(g).chain(g_args.iter())))
        }
        (Term::App(..), _) => Err(CongruenceError::NotApplicationOrOperation(g.clone())),
        _ => Err(CongruenceError::NotApplicationOrOperation(f.clone())),
    }?;

    check_cong(&premises, f_args, g_args)
}
