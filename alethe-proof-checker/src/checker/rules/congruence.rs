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
            // We have to test all four possibilites: neither f nor g are flipped, only f is
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

#[cfg(test)]
mod tests {
    #[test]
    fn eq_congruent() {
        test_cases! {
            definitions = "
                (declare-fun a () Int)
                (declare-fun b () Int)
                (declare-fun c () Int)
                (declare-fun x () Int)
                (declare-fun y () Int)
                (declare-fun z () Int)
                (declare-fun f (Int Int) Int)
                (declare-fun g (Int Int) Int)
                (declare-fun f-1 (Int) Int)
                (declare-fun f-3 (Int Int Int) Int)
            ",
            "Simple working examples" {
                "(step t1 (cl (not (= a b)) (= (f-1 a) (f-1 b))) :rule eq_congruent)": true,

                "(step t1 (cl (not (= a x)) (not (= b y)) (not (= c z))
                          (= (f-3 a b c) (f-3 x y z))) :rule eq_congruent)": true,

                "(step t1 (cl (not (= a x)) (not (= b y)) (not (= c z))
                          (= (* a b c) (* x y z))) :rule eq_congruent)": true,
            }
            "t_i and u_i are possibly flipped" {
                "(step t1 (cl (not (= b a)) (= (f-1 a) (f-1 b))) :rule eq_congruent)": true,

                "(step t1 (cl (not (= x a)) (not (= b y)) (not (= z c))
                          (= (f-3 a b c) (f-3 x y z))) :rule eq_congruent)": true,

                "(step t1 (cl (not (= a x)) (not (= b y)) (= (f x y) (f a b)))
                    :rule eq_congruent)": true,
            }
            "Clause term is not an inequality" {
                "(step t1 (cl (not (= a x)) (= b y) (= (f a b) (f x y))) :rule eq_congruent)": false,
            }
            "Final term is not an equality of applications" {
                "(step t1 (cl (not (= a x)) (not (= b y)) (= (+ a b) (f x y)))
                    :rule eq_congruent)": false,
            }
            "Functions are not the same" {
                "(step t1 (cl (not (= a x)) (not (= b y)) (= (f a b) (g x y)))
                    :rule eq_congruent)": false,

                "(step t1 (cl (not (= a x)) (not (= b y)) (not (= c z))
                          (= (* a b c) (+ x y z))) :rule eq_congruent)": false,
            }
            "Number of function arguments is not the same as the number of inequalities" {
                "(step t1 (cl (not (= a x)) (not (= b y)) (= (f-3 a b c) (f-3 x y z)))
                    :rule eq_congruent)": false,

                "(step t1 (cl (not (= a x)) (not (= b y)) (= (+ a b) (+ x y z)))
                    :rule eq_congruent)": false,
            }
            "Terms don't match" {
                "(step t1 (cl (not (= a x)) (not (= b y)) (= (f b a) (f x y)))
                    :rule eq_congruent)": false,

                "(step t1 (cl (not (= a x)) (not (= b y)) (= (f a b) (f c z)))
                    :rule eq_congruent)": false,
            }
        }
    }

    #[test]
    fn eq_congruent_pred() {
        test_cases! {
            definitions = "
                (declare-fun a () Bool)
                (declare-fun b () Bool)
                (declare-fun c () Bool)
                (declare-fun x () Bool)
                (declare-fun y () Bool)
                (declare-fun z () Bool)
                (declare-fun p (Bool Bool) Bool)
                (declare-fun q (Bool Bool) Bool)
                (declare-fun p-1 (Bool) Bool)
                (declare-fun p-3 (Bool Bool Bool) Bool)
            ",
            "Simple working examples" {
                "(step t1 (cl (not (= a b)) (not (p-1 a)) (p-1 b)) :rule eq_congruent_pred)": true,

                "(step t1 (cl (not (= a x)) (not (= b y)) (not (= c z))
                          (not (p-3 a b c)) (p-3 x y z)) :rule eq_congruent_pred)": true,

                "(step t1 (cl (not (= a x)) (not (= b y)) (not (= c z))
                          (not (and a b c)) (and x y z)) :rule eq_congruent_pred)": true,
            }
            "t_i and u_i are possibly flipped" {
                "(step t1 (cl (not (= b a)) (not (p-1 a)) (p-1 b)) :rule eq_congruent_pred)": true,

                "(step t1 (cl (not (= x a)) (not (= b y)) (not (= z c))
                          (not (p-3 a b c)) (p-3 x y z)) :rule eq_congruent_pred)": true,

                "(step t1 (cl (not (= a x)) (not (= b y)) (not (p x y)) (p a b))
                    :rule eq_congruent_pred)": true,
            }
            "Clause term is not an inequality" {
                "(step t1 (cl (not (= a x)) (= b y) (not (p a b)) (p x y))
                    :rule eq_congruent_pred)": false,
            }
            "Final two terms' order may be flipped" {
                "(step t1 (cl (not (= a x)) (not (= b y)) (p a b) (not (p x y)))
                    :rule eq_congruent_pred)": true,
            }
            "Functions are not the same" {
                "(step t1 (cl (not (= a x)) (not (= b y)) (not (p a b)) (q x y))
                    :rule eq_congruent_pred)": false,

                "(step t1 (cl (not (= a x)) (not (= b y)) (not (= c z))
                          (not (or a b c)) (and x y z)) :rule eq_congruent_pred)": false,
            }
            "Number of function arguments is not the same as the number of inequalities" {
                "(step t1 (cl (not (= a x)) (not (= b y)) (not (p-3 a b c)) (p-3 x y z))
                    :rule eq_congruent_pred)": false,

                "(step t1 (cl (not (= a x)) (not (= b y)) (not (and a b)) (and x y z))
                    :rule eq_congruent_pred)": false,
            }
            "Terms don't match" {
                "(step t1 (cl (not (= a x)) (not (= b y)) (not (p b a)) (p x y))
                    :rule eq_congruent_pred)": false,

                "(step t1 (cl (not (= a x)) (not (= b y)) (not (p a b)) (p c z))
                    :rule eq_congruent_pred)": false,
            }
        }
    }

    #[test]
    fn cong() {
        test_cases! {
            definitions = "
                (declare-sort T 0)
                (declare-fun a () T)
                (declare-fun b () T)
                (declare-fun c () T)
                (declare-fun d () T)
                (declare-fun f (T Bool T) T)
                (declare-fun g (T Bool T) T)
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
                (declare-fun x () Real)
                (declare-fun y () Real)
            ",
            "Simple working examples" {
                "(assume h1 (= a b))
                (assume h2 (= c d))
                (step t3 (cl (= (f b false c) (f a false d))) :rule cong :premises (h1 h2))": true,

                "(assume h1 (= p q))
                (assume h2 (= r s))
                (step t3 (cl (= (and p false s) (and q false r)))
                    :rule cong :premises (h1 h2))": true,
            }
            "Functions or operators don't match" {
                "(assume h1 (= a b))
                (assume h2 (= c d))
                (step t3 (cl (= (f b false c) (g a false d))) :rule cong :premises (h1 h2))": false,

                "(assume h1 (= p q))
                (assume h2 (= r s))
                (step t3 (cl (= (and p false s) (or q false r)))
                    :rule cong :premises (h1 h2))": false,
            }
            "No premises were given" {
                "(step t1 (cl (= (f a true c) (f a true c))) :rule cong)": false,
            }
            "Wrong number of premises" {
                "(assume h1 (= a b))
                (assume h2 (= p q))
                (step t3 (cl (= (f a p c) (f b q d))) :rule cong :premises (h1 h2))": false,

                "(assume h1 (= a b))
                (assume h2 (= p q))
                (assume h3 (= c d))
                (assume h4 (= r s))
                (step t5 (cl (= (f a p c) (f b q d))) :rule cong :premises (h1 h2 h3 h4))": false,
            }
            "Premise doesn't match expected terms" {
                "(assume h1 (= a b))
                (assume h2 (= r s))
                (assume h3 (= c d))
                (step t4 (cl (= (f a p c) (f b q d))) :rule cong :premises (h1 h2 h3))": false,

                "(assume h1 (= a b))
                (assume h2 (= c d))
                (assume h3 (= p q))
                (step t4 (cl (= (f a p c) (f b q d))) :rule cong :premises (h1 h2 h3))": false,
            }
            "Should prefer consuming premise than relying on reflexivity" {
                "(assume h1 (= false false))
                (assume h2 (= r s))
                (step t3 (cl (= (and false false s) (and false false r)))
                    :rule cong :premises (h1 h2))": true,

                "(assume h1 (= (- 1.0) (- 1.0)))
                (step t2 (cl (= (< x (- 1.0)) (< x (- 1.0)))) :rule cong :premises (h1))": true,
            }
            "Argument order may be flipped if operator is \"=\"" {
                "(assume h1 (= x y))
                (step t2 (cl (= (= 0.0 x) (= y 0.0))) :rule cong :premises (h1))": true,

                "(assume h1 (= x y))
                (step t2 (cl (= (= x 0.0) (= 0.0 y))) :rule cong :premises (h1))": true,

                "(assume h1 (= a b)) (assume h2 (= c d))
                (step t3 (cl (= (= c a) (= b d))) :rule cong :premises (h1 h2))": true,

                "(assume h1 (= a b)) (assume h2 (= c d))
                (step t3 (cl (= (= a c) (= d b))) :rule cong :premises (h1 h2))": true,

                "(assume h1 (= a b)) (assume h2 (= c d))
                (step t3 (cl (= (= c a) (= d b))) :rule cong :premises (h1 h2))": true,
            }
        }
    }

    #[test]
    fn ho_cong() {
        test_cases! {
            definitions = "
                (declare-sort T 0)
                (declare-fun a () T)
                (declare-fun b () T)
                (declare-fun f (T Int) T)
                (declare-fun g (T Int) T)
                (declare-fun p () Bool)
                (declare-fun q () Bool)
            ",
            "Simple working examples" {
                "(assume h1 (= f g))
                (assume h2 (= a b))
                (step t3 (cl (= (f a 0) (g b 0))) :rule ho_cong :premises (h1 h2))": true,

                "(assume h1 (= f (lambda ((a T) (x Int)) a)))
                (assume h2 (= 0 1))
                (step t3 (cl (= (f b 0) ((lambda ((a T) (x Int)) a) b 1)))
                    :rule ho_cong :premises (h1 h2))": true,
            }
            "Can't be used with operators" {
                "(assume h1 (= p q))
                (step t3 (cl (= (and p true) (and q true))) :rule ho_cong :premises (h1))": false,
            }
        }
    }
}
