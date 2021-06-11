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
}
