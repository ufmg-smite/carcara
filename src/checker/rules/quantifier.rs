use super::{to_option, RuleArgs};
use crate::{ast::*, utils::DedupIterator};
use std::collections::{HashMap, HashSet};

pub fn forall_inst(
    RuleArgs {
        conclusion,
        args,
        pool,
        ..
    }: RuleArgs,
) -> Option<()> {
    rassert!(conclusion.len() == 1);

    let (forall_term, substituted) = match_term!((or (not f) s) = conclusion[0], RETURN_RCS)?;
    let (quant, bindings, original) = forall_term.unwrap_quant()?;
    rassert!(quant == Quantifier::Forall);

    rassert!(args.len() == bindings.len());

    let mut substitutions: HashMap<_, _> = bindings
        .iter()
        .zip(args)
        .map(|((binding_name, binding_sort), arg)| {
            let (arg_name, arg_value) = match arg {
                ProofArg::Assign(name, value) => (name, value),
                ProofArg::Term(_) => return None,
            };
            let arg_sort = arg_value.sort();
            rassert!(arg_name == binding_name && binding_sort.as_ref() == arg_sort);

            // We must use `pool.add_term` so we don't create a new term for the argument sort, and
            // instead use the one already in the term pool
            let ident_term = terminal!(var arg_name; pool.add_term(arg_sort.clone()));
            Some((pool.add_term(ident_term), arg_value.clone()))
        })
        .collect::<Option<_>>()?;

    // Equalities may be reordered in the final term, so we use `DeepEq::eq_modulo_reordering`
    to_option(DeepEq::eq_modulo_reordering(
        &pool.apply_substitutions(original, &mut substitutions),
        substituted,
    ))
}

pub fn qnt_join(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    rassert!(conclusion.len() == 1);

    let (left, right) = match_term!((= l r) = conclusion[0])?;
    let (q_1, bindings_1, left) = left.unwrap_quant()?;
    let (q_2, bindings_2, left) = left.unwrap_quant()?;
    let (q_3, bindings_3, right) = right.unwrap_quant()?;

    rassert!(q_1 == q_2 && q_2 == q_3 && left == right);

    let combined = bindings_1.iter().chain(bindings_2).dedup();
    to_option(bindings_3.iter().eq(combined))
}

pub fn qnt_rm_unused(
    RuleArgs {
        conclusion, pool, ..
    }: RuleArgs,
) -> Option<()> {
    rassert!(conclusion.len() == 1);

    let (left, right) = match_term!((= l r) = conclusion[0])?;
    let (q_1, bindings_1, phi_1) = left.unwrap_quant()?;
    let (q_2, bindings_2, phi_2) = right.unwrap_quant()?;
    rassert!(q_1 == q_2 && phi_1 == phi_2);
    let free_vars = pool.free_vars(phi_1);
    to_option(
        bindings_1
            .iter()
            .filter(|(var, _)| free_vars.contains(var))
            .eq(bindings_2),
    )
}

fn negation_normal_form(
    pool: &mut TermPool,
    term: &ByRefRc<Term>,
    polarity: bool,
) -> ByRefRc<Term> {
    if let Some(inner) = match_term!((not t) = term, RETURN_RCS) {
        negation_normal_form(pool, inner, !polarity)
    } else if let Term::Op(op @ (Operator::And | Operator::Or), args) = term.as_ref() {
        let op = match (op, polarity) {
            (op, true) => *op,
            (Operator::And, false) => Operator::Or,
            (Operator::Or, false) => Operator::And,
            (_, false) => unreachable!(),
        };
        let args = args
            .iter()
            .map(|a| negation_normal_form(pool, a, polarity))
            .collect();
        pool.add_term(Term::Op(op, args))
    } else if let Some((p, q)) = match_term!((=> p q) = term, RETURN_RCS) {
        let a = negation_normal_form(pool, p, !polarity);
        let b = negation_normal_form(pool, q, polarity);
        let c = negation_normal_form(pool, q, !polarity);
        let d = negation_normal_form(pool, p, polarity);

        match polarity {
            true => build_term!(pool, (and (or {a} {b}) (or {c} {d}))),
            false => build_term!(pool, (or (and {a} {b}) (and {c} {d}))),
        }
    } else if let Some((p, q, r)) = match_term!((ite p q r) = term, RETURN_RCS) {
        let a = negation_normal_form(pool, p, !polarity);
        let b = negation_normal_form(pool, q, polarity);
        let c = negation_normal_form(pool, p, polarity);
        let d = negation_normal_form(pool, r, polarity);

        match polarity {
            true => build_term!(pool, (and (or {a} {b}) (or {c} {d}))),
            false => build_term!(pool, (or (and {a} {b}) (and {c} {d}))),
        }
    } else if let Some((quant, bindings, inner)) = term.unwrap_quant() {
        let quant = if !polarity { !quant } else { quant };
        let inner = negation_normal_form(pool, inner, polarity);
        pool.add_term(Term::Quant(quant, bindings.clone(), inner))
    } else {
        match polarity {
            true => term.clone(),
            false => build_term!(pool, (not {term.clone()})),
        }
    }
}

// This represents a formula in conjunctive normal form, that is, it is a conjunction of clauses,
// which are disjunctions of literals
type CnfFormula = Vec<Vec<ByRefRc<Term>>>;

fn distribute(formulae: &[CnfFormula]) -> CnfFormula {
    match formulae {
        [formula] => formula.iter().map(|clause| clause.to_vec()).collect(),
        [tail @ .., head] => {
            let tail = distribute(tail);
            let mut acc = Vec::with_capacity(head.len() * tail.len());
            for head_clause in head {
                for tail_clause in &tail {
                    let mut result = Vec::with_capacity(tail_clause.len() + head_clause.len());
                    result.extend(tail_clause.iter().cloned());
                    result.extend(head_clause.iter().cloned());
                    acc.push(result)
                }
            }
            acc
        }
        [] => vec![Vec::new()],
    }
}

fn conjunctive_normal_form(term: &ByRefRc<Term>) -> CnfFormula {
    match term.as_ref() {
        Term::Op(Operator::And, args) => args.iter().flat_map(conjunctive_normal_form).collect(),
        Term::Op(Operator::Or, args) => {
            let args: Vec<_> = args.iter().map(conjunctive_normal_form).collect();
            distribute(&args)
        }
        _ => vec![vec![term.clone()]],
    }
}

pub fn qnt_cnf(
    RuleArgs {
        conclusion, pool, ..
    }: RuleArgs,
) -> Option<()> {
    rassert!(conclusion.len() == 1);

    let (l_bindings, phi, r_bindings, phi_prime) = {
        let (l, r) = match_term!((or (not l) r) = conclusion[0])?;
        let (l_q, l_b, phi) = l.unwrap_quant()?;
        let (r_q, r_b, phi_prime) = r.unwrap_quant()?;
        rassert!(l_q == r_q && l_q == Quantifier::Forall);
        (l_b, phi, r_b, phi_prime)
    };

    // TODO: Handle extra bindings added by prenexing
    let r_bindings = r_bindings.iter().collect::<HashSet<_>>();
    rassert!(l_bindings.iter().all(|b| r_bindings.contains(b)));

    // This is currently a WIP, and doesn't work for most cases
    // TODO: Implement prenexing step
    let clauses: Vec<_> = {
        let nnf = negation_normal_form(pool, phi, true);
        conjunctive_normal_form(&nnf)
            .into_iter()
            .map(|c| match c.as_slice() {
                [] => unreachable!(),
                [term] => term.clone(),
                _ => pool.add_term(Term::Op(Operator::Or, c)),
            })
            .collect()
    };
    to_option(clauses.iter().any(|term| term == phi_prime))
}

#[cfg(test)]
mod tests {
    #[test]
    fn forall_inst() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun a () Real)
                (declare-fun b () Real)
                (declare-fun x () Real)
            ",
            "Simple working examples" {
                "(step t1 (cl (or (not (forall ((p Bool)) p)) q))
                    :rule forall_inst :args ((:= p q)))": true,

                "(step t1 (cl (or (not (forall ((x Real) (y Real)) (= x y))) (= a b)))
                    :rule forall_inst :args ((:= x a) (:= y b)))": true,

                "(step t1 (cl (or (not (forall ((x Real)) (= x a))) (= a a)))
                    :rule forall_inst :args ((:= x a)))": true,

                "(step t1 (cl (or (not (forall ((p Bool)) p)) (ite q (= a b) (and (= a 0.0) true))))
                    :rule forall_inst :args ((:= p (ite q (= a b) (and (= a 0.0) true)))))": true,
            }
            "Equalities may be flipped" {
                "(step t1 (cl (or (not (forall ((x Real) (y Real)) (and (= x y) (= 1 0))))
                    (and (= b a) (= 1 0)))) :rule forall_inst :args ((:= x a) (:= y b)))": true,
            }
            "Argument is not in quantifier bindings" {
                "(step t1 (cl (or (not (forall ((x Real)) (= x a))) (= b 0.0)))
                    :rule forall_inst :args ((:= x b) (:= a 0.0)))": false,
            }
            "Binding has no associated substitution" {
                "(step t1 (cl (or (not (forall ((x Real) (y Real)) (= x x))) (= a a)))
                    :rule forall_inst :args ((:= x a)))": false,
            }
            "Substitution was not applied" {
                "(step t1 (cl (or (not (forall ((x Real) (y Real)) (= x y))) (= x b)))
                    :rule forall_inst :args ((:= x a) (:= y b)))": false,
            }
            "Applied substitution was not passed as argument" {
                "(step t1 (cl (or (not (forall ((x Real) (y Real)) (= x y))) (= a b)))
                    :rule forall_inst :args ((:= x a)))": false,
            }
            "Wrong type of rule argument" {
                "(step t1 (cl (or (not (forall ((x Real) (y Real)) (= x y))) (= a b)))
                    :rule forall_inst :args ((:= x a) b))": false,
            }
        }
    }

    #[test]
    fn qnt_join() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun a () Real)
                (declare-fun b () Real)
                (declare-fun x () Real)
            ",
            "Simple working examples" {
                "(step t1 (cl (=
                    (forall ((x Real)) (forall ((y Real)) (= x y)))
                    (forall ((x Real) (y Real)) (= x y))
                )) :rule qnt_join)": true,

                "(step t1 (cl (=
                    (forall ((x Real) (y Real)) (forall ((z Real) (w Real)) (= (+ x y) (+ z w))))
                    (forall ((x Real) (y Real) (z Real) (w Real)) (= (+ x y) (+ z w)))
                )) :rule qnt_join)": true,
            }
            "Bindings in wrong order" {
                "(step t1 (cl (=
                    (forall ((x Real)) (forall ((y Real)) (= x y)))
                    (forall ((y Real) (x Real)) (= x y))
                )) :rule qnt_join)": false,

                "(step t1 (cl (=
                    (forall ((x Real) (y Real)) (forall ((z Real) (w Real)) (= (+ x y) (+ z w))))
                    (forall ((z Real) (y Real) (w Real) (x Real)) (= (+ x y) (+ z w)))
                )) :rule qnt_join)": false,
            }
            "Removing duplicates" {
                "(step t1 (cl (=
                    (forall ((p Bool)) (forall ((p Bool)) p))
                    (forall ((p Bool)) p)
                )) :rule qnt_join)": true,

                "(step t1 (cl (=
                    (forall ((x Real) (y Real)) (forall ((y Real) (z Real)) (distinct x y z)))
                    (forall ((x Real) (y Real) (z Real)) (distinct x y z))
                )) :rule qnt_join)": true,

                "(step t1 (cl (=
                    (forall ((x Real) (y Real)) (forall ((x Real) (y Real)) (= x y)))
                    (forall ((x Real) (y Real)) (= x y))
                )) :rule qnt_join)": true,

                "(step t1 (cl (=
                    (forall ((x Real) (y Real)) (forall ((z Real) (x Real)) (distinct x y z)))
                    (forall ((x Real) (y Real) (z Real) (x Real)) (distinct x y z))
                )) :rule qnt_join)": false,
            }
        }
    }

    #[test]
    fn qnt_rm_unused() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun a () Real)
                (declare-fun b () Real)
                (declare-fun x () Real)
            ",
            "Simple working examples" {
                "(step t1 (cl (=
                    (forall ((x Real) (y Real) (z Real)) (= x z))
                    (forall ((x Real) (z Real)) (= x z))
                )) :rule qnt_rm_unused)": true,

                "(step t1 (cl (=
                    (forall ((x Real) (y Real) (z Real) (w Real)) (= y y))
                    (forall ((y Real)) (= y y))
                )) :rule qnt_rm_unused)": true,
            }
            "Bindings in wrong order" {
                "(step t1 (cl (=
                    (forall ((x Real) (y Real) (z Real)) (= x z))
                    (forall ((z Real) (x Real)) (= x z))
                )) :rule qnt_rm_unused)": false,
            }
            "Not all unused bindings were removed" {
                "(step t1 (cl (=
                    (forall ((x Real) (y Real) (z Real) (w Real)) (= y y))
                    (forall ((y Real) (w Real)) (= y y))
                )) :rule qnt_rm_unused)": false,
            }
        }
    }
}
