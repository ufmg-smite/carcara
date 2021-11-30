use super::{BindingList, Operator, ProofArg, ProofCommand, ProofStep, Rc, Sort, Term, Terminal};
use ahash::AHashSet;

/// A trait that implements less strict definitions of equality for terms. This trait represents
/// two definitions of equality that differ from `PartialEq`:
/// - `DeepEq::eq` implements a "deep" equality, meaning that it compares `ast::Rc`s by value,
/// instead of by reference
/// - `DeepEq::eq_modulo_reordering` is also a "deep" equality, but it considers "=" terms that are
/// "reflections" of each other as equal, meaning the terms "(= a b)" and "(= b a)" are considered
/// equal by this method
pub trait DeepEq {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool;
}

pub fn deep_eq<T: DeepEq>(a: &T, b: &T) -> bool {
    DeepEq::eq(&mut DeepEqualityChecker::new(false), a, b)
}

pub fn deep_eq_modulo_reordering<T: DeepEq>(a: &T, b: &T) -> bool {
    DeepEq::eq(&mut DeepEqualityChecker::new(true), a, b)
}

pub struct DeepEqualityChecker {
    cache: AHashSet<(Rc<Term>, Rc<Term>)>,
    is_mod_reordering: bool,
}

impl DeepEqualityChecker {
    fn new(is_mod_reordering: bool) -> Self {
        Self {
            cache: AHashSet::new(),
            is_mod_reordering,
        }
    }
}

impl DeepEq for Rc<Term> {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        if a == b || checker.cache.contains(&(a.clone(), b.clone())) {
            true
        } else {
            let result = DeepEq::eq(checker, a.as_ref(), b.as_ref());
            if result {
                checker.cache.insert((a.clone(), b.clone()));
            }
            result
        }
    }
}

impl DeepEq for Term {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (Term::App(f_a, args_a), Term::App(f_b, args_b)) => {
                DeepEq::eq(checker, f_a, f_b) && DeepEq::eq(checker, args_a, args_b)
            }
            (Term::Op(op_a, args_a), Term::Op(op_b, args_b)) => {
                if checker.is_mod_reordering {
                    if let (Operator::Equals, [a_1, a_2], Operator::Equals, [b_1, b_2]) =
                        (op_a, args_a.as_slice(), op_b, args_b.as_slice())
                    {
                        // If the term is an equality of two terms, we also check if they would be
                        // equal if one of them was flipped
                        return DeepEq::eq(checker, &(a_1, a_2), &(b_1, b_2))
                            || DeepEq::eq(checker, &(a_1, a_2), &(b_2, b_1));
                    }
                }
                // General case
                op_a == op_b && DeepEq::eq(checker, args_a, args_b)
            }
            (Term::Sort(a), Term::Sort(b)) => DeepEq::eq(checker, a, b),
            (Term::Terminal(a), Term::Terminal(b)) => match (a, b) {
                (Terminal::Var(iden_a, sort_a), Terminal::Var(iden_b, sort_b)) => {
                    iden_a == iden_b && DeepEq::eq(checker, sort_a, sort_b)
                }
                (a, b) => a == b,
            },
            (Term::Quant(q_a, binds_a, a), Term::Quant(q_b, binds_b, b)) => {
                q_a == q_b && DeepEq::eq(checker, binds_a, binds_b) && DeepEq::eq(checker, a, b)
            }
            (Term::Choice(var_a, a), Term::Choice(var_b, b)) => {
                DeepEq::eq(checker, var_a, var_b) && DeepEq::eq(checker, a, b)
            }
            (Term::Let(binds_a, a), Term::Let(binds_b, b)) => {
                DeepEq::eq(checker, binds_a, binds_b) && DeepEq::eq(checker, a, b)
            }
            _ => false,
        }
    }
}

impl DeepEq for BindingList {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        DeepEq::eq(checker, &a.0, &b.0)
    }
}

impl DeepEq for Sort {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (Sort::Function(sorts_a), Sort::Function(sorts_b)) => {
                DeepEq::eq(checker, sorts_a, sorts_b)
            }
            (Sort::Atom(a, sorts_a), Sort::Atom(b, sorts_b)) => {
                a == b && DeepEq::eq(checker, sorts_a, sorts_b)
            }
            (Sort::Bool, Sort::Bool)
            | (Sort::Int, Sort::Int)
            | (Sort::Real, Sort::Real)
            | (Sort::String, Sort::String) => true,
            (Sort::Array(x_a, y_a), Sort::Array(x_b, y_b)) => {
                DeepEq::eq(checker, x_a, x_b) && DeepEq::eq(checker, y_a, y_b)
            }
            _ => false,
        }
    }
}

impl<T: DeepEq> DeepEq for &T {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        DeepEq::eq(checker, *a, *b)
    }
}

impl<T: DeepEq> DeepEq for Vec<T> {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        a.len() == b.len()
            && a.iter()
                .zip(b.iter())
                .all(|(a, b)| DeepEq::eq(checker, a, b))
    }
}

impl<T: DeepEq, U: DeepEq> DeepEq for (T, U) {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        DeepEq::eq(checker, &a.0, &b.0) && DeepEq::eq(checker, &a.1, &b.1)
    }
}

impl DeepEq for String {
    fn eq(_: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        a == b
    }
}

impl DeepEq for ProofArg {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (ProofArg::Term(a), ProofArg::Term(b)) => DeepEq::eq(checker, a, b),
            (ProofArg::Assign(sa, ta), ProofArg::Assign(sb, tb)) => {
                sa == sb && DeepEq::eq(checker, ta, tb)
            }
            _ => false,
        }
    }
}

impl DeepEq for ProofCommand {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        match (a, b) {
            (
                ProofCommand::Assume { index: a_index, term: a_term },
                ProofCommand::Assume { index: b_index, term: b_term },
            ) => a_index == b_index && DeepEq::eq(checker, a_term, b_term),
            (ProofCommand::Step(a), ProofCommand::Step(b)) => DeepEq::eq(checker, a, b),
            _ => false,
        }
    }
}

impl DeepEq for ProofStep {
    fn eq(checker: &mut DeepEqualityChecker, a: &Self, b: &Self) -> bool {
        DeepEq::eq(checker, &a.clause, &b.clause)
            && a.rule == b.rule
            && a.premises == b.premises
            && DeepEq::eq(checker, &a.args, &b.args)
    }
}
