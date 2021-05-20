use super::to_option;

use crate::ast::*;

use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::collections::HashMap;

pub fn la_rw_eq(clause: &[ByRefRc<Term>], _: Vec<&ProofCommand>, _: &[ProofArg]) -> Option<()> {
    if clause.len() != 1 {
        return None;
    }
    let ((t_1, u_1), ((t_2, u_2), (u_3, t_3))) = match_term!(
        (= (= t u) (and (<= t u) (<= u t))) = clause[0]
    )?;
    to_option(t_1 == t_2 && t_2 == t_3 && u_1 == u_2 && u_2 == u_3)
}

pub fn la_disequality(
    clause: &[ByRefRc<Term>],
    _: Vec<&ProofCommand>,
    _: &[ProofArg],
) -> Option<()> {
    if clause.len() != 1 {
        return None;
    }
    let ((t1_1, t2_1), (t1_2, t2_2), (t2_3, t1_3)) = match_term!(
        (or (= t1 t2) (not (<= t1 t2)) (not (<= t2 t1))) = clause[0]
    )?;
    to_option(t1_1 == t1_2 && t1_2 == t1_3 && t2_1 == t2_2 && t2_2 == t2_3)
}

/// Converts a rational represented with division and negation to the resulting rational value. For
/// example, the term "(/ (- 5) 2)" is converted to the rational value "-2.5".
fn simple_operation_to_rational(term: &Term) -> Option<BigRational> {
    // TODO: Add tests for this
    if let Some((n, d)) = match_term!((/ n d) = term) {
        Some(simple_operation_to_rational(n)? / simple_operation_to_rational(d)?)
    } else if let Some(t) = match_term!((-t) = term) {
        Some(-simple_operation_to_rational(t)?)
    } else {
        term.as_ratio()
    }
}

/// Takes a nested sequence of additions, subtractions and negations, and flattens it to a list of
/// terms and the polarity that they appear in. For example, the term "(+ (- x y) (+ (- z) w))" is
/// flattened to `[(x, true), (y, false), (z, false), (w, true)]`, where `true` representes
/// positive polarity.
fn flatten_sum(term: &Term) -> Vec<(&Term, bool)> {
    // TODO: Add tests for this
    if let Some(args) = match_term!((+ ...) = term) {
        args.iter().flat_map(|t| flatten_sum(t.as_ref())).collect()
    } else if let Some(t) = match_term!((-t) = term) {
        let mut result = flatten_sum(t);
        result.iter_mut().for_each(|item| item.1 = !item.1);
        result
    } else if let Some(args) = match_term!((- ...) = term) {
        let mut result = flatten_sum(&args[0]);
        result.extend(args[1..].iter().flat_map(|t| {
            flatten_sum(t.as_ref())
                .into_iter()
                .map(|(t, polarity)| (t, !polarity))
        }));
        result
    } else {
        vec![(term, true)]
    }
}

/// Takes a disequality term and returns its negation, represented by an operator and arguments.
/// The disequality can be:
/// * An application of the "<", ">", "<=" or ">=" operators
/// * The negation of an application of any of these operator
/// * The negation of an application of the "=" operator
fn negate_disequality(term: &Term) -> Option<(Operator, &[ByRefRc<Term>])> {
    // TODO: Add tests for this
    use Operator::*;

    fn negate_operator(op: Operator) -> Option<Operator> {
        Some(match op {
            LessThan => GreaterEq,
            GreaterThan => LessEq,
            LessEq => GreaterThan,
            GreaterEq => LessThan,
            _ => return None,
        })
    }

    if let Some(Term::Op(op, args)) = match_term!((not t) = term) {
        if matches!(op, GreaterEq | LessEq | GreaterThan | LessThan | Eq) {
            return Some((*op, args));
        }
    } else if let Term::Op(op, args) = term {
        return Some((negate_operator(*op)?, args));
    }
    None
}

/// A linear combination, represented by a hash map from non-constant terms to their coefficients,
/// plus a constant term. This is also used to represent a disequality, in which case the left side
/// is the non-constant terms and their coefficients, and the right side is the constant term.
struct LinearComb<'a>(HashMap<&'a Term, BigRational>, BigRational);

impl<'a> LinearComb<'a> {
    fn new() -> Self {
        Self(HashMap::new(), BigRational::zero())
    }

    /// Builds a linear combination from a term. Only one constant term is allowed.
    fn from_term(term: &'a Term) -> Option<Self> {
        let mut result = Self(HashMap::new(), BigRational::zero());
        let mut constant_is_set = false;
        for (arg, polarity) in flatten_sum(term) {
            let polarity_coeff = match polarity {
                true => BigRational::one(),
                false => -BigRational::one(),
            };
            match match_term!((* a b) = arg) {
                Some((a, b)) => {
                    let (var, coeff) = match (a.as_ratio(), b.as_ratio()) {
                        (None, None) => (arg, BigRational::one()),
                        (None, Some(r)) => (a, r),
                        (Some(r), None) => (b, r),
                        (Some(_), Some(_)) => return None,
                    };
                    result.insert(var, coeff * polarity_coeff);
                }
                None => match arg.as_ratio() {
                    Some(r) => {
                        if constant_is_set {
                            return None;
                        }
                        result.1 = r * polarity_coeff;
                        constant_is_set = true;
                    }
                    None => result.insert(arg, polarity_coeff),
                },
            };
        }
        Some(result)
    }

    fn insert(&mut self, key: &'a Term, value: BigRational) {
        use std::collections::hash_map::Entry;

        match self.0.entry(key) {
            Entry::Occupied(mut e) => {
                let new_value = e.get() + value;
                if new_value.is_zero() {
                    e.remove();
                } else {
                    e.insert(new_value);
                }
            }
            Entry::Vacant(e) => {
                e.insert(value);
            }
        }
    }

    fn add(mut self, other: Self) -> Self {
        for (var, coeff) in other.0 {
            self.insert(var, coeff)
        }
        self.1 += other.1;
        self
    }

    fn mul(&mut self, scalar: BigRational) {
        for coeff in self.0.values_mut() {
            *coeff *= &scalar;
        }
        self.1 *= &scalar;
    }

    fn neg(&mut self) {
        // We multiply by -1 instead of using the unary "-" operator because that would require
        // cloning. There is no simple way to negate in place
        self.mul(-BigRational::one());
    }

    fn sub(self, mut other: Self) -> Self {
        other.neg();
        self.add(other)
    }
}

pub fn la_generic(
    clause: &[ByRefRc<Term>],
    _: Vec<&ProofCommand>,
    args: &[ProofArg],
) -> Option<()> {
    if clause.len() != args.len() {
        return None;
    }
    let final_disequality = clause
        .iter()
        .zip(args)
        .map(|(phi, a)| {
            let phi = phi.as_ref();
            let a = match a {
                ProofArg::Term(a) => simple_operation_to_rational(a)?,
                ProofArg::Assign(_, _) => return None,
            };

            // Steps 1 and 2: Negate the disequality
            let (mut op, args) = negate_disequality(phi)?;
            let (s1, s2) = if args.len() == 2 {
                (args[0].as_ref(), args[1].as_ref())
            } else {
                return None;
            };
            let (s1, s2) = (LinearComb::from_term(s1)?, LinearComb::from_term(s2)?);

            // Step 3: Move all non constant terms to the left side, and the d terms to the right.
            // We move everything to the left side by subtracting s2 from s1
            let mut disequality = s1.sub(s2);
            disequality.1 = -disequality.1; // We negate d to move it to the other side

            // If the operator is < or <=, we flip the disequality so it is > or >=
            if op == Operator::LessThan {
                disequality.neg();
                op = Operator::GreaterThan;
            } else if op == Operator::LessEq {
                disequality.neg();
                op = Operator::GreaterEq;
            }

            // Step 4: Apply strengthening rules
            match op {
                Operator::GreaterEq if disequality.1.is_integer() => (),
                Operator::GreaterThan | Operator::GreaterEq => {
                    disequality.1 = disequality.1.floor() + BigRational::one();
                    op = Operator::GreaterEq;
                }
                Operator::LessThan | Operator::LessEq => unreachable!(),
                _ => (),
            }

            // Step 5: Multiply disequality by a
            let a = match op {
                Operator::Eq => a,
                _ => a.abs(),
            };
            disequality.mul(a);

            Some((op, disequality))
        })
        .try_fold((Operator::Eq, LinearComb::new()), |(acc_op, acc), item| {
            let (op, diseq) = item?;
            let new_acc = acc.add(diseq);
            let new_op = match (acc_op, op) {
                (_, Operator::GreaterEq) => Operator::GreaterEq,
                (Operator::Eq, Operator::GreaterThan) => Operator::GreaterThan,
                _ => acc_op,
            };
            Some((new_op, new_acc))
        })?;

    let (op, LinearComb(left_side, right_side)) = final_disequality;

    // The left side must be empty, that is, equal to 0
    if !left_side.is_empty() {
        return None;
    }

    let is_disequality_true = {
        use std::cmp::Ordering;
        use Operator::*;

        // If the operator encompasses the actual relationship between 0 and the right side, the
        // disequality is true
        match BigRational::zero().cmp(&right_side) {
            Ordering::Less => matches!(op, LessThan | LessEq),
            Ordering::Equal => matches!(op, LessEq | GreaterEq | Eq),
            Ordering::Greater => matches!(op, GreaterThan | GreaterEq),
        }
    };

    // The final disequality must be contradictory
    to_option(!is_disequality_true)
}
