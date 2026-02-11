use super::{assert_clause_len, assert_eq, RuleArgs, RuleResult};
use crate::{
    ast::{Operator, Rc, Sort, Term},
    checker::{
        error::PolynomialError,
        rules::{assert_is_expected, assert_num_premises, get_premise_term},
    },
};
use indexmap::{map::Entry, IndexMap};
use rug::{ops::NegAssign, Integer, Rational};

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
struct Monomial(Vec<Rc<Term>>);

impl Monomial {
    fn mul(mut self, other: Self) -> Self {
        self.0.extend(other.0);
        self.0.sort_unstable_by_key(Rc::as_ptr);
        self
    }
}

#[derive(Debug, Clone)]
struct Polynomial(pub(crate) IndexMap<Monomial, Rational>, pub(crate) Rational);

impl Polynomial {
    fn new() -> Self {
        Self(IndexMap::new(), Rational::new())
    }

    /// Builds a polynomial from a term. Takes a term with nested additions, subtractions and
    /// multiplications, and flattens it to polynomial, calculating the coefficient of each
    /// monomial.
    fn from_term(term: &Rc<Term>) -> Self {
        let mut result = Self::new();
        result.add_term(term, &Rational::from(1));
        result
    }

    /// Processes a term and adds it to the polynomial.
    fn add_term(&mut self, term: &Rc<Term>, coeff: &Rational) {
        // We traverse the term without using a cache for the same reasons as `LinearComb`.
        match term.as_ref() {
            Term::Op(Operator::Add | Operator::BvAdd, args) => {
                for a in args {
                    self.add_term(a, coeff);
                }
            }
            Term::Op(Operator::Sub | Operator::BvNeg, args) if args.len() == 1 => {
                self.add_term(&args[0], &coeff.as_neg());
            }
            Term::Op(Operator::Sub | Operator::BvSub, args) => {
                self.add_term(&args[0], coeff);
                for a in &args[1..] {
                    self.add_term(a, &coeff.as_neg());
                }
            }
            Term::Op(Operator::Mult | Operator::BvMul, args) => {
                let result = args.iter().map(Self::from_term).reduce(Self::mul).unwrap();
                for (var, inner_coeff) in result.0 {
                    self.insert(var, inner_coeff * coeff);
                }
                self.1 += coeff * result.1;
            }
            Term::Op(Operator::RealDiv, args)
                if args.len() == 2 && args[1].as_fraction().is_some_and(|r| !r.is_zero()) =>
            {
                let r = args[1].as_fraction().unwrap();
                self.add_term(&args[0], &(coeff / r));
            }
            Term::Op(Operator::ToReal, args) => {
                self.add_term(&args[0], coeff);
            }
            // We check for division by zero separately because `.as_fraction` panics if the
            // denominator is zero. In this case, we consider the term an atom.
            Term::Op(Operator::RealDiv | Operator::IntDiv, args)
                if args.len() == 2 && args[1].as_fraction().is_some_and(|r| r.is_zero()) =>
            {
                self.insert(Monomial(vec![term.clone()]), coeff.clone());
            }
            _ => {
                if let Some(mut r) = term.as_fraction() {
                    r *= coeff;
                    self.1 += r;
                } else if let Some((value, _)) = term.as_bitvector() {
                    // The width is irrelevant for the normalization, overflow will be dealt with
                    // later, using the `modulo` method
                    self.1 += Rational::from(value) * coeff;
                } else {
                    self.insert(Monomial(vec![term.clone()]), coeff.clone());
                }
            }
        }
    }

    fn mul(self, other: Self) -> Self {
        let mut result = Self::new();
        for (x_1, c_1) in self.0 {
            for (x_2, c_2) in &other.0 {
                result.insert(x_1.clone().mul(x_2.clone()), c_1.clone() * c_2);
            }
            result.insert(x_1, c_1 * &other.1);
        }
        for (x_2, c_2) in other.0 {
            result.insert(x_2, c_2 * &self.1);
        }
        result.1 += self.1 * other.1;
        result
    }

    fn insert(&mut self, key: Monomial, value: Rational) {
        if value == 0 {
            return;
        }
        match self.0.entry(key) {
            Entry::Occupied(mut e) => {
                *e.get_mut() += value;
                if *e.get() == 0 {
                    e.swap_remove();
                }
            }
            Entry::Vacant(e) => {
                e.insert(value);
            }
        }
    }

    fn is_zero(&self) -> bool {
        self.0.is_empty() && self.1.is_zero()
    }

    fn add(mut self, other: Self) -> Self {
        for (var, coeff) in other.0 {
            self.insert(var, coeff);
        }
        self.1 += other.1;
        self
    }

    fn neg(&mut self) {
        for coeff in self.0.values_mut() {
            coeff.neg_assign();
        }
        self.1.neg_assign();
    }

    fn sub(self, mut other: Self) -> Self {
        other.neg();
        self.add(other)
    }

    fn modulo(mut self, n: &Integer) -> Option<Self> {
        for (_, coeff) in &mut self.0 {
            if !coeff.is_integer() {
                return None;
            }
            *coeff = coeff.numer().clone().modulo(n).into();
        }
        if self.1.is_integer() {
            self.1 = self.1.numer().clone().modulo(n).into();
            Some(self)
        } else {
            None
        }
    }
}

pub fn poly_simp(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (t, s) = match_term_err!((= t s) = &conclusion[0])?;
    let (t_norm, s_norm) = (Polynomial::from_term(t), Polynomial::from_term(s));
    if !t_norm.sub(s_norm).is_zero() {
        Err(PolynomialError::PolynomialsNotEqual(t.clone(), s.clone()).into())
    } else {
        Ok(())
    }
}

pub fn bv_poly_simp(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (t, s) = match_term_err!((= t s) = &conclusion[0])?;
    let width = match pool.sort(t).as_sort().unwrap() {
        Sort::BitVec(w) => *w,
        other => return Err(PolynomialError::ExpectedBvSort(other.clone()).into()),
    };
    let max = Integer::from(1) << width;
    let (t_norm, s_norm) = (
        Polynomial::from_term(t).modulo(&max).unwrap(),
        Polynomial::from_term(s).modulo(&max).unwrap(),
    );
    if !t_norm.sub(s_norm).is_zero() {
        Err(PolynomialError::PolynomialsNotEqual(t.clone(), s.clone()).into())
    } else {
        Ok(())
    }
}

pub fn poly_simp_rel(RuleArgs { conclusion, premises, .. }: RuleArgs) -> RuleResult {
    use Operator::*;

    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;
    let prem = get_premise_term(&premises[0])?;

    let ((c1, xs), (c2, ys)) = match_term_err!((= (* c1 xs) (* c2 ys)) = prem)?;
    let (x1, x2) =
        match_term_err!((to_real (- x1 x2)) = xs).or_else(|_| match_term_err!((- x1 x2) = xs))?;
    let (y1, y2) =
        match_term_err!((to_real (- y1 y2)) = ys).or_else(|_| match_term_err!((- y1 y2) = ys))?;

    let (c1, c2) = (c1.as_fraction_err()?, c2.as_fraction_err()?);
    for c in [&c1, &c2] {
        rassert!(!c.is_zero(), PolynomialError::CoeffIsZero(c.clone()));
    }

    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;
    match (left.as_op_err()?, right.as_op_err()?) {
        (
            (op @ (LessThan | LessEq | Equals | GreaterEq | GreaterThan), [l1, l2]),
            (op2, [r1, r2]),
        ) if op2 == op => {
            rassert!(
                op == Equals || c1.is_positive() == c2.is_positive(),
                PolynomialError::CoeffDifferentSignums(c1.clone(), c2.clone()),
            );

            assert_eq(l1, x1)?;
            assert_eq(l2, x2)?;
            assert_eq(r1, y1)?;
            assert_eq(r2, y2)?;
            Ok(())
        }
        ((op1, _), (op2, _)) => Err(PolynomialError::InvalidOperators(op1, op2).into()),
    }
}

pub fn bv_poly_simp_eq(RuleArgs { conclusion, premises, pool, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let ((c1, (x1, x2)), (c2, (y1, y2))) =
        match_term_err!((= (* c1 (- x1 x2)) (* c2 (- y1 y2))) = get_premise_term(&premises[0])?)?;

    let sort = pool.sort(c1);
    let Sort::BitVec(width) = sort.as_sort().unwrap() else {
        unreachable!() // The parser ensures that the sort is a bitvector sort
    };
    let one = pool.add(Term::new_bv(Integer::from(1), *width));
    assert_is_expected(c1, one.clone())?;
    assert_is_expected(c2, one)?;

    let ((l1, l2), (r1, r2)) = match_term_err!((= (= x1 x2) (= y1 y2)) = &conclusion[0])?;

    assert_eq(l1, x1)?;
    assert_eq(l2, x2)?;
    assert_eq(r1, y1)?;
    assert_eq(r2, y2)?;
    Ok(())
}
