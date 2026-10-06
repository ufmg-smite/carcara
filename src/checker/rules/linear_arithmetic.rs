use super::{RuleArgs, RuleResult, assert_clause_len, assert_eq, assert_num_args};
use crate::{
    ast::{pool::Pool, *},
    checker::error::{CheckerError, err, rassert},
};
use indexmap::{IndexMap, map::Entry};
use rug::{Integer, Rational, ops::NegAssign};
use std::fmt;

pub fn la_rw_eq(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= (= t u) (and (<= t u) (<= u t))) = &conclusion[0])?;
    Ok(())
}

/// Takes a disequality term and returns its negation, represented by an operator and two linear
/// combinations.
/// The disequality can be:
///
/// - An application of the `<`, `>`, `<=` or `>=` operators
/// - The negation of an application of one of these operators
/// - The negation of an application of the `=` operator
fn negate_disequality(term: &Rc<Term>) -> Result<(Operator, LinearComb, LinearComb), CheckerError> {
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

    fn inner(term: &Rc<Term>) -> Option<(Operator, &[Rc<Term>])> {
        if let Some(Term::Op(op, args)) = term.remove_negation().map(Rc::as_ref) {
            if matches!(op, GreaterEq | LessEq | GreaterThan | LessThan | Equals) {
                return Some((*op, args));
            }
        } else if let Term::Op(op, args) = term.as_ref() {
            return Some((negate_operator(*op)?, args));
        }
        None
    }

    let Some((op, args)) = inner(term) else {
        return err!("term '{term}' is not a valid disequality operation");
    };

    match args {
        [a, b] => Ok((op, LinearComb::from_term(a), LinearComb::from_term(b))),
        _ => err!("too many arguments in disequality '{term}'"),
    }
}

/// A linear combination, represented by a hash map from non-constant terms to their coefficients,
/// plus a constant term. This is also used to represent a disequality, in which case the left side
/// is the non-constant terms and their coefficients, and the right side is the constant term.
#[derive(Debug)]
pub struct LinearComb(pub(crate) IndexMap<Rc<Term>, Rational>, pub(crate) Rational);

impl LinearComb {
    fn new() -> Self {
        Self(IndexMap::new(), Rational::new())
    }

    /// Flattens a term and adds it to the linear combination, multiplying by the coefficient
    /// `coeff`. This method is only intended to be used in `LinearComb::from_term`.
    fn add_term(&mut self, term: &Rc<Term>, coeff: &Rational) {
        // A note on performance: this function traverses the term recursively without making use
        // of a cache, which means sometimes it has to recompute the result for the same term more
        // than once. However, an old implementation of this method that could use a cache showed
        // that making use of one can actually make the performance of this function worse.
        // Benchmarks showed that it would more than double the average time of the `la_generic`
        // rule, which makes extensive use of `LinerComb`s. Because of that, we prefer to not use
        // a cache here, and traverse the term naively.

        match term.as_ref() {
            Term::Op(Operator::Add, args) => {
                for a in args {
                    self.add_term(a, coeff);
                }
            }
            Term::Op(Operator::Sub, args) if args.len() == 1 => {
                self.add_term(&args[0], &coeff.as_neg());
            }
            Term::Op(Operator::Sub, args) => {
                self.add_term(&args[0], coeff);
                for a in &args[1..] {
                    self.add_term(a, &coeff.as_neg());
                }
            }
            Term::Op(Operator::Mult, args) if args.len() == 2 => {
                let (var, mut inner_coeff) = match (args[0].as_fraction(), args[1].as_fraction()) {
                    (None, Some(coeff)) => (&args[0], coeff),
                    (Some(coeff), _) => (&args[1], coeff),
                    (None, None) => return self.insert(term.clone(), coeff.clone()),
                };
                inner_coeff *= coeff;
                self.add_term(var, &inner_coeff);
            }
            _ => {
                if let Some(mut r) = term.as_fraction() {
                    r *= coeff;
                    self.1 += r;
                } else {
                    self.insert(term.clone(), coeff.clone());
                }
            }
        }
    }

    /// Builds a linear combination from a term. Takes a term with nested additions, subtractions
    /// and multiplications, and flattens it to linear combination, calculating the coefficient of
    /// each atom.
    fn from_term(term: &Rc<Term>) -> Self {
        let mut result = Self::new();
        result.add_term(term, &Rational::from(1));
        result
    }

    fn insert(&mut self, key: Rc<Term>, value: Rational) {
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

    fn add(mut self, other: Self) -> Self {
        for (var, coeff) in other.0 {
            self.insert(var, coeff);
        }
        self.1 += other.1;
        self
    }

    fn mul(&mut self, scalar: &Rational) {
        if *scalar == 0 {
            self.0.clear();
            self.1 = Rational::new();
            return;
        }

        if *scalar == 1 {
            return;
        }

        for coeff in self.0.values_mut() {
            *coeff *= scalar;
        }
        self.1 *= scalar;
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

    /// Finds the greatest common divisor of the coefficients in the linear combination. Returns
    /// 1 if the linear combination is empty, or if any of the coefficients is not an integer.
    fn coefficients_gcd(&self) -> Integer {
        if !self.1.is_integer() {
            return Integer::from(1);
        }

        let mut result = self.1.numer().clone();
        for (_, coeff) in &self.0 {
            if result == 1 {
                return Integer::from(1);
            }
            if coeff.is_integer() {
                result.gcd_mut(coeff.numer());
            } else {
                return Integer::from(1);
            }
        }

        // If the linear combination is all zeros, the result would also be zero. In that case, we
        // have to return one instead
        std::cmp::max(Integer::from(1), result)
    }
}

fn strengthen(op: Operator, disequality: &mut LinearComb, a: &Rational) -> Operator {
    // Multiplications are expensive, so we avoid them if we can
    let is_integer = if *a == 0 {
        true
    } else if *a == 1 {
        disequality.1.is_integer()
    } else {
        (disequality.1.clone() * a).is_integer()
    };

    match op {
        Operator::GreaterEq if is_integer => op,

        // In some cases, when the disequality is over integers, we can make the strengthening
        // rules even stronger. Consider for instance the following example:
        // ```
        //     (step t1 (cl
        //         (not (<= (- 1) n))
        //         (not (<= (- 1) (+ n m)))
        //         (<= (- 2) (* 2 n))
        //         (not (<= m 1))
        //     ) :rule la_generic :args (1 1 1 1))
        // ```
        // After the third disequality is negated and flipped, it becomes:
        //     -2 * n > 2
        // If nothing fancy is done, this would strengthen to:
        //     -2 * n >= 3
        // However, in this case, we can divide the disequality by 2 before strengthening, and then
        // multiply it by 2 to get back. This would result in:
        //     -2 * n > 2
        //     -1 * n > 1
        //     -1 * n >= 2
        //     -2 * n >= 4
        // This is a stronger statement, and follows from the original disequality. Importantly,
        // this strengthening is sometimes necessary to check some `la_generic` steps. To find the
        // value by which we should divide we have to take the greatest common divisor of the
        // coefficients (including the constant value on the right-hand side), as this makes sure
        // all coefficients will continue being integers after the division. This strengthening is
        // still valid because, since the variables are integers, the result of their linear
        // combination will always be a multiple of their GCD.
        Operator::GreaterThan if is_integer => {
            // Instead of dividing and then multiplying back, we just multiply the "+ 1"
            // that is added by the strengthening rule
            disequality.1.floor_mut();
            disequality.1 += disequality.coefficients_gcd();
            Operator::GreaterEq
        }
        Operator::GreaterThan | Operator::GreaterEq => {
            disequality.1.floor_mut();
            disequality.1 += 1;
            Operator::GreaterEq
        }
        Operator::LessThan | Operator::LessEq => unreachable!(),
        _ => op,
    }
}

fn process_disequality(
    pool: &Pool,
    (acc_op, acc): (Operator, LinearComb),
    (phi, arg): (&Rc<Term>, Option<Rational>),
    coeff_trace: &mut Option<Vec<Rational>>,
) -> Result<(Operator, LinearComb), CheckerError> {
    // Steps 1 and 2: Negate the disequality
    let (mut op, s1, s2) = negate_disequality(phi)?;

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

    // Extra step: infer argument if it is missing
    let arg = match arg {
        Some(a) => a,
        None => {
            rassert!(disequality.0.len() == 1, "disequality not unit");
            let (var, coeff_1) = disequality.0.iter().next().unwrap();
            assert!(!coeff_1.is_zero()); // TODO
            let Some(coeff_2) = acc.0.get(var) else {
                return err!("coeff not found");
            };
            let inferred = -coeff_2.clone() / coeff_1;
            if let Some(trace) = coeff_trace {
                trace.push(inferred.clone());
            }
            inferred
        }
    };

    // Step 4: Apply strengthening rules. These are only applied if all variables are integer sorted
    let all_vars_are_int = disequality.0.keys().all(|var| *pool.sort(var) == Sort::Int);
    if all_vars_are_int {
        op = strengthen(op, &mut disequality, &arg);
    }

    // Step 5: Multiply disequality by a. If a is zero, we must also weaken `>` into `>=`
    let arg = match op {
        Operator::Equals => arg,
        _ => arg.abs(),
    };
    if op == Operator::GreaterThan && arg.is_zero() {
        op = Operator::GreaterEq;
    }
    disequality.mul(&arg);

    let new_acc = acc.add(disequality);
    let new_op = match (acc_op, op) {
        (Operator::GreaterThan, _) | (_, Operator::GreaterThan) => Operator::GreaterThan,
        (Operator::GreaterEq, _) | (_, Operator::GreaterEq) => Operator::GreaterEq,
        _ => Operator::Equals,
    };
    Ok((new_op, new_acc))
}

pub fn la_generic(rule_args: RuleArgs) -> RuleResult {
    assert_num_args(rule_args.args, rule_args.conclusion.len())?;
    la_generic_partial(
        rule_args.pool,
        rule_args.conclusion,
        rule_args.args,
        &mut None,
    )
}

pub fn bounded_farkas(rule_args: RuleArgs) -> RuleResult {
    la_generic_partial(
        rule_args.pool,
        rule_args.conclusion,
        rule_args.args,
        &mut None,
    )
}

pub fn la_generic_partial(
    pool: &Pool,
    conclusion: &[Rc<Term>],
    args: &[Rc<Term>],
    coeff_trace: &mut Option<Vec<Rational>>,
) -> RuleResult {
    let args: Vec<_> = args
        .iter()
        .map(|a| {
            a.as_fraction()
                .ok_or_else(|| CheckerError::ExpectedAnyNumber(a.clone()))
        })
        .collect::<Result<_, _>>()?;
    let args = args.into_iter().map(Some).chain(std::iter::repeat(None));

    let (op, final_disequality) = conclusion
        .iter()
        .zip(args)
        .try_fold((Operator::Equals, LinearComb::new()), |acc, diseq| {
            process_disequality(pool, acc, diseq, coeff_trace)
        })?;

    let LinearComb(left_side, right_side): &LinearComb = &final_disequality;
    let is_disequality_true = {
        use Operator::*;
        use std::cmp::Ordering;

        // If the operator encompasses the actual relationship between 0 and the right side, the
        // disequality is true
        match Rational::new().cmp(right_side) {
            Ordering::Less => matches!(op, LessThan | LessEq),
            Ordering::Equal => matches!(op, LessEq | GreaterEq | Equals),
            Ordering::Greater => matches!(op, GreaterThan | GreaterEq),
        }
    };

    // The left side must be empty (that is, equal to 0), and the final disequality must be
    // contradictory
    if left_side.is_empty() && !is_disequality_true {
        Ok(())
    } else {
        err!(
            "final disequality is not contradictory: '{}'",
            DisplayLinearComb(&op, &final_disequality),
        )
    }
}

pub fn la_disequality(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    match_term_err!((or (= t1 t2) (not (<= t1 t2)) (not (<= t2 t1))) = &conclusion[0])?;
    Ok(())
}

pub fn la_totality(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    match_term_err!((or (<= t1 t2) (<= t2 t1)) = &conclusion[0])?;
    Ok(())
}

fn assert_less_than(a: &Rc<Term>, b: &Rc<Term>) -> RuleResult {
    rassert!(
        a.as_signed_number_err()? < b.as_signed_number_err()?,
        "expected term '{a}' to be less than term '{b}'",
    );
    Ok(())
}

fn assert_less_eq(a: &Rc<Term>, b: &Rc<Term>) -> RuleResult {
    rassert!(
        a.as_signed_number_err()? <= b.as_signed_number_err()?,
        "expected term '{a}' to be less than or equal to term '{b}'",
    );
    Ok(())
}

pub fn la_tautology(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;

    if let Some((first, second)) = match_term!((or phi_1 phi_2) = conclusion[0]) {
        // If the conclusion if of the second form, there are 5 possible cases:
        if let (Some((s_1, d_1)), Some((s_2, d_2))) = (
            match_term!((not (<= s d1)) = first),
            match_term!((<= s d2) = second),
        ) {
            // First case
            assert_eq(s_1, s_2)?;
            assert_less_eq(d_1, d_2)
        } else if let (Some((s_1, d_1)), Some((s_2, d_2))) = (
            match_term!((<= s d1) = first),
            match_term!((not (<= s d2)) = second),
        ) {
            // Second case
            assert_eq(s_1, s_2)?;
            assert_eq(d_1, d_2)
        } else if let (Some((s_1, d_1)), Some((s_2, d_2))) = (
            match_term!((not (>= s d1)) = first),
            match_term!((>= s d2) = second),
        ) {
            // Third case
            assert_eq(s_1, s_2)?;
            assert_less_eq(d_2, d_1)
        } else if let (Some((s_1, d_1)), Some((s_2, d_2))) = (
            match_term!((>= s d1) = first),
            match_term!((not (>= s d2)) = second),
        ) {
            // Fourth case
            assert_eq(s_1, s_2)?;
            assert_eq(d_1, d_2)
        } else if let (Some((s_1, d_1)), Some((s_2, d_2))) = (
            match_term!((not (<= s d1)) = first),
            match_term!((not (>= s d2)) = second),
        ) {
            // Fifth case
            assert_eq(s_1, s_2)?;
            assert_less_than(d_1, d_2)
        } else {
            err!("term '{}' doesn't match any tautology case", conclusion[0])
        }
    } else {
        // If the conclusion is of the first form, we apply steps 1 through 3 from `la_generic`

        // Steps 1 and 2: Negate the disequality
        let (mut op, s1, s2) = negate_disequality(&conclusion[0])?;

        // Step 3: Move all non constant terms to the left side, and the d terms to the right.
        let mut disequality = s1.sub(s2);
        disequality.1 = -disequality.1;

        // If the operator is < or <=, we flip the disequality so it is > or >=
        if op == Operator::LessThan {
            disequality.neg();
            op = Operator::GreaterThan;
        } else if op == Operator::LessEq {
            disequality.neg();
            op = Operator::GreaterEq;
        }

        // The final disequality should be tautological
        let is_disequality_true = disequality.0.is_empty()
            && (disequality.1 > 0 || op == Operator::GreaterThan && disequality.1 == 0);
        rassert!(
            is_disequality_true,
            "final disequality is not tautological: '{}'",
            DisplayLinearComb(&op, &disequality),
        );
        Ok(())
    }
}

/// A wrapper struct that implements `fmt::Display` for linear combinations.
struct DisplayLinearComb<'a>(&'a Operator, &'a LinearComb);

impl fmt::Display for DisplayLinearComb<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fn write_var(f: &mut fmt::Formatter, (var, coeff): (&Rc<Term>, &Rational)) -> fmt::Result {
            if *coeff == 1i32 {
                write!(f, "{}", var)
            } else {
                write!(f, "(* {:?} {})", coeff.to_f64(), var)
            }
        }

        let DisplayLinearComb(op, LinearComb(vars, constant)) = self;
        write!(f, "({} ", op)?;
        match vars.len() {
            0 => write!(f, "0.0"),
            1 => write_var(f, vars.iter().next().unwrap()),
            _ => {
                write!(f, "(+")?;
                for var in vars {
                    write!(f, " ")?;
                    write_var(f, var)?;
                }
                write!(f, ")")
            }
        }?;
        write!(f, " {:?})", constant.to_f64())
    }
}
