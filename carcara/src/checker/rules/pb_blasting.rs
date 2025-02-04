use super::{assert_eq, RuleArgs, RuleResult};
use crate::{
    ast::{pool::TermPool, Operator, ParamOperator, Rc, Sort, Term},
    checker::error::CheckerError,
    // checker::rules::assert_clause_len,
};
use rug::Integer;

fn build_term_pb_vec(term: &Rc<Term>, size: usize, pool: &mut dyn TermPool) -> Vec<Rc<Term>> {
    let term = if let Some((Operator::BvPBbTerm, args_x)) = term.as_op() {
        args_x.to_vec()
    } else {
        (0..size)
            .map(|i| {
                let op_args = vec![pool.add(Term::new_int(i))];
                pool.add(Term::ParamOp {
                    op: ParamOperator::BvIntOf,
                    op_args,
                    args: vec![term.clone()],
                })
            })
            .collect()
    };
    term
}

pub fn pbblast_bveq(RuleArgs { pool, conclusion, .. }: RuleArgs) -> RuleResult {
    // Check that conclusion is an equivalence between bitvector equality
    // and difference of summations equal to zero
    let ((x, y), ((sum_x, sum_y), _)) =
        match_term_err!((= (= x y) (= (- (+ ...) (+ ...)) 0)) = &conclusion[0])?;

    // Drops the last element, that is zero
    let sum_x = &sum_x[..sum_x.len() - 1];
    let sum_y = &sum_y[..sum_y.len() - 1];

    // Check that `x`'s bitvector width exists in the `pool`
    let Sort::BitVec(x_width) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    // Transforms the width of x to a usize type
    let x_width = x_width.to_usize().unwrap();

    // Check that `sum_x` has the same length as `x`
    rassert!(x_width == sum_x.len(), CheckerError::Unspecified);

    // Check that `y`'s bitvector width exists in the `pool`
    let Sort::BitVec(y_width) = pool.sort(y).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    // Transforms the width of y to a usize type
    let y_width = y_width.to_usize().unwrap();

    // Check that `sum_y` has the same length as `y`
    rassert!(y_width == sum_y.len(), CheckerError::Unspecified);

    // Check that both bitvectors x and y have the same length
    rassert!(x_width == y_width, CheckerError::Unspecified);

    // Define a closure to check the terms for a bitvector and its summation
    let check_bitvector_sum =
        |sum: &[Rc<Term>], width: usize, bitvector: &Rc<Term>| -> RuleResult {
            for (i, element) in sum.iter().enumerate() {
                // Match `element` with a coefficient times an `int_of` application on bitvector `bv`
                // Attempt to match the term with a coefficient
                let (c, idx, bv) = match match_term!((* c ((_ int_of idx) bv)) = element) {
                    Some((c, (idx, bv))) => (c.as_integer_err()?, idx, bv),
                    None => {
                        // If there's no coefficient and i == 0, check the pattern without the coefficient
                        if i == 0 {
                            match match_term!(((_ int_of idx) bitvector) = element) {
                                Some((idx, bv)) => (Integer::from(1), idx, bv), // Default coefficient to 1
                                None => panic!("Element does not match either pattern"),
                            }
                        } else {
                            panic!("Coefficient was not found and i != 0");
                        }
                    }
                };

                // Convert `idx` to integer
                let idx: Integer = idx.as_integer_err()?;

                // Check that the coefficient is actually 2^i
                rassert!(c == (1 << i), CheckerError::Unspecified);
                // Check that the index is actually `width - i - 1`
                rassert!(idx == width - i - 1, CheckerError::Unspecified);
                // Check that the bitvector being indexed is actually `bitvector`
                rassert!(*bv == *bitvector, CheckerError::Unspecified);
            }
            Ok(())
        };

    // Use the closure to check the `sum_x` terms
    check_bitvector_sum(sum_x, x_width, x)?;

    // Use the closure to check the `sum_y` terms
    check_bitvector_sum(sum_y, y_width, y)?;

    Ok(())
}

pub fn pbblast_bvult(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

pub fn pbblast_bvugt(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

pub fn pbblast_bvuge(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

pub fn pbblast_bvule(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

pub fn pbblast_bvslt(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

pub fn pbblast_bvsgt(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

pub fn pbblast_bvsge(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

pub fn pbblast_bvsle(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

pub fn pbblast_pbbvar(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

pub fn pbblast_pbbconst(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

pub fn pbblast_bvxor(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

pub fn pbblast_bvand(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

mod tests {
    #[test]
    fn pbblast_bveq() {
        test_cases! {
            definitions = "
                (declare-const x1 (_ BitVec 1))
                (declare-const y1 (_ BitVec 1))
                (declare-const x2 (_ BitVec 2))
                (declare-const y2 (_ BitVec 2))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x1 y1) (= (- (+ (* 1 ((_ int_of 0) x1)) 0) (+ (* 1 ((_ int_of 0) y1)) 0)) 0))) :rule pbblast_bveq)"#: true,
            }
            "Omit multiplication by 1" {
                r#"(step t1 (cl (= (= x1 y1) (= (- (+ ((_ int_of 0) x1) 0) (+ ((_ int_of 0) y1) 0)) 0))) :rule pbblast_bveq)"#: true,
            }
            "Not a subtraction of sums" {
                r#"(step t1 (cl (= (= x1 y1) (= (+ (* 1 ((_ int_of 0) x1)) 0) 0))) :rule pbblast_bveq)"#: false,
            }
            "Malformed products" {
                r#"(step t1 (cl (= (= x1 y1) (= (- (+ (* 0 ((_ int_of 0) x1)) 0) (+ (* 1 ((_ int_of 0) y1)) 0)) 0))) :rule pbblast_bveq)"#: false,
                r#"(step t1 (cl (= (= x1 y1) (= (- (+ (* 1 ((_ int_of 0) x1)) 0) (+ (* 0 ((_ int_of 0) y1)) 0)) 0))) :rule pbblast_bveq)"#: false,
            }
            "Equality on two bits" {
                r#"(step t1 (cl (= (= x2 y2) (= (- (+ (* 1 ((_ int_of 1) x2)) (* 2 ((_ int_of 0) x2)) 0) (+ (* 1 ((_ int_of 1) y2)) (* 2 ((_ int_of 0) y2)) 0)) 0))) :rule pbblast_bveq)"#: true,
            }
        }
    }
    #[test]
    fn pbblast_bvult() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x y) (= (- (+ ((_ int_of 0) x) 0) (+ ((_ int_of 0) y) 0)) 0))) :rule pbblast_bvult :args (x y))"#: true,
            }
        }
    }
    #[test]
    fn pbblast_bvugt() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x y) (= (- (+ ((_ int_of 0) x) 0) (+ ((_ int_of 0) y) 0)) 0))) :rule pbblast_bvugt :args (x y))"#: true,
            }
        }
    }
    #[test]
    fn pbblast_bvuge() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x y) (= (- (+ ((_ int_of 0) x) 0) (+ ((_ int_of 0) y) 0)) 0))) :rule pbblast_bvuge :args (x y))"#: true,
            }
        }
    }
    #[test]
    fn pbblast_bvule() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x y) (= (- (+ ((_ int_of 0) x) 0) (+ ((_ int_of 0) y) 0)) 0))) :rule pbblast_bvule :args (x y))"#: true,
            }
        }
    }
    #[test]
    fn pbblast_bvslt() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x y) (= (- (+ ((_ int_of 0) x) 0) (+ ((_ int_of 0) y) 0)) 0))) :rule pbblast_bvslt :args (x y))"#: true,
            }
        }
    }
    #[test]
    fn pbblast_bvsgt() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x y) (= (- (+ ((_ int_of 0) x) 0) (+ ((_ int_of 0) y) 0)) 0))) :rule pbblast_bvsgt :args (x y))"#: true,
            }
        }
    }
    #[test]
    fn pbblast_bvsge() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x y) (= (- (+ ((_ int_of 0) x) 0) (+ ((_ int_of 0) y) 0)) 0))) :rule pbblast_bvsge :args (x y))"#: true,
            }
        }
    }
    #[test]
    fn pbblast_bvsle() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x y) (= (- (+ ((_ int_of 0) x) 0) (+ ((_ int_of 0) y) 0)) 0))) :rule pbblast_bvsle :args (x y))"#: true,
            }
        }
    }
    #[test]
    fn pbblast_pbbvar() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x y) (= (- (+ ((_ int_of 0) x) 0) (+ ((_ int_of 0) y) 0)) 0))) :rule pbblast_pbbvar :args (x y))"#: true,
            }
        }
    }
    #[test]
    fn pbblast_pbbconst() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x y) (= (- (+ ((_ int_of 0) x) 0) (+ ((_ int_of 0) y) 0)) 0))) :rule pbblast_pbbconst :args (x y))"#: true,
            }
        }
    }
    #[test]
    fn pbblast_bvxor() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x y) (= (- (+ ((_ int_of 0) x) 0) (+ ((_ int_of 0) y) 0)) 0))) :rule pbblast_bvxor :args (x y))"#: true,
            }
        }
    }
    #[test]
    fn pbblast_bvand() {
        test_cases! {
           definitions = "
                (declare-const x (_ BitVec 1))
                (declare-const y (_ BitVec 1))
                ",
            "Equality on single bits" {
                r#"(step t1 (cl (= (= x y) (= (- (+ ((_ int_of 0) x) 0) (+ ((_ int_of 0) y) 0)) 0))) :rule pbblast_bvand :args (x y))"#: true,
            }
        }
    }
}
