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

pub fn pbblast_bveq(RuleArgs { pool, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} ", args.len(), conclusion.len());

    let ((x, y), ((sum_x, sum_y), _)) =
        match_term_err!((= (= x y) (= (- (+ ...) (+ ...)) 0)) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let size = size.to_usize().unwrap();

    // let x_pb: Vec<Rc<Term>> = build_term_pb_vec(x, size, pool);
    // let y_pb = build_term_pb_vec(y, size, pool);

    println!("size:{size}");
    println!("x: {x:?}");
    println!("y: {y:?}");
    println!("sum_x: {sum_x:?}");
    println!("sum_y: {sum_y:?}");

    // Build Term with x that is equivalent to sum_x
    // sum_x.iter().enumerate().take(size).for_each(|(i, sum)| {
    for i in 0..size {
        let (c, (idx, bv)) = match_term_err!((* c ((_ int_of idx) x)) = &sum_x[i])?;
        // TODO: if i = 0, c can be omitted, so let (idx, bv) = match_term_err!(((_ int_of idx) x) = &sum_x[i])?; is also acceptable

        let c: Integer = c.as_integer_err()?;
        let idx: Integer = idx.as_integer_err()?;

        // TODO: Create appropriate error type
        rassert!(c == (1 << i), CheckerError::Unspecified);
        rassert!(idx == size - i - 1, CheckerError::Unspecified);
        rassert!(bv == x, CheckerError::Unspecified);
    }
    // });

    // Build Term with y that is equivalent to sum_y
    for i in 0..size {
        let (c, (idx, bv)) = match_term_err!((* c ((_ int_of idx) y)) = &sum_y[i])?;

        let c: Integer = c.as_integer_err()?;
        let idx: Integer = idx.as_integer_err()?;

        // TODO: Create appropriate error type
        rassert!(c == (1 << i), CheckerError::Unspecified);
        rassert!(idx == size - i - 1, CheckerError::Unspecified);
        rassert!(bv == y, CheckerError::Unspecified);
    }

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
