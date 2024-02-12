use super::{assert_eq, CheckerError, RuleArgs, RuleResult};
use crate::{
    ast::{pool::TermPool, Operator, ParamOperator, Rc, Sort, Term},
    checker::rules::assert_clause_len,
};
use rug::Integer;

fn build_term_vec(term: &Rc<Term>, size: usize, pool: &mut dyn TermPool) -> Vec<Rc<Term>> {
    let term = if let Some((Operator::BvBbTerm, args_x)) = term.as_op() {
        args_x.to_vec()
    } else {
        (0..size)
            .map(|i| {
                let op_args = vec![pool.add(Term::new_int(i))];
                pool.add(Term::ParamOp {
                    op: ParamOperator::BvBitOf,
                    op_args,
                    args: vec![term.clone()],
                })
            })
            .collect()
    };
    term
}

pub fn value(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (v, res_args) = match_term_err!((= v (bbterm ...)) = &conclusion[0])?;

    match v.as_bitvector() {
        Some((m, w)) => {
            let size = w.to_usize().unwrap();
            let true_term = pool.bool_true();
            let false_term = pool.bool_false();
            // the number of arguments of bbterm must be the same as the width of v
            if size != res_args.len() {
                return Err(CheckerError::Unspecified);
            }
            // the computed value from res_args must be the same as m
            let mut computed_value = 0;
            for i in 0..size - 1 {
                if res_args[i] == true_term {
                    computed_value += 2 * i;
                } else if res_args[i] != false_term {
                    return Err(CheckerError::Unspecified);
                }
            }
            if m != Integer::from(computed_value) {
                return Err(CheckerError::Unspecified);
            }
        }
        _ => {
            return Err(CheckerError::Unspecified);
        }
    }
    Ok(())
}

pub fn and(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvand x y) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let size = size.to_usize().unwrap();

    let x = build_term_vec(x, size, pool);
    let y = build_term_vec(y, size, pool);

    let res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
                pool,
                (and {x[i].clone()} {y[i].clone()})
            )
        })
        .collect();

    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));

    assert_eq(&expected_res, res)
}

pub fn or(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvor x y) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let size = size.to_usize().unwrap();

    let x = build_term_vec(x, size, pool);
    let y = build_term_vec(y, size, pool);

    let res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
              pool,
              (or {x[i].clone()} {y[i].clone()})
            )
        })
        .collect();

    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));

    assert_eq(&expected_res, res)
}

pub fn xor(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvxor x y) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let size = size.to_usize().unwrap();

    let x = build_term_vec(x, size, pool);
    let y = build_term_vec(y, size, pool);

    let res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
              pool,
              (xor {x[i].clone()} {y[i].clone()})
            )
        })
        .collect();

    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));

    assert_eq(&expected_res, res)
}

pub fn xnor(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvxnor x y) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let size = size.to_usize().unwrap();

    let x = build_term_vec(x, size, pool);
    let y = build_term_vec(y, size, pool);

    let res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
              pool,
              (= {x[i].clone()} {y[i].clone()})
            )
        })
        .collect();

    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));

    assert_eq(&expected_res, res)
}

pub fn not(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (x, res) = match_term_err!((= (bvnot x) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let size = size.to_usize().unwrap();

    let x = build_term_vec(x, size, pool);

    let res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
              pool,
              (not {x[i].clone()})
            )
        })
        .collect();

    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));

    assert_eq(&expected_res, res)
}

pub fn ult(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvult x y) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let x = build_term_vec(x, size, pool);
    let y = build_term_vec(y, size, pool);

    let mut expected_res = build_term!(pool, (and (not {x[0].clone()}) {y[0].clone()}));

    for i in 1..size {
        let new_res = build_term!(
            pool,
            (or (and (= {x[i].clone()} {y[i].clone()}) {expected_res.clone()})
                (and (not {x[i].clone()}) {y[i].clone()}))
        );
        expected_res = new_res;
    }

    assert_eq(&expected_res, res)
}

pub fn slt(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvslt x y) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let size = size.to_usize().unwrap();

    let x = build_term_vec(x, size, pool);
    let y = build_term_vec(y, size, pool);

    let mut expected_res = build_term!(pool, (and {x[0].clone()} (not {y[0].clone()})));

    for i in 1..(size - 1) {
        let new_res = build_term!(
            pool,
            (or (and (= {x[i].clone()} {y[i].clone()}) {expected_res.clone()})
                (and (not {x[i].clone()}) {y[i].clone()}))
        );
        expected_res = new_res;
    }

    let new_res = build_term!(
        pool,
        (or
         (and {x[size - 1].clone()} (not {y[size - 1].clone()}))
         (and (and {x[size - 1].clone()} {y[size - 1].clone()}) {expected_res.clone()}))
    );
    expected_res = new_res;

    assert_eq(&expected_res, res)
}

pub fn add(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvadd x y) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let x = build_term_vec(x, size, pool);
    let y = build_term_vec(y, size, pool);

    let mut carries = vec![pool.bool_false()];

    for i in 1..size {
        let carry_i = build_term!(
          pool,
          (or (and {x[i - 1].clone()} {y[i - 1].clone()}) (and (xor {x[i - 1].clone()} {y[i - 1].clone()}) {carries[i - 1].clone()}))
        );
        carries.push(carry_i);
    }

    let res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
              pool,
              (xor (xor {x[i].clone()} {y[i].clone()}) {carries[i].clone()})
            )
        })
        .collect();

    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));

    assert_eq(&expected_res, res)
}

pub fn neg(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (x, res) = match_term_err!((= (bvneg x) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let size = size.to_usize().unwrap();

    let x = build_term_vec(x, size, pool);

    let mut carries = vec![pool.bool_true()];

    for i in 1..size {
        let carry_i = build_term!(
          pool,
          (or (and (not {x[i - 1].clone()}) false) (and (xor (not {x[i - 1].clone()}) false) {carries[i - 1].clone()}))
        );
        carries.push(carry_i);
    }

    let res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
              pool,
              (xor (xor (not {x[i].clone()}) false) {carries[i].clone()})
            )
        })
        .collect();

    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));

    assert_eq(&expected_res, res)
}

//TODO I think this can be redone with build_term_vec.
pub fn extract(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (((_, left_j), left_x), right) =
        match_term_err!((= ((_ extract i j) x) (bbterm ...)) = &conclusion[0])?;

    let left_j = left_j.as_integer().unwrap();
    let mut index = left_j;

    if let Some((Operator::BvBbTerm, args)) = left_x.as_op() {
        let mut index = index.to_usize().unwrap();
        for arg in right {
            assert_eq(&args[index], arg)?;
            index += 1;
        }
        return Ok(());
    }

    for arg in right {
        let expected_arg = Term::ParamOp {
            op: ParamOperator::BvBitOf,
            op_args: vec![pool.add(Term::new_int(index.clone()))],
            args: vec![left_x.clone()],
        };
        let new_arg = pool.add(expected_arg);
        assert_eq(&new_arg, arg)?;
        index += 1;
    }
    Ok(())
}

pub fn concat(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res_vec) = match_term_err!((= (concat x y) (bbterm ...)) = &conclusion[0])?;

    let Sort::BitVec(size1) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };
    let size1 = size1.to_usize().unwrap();

    let Sort::BitVec(size2) = pool.sort(y).as_sort().cloned().unwrap() else {
        unreachable!();
    };
    let size2 = size2.to_usize().unwrap();

    let x = build_term_vec(x, size1, pool);
    let y = build_term_vec(y, size2, pool);

    let mut index = 0;
    for arg in res_vec {
        if index < size1 {
            assert_eq(&x[index], arg)?;
        } else {
            assert_eq(&y[index - size1], arg)?;
        }

        index += 1;
    }
    Ok(())
}

pub fn equality(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (= x y) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let x = build_term_vec(x, size, pool);
    let y = build_term_vec(y, size, pool);

    let expected_res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
                pool,
                (= {x[i].clone()} {y[i].clone()})
            )
        })
        .collect();
    let expected_res = pool.add(Term::Op(Operator::And, expected_res_args));

    assert_eq(&expected_res, res)
}
