use super::{assert_eq, CheckerError, RuleArgs, RuleResult};
use crate::{
    ast::{pool::TermPool, Operator, ParamOperator, Rc, Sort, Term},
    checker::rules::assert_clause_len,
};
use rug::Integer;

fn bitvector_size(pool: &mut dyn TermPool, term: &Rc<Term>) -> usize {
    let Sort::BitVec(size) = pool.sort(term).as_sort().cloned().unwrap() else {
        panic!("trying to get size of non-bitvector term: {}", term);
    };
    size
}

fn get_term_bits(term: &Rc<Term>, pool: &mut dyn TermPool) -> Vec<Rc<Term>> {
    let term = if let Some((Operator::BvBbTerm, args_x)) = term.as_op() {
        args_x.to_vec()
    } else {
        (0..bitvector_size(pool, term))
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

fn ripple_carry_adder(x: &Rc<Term>, y: &Rc<Term>, pool: &mut dyn TermPool) -> Rc<Term> {
    let size = bitvector_size(pool, x);
    let x = get_term_bits(x, pool);
    let y = get_term_bits(y, pool);

    let mut carries = vec![pool.bool_false()];

    for i in 1..size {
        let carry_i = build_term!(
          pool,
            (or
              (and
                {x[i - 1].clone()}
                {y[i - 1].clone()})
              (and
                (xor
                  {x[i - 1].clone()}
                  {y[i - 1].clone()})
                {carries[i - 1].clone()}))
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

    pool.add(Term::Op(Operator::BvBbTerm, res_args))
}

fn shift_add_multiplier(x: &Rc<Term>, y: &Rc<Term>, pool: &mut dyn TermPool) -> Rc<Term> {
    let size = bitvector_size(pool, x);
    let x = get_term_bits(x, pool);
    let y = get_term_bits(y, pool);

    let false_term = pool.bool_false();
    let shift: Vec<Vec<_>> = (0..size)
        .map(|j| {
            (0..size)
                .map(|i| {
                    // if j <= i { build_term!(pool, (and {x[i-j].clone()} {y[j].clone()})) }
                    if j <= i {
                        build_term!(pool, (and {y[j].clone()} {x[i-j].clone()}))
                    } else {
                        false_term.clone()
                    }
                })
                .collect()
        })
        .collect();

    let mut carry: Vec<Vec<_>> = vec![(0..size).map(|_i| false_term.clone()).collect()];
    let mut res: Vec<Vec<_>> = vec![(0..size).map(|i| shift[0][i].clone()).collect()];

    for j in 1..size {
        // carry^j+1_i+1
        carry.push(vec![false_term.clone()]);
        for i in 1..size {
            let prev_carry = if j < i {
                carry[j][i - 1].clone()
            } else {
                false_term.clone()
            };
            carry[j].push(
                if j < i {
                    build_term!(pool,
                                (or (and {res[j-1][i-1].clone()} {shift[j][i-1].clone()})
                                 (and (xor {res[j-1][i-1].clone()} {shift[j][i-1].clone()}) {prev_carry})
                                )
                    )
                }
                else {false_term.clone()});
        }

        // res^j+1_i
        res.push((0..size)
                      .map(|i| {
                          // res^j_0 = sh^0_0
                          if i == 0 { shift[0][0].clone() }
                          else if j > i { res[i][i].clone() }
                          else {
                              build_term!(pool,
                                    (xor (xor {res[j-1][i].clone()} {shift[j][i].clone()}) {carry[j][i].clone()})
                              )
                          }
                      }).collect());
    }

    pool.add(Term::Op(Operator::BvBbTerm, res[size - 1].clone()))
}

pub fn value(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (v, res_args) = match_term_err!((= v (bbterm ...)) = &conclusion[0])?;

    if let Some((m, size)) = v.as_bitvector() {
        let true_term = pool.bool_true();
        let false_term = pool.bool_false();
        // the number of arguments of bbterm must be the same as the width of v
        if size == res_args.len() {
            // the computed value from res_args must be the same as m
            let mut computed_value = Integer::new();
            for (i, arg) in res_args.iter().enumerate() {
                if *arg == true_term {
                    computed_value =
                        &computed_value + Integer::from(Integer::i_pow_u(2, i.try_into().unwrap()));
                } else if *arg != false_term {
                    return Err(CheckerError::Explanation(format!(
                        "bitblasted const {}-th arg neither true nor false",
                        i
                    )));
                }
            }
            if m == computed_value {
                return Ok(());
            }
            return Err(CheckerError::Explanation(format!(
                "const is {} but bitblasting computes to {}",
                m, computed_value
            )));
        }
    }
    Err(CheckerError::Explanation(
        "Not a const being bitblasted.".to_owned(),
    ))
}

pub fn var(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (x, res) = match_term_err!((= x res) = &conclusion[0])?;

    rassert!(
        matches!(pool.sort(x).as_sort().unwrap(), &Sort::BitVec(_)),
        CheckerError::Explanation(format!(
            "Could not get BV sort out of (expected-to-be variable) term {}",
            x
        ))
    );
    let x = get_term_bits(x, pool);

    assert_eq(&pool.add(Term::Op(Operator::BvBbTerm, x)), res)
}

pub fn and(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (bvand_args, res) = match_term_err!((= (bvand ...) res) = &conclusion[0])?;

    let size = bitvector_size(pool, &bvand_args[0]);

    // the conjunction is build left-to-right
    let mut i = 1;
    let mut expected_res = bvand_args[0].clone();

    while i < bvand_args.len() {
        let x = get_term_bits(&expected_res, pool);
        let y = get_term_bits(&bvand_args[i], pool);

        let res_args: Vec<_> = (0..size)
            .map(|i| {
                build_term!(
                    pool,
                    (and {x[i].clone()} {y[i].clone()})
                )
            })
            .collect();
        expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));
        i += 1;
    }

    assert_eq(&expected_res, res)
}

pub fn or(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (bvor_args, res) = match_term_err!((= (bvor ...) res) = &conclusion[0])?;

    let size = bitvector_size(pool, &bvor_args[0]);

    // the disjunction is build left-to-right
    let mut i = 1;
    let mut expected_res = bvor_args[0].clone();

    while i < bvor_args.len() {
        let x = get_term_bits(&expected_res, pool);
        let y = get_term_bits(&bvor_args[i], pool);

        let res_args: Vec<_> = (0..size)
            .map(|i| {
                build_term!(
                    pool,
                    (or {x[i].clone()} {y[i].clone()})
                )
            })
            .collect();
        expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));
        i += 1;
    }

    assert_eq(&expected_res, res)
}

pub fn xor(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (bvxor_args, res) = match_term_err!((= (bvxor ...) res) = &conclusion[0])?;

    let size = bitvector_size(pool, &bvxor_args[0]);

    // the conjunction is build left-to-right
    let mut i = 1;
    let mut expected_res = bvxor_args[0].clone();

    while i < bvxor_args.len() {
        let x = get_term_bits(&expected_res, pool);
        let y = get_term_bits(&bvxor_args[i], pool);

        let res_args: Vec<_> = (0..size)
            .map(|i| {
                build_term!(
                    pool,
                    (xor {x[i].clone()} {y[i].clone()})
                )
            })
            .collect();
        expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));
        i += 1;
    }

    assert_eq(&expected_res, res)
}

pub fn xnor(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvxnor x y) res) = &conclusion[0])?;

    let size = bitvector_size(pool, x);
    let x = get_term_bits(x, pool);
    let y = get_term_bits(y, pool);

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

    let size = bitvector_size(pool, x);
    let x = get_term_bits(x, pool);

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

/// Bitblasts `(bvult x y)`
fn bitblast_ult(pool: &mut dyn TermPool, x: &Rc<Term>, y: &Rc<Term>) -> Rc<Term> {
    let size = bitvector_size(pool, x);
    let x = get_term_bits(x, pool);
    let y = get_term_bits(y, pool);

    let mut res = build_term!(pool, (and (not {x[0].clone()}) {y[0].clone()}));

    for i in 1..size {
        res = build_term!(
            pool,
            (or (and (= {x[i].clone()} {y[i].clone()}) {res.clone()})
                (and (not {x[i].clone()}) {y[i].clone()}))
        );
    }
    res
}

pub fn ult(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvult x y) res) = &conclusion[0])?;

    let expected = bitblast_ult(pool, x, y);

    assert_eq(&expected, res)
}

pub fn slt(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvslt x y) res) = &conclusion[0])?;

    let size = bitvector_size(pool, x);
    let x = get_term_bits(x, pool);
    let y = get_term_bits(y, pool);

    // if size is 1, check directly if x, whose only bit is its LSB,
    // is negative (i.e., first bit is 1) and y positive (i.e., it is
    // zero)
    if size == 1 {
        return assert_eq(
            &build_term!(pool, (and {x[0].clone()} (not {y[0].clone()}))),
            res,
        );
    }

    let mut expected_res = build_term!(pool, (and (not {x[0].clone()}) {y[0].clone()}));

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
         (and (= {x[size - 1].clone()} {y[size - 1].clone()}) {expected_res.clone()})
         (and {x[size - 1].clone()} (not {y[size - 1].clone()}))
        )
    );
    expected_res = new_res;

    assert_eq(&expected_res, res)
}

pub fn add(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (add_args, res) = match_term_err!((= (bvadd ...) res) = &conclusion[0])?;

    let mut i = 1;
    let mut expected_res = add_args[0].clone();
    while i < add_args.len() {
        expected_res = ripple_carry_adder(&expected_res, &add_args[i], pool);
        i += 1;
    }
    assert_eq(&expected_res, res)
}

pub fn mult(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (mult_args, res) = match_term_err!((= (bvmul ...) res) = &conclusion[0])?;

    let mut i = 1;
    let mut expected_res = mult_args[0].clone();
    while i < mult_args.len() {
        expected_res = shift_add_multiplier(&expected_res, &mult_args[i], pool);
        i += 1;
    }
    assert_eq(&expected_res, res)
}

pub fn neg(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (x, res) = match_term_err!((= (bvneg x) res) = &conclusion[0])?;

    let size = bitvector_size(pool, x);
    let x = get_term_bits(x, pool);

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

pub fn equality(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (= x y) res) = &conclusion[0])?;

    let size = bitvector_size(pool, x);
    let x = get_term_bits(x, pool);
    let y = get_term_bits(y, pool);

    let expected_res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
                pool,
                (= {x[i].clone()} {y[i].clone()})
            )
        })
        .collect();
    let expected_res = if expected_res_args.len() > 1 {
        pool.add(Term::Op(Operator::And, expected_res_args))
    } else {
        expected_res_args[0].clone()
    };

    assert_eq(&expected_res, res)
}

pub fn comp(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvcomp x y) res) = &conclusion[0])?;

    let size = bitvector_size(pool, x);
    let x = get_term_bits(x, pool);
    let y = get_term_bits(y, pool);

    let expected_res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
                pool,
                (= {x[i].clone()} {y[i].clone()})
            )
        })
        .collect();
    let expected_res = if expected_res_args.len() > 1 {
        pool.add(Term::Op(Operator::And, expected_res_args))
    } else {
        expected_res_args[0].clone()
    };
    let expected_res = build_term!(pool, (bbterm { expected_res }));

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
    let (concat_args, res_args) = match_term_err!((= (concat ...) (bbterm ...)) = &conclusion[0])?;

    let mut size = bitvector_size(pool, &concat_args[concat_args.len() - 1]);
    let mut expected_res = get_term_bits(&concat_args[concat_args.len() - 1], pool);

    let mut i = 1;
    while i < concat_args.len() {
        let Sort::BitVec(size_i) = pool
            .sort(&concat_args[concat_args.len() - 1 - i])
            .as_sort()
            .cloned()
            .unwrap()
        else {
            unreachable!();
        };
        expected_res.extend(get_term_bits(&concat_args[concat_args.len() - 1 - i], pool));

        size += size_i;
        i += 1;
    }

    if res_args.len() != size {
        return Err(CheckerError::Explanation(format!(
            "Concat size {} different from sum of argument size {}",
            res_args.len(),
            size
        )));
    }
    assert_eq(
        &pool.add(Term::Op(Operator::BvBbTerm, expected_res)),
        &pool.add(Term::Op(Operator::BvBbTerm, res_args.to_vec())),
    )
}

pub fn sign_extend(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((i, x), res) = match_term_err!((= ((_ sign_extend i) x) res) = &conclusion[0])?;

    let i = i.as_integer().unwrap().to_usize().unwrap();
    if i == 0 {
        return assert_eq(x, res);
    }

    let size = bitvector_size(pool, x);
    let mut x = get_term_bits(x, pool);

    for _j in 0..i {
        x.push(x[size - 1].clone());
    }

    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, x));
    assert_eq(&expected_res, res)
}

/// Bitblasts `(bvshl x y)`
fn bitblast_shl(pool: &mut dyn TermPool, x: &Rc<Term>, y: &Rc<Term>) -> Rc<Term> {
    let size = bitvector_size(pool, x);

    // First, we will need to bitblast a term that corresponds to `(bvult y size)`
    let size_term = pool.add(Term::new_bv(size, size));
    let y_ult_size = bitblast_ult(pool, y, &size_term);

    let x = get_term_bits(x, pool);
    let y = get_term_bits(y, pool);

    let mut res = x;

    // We only need to check the bits upto k = ceil(log2(size)). Note that ilog2 rounds down, so we
    // add 1 if it's not an exact power of 2
    let k = size.ilog2() as usize + if size.is_power_of_two() { 0 } else { 1 };

    #[allow(clippy::needless_range_loop)] // clippy gets confused here
    for s in 0..k {
        let previous_res = res.clone();
        let thresh = 1 << s;
        for i in 0..size {
            let ite_args = if i < thresh {
                (pool.bool_false(), previous_res[i].clone())
            } else {
                (previous_res[i - thresh].clone(), previous_res[i].clone())
            };
            res[i] = build_term!(pool, (ite {y[s].clone()} {ite_args.0} {ite_args.1}));
        }
    }

    for bit in &mut res {
        *bit = build_term!(pool, (ite {y_ult_size.clone()} {bit.clone()} false));
    }

    pool.add(Term::Op(Operator::BvBbTerm, res))
}

pub fn shl(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvshl x y) res) = &conclusion[0])?;

    let expected = bitblast_shl(pool, x, y);

    assert_eq(&expected, res)
}

/// Bitblasts `(bvlshr x y)`
fn bitblast_lshr(pool: &mut dyn TermPool, x: &Rc<Term>, y: &Rc<Term>) -> Rc<Term> {
    let size = bitvector_size(pool, x);

    // First, we will need to bitblast a term that corresponds to `(bvult y size)`
    let size_term = pool.add(Term::new_bv(size, size));
    let y_ult_size = bitblast_ult(pool, y, &size_term);

    let x = get_term_bits(x, pool);
    let y = get_term_bits(y, pool);

    let mut res = x;

    // We only need to check the bits upto k = ceil(log2(size)). Note that ilog2 rounds down, so we
    // add 1 if it's not an exact power of 2
    let k = size.ilog2() as usize + if size.is_power_of_two() { 0 } else { 1 };

    #[allow(clippy::needless_range_loop)] // clippy gets confused here
    for s in 0..k {
        let previous_res = res.clone();
        let thresh = 1 << s;
        for i in 0..size {
            res[i] = if i + thresh >= size {
                build_term!(pool, (ite {y[s].clone()} false {previous_res[i].clone()}))
            } else {
                build_term!(pool, (ite
                    (not {y[s].clone()})
                    {previous_res[i].clone()}
                    {previous_res[i + thresh].clone()}
                ))
            };
        }
    }

    for bit in &mut res {
        *bit = build_term!(pool, (ite {y_ult_size.clone()} {bit.clone()} false));
    }

    pool.add(Term::Op(Operator::BvBbTerm, res))
}

pub fn lshr(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvlshr x y) res) = &conclusion[0])?;

    let expected = bitblast_lshr(pool, x, y);

    assert_eq(&expected, res)
}
