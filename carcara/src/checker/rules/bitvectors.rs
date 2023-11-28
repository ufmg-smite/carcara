use crate::{
    ast::{pool::TermPool, Constant, IndexedOperator, Operator, Rc, Sort, Term},
    checker::rules::assert_clause_len,
};

use super::{assert_eq, RuleArgs, RuleResult};

fn build_term_vec(term: &Rc<Term>, size: usize, pool: &mut dyn TermPool) -> Vec<Rc<Term>> {
    let term = if let Some((Operator::BvBbTerm, args_x)) = term.as_op() {
        args_x.to_vec()
    } else {
        (0..size)
            .map(|i| {
                pool.add(Term::IndexedOp {
                    op: IndexedOperator::BvBitOf,
                    op_args: vec![Constant::Integer(i.into())],
                    args: vec![term.clone()],
                })
            })
            .collect()
    };
    term
}

pub fn ult(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvult x y) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let size = size.to_usize().unwrap();

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

mod tests {
    #[test]
    fn ult() {
        test_cases! {
            definitions = "
    (declare-fun x4 () (_ BitVec 4))
    (declare-fun y4 () (_ BitVec 4))
    ",
            "Using bvult with x and y as bitvectors" {
              "(step t3 (cl (= (bvult x4 y4) (or (= ((_ bit_of 3) x4) ((_ bit_of 2) y4)) ((_ bit_of 3) x4) ((_ bit_of 2) y4)))) :rule bitblast_ult)": false,
              "(step t3 (cl (= (bvult x4 y4) (or (and (= ((_ bit_of 3) x4) ((_ bit_of 3) y4)) (or (and (= ((_ bit_of 2) x4) ((_ bit_of 2) y4)) (or (and (= ((_ bit_of 1) x4) ((_ bit_of 1) y4)) (and (not ((_ bit_of 0) x4)) ((_ bit_of 0) y4))) (and (not ((_ bit_of 1) x4)) ((_ bit_of 1) y4)))) (and (not ((_ bit_of 2) x4)) ((_ bit_of 2) y4)))) (and (not ((_ bit_of 3) x4)) ((_ bit_of 3) y4))))) :rule bitblast_ult)": true,
            }
            "Using bvult with x and y as bbterms" {
              "(step t1 (cl (= (bvult (bbterm ((_ bit_of 0) x4) ((_ bit_of 1) x4) ((_ bit_of 2) x4) ((_ bit_of 3) x4)) (bbterm ((_ bit_of 0) y4) ((_ bit_of 1) y4) ((_ bit_of 2) y4) ((_ bit_of 3) y4))) (or (and (= ((_ bit_of 3) x4) ((_ bit_of 3) y4)) (or (and (= ((_ bit_of 2) x4) ((_ bit_of 2) y4)) (or (and (= ((_ bit_of 1) x4) ((_ bit_of 1) y4)) (and (not ((_ bit_of 0) x4)) ((_ bit_of 0) y4))) (and (not ((_ bit_of 1) x4)) ((_ bit_of 1) y4)))) (and (not ((_ bit_of 2) x4)) ((_ bit_of 2) y4)))) (and (not ((_ bit_of 3) x4)) ((_ bit_of 3) y4))))) :rule bitblast_ult)": true,
              "(step t2 (cl (= (bvult (bbterm ((_ bit_of 0) x4) ((_ bit_of 1) x4) ((_ bit_of 2) x4) ((_ bit_of 3) x4)) (bbterm ((_ bit_of 4) y4) ((_ bit_of 1) y4) ((_ bit_of 2) y4) ((_ bit_of 3) y4))) (or (and (= ((_ bit_of 3) x4) ((_ bit_of 3) y4)) (or (and (= ((_ bit_of 2) x4) ((_ bit_of 2) y4)) (or (and (= ((_ bit_of 1) x4) ((_ bit_of 1) y4)) (and (not ((_ bit_of 0) x4)) ((_ bit_of 0) y4))) (and (not ((_ bit_of 1) x4)) ((_ bit_of 1) y4)))) (and (not ((_ bit_of 2) x4)) ((_ bit_of 2) y4)))) (and (not ((_ bit_of 3) x4)) ((_ bit_of 3) y4))))) :rule bitblast_ult)": false,
            }
        }
    }
}
