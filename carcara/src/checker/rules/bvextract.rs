use crate::{
    ast::{Constant, IndexedOperator, Operator, Term},
    checker::rules::assert_clause_len,
};

use super::{assert_eq, RuleArgs, RuleResult};

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
        let expected_arg = Term::IndexedOp {
            op: IndexedOperator::BvBitOf,
            op_args: vec![Constant::Integer(index.clone())],
            args: vec![left_x.clone()],
        };
        let new_arg = pool.add(expected_arg);
        assert_eq(&new_arg, arg)?;
        index += 1;
    }
    Ok(())
}

#[cfg(test)]

mod tests {
    #[test]
    fn extract() {
        test_cases! {
            definitions = "
            (declare-fun a () Bool)
            (declare-fun zz () (_ BitVec 12))
            ",
            "Simple working examples" {
              "(step t2 (cl (= ((_ extract 1 0) (bbterm ((_ bit_of 0) (ite a #b110 #b011)) ((_ bit_of 1) (ite a #b110 #b011)) ((_ bit_of 2) (ite a #b110 #b011)))) (bbterm ((_ bit_of 0) (ite a #b110 #b011)) ((_ bit_of 1) (ite a #b110 #b011))))) :rule bitblast_extract)": true,
              "(step t3 (cl (= ((_ extract 1 0) (bbterm ((_ bit_of 0) (ite a #b110 #b011)) ((_ bit_of 1) (ite a #b110 #b011)) ((_ bit_of 2) (ite a #b110 #b011)))) (bbterm ((_ bit_of 0) (ite a #b111 #b011)) ((_ bit_of 1) (ite a #b111 #b011))))) :rule bitblast_extract)": false,
              "(step t4 (cl (= ((_ extract 11 4) (bbterm ((_ bit_of 0) zz) ((_ bit_of 1) zz) ((_ bit_of 2) zz) ((_ bit_of 3) zz) ((_ bit_of 4) zz) ((_ bit_of 5) zz) ((_ bit_of 6) zz) ((_ bit_of 7) zz) ((_ bit_of 8) zz) ((_ bit_of 9) zz) ((_ bit_of 10) zz) ((_ bit_of 11) zz))) (bbterm ((_ bit_of 4) zz) ((_ bit_of 5) zz) ((_ bit_of 6) zz) ((_ bit_of 7) zz) ((_ bit_of 8) zz) ((_ bit_of 9) zz) ((_ bit_of 10) zz) ((_ bit_of 11) zz)))) :rule bitblast_extract)": true,
              "(step t5 (cl (= ((_ extract 11 4) (bbterm ((_ bit_of 0) zz) ((_ bit_of 1) zz) ((_ bit_of 2) zz) ((_ bit_of 3) zz) ((_ bit_of 4) zz) ((_ bit_of 5) zz) ((_ bit_of 6) zz) ((_ bit_of 7) zz) ((_ bit_of 8) zz) ((_ bit_of 9) zz) ((_ bit_of 10) zz) ((_ bit_of 11) zz))) (bbterm ((_ bit_of 3) zz) ((_ bit_of 5) zz) ((_ bit_of 6) zz) ((_ bit_of 7) zz) ((_ bit_of 8) zz) ((_ bit_of 9) zz) ((_ bit_of 10) zz) ((_ bit_of 11) zz)))) :rule bitblast_extract)": false,
            }
        }
    }
}
