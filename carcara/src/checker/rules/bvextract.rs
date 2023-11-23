use crate::{
    ast::{IndexedOperator, Operator, Term},
    checker::{
        error::{CheckerError, ExtractError},
        rules::assert_clause_len,
    },
};

use super::{RuleArgs, RuleResult};

// ((_ extract i j) x) ≃ (bbterm xj;...;xi)
pub fn extract(RuleArgs { conclusion, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (left, right) = match_term_err!((= l r) = &conclusion[0])?;
    let left_terms = match left.as_ref() {
        Term::IndexedOp {
            op: IndexedOperator::BvExtract,
            op_args,
            args,
        } => {
            let i = op_args[0].as_integer().unwrap().to_usize().unwrap();
            let j = op_args[1].as_integer().unwrap().to_usize().unwrap();
            let x = args[0].clone();
            Ok((i, j, x))
        }
        _ => Err(ExtractError::WrongLeftTerm),
    };
    let (left_i, left_j, left_x) = left_terms.unwrap();
    let size = left_i - left_j + 1;
    match right.as_ref() {
        Term::Op(Operator::BvBbTerm, args) => {
            assert_eq!(args.len(), size);
            let (_, left_x_args) = left_x.as_op().unwrap();
            // dbg!(args, left_x_args);
            assert_eq!(args, &left_x_args[left_j..=left_i]);
            Ok(())
        }
        _ => Err(CheckerError::Extract(ExtractError::WrongRightTerm)),
    }
}

#[cfg(test)]

mod tests {
    #[test]
    fn extract() {
        test_cases! {
            definitions = "
            (declare-fun a () Bool)
            ",
            "Simple working examples" {
              // "(step t1 (cl (= ((_ extract 5 3) #b01100000) ((_ extract 4 3) #b01100000))) :rule bitblast_extract)": false,
              "(step t2 (cl (= ((_ extract 1 0) (bbterm ((_ bit_of 0) (ite a #b110 #b011)) ((_ bit_of 1) (ite a #b110 #b011)) ((_ bit_of 2) (ite a #b110 #b011)))) (bbterm ((_ bit_of 0) (ite a #b110 #b011)) ((_ bit_of 1) (ite a #b110 #b011))))) :rule bitblast_extract)": true,
              // "(step t3 (cl (= ((_ extract 1 0) (bbterm ((_ bit_of 0) (ite a #b110 #b011)) ((_ bit_of 1) (ite a #b110 #b011)) ((_ bit_of 2) (ite a #b110 #b011)))) (bbterm ((_ bit_of 0) (ite a #b110 #b011))))) :rule bitblast_extract)": false,
            }
        }
    }
}
