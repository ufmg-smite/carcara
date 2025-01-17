use super::{RuleArgs, RuleResult};
use crate::checker::error::CheckerError;

pub fn pbblast_bveq(RuleArgs { premises, args, conclusion, .. }: RuleArgs) -> RuleResult {
    println!("{} {} {}", premises.len(), args.len(), conclusion.len());
    Err(CheckerError::Unspecified)
}

mod tests {
    #[test]
    fn pbblast_bveq() {
        test_cases! {
           definitions = "
                (declare-fun x1 () Int)
                (declare-fun x2 () Int)
                ",
            "Dummy Test" {
                r#"(assume c1 (>= (+ (* 1 (- 1 x1)) 0) 1))
                   (assume c2 (>= (+ (* 2 x1) 0) 1))
                   (step t1 (cl (>= (+ (* 1 x1) (* 0 x2) 0) 1)) :rule pbblast_bveq :premises (c1 c2))"#: true,
            }
        }
    }
}
