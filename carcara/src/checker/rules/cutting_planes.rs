use super::{assert_clause_len, assert_num_args, assert_num_premises, RuleArgs, RuleResult};
use rug::Integer;

/*
(step t1 (cl
            (>=
                (+ (* 2 x1) (* 4 x2) (* 2 x3))
                4)
            )
    :rule cp_multiplication
    :premises (c1)
)
(step t2 (cl
            (>=
                (+ (* 3 x1) (* 6 x2) (* 6 x3) (* 2 x4))
                9)
            )
    :rule cp_addition
    :premises (t1 c2)
)
(step t3 (cl
            (>=
                (* 2 (- 1 x4))
                0)
            )
    :rule cp_multiplication
    :premises (c3)
)
(step t4 (cl
             (>=
                (+ (* 3 x1) (* 6 x2) (* 6 x3))
                7)
            )
    :rule cp_addition
    :premises (t2 t3)
)
(step t5 (cl
             (>=
                (+ x1 (* 2 x2) (* 2 x3))
                3)
            )
    :rule cp_division
    :premises (t4)
)
*/

pub fn cp_addition(
    RuleArgs {
        premises,
        args,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    println!("Addition");
    Ok(())
}

pub fn cp_multiplication(
    RuleArgs {
        premises,
        args,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    // Check there is exactly one premise
    assert_num_premises(premises, 1)?;

    // Check there is exactly one arg
    assert_num_args(args, 1)?;
    let scalar: Integer = args[0].as_term()?.as_integer_err()?;
    println!("scalar = {}", scalar);

    // Check there is exactly one conclusion
    assert_clause_len(conclusion, 1)?;
    let conclusion = conclusion[0].clone();

    // For every term of the conclusion,
    // check it's equal to the corresponding term
    // in the premise times the scalar

    // let final_stuff = conclusion.iter().zip(premises).map(|(c, p)| {
    //     println!("{} {}"c, p);
    // });

    println!("Multiplication");
    // println!("{} args:", args.len());
    // for arg in args {
    //     let k = arg.as_term()?.as_integer_err()?;
    //     println!("{}", k);
    // }
    println!("Got {} premises:", premises.len());
    for premise in premises {
        println!("{}", premise.id);
        println!("{} clauses", premise.clause.len());
        for clause in premise.clause {
            println!("{}", clause);
        }
    }
    assert_num_premises(premises, 1)?;

    println!("{}", conclusion);

    Ok(())
}

pub fn cp_division(
    RuleArgs {
        premises,
        args,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    println!("Division");
    Ok(())
}

pub fn cp_saturation(
    RuleArgs {
        premises,
        args,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    println!("Saturation");
    Ok(())
}

mod tests {
    #[test]
    fn cp_addition() {
        test_cases! {
           definitions = "
                (declare-fun x1 () Int)
                ",
            "Simple working examples" {
                r#"(assume c1 (>= x1 1))
                   (step t1 (cl (>= (* 2 x1) 2)) :rule cp_addition :premises (c1 c1))"#: true,
            }

        }
    }
    #[test]
    fn cp_multiplication() {
        test_cases! {
            definitions = "
                (declare-fun x1 () Int)
                ",
            "Simple working examples" {
                r#"(assume c1 (>= x1 1))
                   (step t1 (cl (>= (* 2 x1) 2)) :rule cp_multiplication :premises (c1) :args (2))"#: true,
            }
            "Wrong number of premises" {
                r#"(assume c1 (>= x1 1))
                   (step t1 (cl (>= (* 2 x1) 2)) :rule cp_multiplication :args (2))"#: false,
                r#"(assume c1 (>= x1 1))
                   (step t1 (cl (>= (* 2 x1) 2)) :rule cp_multiplication :premises (c1 c1) :args (2))"#: false,
            }
            "Wrong number of args" {
                r#"(assume c1 (>= x1 1))
                   (step t1 (cl (>= (* 2 x1) 2)) :rule cp_multiplication :premises (c1))"#: false,
                r#"(assume c1 (>= x1 1))
                   (step t1 (cl (>= (* 2 x1) 2)) :rule cp_multiplication :premises (c1) :args (2 3))"#: false,
            }
            // "Wrong number of clauses in the conclusion" {
            //     r#"(assume c1 (>= x1 1))
            //        (step t1 (cl ()) :rule cp_multiplication :premises (c1) :args (2))"#: false,
            // }
        }
    }
    #[test]
    fn cp_division() {
        test_cases! {
            definitions = "
                (declare-fun x1 () Int)
                ",
            "Simple working examples" {
                r#"(assume c1 (>= (* 2 x1) 2))
                   (step t1 (cl (>= x1 1)) :rule cp_division :premises (c1) :args (2) )"#: true,
            }
        }
    }
    #[test]
    fn cp_saturation() {
        test_cases! {
            definitions = "
                (declare-fun x1 () Int)
                ",
            "Simple working examples" {
                r#"(assume c1 (>= (* 2 x1) 1))
                   (step t1 (cl (>= x1 1)) :rule cp_division :premises (c1))"#: true,
            }
        }
    }
}
