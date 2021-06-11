use super::{get_single_term_from_command, to_option, RuleArgs};
use crate::ast::*;

pub fn distinct_elim(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    if conclusion.len() != 1 {
        return None;
    }

    let (distinct_args, second_term) = match_term!((= (distinct ...) second) = conclusion[0])?;
    match distinct_args {
        [] | [_] => unreachable!(),
        [a, b] => {
            let got: (&Term, &Term) = match_term!((not (= x y)) = second_term)?;
            to_option(got == (a, b) || got == (b, a))
        }
        args => {
            if args[0].sort() == Term::BOOL_SORT {
                // If there are more than two boolean arguments to the distinct operator, the
                // second term must be "false"
                return match second_term.try_as_var() {
                    Some("false") => Some(()),
                    _ => None,
                };
            }
            let got = match_term!((and ...) = second_term)?;
            let mut k = 0;
            for i in 0..args.len() {
                for j in i + 1..args.len() {
                    let (a, b) = (args[i].as_ref(), args[j].as_ref());
                    let got = match_term!((not (= x y)) = got[k])?;
                    to_option(got == (a, b) || got == (b, a))?;
                    k += 1;
                }
            }
            Some(())
        }
    }
}

pub fn and(
    RuleArgs {
        conclusion,
        premises,
        ..
    }: RuleArgs,
) -> Option<()> {
    if premises.len() != 1 || conclusion.len() != 1 {
        return None;
    }
    let and_term = get_single_term_from_command(premises[0])?;
    let and_contents = match_term!((and ...) = and_term)?;

    to_option(and_contents.iter().any(|t| t == &conclusion[0]))
}

pub fn or(
    RuleArgs {
        conclusion,
        premises,
        ..
    }: RuleArgs,
) -> Option<()> {
    if premises.len() != 1 {
        return None;
    }
    let or_term = get_single_term_from_command(premises[0])?;
    let or_contents = match_term!((or ...) = or_term)?;

    to_option(or_contents == conclusion)
}

pub fn implies(
    RuleArgs {
        conclusion,
        premises,
        ..
    }: RuleArgs,
) -> Option<()> {
    if premises.len() != 1 || conclusion.len() != 2 {
        return None;
    }
    let premise_term = get_single_term_from_command(premises[0])?;
    let (phi_1, phi_2) = match_term!((=> phi_1 phi_2) = premise_term)?;

    to_option(phi_1 == conclusion[0].remove_negation()? && phi_2 == conclusion[1].as_ref())
}

pub fn nary_elim(RuleArgs { conclusion, .. }: RuleArgs) -> Option<()> {
    // The three possible cases for n-ary operators: chainable, right associative and left
    // associative
    #[derive(Debug, PartialEq, Eq)]
    enum Case {
        Chainable,
        RightAssoc,
        LeftAssoc,
    }

    // A function to check the right and left associative cases. Consider as an example the
    // term (=> p q r s) being transformed into the term (=> p (=> q (=> r s))). This function
    // checks that the operators match, checks that the head argument "p" matches the left-hand
    // argument in the result term (as the operator is right associative) and then calls itself
    // recursively passing the "tail" (=> q r s) and the right-hand argument (=> q (=> r s)).
    // If the operator was right associative, the "head" argument would be the last, and the
    // nested term would be the left-hand arugment of the result term. In the base case, the
    // function will be called with the terms (=> s) and s, and it only needs to compare the
    // two "s"s
    fn check_assoc(
        op: Operator,
        args: &[ByRefRc<Term>],
        result_term: &Term,
        is_right: bool,
    ) -> bool {
        let (head, tail) = match args {
            [] => return false,
            [t] => return t.as_ref() == result_term,

            // The "head" term will be the first or last term in `args`, depending on if the
            // operator is right or left associative
            [first, rest @ ..] if is_right => (first, rest),
            [rest @ .., last] => (last, rest),
        };
        if let Term::Op(got_op, got_args) = result_term {
            // The result term must have only two arguments, and which of them is the nested
            // operation depends on if the operator is right or left associative
            let (got_head, nested) = match got_args.as_slice() {
                [a, b] if is_right => (a, b),
                [a, b] => (b, a),
                _ => return false,
            };

            // Check that the operator and the "head" term match, and call the function
            // recursively on the remaining terms and the nested operation term
            *got_op == op && got_head == head && check_assoc(op, tail, nested, is_right)
        } else {
            false
        }
    }

    if conclusion.len() != 1 {
        return None;
    }
    let (original, result) = match_term!((= o r) = conclusion[0].as_ref())?;
    if let Term::Op(op, args) = original {
        let case = match op {
            Operator::Eq => Case::Chainable,
            Operator::Add | Operator::Sub | Operator::Mult => Case::LeftAssoc,
            Operator::Implies => Case::RightAssoc,
            _ => return None,
        };
        to_option(match case {
            Case::Chainable => {
                // For every term in the chain, check that the operator is the correct one, and
                // extract its arguments
                let chain = match_term!((and ...) = result)?.iter().map(|chain_term| {
                    if let Term::Op(got_op, got_args) = chain_term.as_ref() {
                        if got_op == op {
                            return Some(got_args.as_slice());
                        }
                    }
                    None
                });
                // The terms in the chain should be the operation applied to every two adjacent
                // terms in the original term's arguments. `args.windows(2)` returns an
                // iterator over the pairs of adjacent terms
                args.windows(2).map(Some).eq(chain)
            }
            assoc_case => check_assoc(*op, &args, result, assoc_case == Case::RightAssoc),
        })
    } else {
        None
    }
}
