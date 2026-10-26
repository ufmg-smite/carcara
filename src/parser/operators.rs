//! A declarative rule DSL for type-checking SMT-LIB operators, used by `Parser::make_op`.

use super::{
    Parser,
    error::{ParserError, SortError, assert_num_args, check_relation_sort},
};
use crate::{
    ast::{Constant, Operator, Rc, Sort, Term},
    automata::parser::parse_automaton,
    utils::Range,
};

/// The sorts a single operator argument is allowed to have.
enum ArgSort {
    /// The argument must have exactly this sort.
    Exact(Sort),
    /// The argument must have one of these sorts.
    OneOf(&'static [Sort]),
    /// The argument must have any bitvector sort.
    AnyBitVec,
    /// The argument's sort must satisfy this predicate.
    Predicate(fn(&Rc<Sort>) -> Result<(), ParserError>),
}

impl ArgSort {
    /// Checks that `sort` satisfies this constraint.
    fn check(&self, parser: &mut Parser, sort: &Rc<Sort>) -> Result<(), ParserError> {
        match self {
            ArgSort::Exact(expected) => Ok(parser.check_sort_eq(expected, sort)?),
            ArgSort::OneOf(possibilities) => Ok(parser.check_sort_one_of(possibilities, sort)?),
            ArgSort::AnyBitVec if sort.is_bitvec() => Ok(()),
            ArgSort::AnyBitVec => Err(ParserError::ExpectedBvSort(sort.clone())),
            ArgSort::Predicate(f) => f(sort),
        }
    }
}

/// How the sorts of an operator's arguments, as a whole, should be checked.
enum ArgsCheck {
    /// No per-argument sort checks.
    Unconstrained,
    /// Every argument independently satisfies this constraint.
    Each(ArgSort),
    /// The first argument satisfies this constraint, then all arguments are pairwise equal.
    FirstThenAllEq(ArgSort),
    /// All arguments are pairwise equal, with no other constraint.
    AllEq,
    /// One explicit constraint per argument position.
    Positional(&'static [ArgSort]),
}

impl ArgsCheck {
    /// Checks that `sorts` satisfies this constraint.
    fn check(&self, parser: &mut Parser, sorts: &[Rc<Sort>]) -> Result<(), ParserError> {
        match self {
            ArgsCheck::Unconstrained => Ok(()),
            ArgsCheck::Each(arg_sort) => {
                for sort in sorts {
                    arg_sort.check(parser, sort)?;
                }
                Ok(())
            }
            ArgsCheck::FirstThenAllEq(arg_sort) => {
                arg_sort.check(parser, &sorts[0])?;
                Ok(parser.check_sort_all_eq(sorts)?)
            }
            ArgsCheck::AllEq => Ok(parser.check_sort_all_eq(sorts)?),
            ArgsCheck::Positional(arg_sorts) => {
                for (arg_sort, sort) in arg_sorts.iter().zip(sorts) {
                    arg_sort.check(parser, sort)?;
                }
                Ok(())
            }
        }
    }
}

/// How an operator's arity should be checked.
enum ArityRule {
    /// A fixed arity range.
    Fixed(Range),
    /// The allowed arity range depends on whether the parser is in "strict" mode.
    StrictDependent { strict: Range, lenient: Range },
}

/// A declarative type-checking rule for an operator.
struct Rule {
    arity: ArityRule,
    args: ArgsCheck,
}

impl Rule {
    /// Creates a rule with a fixed arity range.
    fn arity(range: impl Into<Range>, args: ArgsCheck) -> Self {
        Self {
            arity: ArityRule::Fixed(range.into()),
            args,
        }
    }

    /// Creates a rule whose arity range depends on the parser's "strict" mode setting.
    fn strict_arity(strict: impl Into<Range>, lenient: impl Into<Range>, args: ArgsCheck) -> Self {
        Self {
            arity: ArityRule::StrictDependent {
                strict: strict.into(),
                lenient: lenient.into(),
            },
            args,
        }
    }

    /// Checks that `sorts` satisfies this rule's arity and argument sort constraints.
    fn check(self, parser: &mut Parser, sorts: &[Rc<Sort>]) -> Result<(), ParserError> {
        let range = match self.arity {
            ArityRule::Fixed(range) => range,
            ArityRule::StrictDependent { strict, lenient } => {
                if parser.config.strict {
                    strict
                } else {
                    lenient
                }
            }
        };
        assert_num_args(sorts, range)?;
        self.args.check(parser, sorts)
    }
}

/// The sorts `Int` and `Real`, used by several arithmetic operators.
const INT_OR_REAL: &[Sort] = &[Sort::Int, Sort::Real];

/// Builds the `ArgsCheck` shared by `+`, `-` and `*`, which depends on Int/Real subtyping.
fn int_or_real_args(subtyping: bool) -> ArgsCheck {
    if subtyping {
        ArgsCheck::Each(ArgSort::OneOf(INT_OR_REAL))
    } else {
        ArgsCheck::FirstThenAllEq(ArgSort::OneOf(INT_OR_REAL))
    }
}

/// Whether an operator's type checking is expressed declaratively or requires custom logic.
enum OpCheck {
    Rule(Rule),
    Custom,
}

/// Returns the type-checking behavior for `op`, given whether Int/Real subtyping is allowed.
fn op_check(op: Operator, subtyping: bool) -> OpCheck {
    use ArgSort::{AnyBitVec, Exact, OneOf, Predicate};
    use ArgsCheck::{AllEq, Each, FirstThenAllEq, Positional, Unconstrained};

    match op {
        Operator::True | Operator::False => OpCheck::Rule(Rule::arity(0, Unconstrained)),
        Operator::Not => OpCheck::Rule(Rule::arity(1, Each(Exact(Sort::Bool)))),
        Operator::Implies => OpCheck::Rule(Rule::arity(2.., Each(Exact(Sort::Bool)))),
        Operator::Or | Operator::And | Operator::Xor => {
            OpCheck::Rule(Rule::strict_arity(2.., 1.., Each(Exact(Sort::Bool))))
        }
        Operator::Equals | Operator::Distinct => OpCheck::Rule(Rule::arity(2.., AllEq)),
        Operator::Ite => OpCheck::Custom,
        Operator::Add | Operator::Mult => {
            OpCheck::Rule(Rule::arity(2.., int_or_real_args(subtyping)))
        }
        Operator::Sub => OpCheck::Rule(Rule::arity(1.., int_or_real_args(subtyping))),
        Operator::IntDiv => OpCheck::Rule(Rule::arity(2.., FirstThenAllEq(Exact(Sort::Int)))),
        Operator::RealDiv => OpCheck::Custom,
        Operator::Mod => OpCheck::Rule(Rule::arity(
            2,
            Positional(&[Exact(Sort::Int), Exact(Sort::Int)]),
        )),
        Operator::Abs => {
            let args = if subtyping {
                Each(OneOf(INT_OR_REAL))
            } else {
                Each(Exact(Sort::Int))
            };
            OpCheck::Rule(Rule::arity(1, args))
        }
        Operator::LessThan | Operator::GreaterThan | Operator::LessEq | Operator::GreaterEq => {
            OpCheck::Rule(Rule::arity(2.., Each(OneOf(INT_OR_REAL))))
        }
        Operator::ToReal => OpCheck::Rule(Rule::arity(1, Each(OneOf(INT_OR_REAL)))),
        Operator::ToInt | Operator::IsInt => OpCheck::Rule(Rule::arity(1, Each(Exact(Sort::Real)))),
        Operator::Select => OpCheck::Custom,
        Operator::Store => OpCheck::Custom,
        Operator::StrConcat => OpCheck::Rule(Rule::arity(2.., Each(Exact(Sort::String)))),
        Operator::StrLen | Operator::StrIsDigit | Operator::StrToCode | Operator::StrToInt => {
            OpCheck::Rule(Rule::arity(1, Each(Exact(Sort::String))))
        }
        Operator::StrLessThan
        | Operator::StrLessEq
        | Operator::PrefixOf
        | Operator::SuffixOf
        | Operator::Contains
        | Operator::ReRange => OpCheck::Rule(Rule::arity(2, Each(Exact(Sort::String)))),
        Operator::CharAt => OpCheck::Rule(Rule::arity(
            2,
            Positional(&[Exact(Sort::String), Exact(Sort::Int)]),
        )),
        Operator::Substring => OpCheck::Rule(Rule::arity(
            3,
            Positional(&[Exact(Sort::String), Exact(Sort::Int), Exact(Sort::Int)]),
        )),
        Operator::IndexOf => OpCheck::Rule(Rule::arity(
            3,
            Positional(&[Exact(Sort::String), Exact(Sort::String), Exact(Sort::Int)]),
        )),
        Operator::Replace | Operator::ReplaceAll => {
            OpCheck::Rule(Rule::arity(3, Each(Exact(Sort::String))))
        }
        Operator::ReFromAutomaton => OpCheck::Custom,
        Operator::StrFromCode | Operator::StrFromInt => {
            OpCheck::Rule(Rule::arity(1, Each(Exact(Sort::Int))))
        }
        Operator::StrToRe => OpCheck::Rule(Rule::arity(1, Each(Exact(Sort::String)))),
        Operator::StrInRe => OpCheck::Rule(Rule::arity(
            2,
            Positional(&[Exact(Sort::String), Exact(Sort::RegLan)]),
        )),
        Operator::ReNone | Operator::ReAll | Operator::ReAllChar => {
            OpCheck::Rule(Rule::arity(0, Unconstrained))
        }
        Operator::ReConcat | Operator::ReUnion | Operator::ReIntersection | Operator::ReDiff => {
            OpCheck::Rule(Rule::arity(2.., Each(Exact(Sort::RegLan))))
        }
        Operator::ReKleeneClosure
        | Operator::ReComplement
        | Operator::ReKleeneCross
        | Operator::ReOption => OpCheck::Rule(Rule::arity(1, Each(Exact(Sort::RegLan)))),
        Operator::ReplaceRe | Operator::ReplaceReAll => OpCheck::Rule(Rule::arity(
            3,
            Positional(&[
                Exact(Sort::String),
                Exact(Sort::RegLan),
                Exact(Sort::String),
            ]),
        )),
        Operator::BvNot | Operator::BvNeg => OpCheck::Rule(Rule::arity(1, Each(AnyBitVec))),
        Operator::BvSize | Operator::UBvToInt | Operator::SBvToInt => {
            OpCheck::Rule(Rule::arity(1, Each(AnyBitVec)))
        }
        Operator::BvBbTerm => OpCheck::Rule(Rule::arity(1.., FirstThenAllEq(Exact(Sort::Bool)))),
        Operator::BvPBbTerm => OpCheck::Rule(Rule::arity(1.., FirstThenAllEq(Exact(Sort::Int)))),
        Operator::BvConst => OpCheck::Rule(Rule::arity(2, Each(Exact(Sort::Int)))),
        // Note: not all-equal here -- different bitvector widths are allowed in `concat`
        Operator::BvConcat => OpCheck::Rule(Rule::arity(2.., Each(AnyBitVec))),
        Operator::Cl => OpCheck::Rule(Rule::arity(.., Unconstrained)),
        Operator::Delete => OpCheck::Rule(Rule::arity(1, Each(Exact(Sort::Bool)))),
        Operator::BvAdd | Operator::BvMul | Operator::BvAnd | Operator::BvOr | Operator::BvXor => {
            OpCheck::Rule(Rule::arity(2.., FirstThenAllEq(AnyBitVec)))
        }
        Operator::BvUDiv
        | Operator::BvURem
        | Operator::BvShl
        | Operator::BvLShr
        | Operator::BvULt
        | Operator::BvNAnd
        | Operator::BvNOr
        | Operator::BvXNor
        | Operator::BvComp
        | Operator::BvSub
        | Operator::BvSDiv
        | Operator::BvSRem
        | Operator::BvSMod
        | Operator::BvAShr
        | Operator::BvULe
        | Operator::BvUGt
        | Operator::BvUGe
        | Operator::BvSLt
        | Operator::BvSLe
        | Operator::BvSGt
        | Operator::BvSGe => OpCheck::Rule(Rule::arity(2, FirstThenAllEq(AnyBitVec))),
        Operator::BvIte => OpCheck::Custom,
        Operator::RareList => OpCheck::Rule(Rule::arity(.., Unconstrained)),
        Operator::SetInsert => OpCheck::Custom,
        Operator::Tuple => OpCheck::Rule(Rule::arity(1.., Unconstrained)),
        Operator::RelTranspose => {
            OpCheck::Rule(Rule::arity(1, Each(Predicate(check_relation_sort))))
        }
        // TODO: `rel.join`/`rel.product` sort checking could be more precise
        Operator::RelJoin | Operator::RelProduct => {
            OpCheck::Rule(Rule::arity(2, Each(Predicate(check_relation_sort))))
        }
        _ => OpCheck::Custom,
    }
}

/// Handles type checking for the operators whose rules don't fit the declarative `Rule` DSL.
fn custom_check(
    parser: &mut Parser,
    op: Operator,
    args: &[Rc<Term>],
    sorts: &[Rc<Sort>],
) -> Result<Option<Rc<Term>>, ParserError> {
    match op {
        Operator::Ite => {
            assert_num_args(sorts, 3)?;
            parser.check_sort_eq(&Sort::Bool, &sorts[0])?;
            parser.check_sort_eq(sorts[1].as_ref(), &sorts[2])?;
            Ok(None)
        }
        Operator::RealDiv => {
            // Normally, the `/` operator may only receive Real arguments, but if we are allowing
            // Int/Real subtyping, it may also receive Ints
            let args_check = if parser.config.allow_int_real_subtyping {
                ArgsCheck::Each(ArgSort::OneOf(INT_OR_REAL))
            } else {
                ArgsCheck::FirstThenAllEq(ArgSort::Exact(Sort::Real))
            };
            Rule::arity(2.., args_check).check(parser, sorts)?;
            match args {
                [a, b] => Ok(parser.interpret_div_as_real_lit(a, b)),
                _ => Ok(None),
            }
        }
        Operator::Select => {
            assert_num_args(sorts, 2)?;
            parser.check_array_sort(Some(&sorts[1]), None, &sorts[0])?;
            Ok(None)
        }
        Operator::Store => {
            assert_num_args(sorts, 3)?;
            parser.check_array_sort(Some(&sorts[1]), Some(&sorts[2]), &sorts[0])?;
            Ok(None)
        }
        Operator::ReFromAutomaton => {
            assert_num_args(sorts, 1)?;
            parser.check_sort_eq(&Sort::String, &sorts[0])?;
            if let Term::Const(Constant::String(s)) = args[0].as_ref() {
                let automata = match parse_automaton(s.trim()) {
                    Ok((remaining, automata)) => {
                        if !remaining.is_empty() {
                            return Err(ParserError::InvalidAutomatonDeclaration(s.clone()));
                        }
                        Ok(automata)
                    }
                    Err(_) => Err(ParserError::InvalidAutomatonDeclaration(s.clone())),
                }?;
                Ok(Some(parser.pool.add(Term::Const(Constant::RegLan(
                    s.to_owned(),
                    automata,
                )))))
            } else {
                Err(ParserError::ExpectedAnAutomatonDeclaration(args[0].clone()))
            }
        }
        Operator::SetInsert => {
            assert_num_args(sorts, 2..)?;
            parser.check_sort_all_eq(&sorts[..sorts.len() - 1])?;
            let expected = parser.pool.add_sort(Sort::Set(sorts[0].clone()));
            parser.check_sort_eq(&expected, sorts.last().unwrap())?;
            Ok(None)
        }
        Operator::BvIte => {
            assert_num_args(sorts, 3)?;
            parser.check_sort_eq(&Sort::BitVec(1), &sorts[0])?;
            parser.check_sort_all_eq(&sorts[1..])?;
            Ok(None)
        }
        other => {
            let sig = other.sig().unwrap();
            assert_num_args(sorts, sig.arg_sorts.len())?;
            let mut params = vec![None; sig.params.len()];
            for (arg_sig, got) in sig.arg_sorts.iter().zip(sorts) {
                if !arg_sig.match_with(&mut params, got) {
                    let expected = arg_sig.instantiate(parser.pool, &params, sig.params);
                    let expected = vec![expected].into_boxed_slice();
                    return Err(SortError { expected, got: got.clone() }.into());
                }
            }
            Ok(None)
        }
    }
}

/// Type checks the arguments of an operator term, returning a replacement term if the operator
/// builds one, or `None` if the caller should build the default `Term::Op(op, args)`.
pub(super) fn check_op_types(
    parser: &mut Parser,
    op: Operator,
    args: &[Rc<Term>],
    sorts: &[Rc<Sort>],
) -> Result<Option<Rc<Term>>, ParserError> {
    match op_check(op, parser.config.allow_int_real_subtyping) {
        OpCheck::Rule(rule) => {
            rule.check(parser, sorts)?;
            Ok(None)
        }
        OpCheck::Custom => custom_check(parser, op, args, sorts),
    }
}
