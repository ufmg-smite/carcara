//! Type checking and term construction for SMT-LIB operators.

use super::{
    Parser,
    error::{ParserError, SortError, assert_indexed_op_args_value, assert_num_args},
};
use crate::{
    ast::{Constant, Operator, OperatorSig, ParamOperator, QualifiedOperator, Rc, Sort, Term},
    automata::parser::parse_automaton,
    utils::Range,
};
use rug::{Integer, Rational};

impl<'p, 's> Parser<'p, 's> {
    /// Constructs and type checks an operation term.
    pub(super) fn make_op(
        &mut self,
        op: Operator,
        args: Vec<Rc<Term>>,
    ) -> Result<Rc<Term>, ParserError> {
        if let Some(term) = self.type_check_op(op, &args)? {
            return Ok(term);
        }
        Ok(self.pool.add(Term::Op(op, args)))
    }

    /// Constructs and type checks an indexed operation term.
    pub(super) fn make_indexed_op(
        &mut self,
        op: ParamOperator,
        op_args: Vec<Rc<Term>>,
        args: Vec<Rc<Term>>,
    ) -> Result<Rc<Term>, ParserError> {
        if let Some(term) = self.type_check_indexed_op(op, &op_args, &args)? {
            return Ok(term);
        }
        Ok(self.pool.add(Term::ParamOp { op, op_args, args }))
    }

    /// Constructs and type checks a qualified operation term.
    pub(super) fn make_qualified_op(
        &mut self,
        op: QualifiedOperator,
        sort: Rc<Sort>,
        args: Vec<Rc<Term>>,
    ) -> Result<Rc<Term>, ParserError> {
        let sorts: Vec<_> = args.iter().map(|t| self.pool.sort(t)).collect();
        match op {
            QualifiedOperator::Const => {
                assert_num_args(&args, 1)?;
                self.check_array_sort(None, Some(&sorts[0]), &sort)?;
            }
            QualifiedOperator::SetEmpty | QualifiedOperator::SetUniverse => {
                assert_num_args(&args, 0)?;
                if !matches!(sort.as_ref(), Sort::Set(_)) {
                    return Err(ParserError::ExpectedSetSort(sort.clone()));
                }
            }
        }
        Ok(self.pool.add(Term::AsOp(op, sort, args)))
    }

    /// Type checks the arguments of an operation term.
    ///
    /// Returns `None` if the caller should build the default `Term::Op(op, args)`, or `Some` term
    /// if the operator has special term construction.
    fn type_check_op(
        &mut self,
        op: Operator,
        args: &[Rc<Term>],
    ) -> Result<Option<Rc<Term>>, ParserError> {
        let sorts: Vec<_> = args.iter().map(|t| self.pool.sort(t)).collect();
        match op {
            // These are defined in `operators.toml`, but unary `and`, `or` and `xor` terms are
            // allowed outside of strict mode
            Operator::And | Operator::Or | Operator::Xor
                if sorts.len() == 1 && !self.config.strict =>
            {
                self.check_sort_eq(&Sort::Bool, &sorts[0])?;
            }
            // These are defined in `operators.toml`, but mixing `Int` and `Real` arguments is
            // allowed even without Int/Real subtyping, since some solvers (e.g. veriT) produce
            // terms like that
            Operator::LessThan | Operator::GreaterThan | Operator::LessEq | Operator::GreaterEq => {
                self.check_op_sig(op, &sorts, true)?;
            }
            // This is defined in `operators.toml`, but with Int/Real subtyping it also accepts
            // `Int` arguments, which its signature can't express
            Operator::RealDiv => {
                if self.config.allow_int_real_subtyping {
                    assert_num_args(&sorts, 2..)?;
                    self.check_sort_all(&[Sort::Int, Sort::Real], &sorts)?;
                } else {
                    self.check_op_sig(op, &sorts, false)?;
                }
                // Division of integer constants can be interpreted as a rational literal
                if let [a, b] = args {
                    return Ok(self.interpret_div_as_real_lit(a, b));
                }
            }
            Operator::ReFromAutomaton => {
                assert_num_args(&sorts, 1)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
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
                    return Ok(Some(
                        self.pool
                            .add(Term::Const(Constant::RegLan(s.to_owned(), automata))),
                    ));
                } else {
                    return Err(ParserError::ExpectedAnAutomatonDeclaration(args[0].clone()));
                }
            }
            Operator::SetInsert => {
                assert_num_args(&sorts, 2..)?;
                let first = sorts.first().unwrap().as_ref();
                self.check_sort_all(std::slice::from_ref(first), &sorts[1..sorts.len() - 1])?;
                let expected = self.pool.add_sort(Sort::Set(sorts[0].clone()));
                self.check_sort_eq(&expected, sorts.last().unwrap())?;
            }
            Operator::BvBbTerm => {
                assert_num_args(&sorts, 1..)?;
                self.check_sort_all(&[Sort::Bool], &sorts)?;
            }
            Operator::BvPBbTerm => {
                assert_num_args(&sorts, 1..)?;
                self.check_sort_all(&[Sort::Int], &sorts)?;
            }
            Operator::BvConst => {
                assert_num_args(&sorts, 2)?;
                self.check_sort_all(&[Sort::Int], &sorts)?;
            }
            // Different bitvector widths are allowed in `concat`
            Operator::BvConcat => {
                assert_num_args(&sorts, 2..)?;
                if let Some(sort) = sorts.iter().find(|s| !s.is_bitvec()) {
                    return Err(ParserError::ExpectedBvSort(sort.clone()));
                }
            }
            Operator::Cl | Operator::RareList => (),
            Operator::Tuple => assert_num_args(&sorts, 1..)?,
            // TODO: `rel.join`/`rel.product` sort checking could be more precise
            Operator::RelTranspose | Operator::RelJoin | Operator::RelProduct => {
                assert_num_args(&sorts, if op == Operator::RelTranspose { 1 } else { 2 })?;
                for s in &sorts {
                    let Sort::Set(tuple) = s.as_ref() else {
                        return Err(ParserError::ExpectedSetSort(s.clone()));
                    };
                    if !matches!(tuple.as_ref(), Sort::Tuple(_)) {
                        return Err(ParserError::ExpectedTupleSort(tuple.clone()));
                    }
                }
            }
            other => self.check_op_sig(other, &sorts, self.config.allow_int_real_subtyping)?,
        }
        Ok(None)
    }

    /// Checks `sorts` against the signature of `op`, which must be defined in `operators.toml`.
    fn check_op_sig(
        &mut self,
        op: Operator,
        sorts: &[Rc<Sort>],
        subtyping: bool,
    ) -> Result<(), ParserError> {
        let sig = op.sig().unwrap();
        let arity: Range = if sig.nary.is_some() {
            (sig.arg_sorts.len()..).into()
        } else {
            sig.arg_sorts.len().into()
        };
        assert_num_args(sorts, arity)?;
        let mut params = [const { None }; OperatorSig::MAX_SORT_PARAMS];
        let params = &mut params[..sig.params.len()];
        for (arg_sig, got) in sig.arg_sigs().zip(sorts) {
            if !arg_sig.match_with(params, got, subtyping) {
                let expected = arg_sig.instantiate(self.pool, params, sig.params);
                let expected = vec![expected].into_boxed_slice();
                return Err(SortError { expected, got: got.clone() }.into());
            }
        }
        Ok(())
    }

    fn interpret_div_as_real_lit(&mut self, a: &Rc<Term>, b: &Rc<Term>) -> Option<Rc<Term>> {
        // If the term is a division between two positive integer constants, and their GCD is 1,
        // then it should be interpreted as a rational literal. The only exception to this is the
        // term '(/ 1 1)', which is still interpreted as a division term.

        let [a, b] = [a, b].map(|t| match t.as_ref() {
            Term::Const(Constant::Integer(i)) => Some(i),
            Term::Const(Constant::Real(r)) if self.interpret_ints_as_reals() && r.is_integer() => {
                Some(r.numer())
            }
            _ => None,
        });
        let [a, b] = [a?, b?];

        if *a > 0 && *b > 0 && !(*a == 1 && *b == 1) && a.clone().gcd(b) == 1 {
            Some(self.pool.add(Term::new_real(Rational::from((a, b)))))
        } else {
            None
        }
    }

    /// Type checks the regular arguments and operator arguments of an indexed operation term.
    ///
    /// Returns `None` if the caller should build the default `Term::ParamOp { .. }`, or `Some` term
    /// if the operator has special term construction.
    fn type_check_indexed_op(
        &mut self,
        op: ParamOperator,
        op_args: &[Rc<Term>],
        args: &[Rc<Term>],
    ) -> Result<Option<Rc<Term>>, ParserError> {
        let sorts: Vec<_> = args.iter().map(|t| self.pool.sort(t)).collect();
        let op_sorts: Vec<_> = op_args.iter().map(|t| self.pool.sort(t)).collect();

        match &op {
            ParamOperator::BvConst => {
                assert_num_args(op_args, 2)?;
                assert_num_args(args, 0)?;
                if let Some(arg) = op_args.iter().find(|a| a.as_integer().is_none()) {
                    return Err(ParserError::ExpectedIntegerConstant(arg.clone()));
                }
                assert_indexed_op_args_value(&op_args[..1], 0..)?;
                assert_indexed_op_args_value(&op_args[1..], 1..)?;
                let value = op_args[0].as_integer().unwrap();
                let width = op_args[1].as_integer().unwrap().to_usize().unwrap();
                return Ok(Some(
                    self.pool.add(Term::Const(Constant::BitVec(value, width))),
                ));
            }
            ParamOperator::BvExtract => {
                // ((_ extract i j) (_ BitVec m) (_ BitVec n))
                // where
                // - i, j, m, n are numerals
                // - m > i ≥ j ≥ 0,
                // - n = i - j + 1
                assert_num_args(op_args, 2)?;
                assert_num_args(args, 1)?;
                if !sorts[0].is_bitvec() {
                    return Err(ParserError::ExpectedBvSort(sorts[0].clone()));
                }

                self.check_sort_all(&[Sort::Int], &op_sorts)?;

                assert_indexed_op_args_value(op_args, 0..)?;
                let i = op_args[0].as_integer().as_ref().and_then(Integer::to_usize);
                let j = op_args[1].as_integer().as_ref().and_then(Integer::to_usize);

                // j >= 0 is ensured by the parser. We need to ensure that m > i && i >= j, if they
                // are all statically known
                if let (Some(i), Some(j), Sort::BitVec(m)) = (i, j, sorts[0].as_ref())
                    && !(*m > i && i >= j)
                {
                    return Err(ParserError::InvalidExtractArgs(i, j, *m));
                }
            }
            ParamOperator::IntToBv => {
                assert_num_args(op_args, 1)?;
                assert_num_args(args, 1)?;
                self.check_sort_eq(&Sort::Int, &op_sorts[0])?;
                self.check_sort_eq(&Sort::Int, &sorts[0])?;
            }
            ParamOperator::BvBitOf
            | ParamOperator::BvIntOf
            | ParamOperator::ZeroExtend
            | ParamOperator::SignExtend
            | ParamOperator::RotateLeft
            | ParamOperator::RotateRight
            | ParamOperator::Repeat => {
                assert_num_args(op_args, 1)?;
                assert_num_args(args, 1)?;
                self.check_sort_eq(&Sort::Int, &op_sorts[0])?;
                if !sorts[0].is_bitvec() {
                    return Err(ParserError::ExpectedBvSort(sorts[0].clone()));
                }
                assert_indexed_op_args_value(op_args, 0..)?;
            }
            ParamOperator::RePower => {
                assert_num_args(op_args, 1)?;
                assert_num_args(args, 1)?;
                self.check_sort_eq(&Sort::Int, &op_sorts[0])?;
                self.check_sort_eq(&Sort::RegLan, &sorts[0])?;
                assert_indexed_op_args_value(op_args, 0..)?;
            }
            ParamOperator::ReLoop => {
                assert_num_args(op_args, 2)?;
                assert_num_args(args, 1)?;
                self.check_sort_all(&[Sort::Int], &op_sorts)?;
                self.check_sort_eq(&Sort::RegLan, &sorts[0])?;
                assert_indexed_op_args_value(op_args, 0..)?;
            }
            ParamOperator::Tester => {} // TODO
            ParamOperator::TupleSelect => {
                assert_num_args(op_args, 1)?;
                assert_num_args(args, 1)?;
                if op_args[0]
                    .as_integer()
                    .as_ref()
                    .and_then(Integer::to_usize)
                    .is_none()
                {
                    return Err(ParserError::ExpectedIntegerConstant(op_args[0].clone()));
                }
                let Sort::Tuple(elems) = sorts[0].as_ref() else {
                    return Err(ParserError::ExpectedTupleSort(sorts[0].clone()));
                };
                assert_indexed_op_args_value(op_args, ..elems.len())?;
            }
        }
        Ok(None)
    }
}
