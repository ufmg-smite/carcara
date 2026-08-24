//! Some useful helper macros.

/// A variant of `match_term` that returns a `Result<_, CheckerError>` instead of an `Option`.
///
/// The error returned by this macro is always `CheckerError::TermOfWrongForm`.
#[macro_export]
macro_rules! match_term_err {
    ($pat:tt = $var:expr) => {{
        let var = $var;
        carcara_macros::match_term!($pat = var).ok_or_else(|| {
            // Note: `stringify!` can't fully preserve whitespace when turning a token
            // tree into a string — e.g. `(not (and ...))` becomes `(not(and ...))`.
            $crate::checker::error::CheckerError::TermOfWrongForm(stringify!($pat), var.clone())
        })
    }};
}

/// A macro to help build new terms.
///
/// This macro takes two arguments: the `TermPool` with which to build the term, and an s-expression
/// representing the term to be built. Subterms in that s-expression that are surrounded by `{}` are
/// evaluated as expressions, and they should have type `Rc<Term>`.
///
/// # Examples
///
/// Building the term `(and true (not false))`:
/// ```text
/// # use carcara::{ast::*, build_term, match_term};
/// let mut pool = PrimitivePool::new();
/// let t = build_term!(pool, (and {pool.bool_true()} (not {pool.bool_false()})));
/// assert!(match_term!((and true (not false)) = t).is_some());
/// ```
#[macro_export]
macro_rules! build_term {
    ($pool:expr, true) => { $pool.bool_true() };
    ($pool:expr, false) => { $pool.bool_false() };
    ($pool:expr, (let $name:ident $sort:ident)) => {{
        let sort = $pool.add($crate::ast::Term::Sort($crate::ast::Sort::$sort));
        $pool.add($crate::ast::Term::new_var(stringify!($name), sort))
    }};
    ($pool:expr, (choice (($z:literal $sort:ident)) $arg:tt)) => {{
        let sort = $pool.add($crate::ast::Term::Sort($crate::ast::Sort::$sort));
        let bindings = $crate::ast::BindingList(vec![($z.into(), sort)]);
        let body = build_term!($pool, $arg);
        $pool.add(Term::Binder(Binder::Choice, bindings, body))
    }};
    ($pool:expr, $int:literal) => { $pool.add($crate::ast::Term::Const($crate::ast::Constant::Integer($int.into()))) };
    ($pool:expr, (const $name:ident)) => { $pool.add($crate::ast::Term::Const($crate::ast::Constant::Integer($name.clone()))) };
    ($pool:expr, {$terminal:expr}) => { $terminal };
    ($pool:expr, ((_ $indexed_op:tt $($op_args:tt)+) $($args:tt)+)) => {{
        let term = $crate::ast::Term::ParamOp {
            op: carcara_macros::get_param_op_variant!($indexed_op),
            op_args: vec![ $(build_term!($pool, $op_args)),+ ],
            args: vec![ $(build_term!($pool, $args)),+ ],
        };
        $pool.add(term)
    }};
    ($pool:expr, ($op:tt [$arg:expr])) => {{
        let term = $crate::ast::Term::Op(
            carcara_macros::get_op_variant!($op),
            $arg,
        );
        $pool.add(term)
    }};
    ($pool:expr, ($op:tt $($args:tt)+)) => {{
        let term = $crate::ast::Term::Op(
            carcara_macros::get_op_variant!($op),
            vec![ $(build_term!($pool, $args)),+ ],
        );
        $pool.add(term)
    }};
}

/// Implements `FromStr` and `Display` for an enum, given a mapping from each variant to a string
/// literal.
///
/// This macros only supports enums that don't hold any data in any of their variants. The error
/// type for the implementation of `FromStr` will be `()`.
///
/// # Examples
///
// Since this macro is not exported, and since doctests are run as if they were a different crate,
// it's impossible to test this macro. To avoid test errors, we interpret this block as text. This
// is not a perfect solution, since we lose syntax highlighting.
// See https://github.com/rust-lang/rust/issues/63193
/// ```text
/// #[derive(Debug, PartialEq)]
/// enum Foo {
///     A,
///     B,
///     C,
/// }
///
/// impl_str_conversion_traits!(Foo {
///     A: "a",
///     B: "b",
///     C: "c",
/// });
///
/// fn main() {
///     assert_eq!(Foo::from_str("a"), Ok(Foo::A));
///     assert_eq!(format!("{}", Foo::B), "b");
///     assert_eq!(Foo::from_str("d"), Err(()));
/// }
/// ```
macro_rules! impl_str_conversion_traits {
    ($enum_name:ident { $($variant:ident: $str:literal),* $(,)? }) => {
        impl std::str::FromStr for $enum_name {
            type Err = ();

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                match s {
                    $($str => Ok($enum_name::$variant),)*
                    _ => Err(()),
                }
            }
        }

        impl std::fmt::Display for $enum_name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                let s = match self {
                    $($enum_name::$variant => $str,)*
                };
                write!(f, "{}", s)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{pool::PrimitivePool, *};
    use crate::parser::tests::{parse_term, parse_terms};
    use carcara_macros::match_term;

    #[test]
    fn test_match_term() {
        let mut p = PrimitivePool::new();
        let [one, two, five] = [1, 2, 5].map(|n| p.add(Term::new_int(n)));

        let term = parse_term(&mut p, "(= (= (not false) (= true false)) (not true))");
        let (a, b, c, d) = match_term!((= (= (not a) (= b c)) (not d)) = &term).unwrap();
        assert_eq!(a, &p.bool_false());
        assert_eq!(b, &p.bool_true());
        assert_eq!(c, &p.bool_false());
        assert_eq!(d, &p.bool_true());

        let term = parse_term(&mut p, "(ite (not true) (- 2 2) (* 1 5))");
        let (a, b, c) = match_term!((ite (not a) b c) = &term).unwrap();
        assert_eq!(a, &p.bool_true());
        assert_eq!(
            b,
            &p.add(Term::Op(Operator::Sub, vec![two.clone(), two.clone()])),
        );
        assert_eq!(c.as_ref(), &Term::Op(Operator::Mult, vec![one, five]));

        // Test the `...` pattern
        let term = parse_term(&mut p, "(not (and true false true))");
        match match_term!((not (and ...)) = &term) {
            Some([a, b, c]) => {
                assert_eq!(&p.bool_true(), a);
                assert_eq!(&p.bool_false(), b);
                assert_eq!(&p.bool_true(), c);
            }
            _ => panic!(),
        }
        let term = parse_term(&mut p, "(and (or false true) (= 2 2))");
        match match_term!((and (or ...) (= ...)) = &term) {
            Some(([a, b], [c, d])) => {
                assert_eq!(&p.bool_false(), a);
                assert_eq!(&p.bool_true(), b);
                assert_eq!(&two, c);
                assert_eq!(&two, d);
            }
            _ => panic!(),
        }

        let term = parse_term(&mut p, "((_ extract 3 1) (_ bv0 5))");
        let (i, j, b): (&Rc<Term>, &Rc<Term>, &Rc<Term>) =
            match_term!(((_ extract i j) b) = term).unwrap();
        assert_eq!(3, i.as_integer().unwrap());
        assert_eq!(1, j.as_integer().unwrap());
        assert_eq!(Term::new_bv(0, 5), **b);

        let term = parse_term(&mut p, "((_ @bit_of 2) (_ bv0 5))");
        let (i, b): (&Rc<Term>, &[Rc<Term>]) = match_term!(((_ bit_of i) ...) = term).unwrap();
        assert_eq!(2, i.as_integer().unwrap());
        assert_eq!(Term::new_bv(0, 5), *b[0]);

        let term = parse_term(&mut p, "((_ @int_of 2) (_ bv0 5))");
        let (i, b): (&Rc<Term>, &[Rc<Term>]) = match_term!(((_ int_of i) ...) = term).unwrap();
        assert_eq!(2, i.as_integer().unwrap());
        assert_eq!(Term::new_bv(0, 5), *b[0]);
    }

    #[test]
    fn test_match_term_repeated_names() {
        let mut p = PrimitivePool::new();
        let (true_, false_) = (p.bool_true(), p.bool_false());
        let not_true = p.add(Term::Op(Operator::Not, vec![true_]));
        let not_false = p.add(Term::Op(Operator::Not, vec![false_]));

        // A name used more than once only matches if all the terms bound to it are equal, and it
        // contributes a single element to the resulting tuple
        let term = parse_term(&mut p, "(= (not true) (not true))");
        let t: &Rc<Term> = match_term!((= x x) = &term).unwrap();
        assert_eq!(t, &not_true);

        let term = parse_term(&mut p, "(= (not true) (not false))");
        assert!(match_term!((= x x) = &term).is_none());

        // Distinct names still match distinct terms
        let (a, b) = match_term!((= x y) = &term).unwrap();
        assert_eq!(a, &not_true);
        assert_eq!(b, &not_false);

        // Repeated names in nested positions, mixed with distinct ones
        let term = parse_term(&mut p, "(= (= 1 2) (and (<= 1 2) (<= 2 1)))");
        let (t, u) = match_term!((= (= t u) (and (<= t u) (<= u t))) = &term).unwrap();
        assert_eq!(1, t.as_integer().unwrap());
        assert_eq!(2, u.as_integer().unwrap());

        let term = parse_term(&mut p, "(= (= 1 2) (and (<= 1 2) (<= 2 5)))");
        assert!(match_term!((= (= t u) (and (<= t u) (<= u t))) = &term).is_none());

        // '_' is a wildcard: distinct occurrences don't have to be equal, but they are still
        // captured
        let term = parse_term(&mut p, "(= 1 2)");
        let (a, b) = match_term!((= _ _) = &term).unwrap();
        assert_eq!(1, a.as_integer().unwrap());
        assert_eq!(2, b.as_integer().unwrap());

        // Repeated names inside a binder's body
        let term = parse_term(&mut p, "(forall ((x Int)) (= (not true) (not true)))");
        let (bindings, t): (&BindingList, &Rc<Term>) =
            match_term!((forall ... (= x x)) = &term).unwrap();
        assert_eq!(1, bindings.len());
        assert_eq!(t, &not_true);

        let term = parse_term(&mut p, "(forall ((x Int)) (= (not true) (not false)))");
        assert!(match_term!((forall ... (= x x)) = &term).is_none());
    }

    #[test]
    fn test_build_term() {
        let definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun p () Bool)
            (declare-fun q () Bool)
        ";
        let mut pool = PrimitivePool::new();
        let bool_sort = pool.add(Term::Sort(Sort::Bool));
        let int_sort = pool.add(Term::Sort(Sort::Int));

        let [one, two, three] = [1, 2, 3].map(|n| pool.add(Term::new_int(n)));
        let [a, b] = ["a", "b"].map(|s| pool.add(Term::new_var(s, int_sort.clone())));
        let [p, q] = ["p", "q"].map(|s| pool.add(Term::new_var(s, bool_sort.clone())));
        let zeros = pool.add(Term::new_bv(0, 6));

        let cases = [
            ("(= a b)", build_term!(pool, (= {a} {b}))),
            (
                "(= 1 2)",
                build_term!(pool, (= {one.clone()} {two.clone()})),
            ),
            ("(not true)", build_term!(pool, (not {pool.bool_true()}))),
            (
                "(or p false)",
                build_term!(pool, (or {p.clone()} {pool.bool_false()})),
            ),
            (
                "(and (=> p q) (ite p false (= 1 3)))",
                build_term!(pool, (and
                    (=> {p.clone()} {q.clone()})
                    (ite {p.clone()} {pool.bool_false()} (= {one.clone()} {three.clone()}))
                )),
            ),
            (
                "(distinct p q true)",
                build_term!(pool, (distinct {p} {q} {pool.bool_true()})),
            ),
            (
                "(or (not (= 2 3)) (= 1 1))",
                build_term!(pool, (or
                    (not (= {two} {three}))
                    (= {one.clone()} {one})
                )),
            ),
            (
                "((_ @bit_of 1) ((_ extract 3 2) #b000000))",
                build_term!(pool,
                    ((_ bit_of 1) ((_ extract 3 2) {zeros.clone()}))
                ),
            ),
            (
                "((_ @int_of 1) ((_ extract 3 2) #b000000))",
                build_term!(pool,
                    ((_ int_of 1) ((_ extract 3 2) {zeros.clone()}))
                ),
            ),
            ("(and true false)", build_term!(pool, (and true false))),
        ];

        for (s, got) in &cases {
            let [expected] = parse_terms(&mut pool, definitions, [s]);
            assert_eq!(&expected, got);
        }
    }
}
