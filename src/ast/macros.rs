/// A macro to help deconstruct operation terms. Since a term holds references to other terms in
/// `Vec`s and `Rc`s, pattern matching a complex term can be difficult and verbose. This macro
/// helps with that. The return type of this macro is an `Option` of a tree-like tuple. The
/// structure of the tree will depend on the pattern passed, and the leaf nodes will be `&Term`s. An
/// optional flag "RETURN_RCS" can be passed, in which case the leaf nodes will instead be
/// `&ByRefRc<Term>`s.
macro_rules! match_term {
    ($bind:ident = $var:expr) => { Some($var.as_ref()) };
    ($bind:ident = $var:expr, RETURN_RCS) => { Some($var) };
    (($op:tt $($args:tt)+) = $var:expr $(, $flag:ident)?) => {{
        if let Term::Op(match_term!(@GET_VARIANT $op), args) = &$var as &Term {
            match_term!(@ARGS ($($args)+) = args.as_slice() $(, $flag)?)
        } else {
            None
        }
    }};

    (@ARGS (...) = $var:expr $(, $flag:ident)?) => { Some($var) };
    (@ARGS ($arg:tt) = $var:expr $(, $flag:ident)?) => {
        match_term!(@ARGS_IDENT (arg1: $arg) = $var $(, $flag)?)
    };
    (@ARGS ($arg1:tt $arg2:tt) = $var:expr $(, $flag:ident)?) => {
        match_term!(@ARGS_IDENT (arg1: $arg1, arg2: $arg2) = $var $(, $flag)?)
    };
    (@ARGS ($arg1:tt $arg2:tt $arg3:tt) = $var:expr $(, $flag:ident)?) => {
        match_term!(@ARGS_IDENT (arg1: $arg1, arg2: $arg2, arg3: $arg3) = $var $(, $flag)?)
    };
    (@ARGS_IDENT ( $($name:ident : $arg:tt),* ) = $var:expr) => {
        if let [$($name),*] = $var {
            #[allow(unused_parens)]
            #[allow(clippy::manual_map)]
            match ($(match_term!($arg = $name)),*) {
                ($(Some($name)),*) => Some(($($name),*)),
                _ => None,
            }
        } else {
            None
        }
    };
    // `macro_rules!` doesn't allow nested repetition, so I can't do
    //   $(match_term!($arg = $name $(, $flag)?),*
    // Instead, I have to repeat this case, adding the optional flag manually
    (@ARGS_IDENT ( $($name:ident : $arg:tt),* ) = $var:expr, RETURN_RCS) => {
        if let [$($name),*] = $var {
            #[allow(unused_parens)]
            #[allow(clippy::manual_map)]
            match ($(match_term!($arg = $name, RETURN_RCS)),*) {
                ($(Some($name)),*) => Some(($($name),*)),
                _ => None,
            }
        } else {
            None
        }
    };
    (@GET_VARIANT not)      => { Operator::Not };
    (@GET_VARIANT =>)       => { Operator::Implies };
    (@GET_VARIANT and)      => { Operator::And };
    (@GET_VARIANT or)       => { Operator::Or };
    (@GET_VARIANT xor)      => { Operator::Xor };
    (@GET_VARIANT =)        => { Operator::Equals };
    (@GET_VARIANT distinct) => { Operator::Distinct };
    (@GET_VARIANT ite)      => { Operator::Ite };
    (@GET_VARIANT +)        => { Operator::Add };
    (@GET_VARIANT -)        => { Operator::Sub };
    (@GET_VARIANT *)        => { Operator::Mult };
    (@GET_VARIANT /)        => { Operator::Div };
    (@GET_VARIANT <)        => { Operator::LessThan };
    (@GET_VARIANT >)        => { Operator::GreaterThan };
    (@GET_VARIANT <=)       => { Operator::LessEq };
    (@GET_VARIANT >=)       => { Operator::GreaterEq };
}

/// A macro to help build new terms. Note that this macro will construct subterms by calling
/// `ByRefRc::new` and does not make use of hash consing.
macro_rules! build_term {
    ($pool:expr, {$terminal:expr}) => { $terminal };
    ($pool:expr, ($op:tt $($args:tt)+)) => {{
        let term = Term::Op(
            match_term!(@GET_VARIANT $op),
            vec![ $(build_term!($pool, $args)),+ ],
        );
        $pool.add_term(term)
    }};
}

/// Helper macro to construct `Terminal` terms.
macro_rules! terminal {
    (int $e:expr) => {
        Term::Terminal(Terminal::Integer($e.into()))
    };
    (real $num:literal / $denom:literal) => {
        Term::Terminal(Terminal::Real(num_rational::Ratio::new($num.into(), $denom.into())))
    };
    (real $e:expr) => {
        Term::Terminal(Terminal::Real($e))
    };
    (string $e:expr) => {
        Term::Terminal(Terminal::String($e.into()))
    };
    (var $e:expr ; $sort:ident) => {
        Term::Terminal(Terminal::Var(Identifier::Simple($e.into()), Term::$sort.clone().into()))
    };
    (var $e:expr ; $sort:expr) => {
        Term::Terminal(Terminal::Var(Identifier::Simple($e.into()), $sort))
    };
    (bool true) => { terminal!(var "true"; BOOL_SORT) };
    (bool false) => { terminal!(var "false"; BOOL_SORT) };
}

/// Implements `FromStr` and `Debug` for an enum, given a string representation for each variant.
macro_rules! impl_str_conversion_traits {
    ($enum_name:ident { $($variant:ident: $str:literal),* $(,)? }) => {
        impl FromStr for $enum_name {
            type Err = ();

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                match s {
                    $($str => Ok($enum_name::$variant),)*
                    _ => Err(()),
                }
            }
        }

        impl Debug for $enum_name {
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
macro_rules! assert_deep_eq {
    ($($input:tt)*) => { assert!(DeepEq::eq( $($input)* )) };
}

#[cfg(test)]
mod tests {
    use crate::ast::*;
    use crate::parser::tests::{parse_term, parse_term_with_definitions};

    #[test]
    fn test_match_term() {
        let term = parse_term("(= (= (not false) (= true false)) (not true))");
        let ((a, (b, c)), d) = match_term!((= (= (not a) (= b c)) (not d)) = &term).unwrap();
        assert_deep_eq!(a, &terminal!(bool false));
        assert_deep_eq!(b, &terminal!(bool true));
        assert_deep_eq!(c, &terminal!(bool false));
        assert_deep_eq!(d, &terminal!(bool true));

        let term = parse_term("(ite (not true) (- 2 2) (* 1 5))");
        let (a, b, c) = match_term!((ite (not a) b c) = &term).unwrap();
        assert_deep_eq!(a, &terminal!(bool true));
        assert_deep_eq!(
            b,
            &Term::Op(
                Operator::Sub,
                vec![
                    ByRefRc::new(terminal!(int 2)),
                    ByRefRc::new(terminal!(int 2)),
                ],
            ),
        );
        assert_deep_eq!(
            c,
            &Term::Op(
                Operator::Mult,
                vec![
                    ByRefRc::new(terminal!(int 1)),
                    ByRefRc::new(terminal!(int 5)),
                ],
            ),
        );

        // Make sure that when "RETURN_RCS" flag is passed, the macro returns `&ByRefRc<Term>`
        // instead of `&Term`
        let term = parse_term("(= (not false) (=> true false) (or false false))");
        let _: (
            &ByRefRc<_>,
            (&ByRefRc<_>, &ByRefRc<_>),
            (&ByRefRc<_>, &ByRefRc<_>),
        ) = match_term!((= (not a) (=> b c) (or d e)) = &term, RETURN_RCS).unwrap();

        // Test the "..." pattern
        let term = parse_term("(not (and true false true))");
        match match_term!((not (and ...)) = &term) {
            Some([a, b, c]) => {
                assert_deep_eq!(&terminal!(bool true), a);
                assert_deep_eq!(&terminal!(bool false), b);
                assert_deep_eq!(&terminal!(bool true), c);
            }
            _ => panic!(),
        }
        let term = parse_term("(and (or false true) (= 2 2))");
        match match_term!((and (or ...) (= ...)) = &term) {
            Some(([a, b], [c, d])) => {
                assert_deep_eq!(&terminal!(bool false), a);
                assert_deep_eq!(&terminal!(bool true), b);
                assert_deep_eq!(&terminal!(int 2), c);
                assert_deep_eq!(&terminal!(int 2), d);
            }
            _ => panic!(),
        }
    }

    #[test]
    fn test_build_term() {
        let definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun p () Bool)
            (declare-fun q () Bool)
        ";
        let mut pool = TermPool::new();

        let (one, two, three) = (
            pool.add_term(terminal!(int 1)),
            pool.add_term(terminal!(int 2)),
            pool.add_term(terminal!(int 3)),
        );
        let (a, b) = (
            pool.add_term(terminal!(var "a"; INT_SORT)),
            pool.add_term(terminal!(var "b"; INT_SORT)),
        );
        let (p, q) = (
            pool.add_term(terminal!(var "p"; BOOL_SORT)),
            pool.add_term(terminal!(var "q"; BOOL_SORT)),
        );
        let (r#true, r#false) = (pool.bool_true(), pool.bool_false());

        let cases = [
            ("(= a b)", build_term!(pool, (= {a} {b}))),
            (
                "(= 1 2)",
                build_term!(pool, (= {one.clone()} {two.clone()})),
            ),
            ("(not true)", build_term!(pool, (not {r#true.clone()}))),
            (
                "(or p false)",
                build_term!(pool, (or {p.clone()} {r#false.clone()})),
            ),
            (
                "(and (=> p q) (ite p false (= 1 3)))",
                build_term!(pool, (and
                    (=> {p.clone()} {q.clone()})
                    (ite {p.clone()} {r#false} (= {one.clone()} {three.clone()}))
                )),
            ),
            (
                "(distinct p q true)",
                build_term!(pool, (distinct {p} {q} {r#true})),
            ),
            (
                "(or (not (= 2 3)) (= 1 1))",
                build_term!(pool, (or
                    (not (= {two} {three}))
                    (= {one.clone()} {one})
                )),
            ),
        ];

        for (s, got) in &cases {
            let expected = parse_term_with_definitions(definitions, s);
            assert_deep_eq!(&expected, got)
        }
    }
}
