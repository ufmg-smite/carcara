/// A macro to help deconstruct operation terms. Since a term holds references to other terms in
/// `Vec`s and `Rc`s, pattern matching a complex term can be difficult and verbose. This macro
/// helps with that. The return type of this macro is an `Option` of a tree-like tuple. The
/// structure of the tree will depend on the pattern passed, and the leaf nodes will be
/// `&Rc<Term>`s.
macro_rules! match_term {
    (true = $var:expr $(, $flag:ident)?) => {
        if $var.is_bool_true() { Some(()) } else { None }
    };
    (false = $var:expr $(, $flag:ident)?) => {
        if $var.is_bool_false() { Some(()) } else { None }
    };
    ((forall ...) = $var:expr) => {
        if let $crate::ast::Term::Quant($crate::ast::Quantifier::Forall, bindings, inner) =
            &$var as &$crate::ast::Term
        {
            Some((bindings, inner))
        } else {
            None
        }
    };
    ((exists ...) = $var:expr) => {
        if let $crate::ast::Term::Quant($crate::ast::Quantifier::Exists, bindings, inner) =
            &$var as &$crate::ast::Term
        {
            Some((bindings, inner))
        } else {
            None
        }
    };
    ($bind:ident = $var:expr) => { Some($var) };
    (($op:tt $($args:tt)+) = $var:expr) => {{
        if let $crate::ast::Term::Op(match_term!(@GET_VARIANT $op), args) =
            &$var as &$crate::ast::Term
        {
            match_term!(@ARGS ($($args)+) = args.as_slice())
        } else {
            None
        }
    }};

    (@ARGS (...) = $var:expr) => { Some($var) };
    (@ARGS ($arg:tt) = $var:expr) => {
        match_term!(@ARGS_IDENT (arg1: $arg) = $var)
    };
    (@ARGS ($arg1:tt $arg2:tt) = $var:expr) => {
        match_term!(@ARGS_IDENT (arg1: $arg1, arg2: $arg2) = $var)
    };
    (@ARGS ($arg1:tt $arg2:tt $arg3:tt) = $var:expr) => {
        match_term!(@ARGS_IDENT (arg1: $arg1, arg2: $arg2, arg3: $arg3) = $var)
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
    (@GET_VARIANT not)      => { $crate::ast::Operator::Not };
    (@GET_VARIANT =>)       => { $crate::ast::Operator::Implies };
    (@GET_VARIANT and)      => { $crate::ast::Operator::And };
    (@GET_VARIANT or)       => { $crate::ast::Operator::Or };
    (@GET_VARIANT xor)      => { $crate::ast::Operator::Xor };
    (@GET_VARIANT =)        => { $crate::ast::Operator::Equals };
    (@GET_VARIANT distinct) => { $crate::ast::Operator::Distinct };
    (@GET_VARIANT ite)      => { $crate::ast::Operator::Ite };
    (@GET_VARIANT +)        => { $crate::ast::Operator::Add };
    (@GET_VARIANT -)        => { $crate::ast::Operator::Sub };
    (@GET_VARIANT *)        => { $crate::ast::Operator::Mult };
    (@GET_VARIANT div)      => { $crate::ast::Operator::IntDiv };
    (@GET_VARIANT /)        => { $crate::ast::Operator::RealDiv };
    (@GET_VARIANT <)        => { $crate::ast::Operator::LessThan };
    (@GET_VARIANT >)        => { $crate::ast::Operator::GreaterThan };
    (@GET_VARIANT <=)       => { $crate::ast::Operator::LessEq };
    (@GET_VARIANT >=)       => { $crate::ast::Operator::GreaterEq };
}

/// A variant of `match_term` that returns a `Result<_, CheckerError>` instead of an `Option`. The
/// error returned is always `CheckerError::TermOfWrongForm`.
macro_rules! match_term_err {
    ($pat:tt = $var:expr) => {{
        let var = $var;
        match_term!($pat = var).ok_or_else(|| {
            // Note: Annoyingly, the `stringify!` macro can't fully keep whitespace when turning a
            // token tree into a string. It will add spaces when they are required for the tokens
            // to make sense, but remove any other whitespace. This means that, for instance, the
            // token tree `(not (and ...))` will be stringified to `(not(and ...))`. One way to
            // solve this would be to create a procedural macro that uses the tokens `span` to
            // infer how many characters there were between each token, and assume they were all
            // spaces
            $crate::checker::error::CheckerError::TermOfWrongForm(stringify!($pat), var.clone())
        })
    }};
}

/// A macro to help build new terms.
macro_rules! build_term {
    ($pool:expr, {$terminal:expr}) => { $terminal };
    ($pool:expr, ($op:tt $($args:tt)+)) => {{
        let term = $crate::ast::Term::Op(
            match_term!(@GET_VARIANT $op),
            vec![ $(build_term!($pool, $args)),+ ],
        );
        $pool.add_term(term)
    }};
}

/// Helper macro to construct `Terminal` terms.
macro_rules! terminal {
    (int $e:expr) => {
        $crate::ast::Term::Terminal($crate::ast::Terminal::Integer($e.into()))
    };
    (real $num:literal / $denom:literal) => {{
        let num: rug::Integer = $num.into();
        let denom: rug::Integer = $denom.into();
        $crate::ast::Term::Terminal($crate::ast::Terminal::Real((num, denom).into()))
    }};
    (real $e:expr) => {
        $crate::ast::Term::Terminal($crate::ast::Terminal::Real($e))
    };
    (string $e:expr) => {
        $crate::ast::Term::Terminal($crate::ast::Terminal::String($e.into()))
    };
    (var $e:expr ; $sort:ident) => {
        $crate::ast::Term::Terminal($crate::ast::Terminal::Var(
            $crate::ast::Identifier::Simple($e.into()),
            $crate::ast::Term::$sort.clone().into()
        ))
    };
    (var $e:expr ; $sort:expr) => {
        $crate::ast::Term::Terminal($crate::ast::Terminal::Var(
            $crate::ast::Identifier::Simple($e.into()),
            $sort
        ))
    };
    (bool true) => {
        terminal!(
            var "true";
            $crate::ast::Rc::new($crate::ast::Term::Sort($crate::ast::Sort::Bool))
        )
    };
    (bool false) => {
        terminal!(
            var "false";
            $crate::ast::Rc::new($crate::ast::Term::Sort($crate::ast::Sort::Bool))
        )
    };
}

/// Implements `FromStr` and `Debug` for an enum, given a string representation for each variant.
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
macro_rules! assert_deep_eq {
    ($($input:tt)*) => { assert!($crate::ast::deep_eq($($input)*)) };
}

#[cfg(test)]
macro_rules! assert_deep_eq_modulo_reordering {
    ($($input:tt)*) => { assert!($crate::ast::deep_eq_modulo_reordering($($input)*)) };
}

#[cfg(test)]
mod tests {
    use crate::ast::*;
    use crate::parser::tests::{parse_term, parse_terms};

    #[test]
    fn test_match_term() {
        let term = parse_term("(= (= (not false) (= true false)) (not true))");
        let ((a, (b, c)), d) = match_term!((= (= (not a) (= b c)) (not d)) = &term).unwrap();
        assert_deep_eq!(a.as_ref(), &terminal!(bool false));
        assert_deep_eq!(b.as_ref(), &terminal!(bool true));
        assert_deep_eq!(c.as_ref(), &terminal!(bool false));
        assert_deep_eq!(d.as_ref(), &terminal!(bool true));

        let term = parse_term("(ite (not true) (- 2 2) (* 1 5))");
        let (a, b, c) = match_term!((ite (not a) b c) = &term).unwrap();
        assert_deep_eq!(a.as_ref(), &terminal!(bool true));
        assert_deep_eq!(
            b.as_ref(),
            &Term::Op(
                Operator::Sub,
                vec![Rc::new(terminal!(int 2)), Rc::new(terminal!(int 2)),],
            ),
        );
        assert_deep_eq!(
            c.as_ref(),
            &Term::Op(
                Operator::Mult,
                vec![Rc::new(terminal!(int 1)), Rc::new(terminal!(int 5)),],
            ),
        );

        // Test the `...` pattern
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
            pool.add_term(terminal!(var "a"; Rc::new(Term::Sort(Sort::Int)))),
            pool.add_term(terminal!(var "b"; Rc::new(Term::Sort(Sort::Int)))),
        );
        let (p, q) = (
            pool.add_term(terminal!(var "p"; Rc::new(Term::Sort(Sort::Bool)))),
            pool.add_term(terminal!(var "q"; Rc::new(Term::Sort(Sort::Bool)))),
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
            let [expected] = parse_terms(definitions, [s]);
            assert_deep_eq!(&expected, got);
        }
    }
}
