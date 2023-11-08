//! In addition to the parser tests, this module contains some parsing functions that can be
//! useful in tests, and are intended to be used in other modules.
#![cfg(test)]

use super::*;
use crate::ast::pool::PrimitivePool;

const ERROR_MESSAGE: &str = "parser error during test";

const TEST_CONFIG: Config = Config {
    // Some tests need function definitions to be applied
    apply_function_defs: true,
    expand_lets: false,
    allow_int_real_subtyping: false,
};

pub fn parse_terms<const N: usize>(
    pool: &mut PrimitivePool,
    definitions: &str,
    terms: [&str; N],
) -> [Rc<Term>; N] {
    let mut parser = Parser::new(pool, TEST_CONFIG, definitions.as_bytes()).expect(ERROR_MESSAGE);
    parser.parse_problem().expect(ERROR_MESSAGE);

    terms.map(|s| {
        parser.reset(s.as_bytes()).expect(ERROR_MESSAGE);
        parser.parse_term().expect(ERROR_MESSAGE)
    })
}

pub fn parse_term(pool: &mut PrimitivePool, input: &str) -> Rc<Term> {
    Parser::new(pool, TEST_CONFIG, input.as_bytes())
        .and_then(|mut parser| parser.parse_term())
        .expect(ERROR_MESSAGE)
}

/// Tries to parse a term from a `&str`, expecting it to fail. Returns the error encountered, or
/// panics if no error is encountered.
pub fn parse_term_err(input: &str) -> Error {
    let mut pool = PrimitivePool::new();
    Parser::new(&mut pool, TEST_CONFIG, input.as_bytes())
        .and_then(|mut p| p.parse_term())
        .expect_err("expected error")
}

/// Parses a proof from a `&str`. Panics if any error is encountered.
pub fn parse_proof(pool: &mut PrimitivePool, input: &str) -> Proof {
    let commands = Parser::new(pool, TEST_CONFIG, input.as_bytes())
        .expect(ERROR_MESSAGE)
        .parse_proof()
        .expect(ERROR_MESSAGE);
    Proof { premises: IndexSet::new(), commands }
}

fn run_parser_tests(pool: &mut PrimitivePool, cases: &[(&str, Rc<Term>)]) {
    for (case, expected) in cases {
        let got = parse_term(pool, case);
        assert_eq!(expected, &got);
    }
}

#[test]
fn test_hash_consing() {
    use indexmap::IndexSet;

    let mut pool = PrimitivePool::new();
    let input = "(-
        (-
            (+ 1 2)
            (* (+ 1 2) (+ 1 2))
        )
        (* 2 2)
    )";
    let mut parser = Parser::new(&mut pool, Config::new(), input.as_bytes()).unwrap();
    parser.parse_term().unwrap();

    // We expect this input to result in 7 unique terms after parsing:
    //   1
    //   2
    //   (+ 1 2)
    //   (* (+ 1 2) (+ 1 2))
    //   (- (+ 1 2) (* ...))
    //   (* 2 2)
    //   (- (- ...) (* 2 2))
    let expected = vec![
        // The `Bool` sort and the boolean constants `true` and `false` are always added to the
        // terms map
        "Bool",
        "true",
        "false",
        "1",
        "Int",
        "2",
        "(+ 1 2)",
        "(* (+ 1 2) (+ 1 2))",
        "(- (+ 1 2) (* (+ 1 2) (+ 1 2)))",
        "(* 2 2)",
        "(- (- (+ 1 2) (* (+ 1 2) (+ 1 2))) (* 2 2))",
    ]
    .into_iter()
    .collect::<IndexSet<&str>>();

    let pool_terms = pool.storage.into_vec();
    assert_eq!(pool_terms.len(), expected.len());
    for got in pool_terms {
        let formatted: &str = &format!("{:#}", got);
        assert!(expected.contains(formatted), "{}", formatted);
    }
}

#[test]
fn test_constant_terms() {
    let mut p = PrimitivePool::new();
    assert_eq!(Term::new_int(42), *parse_term(&mut p, "42"));
    assert_eq!(Term::new_real((3, 2)), *parse_term(&mut p, "1.5"));
    assert_eq!(Term::new_string("foo"), *parse_term(&mut p, "\"foo\""));
}

#[test]
fn test_arithmetic_ops() {
    let mut p = PrimitivePool::new();
    let [one, two, three, five, seven] = [1, 2, 3, 5, 7].map(|n| p.add(Term::new_int(n)));
    let cases = [
        (
            "(+ 2 3)",
            p.add(Term::Op(Operator::Add, vec![two.clone(), three.clone()])),
        ),
        (
            "(* 2 3 5 7)",
            p.add(Term::Op(
                Operator::Mult,
                vec![two.clone(), three, five.clone(), seven],
            )),
        ),
        ("(- 5)", p.add(Term::Op(Operator::Sub, vec![five]))),
        ("(- (+ 1 1) 2)", {
            let one_plus_one = p.add(Term::Op(Operator::Add, vec![one.clone(), one]));
            p.add(Term::Op(Operator::Sub, vec![one_plus_one, two]))
        }),
    ];
    run_parser_tests(&mut p, &cases);

    assert!(matches!(
        parse_term_err("(+ (- 1 2) (* 3.0 4.2))"),
        Error::Parser(ParserError::SortError(_), _),
    ));
}

#[test]
fn test_logic_ops() {
    let mut p = PrimitivePool::new();
    let [zero, one, two, three, four] = [0, 1, 2, 3, 4].map(|n| p.add(Term::new_int(n)));
    let cases = [
        (
            "(and true false)",
            p.add(Term::Op(Operator::And, vec![p.bool_true(), p.bool_false()])),
        ),
        (
            "(or true true false)",
            p.add(Term::Op(
                Operator::Or,
                vec![p.bool_true(), p.bool_true(), p.bool_false()],
            )),
        ),
        ("(or true (and false false))", {
            let false_and_false = p.add(Term::Op(
                Operator::And,
                vec![p.bool_false(), p.bool_false()],
            ));
            p.add(Term::Op(Operator::Or, vec![p.bool_true(), false_and_false]))
        }),
        (
            "(xor true false false)",
            p.add(Term::Op(
                Operator::Xor,
                vec![p.bool_true(), p.bool_false(), p.bool_false()],
            )),
        ),
        (
            "(= 2 3)",
            p.add(Term::Op(Operator::Equals, vec![two.clone(), three])),
        ),
        (
            "(not false)",
            p.add(Term::Op(Operator::Not, vec![p.bool_false()])),
        ),
        (
            "(distinct 4 2)",
            p.add(Term::Op(Operator::Distinct, vec![four, two])),
        ),
        ("(=> (= 0 1) true false)", {
            let zero_equals_one = p.add(Term::Op(Operator::Equals, vec![zero, one]));
            p.add(Term::Op(
                Operator::Implies,
                vec![zero_equals_one, p.bool_true(), p.bool_false()],
            ))
        }),
    ];
    run_parser_tests(&mut p, &cases);

    assert!(matches!(
        parse_term_err("(or true 1.2)"),
        Error::Parser(ParserError::SortError(_), _),
    ));
    assert!(matches!(
        parse_term_err("(= 10 10.0)"),
        Error::Parser(ParserError::SortError(_), _),
    ));
    assert!(matches!(
        parse_term_err("(not 1 2 3)"),
        Error::Parser(ParserError::WrongNumberOfArgs(_, 3), _),
    ));
    assert!(matches!(
        parse_term_err("(distinct 2 1.0)"),
        Error::Parser(ParserError::SortError(_), _),
    ));
    assert!(matches!(
        parse_term_err("(distinct 0)"),
        Error::Parser(ParserError::WrongNumberOfArgs(_, 1), _),
    ));
    assert!(matches!(
        parse_term_err("(=> true 0)"),
        Error::Parser(ParserError::SortError(_), _),
    ));
}

#[test]
fn test_ite() {
    let mut p = PrimitivePool::new();
    let [one, two, three] = [1, 2, 3].map(|n| p.add(Term::new_int(n)));
    let cases = [
        (
            "(ite true 2 3)",
            p.add(Term::Op(
                Operator::Ite,
                vec![p.bool_true(), two.clone(), three],
            )),
        ),
        ("(ite (not true) 2 (ite false 2 1))", {
            let not_true = p.add(Term::Op(Operator::Not, vec![p.bool_true()]));
            let ite = p.add(Term::Op(
                Operator::Ite,
                vec![p.bool_false(), two.clone(), one],
            ));
            p.add(Term::Op(Operator::Ite, vec![not_true, two, ite]))
        }),
    ];
    run_parser_tests(&mut p, &cases);

    assert!(matches!(
        parse_term_err("(ite true 0)"),
        Error::Parser(ParserError::WrongNumberOfArgs(_, 2), _),
    ));
    assert!(matches!(
        parse_term_err("(ite 0 1 2)"),
        Error::Parser(ParserError::SortError(_), _),
    ));
    assert!(matches!(
        parse_term_err("(ite false 10 10.0)"),
        Error::Parser(ParserError::SortError(_), _),
    ));
}

#[test]
fn test_quantifiers() {
    let mut p = PrimitivePool::new();
    let bool_sort = p.add(Term::Sort(Sort::Bool));
    let real_sort = p.add(Term::Sort(Sort::Real));
    let cases = [
        ("(exists ((p Bool)) p)", {
            let inner = p.add(Term::new_var("p", bool_sort.clone()));
            p.add(Term::Quant(
                Quantifier::Exists,
                BindingList(vec![("p".into(), bool_sort)]),
                inner,
            ))
        }),
        ("(forall ((x Real) (y Real)) (= (+ x y) 0.0))", {
            let [x, y] = ["x", "y"].map(|s| p.add(Term::new_var(s, real_sort.clone())));
            let x_plus_y = p.add(Term::Op(Operator::Add, vec![x, y]));
            let zero = p.add(Term::new_real(0));
            let inner = p.add(Term::Op(Operator::Equals, vec![x_plus_y, zero]));
            p.add(Term::Quant(
                Quantifier::Forall,
                BindingList(vec![
                    ("x".into(), real_sort.clone()),
                    ("y".into(), real_sort),
                ]),
                inner,
            ))
        }),
    ];
    run_parser_tests(&mut p, &cases);
    assert!(matches!(
        parse_term_err("(exists () true)"),
        Error::Parser(ParserError::EmptySequence, _),
    ));
    assert!(matches!(
        parse_term_err("(forall ((x Int)) (+ x x)"),
        Error::Parser(ParserError::SortError(_), _),
    ));
}

#[test]
fn test_choice_terms() {
    let mut p = PrimitivePool::new();
    let bool_sort = p.add(Term::Sort(Sort::Bool));
    let int_sort = p.add(Term::Sort(Sort::Int));
    let cases = [
        ("(choice ((p Bool)) p)", {
            let inner = p.add(Term::new_var("p", bool_sort.clone()));
            p.add(Term::Choice(("p".into(), bool_sort), inner))
        }),
        ("(choice ((x Int)) (= x 0))", {
            let x = p.add(Term::new_var("x", int_sort.clone()));
            let zero = p.add(Term::new_int(0));
            let inner = p.add(Term::Op(Operator::Equals, vec![x, zero]));
            p.add(Term::Choice(("x".into(), int_sort), inner))
        }),
    ];
    run_parser_tests(&mut p, &cases);
    assert!(matches!(
        parse_term_err("(choice () false)"),
        Error::Parser(ParserError::UnexpectedToken(_), _),
    ));
    assert!(matches!(
        parse_term_err("(choice ((x Int) (y Int)) (= x y))"),
        Error::Parser(ParserError::UnexpectedToken(_), _),
    ));
}

#[test]
fn test_let_terms() {
    let mut p = PrimitivePool::new();
    let int_sort = p.add(Term::Sort(Sort::Int));
    let bool_sort = p.add(Term::Sort(Sort::Bool));
    let cases = [
        ("(let ((p false)) p)", {
            let inner = p.add(Term::new_var("p", bool_sort));
            p.add(Term::Let(
                BindingList(vec![("p".into(), p.bool_false())]),
                inner,
            ))
        }),
        ("(let ((x 1) (y 2)) (+ x y))", {
            let [one, two] = [1, 2].map(|n| p.add(Term::new_int(n)));
            let [x, y] = ["x", "y"].map(|s| p.add(Term::new_var(s, int_sort.clone())));
            let inner = p.add(Term::Op(Operator::Add, vec![x, y]));
            p.add(Term::Let(
                BindingList(vec![("x".into(), one), ("y".into(), two)]),
                inner,
            ))
        }),
    ];
    run_parser_tests(&mut p, &cases);
    assert!(matches!(
        parse_term_err("(let () 0)"),
        Error::Parser(ParserError::EmptySequence, _),
    ));
}

#[test]
fn test_lambda_terms() {
    let mut p = PrimitivePool::new();
    let int_sort = p.add(Term::Sort(Sort::Int));
    let cases = [
        ("(lambda ((x Int)) x)", {
            let x = p.add(Term::new_var("x", int_sort.clone()));
            p.add(Term::Lambda(
                BindingList(vec![("x".into(), int_sort.clone())]),
                x,
            ))
        }),
        ("(lambda ((x Int) (y Int)) (+ x y))", {
            let [x, y] = ["x", "y"].map(|s| p.add(Term::new_var(s, int_sort.clone())));
            let inner = p.add(Term::Op(Operator::Add, vec![x, y]));
            p.add(Term::Lambda(
                BindingList(vec![("x".into(), int_sort.clone()), ("y".into(), int_sort)]),
                inner,
            ))
        }),
    ];
    run_parser_tests(&mut p, &cases);
    assert!(matches!(
        parse_term_err("(lambda () false)"),
        Error::Parser(ParserError::EmptySequence, _),
    ));
    assert!(matches!(
        parse_term_err("((lambda ((x Int)) (+ x 1)) false)"),
        Error::Parser(ParserError::SortError(_), _),
    ));
}

#[test]
fn test_annotated_terms() {
    let mut p = PrimitivePool::new();
    let [zero, two, three] = [0, 2, 3].map(|n| p.add(Term::new_int(n)));
    let cases = [
        ("(! 0 :named foo)", zero.clone()),
        ("(! (! 0 :named foo) :named bar)", zero.clone()),
        ("(! 0 :named foo :named bar)", zero.clone()),
        ("(! (! 0 :pattern ((+ 1 0) 3)) :named bar)", zero.clone()),
        ("(ite (! true :named baz) 2 3)", {
            p.add(Term::Op(Operator::Ite, vec![p.bool_true(), two, three]))
        }),
        ("(! 0 :unknown foo)", zero.clone()),
        ("(! 0 :unknown (list of tokens) :named foo)", zero.clone()),
        ("(! 0 :no :arguments)", zero),
    ];
    run_parser_tests(&mut p, &cases);
    assert!(matches!(
        parse_term_err("(! true)"),
        Error::Parser(ParserError::EmptySequence, _),
    ));
    assert!(matches!(
        parse_term_err("(! true not_a_keyword)"),
        Error::Parser(ParserError::UnexpectedToken(_), _),
    ));
    assert!(matches!(
        parse_term_err("(! true :named 1 2 3)"),
        Error::Parser(ParserError::UnexpectedToken(_), _),
    ));
}

#[test]
fn test_declare_fun() {
    let mut p = PrimitivePool::new();

    parse_terms(
        &mut p,
        "(declare-fun f (Bool Int Real) Real)",
        ["(f false 42 3.14159)"],
    );
    parse_terms(
        &mut p,
        "(declare-fun y () Real)
        (declare-fun f (Real) Int)
        (declare-fun g (Int Int) Bool)",
        ["(g (f y) 0)"],
    );

    let [got] = parse_terms(&mut p, "(declare-fun x () Real)", ["x"]);
    let real_sort = p.add(Term::Sort(Sort::Real));
    assert_eq!(p.add(Term::new_var("x", real_sort)), got);
}

#[test]
fn test_declare_sort() {
    let mut p = PrimitivePool::new();

    parse_terms(
        &mut p,
        "(declare-sort T 0)
        (declare-sort U 0)
        (declare-sort Y 0)
        (declare-fun t () T)
        (declare-fun u () U)
        (declare-fun f (T U) Y)",
        ["(f t u)"],
    );

    let [got] = parse_terms(
        &mut p,
        "(declare-sort T 0)
        (declare-fun x () T)",
        ["x"],
    );
    let expected_sort = p.add(Term::Sort(Sort::Atom("T".to_owned(), Vec::new())));
    assert_eq!(p.add(Term::new_var("x", expected_sort)), got);
}

#[test]
fn test_define_fun() {
    let mut p = PrimitivePool::new();
    let [got] = parse_terms(
        &mut p,
        "(define-fun add ((a Int) (b Int)) Int (+ a b))",
        ["(add 2 3)"],
    );
    assert_eq!(parse_term(&mut p, "(+ 2 3)"), got);

    let [got] = parse_terms(&mut p, "(define-fun x () Int 2)", ["(+ x 3)"]);
    assert_eq!(parse_term(&mut p, "(+ 2 3)"), got);

    let [got] = parse_terms(
        &mut p,
        "(define-fun f ((x Int)) Int (+ x 1))
         (define-fun g ((a Int) (b Int)) Int (* (f a) (f b)))",
        ["(g 2 3)"],
    );
    let expected = parse_term(&mut p, "(* (+ 2 1) (+ 3 1))");
    assert_eq!(expected, got);
}

#[test]
fn test_assume() {
    let mut p = PrimitivePool::new();
    let input = "
        (assume h1 true)
        (assume h2 (or true false) :ignore \"extra\" :attributes)
    ";
    let proof = parse_proof(&mut p, input);
    assert_eq!(proof.commands.len(), 2);

    assert_eq!(
        &proof.commands[0],
        &ProofCommand::Assume {
            id: "h1".into(),
            term: p.bool_true(),
        }
    );

    assert_eq!(
        &proof.commands[1],
        &ProofCommand::Assume {
            id: "h2".into(),
            term: parse_term(&mut p, "(or true false)"),
        }
    );
}

#[test]
fn test_step() {
    let mut p = PrimitivePool::new();
    let input = "
        (step t1 (cl (= (+ 2 3) (- 1 2))) :rule rule-name)
        (step t2 (cl) :rule rule-name :premises (t1))
        (step t3 (cl) :rule rule-name :args (1 2.0 \"three\"))
        (step t4 (cl) :rule rule-name :args ((:= a 12) (:= b 3.14) (:= c (* 6 7))))
        (step t5 (cl) :rule rule-name :premises (t1 t2 t3) :args (42)
            :ignore_this :and_this (blah blah 0 1))
    ";
    let proof = parse_proof(&mut p, input);
    assert_eq!(proof.commands.len(), 5);

    assert_eq!(
        &proof.commands[0],
        &ProofCommand::Step(ProofStep {
            id: "t1".into(),
            clause: vec![parse_term(&mut p, "(= (+ 2 3) (- 1 2))")],
            rule: "rule-name".into(),
            premises: Vec::new(),
            args: Vec::new(),
            discharge: Vec::new(),
        })
    );

    assert_eq!(
        &proof.commands[1],
        &ProofCommand::Step(ProofStep {
            id: "t2".into(),
            clause: Vec::new(),
            rule: "rule-name".into(),
            premises: vec![(0, 0)],
            args: Vec::new(),
            discharge: Vec::new(),
        })
    );

    assert_eq!(
        &proof.commands[2],
        &ProofCommand::Step(ProofStep {
            id: "t3".into(),
            clause: Vec::new(),
            rule: "rule-name".into(),
            premises: Vec::new(),
            args: {
                vec![
                    Term::new_int(1),
                    Term::new_real(2),
                    Term::new_string("three"),
                ]
                .into_iter()
                .map(|term| ProofArg::Term(p.add(term)))
                .collect()
            },
            discharge: Vec::new(),
        })
    );

    assert_eq!(
        &proof.commands[3],
        &ProofCommand::Step(ProofStep {
            id: "t4".into(),
            clause: Vec::new(),
            rule: "rule-name".into(),
            premises: Vec::new(),
            args: {
                vec![
                    ProofArg::Assign("a".into(), p.add(Term::new_int(12))),
                    ProofArg::Assign("b".into(), p.add(Term::new_real((314, 100)))),
                    ProofArg::Assign("c".into(), parse_term(&mut p, "(* 6 7)")),
                ]
            },
            discharge: Vec::new(),
        })
    );

    assert_eq!(
        &proof.commands[4],
        &ProofCommand::Step(ProofStep {
            id: "t5".into(),
            clause: Vec::new(),
            rule: "rule-name".into(),
            premises: vec![(0, 0), (0, 1), (0, 2)],
            args: vec![ProofArg::Term(p.add(Term::new_int(42)))],
            discharge: Vec::new(),
        })
    );
}

#[test]
fn test_premises_in_subproofs() {
    let mut p = PrimitivePool::new();
    let input = "
        (assume h1 true)
        (assume h2 true)
        (anchor :step t3)
        (step t3.t1 (cl) :rule rule-name :premises (h1 h2))
        (step t3.t2 (cl) :rule rule-name :premises (t3.t1 h1 h2))
        (step t3 (cl) :rule rule-name :premises (h1 t3.t1 h2 t3.t2))
    ";
    let proof = parse_proof(&mut p, input);
    assert_eq!(proof.commands.len(), 3);
    let subproof = match &proof.commands[2] {
        ProofCommand::Subproof(s) => &s.commands,
        _ => panic!(),
    };
    assert_eq!(subproof.len(), 3);
    assert_eq!(
        &subproof[0],
        &ProofCommand::Step(ProofStep {
            id: "t3.t1".into(),
            clause: Vec::new(),
            rule: "rule-name".into(),
            premises: vec![(0, 0), (0, 1)],
            args: Vec::new(),
            discharge: Vec::new(),
        })
    );
    assert_eq!(
        &subproof[1],
        &ProofCommand::Step(ProofStep {
            id: "t3.t2".into(),
            clause: Vec::new(),
            rule: "rule-name".into(),
            premises: vec![(1, 0), (0, 0), (0, 1)],
            args: Vec::new(),
            discharge: Vec::new(),
        })
    );
    assert_eq!(
        &subproof[2],
        &ProofCommand::Step(ProofStep {
            id: "t3".into(),
            clause: Vec::new(),
            rule: "rule-name".into(),
            premises: vec![(0, 0), (1, 0), (0, 1), (1, 1)],
            args: Vec::new(),
            discharge: Vec::new(),
        })
    );
}
