#![cfg(test)]

use super::*;

const ERROR_MESSAGE: &str = "parser error during test";

pub fn parse_term(input: &str) -> Term {
    Parser::new(input.as_bytes())
        .and_then(|mut p| p.parse_term())
        .expect(ERROR_MESSAGE)
        .as_ref()
        .clone()
}

pub fn parse_term_err(input: &str) -> ParserError {
    Parser::new(input.as_bytes())
        .and_then(|mut p| p.parse_term())
        .expect_err("expected error")
}

/// Parses a series of definitions and declarations, and then parses a term and returns it.
pub fn parse_term_with_definitions(definitions: &str, term: &str) -> Term {
    let mut parser = Parser::new(definitions.as_bytes()).expect(ERROR_MESSAGE);
    parser.parse_problem().expect(ERROR_MESSAGE);

    // To keep the definitions and delcarations, we transfer the parser state to the new
    // parser.
    let mut new_parser = Parser::with_state(term.as_bytes(), parser.state).expect(ERROR_MESSAGE);
    new_parser
        .parse_term()
        .expect(ERROR_MESSAGE)
        .as_ref()
        .clone()
}

pub fn parse_proof(input: &str) -> Proof {
    let commands = Parser::new(input.as_bytes())
        .and_then(|mut p| p.parse_proof())
        .expect(ERROR_MESSAGE);
    Proof { premises: AHashSet::new(), commands }
}

fn run_parser_tests(cases: &[(&str, Term)]) {
    for (case, expected) in cases {
        let got = parse_term(case);
        assert!(
            DeepEq::eq(expected, &got),
            "test case failed: {:?} != {:?}",
            expected,
            got
        );
    }
}

#[test]
fn test_hash_consing() {
    use ahash::AHashSet;

    let input = "(-
        (-
            (+ 1 2)
            (/ (+ 1 2) (+ 1 2))
        )
        (* 2 2)
    )";
    let mut parser = Parser::new(input.as_bytes()).unwrap();
    parser.parse_term().unwrap();

    // We expect this input to result in 7 unique terms after parsing:
    //   1
    //   2
    //   (+ 1 2)
    //   (/ (+ 1 2) (+ 1 2))
    //   (- (+ 1 2) (/ ...))
    //   (* 2 2)
    //   (- (- ...) (* 2 2))
    let expected = vec![
        // The "Bool" sort and the boolean constants "true" and "false" are always added to the
        // terms map
        "Bool",
        "true",
        "false",
        "1",
        "2",
        "(+ 1 2)",
        "(/ (+ 1 2) (+ 1 2))",
        "(- (+ 1 2) (/ (+ 1 2) (+ 1 2)))",
        "(* 2 2)",
        "(- (- (+ 1 2) (/ (+ 1 2) (+ 1 2))) (* 2 2))",
    ]
    .into_iter()
    .collect::<AHashSet<&str>>();

    assert_eq!(parser.state.term_pool.terms.len(), expected.len());

    for got in parser.state.term_pool.terms.keys() {
        let formatted: &str = &format!("{:?}", got);
        assert!(expected.contains(formatted), "{:?}", formatted)
    }
}

#[test]
fn test_constant_terms() {
    assert_eq!(terminal!(int 42), parse_term("42"));
    assert_eq!(terminal!(real 3 / 2), parse_term("1.5"));
    assert_eq!(terminal!(string "foo"), parse_term("\"foo\""));
}

#[test]
fn test_arithmetic_ops() {
    run_parser_tests(&[
        (
            "(+ 2 3)",
            Term::Op(
                Operator::Add,
                vec![Rc::new(terminal!(int 2)), Rc::new(terminal!(int 3))],
            ),
        ),
        (
            "(* 2 3 5 7)",
            Term::Op(
                Operator::Mult,
                vec![
                    Rc::new(terminal!(int 2)),
                    Rc::new(terminal!(int 3)),
                    Rc::new(terminal!(int 5)),
                    Rc::new(terminal!(int 7)),
                ],
            ),
        ),
        (
            "(- 5)",
            Term::Op(Operator::Sub, vec![Rc::new(terminal!(int 5))]),
        ),
        (
            "(- (+ 1 1) 2)",
            Term::Op(
                Operator::Sub,
                vec![
                    Rc::new(Term::Op(
                        Operator::Add,
                        vec![Rc::new(terminal!(int 1)), Rc::new(terminal!(int 1))],
                    )),
                    Rc::new(terminal!(int 2)),
                ],
            ),
        ),
    ]);

    assert!(matches!(
        parse_term_err("(+ (- 1 2) (* 3.0 4.2))"),
        ParserError(ErrorKind::SortError(SortError::Expected { .. }), _),
    ));
}

#[test]
fn test_logic_ops() {
    run_parser_tests(&[
        (
            "(and true false)",
            Term::Op(
                Operator::And,
                vec![
                    Rc::new(terminal!(bool true)),
                    Rc::new(terminal!(bool false)),
                ],
            ),
        ),
        (
            "(or true true false)",
            Term::Op(
                Operator::Or,
                vec![
                    Rc::new(terminal!(bool true)),
                    Rc::new(terminal!(bool true)),
                    Rc::new(terminal!(bool false)),
                ],
            ),
        ),
        (
            "(and true)",
            Term::Op(Operator::And, vec![Rc::new(terminal!(bool true))]),
        ),
        (
            "(or true (and false false))",
            Term::Op(
                Operator::Or,
                vec![
                    Rc::new(terminal!(bool true)),
                    Rc::new(Term::Op(
                        Operator::And,
                        vec![
                            Rc::new(terminal!(bool false)),
                            Rc::new(terminal!(bool false)),
                        ],
                    )),
                ],
            ),
        ),
        (
            "(xor true false false)",
            Term::Op(
                Operator::Xor,
                vec![
                    Rc::new(terminal!(bool true)),
                    Rc::new(terminal!(bool false)),
                    Rc::new(terminal!(bool false)),
                ],
            ),
        ),
        (
            "(= 2 3)",
            Term::Op(
                Operator::Equals,
                vec![Rc::new(terminal!(int 2)), Rc::new(terminal!(int 3))],
            ),
        ),
        (
            "(not false)",
            Term::Op(Operator::Not, vec![Rc::new(terminal!(bool false))]),
        ),
        (
            "(distinct 4 2)",
            Term::Op(
                Operator::Distinct,
                vec![Rc::new(terminal!(int 4)), Rc::new(terminal!(int 2))],
            ),
        ),
        (
            "(=> (= 0 1) true false)",
            Term::Op(
                Operator::Implies,
                vec![
                    Rc::new(Term::Op(
                        Operator::Equals,
                        vec![Rc::new(terminal!(int 0)), Rc::new(terminal!(int 1))],
                    )),
                    Rc::new(terminal!(bool true)),
                    Rc::new(terminal!(bool false)),
                ],
            ),
        ),
    ]);

    assert!(matches!(
        parse_term_err("(or true 1.2)"),
        ParserError(
            ErrorKind::SortError(SortError::Expected {
                expected: Term::Sort(Sort::Bool),
                ..
            }),
            _
        ),
    ));
    assert!(matches!(
        parse_term_err("(= 10 10.0)"),
        ParserError(ErrorKind::SortError(SortError::Expected { .. }), _),
    ));
    assert!(matches!(
        parse_term_err("(not 1 2 3)"),
        ParserError(ErrorKind::WrongNumberOfArgs(1, 3), _),
    ));
    assert!(matches!(
        parse_term_err("(distinct 2 1.0)"),
        ParserError(ErrorKind::SortError(SortError::Expected { .. }), _),
    ));
    assert!(matches!(
        parse_term_err("(distinct 0)"),
        ParserError(ErrorKind::WrongNumberOfArgs(2, 1), _),
    ));
    assert!(matches!(
        parse_term_err("(=> true 0)"),
        ParserError(ErrorKind::SortError(SortError::Expected { .. }), _),
    ));
}

#[test]
fn test_ite() {
    run_parser_tests(&[
        (
            "(ite true 2 3)",
            Term::Op(
                Operator::Ite,
                vec![
                    Rc::new(terminal!(bool true)),
                    Rc::new(terminal!(int 2)),
                    Rc::new(terminal!(int 3)),
                ],
            ),
        ),
        (
            "(ite (not true) 2 (ite false 2 1))",
            Term::Op(
                Operator::Ite,
                vec![
                    Rc::new(parse_term("(not true)")),
                    Rc::new(terminal!(int 2)),
                    Rc::new(Term::Op(
                        Operator::Ite,
                        vec![
                            Rc::new(terminal!(bool false)),
                            Rc::new(terminal!(int 2)),
                            Rc::new(terminal!(int 1)),
                        ],
                    )),
                ],
            ),
        ),
    ]);

    assert!(matches!(
        parse_term_err("(ite true 0)"),
        ParserError(ErrorKind::WrongNumberOfArgs(3, 2), _),
    ));
    assert!(matches!(
        parse_term_err("(ite 0 1 2)"),
        ParserError(
            ErrorKind::SortError(SortError::Expected {
                expected: Term::Sort(Sort::Bool),
                ..
            }),
            _
        ),
    ));
    assert!(matches!(
        parse_term_err("(ite false 10 10.0)"),
        ParserError(ErrorKind::SortError(SortError::Expected { .. }), _),
    ));
}

#[test]
fn test_quantifiers() {
    run_parser_tests(&[
        (
            "(exists ((p Bool)) p)",
            Term::Quant(
                Quantifier::Exists,
                vec![("p".into(), Term::BOOL_SORT.clone().into())],
                Rc::new(terminal!(var "p"; BOOL_SORT)),
            ),
        ),
        (
            "(forall ((x Real) (y Real)) (= (+ x y) 0.0))",
            Term::Quant(
                Quantifier::Forall,
                vec![
                    ("x".into(), Term::REAL_SORT.clone().into()),
                    ("y".into(), Term::REAL_SORT.clone().into()),
                ],
                Rc::new(Term::Op(
                    Operator::Equals,
                    vec![
                        Rc::new(Term::Op(
                            Operator::Add,
                            vec![
                                terminal!(var "x"; REAL_SORT).into(),
                                terminal!(var "y"; REAL_SORT).into(),
                            ],
                        )),
                        terminal!(real 0 / 1).into(),
                    ],
                )),
            ),
        ),
    ]);
    assert!(matches!(
        parse_term_err("(exists () true)"),
        ParserError(ErrorKind::EmptySequence, _),
    ));
    assert!(matches!(
        parse_term_err("(forall ((x Int)) (+ x x)"),
        ParserError(ErrorKind::SortError(SortError::Expected { .. }), _),
    ));
}

#[test]
fn test_let_terms() {
    run_parser_tests(&[
        (
            "(let ((p false)) p)",
            Term::Let(
                vec![("p".into(), Rc::new(terminal!(bool false)))],
                Rc::new(terminal!(var "p"; BOOL_SORT)),
            ),
        ),
        (
            "(let ((x 1) (y 2)) (+ x y))",
            Term::Let(
                vec![
                    ("x".into(), terminal!(int 1).into()),
                    ("y".into(), terminal!(int 2).into()),
                ],
                Rc::new(Term::Op(
                    Operator::Add,
                    vec![
                        terminal!(var "x"; INT_SORT).into(),
                        terminal!(var "y"; INT_SORT).into(),
                    ],
                )),
            ),
        ),
    ]);
    assert!(matches!(
        parse_term_err("(let () 0)"),
        ParserError(ErrorKind::EmptySequence, _),
    ));
}

#[test]
fn test_annotated_terms() {
    run_parser_tests(&[
        ("(! 0 :named foo)", terminal!(int 0)),
        ("(! (! 0 :named foo) :named bar)", terminal!(int 0)),
        (
            "(! (! 0 :pattern ((+ 1 0) 3)) :named bar)",
            terminal!(int 0),
        ),
        (
            "(ite (! true :named baz) 2 3)",
            Term::Op(
                Operator::Ite,
                vec![
                    Rc::new(terminal!(bool true)),
                    Rc::new(terminal!(int 2)),
                    Rc::new(terminal!(int 3)),
                ],
            ),
        ),
    ]);
    assert!(matches!(
        parse_term_err("(! true)"),
        ParserError(ErrorKind::EmptySequence, _),
    ));
    assert!(matches!(
        parse_term_err("(! true not_a_keyword)"),
        ParserError(ErrorKind::UnexpectedToken(_), _),
    ));
    assert!(matches!(
        parse_term_err("(! true :unknown)"),
        ParserError(ErrorKind::UnknownAttribute(_), _),
    ));
    assert!(matches!(
        parse_term_err("(! true :named 1 2 3)"),
        ParserError(ErrorKind::UnexpectedToken(_), _),
    ));
}

#[test]
fn test_declare_fun() {
    parse_term_with_definitions(
        "(declare-fun f (Bool Int Real) Real)",
        "(f false 42 3.14159)",
    );

    parse_term_with_definitions(
        "(declare-fun y () Real)
         (declare-fun f (Real) Int)
         (declare-fun g (Int Int) Bool)",
        "(g (f y) 0)",
    );

    let got = parse_term_with_definitions("(declare-fun x () Real)", "x");
    assert_deep_eq!(&terminal!(var "x"; REAL_SORT), &got);
}

#[test]
fn test_declare_sort() {
    parse_term_with_definitions(
        "(declare-sort T 0)
         (declare-sort U 0)
         (declare-sort Y 0)
         (declare-fun t () T)
         (declare-fun u () U)
         (declare-fun f (T U) Y)",
        "(f t u)",
    );

    let got = parse_term_with_definitions(
        "(declare-sort T 0)
         (declare-fun x () T)",
        "x",
    );
    let expected_sort = Term::Sort(Sort::Atom("T".to_string(), Vec::new()));
    assert_deep_eq!(&terminal!(var "x"; Rc::new(expected_sort)), &got);
}

#[test]
fn test_define_fun() {
    let got = parse_term_with_definitions(
        "(define-fun add ((a Int) (b Int)) Int (+ a b))",
        "(add 2 3)",
    );
    assert_deep_eq!(&parse_term("(+ 2 3)"), &got);

    let got = parse_term_with_definitions("(define-fun x () Int 2)", "(+ x 3)");
    assert_deep_eq!(&parse_term("(+ 2 3)"), &got);

    let got = parse_term_with_definitions(
        "(define-fun f ((x Int)) Int (+ x 1))
         (define-fun g ((a Int) (b Int)) Int (* (f a) (f b)))",
        "(g 2 3)",
    );
    let expected = parse_term("(* (+ 2 1) (+ 3 1))");
    assert_deep_eq!(&expected, &got);
}

#[test]
fn test_step() {
    let input = "
        (step t1 (cl (= (+ 2 3) (- 1 2))) :rule rule-name)
        (step t2 (cl) :rule rule-name :premises (t1))
        (step t3 (cl) :rule rule-name :args (1 2.0 \"three\"))
        (step t4 (cl) :rule rule-name :args ((:= a 12) (:= b 3.14) (:= c (* 6 7))))
        (step t5 (cl) :rule rule-name :premises (t1 t2 t3) :args (42))
    ";
    let proof = parse_proof(input);
    assert_eq!(proof.commands.len(), 5);

    assert_deep_eq!(
        &proof.commands[0],
        &ProofCommand::Step(ProofStep {
            index: "t1".into(),
            clause: vec![Rc::new(parse_term("(= (+ 2 3) (- 1 2))"))],
            rule: "rule-name".into(),
            premises: Vec::new(),
            args: Vec::new(),
        })
    );

    assert_deep_eq!(
        &proof.commands[1],
        &ProofCommand::Step(ProofStep {
            index: "t2".into(),
            clause: Vec::new(),
            rule: "rule-name".into(),
            premises: vec![0],
            args: Vec::new(),
        })
    );

    assert_deep_eq!(
        &proof.commands[2],
        &ProofCommand::Step(ProofStep {
            index: "t3".into(),
            clause: Vec::new(),
            rule: "rule-name".into(),
            premises: Vec::new(),
            args: {
                vec![
                    terminal!(int 1),
                    terminal!(real 2 / 1),
                    terminal!(string "three"),
                ]
                .into_iter()
                .map(|term| ProofArg::Term(Rc::new(term)))
                .collect()
            },
        })
    );

    assert_deep_eq!(
        &proof.commands[3],
        &ProofCommand::Step(ProofStep {
            index: "t4".into(),
            clause: Vec::new(),
            rule: "rule-name".into(),
            premises: Vec::new(),
            args: {
                vec![
                    ("a", terminal!(int 12)),
                    ("b", terminal!(real 314 / 100)),
                    ("c", parse_term("(* 6 7)")),
                ]
                .into_iter()
                .map(|(name, term)| ProofArg::Assign(name.into(), Rc::new(term)))
                .collect()
            },
        })
    );

    assert_deep_eq!(
        &proof.commands[4],
        &ProofCommand::Step(ProofStep {
            index: "t5".into(),
            clause: Vec::new(),
            rule: "rule-name".into(),
            premises: vec![0, 1, 2],
            args: vec![ProofArg::Term(Rc::new(terminal!(int 42)))],
        })
    );
}
