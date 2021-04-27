#![cfg(test)]

use super::*;

impl<'a> Parser<std::io::Cursor<&'a str>> {
    pub fn from_str(input: &'a str) -> ParserResult<Self> {
        Self::new(std::io::Cursor::new(input))
    }

    fn from_str_with_state(input: &'a str, state: ParserState) -> ParserResult<Self> {
        Self::with_state(std::io::Cursor::new(input), state)
    }
}

const ERROR_MESSAGE: &str = "parser error during test";

pub fn parse_term(input: &str) -> Term {
    Parser::from_str(input)
        .and_then(|mut p| p.parse_term())
        .expect(ERROR_MESSAGE)
}

pub fn parse_term_err(input: &str) -> ParserError {
    Parser::from_str(input)
        .and_then(|mut p| p.parse_term())
        .expect_err("expected error")
}

/// Parses a series of definitions and declarations, and then parses a term and returns it.
pub fn parse_term_with_definitions(definitions: &str, term: &str) -> Term {
    let mut parser = Parser::from_str(definitions).expect(ERROR_MESSAGE);
    parser.parse_problem().expect(ERROR_MESSAGE);

    // To keep the definitions and delcarations, we transfer the parser state to the new
    // parser.
    let mut new_parser = Parser::from_str_with_state(term, parser.state).expect(ERROR_MESSAGE);
    new_parser.parse_term().expect(ERROR_MESSAGE)
}

pub fn parse_proof(input: &str) -> Proof {
    Parser::from_str(input)
        .and_then(|mut p| p.parse_proof())
        .expect(ERROR_MESSAGE)
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
    use std::collections::HashSet;

    let input = "(-
        (-
            (+ 1 2)
            (/ (+ 1 2) (+ 1 2))
        )
        (* 2 2)
    )";
    let mut parser = Parser::from_str(input).unwrap();
    parser.parse_term().unwrap();

    // We expect this input to result in 6 unique terms after parsing:
    //   1
    //   2
    //   (+ 1 2)
    //   (/ (+ 1 2) (+ 1 2))
    //   (- (+ 1 2) (/ ...))
    //   (* 2 2)
    // Note that the outer term (- (- ...) (* 2 2)) is not added to the hash map
    let expected = vec![
        // The Bool sort is always added to the terms map because of the boolean bulit-ins "true"
        // and "false"
        "Bool",
        "1",
        "2",
        "(+ 1 2)",
        "(/ (+ 1 2) (+ 1 2))",
        "(- (+ 1 2) (/ (+ 1 2) (+ 1 2)))",
        "(* 2 2)",
    ]
    .into_iter()
    .collect::<HashSet<&str>>();

    assert_eq!(parser.state.terms_map.len(), expected.len());

    for got in parser.state.terms_map.keys() {
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
                vec![
                    ByRefRc::new(terminal!(int 2)),
                    ByRefRc::new(terminal!(int 3)),
                ],
            ),
        ),
        (
            "(* 2 3 5 7)",
            Term::Op(
                Operator::Mult,
                vec![
                    ByRefRc::new(terminal!(int 2)),
                    ByRefRc::new(terminal!(int 3)),
                    ByRefRc::new(terminal!(int 5)),
                    ByRefRc::new(terminal!(int 7)),
                ],
            ),
        ),
        (
            "(- 5)",
            Term::Op(Operator::Sub, vec![ByRefRc::new(terminal!(int 5))]),
        ),
        (
            "(- (+ 1 1) 2)",
            Term::Op(
                Operator::Sub,
                vec![
                    ByRefRc::new(Term::Op(
                        Operator::Add,
                        vec![
                            ByRefRc::new(terminal!(int 1)),
                            ByRefRc::new(terminal!(int 1)),
                        ],
                    )),
                    ByRefRc::new(terminal!(int 2)),
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
                    ByRefRc::new(terminal!(bool true)),
                    ByRefRc::new(terminal!(bool false)),
                ],
            ),
        ),
        (
            "(or true true false)",
            Term::Op(
                Operator::Or,
                vec![
                    ByRefRc::new(terminal!(bool true)),
                    ByRefRc::new(terminal!(bool true)),
                    ByRefRc::new(terminal!(bool false)),
                ],
            ),
        ),
        (
            "(or true (and false false))",
            Term::Op(
                Operator::Or,
                vec![
                    ByRefRc::new(terminal!(bool true)),
                    ByRefRc::new(Term::Op(
                        Operator::And,
                        vec![
                            ByRefRc::new(terminal!(bool false)),
                            ByRefRc::new(terminal!(bool false)),
                        ],
                    )),
                ],
            ),
        ),
        (
            "(= 2 3)",
            Term::Op(
                Operator::Eq,
                vec![
                    ByRefRc::new(terminal!(int 2)),
                    ByRefRc::new(terminal!(int 3)),
                ],
            ),
        ),
        (
            "(not false)",
            Term::Op(Operator::Not, vec![ByRefRc::new(terminal!(bool false))]),
        ),
        (
            "(distinct 4 2)",
            Term::Op(
                Operator::Distinct,
                vec![
                    ByRefRc::new(terminal!(int 4)),
                    ByRefRc::new(terminal!(int 2)),
                ],
            ),
        ),
        (
            "(=> (= 0 1) true false)",
            Term::Op(
                Operator::Implies,
                vec![
                    ByRefRc::new(Term::Op(
                        Operator::Eq,
                        vec![
                            ByRefRc::new(terminal!(int 0)),
                            ByRefRc::new(terminal!(int 1)),
                        ],
                    )),
                    ByRefRc::new(terminal!(bool true)),
                    ByRefRc::new(terminal!(bool false)),
                ],
            ),
        ),
    ]);

    assert!(matches!(
        parse_term_err("(or true 1.2)"),
        ParserError(
            ErrorKind::SortError(SortError::Expected {
                expected: Term::Sort(SortKind::Bool, _),
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
        parse_term_err("(or true)"),
        ParserError(ErrorKind::WrongNumberOfArgs(2, 1), _),
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
                    ByRefRc::new(terminal!(bool true)),
                    ByRefRc::new(terminal!(int 2)),
                    ByRefRc::new(terminal!(int 3)),
                ],
            ),
        ),
        (
            "(ite (not true) 2 (ite false 2 1))",
            Term::Op(
                Operator::Ite,
                vec![
                    ByRefRc::new(parse_term("(not true)")),
                    ByRefRc::new(terminal!(int 2)),
                    ByRefRc::new(Term::Op(
                        Operator::Ite,
                        vec![
                            ByRefRc::new(terminal!(bool false)),
                            ByRefRc::new(terminal!(int 2)),
                            ByRefRc::new(terminal!(int 1)),
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
                expected: Term::Sort(SortKind::Bool, _),
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
    assert!(DeepEq::eq(
        &terminal!(var "x"; ByRefRc::new(Term::REAL_SORT.clone())),
        &got
    ));
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
    let expected_sort = Term::Sort(SortKind::Atom, vec![ByRefRc::new(terminal!(string "T"))]);
    assert!(DeepEq::eq(
        &terminal!(var "x"; ByRefRc::new(expected_sort)),
        &got
    ));
}

#[test]
fn test_define_fun() {
    let got = parse_term_with_definitions(
        "(define-fun add ((a Int) (b Int)) Int (+ a b))",
        "(add 2 3)",
    );
    assert!(DeepEq::eq(&parse_term("(+ 2 3)"), &got));

    let got = parse_term_with_definitions("(define-fun x () Int 2)", "(+ x 3)");
    assert!(DeepEq::eq(&parse_term("(+ 2 3)"), &got));

    let got = parse_term_with_definitions(
        "(define-fun f ((x Int)) Int (+ x 1))
         (define-fun g ((a Int) (b Int)) Int (* (f a) (f b)))",
        "(g 2 3)",
    );
    let expected = parse_term("(* (+ 2 1) (+ 3 1))");
    assert!(DeepEq::eq(&expected, &got));
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
    assert_eq!(proof.0.len(), 5);

    assert!(DeepEq::eq(
        &proof.0[0],
        &ProofCommand::Step {
            clause: vec![ByRefRc::new(parse_term("(= (+ 2 3) (- 1 2))"))],
            rule: "rule-name".into(),
            premises: Vec::new(),
            args: Vec::new(),
        }
    ));

    assert!(DeepEq::eq(
        &proof.0[1],
        &ProofCommand::Step {
            clause: Vec::new(),
            rule: "rule-name".into(),
            premises: vec![0],
            args: Vec::new(),
        }
    ));

    assert!(DeepEq::eq(
        &proof.0[2],
        &ProofCommand::Step {
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
                .map(|term| ProofArg::Term(ByRefRc::new(term)))
                .collect()
            },
        }
    ));

    assert!(DeepEq::eq(
        &proof.0[3],
        &ProofCommand::Step {
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
                .map(|(name, term)| ProofArg::Assign(name.into(), ByRefRc::new(term)))
                .collect()
            },
        }
    ));

    assert!(DeepEq::eq(
        &proof.0[4],
        &ProofCommand::Step {
            clause: Vec::new(),
            rule: "rule-name".into(),
            premises: vec![0, 1, 2],
            args: vec![ProofArg::Term(ByRefRc::new(terminal!(int 42)))],
        }
    ));
}
