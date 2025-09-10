//! Small test suite for Tstp ASTs generation, from Alethe proof certificates.

#[cfg(test)]
use crate::ast::*;
#[cfg(test)]
use crate::translation::{
    tstp::{alethe_2_tstp::*, printer::*},
    PrintProof, Translator,
};

// TODO: ugly, copying this from parser/tests.rs
#[cfg(test)]
use crate::parser::*;
#[cfg(test)]
const ERROR_MESSAGE: &str = "parser error during test";
#[cfg(test)]
const TEST_CONFIG: Config = Config {
    // Some tests need function definitions to be applied
    apply_function_defs: true,
    expand_lets: false,
    allow_int_real_subtyping: false,
    strict: false,
    parse_hole_args: false,
};

#[test]
fn test_simple_cong_example() {
    // Test from files simple-cong.*

    let mut tstp_translator = TstpTranslator::new();

    let mut buf_problem = Vec::new();
    let annotated_formula_formatter_problem = AnnotatedFormulaFormatter::new(&mut buf_problem);
    let mut printer_problem = TstpPrinter::new(annotated_formula_formatter_problem);

    let mut buf_proof = Vec::new();
    let annotated_formula_formatter_proof = AnnotatedFormulaFormatter::new(&mut buf_proof);
    let mut printer_proof = TstpPrinter::new(annotated_formula_formatter_proof);

    let problem = "(set-logic QF_UF)
(set-option :simplification none)

(declare-sort U 0)

(declare-const p1 Bool)
(declare-const p2 Bool)
(declare-const p3 Bool)

(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(declare-fun f (U U) U)

(assert (= a b))
(assert (= c d))
(assert (and p1 true))
(assert (or (not p1) (and p2 p3)))
(assert (or (not p3) (not (= (f a c) (f b d)))))

(check-sat)";

    let alethe_certificate = "
(assume a0 (= a b))
(assume a1 (= c d))
(assume a2 (and p1 true))
(assume a3 (or (not p1) (and p2 p3)))
(assume a4 (or (not p3) (not (= (f a c) (f b d)))))
(step t0 (cl (and (= a b) (= c d)) (not (= a b)) (not (= c d))) :rule and_neg)
(step t1 (cl (=> (and (= a b) (= c d)) (= (f a c) (f b d))) (and (= a b) (= c d))) :rule implies_neg1)
(anchor :step t2)
(assume t2.a0 (= a b))
(assume t2.a1 (= c d))
(step t2.t0 (cl (= (f a c) (f b d))) :rule cong :premises (t2.a0 t2.a1))
(step t2 (cl (not (= a b)) (not (= c d)) (= (f a c) (f b d))) :rule subproof :discharge (t2.a0 t2.a1))
(step t3 (cl (not (and (= a b) (= c d))) (= a b)) :rule and_pos :args (0))
(step t4 (cl (not (and (= a b) (= c d))) (= c d)) :rule and_pos :args (1))
(step t5 (cl (= (f a c) (f b d)) (not (and (= a b) (= c d))) (not (and (= a b) (= c d)))) :rule resolution :premises (t2 t3 t4))
(step t6 (cl (not (and (= a b) (= c d))) (not (and (= a b) (= c d))) (= (f a c) (f b d))) :rule reordering :premises (t5))
(step t7 (cl (not (and (= a b) (= c d))) (= (f a c) (f b d))) :rule contraction :premises (t6))
(step t8 (cl (=> (and (= a b) (= c d)) (= (f a c) (f b d))) (= (f a c) (f b d))) :rule resolution :premises (t1 t7))
(step t9 (cl (=> (and (= a b) (= c d)) (= (f a c) (f b d))) (not (= (f a c) (f b d)))) :rule implies_neg2)
(step t10 (cl (=> (and (= a b) (= c d)) (= (f a c) (f b d))) (=> (and (= a b) (= c d)) (= (f a c) (f b d)))) :rule resolution :premises (t8 t9))
(step t11 (cl (=> (and (= a b) (= c d)) (= (f a c) (f b d)))) :rule contraction :premises (t10))
(step t12 (cl (not (and (= a b) (= c d))) (= (f a c) (f b d))) :rule implies :premises (t11))
(step t13 (cl (not (= a b)) (not (= c d)) (= (f a c) (f b d))) :rule resolution :premises (t0 t12))
(step t14 (cl (= (f a c) (f b d)) (not (= a b)) (not (= c d))) :rule reordering :premises (t13))
(step t15 (cl (not p3) (not (= (f a c) (f b d)))) :rule or :premises (a4))
(step t16 (cl (not (and p2 p3)) p3) :rule and_pos :args (1))
(step t17 (cl p3 (not (and p2 p3))) :rule reordering :premises (t16))
(step t18 (cl (not p1) (and p2 p3)) :rule or :premises (a3))
(step t19 (cl p1) :rule and :premises (a2) :args (0))
(step t20 (cl (and p2 p3)) :rule resolution :premises (t18 t19))
(step t21 (cl p3) :rule resolution :premises (t17 t20))
(step t22 (cl (not (= (f a c) (f b d)))) :rule resolution :premises (t15 t21))
(step t23 (cl) :rule resolution :premises (t14 t22 a1 a0))";

    let (problem_ast, proof_ast, _pool) = parse_instance(
        problem.as_bytes(),
        alethe_certificate.as_bytes(),
        TEST_CONFIG,
    )
    .expect(ERROR_MESSAGE);

    let tstp_problem = tstp_translator.translate_problem(&problem_ast);

    printer_problem.write_proof(&tstp_problem).unwrap();
    // TODO : "The name identifies the formula within the problem"
    // Hence, in tff('U',type,'U': $tType )., its name shouldn't be 'U'.
    // See if we can use the conventions mentioned in the grammar doc.
    // TODO: U should be printed as 'U'.
    assert_eq!(
        "tff(type_1, type, U: $tType).
tff(type_2, type, p1: $o).
tff(type_3, type, p2: $o).
tff(type_4, type, p3: $o).
tff(type_5, type, a: 'U').
tff(type_6, type, b: 'U').
tff(type_7, type, c: 'U').
tff(type_8, type, d: 'U').
tff(type_9, type, f: ( 'U' * 'U' ) > 'U').
tff(axiom_1, axiom, ( a = b )).
tff(axiom_2, axiom, ( c = d )).
tff(axiom_3, axiom, ( p1 & $true )).
tff(axiom_4, axiom, ( ~ p1 | ( p2 & p3 ) )).
tff(axiom_5, axiom, ( ~ p3 | ~ ( f(a, c) = f(b, d) ) )).
",
        std::str::from_utf8(&buf_problem).unwrap()
    );

    let commands = ProofNode::from_commands(proof_ast.commands);
    let tstp_proof = tstp_translator.translate(&commands);

    printer_proof.write_proof(tstp_proof).unwrap();

    assert_eq!(
        "tff('U',type, 'U': $tType ).
    tff(a,type, a: 'U' ).
    tff(b,type, b: 'U' ).
    tff(c,type, c: 'U' ).
    tff(d,type, d: 'U' ).
    tff(f,type, f: ( 'U' * 'U' ) > 'U' ).
    tff(p1,type, p1: $o ).
    tff(p2,type, p2: $o ).
    tff(p3,type, p3: $o ).",
        std::str::from_utf8(&buf_proof).unwrap()
    );
}
// #[test]
// fn test_let_example() {
//     let mut tstp_translator = TstpTranslator::new();

//     let mut buf_problem = Vec::new();
//     let annotated_formula_formatter_problem = AnnotatedFormulaFormatter::new(&mut buf_problem);
//     let mut printer_problem = TstpPrinter::new(annotated_formula_formatter_problem);

//     let mut buf_proof = Vec::new();
//     let annotated_formula_formatter_proof = AnnotatedFormulaFormatter::new(&mut buf_proof);
//     let mut printer_proof = TstpPrinter::new(annotated_formula_formatter_proof);

//     let problem = "(set-logic UF)
//                            (declare-sort S 0)
//                            (declare-const a S)
//                            (declare-const b S)
//                            (assert (= a b))";

//     let alethe_certificate = "(assume h1 (= a b))
//                               (anchor :step t2 :args ((:= x b)))
//                               (step t1 (cl (= x b)) :rule refl)
//                               (step t2 (cl (= (let ((x a)) x) b)) :rule let :premises (h1))";

//     let (problem_ast, proof_ast, _pool) = parse_instance(
//         problem.as_bytes(),
//         alethe_certificate.as_bytes(),
//         TEST_CONFIG,
//     )
//     .expect(ERROR_MESSAGE);

//     let tstp_problem = tstp_translator.translate_problem(&problem_ast);

//     printer_problem.write_proof(&tstp_problem).unwrap();

//     assert_eq!(
//         "(declare-type S ( ))\n\
//          (declare-const a S)\n\
//          (declare-const b S)\n",
//         std::str::from_utf8(&buf_problem).unwrap()
//     );

//     let commands = ProofNode::from_commands(proof_ast.commands);
//     let tstp_proof = tstp_translator.translate(&commands);

//     printer_proof.write_proof(tstp_proof).unwrap();

//     assert_eq!(
//         "(define ctx1 ( ) true)\n\
//          (assume context ctx1)\n\
//          (assume h1 (= a b))\n\
//          (define ctx2 ( ) (@ctx ( ( x S ) ) (and (= x b) ctx1)))\n\
//          (assume-push context ctx2)\n\
//          (step t1 (@cl (= (@var ( ( x S ) ) x) b)) \
//          :rule refl :args ( context ))\n\
//          (step-pop t2 (@cl (= ( _ (@let ( ( x (eo::typeof a) ) ) (@var ( ( x (eo::typeof a) ) ) x)) a) b)) \
//          :rule let_elim :premises ( h1 t1 ))\n",
//         std::str::from_utf8(&buf_proof).unwrap()
//     );
//}
