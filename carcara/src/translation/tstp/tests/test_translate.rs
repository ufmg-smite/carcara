//! Small test suite for Tstp ASTs generation, from Alethe proof certificates.

#[cfg(test)]
use crate::translation::{
    tstp::{alethe_2_tstp::*, printer::PrintProof, printer::*},
    Translator,
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
fn test_let_example() {
    // Test from files let.*

    let mut tstp_translator = TstpTranslator::new();

    let mut buf_problem = Vec::new();
    let annotated_formula_formatter_problem = AnnotatedFormulaFormatter::new(&mut buf_problem);
    let mut printer_problem = TstpPrinter::new(annotated_formula_formatter_problem);

    // let mut buf_proof = Vec::new();
    //let annotated_formula_formatter_proof = AnnotatedFormulaFormatter::new(&mut buf_proof);
    // let mut printer_proof = TstpPrinter::new(annotated_formula_formatter_proof);

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

    let alethe_certificate = "(assume h1 (= a b))
                                                (anchor :step t2 :args ((:= x b)))
                                                (step t1 (cl (= x b)) :rule refl)
                                                (step t2 (cl (= (let ((x a)) x) b)) :rule let :premises (h1))";

    let (problem_ast, _, _pool) = parse_instance(
        problem.as_bytes(),
        alethe_certificate.as_bytes(),
        TEST_CONFIG,
    )
    .expect(ERROR_MESSAGE);

    let tstp_problem = tstp_translator.translate_problem(&problem_ast);

    printer_problem.write_proof(&tstp_problem).unwrap();
    // TODO : "The name identifies the formula within the problem"
    // Hence, in tff('U',type,'U': $tType )., its named shouldn't be 'U'.
    // See if we can use the conventions mentioned in the grammar doc.
    assert_eq!(
        "tff('U',type,'U': $tType ).
tff(p1,type,p1: $o ).
tff(p2,type,p2: $o ).
tff(p3,type,p3: $o ).
tff(a,type,a: 'U' ).
tff(b,type,b: 'U' ).
tff(c,type,c: 'U' ).
tff(d,type,d: 'U' ).
tff(f,type,f: ( 'U' * 'U' ) > 'U' ).
tff(formula_1,axiom,a = b ).
tff(formula_2,axiom,c = d ).
tff(formula_3,axiom,p1 ).
tff(formula_4,axiom,( ~ p1  | ( p2 & p3 ) ) ).
tff(formula_5,axiom,( ~ p3 | ( f(a,c) != f(b,d) ) ) ).",
        std::str::from_utf8(&buf_problem).unwrap()
    );

    //     let commands = ProofNode::from_commands(proof_ast.commands);
    //     let tstp_proof = tstp_translator.translate(&commands);

    //     printer_proof.write_proof(tstp_proof).unwrap();

    //     assert_eq!(
    //         "%---Types:
    // tff('U',type, 'U': $tType ).

    // %---Declarations:
    // tff(a,type, a: 'U' ).
    // tff(b,type, b: 'U' ).
    // tff(c,type, c: 'U' ).
    // tff(d,type, d: 'U' ).
    // tff(f,type, f: ( 'U' * 'U' ) > 'U' ).
    // tff(p1,type, p1: $o ).
    // tff(p2,type, p2: $o ).
    // tff(p3,type, p3: $o ).",
    //         std::str::from_utf8(&buf_proof).unwrap()
    //     );
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
