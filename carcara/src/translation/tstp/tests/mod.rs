//! Test suite and related services.

pub mod test_translate;

use crate::translation::{
    tstp::{alethe_2_tstp::*, printer::*},
    ProofPrinter, Translator,
};

use crate::parser::*;

const ERROR_MESSAGE: &str = "parser error during test";

const TEST_CONFIG: Config = Config {
    // Some tests need function definitions to be applied
    apply_function_defs: true,
    expand_lets: false,
    allow_int_real_subtyping: false,
    strict: false,
    parse_hole_args: false,
};

/// Structure for a basic test involving the translation of a complete 
/// certificate: compares a given alethe problem and certificate against its 
/// TSTP counterpart.
pub fn tstp_full_translation_test(alethe_problem: &str, alethe_certificate: &str,
             tstp_problem: &str, tstp_certificate: &str) {

    let mut tstp_translator = TstpTranslator::new();

    let mut buf_problem = Vec::new();
    let annotated_formula_formatter_problem = AnnotatedFormulaFormatter::new(&mut buf_problem);
    let mut printer_problem = TstpPrinter::new(annotated_formula_formatter_problem);

    let mut buf_proof = Vec::new();
    let annotated_formula_formatter_proof = AnnotatedFormulaFormatter::new(&mut buf_proof);
    let mut printer_proof = TstpPrinter::new(annotated_formula_formatter_proof);

    let (problem_ast, mut proof_ast, _, _pool) = parse_instance(
        alethe_problem,
        alethe_certificate,
        None, 
        TEST_CONFIG,
    )
    .expect(ERROR_MESSAGE);

    let tstp_problem_translated = tstp_translator.translate_problem(&problem_ast);

    printer_problem.write_proof(&tstp_problem_translated).unwrap();

    assert_eq!(tstp_problem, std::str::from_utf8(&buf_problem).unwrap());

    // let commands = ProofNode::from_commands(proof_ast.commands);
    let tstp_certificate_translated = tstp_translator.translate(&mut proof_ast);

    printer_proof.write_proof(tstp_certificate_translated).unwrap();

    assert_eq!(tstp_certificate ,std::str::from_utf8(&buf_proof).unwrap());
}

/// Structure for a basic test involving the translation of a single step.
pub fn tstp_step_translation_test(alethe_step: &str, tstp_step: &str) {
    tstp_full_translation_test("", alethe_step, "", tstp_step);
}
