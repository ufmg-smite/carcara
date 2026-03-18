//! Test suite and related services.

pub mod test_printer;
pub mod test_translate;

use crate::ast::*;

use crate::translation::{
    eunoia::{alethe_2_eunoia::*, printer::*},
    PrintProof, Translator,
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
/// Eunoia counterpart.
pub fn eunoia_full_translation_test(alethe_problem: &str, alethe_certificate: &str,
             eunoia_problem: &str, eunoia_certificate: &str) {

    let mut eunoia_translator = EunoiaTranslator::new();

    let mut buf_problem = Vec::new();
    let s_exp_formatter_problem = SExpFormatter::new(&mut buf_problem);
    let mut printer_problem = EunoiaPrinter::new(s_exp_formatter_problem);

    let mut buf_proof = Vec::new();
    let s_exp_formatter_proof = SExpFormatter::new(&mut buf_proof);
    let mut printer_proof = EunoiaPrinter::new(s_exp_formatter_proof);

    let (problem_ast, proof_ast, _, _pool) = parse_instance(
        alethe_problem.as_bytes(),
        alethe_certificate.as_bytes(),
        None,
        TEST_CONFIG,
    )
    .expect(ERROR_MESSAGE);

    let eunoia_problem_translated = eunoia_translator.translate_problem(&problem_ast);

    printer_problem.write_proof(&eunoia_problem_translated).unwrap();

    assert_eq!(eunoia_problem, std::str::from_utf8(&buf_problem).unwrap()
    );

    let commands = ProofNode::from_commands(proof_ast.commands);
    let eunoia_certificate_translated = eunoia_translator.translate(&commands);

    printer_proof.write_proof(eunoia_certificate_translated).unwrap();

    assert_eq!(eunoia_certificate, std::str::from_utf8(&buf_proof).unwrap()
    );
}

