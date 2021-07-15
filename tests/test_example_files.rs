use std::{
    ffi::OsStr,
    fs::{self, File},
    io::{self, BufReader},
    path::Path,
};

use verit_proof_checker::*;

fn test_file(problem_path: &Path, proof_path: &Path) {
    use checker::CheckerError;
    use parser::error::{ErrorKind, ParserError};

    match check(problem_path, proof_path, true, false) {
        Ok(()) | Err(Error::Parser(ParserError(ErrorKind::NotYetImplemented, _))) => (),
        Err(Error::Parser(e)) => panic!(
            "\ntest file \"{}\"\nreturned parser error: {:?}\n",
            &problem_path.to_str().unwrap(),
            e,
        ),
        Err(Error::Checker(CheckerError::FailedOnRule(rule))) => panic!(
            "\ntest file \"{}\"\nfailed on rule \"{}\"\n",
            &problem_path.to_str().unwrap(),
            rule,
        ),
        // We told the checker to skip unknown rules, so this error is never returned
        Err(Error::Checker(CheckerError::UnknownRule(_))) => unreachable!(),
    }
}

fn test_examples_from_dir(dir_path: &str) {
    fn is_proof_file(entry: &io::Result<fs::DirEntry>) -> bool {
        let entry = entry.as_ref().unwrap();
        entry.file_type().unwrap().is_file()
            && entry.path().extension() == Some(OsStr::new("proof"))
    }
    let dir_path = String::from("test-examples/") + dir_path;
    let rd = fs::read_dir(dir_path).unwrap();
    for entry in rd.filter(is_proof_file) {
        let entry = entry.unwrap();
        let proof_path = entry.path();
        let problem_path = proof_path.with_extension("");
        test_file(&problem_path, &proof_path);
    }
}

macro_rules! generate_tests {
    ( $( $test_name:ident : $dir_name:literal ,)* ) => {
        $(
            #[test]
            fn $test_name() {
                test_examples_from_dir($dir_name)
            }
        )*
    };
}

generate_tests! {
    sh_problems_green_verit: "SH_problems_all_filtered/Green_veriT",
    sh_problems_ordered_resolution_prover_verit:
        "SH_problems_all_filtered/Ordered_Resolution_Prover_veriT",
    sh_problems_ordered_resolution_prover_verit_mirabelle_z3:
        "SH_problems_all_filtered/Ordered_Resolution_Prover_veriT/Mirabelle_z3",
    sh_problems_isabelle_mirabelle_bo_cvc42: "SH_problems_all_filtered/isabelle-mirabelle/BO_cvc42",
    sh_problems_isabelle_mirabelle_green_cvc42:
        "SH_problems_all_filtered/isabelle-mirabelle/Green_cvc42",
    sh_problems_isabelle_mirabelle_green_verit:
        "SH_problems_all_filtered/isabelle-mirabelle/Green_veriT",
    sh_problems_isabelle_mirabelle_green_verit2:
        "SH_problems_all_filtered/isabelle-mirabelle/Green_veriT2",
    sh_problems_isabelle_mirabelle_green_z32:
        "SH_problems_all_filtered/isabelle-mirabelle/Green_z32",
    sh_problems_isabelle_mirabelle_hol_library_smt_cvc4:
        "SH_problems_all_filtered/isabelle-mirabelle/HOL-Library/smt_cvc4",
    sh_problems_isabelle_mirabelle_hol_library_smt_verit:
        "SH_problems_all_filtered/isabelle-mirabelle/HOL-Library/smt_verit",
    sh_problems_isabelle_mirabelle_hol_library_pnt_cvc42:
        "SH_problems_all_filtered/isabelle-mirabelle/PNT_cvc42",
    sh_problems_isabelle_mirabelle_hol_library_pnt_z32:
        "SH_problems_all_filtered/isabelle-mirabelle/PNT_z32",
    sh_problems_all_filtered: "SH_problems_all_filtered/isabelle-mirabelle/Zeta_cvc42",
    simple_tests: "simple-tests",
}
