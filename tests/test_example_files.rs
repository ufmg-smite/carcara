extern crate walkdir;

use std::{ffi::OsStr, fs::File, io::BufReader, path::Path};

use verit_proof_checker::*;
use walkdir::WalkDir;

fn test_file(problem_path: &Path, proof_path: &Path) -> Option<()> {
    use checker::CheckerError;
    use parser::error::ParserError;

    let problem_reader = BufReader::new(File::open(problem_path).ok()?);
    let proof_reader = BufReader::new(File::open(proof_path).ok()?);

    let proof = match parser::parse_problem_proof(problem_reader, proof_reader) {
        Err(ParserError::NotYetImplemented) => return Some(()),
        p => p.ok()?,
    };
    match checker::ProofChecker::new(proof).check() {
        Ok(_) | Err(CheckerError::UnknownRule(_)) => Some(()),
        Err(CheckerError::FailedOnRule(_)) => None,
    }
}

#[test]
fn test_examples() {
    fn is_problem_file(entry: &walkdir::Result<walkdir::DirEntry>) -> bool {
        let entry = entry.as_ref().unwrap();
        entry.file_type().is_file() && entry.path().extension() != Some(OsStr::new("proof"))
    }
    let wd = WalkDir::new("test-examples").into_iter();
    for entry in wd.filter(is_problem_file) {
        let entry = entry.unwrap();
        let problem_path = entry.path();
        let proof_path = {
            let mut owned = problem_path.to_owned();
            let mut file_name = owned.file_name().unwrap().to_owned();
            file_name.push(".proof");
            owned.pop();
            owned.push(file_name);
            owned
        };
        test_file(problem_path, &proof_path)
            .unwrap_or_else(|| panic!("failed on problem: {}", &problem_path.to_str().unwrap()));
    }
}
