#![allow(dead_code)]

use crate::error::CliError;
use std::{ffi::OsStr, fs, path::PathBuf};

const SMT_FILE_EXTENSIONS: [&str; 3] = ["smt", "smt2", "smt_in"];

pub fn infer_problem_path(proof_path: impl Into<PathBuf>) -> Result<PathBuf, CliError> {
    fn inner(mut path: PathBuf) -> Option<PathBuf> {
        while !SMT_FILE_EXTENSIONS.contains(&path.extension()?.to_str()?) {
            path.set_extension("");
        }
        Some(path)
    }
    let proof_path: PathBuf = proof_path.into();
    inner(proof_path.clone()).ok_or(CliError::CantInferProblemFile(proof_path))
}

fn get_instances_from_dir(
    path: PathBuf,
    acc: &mut Vec<(PathBuf, PathBuf)>,
) -> Result<(), CliError> {
    let file_type = fs::metadata(&path)?.file_type();
    if file_type.is_file() {
        if path.extension() == Some(OsStr::new("proof")) {
            let problem_file = infer_problem_path(&path)?;
            acc.push((problem_file, path))
        }
    } else if file_type.is_dir() {
        for entry in fs::read_dir(path)? {
            get_instances_from_dir(entry?.path(), acc)?;
        }
    }
    // We ignore anything that `fs::metadata` doesn't report as either a file or a directory.
    // `fs::metadata` follows symlinks, so this should only happen if the path is something weird
    // like a device file
    Ok(())
}

pub fn get_instances_from_paths<'a, T>(paths: T) -> Result<Vec<(PathBuf, PathBuf)>, CliError>
where
    T: Iterator<Item = &'a str>,
{
    let mut result = Vec::new();
    for p in paths {
        let file_type = fs::metadata(p)?.file_type();
        if file_type.is_file() {
            let problem_file = infer_problem_path(p)?;
            result.push((problem_file, p.into()))
        } else {
            get_instances_from_dir(p.into(), &mut result)?;
        }
    }

    Ok(result)
}
