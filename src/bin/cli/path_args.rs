use crate::error::CliError;
use std::{
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
};

const SMT_FILE_EXTENSIONS: [&str; 3] = ["smt", "smt2", "smt_in"];
const ALETHE_FILE_EXTENSIONS: [&str; 2] = ["alethe", "proof"];

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
    let file_type = fs::metadata(&path)
        .map_err(|inner| carcara::Error::Io { inner, file: path.clone() })?
        .file_type();
    if file_type.is_file() {
        let is_proof_file = path
            .extension()
            .and_then(OsStr::to_str)
            .is_some_and(|ext| ALETHE_FILE_EXTENSIONS.contains(&ext));
        if is_proof_file {
            let problem_file = infer_problem_path(&path)?;
            acc.push((problem_file, path))
        }
    } else if file_type.is_dir() {
        let dir = fs::read_dir(&path)
            .map_err(|inner| carcara::Error::Io { inner, file: path.clone() })?;
        for entry in dir {
            let entry = entry.map_err(|inner| carcara::Error::Io { inner, file: path.clone() })?;
            get_instances_from_dir(entry.path(), acc)?;
        }
    }
    // We ignore anything that `fs::metadata` doesn't report as either a file or a directory.
    // `fs::metadata` follows symlinks, so this should only happen if the path is something weird
    // like a device file
    Ok(())
}

pub fn get_instances_from_paths<T, I>(paths: T) -> Result<Vec<(PathBuf, PathBuf)>, CliError>
where
    I: AsRef<Path>,
    T: IntoIterator<Item = I>,
{
    let mut result = Vec::new();
    for p in paths {
        let p = p.as_ref();
        let file_type = fs::metadata(p)
            .map_err(|inner| carcara::Error::Io { inner, file: p.into() })?
            .file_type();
        if file_type.is_file() {
            let problem_file = infer_problem_path(p)?;
            result.push((problem_file, p.into()))
        } else {
            get_instances_from_dir(p.into(), &mut result)?;
        }
    }

    Ok(result)
}
