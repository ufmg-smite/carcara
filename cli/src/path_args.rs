#![allow(dead_code)]

use std::{ffi::OsStr, fs, io, path::PathBuf};

const SMT_FILE_EXTENSIONS: [&str; 3] = ["smt", "smt2", "smt_in"];

pub fn infer_problem_path(proof_path: impl Into<PathBuf>) -> Option<PathBuf> {
    let mut path: PathBuf = proof_path.into();
    while !SMT_FILE_EXTENSIONS.contains(&path.extension()?.to_str()?) {
        path.set_extension("");
    }
    Some(path)
}

// TODO: Add better error handling
fn get_instances_from_dir(path: PathBuf, acc: &mut Vec<(PathBuf, PathBuf)>) -> io::Result<()> {
    let file_type = fs::metadata(&path)?.file_type();
    if file_type.is_file() {
        if path.extension() == Some(OsStr::new("proof")) {
            let problem_file = infer_problem_path(&path).unwrap();
            acc.push((problem_file, path))
        }
    } else if file_type.is_dir() {
        for entry in fs::read_dir(path)? {
            get_instances_from_dir(entry?.path(), acc)?;
        }
    } else {
        // `fs::metadata` follows symlinks, so this should only be reachable if the path is
        // something weird like a device file
        panic!("path is not file or directory");
    }
    Ok(())
}

pub fn get_instances_from_paths<'a, T>(paths: T) -> io::Result<Vec<(PathBuf, PathBuf)>>
where
    T: Iterator<Item = &'a str>,
{
    let mut result = Vec::new();
    for p in paths {
        let file_type = fs::metadata(p)?.file_type();
        if file_type.is_file() {
            let problem_file = infer_problem_path(p).unwrap();
            result.push((problem_file, p.into()))
        } else {
            get_instances_from_dir(p.into(), &mut result)?;
        }
    }

    Ok(result)
}
