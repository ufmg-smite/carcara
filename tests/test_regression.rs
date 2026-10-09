//! Runs the regression cases in `tests/regression`. Cases in `valid/` must be accepted, and cases
//! in `invalid/` must be rejected. No case may panic.
//!
//! These tests are ignored by default, since many cases still fail. To run them, use
//! `cargo test --test test_regression -- --ignored`.
//!
//! A case can change how it is run with directives in the comments at the start of its proof file:
//!
//! - `; carcara-command: <check | elaborate>`: which command to run. Defaults to `check`.
//! - `; carcara-option: <name> <args>...`: an option, named like the corresponding CLI flag
//!   (without the leading `--`).

use carcara::*;
use std::{
    fs,
    num::NonZero,
    path::{Path, PathBuf},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Command {
    Check,
    Elaborate,
}

#[derive(Debug)]
struct Header {
    command: Command,
    parser_config: parser::Config,
    rare_file: Option<PathBuf>,
    num_threads: Option<NonZero<usize>>,
    pipeline: Option<Vec<elaborator::ElaborationPass>>,
}

fn parse_pass(name: &str) -> Result<elaborator::ElaborationPass, String> {
    use elaborator::ElaborationPass::*;
    Ok(match name {
        "polyeq" => Polyeq,
        "hole" => Hole,
        "local" => Local,
        "uncrowd" => Uncrowd,
        "reordering" => Reordering,
        "sat-refutation" => SatRefutation,
        _ => return Err(format!("unknown elaboration pass '{name}'")),
    })
}

fn parse_option(header: &mut Header, name: &str, args: &[&str]) -> Result<(), String> {
    let config = header.parser_config;
    match (name, args) {
        ("apply-function-defs", []) => header.parser_config = config.apply_function_defs(true),
        ("expand-let-bindings", []) => header.parser_config = config.expand_lets(true),
        ("allow-int-real-subtyping", []) => {
            header.parser_config = config.allow_int_real_subtyping(true)
        }
        ("allow-higher-order-indexed-ops", []) => {
            header.parser_config = config.allow_higher_order_indexed_ops(true)
        }
        ("rare-file", [path]) => header.rare_file = Some(path.into()),
        ("num-threads", [n]) => {
            let n = n
                .parse()
                .map_err(|_| format!("invalid number of threads '{n}'"))?;
            header.num_threads = Some(n)
        }
        ("pipeline", passes) if !passes.is_empty() => {
            let passes = passes
                .iter()
                .map(|p| parse_pass(p))
                .collect::<Result<_, _>>()?;
            header.pipeline = Some(passes)
        }
        _ => return Err(format!("invalid option '{name}' with arguments {args:?}")),
    };
    Ok(())
}

fn parse_header(proof_path: &Path) -> Result<Header, String> {
    let contents = fs::read_to_string(proof_path).map_err(|e| e.to_string())?;
    let mut header = Header {
        command: Command::Check,
        parser_config: parser::Config::new(),
        rare_file: None,
        num_threads: None,
        pipeline: None,
    };
    let mut command = None;

    for line in contents.lines().take_while(|l| l.starts_with(';')) {
        let Some(directive) = line[1..].trim().strip_prefix("carcara-") else {
            continue;
        };
        let (key, value) = directive
            .split_once(':')
            .ok_or_else(|| format!("malformed directive '{line}'"))?;
        let value = value.trim();
        match key {
            "command" if command.is_some() => {
                return Err("'carcara-command' given more than once".to_owned());
            }
            "command" => {
                let c = match value {
                    "check" => Command::Check,
                    "elaborate" => Command::Elaborate,
                    _ => return Err(format!("unknown command '{value}'")),
                };
                command = Some(c);
            }
            "option" => {
                let args: Vec<_> = value.split_whitespace().collect();
                let (name, args) = args.split_first().ok_or("empty option")?;
                parse_option(&mut header, name, args)?;
            }
            _ => return Err(format!("unknown directive 'carcara-{key}'")),
        };
    }

    header.command = command.unwrap_or(Command::Check);
    if header.num_threads.is_some() && header.command != Command::Check {
        return Err("option 'num-threads' is only allowed with the 'check' command".into());
    }
    if header.pipeline.is_some() && header.command != Command::Elaborate {
        return Err("option 'pipeline' is only allowed with the 'elaborate' command".into());
    }
    Ok(header)
}

fn run_test(proof_path: &Path, header: &Header) -> CarcaraResult<Status> {
    let rare_rules = match &header.rare_file {
        Some(f) => Some(parser::Source::file(proof_path.parent().unwrap().join(f))?),
        None => None,
    };
    let input = Input {
        problem: parser::Source::file(proof_path.with_extension(""))?,
        proof: parser::Source::file(proof_path)?,
        rare_rules,
    };
    let checker_config = checker::Config::new();

    match header.command {
        Command::Check => match header.num_threads {
            Some(n) => check_parallel(
                input,
                header.parser_config,
                checker_config,
                n,
                None,
                &mut (),
            ),
            None => check(input, header.parser_config, checker_config, &mut ()),
        },
        Command::Elaborate => {
            use elaborator::ElaborationPass::*;

            // Same as the CLI's default pipeline
            let pipeline = header
                .pipeline
                .clone()
                .unwrap_or_else(|| vec![Polyeq, Hole, Local, Uncrowd, Reordering]);
            let config = elaborator::Config::new();
            check_and_elaborate(
                input,
                header.parser_config,
                checker_config,
                config,
                pipeline,
                &mut (),
            )
            .map(|(status, ..)| status)
        }
    }
}

fn test_file(proof_path: &Path, expect_valid: bool) {
    let path = proof_path.display();
    let header = parse_header(proof_path).unwrap_or_else(|e| panic!("{path}: {e}"));

    match run_test(proof_path, &header) {
        // An IO error means the case itself is broken (e.g., a wrong `rare-file` path), so it never
        // counts as the proof being rejected
        Err(e @ Error::Io { .. }) => panic!("{path}: {e}"),
        Err(e) if expect_valid => panic!("{path}: {e}"),
        Ok(status) if !expect_valid => panic!("{path}: expected an error, got '{status}'"),
        _ => (),
    }
}

#[test_generator::from_dir(path = "tests/regression/valid", ignore)]
#[allow(dead_code)]
fn regression_valid(proof_path: &Path) {
    test_file(proof_path, true);
}

#[test_generator::from_dir(path = "tests/regression/invalid", ignore)]
#[allow(dead_code)]
fn regression_invalid(proof_path: &Path) {
    test_file(proof_path, false);
}
