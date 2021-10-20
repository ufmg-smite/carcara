mod benchmarking;
mod error;
mod logger;
mod path_args;

use ahash::AHashSet;
use alethe_proof_checker::{
    check,
    checker::{Correctness, ProofChecker},
    parser::{error::ParserResult, lexer, parse_instance},
};
use ansi_term::Color;
use clap::{App, AppSettings, Arg, ArgGroup, ArgMatches, SubCommand};
use error::CliError;
use path_args::{get_instances_from_paths, infer_problem_path};
use std::{
    fs::File,
    io::{BufReader, Write},
    path::PathBuf,
};

fn app() -> App<'static, 'static> {
    const PROBLEM_FILE_HELP: &str =
        "The original problem file. If this argument is not present, it will be inferred from the \
        proof file";

    let subcommands = vec![
        SubCommand::with_name("check")
            .about("Checks a proof file")
            .setting(AppSettings::DisableVersion)
            .arg(
                Arg::with_name("proof-file")
                    .required(true)
                    .help("The proof file to be checked"),
            )
            .arg(Arg::with_name("problem-file").help(PROBLEM_FILE_HELP))
            .arg(
                Arg::with_name("skip-unknown-rules")
                    .short("s")
                    .long("skip-unknown-rules")
                    .help("Skips rules that are not yet implemented"),
            ),
        SubCommand::with_name("parse")
            .about("Parses a proof file and prints the AST")
            .setting(AppSettings::DisableVersion)
            .arg(
                Arg::with_name("proof-file")
                    .required(true)
                    .help("The proof file to be parsed"),
            )
            .arg(Arg::with_name("problem-file").help(PROBLEM_FILE_HELP)),
        SubCommand::with_name("bench")
            .about("Checks a series of proof files and records performance statistics")
            .setting(AppSettings::DisableVersion)
            .arg(
                Arg::with_name("num-runs")
                    .short("n")
                    .long("num-runs")
                    .default_value("10")
                    .help("Number of times to run the benchmark for each file"),
            )
            .arg(
                Arg::with_name("num-jobs")
                    .short("j")
                    .long("jobs")
                    .default_value("1")
                    .help("Number of threads to use to run the benchmarks"),
            )
            .arg(Arg::with_name("files").multiple(true).required(true).help(
                "The proof files with which the benchkmark will be run. If a directory is passed, \
                the checker will recursively find all '.proof' files in the directory. The problem \
                files will be inferred from the proof files",
            )),
        SubCommand::with_name("progress-report")
            .setting(AppSettings::DisableVersion)
            .setting(AppSettings::DeriveDisplayOrder)
            .about("Prints a progress report on which rules are implemented")
            .arg(
                Arg::with_name("by-files")
                    .short("f")
                    .long("by-files")
                    .help("Reports which files have all rules implemented"),
            )
            .arg(
                Arg::with_name("by-rules")
                    .short("r")
                    .long("by-rules")
                    .help("Reports which rules in the given files are implemented"),
            )
            .arg(
                Arg::with_name("by-files-and-rules")
                    .short("a")
                    .long("by-files-and-rules")
                    .help("For every file given, reports which rules are implemented"),
            )
            .group(
                ArgGroup::with_name("mode")
                    .args(&["by-files", "by-rules", "by-files-and-rules"])
                    .required(true),
            )
            .arg(
                Arg::with_name("quiet")
                    .short("q")
                    .long("quiet")
                    .help("Print only one character per file/rule"),
            )
            .arg(Arg::with_name("files").multiple(true).help(
                "The proof files with which the progress report will be run. If a directory is \
                passed, the checker will recursively find all '.proof' files in the directory",
            )),
    ];
    App::new("Alethe proof checker")
        .version("0.1.0")
        .setting(AppSettings::SubcommandRequiredElseHelp)
        .subcommands(subcommands)
        .arg(
            Arg::with_name("log-level")
                .long("log")
                .possible_values(&["off", "error", "warn", "info"])
                .default_value("warn")
                .help("Sets the maximum logging level"),
        )
}

fn run_app(matches: &ArgMatches) -> Result<(), CliError> {
    // Instead of just returning a `Result` from `main`, we move most of the behaviour into a
    // separate function so we can control how errors are printed to the user.
    if let Some(matches) = matches.subcommand_matches("check") {
        check_subcommand(matches)
    } else if let Some(matches) = matches.subcommand_matches("parse") {
        parse_subcommand(matches)
    } else if let Some(matches) = matches.subcommand_matches("bench") {
        bench_subcommand(matches)
    } else if let Some(matches) = matches.subcommand_matches("progress-report") {
        progress_report_subcommand(matches)
    } else {
        unreachable!()
    }
}

fn main() {
    use log::LevelFilter;

    let matches = app().get_matches();
    let level = match matches.value_of("log-level") {
        Some("off") => LevelFilter::Off,
        Some("error") => LevelFilter::Error,
        Some("warn") => LevelFilter::Warn,
        Some("info") => LevelFilter::Info,
        _ => unreachable!(),
    };
    logger::init(level);
    if let Err(e) = run_app(&matches) {
        log::error!("{:?}", e);
        std::process::exit(1);
    }
}

fn check_subcommand(matches: &ArgMatches) -> Result<(), CliError> {
    let proof_file = PathBuf::from(matches.value_of("proof-file").unwrap());
    let problem_file = match matches.value_of("problem-file") {
        Some(p) => PathBuf::from(p),
        None => infer_problem_path(&proof_file)?,
    };
    let skip = matches.is_present("skip-unknown-rules");
    match check(problem_file, proof_file, skip, false)? {
        Correctness::True => println!("true"),
        Correctness::False(s, r) => println!("false ({}, {})", s, r),
    }
    Ok(())
}

fn parse_subcommand(matches: &ArgMatches) -> Result<(), CliError> {
    let proof_file = PathBuf::from(matches.value_of("proof-file").unwrap());
    let problem_file = match matches.value_of("problem-file") {
        Some(p) => PathBuf::from(p),
        None => infer_problem_path(&proof_file)?,
    };
    let (problem, proof) = (
        BufReader::new(File::open(problem_file)?),
        BufReader::new(File::open(proof_file)?),
    );
    let (proof, _) = parse_instance(problem, proof).map_err(alethe_proof_checker::Error::from)?;
    println!("{:#?}", proof);
    Ok(())
}

fn bench_subcommand(matches: &ArgMatches) -> Result<(), CliError> {
    let num_runs = matches.value_of("num-runs").unwrap();
    let num_runs = num_runs
        .parse()
        .map_err(|_| CliError::InvalidArgument(num_runs.to_string()))?;

    let num_jobs = matches.value_of("num-jobs").unwrap();
    let num_jobs = num_jobs
        .parse()
        .map_err(|_| CliError::InvalidArgument(num_jobs.to_string()))?;

    let instances = get_instances_from_paths(matches.values_of("files").unwrap())?;

    if instances.is_empty() {
        log::warn!("no files passed");
        return Ok(());
    }

    println!(
        "running benchmark on {} files, doing {} runs each",
        instances.len(),
        num_runs
    );
    let results = benchmarking::run_benchmark(&instances, num_runs, num_jobs)?;

    println!("parsing:            {}", results.parsing());
    println!("checking:           {}", results.checking());
    println!("parsing + checking: {}", results.parsing_checking());
    println!("total:              {}", results.total());

    let data_by_rule = results.step_time_by_rule();
    let mut data_by_rule: Vec<_> = data_by_rule.iter().collect();
    data_by_rule.sort_by_key(|(_, m)| m.mean);
    println!("by rule:");
    for (rule, data) in data_by_rule {
        println!("    {: <18}{}", rule, data);
    }

    println!("worst cases:");
    let worst_step = results.step_time().max();
    println!("    step:            {} ({:?})", worst_step.0, worst_step.1);

    let worst_file_parsing = results.parsing().max();
    println!(
        "    file (parsing):  {} ({:?})",
        worst_file_parsing.0 .0, worst_file_parsing.1
    );

    let worst_file_checking = results.checking().max();
    println!(
        "    file (checking): {} ({:?})",
        worst_file_checking.0 .0, worst_file_checking.1
    );

    let worst_file_total = results.total().max();
    println!(
        "    file overall:    {} ({:?})",
        worst_file_total.0 .0, worst_file_total.1
    );
    Ok(())
}

fn progress_report_subcommand(matches: &ArgMatches) -> Result<(), CliError> {
    let instances = get_instances_from_paths(matches.values_of("files").unwrap())?;
    let files: Vec<_> = instances
        .iter()
        .map(|(_problem, proof)| {
            proof
                .to_str()
                .ok_or_else(|| CliError::InvalidProofFile(proof.clone()))
        })
        .collect::<Result<_, _>>()?;

    if instances.is_empty() {
        log::warn!("no files passed");
    }

    let quiet = matches.is_present("quiet");
    if matches.is_present("by-files") {
        report_by_files(&files, quiet)?;
    } else if matches.is_present("by-rules") {
        report_by_rules(&files, quiet)?;
    } else if matches.is_present("by-files-and-rules") {
        for file in files {
            println!("{}:", file);
            report_by_rules(&[file], quiet)?;
            println!();
        }
    }
    Ok(())
}

fn get_used_rules(file_path: &str) -> ParserResult<Vec<String>> {
    use lexer::{Lexer, Token};

    let file = File::open(file_path)?;
    let mut lex = Lexer::new(BufReader::new(file))?;
    let mut result = Vec::new();
    loop {
        let tk = lex.next_token()?;
        match tk {
            Token::Eof => break,
            Token::Keyword(s) if &s == "rule" => {
                let rule_name = match lex.next_token()? {
                    Token::Symbol(s) => s,
                    Token::ReservedWord(r) => format!("{:?}", r),
                    _ => continue,
                };
                result.push(rule_name)
            }
            _ => (),
        }
    }
    Ok(result)
}

fn print_report_entry(s: &str, success: bool, quiet: bool) {
    let style = match success {
        true => Color::Green.bold(),
        false => Color::Red.normal(),
    };
    if quiet {
        print!("{}", style.paint("."));
        std::io::stdout().flush().unwrap();
    } else {
        println!("{}", style.paint(s));
    }
}

fn report_by_files(files: &[&str], quiet: bool) -> ParserResult<()> {
    let mut implemented = 0;
    for file in files {
        let all_implemented = get_used_rules(file)?
            .iter()
            .all(|rule| ProofChecker::get_rule(rule, false).is_some());
        print_report_entry(file, all_implemented, quiet);
        implemented += all_implemented as i32;
    }
    if quiet {
        println!();
    }
    println!(
        "{} / {} files with all rules implemented",
        implemented,
        files.len()
    );
    Ok(())
}

fn report_by_rules(files: &[&str], quiet: bool) -> ParserResult<()> {
    let rules = files.iter().flat_map(|file| match get_used_rules(file) {
        Ok(rules) => rules.into_iter().map(Ok).collect(),
        Err(e) => vec![Err(e)],
    });

    let mut seen = AHashSet::new();
    let mut implemented = 0;
    for r in rules {
        let r = r?;
        if seen.insert(r.clone()) {
            let success = ProofChecker::get_rule(&r, false).is_some();
            print_report_entry(&r, success, quiet);
            implemented += success as i32;
        }
    }
    if quiet {
        println!();
    }
    println!("{} / {} rules implemented", implemented, seen.len());
    Ok(())
}
