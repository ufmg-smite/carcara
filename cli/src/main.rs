#![allow(deprecated)]

mod benchmarking;
mod error;
mod logger;
mod path_args;

use alethe_proof_checker::{
    ast::print_proof,
    benchmarking::{Metrics, OnlineBenchmarkResults},
    check, check_and_reconstruct, parser,
};
use clap::{ArgEnum, Args, Parser, Subcommand};
use const_format::{formatcp, str_index};
use error::{CliError, CliResult};
use git_version::git_version;
use path_args::{get_instances_from_paths, infer_problem_path};
use std::{
    fs::File,
    io::{self, BufRead},
    path::Path,
};

const GIT_COMMIT_HASH: &str = git_version!(fallback = "unknown");
const GIT_BRANCH_NAME: &str = git_version!(args = ["--all"]);
const APP_VERSION: &str = env!("CARGO_PKG_VERSION");

const VERSION_STRING: &str = formatcp!(
    "{} [git {} {}]",
    APP_VERSION,
    // By default, `git describe` returns something like "heads/main". We ignore the "heads/" part
    // to get only the branch name
    str_index!(GIT_BRANCH_NAME, 6..),
    GIT_COMMIT_HASH,
);

#[derive(Parser)]
#[clap(name = "alethe-proof-checker", version = VERSION_STRING)]
struct Cli {
    #[clap(subcommand)]
    command: Command,

    /// Sets the maximum logging level.
    #[clap(arg_enum, long = "log", default_value_t = LogLevel::Warn)]
    log_level: LogLevel,
}

#[derive(Subcommand)]
enum Command {
    /// Parses a proof file and prints the AST.
    Parse(ParsingOptions),

    /// Checks a proof file.
    Check(CheckingOptions),

    /// Checks and reconstructs a proof file.
    Reconstruct(CheckingOptions),

    /// Checks a series of proof files and records performance statistics.
    Bench(BenchmarkOptions),
}

#[derive(Args)]
struct ParsingOptions {
    /// The proof file to be checked
    proof_file: String,

    /// The original problem file. If this argument is not present, it will be inferred from the
    /// proof file.
    problem_file: Option<String>,

    /// Don't apply function definitions introduced by `define-fun`s and `:named` attributes.
    /// Instead, interpret them as a function declaration and an `assert` that defines the function
    /// to be equal to its body.
    #[clap(long)]
    dont_apply_function_defs: bool,
}

#[derive(Args)]
struct CheckingOptions {
    #[clap(flatten)]
    parsing: ParsingOptions,

    /// Skips rules that are not implemented.
    #[clap(short, long)]
    skip_unknown_rules: bool,
}

#[derive(Args)]
struct BenchmarkOptions {
    /// Number of times to run the benchmark for each file.
    #[clap(short, long, default_value_t = 10)]
    num_runs: usize,

    /// Number of threads to use when running the benchmark.
    #[clap(short = 'j', long, default_value_t = 1)]
    num_threads: usize,

    /// Also reconstruct each proof in addition to parsing and checking.
    #[clap(long)]
    reconstruct: bool,

    /// Show benchmark results sorted by total time taken, instead of by average time taken.
    #[clap(short = 't', long)]
    sort_by_total: bool,

    /// Dump results to csv files instead of printing to screen.
    #[clap(long = "dump-to-csv")]
    dump_to_csv: bool,

    /// The proof files on which the benchkmark will be run. If a directory is passed, the checker
    /// will recursively find all '.proof' files in the directory. The problem files will be
    /// inferred from the proof files.
    files: Vec<String>,
}

#[derive(ArgEnum, Clone)]
enum LogLevel {
    Off,
    Error,
    Warn,
    Info,
}

impl From<LogLevel> for log::LevelFilter {
    fn from(l: LogLevel) -> Self {
        match l {
            LogLevel::Off => Self::Off,
            LogLevel::Error => Self::Error,
            LogLevel::Warn => Self::Warn,
            LogLevel::Info => Self::Info,
        }
    }
}

fn main() {
    let cli = Cli::parse();
    logger::init(cli.log_level.into());

    let result = match cli.command {
        Command::Parse(options) => parse_command(options),
        Command::Check(options) => check_command(options, false),
        Command::Reconstruct(options) => check_command(options, true),
        Command::Bench(options) => bench_command(options),
    };
    if let Err(e) = result {
        log::error!("{}", e);
        std::process::exit(1);
    }
}

fn get_instance(options: ParsingOptions) -> CliResult<(Box<dyn BufRead>, Box<dyn BufRead>)> {
    fn reader_from_path<P: AsRef<Path>>(path: P) -> CliResult<Box<dyn BufRead>> {
        Ok(Box::new(io::BufReader::new(File::open(path)?)))
    }

    match (options.problem_file.as_deref(), options.proof_file.as_str()) {
        (Some("-"), "-") | (None, "-") => Err(CliError::BothFilesStdin),
        (Some(problem), "-") => Ok((reader_from_path(problem)?, Box::new(io::stdin().lock()))),
        (Some("-"), proof) => Ok((Box::new(io::stdin().lock()), reader_from_path(proof)?)),
        (Some(problem), proof) => Ok((reader_from_path(problem)?, reader_from_path(proof)?)),
        (None, proof) => Ok((
            reader_from_path(infer_problem_path(proof)?)?,
            reader_from_path(proof)?,
        )),
    }
}

fn parse_command(options: ParsingOptions) -> CliResult<()> {
    let apply_function_defs = !options.dont_apply_function_defs;
    let (problem, proof) = get_instance(options)?;
    let (proof, _) = parser::parse_instance(problem, proof, apply_function_defs)
        .map_err(alethe_proof_checker::Error::from)?;
    print_proof(&proof.commands)?;
    Ok(())
}

fn check_command(options: CheckingOptions, reconstruct: bool) -> CliResult<()> {
    let apply_function_defs = !options.parsing.dont_apply_function_defs;
    let (problem, proof) = get_instance(options.parsing)?;
    let skip = options.skip_unknown_rules;

    if reconstruct {
        let reconstructed = check_and_reconstruct(problem, proof, apply_function_defs, skip)?;
        print_proof(&reconstructed)?;
    } else {
        check(problem, proof, apply_function_defs, skip)?;
        println!("true");
    }
    Ok(())
}

fn bench_command(options: BenchmarkOptions) -> CliResult<()> {
    let instances = get_instances_from_paths(options.files.iter().map(|s| s.as_str()))?;
    if instances.is_empty() {
        log::warn!("no files passed");
    }

    println!(
        "running benchmark on {} files, doing {} runs each",
        instances.len(),
        options.num_runs
    );

    if options.dump_to_csv {
        benchmarking::run_csv_benchmark(
            &instances,
            options.num_runs,
            options.num_threads,
            false,
            options.reconstruct,
            &mut File::create("runs.csv")?,
            &mut File::create("by_rule.csv")?,
        )?;
        return Ok(());
    }

    let results: OnlineBenchmarkResults = benchmarking::run_benchmark(
        &instances,
        options.num_runs,
        options.num_threads,
        false,
        options.reconstruct,
    );
    if results.is_empty() {
        println!("no benchmark data collected");
        return Ok(());
    }

    print_benchmark_results(results, options.sort_by_total)
}

fn print_benchmark_results(results: OnlineBenchmarkResults, sort_by_total: bool) -> CliResult<()> {
    let [parsing, checking, reconstructing, accounted_for, total] = [
        results.parsing(),
        results.checking(),
        results.reconstructing(),
        results.total_accounted_for(),
        results.total(),
    ]
    .map(|m| {
        if sort_by_total {
            format!("{:#}", m)
        } else {
            format!("{}", m)
        }
    });

    println!("parsing:             {}", parsing);
    println!("checking:            {}", checking);
    if !reconstructing.is_empty() {
        println!("reconstructing:      {}", reconstructing);
    }
    println!(
        "on assume:           {} ({:.02}% of checking time)",
        results.assume_time,
        100.0 * results.assume_time.mean().as_secs_f64() / results.checking().mean().as_secs_f64(),
    );
    println!("on assume (core):    {}", results.assume_core_time);
    println!("assume ratio:        {}", results.assume_time_ratio);
    println!(
        "on deep equality:    {} ({:.02}% of checking time)",
        results.deep_eq_time,
        100.0 * results.deep_eq_time.mean().as_secs_f64() / results.checking().mean().as_secs_f64(),
    );
    println!("deep equality ratio: {}", results.deep_eq_time_ratio);
    println!("total accounted for: {}", accounted_for);
    println!("total:               {}", total);

    let data_by_rule = results.step_time_by_rule();
    let mut data_by_rule: Vec<_> = data_by_rule.iter().collect();
    data_by_rule.sort_by_key(|(_, m)| if sort_by_total { m.total() } else { m.mean() });

    println!("by rule:");
    for (rule, data) in data_by_rule {
        print!("    {: <18}", rule);
        if sort_by_total {
            println!("{:#}", data)
        } else {
            println!("{}", data)
        }
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

    let worst_file_assume = results.assume_time_ratio.max();
    println!(
        "    file (assume):   {} ({:.04}%)",
        worst_file_assume.0 .0,
        worst_file_assume.1 * 100.0
    );

    let worst_file_deep_eq = results.deep_eq_time_ratio.max();
    println!(
        "    file (deep_eq):  {} ({:.04}%)",
        worst_file_deep_eq.0 .0,
        worst_file_deep_eq.1 * 100.0
    );

    let worst_file_total = results.total().max();
    println!(
        "    file overall:    {} ({:?})",
        worst_file_total.0 .0, worst_file_total.1
    );

    let num_hard_assumes = results.num_assumes - results.num_easy_assumes;
    let percent_easy = (results.num_easy_assumes as f64) * 100.0 / (results.num_assumes as f64);
    let percent_hard = (num_hard_assumes as f64) * 100.0 / (results.num_assumes as f64);
    println!("          number of assumes: {}", results.num_assumes);
    println!(
        "                     (easy): {} ({:.02}%)",
        results.num_easy_assumes, percent_easy
    );
    println!(
        "                     (hard): {} ({:.02}%)",
        num_hard_assumes, percent_hard
    );

    let depths = results.deep_eq_depths;
    if !depths.is_empty() {
        println!("    max deep equality depth: {}", depths.max().1);
        println!("  total deep equality depth: {}", depths.total());
        println!("  number of deep equalities: {}", depths.count());
        println!("                 mean depth: {:.4}", depths.mean());
        println!(
            "standard deviation of depth: {:.4}",
            depths.standard_deviation()
        );
    }
    Ok(())
}
