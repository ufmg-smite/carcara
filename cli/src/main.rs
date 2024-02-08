mod benchmarking;
mod error;
mod logger;
mod path_args;

use carcara::{
    ast::print_proof, benchmarking::OnlineBenchmarkResults, check, check_and_elaborate,
    check_parallel, parser, CarcaraOptions, LiaGenericOptions,
};
use clap::{AppSettings, ArgEnum, Args, Parser, Subcommand};
use const_format::{formatcp, str_index};
use error::{CliError, CliResult};
use git_version::git_version;
use path_args::{get_instances_from_paths, infer_problem_path};
use std::{
    fs::File,
    io::{self, BufRead, IsTerminal},
    path::Path,
};

// `git describe --all` will try to find any ref (including tags) that describes the current commit.
// This will include tags like `carcara-0.1.0`, that we create for github releases. To account for
// that, we pass the arguments `--exclude 'carcara-*'`, ignoring these tags.
const GIT_BRANCH_NAME: &str = git_version!(
    args = ["--all", "--exclude", "carcara-*"],
    fallback = "heads/none",
);
const GIT_COMMIT_HASH: &str = git_version!(fallback = "unknown");
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
#[clap(
    name = "carcara",
    version = VERSION_STRING,
    setting = AppSettings::DeriveDisplayOrder
)]
struct Cli {
    #[clap(subcommand)]
    command: Command,

    /// Sets the maximum logging level.
    #[clap(arg_enum, global = true, long = "log", default_value_t = LogLevel::Warn)]
    log_level: LogLevel,

    /// Disables output coloring.
    #[clap(global = true, long)]
    no_color: bool,

    /// Use sharing when printing terms in error messages.
    #[clap(global = true, short, long)]
    quiet: bool,
}

#[derive(Subcommand)]
enum Command {
    /// Parses a proof file and prints it back.
    Parse(ParseCommandOptions),

    /// Checks a proof file.
    Check(CheckCommandOptions),

    /// Checks and elaborates a proof file.
    Elaborate(ElaborateCommandOptions),

    /// Checks a series of proof files and records performance statistics.
    Bench(BenchCommandOptions),

    /// Given a step, takes a slice of a proof consisting of all its transitive premises.
    Slice(SliceCommandOption),
}

#[derive(Args)]
struct Input {
    /// The proof file to be checked
    proof_file: String,

    /// The original problem file. If this argument is not present, it will be inferred from the
    /// proof file.
    problem_file: Option<String>,
}

#[derive(Args)]
struct StatsOptions {
    /// Enables the gathering of performance statistics
    #[clap(long)]
    stats: bool,
}

#[derive(Args)]
struct StackOptions {
    /// Defines the thread stack size for each check worker (does not include the main thread stack size, which should be set manually).
    #[clap(long, default_value = "0")]
    stack_size: usize,
}

#[derive(Args, Clone, Copy)]
struct ParsingOptions {
    /// Expand function definitions introduced by `define-fun`s in the SMT problem. If this flag is
    /// not present, they are instead interpreted as a function declaration and an `assert` that
    /// defines the function name to be equal to its body. Function definitions in the proof itself
    /// are always expanded.
    #[clap(long)]
    apply_function_defs: bool,

    /// Eliminates `let` bindings from terms when parsing.
    #[clap(long)]
    expand_let_bindings: bool,

    /// Enables `Int`/`Real` subtyping in the parser. This allows terms of sort `Int` to be passed
    /// to arithmetic operators that are expecting a term of sort `Real`.
    #[clap(long)]
    allow_int_real_subtyping: bool,

    /// Enables strict parsing and checking.
    ///
    /// When this flag is enabled: unary `and`, `or` and `xor` terms are not allowed; for the `refl`
    /// and `assume` rules, implicit reordering of equalities is not allowed; for the `resolution`
    /// and `th_resolution` rules, the pivots used must be passed as arguments.
    #[clap(short, long)]
    strict: bool,
}

#[derive(Args, Clone)]
struct CheckingOptions {
    /// Allow steps with rules that are not known by the checker, and consider them as holes.
    #[clap(short, long)]
    ignore_unknown_rules: bool,

    // Note: the `--skip-unknown-rules` flag has been deprecated in favor of `--ignore-unknown-rules`
    #[clap(long, conflicts_with("ignore-unknown-rules"), hide = true)]
    skip_unknown_rules: bool,

    /// Check `lia_generic` steps using the provided solver.
    #[clap(long)]
    lia_solver: Option<String>,

    /// The arguments to pass to the `lia_generic` solver. This should be a single string where
    /// multiple arguments are separated by spaces.
    #[clap(
        long,
        requires = "lia-solver",
        allow_hyphen_values = true,
        default_value = "--tlimit=10000 --lang=smt2 --proof-format-mode=alethe --proof-granularity=theory-rewrite --proof-alethe-res-pivots"
    )]
    lia_solver_args: String,

    /// Check `lia_generic` steps by calling into cvc5 (deprecated).
    #[clap(long, conflicts_with("lia-solver"))]
    lia_via_cvc5: bool,
}

#[derive(Args)]
struct PrintingOptions {
    /// Use sharing when printing proof terms.
    #[clap(long = "print-with-sharing")]
    use_sharing: bool,
}

fn build_carcara_options(
    ParsingOptions {
        apply_function_defs,
        expand_let_bindings,
        allow_int_real_subtyping,
        strict,
    }: ParsingOptions,
    CheckingOptions {
        ignore_unknown_rules,
        skip_unknown_rules,
        lia_solver,
        lia_via_cvc5,
        lia_solver_args,
    }: CheckingOptions,
    StatsOptions { stats }: StatsOptions,
) -> CarcaraOptions {
    // If no solver is provided by the `--lia-solver` option, *and* the `--lia-via-cvc5` option was
    // passed, we default to cvc5 as a solver
    let solver = lia_solver.or_else(|| lia_via_cvc5.then(|| "cvc5".into()));
    let lia_options = solver.map(|solver| LiaGenericOptions {
        solver: solver.into(),
        arguments: lia_solver_args.split_whitespace().map(Into::into).collect(),
    });
    CarcaraOptions {
        apply_function_defs,
        expand_lets: expand_let_bindings,
        allow_int_real_subtyping,
        lia_options,
        strict,
        ignore_unknown_rules: ignore_unknown_rules || skip_unknown_rules,
        stats,
    }
}

#[derive(Args)]
struct ParseCommandOptions {
    #[clap(flatten)]
    input: Input,

    #[clap(flatten)]
    parsing: ParsingOptions,

    #[clap(flatten)]
    printing: PrintingOptions,
}

#[derive(Args)]
struct CheckCommandOptions {
    #[clap(flatten)]
    input: Input,

    #[clap(flatten)]
    parsing: ParsingOptions,

    #[clap(flatten)]
    checking: CheckingOptions,

    /// Defines the number of cores for proof checking.
    #[clap(short = 'u', long, required = false, default_value = "1", validator = |s: &str| -> Result<(), String> {
        if let Ok(n) = s.to_string().parse() as Result<u32, _> {
            if n < 1 {
                Err(format!("The threads number can't be {n}."))
            } else {
                Ok(())
            }
        } else {
            Err(String::from("Not a number."))
        }
    })]
    num_threads: usize,

    #[clap(flatten)]
    stats: StatsOptions,

    #[clap(flatten)]
    stack: StackOptions,
}

#[derive(Args)]
struct ElaborateCommandOptions {
    #[clap(flatten)]
    input: Input,

    #[clap(flatten)]
    parsing: ParsingOptions,

    #[clap(flatten)]
    checking: CheckingOptions,

    #[clap(flatten)]
    printing: PrintingOptions,

    #[clap(flatten)]
    stats: StatsOptions,
}

#[derive(Args)]
struct BenchCommandOptions {
    #[clap(flatten)]
    parsing: ParsingOptions,

    #[clap(flatten)]
    checking: CheckingOptions,

    /// Also elaborate each proof in addition to parsing and checking.
    #[clap(long)]
    elaborate: bool,

    /// Number of times to run the benchmark for each file.
    #[clap(short, long, default_value_t = 1)]
    num_runs: usize,

    /// Number of jobs to run simultaneously when running the benchmark.
    #[clap(short = 'j', long, default_value_t = 1)]
    num_jobs: usize,

    /// Show benchmark results sorted by total time taken, instead of by average time taken.
    #[clap(short = 't', long)]
    sort_by_total: bool,

    /// Dump results to csv files instead of printing to screen.
    #[clap(long = "dump-to-csv")]
    dump_to_csv: bool,

    /// The proof files on which the benchmark will be run. If a directory is passed, the checker
    /// will recursively find all proof files in the directory. The problem files will be
    /// inferred from the proof files.
    files: Vec<String>,
}

#[derive(Args)]
struct SliceCommandOption {
    #[clap(flatten)]
    input: Input,

    #[clap(flatten)]
    parsing: ParsingOptions,

    #[clap(flatten)]
    printing: PrintingOptions,

    #[clap(long)]
    from: String,

    #[clap(long, short = 'd')]
    max_distance: Option<usize>,
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
    let colors_enabled = !cli.no_color && std::io::stderr().is_terminal();

    carcara::ast::USE_SHARING_IN_TERM_DISPLAY
        .store(cli.quiet, std::sync::atomic::Ordering::Relaxed);

    logger::init(cli.log_level.into(), colors_enabled);

    if let Command::Check(CheckCommandOptions { checking, .. })
    | Command::Elaborate(ElaborateCommandOptions { checking, .. })
    | Command::Bench(BenchCommandOptions { checking, .. }) = &cli.command
    {
        if checking.skip_unknown_rules {
            log::warn!(
                "the `--skip-unknown-rules` option is deprecated, please use \
                `--ignore-unknown-rules` instead"
            )
        }
        if checking.lia_via_cvc5 {
            log::warn!(
                "the `--lia-via-cvc5` option is deprecated, please use `--lia-solver cvc5` instead"
            )
        }
    }

    let result = match cli.command {
        Command::Parse(options) => parse_command(options),
        Command::Check(options) => {
            match check_command(options) {
                Ok(false) => println!("valid"),
                Ok(true) => println!("holey"),
                Err(e) => {
                    log::error!("{}", e);
                    println!("invalid");
                    std::process::exit(1);
                }
            }
            return;
        }
        Command::Elaborate(options) => elaborate_command(options),
        Command::Bench(options) => bench_command(options),
        Command::Slice(options) => slice_command(options),
    };
    if let Err(e) = result {
        log::error!("{}", e);
        std::process::exit(1);
    }
}

fn get_instance(options: &Input) -> CliResult<(Box<dyn BufRead>, Box<dyn BufRead>)> {
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

fn parse_command(options: ParseCommandOptions) -> CliResult<()> {
    let (problem, proof) = get_instance(&options.input)?;
    let (_, proof, _) = parser::parse_instance(
        problem,
        proof,
        parser::Config {
            apply_function_defs: options.parsing.apply_function_defs,
            expand_lets: options.parsing.expand_let_bindings,
            allow_int_real_subtyping: options.parsing.allow_int_real_subtyping,
            allow_unary_logical_ops: !options.parsing.strict,
        },
    )
    .map_err(carcara::Error::from)?;
    print_proof(&proof.commands, options.printing.use_sharing)?;
    Ok(())
}

fn check_command(options: CheckCommandOptions) -> CliResult<bool> {
    let (problem, proof) = get_instance(&options.input)?;
    let carc_options = build_carcara_options(options.parsing, options.checking, options.stats);
    if options.num_threads == 1 {
        check(problem, proof, carc_options)
    } else {
        check_parallel(
            problem,
            proof,
            carc_options,
            options.num_threads,
            options.stack.stack_size,
        )
    }
    .map_err(Into::into)
}

fn elaborate_command(options: ElaborateCommandOptions) -> CliResult<()> {
    let (problem, proof) = get_instance(&options.input)?;

    let (_, elaborated) = check_and_elaborate(
        problem,
        proof,
        build_carcara_options(options.parsing, options.checking, options.stats),
    )?;
    print_proof(&elaborated.commands, options.printing.use_sharing)?;
    Ok(())
}

fn bench_command(options: BenchCommandOptions) -> CliResult<()> {
    let instances = get_instances_from_paths(options.files.iter().map(|s| s.as_str()))?;
    if instances.is_empty() {
        log::warn!("no files passed");
        return Ok(());
    }

    log::info!(
        "running benchmark on {} files, doing {} runs each",
        instances.len(),
        options.num_runs
    );

    let carc_options = build_carcara_options(
        options.parsing,
        options.checking,
        StatsOptions { stats: false },
    );
    if options.dump_to_csv {
        benchmarking::run_csv_benchmark(
            &instances,
            options.num_runs,
            options.num_jobs,
            &carc_options,
            options.elaborate,
            &mut File::create("runs.csv")?,
            &mut File::create("by-rule.csv")?,
        )?;
        return Ok(());
    }

    let results: OnlineBenchmarkResults = benchmarking::run_benchmark(
        &instances,
        options.num_runs,
        options.num_jobs,
        &carc_options,
        options.elaborate,
    );
    if results.is_empty() {
        println!("no benchmark data collected");
        return Ok(());
    }

    if results.had_error {
        println!("invalid");
    } else if results.is_holey {
        println!("holey");
    } else {
        println!("valid");
    }
    results.print(options.sort_by_total);
    Ok(())
}

fn slice_command(options: SliceCommandOption) -> CliResult<()> {
    let (problem, proof) = get_instance(&options.input)?;
    let config = parser::Config {
        apply_function_defs: options.parsing.apply_function_defs,
        expand_lets: options.parsing.expand_let_bindings,
        allow_int_real_subtyping: options.parsing.allow_int_real_subtyping,
        allow_unary_logical_ops: !options.parsing.strict,
    };
    let (_, proof, _) =
        parser::parse_instance(problem, proof, config).map_err(carcara::Error::from)?;

    let source_index = proof
        .commands
        .iter()
        .position(|c| c.id() == options.from)
        .ok_or_else(|| CliError::InvalidSliceId(options.from.to_owned()))?;

    let diff =
        carcara::elaborator::slice_proof(&proof.commands, source_index, options.max_distance);
    let slice = carcara::elaborator::apply_diff(diff, proof.commands);
    print_proof(&slice, options.printing.use_sharing)?;
    Ok(())
}
