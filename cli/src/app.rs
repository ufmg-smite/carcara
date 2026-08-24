use carcara::{
    checker, elaborator,
    external::{ExternalTool, SatTools},
    parser,
    rare::engine::RunEgglogOptions,
};
use clap::{AppSettings, ArgEnum, Args, Parser, Subcommand};
use const_format::{formatcp, str_index};
use git_version::git_version;
use std::{error::Error, time::Duration};

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

/// Parse a single key-value pair
fn parse_rule_checkers(
    s: &str,
) -> Result<(String, ExternalTool), Box<dyn Error + Send + Sync + 'static>> {
    let (rule, checker) = s
        .split_once("=")
        .ok_or_else(|| format!("invalid KEY=value: no `=` found in `{s}`"))?;
    Ok((rule.parse()?, checker.parse()?))
}

#[derive(Parser)]
#[clap(
    name = "carcara",
    version = VERSION_STRING,
    setting = AppSettings::DeriveDisplayOrder
)]
pub struct Cli {
    #[clap(subcommand)]
    pub command: Command,

    /// Sets the maximum logging level.
    #[clap(arg_enum, global = true, long = "log", default_value_t = LogLevel::Warn)]
    pub log_level: LogLevel,

    /// Disables output coloring.
    #[clap(global = true, long)]
    pub no_color: bool,

    /// Don't use sharing when printing terms.
    #[clap(global = true, short = 'v', long)]
    pub no_print_with_sharing: bool,
}

#[derive(Subcommand)]
pub enum Command {
    /// Parses a proof file and prints it back.
    Parse(ParseCommandOptions),

    /// Checks a proof file.
    Check(CheckCommandOptions),

    /// Checks and elaborates a proof file.
    Elaborate(ElaborateCommandOptions),

    /// Checks a series of proof files and records performance statistics.
    Bench(BenchCommandOptions),

    /// Given a step, takes a slice of a proof consisting of its transitive premises.
    Slice(SliceCommandOptions),

    /// Generates the equivalent SMT instance for every `lia_generic` step in a proof.
    GenerateLiaProblems(ParseCommandOptions),
}

#[derive(Args)]
pub struct Input {
    /// The proof file to be checked
    pub proof_file: String,

    /// The original problem file. If this argument is not present, it will be inferred from the
    /// proof file.
    pub problem_file: Option<String>,

    #[clap(long)]
    pub rare_file: Option<String>,
}

#[derive(Args)]
pub struct StatsOptions {
    /// Enables the gathering of performance statistics
    #[clap(long)]
    pub stats: bool,
}

#[derive(Args)]
pub struct StackOptions {
    /// Defines the thread stack size for each check worker (does not include the main thread stack size, which should be set manually).
    #[clap(long, default_value = "0")]
    pub stack_size: usize,
}

#[derive(Args, Clone)]
pub struct ToolOptions {
    /// SAT solver that can be used when checking or elaborating proofs.
    #[clap(long, help_heading = "EXTERNAL TOOL OPTIONS")]
    pub sat_solver: Option<ExternalTool>,

    /// DRAT checker and trimmer that can be used when checking or elaborating proofs.
    #[clap(long, help_heading = "EXTERNAL TOOL OPTIONS")]
    pub drat_checker: Option<ExternalTool>,

    /// SMT solver that can be used when checking or elaborating proof steps.
    #[clap(long, help_heading = "EXTERNAL TOOL OPTIONS")]
    pub smt_solver: Option<ExternalTool>,
}

#[derive(Args, Clone, Copy)]
pub struct ParsingOptions {
    /// Expand function definitions introduced by `define-fun`s in the SMT problem. If this flag is
    /// not present, they are instead interpreted as a function declaration and an `assert` that
    /// defines the function name to be equal to its body. Function definitions in the proof itself
    /// are always expanded.
    #[clap(long)]
    pub apply_function_defs: bool,

    /// Eliminates `let` bindings from terms when parsing.
    #[clap(long)]
    pub expand_let_bindings: bool,

    /// Enables `Int`/`Real` subtyping in the parser. This allows terms of sort `Int` to be passed
    /// to arithmetic operators that are expecting a term of sort `Real`.
    #[clap(long)]
    pub allow_int_real_subtyping: bool,

    /// Enables strict parsing.
    ///
    /// When this flag is enabled: unary `and`, `or` and `xor` terms are not allowed;
    #[clap(short, long = "strict-parsing")]
    pub strict: bool,

    /// If `true`, Carcara will parse arguments to the `hole` rule, expecting them to be valid
    /// terms. In the future, this will be the default behaviour.
    #[clap(long)]
    pub parse_hole_args: bool,

    /// Buffer the entire file in memory before parsing instead of reading line-by-line.
    /// This can improve performance in network file systems or cluster environments
    /// at the cost of increased memory usage.
    #[clap(long)]
    pub buffer_entire_file: bool,
}

#[derive(ArgEnum, Clone, Copy, PartialEq, Eq)]
pub enum CheckGranularity {
    Normal,
    Elaborated,
}

#[derive(Args, Clone)]
pub struct CheckingOptions {
    /// Allow steps with rules that are not known by the checker, and consider them as holes.
    #[clap(short, long)]
    pub ignore_unknown_rules: bool,

    /// A set of extra rules to be allowed by the checker, and considered as holes.
    #[clap(long, multiple = true)]
    pub allowed_rules: Option<Vec<String>>,

    /// Check resolution steps using only Reverse Unit Propagation (RUP), instead of first trying a
    /// greedy algorithm.
    #[clap(long)]
    pub rup_resolution: bool,

    /// Enforce restrictions on the granularity of the proof.
    ///
    /// If this is "normal", the proof is checked normally, with no extra restrictions. If this
    /// is "elaborated", the checker will expect the proof to have previously been elaborated by
    /// Carcara, and will enforce extra restrictions. In particular:
    /// - the implicit reordering of equalities is not allowed
    /// - the pivots for `resolution` steps must be given as arguments
    #[clap(arg_enum, long, default_value = "normal", verbatim_doc_comment)]
    pub check_granularity: CheckGranularity,

    // TODO: add help messages for remaining options
    // number_of_values = 1 forces the user to repeat the -D option for each key-value pair:
    // my_program -D a=1 -D b=2
    // Without number_of_values = 1 you can do:
    // my_program -D a=1 b=2
    // but this makes adding an argument after the values impossible:
    // my_program -D a=1 -D b=2 my_input_file
    // becomes invalid.
    #[clap(short = 'x', value_parser = parse_rule_checkers, help_heading = "EXTERNAL TOOL OPTIONS")]
    pub rule_checkers: Vec<(String, ExternalTool)>,

    #[clap(long, help_heading = "EXTERNAL TOOL OPTIONS")]
    pub sat_ref_checker: Option<ExternalTool>,

    /// Validate `hole` steps marked as `TRUST_THEORY_REWRITE` using RARE and egglog.
    #[clap(long)]
    pub check_hole_rewrites: bool,

    /// Print the egglog program generated for each checked hole rewrite.
    #[clap(long, requires = "check-hole-rewrites")]
    pub print_egglog: bool,

    /// Keep running RARE egglog schedules one step at a time until goals are saturated.
    #[clap(long = "continous-saturation", requires = "check-hole-rewrites")]
    pub continous_saturation: bool,

    /// Cooperative time budget in milliseconds for each RARE hole rewrite. The budget is checked
    /// between egglog rule iterations.
    #[clap(long, requires = "check-hole-rewrites", value_name = "MILLISECONDS")]
    pub rare_check_timeout: Option<u64>,
}

#[derive(ArgEnum, Clone)]
pub enum ElaborationPass {
    Polyeq,
    Hole,
    Local,
    Uncrowd,
    Reordering,
    SatRefutation,
}

#[derive(Args, Clone)]
pub struct ElaborationOptions {
    /// When uncrowding resolutions steps, also reorder premises to further minimize the number of
    /// `contraction` steps added.
    #[clap(long)]
    pub uncrowd_rotate: bool,

    /// The pipeline of elaboration passes to use.
    #[clap(
        arg_enum,
        long,
        multiple = true,
        default_values = &["polyeq", "hole", "local", "uncrowd", "reordering"]
    )]
    pub pipeline: Vec<ElaborationPass>,
}

#[derive(Args)]
pub struct ParseCommandOptions {
    #[clap(flatten)]
    pub input: Input,

    #[clap(flatten)]
    pub parsing: ParsingOptions,
}

#[derive(Args)]
pub struct CheckCommandOptions {
    #[clap(flatten)]
    pub input: Input,

    #[clap(flatten)]
    pub parsing: ParsingOptions,

    #[clap(flatten)]
    pub checking: CheckingOptions,

    #[clap(flatten)]
    pub tools: ToolOptions,

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
    pub num_threads: usize,

    #[clap(flatten)]
    pub stats: StatsOptions,

    #[clap(flatten)]
    pub stack: StackOptions,
}

#[derive(Args)]
pub struct ElaborateCommandOptions {
    #[clap(flatten)]
    pub input: Input,

    #[clap(flatten)]
    pub parsing: ParsingOptions,

    #[clap(flatten)]
    pub checking: CheckingOptions,

    #[clap(flatten)]
    pub elaboration: ElaborationOptions,

    #[clap(flatten)]
    pub tools: ToolOptions,

    #[clap(flatten)]
    pub stats: StatsOptions,
}

#[derive(Args)]
pub struct BenchCommandOptions {
    #[clap(flatten)]
    pub parsing: ParsingOptions,

    #[clap(flatten)]
    pub checking: CheckingOptions,

    /// Also elaborate each proof in addition to parsing and checking.
    #[clap(long)]
    pub elaborate: bool,

    #[clap(flatten)]
    pub elaboration: ElaborationOptions,

    #[clap(flatten)]
    pub tools: ToolOptions,

    /// Number of times to run the benchmark for each file.
    #[clap(short, long, default_value_t = 1)]
    pub num_runs: usize,

    /// Number of jobs to run simultaneously when running the benchmark.
    #[clap(short = 'j', long, default_value_t = 1)]
    pub num_jobs: usize,

    /// Show benchmark results sorted by total time taken, instead of by average time taken.
    #[clap(short = 't', long)]
    pub sort_by_total: bool,

    /// Dump results to csv files instead of printing to screen.
    #[clap(long = "dump-to-csv")]
    pub dump_to_csv: bool,

    /// The proof files on which the benchmark will be run. If a directory is passed, the checker
    /// will recursively find all proof files in the directory. The problem files will be
    /// inferred from the proof files.
    pub files: Vec<String>,
}

#[derive(Args)]
pub struct SliceCommandOptions {
    #[clap(flatten)]
    pub input: Input,

    /// If provided, write the sliced problem and proof to these files.
    #[clap(long, value_names = &["SLICED_PROBLEM", "SLICED_PROOF"])]
    pub sliced_output: Option<Vec<String>>,

    #[clap(flatten)]
    pub parsing: ParsingOptions,

    /// The id of the step which will be the root of the slice.
    #[clap(long)]
    pub from: String,

    /// How many layers of transitive premises to include beyond the direct premises of the step
    /// being sliced. If this argument is not present, it will default to zero.
    #[clap(long, short = 'd')]
    pub max_distance: Option<usize>,

    // To make slice more convenient to use, we accept (and ignore!) some options from the `check`
    // subcommand
    #[clap(short, long)]
    ignore_unknown_rules: bool,
    #[clap(long, multiple = true, hide = true)]
    allowed_rules: Option<Vec<String>>,
    #[clap(long, hide = true)]
    rup_resolution: bool,
    #[clap(arg_enum, long, default_value = "normal", hide = true)]
    check_granularity: CheckGranularity,
    #[clap(short = 'x', value_parser = parse_rule_checkers, hide = true)]
    rule_checkers: Vec<(String, ExternalTool)>,
    #[clap(long, hide = true)]
    sat_ref_checker: Option<ExternalTool>,
    #[clap(long, hide = true)]
    sat_solver: Option<ExternalTool>,
    #[clap(long, hide = true)]
    drat_checker: Option<ExternalTool>,
    #[clap(long, hide = true)]
    smt_solver: Option<ExternalTool>,
    #[clap(long, hide = true)]
    stats: bool,
    #[clap(long, default_value = "0", hide = true)]
    stack_size: usize,
}

#[derive(ArgEnum, Clone)]
pub enum LogLevel {
    Off,
    Error,
    Warn,
    Info,
    Debug,
}

impl From<LogLevel> for log::LevelFilter {
    fn from(l: LogLevel) -> Self {
        match l {
            LogLevel::Off => Self::Off,
            LogLevel::Error => Self::Error,
            LogLevel::Warn => Self::Warn,
            LogLevel::Info => Self::Info,
            LogLevel::Debug => Self::Debug,
        }
    }
}

// Due to the orphan rule with tuples, we can't use the standard `From`/`Into` traits for this
pub trait IntoConfig {
    type Output;

    fn into_config(self) -> Self::Output;
}

impl IntoConfig for ToolOptions {
    type Output = Option<SatTools>;

    fn into_config(self) -> Self::Output {
        Some(SatTools {
            sat_solver: self.sat_solver?,
            drat_checker: self.drat_checker?,
            smt_solver: self.smt_solver?,
        })
    }
}

impl IntoConfig for ParsingOptions {
    type Output = parser::Config;

    fn into_config(self) -> Self::Output {
        parser::Config {
            apply_function_defs: self.apply_function_defs,
            expand_lets: self.expand_let_bindings,
            allow_int_real_subtyping: self.allow_int_real_subtyping,
            strict: self.strict,
            parse_hole_args: self.parse_hole_args,
        }
    }
}

impl IntoConfig for (CheckingOptions, ToolOptions) {
    type Output = checker::Config;

    fn into_config(self) -> Self::Output {
        let (c, t) = self;
        let sat_ref_config = if let Some(checker) = c.sat_ref_checker {
            // TODO: add warning for when both are passed?
            checker::SatRefConfig::Dedicated(checker)
        } else if let Some(sat_tools) = t.into_config() {
            checker::SatRefConfig::Sat(sat_tools)
        } else {
            checker::SatRefConfig::None
        };
        checker::Config {
            elaborated: c.check_granularity == CheckGranularity::Elaborated,
            ignore_unknown_rules: c.ignore_unknown_rules,
            allowed_rules: c.allowed_rules.unwrap_or_default().into_iter().collect(),
            rup_resolution: c.rup_resolution,
            rule_checkers: c.rule_checkers.into_iter().collect(),
            sat_ref_config,
            check_hole_rewrites: c.check_hole_rewrites,
            hole_rewrite_options: RunEgglogOptions {
                continuous_saturation: c.continous_saturation,
                timeout: c.rare_check_timeout.map(Duration::from_millis),
                print_egglog: c.print_egglog,
                ..RunEgglogOptions::default()
            },
        }
    }
}

impl IntoConfig for (ElaborationOptions, ToolOptions) {
    type Output = (elaborator::Config, Vec<elaborator::ElaborationPass>);

    fn into_config(self) -> Self::Output {
        let (e, t) = self;
        let pipeline: Vec<_> = e
            .pipeline
            .into_iter()
            .map(|p| match p {
                ElaborationPass::Polyeq => elaborator::ElaborationPass::Polyeq,
                ElaborationPass::Hole => elaborator::ElaborationPass::Hole,
                ElaborationPass::Local => elaborator::ElaborationPass::Local,
                ElaborationPass::Uncrowd => elaborator::ElaborationPass::Uncrowd,
                ElaborationPass::Reordering => elaborator::ElaborationPass::Reordering,
                ElaborationPass::SatRefutation => elaborator::ElaborationPass::SatRefutation,
            })
            .collect();

        let config = elaborator::Config {
            lia_solver: t.smt_solver.clone(),
            uncrowd_rotation: e.uncrowd_rotate,
            hole_solver: t.smt_solver.clone(),
            sat_ref_tools: t.into_config(),
        };
        (config, pipeline)
    }
}
