use carcara::{
    checker, elaborator,
    external::{ExternalTool, SatTools},
    parser,
};
use clap::{Args, Parser, Subcommand, ValueEnum};
use std::{error::Error, num::NonZero, path::PathBuf};

const VERSION_STRING: &str = carcara_macros::version_string!();

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
    max_term_width = 120,
)]
pub struct Cli {
    #[clap(subcommand)]
    pub command: Command,

    /// Sets the maximum logging level.
    #[clap(
        value_enum,
        global = true,
        long = "log",
        default_value_t = LogLevel::Warn,
        help_heading = "Global options"
    )]
    pub log_level: LogLevel,

    /// Disables output coloring.
    #[clap(global = true, long, help_heading = "Global options")]
    pub no_color: bool,

    /// Don't use sharing when printing terms.
    #[clap(global = true, short = 'v', long, help_heading = "Global options")]
    pub no_print_with_sharing: bool,

    /// Print term diffs on error.
    #[clap(global = true, long = "diff", help_heading = "Global options")]
    pub print_diffs: bool,
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
    ///
    /// Each instance is written to a file named `<PROOF_FILE>-<step id>.lia_smt2`.
    GenerateLiaProblems(ParseCommandOptions),

    /// Translates an Alethe proof into Eunoia.
    Translate(TranslateCommandOptions),

    /// Compares two terms and prints a readable diff.
    Diff(DiffCommandOptions),
}

#[derive(Args)]
pub struct Input {
    /// The Alethe proof file. If this is `-`, the proof is read from stdin.
    pub proof_file: PathBuf,

    /// The original SMT-LIB problem file. If this argument is not present, it will be inferred from
    /// the proof file.
    pub problem_file: Option<PathBuf>,

    /// A file containing a set of Rare rewrite rules, that will be used when checking or
    /// elaborating the proof.
    #[clap(long)]
    pub rare_file: Option<PathBuf>,
}

#[derive(Args)]
pub struct StatsOptions {
    /// Enables the gathering of performance statistics
    #[clap(long)]
    pub stats: bool,
}

#[derive(Args)]
pub struct StackOptions {
    /// Defines the thread stack size for each check worker (does not include the main thread stack
    /// size, which should be set manually).
    ///
    /// If not provided, the platform's default stack size is used.
    #[clap(long)]
    pub stack_size: Option<usize>,
}

#[derive(Args, Clone)]
pub struct ToolOptions {
    /// SAT solver that can be used when checking or elaborating proofs.
    #[clap(long, help_heading = "External tool options")]
    pub sat_solver: Option<ExternalTool>,

    /// DRAT checker and trimmer that can be used when checking or elaborating proofs.
    #[clap(long, help_heading = "External tool options")]
    pub drat_checker: Option<ExternalTool>,

    /// SMT solver that can be used when checking or elaborating proof steps.
    #[clap(long, help_heading = "External tool options")]
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

    /// Allows indexed operators to be used in "higher-order" fashion.
    ///
    /// That is, in addition to the usual syntax `((_ <op> <op_args>...) <args>...)`, Carcara will
    /// also accept `(<op> <op_args>... <args>...)`.
    #[clap(long)]
    pub allow_higher_order_indexed_ops: bool,

    /// Enables strict parsing.
    ///
    /// When this flag is enabled:
    /// - unary `and`, `or` and `xor` terms are not allowed
    /// - anchor arguments using the old syntax (i.e., `(:= <symbol> <term>)`) are not allowed; the new syntax (`(:= (<symbol> <sort>) <term>)`) must be used instead
    #[clap(short, long = "strict-parsing", verbatim_doc_comment)]
    pub strict: bool,

    /// If this flag is present, Carcara will parse arguments to the `hole` rule, expecting them to
    /// be valid terms.
    #[clap(long)]
    pub parse_hole_args: bool,

    /// Enables parsing of the old (SMT-LIB versions < 2.6) syntax for datatype testers, namely
    /// `is-cons` instead of `(_ is cons)`.
    #[clap(long)]
    pub allow_legacy_tester_syntax: bool,
}

#[derive(ValueEnum, Clone, Copy, PartialEq, Eq)]
pub enum CheckGranularity {
    Normal,
    Elaborated,
}

#[derive(Args, Clone)]
pub struct CheckingOptions {
    /// Allow steps with rules that are not known by the checker, and consider them as holes.
    #[clap(short, long)]
    pub ignore_unknown_rules: bool,

    /// A set of extra rules to be allowed by the checker.
    ///
    /// Steps that use these rules will not make the proof holey.
    #[clap(long, num_args = 1..)]
    pub allowed_rules: Option<Vec<String>>,

    /// Check resolution steps using only Reverse Unit Propagation (RUP), instead of first trying a
    /// greedy algorithm.
    #[clap(long)]
    pub rup_resolution: bool,

    // This help message uses a markdown list, which requires `verbatim_doc_comment` to render
    // properly. In turn, this messes up Clap's automatic line wrapping, since it considers the line
    // breaks in the comment verbatim. Because of that, we don't wrap the paragraph text and have a
    // super long line instead. It's stupid, but it's the best way I found to resolve this.
    /// Enforce restrictions on the granularity of the proof.
    ///
    /// If this is "normal", the proof is checked normally, with no extra restrictions. If this is "elaborated", the checker will expect the proof to have previously been elaborated by Carcara, and will enforce extra restrictions. In particular:
    /// - the implicit reordering of equalities is not allowed
    /// - the pivots for `resolution` steps must be given as arguments
    #[clap(value_enum, long, default_value = "normal", verbatim_doc_comment)]
    pub check_granularity: CheckGranularity,

    /// Defines an external checker for a given rule.
    ///
    /// For example, when given `-x frobnicate=frobnicator.sh`, Carcara will use the external
    /// `frobnicator.sh` script to check every occurrence of the `frobnicate` rule. For more
    /// details, see https://ufmg-smite.github.io/carcara/checking/external.html
    #[clap(
        short = 'x',
        value_parser = parse_rule_checkers,
        help_heading = "External tool options",
        value_names = ["RULE=CHECKER"])
    ]
    pub rule_checkers: Vec<(String, ExternalTool)>,

    /// Defines an external checker for the `sat_refutation` rule.
    #[clap(long, help_heading = "External tool options")]
    pub sat_ref_checker: Option<ExternalTool>,
}

#[derive(ValueEnum, Clone)]
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
    /// When uncrowding resolution steps, also reorder premises to further minimize the number of
    /// `contraction` steps added.
    #[clap(long)]
    pub uncrowd_rotate: bool,

    /// The pipeline of elaboration passes to use.
    #[clap(
        value_enum,
        long,
        num_args = 1..,
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

    /// Defines the number of threads for proof checking.
    #[clap(short = 'u', long, required = false, default_value = "1")]
    pub num_threads: NonZero<usize>,

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
    #[clap(short, long, default_value = "1")]
    pub num_runs: NonZero<usize>,

    /// Number of jobs to run simultaneously when running the benchmark.
    #[clap(short = 'j', long, default_value = "1")]
    pub num_jobs: NonZero<usize>,

    /// Show benchmark results sorted by total time taken, instead of by average time taken.
    #[clap(short = 't', long)]
    pub sort_by_total: bool,

    /// Dump results to the `runs.csv` and `steps.csv` files in the current directory, instead of
    /// printing to screen.
    #[clap(long = "dump-to-csv")]
    pub dump_to_csv: bool,

    /// The proof files on which the benchmark will be run. If a directory is passed, the checker
    /// will recursively find all proof files in the directory. The problem files will be
    /// inferred from the proof files.
    pub files: Vec<PathBuf>,
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
    #[clap(short, long, hide = true)]
    ignore_unknown_rules: bool,
    #[clap(long, num_args = 1.., hide = true)]
    allowed_rules: Option<Vec<String>>,
    #[clap(long, hide = true)]
    rup_resolution: bool,
    #[clap(value_enum, long, default_value = "normal", hide = true)]
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

// Translation-related options.
#[derive(ValueEnum, Clone)]
pub enum TranslationTarget {
    // NOTE: currently supporting translation into Eunoia.
    Eunoia,
}

#[derive(Args)]
pub struct TranslateCommandOptions {
    #[clap(value_enum)]
    pub target: TranslationTarget,

    /// When translating into Eunoia, we need to pass a path to the folder
    /// containing the corresponding mechanization.
    #[clap(long)]
    pub eunoia_mech: PathBuf,

    #[clap(flatten)]
    pub input: Input,

    #[clap(flatten)]
    pub parsing: ParsingOptions,
}

#[derive(Args)]
pub struct DiffCommandOptions {
    /// The original SMT-LIB problem file.
    pub problem_file: PathBuf,

    /// A file containing two terms to be diffed.
    pub terms_file: PathBuf,

    #[clap(flatten)]
    pub parsing: ParsingOptions,
}

#[derive(ValueEnum, Clone)]
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
        parser::Config::new()
            .apply_function_defs(self.apply_function_defs)
            .expand_lets(self.expand_let_bindings)
            .allow_int_real_subtyping(self.allow_int_real_subtyping)
            .strict(self.strict)
            .parse_hole_args(self.parse_hole_args)
            .allow_higher_order_indexed_ops(self.allow_higher_order_indexed_ops)
            .implicit_at_sort_alias(false)
            .allow_legacy_tester_syntax(self.allow_legacy_tester_syntax)
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
        checker::Config::new()
            .elaborated(c.check_granularity == CheckGranularity::Elaborated)
            .ignore_unknown_rules(c.ignore_unknown_rules)
            .rup_resolution(c.rup_resolution)
            .allowed_rules(c.allowed_rules.unwrap_or_default())
            .rule_checkers(c.rule_checkers.into_iter().collect())
            .sat_ref_config(sat_ref_config)
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

        let config = elaborator::Config::new()
            .lia_solver(t.smt_solver.clone())
            .uncrowd_rotation(e.uncrowd_rotate)
            .hole_solver(t.smt_solver.clone())
            .sat_ref_tools(t.into_config());
        (config, pipeline)
    }
}
