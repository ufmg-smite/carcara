mod metrics;
#[cfg(test)]
mod tests;

pub use metrics::*;

use ahash::AHashMap;
use std::{fmt, io, time::Duration};

fn combine_map<K, V, M>(mut a: AHashMap<String, M>, b: AHashMap<String, M>) -> AHashMap<String, M>
where
    V: MetricsUnit,
    M: Metrics<K, V> + Default,
{
    use std::collections::hash_map::Entry;
    for (k, v) in b {
        match a.entry(k) {
            Entry::Occupied(mut e) => {
                // To take the old value from the entry without moving it entirely, we have
                // to insert something in its place, so we insert an empty `M`
                let old = e.insert(M::default());
                e.insert(old.combine(v));
            }
            Entry::Vacant(e) => {
                e.insert(v);
            }
        }
    }
    a
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StepId {
    pub(crate) file: Box<str>,
    pub(crate) step_id: Box<str>,
    pub(crate) rule: Box<str>,
}

impl fmt::Display for StepId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{} ({})", self.file, self.step_id, self.rule)
    }
}

type RunId = (String, usize);

#[derive(Debug, Default, Clone)]
pub struct RunMeasurement {
    pub parsing: Duration,
    pub checking: Duration,
    pub elaboration: Duration,
    pub total: Duration,
    pub deep_eq: Duration,
    pub assume: Duration,
    pub assume_core: Duration,
}

// Higher kinded types would be very useful here. Ideally, I would like `BenchmarkResults` to be
// generic on any kind that implements `Metrics`, like `OnlineMetrics` or `OfflineMetrics`.
#[derive(Debug, Default)]
pub struct BenchmarkResults<ByRun, ByStep, ByRunF64, ByDeepEq> {
    pub parsing: ByRun,
    pub checking: ByRun,
    pub elaborating: ByRun,
    pub total_accounted_for: ByRun,
    pub total: ByRun,
    pub step_time: ByStep,
    pub step_time_by_file: AHashMap<String, ByStep>,
    pub step_time_by_rule: AHashMap<String, ByStep>,

    pub deep_eq_time: ByRun,
    pub deep_eq_time_ratio: ByRunF64,
    pub assume_time: ByRun,
    pub assume_time_ratio: ByRunF64,
    pub assume_core_time: ByRun,

    pub deep_eq_depths: ByDeepEq,
    pub num_assumes: usize,
    pub num_easy_assumes: usize,
}

pub type OnlineBenchmarkResults = BenchmarkResults<
    OnlineMetrics<RunId>,
    OnlineMetrics<StepId>,
    OnlineMetrics<RunId, f64>,
    OnlineMetrics<(), usize>,
>;

pub type OfflineBenchmarkResults = BenchmarkResults<
    OfflineMetrics<RunId>,
    OfflineMetrics<StepId>,
    OfflineMetrics<RunId, f64>,
    OfflineMetrics<(), usize>,
>;

impl<ByRun, ByStep, ByRunF64, ByDeepEq> BenchmarkResults<ByRun, ByStep, ByRunF64, ByDeepEq>
where
    ByRun: Metrics<RunId, Duration> + Default,
    ByStep: Metrics<StepId, Duration> + Default,
    ByRunF64: Metrics<RunId, f64> + Default,
    ByDeepEq: Metrics<(), usize> + Default,
{
    pub fn new() -> Self {
        Default::default()
    }

    /// Return `true` if the results have no entries.
    pub fn is_empty(&self) -> bool {
        self.total.is_empty()
    }

    /// The time per run to completely parse the proof.
    pub fn parsing(&self) -> &ByRun {
        &self.parsing
    }

    /// The time per run to check all the steps in the proof.
    pub fn checking(&self) -> &ByRun {
        &self.checking
    }

    /// The time per run to elaborate the proof.
    pub fn elaborating(&self) -> &ByRun {
        &self.elaborating
    }

    /// The combined time per run to parse, check, and elaborate all the steps in the proof.
    pub fn total_accounted_for(&self) -> &ByRun {
        &self.total_accounted_for
    }

    /// The total time spent per run. Should be pretty similar to `total_accounted_for`.
    pub fn total(&self) -> &ByRun {
        &self.total
    }

    /// The time spent checking each step.
    pub fn step_time(&self) -> &ByStep {
        &self.step_time
    }

    /// For each file, the time spent checking each step in the file.
    pub fn step_time_by_file(&self) -> &AHashMap<String, ByStep> {
        &self.step_time_by_file
    }

    /// For each rule, the time spent checking each step that uses that rule.
    pub fn step_time_by_rule(&self) -> &AHashMap<String, ByStep> {
        &self.step_time_by_rule
    }

    /// Prints the benchmark results
    pub fn print(&self, sort_by_total: bool) {
        let [parsing, checking, elaborating, accounted_for, total] = [
            self.parsing(),
            self.checking(),
            self.elaborating(),
            self.total_accounted_for(),
            self.total(),
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
        if !elaborating.is_empty() {
            println!("elaborating:      {}", elaborating);
        }
        println!(
            "on assume:           {} ({:.02}% of checking time)",
            self.assume_time,
            100.0 * self.assume_time.mean().as_secs_f64() / self.checking().mean().as_secs_f64(),
        );
        println!("on assume (core):    {}", self.assume_core_time);
        println!("assume ratio:        {}", self.assume_time_ratio);
        println!(
            "on deep equality:    {} ({:.02}% of checking time)",
            self.deep_eq_time,
            100.0 * self.deep_eq_time.mean().as_secs_f64() / self.checking().mean().as_secs_f64(),
        );
        println!("deep equality ratio: {}", self.deep_eq_time_ratio);
        println!("total accounted for: {}", accounted_for);
        println!("total:               {}", total);

        let data_by_rule = self.step_time_by_rule();
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
        if !self.step_time().is_empty() {
        let worst_step = self.step_time().max();
        println!("    step:            {} ({:?})", worst_step.0, worst_step.1);
        }

        let worst_file_parsing = self.parsing().max();
        println!(
            "    file (parsing):  {} ({:?})",
            worst_file_parsing.0 .0, worst_file_parsing.1
        );

        let worst_file_checking = self.checking().max();
        println!(
            "    file (checking): {} ({:?})",
            worst_file_checking.0 .0, worst_file_checking.1
        );

        let worst_file_assume = self.assume_time_ratio.max();
        println!(
            "    file (assume):   {} ({:.04}%)",
            worst_file_assume.0 .0,
            worst_file_assume.1 * 100.0
        );

        let worst_file_deep_eq = self.deep_eq_time_ratio.max();
        println!(
            "    file (deep_eq):  {} ({:.04}%)",
            worst_file_deep_eq.0 .0,
            worst_file_deep_eq.1 * 100.0
        );

        let worst_file_total = self.total().max();
        println!(
            "    file overall:    {} ({:?})",
            worst_file_total.0 .0, worst_file_total.1
        );

        let num_hard_assumes = self.num_assumes - self.num_easy_assumes;
        let percent_easy = (self.num_easy_assumes as f64) * 100.0 / (self.num_assumes as f64);
        let percent_hard = (num_hard_assumes as f64) * 100.0 / (self.num_assumes as f64);
        println!("          number of assumes: {}", self.num_assumes);
        println!(
            "                     (easy): {} ({:.02}%)",
            self.num_easy_assumes, percent_easy
        );
        println!(
            "                     (hard): {} ({:.02}%)",
            num_hard_assumes, percent_hard
        );

        let depths = &self.deep_eq_depths;
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
    }
}

#[derive(Default)]
pub struct CsvBenchmarkResults {
    runs: AHashMap<RunId, RunMeasurement>,
    step_time_by_rule: AHashMap<String, OfflineMetrics<StepId>>,
    num_errors: usize,
}

impl CsvBenchmarkResults {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn num_errors(&self) -> usize {
        self.num_errors
    }

    pub fn write_csv(
        self,
        runs_dest: &mut dyn io::Write,
        by_rule_dest: &mut dyn io::Write,
    ) -> io::Result<()> {
        Self::write_runs_csv(self.runs, runs_dest)?;
        Self::write_by_rule_csv(self.step_time_by_rule, by_rule_dest)
    }

    fn write_runs_csv(
        data: AHashMap<RunId, RunMeasurement>,
        dest: &mut dyn io::Write,
    ) -> io::Result<()> {
        writeln!(
            dest,
            "proof_file,run_id,parsing,checking,elaboration,total_accounted_for,\
            total,deep_eq,deep_eq_ratio,assume,assume_ratio"
        )?;

        for (id, m) in data {
            let total_accounted_for = m.parsing + m.checking;
            let deep_eq_ratio = m.deep_eq.as_secs_f64() / m.checking.as_secs_f64();
            let assume_ratio = m.assume.as_secs_f64() / m.checking.as_secs_f64();
            writeln!(
                dest,
                "{},{},{},{},{},{},{},{},{},{},{}",
                id.0,
                id.1,
                m.parsing.as_nanos(),
                m.checking.as_nanos(),
                m.elaboration.as_nanos(),
                total_accounted_for.as_nanos(),
                m.total.as_nanos(),
                m.deep_eq.as_nanos(),
                deep_eq_ratio,
                m.assume.as_nanos(),
                assume_ratio,
            )?;
        }

        Ok(())
    }

    fn write_by_rule_csv(
        data: AHashMap<String, OfflineMetrics<StepId>>,
        dest: &mut dyn io::Write,
    ) -> io::Result<()> {
        let mut data: Vec<_> = data.into_iter().collect();
        data.sort_unstable_by_key(|m| m.1.total());

        writeln!(
            dest,
            "rule,count,total,mean,lower_whisker,first_quartile,median,third_quartile,upper_whisker"
        )?;
        for (rule, mut m) in data {
            let [lower_whisker, first_quartile, median, third_quartile, upper_whisker] =
                m.quartiles().map(|(_, t)| t.as_nanos());
            writeln!(
                dest,
                "{},{},{},{},{},{},{},{},{}",
                rule,
                m.count(),
                m.total().as_nanos(),
                m.mean().as_nanos(),
                lower_whisker,
                first_quartile,
                median,
                third_quartile,
                upper_whisker,
            )?;
        }
        Ok(())
    }
}

pub trait CollectResults {
    fn new() -> Self;
    fn add_step_measurement(&mut self, file: &str, step_id: &str, rule: &str, time: Duration);
    fn add_assume_measurement(&mut self, file: &str, id: &str, is_easy: bool, time: Duration);
    fn add_deep_eq_depth(&mut self, depth: usize);
    fn add_run_measurement(&mut self, id: &RunId, measurement: RunMeasurement);
    fn register_error(&mut self, error: &crate::Error);

    fn combine(a: Self, b: Self) -> Self
    where
        Self: Sized;

    fn copy_from(&mut self, other: &Self)
    where
        Self: Sized;
}

impl<ByRun, ByStep, ByRunF64, ByDeepEq> CollectResults
    for BenchmarkResults<ByRun, ByStep, ByRunF64, ByDeepEq>
where
    ByRun: Metrics<RunId, Duration> + Default + Clone,
    ByStep: Metrics<StepId, Duration> + Default + Clone,
    ByRunF64: Metrics<RunId, f64> + Default + Clone,
    ByDeepEq: Metrics<(), usize> + Default + Clone,
{
    fn new() -> Self {
        Default::default()
    }

    fn add_step_measurement(&mut self, file: &str, step_id: &str, rule: &str, time: Duration) {
        let file = file.to_owned();
        let rule = rule.to_owned();
        let id = StepId {
            file: file.clone().into_boxed_str(),
            step_id: step_id.into(),
            rule: rule.clone().into_boxed_str(),
        };
        self.step_time.add_sample(&id, time);
        self.step_time_by_file
            .entry(file)
            .or_default()
            .add_sample(&id, time);
        self.step_time_by_rule
            .entry(rule)
            .or_default()
            .add_sample(&id, time);
    }

    fn add_assume_measurement(&mut self, file: &str, id: &str, is_easy: bool, time: Duration) {
        self.num_assumes += 1;
        self.num_easy_assumes += is_easy as usize;
        self.add_step_measurement(file, id, "assume", time);
    }

    fn add_deep_eq_depth(&mut self, depth: usize) {
        self.deep_eq_depths.add_sample(&(), depth);
    }

    fn add_run_measurement(&mut self, id: &RunId, measurement: RunMeasurement) {
        let RunMeasurement {
            parsing,
            checking,
            elaboration,
            total,
            deep_eq,
            assume,
            assume_core,
        } = measurement;

        self.parsing.add_sample(id, parsing);
        self.checking.add_sample(id, checking);
        self.elaborating.add_sample(id, elaboration);
        self.total_accounted_for.add_sample(id, parsing + checking);
        self.total.add_sample(id, total);

        self.deep_eq_time.add_sample(id, deep_eq);
        self.assume_time.add_sample(id, assume);
        self.assume_core_time.add_sample(id, assume_core);

        let deep_eq_ratio = deep_eq.as_secs_f64() / checking.as_secs_f64();
        let assume_ratio = assume.as_secs_f64() / checking.as_secs_f64();
        self.deep_eq_time_ratio.add_sample(id, deep_eq_ratio);
        self.assume_time_ratio.add_sample(id, assume_ratio);
    }

    fn combine(a: Self, b: Self) -> Self {
        Self {
            parsing: a.parsing.combine(b.parsing),
            checking: a.checking.combine(b.checking),
            elaborating: a.elaborating.combine(b.elaborating),
            total_accounted_for: a.total_accounted_for.combine(b.total_accounted_for),
            total: a.total.combine(b.total),
            step_time: a.step_time.combine(b.step_time),
            step_time_by_file: combine_map(a.step_time_by_file, b.step_time_by_file),
            step_time_by_rule: combine_map(a.step_time_by_rule, b.step_time_by_rule),

            deep_eq_time: a.deep_eq_time.combine(b.deep_eq_time),
            deep_eq_time_ratio: a.deep_eq_time_ratio.combine(b.deep_eq_time_ratio),
            assume_time: a.assume_time.combine(b.assume_time),
            assume_time_ratio: a.assume_time_ratio.combine(b.assume_time_ratio),
            assume_core_time: a.assume_core_time.combine(b.assume_core_time),

            deep_eq_depths: a.deep_eq_depths.combine(b.deep_eq_depths),
            num_assumes: a.num_assumes + b.num_assumes,
            num_easy_assumes: a.num_easy_assumes + b.num_easy_assumes,
        }
    }

    fn copy_from(&mut self, other: &Self)
    where
        Self: Sized,
    {
        self.parsing = other.parsing.clone();
        self.checking = other.checking.clone();
        self.elaborating = other.elaborating.clone();
        self.total_accounted_for = other.total_accounted_for.clone();
        self.total = other.total.clone();
        self.step_time = other.step_time.clone();
        self.step_time_by_file = other.step_time_by_file.clone();
        self.step_time_by_rule = other.step_time_by_rule.clone();

        self.deep_eq_time = other.deep_eq_time.clone();
        self.deep_eq_time_ratio = other.deep_eq_time_ratio.clone();
        self.assume_time = other.assume_time.clone();
        self.assume_time_ratio = other.assume_time_ratio.clone();
        self.assume_core_time = other.assume_core_time.clone();

        self.deep_eq_depths = other.deep_eq_depths.clone();
        self.num_assumes = other.num_assumes.clone();
        self.num_easy_assumes = other.num_easy_assumes.clone();
    }

    fn register_error(&mut self, _: &crate::Error) {}
}

impl CollectResults for CsvBenchmarkResults {
    fn new() -> Self {
        Default::default()
    }

    fn add_step_measurement(&mut self, file: &str, step_id: &str, rule: &str, time: Duration) {
        let id = StepId {
            file: file.into(),
            step_id: step_id.into(),
            rule: rule.into(),
        };
        self.step_time_by_rule
            .entry(rule.to_owned())
            .or_default()
            .add_sample(&id, time);
    }

    fn add_assume_measurement(&mut self, file: &str, id: &str, _: bool, time: Duration) {
        self.add_step_measurement(file, id, "assume", time);
    }

    fn add_deep_eq_depth(&mut self, _: usize) {}

    fn add_run_measurement(&mut self, id: &RunId, measurement: RunMeasurement) {
        self.runs.insert(id.clone(), measurement);
    }

    fn combine(mut a: Self, b: Self) -> Self {
        // This assumes that the same run never appears in both `a` and `b`. This should be the case
        // in benchmarks anyway
        a.runs.extend(b.runs);
        a.step_time_by_rule = combine_map(a.step_time_by_rule, b.step_time_by_rule);
        a.num_errors += b.num_errors;
        a
    }

    fn register_error(&mut self, _: &crate::Error) {
        self.num_errors += 1;
    }

    fn copy_from(&mut self, other: &Self)
    where
        Self: Sized,
    {
        self.runs = other.runs.clone();
        self.step_time_by_rule = other.step_time_by_rule.clone();
        self.num_errors = other.num_errors;
    }
}
