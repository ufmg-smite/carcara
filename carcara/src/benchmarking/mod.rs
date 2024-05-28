mod metrics;
#[cfg(test)]
mod tests;

pub use metrics::*;

use indexmap::{map::Entry, IndexMap, IndexSet};
use std::{fmt, hash::Hash, io, sync::Arc, time::Duration};

fn combine_map<S, K, V, M>(mut a: IndexMap<S, M>, b: IndexMap<S, M>) -> IndexMap<S, M>
where
    S: Eq + Hash,
    V: MetricsUnit,
    M: Metrics<K, V> + Default,
{
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

#[derive(Debug, Default)]
pub struct RunMeasurement {
    pub parsing: Duration,
    pub checking: Duration,
    pub elaboration: Duration,
    pub scheduling: Duration,
    pub total: Duration,
    pub polyeq: Duration,
    pub assume: Duration,
    pub assume_core: Duration,
}

#[derive(Debug, Default, Clone)]
pub struct OnlineBenchmarkResults {
    pub parsing: OnlineMetrics<RunId>,
    pub checking: OnlineMetrics<RunId>,
    pub elaborating: OnlineMetrics<RunId>,
    pub scheduling: OnlineMetrics<RunId>,
    pub total_accounted_for: OnlineMetrics<RunId>,
    pub total: OnlineMetrics<RunId>,
    pub step_time: OnlineMetrics<StepId>,
    pub step_time_by_file: IndexMap<String, OnlineMetrics<StepId>>,
    pub step_time_by_rule: IndexMap<String, OnlineMetrics<StepId>>,

    pub polyeq_time: OnlineMetrics<RunId>,
    pub polyeq_time_ratio: OnlineMetrics<RunId, f64>,
    pub assume_time: OnlineMetrics<RunId>,
    pub assume_time_ratio: OnlineMetrics<RunId, f64>,
    pub assume_core_time: OnlineMetrics<RunId>,

    pub polyeq_depths: OnlineMetrics<(), usize>,
    pub num_assumes: usize,
    pub num_easy_assumes: usize,

    pub is_holey: bool,
    pub had_error: bool,
}

impl OnlineBenchmarkResults {
    pub fn new() -> Self {
        Default::default()
    }

    /// Return `true` if the results have no entries.
    pub fn is_empty(&self) -> bool {
        self.total.is_empty()
    }

    /// The time per run to completely parse the proof.
    pub fn parsing(&self) -> &OnlineMetrics<RunId> {
        &self.parsing
    }

    /// The time per run to check all the steps in the proof.
    pub fn checking(&self) -> &OnlineMetrics<RunId> {
        &self.checking
    }

    /// The time per run to elaborate the proof.
    pub fn elaborating(&self) -> &OnlineMetrics<RunId> {
        &self.elaborating
    }

    /// The time per run to schedule the threads tasks.
    pub fn scheduling(&self) -> &OnlineMetrics<RunId> {
        &self.scheduling
    }

    /// The combined time per run to parse, check, and elaborate all the steps in the proof.
    pub fn total_accounted_for(&self) -> &OnlineMetrics<RunId> {
        &self.total_accounted_for
    }

    /// The total time spent per run. Should be pretty similar to `total_accounted_for`.
    pub fn total(&self) -> &OnlineMetrics<RunId> {
        &self.total
    }

    /// The time spent checking each step.
    pub fn step_time(&self) -> &OnlineMetrics<StepId> {
        &self.step_time
    }

    /// For each file, the time spent checking each step in the file.
    pub fn step_time_by_file(&self) -> &IndexMap<String, OnlineMetrics<StepId>> {
        &self.step_time_by_file
    }

    /// For each rule, the time spent checking each step that uses that rule.
    pub fn step_time_by_rule(&self) -> &IndexMap<String, OnlineMetrics<StepId>> {
        &self.step_time_by_rule
    }

    /// Prints the benchmark results
    pub fn print(&self, sort_by_total: bool) {
        let [parsing, checking, elaborating, scheduling, accounted_for, total, assume_time, assume_core_time, polyeq_time] =
            [
                self.parsing(),
                self.checking(),
                self.elaborating(),
                self.scheduling(),
                self.total_accounted_for(),
                self.total(),
                &self.assume_time,
                &self.assume_core_time,
                &self.polyeq_time,
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
            println!("elaborating:         {}", elaborating);
        }
        println!("scheduling:          {}", scheduling);

        println!(
            "on assume:           {} ({:.02}% of checking time)",
            assume_time,
            100.0 * self.assume_time.mean().as_secs_f64() / self.checking().mean().as_secs_f64(),
        );
        println!("on assume (core):    {}", assume_core_time);
        println!("assume ratio:        {}", self.assume_time_ratio);
        println!(
            "on polyeq:           {} ({:.02}% of checking time)",
            polyeq_time,
            100.0 * self.polyeq_time.mean().as_secs_f64() / self.checking().mean().as_secs_f64(),
        );
        println!("polyeq ratio:        {}", self.polyeq_time_ratio);

        println!("total accounted for: {}", accounted_for);
        println!("total:               {}", total);

        let data_by_rule = self.step_time_by_rule();
        let mut data_by_rule: Vec<_> = data_by_rule.iter().collect();
        data_by_rule.sort_by_key(|(_, m)| if sort_by_total { m.total() } else { m.mean() });

        println!("by rule:");
        for (rule, data) in data_by_rule {
            print!("    {: <18}", rule);
            if sort_by_total {
                println!("{:#}", data);
            } else {
                println!("{}", data);
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

        let worst_file_polyeq = self.polyeq_time_ratio.max();
        println!(
            "    file (polyeq):   {} ({:.04}%)",
            worst_file_polyeq.0 .0,
            worst_file_polyeq.1 * 100.0
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

        let depths = &self.polyeq_depths;
        if !depths.is_empty() {
            println!("           max polyeq depth: {}", depths.max().1);
            println!("         total polyeq depth: {}", depths.total());
            println!("    number of polyeq checks: {}", depths.count());
            println!("                 mean depth: {:.4}", depths.mean());
            println!(
                "standard deviation of depth: {:.4}",
                depths.standard_deviation()
            );
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InternedStepId {
    pub(crate) file: Arc<str>,
    pub(crate) step_id: Arc<str>,
    pub(crate) rule: Arc<str>,
}

impl fmt::Display for InternedStepId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{} ({})", self.file, self.step_id, self.rule)
    }
}

type InternedRunId = (Arc<str>, usize);

#[derive(Default)]
pub struct CsvBenchmarkResults {
    strings: IndexSet<Arc<str>>,
    runs: IndexMap<InternedRunId, RunMeasurement>,
    steps: Vec<(Arc<str>, Duration)>,
    is_holey: bool,
    num_errors: usize,
}

impl CsvBenchmarkResults {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn is_holey(&self) -> bool {
        self.is_holey
    }

    pub fn num_errors(&self) -> usize {
        self.num_errors
    }

    fn intern(&mut self, s: &str) -> Arc<str> {
        match self.strings.get(s) {
            Some(interned) => interned.clone(),
            None => {
                let result: Arc<str> = Arc::from(s);
                self.strings.insert(result.clone());
                result
            }
        }
    }

    pub fn write_csv(
        self,
        runs_dest: &mut dyn io::Write,
        steps_dest: &mut dyn io::Write,
    ) -> io::Result<()> {
        Self::write_runs_csv(self.runs, runs_dest)?;
        Self::write_steps_csv(self.steps, steps_dest)
    }

    fn write_runs_csv(
        data: IndexMap<InternedRunId, RunMeasurement>,
        dest: &mut dyn io::Write,
    ) -> io::Result<()> {
        writeln!(
            dest,
            "proof_file,run_id,parsing,checking,elaboration,total_accounted_for,\
            total,polyeq,polyeq_ratio,assume,assume_ratio"
        )?;

        for (id, m) in data {
            let total_accounted_for = m.parsing + m.checking + m.elaboration;
            let polyeq_ratio = m.polyeq.as_secs_f64() / m.checking.as_secs_f64();
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
                m.polyeq.as_nanos(),
                polyeq_ratio,
                m.assume.as_nanos(),
                assume_ratio,
            )?;
        }

        Ok(())
    }

    fn write_steps_csv(
        data: Vec<(Arc<str>, Duration)>,
        dest: &mut dyn io::Write,
    ) -> io::Result<()> {
        writeln!(dest, "rule,time")?;
        for (rule, t) in data {
            writeln!(dest, "{},{}", rule, t.as_nanos())?;
        }
        Ok(())
    }
}

pub trait CollectResults {
    fn add_step_measurement(&mut self, file: &str, step_id: &str, rule: &str, time: Duration);
    fn add_assume_measurement(&mut self, file: &str, id: &str, is_easy: bool, time: Duration);
    fn add_polyeq_depth(&mut self, depth: usize);
    fn add_run_measurement(&mut self, id: &RunId, measurement: RunMeasurement);
    fn register_holey(&mut self);
    fn register_error(&mut self, error: &crate::Error);

    fn combine(a: Self, b: Self) -> Self
    where
        Self: Sized;
}

impl CollectResults for OnlineBenchmarkResults {
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

    fn add_polyeq_depth(&mut self, depth: usize) {
        self.polyeq_depths.add_sample(&(), depth);
    }

    fn add_run_measurement(&mut self, id: &RunId, measurement: RunMeasurement) {
        let RunMeasurement {
            parsing,
            checking,
            elaboration,
            scheduling,
            total,
            polyeq,
            assume,
            assume_core,
        } = measurement;

        self.parsing.add_sample(id, parsing);
        self.checking.add_sample(id, checking);
        self.elaborating.add_sample(id, elaboration);
        self.scheduling.add_sample(id, scheduling);
        self.total_accounted_for
            .add_sample(id, parsing + checking + elaboration);
        self.total.add_sample(id, total);

        self.polyeq_time.add_sample(id, polyeq);
        self.assume_time.add_sample(id, assume);
        self.assume_core_time.add_sample(id, assume_core);

        let polyeq_ratio = polyeq.as_secs_f64() / checking.as_secs_f64();
        let assume_ratio = assume.as_secs_f64() / checking.as_secs_f64();
        self.polyeq_time_ratio.add_sample(id, polyeq_ratio);
        self.assume_time_ratio.add_sample(id, assume_ratio);
    }

    fn combine(a: Self, b: Self) -> Self {
        Self {
            parsing: a.parsing.combine(b.parsing),
            checking: a.checking.combine(b.checking),
            elaborating: a.elaborating.combine(b.elaborating),
            scheduling: a.scheduling.combine(b.scheduling),
            total_accounted_for: a.total_accounted_for.combine(b.total_accounted_for),
            total: a.total.combine(b.total),
            step_time: a.step_time.combine(b.step_time),
            step_time_by_file: combine_map(a.step_time_by_file, b.step_time_by_file),
            step_time_by_rule: combine_map(a.step_time_by_rule, b.step_time_by_rule),

            polyeq_time: a.polyeq_time.combine(b.polyeq_time),
            polyeq_time_ratio: a.polyeq_time_ratio.combine(b.polyeq_time_ratio),
            assume_time: a.assume_time.combine(b.assume_time),
            assume_time_ratio: a.assume_time_ratio.combine(b.assume_time_ratio),
            assume_core_time: a.assume_core_time.combine(b.assume_core_time),

            polyeq_depths: a.polyeq_depths.combine(b.polyeq_depths),
            num_assumes: a.num_assumes + b.num_assumes,
            num_easy_assumes: a.num_easy_assumes + b.num_easy_assumes,
            is_holey: a.is_holey || b.is_holey,
            had_error: a.had_error || b.had_error,
        }
    }

    fn register_holey(&mut self) {
        self.is_holey = true;
    }

    fn register_error(&mut self, _: &crate::Error) {
        self.had_error = true;
    }
}

impl CollectResults for CsvBenchmarkResults {
    fn add_step_measurement(&mut self, _: &str, _: &str, rule: &str, time: Duration) {
        let rule = self.intern(rule);
        self.steps.push((rule, time));
    }

    fn add_assume_measurement(&mut self, file: &str, id: &str, _: bool, time: Duration) {
        self.add_step_measurement(file, id, "assume", time);
    }

    fn add_polyeq_depth(&mut self, _: usize) {}

    fn add_run_measurement(&mut self, (file, i): &RunId, measurement: RunMeasurement) {
        let id = (self.intern(file), *i);
        self.runs.insert(id, measurement);
    }

    fn register_holey(&mut self) {
        self.is_holey = true;
    }

    fn register_error(&mut self, _: &crate::Error) {
        self.num_errors += 1;
    }

    fn combine(mut a: Self, b: Self) -> Self {
        // This assumes that the same run never appears in both `a` and `b`. This should be the case
        // in benchmarks anyway
        a.runs.extend(b.runs);
        a.steps.extend(b.steps);
        a.num_errors += b.num_errors;
        a
    }
}
