mod metrics;
#[cfg(test)]
mod tests;

pub use metrics::*;

use ahash::AHashMap;
use std::{fmt, time::Duration};

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

// Higher kinded types would be very useful here. Ideally, I would like `BenchmarkResults` to be
// generic on any kind that implements `Metrics`, like `OnlineMetrics` or `OfflineMetrics`.
#[derive(Debug, Default)]
pub struct BenchmarkResults<ByRun, ByStep, ByRunF64, ByDeepEq> {
    pub parsing: ByRun,
    pub checking: ByRun,
    pub reconstructing: ByRun,
    pub total_accounted_for: ByRun,
    pub total: ByRun,
    pub step_time: ByStep,
    pub step_time_by_file: AHashMap<String, ByStep>,
    pub step_time_by_rule: AHashMap<String, ByStep>,

    pub deep_eq_time: ByRun,
    pub deep_eq_time_ratio: ByRunF64,
    pub assume_time: ByRun,
    pub assume_time_ratio: ByRunF64,

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

    /// The time per run to reconstruct the proof.
    pub fn reconstructing(&self) -> &ByRun {
        &self.reconstructing
    }

    /// The combined time per run to parse, check, and reconstruct all the steps in the proof.
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

    /// Combines two `BenchmarkResults` into one. This method is subject to some numerical
    /// stability issues, as is described in `Metrics::combine`.
    pub fn combine(a: Self, b: Self) -> Self {
        Self {
            parsing: a.parsing.combine(b.parsing),
            checking: a.checking.combine(b.checking),
            reconstructing: a.reconstructing.combine(b.reconstructing),
            total_accounted_for: a.total_accounted_for.combine(b.total_accounted_for),
            total: a.total.combine(b.total),
            step_time: a.step_time.combine(b.step_time),
            step_time_by_file: combine_map(a.step_time_by_file, b.step_time_by_file),
            step_time_by_rule: combine_map(a.step_time_by_rule, b.step_time_by_rule),

            deep_eq_time: a.deep_eq_time.combine(b.deep_eq_time),
            deep_eq_time_ratio: a.deep_eq_time_ratio.combine(b.deep_eq_time_ratio),
            assume_time: a.assume_time.combine(b.assume_time),
            assume_time_ratio: a.assume_time_ratio.combine(b.assume_time_ratio),

            deep_eq_depths: a.deep_eq_depths.combine(b.deep_eq_depths),
            num_assumes: a.num_assumes + b.num_assumes,
            num_easy_assumes: a.num_easy_assumes + b.num_easy_assumes,
        }
    }
}

#[derive(Debug, Default)]
pub struct RunMeasurement {
    pub parsing: Duration,
    pub checking: Duration,
    pub reconstruction: Duration,
    pub total: Duration,
    pub deep_eq: Duration,
    pub assume: Duration,
}

pub trait CollectResults {
    fn add_step_measurement(&mut self, file: &str, step_id: &str, rule: &str, time: Duration);
    fn add_assume_measurement(&mut self, file: &str, id: &str, is_easy: bool, time: Duration);
    fn add_deep_eq_depth(&mut self, depth: usize);
    fn add_run_measurement(&mut self, id: &RunId, measurement: RunMeasurement);
}

impl<ByRun, ByStep, ByRunF64, ByDeepEq> CollectResults
    for BenchmarkResults<ByRun, ByStep, ByRunF64, ByDeepEq>
where
    ByRun: Metrics<RunId, Duration> + Default,
    ByStep: Metrics<StepId, Duration> + Default,
    ByRunF64: Metrics<RunId, f64> + Default,
    ByDeepEq: Metrics<(), usize> + Default,
{
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
        self.add_step_measurement(file, id, "assume*", time);
    }

    fn add_deep_eq_depth(&mut self, depth: usize) {
        self.deep_eq_depths.add_sample(&(), depth);
    }

    fn add_run_measurement(&mut self, id: &RunId, measurement: RunMeasurement) {
        let RunMeasurement {
            parsing,
            checking,
            reconstruction,
            total,
            deep_eq,
            assume,
        } = measurement;

        self.parsing.add_sample(id, parsing);
        self.checking.add_sample(id, checking);
        self.reconstructing.add_sample(id, reconstruction);
        self.total_accounted_for.add_sample(id, parsing + checking);
        self.total.add_sample(id, total);

        self.deep_eq_time.add_sample(id, deep_eq);
        self.assume_time.add_sample(id, assume);

        let deep_eq_ratio = deep_eq.as_secs_f64() / checking.as_secs_f64();
        let assume_ratio = assume.as_secs_f64() / checking.as_secs_f64();
        self.deep_eq_time_ratio.add_sample(id, deep_eq_ratio);
        self.assume_time_ratio.add_sample(id, assume_ratio);
    }
}
