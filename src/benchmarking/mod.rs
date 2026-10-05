//! Tools for benchmarking Carcara.

mod metrics;
#[cfg(test)]
mod tests;

pub use metrics::*;

use indexmap::IndexMap;
use rapidhash::RapidHashSet;
use std::{fmt, fs, hash::Hash, io, sync::Arc, time::Duration};

/// The unique identifier of a single proof step, given by its file, step ID, and rule.
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

/// The timing measurements of a single run of Carcara on a proof.
#[derive(Debug, Default)]
pub struct RunMeasurement {
    /// The time spent parsing the proof.
    pub parsing: Duration,

    /// The time spent checking the proof.
    pub checking: Duration,

    /// The time spent elaborating the proof.
    pub elaboration: Duration,

    /// The total time spent on the run.
    pub total: Duration,

    /// The time spent checking polyequality.
    pub polyeq: Duration,

    /// The time spent checking `assume` steps.
    pub assume: Duration,

    /// The time spent comparing `assume`d terms with their premises.
    pub assume_core: Duration,

    /// The time spent on each pass of the elaboration pipeline.
    pub elaboration_pipeline: Vec<Duration>,
}

/// The benchmark results collected over many runs of Carcara on a set of proofs.
#[derive(Debug, Default, Clone)]
pub struct SummaryStats {
    /// The time per run to parse the proof.
    pub parsing: Metrics<RunId>,

    /// The time per run to check the proof.
    pub checking: Metrics<RunId>,

    /// The time per run to elaborate the proof.
    pub elaborating: Metrics<RunId>,

    /// The combined time per run to parse, check, and elaborate.
    pub total_accounted_for: Metrics<RunId>,

    /// The total time spent per run.
    pub total: Metrics<RunId>,

    /// The time spent checking each step.
    pub step_time: Metrics<StepId>,

    /// For each rule, the time spent checking each step that uses that rule.
    pub step_time_by_rule: IndexMap<String, Metrics<StepId>>,

    /// The time spent checking polyequality.
    pub polyeq_time: Metrics<RunId>,

    /// The proportion of the checking time that was spent checking polyequality.
    pub polyeq_time_ratio: Metrics<RunId, f64>,

    /// The time spent on `assume` steps.
    pub assume_time: Metrics<RunId>,

    /// The proportion of the checking time that was spent on `assume` steps.
    pub assume_time_ratio: Metrics<RunId, f64>,

    /// The time spent comparing `assume`d terms with their premises.
    pub assume_core_time: Metrics<RunId>,

    /// For each elaboration pass, the time per run spent in that pass.
    pub pipeline_times: Vec<Metrics<RunId>>,

    /// The depth of each polyequality check that was performed.
    pub polyeq_depths: Metrics<(), usize>,

    /// The total number of `assume` steps checked.
    pub num_assumes: usize,

    /// The number of `assume` steps that required no polyequality.
    pub num_easy_assumes: usize,
}

impl SummaryStats {
    /// Creates a new, empty `SummaryStats`.
    pub fn new() -> Self {
        Default::default()
    }

    /// Return `true` if the results have no entries.
    pub fn is_empty(&self) -> bool {
        self.total.is_empty()
    }

    /// Prints the benchmark results
    pub fn print(&self, sort_by_total: bool) {
        println!(
            "parsing:             {}",
            self.parsing.display(sort_by_total)
        );
        println!(
            "checking:            {}",
            self.checking.display(sort_by_total)
        );
        if !self.pipeline_times.is_empty() {
            println!(
                "elaborating:         {}",
                self.elaborating.display(sort_by_total)
            );
            for (i, pass) in self.pipeline_times.iter().enumerate() {
                println!("    pass {}:          {}", i, pass.display(sort_by_total));
            }
        }

        println!(
            "on assume:           {} ({:.02}% of checking time)",
            self.assume_time.display(sort_by_total),
            100.0 * self.assume_time.mean().as_secs_f64() / self.checking.mean().as_secs_f64(),
        );
        println!(
            "on assume (core):    {}",
            self.assume_core_time.display(sort_by_total)
        );
        println!(
            "assume ratio:        {}",
            self.assume_time_ratio.display(false)
        );
        println!(
            "on polyeq:           {} ({:.02}% of checking time)",
            self.polyeq_time.display(sort_by_total),
            100.0 * self.polyeq_time.mean().as_secs_f64() / self.checking.mean().as_secs_f64(),
        );
        println!(
            "polyeq ratio:        {}",
            self.polyeq_time_ratio.display(false)
        );

        println!(
            "total accounted for: {}",
            self.total_accounted_for.display(sort_by_total)
        );
        println!("total:               {}", self.total.display(sort_by_total));

        let data_by_rule = &self.step_time_by_rule;
        let mut data_by_rule: Vec<_> = data_by_rule.iter().collect();
        data_by_rule.sort_by_key(|(_, m)| if sort_by_total { m.total() } else { m.mean() });

        println!("by rule:");
        for (rule, data) in data_by_rule {
            println!("    {: <18}{}", rule, data.display(sort_by_total));
        }

        println!("worst cases:");
        if !self.step_time.is_empty() {
            let worst_step = self.step_time.max();
            println!("    step:            {} ({:?})", worst_step.0, worst_step.1);
        }

        let worst_file_parsing = self.parsing.max();
        println!(
            "    file (parsing):  {} ({:?})",
            worst_file_parsing.0.0, worst_file_parsing.1
        );

        let worst_file_checking = self.checking.max();
        println!(
            "    file (checking): {} ({:?})",
            worst_file_checking.0.0, worst_file_checking.1
        );

        let worst_file_assume = self.assume_time_ratio.max();
        println!(
            "    file (assume):   {} ({:.04}%)",
            worst_file_assume.0.0,
            worst_file_assume.1 * 100.0
        );

        let worst_file_polyeq = self.polyeq_time_ratio.max();
        println!(
            "    file (polyeq):   {} ({:.04}%)",
            worst_file_polyeq.0.0,
            worst_file_polyeq.1 * 100.0
        );

        let worst_file_total = self.total.max();
        println!(
            "    file overall:    {} ({:?})",
            worst_file_total.0.0, worst_file_total.1
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

/// Benchmark results that can be written to CSV files.
#[derive(Default)]
pub struct CsvStats {
    strings: RapidHashSet<Arc<str>>,
    runs: Vec<(RunId, RunMeasurement)>,
    steps: Vec<(Arc<str>, Duration)>,
}

impl CsvStats {
    /// Creates a new, empty `CsvStats`.
    pub fn new() -> Self {
        Default::default()
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

    /// Writes the benchmark results to the given writers: one CSV for the run measurements and one
    /// for the step measurements.
    pub fn write_csv(self, runs_file: &str, steps_file: &str) -> Result<(), crate::Error> {
        fs::File::create(runs_file)
            .and_then(|mut f| Self::write_runs_csv(self.runs, &mut f))
            .map_err(|inner| crate::Error::Io { inner, file: runs_file.into() })?;
        fs::File::create(steps_file)
            .and_then(|mut f| Self::write_steps_csv(self.steps, &mut f))
            .map_err(|inner| crate::Error::Io { inner, file: steps_file.into() })
    }

    fn write_runs_csv(
        data: Vec<(RunId, RunMeasurement)>,
        dest: &mut dyn io::Write,
    ) -> io::Result<()> {
        let pipeline_length = data
            .first()
            .map_or(0, |(_, m)| m.elaboration_pipeline.len());
        write!(
            dest,
            "proof_file,run_id,parsing,checking,elaboration,total_accounted_for,\
            total,polyeq,polyeq_ratio,assume,assume_ratio"
        )?;
        for i in 0..pipeline_length {
            write!(dest, ",pipeline_step_{}", i)?;
        }
        writeln!(dest)?;

        for (id, m) in data {
            let total_accounted_for = m.parsing + m.checking + m.elaboration;
            let polyeq_ratio = m.polyeq.as_secs_f64() / m.checking.as_secs_f64();
            let assume_ratio = m.assume.as_secs_f64() / m.checking.as_secs_f64();
            write!(
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
            assert_eq!(m.elaboration_pipeline.len(), pipeline_length);
            for d in m.elaboration_pipeline {
                write!(dest, ",{}", d.as_nanos())?;
            }
            writeln!(dest)?;
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

/// A sink for benchmark results, which receives measurements as proofs are checked and elaborated.
pub trait CollectStats {
    /// Records the time spent checking a single step.
    fn add_step_measurement(&mut self, file: &str, step_id: &str, rule: &str, time: Duration);

    /// Records the time spent checking an `assume` step.
    fn add_assume_measurement(&mut self, file: &str, id: &str, is_easy: bool, time: Duration);

    /// Records the depth of a polyequality check.
    fn add_polyeq_depth(&mut self, depth: usize);

    /// Records the timing measurements of a single run.
    fn add_run_measurement(&mut self, id: &RunId, measurement: RunMeasurement);

    /// Combines two sets of results into one.
    fn combine(a: Self, b: Self) -> Self
    where
        Self: Sized;
}

impl CollectStats for SummaryStats {
    fn add_step_measurement(&mut self, file: &str, step_id: &str, rule: &str, time: Duration) {
        let rule = rule.to_owned();
        let id = StepId {
            file: file.into(),
            step_id: step_id.into(),
            rule: rule.clone().into_boxed_str(),
        };
        self.step_time.add_sample(&id, time);
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
            total,
            polyeq,
            assume,
            assume_core,
            elaboration_pipeline,
        } = measurement;

        self.parsing.add_sample(id, parsing);
        self.checking.add_sample(id, checking);
        self.elaborating.add_sample(id, elaboration);
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

        if self.pipeline_times.len() < elaboration_pipeline.len() {
            self.pipeline_times
                .resize_with(elaboration_pipeline.len(), Metrics::new);
        }
        for (pass, time) in self.pipeline_times.iter_mut().zip(elaboration_pipeline) {
            pass.add_sample(id, time);
        }
    }

    fn combine(a: Self, b: Self) -> Self {
        Self {
            parsing: a.parsing.combine(b.parsing),
            checking: a.checking.combine(b.checking),
            elaborating: a.elaborating.combine(b.elaborating),
            total_accounted_for: a.total_accounted_for.combine(b.total_accounted_for),
            total: a.total.combine(b.total),
            step_time: a.step_time.combine(b.step_time),
            step_time_by_rule: {
                let mut res = a.step_time_by_rule;
                for (k, v) in b.step_time_by_rule {
                    res.entry(k).or_default().combine_in_place(v);
                }
                res
            },

            polyeq_time: a.polyeq_time.combine(b.polyeq_time),
            polyeq_time_ratio: a.polyeq_time_ratio.combine(b.polyeq_time_ratio),
            assume_time: a.assume_time.combine(b.assume_time),
            assume_time_ratio: a.assume_time_ratio.combine(b.assume_time_ratio),
            assume_core_time: a.assume_core_time.combine(b.assume_core_time),

            polyeq_depths: a.polyeq_depths.combine(b.polyeq_depths),
            num_assumes: a.num_assumes + b.num_assumes,
            num_easy_assumes: a.num_easy_assumes + b.num_easy_assumes,
            pipeline_times: {
                let mut res = a.pipeline_times;
                if res.len() < b.pipeline_times.len() {
                    res.resize_with(b.pipeline_times.len(), Metrics::new);
                }
                for (pass, other) in res.iter_mut().zip(b.pipeline_times) {
                    pass.combine_in_place(other);
                }
                res
            },
        }
    }
}

impl CollectStats for CsvStats {
    fn add_step_measurement(&mut self, _: &str, _: &str, rule: &str, time: Duration) {
        let rule = self.intern(rule);
        self.steps.push((rule, time));
    }

    fn add_assume_measurement(&mut self, file: &str, id: &str, _: bool, time: Duration) {
        self.add_step_measurement(file, id, "assume", time);
    }

    fn add_polyeq_depth(&mut self, _: usize) {}

    fn add_run_measurement(&mut self, id: &RunId, measurement: RunMeasurement) {
        self.runs.push((id.clone(), measurement));
    }

    fn combine(mut a: Self, b: Self) -> Self {
        // This assumes that the same run never appears in both `a` and `b`. This should be the case
        // in benchmarks anyway
        a.runs.extend(b.runs);
        a.steps.extend(b.steps);
        a
    }
}
