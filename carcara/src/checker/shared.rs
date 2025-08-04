use crate::{
    ast::*,
    benchmarking::CollectResults,
    checker::{CheckerStatistics, Config},
};
use indexmap::IndexSet;
use std::time::{Duration, Instant};

/// Shared logic for checking assume commands that both single-threaded and parallel
/// implementations can use. Returns true if the assume is valid.
pub fn check_assume_shared<CR: CollectResults + Send + Default>(
    id: &str,
    term: &Rc<Term>,
    premises: &IndexSet<Rc<Term>>,
    config: &Config,
    is_in_subproof: bool,
    stats: &mut Option<&mut CheckerStatistics<CR>>,
) -> bool {
    let time = Instant::now();

    // Some subproofs contain `assume` commands inside them. These don't refer to the original
    // problem premises, but are instead local assumptions that are discharged by the subproof's
    // final step, so we ignore the `assume` command if it is inside a subproof.
    if is_in_subproof {
        return true;
    }

    // Check for exact match first
    if premises.contains(term) {
        let total_time = time.elapsed();
        if let Some(s) = stats {
            s.assume_time += total_time;
            s.results
                .add_assume_measurement(s.file_name, id, true, total_time);
        }
        return true;
    }

    // If elaborated mode, no polyeq checking allowed
    if config.elaborated {
        return false;
    }

    // Perform polyeq checking
    let mut found = false;
    let mut polyeq_time = Duration::ZERO;
    let mut core_time = Duration::ZERO;

    for p in premises {
        let mut this_polyeq_time = Duration::ZERO;

        let mut comp = Polyeq::new().mod_reordering(true).mod_nary(true);
        let result = comp.eq_with_time(term, p, &mut this_polyeq_time);
        let depth = comp.max_depth();

        polyeq_time += this_polyeq_time;

        if let Some(s) = &mut *stats {
            s.results.add_polyeq_depth(depth);
        }
        if result {
            core_time = this_polyeq_time;
            found = true;
            break;
        }
    }

    let total_time = time.elapsed();

    if let Some(s) = stats {
        s.assume_time += total_time;
        s.assume_core_time += core_time;
        s.polyeq_time += polyeq_time;
        s.results
            .add_assume_measurement(s.file_name, id, false, total_time);
    }

    found
}