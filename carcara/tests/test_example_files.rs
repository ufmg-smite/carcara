use carcara::*;
use std::{ffi::OsStr, fs, io, path::Path};

fn get_truncated_message(e: &Error) -> String {
    const ERROR_MESSAGE_LIMIT: usize = 350;
    const TRUNCATION_MESSAGE: &str = "... (long message truncated)";
    const TRUNCATION_LEN: usize = TRUNCATION_MESSAGE.as_bytes().len();

    let mut error_message = format!("{}", e);

    if error_message.len() > ERROR_MESSAGE_LIMIT + TRUNCATION_LEN {
        error_message.truncate(ERROR_MESSAGE_LIMIT);
        error_message.push_str(TRUNCATION_MESSAGE);
    }
    error_message
}

fn run_test(problem_path: &Path, proof_path: &Path) -> CarcaraResult<()> {
    fn test_config<'a>() -> checker::Config<'a> {
        checker::Config {
            strict: false,
            skip_unknown_rules: true,
            is_running_test: false,
            statistics: None,
            check_lia_using_cvc5: true,
        }
    }

    let (prelude, proof, mut pool) = parser::parse_instance(
        io::BufReader::new(fs::File::open(problem_path)?),
        io::BufReader::new(fs::File::open(proof_path)?),
        true,
        false,
    )?;

    // First, we check the proof normally
    checker::ProofChecker::new(&mut pool, test_config(), prelude.clone()).check(&proof)?;

    // Then, we check it while elaborating the proof
    let mut checker = checker::ProofChecker::new(&mut pool, test_config(), prelude.clone());
    let elaborated = checker.check_and_elaborate(proof)?;

    // After that, we check the elaborated proof normally, to make sure it is valid
    checker::ProofChecker::new(&mut pool, test_config(), prelude.clone()).check(&elaborated)?;

    // Finally, we elaborate the already elaborated proof, to make sure the elaboration step is
    // idempotent
    let mut checker = checker::ProofChecker::new(&mut pool, test_config(), prelude);
    let elaborated_twice = checker.check_and_elaborate(elaborated.clone())?;
    assert_eq!(elaborated.commands, elaborated_twice.commands);

    Ok(())
}

fn test_file(problem_path: &Path, proof_path: &Path) {
    if let Err(e) = run_test(problem_path, proof_path) {
        panic!(
            "\ntest file \"{}\"\nreturned error: {}\n",
            &problem_path.to_str().unwrap(),
            get_truncated_message(&e),
        )
    }
}

fn test_examples_from_dir(dir_path: &str) {
    fn is_proof_file(entry: &io::Result<fs::DirEntry>) -> bool {
        let entry = entry.as_ref().unwrap();
        entry.file_type().unwrap().is_file()
            && entry.path().extension() == Some(OsStr::new("proof"))
    }
    let rd = fs::read_dir(dir_path).unwrap();
    for entry in rd.filter(is_proof_file) {
        let entry = entry.unwrap();
        let proof_path = entry.path();
        let problem_path = {
            let mut path = proof_path.clone();
            while path.extension().unwrap() != "smt_in" && path.extension().unwrap() != "smt2" {
                path.set_extension("");
            }
            path
        };
        test_file(&problem_path, &proof_path);
    }
}

macro_rules! generate_tests {
    ($root_dir:literal, $($test_name:ident : $dir_name:literal,)* ) => {
        $(
            #[test]
            fn $test_name() {
                test_examples_from_dir(&format!("{}{}", $root_dir, $dir_name))
            }
        )*
    };
}

generate_tests! {
    "../test-examples/",
    sh_problems_green_verit: "SH_problems_all_filtered/Green_veriT",
    sh_problems_ordered_resolution_prover_verit:
        "SH_problems_all_filtered/Ordered_Resolution_Prover_veriT",
    sh_problems_ordered_resolution_prover_verit_mirabelle_z3:
        "SH_problems_all_filtered/Ordered_Resolution_Prover_veriT/Mirabelle_z3",
    sh_problems_isabelle_mirabelle_bo_cvc42: "SH_problems_all_filtered/isabelle-mirabelle/BO_cvc42",
    sh_problems_isabelle_mirabelle_green_cvc42:
        "SH_problems_all_filtered/isabelle-mirabelle/Green_cvc42",
    sh_problems_isabelle_mirabelle_green_verit:
        "SH_problems_all_filtered/isabelle-mirabelle/Green_veriT",
    sh_problems_isabelle_mirabelle_green_verit2:
        "SH_problems_all_filtered/isabelle-mirabelle/Green_veriT2",
    sh_problems_isabelle_mirabelle_green_z32:
        "SH_problems_all_filtered/isabelle-mirabelle/Green_z32",
    sh_problems_isabelle_mirabelle_hol_library_smt_cvc4:
        "SH_problems_all_filtered/isabelle-mirabelle/HOL-Library/smt_cvc4",
    sh_problems_isabelle_mirabelle_hol_library_smt_verit:
        "SH_problems_all_filtered/isabelle-mirabelle/HOL-Library/smt_verit",
    sh_problems_isabelle_mirabelle_hol_library_pnt_cvc42:
        "SH_problems_all_filtered/isabelle-mirabelle/PNT_cvc42",
    sh_problems_isabelle_mirabelle_hol_library_pnt_z32:
        "SH_problems_all_filtered/isabelle-mirabelle/PNT_z32",
    sh_problems_all_filtered: "SH_problems_all_filtered/isabelle-mirabelle/Zeta_cvc42",
    simple_tests: "simple-tests",
}

// The tests for the large test set. Some tests are commented out because they take a very long
// time to run
#[cfg(feature = "large-test-set")]
generate_tests! {
    "../large-test-set/",
    auflia_20170829_rodin: "AUFLIA/20170829-Rodin",
    auflia_misc: "AUFLIA/misc",
    auflira_fft: "AUFLIRA/FFT",
    auflira_nasa_fol_simplify: "AUFLIRA/nasa/fol_simplify",
    auflira_nasa_fol_simplify_arithmetics: "AUFLIRA/nasa/fol_simplify_arithmetics",
    auflira_nasa_fol_simplify_array: "AUFLIRA/nasa/fol_simplify_array",
    auflira_nasa_fol_simplify_array_only: "AUFLIRA/nasa/fol_simplify_array_only",
    auflira_nasa_fol_simplify_structure_forall: "AUFLIRA/nasa/fol_simplify_structure_forall",
    auflira_nasa_fol_simplify_structure_prop: "AUFLIRA/nasa/fol_simplify_structure_prop",
    auflira_nasa_vc_normalize_subst: "AUFLIRA/nasa/vc_normalize_subst",
    auflira_peter: "AUFLIRA/peter",
    auflira_why: "AUFLIRA/why",
    qf_alia_array_benchmarks_misc: "QF_ALIA/array_benchmarks/misc",
    qf_alia_pivc: "QF_ALIA/piVC",
    qf_auflia_20170829_rodin: "QF_AUFLIA/20170829-Rodin",
    qf_auflia_cvc: "QF_AUFLIA/cvc",
    qf_auflia_swap: "QF_AUFLIA/swap",
    qf_idl_asp_channelrouting: "QF_IDL/asp/ChannelRouting",
    qf_idl_asp_connecteddominatingset: "QF_IDL/asp/ConnectedDominatingSet",
    qf_idl_asp_hierarchicalclustering: "QF_IDL/asp/HierarchicalClustering",
    qf_idl_asp_mazegeneration: "QF_IDL/asp/MazeGeneration",
    qf_idl_asp_schurnumbers: "QF_IDL/asp/SchurNumbers",
    qf_idl_asp_sokoban: "QF_IDL/asp/Sokoban",
    qf_idl_averest_binary_search: "QF_IDL/Averest/binary_search",
    qf_idl_averest_buble_sort: "QF_IDL/Averest/buble_sort",
    qf_idl_averest_fast_max: "QF_IDL/Averest/fast_max",
    // qf_idl_averest_insertion_sort: "QF_IDL/Averest/insertion_sort",
    qf_idl_averest_linear_search: "QF_IDL/Averest/linear_search",
    qf_idl_averest_min_max: "QF_IDL/Averest/min_max",
    qf_idl_averest_parallel_prefix_sum: "QF_IDL/Averest/parallel_prefix_sum",
    qf_idl_averest_parallel_search: "QF_IDL/Averest/parallel_search",
    qf_idl_averest_partition: "QF_IDL/Averest/partition",
    qf_idl_averest_selection_sort: "QF_IDL/Averest/selection_sort",
    qf_idl_averest_sorting_network: "QF_IDL/Averest/sorting_network",
    qf_idl_cellar: "QF_IDL/cellar",
    qf_idl_check: "QF_IDL/check",
    // qf_idl_diamonds: "QF_IDL/diamonds",
    qf_idl_dtp: "QF_IDL/DTP",
    qf_idl_job_shop: "QF_IDL/job_shop",
    qf_idl_mathsat_fischer: "QF_IDL/mathsat/fischer",
    qf_idl_mathsat_post_office: "QF_IDL/mathsat/post_office",
    qf_idl_parity: "QF_IDL/parity",
    qf_idl_planning: "QF_IDL/planning",
    qf_idl_qlock: "QF_IDL/qlock",
    qf_idl_queens_bench_n_queen: "QF_IDL/queens_bench/n_queen",
    qf_idl_queens_bench_super_queen: "QF_IDL/queens_bench/super_queen",
    qf_idl_queens_bench_toroidal_bench: "QF_IDL/queens_bench/toroidal_bench",
    qf_idl_rtcl_b01_tf_15: "QF_IDL/RTCL/b01_tf_15",
    qf_idl_rtcl_b01_tf_20: "QF_IDL/RTCL/b01_tf_20",
    qf_idl_rtcl_b02_tf_15: "QF_IDL/RTCL/b02_tf_15",
    qf_idl_rtcl_b02_tf_20: "QF_IDL/RTCL/b02_tf_20",
    // qf_idl_rtcl_b13_tf_10: "QF_IDL/RTCL/b13_tf_10",
    // qf_idl_rtcl_b13_tf_15: "QF_IDL/RTCL/b13_tf_15",
    // qf_idl_rtcl_b13_tf_20: "QF_IDL/RTCL/b13_tf_20",
    // qf_idl_rtcl_b13_tf_25: "QF_IDL/RTCL/b13_tf_25",
    // qf_idl_rtcl_b13_tf_30: "QF_IDL/RTCL/b13_tf_30",
    qf_idl_sal_bakery: "QF_IDL/sal/bakery",
    qf_idl_sal_lpsat: "QF_IDL/sal/lpsat",
    qf_idl_schedulingidl: "QF_IDL/schedulingIDL",
    qf_idl_sep_hardware: "QF_IDL/sep/hardware",
    qf_lia_20180326_bromberger_more_slacked_cav_2009_benchmarks_coef_size_smt_size_10:
        "QF_LIA/20180326-Bromberger/more_slacked/CAV_2009_benchmarks/coef-size/smt/size-10",
    qf_lia_20180326_bromberger_more_slacked_cav_2009_benchmarks_coef_size_smt_size_100:
        "QF_LIA/20180326-Bromberger/more_slacked/CAV_2009_benchmarks/coef-size/smt/size-100",
    qf_lia_20180326_bromberger_more_slacked_cav_2009_benchmarks_coef_size_smt_size_20:
        "QF_LIA/20180326-Bromberger/more_slacked/CAV_2009_benchmarks/coef-size/smt/size-20",
    qf_lia_20180326_bromberger_more_slacked_cav_2009_benchmarks_coef_size_smt_size_30:
        "QF_LIA/20180326-Bromberger/more_slacked/CAV_2009_benchmarks/coef-size/smt/size-30",
    qf_lia_20180326_bromberger_more_slacked_cav_2009_benchmarks_coef_size_smt_size_40:
        "QF_LIA/20180326-Bromberger/more_slacked/CAV_2009_benchmarks/coef-size/smt/size-40",
    qf_lia_20180326_bromberger_more_slacked_cav_2009_benchmarks_coef_size_smt_size_50:
        "QF_LIA/20180326-Bromberger/more_slacked/CAV_2009_benchmarks/coef-size/smt/size-50",
    qf_lia_20180326_bromberger_more_slacked_cav_2009_benchmarks_coef_size_smt_size_90:
        "QF_LIA/20180326-Bromberger/more_slacked/CAV_2009_benchmarks/coef-size/smt/size-90",
    qf_lia_20180326_bromberger_more_slacked_cav_2009_benchmarks_smt_10_vars:
        "QF_LIA/20180326-Bromberger/more_slacked/CAV_2009_benchmarks/smt/10-vars",
    qf_lia_20180326_bromberger_more_slacked_cav_2009_benchmarks_smt_15_vars:
        "QF_LIA/20180326-Bromberger/more_slacked/CAV_2009_benchmarks/smt/15-vars",
    qf_lia_20180326_bromberger_more_slacked_cav_2009_benchmarks_smt_20_vars:
        "QF_LIA/20180326-Bromberger/more_slacked/CAV_2009_benchmarks/smt/20-vars",
    qf_lia_20180326_bromberger_more_slacked_cav_2009_benchmarks_smt_25_vars:
        "QF_LIA/20180326-Bromberger/more_slacked/CAV_2009_benchmarks/smt/25-vars",
    qf_lia_20180326_bromberger_more_slacked_cav_2009_benchmarks_smt_30_vars:
        "QF_LIA/20180326-Bromberger/more_slacked/CAV_2009_benchmarks/smt/30-vars",
    qf_lia_20180326_bromberger_more_slacked_cut_lemmas_10_vars:
        "QF_LIA/20180326-Bromberger/more_slacked/cut_lemmas/10-vars",
    qf_lia_20180326_bromberger_more_slacked_cut_lemmas_15_vars:
        "QF_LIA/20180326-Bromberger/more_slacked/cut_lemmas/15-vars",
    qf_lia_20180326_bromberger_more_slacked_cut_lemmas_20_vars:
        "QF_LIA/20180326-Bromberger/more_slacked/cut_lemmas/20-vars",
    qf_lia_20210219_dartagnan_reachsafety_loops: "QF_LIA/20210219-Dartagnan/ReachSafety-Loops",
    qf_lia_averest_parallel_prefix_sum: "QF_LIA/Averest/parallel_prefix_sum",
    qf_lia_bofill_scheduling_smt_random_lia: "QF_LIA/bofill-scheduling/SMT_random_LIA",
    qf_lia_bofill_scheduling_smt_real_lia: "QF_LIA/bofill-scheduling/SMT_real_LIA",
    qf_lia_calypto: "QF_LIA/calypto",
    qf_lia_cav_2009_benchmarks_coef_size_smt_size_10:
        "QF_LIA/CAV_2009_benchmarks/coef-size/smt/size-10",
    qf_lia_cav_2009_benchmarks_coef_size_smt_size_100:
        "QF_LIA/CAV_2009_benchmarks/coef-size/smt/size-100",
    qf_lia_cav_2009_benchmarks_coef_size_smt_size_20:
        "QF_LIA/CAV_2009_benchmarks/coef-size/smt/size-20",
    qf_lia_cav_2009_benchmarks_coef_size_smt_size_30:
        "QF_LIA/CAV_2009_benchmarks/coef-size/smt/size-30",
    qf_lia_cav_2009_benchmarks_coef_size_smt_size_40:
        "QF_LIA/CAV_2009_benchmarks/coef-size/smt/size-40",
    qf_lia_cav_2009_benchmarks_coef_size_smt_size_50:
        "QF_LIA/CAV_2009_benchmarks/coef-size/smt/size-50",
    qf_lia_cav_2009_benchmarks_coef_size_smt_size_60:
        "QF_LIA/CAV_2009_benchmarks/coef-size/smt/size-60",
    qf_lia_cav_2009_benchmarks_coef_size_smt_size_90:
        "QF_LIA/CAV_2009_benchmarks/coef-size/smt/size-90",
    qf_lia_cav_2009_benchmarks_smt_10_vars: "QF_LIA/CAV_2009_benchmarks/smt/10-vars",
    qf_lia_cav_2009_benchmarks_smt_15_vars: "QF_LIA/CAV_2009_benchmarks/smt/15-vars",
    qf_lia_cav_2009_benchmarks_smt_20_vars: "QF_LIA/CAV_2009_benchmarks/smt/20-vars",
    qf_lia_cav_2009_benchmarks_smt_25_vars: "QF_LIA/CAV_2009_benchmarks/smt/25-vars",
    qf_lia_cav_2009_benchmarks_smt_30_vars: "QF_LIA/CAV_2009_benchmarks/smt/30-vars",
    qf_lia_check: "QF_LIA/check",
    qf_lia_circ_multiplier: "QF_LIA/CIRC/multiplier",
    qf_lia_circ_simplebitadder: "QF_LIA/CIRC/simplebitadder",
    qf_lia_convert: "QF_LIA/convert",
    qf_lia_cut_lemmas_10_vars: "QF_LIA/cut_lemmas/10-vars",
    qf_lia_cut_lemmas_15_vars: "QF_LIA/cut_lemmas/15-vars",
    qf_lia_cut_lemmas_20_vars: "QF_LIA/cut_lemmas/20-vars",
    qf_lia_dillig: "QF_LIA/dillig",
    qf_lia_fft: "QF_LIA/fft",
    qf_lia_mathsat: "QF_LIA/mathsat",
    // qf_lia_nec_smt_small_int_from_list: "QF_LIA/nec-smt/small/int_from_list",
    qf_lia_pb2010: "QF_LIA/pb2010",
    qf_lia_pidgeons: "QF_LIA/pidgeons",
    qf_lia_prime_cone: "QF_LIA/prime-cone",
    qf_lia_rings: "QF_LIA/rings",
    qf_lia_rings_preprocessed: "QF_LIA/rings_preprocessed",
    qf_lia_slacks: "QF_LIA/slacks",
    qf_lia_tightrhombus: "QF_LIA/tightrhombus",
    qf_lia_wisa: "QF_LIA/wisa",
    qf_lra_2017_heizmann_ultimateinvariantsynthesis:
        "QF_LRA/2017-Heizmann-UltimateInvariantSynthesis",
    qf_lra_check: "QF_LRA/check",
    qf_lra_clock_synchro: "QF_LRA/clock_synchro",
    qf_lra_keymaera: "QF_LRA/keymaera",
    qf_lra_lassoranker_cooperatingt2: "QF_LRA/LassoRanker/CooperatingT2",
    qf_lra_lassoranker_sv_comp: "QF_LRA/LassoRanker/SV-COMP",
    qf_lra_lassoranker_ultimate: "QF_LRA/LassoRanker/Ultimate",
    qf_lra_meti_tarski_asin_8_vars4: "QF_LRA/meti-tarski/asin/8/vars4",
    qf_lra_meti_tarski_atan_problem_1: "QF_LRA/meti-tarski/atan/problem/1",
    qf_lra_meti_tarski_atan_problem_2_weak2: "QF_LRA/meti-tarski/atan/problem/2/weak2",
    qf_lra_meti_tarski_bottom_plate_mixer: "QF_LRA/meti-tarski/bottom-plate-mixer",
    qf_lra_meti_tarski_cbrt_3: "QF_LRA/meti-tarski/cbrt/3",
    qf_lra_meti_tarski_cbrt_3_weak: "QF_LRA/meti-tarski/cbrt/3/weak",
    qf_lra_meti_tarski_chua_1_il_l: "QF_LRA/meti-tarski/Chua/1/IL/L",
    qf_lra_meti_tarski_chua_1_vc1_l: "QF_LRA/meti-tarski/Chua/1/VC1/L",
    qf_lra_meti_tarski_chua_1_vc2_u: "QF_LRA/meti-tarski/Chua/1/VC2/U",
    qf_lra_meti_tarski_cmos: "QF_LRA/meti-tarski/CMOS",
    qf_lra_meti_tarski_log_fun_ineq: "QF_LRA/meti-tarski/log/fun-ineq",
    qf_lra_meti_tarski_polypaver_bench_exp_3d: "QF_LRA/meti-tarski/polypaver/bench-exp-3d",
    qf_lra_meti_tarski_sin_344_3: "QF_LRA/meti-tarski/sin/344/3",
    qf_lra_meti_tarski_sin_344_4: "QF_LRA/meti-tarski/sin/344/4",
    qf_lra_meti_tarski_sin_problem_7: "QF_LRA/meti-tarski/sin/problem/7",
    qf_lra_meti_tarski_sin_problem_7_weak: "QF_LRA/meti-tarski/sin/problem/7/weak",
    qf_lra_meti_tarski_sin_problem_7_weak2: "QF_LRA/meti-tarski/sin/problem/7/weak2",
    qf_lra_meti_tarski_sin_problem_8: "QF_LRA/meti-tarski/sin/problem/8",
    qf_lra_meti_tarski_sin_problem_8_weak: "QF_LRA/meti-tarski/sin/problem/8/weak",
    qf_lra_meti_tarski_sqrt_1mcosq_7: "QF_LRA/meti-tarski/sqrt/1mcosq/7",
    qf_lra_meti_tarski_sqrt_1mcosq_8: "QF_LRA/meti-tarski/sqrt/1mcosq/8",
    qf_lra_meti_tarski_sqrt_problem: "QF_LRA/meti-tarski/sqrt/problem",
    qf_lra_miplib: "QF_LRA/miplib",
    qf_lra_sal_carpark: "QF_LRA/sal/carpark",
    qf_lra_sal_gasburner: "QF_LRA/sal/gasburner",
    qf_lra_sal_pursuit: "QF_LRA/sal/pursuit",
    qf_lra_sal_tgc: "QF_LRA/sal/tgc",
    qf_lra_sal_windowreal: "QF_LRA/sal/windowreal",
    qf_lra_sc: "QF_LRA/sc",
    qf_lra_spider_benchmarks: "QF_LRA/spider_benchmarks",
    qf_lra_tm: "QF_LRA/TM",
    qf_lra_tta_startup: "QF_LRA/tta_startup",
    qf_lra_uart: "QF_LRA/uart",
    qf_rdl_check: "QF_RDL/check",
    qf_rdl_sal: "QF_RDL/sal",
    qf_rdl_scheduling: "QF_RDL/scheduling",
    qf_rdl_skdmxa: "QF_RDL/skdmxa",
    qf_rdl_skdmxa2: "QF_RDL/skdmxa2",
    qf_uf_20170829_rodin: "QF_UF/20170829-Rodin",
    qf_uf_2018_goel_hwbench: "QF_UF/2018-Goel-hwbench",
    qf_uf_eq_diamond: "QF_UF/eq_diamond",
    qf_ufidl_20210312_bouvier: "QF_UFIDL/20210312-Bouvier",
    qf_ufidl_mathsat_euflaarithmetic_vhard: "QF_UFIDL/mathsat/EufLaArithmetic/vhard",
    // qf_ufidl_pete: "QF_UFIDL/pete",
    // qf_ufidl_pete2: "QF_UFIDL/pete2",
    qf_ufidl_rds: "QF_UFIDL/RDS",
    // qf_ufidl_rtcl_b13_tf_100: "QF_UFIDL/RTCL/b13_tf_100",
    qf_ufidl_twosquares: "QF_UFIDL/TwoSquares",
    qf_ufidl_uclid: "QF_UFIDL/uclid",
    qf_ufidl_uclid2: "QF_UFIDL/uclid2",
    qf_ufidl_uclid_pred_aodv: "QF_UFIDL/UCLID-pred/aodv",
    qf_ufidl_uclid_pred_bakery: "QF_UFIDL/UCLID-pred/bakery",
    qf_ufidl_uclid_pred_brp: "QF_UFIDL/UCLID-pred/BRP",
    qf_ufidl_uclid_pred_dlx: "QF_UFIDL/UCLID-pred/DLX",
    qf_ufidl_uclid_pred_ibm_cache: "QF_UFIDL/UCLID-pred/ibm_cache",
    qf_ufidl_uclid_pred_ooo: "QF_UFIDL/UCLID-pred/OOO",
    qf_uflia_mathsat_euflaarithmetic_hard: "QF_UFLIA/mathsat/EufLaArithmetic/hard",
    qf_uflia_mathsat_euflaarithmetic_medium: "QF_UFLIA/mathsat/EufLaArithmetic/medium",
    qf_uflia_mathsat_hash: "QF_UFLIA/mathsat/Hash",
    qf_uflia_mathsat_wisa: "QF_UFLIA/mathsat/Wisa",
    qf_uflia_twosquares: "QF_UFLIA/TwoSquares",
    qf_uflia_wisas: "QF_UFLIA/wisas",
    qf_uflra_fft: "QF_UFLRA/FFT",
    qf_uflra_mathsat_randomcoupled: "QF_UFLRA/mathsat/RandomCoupled",
    qf_uflra_mathsat_randomdecoupled: "QF_UFLRA/mathsat/RandomDecoupled",
    qf_uf_neq: "QF_UF/NEQ",
    qf_uf_peq: "QF_UF/PEQ",
    qf_uf_qg_classification_loops6: "QF_UF/QG-classification/loops6",
    // qf_uf_qg_classification_qg5: "QF_UF/QG-classification/qg5",
    qf_uf_qg_classification_qg6: "QF_UF/QG-classification/qg6",
    qf_uf_qg_classification_qg7: "QF_UF/QG-classification/qg7",
    qf_uf_seq: "QF_UF/SEQ",
    qf_uf_typesafe: "QF_UF/TypeSafe",
    uf_20170428_barrett_cdt_cade2015_nada_afp_abstract_completeness:
        "UF/20170428-Barrett/cdt-cade2015/nada/afp/abstract_completeness",
    uf_20170428_barrett_cdt_cade2015_nada_afp_bindag:
        "UF/20170428-Barrett/cdt-cade2015/nada/afp/bindag",
    uf_20170428_barrett_cdt_cade2015_nada_afp_coinductive_list:
        "UF/20170428-Barrett/cdt-cade2015/nada/afp/coinductive_list",
    uf_20170428_barrett_cdt_cade2015_nada_afp_coinductive_list_prefix:
        "UF/20170428-Barrett/cdt-cade2015/nada/afp/coinductive_list_prefix",
    uf_20170428_barrett_cdt_cade2015_nada_afp_coinductive_stream:
        "UF/20170428-Barrett/cdt-cade2015/nada/afp/coinductive_stream",
    uf_20170428_barrett_cdt_cade2015_nada_afp_hamming_stream:
        "UF/20170428-Barrett/cdt-cade2015/nada/afp/hamming_stream",
    uf_20170428_barrett_cdt_cade2015_nada_afp_huffman:
        "UF/20170428-Barrett/cdt-cade2015/nada/afp/huffman",
    uf_20170428_barrett_cdt_cade2015_nada_afp_koenigslemma:
        "UF/20170428-Barrett/cdt-cade2015/nada/afp/koenigslemma",
    uf_20170428_barrett_cdt_cade2015_nada_afp_llist2:
        "UF/20170428-Barrett/cdt-cade2015/nada/afp/llist2",
    uf_20170428_barrett_cdt_cade2015_nada_afp_lmirror:
        "UF/20170428-Barrett/cdt-cade2015/nada/afp/lmirror",
    uf_20170428_barrett_cdt_cade2015_nada_afp_sorted_list_operations:
        "UF/20170428-Barrett/cdt-cade2015/nada/afp/sorted_list_operations",
    uf_20170428_barrett_cdt_cade2015_nada_afp_splay_tree_analysis:
        "UF/20170428-Barrett/cdt-cade2015/nada/afp/splay_tree_analysis",
    uf_20170428_barrett_cdt_cade2015_nada_afp_tllist:
        "UF/20170428-Barrett/cdt-cade2015/nada/afp/tllist",
    uf_20170428_barrett_cdt_cade2015_nada_distro_gram_lang:
        "UF/20170428-Barrett/cdt-cade2015/nada/distro/gram_lang",
    uf_20170428_barrett_cdt_cade2015_nada_distro_koenig:
        "UF/20170428-Barrett/cdt-cade2015/nada/distro/koenig",
    uf_20170428_barrett_cdt_cade2015_nada_distro_parallel:
        "UF/20170428-Barrett/cdt-cade2015/nada/distro/parallel",
    uf_20170428_barrett_cdt_cade2015_nada_distro_process:
        "UF/20170428-Barrett/cdt-cade2015/nada/distro/process",
    uf_20170428_barrett_cdt_cade2015_nada_distro_rbt_impl:
        "UF/20170428-Barrett/cdt-cade2015/nada/distro/rbt_impl",
    uf_20170428_barrett_cdt_cade2015_nada_distro_stream:
        "UF/20170428-Barrett/cdt-cade2015/nada/distro/stream",
    uf_20170428_barrett_cdt_cade2015_nada_distro_stream_processor:
        "UF/20170428-Barrett/cdt-cade2015/nada/distro/stream_processor",
    uf_20170428_barrett_cdt_cade2015_nada_gandl_bird_tree:
        "UF/20170428-Barrett/cdt-cade2015/nada/gandl/bird_tree",
    uf_20170428_barrett_cdt_cade2015_nada_gandl_cotree:
        "UF/20170428-Barrett/cdt-cade2015/nada/gandl/cotree",
    uf_20170428_barrett_cdt_cade2015_nada_gandl_stern_brocot_tree:
        "UF/20170428-Barrett/cdt-cade2015/nada/gandl/stern_brocot_tree",
    uf_20201221_induction_by_reflection_schoisswohl_reflectiveconjecture:
        "UF/20201221-induction-by-reflection-schoisswohl/reflectiveConjecture",
    uf_grasshopper_instantiated: "UF/grasshopper/instantiated",
    uf_grasshopper_uninstantiated: "UF/grasshopper/uninstantiated",
    ufidl_boogie: "UFIDL/boogie",
    ufidl_burns: "UFIDL/Burns",
    ufidl_ricartagrawala: "UFIDL/RicartAgrawala",
    ufidl_sledgehammer_qepres: "UFIDL/sledgehammer/QEpres",
    ufidl_sledgehammer_typesafe: "UFIDL/sledgehammer/TypeSafe",
    uflia_boogie: "UFLIA/boogie",
    uflia_check: "UFLIA/check",
    uflia_grasshopper_instantiated: "UFLIA/grasshopper/instantiated",
    uflia_grasshopper_uninstantiated: "UFLIA/grasshopper/uninstantiated",
    uflia_misc: "UFLIA/misc",
    uflia_ricartagrawala: "UFLIA/RicartAgrawala",
    uflia_sexpr: "UFLIA/sexpr",
    uflia_simplify: "UFLIA/simplify",
    uflia_simplify2_front_end_suite: "UFLIA/simplify2/front_end_suite",
    uflia_simplify2_small_suite: "UFLIA/simplify2/small_suite",
    uflia_sledgehammer_arrow_order: "UFLIA/sledgehammer/Arrow_Order",
    uflia_sledgehammer_fft: "UFLIA/sledgehammer/FFT",
    uflia_sledgehammer_fundamental_theorem_algebra:
        "UFLIA/sledgehammer/Fundamental_Theorem_Algebra",
    uflia_sledgehammer_hoare: "UFLIA/sledgehammer/Hoare",
    uflia_sledgehammer_ns_shared: "UFLIA/sledgehammer/NS_Shared",
    uflia_sledgehammer_qepres: "UFLIA/sledgehammer/QEpres",
    uflia_sledgehammer_strongnorm: "UFLIA/sledgehammer/StrongNorm",
    uflia_sledgehammer_twosquares: "UFLIA/sledgehammer/TwoSquares",
    uflia_sledgehammer_typesafe: "UFLIA/sledgehammer/TypeSafe",
    uflia_spec_sharp: "UFLIA/spec_sharp",
    uflia_tokeneer_admin: "UFLIA/tokeneer/admin",
    uflia_tokeneer_admintoken: "UFLIA/tokeneer/admintoken",
    uflia_tokeneer_admintoken_readandcheck: "UFLIA/tokeneer/admintoken/readandcheck",
    uflia_tokeneer_alarm: "UFLIA/tokeneer/alarm",
    uflia_tokeneer_auditlog: "UFLIA/tokeneer/auditlog",
    uflia_tokeneer_auditlog_addelementtologfile: "UFLIA/tokeneer/auditlog/addelementtologfile",
    uflia_tokeneer_auditlog_addelementtologfile_addelementtonextfile:
        "UFLIA/tokeneer/auditlog/addelementtologfile/addelementtonextfile",
    uflia_tokeneer_auditlog_init: "UFLIA/tokeneer/auditlog/init",
    uflia_tokeneer_auditlog_init_setfiledetails: "UFLIA/tokeneer/auditlog/init/setfiledetails",
    uflia_tokeneer_bio: "UFLIA/tokeneer/bio",
    uflia_tokeneer_cert: "UFLIA/tokeneer/cert",
    uflia_tokeneer_cert_attr_auth: "UFLIA/tokeneer/cert_/attr_/auth",
    uflia_tokeneer_cert_attr_auth_construct: "UFLIA/tokeneer/cert_/attr_/auth/construct",
    uflia_tokeneer_cert_attr_ianda: "UFLIA/tokeneer/cert_/attr_/ianda",
    uflia_tokeneer_cert_attr_priv: "UFLIA/tokeneer/cert_/attr_/priv",
    uflia_tokeneer_cert_id: "UFLIA/tokeneer/cert_/id",
    uflia_tokeneer_certificatestore: "UFLIA/tokeneer/certificatestore",
    uflia_tokeneer_certificatestore_getnextserialnumber:
        "UFLIA/tokeneer/certificatestore/getnextserialnumber",
    uflia_tokeneer_clock: "UFLIA/tokeneer/clock",
    uflia_tokeneer_configdata: "UFLIA/tokeneer/configdata",
    uflia_tokeneer_configdata_init: "UFLIA/tokeneer/configdata/init",
    uflia_tokeneer_configdata_validatefile: "UFLIA/tokeneer/configdata/validatefile",
    uflia_tokeneer_configdata_writefile: "UFLIA/tokeneer/configdata/writefile",
    uflia_tokeneer_configuration: "UFLIA/tokeneer/configuration",
    uflia_tokeneer_display: "UFLIA/tokeneer/display",
    uflia_tokeneer_door: "UFLIA/tokeneer/door",
    uflia_tokeneer_enclave: "UFLIA/tokeneer/enclave",
    uflia_tokeneer_enclave_archivelogop: "UFLIA/tokeneer/enclave/archivelogop",
    uflia_tokeneer_enclave_startadminactivity: "UFLIA/tokeneer/enclave/startadminactivity",
    uflia_tokeneer_enrolment: "UFLIA/tokeneer/enrolment",
    uflia_tokeneer_enrolment_validate: "UFLIA/tokeneer/enrolment/validate",
    uflia_tokeneer_keyboard: "UFLIA/tokeneer/keyboard",
    uflia_tokeneer_keystore: "UFLIA/tokeneer/keystore",
    uflia_tokeneer_keystore_digest: "UFLIA/tokeneer/keystore/digest",
    uflia_tokeneer_latch: "UFLIA/tokeneer/latch",
    uflia_tokeneer_poll: "UFLIA/tokeneer/poll",
    uflia_tokeneer_screen: "UFLIA/tokeneer/screen",
    uflia_tokeneer_stats: "UFLIA/tokeneer/stats",
    uflia_tokeneer_tismain: "UFLIA/tokeneer/tismain",
    uflia_tokeneer_tismain_processing: "UFLIA/tokeneer/tismain/processing",
    uflia_tokeneer_tokenreader: "UFLIA/tokeneer/tokenreader",
    uflia_tokeneer_tokenreader_init: "UFLIA/tokeneer/tokenreader/init",
    uflia_tokeneer_tokenreader_poll: "UFLIA/tokeneer/tokenreader/poll",
    uflia_tokeneer_tokenreader_poll_checkcardstate:
        "UFLIA/tokeneer/tokenreader/poll/checkcardstate",
    uflia_tokeneer_tokenreader_poll_processreaderstatechange:
        "UFLIA/tokeneer/tokenreader/poll/processreaderstatechange",
    uflia_tokeneer_updates: "UFLIA/tokeneer/updates",
    uflia_tokeneer_userentry: "UFLIA/tokeneer/userentry",
    uflia_tokeneer_usertoken: "UFLIA/tokeneer/usertoken",
    uflia_tokeneer_usertoken_readandcheck: "UFLIA/tokeneer/usertoken/readandcheck",
    uflia_tokeneer_usertoken_readandcheckauthcert: "UFLIA/tokeneer/usertoken/readandcheckauthcert",
    uflia_tptp: "UFLIA/tptp",
    uflra_fft: "UFLRA/FFT",
    uf_misc: "UF/misc",
    uf_sledgehammer_arrow_order: "UF/sledgehammer/Arrow_Order",
    uf_sledgehammer_fft: "UF/sledgehammer/FFT",
    uf_sledgehammer_fundamental_theorem_algebra: "UF/sledgehammer/Fundamental_Theorem_Algebra",
    uf_sledgehammer_hoare: "UF/sledgehammer/Hoare",
    uf_sledgehammer_ns_shared: "UF/sledgehammer/NS_Shared",
    uf_sledgehammer_qepres: "UF/sledgehammer/QEpres",
    uf_sledgehammer_strongnorm: "UF/sledgehammer/StrongNorm",
    uf_sledgehammer_twosquares: "UF/sledgehammer/TwoSquares",
    uf_sledgehammer_typesafe: "UF/sledgehammer/TypeSafe",
}
