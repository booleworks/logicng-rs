use std::fs;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use itertools::Itertools;
use logicng::formulas::FormulaFactory;
use logicng::io::read_formula;
use logicng::knowledge_compilation::dnnf::{compile_dnnf, count};
use logicng::operations::transformations::{pure_expansion, AdvancedFactorizationConfig, CnfAlgorithm, CnfEncoder};

/// Test for parallel model counting with DNNF compilation
/// on a multi-threading formula factory.
pub fn main() {
    for threads in &[1, 2, 4, 6, 8, 10] {
        parallel(*threads as usize);
    }
}

pub fn parallel(thread_count: usize) {
    let f = Arc::new(FormulaFactory::new());
    let paths = Arc::new(
        fs::read_dir("./resources/formula_suite_1").unwrap().map(|p| String::from(p.unwrap().path().to_str().unwrap())).collect_vec(),
    );

    let start = std::time::Instant::now();
    let counter = Arc::new(AtomicUsize::new(0));
    let mut threads = Vec::with_capacity(thread_count);
    for _ in 0..thread_count {
        let counter_l = Arc::clone(&counter);
        let f_l = Arc::clone(&f);
        let paths_l = Arc::clone(&paths);
        let handle = std::thread::spawn(move || loop {
            let c = counter_l.fetch_add(1, Ordering::SeqCst);
            if c >= paths_l.len() {
                break;
            }
            let formula = read_formula(&paths_l[c], &f_l).unwrap();
            let expanded = pure_expansion(formula, &f_l);
            let mut cnf_encoder =
                CnfEncoder::new(CnfAlgorithm::Advanced(AdvancedFactorizationConfig::default().fallback_algorithm(CnfAlgorithm::Tseitin)));
            let cnf_formula = cnf_encoder.transform(expanded, &f_l);
            let dnnf = compile_dnnf(cnf_formula, &f_l);
            count(&dnnf, &f_l);
        });
        threads.push(handle);
    }
    for thread in threads {
        thread.join().expect("thread failed!");
    }
    println!("Model counting, {thread_count} Threads: {}s", start.elapsed().as_secs_f64());
}
