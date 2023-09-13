use std::fs;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use itertools::Itertools;
use logicng::formulas::FormulaFactory;
use logicng::io::read_formula;
use logicng::solver::functions::OptimizationFunction;
use logicng::solver::minisat::MiniSat;

/// Test for parallel model maximization with the SAT solver's
/// optimization function on a multi-threading formula factory.
fn main() {
    for threads in &[1, 2, 4, 6, 8, 10] {
        maximize(*threads as usize);
    }
}

fn maximize(thread_count: usize) {
    let f = Arc::new(FormulaFactory::new());
    let paths = Arc::new(
        fs::read_dir("./resources/formula_suite_1/").unwrap().map(|p| String::from(p.unwrap().path().to_str().unwrap())).collect_vec(),
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
            let literals = formula.variables(&f_l).iter().map(|v| v.pos_lit()).collect_vec();
            let mut solver = MiniSat::new();
            solver.add(formula, &f_l);
            let _model = solver.optimize(&f_l, &OptimizationFunction::maximize(literals));
        });
        threads.push(handle);
    }

    for thread in threads {
        thread.join().expect("thread failed!");
    }
    println!("Solver function, {thread_count} Threads: {}s", start.elapsed().as_secs_f64());
}
