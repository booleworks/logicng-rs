use std::fs;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use itertools::Itertools;
use logicng::formulas::{EncodedFormula, FormulaFactory};
use logicng::io::read_formula;
use logicng::solver::maxsat::{Algorithm, MaxSatSolver};

/// Test for parallel model maximization with the MaxSat solver
/// on a multi-threading formula factory.
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
        let handle = std::thread::spawn(move || {
            loop {
                let c = counter_l.fetch_add(1, Ordering::SeqCst);
                if c >= paths_l.len() {
                    break;
                }
                let formula = read_formula(&paths_l[c], &f_l).unwrap();
                let variables = formula.variables(&f_l);
                let mut solver = MaxSatSolver::new(Algorithm::Oll).unwrap();
                solver.add_hard_formula(formula, &f_l).unwrap();
                for var in &*variables {
                    solver.add_soft_formula(1, EncodedFormula::from(var.pos_lit()), &f_l).unwrap();
                }
                let _res = solver.solve().unwrap();
            }
        });
        threads.push(handle);
    }

    for thread in threads {
        thread.join().expect("thread failed!");
    }
    println!("MaxSAT, {thread_count} Threads: {}s", start.elapsed().as_secs_f64());
}
