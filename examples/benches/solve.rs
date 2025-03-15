use std::fs;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use itertools::Itertools;
use logicng::formulas::FormulaFactory;
use logicng::io::read_formula;
use logicng::solver::lng_core_solver::SatSolver;

pub fn main() {
    for threads in &[1, 2, 4, 8] {
        solve(*threads as usize);
    }
}

fn solve(thread_count: usize) {
    let f = Arc::new(FormulaFactory::new());
    let formulas = Arc::new(
        fs::read_dir("./resources/formula_suite_1/")
            .unwrap()
            .map(|p| read_formula(&String::from(p.unwrap().path().to_str().unwrap()), &f).unwrap())
            .collect_vec(),
    );

    let start = std::time::Instant::now();
    let counter = Arc::new(AtomicUsize::new(0));
    let mut threads = Vec::with_capacity(thread_count);

    for _ in 0..thread_count {
        let counter_l = Arc::clone(&counter);
        let f_l = Arc::clone(&f);
        let formulas_l = Arc::clone(&formulas);
        let handle = std::thread::spawn(move || loop {
            let c = counter_l.fetch_add(1, Ordering::SeqCst);
            if c >= formulas_l.len() {
                break;
            }
            let formula = formulas_l[c];
            let mut solver = SatSolver::<()>::new();
            solver.add_formula(formula, &f_l);
            let _ = solver.sat(&f_l);
        });
        threads.push(handle);
    }

    for thread in threads {
        thread.join().expect("thread failed!");
    }
    println!("MiniSat solve, {thread_count} Threads: {}s", start.elapsed().as_secs_f64());
}
