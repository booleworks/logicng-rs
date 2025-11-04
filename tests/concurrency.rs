use std::fs;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use itertools::Itertools;
use logicng::formulas::FormulaFactory;
use logicng::io::read_formula;

#[test]
#[cfg_attr(not(feature = "long_running_tests"), ignore)]
fn parsing_test() {
    let f = Arc::new(FormulaFactory::new());
    parse_files(1, &f);
    for thread_count in 2..=8 {
        let f2 = Arc::new(FormulaFactory::new());
        parse_files(thread_count, &f2);
        assert_eq!(f.print_stats(), f2.print_stats());
    }
}

fn parse_files(thread_count: usize, f: &Arc<FormulaFactory>) {
    let paths = Arc::new(
        fs::read_dir("./resources/formula_suite_1").unwrap().map(|p| String::from(p.unwrap().path().to_str().unwrap())).collect_vec(),
    );
    let counter = Arc::new(AtomicUsize::new(0));
    let mut threads = Vec::with_capacity(thread_count);
    for _ in 0..thread_count {
        let counter_l = Arc::clone(&counter);
        let f_l = Arc::clone(f);
        let paths_l = Arc::clone(&paths);
        let handle = std::thread::spawn(move || {
            loop {
                let c = counter_l.fetch_add(1, Ordering::SeqCst);
                if c >= paths_l.len() {
                    break;
                }
                read_formula(&paths_l[c], &f_l).unwrap();
            }
        });
        threads.push(handle);
    }
    for thread in threads {
        thread.join().expect("thread paniced");
    }
}
