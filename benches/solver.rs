use std::hint::black_box;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use logicng::formulas::FormulaFactory;
use logicng::io::read_formula;
use logicng::solver::minisat::SolverCnfMethod::FullPgOnSolver;
use logicng::solver::minisat::{MiniSat, MiniSatConfig};

pub fn solver_benchmarks(c: &mut Criterion) {
    pg_on_solver(c);
}

fn pg_on_solver(c: &mut Criterion) {
    let mut group = c.benchmark_group("PG on Solver");

    for file_name in ["large_formula.txt", "large_formula2.txt", "large_formula2-split.txt"] {
        let f = FormulaFactory::new();
        let formula = read_formula(&format!("resources/formulas/{file_name}"), &f).unwrap();
        group.measurement_time(Duration::from_secs(30));
        group.sample_size(20);
        group.bench_with_input(BenchmarkId::new("File", file_name), &file_name, |b, _| {
            b.iter_batched(
                || MiniSat::from_config(MiniSatConfig::default().cnf_method(FullPgOnSolver)),
                |mut solver| {
                    solver.add(formula, &f);
                    black_box(solver.sat());
                },
                criterion::BatchSize::SmallInput,
            )
        });

        group.bench_with_input(BenchmarkId::new("File2", file_name), &file_name, |b, _| {
            b.iter_batched(
                || {
                    let f = FormulaFactory::new();
                    let formula = read_formula(&format!("resources/formulas/{file_name}"), &f).unwrap();
                    let solver = MiniSat::from_config(MiniSatConfig::default().cnf_method(FullPgOnSolver));
                    (f, formula, solver)
                },
                |(f, formula, mut solver)| {
                    solver.add(formula, &f);
                    black_box(solver.sat());
                },
                criterion::BatchSize::SmallInput,
            )
        });
    }
}

criterion_group!(benches, solver_benchmarks);
criterion_main!(benches);
