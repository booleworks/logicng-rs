use std::hint::black_box;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use logicng::formulas::FormulaFactory;
use logicng::io::read_formula;

pub fn parser_benchmarks(c: &mut Criterion) {
    parse_files(c);
}

fn parse_files(c: &mut Criterion) {
    let mut group = c.benchmark_group("Parse Files");

    for file_name in ["large_formula.txt", "large_formula2.txt"] {
        group.bench_with_input(BenchmarkId::new("File", file_name), &file_name, |b, _| {
            b.iter_batched(
                FormulaFactory::new,
                |f| {
                    black_box(read_formula(&format!("resources/formulas/{file_name}"), &f).unwrap());
                },
                criterion::BatchSize::SmallInput,
            )
        });
    }
}

criterion_group!(benches, parser_benchmarks);
criterion_main!(benches);
