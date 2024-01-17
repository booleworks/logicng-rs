use std::hint::black_box;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use fastrand::shuffle;
use logicng::formulas::{EncodedFormula, FormulaFactory};
use logicng::util::formula_randomizer::{FormulaRandomizer, FormulaRandomizerConfig};

pub fn factory_benchmarks(c: &mut Criterion) {
    bench_vars(c);
    bench_nary(c);
    bench_pbc(c);
}

fn bench_vars(c: &mut Criterion) {
    let mut var_group = c.benchmark_group("Variable Creation");
    for size in [1_000, 10_000, 100_000] {
        let names = (0..size).map(|i| i.to_string()).collect::<Vec<String>>();
        var_group.throughput(criterion::Throughput::Elements(size as u64));
        var_group.bench_with_input(BenchmarkId::new("Fresh Variables", size), &names, |b, names| {
            b.iter_batched(
                FormulaFactory::new,
                |f| {
                    for name in names {
                        f.variable(black_box(name));
                    }
                },
                criterion::BatchSize::SmallInput,
            )
        });
    }

    for size in [1_000, 10_000, 100_000] {
        let mut rng = fastrand::Rng::new();
        rng.seed(0);
        let mut names = (0..size).map(|s| (s / 2).to_string()).collect::<Box<[_]>>();
        rng.shuffle(&mut names);
        var_group.throughput(criterion::Throughput::Elements(size as u64));
        var_group.bench_with_input(BenchmarkId::new("Mixed Variables", size), &names, |b, names| {
            b.iter_batched(
                FormulaFactory::new,
                |f| {
                    for name in names.iter() {
                        f.variable(black_box(name));
                    }
                },
                criterion::BatchSize::SmallInput,
            )
        });
    }
}

fn bench_nary(c: &mut Criterion) {
    let mut nary_group = c.benchmark_group("Nary Constructors");
    for size in [1_000, 10_000, 100_000] {
        if size >= 100_000 {
            nary_group.measurement_time(Duration::from_secs(10));
        } else {
            nary_group.measurement_time(Duration::from_secs(5));
        }

        nary_group.bench_function(BenchmarkId::new("And Constructor (Variant 1)", size), |b| {
            b.iter_batched(
                || {
                    let f = FormulaFactory::new();
                    let vars = (0..size).map(|i| f.variable(&i.to_string())).collect::<Vec<_>>();
                    (f, vars)
                },
                |(f, vars)| {
                    f.and(vars);
                },
                criterion::BatchSize::SmallInput,
            )
        });
    }

    for size in [1_000, 10_000, 100_000] {
        if size >= 100_000 {
            nary_group.measurement_time(Duration::from_secs(10));
        } else {
            nary_group.measurement_time(Duration::from_secs(5));
        }

        nary_group.bench_function(BenchmarkId::new("And Constructor (Variant 2)", size), |b| {
            b.iter_batched(
                || {
                    let mut rng = fastrand::Rng::new();
                    rng.seed(0);
                    let f = FormulaFactory::new();
                    let mut vars = (0..size).map(|i| f.variable(&(i / 2).to_string())).collect::<Vec<_>>();
                    shuffle(&mut vars);
                    (f, vars)
                },
                |(f, vars)| {
                    f.and(vars);
                },
                criterion::BatchSize::SmallInput,
            )
        });
    }

    for amount in [100, 1_000, 10_000] {
        let mut rng = fastrand::Rng::new();
        rng.seed(0);
        let mut ands = Vec::new();
        for _ in 0..amount {
            let mut and = Vec::new();
            let len = rng.i64(0..10);
            for _ in 0..len {
                and.push(rng.i64(0..(amount * 10)));
            }
            ands.push(and);
        }
        nary_group.throughput(criterion::Throughput::Elements(amount as u64));

        nary_group.bench_function(BenchmarkId::new("Many small And Constructions", amount), |b| {
            b.iter_batched(
                || {
                    let f = FormulaFactory::new();
                    let vars_for_and =
                        ands.iter().map(|a| a.iter().map(|v| f.variable(&v.to_string())).collect::<Box<[_]>>()).collect::<Box<[_]>>();
                    (f, vars_for_and)
                },
                |(f, vars_for_and)| {
                    for vars in vars_for_and.iter() {
                        black_box(f.and(black_box(vars.iter())));
                    }
                },
                criterion::BatchSize::SmallInput,
            )
        });
    }
}

fn bench_pbc(c: &mut Criterion) {
    let mut cc_group = c.benchmark_group("Cc Constructors");
    for size in [1_000, 10_000, 100_000] {
        if size >= 100_000 {
            cc_group.measurement_time(Duration::from_secs(10));
        } else {
            cc_group.measurement_time(Duration::from_secs(5));
        }
        cc_group.bench_function(BenchmarkId::new("Cc Constructor (Variant 1)", size), |b| {
            b.iter_batched(
                || {
                    let f = FormulaFactory::new();
                    let vars = (0..size).map(|i| f.var(&i.to_string())).collect::<Vec<_>>();
                    (f, vars)
                },
                |(f, vars)| {
                    f.amo(vars);
                },
                criterion::BatchSize::SmallInput,
            )
        });
    }

    for size in [1_000, 10_000, 100_000] {
        if size >= 100_000 {
            cc_group.measurement_time(Duration::from_secs(10));
        } else {
            cc_group.measurement_time(Duration::from_secs(5));
        }
        cc_group.bench_function(BenchmarkId::new("Cc Constructor (Variant 2)", size), |b| {
            b.iter_batched(
                || {
                    let mut rng = fastrand::Rng::new();
                    rng.seed(0);
                    let f = FormulaFactory::new();
                    let mut vars = (0..size).map(|i| f.var(&(i / 2).to_string())).collect::<Vec<_>>();
                    shuffle(&mut vars);
                    (f, vars)
                },
                |(f, vars)| {
                    f.amo(vars);
                },
                criterion::BatchSize::SmallInput,
            )
        });
    }

    cc_group.measurement_time(Duration::from_secs(5));
    for amount in [100, 1_000, 10_000] {
        let mut rng = fastrand::Rng::new();
        rng.seed(0);
        let mut ccs = Vec::new();
        for _ in 0..amount {
            let mut cc = Vec::new();
            let len = rng.i64(0..10);
            for _ in 0..len {
                cc.push(rng.i64(0..(amount * 10)));
            }
            ccs.push(cc);
        }
        cc_group.throughput(criterion::Throughput::Elements(amount as u64));


        cc_group.bench_function(BenchmarkId::new("Many small Cc Constructions", amount), |b| {
            b.iter_batched(
                || {
                    let f = FormulaFactory::new();
                    let vars_for_cc = ccs.iter().map(|a| a.iter().map(|v| f.var(&v.to_string())).collect::<Vec<_>>()).collect::<Vec<_>>();
                    (f, vars_for_cc)
                },
                |(f, vars_for_cc)| {
                    for vars in vars_for_cc.into_iter() {
                        black_box(f.amo(black_box(vars)));
                    }
                },
                criterion::BatchSize::SmallInput,
            )
        });
    }
}

criterion_group!(benches, factory_benchmarks);
criterion_main!(benches);
