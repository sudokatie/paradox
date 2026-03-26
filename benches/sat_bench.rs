//! SAT solving benchmarks.

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use paradox::{parse_dimacs, solver::Solver};

fn generate_random_3sat(num_vars: usize, num_clauses: usize, seed: u64) -> String {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let mut result = format!("p cnf {} {}\n", num_vars, num_clauses);

    let mut hasher = DefaultHasher::new();
    seed.hash(&mut hasher);

    for i in 0..num_clauses {
        let mut clause_hasher = DefaultHasher::new();
        (seed, i).hash(&mut clause_hasher);
        let h = clause_hasher.finish();

        let v1 = ((h % num_vars as u64) + 1) as i32;
        let v2 = (((h >> 16) % num_vars as u64) + 1) as i32;
        let v3 = (((h >> 32) % num_vars as u64) + 1) as i32;

        let s1 = if (h >> 48) & 1 == 0 { 1 } else { -1 };
        let s2 = if (h >> 49) & 1 == 0 { 1 } else { -1 };
        let s3 = if (h >> 50) & 1 == 0 { 1 } else { -1 };

        result.push_str(&format!("{} {} {} 0\n", s1 * v1, s2 * v2, s3 * v3));
    }

    result
}

fn generate_pigeonhole(pigeons: usize, holes: usize) -> String {
    let num_vars = pigeons * holes;
    let mut clauses = Vec::new();

    // Each pigeon must be in at least one hole
    for p in 0..pigeons {
        let mut clause = Vec::new();
        for h in 0..holes {
            clause.push((p * holes + h + 1) as i32);
        }
        clauses.push(clause);
    }

    // At most one pigeon per hole
    for h in 0..holes {
        for p1 in 0..pigeons {
            for p2 in (p1 + 1)..pigeons {
                let v1 = (p1 * holes + h + 1) as i32;
                let v2 = (p2 * holes + h + 1) as i32;
                clauses.push(vec![-v1, -v2]);
            }
        }
    }

    let mut result = format!("p cnf {} {}\n", num_vars, clauses.len());
    for clause in clauses {
        for lit in clause {
            result.push_str(&format!("{} ", lit));
        }
        result.push_str("0\n");
    }
    result
}

fn bench_simple(c: &mut Criterion) {
    let input = r#"
        p cnf 3 2
        1 2 0
        -1 3 0
    "#;

    c.bench_function("simple_3var", |b| {
        b.iter(|| {
            let formula = parse_dimacs(black_box(input)).unwrap();
            let mut solver = Solver::new(formula);
            solver.solve()
        })
    });
}

fn bench_random_3sat(c: &mut Criterion) {
    let mut group = c.benchmark_group("random_3sat");

    for &(vars, clauses) in &[(20, 85), (50, 215), (100, 430)] {
        let input = generate_random_3sat(vars, clauses, 42);

        group.bench_with_input(
            BenchmarkId::new("vars", vars),
            &input,
            |b, input| {
                b.iter(|| {
                    let formula = parse_dimacs(black_box(input)).unwrap();
                    let mut solver = Solver::new(formula);
                    solver.solve()
                })
            },
        );
    }

    group.finish();
}

fn bench_pigeonhole(c: &mut Criterion) {
    let mut group = c.benchmark_group("pigeonhole");

    for &(pigeons, holes) in &[(3, 2), (4, 3), (5, 4)] {
        let input = generate_pigeonhole(pigeons, holes);

        group.bench_with_input(
            BenchmarkId::new("pigeons", pigeons),
            &input,
            |b, input| {
                b.iter(|| {
                    let formula = parse_dimacs(black_box(input)).unwrap();
                    let mut solver = Solver::new(formula);
                    solver.solve()
                })
            },
        );
    }

    group.finish();
}

fn bench_unit_propagation(c: &mut Criterion) {
    // Many unit clauses that chain together
    let mut input = String::from("p cnf 100 100\n");
    for i in 1..=100 {
        input.push_str(&format!("{} 0\n", i));
    }

    c.bench_function("unit_propagation_100", |b| {
        b.iter(|| {
            let formula = parse_dimacs(black_box(&input)).unwrap();
            let mut solver = Solver::new(formula);
            solver.solve()
        })
    });
}

criterion_group!(
    benches,
    bench_simple,
    bench_random_3sat,
    bench_pigeonhole,
    bench_unit_propagation
);

criterion_main!(benches);
