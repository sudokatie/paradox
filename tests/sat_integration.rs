//! Integration tests for SAT solving.

use paradox::{parse_dimacs, solver::Solver, solver::SolveResult};

fn solve_dimacs(input: &str) -> SolveResult {
    let formula = parse_dimacs(input).expect("Failed to parse DIMACS");
    let mut solver = Solver::new(formula);
    solver.solve()
}

#[test]
fn test_simple_sat() {
    let input = r#"
        p cnf 3 2
        1 2 0
        -1 3 0
    "#;
    let result = solve_dimacs(input);
    assert!(matches!(result, SolveResult::Sat(_)));
}

#[test]
fn test_simple_unsat() {
    let input = r#"
        p cnf 1 2
        1 0
        -1 0
    "#;
    let result = solve_dimacs(input);
    assert!(matches!(result, SolveResult::Unsat));
}

#[test]
fn test_empty_formula() {
    let input = "p cnf 0 0\n";
    let result = solve_dimacs(input);
    assert!(matches!(result, SolveResult::Sat(_)));
}

#[test]
fn test_single_unit_clause() {
    let input = r#"
        p cnf 1 1
        1 0
    "#;
    let result = solve_dimacs(input);
    match result {
        SolveResult::Sat(model) => {
            assert!(model.len() >= 1);
            assert!(model[0]); // Variable 1 must be true
        }
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_two_unit_clauses_sat() {
    let input = r#"
        p cnf 2 2
        1 0
        2 0
    "#;
    let result = solve_dimacs(input);
    match result {
        SolveResult::Sat(model) => {
            assert!(model.len() >= 2);
            assert!(model[0]); // Variable 1 must be true
            assert!(model[1]); // Variable 2 must be true
        }
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_pigeonhole_2_1() {
    // 2 pigeons, 1 hole - UNSAT
    let input = r#"
        p cnf 2 3
        1 0
        2 0
        -1 -2 0
    "#;
    let result = solve_dimacs(input);
    assert!(matches!(result, SolveResult::Unsat));
}

#[test]
fn test_pigeonhole_3_2() {
    // 3 pigeons, 2 holes - UNSAT
    // Variables: p(i,j) = pigeon i in hole j
    // p(1,1)=1, p(1,2)=2, p(2,1)=3, p(2,2)=4, p(3,1)=5, p(3,2)=6
    let input = r#"
        p cnf 6 9
        1 2 0
        3 4 0
        5 6 0
        -1 -3 0
        -1 -5 0
        -3 -5 0
        -2 -4 0
        -2 -6 0
        -4 -6 0
    "#;
    let result = solve_dimacs(input);
    assert!(matches!(result, SolveResult::Unsat));
}

#[test]
fn test_3sat_satisfiable() {
    let input = r#"
        p cnf 5 5
        1 2 3 0
        -1 2 4 0
        1 -2 5 0
        -3 4 5 0
        1 3 -4 0
    "#;
    let result = solve_dimacs(input);
    assert!(matches!(result, SolveResult::Sat(_)));
}

#[test]
fn test_model_verification() {
    let input = r#"
        p cnf 3 3
        1 2 0
        -1 3 0
        2 3 0
    "#;
    let result = solve_dimacs(input);
    match result {
        SolveResult::Sat(model) => {
            // Verify model satisfies all clauses
            // Clause 1: x1 OR x2
            assert!(model.get(0).copied().unwrap_or(false) || model.get(1).copied().unwrap_or(false));
            // Clause 2: NOT x1 OR x3
            assert!(!model.get(0).copied().unwrap_or(true) || model.get(2).copied().unwrap_or(false));
            // Clause 3: x2 OR x3
            assert!(model.get(1).copied().unwrap_or(false) || model.get(2).copied().unwrap_or(false));
        }
        _ => panic!("Expected SAT"),
    }
}

#[test]
fn test_large_clause() {
    // One clause with many literals
    let input = r#"
        p cnf 10 1
        1 2 3 4 5 6 7 8 9 10 0
    "#;
    let result = solve_dimacs(input);
    assert!(matches!(result, SolveResult::Sat(_)));
}

#[test]
fn test_all_negative_clause() {
    let input = r#"
        p cnf 3 1
        -1 -2 -3 0
    "#;
    let result = solve_dimacs(input);
    assert!(matches!(result, SolveResult::Sat(_)));
}

#[test]
fn test_chain_implications() {
    // x1 -> x2 -> x3 -> x4, x1, NOT x4
    let input = r#"
        p cnf 4 5
        -1 2 0
        -2 3 0
        -3 4 0
        1 0
        -4 0
    "#;
    let result = solve_dimacs(input);
    assert!(matches!(result, SolveResult::Unsat));
}
