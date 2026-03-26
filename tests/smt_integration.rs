//! Integration tests for SMT solving.

use paradox::{parse_smtlib, dpll_t::DpllT, solver::SolveResult};

fn solve_smt(input: &str) -> SolveResult {
    let problem = parse_smtlib(input).expect("Failed to parse SMT-LIB");
    let mut solver = DpllT::new(problem);
    solver.solve()
}

#[test]
fn test_bool_sat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const p Bool)
        (assert p)
        (check-sat)
    "#;
    let result = solve_smt(input);
    assert!(matches!(result, SolveResult::Sat(_)));
}

#[test]
fn test_bool_unsat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const p Bool)
        (assert p)
        (assert (not p))
        (check-sat)
    "#;
    let result = solve_smt(input);
    assert!(matches!(result, SolveResult::Unsat));
}

#[test]
fn test_bool_and() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const p Bool)
        (declare-const q Bool)
        (assert (and p q))
        (check-sat)
    "#;
    let result = solve_smt(input);
    assert!(matches!(result, SolveResult::Sat(_)));
}

#[test]
fn test_bool_or() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const p Bool)
        (declare-const q Bool)
        (assert (or p q))
        (assert (not p))
        (check-sat)
    "#;
    let result = solve_smt(input);
    assert!(matches!(result, SolveResult::Sat(_)));
}

#[test]
fn test_bool_implies_unsat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const p Bool)
        (declare-const q Bool)
        (assert (=> p q))
        (assert p)
        (assert (not q))
        (check-sat)
    "#;
    let result = solve_smt(input);
    assert!(matches!(result, SolveResult::Unsat));
}

#[test]
fn test_bool_ite() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const c Bool)
        (declare-const x Bool)
        (assert (ite c x (not x)))
        (check-sat)
    "#;
    let result = solve_smt(input);
    assert!(matches!(result, SolveResult::Sat(_)));
}

#[test]
fn test_multiple_assertions() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const c Bool)
        (assert a)
        (assert (or (not a) b))
        (assert (or (not b) c))
        (assert (not c))
        (check-sat)
    "#;
    let result = solve_smt(input);
    assert!(matches!(result, SolveResult::Unsat));
}

#[test]
fn test_true_literal() {
    let input = r#"
        (set-logic QF_UF)
        (assert true)
        (check-sat)
    "#;
    let result = solve_smt(input);
    assert!(matches!(result, SolveResult::Sat(_)));
}

#[test]
fn test_false_literal() {
    let input = r#"
        (set-logic QF_UF)
        (assert false)
        (check-sat)
    "#;
    let result = solve_smt(input);
    assert!(matches!(result, SolveResult::Unsat));
}

#[test]
fn test_qf_lia_simple() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 0))
        (check-sat)
    "#;
    let result = solve_smt(input);
    // Should be SAT - x can be any positive integer
    assert!(matches!(result, SolveResult::Sat(_)) || matches!(result, SolveResult::Unknown));
}

#[test]
fn test_qf_bv_simple() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #xFF))
        (check-sat)
    "#;
    let result = solve_smt(input);
    assert!(matches!(result, SolveResult::Sat(_)) || matches!(result, SolveResult::Unknown));
}

#[test]
fn test_nested_and_or() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const c Bool)
        (assert (and (or a b) (or (not a) c)))
        (check-sat)
    "#;
    let result = solve_smt(input);
    assert!(matches!(result, SolveResult::Sat(_)));
}

#[test]
fn test_xor() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (xor a b))
        (assert a)
        (assert b)
        (check-sat)
    "#;
    let result = solve_smt(input);
    assert!(matches!(result, SolveResult::Unsat));
}
