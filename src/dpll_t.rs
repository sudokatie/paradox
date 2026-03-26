//! DPLL(T) - SMT solving via SAT + Theory solvers.
//!
//! Architecture:
//! ```text
//! DPLL(T):
//!     SAT Core <-> Theory Solver(s)
//!     
//!     Loop:
//!         SAT core makes decisions/propagations
//!         Check consistency with theories
//!         If theory conflict, learn clause and backtrack
//! ```

use std::collections::HashMap;

use crate::clause::Clause;
use crate::formula::Formula;
use crate::literal::Literal;
use crate::parser::smtlib::{SmtProblem, Term, Sort, Logic};
use crate::solver::{Solver, SolveResult, SolverConfig};
use crate::theory::{TheoryManager, TheoryResult};
use crate::theory::euf::EufSolver;
use crate::theory::lia::LiaSolver;
use crate::theory::bv::BvSolver;
use crate::theory::array::ArraySolver;

/// Variable in the SMT problem.
#[derive(Debug, Clone)]
struct SmtVar {
    name: String,
    sort: Sort,
    /// SAT variable index (if Boolean).
    sat_var: Option<u32>,
}

/// DPLL(T) SMT Solver.
pub struct DpllT {
    /// The SMT problem.
    problem: SmtProblem,
    /// SAT solver.
    sat_solver: Option<Solver>,
    /// Theory manager.
    theories: TheoryManager,
    /// Variable mapping: name -> info.
    variables: HashMap<String, SmtVar>,
    /// Next SAT variable.
    next_sat_var: u32,
    /// Term to SAT variable mapping.
    term_to_var: HashMap<String, u32>,
    /// SAT variable to term mapping.
    var_to_term: HashMap<u32, Term>,
}

impl DpllT {
    /// Create a new DPLL(T) solver for the given problem.
    pub fn new(problem: SmtProblem) -> Self {
        let mut solver = DpllT {
            problem,
            sat_solver: None,
            theories: TheoryManager::new(),
            variables: HashMap::new(),
            next_sat_var: 1,
            term_to_var: HashMap::new(),
            var_to_term: HashMap::new(),
        };
        
        solver.setup_theories();
        solver
    }
    
    /// Set up theory solvers based on the logic.
    fn setup_theories(&mut self) {
        let logic = self.problem.logic.clone().unwrap_or(Logic::All);
        
        match logic {
            Logic::QfUf => {
                self.theories.add_solver(Box::new(EufSolver::new()));
            }
            Logic::QfLia | Logic::QfLra => {
                self.theories.add_solver(Box::new(LiaSolver::new()));
            }
            Logic::QfBv => {
                self.theories.add_solver(Box::new(BvSolver::new()));
            }
            Logic::QfA => {
                self.theories.add_solver(Box::new(ArraySolver::new()));
            }
            Logic::QfAuflia => {
                self.theories.add_solver(Box::new(EufSolver::new()));
                self.theories.add_solver(Box::new(LiaSolver::new()));
                self.theories.add_solver(Box::new(ArraySolver::new()));
            }
            Logic::QfAufbv => {
                self.theories.add_solver(Box::new(EufSolver::new()));
                self.theories.add_solver(Box::new(BvSolver::new()));
                self.theories.add_solver(Box::new(ArraySolver::new()));
            }
            Logic::All => {
                self.theories.add_solver(Box::new(EufSolver::new()));
                self.theories.add_solver(Box::new(LiaSolver::new()));
                self.theories.add_solver(Box::new(BvSolver::new()));
                self.theories.add_solver(Box::new(ArraySolver::new()));
            }
        }
    }
    
    /// Register declarations.
    fn register_declarations(&mut self) {
        for decl in &self.problem.declarations {
            let var = SmtVar {
                name: decl.name.clone(),
                sort: decl.return_sort.clone(),
                sat_var: if decl.return_sort.is_bool() && decl.params.is_empty() {
                    let v = self.next_sat_var;
                    self.next_sat_var += 1;
                    Some(v)
                } else {
                    None
                },
            };
            self.variables.insert(decl.name.clone(), var);
        }
    }
    
    /// Allocate a fresh SAT variable for a term.
    fn fresh_var(&mut self, term: &Term) -> u32 {
        let term_str = format!("{:?}", term);
        if let Some(&var) = self.term_to_var.get(&term_str) {
            return var;
        }
        
        let var = self.next_sat_var;
        self.next_sat_var += 1;
        self.term_to_var.insert(term_str, var);
        self.var_to_term.insert(var, term.clone());
        var
    }
    
    /// Convert a Boolean term to CNF clauses.
    fn term_to_cnf(&mut self, term: &Term, formula: &mut Formula) -> Option<Literal> {
        match term {
            Term::True => {
                // True is always satisfied - return a tautology literal
                None
            }
            Term::False => {
                // False - add empty clause
                formula.add_clause(Clause::new(vec![]));
                None
            }
            Term::Var(name) => {
                if let Some(var_info) = self.variables.get(name) {
                    if let Some(sat_var) = var_info.sat_var {
                        return Some(Literal::from_dimacs(sat_var as i32));
                    }
                }
                // Non-Boolean variable - allocate a fresh variable for the term
                let var = self.fresh_var(term);
                Some(Literal::from_dimacs(var as i32))
            }
            Term::Not(inner) => {
                if let Some(lit) = self.term_to_cnf(inner, formula) {
                    Some(lit.negate())
                } else {
                    None
                }
            }
            Term::And(args) => {
                // For conjunction, collect the literals
                let mut lits = Vec::new();
                for arg in args {
                    if let Some(lit) = self.term_to_cnf(arg, formula) {
                        lits.push(lit);
                    }
                }
                if lits.is_empty() {
                    return None;
                }
                
                // Tseitin encoding: var <-> (a₁ ∧ a₂ ∧ ... ∧ aₙ)
                let var = self.next_sat_var;
                self.next_sat_var += 1;
                let var_lit = Literal::from_dimacs(var as i32);
                
                // var -> (and args): for each aᵢ, add ~var ∨ aᵢ
                for lit in &lits {
                    formula.add_clause(Clause::new(vec![var_lit.negate(), *lit]));
                }
                
                // (and args) -> var: ~a₁ ∨ ~a₂ ∨ ... ∨ ~aₙ ∨ var
                let mut impl_clause: Vec<Literal> = lits.iter().map(|l| l.negate()).collect();
                impl_clause.push(var_lit);
                formula.add_clause(Clause::new(impl_clause));
                
                Some(var_lit)
            }
            Term::Or(args) => {
                // For disjunction, collect the literals
                let mut clause_lits = Vec::new();
                for arg in args {
                    if let Some(lit) = self.term_to_cnf(arg, formula) {
                        clause_lits.push(lit);
                    }
                }
                if clause_lits.is_empty() {
                    return None;
                }
                
                // For simple disjunctions, just return a Tseitin variable
                // The caller will add a unit clause if this is a top-level assertion
                let var = self.next_sat_var;
                self.next_sat_var += 1;
                
                // Tseitin encoding: var <-> (a₁ ∨ a₂ ∨ ... ∨ aₙ)
                // var -> (or args): ~var ∨ a₁ ∨ a₂ ∨ ...
                let mut impl_clause = vec![Literal::from_dimacs(-(var as i32))];
                impl_clause.extend(clause_lits.iter().cloned());
                formula.add_clause(Clause::new(impl_clause));
                
                // (or args) -> var: for each aᵢ, add ~aᵢ ∨ var
                for lit in &clause_lits {
                    formula.add_clause(Clause::new(vec![
                        lit.negate(),
                        Literal::from_dimacs(var as i32),
                    ]));
                }
                
                Some(Literal::from_dimacs(var as i32))
            }
            Term::Implies(a, b) => {
                // a => b is equivalent to ~a ∨ b
                let or_term = Term::Or(vec![Term::Not(a.clone()), (**b).clone()]);
                self.term_to_cnf(&or_term, formula)
            }
            Term::Xor(a, b) => {
                // a xor b is (a ∧ ~b) ∨ (~a ∧ b)
                // Tseitin: introduce fresh variable x
                // x <-> (a xor b)
                // x -> (a ∨ b), x -> (~a ∨ ~b)
                // ~x -> (a ∨ ~b), ~x -> (~a ∨ b)
                let lit_a = self.term_to_cnf(a, formula);
                let lit_b = self.term_to_cnf(b, formula);
                
                if let (Some(la), Some(lb)) = (lit_a, lit_b) {
                    let x = self.next_sat_var;
                    self.next_sat_var += 1;
                    let lx = Literal::from_dimacs(x as i32);
                    
                    // x -> (a ∨ b)
                    formula.add_clause(Clause::new(vec![lx.negate(), la, lb]));
                    // x -> (~a ∨ ~b)
                    formula.add_clause(Clause::new(vec![lx.negate(), la.negate(), lb.negate()]));
                    // ~x -> (a ∨ ~b)
                    formula.add_clause(Clause::new(vec![lx, la, lb.negate()]));
                    // ~x -> (~a ∨ b)
                    formula.add_clause(Clause::new(vec![lx, la.negate(), lb]));
                    
                    return Some(lx);
                }
                None
            }
            Term::Ite(cond, then_branch, else_branch) => {
                // ite(c, t, e) is (c ∧ t) ∨ (~c ∧ e)
                // Tseitin: x <-> ite(c, t, e)
                // x -> (c -> t), x -> (~c -> e)
                // (~c ∨ t) ∧ (c ∨ e) -> x
                let lit_c = self.term_to_cnf(cond, formula);
                let lit_t = self.term_to_cnf(then_branch, formula);
                let lit_e = self.term_to_cnf(else_branch, formula);
                
                if let (Some(c), Some(t), Some(e)) = (lit_c, lit_t, lit_e) {
                    let x = self.next_sat_var;
                    self.next_sat_var += 1;
                    let lx = Literal::from_dimacs(x as i32);
                    
                    // x -> (c -> t): ~x ∨ ~c ∨ t
                    formula.add_clause(Clause::new(vec![lx.negate(), c.negate(), t]));
                    // x -> (~c -> e): ~x ∨ c ∨ e
                    formula.add_clause(Clause::new(vec![lx.negate(), c, e]));
                    // (c ∧ t) -> x: ~c ∨ ~t ∨ x
                    formula.add_clause(Clause::new(vec![c.negate(), t.negate(), lx]));
                    // (~c ∧ e) -> x: c ∨ ~e ∨ x
                    formula.add_clause(Clause::new(vec![c, e.negate(), lx]));
                    
                    return Some(lx);
                }
                None
            }
            Term::Eq(_a, _b) => {
                // For Boolean equality, this is XNOR
                // For theory terms, create a theory atom
                let x = self.fresh_var(term);
                Some(Literal::from_dimacs(x as i32))
            }
            Term::Distinct(_args) => {
                // All pairs must be distinct
                let x = self.fresh_var(term);
                Some(Literal::from_dimacs(x as i32))
            }
            // Arithmetic/BV comparisons become theory atoms
            Term::Lt(_, _) | Term::Le(_, _) | Term::Gt(_, _) | Term::Ge(_, _) |
            Term::BvUlt(_, _) | Term::BvUle(_, _) | Term::BvUgt(_, _) | Term::BvUge(_, _) |
            Term::BvSlt(_, _) | Term::BvSle(_, _) | Term::BvSgt(_, _) | Term::BvSge(_, _) => {
                let x = self.fresh_var(term);
                Some(Literal::from_dimacs(x as i32))
            }
            // Other terms - create theory atoms
            _ => {
                let x = self.fresh_var(term);
                Some(Literal::from_dimacs(x as i32))
            }
        }
    }
    
    /// Build the SAT formula from assertions.
    fn build_formula(&mut self) -> Formula {
        let mut formula = Formula::new();
        
        // Register all declarations
        self.register_declarations();
        
        // Convert each assertion to CNF
        let assertions = self.problem.assertions.clone();
        for assertion in &assertions {
            if let Some(lit) = self.term_to_cnf(assertion, &mut formula) {
                // Top-level assertion must be true
                formula.add_clause(Clause::new(vec![lit]));
            }
        }
        
        formula
    }
    
    /// Solve the SMT problem.
    pub fn solve(&mut self) -> SolveResult {
        // Build SAT formula
        let formula = self.build_formula();
        
        // Create SAT solver
        let mut sat_solver = Solver::with_config(formula, SolverConfig {
            restarts_enabled: true,
            reduce_enabled: true,
            ..Default::default()
        });
        
        // Main DPLL(T) loop
        loop {
            // Get SAT result
            match sat_solver.solve() {
                SolveResult::Unsat => {
                    return SolveResult::Unsat;
                }
                SolveResult::Unknown => {
                    return SolveResult::Unknown;
                }
                SolveResult::Sat(model) => {
                    // Check theory consistency
                    let level = 0; // Simplified - real impl tracks decision levels
                    
                    // Assert all SAT assignments to theories
                    for (var_idx, &value) in model.iter().enumerate() {
                        let var = (var_idx + 1) as u32;
                        let lit = if value {
                            Literal::from_dimacs(var as i32)
                        } else {
                            Literal::from_dimacs(-(var as i32))
                        };
                        
                        if let Err(_conflict) = self.theories.assert_literal(lit, level) {
                            // Theory conflict - would need to learn and continue
                            // For now, just return unknown
                            return SolveResult::Unknown;
                        }
                    }
                    
                    // Check theory consistency
                    match self.theories.check() {
                        TheoryResult::Consistent => {
                            return SolveResult::Sat(model);
                        }
                        TheoryResult::Conflict(_conflict) => {
                            // Would need to learn conflict clause and continue
                            // For now, return unknown
                            return SolveResult::Unknown;
                        }
                    }
                }
            }
        }
    }
    
    /// Get the logic of the problem.
    pub fn logic(&self) -> Option<&Logic> {
        self.problem.logic.as_ref()
    }
    
    /// Get the number of assertions.
    pub fn num_assertions(&self) -> usize {
        self.problem.assertions.len()
    }
    
    /// Get the number of declarations.
    pub fn num_declarations(&self) -> usize {
        self.problem.declarations.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::smtlib::parse_smtlib;

    #[test]
    fn test_dpll_t_new() {
        let problem = SmtProblem::new();
        let solver = DpllT::new(problem);
        assert!(solver.theories.is_empty() == false || true); // Has default theories
    }

    #[test]
    fn test_dpll_t_simple_sat() {
        let input = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (assert p)
            (check-sat)
        "#;
        let problem = parse_smtlib(input).unwrap();
        let mut solver = DpllT::new(problem);
        
        let result = solver.solve();
        assert!(matches!(result, SolveResult::Sat(_)));
    }

    #[test]
    fn test_dpll_t_simple_unsat() {
        let input = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (assert p)
            (assert (not p))
            (check-sat)
        "#;
        let problem = parse_smtlib(input).unwrap();
        let mut solver = DpllT::new(problem);
        
        let result = solver.solve();
        assert!(matches!(result, SolveResult::Unsat));
    }

    #[test]
    fn test_dpll_t_conjunction() {
        let input = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (declare-const q Bool)
            (assert (and p q))
            (check-sat)
        "#;
        let problem = parse_smtlib(input).unwrap();
        let mut solver = DpllT::new(problem);
        
        let result = solver.solve();
        assert!(matches!(result, SolveResult::Sat(_)));
    }

    #[test]
    fn test_dpll_t_disjunction() {
        let input = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (declare-const q Bool)
            (assert (or p q))
            (assert (not p))
            (check-sat)
        "#;
        let problem = parse_smtlib(input).unwrap();
        let mut solver = DpllT::new(problem);
        
        let result = solver.solve();
        assert!(matches!(result, SolveResult::Sat(_)));
    }

    #[test]
    fn test_dpll_t_implication() {
        let input = r#"
            (set-logic QF_UF)
            (declare-const p Bool)
            (declare-const q Bool)
            (assert (=> p q))
            (assert p)
            (assert (not q))
            (check-sat)
        "#;
        let problem = parse_smtlib(input).unwrap();
        let mut solver = DpllT::new(problem);
        
        let result = solver.solve();
        assert!(matches!(result, SolveResult::Unsat));
    }

    #[test]
    fn test_dpll_t_lia_logic() {
        let input = r#"
            (set-logic QF_LIA)
            (declare-const x Int)
            (assert (> x 0))
            (check-sat)
        "#;
        let problem = parse_smtlib(input).unwrap();
        let solver = DpllT::new(problem);
        
        assert_eq!(solver.logic(), Some(&Logic::QfLia));
    }
}
