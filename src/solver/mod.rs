//! Core SAT solver.
//!
//! The solver implements CDCL with:
//! - Two-watched-literal propagation
//! - VSIDS variable selection
//! - 1-UIP conflict analysis
//! - Clause learning
//! - Restarts
//! - Clause deletion

pub mod propagate;
pub mod decide;
pub mod conflict;
pub mod learn;
pub mod restart;
pub mod reduce;
pub mod maxsat;

use std::time::{Duration, Instant};

use crate::{
    assignment::{Assignments, Value},
    formula::Formula,
    trail::Trail,
    watch::{init_watches, WatchLists},
};

use self::conflict::analyze_conflict;
use self::decide::Vsids;
use self::learn::{add_learned_clause, bump_involved_vars, LearnStats};
use self::propagate::{propagate, propagate_units, PropagateResult};
use self::reduce::{ClauseReducer, ReduceConfig};
use self::restart::{RestartScheduler, RestartStrategy};

/// Result of SAT solving.
#[derive(Debug, Clone)]
pub enum SolveResult {
    /// Satisfiable with a model (variable assignments).
    Sat(Vec<bool>),
    /// Unsatisfiable.
    Unsat,
    /// Unknown (timeout or resource limit).
    Unknown,
}

/// Statistics from solving.
#[derive(Debug, Default, Clone)]
pub struct SolverStats {
    pub decisions: u64,
    pub propagations: u64,
    pub conflicts: u64,
    pub learned_clauses: u64,
    pub restarts: u64,
    pub reductions: u64,
}

/// Configuration for the solver.
#[derive(Debug, Clone)]
pub struct SolverConfig {
    /// Enable restarts.
    pub restarts_enabled: bool,
    /// Enable clause deletion.
    pub reduce_enabled: bool,
    /// Restart strategy.
    pub restart_strategy: RestartStrategy,
    /// Clause reduction config.
    pub reduce_config: ReduceConfig,
}

impl Default for SolverConfig {
    fn default() -> Self {
        SolverConfig {
            restarts_enabled: true,
            reduce_enabled: true,
            restart_strategy: RestartStrategy::Luby { unit: 100 },
            reduce_config: ReduceConfig::default(),
        }
    }
}

/// CDCL SAT solver.
pub struct Solver {
    /// The formula being solved.
    pub formula: Formula,
    /// Variable assignments.
    pub assignments: Assignments,
    /// Decision trail.
    pub trail: Trail,
    /// Watch lists.
    pub watches: WatchLists,
    /// VSIDS decision heuristic.
    pub vsids: Vsids,
    /// Phase saving (last polarity for each variable).
    pub phases: Vec<bool>,
    /// Restart scheduler.
    pub restart_scheduler: RestartScheduler,
    /// Clause reducer.
    pub clause_reducer: ClauseReducer,
    /// Learning statistics.
    pub learn_stats: LearnStats,
    /// Solver statistics.
    pub stats: SolverStats,
    /// Solver configuration.
    pub config: SolverConfig,
}

impl Solver {
    /// Create a new solver for the given formula.
    pub fn new(mut formula: Formula) -> Self {
        let num_vars = formula.num_vars() as usize;
        let watches = init_watches(&formula);
        
        // Mark original clauses
        formula.mark_original_end();
        
        Solver {
            formula,
            assignments: Assignments::new(num_vars as u32),
            trail: Trail::new(),
            watches,
            vsids: Vsids::new(num_vars),
            phases: vec![true; num_vars],
            restart_scheduler: RestartScheduler::new(RestartStrategy::default()),
            clause_reducer: ClauseReducer::new(ReduceConfig::default()),
            learn_stats: LearnStats::default(),
            stats: SolverStats::default(),
            config: SolverConfig::default(),
        }
    }

    /// Create a solver with custom configuration.
    pub fn with_config(formula: Formula, config: SolverConfig) -> Self {
        let mut solver = Self::new(formula);
        solver.restart_scheduler = RestartScheduler::new(config.restart_strategy.clone());
        solver.clause_reducer = ClauseReducer::new(config.reduce_config.clone());
        solver.config = config;
        solver
    }

    /// Solve the formula.
    pub fn solve(&mut self) -> SolveResult {
        // Check for trivial cases
        if self.formula.is_empty() {
            return SolveResult::Sat(vec![]);
        }
        if self.formula.has_empty_clause() {
            return SolveResult::Unsat;
        }
        
        // Propagate initial unit clauses
        match propagate_units(
            &mut self.formula,
            &mut self.assignments,
            &mut self.trail,
            &mut self.watches,
        ) {
            PropagateResult::Ok => {}
            PropagateResult::Conflict(_) => return SolveResult::Unsat,
        }
        
        // Track propagation position across iterations
        let mut prop_start = self.trail.len();
        
        // Main CDCL loop
        loop {
            // Propagate from where we left off
            let level = self.trail.current_level();
            
            match propagate(
                &mut self.formula,
                &mut self.assignments,
                &mut self.trail,
                &mut self.watches,
                level,
                prop_start,
            ) {
                PropagateResult::Ok => {
                    // Update prop_start to current trail length for next iteration
                    prop_start = self.trail.len();
                    
                    // Check if all variables are assigned
                    if self.all_assigned() {
                        return SolveResult::Sat(self.extract_model());
                    }
                    
                    // Check for restart
                    if self.config.restarts_enabled && self.restart_scheduler.should_restart() {
                        self.restart();
                        prop_start = self.trail.len(); // Reset after restart
                        continue;
                    }
                    
                    // Check for clause reduction
                    let num_learned = self.formula.num_clauses() - self.formula.num_original_clauses();
                    if self.config.reduce_enabled && self.clause_reducer.should_reduce(num_learned) {
                        let deleted = self.clause_reducer.reduce(&mut self.formula, &mut self.watches);
                        self.stats.reductions += 1;
                        let _ = deleted;
                    }
                    
                    // Make a decision - this adds to the trail
                    // prop_start stays where it is, so next iteration will propagate the decision
                    self.decide();
                }
                PropagateResult::Conflict(conflict_clause) => {
                    self.stats.conflicts += 1;
                    
                    // Conflict at level 0 means UNSAT
                    if level == 0 {
                        return SolveResult::Unsat;
                    }
                    
                    // Analyze conflict
                    let result = analyze_conflict(
                        conflict_clause,
                        &self.formula,
                        &self.assignments,
                        &self.trail,
                        level,
                    );
                    
                    // Record conflict for restart scheduler
                    self.restart_scheduler.record_conflict(result.lbd);
                    
                    // Bump VSIDS for involved variables
                    bump_involved_vars(&result.involved_vars, &mut self.vsids);
                    
                    // Learn the clause
                    if !result.learned_clause.is_empty() {
                        let asserting_lit = result.learned_clause[0];
                        
                        // Add learned clause
                        let clause_idx = add_learned_clause(
                            result.learned_clause.clone(),
                            result.lbd,
                            &mut self.formula,
                            &mut self.watches,
                        );
                        
                        self.learn_stats.record(result.learned_clause.len(), result.lbd);
                        self.stats.learned_clauses += 1;
                        
                        // Backtrack
                        self.backtrack(result.backtrack_level);
                        
                        // Propagate the asserting literal
                        let var = asserting_lit.variable();
                        let value = if asserting_lit.is_positive() {
                            Value::True
                        } else {
                            Value::False
                        };
                        self.assignments.assign(var, value, result.backtrack_level, Some(clause_idx));
                        self.trail.push_propagation(asserting_lit);
                        
                        // Update prop_start to propagate the asserting literal
                        prop_start = self.trail.len() - 1;
                        
                        // Save phase
                        let var_idx = var.to_index();
                        if var_idx < self.phases.len() {
                            self.phases[var_idx] = asserting_lit.is_positive();
                        }
                    } else {
                        // Empty learned clause means UNSAT
                        return SolveResult::Unsat;
                    }
                }
            }
        }
    }

    /// Solve with a timeout.
    pub fn solve_with_timeout(&mut self, timeout: Duration) -> SolveResult {
        let start = Instant::now();
        
        // Check for trivial cases
        if self.formula.is_empty() {
            return SolveResult::Sat(vec![]);
        }
        if self.formula.has_empty_clause() {
            return SolveResult::Unsat;
        }
        
        // Propagate initial unit clauses
        match propagate_units(
            &mut self.formula,
            &mut self.assignments,
            &mut self.trail,
            &mut self.watches,
        ) {
            PropagateResult::Ok => {}
            PropagateResult::Conflict(_) => return SolveResult::Unsat,
        }
        
        // Track propagation position across iterations
        let mut prop_start = self.trail.len();
        
        // Main CDCL loop with timeout check
        let mut iterations = 0u64;
        loop {
            // Check timeout periodically
            iterations += 1;
            if iterations % 10000 == 0 && start.elapsed() >= timeout {
                return SolveResult::Unknown;
            }
            
            let level = self.trail.current_level();
            
            match propagate(
                &mut self.formula,
                &mut self.assignments,
                &mut self.trail,
                &mut self.watches,
                level,
                prop_start,
            ) {
                PropagateResult::Ok => {
                    // Update prop_start to current trail length
                    prop_start = self.trail.len();
                    
                    if self.all_assigned() {
                        return SolveResult::Sat(self.extract_model());
                    }
                    
                    if self.config.restarts_enabled && self.restart_scheduler.should_restart() {
                        self.restart();
                        prop_start = self.trail.len(); // Reset after restart
                        continue;
                    }
                    
                    let num_learned = self.formula.num_clauses() - self.formula.num_original_clauses();
                    if self.config.reduce_enabled && self.clause_reducer.should_reduce(num_learned) {
                        self.clause_reducer.reduce(&mut self.formula, &mut self.watches);
                        self.stats.reductions += 1;
                    }
                    
                    // Make decision - prop_start stays, so next iteration propagates it
                    self.decide();
                }
                PropagateResult::Conflict(conflict_clause) => {
                    self.stats.conflicts += 1;
                    
                    if level == 0 {
                        return SolveResult::Unsat;
                    }
                    
                    let result = analyze_conflict(
                        conflict_clause,
                        &self.formula,
                        &self.assignments,
                        &self.trail,
                        level,
                    );
                    
                    self.restart_scheduler.record_conflict(result.lbd);
                    bump_involved_vars(&result.involved_vars, &mut self.vsids);
                    
                    if !result.learned_clause.is_empty() {
                        let asserting_lit = result.learned_clause[0];
                        
                        let clause_idx = add_learned_clause(
                            result.learned_clause.clone(),
                            result.lbd,
                            &mut self.formula,
                            &mut self.watches,
                        );
                        
                        self.learn_stats.record(result.learned_clause.len(), result.lbd);
                        self.stats.learned_clauses += 1;
                        
                        self.backtrack(result.backtrack_level);
                        
                        let var = asserting_lit.variable();
                        let value = if asserting_lit.is_positive() {
                            Value::True
                        } else {
                            Value::False
                        };
                        self.assignments.assign(var, value, result.backtrack_level, Some(clause_idx));
                        self.trail.push_propagation(asserting_lit);
                        
                        // Update prop_start to propagate the asserting literal
                        prop_start = self.trail.len() - 1;
                        
                        let var_idx = var.to_index();
                        if var_idx < self.phases.len() {
                            self.phases[var_idx] = asserting_lit.is_positive();
                        }
                    } else {
                        return SolveResult::Unsat;
                    }
                }
            }
        }
    }

    /// Make a decision.
    fn decide(&mut self) {
        let lit = self.vsids.pick_literal(
            |v| self.assignments.is_assigned(v),
            Some(&self.phases),
        );
        
        if let Some(lit) = lit {
            self.stats.decisions += 1;
            self.trail.new_level();
            
            let var = lit.variable();
            let level = self.trail.current_level();
            let value = if lit.is_positive() {
                Value::True
            } else {
                Value::False
            };
            
            self.assignments.assign(var, value, level, None);
            self.trail.push_propagation(lit);
            
            // Save phase
            let var_idx = var.to_index();
            if var_idx < self.phases.len() {
                self.phases[var_idx] = lit.is_positive();
            }
        }
    }

    /// Backtrack to the given level.
    fn backtrack(&mut self, level: u32) {
        let unassigned = self.trail.backtrack_to(level);
        for lit in unassigned {
            self.assignments.unassign(lit.variable());
        }
    }

    /// Restart (backtrack to level 0).
    fn restart(&mut self) {
        self.backtrack(0);
        self.restart_scheduler.on_restart();
        self.stats.restarts += 1;
    }

    /// Check if all variables are assigned.
    fn all_assigned(&self) -> bool {
        self.assignments.all_assigned()
    }

    /// Extract the model (satisfying assignment).
    fn extract_model(&self) -> Vec<bool> {
        self.assignments.model()
    }

    /// Get solver statistics.
    pub fn stats(&self) -> &SolverStats {
        &self.stats
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clause::Clause;
    use crate::literal::Literal;

    fn lit(v: i32) -> Literal {
        Literal::from_dimacs(v)
    }

    fn clause(lits: &[i32]) -> Clause {
        Clause::new(lits.iter().map(|&v| lit(v)).collect())
    }

    #[test]
    fn test_empty_formula_is_sat() {
        let f = Formula::new();
        let mut solver = Solver::new(f);
        assert!(matches!(solver.solve(), SolveResult::Sat(_)));
    }

    #[test]
    fn test_empty_clause_is_unsat() {
        let mut f = Formula::new();
        f.add_clause(Clause::new(vec![]));
        let mut solver = Solver::new(f);
        assert!(matches!(solver.solve(), SolveResult::Unsat));
    }

    #[test]
    fn test_unit_clause_sat() {
        let mut f = Formula::new();
        f.add_clause(clause(&[1]));
        let mut solver = Solver::new(f);
        
        match solver.solve() {
            SolveResult::Sat(model) => {
                assert!(model.len() >= 1);
                assert!(model[0]); // var 1 should be true
            }
            _ => panic!("Expected SAT"),
        }
    }

    #[test]
    fn test_contradicting_units_unsat() {
        let mut f = Formula::new();
        f.add_clause(clause(&[1]));
        f.add_clause(clause(&[-1]));
        let mut solver = Solver::new(f);
        assert!(matches!(solver.solve(), SolveResult::Unsat));
    }

    #[test]
    fn test_simple_sat() {
        // (1 ∨ 2) ∧ (¬1 ∨ 3)
        let mut f = Formula::new();
        f.add_clause(clause(&[1, 2]));
        f.add_clause(clause(&[-1, 3]));
        let mut solver = Solver::new(f);
        
        match solver.solve() {
            SolveResult::Sat(model) => {
                // Check that the model satisfies both clauses
                let sat_clause1 = model.get(0).copied().unwrap_or(false) 
                    || model.get(1).copied().unwrap_or(false);
                let sat_clause2 = !model.get(0).copied().unwrap_or(true) 
                    || model.get(2).copied().unwrap_or(false);
                assert!(sat_clause1 && sat_clause2);
            }
            _ => panic!("Expected SAT"),
        }
    }

    #[test]
    fn test_pigeonhole_2_1_unsat() {
        // 2 pigeons, 1 hole - UNSAT
        // P(1,1) ∨ P(2,1): at least one pigeon in hole 1
        // ¬P(1,1) ∨ ¬P(2,1): at most one pigeon in hole 1
        // But we need both pigeons somewhere, so UNSAT
        let mut f = Formula::new();
        // Pigeon 1 must be in some hole
        f.add_clause(clause(&[1])); // P(1,1)
        // Pigeon 2 must be in some hole
        f.add_clause(clause(&[2])); // P(2,1)
        // At most one pigeon per hole
        f.add_clause(clause(&[-1, -2])); // ¬P(1,1) ∨ ¬P(2,1)
        
        let mut solver = Solver::new(f);
        assert!(matches!(solver.solve(), SolveResult::Unsat));
    }

    #[test]
    fn test_3sat_instance() {
        // A simple 3-SAT instance
        let mut f = Formula::new();
        f.add_clause(clause(&[1, 2, 3]));
        f.add_clause(clause(&[-1, 2, 3]));
        f.add_clause(clause(&[1, -2, 3]));
        f.add_clause(clause(&[1, 2, -3]));
        
        let mut solver = Solver::new(f);
        match solver.solve() {
            SolveResult::Sat(model) => {
                // Verify the model
                let clauses = [
                    [1, 2, 3],
                    [-1, 2, 3],
                    [1, -2, 3],
                    [1, 2, -3],
                ];
                for c in &clauses {
                    let sat = c.iter().any(|&l: &i32| {
                        let var = l.unsigned_abs() as usize - 1;
                        let positive = l > 0;
                        model.get(var).copied().unwrap_or(false) == positive
                    });
                    assert!(sat, "Clause {:?} not satisfied", c);
                }
            }
            _ => panic!("Expected SAT"),
        }
    }

    #[test]
    fn test_solver_stats() {
        let f = Formula::new();
        let solver = Solver::new(f);
        assert_eq!(solver.stats().decisions, 0);
        assert_eq!(solver.stats().conflicts, 0);
    }

    #[test]
    fn test_timeout() {
        // Simple formula that should solve quickly
        let mut f = Formula::new();
        f.add_clause(clause(&[1, 2]));
        
        let mut solver = Solver::new(f);
        let result = solver.solve_with_timeout(Duration::from_secs(1));
        
        // Should solve before timeout
        assert!(matches!(result, SolveResult::Sat(_)));
    }
}
