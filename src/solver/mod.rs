//! Core SAT solver.
//!
//! The solver implements CDCL with:
//! - Two-watched-literal propagation
//! - VSIDS variable selection
//! - 1-UIP conflict analysis
//! - Clause learning
//! - Restarts
//! - Clause deletion

// Module stubs for later implementation
// pub mod propagate;
// pub mod decide;
// pub mod conflict;
// pub mod learn;
// pub mod restart;
// pub mod reduce;

use std::time::Duration;

use crate::{
    assignment::Assignments,
    formula::Formula,
    trail::Trail,
    watch::{init_watches, WatchLists},
};

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
}

/// Configuration for the solver.
#[derive(Debug, Clone)]
pub struct SolverConfig {
    /// Enable restarts.
    pub restarts_enabled: bool,
    /// Enable clause deletion.
    pub reduce_enabled: bool,
    /// Initial restart interval.
    pub restart_interval: u64,
    /// Restart growth factor.
    pub restart_factor: f64,
}

impl Default for SolverConfig {
    fn default() -> Self {
        SolverConfig {
            restarts_enabled: true,
            reduce_enabled: true,
            restart_interval: 100,
            restart_factor: 1.5,
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
    /// Solver statistics.
    pub stats: SolverStats,
    /// Solver configuration.
    pub config: SolverConfig,
}

impl Solver {
    /// Create a new solver for the given formula.
    pub fn new(formula: Formula) -> Self {
        let num_vars = formula.num_vars();
        let watches = init_watches(&formula);
        
        Solver {
            formula,
            assignments: Assignments::new(num_vars),
            trail: Trail::new(),
            watches,
            stats: SolverStats::default(),
            config: SolverConfig::default(),
        }
    }

    /// Create a solver with custom configuration.
    pub fn with_config(formula: Formula, config: SolverConfig) -> Self {
        let mut solver = Self::new(formula);
        solver.config = config;
        solver
    }

    /// Solve the formula.
    pub fn solve(&mut self) -> SolveResult {
        // Stub: just check for trivial cases
        if self.formula.is_empty() {
            return SolveResult::Sat(vec![]);
        }
        if self.formula.has_empty_clause() {
            return SolveResult::Unsat;
        }
        
        // TODO: Implement full CDCL loop
        SolveResult::Unknown
    }

    /// Solve with a timeout.
    pub fn solve_with_timeout(&mut self, _timeout: Duration) -> SolveResult {
        // Stub: just delegate to solve
        self.solve()
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
    fn test_solver_stats() {
        let f = Formula::new();
        let solver = Solver::new(f);
        assert_eq!(solver.stats().decisions, 0);
        assert_eq!(solver.stats().conflicts, 0);
    }
}
