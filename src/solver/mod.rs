//! SAT solver implementation

mod conflict;
mod propagate;
mod vsids;

pub use conflict::{analyze_conflict, ConflictResult};
pub use propagate::propagate;
pub use vsids::Vsids;

use crate::assignment::{Assignments, Value};
use crate::clause::ClauseRef;
use crate::formula::Formula;
use crate::literal::{Literal, Variable};
use crate::trail::Trail;
use crate::watch::{init_watches, WatchLists};

/// Result of SAT solving
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolveResult {
    /// Satisfiable with a model (variable assignments)
    Sat(Vec<bool>),
    /// Unsatisfiable
    Unsat,
    /// Unknown (timeout or resource limit)
    Unknown,
}

/// Statistics about the solving process
#[derive(Debug, Clone, Default)]
pub struct Stats {
    /// Number of decisions made
    pub decisions: u64,
    /// Number of propagations
    pub propagations: u64,
    /// Number of conflicts
    pub conflicts: u64,
    /// Number of restarts
    pub restarts: u64,
    /// Number of learned clauses
    pub learned_clauses: u64,
}

/// CDCL SAT solver
pub struct Solver {
    /// The CNF formula
    formula: Formula,
    /// Variable assignments
    assignments: Assignments,
    /// Decision trail
    trail: Trail,
    /// Watch lists
    watches: WatchLists,
    /// VSIDS decision heuristic
    vsids: Vsids,
    /// Solving statistics
    stats: Stats,
}

impl Solver {
    /// Create a new solver for the given formula
    pub fn new(formula: Formula) -> Self {
        let num_vars = formula.num_vars();
        
        let mut watches = WatchLists::new(num_vars);
        init_watches(&mut watches, formula.clauses());
        
        Solver {
            formula,
            assignments: Assignments::new(num_vars),
            trail: Trail::new(),
            watches,
            vsids: Vsids::new(num_vars),
            stats: Stats::default(),
        }
    }

    /// Get the current formula
    pub fn formula(&self) -> &Formula {
        &self.formula
    }

    /// Get the current assignments
    pub fn assignments(&self) -> &Assignments {
        &self.assignments
    }

    /// Get mutable assignments
    pub fn assignments_mut(&mut self) -> &mut Assignments {
        &mut self.assignments
    }

    /// Get the trail
    pub fn trail(&self) -> &Trail {
        &self.trail
    }

    /// Get mutable trail
    pub fn trail_mut(&mut self) -> &mut Trail {
        &mut self.trail
    }

    /// Get the watch lists
    pub fn watches(&self) -> &WatchLists {
        &self.watches
    }

    /// Get mutable watch lists
    pub fn watches_mut(&mut self) -> &mut WatchLists {
        &mut self.watches
    }

    /// Get the VSIDS heuristic
    pub fn vsids(&self) -> &Vsids {
        &self.vsids
    }

    /// Get mutable VSIDS
    pub fn vsids_mut(&mut self) -> &mut Vsids {
        &mut self.vsids
    }

    /// Get statistics
    pub fn stats(&self) -> &Stats {
        &self.stats
    }

    /// Run unit propagation
    /// Returns Some(clause_ref) if conflict, None otherwise
    pub fn propagate(&mut self) -> Option<ClauseRef> {
        let result = propagate(
            &self.formula,
            &mut self.assignments,
            &mut self.trail,
            &mut self.watches,
            &mut self.stats.propagations,
        );
        result
    }

    /// Make a decision on an unassigned variable
    /// Returns false if all variables are assigned
    pub fn decide(&mut self) -> bool {
        // Find next unassigned variable using VSIDS
        if let Some(var) = self.vsids.pick_branching_variable(&self.assignments) {
            // Start new decision level
            self.trail.new_level();
            
            // Choose polarity (positive by default, could be smarter)
            let lit = Literal::positive(var);
            
            // Assign and record
            self.assignments.assign(var, true, self.trail.current_level(), None);
            self.trail.push(lit);
            
            self.stats.decisions += 1;
            true
        } else {
            false
        }
    }

    /// Check if all variables are assigned
    pub fn all_assigned(&self) -> bool {
        (1..=self.formula.num_vars())
            .all(|i| self.assignments.value(Variable::new(i)).is_assigned())
    }

    /// Extract model (assuming SAT)
    pub fn model(&self) -> Vec<bool> {
        self.assignments.model()
    }

    /// Backtrack to a given level
    pub fn backtrack(&mut self, level: u32) {
        let unassigned = self.trail.backtrack_to(level);
        for lit in unassigned {
            self.assignments.unassign(lit.variable());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clause::Clause;

    fn make_clause(lits: &[(u32, bool)]) -> Clause {
        let literals: Vec<Literal> = lits
            .iter()
            .map(|&(var, pol)| {
                let v = Variable::new(var);
                if pol { Literal::positive(v) } else { Literal::negative(v) }
            })
            .collect();
        Clause::new(literals)
    }

    #[test]
    fn test_solver_creation() {
        let mut formula = Formula::with_num_vars(3);
        formula.add_clause(make_clause(&[(1, true), (2, false)]));
        formula.add_clause(make_clause(&[(2, true), (3, true)]));
        
        let solver = Solver::new(formula);
        assert_eq!(solver.formula().num_vars(), 3);
        assert_eq!(solver.formula().num_clauses(), 2);
    }

    #[test]
    fn test_decide() {
        let mut formula = Formula::with_num_vars(3);
        formula.add_clause(make_clause(&[(1, true), (2, false)]));
        
        let mut solver = Solver::new(formula);
        
        // First decision
        assert!(solver.decide());
        assert_eq!(solver.trail().current_level(), 1);
        assert_eq!(solver.stats().decisions, 1);
        
        // Second decision
        assert!(solver.decide());
        assert_eq!(solver.trail().current_level(), 2);
        
        // Third decision
        assert!(solver.decide());
        assert_eq!(solver.trail().current_level(), 3);
        
        // No more unassigned variables
        assert!(!solver.decide());
    }

    #[test]
    fn test_backtrack() {
        let mut formula = Formula::with_num_vars(3);
        formula.add_clause(make_clause(&[(1, true), (2, false), (3, true)]));
        
        let mut solver = Solver::new(formula);
        
        solver.decide();
        solver.decide();
        solver.decide();
        
        assert_eq!(solver.trail().current_level(), 3);
        assert!(solver.all_assigned());
        
        solver.backtrack(1);
        assert_eq!(solver.trail().current_level(), 1);
        assert!(!solver.all_assigned());
    }

    #[test]
    fn test_all_assigned() {
        let formula = Formula::with_num_vars(2);
        let mut solver = Solver::new(formula);
        
        assert!(!solver.all_assigned());
        
        solver.assignments_mut().assign(Variable::new(1), true, 0, None);
        assert!(!solver.all_assigned());
        
        solver.assignments_mut().assign(Variable::new(2), false, 0, None);
        assert!(solver.all_assigned());
    }
}
