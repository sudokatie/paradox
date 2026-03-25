//! SAT solver implementation

mod conflict;
mod learn;
mod propagate;
mod reduce;
mod restart;
mod vsids;

pub use conflict::{analyze_conflict, ConflictResult};
pub use learn::{add_learned_clause, bump_conflict_vars, LearningStats};
pub use propagate::propagate;
pub use reduce::{ClauseReducer, ReductionConfig, compact_clauses};
pub use restart::{RestartScheduler, RestartStrategy, luby_value};
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

    /// Main CDCL solve loop
    pub fn solve(&mut self) -> SolveResult {
        // Check for trivial UNSAT (empty clause in original formula)
        if self.formula.has_empty_clause() {
            return SolveResult::Unsat;
        }

        // Check for trivial SAT (empty formula)
        if self.formula.num_clauses() == 0 {
            return SolveResult::Sat(vec![]);
        }

        // Process unit clauses at level 0
        for (clause_ref, clause) in self.formula.unit_clauses().collect::<Vec<_>>() {
            let lit = clause[0];
            let var = lit.variable();
            
            // Check if already assigned
            match self.assignments.value(var) {
                Value::Unassigned => {
                    let val = lit.is_positive();
                    self.assignments.assign(var, val, 0, Some(clause_ref));
                    self.trail.push(lit);
                }
                Value::True if lit.is_positive() => {}  // Already satisfied
                Value::False if !lit.is_positive() => {} // Already satisfied
                _ => return SolveResult::Unsat, // Conflict at level 0
            }
        }

        // Initialize restart scheduler
        let mut restart_scheduler = RestartScheduler::new(RestartStrategy::default());
        
        // Track first learned clause index for reduction
        let first_learned = self.formula.num_clauses();
        let mut reducer = ClauseReducer::new(ReductionConfig::default());

        loop {
            // Propagate
            if let Some(conflict_clause) = self.propagate() {
                // Conflict!
                self.stats.conflicts += 1;
                
                let current_level = self.trail.current_level();
                
                // Conflict at level 0 means UNSAT
                if current_level == 0 {
                    return SolveResult::Unsat;
                }
                
                // Analyze conflict
                let analysis = analyze_conflict(
                    &self.formula,
                    &self.assignments,
                    &self.trail,
                    conflict_clause,
                    current_level,
                );
                
                match analysis {
                    None => return SolveResult::Unsat,
                    Some(result) => {
                        // Bump VSIDS activities
                        bump_conflict_vars(&mut self.vsids, &result.involved_vars);
                        
                        // Backtrack
                        self.backtrack(result.backtrack_level);
                        
                        // Add learned clause
                        let lbd = result.lbd;
                        let clause_ref = add_learned_clause(
                            &mut self.formula,
                            &mut self.watches,
                            result.learned_clause,
                        );
                        self.stats.learned_clauses += 1;
                        
                        // The asserting literal should now be unit
                        // Push it to trail for propagation
                        let asserting = self.formula.clause(clause_ref)[0];
                        let var = asserting.variable();
                        let val = asserting.is_positive();
                        self.assignments.assign(var, val, self.trail.current_level(), Some(clause_ref));
                        self.trail.push(asserting);
                        
                        // Record conflict for restart scheduler
                        restart_scheduler.record_conflict(Some(lbd));
                        
                        // Check for restart
                        if restart_scheduler.should_restart() {
                            self.backtrack(0);
                            restart_scheduler.restart();
                            self.stats.restarts += 1;
                        }
                        
                        // Check for clause reduction
                        let learned_count = self.formula.num_clauses() - first_learned;
                        if reducer.should_reduce(learned_count) {
                            let keep = reducer.select_clauses_to_keep(
                                self.formula.clauses(),
                                first_learned,
                            );
                            compact_clauses(&mut self.formula, &mut self.watches, &keep);
                        }
                    }
                }
            } else {
                // No conflict
                if self.all_assigned() {
                    // SAT!
                    return SolveResult::Sat(self.model());
                }
                
                // Make a decision
                if !self.decide() {
                    // No more decisions possible but not all assigned?
                    // This shouldn't happen, but treat as SAT
                    return SolveResult::Sat(self.model());
                }
            }
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

    #[test]
    fn test_solve_empty_formula() {
        let formula = Formula::new();
        let mut solver = Solver::new(formula);
        
        let result = solver.solve();
        assert_eq!(result, SolveResult::Sat(vec![]));
    }

    #[test]
    fn test_solve_trivial_sat() {
        // (1 v 2)
        let mut formula = Formula::with_num_vars(2);
        formula.add_clause(make_clause(&[(1, true), (2, true)]));
        
        let mut solver = Solver::new(formula);
        let result = solver.solve();
        
        match result {
            SolveResult::Sat(model) => {
                // At least one of x1 or x2 should be true
                assert!(model.len() >= 2);
            }
            _ => panic!("Expected SAT"),
        }
    }

    #[test]
    fn test_solve_trivial_unsat() {
        // (1) and (-1)
        let mut formula = Formula::with_num_vars(1);
        formula.add_clause(make_clause(&[(1, true)]));
        formula.add_clause(make_clause(&[(1, false)]));
        
        let mut solver = Solver::new(formula);
        let result = solver.solve();
        
        assert_eq!(result, SolveResult::Unsat);
    }

    #[test]
    fn test_solve_simple_sat() {
        // (1 v 2) and (-1 v 2) and (1 v -2)
        // SAT: x1 = true, x2 = true
        let mut formula = Formula::with_num_vars(2);
        formula.add_clause(make_clause(&[(1, true), (2, true)]));
        formula.add_clause(make_clause(&[(1, false), (2, true)]));
        formula.add_clause(make_clause(&[(1, true), (2, false)]));
        
        let mut solver = Solver::new(formula);
        let result = solver.solve();
        
        match result {
            SolveResult::Sat(model) => {
                // Verify model satisfies all clauses
                // (x1 v x2) -> x1 or x2
                // (-x1 v x2) -> !x1 or x2
                // (x1 v -x2) -> x1 or !x2
                let x1 = model[0];
                let x2 = model[1];
                assert!(x1 || x2);
                assert!(!x1 || x2);
                assert!(x1 || !x2);
            }
            _ => panic!("Expected SAT"),
        }
    }

    #[test]
    fn test_solve_pigeonhole_2_1() {
        // 2 pigeons, 1 hole -> UNSAT
        // At least one of: p1_h1, p2_h1 (each pigeon in hole 1)
        // But they can't both be in hole 1
        let mut formula = Formula::with_num_vars(2);
        // Pigeon 1 must be somewhere
        formula.add_clause(make_clause(&[(1, true)])); // p1 in h1
        // Pigeon 2 must be somewhere
        formula.add_clause(make_clause(&[(2, true)])); // p2 in h1
        // At most one pigeon per hole
        formula.add_clause(make_clause(&[(1, false), (2, false)])); // not both
        
        let mut solver = Solver::new(formula);
        let result = solver.solve();
        
        assert_eq!(result, SolveResult::Unsat);
    }

    #[test]
    fn test_solve_3sat_instance() {
        // A small 3-SAT instance
        // (1 v 2 v 3) and (-1 v -2 v 3) and (1 v -2 v -3) and (-1 v 2 v -3)
        let mut formula = Formula::with_num_vars(3);
        formula.add_clause(make_clause(&[(1, true), (2, true), (3, true)]));
        formula.add_clause(make_clause(&[(1, false), (2, false), (3, true)]));
        formula.add_clause(make_clause(&[(1, true), (2, false), (3, false)]));
        formula.add_clause(make_clause(&[(1, false), (2, true), (3, false)]));
        
        let mut solver = Solver::new(formula);
        let result = solver.solve();
        
        match result {
            SolveResult::Sat(model) => {
                assert_eq!(model.len(), 3);
                // Verify model
                let x1 = model[0];
                let x2 = model[1];
                let x3 = model[2];
                assert!(x1 || x2 || x3);
                assert!(!x1 || !x2 || x3);
                assert!(x1 || !x2 || !x3);
                assert!(!x1 || x2 || !x3);
            }
            _ => panic!("Expected SAT"),
        }
    }

    #[test]
    fn test_solve_stats() {
        let mut formula = Formula::with_num_vars(3);
        formula.add_clause(make_clause(&[(1, true), (2, true)]));
        formula.add_clause(make_clause(&[(2, false), (3, true)]));
        
        let mut solver = Solver::new(formula);
        solver.solve();
        
        // Should have made some decisions
        let stats = solver.stats();
        assert!(stats.decisions > 0 || stats.propagations > 0);
    }
}
