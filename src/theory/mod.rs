//! Theory solvers for DPLL(T)
//!
//! This module defines the interface for theory solvers and provides
//! implementations for various SMT theories:
//! - EUF (Equality with Uninterpreted Functions)
//! - LIA (Linear Integer Arithmetic)
//! - BV (Bitvectors)
//! - Arrays

pub mod euf;
pub mod lia;
pub mod bv;
pub mod array;

use crate::literal::Literal;
use std::fmt;

pub use euf::EufSolver;
pub use lia::LiaSolver;
pub use bv::BvSolver;
pub use array::ArraySolver;

/// Result of theory operations
pub type TheoryResult<T> = Result<T, TheoryConflict>;

/// A conflict reported by a theory solver
#[derive(Debug, Clone)]
pub struct TheoryConflict {
    /// Explanation clause - a disjunction of literals that is falsified
    /// In the form: NOT(l1) OR NOT(l2) OR ... OR NOT(ln)
    /// Represented as the negation of the conflicting assignment
    pub explanation: Vec<Literal>,
}

impl TheoryConflict {
    /// Create a new theory conflict from explaining literals
    pub fn new(explanation: Vec<Literal>) -> Self {
        TheoryConflict { explanation }
    }

    /// Get the conflict clause (for learning)
    /// The conflict clause is the negation of the explanation
    pub fn as_clause(&self) -> Vec<Literal> {
        self.explanation.iter().map(|l| l.negate()).collect()
    }
}

impl fmt::Display for TheoryConflict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "theory conflict: {:?}", self.explanation)
    }
}

/// Propagation result from a theory solver
#[derive(Debug, Clone)]
pub struct TheoryPropagation {
    /// The propagated literal
    pub literal: Literal,
    /// The explanation (why this literal must be true)
    /// When the explanation literals are true, the propagated literal must be true
    pub explanation: Vec<Literal>,
}

impl TheoryPropagation {
    /// Create a new theory propagation
    pub fn new(literal: Literal, explanation: Vec<Literal>) -> Self {
        TheoryPropagation { literal, explanation }
    }
}

/// Theory solver trait
///
/// A theory solver checks consistency of a partial assignment
/// with respect to a particular theory (e.g., arithmetic, arrays).
pub trait TheorySolver: Send {
    /// Get the name of this theory solver
    fn name(&self) -> &'static str;

    /// Assert a literal to the theory
    ///
    /// Returns Err(conflict) if the literal creates an immediate inconsistency.
    /// The solver should update its internal state.
    fn assert_literal(&mut self, lit: Literal) -> TheoryResult<()>;

    /// Check consistency of current state
    ///
    /// Called when SAT solver has found a complete assignment or
    /// periodically during search.
    /// Returns Err(conflict) if the current assignment is theory-inconsistent.
    fn check(&mut self) -> TheoryResult<()>;

    /// Get theory propagations
    ///
    /// Returns literals that must be true given the current assignment.
    /// Each propagation includes an explanation.
    fn propagate(&mut self) -> Vec<TheoryPropagation>;

    /// Explain a previously propagated literal
    ///
    /// Given a literal that was propagated by this theory,
    /// return the explanation (which literals implied it).
    fn explain(&self, lit: Literal) -> Vec<Literal>;

    /// Backtrack to a previous decision level
    ///
    /// Undo all assertions made after the given level.
    fn backtrack(&mut self, level: u32);

    /// Push a decision level marker
    fn push_level(&mut self);

    /// Get current decision level
    fn current_level(&self) -> u32;

    /// Reset to initial state
    fn reset(&mut self);
}

/// A theory atom - maps between SAT literals and theory expressions
#[derive(Debug, Clone)]
pub struct TheoryAtom {
    /// The SAT literal
    pub literal: Literal,
    /// The theory expression (as a string for now, will be typed later)
    pub expression: String,
}

/// Theory manager - coordinates multiple theory solvers
pub struct TheoryManager {
    /// Active theory solvers
    solvers: Vec<Box<dyn TheorySolver>>,
    /// Current decision level
    level: u32,
}

impl TheoryManager {
    /// Create a new theory manager
    pub fn new() -> Self {
        TheoryManager {
            solvers: Vec::new(),
            level: 0,
        }
    }

    /// Add a theory solver
    pub fn add_solver(&mut self, solver: Box<dyn TheorySolver>) {
        self.solvers.push(solver);
    }

    /// Assert a literal to all theories
    pub fn assert_literal(&mut self, lit: Literal) -> TheoryResult<()> {
        for solver in &mut self.solvers {
            solver.assert_literal(lit)?;
        }
        Ok(())
    }

    /// Check all theories for consistency
    pub fn check(&mut self) -> TheoryResult<()> {
        for solver in &mut self.solvers {
            solver.check()?;
        }
        Ok(())
    }

    /// Get propagations from all theories
    pub fn propagate(&mut self) -> Vec<TheoryPropagation> {
        let mut all_props = Vec::new();
        for solver in &mut self.solvers {
            all_props.extend(solver.propagate());
        }
        all_props
    }

    /// Backtrack all theories
    pub fn backtrack(&mut self, level: u32) {
        self.level = level;
        for solver in &mut self.solvers {
            solver.backtrack(level);
        }
    }

    /// Push a decision level
    pub fn push_level(&mut self) {
        self.level += 1;
        for solver in &mut self.solvers {
            solver.push_level();
        }
    }

    /// Get current decision level
    pub fn current_level(&self) -> u32 {
        self.level
    }

    /// Reset all theories
    pub fn reset(&mut self) {
        self.level = 0;
        for solver in &mut self.solvers {
            solver.reset();
        }
    }

    /// Check if any theories are registered
    pub fn has_theories(&self) -> bool {
        !self.solvers.is_empty()
    }

    /// Get number of registered theories
    pub fn theory_count(&self) -> usize {
        self.solvers.len()
    }
}

impl Default for TheoryManager {
    fn default() -> Self {
        Self::new()
    }
}

/// A mock theory solver for testing
#[cfg(test)]
pub struct MockTheorySolver {
    name: &'static str,
    level: u32,
    conflicts: Vec<(Vec<Literal>, Vec<Literal>)>, // (trigger, conflict)
    assertions: Vec<(u32, Literal)>,
}

#[cfg(test)]
impl MockTheorySolver {
    pub fn new(name: &'static str) -> Self {
        MockTheorySolver {
            name,
            level: 0,
            conflicts: Vec::new(),
            assertions: Vec::new(),
        }
    }

    /// Add a conflict trigger - when all trigger literals are asserted, conflict
    pub fn add_conflict(&mut self, trigger: Vec<Literal>, explanation: Vec<Literal>) {
        self.conflicts.push((trigger, explanation));
    }
}

#[cfg(test)]
impl TheorySolver for MockTheorySolver {
    fn name(&self) -> &'static str {
        self.name
    }

    fn assert_literal(&mut self, lit: Literal) -> TheoryResult<()> {
        self.assertions.push((self.level, lit));
        
        // Check if any conflict is triggered
        for (trigger, explanation) in &self.conflicts {
            let all_asserted = trigger.iter().all(|t| {
                self.assertions.iter().any(|(_, l)| l == t)
            });
            if all_asserted {
                return Err(TheoryConflict::new(explanation.clone()));
            }
        }
        
        Ok(())
    }

    fn check(&mut self) -> TheoryResult<()> {
        Ok(())
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        Vec::new()
    }

    fn explain(&self, _lit: Literal) -> Vec<Literal> {
        Vec::new()
    }

    fn backtrack(&mut self, level: u32) {
        self.level = level;
        self.assertions.retain(|(l, _)| *l <= level);
    }

    fn push_level(&mut self) {
        self.level += 1;
    }

    fn current_level(&self) -> u32 {
        self.level
    }

    fn reset(&mut self) {
        self.level = 0;
        self.assertions.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Variable;

    fn lit(var: u32, positive: bool) -> Literal {
        Literal::new(Variable::new(var), positive)
    }

    #[test]
    fn test_theory_conflict() {
        let conflict = TheoryConflict::new(vec![lit(1, true), lit(2, false)]);
        let clause = conflict.as_clause();
        
        assert_eq!(clause.len(), 2);
        assert_eq!(clause[0], lit(1, false));
        assert_eq!(clause[1], lit(2, true));
    }

    #[test]
    fn test_mock_theory_no_conflict() {
        let mut solver = MockTheorySolver::new("test");
        
        assert!(solver.assert_literal(lit(1, true)).is_ok());
        assert!(solver.assert_literal(lit(2, false)).is_ok());
        assert!(solver.check().is_ok());
    }

    #[test]
    fn test_mock_theory_conflict() {
        let mut solver = MockTheorySolver::new("test");
        
        // Conflict when both x and y are true
        solver.add_conflict(
            vec![lit(1, true), lit(2, true)],
            vec![lit(1, true), lit(2, true)]
        );
        
        assert!(solver.assert_literal(lit(1, true)).is_ok());
        let result = solver.assert_literal(lit(2, true));
        assert!(result.is_err());
    }

    #[test]
    fn test_mock_theory_backtrack() {
        let mut solver = MockTheorySolver::new("test");
        
        solver.assert_literal(lit(1, true)).unwrap();
        solver.push_level();
        solver.assert_literal(lit(2, true)).unwrap();
        
        assert_eq!(solver.assertions.len(), 2);
        
        solver.backtrack(0);
        assert_eq!(solver.assertions.len(), 1);
    }

    #[test]
    fn test_theory_manager() {
        let mut manager = TheoryManager::new();
        
        assert!(!manager.has_theories());
        
        manager.add_solver(Box::new(MockTheorySolver::new("theory1")));
        assert!(manager.has_theories());
        assert_eq!(manager.theory_count(), 1);
    }

    #[test]
    fn test_theory_manager_assert() {
        let mut manager = TheoryManager::new();
        manager.add_solver(Box::new(MockTheorySolver::new("theory1")));
        
        assert!(manager.assert_literal(lit(1, true)).is_ok());
        assert!(manager.check().is_ok());
    }

    #[test]
    fn test_theory_manager_conflict() {
        let mut manager = TheoryManager::new();
        
        let mut solver = MockTheorySolver::new("theory1");
        solver.add_conflict(
            vec![lit(1, true), lit(2, true)],
            vec![lit(1, true), lit(2, true)]
        );
        manager.add_solver(Box::new(solver));
        
        assert!(manager.assert_literal(lit(1, true)).is_ok());
        assert!(manager.assert_literal(lit(2, true)).is_err());
    }

    #[test]
    fn test_theory_manager_levels() {
        let mut manager = TheoryManager::new();
        manager.add_solver(Box::new(MockTheorySolver::new("theory1")));
        
        assert_eq!(manager.current_level(), 0);
        manager.push_level();
        assert_eq!(manager.current_level(), 1);
        manager.backtrack(0);
        assert_eq!(manager.current_level(), 0);
    }

    #[test]
    fn test_theory_propagation() {
        let prop = TheoryPropagation::new(
            lit(3, true),
            vec![lit(1, true), lit(2, true)]
        );
        
        assert_eq!(prop.literal, lit(3, true));
        assert_eq!(prop.explanation.len(), 2);
    }
}
