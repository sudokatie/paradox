//! Theory solvers for SMT solving via DPLL(T).
//!
//! Each theory solver handles a specific theory (EUF, LIA, BV, Arrays).
//! The DPLL(T) loop queries theory solvers after SAT propagation.

pub mod euf;
pub mod lia;
pub mod bv;
pub mod array;

use crate::literal::Literal;

/// A conflict from a theory solver.
#[derive(Debug, Clone)]
pub struct TheoryConflict {
    /// Literals that together cause the conflict.
    /// The negation of this forms a learned clause.
    pub literals: Vec<Literal>,
    /// Optional explanation string.
    pub explanation: Option<String>,
}

impl TheoryConflict {
    pub fn new(literals: Vec<Literal>) -> Self {
        TheoryConflict {
            literals,
            explanation: None,
        }
    }
    
    pub fn with_explanation(literals: Vec<Literal>, explanation: String) -> Self {
        TheoryConflict {
            literals,
            explanation: Some(explanation),
        }
    }
}

/// A propagation from a theory solver.
#[derive(Debug, Clone)]
pub struct TheoryPropagation {
    /// The literal being propagated.
    pub literal: Literal,
    /// Literals that imply this propagation (for explanation).
    pub reason: Vec<Literal>,
}

impl TheoryPropagation {
    pub fn new(literal: Literal, reason: Vec<Literal>) -> Self {
        TheoryPropagation { literal, reason }
    }
}

/// Result of theory checking.
#[derive(Debug, Clone)]
pub enum TheoryResult {
    /// Theory is consistent.
    Consistent,
    /// Theory found a conflict.
    Conflict(TheoryConflict),
}

/// Trait for theory solvers.
///
/// Each theory solver maintains its own state and responds to:
/// - Literal assertions from the SAT solver
/// - Consistency checks
/// - Propagation requests
/// - Backtracking
pub trait TheorySolver: Send {
    /// Get the name of this theory.
    fn name(&self) -> &'static str;
    
    /// Assert a literal in the theory.
    ///
    /// Called when the SAT solver assigns a theory-relevant literal.
    /// Returns a conflict if the assertion is immediately inconsistent.
    fn assert_literal(&mut self, lit: Literal, level: u32) -> Result<(), TheoryConflict>;
    
    /// Check consistency of current assertions.
    ///
    /// Called after propagation to ensure theory state is consistent.
    fn check(&mut self) -> TheoryResult;
    
    /// Get propagations from the theory.
    ///
    /// Returns literals that are implied by current assertions.
    fn propagate(&mut self) -> Vec<TheoryPropagation>;
    
    /// Explain why a literal was propagated.
    ///
    /// Returns the literals that imply the given literal.
    fn explain(&self, lit: Literal) -> Vec<Literal>;
    
    /// Backtrack to the given decision level.
    fn backtrack(&mut self, level: u32);
    
    /// Reset the solver to initial state.
    fn reset(&mut self);
}

/// Manager for multiple theory solvers.
pub struct TheoryManager {
    solvers: Vec<Box<dyn TheorySolver>>,
}

impl TheoryManager {
    /// Create a new empty theory manager.
    pub fn new() -> Self {
        TheoryManager {
            solvers: Vec::new(),
        }
    }
    
    /// Add a theory solver.
    pub fn add_solver(&mut self, solver: Box<dyn TheorySolver>) {
        self.solvers.push(solver);
    }
    
    /// Assert a literal to all theory solvers.
    pub fn assert_literal(&mut self, lit: Literal, level: u32) -> Result<(), TheoryConflict> {
        for solver in &mut self.solvers {
            solver.assert_literal(lit, level)?;
        }
        Ok(())
    }
    
    /// Check all theory solvers for consistency.
    pub fn check(&mut self) -> TheoryResult {
        for solver in &mut self.solvers {
            match solver.check() {
                TheoryResult::Consistent => {}
                conflict => return conflict,
            }
        }
        TheoryResult::Consistent
    }
    
    /// Get propagations from all theory solvers.
    pub fn propagate(&mut self) -> Vec<TheoryPropagation> {
        let mut props = Vec::new();
        for solver in &mut self.solvers {
            props.extend(solver.propagate());
        }
        props
    }
    
    /// Backtrack all theory solvers.
    pub fn backtrack(&mut self, level: u32) {
        for solver in &mut self.solvers {
            solver.backtrack(level);
        }
    }
    
    /// Reset all theory solvers.
    pub fn reset(&mut self) {
        for solver in &mut self.solvers {
            solver.reset();
        }
    }
    
    /// Check if any solvers are registered.
    pub fn is_empty(&self) -> bool {
        self.solvers.is_empty()
    }
}

impl Default for TheoryManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Literal;

    /// Mock theory solver for testing.
    struct MockTheorySolver {
        assertions: Vec<(Literal, u32)>,
        conflicts: Vec<TheoryConflict>,
        propagations: Vec<TheoryPropagation>,
    }

    impl MockTheorySolver {
        fn new() -> Self {
            MockTheorySolver {
                assertions: Vec::new(),
                conflicts: Vec::new(),
                propagations: Vec::new(),
            }
        }
        
        fn add_conflict(&mut self, conflict: TheoryConflict) {
            self.conflicts.push(conflict);
        }
        
        fn add_propagation(&mut self, prop: TheoryPropagation) {
            self.propagations.push(prop);
        }
    }

    impl TheorySolver for MockTheorySolver {
        fn name(&self) -> &'static str {
            "mock"
        }
        
        fn assert_literal(&mut self, lit: Literal, level: u32) -> Result<(), TheoryConflict> {
            self.assertions.push((lit, level));
            Ok(())
        }
        
        fn check(&mut self) -> TheoryResult {
            if let Some(conflict) = self.conflicts.pop() {
                TheoryResult::Conflict(conflict)
            } else {
                TheoryResult::Consistent
            }
        }
        
        fn propagate(&mut self) -> Vec<TheoryPropagation> {
            std::mem::take(&mut self.propagations)
        }
        
        fn explain(&self, _lit: Literal) -> Vec<Literal> {
            Vec::new()
        }
        
        fn backtrack(&mut self, level: u32) {
            self.assertions.retain(|(_, l)| *l <= level);
        }
        
        fn reset(&mut self) {
            self.assertions.clear();
            self.conflicts.clear();
            self.propagations.clear();
        }
    }

    #[test]
    fn test_theory_manager_empty() {
        let mut manager = TheoryManager::new();
        assert!(manager.is_empty());
        assert!(matches!(manager.check(), TheoryResult::Consistent));
    }

    #[test]
    fn test_theory_manager_assert() {
        let mut manager = TheoryManager::new();
        let solver = Box::new(MockTheorySolver::new());
        manager.add_solver(solver);
        
        let lit = Literal::from_dimacs(1);
        assert!(manager.assert_literal(lit, 1).is_ok());
    }

    #[test]
    fn test_theory_manager_conflict() {
        let mut manager = TheoryManager::new();
        let mut solver = MockTheorySolver::new();
        solver.add_conflict(TheoryConflict::new(vec![Literal::from_dimacs(1)]));
        manager.add_solver(Box::new(solver));
        
        assert!(matches!(manager.check(), TheoryResult::Conflict(_)));
    }

    #[test]
    fn test_theory_manager_propagate() {
        let mut manager = TheoryManager::new();
        let mut solver = MockTheorySolver::new();
        solver.add_propagation(TheoryPropagation::new(
            Literal::from_dimacs(2),
            vec![Literal::from_dimacs(1)],
        ));
        manager.add_solver(Box::new(solver));
        
        let props = manager.propagate();
        assert_eq!(props.len(), 1);
    }

    #[test]
    fn test_theory_manager_backtrack() {
        let mut manager = TheoryManager::new();
        manager.add_solver(Box::new(MockTheorySolver::new()));
        
        let lit1 = Literal::from_dimacs(1);
        let lit2 = Literal::from_dimacs(2);
        
        manager.assert_literal(lit1, 1).unwrap();
        manager.assert_literal(lit2, 2).unwrap();
        manager.backtrack(1);
        // After backtracking, level 2 assertions should be removed
    }
}
