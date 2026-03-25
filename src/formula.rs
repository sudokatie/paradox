//! CNF formula representation

use crate::clause::{Clause, ClauseRef};

/// A CNF formula is a conjunction of clauses
#[derive(Debug)]
pub struct Formula {
    /// The clauses in the formula
    clauses: Vec<Clause>,
    /// Number of variables in the formula
    num_vars: u32,
}

impl Formula {
    /// Create a new empty formula
    pub fn new() -> Self {
        Formula {
            clauses: Vec::new(),
            num_vars: 0,
        }
    }

    /// Create a formula with a known number of variables
    pub fn with_num_vars(num_vars: u32) -> Self {
        Formula {
            clauses: Vec::new(),
            num_vars,
        }
    }

    /// Add a clause to the formula
    pub fn add_clause(&mut self, clause: Clause) -> ClauseRef {
        // Update num_vars based on the literals in the clause
        for lit in clause.literals() {
            let var = lit.variable().index();
            if var > self.num_vars {
                self.num_vars = var;
            }
        }
        let idx = self.clauses.len();
        self.clauses.push(clause);
        idx
    }

    /// Get the number of variables
    pub fn num_vars(&self) -> u32 {
        self.num_vars
    }

    /// Set the number of variables (from DIMACS header)
    pub fn set_num_vars(&mut self, num_vars: u32) {
        self.num_vars = num_vars;
    }

    /// Get the number of clauses
    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }

    /// Check if the formula is empty
    pub fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }

    /// Get all clauses
    pub fn clauses(&self) -> &[Clause] {
        &self.clauses
    }

    /// Get a specific clause by reference
    pub fn clause(&self, idx: ClauseRef) -> &Clause {
        &self.clauses[idx]
    }

    /// Get a mutable reference to a clause
    pub fn clause_mut(&mut self, idx: ClauseRef) -> &mut Clause {
        &mut self.clauses[idx]
    }

    /// Iterate over clause references
    pub fn clause_refs(&self) -> impl Iterator<Item = ClauseRef> {
        0..self.clauses.len()
    }

    /// Check if formula contains an empty clause (trivially UNSAT)
    pub fn has_empty_clause(&self) -> bool {
        self.clauses.iter().any(|c| c.is_empty())
    }

    /// Get unit clauses
    pub fn unit_clauses(&self) -> impl Iterator<Item = (ClauseRef, &Clause)> {
        self.clauses
            .iter()
            .enumerate()
            .filter(|(_, c)| c.is_unit())
    }

    /// Replace all clauses (used for clause reduction)
    pub fn replace_clauses(&mut self, new_clauses: Vec<Clause>) {
        self.clauses = new_clauses;
        // Recalculate num_vars
        self.num_vars = 0;
        for clause in &self.clauses {
            for lit in clause.literals() {
                let var = lit.variable().index();
                if var > self.num_vars {
                    self.num_vars = var;
                }
            }
        }
    }
}

impl Default for Formula {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Literal;

    #[test]
    fn test_formula_creation() {
        let formula = Formula::new();
        assert_eq!(formula.num_vars(), 0);
        assert_eq!(formula.num_clauses(), 0);
        assert!(formula.is_empty());
    }

    #[test]
    fn test_formula_with_num_vars() {
        let formula = Formula::with_num_vars(10);
        assert_eq!(formula.num_vars(), 10);
        assert_eq!(formula.num_clauses(), 0);
    }

    #[test]
    fn test_add_clause() {
        let mut formula = Formula::new();
        
        let clause = Clause::new(vec![
            Literal::from_dimacs(1),
            Literal::from_dimacs(-2),
            Literal::from_dimacs(3),
        ]);
        
        let idx = formula.add_clause(clause);
        
        assert_eq!(idx, 0);
        assert_eq!(formula.num_clauses(), 1);
        assert_eq!(formula.num_vars(), 3);
    }

    #[test]
    fn test_num_vars_updates() {
        let mut formula = Formula::new();
        
        formula.add_clause(Clause::new(vec![
            Literal::from_dimacs(1),
            Literal::from_dimacs(2),
        ]));
        assert_eq!(formula.num_vars(), 2);
        
        formula.add_clause(Clause::new(vec![
            Literal::from_dimacs(5),
            Literal::from_dimacs(-3),
        ]));
        assert_eq!(formula.num_vars(), 5);
    }

    #[test]
    fn test_clause_access() {
        let mut formula = Formula::new();
        
        formula.add_clause(Clause::new(vec![Literal::from_dimacs(1)]));
        formula.add_clause(Clause::new(vec![Literal::from_dimacs(2)]));
        
        assert_eq!(formula.clause(0).len(), 1);
        assert_eq!(formula.clause(1).len(), 1);
    }

    #[test]
    fn test_has_empty_clause() {
        let mut formula = Formula::new();
        
        formula.add_clause(Clause::new(vec![Literal::from_dimacs(1)]));
        assert!(!formula.has_empty_clause());
        
        formula.add_clause(Clause::new(vec![]));
        assert!(formula.has_empty_clause());
    }

    #[test]
    fn test_unit_clauses() {
        let mut formula = Formula::new();
        
        formula.add_clause(Clause::new(vec![Literal::from_dimacs(1)]));
        formula.add_clause(Clause::new(vec![
            Literal::from_dimacs(2),
            Literal::from_dimacs(3),
        ]));
        formula.add_clause(Clause::new(vec![Literal::from_dimacs(-4)]));
        
        let units: Vec<_> = formula.unit_clauses().collect();
        assert_eq!(units.len(), 2);
    }

    #[test]
    fn test_clause_refs() {
        let mut formula = Formula::new();
        
        formula.add_clause(Clause::new(vec![Literal::from_dimacs(1)]));
        formula.add_clause(Clause::new(vec![Literal::from_dimacs(2)]));
        formula.add_clause(Clause::new(vec![Literal::from_dimacs(3)]));
        
        let refs: Vec<_> = formula.clause_refs().collect();
        assert_eq!(refs, vec![0, 1, 2]);
    }
}
