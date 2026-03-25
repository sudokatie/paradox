//! CNF Formula representation.

use crate::clause::{Clause, ClauseRef};
use crate::literal::{Literal, Variable};

/// A CNF (Conjunctive Normal Form) formula.
#[derive(Clone)]
pub struct Formula {
    /// All clauses in the formula.
    clauses: Vec<Clause>,
    /// Number of variables (max variable index).
    num_vars: u32,
}

impl Formula {
    /// Create an empty formula.
    pub fn new() -> Self {
        Formula {
            clauses: Vec::new(),
            num_vars: 0,
        }
    }

    /// Create a formula with a known number of variables.
    pub fn with_capacity(num_vars: u32, num_clauses: usize) -> Self {
        Formula {
            clauses: Vec::with_capacity(num_clauses),
            num_vars,
        }
    }

    /// Add a clause to the formula.
    pub fn add_clause(&mut self, clause: Clause) -> ClauseRef {
        // Update num_vars if needed
        for lit in clause.iter() {
            let var = lit.variable().index();
            if var > self.num_vars {
                self.num_vars = var;
            }
        }
        let idx = self.clauses.len();
        self.clauses.push(clause);
        idx
    }

    /// Get the number of variables.
    pub fn num_vars(&self) -> u32 {
        self.num_vars
    }

    /// Set the number of variables (from DIMACS header).
    pub fn set_num_vars(&mut self, num_vars: u32) {
        self.num_vars = num_vars;
    }

    /// Get the number of clauses.
    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }

    /// Get all clauses.
    pub fn clauses(&self) -> &[Clause] {
        &self.clauses
    }

    /// Get a specific clause.
    pub fn clause(&self, idx: ClauseRef) -> &Clause {
        &self.clauses[idx]
    }

    /// Get a mutable reference to a clause.
    pub fn clause_mut(&mut self, idx: ClauseRef) -> &mut Clause {
        &mut self.clauses[idx]
    }

    /// Iterate over clauses with their indices.
    pub fn iter_clauses(&self) -> impl Iterator<Item = (ClauseRef, &Clause)> {
        self.clauses.iter().enumerate()
    }

    /// Iterate over all variables.
    pub fn variables(&self) -> impl Iterator<Item = Variable> {
        (1..=self.num_vars).map(Variable::new)
    }

    /// Check if the formula is empty (trivially SAT).
    pub fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }

    /// Check if the formula contains an empty clause (trivially UNSAT).
    pub fn has_empty_clause(&self) -> bool {
        self.clauses.iter().any(|c| c.is_empty())
    }

    /// Get unit clauses (for initial propagation).
    pub fn unit_clauses(&self) -> impl Iterator<Item = (ClauseRef, Literal)> + '_ {
        self.clauses
            .iter()
            .enumerate()
            .filter(|(_, c)| c.is_unit())
            .map(|(i, c)| (i, c[0]))
    }

    /// Remove a clause (marks it as deleted, doesn't actually remove).
    /// Returns the removed clause.
    pub fn remove_clause(&mut self, idx: ClauseRef) -> Clause {
        // For now, just swap remove. In a real solver, we'd mark deleted.
        self.clauses.swap_remove(idx)
    }
}

impl Default for Formula {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Debug for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Formula({} vars, {} clauses):", self.num_vars, self.clauses.len())?;
        for (i, clause) in self.clauses.iter().enumerate() {
            writeln!(f, "  [{}] {:?}", i, clause)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Literal;

    fn lit(v: i32) -> Literal {
        Literal::from_dimacs(v)
    }

    fn clause(lits: &[i32]) -> Clause {
        Clause::new(lits.iter().map(|&v| lit(v)).collect())
    }

    #[test]
    fn test_empty_formula() {
        let f = Formula::new();
        assert_eq!(f.num_vars(), 0);
        assert_eq!(f.num_clauses(), 0);
        assert!(f.is_empty());
        assert!(!f.has_empty_clause());
    }

    #[test]
    fn test_add_clause() {
        let mut f = Formula::new();
        let idx = f.add_clause(clause(&[1, -2, 3]));
        
        assert_eq!(idx, 0);
        assert_eq!(f.num_clauses(), 1);
        assert_eq!(f.num_vars(), 3);
    }

    #[test]
    fn test_num_vars_tracking() {
        let mut f = Formula::new();
        f.add_clause(clause(&[1, -2]));
        assert_eq!(f.num_vars(), 2);
        
        f.add_clause(clause(&[5, -3]));
        assert_eq!(f.num_vars(), 5);
        
        // Adding smaller variables doesn't reduce num_vars
        f.add_clause(clause(&[1, 2]));
        assert_eq!(f.num_vars(), 5);
    }

    #[test]
    fn test_with_capacity() {
        let mut f = Formula::with_capacity(10, 20);
        assert_eq!(f.num_vars(), 10);
        f.add_clause(clause(&[1, 2]));
        assert_eq!(f.num_vars(), 10);
    }

    #[test]
    fn test_clause_access() {
        let mut f = Formula::new();
        f.add_clause(clause(&[1, -2]));
        f.add_clause(clause(&[3, 4]));
        
        assert_eq!(f.clause(0).len(), 2);
        assert_eq!(f.clause(1).len(), 2);
        assert_eq!(f.clause(0)[0].to_dimacs(), 1);
        assert_eq!(f.clause(1)[0].to_dimacs(), 3);
    }

    #[test]
    fn test_clause_mut() {
        let mut f = Formula::new();
        f.add_clause(clause(&[1, -2]));
        
        f.clause_mut(0).swap(0, 1);
        assert_eq!(f.clause(0)[0].to_dimacs(), -2);
    }

    #[test]
    fn test_empty_clause_detection() {
        let mut f = Formula::new();
        f.add_clause(clause(&[1, 2]));
        assert!(!f.has_empty_clause());
        
        f.add_clause(Clause::new(vec![]));
        assert!(f.has_empty_clause());
    }

    #[test]
    fn test_unit_clauses() {
        let mut f = Formula::new();
        f.add_clause(clause(&[1, 2]));    // not unit
        f.add_clause(clause(&[3]));       // unit
        f.add_clause(clause(&[-4]));      // unit
        f.add_clause(clause(&[5, 6, 7])); // not unit
        
        let units: Vec<_> = f.unit_clauses().collect();
        assert_eq!(units.len(), 2);
        assert_eq!(units[0].1.to_dimacs(), 3);
        assert_eq!(units[1].1.to_dimacs(), -4);
    }

    #[test]
    fn test_iter_clauses() {
        let mut f = Formula::new();
        f.add_clause(clause(&[1]));
        f.add_clause(clause(&[2]));
        
        let indices: Vec<_> = f.iter_clauses().map(|(i, _)| i).collect();
        assert_eq!(indices, vec![0, 1]);
    }

    #[test]
    fn test_variables() {
        let mut f = Formula::new();
        f.add_clause(clause(&[1, -2, 3]));
        
        let vars: Vec<_> = f.variables().collect();
        assert_eq!(vars.len(), 3);
        assert_eq!(vars[0].index(), 1);
        assert_eq!(vars[1].index(), 2);
        assert_eq!(vars[2].index(), 3);
    }
}
