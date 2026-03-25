//! Clause type for CNF formulas.

use crate::literal::Literal;
use std::fmt;

/// Reference to a clause in a formula.
pub type ClauseRef = usize;

/// A clause is a disjunction of literals.
#[derive(Clone)]
pub struct Clause {
    /// The literals in this clause.
    literals: Vec<Literal>,
    /// Whether this is a learned clause (vs original).
    learned: bool,
    /// Activity score for VSIDS-style clause management.
    activity: f64,
    /// Literal Block Distance for clause quality estimation.
    lbd: u32,
}

impl Clause {
    /// Create a new original (non-learned) clause.
    pub fn new(literals: Vec<Literal>) -> Self {
        Clause {
            literals,
            learned: false,
            activity: 0.0,
            lbd: 0,
        }
    }

    /// Create a new learned clause.
    pub fn learned(literals: Vec<Literal>) -> Self {
        Clause {
            literals,
            learned: true,
            activity: 0.0,
            lbd: 0,
        }
    }

    /// Create a learned clause with a specific LBD.
    pub fn learned_with_lbd(literals: Vec<Literal>, lbd: u32) -> Self {
        Clause {
            literals,
            learned: true,
            activity: 0.0,
            lbd,
        }
    }

    /// Get the number of literals in this clause.
    pub fn len(&self) -> usize {
        self.literals.len()
    }

    /// Check if this clause is empty (represents a contradiction).
    pub fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }

    /// Check if this is a unit clause (single literal).
    pub fn is_unit(&self) -> bool {
        self.literals.len() == 1
    }

    /// Check if this is a binary clause (two literals).
    pub fn is_binary(&self) -> bool {
        self.literals.len() == 2
    }

    /// Get the literals in this clause.
    pub fn literals(&self) -> &[Literal] {
        &self.literals
    }

    /// Get mutable access to literals (for clause minimization).
    pub fn literals_mut(&mut self) -> &mut Vec<Literal> {
        &mut self.literals
    }

    /// Get a specific literal by index.
    pub fn get(&self, idx: usize) -> Option<Literal> {
        self.literals.get(idx).copied()
    }

    /// Check if this is a learned clause.
    pub fn is_learned(&self) -> bool {
        self.learned
    }

    /// Get the activity score.
    pub fn activity(&self) -> f64 {
        self.activity
    }

    /// Bump the activity score.
    pub fn bump_activity(&mut self, amount: f64) {
        self.activity += amount;
    }

    /// Decay the activity score.
    pub fn decay_activity(&mut self, factor: f64) {
        self.activity *= factor;
    }

    /// Get the LBD (Literal Block Distance).
    pub fn lbd(&self) -> u32 {
        self.lbd
    }

    /// Set the LBD.
    pub fn set_lbd(&mut self, lbd: u32) {
        self.lbd = lbd;
    }

    /// Swap two literals in the clause (for watch list maintenance).
    pub fn swap(&mut self, i: usize, j: usize) {
        self.literals.swap(i, j);
    }

    /// Get iterator over literals.
    pub fn iter(&self) -> impl Iterator<Item = Literal> + '_ {
        self.literals.iter().copied()
    }
}

impl fmt::Debug for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, lit) in self.literals.iter().enumerate() {
            if i > 0 {
                write!(f, " ∨ ")?;
            }
            write!(f, "{:?}", lit)?;
        }
        write!(f, ")")
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for lit in &self.literals {
            write!(f, "{} ", lit.to_dimacs())?;
        }
        write!(f, "0")
    }
}

impl std::ops::Index<usize> for Clause {
    type Output = Literal;

    fn index(&self, idx: usize) -> &Self::Output {
        &self.literals[idx]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn lit(v: i32) -> Literal {
        Literal::from_dimacs(v)
    }

    #[test]
    fn test_clause_creation() {
        let clause = Clause::new(vec![lit(1), lit(-2), lit(3)]);
        assert_eq!(clause.len(), 3);
        assert!(!clause.is_empty());
        assert!(!clause.is_unit());
        assert!(!clause.is_learned());
    }

    #[test]
    fn test_empty_clause() {
        let clause = Clause::new(vec![]);
        assert!(clause.is_empty());
        assert!(!clause.is_unit());
    }

    #[test]
    fn test_unit_clause() {
        let clause = Clause::new(vec![lit(1)]);
        assert!(clause.is_unit());
        assert!(!clause.is_empty());
    }

    #[test]
    fn test_binary_clause() {
        let clause = Clause::new(vec![lit(1), lit(-2)]);
        assert!(clause.is_binary());
        assert!(!clause.is_unit());
    }

    #[test]
    fn test_learned_clause() {
        let clause = Clause::learned(vec![lit(1), lit(-2)]);
        assert!(clause.is_learned());
        
        let clause = Clause::learned_with_lbd(vec![lit(1)], 2);
        assert!(clause.is_learned());
        assert_eq!(clause.lbd(), 2);
    }

    #[test]
    fn test_clause_literals() {
        let clause = Clause::new(vec![lit(1), lit(-2), lit(3)]);
        let lits: Vec<_> = clause.iter().collect();
        assert_eq!(lits.len(), 3);
        assert_eq!(lits[0].to_dimacs(), 1);
        assert_eq!(lits[1].to_dimacs(), -2);
        assert_eq!(lits[2].to_dimacs(), 3);
    }

    #[test]
    fn test_clause_indexing() {
        let clause = Clause::new(vec![lit(1), lit(-2), lit(3)]);
        assert_eq!(clause[0].to_dimacs(), 1);
        assert_eq!(clause[1].to_dimacs(), -2);
        assert_eq!(clause[2].to_dimacs(), 3);
    }

    #[test]
    fn test_clause_get() {
        let clause = Clause::new(vec![lit(1), lit(-2)]);
        assert_eq!(clause.get(0).unwrap().to_dimacs(), 1);
        assert_eq!(clause.get(1).unwrap().to_dimacs(), -2);
        assert!(clause.get(2).is_none());
    }

    #[test]
    fn test_clause_swap() {
        let mut clause = Clause::new(vec![lit(1), lit(-2), lit(3)]);
        clause.swap(0, 2);
        assert_eq!(clause[0].to_dimacs(), 3);
        assert_eq!(clause[2].to_dimacs(), 1);
    }

    #[test]
    fn test_activity() {
        let mut clause = Clause::new(vec![lit(1)]);
        assert_eq!(clause.activity(), 0.0);
        
        clause.bump_activity(1.0);
        assert_eq!(clause.activity(), 1.0);
        
        clause.bump_activity(0.5);
        assert_eq!(clause.activity(), 1.5);
        
        clause.decay_activity(0.5);
        assert_eq!(clause.activity(), 0.75);
    }

    #[test]
    fn test_lbd() {
        let mut clause = Clause::new(vec![lit(1)]);
        assert_eq!(clause.lbd(), 0);
        
        clause.set_lbd(3);
        assert_eq!(clause.lbd(), 3);
    }

    #[test]
    fn test_display() {
        let clause = Clause::new(vec![lit(1), lit(-2), lit(3)]);
        assert_eq!(format!("{}", clause), "1 -2 3 0");
    }
}
