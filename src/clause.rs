//! Clause type for CNF formulas

use crate::literal::Literal;
use std::fmt;

/// Reference to a clause in the formula
pub type ClauseRef = usize;

/// A clause is a disjunction of literals
#[derive(Debug, Clone)]
pub struct Clause {
    /// The literals in the clause
    literals: Vec<Literal>,
    /// Whether this is a learned clause (vs original)
    learned: bool,
    /// Activity score for clause deletion (VSIDS-like)
    activity: f64,
    /// Literal Block Distance (for learned clause quality)
    lbd: u32,
}

impl Clause {
    /// Create a new original clause
    pub fn new(literals: Vec<Literal>) -> Self {
        Clause {
            literals,
            learned: false,
            activity: 0.0,
            lbd: 0,
        }
    }

    /// Create a learned clause
    pub fn learned(literals: Vec<Literal>) -> Self {
        Clause {
            literals,
            learned: true,
            activity: 0.0,
            lbd: 0,
        }
    }

    /// Create a learned clause with LBD
    pub fn learned_with_lbd(literals: Vec<Literal>, lbd: u32) -> Self {
        Clause {
            literals,
            learned: true,
            activity: 0.0,
            lbd,
        }
    }

    /// Get the number of literals
    pub fn len(&self) -> usize {
        self.literals.len()
    }

    /// Check if the clause is empty (always false)
    pub fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }

    /// Check if this is a unit clause
    pub fn is_unit(&self) -> bool {
        self.literals.len() == 1
    }

    /// Get the literals
    pub fn literals(&self) -> &[Literal] {
        &self.literals
    }

    /// Get a mutable reference to the literals
    pub fn literals_mut(&mut self) -> &mut Vec<Literal> {
        &mut self.literals
    }

    /// Check if this is a learned clause
    pub fn is_learned(&self) -> bool {
        self.learned
    }

    /// Get the activity score
    pub fn activity(&self) -> f64 {
        self.activity
    }

    /// Bump the activity score
    pub fn bump_activity(&mut self, amount: f64) {
        self.activity += amount;
    }

    /// Decay the activity score
    pub fn decay_activity(&mut self, factor: f64) {
        self.activity *= factor;
    }

    /// Get the LBD score
    pub fn lbd(&self) -> u32 {
        self.lbd
    }

    /// Set the LBD score
    pub fn set_lbd(&mut self, lbd: u32) {
        self.lbd = lbd;
    }

    /// Get a specific literal by index
    pub fn get(&self, index: usize) -> Option<&Literal> {
        self.literals.get(index)
    }

    /// Swap two literals (for watch list maintenance)
    pub fn swap(&mut self, i: usize, j: usize) {
        self.literals.swap(i, j);
    }
}

impl std::ops::Index<usize> for Clause {
    type Output = Literal;

    fn index(&self, index: usize) -> &Literal {
        &self.literals[index]
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, lit) in self.literals.iter().enumerate() {
            if i > 0 {
                write!(f, " ∨ ")?;
            }
            write!(f, "{}", lit)?;
        }
        write!(f, ")")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Variable;

    #[test]
    fn test_clause_creation() {
        let lits = vec![
            Literal::from_dimacs(1),
            Literal::from_dimacs(-2),
            Literal::from_dimacs(3),
        ];
        let clause = Clause::new(lits);

        assert_eq!(clause.len(), 3);
        assert!(!clause.is_empty());
        assert!(!clause.is_unit());
        assert!(!clause.is_learned());
    }

    #[test]
    fn test_unit_clause() {
        let lits = vec![Literal::from_dimacs(5)];
        let clause = Clause::new(lits);

        assert!(clause.is_unit());
        assert_eq!(clause.len(), 1);
    }

    #[test]
    fn test_empty_clause() {
        let clause = Clause::new(vec![]);
        assert!(clause.is_empty());
        assert!(!clause.is_unit());
    }

    #[test]
    fn test_learned_clause() {
        let lits = vec![
            Literal::from_dimacs(1),
            Literal::from_dimacs(-2),
        ];
        let clause = Clause::learned(lits);

        assert!(clause.is_learned());
    }

    #[test]
    fn test_clause_activity() {
        let mut clause = Clause::new(vec![Literal::from_dimacs(1)]);
        
        assert_eq!(clause.activity(), 0.0);
        
        clause.bump_activity(1.0);
        assert_eq!(clause.activity(), 1.0);
        
        clause.bump_activity(0.5);
        assert_eq!(clause.activity(), 1.5);
        
        clause.decay_activity(0.5);
        assert_eq!(clause.activity(), 0.75);
    }

    #[test]
    fn test_clause_lbd() {
        let mut clause = Clause::learned_with_lbd(
            vec![Literal::from_dimacs(1), Literal::from_dimacs(-2)],
            3,
        );

        assert_eq!(clause.lbd(), 3);
        clause.set_lbd(5);
        assert_eq!(clause.lbd(), 5);
    }

    #[test]
    fn test_clause_indexing() {
        let clause = Clause::new(vec![
            Literal::from_dimacs(1),
            Literal::from_dimacs(-2),
            Literal::from_dimacs(3),
        ]);

        assert_eq!(clause[0], Literal::from_dimacs(1));
        assert_eq!(clause[1], Literal::from_dimacs(-2));
        assert_eq!(clause[2], Literal::from_dimacs(3));
    }

    #[test]
    fn test_clause_swap() {
        let mut clause = Clause::new(vec![
            Literal::from_dimacs(1),
            Literal::from_dimacs(2),
            Literal::from_dimacs(3),
        ]);

        clause.swap(0, 2);
        assert_eq!(clause[0], Literal::from_dimacs(3));
        assert_eq!(clause[2], Literal::from_dimacs(1));
    }

    #[test]
    fn test_clause_display() {
        let clause = Clause::new(vec![
            Literal::from_dimacs(1),
            Literal::from_dimacs(-2),
        ]);
        let display = format!("{}", clause);
        assert!(display.contains("x1"));
        assert!(display.contains("~x2"));
    }
}
