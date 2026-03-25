//! Decision trail for CDCL.
//!
//! The trail records the order of assignments and marks decision levels.

use crate::literal::Literal;

/// Decision trail tracking assignment order and levels.
pub struct Trail {
    /// Ordered list of assigned literals.
    assignments: Vec<Literal>,
    /// Start index of each decision level in assignments.
    /// levels[0] is always 0 (start of level 0).
    /// levels[d] gives the index where level d starts.
    levels: Vec<usize>,
}

impl Trail {
    /// Create a new empty trail.
    pub fn new() -> Self {
        Trail {
            assignments: Vec::new(),
            levels: vec![0], // Level 0 starts at index 0
        }
    }

    /// Get the current decision level.
    pub fn current_level(&self) -> u32 {
        (self.levels.len() - 1) as u32
    }

    /// Start a new decision level.
    pub fn new_level(&mut self) {
        self.levels.push(self.assignments.len());
    }

    /// Push a decision literal (starts a new level).
    pub fn push_decision(&mut self, lit: Literal) {
        self.new_level();
        self.assignments.push(lit);
    }

    /// Push a propagated literal (same level).
    pub fn push_propagation(&mut self, lit: Literal) {
        self.assignments.push(lit);
    }

    /// Backtrack to a specific level, returning removed literals.
    /// After this call, current_level() == level.
    pub fn backtrack_to(&mut self, level: u32) -> Vec<Literal> {
        let level = level as usize;
        if level >= self.levels.len() - 1 {
            // Already at or below this level
            return Vec::new();
        }

        // Find where this level starts
        let start = self.levels[level + 1];
        let removed: Vec<Literal> = self.assignments.drain(start..).collect();
        
        // Remove level markers
        self.levels.truncate(level + 1);
        
        removed
    }

    /// Get all literals assigned at a specific level.
    pub fn level_literals(&self, level: u32) -> &[Literal] {
        let level = level as usize;
        if level >= self.levels.len() {
            return &[];
        }
        let start = self.levels[level];
        let end = self.levels.get(level + 1).copied().unwrap_or(self.assignments.len());
        &self.assignments[start..end]
    }

    /// Get the decision literal for a level (first literal at that level).
    /// Returns None for level 0 (no decision at root).
    pub fn decision_at(&self, level: u32) -> Option<Literal> {
        if level == 0 {
            return None;
        }
        let level = level as usize;
        if level >= self.levels.len() {
            return None;
        }
        let start = self.levels[level];
        self.assignments.get(start).copied()
    }

    /// Get the number of literals on the trail.
    pub fn len(&self) -> usize {
        self.assignments.len()
    }

    /// Check if trail is empty.
    pub fn is_empty(&self) -> bool {
        self.assignments.is_empty()
    }

    /// Iterate over all literals in assignment order.
    pub fn iter(&self) -> impl Iterator<Item = Literal> + '_ {
        self.assignments.iter().copied()
    }

    /// Iterate in reverse order (most recent first).
    pub fn iter_rev(&self) -> impl Iterator<Item = Literal> + '_ {
        self.assignments.iter().rev().copied()
    }

    /// Get the most recent literal.
    pub fn last(&self) -> Option<Literal> {
        self.assignments.last().copied()
    }

    /// Get literal by trail index.
    pub fn get(&self, idx: usize) -> Option<Literal> {
        self.assignments.get(idx).copied()
    }

    /// Get the index of the start of a level.
    pub fn level_start(&self, level: u32) -> usize {
        self.levels.get(level as usize).copied().unwrap_or(self.assignments.len())
    }

    /// Get literals from a specific index to the end.
    pub fn from_index(&self, idx: usize) -> &[Literal] {
        if idx >= self.assignments.len() {
            &[]
        } else {
            &self.assignments[idx..]
        }
    }
}

impl Default for Trail {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Debug for Trail {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Trail[")?;
        let mut level = 0;
        for (i, lit) in self.assignments.iter().enumerate() {
            // Check if we crossed into a new level
            while level + 1 < self.levels.len() && i >= self.levels[level + 1] {
                level += 1;
                write!(f, " | ")?;
            }
            if i > 0 && (level == 0 || i != self.levels[level]) {
                write!(f, ", ")?;
            }
            write!(f, "{}", lit.to_dimacs())?;
        }
        write!(f, "]")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(v: i32) -> Literal {
        Literal::from_dimacs(v)
    }

    #[test]
    fn test_new_trail() {
        let t = Trail::new();
        assert_eq!(t.current_level(), 0);
        assert!(t.is_empty());
        assert_eq!(t.len(), 0);
    }

    #[test]
    fn test_push_propagation() {
        let mut t = Trail::new();
        t.push_propagation(lit(1));
        t.push_propagation(lit(-2));
        
        assert_eq!(t.current_level(), 0);
        assert_eq!(t.len(), 2);
        
        let lits: Vec<_> = t.iter().collect();
        assert_eq!(lits.len(), 2);
        assert_eq!(lits[0].to_dimacs(), 1);
        assert_eq!(lits[1].to_dimacs(), -2);
    }

    #[test]
    fn test_push_decision() {
        let mut t = Trail::new();
        t.push_propagation(lit(1)); // Level 0 propagation
        t.push_decision(lit(2));    // Level 1 decision
        t.push_propagation(lit(3)); // Level 1 propagation
        
        assert_eq!(t.current_level(), 1);
        assert_eq!(t.len(), 3);
    }

    #[test]
    fn test_level_literals() {
        let mut t = Trail::new();
        t.push_propagation(lit(1));
        t.push_propagation(lit(2));
        t.push_decision(lit(3));
        t.push_propagation(lit(4));
        t.push_decision(lit(5));
        
        let level0: Vec<_> = t.level_literals(0).iter().map(|l| l.to_dimacs()).collect();
        assert_eq!(level0, vec![1, 2]);
        
        let level1: Vec<_> = t.level_literals(1).iter().map(|l| l.to_dimacs()).collect();
        assert_eq!(level1, vec![3, 4]);
        
        let level2: Vec<_> = t.level_literals(2).iter().map(|l| l.to_dimacs()).collect();
        assert_eq!(level2, vec![5]);
    }

    #[test]
    fn test_decision_at() {
        let mut t = Trail::new();
        t.push_propagation(lit(1));
        t.push_decision(lit(2));
        t.push_propagation(lit(3));
        t.push_decision(lit(4));
        
        assert!(t.decision_at(0).is_none()); // No decision at level 0
        assert_eq!(t.decision_at(1).unwrap().to_dimacs(), 2);
        assert_eq!(t.decision_at(2).unwrap().to_dimacs(), 4);
        assert!(t.decision_at(3).is_none()); // Level doesn't exist
    }

    #[test]
    fn test_backtrack() {
        let mut t = Trail::new();
        t.push_propagation(lit(1));
        t.push_decision(lit(2));
        t.push_propagation(lit(3));
        t.push_decision(lit(4));
        t.push_propagation(lit(5));
        
        // Backtrack to level 1
        let removed = t.backtrack_to(1);
        
        assert_eq!(t.current_level(), 1);
        assert_eq!(t.len(), 3);
        assert_eq!(removed.len(), 2);
        assert_eq!(removed[0].to_dimacs(), 4);
        assert_eq!(removed[1].to_dimacs(), 5);
    }

    #[test]
    fn test_backtrack_to_zero() {
        let mut t = Trail::new();
        t.push_propagation(lit(1));
        t.push_decision(lit(2));
        t.push_propagation(lit(3));
        
        let removed = t.backtrack_to(0);
        
        assert_eq!(t.current_level(), 0);
        assert_eq!(t.len(), 1);
        assert_eq!(removed.len(), 2);
    }

    #[test]
    fn test_backtrack_same_level() {
        let mut t = Trail::new();
        t.push_decision(lit(1));
        
        let removed = t.backtrack_to(1);
        
        assert_eq!(t.current_level(), 1);
        assert!(removed.is_empty());
    }

    #[test]
    fn test_iter_rev() {
        let mut t = Trail::new();
        t.push_propagation(lit(1));
        t.push_propagation(lit(2));
        t.push_propagation(lit(3));
        
        let rev: Vec<_> = t.iter_rev().map(|l| l.to_dimacs()).collect();
        assert_eq!(rev, vec![3, 2, 1]);
    }

    #[test]
    fn test_last() {
        let mut t = Trail::new();
        assert!(t.last().is_none());
        
        t.push_propagation(lit(1));
        assert_eq!(t.last().unwrap().to_dimacs(), 1);
        
        t.push_propagation(lit(2));
        assert_eq!(t.last().unwrap().to_dimacs(), 2);
    }

    #[test]
    fn test_from_index() {
        let mut t = Trail::new();
        t.push_propagation(lit(1));
        t.push_propagation(lit(2));
        t.push_propagation(lit(3));
        
        let from1: Vec<_> = t.from_index(1).iter().map(|l| l.to_dimacs()).collect();
        assert_eq!(from1, vec![2, 3]);
        
        let from3 = t.from_index(3);
        assert!(from3.is_empty());
    }
}
