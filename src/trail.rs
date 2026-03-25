//! Decision trail for backtracking

use crate::literal::Literal;

/// The decision trail tracks the order of assignments
/// and allows efficient backtracking to previous decision levels
#[derive(Debug)]
pub struct Trail {
    /// Literals in assignment order
    assignments: Vec<Literal>,
    /// Index into assignments where each level starts
    /// levels[i] is the index where level i begins
    levels: Vec<usize>,
    /// Index of next literal to propagate
    propagate_head: usize,
}

impl Trail {
    /// Create a new empty trail
    pub fn new() -> Self {
        Trail {
            assignments: Vec::new(),
            levels: vec![0], // Level 0 starts at index 0
            propagate_head: 0,
        }
    }

    /// Push a literal onto the trail (generic push)
    pub fn push(&mut self, lit: Literal) {
        self.assignments.push(lit);
    }

    /// Peek at the next literal to propagate (without advancing)
    pub fn peek_propagate(&self) -> Option<&Literal> {
        self.assignments.get(self.propagate_head)
    }

    /// Advance the propagation head
    pub fn advance_propagate(&mut self) {
        if self.propagate_head < self.assignments.len() {
            self.propagate_head += 1;
        }
    }

    /// Get the current decision level
    pub fn current_level(&self) -> u32 {
        (self.levels.len() - 1) as u32
    }

    /// Start a new decision level
    pub fn new_level(&mut self) {
        self.levels.push(self.assignments.len());
    }

    /// Push a decision literal (starts a new level)
    pub fn push_decision(&mut self, lit: Literal) {
        self.new_level();
        self.assignments.push(lit);
    }

    /// Push a propagated literal (same level)
    pub fn push_propagation(&mut self, lit: Literal) {
        self.assignments.push(lit);
    }

    /// Push a literal at level 0 (unit propagation at root)
    pub fn push_at_root(&mut self, lit: Literal) {
        debug_assert!(self.current_level() == 0);
        self.assignments.push(lit);
    }

    /// Backtrack to a specific level, returning unassigned literals
    /// Returns literals in reverse order (most recent first)
    pub fn backtrack_to(&mut self, level: u32) -> Vec<Literal> {
        let level = level as usize;
        
        if level >= self.levels.len() - 1 {
            return Vec::new();
        }
        
        let start_idx = self.levels[level + 1];
        let unassigned: Vec<Literal> = self.assignments[start_idx..].iter().rev().copied().collect();
        
        self.assignments.truncate(start_idx);
        self.levels.truncate(level + 1);
        
        // Reset propagate head if it's past the new end
        if self.propagate_head > start_idx {
            self.propagate_head = start_idx;
        }
        
        unassigned
    }

    /// Get the number of assignments
    pub fn len(&self) -> usize {
        self.assignments.len()
    }

    /// Check if trail is empty
    pub fn is_empty(&self) -> bool {
        self.assignments.is_empty()
    }

    /// Get the last assigned literal
    pub fn last(&self) -> Option<&Literal> {
        self.assignments.last()
    }

    /// Iterate over all assignments in order
    pub fn iter(&self) -> impl Iterator<Item = &Literal> {
        self.assignments.iter()
    }

    /// Get assignments at a specific level
    pub fn level_assignments(&self, level: u32) -> &[Literal] {
        let level = level as usize;
        if level >= self.levels.len() {
            return &[];
        }
        
        let start = self.levels[level];
        let end = if level + 1 < self.levels.len() {
            self.levels[level + 1]
        } else {
            self.assignments.len()
        };
        
        &self.assignments[start..end]
    }

    /// Get the decision literal at a specific level (first literal at that level)
    pub fn decision_at(&self, level: u32) -> Option<&Literal> {
        if level == 0 {
            return None; // Level 0 has no decision
        }
        
        let level = level as usize;
        if level >= self.levels.len() {
            return None;
        }
        
        self.assignments.get(self.levels[level])
    }

    /// Get all literals assigned at or after the given level
    pub fn literals_from_level(&self, level: u32) -> &[Literal] {
        let level = level as usize;
        if level >= self.levels.len() {
            return &[];
        }
        let start = self.levels[level];
        &self.assignments[start..]
    }

    /// Get the index where the given level starts
    pub fn level_start(&self, level: u32) -> usize {
        self.levels.get(level as usize).copied().unwrap_or(self.assignments.len())
    }

    /// Count assignments at the current level
    pub fn count_at_current_level(&self) -> usize {
        let start = *self.levels.last().unwrap();
        self.assignments.len() - start
    }
}

impl Default for Trail {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Variable;

    fn lit(i: i32) -> Literal {
        Literal::from_dimacs(i)
    }

    #[test]
    fn test_trail_creation() {
        let trail = Trail::new();
        assert_eq!(trail.current_level(), 0);
        assert_eq!(trail.len(), 0);
        assert!(trail.is_empty());
    }

    #[test]
    fn test_push_at_root() {
        let mut trail = Trail::new();
        
        trail.push_at_root(lit(1));
        trail.push_at_root(lit(-2));
        
        assert_eq!(trail.current_level(), 0);
        assert_eq!(trail.len(), 2);
    }

    #[test]
    fn test_push_decision() {
        let mut trail = Trail::new();
        
        trail.push_decision(lit(1));
        assert_eq!(trail.current_level(), 1);
        assert_eq!(trail.len(), 1);
        
        trail.push_decision(lit(2));
        assert_eq!(trail.current_level(), 2);
        assert_eq!(trail.len(), 2);
    }

    #[test]
    fn test_push_propagation() {
        let mut trail = Trail::new();
        
        trail.push_decision(lit(1));
        trail.push_propagation(lit(2));
        trail.push_propagation(lit(3));
        
        assert_eq!(trail.current_level(), 1);
        assert_eq!(trail.len(), 3);
    }

    #[test]
    fn test_backtrack() {
        let mut trail = Trail::new();
        
        // Level 0: root propagations
        trail.push_at_root(lit(1));
        
        // Level 1: decide x2, propagate x3
        trail.push_decision(lit(2));
        trail.push_propagation(lit(3));
        
        // Level 2: decide x4, propagate x5, x6
        trail.push_decision(lit(4));
        trail.push_propagation(lit(5));
        trail.push_propagation(lit(6));
        
        assert_eq!(trail.current_level(), 2);
        assert_eq!(trail.len(), 6);
        
        // Backtrack to level 1
        let unassigned = trail.backtrack_to(1);
        
        assert_eq!(unassigned.len(), 3);
        assert_eq!(unassigned[0], lit(6)); // Most recent first
        assert_eq!(unassigned[1], lit(5));
        assert_eq!(unassigned[2], lit(4));
        
        assert_eq!(trail.current_level(), 1);
        assert_eq!(trail.len(), 3);
    }

    #[test]
    fn test_backtrack_to_root() {
        let mut trail = Trail::new();
        
        trail.push_at_root(lit(1));
        trail.push_decision(lit(2));
        trail.push_decision(lit(3));
        
        let unassigned = trail.backtrack_to(0);
        
        assert_eq!(unassigned.len(), 2);
        assert_eq!(trail.current_level(), 0);
        assert_eq!(trail.len(), 1);
    }

    #[test]
    fn test_backtrack_noop() {
        let mut trail = Trail::new();
        
        trail.push_decision(lit(1));
        
        // Backtrack to current level does nothing
        let unassigned = trail.backtrack_to(1);
        assert!(unassigned.is_empty());
        assert_eq!(trail.len(), 1);
        
        // Backtrack to future level does nothing
        let unassigned = trail.backtrack_to(5);
        assert!(unassigned.is_empty());
    }

    #[test]
    fn test_level_assignments() {
        let mut trail = Trail::new();
        
        trail.push_at_root(lit(1));
        trail.push_at_root(lit(2));
        trail.push_decision(lit(3));
        trail.push_propagation(lit(4));
        trail.push_decision(lit(5));
        
        let level0 = trail.level_assignments(0);
        assert_eq!(level0.len(), 2);
        
        let level1 = trail.level_assignments(1);
        assert_eq!(level1.len(), 2);
        assert_eq!(level1[0], lit(3));
        assert_eq!(level1[1], lit(4));
        
        let level2 = trail.level_assignments(2);
        assert_eq!(level2.len(), 1);
        assert_eq!(level2[0], lit(5));
    }

    #[test]
    fn test_decision_at() {
        let mut trail = Trail::new();
        
        trail.push_at_root(lit(1));
        trail.push_decision(lit(2));
        trail.push_propagation(lit(3));
        trail.push_decision(lit(4));
        
        assert_eq!(trail.decision_at(0), None);
        assert_eq!(trail.decision_at(1), Some(&lit(2)));
        assert_eq!(trail.decision_at(2), Some(&lit(4)));
        assert_eq!(trail.decision_at(3), None);
    }

    #[test]
    fn test_iter() {
        let mut trail = Trail::new();
        
        trail.push_at_root(lit(1));
        trail.push_decision(lit(2));
        trail.push_propagation(lit(3));
        
        let lits: Vec<_> = trail.iter().copied().collect();
        assert_eq!(lits, vec![lit(1), lit(2), lit(3)]);
    }

    #[test]
    fn test_last() {
        let mut trail = Trail::new();
        
        assert_eq!(trail.last(), None);
        
        trail.push_decision(lit(5));
        assert_eq!(trail.last(), Some(&lit(5)));
        
        trail.push_propagation(lit(-3));
        assert_eq!(trail.last(), Some(&lit(-3)));
    }

    #[test]
    fn test_count_at_current_level() {
        let mut trail = Trail::new();
        
        trail.push_at_root(lit(1));
        trail.push_at_root(lit(2));
        assert_eq!(trail.count_at_current_level(), 2);
        
        trail.push_decision(lit(3));
        assert_eq!(trail.count_at_current_level(), 1);
        
        trail.push_propagation(lit(4));
        trail.push_propagation(lit(5));
        assert_eq!(trail.count_at_current_level(), 3);
    }
}
