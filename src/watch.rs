//! Two-watched-literal scheme for efficient unit propagation

use crate::clause::ClauseRef;
use crate::literal::Literal;

/// A watcher entry in a watch list
#[derive(Debug, Clone, Copy)]
pub struct Watcher {
    /// The clause being watched
    pub clause: ClauseRef,
    /// The other watched literal (blocker for quick check)
    pub blocker: Literal,
}

impl Watcher {
    /// Create a new watcher
    pub fn new(clause: ClauseRef, blocker: Literal) -> Self {
        Watcher { clause, blocker }
    }
}

/// Watch lists for the two-watched-literal scheme
/// 
/// Each literal has a list of clauses that are watching it.
/// When a literal becomes false, we check its watch list.
#[derive(Debug)]
pub struct WatchLists {
    /// Watch list per literal, indexed by literal.index()
    watches: Vec<Vec<Watcher>>,
}

impl WatchLists {
    /// Create empty watch lists for the given number of variables
    pub fn new(num_vars: u32) -> Self {
        // Need 2 entries per variable (positive and negative literals)
        let size = 2 * (num_vars as usize + 1);
        WatchLists {
            watches: vec![Vec::new(); size],
        }
    }

    /// Resize to accommodate more variables
    pub fn resize(&mut self, num_vars: u32) {
        let size = 2 * (num_vars as usize + 1);
        if self.watches.len() < size {
            self.watches.resize(size, Vec::new());
        }
    }

    /// Add a watcher for a literal
    pub fn add_watch(&mut self, lit: Literal, clause: ClauseRef, blocker: Literal) {
        let idx = lit.index();
        if idx >= self.watches.len() {
            self.resize(lit.variable().index());
        }
        self.watches[idx].push(Watcher::new(clause, blocker));
    }

    /// Remove a watcher for a literal
    pub fn remove_watch(&mut self, lit: Literal, clause: ClauseRef) {
        let idx = lit.index();
        if idx < self.watches.len() {
            self.watches[idx].retain(|w| w.clause != clause);
        }
    }

    /// Get the watch list for a literal
    pub fn watches(&self, lit: Literal) -> &[Watcher] {
        let idx = lit.index();
        if idx < self.watches.len() {
            &self.watches[idx]
        } else {
            &[]
        }
    }

    /// Get a mutable reference to the watch list for a literal
    pub fn watches_mut(&mut self, lit: Literal) -> &mut Vec<Watcher> {
        let idx = lit.index();
        if idx >= self.watches.len() {
            self.resize(lit.variable().index());
        }
        &mut self.watches[idx]
    }

    /// Check if a clause is watched by a literal
    pub fn is_watching(&self, lit: Literal, clause: ClauseRef) -> bool {
        self.watches(lit).iter().any(|w| w.clause == clause)
    }

    /// Clear all watch lists
    pub fn clear(&mut self) {
        for list in &mut self.watches {
            list.clear();
        }
    }

    /// Get the total number of watchers
    pub fn total_watchers(&self) -> usize {
        self.watches.iter().map(|v| v.len()).sum()
    }
}

/// Initialize watch lists from a formula
pub fn init_watches(watches: &mut WatchLists, clauses: &[crate::clause::Clause]) {
    for (idx, clause) in clauses.iter().enumerate() {
        if clause.len() >= 2 {
            // Watch the first two literals
            let lit0 = clause[0];
            let lit1 = clause[1];
            watches.add_watch(lit0, idx, lit1);
            watches.add_watch(lit1, idx, lit0);
        }
        // Unit clauses don't need watches (handled at initialization)
        // Empty clauses are trivially UNSAT
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clause::Clause;
    use crate::literal::Variable;

    fn lit(i: i32) -> Literal {
        Literal::from_dimacs(i)
    }

    #[test]
    fn test_watcher_creation() {
        let w = Watcher::new(5, lit(3));
        assert_eq!(w.clause, 5);
        assert_eq!(w.blocker, lit(3));
    }

    #[test]
    fn test_watch_lists_creation() {
        let watches = WatchLists::new(10);
        
        // Should have space for variables 1-10 (both polarities)
        assert!(watches.watches(lit(10)).is_empty());
        assert!(watches.watches(lit(-10)).is_empty());
    }

    #[test]
    fn test_add_watch() {
        let mut watches = WatchLists::new(5);
        
        watches.add_watch(lit(1), 0, lit(2));
        watches.add_watch(lit(1), 1, lit(3));
        watches.add_watch(lit(-2), 2, lit(1));
        
        assert_eq!(watches.watches(lit(1)).len(), 2);
        assert_eq!(watches.watches(lit(-2)).len(), 1);
        assert!(watches.watches(lit(2)).is_empty());
    }

    #[test]
    fn test_remove_watch() {
        let mut watches = WatchLists::new(5);
        
        watches.add_watch(lit(1), 0, lit(2));
        watches.add_watch(lit(1), 1, lit(3));
        
        watches.remove_watch(lit(1), 0);
        
        let list = watches.watches(lit(1));
        assert_eq!(list.len(), 1);
        assert_eq!(list[0].clause, 1);
    }

    #[test]
    fn test_is_watching() {
        let mut watches = WatchLists::new(5);
        
        watches.add_watch(lit(1), 0, lit(2));
        
        assert!(watches.is_watching(lit(1), 0));
        assert!(!watches.is_watching(lit(1), 1));
        assert!(!watches.is_watching(lit(2), 0));
    }

    #[test]
    fn test_resize() {
        let mut watches = WatchLists::new(2);
        
        // Should auto-resize when adding watch for larger variable
        watches.add_watch(lit(10), 0, lit(5));
        
        assert_eq!(watches.watches(lit(10)).len(), 1);
    }

    #[test]
    fn test_clear() {
        let mut watches = WatchLists::new(5);
        
        watches.add_watch(lit(1), 0, lit(2));
        watches.add_watch(lit(3), 1, lit(4));
        
        watches.clear();
        
        assert!(watches.watches(lit(1)).is_empty());
        assert!(watches.watches(lit(3)).is_empty());
    }

    #[test]
    fn test_total_watchers() {
        let mut watches = WatchLists::new(5);
        
        assert_eq!(watches.total_watchers(), 0);
        
        watches.add_watch(lit(1), 0, lit(2));
        watches.add_watch(lit(1), 1, lit(3));
        watches.add_watch(lit(-2), 2, lit(1));
        
        assert_eq!(watches.total_watchers(), 3);
    }

    #[test]
    fn test_init_watches() {
        let clauses = vec![
            Clause::new(vec![lit(1), lit(2), lit(3)]),
            Clause::new(vec![lit(-1), lit(-2)]),
            Clause::new(vec![lit(4)]), // Unit clause - no watches
        ];
        
        let mut watches = WatchLists::new(4);
        init_watches(&mut watches, &clauses);
        
        // Clause 0 watches lit(1) and lit(2)
        assert!(watches.is_watching(lit(1), 0));
        assert!(watches.is_watching(lit(2), 0));
        assert!(!watches.is_watching(lit(3), 0));
        
        // Clause 1 watches lit(-1) and lit(-2)
        assert!(watches.is_watching(lit(-1), 1));
        assert!(watches.is_watching(lit(-2), 1));
        
        // Unit clause 2 has no watches
        assert_eq!(watches.total_watchers(), 4); // 2 per binary+ clause
    }

    #[test]
    fn test_watches_mut() {
        let mut watches = WatchLists::new(5);
        
        watches.add_watch(lit(1), 0, lit(2));
        
        let list = watches.watches_mut(lit(1));
        list[0].blocker = lit(5);
        
        assert_eq!(watches.watches(lit(1))[0].blocker, lit(5));
    }
}
