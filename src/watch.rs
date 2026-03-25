//! Two-watched-literal scheme for efficient propagation.

use crate::clause::ClauseRef;
use crate::formula::Formula;
use crate::literal::Literal;

/// A watcher entry for a clause.
#[derive(Clone, Copy, Debug)]
pub struct Watcher {
    /// The clause being watched.
    pub clause: ClauseRef,
    /// The other watched literal (blocker optimization).
    pub blocker: Literal,
}

impl Watcher {
    /// Create a new watcher.
    pub fn new(clause: ClauseRef, blocker: Literal) -> Self {
        Watcher { clause, blocker }
    }
}

/// Watch lists indexed by literal.
pub struct WatchLists {
    /// watches[lit.index()] = list of watchers for when lit becomes false.
    watches: Vec<Vec<Watcher>>,
}

impl WatchLists {
    /// Create watch lists for a given number of variables.
    pub fn new(num_vars: u32) -> Self {
        // 2 literals per variable
        let size = (2 * num_vars) as usize;
        WatchLists {
            watches: vec![Vec::new(); size],
        }
    }

    /// Add a watcher for a literal.
    pub fn add_watch(&mut self, lit: Literal, clause: ClauseRef, blocker: Literal) {
        let idx = lit.index();
        if idx >= self.watches.len() {
            self.watches.resize(idx + 1, Vec::new());
        }
        self.watches[idx].push(Watcher::new(clause, blocker));
    }

    /// Remove a watcher for a literal.
    pub fn remove_watch(&mut self, lit: Literal, clause: ClauseRef) {
        let idx = lit.index();
        if idx < self.watches.len() {
            self.watches[idx].retain(|w| w.clause != clause);
        }
    }

    /// Get watchers for a literal (clauses to check when lit becomes false).
    pub fn watches(&self, lit: Literal) -> &[Watcher] {
        let idx = lit.index();
        if idx < self.watches.len() {
            &self.watches[idx]
        } else {
            &[]
        }
    }

    /// Get mutable watchers for a literal.
    pub fn watches_mut(&mut self, lit: Literal) -> &mut Vec<Watcher> {
        let idx = lit.index();
        if idx >= self.watches.len() {
            self.watches.resize(idx + 1, Vec::new());
        }
        &mut self.watches[idx]
    }

    /// Update blocker for a watcher.
    pub fn update_blocker(&mut self, lit: Literal, clause: ClauseRef, new_blocker: Literal) {
        let idx = lit.index();
        if idx < self.watches.len() {
            for w in &mut self.watches[idx] {
                if w.clause == clause {
                    w.blocker = new_blocker;
                    break;
                }
            }
        }
    }

    /// Clear all watches.
    pub fn clear(&mut self) {
        for list in &mut self.watches {
            list.clear();
        }
    }

    /// Total number of watchers.
    pub fn total_watchers(&self) -> usize {
        self.watches.iter().map(|v| v.len()).sum()
    }
}

/// Initialize watch lists from a formula.
/// 
/// Each clause with 2+ literals watches its first two literals.
/// Unit clauses watch their single literal.
/// Empty clauses are not watched.
pub fn init_watches(formula: &Formula) -> WatchLists {
    let mut watches = WatchLists::new(formula.num_vars());
    
    for (idx, clause) in formula.iter_clauses() {
        let len = clause.len();
        if len >= 2 {
            // Watch first two literals
            let lit0 = clause[0];
            let lit1 = clause[1];
            // When lit0 becomes false, check this clause (blocker is lit1)
            watches.add_watch(lit0.negate(), idx, lit1);
            // When lit1 becomes false, check this clause (blocker is lit0)
            watches.add_watch(lit1.negate(), idx, lit0);
        } else if len == 1 {
            // Unit clause: watch the single literal
            let lit = clause[0];
            watches.add_watch(lit.negate(), idx, lit);
        }
        // Empty clauses are not watched (they represent conflict)
    }
    
    watches
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clause::Clause;

    fn lit(v: i32) -> Literal {
        Literal::from_dimacs(v)
    }

    fn clause(lits: &[i32]) -> Clause {
        Clause::new(lits.iter().map(|&v| lit(v)).collect())
    }

    #[test]
    fn test_new_watchlists() {
        let w = WatchLists::new(5);
        assert_eq!(w.watches(lit(1)).len(), 0);
        assert_eq!(w.watches(lit(-1)).len(), 0);
    }

    #[test]
    fn test_add_watch() {
        let mut w = WatchLists::new(3);
        
        w.add_watch(lit(-1), 0, lit(2));
        w.add_watch(lit(-1), 1, lit(3));
        w.add_watch(lit(-2), 0, lit(1));
        
        assert_eq!(w.watches(lit(-1)).len(), 2);
        assert_eq!(w.watches(lit(-2)).len(), 1);
        assert_eq!(w.watches(lit(-3)).len(), 0);
    }

    #[test]
    fn test_remove_watch() {
        let mut w = WatchLists::new(3);
        w.add_watch(lit(-1), 0, lit(2));
        w.add_watch(lit(-1), 1, lit(3));
        
        w.remove_watch(lit(-1), 0);
        
        assert_eq!(w.watches(lit(-1)).len(), 1);
        assert_eq!(w.watches(lit(-1))[0].clause, 1);
    }

    #[test]
    fn test_watcher_properties() {
        let mut w = WatchLists::new(3);
        w.add_watch(lit(-1), 5, lit(2));
        
        let watchers = w.watches(lit(-1));
        assert_eq!(watchers.len(), 1);
        assert_eq!(watchers[0].clause, 5);
        assert_eq!(watchers[0].blocker.to_dimacs(), 2);
    }

    #[test]
    fn test_update_blocker() {
        let mut w = WatchLists::new(3);
        w.add_watch(lit(-1), 0, lit(2));
        
        w.update_blocker(lit(-1), 0, lit(3));
        
        assert_eq!(w.watches(lit(-1))[0].blocker.to_dimacs(), 3);
    }

    #[test]
    fn test_init_watches_binary() {
        let mut f = Formula::new();
        f.add_clause(clause(&[1, 2]));
        
        let w = init_watches(&f);
        
        // When 1 becomes false (-1), check clause 0
        assert_eq!(w.watches(lit(-1)).len(), 1);
        assert_eq!(w.watches(lit(-1))[0].clause, 0);
        assert_eq!(w.watches(lit(-1))[0].blocker.to_dimacs(), 2);
        
        // When 2 becomes false (-2), check clause 0
        assert_eq!(w.watches(lit(-2)).len(), 1);
        assert_eq!(w.watches(lit(-2))[0].clause, 0);
        assert_eq!(w.watches(lit(-2))[0].blocker.to_dimacs(), 1);
    }

    #[test]
    fn test_init_watches_larger_clause() {
        let mut f = Formula::new();
        f.add_clause(clause(&[1, 2, 3, 4]));
        
        let w = init_watches(&f);
        
        // Only first two literals are watched
        assert_eq!(w.watches(lit(-1)).len(), 1);
        assert_eq!(w.watches(lit(-2)).len(), 1);
        assert_eq!(w.watches(lit(-3)).len(), 0);
        assert_eq!(w.watches(lit(-4)).len(), 0);
    }

    #[test]
    fn test_init_watches_unit() {
        let mut f = Formula::new();
        f.add_clause(clause(&[1]));
        
        let w = init_watches(&f);
        
        assert_eq!(w.watches(lit(-1)).len(), 1);
        assert_eq!(w.watches(lit(-1))[0].clause, 0);
    }

    #[test]
    fn test_init_watches_multiple() {
        let mut f = Formula::new();
        f.add_clause(clause(&[1, 2]));     // 0
        f.add_clause(clause(&[1, 3]));     // 1
        f.add_clause(clause(&[-1, 2]));    // 2
        
        let w = init_watches(&f);
        
        // -1 watches clauses 0 and 1
        assert_eq!(w.watches(lit(-1)).len(), 2);
        // 1 watches clause 2
        assert_eq!(w.watches(lit(1)).len(), 1);
        assert_eq!(w.watches(lit(1))[0].clause, 2);
    }

    #[test]
    fn test_total_watchers() {
        let mut f = Formula::new();
        f.add_clause(clause(&[1, 2]));
        f.add_clause(clause(&[3, 4]));
        
        let w = init_watches(&f);
        
        // 4 watchers total (2 per clause)
        assert_eq!(w.total_watchers(), 4);
    }

    #[test]
    fn test_clear() {
        let mut w = WatchLists::new(3);
        w.add_watch(lit(-1), 0, lit(2));
        w.add_watch(lit(-2), 1, lit(3));
        
        w.clear();
        
        assert_eq!(w.watches(lit(-1)).len(), 0);
        assert_eq!(w.watches(lit(-2)).len(), 0);
    }
}
