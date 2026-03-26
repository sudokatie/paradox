//! Clause learning for CDCL.
//!
//! After conflict analysis produces a learned clause, this module handles:
//! - Adding the clause to the formula
//! - Setting up watch lists for the new clause  
//! - Bumping VSIDS activities for involved variables
//! - Tracking statistics

use crate::clause::Clause;
use crate::formula::Formula;
use crate::literal::Literal;
use crate::watch::WatchLists;

use super::decide::Vsids;

/// Statistics about learned clauses.
#[derive(Debug, Default, Clone)]
pub struct LearnStats {
    /// Total clauses learned.
    pub total_learned: u64,
    /// Total literals in learned clauses.
    pub total_literals: u64,
    /// Minimum LBD seen.
    pub min_lbd: u32,
    /// Maximum LBD seen.
    pub max_lbd: u32,
    /// Sum of LBDs (for average).
    pub sum_lbd: u64,
}

impl LearnStats {
    /// Record a learned clause.
    pub fn record(&mut self, clause_len: usize, lbd: u32) {
        self.total_learned += 1;
        self.total_literals += clause_len as u64;
        
        if self.total_learned == 1 {
            self.min_lbd = lbd;
            self.max_lbd = lbd;
        } else {
            self.min_lbd = self.min_lbd.min(lbd);
            self.max_lbd = self.max_lbd.max(lbd);
        }
        self.sum_lbd += lbd as u64;
    }
    
    /// Average LBD of learned clauses.
    pub fn avg_lbd(&self) -> f64 {
        if self.total_learned == 0 {
            0.0
        } else {
            self.sum_lbd as f64 / self.total_learned as f64
        }
    }
    
    /// Average learned clause size.
    pub fn avg_size(&self) -> f64 {
        if self.total_learned == 0 {
            0.0
        } else {
            self.total_literals as f64 / self.total_learned as f64
        }
    }
}

/// Add a learned clause to the formula and set up watches.
///
/// The learned clause should have the asserting literal at position 0.
/// Returns the clause index.
pub fn add_learned_clause(
    literals: Vec<Literal>,
    lbd: u32,
    formula: &mut Formula,
    watches: &mut WatchLists,
) -> usize {
    let clause_idx = formula.num_clauses();
    
    // Create clause marked as learned
    let mut clause = Clause::new(literals.clone());
    clause.set_learned(true);
    clause.set_lbd(lbd);
    
    // Add to formula
    formula.add_clause(clause);
    
    // Set up watches (if clause has at least 2 literals)
    if literals.len() >= 2 {
        // Watch the first two literals
        // When literals[0] becomes false, check this clause
        // When literals[1] becomes false, check this clause
        watches.add_watch(literals[0].negate(), clause_idx, literals[1]);
        watches.add_watch(literals[1].negate(), clause_idx, literals[0]);
    } else if literals.len() == 1 {
        // Unit clause - no watches needed (will be propagated immediately)
    }
    
    clause_idx
}

/// Bump VSIDS activities for variables involved in a conflict.
pub fn bump_involved_vars(involved: &[usize], vsids: &mut Vsids) {
    for &var_idx in involved {
        let var = crate::literal::Variable::from_index(var_idx);
        vsids.bump(var);
    }
    // Decay after bumping
    vsids.decay();
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(v: i32) -> Literal {
        Literal::from_dimacs(v)
    }

    #[test]
    fn test_learn_stats() {
        let mut stats = LearnStats::default();
        
        stats.record(5, 3);
        assert_eq!(stats.total_learned, 1);
        assert_eq!(stats.total_literals, 5);
        assert_eq!(stats.min_lbd, 3);
        assert_eq!(stats.max_lbd, 3);
        
        stats.record(3, 2);
        assert_eq!(stats.total_learned, 2);
        assert_eq!(stats.total_literals, 8);
        assert_eq!(stats.min_lbd, 2);
        assert_eq!(stats.max_lbd, 3);
    }

    #[test]
    fn test_avg_lbd() {
        let mut stats = LearnStats::default();
        stats.record(5, 2);
        stats.record(5, 4);
        assert!((stats.avg_lbd() - 3.0).abs() < 0.01);
    }

    #[test]
    fn test_add_learned_clause() {
        let mut f = Formula::new();
        // Add a dummy clause first so we have variables
        f.add_clause(Clause::new(vec![lit(1), lit(2), lit(3)]));
        
        let mut watches = WatchLists::new(f.num_vars());
        
        let learned = vec![lit(-1), lit(2)];
        let idx = add_learned_clause(learned, 2, &mut f, &mut watches);
        
        assert_eq!(idx, 1);
        assert_eq!(f.num_clauses(), 2);
        assert!(f.clause(idx).is_learned());
        assert_eq!(f.clause(idx).lbd(), 2);
    }

    #[test]
    fn test_add_unit_learned() {
        let mut f = Formula::new();
        f.add_clause(Clause::new(vec![lit(1), lit(2)]));
        
        let mut watches = WatchLists::new(f.num_vars());
        
        let learned = vec![lit(1)];
        let idx = add_learned_clause(learned, 1, &mut f, &mut watches);
        
        assert_eq!(idx, 1);
        assert!(f.clause(idx).is_learned());
    }

    #[test]
    fn test_bump_involved() {
        let mut vsids = Vsids::new(5);
        
        let involved = vec![0, 2, 4];
        bump_involved_vars(&involved, &mut vsids);
        
        let var0 = crate::literal::Variable::from_index(0);
        let var1 = crate::literal::Variable::from_index(1);
        let var2 = crate::literal::Variable::from_index(2);
        
        assert!(vsids.activity(var0) > 0.0);
        assert_eq!(vsids.activity(var1), 0.0);
        assert!(vsids.activity(var2) > 0.0);
    }
}
