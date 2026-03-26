//! Clause reduction (deletion) for CDCL.
//!
//! As the solver learns clauses, memory grows. Periodically we delete
//! low-quality learned clauses to keep the database manageable.
//! Quality is measured by LBD (Literal Block Distance).

use crate::clause::ClauseRef;
use crate::formula::Formula;
use crate::watch::WatchLists;

/// Configuration for clause reduction.
#[derive(Debug, Clone)]
pub struct ReduceConfig {
    /// Initial limit on learned clauses before reduction.
    pub initial_limit: usize,
    /// Growth factor for limit after each reduction.
    pub growth_factor: f64,
    /// Protect clauses with LBD <= this value.
    pub protect_lbd: u32,
    /// Fraction of learned clauses to delete.
    pub delete_fraction: f64,
}

impl Default for ReduceConfig {
    fn default() -> Self {
        ReduceConfig {
            initial_limit: 2000,
            growth_factor: 1.1,
            protect_lbd: 2,
            delete_fraction: 0.5,
        }
    }
}

/// Manages clause reduction.
#[derive(Debug)]
pub struct ClauseReducer {
    config: ReduceConfig,
    /// Current limit before next reduction.
    current_limit: usize,
    /// Number of reductions performed.
    reductions: u64,
    /// Total clauses deleted.
    total_deleted: u64,
}

impl ClauseReducer {
    /// Create a new reducer with the given config.
    pub fn new(config: ReduceConfig) -> Self {
        let initial_limit = config.initial_limit;
        ClauseReducer {
            config,
            current_limit: initial_limit,
            reductions: 0,
            total_deleted: 0,
        }
    }

    /// Check if reduction should be performed.
    pub fn should_reduce(&self, num_learned: usize) -> bool {
        num_learned >= self.current_limit
    }

    /// Perform clause reduction.
    ///
    /// Returns the number of clauses deleted.
    pub fn reduce(&mut self, formula: &mut Formula, watches: &mut WatchLists) -> usize {
        let num_original = formula.num_original_clauses();
        let num_clauses = formula.num_clauses();
        let num_learned = num_clauses - num_original;
        
        if num_learned == 0 {
            return 0;
        }
        
        // Collect learned clause indices and LBDs
        let mut learned_info: Vec<(ClauseRef, u32)> = (num_original..num_clauses)
            .filter_map(|i| {
                let clause = formula.clause(i);
                if clause.is_learned() {
                    Some((i, clause.lbd()))
                } else {
                    None
                }
            })
            .collect();
        
        // Sort by LBD (higher LBD = worse = delete first)
        learned_info.sort_by(|a, b| b.1.cmp(&a.1));
        
        // Calculate how many to delete
        let delete_count = ((learned_info.len() as f64 * self.config.delete_fraction) as usize)
            .min(learned_info.len());
        
        // Mark clauses for deletion (but protect low-LBD clauses)
        let mut to_delete = Vec::new();
        for (clause_idx, lbd) in learned_info.into_iter().take(delete_count) {
            if lbd > self.config.protect_lbd {
                to_delete.push(clause_idx);
            }
        }
        
        let deleted = to_delete.len();
        
        // Delete marked clauses
        if deleted > 0 {
            // Mark clauses as deleted in formula
            for &clause_idx in &to_delete {
                formula.mark_deleted(clause_idx);
            }
            
            // Compact formula (optional, can defer)
            formula.compact();
            
            // Rebuild watch lists
            *watches = crate::watch::init_watches(formula);
        }
        
        self.reductions += 1;
        self.total_deleted += deleted as u64;
        
        // Update limit for next reduction
        self.current_limit = (self.current_limit as f64 * self.config.growth_factor) as usize;
        
        deleted
    }

    /// Get number of reductions performed.
    pub fn num_reductions(&self) -> u64 {
        self.reductions
    }

    /// Get total clauses deleted.
    pub fn total_deleted(&self) -> u64 {
        self.total_deleted
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clause::Clause;
    use crate::literal::Literal;

    fn lit(v: i32) -> Literal {
        Literal::from_dimacs(v)
    }

    fn clause(lits: &[i32]) -> Clause {
        Clause::new(lits.iter().map(|&v| lit(v)).collect())
    }

    fn learned_clause(lits: &[i32], lbd: u32) -> Clause {
        let mut c = clause(lits);
        c.set_learned(true);
        c.set_lbd(lbd);
        c
    }

    #[test]
    fn test_should_reduce() {
        let reducer = ClauseReducer::new(ReduceConfig {
            initial_limit: 100,
            ..Default::default()
        });
        
        assert!(!reducer.should_reduce(50));
        assert!(!reducer.should_reduce(99));
        assert!(reducer.should_reduce(100));
        assert!(reducer.should_reduce(200));
    }

    #[test]
    fn test_reduce_deletes_high_lbd() {
        let mut f = Formula::new();
        
        // Add original clauses
        f.add_clause(clause(&[1, 2, 3]));
        f.add_clause(clause(&[-1, -2]));
        f.mark_original_end();
        
        // Add learned clauses with varying LBD
        f.add_clause(learned_clause(&[1, -3], 2));     // protect_lbd = 2, protected
        f.add_clause(learned_clause(&[-2, 3], 5));     // high LBD, delete
        f.add_clause(learned_clause(&[2, -1], 10));    // very high LBD, delete
        f.add_clause(learned_clause(&[-3, 1], 3));     // medium LBD, maybe delete
        
        let mut watches = WatchLists::new(f.num_vars());
        
        let mut reducer = ClauseReducer::new(ReduceConfig {
            initial_limit: 1,
            protect_lbd: 2,
            delete_fraction: 0.5,
            ..Default::default()
        });
        
        let deleted = reducer.reduce(&mut f, &mut watches);
        
        // Should delete some high-LBD clauses
        assert!(deleted > 0);
        assert!(reducer.total_deleted() > 0);
    }

    #[test]
    fn test_limit_grows() {
        let mut reducer = ClauseReducer::new(ReduceConfig {
            initial_limit: 100,
            growth_factor: 2.0,
            protect_lbd: 1,
            delete_fraction: 0.5,
        });
        
        assert_eq!(reducer.current_limit, 100);
        
        let mut f = Formula::new();
        f.add_clause(clause(&[1, 2]));
        f.mark_original_end();
        
        // Add learned clauses so reduce() actually runs
        f.add_clause(learned_clause(&[1, -2], 5));
        f.add_clause(learned_clause(&[-1, 2], 5));
        
        let mut watches = WatchLists::new(f.num_vars());
        
        reducer.reduce(&mut f, &mut watches);
        
        // Limit should grow after reduction
        assert_eq!(reducer.current_limit, 200);
    }

    #[test]
    fn test_protect_low_lbd() {
        let mut f = Formula::new();
        f.add_clause(clause(&[1, 2]));
        f.mark_original_end();
        
        // All learned clauses have LBD = 2 (protected)
        f.add_clause(learned_clause(&[1, -2], 2));
        f.add_clause(learned_clause(&[-1, 2], 2));
        f.add_clause(learned_clause(&[2, 1], 2));
        
        let mut watches = WatchLists::new(f.num_vars());
        
        let mut reducer = ClauseReducer::new(ReduceConfig {
            initial_limit: 1,
            protect_lbd: 2,
            delete_fraction: 1.0, // Try to delete all
            ..Default::default()
        });
        
        let deleted = reducer.reduce(&mut f, &mut watches);
        
        // None should be deleted (all protected)
        assert_eq!(deleted, 0);
    }

    #[test]
    fn test_no_learned_clauses() {
        let mut f = Formula::new();
        f.add_clause(clause(&[1, 2]));
        f.add_clause(clause(&[-1, -2]));
        f.mark_original_end();
        
        let mut watches = WatchLists::new(f.num_vars());
        
        let mut reducer = ClauseReducer::new(ReduceConfig::default());
        
        let deleted = reducer.reduce(&mut f, &mut watches);
        
        assert_eq!(deleted, 0);
    }
}
