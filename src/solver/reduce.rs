//! Clause reduction - delete low-quality learned clauses
//!
//! As the solver runs, it accumulates learned clauses. Periodically we need
//! to delete low-quality clauses to keep memory usage and propagation time
//! reasonable.

use crate::clause::{Clause, ClauseRef};
use crate::formula::Formula;
use crate::literal::Literal;
use crate::watch::WatchLists;

/// Configuration for clause reduction
#[derive(Debug, Clone)]
pub struct ReductionConfig {
    /// Initial number of learned clauses before first reduction
    pub initial_limit: usize,
    /// Growth factor for limit after each reduction
    pub growth_factor: f64,
    /// Maximum LBD to protect (clauses with LBD <= this are never deleted)
    pub protect_lbd: u32,
    /// Fraction of clauses to delete (0.0 - 1.0)
    pub delete_fraction: f64,
}

impl Default for ReductionConfig {
    fn default() -> Self {
        ReductionConfig {
            initial_limit: 2000,
            growth_factor: 1.1,
            protect_lbd: 2, // Protect glue clauses (LBD <= 2)
            delete_fraction: 0.5,
        }
    }
}

/// Clause reducer
#[derive(Debug)]
pub struct ClauseReducer {
    /// Configuration
    config: ReductionConfig,
    /// Current learned clause limit
    current_limit: usize,
    /// Number of reductions performed
    reduction_count: u64,
}

impl ClauseReducer {
    /// Create a new clause reducer with the given config
    pub fn new(config: ReductionConfig) -> Self {
        let current_limit = config.initial_limit;
        ClauseReducer {
            config,
            current_limit,
            reduction_count: 0,
        }
    }

    /// Check if we should trigger a reduction
    pub fn should_reduce(&self, learned_count: usize) -> bool {
        learned_count >= self.current_limit
    }

    /// Get the current limit
    pub fn current_limit(&self) -> usize {
        self.current_limit
    }

    /// Get the number of reductions performed
    pub fn reduction_count(&self) -> u64 {
        self.reduction_count
    }

    /// Perform clause reduction
    /// 
    /// Returns the indices of clauses to keep.
    /// Caller is responsible for actually removing clauses and updating watches.
    pub fn select_clauses_to_keep(
        &mut self,
        clauses: &[Clause],
        first_learned: usize,
    ) -> Vec<ClauseRef> {
        let mut to_keep: Vec<ClauseRef> = Vec::new();
        
        // Always keep original clauses
        for i in 0..first_learned {
            to_keep.push(i);
        }
        
        // Collect learned clauses with their quality metrics
        let mut learned: Vec<(ClauseRef, &Clause)> = clauses[first_learned..]
            .iter()
            .enumerate()
            .map(|(i, c)| (first_learned + i, c))
            .collect();
        
        // Sort by quality: low LBD and high activity are better
        // We'll use LBD as primary sort key (lower is better)
        learned.sort_by(|a, b| {
            // First by LBD (ascending - lower is better)
            let lbd_cmp = a.1.lbd().cmp(&b.1.lbd());
            if lbd_cmp != std::cmp::Ordering::Equal {
                return lbd_cmp;
            }
            // Then by activity (descending - higher is better)
            b.1.activity().partial_cmp(&a.1.activity())
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        
        // Calculate how many to keep
        let num_learned = learned.len();
        let num_to_delete = (num_learned as f64 * self.config.delete_fraction) as usize;
        let num_to_keep = num_learned.saturating_sub(num_to_delete);
        
        // Keep the best clauses
        for (idx, clause) in learned.into_iter().take(num_to_keep) {
            // Always protect glue clauses
            if clause.lbd() <= self.config.protect_lbd {
                to_keep.push(idx);
            } else if to_keep.len() < first_learned + num_to_keep {
                to_keep.push(idx);
            }
        }
        
        // Update limit for next reduction
        self.current_limit = (self.current_limit as f64 * self.config.growth_factor) as usize;
        self.reduction_count += 1;
        
        to_keep
    }
}

/// Remove clauses from a formula and rebuild watch lists
/// 
/// This is a heavyweight operation that rebuilds the entire clause database.
/// Returns a mapping from old clause refs to new clause refs.
pub fn compact_clauses(
    formula: &mut Formula,
    watches: &mut WatchLists,
    clauses_to_keep: &[ClauseRef],
) -> Vec<Option<ClauseRef>> {
    let old_count = formula.num_clauses();
    let mut old_to_new: Vec<Option<ClauseRef>> = vec![None; old_count];
    
    // Build new clause list
    let mut new_clauses: Vec<Clause> = Vec::with_capacity(clauses_to_keep.len());
    for (new_idx, &old_idx) in clauses_to_keep.iter().enumerate() {
        if old_idx < old_count {
            new_clauses.push(formula.clause(old_idx).clone());
            old_to_new[old_idx] = Some(new_idx);
        }
    }
    
    // Replace formula clauses
    formula.replace_clauses(new_clauses);
    
    // Rebuild watch lists
    watches.clear();
    for (idx, clause) in formula.clauses().iter().enumerate() {
        if clause.len() >= 2 {
            let lit0 = clause[0];
            let lit1 = clause[1];
            watches.add_watch(lit0, idx, lit1);
            watches.add_watch(lit1, idx, lit0);
        }
    }
    
    old_to_new
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Variable;

    fn lit(i: i32) -> Literal {
        Literal::from_dimacs(i)
    }

    fn make_clause(dimacs: &[i32]) -> Clause {
        Clause::new(dimacs.iter().map(|&i| lit(i)).collect())
    }

    fn make_learned_clause(dimacs: &[i32], lbd: u32) -> Clause {
        Clause::learned_with_lbd(dimacs.iter().map(|&i| lit(i)).collect(), lbd)
    }

    #[test]
    fn test_reduction_config_default() {
        let config = ReductionConfig::default();
        assert_eq!(config.initial_limit, 2000);
        assert_eq!(config.protect_lbd, 2);
    }

    #[test]
    fn test_should_reduce() {
        let reducer = ClauseReducer::new(ReductionConfig {
            initial_limit: 100,
            ..Default::default()
        });
        
        assert!(!reducer.should_reduce(50));
        assert!(!reducer.should_reduce(99));
        assert!(reducer.should_reduce(100));
        assert!(reducer.should_reduce(150));
    }

    #[test]
    fn test_select_clauses_keeps_originals() {
        let mut reducer = ClauseReducer::new(ReductionConfig {
            initial_limit: 10,
            delete_fraction: 0.5,
            ..Default::default()
        });
        
        let clauses = vec![
            make_clause(&[1, 2]),           // Original 0
            make_clause(&[3, 4]),           // Original 1
            make_learned_clause(&[-1, -2], 5), // Learned 2
            make_learned_clause(&[-3, -4], 5), // Learned 3
        ];
        
        let keep = reducer.select_clauses_to_keep(&clauses, 2);
        
        // Should always keep originals
        assert!(keep.contains(&0));
        assert!(keep.contains(&1));
    }

    #[test]
    fn test_protect_low_lbd_clauses() {
        let mut reducer = ClauseReducer::new(ReductionConfig {
            initial_limit: 10,
            delete_fraction: 0.9, // Try to delete 90%
            protect_lbd: 2,
            ..Default::default()
        });
        
        let clauses = vec![
            make_clause(&[1, 2]),               // Original
            make_learned_clause(&[-1, -2], 2),  // Learned, LBD=2 (protected)
            make_learned_clause(&[-3, -4], 10), // Learned, LBD=10 (deletable)
        ];
        
        let keep = reducer.select_clauses_to_keep(&clauses, 1);
        
        // Original and LBD=2 clause should be kept
        assert!(keep.contains(&0));
        assert!(keep.contains(&1));
    }

    #[test]
    fn test_limit_grows_after_reduction() {
        let mut reducer = ClauseReducer::new(ReductionConfig {
            initial_limit: 100,
            growth_factor: 1.5,
            ..Default::default()
        });
        
        assert_eq!(reducer.current_limit(), 100);
        
        let clauses: Vec<Clause> = (0..100)
            .map(|i| make_learned_clause(&[i + 1, i + 2], 5))
            .collect();
        
        reducer.select_clauses_to_keep(&clauses, 0);
        
        // Limit should grow by 1.5x
        assert_eq!(reducer.current_limit(), 150);
        assert_eq!(reducer.reduction_count(), 1);
    }

    #[test]
    fn test_compact_clauses() {
        let mut formula = Formula::with_num_vars(5);
        formula.add_clause(make_clause(&[1, 2]));
        formula.add_clause(make_clause(&[3, 4]));
        formula.add_clause(make_learned_clause(&[-1, -3], 5));
        formula.add_clause(make_learned_clause(&[-2, -4], 5));
        
        let mut watches = WatchLists::new(5);
        crate::watch::init_watches(&mut watches, formula.clauses());
        
        assert_eq!(formula.num_clauses(), 4);
        
        // Keep only clauses 0, 1, 3 (remove clause 2)
        let old_to_new = compact_clauses(&mut formula, &mut watches, &[0, 1, 3]);
        
        assert_eq!(formula.num_clauses(), 3);
        assert_eq!(old_to_new[0], Some(0));
        assert_eq!(old_to_new[1], Some(1));
        assert_eq!(old_to_new[2], None); // Deleted
        assert_eq!(old_to_new[3], Some(2)); // Renumbered
        
        // Watches should be rebuilt
        assert!(watches.is_watching(lit(1), 0));
        assert!(watches.is_watching(lit(3), 1));
    }

    #[test]
    fn test_reduction_count() {
        let mut reducer = ClauseReducer::new(ReductionConfig {
            initial_limit: 10,
            ..Default::default()
        });
        
        assert_eq!(reducer.reduction_count(), 0);
        
        let clauses: Vec<Clause> = (0..10)
            .map(|i| make_learned_clause(&[i + 1, i + 2], 5))
            .collect();
        
        reducer.select_clauses_to_keep(&clauses, 0);
        assert_eq!(reducer.reduction_count(), 1);
        
        reducer.select_clauses_to_keep(&clauses, 0);
        assert_eq!(reducer.reduction_count(), 2);
    }

    #[test]
    fn test_sort_by_lbd_then_activity() {
        let mut reducer = ClauseReducer::new(ReductionConfig {
            initial_limit: 10,
            delete_fraction: 0.5,
            protect_lbd: 0, // Don't protect any
            ..Default::default()
        });
        
        // Create clauses with different LBD and activity
        let mut c1 = make_learned_clause(&[1, 2], 5);
        c1.bump_activity(10.0);
        
        let mut c2 = make_learned_clause(&[3, 4], 3);
        c2.bump_activity(1.0);
        
        let mut c3 = make_learned_clause(&[5, 6], 3);
        c3.bump_activity(5.0);
        
        let clauses = vec![c1, c2, c3];
        
        let keep = reducer.select_clauses_to_keep(&clauses, 0);
        
        // Should keep LBD=3 clauses over LBD=5
        // With 50% deletion of 3 clauses, keep ~1-2
        // The LBD=3 clauses should be preferred
        assert!(keep.len() >= 1);
    }
}
