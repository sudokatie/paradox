//! Clause learning - adding learned clauses to the solver
//!
//! After conflict analysis produces a learned clause, we need to:
//! 1. Add it to the formula
//! 2. Set up watches
//! 3. Bump VSIDS activities for involved variables

use crate::clause::{Clause, ClauseRef};
use crate::formula::Formula;
use crate::literal::Variable;
use crate::watch::WatchLists;

use super::vsids::Vsids;

/// Add a learned clause to the formula and set up watches
/// 
/// The learned clause should have the asserting literal first.
/// Returns the clause reference for the new clause.
pub fn add_learned_clause(
    formula: &mut Formula,
    watches: &mut WatchLists,
    clause: Clause,
) -> ClauseRef {
    let clause_ref = formula.add_clause(clause);
    
    // Set up watches for the new clause
    let lits = formula.clause(clause_ref).literals();
    
    if lits.len() >= 2 {
        // Watch the first two literals
        let lit0 = lits[0];
        let lit1 = lits[1];
        watches.add_watch(lit0, clause_ref, lit1);
        watches.add_watch(lit1, clause_ref, lit0);
    }
    // Unit learned clauses don't need watches (will be propagated immediately)
    
    clause_ref
}

/// Bump VSIDS activities for variables involved in a conflict
pub fn bump_conflict_vars(vsids: &mut Vsids, involved_vars: &[Variable]) {
    vsids.bump_all(involved_vars);
    vsids.decay();
}

/// Statistics about learned clauses
#[derive(Debug, Clone, Default)]
pub struct LearningStats {
    /// Total learned clauses
    pub total_learned: u64,
    /// Unit clauses learned
    pub unit_learned: u64,
    /// Binary clauses learned
    pub binary_learned: u64,
    /// Average LBD of learned clauses
    pub avg_lbd: f64,
}

impl LearningStats {
    /// Update statistics with a new learned clause
    pub fn record(&mut self, clause: &Clause) {
        self.total_learned += 1;
        
        match clause.len() {
            1 => self.unit_learned += 1,
            2 => self.binary_learned += 1,
            _ => {}
        }
        
        // Update running average of LBD
        let lbd = clause.lbd() as f64;
        let n = self.total_learned as f64;
        self.avg_lbd = self.avg_lbd * (n - 1.0) / n + lbd / n;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Literal;
    use crate::assignment::Assignments;

    fn lit(i: i32) -> Literal {
        Literal::from_dimacs(i)
    }

    fn make_clause(dimacs: &[i32]) -> Clause {
        Clause::new(dimacs.iter().map(|&i| lit(i)).collect())
    }

    fn make_learned_clause(dimacs: &[i32]) -> Clause {
        Clause::learned(dimacs.iter().map(|&i| lit(i)).collect())
    }

    #[test]
    fn test_add_learned_clause() {
        let mut formula = Formula::with_num_vars(5);
        formula.add_clause(make_clause(&[1, 2]));
        formula.add_clause(make_clause(&[3, 4]));
        
        let mut watches = WatchLists::new(5);
        crate::watch::init_watches(&mut watches, formula.clauses());
        
        assert_eq!(formula.num_clauses(), 2);
        
        // Add learned clause
        let learned = make_learned_clause(&[-1, -3, 5]);
        let clause_ref = add_learned_clause(&mut formula, &mut watches, learned);
        
        assert_eq!(formula.num_clauses(), 3);
        assert_eq!(clause_ref, 2);
        
        // Verify watches were set up
        assert!(watches.is_watching(lit(-1), clause_ref));
        assert!(watches.is_watching(lit(-3), clause_ref));
    }

    #[test]
    fn test_add_unit_learned_clause() {
        let mut formula = Formula::with_num_vars(3);
        let mut watches = WatchLists::new(3);
        
        // Unit clause - no watches needed
        let learned = make_learned_clause(&[1]);
        let clause_ref = add_learned_clause(&mut formula, &mut watches, learned);
        
        assert_eq!(formula.num_clauses(), 1);
        assert_eq!(clause_ref, 0);
        // No watches for unit clause
        assert_eq!(watches.total_watchers(), 0);
    }

    #[test]
    fn test_add_binary_learned_clause() {
        let mut formula = Formula::with_num_vars(3);
        let mut watches = WatchLists::new(3);
        
        // Binary clause
        let learned = make_learned_clause(&[1, -2]);
        let clause_ref = add_learned_clause(&mut formula, &mut watches, learned);
        
        assert_eq!(formula.num_clauses(), 1);
        // Both literals should be watching
        assert!(watches.is_watching(lit(1), clause_ref));
        assert!(watches.is_watching(lit(-2), clause_ref));
    }

    #[test]
    fn test_bump_conflict_vars() {
        let mut vsids = Vsids::new(5);
        
        let v1 = Variable::new(1);
        let v2 = Variable::new(2);
        let v3 = Variable::new(3);
        
        // Initially all zero
        assert_eq!(vsids.activity(v1), 0.0);
        
        // Bump involved vars
        bump_conflict_vars(&mut vsids, &[v1, v2]);
        
        // v1 and v2 should have activity
        assert!(vsids.activity(v1) > 0.0);
        assert!(vsids.activity(v2) > 0.0);
        assert_eq!(vsids.activity(v3), 0.0);
    }

    #[test]
    fn test_learning_stats() {
        let mut stats = LearningStats::default();
        
        assert_eq!(stats.total_learned, 0);
        
        // Record a unit clause
        let unit = Clause::learned_with_lbd(vec![lit(1)], 1);
        stats.record(&unit);
        assert_eq!(stats.total_learned, 1);
        assert_eq!(stats.unit_learned, 1);
        
        // Record a binary clause
        let binary = Clause::learned_with_lbd(vec![lit(1), lit(2)], 2);
        stats.record(&binary);
        assert_eq!(stats.total_learned, 2);
        assert_eq!(stats.binary_learned, 1);
        
        // Record a longer clause
        let longer = Clause::learned_with_lbd(vec![lit(1), lit(2), lit(3)], 3);
        stats.record(&longer);
        assert_eq!(stats.total_learned, 3);
        
        // Average LBD should be (1 + 2 + 3) / 3 = 2
        assert!((stats.avg_lbd - 2.0).abs() < 0.01);
    }

    #[test]
    fn test_formula_grows_correctly() {
        let mut formula = Formula::with_num_vars(10);
        let mut watches = WatchLists::new(10);
        
        // Add some original clauses
        for i in 1..=5 {
            formula.add_clause(make_clause(&[i, i + 1]));
        }
        crate::watch::init_watches(&mut watches, formula.clauses());
        
        let original_count = formula.num_clauses();
        
        // Add learned clauses
        for i in 1..=3 {
            let learned = make_learned_clause(&[-i, -(i + 5)]);
            add_learned_clause(&mut formula, &mut watches, learned);
        }
        
        assert_eq!(formula.num_clauses(), original_count + 3);
    }

    #[test]
    fn test_watches_after_multiple_learns() {
        let mut formula = Formula::with_num_vars(5);
        let mut watches = WatchLists::new(5);
        
        // Add learned clauses
        let c1 = add_learned_clause(&mut formula, &mut watches, 
            make_learned_clause(&[1, 2, 3]));
        let c2 = add_learned_clause(&mut formula, &mut watches,
            make_learned_clause(&[-1, 4, 5]));
        let c3 = add_learned_clause(&mut formula, &mut watches,
            make_learned_clause(&[1, -4]));
        
        // Check watches are correct
        assert!(watches.is_watching(lit(1), c1));
        assert!(watches.is_watching(lit(2), c1));
        
        assert!(watches.is_watching(lit(-1), c2));
        assert!(watches.is_watching(lit(4), c2));
        
        assert!(watches.is_watching(lit(1), c3));
        assert!(watches.is_watching(lit(-4), c3));
    }
}
