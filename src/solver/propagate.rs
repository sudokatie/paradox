//! Unit propagation using two-watched-literal scheme

use crate::assignment::Assignments;
use crate::clause::ClauseRef;
use crate::formula::Formula;
use crate::trail::Trail;
use crate::watch::WatchLists;

/// Propagate unit clauses until fixpoint or conflict
/// 
/// Returns Some(clause_ref) if a conflict is found, None otherwise.
/// Uses the two-watched-literal scheme for efficient propagation.
pub fn propagate(
    formula: &Formula,
    assignments: &mut Assignments,
    trail: &mut Trail,
    watches: &mut WatchLists,
    propagation_count: &mut u64,
) -> Option<ClauseRef> {
    // Process all unprocessed assignments on the trail
    while let Some(&lit) = trail.peek_propagate() {
        // When lit is assigned true, ~lit is assigned false
        // We need to check clauses watching ~lit
        let false_lit = lit.negate();
        
        // Get watchers for the falsified literal
        // We need to iterate carefully since we may modify the list
        let mut i = 0;
        while i < watches.watches(false_lit).len() {
            let watcher = watches.watches(false_lit)[i];
            let clause_ref = watcher.clause;
            let blocker = watcher.blocker;
            
            // Quick check: if blocker is true, clause is satisfied
            if assignments.is_satisfied(blocker) {
                i += 1;
                continue;
            }
            
            // Need to examine the clause
            let clause = formula.clause(clause_ref);
            let lits = clause.literals();
            
            // Find the two watched literals
            let (_watch0, watch1) = if lits[0] == false_lit {
                (0, 1)
            } else {
                debug_assert!(lits.len() > 1 && lits[1] == false_lit);
                (1, 0)
            };
            
            let other_watch = lits[watch1];
            
            // Check if other watched literal is true
            if assignments.is_satisfied(other_watch) {
                // Clause satisfied, update blocker and continue
                watches.watches_mut(false_lit)[i].blocker = other_watch;
                i += 1;
                continue;
            }
            
            // Try to find a new literal to watch
            let mut found_new = false;
            for k in 2..lits.len() {
                let new_lit = lits[k];
                // Can watch if not false
                if !assignments.is_falsified(new_lit) {
                    // Found new literal to watch
                    // Remove from false_lit's watch list
                    watches.watches_mut(false_lit).swap_remove(i);
                    
                    // Add to new_lit's watch list
                    watches.add_watch(new_lit, clause_ref, other_watch);
                    
                    found_new = true;
                    // Don't increment i since we swapped
                    break;
                }
            }
            
            if found_new {
                continue;
            }
            
            // Couldn't find new watch - other_watch is the only non-false literal
            if assignments.is_satisfied(other_watch) {
                // Shouldn't happen, we checked above
                i += 1;
            } else if assignments.is_falsified(other_watch) {
                // Conflict! All literals are false
                trail.advance_propagate();
                return Some(clause_ref);
            } else {
                // Unit propagation: assign other_watch = true
                let var = other_watch.variable();
                let val = other_watch.is_positive();
                let level = trail.current_level();
                
                assignments.assign(var, val, level, Some(clause_ref));
                trail.push(other_watch);
                *propagation_count += 1;
                
                i += 1;
            }
        }
        
        trail.advance_propagate();
    }
    
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clause::Clause;
    use crate::literal::{Literal, Variable};
    use crate::watch::init_watches;

    fn make_clause(lits: &[(u32, bool)]) -> Clause {
        let literals: Vec<Literal> = lits
            .iter()
            .map(|&(var, pol)| {
                let v = Variable::new(var);
                if pol { Literal::positive(v) } else { Literal::negative(v) }
            })
            .collect();
        Clause::new(literals)
    }

    fn lit(var: u32, pol: bool) -> Literal {
        let v = Variable::new(var);
        if pol { Literal::positive(v) } else { Literal::negative(v) }
    }

    #[test]
    fn test_propagate_no_propagation() {
        use crate::formula::Formula;
        
        let mut formula = Formula::with_num_vars(3);
        formula.add_clause(make_clause(&[(1, true), (2, true), (3, true)]));
        
        let mut watches = WatchLists::new(3);
        init_watches(&mut watches, formula.clauses());
        
        let mut assignments = Assignments::new(3);
        let mut trail = Trail::new();
        let mut count = 0;
        
        // No assignments, nothing to propagate
        let result = propagate(&formula, &mut assignments, &mut trail, &mut watches, &mut count);
        assert!(result.is_none());
        assert_eq!(count, 0);
    }

    #[test]
    fn test_propagate_unit_clause() {
        use crate::formula::Formula;
        
        let mut formula = Formula::with_num_vars(3);
        // (1 v 2 v 3) and (-1) and (-2)
        formula.add_clause(make_clause(&[(1, true), (2, true), (3, true)]));
        formula.add_clause(make_clause(&[(1, false)]));
        formula.add_clause(make_clause(&[(2, false)]));
        
        let mut watches = WatchLists::new(3);
        init_watches(&mut watches, formula.clauses());
        
        let mut assignments = Assignments::new(3);
        let mut trail = Trail::new();
        let mut count = 0;
        
        // Assign x1 = false at level 0 (from unit clause)
        assignments.assign(Variable::new(1), false, 0, Some(1));
        trail.push(lit(1, false));
        
        // Propagate
        let result = propagate(&formula, &mut assignments, &mut trail, &mut watches, &mut count);
        assert!(result.is_none());
    }

    #[test]
    fn test_propagate_chain() {
        use crate::formula::Formula;
        
        let mut formula = Formula::with_num_vars(3);
        // (-1 v 2) and (-2 v 3)
        // If x1 = true, then x2 = true, then x3 = true
        formula.add_clause(make_clause(&[(1, false), (2, true)]));
        formula.add_clause(make_clause(&[(2, false), (3, true)]));
        
        let mut watches = WatchLists::new(3);
        init_watches(&mut watches, formula.clauses());
        
        let mut assignments = Assignments::new(3);
        let mut trail = Trail::new();
        let mut count = 0;
        
        // Decide x1 = true
        trail.new_level();
        assignments.assign(Variable::new(1), true, 1, None);
        trail.push(lit(1, true));
        
        // Propagate
        let result = propagate(&formula, &mut assignments, &mut trail, &mut watches, &mut count);
        assert!(result.is_none());
        
        // x2 and x3 should be assigned
        assert_eq!(assignments.value(Variable::new(2)), crate::assignment::Value::True);
        assert_eq!(assignments.value(Variable::new(3)), crate::assignment::Value::True);
        assert_eq!(count, 2);
    }

    #[test]
    fn test_propagate_conflict() {
        use crate::formula::Formula;
        
        // Test conflict detection with binary clauses
        // (-1 v 2) and (-1 v -2) and (-2 v 3) and (-2 v -3)
        // If x1 = true: propagate x2 = true from clause 0
        // Then x2 = true makes clause 1 falsified (needs -2 but 2 is true)
        let mut formula = Formula::with_num_vars(3);
        formula.add_clause(make_clause(&[(1, false), (2, true)]));   // -1 v 2
        formula.add_clause(make_clause(&[(1, false), (2, false)])); // -1 v -2
        
        let mut watches = WatchLists::new(3);
        init_watches(&mut watches, formula.clauses());
        
        let mut assignments = Assignments::new(3);
        let mut trail = Trail::new();
        let mut count = 0;
        
        // Decide x1 = true
        trail.new_level();
        assignments.assign(Variable::new(1), true, 1, None);
        trail.push(lit(1, true));
        
        // Propagate - x1=true makes -1 false in both clauses
        // Clause 0: -1 false, so x2 must be true
        // Clause 1: -1 false and x2 true means -2 false -> conflict!
        let result = propagate(&formula, &mut assignments, &mut trail, &mut watches, &mut count);
        assert!(result.is_some(), "Expected conflict but got None");
    }

    #[test]
    fn test_propagate_multiple_watches() {
        use crate::formula::Formula;
        
        let mut formula = Formula::with_num_vars(4);
        // (-1 v 2 v 3 v 4)
        formula.add_clause(make_clause(&[(1, false), (2, true), (3, true), (4, true)]));
        
        let mut watches = WatchLists::new(4);
        init_watches(&mut watches, formula.clauses());
        
        let mut assignments = Assignments::new(4);
        let mut trail = Trail::new();
        let mut count = 0;
        
        // Assign x1 = true (makes -1 false)
        trail.new_level();
        assignments.assign(Variable::new(1), true, 1, None);
        trail.push(lit(1, true));
        
        // Propagate - should find new watch, no propagation yet
        let result = propagate(&formula, &mut assignments, &mut trail, &mut watches, &mut count);
        assert!(result.is_none());
        assert_eq!(count, 0); // No unit propagation yet
    }

    #[test]
    fn test_propagate_blocker_optimization() {
        use crate::formula::Formula;
        
        let mut formula = Formula::with_num_vars(3);
        // (1 v 2 v 3) - initially watches 1 and 2
        formula.add_clause(make_clause(&[(1, true), (2, true), (3, true)]));
        
        let mut watches = WatchLists::new(3);
        init_watches(&mut watches, formula.clauses());
        
        let mut assignments = Assignments::new(3);
        let mut trail = Trail::new();
        let mut count = 0;
        
        // Assign x3 = true (satisfies clause via blocker check)
        trail.new_level();
        assignments.assign(Variable::new(3), true, 1, None);
        trail.push(lit(3, true));
        
        // Propagate - nothing to do
        let result = propagate(&formula, &mut assignments, &mut trail, &mut watches, &mut count);
        assert!(result.is_none());
        
        // Now make x1 false - should skip due to satisfied clause
        assignments.assign(Variable::new(1), false, 1, None);
        trail.push(lit(1, false));
        
        let result = propagate(&formula, &mut assignments, &mut trail, &mut watches, &mut count);
        assert!(result.is_none());
    }
}
