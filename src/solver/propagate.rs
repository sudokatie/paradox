//! Unit propagation via watched literals.
//!
//! The hot path of CDCL. When a literal becomes false, we check clauses
//! watching that literal and either:
//! 1. Find a new literal to watch
//! 2. Propagate the other watched literal (if it's the only unassigned one)
//! 3. Detect a conflict (if both watched literals are false)

use crate::assignment::{Assignments, Value};
use crate::clause::ClauseRef;
use crate::formula::Formula;
use crate::literal::Literal;
use crate::trail::Trail;
use crate::watch::{Watcher, WatchLists};

/// Result of propagation.
#[derive(Debug, Clone)]
pub enum PropagateResult {
    /// Propagation completed successfully.
    Ok,
    /// Conflict detected at the given clause.
    Conflict(ClauseRef),
}

/// Propagate a single literal assignment.
/// Returns a conflict clause if one is found.
pub fn propagate_literal(
    lit: Literal,
    formula: &mut Formula,
    assignments: &mut Assignments,
    trail: &mut Trail,
    watches: &mut WatchLists,
    level: u32,
) -> PropagateResult {
    // When lit is assigned (true), we check clauses watching lit.
    // Those clauses have lit as a watched literal, and now lit is true,
    // so we need to find a new watch or propagate.
    //
    // Wait - actually when lit is assigned true, those clauses are satisfied.
    // We need to check clauses watching lit.negate() because those have
    // lit.negate() as a watched literal, and when lit is true, lit.negate() is false.
    //
    // Actually the semantics are: watches[l] = clauses to check when l becomes false.
    // When we propagate lit (assign lit to true), lit.negate() becomes false.
    // So we check watches[lit.negate()], which finds clauses that have lit.negate() as watched.
    //
    // But wait, if the clause has lit.negate() as a literal, and lit is true, then
    // lit.negate() is false. So we need to find a new watch.
    //
    // Hmm, let me reconsider. For clause (1, 2):
    // - It watches literals 1 and 2
    // - watches[1] and watches[2] contain this clause
    // - When 1 becomes false (i.e., x1 = False, lit = -1 is assigned), check watches[1]
    //
    // So when we propagate lit = -1 (assigning -1 to true, meaning x1 = False):
    // - We should check watches[1] because literal 1 becomes false
    // - false_lit = lit.negate() = -(-1) = 1
    //
    // That's correct! So we check watches[lit.negate()] = watches[1].
    let false_lit = lit.negate();
    
    // Collect watchers to process (take ownership to avoid borrow issues)
    let old_watchers = std::mem::take(watches.watches_mut(false_lit));
    let mut new_watchers = Vec::with_capacity(old_watchers.len());
    
    for watcher in old_watchers {
        let clause_idx = watcher.clause;
        let blocker = watcher.blocker;
        
        // Quick check: if blocker is true, clause is satisfied
        if assignments.is_satisfied(blocker) {
            new_watchers.push(watcher);
            continue;
        }
        
        // Need to examine the clause
        let clause = formula.clause_mut(clause_idx);
        let clause_len = clause.len();
        
        // Ensure the false literal is at position 0
        if clause[0] != false_lit {
            clause.swap(0, 1);
        }
        debug_assert_eq!(clause[0], false_lit);
        
        // Check if the other watched literal (position 1) is true
        let other_lit = clause[1];
        if assignments.is_satisfied(other_lit) {
            // Update blocker and keep watching
            new_watchers.push(Watcher::new(clause_idx, other_lit));
            continue;
        }
        
        // Try to find a new literal to watch (not at position 0 or 1)
        let mut found_replacement = false;
        for k in 2..clause_len {
            let candidate = clause[k];
            if !assignments.is_falsified(candidate) {
                // Found a replacement - swap it to position 0
                clause.swap(0, k);
                
                // Add to new literal's watch list
                watches.add_watch(candidate.negate(), clause_idx, other_lit);
                
                found_replacement = true;
                break;
            }
        }
        
        if found_replacement {
            // Watcher moved to different list, don't add to new_watchers
            continue;
        }
        
        // No replacement found - this is either a unit clause or conflict
        if assignments.is_falsified(other_lit) {
            // Both watched literals are false - conflict!
            // Restore remaining watchers before returning
            new_watchers.push(watcher);
            *watches.watches_mut(false_lit) = new_watchers;
            return PropagateResult::Conflict(clause_idx);
        }
        
        // other_lit must be unassigned - propagate it
        debug_assert!(!assignments.is_assigned(other_lit.variable()));
        
        // Assign the literal
        let var = other_lit.variable();
        let value = if other_lit.is_positive() {
            Value::True
        } else {
            Value::False
        };
        assignments.assign(var, value, level, Some(clause_idx));
        trail.push_propagation(other_lit);
        
        // Keep watching with updated blocker
        new_watchers.push(Watcher::new(clause_idx, other_lit));
    }
    
    // Put back the processed watchers
    *watches.watches_mut(false_lit) = new_watchers;
    
    PropagateResult::Ok
}

/// Propagate all pending assignments until fixpoint or conflict.
/// 
/// Starts from the given trail position and propagates all assignments.
pub fn propagate(
    formula: &mut Formula,
    assignments: &mut Assignments,
    trail: &mut Trail,
    watches: &mut WatchLists,
    level: u32,
    start_pos: usize,
) -> PropagateResult {
    let mut pos = start_pos;
    
    while pos < trail.len() {
        let lit = trail.get(pos).expect("trail position should be valid");
        pos += 1;
        
        match propagate_literal(lit, formula, assignments, trail, watches, level) {
            PropagateResult::Ok => {}
            conflict => return conflict,
        }
    }
    
    PropagateResult::Ok
}

/// Propagate initial unit clauses (at level 0).
pub fn propagate_units(
    formula: &mut Formula,
    assignments: &mut Assignments,
    trail: &mut Trail,
    watches: &mut WatchLists,
) -> PropagateResult {
    // Find all unit clauses and assign them
    let units: Vec<_> = formula.unit_clauses().collect();
    
    for (clause_idx, lit) in units {
        let var = lit.variable();
        
        // Skip if already assigned
        if assignments.is_assigned(var) {
            if assignments.is_falsified(lit) {
                // Unit clause is falsified - conflict
                return PropagateResult::Conflict(clause_idx);
            }
            // Already satisfied, skip
            continue;
        }
        
        // Assign at level 0
        let value = if lit.is_positive() {
            Value::True
        } else {
            Value::False
        };
        assignments.assign(var, value, 0, Some(clause_idx));
        trail.push_propagation(lit);
    }
    
    // Now propagate
    propagate(formula, assignments, trail, watches, 0, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clause::Clause;
    use crate::watch::init_watches;

    fn lit(v: i32) -> Literal {
        Literal::from_dimacs(v)
    }

    fn clause(lits: &[i32]) -> Clause {
        Clause::new(lits.iter().map(|&v| lit(v)).collect())
    }

    #[test]
    fn test_propagate_unit() {
        let mut f = Formula::new();
        f.add_clause(clause(&[1]));       // unit clause
        f.add_clause(clause(&[1, 2, 3])); // will become unit after -1 propagates
        
        let mut assignments = Assignments::new(f.num_vars());
        let mut trail = Trail::new();
        let mut watches = init_watches(&f);
        
        let result = propagate_units(&mut f, &mut assignments, &mut trail, &mut watches);
        assert!(matches!(result, PropagateResult::Ok));
        
        // Variable 1 should be true
        assert_eq!(assignments.value(lit(1).variable()), Value::True);
    }

    #[test]
    fn test_propagate_chain() {
        // (1) ∧ (¬1 ∨ 2) ∧ (¬2 ∨ 3)
        // Should propagate: 1=T, 2=T, 3=T
        let mut f = Formula::new();
        f.add_clause(clause(&[1]));
        f.add_clause(clause(&[-1, 2]));
        f.add_clause(clause(&[-2, 3]));
        
        let mut assignments = Assignments::new(f.num_vars());
        let mut trail = Trail::new();
        let mut watches = init_watches(&f);
        
        let result = propagate_units(&mut f, &mut assignments, &mut trail, &mut watches);
        assert!(matches!(result, PropagateResult::Ok));
        
        assert!(assignments.is_satisfied(lit(1)));
        assert!(assignments.is_satisfied(lit(2)));
        assert!(assignments.is_satisfied(lit(3)));
    }

    #[test]
    fn test_propagate_conflict() {
        // (1) ∧ (¬1)
        // Conflict at root level
        let mut f = Formula::new();
        f.add_clause(clause(&[1]));
        f.add_clause(clause(&[-1]));
        
        let mut assignments = Assignments::new(f.num_vars());
        let mut trail = Trail::new();
        let mut watches = init_watches(&f);
        
        let result = propagate_units(&mut f, &mut assignments, &mut trail, &mut watches);
        assert!(matches!(result, PropagateResult::Conflict(_)));
    }

    #[test]
    fn test_propagate_binary() {
        // (1 ∨ 2) - assign 1=F, should propagate 2=T
        let mut f = Formula::new();
        f.add_clause(clause(&[1, 2]));
        
        let mut assignments = Assignments::new(f.num_vars());
        let mut trail = Trail::new();
        let mut watches = init_watches(&f);
        
        // Assign 1=F at level 1
        trail.new_level();
        let var1 = lit(1).variable();
        assignments.assign(var1, Value::False, 1, None);
        trail.push_propagation(lit(-1));
        
        let result = propagate(&mut f, &mut assignments, &mut trail, &mut watches, 1, 0);
        assert!(matches!(result, PropagateResult::Ok));
        
        // Variable 2 should be true
        assert!(assignments.is_satisfied(lit(2)));
        assert_eq!(trail.len(), 2);
    }

    #[test]
    fn test_propagate_finds_new_watch() {
        // (1 ∨ 2 ∨ 3) - assign 1=F, should find new watch
        let mut f = Formula::new();
        f.add_clause(clause(&[1, 2, 3]));
        
        let mut assignments = Assignments::new(f.num_vars());
        let mut trail = Trail::new();
        let mut watches = init_watches(&f);
        
        // Assign 1=F
        trail.new_level();
        let var1 = lit(1).variable();
        assignments.assign(var1, Value::False, 1, None);
        trail.push_propagation(lit(-1));
        
        let result = propagate(&mut f, &mut assignments, &mut trail, &mut watches, 1, 0);
        assert!(matches!(result, PropagateResult::Ok));
        
        // 2 and 3 should still be unassigned
        assert!(!assignments.is_assigned(lit(2).variable()));
        assert!(!assignments.is_assigned(lit(3).variable()));
        assert_eq!(trail.len(), 1);
    }

    #[test]
    fn test_propagate_conflict_binary() {
        // (1 ∨ 2) - assign 1=F, 2=F, should conflict
        let mut f = Formula::new();
        f.add_clause(clause(&[1, 2]));
        
        let mut assignments = Assignments::new(f.num_vars());
        let mut trail = Trail::new();
        let mut watches = init_watches(&f);
        
        trail.new_level();
        assignments.assign(lit(1).variable(), Value::False, 1, None);
        trail.push_propagation(lit(-1));
        assignments.assign(lit(2).variable(), Value::False, 1, None);
        trail.push_propagation(lit(-2));
        
        let result = propagate(&mut f, &mut assignments, &mut trail, &mut watches, 1, 0);
        assert!(matches!(result, PropagateResult::Conflict(_)));
    }

    #[test]
    fn test_satisfied_blocker_skip() {
        // (1 ∨ 2 ∨ 3) - assign 2=T, then 1=F, should not propagate
        let mut f = Formula::new();
        f.add_clause(clause(&[1, 2, 3]));
        
        let mut assignments = Assignments::new(f.num_vars());
        let mut trail = Trail::new();
        let mut watches = init_watches(&f);
        
        trail.new_level();
        // First assign 2=T (satisfies clause)
        assignments.assign(lit(2).variable(), Value::True, 1, None);
        trail.push_propagation(lit(2));
        
        // Then assign 1=F
        assignments.assign(lit(1).variable(), Value::False, 1, None);
        trail.push_propagation(lit(-1));
        
        let result = propagate(&mut f, &mut assignments, &mut trail, &mut watches, 1, 0);
        assert!(matches!(result, PropagateResult::Ok));
        
        // 3 should still be unassigned (clause already satisfied)
        assert!(!assignments.is_assigned(lit(3).variable()));
    }

    #[test]
    fn test_antecedent_tracking() {
        // (1) ∧ (¬1 ∨ 2) - propagate and check antecedents
        let mut f = Formula::new();
        f.add_clause(clause(&[1]));
        f.add_clause(clause(&[-1, 2]));
        
        let mut assignments = Assignments::new(f.num_vars());
        let mut trail = Trail::new();
        let mut watches = init_watches(&f);
        
        let result = propagate_units(&mut f, &mut assignments, &mut trail, &mut watches);
        assert!(matches!(result, PropagateResult::Ok));
        
        // Check antecedents
        assert_eq!(assignments.antecedent(lit(1).variable()), Some(0)); // clause 0
        assert_eq!(assignments.antecedent(lit(2).variable()), Some(1)); // clause 1
    }

    #[test]
    fn test_long_propagation_chain() {
        // (1) ∧ (¬1 ∨ 2) ∧ (¬2 ∨ 3) ∧ (¬3 ∨ 4) ∧ (¬4 ∨ 5)
        let mut f = Formula::new();
        f.add_clause(clause(&[1]));
        f.add_clause(clause(&[-1, 2]));
        f.add_clause(clause(&[-2, 3]));
        f.add_clause(clause(&[-3, 4]));
        f.add_clause(clause(&[-4, 5]));
        
        let mut assignments = Assignments::new(f.num_vars());
        let mut trail = Trail::new();
        let mut watches = init_watches(&f);
        
        let result = propagate_units(&mut f, &mut assignments, &mut trail, &mut watches);
        assert!(matches!(result, PropagateResult::Ok));
        
        // All should be satisfied
        for i in 1..=5 {
            assert!(assignments.is_satisfied(lit(i)));
        }
        assert_eq!(trail.len(), 5);
    }
}
