//! Conflict analysis using 1-UIP (First Unique Implication Point) scheme
//!
//! When a conflict occurs, we analyze the implication graph to learn
//! a new clause that prevents the same conflict in the future.

use crate::assignment::Assignments;
use crate::clause::{Clause, ClauseRef};
use crate::formula::Formula;
use crate::literal::{Literal, Variable};
use crate::trail::Trail;
use std::collections::HashSet;

/// Result of conflict analysis
#[derive(Debug, Clone)]
pub struct ConflictResult {
    /// The learned clause (asserting clause)
    pub learned_clause: Clause,
    /// Level to backtrack to
    pub backtrack_level: u32,
    /// LBD (Literal Block Distance) of the learned clause
    pub lbd: u32,
    /// Variables involved in the conflict (for VSIDS bumping)
    pub involved_vars: Vec<Variable>,
}

/// Analyze a conflict and produce a learned clause
///
/// Uses the 1-UIP (First Unique Implication Point) scheme:
/// 1. Start with the conflict clause
/// 2. Resolve with antecedents of literals from the current level
/// 3. Stop when exactly one literal remains from the current level
///
/// Returns None if conflict at level 0 (UNSAT)
pub fn analyze_conflict(
    formula: &Formula,
    assignments: &Assignments,
    trail: &Trail,
    conflict_clause: ClauseRef,
    current_level: u32,
) -> Option<ConflictResult> {
    // Conflict at level 0 means UNSAT
    if current_level == 0 {
        return None;
    }

    // Track seen variables (to avoid duplicates)
    let mut seen: HashSet<Variable> = HashSet::new();
    
    // Track variables involved in conflict (for VSIDS)
    let mut involved_vars: Vec<Variable> = Vec::new();
    
    // Literals for the learned clause
    let mut learned_lits: Vec<Literal> = Vec::new();
    
    // Count of literals from current level in the resolvent
    let mut current_level_count = 0;
    
    // Initialize with conflict clause literals
    for &lit in formula.clause(conflict_clause).literals() {
        let var = lit.variable();
        if !seen.contains(&var) {
            seen.insert(var);
            involved_vars.push(var);
            
            let level = assignments.level(var);
            if level == current_level {
                current_level_count += 1;
            } else if level > 0 {
                // Add to learned clause (not from current level, not level 0)
                learned_lits.push(lit.negate());
            }
        }
    }
    
    // Walk backward through the trail, resolving until 1-UIP
    let trail_lits: Vec<Literal> = trail.iter().cloned().collect();
    let mut trail_idx = trail_lits.len();
    let mut asserting_lit: Option<Literal> = None;
    
    while current_level_count > 1 {
        // Find the next literal from current level (walking backward)
        trail_idx -= 1;
        let lit = trail_lits[trail_idx];
        let var = lit.variable();
        
        if !seen.contains(&var) {
            continue;
        }
        
        let level = assignments.level(var);
        if level != current_level {
            continue;
        }
        
        // This literal is from current level and was seen
        current_level_count -= 1;
        
        // Get its antecedent and resolve
        if let Some(antecedent) = assignments.antecedent(var) {
            for &ante_lit in formula.clause(antecedent).literals() {
                let ante_var = ante_lit.variable();
                if ante_var == var {
                    continue; // Skip the resolved variable
                }
                
                if !seen.contains(&ante_var) {
                    seen.insert(ante_var);
                    involved_vars.push(ante_var);
                    
                    let ante_level = assignments.level(ante_var);
                    if ante_level == current_level {
                        current_level_count += 1;
                    } else if ante_level > 0 {
                        learned_lits.push(ante_lit.negate());
                    }
                }
            }
        }
        
        // If this was the last one, it's the asserting literal
        if current_level_count == 1 {
            asserting_lit = Some(lit.negate());
        }
    }
    
    // If we still have exactly one literal from current level, find it
    if asserting_lit.is_none() {
        // Walk backward to find it
        for i in (0..trail_idx).rev() {
            let lit = trail_lits[i];
            let var = lit.variable();
            if seen.contains(&var) && assignments.level(var) == current_level {
                asserting_lit = Some(lit.negate());
                break;
            }
        }
    }
    
    // The asserting literal should be first in the learned clause
    let asserting = asserting_lit?;
    let mut final_lits = vec![asserting];
    final_lits.extend(learned_lits);
    
    // Compute backtrack level (second highest level in learned clause)
    let backtrack_level = compute_backtrack_level(&final_lits, assignments);
    
    // Compute LBD
    let lbd = compute_lbd(&final_lits, assignments);
    
    // Create learned clause
    let learned_clause = Clause::learned_with_lbd(final_lits, lbd);
    
    Some(ConflictResult {
        learned_clause,
        backtrack_level,
        lbd,
        involved_vars,
    })
}

/// Compute the backtrack level for a learned clause
/// This is the second-highest decision level among literals in the clause
/// (the asserting literal is at the current level, so we want the next highest)
fn compute_backtrack_level(lits: &[Literal], assignments: &Assignments) -> u32 {
    if lits.len() <= 1 {
        return 0;
    }
    
    let mut max_level = 0;
    let mut second_max = 0;
    
    for lit in lits {
        let level = assignments.level(lit.variable());
        if level > max_level {
            second_max = max_level;
            max_level = level;
        } else if level > second_max && level < max_level {
            second_max = level;
        }
    }
    
    second_max
}

/// Compute the LBD (Literal Block Distance) of a clause
/// LBD is the number of distinct decision levels among literals
fn compute_lbd(lits: &[Literal], assignments: &Assignments) -> u32 {
    let levels: HashSet<u32> = lits
        .iter()
        .map(|lit| assignments.level(lit.variable()))
        .collect();
    levels.len() as u32
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::Formula;

    fn lit(i: i32) -> Literal {
        Literal::from_dimacs(i)
    }

    fn make_clause(dimacs: &[i32]) -> Clause {
        Clause::new(dimacs.iter().map(|&i| lit(i)).collect())
    }

    #[test]
    fn test_compute_lbd() {
        let mut assignments = Assignments::new(5);
        
        // Assign variables at different levels
        assignments.assign(Variable::new(1), true, 1, None);
        assignments.assign(Variable::new(2), true, 2, None);
        assignments.assign(Variable::new(3), true, 2, None);
        assignments.assign(Variable::new(4), true, 3, None);
        
        // Clause with literals from levels 1, 2, 3
        let lits = vec![lit(-1), lit(-2), lit(-4)];
        let lbd = compute_lbd(&lits, &assignments);
        assert_eq!(lbd, 3);
        
        // Clause with literals from same level
        let lits = vec![lit(-2), lit(-3)];
        let lbd = compute_lbd(&lits, &assignments);
        assert_eq!(lbd, 1);
    }

    #[test]
    fn test_compute_backtrack_level() {
        let mut assignments = Assignments::new(5);
        
        assignments.assign(Variable::new(1), true, 1, None);
        assignments.assign(Variable::new(2), true, 2, None);
        assignments.assign(Variable::new(3), true, 3, None);
        assignments.assign(Variable::new(4), true, 4, None);
        
        // Learned clause: asserting lit at level 4, others at 1, 2, 3
        let lits = vec![lit(-4), lit(-1), lit(-2), lit(-3)];
        let level = compute_backtrack_level(&lits, &assignments);
        assert_eq!(level, 3); // Second highest after 4
        
        // Unit learned clause
        let lits = vec![lit(-4)];
        let level = compute_backtrack_level(&lits, &assignments);
        assert_eq!(level, 0);
        
        // Binary learned clause
        let lits = vec![lit(-4), lit(-2)];
        let level = compute_backtrack_level(&lits, &assignments);
        assert_eq!(level, 2);
    }

    #[test]
    fn test_analyze_conflict_level_zero() {
        let formula = Formula::new();
        let assignments = Assignments::new(5);
        let trail = Trail::new();
        
        // Conflict at level 0 returns None (UNSAT)
        let result = analyze_conflict(&formula, &assignments, &trail, 0, 0);
        assert!(result.is_none());
    }

    #[test]
    fn test_analyze_simple_conflict() {
        // Set up a simple conflict scenario:
        // Clauses: (1 v 2), (-1 v 3), (-2 v -3)
        // Decide x1 = true at level 1
        // Propagate: x3 = true (from -1 v 3)
        // Decide x2 = true at level 2
        // Conflict in (-2 v -3): both -2 and -3 are false
        
        let mut formula = Formula::with_num_vars(3);
        formula.add_clause(make_clause(&[1, 2]));      // clause 0
        formula.add_clause(make_clause(&[-1, 3]));     // clause 1
        formula.add_clause(make_clause(&[-2, -3]));    // clause 2 (conflict)
        
        let mut assignments = Assignments::new(3);
        let mut trail = Trail::new();
        
        // Level 1: decide x1 = true, propagate x3 = true
        trail.new_level();
        assignments.assign(Variable::new(1), true, 1, None);
        trail.push(lit(1));
        assignments.assign(Variable::new(3), true, 1, Some(1)); // from clause 1
        trail.push(lit(3));
        
        // Level 2: decide x2 = true -> conflict in clause 2
        trail.new_level();
        assignments.assign(Variable::new(2), true, 2, None);
        trail.push(lit(2));
        
        let result = analyze_conflict(&formula, &assignments, &trail, 2, 2);
        assert!(result.is_some());
        
        let result = result.unwrap();
        // Should backtrack to level 1
        assert_eq!(result.backtrack_level, 1);
        // Learned clause should contain -2 (asserting) and something from level 1
        assert!(!result.learned_clause.is_empty());
    }

    #[test]
    fn test_involved_vars_for_vsids() {
        let mut formula = Formula::with_num_vars(3);
        formula.add_clause(make_clause(&[-1, 2]));     // clause 0
        formula.add_clause(make_clause(&[-2, 3]));     // clause 1  
        formula.add_clause(make_clause(&[-1, -3]));    // clause 2 (conflict)
        
        let mut assignments = Assignments::new(3);
        let mut trail = Trail::new();
        
        // Level 1: x1 = true -> x2 = true -> x3 = true -> conflict
        trail.new_level();
        assignments.assign(Variable::new(1), true, 1, None);
        trail.push(lit(1));
        assignments.assign(Variable::new(2), true, 1, Some(0));
        trail.push(lit(2));
        assignments.assign(Variable::new(3), true, 1, Some(1));
        trail.push(lit(3));
        
        let result = analyze_conflict(&formula, &assignments, &trail, 2, 1);
        assert!(result.is_some());
        
        let result = result.unwrap();
        // All variables should be involved
        assert!(!result.involved_vars.is_empty());
    }
}
