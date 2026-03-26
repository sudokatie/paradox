//! Conflict analysis for CDCL.
//!
//! Implements 1-UIP (First Unique Implication Point) learning scheme.
//! When a conflict is detected, we resolve the conflict clause with
//! antecedents until exactly one literal from the current decision level
//! remains. This learned clause is asserting and causes backtracking.

use crate::assignment::Assignments;
use crate::clause::ClauseRef;
use crate::formula::Formula;
use crate::literal::Literal;
use crate::trail::Trail;

/// Result of conflict analysis.
#[derive(Debug, Clone)]
pub struct ConflictResult {
    /// The learned clause (asserting literal first).
    pub learned_clause: Vec<Literal>,
    /// Level to backtrack to.
    pub backtrack_level: u32,
    /// LBD (Literal Block Distance) of learned clause.
    pub lbd: u32,
    /// Variables involved in the conflict (for VSIDS bumping).
    pub involved_vars: Vec<usize>,
}

/// Analyze a conflict and produce a learned clause.
///
/// Uses resolution starting from the conflict clause, resolving with
/// antecedents until we reach the 1-UIP (exactly one literal from
/// the current decision level in the resolvent).
pub fn analyze_conflict(
    conflict_clause: ClauseRef,
    formula: &Formula,
    assignments: &Assignments,
    trail: &Trail,
    current_level: u32,
) -> ConflictResult {
    let mut seen = vec![false; assignments.num_vars()];
    let mut learnt: Vec<Literal> = Vec::new();
    let mut involved_vars: Vec<usize> = Vec::new();
    let mut num_current_level = 0;
    
    // Start with conflict clause
    let conflict_lits: Vec<_> = formula.clause(conflict_clause).iter().collect();
    
    for lit in &conflict_lits {
        let var = lit.variable();
        let idx = var.to_index();
        if idx < seen.len() && !seen[idx] {
            seen[idx] = true;
            involved_vars.push(idx);
            
            if assignments.level(var) == current_level {
                num_current_level += 1;
            } else if assignments.level(var) > 0 {
                // Literal from earlier level - add to learned clause
                learnt.push(*lit);
            }
            // Level 0 literals are always true/false, skip
        }
    }
    
    // Resolve until 1-UIP: exactly one literal from current level
    let mut trail_idx = trail.len();
    
    while num_current_level > 1 {
        trail_idx -= 1;
        let Some(lit) = trail.get(trail_idx) else {
            break;
        };
        
        let var = lit.variable();
        let idx = var.to_index();
        if idx >= seen.len() || !seen[idx] {
            continue;
        }
        
        // This literal is from current level and was seen
        // Resolve with its antecedent (if any)
        if let Some(antecedent) = assignments.antecedent(var) {
            let ante_clause = formula.clause(antecedent);
            for ante_lit in ante_clause.iter() {
                let ante_var = ante_lit.variable();
                let ante_idx = ante_var.to_index();
                if ante_idx < seen.len() && !seen[ante_idx] {
                    seen[ante_idx] = true;
                    involved_vars.push(ante_idx);
                    
                    if assignments.level(ante_var) == current_level {
                        num_current_level += 1;
                    } else if assignments.level(ante_var) > 0 {
                        learnt.push(ante_lit);
                    }
                }
            }
        }
        
        num_current_level -= 1;
    }
    
    // Find the 1-UIP literal (only remaining current-level literal)
    let mut uip_lit = None;
    for idx in (0..trail_idx).rev() {
        if let Some(lit) = trail.get(idx) {
            let var = lit.variable();
            let var_idx = var.to_index();
            if var_idx < seen.len() && seen[var_idx] && assignments.level(var) == current_level {
                // The UIP literal should be negated in the learned clause
                uip_lit = Some(lit.negate());
                break;
            }
        }
    }
    // Also check the remaining part of trail
    if uip_lit.is_none() {
        for idx in trail_idx..trail.len() {
            if let Some(lit) = trail.get(idx) {
                let var = lit.variable();
                let var_idx = var.to_index();
                if var_idx < seen.len() && seen[var_idx] && assignments.level(var) == current_level {
                    uip_lit = Some(lit.negate());
                    break;
                }
            }
        }
    }
    
    if let Some(uip) = uip_lit {
        learnt.insert(0, uip);
    }
    
    // Compute backtrack level (second-highest level in learned clause)
    let backtrack_level = if learnt.len() <= 1 {
        0
    } else {
        learnt[1..]
            .iter()
            .map(|lit| assignments.level(lit.variable()))
            .max()
            .unwrap_or(0)
    };
    
    // Compute LBD (number of distinct decision levels)
    let lbd = compute_lbd(&learnt, assignments);
    
    ConflictResult {
        learned_clause: learnt,
        backtrack_level,
        lbd,
        involved_vars,
    }
}

/// Compute LBD (Literal Block Distance) for a clause.
/// LBD = number of distinct decision levels among literals.
pub fn compute_lbd(clause: &[Literal], assignments: &Assignments) -> u32 {
    let mut levels_seen = vec![false; assignments.num_vars() + 1];
    let mut count = 0;
    
    for lit in clause {
        let level = assignments.level(lit.variable()) as usize;
        if level < levels_seen.len() && !levels_seen[level] {
            levels_seen[level] = true;
            count += 1;
        }
    }
    
    count
}

/// Minimize learned clause by removing redundant literals.
/// A literal is redundant if it's implied by other literals in the clause.
pub fn minimize_clause(
    clause: &mut Vec<Literal>,
    formula: &Formula,
    assignments: &Assignments,
) {
    if clause.len() <= 2 {
        return;
    }
    
    let mut dominated = vec![false; clause.len()];
    
    for (i, lit) in clause.iter().enumerate().skip(1) {
        // Skip the asserting literal (position 0)
        let var = lit.variable();
        if let Some(antecedent) = assignments.antecedent(var) {
            let ante_clause = formula.clause(antecedent);
            let all_in_clause = ante_clause
                .iter()
                .filter(|ante_lit| ante_lit.variable() != var)
                .all(|ante_lit| {
                    clause.iter().any(|c_lit| {
                        c_lit.variable() == ante_lit.variable()
                    })
                });
            
            if all_in_clause {
                dominated[i] = true;
            }
        }
    }
    
    // Remove dominated literals (in reverse to preserve indices)
    for i in (1..clause.len()).rev() {
        if dominated[i] {
            clause.swap_remove(i);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assignment::Value;
    use crate::clause::Clause;

    fn lit(v: i32) -> Literal {
        Literal::from_dimacs(v)
    }

    fn clause(lits: &[i32]) -> Clause {
        Clause::new(lits.iter().map(|&v| lit(v)).collect())
    }

    #[test]
    fn test_simple_conflict() {
        // Setup: (1 ∨ 2) with 1=F, 2=F at level 1
        // Conflict clause is clause 0
        let mut f = Formula::new();
        f.add_clause(clause(&[1, 2]));
        
        let mut assignments = Assignments::new(2);
        let mut trail = Trail::new();
        
        // Assign at level 1
        trail.new_level();
        assignments.assign(lit(1).variable(), Value::False, 1, None);
        trail.push_propagation(lit(-1));
        assignments.assign(lit(2).variable(), Value::False, 1, Some(0));
        trail.push_propagation(lit(-2));
        
        let result = analyze_conflict(0, &f, &assignments, &trail, 1);
        
        // Should learn something
        assert!(!result.learned_clause.is_empty());
        assert!(result.backtrack_level < 1);
    }

    #[test]
    fn test_conflict_with_antecedent() {
        // (1) ∧ (¬1 ∨ 2) ∧ (¬2 ∨ ¬3)
        // Decide 3=T at level 1, propagates: 1=T (clause 0), 2=T (clause 1)
        // Then ¬2 ∨ ¬3 conflicts
        let mut f = Formula::new();
        f.add_clause(clause(&[1]));      // 0
        f.add_clause(clause(&[-1, 2]));  // 1
        f.add_clause(clause(&[-2, -3])); // 2
        
        let mut assignments = Assignments::new(3);
        let mut trail = Trail::new();
        
        // Level 0: propagate unit clause
        assignments.assign(lit(1).variable(), Value::True, 0, Some(0));
        trail.push_propagation(lit(1));
        assignments.assign(lit(2).variable(), Value::True, 0, Some(1));
        trail.push_propagation(lit(2));
        
        // Level 1: decide 3=T
        trail.new_level();
        assignments.assign(lit(3).variable(), Value::True, 1, None);
        trail.push_propagation(lit(3));
        
        // Conflict at clause 2: -2 ∨ -3, both are false
        let result = analyze_conflict(2, &f, &assignments, &trail, 1);
        
        // Should backtrack to level 0
        assert_eq!(result.backtrack_level, 0);
    }

    #[test]
    fn test_lbd_computation() {
        let mut assignments = Assignments::new(5);
        
        // Assign at different levels
        assignments.assign(lit(1).variable(), Value::True, 1, None);
        assignments.assign(lit(2).variable(), Value::True, 1, None);
        assignments.assign(lit(3).variable(), Value::True, 2, None);
        assignments.assign(lit(4).variable(), Value::True, 3, None);
        
        let clause = vec![lit(1), lit(2), lit(3), lit(4)];
        let lbd = compute_lbd(&clause, &assignments);
        
        // 3 distinct levels: 1, 2, 3
        assert_eq!(lbd, 3);
    }

    #[test]
    fn test_involved_vars() {
        let mut f = Formula::new();
        f.add_clause(clause(&[1, 2, 3]));
        
        let mut assignments = Assignments::new(3);
        let mut trail = Trail::new();
        
        trail.new_level();
        assignments.assign(lit(1).variable(), Value::False, 1, None);
        trail.push_propagation(lit(-1));
        assignments.assign(lit(2).variable(), Value::False, 1, None);
        trail.push_propagation(lit(-2));
        assignments.assign(lit(3).variable(), Value::False, 1, Some(0));
        trail.push_propagation(lit(-3));
        
        let result = analyze_conflict(0, &f, &assignments, &trail, 1);
        
        // All 3 variables should be involved
        assert_eq!(result.involved_vars.len(), 3);
    }

    #[test]
    fn test_unit_learned_clause() {
        // Everything at level 1 with no antecedents - just one literal learned
        let mut f = Formula::new();
        f.add_clause(clause(&[1]));
        
        let mut assignments = Assignments::new(1);
        let mut trail = Trail::new();
        
        trail.new_level();
        assignments.assign(lit(1).variable(), Value::False, 1, None);
        trail.push_propagation(lit(-1));
        
        let result = analyze_conflict(0, &f, &assignments, &trail, 1);
        
        // Learned clause should contain negation of assigned literal
        assert!(result.learned_clause.contains(&lit(1)) || result.learned_clause.contains(&lit(-1)));
        assert_eq!(result.backtrack_level, 0);
    }
}
