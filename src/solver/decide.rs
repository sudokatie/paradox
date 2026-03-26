//! VSIDS (Variable State Independent Decaying Sum) decision heuristic.
//!
//! The key insight: variables involved in recent conflicts are likely to be
//! involved in future conflicts. VSIDS maintains an activity score for each
//! variable, bumping scores on conflict involvement and decaying periodically.

use crate::literal::{Literal, Variable};
use std::collections::BinaryHeap;

/// Activity-based variable ordering for decisions.
#[derive(Debug)]
pub struct Vsids {
    /// Activity score for each variable (indexed by variable 0-based).
    activities: Vec<f64>,
    /// Heap for efficient max-activity lookup.
    heap: BinaryHeap<VarActivity>,
    /// Current activity increment (increases with decay).
    increment: f64,
    /// Decay factor (multiply increment by 1/decay each conflict).
    decay: f64,
    /// Rescale threshold to prevent overflow.
    rescale_threshold: f64,
}

/// Wrapper for heap ordering by activity.
#[derive(Debug, Clone, Copy)]
struct VarActivity {
    var: Variable,
    activity: f64,
}

impl PartialEq for VarActivity {
    fn eq(&self, other: &Self) -> bool {
        self.activity == other.activity
    }
}

impl Eq for VarActivity {}

impl PartialOrd for VarActivity {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for VarActivity {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Higher activity = higher priority
        self.activity.partial_cmp(&other.activity).unwrap_or(std::cmp::Ordering::Equal)
    }
}

impl Vsids {
    /// Create VSIDS for the given number of variables.
    pub fn new(num_vars: usize) -> Self {
        let activities = vec![0.0; num_vars];
        let mut heap = BinaryHeap::with_capacity(num_vars);
        
        // Initially all variables have activity 0
        for i in 0..num_vars {
            let var = Variable::from_index(i);
            heap.push(VarActivity { var, activity: 0.0 });
        }
        
        Vsids {
            activities,
            heap,
            increment: 1.0,
            decay: 0.95,
            rescale_threshold: 1e100,
        }
    }

    /// Get activity for a variable.
    pub fn activity(&self, var: Variable) -> f64 {
        let idx = var.to_index();
        self.activities.get(idx).copied().unwrap_or(0.0)
    }

    /// Bump activity for a variable (called when involved in conflict).
    pub fn bump(&mut self, var: Variable) {
        let idx = var.to_index();
        if idx >= self.activities.len() {
            return;
        }
        
        self.activities[idx] += self.increment;
        
        // Check for rescale
        if self.activities[idx] > self.rescale_threshold {
            self.rescale();
        }
        
        // Re-add to heap with new activity
        self.heap.push(VarActivity {
            var,
            activity: self.activities[idx],
        });
    }

    /// Bump activity for a literal (convenience wrapper).
    pub fn bump_lit(&mut self, lit: Literal) {
        self.bump(lit.variable());
    }

    /// Decay all activities (called after each conflict).
    /// Instead of multiplying all activities by decay, we divide the increment.
    pub fn decay(&mut self) {
        self.increment /= self.decay;
        
        // Check if increment is too large
        if self.increment > self.rescale_threshold {
            self.rescale();
        }
    }

    /// Rescale all activities to prevent overflow.
    fn rescale(&mut self) {
        let scale = 1e-100;
        for act in &mut self.activities {
            *act *= scale;
        }
        self.increment *= scale;
        
        // Rebuild heap with new activities
        self.rebuild_heap();
    }

    /// Rebuild the heap from current activities.
    fn rebuild_heap(&mut self) {
        self.heap.clear();
        for (i, &act) in self.activities.iter().enumerate() {
            let var = Variable::from_index(i);
            self.heap.push(VarActivity { var, activity: act });
        }
    }

    /// Pick the highest-activity unassigned variable.
    /// Returns None if all variables are assigned.
    pub fn pick_var<F>(&mut self, is_assigned: F) -> Option<Variable>
    where
        F: Fn(Variable) -> bool,
    {
        // Keep popping until we find an unassigned variable with correct activity
        while let Some(va) = self.heap.pop() {
            let var = va.var;
            let idx = var.to_index();
            
            // Skip if variable index is out of bounds
            if idx >= self.activities.len() {
                continue;
            }
            
            // Check if this entry is stale (activity doesn't match)
            if (va.activity - self.activities[idx]).abs() > 1e-10 {
                continue;
            }
            
            // Check if variable is already assigned
            if is_assigned(var) {
                continue;
            }
            
            // Re-add to heap for future use
            self.heap.push(va);
            return Some(var);
        }
        
        None
    }

    /// Pick a decision literal (variable + polarity).
    /// Uses phase saving or defaults to positive.
    pub fn pick_literal<F>(&mut self, is_assigned: F, phases: Option<&[bool]>) -> Option<Literal>
    where
        F: Fn(Variable) -> bool,
    {
        self.pick_var(is_assigned).map(|var| {
            let positive = phases
                .and_then(|p| p.get(var.to_index()).copied())
                .unwrap_or(true);
            if positive {
                Literal::positive(var)
            } else {
                Literal::negative(var)
            }
        })
    }

    /// Set decay factor.
    pub fn set_decay(&mut self, decay: f64) {
        self.decay = decay.clamp(0.5, 0.999);
    }

    /// Initialize activities from clause occurrences (optional).
    pub fn init_from_formula(&mut self, clauses: &[Vec<Literal>]) {
        for clause in clauses {
            for lit in clause {
                let idx = lit.variable().to_index();
                if idx < self.activities.len() {
                    self.activities[idx] += 1.0;
                }
            }
        }
        self.rebuild_heap();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(i: usize) -> Variable {
        Variable::from_index(i)
    }

    #[test]
    fn test_new_vsids() {
        let vsids = Vsids::new(5);
        for i in 0..5 {
            assert_eq!(vsids.activity(var(i)), 0.0);
        }
    }

    #[test]
    fn test_bump_increases_activity() {
        let mut vsids = Vsids::new(5);
        vsids.bump(var(2));
        assert!(vsids.activity(var(2)) > 0.0);
        assert_eq!(vsids.activity(var(0)), 0.0);
    }

    #[test]
    fn test_multiple_bumps() {
        let mut vsids = Vsids::new(5);
        vsids.bump(var(1));
        vsids.bump(var(1));
        vsids.bump(var(1));
        assert!(vsids.activity(var(1)) > vsids.activity(var(0)));
    }

    #[test]
    fn test_decay_increases_increment() {
        let mut vsids = Vsids::new(5);
        let old_inc = vsids.increment;
        vsids.decay();
        assert!(vsids.increment > old_inc);
    }

    #[test]
    fn test_pick_highest_activity() {
        let mut vsids = Vsids::new(5);
        vsids.bump(var(3));
        vsids.bump(var(3));
        vsids.bump(var(1));
        
        let picked = vsids.pick_var(|_| false);
        assert_eq!(picked, Some(var(3)));
    }

    #[test]
    fn test_pick_skips_assigned() {
        let mut vsids = Vsids::new(5);
        vsids.bump(var(3));
        vsids.bump(var(3));
        vsids.bump(var(1));
        
        let assigned = [false, false, false, true, false]; // var 3 assigned
        let picked = vsids.pick_var(|v| assigned[v.to_index()]);
        assert_eq!(picked, Some(var(1)));
    }

    #[test]
    fn test_pick_literal_default_positive() {
        let mut vsids = Vsids::new(3);
        vsids.bump(var(1));
        
        let lit = vsids.pick_literal(|_| false, None).unwrap();
        assert!(lit.is_positive());
        assert_eq!(lit.variable(), var(1));
    }

    #[test]
    fn test_pick_literal_with_phase() {
        let mut vsids = Vsids::new(3);
        vsids.bump(var(1));
        
        let phases = [true, false, true]; // var 1 prefers negative
        let lit = vsids.pick_literal(|_| false, Some(&phases)).unwrap();
        assert!(!lit.is_positive());
        assert_eq!(lit.variable(), var(1));
    }

    #[test]
    fn test_all_assigned_returns_none() {
        let mut vsids = Vsids::new(3);
        let picked = vsids.pick_var(|_| true);
        assert_eq!(picked, None);
    }

    #[test]
    fn test_rescale_preserves_ordering() {
        let mut vsids = Vsids::new(3);
        
        // Bump var 0 a lot
        for _ in 0..1000 {
            vsids.bump(var(0));
        }
        // Bump var 1 a little
        for _ in 0..10 {
            vsids.bump(var(1));
        }
        
        // Force rescale
        vsids.rescale();
        
        // Ordering should be preserved
        assert!(vsids.activity(var(0)) > vsids.activity(var(1)));
        assert!(vsids.activity(var(1)) > vsids.activity(var(2)));
    }

    #[test]
    fn test_init_from_formula() {
        let mut vsids = Vsids::new(4);
        
        let clauses = vec![
            vec![Literal::from_dimacs(1), Literal::from_dimacs(2)],
            vec![Literal::from_dimacs(1), Literal::from_dimacs(3)],
            vec![Literal::from_dimacs(2), Literal::from_dimacs(3)],
        ];
        
        vsids.init_from_formula(&clauses);
        
        // var 0 (1) appears twice
        // var 1 (2) appears twice
        // var 2 (3) appears twice
        // var 3 (4) appears zero times
        assert_eq!(vsids.activity(var(0)), 2.0);
        assert_eq!(vsids.activity(var(1)), 2.0);
        assert_eq!(vsids.activity(var(2)), 2.0);
        assert_eq!(vsids.activity(var(3)), 0.0);
    }
}
