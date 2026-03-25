//! VSIDS (Variable State Independent Decaying Sum) decision heuristic
//!
//! Each variable has an activity score that is bumped when involved in conflicts.
//! Scores decay over time. We pick the unassigned variable with highest activity.

use crate::assignment::Assignments;
use crate::literal::Variable;
use std::collections::BinaryHeap;

/// VSIDS decision heuristic
#[derive(Debug)]
pub struct Vsids {
    /// Activity score for each variable (indexed by var.array_index())
    activities: Vec<f64>,
    /// Increment to add when bumping activity
    increment: f64,
    /// Decay factor (multiply increment by 1/decay after each conflict)
    decay_factor: f64,
    /// Max-heap of (activity, variable) pairs
    heap: BinaryHeap<ActivityEntry>,
    /// Track which variables are in the heap
    in_heap: Vec<bool>,
}

/// Entry in the priority heap
#[derive(Debug, Clone)]
struct ActivityEntry {
    activity: f64,
    var: Variable,
}

impl PartialEq for ActivityEntry {
    fn eq(&self, other: &Self) -> bool {
        self.var == other.var
    }
}

impl Eq for ActivityEntry {}

impl PartialOrd for ActivityEntry {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ActivityEntry {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Higher activity = higher priority
        // Use total_cmp for stable f64 comparison
        self.activity.total_cmp(&other.activity)
    }
}

impl Vsids {
    /// Create a new VSIDS heuristic for the given number of variables
    pub fn new(num_vars: u32) -> Self {
        let mut heap = BinaryHeap::new();
        let mut in_heap = vec![false; num_vars as usize];
        
        // Initialize all variables in heap with zero activity
        for i in 1..=num_vars {
            let var = Variable::new(i);
            heap.push(ActivityEntry { activity: 0.0, var });
            in_heap[var.array_index()] = true;
        }
        
        Vsids {
            activities: vec![0.0; num_vars as usize],
            increment: 1.0,
            decay_factor: 0.95,
            heap,
            in_heap,
        }
    }

    /// Get the activity of a variable
    pub fn activity(&self, var: Variable) -> f64 {
        self.activities[var.array_index()]
    }

    /// Bump the activity of a variable (call when involved in conflict)
    pub fn bump(&mut self, var: Variable) {
        let idx = var.array_index();
        self.activities[idx] += self.increment;
        
        // Rescale if activities get too large (prevents overflow)
        if self.activities[idx] > 1e100 {
            self.rescale();
        }
        
        // Re-insert into heap with updated activity
        if self.in_heap[idx] {
            self.heap.push(ActivityEntry {
                activity: self.activities[idx],
                var,
            });
        }
    }

    /// Bump multiple variables at once
    pub fn bump_all(&mut self, vars: &[Variable]) {
        for &var in vars {
            self.bump(var);
        }
    }

    /// Decay all activities (call after each conflict)
    pub fn decay(&mut self) {
        // Instead of decaying all activities, we increase the increment
        // This is equivalent but more efficient
        self.increment /= self.decay_factor;
        
        // Rescale if increment gets too large
        if self.increment > 1e100 {
            self.rescale();
        }
    }

    /// Rescale all activities to prevent overflow
    fn rescale(&mut self) {
        let scale = 1e-100;
        for activity in &mut self.activities {
            *activity *= scale;
        }
        self.increment *= scale;
        
        // Rebuild heap with rescaled activities
        self.rebuild_heap();
    }

    /// Rebuild the heap from current activities
    fn rebuild_heap(&mut self) {
        self.heap.clear();
        for (i, &activity) in self.activities.iter().enumerate() {
            if self.in_heap[i] {
                let var = Variable::new((i + 1) as u32);
                self.heap.push(ActivityEntry { activity, var });
            }
        }
    }

    /// Pick the unassigned variable with highest activity
    /// Returns None if all variables are assigned
    pub fn pick_branching_variable(&mut self, assignments: &Assignments) -> Option<Variable> {
        while let Some(entry) = self.heap.pop() {
            let var = entry.var;
            let idx = var.array_index();
            
            // Check if variable is still unassigned
            if !assignments.value(var).is_assigned() {
                // Check if this is the current activity (not a stale entry)
                if (entry.activity - self.activities[idx]).abs() < 1e-10 {
                    // Re-insert and return
                    self.heap.push(ActivityEntry {
                        activity: self.activities[idx],
                        var,
                    });
                    return Some(var);
                }
                // Stale entry, push updated one and continue
                self.heap.push(ActivityEntry {
                    activity: self.activities[idx],
                    var,
                });
            }
        }
        None
    }

    /// Mark a variable as assigned (remove from heap consideration)
    pub fn var_assigned(&mut self, var: Variable) {
        self.in_heap[var.array_index()] = false;
    }

    /// Mark a variable as unassigned (add back to heap)
    pub fn var_unassigned(&mut self, var: Variable) {
        let idx = var.array_index();
        self.in_heap[idx] = true;
        self.heap.push(ActivityEntry {
            activity: self.activities[idx],
            var,
        });
    }

    /// Get the decay factor
    pub fn decay_factor(&self) -> f64 {
        self.decay_factor
    }

    /// Set the decay factor
    pub fn set_decay_factor(&mut self, factor: f64) {
        assert!(factor > 0.0 && factor < 1.0, "Decay factor must be in (0, 1)");
        self.decay_factor = factor;
    }

    /// Get current increment value (for debugging)
    pub fn increment(&self) -> f64 {
        self.increment
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vsids_creation() {
        let vsids = Vsids::new(5);
        
        for i in 1..=5 {
            assert_eq!(vsids.activity(Variable::new(i)), 0.0);
        }
    }

    #[test]
    fn test_bump_activity() {
        let mut vsids = Vsids::new(3);
        
        let v1 = Variable::new(1);
        let v2 = Variable::new(2);
        
        vsids.bump(v1);
        assert_eq!(vsids.activity(v1), 1.0);
        assert_eq!(vsids.activity(v2), 0.0);
        
        vsids.bump(v1);
        assert_eq!(vsids.activity(v1), 2.0);
        
        vsids.bump(v2);
        assert_eq!(vsids.activity(v2), 1.0);
    }

    #[test]
    fn test_decay() {
        let mut vsids = Vsids::new(2);
        
        let v1 = Variable::new(1);
        
        // Initial bump: activity = 1.0
        vsids.bump(v1);
        assert_eq!(vsids.activity(v1), 1.0);
        
        // Decay increases the increment
        let old_inc = vsids.increment();
        vsids.decay();
        let new_inc = vsids.increment();
        assert!(new_inc > old_inc);
        
        // Next bump uses larger increment
        vsids.bump(v1);
        assert!(vsids.activity(v1) > 2.0);
    }

    #[test]
    fn test_pick_branching_variable() {
        let mut vsids = Vsids::new(3);
        let assignments = Assignments::new(3);
        
        let v1 = Variable::new(1);
        let v2 = Variable::new(2);
        let v3 = Variable::new(3);
        
        // Bump v2 highest
        vsids.bump(v2);
        vsids.bump(v2);
        vsids.bump(v2);
        
        // Bump v3 second
        vsids.bump(v3);
        vsids.bump(v3);
        
        // Bump v1 least
        vsids.bump(v1);
        
        // Should pick v2 (highest activity)
        let picked = vsids.pick_branching_variable(&assignments);
        assert_eq!(picked, Some(v2));
    }

    #[test]
    fn test_pick_skips_assigned() {
        let mut vsids = Vsids::new(3);
        let mut assignments = Assignments::new(3);
        
        let v1 = Variable::new(1);
        let v2 = Variable::new(2);
        let v3 = Variable::new(3);
        let _ = v3; // suppress unused warning
        
        // Bump v1 highest
        vsids.bump(v1);
        vsids.bump(v1);
        vsids.bump(v1);
        
        // Bump v2 second
        vsids.bump(v2);
        vsids.bump(v2);
        
        // Assign v1
        assignments.assign(v1, true, 0, None);
        
        // Should skip v1 and pick v2
        let picked = vsids.pick_branching_variable(&assignments);
        assert_eq!(picked, Some(v2));
    }

    #[test]
    fn test_pick_returns_none_when_all_assigned() {
        let mut vsids = Vsids::new(2);
        let mut assignments = Assignments::new(2);
        
        assignments.assign(Variable::new(1), true, 0, None);
        assignments.assign(Variable::new(2), false, 0, None);
        
        let picked = vsids.pick_branching_variable(&assignments);
        assert_eq!(picked, None);
    }

    #[test]
    fn test_bump_all() {
        let mut vsids = Vsids::new(3);
        
        let v1 = Variable::new(1);
        let v2 = Variable::new(2);
        let v3 = Variable::new(3);
        
        vsids.bump_all(&[v1, v2]);
        
        assert_eq!(vsids.activity(v1), 1.0);
        assert_eq!(vsids.activity(v2), 1.0);
        assert_eq!(vsids.activity(v3), 0.0);
    }

    #[test]
    fn test_rescale() {
        let mut vsids = Vsids::new(2);
        
        let v1 = Variable::new(1);
        
        // Simulate many bumps that would cause overflow
        for _ in 0..1000 {
            vsids.bump(v1);
            vsids.decay();
        }
        
        // Activities should still be reasonable
        assert!(vsids.activity(v1) < 1e100);
        assert!(vsids.increment() < 1e100);
    }

    #[test]
    fn test_decay_factor() {
        let mut vsids = Vsids::new(2);
        
        assert_eq!(vsids.decay_factor(), 0.95);
        
        vsids.set_decay_factor(0.90);
        assert_eq!(vsids.decay_factor(), 0.90);
    }

    #[test]
    #[should_panic]
    fn test_invalid_decay_factor() {
        let mut vsids = Vsids::new(2);
        vsids.set_decay_factor(1.5); // Should panic
    }

    #[test]
    fn test_var_assigned_unassigned() {
        let mut vsids = Vsids::new(2);
        let mut assignments = Assignments::new(2);
        
        let v1 = Variable::new(1);
        let v2 = Variable::new(2);
        
        // Bump v1 higher
        vsids.bump(v1);
        vsids.bump(v1);
        vsids.bump(v2);
        
        // Mark v1 as assigned
        vsids.var_assigned(v1);
        assignments.assign(v1, true, 0, None);
        
        // Should pick v2
        let picked = vsids.pick_branching_variable(&assignments);
        assert_eq!(picked, Some(v2));
        
        // Unassign v1
        vsids.var_unassigned(v1);
        assignments.unassign(v1);
        
        // Now should pick v1 again
        let picked = vsids.pick_branching_variable(&assignments);
        assert_eq!(picked, Some(v1));
    }
}
