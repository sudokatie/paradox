//! Variable assignment tracking.

use crate::clause::ClauseRef;
use crate::literal::{Literal, Variable};

/// Value of a variable.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Value {
    True,
    False,
    Unassigned,
}

impl Value {
    /// Negate the value (True <-> False, Unassigned stays).
    pub fn negate(self) -> Self {
        match self {
            Value::True => Value::False,
            Value::False => Value::True,
            Value::Unassigned => Value::Unassigned,
        }
    }

    /// Check if this value satisfies a literal.
    pub fn satisfies(self, positive: bool) -> bool {
        match (self, positive) {
            (Value::True, true) => true,
            (Value::False, false) => true,
            _ => false,
        }
    }

    /// Check if assigned (True or False).
    pub fn is_assigned(self) -> bool {
        self != Value::Unassigned
    }
}

/// Information about a variable's assignment.
#[derive(Clone, Debug)]
pub struct AssignmentInfo {
    /// The assigned value.
    pub value: Value,
    /// Decision level at which this assignment was made.
    pub level: u32,
    /// The clause that implied this assignment (None for decisions).
    pub antecedent: Option<ClauseRef>,
    /// Order in which this assignment was made (for trail).
    pub order: u32,
}

impl Default for AssignmentInfo {
    fn default() -> Self {
        AssignmentInfo {
            value: Value::Unassigned,
            level: 0,
            antecedent: None,
            order: 0,
        }
    }
}

/// Track assignments for all variables.
pub struct Assignments {
    /// Per-variable assignment info.
    assignments: Vec<AssignmentInfo>,
    /// Counter for assignment order.
    order_counter: u32,
}

impl Assignments {
    /// Create assignments for a given number of variables.
    pub fn new(num_vars: u32) -> Self {
        Assignments {
            assignments: vec![AssignmentInfo::default(); num_vars as usize],
            order_counter: 0,
        }
    }

    /// Get the value of a variable.
    pub fn value(&self, var: Variable) -> Value {
        self.assignments
            .get(var.to_index())
            .map(|a| a.value)
            .unwrap_or(Value::Unassigned)
    }

    /// Get the decision level of a variable's assignment.
    pub fn level(&self, var: Variable) -> u32 {
        self.assignments
            .get(var.to_index())
            .map(|a| a.level)
            .unwrap_or(0)
    }

    /// Get the antecedent clause (None for decisions).
    pub fn antecedent(&self, var: Variable) -> Option<ClauseRef> {
        self.assignments.get(var.to_index()).and_then(|a| a.antecedent)
    }

    /// Get full assignment info.
    pub fn info(&self, var: Variable) -> Option<&AssignmentInfo> {
        self.assignments.get(var.to_index())
    }

    /// Check if a variable is assigned.
    pub fn is_assigned(&self, var: Variable) -> bool {
        self.value(var).is_assigned()
    }

    /// Assign a variable.
    pub fn assign(
        &mut self,
        var: Variable,
        value: Value,
        level: u32,
        antecedent: Option<ClauseRef>,
    ) {
        debug_assert!(value != Value::Unassigned);
        let idx = var.to_index();
        if idx >= self.assignments.len() {
            self.assignments.resize(idx + 1, AssignmentInfo::default());
        }
        self.order_counter += 1;
        self.assignments[idx] = AssignmentInfo {
            value,
            level,
            antecedent,
            order: self.order_counter,
        };
    }

    /// Unassign a variable.
    pub fn unassign(&mut self, var: Variable) {
        let idx = var.to_index();
        if idx < self.assignments.len() {
            self.assignments[idx] = AssignmentInfo::default();
        }
    }

    /// Evaluate a literal given current assignments.
    pub fn eval_literal(&self, lit: Literal) -> Value {
        let val = self.value(lit.variable());
        if lit.is_positive() {
            val
        } else {
            val.negate()
        }
    }

    /// Check if a literal is satisfied.
    pub fn is_satisfied(&self, lit: Literal) -> bool {
        self.eval_literal(lit) == Value::True
    }

    /// Check if a literal is falsified.
    pub fn is_falsified(&self, lit: Literal) -> bool {
        self.eval_literal(lit) == Value::False
    }

    /// Get the model (assignments for SAT result).
    pub fn model(&self) -> Vec<bool> {
        self.assignments
            .iter()
            .map(|a| a.value == Value::True)
            .collect()
    }

    /// Get model as DIMACS literals.
    pub fn model_dimacs(&self) -> Vec<i32> {
        self.assignments
            .iter()
            .enumerate()
            .filter(|(_, a)| a.value != Value::Unassigned)
            .map(|(i, a)| {
                let var = (i + 1) as i32;
                if a.value == Value::True {
                    var
                } else {
                    -var
                }
            })
            .collect()
    }

    /// Count assigned variables.
    pub fn num_assigned(&self) -> usize {
        self.assignments
            .iter()
            .filter(|a| a.value.is_assigned())
            .count()
    }

    /// Count unassigned variables.
    pub fn num_unassigned(&self) -> usize {
        self.assignments
            .iter()
            .filter(|a| !a.value.is_assigned())
            .count()
    }

    /// Get all unassigned variables.
    pub fn unassigned_vars(&self) -> impl Iterator<Item = Variable> + '_ {
        self.assignments
            .iter()
            .enumerate()
            .filter(|(_, a)| !a.value.is_assigned())
            .map(|(i, _)| Variable::from_index(i))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(n: u32) -> Variable {
        Variable::new(n)
    }

    fn lit(v: i32) -> Literal {
        Literal::from_dimacs(v)
    }

    #[test]
    fn test_value_negate() {
        assert_eq!(Value::True.negate(), Value::False);
        assert_eq!(Value::False.negate(), Value::True);
        assert_eq!(Value::Unassigned.negate(), Value::Unassigned);
    }

    #[test]
    fn test_value_satisfies() {
        assert!(Value::True.satisfies(true));
        assert!(!Value::True.satisfies(false));
        assert!(!Value::False.satisfies(true));
        assert!(Value::False.satisfies(false));
        assert!(!Value::Unassigned.satisfies(true));
        assert!(!Value::Unassigned.satisfies(false));
    }

    #[test]
    fn test_new_assignments() {
        let a = Assignments::new(5);
        for i in 1..=5 {
            assert_eq!(a.value(var(i)), Value::Unassigned);
            assert!(!a.is_assigned(var(i)));
        }
    }

    #[test]
    fn test_assign_and_unassign() {
        let mut a = Assignments::new(3);
        
        a.assign(var(1), Value::True, 1, None);
        assert_eq!(a.value(var(1)), Value::True);
        assert!(a.is_assigned(var(1)));
        assert_eq!(a.level(var(1)), 1);
        assert!(a.antecedent(var(1)).is_none());
        
        a.assign(var(2), Value::False, 2, Some(5));
        assert_eq!(a.value(var(2)), Value::False);
        assert_eq!(a.level(var(2)), 2);
        assert_eq!(a.antecedent(var(2)), Some(5));
        
        a.unassign(var(1));
        assert_eq!(a.value(var(1)), Value::Unassigned);
        assert!(!a.is_assigned(var(1)));
    }

    #[test]
    fn test_eval_literal() {
        let mut a = Assignments::new(3);
        a.assign(var(1), Value::True, 0, None);
        a.assign(var(2), Value::False, 0, None);
        
        // Positive literal, true variable -> True
        assert_eq!(a.eval_literal(lit(1)), Value::True);
        // Negative literal, true variable -> False
        assert_eq!(a.eval_literal(lit(-1)), Value::False);
        // Positive literal, false variable -> False
        assert_eq!(a.eval_literal(lit(2)), Value::False);
        // Negative literal, false variable -> True
        assert_eq!(a.eval_literal(lit(-2)), Value::True);
        // Unassigned
        assert_eq!(a.eval_literal(lit(3)), Value::Unassigned);
        assert_eq!(a.eval_literal(lit(-3)), Value::Unassigned);
    }

    #[test]
    fn test_is_satisfied_falsified() {
        let mut a = Assignments::new(2);
        a.assign(var(1), Value::True, 0, None);
        
        assert!(a.is_satisfied(lit(1)));
        assert!(!a.is_falsified(lit(1)));
        assert!(!a.is_satisfied(lit(-1)));
        assert!(a.is_falsified(lit(-1)));
    }

    #[test]
    fn test_model() {
        let mut a = Assignments::new(3);
        a.assign(var(1), Value::True, 0, None);
        a.assign(var(2), Value::False, 0, None);
        a.assign(var(3), Value::True, 0, None);
        
        let model = a.model();
        assert_eq!(model, vec![true, false, true]);
    }

    #[test]
    fn test_model_dimacs() {
        let mut a = Assignments::new(3);
        a.assign(var(1), Value::True, 0, None);
        a.assign(var(2), Value::False, 0, None);
        a.assign(var(3), Value::True, 0, None);
        
        let model = a.model_dimacs();
        assert_eq!(model, vec![1, -2, 3]);
    }

    #[test]
    fn test_counting() {
        let mut a = Assignments::new(5);
        a.assign(var(1), Value::True, 0, None);
        a.assign(var(3), Value::False, 0, None);
        
        assert_eq!(a.num_assigned(), 2);
        assert_eq!(a.num_unassigned(), 3);
    }

    #[test]
    fn test_unassigned_vars() {
        let mut a = Assignments::new(5);
        a.assign(var(1), Value::True, 0, None);
        a.assign(var(3), Value::False, 0, None);
        
        let unassigned: Vec<_> = a.unassigned_vars().collect();
        assert_eq!(unassigned.len(), 3);
        assert_eq!(unassigned[0].index(), 2);
        assert_eq!(unassigned[1].index(), 4);
        assert_eq!(unassigned[2].index(), 5);
    }

    #[test]
    fn test_assignment_order() {
        let mut a = Assignments::new(3);
        a.assign(var(2), Value::True, 0, None);
        a.assign(var(1), Value::False, 0, None);
        
        // Order should be different
        assert!(a.info(var(1)).unwrap().order > a.info(var(2)).unwrap().order);
    }
}
