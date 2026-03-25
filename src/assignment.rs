//! Variable assignment tracking

use crate::clause::ClauseRef;
use crate::literal::{Literal, Variable};

/// The value of a variable assignment
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Value {
    True,
    False,
    Unassigned,
}

impl Value {
    /// Check if the value is assigned
    pub fn is_assigned(&self) -> bool {
        !matches!(self, Value::Unassigned)
    }

    /// Convert to Option<bool>
    pub fn to_bool(&self) -> Option<bool> {
        match self {
            Value::True => Some(true),
            Value::False => Some(false),
            Value::Unassigned => None,
        }
    }

    /// Create from bool
    pub fn from_bool(b: bool) -> Self {
        if b { Value::True } else { Value::False }
    }
}

/// Information about a single variable assignment
#[derive(Debug, Clone)]
pub struct AssignmentInfo {
    /// The assigned value
    pub value: Value,
    /// Decision level at which this assignment was made
    pub level: u32,
    /// The clause that forced this assignment (None for decisions)
    pub antecedent: Option<ClauseRef>,
    /// Order in which this variable was assigned (for trail)
    pub order: u32,
}

impl AssignmentInfo {
    /// Create a new unassigned info
    pub fn unassigned() -> Self {
        AssignmentInfo {
            value: Value::Unassigned,
            level: 0,
            antecedent: None,
            order: 0,
        }
    }

    /// Check if this is a decision (no antecedent)
    pub fn is_decision(&self) -> bool {
        self.antecedent.is_none() && self.value.is_assigned()
    }

    /// Check if this is a propagated assignment
    pub fn is_propagated(&self) -> bool {
        self.antecedent.is_some()
    }
}

/// Manages variable assignments
#[derive(Debug)]
pub struct Assignments {
    /// Assignment info for each variable (indexed by variable - 1)
    assignments: Vec<AssignmentInfo>,
    /// Current assignment order counter
    order_counter: u32,
}

impl Assignments {
    /// Create a new assignment tracker for the given number of variables
    pub fn new(num_vars: u32) -> Self {
        Assignments {
            assignments: vec![AssignmentInfo::unassigned(); num_vars as usize],
            order_counter: 0,
        }
    }

    /// Resize to accommodate more variables
    pub fn resize(&mut self, num_vars: u32) {
        while self.assignments.len() < num_vars as usize {
            self.assignments.push(AssignmentInfo::unassigned());
        }
    }

    /// Get the value of a variable
    pub fn value(&self, var: Variable) -> Value {
        self.assignments
            .get(var.array_index())
            .map(|a| a.value)
            .unwrap_or(Value::Unassigned)
    }

    /// Get the decision level of a variable
    pub fn level(&self, var: Variable) -> u32 {
        self.assignments
            .get(var.array_index())
            .map(|a| a.level)
            .unwrap_or(0)
    }

    /// Get the antecedent clause of a variable
    pub fn antecedent(&self, var: Variable) -> Option<ClauseRef> {
        self.assignments
            .get(var.array_index())
            .and_then(|a| a.antecedent)
    }

    /// Get the assignment info for a variable
    pub fn info(&self, var: Variable) -> Option<&AssignmentInfo> {
        self.assignments.get(var.array_index())
    }

    /// Check if a variable is assigned
    pub fn is_assigned(&self, var: Variable) -> bool {
        self.value(var).is_assigned()
    }

    /// Assign a variable (decision or propagation)
    pub fn assign(
        &mut self,
        var: Variable,
        value: bool,
        level: u32,
        antecedent: Option<ClauseRef>,
    ) {
        let idx = var.array_index();
        if idx >= self.assignments.len() {
            self.resize(var.index());
        }
        
        self.order_counter += 1;
        self.assignments[idx] = AssignmentInfo {
            value: Value::from_bool(value),
            level,
            antecedent,
            order: self.order_counter,
        };
    }

    /// Make a decision assignment
    pub fn decide(&mut self, var: Variable, value: bool, level: u32) {
        self.assign(var, value, level, None);
    }

    /// Make a propagated assignment
    pub fn propagate(&mut self, var: Variable, value: bool, level: u32, antecedent: ClauseRef) {
        self.assign(var, value, level, Some(antecedent));
    }

    /// Unassign a variable
    pub fn unassign(&mut self, var: Variable) {
        let idx = var.array_index();
        if idx < self.assignments.len() {
            self.assignments[idx] = AssignmentInfo::unassigned();
        }
    }

    /// Evaluate a literal given current assignments
    pub fn eval_literal(&self, lit: Literal) -> Value {
        match self.value(lit.variable()) {
            Value::True => {
                if lit.is_positive() {
                    Value::True
                } else {
                    Value::False
                }
            }
            Value::False => {
                if lit.is_positive() {
                    Value::False
                } else {
                    Value::True
                }
            }
            Value::Unassigned => Value::Unassigned,
        }
    }

    /// Check if a literal is satisfied
    pub fn is_satisfied(&self, lit: Literal) -> bool {
        self.eval_literal(lit) == Value::True
    }

    /// Check if a literal is falsified
    pub fn is_falsified(&self, lit: Literal) -> bool {
        self.eval_literal(lit) == Value::False
    }

    /// Get all assigned variables
    pub fn assigned_vars(&self) -> impl Iterator<Item = Variable> + '_ {
        self.assignments
            .iter()
            .enumerate()
            .filter(|(_, a)| a.value.is_assigned())
            .map(|(i, _)| Variable::new((i + 1) as u32))
    }

    /// Get the number of assigned variables
    pub fn num_assigned(&self) -> usize {
        self.assignments.iter().filter(|a| a.value.is_assigned()).count()
    }

    /// Check if all variables are assigned
    pub fn all_assigned(&self) -> bool {
        self.assignments.iter().all(|a| a.value.is_assigned())
    }

    /// Get the current model (assignment of all variables)
    pub fn model(&self) -> Vec<bool> {
        self.assignments
            .iter()
            .map(|a| a.value == Value::True)
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_value() {
        assert!(Value::True.is_assigned());
        assert!(Value::False.is_assigned());
        assert!(!Value::Unassigned.is_assigned());

        assert_eq!(Value::True.to_bool(), Some(true));
        assert_eq!(Value::False.to_bool(), Some(false));
        assert_eq!(Value::Unassigned.to_bool(), None);

        assert_eq!(Value::from_bool(true), Value::True);
        assert_eq!(Value::from_bool(false), Value::False);
    }

    #[test]
    fn test_assignments_creation() {
        let assignments = Assignments::new(5);
        
        for i in 1..=5 {
            let var = Variable::new(i);
            assert_eq!(assignments.value(var), Value::Unassigned);
            assert!(!assignments.is_assigned(var));
        }
    }

    #[test]
    fn test_decide() {
        let mut assignments = Assignments::new(5);
        let var = Variable::new(2);
        
        assignments.decide(var, true, 1);
        
        assert_eq!(assignments.value(var), Value::True);
        assert_eq!(assignments.level(var), 1);
        assert_eq!(assignments.antecedent(var), None);
        assert!(assignments.is_assigned(var));
    }

    #[test]
    fn test_propagate() {
        let mut assignments = Assignments::new(5);
        let var = Variable::new(3);
        
        assignments.propagate(var, false, 2, 0);
        
        assert_eq!(assignments.value(var), Value::False);
        assert_eq!(assignments.level(var), 2);
        assert_eq!(assignments.antecedent(var), Some(0));
    }

    #[test]
    fn test_unassign() {
        let mut assignments = Assignments::new(5);
        let var = Variable::new(1);
        
        assignments.decide(var, true, 1);
        assert!(assignments.is_assigned(var));
        
        assignments.unassign(var);
        assert!(!assignments.is_assigned(var));
        assert_eq!(assignments.value(var), Value::Unassigned);
    }

    #[test]
    fn test_eval_literal() {
        let mut assignments = Assignments::new(5);
        let var = Variable::new(2);
        
        // Unassigned
        let pos = Literal::positive(var);
        let neg = Literal::negative(var);
        assert_eq!(assignments.eval_literal(pos), Value::Unassigned);
        assert_eq!(assignments.eval_literal(neg), Value::Unassigned);
        
        // Assigned true
        assignments.decide(var, true, 1);
        assert_eq!(assignments.eval_literal(pos), Value::True);
        assert_eq!(assignments.eval_literal(neg), Value::False);
        assert!(assignments.is_satisfied(pos));
        assert!(assignments.is_falsified(neg));
        
        // Assigned false
        assignments.unassign(var);
        assignments.decide(var, false, 1);
        assert_eq!(assignments.eval_literal(pos), Value::False);
        assert_eq!(assignments.eval_literal(neg), Value::True);
    }

    #[test]
    fn test_assigned_vars() {
        let mut assignments = Assignments::new(5);
        
        assignments.decide(Variable::new(1), true, 1);
        assignments.decide(Variable::new(3), false, 1);
        assignments.decide(Variable::new(5), true, 2);
        
        let assigned: Vec<_> = assignments.assigned_vars().collect();
        assert_eq!(assigned.len(), 3);
        assert!(assigned.contains(&Variable::new(1)));
        assert!(assigned.contains(&Variable::new(3)));
        assert!(assigned.contains(&Variable::new(5)));
    }

    #[test]
    fn test_num_assigned() {
        let mut assignments = Assignments::new(5);
        
        assert_eq!(assignments.num_assigned(), 0);
        assert!(!assignments.all_assigned());
        
        assignments.decide(Variable::new(1), true, 1);
        assignments.decide(Variable::new(2), true, 1);
        assert_eq!(assignments.num_assigned(), 2);
        
        assignments.decide(Variable::new(3), true, 1);
        assignments.decide(Variable::new(4), true, 1);
        assignments.decide(Variable::new(5), true, 1);
        assert_eq!(assignments.num_assigned(), 5);
        assert!(assignments.all_assigned());
    }

    #[test]
    fn test_model() {
        let mut assignments = Assignments::new(3);
        
        assignments.decide(Variable::new(1), true, 1);
        assignments.decide(Variable::new(2), false, 1);
        assignments.decide(Variable::new(3), true, 1);
        
        let model = assignments.model();
        assert_eq!(model, vec![true, false, true]);
    }

    #[test]
    fn test_assignment_info() {
        let mut assignments = Assignments::new(5);
        
        // Decision
        assignments.decide(Variable::new(1), true, 1);
        let info = assignments.info(Variable::new(1)).unwrap();
        assert!(info.is_decision());
        assert!(!info.is_propagated());
        
        // Propagation
        assignments.propagate(Variable::new(2), false, 1, 0);
        let info = assignments.info(Variable::new(2)).unwrap();
        assert!(!info.is_decision());
        assert!(info.is_propagated());
    }

    #[test]
    fn test_resize() {
        let mut assignments = Assignments::new(2);
        
        // Should auto-resize on assign
        assignments.decide(Variable::new(5), true, 1);
        assert!(assignments.is_assigned(Variable::new(5)));
    }
}
