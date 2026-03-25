//! LIA (Linear Integer Arithmetic) Theory Solver
//!
//! Implements bound propagation and conflict detection for
//! linear integer arithmetic constraints.

use super::{TheoryConflict, TheoryPropagation, TheoryResult, TheorySolver};
use crate::literal::Literal;
use std::collections::HashMap;

/// A linear expression: c1*x1 + c2*x2 + ... + cn*xn + k
#[derive(Debug, Clone)]
pub struct LinearExpr {
    /// Coefficients for each variable
    pub terms: Vec<(VarId, i64)>,
    /// Constant term
    pub constant: i64,
}

impl LinearExpr {
    /// Create a new linear expression
    pub fn new(terms: Vec<(VarId, i64)>, constant: i64) -> Self {
        LinearExpr { terms, constant }
    }

    /// Create a constant expression
    pub fn constant(k: i64) -> Self {
        LinearExpr { terms: Vec::new(), constant: k }
    }

    /// Create a single variable expression
    pub fn var(var: VarId) -> Self {
        LinearExpr { terms: vec![(var, 1)], constant: 0 }
    }

    /// Add two expressions
    pub fn add(&self, other: &LinearExpr) -> LinearExpr {
        let mut result = self.clone();
        result.constant += other.constant;
        
        for (var, coeff) in &other.terms {
            if let Some(pos) = result.terms.iter().position(|(v, _)| v == var) {
                result.terms[pos].1 += coeff;
                if result.terms[pos].1 == 0 {
                    result.terms.remove(pos);
                }
            } else {
                result.terms.push((*var, *coeff));
            }
        }
        result
    }

    /// Multiply by a scalar
    pub fn scale(&self, k: i64) -> LinearExpr {
        LinearExpr {
            terms: self.terms.iter().map(|(v, c)| (*v, c * k)).collect(),
            constant: self.constant * k,
        }
    }

    /// Evaluate the expression given variable assignments
    pub fn evaluate(&self, assignments: &HashMap<VarId, i64>) -> Option<i64> {
        let mut result = self.constant;
        for (var, coeff) in &self.terms {
            result += coeff * assignments.get(var)?;
        }
        Some(result)
    }
}

/// Variable identifier
pub type VarId = u32;

/// A bound on a variable
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Bound {
    /// x >= k
    Lower(i64),
    /// x <= k
    Upper(i64),
    /// x == k
    Exact(i64),
}

/// A LIA constraint
#[derive(Debug, Clone)]
pub struct LiaConstraint {
    /// The constraint kind
    pub kind: ConstraintKind,
    /// The SAT literal that implies this constraint
    pub literal: Literal,
    /// Decision level when asserted
    pub level: u32,
}

/// Kinds of LIA constraints
#[derive(Debug, Clone)]
pub enum ConstraintKind {
    /// expr >= 0
    Ge(LinearExpr),
    /// expr > 0 (equivalent to expr >= 1 for integers)
    Gt(LinearExpr),
    /// expr <= 0
    Le(LinearExpr),
    /// expr < 0 (equivalent to expr <= -1 for integers)
    Lt(LinearExpr),
    /// expr == 0
    Eq(LinearExpr),
    /// expr != 0
    Ne(LinearExpr),
}

/// Variable bounds
#[derive(Debug, Clone)]
struct VarBounds {
    /// Lower bounds (value, reason literal)
    lower: Vec<(i64, Literal)>,
    /// Upper bounds (value, reason literal)
    upper: Vec<(i64, Literal)>,
}

impl VarBounds {
    fn new() -> Self {
        VarBounds {
            lower: Vec::new(),
            upper: Vec::new(),
        }
    }

    /// Get the current lower bound
    fn lower_bound(&self) -> Option<(i64, Literal)> {
        self.lower.iter().max_by_key(|(v, _)| v).cloned()
    }

    /// Get the current upper bound
    fn upper_bound(&self) -> Option<(i64, Literal)> {
        self.upper.iter().min_by_key(|(v, _)| v).cloned()
    }

    /// Check if bounds are consistent
    fn is_consistent(&self) -> bool {
        match (self.lower_bound(), self.upper_bound()) {
            (Some((lo, _)), Some((hi, _))) => lo <= hi,
            _ => true,
        }
    }
}

/// LIA Theory Solver
pub struct LiaSolver {
    /// Variable bounds
    bounds: HashMap<VarId, VarBounds>,
    /// Asserted constraints (for check)
    constraints: Vec<LiaConstraint>,
    /// Current decision level
    level: u32,
    /// Trail for backtracking
    trail: Vec<(u32, VarId, bool)>, // (level, var, is_lower)
    /// Propagated literals
    propagated: HashMap<Literal, Vec<Literal>>,
}

impl LiaSolver {
    /// Create a new LIA solver
    pub fn new() -> Self {
        LiaSolver {
            bounds: HashMap::new(),
            constraints: Vec::new(),
            level: 0,
            trail: Vec::new(),
            propagated: HashMap::new(),
        }
    }

    /// Ensure a variable exists in bounds map
    fn ensure_var(&mut self, var: VarId) {
        self.bounds.entry(var).or_insert_with(VarBounds::new);
    }

    /// Assert a lower bound on a variable
    pub fn assert_lower(&mut self, var: VarId, bound: i64, reason: Literal) -> TheoryResult<()> {
        self.ensure_var(var);
        
        let bounds = self.bounds.get_mut(&var).unwrap();
        
        // Check for conflict with upper bound
        if let Some((upper, upper_lit)) = bounds.upper_bound() {
            if bound > upper {
                // Conflict: lower > upper
                return Err(TheoryConflict::new(vec![reason, upper_lit]));
            }
        }
        
        bounds.lower.push((bound, reason));
        self.trail.push((self.level, var, true));
        
        Ok(())
    }

    /// Assert an upper bound on a variable
    pub fn assert_upper(&mut self, var: VarId, bound: i64, reason: Literal) -> TheoryResult<()> {
        self.ensure_var(var);
        
        let bounds = self.bounds.get_mut(&var).unwrap();
        
        // Check for conflict with lower bound
        if let Some((lower, lower_lit)) = bounds.lower_bound() {
            if bound < lower {
                // Conflict: upper < lower
                return Err(TheoryConflict::new(vec![reason, lower_lit]));
            }
        }
        
        bounds.upper.push((bound, reason));
        self.trail.push((self.level, var, false));
        
        Ok(())
    }

    /// Assert an equality (x == k)
    pub fn assert_equal(&mut self, var: VarId, value: i64, reason: Literal) -> TheoryResult<()> {
        self.assert_lower(var, value, reason)?;
        self.assert_upper(var, value, reason)?;
        Ok(())
    }

    /// Assert a constraint
    pub fn assert_constraint(&mut self, constraint: LiaConstraint) -> TheoryResult<()> {
        // For simple single-variable constraints, we can extract bounds directly
        let result = match &constraint.kind {
            ConstraintKind::Ge(expr) => {
                if expr.terms.len() == 1 {
                    let (var, coeff) = expr.terms[0];
                    if coeff == 1 {
                        // x + k >= 0 means x >= -k
                        self.assert_lower(var, -expr.constant, constraint.literal)
                    } else if coeff == -1 {
                        // -x + k >= 0 means x <= k
                        self.assert_upper(var, expr.constant, constraint.literal)
                    } else {
                        Ok(()) // Complex constraint, defer to check
                    }
                } else {
                    Ok(())
                }
            }
            ConstraintKind::Le(expr) => {
                if expr.terms.len() == 1 {
                    let (var, coeff) = expr.terms[0];
                    if coeff == 1 {
                        // x + k <= 0 means x <= -k
                        self.assert_upper(var, -expr.constant, constraint.literal)
                    } else if coeff == -1 {
                        // -x + k <= 0 means x >= k
                        self.assert_lower(var, expr.constant, constraint.literal)
                    } else {
                        Ok(())
                    }
                } else {
                    Ok(())
                }
            }
            ConstraintKind::Gt(expr) => {
                // x + k > 0 is x + k >= 1 for integers
                let adjusted = LinearExpr::new(expr.terms.clone(), expr.constant - 1);
                let adjusted_constraint = LiaConstraint {
                    kind: ConstraintKind::Ge(adjusted),
                    literal: constraint.literal,
                    level: constraint.level,
                };
                return self.assert_constraint(adjusted_constraint);
            }
            ConstraintKind::Lt(expr) => {
                // x + k < 0 is x + k <= -1 for integers
                let adjusted = LinearExpr::new(expr.terms.clone(), expr.constant + 1);
                let adjusted_constraint = LiaConstraint {
                    kind: ConstraintKind::Le(adjusted),
                    literal: constraint.literal,
                    level: constraint.level,
                };
                return self.assert_constraint(adjusted_constraint);
            }
            ConstraintKind::Eq(expr) => {
                if expr.terms.len() == 1 && expr.terms[0].1.abs() == 1 {
                    let (var, coeff) = expr.terms[0];
                    let value = if coeff == 1 { -expr.constant } else { expr.constant };
                    self.assert_equal(var, value, constraint.literal)
                } else {
                    Ok(())
                }
            }
            ConstraintKind::Ne(_) => {
                // Disequalities are handled during check
                Ok(())
            }
        };
        
        self.constraints.push(constraint);
        result
    }

    /// Get the current bounds for a variable
    pub fn get_bounds(&self, var: VarId) -> (Option<i64>, Option<i64>) {
        match self.bounds.get(&var) {
            Some(b) => (
                b.lower_bound().map(|(v, _)| v),
                b.upper_bound().map(|(v, _)| v),
            ),
            None => (None, None),
        }
    }
}

impl Default for LiaSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl TheorySolver for LiaSolver {
    fn name(&self) -> &'static str {
        "LIA"
    }

    fn assert_literal(&mut self, _lit: Literal) -> TheoryResult<()> {
        // Literal decoding handled externally via assert_constraint
        Ok(())
    }

    fn check(&mut self) -> TheoryResult<()> {
        // Check all variable bounds are consistent
        for (_var, bounds) in &self.bounds {
            if !bounds.is_consistent() {
                let (_, lower_lit) = bounds.lower_bound().unwrap();
                let (_, upper_lit) = bounds.upper_bound().unwrap();
                return Err(TheoryConflict::new(vec![lower_lit, upper_lit]));
            }
        }
        
        // For now, we don't check complex multi-variable constraints
        // A full implementation would use Simplex
        Ok(())
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        // Bound propagation could deduce new bounds from constraints
        // For now, return empty
        Vec::new()
    }

    fn explain(&self, lit: Literal) -> Vec<Literal> {
        self.propagated.get(&lit).cloned().unwrap_or_default()
    }

    fn backtrack(&mut self, level: u32) {
        self.level = level;
        
        // Remove bounds from higher levels
        while let Some(&(bound_level, var, is_lower)) = self.trail.last() {
            if bound_level <= level {
                break;
            }
            
            if let Some(bounds) = self.bounds.get_mut(&var) {
                if is_lower {
                    bounds.lower.pop();
                } else {
                    bounds.upper.pop();
                }
            }
            
            self.trail.pop();
        }
        
        // Remove constraints from higher levels
        self.constraints.retain(|c| c.level <= level);
    }

    fn push_level(&mut self) {
        self.level += 1;
    }

    fn current_level(&self) -> u32 {
        self.level
    }

    fn reset(&mut self) {
        self.bounds.clear();
        self.constraints.clear();
        self.level = 0;
        self.trail.clear();
        self.propagated.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Variable;

    fn lit(var: u32, positive: bool) -> Literal {
        Literal::new(Variable::new(var), positive)
    }

    #[test]
    fn test_lia_lower_bound() {
        let mut solver = LiaSolver::new();
        
        // x >= 5
        solver.assert_lower(1, 5, lit(1, true)).unwrap();
        
        let (lo, hi) = solver.get_bounds(1);
        assert_eq!(lo, Some(5));
        assert_eq!(hi, None);
    }

    #[test]
    fn test_lia_upper_bound() {
        let mut solver = LiaSolver::new();
        
        // x <= 10
        solver.assert_upper(1, 10, lit(1, true)).unwrap();
        
        let (lo, hi) = solver.get_bounds(1);
        assert_eq!(lo, None);
        assert_eq!(hi, Some(10));
    }

    #[test]
    fn test_lia_both_bounds() {
        let mut solver = LiaSolver::new();
        
        // 5 <= x <= 10
        solver.assert_lower(1, 5, lit(1, true)).unwrap();
        solver.assert_upper(1, 10, lit(2, true)).unwrap();
        
        let (lo, hi) = solver.get_bounds(1);
        assert_eq!(lo, Some(5));
        assert_eq!(hi, Some(10));
        
        assert!(solver.check().is_ok());
    }

    #[test]
    fn test_lia_conflict_lower_upper() {
        let mut solver = LiaSolver::new();
        
        // x >= 10
        solver.assert_lower(1, 10, lit(1, true)).unwrap();
        
        // x <= 5 - conflict!
        let result = solver.assert_upper(1, 5, lit(2, true));
        assert!(result.is_err());
    }

    #[test]
    fn test_lia_equality() {
        let mut solver = LiaSolver::new();
        
        // x == 7
        solver.assert_equal(1, 7, lit(1, true)).unwrap();
        
        let (lo, hi) = solver.get_bounds(1);
        assert_eq!(lo, Some(7));
        assert_eq!(hi, Some(7));
    }

    #[test]
    fn test_lia_constraint_ge() {
        let mut solver = LiaSolver::new();
        
        // x >= 5 as constraint (x + (-5) >= 0)
        let expr = LinearExpr::new(vec![(1, 1)], -5);
        let constraint = LiaConstraint {
            kind: ConstraintKind::Ge(expr),
            literal: lit(1, true),
            level: 0,
        };
        
        solver.assert_constraint(constraint).unwrap();
        
        let (lo, _) = solver.get_bounds(1);
        assert_eq!(lo, Some(5));
    }

    #[test]
    fn test_lia_constraint_le() {
        let mut solver = LiaSolver::new();
        
        // x <= 10 as constraint (x + (-10) <= 0)
        let expr = LinearExpr::new(vec![(1, 1)], -10);
        let constraint = LiaConstraint {
            kind: ConstraintKind::Le(expr),
            literal: lit(1, true),
            level: 0,
        };
        
        solver.assert_constraint(constraint).unwrap();
        
        let (_, hi) = solver.get_bounds(1);
        assert_eq!(hi, Some(10));
    }

    #[test]
    fn test_lia_backtrack() {
        let mut solver = LiaSolver::new();
        
        // Level 0: x >= 5
        solver.assert_lower(1, 5, lit(1, true)).unwrap();
        
        // Level 1: x >= 10 (tighter bound)
        solver.push_level();
        solver.assert_lower(1, 10, lit(2, true)).unwrap();
        
        let (lo, _) = solver.get_bounds(1);
        assert_eq!(lo, Some(10));
        
        // Backtrack to level 0
        solver.backtrack(0);
        
        let (lo, _) = solver.get_bounds(1);
        assert_eq!(lo, Some(5));
    }

    #[test]
    fn test_lia_reset() {
        let mut solver = LiaSolver::new();
        
        solver.assert_lower(1, 5, lit(1, true)).unwrap();
        solver.reset();
        
        let (lo, hi) = solver.get_bounds(1);
        assert_eq!(lo, None);
        assert_eq!(hi, None);
    }

    #[test]
    fn test_linear_expr_evaluate() {
        // 2x + 3y + 5
        let expr = LinearExpr::new(vec![(1, 2), (2, 3)], 5);
        
        let mut assignments = HashMap::new();
        assignments.insert(1, 10); // x = 10
        assignments.insert(2, 20); // y = 20
        
        // 2*10 + 3*20 + 5 = 20 + 60 + 5 = 85
        assert_eq!(expr.evaluate(&assignments), Some(85));
    }

    #[test]
    fn test_linear_expr_add() {
        // x + 5
        let e1 = LinearExpr::new(vec![(1, 1)], 5);
        // 2x + y + 3
        let e2 = LinearExpr::new(vec![(1, 2), (2, 1)], 3);
        
        // 3x + y + 8
        let result = e1.add(&e2);
        assert_eq!(result.constant, 8);
        
        let mut assignments = HashMap::new();
        assignments.insert(1, 1);
        assignments.insert(2, 1);
        // 3*1 + 1 + 8 = 12
        assert_eq!(result.evaluate(&assignments), Some(12));
    }
}
