//! Theory solver for Linear Integer Arithmetic (LIA).
//!
//! Handles:
//! - Linear constraints: a₁x₁ + a₂x₂ + ... + aₙxₙ ⋈ c (where ⋈ ∈ {<, ≤, =, ≥, >})
//! - Bound propagation
//! - Conflict detection via bound inconsistency

use std::collections::HashMap;
use crate::literal::Literal;
use super::{TheorySolver, TheoryConflict, TheoryPropagation, TheoryResult};

/// Variable identifier.
pub type VarId = u32;

/// A coefficient in a linear expression.
pub type Coeff = i64;

/// A linear expression: Σ aᵢxᵢ
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearExpr {
    /// Variable coefficients.
    pub coeffs: HashMap<VarId, Coeff>,
    /// Constant term.
    pub constant: Coeff,
}

impl LinearExpr {
    /// Create a zero expression.
    pub fn zero() -> Self {
        LinearExpr {
            coeffs: HashMap::new(),
            constant: 0,
        }
    }
    
    /// Create a constant expression.
    pub fn constant(c: Coeff) -> Self {
        LinearExpr {
            coeffs: HashMap::new(),
            constant: c,
        }
    }
    
    /// Create a variable expression.
    pub fn var(v: VarId) -> Self {
        let mut coeffs = HashMap::new();
        coeffs.insert(v, 1);
        LinearExpr {
            coeffs,
            constant: 0,
        }
    }
    
    /// Add another expression to this one.
    pub fn add(&self, other: &LinearExpr) -> Self {
        let mut result = self.clone();
        for (&var, &coeff) in &other.coeffs {
            *result.coeffs.entry(var).or_insert(0) += coeff;
            if result.coeffs[&var] == 0 {
                result.coeffs.remove(&var);
            }
        }
        result.constant += other.constant;
        result
    }
    
    /// Subtract another expression from this one.
    pub fn sub(&self, other: &LinearExpr) -> Self {
        let mut result = self.clone();
        for (&var, &coeff) in &other.coeffs {
            *result.coeffs.entry(var).or_insert(0) -= coeff;
            if result.coeffs[&var] == 0 {
                result.coeffs.remove(&var);
            }
        }
        result.constant -= other.constant;
        result
    }
    
    /// Multiply by a scalar.
    pub fn scale(&self, s: Coeff) -> Self {
        if s == 0 {
            return Self::zero();
        }
        let mut result = self.clone();
        for coeff in result.coeffs.values_mut() {
            *coeff *= s;
        }
        result.constant *= s;
        result
    }
    
    /// Negate the expression.
    pub fn negate(&self) -> Self {
        self.scale(-1)
    }
    
    /// Evaluate with given variable values.
    pub fn evaluate(&self, values: &HashMap<VarId, Coeff>) -> Coeff {
        let mut sum = self.constant;
        for (&var, &coeff) in &self.coeffs {
            if let Some(&val) = values.get(&var) {
                sum += coeff * val;
            }
        }
        sum
    }
    
    /// Check if this is a constant expression.
    pub fn is_constant(&self) -> bool {
        self.coeffs.is_empty()
    }
    
    /// Get the single variable if this expression has exactly one variable.
    /// Returns (variable_id, coefficient).
    pub fn get_single_var(&self) -> Option<(VarId, Coeff)> {
        if self.coeffs.len() == 1 {
            self.coeffs.iter().next().map(|(&v, &c)| (v, c))
        } else {
            None
        }
    }
}

/// Constraint kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstraintKind {
    /// expr < 0
    Lt,
    /// expr ≤ 0
    Le,
    /// expr = 0
    Eq,
    /// expr ≥ 0
    Ge,
    /// expr > 0
    Gt,
    /// expr ≠ 0
    Ne,
}

impl ConstraintKind {
    /// Negate the constraint kind.
    pub fn negate(self) -> Self {
        match self {
            ConstraintKind::Lt => ConstraintKind::Ge,
            ConstraintKind::Le => ConstraintKind::Gt,
            ConstraintKind::Ge => ConstraintKind::Lt,
            ConstraintKind::Gt => ConstraintKind::Le,
            ConstraintKind::Eq => ConstraintKind::Ne,
            ConstraintKind::Ne => ConstraintKind::Eq,
        }
    }
}

/// A linear constraint.
#[derive(Debug, Clone)]
pub struct Constraint {
    /// Left-hand side expression (constraint is: expr ⋈ 0).
    pub expr: LinearExpr,
    /// Kind of constraint.
    pub kind: ConstraintKind,
    /// The literal associated with this constraint.
    pub literal: Literal,
    /// Decision level when asserted.
    pub level: u32,
}

/// Bound on a variable.
#[derive(Debug, Clone, Copy)]
pub struct Bound {
    /// The bound value.
    pub value: Coeff,
    /// Is the bound strict (< or >) or non-strict (≤ or ≥)?
    pub strict: bool,
    /// The literal that caused this bound.
    pub literal: Literal,
    /// Decision level.
    pub level: u32,
}

/// Variable bounds.
#[derive(Debug, Clone, Default)]
pub struct VarBounds {
    /// Lower bound.
    pub lower: Option<Bound>,
    /// Upper bound.
    pub upper: Option<Bound>,
}

impl VarBounds {
    /// Check if bounds are contradictory.
    pub fn is_contradictory(&self) -> bool {
        match (&self.lower, &self.upper) {
            (Some(lb), Some(ub)) => {
                if lb.value > ub.value {
                    return true;
                }
                if lb.value == ub.value && (lb.strict || ub.strict) {
                    return true;
                }
                false
            }
            _ => false,
        }
    }
}

/// LIA Theory Solver.
pub struct LiaSolver {
    /// Variable count.
    num_vars: u32,
    /// Variable bounds.
    bounds: HashMap<VarId, VarBounds>,
    /// Active constraints.
    constraints: Vec<Constraint>,
    /// Pending propagations.
    pending_propagations: Vec<TheoryPropagation>,
    /// Current decision level.
    current_level: u32,
    /// Explanation cache.
    explanations: HashMap<Literal, Vec<Literal>>,
}

impl LiaSolver {
    /// Create a new LIA solver.
    pub fn new() -> Self {
        LiaSolver {
            num_vars: 0,
            bounds: HashMap::new(),
            constraints: Vec::new(),
            pending_propagations: Vec::new(),
            current_level: 0,
            explanations: HashMap::new(),
        }
    }
    
    /// Declare a new variable.
    pub fn new_var(&mut self) -> VarId {
        let id = self.num_vars;
        self.num_vars += 1;
        id
    }
    
    /// Assert a constraint.
    pub fn assert_constraint(
        &mut self,
        expr: LinearExpr,
        kind: ConstraintKind,
        literal: Literal,
        level: u32,
    ) -> Result<(), TheoryConflict> {
        self.current_level = level;
        
        // Handle constant constraints
        if expr.is_constant() {
            let val = expr.constant;
            let satisfied = match kind {
                ConstraintKind::Lt => val < 0,
                ConstraintKind::Le => val <= 0,
                ConstraintKind::Eq => val == 0,
                ConstraintKind::Ge => val >= 0,
                ConstraintKind::Gt => val > 0,
                ConstraintKind::Ne => val != 0,
            };
            if !satisfied {
                return Err(TheoryConflict::new(vec![literal]));
            }
            return Ok(());
        }
        
        // Handle single-variable constraints (bound propagation)
        if let Some((var, coeff)) = expr.get_single_var() {
            let c = -expr.constant; // expr = coeff*x + constant ⋈ 0 => coeff*x ⋈ -constant
            
            // Adjust for coefficient sign
            let (kind, bound_val) = if coeff > 0 {
                (kind, c / coeff)
            } else {
                // Flip inequality when dividing by negative
                let flipped = match kind {
                    ConstraintKind::Lt => ConstraintKind::Gt,
                    ConstraintKind::Le => ConstraintKind::Ge,
                    ConstraintKind::Gt => ConstraintKind::Lt,
                    ConstraintKind::Ge => ConstraintKind::Le,
                    k => k,
                };
                (flipped, c / coeff)
            };
            
            let bounds = self.bounds.entry(var).or_default();
            
            match kind {
                ConstraintKind::Lt => {
                    // x < bound_val means upper bound of bound_val-1 (for integers)
                    let new_upper = Bound {
                        value: bound_val - 1,
                        strict: false,
                        literal,
                        level,
                    };
                    if let Some(ref mut ub) = bounds.upper {
                        if new_upper.value < ub.value {
                            *ub = new_upper;
                        }
                    } else {
                        bounds.upper = Some(new_upper);
                    }
                }
                ConstraintKind::Le => {
                    let new_upper = Bound {
                        value: bound_val,
                        strict: false,
                        literal,
                        level,
                    };
                    if let Some(ref mut ub) = bounds.upper {
                        if new_upper.value < ub.value {
                            *ub = new_upper;
                        }
                    } else {
                        bounds.upper = Some(new_upper);
                    }
                }
                ConstraintKind::Gt => {
                    // x > bound_val means lower bound of bound_val+1
                    let new_lower = Bound {
                        value: bound_val + 1,
                        strict: false,
                        literal,
                        level,
                    };
                    if let Some(ref mut lb) = bounds.lower {
                        if new_lower.value > lb.value {
                            *lb = new_lower;
                        }
                    } else {
                        bounds.lower = Some(new_lower);
                    }
                }
                ConstraintKind::Ge => {
                    let new_lower = Bound {
                        value: bound_val,
                        strict: false,
                        literal,
                        level,
                    };
                    if let Some(ref mut lb) = bounds.lower {
                        if new_lower.value > lb.value {
                            *lb = new_lower;
                        }
                    } else {
                        bounds.lower = Some(new_lower);
                    }
                }
                ConstraintKind::Eq => {
                    // x = c means both x >= c and x <= c
                    let bound = Bound {
                        value: bound_val,
                        strict: false,
                        literal,
                        level,
                    };
                    bounds.lower = Some(bound);
                    bounds.upper = Some(bound);
                }
                ConstraintKind::Ne => {
                    // Disequality - just store the constraint
                }
            }
            
            // Check for contradiction
            if bounds.is_contradictory() {
                let mut conflict_lits = Vec::new();
                if let Some(lb) = &bounds.lower {
                    conflict_lits.push(lb.literal);
                }
                if let Some(ub) = &bounds.upper {
                    if !conflict_lits.contains(&ub.literal) {
                        conflict_lits.push(ub.literal);
                    }
                }
                return Err(TheoryConflict::new(conflict_lits));
            }
        }
        
        self.constraints.push(Constraint {
            expr,
            kind,
            literal,
            level,
        });
        
        Ok(())
    }
    
    /// Check constraints for consistency.
    fn check_consistency(&self) -> Option<TheoryConflict> {
        // Check all variable bounds
        for (_var, bounds) in &self.bounds {
            if bounds.is_contradictory() {
                let mut conflict_lits = Vec::new();
                if let Some(lb) = &bounds.lower {
                    conflict_lits.push(lb.literal);
                }
                if let Some(ub) = &bounds.upper {
                    if !conflict_lits.contains(&ub.literal) {
                        conflict_lits.push(ub.literal);
                    }
                }
                return Some(TheoryConflict::new(conflict_lits));
            }
        }
        
        None
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
    
    fn assert_literal(&mut self, _lit: Literal, level: u32) -> Result<(), TheoryConflict> {
        // In a full implementation, we would map literals to constraints
        self.current_level = level;
        Ok(())
    }
    
    fn check(&mut self) -> TheoryResult {
        if let Some(conflict) = self.check_consistency() {
            TheoryResult::Conflict(conflict)
        } else {
            TheoryResult::Consistent
        }
    }
    
    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        std::mem::take(&mut self.pending_propagations)
    }
    
    fn explain(&self, lit: Literal) -> Vec<Literal> {
        self.explanations.get(&lit).cloned().unwrap_or_default()
    }
    
    fn backtrack(&mut self, level: u32) {
        // Remove constraints above the given level
        self.constraints.retain(|c| c.level <= level);
        
        // Rebuild bounds from remaining constraints
        self.bounds.clear();
        let constraints = std::mem::take(&mut self.constraints);
        for c in &constraints {
            if let Some((var, coeff)) = c.expr.get_single_var() {
                let bound_val = -c.expr.constant / coeff;
                let bounds = self.bounds.entry(var).or_default();
                
                match c.kind {
                    ConstraintKind::Le | ConstraintKind::Lt => {
                        let strict = c.kind == ConstraintKind::Lt;
                        let val = if strict { bound_val - 1 } else { bound_val };
                        if bounds.upper.is_none() || bounds.upper.as_ref().unwrap().value > val {
                            bounds.upper = Some(Bound {
                                value: val,
                                strict: false,
                                literal: c.literal,
                                level: c.level,
                            });
                        }
                    }
                    ConstraintKind::Ge | ConstraintKind::Gt => {
                        let strict = c.kind == ConstraintKind::Gt;
                        let val = if strict { bound_val + 1 } else { bound_val };
                        if bounds.lower.is_none() || bounds.lower.as_ref().unwrap().value < val {
                            bounds.lower = Some(Bound {
                                value: val,
                                strict: false,
                                literal: c.literal,
                                level: c.level,
                            });
                        }
                    }
                    ConstraintKind::Eq => {
                        bounds.lower = Some(Bound {
                            value: bound_val,
                            strict: false,
                            literal: c.literal,
                            level: c.level,
                        });
                        bounds.upper = Some(Bound {
                            value: bound_val,
                            strict: false,
                            literal: c.literal,
                            level: c.level,
                        });
                    }
                    ConstraintKind::Ne => {}
                }
            }
        }
        self.constraints = constraints;
        self.current_level = level;
    }
    
    fn reset(&mut self) {
        self.bounds.clear();
        self.constraints.clear();
        self.pending_propagations.clear();
        self.current_level = 0;
        self.explanations.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_linear_expr_add() {
        let x = LinearExpr::var(0);
        let y = LinearExpr::var(1);
        let sum = x.add(&y);
        
        assert_eq!(sum.coeffs.len(), 2);
        assert_eq!(sum.coeffs[&0], 1);
        assert_eq!(sum.coeffs[&1], 1);
    }

    #[test]
    fn test_linear_expr_scale() {
        let x = LinearExpr::var(0);
        let scaled = x.scale(3);
        
        assert_eq!(scaled.coeffs[&0], 3);
    }

    #[test]
    fn test_linear_expr_evaluate() {
        let mut expr = LinearExpr::var(0);
        expr = expr.add(&LinearExpr::var(1).scale(2));
        expr.constant = 5;
        
        let mut values = HashMap::new();
        values.insert(0, 3);
        values.insert(1, 4);
        
        // 3 + 2*4 + 5 = 16
        assert_eq!(expr.evaluate(&values), 16);
    }

    #[test]
    fn test_bound_propagation() {
        let mut solver = LiaSolver::new();
        let x = solver.new_var();
        
        // x >= 5
        let expr1 = LinearExpr::var(x).sub(&LinearExpr::constant(5));
        solver.assert_constraint(expr1, ConstraintKind::Ge, Literal::from_dimacs(1), 1).unwrap();
        
        // x <= 10
        let expr2 = LinearExpr::var(x).sub(&LinearExpr::constant(10));
        solver.assert_constraint(expr2, ConstraintKind::Le, Literal::from_dimacs(2), 1).unwrap();
        
        assert!(matches!(solver.check(), TheoryResult::Consistent));
    }

    #[test]
    fn test_bound_conflict() {
        let mut solver = LiaSolver::new();
        let x = solver.new_var();
        
        // x >= 10
        let expr1 = LinearExpr::var(x).sub(&LinearExpr::constant(10));
        solver.assert_constraint(expr1, ConstraintKind::Ge, Literal::from_dimacs(1), 1).unwrap();
        
        // x <= 5
        let expr2 = LinearExpr::var(x).sub(&LinearExpr::constant(5));
        let result = solver.assert_constraint(expr2, ConstraintKind::Le, Literal::from_dimacs(2), 1);
        
        assert!(result.is_err());
    }

    #[test]
    fn test_constant_constraint_sat() {
        let mut solver = LiaSolver::new();
        
        // 5 > 0 (always true)
        let expr = LinearExpr::constant(5);
        solver.assert_constraint(expr, ConstraintKind::Gt, Literal::from_dimacs(1), 1).unwrap();
        
        assert!(matches!(solver.check(), TheoryResult::Consistent));
    }

    #[test]
    fn test_constant_constraint_unsat() {
        let mut solver = LiaSolver::new();
        
        // 5 < 0 (always false)
        let expr = LinearExpr::constant(5);
        let result = solver.assert_constraint(expr, ConstraintKind::Lt, Literal::from_dimacs(1), 1);
        
        assert!(result.is_err());
    }

    #[test]
    fn test_equality_constraint() {
        let mut solver = LiaSolver::new();
        let x = solver.new_var();
        
        // x = 5
        let expr = LinearExpr::var(x).sub(&LinearExpr::constant(5));
        solver.assert_constraint(expr, ConstraintKind::Eq, Literal::from_dimacs(1), 1).unwrap();
        
        let bounds = solver.bounds.get(&x).unwrap();
        assert_eq!(bounds.lower.as_ref().unwrap().value, 5);
        assert_eq!(bounds.upper.as_ref().unwrap().value, 5);
    }

    #[test]
    fn test_backtrack() {
        let mut solver = LiaSolver::new();
        let x = solver.new_var();
        
        // Level 1: x >= 5
        let expr1 = LinearExpr::var(x).sub(&LinearExpr::constant(5));
        solver.assert_constraint(expr1, ConstraintKind::Ge, Literal::from_dimacs(1), 1).unwrap();
        
        // Level 2: x <= 3 (would conflict)
        let expr2 = LinearExpr::var(x).sub(&LinearExpr::constant(3));
        let _ = solver.assert_constraint(expr2, ConstraintKind::Le, Literal::from_dimacs(2), 2);
        
        // Backtrack to level 1
        solver.backtrack(1);
        
        // Should be consistent now
        assert!(matches!(solver.check(), TheoryResult::Consistent));
    }

    #[test]
    fn test_reset() {
        let mut solver = LiaSolver::new();
        let x = solver.new_var();
        
        let expr = LinearExpr::var(x).sub(&LinearExpr::constant(5));
        solver.assert_constraint(expr, ConstraintKind::Ge, Literal::from_dimacs(1), 1).unwrap();
        
        solver.reset();
        
        assert!(solver.constraints.is_empty());
        assert!(solver.bounds.is_empty());
    }
}
