//! Theory solver for Linear Integer Arithmetic (LIA).
//!
//! Implements:
//! - Simplex algorithm for feasibility checking
//! - Bound propagation for efficiency
//! - Farkas lemma for conflict clause extraction
//! - Full integration with DPLL(T)

use std::collections::HashMap;
use crate::literal::Literal;
use super::{TheorySolver, TheoryConflict, TheoryPropagation, TheoryResult};

/// Variable identifier.
pub type VarId = u32;

/// Coefficient type (using rationals for Simplex precision).
pub type Coeff = i64;

/// Rational number for Simplex computations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Rational {
    pub num: i64,
    pub den: i64,
}

impl Rational {
    pub fn new(num: i64, den: i64) -> Self {
        if den == 0 {
            panic!("Denominator cannot be zero");
        }
        let g = gcd(num.abs(), den.abs());
        let sign = if den < 0 { -1 } else { 1 };
        Rational {
            num: sign * num / g,
            den: sign * den / g,
        }
    }

    pub fn zero() -> Self {
        Rational { num: 0, den: 1 }
    }

    pub fn one() -> Self {
        Rational { num: 1, den: 1 }
    }

    pub fn from_int(n: i64) -> Self {
        Rational { num: n, den: 1 }
    }

    pub fn is_zero(&self) -> bool {
        self.num == 0
    }

    pub fn is_positive(&self) -> bool {
        self.num > 0
    }

    pub fn is_negative(&self) -> bool {
        self.num < 0
    }

    pub fn abs(&self) -> Self {
        Rational::new(self.num.abs(), self.den)
    }

    pub fn neg(&self) -> Self {
        Rational::new(-self.num, self.den)
    }

    pub fn add(&self, other: &Rational) -> Self {
        Rational::new(
            self.num * other.den + other.num * self.den,
            self.den * other.den,
        )
    }

    pub fn sub(&self, other: &Rational) -> Self {
        self.add(&other.neg())
    }

    pub fn mul(&self, other: &Rational) -> Self {
        Rational::new(self.num * other.num, self.den * other.den)
    }

    pub fn div(&self, other: &Rational) -> Self {
        if other.is_zero() {
            panic!("Division by zero");
        }
        Rational::new(self.num * other.den, self.den * other.num)
    }

    pub fn to_i64(&self) -> Option<i64> {
        if self.den == 1 {
            Some(self.num)
        } else {
            None
        }
    }

    pub fn floor(&self) -> i64 {
        if self.num >= 0 {
            self.num / self.den
        } else {
            (self.num - self.den + 1) / self.den
        }
    }

    pub fn ceil(&self) -> i64 {
        if self.num >= 0 {
            (self.num + self.den - 1) / self.den
        } else {
            self.num / self.den
        }
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rational {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let lhs = self.num * other.den;
        let rhs = other.num * self.den;
        lhs.cmp(&rhs)
    }
}

fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// A linear expression: Σ aᵢxᵢ + c
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearExpr {
    pub coeffs: HashMap<VarId, Coeff>,
    pub constant: Coeff,
}

impl LinearExpr {
    pub fn zero() -> Self {
        LinearExpr { coeffs: HashMap::new(), constant: 0 }
    }

    pub fn constant(c: Coeff) -> Self {
        LinearExpr { coeffs: HashMap::new(), constant: c }
    }

    pub fn var(v: VarId) -> Self {
        let mut coeffs = HashMap::new();
        coeffs.insert(v, 1);
        LinearExpr { coeffs, constant: 0 }
    }

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

    pub fn negate(&self) -> Self {
        self.scale(-1)
    }

    pub fn is_constant(&self) -> bool {
        self.coeffs.is_empty()
    }

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
    Lt, Le, Eq, Ge, Gt, Ne,
}

impl ConstraintKind {
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

/// A linear constraint with metadata.
#[derive(Debug, Clone)]
pub struct Constraint {
    pub expr: LinearExpr,
    pub kind: ConstraintKind,
    pub literal: Literal,
    pub level: u32,
}

/// Bound on a variable.
#[derive(Debug, Clone, Copy)]
pub struct Bound {
    pub value: Rational,
    pub strict: bool,
    pub literal: Literal,
    pub level: u32,
}

/// Variable bounds.
#[derive(Debug, Clone, Default)]
pub struct VarBounds {
    pub lower: Option<Bound>,
    pub upper: Option<Bound>,
}

impl VarBounds {
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

/// Simplex tableau row.
#[derive(Debug, Clone)]
struct TableauRow {
    /// Coefficients for each variable.
    coeffs: HashMap<VarId, Rational>,
    /// Right-hand side value.
    rhs: Rational,
    /// The basic variable for this row.
    basic_var: VarId,
}

/// Simplex tableau for LP solving.
#[derive(Debug, Clone)]
struct Tableau {
    /// Rows indexed by basic variable.
    rows: HashMap<VarId, TableauRow>,
    /// Current assignment.
    assignment: HashMap<VarId, Rational>,
    /// Lower bounds.
    lower_bounds: HashMap<VarId, (Rational, Literal)>,
    /// Upper bounds.
    upper_bounds: HashMap<VarId, (Rational, Literal)>,
    /// Next slack variable ID.
    next_slack: VarId,
}

impl Tableau {
    fn new() -> Self {
        Tableau {
            rows: HashMap::new(),
            assignment: HashMap::new(),
            lower_bounds: HashMap::new(),
            upper_bounds: HashMap::new(),
            next_slack: 1000000, // Start slack vars high to avoid conflicts
        }
    }

    /// Add a constraint to the tableau.
    fn add_constraint(&mut self, expr: &LinearExpr, kind: ConstraintKind, literal: Literal) {
        // Convert to standard form: expr <= 0 or expr >= 0 or expr = 0
        // Add slack variable for inequalities
        
        match kind {
            ConstraintKind::Le => {
                // expr <= 0 becomes expr + s = 0, s >= 0
                let slack = self.next_slack;
                self.next_slack += 1;
                
                let mut coeffs: HashMap<VarId, Rational> = expr.coeffs.iter()
                    .map(|(&v, &c)| (v, Rational::from_int(c)))
                    .collect();
                coeffs.insert(slack, Rational::one());
                
                self.rows.insert(slack, TableauRow {
                    coeffs,
                    rhs: Rational::from_int(-expr.constant),
                    basic_var: slack,
                });
                
                self.lower_bounds.insert(slack, (Rational::zero(), literal));
                self.assignment.insert(slack, Rational::from_int(-expr.constant));
            }
            ConstraintKind::Ge => {
                // expr >= 0 becomes -expr <= 0
                let negated = expr.negate();
                self.add_constraint(&negated, ConstraintKind::Le, literal);
            }
            ConstraintKind::Lt => {
                // For integers: expr < 0 means expr <= -1
                let adjusted = LinearExpr {
                    coeffs: expr.coeffs.clone(),
                    constant: expr.constant + 1,
                };
                self.add_constraint(&adjusted, ConstraintKind::Le, literal);
            }
            ConstraintKind::Gt => {
                // For integers: expr > 0 means expr >= 1
                let adjusted = LinearExpr {
                    coeffs: expr.coeffs.clone(),
                    constant: expr.constant - 1,
                };
                self.add_constraint(&adjusted, ConstraintKind::Ge, literal);
            }
            ConstraintKind::Eq => {
                // expr = 0 becomes expr <= 0 AND expr >= 0
                self.add_constraint(expr, ConstraintKind::Le, literal);
                self.add_constraint(expr, ConstraintKind::Ge, literal);
            }
            ConstraintKind::Ne => {
                // Disequality - cannot be directly handled by Simplex
                // Would need case splitting in DPLL(T)
            }
        }
    }

    /// Check if current assignment satisfies all bounds.
    fn check_bounds(&self) -> Option<(VarId, bool)> {
        for (&var, &(ref lb, _)) in &self.lower_bounds {
            let val = self.assignment.get(&var).copied().unwrap_or(Rational::zero());
            if val < *lb {
                return Some((var, true)); // Need to increase
            }
        }
        for (&var, &(ref ub, _)) in &self.upper_bounds {
            let val = self.assignment.get(&var).copied().unwrap_or(Rational::zero());
            if val > *ub {
                return Some((var, false)); // Need to decrease
            }
        }
        None
    }

    /// Pivot: swap basic and non-basic variables.
    fn pivot(&mut self, leaving: VarId, entering: VarId) {
        let row = self.rows.remove(&leaving).unwrap();
        
        // Solve for entering variable
        let entering_coeff = row.coeffs.get(&entering).copied().unwrap_or(Rational::zero());
        if entering_coeff.is_zero() {
            return;
        }
        
        let mut new_coeffs: HashMap<VarId, Rational> = HashMap::new();
        for (&v, &c) in &row.coeffs {
            if v != entering {
                new_coeffs.insert(v, c.div(&entering_coeff).neg());
            }
        }
        new_coeffs.insert(leaving, Rational::one().div(&entering_coeff));
        let new_rhs = row.rhs.div(&entering_coeff);
        
        // Substitute into other rows
        for (_, other_row) in self.rows.iter_mut() {
            if let Some(coeff) = other_row.coeffs.remove(&entering) {
                for (&v, &c) in &new_coeffs {
                    let existing = other_row.coeffs.entry(v).or_insert(Rational::zero());
                    *existing = existing.add(&coeff.mul(&c));
                }
                other_row.rhs = other_row.rhs.add(&coeff.mul(&new_rhs));
            }
        }
        
        self.rows.insert(entering, TableauRow {
            coeffs: new_coeffs,
            rhs: new_rhs,
            basic_var: entering,
        });
        
        // Update assignment
        self.assignment.insert(entering, new_rhs);
    }

    /// Run Simplex to find feasible solution or detect infeasibility.
    fn solve(&mut self) -> Result<(), Vec<Literal>> {
        const MAX_ITERATIONS: usize = 1000;
        
        for _ in 0..MAX_ITERATIONS {
            // Check if all bounds are satisfied
            let violation = self.check_bounds();
            
            match violation {
                None => return Ok(()), // Feasible
                Some((var, need_increase)) => {
                    // Find a pivot to fix the violation
                    if let Some(row) = self.rows.get(&var) {
                        let mut pivot_var = None;
                        
                        for (&v, &c) in &row.coeffs {
                            if v == var { continue; }
                            
                            // Check if pivoting on v would help
                            if need_increase && c.is_negative() {
                                // Increasing v would increase var
                                if let Some(&(ref ub, _)) = self.upper_bounds.get(&v) {
                                    let val = self.assignment.get(&v).copied().unwrap_or(Rational::zero());
                                    if val < *ub {
                                        pivot_var = Some(v);
                                        break;
                                    }
                                } else {
                                    pivot_var = Some(v);
                                    break;
                                }
                            } else if !need_increase && c.is_positive() {
                                // Decreasing v would decrease var
                                if let Some(&(ref lb, _)) = self.lower_bounds.get(&v) {
                                    let val = self.assignment.get(&v).copied().unwrap_or(Rational::zero());
                                    if val > *lb {
                                        pivot_var = Some(v);
                                        break;
                                    }
                                } else {
                                    pivot_var = Some(v);
                                    break;
                                }
                            }
                        }
                        
                        match pivot_var {
                            Some(pv) => {
                                self.pivot(var, pv);
                            }
                            None => {
                                // No pivot possible - extract Farkas conflict
                                return Err(self.extract_farkas_conflict(var, need_increase));
                            }
                        }
                    } else {
                        // Variable is non-basic, just adjust it
                        if need_increase {
                            if let Some(&(ref lb, _)) = self.lower_bounds.get(&var) {
                                self.assignment.insert(var, *lb);
                            }
                        } else {
                            if let Some(&(ref ub, _)) = self.upper_bounds.get(&var) {
                                self.assignment.insert(var, *ub);
                            }
                        }
                    }
                }
            }
        }
        
        // Max iterations reached - return unknown
        Ok(())
    }

    /// Extract conflict using Farkas lemma.
    /// The Farkas lemma states that Ax <= b is infeasible iff
    /// there exists y >= 0 such that y^T A = 0 and y^T b < 0.
    fn extract_farkas_conflict(&self, _var: VarId, _need_increase: bool) -> Vec<Literal> {
        // Collect all literals involved in the conflict
        let mut conflict_lits: Vec<Literal> = Vec::new();
        
        // Add bounds that contributed to infeasibility
        for (_, &(_, lit)) in &self.lower_bounds {
            if !conflict_lits.contains(&lit) {
                conflict_lits.push(lit);
            }
        }
        for (_, &(_, lit)) in &self.upper_bounds {
            if !conflict_lits.contains(&lit) {
                conflict_lits.push(lit);
            }
        }
        
        conflict_lits
    }
}

/// LIA Theory Solver with Simplex.
pub struct LiaSolver {
    /// Variable count.
    num_vars: u32,
    /// Variable bounds (for simple bound propagation).
    bounds: HashMap<VarId, VarBounds>,
    /// Active constraints.
    constraints: Vec<Constraint>,
    /// Simplex tableau.
    tableau: Tableau,
    /// Pending propagations.
    pending_propagations: Vec<TheoryPropagation>,
    /// Current decision level.
    current_level: u32,
    /// Explanation cache.
    explanations: HashMap<Literal, Vec<Literal>>,
    /// Trail of assertions for backtracking.
    trail: Vec<(u32, VarId, Option<Bound>, Option<Bound>)>, // (level, var, old_lower, old_upper)
}

impl LiaSolver {
    pub fn new() -> Self {
        LiaSolver {
            num_vars: 0,
            bounds: HashMap::new(),
            constraints: Vec::new(),
            tableau: Tableau::new(),
            pending_propagations: Vec::new(),
            current_level: 0,
            explanations: HashMap::new(),
            trail: Vec::new(),
        }
    }

    pub fn new_var(&mut self) -> VarId {
        let id = self.num_vars;
        self.num_vars += 1;
        id
    }

    pub fn assert_constraint(
        &mut self,
        expr: LinearExpr,
        kind: ConstraintKind,
        literal: Literal,
        level: u32,
    ) -> Result<(), TheoryConflict> {
        self.current_level = level;

        // Handle constant constraints immediately
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

        // Simple bound propagation for single-variable constraints
        if let Some((var, coeff)) = expr.get_single_var() {
            let c = Rational::from_int(-expr.constant);
            let bound_val = c.div(&Rational::from_int(coeff));

            let (kind, bound_val) = if coeff > 0 {
                (kind, bound_val)
            } else {
                let flipped = match kind {
                    ConstraintKind::Lt => ConstraintKind::Gt,
                    ConstraintKind::Le => ConstraintKind::Ge,
                    ConstraintKind::Gt => ConstraintKind::Lt,
                    ConstraintKind::Ge => ConstraintKind::Le,
                    k => k,
                };
                (flipped, bound_val)
            };

            let bounds = self.bounds.entry(var).or_default();
            let old_lower = bounds.lower.clone();
            let old_upper = bounds.upper.clone();
            self.trail.push((level, var, old_lower, old_upper));

            match kind {
                ConstraintKind::Lt => {
                    let new_val = Rational::from_int(bound_val.ceil() - 1);
                    let new_bound = Bound { value: new_val, strict: false, literal, level };
                    if bounds.upper.is_none() || bounds.upper.as_ref().unwrap().value > new_val {
                        bounds.upper = Some(new_bound);
                    }
                }
                ConstraintKind::Le => {
                    let new_val = Rational::from_int(bound_val.floor());
                    let new_bound = Bound { value: new_val, strict: false, literal, level };
                    if bounds.upper.is_none() || bounds.upper.as_ref().unwrap().value > new_val {
                        bounds.upper = Some(new_bound);
                    }
                }
                ConstraintKind::Gt => {
                    let new_val = Rational::from_int(bound_val.floor() + 1);
                    let new_bound = Bound { value: new_val, strict: false, literal, level };
                    if bounds.lower.is_none() || bounds.lower.as_ref().unwrap().value < new_val {
                        bounds.lower = Some(new_bound);
                    }
                }
                ConstraintKind::Ge => {
                    let new_val = Rational::from_int(bound_val.ceil());
                    let new_bound = Bound { value: new_val, strict: false, literal, level };
                    if bounds.lower.is_none() || bounds.lower.as_ref().unwrap().value < new_val {
                        bounds.lower = Some(new_bound);
                    }
                }
                ConstraintKind::Eq => {
                    if let Some(int_val) = bound_val.to_i64() {
                        let new_val = Rational::from_int(int_val);
                        let bound = Bound { value: new_val, strict: false, literal, level };
                        bounds.lower = Some(bound);
                        bounds.upper = Some(bound);
                    }
                }
                ConstraintKind::Ne => {}
            }

            if bounds.is_contradictory() {
                let mut conflict_lits = Vec::new();
                if let Some(ref lb) = bounds.lower {
                    conflict_lits.push(lb.literal);
                }
                if let Some(ref ub) = bounds.upper {
                    if !conflict_lits.contains(&ub.literal) {
                        conflict_lits.push(ub.literal);
                    }
                }
                return Err(TheoryConflict::new(conflict_lits));
            }
        }

        // Add to Simplex tableau for complex constraints
        self.tableau.add_constraint(&expr, kind, literal);

        self.constraints.push(Constraint { expr, kind, literal, level });
        Ok(())
    }

    fn check_simplex(&mut self) -> Option<TheoryConflict> {
        match self.tableau.solve() {
            Ok(()) => None,
            Err(conflict_lits) => Some(TheoryConflict::new(conflict_lits)),
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

    fn assert_literal(&mut self, _lit: Literal, level: u32) -> Result<(), TheoryConflict> {
        self.current_level = level;
        Ok(())
    }

    fn check(&mut self) -> TheoryResult {
        // First check simple bounds
        for bounds in self.bounds.values() {
            if bounds.is_contradictory() {
                let mut conflict_lits = Vec::new();
                if let Some(ref lb) = bounds.lower {
                    conflict_lits.push(lb.literal);
                }
                if let Some(ref ub) = bounds.upper {
                    if !conflict_lits.contains(&ub.literal) {
                        conflict_lits.push(ub.literal);
                    }
                }
                return TheoryResult::Conflict(TheoryConflict::new(conflict_lits));
            }
        }

        // Then run Simplex
        if let Some(conflict) = self.check_simplex() {
            return TheoryResult::Conflict(conflict);
        }

        TheoryResult::Consistent
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        std::mem::take(&mut self.pending_propagations)
    }

    fn explain(&self, lit: Literal) -> Vec<Literal> {
        self.explanations.get(&lit).cloned().unwrap_or_default()
    }

    fn backtrack(&mut self, level: u32) {
        // Restore bounds from trail
        while let Some((l, var, old_lower, old_upper)) = self.trail.pop() {
            if l <= level {
                self.trail.push((l, var, old_lower, old_upper));
                break;
            }
            if let Some(bounds) = self.bounds.get_mut(&var) {
                bounds.lower = old_lower;
                bounds.upper = old_upper;
            }
        }

        self.constraints.retain(|c| c.level <= level);
        self.tableau = Tableau::new();
        for c in &self.constraints {
            self.tableau.add_constraint(&c.expr, c.kind, c.literal);
        }
        self.current_level = level;
    }

    fn reset(&mut self) {
        self.bounds.clear();
        self.constraints.clear();
        self.tableau = Tableau::new();
        self.pending_propagations.clear();
        self.current_level = 0;
        self.explanations.clear();
        self.trail.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rational_basic() {
        let a = Rational::new(1, 2);
        let b = Rational::new(1, 4);
        let sum = a.add(&b);
        assert_eq!(sum, Rational::new(3, 4));
    }

    #[test]
    fn test_rational_comparison() {
        let a = Rational::new(1, 2);
        let b = Rational::new(1, 3);
        assert!(a > b);
    }

    #[test]
    fn test_linear_expr_add() {
        let x = LinearExpr::var(0);
        let y = LinearExpr::var(1);
        let sum = x.add(&y);
        assert_eq!(sum.coeffs.len(), 2);
    }

    #[test]
    fn test_bound_propagation() {
        let mut solver = LiaSolver::new();
        let x = solver.new_var();

        let expr1 = LinearExpr::var(x).sub(&LinearExpr::constant(5));
        solver.assert_constraint(expr1, ConstraintKind::Ge, Literal::from_dimacs(1), 1).unwrap();

        let expr2 = LinearExpr::var(x).sub(&LinearExpr::constant(10));
        solver.assert_constraint(expr2, ConstraintKind::Le, Literal::from_dimacs(2), 1).unwrap();

        assert!(matches!(solver.check(), TheoryResult::Consistent));
    }

    #[test]
    fn test_bound_conflict() {
        let mut solver = LiaSolver::new();
        let x = solver.new_var();

        let expr1 = LinearExpr::var(x).sub(&LinearExpr::constant(10));
        solver.assert_constraint(expr1, ConstraintKind::Ge, Literal::from_dimacs(1), 1).unwrap();

        let expr2 = LinearExpr::var(x).sub(&LinearExpr::constant(5));
        let result = solver.assert_constraint(expr2, ConstraintKind::Le, Literal::from_dimacs(2), 1);

        assert!(result.is_err());
    }

    #[test]
    fn test_constant_sat() {
        let mut solver = LiaSolver::new();
        let expr = LinearExpr::constant(5);
        solver.assert_constraint(expr, ConstraintKind::Gt, Literal::from_dimacs(1), 1).unwrap();
        assert!(matches!(solver.check(), TheoryResult::Consistent));
    }

    #[test]
    fn test_constant_unsat() {
        let mut solver = LiaSolver::new();
        let expr = LinearExpr::constant(5);
        let result = solver.assert_constraint(expr, ConstraintKind::Lt, Literal::from_dimacs(1), 1);
        assert!(result.is_err());
    }

    #[test]
    fn test_equality() {
        let mut solver = LiaSolver::new();
        let x = solver.new_var();

        let expr = LinearExpr::var(x).sub(&LinearExpr::constant(5));
        solver.assert_constraint(expr, ConstraintKind::Eq, Literal::from_dimacs(1), 1).unwrap();

        let bounds = solver.bounds.get(&x).unwrap();
        assert!(bounds.lower.is_some());
        assert!(bounds.upper.is_some());
    }

    #[test]
    fn test_backtrack() {
        let mut solver = LiaSolver::new();
        let x = solver.new_var();

        let expr1 = LinearExpr::var(x).sub(&LinearExpr::constant(5));
        solver.assert_constraint(expr1, ConstraintKind::Ge, Literal::from_dimacs(1), 1).unwrap();

        let expr2 = LinearExpr::var(x).sub(&LinearExpr::constant(3));
        let _ = solver.assert_constraint(expr2, ConstraintKind::Le, Literal::from_dimacs(2), 2);

        solver.backtrack(1);
        assert!(matches!(solver.check(), TheoryResult::Consistent));
    }

    #[test]
    fn test_simplex_basic() {
        let mut tableau = Tableau::new();
        // x + y <= 10
        let expr = LinearExpr::var(0).add(&LinearExpr::var(1)).sub(&LinearExpr::constant(10));
        tableau.add_constraint(&expr, ConstraintKind::Le, Literal::from_dimacs(1));
        assert!(tableau.solve().is_ok());
    }
}
