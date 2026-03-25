//! Bitvector Theory Solver
//!
//! Implements fixed-width bitvector arithmetic via bit-blasting
//! and word-level propagation.

use super::{TheoryConflict, TheoryPropagation, TheoryResult, TheorySolver};
use crate::literal::Literal;
use std::collections::HashMap;

/// Bitvector identifier
pub type BvId = u32;

/// A bitvector value (up to 64 bits)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BitVec {
    /// The value
    pub value: u64,
    /// Width in bits
    pub width: u32,
}

impl BitVec {
    /// Create a new bitvector
    pub fn new(value: u64, width: u32) -> Self {
        assert!(width > 0 && width <= 64, "Width must be 1-64 bits");
        let mask = if width == 64 { u64::MAX } else { (1u64 << width) - 1 };
        BitVec { value: value & mask, width }
    }

    /// Get bit at position
    pub fn bit(&self, pos: u32) -> bool {
        assert!(pos < self.width);
        (self.value >> pos) & 1 == 1
    }

    /// Set bit at position
    pub fn set_bit(&mut self, pos: u32, val: bool) {
        assert!(pos < self.width);
        if val {
            self.value |= 1 << pos;
        } else {
            self.value &= !(1 << pos);
        }
    }

    /// Bitwise NOT
    pub fn not(&self) -> BitVec {
        let mask = if self.width == 64 { u64::MAX } else { (1u64 << self.width) - 1 };
        BitVec::new(!self.value & mask, self.width)
    }

    /// Bitwise AND
    pub fn and(&self, other: &BitVec) -> BitVec {
        assert_eq!(self.width, other.width);
        BitVec::new(self.value & other.value, self.width)
    }

    /// Bitwise OR
    pub fn or(&self, other: &BitVec) -> BitVec {
        assert_eq!(self.width, other.width);
        BitVec::new(self.value | other.value, self.width)
    }

    /// Bitwise XOR
    pub fn xor(&self, other: &BitVec) -> BitVec {
        assert_eq!(self.width, other.width);
        BitVec::new(self.value ^ other.value, self.width)
    }

    /// Addition (wrapping)
    pub fn add(&self, other: &BitVec) -> BitVec {
        assert_eq!(self.width, other.width);
        BitVec::new(self.value.wrapping_add(other.value), self.width)
    }

    /// Subtraction (wrapping)
    pub fn sub(&self, other: &BitVec) -> BitVec {
        assert_eq!(self.width, other.width);
        BitVec::new(self.value.wrapping_sub(other.value), self.width)
    }

    /// Multiplication (wrapping)
    pub fn mul(&self, other: &BitVec) -> BitVec {
        assert_eq!(self.width, other.width);
        BitVec::new(self.value.wrapping_mul(other.value), self.width)
    }

    /// Unsigned division
    pub fn udiv(&self, other: &BitVec) -> BitVec {
        assert_eq!(self.width, other.width);
        if other.value == 0 {
            // Division by zero returns all 1s (common convention)
            let mask = if self.width == 64 { u64::MAX } else { (1u64 << self.width) - 1 };
            BitVec::new(mask, self.width)
        } else {
            BitVec::new(self.value / other.value, self.width)
        }
    }

    /// Unsigned remainder
    pub fn urem(&self, other: &BitVec) -> BitVec {
        assert_eq!(self.width, other.width);
        if other.value == 0 {
            BitVec::new(self.value, self.width)
        } else {
            BitVec::new(self.value % other.value, self.width)
        }
    }

    /// Left shift
    pub fn shl(&self, amount: u32) -> BitVec {
        if amount >= self.width {
            BitVec::new(0, self.width)
        } else {
            BitVec::new(self.value << amount, self.width)
        }
    }

    /// Logical right shift
    pub fn lshr(&self, amount: u32) -> BitVec {
        if amount >= self.width {
            BitVec::new(0, self.width)
        } else {
            BitVec::new(self.value >> amount, self.width)
        }
    }

    /// Arithmetic right shift
    pub fn ashr(&self, amount: u32) -> BitVec {
        if amount >= self.width {
            // Sign extend
            if self.bit(self.width - 1) {
                let mask = if self.width == 64 { u64::MAX } else { (1u64 << self.width) - 1 };
                BitVec::new(mask, self.width)
            } else {
                BitVec::new(0, self.width)
            }
        } else {
            let sign_bit = self.bit(self.width - 1);
            let shifted = self.value >> amount;
            if sign_bit {
                // Fill with 1s
                let fill = if self.width == 64 {
                    u64::MAX << (self.width - amount)
                } else {
                    ((1u64 << amount) - 1) << (self.width - amount)
                };
                BitVec::new(shifted | fill, self.width)
            } else {
                BitVec::new(shifted, self.width)
            }
        }
    }

    /// Concatenation (self is high bits, other is low bits)
    pub fn concat(&self, other: &BitVec) -> BitVec {
        let new_width = self.width + other.width;
        assert!(new_width <= 64);
        BitVec::new((self.value << other.width) | other.value, new_width)
    }

    /// Extract bits [high:low]
    pub fn extract(&self, high: u32, low: u32) -> BitVec {
        assert!(high >= low && high < self.width);
        let new_width = high - low + 1;
        let mask = if new_width == 64 { u64::MAX } else { (1u64 << new_width) - 1 };
        BitVec::new((self.value >> low) & mask, new_width)
    }

    /// Zero extension
    pub fn zext(&self, new_width: u32) -> BitVec {
        assert!(new_width >= self.width && new_width <= 64);
        BitVec::new(self.value, new_width)
    }

    /// Sign extension
    pub fn sext(&self, new_width: u32) -> BitVec {
        assert!(new_width >= self.width && new_width <= 64);
        if self.bit(self.width - 1) {
            // Sign bit is 1, extend with 1s
            let extension_bits = new_width - self.width;
            let mask = if extension_bits == 64 {
                u64::MAX
            } else {
                ((1u64 << extension_bits) - 1) << self.width
            };
            BitVec::new(self.value | mask, new_width)
        } else {
            BitVec::new(self.value, new_width)
        }
    }

    /// Unsigned less than
    pub fn ult(&self, other: &BitVec) -> bool {
        assert_eq!(self.width, other.width);
        self.value < other.value
    }

    /// Unsigned less than or equal
    pub fn ule(&self, other: &BitVec) -> bool {
        assert_eq!(self.width, other.width);
        self.value <= other.value
    }

    /// Signed less than
    pub fn slt(&self, other: &BitVec) -> bool {
        assert_eq!(self.width, other.width);
        let a = self.to_signed();
        let b = other.to_signed();
        a < b
    }

    /// Signed less than or equal
    pub fn sle(&self, other: &BitVec) -> bool {
        assert_eq!(self.width, other.width);
        let a = self.to_signed();
        let b = other.to_signed();
        a <= b
    }

    /// Convert to signed integer
    fn to_signed(&self) -> i64 {
        if self.bit(self.width - 1) {
            // Negative number - sign extend
            let mask = if self.width == 64 {
                0
            } else {
                u64::MAX << self.width
            };
            (self.value | mask) as i64
        } else {
            self.value as i64
        }
    }
}

/// A bitvector term
#[derive(Debug, Clone)]
pub enum BvTerm {
    /// Constant value
    Const(BitVec),
    /// Variable with given width
    Var { id: BvId, width: u32 },
    /// Unary operation
    Unary { op: UnaryOp, arg: Box<BvTerm> },
    /// Binary operation
    Binary { op: BinaryOp, lhs: Box<BvTerm>, rhs: Box<BvTerm> },
    /// Extract bits
    Extract { term: Box<BvTerm>, high: u32, low: u32 },
    /// Concatenation
    Concat { high: Box<BvTerm>, low: Box<BvTerm> },
    /// Zero extension
    ZeroExt { term: Box<BvTerm>, new_width: u32 },
    /// Sign extension
    SignExt { term: Box<BvTerm>, new_width: u32 },
}

/// Unary bitvector operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Neg,
}

/// Binary bitvector operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    And, Or, Xor,
    Add, Sub, Mul,
    UDiv, URem,
    Shl, LShr, AShr,
}

impl BvTerm {
    /// Get the width of this term
    pub fn width(&self) -> u32 {
        match self {
            BvTerm::Const(bv) => bv.width,
            BvTerm::Var { width, .. } => *width,
            BvTerm::Unary { arg, .. } => arg.width(),
            BvTerm::Binary { lhs, .. } => lhs.width(),
            BvTerm::Extract { high, low, .. } => high - low + 1,
            BvTerm::Concat { high, low } => high.width() + low.width(),
            BvTerm::ZeroExt { new_width, .. } => *new_width,
            BvTerm::SignExt { new_width, .. } => *new_width,
        }
    }

    /// Evaluate the term given variable assignments
    pub fn evaluate(&self, assignments: &HashMap<BvId, BitVec>) -> Option<BitVec> {
        match self {
            BvTerm::Const(bv) => Some(*bv),
            BvTerm::Var { id, width } => {
                assignments.get(id).copied().or_else(|| {
                    // Return None if variable not assigned
                    None
                }).filter(|v| v.width == *width)
            }
            BvTerm::Unary { op, arg } => {
                let a = arg.evaluate(assignments)?;
                Some(match op {
                    UnaryOp::Not => a.not(),
                    UnaryOp::Neg => BitVec::new(0, a.width).sub(&a),
                })
            }
            BvTerm::Binary { op, lhs, rhs } => {
                let l = lhs.evaluate(assignments)?;
                let r = rhs.evaluate(assignments)?;
                Some(match op {
                    BinaryOp::And => l.and(&r),
                    BinaryOp::Or => l.or(&r),
                    BinaryOp::Xor => l.xor(&r),
                    BinaryOp::Add => l.add(&r),
                    BinaryOp::Sub => l.sub(&r),
                    BinaryOp::Mul => l.mul(&r),
                    BinaryOp::UDiv => l.udiv(&r),
                    BinaryOp::URem => l.urem(&r),
                    BinaryOp::Shl => l.shl(r.value as u32),
                    BinaryOp::LShr => l.lshr(r.value as u32),
                    BinaryOp::AShr => l.ashr(r.value as u32),
                })
            }
            BvTerm::Extract { term, high, low } => {
                let t = term.evaluate(assignments)?;
                Some(t.extract(*high, *low))
            }
            BvTerm::Concat { high, low } => {
                let h = high.evaluate(assignments)?;
                let l = low.evaluate(assignments)?;
                Some(h.concat(&l))
            }
            BvTerm::ZeroExt { term, new_width } => {
                let t = term.evaluate(assignments)?;
                Some(t.zext(*new_width))
            }
            BvTerm::SignExt { term, new_width } => {
                let t = term.evaluate(assignments)?;
                Some(t.sext(*new_width))
            }
        }
    }
}

/// Bitvector constraint
#[derive(Debug, Clone)]
pub struct BvConstraint {
    /// Constraint kind
    pub kind: BvConstraintKind,
    /// SAT literal that implies this
    pub literal: Literal,
    /// Decision level
    pub level: u32,
}

/// Kinds of bitvector constraints
#[derive(Debug, Clone)]
pub enum BvConstraintKind {
    /// term1 = term2
    Eq(BvTerm, BvTerm),
    /// term1 != term2
    Ne(BvTerm, BvTerm),
    /// term1 <u term2 (unsigned)
    Ult(BvTerm, BvTerm),
    /// term1 <=u term2 (unsigned)
    Ule(BvTerm, BvTerm),
    /// term1 <s term2 (signed)
    Slt(BvTerm, BvTerm),
    /// term1 <=s term2 (signed)
    Sle(BvTerm, BvTerm),
}

/// Bitvector Theory Solver
pub struct BvSolver {
    /// Variable assignments (partial or complete)
    assignments: HashMap<BvId, BitVec>,
    /// Asserted constraints
    constraints: Vec<BvConstraint>,
    /// Decision level
    level: u32,
    /// Trail for backtracking
    trail: Vec<(u32, BvId)>,
    /// Propagated literals
    propagated: HashMap<Literal, Vec<Literal>>,
}

impl BvSolver {
    /// Create a new bitvector solver
    pub fn new() -> Self {
        BvSolver {
            assignments: HashMap::new(),
            constraints: Vec::new(),
            level: 0,
            trail: Vec::new(),
            propagated: HashMap::new(),
        }
    }

    /// Assign a value to a variable
    pub fn assign(&mut self, var: BvId, value: BitVec) {
        self.assignments.insert(var, value);
        self.trail.push((self.level, var));
    }

    /// Get a variable's value
    pub fn get_value(&self, var: BvId) -> Option<BitVec> {
        self.assignments.get(&var).copied()
    }

    /// Assert a constraint
    pub fn assert_constraint(&mut self, constraint: BvConstraint) -> TheoryResult<()> {
        // Check if constraint is immediately violated
        let violated = match &constraint.kind {
            BvConstraintKind::Eq(lhs, rhs) => {
                match (lhs.evaluate(&self.assignments), rhs.evaluate(&self.assignments)) {
                    (Some(l), Some(r)) => l != r,
                    _ => false,
                }
            }
            BvConstraintKind::Ne(lhs, rhs) => {
                match (lhs.evaluate(&self.assignments), rhs.evaluate(&self.assignments)) {
                    (Some(l), Some(r)) => l == r,
                    _ => false,
                }
            }
            BvConstraintKind::Ult(lhs, rhs) => {
                match (lhs.evaluate(&self.assignments), rhs.evaluate(&self.assignments)) {
                    (Some(l), Some(r)) => !l.ult(&r),
                    _ => false,
                }
            }
            BvConstraintKind::Ule(lhs, rhs) => {
                match (lhs.evaluate(&self.assignments), rhs.evaluate(&self.assignments)) {
                    (Some(l), Some(r)) => !l.ule(&r),
                    _ => false,
                }
            }
            BvConstraintKind::Slt(lhs, rhs) => {
                match (lhs.evaluate(&self.assignments), rhs.evaluate(&self.assignments)) {
                    (Some(l), Some(r)) => !l.slt(&r),
                    _ => false,
                }
            }
            BvConstraintKind::Sle(lhs, rhs) => {
                match (lhs.evaluate(&self.assignments), rhs.evaluate(&self.assignments)) {
                    (Some(l), Some(r)) => !l.sle(&r),
                    _ => false,
                }
            }
        };

        if violated {
            return Err(TheoryConflict::new(vec![constraint.literal]));
        }

        self.constraints.push(constraint);
        Ok(())
    }
}

impl Default for BvSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl TheorySolver for BvSolver {
    fn name(&self) -> &'static str {
        "BV"
    }

    fn assert_literal(&mut self, _lit: Literal) -> TheoryResult<()> {
        Ok(())
    }

    fn check(&mut self) -> TheoryResult<()> {
        // Check all constraints
        for constraint in &self.constraints {
            let violated = match &constraint.kind {
                BvConstraintKind::Eq(lhs, rhs) => {
                    match (lhs.evaluate(&self.assignments), rhs.evaluate(&self.assignments)) {
                        (Some(l), Some(r)) => l != r,
                        _ => false,
                    }
                }
                BvConstraintKind::Ne(lhs, rhs) => {
                    match (lhs.evaluate(&self.assignments), rhs.evaluate(&self.assignments)) {
                        (Some(l), Some(r)) => l == r,
                        _ => false,
                    }
                }
                BvConstraintKind::Ult(lhs, rhs) => {
                    match (lhs.evaluate(&self.assignments), rhs.evaluate(&self.assignments)) {
                        (Some(l), Some(r)) => !l.ult(&r),
                        _ => false,
                    }
                }
                BvConstraintKind::Ule(lhs, rhs) => {
                    match (lhs.evaluate(&self.assignments), rhs.evaluate(&self.assignments)) {
                        (Some(l), Some(r)) => !l.ule(&r),
                        _ => false,
                    }
                }
                BvConstraintKind::Slt(lhs, rhs) => {
                    match (lhs.evaluate(&self.assignments), rhs.evaluate(&self.assignments)) {
                        (Some(l), Some(r)) => !l.slt(&r),
                        _ => false,
                    }
                }
                BvConstraintKind::Sle(lhs, rhs) => {
                    match (lhs.evaluate(&self.assignments), rhs.evaluate(&self.assignments)) {
                        (Some(l), Some(r)) => !l.sle(&r),
                        _ => false,
                    }
                }
            };

            if violated {
                return Err(TheoryConflict::new(vec![constraint.literal]));
            }
        }
        Ok(())
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        Vec::new()
    }

    fn explain(&self, lit: Literal) -> Vec<Literal> {
        self.propagated.get(&lit).cloned().unwrap_or_default()
    }

    fn backtrack(&mut self, level: u32) {
        self.level = level;
        
        // Remove assignments from higher levels
        while let Some(&(assign_level, var)) = self.trail.last() {
            if assign_level <= level {
                break;
            }
            self.assignments.remove(&var);
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
        self.assignments.clear();
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
    fn test_bitvec_basic() {
        let bv = BitVec::new(0xFF, 8);
        assert_eq!(bv.value, 255);
        assert_eq!(bv.width, 8);
    }

    #[test]
    fn test_bitvec_mask() {
        // Value should be masked to width
        let bv = BitVec::new(0xFFFF, 8);
        assert_eq!(bv.value, 0xFF);
    }

    #[test]
    fn test_bitvec_bit_access() {
        let bv = BitVec::new(0b10101010, 8);
        assert!(!bv.bit(0));
        assert!(bv.bit(1));
        assert!(!bv.bit(2));
        assert!(bv.bit(3));
    }

    #[test]
    fn test_bitvec_not() {
        let bv = BitVec::new(0b10101010, 8);
        let result = bv.not();
        assert_eq!(result.value, 0b01010101);
    }

    #[test]
    fn test_bitvec_and() {
        let a = BitVec::new(0b11110000, 8);
        let b = BitVec::new(0b10101010, 8);
        let result = a.and(&b);
        assert_eq!(result.value, 0b10100000);
    }

    #[test]
    fn test_bitvec_add() {
        let a = BitVec::new(100, 8);
        let b = BitVec::new(50, 8);
        let result = a.add(&b);
        assert_eq!(result.value, 150);
    }

    #[test]
    fn test_bitvec_add_overflow() {
        let a = BitVec::new(200, 8);
        let b = BitVec::new(100, 8);
        let result = a.add(&b);
        // 200 + 100 = 300, but wraps to 44 in 8 bits
        assert_eq!(result.value, 44);
    }

    #[test]
    fn test_bitvec_concat() {
        let high = BitVec::new(0xAB, 8);
        let low = BitVec::new(0xCD, 8);
        let result = high.concat(&low);
        assert_eq!(result.value, 0xABCD);
        assert_eq!(result.width, 16);
    }

    #[test]
    fn test_bitvec_extract() {
        let bv = BitVec::new(0xABCD, 16);
        let result = bv.extract(11, 4);
        assert_eq!(result.value, 0xBC);
        assert_eq!(result.width, 8);
    }

    #[test]
    fn test_bitvec_sext() {
        // Negative number (sign bit = 1)
        let bv = BitVec::new(0x80, 8); // -128 in signed 8-bit
        let result = bv.sext(16);
        assert_eq!(result.value, 0xFF80);
        assert_eq!(result.width, 16);
    }

    #[test]
    fn test_bitvec_zext() {
        let bv = BitVec::new(0x80, 8);
        let result = bv.zext(16);
        assert_eq!(result.value, 0x0080);
        assert_eq!(result.width, 16);
    }

    #[test]
    fn test_bitvec_ult() {
        let a = BitVec::new(5, 8);
        let b = BitVec::new(10, 8);
        assert!(a.ult(&b));
        assert!(!b.ult(&a));
    }

    #[test]
    fn test_bitvec_slt() {
        // 0xFF as signed 8-bit is -1
        let a = BitVec::new(0xFF, 8);
        let b = BitVec::new(1, 8);
        // -1 < 1 signed
        assert!(a.slt(&b));
        // But 255 > 1 unsigned
        assert!(!a.ult(&b));
    }

    #[test]
    fn test_bv_solver_assign() {
        let mut solver = BvSolver::new();
        
        let value = BitVec::new(42, 8);
        solver.assign(1, value);
        
        assert_eq!(solver.get_value(1), Some(value));
    }

    #[test]
    fn test_bv_solver_constraint_eq_ok() {
        let mut solver = BvSolver::new();
        
        solver.assign(1, BitVec::new(42, 8));
        solver.assign(2, BitVec::new(42, 8));
        
        let constraint = BvConstraint {
            kind: BvConstraintKind::Eq(
                BvTerm::Var { id: 1, width: 8 },
                BvTerm::Var { id: 2, width: 8 },
            ),
            literal: lit(1, true),
            level: 0,
        };
        
        assert!(solver.assert_constraint(constraint).is_ok());
    }

    #[test]
    fn test_bv_solver_constraint_eq_conflict() {
        let mut solver = BvSolver::new();
        
        solver.assign(1, BitVec::new(42, 8));
        solver.assign(2, BitVec::new(43, 8));
        
        let constraint = BvConstraint {
            kind: BvConstraintKind::Eq(
                BvTerm::Var { id: 1, width: 8 },
                BvTerm::Var { id: 2, width: 8 },
            ),
            literal: lit(1, true),
            level: 0,
        };
        
        assert!(solver.assert_constraint(constraint).is_err());
    }

    #[test]
    fn test_bv_solver_backtrack() {
        let mut solver = BvSolver::new();
        
        solver.assign(1, BitVec::new(1, 8));
        solver.push_level();
        solver.assign(2, BitVec::new(2, 8));
        
        assert!(solver.get_value(1).is_some());
        assert!(solver.get_value(2).is_some());
        
        solver.backtrack(0);
        
        assert!(solver.get_value(1).is_some());
        assert!(solver.get_value(2).is_none());
    }

    #[test]
    fn test_bv_term_evaluate() {
        let mut assignments = HashMap::new();
        assignments.insert(1, BitVec::new(10, 8));
        assignments.insert(2, BitVec::new(20, 8));
        
        // x + y
        let term = BvTerm::Binary {
            op: BinaryOp::Add,
            lhs: Box::new(BvTerm::Var { id: 1, width: 8 }),
            rhs: Box::new(BvTerm::Var { id: 2, width: 8 }),
        };
        
        let result = term.evaluate(&assignments).unwrap();
        assert_eq!(result.value, 30);
    }
}
