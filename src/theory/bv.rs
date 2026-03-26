//! Theory solver for Bitvectors (BV).
//!
//! Handles fixed-width bitvector operations:
//! - Bitwise: and, or, xor, not
//! - Arithmetic: add, sub, mul, div, rem
//! - Shifts: shl, lshr, ashr
//! - Comparisons: ult, ule, ugt, uge, slt, sle, sgt, sge
//! - Extract, concat, extend

use std::fmt;
use std::ops::{BitAnd, BitOr, BitXor, Not, Add, Sub, Mul, Shl, Shr};
use crate::literal::Literal;
use super::{TheorySolver, TheoryConflict, TheoryPropagation, TheoryResult};

/// A fixed-width bitvector value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BitVec {
    /// The value (stored in lower bits).
    pub value: u64,
    /// Width in bits.
    pub width: u32,
}

impl BitVec {
    /// Create a new bitvector with the given value and width.
    pub fn new(value: u64, width: u32) -> Self {
        assert!(width > 0 && width <= 64, "Width must be 1-64");
        let mask = if width == 64 { u64::MAX } else { (1u64 << width) - 1 };
        BitVec {
            value: value & mask,
            width,
        }
    }
    
    /// Create a zero bitvector.
    pub fn zero(width: u32) -> Self {
        BitVec::new(0, width)
    }
    
    /// Create a bitvector with all ones.
    pub fn ones(width: u32) -> Self {
        let mask = if width == 64 { u64::MAX } else { (1u64 << width) - 1 };
        BitVec::new(mask, width)
    }
    
    /// Get the mask for this width.
    fn mask(&self) -> u64 {
        if self.width == 64 { u64::MAX } else { (1u64 << self.width) - 1 }
    }
    
    /// Normalize value to fit width.
    fn normalize(&self) -> u64 {
        self.value & self.mask()
    }
    
    /// Unsigned less than.
    pub fn ult(&self, other: &BitVec) -> bool {
        assert_eq!(self.width, other.width);
        self.normalize() < other.normalize()
    }
    
    /// Unsigned less than or equal.
    pub fn ule(&self, other: &BitVec) -> bool {
        assert_eq!(self.width, other.width);
        self.normalize() <= other.normalize()
    }
    
    /// Unsigned greater than.
    pub fn ugt(&self, other: &BitVec) -> bool {
        assert_eq!(self.width, other.width);
        self.normalize() > other.normalize()
    }
    
    /// Unsigned greater than or equal.
    pub fn uge(&self, other: &BitVec) -> bool {
        assert_eq!(self.width, other.width);
        self.normalize() >= other.normalize()
    }
    
    /// Convert to signed value.
    fn to_signed(&self) -> i64 {
        let val = self.normalize();
        let sign_bit = 1u64 << (self.width - 1);
        if val & sign_bit != 0 {
            // Negative - sign extend
            let mask = if self.width == 64 { 0 } else { !((1u64 << self.width) - 1) };
            (val | mask) as i64
        } else {
            val as i64
        }
    }
    
    /// Signed less than.
    pub fn slt(&self, other: &BitVec) -> bool {
        assert_eq!(self.width, other.width);
        self.to_signed() < other.to_signed()
    }
    
    /// Signed less than or equal.
    pub fn sle(&self, other: &BitVec) -> bool {
        assert_eq!(self.width, other.width);
        self.to_signed() <= other.to_signed()
    }
    
    /// Signed greater than.
    pub fn sgt(&self, other: &BitVec) -> bool {
        assert_eq!(self.width, other.width);
        self.to_signed() > other.to_signed()
    }
    
    /// Signed greater than or equal.
    pub fn sge(&self, other: &BitVec) -> bool {
        assert_eq!(self.width, other.width);
        self.to_signed() >= other.to_signed()
    }
    
    /// Unsigned division.
    pub fn udiv(&self, other: &BitVec) -> BitVec {
        assert_eq!(self.width, other.width);
        if other.value == 0 {
            BitVec::ones(self.width) // Division by zero returns all ones
        } else {
            BitVec::new(self.normalize() / other.normalize(), self.width)
        }
    }
    
    /// Unsigned remainder.
    pub fn urem(&self, other: &BitVec) -> BitVec {
        assert_eq!(self.width, other.width);
        if other.value == 0 {
            *self // Remainder by zero returns dividend
        } else {
            BitVec::new(self.normalize() % other.normalize(), self.width)
        }
    }
    
    /// Signed division.
    pub fn sdiv(&self, other: &BitVec) -> BitVec {
        assert_eq!(self.width, other.width);
        if other.value == 0 {
            BitVec::ones(self.width)
        } else {
            let result = self.to_signed() / other.to_signed();
            BitVec::new(result as u64, self.width)
        }
    }
    
    /// Signed remainder.
    pub fn srem(&self, other: &BitVec) -> BitVec {
        assert_eq!(self.width, other.width);
        if other.value == 0 {
            *self
        } else {
            let result = self.to_signed() % other.to_signed();
            BitVec::new(result as u64, self.width)
        }
    }
    
    /// Logical shift left.
    pub fn shl_bv(&self, amount: &BitVec) -> BitVec {
        let shift = amount.value.min(self.width as u64) as u32;
        BitVec::new(self.value << shift, self.width)
    }
    
    /// Logical shift right.
    pub fn lshr(&self, amount: &BitVec) -> BitVec {
        let shift = amount.value.min(self.width as u64) as u32;
        BitVec::new(self.normalize() >> shift, self.width)
    }
    
    /// Arithmetic shift right.
    pub fn ashr(&self, amount: &BitVec) -> BitVec {
        let shift = amount.value.min(self.width as u64) as u32;
        let result = self.to_signed() >> shift;
        BitVec::new(result as u64, self.width)
    }
    
    /// Concatenate two bitvectors.
    pub fn concat(&self, other: &BitVec) -> BitVec {
        let new_width = self.width + other.width;
        assert!(new_width <= 64, "Concatenation exceeds 64 bits");
        let result = (self.normalize() << other.width) | other.normalize();
        BitVec::new(result, new_width)
    }
    
    /// Extract bits [high:low] (inclusive).
    pub fn extract(&self, high: u32, low: u32) -> BitVec {
        assert!(high >= low && high < self.width);
        let new_width = high - low + 1;
        let result = (self.normalize() >> low) & ((1u64 << new_width) - 1);
        BitVec::new(result, new_width)
    }
    
    /// Zero extend to a wider width.
    pub fn zero_extend(&self, extra_bits: u32) -> BitVec {
        BitVec::new(self.normalize(), self.width + extra_bits)
    }
    
    /// Sign extend to a wider width.
    pub fn sign_extend(&self, extra_bits: u32) -> BitVec {
        let new_width = self.width + extra_bits;
        let result = self.to_signed() as u64;
        BitVec::new(result, new_width)
    }
}

impl fmt::Display for BitVec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#x{:0width$x}", self.value, width = (self.width as usize + 3) / 4)
    }
}

impl Not for BitVec {
    type Output = BitVec;
    fn not(self) -> BitVec {
        BitVec::new(!self.value, self.width)
    }
}

impl BitAnd for BitVec {
    type Output = BitVec;
    fn bitand(self, rhs: BitVec) -> BitVec {
        assert_eq!(self.width, rhs.width);
        BitVec::new(self.value & rhs.value, self.width)
    }
}

impl BitOr for BitVec {
    type Output = BitVec;
    fn bitor(self, rhs: BitVec) -> BitVec {
        assert_eq!(self.width, rhs.width);
        BitVec::new(self.value | rhs.value, self.width)
    }
}

impl BitXor for BitVec {
    type Output = BitVec;
    fn bitxor(self, rhs: BitVec) -> BitVec {
        assert_eq!(self.width, rhs.width);
        BitVec::new(self.value ^ rhs.value, self.width)
    }
}

impl Add for BitVec {
    type Output = BitVec;
    fn add(self, rhs: BitVec) -> BitVec {
        assert_eq!(self.width, rhs.width);
        BitVec::new(self.value.wrapping_add(rhs.value), self.width)
    }
}

impl Sub for BitVec {
    type Output = BitVec;
    fn sub(self, rhs: BitVec) -> BitVec {
        assert_eq!(self.width, rhs.width);
        BitVec::new(self.value.wrapping_sub(rhs.value), self.width)
    }
}

impl Mul for BitVec {
    type Output = BitVec;
    fn mul(self, rhs: BitVec) -> BitVec {
        assert_eq!(self.width, rhs.width);
        BitVec::new(self.value.wrapping_mul(rhs.value), self.width)
    }
}

impl Shl<u32> for BitVec {
    type Output = BitVec;
    fn shl(self, rhs: u32) -> BitVec {
        BitVec::new(self.value << rhs.min(self.width), self.width)
    }
}

impl Shr<u32> for BitVec {
    type Output = BitVec;
    fn shr(self, rhs: u32) -> BitVec {
        BitVec::new(self.normalize() >> rhs.min(self.width), self.width)
    }
}

/// Variable identifier.
pub type BvVarId = u32;

/// Bitvector term.
#[derive(Debug, Clone)]
pub enum BvTerm {
    /// Constant.
    Const(BitVec),
    /// Variable.
    Var(BvVarId, u32), // (id, width)
    /// Bitwise NOT.
    Not(Box<BvTerm>),
    /// Bitwise AND.
    And(Box<BvTerm>, Box<BvTerm>),
    /// Bitwise OR.
    Or(Box<BvTerm>, Box<BvTerm>),
    /// Bitwise XOR.
    Xor(Box<BvTerm>, Box<BvTerm>),
    /// Addition.
    Add(Box<BvTerm>, Box<BvTerm>),
    /// Subtraction.
    Sub(Box<BvTerm>, Box<BvTerm>),
    /// Multiplication.
    Mul(Box<BvTerm>, Box<BvTerm>),
    /// Unsigned division.
    Udiv(Box<BvTerm>, Box<BvTerm>),
    /// Signed division.
    Sdiv(Box<BvTerm>, Box<BvTerm>),
    /// Unsigned remainder.
    Urem(Box<BvTerm>, Box<BvTerm>),
    /// Signed remainder.
    Srem(Box<BvTerm>, Box<BvTerm>),
    /// Shift left.
    Shl(Box<BvTerm>, Box<BvTerm>),
    /// Logical shift right.
    Lshr(Box<BvTerm>, Box<BvTerm>),
    /// Arithmetic shift right.
    Ashr(Box<BvTerm>, Box<BvTerm>),
    /// Concatenation.
    Concat(Box<BvTerm>, Box<BvTerm>),
    /// Extraction.
    Extract(u32, u32, Box<BvTerm>), // (high, low, term)
    /// Zero extension.
    ZeroExtend(u32, Box<BvTerm>),
    /// Sign extension.
    SignExtend(u32, Box<BvTerm>),
}

impl BvTerm {
    /// Get the width of this term.
    pub fn width(&self) -> u32 {
        match self {
            BvTerm::Const(bv) => bv.width,
            BvTerm::Var(_, w) => *w,
            BvTerm::Not(t) => t.width(),
            BvTerm::And(a, _) | BvTerm::Or(a, _) | BvTerm::Xor(a, _) => a.width(),
            BvTerm::Add(a, _) | BvTerm::Sub(a, _) | BvTerm::Mul(a, _) => a.width(),
            BvTerm::Udiv(a, _) | BvTerm::Sdiv(a, _) => a.width(),
            BvTerm::Urem(a, _) | BvTerm::Srem(a, _) => a.width(),
            BvTerm::Shl(a, _) | BvTerm::Lshr(a, _) | BvTerm::Ashr(a, _) => a.width(),
            BvTerm::Concat(a, b) => a.width() + b.width(),
            BvTerm::Extract(high, low, _) => high - low + 1,
            BvTerm::ZeroExtend(extra, t) | BvTerm::SignExtend(extra, t) => t.width() + extra,
        }
    }
    
    /// Evaluate the term with given variable values.
    pub fn evaluate(&self, env: &std::collections::HashMap<BvVarId, BitVec>) -> Option<BitVec> {
        match self {
            BvTerm::Const(bv) => Some(*bv),
            BvTerm::Var(id, w) => env.get(id).copied().or(Some(BitVec::zero(*w))),
            BvTerm::Not(t) => t.evaluate(env).map(|v| !v),
            BvTerm::And(a, b) => {
                let va = a.evaluate(env)?;
                let vb = b.evaluate(env)?;
                Some(va & vb)
            }
            BvTerm::Or(a, b) => {
                let va = a.evaluate(env)?;
                let vb = b.evaluate(env)?;
                Some(va | vb)
            }
            BvTerm::Xor(a, b) => {
                let va = a.evaluate(env)?;
                let vb = b.evaluate(env)?;
                Some(va ^ vb)
            }
            BvTerm::Add(a, b) => {
                let va = a.evaluate(env)?;
                let vb = b.evaluate(env)?;
                Some(va + vb)
            }
            BvTerm::Sub(a, b) => {
                let va = a.evaluate(env)?;
                let vb = b.evaluate(env)?;
                Some(va - vb)
            }
            BvTerm::Mul(a, b) => {
                let va = a.evaluate(env)?;
                let vb = b.evaluate(env)?;
                Some(va * vb)
            }
            BvTerm::Udiv(a, b) => {
                let va = a.evaluate(env)?;
                let vb = b.evaluate(env)?;
                Some(va.udiv(&vb))
            }
            BvTerm::Sdiv(a, b) => {
                let va = a.evaluate(env)?;
                let vb = b.evaluate(env)?;
                Some(va.sdiv(&vb))
            }
            BvTerm::Urem(a, b) => {
                let va = a.evaluate(env)?;
                let vb = b.evaluate(env)?;
                Some(va.urem(&vb))
            }
            BvTerm::Srem(a, b) => {
                let va = a.evaluate(env)?;
                let vb = b.evaluate(env)?;
                Some(va.srem(&vb))
            }
            BvTerm::Shl(a, b) => {
                let va = a.evaluate(env)?;
                let vb = b.evaluate(env)?;
                Some(va.shl_bv(&vb))
            }
            BvTerm::Lshr(a, b) => {
                let va = a.evaluate(env)?;
                let vb = b.evaluate(env)?;
                Some(va.lshr(&vb))
            }
            BvTerm::Ashr(a, b) => {
                let va = a.evaluate(env)?;
                let vb = b.evaluate(env)?;
                Some(va.ashr(&vb))
            }
            BvTerm::Concat(a, b) => {
                let va = a.evaluate(env)?;
                let vb = b.evaluate(env)?;
                Some(va.concat(&vb))
            }
            BvTerm::Extract(high, low, t) => {
                let v = t.evaluate(env)?;
                Some(v.extract(*high, *low))
            }
            BvTerm::ZeroExtend(extra, t) => {
                let v = t.evaluate(env)?;
                Some(v.zero_extend(*extra))
            }
            BvTerm::SignExtend(extra, t) => {
                let v = t.evaluate(env)?;
                Some(v.sign_extend(*extra))
            }
        }
    }
}

/// Bitvector constraint.
#[derive(Debug, Clone)]
pub struct BvConstraint {
    /// Left-hand side term.
    pub lhs: BvTerm,
    /// Right-hand side term.
    pub rhs: BvTerm,
    /// Is equality (true) or disequality (false)?
    pub is_equality: bool,
    /// The literal that caused this constraint.
    pub literal: Literal,
    /// Decision level.
    pub level: u32,
}

/// BV Theory Solver.
pub struct BvSolver {
    /// Constraints.
    constraints: Vec<BvConstraint>,
    /// Variable assignments.
    assignments: std::collections::HashMap<BvVarId, BitVec>,
    /// Pending propagations.
    pending_propagations: Vec<TheoryPropagation>,
    /// Current decision level.
    current_level: u32,
    /// Explanation cache.
    explanations: std::collections::HashMap<Literal, Vec<Literal>>,
}

impl BvSolver {
    /// Create a new BV solver.
    pub fn new() -> Self {
        BvSolver {
            constraints: Vec::new(),
            assignments: std::collections::HashMap::new(),
            pending_propagations: Vec::new(),
            current_level: 0,
            explanations: std::collections::HashMap::new(),
        }
    }
    
    /// Assert an equality constraint.
    pub fn assert_equality(
        &mut self,
        lhs: BvTerm,
        rhs: BvTerm,
        literal: Literal,
        level: u32,
    ) -> Result<(), TheoryConflict> {
        self.current_level = level;
        self.constraints.push(BvConstraint {
            lhs,
            rhs,
            is_equality: true,
            literal,
            level,
        });
        Ok(())
    }
    
    /// Assert a disequality constraint.
    pub fn assert_disequality(
        &mut self,
        lhs: BvTerm,
        rhs: BvTerm,
        literal: Literal,
        level: u32,
    ) -> Result<(), TheoryConflict> {
        self.current_level = level;
        self.constraints.push(BvConstraint {
            lhs,
            rhs,
            is_equality: false,
            literal,
            level,
        });
        Ok(())
    }
    
    /// Check constraints for consistency.
    fn check_consistency(&self) -> Option<TheoryConflict> {
        // Only check constraints where both sides are fully determined
        // (i.e., no unassigned variables)
        for constraint in &self.constraints {
            // Only evaluate if both sides are constants or assigned variables
            let lhs_concrete = self.is_concrete(&constraint.lhs);
            let rhs_concrete = self.is_concrete(&constraint.rhs);
            
            if lhs_concrete && rhs_concrete {
                let lhs_val = constraint.lhs.evaluate(&self.assignments);
                let rhs_val = constraint.rhs.evaluate(&self.assignments);
                
                if let (Some(l), Some(r)) = (lhs_val, rhs_val) {
                    if constraint.is_equality {
                        if l != r {
                            return Some(TheoryConflict::new(vec![constraint.literal]));
                        }
                    } else {
                        if l == r {
                            return Some(TheoryConflict::new(vec![constraint.literal]));
                        }
                    }
                }
            }
        }
        None
    }
    
    /// Check if a term is fully concrete (no unassigned variables).
    fn is_concrete(&self, term: &BvTerm) -> bool {
        match term {
            BvTerm::Const(_) => true,
            BvTerm::Var(id, _) => self.assignments.contains_key(id),
            BvTerm::Not(t) => self.is_concrete(t),
            BvTerm::And(a, b) | BvTerm::Or(a, b) | BvTerm::Xor(a, b) |
            BvTerm::Add(a, b) | BvTerm::Sub(a, b) | BvTerm::Mul(a, b) |
            BvTerm::Udiv(a, b) | BvTerm::Sdiv(a, b) |
            BvTerm::Urem(a, b) | BvTerm::Srem(a, b) |
            BvTerm::Shl(a, b) | BvTerm::Lshr(a, b) | BvTerm::Ashr(a, b) |
            BvTerm::Concat(a, b) => self.is_concrete(a) && self.is_concrete(b),
            BvTerm::Extract(_, _, t) |
            BvTerm::ZeroExtend(_, t) |
            BvTerm::SignExtend(_, t) => self.is_concrete(t),
        }
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
    
    fn assert_literal(&mut self, _lit: Literal, level: u32) -> Result<(), TheoryConflict> {
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
        self.constraints.retain(|c| c.level <= level);
        self.current_level = level;
    }
    
    fn reset(&mut self) {
        self.constraints.clear();
        self.assignments.clear();
        self.pending_propagations.clear();
        self.current_level = 0;
        self.explanations.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bitvec_new() {
        let bv = BitVec::new(255, 8);
        assert_eq!(bv.value, 255);
        assert_eq!(bv.width, 8);
    }

    #[test]
    fn test_bitvec_overflow() {
        let bv = BitVec::new(256, 8);
        assert_eq!(bv.value, 0); // 256 mod 256 = 0
    }

    #[test]
    fn test_bitvec_not() {
        let bv = BitVec::new(0x0F, 8);
        let result = !bv;
        assert_eq!(result.value, 0xF0);
    }

    #[test]
    fn test_bitvec_and() {
        let a = BitVec::new(0xFF, 8);
        let b = BitVec::new(0x0F, 8);
        assert_eq!((a & b).value, 0x0F);
    }

    #[test]
    fn test_bitvec_or() {
        let a = BitVec::new(0xF0, 8);
        let b = BitVec::new(0x0F, 8);
        assert_eq!((a | b).value, 0xFF);
    }

    #[test]
    fn test_bitvec_xor() {
        let a = BitVec::new(0xFF, 8);
        let b = BitVec::new(0x0F, 8);
        assert_eq!((a ^ b).value, 0xF0);
    }

    #[test]
    fn test_bitvec_add() {
        let a = BitVec::new(100, 8);
        let b = BitVec::new(50, 8);
        assert_eq!((a + b).value, 150);
    }

    #[test]
    fn test_bitvec_add_overflow() {
        let a = BitVec::new(200, 8);
        let b = BitVec::new(100, 8);
        assert_eq!((a + b).value, 44); // 300 mod 256 = 44
    }

    #[test]
    fn test_bitvec_sub() {
        let a = BitVec::new(100, 8);
        let b = BitVec::new(50, 8);
        assert_eq!((a - b).value, 50);
    }

    #[test]
    fn test_bitvec_mul() {
        let a = BitVec::new(10, 8);
        let b = BitVec::new(5, 8);
        assert_eq!((a * b).value, 50);
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
        let a = BitVec::new(0xFF, 8); // -1 as signed
        let b = BitVec::new(0, 8);
        assert!(a.slt(&b)); // -1 < 0
    }

    #[test]
    fn test_bitvec_concat() {
        let a = BitVec::new(0xAB, 8);
        let b = BitVec::new(0xCD, 8);
        let result = a.concat(&b);
        assert_eq!(result.value, 0xABCD);
        assert_eq!(result.width, 16);
    }

    #[test]
    fn test_bitvec_extract() {
        let bv = BitVec::new(0xABCD, 16);
        let high = bv.extract(15, 8);
        let low = bv.extract(7, 0);
        assert_eq!(high.value, 0xAB);
        assert_eq!(low.value, 0xCD);
    }

    #[test]
    fn test_bitvec_zero_extend() {
        let bv = BitVec::new(0xFF, 8);
        let extended = bv.zero_extend(8);
        assert_eq!(extended.value, 0xFF);
        assert_eq!(extended.width, 16);
    }

    #[test]
    fn test_bitvec_sign_extend() {
        let bv = BitVec::new(0xFF, 8); // -1
        let extended = bv.sign_extend(8);
        assert_eq!(extended.value, 0xFFFF);
        assert_eq!(extended.width, 16);
    }

    #[test]
    fn test_bv_term_evaluate() {
        use std::collections::HashMap;
        
        let term = BvTerm::Add(
            Box::new(BvTerm::Const(BitVec::new(10, 8))),
            Box::new(BvTerm::Const(BitVec::new(5, 8))),
        );
        
        let result = term.evaluate(&HashMap::new()).unwrap();
        assert_eq!(result.value, 15);
    }

    #[test]
    fn test_bv_solver_consistent() {
        let mut solver = BvSolver::new();
        
        // Assert x = 5
        solver.assert_equality(
            BvTerm::Var(0, 8),
            BvTerm::Const(BitVec::new(5, 8)),
            Literal::from_dimacs(1),
            1,
        ).unwrap();
        
        assert!(matches!(solver.check(), TheoryResult::Consistent));
    }

    #[test]
    fn test_bv_solver_backtrack() {
        let mut solver = BvSolver::new();
        
        solver.assert_equality(
            BvTerm::Var(0, 8),
            BvTerm::Const(BitVec::new(5, 8)),
            Literal::from_dimacs(1),
            1,
        ).unwrap();
        
        solver.assert_equality(
            BvTerm::Var(0, 8),
            BvTerm::Const(BitVec::new(10, 8)),
            Literal::from_dimacs(2),
            2,
        ).unwrap();
        
        solver.backtrack(1);
        
        assert_eq!(solver.constraints.len(), 1);
    }
}
