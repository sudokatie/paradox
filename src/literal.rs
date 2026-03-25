//! Literal and Variable types for SAT solving.
//!
//! A Variable is a 1-indexed integer (DIMACS convention).
//! A Literal is a variable with a polarity (positive or negative).

use std::fmt;

/// A propositional variable (1-indexed for DIMACS compatibility).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Variable(pub u32);

impl Variable {
    /// Create a new variable with the given index (1-indexed).
    pub fn new(index: u32) -> Self {
        debug_assert!(index > 0, "Variable index must be positive (1-indexed)");
        Variable(index)
    }

    /// Get the 1-indexed variable number.
    pub fn index(&self) -> u32 {
        self.0
    }

    /// Convert to 0-indexed for array access.
    pub fn to_index(&self) -> usize {
        (self.0 - 1) as usize
    }

    /// Create from 0-indexed array index.
    pub fn from_index(idx: usize) -> Self {
        Variable((idx + 1) as u32)
    }
}

impl fmt::Debug for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x{}", self.0)
    }
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x{}", self.0)
    }
}

/// A literal is a variable with polarity.
///
/// Internally represented as 2*var + polarity for efficient indexing.
/// - Positive literal for var n: 2*(n-1) + 1 = 2n - 1
/// - Negative literal for var n: 2*(n-1) + 0 = 2n - 2
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Literal(u32);

impl Literal {
    /// Create a new literal.
    pub fn new(var: Variable, positive: bool) -> Self {
        let code = 2 * (var.0 - 1) + if positive { 1 } else { 0 };
        Literal(code)
    }

    /// Create a positive literal for a variable.
    pub fn positive(var: Variable) -> Self {
        Literal::new(var, true)
    }

    /// Create a negative literal for a variable.
    pub fn negative(var: Variable) -> Self {
        Literal::new(var, false)
    }

    /// Parse from DIMACS format (positive = variable, negative = negated).
    pub fn from_dimacs(value: i32) -> Self {
        debug_assert!(value != 0, "DIMACS literal cannot be 0");
        let var = Variable::new(value.unsigned_abs());
        let positive = value > 0;
        Literal::new(var, positive)
    }

    /// Convert to DIMACS format.
    pub fn to_dimacs(&self) -> i32 {
        let var = self.variable().index() as i32;
        if self.is_positive() {
            var
        } else {
            -var
        }
    }

    /// Get the underlying variable.
    pub fn variable(&self) -> Variable {
        Variable((self.0 / 2) + 1)
    }

    /// Check if this is a positive literal.
    pub fn is_positive(&self) -> bool {
        self.0 % 2 == 1
    }

    /// Check if this is a negative literal.
    pub fn is_negative(&self) -> bool {
        self.0 % 2 == 0
    }

    /// Get the negation of this literal.
    pub fn negate(&self) -> Self {
        Literal(self.0 ^ 1)
    }

    /// Get an index for array access (2*var_idx + polarity).
    pub fn index(&self) -> usize {
        self.0 as usize
    }

    /// Create from index.
    pub fn from_index(idx: usize) -> Self {
        Literal(idx as u32)
    }

    /// Get polarity as integer (1 for positive, 0 for negative).
    pub fn polarity(&self) -> u32 {
        self.0 % 2
    }
}

impl fmt::Debug for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_positive() {
            write!(f, "x{}", self.variable().index())
        } else {
            write!(f, "~x{}", self.variable().index())
        }
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_dimacs())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_variable_creation() {
        let v = Variable::new(1);
        assert_eq!(v.index(), 1);
        assert_eq!(v.to_index(), 0);

        let v = Variable::new(5);
        assert_eq!(v.index(), 5);
        assert_eq!(v.to_index(), 4);
    }

    #[test]
    fn test_variable_from_index() {
        let v = Variable::from_index(0);
        assert_eq!(v.index(), 1);

        let v = Variable::from_index(4);
        assert_eq!(v.index(), 5);
    }

    #[test]
    fn test_literal_positive() {
        let v = Variable::new(3);
        let lit = Literal::positive(v);
        assert!(lit.is_positive());
        assert!(!lit.is_negative());
        assert_eq!(lit.variable(), v);
    }

    #[test]
    fn test_literal_negative() {
        let v = Variable::new(3);
        let lit = Literal::negative(v);
        assert!(lit.is_negative());
        assert!(!lit.is_positive());
        assert_eq!(lit.variable(), v);
    }

    #[test]
    fn test_literal_negation() {
        let v = Variable::new(2);
        let pos = Literal::positive(v);
        let neg = pos.negate();
        
        assert!(pos.is_positive());
        assert!(neg.is_negative());
        assert_eq!(pos.variable(), neg.variable());
        assert_eq!(neg.negate(), pos);
    }

    #[test]
    fn test_literal_from_dimacs() {
        let lit = Literal::from_dimacs(3);
        assert!(lit.is_positive());
        assert_eq!(lit.variable().index(), 3);

        let lit = Literal::from_dimacs(-3);
        assert!(lit.is_negative());
        assert_eq!(lit.variable().index(), 3);

        let lit = Literal::from_dimacs(1);
        assert!(lit.is_positive());
        assert_eq!(lit.variable().index(), 1);

        let lit = Literal::from_dimacs(-1);
        assert!(lit.is_negative());
        assert_eq!(lit.variable().index(), 1);
    }

    #[test]
    fn test_literal_to_dimacs() {
        let v = Variable::new(3);
        assert_eq!(Literal::positive(v).to_dimacs(), 3);
        assert_eq!(Literal::negative(v).to_dimacs(), -3);
    }

    #[test]
    fn test_dimacs_roundtrip() {
        for i in 1..=10 {
            let lit = Literal::from_dimacs(i);
            assert_eq!(lit.to_dimacs(), i);

            let lit = Literal::from_dimacs(-i);
            assert_eq!(lit.to_dimacs(), -i);
        }
    }

    #[test]
    fn test_literal_indexing() {
        // Verify index scheme: 2*(var-1) + polarity
        let v1 = Variable::new(1);
        assert_eq!(Literal::negative(v1).index(), 0); // 2*0 + 0 = 0
        assert_eq!(Literal::positive(v1).index(), 1); // 2*0 + 1 = 1

        let v2 = Variable::new(2);
        assert_eq!(Literal::negative(v2).index(), 2); // 2*1 + 0 = 2
        assert_eq!(Literal::positive(v2).index(), 3); // 2*1 + 1 = 3
    }

    #[test]
    fn test_literal_from_index() {
        let lit = Literal::from_index(0);
        assert!(lit.is_negative());
        assert_eq!(lit.variable().index(), 1);

        let lit = Literal::from_index(1);
        assert!(lit.is_positive());
        assert_eq!(lit.variable().index(), 1);

        let lit = Literal::from_index(5);
        assert!(lit.is_positive());
        assert_eq!(lit.variable().index(), 3);
    }
}
