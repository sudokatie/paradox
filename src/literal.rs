//! Literal and Variable types for SAT solving

use std::fmt;

/// A boolean variable (1-indexed for DIMACS compatibility)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Variable(pub u32);

impl Variable {
    /// Create a new variable with the given index (1-indexed)
    pub fn new(index: u32) -> Self {
        debug_assert!(index > 0, "Variables are 1-indexed");
        Variable(index)
    }

    /// Get the variable index (1-indexed)
    pub fn index(&self) -> u32 {
        self.0
    }

    /// Get the 0-based array index
    pub fn array_index(&self) -> usize {
        (self.0 - 1) as usize
    }
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x{}", self.0)
    }
}

/// A literal is a variable with a polarity (positive or negative)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Literal {
    /// Encoded as 2*var + (1 if negative, 0 if positive)
    /// This allows efficient indexing for watch lists
    code: u32,
}

impl Literal {
    /// Create a new literal
    pub fn new(var: Variable, positive: bool) -> Self {
        let code = 2 * var.0 + if positive { 0 } else { 1 };
        Literal { code }
    }

    /// Create a positive literal
    pub fn positive(var: Variable) -> Self {
        Self::new(var, true)
    }

    /// Create a negative literal
    pub fn negative(var: Variable) -> Self {
        Self::new(var, false)
    }

    /// Parse from DIMACS format (non-zero integer)
    pub fn from_dimacs(i: i32) -> Self {
        debug_assert!(i != 0, "DIMACS literal cannot be 0");
        let var = Variable::new(i.unsigned_abs());
        Self::new(var, i > 0)
    }

    /// Convert to DIMACS format
    pub fn to_dimacs(&self) -> i32 {
        let var = self.variable().0 as i32;
        if self.is_positive() { var } else { -var }
    }

    /// Get the underlying variable
    pub fn variable(&self) -> Variable {
        Variable(self.code / 2)
    }

    /// Check if this is a positive literal
    pub fn is_positive(&self) -> bool {
        self.code % 2 == 0
    }

    /// Check if this is a negative literal
    pub fn is_negative(&self) -> bool {
        !self.is_positive()
    }

    /// Get the negation of this literal
    pub fn negate(&self) -> Literal {
        Literal { code: self.code ^ 1 }
    }

    /// Get an index for array access (0-based, separate for pos/neg)
    pub fn index(&self) -> usize {
        self.code as usize
    }

    /// Get the polarity (true for positive, false for negative)
    pub fn polarity(&self) -> bool {
        self.is_positive()
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_positive() {
            write!(f, "{}", self.variable())
        } else {
            write!(f, "~{}", self.variable())
        }
    }
}

impl std::ops::Not for Literal {
    type Output = Literal;

    fn not(self) -> Literal {
        self.negate()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_variable_creation() {
        let v = Variable::new(1);
        assert_eq!(v.index(), 1);
        assert_eq!(v.array_index(), 0);

        let v2 = Variable::new(5);
        assert_eq!(v2.index(), 5);
        assert_eq!(v2.array_index(), 4);
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
        assert!(!lit.is_positive());
        assert!(lit.is_negative());
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
    fn test_literal_not_operator() {
        let lit = Literal::from_dimacs(5);
        let neg = !lit;
        assert_eq!(neg, Literal::from_dimacs(-5));
    }

    #[test]
    fn test_dimacs_conversion() {
        // Positive
        let lit = Literal::from_dimacs(3);
        assert!(lit.is_positive());
        assert_eq!(lit.variable(), Variable::new(3));
        assert_eq!(lit.to_dimacs(), 3);

        // Negative
        let lit2 = Literal::from_dimacs(-5);
        assert!(lit2.is_negative());
        assert_eq!(lit2.variable(), Variable::new(5));
        assert_eq!(lit2.to_dimacs(), -5);
    }

    #[test]
    fn test_literal_index() {
        // Index should be unique for each (var, polarity) pair
        let v1_pos = Literal::from_dimacs(1);
        let v1_neg = Literal::from_dimacs(-1);
        let v2_pos = Literal::from_dimacs(2);
        let v2_neg = Literal::from_dimacs(-2);

        let indices: Vec<usize> = vec![
            v1_pos.index(),
            v1_neg.index(),
            v2_pos.index(),
            v2_neg.index(),
        ];

        // All indices should be unique
        let mut sorted = indices.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(sorted.len(), indices.len());
    }

    #[test]
    fn test_variable_display() {
        let v = Variable::new(42);
        assert_eq!(format!("{}", v), "x42");
    }

    #[test]
    fn test_literal_display() {
        let pos = Literal::from_dimacs(3);
        let neg = Literal::from_dimacs(-5);
        assert_eq!(format!("{}", pos), "x3");
        assert_eq!(format!("{}", neg), "~x5");
    }
}
