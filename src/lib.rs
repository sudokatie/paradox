//! Paradox - SAT/SMT solver with CDCL and theory solvers
//!
//! A satisfiability solver implementing:
//! - SAT solving via CDCL (Conflict-Driven Clause Learning)
//! - SMT solving via DPLL(T) architecture
//! - Theory solvers for EUF, LIA, bitvectors, and arrays

pub mod literal;
pub mod clause;

pub use literal::{Literal, Variable};
pub use clause::{Clause, ClauseRef};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_paradox_basic() {
        // Basic smoke test
        let v = Variable::new(1);
        let lit = Literal::positive(v);
        let clause = Clause::new(vec![lit]);
        
        assert_eq!(clause.len(), 1);
        assert!(clause.is_unit());
    }
}
