//! Paradox - SAT/SMT solver with CDCL and theory solvers
//!
//! A satisfiability solver implementing:
//! - SAT solving via CDCL (Conflict-Driven Clause Learning)
//! - SMT solving via DPLL(T) architecture
//! - Theory solvers for EUF, LIA, bitvectors, and arrays

pub mod literal;
pub mod clause;
pub mod formula;
pub mod assignment;
pub mod trail;
pub mod watch;
pub mod parser;
pub mod solver;
pub mod theory;
pub mod verify;

pub use literal::{Literal, Variable};
pub use clause::{Clause, ClauseRef};
pub use formula::Formula;
pub use assignment::{Assignments, AssignmentInfo, Value};
pub use trail::Trail;
pub use watch::{WatchLists, Watcher, init_watches};
pub use parser::{parse_dimacs, DimacsError, parse_smtlib, SmtLibError};
pub use solver::{Solver, SolveResult, propagate, analyze_conflict, ConflictResult};
pub use theory::{TheorySolver, TheoryConflict, TheoryPropagation, TheoryManager};

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
