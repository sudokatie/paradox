//! Paradox - SAT/SMT solver with CDCL and theory solvers.
//!
//! # Features
//!
//! - SAT solving via CDCL (Conflict-Driven Clause Learning)
//! - Two-watched-literal scheme for efficient propagation
//! - VSIDS variable selection heuristic
//! - SMT solving via DPLL(T) architecture (planned)
//!
//! # Example
//!
//! ```
//! use paradox::parser::parse_dimacs;
//!
//! let input = r#"
//! p cnf 3 2
//! 1 -2 3 0
//! -1 2 0
//! "#;
//!
//! let formula = parse_dimacs(input).unwrap();
//! assert_eq!(formula.num_vars(), 3);
//! assert_eq!(formula.num_clauses(), 2);
//! ```

pub mod literal;
pub mod clause;
pub mod formula;
pub mod assignment;
pub mod trail;
pub mod watch;
pub mod parser;
pub mod solver;

// Re-exports for convenience
pub use literal::{Literal, Variable};
pub use clause::{Clause, ClauseRef};
pub use formula::Formula;
pub use assignment::{Assignments, Value};
pub use trail::Trail;
pub use watch::{WatchLists, Watcher, init_watches};
pub use parser::{parse_dimacs, parse_dimacs_file};
