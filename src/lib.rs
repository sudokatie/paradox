//! Paradox - SAT/SMT solver with CDCL and theory solvers.
//!
//! # Features
//!
//! - SAT solving via CDCL (Conflict-Driven Clause Learning)
//! - Two-watched-literal scheme for efficient propagation
//! - VSIDS variable selection heuristic
//! - SMT solving via DPLL(T) architecture
//! - Theory solvers: EUF, LIA, BV, Arrays
//!
//! # SAT Example
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
//!
//! # SMT Example
//!
//! ```
//! use paradox::parser::parse_smtlib;
//!
//! let input = r#"
//! (set-logic QF_LIA)
//! (declare-const x Int)
//! (assert (> x 0))
//! (check-sat)
//! "#;
//!
//! let problem = parse_smtlib(input).unwrap();
//! assert_eq!(problem.assertions.len(), 1);
//! ```

pub mod literal;
pub mod clause;
pub mod formula;
pub mod assignment;
pub mod trail;
pub mod watch;
pub mod parser;
pub mod solver;
pub mod theory;
pub mod dpll_t;

// Re-exports for convenience
pub use literal::{Literal, Variable};
pub use clause::{Clause, ClauseRef};
pub use formula::Formula;
pub use assignment::{Assignments, Value};
pub use trail::Trail;
pub use watch::{WatchLists, Watcher, init_watches};
pub use parser::{parse_dimacs, parse_dimacs_file, parse_smtlib, parse_smtlib_file};
pub use parser::{InputFormat, detect_format};
pub use dpll_t::DpllT;
