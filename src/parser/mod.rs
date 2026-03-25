//! Parsing for SAT/SMT input formats.

pub mod dimacs;

pub use dimacs::{parse_dimacs, parse_dimacs_file, DimacsError};
