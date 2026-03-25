//! Parsers for various input formats

pub mod dimacs;

pub use dimacs::{parse_dimacs, DimacsError};
