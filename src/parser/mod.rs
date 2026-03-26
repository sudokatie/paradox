//! Parsing for SAT/SMT input formats.

pub mod dimacs;
pub mod smtlib;

pub use dimacs::{parse_dimacs, parse_dimacs_file, DimacsError};
pub use smtlib::{
    parse_smtlib, parse_smtlib_file, SmtLibError, SmtProblem,
    Logic, Sort, Term, Command, FunDecl,
};

use std::path::Path;

/// Detected input format.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InputFormat {
    Dimacs,
    SmtLib,
}

/// Detect the input format from a file path.
pub fn detect_format(path: &Path) -> InputFormat {
    match path.extension().and_then(|e| e.to_str()) {
        Some("cnf") | Some("dimacs") => InputFormat::Dimacs,
        Some("smt2") | Some("smt") => InputFormat::SmtLib,
        _ => {
            // Try to detect from content
            if let Ok(content) = std::fs::read_to_string(path) {
                let trimmed = content.trim_start();
                if trimmed.starts_with('(') {
                    InputFormat::SmtLib
                } else {
                    InputFormat::Dimacs
                }
            } else {
                InputFormat::Dimacs
            }
        }
    }
}
