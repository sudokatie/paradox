//! DIMACS CNF parser
//!
//! Parses the standard DIMACS CNF format:
//! ```text
//! c This is a comment
//! p cnf 3 2
//! 1 -2 0
//! 2 3 0
//! ```

use crate::clause::Clause;
use crate::formula::Formula;
use crate::literal::{Literal, Variable};
use std::io::BufRead;

/// Errors that can occur during DIMACS parsing
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DimacsError {
    /// Missing problem line (p cnf ...)
    MissingHeader,
    /// Invalid problem line format
    InvalidHeader(String),
    /// Invalid literal value
    InvalidLiteral(String),
    /// Variable index out of declared range
    VariableOutOfRange { var: u32, max: u32 },
    /// Wrong number of clauses
    ClauseCountMismatch { expected: usize, actual: usize },
    /// Empty clause (contradiction)
    EmptyClause,
    /// IO error
    IoError(String),
}

impl std::fmt::Display for DimacsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DimacsError::MissingHeader => write!(f, "missing problem line (p cnf ...)"),
            DimacsError::InvalidHeader(s) => write!(f, "invalid header: {}", s),
            DimacsError::InvalidLiteral(s) => write!(f, "invalid literal: {}", s),
            DimacsError::VariableOutOfRange { var, max } => {
                write!(f, "variable {} out of range (max: {})", var, max)
            }
            DimacsError::ClauseCountMismatch { expected, actual } => {
                write!(f, "expected {} clauses, found {}", expected, actual)
            }
            DimacsError::EmptyClause => write!(f, "empty clause (trivially unsatisfiable)"),
            DimacsError::IoError(s) => write!(f, "io error: {}", s),
        }
    }
}

impl std::error::Error for DimacsError {}

/// Parse DIMACS CNF from a reader
pub fn parse_dimacs<R: BufRead>(reader: R) -> Result<Formula, DimacsError> {
    let mut num_vars: Option<u32> = None;
    let mut num_clauses: Option<usize> = None;
    let mut formula: Option<Formula> = None;
    let mut current_clause: Vec<Literal> = Vec::new();
    let mut clause_count = 0;

    for line_result in reader.lines() {
        let line = line_result.map_err(|e| DimacsError::IoError(e.to_string()))?;
        let line = line.trim();

        // Skip empty lines and comments
        if line.is_empty() || line.starts_with('c') {
            continue;
        }

        // Parse problem line
        if line.starts_with('p') {
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() < 4 || parts[1] != "cnf" {
                return Err(DimacsError::InvalidHeader(line.to_string()));
            }
            num_vars = Some(
                parts[2]
                    .parse()
                    .map_err(|_| DimacsError::InvalidHeader(line.to_string()))?,
            );
            num_clauses = Some(
                parts[3]
                    .parse()
                    .map_err(|_| DimacsError::InvalidHeader(line.to_string()))?,
            );
            formula = Some(Formula::with_num_vars(num_vars.unwrap()));
            continue;
        }

        // Ensure we have a header
        let nv = num_vars.ok_or(DimacsError::MissingHeader)?;
        let f = formula.as_mut().ok_or(DimacsError::MissingHeader)?;

        // Parse clause literals
        for token in line.split_whitespace() {
            let lit_val: i32 = token
                .parse()
                .map_err(|_| DimacsError::InvalidLiteral(token.to_string()))?;

            if lit_val == 0 {
                // End of clause
                if current_clause.is_empty() {
                    return Err(DimacsError::EmptyClause);
                }
                let clause = Clause::new(current_clause.clone());
                f.add_clause(clause);
                current_clause.clear();
                clause_count += 1;
            } else {
                // Parse literal
                let var_idx = lit_val.unsigned_abs();
                if var_idx == 0 || var_idx > nv {
                    return Err(DimacsError::VariableOutOfRange { var: var_idx, max: nv });
                }
                let var = Variable::new(var_idx);
                let lit = if lit_val > 0 {
                    Literal::positive(var)
                } else {
                    Literal::negative(var)
                };
                current_clause.push(lit);
            }
        }
    }

    // Handle unterminated clause (some files omit trailing 0)
    if !current_clause.is_empty() {
        let f = formula.as_mut().ok_or(DimacsError::MissingHeader)?;
        let clause = Clause::new(current_clause);
        f.add_clause(clause);
        clause_count += 1;
    }

    // Verify clause count (warning only - some files are wrong)
    if let Some(expected) = num_clauses {
        if clause_count != expected {
            // Many DIMACS files have wrong counts, so just warn
            eprintln!(
                "Warning: expected {} clauses, found {}",
                expected, clause_count
            );
        }
    }

    formula.ok_or(DimacsError::MissingHeader)
}

/// Parse DIMACS CNF from a string
pub fn parse_dimacs_str(input: &str) -> Result<Formula, DimacsError> {
    parse_dimacs(input.as_bytes())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple() {
        let input = "p cnf 3 2\n1 -2 0\n2 3 0\n";
        let formula = parse_dimacs_str(input).unwrap();
        assert_eq!(formula.num_vars(), 3);
        assert_eq!(formula.num_clauses(), 2);
    }

    #[test]
    fn test_parse_with_comments() {
        let input = "c comment\nc another comment\np cnf 2 1\n1 2 0\n";
        let formula = parse_dimacs_str(input).unwrap();
        assert_eq!(formula.num_vars(), 2);
        assert_eq!(formula.num_clauses(), 1);
    }

    #[test]
    fn test_parse_multiline_clause() {
        let input = "p cnf 4 1\n1 2\n3 4 0\n";
        let formula = parse_dimacs_str(input).unwrap();
        assert_eq!(formula.num_clauses(), 1);
        assert_eq!(formula.clause(0).len(), 4);
    }

    #[test]
    fn test_parse_single_literal_clause() {
        let input = "p cnf 1 1\n1 0\n";
        let formula = parse_dimacs_str(input).unwrap();
        assert_eq!(formula.num_clauses(), 1);
        assert_eq!(formula.clause(0).len(), 1);
    }

    #[test]
    fn test_parse_negative_literals() {
        let input = "p cnf 3 1\n-1 -2 -3 0\n";
        let formula = parse_dimacs_str(input).unwrap();
        let clause = formula.clause(0);
        assert!(clause.literals().iter().all(|l| !l.polarity()));
    }

    #[test]
    fn test_missing_header() {
        let input = "1 2 0\n";
        let result = parse_dimacs_str(input);
        assert!(matches!(result, Err(DimacsError::MissingHeader)));
    }

    #[test]
    fn test_invalid_header() {
        let input = "p sat 3 2\n";
        let result = parse_dimacs_str(input);
        assert!(matches!(result, Err(DimacsError::InvalidHeader(_))));
    }

    #[test]
    fn test_invalid_literal() {
        let input = "p cnf 3 1\n1 abc 0\n";
        let result = parse_dimacs_str(input);
        assert!(matches!(result, Err(DimacsError::InvalidLiteral(_))));
    }

    #[test]
    fn test_variable_out_of_range() {
        let input = "p cnf 2 1\n1 5 0\n";
        let result = parse_dimacs_str(input);
        assert!(matches!(result, Err(DimacsError::VariableOutOfRange { .. })));
    }

    #[test]
    fn test_empty_clause() {
        let input = "p cnf 2 1\n0\n";
        let result = parse_dimacs_str(input);
        assert!(matches!(result, Err(DimacsError::EmptyClause)));
    }

    #[test]
    fn test_empty_input() {
        let input = "";
        let result = parse_dimacs_str(input);
        assert!(matches!(result, Err(DimacsError::MissingHeader)));
    }

    #[test]
    fn test_only_comments() {
        let input = "c just a comment\nc another one\n";
        let result = parse_dimacs_str(input);
        assert!(matches!(result, Err(DimacsError::MissingHeader)));
    }

    #[test]
    fn test_trailing_whitespace() {
        let input = "p cnf 2 1  \n  1 2 0  \n";
        let formula = parse_dimacs_str(input).unwrap();
        assert_eq!(formula.num_clauses(), 1);
    }

    #[test]
    fn test_multiple_spaces() {
        let input = "p cnf 3 1\n1   2   3   0\n";
        let formula = parse_dimacs_str(input).unwrap();
        assert_eq!(formula.clause(0).len(), 3);
    }

    #[test]
    fn test_unterminated_clause() {
        // Some DIMACS files omit the trailing 0
        let input = "p cnf 2 1\n1 2";
        let formula = parse_dimacs_str(input).unwrap();
        assert_eq!(formula.num_clauses(), 1);
    }

    #[test]
    fn test_large_variable_index() {
        let input = "p cnf 1000000 1\n1000000 -999999 0\n";
        let formula = parse_dimacs_str(input).unwrap();
        assert_eq!(formula.num_vars(), 1000000);
    }

    #[test]
    fn test_parse_preserves_literal_order() {
        let input = "p cnf 4 1\n4 3 2 1 0\n";
        let formula = parse_dimacs_str(input).unwrap();
        let lits: Vec<_> = formula.clause(0).literals().iter().map(|l| l.variable().index()).collect();
        assert_eq!(lits, vec![4, 3, 2, 1]);
    }
}
