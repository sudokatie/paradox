//! DIMACS CNF parser.
//!
//! DIMACS CNF format:
//! ```text
//! c comment line
//! p cnf <num_vars> <num_clauses>
//! 1 -2 3 0
//! -1 2 0
//! ```
//!
//! - Comments start with 'c'
//! - Problem line starts with 'p'
//! - Variables are positive integers
//! - Negative means negation
//! - Each clause ends with 0

use crate::clause::Clause;
use crate::formula::Formula;
use crate::literal::Literal;
use std::fs;
use std::path::Path;
use thiserror::Error;

/// Errors that can occur during DIMACS parsing.
#[derive(Error, Debug)]
pub enum DimacsError {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    #[error("Missing problem line (p cnf ...)")]
    MissingProblemLine,

    #[error("Invalid problem line: {0}")]
    InvalidProblemLine(String),

    #[error("Invalid literal '{0}' on line {1}")]
    InvalidLiteral(String, usize),

    #[error("Literal 0 not allowed except as clause terminator (line {0})")]
    ZeroLiteral(usize),

    #[error("Variable {0} exceeds declared count {1}")]
    VariableOutOfRange(u32, u32),

    #[error("Clause count mismatch: expected {expected}, got {actual}")]
    ClauseCountMismatch { expected: usize, actual: usize },
}

/// Parse a DIMACS CNF string.
pub fn parse_dimacs(input: &str) -> Result<Formula, DimacsError> {
    let mut num_vars: Option<u32> = None;
    let mut num_clauses: Option<usize> = None;
    let mut formula = Formula::new();
    let mut current_clause = Vec::new();
    let mut clause_count = 0;

    for (line_num, line) in input.lines().enumerate() {
        let line_num = line_num + 1; // 1-indexed for errors
        let line = line.trim();

        // Skip empty lines
        if line.is_empty() {
            continue;
        }

        // Comment line
        if line.starts_with('c') {
            continue;
        }

        // Problem line
        if line.starts_with('p') {
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() < 4 || parts[1] != "cnf" {
                return Err(DimacsError::InvalidProblemLine(line.to_string()));
            }
            num_vars = Some(
                parts[2]
                    .parse()
                    .map_err(|_| DimacsError::InvalidProblemLine(line.to_string()))?,
            );
            num_clauses = Some(
                parts[3]
                    .parse()
                    .map_err(|_| DimacsError::InvalidProblemLine(line.to_string()))?,
            );
            formula.set_num_vars(num_vars.unwrap());
            continue;
        }

        // Must have seen problem line by now
        if num_vars.is_none() {
            return Err(DimacsError::MissingProblemLine);
        }
        let max_var = num_vars.unwrap();

        // Parse literals
        for token in line.split_whitespace() {
            let lit_val: i32 = token
                .parse()
                .map_err(|_| DimacsError::InvalidLiteral(token.to_string(), line_num))?;

            if lit_val == 0 {
                // End of clause
                formula.add_clause(Clause::new(current_clause.clone()));
                clause_count += 1;
                current_clause.clear();
            } else {
                // Check variable range
                let var = lit_val.unsigned_abs();
                if var > max_var {
                    return Err(DimacsError::VariableOutOfRange(var, max_var));
                }
                current_clause.push(Literal::from_dimacs(lit_val));
            }
        }
    }

    // Handle unterminated clause (some formats allow this)
    if !current_clause.is_empty() {
        formula.add_clause(Clause::new(current_clause));
        clause_count += 1;
    }

    // Check clause count (warning only - many files don't match exactly)
    if let Some(expected) = num_clauses {
        if clause_count != expected {
            // Log warning but don't fail - many benchmark files have wrong counts
            log::warn!(
                "Clause count mismatch: expected {}, got {}",
                expected,
                clause_count
            );
        }
    }

    Ok(formula)
}

/// Parse a DIMACS CNF file.
pub fn parse_dimacs_file<P: AsRef<Path>>(path: P) -> Result<Formula, DimacsError> {
    let content = fs::read_to_string(path)?;
    parse_dimacs(&content)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_dimacs() {
        let input = r#"
c Comment
p cnf 3 2
1 -2 3 0
-1 2 0
"#;
        let formula = parse_dimacs(input).unwrap();
        assert_eq!(formula.num_vars(), 3);
        assert_eq!(formula.num_clauses(), 2);
        
        assert_eq!(formula.clause(0).len(), 3);
        assert_eq!(formula.clause(0)[0].to_dimacs(), 1);
        assert_eq!(formula.clause(0)[1].to_dimacs(), -2);
        assert_eq!(formula.clause(0)[2].to_dimacs(), 3);
        
        assert_eq!(formula.clause(1).len(), 2);
        assert_eq!(formula.clause(1)[0].to_dimacs(), -1);
        assert_eq!(formula.clause(1)[1].to_dimacs(), 2);
    }

    #[test]
    fn test_multiple_clauses_per_line() {
        let input = r#"
p cnf 2 3
1 2 0 -1 -2 0 1 0
"#;
        let formula = parse_dimacs(input).unwrap();
        assert_eq!(formula.num_clauses(), 3);
    }

    #[test]
    fn test_clause_across_lines() {
        let input = r#"
p cnf 3 1
1
2
3 0
"#;
        let formula = parse_dimacs(input).unwrap();
        assert_eq!(formula.num_clauses(), 1);
        assert_eq!(formula.clause(0).len(), 3);
    }

    #[test]
    fn test_empty_clause() {
        let input = r#"
p cnf 1 1
0
"#;
        let formula = parse_dimacs(input).unwrap();
        assert_eq!(formula.num_clauses(), 1);
        assert!(formula.clause(0).is_empty());
    }

    #[test]
    fn test_unit_clauses() {
        let input = r#"
p cnf 3 3
1 0
-2 0
3 0
"#;
        let formula = parse_dimacs(input).unwrap();
        assert_eq!(formula.num_clauses(), 3);
        assert!(formula.clause(0).is_unit());
        assert!(formula.clause(1).is_unit());
        assert!(formula.clause(2).is_unit());
    }

    #[test]
    fn test_multiple_comments() {
        let input = r#"
c First comment
c Second comment
p cnf 2 1
c Comment between
1 2 0
c Final comment
"#;
        let formula = parse_dimacs(input).unwrap();
        assert_eq!(formula.num_clauses(), 1);
    }

    #[test]
    fn test_missing_problem_line() {
        let input = "1 2 0";
        let result = parse_dimacs(input);
        assert!(matches!(result, Err(DimacsError::MissingProblemLine)));
    }

    #[test]
    fn test_invalid_problem_line() {
        let input = "p sat 3 2";
        let result = parse_dimacs(input);
        assert!(matches!(result, Err(DimacsError::InvalidProblemLine(_))));
    }

    #[test]
    fn test_invalid_literal() {
        let input = r#"
p cnf 2 1
1 abc 0
"#;
        let result = parse_dimacs(input);
        assert!(matches!(result, Err(DimacsError::InvalidLiteral(_, _))));
    }

    #[test]
    fn test_variable_out_of_range() {
        let input = r#"
p cnf 2 1
1 5 0
"#;
        let result = parse_dimacs(input);
        assert!(matches!(result, Err(DimacsError::VariableOutOfRange(5, 2))));
    }

    #[test]
    fn test_unterminated_clause() {
        // Some DIMACS files don't terminate the last clause
        let input = r#"
p cnf 2 1
1 2
"#;
        let formula = parse_dimacs(input).unwrap();
        assert_eq!(formula.num_clauses(), 1);
        assert_eq!(formula.clause(0).len(), 2);
    }

    #[test]
    fn test_whitespace_handling() {
        let input = "  p   cnf   2   1  \n  1    2   0  ";
        let formula = parse_dimacs(input).unwrap();
        assert_eq!(formula.num_vars(), 2);
        assert_eq!(formula.num_clauses(), 1);
    }

    #[test]
    fn test_negative_literals() {
        let input = r#"
p cnf 3 1
-1 -2 -3 0
"#;
        let formula = parse_dimacs(input).unwrap();
        assert_eq!(formula.clause(0)[0].to_dimacs(), -1);
        assert_eq!(formula.clause(0)[1].to_dimacs(), -2);
        assert_eq!(formula.clause(0)[2].to_dimacs(), -3);
    }

    #[test]
    fn test_real_world_format() {
        // Based on SAT Competition format
        let input = r#"
c This is a comment
c Generated by some tool
c
p cnf 5 3
1 -5 4 0
-1 5 3 4 0
-3 -4 0
"#;
        let formula = parse_dimacs(input).unwrap();
        assert_eq!(formula.num_vars(), 5);
        assert_eq!(formula.num_clauses(), 3);
    }
}
