//! DRAT proof logging for SAT solver
//!
//! DRAT (Deletion Resolution Asymmetric Tautology) is a standard format for
//! verifying unsatisfiability proofs from CDCL SAT solvers.
//!
//! Format:
//! - Addition: literals separated by spaces, terminated by 0
//! - Deletion: "d" followed by literals and 0
//!
//! Example:
//! ```text
//! 1 2 -3 0      // Add clause (1 OR 2 OR NOT 3)
//! d 1 2 0       // Delete clause (1 OR 2)
//! ```

use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

use crate::clause::Clause;
use crate::literal::Literal;

/// DRAT proof writer
pub struct ProofWriter {
    writer: Option<BufWriter<File>>,
    clause_count: u64,
    deletion_count: u64,
}

impl ProofWriter {
    /// Create a new proof writer that writes to the given path
    pub fn new<P: AsRef<Path>>(path: P) -> std::io::Result<Self> {
        let file = File::create(path)?;
        Ok(ProofWriter {
            writer: Some(BufWriter::new(file)),
            clause_count: 0,
            deletion_count: 0,
        })
    }

    /// Create a dummy proof writer that discards output
    pub fn null() -> Self {
        ProofWriter {
            writer: None,
            clause_count: 0,
            deletion_count: 0,
        }
    }

    /// Check if proof writing is enabled
    pub fn is_enabled(&self) -> bool {
        self.writer.is_some()
    }

    /// Log an added clause (learned clause)
    pub fn add_clause(&mut self, clause: &Clause) -> std::io::Result<()> {
        if let Some(ref mut writer) = self.writer {
            for lit in clause.literals() {
                write!(writer, "{} ", lit_to_dimacs(*lit))?;
            }
            writeln!(writer, "0")?;
            self.clause_count += 1;
        }
        Ok(())
    }

    /// Log a clause addition from literals
    pub fn add_literals(&mut self, literals: &[Literal]) -> std::io::Result<()> {
        if let Some(ref mut writer) = self.writer {
            for lit in literals {
                write!(writer, "{} ", lit_to_dimacs(*lit))?;
            }
            writeln!(writer, "0")?;
            self.clause_count += 1;
        }
        Ok(())
    }

    /// Log a deleted clause
    pub fn delete_clause(&mut self, clause: &Clause) -> std::io::Result<()> {
        if let Some(ref mut writer) = self.writer {
            write!(writer, "d ")?;
            for lit in clause.literals() {
                write!(writer, "{} ", lit_to_dimacs(*lit))?;
            }
            writeln!(writer, "0")?;
            self.deletion_count += 1;
        }
        Ok(())
    }

    /// Log a clause deletion from literals
    pub fn delete_literals(&mut self, literals: &[Literal]) -> std::io::Result<()> {
        if let Some(ref mut writer) = self.writer {
            write!(writer, "d ")?;
            for lit in literals {
                write!(writer, "{} ", lit_to_dimacs(*lit))?;
            }
            writeln!(writer, "0")?;
            self.deletion_count += 1;
        }
        Ok(())
    }

    /// Flush the proof output
    pub fn flush(&mut self) -> std::io::Result<()> {
        if let Some(ref mut writer) = self.writer {
            writer.flush()?;
        }
        Ok(())
    }

    /// Get the number of clauses added
    pub fn clause_count(&self) -> u64 {
        self.clause_count
    }

    /// Get the number of clauses deleted
    pub fn deletion_count(&self) -> u64 {
        self.deletion_count
    }
}

impl Drop for ProofWriter {
    fn drop(&mut self) {
        let _ = self.flush();
    }
}

/// Convert internal literal to DIMACS format
/// Internal: variable index is already 1-indexed
/// DIMACS: positive as v, negative as -v
fn lit_to_dimacs(lit: Literal) -> i32 {
    let var = lit.variable().index() as i32;
    if lit.is_positive() {
        var
    } else {
        -var
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Read;
    use tempfile::NamedTempFile;

    fn make_literal(var: u32, positive: bool) -> Literal {
        let v = crate::literal::Variable::new(var);
        Literal::new(v, positive)
    }

    fn make_clause(lits: &[(u32, bool)]) -> Clause {
        let literals: Vec<Literal> = lits.iter()
            .map(|(v, p)| make_literal(*v, *p))
            .collect();
        Clause::new(literals)
    }

    #[test]
    fn test_null_writer() {
        let mut writer = ProofWriter::null();
        assert!(!writer.is_enabled());
        
        let clause = make_clause(&[(1, true), (2, false)]);
        writer.add_clause(&clause).unwrap();
        assert_eq!(writer.clause_count(), 0); // null writer doesn't count
    }

    #[test]
    fn test_add_clause() {
        let temp = NamedTempFile::new().unwrap();
        let mut writer = ProofWriter::new(temp.path()).unwrap();
        assert!(writer.is_enabled());

        // Add clause (1 OR NOT 2 OR 3) - use 1-indexed vars
        let clause = make_clause(&[(1, true), (2, false), (3, true)]);
        writer.add_clause(&clause).unwrap();
        writer.flush().unwrap();

        let mut content = String::new();
        std::fs::File::open(temp.path()).unwrap().read_to_string(&mut content).unwrap();
        assert_eq!(content.trim(), "1 -2 3 0");
    }

    #[test]
    fn test_delete_clause() {
        let temp = NamedTempFile::new().unwrap();
        let mut writer = ProofWriter::new(temp.path()).unwrap();

        let clause = make_clause(&[(1, true), (2, true)]);
        writer.delete_clause(&clause).unwrap();
        writer.flush().unwrap();

        let mut content = String::new();
        std::fs::File::open(temp.path()).unwrap().read_to_string(&mut content).unwrap();
        assert_eq!(content.trim(), "d 1 2 0");
    }

    #[test]
    fn test_mixed_operations() {
        let temp = NamedTempFile::new().unwrap();
        let mut writer = ProofWriter::new(temp.path()).unwrap();

        // Add (1 OR 2)
        let clause1 = make_clause(&[(1, true), (2, true)]);
        writer.add_clause(&clause1).unwrap();

        // Add (NOT 1 OR 3)
        let clause2 = make_clause(&[(1, false), (3, true)]);
        writer.add_clause(&clause2).unwrap();

        // Delete (1 OR 2)
        writer.delete_clause(&clause1).unwrap();

        writer.flush().unwrap();

        assert_eq!(writer.clause_count(), 2);
        assert_eq!(writer.deletion_count(), 1);

        let mut content = String::new();
        std::fs::File::open(temp.path()).unwrap().read_to_string(&mut content).unwrap();
        let lines: Vec<&str> = content.trim().lines().collect();
        assert_eq!(lines.len(), 3);
        assert_eq!(lines[0], "1 2 0");
        assert_eq!(lines[1], "-1 3 0");
        assert_eq!(lines[2], "d 1 2 0");
    }

    #[test]
    fn test_lit_to_dimacs() {
        // Variable 1, positive -> 1
        let lit = make_literal(1, true);
        assert_eq!(lit_to_dimacs(lit), 1);

        // Variable 1, negative -> -1
        let lit = make_literal(1, false);
        assert_eq!(lit_to_dimacs(lit), -1);

        // Variable 5, positive -> 5
        let lit = make_literal(5, true);
        assert_eq!(lit_to_dimacs(lit), 5);

        // Variable 5, negative -> -5
        let lit = make_literal(5, false);
        assert_eq!(lit_to_dimacs(lit), -5);
    }
}
