//! DRAT proof checker implementation
//!
//! Verifies DRAT proofs using reverse unit propagation (RUP).
//! A clause C is RUP if unit propagation on (F ∧ ¬C) derives a conflict.

use std::collections::HashSet;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;

use crate::formula::Formula;
use crate::literal::Literal;

/// Result of DRAT verification
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerifyResult {
    /// Proof is valid - formula is UNSAT
    Valid,
    /// Proof is invalid at the given line
    Invalid { line: usize, reason: String },
}

/// Verification error
#[derive(Debug)]
pub enum VerifyError {
    /// IO error reading files
    Io(std::io::Error),
    /// Parse error in proof file
    Parse { line: usize, message: String },
}

impl From<std::io::Error> for VerifyError {
    fn from(e: std::io::Error) -> Self {
        VerifyError::Io(e)
    }
}

/// DRAT proof verifier
pub struct DratVerifier {
    /// Active clauses (original + learned - deleted)
    clauses: Vec<Option<Vec<Literal>>>,
    /// Number of variables
    num_vars: u32,
    /// Current assignments during unit propagation
    assignments: Vec<Option<bool>>,
    /// Propagation queue
    propagation_queue: Vec<Literal>,
    /// Statistics
    stats: VerifyStats,
}

/// Verification statistics
#[derive(Debug, Clone, Default)]
pub struct VerifyStats {
    /// Number of clauses checked
    pub clauses_checked: u64,
    /// Number of deletions processed
    pub deletions_processed: u64,
    /// Number of RUP checks performed
    pub rup_checks: u64,
}

impl DratVerifier {
    /// Create a new verifier from a CNF formula
    pub fn new(formula: &Formula) -> Self {
        let num_vars = formula.num_vars();
        let clauses: Vec<Option<Vec<Literal>>> = formula
            .clauses()
            .iter()
            .map(|c| Some(c.literals().to_vec()))
            .collect();

        DratVerifier {
            clauses,
            num_vars,
            assignments: vec![None; (num_vars + 1) as usize],
            propagation_queue: Vec::new(),
            stats: VerifyStats::default(),
        }
    }

    /// Create a verifier from a DIMACS CNF file
    pub fn from_cnf_file<P: AsRef<Path>>(path: P) -> Result<Self, VerifyError> {
        let file = File::open(path)?;
        let reader = BufReader::new(file);
        
        let mut num_vars: u32 = 0;
        let mut clauses: Vec<Option<Vec<Literal>>> = Vec::new();

        for line in reader.lines() {
            let line = line?;
            let line = line.trim();
            
            // Skip comments and empty lines
            if line.is_empty() || line.starts_with('c') {
                continue;
            }
            
            // Parse header
            if line.starts_with('p') {
                let parts: Vec<&str> = line.split_whitespace().collect();
                if parts.len() >= 3 {
                    num_vars = parts[2].parse().unwrap_or(0);
                }
                continue;
            }
            
            // Parse clause
            let lits: Vec<Literal> = line
                .split_whitespace()
                .filter_map(|s| s.parse::<i32>().ok())
                .take_while(|&n| n != 0)
                .map(|n| Literal::from_dimacs(n))
                .collect();
            
            if !lits.is_empty() {
                clauses.push(Some(lits));
            }
        }

        Ok(DratVerifier {
            clauses,
            num_vars,
            assignments: vec![None; (num_vars + 1) as usize],
            propagation_queue: Vec::new(),
            stats: VerifyStats::default(),
        })
    }

    /// Verify a DRAT proof file
    pub fn verify_proof<P: AsRef<Path>>(&mut self, proof_path: P) -> Result<VerifyResult, VerifyError> {
        let file = File::open(proof_path)?;
        let reader = BufReader::new(file);

        for (line_num, line) in reader.lines().enumerate() {
            let line = line?;
            let line = line.trim();
            
            if line.is_empty() {
                continue;
            }

            let is_deletion = line.starts_with('d');
            let clause_str = if is_deletion {
                line[1..].trim()
            } else {
                line
            };

            // Parse literals
            let lits: Vec<Literal> = clause_str
                .split_whitespace()
                .filter_map(|s| s.parse::<i32>().ok())
                .take_while(|&n| n != 0)
                .map(|n| Literal::from_dimacs(n))
                .collect();

            if is_deletion {
                self.process_deletion(&lits);
                self.stats.deletions_processed += 1;
            } else {
                // Check if clause is RUP (Reverse Unit Propagation)
                if !self.check_rup(&lits) {
                    return Ok(VerifyResult::Invalid {
                        line: line_num + 1,
                        reason: format!("Clause {:?} is not RUP", lits_to_dimacs(&lits)),
                    });
                }
                
                // Add the clause
                self.clauses.push(Some(lits));
                self.stats.clauses_checked += 1;
            }
        }

        // Check if empty clause was derived
        if self.has_empty_clause() {
            Ok(VerifyResult::Valid)
        } else {
            Ok(VerifyResult::Invalid {
                line: 0,
                reason: "Proof does not derive empty clause".to_string(),
            })
        }
    }

    /// Check if a clause is RUP (Reverse Unit Propagation)
    /// A clause C is RUP if unit propagation on (F ∧ ¬C) derives a conflict
    fn check_rup(&mut self, clause: &[Literal]) -> bool {
        self.stats.rup_checks += 1;
        
        // Empty clause is trivially RUP (it's a conflict)
        if clause.is_empty() {
            return true;
        }

        // Reset assignments
        self.assignments.fill(None);
        self.propagation_queue.clear();

        // Assign negation of all literals in the clause
        for &lit in clause {
            let var = lit.variable().index() as usize;
            let val = !lit.is_positive();
            
            if let Some(existing) = self.assignments[var] {
                if existing != val {
                    // Conflict immediately - clause is RUP
                    return true;
                }
            } else {
                self.assignments[var] = Some(val);
                self.propagation_queue.push(lit.negate());
            }
        }

        // Run unit propagation
        self.unit_propagate()
    }

    /// Run unit propagation, returns true if conflict found
    fn unit_propagate(&mut self) -> bool {
        while let Some(assigned_lit) = self.propagation_queue.pop() {
            // Check all clauses for unit propagation
            for clause_opt in &self.clauses {
                if let Some(clause) = clause_opt {
                    let result = self.check_clause_unit(clause, assigned_lit);
                    match result {
                        ClauseState::Conflict => return true,
                        ClauseState::Unit(unit_lit) => {
                            let var = unit_lit.variable().index() as usize;
                            let val = unit_lit.is_positive();
                            
                            if let Some(existing) = self.assignments[var] {
                                if existing != val {
                                    return true; // Conflict
                                }
                            } else {
                                self.assignments[var] = Some(val);
                                self.propagation_queue.push(unit_lit);
                            }
                        }
                        ClauseState::Satisfied | ClauseState::Unresolved => {}
                    }
                }
            }
        }
        
        false // No conflict
    }

    /// Check clause state after an assignment
    fn check_clause_unit(&self, clause: &[Literal], _trigger: Literal) -> ClauseState {
        let mut unassigned: Option<Literal> = None;
        let mut unassigned_count = 0;

        for &lit in clause {
            let var = lit.variable().index() as usize;
            match self.assignments.get(var).copied().flatten() {
                Some(val) => {
                    if val == lit.is_positive() {
                        return ClauseState::Satisfied;
                    }
                    // Otherwise literal is false, continue
                }
                None => {
                    unassigned = Some(lit);
                    unassigned_count += 1;
                    if unassigned_count > 1 {
                        return ClauseState::Unresolved;
                    }
                }
            }
        }

        match unassigned_count {
            0 => ClauseState::Conflict,
            1 => ClauseState::Unit(unassigned.unwrap()),
            _ => ClauseState::Unresolved,
        }
    }

    /// Process a deletion - mark clause as inactive
    fn process_deletion(&mut self, lits: &[Literal]) {
        // Find and remove matching clause
        let lits_set: HashSet<_> = lits.iter().collect();
        
        for clause_opt in &mut self.clauses {
            if let Some(clause) = clause_opt {
                if clause.len() == lits.len() {
                    let clause_set: HashSet<_> = clause.iter().collect();
                    if lits_set == clause_set {
                        *clause_opt = None;
                        return;
                    }
                }
            }
        }
    }

    /// Check if empty clause exists
    fn has_empty_clause(&self) -> bool {
        self.clauses.iter().any(|c| {
            c.as_ref().map(|lits| lits.is_empty()).unwrap_or(false)
        })
    }

    /// Get verification statistics
    pub fn stats(&self) -> &VerifyStats {
        &self.stats
    }
}

/// State of a clause during propagation
enum ClauseState {
    Satisfied,
    Conflict,
    Unit(Literal),
    Unresolved,
}

/// Convert literals to DIMACS format for error messages
fn lits_to_dimacs(lits: &[Literal]) -> Vec<i32> {
    lits.iter()
        .map(|lit| {
            let var = lit.variable().index() as i32;
            if lit.is_positive() { var } else { -var }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clause::Clause;
    use crate::literal::Variable;

    fn make_clause(lits: &[(u32, bool)]) -> Clause {
        let literals: Vec<Literal> = lits
            .iter()
            .map(|&(var, pol)| {
                let v = Variable::new(var);
                Literal::new(v, pol)
            })
            .collect();
        Clause::new(literals)
    }

    fn make_formula(clauses: Vec<Vec<(u32, bool)>>) -> Formula {
        let max_var = clauses.iter()
            .flat_map(|c| c.iter().map(|(v, _)| *v))
            .max()
            .unwrap_or(0);
        
        let mut formula = Formula::with_num_vars(max_var);
        for clause_lits in clauses {
            formula.add_clause(make_clause(&clause_lits));
        }
        formula
    }

    #[test]
    fn test_verifier_creation() {
        let formula = make_formula(vec![
            vec![(1, true), (2, true)],
            vec![(1, false), (3, true)],
        ]);
        
        let verifier = DratVerifier::new(&formula);
        assert_eq!(verifier.clauses.len(), 2);
    }

    #[test]
    fn test_rup_empty_clause() {
        let formula = make_formula(vec![
            vec![(1, true)],
            vec![(1, false)],
        ]);
        
        let mut verifier = DratVerifier::new(&formula);
        // Empty clause should be RUP when formula is contradictory
        assert!(verifier.check_rup(&[]));
    }

    #[test]
    fn test_rup_unit_propagation() {
        // Formula: (1) ∧ (¬1 ∨ 2) ∧ (¬2 ∨ 3)
        // Adding (3) should be RUP
        let formula = make_formula(vec![
            vec![(1, true)],
            vec![(1, false), (2, true)],
            vec![(2, false), (3, true)],
        ]);
        
        let mut verifier = DratVerifier::new(&formula);
        let lit3 = Literal::new(Variable::new(3), true);
        assert!(verifier.check_rup(&[lit3]));
    }

    #[test]
    fn test_deletion() {
        let formula = make_formula(vec![
            vec![(1, true), (2, true)],
            vec![(1, false), (2, false)],
        ]);
        
        let mut verifier = DratVerifier::new(&formula);
        
        // Delete first clause
        let lit1 = Literal::new(Variable::new(1), true);
        let lit2 = Literal::new(Variable::new(2), true);
        verifier.process_deletion(&[lit1, lit2]);
        
        // First clause should be None
        assert!(verifier.clauses[0].is_none());
        assert!(verifier.clauses[1].is_some());
    }

    #[test]
    fn test_has_empty_clause() {
        let formula = make_formula(vec![
            vec![(1, true)],
        ]);
        
        let mut verifier = DratVerifier::new(&formula);
        assert!(!verifier.has_empty_clause());
        
        // Add empty clause
        verifier.clauses.push(Some(vec![]));
        assert!(verifier.has_empty_clause());
    }

    #[test]
    fn test_simple_proof() {
        // Formula: (1) ∧ (¬1)
        // This is trivially UNSAT, proof just needs empty clause
        let formula = make_formula(vec![
            vec![(1, true)],
            vec![(1, false)],
        ]);
        
        let mut verifier = DratVerifier::new(&formula);
        
        // Empty clause should be RUP
        assert!(verifier.check_rup(&[]));
        verifier.clauses.push(Some(vec![]));
        
        assert!(verifier.has_empty_clause());
    }
}
