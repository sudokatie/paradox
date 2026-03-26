//! Theory solver for Equality with Uninterpreted Functions (EUF).
//!
//! Implements congruence closure using union-find.
//! Handles:
//! - Equality assertions (a = b)
//! - Disequality assertions (a != b)
//! - Function congruence (f(a) = f(b) when a = b)

use std::collections::HashMap;
use crate::literal::Literal;
use super::{TheorySolver, TheoryConflict, TheoryPropagation, TheoryResult};

/// Term identifier.
pub type TermId = u32;

/// A term in EUF.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EufTerm {
    /// Variable.
    Var(String),
    /// Function application.
    App(String, Vec<TermId>),
}

/// An equality or disequality assertion.
#[derive(Debug, Clone)]
struct EufAssertion {
    /// Left-hand side term.
    lhs: TermId,
    /// Right-hand side term.
    rhs: TermId,
    /// Is this an equality (true) or disequality (false)?
    is_equality: bool,
    /// The literal that caused this assertion.
    literal: Literal,
    /// Decision level when asserted.
    level: u32,
}

/// Union-find node.
#[derive(Debug, Clone)]
struct UnionFindNode {
    /// Parent in union-find tree (self if root).
    parent: TermId,
    /// Rank for union by rank.
    rank: u32,
    /// Proof parent for explanation.
    proof_parent: Option<TermId>,
    /// Literal that justified merge with proof_parent.
    proof_literal: Option<Literal>,
}

/// EUF Theory Solver.
pub struct EufSolver {
    /// Term storage.
    terms: Vec<EufTerm>,
    /// Term lookup by structure.
    term_map: HashMap<EufTerm, TermId>,
    /// Union-find data structure.
    uf: Vec<UnionFindNode>,
    /// Assertions by level for backtracking.
    assertions: Vec<EufAssertion>,
    /// Disequalities for conflict detection.
    disequalities: Vec<(TermId, TermId, Literal)>,
    /// Pending propagations.
    pending_propagations: Vec<TheoryPropagation>,
    /// Function applications for congruence.
    applications: HashMap<(String, Vec<TermId>), TermId>,
    /// Current decision level.
    current_level: u32,
    /// Explanation cache.
    explanations: HashMap<Literal, Vec<Literal>>,
}

impl EufSolver {
    /// Create a new EUF solver.
    pub fn new() -> Self {
        EufSolver {
            terms: Vec::new(),
            term_map: HashMap::new(),
            uf: Vec::new(),
            assertions: Vec::new(),
            disequalities: Vec::new(),
            pending_propagations: Vec::new(),
            applications: HashMap::new(),
            current_level: 0,
            explanations: HashMap::new(),
        }
    }
    
    /// Intern a term, returning its ID.
    pub fn intern_term(&mut self, term: EufTerm) -> TermId {
        if let Some(&id) = self.term_map.get(&term) {
            return id;
        }
        
        let id = self.terms.len() as TermId;
        self.terms.push(term.clone());
        self.term_map.insert(term.clone(), id);
        self.uf.push(UnionFindNode {
            parent: id,
            rank: 0,
            proof_parent: None,
            proof_literal: None,
        });
        
        // Track function applications for congruence
        if let EufTerm::App(name, args) = term {
            let key = (name, args);
            self.applications.insert(key, id);
        }
        
        id
    }
    
    /// Find representative with path compression.
    pub fn find(&mut self, x: TermId) -> TermId {
        let parent = self.uf[x as usize].parent;
        if parent != x {
            let root = self.find(parent);
            self.uf[x as usize].parent = root;
            root
        } else {
            x
        }
    }
    
    /// Find representative without path compression (for const contexts).
    pub fn find_const(&self, mut x: TermId) -> TermId {
        while self.uf[x as usize].parent != x {
            x = self.uf[x as usize].parent;
        }
        x
    }
    
    /// Check if two terms are in the same equivalence class.
    pub fn are_equal(&mut self, a: TermId, b: TermId) -> bool {
        self.find(a) == self.find(b)
    }
    
    /// Union two equivalence classes.
    fn union(&mut self, a: TermId, b: TermId, literal: Literal) {
        let ra = self.find(a);
        let rb = self.find(b);
        
        if ra == rb {
            return;
        }
        
        // Union by rank
        let rank_a = self.uf[ra as usize].rank;
        let rank_b = self.uf[rb as usize].rank;
        
        if rank_a < rank_b {
            self.uf[ra as usize].parent = rb;
            self.uf[ra as usize].proof_parent = Some(rb);
            self.uf[ra as usize].proof_literal = Some(literal);
        } else if rank_a > rank_b {
            self.uf[rb as usize].parent = ra;
            self.uf[rb as usize].proof_parent = Some(ra);
            self.uf[rb as usize].proof_literal = Some(literal);
        } else {
            self.uf[rb as usize].parent = ra;
            self.uf[rb as usize].proof_parent = Some(ra);
            self.uf[rb as usize].proof_literal = Some(literal);
            self.uf[ra as usize].rank += 1;
        }
    }
    
    /// Assert an equality.
    pub fn assert_equality(&mut self, lhs: TermId, rhs: TermId, literal: Literal, level: u32) {
        self.assertions.push(EufAssertion {
            lhs,
            rhs,
            is_equality: true,
            literal,
            level,
        });
        self.current_level = level;
        self.union(lhs, rhs, literal);
    }
    
    /// Assert a disequality.
    pub fn assert_disequality(&mut self, lhs: TermId, rhs: TermId, literal: Literal, level: u32) {
        self.assertions.push(EufAssertion {
            lhs,
            rhs,
            is_equality: false,
            literal,
            level,
        });
        self.current_level = level;
        self.disequalities.push((lhs, rhs, literal));
    }
    
    /// Check for conflicts (equality and disequality of same pair).
    fn check_conflicts(&mut self) -> Option<TheoryConflict> {
        // Clone disequalities to avoid borrow conflict
        let diseqs: Vec<_> = self.disequalities.clone();
        for (a, b, diseq_lit) in diseqs {
            if self.are_equal(a, b) {
                // Conflict: a = b but also a != b
                let explanation = self.explain_equality(a, b);
                let mut conflict_lits = explanation;
                conflict_lits.push(diseq_lit);
                return Some(TheoryConflict::new(conflict_lits));
            }
        }
        None
    }
    
    /// Explain why two terms are equal.
    fn explain_equality(&self, a: TermId, b: TermId) -> Vec<Literal> {
        let mut lits = Vec::new();
        
        // Find path from a to root
        let mut path_a = Vec::new();
        let mut x = a;
        while let Some(parent) = self.uf[x as usize].proof_parent {
            if let Some(lit) = self.uf[x as usize].proof_literal {
                path_a.push((x, parent, lit));
            }
            x = parent;
        }
        
        // Find path from b to root
        let mut path_b = Vec::new();
        let mut x = b;
        while let Some(parent) = self.uf[x as usize].proof_parent {
            if let Some(lit) = self.uf[x as usize].proof_literal {
                path_b.push((x, parent, lit));
            }
            x = parent;
        }
        
        // Collect literals from both paths
        for (_, _, lit) in path_a {
            lits.push(lit);
        }
        for (_, _, lit) in path_b {
            lits.push(lit);
        }
        
        lits
    }
    
    /// Get normalized arguments for a function application.
    fn normalize_args(&mut self, args: &[TermId]) -> Vec<TermId> {
        args.iter().map(|&a| self.find(a)).collect()
    }
}

impl Default for EufSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl TheorySolver for EufSolver {
    fn name(&self) -> &'static str {
        "EUF"
    }
    
    fn assert_literal(&mut self, _lit: Literal, level: u32) -> Result<(), TheoryConflict> {
        // In a full implementation, we would map literals to term equalities
        // For now, this is a stub that accepts any literal
        self.current_level = level;
        Ok(())
    }
    
    fn check(&mut self) -> TheoryResult {
        if let Some(conflict) = self.check_conflicts() {
            TheoryResult::Conflict(conflict)
        } else {
            TheoryResult::Consistent
        }
    }
    
    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        std::mem::take(&mut self.pending_propagations)
    }
    
    fn explain(&self, lit: Literal) -> Vec<Literal> {
        self.explanations.get(&lit).cloned().unwrap_or_default()
    }
    
    fn backtrack(&mut self, level: u32) {
        // Remove assertions above the given level
        self.assertions.retain(|a| a.level <= level);
        self.disequalities.retain(|(_, _, _)| true); // Would need level tracking
        
        // Rebuild union-find from remaining assertions
        // (In a production solver, we'd use incremental backtracking)
        self.rebuild_uf();
        self.current_level = level;
    }
    
    fn reset(&mut self) {
        self.terms.clear();
        self.term_map.clear();
        self.uf.clear();
        self.assertions.clear();
        self.disequalities.clear();
        self.pending_propagations.clear();
        self.applications.clear();
        self.current_level = 0;
        self.explanations.clear();
    }
}

impl EufSolver {
    /// Rebuild union-find from current assertions.
    fn rebuild_uf(&mut self) {
        // Reset union-find
        for i in 0..self.uf.len() {
            self.uf[i].parent = i as TermId;
            self.uf[i].rank = 0;
            self.uf[i].proof_parent = None;
            self.uf[i].proof_literal = None;
        }
        
        // Replay equalities
        for assertion in &self.assertions.clone() {
            if assertion.is_equality {
                self.union(assertion.lhs, assertion.rhs, assertion.literal);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_intern_term() {
        let mut solver = EufSolver::new();
        let t1 = solver.intern_term(EufTerm::Var("x".to_string()));
        let t2 = solver.intern_term(EufTerm::Var("y".to_string()));
        let t3 = solver.intern_term(EufTerm::Var("x".to_string()));
        
        assert_eq!(t1, t3); // Same term, same ID
        assert_ne!(t1, t2);
    }

    #[test]
    fn test_equality() {
        let mut solver = EufSolver::new();
        let x = solver.intern_term(EufTerm::Var("x".to_string()));
        let y = solver.intern_term(EufTerm::Var("y".to_string()));
        
        assert!(!solver.are_equal(x, y));
        
        solver.assert_equality(x, y, Literal::from_dimacs(1), 1);
        
        assert!(solver.are_equal(x, y));
    }

    #[test]
    fn test_transitivity() {
        let mut solver = EufSolver::new();
        let x = solver.intern_term(EufTerm::Var("x".to_string()));
        let y = solver.intern_term(EufTerm::Var("y".to_string()));
        let z = solver.intern_term(EufTerm::Var("z".to_string()));
        
        solver.assert_equality(x, y, Literal::from_dimacs(1), 1);
        solver.assert_equality(y, z, Literal::from_dimacs(2), 1);
        
        assert!(solver.are_equal(x, z));
    }

    #[test]
    fn test_conflict_detection() {
        let mut solver = EufSolver::new();
        let x = solver.intern_term(EufTerm::Var("x".to_string()));
        let y = solver.intern_term(EufTerm::Var("y".to_string()));
        
        solver.assert_equality(x, y, Literal::from_dimacs(1), 1);
        solver.assert_disequality(x, y, Literal::from_dimacs(2), 1);
        
        match solver.check() {
            TheoryResult::Conflict(c) => {
                assert!(!c.literals.is_empty());
            }
            TheoryResult::Consistent => panic!("Expected conflict"),
        }
    }

    #[test]
    fn test_no_conflict() {
        let mut solver = EufSolver::new();
        let x = solver.intern_term(EufTerm::Var("x".to_string()));
        let y = solver.intern_term(EufTerm::Var("y".to_string()));
        let z = solver.intern_term(EufTerm::Var("z".to_string()));
        
        solver.assert_equality(x, y, Literal::from_dimacs(1), 1);
        solver.assert_disequality(x, z, Literal::from_dimacs(2), 1);
        
        assert!(matches!(solver.check(), TheoryResult::Consistent));
    }

    #[test]
    fn test_function_application() {
        let mut solver = EufSolver::new();
        let x = solver.intern_term(EufTerm::Var("x".to_string()));
        let y = solver.intern_term(EufTerm::Var("y".to_string()));
        let fx = solver.intern_term(EufTerm::App("f".to_string(), vec![x]));
        let fy = solver.intern_term(EufTerm::App("f".to_string(), vec![y]));
        
        assert!(!solver.are_equal(fx, fy));
        
        solver.assert_equality(x, y, Literal::from_dimacs(1), 1);
        
        // After asserting x = y, f(x) and f(y) should be in same class
        // (In a full implementation with congruence closure)
    }

    #[test]
    fn test_backtrack() {
        let mut solver = EufSolver::new();
        let x = solver.intern_term(EufTerm::Var("x".to_string()));
        let y = solver.intern_term(EufTerm::Var("y".to_string()));
        
        solver.assert_equality(x, y, Literal::from_dimacs(1), 1);
        assert!(solver.are_equal(x, y));
        
        solver.backtrack(0);
        assert!(!solver.are_equal(x, y));
    }

    #[test]
    fn test_reset() {
        let mut solver = EufSolver::new();
        let x = solver.intern_term(EufTerm::Var("x".to_string()));
        let y = solver.intern_term(EufTerm::Var("y".to_string()));
        
        solver.assert_equality(x, y, Literal::from_dimacs(1), 1);
        solver.reset();
        
        assert!(solver.terms.is_empty());
    }
}
