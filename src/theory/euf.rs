//! EUF (Equality with Uninterpreted Functions) Theory Solver
//!
//! Implements congruence closure for deciding equality constraints
//! with uninterpreted functions.

use super::{TheoryConflict, TheoryPropagation, TheoryResult, TheorySolver};
use crate::literal::Literal;
use std::collections::HashMap;

/// A term in the EUF theory
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EufTerm {
    /// A constant or variable
    Const(u32),
    /// Function application: f(arg1, arg2, ...)
    App { func: u32, args: Vec<TermId> },
}

/// Term identifier (index into term storage)
pub type TermId = u32;

/// An equality or disequality constraint
#[derive(Debug, Clone)]
pub struct EufConstraint {
    /// Left-hand side term
    pub lhs: TermId,
    /// Right-hand side term
    pub rhs: TermId,
    /// True for equality, false for disequality
    pub is_equality: bool,
    /// The SAT literal that implies this constraint
    pub literal: Literal,
    /// Decision level when this was asserted
    pub level: u32,
}

/// Union-find node for congruence closure
#[derive(Debug, Clone)]
struct UnionFindNode {
    /// Parent in union-find tree (self if root)
    parent: TermId,
    /// Rank for union by rank
    rank: u32,
    /// The proof edge (for explanation generation)
    /// If Some((other, literal)), this node was merged with other due to literal
    proof_edge: Option<(TermId, Literal)>,
}

/// Signature for congruence closure
/// Two function applications are congruent if they have the same function
/// and their arguments are in the same equivalence classes
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Signature {
    func: u32,
    arg_classes: Vec<TermId>,
}

/// EUF Theory Solver
pub struct EufSolver {
    /// Term storage
    terms: Vec<EufTerm>,
    /// Union-find nodes
    nodes: Vec<UnionFindNode>,
    /// Pending congruences to process
    pending: Vec<(TermId, TermId, Literal)>,
    /// Signature table for congruence closure
    /// Maps signature -> term with that signature
    signatures: HashMap<Signature, TermId>,
    /// All function applications (for congruence checking)
    apps: Vec<TermId>,
    /// Asserted disequalities
    disequalities: Vec<(TermId, TermId, Literal)>,
    /// Trail of merges for backtracking (level, term1, term2)
    merge_trail: Vec<(u32, TermId, TermId)>,
    /// Current decision level
    level: u32,
    /// Level markers in merge_trail
    level_markers: Vec<usize>,
    /// Propagated literals (for explain)
    propagated: HashMap<Literal, Vec<Literal>>,
}

impl EufSolver {
    /// Create a new EUF solver
    pub fn new() -> Self {
        EufSolver {
            terms: Vec::new(),
            nodes: Vec::new(),
            pending: Vec::new(),
            signatures: HashMap::new(),
            apps: Vec::new(),
            disequalities: Vec::new(),
            merge_trail: Vec::new(),
            level: 0,
            level_markers: vec![0],
            propagated: HashMap::new(),
        }
    }

    /// Add a constant term
    pub fn add_const(&mut self, id: u32) -> TermId {
        let term_id = self.terms.len() as TermId;
        self.terms.push(EufTerm::Const(id));
        self.nodes.push(UnionFindNode {
            parent: term_id,
            rank: 0,
            proof_edge: None,
        });
        term_id
    }

    /// Add a function application term
    pub fn add_app(&mut self, func: u32, args: Vec<TermId>) -> TermId {
        let term_id = self.terms.len() as TermId;
        self.terms.push(EufTerm::App { func, args: args.clone() });
        self.nodes.push(UnionFindNode {
            parent: term_id,
            rank: 0,
            proof_edge: None,
        });
        
        // Record this application for congruence checking
        self.apps.push(term_id);
        
        // Add to signature table
        let sig = self.get_signature(term_id);
        if let Some(sig) = sig {
            self.signatures.insert(sig, term_id);
        }
        
        term_id
    }

    /// Get the signature of a term (if it's a function application)
    fn get_signature(&self, term: TermId) -> Option<Signature> {
        match &self.terms[term as usize] {
            EufTerm::App { func, args } => {
                let arg_classes: Vec<TermId> = args.iter()
                    .map(|&a| self.find(a))
                    .collect();
                Some(Signature { func: *func, arg_classes })
            }
            EufTerm::Const(_) => None,
        }
    }

    /// Find the representative of a term's equivalence class (with path compression)
    pub fn find(&self, term: TermId) -> TermId {
        let node = &self.nodes[term as usize];
        if node.parent == term {
            term
        } else {
            self.find(node.parent)
        }
    }

    /// Find with path compression (mutable version for optimization)
    fn find_mut(&mut self, term: TermId) -> TermId {
        let parent = self.nodes[term as usize].parent;
        if parent == term {
            term
        } else {
            let root = self.find_mut(parent);
            self.nodes[term as usize].parent = root;
            root
        }
    }

    /// Check if two terms are in the same equivalence class
    pub fn are_equal(&self, a: TermId, b: TermId) -> bool {
        self.find(a) == self.find(b)
    }

    /// Merge two equivalence classes
    fn merge(&mut self, a: TermId, b: TermId, reason: Literal) {
        let root_a = self.find_mut(a);
        let root_b = self.find_mut(b);

        if root_a == root_b {
            return; // Already in same class
        }

        // Union by rank
        let (new_root, old_root) = {
            let rank_a = self.nodes[root_a as usize].rank;
            let rank_b = self.nodes[root_b as usize].rank;
            if rank_a < rank_b {
                (root_b, root_a)
            } else {
                (root_a, root_b)
            }
        };

        // Record merge for backtracking
        self.merge_trail.push((self.level, new_root, old_root));

        // Update parent and proof edge
        self.nodes[old_root as usize].parent = new_root;
        self.nodes[old_root as usize].proof_edge = Some((new_root, reason));

        // Update rank if necessary
        if self.nodes[new_root as usize].rank == self.nodes[old_root as usize].rank {
            self.nodes[new_root as usize].rank += 1;
        }

        // Queue congruence checks
        self.queue_congruences(old_root, new_root, reason);
    }

    /// Queue congruence checks after a merge
    fn queue_congruences(&mut self, _old_root: TermId, new_root: TermId, reason: Literal) {
        // Find all function applications that might become congruent
        for &app_id in &self.apps {
            if let EufTerm::App { args, .. } = &self.terms[app_id as usize] {
                // Check if any argument's class was affected by the merge
                let affected = args.iter().any(|&arg| {
                    let root = self.find(arg);
                    root == new_root
                });

                if affected {
                    // Recompute signature and check for congruence
                    if let Some(new_sig) = self.get_signature(app_id) {
                        if let Some(&other) = self.signatures.get(&new_sig) {
                            if other != app_id && !self.are_equal(app_id, other) {
                                // Found congruence: f(a) = f(b) because a = b
                                self.pending.push((app_id, other, reason));
                            }
                        }
                    }
                }
            }
        }
    }

    /// Process pending congruences
    fn process_pending(&mut self) -> TheoryResult<()> {
        while let Some((a, b, _reason)) = self.pending.pop() {
            if !self.are_equal(a, b) {
                // Create a synthetic reason for the congruence
                // (In a full implementation, we'd track the exact reason)
                let congruence_reason = self.explain_congruence(a, b);
                
                // Check for conflict with disequalities
                for (lhs, rhs, diseq_lit) in &self.disequalities {
                    if (self.are_equal(a, *lhs) && self.are_equal(b, *rhs)) ||
                       (self.are_equal(a, *rhs) && self.are_equal(b, *lhs)) {
                        // Conflict: we're about to make a = b, but a != b was asserted
                        let mut explanation = congruence_reason.clone();
                        explanation.push(*diseq_lit);
                        return Err(TheoryConflict::new(explanation));
                    }
                }

                // For congruences, we use a placeholder literal
                // (Real implementation would track the actual reason)
                if let Some(&reason_lit) = congruence_reason.first() {
                    self.merge(a, b, reason_lit);
                }
            }
        }
        Ok(())
    }

    /// Explain why a congruence holds
    fn explain_congruence(&self, a: TermId, b: TermId) -> Vec<Literal> {
        let mut explanation = Vec::new();

        if let (EufTerm::App { func: f1, args: args1 }, EufTerm::App { func: f2, args: args2 }) = 
            (&self.terms[a as usize], &self.terms[b as usize]) {
            if f1 == f2 && args1.len() == args2.len() {
                // Explain why each pair of arguments is equal
                for (&arg1, &arg2) in args1.iter().zip(args2.iter()) {
                    if !self.are_equal(arg1, arg2) {
                        continue;
                    }
                    // Find explanation for arg1 = arg2
                    explanation.extend(self.explain_equality(arg1, arg2));
                }
            }
        }

        explanation
    }

    /// Explain why two terms are equal (find path in union-find with proof edges)
    fn explain_equality(&self, a: TermId, b: TermId) -> Vec<Literal> {
        if a == b {
            return Vec::new();
        }

        let mut explanation = Vec::new();
        
        // Find path from a to root
        let mut path_a = Vec::new();
        let mut current = a;
        while self.nodes[current as usize].parent != current {
            path_a.push(current);
            if let Some((_, lit)) = self.nodes[current as usize].proof_edge {
                explanation.push(lit);
            }
            current = self.nodes[current as usize].parent;
        }
        path_a.push(current); // Add root

        // Find path from b to root
        let mut current = b;
        while self.nodes[current as usize].parent != current {
            if let Some((_, lit)) = self.nodes[current as usize].proof_edge {
                explanation.push(lit);
            }
            current = self.nodes[current as usize].parent;
        }

        explanation
    }

    /// Assert an equality constraint
    pub fn assert_equality(&mut self, lhs: TermId, rhs: TermId, literal: Literal) -> TheoryResult<()> {
        self.merge(lhs, rhs, literal);
        self.process_pending()
    }

    /// Assert a disequality constraint
    pub fn assert_disequality(&mut self, lhs: TermId, rhs: TermId, literal: Literal) -> TheoryResult<()> {
        // Check if already equal
        if self.are_equal(lhs, rhs) {
            // Conflict: asserting a != b when a = b
            let mut explanation = self.explain_equality(lhs, rhs);
            explanation.push(literal);
            return Err(TheoryConflict::new(explanation));
        }

        // Record the disequality
        self.disequalities.push((lhs, rhs, literal));
        Ok(())
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

    fn assert_literal(&mut self, _lit: Literal) -> TheoryResult<()> {
        // In a full implementation, we'd decode the literal to determine
        // if it's an equality or disequality, and which terms are involved.
        // For now, we rely on direct calls to assert_equality/assert_disequality.
        Ok(())
    }

    fn check(&mut self) -> TheoryResult<()> {
        // Check all disequalities against current equivalence classes
        for (lhs, rhs, lit) in self.disequalities.clone() {
            if self.are_equal(lhs, rhs) {
                let mut explanation = self.explain_equality(lhs, rhs);
                explanation.push(lit);
                return Err(TheoryConflict::new(explanation));
            }
        }
        Ok(())
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        // EUF propagation would involve detecting equalities that must hold
        // based on the current state. For now, return empty.
        Vec::new()
    }

    fn explain(&self, lit: Literal) -> Vec<Literal> {
        self.propagated.get(&lit).cloned().unwrap_or_default()
    }

    fn backtrack(&mut self, level: u32) {
        self.level = level;

        // Undo merges
        while let Some(&(merge_level, _new_root, old_root)) = self.merge_trail.last() {
            if merge_level <= level {
                break;
            }
            
            // Restore old_root's parent to itself
            self.nodes[old_root as usize].parent = old_root;
            self.nodes[old_root as usize].proof_edge = None;
            
            self.merge_trail.pop();
        }

        // Remove disequalities from higher levels
        // (Note: this is simplified; real impl would track levels properly)
    }

    fn push_level(&mut self) {
        self.level += 1;
        self.level_markers.push(self.merge_trail.len());
    }

    fn current_level(&self) -> u32 {
        self.level
    }

    fn reset(&mut self) {
        self.terms.clear();
        self.nodes.clear();
        self.pending.clear();
        self.signatures.clear();
        self.apps.clear();
        self.disequalities.clear();
        self.merge_trail.clear();
        self.level = 0;
        self.level_markers = vec![0];
        self.propagated.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Variable;

    fn lit(var: u32, positive: bool) -> Literal {
        Literal::new(Variable::new(var), positive)
    }

    #[test]
    fn test_euf_basic_equality() {
        let mut solver = EufSolver::new();
        
        let a = solver.add_const(1);
        let b = solver.add_const(2);
        
        assert!(!solver.are_equal(a, b));
        
        solver.assert_equality(a, b, lit(1, true)).unwrap();
        
        assert!(solver.are_equal(a, b));
    }

    #[test]
    fn test_euf_transitivity() {
        let mut solver = EufSolver::new();
        
        let a = solver.add_const(1);
        let b = solver.add_const(2);
        let c = solver.add_const(3);
        
        solver.assert_equality(a, b, lit(1, true)).unwrap();
        solver.assert_equality(b, c, lit(2, true)).unwrap();
        
        // a = b and b = c implies a = c
        assert!(solver.are_equal(a, c));
    }

    #[test]
    fn test_euf_disequality_conflict() {
        let mut solver = EufSolver::new();
        
        let a = solver.add_const(1);
        let b = solver.add_const(2);
        
        // Assert a = b
        solver.assert_equality(a, b, lit(1, true)).unwrap();
        
        // Assert a != b - should conflict
        let result = solver.assert_disequality(a, b, lit(2, true));
        assert!(result.is_err());
    }

    #[test]
    fn test_euf_disequality_ok() {
        let mut solver = EufSolver::new();
        
        let a = solver.add_const(1);
        let b = solver.add_const(2);
        
        // Assert a != b when they're not equal - should be fine
        let result = solver.assert_disequality(a, b, lit(1, true));
        assert!(result.is_ok());
    }

    #[test]
    fn test_euf_congruence() {
        let mut solver = EufSolver::new();
        
        let a = solver.add_const(1);
        let b = solver.add_const(2);
        
        // f(a) and f(b)
        let fa = solver.add_app(1, vec![a]);
        let fb = solver.add_app(1, vec![b]);
        
        assert!(!solver.are_equal(fa, fb));
        
        // Assert a = b
        solver.assert_equality(a, b, lit(1, true)).unwrap();
        
        // Process congruences - now f(a) = f(b) should hold
        // Note: in the current implementation, congruence is queued but
        // might not be automatically processed. Let's check manually.
        solver.process_pending().unwrap();
        
        // After congruence closure, f(a) = f(b)
        assert!(solver.are_equal(fa, fb));
    }

    #[test]
    fn test_euf_backtrack() {
        let mut solver = EufSolver::new();
        
        let a = solver.add_const(1);
        let b = solver.add_const(2);
        let c = solver.add_const(3);
        
        // Level 0: a = b
        solver.assert_equality(a, b, lit(1, true)).unwrap();
        assert!(solver.are_equal(a, b));
        
        // Level 1: b = c
        solver.push_level();
        solver.assert_equality(b, c, lit(2, true)).unwrap();
        assert!(solver.are_equal(a, c));
        
        // Backtrack to level 0
        solver.backtrack(0);
        
        // a = b should still hold
        assert!(solver.are_equal(a, b));
        // b = c should NOT hold
        assert!(!solver.are_equal(b, c));
    }

    #[test]
    fn test_euf_check_consistency() {
        let mut solver = EufSolver::new();
        
        let a = solver.add_const(1);
        let b = solver.add_const(2);
        
        // Assert a != b
        solver.assert_disequality(a, b, lit(1, true)).unwrap();
        
        // Check should pass
        assert!(solver.check().is_ok());
        
        // Now assert a = b
        solver.assert_equality(a, b, lit(2, true)).unwrap();
        
        // Check should fail
        assert!(solver.check().is_err());
    }

    #[test]
    fn test_euf_explain_equality() {
        let mut solver = EufSolver::new();
        
        let a = solver.add_const(1);
        let b = solver.add_const(2);
        let c = solver.add_const(3);
        
        let lit1 = lit(1, true);
        let lit2 = lit(2, true);
        
        solver.assert_equality(a, b, lit1).unwrap();
        solver.assert_equality(b, c, lit2).unwrap();
        
        // Explanation for a = c should include both assertions
        let explanation = solver.explain_equality(a, c);
        assert!(!explanation.is_empty());
    }

    #[test]
    fn test_euf_multiple_args() {
        let mut solver = EufSolver::new();
        
        let a = solver.add_const(1);
        let b = solver.add_const(2);
        let c = solver.add_const(3);
        let d = solver.add_const(4);
        
        // f(a, c) and f(b, d)
        let f_ac = solver.add_app(1, vec![a, c]);
        let f_bd = solver.add_app(1, vec![b, d]);
        
        // Assert a = b and c = d
        solver.assert_equality(a, b, lit(1, true)).unwrap();
        solver.assert_equality(c, d, lit(2, true)).unwrap();
        
        // Process congruences
        solver.process_pending().unwrap();
        
        // f(a, c) = f(b, d) should hold
        assert!(solver.are_equal(f_ac, f_bd));
    }

    #[test]
    fn test_euf_reset() {
        let mut solver = EufSolver::new();
        
        let a = solver.add_const(1);
        let b = solver.add_const(2);
        
        solver.assert_equality(a, b, lit(1, true)).unwrap();
        
        solver.reset();
        
        // After reset, solver should be empty
        assert!(solver.terms.is_empty());
        assert_eq!(solver.level, 0);
    }
}
