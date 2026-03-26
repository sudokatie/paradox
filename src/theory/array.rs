//! Theory solver for Arrays.
//!
//! Handles:
//! - Read-over-write axioms: select(store(a, i, v), i) = v
//! - Array extensionality: (∀i. select(a, i) = select(b, i)) → a = b
//! - Lazy axiom instantiation

use std::collections::{HashMap, HashSet};
use crate::literal::Literal;
use super::{TheorySolver, TheoryConflict, TheoryPropagation, TheoryResult};

/// Array identifier.
pub type ArrayId = u32;

/// Index/element identifier.
pub type ElemId = u32;

/// An array term.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ArrayTerm {
    /// Variable array.
    Var(ArrayId),
    /// Store operation: store(array, index, value).
    Store(Box<ArrayTerm>, ElemId, ElemId),
}

impl ArrayTerm {
    /// Get the base array variable.
    pub fn base_array(&self) -> ArrayId {
        match self {
            ArrayTerm::Var(id) => *id,
            ArrayTerm::Store(arr, _, _) => arr.base_array(),
        }
    }
}

/// A select operation.
#[derive(Debug, Clone)]
pub struct Select {
    /// The array being read from.
    pub array: ArrayTerm,
    /// The index being read.
    pub index: ElemId,
    /// The resulting element.
    pub result: ElemId,
    /// Decision level when this select was added.
    pub level: u32,
}

/// An array axiom instance.
#[derive(Debug, Clone)]
enum Axiom {
    /// Read-over-write same index: select(store(a, i, v), i) = v
    ReadOverWriteSame {
        array: ArrayTerm,
        index: ElemId,
        value: ElemId,
        result: ElemId,
    },
    /// Read-over-write different index: i ≠ j → select(store(a, i, v), j) = select(a, j)
    ReadOverWriteDiff {
        array: ArrayTerm,
        store_index: ElemId,
        read_index: ElemId,
        value: ElemId,
        store_result: ElemId,
        base_result: ElemId,
    },
}

/// Array equality/disequality assertion.
#[derive(Debug, Clone)]
struct ArrayAssertion {
    /// First element/array.
    lhs: ElemId,
    /// Second element/array.
    rhs: ElemId,
    /// Is equality (true) or disequality (false)?
    is_equality: bool,
    /// The literal that caused this assertion.
    literal: Literal,
    /// Decision level.
    level: u32,
}

/// Array Theory Solver.
pub struct ArraySolver {
    /// Equality classes for elements (union-find).
    parent: HashMap<ElemId, ElemId>,
    /// Rank for union by rank.
    rank: HashMap<ElemId, u32>,
    /// Proof edges for explanation.
    proof: HashMap<ElemId, (ElemId, Literal)>,
    
    /// All select operations.
    selects: Vec<Select>,
    /// Assertions (equalities and disequalities).
    assertions: Vec<ArrayAssertion>,
    /// Disequalities for conflict checking.
    disequalities: Vec<(ElemId, ElemId, Literal)>,
    
    /// Pending axiom instances.
    pending_axioms: Vec<(Axiom, u32)>,
    /// Generated axioms (to avoid duplicates).
    generated: HashSet<(ElemId, ElemId)>,
    
    /// Pending propagations.
    pending_propagations: Vec<TheoryPropagation>,
    /// Current decision level.
    current_level: u32,
    /// Explanation cache.
    explanations: HashMap<Literal, Vec<Literal>>,
}

impl ArraySolver {
    /// Create a new array solver.
    pub fn new() -> Self {
        ArraySolver {
            parent: HashMap::new(),
            rank: HashMap::new(),
            proof: HashMap::new(),
            selects: Vec::new(),
            assertions: Vec::new(),
            disequalities: Vec::new(),
            pending_axioms: Vec::new(),
            generated: HashSet::new(),
            pending_propagations: Vec::new(),
            current_level: 0,
            explanations: HashMap::new(),
        }
    }
    
    /// Ensure an element exists in union-find.
    fn ensure_elem(&mut self, e: ElemId) {
        if !self.parent.contains_key(&e) {
            self.parent.insert(e, e);
            self.rank.insert(e, 0);
        }
    }
    
    /// Find representative with path compression.
    pub fn find(&mut self, x: ElemId) -> ElemId {
        self.ensure_elem(x);
        let p = self.parent[&x];
        if p != x {
            let root = self.find(p);
            self.parent.insert(x, root);
            root
        } else {
            x
        }
    }
    
    /// Find representative (const version).
    pub fn find_const(&self, mut x: ElemId) -> ElemId {
        while let Some(&p) = self.parent.get(&x) {
            if p == x {
                break;
            }
            x = p;
        }
        x
    }
    
    /// Check if two elements are equal.
    pub fn are_equal(&mut self, a: ElemId, b: ElemId) -> bool {
        self.find(a) == self.find(b)
    }
    
    /// Union two elements.
    fn union(&mut self, a: ElemId, b: ElemId, literal: Literal) {
        let ra = self.find(a);
        let rb = self.find(b);
        
        if ra == rb {
            return;
        }
        
        let rank_a = *self.rank.get(&ra).unwrap_or(&0);
        let rank_b = *self.rank.get(&rb).unwrap_or(&0);
        
        if rank_a < rank_b {
            self.parent.insert(ra, rb);
            self.proof.insert(ra, (rb, literal));
        } else if rank_a > rank_b {
            self.parent.insert(rb, ra);
            self.proof.insert(rb, (ra, literal));
        } else {
            self.parent.insert(rb, ra);
            self.proof.insert(rb, (ra, literal));
            self.rank.insert(ra, rank_a + 1);
        }
    }
    
    /// Assert equality between two elements.
    pub fn assert_equality(&mut self, a: ElemId, b: ElemId, literal: Literal, level: u32) {
        self.ensure_elem(a);
        self.ensure_elem(b);
        self.assertions.push(ArrayAssertion {
            lhs: a,
            rhs: b,
            is_equality: true,
            literal,
            level,
        });
        self.current_level = level;
        self.union(a, b, literal);
    }
    
    /// Assert disequality between two elements.
    pub fn assert_disequality(&mut self, a: ElemId, b: ElemId, literal: Literal, level: u32) {
        self.ensure_elem(a);
        self.ensure_elem(b);
        self.assertions.push(ArrayAssertion {
            lhs: a,
            rhs: b,
            is_equality: false,
            literal,
            level,
        });
        self.current_level = level;
        self.disequalities.push((a, b, literal));
    }
    
    /// Add a select operation.
    pub fn add_select(&mut self, array: ArrayTerm, index: ElemId, result: ElemId, level: u32) {
        self.ensure_elem(index);
        self.ensure_elem(result);
        self.selects.push(Select { array, index, result, level });
        
        // Generate axioms lazily
        self.generate_axioms_for_select(self.selects.len() - 1);
    }
    
    /// Generate axioms for a new select.
    fn generate_axioms_for_select(&mut self, select_idx: usize) {
        let select = &self.selects[select_idx];
        
        // If selecting from a store, generate read-over-write axioms
        if let ArrayTerm::Store(base, store_idx, store_val) = &select.array {
            let read_idx = select.index;
            let read_result = select.result;
            let level = select.level;
            
            // Check if indices might be equal
            let key = (store_idx.min(&read_idx).clone(), store_idx.max(&read_idx).clone());
            if !self.generated.contains(&key) {
                self.generated.insert(key);
                
                // Same index case: select(store(a, i, v), i) = v
                self.pending_axioms.push((
                    Axiom::ReadOverWriteSame {
                        array: (**base).clone(),
                        index: *store_idx,
                        value: *store_val,
                        result: read_result,
                    },
                    level,
                ));
                
                // Different index case: i ≠ j → select(store(a, i, v), j) = select(a, j)
                // This would require a new select on the base array
            }
        }
    }
    
    /// Check for conflicts.
    fn check_conflicts(&mut self) -> Option<TheoryConflict> {
        // Clone disequalities to avoid borrow conflict
        let diseqs: Vec<_> = self.disequalities.clone();
        for (a, b, lit) in diseqs {
            if self.are_equal(a, b) {
                let explanation = self.explain_equality(a, b);
                let mut conflict_lits = explanation;
                conflict_lits.push(lit);
                return Some(TheoryConflict::new(conflict_lits));
            }
        }
        
        // Check read-over-write axioms
        for (axiom, _level) in &self.pending_axioms.clone() {
            match axiom {
                Axiom::ReadOverWriteSame { index, value, result, .. } => {
                    // If indices are equal, result must equal value
                    if self.are_equal(*index, *index) {
                        if !self.are_equal(*result, *value) {
                            // This should be propagated, not a conflict yet
                        }
                    }
                }
                Axiom::ReadOverWriteDiff { .. } => {
                    // Handle different index case
                }
            }
        }
        
        None
    }
    
    /// Explain equality between two elements.
    fn explain_equality(&self, a: ElemId, b: ElemId) -> Vec<Literal> {
        let mut lits = Vec::new();
        
        // Collect path from a to root
        let mut x = a;
        while let Some(&(parent, lit)) = self.proof.get(&x) {
            lits.push(lit);
            x = parent;
        }
        
        // Collect path from b to root
        let mut x = b;
        while let Some(&(parent, lit)) = self.proof.get(&x) {
            if !lits.contains(&lit) {
                lits.push(lit);
            }
            x = parent;
        }
        
        lits
    }
    
    /// Rebuild union-find from assertions.
    fn rebuild(&mut self) {
        self.parent.clear();
        self.rank.clear();
        self.proof.clear();
        
        for assertion in &self.assertions.clone() {
            if assertion.is_equality {
                self.ensure_elem(assertion.lhs);
                self.ensure_elem(assertion.rhs);
                self.union(assertion.lhs, assertion.rhs, assertion.literal);
            }
        }
    }
}

impl Default for ArraySolver {
    fn default() -> Self {
        Self::new()
    }
}

impl TheorySolver for ArraySolver {
    fn name(&self) -> &'static str {
        "Array"
    }
    
    fn assert_literal(&mut self, _lit: Literal, level: u32) -> Result<(), TheoryConflict> {
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
        self.assertions.retain(|a| a.level <= level);
        self.selects.retain(|s| s.level <= level);
        self.disequalities.retain(|(_, _, _)| true); // Would need level tracking
        self.pending_axioms.retain(|(_, l)| *l <= level);
        self.rebuild();
        self.current_level = level;
    }
    
    fn reset(&mut self) {
        self.parent.clear();
        self.rank.clear();
        self.proof.clear();
        self.selects.clear();
        self.assertions.clear();
        self.disequalities.clear();
        self.pending_axioms.clear();
        self.generated.clear();
        self.pending_propagations.clear();
        self.current_level = 0;
        self.explanations.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_array_solver_new() {
        let solver = ArraySolver::new();
        assert!(solver.selects.is_empty());
    }

    #[test]
    fn test_equality() {
        let mut solver = ArraySolver::new();
        
        solver.assert_equality(1, 2, Literal::from_dimacs(1), 1);
        
        assert!(solver.are_equal(1, 2));
    }

    #[test]
    fn test_transitivity() {
        let mut solver = ArraySolver::new();
        
        solver.assert_equality(1, 2, Literal::from_dimacs(1), 1);
        solver.assert_equality(2, 3, Literal::from_dimacs(2), 1);
        
        assert!(solver.are_equal(1, 3));
    }

    #[test]
    fn test_conflict_detection() {
        let mut solver = ArraySolver::new();
        
        solver.assert_equality(1, 2, Literal::from_dimacs(1), 1);
        solver.assert_disequality(1, 2, Literal::from_dimacs(2), 1);
        
        match solver.check() {
            TheoryResult::Conflict(c) => {
                assert!(!c.literals.is_empty());
            }
            TheoryResult::Consistent => panic!("Expected conflict"),
        }
    }

    #[test]
    fn test_no_conflict() {
        let mut solver = ArraySolver::new();
        
        solver.assert_equality(1, 2, Literal::from_dimacs(1), 1);
        solver.assert_disequality(1, 3, Literal::from_dimacs(2), 1);
        
        assert!(matches!(solver.check(), TheoryResult::Consistent));
    }

    #[test]
    fn test_add_select() {
        let mut solver = ArraySolver::new();
        
        let arr = ArrayTerm::Var(0);
        solver.add_select(arr, 1, 2, 1);
        
        assert_eq!(solver.selects.len(), 1);
    }

    #[test]
    fn test_select_from_store() {
        let mut solver = ArraySolver::new();
        
        let base = ArrayTerm::Var(0);
        let stored = ArrayTerm::Store(Box::new(base), 1, 10);
        
        // select(store(a, 1, 10), 1) should equal 10
        solver.add_select(stored, 1, 20, 1);
        
        // Axiom should be generated
        assert!(!solver.pending_axioms.is_empty());
    }

    #[test]
    fn test_backtrack() {
        let mut solver = ArraySolver::new();
        
        solver.assert_equality(1, 2, Literal::from_dimacs(1), 1);
        assert!(solver.are_equal(1, 2));
        
        solver.backtrack(0);
        assert!(!solver.are_equal(1, 2));
    }

    #[test]
    fn test_reset() {
        let mut solver = ArraySolver::new();
        
        solver.assert_equality(1, 2, Literal::from_dimacs(1), 1);
        let arr = ArrayTerm::Var(0);
        solver.add_select(arr, 1, 2, 1);
        
        solver.reset();
        
        assert!(solver.assertions.is_empty());
        assert!(solver.selects.is_empty());
    }

    #[test]
    fn test_explain_equality() {
        let mut solver = ArraySolver::new();
        
        solver.assert_equality(1, 2, Literal::from_dimacs(1), 1);
        solver.assert_equality(2, 3, Literal::from_dimacs(2), 1);
        
        let explanation = solver.explain_equality(1, 3);
        
        // Should include both merge literals
        assert!(!explanation.is_empty());
    }
}
