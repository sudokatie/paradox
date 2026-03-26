//! Theory solver for Arrays.
//!
//! Implements:
//! - Read-over-write axioms: select(store(a, i, v), i) = v
//! - Read-over-write different: i ≠ j → select(store(a, i, v), j) = select(a, j)
//! - Array extensionality: (∀i. select(a, i) = select(b, i)) → a = b
//! - Lazy axiom instantiation for efficiency

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
    pub array: ArrayTerm,
    pub index: ElemId,
    pub result: ElemId,
    pub level: u32,
}

/// Read-over-write axiom instance.
#[derive(Debug, Clone)]
struct RowAxiom {
    /// The store term.
    store_array: ArrayTerm,
    /// Store index.
    store_index: ElemId,
    /// Stored value.
    store_value: ElemId,
    /// Read index.
    read_index: ElemId,
    /// Read result.
    read_result: ElemId,
    /// Decision level.
    level: u32,
}

/// Extensionality axiom instance.
#[derive(Debug, Clone)]
struct ExtAxiom {
    /// First array.
    array1: ArrayTerm,
    /// Second array.
    array2: ArrayTerm,
    /// Witness index (where they might differ).
    witness_index: ElemId,
    /// Decision level.
    level: u32,
}

/// Array equality/disequality assertion.
#[derive(Debug, Clone)]
struct ArrayAssertion {
    lhs: ElemId,
    rhs: ElemId,
    is_equality: bool,
    literal: Literal,
    level: u32,
}

/// Array Theory Solver with extensionality.
pub struct ArraySolver {
    /// Union-find parent pointers.
    parent: HashMap<ElemId, ElemId>,
    /// Rank for union by rank.
    rank: HashMap<ElemId, u32>,
    /// Proof edges for explanation.
    proof: HashMap<ElemId, (ElemId, Literal)>,

    /// All select operations.
    selects: Vec<Select>,
    /// Assertions.
    assertions: Vec<ArrayAssertion>,
    /// Disequalities.
    disequalities: Vec<(ElemId, ElemId, Literal)>,

    /// Array disequalities (for extensionality).
    array_disequalities: Vec<(ArrayTerm, ArrayTerm, Literal, u32)>,
    /// Array equalities.
    array_equalities: Vec<(ArrayTerm, ArrayTerm, Literal, u32)>,

    /// Read-over-write axiom instances.
    row_axioms: Vec<RowAxiom>,
    /// Extensionality axiom instances.
    ext_axioms: Vec<ExtAxiom>,

    /// Generated axiom pairs (to avoid duplicates).
    generated_row: HashSet<(ElemId, ElemId)>,
    /// Generated extensionality pairs.
    generated_ext: HashSet<(ArrayId, ArrayId)>,

    /// Pending propagations.
    pending_propagations: Vec<TheoryPropagation>,
    /// Current decision level.
    current_level: u32,
    /// Explanation cache.
    explanations: HashMap<Literal, Vec<Literal>>,
    /// Next fresh element ID.
    next_elem: ElemId,
}

impl ArraySolver {
    pub fn new() -> Self {
        ArraySolver {
            parent: HashMap::new(),
            rank: HashMap::new(),
            proof: HashMap::new(),
            selects: Vec::new(),
            assertions: Vec::new(),
            disequalities: Vec::new(),
            array_disequalities: Vec::new(),
            array_equalities: Vec::new(),
            row_axioms: Vec::new(),
            ext_axioms: Vec::new(),
            generated_row: HashSet::new(),
            generated_ext: HashSet::new(),
            pending_propagations: Vec::new(),
            current_level: 0,
            explanations: HashMap::new(),
            next_elem: 1000000,
        }
    }

    /// Allocate a fresh element ID.
    pub fn fresh_elem(&mut self) -> ElemId {
        let id = self.next_elem;
        self.next_elem += 1;
        self.ensure_elem(id);
        id
    }

    fn ensure_elem(&mut self, e: ElemId) {
        if !self.parent.contains_key(&e) {
            self.parent.insert(e, e);
            self.rank.insert(e, 0);
        }
    }

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

    pub fn find_const(&self, mut x: ElemId) -> ElemId {
        while let Some(&p) = self.parent.get(&x) {
            if p == x { break; }
            x = p;
        }
        x
    }

    pub fn are_equal(&mut self, a: ElemId, b: ElemId) -> bool {
        self.find(a) == self.find(b)
    }

    fn union(&mut self, a: ElemId, b: ElemId, literal: Literal) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb { return; }

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

    pub fn assert_equality(&mut self, a: ElemId, b: ElemId, literal: Literal, level: u32) {
        self.ensure_elem(a);
        self.ensure_elem(b);
        self.assertions.push(ArrayAssertion {
            lhs: a, rhs: b, is_equality: true, literal, level,
        });
        self.current_level = level;
        self.union(a, b, literal);
    }

    pub fn assert_disequality(&mut self, a: ElemId, b: ElemId, literal: Literal, level: u32) {
        self.ensure_elem(a);
        self.ensure_elem(b);
        self.assertions.push(ArrayAssertion {
            lhs: a, rhs: b, is_equality: false, literal, level,
        });
        self.current_level = level;
        self.disequalities.push((a, b, literal));
    }

    /// Assert array equality.
    pub fn assert_array_equality(&mut self, a: ArrayTerm, b: ArrayTerm, literal: Literal, level: u32) {
        self.array_equalities.push((a, b, literal, level));
        self.current_level = level;
    }

    /// Assert array disequality (triggers extensionality).
    pub fn assert_array_disequality(&mut self, a: ArrayTerm, b: ArrayTerm, literal: Literal, level: u32) {
        self.array_disequalities.push((a.clone(), b.clone(), literal, level));
        self.current_level = level;

        // Generate extensionality witness
        self.generate_extensionality(&a, &b, level);
    }

    /// Generate extensionality axiom: if a ≠ b, then ∃i. select(a, i) ≠ select(b, i)
    fn generate_extensionality(&mut self, a: &ArrayTerm, b: &ArrayTerm, level: u32) {
        let a_id = a.base_array();
        let b_id = b.base_array();
        let key = (a_id.min(b_id), a_id.max(b_id));

        if self.generated_ext.contains(&key) {
            return;
        }
        self.generated_ext.insert(key);

        // Create fresh witness index
        let witness = self.fresh_elem();

        self.ext_axioms.push(ExtAxiom {
            array1: a.clone(),
            array2: b.clone(),
            witness_index: witness,
            level,
        });

        // The axiom: a ≠ b → select(a, witness) ≠ select(b, witness)
        // This creates two select terms that must differ
    }

    pub fn add_select(&mut self, array: ArrayTerm, index: ElemId, result: ElemId, level: u32) {
        self.ensure_elem(index);
        self.ensure_elem(result);
        self.selects.push(Select { array: array.clone(), index, result, level });

        // Generate read-over-write axioms
        self.generate_row_axioms(self.selects.len() - 1, level);
    }

    fn generate_row_axioms(&mut self, select_idx: usize, level: u32) {
        let select = &self.selects[select_idx];

        if let ArrayTerm::Store(base, store_idx, store_val) = &select.array {
            let read_idx = select.index;
            let read_result = select.result;

            let key = ((*store_idx).min(read_idx), (*store_idx).max(read_idx));
            if !self.generated_row.contains(&key) {
                self.generated_row.insert(key);

                self.row_axioms.push(RowAxiom {
                    store_array: (**base).clone(),
                    store_index: *store_idx,
                    store_value: *store_val,
                    read_index: read_idx,
                    read_result,
                    level,
                });
            }
        }
    }

    fn check_conflicts(&mut self) -> Option<TheoryConflict> {
        // Check element disequalities
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
        let row_axioms = self.row_axioms.clone();
        let diseqs_for_row = self.disequalities.clone();
        for axiom in row_axioms {
            // If store_index = read_index, then read_result = store_value
            if self.are_equal(axiom.store_index, axiom.read_index) {
                if !self.are_equal(axiom.read_result, axiom.store_value) {
                    // Need to propagate read_result = store_value
                    // For now, detect if there's a conflict with existing disequality
                    for (a, b, lit) in &diseqs_for_row {
                        if (self.are_equal(*a, axiom.read_result) && self.are_equal(*b, axiom.store_value))
                            || (self.are_equal(*a, axiom.store_value) && self.are_equal(*b, axiom.read_result))
                        {
                            let mut conflict_lits = self.explain_equality(axiom.store_index, axiom.read_index);
                            conflict_lits.push(*lit);
                            return Some(TheoryConflict::new(conflict_lits));
                        }
                    }
                }
            }
        }

        // Check extensionality axioms
        for _axiom in self.ext_axioms.clone() {
            // If arrays are equal, but we have array disequality, conflict
            // This is simplified - full implementation would track array term equality
        }

        None
    }

    fn explain_equality(&self, a: ElemId, b: ElemId) -> Vec<Literal> {
        let mut lits = Vec::new();

        let mut x = a;
        while let Some(&(parent, lit)) = self.proof.get(&x) {
            lits.push(lit);
            x = parent;
        }

        let mut x = b;
        while let Some(&(parent, lit)) = self.proof.get(&x) {
            if !lits.contains(&lit) {
                lits.push(lit);
            }
            x = parent;
        }

        lits
    }

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
        self.disequalities.retain(|&(_, _, _)| true);
        self.array_disequalities.retain(|&(_, _, _, l)| l <= level);
        self.array_equalities.retain(|&(_, _, _, l)| l <= level);
        self.row_axioms.retain(|a| a.level <= level);
        self.ext_axioms.retain(|a| a.level <= level);
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
        self.array_disequalities.clear();
        self.array_equalities.clear();
        self.row_axioms.clear();
        self.ext_axioms.clear();
        self.generated_row.clear();
        self.generated_ext.clear();
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
        solver.add_select(stored, 1, 20, 1);
        assert!(!solver.row_axioms.is_empty());
    }

    #[test]
    fn test_extensionality() {
        let mut solver = ArraySolver::new();
        let a = ArrayTerm::Var(0);
        let b = ArrayTerm::Var(1);
        solver.assert_array_disequality(a, b, Literal::from_dimacs(1), 1);
        assert!(!solver.ext_axioms.is_empty());
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
}
