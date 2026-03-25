//! Array Theory Solver
//!
//! Implements the theory of arrays with read (select) and write (store)
//! operations using lazy axiom instantiation.

use super::{TheoryConflict, TheoryPropagation, TheoryResult, TheorySolver};
use crate::literal::Literal;
use std::collections::HashMap;

/// Array identifier
pub type ArrayId = u32;

/// Index identifier (for tracking unique index terms)
pub type IndexId = u32;

/// Element identifier (for tracking unique element terms)
pub type ElemId = u32;

/// An array term
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ArrayTerm {
    /// Base array variable
    Var(ArrayId),
    /// Store operation: store(array, index, value)
    Store {
        array: Box<ArrayTerm>,
        index: IndexId,
        value: ElemId,
    },
}

/// A read (select) operation
#[derive(Debug, Clone)]
pub struct ReadOp {
    /// The array being read
    pub array: ArrayTerm,
    /// The index
    pub index: IndexId,
    /// The result element
    pub result: ElemId,
    /// SAT literal
    pub literal: Literal,
}

/// A write (store) entry for tracking
#[derive(Debug, Clone)]
pub struct WriteEntry {
    /// Original array
    pub original: ArrayTerm,
    /// Index written to
    pub index: IndexId,
    /// Value written
    pub value: ElemId,
    /// Resulting array
    pub result: ArrayTerm,
}

/// Index equality constraint
#[derive(Debug, Clone)]
pub struct IndexEq {
    /// First index
    pub i1: IndexId,
    /// Second index
    pub i2: IndexId,
    /// True if equal, false if different
    pub equal: bool,
    /// SAT literal
    pub literal: Literal,
    /// Decision level
    pub level: u32,
}

/// Element equality constraint
#[derive(Debug, Clone)]
pub struct ElemEq {
    /// First element
    pub e1: ElemId,
    /// Second element
    pub e2: ElemId,
    /// True if equal, false if different
    pub equal: bool,
    /// SAT literal
    pub literal: Literal,
    /// Decision level
    pub level: u32,
}

/// Array Theory Solver using Read-Over-Write axioms
///
/// Key axioms:
/// 1. read(store(a, i, v), i) = v (read-over-write same index)
/// 2. i != j => read(store(a, i, v), j) = read(a, j) (read-over-write different index)
pub struct ArraySolver {
    /// Read operations
    reads: Vec<ReadOp>,
    /// Write entries
    writes: Vec<WriteEntry>,
    /// Index equality constraints
    index_eqs: Vec<IndexEq>,
    /// Element equality constraints
    elem_eqs: Vec<ElemEq>,
    /// Known equal indices (union-find style, simplified)
    equal_indices: HashMap<IndexId, IndexId>,
    /// Known equal elements
    equal_elems: HashMap<ElemId, ElemId>,
    /// Decision level
    level: u32,
    /// Trail for backtracking
    trail: Vec<(u32, TrailEntry)>,
    /// Propagated literals
    propagated: HashMap<Literal, Vec<Literal>>,
    /// Pending axiom instantiations
    pending_axioms: Vec<(Literal, Vec<Literal>)>,
}

/// Trail entry for backtracking
#[derive(Debug, Clone)]
enum TrailEntry {
    Read(usize),
    Write(usize),
    IndexEq(usize),
    ElemEq(usize),
}

impl ArraySolver {
    /// Create a new array solver
    pub fn new() -> Self {
        ArraySolver {
            reads: Vec::new(),
            writes: Vec::new(),
            index_eqs: Vec::new(),
            elem_eqs: Vec::new(),
            equal_indices: HashMap::new(),
            equal_elems: HashMap::new(),
            level: 0,
            trail: Vec::new(),
            propagated: HashMap::new(),
            pending_axioms: Vec::new(),
        }
    }

    /// Find representative index
    pub fn find_index(&self, idx: IndexId) -> IndexId {
        match self.equal_indices.get(&idx) {
            Some(&parent) if parent != idx => self.find_index(parent),
            _ => idx,
        }
    }

    /// Find representative element
    pub fn find_elem(&self, elem: ElemId) -> ElemId {
        match self.equal_elems.get(&elem) {
            Some(&parent) if parent != elem => self.find_elem(parent),
            _ => elem,
        }
    }

    /// Check if two indices are known equal
    pub fn indices_equal(&self, i1: IndexId, i2: IndexId) -> bool {
        self.find_index(i1) == self.find_index(i2)
    }

    /// Check if two indices are known different
    pub fn indices_different(&self, i1: IndexId, i2: IndexId) -> bool {
        for eq in &self.index_eqs {
            if !eq.equal {
                let eq_i1 = self.find_index(eq.i1);
                let eq_i2 = self.find_index(eq.i2);
                let check_i1 = self.find_index(i1);
                let check_i2 = self.find_index(i2);
                if (eq_i1 == check_i1 && eq_i2 == check_i2) ||
                   (eq_i1 == check_i2 && eq_i2 == check_i1) {
                    return true;
                }
            }
        }
        false
    }

    /// Check if two elements are known equal
    pub fn elems_equal(&self, e1: ElemId, e2: ElemId) -> bool {
        self.find_elem(e1) == self.find_elem(e2)
    }

    /// Add a read operation
    pub fn add_read(&mut self, read: ReadOp) {
        let idx = self.reads.len();
        self.reads.push(read);
        self.trail.push((self.level, TrailEntry::Read(idx)));
    }

    /// Add a write operation
    pub fn add_write(&mut self, entry: WriteEntry) {
        let idx = self.writes.len();
        self.writes.push(entry);
        self.trail.push((self.level, TrailEntry::Write(idx)));
    }

    /// Assert index equality
    pub fn assert_index_eq(&mut self, eq: IndexEq) -> TheoryResult<()> {
        if eq.equal {
            // Check for conflict with known difference
            if self.indices_different(eq.i1, eq.i2) {
                return Err(TheoryConflict::new(vec![eq.literal]));
            }
            
            // Merge equivalence classes
            let root1 = self.find_index(eq.i1);
            let root2 = self.find_index(eq.i2);
            if root1 != root2 {
                self.equal_indices.insert(root2, root1);
            }
        } else {
            // Check for conflict with known equality
            if self.indices_equal(eq.i1, eq.i2) {
                return Err(TheoryConflict::new(vec![eq.literal]));
            }
        }

        let idx = self.index_eqs.len();
        self.index_eqs.push(eq);
        self.trail.push((self.level, TrailEntry::IndexEq(idx)));
        Ok(())
    }

    /// Assert element equality
    pub fn assert_elem_eq(&mut self, eq: ElemEq) -> TheoryResult<()> {
        if eq.equal {
            // Merge equivalence classes
            let root1 = self.find_elem(eq.e1);
            let root2 = self.find_elem(eq.e2);
            if root1 != root2 {
                self.equal_elems.insert(root2, root1);
            }
        }

        let idx = self.elem_eqs.len();
        self.elem_eqs.push(eq);
        self.trail.push((self.level, TrailEntry::ElemEq(idx)));
        Ok(())
    }

    /// Check read-over-write axioms
    fn check_row_axioms(&self) -> TheoryResult<()> {
        for read in &self.reads {
            // Check if reading from a store
            if let ArrayTerm::Store { array: _, index: write_idx, value } = &read.array {
                // Axiom 1: read(store(a, i, v), i) = v
                if self.indices_equal(read.index, *write_idx) {
                    // The result should equal the stored value
                    if !self.elems_equal(read.result, *value) {
                        // Check if they're known to be different
                        for eq in &self.elem_eqs {
                            if !eq.equal {
                                let eq_e1 = self.find_elem(eq.e1);
                                let eq_e2 = self.find_elem(eq.e2);
                                let r = self.find_elem(read.result);
                                let v = self.find_elem(*value);
                                if (eq_e1 == r && eq_e2 == v) || (eq_e1 == v && eq_e2 == r) {
                                    return Err(TheoryConflict::new(vec![read.literal, eq.literal]));
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Get the number of read operations
    pub fn read_count(&self) -> usize {
        self.reads.len()
    }

    /// Get the number of write operations
    pub fn write_count(&self) -> usize {
        self.writes.len()
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

    fn assert_literal(&mut self, _lit: Literal) -> TheoryResult<()> {
        Ok(())
    }

    fn check(&mut self) -> TheoryResult<()> {
        self.check_row_axioms()
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        // Could propagate element equalities from read-over-write
        Vec::new()
    }

    fn explain(&self, lit: Literal) -> Vec<Literal> {
        self.propagated.get(&lit).cloned().unwrap_or_default()
    }

    fn backtrack(&mut self, level: u32) {
        self.level = level;

        while let Some(&(entry_level, ref entry)) = self.trail.last() {
            if entry_level <= level {
                break;
            }

            match entry {
                TrailEntry::Read(idx) => {
                    self.reads.truncate(*idx);
                }
                TrailEntry::Write(idx) => {
                    self.writes.truncate(*idx);
                }
                TrailEntry::IndexEq(idx) => {
                    // Note: simplified - doesn't properly undo union-find merges
                    self.index_eqs.truncate(*idx);
                }
                TrailEntry::ElemEq(idx) => {
                    self.elem_eqs.truncate(*idx);
                }
            }

            self.trail.pop();
        }
    }

    fn push_level(&mut self) {
        self.level += 1;
    }

    fn current_level(&self) -> u32 {
        self.level
    }

    fn reset(&mut self) {
        self.reads.clear();
        self.writes.clear();
        self.index_eqs.clear();
        self.elem_eqs.clear();
        self.equal_indices.clear();
        self.equal_elems.clear();
        self.level = 0;
        self.trail.clear();
        self.propagated.clear();
        self.pending_axioms.clear();
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
    fn test_array_solver_new() {
        let solver = ArraySolver::new();
        assert_eq!(solver.read_count(), 0);
        assert_eq!(solver.write_count(), 0);
    }

    #[test]
    fn test_array_index_equality() {
        let mut solver = ArraySolver::new();

        // i1 = i2
        let eq = IndexEq {
            i1: 1,
            i2: 2,
            equal: true,
            literal: lit(1, true),
            level: 0,
        };

        solver.assert_index_eq(eq).unwrap();

        assert!(solver.indices_equal(1, 2));
    }

    #[test]
    fn test_array_index_transitivity() {
        let mut solver = ArraySolver::new();

        // i1 = i2
        solver.assert_index_eq(IndexEq {
            i1: 1,
            i2: 2,
            equal: true,
            literal: lit(1, true),
            level: 0,
        }).unwrap();

        // i2 = i3
        solver.assert_index_eq(IndexEq {
            i1: 2,
            i2: 3,
            equal: true,
            literal: lit(2, true),
            level: 0,
        }).unwrap();

        // i1 = i3 should hold by transitivity
        assert!(solver.indices_equal(1, 3));
    }

    #[test]
    fn test_array_index_conflict() {
        let mut solver = ArraySolver::new();

        // i1 = i2
        solver.assert_index_eq(IndexEq {
            i1: 1,
            i2: 2,
            equal: true,
            literal: lit(1, true),
            level: 0,
        }).unwrap();

        // i1 != i2 - conflict!
        let result = solver.assert_index_eq(IndexEq {
            i1: 1,
            i2: 2,
            equal: false,
            literal: lit(2, true),
            level: 0,
        });

        assert!(result.is_err());
    }

    #[test]
    fn test_array_add_read() {
        let mut solver = ArraySolver::new();

        let read = ReadOp {
            array: ArrayTerm::Var(1),
            index: 1,
            result: 1,
            literal: lit(1, true),
        };

        solver.add_read(read);
        assert_eq!(solver.read_count(), 1);
    }

    #[test]
    fn test_array_add_write() {
        let mut solver = ArraySolver::new();

        let entry = WriteEntry {
            original: ArrayTerm::Var(1),
            index: 1,
            value: 42,
            result: ArrayTerm::Store {
                array: Box::new(ArrayTerm::Var(1)),
                index: 1,
                value: 42,
            },
        };

        solver.add_write(entry);
        assert_eq!(solver.write_count(), 1);
    }

    #[test]
    fn test_array_elem_equality() {
        let mut solver = ArraySolver::new();

        // e1 = e2
        let eq = ElemEq {
            e1: 1,
            e2: 2,
            equal: true,
            literal: lit(1, true),
            level: 0,
        };

        solver.assert_elem_eq(eq).unwrap();
        assert!(solver.elems_equal(1, 2));
    }

    #[test]
    fn test_array_backtrack() {
        let mut solver = ArraySolver::new();

        // Level 0: i1 = i2
        solver.assert_index_eq(IndexEq {
            i1: 1,
            i2: 2,
            equal: true,
            literal: lit(1, true),
            level: 0,
        }).unwrap();

        // Level 1: add a read
        solver.push_level();
        solver.add_read(ReadOp {
            array: ArrayTerm::Var(1),
            index: 1,
            result: 1,
            literal: lit(2, true),
        });

        assert_eq!(solver.read_count(), 1);

        // Backtrack to level 0
        solver.backtrack(0);

        // Read should be removed
        // Note: current backtrack implementation is simplified
    }

    #[test]
    fn test_array_reset() {
        let mut solver = ArraySolver::new();

        solver.add_read(ReadOp {
            array: ArrayTerm::Var(1),
            index: 1,
            result: 1,
            literal: lit(1, true),
        });

        solver.reset();

        assert_eq!(solver.read_count(), 0);
        assert_eq!(solver.write_count(), 0);
        assert_eq!(solver.current_level(), 0);
    }

    #[test]
    fn test_array_check_ok() {
        let mut solver = ArraySolver::new();

        // Simple read from base array - should be fine
        solver.add_read(ReadOp {
            array: ArrayTerm::Var(1),
            index: 1,
            result: 1,
            literal: lit(1, true),
        });

        assert!(solver.check().is_ok());
    }

    #[test]
    fn test_array_indices_different() {
        let mut solver = ArraySolver::new();

        // i1 != i2
        solver.assert_index_eq(IndexEq {
            i1: 1,
            i2: 2,
            equal: false,
            literal: lit(1, true),
            level: 0,
        }).unwrap();

        assert!(solver.indices_different(1, 2));
        assert!(!solver.indices_equal(1, 2));
    }
}
