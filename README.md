# Paradox

SAT/SMT solver with CDCL (Conflict-Driven Clause Learning) and theory solvers.

Built as an educational project exploring satisfiability solving techniques.

## Features

### SAT Solving
- **CDCL algorithm** with watched literals for efficient propagation
- **VSIDS** variable selection heuristic
- **1-UIP** conflict analysis and clause learning
- **Restarts**: Luby, geometric, and Glucose-style dynamic restarts
- **Clause deletion** based on LBD (Literal Block Distance)

### SMT Solving (DPLL(T))
- **Theory solver interface** for modular theory integration
- **EUF**: Equality with Uninterpreted Functions (congruence closure)
- **LIA**: Linear Integer Arithmetic (bound propagation)
- **BV**: Bitvector operations (fixed-width arithmetic)
- **Arrays**: Read-over-write axioms with lazy instantiation

### Input Formats
- **DIMACS CNF** for SAT problems
- **SMT-LIB 2** for SMT problems

## Installation

```bash
cargo install --path .
```

## Usage

```bash
# Solve a DIMACS CNF file
paradox input.cnf

# Solve an SMT-LIB file
paradox input.smt2

# With verbose output
paradox -v input.cnf

# With statistics
paradox -s input.cnf

# With timeout (seconds)
paradox -t 60 input.cnf

# Force format
paradox -f smtlib input.smt2
```

## Examples

### DIMACS CNF

```
c This is a comment
p cnf 3 2
1 -2 3 0
-1 2 0
```

- `c` lines are comments
- `p cnf <vars> <clauses>` declares the problem
- Each clause is a list of literals ending with `0`
- Negative numbers are negated literals

### SMT-LIB 2

```smt2
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (> x 0))
(assert (< y 10))
(assert (= (+ x y) 15))
(check-sat)
```

Supported logics: QF_UF, QF_LIA, QF_BV, QF_A, QF_AUFLIA, QF_AUFBV

## Exit Codes

- `10`: SAT (satisfiable)
- `20`: UNSAT (unsatisfiable)
- `1`: Error or unknown

## Algorithm Overview

### CDCL

```
while True:
    conflict = propagate()
    if conflict:
        if level == 0: return UNSAT
        learned, backtrack_level = analyze(conflict)
        add_clause(learned)
        backtrack(backtrack_level)
        bump_vsids(involved_vars)
    elif all_assigned():
        return SAT
    else:
        if should_restart(): restart()
        if should_reduce(): reduce()
        decide()
```

### Two-Watched Literals

Each clause watches exactly two literals. When a watched literal becomes false:
1. Try to find a new literal to watch (unassigned or true)
2. If found, update the watch
3. If the other watched literal is unassigned, propagate it (unit clause)
4. If both watched literals are false, conflict

This gives O(1) clause checking per assignment.

### Conflict Analysis

Uses the 1-UIP (First Unique Implication Point) scheme:
1. Start from conflict clause
2. Resolve with antecedent clauses until one literal from current decision level remains
3. Learn the resulting clause
4. Backtrack to the second-highest level in the learned clause

## References

- GRASP: J. P. Marques-Silva and K. A. Sakallah, "GRASP: A Search Algorithm for Propositional Satisfiability"
- Chaff: M. Moskewicz et al., "Chaff: Engineering an Efficient SAT Solver"
- MiniSat: N. Een and N. Sorensson, "An Extensible SAT-solver"
- Glucose: G. Audemard and L. Simon, "Predicting Learnt Clauses Quality in Modern SAT Solvers" (LBD)

## Development

```bash
# Run tests
cargo test

# Run with logging
RUST_LOG=debug paradox input.cnf

# Build release
cargo build --release
```

## Project Structure

```
src/
├── lib.rs           # Public API
├── main.rs          # CLI
├── literal.rs       # Literal/Variable types
├── clause.rs        # Clause type
├── formula.rs       # CNF formula
├── assignment.rs    # Variable assignments
├── trail.rs         # Decision trail
├── watch.rs         # Watched literals
├── solver/          # SAT solver
│   ├── mod.rs       # Main CDCL loop
│   ├── propagate.rs # Unit propagation
│   ├── decide.rs    # VSIDS
│   ├── conflict.rs  # Conflict analysis
│   ├── learn.rs     # Clause learning
│   ├── restart.rs   # Restart strategies
│   └── reduce.rs    # Clause deletion
├── parser/          # Input parsing
│   ├── dimacs.rs    # DIMACS CNF
│   └── smtlib.rs    # SMT-LIB 2
├── theory/          # Theory solvers
│   ├── mod.rs       # TheorySolver trait
│   ├── euf.rs       # Equality/UF
│   ├── lia.rs       # Linear arithmetic
│   ├── bv.rs        # Bitvectors
│   └── array.rs     # Arrays
└── dpll_t.rs        # DPLL(T) integration
```

## License

MIT
