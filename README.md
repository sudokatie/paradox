# paradox

A SAT/SMT solver that actually solves things. Built with Rust, CDCL, and mild existential uncertainty.

## Why This Exists

Because sometimes you need to know if a boolean formula is satisfiable, and staring at it really hard doesn't scale.

Paradox implements Conflict-Driven Clause Learning (CDCL) - the algorithm that powers every serious SAT solver built in the last 25 years. It also includes theory solvers for SMT (Satisfiability Modulo Theories).

## Features

**SAT Solving (CDCL)**
- Two-watched-literal propagation
- VSIDS decision heuristic
- 1-UIP conflict analysis with clause learning
- Restart strategies (Luby, geometric, Glucose-style)
- Clause reduction based on LBD quality

**SMT Theories**
- EUF (Equality with Uninterpreted Functions)
- LIA (Linear Integer Arithmetic)
- Bitvectors (fixed-width arithmetic)
- Arrays (read/write with lazy axiom instantiation)

## Installation

```bash
cargo build --release
```

## Quick Start

```bash
# Solve a DIMACS CNF file
./target/release/paradox examples/simple.cnf

# Show the satisfying assignment
./target/release/paradox examples/simple.cnf --model

# Show solver statistics
./target/release/paradox examples/simple.cnf --stats

# Read from stdin
cat problem.cnf | ./target/release/paradox -
```

## Examples

The `examples/` directory contains sample problems:

**SAT (DIMACS CNF)**
- `simple.cnf` - Basic satisfiable formula
- `unsatisfiable.cnf` - Pigeonhole principle (always UNSAT)
- `3sat.cnf` - Random 3-SAT instance
- `sudoku.cnf` - Tiny 2x2 Sudoku encoding

**SMT (SMT-LIB 2)**
- `euf.smt2` - Equality and congruence
- `lia.smt2` - Linear integer constraints
- `bitvec.smt2` - Bitvector arithmetic
- `array.smt2` - Read-over-write axioms

Try them:

```bash
# SAT examples
./target/release/paradox examples/simple.cnf --model
./target/release/paradox examples/unsatisfiable.cnf
./target/release/paradox examples/3sat.cnf --stats

# Verify UNSAT (pigeonhole - 3 pigeons, 2 holes)
./target/release/paradox examples/unsatisfiable.cnf
# Exit code: 20 (UNSAT)
```

## DIMACS Format

Standard DIMACS CNF format:

```
c Comment line
p cnf 3 2
1 -2 0
2 3 0
```

- `p cnf <vars> <clauses>` declares problem size
- Clauses are space-separated literals ending with `0`
- Positive = true, negative = negated

## Exit Codes

Following SAT competition convention:
- `10` - SATISFIABLE
- `20` - UNSATISFIABLE  
- `0` - UNKNOWN (timeout or error)

## How It Works

### CDCL Algorithm

```
while true:
    conflict = propagate()
    if conflict:
        if level == 0: return UNSAT
        learned, backtrack_level = analyze(conflict)
        add_clause(learned)
        backtrack(backtrack_level)
    else if all_assigned():
        return SAT
    else:
        if should_restart(): restart()
        if should_reduce(): reduce_clauses()
        decide()
```

### Key Techniques

**Watched Literals**: Instead of checking every clause on every assignment, we watch two literals per clause. Propagation is only triggered when a watched literal becomes false.

**VSIDS**: Variable State Independent Decaying Sum. Variables involved in conflicts get "bumped" and decay over time. Tends to focus search on relevant parts of the problem.

**1-UIP Learning**: On conflict, we resolve backwards through the implication graph until we find the First Unique Implication Point - the single literal responsible for the conflict at the current decision level.

**LBD (Literal Block Distance)**: Measures clause quality by counting distinct decision levels. Lower LBD = more "glue" = keep it. High LBD clauses get deleted.

## Performance

Handles problems with hundreds of variables in milliseconds. For thousand+ variable problems, expect seconds. This is a learning project - if you need industrial-strength performance, use CaDiCaL or Z3.

## References

- [GRASP: A Search Algorithm for Propositional Satisfiability](https://doi.org/10.1109/12.769433) - Original CDCL
- [Chaff: Engineering an Efficient SAT Solver](https://doi.org/10.1145/378239.379017) - Two-watched literals, VSIDS
- [Predicting Learnt Clauses Quality in Modern SAT Solvers](https://www.ijcai.org/Proceedings/09/Papers/074.pdf) - LBD metric
- [Handbook of Satisfiability](https://doi.org/10.3233/978-1-58603-929-5-131) - Comprehensive reference

## License

MIT

---

*Built by Katie, who may or may not have feelings about boolean satisfiability.*
