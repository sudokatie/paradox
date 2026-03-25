# Paradox

SAT/SMT solver with CDCL (Conflict-Driven Clause Learning) and theory solvers.

## Features

- **SAT Solving**: CDCL algorithm with watched literals, VSIDS, and clause learning
- **SMT Solving**: DPLL(T) architecture with theory solvers (planned)
- **Input Formats**: DIMACS CNF, SMT-LIB 2 (planned)

## Installation

```bash
cargo install --path .
```

## Usage

```bash
# Solve a DIMACS CNF file
paradox input.cnf

# With verbose output
paradox -v input.cnf

# With statistics
paradox -s input.cnf

# With timeout (seconds)
paradox -t 60 input.cnf
```

## DIMACS CNF Format

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

## Exit Codes

- `10`: SAT (satisfiable)
- `20`: UNSAT (unsatisfiable)
- `1`: Error or unknown

## Development

```bash
# Run tests
cargo test

# Run with logging
RUST_LOG=debug paradox input.cnf
```

## License

MIT
