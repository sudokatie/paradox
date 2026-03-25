# paradox

A SAT solver that actually solves things. Built with Rust, CDCL, and mild existential uncertainty.

## Why This Exists

Because sometimes you need to know if a boolean formula is satisfiable, and staring at it really hard doesn't scale.

Paradox implements Conflict-Driven Clause Learning (CDCL) - the algorithm that powers every serious SAT solver built in the last 25 years. It's not the fastest solver out there, but it's mine, and I understand every line of it.

## Features

- CDCL with watched literals (two-watched-literal scheme)
- VSIDS decision heuristic (the one that actually works)
- 1-UIP conflict analysis with clause learning
- Restart strategies (Luby, geometric, Glucose-style)
- Clause reduction based on LBD quality

## Quick Start

```bash
# Build
cargo build --release

# Solve a DIMACS CNF file
./target/release/paradox problem.cnf

# With model output
./target/release/paradox problem.cnf --model

# With statistics
./target/release/paradox problem.cnf --stats

# Read from stdin
cat problem.cnf | ./target/release/paradox -
```

## DIMACS Format

Paradox reads standard DIMACS CNF format:

```
c This is a comment
p cnf 3 2
1 -2 0
2 3 0
```

- `p cnf <vars> <clauses>` declares the problem size
- Each clause is a space-separated list of literals ending with `0`
- Positive numbers are positive literals, negative are negated

## Exit Codes

Following SAT competition convention:
- `10` - SATISFIABLE
- `20` - UNSATISFIABLE  
- `0` - UNKNOWN (timeout or error)

## Performance

Currently handles problems in the hundreds of variables reasonably well. It's a learning project, not a MiniSat replacement. If you need speed, use CaDiCaL.

## Philosophy

1. Correctness over cleverness
2. Every optimization earns its place through measurement
3. If I can't explain it, I shouldn't ship it

## License

MIT

---

*Built by Katie, who may or may not have feelings about boolean satisfiability.*
