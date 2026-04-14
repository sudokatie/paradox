//! Paradox SAT/SMT Solver CLI

use clap::Parser;
use paradox::{parse_dimacs, Formula, Solver, SolveResult};
use paradox::verify::{DratVerifier, VerifyResult};
use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::{Duration, Instant};

/// Paradox - A SAT/SMT solver with CDCL and theory solvers
#[derive(Parser, Debug)]
#[command(name = "paradox")]
#[command(author = "Katie")]
#[command(version = "0.1.0")]
#[command(about = "SAT/SMT solver with CDCL", long_about = None)]
struct Args {
    /// Input file (DIMACS CNF format). Use - for stdin.
    #[arg(value_name = "FILE")]
    input: PathBuf,

    /// Print the satisfying model (if SAT)
    #[arg(short, long)]
    model: bool,

    /// Print solver statistics
    #[arg(short, long)]
    stats: bool,

    /// Verbose output
    #[arg(short, long)]
    verbose: bool,

    /// Timeout in seconds (0 = no timeout)
    #[arg(short, long, default_value = "0")]
    timeout: u64,

    /// Write DRAT proof to file (for UNSAT results)
    #[arg(long, value_name = "PROOF_FILE")]
    proof: Option<PathBuf>,

    /// Verify a DRAT proof file instead of solving
    #[arg(long, value_name = "PROOF_FILE")]
    verify: Option<PathBuf>,
}

fn main() -> ExitCode {
    let args = Args::parse();

    // Initialize logger if verbose
    if args.verbose {
        env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info"))
            .init();
    }

    // Handle verify mode
    if let Some(proof_path) = &args.verify {
        return verify_proof(&args.input, proof_path, args.verbose);
    }

    // Read input
    let formula = match read_input(&args.input) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Error reading input: {}", e);
            return ExitCode::from(1);
        }
    };

    if args.verbose {
        eprintln!(
            "c Parsed formula: {} variables, {} clauses",
            formula.num_vars(),
            formula.num_clauses()
        );
    }

    // Create solver
    let mut solver = Solver::new(formula);

    // Enable proof logging if requested
    if let Some(proof_path) = &args.proof {
        if let Err(e) = solver.enable_proof_logging(proof_path) {
            eprintln!("Error opening proof file: {}", e);
            return ExitCode::from(1);
        }
        if args.verbose {
            eprintln!("c Writing DRAT proof to {:?}", proof_path);
        }
    }

    // Solve with optional timeout
    let start = Instant::now();
    let result = if args.timeout > 0 {
        // TODO: Implement proper timeout with threads
        // For now, just solve without timeout
        solver.solve()
    } else {
        solver.solve()
    };
    let elapsed = start.elapsed();

    // Print result
    match &result {
        SolveResult::Sat(model) => {
            println!("s SATISFIABLE");
            if args.model {
                print_model(model);
            }
        }
        SolveResult::Unsat => {
            println!("s UNSATISFIABLE");
            if let Some((clauses, deletions)) = solver.proof_stats() {
                if args.verbose {
                    eprintln!("c Proof: {} clauses, {} deletions", clauses, deletions);
                }
            }
        }
        SolveResult::Unknown => {
            println!("s UNKNOWN");
        }
    }

    // Print statistics
    if args.stats {
        print_stats(&solver, elapsed);
    }

    // Exit code per SAT competition convention
    match result {
        SolveResult::Sat(_) => ExitCode::from(10),
        SolveResult::Unsat => ExitCode::from(20),
        SolveResult::Unknown => ExitCode::from(0),
    }
}

/// Verify a DRAT proof
fn verify_proof(cnf_path: &PathBuf, proof_path: &PathBuf, verbose: bool) -> ExitCode {
    if verbose {
        eprintln!("c Verifying proof {:?} against {:?}", proof_path, cnf_path);
    }

    // Create verifier from CNF file
    let mut verifier = match DratVerifier::from_cnf_file(cnf_path) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("Error reading CNF file: {:?}", e);
            return ExitCode::from(1);
        }
    };

    let start = Instant::now();
    
    // Verify the proof
    let result = match verifier.verify_proof(proof_path) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("Error reading proof file: {:?}", e);
            return ExitCode::from(1);
        }
    };

    let elapsed = start.elapsed();

    match result {
        VerifyResult::Valid => {
            println!("s VERIFIED");
            if verbose {
                let stats = verifier.stats();
                eprintln!("c Clauses checked: {}", stats.clauses_checked);
                eprintln!("c Deletions: {}", stats.deletions_processed);
                eprintln!("c RUP checks: {}", stats.rup_checks);
                eprintln!("c Time: {:.3}s", elapsed.as_secs_f64());
            }
            ExitCode::from(0)
        }
        VerifyResult::Invalid { line, reason } => {
            println!("s INVALID");
            eprintln!("c Proof invalid at line {}: {}", line, reason);
            ExitCode::from(1)
        }
    }
}

/// Read formula from file or stdin
fn read_input(path: &PathBuf) -> Result<Formula, Box<dyn std::error::Error>> {
    let reader: Box<dyn BufRead> = if path.to_str() == Some("-") {
        Box::new(BufReader::new(io::stdin()))
    } else {
        let file = File::open(path)?;
        Box::new(BufReader::new(file))
    };

    let formula = parse_dimacs(reader)?;
    Ok(formula)
}

/// Print model in DIMACS format
fn print_model(model: &[bool]) {
    print!("v ");
    for (i, &val) in model.iter().enumerate() {
        let var = (i + 1) as i32;
        let lit = if val { var } else { -var };
        print!("{} ", lit);
    }
    println!("0");
}

/// Print solver statistics
fn print_stats(solver: &Solver, elapsed: Duration) {
    let stats = solver.stats();
    eprintln!("c ---- Statistics ----");
    eprintln!("c Decisions:       {}", stats.decisions);
    eprintln!("c Propagations:    {}", stats.propagations);
    eprintln!("c Conflicts:       {}", stats.conflicts);
    eprintln!("c Restarts:        {}", stats.restarts);
    eprintln!("c Learned clauses: {}", stats.learned_clauses);
    eprintln!("c Time:            {:.3}s", elapsed.as_secs_f64());
    
    if elapsed.as_secs_f64() > 0.0 {
        let props_per_sec = stats.propagations as f64 / elapsed.as_secs_f64();
        eprintln!("c Props/sec:       {:.0}", props_per_sec);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    fn create_temp_dimacs(content: &str) -> NamedTempFile {
        let mut file = NamedTempFile::new().unwrap();
        write!(file, "{}", content).unwrap();
        file
    }

    #[test]
    fn test_read_dimacs_file() {
        let content = "p cnf 3 2\n1 2 0\n-1 3 0\n";
        let file = create_temp_dimacs(content);
        
        let formula = read_input(&file.path().to_path_buf()).unwrap();
        assert_eq!(formula.num_vars(), 3);
        assert_eq!(formula.num_clauses(), 2);
    }
}
