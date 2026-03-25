//! Paradox CLI - SAT/SMT solver.

use clap::Parser;
use paradox::{parse_dimacs_file, solver::Solver};
use std::path::PathBuf;
use std::process::ExitCode;

#[derive(Parser)]
#[command(name = "paradox")]
#[command(about = "SAT/SMT solver with CDCL")]
struct Cli {
    /// Input file (DIMACS CNF or SMT-LIB)
    input: PathBuf,

    /// Show verbose output
    #[arg(short, long)]
    verbose: bool,

    /// Show statistics after solving
    #[arg(short, long)]
    stats: bool,

    /// Timeout in seconds
    #[arg(short, long)]
    timeout: Option<u64>,
}

fn main() -> ExitCode {
    env_logger::init();
    let cli = Cli::parse();

    // Parse input file
    let formula = match parse_dimacs_file(&cli.input) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Error parsing {}: {}", cli.input.display(), e);
            return ExitCode::FAILURE;
        }
    };

    if cli.verbose {
        eprintln!(
            "c Loaded {} variables, {} clauses",
            formula.num_vars(),
            formula.num_clauses()
        );
    }

    // Create solver
    let mut solver = Solver::new(formula);

    // Solve
    let result = if let Some(timeout) = cli.timeout {
        solver.solve_with_timeout(std::time::Duration::from_secs(timeout))
    } else {
        solver.solve()
    };

    // Output result
    match result {
        paradox::solver::SolveResult::Sat(model) => {
            println!("SAT");
            // Print model in DIMACS format
            for (i, &val) in model.iter().enumerate() {
                let var = (i + 1) as i32;
                print!("{} ", if val { var } else { -var });
            }
            println!("0");

            if cli.stats {
                print_stats(&solver);
            }
            ExitCode::from(10) // SAT convention
        }
        paradox::solver::SolveResult::Unsat => {
            println!("UNSAT");
            if cli.stats {
                print_stats(&solver);
            }
            ExitCode::from(20) // UNSAT convention
        }
        paradox::solver::SolveResult::Unknown => {
            println!("UNKNOWN");
            if cli.stats {
                print_stats(&solver);
            }
            ExitCode::FAILURE
        }
    }
}

fn print_stats(solver: &Solver) {
    let stats = solver.stats();
    eprintln!("c Statistics:");
    eprintln!("c   decisions: {}", stats.decisions);
    eprintln!("c   propagations: {}", stats.propagations);
    eprintln!("c   conflicts: {}", stats.conflicts);
    eprintln!("c   learned clauses: {}", stats.learned_clauses);
    eprintln!("c   restarts: {}", stats.restarts);
}
