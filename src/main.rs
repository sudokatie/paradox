//! Paradox CLI - SAT/SMT solver.

use clap::Parser;
use paradox::{
    parse_dimacs_file, parse_smtlib_file,
    detect_format, InputFormat,
    solver::Solver,
    dpll_t::DpllT,
};
use std::path::PathBuf;
use std::process::ExitCode;

#[derive(Parser)]
#[command(name = "paradox")]
#[command(about = "SAT/SMT solver with CDCL and theory solvers")]
#[command(version)]
struct Cli {
    /// Input file (DIMACS CNF or SMT-LIB 2)
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

    /// Force input format (dimacs or smtlib)
    #[arg(short, long)]
    format: Option<String>,
}

fn main() -> ExitCode {
    env_logger::init();
    let cli = Cli::parse();

    // Detect or use specified format
    let format = if let Some(ref fmt) = cli.format {
        match fmt.to_lowercase().as_str() {
            "dimacs" | "cnf" => InputFormat::Dimacs,
            "smtlib" | "smt2" | "smt" => InputFormat::SmtLib,
            _ => {
                eprintln!("Unknown format: {}. Use 'dimacs' or 'smtlib'.", fmt);
                return ExitCode::FAILURE;
            }
        }
    } else {
        detect_format(&cli.input)
    };

    match format {
        InputFormat::Dimacs => solve_dimacs(&cli),
        InputFormat::SmtLib => solve_smtlib(&cli),
    }
}

fn solve_dimacs(cli: &Cli) -> ExitCode {
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

fn solve_smtlib(cli: &Cli) -> ExitCode {
    // Parse input file
    let problem = match parse_smtlib_file(&cli.input) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Error parsing {}: {}", cli.input.display(), e);
            return ExitCode::FAILURE;
        }
    };

    if cli.verbose {
        if let Some(ref logic) = problem.logic {
            eprintln!("c Logic: {:?}", logic);
        }
        eprintln!(
            "c {} declarations, {} assertions",
            problem.declarations.len(),
            problem.assertions.len()
        );
    }

    // Create DPLL(T) solver
    let mut solver = DpllT::new(problem);

    // Solve
    let result = solver.solve();

    // Output result
    match result {
        paradox::solver::SolveResult::Sat(model) => {
            println!("sat");
            if cli.verbose {
                // Print model (would need variable name mapping for proper output)
                eprintln!("c Model: {:?}", model);
            }
            ExitCode::from(10)
        }
        paradox::solver::SolveResult::Unsat => {
            println!("unsat");
            ExitCode::from(20)
        }
        paradox::solver::SolveResult::Unknown => {
            println!("unknown");
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
