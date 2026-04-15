//! Paradox CLI - SAT/SMT solver.

use clap::{Parser, Subcommand};
use paradox::{
    parse_dimacs_file, parse_smtlib_file,
    detect_format, InputFormat,
    solver::Solver,
    solver::maxsat::{MaxSatSolver, MaxSatResult, parse_wcnf},
    dpll_t::DpllT,
};
use std::fs::{self, File};
use std::io::Write;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

#[derive(Parser)]
#[command(name = "paradox")]
#[command(about = "SAT/SMT solver with CDCL and theory solvers")]
#[command(version)]
struct Cli {
    #[command(subcommand)]
    command: Option<Commands>,

    /// Input file (DIMACS CNF or SMT-LIB 2) - for direct invocation
    #[arg(global = true)]
    input: Option<PathBuf>,

    /// Show verbose output
    #[arg(short, long, global = true)]
    verbose: bool,

    /// Show statistics after solving
    #[arg(short, long, global = true)]
    stats: bool,

    /// Timeout in seconds
    #[arg(short, long, global = true)]
    timeout: Option<u64>,

    /// Force input format (dimacs or smtlib)
    #[arg(short, long, global = true)]
    format: Option<String>,

    /// Output proof to file (UNSAT only)
    #[arg(short, long, global = true)]
    proof: Option<PathBuf>,
}

#[derive(Subcommand)]
enum Commands {
    /// Solve a SAT/SMT problem
    Solve {
        /// Input file (DIMACS CNF or SMT-LIB 2)
        input: PathBuf,
    },
}

fn main() -> ExitCode {
    env_logger::init();
    let cli = Cli::parse();

    // Determine input file from either subcommand or direct argument
    let input = match &cli.command {
        Some(Commands::Solve { input }) => input.clone(),
        None => match &cli.input {
            Some(input) => input.clone(),
            None => {
                eprintln!("Error: No input file specified");
                eprintln!("Usage: paradox [OPTIONS] <INPUT>");
                eprintln!("       paradox solve [OPTIONS] <INPUT>");
                return ExitCode::FAILURE;
            }
        },
    };

    // Check for WCNF extension first
    let is_wcnf = input.extension()
        .map(|ext| ext == "wcnf")
        .unwrap_or(false)
        || cli.format.as_deref() == Some("wcnf")
        || cli.format.as_deref() == Some("maxsat");

    if is_wcnf {
        return solve_maxsat(&cli, &input);
    }

    // Detect or use specified format
    let format = if let Some(ref fmt) = cli.format {
        match fmt.to_lowercase().as_str() {
            "dimacs" | "cnf" => InputFormat::Dimacs,
            "smtlib" | "smt2" | "smt" => InputFormat::SmtLib,
            _ => {
                eprintln!("Unknown format: {}. Use 'dimacs', 'smtlib', or 'wcnf'.", fmt);
                return ExitCode::FAILURE;
            }
        }
    } else {
        detect_format(&input)
    };

    match format {
        InputFormat::Dimacs => solve_dimacs(&cli, &input),
        InputFormat::SmtLib => solve_smtlib(&cli, &input),
    }
}

fn solve_maxsat(cli: &Cli, input: &PathBuf) -> ExitCode {
    let start_time = Instant::now();

    // Read and parse WCNF file
    let content = match fs::read_to_string(input) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error reading {}: {}", input.display(), e);
            return ExitCode::FAILURE;
        }
    };

    let formula = match parse_wcnf(&content) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Error parsing {}: {}", input.display(), e);
            return ExitCode::FAILURE;
        }
    };

    if cli.verbose {
        eprintln!(
            "c Loaded {} variables, {} hard clauses, {} soft clauses (total weight: {})",
            formula.num_vars,
            formula.num_hard(),
            formula.num_soft(),
            formula.total_weight()
        );
    }

    // Create MaxSAT solver
    let mut solver = MaxSatSolver::new(formula);

    // Solve
    let result = solver.solve();
    let elapsed = start_time.elapsed();

    // Output result
    match result {
        MaxSatResult::Optimum { model, cost, satisfied } => {
            println!("s OPTIMUM FOUND");
            println!("o {}", cost);
            
            // Print model in DIMACS format
            print!("v ");
            for (i, &val) in model.iter().enumerate() {
                let var = (i + 1) as i32;
                print!("{} ", if val { var } else { -var });
            }
            println!("0");

            if cli.verbose {
                eprintln!("c Satisfied {} of {} soft clauses", satisfied.len(), solver.stats().relax_vars);
            }

            if cli.stats {
                print_maxsat_stats(&solver, elapsed);
            }
            ExitCode::from(10) // OPTIMUM convention
        }
        MaxSatResult::Unsatisfiable => {
            println!("s UNSATISFIABLE");
            
            if cli.stats {
                print_maxsat_stats(&solver, elapsed);
            }
            ExitCode::from(20) // UNSAT convention
        }
        MaxSatResult::Unknown => {
            println!("s UNKNOWN");
            if cli.stats {
                print_maxsat_stats(&solver, elapsed);
            }
            ExitCode::FAILURE
        }
    }
}

fn print_maxsat_stats(solver: &MaxSatSolver, elapsed: std::time::Duration) {
    let stats = solver.stats();
    eprintln!("c MaxSAT Statistics:");
    eprintln!("c   SAT calls: {}", stats.sat_calls);
    eprintln!("c   cores extracted: {}", stats.cores_extracted);
    eprintln!("c   relaxation vars: {}", stats.relax_vars);
    eprintln!("c   AMO constraints: {}", stats.amo_constraints);
    eprintln!("c   time: {:.2}s", elapsed.as_secs_f64());
}

fn solve_dimacs(cli: &Cli, input: &PathBuf) -> ExitCode {
    let start_time = Instant::now();

    // Parse input file
    let formula = match parse_dimacs_file(input) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Error parsing {}: {}", input.display(), e);
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

    let elapsed = start_time.elapsed();

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
                print_stats(&solver, elapsed);
            }
            ExitCode::from(10) // SAT convention
        }
        paradox::solver::SolveResult::Unsat => {
            println!("UNSAT");

            // Output proof if requested
            if let Some(ref proof_path) = cli.proof {
                if let Err(e) = write_proof(proof_path, &solver) {
                    eprintln!("Warning: Failed to write proof: {}", e);
                }
            }

            if cli.stats {
                print_stats(&solver, elapsed);
            }
            ExitCode::from(20) // UNSAT convention
        }
        paradox::solver::SolveResult::Unknown => {
            println!("UNKNOWN");
            if cli.stats {
                print_stats(&solver, elapsed);
            }
            ExitCode::FAILURE
        }
    }
}

fn solve_smtlib(cli: &Cli, input: &PathBuf) -> ExitCode {
    let start_time = Instant::now();

    // Parse input file
    let problem = match parse_smtlib_file(input) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Error parsing {}: {}", input.display(), e);
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
    let elapsed = start_time.elapsed();

    // Output result
    match result {
        paradox::solver::SolveResult::Sat(model) => {
            println!("sat");
            if cli.verbose {
                eprintln!("c Model: {:?}", model);
            }
            if cli.stats {
                print_smt_stats(elapsed);
            }
            ExitCode::from(10)
        }
        paradox::solver::SolveResult::Unsat => {
            println!("unsat");

            if let Some(ref proof_path) = cli.proof {
                if let Err(e) = write_smt_proof(proof_path) {
                    eprintln!("Warning: Failed to write proof: {}", e);
                }
            }

            if cli.stats {
                print_smt_stats(elapsed);
            }
            ExitCode::from(20)
        }
        paradox::solver::SolveResult::Unknown => {
            println!("unknown");
            if cli.stats {
                print_smt_stats(elapsed);
            }
            ExitCode::FAILURE
        }
    }
}

fn print_stats(solver: &Solver, elapsed: std::time::Duration) {
    let stats = solver.stats();
    eprintln!("c Statistics:");
    eprintln!("c   decisions: {}", stats.decisions);
    eprintln!("c   propagations: {}", stats.propagations);
    eprintln!("c   conflicts: {}", stats.conflicts);
    eprintln!("c   learned clauses: {}", stats.learned_clauses);
    eprintln!("c   restarts: {}", stats.restarts);
    eprintln!("c   time: {:.2}s", elapsed.as_secs_f64());
}

fn print_smt_stats(elapsed: std::time::Duration) {
    eprintln!("c Statistics:");
    eprintln!("c   time: {:.2}s", elapsed.as_secs_f64());
}

fn write_proof(path: &PathBuf, _solver: &Solver) -> std::io::Result<()> {
    let mut file = File::create(path)?;
    writeln!(file, "c Proof certificate")?;
    writeln!(file, "c Format: DRAT (simplified)")?;
    writeln!(file, "c")?;
    writeln!(file, "c Note: Full DRAT proof generation not yet implemented.")?;
    writeln!(file, "c This is a placeholder proof file.")?;
    writeln!(file, "c")?;
    writeln!(file, "0")?; // Empty clause marker
    Ok(())
}

fn write_smt_proof(path: &PathBuf) -> std::io::Result<()> {
    let mut file = File::create(path)?;
    writeln!(file, "; SMT proof certificate")?;
    writeln!(file, "; Format: Placeholder")?;
    writeln!(file, ";")?;
    writeln!(file, "; Note: Full SMT proof generation not yet implemented.")?;
    writeln!(file, "(proof placeholder)")?;
    Ok(())
}
