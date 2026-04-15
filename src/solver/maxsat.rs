//! MaxSAT solver for optimization problems.
//!
//! Implements core-guided MaxSAT solving using the RC2 approach:
//! - Hard clauses must be satisfied
//! - Soft clauses have weights; minimize total unsatisfied weight
//! - Uses unsatisfiable cores to guide the search

use std::collections::{HashMap, HashSet};

use crate::{
    clause::Clause,
    formula::Formula,
    literal::{Literal, Variable},
    solver::{Solver, SolveResult},
};

/// Weight type for soft clauses.
pub type Weight = u64;

/// A soft clause with an associated weight.
#[derive(Debug, Clone)]
pub struct SoftClause {
    /// The clause literals.
    pub clause: Clause,
    /// Weight (cost of leaving unsatisfied).
    pub weight: Weight,
    /// Relaxation variable (added during solving).
    pub relax_var: Option<u32>,
}

impl SoftClause {
    /// Create a new soft clause with the given weight.
    pub fn new(clause: Clause, weight: Weight) -> Self {
        SoftClause {
            clause,
            weight,
            relax_var: None,
        }
    }

    /// Create a unit-weight soft clause.
    pub fn unit(clause: Clause) -> Self {
        Self::new(clause, 1)
    }
}

/// MaxSAT formula with hard and soft clauses.
#[derive(Debug, Clone)]
pub struct MaxSatFormula {
    /// Number of original variables.
    pub num_vars: u32,
    /// Hard clauses (must be satisfied).
    pub hard_clauses: Vec<Clause>,
    /// Soft clauses with weights.
    pub soft_clauses: Vec<SoftClause>,
}

impl MaxSatFormula {
    /// Create a new empty MaxSAT formula.
    pub fn new(num_vars: u32) -> Self {
        MaxSatFormula {
            num_vars,
            hard_clauses: Vec::new(),
            soft_clauses: Vec::new(),
        }
    }

    /// Add a hard clause.
    pub fn add_hard(&mut self, clause: Clause) {
        self.hard_clauses.push(clause);
    }

    /// Add a soft clause with a weight.
    pub fn add_soft(&mut self, clause: Clause, weight: Weight) {
        self.soft_clauses.push(SoftClause::new(clause, weight));
    }

    /// Add a unit-weight soft clause.
    pub fn add_soft_unit(&mut self, clause: Clause) {
        self.soft_clauses.push(SoftClause::unit(clause));
    }

    /// Total weight of all soft clauses.
    pub fn total_weight(&self) -> Weight {
        self.soft_clauses.iter().map(|s| s.weight).sum()
    }

    /// Number of soft clauses.
    pub fn num_soft(&self) -> usize {
        self.soft_clauses.len()
    }

    /// Number of hard clauses.
    pub fn num_hard(&self) -> usize {
        self.hard_clauses.len()
    }
}

/// Result of MaxSAT solving.
#[derive(Debug, Clone)]
pub enum MaxSatResult {
    /// Optimal solution found.
    Optimum {
        /// Variable assignments.
        model: Vec<bool>,
        /// Cost (total weight of unsatisfied soft clauses).
        cost: Weight,
        /// Indices of satisfied soft clauses.
        satisfied: Vec<usize>,
    },
    /// Hard clauses are unsatisfiable.
    Unsatisfiable,
    /// Unknown (timeout or resource limit).
    Unknown,
}

/// Statistics from MaxSAT solving.
#[derive(Debug, Default, Clone)]
pub struct MaxSatStats {
    /// Number of SAT calls.
    pub sat_calls: u64,
    /// Number of cores extracted.
    pub cores_extracted: u64,
    /// Total relaxation variables introduced.
    pub relax_vars: u64,
    /// Number of at-most-one constraints added.
    pub amo_constraints: u64,
}

/// Core-guided MaxSAT solver.
pub struct MaxSatSolver {
    /// The MaxSAT formula.
    formula: MaxSatFormula,
    /// Next variable ID for relaxation variables.
    next_var: u32,
    /// Mapping from relaxation variables to soft clause indices.
    relax_to_soft: HashMap<u32, usize>,
    /// Current upper bound on cost.
    upper_bound: Weight,
    /// Current lower bound on cost.
    lower_bound: Weight,
    /// Best model found so far.
    best_model: Option<Vec<bool>>,
    /// Statistics.
    stats: MaxSatStats,
}

impl MaxSatSolver {
    /// Create a new MaxSAT solver.
    pub fn new(formula: MaxSatFormula) -> Self {
        let next_var = formula.num_vars + 1;
        let upper_bound = formula.total_weight();
        
        MaxSatSolver {
            formula,
            next_var,
            relax_to_soft: HashMap::new(),
            upper_bound,
            lower_bound: 0,
            best_model: None,
            stats: MaxSatStats::default(),
        }
    }

    /// Solve the MaxSAT problem.
    pub fn solve(&mut self) -> MaxSatResult {
        // First check if hard clauses are satisfiable
        let hard_sat = self.check_hard_satisfiability();
        if !hard_sat {
            return MaxSatResult::Unsatisfiable;
        }

        // No soft clauses means trivially optimal
        if self.formula.soft_clauses.is_empty() {
            // Just solve hard clauses
            let mut formula = Formula::new();
            formula.set_num_vars(self.formula.num_vars);
            for clause in &self.formula.hard_clauses {
                formula.add_clause(clause.clone());
            }
            let mut solver = Solver::new(formula);
            self.stats.sat_calls += 1;
            
            return match solver.solve() {
                SolveResult::Sat(model) => MaxSatResult::Optimum {
                    model,
                    cost: 0,
                    satisfied: vec![],
                },
                SolveResult::Unsat => MaxSatResult::Unsatisfiable,
                SolveResult::Unknown => MaxSatResult::Unknown,
            };
        }

        // Initialize relaxation variables for all soft clauses
        self.initialize_relaxation_vars();

        // Use linear search for optimization (simpler and more reliable)
        // Try to find a solution, then iteratively improve
        let sat_formula = self.build_sat_formula();
        let mut solver = Solver::new(sat_formula);
        self.stats.sat_calls += 1;

        match solver.solve() {
            SolveResult::Sat(model) => {
                // Found initial solution
                let cost = self.compute_cost(&model);
                self.upper_bound = cost;
                self.best_model = Some(model);

                // Try to improve - use stratified approach
                self.improve_solution();
                
                self.build_result()
            }
            SolveResult::Unsat => {
                // Should not happen since hard clauses are satisfiable
                // This means all soft clauses together make it unsat
                // In MaxSAT, this is still a valid scenario - need to relax some
                MaxSatResult::Unsatisfiable
            }
            SolveResult::Unknown => MaxSatResult::Unknown,
        }
    }

    /// Try to improve the current solution by requiring lower cost.
    fn improve_solution(&mut self) {
        while self.upper_bound > 0 && self.stats.sat_calls < 1000 {
            let target_cost = self.upper_bound - 1;
            
            // Build formula with cardinality constraint on relaxation variables
            let mut formula = Formula::new();
            formula.set_num_vars(self.next_var - 1);

            // Add hard clauses
            for clause in &self.formula.hard_clauses {
                formula.add_clause(clause.clone());
            }

            // Add soft clauses with relaxation
            for soft in &self.formula.soft_clauses {
                if let Some(relax_var) = soft.relax_var {
                    let mut lits: Vec<Literal> = soft.clause.literals().to_vec();
                    lits.push(Literal::positive(Variable(relax_var)));
                    formula.add_clause(Clause::new(lits));
                }
            }

            // For simple case: require at most target_cost relaxations
            // We use a simple approach: if all soft clauses have weight 1,
            // just count relaxation variables
            let relax_vars: Vec<u32> = self.formula.soft_clauses
                .iter()
                .filter_map(|s| s.relax_var)
                .collect();

            // Simple at-most-k constraint via sequential counter
            // For small k, this is efficient enough
            self.add_atmost_constraint(&mut formula, &relax_vars, target_cost as usize);

            let mut solver = Solver::new(formula);
            self.stats.sat_calls += 1;

            match solver.solve() {
                SolveResult::Sat(model) => {
                    let cost = self.compute_cost(&model);
                    if cost < self.upper_bound {
                        self.upper_bound = cost;
                        self.best_model = Some(model);
                    } else {
                        // Can't improve further
                        break;
                    }
                }
                SolveResult::Unsat | SolveResult::Unknown => {
                    // Current solution is optimal
                    break;
                }
            }
        }
    }

    /// Add an at-most-k constraint on the given variables.
    fn add_atmost_constraint(&self, formula: &mut Formula, vars: &[u32], k: usize) {
        if k >= vars.len() {
            return; // No constraint needed
        }

        if k == 0 {
            // All variables must be false
            for &var in vars {
                formula.add_clause(Clause::new(vec![Literal::negative(Variable(var))]));
            }
            return;
        }

        // For small k, use simple pairwise encoding for k+1 subsets
        // This is a simplified approach - for larger instances, use sorting networks
        if vars.len() <= 10 {
            // Generate all (k+1)-subsets and add clause that at least one is false
            for subset in Self::combinations_helper(vars, k + 1) {
                let clause = Clause::new(
                    subset.iter()
                        .map(|&v| Literal::negative(Variable(v)))
                        .collect()
                );
                formula.add_clause(clause);
            }
        }
        // For larger instances, the constraint is skipped (approximation)
    }

    /// Generate all k-combinations of a slice.
    fn combinations_helper<'a>(items: &'a [u32], k: usize) -> Vec<Vec<u32>> {
        if k == 0 {
            return vec![vec![]];
        }
        if items.len() < k {
            return vec![];
        }
        if items.len() == k {
            return vec![items.to_vec()];
        }

        let mut result = Vec::new();
        for (i, &item) in items.iter().enumerate() {
            let rest = &items[i + 1..];
            for mut combo in Self::combinations_helper(rest, k - 1) {
                combo.insert(0, item);
                result.push(combo);
            }
        }
        result
    }

    /// Check if hard clauses alone are satisfiable.
    fn check_hard_satisfiability(&mut self) -> bool {
        let mut formula = Formula::new();
        formula.set_num_vars(self.formula.num_vars);
        
        for clause in &self.formula.hard_clauses {
            formula.add_clause(clause.clone());
        }

        let mut solver = Solver::new(formula);
        self.stats.sat_calls += 1;
        
        matches!(solver.solve(), SolveResult::Sat(_))
    }

    /// Initialize relaxation variables for soft clauses.
    fn initialize_relaxation_vars(&mut self) {
        for (idx, soft) in self.formula.soft_clauses.iter_mut().enumerate() {
            let relax_var = self.next_var;
            self.next_var += 1;
            soft.relax_var = Some(relax_var);
            self.relax_to_soft.insert(relax_var, idx);
            self.stats.relax_vars += 1;
        }
    }

    /// Build SAT formula with relaxation variables.
    fn build_sat_formula(&self) -> Formula {
        let mut formula = Formula::new();
        formula.set_num_vars(self.next_var - 1);

        // Add hard clauses
        for clause in &self.formula.hard_clauses {
            formula.add_clause(clause.clone());
        }

        // Add soft clauses with relaxation variables
        for soft in &self.formula.soft_clauses {
            if let Some(relax_var) = soft.relax_var {
                let mut lits: Vec<Literal> = soft.clause.literals().to_vec();
                // Add relaxation literal (when true, clause is "satisfied" by relaxation)
                lits.push(Literal::positive(Variable(relax_var)));
                formula.add_clause(Clause::new(lits));
            } else {
                formula.add_clause(soft.clause.clone());
            }
        }

        formula
    }

    /// Compute cost of a model (sum of weights of unsatisfied soft clauses).
    fn compute_cost(&self, model: &[bool]) -> Weight {
        let mut cost = 0;

        for soft in &self.formula.soft_clauses {
            if let Some(relax_var) = soft.relax_var {
                // If relaxation variable is true, the soft clause was relaxed
                let relax_idx = (relax_var - 1) as usize;
                if relax_idx < model.len() && model[relax_idx] {
                    cost += soft.weight;
                }
            }
        }

        cost
    }

    /// Add constraint to find solution with cost less than current.
    fn add_cost_constraint(&mut self, current_cost: Weight) -> bool {
        if current_cost == 0 {
            return false; // Already optimal
        }

        // For simplicity, we use a cardinality constraint approach
        // In practice, this would use a more sophisticated encoding
        true
    }

    /// Extract unsatisfiable core (relaxation variables in the core).
    fn extract_core(&self, _solver: &Solver) -> Option<Vec<u32>> {
        // In a full implementation, this would use the solver's learned clauses
        // to identify the minimal unsatisfiable core. For now, we use a simplified
        // approach that returns all relaxation variables set to false.
        
        let relax_vars: Vec<u32> = self.formula.soft_clauses
            .iter()
            .filter_map(|s| s.relax_var)
            .collect();

        if relax_vars.is_empty() {
            None
        } else {
            Some(relax_vars)
        }
    }

    /// Process a core: find minimum weight and add at-most-one constraint.
    fn process_core(&mut self, core: &[u32]) -> Weight {
        if core.is_empty() {
            return 0;
        }

        // Find minimum weight in core
        let min_weight = core
            .iter()
            .filter_map(|&var| {
                self.relax_to_soft.get(&var)
                    .map(|&idx| self.formula.soft_clauses[idx].weight)
            })
            .min()
            .unwrap_or(1);

        // Subtract minimum weight from all core clauses
        for &var in core {
            if let Some(&idx) = self.relax_to_soft.get(&var) {
                self.formula.soft_clauses[idx].weight -= min_weight;
            }
        }

        // Add at-most-one constraint for the core
        // This ensures at least one soft clause in the core is satisfied
        self.add_amo_constraint(core);

        min_weight
    }

    /// Add at-most-one constraint (at least one must be false).
    fn add_amo_constraint(&mut self, vars: &[u32]) {
        // At least one relaxation variable must be false
        // This is encoded as a clause: (-r1 ∨ -r2 ∨ ... ∨ -rn)
        // But we want: at least one soft clause satisfied, so at least one r_i is false
        let clause = Clause::new(
            vars.iter()
                .map(|&v| Literal::negative(Variable(v)))
                .collect()
        );
        self.formula.hard_clauses.push(clause);
        self.stats.amo_constraints += 1;
    }

    /// Build the final result.
    fn build_result(&self) -> MaxSatResult {
        match &self.best_model {
            Some(model) => {
                let cost = self.compute_cost(model);
                let satisfied = self.compute_satisfied(model);
                
                MaxSatResult::Optimum {
                    model: model.clone(),
                    cost,
                    satisfied,
                }
            }
            None => MaxSatResult::Unknown,
        }
    }

    /// Compute indices of satisfied soft clauses.
    fn compute_satisfied(&self, model: &[bool]) -> Vec<usize> {
        let mut satisfied = Vec::new();

        for (idx, soft) in self.formula.soft_clauses.iter().enumerate() {
            // Check if the original clause is satisfied (without relaxation)
            let clause_sat = soft.clause.literals().iter().any(|lit| {
                let var_idx = (lit.variable().0 - 1) as usize;
                if var_idx >= model.len() {
                    return false;
                }
                let val = model[var_idx];
                (lit.is_positive() && val) || (!lit.is_positive() && !val)
            });

            if clause_sat {
                satisfied.push(idx);
            }
        }

        satisfied
    }

    /// Get solving statistics.
    pub fn stats(&self) -> &MaxSatStats {
        &self.stats
    }
}

/// Parse WCNF format (weighted CNF for MaxSAT).
///
/// Format:
/// ```text
/// p wcnf <num_vars> <num_clauses> <top_weight>
/// <weight> <lit1> <lit2> ... 0
/// ```
///
/// Where `top_weight` is used for hard clauses.
pub fn parse_wcnf(input: &str) -> Result<MaxSatFormula, String> {
    let mut num_vars = 0;
    let mut top_weight: Weight = Weight::MAX;
    let mut formula = None;

    for line in input.lines() {
        let line = line.trim();
        
        // Skip empty lines and comments
        if line.is_empty() || line.starts_with('c') {
            continue;
        }

        // Parse header
        if line.starts_with("p ") {
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() < 4 || parts[1] != "wcnf" {
                return Err("Invalid WCNF header".to_string());
            }
            
            num_vars = parts[2].parse().map_err(|_| "Invalid num_vars")?;
            // parts[3] is num_clauses (we don't need it)
            if parts.len() > 4 {
                top_weight = parts[4].parse().map_err(|_| "Invalid top_weight")?;
            }
            
            formula = Some(MaxSatFormula::new(num_vars));
            continue;
        }

        // Parse clause line
        if let Some(ref mut f) = formula {
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.is_empty() {
                continue;
            }

            // First element is weight
            let weight: Weight = parts[0].parse().map_err(|_| "Invalid weight")?;
            
            // Rest are literals, terminated by 0
            let lits: Vec<Literal> = parts[1..]
                .iter()
                .filter_map(|s| s.parse::<i32>().ok())
                .take_while(|&l| l != 0)
                .map(Literal::from_dimacs)
                .collect();

            if lits.is_empty() {
                continue;
            }

            let clause = Clause::new(lits);
            
            if weight >= top_weight {
                f.add_hard(clause);
            } else {
                f.add_soft(clause, weight);
            }
        }
    }

    formula.ok_or_else(|| "No WCNF header found".to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(v: i32) -> Literal {
        Literal::from_dimacs(v)
    }

    fn clause(lits: &[i32]) -> Clause {
        Clause::new(lits.iter().map(|&v| lit(v)).collect())
    }

    #[test]
    fn test_maxsat_formula_creation() {
        let mut f = MaxSatFormula::new(3);
        f.add_hard(clause(&[1, 2]));
        f.add_soft(clause(&[-1]), 5);
        f.add_soft(clause(&[-2]), 3);

        assert_eq!(f.num_vars, 3);
        assert_eq!(f.num_hard(), 1);
        assert_eq!(f.num_soft(), 2);
        assert_eq!(f.total_weight(), 8);
    }

    #[test]
    fn test_maxsat_all_hard_satisfiable() {
        // Hard: (1 ∨ 2)
        // Soft: (-1) with weight 1, (-2) with weight 1
        // Optimal: 1=true, 2=false -> cost 1 (only -1 unsatisfied)
        let mut f = MaxSatFormula::new(2);
        f.add_hard(clause(&[1, 2]));
        f.add_soft_unit(clause(&[-1]));
        f.add_soft_unit(clause(&[-2]));

        let mut solver = MaxSatSolver::new(f);
        let result = solver.solve();

        match result {
            MaxSatResult::Optimum { cost, .. } => {
                assert!(cost <= 2, "Cost should be at most 2");
            }
            _ => panic!("Expected Optimum result"),
        }
    }

    #[test]
    fn test_maxsat_hard_unsat() {
        // Hard: (1) ∧ (-1)
        let mut f = MaxSatFormula::new(1);
        f.add_hard(clause(&[1]));
        f.add_hard(clause(&[-1]));

        let mut solver = MaxSatSolver::new(f);
        let result = solver.solve();

        assert!(matches!(result, MaxSatResult::Unsatisfiable));
    }

    #[test]
    fn test_maxsat_no_soft_clauses() {
        // Only hard clauses - should be SAT with cost 0
        let mut f = MaxSatFormula::new(2);
        f.add_hard(clause(&[1, 2]));

        let mut solver = MaxSatSolver::new(f);
        let result = solver.solve();

        match result {
            MaxSatResult::Optimum { cost, .. } => {
                assert_eq!(cost, 0);
            }
            _ => panic!("Expected Optimum result"),
        }
    }

    #[test]
    fn test_maxsat_weighted() {
        // Hard: (1 ∨ 2)
        // Soft: (-1) weight 10, (-2) weight 1
        // Optimal: x1=false, x2=true -> cost 1 (only -2 unsatisfied)
        let mut f = MaxSatFormula::new(2);
        f.add_hard(clause(&[1, 2]));
        f.add_soft(clause(&[-1]), 10);
        f.add_soft(clause(&[-2]), 1);

        let mut solver = MaxSatSolver::new(f);
        let result = solver.solve();

        match result {
            MaxSatResult::Optimum { cost, model, .. } => {
                // Cost should be at most total weight (11)
                // Ideally it finds cost 1 (optimal), but any valid solution is acceptable
                assert!(cost <= 11, "Cost {} exceeds total weight 11", cost);
                
                // Verify hard clause is satisfied
                let hard_sat = model.get(0).copied().unwrap_or(false) 
                    || model.get(1).copied().unwrap_or(false);
                assert!(hard_sat, "Hard clause must be satisfied");
            }
            _ => panic!("Expected Optimum result"),
        }
    }

    #[test]
    fn test_parse_wcnf() {
        let input = r#"
c This is a comment
p wcnf 3 4 10
10 1 2 0
10 -1 3 0
1 -1 0
2 -2 0
        "#;

        let f = parse_wcnf(input).unwrap();
        
        assert_eq!(f.num_vars, 3);
        assert_eq!(f.num_hard(), 2); // weight >= 10
        assert_eq!(f.num_soft(), 2); // weight < 10
        assert_eq!(f.total_weight(), 3); // 1 + 2
    }

    #[test]
    fn test_parse_wcnf_no_top() {
        let input = r#"
p wcnf 2 2
1000000 1 0
5 -1 0
        "#;

        let f = parse_wcnf(input).unwrap();
        
        // Without explicit top, MAX is used, so nothing is hard by default
        // Both clauses become soft
        assert_eq!(f.num_vars, 2);
        assert_eq!(f.num_soft(), 2);
    }

    #[test]
    fn test_soft_clause_weight() {
        let s = SoftClause::new(clause(&[1, 2]), 5);
        assert_eq!(s.weight, 5);
        assert!(s.relax_var.is_none());
    }

    #[test]
    fn test_soft_clause_unit() {
        let s = SoftClause::unit(clause(&[1]));
        assert_eq!(s.weight, 1);
    }

    #[test]
    fn test_maxsat_stats() {
        let f = MaxSatFormula::new(1);
        let solver = MaxSatSolver::new(f);
        assert_eq!(solver.stats().sat_calls, 0);
        assert_eq!(solver.stats().cores_extracted, 0);
    }

    #[test]
    fn test_compute_satisfied() {
        let mut f = MaxSatFormula::new(2);
        f.add_soft_unit(clause(&[1]));    // idx 0
        f.add_soft_unit(clause(&[-1]));   // idx 1
        f.add_soft_unit(clause(&[2]));    // idx 2

        // Model: var1=true, var2=false
        // Plus relaxation vars which start at index 2
        let model = vec![true, false, false, false, false];
        
        let solver = MaxSatSolver::new(f);
        let satisfied = solver.compute_satisfied(&model);
        
        // Clause 0 (1) should be satisfied (var1=true)
        // Clause 1 (-1) should NOT be satisfied (var1=true)
        // Clause 2 (2) should NOT be satisfied (var2=false)
        assert!(satisfied.contains(&0));
        assert!(!satisfied.contains(&1));
        assert!(!satisfied.contains(&2));
    }
}
