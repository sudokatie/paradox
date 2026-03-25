//! Restart strategies for CDCL solvers
//!
//! Restarts help escape from unproductive parts of the search space.
//! Common strategies include:
//! - Luby sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
//! - Geometric: base * factor^n
//! - Glucose-style: based on recent LBD quality

/// Restart strategy configuration
#[derive(Debug, Clone)]
pub enum RestartStrategy {
    /// Luby sequence restarts with base unit
    Luby { base_conflicts: u64 },
    /// Geometric restarts
    Geometric { initial: u64, factor: f64 },
    /// Glucose-style dynamic restarts based on LBD
    Glucose { 
        /// Window size for LBD averaging
        window_size: usize,
        /// Threshold multiplier (restart if recent > threshold * global)
        threshold: f64,
    },
    /// No restarts
    Never,
}

impl Default for RestartStrategy {
    fn default() -> Self {
        RestartStrategy::Luby { base_conflicts: 100 }
    }
}

/// Restart scheduler
#[derive(Debug)]
pub struct RestartScheduler {
    /// Current strategy
    strategy: RestartStrategy,
    /// Number of conflicts since last restart
    conflicts_since_restart: u64,
    /// Total number of restarts
    restart_count: u64,
    /// Current restart threshold (conflicts until next restart)
    current_threshold: u64,
    /// Luby sequence index
    luby_index: u64,
    /// Recent LBD values for Glucose strategy
    recent_lbds: Vec<u32>,
    /// Global average LBD
    global_lbd_sum: u64,
    /// Global LBD count
    global_lbd_count: u64,
}

impl RestartScheduler {
    /// Create a new restart scheduler with the given strategy
    pub fn new(strategy: RestartStrategy) -> Self {
        let current_threshold = match &strategy {
            RestartStrategy::Luby { base_conflicts } => *base_conflicts,
            RestartStrategy::Geometric { initial, .. } => *initial,
            RestartStrategy::Glucose { .. } => 50, // Check every 50 conflicts
            RestartStrategy::Never => u64::MAX,
        };
        
        RestartScheduler {
            strategy,
            conflicts_since_restart: 0,
            restart_count: 0,
            current_threshold,
            luby_index: 1,
            recent_lbds: Vec::new(),
            global_lbd_sum: 0,
            global_lbd_count: 0,
        }
    }

    /// Record a conflict (and optionally its LBD for Glucose strategy)
    pub fn record_conflict(&mut self, lbd: Option<u32>) {
        self.conflicts_since_restart += 1;
        
        if let Some(lbd_val) = lbd {
            // Update global LBD stats
            self.global_lbd_sum += lbd_val as u64;
            self.global_lbd_count += 1;
            
            // Update recent LBD window for Glucose
            if let RestartStrategy::Glucose { window_size, .. } = &self.strategy {
                self.recent_lbds.push(lbd_val);
                while self.recent_lbds.len() > *window_size {
                    self.recent_lbds.remove(0);
                }
            }
        }
    }

    /// Check if we should restart
    pub fn should_restart(&self) -> bool {
        match &self.strategy {
            RestartStrategy::Luby { .. } | RestartStrategy::Geometric { .. } => {
                self.conflicts_since_restart >= self.current_threshold
            }
            RestartStrategy::Glucose { window_size, threshold } => {
                if self.recent_lbds.len() < *window_size || self.global_lbd_count == 0 {
                    return false;
                }
                
                let recent_avg: f64 = self.recent_lbds.iter()
                    .map(|&x| x as f64)
                    .sum::<f64>() / self.recent_lbds.len() as f64;
                let global_avg = self.global_lbd_sum as f64 / self.global_lbd_count as f64;
                
                recent_avg > threshold * global_avg
            }
            RestartStrategy::Never => false,
        }
    }

    /// Execute a restart (update internal state)
    pub fn restart(&mut self) {
        self.restart_count += 1;
        self.conflicts_since_restart = 0;
        
        match &self.strategy {
            RestartStrategy::Luby { base_conflicts } => {
                self.luby_index += 1;
                self.current_threshold = luby_value(self.luby_index) * base_conflicts;
            }
            RestartStrategy::Geometric { factor, .. } => {
                self.current_threshold = (self.current_threshold as f64 * factor) as u64;
            }
            RestartStrategy::Glucose { .. } => {
                self.recent_lbds.clear();
            }
            RestartStrategy::Never => {}
        }
    }

    /// Get the number of restarts
    pub fn restart_count(&self) -> u64 {
        self.restart_count
    }

    /// Get conflicts since last restart
    pub fn conflicts_since_restart(&self) -> u64 {
        self.conflicts_since_restart
    }

    /// Get the current threshold
    pub fn current_threshold(&self) -> u64 {
        self.current_threshold
    }
}

/// Compute the i-th value of the Luby sequence (1-indexed)
/// Luby sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
pub fn luby_value(i: u64) -> u64 {
    // Find k such that 2^k - 1 < i <= 2^(k+1) - 1
    let mut k = 0u32;
    let mut pow = 1u64;
    while pow < i + 1 {
        k += 1;
        pow *= 2;
    }
    
    // pow = 2^k
    // If i == 2^k - 1, return 2^(k-1)
    if i == pow - 1 {
        return pow / 2;
    }
    
    // Otherwise, recurse: luby(i - 2^(k-1) + 1)
    luby_value(i - pow / 2 + 1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_luby_sequence() {
        // Luby sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
        let expected = [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8];
        for (i, &val) in expected.iter().enumerate() {
            assert_eq!(luby_value((i + 1) as u64), val, "luby({}) should be {}", i + 1, val);
        }
    }

    #[test]
    fn test_luby_scheduler() {
        let mut scheduler = RestartScheduler::new(RestartStrategy::Luby { base_conflicts: 10 });
        
        // First restart at 10 conflicts (luby(1) = 1)
        assert_eq!(scheduler.current_threshold(), 10);
        
        for _ in 0..9 {
            scheduler.record_conflict(None);
            assert!(!scheduler.should_restart());
        }
        scheduler.record_conflict(None);
        assert!(scheduler.should_restart());
        
        scheduler.restart();
        assert_eq!(scheduler.restart_count(), 1);
        
        // Second restart also at 10 (luby(2) = 1)
        assert_eq!(scheduler.current_threshold(), 10);
        
        for _ in 0..10 {
            scheduler.record_conflict(None);
        }
        scheduler.restart();
        assert_eq!(scheduler.restart_count(), 2);
        
        // Third restart at 20 (luby(3) = 2)
        assert_eq!(scheduler.current_threshold(), 20);
    }

    #[test]
    fn test_geometric_scheduler() {
        let mut scheduler = RestartScheduler::new(RestartStrategy::Geometric { 
            initial: 100, 
            factor: 1.5 
        });
        
        assert_eq!(scheduler.current_threshold(), 100);
        
        for _ in 0..100 {
            scheduler.record_conflict(None);
        }
        assert!(scheduler.should_restart());
        scheduler.restart();
        
        // Next threshold: 100 * 1.5 = 150
        assert_eq!(scheduler.current_threshold(), 150);
        
        for _ in 0..150 {
            scheduler.record_conflict(None);
        }
        scheduler.restart();
        
        // Next threshold: 150 * 1.5 = 225
        assert_eq!(scheduler.current_threshold(), 225);
    }

    #[test]
    fn test_glucose_scheduler() {
        let mut scheduler = RestartScheduler::new(RestartStrategy::Glucose { 
            window_size: 5,
            threshold: 1.5,
        });
        
        // Need to fill the window first
        for _ in 0..5 {
            scheduler.record_conflict(Some(3)); // LBD = 3
            assert!(!scheduler.should_restart());
        }
        
        // Global average = 3, recent average = 3
        // Threshold: recent > 1.5 * global => 3 > 4.5 => false
        assert!(!scheduler.should_restart());
        
        // Add some high LBD conflicts
        for _ in 0..5 {
            scheduler.record_conflict(Some(10)); // LBD = 10
        }
        
        // Recent average ~ 10, global average ~ 6.5
        // Threshold: 10 > 1.5 * 6.5 = 9.75 => true
        assert!(scheduler.should_restart());
        
        scheduler.restart();
        // After restart, recent LBDs should be cleared
        assert!(!scheduler.should_restart());
    }

    #[test]
    fn test_never_restart() {
        let mut scheduler = RestartScheduler::new(RestartStrategy::Never);
        
        for _ in 0..1000 {
            scheduler.record_conflict(Some(5));
            assert!(!scheduler.should_restart());
        }
    }

    #[test]
    fn test_restart_count() {
        let mut scheduler = RestartScheduler::new(RestartStrategy::Luby { base_conflicts: 1 });
        
        assert_eq!(scheduler.restart_count(), 0);
        
        scheduler.record_conflict(None);
        scheduler.restart();
        assert_eq!(scheduler.restart_count(), 1);
        
        scheduler.record_conflict(None);
        scheduler.restart();
        assert_eq!(scheduler.restart_count(), 2);
    }

    #[test]
    fn test_conflicts_since_restart() {
        let mut scheduler = RestartScheduler::new(RestartStrategy::Luby { base_conflicts: 100 });
        
        assert_eq!(scheduler.conflicts_since_restart(), 0);
        
        for i in 1..=50 {
            scheduler.record_conflict(None);
            assert_eq!(scheduler.conflicts_since_restart(), i);
        }
        
        // Simulate manual restart
        scheduler.restart();
        assert_eq!(scheduler.conflicts_since_restart(), 0);
    }

    #[test]
    fn test_default_strategy() {
        let strategy = RestartStrategy::default();
        match strategy {
            RestartStrategy::Luby { base_conflicts: 100 } => {}
            _ => panic!("Expected default to be Luby with base_conflicts=100"),
        }
    }
}
