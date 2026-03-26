//! Restart strategies for CDCL.
//!
//! Restarts help escape bad search regions. Several strategies:
//! - Luby sequence: theoretically optimal for randomized algorithms
//! - Geometric: simple exponential growth
//! - Glucose-style: based on recent LBD quality

/// Restart strategy configuration.
#[derive(Debug, Clone)]
pub enum RestartStrategy {
    /// Luby sequence with unit multiplier.
    Luby { unit: u64 },
    /// Geometric growth: interval *= factor each restart.
    Geometric { initial: u64, factor: f64, max: u64 },
    /// Glucose-style: restart when recent LBD is poor.
    Glucose { margin: f64, window: usize },
    /// No restarts.
    None,
}

impl Default for RestartStrategy {
    fn default() -> Self {
        RestartStrategy::Luby { unit: 100 }
    }
}

/// Manages restart decisions.
#[derive(Debug)]
pub struct RestartScheduler {
    strategy: RestartStrategy,
    /// Number of restarts performed.
    restarts: u64,
    /// Conflicts since last restart.
    conflicts_since_restart: u64,
    /// Current restart threshold.
    current_threshold: u64,
    /// Recent LBD values (for Glucose).
    recent_lbds: Vec<u32>,
    /// Global average LBD.
    global_lbd_sum: f64,
    /// Global LBD count.
    global_lbd_count: u64,
}

impl RestartScheduler {
    /// Create a new scheduler with the given strategy.
    pub fn new(strategy: RestartStrategy) -> Self {
        let initial_threshold = match &strategy {
            RestartStrategy::Luby { unit } => *unit,
            RestartStrategy::Geometric { initial, .. } => *initial,
            RestartStrategy::Glucose { .. } => 50, // Check every 50 conflicts
            RestartStrategy::None => u64::MAX,
        };
        
        RestartScheduler {
            strategy,
            restarts: 0,
            conflicts_since_restart: 0,
            current_threshold: initial_threshold,
            recent_lbds: Vec::new(),
            global_lbd_sum: 0.0,
            global_lbd_count: 0,
        }
    }

    /// Record a conflict (for conflict counting and LBD tracking).
    pub fn record_conflict(&mut self, lbd: u32) {
        self.conflicts_since_restart += 1;
        
        // Track LBD for Glucose strategy
        if let RestartStrategy::Glucose { window, .. } = &self.strategy {
            self.recent_lbds.push(lbd);
            if self.recent_lbds.len() > *window {
                self.recent_lbds.remove(0);
            }
        }
        
        self.global_lbd_sum += lbd as f64;
        self.global_lbd_count += 1;
    }

    /// Check if we should restart.
    pub fn should_restart(&self) -> bool {
        match &self.strategy {
            RestartStrategy::None => false,
            RestartStrategy::Luby { .. } | RestartStrategy::Geometric { .. } => {
                self.conflicts_since_restart >= self.current_threshold
            }
            RestartStrategy::Glucose { margin, window } => {
                if self.recent_lbds.len() < *window {
                    return false;
                }
                
                let global_avg = if self.global_lbd_count == 0 {
                    return false;
                } else {
                    self.global_lbd_sum / self.global_lbd_count as f64
                };
                
                let recent_avg: f64 = self.recent_lbds.iter()
                    .map(|&x| x as f64)
                    .sum::<f64>() / self.recent_lbds.len() as f64;
                
                // Restart if recent LBDs are worse than global average
                recent_avg > global_avg * margin
            }
        }
    }

    /// Notify that a restart was performed.
    pub fn on_restart(&mut self) {
        self.restarts += 1;
        self.conflicts_since_restart = 0;
        
        // Update threshold for next restart
        match &self.strategy {
            RestartStrategy::Luby { unit } => {
                self.current_threshold = luby_sequence(self.restarts + 1) * unit;
            }
            RestartStrategy::Geometric { factor, max, .. } => {
                let new = (self.current_threshold as f64 * factor) as u64;
                self.current_threshold = new.min(*max);
            }
            RestartStrategy::Glucose { .. } => {
                // Clear recent LBDs
                self.recent_lbds.clear();
            }
            RestartStrategy::None => {}
        }
    }

    /// Get number of restarts performed.
    pub fn num_restarts(&self) -> u64 {
        self.restarts
    }

    /// Get conflicts since last restart.
    pub fn conflicts_since_restart(&self) -> u64 {
        self.conflicts_since_restart
    }
}

/// Compute the Luby sequence value at position n (1-indexed).
///
/// The Luby sequence is: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
/// It has the property that it's optimal for Las Vegas algorithms.
pub fn luby_sequence(mut n: u64) -> u64 {
    // Find the largest k such that 2^k - 1 < n
    let mut k = 1u64;
    while (1u64 << k) - 1 < n {
        k += 1;
    }
    
    // Check if n is exactly 2^k - 1
    if (1u64 << k) - 1 == n {
        return 1u64 << (k - 1);
    }
    
    // Otherwise, recurse into the sequence
    n -= (1u64 << (k - 1)) - 1;
    luby_sequence(n)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_luby_sequence() {
        // First 15 values: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8
        let expected = [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8];
        for (i, &exp) in expected.iter().enumerate() {
            assert_eq!(luby_sequence(i as u64 + 1), exp, "Luby({}) failed", i + 1);
        }
    }

    #[test]
    fn test_luby_scheduler() {
        let mut sched = RestartScheduler::new(RestartStrategy::Luby { unit: 10 });
        
        // First restart at 10 conflicts (1 * 10)
        for _ in 0..9 {
            sched.record_conflict(2);
            assert!(!sched.should_restart());
        }
        sched.record_conflict(2);
        assert!(sched.should_restart());
        
        sched.on_restart();
        
        // Second restart at 10 more conflicts (1 * 10)
        for _ in 0..9 {
            sched.record_conflict(2);
            assert!(!sched.should_restart());
        }
        sched.record_conflict(2);
        assert!(sched.should_restart());
        
        sched.on_restart();
        
        // Third restart at 20 conflicts (2 * 10)
        for _ in 0..19 {
            sched.record_conflict(2);
            assert!(!sched.should_restart());
        }
        sched.record_conflict(2);
        assert!(sched.should_restart());
    }

    #[test]
    fn test_geometric_scheduler() {
        let mut sched = RestartScheduler::new(RestartStrategy::Geometric {
            initial: 100,
            factor: 1.5,
            max: 10000,
        });
        
        // First restart at 100
        assert_eq!(sched.current_threshold, 100);
        
        for _ in 0..100 {
            sched.record_conflict(2);
        }
        assert!(sched.should_restart());
        
        sched.on_restart();
        
        // Second threshold is 150
        assert_eq!(sched.current_threshold, 150);
    }

    #[test]
    fn test_geometric_max() {
        let mut sched = RestartScheduler::new(RestartStrategy::Geometric {
            initial: 100,
            factor: 10.0,
            max: 500,
        });
        
        for _ in 0..100 {
            sched.record_conflict(2);
        }
        sched.on_restart();
        
        // Should be capped at 500, not 1000
        assert_eq!(sched.current_threshold, 500);
    }

    #[test]
    fn test_glucose_scheduler() {
        let mut sched = RestartScheduler::new(RestartStrategy::Glucose {
            margin: 1.2,
            window: 50,
        });
        
        // Build up global average with good LBDs
        for _ in 0..100 {
            sched.record_conflict(3);
        }
        
        // Recent window has average 3.0, global is 3.0, no restart
        assert!(!sched.should_restart());
        
        // Now add bad LBDs
        for _ in 0..50 {
            sched.record_conflict(10);
        }
        
        // Recent avg is ~10, global is ~5, should restart
        // 10 > 5 * 1.2 = 6, so yes
        assert!(sched.should_restart());
    }

    #[test]
    fn test_no_restart_strategy() {
        let mut sched = RestartScheduler::new(RestartStrategy::None);
        
        for _ in 0..10000 {
            sched.record_conflict(5);
        }
        
        assert!(!sched.should_restart());
    }

    #[test]
    fn test_restart_count() {
        let mut sched = RestartScheduler::new(RestartStrategy::Luby { unit: 10 });
        
        assert_eq!(sched.num_restarts(), 0);
        
        for _ in 0..10 {
            sched.record_conflict(2);
        }
        sched.on_restart();
        
        assert_eq!(sched.num_restarts(), 1);
    }
}
