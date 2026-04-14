//! DRAT proof verification
//!
//! Verifies unsatisfiability proofs in DRAT format.
//! DRAT = Deletion Resolution Asymmetric Tautology

mod checker;

pub use checker::{DratVerifier, VerifyResult, VerifyError};
