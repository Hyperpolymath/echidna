// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! ECHIDNA: Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance
//!
//! A neurosymbolic theorem proving platform supporting 12 theorem provers
//! with aspect tagging, OpenCyc integration, and neural premise selection.

pub mod core;
pub mod provers;
pub mod parsers;
pub mod neural;
pub mod aspect;
pub mod agent;

pub use core::{ProofState, Term, Tactic, TacticResult};
pub use provers::{ProverBackend, ProverKind, ProverConfig};
pub use agent::{AgentCore, AgentConfig};

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
