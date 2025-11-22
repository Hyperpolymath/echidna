// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Neural premise selection and tactic suggestion (stub)

use crate::core::Tactic;

pub struct NeuralSuggester;

impl NeuralSuggester {
    pub fn new() -> Self {
        NeuralSuggester
    }

    pub async fn suggest_tactics(&self, _context: &str) -> Vec<Tactic> {
        Vec::new()
    }
}
