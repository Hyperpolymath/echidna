// SPDX-FileCopyrightText: 2025 ECHIDNA Project Contributors
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! ConceptNet Integration - Common-sense knowledge augmentation
//!
//! ConceptNet is a lightweight alternative to OpenCyc for semantic knowledge.
//! REST API: http://api.conceptnet.io/

use anyhow::Result;
use reqwest::Client;
use serde::{Deserialize, Serialize};
use tracing::{debug, info};

const CONCEPTNET_API_BASE: &str = "http://api.conceptnet.io";

/// A ConceptNet edge (relationship between concepts)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConceptNetEdge {
    #[serde(rename = "@id")]
    pub id: String,

    pub rel: ConceptNetRelation,
    pub start: ConceptNetNode,
    pub end: ConceptNetNode,
    pub weight: f64,
}

/// A ConceptNet relation type
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConceptNetRelation {
    #[serde(rename = "@id")]
    pub id: String,

    pub label: String,
}

/// A ConceptNet node (concept)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConceptNetNode {
    #[serde(rename = "@id")]
    pub id: String,

    pub label: String,

    #[serde(default)]
    pub language: Option<String>,
}

/// ConceptNet API response
#[derive(Debug, Clone, Serialize, Deserialize)]
struct ConceptNetResponse {
    edges: Vec<ConceptNetEdge>,
}

/// ConceptNet client
pub struct ConceptNetClient {
    client: Client,
    base_url: String,
}

impl ConceptNetClient {
    /// Create a new ConceptNet client
    pub fn new() -> Self {
        ConceptNetClient {
            client: Client::new(),
            base_url: CONCEPTNET_API_BASE.to_string(),
        }
    }

    /// Query related concepts
    pub async fn related_concepts(&self, concept: &str) -> Result<Vec<ConceptNetEdge>> {
        let url = format!("{}/query?node=/c/en/{}&limit=20", self.base_url, concept);

        debug!("Querying ConceptNet: {}", url);

        let response = self.client.get(&url)
            .send()
            .await?
            .json::<ConceptNetResponse>()
            .await?;

        info!("Found {} related concepts for '{}'", response.edges.len(), concept);

        Ok(response.edges)
    }

    /// Find concepts related by a specific relation
    pub async fn related_by(&self, concept: &str, relation: &str) -> Result<Vec<ConceptNetEdge>> {
        let url = format!("{}/query?node=/c/en/{}&rel=/r/{}&limit=20",
                         self.base_url, concept, relation);

        debug!("Querying ConceptNet with relation: {}", url);

        let response = self.client.get(&url)
            .send()
            .await?
            .json::<ConceptNetResponse>()
            .await?;

        info!("Found {} concepts related to '{}' by '{}'",
              response.edges.len(), concept, relation);

        Ok(response.edges)
    }

    /// Extract relevant concepts for theorem proving
    pub async fn augment_theorem(&self, theorem_text: &str) -> Result<Vec<String>> {
        // Extract key terms from theorem
        let terms = self.extract_terms(theorem_text);

        let mut related = Vec::new();

        for term in terms {
            // Get related concepts
            let edges = self.related_concepts(&term).await?;

            for edge in edges {
                // Extract concept labels
                related.push(edge.end.label.clone());
            }
        }

        // Deduplicate
        related.sort();
        related.dedup();

        Ok(related)
    }

    /// Simple term extraction (split on whitespace and filter)
    fn extract_terms(&self, text: &str) -> Vec<String> {
        text.split_whitespace()
            .filter(|w| w.len() > 3) // Skip short words
            .map(|w| w.trim_matches(|c: char| !c.is_alphanumeric()))
            .filter(|w| !w.is_empty())
            .map(|w| w.to_lowercase())
            .collect()
    }
}

impl Default for ConceptNetClient {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    #[ignore] // Requires network access
    async fn test_conceptnet_query() {
        let client = ConceptNetClient::new();
        let results = client.related_concepts("group").await.unwrap();
        assert!(!results.is_empty());
    }

    #[test]
    fn test_term_extraction() {
        let client = ConceptNetClient::new();
        let terms = client.extract_terms("Prove that every group has an identity element");
        assert!(terms.contains(&"group".to_string()));
        assert!(terms.contains(&"identity".to_string()));
        assert!(terms.contains(&"element".to_string()));
    }
}
