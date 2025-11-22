// SPDX-FileCopyrightText: 2025 ECHIDNA Project Contributors
// SPDX-License-Identifier: MIT OR Palimpsest-0.6

//! Actor-based Multi-Agent Orchestration
//!
//! Uses Actix to enable parallel proof search across multiple provers.

use actix::prelude::*;
use anyhow::Result;
use std::time::{Duration, Instant};
use tracing::{debug, info, warn};

use crate::core::{Goal, ProofState};
use crate::provers::{ProverBackend, ProverKind};
use super::{AgenticGoal, GoalResult};

/// Message types for actor communication
#[derive(Message)]
#[rtype(result = "Result<ProofState>")]
pub struct ProveGoal {
    pub goal: Goal,
    pub timeout_ms: u64,
}

#[derive::(Message)]
#[rtype(result = "Vec<String>")]
pub struct GetRelatedConcepts {
    pub theorem_text: String,
}

#[derive(Message)]
#[rtype(result = "Result<Vec<String>>")]
pub struct GenerateLemmas {
    pub goal: Goal,
    pub max_lemmas: usize,
}

#[derive(Message)]
#[rtype(result = "()")]
pub struct RecordSuccess {
    pub goal_id: String,
    pub prover: ProverKind,
    pub time_ms: u64,
}

#[derive(Message)]
#[rtype(result = "()")]
pub struct RecordFailure {
    pub goal_id: String,
    pub prover: ProverKind,
    pub reason: String,
}

/// Prover agent - wraps a single prover backend
pub struct ProverAgent {
    kind: ProverKind,
    backend: Box<dyn ProverBackend>,
}

impl ProverAgent {
    pub fn new(kind: ProverKind, backend: Box<dyn ProverBackend>) -> Self {
        ProverAgent { kind, backend }
    }

    /// Start the actor
    pub fn start_actor(kind: ProverKind, backend: Box<dyn ProverBackend>) -> Addr<Self> {
        SyncArbiter::start(1, move || {
            ProverAgent::new(kind.clone(), backend.clone())
        })
    }
}

impl Actor for ProverAgent {
    type Context = SyncContext<Self>;

    fn started(&mut self, _ctx: &mut Self::Context) {
        info!("ProverAgent started: {:?}", self.kind);
    }
}

impl Handler<ProveGoal> for ProverAgent {
    type Result = Result<ProofState>;

    fn handle(&mut self, msg: ProveGoal, _ctx: &mut Self::Context) -> Self::Result {
        debug!("ProverAgent {:?} attempting goal: {}", self.kind, msg.goal.id);

        let start = Instant::now();

        // Attempt proof with timeout
        let result = self.backend.prove(&msg.goal);

        let elapsed = start.elapsed().as_millis() as u64;

        match result {
            Ok(proof) => {
                info!("ProverAgent {:?} succeeded in {}ms", self.kind, elapsed);
                Ok(proof)
            }
            Err(e) => {
                debug!("ProverAgent {:?} failed: {}", self.kind, e);
                Err(e)
            }
        }
    }
}

/// Context agent - queries ConceptNet for related concepts
pub struct ContextAgent {
    #[cfg(feature = "conceptnet")]
    client: crate::integrations::ConceptNetClient,
}

impl ContextAgent {
    pub fn new() -> Self {
        ContextAgent {
            #[cfg(feature = "conceptnet")]
            client: crate::integrations::ConceptNetClient::new(),
        }
    }

    pub fn start_actor() -> Addr<Self> {
        SyncArbiter::start(1, || ContextAgent::new())
    }
}

impl Default for ContextAgent {
    fn default() -> Self {
        Self::new()
    }
}

impl Actor for ContextAgent {
    type Context = SyncContext<Self>;

    fn started(&mut self, _ctx: &mut Self::Context) {
        info!("ContextAgent started");
    }
}

impl Handler<GetRelatedConcepts> for ContextAgent {
    type Result = Vec<String>;

    fn handle(&mut self, msg: GetRelatedConcepts, _ctx: &mut Self::Context) -> Self::Result {
        #[cfg(feature = "conceptnet")]
        {
            use actix::AsyncContext;

            debug!("ContextAgent querying ConceptNet for: {}", msg.theorem_text);

            // This should be async, but for simplicity we'll make it sync
            // In production, use actix-web's client for proper async handling
            let runtime = tokio::runtime::Runtime::new().unwrap();
            match runtime.block_on(self.client.augment_theorem(&msg.theorem_text)) {
                Ok(concepts) => {
                    info!("ContextAgent found {} related concepts", concepts.len());
                    concepts
                }
                Err(e) => {
                    warn!("ContextAgent failed to query ConceptNet: {}", e);
                    Vec::new()
                }
            }
        }

        #[cfg(not(feature = "conceptnet"))]
        {
            debug!("ConceptNet not enabled, returning empty results");
            Vec::new()
        }
    }
}

/// Lemma agent - generates auxiliary lemmas
pub struct LemmaAgent;

impl LemmaAgent {
    pub fn new() -> Self {
        LemmaAgent
    }

    pub fn start_actor() -> Addr<Self> {
        SyncArbiter::start(1, || LemmaAgent::new())
    }
}

impl Default for LemmaAgent {
    fn default() -> Self {
        Self::new()
    }
}

impl Actor for LemmaAgent {
    type Context = SyncContext<Self>;

    fn started(&mut self, _ctx: &mut Self::Context) {
        info!("LemmaAgent started");
    }
}

impl Handler<GenerateLemmas> for LemmaAgent {
    type Result = Result<Vec<String>>;

    fn handle(&mut self, msg: GenerateLemmas, _ctx: &mut Self::Context) -> Self::Result {
        debug!("LemmaAgent generating lemmas for goal: {}", msg.goal.id);

        // TODO: Implement lemma generation using:
        // - Pattern matching on goal structure
        // - ConceptNet queries for related concepts
        // - Template-based generation

        // For now, return empty list
        Ok(Vec::new())
    }
}

/// Coordinator agent - orchestrates multiple provers in parallel
pub struct CoordinatorAgent {
    prover_agents: Vec<(ProverKind, Addr<ProverAgent>)>,
    context_agent: Addr<ContextAgent>,
    lemma_agent: Addr<LemmaAgent>,
}

impl CoordinatorAgent {
    pub fn new(
        prover_agents: Vec<(ProverKind, Addr<ProverAgent>)>,
        context_agent: Addr<ContextAgent>,
        lemma_agent: Addr<LemmaAgent>,
    ) -> Self {
        CoordinatorAgent {
            prover_agents,
            context_agent,
            lemma_agent,
        }
    }

    pub fn start_actor(
        prover_agents: Vec<(ProverKind, Addr<ProverAgent>)>,
        context_agent: Addr<ContextAgent>,
        lemma_agent: Addr<LemmaAgent>,
    ) -> Addr<Self> {
        CoordinatorAgent::create(|_ctx| {
            CoordinatorAgent::new(prover_agents, context_agent, lemma_agent)
        })
    }
}

impl Actor for CoordinatorAgent {
    type Context = Context<Self>;

    fn started(&mut self, _ctx: &mut Self::Context) {
        info!("CoordinatorAgent started with {} prover agents", self.prover_agents.len());
    }
}

/// Message to coordinate parallel proof search
#[derive(Message)]
#[rtype(result = "Result<(ProofState, ProverKind)>")]
pub struct CoordinateProof {
    pub goal: AgenticGoal,
    pub timeout_ms: u64,
    pub parallel: bool,
}

impl Handler<CoordinateProof> for CoordinatorAgent {
    type Result = ResponseActFuture<Self, Result<(ProofState, ProverKind)>>;

    fn handle(&mut self, msg: CoordinateProof, _ctx: &mut Self::Context) -> Self::Result {
        info!("CoordinatorAgent orchestrating proof for goal: {}", msg.goal.goal.id);

        // Query ConceptNet for related concepts (optional enrichment)
        let context_fut = self.context_agent
            .send(GetRelatedConcepts {
                theorem_text: format!("{:?}", msg.goal.goal.target),
            })
            .into_actor(self);

        // Query lemma generator for auxiliary lemmas
        let lemma_fut = self.lemma_agent
            .send(GenerateLemmas {
                goal: msg.goal.goal.clone(),
                max_lemmas: 5,
            })
            .into_actor(self);

        if msg.parallel {
            // Parallel mode: send to all provers simultaneously
            let futures: Vec<_> = self.prover_agents
                .iter()
                .map(|(kind, addr)| {
                    let prove_msg = ProveGoal {
                        goal: msg.goal.goal.clone(),
                        timeout_ms: msg.timeout_ms,
                    };
                    (*kind, addr.send(prove_msg))
                })
                .collect();

            // Wait for first success
            Box::pin(
                context_fut
                    .then(move |_concepts, _act, _ctx| lemma_fut)
                    .then(move |_lemmas, _act, _ctx| {
                        // Race all prover futures
                        async move {
                            for (kind, fut) in futures {
                                match fut.await {
                                    Ok(Ok(proof)) => {
                                        return Ok((proof, kind));
                                    }
                                    Ok(Err(_)) => continue,
                                    Err(_) => continue,
                                }
                            }
                            Err(anyhow::anyhow!("All provers failed"))
                        }
                        .into_actor(_act)
                    })
            )
        } else {
            // Sequential mode: try preferred prover first, then others
            let preferred = msg.goal.preferred_prover.unwrap_or(ProverKind::Z3);

            let prover_addr = self.prover_agents
                .iter()
                .find(|(k, _)| *k == preferred)
                .map(|(_, addr)| addr.clone());

            if let Some(addr) = prover_addr {
                let prove_msg = ProveGoal {
                    goal: msg.goal.goal.clone(),
                    timeout_ms: msg.timeout_ms,
                };

                Box::pin(
                    context_fut
                        .then(move |_concepts, _act, _ctx| lemma_fut)
                        .then(move |_lemmas, _act, _ctx| {
                            addr.send(prove_msg).into_actor(_act)
                        })
                        .then(move |result, _act, _ctx| {
                            async move {
                                match result {
                                    Ok(Ok(proof)) => Ok((proof, preferred)),
                                    _ => Err(anyhow::anyhow!("Prover failed")),
                                }
                            }
                            .into_actor(_act)
                        })
                )
            } else {
                Box::pin(async move { Err(anyhow::anyhow!("No prover available")) }.into_actor(self))
            }
        }
    }
}

/// Multi-agent system manager
pub struct MultiAgentSystem {
    coordinator: Addr<CoordinatorAgent>,
}

impl MultiAgentSystem {
    /// Initialize the multi-agent system
    pub fn new(provers: Vec<(ProverKind, Box<dyn ProverBackend>)>) -> Self {
        // Start prover agents
        let prover_agents: Vec<_> = provers
            .into_iter()
            .map(|(kind, backend)| {
                let addr = ProverAgent::start_actor(kind, backend);
                (kind, addr)
            })
            .collect();

        // Start context agent
        let context_agent = ContextAgent::start_actor();

        // Start lemma agent
        let lemma_agent = LemmaAgent::start_actor();

        // Start coordinator
        let coordinator = CoordinatorAgent::start_actor(
            prover_agents,
            context_agent,
            lemma_agent,
        );

        MultiAgentSystem { coordinator }
    }

    /// Submit a goal to the multi-agent system
    pub async fn prove(&self, goal: AgenticGoal, parallel: bool) -> Result<(ProofState, ProverKind)> {
        self.coordinator
            .send(CoordinateProof {
                goal,
                timeout_ms: 30000, // 30 second timeout
                parallel,
            })
            .await
            .map_err(|e| anyhow::anyhow!("Coordinator mailbox error: {}", e))?
    }

    /// Get coordinator address for advanced usage
    pub fn coordinator(&self) -> &Addr<CoordinatorAgent> {
        &self.coordinator
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[actix::test]
    async fn test_context_agent() {
        let context_agent = ContextAgent::start_actor();

        let result = context_agent
            .send(GetRelatedConcepts {
                theorem_text: "group theory identity element".to_string(),
            })
            .await;

        assert!(result.is_ok());
    }

    #[actix::test]
    async fn test_lemma_agent() {
        let lemma_agent = LemmaAgent::start_actor();

        let goal = Goal {
            id: "test".to_string(),
            target: crate::core::Term::Var("test".to_string()),
            hypotheses: vec![],
        };

        let result = lemma_agent
            .send(GenerateLemmas {
                goal,
                max_lemmas: 5,
            })
            .await;

        assert!(result.is_ok());
    }
}
