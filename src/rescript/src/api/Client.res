// SPDX-License-Identifier: MIT OR Palimpsest-0.6
// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team

/**
 * API client for ECHIDNA Rust backend
 * Handles all communication with the proof backend
 */

open Store

// API configuration
let apiBase = "/api"

// Response types
type apiResponse<'a> = {
  data: option<'a>,
  error: option<string>,
}

// JSON encoding/decoding helpers
module Decode = {
  let goal = (json): goal => {
    open JSON.Decode
    {
      id: field("id", string, json),
      hypotheses: field("hypotheses", array(string), json),
      conclusion: field("conclusion", string, json),
      context: field("context", array(string), json),
    }
  }

  let tacticSuggestion = (json): tacticSuggestion => {
    open JSON.Decode
    {
      tactic: field("tactic", string, json),
      confidence: field("confidence", float, json),
      premise: optional(field("premise", string), json),
      aspectTags: field("aspect_tags", array(string), json),
    }
  }

  let proofState = (json): proofState => {
    open JSON.Decode
    {
      goals: field("goals", array(goal), json),
      currentGoalIndex: field("current_goal_index", int, json),
      proofScript: field("proof_script", array(string), json),
      completed: field("completed", bool, json),
    }
  }

  let aspectTag = (json): aspectTag => {
    open JSON.Decode
    {
      name: field("name", string, json),
      category: field("category", string, json),
      active: field("active", bool, json),
    }
  }
}

module Encode = {
  let prover = (prover: prover): JSON.t => {
    proverToString(prover)->JSON.String
  }

  let tactic = (tactic: string): JSON.t => {
    open JSON.Encode
    object([
      ("tactic", string(tactic)),
    ])
  }

  let searchQuery = (query: string, aspectTags: array<string>): JSON.t => {
    open JSON.Encode
    object([
      ("query", string(query)),
      ("aspect_tags", array(string, aspectTags)),
    ])
  }
}

// API functions
let handleResponse = async (response: Fetch.Response.t): Promise.t<apiResponse<'a>> => {
  if response->Fetch.Response.ok {
    try {
      let json = await response->Fetch.Response.json
      Promise.resolve({data: Some(json), error: None})
    } catch {
    | error => Promise.resolve({
        data: None,
        error: Some(`Failed to parse response: ${error->JSON.stringify}`),
      })
    }
  } else {
    let status = response->Fetch.Response.status
    Promise.resolve({
      data: None,
      error: Some(`API error: ${status->Int.toString}`),
    })
  }
}

// Initialize proof session
let initProofSession = async (prover: prover): Promise.t<result<proofState, string>> => {
  try {
    let response = await Fetch.fetch(
      `${apiBase}/proof/init`,
      {
        method: #POST,
        headers: Headers.fromObject({
          "Content-Type": "application/json",
        }),
        body: Encode.prover(prover)->JSON.stringify->Body.string,
      },
    )

    let result = await handleResponse(response)
    switch result {
    | {data: Some(json), error: None} =>
      try {
        let state = Decode.proofState(json)
        Promise.resolve(Ok(state))
      } catch {
      | error => Promise.resolve(Error(`Decode error: ${error->JSON.stringify}`))
      }
    | {error: Some(err)} => Promise.resolve(Error(err))
    | _ => Promise.resolve(Error("Unknown error"))
    }
  } catch {
  | error => Promise.resolve(Error(`Network error: ${error->JSON.stringify}`))
  }
}

// Apply tactic
let applyTactic = async (
  tactic: string,
  goalId: string,
): Promise.t<result<proofState, string>> => {
  try {
    let response = await Fetch.fetch(
      `${apiBase}/proof/tactic`,
      {
        method: #POST,
        headers: Headers.fromObject({
          "Content-Type": "application/json",
        }),
        body: JSON.stringify(
          JSON.Encode.object([
            ("tactic", JSON.Encode.string(tactic)),
            ("goal_id", JSON.Encode.string(goalId)),
          ]),
        )->Body.string,
      },
    )

    let result = await handleResponse(response)
    switch result {
    | {data: Some(json), error: None} =>
      try {
        let state = Decode.proofState(json)
        Promise.resolve(Ok(state))
      } catch {
      | error => Promise.resolve(Error(`Decode error: ${error->JSON.stringify}`))
      }
    | {error: Some(err)} => Promise.resolve(Error(err))
    | _ => Promise.resolve(Error("Unknown error"))
    }
  } catch {
  | error => Promise.resolve(Error(`Network error: ${error->JSON.stringify}`))
  }
}

// Get tactic suggestions (neural)
let getTacticSuggestions = async (
  goalId: string,
  aspectTags: array<string>,
): Promise.t<result<array<tacticSuggestion>, string>> => {
  try {
    let url = `${apiBase}/proof/suggestions?goal_id=${goalId}&tags=${aspectTags->Array.joinWith(",")}`
    let response = await Fetch.fetch(url)

    let result = await handleResponse(response)
    switch result {
    | {data: Some(json), error: None} =>
      try {
        let suggestions = JSON.Decode.array(Decode.tacticSuggestion, json)
        Promise.resolve(Ok(suggestions))
      } catch {
      | error => Promise.resolve(Error(`Decode error: ${error->JSON.stringify}`))
      }
    | {error: Some(err)} => Promise.resolve(Error(err))
    | _ => Promise.resolve(Error("Unknown error"))
    }
  } catch {
  | error => Promise.resolve(Error(`Network error: ${error->JSON.stringify}`))
  }
}

// Search theorems
let searchTheorems = async (
  query: string,
  aspectTags: array<string>,
): Promise.t<result<array<string>, string>> => {
  try {
    let response = await Fetch.fetch(
      `${apiBase}/theorems/search`,
      {
        method: #POST,
        headers: Headers.fromObject({
          "Content-Type": "application/json",
        }),
        body: Encode.searchQuery(query, aspectTags)->JSON.stringify->Body.string,
      },
    )

    let result = await handleResponse(response)
    switch result {
    | {data: Some(json), error: None} =>
      try {
        let theorems = JSON.Decode.array(JSON.Decode.string, json)
        Promise.resolve(Ok(theorems))
      } catch {
      | error => Promise.resolve(Error(`Decode error: ${error->JSON.stringify}`))
      }
    | {error: Some(err)} => Promise.resolve(Error(err))
    | _ => Promise.resolve(Error("Unknown error"))
    }
  } catch {
  | error => Promise.resolve(Error(`Network error: ${error->JSON.stringify}`))
  }
}

// Get aspect tags
let getAspectTags = async (): Promise.t<result<array<aspectTag>, string>> => {
  try {
    let response = await Fetch.fetch(`${apiBase}/aspects/tags`)

    let result = await handleResponse(response)
    switch result {
    | {data: Some(json), error: None} =>
      try {
        let tags = JSON.Decode.array(Decode.aspectTag, json)
        Promise.resolve(Ok(tags))
      } catch {
      | error => Promise.resolve(Error(`Decode error: ${error->JSON.stringify}`))
      }
    | {error: Some(err)} => Promise.resolve(Error(err))
    | _ => Promise.resolve(Error("Unknown error"))
    }
  } catch {
  | error => Promise.resolve(Error(`Network error: ${error->JSON.stringify}`))
  }
}

// Get proof tree structure
let getProofTree = async (): Promise.t<result<JSON.t, string>> => {
  try {
    let response = await Fetch.fetch(`${apiBase}/proof/tree`)

    let result = await handleResponse(response)
    switch result {
    | {data: Some(json), error: None} => Promise.resolve(Ok(json))
    | {error: Some(err)} => Promise.resolve(Error(err))
    | _ => Promise.resolve(Error("Unknown error"))
    }
  } catch {
  | error => Promise.resolve(Error(`Network error: ${error->JSON.stringify}`))
  }
}
