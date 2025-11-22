// SPDX-License-Identifier: MIT OR Palimpsest-0.6
// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team

/**
 * Application state management for ECHIDNA UI
 * Manages proof state, prover selection, and UI state
 */

// Types for theorem provers
type proverTier =
  | Tier1 // Agda, Coq/Rocq, Lean, Isabelle, Z3, CVC5
  | Tier2 // Metamath, HOL Light, Mizar
  | Tier3 // PVS, ACL2
  | Tier4 // HOL4

type prover =
  | Agda
  | Coq
  | Lean
  | Isabelle
  | Z3
  | CVC5
  | Metamath
  | HOLLight
  | Mizar
  | PVS
  | ACL2
  | HOL4

// Proof state types
type goal = {
  id: string,
  hypotheses: array<string>,
  conclusion: string,
  context: array<string>,
}

type tacticSuggestion = {
  tactic: string,
  confidence: float,
  premise: option<string>,
  aspectTags: array<string>,
}

type proofState = {
  goals: array<goal>,
  currentGoalIndex: int,
  proofScript: array<string>,
  completed: bool,
}

type aspectTag = {
  name: string,
  category: string, // "domain", "difficulty", "technique", etc.
  active: bool,
}

// Application state
type state = {
  selectedProver: option<prover>,
  proofState: option<proofState>,
  tacticSuggestions: array<tacticSuggestion>,
  aspectTags: array<aspectTag>,
  searchQuery: string,
  searchResults: array<string>,
  isLoading: bool,
  error: option<string>,
}

// Actions
type action =
  | SelectProver(prover)
  | UpdateProofState(proofState)
  | UpdateTacticSuggestions(array<tacticSuggestion>)
  | ApplyTactic(string)
  | ToggleAspectTag(string)
  | UpdateSearchQuery(string)
  | UpdateSearchResults(array<string>)
  | SetLoading(bool)
  | SetError(option<string>)
  | ResetState

// Helper functions
let proverToString = prover =>
  switch prover {
  | Agda => "Agda"
  | Coq => "Coq"
  | Lean => "Lean"
  | Isabelle => "Isabelle"
  | Z3 => "Z3"
  | CVC5 => "CVC5"
  | Metamath => "Metamath"
  | HOLLight => "HOL Light"
  | Mizar => "Mizar"
  | PVS => "PVS"
  | ACL2 => "ACL2"
  | HOL4 => "HOL4"
  }

let proverTier = prover =>
  switch prover {
  | Agda | Coq | Lean | Isabelle | Z3 | CVC5 => Tier1
  | Metamath | HOLLight | Mizar => Tier2
  | PVS | ACL2 => Tier3
  | HOL4 => Tier4
  }

let allProvers = [
  Agda, Coq, Lean, Isabelle, Z3, CVC5,
  Metamath, HOLLight, Mizar,
  PVS, ACL2,
  HOL4
]

// Initial state
let initialState = {
  selectedProver: None,
  proofState: None,
  tacticSuggestions: [],
  aspectTags: [],
  searchQuery: "",
  searchResults: [],
  isLoading: false,
  error: None,
}

// Reducer
let reducer = (state, action) =>
  switch action {
  | SelectProver(prover) => {
      ...state,
      selectedProver: Some(prover),
      error: None,
    }
  | UpdateProofState(proofState) => {
      ...state,
      proofState: Some(proofState),
      error: None,
    }
  | UpdateTacticSuggestions(suggestions) => {
      ...state,
      tacticSuggestions: suggestions,
    }
  | ApplyTactic(tactic) => {
      // Update proof script
      switch state.proofState {
      | Some(ps) => {
          ...state,
          proofState: Some({
            ...ps,
            proofScript: Array.concat(ps.proofScript, [tactic]),
          }),
        }
      | None => state
      }
    }
  | ToggleAspectTag(tagName) => {
      ...state,
      aspectTags: state.aspectTags->Array.map(tag =>
        tag.name === tagName ? {...tag, active: !tag.active} : tag
      ),
    }
  | UpdateSearchQuery(query) => {
      ...state,
      searchQuery: query,
    }
  | UpdateSearchResults(results) => {
      ...state,
      searchResults: results,
    }
  | SetLoading(loading) => {
      ...state,
      isLoading: loading,
    }
  | SetError(error) => {
      ...state,
      error: error,
      isLoading: false,
    }
  | ResetState => initialState
  }

// React context
let context = React.createContext((initialState, (_: action) => ()))

module Provider = {
  let make = React.Context.provider(context)
}

// Custom hook
let useStore = () => {
  React.useContext(context)
}
