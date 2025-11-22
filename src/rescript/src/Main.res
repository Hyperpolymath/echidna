// SPDX-License-Identifier: MIT OR Palimpsest-0.6
// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team

/**
 * Main entry point for ECHIDNA UI
 * Coordinates all components and manages application state
 */

open Store

type view =
  | SelectProver
  | ProofSession
  | TheoremLibrary

@react.component
let make = () => {
  let (state, dispatch) = React.useReducer(reducer, initialState)
  let (currentView, setCurrentView) = React.useState(() => SelectProver)
  let (selectedGoalId, setSelectedGoalId) = React.useState(() => None)

  // Load aspect tags on mount
  React.useEffect(() => {
    let _ = Client.getAspectTags()->Promise.then(result => {
      switch result {
      | Ok(tags) => {
          dispatch(UpdateProofState({
            goals: [],
            currentGoalIndex: 0,
            proofScript: [],
            completed: false,
          }))
          // Initialize aspect tags
          let initializedTags = tags->Array.map(tag => {...tag, active: false})
          dispatch(
            UpdateProofState({
              goals: [],
              currentGoalIndex: 0,
              proofScript: [],
              completed: false,
            }),
          )
          Promise.resolve()
        }
      | Error(_) => Promise.resolve()
      }
    })
    None
  }, [])

  let handleSelectProver = prover => {
    dispatch(SetLoading(true))
    let _ = Client.initProofSession(prover)->Promise.then(result => {
      switch result {
      | Ok(proofState) => {
          dispatch(UpdateProofState(proofState))
          dispatch(SetLoading(false))
          setCurrentView(_ => ProofSession)
          Promise.resolve()
        }
      | Error(err) => {
          dispatch(SetError(Some(err)))
          dispatch(SetLoading(false))
          Promise.resolve()
        }
      }
    })
  }

  let handleApplyTactic = tactic => {
    switch selectedGoalId {
    | Some(goalId) => {
        dispatch(SetLoading(true))
        dispatch(ApplyTactic(tactic))

        let _ = Client.applyTactic(tactic, goalId)->Promise.then(result => {
          switch result {
          | Ok(newState) => {
              dispatch(UpdateProofState(newState))
              dispatch(SetLoading(false))
              Promise.resolve()
            }
          | Error(err) => {
              dispatch(SetError(Some(err)))
              dispatch(SetLoading(false))
              Promise.resolve()
            }
          }
        })
      }
    | None => ()
    }
  }

  let handleSelectGoal = goalId => {
    setSelectedGoalId(_ => Some(goalId))
  }

  let handleSelectTheorem = theorem => {
    // Apply theorem as a tactic
    handleApplyTactic(theorem)
  }

  let renderNavigation = () =>
    <nav className="bg-gray-800 text-white p-4 shadow-lg">
      <div className="container mx-auto flex justify-between items-center">
        <div className="flex items-center">
          <h1 className="text-2xl font-bold"> {React.string("🦔 ECHIDNA")} </h1>
          <p className="ml-4 text-sm text-gray-300">
            {React.string("Neurosymbolic Theorem Proving Platform")}
          </p>
        </div>
        <div className="flex gap-2">
          <button
            className={`px-4 py-2 rounded transition-colors ${
              currentView == SelectProver ? "bg-blue-600" : "bg-gray-700 hover:bg-gray-600"
            }`}
            onClick={_ => setCurrentView(_ => SelectProver)}>
            {React.string("Provers")}
          </button>
          <button
            className={`px-4 py-2 rounded transition-colors ${
              currentView == ProofSession ? "bg-blue-600" : "bg-gray-700 hover:bg-gray-600"
            }`}
            onClick={_ => setCurrentView(_ => ProofSession)}
            disabled={Option.isNone(state.selectedProver)}>
            {React.string("Proof")}
          </button>
          <button
            className={`px-4 py-2 rounded transition-colors ${
              currentView == TheoremLibrary ? "bg-blue-600" : "bg-gray-700 hover:bg-gray-600"
            }`}
            onClick={_ => setCurrentView(_ => TheoremLibrary)}>
            {React.string("Library")}
          </button>
        </div>
      </div>
    </nav>

  let renderError = () =>
    switch state.error {
    | Some(err) =>
      <div className="error-banner bg-red-50 border-l-4 border-red-500 p-4 mb-4">
        <div className="flex justify-between items-center">
          <div>
            <p className="font-bold text-red-800"> {React.string("Error")} </p>
            <p className="text-sm text-red-700"> {React.string(err)} </p>
          </div>
          <button
            className="text-red-500 hover:text-red-700"
            onClick={_ => dispatch(SetError(None))}>
            {React.string("✕")}
          </button>
        </div>
      </div>
    | None => React.null
    }

  let renderContent = () =>
    switch currentView {
    | SelectProver => <ProverSelector onSelect=handleSelectProver />
    | ProofSession =>
      <div className="proof-session-container grid grid-cols-1 lg:grid-cols-2 gap-6">
        <div className="left-panel space-y-6">
          <GoalList onSelectGoal=handleSelectGoal />
          <ProofViewer />
        </div>
        <div className="right-panel space-y-6">
          <TacticSuggester onApplyTactic=handleApplyTactic goalId=selectedGoalId />
          <ProofTree />
        </div>
      </div>
    | TheoremLibrary => <TheoremSearch onSelectTheorem=handleSelectTheorem />
    }

  <Store.Provider value=(state, dispatch)>
    <div className="app min-h-screen bg-gray-100">
      {renderNavigation()}
      <main className="container mx-auto py-8 px-4">
        {renderError()}
        {if state.isLoading {
          <div className="loading-overlay fixed inset-0 bg-black bg-opacity-50 flex items-center justify-center z-50">
            <div className="bg-white rounded-lg p-8 shadow-xl">
              <div className="animate-spin rounded-full h-16 w-16 border-b-4 border-blue-600 mx-auto mb-4" />
              <p className="text-gray-700 font-semibold"> {React.string("Loading...")} </p>
            </div>
          </div>
        } else {
          React.null
        }}
        {renderContent()}
      </main>
      <footer className="bg-gray-800 text-white py-4 mt-8">
        <div className="container mx-auto text-center text-sm">
          <p>
            {React.string("ECHIDNA v0.1.0 - Extensible Cognitive Hybrid Intelligence for Deductive Neural Assistance")}
          </p>
          <p className="text-gray-400 mt-1">
            {React.string("MIT OR Palimpsest-0.6 License")}
          </p>
        </div>
      </footer>
    </div>
  </Store.Provider>
}

// Mount the app
switch ReactDOM.querySelector("#root") {
| Some(root) => {
    let reactRoot = ReactDOM.Client.createRoot(root)
    ReactDOM.Client.render(reactRoot, <make />)
  }
| None => Console.error("Root element not found")
}
