// SPDX-License-Identifier: MIT OR Palimpsest-0.6
// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team

/**
 * ProofViewer component - Display complete proof state
 * Shows proof script, execution history, and prover-specific syntax
 */

open Store

@react.component
let make = () => {
  let (state, _dispatch) = useStore()
  let (showSyntax, setShowSyntax) = React.useState(() => true)

  let getSyntaxHighlightClass = prover =>
    switch prover {
    | Agda => "syntax-agda"
    | Coq => "syntax-coq"
    | Lean => "syntax-lean"
    | Isabelle => "syntax-isabelle"
    | Z3 | CVC5 => "syntax-smt"
    | Metamath => "syntax-metamath"
    | HOLLight | HOL4 => "syntax-hol"
    | Mizar => "syntax-mizar"
    | PVS => "syntax-pvs"
    | ACL2 => "syntax-lisp"
    }

  let renderProofLine = (tactic: string, index: int) => {
    let syntaxClass = switch state.selectedProver {
    | Some(prover) => getSyntaxHighlightClass(prover)
    | None => ""
    }

    <div
      key={Int.toString(index)}
      className="proof-line flex items-start py-2 px-3 hover:bg-gray-50 border-b border-gray-100">
      <span className="line-number text-xs text-gray-400 mr-4 font-mono w-8 text-right">
        {React.string(Int.toString(index + 1))}
      </span>
      <code className={`flex-1 text-sm font-mono ${syntaxClass}`}>
        {React.string(tactic)}
      </code>
    </div>
  }

  let renderProofStats = (proofState: proofState) => {
    let totalLines = Array.length(proofState.proofScript)
    let goalsRemaining = Array.length(proofState.goals)
    let progress = if totalLines > 0 && goalsRemaining == 0 {
      100.0
    } else {
      0.0 // Can be enhanced with more sophisticated progress tracking
    }

    <div className="proof-stats grid grid-cols-3 gap-4 mb-4">
      <div className="stat-card p-3 bg-blue-50 border border-blue-200 rounded-lg">
        <p className="text-xs text-blue-600 font-semibold"> {React.string("Proof Lines")} </p>
        <p className="text-2xl font-bold text-blue-900"> {React.string(Int.toString(totalLines))} </p>
      </div>
      <div className="stat-card p-3 bg-purple-50 border border-purple-200 rounded-lg">
        <p className="text-xs text-purple-600 font-semibold"> {React.string("Goals Left")} </p>
        <p className="text-2xl font-bold text-purple-900">
          {React.string(Int.toString(goalsRemaining))}
        </p>
      </div>
      <div className="stat-card p-3 bg-green-50 border border-green-200 rounded-lg">
        <p className="text-xs text-green-600 font-semibold"> {React.string("Progress")} </p>
        <p className="text-2xl font-bold text-green-900">
          {React.string(Float.toString(progress) ++ "%")}
        </p>
      </div>
    </div>
  }

  <div className="proof-viewer">
    <div className="header mb-4">
      <div className="flex justify-between items-center">
        <div>
          <h2 className="text-2xl font-bold text-gray-900"> {React.string("Proof Script")} </h2>
          {switch state.selectedProver {
          | Some(prover) =>
            <p className="text-sm text-gray-600">
              {React.string(`Prover: ${proverToString(prover)}`)}
            </p>
          | None => React.null
          }}
        </div>
        <div className="controls flex gap-2">
          <button
            className={`px-3 py-1 text-sm rounded transition-colors ${
              showSyntax
                ? "bg-blue-600 text-white"
                : "bg-gray-200 text-gray-700 hover:bg-gray-300"
            }`}
            onClick={_ => setShowSyntax(prev => !prev)}>
            {React.string(showSyntax ? "Hide Syntax" : "Show Syntax")}
          </button>
        </div>
      </div>
    </div>

    {switch state.proofState {
    | Some(ps) => {
        renderProofStats(ps)

        if Array.length(ps.proofScript) == 0 {
          <div className="empty-proof p-8 text-center bg-gray-50 border border-gray-300 rounded-lg">
            <p className="text-gray-600"> {React.string("No proof steps yet")} </p>
            <p className="text-sm text-gray-500 mt-2">
              {React.string("Apply tactics to build your proof")}
            </p>
          </div>
        } else {
          <div className="proof-script bg-white border border-gray-300 rounded-lg overflow-hidden">
            <div className="proof-header px-4 py-2 bg-gray-100 border-b border-gray-300">
              <p className="text-xs font-semibold text-gray-700">
                {React.string("PROOF SCRIPT")}
              </p>
            </div>
            <div className="proof-content max-h-96 overflow-y-auto">
              {ps.proofScript->Array.mapWithIndex(renderProofLine)->React.array}
            </div>
          </div>
        }

        if ps.completed {
          <div className="proof-complete mt-4 p-4 bg-green-50 border-2 border-green-500 rounded-lg">
            <div className="flex items-center">
              <span className="text-4xl mr-4"> {React.string("✓")} </span>
              <div>
                <h3 className="text-xl font-bold text-green-800">
                  {React.string("Proof Completed!")}
                </h3>
                <p className="text-sm text-green-700">
                  {React.string("All goals have been successfully proven.")}
                </p>
              </div>
            </div>
          </div>
        } else {
          React.null
        }
      }
    | None =>
      <div className="no-proof p-8 text-center bg-gray-50 border border-gray-300 rounded-lg">
        <p className="text-gray-600"> {React.string("No active proof session")} </p>
        <p className="text-sm text-gray-500 mt-2">
          {React.string("Select a prover and start proving")}
        </p>
      </div>
    }}

    <div className="syntax-legend mt-4 p-4 bg-gray-50 border border-gray-200 rounded-lg">
      <h3 className="font-bold text-sm text-gray-900 mb-2">
        {React.string("Syntax Highlighting")}
      </h3>
      <p className="text-xs text-gray-700">
        {React.string(
          "Proof scripts are displayed with prover-specific syntax highlighting. " ++
          "Each of the 12 provers has its own color scheme and formatting rules.",
        )}
      </p>
    </div>
  </div>
}
