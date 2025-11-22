// SPDX-License-Identifier: MIT OR Palimpsest-0.6
// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team

/**
 * GoalList component - Display current proof goals
 * Shows hypotheses, context, and conclusion for each goal
 */

open Store

@react.component
let make = (~onSelectGoal: string => unit) => {
  let (state, _dispatch) = useStore()

  let renderHypothesis = (hyp: string, index: int) =>
    <div key={Int.toString(index)} className="hypothesis pl-4 border-l-2 border-gray-300 mb-1">
      <code className="text-sm text-gray-700"> {React.string(hyp)} </code>
    </div>

  let renderContext = (ctx: string, index: int) =>
    <div key={Int.toString(index)} className="context-item text-xs text-gray-500 mb-1">
      <code> {React.string(ctx)} </code>
    </div>

  let renderGoal = (goal: goal, index: int, isCurrent: bool) => {
    let cardClasses = isCurrent
      ? "goal-card p-4 mb-4 bg-blue-50 border-2 border-blue-500 rounded-lg shadow-md"
      : "goal-card p-4 mb-4 bg-white border border-gray-300 rounded-lg hover:shadow-md transition-shadow cursor-pointer"

    <div
      key={goal.id}
      className=cardClasses
      onClick={_ => onSelectGoal(goal.id)}>
      <div className="goal-header flex justify-between items-center mb-3">
        <h3 className="font-bold text-lg">
          {React.string(`Goal ${Int.toString(index + 1)}`)}
          {isCurrent ? <span className="ml-2 text-blue-600"> {React.string("(Current)")} </span> : React.null}
        </h3>
        <span className="text-xs text-gray-500 font-mono"> {React.string(goal.id)} </span>
      </div>

      {if Array.length(goal.context) > 0 {
        <div className="context mb-3">
          <h4 className="text-xs font-semibold text-gray-600 mb-1">
            {React.string("CONTEXT")}
          </h4>
          <div className="context-list">
            {goal.context->Array.mapWithIndex(renderContext)->React.array}
          </div>
        </div>
      } else {
        React.null
      }}

      {if Array.length(goal.hypotheses) > 0 {
        <div className="hypotheses mb-3">
          <h4 className="text-sm font-semibold text-gray-700 mb-2">
            {React.string("Hypotheses")}
          </h4>
          <div className="hypothesis-list">
            {goal.hypotheses->Array.mapWithIndex(renderHypothesis)->React.array}
          </div>
        </div>
      } else {
        React.null
      }}

      <div className="conclusion">
        <h4 className="text-sm font-semibold text-gray-700 mb-2">
          {React.string("Conclusion")}
        </h4>
        <div className="conclusion-content p-3 bg-yellow-50 border-l-4 border-yellow-500 rounded">
          <code className="text-base font-semibold text-gray-900">
            {React.string(goal.conclusion)}
          </code>
        </div>
      </div>
    </div>
  }

  <div className="goal-list">
    <div className="goal-list-header mb-4">
      <h2 className="text-2xl font-bold text-gray-900"> {React.string("Proof Goals")} </h2>
      {switch state.proofState {
      | Some(ps) =>
        <p className="text-sm text-gray-600">
          {React.string(
            `${Int.toString(Array.length(ps.goals))} ${Array.length(ps.goals) == 1 ? "goal" : "goals"} remaining`,
          )}
        </p>
      | None => React.null
      }}
    </div>

    {switch state.proofState {
    | Some(ps) =>
      if Array.length(ps.goals) == 0 {
        <div className="no-goals p-8 text-center bg-green-50 border-2 border-green-500 rounded-lg">
          <div className="text-6xl mb-4"> {React.string("✓")} </div>
          <h3 className="text-2xl font-bold text-green-800 mb-2">
            {React.string("Proof Complete!")}
          </h3>
          <p className="text-green-700"> {React.string("All goals have been solved.")} </p>
        </div>
      } else {
        <div className="goals-container">
          {ps.goals->Array.mapWithIndex((goal, index) =>
            renderGoal(goal, index, index == ps.currentGoalIndex)
          )->React.array}
        </div>
      }
    | None =>
      <div className="no-proof-state p-8 text-center bg-gray-50 border border-gray-300 rounded-lg">
        <p className="text-gray-600"> {React.string("No active proof session")} </p>
        <p className="text-sm text-gray-500 mt-2">
          {React.string("Select a prover to start a new proof")}
        </p>
      </div>
    }}
  </div>
}
