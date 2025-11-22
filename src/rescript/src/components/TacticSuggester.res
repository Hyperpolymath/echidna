// SPDX-License-Identifier: MIT OR Palimpsest-0.6
// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team

/**
 * TacticSuggester component - Neural tactic suggestions
 * Displays AI-powered tactic recommendations with confidence scores
 */

open Store

@react.component
let make = (~onApplyTactic: string => unit, ~goalId: option<string>) => {
  let (state, dispatch) = useStore()
  let (isRefreshing, setIsRefreshing) = React.useState(() => false)

  // Fetch suggestions when goal changes
  React.useEffect(() => {
    switch goalId {
    | Some(id) => {
        setIsRefreshing(_ => true)
        let activeTags = state.aspectTags
          ->Array.filter(tag => tag.active)
          ->Array.map(tag => tag.name)

        let _ = Client.getTacticSuggestions(id, activeTags)->Promise.then(result => {
          switch result {
          | Ok(suggestions) => {
              dispatch(UpdateTacticSuggestions(suggestions))
              setIsRefreshing(_ => false)
              Promise.resolve()
            }
          | Error(err) => {
              dispatch(SetError(Some(err)))
              setIsRefreshing(_ => false)
              Promise.resolve()
            }
          }
        })
      }
    | None => ()
    }
    None
  }, [goalId])

  let confidenceColor = (confidence: float) =>
    if confidence >= 0.8 {
      "bg-green-100 text-green-800"
    } else if confidence >= 0.5 {
      "bg-yellow-100 text-yellow-800"
    } else {
      "bg-orange-100 text-orange-800"
    }

  let confidenceBar = (confidence: float) => {
    let width = Float.toString(confidence *. 100.0) ++ "%"
    let bgColor = if confidence >= 0.8 {
      "bg-green-500"
    } else if confidence >= 0.5 {
      "bg-yellow-500"
    } else {
      "bg-orange-500"
    }

    <div className="w-full bg-gray-200 rounded-full h-2 mt-2">
      <div className={`${bgColor} h-2 rounded-full transition-all`} style={{width: width}} />
    </div>
  }

  let renderAspectTag = (tag: string) =>
    <span
      key=tag
      className="inline-block px-2 py-1 text-xs font-semibold bg-purple-100 text-purple-800 rounded-full mr-1">
      {React.string(tag)}
    </span>

  let renderSuggestion = (suggestion: tacticSuggestion, index: int) => {
    let confidencePercent = Int.toString(Float.toInt(suggestion.confidence *. 100.0)) ++ "%"

    <div
      key={Int.toString(index)}
      className="suggestion-card p-4 mb-3 bg-white border border-gray-300 rounded-lg hover:shadow-md transition-shadow">
      <div className="flex justify-between items-start mb-2">
        <div className="flex-1">
          <code className="text-base font-semibold text-gray-900 bg-gray-50 px-2 py-1 rounded">
            {React.string(suggestion.tactic)}
          </code>
        </div>
        <button
          className="ml-4 px-4 py-2 bg-blue-600 text-white rounded hover:bg-blue-700 transition-colors font-semibold text-sm"
          onClick={_ => onApplyTactic(suggestion.tactic)}>
          {React.string("Apply")}
        </button>
      </div>

      <div className="confidence mt-3">
        <div className="flex justify-between items-center mb-1">
          <span className="text-xs font-semibold text-gray-600">
            {React.string("Confidence")}
          </span>
          <span className={`text-xs font-bold px-2 py-1 rounded ${confidenceColor(suggestion.confidence)}`}>
            {React.string(confidencePercent)}
          </span>
        </div>
        {confidenceBar(suggestion.confidence)}
      </div>

      {switch suggestion.premise {
      | Some(premise) =>
        <div className="premise mt-3 p-2 bg-blue-50 border-l-2 border-blue-500 rounded">
          <p className="text-xs font-semibold text-blue-900 mb-1">
            {React.string("Suggested Premise:")}
          </p>
          <code className="text-sm text-blue-800"> {React.string(premise)} </code>
        </div>
      | None => React.null
      }}

      {if Array.length(suggestion.aspectTags) > 0 {
        <div className="aspect-tags mt-3">
          <p className="text-xs font-semibold text-gray-600 mb-1">
            {React.string("Aspect Tags:")}
          </p>
          <div className="tags-container">
            {suggestion.aspectTags->Array.map(renderAspectTag)->React.array}
          </div>
        </div>
      } else {
        React.null
      }}
    </div>
  }

  <div className="tactic-suggester">
    <div className="header mb-4 flex justify-between items-center">
      <div>
        <h2 className="text-2xl font-bold text-gray-900"> {React.string("Tactic Suggestions")} </h2>
        <p className="text-sm text-gray-600"> {React.string("AI-powered recommendations")} </p>
      </div>
      {switch goalId {
      | Some(_) =>
        <button
          className="px-4 py-2 bg-gray-200 text-gray-700 rounded hover:bg-gray-300 transition-colors disabled:opacity-50"
          disabled=isRefreshing
          onClick={_ => {
            // Trigger refresh by re-fetching
            setIsRefreshing(_ => true)
          }}>
          {React.string(isRefreshing ? "Refreshing..." : "Refresh")}
        </button>
      | None => React.null
      }}
    </div>

    {if isRefreshing {
      <div className="loading p-8 text-center">
        <div className="animate-spin rounded-full h-12 w-12 border-b-2 border-blue-600 mx-auto mb-4" />
        <p className="text-gray-600"> {React.string("Generating suggestions...")} </p>
      </div>
    } else if Array.length(state.tacticSuggestions) == 0 {
      <div className="no-suggestions p-8 text-center bg-gray-50 border border-gray-300 rounded-lg">
        <p className="text-gray-600"> {React.string("No suggestions available")} </p>
        <p className="text-sm text-gray-500 mt-2">
          {React.string("Select a goal to get AI-powered tactic suggestions")}
        </p>
      </div>
    } else {
      <div className="suggestions-container">
        {state.tacticSuggestions->Array.mapWithIndex(renderSuggestion)->React.array}
      </div>
    }}

    <div className="info-box mt-4 p-4 bg-purple-50 border border-purple-200 rounded-lg">
      <h3 className="font-bold text-sm text-purple-900 mb-2">
        {React.string("About Neural Suggestions")}
      </h3>
      <p className="text-xs text-purple-800">
        {React.string(
          "Suggestions are generated using neural premise selection and aspect tagging. " ++
          "Higher confidence scores indicate tactics more likely to succeed. " ++
          "Aspect tags help filter suggestions by domain and technique.",
        )}
      </p>
    </div>
  </div>
}
