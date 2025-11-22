// SPDX-License-Identifier: MIT OR Palimpsest-0.6
// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team

/**
 * TheoremSearch component - Search theorem libraries
 * Integrated with OpenCyc ontology and aspect tag filtering
 */

open Store

@react.component
let make = (~onSelectTheorem: string => unit) => {
  let (state, dispatch) = useStore()
  let (isSearching, setIsSearching) = React.useState(() => false)
  let (searchInput, setSearchInput) = React.useState(() => "")

  let handleSearch = () => {
    if String.length(searchInput) > 0 {
      setIsSearching(_ => true)
      dispatch(UpdateSearchQuery(searchInput))

      let activeTags = state.aspectTags
        ->Array.filter(tag => tag.active)
        ->Array.map(tag => tag.name)

      let _ = Client.searchTheorems(searchInput, activeTags)->Promise.then(result => {
        switch result {
        | Ok(results) => {
            dispatch(UpdateSearchResults(results))
            setIsSearching(_ => false)
            Promise.resolve()
          }
        | Error(err) => {
            dispatch(SetError(Some(err)))
            setIsSearching(_ => false)
            Promise.resolve()
          }
        }
      })
    }
  }

  let handleKeyPress = event => {
    if ReactEvent.Keyboard.key(event) == "Enter" {
      handleSearch()
    }
  }

  let toggleAspectTag = tagName => {
    dispatch(ToggleAspectTag(tagName))
  }

  let renderAspectTag = (tag: aspectTag) => {
    let classes = tag.active
      ? "px-3 py-1 text-sm font-semibold bg-purple-600 text-white rounded-full cursor-pointer hover:bg-purple-700"
      : "px-3 py-1 text-sm font-semibold bg-gray-200 text-gray-700 rounded-full cursor-pointer hover:bg-gray-300"

    <button
      key={tag.name}
      className=classes
      onClick={_ => toggleAspectTag(tag.name)}>
      {React.string(tag.name)}
    </button>
  }

  let renderResult = (theorem: string, index: int) =>
    <div
      key={Int.toString(index)}
      className="result-card p-4 mb-3 bg-white border border-gray-300 rounded-lg hover:shadow-md transition-shadow cursor-pointer"
      onClick={_ => onSelectTheorem(theorem)}>
      <div className="flex justify-between items-start">
        <code className="text-sm font-mono text-gray-900 flex-1"> {React.string(theorem)} </code>
        <button
          className="ml-4 px-3 py-1 bg-blue-600 text-white text-sm rounded hover:bg-blue-700 transition-colors"
          onClick={e => {
            ReactEvent.Mouse.stopPropagation(e)
            onSelectTheorem(theorem)
          }}>
          {React.string("Use")}
        </button>
      </div>
    </div>

  let renderAspectFilters = () => {
    // Group tags by category
    let categories = state.aspectTags->Array.reduce(Map.make(), (acc, tag) => {
      let existing = Map.get(acc, tag.category)->Option.getOr([])
      Map.set(acc, tag.category, Array.concat(existing, [tag]))
      acc
    })

    if Map.size(categories) == 0 {
      React.null
    } else {
      <div className="aspect-filters mb-4">
        <h3 className="text-sm font-bold text-gray-700 mb-2">
          {React.string("Filter by Aspect Tags")}
        </h3>
        {Map.entries(categories)
          ->Array.fromIterator
          ->Array.map(((category, tags)) =>
            <div key=category className="category-group mb-3">
              <p className="text-xs font-semibold text-gray-600 mb-1">
                {React.string(String.toUpperCase(category))}
              </p>
              <div className="flex flex-wrap gap-2">
                {tags->Array.map(renderAspectTag)->React.array}
              </div>
            </div>
          )
          ->React.array}
      </div>
    }
  }

  <div className="theorem-search">
    <div className="header mb-4">
      <h2 className="text-2xl font-bold text-gray-900"> {React.string("Theorem Library")} </h2>
      <p className="text-sm text-gray-600">
        {React.string("Search across integrated theorem libraries with aspect tagging")}
      </p>
    </div>

    <div className="search-box mb-4">
      <div className="flex gap-2">
        <input
          type_="text"
          className="flex-1 px-4 py-2 border border-gray-300 rounded-lg focus:outline-none focus:ring-2 focus:ring-blue-500"
          placeholder="Search theorems, lemmas, definitions..."
          value=searchInput
          onChange={e => {
            let value = ReactEvent.Form.target(e)["value"]
            setSearchInput(_ => value)
          }}
          onKeyPress=handleKeyPress
        />
        <button
          className="px-6 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors font-semibold disabled:opacity-50 disabled:cursor-not-allowed"
          onClick={_ => handleSearch()}
          disabled=isSearching>
          {React.string(isSearching ? "Searching..." : "Search")}
        </button>
      </div>
    </div>

    {renderAspectFilters()}

    {if isSearching {
      <div className="loading p-8 text-center">
        <div className="animate-spin rounded-full h-12 w-12 border-b-2 border-blue-600 mx-auto mb-4" />
        <p className="text-gray-600"> {React.string("Searching theorem libraries...")} </p>
      </div>
    } else if String.length(state.searchQuery) == 0 {
      <div className="search-help p-8 text-center bg-gray-50 border border-gray-300 rounded-lg">
        <div className="text-5xl mb-4"> {React.string("🔍")} </div>
        <p className="text-gray-600 mb-2"> {React.string("Enter a search query to begin")} </p>
        <p className="text-sm text-gray-500">
          {React.string("Search by theorem name, statement, or keywords")}
        </p>
      </div>
    } else if Array.length(state.searchResults) == 0 {
      <div className="no-results p-8 text-center bg-yellow-50 border border-yellow-300 rounded-lg">
        <p className="text-yellow-800"> {React.string("No theorems found")} </p>
        <p className="text-sm text-yellow-700 mt-2">
          {React.string(`No results for "${state.searchQuery}"`)}
        </p>
      </div>
    } else {
      <div className="search-results">
        <div className="results-header mb-3">
          <p className="text-sm text-gray-600">
            {React.string(
              `Found ${Int.toString(Array.length(state.searchResults))} ${Array.length(state.searchResults) == 1 ? "result" : "results"}`,
            )}
          </p>
        </div>
        <div className="results-list max-h-96 overflow-y-auto">
          {state.searchResults->Array.mapWithIndex(renderResult)->React.array}
        </div>
      </div>
    }}

    <div className="info-box mt-4 p-4 bg-blue-50 border border-blue-200 rounded-lg">
      <h3 className="font-bold text-sm text-blue-900 mb-2">
        {React.string("OpenCyc Integration")}
      </h3>
      <p className="text-xs text-blue-800">
        {React.string(
          "Theorem search is powered by OpenCyc ontology integration, providing " ++
          "semantic understanding and aspect-based filtering across all 12 provers.",
        )}
      </p>
    </div>
  </div>
}
