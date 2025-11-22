// SPDX-License-Identifier: MIT OR Palimpsest-0.6
// SPDX-FileCopyrightText: 2025 ECHIDNA Project Team

/**
 * ProverSelector component - Choose from 12 theorem provers
 * Organized by tier with visual indicators
 */

open Store

@react.component
let make = (~onSelect: prover => unit) => {
  let (state, dispatch) = useStore()

  let handleSelect = (prover: prover) => {
    dispatch(SelectProver(prover))
    onSelect(prover)
  }

  let tierColor = tier =>
    switch tier {
    | Tier1 => "bg-green-100 border-green-500"
    | Tier2 => "bg-blue-100 border-blue-500"
    | Tier3 => "bg-yellow-100 border-yellow-500"
    | Tier4 => "bg-orange-100 border-orange-500"
    }

  let tierLabel = tier =>
    switch tier {
    | Tier1 => "Tier 1: Core"
    | Tier2 => "Tier 2: Extended"
    | Tier3 => "Tier 3: Specialized"
    | Tier4 => "Tier 4: Advanced"
    }

  let proversByTier = tier =>
    allProvers->Array.filter(p => proverTier(p) == tier)

  let renderProverCard = prover => {
    let isSelected = switch state.selectedProver {
    | Some(p) => p == prover
    | None => false
    }

    let tier = proverTier(prover)
    let baseClasses = `p-4 rounded-lg border-2 cursor-pointer transition-all hover:shadow-md ${tierColor(tier)}`
    let classes = isSelected ? `${baseClasses} ring-2 ring-blue-500 shadow-lg` : baseClasses

    <div
      key={proverToString(prover)}
      className=classes
      onClick={_ => handleSelect(prover)}>
      <h3 className="font-bold text-lg mb-1"> {React.string(proverToString(prover))} </h3>
      <p className="text-sm text-gray-600">
        {React.string(
          switch prover {
          | Agda => "Dependently typed language"
          | Coq => "Proof assistant with tactics"
          | Lean => "Modern proof assistant"
          | Isabelle => "HOL-based system"
          | Z3 => "SMT solver"
          | CVC5 => "SMT solver"
          | Metamath => "Minimal logic system"
          | HOLLight => "Simple HOL system"
          | Mizar => "Mathematical language"
          | PVS => "Verification system"
          | ACL2 => "Applicative lisp"
          | HOL4 => "Higher-order logic"
          },
        )}
      </p>
    </div>
  }

  let renderTier = tier => {
    let provers = proversByTier(tier)
    if Array.length(provers) == 0 {
      React.null
    } else {
      <div key={tierLabel(tier)} className="mb-6">
        <h2 className="text-xl font-bold mb-3 text-gray-800"> {React.string(tierLabel(tier))} </h2>
        <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">
          {provers->Array.map(renderProverCard)->React.array}
        </div>
      </div>
    }
  }

  <div className="prover-selector p-6">
    <div className="mb-6">
      <h1 className="text-3xl font-bold text-gray-900 mb-2">
        {React.string("Select Theorem Prover")}
      </h1>
      <p className="text-gray-600">
        {React.string("Choose from 12 integrated theorem provers across 4 tiers")}
      </p>
    </div>

    {switch state.selectedProver {
    | Some(prover) =>
      <div className="mb-4 p-4 bg-blue-50 border-l-4 border-blue-500 rounded">
        <p className="text-blue-800">
          <strong> {React.string("Selected: ")} </strong>
          {React.string(proverToString(prover))}
        </p>
      </div>
    | None => React.null
    }}

    <div className="space-y-6">
      {[Tier1, Tier2, Tier3, Tier4]->Array.map(renderTier)->React.array}
    </div>

    <div className="mt-6 p-4 bg-gray-50 rounded-lg">
      <h3 className="font-bold mb-2"> {React.string("Tier Information")} </h3>
      <ul className="text-sm text-gray-700 space-y-1">
        <li> {React.string("• Tier 1: Core provers (6) - Agda, Coq, Lean, Isabelle, Z3, CVC5")} </li>
        <li> {React.string("• Tier 2: Extended coverage (3) - Metamath, HOL Light, Mizar")} </li>
        <li> {React.string("• Tier 3: Specialized systems (2) - PVS, ACL2")} </li>
        <li> {React.string("• Tier 4: Advanced logic (1) - HOL4")} </li>
      </ul>
    </div>
  </div>
}
