K9!
# SPDX-License-Identifier: MPL-2.0
# intend.k9.ncl — K9 trust-tier component of the intend trident
# Author: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# Pairs with: Intentfile.a2ml (declaration) + intend.ncl (runner).
# Trident completeness is a hard precondition — a repo shipping
# Intentfile without this file AND its runner is an invalid trident;
# the contractile CLI's verify gate refuses partial publication.
#
# Verb:       intend          (north star — commitments + aspirations)
# Tier:       Hunt            (capability: subprocess probes may shell out)
# Authority:  reporting       (never blocks; drift-log only)
#
# Cardinality: ONE intend trident per repo (see feedback_contractile_
# layout_rules.md). ANCHOR.a2ml is the sole multi-instance exception —
# it is NOT a verb contractile.
#
# ECHIDNA context: intend records progress toward committed next-actions
# (prover-backend coverage, trust-pipeline hardening, VeriSimDB recording,
# Hypatia learning loop) and lists horizon aspirations. It NEVER asserts
# these as shipped — intent is guidance, not evidence-of-completion. The
# blocking verbs (must/trust/bust) carry the gates; intend reports only.
#
# Design commitments baked in (see memory trail 2026-04-18 for full
# context; key files referenced by name in annotations below):
# * α two-axis (tier × authority) — structurally separate capability
#   from authority so "Hunt tier = can override" is impossible.
# * Variance schema first-class, not comment markers
#   (feedback_audit_tool_suppression_design.md — structural > markers).
# * Sessional drift detection hooks (on_close, on_open).
# * Ratification at session open; drift log at session close.
# * Evidence sinks: VeriSimDB (queryable) + descriptiles/DRIFT.a2ml (repo-local).
# * Failure-mode defenses cross-referenced to the AI failure catalog.

let base_k9 = import "../k9/template-hunt.k9.ncl" in
let base    = import "../_base.ncl" in

{
  pedigree = base_k9.pedigree_schema & {
    contractile_verb = "intend",
    paired_xfile     = "../intend/Intentfile.a2ml",
    paired_runner    = "../intend/intend.ncl",

    # α two-axis declaration — capability × authority.
    # intend is Hunt-capable (probes shell out) but reporting-authority
    # (never blocks). must/trust/bust declare (Hunt, blocking);
    # adjust/dust declare (Yard, advisory). Splitting the axes
    # means "I'm Hunt-tier so I can override everything" is structurally
    # impossible — authority is a separate field.
    tier      = 'Hunt,
    authority = 'reporting,

    metadata = {
      name = "intend-k9",
      version = "2.0.0",             # 1.0.0 (2026-04-18 AM): initial trident.
                                     # 2.0.0 (2026-04-18 PM): negotiation +
                                     # accountability + plain-language-translation
                                     # schema baked into on_open — prerequisite for
                                     # the adversarial Gemini+Copilot drift pilot.
      description = "Executes ECHIDNA Intentfile probes + emits drift log. Non-gating; reporting authority only. on_open hook implements negotiation-ratification-accountability protocol.",
      paired_xfile = "Intentfile.a2ml",
      paired_runner = "intend.ncl",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },

    security = {
      leash = 'Hunt,
      signature_required = true,
      trust_level = "subprocess + filesystem-read",
      allow_network = false,
      allow_filesystem_write = false,   # evidence sinks are indirected
      allow_subprocess = true,
    },
  },

  # -------------------------------------------------------------------
  # Variance schema — P-shape scoped exceptions per entry.
  # A variance suppresses a specific intent's or wish's obligation for a
  # reason, with approver + expiry. Expired variance = effective
  # re-imposition of the obligation. Unmet intent without a variance =
  # drift, logged to the drift log.
  # Per user 2026-04-18: variances are structural, not magic-comment
  # markers — markers are gameable.
  # -------------------------------------------------------------------
  variance_schema = {
    entry_id     | String,   # which intent/wish id the variance applies to
    reason       | String,
    approved_by  | String,
    scope        | String,   # path glob | session-id | "until-<date>"
    expires      | String,   # absolute date or condition
    review_notes | String | optional,
  },

  # -------------------------------------------------------------------
  # Execution policy
  # -------------------------------------------------------------------
  execution = {
    # When the component runs.
    # session_close is mandatory (the "picked up sessionally" check).
    triggers = [ 'session_close, 'on_demand, 'pre_push ],

    # Per-intent execution.
    per_intent = {
      run_probe = true,
      record_outcome = true,
      respect_variance = true,    # active variance suppresses failure
      on_unmet = 'log_drift,      # never 'fail — authority = reporting
    },

    # Per-wish execution (wishes are non-probeable; horizon-group only).
    per_wish = {
      run_probe = false,
      emit_horizon_summary = true,
      # Vertical alignment soft-check per user_6a2_is_contractile_ought.md:
      # highest-level alignment is meta ↔ north-star (soft), not hard gate.
      check_alignment_with_META = true,
    },

    # Evidence sinks — BOTH written, every execution.
    # VeriSimDB = queryable machine record (feedback_verisimdb_policy.md);
    # ECHIDNA records every proof attempt to VeriSimDB, so contractile
    # executions land in the same store for cross-query.
    # descriptiles/DRIFT.a2ml = repo-local append-only drift log (feedback_sessional_
    # drift_detection.md + user_6a2_is_contractile_ought.md descriptive role).
    evidence_sinks = [
      {
        kind   = 'verisimdb,
        table  = "contractile_executions",
        schema = "contractile_execution_v1",
      },
      {
        kind        = 'drift_log,
        path        = ".machine_readable/descriptiles/DRIFT.a2ml",
        append_only = true,
      },
    ],

    # Session-close hook — the "picked up sessionally" requirement.
    # Re-execute, diff against the last ratification, surface expired
    # variances, emit drift entries for new failures.
    on_close = {
      re_execute_all_intents = true,
      diff_against_last_ratification = true,
      emit_drift_entries_for_new_failures = true,
      surface_expired_variances = true,
    },

    # -----------------------------------------------------------------
    # Session-open hook — NEGOTIATION + RATIFICATION + ACCOUNTABILITY
    # (user_contract_negotiation_and_accountability_pledge.md)
    # (user_contractiles_agreed_at_session_start.md)
    #
    # Ratification is not passive acknowledgement; it is negotiation
    # ending in an explicit accountability pledge from BOTH parties.
    # Work cannot proceed before both pledges are on file.
    # -----------------------------------------------------------------
    on_open = {
      # --- Context presentation (pre-negotiation) ---
      render_summary = 'plain_language,    # metaphor-capture defense
      include_drift_log_from_last_close = true,
      include_active_variances = true,
      include_recent_anchors = true,
      anchor_lookback_weeks = 8,

      # --- Negotiation phase (five mandatory inputs) ---
      # AI must surface all five before the user is asked to ratify.
      # "Yes, and …" — not "yes". Missing any of the five = the
      # negotiation is incomplete and work cannot proceed.
      negotiation = {
        required = true,              # blank-cheque ratification refused

        # The five inputs the AI must contribute to the negotiation.
        # Each is a structured field the agent is required to populate,
        # not optional prose. See user_contract_negotiation_and_
        # accountability_pledge.md for the domain-language-rendering rule.
        ai_required_inputs = [
          'timeline_realism,           # "this will take X; not Y"
          'industry_standards,         # WCAG, ISO, OWASP, GDPR, licensing …
          'audience_feasibility,       # real addressable user set
          'resulting_invariants,       # what must/trust/adjust entries follow
          'ecosystem_dependencies,     # libs, licences, threat-model implications
        ],

        # User must actually engage with each input — not
        # auto-approve. If user tries to skip ("just do it, I trust you")
        # the system re-renders the obligations and requires the pledge.
        user_engagement_required = true,
        user_engagement_mode = 'per_input_response,

        # The AI does the specification-form work. The user reviews the
        # rendering in domain language and accepts / amends / pushes back.
        # User never has to author Nickel schemas or decide on type
        # specificity — that is the AI's translation responsibility,
        # with auditable faithfulness.
        specification_translation = {
          ai_produces_spec_form = true,
          user_reviews_in_domain_language = true,
          schema_authoring_is_ai_responsibility = true,
          translation_faithfulness_auditable = true,
          # Failure mode this closes: user is forced to learn spec-theory
          # (type refinement, Nickel contract grammar) to ratify a contract
          # — which drives users away from ratification entirely.
        },
      },

      # --- Accountability pledge (both parties, explicit) ---
      # Not "I read it" — "I am answerable for this obligation".
      # Both pledges are required before work proceeds; both are recorded.
      accountability_pledge = {
        required = true,
        parties = [
          {
            role = 'user,
            pledge = "I have reviewed the obligations as negotiated; I accept accountability for meeting the declared invariants and for the audience/timeline/standards consequences surfaced in negotiation.",
            signature_required = true,
          },
          {
            role = 'ai_agent,
            pledge = "I will hold the user to the obligations as negotiated, including by surfacing drift at session close and refusing off-contract actions, even when the user is enthusiastic about them. If the user wishes to depart from the contract, I will require a variance or amendment, not silent acceptance.",
            signature_required = true,
            # Per user_contractile_is_contract_do_not_break.md —
            # the AI is the holder of the line against enthusiasm drift.
          },
        ],
        signed_record_destination = ".machine_readable/descriptiles/ratification-<session-id>.a2ml",
        must_precede_work = true,
      },

      # --- Policy: ratification output ---
      # The ratification record IS the negotiation transcript + the
      # accountability pledge combined. One document; future-session
      # ground-truth for "what was agreed, who is accountable".
      ratification_record_shape = {
        includes_negotiation_transcript = true,
        includes_both_pledges = true,
        signed = true,
        dated = true,
        session_id = 'required,
        contract_hash = 'required,    # pins what was actually signed
      },
    },
  },

  # -------------------------------------------------------------------
  # Failure-mode defenses — explicit cross-reference to the catalog
  # (feedback_ai_failure_mode_catalog.md). New catalog entries that
  # shift this verb's defenses must update this list, not narrative.
  # -------------------------------------------------------------------
  failure_mode_defenses = [
    'A1_enthusiasm_capture,            # scope breach → drift log
    'A2_metaphor_capture,              # render_summary = 'plain_language
    'A3_allegory_drift,                # intents cite concrete obligations
    'C1_scope_creep,                   # feature-adjacent change needs intent_id
    'C3_helpfulness_inflation,         # changes without intent_id flagged
    'C4_modernization_drift,           # upgrade cannot cite intent → drift
    'D5_sycophancy,                    # ratification compares user framing vs contract
    'F1_across_session_forgetting,     # on_open reads last-ratification record
  ],
}
