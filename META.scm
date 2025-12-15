;; SPDX-License-Identifier: AGPL-3.0-or-later
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;;; META.scm — echidna

(define-module (echidna meta)
  #:export (architecture-decisions development-practices design-rationale))

(define architecture-decisions
  '((adr-001
     (title . "RSR Compliance")
     (status . "accepted")
     (date . "2025-12-15")
     (context . "*E*xtensible *C*ognitive *H*ybrid *I*ntelligence for *D*eductive *N*eural *A*ssistance")
     (decision . "Follow Rhodium Standard Repository guidelines")
     (consequences . ("RSR Gold target" "SHA-pinned actions" "SPDX headers" "Multi-platform CI")))))

(define development-practices
  '((code-style (languages . ("Agda" "CSS" "Dockerfile" "HTML" "Isabelle" "JavaScript" "Julia" "Just" "Lean" "Nix" "ReScript" "Rocq Prover" "Rust" "Scheme" "Shell" "TypeScript")) (formatter . "auto-detect") (linter . "auto-detect"))
    (security (sast . "CodeQL") (credentials . "env vars only"))
    (testing (coverage-minimum . 70))
    (versioning (scheme . "SemVer 2.0.0"))))

(define design-rationale
  '((why-rsr "RSR ensures consistency, security, and maintainability.")))
