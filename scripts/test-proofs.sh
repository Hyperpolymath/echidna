#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
# SPDX-License-Identifier: MIT OR Palimpsest-0.6

# Test all proof examples for ECHIDNA provers
# Usage: ./scripts/test-proofs.sh [prover_name]

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Project root
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROOFS_DIR="${PROJECT_ROOT}/proofs"

# Statistics
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0
SKIPPED_TESTS=0

# Log functions
log_info() {
    echo -e "${BLUE}[INFO]${NC} $*"
}

log_success() {
    echo -e "${GREEN}[PASS]${NC} $*"
}

log_error() {
    echo -e "${RED}[FAIL]${NC} $*"
}

log_skip() {
    echo -e "${YELLOW}[SKIP]${NC} $*"
}

log_section() {
    echo ""
    echo -e "${BLUE}======================================${NC}"
    echo -e "${BLUE}$*${NC}"
    echo -e "${BLUE}======================================${NC}"
}

# Check if a prover is available
check_prover() {
    local prover=$1
    local executable=$2

    if command -v "$executable" &> /dev/null; then
        return 0
    else
        return 1
    fi
}

# Test Agda proofs
test_agda() {
    log_section "Testing Agda Proofs"

    if ! check_prover "Agda" "agda"; then
        log_skip "Agda not installed"
        return
    fi

    local agda_dir="${PROOFS_DIR}/agda"
    if [ ! -d "$agda_dir" ]; then
        log_skip "No Agda proofs found"
        return
    fi

    for file in "$agda_dir"/*.agda; do
        [ -f "$file" ] || continue
        TOTAL_TESTS=$((TOTAL_TESTS + 1))

        local filename=$(basename "$file")
        log_info "Testing $filename..."

        if agda --safe "$file" &> /dev/null; then
            log_success "$filename"
            PASSED_TESTS=$((PASSED_TESTS + 1))
        else
            log_error "$filename"
            FAILED_TESTS=$((FAILED_TESTS + 1))
        fi
    done
}

# Test Coq proofs
test_coq() {
    log_section "Testing Coq Proofs"

    if ! check_prover "Coq" "coqc"; then
        log_skip "Coq not installed"
        return
    fi

    local coq_dir="${PROOFS_DIR}/coq"
    if [ ! -d "$coq_dir" ]; then
        log_skip "No Coq proofs found"
        return
    fi

    for file in "$coq_dir"/*.v; do
        [ -f "$file" ] || continue
        TOTAL_TESTS=$((TOTAL_TESTS + 1))

        local filename=$(basename "$file")
        log_info "Testing $filename..."

        if coqc "$file" &> /dev/null; then
            log_success "$filename"
            PASSED_TESTS=$((PASSED_TESTS + 1))
        else
            log_error "$filename"
            FAILED_TESTS=$((FAILED_TESTS + 1))
        fi
    done
}

# Test Lean proofs
test_lean() {
    log_section "Testing Lean Proofs"

    if ! check_prover "Lean" "lean"; then
        log_skip "Lean not installed"
        return
    fi

    local lean_dir="${PROOFS_DIR}/lean"
    if [ ! -d "$lean_dir" ]; then
        log_skip "No Lean proofs found"
        return
    fi

    # Lean uses lake for building, try that first
    if [ -f "$lean_dir/lakefile.lean" ]; then
        log_info "Building Lean project..."
        cd "$lean_dir"
        if lake build &> /dev/null; then
            log_success "Lean project build"
            TOTAL_TESTS=$((TOTAL_TESTS + 1))
            PASSED_TESTS=$((PASSED_TESTS + 1))
        else
            log_error "Lean project build"
            TOTAL_TESTS=$((TOTAL_TESTS + 1))
            FAILED_TESTS=$((FAILED_TESTS + 1))
        fi
        cd "$PROJECT_ROOT"
    else
        # Test individual files
        for file in "$lean_dir"/*.lean; do
            [ -f "$file" ] || continue
            [[ "$file" == *"lakefile.lean" ]] && continue
            TOTAL_TESTS=$((TOTAL_TESTS + 1))

            local filename=$(basename "$file")
            log_info "Testing $filename..."

            if lean "$file" &> /dev/null; then
                log_success "$filename"
                PASSED_TESTS=$((PASSED_TESTS + 1))
            else
                log_error "$filename"
                FAILED_TESTS=$((FAILED_TESTS + 1))
            fi
        done
    fi
}

# Test Isabelle proofs
test_isabelle() {
    log_section "Testing Isabelle Proofs"

    if ! check_prover "Isabelle" "isabelle"; then
        log_skip "Isabelle not installed"
        return
    fi

    local isabelle_dir="${PROOFS_DIR}/isabelle"
    if [ ! -d "$isabelle_dir" ]; then
        log_skip "No Isabelle proofs found"
        return
    fi

    for file in "$isabelle_dir"/*.thy; do
        [ -f "$file" ] || continue
        TOTAL_TESTS=$((TOTAL_TESTS + 1))

        local filename=$(basename "$file")
        log_info "Testing $filename..."

        if isabelle build -D "$isabelle_dir" &> /dev/null; then
            log_success "$filename"
            PASSED_TESTS=$((PASSED_TESTS + 1))
        else
            log_error "$filename"
            FAILED_TESTS=$((FAILED_TESTS + 1))
        fi
    done
}

# Test Z3 proofs
test_z3() {
    log_section "Testing Z3 Proofs"

    if ! check_prover "Z3" "z3"; then
        log_skip "Z3 not installed"
        return
    fi

    local z3_dir="${PROOFS_DIR}/z3"
    if [ ! -d "$z3_dir" ]; then
        log_skip "No Z3 proofs found"
        return
    fi

    for file in "$z3_dir"/*.smt2; do
        [ -f "$file" ] || continue
        TOTAL_TESTS=$((TOTAL_TESTS + 1))

        local filename=$(basename "$file")
        log_info "Testing $filename..."

        local output
        output=$(z3 "$file" 2>&1)

        if echo "$output" | grep -q "^sat\|^unsat"; then
            log_success "$filename"
            PASSED_TESTS=$((PASSED_TESTS + 1))
        else
            log_error "$filename"
            FAILED_TESTS=$((FAILED_TESTS + 1))
        fi
    done
}

# Test CVC5 proofs
test_cvc5() {
    log_section "Testing CVC5 Proofs"

    if ! check_prover "CVC5" "cvc5"; then
        log_skip "CVC5 not installed"
        return
    fi

    local cvc5_dir="${PROOFS_DIR}/cvc5"
    if [ ! -d "$cvc5_dir" ]; then
        log_skip "No CVC5 proofs found"
        return
    fi

    for file in "$cvc5_dir"/*.smt2; do
        [ -f "$file" ] || continue
        TOTAL_TESTS=$((TOTAL_TESTS + 1))

        local filename=$(basename "$file")
        log_info "Testing $filename..."

        local output
        output=$(cvc5 "$file" 2>&1)

        if echo "$output" | grep -q "^sat\|^unsat"; then
            log_success "$filename"
            PASSED_TESTS=$((PASSED_TESTS + 1))
        else
            log_error "$filename"
            FAILED_TESTS=$((FAILED_TESTS + 1))
        fi
    done
}

# Test Metamath proofs
test_metamath() {
    log_section "Testing Metamath Proofs"

    if ! check_prover "Metamath" "metamath"; then
        log_skip "Metamath not installed"
        return
    fi

    local metamath_dir="${PROOFS_DIR}/metamath"
    if [ ! -d "$metamath_dir" ]; then
        log_skip "No Metamath proofs found"
        return
    fi

    for file in "$metamath_dir"/*.mm; do
        [ -f "$file" ] || continue
        TOTAL_TESTS=$((TOTAL_TESTS + 1))

        local filename=$(basename "$file")
        log_info "Testing $filename..."

        # Metamath verification is done through the 'verify proof *' command
        if echo "read '$file'; verify proof *; exit" | metamath &> /dev/null; then
            log_success "$filename"
            PASSED_TESTS=$((PASSED_TESTS + 1))
        else
            log_error "$filename"
            FAILED_TESTS=$((FAILED_TESTS + 1))
        fi
    done
}

# Test Mizar proofs
test_mizar() {
    log_section "Testing Mizar Proofs"

    if ! check_prover "Mizar" "mizf"; then
        log_skip "Mizar not installed"
        return
    fi

    local mizar_dir="${PROOFS_DIR}/mizar"
    if [ ! -d "$mizar_dir" ]; then
        log_skip "No Mizar proofs found"
        return
    fi

    for file in "$mizar_dir"/*.miz; do
        [ -f "$file" ] || continue
        TOTAL_TESTS=$((TOTAL_TESTS + 1))

        local filename=$(basename "$file")
        log_info "Testing $filename..."

        if mizf "$file" &> /dev/null; then
            log_success "$filename"
            PASSED_TESTS=$((PASSED_TESTS + 1))
        else
            log_error "$filename"
            FAILED_TESTS=$((FAILED_TESTS + 1))
        fi
    done
}

# Print summary
print_summary() {
    log_section "Test Summary"

    echo "Total tests:  $TOTAL_TESTS"
    echo -e "${GREEN}Passed:       $PASSED_TESTS${NC}"
    echo -e "${RED}Failed:       $FAILED_TESTS${NC}"
    echo -e "${YELLOW}Skipped:      $SKIPPED_TESTS${NC}"

    if [ $TOTAL_TESTS -eq 0 ]; then
        echo ""
        echo -e "${YELLOW}No tests were run. Make sure theorem provers are installed.${NC}"
        exit 0
    fi

    local success_rate=0
    if [ $TOTAL_TESTS -gt 0 ]; then
        success_rate=$((PASSED_TESTS * 100 / TOTAL_TESTS))
    fi

    echo ""
    echo "Success rate: ${success_rate}%"

    if [ $FAILED_TESTS -gt 0 ]; then
        exit 1
    fi
}

# Main execution
main() {
    log_info "ECHIDNA Proof Validation Suite"
    log_info "Project root: $PROJECT_ROOT"
    log_info "Proofs directory: $PROOFS_DIR"
    echo ""

    # If a specific prover is requested, test only that one
    if [ $# -gt 0 ]; then
        case "$1" in
            agda)
                test_agda
                ;;
            coq)
                test_coq
                ;;
            lean)
                test_lean
                ;;
            isabelle)
                test_isabelle
                ;;
            z3)
                test_z3
                ;;
            cvc5)
                test_cvc5
                ;;
            metamath)
                test_metamath
                ;;
            mizar)
                test_mizar
                ;;
            *)
                echo "Unknown prover: $1"
                echo "Available: agda, coq, lean, isabelle, z3, cvc5, metamath, mizar"
                exit 1
                ;;
        esac
    else
        # Test all provers
        test_agda
        test_coq
        test_lean
        test_isabelle
        test_z3
        test_cvc5
        test_metamath
        test_mizar
    fi

    print_summary
}

# Run main
main "$@"
