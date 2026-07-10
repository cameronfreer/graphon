#!/usr/bin/env bash
# Thin wrapper for CI: see scripts/check_census_and_axioms.py for the policy
# (declaration-name allowlist census + subset-of-allowed-axioms audit).
set -euo pipefail
exec python3 scripts/check_census_and_axioms.py
