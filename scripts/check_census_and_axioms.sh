#!/usr/bin/env bash
# CI gate: (1) the literal `sorry` census is EXACTLY the seven frozen known-false
# documentation stubs; (2) the six headline theorems use only the standard axioms.
# Run from the repository root after `lake build`.
set -euo pipefail

echo "== Frozen-stub census =="
census=$(grep -rcE '^\s*sorry$' Graphon/*.lean | grep -v ':0$' | sort || true)
expected=$'Graphon/Lovasz.lean:2\nGraphon/MatrixDetermination.lean:3\nGraphon/Spectral.lean:2'
echo "$census"
if [ "$census" != "$expected" ]; then
  echo "FAIL: sorry census deviates from the seven documented frozen stubs." >&2
  echo "Expected:" >&2
  echo "$expected" >&2
  exit 1
fi

echo "== Headline axiom audit =="
out=$(lake env lean scripts/axiom_audit.lean)
echo "$out"
clean=$(echo "$out" | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" || true)
if [ "$clean" -ne 6 ]; then
  echo "FAIL: expected 6 standard-axiom-only headline theorems, found $clean." >&2
  exit 1
fi

echo "OK: census and axiom audit passed."
