#!/usr/bin/env bash
# Re-run the formal verification of this library (see README.md):
#   1. the Lean proofs, and that they rest on no axiom beyond Lean's own;
#   2. model conformance: the Lean model against the OCaml library;
#   3. the TLA+ models, with TLC.
#
# Needs lake (the Lean toolchain named in lean/lean-toolchain; the proofs
# use Lean's core library only), dune, java, and TLA2TOOLS set to the path
# of tla2tools.jar (TLA+ 1.8). FULL=1 adds the slow 4-leaf protocol model.
set -euo pipefail
cd "$(dirname "$0")"
here=$(pwd)
mkdir -p _out

echo "== Lean: proofs"
(cd lean && lake build)
if grep -rnE '\b(sorry|admit|native_decide)\b|^axiom ' lean/Merkle lean/Merkle.lean; then
  echo "unproved or trusted steps in the Lean development" >&2
  exit 1
fi
(cd lean && lake env lean Axioms.lean) | tee _out/axioms.txt
# every axiom listed must be one of Lean's three standard ones
if grep -o "depends on axioms: \[.*\]" _out/axioms.txt | sed 's/.*\[//; s/\]//' | tr ',' '\n' |
    sed 's/^ *//' | grep -vxE "propext|Classical.choice|Quot.sound"; then
  echo "a theorem depends on an unexpected axiom" >&2
  exit 1
fi

echo "== model conformance: Lean model vs OCaml library"
# `fixed`: the library carries the verify_consistency fix of finding 1
(cd lean && lake build conformance && .lake/build/bin/conformance 40 fixed > "$here/_out/conformance.txt")
(cd .. && dune build ./formal/conformance/check.exe &&
  ./_build/default/formal/conformance/check.exe formal/_out/conformance.txt)

echo "== TLA+: TLC"
: "${TLA2TOOLS:?set TLA2TOOLS to the path of tla2tools.jar}"
tlc() {
  (cd tla && java -XX:+UseParallelGC -cp "$TLA2TOOLS" tlc2.TLC -workers auto -deadlock \
    -metadir "$here/_out/states" -config "$1.cfg" "$2" 2>&1) > "_out/$1.log" || true
}
pass() {
  tlc "$1" "$2"
  if grep -q "No error has been found" "_out/$1.log"; then echo "ok    $1"
  else echo "FAIL  $1 (see formal/_out/$1.log)"; exit 1; fi
}
expect_violation() {
  tlc "$1" "$2"
  if grep -q "Invariant $3 is violated" "_out/$1.log"; then echo "ok    $1 (violates $3, as expected)"
  else echo "FAIL  $1: expected $3 to be violated (see formal/_out/$1.log)"; exit 1; fi
}
pass VerifierContracts_released VerifierContracts
expect_violation VerifierContracts_empty_bug VerifierContracts EmptyTreeContract
pass VerifierContracts_fixed VerifierContracts
pass VerifierContracts_deep VerifierContracts
pass TestOracles TestOracles
pass TestOracles_frontier TestOracles
pass LogStorage_small LogStorage
pass LogStorage_ocaml LogStorage
pass Transparency Transparency
pass Transparency_fixed Transparency
if [ "${FULL:-0}" = 1 ]; then pass Transparency_4 Transparency; fi
echo "all checks passed"
