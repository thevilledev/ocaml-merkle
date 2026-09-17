#!/usr/bin/env bash
# Differential test: this library against the Go reference implementation,
# github.com/transparency-dev/merkle. See README.md.
#
# Needs: dune (run under `opam exec --` if needed) and go.
# Tunables, all optional: SEED, LEAVES, EXHAUSTIVE, QUERIED, SAMPLES, OUT.
set -euo pipefail
cd "$(dirname "$0")"

OUT="${OUT:-_out}"
mkdir -p "$OUT"
OUT="$(cd "$OUT" && pwd)"

echo "== building"
(cd .. && dune build compat/ocaml/replay.exe)
(cd go && go build -o "$OUT/merkle-compat" .)

echo "== generating the corpus with transparency-dev/merkle"
"$OUT/merkle-compat" corpus "$OUT/corpus.txt"

echo "== replaying it against ocaml-merkle"
../_build/default/compat/ocaml/replay.exe "$OUT/corpus.txt"

echo "== checking that test/reference_vectors.ml is current"
"$OUT/merkle-compat" vectors | diff -u ../test/reference_vectors.ml -
echo "ok"
