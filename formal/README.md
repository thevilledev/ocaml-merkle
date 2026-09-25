# Formal verification

This directory verifies the library formally, in two complementary ways:

- **Lean 4** proofs of the algorithms for *all* inputs: every tree size,
  every index, every proof. The proofs use Lean's core library only.
- **TLA+** models checked exhaustively by TLC, up to a bound. They
  cover the verifiers against every proof an adversary could assemble,
  `Log`'s mutable storage at each intermediate step of an append, and the
  protocol the verifiers exist for: an auditor and clients against a log
  that lies.

A **conformance check** replays the executable Lean model against the
OCaml library. The model is a hand translation, and this is what ties it
to the code.

Two findings came out of this work. Each is fixed on its own branch
(see [Findings](#findings)).

## What is proved (Lean, `lean/`)

The model transcribes `src/merkle.ml` statement by statement, and the OCaml
it models is quoted next to each definition. Hashes are an arbitrary type
with an arbitrary node-hash function `H`. Sizes and indices are `Int`,
like OCaml's `int`. `land 1` and `lsr 1` are `&&& 1` and `>>> 1`.

| Theorem | Statement |
|---|---|
| `mth_eq_rootLevels`, `path_eq_pathLevel`, `subproof_eq_conLevel` (`Tree.lean`, `Subproof.lean`) | RFC 6962's top-down MTH, PATH and SUBPROOF describe the same tree and proofs as the bottom-up, level-by-level walk the RFC 9162 verifiers do. |
| `verifyInclusion_complete` (`Theorems.lean`) | Every audit path verifies against the root. |
| `verifyInclusion_sound` | If `H` is injective on child pairs, a proof that verifies against the true root and size of `D` has an index in range, the leaf is `D[index]`, and the proof *is* `PATH(index, D)`: proofs are unique. |
| `verifyConsistency_complete` | Every consistency proof verifies, for every `0 ≤ m ≤ n`. |
| `verifyConsistency_sound` | Under the same assumption, a proof that verifies against the true new root has `0 ≤ old_size ≤ new_size`, the old root is `MTH(D[0:old_size])`, and the proof is the one `Log` produces. |
| `verifyInclusion_out_of_range`, `verifyConsistency_out_of_range`, `verifyConsistency_rejects_explicit_old_root`, `verifyConsistency_equal_sizes`, `verifyConsistency_from_empty` | The documented guards and special cases. |
| `mthA_eq'`, `pathA_eq'`, `subproofA_eq'` (`Log.lean`) | The `lo`/`hi` index arithmetic over the array computes the RFC functions on the slice. |
| `Log.appendLeafHash_holds`, `appendAll_holds` | `append` returns the next index, and no leaf is lost when `ensure` reallocates and blits. |
| `log_inclusion_verifies`, `log_consistency_verifies` | End to end: for any sequence of appends, every proof `Log` returns verifies against the roots it reports. |
| `Hex.hashOfHex_eq` (`Hex.lean`, with digestif's `of_hex` modelled too) | `hash_of_hex` accepts exactly `2 * hash_size` hex digits, in either case, and decodes them in pairs. |
| `Hex.hashOfHex_toHex`, `Hex.hashOfHex_same_iff` | Round trip; two strings parse to the same hash exactly when they agree up to letter case. |
| `Hashing.leafInput_ne_nodeInput`, `Hashing.nodeInput_injective`, `Hashing.collision_of_not_nodeInjective` (`Hashing.lean`) | The byte strings fed to SHA-256 are domain-separated and unambiguous, so the soundness assumption fails only if a SHA-256 collision is found. |
| `Findings.lean` | Both findings: the counterexamples, and the patched behaviour with soundness and completeness carried over. |

`split` is modelled over `Nat`. The OCaml loop's `!k * 2` could only
overflow for `n > 2^61`, and `split` only sees array ranges, which are far
smaller than that.

`lean/Axioms.lean` prints what each main theorem rests on: only
`propext`, `Quot.sound` and `Classical.choice`. There is no `sorry`, no
`native_decide`, and no added axiom.

## What is model-checked (TLA+, `tla/`)

`MerkleTree.tla` transcribes the verifiers over symbolic hashes: tagged
terms, collision-free by construction.

| Model | Checks | Bound |
|---|---|---|
| `VerifierContracts` | Completeness. Soundness against every proof of up to 3–4 hashes drawn from every subtree root, the empty root and junk. The documented edge cases. | Trees up to 3 leaves over 2 values; up to 7 leaves over 1 value. |
| `TestOracles` | The test suite's own oracles are right: the frontier root is MTH, and `oracle_verify_*` agree with the verifiers on every query. | Frontier root up to 9 leaves (1023 trees); oracles up to 3 leaves. |
| `LogStorage` | `Log`'s array, `ensure`/`blit` and `append_leaf_hash`, one statement per step. It refines `AppendOnlyLog` at every step, stores never go out of bounds, append returns its index, and every append completes. | Up to 17 leaves with the real minimum capacity of 16; up to 9 with capacity 2, which reallocates four times. |
| `Transparency` | A log that can rewrite its history and send any proof, an auditor chaining tree heads by consistency proofs, and clients checking inclusion. The auditor's accepted heads always extend each other, no client is ever fooled, and an honest log is never rejected. | Trees up to 3 leaves with proofs up to 3 hashes: 35 million transitions. Trees up to 4 leaves in `Transparency_4.cfg`: 262 million transitions, about 20 minutes. |

The checks are not vacuous. Planted bugs were caught: dropping the final
`sn = 0` test fools clients, dropping the old-root comparison lets a
rewritten history past the auditor (this needs the 4-leaf bound), and
blitting one cell too few loses a leaf. The mutation runs are not
committed.

TLC also records one out-of-contract behaviour. With a size that is not
the root's own, a proof can reuse leaf hashes where the verifier expects
subtree roots. For example, the root of `<<a, a>>` "proves" leaf `a` at
index 2 of a 3-leaf tree. This is inherent to RFC 9162 (the Go reference
does the same). It is why the interface requires `root` and `size` to come
together from a trusted tree head, and the soundness theorems assume they
do.

## Model conformance (`lean/Conformance.lean`, `conformance/`)

The Lean model runs as a program on symbolic hashes and writes about
60 000 checks: roots, audit paths, consistency proofs, and verdicts on
honest and damaged proofs. `conformance/check.exe` replays them against
the library on the SHA-256 hashes the symbols denote. Every root and proof
must be identical, and every verdict the same. They are.

## Findings

1. **`verify_consistency` accepts any old root from the empty tree to the
   empty tree.** The interface says that "from the empty tree, `old_root`
   must be `empty_root`". The equal-sizes branch runs first, though, so
   `verify_consistency ~old_size:0 ~old_root:x ~new_size:0 ~new_root:x
   ~proof:[]` is `true` for every `x`.
   - Lean: `emptyTreeContract_violated`.
   - TLC: `VerifierContracts_empty_bug.cfg`.
   - The Go differential test could not notice. Go accepts these queries,
     and its corpus never asked them.
   - Fixed on branch `fix/consistency-empty-tree-root`, which also extends
     the Go corpus. The patch is proved sound and complete in Lean
     (`fixed_sound`, `fixed_complete`, `fixed_meets_contract`) and passes
     every TLC model.
   - The fix branch's code agrees with the patched model on every
     conformance check (`conformance 40 fixed`). Against the released
     model it differs on exactly the 41 `(0, x) → (0, x)` queries in the
     corpus.
2. **`hash_of_hex` is not injective, as its interface claimed.** The
   `.mli` said that "distinct strings never parse to the same hash", but
   upper and lower case parse alike (Lean: `Hex.hashOfHex_not_injective`).
   The true statement is proved (`Hex.hashOfHex_same_iff`). The
   documentation is corrected on branch `fix/hash-of-hex-doc`.

Nothing else was found. The RFC 9162 loops, the RFC 6962 proof generation,
the array storage and the hex validation are correct as specified.

## Running it

```sh
formal/check.sh            # Lean, conformance, TLC (a few minutes)
FULL=1 formal/check.sh     # also the 4-leaf protocol model (longer)
```

This needs:

- `lake`, for the Lean version in `lean/lean-toolchain`;
- `dune` with this library's dependencies;
- `java`;
- `TLA2TOOLS` set to the path of `tla2tools.jar` (TLA+ 1.8).
