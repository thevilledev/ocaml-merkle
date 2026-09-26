# Unreleased

- `verify_consistency` no longer accepts an old root other than the
  empty tree's, `H("")`, when both sizes are 0. The documented rule —
  from the empty tree, `old_root` must be `empty_root` — was enforced
  only when the new tree was non-empty: `(0, X) -> (0, X)` verified for
  any `X`. Found by formal verification of the documented contract.
- The differential test could not catch this. The Go reference accepts
  any old root of size 0, so on these queries the two agreed. It now
  checks the empty-tree rule on its own, whatever Go's verdict, and its
  corpus includes equal sizes with equal roots that are not the tree's.
  Against release 0.1.0 it reports this bug 42 times.
- Documentation: `hash_of_hex` is not injective, as its interface
  claimed ("distinct strings never parse to the same hash"): it accepts
  either case, so strings differing in letter case alone parse to the
  same hash. The interface now says so, and that `hash_to_hex` gives
  back the input in lowercase. Found by formal verification.

# 0.1.0 (2026-09-17)

- Initial release.
- RFC 6962 hashing, audit paths and consistency proofs; RFC 9162
  stateless verifiers, which return `false` rather than raise on any
  malformed query.
- Functorized over digestif hashes; `Merkle.SHA256` provided.
- `hash_of_hex` accepts exactly `2 * hash_size` hexadecimal digits.
  Unlike digestif's own parser it rejects whitespace, short input
  (which digestif zero-pads) and long input (which digestif truncates).
- Verified against the Certificate Transparency reference test vectors,
  and differentially tested against the Go reference implementation,
  transparency-dev/merkle: identical roots and proofs, and the same
  verdict on about 128 000 honest and damaged proofs (`compat/`).
- Requires OCaml 4.14, Dune 3.14 and digestif 1.0.0 or later; each lower
  bound is tested in CI.
