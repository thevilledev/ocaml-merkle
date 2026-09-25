# Unreleased

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
