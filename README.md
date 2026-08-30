# ocaml-merkle

[![CI](https://github.com/thevilledev/ocaml-merkle/actions/workflows/ci.yml/badge.svg)](https://github.com/thevilledev/ocaml-merkle/actions/workflows/ci.yml)

RFC 6962 / RFC 9162 Merkle trees for OCaml — the construction behind
Certificate Transparency, sigstore/Rekor and transparency logs
generally:

- Domain-separated hashing (`H(0x00 ‖ leaf)`, `H(0x01 ‖ l ‖ r)`)
- **Stateless proof verification** implementing the RFC 9162 algorithms:
  `verify_inclusion` (§2.1.3.2) and `verify_consistency` (§2.1.4.2) —
  usable against proofs from any conformant log (CT
  `get-proof-by-hash`, Rekor inclusion proofs, ...)
- An in-memory append-only `Log` producing audit paths and consistency
  proofs
- Functorized over any [`digestif`](https://github.com/mirage/digestif)
  hash (`Merkle.Make`), instantiated as `Merkle.SHA256` (the RFC 6962
  default)
- Verified against the Certificate Transparency reference test vectors
  (incremental roots, inclusion paths, consistency proofs), with
  exhaustive tamper-detection tests on top

## Install

```sh
opam install merkle         # once released
opam pin add merkle https://github.com/thevilledev/ocaml-merkle.git
```

## Usage

### Verifying a log's proof (the common consumer case)

```ocaml
module M = Merkle.SHA256

(* Data from the log's API responses: *)
let root = M.hash_of_hex sth_root_hash          (* signed tree head *)
let proof = List.map M.hash_of_raw audit_path   (* proof hashes *)

let ok =
  M.verify_inclusion
    ~root ~size:tree_size ~index:leaf_index
    ~leaf:(M.leaf_hash entry_bytes)
    ~proof

(* Append-only check between two signed tree heads: *)
let still_append_only =
  M.verify_consistency
    ~old_size ~old_root ~new_size ~new_root
    ~proof:consistency_hashes
```

### Producing proofs

```ocaml
let log = M.Log.create () in
List.iter (fun e -> ignore (M.Log.append log e)) entries;

let root = M.Log.root log in
let proof = M.Log.inclusion_proof log ~index:2 ~size:(M.Log.size log) in
assert (M.verify_inclusion ~root ~size:(M.Log.size log) ~index:2
          ~leaf:(M.Log.leaf log 2) ~proof)
```

`Log` stores one hash per leaf and recomputes roots/proofs on demand
(O(n) time, O(log n) stack) — simple and predictable for logs up to
millions of entries. Cached subtree hashing (compact ranges) is future
work.

### Other hash algorithms

```ocaml
module M512 = Merkle.Make (Digestif.SHA512)
```

## References

- [RFC 6962](https://www.rfc-editor.org/rfc/rfc6962) — Certificate
  Transparency (tree definition, §2.1)
- [RFC 9162](https://www.rfc-editor.org/rfc/rfc9162) — CT v2
  (verification algorithms, §2.1.3.2 and §2.1.4.2)
- [transparency-dev/merkle](https://github.com/transparency-dev/merkle) —
  the Go reference this library is vector-compatible with

## License

MIT — see [LICENSE](LICENSE).
