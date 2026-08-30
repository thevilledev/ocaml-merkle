(lang dune 3.17)
(name merkle)
(version 0.1.0)

(generate_opam_files true)

(source (github thevilledev/ocaml-merkle))
(license MIT)
(authors "Ville Vesilehto <ville@vesilehto.fi>")
(maintainers "Ville Vesilehto <ville@vesilehto.fi>")
(documentation "https://github.com/thevilledev/ocaml-merkle")

(package
 (name merkle)
 (synopsis "RFC 6962/9162 Merkle trees: inclusion and consistency proofs")
 (description
  "The Merkle tree construction used by Certificate Transparency and transparency logs generally (sigstore/Rekor, key transparency, binary transparency): domain-separated leaf/node hashing, audit paths, and the RFC 9162 verification algorithms for inclusion and consistency proofs. Stateless verifiers work against any log; an in-memory append-only log supports proof generation. Functorized over any digestif hash, instantiated for SHA-256. Verified against the Certificate Transparency reference test vectors.")
 (depends
  (ocaml (>= 4.14))
  (digestif (>= 1.0.0))
  (alcotest :with-test)
  (qcheck-core :with-test)
  (qcheck-alcotest :with-test))
 (tags (merkle "certificate transparency" rfc6962 rfc9162 "transparency log" "org:thevilledev")))
