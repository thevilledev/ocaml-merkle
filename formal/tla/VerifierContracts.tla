--------------------------- MODULE VerifierContracts ---------------------------
(***************************************************************************)
(* Bounded-exhaustive check of the verifiers' contracts: completeness,    *)
(* soundness against every proof up to MaxProofLen hashes drawn from      *)
(* every subtree root there is (plus junk), and the edge cases documented *)
(* in src/merkle.mli.                                                      *)
(*                                                                         *)
(* The spec has a single variable q, the tree a query is about, so that   *)
(* TLC reports a violated property together with the input violating it. *)
(***************************************************************************)
EXTENDS MerkleTree, FiniteSets, TLC

CONSTANTS Alphabet,     \* leaf data
          MaxN,         \* largest tree
          MaxProofLen,  \* longest adversarial proof
          Fixed         \* check the patched verify_consistency

Junk == <<"J">>
Leaves == {LeafHash(x) : x \in Alphabet}

Seqs(k) == UNION {[1..j -> Leaves] : j \in 0..k}
Trees == Seqs(MaxN)

(* every hash an adversary could usefully send: every subtree root, the
   empty root and one unrelated hash *)
Universe == {MTH(s) : s \in Trees \ {<<>>}} \cup {EmptyRoot, Junk}
Proofs == UNION {[1..j -> Universe] : j \in 0..MaxProofLen}

VC(m, r1, n, r2, p) ==
  IF Fixed THEN VerifyConsistencyFixed(m, r1, n, r2, p)
  ELSE VerifyConsistency(m, r1, n, r2, p)

VARIABLE q
Init == q \in Trees
Next == UNCHANGED q
Spec == Init /\ [][Next]_q

(* Every audit path Log produces verifies. *)
InclusionComplete ==
  \A i \in 0..Len(q) - 1 : VerifyInclusion(MTH(q), Len(q), i, q[i + 1], Path(i, q))

(* Against the true root and size: only the true leaf, only at its index,
   only with the honest audit path. Indices out of range are FALSE.

   The size has to be the true one too, as merkle.mli says ("[root] and
   [size] themselves must come from somewhere you trust"): with a size
   that is not the root's, a proof can be built from hashes that are
   leaf hashes where the verifier expects subtree roots. TLC's first
   counterexample for a size-agnostic version of this property was the
   root of <<a, a>> "proving" leaf a at index 2 of a 3-leaf tree with the
   proof <<a>>. The Go reference behaves the same; a signed tree head
   binds the two. *)
InclusionSound ==
  \A i \in -1..Len(q), x \in Leaves \cup {Junk}, p \in Proofs :
     VerifyInclusion(MTH(q), Len(q), i, x, p) =>
        /\ 0 <= i /\ i < Len(q)
        /\ x = q[i + 1]
        /\ p = Path(i, q)

(* Every consistency proof Log produces verifies. *)
ConsistencyComplete ==
  \A m \in 0..Len(q) : VC(m, MTH(Take(q, m)), Len(q), MTH(q), ConsProof(m, q))

(* Against the true new root, only the root of the true prefix, with the
   honest proof. *)
ConsistencySound ==
  \A m \in -1..Len(q) + 1, r1 \in Universe, p \in Proofs :
     VC(m, r1, Len(q), MTH(q), p) =>
        /\ 0 <= m /\ m <= Len(q)
        /\ r1 = MTH(Take(q, m))
        /\ p = ConsProof(m, q)

(* merkle.mli: "As in RFC 6962, the proof omits [old_root] when [old_size]
   is a power of two; a proof that spells it out is rejected." *)
ExplicitOldRootRejected ==
  \A m \in 1..Len(q) - 1 :
     IsPow2(m) => ~VC(m, MTH(Take(q, m)), Len(q), MTH(q), <<MTH(Take(q, m))>> \o ConsProof(m, q))

(* merkle.mli: "from the empty tree, [old_root] must be {!empty_root},
   where the Go verifier ignores it". Unconditional: whatever the rest of
   the query, an old root of size 0 other than H("") is not a tree head.
   (With a genuine new root the empty case is sound anyway: see
   ConsistencySound.) *)
EmptyTreeContract ==
  \A r1, r2 \in Universe, n \in {0, Len(q)}, p \in UNION {[1..j -> Universe] : j \in 0..1} :
     VC(0, r1, n, r2, p) => r1 = EmptyRoot
=============================================================================
