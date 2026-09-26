------------------------------ MODULE MerkleTree ------------------------------
(***************************************************************************)
(* RFC 6962 trees and the RFC 9162 verifiers of src/merkle.ml, over        *)
(* symbolic hashes.                                                        *)
(*                                                                         *)
(* Hashes are tagged tuples: <<"L", x>> is the leaf hash of entry x,      *)
(* <<"E">> the empty root, <<"N", l, r>> node_hash l r. Distinct terms    *)
(* are distinct hashes: the model is collision free by construction, so   *)
(* a verifier that accepts a false claim here would accept it with any    *)
(* hash.                                                                   *)
(***************************************************************************)
EXTENDS Integers, Sequences

EmptyRoot == <<"E">>
LeafHash(x) == <<"L", x>>
Node(l, r) == <<"N", l, r>>

(* let split n = let k = ref 1 in while !k * 2 < n do k := !k * 2 done; !k *)
RECURSIVE SplitLoop(_, _)
SplitLoop(k, n) == IF k * 2 < n THEN SplitLoop(k * 2, n) ELSE k
Split(n) == SplitLoop(1, n)

(* OCaml: let is_pow2 n = n > 0 && n land (n - 1) = 0 *)
RECURSIVE IsPow2(_)
IsPow2(n) == n = 1 \/ (n > 1 /\ n % 2 = 0 /\ IsPow2(n \div 2))

Take(s, k) == SubSeq(s, 1, k)
Drop(s, k) == SubSeq(s, k + 1, Len(s))

(* MTH(D[n]), RFC 6962 section 2.1 *)
RECURSIVE MTH(_)
MTH(D) ==
  IF Len(D) = 0 THEN EmptyRoot
  ELSE IF Len(D) = 1 THEN D[1]
  ELSE LET k == Split(Len(D)) IN Node(MTH(Take(D, k)), MTH(Drop(D, k)))

(* PATH(m, D[n]), RFC 6962 section 2.1.1 *)
RECURSIVE Path(_, _)
Path(m, D) ==
  IF Len(D) <= 1 THEN <<>>
  ELSE LET k == Split(Len(D)) IN
       IF m < k THEN Path(m, Take(D, k)) \o <<MTH(Drop(D, k))>>
       ELSE Path(m - k, Drop(D, k)) \o <<MTH(Take(D, k))>>

(* SUBPROOF(m, D[n], b), RFC 6962 section 2.1.2 *)
RECURSIVE SubProof(_, _, _)
SubProof(m, D, b) ==
  IF m = Len(D) THEN (IF b THEN <<>> ELSE <<MTH(D)>>)
  ELSE LET k == Split(Len(D)) IN
       IF m <= k THEN SubProof(m, Take(D, k), b) \o <<MTH(Drop(D, k))>>
       ELSE SubProof(m - k, Drop(D, k), FALSE) \o <<MTH(Take(D, k))>>

(* Log.consistency_proof, after its argument checks *)
ConsProof(m, D) == IF m = Len(D) \/ m = 0 THEN <<>> ELSE SubProof(m, D, TRUE)

(***************************************************************************)
(* The verifiers. land 1 is % 2, lsr 1 is \div 2 (the operands are never  *)
(* negative). The List.iter loops are recursions over the proof; the ok   *)
(* flag becomes the first component of the result.                         *)
(***************************************************************************)

(* while not (fn land 1 = 1 || fn = 0) do fn := fn lsr 1; sn := sn lsr 1 done *)
RECURSIVE ShiftWhileEven(_, _)
ShiftWhileEven(fn, sn) ==
  IF fn % 2 = 1 \/ fn = 0 THEN <<fn, sn>> ELSE ShiftWhileEven(fn \div 2, sn \div 2)

(* the verify_inclusion loop body, over the rest of the proof *)
RECURSIVE IncLoop(_, _, _, _)
IncLoop(fn, sn, r, p) ==
  IF p = <<>> THEN <<TRUE, sn, r>>
  ELSE IF sn = 0 THEN <<FALSE, sn, r>>
  ELSE IF fn % 2 = 1 \/ fn = sn THEN
         LET fs == IF fn % 2 = 0 THEN ShiftWhileEven(fn, sn) ELSE <<fn, sn>>
         IN IncLoop(fs[1] \div 2, fs[2] \div 2, Node(Head(p), r), Tail(p))
       ELSE IncLoop(fn \div 2, sn \div 2, Node(r, Head(p)), Tail(p))

VerifyInclusion(root, size, index, leaf, proof) ==
  IF index < 0 \/ size < 1 \/ index >= size THEN FALSE
  ELSE LET res == IncLoop(index, size - 1, leaf, proof)
       IN res[1] /\ res[2] = 0 /\ res[3] = root

(* while fn land 1 = 1 do fn := fn lsr 1; sn := sn lsr 1 done *)
RECURSIVE StripOnes(_, _)
StripOnes(fn, sn) == IF fn % 2 = 1 THEN StripOnes(fn \div 2, sn \div 2) ELSE <<fn, sn>>

(* the verify_consistency loop body *)
RECURSIVE ConLoop(_, _, _, _, _)
ConLoop(fn, sn, fr, sr, p) ==
  IF p = <<>> THEN <<TRUE, sn, fr, sr>>
  ELSE IF sn = 0 THEN <<FALSE, sn, fr, sr>>
  ELSE IF fn % 2 = 1 \/ fn = sn THEN
         LET fs == IF fn % 2 = 0 THEN ShiftWhileEven(fn, sn) ELSE <<fn, sn>>
         IN ConLoop(fs[1] \div 2, fs[2] \div 2, Node(Head(p), fr), Node(Head(p), sr), Tail(p))
       ELSE ConLoop(fn \div 2, sn \div 2, fr, Node(sr, Head(p)), Tail(p))

(* 0 < old_size < new_size *)
ConCore(m, r1, n, r2, proof) ==
  LET p == IF IsPow2(m) THEN <<r1>> \o proof ELSE proof
  IN IF p = <<>> THEN FALSE
     ELSE LET fs == StripOnes(m - 1, n - 1)
              res == ConLoop(fs[1], fs[2], Head(p), Head(p), Tail(p))
          IN res[1] /\ res[2] = 0 /\ res[3] = r1 /\ res[4] = r2

(* verify_consistency as released (0.1.0) *)
VerifyConsistency(m, r1, n, r2, proof) ==
  IF m < 0 \/ n < m THEN FALSE
  ELSE IF m = n THEN proof = <<>> /\ r1 = r2
  ELSE IF m = 0 THEN proof = <<>> /\ r1 = EmptyRoot
  ELSE ConCore(m, r1, n, r2, proof)

(* with the fix: from the empty tree the old root must be H("") even
   when the new tree is empty too *)
VerifyConsistencyFixed(m, r1, n, r2, proof) ==
  IF m < 0 \/ n < m THEN FALSE
  ELSE IF m = n THEN proof = <<>> /\ r1 = r2 /\ (m > 0 \/ r1 = EmptyRoot)
  ELSE IF m = 0 THEN proof = <<>> /\ r1 = EmptyRoot
  ELSE ConCore(m, r1, n, r2, proof)

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s
=============================================================================
