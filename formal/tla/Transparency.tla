----------------------------- MODULE Transparency -----------------------------
(***************************************************************************)
(* What the verifiers are for: a log that may lie, an auditor that        *)
(* accepts a new tree head only with a consistency proof from the last    *)
(* one, and clients that accept an entry only with an inclusion proof     *)
(* against the auditor's head.                                             *)
(*                                                                         *)
(* The log may rewrite its history at any time and may send any proof     *)
(* made of up to MaxProofLen hashes (MaxClaimLen for inclusion proofs)  *)
(* it could know (every subtree root of                                  *)
(* every tree, the empty root, junk). Tree heads are genuine: the root   *)
(* is the root of what the log holds, as a signature would guarantee.    *)
(* Hashes are collision-free terms (MerkleTree).                          *)
(***************************************************************************)
EXTENDS MerkleTree, TLC

CONSTANTS Alphabet, MaxN, MaxProofLen, MaxClaimLen, Fixed

Junk == <<"J">>
Leaves == {LeafHash(x) : x \in Alphabet}
Trees == UNION {[1..j -> Leaves] : j \in 0..MaxN}
Universe == {MTH(s) : s \in Trees \ {<<>>}} \cup {EmptyRoot, Junk}
Proofs == UNION {[1..j -> Universe] : j \in 0..MaxProofLen}
ClaimProofs == UNION {[1..j -> Universe] : j \in 0..MaxClaimLen}

VC(m, r1, n, r2, p) ==
  IF Fixed THEN VerifyConsistencyFixed(m, r1, n, r2, p)
  ELSE VerifyConsistency(m, r1, n, r2, p)

VARIABLES
  served,        \* the leaves the log currently serves
  forked,        \* ghost: the log has rewritten history at least once
  head,          \* the auditor's latest accepted head: [size, root, tree (ghost)]
  history,       \* ghost: the trees behind every head the auditor accepted
  honestReject,  \* ghost: the auditor rejected an honest log's honest proof
  fooled         \* ghost: a client accepted an entry that is not in the tree

vars == <<served, forked, head, history, honestReject, fooled>>

TreeHead(s) == [size |-> Len(s), root |-> MTH(s), tree |-> s]

Init == /\ served = <<>>
        /\ forked = FALSE
        /\ head = TreeHead(<<>>)
        /\ history = <<<<>>>>
        /\ honestReject = FALSE
        /\ fooled = FALSE

(* an honest append *)
Grow(x) == /\ Len(served) < MaxN
             /\ served' = Append(served, x)
             /\ UNCHANGED <<forked, head, history, honestReject, fooled>>

(* the log replaces its contents with anything at all *)
Rewrite(s) == /\ served' = s
              /\ forked' = (forked \/ ~IsPrefix(served, s))
              /\ UNCHANGED <<head, history, honestReject, fooled>>

(* Log.consistency_proof from the auditor's head, when there is one (it
   raises Invalid_argument once a rewrite has shrunk the log) *)
HonestProofs == IF head.size <= Len(served) THEN {ConsProof(head.size, served)} ELSE {}

(* the log publishes its current head with proof p; the auditor checks it *)
Publish(p) ==
  LET new == TreeHead(served)
      ok == VC(head.size, head.root, new.size, new.root, p)
  IN /\ head' = IF ok THEN new ELSE head
     /\ history' = IF ok /\ new.tree /= head.tree THEN Append(history, new.tree) ELSE history
     /\ honestReject' = (honestReject \/ (~forked /\ p \in HonestProofs /\ ~ok))
     /\ UNCHANGED <<served, forked, fooled>>

(* the log claims entry x is at index i of the auditor's head *)
Claim(i, x, p) ==
  /\ fooled' = (fooled \/ (VerifyInclusion(head.root, head.size, i, x, p)
                           /\ ~(0 <= i /\ i < Len(head.tree) /\ head.tree[i + 1] = x)))
  /\ UNCHANGED <<served, forked, head, history, honestReject>>

Next == \/ \E x \in Leaves : Grow(x)
        \/ \E s \in Trees : Rewrite(s)
        \/ \E p \in Proofs \cup HonestProofs : Publish(p)
        \/ \E i \in -1..MaxN, x \in Leaves, p \in ClaimProofs : Claim(i, x, p)

Spec == Init /\ [][Next]_vars

(* Every head the auditor ever accepted extends the one before: a log    *)
(* that rewrites its history cannot get the rewrite past the auditor.    *)
AuditorSafety == \A i \in 1..Len(history) - 1 : IsPrefix(history[i], history[i + 1])

(* No client ever accepts an entry that is not where the log said. *)
ClientSafety == ~fooled

(* An honest log's honest proof is never rejected. *)
HonestLogAccepted == ~honestReject

(* The auditor's head is always the head of a tree the log once served. *)
HeadGenuine == head.root = MTH(head.tree) /\ head.size = Len(head.tree)
=============================================================================
