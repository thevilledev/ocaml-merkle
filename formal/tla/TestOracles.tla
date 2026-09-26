------------------------------ MODULE TestOracles ------------------------------
(***************************************************************************)
(* The independent oracles of test/test_merkle.ml, which the test suite   *)
(* trusts to judge the library: are they right?                           *)
(*                                                                         *)
(*  - frontier_root: roots by the incremental stack-of-perfect-subtrees   *)
(*    method; must be MTH;                                                *)
(*  - oracle_verify_inclusion / oracle_verify_consistency: RFC 6962 read  *)
(*    backwards by structural recursion; must agree with the RFC 9162     *)
(*    verifiers on every query (the "released" special cases: the oracle  *)
(*    copies them).                                                        *)
(***************************************************************************)
EXTENDS MerkleTree, TLC

CONSTANTS Alphabet, MaxN, MaxProofLen

Junk == <<"J">>
Leaves == {LeafHash(x) : x \in Alphabet}
Trees == UNION {[1..j -> Leaves] : j \in 0..MaxN}
Universe == {MTH(s) : s \in Trees \ {<<>>}} \cup {EmptyRoot, Junk}
Proofs == UNION {[1..j -> Universe] : j \in 0..MaxProofLen}

Reverse(s) == [i \in 1..Len(s) |-> s[Len(s) - i + 1]]

(* let rec push height h = function
     | (height', l) :: rest when height' = height ->
       push (height + 1) (M.node_hash l h) rest
     | stack -> (height, h) :: stack                                    *)
RECURSIVE Push(_, _, _)
Push(height, h, stack) ==
  IF stack /= <<>> /\ Head(stack)[1] = height
  THEN Push(height + 1, Node(Head(stack)[2], h), Tail(stack))
  ELSE <<<<height, h>>>> \o stack

RECURSIVE PushAll(_, _)
PushAll(stack, hs) == IF hs = <<>> THEN stack ELSE PushAll(Push(0, Head(hs), stack), Tail(hs))

RECURSIVE FoldDown(_, _)
FoldDown(acc, rest) == IF rest = <<>> THEN acc ELSE FoldDown(Node(Head(rest)[2], acc), Tail(rest))

FrontierRoot(hs) ==
  LET st == PushAll(<<>>, hs)
  IN IF st = <<>> THEN EmptyRoot ELSE FoldDown(Head(st)[2], Tail(st))

(* root_of_path ~index ~size ~leaf rev_path; "None" is <<>> , Some r is <<r>> *)
RECURSIVE RootOfPath(_, _, _, _)
RootOfPath(index, size, leaf, rev) ==
  IF size = 1 THEN (IF rev = <<>> THEN <<leaf>> ELSE <<>>)
  ELSE IF rev = <<>> THEN <<>>
  ELSE LET top == Head(rev)
           k == Split(size)
       IN IF index < k
          THEN LET o == RootOfPath(index, k, leaf, Tail(rev))
               IN IF o = <<>> THEN <<>> ELSE <<Node(o[1], top)>>
          ELSE LET o == RootOfPath(index - k, size - k, leaf, Tail(rev))
               IN IF o = <<>> THEN <<>> ELSE <<Node(top, o[1])>>

OracleVerifyInclusion(root, size, index, leaf, proof) ==
  /\ index >= 0 /\ index < size
  /\ LET o == RootOfPath(index, size, leaf, Reverse(proof)) IN o /= <<>> /\ o[1] = root

(* roots_of_subproof ~m ~n ~b ~old_root rev_proof; Some (o, nw) is <<o, nw>> *)
RECURSIVE RootsOfSubproof(_, _, _, _, _)
RootsOfSubproof(m, n, b, oldRoot, rev) ==
  IF m = n THEN
    IF b /\ rev = <<>> THEN <<oldRoot, oldRoot>>
    ELSE IF ~b /\ Len(rev) = 1 THEN <<rev[1], rev[1]>>
    ELSE <<>>
  ELSE IF rev = <<>> THEN <<>>
  ELSE LET top == Head(rev)
           k == Split(n)
       IN IF m <= k
          THEN LET o == RootsOfSubproof(m, k, b, oldRoot, Tail(rev))
               IN IF o = <<>> THEN <<>> ELSE <<o[1], Node(o[2], top)>>
          ELSE LET o == RootsOfSubproof(m - k, n - k, FALSE, oldRoot, Tail(rev))
               IN IF o = <<>> THEN <<>> ELSE <<Node(top, o[1]), Node(top, o[2])>>

OracleVerifyConsistency(m, r1, n, r2, proof) ==
  IF m < 0 \/ n < m THEN FALSE
  ELSE IF m = n THEN proof = <<>> /\ r1 = r2
  ELSE IF m = 0 THEN proof = <<>> /\ r1 = EmptyRoot
  ELSE LET o == RootsOfSubproof(m, n, TRUE, r1, Reverse(proof))
       IN o /= <<>> /\ o[1] = r1 /\ o[2] = r2

VARIABLE q
Init == q \in Trees
Next == UNCHANGED q
Spec == Init /\ [][Next]_q

FrontierIsMTH == FrontierRoot(q) = MTH(q)

InclusionOracleAgrees ==
  \A i \in -1..Len(q), x \in Leaves \cup {Junk}, p \in Proofs, r \in {MTH(q), Junk} :
     OracleVerifyInclusion(r, Len(q), i, x, p) = VerifyInclusion(r, Len(q), i, x, p)

ConsistencyOracleAgrees ==
  \A m \in -1..Len(q) + 1, r1 \in Universe, p \in Proofs :
     OracleVerifyConsistency(m, r1, Len(q), MTH(q), p) = VerifyConsistency(m, r1, Len(q), MTH(q), p)
=============================================================================
