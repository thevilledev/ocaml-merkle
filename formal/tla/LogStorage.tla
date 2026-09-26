------------------------------ MODULE LogStorage ------------------------------
(***************************************************************************)
(* Merkle.Log's storage, statement by statement:                          *)
(*                                                                         *)
(*   type t = { mutable leaves : hash array; mutable len : int }           *)
(*                                                                         *)
(*   let ensure t n =                                                      *)
(*     if n > Array.length t.leaves then begin                             *)
(*       let cap = max 16 (max n (2 * Array.length t.leaves)) in           *)
(*       let a = Array.make cap empty_root in                              *)
(*       Array.blit t.leaves 0 a 0 t.len;                                  *)
(*       t.leaves <- a                                                     *)
(*     end                                                                 *)
(*                                                                         *)
(*   let append_leaf_hash t h =                                            *)
(*     ensure t (t.len + 1);         (* pc = "ensure" *)                   *)
(*     t.leaves.(t.len) <- h;        (* pc = "store"  *)                   *)
(*     t.len <- t.len + 1;           (* pc = "incr"   *)                   *)
(*     t.len - 1                                                           *)
(*                                                                         *)
(* The array is a function from 0..Cap-1. MinCap is the OCaml 16, made a  *)
(* parameter so that small models reallocate several times. The spec     *)
(* refines AppendOnlyLog: every state, including those in the middle of  *)
(* an append, maps to the sequence of the first len cells.               *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS Hashes, MaxLen, MinCap, EmptyRoot

VARIABLES leaves,   \* the array
          len,
          pc,       \* where append_leaf_hash is
          pending,  \* the hash being appended
          ret,      \* the index the last append returned
          ghost     \* what has been appended, for checking only

vars == <<leaves, len, pc, pending, ret, ghost>>

Max(a, b) == IF a > b THEN a ELSE b
Size(a) == CHOOSE k \in 0..(2 * MaxLen + MinCap) : DOMAIN a = 0..(k - 1)

Init == /\ leaves = [i \in {} |-> EmptyRoot]
        /\ len = 0
        /\ pc = "idle"
        /\ pending = EmptyRoot
        /\ ret = -1
        /\ ghost = <<>>

Call(h) == /\ pc = "idle"
           /\ len < MaxLen
           /\ pending' = h
           /\ ghost' = Append(ghost, h)
           /\ pc' = "ensure"
           /\ UNCHANGED <<leaves, len, ret>>

Ensure == /\ pc = "ensure"
          /\ LET n == len + 1
                 cap == Max(MinCap, Max(n, 2 * Size(leaves)))
             IN leaves' = IF n > Size(leaves)
                          THEN [i \in 0..(cap - 1) |-> IF i < len THEN leaves[i] ELSE EmptyRoot]
                          ELSE leaves
          /\ pc' = "store"
          /\ UNCHANGED <<len, pending, ret, ghost>>

Store == /\ pc = "store"
         /\ len \in DOMAIN leaves          \* no Invalid_argument "index out of bounds"
         /\ leaves' = [leaves EXCEPT ![len] = pending]
         /\ pc' = "incr"
         /\ UNCHANGED <<len, pending, ret, ghost>>

Incr == /\ pc = "incr"
        /\ len' = len + 1
        /\ ret' = len
        /\ pc' = "idle"
        /\ UNCHANGED <<leaves, pending, ghost>>

Next == \/ \E h \in Hashes : Call(h)
        \/ Ensure \/ Store \/ Incr

Spec == Init /\ [][Next]_vars /\ WF_vars(Ensure \/ Store \/ Incr)

(* the array never runs out under a store *)
StoreInBounds == pc = "store" => len < Size(leaves)

(* the first len cells are what was appended, in order *)
Contents == \A i \in 0..(len - 1) : leaves[i] = ghost[i + 1]

(* append returns the index it stored at *)
Returns == pc = "idle" /\ len > 0 => ret = len - 1 /\ leaves[ret] = ghost[len]

(* the capacity stays within a factor of two of what is needed *)
Capacity == Size(leaves) = 0 \/ Size(leaves) <= Max(MinCap, 2 * (len + 1))

(* every call completes *)
Completes == pc /= "idle" ~> pc = "idle"

Abstract == INSTANCE AppendOnlyLog WITH log <- [i \in 1..len |-> leaves[i - 1]]
Refinement == Abstract!Spec
=============================================================================
