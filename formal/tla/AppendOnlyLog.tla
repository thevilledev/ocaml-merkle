---------------------------- MODULE AppendOnlyLog ----------------------------
(* The abstract log: a sequence of leaf hashes that only ever grows. *)
EXTENDS Naturals, Sequences

CONSTANTS Hashes, MaxLen

VARIABLE log

Init == log = <<>>
Push(h) == Len(log) < MaxLen /\ log' = Append(log, h)
Next == \E h \in Hashes : Push(h)
Spec == Init /\ [][Next]_log
=============================================================================
