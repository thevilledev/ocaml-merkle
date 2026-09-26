/-
  Conformance corpus: runs the Lean model on symbolic hashes and prints
  what it computes, for `formal/conformance/check.exe` to replay
  against the OCaml library on real SHA-256 hashes.

  A symbolic hash is a term: `L<i>` is the leaf hash of the entry
  "leaf-<i>", `E` the empty root, `J<k>` an unrelated hash, `(a b)` the
  node hash of `a` and `b`. Distinct terms are distinct hashes (barring
  a SHA-256 collision), so the model's verdicts on terms must be the
  library's verdicts on the hashes the terms denote.

  Lines (fields separated by spaces, a proof is `-` or terms joined by
  `,`):

  Usage: `conformance [MAX_SIZE] [fixed]`; `fixed` models the patched
  `verify_consistency` (thevilledev/ocaml-merkle#1, the library since).

      R n root                        Log.root_at n
      P i n proof                     Log.inclusion_proof ~index:i ~size:n
      Q m n proof                     Log.consistency_proof ~old_size:m ~new_size:n
      I root size index leaf proof v  verify_inclusion, v = 0 | 1
      C m old n new proof v           verify_consistency
-/
import Merkle

open Merkle

inductive T where
  | leaf (i : Nat)
  | empty
  | junk (k : Nat)
  | node (l r : T)
  deriving DecidableEq, Inhabited

def T.show : T → String
  | .leaf i => s!"L{i}"
  | .empty => "E"
  | .junk k => s!"J{k}"
  | .node l r => s!"({l.show} {r.show})"

def showProof : List T → String
  | [] => "-"
  | ps => ",".intercalate (ps.map T.show)

def Hn : T → T → T := T.node
def E : T := T.empty

def leaves : Nat → T := T.leaf

/-- The log holding `L0 .. L(n-1)`. -/
def logOf (n : Nat) : Log T := appendAll E Log.create ((List.range n).map T.leaf)

/-- A small linear congruential generator. -/
structure Rng where
  s : Nat

def Rng.next (r : Rng) : Nat × Rng :=
  let s := (r.s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  (s / 2 ^ 33, ⟨s⟩)

def Rng.below (r : Rng) (n : Nat) : Nat × Rng :=
  let (x, r) := r.next
  (if n = 0 then 0 else x % n, r)

def swapEnds (p : List T) : List T :=
  match p, p.getLast? with
  | a :: rest@(_ :: _), some z => z :: (rest.dropLast ++ [a])
  | _, _ => p

def setAt (p : List T) (j : Nat) (x : T) : List T := p.set j x

def damage : T → T
  | .leaf i => .junk (1000000 + i)
  | .junk k => .junk (k + 1)
  | .empty => .junk 999999
  | .node l r => .node r l

structure Out where
  lines : Array String := #[]
  deriving Inhabited

def Out.add (o : Out) (l : String) : Out := { o with lines := o.lines.push l }

def inclusionLine (o : Out) (root : T) (size index : Int) (leaf : T) (p : List T) : Out :=
  let v := verifyInclusion Hn root size index leaf p
  o.add s!"I {root.show} {size} {index} {leaf.show} {showProof p} {if v then 1 else 0}"

/-- `fixed`: model the patched `verify_consistency` (`Findings.lean`). -/
def consistencyLine (fixed : Bool) (o : Out) (m : Int) (r1 : T) (n : Int) (r2 : T) (p : List T) : Out :=
  let v := if fixed then verifyConsistencyFixed Hn E m r1 n r2 p else verifyConsistency Hn E m r1 n r2 p
  o.add s!"C {m} {r1.show} {n} {r2.show} {showProof p} {if v then 1 else 0}"

def rootAt (t : Log T) (n : Nat) : T := (t.rootAt Hn E n).getD E

def main (args : List String) : IO Unit := do
  let maxN := (args.head? >>= String.toNat?).getD 40
  let fixed := args.contains "fixed"
  let consistencyLine := consistencyLine fixed
  let t := logOf (maxN + 2)
  let mut o : Out := {}
  let mut rng : Rng := ⟨20260925⟩
  -- roots and proofs from the log model
  for n in List.range (maxN + 1) do
    o := o.add s!"R {n} {(rootAt t n).show}"
  for n in List.range (maxN + 1) do
    for i in List.range n do
      o := o.add s!"P {i} {n} {showProof ((t.inclusionProof Hn E i n).getD [])}"
    for m in List.range (n + 1) do
      o := o.add s!"Q {m} {n} {showProof ((t.consistencyProof Hn E m n).getD [])}"
  -- every subtree root, to draw random proof elements from
  let pool : Array T := Id.run do
    let mut a := #[E, T.junk 1, T.junk 2]
    for lo in List.range (maxN + 1) do
      for len in List.range (maxN + 2 - lo) do
        if len > 0 then a := a.push (mthA Hn E leaves lo (lo + len))
    return a
  -- inclusion queries
  for n in List.range (maxN + 1) do
    for i in List.range n do
      let root := rootAt t n
      let leaf := leaves i
      let p := (t.inclusionProof Hn E i n).getD []
      o := inclusionLine o root n i leaf p
      o := inclusionLine o root n i (damage leaf) p
      o := inclusionLine o (damage root) n i leaf p
      for d in [-2, -1, 1, 2] do
        o := inclusionLine o root n (i + d) leaf p
        o := inclusionLine o root (n + d) i leaf p
      o := inclusionLine o root (2 * n) i leaf p
      o := inclusionLine o root ((n + 1) / 2) i leaf p
      o := inclusionLine o root 0 i leaf p
      o := inclusionLine o root n n leaf p
      o := inclusionLine o root n (-(i : Int) - 1) leaf p
      o := inclusionLine o root (n + 2 ^ 40) i leaf p
      o := inclusionLine o root n i leaf p.dropLast
      o := inclusionLine o root n i leaf p.tail
      o := inclusionLine o root n i leaf (swapEnds p)
      o := inclusionLine o root n i leaf p.reverse
      o := inclusionLine o root n i leaf (p ++ [T.junk 7])
      o := inclusionLine o root n i leaf (T.junk 7 :: p)
      o := inclusionLine o root n i leaf (p ++ [root])
      o := inclusionLine o root n i leaf []
      o := inclusionLine o root n i root []
      for j in List.range p.length do
        o := inclusionLine o root n i leaf (setAt p j (damage (p.getD j E)))
      -- random proofs of plausible lengths from the subtree pool
      for _ in List.range 4 do
        let (len, r1) := rng.below (p.length + 2); rng := r1
        let mut q : List T := []
        for _ in List.range len do
          let (k, r2) := rng.below pool.size; rng := r2
          q := q ++ [pool.getD k E]
        o := inclusionLine o root n i leaf q
  -- consistency queries
  for n in List.range (maxN + 1) do
    for m in List.range (n + 1) do
      let r1 := rootAt t m
      let r2 := rootAt t n
      let p := (t.consistencyProof Hn E m n).getD []
      o := consistencyLine o m r1 n r2 p
      o := consistencyLine o m (damage r1) n r2 p
      o := consistencyLine o m r1 n (damage r2) p
      o := consistencyLine o m r2 n r1 p
      o := consistencyLine o n r2 m r1 p
      o := consistencyLine o m (T.junk 5) m (T.junk 5) []
      o := consistencyLine o m E m E []
      for d in [-2, -1, 1, 2] do
        o := consistencyLine o (m + d) r1 n r2 p
        o := consistencyLine o m r1 (n + d) r2 p
      o := consistencyLine o m r1 (2 * n) r2 p
      o := consistencyLine o (2 * m) r1 (2 * n) r2 p
      o := consistencyLine o m r1 (n + 2 ^ 40) r2 p
      o := consistencyLine o (-(m : Int) - 1) r1 n r2 p
      o := consistencyLine o m r1 n r2 []
      o := consistencyLine o m r1 n r2 (r1 :: p)
      o := consistencyLine o m r1 n r2 (p ++ [T.junk 9])
      o := consistencyLine o m r1 n r2 (p ++ [r2])
      o := consistencyLine o m r1 n r2 (T.junk 9 :: p)
      o := consistencyLine o m r1 n r2 p.dropLast
      o := consistencyLine o m r1 n r2 p.tail
      o := consistencyLine o m r1 n r2 (swapEnds p)
      for j in List.range p.length do
        o := consistencyLine o m r1 n r2 (setAt p j (damage (p.getD j E)))
      for _ in List.range 3 do
        let (len, r1') := rng.below (p.length + 2); rng := r1'
        let mut q : List T := []
        for _ in List.range len do
          let (k, r2') := rng.below pool.size; rng := r2'
          q := q ++ [pool.getD k E]
        o := consistencyLine o m r1 n r2 q
  let out ← IO.getStdout
  for l in o.lines do
    out.putStrLn l
