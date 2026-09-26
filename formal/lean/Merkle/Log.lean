/-
  `Log`: the in-memory log of `src/merkle.ml`, with its array storage,
  and the `lo`/`hi` index arithmetic of `mth`, `path` and `subproof`.

  The array is modelled as the list of all its cells (its capacity);
  reads are `get e`. Functions that raise `Invalid_argument` return
  `none`.
-/
import Merkle.Theorems

namespace Merkle

variable {α : Type} (H : α → α → α) (e : α)

/-! ## `mth`, `path`, `subproof` on an array range -/

/-- `leaves.(lo) .. leaves.(lo + n - 1)` -/
def seg (a : Nat → α) (lo : Nat) : Nat → List α
  | 0 => []
  | n + 1 => a lo :: seg a (lo + 1) n

theorem length_seg (a : Nat → α) (lo n : Nat) : (seg a lo n).length = n := by
  induction n generalizing lo <;> simp [seg, *]

theorem take_seg (a : Nat → α) (lo n k : Nat) (hk : k ≤ n) : (seg a lo n).take k = seg a lo k := by
  induction k generalizing lo n with
  | zero => simp [seg]
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n => simp [seg, ih (lo + 1) n (by omega)]

theorem drop_seg (a : Nat → α) (lo n k : Nat) (hk : k ≤ n) :
    (seg a lo n).drop k = seg a (lo + k) (n - k) := by
  induction k generalizing lo n with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      simp only [seg, List.drop_succ_cons]
      rw [ih (lo + 1) n (by omega)]
      congr 1 <;> omega

theorem get_seg (a : Nat → α) (lo n i : Nat) (hi : i < n) : get e (seg a lo n) i = a (lo + i) := by
  induction i generalizing lo n with
  | zero => cases n <;> simp_all [seg]
  | succ i ih =>
    cases n with
    | zero => omega
    | succ n => simp only [seg, get_cons_succ]; rw [ih _ _ (by omega)]; congr 1; omega

/-- OCaml:

      let rec mth leaves lo hi =
        let n = hi - lo in
        if n = 0 then empty_root
        else if n = 1 then leaves.(lo)
        else begin
          let k = split n in
          node_hash (mth leaves lo (lo + k)) (mth leaves (lo + k) hi)
        end -/
def mthA (a : Nat → α) (lo hi : Nat) : α :=
  if hi - lo = 0 then e
  else if hi - lo = 1 then a lo
  else H (mthA a lo (lo + split (hi - lo))) (mthA a (lo + split (hi - lo)) hi)
termination_by hi - lo
decreasing_by
  · have := split_lt (n := hi - lo) (by omega); omega
  · have := split_pos (n := hi - lo) (by omega); omega

/-- OCaml:

      let rec path leaves m lo hi =
        let n = hi - lo in
        if n <= 1 then []
        else begin
          let k = split n in
          if m < k then path leaves m lo (lo + k) @ [ mth leaves (lo + k) hi ]
          else path leaves (m - k) (lo + k) hi @ [ mth leaves lo (lo + k) ]
        end -/
def pathA (a : Nat → α) (m lo hi : Nat) : List α :=
  if hi - lo ≤ 1 then []
  else if m < split (hi - lo) then
    pathA a m lo (lo + split (hi - lo)) ++ [mthA H e a (lo + split (hi - lo)) hi]
  else pathA a (m - split (hi - lo)) (lo + split (hi - lo)) hi ++ [mthA H e a lo (lo + split (hi - lo))]
termination_by hi - lo
decreasing_by
  · have := split_lt (n := hi - lo) (by omega); omega
  · have := split_pos (n := hi - lo) (by omega); omega

/-- OCaml:

      let rec subproof leaves m lo hi known_root =
        let n = hi - lo in
        if m = n then if known_root then [] else [ mth leaves lo hi ]
        else begin
          let k = split n in
          if m <= k then
            subproof leaves m lo (lo + k) known_root @ [ mth leaves (lo + k) hi ]
          else
            subproof leaves (m - k) (lo + k) hi false @ [ mth leaves lo (lo + k) ]
        end

    The extra `n < 2` guard is unreachable for `0 < m ≤ n`, the only
    calls `consistency_proof` makes; it makes the model total where the
    OCaml would recurse forever (`m = 0`). -/
def subproofA (a : Nat → α) (m lo hi : Nat) (b : Bool) : List α :=
  if m = hi - lo then (if b then [] else [mthA H e a lo hi])
  else if hi - lo < 2 then []
  else if m ≤ split (hi - lo) then
    subproofA a m lo (lo + split (hi - lo)) b ++ [mthA H e a (lo + split (hi - lo)) hi]
  else subproofA a (m - split (hi - lo)) (lo + split (hi - lo)) hi false ++ [mthA H e a lo (lo + split (hi - lo))]
termination_by hi - lo
decreasing_by
  · have := split_lt (n := hi - lo) (by omega); omega
  · have := split_pos (n := hi - lo) (by omega); omega

theorem mthA_eq' (a : Nat → α) (n lo : Nat) : mthA H e a lo (lo + n) = mth H e (seg a lo n) := by
  induction n using Nat.strongRecOn generalizing lo with
  | _ n ih =>
    unfold mthA mth
    simp only [Nat.add_sub_cancel_left, length_seg]
    by_cases h0 : n = 0
    · subst h0; rfl
    by_cases h1 : n = 1
    · subst h1; rfl
    rw [if_neg h0, if_neg h1, dif_neg (by omega)]
    have hs := split_lt (n := n) (by omega)
    have hp := split_pos (n := n) (by omega)
    rw [ih _ hs lo, show lo + n = (lo + split n) + (n - split n) by omega, ih _ (by omega) _,
      take_seg _ _ _ _ (by omega), drop_seg _ _ _ _ (by omega)]

theorem mthA_eq (a : Nat → α) (lo hi : Nat) (h : lo ≤ hi) :
    mthA H e a lo hi = mth H e (seg a lo (hi - lo)) := by
  rw [← mthA_eq', Nat.add_sub_cancel' h]

theorem pathA_eq' (a : Nat → α) (n m lo : Nat) :
    pathA H e a m lo (lo + n) = path H e m (seg a lo n) := by
  induction n using Nat.strongRecOn generalizing m lo with
  | _ n ih =>
    unfold pathA path
    simp only [Nat.add_sub_cancel_left, length_seg]
    by_cases h1 : n ≤ 1
    · rw [if_pos h1, dif_pos (by omega)]
    rw [if_neg h1, dif_neg (by omega)]
    have hs := split_lt (n := n) (by omega)
    have hp := split_pos (n := n) (by omega)
    by_cases hm : m < split n
    · rw [if_pos hm, if_pos hm, ih _ hs, show lo + n = (lo + split n) + (n - split n) by omega,
        mthA_eq', take_seg _ _ _ _ (by omega), drop_seg _ _ _ _ (by omega)]
    · rw [if_neg hm, if_neg hm, show lo + n = (lo + split n) + (n - split n) by omega, ih _ (by omega),
        mthA_eq', take_seg _ _ _ _ (by omega), drop_seg _ _ _ _ (by omega)]

theorem subproofA_eq' (a : Nat → α) (n m lo : Nat) (b : Bool) :
    subproofA H e a m lo (lo + n) b = subproof H e m (seg a lo n) b := by
  induction n using Nat.strongRecOn generalizing m lo b with
  | _ n ih =>
    unfold subproofA subproof
    simp only [Nat.add_sub_cancel_left, length_seg]
    by_cases h1 : m = n
    · rw [if_pos h1, if_pos h1, mthA_eq']
    rw [if_neg h1, if_neg h1]
    by_cases h2 : n < 2
    · rw [if_pos h2, dif_pos h2]
    rw [if_neg h2, dif_neg h2]
    have hs := split_lt (n := n) (by omega)
    have hp := split_pos (n := n) (by omega)
    by_cases hm : m ≤ split n
    · rw [if_pos hm, if_pos hm, ih _ hs, show lo + n = (lo + split n) + (n - split n) by omega,
        mthA_eq', take_seg _ _ _ _ (by omega), drop_seg _ _ _ _ (by omega)]
    · rw [if_neg hm, if_neg hm, show lo + n = (lo + split n) + (n - split n) by omega, ih _ (by omega),
        mthA_eq', take_seg _ _ _ _ (by omega), drop_seg _ _ _ _ (by omega)]

/-! ## The log -/

/-- `type t = { mutable leaves : hash array; mutable len : int }`; the
    array is the list of all its cells. -/
structure Log (α : Type) where
  leaves : List α
  len : Nat

/-- `let create () = { leaves = [||]; len = 0 }` -/
def Log.create : Log α := ⟨[], 0⟩

/-- OCaml:

      let ensure t n =
        if n > Array.length t.leaves then begin
          let cap = max 16 (max n (2 * Array.length t.leaves)) in
          let a = Array.make cap empty_root in
          Array.blit t.leaves 0 a 0 t.len;
          t.leaves <- a
        end -/
def Log.ensure (t : Log α) (n : Nat) : Log α :=
  if n > t.leaves.length then
    let cap := max 16 (max n (2 * t.leaves.length))
    { t with leaves := t.leaves.take t.len ++ List.replicate (cap - t.len) e }
  else t

/-- OCaml:

      let append_leaf_hash t h =
        ensure t (t.len + 1);
        t.leaves.(t.len) <- h;
        t.len <- t.len + 1;
        t.len - 1

    Returns the new log and the result. -/
def Log.appendLeafHash (t : Log α) (h : α) : Log α × Nat :=
  let t := t.ensure e (t.len + 1)
  ({ leaves := t.leaves.set t.len h, len := t.len + 1 }, t.len)

/-- `let append t data = append_leaf_hash t (leaf_hash data)` -/
def Log.append (leafHash : β → α) (t : Log α) (data : β) : Log α × Nat :=
  t.appendLeafHash e (leafHash data)

def Log.size (t : Log α) : Nat := t.len

def Log.leaf (t : Log α) (i : Int) : Option α :=
  if i < 0 ∨ i ≥ t.len then none else some (get e t.leaves i.toNat)

def Log.rootAt (t : Log α) (n : Int) : Option α :=
  if n < 0 ∨ n > t.len then none else some (mthA H e (get e t.leaves) 0 n.toNat)

def Log.root (t : Log α) : α := mthA H e (get e t.leaves) 0 t.len

def Log.inclusionProof (t : Log α) (index size : Int) : Option (List α) :=
  if size < 1 ∨ size > t.len ∨ index < 0 ∨ index ≥ size then none
  else some (pathA H e (get e t.leaves) index.toNat 0 size.toNat)

def Log.consistencyProof (t : Log α) (oldSize newSize : Int) : Option (List α) :=
  if oldSize < 0 ∨ oldSize > newSize ∨ newSize > t.len then none
  else if oldSize = newSize ∨ oldSize = 0 then some []
  else some (subproofA H e (get e t.leaves) oldSize.toNat 0 newSize.toNat true)

/-! ## The abstraction: a log holds the leaves appended to it -/

/-- `t` holds exactly the leaf hashes `D`. -/
def Log.Holds (t : Log α) (D : List α) : Prop :=
  t.len = D.length ∧ D.length ≤ t.leaves.length ∧ ∀ i, i < D.length → get e t.leaves i = get e D i

theorem Log.create_holds : (Log.create : Log α).Holds e [] := by
  simp [Log.Holds, Log.create]

theorem get_set_eq : ∀ (l : List α) (i : Nat) (h : α), i < l.length → get e (l.set i h) i = h
  | [], _, _, hi => by simp at hi
  | _ :: _, 0, _, _ => rfl
  | _ :: l, i + 1, h, hi => by simp only [List.set_cons_succ, get_cons_succ]; exact get_set_eq l i h (by simp at hi; omega)

theorem get_set_ne : ∀ (l : List α) (i j : Nat) (h : α), j ≠ i → get e (l.set i h) j = get e l j
  | [], _, _, _, _ => by simp
  | _ :: _, 0, 0, _, hne => absurd rfl hne
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: l, i + 1, j + 1, h, hne => by
    simp only [List.set_cons_succ, get_cons_succ]; exact get_set_ne l i j h (by omega)

theorem Log.ensure_holds (t : Log α) (D : List α) (n : Nat) (ht : t.Holds e D) :
    (t.ensure e n).Holds e D ∧ n ≤ (t.ensure e n).leaves.length ∧ (t.ensure e n).len = t.len := by
  obtain ⟨h1, h2, h3⟩ := ht
  unfold Log.ensure
  by_cases hn : n > t.leaves.length
  · rw [if_pos hn]
    refine ⟨⟨h1, ?_, ?_⟩, ?_, rfl⟩
    · simp; omega
    · intro i hi
      rw [get_append_left e _ _ _ (by simp; omega), get_take e _ _ _ (by omega), h3 i hi]
    · simp; omega
  · rw [if_neg hn]; exact ⟨⟨h1, h2, h3⟩, by omega, rfl⟩

/-- Appending returns the next index, and the log then holds `D ++ [h]`:
    no leaf is lost when the array is reallocated. -/
theorem Log.appendLeafHash_holds (t : Log α) (D : List α) (h : α) (ht : t.Holds e D) :
    (t.appendLeafHash e h).2 = D.length ∧ (t.appendLeafHash e h).1.Holds e (D ++ [h]) := by
  obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := Log.ensure_holds e t D (t.len + 1) ht
  dsimp only [Log.appendLeafHash]
  refine ⟨by first | omega | (simp; omega), ?_, ?_, ?_⟩
  · first | omega | (simp; omega)
  · first | omega | (simp; omega)
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlast : i = D.length
    · subst hlast
      rw [show (t.ensure e (t.len + 1)).len = D.length by omega, get_set_eq e _ _ _ (by omega)]
      rw [show D.length = D.length + 0 by rfl, get_append_right]; rfl
    · rw [get_set_ne e _ _ _ _ (by omega), h3 i (by omega), get_append_left e _ _ _ (by omega)]

theorem ext_get : ∀ (l1 l2 : List α), l1.length = l2.length →
    (∀ i, i < l1.length → get e l1 i = get e l2 i) → l1 = l2
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l1, b :: l2, h, hg => by
    have h0 := hg 0 (by simp)
    simp only [get_cons_zero] at h0
    rw [h0, ext_get l1 l2 (by simpa using h) (fun i hi => by
      have := hg (i + 1) (by simp; omega); simpa using this)]

theorem seg_holds (t : Log α) (D : List α) (ht : t.Holds e D) (n : Nat) (hn : n ≤ D.length) :
    seg (get e t.leaves) 0 n = D.take n := by
  apply ext_get e
  · simp [length_seg]; omega
  · intro i hi
    rw [length_seg] at hi
    rw [get_seg e _ _ _ _ hi, Nat.zero_add, ht.2.2 i (by omega), get_take e _ _ _ hi]

theorem Log.rootAt_holds (t : Log α) (D : List α) (ht : t.Holds e D) (n : Nat) (hn : n ≤ D.length) :
    t.rootAt H e n = some (mth H e (D.take n)) := by
  unfold Log.rootAt
  rw [if_neg (by have := ht.1; omega), show (n : Int).toNat = 0 + n by omega, mthA_eq',
    seg_holds e t D ht n hn]

theorem Log.inclusionProof_holds (t : Log α) (D : List α) (ht : t.Holds e D) (i n : Nat)
    (hi : i < n) (hn : n ≤ D.length) :
    t.inclusionProof H e i n = some (path H e i (D.take n)) := by
  unfold Log.inclusionProof
  rw [if_neg (by have := ht.1; omega), show (n : Int).toNat = 0 + n by omega, pathA_eq',
    show (i : Int).toNat = i by omega, seg_holds e t D ht n hn]

theorem Log.consistencyProof_holds (t : Log α) (D : List α) (ht : t.Holds e D) (m n : Nat)
    (hm : m ≤ n) (hn : n ≤ D.length) :
    t.consistencyProof H e m n = some (Merkle.consistencyProof H e m (D.take n)) := by
  unfold Log.consistencyProof Merkle.consistencyProof
  rw [if_neg (by have := ht.1; omega)]
  have hl : (D.take n).length = n := by simp; omega
  by_cases hs : m = n ∨ m = 0
  · rw [if_pos (by omega), if_pos (by rw [hl]; exact hs)]
  · rw [if_neg (by omega), if_neg (by rw [hl]; exact hs), show (n : Int).toNat = 0 + n by omega,
      subproofA_eq', show (m : Int).toNat = m by omega, seg_holds e t D ht n hn]

/-! ## End to end -/

/-- A log built by any sequence of appends holds exactly the appended
    leaf hashes, and returned the index of each. -/
def appendAll (t : Log α) : List α → Log α
  | [] => t
  | h :: hs => appendAll (t.appendLeafHash e h).1 hs

theorem appendAll_holds (t : Log α) (D hs : List α) (ht : t.Holds e D) :
    (appendAll e t hs).Holds e (D ++ hs) := by
  induction hs generalizing t D with
  | nil => simpa [appendAll]
  | cons h hs ih =>
    have := (Log.appendLeafHash_holds e t D h ht).2
    simp only [appendAll]
    have := ih _ _ this
    simpa using this

/-- Every audit path a log produces verifies against the root it
    reports. -/
theorem log_inclusion_verifies [DecidableEq α] (hs : List α) (i n : Nat) (hi : i < n)
    (hn : n ≤ hs.length) :
    let t := appendAll e Log.create hs
    ∃ root proof leaf, t.rootAt H e n = some root ∧ t.inclusionProof H e i n = some proof ∧
      t.leaf e i = some leaf ∧ verifyInclusion H root n i leaf proof = true := by
  intro t
  have ht : t.Holds e hs := by simpa using appendAll_holds e Log.create [] hs (Log.create_holds e)
  refine ⟨_, _, get e hs i, Log.rootAt_holds H e t hs ht n hn,
    Log.inclusionProof_holds H e t hs ht i n hi hn, ?_, ?_⟩
  · unfold Log.leaf; rw [if_neg (by have := ht.1; omega), show (i : Int).toNat = i by omega,
      ht.2.2 i (by omega)]
  · have := verifyInclusion_complete H e (hs.take n) i (by simp; omega)
    rw [show (hs.take n).length = n by simp; omega, get_take e _ _ _ hi] at this
    exact this

/-- Every consistency proof a log produces verifies between the roots it
    reports. -/
theorem log_consistency_verifies [DecidableEq α] (hs : List α) (m n : Nat) (hm : m ≤ n)
    (hn : n ≤ hs.length) :
    let t := appendAll e Log.create hs
    ∃ r1 r2 proof, t.rootAt H e m = some r1 ∧ t.rootAt H e n = some r2 ∧
      t.consistencyProof H e m n = some proof ∧ verifyConsistency H e m r1 n r2 proof = true := by
  intro t
  have ht : t.Holds e hs := by simpa using appendAll_holds e Log.create [] hs (Log.create_holds e)
  refine ⟨_, _, _, Log.rootAt_holds H e t hs ht m (by omega), Log.rootAt_holds H e t hs ht n hn,
    Log.consistencyProof_holds H e t hs ht m n hm hn, ?_⟩
  have := verifyConsistency_complete H e (hs.take n) m (by simp; omega)
  rw [show (hs.take n).length = n by simp; omega, List.take_take, Nat.min_eq_left hm] at this
  exact this

end Merkle
