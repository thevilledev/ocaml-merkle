/-
  Findings: documented contracts the code does not meet, each with a
  machine-checked counterexample, and the patched behaviour with its
  proof.
-/
import Merkle.Log
import Merkle.Hex

namespace Merkle

variable {α : Type} [DecidableEq α] (H : α → α → α) (e : α)

/-! ## Finding 1: `verify_consistency` from the empty tree to the empty tree

  `merkle.mli`: "The empty tree ([old_size = 0], [old_root = empty_root])
  is consistent with every tree via an empty proof ... from the empty
  tree, [old_root] must be {!empty_root}, where the Go verifier ignores
  it." `compat/README.md` gives the reason: "a caller holding some other
  'root of size 0' is holding something that is not a tree head".

  The equal-sizes branch runs first, so with `new_size = 0` too any
  `old_root` is accepted, as long as `new_root` repeats it.
-/

/-- The contract, as documented. -/
def EmptyTreeContract : Prop :=
  ∀ (oldRoot : α) (newSize : Int) (newRoot : α) (proof : List α),
    verifyConsistency H e 0 oldRoot newSize newRoot proof = true → oldRoot = e

theorem verifyConsistency_empty_accepts_any_root (x : α) :
    verifyConsistency H e 0 x 0 x [] = true := by
  simp [verifyConsistency]

/-- The code breaks the contract whenever there is any hash other than
    `empty_root`. -/
theorem emptyTreeContract_violated (x : α) (hx : x ≠ e) : ¬ EmptyTreeContract H e :=
  fun h => hx (h x 0 x [] (verifyConsistency_empty_accepts_any_root H e x))

/-- The patch (`src/merkle.ml`, fix branch):

      else if old_size = new_size then
        proof = [] && H.equal old_root new_root
        && (old_size > 0 || H.equal old_root empty_root) -/
def verifyConsistencyFixed (oldSize : Int) (oldRoot : α) (newSize : Int) (newRoot : α)
    (proof : List α) : Bool :=
  if oldSize < 0 ∨ newSize < oldSize then false
  else if oldSize = newSize then
    proof.isEmpty && oldRoot == newRoot && (decide (oldSize > 0) || oldRoot == e)
  else verifyConsistency H e oldSize oldRoot newSize newRoot proof

theorem fixed_meets_contract :
    ∀ (oldRoot : α) (newSize : Int) (newRoot : α) (proof : List α),
      verifyConsistencyFixed H e 0 oldRoot newSize newRoot proof = true → oldRoot = e := by
  intro oldRoot newSize newRoot proof h
  unfold verifyConsistencyFixed at h
  by_cases hg : (0 : Int) < 0 ∨ newSize < 0
  · rw [if_pos hg] at h; exact absurd h (by decide)
  rw [if_neg hg] at h
  by_cases hn : (0 : Int) = newSize
  · rw [if_pos hn] at h; simp at h; exact h.2
  · rw [if_neg hn] at h
    unfold verifyConsistency at h
    rw [if_neg hg, if_neg hn, if_pos rfl] at h
    simp at h; exact h.2

/-- The patch changes exactly one verdict: `(0, X) → (0, X)` with
    `X ≠ empty_root`, from `true` to `false`. -/
theorem fixed_eq_unless_empty_pair (oldSize : Int) (oldRoot : α) (newSize : Int) (newRoot : α)
    (proof : List α) (h : ¬ (oldSize = 0 ∧ newSize = 0 ∧ oldRoot ≠ e)) :
    verifyConsistencyFixed H e oldSize oldRoot newSize newRoot proof =
      verifyConsistency H e oldSize oldRoot newSize newRoot proof := by
  unfold verifyConsistencyFixed
  by_cases hg : oldSize < 0 ∨ newSize < oldSize
  · rw [if_pos hg, verifyConsistency_out_of_range H e _ _ _ _ _ hg]
  rw [if_neg hg]
  by_cases hs : oldSize = newSize
  · rw [if_pos hs]
    unfold verifyConsistency
    rw [if_neg hg, if_pos hs]
    by_cases h0 : oldSize > 0
    · simp [h0]
    · have : oldRoot = e := by
        exact Classical.byContradiction fun hne => h ⟨by omega, by omega, hne⟩
      subst this; simp
  · rw [if_neg hs]

/-- So every theorem about the verifier carries over. In particular the
    patched verifier is still complete ... -/
theorem fixed_complete (D : List α) (m : Nat) (hm : m ≤ D.length) :
    verifyConsistencyFixed H e m (mth H e (D.take m)) D.length (mth H e D)
      (consistencyProof H e m D) = true := by
  rw [fixed_eq_unless_empty_pair]
  · exact verifyConsistency_complete H e D m hm
  · rintro ⟨h0, hn, hne⟩
    apply hne
    have : m = 0 := by omega
    subst this
    unfold mth; simp

/-- ... and sound. -/
theorem fixed_sound (hinj : NodeInjective H) (D : List α) (oldSize : Int) (oldRoot : α)
    (proof : List α)
    (h : verifyConsistencyFixed H e oldSize oldRoot D.length (mth H e D) proof = true) :
    0 ≤ oldSize ∧ oldSize ≤ D.length ∧ oldRoot = mth H e (D.take oldSize.toNat) ∧
      proof = consistencyProof H e oldSize.toNat D := by
  by_cases hc : oldSize = 0 ∧ (D.length : Int) = 0 ∧ oldRoot ≠ e
  · exact absurd (fixed_meets_contract H e oldRoot _ _ _ (by rw [← hc.1]; exact h)) hc.2.2
  · rw [fixed_eq_unless_empty_pair H e _ _ _ _ _ hc] at h
    exact verifyConsistency_sound H e hinj D oldSize oldRoot proof h

/-! ## Finding 2: `hash_of_hex` and distinct strings

  `merkle.mli`: "here all of those are rejected, so distinct strings
  never parse to the same hash". Upper and lower case are both
  accepted, so they do: `Hex.hashOfHex_not_injective` is the
  counterexample, and `Hex.hashOfHex_same_iff` the true statement — two
  strings parse to the same hash exactly when they are equal up to
  letter case.
-/

example : Hex.hashOfHex 1 ['A', 'B'] = Hex.hashOfHex 1 ['a', 'b'] ∧
    (['A', 'B'] : List Char) ≠ ['a', 'b'] :=
  ⟨Hex.hashOfHex_not_injective.1, Hex.hashOfHex_not_injective.2.2⟩

end Merkle
