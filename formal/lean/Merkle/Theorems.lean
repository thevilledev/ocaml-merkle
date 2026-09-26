/-
  The main results, about the verifiers exactly as `src/merkle.ml`
  exposes them.

  * Completeness: every proof `Log` produces verifies.
  * Soundness: if a proof verifies against the true root of a list of
    leaf hashes `D`, and the node hash is injective (no collisions have
    been found), then the claim is true — the leaf is `D[index]`, the
    old root is the root of the prefix — and moreover the proof is the
    one `Log` produces: proofs are unique.
  * Totality: out-of-range sizes and indices are `false`.
-/
import Merkle.Verify

namespace Merkle

variable {α : Type} [DecidableEq α] (H : α → α → α) (e : α)

/-- `Log.consistency_proof` (after its argument checks). -/
def consistencyProof (m : Nat) (D : List α) : List α :=
  if m = D.length ∨ m = 0 then [] else subproof H e m D true

/-! ## Glue between the OCaml-shaped verdicts and `incRes`/`conRes` -/

theorem incVerdict_iff (s : Nat × Nat × α) (ps : List α) (root : α) :
    incVerdict root (incFold H s ps) = true ↔ incRes H s ps = some root := by
  unfold incRes
  rcases incFold H s ps with _ | ⟨a, sn, r⟩
  · simp [incVerdict]
  · by_cases h : sn = 0 <;> simp [incVerdict, h]

theorem conVerdict_iff (s : Nat × Nat × α × α) (ps : List α) (r1 r2 : α) :
    conVerdict r1 r2 (conFold H s ps) = true ↔ conRes H s ps = some (r1, r2) := by
  unfold conRes
  rcases conFold H s ps with _ | ⟨a, sn, fr, sr⟩
  · simp [conVerdict]
  · by_cases h : sn = 0 <;> simp [conVerdict, h, Bool.and_assoc]

theorem mth_nil : mth H e [] = e := by unfold mth; simp

theorem stripNum_stripL (x : Nat) (L : List α) (hL : 1 ≤ L.length) :
    stripNum x (L.length - 1) = ((stripL H x L).1, (stripL H x L).2.length - 1) := by
  induction x using Nat.strongRecOn generalizing L with
  | _ x ih =>
    rw [stripNum_eq]
    by_cases h : x % 2 = 1
    · rw [if_pos h, stripL_odd H x L h,
        show (L.length - 1) / 2 = (levelUp H L).length - 1 by rw [length_levelUp]; omega]
      exact ih _ (by omega) _ (by rw [length_levelUp]; omega)
    · rw [if_neg h, stripL_even H x L h]

/-! ## Inclusion -/

theorem verifyInclusion_out_of_range (root : α) (size index : Int) (leaf : α) (proof : List α)
    (h : index < 0 ∨ size < 1 ∨ index ≥ size) :
    verifyInclusion H root size index leaf proof = false := by
  unfold verifyInclusion; rw [if_pos h]

/-- Completeness: the audit path `Log.inclusion_proof` returns verifies. -/
theorem verifyInclusion_complete (D : List α) (i : Nat) (hi : i < D.length) :
    verifyInclusion H (mth H e D) D.length i (get e D i) (path H e i D) = true := by
  unfold verifyInclusion
  rw [if_neg (by omega), show (i : Int).toNat = i by omega,
    show ((D.length : Int) - 1).toNat = D.length - 1 by omega, incVerdict_iff,
    path_eq_pathLevel H e i D hi, mth_eq_rootLevels]
  exact incRes_complete H e D i hi

/-- Soundness: against the true root of `D`, only `D[index]` verifies,
    and only with the honest audit path. -/
theorem verifyInclusion_sound (hinj : NodeInjective H) (D : List α) (index : Int) (leaf : α)
    (proof : List α) (h : verifyInclusion H (mth H e D) D.length index leaf proof = true) :
    0 ≤ index ∧ index < D.length ∧ leaf = get e D index.toNat ∧ proof = path H e index.toNat D := by
  unfold verifyInclusion at h
  by_cases hg : index < 0 ∨ (D.length : Int) < 1 ∨ index ≥ D.length
  · rw [if_pos hg] at h; exact absurd h (by decide)
  rw [if_neg hg, incVerdict_iff, show ((D.length : Int) - 1).toNat = D.length - 1 by omega,
    mth_eq_rootLevels] at h
  have hi : index.toNat < D.length := by omega
  obtain ⟨h1, h2⟩ := incRes_sound H e hinj D index.toNat leaf proof hi h
  exact ⟨by omega, by omega, h1, by rw [h2, path_eq_pathLevel H e _ D hi]⟩

/-! ## Consistency -/

theorem verifyConsistency_out_of_range (oldSize : Int) (oldRoot : α) (newSize : Int) (newRoot : α)
    (proof : List α) (h : oldSize < 0 ∨ newSize < oldSize) :
    verifyConsistency H e oldSize oldRoot newSize newRoot proof = false := by
  unfold verifyConsistency; rw [if_pos h]

/-- The shared core of both directions: for `0 < m < n`, stripping the
    old tree's trailing right children, in the old tree and the new. -/
structure Stripped (D : List α) (m : Nat) where
  f : Nat
  O' : List α
  N' : List α
  hN : stripL H (m - 1) D = (f, N')
  hf : f < N'.length
  hO : f + 1 = O'.length
  hag : ∀ i, i ≤ f → get e O' i = get e N' i
  hrO : rootLevels H e O' = mth H e (D.take m)
  hrN : rootLevels H e N' = mth H e D
  hnum : stripNum (m - 1) (D.length - 1) = (f, N'.length - 1)
  hpow : isPow2 m = true → f = 0

def stripped (D : List α) (m : Nat) (hm0 : 0 < m) (hm : m < D.length) : Stripped H e D m := by
  have hagr := stripL_agree H e (m - 1) (D.take m) D (by simp; omega) (by omega)
    (fun i hi => get_take e D m i (by omega))
  exact {
    f := (stripL H (m - 1) D).1
    O' := (stripL H (m - 1) (D.take m)).2
    N' := (stripL H (m - 1) D).2
    hN := rfl
    hf := hagr.2.1
    hO := by
      rw [← hagr.1]; exact stripL_last H (m - 1) (D.take m) (by simp; omega)
    hag := fun i hi => hagr.2.2 i (by rw [hagr.1]; exact hi)
    hrO := by rw [stripL_rootLevels, mth_eq_rootLevels]
    hrN := by rw [stripL_rootLevels, mth_eq_rootLevels]
    hnum := stripNum_stripL H (m - 1) D (by omega)
    hpow := by
      intro hp
      obtain ⟨j, rfl⟩ := (isPow2_iff m).1 hp
      rw [stripL_pow] }

theorem conLevel_stripped (D : List α) (m : Nat) (s : Stripped H e D m) :
    conLevel H e m D true = (if isPow2 m then [] else [get e s.N' s.f]) ++ pathLevel H e s.f s.N' := by
  unfold conLevel; rw [s.hN]; simp

/-- Completeness: the consistency proof `Log.consistency_proof` returns
    verifies, between every prefix and the whole. -/
theorem verifyConsistency_complete (D : List α) (m : Nat) (hm : m ≤ D.length) :
    verifyConsistency H e m (mth H e (D.take m)) D.length (mth H e D) (consistencyProof H e m D) = true := by
  unfold verifyConsistency consistencyProof
  rw [if_neg (by omega)]
  by_cases hmn : m = D.length
  · subst hmn; simp
  by_cases hm0 : m = 0
  · subst hm0; simp [mth_nil, show ¬ (0 : Int) = D.length by omega]
  rw [if_neg (show ¬ (m : Int) = D.length by omega), if_neg (show ¬ (m : Int) = 0 by omega),
    if_neg (show ¬ (m = D.length ∨ m = 0) by omega),
    subproof_eq_conLevel H e m D true (by omega) (by omega),
    show (m : Int).toNat = m by omega, show (D.length : Int).toNat = D.length by omega]
  let s := stripped H e D m (by omega) (by omega)
  rw [conLevel_stripped H e D m s]
  -- the proof the verifier walks, old root prepended or not
  have hwalk : (if isPow2 m then mth H e (D.take m) :: ((if isPow2 m then [] else [get e s.N' s.f]) ++
      pathLevel H e s.f s.N') else (if isPow2 m then [] else [get e s.N' s.f]) ++ pathLevel H e s.f s.N') =
      get e s.N' s.f :: pathLevel H e s.f s.N' := by
    by_cases hp : isPow2 m
    · have hf0 := s.hpow hp
      have hO1 : s.O'.length = 1 := by rw [← s.hO, hf0]
      rw [if_pos hp, if_pos hp, List.nil_append, ← s.hrO, ← s.hag s.f (Nat.le_refl _), hf0]
      unfold rootLevels; simp [hO1, get_zero_eq_headD]
    · rw [if_neg hp, if_neg hp]; rfl
  rw [hwalk, conWalk, s.hnum, conVerdict_iff, ← s.hrO, ← s.hrN]
  have := conRes_complete H e s.N' s.O' s.f s.hO (by have := s.hf; have := s.hO; omega)
    (fun i hi => s.hag i (by omega))
  rw [s.hag s.f (Nat.le_refl _)] at this
  exact this

/-- Soundness: a consistency proof that verifies against the true root
    of `D` pins the old root to the root of `D`'s prefix, and is the
    proof `Log` produces. -/
theorem verifyConsistency_sound (hinj : NodeInjective H) (D : List α) (oldSize : Int) (oldRoot : α)
    (proof : List α)
    (h : verifyConsistency H e oldSize oldRoot D.length (mth H e D) proof = true) :
    0 ≤ oldSize ∧ oldSize ≤ D.length ∧ oldRoot = mth H e (D.take oldSize.toNat) ∧
      proof = consistencyProof H e oldSize.toNat D := by
  unfold verifyConsistency at h
  by_cases hg : oldSize < 0 ∨ (D.length : Int) < oldSize
  · rw [if_pos hg] at h; exact absurd h (by decide)
  rw [if_neg hg] at h
  refine ⟨by omega, by omega, ?_⟩
  unfold consistencyProof
  by_cases hmn : oldSize = D.length
  · rw [if_pos hmn] at h
    simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h
    rw [hmn, show (D.length : Int).toNat = D.length by omega, List.take_length, if_pos (Or.inl rfl)]
    exact h.symm
  rw [if_neg hmn] at h
  by_cases hm0 : oldSize = 0
  · rw [if_pos hm0] at h
    simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h
    rw [hm0]; simp [mth_nil, h.1, h.2]
  rw [if_neg hm0] at h
  have hm : oldSize.toNat < D.length := by omega
  have hm0' : 0 < oldSize.toNat := by omega
  rw [if_neg (by omega), subproof_eq_conLevel H e _ D true hm0' hm]
  generalize oldSize.toNat = m at h hm hm0' ⊢
  let s := stripped H e D m hm0' hm
  rw [conLevel_stripped H e D m s]
  rw [show (D.length : Int).toNat = D.length by omega] at h
  -- the list the verifier walks
  generalize hw : (if isPow2 m then oldRoot :: proof else proof) = w at h
  cases w with
  | nil => simp [conWalk] at h
  | cons first rest =>
    rw [conWalk, s.hnum, conVerdict_iff, ← s.hrN] at h
    have hinc := conRes_proj H _ _ _ _ _ _ _ h
    obtain ⟨hfirst, hrest⟩ := incRes_sound H e hinj s.N' s.f first rest s.hf hinc
    have hc := conRes_complete H e s.N' s.O' s.f s.hO (by have := s.hf; have := s.hO; omega)
      (fun i hi => s.hag i (by omega))
    rw [s.hag s.f (Nat.le_refl _), ← hfirst, ← hrest, h] at hc
    have hr1 : oldRoot = mth H e (D.take m) := by
      rw [← s.hrO]; simp only [Option.some.injEq, Prod.mk.injEq] at hc; exact hc.1
    refine ⟨hr1, ?_⟩
    by_cases hp : isPow2 m
    · rw [if_pos hp] at hw ⊢
      simp only [List.cons.injEq] at hw
      rw [List.nil_append, hw.2, hrest]
    · rw [if_neg hp] at hw ⊢
      rw [hw, hfirst, hrest]; rfl

/-! ## Corollaries about the documented behaviour -/

/-- "As in RFC 6962, the proof omits `old_root` when `old_size` is a
    power of two; a proof that spells it out is rejected." -/
theorem verifyConsistency_rejects_explicit_old_root (hinj : NodeInjective H) (D : List α) (m : Nat)
    (hm0 : 0 < m) (hm : m < D.length) (hp : isPow2 m = true) :
    verifyConsistency H e m (mth H e (D.take m)) D.length (mth H e D)
      (mth H e (D.take m) :: consistencyProof H e m D) = false := by
  cases hv : verifyConsistency H e m (mth H e (D.take m)) D.length (mth H e D)
      (mth H e (D.take m) :: consistencyProof H e m D)
  · rfl
  · have := (verifyConsistency_sound H e hinj D m _ _ hv).2.2.2
    rw [show (m : Int).toNat = m by omega] at this
    have := congrArg List.length this
    simp at this

/-- Consistency from the empty tree, as documented: an empty proof, and
    the old root must be `empty_root` (checked when the new tree is not
    empty). -/
theorem verifyConsistency_from_empty (oldRoot : α) (newSize : Int) (newRoot : α) (proof : List α)
    (hn : 0 < newSize) :
    verifyConsistency H e 0 oldRoot newSize newRoot proof = (proof.isEmpty && oldRoot == e) := by
  unfold verifyConsistency
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

/-- Equal sizes: an empty proof and equal roots. -/
theorem verifyConsistency_equal_sizes (size : Int) (oldRoot newRoot : α) (proof : List α)
    (hs : 0 ≤ size) :
    verifyConsistency H e size oldRoot size newRoot proof = (proof.isEmpty && oldRoot == newRoot) := by
  unfold verifyConsistency
  rw [if_neg (by omega), if_pos rfl]

end Merkle
