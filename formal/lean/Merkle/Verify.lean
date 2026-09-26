/-
  The RFC 9162 verifiers of `src/merkle.ml`, transcribed statement by
  statement, and their correctness.

  Sizes and indices are `Int`, like OCaml's `int` (the verifiers do no
  arithmetic that could overflow on a representable input: only
  `size - 1` with `size ≥ 1`, `land 1` and `lsr 1`). `land` is `&&&`,
  `lsr` is `>>>`, `H.equal` is `==` on a type with decidable equality.
  The OCaml loops thread an `ok` flag through `List.iter`; once it is
  false nothing else changes and the verdict is `false`, which is
  exactly `Option`'s short-circuit here.
-/
import Merkle.Subproof

namespace Merkle

variable {α : Type} (H : α → α → α) (e : α)

/-! ## The loops -/

/-- `while not (fn land 1 = 1 || fn = 0) do fn := fn lsr 1; sn := sn lsr 1 done` -/
def shiftWhileEven (fn sn : Nat) : Nat × Nat :=
  if fn &&& 1 = 1 ∨ fn = 0 then (fn, sn) else shiftWhileEven (fn >>> 1) (sn >>> 1)
termination_by fn
decreasing_by simp only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at *; omega

/-- One iteration of the `List.iter` body in `verify_inclusion`:

      if !sn = 0 then ok := false
      else begin
        if !fn land 1 = 1 || !fn = !sn then begin
          r := node_hash p !r;
          if !fn land 1 = 0 then
            while not (!fn land 1 = 1 || !fn = 0) do
              fn := !fn lsr 1; sn := !sn lsr 1
            done
        end
        else r := node_hash !r p;
        fn := !fn lsr 1; sn := !sn lsr 1
      end -/
def incStep (s : Nat × Nat × α) (p : α) : Option (Nat × Nat × α) :=
  let (fn, sn, r) := s
  if sn = 0 then none
  else if fn &&& 1 = 1 ∨ fn = sn then
    let r := H p r
    let (fn, sn) := if fn &&& 1 = 0 then shiftWhileEven fn sn else (fn, sn)
    some (fn >>> 1, sn >>> 1, r)
  else some (fn >>> 1, sn >>> 1, H r p)

def incFold : Nat × Nat × α → List α → Option (Nat × Nat × α)
  | s, [] => some s
  | s, p :: ps => match incStep H s p with
    | none => none
    | some s' => incFold s' ps

/-- `!ok && !sn = 0 && H.equal !r root` -/
def incVerdict [DecidableEq α] (root : α) : Option (Nat × Nat × α) → Bool
  | some (_, sn, r) => sn == 0 && r == root
  | none => false

/-- OCaml:

      let verify_inclusion ~root ~size ~index ~leaf ~proof =
        if index < 0 || size < 1 || index >= size then false
        else begin
          let fn = ref index and sn = ref (size - 1) in
          let r = ref leaf in
          let ok = ref true in
          List.iter (fun p -> ...) proof;
          !ok && !sn = 0 && H.equal !r root
        end -/
def verifyInclusion [DecidableEq α] (root : α) (size index : Int) (leaf : α) (proof : List α) : Bool :=
  if index < 0 ∨ size < 1 ∨ index ≥ size then false
  else incVerdict root (incFold H (index.toNat, (size - 1).toNat, leaf) proof)

/-- `while !fn land 1 = 1 do fn := !fn lsr 1; sn := !sn lsr 1 done` -/
def stripNum (fn sn : Nat) : Nat × Nat :=
  if fn &&& 1 = 1 then stripNum (fn >>> 1) (sn >>> 1) else (fn, sn)
termination_by fn
decreasing_by simp only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at *; omega

/-- One iteration of the `List.iter` body in `verify_consistency`. -/
def conStep (s : Nat × Nat × α × α) (c : α) : Option (Nat × Nat × α × α) :=
  let (fn, sn, fr, sr) := s
  if sn = 0 then none
  else if fn &&& 1 = 1 ∨ fn = sn then
    let fr := H c fr
    let sr := H c sr
    let (fn, sn) := if fn &&& 1 = 0 then shiftWhileEven fn sn else (fn, sn)
    some (fn >>> 1, sn >>> 1, fr, sr)
  else some (fn >>> 1, sn >>> 1, fr, H sr c)

def conFold : Nat × Nat × α × α → List α → Option (Nat × Nat × α × α)
  | s, [] => some s
  | s, c :: cs => match conStep H s c with
    | none => none
    | some s' => conFold s' cs

/-- `!ok && !sn = 0 && H.equal !fr old_root && H.equal !sr new_root` -/
def conVerdict [DecidableEq α] (oldRoot newRoot : α) : Option (Nat × Nat × α × α) → Bool
  | some (_, sn, fr, sr) => sn == 0 && fr == oldRoot && sr == newRoot
  | none => false

/-- The `match proof with` of `verify_consistency`, for `0 < m < n`. -/
def conWalk [DecidableEq α] (oldRoot newRoot : α) (m n : Nat) : List α → Bool
  | [] => false
  | first :: rest =>
    -- `fn, sn` after the first `while` loop
    let fnsn := stripNum (m - 1) (n - 1)
    conVerdict oldRoot newRoot (conFold H (fnsn.1, fnsn.2, first, first) rest)

/-- OCaml:

      let verify_consistency ~old_size ~old_root ~new_size ~new_root ~proof =
        if old_size < 0 || new_size < old_size then false
        else if old_size = new_size then
          proof = [] && H.equal old_root new_root
        else if old_size = 0 then
          proof = [] && H.equal old_root empty_root
        else begin
          let proof = if is_pow2 old_size then old_root :: proof else proof in
          match proof with
          | [] -> false
          | first :: rest ->
            let fn = ref (old_size - 1) and sn = ref (new_size - 1) in
            while !fn land 1 = 1 do fn := !fn lsr 1; sn := !sn lsr 1 done;
            let fr = ref first and sr = ref first in
            let ok = ref true in
            List.iter (fun c -> ...) rest;
            !ok && !sn = 0 && H.equal !fr old_root && H.equal !sr new_root
        end -/
def verifyConsistency [DecidableEq α] (oldSize : Int) (oldRoot : α) (newSize : Int) (newRoot : α)
    (proof : List α) : Bool :=
  if oldSize < 0 ∨ newSize < oldSize then false
  else if oldSize = newSize then proof.isEmpty && oldRoot == newRoot
  else if oldSize = 0 then proof.isEmpty && oldRoot == e
  else
    -- `let proof = if is_pow2 old_size then old_root :: proof else proof in`
    conWalk H oldRoot newRoot oldSize.toNat newSize.toNat
      (if isPow2 oldSize.toNat then oldRoot :: proof else proof)

/-! ## Arithmetic views of the loops -/

theorem shiftWhileEven_eq (fn sn : Nat) :
    shiftWhileEven fn sn =
      if fn % 2 = 1 ∨ fn = 0 then (fn, sn) else shiftWhileEven (fn / 2) (sn / 2) := by
  rw [shiftWhileEven]; simp [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

theorem stripNum_eq (fn sn : Nat) :
    stripNum fn sn = if fn % 2 = 1 then stripNum (fn / 2) (sn / 2) else (fn, sn) := by
  rw [stripNum]; simp [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

theorem incStep_zero (fn : Nat) (r p : α) : incStep H (fn, 0, r) p = none := by
  simp [incStep]

theorem incStep_odd (fn sn : Nat) (r p : α) (hs : sn ≠ 0) (hf : fn % 2 = 1) :
    incStep H (fn, sn, r) p = some (fn / 2, sn / 2, H p r) := by
  simp [incStep, hs, Nat.and_one_is_mod, hf, Nat.shiftRight_eq_div_pow]

theorem incStep_right (fn sn : Nat) (r p : α) (hs : sn ≠ 0) (hf : fn % 2 = 0) (hne : fn ≠ sn) :
    incStep H (fn, sn, r) p = some (fn / 2, sn / 2, H r p) := by
  simp [incStep, hs, Nat.and_one_is_mod, hf, hne, Nat.shiftRight_eq_div_pow]

/-- A last even node is promoted: the step is the one a level up. -/
theorem incStep_promote (fn : Nat) (r p : α) (hs : fn ≠ 0) (hf : fn % 2 = 0) :
    incStep H (fn, fn, r) p = incStep H (fn / 2, fn / 2, r) p := by
  have h2 : fn / 2 ≠ 0 := by omega
  simp only [incStep, hs, h2, Nat.and_one_is_mod, hf, if_false, or_true, if_true,
    Nat.shiftRight_eq_div_pow, Nat.pow_one]
  rw [shiftWhileEven_eq fn fn, if_neg (by omega)]
  by_cases h : fn / 2 % 2 = 1
  · rw [if_neg (by omega), shiftWhileEven_eq, if_pos (Or.inl h)]
  · rw [if_pos (by omega)]

theorem conStep_zero (fn : Nat) (fr sr c : α) : conStep H (fn, 0, fr, sr) c = none := by
  simp [conStep]

theorem conStep_odd (fn sn : Nat) (fr sr c : α) (hs : sn ≠ 0) (hf : fn % 2 = 1) :
    conStep H (fn, sn, fr, sr) c = some (fn / 2, sn / 2, H c fr, H c sr) := by
  simp [conStep, hs, Nat.and_one_is_mod, hf, Nat.shiftRight_eq_div_pow]

theorem conStep_right (fn sn : Nat) (fr sr c : α) (hs : sn ≠ 0) (hf : fn % 2 = 0) (hne : fn ≠ sn) :
    conStep H (fn, sn, fr, sr) c = some (fn / 2, sn / 2, fr, H sr c) := by
  simp [conStep, hs, Nat.and_one_is_mod, hf, hne, Nat.shiftRight_eq_div_pow]

theorem conStep_promote (fn : Nat) (fr sr c : α) (hs : fn ≠ 0) (hf : fn % 2 = 0) :
    conStep H (fn, fn, fr, sr) c = conStep H (fn / 2, fn / 2, fr, sr) c := by
  have h2 : fn / 2 ≠ 0 := by omega
  simp only [conStep, hs, h2, Nat.and_one_is_mod, hf, if_false, or_true, if_true,
    Nat.shiftRight_eq_div_pow, Nat.pow_one]
  rw [shiftWhileEven_eq fn fn, if_neg (by omega)]
  by_cases h : fn / 2 % 2 = 1
  · rw [if_neg (by omega), shiftWhileEven_eq, if_pos (Or.inl h)]
  · rw [if_pos (by omega)]

/-! ## Results: accept only with `sn = 0` -/

/-- The value the inclusion loop commits to, if it ends with `sn = 0`. -/
def incRes (s : Nat × Nat × α) (ps : List α) : Option α :=
  match incFold H s ps with
  | some (_, sn, r) => if sn = 0 then some r else none
  | none => none

def conRes (s : Nat × Nat × α × α) (ps : List α) : Option (α × α) :=
  match conFold H s ps with
  | some (_, sn, fr, sr) => if sn = 0 then some (fr, sr) else none
  | none => none

theorem incRes_nil (fn sn : Nat) (r : α) :
    incRes H (fn, sn, r) [] = if sn = 0 then some r else none := rfl

theorem incRes_cons (s : Nat × Nat × α) (p : α) (ps : List α) :
    incRes H s (p :: ps) = match incStep H s p with
      | none => none
      | some s' => incRes H s' ps := by
  unfold incRes; simp only [incFold]; cases incStep H s p <;> rfl

theorem incRes_promote (fn : Nat) (r : α) (ps : List α) (hs : fn ≠ 0) (hf : fn % 2 = 0) :
    incRes H (fn, fn, r) ps = incRes H (fn / 2, fn / 2, r) ps := by
  cases ps with
  | nil => rw [incRes_nil, incRes_nil, if_neg hs, if_neg (by omega)]
  | cons p ps => rw [incRes_cons, incRes_cons, incStep_promote H fn r p hs hf]

theorem conRes_nil (fn sn : Nat) (fr sr : α) :
    conRes H (fn, sn, fr, sr) [] = if sn = 0 then some (fr, sr) else none := rfl

theorem conRes_cons (s : Nat × Nat × α × α) (c : α) (cs : List α) :
    conRes H s (c :: cs) = match conStep H s c with
      | none => none
      | some s' => conRes H s' cs := by
  unfold conRes; simp only [conFold]; cases conStep H s c <;> rfl

theorem conRes_promote (fn : Nat) (fr sr : α) (cs : List α) (hs : fn ≠ 0) (hf : fn % 2 = 0) :
    conRes H (fn, fn, fr, sr) cs = conRes H (fn / 2, fn / 2, fr, sr) cs := by
  cases cs with
  | nil => rw [conRes_nil, conRes_nil, if_neg hs, if_neg (by omega)]
  | cons c cs => rw [conRes_cons, conRes_cons, conStep_promote H fn fr sr c hs hf]

/-- The consistency loop runs the inclusion loop on `sr`. -/
theorem conRes_proj (fn sn : Nat) (fr sr : α) (cs : List α) (fr' sr' : α)
    (h : conRes H (fn, sn, fr, sr) cs = some (fr', sr')) : incRes H (fn, sn, sr) cs = some sr' := by
  induction cs generalizing fn sn fr sr with
  | nil =>
    rw [conRes_nil] at h; rw [incRes_nil]
    split at h
    · simp_all
    · simp at h
  | cons c cs ih =>
    rw [conRes_cons] at h; rw [incRes_cons]
    by_cases hs : sn = 0
    · subst hs; rw [conStep_zero] at h; simp at h
    by_cases hf : fn % 2 = 1
    · rw [conStep_odd H fn sn fr sr c hs hf] at h
      rw [incStep_odd H fn sn sr c hs hf]
      exact ih _ _ _ _ h
    by_cases hne : fn = sn
    · subst hne
      rw [conStep_promote H fn fr sr c hs (by omega)] at h
      rw [incStep_promote H fn sr c hs (by omega)]
      -- one level up the step is again a promotion or an odd step
      have hs2 : fn / 2 ≠ 0 := by omega
      revert h
      generalize hk : fn / 2 = k
      intro h
      induction k using Nat.strongRecOn generalizing fn with
      | _ k ihk =>
        by_cases hk1 : k % 2 = 1
        · rw [conStep_odd H k k fr sr c (by omega) hk1] at h
          rw [incStep_odd H k k sr c (by omega) hk1]
          exact ih _ _ _ _ h
        · rw [conStep_promote H k fr sr c (by omega) (by omega)] at h
          rw [incStep_promote H k sr c (by omega) (by omega)]
          exact ihk (k / 2) (by omega) k (by omega) (by omega) (by omega) rfl h
    · rw [conStep_right H fn sn fr sr c hs (by omega) hne] at h
      rw [incStep_right H fn sn sr c hs (by omega) hne]
      exact ih _ _ _ _ h

/-! ## Inclusion: completeness and soundness on levels -/

/-- The honest audit path leads from `L[fn]` to the root. -/
theorem incRes_complete (L : List α) (fn : Nat) (hfn : fn < L.length) :
    incRes H (fn, L.length - 1, get e L fn) (pathLevel H e fn L) = some (rootLevels H e L) := by
  induction h : L.length using Nat.strongRecOn generalizing L fn with
  | _ n ih =>
    by_cases hl : L.length < 2
    · rw [pathLevel_short H e _ _ hl, incRes_nil, if_pos (by omega)]
      have : fn = 0 := by omega
      subst this
      unfold rootLevels; simp [hl, get_zero_eq_headD]
    · have hup : (levelUp H L).length - 1 = (n - 1) / 2 := by rw [length_levelUp]; omega
      have ihL := fun fn' h' => ih _ (by rw [← h, length_levelUp]; omega) (levelUp H L) fn' h' rfl
      rw [pathLevel_long H e _ _ hl, ← rootLevels_levelUp]
      by_cases hf : fn % 2 = 1
      · rw [if_pos hf, List.singleton_append, incRes_cons,
          incStep_odd H _ _ _ _ (by omega) hf, ← hup,
          show H (get e L (fn - 1)) (get e L fn) = get e (levelUp H L) (fn / 2) by
            rw [get_levelUp_pair H e L (fn / 2) (by omega)]
            rw [show 2 * (fn / 2) = fn - 1 by omega, show fn - 1 + 1 = fn by omega]]
        exact ihL _ (by rw [length_levelUp]; omega)
      · rw [if_neg hf]
        by_cases hr : fn + 1 < L.length
        · rw [if_pos hr, List.singleton_append, incRes_cons,
            incStep_right H _ _ _ _ (by omega) (by omega) (by omega), ← hup,
            show H (get e L fn) (get e L (fn + 1)) = get e (levelUp H L) (fn / 2) by
              rw [get_levelUp_pair H e L (fn / 2) (by omega)]
              rw [show 2 * (fn / 2) = fn by omega]]
          exact ihL _ (by rw [length_levelUp]; omega)
        · rw [if_neg hr, List.nil_append, show n - 1 = fn by omega,
            incRes_promote H _ _ _ (by omega) (by omega),
            show fn / 2 = (levelUp H L).length - 1 by rw [length_levelUp]; omega,
            show get e L fn = get e (levelUp H L) ((levelUp H L).length - 1) by
              rw [get_levelUp_last H e L _ (by rw [length_levelUp]; omega)]
              congr 1; rw [length_levelUp]; omega]
          exact ihL _ (by rw [length_levelUp]; omega)

/-- Hash injectivity: finding two different pairs with the same node
    hash is finding a collision. -/
def NodeInjective (H : α → α → α) : Prop := ∀ a b c d, H a b = H c d → a = c ∧ b = d

/-- If the loop reaches the true root, the leaf is `L[fn]` and the
    proof is the honest audit path. -/
theorem incRes_sound (hinj : NodeInjective H) (L : List α) (fn : Nat) (x : α) (ps : List α)
    (hfn : fn < L.length)
    (hres : incRes H (fn, L.length - 1, x) ps = some (rootLevels H e L)) :
    x = get e L fn ∧ ps = pathLevel H e fn L := by
  induction h : L.length using Nat.strongRecOn generalizing L fn x ps with
  | _ n ih =>
    by_cases hl : L.length < 2
    · have : fn = 0 := by omega
      subst this
      have hsn : L.length - 1 = 0 := by omega
      rw [hsn] at hres
      cases ps with
      | nil =>
        rw [incRes_nil, if_pos rfl] at hres
        unfold rootLevels at hres
        simp [hl] at hres
        rw [pathLevel_short H e _ _ hl, get_zero_eq_headD, hres]; simp
      | cons p ps => rw [incRes_cons, incStep_zero] at hres; simp at hres
    · have hup : (levelUp H L).length - 1 = (L.length - 1) / 2 := by rw [length_levelUp]; omega
      have ihL := fun fn' x' ps' h1 h2 =>
        ih _ (by rw [← h, length_levelUp]; omega) (levelUp H L) fn' x' ps' h1 h2 rfl
      rw [← rootLevels_levelUp] at hres
      rw [pathLevel_long H e _ _ hl]
      cases ps with
      | nil => rw [incRes_nil, if_neg (by omega)] at hres; simp at hres
      | cons p ps =>
        by_cases hf : fn % 2 = 1
        · rw [incRes_cons, incStep_odd H _ _ _ _ (by omega) hf, ← hup] at hres
          obtain ⟨h1, h2⟩ := ihL _ _ _ (by rw [length_levelUp]; omega) hres
          rw [get_levelUp_pair H e L (fn / 2) (by omega),
            show 2 * (fn / 2) = fn - 1 by omega, show fn - 1 + 1 = fn by omega] at h1
          obtain ⟨hp, hx⟩ := hinj _ _ _ _ h1
          rw [if_pos hf, hx, hp, h2]; simp
        · by_cases hr : fn + 1 < L.length
          · rw [incRes_cons, incStep_right H _ _ _ _ (by omega) (by omega) (by omega), ← hup] at hres
            obtain ⟨h1, h2⟩ := ihL _ _ _ (by rw [length_levelUp]; omega) hres
            rw [get_levelUp_pair H e L (fn / 2) (by omega), show 2 * (fn / 2) = fn by omega] at h1
            obtain ⟨hx, hp⟩ := hinj _ _ _ _ h1
            rw [if_neg hf, if_pos hr, hx, hp, h2]; simp
          · rw [show L.length - 1 = fn by omega, incRes_promote H _ _ _ (by omega) (by omega),
              show fn / 2 = (levelUp H L).length - 1 by rw [length_levelUp]; omega] at hres
            obtain ⟨h1, h2⟩ := ihL _ _ _ (by rw [length_levelUp]; omega) hres
            have hm1 : (levelUp H L).length - 1 = fn / 2 := by rw [length_levelUp]; omega
            rw [hm1, get_levelUp_last H e L _ (by omega), show 2 * (fn / 2) = fn by omega] at h1
            rw [hm1] at h2
            rw [if_neg hf, if_neg hr, h1, List.nil_append, h2]
            exact ⟨rfl, rfl⟩

/-! ## Consistency: the honest run on levels -/

/-- Walking the honest path of the old tree's last node in the new tree
    `N` computes both roots, as long as the old tree `O` agrees with `N`
    left of that node. -/
theorem conRes_complete (N O : List α) (fn : Nat) (hO : fn + 1 = O.length) (hON : O.length ≤ N.length)
    (hag : ∀ i, i < fn → get e O i = get e N i) :
    conRes H (fn, N.length - 1, get e O fn, get e N fn) (pathLevel H e fn N) =
      some (rootLevels H e O, rootLevels H e N) := by
  induction h : N.length using Nat.strongRecOn generalizing N O fn with
  | _ n ih =>
    by_cases hl : N.length < 2
    · rw [pathLevel_short H e _ _ hl, conRes_nil, if_pos (by omega)]
      have : fn = 0 := by omega
      subst this
      have hO1 : O.length < 2 := by omega
      unfold rootLevels; simp [hl, hO1, get_zero_eq_headD]
    · have hupN : (levelUp H N).length - 1 = (n - 1) / 2 := by rw [length_levelUp]; omega
      have hupO : (levelUp H O).length = fn / 2 + 1 := by rw [length_levelUp]; omega
      have ihL := fun O' fn' h1 h2 h3 =>
        ih _ (by rw [← h, length_levelUp]; omega) (levelUp H N) O' fn' h1 h2 h3 rfl
      rw [pathLevel_long H e _ _ hl, ← rootLevels_levelUp H e N, ← rootLevels_levelUp H e O]
      by_cases hf : fn % 2 = 1
      · rw [if_pos hf, List.singleton_append, conRes_cons,
          conStep_odd H _ _ _ _ _ (by omega) hf, ← hupN,
          show H (get e N (fn - 1)) (get e O fn) = get e (levelUp H O) (fn / 2) by
            rw [get_levelUp_pair H e O (fn / 2) (by omega),
              show 2 * (fn / 2) = fn - 1 by omega, show fn - 1 + 1 = fn by omega,
              hag (fn - 1) (by omega)],
          show H (get e N (fn - 1)) (get e N fn) = get e (levelUp H N) (fn / 2) by
            rw [get_levelUp_pair H e N (fn / 2) (by omega),
              show 2 * (fn / 2) = fn - 1 by omega, show fn - 1 + 1 = fn by omega]]
        apply ihL _ _ hupO.symm (by rw [hupO, length_levelUp]; omega)
        intro i hi
        rw [get_levelUp_pair H e O i (by omega), get_levelUp_pair H e N i (by omega),
          hag _ (by omega), hag _ (by omega)]
      · rw [if_neg hf]
        have hOlast : get e O fn = get e (levelUp H O) (fn / 2) := by
          rw [get_levelUp_last H e O _ (by omega), show 2 * (fn / 2) = fn by omega]
        have hagup : ∀ i, i < fn / 2 → get e (levelUp H O) i = get e (levelUp H N) i := by
          intro i hi
          rw [get_levelUp_pair H e O i (by omega), get_levelUp_pair H e N i (by omega),
            hag _ (by omega), hag _ (by omega)]
        by_cases hr : fn + 1 < N.length
        · rw [if_pos hr, List.singleton_append, conRes_cons,
            conStep_right H _ _ _ _ _ (by omega) (by omega) (by omega), ← hupN, hOlast,
            show H (get e N fn) (get e N (fn + 1)) = get e (levelUp H N) (fn / 2) by
              rw [get_levelUp_pair H e N (fn / 2) (by omega), show 2 * (fn / 2) = fn by omega]]
          exact ihL _ _ hupO.symm (by rw [hupO, length_levelUp]; omega) hagup
        · rw [if_neg hr, List.nil_append, show n - 1 = fn by omega,
            conRes_promote H _ _ _ _ (by omega) (by omega), hOlast,
            show get e N fn = get e (levelUp H N) (fn / 2) by
              rw [get_levelUp_last H e N _ (by omega), show 2 * (fn / 2) = fn by omega]]
          have hm1 : (levelUp H N).length - 1 = fn / 2 := by rw [length_levelUp]; omega
          have := ihL _ _ hupO.symm (by rw [hupO, length_levelUp]; omega) hagup
          rw [hm1] at this
          exact this

end Merkle
