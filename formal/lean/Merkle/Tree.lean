/-
  RFC 6962 Merkle trees over an abstract hash.

  Hashes are an arbitrary type `α` with a node hash `H : α → α → α`
  (`node_hash`) and a default value `e` (`empty_root`, only used as the
  root of the empty list and as the out-of-range default of `get`).
  Leaves are leaf *hashes* — exactly what `Log` stores.

  Two views of the same tree:

  * top-down, as the RFC defines it and as `src/merkle.ml` computes
    roots and proofs: split at the largest power of two `k < n`
    (`mth`, `path`, `subproof`);
  * bottom-up, level by level, as the RFC 9162 verifiers walk it: pair
    neighbours, promote a last odd node unchanged (`levelUp`,
    `rootLevels`, `pathLevel`).

  This file proves the two views agree.
-/
import Merkle.Split

namespace Merkle

variable {α : Type}

/-- Total list indexing with a default. -/
def get (e : α) : List α → Nat → α
  | [], _ => e
  | a :: _, 0 => a
  | _ :: l, n + 1 => get e l n

section
variable (e : α)

@[simp] theorem get_nil (i : Nat) : get e ([] : List α) i = e := by cases i <;> rfl
@[simp] theorem get_cons_zero (a : α) (l : List α) : get e (a :: l) 0 = a := rfl
@[simp] theorem get_cons_succ (a : α) (l : List α) (i : Nat) :
    get e (a :: l) (i + 1) = get e l i := rfl

theorem get_append_left : ∀ (A B : List α) (i : Nat), i < A.length →
    get e (A ++ B) i = get e A i
  | [], _, _, h => by simp at h
  | _ :: _, _, 0, _ => rfl
  | _ :: A, B, i + 1, h => by
    simp only [List.cons_append, get_cons_succ]
    exact get_append_left A B i (by simp at h; omega)

theorem get_append_right : ∀ (A B : List α) (i : Nat),
    get e (A ++ B) (A.length + i) = get e B i
  | [], _, _ => by simp
  | _ :: A, B, i => by
    simp only [List.cons_append, List.length_cons]
    rw [show A.length + 1 + i = (A.length + i) + 1 by omega, get_cons_succ]
    exact get_append_right A B i

theorem get_take : ∀ (l : List α) (k i : Nat), i < k → get e (l.take k) i = get e l i
  | [], _, _, _ => by simp
  | _ :: _, 0, _, h => by omega
  | _ :: _, _ + 1, 0, _ => rfl
  | _ :: l, k + 1, i + 1, h => by
    simp only [List.take_succ_cons, get_cons_succ]
    exact get_take l k i (by omega)

theorem get_drop : ∀ (l : List α) (k i : Nat), get e (l.drop k) i = get e l (k + i)
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | _ :: l, k + 1, i => by
    simp only [List.drop_succ_cons]
    rw [show k + 1 + i = (k + i) + 1 by omega, get_cons_succ]
    exact get_drop l k i

theorem get_zero_eq_headD : ∀ (l : List α), get e l 0 = l.headD e
  | [] => rfl
  | _ :: _ => rfl
end

variable (H : α → α → α) (e : α)

/-! ## Levels -/

/-- One level up: hash neighbours pairwise, promote a last odd node. -/
def levelUp : List α → List α
  | a :: b :: t => H a b :: levelUp t
  | l => l

@[simp] theorem levelUp_nil : levelUp H ([] : List α) = [] := rfl
@[simp] theorem levelUp_single (a : α) : levelUp H [a] = [a] := rfl
@[simp] theorem levelUp_cons_cons (a b : α) (t : List α) :
    levelUp H (a :: b :: t) = H a b :: levelUp H t := rfl

theorem length_levelUp : ∀ l : List α, (levelUp H l).length = (l.length + 1) / 2
  | [] => by simp
  | [_] => by simp
  | _ :: _ :: t => by simp [length_levelUp t]; omega

theorem levelUp_of_length_le_one : ∀ l : List α, l.length ≤ 1 → levelUp H l = l
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _, h => by simp at h

/-- Pairs never straddle an even-length prefix. -/
theorem levelUp_append : ∀ (A B : List α), A.length % 2 = 0 →
    levelUp H (A ++ B) = levelUp H A ++ levelUp H B
  | [], _, _ => rfl
  | [_], _, h => by simp at h
  | a :: b :: A, B, h => by
    simp only [List.cons_append, levelUp_cons_cons]
    rw [levelUp_append A B (by simp at h; omega)]

theorem get_levelUp_pair : ∀ (l : List α) (j : Nat), 2 * j + 1 < l.length →
    get e (levelUp H l) j = H (get e l (2 * j)) (get e l (2 * j + 1))
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | _ :: _ :: _, 0, _ => rfl
  | _ :: _ :: t, j + 1, h => by
    have ih := get_levelUp_pair t j (by simp at h; omega)
    simp only [levelUp_cons_cons, get_cons_succ,
      show 2 * (j + 1) = 2 * j + 1 + 1 by omega]
    exact ih

theorem get_levelUp_last : ∀ (l : List α) (j : Nat), 2 * j + 1 = l.length →
    get e (levelUp H l) j = get e l (2 * j)
  | [], _, h => by simp at h
  | [_], 0, _ => rfl
  | [_], _ + 1, h => by simp at h <;> omega
  | _ :: _ :: t, 0, h => by simp at h <;> omega
  | _ :: _ :: t, j + 1, h => by
    have ih := get_levelUp_last t j (by simp at h; omega)
    simp only [levelUp_cons_cons, get_cons_succ, show 2 * (j + 1) = 2 * j + 1 + 1 by omega]
    exact ih

/-- The root, computed bottom-up. -/
def rootLevels (l : List α) : α :=
  if l.length < 2 then l.headD e else rootLevels (levelUp H l)
termination_by l.length
decreasing_by rw [length_levelUp]; omega

theorem rootLevels_levelUp (l : List α) : rootLevels H e (levelUp H l) = rootLevels H e l := by
  by_cases h : l.length < 2
  · rw [levelUp_of_length_le_one H l (by omega)]
  · conv => rhs; unfold rootLevels
    rw [if_neg h]

theorem rootLevels_single (a : α) : rootLevels H e [a] = a := by
  unfold rootLevels; simp

theorem rootLevels_pair (a b : α) : rootLevels H e [a, b] = H a b := by
  unfold rootLevels; simp [rootLevels_single]

/-- `lvl t l`: `t` levels up. -/
def lvl : Nat → List α → List α
  | 0, l => l
  | t + 1, l => lvl t (levelUp H l)

theorem rootLevels_lvl : ∀ (t : Nat) (l : List α), rootLevels H e (lvl H t l) = rootLevels H e l
  | 0, _ => rfl
  | t + 1, l => by simp only [lvl]; rw [rootLevels_lvl t, rootLevels_levelUp]

/-! ## Top-down: RFC 6962 section 2.1 -/

/-- MTH(D[n]). -/
def mth (l : List α) : α :=
  if h : l.length < 2 then l.headD e
  else H (mth (l.take (split l.length))) (mth (l.drop (split l.length)))
termination_by l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]
  · have := split_lt (n := l.length) (by omega); omega
  · have := split_pos (n := l.length) (by omega); omega

/-- G0: a perfect left subtree and a right subtree no bigger than it
    hash to `H (root left) (root right)`, bottom-up too. -/
theorem rootLevels_append : ∀ (j : Nat) (A B : List α),
    A.length = 2 ^ j → 1 ≤ B.length → B.length ≤ A.length →
    rootLevels H e (A ++ B) = H (rootLevels H e A) (rootLevels H e B)
  | 0, A, B, hA, hB1, hB2 => by
    match A, B, hA with
    | [a], [b], _ => simp [rootLevels_pair, rootLevels_single]
    | [a], [], _ => simp at hB1
    | [a], _ :: _ :: _, _ => simp at hB2
  | j + 1, A, B, hA, hB1, hB2 => by
    have hA2 : A.length % 2 = 0 := by rw [hA, Nat.pow_succ]; omega
    have hlen : ¬ (A ++ B).length < 2 := by
      simp; have := Nat.one_le_two_pow (n := j); rw [Nat.pow_succ] at hA; omega
    rw [← rootLevels_levelUp H e (A ++ B), levelUp_append H A B hA2,
      rootLevels_append j (levelUp H A) (levelUp H B)]
    · rw [rootLevels_levelUp, rootLevels_levelUp]
    · rw [length_levelUp, hA, Nat.pow_succ]; omega
    · simp only [length_levelUp]; omega
    · simp only [length_levelUp]; omega

/-- MTH is the bottom-up root. -/
theorem mth_eq_rootLevels (l : List α) : mth H e l = rootLevels H e l := by
  induction h : l.length using Nat.strongRecOn generalizing l with
  | _ n ih =>
    by_cases hl : l.length < 2
    · unfold mth rootLevels; simp [hl]
    · obtain ⟨j, hk, hk1, hk2⟩ := split_spec (n := l.length) (by omega)
      unfold mth
      rw [dif_neg hl]
      have e1 : (l.take (split l.length)).length = 2 ^ j := by
        simp [hk]; omega
      have e2 : (l.drop (split l.length)).length = l.length - 2 ^ j := by simp [hk]
      rw [ih _ (by omega) _ rfl, ih _ (by omega) _ rfl]
      conv => rhs; rw [← List.take_append_drop (split l.length) l]
      rw [rootLevels_append H e j _ _ e1 (by omega) (by omega)]

/-! ## Audit paths -/

/-- PATH(m, D[n]), RFC 6962 section 2.1.1, top-down. -/
def path (m : Nat) (l : List α) : List α :=
  if h : l.length < 2 then []
  else if m < split l.length then
    path m (l.take (split l.length)) ++ [mth H e (l.drop (split l.length))]
  else
    path (m - split l.length) (l.drop (split l.length)) ++ [mth H e (l.take (split l.length))]
termination_by l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]
  · have := split_lt (n := l.length) (by omega); omega
  · have := split_pos (n := l.length) (by omega); omega

/-- The audit path bottom-up, in the order the RFC 9162 verifier
    consumes it: at each level the sibling, if there is one (a last odd
    node is promoted and contributes nothing). -/
def pathLevel (m : Nat) (l : List α) : List α :=
  if l.length < 2 then []
  else
    (if m % 2 = 1 then [get e l (m - 1)] else if m + 1 < l.length then [get e l (m + 1)] else [])
      ++ pathLevel (m / 2) (levelUp H l)
termination_by l.length
decreasing_by rw [length_levelUp]; omega

theorem pathLevel_short (m : Nat) (l : List α) (h : l.length < 2) : pathLevel H e m l = [] := by
  unfold pathLevel; simp [h]

theorem pathLevel_long (m : Nat) (l : List α) (h : ¬ l.length < 2) :
    pathLevel H e m l =
      (if m % 2 = 1 then [get e l (m - 1)] else if m + 1 < l.length then [get e l (m + 1)] else [])
        ++ pathLevel H e (m / 2) (levelUp H l) := by
  rw [pathLevel, if_neg h]

/-- G1: a leaf in a perfect left subtree. -/
theorem pathLevel_append_left : ∀ (j : Nat) (A B : List α) (x : Nat),
    A.length = 2 ^ j → x < A.length → 1 ≤ B.length → B.length ≤ A.length →
    pathLevel H e x (A ++ B) = pathLevel H e x A ++ [rootLevels H e B]
  | 0, A, B, x, hA, hx, hB1, hB2 => by
    match A, B, hA with
    | [a], [b], _ =>
      have : x = 0 := by simp at hx; omega
      subst this
      rw [pathLevel_long H e _ _ (by simp), pathLevel_short H e _ [a] (by simp)]
      simp [pathLevel_short, rootLevels_single]
    | [a], [], _ => simp at hB1
    | [a], _ :: _ :: _, _ => simp at hB2
  | j + 1, A, B, x, hA, hx, hB1, hB2 => by
    have hA2 : A.length % 2 = 0 := by rw [hA, Nat.pow_succ]; omega
    have hAl : ¬ A.length < 2 := by
      have := Nat.one_le_two_pow (n := j); rw [Nat.pow_succ] at hA; omega
    rw [pathLevel_long H e _ _ (by simp; omega), pathLevel_long H e _ _ hAl,
      levelUp_append H A B hA2,
      pathLevel_append_left j (levelUp H A) (levelUp H B) (x / 2)]
    · rw [rootLevels_levelUp]
      simp only [List.length_append, List.append_assoc]
      congr 1
      by_cases hx1 : x % 2 = 1
      · rw [if_pos hx1, if_pos hx1, get_append_left e A B (x - 1) (by omega)]
      · have : x + 1 < A.length := by omega
        rw [if_neg hx1, if_neg hx1, if_pos this, if_pos (by omega), get_append_left e A B _ this]
    · rw [length_levelUp, hA, Nat.pow_succ]; omega
    · simp only [length_levelUp]; omega
    · simp only [length_levelUp]; omega
    · simp only [length_levelUp]; omega

/-- G2: a leaf in the right subtree. -/
theorem pathLevel_append_right : ∀ (j : Nat) (A B : List α) (x : Nat),
    A.length = 2 ^ j → x < B.length → B.length ≤ A.length →
    pathLevel H e (A.length + x) (A ++ B) = pathLevel H e x B ++ [rootLevels H e A]
  | 0, A, B, x, hA, hx, hB2 => by
    match A, B, hA with
    | [a], [b], _ =>
      have : x = 0 := by simp at hx; omega
      subst this
      rw [pathLevel_long H e _ _ (by simp), pathLevel_short H e _ [b] (by simp)]
      simp [pathLevel_short, rootLevels_single]
    | [a], [], _ => simp at hx
    | [a], _ :: _ :: _, _ => simp at hB2
  | j + 1, A, B, x, hA, hx, hB2 => by
    have hA2 : A.length % 2 = 0 := by rw [hA, Nat.pow_succ]; omega
    have hAl : ¬ A.length < 2 := by
      have := Nat.one_le_two_pow (n := j); rw [Nat.pow_succ] at hA; omega
    have hdiv : (A.length + x) / 2 = (levelUp H A).length + x / 2 := by
      rw [length_levelUp]; omega
    rw [pathLevel_long H e _ _ (by simp; omega), levelUp_append H A B hA2, hdiv,
      pathLevel_append_right j (levelUp H A) (levelUp H B) (x / 2)]
    · rw [rootLevels_levelUp]
      by_cases hB : B.length < 2
      · -- B is a single node: it is promoted until it meets A's root
        have hx0 : x = 0 := by omega
        subst hx0
        rw [levelUp_of_length_le_one H B (by omega), pathLevel_short H e _ B hB]
        simp [hA2, show ¬ A.length + 1 < A.length + B.length by omega]
      · rw [pathLevel_long H e _ B hB]
        simp only [List.length_append, List.append_assoc]
        congr 1
        by_cases hx1 : x % 2 = 1
        · have : (A.length + x) % 2 = 1 := by omega
          simp only [this, hx1, if_true]
          rw [show A.length + x - 1 = A.length + (x - 1) by omega, get_append_right]
        · have : ¬ (A.length + x) % 2 = 1 := by omega
          simp only [this, hx1, if_false]
          by_cases hx2 : x + 1 < B.length
          · simp only [show A.length + x + 1 < A.length + B.length by omega, hx2, if_true]
            rw [show A.length + x + 1 = A.length + (x + 1) by omega, get_append_right]
          · simp [show ¬ A.length + x + 1 < A.length + B.length by omega, hx2]
    · rw [length_levelUp, hA, Nat.pow_succ]; omega
    · simp only [length_levelUp]; omega
    · simp only [length_levelUp]; omega

/-- PATH is the bottom-up audit path. -/
theorem path_eq_pathLevel (m : Nat) (l : List α) (hm : m < l.length) :
    path H e m l = pathLevel H e m l := by
  induction h : l.length using Nat.strongRecOn generalizing l m with
  | _ n ih =>
    by_cases hl : l.length < 2
    · unfold path; rw [dif_pos hl, pathLevel_short H e _ _ hl]
    · obtain ⟨j, hk, hk1, hk2⟩ := split_spec (n := l.length) (by omega)
      have e1 : (l.take (split l.length)).length = 2 ^ j := by simp [hk]; omega
      have e2 : (l.drop (split l.length)).length = l.length - 2 ^ j := by simp [hk]
      unfold path
      rw [dif_neg hl]
      conv => rhs; rw [← List.take_append_drop (split l.length) l]
      by_cases hmk : m < split l.length
      · rw [if_pos hmk, ih _ (by omega) _ _ (by omega) rfl, mth_eq_rootLevels,
          pathLevel_append_left H e j _ _ m e1 (by omega) (by omega) (by omega)]
      · rw [if_neg hmk, ih _ (by omega) _ _ (by omega) rfl, mth_eq_rootLevels]
        have := pathLevel_append_right H e j (l.take (split l.length)) (l.drop (split l.length))
          (m - split l.length) e1 (by omega) (by omega)
        rw [e1, ← hk, show split l.length + (m - split l.length) = m by omega] at this
        exact this.symm

end Merkle
