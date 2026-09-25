/-
  Consistency proofs: RFC 6962 SUBPROOF, top-down, and the bottom-up
  shape the RFC 9162 verifier expects.
-/
import Merkle.Tree

namespace Merkle

/-! ## `is_pow2` -/

/-- OCaml: `let is_pow2 n = n > 0 && n land (n - 1) = 0`. -/
def isPow2 (n : Nat) : Bool := decide (0 < n) && (n &&& (n - 1) == 0)

theorem isPow2_two_pow (j : Nat) : isPow2 (2 ^ j) = true := by
  simp [isPow2, Nat.two_pow_pos]

theorem isPow2_between {j m : Nat} (h1 : 2 ^ j < m) (h2 : m < 2 * 2 ^ j) : isPow2 m = false := by
  simp only [isPow2, Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
  right
  intro h
  have hbit : ∀ z, z < 2 ^ j → (2 ^ j + z).testBit j = true := by
    intro z hz
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hz]; rfl
  have t1 := hbit (m - 2 ^ j) (by omega)
  have t2 := hbit (m - 1 - 2 ^ j) (by omega)
  rw [show 2 ^ j + (m - 2 ^ j) = m by omega] at t1
  rw [show 2 ^ j + (m - 1 - 2 ^ j) = m - 1 by omega] at t2
  have : (m &&& (m - 1)).testBit j = true := by rw [Nat.testBit_and, t1, t2]; rfl
  rw [h, Nat.zero_testBit] at this
  exact Bool.false_ne_true this

theorem isPow2_iff (m : Nat) : isPow2 m = true ↔ ∃ j, m = 2 ^ j := by
  constructor
  · intro h
    have hm : m ≠ 0 := by intro h0; subst h0; simp [isPow2] at h
    refine ⟨m.log2, ?_⟩
    have l1 := Nat.log2_self_le hm
    have l2 := Nat.lt_log2_self (n := m)
    rw [Nat.pow_succ] at l2
    rcases Nat.lt_or_eq_of_le l1 with hlt | heq
    · rw [isPow2_between hlt (by omega)] at h; exact absurd h (by decide)
    · exact heq.symm
  · rintro ⟨j, rfl⟩; exact isPow2_two_pow j

variable {α : Type} (H : α → α → α) (e : α)

/-! ## SUBPROOF, RFC 6962 section 2.1.2 -/

/-- SUBPROOF(m, D[n], b). As in `src/merkle.ml`; the OCaml recursion
    never terminates for `m = 0`, which `Log.consistency_proof` never
    passes, and this model returns `[]` on the other unreachable input
    (`m ≠ n` with `n < 2`). On the domain `0 < m ≤ n` the two agree. -/
def subproof (m : Nat) (l : List α) (b : Bool) : List α :=
  if m = l.length then (if b then [] else [mth H e l])
  else if h : l.length < 2 then []
  else if m ≤ split l.length then
    subproof m (l.take (split l.length)) b ++ [mth H e (l.drop (split l.length))]
  else
    subproof (m - split l.length) (l.drop (split l.length)) false ++ [mth H e (l.take (split l.length))]
termination_by l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]
  · have := split_lt (n := l.length) (by omega); omega
  · have := split_pos (n := l.length) (by omega); omega

/-! ## Stripping trailing ones -/

/-- The verifier's first loop, on levels: while the old tree's last node
    is a right child, go up. -/
def stripL (x : Nat) (l : List α) : Nat × List α :=
  if x % 2 = 1 then stripL (x / 2) (levelUp H l) else (x, l)
termination_by x
decreasing_by omega

theorem stripL_odd (x : Nat) (l : List α) (h : x % 2 = 1) :
    stripL H x l = stripL H (x / 2) (levelUp H l) := by
  rw [stripL, if_pos h]

theorem stripL_even (x : Nat) (l : List α) (h : ¬ x % 2 = 1) : stripL H x l = (x, l) := by
  rw [stripL, if_neg h]

theorem stripL_rootLevels (x : Nat) (l : List α) :
    rootLevels H e (stripL H x l).2 = rootLevels H e l := by
  induction x using Nat.strongRecOn generalizing l with
  | _ x ih =>
    by_cases h : x % 2 = 1
    · rw [stripL_odd H x l h, ih _ (by omega), rootLevels_levelUp]
    · rw [stripL_even H x l h]

theorem stripL_lt (x : Nat) (l : List α) (hx : x < l.length) :
    (stripL H x l).1 < (stripL H x l).2.length := by
  induction x using Nat.strongRecOn generalizing l with
  | _ x ih =>
    by_cases h : x % 2 = 1
    · rw [stripL_odd H x l h]; exact ih _ (by omega) _ (by rw [length_levelUp]; omega)
    · rw [stripL_even H x l h]; exact hx

theorem stripL_last (x : Nat) (l : List α) (hx : x + 1 = l.length) :
    (stripL H x l).1 + 1 = (stripL H x l).2.length := by
  induction x using Nat.strongRecOn generalizing l with
  | _ x ih =>
    by_cases h : x % 2 = 1
    · rw [stripL_odd H x l h]; exact ih _ (by omega) _ (by rw [length_levelUp]; omega)
    · rw [stripL_even H x l h]; exact hx

theorem stripL_even_result (x : Nat) (l : List α) : ¬ (stripL H x l).1 % 2 = 1 := by
  induction x using Nat.strongRecOn generalizing l with
  | _ x ih =>
    by_cases h : x % 2 = 1
    · rw [stripL_odd H x l h]; exact ih _ (by omega) _
    · rw [stripL_even H x l h]; exact h

theorem stripL_pow (j : Nat) (l : List α) : stripL H (2 ^ j - 1) l = (0, lvl H j l) := by
  induction j generalizing l with
  | zero => rw [stripL_even H _ _ (by simp)]; rfl
  | succ j ih =>
    have : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ]; omega
    have hp := Nat.two_pow_pos j
    rw [stripL_odd H _ _ (by omega), show (2 ^ (j + 1) - 1) / 2 = 2 ^ j - 1 by omega, ih]
    rfl

/-- Old and new trees that agree on the first `x + 1` leaves keep
    agreeing while the old tree's last node is stripped upwards. -/
theorem stripL_agree (x : Nat) (O N : List α) (hO : x + 1 = O.length) (hN : x < N.length)
    (hag : ∀ i, i ≤ x → get e O i = get e N i) :
    (stripL H x O).1 = (stripL H x N).1 ∧
    (stripL H x N).1 < (stripL H x N).2.length ∧
    ∀ i, i ≤ (stripL H x O).1 → get e (stripL H x O).2 i = get e (stripL H x N).2 i := by
  induction x using Nat.strongRecOn generalizing O N with
  | _ x ih =>
    by_cases h : x % 2 = 1
    · rw [stripL_odd H x O h, stripL_odd H x N h]
      apply ih _ (by omega)
      · rw [length_levelUp]; omega
      · rw [length_levelUp]; omega
      · intro i hi
        rw [get_levelUp_pair H e O i (by omega), get_levelUp_pair H e N i (by omega),
          hag _ (by omega), hag _ (by omega)]
    · rw [stripL_even H x O h, stripL_even H x N h]
      exact ⟨rfl, hN, hag⟩

/-! ## The consistency proof, bottom-up -/

/-- What the RFC 9162 verifier consumes: the old tree's last complete
    subtree (omitted when the old tree is itself complete and `b`), then
    that subtree's audit path in the new tree. -/
def conLevel (m : Nat) (l : List α) (b : Bool) : List α :=
  (if b && isPow2 m then [] else [get e (stripL H (m - 1) l).2 (stripL H (m - 1) l).1])
    ++ pathLevel H e (stripL H (m - 1) l).1 (stripL H (m - 1) l).2

/-- S1: the old tree ends inside a perfect left subtree. -/
theorem stripL_append_left : ∀ (j : Nat) (A B : List α) (x : Nat),
    A.length = 2 ^ j → x + 1 < A.length → 1 ≤ B.length → B.length ≤ A.length →
    ∃ i B', stripL H x (A ++ B) = ((stripL H x A).1, (stripL H x A).2 ++ B') ∧
      (stripL H x A).2.length = 2 ^ i ∧ 1 ≤ B'.length ∧ B'.length ≤ 2 ^ i ∧
      rootLevels H e B' = rootLevels H e B
  | 0, A, B, x, hA, hx, _, _ => by rw [hA] at hx; simp at hx
  | j + 1, A, B, x, hA, hx, hB1, hB2 => by
    have hA2 : A.length % 2 = 0 := by rw [hA, Nat.pow_succ]; omega
    by_cases h : x % 2 = 1
    · rw [stripL_odd H x _ h, stripL_odd H x A h, levelUp_append H A B hA2]
      have hlA : (levelUp H A).length = 2 ^ j := by
        rw [length_levelUp, hA, Nat.pow_succ]; omega
      obtain ⟨i, B', h1, h2, h3, h4, h5⟩ :=
        stripL_append_left j (levelUp H A) (levelUp H B) (x / 2) hlA
          (by rw [hlA]; rw [hA, Nat.pow_succ] at hx; omega)
          (by rw [length_levelUp]; omega) (by rw [hlA, length_levelUp]; rw [hA, Nat.pow_succ] at hB2; omega)
      exact ⟨i, B', h1, h2, h3, h4, by rw [h5, rootLevels_levelUp]⟩
    · rw [stripL_even H x _ h, stripL_even H x A h]
      exact ⟨j + 1, B, rfl, hA, hB1, by omega, rfl⟩

/-- S2: the old tree is exactly the perfect left subtree. -/
theorem stripL_append_exact : ∀ (j : Nat) (A B : List α),
    A.length = 2 ^ j → 1 ≤ B.length → B.length ≤ A.length →
    stripL H (2 ^ j - 1) (A ++ B) = (0, [rootLevels H e A, rootLevels H e B])
  | 0, A, B, hA, hB1, hB2 => by
    match A, B, hA with
    | [a], [b], _ => rw [stripL_even H _ _ (by simp)]; simp [rootLevels_single]
    | [a], [], _ => simp at hB1
    | [a], _ :: _ :: _, _ => simp at hB2
  | j + 1, A, B, hA, hB1, hB2 => by
    have hA2 : A.length % 2 = 0 := by rw [hA, Nat.pow_succ]; omega
    have hp := Nat.two_pow_pos j
    have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ]; omega
    have hlA : (levelUp H A).length = 2 ^ j := by rw [length_levelUp, hA]; omega
    rw [stripL_odd H _ _ (by omega), levelUp_append H A B hA2,
      show (2 ^ (j + 1) - 1) / 2 = 2 ^ j - 1 by omega,
      stripL_append_exact j (levelUp H A) (levelUp H B) hlA
        (by rw [length_levelUp]; omega) (by rw [hlA, length_levelUp]; omega),
      rootLevels_levelUp, rootLevels_levelUp]

/-- S3: the old tree ends inside the right subtree. -/
theorem stripL_append_right : ∀ (j : Nat) (A B : List α) (y : Nat),
    A.length = 2 ^ j → y + 1 < B.length → B.length ≤ A.length →
    ∃ A', stripL H (A.length + y) (A ++ B) =
        (A'.length + (stripL H y B).1, A' ++ (stripL H y B).2) ∧
      (∃ i, A'.length = 2 ^ i) ∧ (stripL H y B).2.length ≤ A'.length ∧
      rootLevels H e A' = rootLevels H e A
  | 0, A, B, y, hA, hy, hB => by rw [hA] at hB; simp at hB; omega
  | j + 1, A, B, y, hA, hy, hB => by
    have hA2 : A.length % 2 = 0 := by rw [hA, Nat.pow_succ]; omega
    by_cases h : y % 2 = 1
    · have hlA : (levelUp H A).length = 2 ^ j := by
        rw [length_levelUp, hA, Nat.pow_succ]; omega
      rw [stripL_odd H _ _ (by omega), stripL_odd H y B h, levelUp_append H A B hA2,
        show (A.length + y) / 2 = (levelUp H A).length + y / 2 by rw [length_levelUp]; omega]
      obtain ⟨A', h1, h2, h3, h4⟩ :=
        stripL_append_right j (levelUp H A) (levelUp H B) (y / 2) hlA
          (by rw [length_levelUp]; omega) (by rw [hlA, length_levelUp]; rw [hA, Nat.pow_succ] at hB; omega)
      exact ⟨A', h1, h2, h3, by rw [h4, rootLevels_levelUp]⟩
    · rw [stripL_even H _ _ (by omega), stripL_even H y B h]
      exact ⟨A, rfl, ⟨j + 1, hA⟩, by omega, rfl⟩

/-- SUBPROOF is the bottom-up consistency proof. -/
theorem subproof_eq_conLevel (m : Nat) (l : List α) (b : Bool) (hm0 : 0 < m) (hm : m < l.length) :
    subproof H e m l b = conLevel H e m l b := by
  induction h : l.length using Nat.strongRecOn generalizing l m b with
  | _ n ih =>
    have hl : ¬ l.length < 2 := by omega
    obtain ⟨j, hk, hk1, hk2⟩ := split_spec (n := l.length) (by omega)
    have e1 : (l.take (split l.length)).length = 2 ^ j := by simp [hk]; omega
    have e2 : (l.drop (split l.length)).length = l.length - 2 ^ j := by simp [hk]
    have hsplit := List.take_append_drop (split l.length) l
    have hc : conLevel H e m l b =
        conLevel H e m (l.take (split l.length) ++ l.drop (split l.length)) b := by rw [hsplit]
    unfold subproof
    rw [if_neg (by omega), dif_neg hl, hc]
    have ihA := fun m' b' (h0 : 0 < m') (h1 : m' < (l.take (split l.length)).length) =>
      ih _ (by omega) m' (l.take (split l.length)) b' h0 h1 rfl
    have ihB := fun m' b' (h0 : 0 < m') (h1 : m' < (l.drop (split l.length)).length) =>
      ih _ (by omega) m' (l.drop (split l.length)) b' h0 h1 rfl
    rw [hk] at *
    generalize l.take (2 ^ j) = A at *
    generalize l.drop (2 ^ j) = B at *
    have hB1 : 1 ≤ B.length := by omega
    have hB2 : B.length ≤ A.length := by omega
    rw [mth_eq_rootLevels, mth_eq_rootLevels]
    by_cases hmk : m < 2 ^ j
    · -- old tree inside the left subtree
      rw [if_pos (by omega), ihA m b hm0 (by omega)]
      obtain ⟨i, B', h1, h2, h3, h4, h5⟩ := stripL_append_left H e j A B (m - 1) e1 (by omega) hB1 hB2
      unfold conLevel
      rw [h1]
      have hf := stripL_lt H (m - 1) A (by omega)
      rw [get_append_left e _ _ _ hf, pathLevel_append_left H e i _ B' _ h2 hf h3 (by omega), h5]
      simp
    · by_cases hmk' : m = 2 ^ j
      · -- old tree is exactly the left subtree
        subst hmk'
        rw [if_pos (by omega)]
        unfold subproof
        rw [if_pos (by omega)]
        unfold conLevel
        rw [stripL_append_exact H e j A B e1 hB1 hB2, isPow2_two_pow, mth_eq_rootLevels,
          pathLevel_long H e _ _ (by simp)]
        cases b <;> simp [pathLevel_short]
      · -- old tree ends in the right subtree
        rw [if_neg (by omega), ihB (m - 2 ^ j) false (by omega) (by omega)]
        obtain ⟨A', h1, ⟨i, h2⟩, h3, h4⟩ := stripL_append_right H e j A B (m - 2 ^ j - 1) e1
          (by omega) hB2
        unfold conLevel
        rw [e1, show 2 ^ j + (m - 2 ^ j - 1) = m - 1 by omega] at h1
        rw [h1, isPow2_between (j := j) (m := m) (by omega) (by omega)]
        have hf := stripL_lt H (m - 2 ^ j - 1) B (by omega)
        rw [get_append_right, pathLevel_append_right H e i A' _ _ h2 hf h3, h4]
        simp [show m - 2 ^ j - 1 = m - 1 - 2 ^ j by omega]

end Merkle
