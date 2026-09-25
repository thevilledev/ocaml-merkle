/-
  `split n`: the largest power of two strictly smaller than `n`.

  OCaml (src/merkle.ml):

      let split n =
        let k = ref 1 in
        while !k * 2 < n do k := !k * 2 done;
        !k

  Modelled over `Nat`. The OCaml loop can only differ from this model
  if `!k * 2` overflows, which needs `n > 2^61`: `split` is only called
  on the size of a sub-range of an OCaml array, and arrays are far
  smaller than that (`Sys.max_array_length` is 2^54 - 1 on 64-bit and
  2^22 - 1 on 32-bit platforms).
-/

namespace Merkle

def splitLoop (k n : Nat) : Nat :=
  if k = 0 then 0 else if k * 2 < n then splitLoop (k * 2) n else k
termination_by n - k
decreasing_by omega

def split (n : Nat) : Nat := splitLoop 1 n

theorem splitLoop_spec (n : Nat) :
    ∀ j, 2 ^ j < n → ∃ j', splitLoop (2 ^ j) n = 2 ^ j' ∧ 2 ^ j' < n ∧ n ≤ 2 * 2 ^ j' := by
  intro j hj
  -- induction on the measure n - 2^j
  induction h : n - 2 ^ j using Nat.strongRecOn generalizing j with
  | _ m ih =>
    have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
    unfold splitLoop
    rw [if_neg (by omega)]
    by_cases hc : 2 ^ j * 2 < n
    · rw [if_pos hc]
      have : 2 ^ j * 2 = 2 ^ (j + 1) := (Nat.pow_succ 2 j).symm
      rw [this] at hc ⊢
      exact ih (n - 2 ^ (j + 1)) (by omega) (j + 1) hc rfl
    · rw [if_neg hc]
      exact ⟨j, rfl, hj, by omega⟩

/-- For `n ≥ 2`, `split n = 2^j` with `2^j < n ≤ 2^(j+1)`. -/
theorem split_spec {n : Nat} (hn : 2 ≤ n) :
    ∃ j, split n = 2 ^ j ∧ 2 ^ j < n ∧ n ≤ 2 * 2 ^ j := by
  have := splitLoop_spec n 0 (by simp; omega)
  simpa [split] using this

theorem split_pos {n : Nat} (hn : 2 ≤ n) : 0 < split n := by
  obtain ⟨j, h, -, -⟩ := split_spec hn
  rw [h]; exact Nat.two_pow_pos j

theorem split_lt {n : Nat} (hn : 2 ≤ n) : split n < n := by
  obtain ⟨j, h, h1, -⟩ := split_spec hn
  omega

theorem split_ge {n : Nat} (hn : 2 ≤ n) : n ≤ 2 * split n := by
  obtain ⟨j, h, -, h2⟩ := split_spec hn
  omega

/-- The split is the unique power of two in `[n/2, n)`: any `2^j` with
    `2^j < n ≤ 2^(j+1)` is it. -/
theorem split_unique {n j : Nat} (h1 : 2 ^ j < n) (h2 : n ≤ 2 * 2 ^ j) :
    split n = 2 ^ j := by
  have hn : 2 ≤ n := by have := Nat.one_le_two_pow (n := j); omega
  obtain ⟨j', h, h1', h2'⟩ := split_spec hn
  rw [h]
  -- 2^j and 2^j' are both in [n/2, n): they are equal
  rcases Nat.lt_trichotomy j j' with hlt | heq | hgt
  · have : 2 ^ (j + 1) ≤ 2 ^ j' := Nat.pow_le_pow_right (by omega) hlt
    rw [Nat.pow_succ] at this; omega
  · rw [heq]
  · have : 2 ^ (j' + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hgt
    rw [Nat.pow_succ] at this; omega

/-- If the split of `n` is `k` and `k < m ≤ n`, the split of `m` is `k`
    too: the old and new trees of a consistency proof share their left
    subtree. -/
theorem split_of_between {n m : Nat} (hn : 2 ≤ n) (hk : split n < m) (hm : m ≤ n) :
    split m = split n := by
  obtain ⟨j, h, h1, h2⟩ := split_spec hn
  rw [h] at hk ⊢
  exact split_unique hk (by omega)

end Merkle
