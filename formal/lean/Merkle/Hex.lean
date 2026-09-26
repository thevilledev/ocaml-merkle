/-
  `hash_of_hex`: the strict validation in `src/merkle.ml` in front of
  digestif's lenient parser, and `hash_to_hex`.

  Strings are `List Char`, hashes are their bytes (`List Nat`). The
  digestif side is `Digestif_conv.Make.of_hex` of digestif 1.0.0 to
  1.3.0 (unchanged between them), including its `offset` reference
  threaded through `String.init`, which calls its function on indices
  0, 1, 2, ... in order.
-/

namespace Merkle.Hex

/-- `'0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> true | _ -> false` -/
def isHexDigit (c : Char) : Bool :=
  (48 ≤ c.toNat && c.toNat ≤ 57) || (97 ≤ c.toNat && c.toNat ≤ 102) || (65 ≤ c.toNat && c.toNat ≤ 70)

/-! ## digestif -/

/-- `code`: raises (here `none`) on a non-digit. -/
def code (c : Char) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48)
  else if 65 ≤ c.toNat ∧ c.toNat ≤ 70 then some (c.toNat - 55)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 102 then some (c.toNat - 87)
  else none

/-- `decode chr1 chr2 = Char.chr ((code chr1 lsl 4) lor code chr2)` -/
def decode (c1 c2 : Char) : Option Nat := do
  let a ← code c1
  let b ← code c2
  pure (a * 16 + b)

def isWs (c : Char) : Bool := c = ' ' || c = '\t' || c = '\r' || c = '\n'

/-- `go true idx`: the second digit of a pair (never raises). Returns
    the character and the new `!offset`. -/
def goSecond (s : List Char) (idx off : Nat) : Char × Nat :=
  if h : off + idx < s.length then
    if isWs s[off + idx] then goSecond s idx (off + 1) else (s[off + idx], off)
  else ('\x00', off)
termination_by s.length - (off + idx)

/-- `go false idx`: one output byte. -/
def goFirst (s : List Char) (idx off : Nat) : Option (Nat × Nat) :=
  if h : off + idx < s.length then
    if isWs s[off + idx] then goFirst s idx (off + 1)
    else
      let (c2, off') := goSecond s idx (off + 1)
      if c2 ≠ '\x00' then (decode s[off + idx] c2).map (·, off') else none
  else some (0, off)
termination_by s.length - (off + idx)

/-- `String.init D.digest_size (go false)`, threading `offset`. -/
def ofHexLoop (s : List Char) (n : Nat) (idx off : Nat) : Option (List Nat) :=
  if idx < n then
    match goFirst s idx off with
    | none => none
    | some (b, off') => (ofHexLoop s n (idx + 1) off').map (b :: ·)
  else some []
termination_by n - idx

/-- digestif's `of_hex` for a `size`-byte digest. -/
def digestifOfHex (size : Nat) (s : List Char) : Option (List Nat) := ofHexLoop s size 0 0

/-- digestif's `to_hex`: lowercase. -/
def nibble (x : Nat) : Char := if x < 10 then Char.ofNat (48 + x) else Char.ofNat (97 + (x - 10))

def toHex : List Nat → List Char
  | [] => []
  | v :: vs => nibble (v / 16) :: nibble (v % 16) :: toHex vs

/-! ## `hash_of_hex` -/

/-- OCaml:

      let hash_of_hex s =
        if String.length s <> 2 * H.digest_size then
          invalid_arg "Merkle.hash_of_hex: wrong length";
        if not (String.for_all is_hex_digit s) then
          invalid_arg "Merkle.hash_of_hex: invalid hex";
        H.of_hex s -/
def hashOfHex (size : Nat) (s : List Char) : Option (List Nat) :=
  if s.length ≠ 2 * size then none
  else if !(s.all isHexDigit) then none
  else digestifOfHex size s

/-! ## Characters: finite checks -/

theorem hex_lt (c : Char) (h : isHexDigit c = true) : c.toNat < 128 := by
  simp [isHexDigit] at h; omega

theorem hex_char_facts : ∀ k, k < 128 → isHexDigit (Char.ofNat k) = true →
    isWs (Char.ofNat k) = false ∧ Char.ofNat k ≠ '\x00' ∧
    (∃ v, code (Char.ofNat k) = some v ∧ v < 16 ∧ nibble v = (Char.ofNat k).toLower) := by
  decide

theorem hex_facts (c : Char) (h : isHexDigit c = true) :
    isWs c = false ∧ c ≠ '\x00' ∧ ∃ v, code c = some v ∧ v < 16 ∧ nibble v = c.toLower := by
  have := hex_char_facts c.toNat (hex_lt c h) (by rw [Char.ofNat_toNat]; exact h)
  rwa [Char.ofNat_toNat] at this

/-! ## What the validated parser computes -/

/-- The value of a hex digit (`0` for non-digits; only used on digits). -/
def val (c : Char) : Nat := (code c).getD 0

/-- Pairs of digits, decoded. -/
def pairs : List Char → List Nat
  | c1 :: c2 :: rest => (val c1 * 16 + val c2) :: pairs rest
  | _ => []

theorem getElem_drop' (s : List Char) (k i : Nat) (h : k + i < s.length) :
    s[k + i] = (s.drop k)[i]'(by simp; omega) := by
  simp

/-- On a validated string, digestif reads byte `idx` from positions
    `2 idx` and `2 idx + 1`, with `offset = idx` before and `idx + 1`
    after. -/
theorem ofHexLoop_valid (s : List Char) (n idx : Nat) (hlen : s.length = 2 * n)
    (hhex : ∀ c ∈ s, isHexDigit c = true) (hidx : idx ≤ n) :
    ofHexLoop s n idx idx = some (pairs (s.drop (2 * idx))) := by
  induction h : n - idx generalizing idx with
  | zero =>
    have : idx = n := by omega
    subst this
    rw [ofHexLoop, if_neg (by omega), show s.drop (2 * idx) = [] by
      apply List.eq_nil_of_length_eq_zero; simp; omega]
    rfl
  | succ k ih =>
    have p1 : idx + idx < s.length := by omega
    have p2 : idx + 1 + idx < s.length := by omega
    obtain ⟨w1, _, v1, hv1, _, _⟩ := hex_facts s[idx + idx] (hhex _ (List.getElem_mem p1))
    obtain ⟨w2, z2, v2, hv2, _, _⟩ := hex_facts s[idx + 1 + idx] (hhex _ (List.getElem_mem p2))
    have hs : goSecond s idx (idx + 1) = (s[idx + 1 + idx], idx + 1) := by
      rw [goSecond, dif_pos p2, if_neg (by simp [w2])]
    have hf : goFirst s idx idx = some (v1 * 16 + v2, idx + 1) := by
      rw [goFirst, dif_pos p1, if_neg (by simp [w1])]
      simp only [hs]
      rw [if_pos z2]
      simp [decode, hv1, hv2]
    rw [ofHexLoop, if_pos (by omega), hf]
    simp only
    rw [ih (idx + 1) (by omega) (by omega)]
    -- the drop at `2 idx` starts with the two digits
    have hd : s.drop (2 * idx) = s[idx + idx] :: s[idx + 1 + idx] :: s.drop (2 * (idx + 1)) := by
      rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
        show 2 * idx + 1 + 1 = 2 * (idx + 1) by omega]
      have e1 : s[2 * idx]'(by omega) = s[idx + idx] := by congr 1; omega
      have e2 : s[2 * idx + 1]'(by omega) = s[idx + 1 + idx] := by congr 1; omega
      rw [e1, e2]
    rw [hd]
    simp [pairs, val, hv1, hv2]

/-- `hash_of_hex` accepts exactly the strings of `2 * size` hex digits
    (either case), and decodes them pair by pair. -/
theorem hashOfHex_eq (size : Nat) (s : List Char) :
    hashOfHex size s =
      if s.length = 2 * size ∧ (∀ c ∈ s, isHexDigit c = true) then some (pairs s) else none := by
  unfold hashOfHex
  by_cases hl : s.length = 2 * size
  · rw [if_neg (by simpa using hl)]
    by_cases hh : ∀ c ∈ s, isHexDigit c = true
    · rw [if_neg (by simpa using hh), if_pos ⟨hl, hh⟩, digestifOfHex,
        ofHexLoop_valid s size 0 hl hh (by omega)]
      simp
    · rw [if_pos (by simpa using hh), if_neg (by intro h; exact hh h.2)]
  · rw [if_pos hl, if_neg (by intro h; exact hl h.1)]

/-- Printing a parsed hash gives back the input, lowercased. -/
theorem toHex_pairs (s : List Char) (hhex : ∀ c ∈ s, isHexDigit c = true) (heven : s.length % 2 = 0) :
    toHex (pairs s) = s.map Char.toLower := by
  induction s using pairs.induct with
  | case1 c1 c2 rest ih =>
    obtain ⟨-, -, v1, hv1, hl1, hn1⟩ := hex_facts c1 (hhex c1 (by simp))
    obtain ⟨-, -, v2, hv2, hl2, hn2⟩ := hex_facts c2 (hhex c2 (by simp))
    simp only [pairs, toHex, val, hv1, hv2, Option.getD_some, List.map_cons]
    rw [show (v1 * 16 + v2) / 16 = v1 by omega, show (v1 * 16 + v2) % 16 = v2 by omega, hn1, hn2,
      ih (fun c hc => hhex c (by simp [hc])) (by simp at heven; omega)]
  | case2 l h =>
    match l, h with
    | [], _ => rfl
    | [_], _ => simp at heven
    | _ :: _ :: _, h => exact absurd rfl (h _ _ _)

/-- Consequently two strings parse to the same hash exactly when they
    agree up to letter case. -/
theorem hashOfHex_same_iff (size : Nat) (s t : List Char) (b : List Nat)
    (hs : hashOfHex size s = some b) :
    hashOfHex size t = some b ↔ t.map Char.toLower = s.map Char.toLower ∧ t.length = s.length ∧
      ∀ c ∈ t, isHexDigit c = true := by
  rw [hashOfHex_eq] at hs ⊢
  split at hs
  · rename_i hsv
    simp only [Option.some.injEq] at hs
    subst hs
    constructor
    · intro ht
      split at ht
      · rename_i htv
        simp only [Option.some.injEq] at ht
        rw [← toHex_pairs t htv.2 (by omega), ← toHex_pairs s hsv.2 (by omega), ht]
        exact ⟨rfl, by omega, htv.2⟩
      · simp at ht
    · rintro ⟨hlow, hlen, hhex⟩
      rw [if_pos ⟨by omega, hhex⟩]
      -- `pairs` only depends on the lowercase string
      have key : ∀ (u v : List Char), u.map Char.toLower = v.map Char.toLower →
          (∀ c ∈ u, isHexDigit c = true) → (∀ c ∈ v, isHexDigit c = true) → pairs u = pairs v := by
        intro u
        induction u using pairs.induct with
        | case1 c1 c2 rest ih =>
          intro v huv hu hv
          match v, huv with
          | d1 :: d2 :: rest', huv =>
            simp only [List.map_cons, List.cons.injEq] at huv
            obtain ⟨-, -, a1, ha1, la1, hn1⟩ := hex_facts c1 (hu c1 (by simp))
            obtain ⟨-, -, a2, ha2, la2, hn2⟩ := hex_facts c2 (hu c2 (by simp))
            obtain ⟨-, -, b1, hb1, lb1, hm1⟩ := hex_facts d1 (hv d1 (by simp))
            obtain ⟨-, -, b2, hb2, lb2, hm2⟩ := hex_facts d2 (hv d2 (by simp))
            have nib : ∀ x, x < 16 → ∀ y, y < 16 → nibble x = nibble y → x = y := by decide
            have e1 := nib a1 la1 b1 lb1 (by rw [hn1, hm1, huv.1])
            have e2 := nib a2 la2 b2 lb2 (by rw [hn2, hm2, huv.2.1])
            simp only [pairs, val, ha1, ha2, hb1, hb2, Option.getD_some, e1, e2]
            rw [ih rest' huv.2.2 (fun c hc => hu c (by simp [hc])) (fun c hc => hv c (by simp [hc]))]
          | [], huv => simp at huv
          | [_], huv => simp at huv
        | case2 l h =>
          intro v huv _ _
          match l, h, v, huv with
          | [], _, [], _ => rfl
          | [], _, _ :: _, huv => simp at huv
          | [a], _, [b], _ => rfl
          | [a], _, [], huv => simp at huv
          | [a], _, _ :: _ :: _, huv => simp at huv
          | _ :: _ :: _, h, _, _ => exact absurd rfl (h _ _ _)
      rw [key t s hlow hhex hsv.2]
  · simp at hs

/-- The documented claim "distinct strings never parse to the same
    hash" is false: case is not significant. -/
theorem hashOfHex_not_injective :
    hashOfHex 1 ['A', 'B'] = hashOfHex 1 ['a', 'b'] ∧ hashOfHex 1 ['a', 'b'] = some [171] ∧
      (['A', 'B'] : List Char) ≠ ['a', 'b'] := by
  rw [hashOfHex_eq, hashOfHex_eq]; decide

/-- Round trip: printing then parsing is the identity on byte strings. -/
theorem hashOfHex_toHex (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) :
    hashOfHex bs.length (toHex bs) = some bs := by
  have nibhex : ∀ x, x < 16 → isHexDigit (nibble x) = true ∧ val (nibble x) = x := by decide
  have hlen : ∀ bs : List Nat, (toHex bs).length = 2 * bs.length := by
    intro bs; induction bs with
    | nil => rfl
    | cons b bs ih => simp [toHex, ih]; omega
  have hhex : ∀ bs : List Nat, (∀ b ∈ bs, b < 256) → ∀ c ∈ toHex bs, isHexDigit c = true := by
    intro bs hb; induction bs with
    | nil => simp [toHex]
    | cons b bs ih =>
      have h1 := hb b (by simp)
      intro c hc
      simp only [toHex, List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · exact (nibhex _ (by omega)).1
      · exact (nibhex _ (by omega)).1
      · exact ih (fun b h => hb b (by simp [h])) c hc
  have hpairs : ∀ bs : List Nat, (∀ b ∈ bs, b < 256) → pairs (toHex bs) = bs := by
    intro bs hb; induction bs with
    | nil => rfl
    | cons b bs ih =>
      have h1 := hb b (by simp)
      simp only [toHex, pairs, (nibhex _ (show b / 16 < 16 by omega)).2,
        (nibhex _ (show b % 16 < 16 by omega)).2, ih (fun b h => hb b (by simp [h]))]
      congr 1; omega
  rw [hashOfHex_eq, if_pos ⟨hlen bs, hhex bs hb⟩, hpairs bs hb]

end Merkle.Hex
