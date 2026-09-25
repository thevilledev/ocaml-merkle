/-
  The hashing primitives, down to the bytes they feed the hash:

      let leaf_hash data = H.get (H.feed_string (H.feed_string H.empty "\x00") data)
      let node_hash l r  = H.get (... "\x01" ... (H.to_raw_string l) ... (H.to_raw_string r))

  i.e. `leaf_hash d = H (0x00 ‖ d)` and `node_hash l r = H (0x01 ‖ l ‖ r)`
  with `l`, `r` raw digests of `hash_size` bytes.

  SHA-256 itself is not modelled. What is proved is that the inputs are
  unambiguous, which is what turns the soundness theorems' assumption
  (`NodeInjective`: no two different child pairs share a node hash) and
  the RFC 6962 second-preimage defence into plain collision resistance:
  two different node hashes of equal value, or a node hash equal to a
  leaf hash, are two *different inputs* with the same digest.
-/
import Merkle.Verify

namespace Merkle.Hashing

abbrev Bytes := List UInt8

def leafInput (d : Bytes) : Bytes := 0x00 :: d
def nodeInput (l r : Bytes) : Bytes := 0x01 :: (l ++ r)

/-- Domain separation: no leaf input is a node input. -/
theorem leafInput_ne_nodeInput (d l r : Bytes) : leafInput d ≠ nodeInput l r := by
  simp [leafInput, nodeInput]

/-- With digests of a fixed size, a node input determines its children. -/
theorem nodeInput_injective (n : Nat) (l r l' r' : Bytes) (hl : l.length = n) (hl' : l'.length = n)
    (h : nodeInput l r = nodeInput l' r') : l = l' ∧ r = r' := by
  simp only [nodeInput, List.cons.injEq, true_and] at h
  have hl : l.length = l'.length := by rw [hl, hl']
  exact List.append_inj h hl

/-- A leaf input determines the entry. -/
theorem leafInput_injective (d d' : Bytes) (h : leafInput d = leafInput d') : d = d' := by
  simpa [leafInput] using h

/-- The reduction. Let `hash : Bytes → Bytes` be any function, and
    `nodeHash l r = hash (nodeInput l r)` on children of `n` bytes. If two
    different child pairs have the same node hash, `hash` has a collision
    (two different inputs, one output): `NodeInjective` holds unless one
    has been found. -/
theorem collision_of_not_nodeInjective (n : Nat) (hash : Bytes → Bytes)
    (a b c d : Bytes) (ha : a.length = n) (hc : c.length = n)
    (hne : ¬ (a = c ∧ b = d)) (heq : hash (nodeInput a b) = hash (nodeInput c d)) :
    nodeInput a b ≠ nodeInput c d ∧ hash (nodeInput a b) = hash (nodeInput c d) :=
  ⟨fun h => hne (nodeInput_injective n a b c d ha hc h), heq⟩

end Merkle.Hashing
