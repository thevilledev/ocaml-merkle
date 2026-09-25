-- Which axioms each main result rests on (run by formal/check.sh).
import Merkle
open Merkle
#print axioms verifyInclusion_complete
#print axioms verifyInclusion_sound
#print axioms verifyConsistency_complete
#print axioms verifyConsistency_sound
#print axioms verifyConsistency_rejects_explicit_old_root
#print axioms log_inclusion_verifies
#print axioms log_consistency_verifies
#print axioms Log.appendLeafHash_holds
#print axioms Hex.hashOfHex_eq
#print axioms Hex.hashOfHex_same_iff
#print axioms Hex.hashOfHex_toHex
#print axioms Hex.hashOfHex_not_injective
#print axioms emptyTreeContract_violated
#print axioms fixed_meets_contract
#print axioms fixed_complete
#print axioms fixed_sound
#print axioms Hashing.leafInput_ne_nodeInput
#print axioms Hashing.nodeInput_injective
#print axioms Hashing.collision_of_not_nodeInjective
