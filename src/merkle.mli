(** Merkle trees as used by transparency logs (RFC 6962 / RFC 9162).

    This is the tree construction behind Certificate Transparency,
    sigstore/Rekor and transparency logs generally: an append-only log
    of leaves, hashed with domain separation ([H(0x00 ‖ leaf)] for
    leaves, [H(0x01 ‖ left ‖ right)] for interior nodes), supporting two
    kinds of efficient, O(log n) proofs:

    - {b inclusion}: leaf [i] is contained in the tree of size [n] with
      root [r];
    - {b consistency}: the tree of size [n] with root [r'] is an
      append-only extension of the earlier tree of size [m] with root
      [r].

    The verification functions are stateless and implement the
    algorithms of RFC 9162 sections 2.1.3.2 and 2.1.4.2 — use them to
    check proofs produced by any conformant log (a CT log's
    [get-proof-by-hash], Rekor's inclusion proofs, ...). The {!S.Log}
    module is an in-memory tree for producing proofs.

    Everything is verified against the Certificate Transparency
    reference test vectors. *)

(** Output signature: a Merkle tree over hash algorithm ['hash]. *)
module type S = sig
  type hash

  val hash_size : int

  (** {1 Hashing primitives (RFC 6962 section 2.1)} *)

  val empty_root : hash
  (** The root of the empty tree: [H("")]. *)

  val leaf_hash : string -> hash
  (** [H(0x00 ‖ data)]. *)

  val node_hash : hash -> hash -> hash
  (** [H(0x01 ‖ left ‖ right)]. *)

  (** {1 Hash conversions} *)

  val equal_hash : hash -> hash -> bool

  val hash_to_raw : hash -> string
  val hash_of_raw : string -> hash
  (** @raise Invalid_argument if the input is not [hash_size] bytes. *)

  val hash_to_hex : hash -> string
  (** Lowercase hexadecimal, [2 * hash_size] characters. *)

  val hash_of_hex : string -> hash
  (** Parses exactly [2 * hash_size] hexadecimal digits, in either case.
      This is deliberately stricter than [Digestif]'s own parser, which
      skips whitespace, zero-pads short input and truncates long input:
      here all of those are rejected, so distinct strings never parse
      to the same hash.
      @raise Invalid_argument if the length is wrong or a character is
      not a hexadecimal digit. *)

  (** {1 Stateless proof verification (RFC 9162)}

      Proofs are lists of sibling hashes, leaf-adjacent first — the
      order produced by {!Log} and by conformant logs. *)

  val verify_inclusion :
    root:hash -> size:int -> index:int -> leaf:hash -> proof:hash list -> bool
  (** [verify_inclusion ~root ~size ~index ~leaf ~proof] checks that the
      leaf whose {!leaf_hash} is [leaf] sits at position [index]
      (0-based) of the tree of [size] leaves whose root is [root]. *)

  val verify_consistency :
    old_size:int ->
    old_root:hash ->
    new_size:int ->
    new_root:hash ->
    proof:hash list ->
    bool
  (** [verify_consistency ~old_size ~old_root ~new_size ~new_root
      ~proof] checks that the tree of size [new_size] is an append-only
      extension of the tree of size [old_size]. The empty tree
      ([old_size = 0], [old_root = empty_root]) is consistent with
      every tree via an empty proof; equal sizes require equal roots
      and an empty proof. *)

  (** {1 In-memory log (proof generation)} *)

  module Log : sig
    type t
    (** An append-only sequence of leaf hashes. Stores one hash per
        leaf; roots and proofs are computed on demand in O(n) time and
        O(log n) stack. Not thread-safe. *)

    val create : unit -> t

    val append : t -> string -> int
    (** Append a leaf (raw data; it is leaf-hashed) and return its
        index. *)

    val append_leaf_hash : t -> hash -> int
    (** Append an already-computed {!leaf_hash}. *)

    val size : t -> int

    val leaf : t -> int -> hash
    (** The leaf hash at an index.
        @raise Invalid_argument if out of bounds. *)

    val root : t -> hash
    (** Root over all current leaves ({!empty_root} when empty). *)

    val root_at : t -> int -> hash
    (** Root of the prefix of the first [n] leaves.
        @raise Invalid_argument unless [0 <= n <= size]. *)

    val inclusion_proof : t -> index:int -> size:int -> hash list
    (** Audit path for [index] within the prefix tree of [size] leaves
        (RFC 6962 section 2.1.1).
        @raise Invalid_argument unless [0 <= index < size <= size t]. *)

    val consistency_proof : t -> old_size:int -> new_size:int -> hash list
    (** Consistency proof between the prefix trees of [old_size] and
        [new_size] leaves (RFC 6962 section 2.1.2).
        @raise Invalid_argument unless
        [0 <= old_size <= new_size <= size t]. *)
  end
end

module Make (H : Digestif.S) : S with type hash = H.t
(** Build a Merkle tree implementation over any [digestif] hash. *)

module SHA256 : S with type hash = Digestif.SHA256.t
(** The RFC 6962 default; what CT logs and Rekor use. *)
