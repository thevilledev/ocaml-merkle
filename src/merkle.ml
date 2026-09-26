module type S = sig
  type hash

  val hash_size : int
  val empty_root : hash
  val leaf_hash : string -> hash
  val node_hash : hash -> hash -> hash
  val equal_hash : hash -> hash -> bool
  val hash_to_raw : hash -> string
  val hash_of_raw : string -> hash
  val hash_to_hex : hash -> string
  val hash_of_hex : string -> hash

  val verify_inclusion :
    root:hash -> size:int -> index:int -> leaf:hash -> proof:hash list -> bool

  val verify_consistency :
    old_size:int ->
    old_root:hash ->
    new_size:int ->
    new_root:hash ->
    proof:hash list ->
    bool

  module Log : sig
    type t

    val create : unit -> t
    val append : t -> string -> int
    val append_leaf_hash : t -> hash -> int
    val size : t -> int
    val leaf : t -> int -> hash
    val root : t -> hash
    val root_at : t -> int -> hash
    val inclusion_proof : t -> index:int -> size:int -> hash list
    val consistency_proof : t -> old_size:int -> new_size:int -> hash list
  end
end

module Make (H : Digestif.S) : S with type hash = H.t = struct
  type hash = H.t

  let hash_size = H.digest_size
  let empty_root = H.digest_string ""

  let leaf_hash data =
    H.get (H.feed_string (H.feed_string H.empty "\x00") data)

  let node_hash l r =
    H.get
      (H.feed_string
         (H.feed_string
            (H.feed_string H.empty "\x01")
            (H.to_raw_string l))
         (H.to_raw_string r))

  let equal_hash = H.equal
  let hash_to_raw = H.to_raw_string

  let hash_of_raw s =
    if String.length s <> H.digest_size then
      invalid_arg "Merkle.hash_of_raw: wrong length";
    H.of_raw_string s

  let hash_to_hex = H.to_hex

  let is_hex_digit = function
    | '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> true
    | _ -> false

  (* Digestif's own hex parser is lenient: it skips whitespace, zero-pads
     short input and truncates long input, so strings that differ in
     more than letter case would parse to the same hash. Validate
     strictly before handing over. *)
  let hash_of_hex s =
    if String.length s <> 2 * H.digest_size then
      invalid_arg "Merkle.hash_of_hex: wrong length";
    if not (String.for_all is_hex_digit s) then
      invalid_arg "Merkle.hash_of_hex: invalid hex";
    H.of_hex s

  (* Largest power of two strictly smaller than n (n >= 2). *)
  let split n =
    let k = ref 1 in
    while !k * 2 < n do
      k := !k * 2
    done;
    !k

  (* MTH over leaves.(lo) .. leaves.(hi-1), RFC 6962 section 2.1. *)
  let rec mth leaves lo hi =
    let n = hi - lo in
    if n = 0 then empty_root
    else if n = 1 then leaves.(lo)
    else begin
      let k = split n in
      node_hash (mth leaves lo (lo + k)) (mth leaves (lo + k) hi)
    end

  (* PATH(m, D[n]), RFC 6962 section 2.1.1; [m] relative to [lo, hi). *)
  let rec path leaves m lo hi =
    let n = hi - lo in
    if n <= 1 then []
    else begin
      let k = split n in
      if m < k then path leaves m lo (lo + k) @ [ mth leaves (lo + k) hi ]
      else path leaves (m - k) (lo + k) hi @ [ mth leaves lo (lo + k) ]
    end

  (* SUBPROOF(m, D[n], b), RFC 6962 section 2.1.2. *)
  let rec subproof leaves m lo hi known_root =
    let n = hi - lo in
    if m = n then if known_root then [] else [ mth leaves lo hi ]
    else begin
      let k = split n in
      if m <= k then
        subproof leaves m lo (lo + k) known_root @ [ mth leaves (lo + k) hi ]
      else
        subproof leaves (m - k) (lo + k) hi false @ [ mth leaves lo (lo + k) ]
    end

  (* RFC 9162 section 2.1.3.2. *)
  let verify_inclusion ~root ~size ~index ~leaf ~proof =
    if index < 0 || size < 1 || index >= size then false
    else begin
      let fn = ref index and sn = ref (size - 1) in
      let r = ref leaf in
      let ok = ref true in
      List.iter
        (fun p ->
          if !ok then begin
            if !sn = 0 then ok := false
            else begin
              if !fn land 1 = 1 || !fn = !sn then begin
                r := node_hash p !r;
                if !fn land 1 = 0 then
                  while not (!fn land 1 = 1 || !fn = 0) do
                    fn := !fn lsr 1;
                    sn := !sn lsr 1
                  done
              end
              else r := node_hash !r p;
              fn := !fn lsr 1;
              sn := !sn lsr 1
            end
          end)
        proof;
      !ok && !sn = 0 && H.equal !r root
    end

  let is_pow2 n = n > 0 && n land (n - 1) = 0

  (* RFC 9162 section 2.1.4.2. *)
  let verify_consistency ~old_size ~old_root ~new_size ~new_root ~proof =
    if old_size < 0 || new_size < old_size then false
    else if old_size = new_size then
      (* the empty tree's only valid root is H(""), even when the new
         tree is empty too *)
      proof = [] && H.equal old_root new_root
      && (old_size > 0 || H.equal old_root empty_root)
    else if old_size = 0 then
      (* the empty tree, whose only valid root is H(""), is consistent
         with everything via an empty proof *)
      proof = [] && H.equal old_root empty_root
    else begin
      (* 0 < old_size < new_size *)
      let proof = if is_pow2 old_size then old_root :: proof else proof in
      match proof with
      | [] -> false
      | first :: rest ->
        let fn = ref (old_size - 1) and sn = ref (new_size - 1) in
        while !fn land 1 = 1 do
          fn := !fn lsr 1;
          sn := !sn lsr 1
        done;
        let fr = ref first and sr = ref first in
        let ok = ref true in
        List.iter
          (fun c ->
            if !ok then begin
              if !sn = 0 then ok := false
              else begin
                if !fn land 1 = 1 || !fn = !sn then begin
                  fr := node_hash c !fr;
                  sr := node_hash c !sr;
                  if !fn land 1 = 0 then
                    while not (!fn land 1 = 1 || !fn = 0) do
                      fn := !fn lsr 1;
                      sn := !sn lsr 1
                    done
                end
                else sr := node_hash !sr c;
                fn := !fn lsr 1;
                sn := !sn lsr 1
              end
            end)
          rest;
        !ok && !sn = 0 && H.equal !fr old_root && H.equal !sr new_root
    end

  module Log = struct
    type t = { mutable leaves : hash array; mutable len : int }

    let create () = { leaves = [||]; len = 0 }

    let ensure t n =
      if n > Array.length t.leaves then begin
        let cap = max 16 (max n (2 * Array.length t.leaves)) in
        let a = Array.make cap empty_root in
        Array.blit t.leaves 0 a 0 t.len;
        t.leaves <- a
      end

    let append_leaf_hash t h =
      ensure t (t.len + 1);
      t.leaves.(t.len) <- h;
      t.len <- t.len + 1;
      t.len - 1

    let append t data = append_leaf_hash t (leaf_hash data)
    let size t = t.len

    let leaf t i =
      if i < 0 || i >= t.len then invalid_arg "Merkle.Log.leaf: out of bounds";
      t.leaves.(i)

    let root_at t n =
      if n < 0 || n > t.len then invalid_arg "Merkle.Log.root_at: bad size";
      mth t.leaves 0 n

    let root t = root_at t t.len

    let inclusion_proof t ~index ~size =
      if size < 1 || size > t.len || index < 0 || index >= size then
        invalid_arg "Merkle.Log.inclusion_proof: bad index/size";
      path t.leaves index 0 size

    let consistency_proof t ~old_size ~new_size =
      if old_size < 0 || old_size > new_size || new_size > t.len then
        invalid_arg "Merkle.Log.consistency_proof: bad sizes";
      if old_size = new_size || old_size = 0 then []
      else subproof t.leaves old_size 0 new_size true
  end
end

module SHA256 = Make (Digestif.SHA256)
