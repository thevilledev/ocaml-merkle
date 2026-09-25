(* Known-answer tests from the Certificate Transparency reference
   implementation (google/certificate-transparency,
   cpp/merkletree/merkle_tree_test.cc), which defined the canonical
   RFC 6962 test vectors, and from the Go reference implementation for
   larger trees (reference_vectors.ml); independent oracles; targeted
   tests for each guard of the verifiers; property tests. *)

module M = Merkle.SHA256

(* ---------- hash-generic helpers, oracles and laws ----------

   The library computes roots by the recursive definition of RFC 6962
   and verifies proofs with the iterative, bit-twiddling algorithms of
   RFC 9162. The oracles here deliberately do both the other way round
   -- roots bottom-up, verification by structural recursion -- so that
   agreement is evidence rather than tautology. *)

module Suite (M : Merkle.S) = struct
  let leaf_data i = Printf.sprintf "leaf-%d" i

  let build_log n =
    let log = M.Log.create () in
    for i = 0 to n - 1 do
      ignore (M.Log.append log (leaf_data i))
    done;
    log

  let flip_bit h =
    let raw = Bytes.of_string (M.hash_to_raw h) in
    Bytes.set raw 0 (Char.chr (Char.code (Bytes.get raw 0) lxor 1));
    M.hash_of_raw (Bytes.to_string raw)

  (* Root by the incremental "frontier" method logs use in practice: a
     stack of perfect-subtree roots, merged whenever the two on top have
     equal height, then folded right to left. Shares nothing with the
     library's recursion, and nothing with its storage. *)
  let frontier_root leaf_hashes =
    let rec push height h = function
      | (height', l) :: rest when height' = height ->
        push (height + 1) (M.node_hash l h) rest
      | stack -> (height, h) :: stack
    in
    match List.fold_left (fun st h -> push 0 h st) [] leaf_hashes with
    | [] -> M.empty_root
    | (_, top) :: rest ->
      List.fold_left (fun acc (_, l) -> M.node_hash l acc) top rest

  (* largest power of two strictly smaller than n (n >= 2) *)
  let split n =
    let rec go k = if 2 * k < n then go (2 * k) else k in
    go 1

  (* RFC 6962 section 2.1.1, read backwards:
       PATH(m, D[n]) = PATH(m, D[0:k]) : MTH(D[k:n])      for m < k
                     = PATH(m - k, D[k:n]) : MTH(D[0:k])  for m >= k
     so the last hash of a path is the sibling just below the root. *)
  let rec root_of_path ~index ~size ~leaf rev_path =
    if size = 1 then match rev_path with [] -> Some leaf | _ -> None
    else
      match rev_path with
      | [] -> None
      | top :: rest ->
        let k = split size in
        if index < k then
          Option.map
            (fun l -> M.node_hash l top)
            (root_of_path ~index ~size:k ~leaf rest)
        else
          Option.map
            (fun r -> M.node_hash top r)
            (root_of_path ~index:(index - k) ~size:(size - k) ~leaf rest)

  let oracle_verify_inclusion ~root ~size ~index ~leaf ~proof =
    index >= 0 && index < size
    &&
    match root_of_path ~index ~size ~leaf (List.rev proof) with
    | Some r -> M.equal_hash r root
    | None -> false

  (* RFC 6962 section 2.1.2, read backwards: SUBPROOF(m, D[n], b) yields
     the (old, new) subtree roots the proof commits to. *)
  let rec roots_of_subproof ~m ~n ~b ~old_root rev_proof =
    if m = n then
      match (b, rev_proof) with
      | true, [] -> Some (old_root, old_root)
      | false, [ h ] -> Some (h, h)
      | _ -> None
    else
      match rev_proof with
      | [] -> None
      | top :: rest ->
        let k = split n in
        if m <= k then
          (* top = MTH(D[k:n]): only the new tree reaches it *)
          Option.map
            (fun (o, nw) -> (o, M.node_hash nw top))
            (roots_of_subproof ~m ~n:k ~b ~old_root rest)
        else
          (* top = MTH(D[0:k]): common to both trees *)
          Option.map
            (fun (o, nw) -> (M.node_hash top o, M.node_hash top nw))
            (roots_of_subproof ~m:(m - k) ~n:(n - k) ~b:false ~old_root rest)

  (* the three special cases are the library's documented conventions
     rather than part of the RFC algorithm *)
  let oracle_verify_consistency ~old_size ~old_root ~new_size ~new_root ~proof =
    if old_size < 0 || new_size < old_size then false
    else if old_size = new_size then
      proof = [] && M.equal_hash old_root new_root
    else if old_size = 0 then proof = [] && M.equal_hash old_root M.empty_root
    else
      match
        roots_of_subproof ~m:old_size ~n:new_size ~b:true ~old_root
          (List.rev proof)
      with
      | Some (o, nw) -> M.equal_hash o old_root && M.equal_hash nw new_root
      | None -> false

  (* ----- laws that must hold for every hash algorithm ----- *)

  let n_laws = 70

  let test_storage_and_roots () =
    let log = M.Log.create () in
    let hashes = ref [] in
    Alcotest.(check int) "empty size" 0 (M.Log.size log);
    for i = 0 to n_laws - 1 do
      (* append reports the index it assigned *)
      Alcotest.(check int)
        (Printf.sprintf "append %d" i)
        i
        (M.Log.append log (leaf_data i));
      Alcotest.(check int) "size" (i + 1) (M.Log.size log);
      hashes := M.leaf_hash (leaf_data i) :: !hashes;
      Alcotest.(check string)
        (Printf.sprintf "root after %d appends" (i + 1))
        (M.hash_to_hex (frontier_root (List.rev !hashes)))
        (M.hash_to_hex (M.Log.root log))
    done;
    (* n_laws exceeds the log's initial capacity several times over:
       every leaf must have survived the reallocations, and every prefix
       root must still be derivable *)
    let all = List.rev !hashes in
    List.iteri
      (fun i h ->
        Alcotest.(check string)
          (Printf.sprintf "leaf %d" i)
          (M.hash_to_hex h)
          (M.hash_to_hex (M.Log.leaf log i)))
      all;
    for n = 0 to n_laws do
      Alcotest.(check string)
        (Printf.sprintf "root_at %d" n)
        (M.hash_to_hex (frontier_root (List.filteri (fun i _ -> i < n) all)))
        (M.hash_to_hex (M.Log.root_at log n))
    done

  let test_proofs () =
    let log = build_log n_laws in
    for size = 1 to n_laws do
      let root = M.Log.root_at log size in
      for index = 0 to size - 1 do
        let proof = M.Log.inclusion_proof log ~index ~size in
        let leaf = M.Log.leaf log index in
        if not (M.verify_inclusion ~root ~size ~index ~leaf ~proof) then
          Alcotest.failf "inclusion (%d, %d) does not verify" index size;
        if not (oracle_verify_inclusion ~root ~size ~index ~leaf ~proof) then
          Alcotest.failf "inclusion (%d, %d) rejected by the oracle" index size
      done
    done;
    for new_size = 0 to n_laws do
      let new_root = M.Log.root_at log new_size in
      for old_size = 0 to new_size do
        let old_root = M.Log.root_at log old_size in
        let proof = M.Log.consistency_proof log ~old_size ~new_size in
        if
          not
            (M.verify_consistency ~old_size ~old_root ~new_size ~new_root
               ~proof)
        then
          Alcotest.failf "consistency (%d, %d) does not verify" old_size
            new_size;
        if
          not
            (oracle_verify_consistency ~old_size ~old_root ~new_size ~new_root
               ~proof)
        then
          Alcotest.failf "consistency (%d, %d) rejected by the oracle" old_size
            new_size
      done
    done

  let test_hash_conversions () =
    let h = M.leaf_hash "hello" in
    let raw = M.hash_to_raw h and hex = M.hash_to_hex h in
    Alcotest.(check int) "raw length" M.hash_size (String.length raw);
    Alcotest.(check int) "hex length" (2 * M.hash_size) (String.length hex);
    Alcotest.(check int)
      "empty_root length" M.hash_size
      (String.length (M.hash_to_raw M.empty_root));
    Alcotest.(check bool)
      "raw round-trip" true
      (M.equal_hash h (M.hash_of_raw raw));
    Alcotest.(check bool)
      "hex round-trip" true
      (M.equal_hash h (M.hash_of_hex hex));
    Alcotest.(check string) "hex is lowercase" (String.lowercase_ascii hex) hex;
    Alcotest.(check bool)
      "uppercase hex accepted" true
      (M.equal_hash h (M.hash_of_hex (String.uppercase_ascii hex)));
    (* case is the only freedom: printing a parsed string gives it back
       in lowercase, whatever mix of cases it came in *)
    let mixed =
      String.mapi
        (fun i c -> if i mod 2 = 0 then Char.uppercase_ascii c else c)
        hex
    in
    Alcotest.(check string)
      "mixed-case hex round-trips to lowercase" hex
      (M.hash_to_hex (M.hash_of_hex mixed));
    let raw_rejected name s =
      Alcotest.check_raises name
        (Invalid_argument "Merkle.hash_of_raw: wrong length") (fun () ->
          ignore (M.hash_of_raw s))
    in
    raw_rejected "raw: empty" "";
    raw_rejected "raw: one short" (String.sub raw 0 (M.hash_size - 1));
    raw_rejected "raw: one long" (raw ^ "\x00");
    let hex_rejected name why s =
      Alcotest.check_raises name
        (Invalid_argument ("Merkle.hash_of_hex: " ^ why)) (fun () ->
          ignore (M.hash_of_hex s))
    in
    let n = String.length hex in
    (* Digestif's lenient parser accepts all of these but the odd one *)
    hex_rejected "hex: empty" "wrong length" "";
    hex_rejected "hex: short" "wrong length" (String.sub hex 0 (n - 2));
    hex_rejected "hex: long" "wrong length" (hex ^ "00");
    hex_rejected "hex: trailing newline" "wrong length" (hex ^ "\n");
    hex_rejected "hex: leading space" "wrong length" (" " ^ hex);
    hex_rejected "hex: odd length" "wrong length" (String.sub hex 0 (n - 1));
    hex_rejected "hex: 0x prefix" "wrong length" ("0x" ^ hex);
    (* right length, wrong alphabet *)
    hex_rejected "hex: inner space" "invalid hex"
      (" " ^ String.sub hex 1 (n - 1));
    hex_rejected "hex: non-hex digit" "invalid hex"
      ("g" ^ String.sub hex 1 (n - 1))

  let laws name =
    [
      Alcotest.test_case
        (name ^ ": storage and roots vs frontier oracle")
        `Quick test_storage_and_roots;
      Alcotest.test_case (name ^ ": all proofs verify") `Quick test_proofs;
      Alcotest.test_case
        (name ^ ": hash conversions")
        `Quick test_hash_conversions;
    ]
end

module S = Suite (M)

(* other digest sizes: 20 and 64 bytes *)
module M1 = Merkle.Make (Digestif.SHA1)
module M512 = Merkle.Make (Digestif.SHA512)
module S1 = Suite (M1)
module S512 = Suite (M512)

let flip_bit = S.flip_bit
let check_true name b = Alcotest.(check bool) name true b
let check_false name b = Alcotest.(check bool) name false b

(* ---------- Certificate Transparency reference vectors ---------- *)

(* The eight reference inputs, hex-decoded. *)
let inputs =
  [
    "";
    "\x00";
    "\x10";
    "\x20\x21";
    "\x30\x31";
    "\x40\x41\x42\x43";
    "\x50\x51\x52\x53\x54\x55\x56\x57";
    "\x60\x61\x62\x63\x64\x65\x66\x67\x68\x69\x6a\x6b\x6c\x6d\x6e\x6f";
  ]

let empty_root_hex =
  "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"

(* Roots after adding leaf 1..8. *)
let roots_hex =
  [|
    "6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d";
    "fac54203e7cc696cf0dfcb42c92a1d9dbaf70ad9e621f4bd8d98662f00e3c125";
    "aeb6bcfe274b70a14fb067a5e5578264db0fa9b51af5e0ba159158f329e06e77";
    "d37ee418976dd95753c1c73862b9398fa2a2cf9b4ff0fdfe8b30cd95209614b7";
    "4e3bbb1f7b478dcfe71fb631631519a3bca12c9aefca1612bfce4c13a86264d4";
    "76e67dadbcdf1e10e1b74ddc608abd2f98dfb16fbce75277b5232a127f2087ef";
    "ddb89be403809e325750d3d263cd78929c2942b7942a34b77e122c9594a74c8c";
    "5dc9da79a70659a9ad559cb701ded9a2ab9d823aad2f4960cfe370eff4604328";
  |]

(* (index, size, path) — 0-based leaf index. *)
let inclusion_vectors =
  [
    (0, 1, []);
    ( 0,
      8,
      [
        "96a296d224f285c67bee93c30f8a309157f0daa35dc5b87e410b78630a09cfc7";
        "5f083f0a1a33ca076a95279832580db3e0ef4584bdff1f54c8a360f50de3031e";
        "6b47aaf29ee3c2af9af889bc1fb9254dabd31177f16232dd6aab035ca39bf6e4";
      ] );
    ( 5,
      8,
      [
        "bc1a0643b12e4d2d7c77918f44e0f4f79a838b6cf9ec5b5c283e1f4d88599e6b";
        "ca854ea128ed050b41b35ffc1b87b8eb2bde461e9e3b5596ece6b9d5975a0ae0";
        "d37ee418976dd95753c1c73862b9398fa2a2cf9b4ff0fdfe8b30cd95209614b7";
      ] );
    ( 2,
      3,
      [ "fac54203e7cc696cf0dfcb42c92a1d9dbaf70ad9e621f4bd8d98662f00e3c125" ]
    );
    ( 1,
      5,
      [
        "6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d";
        "5f083f0a1a33ca076a95279832580db3e0ef4584bdff1f54c8a360f50de3031e";
        "bc1a0643b12e4d2d7c77918f44e0f4f79a838b6cf9ec5b5c283e1f4d88599e6b";
      ] );
  ]

(* (old_size, new_size, proof) *)
let consistency_vectors =
  [
    (1, 1, []);
    ( 1,
      8,
      [
        "96a296d224f285c67bee93c30f8a309157f0daa35dc5b87e410b78630a09cfc7";
        "5f083f0a1a33ca076a95279832580db3e0ef4584bdff1f54c8a360f50de3031e";
        "6b47aaf29ee3c2af9af889bc1fb9254dabd31177f16232dd6aab035ca39bf6e4";
      ] );
    ( 6,
      8,
      [
        "0ebc5d3437fbe2db158b9f126a1d118e308181031d0a949f8dededebc558ef6a";
        "ca854ea128ed050b41b35ffc1b87b8eb2bde461e9e3b5596ece6b9d5975a0ae0";
        "d37ee418976dd95753c1c73862b9398fa2a2cf9b4ff0fdfe8b30cd95209614b7";
      ] );
    ( 2,
      5,
      [
        "5f083f0a1a33ca076a95279832580db3e0ef4584bdff1f54c8a360f50de3031e";
        "bc1a0643b12e4d2d7c77918f44e0f4f79a838b6cf9ec5b5c283e1f4d88599e6b";
      ] );
  ]

let ct_log () =
  let log = M.Log.create () in
  List.iter (fun i -> ignore (M.Log.append log i)) inputs;
  log

let hexes hs = List.map M.hash_to_hex hs
let hex_list = Alcotest.(list string)

(* ---------- known-answer tests ---------- *)

let test_roots () =
  let log = M.Log.create () in
  Alcotest.(check string) "empty root" empty_root_hex
    (M.hash_to_hex (M.Log.root log));
  Alcotest.(check string) "empty_root" empty_root_hex
    (M.hash_to_hex M.empty_root);
  List.iteri
    (fun i input ->
      ignore (M.Log.append log input);
      Alcotest.(check string)
        (Printf.sprintf "root at size %d" (i + 1))
        roots_hex.(i)
        (M.hash_to_hex (M.Log.root log)))
    inputs;
  (* prefix roots agree after the fact *)
  Array.iteri
    (fun i hex ->
      Alcotest.(check string)
        (Printf.sprintf "root_at %d" (i + 1))
        hex
        (M.hash_to_hex (M.Log.root_at log (i + 1))))
    roots_hex

let test_inclusion_vectors () =
  let log = ct_log () in
  List.iter
    (fun (index, size, want) ->
      Alcotest.check hex_list
        (Printf.sprintf "path(%d, %d)" index size)
        want
        (hexes (M.Log.inclusion_proof log ~index ~size)))
    inclusion_vectors

let test_consistency_vectors () =
  let log = ct_log () in
  List.iter
    (fun (old_size, new_size, want) ->
      Alcotest.check hex_list
        (Printf.sprintf "consistency(%d, %d)" old_size new_size)
        want
        (hexes (M.Log.consistency_proof log ~old_size ~new_size)))
    consistency_vectors

(* ---------- Go reference implementation vectors ---------- *)

let reference_log = lazy (S.build_log 1000)

let test_reference_roots () =
  let log = Lazy.force reference_log in
  List.iter
    (fun (size, want) ->
      Alcotest.(check string)
        (Printf.sprintf "root_at %d" size)
        want
        (M.hash_to_hex (M.Log.root_at log size)))
    Reference_vectors.roots

let test_reference_inclusion () =
  let log = Lazy.force reference_log in
  List.iter
    (fun (index, size, want) ->
      let name = Printf.sprintf "path(%d, %d)" index size in
      Alcotest.check hex_list name want
        (hexes (M.Log.inclusion_proof log ~index ~size));
      (* and the reference's bytes verify, independently of our prover *)
      check_true (name ^ " verifies")
        (M.verify_inclusion
           ~root:(M.hash_of_hex (List.assoc size Reference_vectors.roots))
           ~size ~index
           ~leaf:(M.leaf_hash (S.leaf_data index))
           ~proof:(List.map M.hash_of_hex want)))
    Reference_vectors.inclusion

let test_reference_consistency () =
  let log = Lazy.force reference_log in
  List.iter
    (fun (old_size, new_size, want) ->
      let name = Printf.sprintf "consistency(%d, %d)" old_size new_size in
      Alcotest.check hex_list name want
        (hexes (M.Log.consistency_proof log ~old_size ~new_size));
      let root n =
        match List.assoc_opt n Reference_vectors.roots with
        | Some hex -> M.hash_of_hex hex
        | None -> M.Log.root_at log n
      in
      check_true (name ^ " verifies")
        (M.verify_consistency ~old_size ~old_root:(root old_size) ~new_size
           ~new_root:(root new_size)
           ~proof:(List.map M.hash_of_hex want)))
    Reference_vectors.consistency

(* ---------- verification, exhaustively on the reference tree ---------- *)

let test_verify_inclusion_exhaustive () =
  let log = ct_log () in
  for size = 1 to 8 do
    let root = M.Log.root_at log size in
    for index = 0 to size - 1 do
      let proof = M.Log.inclusion_proof log ~index ~size in
      let leaf = M.Log.leaf log index in
      let name = Printf.sprintf "(%d, %d)" index size in
      Alcotest.(check bool)
        (name ^ " verifies") true
        (M.verify_inclusion ~root ~size ~index ~leaf ~proof);
      Alcotest.(check bool)
        (name ^ " wrong root") false
        (M.verify_inclusion ~root:(flip_bit root) ~size ~index ~leaf ~proof);
      Alcotest.(check bool)
        (name ^ " wrong leaf") false
        (M.verify_inclusion ~root ~size ~index ~leaf:(flip_bit leaf) ~proof);
      Alcotest.(check bool)
        (name ^ " extra element") false
        (M.verify_inclusion ~root ~size ~index ~leaf
           ~proof:(proof @ [ M.empty_root ]));
      (match proof with
      | [] -> ()
      | p :: rest ->
        Alcotest.(check bool)
          (name ^ " tampered proof") false
          (M.verify_inclusion ~root ~size ~index ~leaf
             ~proof:(flip_bit p :: rest));
        Alcotest.(check bool)
          (name ^ " truncated proof") false
          (M.verify_inclusion ~root ~size ~index ~leaf ~proof:rest));
      (* wrong index *)
      if size > 1 then
        Alcotest.(check bool)
          (name ^ " wrong index") false
          (M.verify_inclusion ~root ~size ~index:((index + 1) mod size) ~leaf
             ~proof)
    done
  done

let test_verify_consistency_exhaustive () =
  let log = ct_log () in
  for old_size = 0 to 8 do
    for new_size = old_size to 8 do
      let old_root = M.Log.root_at log old_size in
      let new_root = M.Log.root_at log new_size in
      let proof = M.Log.consistency_proof log ~old_size ~new_size in
      let name = Printf.sprintf "(%d -> %d)" old_size new_size in
      Alcotest.(check bool)
        (name ^ " verifies") true
        (M.verify_consistency ~old_size ~old_root ~new_size ~new_root ~proof);
      (* consistency with the empty tree is vacuous: it makes no claim
         about the new root, so only check tampering when old_size > 0
         (or when equal sizes force root equality) *)
      if old_size > 0 || old_size = new_size then
        Alcotest.(check bool)
          (name ^ " wrong new root") false
          (M.verify_consistency ~old_size ~old_root ~new_size
             ~new_root:(flip_bit new_root) ~proof);
      (* the empty tree has exactly one root, so this holds at 0 too *)
      Alcotest.(check bool)
        (name ^ " wrong old root") false
        (M.verify_consistency ~old_size ~old_root:(flip_bit old_root)
           ~new_size ~new_root ~proof);
      Alcotest.(check bool)
        (name ^ " extra element") false
        (M.verify_consistency ~old_size ~old_root ~new_size ~new_root
           ~proof:(proof @ [ M.empty_root ]));
      match proof with
      | [] -> ()
      | p :: rest ->
        Alcotest.(check bool)
          (name ^ " tampered proof") false
          (M.verify_consistency ~old_size ~old_root ~new_size ~new_root
             ~proof:(flip_bit p :: rest));
        Alcotest.(check bool)
          (name ^ " truncated proof") false
          (M.verify_consistency ~old_size ~old_root ~new_size ~new_root
             ~proof:rest)
    done
  done

(* ---------- each guard of the verifiers, one attack apiece ----------

   Every case below is a false statement that is accepted if the named
   check is removed from the verifier. *)

let test_inclusion_range () =
  let log = ct_log () in
  (* a one-leaf tree's root is its leaf hash and its audit path is empty,
     so nothing but the range check can reject a bad index here *)
  let leaf = M.Log.leaf log 0 in
  let root = M.Log.root_at log 1 in
  check_true "(0, 1)"
    (M.verify_inclusion ~root ~size:1 ~index:0 ~leaf ~proof:[]);
  check_false "index = size"
    (M.verify_inclusion ~root ~size:1 ~index:1 ~leaf ~proof:[]);
  check_false "index < 0"
    (M.verify_inclusion ~root ~size:1 ~index:(-1) ~leaf ~proof:[]);
  check_false "size = 0"
    (M.verify_inclusion ~root ~size:0 ~index:0 ~leaf ~proof:[]);
  check_false "size < 0"
    (M.verify_inclusion ~root ~size:(-1) ~index:0 ~leaf ~proof:[]);
  check_false "index = max_int"
    (M.verify_inclusion ~root ~size:1 ~index:max_int ~leaf ~proof:[]);
  let root = M.Log.root_at log 8 in
  let proof = M.Log.inclusion_proof log ~index:7 ~size:8 in
  let leaf = M.Log.leaf log 7 in
  check_true "(7, 8)" (M.verify_inclusion ~root ~size:8 ~index:7 ~leaf ~proof);
  check_false "(8, 8)" (M.verify_inclusion ~root ~size:8 ~index:8 ~leaf ~proof);
  check_false "(-1, 8)"
    (M.verify_inclusion ~root ~size:8 ~index:(-1) ~leaf ~proof)

let test_inclusion_binds_size () =
  let log = ct_log () in
  let leaf = M.Log.leaf log 0 in
  let root = M.Log.root_at log 4 in
  let proof = M.Log.inclusion_proof log ~index:0 ~size:4 in
  check_true "(0, 4)" (M.verify_inclusion ~root ~size:4 ~index:0 ~leaf ~proof);
  (* PATH(0, D[4]) retraces the first two steps of PATH(0, D[n]) for any
     larger n and so reaches the same hash: only the closing sn = 0 test
     notices that a larger tree was not climbed to its root *)
  List.iter
    (fun size ->
      check_false
        (Printf.sprintf "same path claimed for size %d" size)
        (M.verify_inclusion ~root ~size ~index:0 ~leaf ~proof))
    [ 5; 6; 7; 8; 16; 1 lsl 40 ]

let test_inclusion_overlong () =
  let log = ct_log () in
  (* leaves 4..7 as a tree of their own: the right half of the 8-leaf tree *)
  let right = M.Log.create () in
  List.iteri (fun i d -> if i >= 4 then ignore (M.Log.append right d)) inputs;
  let leaf = M.Log.leaf log 5 in
  let root = M.Log.root log in
  let proof =
    M.Log.inclusion_proof right ~index:1 ~size:4 @ [ M.Log.root_at log 4 ]
  in
  Alcotest.check hex_list "the honest path for (5, 8)"
    (hexes (M.Log.inclusion_proof log ~index:5 ~size:8))
    (hexes proof);
  check_true "(5, 8)" (M.verify_inclusion ~root ~size:8 ~index:5 ~leaf ~proof);
  (* the same hashes read as "index 1 of 4" run past the root of a 4-leaf
     tree; hashing on regardless lands on the 8-leaf root *)
  check_false "claimed as (1, 4)"
    (M.verify_inclusion ~root ~size:4 ~index:1 ~leaf ~proof)

let test_consistency_special_cases () =
  let log = ct_log () in
  let r n = M.Log.root_at log n in
  let some = [ r 3 ] in
  (* shrinking: a lone old root "verifies" 8 -> 4 without the size guard *)
  check_false "new < old"
    (M.verify_consistency ~old_size:8 ~old_root:(r 8) ~new_size:4
       ~new_root:(r 8) ~proof:[]);
  check_false "new < old, honest roots"
    (M.verify_consistency ~old_size:8 ~old_root:(r 8) ~new_size:4
       ~new_root:(r 4)
       ~proof:(M.Log.consistency_proof log ~old_size:4 ~new_size:8));
  check_false "old < 0"
    (M.verify_consistency ~old_size:(-1) ~old_root:(r 0) ~new_size:4
       ~new_root:(r 4) ~proof:[]);
  check_false "both < 0"
    (M.verify_consistency ~old_size:(-2) ~old_root:(r 0) ~new_size:(-2)
       ~new_root:(r 0) ~proof:[]);
  (* equal sizes *)
  check_true "4 = 4"
    (M.verify_consistency ~old_size:4 ~old_root:(r 4) ~new_size:4
       ~new_root:(r 4) ~proof:[]);
  check_false "4 = 4, non-empty proof"
    (M.verify_consistency ~old_size:4 ~old_root:(r 4) ~new_size:4
       ~new_root:(r 4) ~proof:some);
  check_false "4 = 4, different roots"
    (M.verify_consistency ~old_size:4 ~old_root:(r 4) ~new_size:4
       ~new_root:(r 5) ~proof:[]);
  check_true "0 = 0"
    (M.verify_consistency ~old_size:0 ~old_root:M.empty_root ~new_size:0
       ~new_root:M.empty_root ~proof:[]);
  (* from the empty tree *)
  check_true "0 -> 4"
    (M.verify_consistency ~old_size:0 ~old_root:M.empty_root ~new_size:4
       ~new_root:(r 4) ~proof:[]);
  check_false "0 -> 4, non-empty proof"
    (M.verify_consistency ~old_size:0 ~old_root:M.empty_root ~new_size:4
       ~new_root:(r 4) ~proof:some);
  check_false "0 -> 4, old root is not H(\"\")"
    (M.verify_consistency ~old_size:0 ~old_root:(r 1) ~new_size:4
       ~new_root:(r 4) ~proof:[]);
  (* 0 < old < new always needs hashes, power of two or not *)
  List.iter
    (fun (old_size, new_size) ->
      check_false
        (Printf.sprintf "%d -> %d, empty proof" old_size new_size)
        (M.verify_consistency ~old_size ~old_root:(r old_size) ~new_size
           ~new_root:(r new_size) ~proof:[]))
    [ (1, 2); (2, 4); (4, 8); (3, 4); (6, 8); (7, 8) ];
  (* some logs send the old root first even when old_size is a power of
     two; RFC 6962 omits it, and so must the proof *)
  check_false "4 -> 8 with the old root prepended"
    (M.verify_consistency ~old_size:4 ~old_root:(r 4) ~new_size:8
       ~new_root:(r 8)
       ~proof:(r 4 :: M.Log.consistency_proof log ~old_size:4 ~new_size:8))

let test_consistency_binds_size () =
  let log = ct_log () in
  let old_root = M.Log.root_at log 4 and new_root = M.Log.root_at log 8 in
  let proof = M.Log.consistency_proof log ~old_size:4 ~new_size:8 in
  check_true "4 -> 8"
    (M.verify_consistency ~old_size:4 ~old_root ~new_size:8 ~new_root ~proof);
  (* in a 16-leaf tree the same hashes stop one level short of the root;
     only the closing sn = 0 test notices *)
  List.iter
    (fun new_size ->
      check_false
        (Printf.sprintf "same proof claimed for 4 -> %d" new_size)
        (M.verify_consistency ~old_size:4 ~old_root ~new_size ~new_root ~proof))
    [ 9; 12; 16; 1 lsl 40 ]

let test_consistency_overlong () =
  let log = ct_log () in
  let right = M.Log.create () in
  List.iteri (fun i d -> if i >= 4 then ignore (M.Log.append right d)) inputs;
  let old_root = M.Log.root_at log 7 and new_root = M.Log.root_at log 8 in
  let proof =
    M.Log.consistency_proof right ~old_size:3 ~new_size:4
    @ [ M.Log.root_at log 4 ]
  in
  Alcotest.check hex_list "the honest proof for 7 -> 8"
    (hexes (M.Log.consistency_proof log ~old_size:7 ~new_size:8))
    (hexes proof);
  check_true "7 -> 8"
    (M.verify_consistency ~old_size:7 ~old_root ~new_size:8 ~new_root ~proof);
  (* read as 3 -> 4 the proof is one hash too long; hashing on regardless
     reproduces both 8-leaf-tree roots *)
  check_false "claimed as 3 -> 4"
    (M.verify_consistency ~old_size:3 ~old_root ~new_size:4 ~new_root ~proof)

(* ---------- API odds and ends ---------- *)

let test_domain_separation () =
  let l = M.leaf_hash "left" and r = M.leaf_hash "right" in
  (* the second-preimage defence of RFC 6962: an interior node can never
     be passed off as a leaf holding its children's concatenation *)
  check_false "leaf vs node"
    (M.equal_hash (M.node_hash l r)
       (M.leaf_hash (M.hash_to_raw l ^ M.hash_to_raw r)));
  check_false "node_hash is ordered"
    (M.equal_hash (M.node_hash l r) (M.node_hash r l));
  check_false "the empty leaf is not the empty tree"
    (M.equal_hash (M.leaf_hash "") M.empty_root);
  (* SHA-256 is what the type equation promises *)
  let (_ : Digestif.SHA256.t) = M.empty_root in
  Alcotest.(check int) "hash_size" 32 M.hash_size;
  Alcotest.(check int) "SHA-1 hash_size" 20 M1.hash_size;
  Alcotest.(check int) "SHA-512 hash_size" 64 M512.hash_size;
  Alcotest.(check string) "SHA-512 empty root"
    ("cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce"
   ^ "47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e")
    (M512.hash_to_hex M512.empty_root)

let test_append_leaf_hash () =
  let by_data = M.Log.create () and by_hash = M.Log.create () in
  List.iteri
    (fun i d ->
      ignore (M.Log.append by_data d);
      Alcotest.(check int)
        (Printf.sprintf "index %d" i)
        i
        (M.Log.append_leaf_hash by_hash (M.leaf_hash d)))
    inputs;
  Alcotest.(check string) "same root" roots_hex.(7)
    (M.hash_to_hex (M.Log.root by_hash));
  check_true "stored as given"
    (M.equal_hash (M.Log.leaf by_hash 3) (M.leaf_hash (List.nth inputs 3)));
  check_true "same as append"
    (M.equal_hash (M.Log.root by_data) (M.Log.root by_hash))

let test_bounds () =
  let log = ct_log () in
  let raises name msg f = Alcotest.check_raises name (Invalid_argument msg) f in
  let inclusion name ~index ~size =
    raises ("inclusion_proof: " ^ name)
      "Merkle.Log.inclusion_proof: bad index/size" (fun () ->
        ignore (M.Log.inclusion_proof log ~index ~size))
  in
  inclusion "index = size" ~index:5 ~size:5;
  inclusion "index < 0" ~index:(-1) ~size:5;
  inclusion "size = 0" ~index:0 ~size:0;
  inclusion "size < 0" ~index:0 ~size:(-1);
  inclusion "size > log" ~index:0 ~size:9;
  let consistency name ~old_size ~new_size =
    raises ("consistency_proof: " ^ name)
      "Merkle.Log.consistency_proof: bad sizes" (fun () ->
        ignore (M.Log.consistency_proof log ~old_size ~new_size))
  in
  consistency "new > log" ~old_size:2 ~new_size:9;
  consistency "old > new" ~old_size:5 ~new_size:4;
  consistency "old < 0" ~old_size:(-1) ~new_size:4;
  let root_at name n =
    raises ("root_at: " ^ name) "Merkle.Log.root_at: bad size" (fun () ->
        ignore (M.Log.root_at log n))
  in
  root_at "n > log" 9;
  root_at "n < 0" (-1);
  let leaf name i =
    raises ("leaf: " ^ name) "Merkle.Log.leaf: out of bounds" (fun () ->
        ignore (M.Log.leaf log i))
  in
  leaf "i = size" 8;
  leaf "i < 0" (-1);
  raises "leaf: empty log" "Merkle.Log.leaf: out of bounds" (fun () ->
      ignore (M.Log.leaf (M.Log.create ()) 0));
  (* the degenerate proofs are empty rather than errors *)
  Alcotest.check hex_list "consistency 0 -> 8" []
    (hexes (M.Log.consistency_proof log ~old_size:0 ~new_size:8));
  Alcotest.check hex_list "consistency 8 -> 8" []
    (hexes (M.Log.consistency_proof log ~old_size:8 ~new_size:8));
  Alcotest.check hex_list "consistency 0 -> 0" []
    (hexes (M.Log.consistency_proof log ~old_size:0 ~new_size:0));
  Alcotest.(check string) "root_at 0" empty_root_hex
    (M.hash_to_hex (M.Log.root_at log 0))

(* ---------- properties on random logs ---------- *)

let build_log = S.build_log

let prop_inclusion =
  QCheck2.Test.make ~name:"random inclusion proofs verify (and tampers fail)"
    ~count:300
    ~print:QCheck2.Print.(triple int int int)
    QCheck2.Gen.(triple (1 -- 120) nat nat)
    (fun (n, a, b) ->
      let log = build_log n in
      let size = 1 + (a mod n) in
      let index = b mod size in
      let proof = M.Log.inclusion_proof log ~index ~size in
      let root = M.Log.root_at log size in
      let leaf = M.Log.leaf log index in
      M.verify_inclusion ~root ~size ~index ~leaf ~proof
      && (proof = []
         ||
         match proof with
         | p :: rest ->
           not
             (M.verify_inclusion ~root ~size ~index ~leaf
                ~proof:(flip_bit p :: rest))
         | [] -> true))

let prop_consistency =
  QCheck2.Test.make ~name:"random consistency proofs verify (and tampers fail)"
    ~count:300
    ~print:QCheck2.Print.(triple int int int)
    QCheck2.Gen.(triple (1 -- 120) nat nat)
    (fun (n, a, b) ->
      let log = build_log n in
      let new_size = 1 + (a mod n) in
      let old_size = b mod (new_size + 1) in
      let proof = M.Log.consistency_proof log ~old_size ~new_size in
      let old_root = M.Log.root_at log old_size in
      let new_root = M.Log.root_at log new_size in
      M.verify_consistency ~old_size ~old_root ~new_size ~new_root ~proof
      && (old_size = 0 && new_size > 0
         (* vacuous case: no claim about the new root *)
         || not
              (M.verify_consistency ~old_size ~old_root ~new_size
                 ~new_root:(flip_bit new_root) ~proof)))

(* The verifiers against the structural oracles, on proofs that are
   honest or damaged in one way. Shifting an index or a size does not
   always invalidate a proof -- PATH(0, D[3]) and PATH(0, D[4]) have the
   same shape -- so there the oracle, not a fixed answer, is the judge. *)

let damage_names =
  [|
    "intact"; "index - 1"; "index + 1"; "size - 1"; "size + 1"; "size * 2";
    "drop first"; "drop last"; "extra first"; "extra last"; "flip one";
    "swap ends"; "reversed"; "bad root"; "bad leaf / old root";
  |]

let n_damages = Array.length damage_names

let drop_last l = List.filteri (fun i _ -> i < List.length l - 1) l

let swap_ends = function
  | [] | [ _ ] as l -> l
  | first :: rest ->
    let last = List.nth rest (List.length rest - 1) in
    (last :: drop_last rest) @ [ first ]

let damage_proof damage pick proof =
  match damage with
  | 6 -> (match proof with [] -> [] | _ :: rest -> rest)
  | 7 -> drop_last proof
  | 8 -> M.leaf_hash "extra" :: proof
  | 9 -> proof @ [ M.leaf_hash "extra" ]
  | 10 when proof <> [] ->
    let j = pick mod List.length proof in
    List.mapi (fun i h -> if i = j then flip_bit h else h) proof
  | 11 -> swap_ends proof
  | 12 -> List.rev proof
  | _ -> proof

let print_case (a, b, damage, pick) =
  Printf.sprintf "(%d, %d, %s, pick %d)" a b damage_names.(damage) pick

let oracle_log = lazy (build_log 300)

let prop_inclusion_oracle =
  QCheck2.Test.make ~name:"verify_inclusion agrees with the structural oracle"
    ~count:3000 ~print:print_case
    QCheck2.Gen.(
      map2
        (fun (size, b) (damage, pick) -> (size, b, damage, pick))
        (pair (1 -- 300) nat)
        (pair (0 -- (n_damages - 1)) nat))
    (fun (size, b, damage, pick) ->
      let log = Lazy.force oracle_log in
      let index = b mod size in
      let honest = M.Log.inclusion_proof log ~index ~size in
      let root = M.Log.root_at log size and leaf = M.Log.leaf log index in
      let index', size' =
        match damage with
        | 1 -> (index - 1, size)
        | 2 -> (index + 1, size)
        | 3 -> (index, size - 1)
        | 4 -> (index, size + 1)
        | 5 -> (index, size * 2)
        | _ -> (index, size)
      in
      let root' = if damage = 13 then flip_bit root else root in
      let leaf' = if damage = 14 then flip_bit leaf else leaf in
      let proof = damage_proof damage pick honest in
      let got =
        M.verify_inclusion ~root:root' ~size:size' ~index:index' ~leaf:leaf'
          ~proof
      in
      let want =
        S.oracle_verify_inclusion ~root:root' ~size:size' ~index:index'
          ~leaf:leaf' ~proof
      in
      got = want
      && (damage <> 0 || got)
      (* whatever changes a hash that is fed in must be caught *)
      && ((damage <> 13 && damage <> 14) || not got))

let prop_consistency_oracle =
  QCheck2.Test.make
    ~name:"verify_consistency agrees with the structural oracle" ~count:3000
    ~print:print_case
    QCheck2.Gen.(
      map2
        (fun (new_size, b) (damage, pick) -> (new_size, b, damage, pick))
        (pair (1 -- 300) nat)
        (pair (0 -- (n_damages - 1)) nat))
    (fun (new_size, b, damage, pick) ->
      let log = Lazy.force oracle_log in
      let old_size = b mod (new_size + 1) in
      let honest = M.Log.consistency_proof log ~old_size ~new_size in
      let old_root = M.Log.root_at log old_size in
      let new_root = M.Log.root_at log new_size in
      let old_size', new_size' =
        match damage with
        | 1 -> (old_size - 1, new_size)
        | 2 -> (old_size + 1, new_size)
        | 3 -> (old_size, new_size - 1)
        | 4 -> (old_size, new_size + 1)
        | 5 -> (old_size, new_size * 2)
        | _ -> (old_size, new_size)
      in
      let new_root' = if damage = 13 then flip_bit new_root else new_root in
      let old_root' = if damage = 14 then flip_bit old_root else old_root in
      let proof = damage_proof damage pick honest in
      let got =
        M.verify_consistency ~old_size:old_size' ~old_root:old_root'
          ~new_size:new_size' ~new_root:new_root' ~proof
      in
      let want =
        S.oracle_verify_consistency ~old_size:old_size' ~old_root:old_root'
          ~new_size:new_size' ~new_root:new_root' ~proof
      in
      got = want
      && (damage <> 0 || got)
      && (damage <> 14 || not got)
      (* from the empty tree nothing is claimed about the new root *)
      && (damage <> 13 || old_size = 0 || not got))

let () =
  Alcotest.run "merkle"
    [
      ( "ct vectors",
        [
          Alcotest.test_case "incremental roots" `Quick test_roots;
          Alcotest.test_case "inclusion paths" `Quick test_inclusion_vectors;
          Alcotest.test_case "consistency proofs" `Quick
            test_consistency_vectors;
        ] );
      ( "go reference vectors",
        [
          Alcotest.test_case "roots" `Quick test_reference_roots;
          Alcotest.test_case "inclusion paths" `Quick test_reference_inclusion;
          Alcotest.test_case "consistency proofs" `Quick
            test_reference_consistency;
        ] );
      ( "verification",
        [
          Alcotest.test_case "inclusion, all (index, size)" `Quick
            test_verify_inclusion_exhaustive;
          Alcotest.test_case "consistency, all (old, new)" `Quick
            test_verify_consistency_exhaustive;
        ] );
      ( "verifier guards",
        [
          Alcotest.test_case "inclusion: index range" `Quick
            test_inclusion_range;
          Alcotest.test_case "inclusion: binds the tree size" `Quick
            test_inclusion_binds_size;
          Alcotest.test_case "inclusion: over-long path" `Quick
            test_inclusion_overlong;
          Alcotest.test_case "consistency: special cases" `Quick
            test_consistency_special_cases;
          Alcotest.test_case "consistency: binds the tree size" `Quick
            test_consistency_binds_size;
          Alcotest.test_case "consistency: over-long proof" `Quick
            test_consistency_overlong;
        ] );
      ( "api",
        [
          Alcotest.test_case "domain separation" `Quick test_domain_separation;
          Alcotest.test_case "append_leaf_hash" `Quick test_append_leaf_hash;
          Alcotest.test_case "bounds" `Quick test_bounds;
        ] );
      ("laws", S.laws "SHA-256" @ S1.laws "SHA-1" @ S512.laws "SHA-512");
      ( "properties",
        List.map QCheck_alcotest.to_alcotest
          [
            prop_inclusion;
            prop_consistency;
            prop_inclusion_oracle;
            prop_consistency_oracle;
          ] );
    ]
