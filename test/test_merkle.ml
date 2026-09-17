(* Known-answer tests from the Certificate Transparency reference
   implementation (google/certificate-transparency,
   cpp/merkletree/merkle_tree_test.cc), which defined the canonical
   RFC 6962 test vectors; plus property tests. *)

module M = Merkle.SHA256

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

let flip_bit h =
  let raw = Bytes.of_string (M.hash_to_raw h) in
  Bytes.set raw 0 (Char.chr (Char.code (Bytes.get raw 0) lxor 1));
  M.hash_of_raw (Bytes.to_string raw)

(* ---------- known-answer tests ---------- *)

let test_roots () =
  let log = M.Log.create () in
  Alcotest.(check string) "empty root" empty_root_hex
    (M.hash_to_hex (M.Log.root log));
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
      if old_size > 0 then
        Alcotest.(check bool)
          (name ^ " wrong old root") false
          (M.verify_consistency ~old_size ~old_root:(flip_bit old_root)
             ~new_size ~new_root ~proof);
      match proof with
      | [] -> ()
      | p :: rest ->
        Alcotest.(check bool)
          (name ^ " tampered proof") false
          (M.verify_consistency ~old_size ~old_root ~new_size ~new_root
             ~proof:(flip_bit p :: rest))
    done
  done

(* ---------- API odds and ends ---------- *)

let test_conversions () =
  let h = M.leaf_hash "hello" in
  Alcotest.(check bool)
    "raw round-trip" true
    (M.equal_hash h (M.hash_of_raw (M.hash_to_raw h)));
  Alcotest.(check bool)
    "hex round-trip" true
    (M.equal_hash h (M.hash_of_hex (M.hash_to_hex h)));
  Alcotest.(check int) "hash_size" 32 M.hash_size;
  Alcotest.check_raises "bad raw"
    (Invalid_argument "Merkle.hash_of_raw: wrong length") (fun () ->
      ignore (M.hash_of_raw "short"));
  let hex = M.hash_to_hex h in
  let n = String.length hex in
  Alcotest.(check string) "hex is lowercase" (String.lowercase_ascii hex) hex;
  Alcotest.(check bool)
    "uppercase hex accepted" true
    (M.equal_hash h (M.hash_of_hex (String.uppercase_ascii hex)));
  let hex_rejected name why s =
    Alcotest.check_raises name
      (Invalid_argument ("Merkle.hash_of_hex: " ^ why)) (fun () ->
        ignore (M.hash_of_hex s))
  in
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

let test_bounds () =
  let log = ct_log () in
  Alcotest.check_raises "index out of size"
    (Invalid_argument "Merkle.Log.inclusion_proof: bad index/size") (fun () ->
      ignore (M.Log.inclusion_proof log ~index:5 ~size:5));
  Alcotest.check_raises "size too big"
    (Invalid_argument "Merkle.Log.consistency_proof: bad sizes") (fun () ->
      ignore (M.Log.consistency_proof log ~old_size:2 ~new_size:9));
  Alcotest.check_raises "leaf oob"
    (Invalid_argument "Merkle.Log.leaf: out of bounds") (fun () ->
      ignore (M.Log.leaf log 8))

(* ---------- properties on random logs ---------- *)

let build_log n =
  let log = M.Log.create () in
  for i = 0 to n - 1 do
    ignore (M.Log.append log (Printf.sprintf "leaf-%d" i))
  done;
  log

let prop_inclusion =
  QCheck2.Test.make ~name:"random inclusion proofs verify (and tampers fail)"
    ~count:300
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
      ( "verification",
        [
          Alcotest.test_case "inclusion, all (index, size)" `Quick
            test_verify_inclusion_exhaustive;
          Alcotest.test_case "consistency, all (old, new)" `Quick
            test_verify_consistency_exhaustive;
        ] );
      ( "api",
        [
          Alcotest.test_case "conversions" `Quick test_conversions;
          Alcotest.test_case "bounds" `Quick test_bounds;
        ] );
      ( "properties",
        List.map QCheck_alcotest.to_alcotest
          [ prop_inclusion; prop_consistency ] );
    ]
