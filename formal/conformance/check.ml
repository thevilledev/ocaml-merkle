(* Model conformance: replay what the Lean model of this library computes
   on symbolic hashes (formal/lean/Conformance.lean) against the library
   itself on the SHA-256 hashes those symbols denote, and require the
   same roots, the same proofs and the same verdicts.

   A symbolic hash: [L<i>] is [leaf_hash "leaf-<i>"], [E] is
   [empty_root], [J<k>] is [leaf_hash "junk-<k>"], [(a b)] is
   [node_hash a b]. *)

module M = Merkle.SHA256

(* ---- terms ---- *)

let parse_term s =
  let n = String.length s in
  let rec term i =
    match s.[i] with
    | '(' ->
      let l, i = term (i + 1) in
      if s.[i] <> ' ' then failwith ("bad term: " ^ s);
      let r, i = term (i + 1) in
      if s.[i] <> ')' then failwith ("bad term: " ^ s);
      (M.node_hash l r, i + 1)
    | 'E' -> (M.empty_root, i + 1)
    | ('L' | 'J') as c ->
      let j = ref (i + 1) in
      while !j < n && s.[!j] >= '0' && s.[!j] <= '9' do incr j done;
      let k = String.sub s (i + 1) (!j - i - 1) in
      let data = (if c = 'L' then "leaf-" else "junk-") ^ k in
      (M.leaf_hash data, !j)
    | _ -> failwith ("bad term: " ^ s)
  in
  let h, i = term 0 in
  if i <> n then failwith ("trailing input in term: " ^ s);
  h

(* a proof: "-" or terms separated by top-level commas *)
let parse_proof s =
  if s = "-" then []
  else begin
    let parts = ref [] and depth = ref 0 and start = ref 0 in
    String.iteri
      (fun i c ->
        match c with
        | '(' -> incr depth
        | ')' -> decr depth
        | ',' when !depth = 0 ->
          parts := String.sub s !start (i - !start) :: !parts;
          start := i + 1
        | _ -> ())
      s;
    parts := String.sub s !start (String.length s - !start) :: !parts;
    List.rev_map parse_term !parts
  end

(* A line is space separated, but terms contain spaces: split at spaces
   outside parentheses. *)
let fields line =
  let out = ref [] and depth = ref 0 and start = ref 0 in
  String.iteri
    (fun i c ->
      match c with
      | '(' -> incr depth
      | ')' -> decr depth
      | ' ' when !depth = 0 ->
        out := String.sub line !start (i - !start) :: !out;
        start := i + 1
      | _ -> ())
    line;
  List.rev (String.sub line !start (String.length line - !start) :: !out)

let hexes p = String.concat "," (List.map M.hash_to_hex p)

let () =
  let ic =
    match Sys.argv with
    | [| _; path |] -> open_in path
    | _ ->
      prerr_endline "usage: check CORPUS";
      exit 2
  in
  let log = M.Log.create () in
  let grow n =
    while M.Log.size log < n do
      ignore (M.Log.append log (Printf.sprintf "leaf-%d" (M.Log.size log)))
    done
  in
  let checks = ref 0 and failures = ref 0 in
  let fail fmt =
    incr failures;
    Printf.kfprintf (fun oc -> output_char oc '\n') stdout fmt
  in
  (try
     while true do
       let line = input_line ic in
       incr checks;
       match fields line with
       | [ "R"; n; root ] ->
         let n = int_of_string n in
         grow n;
         let got = M.Log.root_at log n in
         if not (M.equal_hash got (parse_term root)) then fail "root %d differs" n
       | [ "P"; i; n; p ] ->
         let i = int_of_string i and n = int_of_string n in
         grow n;
         let got = M.Log.inclusion_proof log ~index:i ~size:n in
         if hexes got <> hexes (parse_proof p) then
           fail "inclusion proof (%d, %d) differs" i n
       | [ "Q"; m; n; p ] ->
         let m = int_of_string m and n = int_of_string n in
         grow n;
         let got = M.Log.consistency_proof log ~old_size:m ~new_size:n in
         if hexes got <> hexes (parse_proof p) then
           fail "consistency proof (%d, %d) differs" m n
       | [ "I"; root; size; index; leaf; p; v ] ->
         let got =
           M.verify_inclusion ~root:(parse_term root) ~size:(int_of_string size)
             ~index:(int_of_string index) ~leaf:(parse_term leaf)
             ~proof:(parse_proof p)
         in
         if got <> (v = "1") then fail "verify_inclusion: model %s, library %b: %s" v got line
       | [ "C"; m; r1; n; r2; p; v ] ->
         let got =
           M.verify_consistency ~old_size:(int_of_string m) ~old_root:(parse_term r1)
             ~new_size:(int_of_string n) ~new_root:(parse_term r2)
             ~proof:(parse_proof p)
         in
         if got <> (v = "1") then
           fail "verify_consistency: model %s, library %b: %s" v got line
       | _ -> fail "unparsed line: %s" line
     done
   with End_of_file -> close_in ic);
  Printf.printf "%d checks of the Lean model against the library, %d failures\n"
    !checks !failures;
  if !checks = 0 then exit 2;
  exit (if !failures = 0 then 0 else 1)
