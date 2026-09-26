(* The OCaml side of the differential test: replay the corpus written by
   compat/go against this library and require the same roots, the same
   proofs byte for byte, and the same verdict on every verification
   query. See ../README.md for the line formats. *)

module M = Merkle.SHA256

let unhex s =
  if s = "-" then ""
  else
    String.init
      (String.length s / 2)
      (fun i -> Char.chr (int_of_string ("0x" ^ String.sub s (2 * i) 2)))

let hash s = M.hash_of_raw (unhex s)
let proof s = if s = "-" then [] else List.map hash (String.split_on_char ',' s)

let proof_hex = function
  | [] -> "-"
  | p -> String.concat "," (List.map M.hash_to_hex p)

let () =
  let path =
    match Sys.argv with
    | [| _; path |] -> path
    | _ ->
      prerr_endline "usage: replay CORPUS";
      exit 2
  in
  let ic = open_in path in
  let log = M.Log.create () in
  let mismatches = ref 0 and stricter = ref 0 in
  let roots = ref 0 and proofs = ref 0 and verdicts = ref 0 in
  let mismatch fmt =
    incr mismatches;
    Printf.kfprintf (fun oc -> output_char oc '\n') stdout fmt
  in
  (try
     while true do
       let line = input_line ic in
       match String.split_on_char ' ' line with
       | [ "L"; data ] -> ignore (M.Log.append log (unhex data))
       | [ "R"; size; want ] ->
         incr roots;
         let got = M.hash_to_hex (M.Log.root_at log (int_of_string size)) in
         if got <> want then mismatch "root %s: go %s, ocaml %s" size want got
       | [ "P"; index; size; want ] ->
         incr proofs;
         let got =
           proof_hex
             (M.Log.inclusion_proof log ~index:(int_of_string index)
                ~size:(int_of_string size))
         in
         if got <> want then
           mismatch "inclusion proof (%s, %s): go %s, ocaml %s" index size want
             got
       | [ "Q"; old_size; new_size; want ] ->
         incr proofs;
         let got =
           proof_hex
             (M.Log.consistency_proof log ~old_size:(int_of_string old_size)
                ~new_size:(int_of_string new_size))
         in
         if got <> want then
           mismatch "consistency proof (%s, %s): go %s, ocaml %s" old_size
             new_size want got
       | [ "I"; index; size; leaf; root; p; want ] ->
         incr verdicts;
         let got =
           M.verify_inclusion ~root:(hash root) ~size:(int_of_string size)
             ~index:(int_of_string index) ~leaf:(hash leaf) ~proof:(proof p)
         in
         if got <> (want = "1") then
           mismatch "verify_inclusion: go %s, ocaml %b: %s" want got line
       | [ "C"; old_size; new_size; old_root; new_root; p; want ] ->
         incr verdicts;
         let old_size = int_of_string old_size in
         let old_root = hash old_root in
         let got =
           M.verify_consistency ~old_size ~old_root
             ~new_size:(int_of_string new_size) ~new_root:(hash new_root)
             ~proof:(proof p)
         in
         let empty_root_ok = M.equal_hash old_root M.empty_root in
         if old_size = 0 && got && not empty_root_ok then
           (* The rule behind the documented difference, checked on its
              own: agreeing with Go here is no evidence, as Go accepts
              any old root of size 0. *)
           mismatch "verify_consistency accepts an old root of size 0 other \
                     than H(\"\"): %s"
             line
         else if got <> (want = "1") then
           (* The one documented difference: from the empty tree this
              library also requires old_root = H(""), which the Go
              verifier does not look at. *)
           if old_size = 0 && want = "1" && not empty_root_ok then incr stricter
           else mismatch "verify_consistency: go %s, ocaml %b: %s" want got line
       | _ -> mismatch "unparsed line: %s" line
     done
   with End_of_file -> close_in ic);
  Printf.printf
    "%d roots, %d proofs and %d verdicts compared with \
     transparency-dev/merkle\n\
     %d mismatches; %d queries where only this library insists that the\n\
     empty tree's root is H(\"\") (documented)\n"
    !roots !proofs !verdicts !mismatches !stricter;
  if !roots = 0 || !proofs = 0 || !verdicts = 0 then begin
    prerr_endline "replay: the corpus is empty";
    exit 2
  end;
  exit (if !mismatches = 0 then 0 else 1)
