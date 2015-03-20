let file_iter fname fn =
  let ic = try open_in fname with Sys_error _ -> failwith ("file_iter: "^fname) in
  let next = ref 0 in
  let rec suck_lines () = fn !next (input_line ic); incr next; suck_lines () in
  try suck_lines () with End_of_file -> close_in ic
;;

let rec rdirents isok prefix acc d =
  try
    let dirh = Unix.opendir (prefix ^ d) in
    let rec fs acc = try fs
      (let l = Unix.readdir dirh in if l <> "." && l <> ".." then rdirents isok (prefix ^ d ^ "/") acc l else acc)
      with End_of_file -> acc in
    let ret = fs acc in
    Unix.closedir dirh; ret
  with Unix.Unix_error (Unix.ENOTDIR, _, _) -> if isok d then (prefix ^ d) :: acc else acc
;;

let find_ext dir ext =
  let n_ext = String.length ext in
  let isok s =
    let l = String.length s in
    l > n_ext && String.sub s (l - n_ext) n_ext = ext
  in
  let l = rdirents isok "" [] dir in
  let len = String.length dir in
  List.map (fun s -> String.sub s (len + 1) (String.length s - len - 1)) l
;;

let find_p dir            = find_ext dir ".p"
let find_hd dir           = find_ext dir ".hd"
let find_xml2 dir         = find_ext dir ".xml2"
let find_con_xml dir      = find_ext dir ".con.xml"
let find_ind_xml dir      = find_ext dir ".ind.xml"
let find_con_body_xml dir = find_ext dir ".con.body.xml"


let file_to_stringl file =
  let r = ref [] in
  let f _ s = r := s :: !r in
    file_iter file f; List.rev !r
;;

let rxpspace = Str.regexp " ";;

let read_prf_aux fname =
  let inc = Pervasives.open_in fname in
  let lexb = Lexing.from_channel inc in
  let rec prf () =
    try let v = try Hh_parse.hhtop Hh_lexer.hh2lex lexb
      with Parsing.YYexit a -> Obj.magic a in v :: (prf ())
    with End_of_file ->
      close_in inc;
      []
    | exn ->
      begin
        let curr = lexb.Lexing.lex_curr_p in
        let line = curr.Lexing.pos_lnum in
        let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
        Printf.eprintf "HH Parse error: %s line %i, char %i\n" fname line cnum;
        raise exn
      end
  in prf ()
;;

let read_prf filel =
  let hash = Hashtbl.create 1000 in
  let read1 fname =
    let add (_, name, ty, tm) = Hashtbl.add hash (fname, name) (ty, tm) in
    let l = read_prf_aux fname in
    List.iter add l
  in
  List.iter read1 filel;
	hash
;;

let read_deps dir files =
  let hash = Hashtbl.create 1000 in
  let add fname _ s =
    match Str.split rxpspace s with
      (h :: t) -> Hashtbl.add hash (fname, h) t
    | _ -> failwith ("empty .hd file line: " ^ fname)
  in
  List.iter (fun f -> file_iter (dir ^ "/" ^ f) (add f)) files;
  hash
;;

let read_dir dir =
  let hds = find_hd dir in
  let ps = List.map (fun x -> String.sub x 0 (String.length x - 2) ^ "p") hds in
  (read_deps dir hds, read_prf (List.map (fun x -> (dir ^ "/" ^ x)) ps))
;;

(* Alternative format used in thf1hh1.ml and generate.ml *)
(* Different reading fonction for hol_light
  let s1 = List.hd (List.rev (Str.split (Str.regexp "[/]") s)) in
  let s2 = List.hd (Str.split (Str.regexp "[.]") s1) in
*)
let read_thy_graph fname =
  let hash = Hashtbl.create 1000 in
  let add _ s = let (h :: t) = Str.split rxpspace s in Hashtbl.add hash h t in
    file_iter fname add; hash

let read_thy_lo fname =
  let ll = ref [] in
  let add _ s = ll := (Str.split rxpspace s) :: !ll in
    file_iter fname add; List.hd(List.rev !ll)

let alt_read_prf dir filel =
  List.map (fun fname -> (Filename.chop_extension fname, read_prf_aux (dir ^ "/" ^ fname))) filel

let alt_read_deps dir filel =
  let hash = Hashtbl.create 20000 in
  let add fname _ s =
    let (h :: t) = Str.split rxpspace s in
    Hashtbl.add hash h (Filename.chop_extension fname, t)
  in
  List.iter (fun f -> file_iter (dir ^ "/" ^ f) (add f)) filel;
  hash

let alt_read_dir dir =
  let hds = find_hd dir in
  let ps = List.map (fun x -> String.sub x 0 (String.length x - 2) ^ "p") hds in
  (alt_read_deps dir hds, alt_read_prf dir ps)

(* holyhammer for hol4 *)
let read_conjecture fname =
  let fourth (_,_,_,t) = t in
  fourth (List.hd (read_prf_aux fname))

(* No deps *)
let read_dir_nodep dir = alt_read_prf dir (find_p dir)




