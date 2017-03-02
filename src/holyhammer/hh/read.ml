(*-------------------------------------------------------------------------- *)
(* Read statements .p,dependencies .hd, (.sx not yet supported) from the     *)
(* libraries exported from different ITPs. All .p and .hd files below the    *)
(* input directory (including files in subdirectories)                       *)
(*-------------------------------------------------------------------------- *)

(*-------------------------------------------------------------------------- 
  Input directories
  -------------------------------------------------------------------------- *)

let lib_dir = "../palibs"
let dir_of_itp p = match p with
    "h4"     -> lib_dir ^ "/h4-kananaskis10/standard_library"
  | "hl"     -> lib_dir ^ "/hl-225/standard_library"
  | "h4core" -> lib_dir ^ "/h4-kananaskis10/core_library"
  | "hlcore" -> lib_dir ^ "/hl-225/core_library"
  | "h4exp" -> lib_dir ^ "/h4-kananaskis10/exp_library"
  | "hlexp" -> lib_dir ^ "/hl-225/exp_library"
  | _        -> failwith "dir_of_prover"
let thydep_of_itp p = dir_of_itp p ^ "/info/theory_dep"
let thyorder_of_itp p = dir_of_itp p ^ "/info/theory_order"

(*-------------------------------------------------------------------------- 
  Reading a file
  -------------------------------------------------------------------------- *)

let file_iter fname fn =
  let ic = try open_in fname with Sys_error _ -> failwith ("file_iter: "^fname) in
  let next = ref 0 in
  let rec suck_lines () = fn !next (input_line ic); incr next; suck_lines () in
  try suck_lines () with End_of_file -> close_in ic

let file_to_stringl file =
  let r = ref [] in
  let f _ s = r := s :: !r in
    file_iter file f; List.rev !r

(*-------------------------------------------------------------------------- 
  Recursive search of files with a given extension
  -------------------------------------------------------------------------- *)

let rec rdirents isok prefix acc d =
  try
    let dirh = Unix.opendir (prefix ^ d) in
    let rec fs acc = try fs
      (
      let l = Unix.readdir dirh in 
      if l <> "." && l <> ".." 
        then rdirents isok (prefix ^ d ^ "/") acc l 
        else acc
      )
      with End_of_file -> acc in
    let ret = fs acc in
    Unix.closedir dirh; ret
  with Unix.Unix_error (Unix.ENOTDIR, _, _) -> if isok d then (prefix ^ d) :: acc else acc

let find_ext dir ext =
  let n_ext = String.length ext in
  let isok s = 
    let l = String.length s in 
    l > n_ext && String.sub s (l - n_ext) n_ext = ext 
  in
  let l = rdirents isok "" [] dir in
  let len = String.length dir in
  List.map (fun s -> String.sub s (len + 1) (String.length s - len - 1)) l

let find_p dir            = find_ext dir ".p"
let find_hd dir           = find_ext dir ".hd"
let find_fea dir          = find_ext dir ".fea"

(* TODO: To be moved to mizar and coq export *)
let find_xml2 dir         = find_ext dir ".xml2"
let find_con_xml dir      = find_ext dir ".con.xml"
let find_ind_xml dir      = find_ext dir ".ind.xml"
let find_con_body_xml dir = find_ext dir ".con.body.xml"


(*-------------------------------------------------------------------------- 
  Parsing statements (.p) and dependencies (.hd) and features (.fea)
  -------------------------------------------------------------------------- *)

(* Parsing statements *)
let rxpspace = Str.regexp " ";;

let read_statements_aux fname =
  let inc = Pervasives.open_in fname in
  let lexb = Lexing.from_channel inc in
  let rec parse_statements () =
    try let v = try Hh_parse.hhtop Hh_lexer.hh2lex lexb
      with Parsing.YYexit a -> Obj.magic a in v :: (parse_statements ())
    with End_of_file ->
      close_in inc;
      []
    | exn -> (* error message *)
      begin
        let curr = lexb.Lexing.lex_curr_p in
        let line = curr.Lexing.pos_lnum in
        let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
        Printf.eprintf "HH Parse error: %s line %i, char %i\n" fname line cnum;
        raise exn
      end
  in parse_statements ()

let read_statements dir filel =
  let f x = (Filename.chop_extension x, read_statements_aux (dir ^ "/" ^ x)) in
    List.map f filel

(* Parsing dependencies *)
let read_thy_graph fname =
  let hash = Hashtbl.create 1000 in
  let add _ line = 
    match Str.split rxpspace line with
      []     -> failwith ("empty line: " ^ fname)
    | h :: t -> Hashtbl.add hash h t
  in
    file_iter fname add; hash	

let read_thy_lo fname =
  let ll = ref [] in
  let add _ s = ll := (Str.split rxpspace s) :: !ll in
    file_iter fname add; List.hd(List.rev !ll)

let read_deps dir filel =
  let hash = Hashtbl.create 20000 in
  let add fname _ line = 
    match Str.split rxpspace line with
      []     -> failwith ("empty .hd file line: " ^ fname)
    | h :: t -> Hashtbl.add hash h (Filename.chop_extension fname, t)    
  in
  List.iter (fun f -> file_iter (dir ^ "/" ^ f) (add f)) filel;
  hash

(* Parsing features *)
let read_features dir filel =
  let hash = Hashtbl.create 20000 in
  let add fname _ line = 
    match Str.split rxpspace line with
      []     -> failwith ("empty .fea file line: " ^ fname)
    | h :: t -> Hashtbl.add hash h t
  in
  List.iter (fun f -> file_iter (dir ^ "/" ^ f) (add f)) filel;
  (hash, List.map Filename.chop_extension filel)

(*-------------------------------------------------------------------------- 
  Main reading functions
  -------------------------------------------------------------------------- *)

(* Features *) 
let read_features_dir dir =
  let fea = find_fea dir in read_features dir fea

(* Statements + Dependencies *) 
let read_dir dir =
  let hds = find_hd dir in
  let ps = find_p dir in
  (read_deps dir hds, read_statements dir ps)

(* Conjecture *)
let read_conjecture fname = 
  let fourth (_,_,_,t) = t in
  fourth (List.hd (read_statements_aux fname))

(* Kept for thf0hh1 *)
let read_prf filel =
  let hash = Hashtbl.create 1000 in
  let read1 fname =
    let add (_, name, ty, tm) = Hashtbl.add hash (fname, name) (ty, tm) in
    let l = read_statements_aux fname in
    List.iter add l
  in
  List.iter read1 filel; 
	hash

