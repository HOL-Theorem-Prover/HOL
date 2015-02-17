(* Example usage: echo "conjecture" | ./hh_h4 128 ../theories *)

open Hh_parse
open Thf1hh1
open Dependency
open Predict_knn
open Filename

type filepath = string

(* Do we only need these additional theorems for HOL4 or also in
   HOL Light, Thibault? Also in HOL Light *)
let additional_theorems () =
  let falsity = Fusion.Sequent([],Hl_parser.parse_term "~F") in
  let ext = Fusion.Sequent([],Hl_parser.parse_term "!f g. (!x. f x = g x) ==> f = g") in
  [Bool.tRUTH; falsity; Bool.bOOL_CASES_AX; ext],
  ["HL_TRUTH"; "HL_FALSITY"; "HL_BOOL_CASES"; "HL_EXT"]

(* Make a theorem without premises (?) from a theorem name. *)
let mk_thm (thm_name : string) = Fusion.Sequent ([], term_of thm_name)

(* Write a FOF file from given conjecture and axioms for use with an ATP. *)
let write_fof (fname : filepath) (cj_name, axioms) =
  let (ath, a) = additional_theorems () in
  let (pth, p) = (ath @ List.map mk_thm axioms, a @ axioms) in
  Hh_write.write_atp_proof fname (pth,p) cj_name (term_of cj_name)



(* Load theories and conjecture. *)
let init_interactive (thy_dir : filepath) (cj_file : filepath) (cj_name : string) =
  let ((tyl,cl,thml),(thmh,roleh,thmlo)) = Init.init_dir thy_dir in
  let cj = Read.read_conjecture cj_file in
  let _ = init_depenv (Some (thy_dir ^ "/thydep")) None (thmh,roleh,thmlo) in
  Thf1hh1.parse (tyl,cl,(cj_name,cj) :: thml)


(* Predict n premises for a conjecture, saving results to directory. *)
let predict (out_dir : filepath) (n_preds : int) (cj_name : string) =
  let cj = term_of cj_name in
  predict_interactive out_dir n_preds cj (gen_all ())


(* Help text displayed when incorrect arguments supplied. *)
let help =
"HOL(y) Hammer.
Usage: " ^ Sys.argv.(0) ^ " <n_predictions> <theory_dir> <cj_file> <cj_name> <out_dir>"
;;

(* Parse command-line arguments, exiting with help if not valid.
   TODO: Read a conjecture itself, not its name. *)
let parse_commandline () =
  if Array.length Sys.argv <> 6
  then begin
    print_endline help;
    exit 1
  end;

  let n_predictions = try int_of_string (Sys.argv.(1))
    with _ -> failwith "Number of predictions have to be an integer." in
  let theory_dir = Sys.argv.(2) in
  let cj_file = Sys.argv.(3) in
  let cj_name = Sys.argv.(4) in
  let out_dir = concat Sys.argv.(5) "" in

  (n_predictions, theory_dir, cj_file, cj_name, out_dir)


(* Main function. *)
let _ =
  let (n_predictions, theory_dir, cj_file, cj_name, out_dir) = parse_commandline () in

  print_endline ("Loading theories from " ^ theory_dir);
  init_interactive theory_dir cj_file cj_name;

  print_endline ("Predicting " ^ (string_of_int n_predictions) ^ " lemmata");
  let axioms = predict out_dir n_predictions cj_name in

  print_endline "Writing ATP file";
  let atp_path = Filename.concat out_dir "atp_in" in
  write_fof atp_path (cj_name, axioms);
;
