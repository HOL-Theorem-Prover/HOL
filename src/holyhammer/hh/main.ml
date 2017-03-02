(* Example usage: echo "conjecture" | ./hh 128 ../theories *)

open Hh_parse
open Thf1hh1
open Dependency
open Prepredict
open Write
open Filename

type filepath = string

(* Load theories and conjecture. *)
let init_proving_env thy_dir cj_file cj_name thydep_file thylo_file =
  let ((tyl,cl,thml),(thmh,roleh,thmlo)) = Init.init_dir thy_dir in
  let cj = Read.read_conjecture cj_file in
  let _ = init_dep_env thydep_file thylo_file (thmh,roleh,thmlo) in
  Thf1hh1.parse (tyl,cl,(cj_name,cj) :: thml) (* creating the term hash *)

(* Predict n premises for a conjecture, saving results to directory. *)
let predict (p : predictor) (out_dir : filepath) (n_preds : int) (cj : string) =
  predict_wrap p out_dir n_preds cj (gen_all ())

(* Parse command-line arguments, exiting with help if not valid.
   TODO: Read a conjecture itself, not its name. *)
let parse_commandline () =
  (* Saving results into two references and a array. *)
  let anon_counter = ref 0 in
  let anon_tab = Array.make 6 "" in
  let thydep_ref = ref "" in
  let thylo_ref = ref "" in
  let option_of_string s = if s = "" then None else Some s in
  let parse_anon anon = anon_tab.(!anon_counter) <- anon; incr anon_counter in
  let speclist =
    [("-thydep", Arg.Set_string thydep_ref, "Provides dependencies between theories");
     ("-thylo",  Arg.Set_string thylo_ref,  "Provides a linear order for the theories.\n" ^ 
      "Warning: all theories that do not belong to this order are ignored.")] 
  in
  let usage_msg = "HOL(y) Hammer. Usage: " ^ 
    Sys.argv.(0) ^ " <knn|nbayes|mepo|geo|kepo> <n_preds> <theory_dir> <cj_file> <cj_name> <out_dir>"
  in
  Arg.parse speclist parse_anon usage_msg;
  (* Processing the parsed objects. *)
  let predictor = match anon_tab.(0) with
      "knn" -> KNN
    | "nbayes" -> NaiveBayes
    | "mepo" -> Mepo
    | "geo" -> Geo
    | "kepo" -> Kepo
    | _ -> failwith "Unknown predictor." in
  let n_predictions = try int_of_string (anon_tab.(1))
    with _ -> failwith "Number of predictions have to be an integer." in
  let theory_dir = anon_tab.(2) in
  let cj_file = anon_tab.(3) in
  let cj_name = anon_tab.(4) in
  let out_dir = concat anon_tab.(5) "" in (* I don't understand why you need concat here *)
  let thydep_file = option_of_string !thydep_ref in
  let thylo_file = option_of_string !thylo_ref in
  (predictor, n_predictions, theory_dir, cj_file, cj_name, out_dir, thydep_file, thylo_file)


(* Main function. *)
(* TO DO: read the conjecture from the file *)
let _ =
  let (predictor, n_predictions, theory_dir, cj_file, 
       cj_name, out_dir, thydep_file, thylo_file) = parse_commandline () in

  print_endline ("Loading theories from " ^ theory_dir);
  init_proving_env theory_dir cj_file cj_name thydep_file thylo_file;

  print_endline ("Predicting " ^ (string_of_int n_predictions) ^ " lemmata");
  let axioms = predict predictor out_dir n_predictions cj_name in

  print_endline "Writing ATP file";
  let atp_path = Filename.concat out_dir "atp_in" in
  write_fof atp_path (cj_name, axioms);
;
