(*-------------------------------------------------------------------------- 
  Precomputing the features.
  -------------------------------------------------------------------------- *)

open Thf1hh1
open Toolbox

(* Optimization for multiple experiments (memorize previous call of get_symbols) *)
let feature_hash = ref (Hashtbl.create 20000)

let feature_of thm = 
  try Hashtbl.find !feature_hash thm
  with _ ->
    let l = Hh_symbols.get_symbols (term_of thm) in
    Hashtbl.add (!feature_hash) thm l;
    l

(* Never store the current theory as it may changed *)
let string_of_feature thm = (thm ^ " " ^ String.concat " " (feature_of thm))

let export_features dir thmlo thy = 
  let fname = dir ^ "/" ^ thy ^ ".fea" in
  let thml = List.assoc thy thmlo in
  let l = List.map string_of_feature thml in
  writel fname l

let updating_features dir ct_option =
  let ((tyl,cl,thml),(deph,roleh,thmlo),(feah,fea_thyl)) = 
    Init.init_dir_features dir
  in
  feature_hash := feah;
  let thyl = List.map fst thmlo in
  let not_ct x = match ct_option with
    None    -> true 
  | Some ct -> ct <> x in
  let updatable_thy thy = not (List.mem thy fea_thyl) && not_ct thy in
  let mthyl = List.filter updatable_thy thyl in
  print_string ("- computing features for " ^ 
                string_of_int (List.length mthyl) ^ " theories\n");
  let mthml = List.concat (List.map (fun x -> List.assoc x thmlo) mthyl) in
  let mthml2 = List.filter (fun (x,_) -> List.mem x mthml) thml in
  Thf1hh1.parse (tyl,cl,mthml2);
  List.iter (export_features dir thmlo) mthyl

(* Running
terminal command: rlwrap ./top -I hh1

open Features;;
open Toolbox;;
let dir = "../palibs/cakeml";;

updating_features dir None;;
time_here Init.init_dir_features dir;;
*)
