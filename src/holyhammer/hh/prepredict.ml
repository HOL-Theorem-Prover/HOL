(*-------------------------------------------------------------------------- *)
(* Printing the necessary files for the predictors, such as dependencies     *)
(* and features.                                                             *)
(*-------------------------------------------------------------------------- *)

open Dependency
open Thf1hh1

let tmp_file = "predictions/predict_hh_";;

(* Predictor *)
let os = output_string 

let print_dep fname axl =
  let ocdep = open_out (fname ^ "dep") in
  let f x   = os ocdep (x ^ ":" ^ String.concat " " (dep_of x) ^ "\n") in 
    List.iter f axl; close_out ocdep

let out_dep ocdep axl =
  let f x   = os ocdep (x ^ ":" ^ String.concat " " (dep_of x) ^ "\n") in 
    List.iter f axl

let print_seq fname axl =
  let ocseq = open_out (fname ^ "seq") in
  let f x   = os ocseq (x ^ "\n") in 
    List.iter f axl; close_out ocseq 

let print_syms fname axassoc =
  let ocsym = open_out (fname ^ "syms") in
  let axsym = List.map (fun (a,b) -> (a, Hh_symbols.get_symbols b)) axassoc in
  let f (x,ths) =  
    let s = match ths with
      [] -> "\n"
    | _ -> "\"" ^ String.concat "\", \"" ths ^ "\"\n"
    in
      os ocsym (x ^ ":" ^ s) 
  in    
    List.iter f axsym; close_out ocsym

let print_csyms fname cj =
  let csyms = Hh_symbols.get_symbols cj in
  let ocsym = open_out (fname ^ "csyms") in
    if csyms = [] 
      then os ocsym "\n" 
      else os ocsym ("\"" ^ (String.concat "\", \"" csyms) ^ "\"\n");
    close_out ocsym

let print_all fname axl conj =
  let cj = term_of conj in
  let axassoc = List.map (fun x -> (x,term_of x)) axl in
    print_dep fname axl;
    print_seq fname axl;
    print_syms fname axassoc;
    print_csyms fname cj

type predictor = KNN | NaiveBayes | Mepo

let run_predictor = function
  KNN        -> Predict.knn_advice2
| NaiveBayes -> Predict.nb_advice2
| Mepo       -> Predict.mepo_advice2

let predict predictor n conj axl =
  print_all tmp_file axl conj;
  run_predictor predictor tmp_file n


let print_all_interactive fname axl cj =
  let axassoc = List.map (fun x -> (x,term_of x)) axl in
    print_dep fname axl;
    print_seq fname axl;
    print_syms fname axassoc;
    print_csyms fname cj
  
let predict_interactive predictor file_prefix n cjterm axnamel =
  print_all_interactive file_prefix axnamel cjterm;
  run_predictor predictor file_prefix n

(* Matching experiments 1 *)

let run_predictor_matching = function
  KNN        -> Predict.knn_advice3
| NaiveBayes -> Predict.nb_advice3
| _          -> failwith "not supported"

let print_all_matching file_prefix dep_env1 dep_env2 axl1 axl2 cjterm =
  let axnamel = axl1 @ axl2 in
  let axterml = List.map (fun x -> (x,term_of x)) axnamel in
    (* dependencies *)
    let ocdep = open_out (file_prefix ^ "dep") in
    set_dep_env dep_env1;
    out_dep ocdep axl1;
    set_dep_env dep_env2;
    out_dep ocdep axl2;
    close_out ocdep;
    (* term *)
    print_seq   file_prefix axnamel;
    print_syms  file_prefix axterml;
    print_csyms file_prefix cjterm
  
let predict_matching predictor file_prefix dep_env1 dep_env2 axl1 axl2 n cjterm =
  print_all_matching file_prefix dep_env1 dep_env2 axl1 axl2 cjterm;
  run_predictor_matching predictor file_prefix n













