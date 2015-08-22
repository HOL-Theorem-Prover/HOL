(*-------------------------------------------------------------------------- *)
(* Printing the necessary files for the predictors, such as dependencies     *)
(* and features.                                                             *)
(*-------------------------------------------------------------------------- *)

open Features
open Dependency
open Thf1hh1

(*-------------------------------------------------------------------------- 
  Preparing files for the predictor
  -------------------------------------------------------------------------- *)

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

let print_syms fname axl =
  let ocsym = open_out (fname ^ "syms") in
  let axsym = List.map (fun a -> (a, feature_of a)) axl in
  let f (x,ths) =  
    let s = match ths with
      [] -> "\n"
    | _ -> "\"" ^ String.concat "\", \"" ths ^ "\"\n"
    in
      os ocsym (x ^ ":" ^ s) 
  in    
    List.iter f axsym; close_out ocsym

let print_csyms fname cjname =
  let csyms = feature_of cjname in
  let ocsym = open_out (fname ^ "csyms") in
    if csyms = [] 
      then os ocsym "\n" 
      else os ocsym ("\"" ^ (String.concat "\", \"" csyms) ^ "\"\n");
    close_out ocsym

let predict_print_all fname axl cjname =
    print_dep fname axl;
    print_seq fname axl;
    print_syms fname axl;
    print_csyms fname cjname


(*-------------------------------------------------------------------------- 
  Running the predictor
  -------------------------------------------------------------------------- *)

type predictor = KNN | NaiveBayes | Mepo | Geo | Kepo

let run_predictor p fname limit = 
  if limit <= 0 
  then [] 
  else 
    begin
    match p with
      KNN        -> Predict.knn_advice2 fname limit
    | NaiveBayes -> Predict.nb_advice2 fname limit
    | Mepo       -> Predict.mepo_advice2 fname limit
    | Geo        -> Predict.geo_advice2 fname limit
    | Kepo       -> Predict.kepo_advice2 fname limit
    end

let predict_wrap predictor file_prefix n cj axl =
  predict_print_all file_prefix axl cj;
  run_predictor predictor file_prefix n

(* Matching experiments 1 *)

let run_predictor_matching = function
  KNN        -> Predict.knn_advice3
| NaiveBayes -> Predict.nb_advice3
| _          -> failwith "not supported"

let print_all_matching file_prefix dep_env1 dep_env2 axl1 axl2 cjname =
  let axl = axl1 @ axl2 in
    (* dependencies *)
    let ocdep = open_out (file_prefix ^ "dep") in
    set_dep_env dep_env1;
    out_dep ocdep axl1;
    set_dep_env dep_env2;
    out_dep ocdep axl2;
    close_out ocdep;
    (* term *)
    print_seq   file_prefix axl;
    print_syms  file_prefix axl;
    print_csyms file_prefix cjname
  
let predict_matching predictor file_prefix dep_env1 dep_env2 axl1 axl2 n cjname =
  print_all_matching file_prefix dep_env1 dep_env2 axl1 axl2 cjname;
  run_predictor_matching predictor file_prefix n













