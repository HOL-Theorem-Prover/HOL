open Dependency
open Thf1hh1

let tmp_file = "predictions/predict_hh_";;

(* Predictor *)
let os = output_string 

let print_dep fname axl =
  let ocdep = open_out (fname ^ "dep") in
  let f x   = os ocdep (x ^ ":" ^ String.concat " " (dep_of x) ^ "\n") in 
    List.iter f axl; close_out ocdep

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
    os ocsym ("\"" ^ (String.concat "\", \"" csyms) ^ "\"\n");
    close_out ocsym

let print_all fname axl conj =
  let cj = term_of conj in
  let axassoc = List.map (fun x -> (x,term_of x)) axl in
    print_dep fname axl;
    print_seq fname axl;
    print_syms fname axassoc;
    print_csyms fname cj

type predictor = KNN | NaiveBayes;;

let run_predictor = function
  KNN        -> Predict.knn_advice2
| NaiveBayes -> Predict.nb_advice2;;

let predict predictor n conj axl =
  print_all tmp_file axl conj;
  run_predictor predictor tmp_file n

let print_all_interactive fname axl cj =
  let axassoc = List.map (fun x -> (x,term_of x)) axl in
    print_dep fname axl;
    print_seq fname axl;
    print_syms fname axassoc;
    print_csyms fname cj
  
let predict_interactive predictor file_prefix n conj axl =
  print_all_interactive file_prefix axl conj;
  run_predictor predictor file_prefix n
