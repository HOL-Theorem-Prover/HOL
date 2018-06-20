let mydir = Filename.dirname (Sys.executable_name);;

let os = output_string;;

let unlink = ref [];;

let cpp_advice axsyms csyms cmd =
  let fname = Filename.temp_file "predict" "" in
  let ocsym = open_out (fname ^ "syms") in
  let ocseq = open_out (fname ^ "seq") in
  let ocdep = open_out (fname ^ "dep") in
  unlink := fname :: (fname ^ "syms") :: (fname ^ "csyms") :: (fname ^ "seq") :: (fname ^ "dep") :: (fname ^ "out") :: !unlink;
  List.iter (fun (thn, ths) ->
    os ocseq thn; output_char ocseq '\n';
    os ocdep thn; os ocdep ":\n";
    os ocsym thn; output_char ocsym ':';
    match ths with
      [] -> output_char ocsym '\n'
    | l -> output_char ocsym '\"'; os ocsym (String.concat "\", \"" l); os ocsym "\"\n"
  ) axsyms;
  close_out ocsym;
  close_out ocseq;
  close_out ocdep;
  let ocsym = open_out (fname ^ "csyms") in
  output_char ocsym '\"'; os ocsym (String.concat "\", \"" csyms); os ocsym "\"\n";
  close_out ocsym;
  ignore (Sys.command (cmd fname));
  let ic = open_in (fname ^ "out") in
  let predict = Str.split (Str.regexp " ") (try input_line ic with End_of_file -> failwith "predictor did not return advice") in
  close_in ic;
  predict
;;

let knn_advice divider axsyms csyms limit =
  (*let limit = min (List.length axsyms) limit in
  let kno = limit / divider in*)
  let cmd s = Printf.sprintf "%s/../predict/predict knn %i %ssyms %sdep %sseq < %scsyms > %sout 2>/dev/null" mydir limit s s s s s in
  cpp_advice axsyms csyms cmd
;;

let mepo_advice axsyms csyms limit =
  let cmd s = Printf.sprintf "%s/../predict/predict mepo %i %ssyms %sdep %sseq < %scsyms > %sout 2>/dev/null" mydir limit s s s s s in
  cpp_advice axsyms csyms cmd
;;

let nb_advice axsyms csyms limit =
  let cmd s = Printf.sprintf "%s/../predict/predict nbayes %i %ssyms %sdep %sseq < %scsyms > %sout 2>/dev/null" mydir limit s s s s s in
  cpp_advice axsyms csyms cmd
;;

(* Thibault's experiments *)
let cpp_advice2 fname cmd =
  print_endline ("Running predictor: " ^ cmd fname);
  ignore (Sys.command (cmd fname));
  let ic = open_in (fname ^ "out") in
  let predict = Str.split (Str.regexp " ") 
    (try input_line ic with End_of_file -> failwith "predictor did not return advice") in
  close_in ic;
  predict

let knn_advice2 fname limit =
  let cmd s = Printf.sprintf 
    "../predict/predict %ssyms %sdep %sseq -n %i -p knn < %scsyms > %sout 2> %serror" 
    s s s limit s s s in
  cpp_advice2 fname cmd

let nb_advice2 fname limit =
  let cmd s = Printf.sprintf 
    "../predict/predict %ssyms %sdep %sseq -n %i -p nbayes < %scsyms > %sout 2> %serror"
    s s s limit s s s in
  cpp_advice2 fname cmd

let mepo_advice2 fname limit =
  let cmd s = Printf.sprintf 
     "../predict/mepo/mepo3 %i %ssyms %sdep %i %sseq < %scsyms > %sout 2> %serror"
     0 s s limit s s s s in
  cpp_advice2 fname cmd

let geo_advice2 fname limit =
  let cmd s = Printf.sprintf 
     "../predict/mepo/geo %i %f %ssyms %sdep %i %sseq < %scsyms > %sout 2> %serror"
     1 0.99 s s limit s s s s in
  cpp_advice2 fname cmd

let kepo_advice2 fname limit =
  let l1 = mepo_advice2 fname limit in
  let l2 = knn_advice2 fname limit in
  Toolbox.mk_set (l1 @ l2)

(* Matching experiments *)

let nb_advice3 fname limit =
  let cmd s = Printf.sprintf "../../predict/predict %ssyms %sdep %sseq -n %i -p nbayes < %scsyms > %sout 2> %serror"  s s s limit s s s in
  cpp_advice2 fname cmd
;;

let knn_advice3 fname limit =
  let cmd s = Printf.sprintf "../../predict/predict %ssyms %sdep %sseq -n %i -p knn < %scsyms > %sout 2> %serror"  s s s limit s s s in
  cpp_advice2 fname cmd
;;




