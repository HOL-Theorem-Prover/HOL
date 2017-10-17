(* This is the main loop of a HOLyHammer based THF0 prover
   submitted to CASC 2014 *)
let try_predict pred time axassoc cname conj prover =
  let fname = Filename.temp_file "hh" ".p" in
  Predict.unlink := fname :: !Predict.unlink;
  let pth = List.map (fun x -> Fusion.Sequent ([], List.assoc x axassoc)) pred in
  let pth, p = [Bool.tRUTH; Bool.bOOL_CASES_AX] @ pth, ["TRUTH"; "BOOL_CASES"] @ pred in
  Hh_write.write_atp_proof fname (pth, p) cname conj;
  Thf0hh1.run_prover time fname prover
;;

let try_predict_seq predl t axassoc cname conj =
  let t = string_of_int (int_of_string t / (List.length predl)) in
  let fold_fun sf (pred,prover) =
    match sf with Some _ -> sf | None ->
      (Printf.printf "Trying: pred len %i prover %s\n%!" (List.length pred) (Digest.to_hex (Digest.string prover));
       try_predict pred t axassoc cname conj prover) in
  List.fold_left fold_fun None predl
;;

let make_maybe_seq len axsyms csyms axassoc =
  let l2 = int_of_float (1.5 *. ((float_of_int len) ** 0.6)) in
  let l3 = int_of_float (3.0 *. ((float_of_int len) ** 0.6)) in
  let l4 = int_of_float (5.0 *. ((float_of_int len) ** 0.6)) in
  let a1 = Predict.mepo_advice axsyms csyms l4 in
  let a2 = Predict.knn_advice 4 axsyms csyms l3 in
  let a3 = Predict.nb_advice axsyms csyms l2 in
  [(a1,"e"); (a2,"e"); (a3,"e"); (List.map fst axassoc, "e")]
;;

let fast_seq = [
  "atpstr_my_fe548d15a6fc730fd350de634ad9d912ae198efd";
  "atpstr_my_e6869afe09f22abfbe1163ee95524cfdbfe77603";
  "my7simple";
  "atpstr_my_a473e2c35f909af4ba00d9f1a7a8a454a851ed9c";
  "atpstr_my_edc94794a7d25c504761344c2a8b4afaac43a2d0";
  "my24simple";
  "G_E___008_C45_F1_AE_CS_SP_S0Y";
  "X_____auto_sine03";
  "atpstr_my_69856783cec8fab1acccfe08bb382ad42c8475df";
  "H_____047_C18_F1_AE_R8_CS_SP_S2S";
  "G_E___024_B07_F1_PI_AE_Q4_CS_SP_S0Y";
  "atpstr_my_e8ac4ce30401bd9e99200725cfa03816a32e3aa4";
];;

let make_fast_seq axnames = List.map (fun p -> (axnames, Proto.lookup p)) fast_seq;;

let slow_seq = [
  ("atpstr_my_fe548d15a6fc730fd350de634ad9d912ae198efd","all",0);
  ("atpstr_my_a74b37f2d8b7e35be554fc999f671188cf40f113","mepo",1);
  ("my24simple","all",0);
  ("G_E___008_C18_F1_PI_AE_IO_Q7_CS_SP_S4S","mepo",1);
  ("X_____auto_sine05","all",0);
  ("atpstr_my_e6869afe09f22abfbe1163ee95524cfdbfe77603","mepo",2);
  ("atpstr_my_69856783cec8fab1acccfe08bb382ad42c8475df","knn2",2);
  ("atpstr_my_edc94794a7d25c504761344c2a8b4afaac43a2d0","mepo",2);
  ("atpstr_my_9f72062a403172caf26fbe878a32becf1403c276","knn8",3);
  ("atpstr_my_9f72062a403172caf26fbe878a32becf1403c276","nb",2);
  ("atpstr_my_4e6e6157a8ac18b9bae11142d40377c9660db06b","knn8",3);
  ("atpstr_my_c284f1f10aedfccc65cdb7d9b1210ef814cb8f1a","mepo",2);
  ("atpstr_my_a4a4da5778ba9bebf9bc5e616786c7ad501b1af5","knn2",1);
  ("atpstr_my_7b674c1081cd73ca6ce34d02596e6f6fd903ac6c","mepo",2);
  ("atpstr_my_edc94794a7d25c504761344c2a8b4afaac43a2d0","mepo",3);
  ("G_E___024_B07_F1_PI_AE_Q4_CS_SP_S0Y","all",0);
];;

let rec cut_list acc n = function
  [] -> List.rev acc
| h :: t -> if n = 0 then List.rev acc else cut_list (h :: acc) (n - 1) t;;

let make_slow_seq len axsyms csyms axassoc =
  let len1 = int_of_float (1.5 *. ((float_of_int len) ** 0.6))
  and len2 = int_of_float (3.0 *. ((float_of_int len) ** 0.6))
  and len3 = int_of_float (5.0 *. ((float_of_int len) ** 0.6)) in
  let knn8 = Predict.knn_advice 8 axsyms csyms len3 in
  let knn2 = Predict.knn_advice 2 axsyms csyms len2 in
  let mepo = Predict.mepo_advice axsyms csyms len3 in
  let nb = Predict.nb_advice axsyms csyms len2 in
  let map_len pl = if pl = 1 then len1 else if pl = 2 then len2 else len3 in
  let mapper (p, pm, pl) =
    match pm with
    "knn8" -> (cut_list [] (map_len pl) knn8,Proto.lookup p)
  | "knn2" -> (cut_list [] (map_len pl) knn2,Proto.lookup p)
  | "mepo" -> (cut_list [] (map_len pl) mepo,Proto.lookup p)
  | "nb" -> (cut_list [] (map_len pl) nb,Proto.lookup p)
  | "all" -> (List.map fst axassoc,Proto.lookup p)
  | _ -> failwith "unknown prediction strategy"
  in
  List.map mapper slow_seq
;;

let make_pred predmethod predlen axassoc conj prover =
  let len = List.length axassoc in
  if len < 100 && predmethod = "" then make_fast_seq (List.map fst axassoc) else
  let axsyms = List.map (fun (a,b) -> (a, Hh_symbols.get_symbols b)) axassoc in
  let csyms = Hh_symbols.get_symbols conj in
  if predmethod = "" then make_slow_seq len axsyms csyms axassoc else
  let l =
    if predlen = 1 then int_of_float (1.5 *. ((float_of_int len) ** 0.6)) else
    if predlen = 2 then int_of_float (3.0 *. ((float_of_int len) ** 0.6))
                   else int_of_float (5.0 *. ((float_of_int len) ** 0.6)) in
  let a = match predmethod with
    "knn8" -> Predict.knn_advice 8 axsyms csyms l
  | "knn4" -> Predict.knn_advice 4 axsyms csyms l
  | "knn2" -> Predict.knn_advice 2 axsyms csyms l
  | "mepo" -> Predict.mepo_advice axsyms csyms l
  | "nb" -> Predict.nb_advice axsyms csyms l
  | "all" -> List.map fst axassoc
  | _ -> failwith "unknown prediction strategy"
  in
  [(a, prover)]
;;

(*let (time, file, predmethod, predlen, prover) = ("300", "/tmp/SEU824^3.p", "", 0, "e");;*)

try
  let (time, file, predmethod, predlen, prover) = match Array.to_list Sys.argv with
      [ _; t; f] -> (t, f, "", 0, "e")
    | _ :: t :: f :: pm :: len :: pr -> (t, f, pm, int_of_string len, String.concat " " pr)
    | _ -> Printf.printf "Hol(y)Hammer version 20140613\nUsage: ./hh time_in_seconds thf_file_name [pred_method predlen prover]\n";
       failwith "Invalid executable arguments"
  in
  (try ignore (int_of_string time) with _ -> failwith "Time must be integer");
  let (cname, conj, axassoc) = Thf0hh1.read_file file in
  let pl = make_pred predmethod predlen axassoc conj prover in
  match try_predict_seq pl time axassoc cname conj with
    None   -> Printf.printf "SZS status Timeout\n"
  | Some l -> Printf.printf "SZS status Theorem\nSZS core %s\n" (String.concat " " l)
  (*if ret > 0 then Printf.printf "SZS status GaveUp\n" else*)
with
  Failure   x -> Format.printf "SZS status Error\n%s\n" x
| Sys_error x -> Format.printf "SZS status Error\nSys_error %s\n" x
|           x -> Format.printf "SZS status Error\nUnhandled Exception\n"; flush stdout; raise x
;;

List.iter (fun x -> try Unix.unlink x with _ -> ()) !Predict.unlink;


(*Hh_write.write_atp_proof "testo.p"
  ([Bool.tRUTH; Bool.bOOL_CASES_AX], ["TRUTH"; "BOOL_CASES"])
  "conj" (Parser.parse_term "x = x")
;;*)
