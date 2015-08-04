open Fusion;;
open Format;;
open Printer;;
open Basics;;
open Lib;;
open Bool;;

let theorems = ref [];;



module Sm = Map.Make(struct type t = string let compare = compare end);;
module Tmm = Map.Make(struct type t = term let compare = compare end);;
let os = output_string;;

let print_to_lstring printer =
  let sbuff = ref "" in
  let output s m n = if s <> "\n" then sbuff := (!sbuff)^(String.sub s m n) else ()
  and flush() = () in
  let fmt = make_formatter output flush in
  pp_set_max_boxes fmt 1; pp_set_margin fmt 1000000000; pp_set_max_indent fmt 1000000000;
  fun i -> ignore(printer fmt i); ignore(pp_print_flush fmt ()); let s = !sbuff in sbuff := ""; s
;;
let lstring_of_type = print_to_lstring pp_print_type;;
let lstring_of_term = print_to_lstring pp_print_term;;
let lstring_of_thm = print_to_lstring pp_print_thm;;

let rec fold_apps fn bnd tm sofar =
  try let l,r = try dest_forall tm with Failure _ ->
                try dest_exists tm with Failure _ ->
                    dest_abs tm in
      fold_apps fn (l :: bnd) r sofar
  with Failure _ -> try
      let l,r = try dest_conj tm with Failure _ ->
                try dest_disj tm with Failure _ ->
                try (let l,r = dest_eq tm in if type_of l = bool_ty then failwith "equivalence" else (l,r)) with Failure _ ->
                    dest_imp tm in
      fold_apps fn bnd r (fold_apps fn bnd l sofar)
  with Failure _ -> try
      let tm = dest_neg tm in fold_apps fn bnd tm sofar
  with Failure _ ->
      let hop, args = strip_comb tm in
      let sofar = if is_abs hop then fold_apps fn bnd hop sofar else sofar in
      itlist (fold_apps fn bnd) args (fn bnd hop args sofar);;

let funtys_of_tm tm =
  let mergel l = setify (List.concat l) in
  let tys tm = map type_of (find_terms (fun x -> is_var x or is_const x) tm) in
  let rec funtypes t =
    if is_vartype t then [] else
    let (s, l) = dest_type t in
    mergel ([s]::(map funtypes l)) in
  mergel (map funtypes (tys tm))
;;

let rec rename_bnds map min tm prfun =
  try let l, r = dest_abs tm in
    let _, ty = dest_var l in
    let nl = mk_var (prfun min ty, ty) in
    mk_abs (nl, rename_bnds (Tmm.add l nl (Tmm.remove l map)) (min + 1) r prfun)
  with _ -> try let l, r = dest_comb tm in
    mk_comb (rename_bnds map min l prfun, rename_bnds map min r prfun)
  with _ -> try Tmm.find tm map with _ -> tm
;;
let rename_all tm prfun =
  let fs = frees tm in
  let tys = map (o snd dest_var) fs in
  let s = Array.to_list (Array.init (List.length fs) (fun i -> prfun i (List.nth tys i))) in
  let nfs = map mk_var (zip s tys) in
  rename_bnds Tmm.empty (List.length fs) (vsubst (zip nfs fs) tm) prfun
;;
let get_subterms tm prfun =
  let fold_apps_fn _ hop args ts =
    Sm.add (lstring_of_term (rename_all (list_mk_comb (hop, args)) prfun)) () ts
  in map fst (Sm.bindings (fold_apps fold_apps_fn [] tm Sm.empty))
;;

let prfun0 min ty = "A0";;
let prfun min ty = "A" ^ string_of_int min;;
let prfunt min ty = "A" ^ lstring_of_type ty;;
let prfunnt min ty = "A" ^ string_of_int min ^ lstring_of_type ty;;

let retyvar tm =
  let tvs = type_vars_in_term tm in
  let tyvno = ref (Char.code 'A' - 1) in
  let ins = List.map (fun x -> incr tyvno; (mk_vartype (String.make 1 (Char.chr !tyvno)),x)) tvs in
  inst ins tm
;;

let retyvar0 tm =
  let tvs = type_vars_in_term tm in
  let ins = List.map (fun x -> (mk_vartype "A",x)) tvs in
  inst ins tm
;;

let get_symbols tm =
  let cns = find_terms (fun x -> is_const x) tm in
  let names = subtract (setify (map (o fst dest_const) cns)) ["!";"?";"/\\";"\\/";"==>"] in
  let tys = funtys_of_tm tm in
(*  let subs0 = get_subterms tm prfun0 in
  let subss = get_subterms tm prfun in*)
  let subst = get_subterms (retyvar tm) prfunt in
(*  let subsd = get_subterms tm prfunt in
  let subsn = get_subterms tm prfunnt in*)
(*  let r0 = List.rev_append tys (List.rev_append names subs0) in
  let rs = List.rev_append tys (List.rev_append names subss) in*)
  let rt = List.rev_append tys (List.rev_append names subst) in
(*  let rd = List.rev_append tys (List.rev_append names subsd) in
  let rn = List.rev_append tys (List.rev_append names subsn) in
  (r0, rs, rt, rd, rn)*)
  rt
;;

(*let get_symbolst tm = let (_,_,r,_,_) = get_symbols tm in r;;*)

let name2pairs acc (name, th) =
  if is_conj (concl th) then
    let fold_fun (no, acc) th = (no + 1, (name ^ "_conjunct" ^ (string_of_int no), th) :: acc) in
    snd (List.fold_left fold_fun (0, acc) (cONJUNCTS th))
  else (name, th) :: acc
;;

let name2pairsconjs acc (name, th) =
  if is_conj (concl th) then
    let fold_fun (no, acc) th = (no + 1, (name ^ "_conjunct" ^ (string_of_int no), th) :: acc) in
    (name, th) :: snd (List.fold_left fold_fun (0, acc) (cONJUNCTS th))
  else (name, th) :: acc
;;

let conjregex = Str.regexp "_conjunct";;
let best_name l =
  if List.length l = 1 then List.hd l else
  let notnew = List.filter (fun s -> String.length s < 6 or String.sub s 0 6 <> "NEWDEP") l in
  let l = if List.length notnew > 0 then notnew else l in
  let nodash = List.filter (fun s -> s <> "-") l in
  let l = if List.length nodash > 0 then nodash else l in
  let nodot = List.filter (fun s -> not (String.contains s '.')) l in
  let l = if List.length nodot > 0 then nodot else l in
  if List.length l = 1 then List.hd l else
  let nocon = List.filter (fun s -> try ignore (Str.search_forward conjregex s 0);
    false with Not_found -> true) l in
  let l = if List.length nocon > 0 then nocon else l in
  List.hd (List.sort compare l)
;;

let write_theorems () =
  let hash = Hashtbl.create 17000 in
  let all_thms = List.fold_left name2pairsconjs [] !theorems in
  List.iter (fun (a, b) -> Hashtbl.add hash (dest_thm b) a) all_thms;
  let names = Hashtbl.create 17000 in
  Hashtbl.iter (fun k _ ->
    if Hashtbl.mem names k then () else Hashtbl.add names k (best_name (Hashtbl.find_all hash k))) hash;
  let thms = Hashtbl.fold (fun k n l -> (n, k) :: l) names [] in
  let thname = try Sys.getenv "EVAL" ^ "/theorems" with _ -> "HH/theorems" in
  let oc = open_out thname in
  output_value oc (List.map (fun (n,t) -> (n,t)) thms);
  close_out oc
;;

let md5 x = Digest.to_hex (Digest.string (Marshal.to_string x [Marshal.No_sharing]));;
type myterm =
  Myvar of string * hol_type
| Myconst of string * hol_type
| Mycomb of myterm * myterm
| Myabs of myterm * myterm;;
let rec rename_consts f t =
  try let l, r = dest_abs t in mk_abs (l, rename_consts f r) with _ ->
  try let l, r = dest_comb t in mk_comb (rename_consts f l, rename_consts f r) with _ ->
  try let c, ty = dest_const t in Obj.magic (Myconst (f c, ty)) with _ -> t
;;
let hash_const_name =
  let defs = List.rev (List.map (o (fun (a,b) -> (fst (dest_const a), rename_all (retyvar b) prfun)) (o dest_eq concl)) (definitions ())) in
  let recdefs = List.map (fun (a,b) -> (a, (try let (ba,bb) = dest_comb b in let (baa,_) = dest_comb ba in let (baac,_) = dest_const baa in if baac = "@" then ba else b with _ -> b))) defs in
  let hash = Hashtbl.create 300 in
  let renamec n = try Hashtbl.find hash n with Not_found -> n in
  let hash_term t = md5 (rename_consts renamec (rename_all (retyvar t) prfun)) in
  List.iter (fun (n, t) -> Hashtbl.add hash n (hash_term t)) recdefs;
  renamec
;;
let hash_const_name_concat s = s ^ hash_const_name s;;

let hash_th th = md5 (rename_consts hash_const_name (rename_all ((o retyvar (o concl (o gEN_ALL dISCH_ALL))) th) prfunnt));;

(*
let hash_th_b th = md5 (rename_all ((retyvar o concl o GEN_ALL o DISCH_ALL) th) prfunnt);;
let thms = List.fold_left name2pairsconjs [] !theorems;;
let thhs = List.map (fun (_,th) -> dest_thm th, hash_th th) thms;;
let hash = Hashtbl.create 17000;;
List.iter (fun (a, b) -> Hashtbl.add hash (hash_th_b b) a) thms;;
let thms = List.fold_left name2pairsconjs [] !theorems;;
let thhs = List.map (fun (_,th) -> dest_thm th, hash_th th) thms;;
let names = Hashtbl.create 17000;;
Hashtbl.iter (fun k _ ->
  if Hashtbl.mem names k then () else
  Hashtbl.add names k (best_name (Hashtbl.find_all hash k))) hash;;#g*
let naname2 = try Sys.getenv "EVAL" ^ "/hashnamesnoconst" with _ -> "HH/hashnamesnoconst";;
let oc = open_out naname2;;
Hashtbl.iter (fun k v -> Printf.fprintf oc "%s %s\n" k v) names;;
close_out oc;;
*)

let get_hashes () =
  theorems := List.filter (fun (x,_) -> x <> "happ_def" && x <> "happ_conv_th") !theorems;
  let thms = List.fold_left name2pairsconjs [] !theorems in
  let hash = Hashtbl.create 17000 in
  List.iter (fun (a, b) -> Hashtbl.add hash (hash_th b) a) thms;
  let names = Hashtbl.create 17000 in
  Hashtbl.iter (fun k _ ->
    if Hashtbl.mem names k then () else
    Hashtbl.add names k (best_name (Hashtbl.find_all hash k))) hash;
  names;;

(*
let write_hashes () =
  theorems := List.filter (fun (x,_) -> x <> "happ_def" && x <> "happ_conv_th") !theorems;
  let thms = List.fold_left name2pairsconjs [] !theorems in
  let thhs = List.map (fun (_,th) -> dest_thm th, hash_th th) thms in
  let hsname = try Sys.getenv "EVAL" ^ "/hashes" with _ -> "HH/hashes" in
  let oc = open_out hsname in
  output_value oc (setify thhs);
  close_out oc;
  let names = get_hashes () in
  let naname = try Sys.getenv "EVAL" ^ "/hashnames" with _ -> "HH/hashnames" in
  let oc = open_out naname in
  Hashtbl.iter (fun k v -> Printf.fprintf oc "%s %s\n" k v) names;
  close_out oc;
  let coname = try Sys.getenv "EVAL" ^ "/constnames" with _ -> "HH/constnames" in
  let cs = List.rev (List.filter (fun s -> s <> "happ") (List.map (fun x -> fst (dest_const (fst (dest_eq (concl x))))) (definitions ()))) in
  let oc = open_out coname in
  List.iter (fun c -> Printf.fprintf oc "%s %s\n" (hash_const_name c) c) cs;
  close_out oc;
  let hash = Hashtbl.create 10000 in
  List.iter (fun (th, hs) -> Hashtbl.replace hash hs th) thhs;
  let (oc0,ocs,oct,ocd,ocn,ocu) =
    let hhs = (try Sys.getenv "EVAL" with _ -> "HH") ^ "/syms" in
    open_out (hhs ^ "0"),open_out (hhs ^ "s"),open_out (hhs ^ "t"),
    open_out (hhs ^ "d"),open_out (hhs ^ "n"),open_out (hhs ^ "u") in
  let out_oc oc thn l =
    os oc thn; output_char oc ':';
    if l <> [] then (
    output_char oc '\"';
    os oc (String.concat "\", \"" l);
    os oc "\"\n") else output_char oc '\n' in
  let out_tm (thn, (asms, gl)) =
    let tm = itlist (curry mk_imp) asms gl in
    let (s0,ss,st,sd,sn) = get_symbols tm in
    out_oc oc0 thn (setify s0);
    out_oc ocs thn (setify ss);
    out_oc oct thn (setify st);
    out_oc ocd thn (setify sd);
    out_oc ocn thn (setify sn);
    out_oc ocu thn (setify (List.concat [s0; ss; st; sn]));
  in
  Hashtbl.iter (fun hs th -> out_tm (hs, th)) hash;
  close_out oc0; close_out ocs; close_out oct; close_out ocd; close_out ocn; close_out ocu
;;

let write_symbols_fast () =
  let hash = Hashtbl.create 17000 in
  let all_thms = List.fold_left name2pairsconjs [] !theorems in
  List.iter (fun (a, b) -> Hashtbl.add hash (dest_thm b) a) all_thms;
  let names = Hashtbl.create 17000 in
  Hashtbl.iter (fun k _ ->
    if Hashtbl.mem names k then () else Hashtbl.add names k (best_name (Hashtbl.find_all hash k))) hash;
  let oct =
    let hhs = (try Sys.getenv "EVAL" with _ -> "HH") ^ "/syms" in open_out (hhs ^ "t") in
  let out_oc oc thn l =
    os oc thn; output_char oc ':';
    if l <> [] then (
    output_char oc '\"';
    os oc (String.concat "\", \"" l);
    os oc "\"\n") else output_char oc '\n' in
  let out_tm (thn, th) =
    let (asms, gl) = dest_thm th in
    let tm = itlist (curry mk_imp) asms gl in
    let (s0,ss,st,sd,_) = get_symbols tm in
    out_oc oct thn st;
  in
  List.iter out_tm all_thms;
  close_out oct;
  let conjs = List.filter (fun (_, th) -> is_conj (concl th)) all_thms in
  let cname = try Sys.getenv "EVAL" ^ "/conjs" with _ -> "HH/conjs" in
  let oc = open_out cname in
  let iter_fun (n, th) =
    let (asms,gl) = dest_thm th in
    let gls = List.map (fun x -> (asms, x)) (conjuncts gl) in
    let ns = setify (List.map (Hashtbl.find names) gls) in
    os oc n; os oc ":"; os oc (String.concat " " ns); os oc "\n"
  in
  List.iter iter_fun conjs;
  close_out oc
;;

let write_symbols () =
  let hash = Hashtbl.create 17000 in
  let all_thms = List.fold_left name2pairsconjs [] !theorems in
  List.iter (fun (a, b) -> Hashtbl.add hash (dest_thm b) a) all_thms;
  let names = Hashtbl.create 17000 in
  Hashtbl.iter (fun k _ ->
    if Hashtbl.mem names k then () else Hashtbl.add names k (best_name (Hashtbl.find_all hash k))) hash;
  let thms = Hashtbl.fold (fun k n l -> (n, k) :: l) names [] in
  let (oc0,ocs,oct,ocd,ocu) =
    let hhs = (try Sys.getenv "EVAL" with _ -> "HH") ^ "/syms" in
    open_out (hhs ^ "0"),open_out (hhs ^ "s"),open_out (hhs ^ "t"),
    open_out (hhs ^ "d"),open_out (hhs ^ "u") in
  let out_oc oc thn l =
    os oc thn; output_char oc ':';
    if l <> [] then (
    output_char oc '\"';
    os oc (String.concat "\", \"" l);
    os oc "\"\n") else output_char oc '\n' in
  let out_tm (thn, (asms, gl)) =
    let tm = itlist (curry mk_imp) asms gl in
    let (s0,ss,st,sd,_) = get_symbols tm in
    out_oc oc0 thn s0;
    out_oc ocs thn ss;
    out_oc oct thn st;
    out_oc ocd thn sd;
    out_oc ocu thn (setify (List.concat [s0; ss; st]));
  in
  List.iter out_tm thms;
  close_out oc0; close_out ocs; close_out oct; close_out ocd; close_out ocu;
  let thname = try Sys.getenv "EVAL" ^ "/theorems" with _ -> "HH/theorems" in
  let oc = open_out thname in
  output_value oc (List.map (fun (n,t) -> (n,t)) thms);
  close_out oc;
(*  let names2 = Hashtbl.create 17000 in
  Hashtbl.iter (fun k v -> Hashtbl.replace names2 (dest_thm k) v) names;*)
  let conjs = List.filter (fun (_, (_,th)) -> is_conj th) thms in
  let cname = try Sys.getenv "EVAL" ^ "/conjs" with _ -> "HH/conjs" in
  let oc = open_out cname in
  let iter_fun (n, (asms,gl)) =
    let gls = List.map (fun x -> (asms, x)) (conjuncts gl) in
    let ns = setify (List.map (Hashtbl.find names) gls) in
    os oc n; os oc ":"; os oc (String.concat " " ns); os oc "\n"
  in
  List.iter iter_fun conjs;
  close_out oc
;;
*)
