(* hh_write module: write a given problem to various TPTP formats:
   fof, tff1, thf0 and full thf *)

open Lib;;
open Fusion;;
open Basics;;
open Bool;;
open Equal;;
open Hl_parser;;
open Tactics;;
open Simp;;
(*open Theorems;;*)
open Hh_symbols;;
open Hh_tac;;

module Sm = Map.Make(struct type t = string let compare = compare end);;
module Tmm = Map.Make(struct type t = term let compare = compare end);;

let variant_name_hash s used =
  try let i = Hashtbl.find used s in
    let rec new_name s i =
      let si = s ^ string_of_int i in
      if Hashtbl.mem used si then new_name s (i + 1)
      else (Hashtbl.replace used si 0; Hashtbl.replace used si (i + 1); si)
    in new_name s i
  with Not_found -> Hashtbl.replace used s 0; s

let variant_name_map s used =
  try let i = Sm.find s used in
    let rec new_name s i =
      let si = s ^ string_of_int i in
      if Sm.mem si used then new_name s (i + 1)
      else (si, Sm.add s (i + 1) (Sm.add si 0 used))
    in new_name s i
  with Not_found -> (s, Sm.add s 0 used)

let print_vartype t =
  let s = String.copy (dest_vartype t) in
    escape_var s

let os = output_string;;
let rec oiter oc fn sep = function
    [] -> ()
  | [e] -> fn oc e
  | h :: t -> fn oc h; os oc sep; oiter oc fn sep t;;

let string_list_of_string str sep =
  let rec slos_aux str ans =
    if str = "" then ans else
    try
      let first_space = String.index str sep in
      if first_space = 0 then
        slos_aux (String.sub str 1 (String.length str - 1)) ans
      else
        slos_aux
          (String.sub str (first_space + 1)(String.length str - 1 - first_space))
          ((String.sub str 0 (first_space)) :: ans)
    with
      Not_found ->
        List.rev (str :: ans)
  in slos_aux str []
;;

let rec chop_listnok acc n = function
    [] -> (List.rev acc, [])
  | h :: t -> if n = 0 then (List.rev acc, h :: t) else chop_listnok (h :: acc) (n - 1) t;;

let rec chop_listn acc n = function
    [] -> failwith "chop_listn"
  | h :: t -> if n = 0 then (List.rev acc, h :: t) else chop_listn (h :: acc) (n - 1) t;;

(* The HO-funtype `:(A -> B) list` will be lost *)
let name_tscs_mono_fold ho (tys, cs, used) tm () =
  let ctys = if not ho then [type_of tm] else striplist dest_fun_ty (type_of tm) in
  let rec name_ty ty =
    if Hashtbl.mem tys ty then () else
    let n =
      if is_type ty then
        let s, stys = dest_type ty in
        List.iter name_ty stys;
        String.concat "" (escape_const s :: (map (fun x -> Hashtbl.find tys x) stys))
      else print_vartype ty in
    let n = variant_name_hash n used in Hashtbl.replace tys ty n
  in
  List.iter name_ty ctys;
  if Hashtbl.mem cs tm or is_var tm then () else
  let n = escape_const (fst (dest_const tm)) in
  let n = variant_name_hash n used in
  Hashtbl.replace cs tm n
;;

let name_tscs_poly_fold (tys, cs, used) tm () =
  let rec name_ty ty =
    if is_type ty then
      let s, stys = dest_type ty in
      (if Hashtbl.mem tys s then () else
      Hashtbl.replace tys s (variant_name_hash (escape_const s) used));
      List.iter name_ty stys;
    else
      let s = dest_vartype ty in
      (if Hashtbl.mem tys s then () else
      Hashtbl.replace tys s (variant_name_hash (print_vartype ty) used));
  in
  name_ty (type_of tm);
  if is_var tm then
    let s = fst (dest_var tm) in
    if Hashtbl.mem cs ("`" ^ s) then () else 
    let n = variant_name_hash (escape_const s) used in
    Hashtbl.replace cs ("`" ^ s) n
  else
  let s, _ = dest_const tm in
  if Hashtbl.mem cs s then () else
  let n = variant_name_hash (escape_const s) used in
  Hashtbl.replace cs s n
;;

let rec fold_cs_vs fn tm sofar =
  try let l,r = try dest_forall tm with Failure _ ->
                try dest_exists tm with Failure _ ->
                    dest_abs tm in
      fold_cs_vs fn r (fold_cs_vs fn l sofar)
  with Failure _ -> try
      let l,r = try dest_conj tm with Failure _ ->
                try dest_disj tm with Failure _ ->
                try dest_eq tm with Failure _ ->
                    dest_imp tm in
      fold_cs_vs fn r (fold_cs_vs fn l sofar)
  with Failure _ -> try
      let tm = dest_neg tm in fold_cs_vs fn tm sofar
  with Failure _ -> try
      let l, r = dest_comb tm in
      fold_cs_vs fn r (fold_cs_vs fn l sofar)
  with Failure _ -> fn tm sofar;;

let name_tscs_mono ho data tm =
  fold_cs_vs (name_tscs_mono_fold ho data) tm ();;
let name_tscs_poly data tm =
  fold_cs_vs (name_tscs_poly_fold data) tm ();;

let is_fun_ty = function Tyapp("fun",[ty1;ty2]) -> true | _ -> false;;

let rec oty_mono ts order oc ty =
  if is_fun_ty ty then
    match order with
      0 -> os oc (Hashtbl.find ts ty)
    | 1 ->
        let t1, t2 = dest_fun_ty ty in
        os oc "("; oty_mono ts 0 oc t1; os oc " > "; oty_mono ts 0 oc t2; os oc ")"
    | _ ->
        let args, res = splitlist dest_fun_ty ty in
        os oc "("; oiter oc (oty_mono ts (order - 1)) " > " args; os oc " > ";
        oty_mono ts (order - 1) oc res; os oc ")"
  else os oc (Hashtbl.find ts ty);;

let rec oty_poly ts order oc ty =
  (* try is needed for constant types in TFF *)
  if is_vartype ty then os oc (try Hashtbl.find ts (dest_vartype ty) with Not_found -> print_vartype ty) else
  let pr_br ty =
    let (s, tys) = dest_type ty in
    if order < 0 then begin
      if tys <> [] then os oc "(";
      os oc (Hashtbl.find ts s);
      List.iter (fun ty -> os oc " @ "; oty_poly ts order oc ty) tys;
      if tys <> [] then os oc ")";
    end else begin
      os oc (Hashtbl.find ts s);
      if tys = [] then () else (os oc "("; oiter oc (oty_poly ts 0) "," tys; os oc ")")
    end in
  if is_fun_ty ty then
    (match order with
      0 -> pr_br ty
    | 1 ->
        let args, res = splitlist dest_fun_ty ty in
        (match args with
          [a] -> oty_poly ts 0 oc a; os oc " > "; oty_poly ts 0 oc res
        | _ -> os oc "("; oiter oc (oty_poly ts 0) " * " args; os oc " > "; oty_poly ts 0 oc res)
    | _ ->
        let args, res = splitlist dest_fun_ty ty in
        os oc "("; oiter oc (oty_poly ts (order - 1)) " > " args; os oc " > ";
        oty_poly ts (order - 1) oc res; os oc ")")
  else pr_br ty;;

let inst_const tm =
  if is_const tm then
    let (n, ty) = dest_const tm in
    let gty = get_const_type n in
    let inst = type_match gty ty [] in
    let rinst = map (fun (a, b) -> (b, a)) inst in
    let tvs = tyvars gty in
    map (fun x -> assoc x rinst) tvs
  else [];;

let rec tff_tm oc (bnd, used) cs ts tm =
  if is_var tm then begin
    os oc (try Tmm.find tm bnd with Not_found -> Hashtbl.find cs ("`" ^ (o fst dest_var) tm))
  end else begin
    let (f, args) = strip_comb tm in
    os oc (Hashtbl.find cs (fst (dest_const f)));
    let insts = inst_const f in
    if args <> [] or insts <> [] then begin
      os oc "(";
      oiter oc (fun oc ty -> oty_poly ts 0 oc ty) "," insts;
      (if args <> [] && insts <> [] then os oc "," else ());
      oiter oc (fun oc e -> tff_tm oc (bnd, used) cs ts e) "," args;
      os oc ")"
    end
  end;;

let bindv v (bnd, used) =
  if Tmm.mem v bnd then (bnd, used) else
  let n = escape_var (fst (dest_var v)) in
  let (n, used) = variant_name_map n used in
  (Tmm.add v n bnd, used)
;;

let pr_bs_poly oc order bnd ts bs =
  (os oc "["; oiter oc (fun oc v -> os oc (Tmm.find v bnd); os oc ":"; oty_poly ts order oc (type_of v)) "," bs;
   os oc "]:");;

let rec tff_pred oc (bnd, used) cs ts tm =
  if is_forall tm then
    let bs, bod = strip_forall tm in
    let (bnd, used) = rev_itlist bindv bs (bnd, used) in
    os oc "!"; pr_bs_poly oc 0 bnd ts bs; tff_pred oc (bnd, used) cs ts bod
  else if is_exists tm then
    let bs, bod = strip_exists tm in
    let (bnd, used) = rev_itlist bindv bs (bnd, used) in
    os oc "?"; pr_bs_poly oc 0 bnd ts bs; tff_pred oc (bnd, used) cs ts bod
  else if is_conj tm then
    (os oc "("; oiter oc (fun oc e -> tff_pred oc (bnd, used) cs ts e) " & " (conjuncts tm); os oc ")")
  else if is_disj tm then
    (os oc "("; oiter oc (fun oc e -> tff_pred oc (bnd, used) cs ts e) " | " (disjuncts tm); os oc ")")
  else if is_imp tm then let l, r = dest_imp tm in
    (os oc "("; tff_pred oc (bnd, used) cs ts l; os oc " => ";
               tff_pred oc (bnd, used) cs ts r; os oc ")")
  else if is_neg tm then
    let t = dest_neg tm in (os oc "~ ("; tff_pred oc (bnd,used) cs ts t; os oc ")")
  else if is_eq tm then let l,r = dest_eq tm in
    if must_pred l or must_pred r then
      (os oc "("; tff_pred oc (bnd, used) cs ts l; os oc " <=> ";
      tff_pred oc (bnd, used) cs ts r; os oc ")")
    else
      (tff_tm oc (bnd, used) cs ts l; os oc " = "; tff_tm oc (bnd, used) cs ts r)
  else
    (os oc "p("; tff_tm oc (bnd, used) cs ts tm; os oc ")");;

let tff_pred oc cs ts used_map t =
  let tvs = type_vars_in_term t in
  let stvs = map dest_vartype tvs in
  let used_map = itlist (fun s m -> Sm.add s 0 m) stvs used_map in
  (if tvs <> [] then (os oc "!["; oiter oc (fun oc e -> oty_poly ts 0 oc e; os oc " : $tType") "," tvs; os oc "]: "));
  tff_pred oc (Tmm.empty, used_map) cs ts t
;;

let pr_bs_mono oc order bnd ts bs =
  (os oc "["; oiter oc (fun oc v -> os oc (Tmm.find v bnd); os oc ":"; oty_mono ts order oc (type_of v)) "," bs;
   os oc "]:");;

let rec thf_tm oc (bnd, used) cs ts tm =
  if is_forall tm then
    let bs, bod = strip_forall tm in
    let (bnd, used) = rev_itlist bindv bs (bnd, used) in
    os oc "!"; pr_bs_mono oc (-1) bnd ts bs; thf_tm oc (bnd, used) cs ts bod
  else if is_exists tm then
    let bs, bod = strip_exists tm in
    let (bnd, used) = rev_itlist bindv bs (bnd, used) in
    os oc "?"; pr_bs_mono oc (-1) bnd ts bs; thf_tm oc (bnd, used) cs ts bod
  else if is_abs tm then
    let bs, bod = strip_abs tm in
    let (bnd, used) = rev_itlist bindv bs (bnd, used) in
    os oc "^"; pr_bs_mono oc (-1) bnd ts bs; thf_tm oc (bnd, used) cs ts bod
  else if is_conj tm then
    (os oc "("; oiter oc (fun oc e -> thf_tm oc (bnd, used) cs ts e) " & " (conjuncts tm); os oc ")")
  else if is_disj tm then
    (os oc "("; oiter oc (fun oc e -> thf_tm oc (bnd, used) cs ts e) " | " (disjuncts tm); os oc ")")
  else if is_imp tm then let l, r = dest_imp tm in
    (os oc "("; thf_tm oc (bnd, used) cs ts l; os oc " => ";
               thf_tm oc (bnd, used) cs ts r; os oc ")")
  else if is_neg tm then
    let t = dest_neg tm in (os oc "~ ("; thf_tm oc (bnd,used) cs ts t; os oc ")")
  else if is_eq tm then let l,r = dest_eq tm in
    (os oc "("; thf_tm oc (bnd, used) cs ts l;
    os oc (if type_of l = bool_ty then " <=> " else " = ");
    thf_tm oc (bnd, used) cs ts r; os oc ")")
  else if is_comb tm then let hop, args = strip_comb tm in
    (os oc "("; oiter oc (fun oc e -> thf_tm oc (bnd, used) cs ts e) " @ " (hop :: args); os oc ")")
  else if is_const tm then os oc (Hashtbl.find cs tm)
  else os oc (try Tmm.find tm bnd with Not_found -> failwith "thf_tm");;

let output_gs oc (asms, gl) =
  let iter (s, thm) = os oc "% Assm ["; os oc s; os oc "]: "; os oc (lstring_of_term (concl thm)); os oc "\n" in
  List.iter iter asms;
  os oc "% Goal: "; os oc (lstring_of_term gl); os oc "\n";;

let oi oc i = os oc (string_of_int i);;

let thf_gl oc ls asms gl n =
  let ts, cs, used = Hashtbl.create 20, Hashtbl.create 50, Hashtbl.create 50 in
  Hashtbl.add used "lambda" 0; (* LeoII throws syntax errors with 'lambda' *)
  List.iter (name_tscs_mono true (ts, cs, used)) (gl :: asms);
  let ohdr s1 s2 = os oc "thf("; os oc s1; os oc ", "; os oc s2; os oc ", " in
  let otl () = os oc ").\n" in
  os oc "%  TYPES\n";
  Hashtbl.remove ts (parse_type "bool");
  Hashtbl.iter (fun _ ty -> ohdr ty "type"; os oc ty; os oc " : $tType"; otl ()) ts;
  Hashtbl.add ts (parse_type "bool") "$o";
  os oc "%  CONSTS\n";
  Hashtbl.remove cs (parse_term "T"); Hashtbl.remove cs (parse_term "F");
  Hashtbl.iter (fun t s -> ohdr s "type"; os oc s; os oc " : "; oty_mono ts (-1) oc (type_of t); otl ()) cs;
  Hashtbl.add cs (parse_term "T") "$true"; Hashtbl.add cs (parse_term "F") "$false";
  os oc "%  AXIOMS\n";
  List.iter2 (fun n t -> ohdr n "axiom"; thf_tm oc (Tmm.empty, Sm.empty) cs ts t; otl ()) ls asms;
  ohdr n "conjecture"; thf_tm oc (Tmm.empty, Sm.empty) cs ts gl; otl ()
;;

let rec thff_tm oc (bnd, used) cs ts tm =
  if is_forall tm then
    let bs, bod = strip_forall tm in
    let (bnd, used) = rev_itlist bindv bs (bnd, used) in
    os oc "!"; pr_bs_poly oc (-1) bnd ts bs; thff_tm oc (bnd, used) cs ts bod
  else if is_exists tm then
    let bs, bod = strip_exists tm in
    let (bnd, used) = rev_itlist bindv bs (bnd, used) in
    os oc "?"; pr_bs_poly oc (-1) bnd ts bs; thff_tm oc (bnd, used) cs ts bod
  else if is_abs tm then
    let bs, bod = strip_abs tm in
    let (bnd, used) = rev_itlist bindv bs (bnd, used) in
    os oc "^"; pr_bs_poly oc (-1) bnd ts bs; thff_tm oc (bnd, used) cs ts bod
  else if is_conj tm then
    (os oc "("; oiter oc (fun oc e -> thff_tm oc (bnd, used) cs ts e) " & " (conjuncts tm); os oc ")")
  else if is_disj tm then
    (os oc "("; oiter oc (fun oc e -> thff_tm oc (bnd, used) cs ts e) " | " (disjuncts tm); os oc ")")
  else if is_imp tm then let l, r = dest_imp tm in
    (os oc "("; thff_tm oc (bnd, used) cs ts l; os oc " => ";
                thff_tm oc (bnd, used) cs ts r; os oc ")")
  else if is_neg tm then
    let t = dest_neg tm in (os oc "~ ("; thff_tm oc (bnd,used) cs ts t; os oc ")")
  else if is_eq tm then let l,r = dest_eq tm in
    (os oc "("; thff_tm oc (bnd, used) cs ts l;
    os oc (if type_of l = bool_ty then " <=> " else " = ");
    thff_tm oc (bnd, used) cs ts r; os oc ")")
  else if is_comb tm then let hop, args = strip_comb tm in
    (os oc "("; oiter oc (fun oc e -> thff_tm oc (bnd, used) cs ts e) " @ " (hop :: args); os oc ")")
  else if is_const tm then begin
    let insts = inst_const tm in
    if insts <> [] then os oc "(";
    os oc (Hashtbl.find cs (fst (dest_const tm)));
    if insts <> [] then (List.iter (fun ty -> os oc " @ "; oty_poly ts (-1) oc ty) insts; os oc ")");
  end
  else os oc (try Tmm.find tm bnd with Not_found -> failwith "thff_tm");;


let thff_pred oc used_map cs ts tm =
  let tvs = type_vars_in_term tm in
  (if tvs <> [] then (os oc "!["; oiter oc (fun oc e -> oty_poly ts (-1) oc e; os oc ":$tType") "," tvs; os oc "]: "));
  thff_tm oc (Tmm.empty, used_map) cs ts tm
;;

let used_to_map h = Hashtbl.fold Sm.add h Sm.empty;;

let otyquant oc ts tys =
  if tys <> [] then begin
    os oc "!>["; oiter oc (fun oc t -> os oc (print_vartype t); os oc ":$tType")
      "," tys; os oc "]: " end;;

let thff_gl oc ls asms gl =
  let ts, cs, used = Hashtbl.create 20, Hashtbl.create 50, Hashtbl.create 50 in
  List.iter (name_tscs_poly (ts, cs, used)) (gl :: asms);
  let ohdr s1 s2 = os oc "thf("; os oc s1; os oc ", "; os oc s2; os oc ", " in
  let otl () = os oc ").\n" in
  os oc "%  TYPES\n";
  Hashtbl.remove ts "bool";
  Hashtbl.remove ts "fun";
  Hashtbl.iter (fun t s ->
    try
      let ar = get_type_arity t in
      ohdr t "type"; os oc s; os oc ":";
      let rec prty n = if n = 0 then os oc "$tType" else (os oc "$tType > "; prty (n - 1)) in
      prty ar; otl ()
    with Failure _ -> ()) ts; (* Failure in get_type_arity for ` *)
  Hashtbl.add ts "bool" "$o";
  os oc "%  CONSTS\n";
  Hashtbl.remove cs "T"; Hashtbl.remove cs "F";
  (* only print constants and not types *)
  Hashtbl.iter (fun t s -> if t.[0] <> '`' then (ohdr s "type"; os oc s; os oc " : ";
    let ty = get_const_type t in
    let tvs = tyvars ty in
    otyquant oc ts tvs;
    oty_poly ts (-1) oc ty; otl ())) cs;
  Hashtbl.add cs "T" "$true"; Hashtbl.add cs "F" "$false";
  os oc "%  AXIOMS\n";
  let used_map = used_to_map used in
  List.iter2 (fun n t -> ohdr n "axiom"; thff_pred oc used_map cs ts t; otl ()) ls asms;
  (* Something is wrong here (I may have erased something) *)
  ohdr ("c") "conjecture"; thff_pred oc used_map cs ts gl; otl ()
;;


let rec oty_isa ts oc ty =
  if is_vartype ty then (os oc "'"; os oc (try Hashtbl.find ts (dest_vartype ty)
    with Not_found -> print_vartype ty)) else
  let (s, tys) = dest_type ty in
  (if tys = [] then () else (os oc "("; oiter oc (oty_isa ts) "," tys; os oc ")"));
  os oc (Hashtbl.find ts s);;

let pr_bs_isa oc bnd ts bs =
  os oc "(";
  oiter oc (fun oc v -> os oc (Tmm.find v bnd); os oc "::"; oty_isa ts oc (type_of v)) ") (" bs;
  os oc ").";;

let rec otm_isa oc (bnd, used) cs ts tm =
  if is_forall tm then
    let bs, bod = strip_forall tm in
    let (bnd, used) = rev_itlist bindv bs (bnd, used) in
    os oc "(ALL"; pr_bs_isa oc bnd ts bs; otm_isa oc (bnd, used) cs ts bod; os oc ")"
  else if is_exists tm then
    let bs, bod = strip_exists tm in
    let (bnd, used) = rev_itlist bindv bs (bnd, used) in
    os oc "(EX"; pr_bs_isa oc bnd ts bs; otm_isa oc (bnd, used) cs ts bod; os oc ")"
  else if is_abs tm then
    let bs, bod = strip_abs tm in
    let (bnd, used) = rev_itlist bindv bs (bnd, used) in
    os oc "(%"; pr_bs_isa oc bnd ts bs; otm_isa oc (bnd, used) cs ts bod; os oc ")"
  else if is_conj tm then
    (os oc "("; oiter oc (fun oc e -> otm_isa oc (bnd, used) cs ts e) " & " (conjuncts tm); os oc ")")
  else if is_disj tm then
    (os oc "("; oiter oc (fun oc e -> otm_isa oc (bnd, used) cs ts e) " | " (disjuncts tm); os oc ")")
  else if is_imp tm then let l, r = dest_imp tm in
    (os oc "("; otm_isa oc (bnd, used) cs ts l; os oc " --> ";
               otm_isa oc (bnd, used) cs ts r; os oc ")")
  else if is_neg tm then
    let t = dest_neg tm in (os oc "(~"; otm_isa oc (bnd,used) cs ts t; os oc ")")
  else if is_eq tm then let l,r = dest_eq tm in
    (os oc "("; otm_isa oc (bnd, used) cs ts l; os oc " = ";
    otm_isa oc (bnd, used) cs ts r; os oc ")")
  else if is_comb tm then let hop, args = strip_comb tm in
    (os oc "("; oiter oc (fun oc e -> otm_isa oc (bnd, used) cs ts e) " " (hop :: args); os oc ")")
  else if is_const tm then os oc (Hashtbl.find cs (fst (dest_const tm)))
  else os oc (try Tmm.find tm bnd with Not_found -> failwith ("tm_isa:" ^ (fst (dest_var tm))));;

let hash_to_list h = Hashtbl.fold (fun a b l -> (a,b) :: l) h [];;

let isa_fix_names h u =
  let l = Hashtbl.fold (fun a b c -> (a, b) :: c) h [] in
  let itr (k, v) =
    if v.[String.length v - 1] = '_' then
      let n = variant_name_hash v u in
      Hashtbl.replace h k n
  in List.iter itr l
;;

let isa_gl oc names asms gl =
  os oc "theory Bla imports \"~~/src/HOL/TPTP/ATP_Problem_Import\" begin\n";
  let ts, cs, used = Hashtbl.create 20, Hashtbl.create 50, Hashtbl.create 50 in
  Hashtbl.add used "bool" 0; Hashtbl.add used "fun" 0;
  Hashtbl.add used "True" 0; Hashtbl.add used "False" 0;
  Hashtbl.add used "in" 0;
  List.iter (name_tscs_poly (ts, cs, used)) (gl :: asms);
  isa_fix_names ts used; isa_fix_names cs used;
  Hashtbl.remove ts "bool"; Hashtbl.remove ts "fun";
  Hashtbl.remove cs "T"; Hashtbl.remove cs "F";
  Hashtbl.iter (fun hty sty ->
    try
      let a = get_type_arity hty in
      os oc "typedecl ";
      (if a > 0 then (os oc "("; os oc
                        (String.concat "," (Array.to_list (Array.init a (fun i -> "'" ^ (String.make 1 (Char.chr (65 + i))))))); os oc ") ") else ());
      os oc sty; os oc "\n"
    with Failure "find" -> ()
  ) ts;
  Hashtbl.replace ts "bool" "bool"; Hashtbl.replace ts "fun" "fun";
  os oc "axiomatization\n";
  oiter oc (fun oc (t, s) -> os oc s; os oc " :: \""; oty_isa ts oc (get_const_type t); os oc "\"\n") "and " (hash_to_list cs);
  Hashtbl.replace cs "T" "True"; Hashtbl.replace cs "F" "False";
  os oc "axiomatization where\n";
  oiter oc (fun oc (n, t) -> os oc n; os oc ": \""; otm_isa oc (Tmm.empty, Sm.empty) cs ts t; os oc "\"\n") "and " (zip (rev names) asms);
  os oc "lemma conjecture:\n  \"";
  otm_isa oc (Tmm.empty, Sm.empty) cs ts gl; os oc "\"\n"
;;


let fileno = ref 0;;

let rec fullsplitlist dest x =
  try let l,r = dest x in
      let ls = fullsplitlist dest r in (l::ls)
  with Failure _ -> ([x]);;

let rec otff_funtype oc ts t min =
  if min = 0 then oty_poly ts 0 oc t else
  let tys = fullsplitlist dest_fun_ty t in
  let (tys1, tys2) = chop_listn [] min tys in
  let ty2 = end_itlist mk_fun_ty tys2 in
  os oc "("; (if List.length tys1 > 1 then os oc "(" else ());
  oiter oc (fun oc e -> oty_poly ts 0 oc e) " * " tys1;
  (if List.length tys1 > 1 then os oc ")" else ());
  os oc " > "; oty_poly ts 0 oc ty2; os oc ")"
;;

let funtys_of_tm tm =
  let mergel l = setify (List.concat l) in
  let tys tm = map type_of (find_terms (fun x -> is_var x or is_const x) tm) in
  let rec funtypes t =
    if is_vartype t then [] else
    let (s, l) = dest_type t in
    mergel ([s]::(map funtypes l)) in
  mergel (map funtypes (tys tm))
;;

let funtys_of_tms tms = setify (List.concat (map funtys_of_tm tms));;

let tff_gl_mk_hash terms =
  let ts, cs, used = Hashtbl.create 20, Hashtbl.create 50, Hashtbl.create 50 in
  Hashtbl.add used "p" 0; Hashtbl.add cs "happ" "i"; Hashtbl.add used "i" 0;
  Hashtbl.add ts "fun" "fn"; Hashtbl.add used "fn" 0; Hashtbl.add used "fun" 0;
  List.iter (name_tscs_poly (ts, cs, used)) terms;
  (ts,cs,used_to_map used)
;;

let tff_gl_hash oc names name asms gl (ts,cs,used) =
  let ohdr s1 s2 = os oc "tff("; os oc s1; os oc ", "; os oc s2; os oc ", " in
  let otl () = os oc ").\n" in
  os oc "%   TYPES\n";
  List.iter (fun t ->
    let s = Hashtbl.find ts t in
    ohdr t "type"; os oc s; os oc ":";
    begin match get_type_arity t with
      0 -> os oc "$tType"
    | 1 -> os oc "$tType > $tType"
    | n -> os oc "("; oiter oc (fun oc _ -> os oc "$tType") " * " (Array.to_list (Array.make n ()));
        os oc ") > $tType" end; otl ()) (funtys_of_tms (gl::asms));
  os oc "%   CONSTS\n";
  ohdr "cp" "type"; os oc "p : (bool > $o)"; otl ();
  let output_const (c, argno) =
    let ty = get_const_type c in let tvs = tyvars ty in
    ohdr c "type"; os oc (Hashtbl.find cs c); os oc ":";
    otyquant oc ts tvs; otff_funtype oc ts ty argno; otl ()
  in
  List.iter output_const (fst (get_mindata (asms, gl)));
  os oc "%   AXIOMS\n";
  List.iter2 (fun n t -> ohdr n "axiom"; tff_pred oc cs ts used t; otl ()) names asms;
  ohdr (escape_thm name) "conjecture"; tff_pred oc cs ts used gl; otl ();
;;

let tff_gl oc names name asms gl =
  let tcu = tff_gl_mk_hash (gl :: asms) in
  tff_gl_hash oc names name asms gl tcu
;;

let oorig oc n ls ts gl g2 =
  output_string oc ("%   ORIGINAL: " ^ n ^ "\n");
  List.iter2 (fun n t ->
    output_string oc ("% Assm: " ^ n ^ ": " ^ lstring_of_term (concl t) ^ "\n")) ls ts;
  output_string oc ("% Goal: " ^ lstring_of_term gl ^ "\n");
  output_string oc "%   PROCESSED\n";
  output_gs oc g2
;;

let rec fof_tm oc (bnd, used) cs ts tm =
  if is_var tm then begin
    os oc "s("; oty_poly ts 0 oc (type_of tm); os oc ","; os oc (
      try Tmm.find tm bnd with Not_found -> Hashtbl.find cs ("`" ^ (o fst dest_var) tm));
    os oc ")"
  end else begin
    let (f, args) = strip_comb tm in
    os oc "s("; oty_poly ts 0 oc (type_of tm); os oc ","; os oc (
      try Hashtbl.find cs (fst (dest_const f)) with _ -> Hashtbl.find cs ("`" ^ (o fst dest_var) f));
    (if args <> [] then
      (os oc "("; oiter oc (fun oc e -> fof_tm oc (bnd, used) cs ts e) "," args; os oc ")"));
    os oc ")"
  end;;

(* Type unsafe version, currently not used *)
let rec fof_tm_unsafe oc (bnd, used) cs ts tm =
  if is_var tm then os oc (Tmm.find tm bnd)
  else
    let (f, args) = strip_comb tm in
    os oc (Hashtbl.find cs (fst (dest_const f)));
    (if args <> [] then
      (os oc "("; oiter oc (fun oc e -> fof_tm_unsafe oc (bnd, used) cs ts e) "," args; os oc ")"));;

let rec fof_pred oc (bnd, used) cs ts tm =
  if is_forall tm then
    let vs, bod = strip_forall tm in
    let (bnd, used) = rev_itlist bindv vs (bnd, used) in
    os oc "![";oiter oc (fun oc v -> os oc (Tmm.find v bnd)) ", " vs;os oc "]: ";fof_pred oc (bnd, used) cs ts bod
  else if is_exists tm then
    let vs, bod = strip_exists tm in
    let (bnd, used) = rev_itlist bindv vs (bnd, used) in
    os oc "?[";oiter oc (fun oc v -> os oc (Tmm.find v bnd)) ", " vs;os oc "]: ";fof_pred oc (bnd, used) cs ts bod
  else if is_conj tm then let l, r = dest_conj tm in
    (os oc "("; fof_pred oc (bnd, used) cs ts l; os oc " & "; fof_pred oc (bnd, used) cs ts r; os oc ")")
  else if is_disj tm then let l, r = dest_disj tm in
    (os oc "("; fof_pred oc (bnd, used) cs ts l; os oc " | "; fof_pred oc (bnd, used) cs ts r; os oc ")")
  else if is_imp tm then let l, r = dest_imp tm in
    (os oc "("; fof_pred oc (bnd, used) cs ts l; os oc " => "; fof_pred oc (bnd, used) cs ts r; os oc ")")
  else if is_neg tm then
    let t = dest_neg tm in (os oc "~ ("; fof_pred oc (bnd,used) cs ts t; os oc ")")
  else if is_eq tm then let l,r = dest_eq tm in
    if must_pred l or must_pred r then
      (os oc "("; fof_pred oc (bnd, used) cs ts l; os oc " <=> ";
      fof_pred oc (bnd, used) cs ts r; os oc ")")
    else
      (fof_tm oc (bnd, used) cs ts l; os oc " = "; fof_tm oc (bnd, used) cs ts r)
  else
    (os oc "p("; fof_tm oc (bnd, used) cs ts tm; os oc ")");;

let fof_pred oc cs ts used_map t =
  let tvs = type_vars_in_term t in
  (if tvs <> [] then (os oc "!["; oiter oc (fun oc e -> oty_poly ts 0 oc e) "," tvs; os oc "]: "));
  fof_pred oc (Tmm.empty, used_map) cs ts t
;;

let fof_gl_hash oc names name asms gl (ts,cs,used) =
  let ohdr s1 s2 = os oc "fof("; os oc s1; os oc ", "; os oc s2; os oc ", " in
  let otl () = os oc ").\n" in
  List.iter2 (fun n t -> ohdr n "axiom"; fof_pred oc cs ts used t; otl ()) names asms;
  ohdr (escape_thm name) "conjecture"; fof_pred oc cs ts used gl; otl ();
;;

let fof_gl_mk_hash terms =
  let ts, cs, used = Hashtbl.create 20, Hashtbl.create 50, Hashtbl.create 50 in
  Hashtbl.add used "p" 0; Hashtbl.add used "s" 0;
  Hashtbl.add cs "happ" "i"; Hashtbl.add used "i" 0;
  List.iter (name_tscs_poly (ts, cs, used)) terms;
  (ts,cs,used_to_map used)
;;

let fof_gl oc names name asms gl =
  let (ts,cs,used) = fof_gl_mk_hash (gl :: asms) in
  fof_gl_hash oc names name asms gl (ts,cs,used);
  (ts,cs)
;;

let pRE_HH_TAC =
  eVERY_ASSUM (fun th -> if frees(concl th) = []
    then aLL_TAC else uNDISCH_TAC (concl th)) ++++
  www (fun (asl,w) -> mAP_EVERY (fun v -> sPEC_TAC(v,v)) (frees w))
;;

let pREP_HH_TAC names need_mono ths =
  pURE_REWRITE_TAC [eXISTS_UNIQUE_THM; eXISTS_UNIQUE_DEF] ++++
  ((if need_mono then pOLY_ASSUME_TAC else lABEL_ASSUME_TAC) (rev names) (rev ths)) ++++
  rULE_ASSUM_TAC (pURE_REWRITE_RULE [eXISTS_UNIQUE_THM; eXISTS_UNIQUE_DEF])
;;

let pREP_TFF_TAC =
  let tOP_DEPTH_CONV c tm = genvarreset (); tOP_DEPTH_CONV c tm in
(*  sELECT_ELIM_TAC ++++*)
  cONV_TAC(tOP_SWEEP_QCONV eLIM_LAMBDA_EQ) ++++
  rULE_ASSUM_TAC (cONV_RULE (tOP_SWEEP_QCONV eLIM_LAMBDA_EQ)) ++++
  cONV_TAC(tHENC (tOP_DEPTH_CONV bETA_CONV) (tHENC lAMBDA_ELIM_CONV2 lAMBDA_ELIM_CONV)) ++++
  rULE_ASSUM_TAC((cONV_RULE(tHENC (tOP_DEPTH_CONV bETA_CONV) (tHENC lAMBDA_ELIM_CONV2 lAMBDA_ELIM_CONV))))
;;

let write_atp_proof filen (ts, names) n gl =
  let (_, [g], _) = mk_goalstate ([],gl) in
  begin match (pREP_HH_TAC names false ts ++++ pREP_TFF_TAC ++++ fOL_IT_TAC) g with
    (_, [g2], _) ->
      let oc = open_out filen in
      oorig oc n names ts gl g2;
      let names = map fst (fst g2) in
      ignore (fof_gl oc names n (map (o concl snd) (fst g2)) (snd g2));
      (*tff_gl oc names (map (o concl snd) (fst g2)) (snd g2);*)
      close_out oc;
    | _ -> failwith ("PREP_HH_TAC created more goals: " ^ n)
  end;;

let write_thf_proof filen (ts, names) n gl =
  let (_, [g], _) = mk_goalstate ([],gl) in
  begin match (pREP_HH_TAC names true ts) g with
    (_, [g2], _) ->
      let oc = open_out filen in
      oorig oc n names ts gl g2;
      ignore (thf_gl oc (map fst (fst g2)) (map (o concl snd) (fst g2)) (snd g2) n);
      close_out oc
    | _ -> failwith "PREP_HH_TAC created more goals"
  end;;

let write_isa_proof filen (ts, names) n gl =
  let (_, [g], _) = mk_goalstate ([],gl) in
  begin match (www(fun (asl,w) -> mAP_EVERY (fun v -> sPEC_TAC(v,v)) (frees w)) ++++
    lABEL_ASSUME_TAC names (map (o gEN_ALL dISCH_ALL) ts)) g with
    (_, [g2], _) ->
      let oc = open_out filen in
      isa_gl oc names (map (o concl snd) (fst g2)) (snd g2);
      close_out oc
  | _ -> failwith "PREP_HH_TAC created more goals"
  end
;;

let rec cut_list md n = function
    [] -> []
  | h :: t -> if n mod md = 0 then h :: (cut_list md (n + 1) t) else cut_list md (n + 1) t;;

let normalize_th th = gEN_ALL (dISCH_ALL th);;
