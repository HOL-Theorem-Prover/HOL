(* Tactics to transform a problem to TPTP format. *)

open Lib;;
open Hl_parser;;
open Tactics;;
open Simp;;
open Basics;;
open Drule;;
open Fusion;;
open Bool;;
open Equal;;
(*open Theorems;;*)

(* Given a predicate as an argument of another predicate, the
  conversion pRED_ARG_CONV changes it to an equivalent expression
  that has the predicate only at top level, so it can be encoded
  as tPTP; for example:
    P(!x. Q x)    Is rewritten to   ?v. (v <=> !x. Q x) /\ P v   *)
let pRED_ARG_THM = Sequent ([], parse_term "!f a. f a <=> (?v. (v <=> a) /\\ f v)");;

let must_pred tm =
  is_forall tm or is_exists tm or is_conj tm or is_disj tm or
  is_imp tm or is_eq tm or is_neg tm or is_abs tm;;

let rec pRED_ARG_TM build_tm t =
  if must_pred t then
    let v = (parse_term "dumvar:bool") in
    bETA_RULE (sPEC t (sPEC (mk_abs (v, build_tm v)) pRED_ARG_THM))
  else
    let f, a = dest_comb t in
    if find_terms must_pred a <> [] then
      let build_tm subt = build_tm (mk_comb (f, subt)) in
      pRED_ARG_TM build_tm a
    else
      let build_tm subt = build_tm (mk_comb (subt, a)) in
      pRED_ARG_TM build_tm f
;;

let rec pRED_ARG_CONV tm =
  if is_forall tm or is_exists tm then bINDER_CONV pRED_ARG_CONV tm else
  if is_conj tm or is_disj tm or is_imp tm then bINOP_CONV pRED_ARG_CONV tm else
  if is_neg tm then rAND_CONV pRED_ARG_CONV tm else
  if is_eq tm then
    let l, r = dest_eq tm in
    if must_pred l or must_pred r then bINOP_CONV pRED_ARG_CONV tm
    else
      if find_terms must_pred l <> [] then
        let build_tm subt = mk_eq (subt, r) in
        (tHENC (pRED_ARG_TM build_tm) pRED_ARG_CONV) l
      else if find_terms must_pred r <> [] then
        let build_tm subt = mk_eq (l, subt) in
        (tHENC (pRED_ARG_TM build_tm) pRED_ARG_CONV) r
      else rEFL tm
  else if find_terms must_pred tm = [] then rEFL tm
  else let l, r = dest_comb tm in
  if find_terms must_pred l <> [] then
    let build_tm subt = mk_comb (subt, r) in
    (tHENC (pRED_ARG_TM build_tm) pRED_ARG_CONV) l
  else if find_terms must_pred r <> [] then
    let build_tm subt = mk_comb (l, subt) in
    (tHENC (pRED_ARG_TM build_tm) pRED_ARG_CONV) r
  else rEFL tm;;

(* Depth conversion that runs at most once per depth *)
let rec tOP_SWEEP_QCONV conv tm =
  let cOMB_QCONV conv tm =
    let l,r = dest_comb tm in
    try let th1 = conv l in
    try let th2 = conv r in mK_COMB(th1,th2)
    with Failure _ -> aP_THM th1 r
    with Failure _ -> aP_TERM l (conv r) in
  let sUB_QCONV conv tm =
    if is_abs tm then aBS_CONV conv tm
    else cOMB_QCONV conv tm in
  let tHENQC conv1 conv2 tm =
    try let th1 = conv1 tm in
    try let th2 = conv2(rand(concl th1)) in tRANS th1 th2
    with Failure _ -> th1
    with Failure _ -> conv2 tm in
  tHENQC (tRY_CONV conv) (sUB_QCONV (tOP_SWEEP_QCONV conv)) tm;;

(* Removes simple lambda-equalities before doing proper lambda-lifting *)
let eLIM_LAMBDA_EQ tm =
  let (l, r) = dest_eq tm in
  (if is_abs l or is_abs r then
  (tHENC (oNCE_REWRITE_CONV [fUN_EQ_THM]) (tOP_DEPTH_CONV bETA_CONV))
  else aLL_CONV) tm;;

(* fOL_TAC2 Tries to do more intelligent folification than fOL_TAC:
   - better computation of minimum needed arguments
   - does not use identity of the system to work with theorems that talk about I.
   - handles both the assumptions and the goal
 *)
let replace_smaller_assoc key newmin l =
  if List.mem_assoc key l then
    if newmin < assoc key l then
      (key, newmin) :: (List.remove_assoc key l)
    else l
  else (key, newmin) :: l;;

let rec fold_apps fn bnd tm sofar =
  try let l,r = try dest_forall tm with Failure _ ->
                try dest_exists tm with Failure _ ->
                    dest_abs tm in
      fold_apps fn (l :: bnd) r sofar
  with Failure _ -> try
      let l,r = try dest_conj tm with Failure _ ->
                try dest_disj tm with Failure _ ->
                try dest_eq tm with Failure _ ->
                    dest_imp tm in
      fold_apps fn bnd r (fold_apps fn bnd l sofar)
  with Failure _ -> try
      let tm = dest_neg tm in fold_apps fn bnd tm sofar
  with Failure _ ->
      let hop, args = strip_comb tm in
      let sofar = if is_abs hop then fold_apps fn bnd hop sofar else sofar in
      itlist (fold_apps fn bnd) args (fn bnd hop args sofar);;

let get_minarg tm sofar =
  let get_minarg_fold bnd hop args (cmin, vmin) =
    let len = List.length args in
    if is_var hop then if mem hop bnd then (cmin, vmin)
    else (cmin, replace_smaller_assoc (fst (dest_var hop)) len vmin)
    else (replace_smaller_assoc (fst (dest_const hop)) len cmin, vmin) in
  fold_apps get_minarg_fold [] tm sofar;;

(*let happ_def = new_definition (parse_term "(happ : ((A -> B) -> A -> B)) = I");;*)
let happ_conv_th = Sequent ([],parse_term "!(f:A->B) x. f x = happ f x");;

(* For ATP learning: Thibault and Josef *)
let happ_conv = rEWR_CONV happ_conv_th;;
let rec happ_n_conv n tm =
  if n = 1 then happ_conv tm
  else (tHENC (rATOR_CONV (happ_n_conv (n - 1))) happ_conv) tm;;


let fol_conv_assoc op (cmin,vmin) =
  if is_const op then assoc (fst (dest_const op)) cmin else
  if is_var op then try assoc (fst (dest_var op)) vmin with _ -> 0 else failwith "fol_conv_assoc";;
let rec fOL_CONV ((cmin,vmin) as data) tm =
  try let l,r = try dest_forall tm with _ -> try dest_exists tm with _ -> dest_abs tm in
    bINDER_CONV (fOL_CONV (cmin, List.remove_assoc (fst (dest_var l)) vmin)) tm
  with _ ->
  if is_conj tm or is_disj tm or is_imp tm or is_eq tm then bINOP_CONV (fOL_CONV data) tm else
  if is_neg tm then rAND_CONV (fOL_CONV data) tm else
  let op,args = strip_comb tm in
  let th = rev_itlist (ccc (curry mK_COMB)) (map (fOL_CONV data) args) (rEFL op) in
  let tm' = rand(concl th) in
  let n = List.length args - fol_conv_assoc op data in
  if n = 0 then th
  else tRANS th (happ_n_conv n tm');;

let get_mindata (asms, gl) =
  let (cmin, vmin) = itlist get_minarg (gl :: asms) ([],[]) in
  let correct_min (c, min1) =
    let ty = get_const_type c in
    let min2 = List.length (fst (splitlist dest_fun_ty ty)) in
    (c, min min1 min2)
  in
  let cmin = map correct_min cmin in (cmin, vmin)
;;

let fOL_CONV2 tm =
  let mindata = get_mindata ([], tm) in
  fOL_CONV mindata tm;;

let fOL_TAC2 ((ps,gl) as gs) =
  let mindata = get_mindata (map (o concl snd) ps, gl) in
  (cONV_TAC (fOL_CONV mindata) ++++
  rULE_ASSUM_TAC (cONV_RULE (fOL_CONV mindata))) gs;;

(* Combined fOLification *)
let fOL_IT_TAC = cONV_TAC pRED_ARG_CONV ++++ rULE_ASSUM_TAC(cONV_RULE pRED_ARG_CONV) ++++ fOL_TAC2;;

(* Escape characters not accepted by the TPTP format. *)
let escape_to_hex s =
  let n = ref 0 in
  for i = 0 to String.length s - 1 do
    n := !n + (match String.unsafe_get s i with
     'a'|'b'|'c'|'d'|'e'|'f'|'g'|'h'|'i'|'j'|'k'|'l'|'m'|'n'|'o'|'p'|'q'|'r'|'s'|'t'|'u'|'v'|'w'|'x'|'y'|'z'
    |'A'|'B'|'C'|'D'|'E'|'F'|'G'|'H'|'I'|'J'|'K'|'L'|'M'|'N'|'O'|'P'|'Q'|'R'|'S'|'T'|'U'|'V'|'W'|'X'|'Y'|'Z'
    |'0'|'1'|'2'|'3'|'4'|'5'|'6'|'7'|'8'|'9' -> 1
    |'_' -> 2 | _ -> 3)
  done;
  if !n = String.length s then s else begin
    let s' = String.create !n in
    n := 0;
    for i = 0 to String.length s - 1 do begin
      match String.unsafe_get s i with
      ('a'|'b'|'c'|'d'|'e'|'f'|'g'|'h'|'i'|'j'|'k'|'l'|'m'|'n'|'o'|'p'|'q'|'r'|'s'|'t'|'u'|'v'|'w'|'x'|'y'|'z'
      |'A'|'B'|'C'|'D'|'E'|'F'|'G'|'H'|'I'|'J'|'K'|'L'|'M'|'N'|'O'|'P'|'Q'|'R'|'S'|'T'|'U'|'V'|'W'|'X'|'Y'|'Z'
      |'0'|'1'|'2'|'3'|'4'|'5'|'6'|'7'|'8'|'9' as c) -> String.unsafe_set s' !n c
      | '_' -> String.unsafe_set s' !n '_'; incr n; String.unsafe_set s' !n '_'
      | c -> let c = Char.code c in
             String.unsafe_set s' !n '_'; incr n;
             String.unsafe_set s' !n (Printf.sprintf "%x" (c / 16)).[0]; incr n;
             String.unsafe_set s' !n (Printf.sprintf "%x" (c mod 16)).[0]
    end; incr n; done;
    s'
  end
;;

let add_prime s = "\'" ^ s ^ "\'"  

let is_lowercase c = 
  let i = Char.code c in i >= Char.code 'a' && i <= Char.code 'z' 
let is_uppercase c = 
  let i = Char.code c in i >= Char.code 'A' && i <= Char.code 'Z'
let is_letter c =
  (is_lowercase c) or (is_uppercase c)

(* We don't have complete control over the names of 
   the type variables so we escape them completely 
   (for example the sytem may name them "'a" which clash with our
    escaping method'word')
*)
let escape_var s = 
  let s1 = escape_to_hex s in "V" ^ s1

let escape_const s = let s1 = escape_to_hex s in "c" ^ s1

let escape_thm s = 
  if (s.[0] = '\'') or (is_lowercase s.[0]) then s else add_prime s
 
(* Less explosive version of pOLY_ASSUME_TAC *)
let rec fold_cs fn tm sofar =
  try let l,r = try dest_forall tm with Failure _ ->
                try dest_exists tm with Failure _ ->
                    dest_abs tm in fold_cs fn r sofar
  with Failure _ -> try
      let l,r = try dest_conj tm with Failure _ ->
                try dest_disj tm with Failure _ ->
                    dest_imp tm in
      fold_cs fn r (fold_cs fn l sofar)
  with Failure _ -> try
      let tm = dest_neg tm in fold_cs fn tm sofar
  with Failure _ -> if is_eq tm then (* eq is last *)
      let (c, [l; r]) = strip_comb tm in
      fn (dest_const c) (fold_cs fn r (fold_cs fn l sofar))
  else try
      let l, r = dest_comb tm in
      fold_cs fn r (fold_cs fn l sofar)
  with Failure _ ->
    if is_var tm then sofar else fn (dest_const tm) sofar;;


let insts_as gcs tm =
  let fold_fun (n, ty) insts =
    try
      let tys = List.assoc n gcs in
      let inst_fun gty inst =
        try [type_match ty gty inst] with _ -> [] in
      let gty_fun gty = List.concat (map (inst_fun gty) insts) in
      let ret = List.concat (map gty_fun tys) in
      if ret = [] then insts else ret
    with Not_found -> insts
  in
  fold_cs fold_fun tm [[]]
;;

let rec uniq' eq = fun l ->
  match l with
    x::(y::_ as t) -> let t' = uniq' eq t in
    if eq x y then t' else
    if t'==t then l else x::t'
  | _ -> l;;

let polymorph gcs th =
  let tyins = insts_as gcs (concl th) in
  let setify' le eq s = uniq' eq (sort le s) in
  let ths' =
    setify' (fun th th' -> dest_thm th <= dest_thm th')
            equals_thm (mapfilter (ccc iNST_TYPE th) tyins) in
  if ths' = [] then ([th])
  else ths';;

let gl_constants tms =
  let fold_fun (n, ty) cs =
    try (n, (insert ty (List.assoc n cs))) :: (List.remove_assoc n cs)
    with Not_found -> (n, [ty]) :: cs
  in
  let consts = itlist (fun tm sofar -> fold_cs fold_fun tm sofar) tms [] in
  filter (fun (n, tys) -> List.length (tyvars (get_const_type n)) > 0) (setify consts)
;;

let pOLY_ASSUME_TAC names ths (asl,w as gl) =
  let gcs = gl_constants (w :: map (o concl snd) asl) in
  let ths = map (polymorph gcs) ths in
  let ths2 = List.combine names ths in
  let map_fun (n, ts) =
    if List.length ts = 1 then [(n, List.hd ts)] else
    let fold_fun (cno, clst) t =
      (cno + 1, (n ^ "_monomorphized" ^ string_of_int cno, t) :: clst) in
    snd (List.fold_left fold_fun (0, []) ts)
  in
  let ths3 = List.map map_fun ths2 in
  let ths4 = List.concat ths3 in
(*  let names, ths' = List.split ths4 in*)
  mAP_EVERY (fun (n, th) -> lABEL_TAC (escape_thm n) th) ths4 gl;;

let lABEL_ASSUME_TAC names ths =
  mAP_EVERY (fun (n, th) -> lABEL_TAC (escape_thm n) th) (zip names ths);;

(* lAMBDA_ELIM_CONV2 does less explosive lambda-lifting than lAMBDA_ELIM_CONV
   for universally quantified theorems; all the quantified variables do not
   need to be arguments of function that replaces the lambda expression. *)
let genvarsmall,genvarreset =
  let gcounter = ref 0 in
  ((fun ty -> let count = !gcounter in
             (gcounter := count + 1;
              mk_var("_"^(string_of_int count),ty))),
   fun () -> gcounter := 0);;

let rIGHT_BETAS =
  rev_itlist (fun a -> o (cONV_RULE (rAND_CONV bETA_CONV)) (ccc aP_THM a));;

let lAMBDA_ELIM_CONV =
  let hALF_MK_ABS_CONV =
    let pth = Sequent ([], parse_term "(s = \\x. t x) <=> (!x. s x = t x)") in
    let rec conv vs tm =
      if vs = [] then rEFL tm else
      (tHENC (gEN_REWRITE_CONV iii [pth]) (bINDER_CONV(conv (tl vs)))) tm in
    conv in
  let rec find_lambda tm =
    if is_abs tm then tm
    else if is_var tm or is_const tm then failwith "find_lambda"
    else if is_abs tm then tm else
    if is_forall tm or is_exists tm or is_uexists tm
    then find_lambda (body(rand tm)) else
    let l,r = dest_comb tm in
    try find_lambda l with Failure _ -> find_lambda r in
  let rec eLIM_LAMBDA conv tm =
    try conv tm with Failure _ ->
    if is_abs tm then aBS_CONV (eLIM_LAMBDA conv) tm
    else if is_var tm or is_const tm then rEFL tm else
    if is_forall tm or is_exists tm or is_uexists tm
    then bINDER_CONV (eLIM_LAMBDA conv) tm
    else cOMB_CONV (eLIM_LAMBDA conv) tm in
  let aPPLY_PTH =
    let pth = Sequent ([], parse_term "(!a. (a = c) ==> (P = Q a)) ==> (P <=> !a. (a = c) ==> Q a)") in
    mATCH_MP pth in
  let lAMB1_CONV tm =
    let atm = find_lambda tm in
    let v,bod = dest_abs atm in
    let vs = frees atm in
    let vs' = vs @ [v] in
    let aatm = list_mk_abs(vs,atm) in
    let f = genvarsmall(type_of aatm) in
    let eq = mk_eq(f,aatm) in
    let th1 = sYM(rIGHT_BETAS vs (aSSUME eq)) in
    let th2 = eLIM_LAMBDA(gEN_REWRITE_CONV iii [th1]) tm in
    let th3 = aPPLY_PTH (gEN f (dISCH_ALL th2)) in
    cONV_RULE(rAND_CONV(bINDER_CONV(lAND_CONV (hALF_MK_ABS_CONV vs')))) th3 in
  let rec conv tm =
    try (tHENC lAMB1_CONV conv) tm with Failure _ -> rEFL tm in
  conv;;


let lAMBDA_ELIM_CONV2 =
  let hALF_MK_ABS_CONV =
    let pth = Sequent ([], parse_term "(s = \\x. t x) <=> (!x. s x = t x)") in
    let rec conv vs tm =
      if vs = [] then rEFL tm else
      (tHENC (gEN_REWRITE_CONV iii [pth]) (bINDER_CONV(conv (tl vs)))) tm in
    conv in
  let rec find_lambda tm =
    if is_abs tm then tm
    else if is_var tm or is_const tm then failwith "find_lambda"
    else if is_abs tm then tm else
    if is_forall tm or is_exists tm or is_uexists tm
    then find_lambda (body(rand tm)) else
    let l,r = dest_comb tm in
    try find_lambda l with Failure _ -> find_lambda r in
  let rec eLIM_LAMBDA conv tm =
    try conv tm with Failure _ ->
    if is_abs tm then aBS_CONV (eLIM_LAMBDA conv) tm
    else if is_var tm or is_const tm then rEFL tm else
    if is_forall tm or is_exists tm or is_uexists tm
    then bINDER_CONV (eLIM_LAMBDA conv) tm
    else cOMB_CONV (eLIM_LAMBDA conv) tm in
  let aPPLY_PTH =
    let pth = Sequent ([], parse_term "(!a. (a = c) ==> (P = Q a)) ==> (P <=> !a. (a = c) ==> Q a)") in
    mATCH_MP pth in
  let lAMB2_CONV tm =
    let atm = find_lambda tm in
    let v,bod = dest_abs atm in
    let vs = subtract (frees atm) (frees tm) in
    let vs' = vs @ [v] in
    let aatm = list_mk_abs(vs,atm) in
    let f = genvarsmall(type_of aatm) in
    let eq = mk_eq(f,aatm) in
    let th1 = sYM(rIGHT_BETAS vs (aSSUME eq)) in
    let th2 = eLIM_LAMBDA(gEN_REWRITE_CONV iii [th1]) tm in
    let th3 = aPPLY_PTH (gEN f (dISCH_ALL th2)) in
    cONV_RULE(rAND_CONV(bINDER_CONV(lAND_CONV (hALF_MK_ABS_CONV vs')))) th3 in
  let rec conv tm =
    try (tHENC lAMB2_CONV conv) tm with Failure _ -> rEFL tm in
  conv;;
