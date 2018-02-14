open HolKernel boolSyntax

val PRED_ARG_THM = Q.prove(`!f a. f a <=> (?v. (v <=> a) /\ f v)`,
  rpt strip_tac \\ EQ_TAC \\ rpt strip_tac \\ rpt BasicProvers.VAR_EQ_TAC
  \\ TRY (qexists_tac`a`) \\ ASM_REWRITE_TAC[]);
val happ_conv_th = mk_thm([],``!(f:'a->'b) x. f x = happ f x``);

fun must_pred tm =
  is_forall tm orelse is_exists tm orelse is_conj tm orelse is_disj tm orelse
  is_imp tm orelse is_eq tm orelse is_neg tm orelse is_abs tm;

fun PRED_ARG_TM build_tm t =
  if must_pred t then
    let val v = (mk_var("dumvar",bool)) in
    BETA_RULE (SPEC t (SPEC (mk_abs (v, build_tm v)) PRED_ARG_THM))
    end
  else
    let val (f, a) = dest_comb t in
    if find_terms must_pred a <> [] then
      let fun build_tm subt = build_tm (mk_comb (f, subt)) in
      PRED_ARG_TM build_tm a end
    else
      let fun build_tm subt = build_tm (mk_comb (subt, a)) in
      PRED_ARG_TM build_tm f end
    end

fun PRED_ARG_CONV tm =
  if is_forall tm orelse is_exists tm then BINDER_CONV PRED_ARG_CONV tm else
  if is_conj tm orelse is_disj tm orelse is_imp tm then BINOP_CONV PRED_ARG_CONV tm else
  if is_neg tm then RAND_CONV PRED_ARG_CONV tm else
  if is_eq tm then
    let val (l, r) = dest_eq tm in
    if must_pred l orelse must_pred r then BINOP_CONV PRED_ARG_CONV tm
    else
      if find_terms must_pred l <> [] then
        let fun build_tm subt = mk_eq (subt, r) in
        (PRED_ARG_TM build_tm THENC PRED_ARG_CONV) l end
      else if find_terms must_pred r <> [] then
        let fun build_tm subt = mk_eq (l, subt) in
        (PRED_ARG_TM build_tm THENC PRED_ARG_CONV) r end
      else REFL tm end
  else if find_terms must_pred tm = [] then REFL tm
  else let val (l, r) = dest_comb tm in
  if find_terms must_pred l <> [] then
    let fun build_tm subt = mk_comb (subt, r) in
    (PRED_ARG_TM build_tm THENC PRED_ARG_CONV) l end
  else if find_terms must_pred r <> [] then
    let fun build_tm subt = mk_comb (l, subt) in
    (PRED_ARG_TM build_tm THENC PRED_ARG_CONV) r end
  else REFL tm end;

(* Removes simple lambda-equalities before doing proper lambda-lifting *)
fun ELIM_LAMBDA_EQ tm =
  let val (l, r) = dest_eq tm in
  (if is_abs l orelse is_abs r then
  (ONCE_REWRITE_CONV [FUN_EQ_THM] THENC (TOP_DEPTH_CONV BETA_CONV))
  else ALL_CONV) tm end;

(* FOL_TAC2 Tries to do more intelligent folification than FOL_TAC:
   - better computation of minimum needed arguments
   - does not use identity of the system to work with theorems that talk about I.
   - handles both the assumptions and the goal
 *)
fun replace_smaller_assoc key newmin l =
  if List.exists (equal key o #1) l then
    if newmin < assoc key l then
      (key, newmin) :: (List.filter (not o equal key o #1) l)
    else l
  else (key, newmin) :: l;

fun fold_apps f bnd tm sofar =
  let val (l,r) = dest_forall tm handle HOL_ERR _ =>
                  dest_exists tm handle HOL_ERR _ =>
                  dest_abs tm in fold_apps f (l :: bnd) r sofar end
  handle HOL_ERR _ =>
  let val (l,r) = dest_conj tm handle HOL_ERR _ =>
                  dest_disj tm handle HOL_ERR _ =>
                  dest_eq tm handle HOL_ERR _ =>
                  dest_imp tm in fold_apps f bnd r (fold_apps f bnd l sofar) end
  handle HOL_ERR _ =>
      let val tm = dest_neg tm in fold_apps f bnd tm sofar end
  handle HOL_ERR _ =>
      let val (hop, args) = strip_comb tm
          val sofar = if is_abs hop then fold_apps f bnd hop sofar else sofar in
      itlist (fold_apps f bnd) args (f bnd hop args sofar)
      end;

fun const_name tm =
  let val {Name,Thy,...} = dest_thy_const tm in (Thy,Name) end

fun get_minarg tm sofar =
  let fun get_minarg_fold bnd hop args (cmin, vmin) =
    let val len = List.length args in
    if is_var hop then if mem hop bnd then (cmin, vmin)
    else (cmin, replace_smaller_assoc (fst (dest_var hop)) len vmin)
    else (replace_smaller_assoc (const_name hop) len cmin, vmin) end
  in fold_apps get_minarg_fold [] tm sofar end

val happ_conv = REWR_CONV happ_conv_th;

fun happ_n_conv n tm =
  if n = 1 then happ_conv tm
  else (RATOR_CONV (happ_n_conv (n-1)) THENC happ_conv) tm;

fun fol_conv_assoc oper (cmin,vmin) =
  if is_const oper then assoc (const_name oper) cmin else
  if is_var oper then assoc (fst (dest_var oper)) vmin handle HOL_ERR _ => 0
  else failwith "fol_conv_assoc";

fun FOL_CONV (data as (cmin,vmin)) tm =
  let val (l,r) = dest_forall tm handle HOL_ERR _ => dest_exists tm handle HOL_ERR _ => dest_abs tm in
    BINDER_CONV (FOL_CONV (cmin, List.filter (not o equal (fst (dest_var l)) o fst) vmin)) tm end
  handle HOL_ERR _ =>
  if is_conj tm orelse is_disj tm orelse is_imp tm orelse is_eq tm then BINOP_CONV (FOL_CONV data) tm else
  if is_neg tm then RAND_CONV (FOL_CONV data) tm else
  let
    val (oper,args) = strip_comb tm
    val th = rev_itlist (Lib.C (curry MK_COMB)) (map (FOL_CONV data) args) (REFL oper)
    val tm' = rand(concl th)
    val n = List.length args - fol_conv_assoc oper data
  in
    if n = 0 then th
    else TRANS th (happ_n_conv n tm')
  end;

fun get_mindata (asms, gl) =
  let
    val (cmin, vmin) = itlist get_minarg (gl :: asms) ([],[])
    fun correct_min (c, min1) =
      let
        val ty = type_of (prim_mk_const {Thy= #1 c, Name= #2 c})
        val min2 = List.length (fst (strip_fun ty))
      in (c, Int.min (min1,min2)) end
    val cmin = map correct_min cmin
  in (cmin, vmin) end;

fun FOL_CONV2 tm =
  let val mindata = get_mindata ([], tm) in
  FOL_CONV mindata tm end;

fun FOL_TAC2 (gs as (ps,gl)) =
  let val mindata = get_mindata (ps, gl) in
  (CONV_TAC (FOL_CONV mindata) THEN
   RULE_ASSUM_TAC (CONV_RULE (FOL_CONV mindata))) gs end

val FOL_IT_TAC = CONV_TAC PRED_ARG_CONV THEN RULE_ASSUM_TAC(CONV_RULE PRED_ARG_CONV) THEN FOL_TAC2;


fun escape_to_hex s =
  let
    fun pad2 s = if String.size s < 2 then ["0",s] else [s]
  in
    Substring.translate(fn c =>
      if Char.isAlpha c orelse Char.isDigit c
      then String.str c
      else if c = #"_" then "__"
      else String.concat("_"::pad2 (Int.fmt StringCvt.HEX (Char.ord c))))
    (Substring.full s)
  end

fun add_prime s = "'" ^ s ^ "'"

fun escape_var s =
  let val s1 = escape_to_hex s in "V" ^ s1 end

fun escape_const s = let val s1 = escape_to_hex s in "c" ^ s1 end

fun escape_thm s =
  if (String.sub(s,0) = #"'") orelse (Char.isLower(String.sub(s,0))) then s else add_prime s

(* Less explosive version of POLY_ASSUME_TAC *)
fun fold_cs oper tm sofar =
  let val (l,r) = dest_forall tm handle HOL_ERR _ =>
                  dest_exists tm handle HOL_ERR _ =>
                  dest_abs tm in fold_cs oper r sofar end
  handle HOL_ERR _ =>
      let val (l,r) = dest_conj tm handle HOL_ERR _ =>
                      dest_disj tm handle HOL_ERR _ =>
                      dest_imp tm in
      fold_cs oper r (fold_cs oper l sofar) end
  handle HOL_ERR _ =>
      let val tm = dest_neg tm in fold_cs oper tm sofar end
  handle HOL_ERR _ => if is_eq tm then (* eq is last *)
      let val (c, [l, r]) = strip_comb tm in
      oper (dest_const c) (fold_cs oper r (fold_cs oper l sofar))
      end
  else
      let val (l, r) = dest_comb tm in
      fold_cs oper r (fold_cs oper l sofar) end
  handle HOL_ERR _ =>
    if is_var tm then sofar else oper (dest_const tm) sofar;

(* Translation from ocaml to sml works till this point *)

let rec type_match vty cty sofar =
  if is_vartype vty then
     try if rev_assoc vty sofar = cty then sofar else failwith "type_match"
     with Failure "find" -> (cty,vty)::sofar
  else
     let vop,vargs = dest_type vty and cop,cargs = dest_type cty in
     if vop = cop then itlist2 type_match vargs cargs sofar
     else failwith "type_match";;

fun insts_as gcs tm =
  let fun fold_fun (n, ty) insts =
      let val tys = Lib.assoc n gcs
      fun inst_fun gty inst =
        [raw_match_type ty gty inst] handle HOL_ERR _ => []
      fun gty_fun gty = List.concat (map (inst_fun gty) insts)
      val ret = List.concat (map gty_fun tys) in
      if List.null ret then insts else ret end
    handle HOL_ERR {message="not found",...} => insts
  in
  fold_cs fold_fun tm [[]]
  end

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
    else if is_var tm || is_const tm then failwith "find_lambda"
    else if is_abs tm then tm else
    if is_forall tm || is_exists tm || is_uexists tm
    then find_lambda (body(rand tm)) else
    let l,r = dest_comb tm in
    try find_lambda l with Failure _ -> find_lambda r in
  let rec eLIM_LAMBDA conv tm =
    try conv tm with Failure _ ->
    if is_abs tm then aBS_CONV (eLIM_LAMBDA conv) tm
    else if is_var tm || is_const tm then rEFL tm else
    if is_forall tm || is_exists tm || is_uexists tm
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
    else if is_var tm || is_const tm then failwith "find_lambda"
    else if is_abs tm then tm else
    if is_forall tm || is_exists tm || is_uexists tm
    then find_lambda (body(rand tm)) else
    let l,r = dest_comb tm in
    try find_lambda l with Failure _ -> find_lambda r in
  let rec eLIM_LAMBDA conv tm =
    try conv tm with Failure _ ->
    if is_abs tm then aBS_CONV (eLIM_LAMBDA conv) tm
    else if is_var tm || is_const tm then rEFL tm else
    if is_forall tm || is_exists tm || is_uexists tm
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
