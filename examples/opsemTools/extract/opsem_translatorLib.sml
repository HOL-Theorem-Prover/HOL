structure opsem_translatorLib :> opsem_translatorLib =
struct

open HolKernel boolLib bossLib;
open sepOpsemTheory newOpsemTheory finite_mapTheory arithmeticTheory pred_setTheory;
open stringLib pairSyntax;


val car = fst o dest_comb
val cdr = snd o dest_comb

fun mk_star (tm1,tm2) = (fst o dest_eq o concl o ISPECL [tm1,tm2]) STAR_COMM
fun mk_VAR (tm1,tm2) = (fst o dest_eq o concl o ISPECL [tm1,tm2]) VAR_def
fun mk_ARRAY (tm1,tm2) = (fst o dest_eq o concl o ISPECL [tm1,tm2]) ARRAY_def
fun mk_SEP_SPEC (pre,prog,post) = (fst o dest_eq o concl o ISPECL [pre,prog,post]) SEP_SPEC_def

fun list_mk_star [] = ``emp:state->bool``
  | list_mk_star [x] = x
  | list_mk_star xs = mk_star(list_mk_star (butlast xs),last xs)

fun is_emp tm = fst (dest_const tm) = "emp" handle HOL_ERR _ => false;
fun is_VAR tm = repeat car tm = ``VAR``
fun is_ARRAY tm = repeat car tm = ``ARRAY``
fun is_VAR_or_ARRAY x = (is_VAR x orelse is_ARRAY x)

fun dest_star tm = let
  val (x,z) = dest_comb tm
  val (x,y) = dest_comb x
  in if fst (dest_const x) = "STAR" then (y,z) else hd [] end

fun list_dest f tm = let val (x,y) = f tm in list_dest f x @ list_dest f y end handle e => [tm];
fun list_dest_star tm = filter (not o is_emp) (list_dest dest_star tm);

fun all_distinct [] = []
  | all_distinct (x::xs) = x :: all_distinct (filter (fn y => not (x = y)) xs)

val PRE_CONV = RATOR_CONV o RATOR_CONV o RAND_CONV
val POST_CONV = RAND_CONV

fun SORT_VAR_CONV tm = let
  val xs = list_dest_star tm
  val get_varname = fromHOLstring o cdr o car
  val ys = sort (fn x => fn y => get_varname x < get_varname y) (filter is_VAR_or_ARRAY xs)
  val tm2 = list_mk_star (ys @ filter (not o is_VAR_or_ARRAY) xs)
  in prove(mk_eq(tm,tm2),SIMP_TAC bool_ss [AC STAR_ASSOC STAR_COMM,emp_STAR]) end
  handle HOL_ERR _ => ALL_CONV tm;

val SPEC_SORT_VAR_RULE = CONV_RULE
  (REWRITE_CONV [emp_STAR] THENC PRE_CONV SORT_VAR_CONV THENC POST_CONV SORT_VAR_CONV);

fun EVAL_beval_neval_aeval exp = let
  val tm = subst [``e:nexp``|->exp] ``neval e s``
           handle HOL_ERR _ => subst [``e:bexp``|->exp] ``beval e s``
           handle HOL_ERR _ => subst [``e:aexp``|->exp] ``aeval e s``
  val e = (snd o dest_eq o concl o SIMP_CONV bool_ss [neval_def,aeval_def,beval_def]) tm
  val vs = find_terms (can (match_term ``ScalarOf (s:state ' x)``)) e
  val e = subst (map (fn v => v |-> mk_var(fromHOLstring (cdr (cdr v)),type_of v)) vs) e
  val vs = find_terms (can (match_term ``ArrayOf (s:state ' x)``)) e
  val e = subst (map (fn v => v |-> mk_var(fromHOLstring (cdr (cdr v)),type_of v)) vs) e
  in e end

fun SPEC_FILL_AND_SORT th1 th2 vs ws = let
  val vs = map mk_VAR (map (fn v => (fromMLstring v,mk_var(v,``:int``))) vs)
  val ws = map mk_ARRAY (map (fn v => (fromMLstring v,mk_var(v,``:num|->int``))) ws)
  val p1 = (list_dest_star o cdr o car o car o concl) th1
  val p2 = (list_dest_star o cdr o car o car o concl) th2
  val add_to1 = filter (fn x => not (mem x p1)) (all_distinct (p2 @ vs @ ws))
  val add_to2 = filter (fn x => not (mem x p2)) (all_distinct (p1 @ vs @ ws))
  fun apply_frame th = MATCH_MP SEP_SPEC_FRAME th handle HOL_ERR _ =>
                       MATCH_MP SEP_TOTAL_SPEC_FRAME th
  val th1 = SPEC (list_mk_star add_to1) (apply_frame th1)
  val th2 = SPEC (list_mk_star add_to2) (apply_frame th2)
  val th1 = SPEC_SORT_VAR_RULE th1
  val th2 = SPEC_SORT_VAR_RULE th2
  in (th1,th2) end;

fun find_strings tm =
  if is_string tm then [tm] else
     find_strings (car tm) @ find_strings (cdr tm) handle HOL_ERR _ => []

fun FORCE_PBETA_CONV tm = let
  val (tm1,tm2) = dest_comb tm
  val vs = fst (pairSyntax.dest_pabs tm1)
  fun expand_pair_conv tm = ISPEC tm (GSYM pairTheory.PAIR)
  fun get_conv vs = let
    val (x,y) = pairSyntax.dest_pair vs
    in expand_pair_conv THENC (RAND_CONV (get_conv y)) end
    handle e => ALL_CONV
  in (RAND_CONV (get_conv vs) THENC PairRules.PBETA_CONV) tm end;

fun get_scalar_and_array_varnames tm = let
  val vs = map fromHOLstring (find_strings tm)
  val scalars = map (fromHOLstring o cdr) (find_terms (can (match_term ``Var v``)) tm)
  val a = (find_terms (can (match_term ``Assign v``)) tm)
  val scalars = scalars @ (map (fromHOLstring o cdr) a)
  val vs = all_distinct (filter (fn s => not (mem s scalars)) vs)
  val scalars = all_distinct scalars
  in (scalars,vs) end;

fun get_VAR_and_ARRAY tm v = let
  val (scalars,vs) = get_scalar_and_array_varnames tm
  val vs = filter (fn w => not (w = v)) vs
  val scalars = filter (fn w => not (w = v)) scalars
  val vs = map mk_ARRAY (map (fn v => (fromMLstring v,mk_var(v,``:num |-> int``))) vs)
  val scalars = map mk_VAR (map (fn v => (fromMLstring v,mk_var(v,``:int``))) scalars)
  in scalars @ vs end;

fun PROVE_SEP_EXP th =
  MATCH_MP th (prove((fst o dest_imp o concl) th,
    SIMP_TAC std_ss [SEP_EXP_def,SEP_GUARD_def,pairTheory.FORALL_PROD,GSYM STAR_ASSOC,
      GEN_VAR_STAR,aeval_def,beval_def,neval_def,DOMSUB_FAPPLY_THM,VAR_def,
      ScalarOf_def,ArrayOf_def,ARRAY_def]
    THEN CONV_TAC (DEPTH_CONV stringLib.string_EQ_CONV)
    THEN SIMP_TAC std_ss [ScalarOf_def,ArrayOf_def]));

fun MK_SEP_SPEC_ASSIGN tm total = let
  val v = (fromHOLstring o cdr o car) tm
  val vs = get_VAR_and_ARRAY tm v
  val p = list_mk_star vs
  val z = list_mk_pair(free_vars p) handle e => genvar(``:int``)
  val rhs = EVAL_beval_neval_aeval (cdr tm)
  val n = mk_pabs(mk_pair(mk_var(v,``:int``),z),rhs)
  val th = ISPEC (mk_pabs (z, p)) SEP_SPEC_ASSIGN
  val th = SPECL [fromMLstring v,mk_var(v,``:int``),z,cdr tm,n] th
  val th = PROVE_SEP_EXP th
  val th = SPEC_SORT_VAR_RULE (SIMP_RULE std_ss [] th)
  val th = if total then REWRITE_RULE [SEP_TOTAL_ASSIGN_THM] th else th
  in (th,(mk_var(v,``:int``),rhs)) end;

fun MK_SEP_SPEC_ARRAY_ASSIGN tm total = let
  val v = (fromHOLstring o cdr o car o car) tm
  val vs = get_VAR_and_ARRAY tm v
  val p = list_mk_star vs
  val z = list_mk_pair(free_vars p) handle e => genvar(``:num |-> int``)
  val rhs2 = EVAL_beval_neval_aeval (cdr tm)
  val rhs1 = EVAL_beval_neval_aeval (cdr (car tm))
  val n2 = mk_pabs(mk_pair(mk_var(v,``:num |-> int``),z),rhs2)
  val n1 = mk_pabs(mk_pair(mk_var(v,``:num |-> int``),z),rhs1)
  val th = ISPEC (mk_pabs (z, p)) SEP_SPEC_ARRAY_ASSIGN
  val th = SPECL [fromMLstring v,mk_var(v,``:num|->int``),z,cdr (car tm), cdr tm,n1,n2] th
  val th = PROVE_SEP_EXP th
  val th = PROVE_SEP_EXP th
  val rhs = (cdr o cdr o car o cdr o concl) th
  val rhs = (cdr o concl o SIMP_CONV std_ss []) rhs
  val th = SPEC_SORT_VAR_RULE (SIMP_RULE std_ss [] th)
  val th = if total then REWRITE_RULE [SEP_TOTAL_ARRAY_ASSIGN_THM] th else th
  in (th,(mk_var(v,``:num|->int``),rhs)) end;

fun FORCE_DISCH th = let
  val th = PURE_REWRITE_RULE [GSYM CONJ_ASSOC,AND_IMP_INTRO] (DISCH_ALL th)
  in if is_imp (concl th) then th else DISCH ``T:bool`` th end;

fun is_total th = repeat car (concl th) = ``SEP_TOTAL_SPEC``;

fun MK_SEP_SPEC_SEQ th1 th2 = let
  val (th1,th2) = SPEC_FILL_AND_SORT th1 th2 [] []
  val (i,t) = match_term ((cdr o car o car o concl) th2) ((cdr o concl) th1)
  val th2 = INST i (INST_TYPE t th2)
  in if not (is_total th1) then MATCH_MP SEP_SPEC_SEQ (CONJ th1 th2) else
       (UNDISCH_ALL o REWRITE_RULE [] o MATCH_MP SEP_TOTAL_SPEC_SEQ)
         (CONJ (FORCE_DISCH th1) (FORCE_DISCH th2))
  end;

fun VARS_UNBETA_CONV tm = let
  val vs = filter is_VAR (list_dest_star tm)
  val ws = filter is_ARRAY (list_dest_star tm)
  val x = list_mk_pair (map cdr (vs @ ws))
  val vs = map (fromHOLstring o cdr o car) vs
  val ws = map (fromHOLstring o cdr o car) ws
  val vs' = map (fn v => mk_VAR(fromMLstring v,mk_var(v,``:int``))) vs
  val ws' = map (fn v => mk_ARRAY(fromMLstring v,mk_var(v,``:num|->int``))) ws
  val tm1 = list_mk_star (vs' @ ws' @ filter (not o is_VAR_or_ARRAY) (list_dest_star tm))
  val tm1 = (cdr o concl o SORT_VAR_CONV) tm1
  val p = list_mk_pair (map(fn v => mk_var(v,``:int``)) vs @
                        map(fn v => mk_var(v,``:num|->int``)) ws)
  val tm2 = mk_comb(mk_pabs(p,tm1),x)
  val goal = mk_eq(tm,tm2)
  in prove(goal,SIMP_TAC std_ss [AC STAR_ASSOC STAR_COMM, emp_STAR]) end;

fun MK_SEP_GUARD h th1 = let
  val (x,y) = (dest_comb o cdr o car o car o concl) th1
  val g = mk_pabs(y,EVAL_beval_neval_aeval h)
  val tm = repeat car (inst [``:'a``|->type_of y] ``SEP_GUARD p (g:'a->bool) h``)
  val goal = mk_comb(mk_comb(mk_comb(tm,x),g),h)
  val lemma = prove(``!b. b ==> b:bool``,REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [])
    val th = SPEC goal lemma
  val th = PROVE_SEP_EXP th
  in (g,th) end;

fun MK_SEP_SPEC_COND th1 th2 h = let
  val total = is_total th1
  val (vs,ws) = get_scalar_and_array_varnames h
  val (th1,th2) = SPEC_FILL_AND_SORT th1 th2 vs ws
  val th1 = CONV_RULE (PRE_CONV VARS_UNBETA_CONV THENC POST_CONV VARS_UNBETA_CONV) th1
  val th2 = CONV_RULE (PRE_CONV VARS_UNBETA_CONV THENC POST_CONV VARS_UNBETA_CONV) th2
  val (g,th) = MK_SEP_GUARD h th1
  val th = MATCH_MP (if total then SEP_TOTAL_SPEC_COND else SEP_SPEC_COND) th
  val th = MATCH_MP th (if total then FORCE_DISCH th1 else th1)
  val th = MATCH_MP th (if total then FORCE_DISCH th2 else th2)
  in UNDISCH_ALL th end;

fun MK_SEP_SPEC_WHILE th1 h = let
  val total = is_total th1
  val (vs,ws) = get_scalar_and_array_varnames h
  val th1 = fst (SPEC_FILL_AND_SORT th1 SEP_SPEC_SKIP vs ws)
  val th1 = CONV_RULE (PRE_CONV VARS_UNBETA_CONV THENC POST_CONV VARS_UNBETA_CONV) th1
  val (g,th) = MK_SEP_GUARD h th1
  val p = (cdr o cdr o car o car o concl) th1
  val q = (cdr o cdr o concl) th1
  val thi = prove(mk_eq(q,mk_comb(mk_pabs(p,q),p)),SIMP_TAC std_ss [])
  val th1 = CONV_RULE ((RAND_CONV o RAND_CONV) (fn tm => thi)) th1
  val x = mk_var("x",type_of p)
  val goal = (subst [p|->x] o concl) th1
  val tm2 = mk_pabs(p, (fst o dest_imp o concl o FORCE_DISCH) th1)
  val tm3 = mk_imp(mk_conj(mk_comb(g,x),mk_comb(tm2,x)),goal)
  val goal = mk_forall(x,if total then tm3 else goal)
  val th1 = prove(goal,
    ASSUME_TAC (GEN_ALL (DISCH_ALL th1)) THEN POP_ASSUM MP_TAC
    THEN SIMP_TAC std_ss [pairTheory.FORALL_PROD])
  val thi = if total then SEP_TOTAL_SPEC_WHILE else SEP_SPEC_WHILE
  val th = MATCH_MP thi th
  val th = MATCH_MP th th1
  val th = SIMP_RULE std_ss [] (SPEC p th)
  in th end;

fun find_modified t0 t1 t2 =
  if not (is_pair t0) then
    if (t0 = t1) andalso (t1 = t2) then [] else [t0]
  else let
    val (x0,y0) = dest_pair t0
    val (x1,y1) = dest_pair t1
    val (x2,y2) = dest_pair t2
    in if (x0 = x1) andalso (x1 = x2)
       then find_modified y0 y1 y2 else x0::find_modified y0 y1 y2 end;

fun mk_lets [] p = p
  | mk_lets lets p =
  if fst (last lets) = p then list_mk_anylet(map (fn x => [x]) (butlast lets), snd (last lets))
                         else list_mk_anylet(map (fn x => [x]) lets, p)

(*
val total = true
val name = "hoo"
val index = 0
val instr_tm =
``
       (Seq (Assign "temp" (Arr "a" (Var "i")))
          (Seq (ArrayAssign "a" (Var "i") (Var "j"))
               (ArrayAssign "a" (Var "j") (Var "temp"))))``;

val tm = ((cdr o car) instr_tm)

*)

fun SPEC_FOR_SEQ instr_tm index name total = let
  val func_name = if index = 0 then name else name ^ int_to_string index
  in if repeat car instr_tm = ``Skip`` then
    (if total then SEP_TOTAL_SPEC_SKIP else SEP_SPEC_SKIP,[],index,TRUTH,TRUTH)
  else if repeat car instr_tm = ``Assign`` then let
    val (th,(lhs,rhs)) = MK_SEP_SPEC_ASSIGN instr_tm total
    in (th,[(lhs,rhs)],index,TRUTH,TRUTH) end
  else if repeat car instr_tm = ``ArrayAssign`` then let
    val (th,(lhs,rhs)) = MK_SEP_SPEC_ARRAY_ASSIGN instr_tm total
    in (th,[(lhs,rhs)],index,TRUTH,TRUTH) end
  else if repeat car instr_tm = ``Seq`` then let
    val (th1,lets1,i1,rw_th1,rw_pre1) = SPEC_FOR_SEQ ((cdr o car) instr_tm) index name total
    val (th2,lets2,i2,rw_th2,rw_pre2) = SPEC_FOR_SEQ (cdr instr_tm) i1 name total
    val th = MK_SEP_SPEC_SEQ th1 th2
    val f = fst o dest_imp o concl o FORCE_DISCH
    val tm2 = f th2
    val tm2 = if tm2 = T then T else mk_lets lets1 tm2
    val goal = mk_eq(f th, mk_conj(f th1,tm2))
    val lemma = prove(goal,SIMP_TAC std_ss [LET_DEF]
               THEN CONV_TAC (DEPTH_CONV FORCE_PBETA_CONV)
               THEN REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
               THEN ASM_SIMP_TAC std_ss [LET_DEF])
    val th = CONV_RULE (RATOR_CONV (RAND_CONV (fn tm => lemma))) (FORCE_DISCH th)
    val th = UNDISCH_ALL (REWRITE_RULE [] th)
    val rw_th = CONJ rw_th1 rw_th2
    val rw_pre = CONJ rw_pre1 rw_pre2
    in (th,lets1@lets2,i2,rw_th,rw_pre) end
  else if repeat car instr_tm = ``Cond`` then let
    val (th1,lets1,i1,rw_th1,rw_pre1) = SPEC_FOR_SEQ ((cdr o car) instr_tm) (index+1) name total
    val (th2,lets2,i2,rw_th2,rw_pre2) = SPEC_FOR_SEQ (cdr instr_tm) i1 name total
    val th = MK_SEP_SPEC_COND th1 th2 ((cdr o car o car) instr_tm)
    val tm = (cdr o cdr o concl) th
    val (g_tm,t1,t2) = dest_cond tm
    val g = (cdr o concl o SIMP_CONV std_ss []) g_tm
    val t0 = cdr g_tm
    val t4 = if index = 0 then t0 else list_mk_pair (find_modified t0 t1 t2)
    val l1 = mk_lets lets1 t4
    val l2 = mk_lets lets2 t4
    val rhs = mk_cond(g,l1,l2)
    val f = mk_var(func_name,mk_type("fun",[type_of (cdr g_tm),type_of rhs]))
    val def = Define [ANTIQUOTE (mk_eq(mk_comb(f,t0),rhs))]
    fun find_result xs [] func = xs
      | find_result [] ys func = []
      | find_result (x::xs) (y::ys) func =
         if not (x = y) then x :: find_result xs (y::ys) func else
         if length ys = 0 then func :: find_result xs [] func else
           mk_fst func :: find_result xs ys (mk_snd func)
    val xs = list_dest dest_pair t0
    val ys = list_dest dest_pair t4
    val func = (fst o dest_eq o concl o SPEC_ALL) def
    val tm2 = list_mk_pair (find_result xs ys func)
    val goal = mk_eq(tm,tm2)
    val rw = prove(goal,
      SIMP_TAC std_ss [def] THEN Cases_on [ANTIQUOTE g] THEN FULL_SIMP_TAC std_ss [LET_DEF]
      THEN CONV_TAC (DEPTH_CONV FORCE_PBETA_CONV)
      THEN ASM_SIMP_TAC std_ss [def,LET_DEF])
    val th = CONV_RULE (RAND_CONV (RAND_CONV (fn tm => rw))) th
    val th = SIMP_RULE std_ss [] th
    val th = FORCE_DISCH th
    val th = REWRITE_RULE [] (CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV std_ss [])) th)
    val (th,def_pre) = if not (is_imp (concl th)) then (th,TRUTH) else let
      val f_pre = mk_var(func_name^"_pre",mk_type("fun",[type_of (cdr g_tm),``:bool``]))
      val def_pre = Define [ANTIQUOTE (mk_eq(mk_comb(f_pre,cdr g_tm),(cdr o car o concl) th))]
      val th = REWRITE_RULE [GSYM def_pre] th
      in (th,def_pre) end
    val th = UNDISCH_ALL th
    val rw_th = CONJ (SPEC_ALL def) (CONJ rw_th1 rw_th2)
    val rw_pre = CONJ (SPEC_ALL def_pre) (CONJ rw_pre1 rw_pre2)
    in (th,[(t4,func)],i2,rw_th,rw_pre) end
  else if repeat car instr_tm = ``While`` then let
    val (th1,lets1,i1,rw_th1,rw_pre1) = SPEC_FOR_SEQ (cdr instr_tm) (index+1) name total
    val th = MK_SEP_SPEC_WHILE th1 ((cdr o car) instr_tm)
    val (func,p) = (dest_comb o cdr o cdr o concl o UNDISCH_ALL) th
    val f = mk_var(func_name,type_of func)
    val def = Define [ANTIQUOTE (mk_eq(f,func))]
    val func_pre = (car o cdr o car o concl o FORCE_DISCH) th handle HOL_ERR _ => T
    val f_pre = mk_var(func_name^"_pre",type_of func_pre)
    val def_pre = if total then Define [ANTIQUOTE (mk_eq(f_pre,func_pre))] else TRUTH
    val th = REWRITE_RULE [GSYM def, GSYM def_pre] th
    val func_tm = mk_comb((cdr o car o concl o SPEC_ALL) def,p)
    val th = UNDISCH_ALL (CONV_RULE (DEPTH_CONV FORCE_PBETA_CONV) th)
    val l1 = mk_lets lets1 func_tm
    val g = (cdr o concl o SIMP_CONV std_ss []) (mk_comb ((cdr o car) func,p))
    val goal = mk_eq(func_tm,mk_cond(mk_neg g,p,l1))
    val rw = prove(goal,
      CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [def]))
      THEN ONCE_REWRITE_TAC [whileTheory.WHILE]
      THEN Cases_on [ANTIQUOTE g]
      THEN FULL_SIMP_TAC std_ss [def,LET_DEF]
      THEN CONV_TAC (DEPTH_CONV FORCE_PBETA_CONV)
      THEN ASM_SIMP_TAC std_ss [def,LET_DEF])
    val rw_pre = if not total then TRUTH else let
      val pre_tm = mk_comb(((cdr o concl o SPEC_ALL) def_pre),p)
      val (i,t) = match_term ((cdr o car o concl o SPEC_ALL) PRE_THM) pre_tm
      val rw_pre = (INST i o INST_TYPE t o SPEC_ALL) PRE_THM
      val rw_pre = PURE_REWRITE_RULE [GSYM def_pre] rw_pre
      val tm = (cdr o cdr o cdr o concl) rw_pre
      val goal = mk_eq(tm,mk_lets lets1 (mk_comb(car tm, p)))
      val lemma = prove(goal,SIMP_TAC std_ss [LET_DEF] THEN
                        CONV_TAC (DEPTH_CONV FORCE_PBETA_CONV) THEN SIMP_TAC std_ss [])
      val rw_pre = CONV_RULE ((RAND_CONV o RAND_CONV o RAND_CONV) (fn tm => lemma)) rw_pre
      val rw_pre = SIMP_RULE std_ss [] rw_pre
      in rw_pre end
    val rw_th = CONJ (SPEC_ALL rw) rw_th1
    val rw_pre = CONJ (SPEC_ALL rw_pre) rw_pre1
    in (th,[(p,func_tm)],i1,rw_th,rw_pre) end
  else raise mk_HOL_ERR "sepOpsemLib" "FUNCTION"
    ("Program construct not supported: " ^ term_to_string (repeat car instr_tm)) end

fun RAW_SPEC_FOR_CODE instr_tm name total =
  if mem (repeat car instr_tm) [``While``,``Cond``] then let
    val (th,lets,_,rw,rw_pre) = SPEC_FOR_SEQ instr_tm 0 name total
    in (th,CONJ rw rw_pre) end
  else let
    val (th,lets,_,rw,rw_pre) = SPEC_FOR_SEQ instr_tm 1 name total
    val th1 = CONV_RULE (PRE_CONV VARS_UNBETA_CONV THENC POST_CONV VARS_UNBETA_CONV) th
    val p = (cdr o cdr o car o car o concl) th1
    val l1 = mk_lets lets p
    val f = mk_var(name,mk_type("fun",[type_of l1,type_of p]))
    val def = Define [ANTIQUOTE (mk_eq(mk_comb(f,p),l1))]
    val rw = CONJ (SPEC_ALL def) rw
    val f = fst o dest_imp o concl o FORCE_DISCH
    val (th,rw_pre) = if f th = T then (th,rw_pre) else let
      val f_pre = mk_var(name^"_pre",mk_type("fun",[type_of l1,``:bool``]))
      val def_pre = Define [ANTIQUOTE (mk_eq(mk_comb(f_pre,p),f th))]
      val rw_pre = CONJ (SPEC_ALL def_pre) rw_pre
      val th = CONV_RULE (RATOR_CONV (RAND_CONV (REWRITE_CONV [GSYM def_pre]))) (FORCE_DISCH th)
      val th = UNDISCH th
      in (th,rw_pre) end
    in (th,CONJ rw rw_pre) end;

fun DERIVE_SEP_SPEC_AUX total name instr_tm = let
  val (th,rw) = RAW_SPEC_FOR_CODE instr_tm name total
  val rw = REWRITE_RULE [GSYM CONJ_ASSOC] rw
  val f = (fst o dest_eq o concl o hd o CONJUNCTS) rw
  val p = (cdr o cdr o car o car o concl o CONV_RULE (PRE_CONV VARS_UNBETA_CONV)) th
  val q = (cdr o concl) th
  val q2 = mk_anylet([(p,f)],(cdr o car o car o concl) th)
  val lemma = prove(mk_eq(q,q2),
    SIMP_TAC std_ss [LET_DEF]
    THEN CONV_TAC (DEPTH_CONV FORCE_PBETA_CONV)
    THEN ASM_SIMP_TAC std_ss [LET_DEF]
    THEN CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [rw]))
    THEN SIMP_TAC std_ss [LET_DEF]
    THEN CONV_TAC (DEPTH_CONV FORCE_PBETA_CONV)
    THEN ASM_SIMP_TAC std_ss [LET_DEF])
  val th = CONV_RULE (RAND_CONV (fn tm => lemma)) th
  val th = REWRITE_RULE [] (FORCE_DISCH th)
  val _ = save_thm(name^"_thm",rw)
  val _ = save_thm(name^"_program",th)
  in (th,rw) end;

val DERIVE_SEP_SPEC = DERIVE_SEP_SPEC_AUX false;
val DERIVE_SEP_TOTAL_SPEC = DERIVE_SEP_SPEC_AUX true;

val EXPAND_PAIR_LEMMA = prove(
  ``!x p q. (x = (p:'a,q:'b)) = (FST x = p) /\ (SND x = q)``,
  Cases THEN SIMP_TAC std_ss []);

fun SEP_SPEC_SEMANTICS th = let
  val th1 = REWRITE_RULE [SEP_SPEC_THM,SEP_TOTAL_SPEC_THM,LET_DEF] (UNDISCH_ALL th)
  val th1 = CONV_RULE (DEPTH_CONV FORCE_PBETA_CONV) th1
  val th1 = REWRITE_RULE [GSYM STAR_ASSOC,VAR_def,ARRAY_def,GEN_VAR_STAR,FDOM_DOMSUB,IN_DELETE] th1
  val th1 = SIMP_RULE std_ss [GSYM AND_IMP_INTRO] th1
  val th1 = REWRITE_RULE [DOMSUB_FAPPLY_THM] th1
  val th1 = SIMP_RULE bool_ss [] th1
  val th1 = CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV) th1
  val th1 = REWRITE_RULE [] th1
  val r = genvar(``:state->bool``)
  val s1 = genvar(``:state``)
  val th1 = SPECL [r,s1] th1
  val tm = (cdr o cdr o fst o dest_imp o concl o REWRITE_RULE [AND_IMP_INTRO]) th1
  val v = genvar(``:state``)
  val frame = mk_abs(v,mk_eq(tm,v))
  val th1 = INST [r|->frame] th1
  val th1 = INST [s1|->``s1:state``] th1
  val th1 = SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC] (DISCH_ALL th1)
  val th1 = GEN ``s1:state`` th1
  in th1 end;


end
