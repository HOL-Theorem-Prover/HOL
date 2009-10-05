open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_final";

open lisp_evalTheory lisp_parseTheory lisp_printTheory lisp_proofTheory;
open lisp_invTheory;
open pairSyntax helperLib;
open listTheory pred_setTheory;
open progTheory addressTheory set_sepTheory;
open finite_mapTheory;

val aLISP_def = lisp_opsTheory.aLISP_def;
val pLISP_def = lisp_opsTheory.pLISP_def;
val xLISP_def = lisp_opsTheory.xLISP_def;

(* aid in hiding the code, temporarily *)

fun take_until p [] = []
  | take_until p (x::xs) = if p x then [] else x:: take_until p xs

val code_abbreviations = ref ([]:thm list);
fun add_code_abbrev thms = (code_abbreviations := thms @ !code_abbreviations);

fun ABBREV_CODE_RULE name th = let
  val (m,_,c,_) = (dest_spec o concl o SPEC_ALL) th
  val model_name = (to_lower o implode o take_until (fn x => x = #"_") o explode o fst o dest_const) m
  val x = list_mk_pair (free_vars c)
  val def_name = name ^ "_" ^ model_name
  val v = mk_var(def_name,type_of(mk_pabs(x,c)))
  val code_def = new_definition(def_name ^ "_def",mk_eq(mk_comb(v,x),c))
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
           (ONCE_REWRITE_CONV [GSYM code_def])) (UNDISCH_ALL th)
  val _ = add_code_abbrev [code_def]
  in th end;

(* SPEC tools *)

fun SPEC_STRENGTHEN_RULE th pre = let
  val th = SPEC pre (MATCH_MP progTheory.SPEC_STRENGTHEN th)
  val goal = (fst o dest_imp o concl) th
  in (th,goal) end;

fun SPEC_WEAKEN_RULE th post = let
  val th = SPEC post (MATCH_MP progTheory.SPEC_WEAKEN th)
  val goal = (fst o dest_imp o concl) th
  in (th,goal) end;

fun SPEC_FRAME_RULE th frame =
  SPEC frame (MATCH_MP progTheory.SPEC_FRAME th)

fun SPEC_BOOL_FRAME_RULE th frame = let
  val th = MATCH_MP progTheory.SPEC_FRAME th
  val th = Q.SPEC `cond boolean_variable_name` th
  val th = INST [mk_var("boolean_variable_name",``:bool``) |-> frame] th
  in th end

fun subst_SPEC_PC th tm = let
  val p = find_term (can (match_term ``aPC p``)) (cdr (concl th)) handle e =>
          find_term (can (match_term ``pPC p``)) (cdr (concl th)) handle e =>
          find_term (can (match_term ``xPC p``)) (cdr (concl th))
  val p = cdr p
  val tm = subst [mk_var("p",``:word32``) |-> p] tm
  in tm end;

fun spec_pre th = let
  val (_,p,_,_) = dest_spec (concl th) in (list_dest dest_star p, type_of p) end;
fun spec_post th = let
  val (_,_,_,q) = dest_spec (concl th) in (list_dest dest_star q, type_of q) end;

fun spec_post_and_pre th1 th2 = let
  val (_,_,_,q) = dest_spec (concl th1)
  val (_,p,_,_) = dest_spec (concl th2)
  in (list_dest dest_star q, list_dest dest_star p, type_of q) end;

fun DISCH_ALL_AS_SINGLE_IMP th = let
  val th = RW [AND_IMP_INTRO] (DISCH_ALL th)
  in if is_imp (concl th) then th else DISCH ``T`` th end

fun remove_primes th = let
  fun last s = substring(s,size s-1,1)
  fun delete_last_prime s = if last s = "'" then substring(s,0,size(s)-1) else fail()
  fun foo [] ys i = i
    | foo (x::xs) ys i = let
      val name = (fst o dest_var) x
      val new_name = repeat delete_last_prime name
      in if name = new_name then foo xs (x::ys) i else let
        val new_var = mk_var(new_name,type_of x)
        in foo xs (new_var::ys) ((x |-> new_var) :: i) end end
  val i = foo (free_varsl (concl th :: hyp th)) [] []
  in INST i th end

fun find_composition1 th1 th2 = let
  val (q,p,ty) = spec_post_and_pre th1 th2
  fun get_match_term tm = get_sep_domain tm
  fun mm x y = get_match_term x = get_match_term y
  fun fetch_match x [] zs = fail()
    | fetch_match x (y::ys) zs =
        if mm x y then (y, rev zs @ ys) else fetch_match x ys (y::zs)
  fun partition [] ys (xs1,xs2,ys1) = (rev xs1, rev xs2, rev ys1, ys)
    | partition (x::xs) ys (xs1,xs2,ys1) =
        let val (y,zs) = fetch_match x ys [] in
          partition xs zs (x::xs1, xs2, y::ys1)
        end handle e =>
          partition xs ys (xs1, x::xs2, ys1)
  val (xs1,xs2,ys1,ys2) = partition q p ([],[],[])
  val tm1 = mk_star (list_mk_star xs1 ty, list_mk_star xs2 ty)
  val tm2 = mk_star (list_mk_star ys1 ty, list_mk_star ys2 ty)
  val th1 = CONV_RULE (POST_CONV (MOVE_STAR_CONV tm1)) th1
  val th2 = CONV_RULE (PRE_CONV (MOVE_STAR_CONV tm2)) th2
  val th = MATCH_MP SPEC_FRAME_COMPOSE (DISCH_ALL_AS_SINGLE_IMP th2)
  val th = MATCH_MP th (DISCH_ALL_AS_SINGLE_IMP th1)
  val th = UNDISCH_ALL (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO,AND_CLAUSES] th)
  val th = SIMP_RULE std_ss [INSERT_UNION_EQ,UNION_EMPTY,word_arith_lemma1,
             word_arith_lemma2,word_arith_lemma3,word_arith_lemma4,SEP_CLAUSES] th
  in remove_primes th end;

fun find_composition2 th1 th2 = let
  val (q,p,ty) = spec_post_and_pre th1 th2
  val post_not_hidden = map get_sep_domain (filter (not o can dest_sep_hide) q)
  val pre_not_hidden  = map get_sep_domain (filter (not o can dest_sep_hide) p)
  fun f (d:term,(zs,to_be_hidden)) =
    if not (can dest_sep_hide d) then (zs,to_be_hidden) else
      (zs,filter (fn x => get_sep_domain d = x) zs @ to_be_hidden)
  val hide_from_post = snd (foldr f (post_not_hidden,[]) p)
  val hide_from_pre  = snd (foldr f (pre_not_hidden,[]) q)
  val th1 = foldr (uncurry HIDE_POST_RULE) th1 hide_from_post
  val th2 = foldr (uncurry HIDE_PRE_RULE) th2 hide_from_pre
  in find_composition1 th1 th2 end;

val SPEC_COMPOSE_RULE = find_composition2;

fun LISP_SPEC_COMPOSE_RULE [] = fail()
  | LISP_SPEC_COMPOSE_RULE [th] = th
  | LISP_SPEC_COMPOSE_RULE (th1::th2::thms) =
      LISP_SPEC_COMPOSE_RULE ((SPEC_COMPOSE_RULE th1 th2)::thms)

(* SEP_EXISTS tools *)

(* val tm = ``(SEP_EXISTS f z. cond (z = f + 5)) s`` *)

open set_sepTheory
open wordsTheory

fun SEP_EXISTS_CONV tm = let
  val m = ``$SEP_EXISTS (P :'a -> ('b -> bool) -> bool) (x :'b -> bool)``
  val i = match_term m tm
  val (i,m) = match_term ((cdr o car o concl) SEP_EXISTS) ((car o car) tm)
  val v = (fst o dest_abs o cdr o car) tm
  val ty = (type_of o fst o dest_abs o cdr o car) tm
  fun BETTER_ALPHA_CONV s tm = let
    val (v,x) = dest_abs(tm)
    in ALPHA_CONV (mk_var(s,type_of v)) tm end
  val thi = CONV_RULE (
              (RAND_CONV) (BETTER_ALPHA_CONV "_") THENC
              (RAND_CONV o ABS_CONV o ABS_CONV o RAND_CONV)
                (ALPHA_CONV v)) (INST_TYPE m SEP_EXISTS)
  in (((RATOR_CONV o RATOR_CONV) (fn tm => thi))
      THENC (RATOR_CONV BETA_CONV) THENC BETA_CONV
      THENC (QUANT_CONV o RATOR_CONV) BETA_CONV) tm end

fun EX_TAC [] = ALL_TAC
  | EX_TAC (x::xs) = Q.EXISTS_TAC x THEN EX_TAC xs

(* print *)

val _ = map Parse.hide ["r0","r1","r2","r3","r4","r5","r6","r7","r8","r9"]

val one_string_IMP_string_mem = prove(
  ``!s a c df f. one_string a s c (fun2set (f,df)) ==> string_mem s (a,f,df)``,
  Induct
  THEN FULL_SIMP_TAC std_ss [one_string_def,MAP,one_list_def,cond_def,
      string_mem_def,one_STAR,IN_fun2set,GSYM AND_IMP_INTRO,fun2set_DELETE]
  THEN ONCE_REWRITE_TAC [EQ_SYM_EQ]
  THEN FULL_SIMP_TAC std_ss [fun2set_DELETE]
  THEN REPEAT STRIP_TAC
  THEN RES_TAC
  THEN POP_ASSUM MP_TAC
  THEN REPEAT (POP_ASSUM (K ALL_TAC))
  THEN Q.SPEC_TAC (`a+1w`,`b`)
  THEN Induct_on `s`
  THEN ASM_SIMP_TAC std_ss [string_mem_def,IN_DELETE]);

val aLISP1_def = Define `
  aLISP1 (x,l) = SEP_EXISTS x2 x3 x4 x5 x6. aLISP (x,x2,x3,x4,x5,x6,l)`;
val pLISP1_def = Define `
  pLISP1 (x,l) = SEP_EXISTS x2 x3 x4 x5 x6. pLISP (x,x2,x3,x4,x5,x6,l)`;
val xLISP1_def = Define `
  xLISP1 (x,l) = SEP_EXISTS x2 x3 x4 x5 x6. xLISP (x,x2,x3,x4,x5,x6,l)`;

val aSTRING_SPACE_def = Define `
  aSTRING_SPACE a n = SEP_EXISTS df f c. aBYTE_MEMORY df f *
      cond (one_space a (n + 1) c (fun2set (f,df)))`;
val pSTRING_SPACE_def = Define `
  pSTRING_SPACE a n = SEP_EXISTS df f c. pBYTE_MEMORY df f *
      cond (one_space a (n + 1) c (fun2set (f,df)))`;
val xSTRING_SPACE_def = Define `
  xSTRING_SPACE a n = SEP_EXISTS df f c. xBYTE_MEMORY df f *
      cond (one_space a (n + 1) c (fun2set (f,df)))`;

val one_space_EXPAND = prove(
  ``!n a b s. one_space a n b s =
              one_space a n (a + n2w n) s /\ (b = a + n2w n)``,
  Induct
  THEN SIMP_TAC std_ss [one_space_def,WORD_ADD_0,cond_def,SEP_EXISTS]
  THEN SIMP_TAC std_ss [one_STAR]
  THEN ONCE_ASM_REWRITE_TAC []
  THEN SIMP_TAC std_ss [DECIDE ``SUC n = 1 + n``,GSYM word_add_n2w,WORD_ADD_ASSOC]
  THEN METIS_TAC []);

val arm_sexp2string_th = let
  val th = arm_sexp2string_thm
  val imp = arm_print_sexp_lemma
  val imp = Q.INST [`r7`|->`r1`,`rest`|->`(dm,m,dg,g)`] imp
  val imp = SIMP_RULE std_ss [] (RW1 [one_space_EXPAND] imp)
  val imp = Q.INST [`c`|->`r1 + n2w (STRLEN (sexp2string t1) + 1)`] imp
  val imp = RW [] imp
  val tm = (fst o dest_imp o concl) imp
  val th = SPEC_BOOL_FRAME_RULE th tm
  val th = Q.INST [`r3`|->`w1`] th
  val post = ``SEP_EXISTS r3 dg g dm m dh h. aR 3w r3 * aSTRING r3 (sexp2string t1)
         * aBYTE_MEMORY dg g * aMEMORY dh h * aMEMORY dm m * ~aR 0w *
         ~aR 1w * ~aR 2w * ~aR 4w * ~aR 5w * ~aR 6w * ~aR 7w
         * ~aR 8w * ~aR 9w * aPC p * ~aS``
  val post = subst_SPEC_PC th post
  val (th,goal) = SPEC_WEAKEN_RULE th post
  val tac =
    SIMP_TAC std_ss [aSTRING_def]
    THEN SIMP_TAC std_ss [SEP_CLAUSES,SEP_IMP_MOVE_COND]
    THEN STRIP_TAC
    THEN IMP_RES_TAC (Q.INST [`w1`|->`r3`] imp)
    THEN FULL_SIMP_TAC (std_ss++sep_cond_ss) [arm_sexp2string_def,LET_DEF]
    THEN SIMP_TAC std_ss [SEP_IMP_def]
    THEN CONV_TAC (REPEATC (DEPTH_CONV SEP_EXISTS_CONV))
    THEN REPEAT STRIP_TAC
    THEN EX_TAC [`r1`,`dg`,`g`,`dm`,`m`,`dh`,`hi`,`df`,`fi`]
    THEN IMP_RES_TAC one_string_IMP_string_mem
    THEN ASM_SIMP_TAC std_ss [cond_STAR]
    THEN FULL_SIMP_TAC std_ss [AC STAR_ASSOC STAR_COMM]
  val th = MP th (prove(goal,tac))
  val th = foldr (uncurry EXISTS_PRE) th [`df`,`f`,`dg`,`g`,`dm`,`m`,`dh`,`h`,`sym`]
  val th = foldr (uncurry EXISTS_PRE) th [`t2`,`t3`,`t4`,`t5`,`t6`]
  val th = foldr (uncurry EXISTS_PRE) th [`w1`,`w2`,`w3`,`w4`,`w5`,`w6`,`r9`]
  val pre = ``aLISP1 (t1,l) * aR 1w r1 * aSTRING_SPACE r1 (LENGTH (sexp2string t1)) *
              ~aR 0w * aPC p * ~aS``
  val (th,goal) = SPEC_STRENGTHEN_RULE th pre
  val tac =
    SIMP_TAC std_ss [aSTRING_SPACE_def]
    THEN SIMP_TAC std_ss [SEP_CLAUSES,SEP_IMP_MOVE_COND]
    THEN SIMP_TAC std_ss [aLISP1_def,aLISP_def]
    THEN SIMP_TAC std_ss [SEP_CLAUSES,SEP_IMP_MOVE_COND]
    THEN SIMP_TAC std_ss [SEP_IMP_def]
    THEN CONV_TAC (REPEATC (DEPTH_CONV SEP_EXISTS_CONV))
    THEN SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,Once one_space_EXPAND]
    THEN NTAC 2 STRIP_TAC
    THEN EX_TAC [`r3'`,`r4'`,`r5'`,`r6'`,`r7'`,`r8'`,`a`]
    THEN EX_TAC [`x2`,`x3`,`x4`,`x5`,`x6`]
    THEN EX_TAC [`df`,`f`,`dg`,`g`,`dm`,`m`,`df'`,`f'`,`s'`]
    THEN IMP_RES_TAC imp
    THEN ASM_SIMP_TAC std_ss [arm_sexp2string_pre_def,LET_DEF]
    THEN SIMP_TAC (std_ss++sep_cond_ss) [Q.ISPEC `aR 4w` SEP_HIDE_def,SEP_CLAUSES]
    THEN SIMP_TAC (std_ss++sep_cond_ss) [Q.ISPEC `aR 5w` SEP_HIDE_def,SEP_CLAUSES]
    THEN SIMP_TAC (std_ss++sep_cond_ss) [Q.ISPEC `aR 6w` SEP_HIDE_def,SEP_CLAUSES]
    THEN SIMP_TAC (std_ss++sep_cond_ss) [Q.ISPEC `aR 7w` SEP_HIDE_def,SEP_CLAUSES]
    THEN SIMP_TAC (std_ss++sep_cond_ss) [Q.ISPEC `aR 8w` SEP_HIDE_def,SEP_CLAUSES]
    THEN CONV_TAC (REPEATC (DEPTH_CONV SEP_EXISTS_CONV))
    THEN EX_TAC [`r4'`,`r5'`,`r6'`,`r7'`,`r8'`]
    THEN FULL_SIMP_TAC std_ss [AC STAR_ASSOC STAR_COMM]
  val th = MP th (prove(goal,tac))
  in th end;

val ppc_sexp2string_th = let
  val th = ppc_sexp2string_thm
  val imp = arm_print_sexp_lemma
  val imp = Q.INST [`r7`|->`r1`,`rest`|->`(dm,m,dg,g)`] imp
  val imp = SIMP_RULE std_ss [] (RW1 [one_space_EXPAND] imp)
  val imp = Q.INST [`c`|->`r1 + n2w (STRLEN (sexp2string t1) + 1)`] imp
  val imp = RW [] imp
  val tm = (fst o dest_imp o concl) imp
  val th = SPEC_BOOL_FRAME_RULE th tm
  val th = Q.INST [`r3`|->`w1`] th
  val post = ``SEP_EXISTS r3 dg g dm m dh h. pR 3w r3 * pSTRING r3 (sexp2string t1)
         * pBYTE_MEMORY dg g * pMEMORY dh h * pMEMORY dm m * ~pR 0w *
         ~pR 1w * ~pR 2w * ~pR 4w * ~pR 5w * ~pR 6w * ~pR 7w
         * ~pR 8w * ~pR 9w * pPC p * ~pS``
  val post = subst_SPEC_PC th post
  val (th,goal) = SPEC_WEAKEN_RULE th post
  val tac =
    SIMP_TAC std_ss [pSTRING_def]
    THEN SIMP_TAC std_ss [SEP_CLAUSES,SEP_IMP_MOVE_COND]
    THEN STRIP_TAC
    THEN IMP_RES_TAC (Q.INST [`w1`|->`r3`] imp)
    THEN FULL_SIMP_TAC (std_ss++sep_cond_ss) [ppc_sexp2string_def,LET_DEF,WORD_OR_CLAUSES]
    THEN SIMP_TAC std_ss [SEP_IMP_def]
    THEN CONV_TAC (REPEATC (DEPTH_CONV SEP_EXISTS_CONV))
    THEN REPEAT STRIP_TAC
    THEN EX_TAC [`r1`,`dg`,`g`,`dm`,`m`,`dh`,`hi`,`df`,`fi`]
    THEN IMP_RES_TAC one_string_IMP_string_mem
    THEN ASM_SIMP_TAC std_ss [cond_STAR]
    THEN FULL_SIMP_TAC std_ss [AC STAR_ASSOC STAR_COMM]
  val th = MP th (prove(goal,tac))
  val th = foldr (uncurry EXISTS_PRE) th [`df`,`f`,`dg`,`g`,`dm`,`m`,`dh`,`h`,`sym`]
  val th = foldr (uncurry EXISTS_PRE) th [`t2`,`t3`,`t4`,`t5`,`t6`]
  val th = foldr (uncurry EXISTS_PRE) th [`w1`,`w2`,`w3`,`w4`,`w5`,`w6`,`r9`]
  val pre = ``pLISP1 (t1,l) * pR 1w r1 * pSTRING_SPACE r1 (LENGTH (sexp2string t1)) *
              pPC p * ~pS``
  val (th,goal) = SPEC_STRENGTHEN_RULE th pre
  val tac =
    SIMP_TAC std_ss [pSTRING_SPACE_def]
    THEN SIMP_TAC std_ss [SEP_CLAUSES,SEP_IMP_MOVE_COND]
    THEN SIMP_TAC std_ss [pLISP1_def,pLISP_def]
    THEN SIMP_TAC std_ss [SEP_CLAUSES,SEP_IMP_MOVE_COND]
    THEN SIMP_TAC std_ss [SEP_IMP_def]
    THEN CONV_TAC ((REDEPTH_CONV SEP_EXISTS_CONV))
    THEN SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,Once one_space_EXPAND]
    THEN NTAC 2 STRIP_TAC
    THEN EX_TAC [`r3'`,`r4'`,`r5'`,`r6'`,`r7'`,`r8'`,`a`]
    THEN EX_TAC [`x2`,`x3`,`x4`,`x5`,`x6`]
    THEN EX_TAC [`df`,`f`,`dg`,`g`,`dm`,`m`,`df'`,`f'`,`s'`]
    THEN IMP_RES_TAC imp
    THEN ASM_SIMP_TAC std_ss [ppc_sexp2string_pre_def,LET_DEF,WORD_OR_CLAUSES]
    THEN SIMP_TAC (std_ss++sep_cond_ss) [Q.ISPEC `pR 4w` SEP_HIDE_def,SEP_CLAUSES]
    THEN SIMP_TAC (std_ss++sep_cond_ss) [Q.ISPEC `pR 5w` SEP_HIDE_def,SEP_CLAUSES]
    THEN SIMP_TAC (std_ss++sep_cond_ss) [Q.ISPEC `pR 6w` SEP_HIDE_def,SEP_CLAUSES]
    THEN SIMP_TAC (std_ss++sep_cond_ss) [Q.ISPEC `pR 7w` SEP_HIDE_def,SEP_CLAUSES]
    THEN SIMP_TAC (std_ss++sep_cond_ss) [Q.ISPEC `pR 8w` SEP_HIDE_def,SEP_CLAUSES]
    THEN CONV_TAC (REPEATC (DEPTH_CONV SEP_EXISTS_CONV))
    THEN EX_TAC [`r4'`,`r5'`,`r6'`,`r7'`,`r8'`]
    THEN FULL_SIMP_TAC std_ss [AC STAR_ASSOC STAR_COMM]
  val th = MP th (prove(goal,tac))
  in th end;

val xSTACK_def = Define `
  (xSTACK a [] = cond (ALIGNED a)) /\
  (xSTACK a (w::ws) = xM a w * xSTACK (a + 4w) ws)`;

val xSTACK_PUSH_EDI = let
  val (th,t_def) = decompilerLib.decompile
    prog_x86Lib.x86_tools "test" [QUOTE (x86_encodeLib.x86_encode "push edi")]
  val th = SIMP_RULE std_ss [t_def,LET_DEF] th
  val th = Q.INST [`df`|->`{esp - 4w}`,`f`|->`\x.w`] th
  val th = SPEC_BOOL_FRAME_RULE th ``ALIGNED esp``
  val post = ``xSTACK (esp-4w) [edi] * xR EDI edi * xR ESP (esp - 0x4w) * xPC (p + 0x1w)``
  val (th,goal) = SPEC_WEAKEN_RULE th post
  val tac =
    SIMP_TAC std_ss [SEP_IMP_MOVE_COND,xSTACK_def,prog_x86Theory.xM_THM,
      ALIGNED,SEP_CLAUSES] THEN SIMP_TAC (std_ss++star_ss) [SEP_IMP_REFL]
  val th = MP th (prove(goal,tac))
  val pre = ``xSTACK (esp-4w) [w] * xR EDI edi * xR ESP esp * xPC p``
  val (th,goal) = SPEC_STRENGTHEN_RULE th pre
  val tac =
    SIMP_TAC (std_ss++sep_cond_ss) [SEP_IMP_MOVE_COND,xSTACK_def,prog_x86Theory.xM_THM,
      ALIGNED,SEP_CLAUSES,SEP_IMP_REFL,IN_INSERT,NOT_IN_EMPTY]
    THEN SIMP_TAC (std_ss++star_ss) [ALIGNED_INTRO,ALIGNED,SEP_CLAUSES,SEP_IMP_REFL]
  val th = MP th (prove(goal,tac))
  in th end;

val xSTACK_MOVE_EDI = let
  val (th,t_def) = decompilerLib.decompile
    prog_x86Lib.x86_tools "test" [QUOTE (x86_encodeLib.x86_encode "mov edi, [esp]")]
  val th = SIMP_RULE std_ss [t_def,LET_DEF] th
  val th = Q.INST [`df`|->`{esp}`,`f`|->`\x.w`] th
  val th = SPEC_BOOL_FRAME_RULE th ``ALIGNED esp``
  val post = ``xSTACK esp [w] * xR EDI w * xR ESP esp * xPC (p + 0x3w)``
  val (th,goal) = SPEC_WEAKEN_RULE th post
  val tac =
    SIMP_TAC std_ss [SEP_IMP_MOVE_COND,xSTACK_def,prog_x86Theory.xM_THM,
      ALIGNED,SEP_CLAUSES] THEN SIMP_TAC (std_ss++star_ss) [SEP_IMP_REFL]
  val th = MP th (prove(goal,tac))
  val pre = ``xSTACK esp [w] * ~xR EDI * xR ESP esp * xPC p``
  val (th,goal) = SPEC_STRENGTHEN_RULE th pre
  val tac =
    SIMP_TAC (std_ss++sep_cond_ss) [SEP_IMP_MOVE_COND,xSTACK_def,prog_x86Theory.xM_THM,
      ALIGNED,SEP_CLAUSES,SEP_IMP_REFL,IN_INSERT,NOT_IN_EMPTY]
    THEN SIMP_TAC (std_ss++star_ss) [ALIGNED_INTRO,ALIGNED,SEP_CLAUSES,SEP_IMP_REFL]
  val th = MP th (prove(goal,tac))
  in th end;

val xSTACK_POP_EDI = let
  val (th,t_def) = decompilerLib.decompile
    prog_x86Lib.x86_tools "test" [QUOTE (x86_encodeLib.x86_encode "pop edi")]
  val th = SIMP_RULE std_ss [t_def,LET_DEF] th
  val th = Q.INST [`df`|->`{esp}`,`f`|->`\x.w`] th
  val th = SPEC_BOOL_FRAME_RULE th ``ALIGNED esp``
  val post = ``xSTACK esp [w] * xR EDI w * xR ESP (esp+4w) * xPC (p + 0x1w)``
  val (th,goal) = SPEC_WEAKEN_RULE th post
  val tac =
    SIMP_TAC std_ss [SEP_IMP_MOVE_COND,xSTACK_def,prog_x86Theory.xM_THM,
      ALIGNED,SEP_CLAUSES] THEN SIMP_TAC (std_ss++star_ss) [SEP_IMP_REFL]
  val th = MP th (prove(goal,tac))
  val pre = ``xSTACK esp [w] * ~xR EDI * xR ESP esp * xPC p``
  val (th,goal) = SPEC_STRENGTHEN_RULE th pre
  val tac =
    SIMP_TAC (std_ss++sep_cond_ss) [SEP_IMP_MOVE_COND,xSTACK_def,prog_x86Theory.xM_THM,
      ALIGNED,SEP_CLAUSES,SEP_IMP_REFL,IN_INSERT,NOT_IN_EMPTY]
    THEN SIMP_TAC (std_ss++star_ss) [ALIGNED_INTRO,ALIGNED,SEP_CLAUSES,SEP_IMP_REFL]
  val th = MP th (prove(goal,tac))
  in th end;

val x86_sexp2string_th = let
  val th = SPEC_COMPOSE_RULE xSTACK_MOVE_EDI x86_sexp2string_thm
  val post = ``(let (eax,ecx,edi,esi,ebp,dh,h,df,f,dm,m,dg,g) =
             arm_print_sexp (eax,w,ebp,dh,h,df,f,dm,m,dg,g)
       in
         xBYTE_MEMORY df f * xBYTE_MEMORY dg g * xMEMORY dh h *
         xMEMORY dm m * xR EAX eax * xR EBP ebp * ~xR EBX * xR ECX ecx *
         ~xR EDX * xR ESI esi * ~xS) *
      (~xR EDI * xSTACK esp [w] * xR ESP esp * xPC p)``
  val post = subst_SPEC_PC th post
  val (th,goal) = SPEC_WEAKEN_RULE th post
  val tac =
    SIMP_TAC std_ss [LET_DEF]
    THEN CONV_TAC (DEPTH_CONV FORCE_PBETA_CONV)
    THEN SIMP_TAC (std_ss++sep_cond_ss) [Q.ISPEC `xR EDI` SEP_HIDE_def,SEP_CLAUSES]
    THEN SIMP_TAC std_ss [SEP_IMP_def]
    THEN CONV_TAC (REPEATC (DEPTH_CONV SEP_EXISTS_CONV))
    THEN REPEAT STRIP_TAC
    THEN Q.EXISTS_TAC `(FST
        (SND (SND (arm_print_sexp (eax,w,ebp,dh,h,df,f,dm,m,dg,g)))))`
    THEN FULL_SIMP_TAC std_ss [AC STAR_COMM STAR_ASSOC]
  val th = MP th (prove(goal,tac))
  val th = SPEC_COMPOSE_RULE th xSTACK_POP_EDI
  val th = RW [] (DISCH_ALL th)
  val imp = arm_print_sexp_lemma
  val imp = Q.INST [`r7`|->`r1`,`rest`|->`(dm,m,dg,g)`] imp
  val imp = SIMP_RULE std_ss [] (RW1 [one_space_EXPAND] imp)
  val imp = Q.INST [`c`|->`r1 + n2w (STRLEN (sexp2string t1) + 1)`] imp
  val imp = RW [] imp
  val tm = (fst o dest_imp o concl) imp
  val th = SPEC_BOOL_FRAME_RULE th tm
  val th = Q.INST [`eax`|->`w1`,`ebp`|->`r9`,`r1`|->`w`] th
  val post = ``SEP_EXISTS edi dg g dm m dh h. xR EDI edi * xSTRING edi (sexp2string t1)
         * xBYTE_MEMORY dg g * xMEMORY dh h * xMEMORY dm m *
         ~xR EAX * ~xR EBP * ~xR EBX * ~xR ECX * ~xR EDX * ~xR ESI
         * xPC p * ~xS * xSTACK esp [w] * xR ESP (esp + 0x4w)``
  val post = subst_SPEC_PC th post
  val (th,goal) = SPEC_WEAKEN_RULE th post
  val tac =
    SIMP_TAC std_ss [xSTRING_def]
    THEN SIMP_TAC std_ss [SEP_CLAUSES,SEP_IMP_MOVE_COND]
    THEN STRIP_TAC
    THEN IMP_RES_TAC imp
    THEN FULL_SIMP_TAC (std_ss++sep_cond_ss) [LET_DEF,WORD_OR_CLAUSES]
    THEN SIMP_TAC std_ss [SEP_IMP_def]
    THEN CONV_TAC (REPEATC (DEPTH_CONV SEP_EXISTS_CONV))
    THEN REPEAT STRIP_TAC
    THEN EX_TAC [`w`,`dg`,`g`,`dm`,`m`,`dh`,`hi`,`df`,`fi`]
    THEN IMP_RES_TAC one_string_IMP_string_mem
    THEN ASM_SIMP_TAC std_ss [cond_STAR]
    THEN SIMP_TAC (std_ss++sep_cond_ss) [Q.ISPEC `xR ECX` SEP_HIDE_def,SEP_CLAUSES]
    THEN CONV_TAC (REPEATC (DEPTH_CONV SEP_EXISTS_CONV))
    THEN EX_TAC [`r4i`]
    THEN SIMP_TAC (std_ss++sep_cond_ss) [Q.ISPEC `xR EAX` SEP_HIDE_def,SEP_CLAUSES]
    THEN CONV_TAC (REPEATC (DEPTH_CONV SEP_EXISTS_CONV))
    THEN EX_TAC [`w`]
    THEN SIMP_TAC (std_ss++sep_cond_ss) [Q.ISPEC `xR EBP` SEP_HIDE_def,SEP_CLAUSES]
    THEN CONV_TAC (REPEATC (DEPTH_CONV SEP_EXISTS_CONV))
    THEN EX_TAC [`r9`]
    THEN SIMP_TAC (std_ss++sep_cond_ss) [Q.ISPEC `xR ESI` SEP_HIDE_def,SEP_CLAUSES]
    THEN CONV_TAC (REPEATC (DEPTH_CONV SEP_EXISTS_CONV))
    THEN EX_TAC [`r8i`]
    THEN FULL_SIMP_TAC std_ss [AC STAR_ASSOC STAR_COMM]
  val th = MP th (prove(goal,tac))
  val th = foldr (uncurry EXISTS_PRE) th [`df`,`f`,`dg`,`g`,`dm`,`m`,`dh`,`h`,`sym`]
  val th = foldr (uncurry EXISTS_PRE) th [`t2`,`t3`,`t4`,`t5`,`t6`]
  val th = foldr (uncurry EXISTS_PRE) th [`w1`,`w2`,`w3`,`w4`,`w5`,`w6`,`r9`]
  val pre = ``xLISP1 (t1,l) * xSTRING_SPACE w (LENGTH (sexp2string t1)) *
              xPC p * ~xS * xSTACK esp [w] * xR ESP esp``
  val (th,goal) = SPEC_STRENGTHEN_RULE th pre
  val tac =
    SIMP_TAC std_ss [xSTRING_SPACE_def]
    THEN SIMP_TAC std_ss [SEP_CLAUSES,SEP_IMP_MOVE_COND]
    THEN SIMP_TAC std_ss [xLISP1_def,xLISP_def]
    THEN SIMP_TAC std_ss [SEP_CLAUSES,SEP_IMP_MOVE_COND]
    THEN SIMP_TAC std_ss [SEP_IMP_def]
    THEN CONV_TAC ((REDEPTH_CONV SEP_EXISTS_CONV))
    THEN SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,Once one_space_EXPAND]
    THEN NTAC 2 STRIP_TAC
    THEN EX_TAC [`r3'`,`r4'`,`r5'`,`r6'`,`r7'`,`r8'`,`a`]
    THEN EX_TAC [`x2`,`x3`,`x4`,`x5`,`x6`]
    THEN EX_TAC [`df`,`f`,`dg`,`g`,`dm`,`m`,`df'`,`f'`,`s'`]
    THEN IMP_RES_TAC imp
    THEN ASM_SIMP_TAC std_ss [LET_DEF,WORD_OR_CLAUSES]
    THEN SIMP_TAC (std_ss++sep_cond_ss) [Q.ISPEC `xR ESI` SEP_HIDE_def,SEP_CLAUSES]
    THEN CONV_TAC (REPEATC (DEPTH_CONV SEP_EXISTS_CONV))
    THEN EX_TAC [`r8'`]
    THEN SIMP_TAC (std_ss++sep_cond_ss) [Q.ISPEC `xR EDI` SEP_HIDE_def,SEP_CLAUSES]
    THEN CONV_TAC (REPEATC (DEPTH_CONV SEP_EXISTS_CONV))
    THEN EX_TAC [`r7'`]
    THEN SIMP_TAC (std_ss++sep_cond_ss) [Q.ISPEC `xR EBX` SEP_HIDE_def,SEP_CLAUSES]
    THEN CONV_TAC (REPEATC (DEPTH_CONV SEP_EXISTS_CONV))
    THEN EX_TAC [`r6'`]
    THEN SIMP_TAC (std_ss++sep_cond_ss) [Q.ISPEC `xR EDX` SEP_HIDE_def,SEP_CLAUSES]
    THEN CONV_TAC (REPEATC (DEPTH_CONV SEP_EXISTS_CONV))
    THEN EX_TAC [`r5'`]
    THEN SIMP_TAC (std_ss++sep_cond_ss) [Q.ISPEC `xR ECX` SEP_HIDE_def,SEP_CLAUSES]
    THEN CONV_TAC (REPEATC (DEPTH_CONV SEP_EXISTS_CONV))
    THEN EX_TAC [`r4'`]
    THEN FULL_SIMP_TAC std_ss [AC STAR_ASSOC STAR_COMM]
  val th = MP th (prove(goal,tac))
  in th end;

val R_ev_thm = let
  val rw = RW [] (MATCH_MP SET_TO_LIST_THM FINITE_EMPTY)
  val thi = Q.SPECL [`s`,`FEMPTY`,`t`,`l`] LISP_EVAL_CORRECT
  val thi = CONJ thi (Q.SPECL [`s`,`FEMPTY`,`t`,`l`] LISP_EVAL_LIMIT_CORRECT)
  val thi = SIMP_RULE std_ss [rw,fmap2list_def,FDOM_FEMPTY,MAP,alist2sexp_def,list2sexp_def,LISP_EVAL_def] thi
  in thi end;

fun auto_prove th post = let
  val th = Q.INST [`x`|->`Sym "nil"`] th
  val th = Q.INST [`y`|->`Sym "nil"`] th
  val th = Q.INST [`z`|->`Sym "nil"`] th
  val th = Q.INST [`stack`|->`Sym "nil"`] th
  val th = Q.INST [`alist`|->`Sym "nil"`] th
  val post = subst_SPEC_PC th post
  val th = SPEC_BOOL_FRAME_RULE th ``R_ev (s,FEMPTY) s2 /\ (exp = term2sexp s)``
  val (th,goal) = SPEC_WEAKEN_RULE th post
  val tac =
    SIMP_TAC std_ss [LISP_EVAL_def,aLISP1_def,pLISP1_def,xLISP1_def]
    THEN `?exp2 x2 y2 z2 stack2 alist2 l2.
       lisp_eval (exp,Sym "nil",Sym "nil",Sym "nil",Sym "nil",Sym "nil",l) =
       (exp2,x2,y2,z2,stack2,alist2,l2)` by METIS_TAC [pairTheory.PAIR]
    THEN ASM_SIMP_TAC std_ss [LET_DEF,SEP_IMP_def,cond_STAR]
    THEN SIMP_TAC std_ss [SEP_CLAUSES]
    THEN CONV_TAC (REPEATC (DEPTH_CONV SEP_EXISTS_CONV))
    THEN REPEAT STRIP_TAC
    THEN EX_TAC [`x2`,`y2`,`z2`,`stack2`,`alist2`]
    THEN FULL_SIMP_TAC std_ss []
    THEN MP_TAC (Q.INST [`t`|->`s2`] R_ev_thm)
    THEN ASM_SIMP_TAC std_ss []
    THEN REPEAT STRIP_TAC
    THEN FULL_SIMP_TAC std_ss []
  val th = MP th (prove(goal,tac))
  in th end;

val arm_th = auto_prove SPEC_lisp_eval_arm_thm
  ``aLISP1 (sexpression2sexp s2,l) * aPC p * ~aS``

val ppc_th = auto_prove SPEC_lisp_eval_ppc_thm
  ``pLISP1 (sexpression2sexp s2,l) * pPC p * ~pS``

val x86_th = auto_prove SPEC_lisp_eval_x86_thm
  ``xLISP1 (sexpression2sexp s2,l) * xPC p * ~xS``

val _ = codegen_x86Lib.set_x86_regs
  [(3,"eax"),(4,"ecx"),(5,"edx"),(6,"ebx"),(7,"edi"),(8,"esi")]

val (th1,th2,th3) = compilerLib.compile_all ``
  add32 (r5:word32) = let r5 = r5 + 32w in r5``;

val setup_code =
  map (fn (s,th) => (s,SIMP_RULE std_ss [th2,th3,LET_DEF,SEP_CLAUSES] th)) th1

fun find_thm t [] = fail()
  | find_thm t ((s,th)::xs) = if t = s then th else find_thm t xs

val arm_eval_th = LISP_SPEC_COMPOSE_RULE
  [find_thm "arm" setup_code,
   arm_string2sexp_arm_thm,
   arm_th,
   arm_sexp2string_th]

val ppc_eval_th = LISP_SPEC_COMPOSE_RULE
  [find_thm "ppc" setup_code,
   arm_string2sexp_ppc_thm,
   ppc_th,
   ppc_sexp2string_th]

val x86_eval_th = LISP_SPEC_COMPOSE_RULE
  [find_thm "x86" setup_code,
   xSTACK_PUSH_EDI,
   arm_string2sexp_x86_thm,
   x86_th,
   Q.INST [`w`|->`edi`,`esp`|->`esp-4w`] x86_sexp2string_th]


val _ = save_thm("arm_eval_th",arm_eval_th);
val _ = save_thm("ppc_eval_th",ppc_eval_th);
val _ = save_thm("x86_eval_th",x86_eval_th);

open export_codeLib;

val _ = write_code_to_file "arm_eval.s" arm_eval_th
val _ = write_code_to_file "ppc_eval.s" ppc_eval_th
val _ = write_code_to_file "x86_eval.s" x86_eval_th

val _ = export_theory();
