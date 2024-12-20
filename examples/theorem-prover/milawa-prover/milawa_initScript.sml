open HolKernel boolLib bossLib Parse; val _ = new_theory "milawa_init";
val _ = ParseExtras.temp_loose_equality()

open lisp_extractLib lisp_extractTheory;

open stringTheory finite_mapTheory pred_setTheory listTheory sumTheory;
open optionTheory arithmeticTheory relationTheory;

open lisp_sexpTheory lisp_semanticsTheory lisp_parseTheory;

open milawa_coreTheory;
val _ = max_print_depth := 20;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;



(* Reading in the top-level definitions from the Milawa core *)

val (R_aux_exec_rules,R_aux_exec_ind,R_aux_exec_cases) = Hol_reln `
 (!fns io.
    R_aux_exec ([],fns,io) (io,T))
  /\
 (!xs fns io exp s fns2 io2 ok2 io3 ok3.
    R_ev (sexp2term exp,FEMPTY,fns,io,T) (s,fns2,io2,ok2) /\
    R_aux_exec (xs,fns2,io2 ++ sexp2string s ++ "\n") (io3,ok3) ==>
    R_aux_exec (exp::xs,fns,io) (io3,ok2 /\ ok3))`;

val R_aux_exec_IMP_R_exec = prove(
  ``!p q. R_aux_exec p q ==>
          !str. (FST p = read_sexps str) ==> R_exec (str,SND p) q``,
  HO_MATCH_MP_TAC R_aux_exec_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [read_sexps_def]
  \\ Cases_on `is_eof str`
  \\ Cases_on `sexp_parse_stream r`
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  THEN1 METIS_TAC [R_exec_cases]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ ONCE_REWRITE_TAC [R_exec_cases] \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC []);

val PULL_EXISTS_CONJ = METIS_PROVE []
  ``(p /\ (?x. q x) = ?x. p /\ q x) /\ ((?x. q x) /\ p = ?x. q x /\ p)``

val R_aux_exec6 = prove(
  ``R_ev (sexp2term x1,FEMPTY,fns1,io1,T) (ans1,fns2,io2',ok2) /\
    (io2 = io2' ++ sexp2string ans1 ++ "\n") /\
    R_ev (sexp2term x2,FEMPTY,fns2,io2,T) (ans2,fns3,io3',ok3) /\
    (io3 = io3' ++ sexp2string ans2 ++ "\n") /\
    R_ev (sexp2term x3,FEMPTY,fns3,io3,T) (ans3,fns4,io4',ok4) /\
    (io4 = io4' ++ sexp2string ans3 ++ "\n") /\
    R_ev (sexp2term x4,FEMPTY,fns4,io4,T) (ans4,fns5,io5',ok5) /\
    (io5 = io5' ++ sexp2string ans4 ++ "\n") /\
    R_ev (sexp2term x5,FEMPTY,fns5,io5,T) (ans5,fns6,io6',ok6) /\
    (io6 = io6' ++ sexp2string ans5 ++ "\n") /\
    R_ev (sexp2term x6,FEMPTY,fns6,io6,T) (ans6,fns7,io7',ok7) /\
    (io7 = io7' ++ sexp2string ans6 ++ "\n") ==>
    R_aux_exec ([x1;x2;x3;x4;x5;x6],fns1,io1) (io7,ok2 /\ ok3 /\ ok4 /\ ok5 /\ ok6 /\ ok7)``,
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
  \\ NTAC 8 (ONCE_REWRITE_TAC [R_aux_exec_cases] \\ SIMP_TAC (srw_ss()) [])
  \\ REPEAT STRIP_TAC \\ SIMP_TAC std_ss [PULL_EXISTS_CONJ]
  \\ Q.LIST_EXISTS_TAC [`ans1`,`fns2`,`io2'`,`ok2`]
  \\ Q.LIST_EXISTS_TAC [`ans2`,`fns3`,`io3'`,`ok3`]
  \\ Q.LIST_EXISTS_TAC [`ans3`,`fns4`,`io4'`,`ok4`]
  \\ Q.LIST_EXISTS_TAC [`ans4`,`fns5`,`io5'`,`ok5`]
  \\ Q.LIST_EXISTS_TAC [`ans5`,`fns6`,`io6'`,`ok6`]
  \\ Q.LIST_EXISTS_TAC [`ok7`,`ans6`,`fns7`,`io7'`]
  \\ ASM_SIMP_TAC std_ss []) |> GEN_ALL;

val list2sexp_11 = prove(
  ``!xs ys. (list2sexp xs = list2sexp ys) = (xs = ys)``,
  Induct \\ Cases_on `ys` \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss []);

val MAP_Sym_11 = prove(
  ``!xs ys. (MAP Sym xs = MAP Sym ys) = (xs = ys)``,
  Induct \\ Cases_on `ys` \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss []);

val sexp2list_list2sexp = prove(
  ``!xs. sexp2list (list2sexp xs) = xs``,
  Induct \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss []);

val MAP_getSym_MAP_Sym = prove(
  ``!xs. MAP getSym (MAP Sym xs) = xs``,
  Induct \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss []);

val R_ev_App_Define = prove(
  ``!params.
      R_ev (App Define [Const (Sym name); Const (list2sexp (MAP Sym params)); Const body],FEMPTY,fns,io,T)
         (ans,fns1,io1,ok1) =
      (ans = Sym "NIL") /\ (fns1 = add_def fns (name,params,sexp2term body)) /\
      (io1 = io) /\ (ok1 = ~(name IN FDOM fns))``,
  NTAC 5 (ONCE_REWRITE_TAC [R_ev_cases]
          \\ SIMP_TAC (srw_ss()) [list2sexp_11,MAP_Sym_11,getSym_def,sexp2list_list2sexp,MAP_getSym_MAP_Sym]));

val R_ev_App_Define_CLAUSES =
  LIST_CONJ [Q.SPEC `[]` R_ev_App_Define,
             Q.SPEC `[x1]` R_ev_App_Define,
             Q.SPEC `[x1;x2]` R_ev_App_Define,
             Q.SPEC `[x1;x2;x3]` R_ev_App_Define,
             Q.SPEC `[x1;x2;x3;x4]` R_ev_App_Define,
             Q.SPEC `[x1;x2;x3;x4;x5]` R_ev_App_Define] |> RW [list2sexp_def,MAP]

fun list_dest f tm = let val (x,y) = f tm in list_dest f x @ list_dest f y end
                     handle HOL_ERR _ => [tm];

fun REWRITE_EQS th = let
  val tm = fst (dest_imp (concl th))
  fun dest_var_eq tm = let val (x,y) = dest_eq tm
                           val _ = x !~ y orelse fail()
                           val _ = is_var x orelse fail() in (x,y) end
  val (v,exp) = dest_eq (first (can dest_var_eq) (list_dest dest_conj tm))
  in REWRITE_EQS (INST [v|->exp] th) end handle HOL_ERR _ => th

val (MILAWA_CORE_SEXP_thm,MILAWA_INIT_def) = let
  val tm = concl MILAWA_CORE_SEXP_def
  val tm = find_term (can (match_term ``Dot (Dot (Sym "NOT") x) y``)) tm
  val MILAWA_INIT_def = zDefine `MILAWA_INIT = ^tm`
  in (RW [GSYM MILAWA_INIT_def] MILAWA_CORE_SEXP_def,MILAWA_INIT_def) end

val IN_FDOM_add_def = prove(
  ``z IN FDOM (add_def k (x,y)) = (z = x) \/ z IN FDOM k``,
  SIMP_TAC std_ss [add_def_def,FUNION_DEF,IN_UNION,FDOM_FUPDATE,
    FDOM_FEMPTY,IN_INSERT,NOT_IN_EMPTY] \\ METIS_TAC []);

val (init_fns_def,init_th) = let
  val _ = print "."
  val rw = ASSUME ``read_sexps rest = [Dot (Sym "MILAWA-MAIN") (Dot (Dot (Sym "QUOTE") (Dot x (Sym "NIL"))) (Sym "NIL"))]``
  val th = RW [rw] (SPEC_ALL MILAWA_CORE_SEXP_thm)
  val xs = th |> concl |> rand |> listSyntax.dest_list |> fst
  val _ = print "."
  val th = foldr (uncurry SPEC) R_aux_exec6 xs |> RW [GSYM MILAWA_CORE_SEXP_thm]
  val _ = print "."
  val tms = find_terms (can (match_term ``sexp2term x``)) (concl th)
  val _ = print "."
  val th = RW1 (map (fn t => (print "."; EVAL t)) tms) th
  val _ = print "."
  val th = RW [R_ev_App_Define_CLAUSES,GSYM CONJ_ASSOC,AND_IMP_INTRO] (SPEC_ALL th)
  val _ = print "."
  val tms = find_terms (can (match_term ``sexp2term x``)) (concl th)
  val _ = print "."
  val th = RW1 (map (fn t => (print "."; EVAL t)) tms) th
  val _ = print "."
  val th = RW [FDOM_FUPDATE,IN_INSERT,EVAL ``sexp2string (Sym "NIL")``,APPEND,GSYM APPEND_ASSOC] (REWRITE_EQS th)
  val _ = print "."
  val th = Q.INST [`fns1`|->`FEMPTY`] th
  val th = SIMP_RULE (srw_ss()) [] (UNDISCH th)
  val _ = print "."
  val th = MATCH_MP R_aux_exec_IMP_R_exec th
  val _ = print "."
  val th = Q.SPEC `MILAWA_CORE_TEXT ++ rest` (RW [] th)
  val th = RW [RW [rw] (SPEC_ALL MILAWA_CORE_SEXP_thm)] th
  val _ = print "."
  val th = DISCH_ALL th
  val _ = print "."
  val x = find_term (can (match_term ``add_def fns1 qqq``)) (concl th)
  val _ = print ".\n"
  val init_fns_def = Define `init_fns = ^x`
  val th = RW1 [GSYM init_fns_def] th
  val th = SIMP_RULE (srw_ss()) [IN_FDOM_add_def] th
  in (init_fns_def,th) end

val milawa_init_expanded = let
  val th = init_th
    |> RW1 [MILAWA_INIT_def]
    |> RW [MILAWA_CORE_TEXT_THM,MILAWA_CORE_SEXP_def,CONS_11,CAR_def]
    |> GSYM
  val tm = th |> concl |> dest_imp |> fst
  val lemma =
    (ONCE_REWRITE_CONV [R_ev_cases] THENC
     SIMP_CONV (srw_ss()) [] THENC
     SIMP_CONV std_ss [Once R_ev_cases] THENC
     SIMP_CONV (srw_ss()) [] THENC
     SIMP_CONV std_ss [Once R_ev_cases] THENC
     SIMP_CONV (srw_ss()) [] THENC
     SIMP_CONV std_ss [Once R_ev_cases] THENC
     SIMP_CONV (srw_ss()) []) tm
  in RW [lemma] th end

val _ = save_thm("milawa_init_expanded",milawa_init_expanded);


(* extract functions for Milawa's top-level definitions *)

val xs = concl init_fns_def
         |> find_terms (can (match_term ``add_def x (y:'a # 'b)``))
         |> map rand |> (fn tms => listSyntax.mk_list(tms,type_of (hd tms)))

val init_assum_def = Define `init_assum k = fns_assum k ^xs`
val init_assum_thm = store_thm("init_assum_thm",
  ``init_assum init_fns``,
  EVAL_TAC \\ SRW_TAC [] [FUNION_DEF]);

val _ = install_assum_eq init_assum_def


val name = "LOOKUP-SAFE"
val term_tac = SOME
 (WF_REL_TAC `measure (LSIZE o SND)`
  \\ FULL_SIMP_TAC std_ss [lisp_extractTheory.isTrue_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [isDot_thm] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LSIZE_def,CDR_def] \\ DECIDE_TAC)
val lookup_safe_def = pure_extract name term_tac

val name = "DEFINE-SAFE"
val term_tac = NONE
val define_safe_def = impure_extract name term_tac

val name = "DEFINE-SAFE-LIST"
val term_tac = SOME
 (WF_REL_TAC `measure (LSIZE o FST o SND)`
  \\ FULL_SIMP_TAC std_ss [lisp_extractTheory.isTrue_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [isDot_thm] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LSIZE_def,CDR_def] \\ DECIDE_TAC)
val define_safe_list_def = impure_extract name term_tac

val name = "MILAWA-INIT"
val term_tac = NONE
val milawa_init_def = impure_extract name term_tac


val define_safe_list_side_thm = store_thm("define_safe_list_side_thm",
  ``!ftbl defs k io ok. define_safe_list_side ftbl defs k io ok = T``,
  Induct_on `defs` \\ SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [fetch "-" "define_safe_list_side_def"]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,fetch "-" "define_safe_side_def",
       isTrue_CLAUSES,isDot_def,CDR_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ SIMP_TAC std_ss []);

val milawa_init_side_thm = store_thm("milawa_init_side_thm",
  ``!k io ok. milawa_init_side k io ok = T``,
  SIMP_TAC std_ss [fetch "-" "milawa_init_side_def",
    define_safe_list_side_thm]);



val define_safe_thm = prove(
  ``define_safe ftbl name formals body k io ok =
     if isTrue (lookup_safe name ftbl) then
       if lookup_safe name ftbl =
          LISP_CONS name (LISP_CONS formals (LISP_CONS body (Sym "NIL")))
       then (ftbl,k,io,ok)
       else (Sym "NIL",k,STRCAT
       (STRCAT io
          (sexp2string
             (list2sexp
                [Sym "ERROR";
                 LISP_CONS (Sym "REDEFINITION-ERROR")
                   (LISP_CONS (lookup_safe name ftbl)
                      (LISP_CONS
                         (LISP_CONS name
                            (LISP_CONS formals
                               (LISP_CONS body (Sym "NIL"))))
                         (Sym "NIL")))]))) "\n",F)
     else
       (LISP_CONS
          (LISP_CONS name
             (LISP_CONS formals (LISP_CONS body (Sym "NIL")))) ftbl,
        add_def k
          (getSym name,MAP getSym (sexp2list formals),sexp2term body),
        io,ok /\ getSym name NOTIN FDOM k)``,
  SIMP_TAC std_ss [Once define_safe_def,LET_DEF,isTrue_CLAUSES]
  \\ SRW_TAC [] [] \\ METIS_TAC []);


val FDOM_init_fns = prove(
  ``FDOM init_fns = {"MILAWA-MAIN";"MILAWA-INIT";"DEFINE-SAFE";"DEFINE-SAFE-LIST";"LOOKUP-SAFE"}``,
  SRW_TAC [] [init_fns_def,EXTENSION,FUNION_DEF,add_def_def] \\ METIS_TAC []);

val lookup_safe_lemma1 = RW [isTrue_CLAUSES] lookup_safe_def
val lookup_safe_lemma2 = lookup_safe_lemma1 |> Q.INST [`x`|->`Sym t`] |> RW [isDot_def]
val lookup_safe_lemma3 = lookup_safe_lemma1
   |> Q.INST [`x`|->`Dot (Dot (Sym s) y) z`,`a`|->`Sym t`]
   |> RW [isDot_def,CAR_def,CDR_def,SExp_11]

val lookup_safe_conv =
  REPEATC
  (REWR_CONV lookup_safe_lemma2
   ORELSEC
   (REWR_CONV lookup_safe_lemma3 THENC
    (RATOR_CONV o RATOR_CONV o RAND_CONV) EVAL THENC
    COND_CONV))

val define_safe_conv_lemma = SPEC_ALL define_safe_thm |> RW [LISP_CONS_def]

fun define_safe_conv tm = let
  val str = tm |> rator |> rator |> rator |> rator  |> rator |> rand
               |> rand |> stringSyntax.fromHOLstring
  val _ = print "define_safe_conv: "
  val _ = print str
  val _ = print "\n"
  val result =
     (REWR_CONV define_safe_conv_lemma THENC
      (RATOR_CONV o RATOR_CONV o RAND_CONV o RAND_CONV) lookup_safe_conv THENC
      (RATOR_CONV o RATOR_CONV o RAND_CONV) EVAL THENC
      COND_CONV THENC
      (RAND_CONV o RATOR_CONV o RAND_CONV o RAND_CONV) EVAL) tm
  in result end

val define_safe_list_conv_lemma = prove(
  ``define_safe_list ftbl (Dot (Dot name (Dot params (Dot body z))) y) k io T =
    (\(ftbl',k',io',ok'). define_safe_list ftbl' y k' io' ok')
      (define_safe ftbl name params body k io T)``,
  SIMP_TAC std_ss [Once define_safe_list_def]
  \\ FULL_SIMP_TAC std_ss [isDot_def,CAR_def,LET_DEF,FIRST_def,SECOND_def,
       THIRD_def,CDR_def,isTrue_CLAUSES]
  \\ Cases_on `define_safe ftbl name params body k io ok`
  \\ FULL_SIMP_TAC std_ss []
  \\ CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV))
  \\ FULL_SIMP_TAC std_ss []);

val define_safe_list_conv_lemma_nil =
  define_safe_list_def
  |> Q.INST [`defs`|->`Sym t`,`ok`|->`ok`]
  |> SIMP_RULE std_ss [isDot_def,isTrue_CLAUSES]

fun define_safe_list_conv tm =
  (REWR_CONV define_safe_list_conv_lemma THENC
   RAND_CONV define_safe_conv THENC
   PairRules.PBETA_CONV THENC
   RAND_CONV (REWRITE_CONV [getSym_def,IN_FDOM_add_def,FDOM_init_fns]
              THENC SIMP_CONV (srw_ss()) [])) tm


local
  val milawa_init_lemma = let
    val tm = milawa_init_def |> RW [MILAWA_INIT_def] |> SPEC_ALL
             |> Q.INST [`k`|->`init_fns`,`ok`|->`T`] |> RW [init_fns_def] |> concl |> rand
    in (REPEATC define_safe_list_conv THENC
        TRY_CONV (REWR_CONV define_safe_list_conv_lemma_nil)) tm end
  val dest_tuple = list_dest pairSyntax.dest_pair
  val tms =  milawa_init_lemma |> concl |> rand |> dest_tuple
in
  val init_ftbl_def = Define `init_ftbl = ^(el 1 tms)`;
  val core_funs_def = Define `core_funs = ^(el 2 tms)`;
  val milawa_init_evaluated =
    RW1 [GSYM init_ftbl_def,GSYM core_funs_def,GSYM MILAWA_INIT_def] milawa_init_lemma
    |> RW [GSYM init_fns_def,GSYM milawa_init_def]
end

val _ = save_thm("milawa_init_evaluated",milawa_init_evaluated);


(* construct fns_assum for all core functions *)

val fns_assum_add_def = prove(
  ``~(n IN FDOM k) /\ fns_assum k xs ==>
    fns_assum (add_def k (n,ps,body)) ((n,ps,body)::xs)``,
  FULL_SIMP_TAC (srw_ss()) [fns_assum_def,EVERY_DEF,add_def_def,FUNION_DEF,
    EVERY_MEM,IN_UNION,FDOM_FUPDATE,pairTheory.FORALL_PROD] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []);

val (list_of_defs_tm,core_fun_names) = let
  val tm = core_funs_def |> RW [init_fns_def] |> concl |> rand
  fun foo tm =
    if can (match_term ``add_def x (y:'a # 'b)``) tm then
      rand tm :: foo (rand (rator tm)) else []
  val xs = foo tm
  val core_fun_names = rev (map (stringSyntax.fromHOLstring o rand o rator) xs)
                       |> tl |> tl |> tl |> tl |> tl
  val list_of_defs_tm = listSyntax.mk_list(xs,type_of (hd xs))
  in (list_of_defs_tm,core_fun_names) end

val core_assum_def = Define `core_assum k = fns_assum k ^list_of_defs_tm`;
val core_assum_thm = store_thm("core_assum_thm",
  ``core_assum core_funs``,
  REWRITE_TAC [init_fns_def,core_funs_def,core_assum_def]
  \\ REPEAT
    (MATCH_MP_TAC fns_assum_add_def
     \\ STRIP_TAC THEN1
         (REWRITE_TAC [IN_FDOM_add_def]
          \\ CONV_TAC (DEPTH_CONV stringLib.string_EQ_CONV)
          \\ REWRITE_TAC [] \\ SIMP_TAC (srw_ss()) []))
  \\ SIMP_TAC std_ss [fns_assum_def,EVERY_DEF]);


val _ = export_theory();
