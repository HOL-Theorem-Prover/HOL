
open HolKernel Parse boolLib bossLib; val _ = new_theory "milawa_proofp";

open lisp_sexpTheory lisp_semanticsTheory lisp_extractTheory;
open milawa_defsTheory milawa_logicTheory milawa_execTheory;

open arithmeticTheory listTheory pred_setTheory finite_mapTheory combinTheory;
open pairTheory;

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1
val bool_ss = bool_ss -* ["lift_disj_eq", "lift_imp_disj"]
val std_ss = std_ss -* ["lift_disj_eq", "lift_imp_disj", "NOT_LT_ZERO_EQ_ZERO"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]


val rw = ref (tl [TRUTH]);

fun add_rw th = (rw := th::(!rw); th);
fun add_rws thms = (rw := thms @ (!rw));
val add_prove = add_rw o prove

val LISP_TEST_THM = prove(
  ``!b. (isTrue (LISP_TEST b) = b) /\
        ((LISP_TEST b = Sym "NIL") = ~b) /\ ((LISP_TEST b = Sym "T") = b)``,
  Cases \\ FULL_SIMP_TAC std_ss [] \\ EVAL_TAC);

val _ = add_rws [isTrue_CLAUSES,
  CDR_def,CAR_def,getVal_def,SExp_11,SExp_distinct,
  isDot_def,isVal_def,isSym_def,LISP_ADD_def,LISP_SUB_def,list2sexp_def,MEM,
  EVAL ``LISP_TEST F``,EVAL ``LISP_TEST T``,LISP_CONS_def,LISP_TEST_THM,
  FIRST_def,SECOND_def,
  THIRD_def,FOURTH_def,
  FIFTH_def,NOT_CONS_NIL]

fun SS thms = SIMP_TAC std_ss (thms @ !rw)
fun FS thms = FULL_SIMP_TAC std_ss (thms @ !rw)
fun SR thms = SIMP_RULE std_ss (thms @ !rw)


(* various auxilliary functions *)

val alist2sexp_def = (add_rw o Define) `
  (alist2sexp [] = Sym "NIL") /\
  (alist2sexp ((x,y)::xs) = Dot (Dot x y) (alist2sexp xs))`;

val isTrue_not = add_prove(
  ``!x. isTrue (not x) = ~(isTrue x)``,
  SIMP_TAC std_ss [not_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `isTrue x` \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC);

val nfix_thm = add_prove(
  ``!x. nfix x = Val (getVal x)``,
  Cases \\ EVAL_TAC);

val less_eq_thm = add_prove(
  ``!x y. less_eq x y = LISP_TEST (getVal x <= getVal y)``,
  Cases \\ Cases \\ EVAL_TAC \\ SIMP_TAC std_ss [GSYM NOT_LESS]
  \\ Cases_on `0 < n` \\ ASM_SIMP_TAC std_ss [DECIDE ``(n = 0) = ~(0<n:num)``]
  \\ Cases_on `n'<n` \\ FULL_SIMP_TAC std_ss []);

val len_thm = add_prove(
  ``!xs. len (list2sexp xs) = Val (LENGTH xs)``,
  Induct THEN1 EVAL_TAC
  \\ SIMP_TAC std_ss [list2sexp_def]
  \\ ONCE_REWRITE_TAC [len_def]
  \\ FS [LENGTH,ADD1,AC ADD_COMM ADD_ASSOC]);

val memberp_thm = add_prove(
  ``!xs a. memberp a (list2sexp xs) = LISP_TEST (MEM a xs)``,
  Induct \\ ONCE_REWRITE_TAC [memberp_def] \\ FS []
  \\ SRW_TAC [] [LISP_EQUAL_def] \\ FS []);

val uniquep_thm = add_prove(
  ``!xs. uniquep (list2sexp xs) = LISP_TEST (ALL_DISTINCT xs)``,
  Induct \\ ONCE_REWRITE_TAC [uniquep_def] \\ FS [ALL_DISTINCT]
  \\ STRIP_TAC \\ Cases_on `MEM h xs` \\ FS []);

val list_fix_thm = add_prove(
  ``!xs. list_fix (list2sexp xs) = list2sexp xs``,
  Induct \\ ONCE_REWRITE_TAC [list_fix_def] \\ FS []);

val app_thm = add_prove(
  ``!xs ys. app (list2sexp xs) (list2sexp ys) = list2sexp (xs ++ ys)``,
  Induct \\ ONCE_REWRITE_TAC [app_def] \\ FS [APPEND]);

val rev_thm = add_prove(
  ``!xs. rev (list2sexp xs) = list2sexp (REVERSE xs)``,
  Induct \\ ONCE_REWRITE_TAC [rev_def] \\ FS [REVERSE_DEF]
  \\ FULL_SIMP_TAC std_ss [GSYM list2sexp_def,app_thm]);

val true_listp_thm = add_prove(
  ``!xs. true_listp (list2sexp xs) = Sym "T"``,
  Induct \\ ONCE_REWRITE_TAC [true_listp_def] \\ FS [LISP_EQUAL_def]);

val isTrue_true_listp = add_prove(
  ``!x. isTrue (true_listp x) = ?xs. x = list2sexp xs``,
  REVERSE (REPEAT STRIP_TAC \\ EQ_TAC) THEN1 (REPEAT STRIP_TAC \\ FS [])
  \\ REVERSE (Induct_on `x`) \\ ONCE_REWRITE_TAC [true_listp_def] \\ FS []
  THEN1 (Q.EXISTS_TAC `[]` \\ FS [])
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ Q.EXISTS_TAC `x::xs` \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss []);

val isTrue_zp = add_prove(
  ``!x. isTrue (zp x) = (getVal x = 0)``,
  Cases \\ EVAL_TAC \\ SRW_TAC [] []);

val subset_thm = add_prove(
  ``!xs ys. subsetp (list2sexp xs) (list2sexp ys) =
            LISP_TEST (set xs SUBSET set ys)``,
  Induct \\ ONCE_REWRITE_TAC [subsetp_def]
  \\ FS [LIST_TO_SET_THM,EMPTY_SUBSET,INSERT_SUBSET] \\ REPEAT STRIP_TAC
  \\ Cases_on `MEM h ys` \\ FS []);

val list_exists_def = Define `
  list_exists n x = ?xs. (LENGTH xs = n) /\ (x = list2sexp xs)`;

val tuplep_thm = add_prove(
  ``!x n. tuplep n x = LISP_TEST (list_exists (getVal n) x)``,
  SIMP_TAC std_ss [list_exists_def]
  \\ Induct_on `getVal n` \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ONCE_REWRITE_TAC [tuplep_def] \\ FS [LENGTH_NIL,LISP_EQUAL_def,ADD1]
  \\ REPEAT STRIP_TAC \\ Cases_on `isDot x` \\ FS [] THEN1
   (AP_TERM_TAC \\ FS [isDot_thm] \\ EQ_TAC \\ REPEAT STRIP_TAC
    THEN1 (Cases_on `xs` \\ FS [LENGTH,ADD1] \\ Q.EXISTS_TAC `t` \\ FS [LENGTH])
    THEN1 (Q.EXISTS_TAC `a::xs` \\ FS [LENGTH,ADD1]))
  \\ CCONTR_TAC \\ FS [] \\ Cases_on `xs` \\ FS [LENGTH]);

val tuple_listp_thm = add_prove(
  ``!xs n. tuple_listp n (list2sexp xs) =
           LISP_TEST (EVERY (list_exists (getVal n)) xs)``,
  Induct \\ ONCE_REWRITE_TAC [tuple_listp_def] \\ FS [EVERY_DEF]
  \\ REPEAT STRIP_TAC \\ Cases_on `list_exists (getVal n) h` \\ FS []);

val list_exists_simp = add_prove(
  ``(list_exists n (Val k) = F) /\
    (list_exists n (Sym s) = (n = 0) /\ (s = "NIL")) /\
    (list_exists n (Dot x y) = list_exists (n-1) y /\ 0 < n)``,
  SIMP_TAC std_ss [list_exists_def]
  \\ REPEAT STRIP_TAC \\ REPEAT EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (Cases_on `xs` \\ FS [LENGTH])
  THEN1 (Cases_on `xs` \\ FS [LENGTH])
  THEN1 (Cases_on `xs` \\ FS [LENGTH])
  THEN1 (FS [LENGTH_NIL])
  THEN1 (Cases_on `xs` \\ FS [LENGTH] \\ Q.EXISTS_TAC `t` \\ FS [] \\ DECIDE_TAC)
  THEN1 (Cases_on `xs` \\ FS [LENGTH] \\ DECIDE_TAC)
  THEN1 (Q.EXISTS_TAC `x::xs` \\ FS [LENGTH] \\ DECIDE_TAC));

val remove_all_thm = add_prove(
  ``!xs a. remove_all a (list2sexp xs) = list2sexp (FILTER (\x. ~(x = a)) xs)``,
  Induct \\ ONCE_REWRITE_TAC [remove_all_def] \\ FS [FILTER]
  \\ REPEAT STRIP_TAC \\ Cases_on `h = a` \\ FS []);

val remove_duplicates_thm = add_prove(
  ``!xs. remove_duplicates (list2sexp xs) =
         list2sexp (REMOVE_DUPLICATES xs)``,
  Induct \\ ONCE_REWRITE_TAC [remove_duplicates_def]
  \\ FS [REMOVE_DUPLICATES_def] \\ Cases_on `MEM h xs` \\ FS []);

val difference_thm = add_prove(
  ``!xs ys. difference (list2sexp xs) (list2sexp ys) =
            list2sexp (FILTER (\x. ~MEM x ys) xs)``,
  Induct \\ ONCE_REWRITE_TAC [difference_def] \\ FS [FILTER]
  \\ REPEAT STRIP_TAC \\ Cases_on `MEM h ys` \\ FS []);

val strip_firsts_thm = add_prove(
  ``!xs. strip_firsts (list2sexp xs) = list2sexp (MAP CAR xs)``,
  Induct \\ ONCE_REWRITE_TAC [strip_firsts_def] \\ FS [MAP]);

val strip_seconds_thm = add_prove(
  ``!xs. strip_seconds (list2sexp xs) = list2sexp (MAP (CAR o CDR) xs)``,
  Induct \\ ONCE_REWRITE_TAC [strip_seconds_def] \\ FS [MAP]);

val CONS_ZIP_def = Define `
  (CONS_ZIP [] [] = []) /\
  (CONS_ZIP [] (y::ys) = []) /\
  (CONS_ZIP (x::xs) [] = (LISP_CONS x (Sym "NIL")) :: CONS_ZIP xs []) /\
  (CONS_ZIP (x::xs) (y::ys) = (LISP_CONS x y) :: CONS_ZIP xs ys)`;

val pair_lists_thm = add_prove(
  ``!xs ys. pair_lists (list2sexp xs) (list2sexp ys) = list2sexp (CONS_ZIP xs ys)``,
  Induct \\ Cases_on `ys` \\ ONCE_REWRITE_TAC [pair_lists_def] \\ FS [CONS_ZIP_def]
  \\ ASM_SIMP_TAC std_ss [GSYM list2sexp_def]);

val GENLIST_CONS = prove(
  ``!n. GENLIST (K x) (SUC n) = x::GENLIST (K x) n``,
  Induct \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [GENLIST]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,APPEND]);

val repeat_thm = add_prove(
  ``!a n. repeat a n = list2sexp (GENLIST (K a) (getVal n))``,
  Induct_on `getVal n`
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [repeat_def] THEN1 (FS [GENLIST])
  \\ FS [GENLIST_CONS,ADD1]);

val string_le = prove(
  ``!s t. s <= t = ~(t < (s:string))``,
  FULL_SIMP_TAC std_ss [stringTheory.string_le_def] \\ REPEAT STRIP_TAC
  \\ METIS_TAC [stringTheory.string_lt_cases,stringTheory.string_lt_antisym,
                stringTheory.string_lt_nonrefl]);

val sort_symbols_insert_thm = add_prove(
  ``!xs a. sort_symbols_insert a (list2sexp xs) =
           list2sexp (ISORT_INSERT (\x y. getSym x <= getSym y) a xs)``,
  Induct \\ ONCE_REWRITE_TAC [sort_symbols_insert_def]
  \\ FS [ISORT_INSERT_def,LISP_SYMBOL_LESS_def,string_le]
  \\ REPEAT STRIP_TAC \\ Cases_on `getSym a < getSym h` \\ FS []);

val sort_symbols_thm = add_prove(
  ``!xs. sort_symbols (list2sexp xs) =
         list2sexp (ISORT (\x y. getSym x <= getSym y) xs)``,
  Induct \\ ONCE_REWRITE_TAC [sort_symbols_def] \\ FS [ISORT_def]);

val LOOKUP_DOT_def = Define `
  (LOOKUP_DOT a [] = Sym "NIL") /\
  (LOOKUP_DOT a ((x,y)::xs) = if a = x then Dot x y else LOOKUP_DOT a xs)`;

val lookup_thm = add_prove(
  ``!xs a. lookup a (alist2sexp xs) = LOOKUP_DOT a xs``,
  Induct \\ ONCE_REWRITE_TAC [milawa_defsTheory.lookup_def] \\ FS [LOOKUP_DOT_def]
  \\ Cases \\ FS [LOOKUP_DOT_def]);

val MEM_IMP_INDEX_OF = prove(
  ``!xs y n. MEM y xs ==>
             ?k. (milawa_exec$INDEX_OF n y xs = SOME (n+k)) /\ (EL k xs = y)``,
  Induct \\ SIMP_TAC std_ss [MEM,milawa_execTheory.INDEX_OF_def]
  \\ NTAC 3 STRIP_TAC
  \\ Cases_on `y = h` \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `0` \\ FULL_SIMP_TAC std_ss [EL,HD])
  \\ RES_TAC \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `n+1`)
  \\ Q.EXISTS_TAC `k+1` \\ ASM_SIMP_TAC std_ss [EL,GSYM ADD1,TL] \\ DECIDE_TAC);

val bad_names_tm =
  ``["NIL"; "QUOTE"; "CONS"; "EQUAL"; "<"; "SYMBOL-<"; "+"; "-"; "CONSP";
     "NATP"; "SYMBOLP"; "CAR"; "CDR"; "NOT"; "RANK"; "IF"; "ORDP"; "ORD<"]``

val logic_func2sexp_11 = add_prove(
  ``((logic_func2sexp x = logic_func2sexp y) = (x = y)) /\
    ~(logic_func2sexp x = Sym "QUOTE") /\
    ~(logic_func2sexp x = Sym "NIL")``,
  REVERSE STRIP_TAC THEN1
   (Cases_on `x` THEN1 (Cases_on `l` \\ EVAL_TAC)
    \\ SIMP_TAC (srw_ss()) [logic_func2sexp_def,isSym_def]
    \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [])
  \\ Cases_on `x` \\ Cases_on `y`
  THEN1 (Cases_on `l` \\ Cases_on `l'` \\ EVAL_TAC \\ SRW_TAC [] [])
  THEN1 (Cases_on `l` \\ SRW_TAC [] [logic_func2sexp_def,logic_prim2sym_def]
         \\ FULL_SIMP_TAC std_ss [])
  THEN1 (Cases_on `l` \\ SRW_TAC [] [logic_func2sexp_def,logic_prim2sym_def]
         \\ FULL_SIMP_TAC std_ss [])
  \\ SIMP_TAC std_ss [logic_func2sexp_def]
  \\ Cases_on `MEM s ^bad_names_tm` \\ Cases_on `MEM s' ^bad_names_tm`
  \\ FULL_SIMP_TAC std_ss [SExp_11,SExp_distinct,logic_func_11,logic_func_distinct]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC (Q.SPECL [`xs`,`x`,`0`] MEM_IMP_INDEX_OF)
  \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []);

val func_syntax_ok_def = Define `
  (func_syntax_ok (mPrimitiveFun p) = T) /\
  (func_syntax_ok (mFun f) = ~(MEM f ["NIL"; "QUOTE"; "PEQUAL*";
        "PNOT*"; "POR*"; "FIRST"; "SECOND"; "THIRD"; "FOURTH";
        "FIFTH"; "AND"; "OR"; "LIST"; "COND"; "LET"; "LET*"; "CONS";
        "EQUAL"; "<"; "SYMBOL-<"; "+"; "-"; "CONSP"; "NATP"; "SYMBOLP";
        "CAR"; "CDR"; "NOT"; "RANK"; "IF"; "ORDP"; "ORD<" ]))`;

val var_ok_def = Define `
  var_ok x = ~(x = "NIL") /\ ~(x = "T")`;

val term_syntax_ok_def = tDefine "term_syntax_ok" `
  (term_syntax_ok (mConst s) = T) /\
  (term_syntax_ok (mVar v) = ~(MEM v ["NIL";"T"])) /\
  (term_syntax_ok (mApp fc vs) = func_syntax_ok fc /\ EVERY (term_syntax_ok) vs) /\
  (term_syntax_ok (mLamApp xs y zs) =
     (LIST_TO_SET (free_vars y) SUBSET LIST_TO_SET xs) /\ ALL_DISTINCT xs /\
     EVERY var_ok xs /\
     EVERY (term_syntax_ok) zs /\ term_syntax_ok y /\ (LENGTH xs = LENGTH zs))`
 (WF_REL_TAC `measure (logic_term_size)`);

val formula_syntax_ok_def = Define `
  (formula_syntax_ok (Not x) = formula_syntax_ok x) /\
  (formula_syntax_ok (Or x y) = formula_syntax_ok x /\ formula_syntax_ok y) /\
  (formula_syntax_ok (Equal t1 t2) = term_syntax_ok t1 /\ term_syntax_ok t2)`;

val logic_flag_term_vars_Dot =
  ``logic_flag_term_vars (Sym "LIST") (Dot x y) acc``
  |> ONCE_REWRITE_CONV [logic_flag_term_vars_def]
  |> SIMP_RULE (srw_ss()) [isTrue_CLAUSES,isDot_def,CDR_def,CAR_def]

val logic_flag_term_vars_Sym =
  ``logic_flag_term_vars (Sym "LIST") (Sym s) acc``
  |> ONCE_REWRITE_CONV [logic_flag_term_vars_def]
  |> SIMP_RULE (srw_ss()) [isTrue_CLAUSES,isDot_def,CDR_def,CAR_def]

val PULL_FORALL_IMP = METIS_PROVE [] ``(p ==> !x. q x) = !x. p ==> q x``;

val _ = add_rw (EVAL ``"LIST" = "TERM"``);
val _ = add_rw (EVAL ``"TERM" = "LIST"``);
val _ = add_rw (EVAL ``isTrue (Sym "NIL")``);
val _ = add_rw (ETA_THM);

val term_vars_ok_def = tDefine "term_vars_ok" `
  (term_vars_ok (mConst s) = T) /\
  (term_vars_ok (mVar v) = ~(MEM v ["NIL";"T"])) /\
  (term_vars_ok (mApp fc vs) = ~(fc = mFun "QUOTE") /\ EVERY (term_vars_ok) vs) /\
  (term_vars_ok (mLamApp xs y zs) =
     EVERY (term_vars_ok) zs /\ term_vars_ok y)`
 (WF_REL_TAC `measure (logic_term_size)`);

val logic_flag_term_vars_TERM = prove(
  ``logic_flag_term_vars (Sym "LIST") (Dot (t2sexp l) (Sym "NIL")) acc =
    logic_flag_term_vars (Sym "TERM") (t2sexp l) acc``,
  SIMP_TAC std_ss [Once logic_flag_term_vars_def]
  \\ FS [EVAL ``logic_flag_term_vars (Sym "LIST") (Sym "NIL") acc``]);

val logic_func2sexp_NOT_EQAL_NIL = add_prove(
  ``LISP_EQUAL (logic_func2sexp l0) (Sym "QUOTE") = Sym "NIL"``,
  FS [LISP_EQUAL_def]);

val logic_flag_term_vars_thm = prove(
  ``!l acc.
      EVERY term_vars_ok l ==>
      (logic_flag_term_vars (Sym "LIST") (list2sexp (MAP t2sexp l)) (list2sexp (MAP Sym acc)) =
       list2sexp (MAP Sym ((FLAT (MAP (\a. free_vars a) l)) ++ acc)))``,
  STRIP_TAC \\ completeInduct_on `logic_term1_size l` \\ REPEAT STRIP_TAC
  \\ FS [PULL_FORALL_IMP] \\ Cases_on `l`
  \\ ONCE_REWRITE_TAC [logic_flag_term_vars_def]
  \\ FS [t2sexp_def,list2sexp_def,logic_constantp_def,free_vars_def,
         REVERSE_DEF,APPEND,MAP,FLAT,REVERSE_DEF,EVERY_DEF]
  \\ `logic_term1_size t < logic_term1_size (h::t)` by (EVAL_TAC \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `h` THEN1
   (ONCE_REWRITE_TAC [logic_flag_term_vars_def]
    \\ FS [t2sexp_def,list2sexp_def,logic_constantp_def,free_vars_def,
           APPEND])
  THEN1
   (ONCE_REWRITE_TAC [logic_flag_term_vars_def]
    \\ FS [t2sexp_def,list2sexp_def,logic_constantp_def,free_vars_def,
           logic_variablep_def,APPEND,term_vars_ok_def,MAP,MAP_APPEND])
  THEN1
   (ONCE_REWRITE_TAC [logic_flag_term_vars_def]
    \\ FS [t2sexp_def,list2sexp_def,logic_constantp_def,free_vars_def,
           logic_variablep_def,APPEND,term_vars_ok_def,MAP,MAP_APPEND]
    \\ FS [logic_term_size_def]
    \\ `logic_term1_size l <
      1 + (1 + (logic_func_size l0 + logic_term1_size l) + logic_term1_size t)`
         by DECIDE_TAC
    \\ `(\a. term_vars_ok a) = term_vars_ok` by FULL_SIMP_TAC std_ss [FUN_EQ_THM]
    \\ `(\a. t2sexp a) = t2sexp` by FULL_SIMP_TAC std_ss [FUN_EQ_THM]
    \\ FS [] \\ RES_TAC \\ FS [GSYM MAP_APPEND] \\ FS [APPEND_ASSOC])
  THEN1
   (ONCE_REWRITE_TAC [logic_flag_term_vars_def]
    \\ FS [t2sexp_def,list2sexp_def,logic_constantp_def,free_vars_def,
         REVERSE_DEF,logic_variablep_def,APPEND,term_vars_ok_def,MAP,
         logic_flag_term_vars_Dot,logic_flag_term_vars_Sym,REVERSE_APPEND,
         APPEND_ASSOC] \\ FS [LISP_EQUAL_def]
    \\ `(\a. term_vars_ok a) = term_vars_ok` by FULL_SIMP_TAC std_ss [FUN_EQ_THM]
    \\ `(\a. t2sexp a) = t2sexp` by FULL_SIMP_TAC std_ss [FUN_EQ_THM]
    \\ `logic_term1_size l0 < logic_term1_size (mLamApp l1 l l0::t)` by
          (FS [logic_term_size_def] \\ DECIDE_TAC)
    \\ FS [APPEND_ASSOC]));

val IMP_IMP = METIS_PROVE [] ``b1 /\ (b2 ==> b3) ==> ((b1 ==> b2) ==> b3)``;

val MEM_logic_term_size = prove(
  ``!xs x. MEM x xs ==> logic_term_size x < logic_term1_size xs``,
  Induct \\ SIMP_TAC std_ss [MEM] \\ NTAC 2 STRIP_TAC
  \\ Cases_on `x = h` \\ FULL_SIMP_TAC std_ss [EVERY_DEF,logic_term_size_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ DECIDE_TAC);

val syntax_ok_IMP_vars_ok = add_prove(
  ``!t. term_syntax_ok t ==> term_vars_ok t``,
  STRIP_TAC \\ completeInduct_on `logic_term_size t` \\ REPEAT STRIP_TAC
  \\ Cases_on `t` \\ FS [PULL_FORALL_IMP]
  \\ FS [term_syntax_ok_def,term_vars_ok_def]
  \\ REPEAT STRIP_TAC \\ FS [func_syntax_ok_def]
  \\ FS [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC THEN1
   (Q.PAT_X_ASSUM `!t.bbb ==> b2 ==> b3` (MP_TAC o Q.SPEC `e`)
    \\ MATCH_MP_TAC IMP_IMP \\ FS []
    \\ EVAL_TAC \\ IMP_RES_TAC MEM_logic_term_size \\ DECIDE_TAC) THEN1
   (Q.PAT_X_ASSUM `!t.bbb ==> b2 ==> b3` (MP_TAC o Q.SPEC `e`)
    \\ MATCH_MP_TAC IMP_IMP \\ FS []
    \\ EVAL_TAC \\ IMP_RES_TAC MEM_logic_term_size \\ DECIDE_TAC) THEN1
   (Q.PAT_X_ASSUM `!t.bbb ==> b2 ==> b3` (MP_TAC o Q.SPEC `l`)
    \\ MATCH_MP_TAC IMP_IMP \\ FS []
    \\ EVAL_TAC \\ IMP_RES_TAC MEM_logic_term_size \\ DECIDE_TAC));

val logic_term_vars_raw_thm = add_prove(
  ``!x. term_vars_ok x ==>
        (logic_term_vars (t2sexp x) = list2sexp (MAP Sym (free_vars x)))``,
  SIMP_TAC std_ss [logic_term_vars_def,GSYM logic_flag_term_vars_TERM]
  \\ REPEAT STRIP_TAC \\ MP_TAC (Q.SPECL [`[x]`,`[]`] logic_flag_term_vars_thm)
  \\ FS [EVERY_DEF,MAP,FLAT,APPEND_NIL]);

val logic_term_vars_thm = add_prove(
  ``!x. term_syntax_ok x ==>
        (logic_term_vars (t2sexp x) = list2sexp (MAP Sym (free_vars x)))``,
  SIMP_TAC std_ss [logic_term_vars_raw_thm,syntax_ok_IMP_vars_ok]);

val LIST_LSIZE_def = Define `
  (LIST_LSIZE [] = 0) /\
  (LIST_LSIZE (x::xs) = 1 + LSIZE x + LIST_LSIZE xs)`;

val lisp2sexp_11 = add_prove(
  ``!xs ys. (list2sexp xs = list2sexp ys) = (xs = ys)``,
  Induct \\ Cases_on `ys` \\ FS [NOT_CONS_NIL,CONS_11]);

val LIST_LSIZE_LESS_EQ = prove(
  ``!xs. LIST_LSIZE xs <= LSIZE (list2sexp xs)``,
  Induct \\ EVAL_TAC \\ DECIDE_TAC);

val logic_variable_listp_IMP = prove(
  ``!xs. isTrue (logic_variable_listp (list2sexp xs)) ==>
         ?zs. (xs = MAP Sym zs) /\ EVERY var_ok zs``,
  Induct \\ ONCE_REWRITE_TAC [logic_variable_listp_def]
  THEN1 (FS [logic_variablep_def] \\ METIS_TAC [MAP,EVERY_DEF])
  \\ FS [logic_variablep_def,EVERY_DEF] \\ SRW_TAC [] [] \\ FS []
  \\ Cases_on `isSym h` \\ FS []
  \\ FULL_SIMP_TAC std_ss [isSym_thm]
  \\ Q.EXISTS_TAC `a::zs` \\ FS [MAP,EVERY_DEF]
  \\ FULL_SIMP_TAC std_ss [var_ok_def] \\ REPEAT STRIP_TAC
  \\ FS [NOT_CONS_NIL,CONS_11]);

val IMP_IMP = METIS_PROVE [] ``b1 /\ (b2 ==> b3) ==> ((b1 ==> b2) ==> b3)``;

val logic_flag_termp_TERM = prove(
  ``isTrue (logic_flag_termp (Sym "LIST") (list2sexp [x])) =
    isTrue (logic_flag_termp (Sym "TERM") x)``,
  SIMP_TAC std_ss [Once logic_flag_termp_def] \\ FS []
  \\ Cases_on `isTrue (logic_flag_termp (Sym "TERM") x)` \\ FS []
  \\ SIMP_TAC std_ss [Once logic_flag_termp_def] \\ FS []);

val ALL_DISTINCT_Sym = add_prove(
  ``!xs. ALL_DISTINCT (MAP Sym xs) = ALL_DISTINCT xs``,
  Induct \\ FS [ALL_DISTINCT,MAP,MEM_MAP]);

val logic_sym2prim_thm = add_prove(
  ``(logic_sym2prim a = SOME x) ==> (a = logic_prim2sym x)``,
  Cases_on `x` \\ FULL_SIMP_TAC std_ss [logic_sym2prim_def]
  \\ SRW_TAC [] [logic_prim2sym_def]);

val logic_flag_termp_thm = prove(
  ``!xs. isTrue (logic_flag_termp (Sym "LIST") (list2sexp xs)) ==>
         ?ts. (xs = MAP t2sexp ts) /\ EVERY term_syntax_ok ts``,
  STRIP_TAC \\ completeInduct_on `LIST_LSIZE xs` \\ STRIP_TAC \\ STRIP_TAC
  \\ FS [PULL_FORALL_IMP] \\ Cases_on `xs`
  \\ ONCE_REWRITE_TAC [logic_flag_termp_def]
  \\ FS [] \\ REPEAT STRIP_TAC THEN1 (Q.EXISTS_TAC `[]` \\ EVAL_TAC)
  \\ POP_ASSUM MP_TAC \\ SRW_TAC [] [] \\ FS []
  \\ `?ts2. (h = t2sexp ts2) /\ term_syntax_ok ts2` suffices_by (STRIP_TAC THEN `LIST_LSIZE t < LIST_LSIZE (h::t)` by (FS [LIST_LSIZE_def] \\ DECIDE_TAC)
    \\ RES_TAC \\ Q.EXISTS_TAC `ts2::ts` \\ FS [MAP,EVERY_DEF])
  \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC \\ REVERSE (Cases_on `h`)
  THEN1
   (ONCE_REWRITE_TAC [logic_flag_termp_def]
    \\ FS [logic_variablep_def,logic_constantp_def]
    \\ Cases_on `s = "T"` \\ FS []
    \\ Cases_on `s = "NIL"` \\ FS []
    \\ Q.EXISTS_TAC `mVar s` \\ EVAL_TAC \\ FS [])
  THEN1
   (ONCE_REWRITE_TAC [logic_flag_termp_def]
    \\ FS [logic_variablep_def,logic_constantp_def]
    \\ FS [LISP_EQUAL_def] \\ SIMP_TAC (srw_ss()) [] \\ FS [])
  \\ ONCE_REWRITE_TAC [logic_flag_termp_def] \\ FS [logic_variablep_def]
  \\ Cases_on `isTrue (logic_constantp (Dot S' S0))` \\ FS [] THEN1
   (POP_ASSUM MP_TAC \\ Cases_on `S0` \\ FS [logic_constantp_def]
    \\ Cases_on `S0'` \\ FS [] \\ SRW_TAC [] [] \\ FS []
    \\ Q.EXISTS_TAC `mConst S''` \\ EVAL_TAC)
  \\ REVERSE (Cases_on `isTrue (logic_function_namep S')`) \\ FS [] THEN1
   (Cases_on `list_exists 3 S'` \\ FS [LET_DEF]
    \\ Cases_on `?xs. CAR (CDR S') = list2sexp xs` \\ FS []
    \\ Cases_on `?ys. S0 = list2sexp ys` \\ FS []
    \\ Cases_on `isTrue (logic_flag_termp (Sym "LIST") (list2sexp ys))` \\ FS []
    \\ SRW_TAC [] [] \\ FS []
    \\ `LIST_LSIZE ys < LIST_LSIZE (Dot S' (list2sexp ys)::t)` by
     (SIMP_TAC std_ss [LIST_LSIZE_def,LSIZE_def]
      \\ `LIST_LSIZE ys <= LSIZE (list2sexp ys)` by FS [LIST_LSIZE_LESS_EQ]
      \\ DECIDE_TAC)
    \\ RES_TAC
    \\ Cases_on `S'` \\ FS []
    \\ Cases_on `S0` \\ FS []
    \\ Cases_on `S0'` \\ FS []
    \\ Cases_on `S0` \\ FS []
    \\ IMP_RES_TAC logic_variable_listp_IMP
    \\ FS [LIST_LSIZE_def,LSIZE_def]
    \\ Q.PAT_X_ASSUM `!xs.bbb` (MP_TAC o Q.SPEC `[S''']`)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC std_ss [logic_flag_termp_TERM] \\ STRIP_TAC
    \\ Cases_on `ts'` \\ FS [MAP,NOT_CONS_NIL]
    \\ Cases_on `t'` \\ FS [MAP,NOT_CONS_NIL,CONS_11]
    \\ Q.EXISTS_TAC `mLamApp zs h ts` \\ FS [t2sexp_def,term_syntax_ok_def,EVERY_DEF]
    \\ FS [LENGTH_MAP] \\ FS [SUBSET_DEF,MEM_MAP]
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x. bb1 ==> bb2` (MP_TAC o Q.SPEC `Sym x`) \\ FS [])
  \\ FS [LET_DEF] \\ Cases_on `?xs. S0 = list2sexp xs` \\ FS []
  \\ Cases_on `isTrue (logic_flag_termp (Sym "LIST") (list2sexp xs))` \\ FS []
  \\ `LIST_LSIZE xs < LIST_LSIZE (Dot S' (list2sexp xs)::t)` by
      (SIMP_TAC std_ss [LIST_LSIZE_def,LSIZE_def]
       \\ `LIST_LSIZE xs <= LSIZE (list2sexp xs)` by FS [LIST_LSIZE_LESS_EQ]
       \\ DECIDE_TAC)
  \\ RES_TAC \\ FS [logic_function_namep_def]
  \\ FULL_SIMP_TAC std_ss [GSYM list2sexp_def,memberp_thm]
  \\ Cases_on `isSym S'` \\ FS [] \\ FS [isSym_thm]
  \\ Cases_on `logic_sym2prim a` THEN1
   (Q.EXISTS_TAC `mApp (mFun a) ts`
    \\ FS [t2sexp_def,term_syntax_ok_def,EVERY_DEF,
         logic_func2sexp_def,func_syntax_ok_def]
    \\ POP_ASSUM MP_TAC
    \\ SIMP_TAC std_ss [logic_sym2prim_def] \\ SRW_TAC [] [])
  \\ Q.EXISTS_TAC `mApp (mPrimitiveFun x) ts`
  \\ FS [t2sexp_def,term_syntax_ok_def,EVERY_DEF,
         logic_func2sexp_def,func_syntax_ok_def]);

val logic_termp_thm = prove(
  ``!x. isTrue (logic_termp x) ==> ?t. (x = t2sexp t) /\ term_syntax_ok t``,
  REPEAT STRIP_TAC \\ MP_TAC (Q.SPEC `[x]` logic_flag_termp_thm)
  \\ FS [logic_flag_termp_TERM,logic_termp_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `ts` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC []);

val _ = add_rws [logic_unquote_def, logic_functionp_def,
                 logic_function_name_def, logic_function_args_def,
                 logic_function_def, logic_lambdap_def,
                 logic_lambda_formals_def, logic_lambda_body_def,
                 logic_lambda_actuals_def, logic_lambda_def,
                 logic_constantp_def];

val logic_func2sexp_QUOTE = add_prove(
  ``func_syntax_ok l0 ==>
    (LISP_EQUAL (logic_func2sexp l0) (Sym "QUOTE") = Sym "NIL")``,
  FS []);

val logic_func2sexp_NOT_QUOTE = add_prove(
  ``func_syntax_ok l0 ==> ~(logic_func2sexp l0 = Sym "QUOTE")``,
  FS []);

val logic_function_namep_Dot = add_prove(
  ``logic_function_namep (Dot x y) = Sym "NIL"``, EVAL_TAC);

val LISP_EQUAL_Dot_Sym = add_prove(
  ``LISP_EQUAL (Dot x y) (Sym z) = Sym "NIL"``, EVAL_TAC);

val logic_function_namep_thm = add_prove(
  ``func_syntax_ok l0 ==> (logic_function_namep (logic_func2sexp l0) = Sym "T")``,
  Cases_on `l0` \\ FS [] THEN1 (Cases_on `l` \\ EVAL_TAC)
  \\ FS [logic_func2sexp_def,logic_function_namep_def]
  \\ FULL_SIMP_TAC std_ss [GSYM list2sexp_def,memberp_thm]
  \\ FS [not_def] \\ EVAL_TAC
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [isSym_def]);

val logic_flag_term_atblp_TERM = prove(
  ``isTrue (logic_flag_term_atblp (Sym "LIST") (list2sexp (MAP t2sexp [l])) atbl) =
    isTrue (logic_flag_term_atblp (Sym "TERM") (t2sexp l) atbl)``,
  SIMP_TAC std_ss [Once logic_flag_term_atblp_def] \\ FS [MAP]
  \\ Cases_on `isTrue (logic_flag_term_atblp (Sym "TERM") (t2sexp l) atbl)` \\ FS []
  \\ SIMP_TAC std_ss [Once logic_flag_term_atblp_def] \\ FS [MAP]);

(* informally domain atbl = primitives UNION domain ctxt, they agree on content *)
val atbl_ok_def = Define `
  atbl_ok (ctxt:context_type) atbl =
    !f. func_syntax_ok f ==>
          (CDR (lookup (logic_func2sexp f) atbl) =
           if func_arity ctxt f = NONE then Sym "NIL" else
             Val (THE (func_arity ctxt f)))`

val logic_flag_term_atblp_thm = prove(
  ``!ts.
      EVERY term_syntax_ok ts /\ atbl_ok ctxt atbl ==>
      isTrue (logic_flag_term_atblp (Sym "LIST") (list2sexp (MAP t2sexp ts)) atbl) ==>
      EVERY (term_ok ctxt) ts``,
  STRIP_TAC \\ completeInduct_on `logic_term1_size ts` \\ STRIP_TAC \\ STRIP_TAC
  \\ FS [PULL_FORALL_IMP] \\ Cases_on `ts` \\ FS [EVERY_DEF] \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [logic_flag_term_atblp_def] \\ FS [MAP]
  \\ Cases_on `isTrue (logic_flag_term_atblp (Sym "TERM") (t2sexp h) atbl)` \\ FS []
  \\ `logic_term1_size t < logic_term1_size (h::t)` by (EVAL_TAC \\ DECIDE_TAC)
  \\ FS [] \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `isTrue (logic_flag_term_atblp (Sym "TERM") (t2sexp h) atbl)` MP_TAC
  \\ ONCE_REWRITE_TAC [logic_flag_term_atblp_def] \\ FS [MAP]
  \\ REVERSE (Cases_on `h`)
  \\ FS [t2sexp_def,term_ok_def,logic_variablep_def,term_syntax_ok_def]
  \\ FS [LET_DEF,LENGTH_MAP] THEN1
   (Cases_on `isTrue (logic_flag_term_atblp (Sym "TERM") (t2sexp l) atbl)` \\ FS []
    \\ STRIP_TAC
    \\ Q.PAT_X_ASSUM `!ts.bbb` (fn th => (MP_TAC o Q.SPEC `l0`) th THEN
                                       (MP_TAC o Q.SPEC `[l]`) th)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [EVERY_DEF,logic_flag_term_atblp_TERM] \\ STRIP_TAC
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC)
    \\ FS [EVERY_MEM])
  \\ Cases_on `Val (LENGTH l) = CDR (lookup (logic_func2sexp l0) atbl)` \\ FS []
  \\ STRIP_TAC \\ Q.PAT_X_ASSUM `!ts.bbb` (MP_TAC o Q.SPEC `l`)
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC)
  \\ FS [] \\ FS [EVERY_MEM] \\ STRIP_TAC
  \\ FS [atbl_ok_def] \\ RES_TAC \\ FS []
  \\ Cases_on `func_arity ctxt l0` \\ FS []);

val logic_term_atblp_thm = prove(
  ``term_syntax_ok t /\ atbl_ok ctxt atbl ==>
    isTrue (logic_term_atblp (t2sexp t) atbl) ==>
    term_ok ctxt t``,
  REPEAT STRIP_TAC \\ FS [logic_term_atblp_def]
  \\ MP_TAC (Q.SPEC `[t]` logic_flag_term_atblp_thm)
  \\ FS [EVERY_DEF,logic_flag_term_atblp_TERM]);

val _ = add_rws [logic_fmtype_def, logic__lhs_def, logic__rhs_def,
                 logic__arg_def, logic_vlhs_def, logic_vrhs_def,
                 logic_pequal_def, logic_pnot_def, logic_por_def];

val logic_formulap_thm = prove(
  ``!x. isTrue (logic_formulap x) ==> ?t. (x = f2sexp t) /\ formula_syntax_ok t``,
  STRIP_TAC \\ completeInduct_on `LSIZE x` \\ STRIP_TAC \\ STRIP_TAC
  \\ FS [PULL_FORALL_IMP] \\ ONCE_REWRITE_TAC [logic_formulap_def] \\ FS []
  \\ Cases_on `x` \\ FS [] \\ FULL_SIMP_TAC (srw_ss()) [] \\ FS []
  \\ Cases_on `S'` \\ FS [] \\ Cases_on `S0` \\ FS []
  \\ SRW_TAC [] [] \\ FS [] THEN1
   (Cases_on `S0'` \\ FS [] \\ Cases_on `S0` \\ FS []
    \\ IMP_RES_TAC logic_termp_thm \\ FS []
    \\ Q.EXISTS_TAC `Equal t' t` \\ EVAL_TAC \\ FS [])
  THEN1
   (Cases_on `S0'` \\ FS [LSIZE_def]
    \\ `LSIZE S' < SUC (SUC (LSIZE S'))` by DECIDE_TAC \\ RES_TAC
    \\ Q.EXISTS_TAC `Not t` \\ EVAL_TAC \\ FS [])
  THEN1
   (Cases_on `S0'` \\ FS [] \\ Cases_on `S0` \\ FS [LSIZE_def]
    \\ `LSIZE S' < SUC (SUC (LSIZE S' + SUC (LSIZE S''))) /\
        LSIZE S'' < SUC (SUC (LSIZE S' + SUC (LSIZE S'')))` by DECIDE_TAC
    \\ RES_TAC \\ FS []
    \\ Q.EXISTS_TAC `Or t' t` \\ EVAL_TAC \\ FS []));

val logic_formula_atblp_thm = prove(
  ``!t. formula_syntax_ok t /\ atbl_ok ctxt atbl ==>
        isTrue (logic_formula_atblp (f2sexp t) atbl) ==>
        formula_ok ctxt t``,
  Induct \\ ONCE_REWRITE_TAC [logic_formula_atblp_def]
  \\ FS [formula_syntax_ok_def,formula_ok_def,LET_DEF,f2sexp_def]
  \\ FULL_SIMP_TAC (srw_ss()) []
  THEN1 (Cases_on `isTrue (logic_formula_atblp (f2sexp t) atbl)` \\ FS [])
  \\ NTAC 3 STRIP_TAC
  \\ Cases_on `isTrue (logic_term_atblp (t2sexp l) atbl)` \\ FS [] \\ STRIP_TAC
  \\ IMP_RES_TAC logic_term_atblp_thm \\ FS []);

val logic_disjoin_formulas_thm = add_prove(
  ``!xs. (logic_disjoin_formulas (list2sexp (MAP f2sexp xs)) =
          if xs = [] then Sym "NIL" else f2sexp (or_list xs))``,
  Induct THEN1 EVAL_TAC \\ REPEAT STRIP_TAC \\ FS []
  \\ Cases_on `xs` \\ FS [MAP,or_list_def]
  \\ ONCE_REWRITE_TAC [logic_disjoin_formulas_def] \\ FS [f2sexp_def]);

val _ = Hol_datatype `
  logic_appeal =
    Appeal of string => formula => (logic_appeal list # (SExp option)) option`

val logic_appeal_size_def = fetch "-" "logic_appeal_size_def"

val CONCL_def = Define `CONCL (Appeal name concl x) = concl`;
val HYPS_def = Define `
  (HYPS (Appeal name concl NONE) = []) /\
  (HYPS (Appeal name concl (SOME(x,y))) = x)`;

val logic_appeal_size_def = fetch "-" "logic_appeal_size_def"

val logic_appeal3_size_lemma = prove(
  ``!q a. MEM a q ==> logic_appeal_size a < logic_appeal3_size q``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [logic_appeal_size_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [logic_appeal_size_def] \\ DECIDE_TAC);

val a2sexp_def = tDefine "a2sexp" `
  a2sexp (Appeal name concl subproofs_extras) =
    let xs =
       (if subproofs_extras = NONE then [] else
         [list2sexp (MAP a2sexp (FST (THE subproofs_extras)))] ++
           if SND (THE subproofs_extras) = NONE then [] else
             [THE (SND (THE subproofs_extras))]) in
       list2sexp ([Sym name; f2sexp concl] ++ xs)`
 (WF_REL_TAC `measure (logic_appeal_size)` \\ REPEAT STRIP_TAC
  \\ Cases_on `subproofs_extras` \\ FULL_SIMP_TAC (srw_ss()) [logic_appeal_size_def]
  \\ Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) [logic_appeal_size_def]
  \\ IMP_RES_TAC logic_appeal3_size_lemma \\ DECIDE_TAC)

val appeal_syntax_ok_def = tDefine "appeal_syntax_ok" `
  appeal_syntax_ok (Appeal name concl subproofs_extras) =
    formula_syntax_ok concl /\
    (~(subproofs_extras = NONE) ==>
       EVERY appeal_syntax_ok (FST (THE subproofs_extras)))`
 (WF_REL_TAC `measure (logic_appeal_size)` \\ REPEAT STRIP_TAC
  \\ Cases_on `subproofs_extras` \\ FULL_SIMP_TAC (srw_ss()) [logic_appeal_size_def]
  \\ Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) [logic_appeal_size_def]
  \\ IMP_RES_TAC logic_appeal3_size_lemma \\ DECIDE_TAC);

val appeal_syntax_ok_thm = prove(
  ``appeal_syntax_ok a =
      formula_syntax_ok (CONCL a) /\
      EVERY appeal_syntax_ok (HYPS a)``,
  Cases_on `a` \\ SIMP_TAC std_ss [Once appeal_syntax_ok_def,CONCL_def,HYPS_def]
  \\ Cases_on `o'` \\ FS [HYPS_def,EVERY_DEF]
  \\ Cases_on `x` \\ FS [HYPS_def,EVERY_DEF]);

val anylist2sexp_def = (add_rw o Define) `
  (anylist2sexp [] x = x) /\
  (anylist2sexp (y::ys) x = Dot y (anylist2sexp ys x))`;

val logic_flag_appealp_lemma = add_prove(
  ``isTrue (logic_formulap (Sym "NIL")) = F``,
  EVAL_TAC);

val anylist2sexp_NIL = add_prove(
  ``!xs. anylist2sexp xs (Sym "NIL") = list2sexp xs``,
  Induct \\ FS []);

val anylist2sexp_EXISTS = prove(
  ``!x. ?zs z. (x = anylist2sexp zs z) /\ ~(isDot z)``,
  REVERSE Induct
  THEN1 (REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`[]`,`Sym s`] \\ EVAL_TAC)
  THEN1 (REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`[]`,`Val n`] \\ EVAL_TAC)
  \\ FS [] \\ Q.LIST_EXISTS_TAC [`x::zs'`,`z'`] \\ FS []);

val logic_flag_appealp_thm = prove(
  ``!xs. isTrue (logic_flag_appealp (Sym "LIST") (list2sexp xs)) ==>
         ?ts. (xs = MAP a2sexp ts) /\ EVERY appeal_syntax_ok ts``,
  STRIP_TAC \\ completeInduct_on `LIST_LSIZE xs` \\ STRIP_TAC  \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [logic_flag_appealp_def]
  \\ FS [PULL_FORALL_IMP] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `xs` \\ FS []
  THEN1 (FS [GSYM AND_IMP_INTRO] \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `[]` \\ EVAL_TAC)
  \\ Cases_on `isTrue (logic_flag_appealp (Sym "PROOF") h)` \\ FS []
  \\ REPEAT STRIP_TAC
  \\ REVERSE (sg `?t. (h = a2sexp t) /\ appeal_syntax_ok t`)
  \\ `LIST_LSIZE t < LIST_LSIZE (h::t)` by (EVAL_TAC \\ DECIDE_TAC) \\ RES_TAC
  THEN1 (Q.EXISTS_TAC `t'::ts` \\ FS [CONS_11,APPEND,MAP,EVERY_DEF])
  \\ Q.PAT_X_ASSUM `isTrue (logic_flag_appealp (Sym "PROOF") h)` MP_TAC
  \\ ONCE_REWRITE_TAC [logic_flag_appealp_def]
  \\ SRW_TAC [] [] \\ FS []
  \\ Q.PAT_X_ASSUM `h = list2sexp xs` ASSUME_TAC \\ FS []
  \\ Cases_on `xs` THEN1 (FS [] \\ Cases_on `xs'` \\ FS [])
  \\ Cases_on `t` THEN1 (FS [] \\ Cases_on `xs'` \\ FS [])
  \\ Cases_on `t'` THEN1
   (FS [isSym_thm] \\ IMP_RES_TAC logic_formulap_thm \\ FS []
    \\ Cases_on `xs'` \\ FS []
    \\ Q.EXISTS_TAC `Appeal a t NONE`
    \\ FS [appeal_syntax_ok_def,a2sexp_def,list2sexp_def,LET_DEF,APPEND])
  \\ Cases_on `t` THEN1
   (FS [isSym_thm] \\ IMP_RES_TAC logic_formulap_thm \\ FS []
    \\ Q.PAT_X_ASSUM `!xs.bb` (MP_TAC o Q.SPEC `xs'`)
    \\ FULL_SIMP_TAC std_ss [isDot_def]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [LIST_LSIZE_def,LSIZE_def]
      \\ `LIST_LSIZE xs' <= LSIZE (list2sexp xs')` by FS [LIST_LSIZE_LESS_EQ]
      \\ DECIDE_TAC)
    \\ Q.PAT_X_ASSUM `h''' = list2sexp xs'` ASSUME_TAC \\ FS []
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `Appeal a t (SOME(ts',NONE))`
    \\ FS [appeal_syntax_ok_def,a2sexp_def,list2sexp_def,LET_DEF,APPEND])
  \\ Cases_on `t'` THEN1
   (FS [isSym_thm] \\ IMP_RES_TAC logic_formulap_thm \\ FS []
    \\ Q.PAT_X_ASSUM `!xs.bb` (MP_TAC o Q.SPEC `xs'`) \\ FS []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [LIST_LSIZE_def,LSIZE_def]
      \\ `LIST_LSIZE xs' <= LSIZE (list2sexp xs')` by FS [LIST_LSIZE_LESS_EQ]
      \\ DECIDE_TAC)
    \\ Q.PAT_X_ASSUM `h''' = list2sexp xs'` ASSUME_TAC \\ FS []
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `Appeal a t (SOME(ts',SOME h''''))`
    \\ FS [appeal_syntax_ok_def,a2sexp_def,list2sexp_def,LET_DEF,APPEND])
  \\ FS [LENGTH] \\ `F` by DECIDE_TAC);

val logic_appealp_thm = prove(
  ``!x. isTrue (logic_appealp x) ==> ?t. (x = a2sexp t) /\ appeal_syntax_ok t``,
  FS [logic_appealp_def] \\ REPEAT STRIP_TAC
  \\ MP_TAC (Q.SPEC `[x]` logic_flag_appealp_thm)
  \\ ONCE_REWRITE_TAC [logic_flag_appealp_def]
  \\ FS [] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [logic_flag_appealp_def]
  \\ FS [] \\ FULL_SIMP_TAC (srw_ss()) [] \\ FS []
  \\ REPEAT STRIP_TAC \\ Cases_on `ts` \\ FULL_SIMP_TAC (srw_ss()) [MAP]
  \\ METIS_TAC []);

val logic_appeal_listp_thm = prove(
  ``!xs. isTrue (logic_appeal_listp (list2sexp xs)) ==>
         ?ts. (xs = MAP a2sexp ts) /\ EVERY appeal_syntax_ok ts``,
  FS [logic_appeal_listp_def,logic_flag_appealp_thm]);

val logic_appeal_anylistp_thm = prove(
  ``!xs y. ~(isDot y) /\ isTrue (logic_appeal_listp (anylist2sexp xs y)) ==>
           ?ts. (xs = MAP a2sexp ts) /\ EVERY appeal_syntax_ok ts``,
  SIMP_TAC std_ss [logic_appeal_listp_def]
  \\ Induct \\ REPEAT STRIP_TAC THEN1 (Q.EXISTS_TAC `[]` \\ EVAL_TAC)
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [logic_flag_appealp_def]
  \\ FS [anylist2sexp_def] \\ SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] [] \\ FS [] \\ FS [GSYM logic_appealp_def]
  \\ IMP_RES_TAC logic_appealp_thm \\ RES_TAC \\ FS []
  \\ Q.EXISTS_TAC `t::ts` \\ FS [MAP,EVERY_DEF]);


val _ = add_rws [logic_method_def, logic_conclusion_def,
                 logic_subproofs_def, logic_extras_def]

val logic_strip_conclusions_thm = add_prove(
  ``!xs. logic_strip_conclusions (list2sexp xs) = list2sexp (MAP (CAR o CDR) xs)``,
  Induct THEN1 EVAL_TAC
  \\ ONCE_REWRITE_TAC [logic_strip_conclusions_def] \\ FS [MAP]);

val logic_func2sexp_NOT_Dot = add_prove(
  ``~(logic_func2sexp l0 = Dot x y)``,
  Cases_on `l0` \\ FS [func_syntax_ok_def]
  THEN1 (Cases_on `l` \\ EVAL_TAC)
  \\ SRW_TAC [] [logic_func2sexp_def]);

val MAP_EQ_MAP = prove(
  ``!xs ys.
      (!x y. MEM x xs /\ MEM y ys /\ (f x = f y) ==> (x = y)) ==>
      ((MAP f xs = MAP f ys) = (xs = ys))``,
  Induct \\ Cases_on `ys` \\ FS [MAP,LENGTH]
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `t`)
  \\ REPEAT STRIP_TAC \\ SIMP_TAC std_ss [CONS_11]
  \\ `(!x y. MEM x xs /\ MEM y t /\ (f x = f y) ==> (x = y))` by METIS_TAC []
  \\ `((MAP f xs = MAP f t) <=> (xs = t))` by RES_TAC
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
  \\ Cases_on `h = h'` \\ METIS_TAC []);

val MEM_logic_term_size = prove(
  ``!l x. MEM x l ==> logic_term_size x <= logic_term1_size l``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [logic_term_size_def] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val t2sexp_11 = add_prove(
  ``!x y. ((t2sexp x = t2sexp y) = (x = y))``,
  STRIP_TAC \\ completeInduct_on `logic_term_size x`
  \\ REPEAT STRIP_TAC \\ FS [PULL_FORALL_IMP]
  \\ Cases_on `x` \\ Cases_on `y` \\ FS [t2sexp_def]
  \\ FULL_SIMP_TAC (srw_ss()) [term_syntax_ok_def] \\ FS [logic_func2sexp_11] THEN1
   (sg `(MAP t2sexp l = MAP t2sexp l') = (l = l')` \\ FS []
    \\ MATCH_MP_TAC MAP_EQ_MAP \\ REPEAT STRIP_TAC
    \\ FS [EVERY_MEM] \\ RES_TAC
    \\ `logic_term_size x < logic_term_size (mApp l0 l)` by
        (EVAL_TAC \\ IMP_RES_TAC MEM_logic_term_size \\ DECIDE_TAC)
    \\ METIS_TAC [])
  \\ `(MAP Sym l1 = MAP Sym l1') = (l1 = l1')` by
        (MATCH_MP_TAC MAP_EQ_MAP \\ REPEAT STRIP_TAC \\ FS [])
  \\ `(t2sexp l = t2sexp l') = (l = l')` by
       (Q.PAT_X_ASSUM `!xx.bbb` (MATCH_MP_TAC o REWRITE_RULE [AND_IMP_INTRO])
        \\ FS [] \\ EVAL_TAC \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ sg `(MAP t2sexp l0 = MAP t2sexp l0') = (l0 = l0')`
  \\ FS [CONJ_ASSOC]
  \\ MATCH_MP_TAC MAP_EQ_MAP \\ REPEAT STRIP_TAC
  \\ FS [EVERY_MEM] \\ RES_TAC
  \\ `logic_term_size x < logic_term_size (mLamApp l1 l l0)` by
       (EVAL_TAC \\ IMP_RES_TAC MEM_logic_term_size \\ DECIDE_TAC)
  \\ METIS_TAC []);

val f2sexp_11 = add_prove(
  ``!x y. ((f2sexp x = f2sexp y) = (x = y))``,
  Induct \\ Cases_on `y` \\ FS [formula_syntax_ok_def,f2sexp_def]
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ FS []);


(* step checking *)

val appeal_assum_def = (add_rw o Define) `
  appeal_assum ctxt atbl a =
    appeal_syntax_ok a /\ atbl_ok ctxt atbl /\
    EVERY (MilawaTrue ctxt) (MAP CONCL (HYPS a))`;

val thms_inv_def = Define `
  thms_inv ctxt xs = EVERY (MilawaTrue ctxt) xs /\
                     EVERY formula_syntax_ok xs`;

val a2sexp_CONCL = add_prove(
  ``CAR (CDR (a2sexp a)) = f2sexp (CONCL a)``,
  Cases_on `a` \\ FS [a2sexp_def,LET_DEF,APPEND,CONCL_def]);

val appela_syntax_ok_CONCL = add_prove(
  ``appeal_syntax_ok a ==> formula_syntax_ok (CONCL a)``,
  Cases_on `a` \\ EVAL_TAC \\ FS []);

val logic_axiom_okp_thm = add_prove(
  ``appeal_assum ctxt atbl a /\ thms_inv ctxt axioms ==>
    isTrue (logic_axiom_okp (a2sexp a) (list2sexp (MAP f2sexp axioms)) atbl) ==>
    MilawaTrue ctxt (CONCL a)``,
  SIMP_TAC std_ss [logic_axiom_okp_def,LET_DEF] \\ SRW_TAC [] [] \\ FS []
  \\ FS [appeal_assum_def,thms_inv_def,MEM_MAP,EVERY_MEM] \\ RES_TAC \\ FS []);

val logic_theorem_okp_thm = add_prove(
  ``appeal_assum ctxt atbl a /\ thms_inv ctxt thms ==>
    isTrue (logic_theorem_okp (a2sexp a) (list2sexp (MAP f2sexp thms)) atbl) ==>
    MilawaTrue ctxt (CONCL a)``,
  SIMP_TAC std_ss [logic_theorem_okp_def,LET_DEF] \\ SRW_TAC [] [] \\ FS []
  \\ FS [appeal_assum_def,thms_inv_def,MEM_MAP,EVERY_MEM] \\ RES_TAC \\ FS []);

val a2sexp_HYPS = prove(
  ``(list_exists 1 (CAR (CDR (CDR (a2sexp a)))) ==> ?h1. HYPS a = [h1]) /\
    (list_exists 2 (CAR (CDR (CDR (a2sexp a)))) ==> ?h1 h2. HYPS a = [h1;h2])``,
  Cases_on `a` \\ FS [a2sexp_def,LET_DEF,APPEND]
  \\ Cases_on `o'` \\ FS [] \\ Cases_on `x` \\ FS [HYPS_def]
  \\ Cases_on `q` \\ FS [MAP] \\ Cases_on `t` \\ FS [MAP,CONS_11]
  \\ Cases_on `t'` \\ FS [MAP,CONS_11]);

val a2sexp_SELECT = add_prove(
  ``!a.
      (HYPS a = x::xs) ==>
      (CAR (CDR (CDR (a2sexp a))) = list2sexp (MAP a2sexp (x::xs)))``,
  Cases \\ SIMP_TAC std_ss [a2sexp_def,LET_DEF,APPEND] \\ FS []
  \\ Cases_on `o'` \\ FS [HYPS_def] \\ Cases_on `x'` \\ FS [HYPS_def]);

val f2sexp_IMP = prove(
  ``!a. ((CAR (f2sexp a) = Sym "POR*") ==> ?x1 x2. a = Or x1 x2) /\
        ((CAR (f2sexp a) = Sym "PNOT*") ==> ?x1. a = Not x1) /\
        ((CAR (f2sexp a) = Sym "PEQUAL*") ==> ?t1 t2. a = Equal t1 t2)``,
  Cases \\ FS [f2sexp_def] \\ FULL_SIMP_TAC (srw_ss()) []);

val logic_associativity_okp_thm = add_prove(
  ``appeal_assum ctxt atbl a ==>
    isTrue (logic_associativity_okp (a2sexp a)) ==>
    MilawaTrue ctxt (CONCL a)``,
  SIMP_TAC std_ss [logic_associativity_okp_def,LET_DEF]
  \\ SRW_TAC [] [] \\ FS [appeal_syntax_ok_thm]
  \\ IMP_RES_TAC a2sexp_HYPS
  \\ IMP_RES_TAC a2sexp_SELECT
  \\ FS [MAP]
  \\ IMP_RES_TAC f2sexp_IMP
  \\ FS [f2sexp_def]
  \\ IMP_RES_TAC f2sexp_IMP
  \\ FS [f2sexp_def,formula_syntax_ok_def,EVERY_DEF,appeal_syntax_ok_thm]
  \\ REPEAT (Q.PAT_X_ASSUM `f2sexp yyy = f2sexp xxx` MP_TAC)
  \\ FS [f2sexp_def,formula_syntax_ok_def,EVERY_DEF,appeal_syntax_ok_thm]
  \\ REPEAT STRIP_TAC
  \\ FS [f2sexp_def,formula_syntax_ok_def,EVERY_DEF,appeal_syntax_ok_thm]
  \\ ONCE_REWRITE_TAC [MilawaTrue_cases] \\ ASM_SIMP_TAC (srw_ss()) []);

val logic_contraction_okp_thm = add_prove(
  ``appeal_assum ctxt atbl a ==>
    isTrue (logic_contraction_okp (a2sexp a)) ==>
    MilawaTrue ctxt (CONCL a)``,
  SIMP_TAC std_ss [logic_contraction_okp_def,LET_DEF]
  \\ SRW_TAC [] [] \\ FS [appeal_syntax_ok_thm]
  \\ IMP_RES_TAC a2sexp_HYPS
  \\ IMP_RES_TAC a2sexp_SELECT
  \\ FS [MAP]
  \\ IMP_RES_TAC f2sexp_IMP
  \\ FS [f2sexp_def]
  \\ FS [f2sexp_def,formula_syntax_ok_def,EVERY_DEF,appeal_syntax_ok_thm]
  \\ REPEAT STRIP_TAC \\ FS []
  \\ ONCE_REWRITE_TAC [MilawaTrue_cases] \\ ASM_SIMP_TAC (srw_ss()) []
  \\ METIS_TAC []);

val logic_cut_okp_thm = add_prove(
  ``appeal_assum ctxt atbl a ==>
    isTrue (logic_cut_okp (a2sexp a)) ==>
    MilawaTrue ctxt (CONCL a)``,
  SIMP_TAC std_ss [logic_cut_okp_def,LET_DEF]
  \\ SRW_TAC [] [] \\ FS [appeal_syntax_ok_thm]
  \\ IMP_RES_TAC a2sexp_HYPS
  \\ IMP_RES_TAC a2sexp_SELECT
  \\ FS [MAP,EVERY_DEF]
  \\ IMP_RES_TAC f2sexp_IMP
  \\ FS [f2sexp_def]
  \\ IMP_RES_TAC f2sexp_IMP
  \\ FS [f2sexp_def]
  \\ FS [f2sexp_def,formula_syntax_ok_def,EVERY_DEF,appeal_syntax_ok_thm]
  \\ REPEAT STRIP_TAC \\ FS []
  \\ ONCE_REWRITE_TAC [MilawaTrue_cases] \\ ASM_SIMP_TAC (srw_ss()) []
  \\ METIS_TAC []);

val logic_expansion_okp_thm = add_prove(
  ``appeal_assum ctxt atbl a ==>
    isTrue (logic_expansion_okp (a2sexp a) atbl) ==>
    MilawaTrue ctxt (CONCL a)``,
  SIMP_TAC std_ss [logic_expansion_okp_def,LET_DEF]
  \\ SRW_TAC [] [] \\ FS [appeal_syntax_ok_thm]
  \\ IMP_RES_TAC a2sexp_HYPS
  \\ IMP_RES_TAC a2sexp_SELECT
  \\ FS [MAP,EVERY_DEF]
  \\ IMP_RES_TAC f2sexp_IMP
  \\ FS [f2sexp_def]
  \\ REPEAT (Q.PAT_X_ASSUM `f2sexp yyy = f2sexp xxx` MP_TAC)
  \\ FS [f2sexp_def,formula_syntax_ok_def,EVERY_DEF,appeal_syntax_ok_thm]
  \\ REPEAT STRIP_TAC \\ FS []
  \\ IMP_RES_TAC logic_formula_atblp_thm
  \\ ONCE_REWRITE_TAC [MilawaTrue_cases] \\ ASM_SIMP_TAC (srw_ss()) []
  \\ METIS_TAC []);

val logic_propositional_schema_okp_thm = add_prove(
  ``appeal_assum ctxt atbl a ==>
    isTrue (logic_propositional_schema_okp (a2sexp a) atbl) ==>
    MilawaTrue ctxt (CONCL a)``,
  SIMP_TAC std_ss [logic_propositional_schema_okp_def,LET_DEF]
  \\ SRW_TAC [] [] \\ FS [appeal_syntax_ok_thm]
  \\ IMP_RES_TAC a2sexp_HYPS
  \\ IMP_RES_TAC a2sexp_SELECT
  \\ FS [MAP,EVERY_DEF]
  \\ IMP_RES_TAC f2sexp_IMP
  \\ FS [f2sexp_def]
  \\ IMP_RES_TAC f2sexp_IMP
  \\ FS [f2sexp_def]
  \\ REPEAT (Q.PAT_X_ASSUM `f2sexp yyy = f2sexp xxx` MP_TAC)
  \\ FS [f2sexp_def,formula_syntax_ok_def,EVERY_DEF,appeal_syntax_ok_thm]
  \\ REPEAT STRIP_TAC \\ FS []
  \\ IMP_RES_TAC logic_formula_atblp_thm
  \\ ONCE_REWRITE_TAC [MilawaTrue_cases] \\ ASM_SIMP_TAC (srw_ss()) []
  \\ METIS_TAC []);

val logic_function_namep_IMP = prove(
  ``!x. isTrue (logic_function_namep x) ==>
        ?f. (x = logic_func2sexp f) /\ func_syntax_ok f``,
  FS [logic_function_namep_def] \\ FULL_SIMP_TAC std_ss [GSYM list2sexp_def]
  \\ FULL_SIMP_TAC std_ss [memberp_thm] \\ STRIP_TAC
  \\ Cases_on `isSym x` \\ FS [] \\ FULL_SIMP_TAC std_ss [isSym_thm] \\ FS []
  \\ REPEAT STRIP_TAC
  \\ Cases_on `logic_sym2prim a` THEN1
   (POP_ASSUM MP_TAC \\ SIMP_TAC std_ss [logic_sym2prim_def] \\ SRW_TAC [] []
    \\ Q.EXISTS_TAC `mFun a` \\ FS [logic_func2sexp_def,func_syntax_ok_def,MEM])
  \\ Q.EXISTS_TAC `mPrimitiveFun x'`
  \\ FULL_SIMP_TAC std_ss [logic_func2sexp_def,func_syntax_ok_def] \\ FS []);

val logic_check_functional_axiom_lemma = prove(
  ``term_syntax_ok l /\ func_syntax_ok f ==>
    (CAR (t2sexp l) = logic_func2sexp f) ==>
    ?x2. l = mApp f x2``,
  Cases_on `l` \\ FS [t2sexp_def,term_syntax_ok_def]
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT (Cases_on `l0`)
  \\ Cases_on `f` \\ REPEAT (Cases_on `l`) \\ REPEAT (Cases_on `l''`) \\ EVAL_TAC
  \\ SIMP_TAC std_ss []);

val logic_check_functional_axiom_thm = prove(
  ``!f xs ys.
      (LENGTH xs = LENGTH ys) ==>
      formula_syntax_ok f /\
      EVERY term_syntax_ok (REVERSE xs) /\
      EVERY term_syntax_ok (REVERSE ys) /\
      isTrue (logic_check_functional_axiom
                 (f2sexp f)
                 (list2sexp (MAP t2sexp xs))
                 (list2sexp (MAP t2sexp ys))) ==>
      ?ts g res.
           (f = (or_not_equal_list ts
                    (Equal (mApp g (REVERSE xs ++ (MAP FST ts)))
                           (mApp g (REVERSE ys ++ (MAP SND ts))))))``,
  STRIP_TAC \\ completeInduct_on `formula_size f` \\ NTAC 5 STRIP_TAC
  \\ FS [PULL_FORALL_IMP]
  \\ ONCE_REWRITE_TAC [logic_check_functional_axiom_def] \\ FS []
  \\ Cases_on `f` \\ FS [f2sexp_def] \\ FULL_SIMP_TAC (srw_ss()) [] \\ FS []
  \\ SRW_TAC [] [] \\ FS [] THEN1
   (Cases_on `f'` \\ FS [f2sexp_def] \\ SRW_TAC [] [] \\ FS []
    \\ Cases_on `f` \\ FS [f2sexp_def] \\ SRW_TAC [] [] \\ FS []
    \\ `formula_size f0 < formula_size (Or (Not (Equal l l0)) f0)` by
        (EVAL_TAC \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [GSYM list2sexp_def,GSYM MAP,formula_syntax_ok_def]
    \\ Q.PAT_X_ASSUM `!ff xx. bb` (MP_TAC o Q.SPECL [`f0`,`l::xs`,`l0::ys`])
    \\ FS [LENGTH,REVERSE_DEF,EVERY_APPEND,EVERY_DEF] \\ REPEAT STRIP_TAC
    \\ FS [GSYM or_not_equal_list_def]
    \\ Q.LIST_EXISTS_TAC [`(l,l0)::ts`,`g`]
    \\ FS [MAP,REVERSE_DEF] \\ FS [GSYM APPEND_ASSOC,APPEND])
  \\ Q.LIST_EXISTS_TAC [`[]`]
  \\ FS [or_not_equal_list_def] \\ SRW_TAC [] []
  \\ IMP_RES_TAC logic_function_namep_IMP
  \\ FS [formula_syntax_ok_def]
  \\ IMP_RES_TAC logic_check_functional_axiom_lemma
  \\ FS [t2sexp_def] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FS [GSYM rich_listTheory.MAP_REVERSE,term_syntax_ok_def]
  \\ `!x y. MEM x x2' /\ MEM y (REVERSE xs) /\ (t2sexp x = t2sexp y) ==> (x = y)` by
        (FS [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC \\ FS [])
  \\ `!x y. MEM x x2 /\ MEM y (REVERSE ys) /\ (t2sexp x = t2sexp y) ==> (x = y)` by
        (FS [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC \\ FS [])
  \\ IMP_RES_TAC MAP_EQ_MAP \\ FS [])
  |> Q.SPECL [`f`,`[]`,`[]`]
  |> SIMP_RULE std_ss [REVERSE_DEF,MAP,EVERY_DEF,list2sexp_def,APPEND]

val logic_functional_equality_okp_thm = add_prove(
  ``appeal_assum ctxt atbl a ==>
    isTrue (logic_functional_equality_okp (a2sexp a) atbl) ==>
    MilawaTrue ctxt (CONCL a)``,
  SIMP_TAC std_ss [logic_functional_equality_okp_def,LET_DEF]
  \\ SRW_TAC [] [] \\ FS [appeal_syntax_ok_thm]
  \\ IMP_RES_TAC logic_check_functional_axiom_thm
  \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC logic_formula_atblp_thm
  \\ ONCE_REWRITE_TAC [MilawaTrue_cases] \\ ASM_SIMP_TAC (srw_ss()) [] \\ METIS_TAC []);

val t2sexp_IMP = prove(
  ``term_syntax_ok t ==> (CAR (t2sexp t) = Sym "QUOTE") ==> ?x. t = mConst x``,
  Cases_on `t` \\ FS [t2sexp_def] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `l0` \\ TRY (Cases_on `l'`) \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss []);

val prims_tm = ``[(logic_IF,[x1;x2;x3]); (logic_EQUAL,[x1;x2]);
                  (logic_CONSP,[x1]); (logic_CONS,[x1;x2]);
                  (logic_CAR,[x1]); (logic_CDR,[x1]);
                  (logic_SYMBOLP,[x1]); (logic_SYMBOL_LESS,[x1;x2]);
                  (logic_NATP,[x1]); (logic_LESS,[x1;x2]);
                  (logic_ADD,[x1;x2]); (logic_SUB,[x1;x2:SExp])]``

val logic_base_evaluablep_thm = prove(
  ``term_syntax_ok t /\
    isTrue (logic_base_evaluablep (t2sexp t)) ==>
    ?p xs x1 x2 x3.
       (LENGTH xs = primitive_arity p) /\
       (t = mApp (mPrimitiveFun p) (MAP mConst xs)) /\
       MEM (p,xs) ^prims_tm``,
  FS [logic_base_evaluablep_def,LET_DEF] \\ SRW_TAC [] [] \\ FS []
  \\ REPEAT (POP_ASSUM MP_TAC)
  \\ FS [logic_initial_arity_table_def]
  \\ FULL_SIMP_TAC std_ss [GSYM alist2sexp_def,lookup_thm]
  \\ FULL_SIMP_TAC std_ss [LOOKUP_DOT_def]
  \\ Cases_on `t` \\ FS [t2sexp_def] \\ SRW_TAC [] [] \\ FS []
  \\ Q.PAT_X_ASSUM `logic_func2sexp l0 = xxx` MP_TAC \\ FS [term_syntax_ok_def]
  \\ Cases_on `l0` \\ SRW_TAC [] [logic_func2sexp_def]
  \\ FS [func_syntax_ok_def] \\ FULL_SIMP_TAC (srw_ss()) [] \\ Cases_on `l'`
  \\ FULL_SIMP_TAC (srw_ss()) [primitive_arity_def,logic_prim2sym_def]
  \\ TRY (Cases_on `l` \\ FS [MAP])
  \\ TRY (Cases_on `t` \\ FS [MAP])
  \\ TRY (Cases_on `t'` \\ FS [MAP])
  \\ TRY (Cases_on `t` \\ FS [MAP])
  \\ FULL_SIMP_TAC std_ss [Once logic_constant_listp_def] \\ FS []
  \\ FULL_SIMP_TAC std_ss [Once logic_constant_listp_def] \\ FS []
  \\ FULL_SIMP_TAC std_ss [Once logic_constant_listp_def] \\ FS []
  \\ FULL_SIMP_TAC std_ss [Once logic_constant_listp_def] \\ FS []
  \\ REPEAT (POP_ASSUM MP_TAC) \\ SRW_TAC [] []
  \\ REPEAT (POP_ASSUM MP_TAC) \\ SRW_TAC [] [] \\ FS []
  \\ IMP_RES_TAC t2sexp_IMP
  \\ FULL_SIMP_TAC std_ss [MEM] \\ FULL_SIMP_TAC (srw_ss()) []);

val logic_unquote_list_thm = add_prove(
  ``!xs. logic_unquote_list (list2sexp (MAP t2sexp (MAP mConst xs))) = list2sexp xs``,
  Induct \\ ONCE_REWRITE_TAC [logic_unquote_list_def] \\ FS [MAP,t2sexp_def]);

val logic_base_evaluator_thm = prove(
  ``MEM (p,xs) ^prims_tm ==>
    (logic_base_evaluator (t2sexp (mApp (mPrimitiveFun p) (MAP mConst xs))) =
     t2sexp (mConst (EVAL_PRIMITIVE p xs)))``,
  FS [MEM] \\ REPEAT STRIP_TAC \\ FS [t2sexp_def]
  \\ FS [logic_base_evaluator_def,logic_func2sexp_def,LET_DEF,logic_prim2sym_def]
  \\ FULL_SIMP_TAC (srw_ss()) [EVAL_PRIMITIVE_def,LISP_IF_def,LISP_CONS_def,
        LISP_ADD_def,LISP_SUB_def]);

val logic_base_eval_okp_thm = add_prove(
  ``appeal_assum ctxt atbl a ==>
    isTrue (logic_base_eval_okp (a2sexp a) atbl) ==>
    MilawaTrue ctxt (CONCL a)``,
  SIMP_TAC std_ss [logic_base_eval_okp_def,LET_DEF]
  \\ SRW_TAC [] [] \\ FS [appeal_syntax_ok_thm]
  \\ IMP_RES_TAC f2sexp_IMP
  \\ FS [f2sexp_def,formula_syntax_ok_def]
  \\ MP_TAC (Q.INST [`t`|->`t1`] logic_base_evaluablep_thm)
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC logic_base_evaluator_thm
  \\ FULL_SIMP_TAC std_ss [t2sexp_11,term_syntax_ok_def]
  \\ Q.PAT_X_ASSUM `xxx = t2` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
  \\ ONCE_REWRITE_TAC [MilawaTrue_cases] \\ ASM_SIMP_TAC (srw_ss()) [] \\ METIS_TAC []);

val sigmap2sexp_def = (add_rw o Define) `
  (sigmap2sexp [] z = z) /\
  (sigmap2sexp ((x,y)::xs) z = Dot (Dot (Sym x) (t2sexp y)) (sigmap2sexp xs z))`;

val lookup_sigmap2sexp_thm = add_prove(
  ``~isDot z ==>
    !xs a. lookup a (sigmap2sexp xs z) =
           LOOKUP a (MAP (\(x,y). (Sym x, (Dot (Sym x) (t2sexp y)))) xs) (Sym "NIL")``,
  STRIP_TAC \\ Induct \\ ONCE_REWRITE_TAC [milawa_defsTheory.lookup_def]
  \\ FS [LOOKUP_def,MAP] \\ Cases \\ FS [LOOKUP_def,MAP]);

val logic_sigmap_thm = prove(
  ``!x. isTrue (logic_sigmap x) ==>
        ?xs z. (x = sigmap2sexp xs z) /\ ~isDot z``,
  REVERSE Induct \\ ONCE_REWRITE_TAC [logic_sigmap_def] \\ FS [] \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `[]` \\ FS []) THEN1 (Q.EXISTS_TAC `[]` \\ FS [])
  \\ POP_ASSUM MP_TAC \\ SRW_TAC [] [] \\ FS []
  \\ Cases_on `x` \\ FS []
  \\ Q.PAT_X_ASSUM `isTrue (logic_variablep xxx)` MP_TAC
  \\ IMP_RES_TAC logic_termp_thm \\ FS [logic_variablep_def]
  \\ SRW_TAC [] [] \\ FS [] \\ FS [isSym_thm]
  \\ Q.LIST_EXISTS_TAC [`(a,t)::xs`,`z`]
  \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss []);

val logic_flag_substitute_thm = prove(
  ``!ts.
      EVERY term_syntax_ok ts /\ ~isDot z ==>
      (logic_flag_substitute (Sym "LIST") (list2sexp (MAP t2sexp ts)) (sigmap2sexp xs z) =
       list2sexp (MAP (t2sexp o term_sub xs) ts))``,
  STRIP_TAC \\ completeInduct_on `logic_term1_size ts` \\ NTAC 3 STRIP_TAC
  \\ FS [PULL_FORALL_IMP] \\ ONCE_REWRITE_TAC [logic_flag_substitute_def]
  \\ Cases_on `ts` \\ FS [] \\ FULL_SIMP_TAC (srw_ss()) [] \\ FS []
  \\ `logic_term1_size t < logic_term1_size (h::t)` by (EVAL_TAC \\ DECIDE_TAC)
  \\ FS [] \\ Cases_on `h` \\ ONCE_REWRITE_TAC [logic_flag_substitute_def]
  \\ FS [t2sexp_def,term_sub_def,logic_variablep_def,LET_DEF,term_syntax_ok_def]
  THEN1
   (REPEAT (POP_ASSUM (K ALL_TAC)) \\ Induct_on `xs`
    \\ FS [MAP,LOOKUP_def,t2sexp_def,FORALL_PROD]
    \\ SRW_TAC [] [] \\ FS [] \\ FS [isTrue_def])
  THEN1
   (`logic_term1_size l < logic_term1_size (mApp l0 l::t)` by (EVAL_TAC \\ DECIDE_TAC)
    \\ FS [] \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ Induct_on `l` \\ FS [MAP])
  THEN1
   (`logic_term1_size l0 < logic_term1_size (mLamApp l1 l l0::t)` by (EVAL_TAC \\ DECIDE_TAC)
    \\ FS [] \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ Induct_on `l0` \\ FS [MAP]));

val logic_substitute_thm = add_prove(
  ``term_syntax_ok t /\ ~isDot z ==>
    (logic_substitute (t2sexp t) (sigmap2sexp xs z) = t2sexp (term_sub xs t))``,
  REPEAT STRIP_TAC \\ MP_TAC (Q.SPEC `[t]` logic_flag_substitute_thm)
  \\ FS [EVERY_DEF]
  \\ ONCE_REWRITE_TAC [logic_flag_substitute_def]
  \\ FS [] \\ FULL_SIMP_TAC (srw_ss()) [] \\ FS [logic_substitute_def]);

val logic_substitute_list_thm =
  REWRITE_RULE [GSYM logic_substitute_list_def] logic_flag_substitute_thm;

val logic_substitute_formula_thm = prove(
  ``!f. formula_syntax_ok f /\ ~isDot z ==>
        (logic_substitute_formula (f2sexp f) (sigmap2sexp xs z) =
         f2sexp (formula_sub xs f))``,
  Induct \\ FS [formula_syntax_ok_def] \\ REPEAT STRIP_TAC \\ FS []
  \\ ONCE_REWRITE_TAC [logic_substitute_formula_def]
  \\ FS [LET_DEF,f2sexp_def,formula_sub_def] \\ FULL_SIMP_TAC (srw_ss()) []);

val logic_instantiation_okp_thm = add_prove(
  ``appeal_assum ctxt atbl a ==>
    isTrue (logic_instantiation_okp (a2sexp a) atbl) ==>
    MilawaTrue ctxt (CONCL a)``,
  SIMP_TAC std_ss [logic_instantiation_okp_def,LET_DEF]
  \\ SRW_TAC [] [] \\ FS [appeal_syntax_ok_thm]
  \\ IMP_RES_TAC a2sexp_HYPS
  \\ IMP_RES_TAC a2sexp_SELECT
  \\ FS [MAP]
  \\ IMP_RES_TAC logic_sigmap_thm
  \\ FS [logic_substitute_formula_thm,EVERY_DEF,appeal_syntax_ok_thm]
  \\ IMP_RES_TAC logic_formula_atblp_thm
  \\ FS [f2sexp_11]
  \\ Q.PAT_X_ASSUM `formula_sub xs (CONCL h1) = CONCL a` (ASSUME_TAC o GSYM)
  \\ REPEAT STRIP_TAC \\ FS []
  \\ ONCE_REWRITE_TAC [MilawaTrue_cases] \\ ASM_SIMP_TAC (srw_ss()) []
  \\ METIS_TAC []);

val isDot_logic_func2sexp = add_prove(
  ``!l0. isDot (logic_func2sexp l0) = F``,
  Cases \\ TRY (Cases_on `l`) \\ EVAL_TAC \\ SRW_TAC [] [isDot_def]);

val list2sexp_CONS_ZIP = prove(
  ``!xs ys.
       (LENGTH xs = LENGTH ys) ==>
       (list2sexp (CONS_ZIP (MAP Sym xs) (MAP t2sexp ys)) =
        sigmap2sexp (ZIP (xs,ys)) (Sym "NIL"))``,
  Induct \\ Cases_on `ys`
  \\ SRW_TAC [] [sigmap2sexp_def,CONS_ZIP_def,list2sexp_def,LISP_CONS_def]);

val logic_beta_reduction_okp_thm = add_prove(
  ``appeal_assum ctxt atbl a ==>
    isTrue (logic_beta_reduction_okp (a2sexp a) atbl) ==>
    MilawaTrue ctxt (CONCL a)``,
  SIMP_TAC std_ss [logic_beta_reduction_okp_def,LET_DEF]
  \\ SRW_TAC [] [] \\ FS [appeal_syntax_ok_thm]
  \\ IMP_RES_TAC a2sexp_HYPS
  \\ IMP_RES_TAC a2sexp_SELECT
  \\ FS [MAP]
  \\ IMP_RES_TAC f2sexp_IMP
  \\ IMP_RES_TAC logic_formula_atblp_thm
  \\ FS [f2sexp_def]
  \\ Cases_on `t1`
  \\ FS [t2sexp_def,formula_syntax_ok_def,term_syntax_ok_def]
  \\ Q.PAT_X_ASSUM `xxx = t2sexp t2` (MP_TAC o GSYM)
  \\ FS [list2sexp_CONS_ZIP,t2sexp_11] \\ REPEAT STRIP_TAC \\ FS []
  \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [MilawaTrue_cases] \\ ASM_SIMP_TAC (srw_ss()) []
  \\ METIS_TAC []);

val logic_formula_listp_thm = prove(
  ``!x. isTrue (logic_formula_listp x) ==>
        ?qs r. EVERY formula_syntax_ok qs /\
               (x = anylist2sexp (MAP f2sexp qs) r) /\ ~isDot r``,
  REVERSE Induct \\ ONCE_REWRITE_TAC [logic_formula_listp_def]
  \\ FS [MAP] \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `[]` \\ EVAL_TAC \\ SIMP_TAC std_ss [isDot_def])
  THEN1 (Q.EXISTS_TAC `[]` \\ EVAL_TAC \\ SIMP_TAC std_ss [isDot_def])
  \\ POP_ASSUM MP_TAC \\ SRW_TAC [] [] \\ FS []
  \\ IMP_RES_TAC logic_formulap_thm
  \\ Q.LIST_EXISTS_TAC [`t::qs`,`r`] \\ FS [EVERY_DEF,MAP]);

val logic_substitute_each_sigma_into_formula_thm = prove(
  ``!ys.
      formula_syntax_ok f /\ EVERY (\(xs,z). ~isDot z) ys /\ ~isDot r ==>
      (logic_substitute_each_sigma_into_formula (f2sexp f)
        (anylist2sexp (MAP (\(xs,z). sigmap2sexp xs z) ys) r) =
       list2sexp (MAP (\s. f2sexp (formula_sub s f)) (MAP FST ys)))``,
  Induct \\ ONCE_REWRITE_TAC [logic_substitute_each_sigma_into_formula_def]
  \\ FS [MAP,FORALL_PROD,logic_substitute_formula_thm,EVERY_DEF])

val logic_pnot_thm = prove(
  ``logic_pnot (f2sexp f) = f2sexp (Not f)``,
  FS [f2sexp_def]);

val logic_make_induction_step_lemma = prove(
  ``!ys. MAP (\(xs,z). f2sexp (formula_sub xs (Not f))) ys =
         MAP f2sexp (MAP (\(xs,z). formula_sub xs (Not f)) ys)``,
  Induct \\ SRW_TAC [] [] \\ Cases_on `h` \\ SRW_TAC [] []);

val logic_make_induction_step_thm = prove(
  ``!ys.
      formula_syntax_ok f /\ EVERY ( \ (xs,z). ~isDot z) ys /\ ~isDot r ==>
      (logic_make_induction_step (f2sexp f) (f2sexp q_i)
         (anylist2sexp (MAP ( \ (xs,z). sigmap2sexp xs z) ys) r) =
       f2sexp (or_list (f::Not q_i::MAP ( \ s. formula_sub s (Not f)) (MAP FST ys))))``,
  FULL_SIMP_TAC std_ss [logic_make_induction_step_def,formula_syntax_ok_def,
    logic_substitute_each_sigma_into_formula_thm,logic_pnot_thm]
  \\ FULL_SIMP_TAC std_ss [GSYM list2sexp_def,LISP_CONS_def]
  \\ ASSUME_TAC (GSYM (GEN_ALL (Q.SPEC `(x::xs)` logic_disjoin_formulas_thm)))
  \\ FULL_SIMP_TAC (srw_ss()) [logic_make_induction_step_lemma,MAP_MAP_o]
  \\ REPEAT STRIP_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC \\ FS [FUN_EQ_THM]);

val logic_make_induction_steps_thm = prove(
  ``!qs yss.
      formula_syntax_ok f /\ ~isDot r /\ ~isDot r2 /\
      EVERY (\ (ys,r). EVERY ( \ (xs,z). ~isDot z) ys /\ ~isDot r) yss /\
      (LENGTH qs = LENGTH yss) ==>
      (logic_make_induction_steps (f2sexp f) (anylist2sexp (MAP f2sexp qs) r2)
         (anylist2sexp (MAP (\ (ys,r). anylist2sexp
                       (MAP (\ (xs,z). sigmap2sexp xs z) ys) r) yss) r) =
       list2sexp (MAP (\(q_i,ys,r). f2sexp
         (or_list (f::Not q_i::MAP ( \s. formula_sub s (Not f)) (MAP FST ys)))) (ZIP (qs,yss))))``,
  Induct \\ ONCE_REWRITE_TAC [logic_make_induction_steps_def]
  \\ Cases_on `yss` \\ FS [LENGTH,MAP,ZIP,ADD1,EVERY_DEF,
       logic_make_induction_step_thm]
  \\ Cases_on `h` \\ FS [LENGTH,MAP,ZIP,ADD1,EVERY_DEF,
       logic_make_induction_step_thm]);

val ordp = ``mApp (mPrimitiveFun logic_ORDP)``
val ord_less = ``mApp (mPrimitiveFun logic_ORD_LESS)``

val logic_make_measure_step_thm = add_prove(
  ``formula_syntax_ok q_i /\ ~isDot z /\ term_syntax_ok m ==>
      (logic_make_measure_step (t2sexp m) (f2sexp q_i) (sigmap2sexp s z) =
       f2sexp (Or (Not q_i) (Equal (^ord_less [term_sub s m;m]) (mConst (Sym "T")))))``,
  FS [logic_make_measure_step_def,f2sexp_def,t2sexp_def,MAP] \\ EVAL_TAC);

val logic_make_measure_steps_thm = add_prove(
  ``!ys.
      formula_syntax_ok q_i /\ EVERY ( \ (xs,z). ~isDot z) ys /\
      term_syntax_ok m /\ ~isDot r ==>
      (logic_make_measure_steps (t2sexp m) (f2sexp q_i)
          (anylist2sexp (MAP ( \ (s,z). sigmap2sexp s z) ys) r) =
       list2sexp (MAP ( \ (s,z).
          f2sexp (Or (Not q_i) (Equal (^ord_less [term_sub s m;m]) (mConst (Sym "T")))))
          ys))``,
  Induct \\ ONCE_REWRITE_TAC [logic_make_measure_steps_def] \\ FS [MAP]
  \\ Cases \\ FS [EVERY_DEF]);

val logic_make_all_measure_steps_thm = add_prove(
  ``!qs yss f.
      term_syntax_ok m /\ ~isDot r /\ ~isDot r2 /\
      EVERY (\ (ys,r). EVERY ( \ (xs,z). ~isDot z) ys /\ ~isDot r) yss /\
      EVERY formula_syntax_ok qs /\ (LENGTH qs = LENGTH yss) ==>
      (logic_make_all_measure_steps (t2sexp m) (anylist2sexp (MAP f2sexp qs) r2)
         (anylist2sexp (MAP (\ (ys,r). anylist2sexp
                       (MAP (\ (xs,z). sigmap2sexp xs z) ys) r) yss) r) =
       list2sexp (FLAT (MAP (\ (q_i,ys,r).
           (MAP ( \ (s,z).
            f2sexp (Or (Not q_i) (Equal (^ord_less [term_sub s m;m]) (mConst (Sym "T")))))
            ys))
       (ZIP(qs,yss)))))``,
  Induct \\ SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [logic_make_all_measure_steps_def]
  \\ Cases_on `yss` \\ FS [LENGTH,MAP,ZIP,ADD1,EVERY_DEF,FLAT,EVERY_DEF]
  \\ Cases_on `h` \\ FS [LENGTH,MAP,ZIP,ADD1,EVERY_DEF,FLAT,EVERY_DEF]);

val a2sexp_HYPS = prove(
  ``!a. CAR (CDR (CDR (a2sexp a))) = list2sexp (MAP a2sexp (HYPS a))``,
  Cases \\ Cases_on `o'` THEN1 EVAL_TAC \\ Cases_on `x` \\ EVAL_TAC \\ FS []);

val MAP_CAR_CDR_a2sexp = add_prove(
  ``!xs. MAP (CAR o CDR) (MAP a2sexp xs) = MAP f2sexp (MAP CONCL xs)``,
  Induct \\ SRW_TAC [] [a2sexp_def] \\ Cases_on `h` \\ FS []);

val logic_make_ordinal_step_thm = add_prove(
  ``logic_make_ordinal_step (t2sexp m) =
    f2sexp (Equal (^ordp [m]) (mConst (Sym "T")))``,
  EVAL_TAC);

val MEM_f2sexp = add_prove(
  ``!xs. MEM (f2sexp x) (MAP f2sexp xs) = MEM x xs``,
  Induct \\ SRW_TAC [] [f2sexp_11]);

val logic_disjoin_formulas_alt = add_prove(
  ``!xs. ~isDot r ==>
         (logic_disjoin_formulas (anylist2sexp (MAP f2sexp xs) r) =
           if xs = [] then Sym "NIL" else f2sexp (or_list xs))``,
  Induct \\ ONCE_REWRITE_TAC [logic_disjoin_formulas_def] \\ FS [MAP]
  \\ REPEAT STRIP_TAC \\ Cases_on `xs` \\ FS [or_list_def,MAP,f2sexp_def]);

val logic_sigma_listp_thm = prove(
  ``!x. isTrue (logic_sigma_listp x) ==>
        ?ys r. (x = anylist2sexp (MAP (\(xs,z). sigmap2sexp xs z) ys) r) /\
               EVERY (\(xs,z). ~isDot z) ys /\ ~(isDot r)``,
  REVERSE Induct \\ ONCE_REWRITE_TAC [logic_sigma_listp_def]
  \\ FS [MAP] \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `[]` \\ EVAL_TAC \\ SIMP_TAC std_ss [isDot_def])
  THEN1 (Q.EXISTS_TAC `[]` \\ EVAL_TAC \\ SIMP_TAC std_ss [isDot_def])
  \\ POP_ASSUM MP_TAC \\ SRW_TAC [] [] \\ FS []
  \\ IMP_RES_TAC logic_sigmap_thm \\ FS []
  \\ Q.LIST_EXISTS_TAC [`(xs,z)::ys`,`r`] \\ FS [EVERY_DEF,MAP]);

val logic_sigma_list_listp_thm = prove(
  ``!x. isTrue (logic_sigma_list_listp x) ==>
        ?yss r. (x = (anylist2sexp (MAP ( \ (ys,r).
                      anylist2sexp (MAP ( \ (xs,z). sigmap2sexp xs z) ys) r) yss) r)) /\
                EVERY ( \ (ys,r). EVERY ( \ (xs,z). ~isDot z) ys /\ ~(isDot r)) yss /\
                ~(isDot r)``,
  REVERSE Induct \\ ONCE_REWRITE_TAC [logic_sigma_list_listp_def]
  \\ FS [MAP] \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `[]` \\ EVAL_TAC \\ SIMP_TAC std_ss [isDot_def])
  THEN1 (Q.EXISTS_TAC `[]` \\ EVAL_TAC \\ SIMP_TAC std_ss [isDot_def])
  \\ POP_ASSUM MP_TAC \\ SRW_TAC [] [] \\ FS []
  \\ IMP_RES_TAC logic_sigma_listp_thm \\ FS []
  \\ Q.LIST_EXISTS_TAC [`(ys,r')::yss`,`r`] \\ FS [EVERY_DEF,MAP]);

val len_anlist2sexp = add_prove(
  ``!xs. ~isDot r ==> (len (anylist2sexp xs r) = Val (LENGTH xs))``,
  Induct \\ ONCE_REWRITE_TAC [len_def]
  \\ FS [LENGTH,ADD1] \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

val MAP_FST_ZIP = prove(
  ``!xs ys. (LENGTH xs = LENGTH ys) ==> (MAP FST (ZIP (xs,ys)) = xs)``,
  Induct \\ Cases_on `ys` \\ FS [LENGTH,ADD1,ZIP,MAP]);

val PULL_EXISTS_IMP = METIS_PROVE [] ``((?x. P x) ==> b) = !x. P x ==> b``
val PULL_CONJ = METIS_PROVE []
  ``((?x. P x) /\ Q = ?x. P x /\ Q) /\
    (Q /\ (?x. P x) = ?x. Q /\ P x)``

val logic_induction_okp_thm = add_prove(
  ``appeal_assum ctxt atbl a ==>
    isTrue (logic_induction_okp (a2sexp a)) ==>
    MilawaTrue ctxt (CONCL a)``,
  SIMP_TAC std_ss [logic_induction_okp_def,LET_DEF]
  \\ SRW_TAC [] [] \\ FS [appeal_syntax_ok_thm]
  \\ IMP_RES_TAC a2sexp_HYPS
  \\ IMP_RES_TAC a2sexp_SELECT
  \\ FS [MAP]
  \\ `?mx qsx sigsx. CAR (CDR (CDR (CDR (a2sexp a)))) = list2sexp [mx;qsx;sigsx]` by
    (FS [list_exists_def] \\ Cases_on `xs` \\ FS [LENGTH,ADD1]
     \\ Cases_on `t` \\ FS [LENGTH,ADD1]
     \\ Cases_on `t'` \\ FS [LENGTH,ADD1]
     \\ Cases_on `t` \\ FS [LENGTH,ADD1] \\ DECIDE_TAC)
  \\ FS [] \\ IMP_RES_TAC logic_termp_thm \\ FS [a2sexp_HYPS]
  \\ IMP_RES_TAC logic_formula_listp_thm \\ FS []
  \\ IMP_RES_TAC logic_sigma_list_listp_thm \\ FS []
  \\ FS [logic_make_basis_step_def]
  \\ FULL_SIMP_TAC std_ss [GSYM anylist2sexp_def,logic_disjoin_formulas_alt,
       GSYM MAP,NOT_CONS_NIL] \\ FS []
  \\ ONCE_REWRITE_TAC [MilawaTrue_cases]
  \\ REPEAT DISJ2_TAC
  \\ Q.ABBREV_TAC `qss = MAP (MAP FST o FST) yss`
  \\ Q.LIST_EXISTS_TAC [`ZIP (qs,qss)`,`t`]
  \\ `LENGTH qs = LENGTH qss` by
       (Q.UNABBREV_TAC `qss` \\ SRW_TAC [] [] \\ FS [LENGTH_MAP])
  \\ FS [LENGTH_MAP,MAP_FST_ZIP]
  \\ `MilawaTrue ctxt (or_list (CONCL a::qs))` by FS [EVERY_MEM]
  \\ `MilawaTrue ctxt (Equal (mApp (mPrimitiveFun logic_ORDP) [t])
         (mConst (Sym "T")))` by FS [EVERY_MEM]
  \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT (Q.PAT_X_ASSUM `isTrue xxx` MP_TAC)
  \\ FS [logic_make_all_measure_steps_thm]
  \\ FS [logic_make_induction_steps_thm]
  \\ FS [SUBSET_DEF,MEM_FLAT,MEM_MAP,f2sexp_11,
       PULL_EXISTS_IMP,EXISTS_PROD,PULL_CONJ]
  \\ REPEAT STRIP_TAC
  \\ `?x1 zs1. MEM (q,zs1,x1) (ZIP (qs,yss)) /\ (ss = MAP FST zs1)` by
     (Q.PAT_X_ASSUM `MEM (q,ss) (ZIP (qs,qss))` MP_TAC \\ Q.UNABBREV_TAC `qss`
      \\ FULL_SIMP_TAC std_ss [MEM_ZIP] \\ REPEAT STRIP_TAC
      \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [EL_MAP] \\ REPEAT STRIP_TAC
      \\ Q.EXISTS_TAC `SND (EL n yss)`
      \\ Q.EXISTS_TAC `FST (EL n yss)`
      \\ FS [] \\ Q.EXISTS_TAC `n` \\ FS [])
  \\ FS [] \\ RES_TAC \\ FS [EVERY_MEM,MEM_MAP,formula_sub_def]
  \\ Q.PAT_X_ASSUM `!e. bbb ==> MilawaTrue ctxt e` MATCH_MP_TAC
  THEN1 (METIS_TAC [])
  \\ Cases_on `y'''` \\ FS [] \\ RES_TAC \\ METIS_TAC []);

val logic_appeal_step_okp_thm = add_prove(
  ``appeal_assum ctxt atbl a /\ thms_inv ctxt thms /\ thms_inv ctxt axioms ==>
    isTrue (logic_appeal_step_okp (a2sexp a) (list2sexp (MAP f2sexp axioms))
                                             (list2sexp (MAP f2sexp thms)) atbl) ==>
    MilawaTrue ctxt (CONCL a)``,
  SIMP_TAC std_ss [logic_appeal_step_okp_def,LET_DEF] \\ SRW_TAC [] []
  \\ IMP_RES_TAC logic_axiom_okp_thm \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC logic_theorem_okp_thm \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC logic_propositional_schema_okp_thm \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC logic_functional_equality_okp_thm \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC logic_expansion_okp_thm \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC logic_contraction_okp_thm \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC logic_beta_reduction_okp_thm \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC logic_associativity_okp_thm \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC logic_cut_okp_thm \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC logic_instantiation_okp_thm \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC logic_induction_okp_thm \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC logic_base_eval_okp_thm \\ ASM_SIMP_TAC std_ss []
  \\ FS []);

val logic_flag_proofp_thm = prove(
  ``!al.
      EVERY appeal_syntax_ok al /\ atbl_ok ctxt atbl /\
      thms_inv ctxt thms /\ thms_inv ctxt axioms ==>
      isTrue (logic_flag_proofp (Sym "LIST")
                                (list2sexp (MAP a2sexp al))
                                (list2sexp (MAP f2sexp axioms))
                                (list2sexp (MAP f2sexp thms)) atbl) ==>
      EVERY (MilawaTrue ctxt o CONCL) al``,
  STRIP_TAC \\ completeInduct_on `logic_appeal3_size al` \\ NTAC 3 STRIP_TAC
  \\ FS [PULL_FORALL_IMP] \\ Cases_on `al` \\ FS [EVERY_DEF]
  \\ ONCE_REWRITE_TAC [logic_flag_proofp_def]
  \\ FS [] \\ FULL_SIMP_TAC (srw_ss()) [] \\ FS [MAP] \\ SRW_TAC [] [] \\ FS []
  \\ `logic_appeal3_size t < logic_appeal3_size (h::t)` by (EVAL_TAC \\ DECIDE_TAC)
  \\ FS [] \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [logic_flag_proofp_def] \\ FS [a2sexp_HYPS]
  \\ SRW_TAC [] [] \\ FS []
  \\ MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] logic_appeal_step_okp_thm)
  \\ FS [AND_IMP_INTRO,REWRITE_RULE [GSYM o_DEF] EVERY_MAP]
  \\ Q.PAT_X_ASSUM `!xx.bbb` MATCH_MP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `h` \\ Cases_on `o'` \\ FULL_SIMP_TAC std_ss [HYPS_def,EVERY_DEF]
  THEN1 (EVAL_TAC \\ DECIDE_TAC)
  \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss [HYPS_def,EVERY_DEF,appeal_syntax_ok_def]
  \\ FS [EVERY_MEM] \\ EVAL_TAC \\ DECIDE_TAC);

val logic_proofp_thm = prove(
  ``appeal_syntax_ok a /\ atbl_ok ctxt atbl /\
    thms_inv ctxt thms /\ thms_inv ctxt axioms ==>
    isTrue (logic_proofp (a2sexp a) (list2sexp (MAP f2sexp axioms))
                                    (list2sexp (MAP f2sexp thms)) atbl) ==>
    MilawaTrue ctxt (CONCL a)``,
  REPEAT STRIP_TAC \\ MP_TAC (Q.SPEC `[a]` logic_flag_proofp_thm)
  \\ FS [EVERY_DEF] \\ ONCE_REWRITE_TAC [logic_flag_proofp_def]
  \\ FS [MAP,logic_proofp_def] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [logic_flag_proofp_def] \\ FS []
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ FS []);




val callmap2sexp_def = Define `
  callmap2sexp ts =
    list2sexp (MAP (\(xs,ys). Dot (list2sexp (MAP t2sexp xs))
                                  (list2sexp (MAP t2sexp ys))) ts)`;

val app_EQ_list2sexp = prove(
  ``!y ys. (app y (Sym "NIL") = list2sexp ys) /\ isTrue (true_listp y) ==>
           (y = list2sexp ys)``,
  REVERSE Induct \\ ONCE_REWRITE_TAC [app_def] \\ FS []
  \\ Cases_on `ys` \\ FS []
  \\ ONCE_REWRITE_TAC [list_fix_def] \\ FS []
  \\ REPEAT STRIP_TAC \\ FS [] \\ Cases_on `xs` \\ FS []);

val true_listp_nil = prove(
  ``isTrue (true_listp (Sym "NIL"))``,
  EVAL_TAC);

val true_listp_cons = prove(
  ``isTrue (true_listp (LISP_CONS x y)) = isTrue (true_listp y)``,
  SIMP_TAC std_ss [Once true_listp_def] \\ FS []);

val true_listp_list_fix = prove(
  ``!y. isTrue (true_listp (list_fix y))``,
  REVERSE Induct
  THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ ONCE_REWRITE_TAC [list_fix_def]
  \\ SIMP_TAC std_ss [LISP_CONSP_def,isDot_def,LISP_TEST_def,isTrue_def]
  \\ SRW_TAC [] [CAR_def,CDR_def,true_listp_cons,LISP_CONS_def]
  \\ ONCE_REWRITE_TAC [true_listp_def] \\ FS [] \\ EVAL_TAC);

val true_listp_app = prove(
  ``!x y. isTrue (true_listp (app x y))``,
  Induct \\ ONCE_REWRITE_TAC [app_def]
  \\ FULL_SIMP_TAC std_ss [isTrue_CLAUSES,
       isDot_def,CAR_def,CDR_def,true_listp_cons,true_listp_list_fix]);

val true_listp_logic_flag_callmap_list = prove(
  ``isTrue (true_listp (logic_flag_callmap (Sym "LIST") y z))``,
  ONCE_REWRITE_TAC [logic_flag_callmap_def] \\ SIMP_TAC std_ss [LET_DEF]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [true_listp_app] \\ FS []
  \\ Q.EXISTS_TAC `[]` \\ FS []);

val true_listp_logic_flag_callmap = prove(
  ``isTrue (true_listp (logic_flag_callmap x y z))``,
  ONCE_REWRITE_TAC [logic_flag_callmap_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC std_ss [true_listp_nil,true_listp_cons,true_listp_app]
  \\ FULL_SIMP_TAC std_ss [true_listp_logic_flag_callmap_list]);

val logic_flag_callmap_TERM = prove(
  ``(logic_flag_callmap (Sym "LIST") (Sym name) (Dot (t2sexp x) (Sym "NIL")) =
     callmap2sexp (callmap name x)) ==>
    (logic_flag_callmap (Sym "TERM") (Sym name) (t2sexp x) =
     callmap2sexp (callmap name x))``,
  SIMP_TAC std_ss [Once logic_flag_callmap_def] \\ FS []
  \\ Q.ABBREV_TAC `y = logic_flag_callmap (Sym "TERM") (Sym name) (t2sexp x)`
  \\ SIMP_TAC std_ss [Once logic_flag_callmap_def] \\ FS []
  \\ FS [callmap2sexp_def] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC app_EQ_list2sexp \\ ASM_SIMP_TAC std_ss []
  \\ Q.UNABBREV_TAC `y` \\ FS [true_listp_logic_flag_callmap]);

val t2sexp_mApp_mPrimitiveFun = prove(
  ``t2sexp (mApp (mPrimitiveFun logic_NOT) [x1]) =
    Dot (Sym "NOT") (Dot (t2sexp x1) (Sym "NIL"))``,
  EVAL_TAC);

val cons_onto_ranges_thm = prove(
  ``!xs. cons_onto_ranges (t2sexp x1) (callmap2sexp xs) =
         callmap2sexp (MAP (\(x,y). (x,x1::y)) xs)``,
  Induct THEN1 EVAL_TAC \\ Cases \\ FS [MAP,callmap2sexp_def]
  \\ ONCE_REWRITE_TAC [cons_onto_ranges_def] \\ FS []);

val logic_func2sexp_NEQ_IF = prove(
  ``func_syntax_ok l0 /\ ~(l0 = mPrimitiveFun logic_IF) ==>
    ~(logic_func2sexp l0 = Sym "IF")``,
  REPEAT STRIP_TAC \\ Cases_on `l0` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT (Cases_on `l`)
  \\ FULL_SIMP_TAC (srw_ss()) [logic_func2sexp_def,logic_prim2sym_def]
  \\ POP_ASSUM MP_TAC \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss []);

val sigmap2sexp_intro = add_prove(
  ``!xs ys.
      (LENGTH xs = LENGTH ys) ==>
      (list2sexp (CONS_ZIP (MAP Sym xs) (MAP t2sexp ys)) =
       sigmap2sexp (ZIP (xs, ys)) (Sym "NIL"))``,
  Induct \\ Cases_on `ys` \\ FS [LENGTH,ADD,ZIP,MAP,ADD1,CONS_ZIP_def]);

val logic_substitute_callmap_thm = prove(
  ``!ts xs.
      EVERY (EVERY term_syntax_ok o FST) ts /\
      EVERY (EVERY term_syntax_ok o SND) ts ==>
      (logic_substitute_callmap (callmap2sexp ts) (sigmap2sexp xs (Sym "NIL")) =
       callmap2sexp (callmap_sub xs ts))``,
  Induct \\ ONCE_REWRITE_TAC [logic_substitute_callmap_def]
  \\ FS [callmap2sexp_def,callmap_sub_def,MAP,EVERY_DEF] \\ Cases_on `h`
  \\ FS [callmap2sexp_def,callmap_sub_def,MAP,LET_DEF]
  \\ FS [logic_substitute_list_thm,isDot_def,GSYM MAP_MAP_o]);

val LOOKUP_IMP = prove(
  ``!xs. EVERY (P o SND) xs /\ P y ==> P (LOOKUP s xs y)``,
  Induct \\ SIMP_TAC std_ss [LOOKUP_def] \\ Cases
  \\ SIMP_TAC std_ss [LOOKUP_def,EVERY_DEF] \\ SRW_TAC [] [] \\ FS []);

val term_syntax_ok_term_sub = prove(
  ``term_syntax_ok t /\ EVERY (term_syntax_ok o SND) xs ==>
    term_syntax_ok (term_sub xs t)``,
  completeInduct_on `logic_term_size t` \\ NTAC 3 STRIP_TAC
  \\ FS [PULL_FORALL_IMP] \\ Cases_on `t`
  \\ FULL_SIMP_TAC std_ss [term_sub_def,term_syntax_ok_def,LENGTH_MAP]
  THEN1 (MATCH_MP_TAC LOOKUP_IMP \\ FULL_SIMP_TAC std_ss [term_syntax_ok_def])
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_EXISTS_IMP,AND_IMP_INTRO]
  \\ REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `!t. b1 /\ b2 ==> b3` MATCH_MP_TAC \\ FS []
  \\ EVAL_TAC \\ IMP_RES_TAC MEM_logic_term_size \\ DECIDE_TAC);

val logic_flag_callmap_thm = prove(
  ``!ts.
      EVERY term_syntax_ok ts /\ EVERY (term_ok ctxt) ts /\
      (logic_func2sexp (mFun name) = Sym name) ==>
      (logic_flag_callmap (Sym "LIST") (Sym name) (list2sexp (MAP t2sexp ts)) =
       callmap2sexp (FLAT (MAP (callmap name) ts))) /\
      EVERY (EVERY term_syntax_ok o FST) (FLAT (MAP (callmap name) ts)) /\
      EVERY (EVERY term_syntax_ok o SND) (FLAT (MAP (callmap name) ts)) /\
      EVERY (\x. LENGTH (FST x) = LENGTH (FST (ctxt ' name)))
            (FLAT (MAP (callmap name) ts))``,
  STRIP_TAC \\ completeInduct_on `logic_term1_size ts` \\ NTAC 3 STRIP_TAC
  \\ FS [PULL_FORALL_IMP] \\ Cases_on `ts`
  \\ ONCE_REWRITE_TAC [logic_flag_callmap_def]
  \\ FS [MAP,FLAT,callmap2sexp_def,MAP_APPEND,EVERY_DEF,EVERY_APPEND]
  \\ `logic_term1_size t < logic_term1_size (h::t)` by (EVAL_TAC \\ DECIDE_TAC)
  \\ sg `(logic_flag_callmap (Sym "TERM") (Sym name) (t2sexp h) =
       callmap2sexp (callmap name h)) /\
      EVERY (EVERY term_syntax_ok o FST) (callmap name h) /\
      EVERY (EVERY term_syntax_ok o SND) (callmap name h) /\
      EVERY (\x. LENGTH (FST x) = LENGTH (FST (ctxt ' name))) (callmap name h)`
  \\ FS [callmap2sexp_def]
  \\ ONCE_REWRITE_TAC [logic_flag_callmap_def] \\ FS [LET_DEF,MAP]
  \\ Cases_on `h` \\ FS [t2sexp_def,callmap_def,MAP,
       logic_variablep_def,term_syntax_ok_def,EVERY_DEF]
  THEN1
   (Cases_on `l0 = mPrimitiveFun logic_IF` THEN1
     (FS [logic_func2sexp_def,logic_prim2sym_def,GSYM callmap2sexp_def]
      \\ FS [func_syntax_ok_def,term_ok_def,func_arity_def,primitive_arity_def]
      \\ FS [LENGTH_MAP]
      \\ `?x1 x2 x3. l = [x1;x2;x3]` by
        (Cases_on `l` \\ FULL_SIMP_TAC std_ss [LENGTH]
         \\ Cases_on `t'` \\ FULL_SIMP_TAC std_ss [LENGTH]
         \\ Cases_on `t''` \\ FULL_SIMP_TAC std_ss [LENGTH]
         \\ Cases_on `t'` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
         \\ `F` by DECIDE_TAC)
      \\ FS [EVERY_DEF,MAP,EL,HD,TL,EVAL ``EL 1 (x1::x2::x3::xs)``,
           EVAL ``EL 2 (x1::x2::x3::xs)``]
      \\ Q.PAT_X_ASSUM `!ts.bbb` (fn th =>
           (MP_TAC o Q.SPEC `[x1]`) th THEN
           (MP_TAC o Q.SPEC `[x2]`) th THEN
           (MP_TAC o Q.SPEC `[x3]`) th)
      \\ FS [EVERY_DEF,MAP,FLAT,APPEND_NIL]
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC) \\ STRIP_TAC
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC) \\ STRIP_TAC
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC) \\ STRIP_TAC
      \\ IMP_RES_TAC logic_flag_callmap_TERM \\ FS []
      \\ FULL_SIMP_TAC std_ss [GSYM t2sexp_mApp_mPrimitiveFun,cons_onto_ranges_thm]
      \\ FS [callmap2sexp_def,MAP_APPEND] \\ FS [APPEND_ASSOC]
      \\ FS [EVERY_APPEND,EVERY_MAP]
      \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
      \\ FS [EVERY_DEF,term_syntax_ok_def,func_syntax_ok_def]
      \\ FS [o_DEF])
    \\ FS [logic_func2sexp_NEQ_IF]
    \\ Cases_on `l0 = mFun name` \\ FS [] THEN1
     (`(\a. callmap name a) = callmap name` by FULL_SIMP_TAC std_ss [FUN_EQ_THM]
      \\ FS [EVERY_DEF,MAP,term_ok_def,func_arity_def]
      \\ FS [MAP,AND_IMP_INTRO] \\ Q.PAT_X_ASSUM `!ts.bbb` MATCH_MP_TAC
      \\ FS [term_ok_def,EVERY_MEM,logic_term_size_def] \\ DECIDE_TAC)
    \\ `~(logic_func2sexp l0 = Sym name)` by
     (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ Cases_on `l0`
      \\ SIMP_TAC (srw_ss()) [logic_func2sexp_def]
      \\ REPEAT STRIP_TAC \\ FS [] THEN1
       (Q.PAT_X_ASSUM `logic_func2sexp (mFun (logic_prim2sym l')) =
                     Sym (logic_prim2sym l')` MP_TAC
        \\ Cases_on `l'` \\ EVAL_TAC)
      \\ POP_ASSUM MP_TAC \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [])
    \\ FS [] THEN1
     (`(\a. callmap name a) = callmap name` by FULL_SIMP_TAC std_ss [FUN_EQ_THM]
      \\ FS [MAP,AND_IMP_INTRO] \\ Q.PAT_X_ASSUM `!ts.bbb` MATCH_MP_TAC
      \\ FS [term_ok_def,EVERY_MEM,logic_term_size_def] \\ DECIDE_TAC))
  \\ Q.PAT_X_ASSUM `!ts.bbb` (fn th =>
           (MP_TAC o Q.SPEC `l0`) th THEN (MP_TAC o Q.SPEC `[l]`) th)
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,term_ok_def]
  \\ `EVERY (term_ok ctxt) l0` by FULL_SIMP_TAC std_ss [EVERY_MEM]
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,term_ok_def]
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC) \\ STRIP_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC) \\ STRIP_TAC
  \\ FS [MAP,GSYM callmap2sexp_def,FLAT,APPEND_NIL]
  \\ IMP_RES_TAC logic_flag_callmap_TERM \\ FS [EVERY_APPEND]
  \\ `(\a. callmap name a) = callmap name` by FULL_SIMP_TAC std_ss [FUN_EQ_THM]
  \\ FS [logic_substitute_callmap_thm] \\ FS [callmap2sexp_def,MAP_APPEND]
  \\ Q.PAT_X_ASSUM `EVERY (\x. LENGTH (FST x) = LENGTH (FST (ctxt ' name)))
         (callmap name l)` MP_TAC
  \\ Q.PAT_X_ASSUM `EVERY (EVERY term_syntax_ok o xx) (callmap name l)` MP_TAC
  \\ Q.PAT_X_ASSUM `EVERY (EVERY term_syntax_ok o xx) (callmap name l)` MP_TAC
  \\ Q.PAT_X_ASSUM `LENGTH l1 = LENGTH l0` MP_TAC
  \\ Q.PAT_X_ASSUM `EVERY (term_syntax_ok) l0` MP_TAC
  \\ Q.SPEC_TAC (`callmap name l`,`qs`)
  \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ FS [AND_IMP_INTRO]
  \\ FS [callmap_sub_def]
  \\ SIMP_TAC std_ss [EVERY_MEM,EXISTS_PROD,FORALL_PROD,
       MEM_MAP,PULL_EXISTS_IMP] \\ REPEAT STRIP_TAC \\ RES_TAC \\ FS []
  \\ FS [LENGTH_MAP,MEM_FLAT,MEM_MAP,PULL_EXISTS_IMP,PULL_CONJ]
  \\ MATCH_MP_TAC term_syntax_ok_term_sub \\ ASM_SIMP_TAC std_ss []
  \\ FS [EVERY_MEM,MEM_ZIP] \\ Cases \\ FS [] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC rich_listTheory.EL_IS_EL \\ RES_TAC \\ FS []);

val logic_callmap_thm = prove(
  ``term_syntax_ok t /\ term_ok ctxt t /\
    (logic_func2sexp (mFun name) = Sym name) ==>
    (logic_callmap (Sym name) (t2sexp t) =
       callmap2sexp (callmap name t)) /\
    EVERY (EVERY term_syntax_ok o FST) (callmap name t) /\
    EVERY (EVERY term_syntax_ok o SND) (callmap name t) /\
    EVERY (\x. LENGTH (FST x) = LENGTH (FST (ctxt ' name))) (callmap name t)``,
  STRIP_TAC \\ MP_TAC (Q.SPEC `[t]` logic_flag_callmap_thm)
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,MAP,FLAT,APPEND_NIL,logic_callmap_def]
  \\ REPEAT STRIP_TAC \\ FS []
  \\ IMP_RES_TAC logic_flag_callmap_TERM \\ FS []);

val logic_pequal_list_thm = add_prove(
  ``!xs ys.
      (LENGTH xs = LENGTH ys) ==>
      (logic_pequal_list (list2sexp (MAP t2sexp xs)) (list2sexp (MAP t2sexp ys)) =
       list2sexp (MAP (\ (x,y). f2sexp (Equal x y)) (ZIP(xs,ys))))``,
  Induct \\ Cases_on `ys` \\ ONCE_REWRITE_TAC [logic_pequal_list_def]
  \\ FS [MAP,LENGTH,ADD1,ZIP,f2sexp_def]);

val GENLIST_K_LENGTH = prove(
  ``!xs. GENLIST (K x) (LENGTH xs) = MAP (K x) xs``,
  Induct \\ FULL_SIMP_TAC std_ss [MAP,GENLIST,LENGTH]
  \\ POP_ASSUM (K ALL_TAC) \\ Induct_on `xs`
  \\ FULL_SIMP_TAC std_ss [MAP,GENLIST,LENGTH,SNOC]);

val logic_progress_obligation_thm = add_prove(
  ``(LENGTH formals = LENGTH actuals) /\ term_syntax_ok t ==>
    (logic_progress_obligation (t2sexp t) (list2sexp (MAP Sym formals))
                                          (list2sexp (MAP t2sexp actuals))
                                          (list2sexp (MAP t2sexp rulers)) =
     f2sexp (progress_obligation t formals (actuals,rulers)))``,
  SIMP_TAC std_ss [progress_obligation_def]
  \\ FS [logic_progress_obligation_def,LET_DEF,LENGTH_MAP,LENGTH_GENLIST]
  \\ `(GENLIST (K (Dot (Sym "QUOTE") (Dot (Sym "NIL") (Sym "NIL")))) (LENGTH rulers)) =
      MAP t2sexp (GENLIST (K (mConst (Sym "NIL"))) (LENGTH rulers))` by
         (FS [MAP_GENLIST,t2sexp_def])
  \\ FS [LENGTH_MAP,LENGTH_GENLIST]
  \\ FULL_SIMP_TAC std_ss [GSYM list2sexp_def]
  \\ SIMP_TAC std_ss [f2sexp_def,t2sexp_def,SIMP_RULE std_ss [NOT_CONS_NIL]
       (Q.SPEC `x::xs` (GSYM logic_disjoin_formulas_thm)),list2sexp_def,MAP,
       logic_func2sexp_def,MAP_MAP_o,o_DEF]
  \\ CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV))
  \\ FS [f2sexp_def,logic_prim2sym_def]
  \\ REPEAT STRIP_TAC \\ REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ FULL_SIMP_TAC std_ss [GENLIST_K_LENGTH]
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Induct_on `rulers`
  \\ FULL_SIMP_TAC std_ss [MAP,ZIP,FORALL_PROD,CONS_11,t2sexp_def,list2sexp_def]);

val logic_progress_obligations_thm = prove(
  ``!ts.
      EVERY (\t. LENGTH formals = LENGTH (FST t)) ts /\ term_syntax_ok t ==>
      (logic_progress_obligations (t2sexp t) (list2sexp (MAP Sym formals))
                                             (callmap2sexp ts) =
       list2sexp (MAP f2sexp (MAP (progress_obligation t formals) ts)))``,
  Induct \\ ONCE_REWRITE_TAC [logic_progress_obligations_def]
  \\ FS [MAP,callmap2sexp_def,EVERY_DEF] \\ Cases_on `h` \\ FS [LET_DEF]);

val logic_termination_obligations_thm = prove(
  ``term_syntax_ok m /\ term_syntax_ok body /\ term_ok ctxt body /\
    (LENGTH formals = LENGTH (FST (ctxt ' name))) /\
    (logic_func2sexp (mFun name) = Sym name) ==>
    (logic_termination_obligations (Sym name) (list2sexp (MAP Sym formals))
                                   (t2sexp body) (t2sexp m) =
     if (callmap name body = []) then Sym "NIL" else
       list2sexp (MAP f2sexp
         ((Equal (mApp (mPrimitiveFun logic_ORDP) [m]) (mConst (Sym "T")))::
          (MAP (progress_obligation m formals) (callmap name body)))))``,
  SIMP_TAC std_ss [logic_termination_obligations_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC logic_callmap_thm \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `callmap name body = []` THEN1 (FS [callmap2sexp_def,MAP]) \\ FS []
  \\ `isTrue (callmap2sexp (callmap name body))` by (Cases_on `callmap name body` \\ FS [] \\ Cases_on `h` \\ FS [] \\ EVAL_TAC)
  \\ FS [MAP,f2sexp_def] \\ STRIP_TAC THEN1 EVAL_TAC
  \\ `EVERY (\t. LENGTH formals = LENGTH (FST t)) (callmap name body)` suffices_by
  (STRIP_TAC THEN IMP_RES_TAC logic_progress_obligations_thm \\ FS [])
  \\ FS [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC);

val logic_termination_obligations_thm = prove(
  ``term_syntax_ok m /\ term_syntax_ok body /\ term_ok ctxt body /\
    (LENGTH formals = LENGTH (FST (ctxt ' name))) /\
    (logic_func2sexp (mFun name) = Sym name) ==>
    (logic_termination_obligations (Sym name) (list2sexp (MAP Sym formals))
                                   (t2sexp body) (t2sexp m) =
     list2sexp (MAP f2sexp (termination_obligations name body formals m)))``,
  SIMP_TAC std_ss [termination_obligations_def]
  \\ SIMP_TAC std_ss [logic_termination_obligations_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC logic_callmap_thm \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `callmap name body = []` THEN1 (FS [callmap2sexp_def,MAP]) \\ FS []
  \\ `isTrue (callmap2sexp (callmap name body))` by (Cases_on `callmap name body` \\ FS [] \\ Cases_on `h` \\ FS [] \\ EVAL_TAC)
  \\ FS [MAP,f2sexp_def] \\ STRIP_TAC THEN1 EVAL_TAC
  \\ `EVERY (\t. LENGTH formals = LENGTH (FST t)) (callmap name body)` by
       (FS [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC)
  \\ IMP_RES_TAC logic_progress_obligations_thm \\ FS []);

val IMP_isDot = prove(
  ``!x. ~isVal x /\ ~isSym x ==> isDot x``,
  Cases \\ EVAL_TAC);

val MEM_sexp2list_LSIZE = prove(
  ``!b a. MEM a (sexp2list b) ==> LSIZE a < LSIZE b``,
  Induct \\ SIMP_TAC std_ss [sexp2list_def,MEM,LSIZE_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ DECIDE_TAC);

val LSIZE_CAR_LESS = prove(
  ``!x m. LSIZE x < m ==> LSIZE (CAR x) < m``,
  Cases \\ SIMP_TAC std_ss [CAR_def,LSIZE_def] \\ DECIDE_TAC);

val LSIZE_CDR_LESS = prove(
  ``!x m. LSIZE x < m ==> LSIZE (CDR x) < m``,
  Cases \\ SIMP_TAC std_ss [CDR_def,LSIZE_def] \\ DECIDE_TAC);

val sexp3term_def = tDefine "sexp3term" `
  sexp3term x = if x = Sym "T" then Const x else
                if x = Sym "NIL" then Const x else
                if isVal x then Const x else
                if isSym x then Var (getSym x) else
                let x1 = CAR x in
                let x2 = CAR (CDR x) in
                let x3 = CAR (CDR (CDR x)) in
                let x4 = CAR (CDR (CDR (CDR x))) in
                if x1 = Sym "QUOTE" then Const x2 else
                if ~(sym2prim (getSym x1) = NONE) then
                  App (PrimitiveFun (THE (sym2prim (getSym x1))))
                    (MAP sexp3term (sexp2list (CDR x))) else
                if x1 = Sym "FIRST" then First (sexp3term x2) else
                if x1 = Sym "SECOND" then Second (sexp3term x2) else
                if x1 = Sym "THIRD" then Third (sexp3term x2) else
                if x1 = Sym "FOURTH" then Fourth (sexp3term x2) else
                if x1 = Sym "FIFTH" then Fifth (sexp3term x2) else
                if x1 = Sym "OR" then Or (MAP sexp3term (sexp2list (CDR x))) else
                if x1 = Sym "AND" then And (MAP sexp3term (sexp2list (CDR x))) else
                if x1 = Sym "LIST" then List (MAP sexp3term (sexp2list (CDR x))) else
                if x1 = Sym "COND" then
                  Cond (MAP (\y. (sexp3term (CAR y), sexp3term (CAR (CDR y))))
                            (sexp2list (CDR x))) else
                if x1 = Sym "LET" then
                  Let (MAP (\y. (getSym (CAR y), sexp3term (CAR (CDR y))))
                           (sexp2list x2)) (sexp3term x3) else
                if x1 = Sym "LET*" then
                  LetStar (MAP (\y. (getSym (CAR y), sexp3term (CAR (CDR y))))
                               (sexp2list x2)) (sexp3term x3) else
                if CAR x1 = Sym "LAMBDA" then
                  let y2 = CAR (CDR x1) in
                  let y3 = CAR (CDR (CDR x1)) in
                    LamApp (MAP getSym (sexp2list y2)) (sexp3term y3)
                           (MAP sexp3term (sexp2list (CDR x)))
                else (* user-defined fun *)
                  App (Fun (getSym x1))
                    (MAP sexp3term (sexp2list (CDR x)))`
 (WF_REL_TAC `measure LSIZE`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC IMP_isDot
  \\ FULL_SIMP_TAC std_ss [isDot_thm,LSIZE_def,CDR_def,CAR_def]
  \\ IMP_RES_TAC MEM_sexp2list_LSIZE
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [CDR_def]
  \\ REPEAT STRIP_TAC
  \\ REPEAT (MATCH_MP_TAC LSIZE_CAR_LESS)
  \\ REPEAT (MATCH_MP_TAC LSIZE_CDR_LESS) \\ REPEAT DECIDE_TAC
  \\ Cases_on `b` \\ FULL_SIMP_TAC std_ss [CAR_def,LSIZE_def] \\ DECIDE_TAC);

val sexp2sexp_def = Define `
  sexp2sexp x = t2sexp (term2t (sexp3term x))`;

val list_exists3 = prove(
  ``!x. list_exists 3 x ==> ?x1 x2 x3. x = list2sexp [x1;x2;x3]``,
  Cases \\ FS [] \\ Cases_on `S0` \\ FS []
  \\ Cases_on `S0'` \\ FS [] \\ Cases_on `S0` \\ FS []);

val isTrue_logic_flag_translate_TERM = prove(
  ``(isTrue (CAR (logic_flag_translate (Sym "LIST") (Dot x3 (Sym "NIL")))) =
     isTrue (logic_flag_translate (Sym "TERM") x3))``,
  SIMP_TAC std_ss [Once logic_flag_translate_def] \\ FS [LET_DEF]
  \\ Cases_on `isTrue (logic_flag_translate (Sym "TERM") x3)` \\ FS []
  \\ SIMP_TAC std_ss [Once logic_flag_translate_def] \\ FS [LET_DEF])

val logic_flag_translate_TERM = prove(
  ``isTrue (logic_flag_translate (Sym "TERM") x3) ==>
    (logic_flag_translate (Sym "LIST") (Dot x3 (Sym "NIL")) =
     Dot (Sym "T") (Dot (logic_flag_translate (Sym "TERM") x3) (Sym "NIL")))``,
  STRIP_TAC \\ SIMP_TAC std_ss [Once logic_flag_translate_def] \\ FS [LET_DEF]
  \\ SIMP_TAC std_ss [Once logic_flag_translate_def] \\ FS [LET_DEF]
  \\ SIMP_TAC std_ss [EVAL ``logic_flag_translate (Sym "LIST") (Sym "NIL")``]
  \\ FS []);

val sexp2list_list2sexp = add_prove(
  ``!xs. sexp2list (list2sexp xs) = xs``,
  Induct \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss []);

val logic_variable_listp_thm = add_prove(
  ``!xs. isTrue (logic_variable_listp (list2sexp xs)) ==>
         (MAP Sym (MAP getSym xs) = xs)``,
  Induct THEN1 EVAL_TAC
  \\ ONCE_REWRITE_TAC [logic_variable_listp_def] \\ FS [logic_variablep_def]
  \\ SRW_TAC [] [] \\ FS []
  \\ REPEAT (POP_ASSUM MP_TAC) \\ SRW_TAC [] [] \\ FS []
  \\ FULL_SIMP_TAC std_ss [isSym_thm] \\ FS [getSym_def]);

val logic_variable_listp_MAP_CAR = add_prove(
  ``!xs. isTrue (logic_variable_listp (list2sexp (MAP CAR xs))) ==>
         (MAP (\x. Sym (getSym (CAR x))) xs = MAP CAR xs)``,
  Induct THEN1 EVAL_TAC
  \\ ONCE_REWRITE_TAC [logic_variable_listp_def] \\ FS [logic_variablep_def]
  \\ FS [MAP] \\ SRW_TAC [] [] \\ FS []
  \\ REPEAT (POP_ASSUM MP_TAC) \\ SRW_TAC [] [] \\ FS []
  \\ FULL_SIMP_TAC std_ss [isSym_thm] \\ FS [getSym_def]);

val isTrue_memberp_rw = prove(
  ``isTrue (memberp (Sym name) (Dot (Sym x) y)) =
    (name = x) \/ isTrue (memberp (Sym name) y)``,
  SIMP_TAC std_ss [Once memberp_def] \\ FS [] \\ SRW_TAC [] [] \\ FS []);

val logic_translate_cond_term_thm = prove(
  ``!xs.
      EVERY (\x. term_vars_ok (term2t (sexp3term x))) (MAP (CAR o CDR) xs) /\
      EVERY (\x. term_vars_ok (term2t (sexp3term x))) (MAP CAR xs) ==>
      (logic_translate_cond_term (list2sexp (MAP sexp2sexp (MAP CAR xs)))
        (list2sexp (MAP sexp2sexp (MAP (CAR o CDR) xs))) =
       t2sexp (term2t
            (Cond (MAP (\y. (sexp3term (CAR y),sexp3term (CAR (CDR y)))) xs)))) /\
       term_vars_ok (term2t
            (Cond (MAP (\y. (sexp3term (CAR y),sexp3term (CAR (CDR y)))) xs)))``,
  Induct THEN1 EVAL_TAC
  \\ FS [MAP] \\ ONCE_REWRITE_TAC [logic_translate_cond_term_def]
  \\ FS [term2t_def,t2sexp_def,MAP,LET_DEF]
  \\ FS [sexp2sexp_def,EVERY_DEF,term_vars_ok_def] \\ NTAC 2 STRIP_TAC \\ EVAL_TAC);

val LIST_LSIZE_MAP = prove(
  ``!xs. LIST_LSIZE (MAP (CAR o CDR) xs) <= LSIZE (list2sexp xs) /\
         LIST_LSIZE (MAP (CAR) xs) <= LSIZE (list2sexp xs)``,
  Induct \\ EVAL_TAC \\ REPEAT STRIP_TAC
  \\ Cases_on `h` \\ EVAL_TAC \\ TRY (Cases_on `S0`) \\ EVAL_TAC \\ DECIDE_TAC);

val MAP_sexp2sexp = prove(
  ``!xs. MAP t2sexp (MAP term2t (MAP sexp3term xs)) = MAP sexp2sexp xs``,
  Induct \\ ASM_SIMP_TAC std_ss [MAP,CONS_11,sexp2sexp_def]);

val EVERY_MAP_ID = prove(
  ``!xs f P. (!x. P x ==> (f x = x)) /\ EVERY P xs ==> (xs = MAP f xs)``,
  Induct \\ SRW_TAC [] [] \\ METIS_TAC []);

val EVERY_ISORT_INSERT = prove(
  ``!xs f P. EVERY P xs /\ P h ==> EVERY P (ISORT_INSERT f h xs)``,
  Induct \\ SRW_TAC [] [ISORT_INSERT_def]);

val EVERY_ISORT = prove(
  ``!xs f P. EVERY P xs ==> EVERY P (ISORT f xs)``,
  Induct \\ SRW_TAC [] [ISORT_def,EVERY_ISORT_INSERT]);

val EVERY_FILTER = prove(
  ``!xs f P. EVERY P xs ==> EVERY P (FILTER f xs)``,
  Induct \\ SRW_TAC [] [FILTER]);

val EVERY_REMOVE_DUPLICATES = prove(
  ``!xs P. EVERY P xs ==> EVERY P (REMOVE_DUPLICATES xs)``,
  Induct \\ SRW_TAC [] [REMOVE_DUPLICATES_def]);

val EVERY_FLAT = prove(
  ``!xs P. EVERY P (FLAT xs) = !x. MEM x xs ==> EVERY P x``,
  Induct \\ FS [MEM,FLAT,EVERY_DEF,EVERY_APPEND] \\ METIS_TAC []);

val EVERY_free_vars = prove(
  ``!y. term_vars_ok y ==> EVERY (\x. x <> "NIL" /\ x <> "T") (free_vars y)``,
  STRIP_TAC \\ completeInduct_on `logic_term_size y` \\ NTAC 3 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL_IMP,AND_IMP_INTRO] \\ Cases_on `y`
  \\ FS [free_vars_def,EVERY_DEF,term_vars_ok_def,EVERY_FLAT,MEM_MAP,PULL_EXISTS_IMP]
  \\ REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `!y.bbb` MATCH_MP_TAC \\ FS [EVERY_MEM]
  \\ EVAL_TAC \\ IMP_RES_TAC MEM_logic_term_size \\ DECIDE_TAC);

val logic_translate_let_term_apply = prove(
  ``!xs.
      isTrue (logic_variable_listp (list2sexp (MAP CAR xs))) ==>
      EVERY (\x. term_vars_ok (term2t (sexp3term (CAR (CDR x))))) xs ==>
      term_vars_ok y ==>
      (logic_translate_let_term (list2sexp (MAP CAR xs))
        (list2sexp (MAP (\x. sexp2sexp (CAR (CDR x))) xs))
          (t2sexp y) =
       t2sexp
         (let2t
           (MAP (\y. (getSym (CAR y),term2t (sexp3term (CAR (CDR y))))) xs) y)) /\
       term_vars_ok (let2t
           (MAP (\y. (getSym (CAR y),term2t (sexp3term (CAR (CDR y))))) xs) y)``,
  SIMP_TAC std_ss [term2t_def,MAP_MAP_o,o_DEF,let2t_def]
  \\ FS [logic_translate_let_term_def,LET_DEF,t2sexp_def]
  \\ FS [MAP_APPEND,MAP_MAP_o,o_DEF,GSYM sexp2sexp_def,t2sexp_def]
  \\ FS [APPEND_11] \\ REPEAT STRIP_TAC THEN1
   (MATCH_MP_TAC EVERY_MAP_ID \\ Q.EXISTS_TAC `isSym`
    \\ STRIP_TAC THEN1 (Cases \\ FS [getSym_def])
    \\ MATCH_MP_TAC EVERY_ISORT
    \\ MATCH_MP_TAC EVERY_FILTER
    \\ MATCH_MP_TAC EVERY_REMOVE_DUPLICATES
    \\ FS [EVERY_MEM,MEM_MAP,PULL_EXISTS_IMP])
  \\ FS [term_vars_ok_def,LENGTH_MAP,LENGTH_APPEND,EVERY_APPEND,EVERY_MAP]
  \\ MATCH_MP_TAC EVERY_ISORT
  \\ MATCH_MP_TAC EVERY_FILTER
  \\ MATCH_MP_TAC EVERY_REMOVE_DUPLICATES
  \\ FS [EVERY_MAP,getSym_def,EVERY_free_vars]);

val logic_translate_let_term_thm = prove(
  ``!xs.
      isTrue (logic_variable_listp (list2sexp (MAP CAR xs))) ==>
      EVERY (\x. term_vars_ok (term2t (sexp3term x))) (MAP (CAR o CDR) xs) ==>
      term_vars_ok (term2t y) ==>
      (logic_translate_let_term (list2sexp (MAP CAR xs))
         (list2sexp (MAP sexp2sexp (MAP (CAR o CDR) xs))) (t2sexp (term2t y)) =
       t2sexp
         (term2t
           (Let (MAP (\y. (getSym (CAR y),sexp3term (CAR (CDR y)))) xs)
             y))) /\
      term_vars_ok
         (term2t
           (Let (MAP (\y. (getSym (CAR y),sexp3term (CAR (CDR y)))) xs)
             y))``,
  REPEAT STRIP_TAC
  \\ FS [term2t_def,MAP_MAP_o,o_DEF,EVERY_MAP]
  \\ IMP_RES_TAC logic_translate_let_term_apply);

val logic_translate_let_term_lemma =
  logic_translate_let_term_thm |> SIMP_RULE std_ss [term2t_def]
  |> Q.SPEC `[x]` |> SIMP_RULE std_ss [MAP,list2sexp_def,CAR_def,CDR_def]
  |> ONCE_REWRITE_RULE [logic_variable_listp_def]
  |> ONCE_REWRITE_RULE [logic_variable_listp_def]
  |> DISCH ``isTrue (logic_variablep (CAR x))``
  |> SR [EVERY_DEF]

val logic_translate_let_term_alt = prove(
  ``term_vars_ok y /\ ~(v = "NIL") /\ ~(v = "T") /\
    term_vars_ok (term2t (sexp3term x)) ==>
     (t2sexp (let2t [(v,term2t (sexp3term x))] y) =
     logic_translate_let_term (Dot (Sym v) (Sym "NIL"))
        (Dot (t2sexp (term2t (sexp3term x))) (Sym "NIL")) (t2sexp y)) /\
    term_vars_ok (let2t [(getSym (Sym v),term2t (sexp3term x))] y)``,
  REPEAT STRIP_TAC
  \\ MP_TAC (Q.SPEC `[Dot (Sym v) (Dot x (Sym "NIL"))]` (logic_translate_let_term_apply))
  \\ FS [MAP,EVERY_DEF]
  \\ ONCE_REWRITE_TAC [logic_variable_listp_def]
  \\ ONCE_REWRITE_TAC [logic_variable_listp_def]
  \\ FS [MAP,logic_variablep_def]
  \\ SRW_TAC [] [] \\ FS [] \\ REPEAT (POP_ASSUM MP_TAC)
  \\ SRW_TAC [] [] \\ FS [sexp2sexp_def,getSym_def]);

val logic_translate_let__term_thm = prove(
  ``!xs.
       term_vars_ok (term2t (sexp3term y)) /\
       EVERY (\x. term_vars_ok (term2t (sexp3term x))) (MAP (CAR o CDR) xs) /\
       isTrue (logic_variable_listp (list2sexp (MAP CAR xs))) ==>
       (logic_translate_let__term (list2sexp (MAP CAR xs))
         (list2sexp (MAP sexp2sexp (MAP (CAR o CDR) xs))) (sexp2sexp y) =
       t2sexp
         (term2t
           (LetStar (MAP (\y. (getSym (CAR y),sexp3term (CAR (CDR y)))) xs)
             (sexp3term y)))) /\
       term_vars_ok
         (term2t
           (LetStar (MAP (\y. (getSym (CAR y),sexp3term (CAR (CDR y)))) xs)
             (sexp3term y)))``,
  Induct \\ SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [logic_translate_let__term_def]
  \\ FS [MAP,term2t_def,sexp2sexp_def]
  \\ ONCE_REWRITE_TAC [logic_variable_listp_def] \\ FS []
  \\ FS [GSYM AND_IMP_INTRO] \\ STRIP_TAC  \\ STRIP_TAC
  \\ FS [EVERY_DEF] \\ STRIP_TAC
  \\ Cases_on `isTrue (logic_variablep (CAR h))` \\ FS [] \\ STRIP_TAC \\ FS []
  \\ IMP_RES_TAC logic_translate_let_term_lemma
  \\ FULL_SIMP_TAC std_ss [sexp2sexp_def]);

val logic_translate_or_term_thm = prove(
  ``!xs.
      EVERY (\x. term_vars_ok (term2t (sexp3term x))) xs ==>
      (t2sexp (term2t (Or (MAP sexp3term xs))) =
       logic_translate_or_term (list2sexp (MAP sexp2sexp xs))) /\
      term_vars_ok (term2t (Or (MAP sexp3term xs)))``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [term2t_def] \\ Induct THEN1 EVAL_TAC
  \\ Cases_on `xs` THEN1
   (SIMP_TAC std_ss [MAP,or2t_def,list2sexp_def]
    \\ ONCE_REWRITE_TAC [logic_translate_or_term_def]
    \\ FS [LET_DEF,sexp2sexp_def,EVERY_DEF])
  \\ SIMP_TAC std_ss [MAP,or2t_def,list2sexp_def]
  \\ ONCE_REWRITE_TAC [logic_translate_or_term_def]
  \\ FS [LET_DEF,EVERY_DEF] \\ STRIP_TAC \\ STRIP_TAC
  \\ Cases_on `isTrue (logic_variablep (sexp2sexp h'))`
  \\ FS [sexp2sexp_def,logic_func2sexp_def,logic_prim2sym_def,t2sexp_def,MAP,
         term_vars_ok_def,EVERY_DEF,logic_func_distinct]
  \\ Cases_on `isTrue (logic_constantp (sexp2sexp h'))`
  \\ FS [sexp2sexp_def,logic_func2sexp_def,logic_prim2sym_def,t2sexp_def,MAP,
         term_vars_ok_def,EVERY_DEF,logic_func_distinct]
  \\ FS [logic_term_vars_thm,MEM_MAP]
  \\ SRW_TAC [] [] \\ FS []
  \\ ONCE_REWRITE_TAC [t2sexp_def]
  \\ FS [MAP,logic_func2sexp_def,logic_prim2sym_def,term_vars_ok_def,
         EVERY_DEF,logic_func_distinct]
  \\ MP_TAC (logic_translate_let_term_alt |> Q.INST [`v`|->`"SPECIAL-VAR-FOR-OR"`,
       `y`|->`(mApp (mPrimitiveFun logic_IF)
        [mVar "SPECIAL-VAR-FOR-OR"; mVar "SPECIAL-VAR-FOR-OR";
         or2t (term2t (sexp3term h)::MAP term2t (MAP sexp3term t))])`,
       `x`|->`h'`])
  \\ FS [term_vars_ok_def,logic_func_distinct,EVERY_DEF]
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ FS [t2sexp_def,MAP,term_vars_ok_def,getSym_def]
  \\ REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) \\ EVAL_TAC);

val logic_translate_list_term_thm = prove(
  ``!xs.
      EVERY (\x. term_vars_ok (term2t (sexp3term x))) xs ==>
      (t2sexp (term2t (List (MAP sexp3term xs))) =
       logic_translate_list_term (list2sexp (MAP sexp2sexp xs))) /\
      term_vars_ok (term2t (List (MAP sexp3term xs)))``,
  Induct_on `xs` THEN1 (EVAL_TAC \\ METIS_TAC [])
  \\ ONCE_REWRITE_TAC [term2t_def]
  \\ ONCE_REWRITE_TAC [logic_translate_list_term_def] \\ FS [sexp2sexp_def,MAP]
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF]
  \\ SIMP_TAC std_ss [term2t_def,t2sexp_def,MAP,list2sexp_def,
       term_vars_ok_def,EVERY_DEF,logic_func2sexp_def,logic_prim2sym_def]
  \\ FS [] \\ REPEAT STRIP_TAC \\ FS [] \\ POP_ASSUM MP_TAC \\ EVAL_TAC);

val logic_translate_and_term_thm = prove(
  ``!xs.
      EVERY (\x. term_vars_ok (term2t (sexp3term x))) xs ==>
      (t2sexp (term2t (And (MAP sexp3term xs))) =
       logic_translate_and_term (list2sexp (MAP sexp2sexp xs))) /\
      term_vars_ok (term2t (And (MAP sexp3term xs)))``,
  Induct_on `xs` THEN1 (EVAL_TAC \\ METIS_TAC [])
  \\ Cases_on `xs` \\ FS [MAP]
  \\ ONCE_REWRITE_TAC [term2t_def]
  \\ ONCE_REWRITE_TAC [logic_translate_and_term_def] \\ FS [sexp2sexp_def,MAP]
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF]
  \\ SIMP_TAC std_ss [term2t_def,t2sexp_def,MAP,list2sexp_def,
       term_vars_ok_def,EVERY_DEF] \\ REPEAT STRIP_TAC
  \\ FS [markerTheory.Abbrev_def,EVERY_DEF]
  \\ EVAL_TAC \\ POP_ASSUM MP_TAC \\ EVAL_TAC);

val logic_flag_translate_thm = prove(
  ``!xs.
      let res = logic_flag_translate (Sym "LIST") (list2sexp xs) in
       (isTrue (CAR res) ==> (res = Dot (Sym "T") (list2sexp (MAP sexp2sexp xs))) /\
                             EVERY (\x. term_vars_ok (term2t (sexp3term x))) xs)``,
  STRIP_TAC \\ completeInduct_on `LIST_LSIZE xs` \\ NTAC 2 STRIP_TAC
  \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [PULL_FORALL_IMP]
  \\ ONCE_REWRITE_TAC [logic_flag_translate_def] \\ FS [] THEN1 EVAL_TAC
  \\ REVERSE (Cases_on `isTrue (logic_flag_translate (Sym "TERM") h)`)
  \\ FS [LET_DEF]
  \\ Cases_on `isTrue (CAR (logic_flag_translate (Sym "LIST") (list2sexp t)))`
  \\ FS [] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ `LIST_LSIZE t < LIST_LSIZE (h::t)` by (EVAL_TAC \\ DECIDE_TAC)
  \\ RES_TAC \\ FS []
  \\ `let res = logic_flag_translate (Sym "TERM") h in
                 (isTrue res ==> Abbrev ((res = sexp2sexp h) /\
                    term_vars_ok (term2t (sexp3term h))))` suffices_by
  (STRIP_TAC THEN FS [LET_DEF,markerTheory.Abbrev_def])
  \\ REVERSE (Cases_on `h`) THEN1
   (ONCE_REWRITE_TAC [logic_flag_translate_def]
    \\ FS [LET_DEF,markerTheory.Abbrev_def]
    \\ SRW_TAC [] [] \\ EVAL_TAC \\ FS [] \\ EVAL_TAC \\ FS [isTrue_def])
  THEN1 (ONCE_REWRITE_TAC [logic_flag_translate_def] \\ FS [LET_DEF]
         \\ FS [LET_DEF,markerTheory.Abbrev_def] \\ EVAL_TAC)
  \\ ONCE_REWRITE_TAC [logic_flag_translate_def] \\ FS []
  \\ REVERSE (Cases_on `isSym S'`) \\ FS [LET_DEF] THEN1
   (SRW_TAC [] [] \\ FS []
    \\ IMP_RES_TAC list_exists3 \\ FS []
    \\ Q.PAT_X_ASSUM `!xss.bbb` (fn th => (MP_TAC o Q.SPEC `xs'`) th THEN
                                        (MP_TAC o Q.SPEC `[x3]`) th)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (EVAL_TAC \\ MP_TAC (Q.SPEC `xs'` LIST_LSIZE_LESS_EQ) \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC std_ss [] \\ FS []
    \\ FS [isTrue_logic_flag_translate_TERM]
    \\ FS [logic_flag_translate_TERM] \\ STRIP_TAC
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (EVAL_TAC \\ MP_TAC (Q.SPEC `xs'` LIST_LSIZE_LESS_EQ) \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FS [MAP]
    \\ SIMP_TAC std_ss [markerTheory.Abbrev_def] \\ STRIP_TAC
    \\ SIMP_TAC std_ss [sexp2sexp_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ SIMP_TAC std_ss [Once sexp3term_def]
    \\ FS [LET_DEF,getSym_def,EVAL ``sym2prim "NIL"``]
    \\ FS [term2t_def,t2sexp_def,sexp2list_list2sexp]
    \\ FS [term_vars_ok_def,EVERY_MAP,MAP_MAP_o,o_DEF,EVERY_DEF]
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ Induct_on `xs'` \\ FS [MAP,CONS_11] \\ FS [sexp2sexp_def])
  \\ SRW_TAC [] [] \\ FS []
  THEN1
   (SIMP_TAC std_ss [sexp2sexp_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ SIMP_TAC std_ss [markerTheory.Abbrev_def] \\ REPEAT STRIP_TAC
    \\ SIMP_TAC std_ss [Once sexp3term_def] \\ FS [LET_DEF,getSym_def]
    \\ FS [term2t_def,t2sexp_def] \\ Cases_on `S0` \\ FS []
    \\ Cases_on `S0'` \\ FS [term_vars_ok_def])
  THEN1
   (SIMP_TAC std_ss [Once sexp3term_def] \\ FS [LET_DEF,getSym_def]
    \\ SIMP_TAC std_ss [sexp2sexp_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ SIMP_TAC std_ss [Once sexp3term_def] \\ FS [LET_DEF,getSym_def]
    \\ FULL_SIMP_TAC (srw_ss()) [EVAL ``sym2prim "FIRST"``]
    \\ FS [term2t_def,t2sexp_def,logic_func2sexp_def,logic_prim2sym_def,MAP]
    \\ Cases_on `S0` \\ FS [] \\ Cases_on `S0'` \\ FS []
    \\ Q.PAT_X_ASSUM `!xs.bbb` (MP_TAC o Q.SPEC `[S']`)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC)
    \\ FS [isTrue_logic_flag_translate_TERM,MAP,logic_flag_translate_TERM]
    \\ SIMP_TAC std_ss [sexp2sexp_def,markerTheory.Abbrev_def,term_vars_ok_def,
          EVERY_DEF] \\ STRIP_TAC \\ EVAL_TAC)
  THEN1
   (SIMP_TAC std_ss [Once sexp3term_def] \\ FS [LET_DEF,getSym_def]
    \\ SIMP_TAC std_ss [sexp2sexp_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ SIMP_TAC std_ss [Once sexp3term_def] \\ FS [LET_DEF,getSym_def]
    \\ FULL_SIMP_TAC (srw_ss()) [EVAL ``sym2prim "SECOND"``]
    \\ FS [term2t_def,t2sexp_def,logic_func2sexp_def,logic_prim2sym_def,MAP]
    \\ Cases_on `S0` \\ FS [] \\ Cases_on `S0'` \\ FS []
    \\ Q.PAT_X_ASSUM `!xs.bbb` (MP_TAC o Q.SPEC `[S']`)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC)
    \\ FS [isTrue_logic_flag_translate_TERM,MAP,logic_flag_translate_TERM]
    \\ SIMP_TAC std_ss [sexp2sexp_def,markerTheory.Abbrev_def,term_vars_ok_def,
          EVERY_DEF] \\ STRIP_TAC \\ EVAL_TAC)
  THEN1
   (SIMP_TAC std_ss [Once sexp3term_def] \\ FS [LET_DEF,getSym_def]
    \\ SIMP_TAC std_ss [sexp2sexp_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ SIMP_TAC std_ss [Once sexp3term_def] \\ FS [LET_DEF,getSym_def]
    \\ FULL_SIMP_TAC (srw_ss()) [EVAL ``sym2prim "THIRD"``]
    \\ FS [term2t_def,t2sexp_def,logic_func2sexp_def,logic_prim2sym_def,MAP]
    \\ Cases_on `S0` \\ FS [] \\ Cases_on `S0'` \\ FS []
    \\ Q.PAT_X_ASSUM `!xs.bbb` (MP_TAC o Q.SPEC `[S']`)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC)
    \\ FS [isTrue_logic_flag_translate_TERM,MAP,logic_flag_translate_TERM]
    \\ SIMP_TAC std_ss [sexp2sexp_def,markerTheory.Abbrev_def,term_vars_ok_def,
          EVERY_DEF] \\ STRIP_TAC \\ EVAL_TAC)
  THEN1
   (SIMP_TAC std_ss [Once sexp3term_def] \\ FS [LET_DEF,getSym_def]
    \\ SIMP_TAC std_ss [sexp2sexp_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ SIMP_TAC std_ss [Once sexp3term_def] \\ FS [LET_DEF,getSym_def]
    \\ FULL_SIMP_TAC (srw_ss()) [EVAL ``sym2prim "FOURTH"``]
    \\ FS [term2t_def,t2sexp_def,logic_func2sexp_def,logic_prim2sym_def,MAP]
    \\ Cases_on `S0` \\ FS [] \\ Cases_on `S0'` \\ FS []
    \\ Q.PAT_X_ASSUM `!xs.bbb` (MP_TAC o Q.SPEC `[S']`)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC)
    \\ FS [isTrue_logic_flag_translate_TERM,MAP,logic_flag_translate_TERM]
    \\ SIMP_TAC std_ss [sexp2sexp_def,markerTheory.Abbrev_def,term_vars_ok_def,
          EVERY_DEF] \\ STRIP_TAC \\ EVAL_TAC)
  THEN1
   (FULL_SIMP_TAC std_ss [GSYM list2sexp_def,memberp_thm] \\ FS []
    \\ SIMP_TAC std_ss [Once sexp3term_def] \\ FS [LET_DEF,getSym_def]
    \\ SIMP_TAC std_ss [sexp2sexp_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ SIMP_TAC std_ss [Once sexp3term_def] \\ FS [LET_DEF,getSym_def]
    \\ FULL_SIMP_TAC (srw_ss()) [EVAL ``sym2prim "FIFTH"``]
    \\ FS [term2t_def,t2sexp_def,logic_func2sexp_def,logic_prim2sym_def,MAP]
    \\ Cases_on `S0` \\ FS [] \\ Cases_on `S0'` \\ FS []
    \\ Q.PAT_X_ASSUM `!xs.bbb` (MP_TAC o Q.SPEC `[S'']`)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC)
    \\ FS [isTrue_logic_flag_translate_TERM,MAP,logic_flag_translate_TERM]
    \\ SIMP_TAC std_ss [sexp2sexp_def,markerTheory.Abbrev_def,term_vars_ok_def,
          EVERY_DEF] \\ STRIP_TAC \\ EVAL_TAC)
  THEN1
   (Q.PAT_X_ASSUM `!xss.bbb` (MP_TAC o Q.SPEC `xs`)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (EVAL_TAC \\ MP_TAC (Q.SPEC `xs` LIST_LSIZE_LESS_EQ) \\ DECIDE_TAC)
    \\ FS [] \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ SIMP_TAC std_ss [Once sexp3term_def] \\ FS [LET_DEF,getSym_def]
    \\ SIMP_TAC std_ss [sexp2sexp_def]
    \\ SIMP_TAC std_ss [Once sexp3term_def] \\ FS [LET_DEF,getSym_def]
    \\ FULL_SIMP_TAC (srw_ss()) [EVAL ``sym2prim "AND"``]
    \\ POP_ASSUM MP_TAC
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ FS [markerTheory.Abbrev_def]
    \\ FS [logic_translate_and_term_thm])
  THEN1
   (Q.PAT_X_ASSUM `!xss.bbb` (MP_TAC o Q.SPEC `xs`)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (EVAL_TAC \\ MP_TAC (Q.SPEC `xs` LIST_LSIZE_LESS_EQ) \\ DECIDE_TAC)
    \\ FS [] \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ SIMP_TAC std_ss [Once sexp3term_def] \\ FS [LET_DEF,getSym_def]
    \\ SIMP_TAC std_ss [sexp2sexp_def]
    \\ SIMP_TAC std_ss [Once sexp3term_def] \\ FS [LET_DEF,getSym_def]
    \\ FULL_SIMP_TAC (srw_ss()) [EVAL ``sym2prim "OR"``]
    \\ FS [markerTheory.Abbrev_def]
    \\ FS [logic_translate_or_term_thm])
  THEN1
   (FULL_SIMP_TAC std_ss [GSYM list2sexp_def,memberp_thm] \\ FS []
    \\ Q.PAT_X_ASSUM `!xss.bbb` (MP_TAC o Q.SPEC `xs`)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (EVAL_TAC \\ MP_TAC (Q.SPEC `xs` LIST_LSIZE_LESS_EQ) \\ DECIDE_TAC)
    \\ FS [] \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ SIMP_TAC std_ss [Once sexp3term_def] \\ FS [LET_DEF,getSym_def]
    \\ SIMP_TAC std_ss [sexp2sexp_def]
    \\ SIMP_TAC std_ss [Once sexp3term_def] \\ FS [LET_DEF,getSym_def]
    \\ FULL_SIMP_TAC (srw_ss()) [EVAL ``sym2prim "LIST"``]
    \\ FS [markerTheory.Abbrev_def]
    \\ FS [logic_translate_list_term_thm])
  THEN1
   (SIMP_TAC std_ss [sexp2sexp_def] \\ ONCE_REWRITE_TAC [sexp3term_def]
    \\ FS [LET_DEF] \\ FULL_SIMP_TAC (srw_ss()) [getSym_def,sym2prim_def]
    \\ Q.PAT_X_ASSUM `!ts.bbb` (fn th => (MP_TAC o Q.SPEC `MAP CAR xs`) th THEN
                                       (MP_TAC o Q.SPEC `MAP (CAR o CDR) xs`) th)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (EVAL_TAC \\ MP_TAC (Q.SPEC `xs` LIST_LSIZE_MAP) \\ DECIDE_TAC)
    \\ FS [] \\ STRIP_TAC
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (EVAL_TAC \\ MP_TAC (Q.SPEC `xs` LIST_LSIZE_MAP) \\ DECIDE_TAC)
    \\ FS [markerTheory.Abbrev_def]
    \\ FS [] \\ STRIP_TAC \\ FS [logic_translate_cond_term_thm])
  THEN1
   (SIMP_TAC std_ss [sexp2sexp_def] \\ ONCE_REWRITE_TAC [sexp3term_def]
    \\ FS [LET_DEF] \\ FULL_SIMP_TAC (srw_ss()) [getSym_def,sym2prim_def]
    \\ Cases_on `S0` \\ FS [] \\ Cases_on `S0'` \\ FS [] \\ Cases_on `S0` \\ FS []
    \\ Q.PAT_X_ASSUM `!ts.bbb` (fn th =>
          (MP_TAC o Q.SPEC `MAP (CAR o CDR) xs`) th THEN
          (MP_TAC o Q.SPEC `[S'']`) th)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (EVAL_TAC \\ MP_TAC (Q.SPEC `xs` LIST_LSIZE_MAP) \\ DECIDE_TAC)
    \\ FS [isTrue_logic_flag_translate_TERM,logic_flag_translate_TERM,MAP]
    \\ STRIP_TAC \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (EVAL_TAC \\ MP_TAC (Q.SPEC `xs` LIST_LSIZE_MAP) \\ DECIDE_TAC)
    \\ FS [markerTheory.Abbrev_def,EVERY_DEF] \\ STRIP_TAC
    \\ FS [logic_translate_let_term_thm,sexp2sexp_def])
  THEN1
   (FULL_SIMP_TAC std_ss [GSYM list2sexp_def,memberp_thm,MEM] \\ FS []
    \\ SIMP_TAC std_ss [sexp2sexp_def] \\ ONCE_REWRITE_TAC [sexp3term_def]
    \\ FS [LET_DEF] \\ FULL_SIMP_TAC (srw_ss()) [getSym_def,sym2prim_def]
    \\ Cases_on `S0` \\ FS [] \\ Cases_on `S0'` \\ FS [] \\ Cases_on `S0` \\ FS []
    \\ Q.PAT_X_ASSUM `!ts.bbb` (fn th =>
          (MP_TAC o Q.SPEC `MAP (CAR o CDR) xs`) th THEN
          (MP_TAC o Q.SPEC `[S''']`) th)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (EVAL_TAC \\ DECIDE_TAC)
    \\ FS [isTrue_logic_flag_translate_TERM,logic_flag_translate_TERM,MAP]
    \\ STRIP_TAC \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (EVAL_TAC \\ MP_TAC (Q.SPEC `xs` LIST_LSIZE_MAP) \\ DECIDE_TAC)
    \\ FS [markerTheory.Abbrev_def,EVERY_DEF] \\ STRIP_TAC
    \\ FS [logic_translate_let__term_thm,sexp2sexp_def])
  THEN1
   (Q.PAT_X_ASSUM `!xx.bbb` (MP_TAC o Q.SPEC `xs`)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (EVAL_TAC \\ MP_TAC (Q.SPEC `xs` LIST_LSIZE_LESS_EQ) \\ DECIDE_TAC)
    \\ FS [] \\ REPEAT STRIP_TAC
    \\ `?name. S' = Sym name` by FS [isSym_thm]
    \\ FS [sexp2sexp_def]
    \\ ONCE_REWRITE_TAC [sexp3term_def] \\ FS [LET_DEF,getSym_def,isTrue_memberp_rw]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `sym2prim name` \\ FS [] \\ POP_ASSUM MP_TAC
    \\ SIMP_TAC std_ss [sym2prim_def] \\ SRW_TAC [] [] THEN1
     (ONCE_REWRITE_TAC [term2t_def,func2f_def]
      \\ FS [t2sexp_def,MAP_sexp2sexp,func2f_def]
      \\ SRW_TAC [] [] \\ ASM_SIMP_TAC std_ss [logic_func2sexp_def,logic_prim2sym_def]
      \\ FS [logic_function_namep_def,isTrue_memberp_rw]
      \\ FS [term_vars_ok_def,EVERY_MAP,MAP_MAP_o,o_DEF]
      \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss [markerTheory.Abbrev_def])
    \\ FS [GSYM MAP_sexp2sexp] \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss []
    \\ FS [term_vars_ok_def,EVERY_MAP,MAP_MAP_o,o_DEF]
    \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss [markerTheory.Abbrev_def]));

val logic_translate_thm = prove(
  ``isTrue (logic_translate x) ==> (logic_translate x = sexp2sexp x)``,
  SIMP_TAC std_ss [logic_translate_def] \\ REPEAT STRIP_TAC
  \\ MP_TAC (Q.SPEC `[x]` logic_flag_translate_thm)
  \\ FULL_SIMP_TAC std_ss [logic_flag_translate_TERM,LET_DEF,
      isTrue_logic_flag_translate_TERM,list2sexp_def] \\ FS [MAP]);


val lookup_safe_STEP = prove(
  ``lookup_safe (Sym name) (Dot (Dot (Sym k) x) y) =
      if name = k then (Dot (Sym k) x) else
        lookup_safe (Sym name) y``,
  SIMP_TAC std_ss [Once lookup_safe_def] \\ FS []);

val lookup_safe_init_ftbl_EXISTS = prove(
  ``MEM fname ["NOT"; "RANK"; "ORD<"; "ORDP"] ==>
    ?fparams raw_body.
      (list2sexp [Sym fname; list2sexp (MAP Sym fparams); raw_body] =
       lookup_safe (Sym fname) init_ftbl)``,
  SIMP_TAC std_ss [MEM] \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [milawa_initTheory.init_ftbl_def]
  \\ REWRITE_TAC [lookup_safe_STEP,CONS_11,NOT_CONS_NIL,NOT_NIL_CONS]
  \\ SIMP_TAC (srw_ss()) [] \\ FS [list2sexp_def]
  THEN1 (Q.EXISTS_TAC `["X"]` \\ FS [MAP,list2sexp_def])
  THEN1 (Q.EXISTS_TAC `["X"]` \\ FS [MAP,list2sexp_def])
  THEN1 (Q.EXISTS_TAC `["X";"Y"]` \\ FS [MAP,list2sexp_def])
  THEN1 (Q.EXISTS_TAC `["X"]` \\ FS [MAP,list2sexp_def]));

val set_MAP_SUBSET = add_prove(
  ``!xs ys. set (MAP Sym xs) SUBSET set (MAP Sym ys) = set xs SUBSET set ys``,
  SIMP_TAC std_ss [SUBSET_DEF,MEM_MAP]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ FS []
  \\ METIS_TAC [SExp_11,SExp_distinct]);

val logic_flag_termp_LIST = prove(
  ``!xs. isTrue (logic_flag_termp (Sym "LIST") (list2sexp xs)) =
         EVERY (\x. isTrue (logic_flag_termp (Sym "TERM") x)) xs``,
  Induct \\ SIMP_TAC std_ss [Once logic_flag_termp_def]
  \\ FS [EVERY_DEF] \\ Cases_on `isTrue (logic_flag_termp (Sym "TERM") h)` \\ FS []);

val logic_variablep_EQ_var_ok = prove(
  ``!h. isTrue (logic_variablep (Sym h)) = var_ok h``,
  SIMP_TAC std_ss [logic_variablep_def] \\ FS [] \\ REPEAT STRIP_TAC
  \\ Cases_on `h = "T"` \\ FS [var_ok_def]);

val logic_variable_listp_EQ_var_ok = prove(
  ``!xs. isTrue (logic_variable_listp (list2sexp (MAP Sym xs))) = EVERY var_ok xs``,
  Induct \\ SIMP_TAC std_ss [Once logic_variable_listp_def]
  \\ FS [EVERY_DEF,MAP,logic_variablep_EQ_var_ok]
  \\ REPEAT STRIP_TAC \\ Cases_on `var_ok h` \\ FS []);

val term_syntax_ok_lemma = prove(
  ``!t. term_syntax_ok t ==>
        isTrue (logic_flag_termp (Sym "TERM") (t2sexp t))``,
  HO_MATCH_MP_TAC t2sexp_ind \\ REPEAT STRIP_TAC
  THEN1 (SIMP_TAC std_ss [t2sexp_def]
         \\ ONCE_REWRITE_TAC [logic_flag_termp_def]
         \\ FS [logic_variablep_def,term_syntax_ok_def,logic_constantp_def])
  THEN1 (SIMP_TAC std_ss [t2sexp_def]
         \\ ONCE_REWRITE_TAC [logic_flag_termp_def]
         \\ FS [logic_variablep_def,term_syntax_ok_def])
  THEN1 (SIMP_TAC std_ss [t2sexp_def]
         \\ ONCE_REWRITE_TAC [logic_flag_termp_def]
         \\ FS [logic_variablep_def,term_syntax_ok_def,LET_DEF]
         \\ Cases_on `isTrue (logic_flag_termp (Sym "LIST") (list2sexp (MAP t2sexp vs)))`
         \\ FS [] \\ FS [logic_flag_termp_LIST,EVERY_MEM,MEM_MAP] \\ METIS_TAC [])
  THEN1 (SIMP_TAC std_ss [t2sexp_def]
         \\ ONCE_REWRITE_TAC [logic_flag_termp_def]
         \\ FS [logic_variablep_def,term_syntax_ok_def,LET_DEF,LENGTH_MAP]
         \\ FS [logic_variable_listp_EQ_var_ok]
         \\ Cases_on `isTrue (logic_flag_termp (Sym "LIST") (list2sexp (MAP t2sexp ys)))`
         \\ FS [] \\ FS [logic_flag_termp_LIST,EVERY_MEM,MEM_MAP] \\ METIS_TAC []));

val term_syntax_ok_thm = prove(
  ``!t. term_syntax_ok t ==> isTrue (logic_termp (t2sexp t))``,
  SIMP_TAC std_ss [term_syntax_ok_lemma,logic_termp_def]);

val formula_syntax_ok_thm = prove(
  ``!t. formula_syntax_ok t ==> isTrue (logic_formulap (f2sexp t))``,
  Induct \\ FS [formula_syntax_ok_def,f2sexp_def]
  \\ ONCE_REWRITE_TAC [logic_formulap_def] \\ FS []
  \\ FULL_SIMP_TAC (srw_ss()) [term_syntax_ok_thm]);

val list2sexp_11 = prove(
  ``!xs ys. (list2sexp xs = list2sexp ys) = (xs = ys)``,
  Induct \\ Cases_on `ys` \\ FS []);

val logic_flag_appealp_LIST = prove(
  ``!xs. isTrue (logic_flag_appealp (Sym "LIST") (list2sexp xs)) =
         EVERY (\x. isTrue (logic_flag_appealp (Sym "PROOF") x)) xs``,
  Induct \\ SIMP_TAC std_ss [Once logic_flag_appealp_def]
  \\ FS [EVERY_DEF] \\ FULL_SIMP_TAC (srw_ss()) [] \\ FS []
  \\ Cases_on `isTrue (logic_flag_appealp (Sym "PROOF") h)` \\ FS []);

val appeal_syntax_ok_thm = prove(
  ``!t. appeal_syntax_ok t ==> isTrue (logic_appealp (a2sexp t))``,
  HO_MATCH_MP_TAC (fetch "-" "a2sexp_ind") \\ REPEAT STRIP_TAC
  \\ Cases_on `subproofs_extras`
  \\ FS [appeal_syntax_ok_def,a2sexp_def,LET_DEF]
  \\ REPEAT STRIP_TAC \\ FS [APPEND]
  \\ ONCE_REWRITE_TAC [logic_appealp_def] \\ FS []
  \\ ONCE_REWRITE_TAC [logic_flag_appealp_def] \\ FS []
  \\ SIMP_TAC std_ss [GSYM list2sexp_def,list2sexp_11]
  \\ ASM_SIMP_TAC std_ss [len_thm,getVal_def,LENGTH,formula_syntax_ok_thm]
  THEN1 EVAL_TAC \\ Cases_on `SND x` \\ FS [LENGTH]
  \\ FS [logic_flag_appealp_LIST,EVERY_MEM,MEM_MAP,PULL_EXISTS_IMP]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss [logic_appealp_def]);


(* Milawa's top-level invariant *)

val _ = add_rws [core_checker_def,core_axioms_def,core_thms_def,core_atbl_def,core_ftbl_def]

val core_check_proof_inv_def = Define `
  core_check_proof_inv checker k =
    ?name.
      (checker = Sym name) /\
      !x1 x2 x3 x4 io ok. ?res ok2 io2.
         R_ap (Fun name,[x1;x2;x3;x4],ARB,k,io,ok) (res,k,io ++ io2,ok2) /\
         (ok2 ==> (io2 = "")) /\
         !proof axioms thms atbl ctxt.
            appeal_syntax_ok proof /\ atbl_ok ctxt atbl /\
            thms_inv ctxt thms /\ thms_inv ctxt axioms /\
            isTrue res /\ (x1 = a2sexp proof) /\
            (x2 = list2sexp (MAP f2sexp axioms)) /\
            (x3 = list2sexp (MAP f2sexp thms)) /\ (x4 = atbl) /\ ok2 ==>
            MilawaTrue ctxt (CONCL proof)`;

val core_check_proof_inv_init = prove(
  ``core_check_proof_inv (Sym "LOGIC.PROOFP") core_funs``,
  SIMP_TAC (srw_ss()) [core_check_proof_inv_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `logic_proofp x1 x2 x3 x4` \\ Q.EXISTS_TAC `ok`
  \\ Q.EXISTS_TAC `""` \\ SIMP_TAC std_ss [APPEND_NIL]
  \\ STRIP_TAC THEN1
   (MATCH_MP_TAC R_ev_logic_proofp
    \\ SIMP_TAC std_ss [milawa_initTheory.core_assum_thm])
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC logic_proofp_thm);

val add_def_lemma = prove(
  ``(FDOM (add_def k x) = FDOM k UNION {FST x}) /\
    (add_def k x ' n = if n IN FDOM k then k ' n else
                       if n = FST x then SND x else FEMPTY ' n)``,
  Cases_on `x`
  \\ ASM_SIMP_TAC std_ss [SUBMAP_DEF,add_def_def,
    FUNION_DEF,FAPPLY_FUPDATE_THM,
    FDOM_FUPDATE,IN_UNION,FDOM_FUPDATE,
    FDOM_FEMPTY]);

val R_ev_SUBMAP = prove(
  ``(!x y. R_ap x y ==> (FST (SND (SND (SND x)))) SUBMAP (FST (SND y))) /\
    (!x y. R_evl x y ==> (FST (SND (SND x))) SUBMAP (FST (SND y))) /\
    (!x y. R_ev x y ==> (FST (SND (SND x))) SUBMAP (FST (SND y)))``,
  HO_MATCH_MP_TAC R_ev_ind \\ SIMP_TAC std_ss [FORALL_PROD,LET_DEF]
  \\ SIMP_TAC std_ss [SUBMAP_REFL] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC SUBMAP_TRANS \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [add_def_lemma,SUBMAP_DEF,IN_UNION]);

val R_ev_OK = prove(
  ``(!x y. R_ap x y ==> SND (SND (SND y)) ==> (SND (SND (SND (SND (SND x)))))) /\
    (!x y. R_evl x y ==> SND (SND (SND y)) ==> (SND (SND (SND (SND (x)))))) /\
    (!x y. R_ev x y ==> SND (SND (SND y)) ==> (SND (SND (SND (SND (x))))))``,
  HO_MATCH_MP_TAC R_ev_ind \\ SIMP_TAC std_ss [FORALL_PROD,LET_DEF]);

val PREFIX_def = Define `
  (PREFIX [] _ = T) /\
  (PREFIX (x::xs) (y::ys) = (x = y) /\ PREFIX xs ys) /\
  (PREFIX (x::xs) [] = F)`;

val PREFIX_REFL = prove(
  ``!xs. PREFIX xs xs``,
  Induct \\ ASM_SIMP_TAC std_ss [PREFIX_def]);

val PREFIX_ANTISYM = prove(
  ``!xs ys. PREFIX xs ys /\ PREFIX ys xs = (xs = ys)``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [PREFIX_def] \\ METIS_TAC []);

val PREFIX_TRANS = prove(
  ``!xs ys zs. PREFIX xs ys /\ PREFIX ys zs ==> PREFIX xs zs``,
  Induct \\ Cases_on `ys` \\ Cases_on `zs`
  \\ FULL_SIMP_TAC (srw_ss()) [PREFIX_def] \\ METIS_TAC []);

val PREFIX_APPEND = prove(
  ``!xs ys. PREFIX xs (xs ++ ys)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [PREFIX_def,APPEND] \\ METIS_TAC []);

val R_ev_PREFIX = prove(
  ``(!x y. R_ap x y ==> PREFIX (FST (SND (SND (SND (SND x))))) (FST (SND (SND y)))) /\
    (!x y. R_evl x y ==> PREFIX (FST (SND (SND (SND x)))) (FST (SND (SND y)))) /\
    (!x y. R_ev x y ==> PREFIX (FST (SND (SND (SND x)))) (FST (SND (SND y))))``,
  HO_MATCH_MP_TAC R_ev_ind \\ SIMP_TAC std_ss [FORALL_PROD,LET_DEF]
  \\ SIMP_TAC std_ss [PREFIX_REFL] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC PREFIX_TRANS \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,PREFIX_APPEND]);

val add_def_SUBMAP = prove(
  ``add_def fns (x,y) SUBMAP fns ==> x IN FDOM fns``,
  ASM_SIMP_TAC std_ss [SUBMAP_DEF,add_def_lemma,
    IN_UNION,IN_INSERT,NOT_IN_EMPTY]);

val R_ev_induct = IndDefLib.derive_strong_induction(R_ev_rules,R_ev_ind);

val R_ev_add_def = prove(
  ``(!x y. R_ap x y ==>
       let (f,args,env,k,io,ok) = x in
       let (res,k2,io2,ok2) = y in
         (k2 = k) ==>
         R_ap (f,args,env,add_def k d,io,ok) (res,add_def k2 d,io2,ok2)) /\
    (!x y. R_evl x y ==>
       let (e,env,k,io,ok) = x in
       let (res,k2,io2,ok2) = y in
         (k2 = k) ==>
         R_evl (e,env,add_def k d,io,ok) (res,add_def k2 d,io2,ok2)) /\
    (!x y. R_ev x y ==>
       let (e,env,k,io,ok) = x in
       let (res,k2,io2,ok2) = y in
         (k2 = k) ==>
         R_ev (e,env,add_def k d,io,ok) (res,add_def k2 d,io2,ok2))``,
  HO_MATCH_MP_TAC R_ev_induct \\ SIMP_TAC std_ss [FORALL_PROD,LET_DEF]
  \\ REVERSE (REPEAT STRIP_TAC)
  \\ ONCE_REWRITE_TAC [R_ev_cases] \\ ASM_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC R_ev_SUBMAP \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC SUBMAP_ANTISYM \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [add_def_lemma,IN_UNION]
  \\ IMP_RES_TAC add_def_SUBMAP \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [GSYM SUBMAP_ANTISYM]
  \\ SIMP_TAC std_ss [SUBMAP_DEF,add_def_lemma,IN_UNION,
       IN_INSERT,NOT_IN_EMPTY] \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ METIS_TAC []) |> SIMP_RULE std_ss [FORALL_PROD,LET_DEF];

val R_ap_add_def = prove(
  ``R_ap (f,args,env,k,io,ok) (res,k,io2,ok2) ==>
    R_ap (f,args,env,add_def k d,io,ok) (res,add_def k d,io2,ok2)``,
  METIS_TAC [R_ev_add_def]);

val core_check_proof_inv_step = prove(
  ``core_check_proof_inv name k ==>
    core_check_proof_inv name (add_def k new_def)``,
  SIMP_TAC std_ss [core_check_proof_inv_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL)
  \\ Q.LIST_EXISTS_TAC [`res`,`ok2`,`io2`] \\ REVERSE STRIP_TAC THEN1 METIS_TAC []
  \\ MATCH_MP_TAC R_ap_add_def \\ FULL_SIMP_TAC std_ss []);

val core_check_proof_inv_IMP_RAW = prove(
  ``core_check_proof_inv checker k ==>
    core_check_proof_side checker t axioms thms atbl k io ok /\
    (SND (SND (SND (core_check_proof checker t axioms thms atbl k io ok))) ==> ok /\
     (FST (SND (core_check_proof checker t axioms thms atbl k io ok)) = k) /\
     (FST (SND (SND (core_check_proof checker t axioms thms atbl k io ok))) = io))``,
  SIMP_TAC std_ss [core_check_proof_inv_def] \\ STRIP_TAC
  \\ REPEAT (POP_ASSUM MP_TAC) \\ STRIP_TAC \\ STRIP_TAC
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`t`,`axioms`,`thms`,`atbl`,`io`,`ok`])
  \\ `R_ap (Funcall,[Sym name; t; axioms; thms; atbl],ARB,k,io,ok) (res,k,io ++ io2,ok2)` by
   (POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
    \\ ONCE_REWRITE_TAC [R_ev_cases] \\ SIMP_TAC (srw_ss()) [] \\ METIS_TAC [])
  \\ SIMP_TAC std_ss [core_check_proof_side_def]
  \\ `funcall_ok [checker; t; axioms; thms; atbl] k io ok` by
       (SIMP_TAC std_ss [funcall_ok_def] \\ METIS_TAC [])
  \\ SIMP_TAC std_ss [core_check_proof_def]
  \\ ASM_SIMP_TAC std_ss [funcall_def]
  \\ Cases_on `ok2` THEN1
   (FULL_SIMP_TAC std_ss [] \\ Q.PAT_X_ASSUM `io2 = ""` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [APPEND_NIL]
    \\ `!x. R_ap (Funcall,[Sym name; t; axioms; thms; atbl],ARB,k,io,ok) x =
           (x = (res,k,io,T))` by METIS_TAC [R_ap_T_11]
    \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC R_ev_OK \\ FULL_SIMP_TAC std_ss [])
  \\ Q.ABBREV_TAC `xxx = (@result.
           R_ap (Funcall,[Sym name; t; axioms; thms; atbl],ARB,k,io,ok)
             result)`
  \\ `R_ap (Funcall,[Sym name; t; axioms; thms; atbl],ARB,k,io,ok) xxx` by METIS_TAC []
  \\ `?x1 x2 x3 b. xxx = (x1,x2,x3,b)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [R_ap_F_11]);

val core_check_proof_inv_IMP = prove(
  ``core_check_proof_inv checker k ==>
    core_check_proof_side checker t axioms thms atbl k io ok /\
    (SND (SND (SND (core_check_proof checker t axioms thms atbl k io ok))) ==>
      (FST (SND (core_check_proof checker t axioms thms atbl k io ok)) = k) /\
      (FST (SND (SND (core_check_proof checker t axioms thms atbl k io ok))) = io))``,
  METIS_TAC [core_check_proof_inv_IMP_RAW]);

val core_check_proof_inv_IMP_OK = prove(
  ``core_check_proof_inv checker k ==>
    (SND (SND (SND (core_check_proof checker t axioms thms atbl k io ok))) ==> ok)``,
  METIS_TAC [core_check_proof_inv_IMP_RAW]);

val core_check_proof_IMP_OK = prove(
  ``SND (SND (SND (core_check_proof checker proofs axioms thms atbl k io ok))) ==>
    ok``,
  SIMP_TAC std_ss [core_check_proof_def,funcall_def]
  \\ Cases_on `funcall_ok [checker; proofs; axioms; thms; atbl] k io ok`
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [funcall_ok_def]
  \\ Cases_on `ok` \\ FULL_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `xxx = R_ap (Funcall,[checker; proofs; axioms; thms; atbl],ARB,k,io,F)`
  \\ `xxx (@result. xxx result)` by METIS_TAC []
  \\ `?x1 x2 x3 x4. (@result. xxx result) = (x1,x2,x3,x4)` by METIS_TAC [PAIR]
  \\ Q.UNABBREV_TAC `xxx` \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC R_ev_OK \\ FULL_SIMP_TAC std_ss []);

val core_check_proof_list_IMP_OK = prove(
  ``!proofs k io ok.
      SND (SND (SND (core_check_proof_list checker proofs axioms thms atbl k io ok))) ==>
      ok``,
  REVERSE Induct \\ ONCE_REWRITE_TAC [core_check_proof_list_def]
  \\ SS [LET_DEF] \\ CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV))
  \\ Cases_on `isTrue (FST
                  (core_check_proof checker proofs axioms thms atbl k io ok))`
  \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ IMP_RES_TAC core_check_proof_IMP_OK);

val SUBMAP_core_check_proof = prove(
  ``k SUBMAP (FST (SND (core_check_proof checker t axioms thms atbl k io ok)))``,
  SIMP_TAC std_ss [core_check_proof_def,funcall_def]
  \\ Cases_on `funcall_ok [checker; t; axioms; thms; atbl] k io ok` \\ FS []
  \\ FULL_SIMP_TAC std_ss [SUBMAP_REFL]
  \\ FULL_SIMP_TAC std_ss [funcall_ok_def]
  \\ Q.ABBREV_TAC `xxx = (@result.
        R_ap (Funcall,[checker; t; axioms; thms; atbl],ARB,k,io,ok)
          result)`
  \\ `R_ap (Funcall,[checker; t; axioms; thms; atbl],ARB,k,io,ok) xxx` by METIS_TAC []
  \\ IMP_RES_TAC R_ev_SUBMAP \\ FULL_SIMP_TAC std_ss []);

val add_def_SUBMAP = prove(
  ``add_def fns (x,y,z) SUBMAP fns ==> x IN FDOM fns``,
  SIMP_TAC std_ss [SUBMAP_DEF,add_def_def,FUNION_DEF,FDOM_FUPDATE,
    FDOM_FEMPTY,FAPPLY_FUPDATE_THM,IN_UNION,IN_INSERT,NOT_IN_EMPTY]);

val add_def_EQ = prove(
  ``x IN FDOM k ==> (k = add_def k (x,y,z))``,
  SIMP_TAC std_ss [GSYM SUBMAP_ANTISYM]
  \\ SIMP_TAC std_ss [SUBMAP_DEF,add_def_def,FUNION_DEF,FDOM_FUPDATE,
    FDOM_FEMPTY,FAPPLY_FUPDATE_THM,IN_UNION,IN_INSERT,NOT_IN_EMPTY]
  \\ METIS_TAC []);

val SUBMAP_IMP_R_ev_lemma = prove(
  ``(!x y. R_ap x y ==>
       let (f,args,env,k,io,ok) = x in
       let (res,k2,io2,ok2) = y in
         !k3. (k = k2) /\ k SUBMAP k3 ==>
           R_ap (f,args,env,k3,io,ok) (res,k3,io2,ok2)) /\
    (!x y. R_evl x y ==>
       let (exp,env,k,io,ok) = x in
       let (res,k2,io2,ok2) = y in
         !k3. (k = k2) /\ k SUBMAP k3 ==>
           R_evl (exp,env,k3,io,ok) (res,k3,io2,ok2)) /\
    (!x y. R_ev x y ==>
       let (exp,env,k,io,ok) = x in
       let (res,k2,io2,ok2) = y in
         !k3. (k = k2) /\ k SUBMAP k3 ==>
           R_ev (exp,env,k3,io,ok) (res,k3,io2,ok2))``,
  HO_MATCH_MP_TAC R_ev_induct \\ SIMP_TAC std_ss [LET_DEF]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT (ONCE_REWRITE_TAC [R_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) []
             \\ IMP_RES_TAC R_ev_SUBMAP \\ FULL_SIMP_TAC std_ss []
             \\ IMP_RES_TAC SUBMAP_ANTISYM
             \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC
             \\ IMP_RES_TAC add_def_SUBMAP \\ FULL_SIMP_TAC std_ss []
             \\ METIS_TAC [SUBMAP_DEF,add_def_SUBMAP,add_def_EQ]))
  |> SIMP_RULE std_ss [FORALL_PROD,LET_DEF]

val SUBMAP_IMP_R_ev = prove(
  ``k SUBMAP k2 /\
    R_ap (f,args,env,k,io,ok) (res,k,io2,ok2) ==>
    R_ap (f,args,env,k2,io,ok) (res,k2,io2,ok2)``,
  METIS_TAC [SUBMAP_IMP_R_ev_lemma]);

val core_check_proof_list_inv_IMP_side = prove(
  ``!ok io k.
      core_check_proof_inv checker k ==>
      core_check_proof_list_side checker t axioms thms atbl k io ok``,
  REVERSE (Induct_on `t`)
  \\ ONCE_REWRITE_TAC [core_check_proof_list_def,core_check_proof_list_side_def]
  \\ FS [LET_DEF] \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ FULL_SIMP_TAC std_ss [core_check_proof_inv_IMP]
  \\ REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `!bb.bbb` MATCH_MP_TAC
  \\ Q.ABBREV_TAC `k2 = (FST (SND (core_check_proof checker t axioms thms atbl k io ok)))`
  \\ `k SUBMAP k2` by METIS_TAC [SUBMAP_core_check_proof]
  \\ FULL_SIMP_TAC std_ss [core_check_proof_inv_def]
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `!x1.bbb` (STRIP_ASSUME_TAC o Q.SPECL [`x1`,`x2`,`x3`,`x4`,`io'`,`ok'`])
  \\ Q.LIST_EXISTS_TAC [`res`,`ok2`,`io2`] \\ FULL_SIMP_TAC std_ss []
  \\ METIS_TAC [SUBMAP_IMP_R_ev]);

val core_check_proof_list_inv_IMP = prove(
  ``core_check_proof_inv checker k /\
    SND (SND (SND (core_check_proof_list checker t axioms thms atbl k io ok))) ==>
      (FST (SND (core_check_proof_list checker t axioms thms atbl k io ok)) = k) /\
      (FST (SND (SND (core_check_proof_list checker t axioms thms atbl k io ok))) = io)``,
  REVERSE (Induct_on `t`)
  \\ ONCE_REWRITE_TAC [core_check_proof_list_def,core_check_proof_list_side_def]
  \\ FS [LET_DEF] \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `isTrue (FST (core_check_proof checker t axioms thms atbl k io ok))`
  \\ FS [] \\ STRIP_TAC
  \\ IMP_RES_TAC core_check_proof_list_IMP_OK
  \\ IMP_RES_TAC core_check_proof_IMP_OK
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC core_check_proof_inv_IMP
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `ok` ASSUME_TAC \\ FULL_SIMP_TAC std_ss [])
  |> DISCH_ALL |> SIMP_RULE std_ss [];

val core_check_proof_list_inv_IMP_OK = prove(
  ``!ok. core_check_proof_inv checker k ==>
        (SND (SND (SND (core_check_proof_list checker t axioms thms atbl k io ok))) ==> ok)``,
  METIS_TAC [core_check_proof_list_IMP_OK]);

val ftbl_inv_def = Define `
  ftbl_inv k ftbl =
    (* every proper ftbl entry exists in the runtime *)
    EVERY (\x. if isTrue (CDR x) then
                 let name = getSym (CAR x) in
                 let formals = MAP getSym (sexp2list (CAR (CDR x))) in
                 let body = sexp2term (CAR (CDR (CDR x))) in
                   name IN FDOM k /\ (k ' name = (formals,body))
               else T)
          (sexp2list ftbl) /\
    (* a list of fake ftbl entries are present, the fake entries
       make it impossible to define functions with certain names
       using define-safe and admit-defun. *)
    EVERY (\s. lookup_safe (Sym s) ftbl = list2sexp [Sym s]) fake_ftbl_entries
    (* the initial content is present throughout execution *) /\
    (* all entries are conses and the keys are distinct *)
    EVERY isDot (sexp2list ftbl) /\ ALL_DISTINCT (MAP CAR (sexp2list ftbl)) /\
    (* the initial ftbl is at the bottom of the list *)
    ?old. FUNPOW CDR old ftbl = init_ftbl`;

val str2func_def = Define `
  str2func str = if str = "RANK" then mPrimitiveFun logic_RANK else
                 if str = "NOT" then mPrimitiveFun logic_NOT else
                 if str = "ORDP" then mPrimitiveFun logic_ORDP else
                 if str = "ORD<" then mPrimitiveFun logic_ORD_LESS else mFun str`;

val def_axiom_def = Define `
  (def_axiom name (params,BODY_FUN body,sem) =
     (Equal (mApp (str2func name) (MAP mVar params)) body)) /\
  (def_axiom name (params,WITNESS_FUN exp var_name,sem) =
     (Or (Equal exp (mConst (Sym "NIL")))
         (Not (Equal (mLamApp (var_name::params) exp
                              (mApp (str2func name) (MAP mVar params)::MAP mVar params))
                     (mConst (Sym "NIL"))))))`;

val func_definition_exists_def = Define `
  func_definition_exists ctxt name params body sem =
    name IN FDOM ctxt /\ (ctxt ' name = (params,body,sem)) \/
    ?raw_body.
      MEM name ["NOT";"RANK";"ORD<";"ORDP"] /\
      (list2sexp [Sym name; list2sexp (MAP Sym params); raw_body] =
         lookup_safe (Sym name) init_ftbl) /\
      (body = BODY_FUN (term2t (sexp3term raw_body)))`;

val logic_func_inv_def = Define `
  logic_func_inv name ctxt raw_body =
    (MEM name ["NOT";"RANK";"ORD<";"ORDP"] \/
     let logic_body = term2t (sexp3term raw_body) in
       !a. M_ev name (logic_body,a,ctxt) (EvalTerm (a,ctxt) logic_body))`;

val witness_body_def = Define `
  witness_body name var_name params raw_body =
    list2sexp [Sym "ERROR"; list2sexp [Sym "QUOTE";
      list2sexp [Sym name; Sym var_name; list2sexp (MAP Sym params); raw_body]]]`;

val axioms_aux_def = Define `
  (axioms_aux name ctxt axioms ftbl params sem (BODY_FUN body) =
     ?raw_body.
        (MEM (list2sexp [Sym name; list2sexp (MAP Sym params); raw_body]) (sexp2list ftbl)) /\
        (body = (term2t (sexp3term raw_body))) /\
        (MEM (def_axiom name (params,BODY_FUN body,sem)) axioms) /\
        logic_func_inv name ctxt raw_body /\ ~(CAR raw_body = Sym "ERROR")) /\
  (axioms_aux name ctxt axioms ftbl params sem (WITNESS_FUN body var_name) =
     ?raw_body.
        (MEM (list2sexp [Sym name; list2sexp (MAP Sym params);
                         witness_body name var_name params raw_body]) (sexp2list ftbl)) /\
        (body = (term2t (sexp3term raw_body))) /\
        (MEM (def_axiom name (params,WITNESS_FUN body var_name,sem)) axioms)) /\
  (axioms_aux name ctxt axioms ftbl params sem NO_FUN = F)`;

val axioms_inv_def = Define `
  axioms_inv ctxt ftbl axioms =
    EVERY (\x. ~(x IN FDOM ctxt)) ["NOT";"RANK";"ORDP";"ORD<"] /\
    !name params body sem.
      func_definition_exists ctxt name params body sem ==>
      axioms_aux name ctxt axioms ftbl params sem body`;

val atbl_ftbl_inv_def = Define `
  atbl_ftbl_inv atbl ftbl =
    !fname. isTrue (lookup (Sym fname) atbl) ==>
            MEM (Sym fname) (MAP CAR (sexp2list ftbl)) /\ ~(fname = "ERROR")`;

val atbl_inv_def = Define `
  atbl_inv atbl = EVERY (\x. isVal (CDR x)) (sexp2list atbl)`;

val context_inv_def = Define `
  context_inv ctxt =
    (!fname params body sem.
       fname IN FDOM ctxt /\ (ctxt ' fname = (params,BODY_FUN body,sem)) ==>
       (sem = EvalFun fname ctxt)) /\
    (!fname params var body sem.
       fname IN FDOM ctxt /\ (ctxt ' fname = (params,WITNESS_FUN body var,sem)) ==>
       (sem = \args.
         @v. isTrue (EvalTerm (FunVarBind (var::params) (v::args),ctxt) body)))`;

val context_syntax_same_def = Define `
  context_syntax_same ctxt simple_ctxt =
    (FDOM simple_ctxt = FDOM ctxt) /\
    FEVERY (\(name,formals,body,interp).
               name IN FDOM ctxt /\
               ?sem. ctxt ' name = (formals,body,sem)) simple_ctxt`;

val similar_context_def = Define `
  similar_context ctxt simple_ctxt =
    context_ok simple_ctxt /\ context_syntax_same ctxt simple_ctxt`
  |> REWRITE_RULE [context_syntax_same_def,GSYM CONJ_ASSOC];

val milawa_inv_def = Define `
  milawa_inv ctxt simple_ctxt k (axioms,thms,atbl,checker,ftbl) =
    context_ok ctxt /\ context_inv ctxt /\
    similar_context ctxt simple_ctxt /\
    atbl_ok ctxt atbl /\ atbl_inv atbl /\
    thms_inv ctxt thms /\ thms_inv ctxt axioms /\
    core_check_proof_inv checker k /\ ftbl_inv k ftbl /\
    axioms_inv ctxt ftbl axioms /\ atbl_ftbl_inv atbl ftbl /\
    runtime_inv ctxt k /\ core_assum k`;

val milawa_state_def = Define `
  milawa_state (axioms,thms,atbl,checker,ftbl) =
    core_state (list2sexp (MAP f2sexp axioms))
               (list2sexp (MAP f2sexp thms)) atbl checker ftbl`;

val DISJ_EQ_IMP = METIS_PROVE [] ``x \/ y = ~x ==> y``;


(* admit theorem *)

val Funcall_lemma = prove(
  ``R_ap (Fun name,xs,env,k,io,ok) res ==>
    R_ap (Funcall,(Sym name)::xs,env,k,io,ok) res``,
  ONCE_REWRITE_TAC [R_ev_cases]
  \\ SIMP_TAC (srw_ss()) [] \\ METIS_TAC []);

val core_check_proof_thm = prove(
  ``core_check_proof_inv checker k /\ appeal_syntax_ok t /\ atbl_ok ctxt atbl /\
    context_ok ctxt /\ thms_inv ctxt thms /\ thms_inv ctxt axioms /\
    SND (SND (SND (core_check_proof checker (a2sexp t)
                     (list2sexp (MAP f2sexp axioms))
                     (list2sexp (MAP f2sexp thms)) atbl k io ok))) /\
    isTrue (FST (core_check_proof checker (a2sexp t)
                  (list2sexp (MAP f2sexp axioms))
                  (list2sexp (MAP f2sexp thms)) atbl k io ok)) ==>
    MilawaTrue ctxt (CONCL t)``,
  REPEAT STRIP_TAC
  \\ STRIP_ASSUME_TAC (UNDISCH core_check_proof_inv_IMP |> CONJUNCT1 |> GEN_ALL)
  \\ FULL_SIMP_TAC std_ss [core_check_proof_inv_def]
  \\ FULL_SIMP_TAC std_ss [Once core_check_proof_side_def]
  \\ POP_ASSUM MP_TAC
  \\ Q.PAT_X_ASSUM `!(x1:SExp). bbb` (MP_TAC o Q.SPECL [`a2sexp t`,
       `list2sexp (MAP f2sexp axioms)`,
       `list2sexp (MAP f2sexp thms)`,`atbl`,`io`,`ok`])
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [core_check_proof_def,funcall_def]
  \\ Q.PAT_X_ASSUM `checker = Sym name` (ASSUME_TAC)
  \\ IMP_RES_TAC Funcall_lemma
  \\ Cases_on `ok2` THEN1
   (FULL_SIMP_TAC std_ss [APPEND_NIL]
    \\ Q.PAT_X_ASSUM `io2 = ""` ASSUME_TAC \\ FULL_SIMP_TAC std_ss [APPEND_NIL]
    \\ `!x. R_ap (Funcall,
         [Sym name; a2sexp t; list2sexp (MAP f2sexp axioms);
          list2sexp (MAP f2sexp thms); atbl],ARB,k,io,ok) x =
           (x = (res,k,io,T))` by METIS_TAC [R_ap_T_11]
    \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ Q.ABBREV_TAC `xxx = (@result.
           R_ap (Funcall,
         [Sym name; a2sexp t; list2sexp (MAP f2sexp axioms);
          list2sexp (MAP f2sexp thms); atbl],ARB,k,io,ok)
             result)`
  \\ `R_ap (Funcall,
         [Sym name; a2sexp t; list2sexp (MAP f2sexp axioms);
          list2sexp (MAP f2sexp thms); atbl],ARB,k,io,ok) xxx` by METIS_TAC []
  \\ `?x1 x2 x3 b. xxx = (x1,x2,x3,b)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [R_ap_F_11]);

val core_admit_theorem_thm = prove(
  ``milawa_inv ctxt simple_ctxt k (axioms,thms,atbl,checker,ftbl) ==>
    ?x k2 io2 ok2 result.
      core_admit_theorem_side cmd (milawa_state (axioms,thms,atbl,checker,ftbl)) k io ok /\
      (core_admit_theorem cmd (milawa_state (axioms,thms,atbl,checker,ftbl)) k io ok =
         (x,k2,io2,ok2)) /\
      (ok2 ==> (k2 = k) /\ (io2 = io) /\
               ?result. (x = milawa_state result) /\ milawa_inv ctxt simple_ctxt k result)``,
  FS [core_admit_theorem_def,LET_DEF,milawa_state_def,core_state_def,
      SIMP_RULE std_ss [DISJ_EQ_IMP,GSYM AND_IMP_INTRO,LET_DEF] core_admit_theorem_side_def]
  \\ SRW_TAC [] [] \\ FS [] \\ FS []
  \\ IMP_RES_TAC logic_appealp_thm \\ FS []
  \\ Q.PAT_X_ASSUM `f2sexp (CONCL t) = xxx` (ASSUME_TAC o GSYM) \\ FS []
  \\ FS [milawa_inv_def,EVERY_DEF]
  \\ STRIP_ASSUME_TAC (core_check_proof_inv_IMP |> UNDISCH |> GEN_ALL)
  \\ FS [] THEN1
   (Q.EXISTS_TAC `(axioms,thms,atbl,checker,ftbl)`
    \\ ASM_SIMP_TAC std_ss [milawa_inv_def] \\ EVAL_TAC)
  \\ Q.EXISTS_TAC `(axioms,CONCL t::thms,atbl,checker,ftbl)`
  \\ STRIP_TAC THEN1 EVAL_TAC
  \\ FS [milawa_inv_def,thms_inv_def,EVERY_DEF]
  \\ METIS_TAC [core_check_proof_thm,thms_inv_def]);


(* admit defun *)

val if_memberp_def = Define `
  if_memberp new_axiom axioms =
    if isTrue (memberp new_axiom axioms) then axioms else LISP_CONS new_axiom axioms`

val if_lookup_def = Define `
  if_lookup name atbl new_atbl =
    if isTrue (lookup name atbl) then atbl else new_atbl`;

val core_admit_defun_lemma = core_admit_defun_def
  |> SIMP_RULE std_ss [GSYM if_memberp_def,GSYM if_lookup_def]

val core_admit_defun_side_lemma = core_admit_defun_side_def
  |> SIMP_RULE std_ss [DISJ_EQ_IMP,GSYM AND_IMP_INTRO,LET_DEF,define_safe_side_def]

val SND_SND_SND_define_safe_IMP = prove(
  ``SND (SND (SND (define_safe ftbl name formals body k io ok))) ==> ok``,
  SIMP_TAC std_ss [define_safe_def,LET_DEF] \\ SRW_TAC [] []);

val fake_ftbl_entries = prove(
  ``ftbl_inv k ftbl /\
    SND (SND (SND (define_safe ftbl (Sym fname) ys body k io ok))) ==>
    ~(MEM fname fake_ftbl_entries)``,
  SIMP_TAC std_ss [define_safe_def] \\ FS [LET_DEF] \\ REPEAT STRIP_TAC
  \\ sg `lookup_safe (Sym fname) ftbl = list2sexp [Sym fname]`
  \\ FS [EVAL ``isTrue (Dot x y)``]
  \\ FS [ftbl_inv_def,EVERY_MEM]);

val MAP_t2sexp_MAP_mVar = add_prove(
  ``!xs. MAP t2sexp (MAP mVar xs) = MAP Sym xs``,
  Induct \\ FS [] \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss []);

val core_admit_defun_cmd = prove(
  ``list_exists 6 cmd ==>
    ?x name formals body meas proof_list.
        cmd = list2sexp [x;name;formals;body;meas;proof_list]``,
  REPEAT STRIP_TAC \\ EVAL_TAC \\ Cases_on `cmd` \\ FS []
  \\ REPEAT ((Cases_on `S0` \\ FS []) ORELSE (Cases_on `S0'` \\ FS [])) \\ FS []);

val logic_variable_listp_ALL_DISTINCT_IMP = prove(
  ``!xs. isTrue (logic_variable_listp (list2sexp xs)) /\ ALL_DISTINCT xs ==>
         ALL_DISTINCT (MAP getSym xs)``,
  Induct THEN1 EVAL_TAC \\ ONCE_REWRITE_TAC [logic_variable_listp_def]
  \\ FS [MAP,ALL_DISTINCT,MEM_MAP,EVERY_DEF] \\ STRIP_TAC
  \\ Cases_on `isTrue (logic_variablep h)` \\ FS []
  \\ REPEAT STRIP_TAC \\ Cases_on `MEM y xs` \\ FS []
  \\ REPEAT STRIP_TAC \\ FS [logic_variablep_def]
  \\ Cases_on `isSym h` \\ FS []
  \\ Cases_on `h = Sym "T"` \\ FS []
  \\ FS [isSym_thm] \\ Cases_on `y` \\ FS [getSym_def]);

val logic_variable_listp_IMP_EVERY = prove(
  ``!xs. isTrue (logic_variable_listp (list2sexp xs)) ==>
         EVERY (\x. getSym x <> "NIL" /\ getSym x <> "T") xs``,
  Induct THEN1 EVAL_TAC \\ SIMP_TAC std_ss [Once logic_variable_listp_def]
  \\ FS [] \\ SRW_TAC [] [] \\ FS [] \\ FS [logic_variablep_def]
  \\ Cases_on `isSym h` \\ FS [] \\ Cases_on `h = Sym "T"` \\ FS []
  \\ Cases_on `h = Sym "NIL"` \\ FS [] \\ Cases_on `h` \\ FS [getSym_def]);

val logic_strip_conclusions_thm = prove(
  ``!ts z. ~isDot z ==>
      (logic_strip_conclusions (anylist2sexp (MAP a2sexp ts) z) =
       list2sexp (MAP f2sexp (MAP CONCL ts)))``,
  REPEAT STRIP_TAC \\ Induct_on `ts`
  \\ ONCE_REWRITE_TAC [logic_strip_conclusions_def] \\ FS [MAP]);

val MAP_f2sexp_11 = prove(
  ``!xs ys. (MAP f2sexp xs = MAP f2sexp ys) = (xs = ys)``,
  Induct \\ Cases_on `ys` \\ FS [MAP,CONS_11]);

val MAP_getSym_Sym = prove(
  ``!xs. MAP getSym (MAP Sym xs) = xs``,
  Induct \\ FS [MAP,getSym_def]);

val core_check_proof_list_thm = prove(
  ``!ok.
      core_check_proof_inv checker k /\ ~isDot z /\ atbl_ok ctxt atbl /\ context_ok ctxt /\
      thms_inv ctxt thms /\ thms_inv ctxt axioms /\ EVERY appeal_syntax_ok ts ==>
      SND (SND (SND
            (core_check_proof_list checker
               (anylist2sexp (MAP a2sexp ts) z)
               (list2sexp (MAP f2sexp axioms))
               (list2sexp (MAP f2sexp thms)) atbl k io ok))) /\
      isTrue (FST
            (core_check_proof_list checker
               (anylist2sexp (MAP a2sexp ts) z)
               (list2sexp (MAP f2sexp axioms))
               (list2sexp (MAP f2sexp thms)) atbl k io ok)) ==>
      EVERY (MilawaTrue ctxt) (MAP CONCL ts)``,
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO] \\ NTAC 5 STRIP_TAC
  \\ Induct_on `ts` \\ FS [EVERY_DEF,MAP]
  \\ ONCE_REWRITE_TAC [core_check_proof_list_def] \\ FS [LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ FS []
  \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
  \\ Cases_on `isTrue (FST
               (core_check_proof checker (a2sexp h)
                  (list2sexp (MAP f2sexp axioms))
                  (list2sexp (MAP f2sexp thms)) atbl k io ok))` \\ FS []
  \\ STRIP_TAC
  \\ IMP_RES_TAC core_check_proof_list_IMP_OK
  \\ IMP_RES_TAC core_check_proof_IMP_OK
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC core_check_proof_inv_IMP
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `ok` ASSUME_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FS [] \\ METIS_TAC [core_check_proof_thm]);

val isTrue_lookup_safe = prove(
  ``!ftbl.
      isTrue (lookup_safe (Sym fname) ftbl) /\ EVERY isDot (sexp2list ftbl) ==>
      MEM (lookup_safe (Sym fname) ftbl) (sexp2list ftbl)``,
  REVERSE Induct \\ ONCE_REWRITE_TAC [lookup_safe_def] \\ FS [sexp2list_def]
  \\ Cases_on `Sym fname = CAR ftbl` \\ FS []
  \\ Cases_on `isDot ftbl` \\ FS [EVERY_DEF]);

val lookup_safe_EQ_MEM = prove(
  ``!ftbl. MEM (Sym fname) (MAP CAR (sexp2list ftbl)) =
           isTrue (lookup_safe (Sym fname) ftbl)``,
  REVERSE Induct \\ SIMP_TAC std_ss [sexp2list_def,MAP,MEM]
  \\ ONCE_REWRITE_TAC [lookup_safe_def] \\ FS []
  \\ Cases_on `Sym fname = CAR ftbl` \\ FS []
  \\ Cases_on `ftbl` \\ EVAL_TAC);

val define_safe_ID = prove(
  ``SND (SND (SND (define_safe ftbl (Sym fname) (list2sexp xs) body k io T))) /\
    MEM (Sym fname) (MAP CAR (sexp2list ftbl)) ==>
    (define_safe ftbl (Sym fname) (list2sexp xs) body k io T =
       (ftbl,k,io,T))``,
  SIMP_TAC std_ss [define_safe_def,LET_DEF]
  \\ Cases_on `isTrue (lookup_safe (Sym fname) ftbl)` \\ FS []
  \\ REPEAT STRIP_TAC \\ METIS_TAC [lookup_safe_EQ_MEM]);

val CDR_lookup_NOT_NIL = prove(
  ``!atbl. isTrue (lookup (Sym fname) atbl) /\ atbl_inv atbl ==>
           CDR (lookup (Sym fname) atbl) <> Sym "NIL"``,
  REVERSE Induct \\ ONCE_REWRITE_TAC [lookup_def]
  \\ FS [atbl_inv_def,sexp2list_def,EVERY_DEF]
  \\ SRW_TAC [] [] \\ FS [] \\ FS [isVal_thm]);

val MEM_ftbl = prove(
  ``MEM (Sym fname) (MAP CAR (sexp2list ftbl)) /\ ftbl_inv k ftbl /\
    SND (SND (SND (define_safe ftbl (Sym fname) x body k io T))) ==>
    MEM (Dot (Sym fname) (Dot x (Dot body (Sym "NIL")))) (sexp2list ftbl)``,
  SIMP_TAC std_ss [define_safe_def,LET_DEF,GSYM AND_IMP_INTRO,GSYM lookup_safe_EQ_MEM]
  \\ FS [] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ REPEAT STRIP_TAC \\ FS [ftbl_inv_def]
  \\ METIS_TAC [isTrue_lookup_safe,lookup_safe_EQ_MEM]);

val MEM_MEM_ftbl = prove(
  ``MEM (Dot (Sym fname) x1) (sexp2list ftbl) /\
    MEM (Dot (Sym fname) x2) (sexp2list ftbl) /\
    ftbl_inv k ftbl ==> (x1 = x2)``,
  SIMP_TAC std_ss [ftbl_inv_def] \\ Q.SPEC_TAC (`sexp2list ftbl`,`xs`)
  \\ REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `MEM xx yy` MP_TAC
  \\ SIMP_TAC std_ss [MEM_SPLIT] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [MEM_APPEND,MEM]
  \\ FS [MAP_APPEND,MAP,ALL_DISTINCT_APPEND,MEM_MAP,PULL_EXISTS_IMP,ALL_DISTINCT]
  \\ FS [METIS_PROVE [] ``(b \/ ~c) = (c ==> b:bool)``] \\ RES_TAC \\ FS []);

val func_definition_exists_NEQ = prove(
  ``name <> fname ==>
    (func_definition_exists (ctxt |+ (fname,ps,b,ef)) name params body sem =
     func_definition_exists ctxt name params body sem)``,
  SIMP_TAC std_ss [func_definition_exists_def,FAPPLY_FUPDATE_THM,
    FDOM_FUPDATE,IN_INSERT,LET_DEF]);

val func_definition_exists_EQ = prove(
  ``~MEM fname ["NOT";"RANK";"ORD<";"ORDP"] ==>
    (func_definition_exists (ctxt |+ (fname,ps,b,ef)) fname params body sem =
     (ps = params) /\ (b = body) /\ (ef = sem))``,
  SIMP_TAC std_ss [func_definition_exists_def,FAPPLY_FUPDATE_THM,FDOM_FUPDATE,
    IN_INSERT]);

val logic_func_inv_NEQ = prove(
  ``term_ok ctxt (term2t (sexp3term raw_body)) /\
    context_ok ctxt /\ name IN FDOM ctxt /\
    logic_func_inv name ctxt raw_body /\ fname NOTIN FDOM ctxt /\ name <> fname ==>
    logic_func_inv name (ctxt |+ (fname,MAP getSym xs,bb,ef)) raw_body``,
  SIMP_TAC std_ss [logic_func_inv_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ DISJ2_TAC \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [GSYM EvalTerm_FUPDATE]
  \\ MATCH_MP_TAC (GEN_ALL M_ev_EQ_CTXT_LEMMA) \\ Q.EXISTS_TAC `ctxt`
  \\ FULL_SIMP_TAC (srw_ss()) [FAPPLY_FUPDATE_THM]
  \\ `?params bbb sem. ctxt ' name = (params,bbb,sem)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `bbb` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ Cases_on `m = fname` \\ FS []
  \\ FULL_SIMP_TAC std_ss [context_ok_def]
  \\ RES_TAC \\ IMP_RES_TAC term_ok_MEM_funs_IMP);

val ALL_DISTINCT_MAP_getSym = prove(
  ``!xs. ALL_DISTINCT xs /\ EVERY isSym xs ==> ALL_DISTINCT (MAP getSym xs)``,
  Induct \\ SIMP_TAC std_ss [ALL_DISTINCT,MAP,EVERY_DEF,isSym_thm]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [MEM_MAP]
  \\ Q.PAT_X_ASSUM `h = Sym a` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [getSym_def]
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [isSym_thm]
  \\ FULL_SIMP_TAC std_ss [getSym_def]);

val logic_func_inv_EQ = prove(
  ``context_ok (ctxt |+ (fname,MAP getSym xs,BODY_FUN b,ef)) /\
    ALL_DISTINCT xs /\ EVERY isSym xs /\
    term_ok (ctxt |+ (fname,MAP getSym xs,BODY_FUN b,ef)) b /\
    EVERY (MilawaTrue (ctxt |+ (fname,MAP getSym xs,BODY_FUN b,ef)))
      (termination_obligations fname b (MAP getSym xs) m) /\
    (EvalFun fname (ctxt |+ (fname,MAP getSym xs,BODY_FUN b,ef)) = ef) /\
    set (free_vars b) SUBSET set (MAP getSym xs) /\
    ((term2t (sexp3term body)) = b) ==>
    logic_func_inv fname (ctxt |+ (fname,MAP getSym xs,BODY_FUN b,ef)) body``,
  SIMP_TAC std_ss [logic_func_inv_def]
  \\ Cases_on `MEM fname ["NOT"; "RANK"; "ORD<"; "ORDP"]` \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ SIMP_TAC std_ss [LET_DEF]
  \\ Q.ABBREV_TAC `ctxt2 = ctxt |+ (fname,MAP getSym xs,BODY_FUN b,ef)`
  \\ MATCH_MP_TAC (GEN_ALL M_ev_TERMINATES)
  \\ Q.LIST_EXISTS_TAC [`MAP getSym xs`,`m`]
  \\ FULL_SIMP_TAC std_ss []
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ FULL_SIMP_TAC std_ss []
  \\ Q.UNABBREV_TAC `ctxt2`
  \\ FULL_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM,FDOM_FUPDATE,IN_INSERT]
  \\ STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [ALL_DISTINCT_MAP_getSym])
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ IMP_RES_TAC Milawa_SOUNDESS);

val logic_variable_listp_IMP_EVERY_Sym = prove(
  ``!xs. isTrue (logic_variable_listp (list2sexp xs)) ==> EVERY isSym xs``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC logic_variable_listp_IMP
  \\ FS [EVERY_MEM,MEM_MAP] \\ REPEAT STRIP_TAC \\ FS []);

val NAME_NOT_ERROR = prove(
  ``SND (SND (SND(define_safe ftbl (Sym fname) (list2sexp xs) body k io T))) /\
    ftbl_inv k ftbl ==> ~(fname = "ERROR")``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [define_safe_def,LET_DEF,getSym_def]
  \\ FULL_SIMP_TAC std_ss [ftbl_inv_def,fake_ftbl_entries_def,EVERY_DEF]
  \\ FS [] \\ FULL_SIMP_TAC (srw_ss()) [isTrue_def]);

val NOT_CAR_EQ_ERROR = prove(
  ``term_ok ctxt (term2t (sexp3term body)) /\ ~("ERROR" IN FDOM ctxt) ==>
    ~(CAR body = Sym "ERROR")``,
  REPEAT STRIP_TAC \\ Cases_on `body` \\ TRY (Cases_on `S'`) \\ FS []
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT (POP_ASSUM MP_TAC)
  \\ ONCE_REWRITE_TAC [sexp3term_def] \\ FS [LET_DEF]
  \\ FULL_SIMP_TAC (srw_ss()) [getSym_def,sym2prim_def,term2t_def,
       func2f_def,term_ok_def,func_arity_def]);

local
  val PUSH_STRIP_LEMMA = METIS_PROVE [] ``b /\ (b ==> x) ==> b /\ x``
in
  val PUSH_STRIP_TAC =
    MATCH_MP_TAC PUSH_STRIP_LEMMA THEN STRIP_TAC
    THENL [ALL_TAC, STRIP_TAC]
end

val MAP_EQ_MAP = prove(
  ``!xs. (MAP f xs = MAP g xs) = !x. MEM x xs ==> (f x = g x)``,
  Induct \\ SIMP_TAC std_ss [MAP,MEM,CONS_11] \\ METIS_TAC [])

val sexp2list_EQ_3 = prove(
  ``(3 = LENGTH (sexp2list (CDR raw_body))) ==>
    ?x1 x2 x3 x4 x5. (raw_body = Dot x1 (Dot x2 (Dot x3 (Dot x4 x5)))) /\ ~isDot x5``,
  Cases_on `raw_body` \\ FULL_SIMP_TAC std_ss [CDR_def,sexp2list_def,LENGTH]
  \\ Cases_on `S0` \\ FULL_SIMP_TAC std_ss [CDR_def,sexp2list_def,LENGTH]
  \\ Cases_on `S0'` \\ FULL_SIMP_TAC std_ss [CDR_def,sexp2list_def,LENGTH]
  \\ Cases_on `S0` \\ FULL_SIMP_TAC std_ss [CDR_def,sexp2list_def,LENGTH]
  \\ Cases_on `S0'` \\ FULL_SIMP_TAC std_ss [CDR_def,sexp2list_def,LENGTH]
  \\ FULL_SIMP_TAC (srw_ss()) [isDot_def] \\ DECIDE_TAC);

val sexp2list_NIL = prove(
  ``!x. ~isDot x ==> (sexp2list x = [])``,
  Cases \\ EVAL_TAC);

val sexp3term_And_lemma = prove(
  ``!xs.
      (EVERY (term_ok ctxt) (MAP (term2t o sexp3term) xs) ==>
       EVERY (\x. term2t (sexp3term x) = term2t (sexp2term x)) xs) ==>
      term_ok ctxt (term2t (And (MAP (\a. sexp3term a) xs))) ==>
      (term2t (And (MAP (\a. sexp3term a) xs)) =
       term2t (And (MAP (\a. sexp2term a) xs)))``,
  Induct \\ SIMP_TAC std_ss [MAP,term2t_def,EVERY_DEF]
  \\ Cases_on `xs` \\ FULL_SIMP_TAC (srw_ss()) [MAP,term2t_def,EVERY_DEF,term_ok_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ sg `term_ok ctxt (term2t (sexp3term h)) /\
       EVERY (term_ok ctxt) (MAP (term2t o sexp3term) t)`
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  THEN1 (Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) [MAP,term2t_def,EVERY_DEF,term_ok_def])
  \\ POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Q.SPEC_TAC (`h`,`h`) \\ Q.SPEC_TAC (`t`,`t`)
  \\ Induct
  \\ FULL_SIMP_TAC (srw_ss()) [MAP,term2t_def,EVERY_DEF,term_ok_def]
  \\ Cases_on `t`
  \\ FULL_SIMP_TAC (srw_ss()) [MAP,term2t_def,EVERY_DEF,term_ok_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC);

val sexp3term_List_lemma = prove(
  ``(EVERY (term_ok ctxt) (MAP (term2t o sexp3term) xs) ==>
     EVERY (\x. term2t (sexp3term x) = term2t (sexp2term x)) xs) ==>
    term_ok ctxt (term2t (List (MAP (\a. sexp3term a) xs))) ==>
    (term2t (List (MAP (\a. sexp3term a) xs)) =
     term2t (List (MAP (\a. sexp2term a) xs)))``,
  Induct_on `xs` \\ SIMP_TAC std_ss [MAP,term2t_def,EVERY_DEF]
  \\ Cases_on `xs` \\ FULL_SIMP_TAC (srw_ss()) [MAP,term2t_def,EVERY_DEF,term_ok_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ sg `EVERY (term_ok ctxt) (MAP (term2t o sexp3term) t)`
  \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Q.SPEC_TAC (`t`,`t`) \\ Induct
  \\ FULL_SIMP_TAC (srw_ss()) [MAP,term2t_def,EVERY_DEF,term_ok_def]);

val term_ok_Cond_lemma = prove(
  ``term_ok ctxt (term2t
      (Cond (MAP (\y. (sexp3term (CAR y),sexp3term (CAR (CDR y)))) xs))) =
    EVERY (\x. term_ok ctxt (term2t (sexp3term (CAR x)))) xs /\
    EVERY (\x. term_ok ctxt (term2t (sexp3term (CAR (CDR x))))) xs``,
  Induct_on `xs` \\ ASM_SIMP_TAC std_ss [term2t_def,MAP,term_ok_def,LENGTH,EVERY_DEF]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [func_arity_def,primitive_arity_def]
  \\ METIS_TAC []);

val term2t_Cond_lemma = prove(
  ``(term2t (Cond (MAP (\y. (sexp3term (CAR y),sexp3term (CAR (CDR y)))) xs)) =
     term2t (Cond (MAP (\y. (sexp2term (CAR y),sexp2term (CAR (CDR y)))) xs))) =
    EVERY (\x. term2t (sexp3term (CAR x)) = term2t (sexp2term (CAR x))) xs /\
    EVERY (\x. term2t (sexp3term (CAR (CDR x))) = term2t (sexp2term (CAR (CDR x)))) xs``,
  Induct_on `xs` \\ ASM_SIMP_TAC (srw_ss()) [MAP,EVERY_DEF,term2t_def]
  \\ METIS_TAC []);

val term2t_LamApp_lemma = prove(
  ``(term2t
      (LamApp (MAP getSym (sexp2list xs))
        (sexp3term y)
        (MAP (\a. sexp3term a) ys)) =
     term2t
      (LamApp (MAP getSym (sexp2list xs))
        (sexp2term y)
        (MAP (\a. sexp2term a) ys))) =
    EVERY (\x. term2t (sexp3term x) = term2t (sexp2term x)) ys /\
    (term2t (sexp3term y) = term2t (sexp2term y))``,
  SIMP_TAC (srw_ss()) [term2t_def,MAP_MAP_o,MAP_EQ_MAP,EVERY_MEM] \\ METIS_TAC []);

val term_ok_LamApp_lemma = prove(
  ``term_ok ctxt (term2t (LamApp (MAP getSym (sexp2list xs)) (sexp3term y)
      (MAP (\a. sexp3term a) ys))) ==>
    EVERY (\x. term_ok ctxt (term2t (sexp3term x))) ys /\
    term_ok ctxt (term2t (sexp3term y))``,
  SIMP_TAC std_ss [term2t_def,term_ok_def,LENGTH_MAP,EVERY_MEM]
  \\ FULL_SIMP_TAC std_ss [MEM_MAP,PULL_EXISTS_IMP]);

val DISJ_EQ_IMP = METIS_PROVE [] ``b \/ c = ~b ==> c``

val term_ok_let2t = prove(
  ``term_ok ctxt (let2t xs y) ==>
    EVERY (\x. term_ok ctxt (SND x)) xs /\ term_ok ctxt y``,
  SIMP_TAC std_ss [let2t_def,LET_DEF,term_ok_def,EVERY_APPEND,EVERY_MEM,MEM_MAP]
  \\ SIMP_TAC std_ss [PULL_EXISTS_IMP]);

val term_ok_let_star2t = prove(
  ``term_ok ctxt (term2t (LetStar xs y)) ==>
    EVERY (\x. term_ok ctxt (term2t (SND x))) xs /\ term_ok ctxt (term2t y)``,
  Induct_on `xs` \\ SIMP_TAC std_ss [term2t_def,EVERY_DEF] \\ Cases
  \\ ASM_SIMP_TAC std_ss [term2t_def,EVERY_DEF] \\ STRIP_TAC
  \\ IMP_RES_TAC term_ok_let2t \\ RES_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [EVERY_DEF,MAP]);

val term_ok_or2t = prove(
  ``!xs. term_ok ctxt (or2t (MAP (\a. term2t a) (MAP (\a. sexp3term a) xs))) ==>
         EVERY (\x. term_ok ctxt (term2t (sexp3term x))) xs``,
  Cases THEN1 SIMP_TAC std_ss [or2t_def,MAP,term_ok_def,EVERY_DEF]
  \\ Q.SPEC_TAC (`h`,`h`) \\ Induct_on `t`
  \\ SIMP_TAC std_ss [or2t_def,MAP,term_ok_def,EVERY_DEF]
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ STRIP_TAC \\ STRIP_TAC \\ SIMP_TAC std_ss [DISJ_EQ_IMP]
  \\ Cases_on `~isTrue (logic_variablep (t2sexp (term2t (sexp3term h')))) /\
     ~isTrue (logic_constantp (t2sexp (term2t (sexp3term h')))) ==>
     MEM "SPECIAL-VAR-FOR-OR"
       (free_vars
          (or2t
             (term2t (sexp3term h)::
                  MAP (\a. term2t a) (MAP (\a. sexp3term a) t))))` \\ FS []
  THEN1
   (FULL_SIMP_TAC std_ss [term_ok_def,EVERY_DEF,MAP] \\ REPEAT STRIP_TAC \\ RES_TAC)
  \\ FULL_SIMP_TAC std_ss [term_ok_def,EVERY_DEF,MAP] \\ STRIP_TAC
  \\ IMP_RES_TAC term_ok_let2t
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,term_ok_def] \\ RES_TAC);

val let2t_IMP = prove(
  ``(xs = ys) /\ (x = y) ==> (let2t xs x = let2t ys y)``,
  SIMP_TAC std_ss []);

val or2t_IMP = prove(
  ``(xs = ys) ==> (or2t xs = or2t ys)``,
  SIMP_TAC std_ss []);

val let_star2t_IMP = prove(
  ``(MAP (\x. (FST x, term2t (SND x))) xs = MAP (\x. (FST x, term2t (SND x))) ys) /\
    (term2t x = term2t y) ==>
    (term2t (LetStar xs x) = term2t (LetStar ys y))``,
  Q.SPEC_TAC (`ys`,`ys`) \\ Induct_on `xs`
  \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [MAP,term2t_def]
  \\ Cases \\ FULL_SIMP_TAC (srw_ss()) [MAP,term2t_def]
  \\ Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) [MAP,term2t_def]
  \\ METIS_TAC []);

val term2t_sexp3term_LEMMA = prove(
  ``!raw_body.
      ~("DEFUN" IN FDOM ctxt) /\ term_ok ctxt (term2t (sexp3term raw_body)) ==>
      (term2t (sexp3term raw_body) = term2t (sexp2term raw_body))``,
  HO_MATCH_MP_TAC sexp2term_ind \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [sexp3term_def,sexp2term_def]
  \\ Cases_on `raw_body = Sym "T"` THEN1 ASM_SIMP_TAC std_ss []
  \\ Cases_on `raw_body = Sym "NIL"` THEN1 ASM_SIMP_TAC std_ss []
  \\ Cases_on `isVal raw_body` THEN1 ASM_SIMP_TAC std_ss []
  \\ Cases_on `isSym raw_body` THEN1 ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [LET_DEF]
  \\ Cases_on `CAR raw_body = Sym "QUOTE"` THEN1 ASM_SIMP_TAC std_ss []
  \\ Cases_on `CAR raw_body = Sym "IF"` THEN1
   (ASM_SIMP_TAC (srw_ss()) [getSym_def,sym2prim_def,CAR_def,
      term2t_def,func2f_def,term_ok_def,func_arity_def,primitive_arity_def]
    \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO] \\ STRIP_TAC
    \\ IMP_RES_TAC sexp2list_EQ_3 \\ IMP_RES_TAC sexp2list_NIL
    \\ ASM_REWRITE_TAC [sexp2list_def,CDR_def,MAP,CAR_def]
    \\ SIMP_TAC std_ss [EVERY_DEF,CONS_11]
    \\ REPEAT (Q.PAT_X_ASSUM `!xx.bb` MP_TAC)
    \\ Q.PAT_X_ASSUM `CAR raw_body = Sym "IF"` MP_TAC
    \\ ASM_REWRITE_TAC [CAR_def,CDR_def,sexp2list_def,MEM,EVERY_DEF]
    \\ STRIP_TAC
    \\ NTAC 22 (MATCH_MP_TAC (METIS_PROVE [] ``b ==> (c ==> b)``))
    \\ `~(x1 = Sym "QUOTE")` by (REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ Q.PAT_X_ASSUM `CAR raw_body <> bbb` (K ALL_TAC)
    \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `sym2prim (getSym (CAR raw_body)) <> NONE` THEN1
   (ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (srw_ss()) [term2t_def,term_ok_def,MAP_MAP_o]
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_EXISTS_IMP,MAP_EQ_MAP])
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `CAR raw_body = Sym "FIRST"` \\ ASM_SIMP_TAC std_ss []
  THEN1 (FULL_SIMP_TAC (srw_ss()) [term2t_def,term_ok_def])
  \\ Cases_on `CAR raw_body = Sym "SECOND"` \\ ASM_SIMP_TAC std_ss []
  THEN1 (FULL_SIMP_TAC (srw_ss()) [term2t_def,term_ok_def])
  \\ Cases_on `CAR raw_body = Sym "THIRD"` \\ ASM_SIMP_TAC std_ss []
  THEN1 (FULL_SIMP_TAC (srw_ss()) [term2t_def,term_ok_def])
  \\ Cases_on `CAR raw_body = Sym "FOURTH"` \\ ASM_SIMP_TAC std_ss []
  THEN1 (FULL_SIMP_TAC (srw_ss()) [term2t_def,term_ok_def])
  \\ Cases_on `CAR raw_body = Sym "FIFTH"` \\ ASM_SIMP_TAC std_ss []
  THEN1 (FULL_SIMP_TAC (srw_ss()) [term2t_def,term_ok_def])
  \\ Cases_on `CAR raw_body = Sym "OR"` \\ ASM_SIMP_TAC std_ss []
  THEN1
   (SIMP_TAC std_ss [term2t_def] \\ STRIP_TAC \\ IMP_RES_TAC term_ok_or2t
    \\ MATCH_MP_TAC or2t_IMP \\ SIMP_TAC std_ss [MAP_EQ_MAP,MAP_MAP_o]
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM])
  \\ Cases_on `CAR raw_body = Sym "AND"` \\ ASM_SIMP_TAC std_ss []
  THEN1 (MATCH_MP_TAC sexp3term_And_lemma
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_EXISTS_IMP])
  \\ Cases_on `CAR raw_body = Sym "LIST"` \\ ASM_SIMP_TAC std_ss []
  THEN1 (MATCH_MP_TAC sexp3term_List_lemma
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_EXISTS_IMP])
  \\ Cases_on `CAR raw_body = Sym "DEFUN"` \\ ASM_SIMP_TAC std_ss []
  THEN1 (FULL_SIMP_TAC (srw_ss()) [CAR_def,term2t_def,term_ok_def,
          func_arity_def,func2f_def,getSym_def])
  \\ Cases_on `CAR raw_body = Sym "COND"` \\ ASM_SIMP_TAC std_ss []
  THEN1 (SIMP_TAC std_ss [term_ok_Cond_lemma,term2t_Cond_lemma,EVERY_MEM]
         \\ FULL_SIMP_TAC std_ss [])
  \\ Cases_on `CAR raw_body = Sym "LET"` \\ ASM_SIMP_TAC std_ss []
  THEN1
   (SIMP_TAC std_ss [term2t_def] \\ STRIP_TAC \\ IMP_RES_TAC term_ok_let2t
    \\ MATCH_MP_TAC let2t_IMP \\ SIMP_TAC std_ss [MAP_EQ_MAP,MAP_MAP_o]
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM]
    \\ FULL_SIMP_TAC std_ss [MEM_MAP,PULL_EXISTS_IMP])
  \\ Cases_on `CAR raw_body = Sym "LET*"` \\ ASM_SIMP_TAC std_ss []
  THEN1
   (SIMP_TAC std_ss [term2t_def] \\ STRIP_TAC \\ IMP_RES_TAC term_ok_let_star2t
    \\ MATCH_MP_TAC let_star2t_IMP \\ SIMP_TAC std_ss [MAP_EQ_MAP,MAP_MAP_o]
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM]
    \\ FULL_SIMP_TAC std_ss [MEM_MAP,PULL_EXISTS_IMP])
  \\ Cases_on `CAR (CAR raw_body) = Sym "LAMBDA"` \\ ASM_SIMP_TAC std_ss []
  THEN1
   (REPEAT STRIP_TAC \\ IMP_RES_TAC term_ok_LamApp_lemma \\ NTAC 3 (POP_ASSUM MP_TAC)
    \\ SIMP_TAC std_ss [term2t_LamApp_lemma,EVERY_MEM] \\ METIS_TAC [])
  \\ Cases_on `CAR raw_body = Sym "DEFINE"` \\ ASM_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC (srw_ss()) [term2t_def,func2f_def,getSym_def]
    \\ FULL_SIMP_TAC (srw_ss()) [term2t_def,term_ok_def,MAP_MAP_o]
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_EXISTS_IMP,MAP_EQ_MAP])
  \\ Cases_on `CAR raw_body = Sym "ERROR"` \\ ASM_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC (srw_ss()) [term2t_def,func2f_def,getSym_def]
    \\ FULL_SIMP_TAC (srw_ss()) [term2t_def,term_ok_def,MAP_MAP_o]
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_EXISTS_IMP,MAP_EQ_MAP])
  \\ Cases_on `CAR raw_body = Sym "FUNCALL"` \\ ASM_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC (srw_ss()) [term2t_def,func2f_def,getSym_def]
    \\ FULL_SIMP_TAC (srw_ss()) [term2t_def,term_ok_def,MAP_MAP_o]
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_EXISTS_IMP,MAP_EQ_MAP])
  \\ Cases_on `CAR raw_body = Sym "PRINT"` \\ ASM_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC (srw_ss()) [term2t_def,func2f_def,getSym_def]
    \\ FULL_SIMP_TAC (srw_ss()) [term2t_def,term_ok_def,MAP_MAP_o]
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_EXISTS_IMP,MAP_EQ_MAP])
  \\ ASM_SIMP_TAC (srw_ss()) [term2t_def,func2f_def,getSym_def,
       term2t_def,term_ok_def,MAP_MAP_o]
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_EXISTS_IMP,MAP_EQ_MAP])

val SUBMAP_add_def = prove(
  ``k SUBMAP add_def k (x,y,z)``,
  SIMP_TAC std_ss [SUBMAP_DEF,add_def_def,FUNION_DEF,IN_UNION]);

val lookup_safe_IMP_MEM = prove(
  ``!ftbl. (lookup_safe (Sym x) ftbl = Dot y z) /\ ~(x = "NIL") ==>
           MEM (Dot y z) (sexp2list ftbl)``,
  REVERSE Induct \\ ONCE_REWRITE_TAC [lookup_safe_def] \\ FS []
  \\ Cases_on `Sym x = CAR ftbl` \\ FS [] THEN1
   (Cases_on `isDot ftbl` \\ FS [sexp2list_def,MEM] \\ Cases_on `ftbl` \\ FS [])
  \\ FS [sexp2list_def,MEM]);

val ALL_DISTINCT_IMP_11 = prove(
  ``!xs. ALL_DISTINCT (MAP f xs) /\ MEM x xs /\ MEM y xs /\ (f x = f y) ==> (x = y)``,
  Induct \\ SIMP_TAC std_ss [MEM,MAP,ALL_DISTINCT]
  \\ FULL_SIMP_TAC std_ss [MEM_MAP] \\ REPEAT STRIP_TAC \\ METIS_TAC []);

val fake_ftbl_entries_NOT_IN_CTXT = prove(
  ``axioms_inv ctxt ftbl axioms /\ ftbl_inv k ftbl ==>
    EVERY (\x. x NOTIN FDOM ctxt) fake_ftbl_entries``,
  SIMP_TAC std_ss [ftbl_inv_def,axioms_inv_def]
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ `?params body sem. ctxt ' x = (params,body,sem)` by METIS_TAC [PAIR]
  \\ `func_definition_exists ctxt x params body sem` by METIS_TAC [func_definition_exists_def]
  \\ RES_TAC \\ `?y z. MEM (list2sexp [Sym x; y; z]) (sexp2list ftbl)` by (Cases_on `body` \\ FULL_SIMP_TAC std_ss [axioms_aux_def] \\ METIS_TAC [])
  \\ FS [] \\ `~(x = "NIL")` by FULL_SIMP_TAC (srw_ss()) [fake_ftbl_entries_def,MEM]
  \\ IMP_RES_TAC lookup_safe_IMP_MEM
  \\ `CAR (Dot (Sym x) (Dot y (Dot z (Sym "NIL")))) = CAR (Dot (Sym x) (Sym "NIL"))` by EVAL_TAC
  \\ IMP_RES_TAC ALL_DISTINCT_IMP_11
  \\ Q.PAT_X_ASSUM `xxx = yyy` MP_TAC \\ SS []);

val MR_ap_CTXT =
  MR_ev_CTXT
  |> CONJUNCTS |> hd |> SPEC_ALL |> Q.INST [`ctxt`|->`ctxt |+ (name,x)`]
  |> SIMP_RULE std_ss [DOMSUB_FUPDATE]
  |> DISCH ``~(name IN FDOM (ctxt:context_type))``
  |> SIMP_RULE std_ss [DOMSUB_NOT_IN_DOM]
  |> SIMP_RULE std_ss [AND_IMP_INTRO]

val IMP_LSIZE_CAR = prove(
  ``!x. LSIZE x < n ==> LSIZE (CAR x) < n``,
  Cases \\ EVAL_TAC \\ DECIDE_TAC);

val IMP_LSIZE_CDR = prove(
  ``!x. LSIZE x < n ==> LSIZE (CDR x) < n``,
  Cases \\ EVAL_TAC \\ DECIDE_TAC);

val MEM_sexp2list_IMP = prove(
  ``!x a. MEM a (sexp2list x) ==> LSIZE a < LSIZE x``,
  Induct \\ FULL_SIMP_TAC std_ss [LSIZE_def,sexp2list_def,MEM]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FS [] \\ DECIDE_TAC);

val string2func_def = Define `
  string2func name =
    case logic_sym2prim name of
      SOME op => mPrimitiveFun op
    | NONE => mFun name`;

val sexp2t_def = tDefine "sexp2t" `
  sexp2t x = if isSym x then mVar (getSym x) else
             if isVal x then mConst x else
             if CAR x = Sym "QUOTE" then mConst (CAR (CDR x)) else
             if isDot (CAR x) then
               let lam = CAR x in
               let vs = MAP getSym (sexp2list (CAR (CDR lam))) in
               let body = sexp2t (CAR (CDR (CDR lam))) in
               let xs = MAP sexp2t (sexp2list (CDR x)) in
                 mLamApp vs body xs
             else
               let xs = MAP sexp2t (sexp2list (CDR x)) in
                 mApp (string2func (getSym (CAR x))) xs`
 (WF_REL_TAC `measure LSIZE` \\ REPEAT STRIP_TAC \\ Cases_on `x`
  \\ FULL_SIMP_TAC std_ss [LSIZE_def,isSym_def,isVal_def,CAR_def,CDR_def]
  THEN1 (IMP_RES_TAC MEM_sexp2list_IMP \\ DECIDE_TAC)
  THEN1 (FULL_SIMP_TAC std_ss [isDot_thm,CAR_def,CDR_def,LSIZE_def]
         \\ MATCH_MP_TAC IMP_LSIZE_CAR \\ MATCH_MP_TAC IMP_LSIZE_CDR \\ DECIDE_TAC)
  THEN1 (IMP_RES_TAC MEM_sexp2list_IMP \\ DECIDE_TAC));

val defun_ctxt_def = Define `
  defun_ctxt ctxt cmd =
    let name = getSym (CAR (CDR cmd)) in
    let formals = MAP getSym (sexp2list (CAR (CDR (CDR cmd)))) in
    let body = BODY_FUN (sexp2t (sexp2sexp (CAR (CDR (CDR (CDR cmd)))))) in
    let interp = @interp. context_ok (ctxt |+ (name,formals,body,interp)) in
      if name IN FDOM ctxt UNION {"NOT";"RANK";"ORDP";"ORD<"} then ctxt
      else ctxt |+ (name,formals,body,interp)`;

val sexp2t_t2sexp_thm = prove(
  ``!b. term_syntax_ok b ==> (sexp2t (t2sexp b) = b)``,
  HO_MATCH_MP_TAC t2sexp_ind \\ REPEAT STRIP_TAC
  THEN1 (FS [t2sexp_def,Once sexp2t_def,getSym_def,LET_DEF])
  THEN1 (FS [t2sexp_def,Once sexp2t_def,getSym_def,LET_DEF])
  THEN1
   (FULL_SIMP_TAC std_ss [t2sexp_def,term_syntax_ok_def,EVERY_MEM,list2sexp_def]
    \\ ONCE_REWRITE_TAC [sexp2t_def] \\ FS [LET_DEF]
    \\ SIMP_TAC (srw_ss()) [] \\ STRIP_TAC THEN1
     (Cases_on `fc` \\ FS [func_syntax_ok_def,getSym_def,logic_func2sexp_def]
      THEN1 (Cases_on `l` \\ EVAL_TAC) \\ EVAL_TAC \\ FS [getSym_def])
    \\ Induct_on `vs` \\ FS [MAP])
  THEN1
   (FULL_SIMP_TAC std_ss [t2sexp_def,term_syntax_ok_def,EVERY_MEM,list2sexp_def]
    \\ ONCE_REWRITE_TAC [sexp2t_def] \\ FS [LET_DEF]
    \\ SIMP_TAC (srw_ss()) [] \\ STRIP_TAC
    \\ Q.PAT_X_ASSUM `LENGTH xs = LENGTH ys` (K ALL_TAC)
    \\ Q.PAT_X_ASSUM `set (free_vars b) SUBSET set xs` (K ALL_TAC)
    THEN1 (Induct_on `xs` \\ FS [MAP,getSym_def,CONS_11,ALL_DISTINCT])
    THEN1 (Induct_on `ys` \\ FS [MAP,getSym_def,CONS_11,ALL_DISTINCT])));

val term_ok_syntax_same = prove(
  ``!ctxt x ctxt2. term_ok ctxt x /\ context_syntax_same ctxt ctxt2 ==> term_ok ctxt2 x``,
  HO_MATCH_MP_TAC term_ok_ind \\ FULL_SIMP_TAC std_ss [term_ok_def,EVERY_MEM]
  \\ REPEAT STRIP_TAC \\ Cases_on `fc`
  \\ FULL_SIMP_TAC std_ss [func_arity_def,context_syntax_same_def,FEVERY_DEF]
  \\ POP_ASSUM MP_TAC \\ FS [] \\ STRIP_TAC \\ RES_TAC
  \\ POP_ASSUM MP_TAC \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ REPEAT STRIP_TAC \\ FS []);

val formula_ok_syntax_same = prove(
  ``!ctxt x ctxt2. formula_ok ctxt x /\ context_syntax_same ctxt ctxt2 ==> formula_ok ctxt2 x``,
  STRIP_TAC \\ Induct \\ FS [formula_ok_def] \\ METIS_TAC [term_ok_syntax_same]);

fun TAC n =
   (SIMP_TAC std_ss [Once MilawaTrue_cases]
    \\ NTAC n DISJ2_TAC \\ TRY DISJ1_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [FAPPLY_FUPDATE_THM]
    \\ METIS_TAC [formula_ok_syntax_same])

val MilawaTrue_context_syntax_same = prove(
  ``!ctxt x.
      MilawaTrue ctxt x ==> context_syntax_same ctxt ctxt2 ==>
      MilawaTrue ctxt2 x``,
  HO_MATCH_MP_TAC MilawaTrue_ind \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  THEN1 TAC 0 THEN1 TAC 1 THEN1 TAC 2 THEN1 TAC 3 THEN1 TAC 4 THEN1 TAC 5
  THEN1 TAC 6 THEN1 TAC 7 THEN1 TAC 8 THEN1 TAC 9
  THEN1
   (SIMP_TAC std_ss [Once MilawaTrue_cases]
    \\ NTAC 10 DISJ2_TAC \\ TRY DISJ1_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [FAPPLY_FUPDATE_THM]
    \\ FS [context_syntax_same_def,FEVERY_DEF]
    \\ POP_ASSUM MP_TAC \\ FS []
    \\ REPEAT STRIP_TAC \\ RES_TAC \\ POP_ASSUM MP_TAC \\ POP_ASSUM (K ALL_TAC)
    \\ `?x1 x2 x3. ctxt2 ' f = (x1,x2,x3)` by METIS_TAC [PAIR] \\ FS [])
  THEN1
   (SIMP_TAC std_ss [Once MilawaTrue_cases]
    \\ NTAC 11 DISJ2_TAC \\ TRY DISJ1_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [FAPPLY_FUPDATE_THM]
    \\ FS [context_syntax_same_def,FEVERY_DEF]
    \\ POP_ASSUM MP_TAC \\ FS []
    \\ REPEAT STRIP_TAC \\ RES_TAC \\ POP_ASSUM MP_TAC \\ POP_ASSUM (K ALL_TAC)
    \\ `?x1 x2 x3. ctxt2 ' f = (x1,x2,x3)` by METIS_TAC [PAIR] \\ FS [])
  \\ SIMP_TAC std_ss [Once MilawaTrue_cases]
  \\ NTAC 12 DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`qs_ss`,`m`]
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ RES_TAC)
  |> SIMP_RULE std_ss [];

val context_syntax_same_FUPDATE = prove(
  ``!x. context_syntax_same ctxt ctxt2 ==>
        context_syntax_same (ctxt |+ x) (ctxt2 |+ x)``,
  FS [context_syntax_same_def,FORALL_PROD,FDOM_FUPDATE,FEVERY_DEF,
    FAPPLY_FUPDATE_THM,IN_INSERT]
  \\ NTAC 6 STRIP_TAC \\ Cases_on `x = p_1` \\ FS [] \\ STRIP_TAC
  \\ Q.PAT_X_ASSUM `!x.bbb` MP_TAC \\ FS []);

val similar_context_definition_ok = prove(
  ``similar_context ctxt ctxt2 ==>
    definition_ok (fname,params,b,ctxt) ==>
    definition_ok (fname,params,b,ctxt2)``,
  REVERSE (Cases_on `b`) \\ FULL_SIMP_TAC std_ss [definition_ok_def]
  THEN1 (FS [similar_context_def])
  THEN1 (REPEAT STRIP_TAC \\ TRY (MATCH_MP_TAC term_ok_syntax_same)
         \\ TRY (Q.EXISTS_TAC `ctxt`)
         \\ FS [similar_context_def,context_syntax_same_def]
         \\ METIS_TAC [])
  THEN1
   (REPEAT STRIP_TAC
    \\ `context_syntax_same ctxt ctxt2` by FS [context_syntax_same_def,similar_context_def]
    \\ `context_syntax_same (ctxt |+ (fname,params,NO_FUN,ARB))
                            (ctxt2 |+ (fname,params,NO_FUN,ARB))` by
          METIS_TAC [context_syntax_same_FUPDATE]
    \\ `context_syntax_same (ctxt |+ (fname,params,BODY_FUN l,ARB))
                            (ctxt2 |+ (fname,params,BODY_FUN l,ARB))` by
          METIS_TAC [context_syntax_same_FUPDATE]
    THEN1 (METIS_TAC [term_ok_syntax_same])
    THEN1 (FS [similar_context_def] \\ METIS_TAC [])
    \\ FS [EVERY_MEM] \\ METIS_TAC [MilawaTrue_context_syntax_same]));

val core_admit_defun_thm = prove(
  ``milawa_inv ctxt simple_ctxt k (axioms,thms,atbl,checker,ftbl) ==>
    ?x k2 io2 ok2 result.
      core_admit_defun_side cmd (milawa_state (axioms,thms,atbl,checker,ftbl)) k io ok /\
      (core_admit_defun cmd (milawa_state (axioms,thms,atbl,checker,ftbl)) k io ok =
         (x,k2,io2,ok2)) /\
      (ok2 ==> (io2 = io) /\
               ?result ctxt.
                  (x = milawa_state result) /\
                  milawa_inv ctxt (defun_ctxt simple_ctxt cmd) k2 result)``,
  FS [core_admit_defun_side_lemma,core_admit_defun_lemma,
      LET_DEF,milawa_state_def,core_state_def]
  \\ SRW_TAC [] [] \\ FS [] \\ FS [milawa_inv_def]
  \\ ASM_SIMP_TAC std_ss [core_check_proof_list_inv_IMP_side]
  \\ IMP_RES_TAC SND_SND_SND_define_safe_IMP
  \\ IMP_RES_TAC core_check_proof_list_inv_IMP
  \\ IMP_RES_TAC core_admit_defun_cmd \\ FS []
  \\ Q.PAT_X_ASSUM `formals = list2sexp xs` ASSUME_TAC \\ FS []
  THEN1 (SRW_TAC [] [define_safe_def] \\ FS [define_safe_def]
         \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [LET_DEF])
  \\ REPEAT (Q.PAT_X_ASSUM `!xx.bbb` (K ALL_TAC)) \\ POP_ASSUM (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `xxx = io` (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `xxx = k` (K ALL_TAC)
  \\ POP_ASSUM (K ALL_TAC)
  \\ IMP_RES_TAC core_check_proof_list_inv_IMP_OK \\ FULL_SIMP_TAC std_ss []
  \\ `isTrue (logic_translate body) /\ isTrue (logic_translate meas)` by
    (SIMP_TAC std_ss [isTrue_def] \\ REPEAT STRIP_TAC
     \\ FS [EVAL ``logic_termp (Sym "NIL")``])
  \\ FS [logic_translate_thm] \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
  \\ `?b. term_syntax_ok b /\ (sexp2sexp body = t2sexp b)` by METIS_TAC [logic_termp_thm]
  \\ `?m. term_syntax_ok m /\ (sexp2sexp meas = t2sexp m)` by METIS_TAC [logic_termp_thm]
  \\ FS [] \\ `?fname. name = Sym fname` by
    (Cases_on `isSym name` \\ FS [logic_function_namep_def] \\ FS [isSym_thm])
  \\ FS [] \\ POP_ASSUM (K ALL_TAC)
  \\ REPEAT (Q.PAT_X_ASSUM `isTrue (logic_termp (t2sexp xxx))` (K ALL_TAC))
  \\ `set xs = set (MAP Sym (MAP getSym xs))` by
     (IMP_RES_TAC logic_variable_listp_thm \\ FS [])
  \\ FS [] \\ POP_ASSUM (K ALL_TAC)
  \\ Q.ABBREV_TAC `new_axiom = Equal ((mApp (func2f (Fun fname)) (MAP mVar (MAP getSym xs)))) b`
  \\ Q.ABBREV_TAC `if_new_axiom = if MEM new_axiom axioms then axioms else new_axiom :: axioms`
  \\ Q.ABBREV_TAC `if_new_atbl = if_lookup (Sym fname) atbl (Dot (Dot (Sym fname) (Val (LENGTH xs))) atbl)`
  \\ `~(fname = "ERROR")` by METIS_TAC [NAME_NOT_ERROR]
  \\ Cases_on `isTrue (lookup (Sym fname) atbl)` THEN1
   (Q.EXISTS_TAC `(axioms,thms,atbl,checker,ftbl)` \\ Q.EXISTS_TAC `ctxt`
    \\ FS [milawa_inv_def,milawa_state_def,core_state_def]
    \\ Q.UNABBREV_TAC `if_new_atbl` \\ FS [if_lookup_def]
    \\ FULL_SIMP_TAC std_ss [if_memberp_def]
    \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC]
    \\ Q.PAT_X_ASSUM `axioms_inv ctxt ftbl axioms` ASSUME_TAC
    \\ FS [atbl_ftbl_inv_def] \\ RES_TAC
    \\ FS [define_safe_ID]
    \\ `?fparams fbody fsem.
          func_definition_exists ctxt fname fparams fbody fsem` suffices_by (STRIP_TAC THEN REVERSE STRIP_TAC THEN1
       (SUFF_TAC ``fname IN FDOM (ctxt:context_type) UNION {"NOT";"RANK";"ORDP";"ORD<"}``
        THEN1 (FS [defun_ctxt_def,similar_context_def,LET_DEF,getSym_def])
        \\ FS [axioms_inv_def,EVERY_DEF,func_definition_exists_def,IN_UNION,IN_INSERT])
      \\ MATCH_MP_TAC (METIS_PROVE [] ``x ==> ((if x then y else z) = y)``)
      \\ FS [axioms_inv_def] \\ REVERSE (Cases_on `fbody`)
      \\ RES_TAC \\ FS [axioms_aux_def] \\ FS [] THEN1
       (IMP_RES_TAC MEM_ftbl
        \\ IMP_RES_TAC MEM_MEM_ftbl
        \\ FS [] \\ FS [sexp2sexp_def,witness_body_def]
        \\ REPEAT (Q.PAT_X_ASSUM `T` (K ALL_TAC))
        \\ Q.PAT_X_ASSUM `xxx = body` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
        \\ Q.PAT_X_ASSUM `term2t (sexp3term xx) = b` MP_TAC
        \\ SIMP_TAC (srw_ss()) [Once sexp3term_def,LET_DEF] \\ FS []
        \\ SIMP_TAC (srw_ss()) [] \\ FS [getSym_def,sym2prim_def]
        \\ SIMP_TAC (srw_ss()) [] \\ FS []
        \\ SIMP_TAC std_ss [sexp2list_def,MAP]
        \\ SIMP_TAC (srw_ss()) [Once sexp3term_def,LET_DEF] \\ FS []
        \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ STRIP_TAC \\ FS []
        \\ REPEAT (Q.PAT_X_ASSUM `isTrue (logic_term_atblp xxx yyy)` MP_TAC)
        \\ SIMP_TAC (srw_ss()) [logic_term_atblp_def,t2sexp_def,
             term2t_def,MAP,func2f_def,logic_func2sexp_def,list2sexp_def]
        \\ ONCE_REWRITE_TAC [logic_flag_term_atblp_def] \\ FS []
        \\ FS [logic_variablep_def,logic_function_namep_def]
        \\ FULL_SIMP_TAC std_ss [GSYM list2sexp_def,memberp_thm] \\ FS []
        \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
        \\ `CDR (lookup (Sym "ERROR")
             (Dot (Dot (Sym fname) (Val (LENGTH xs))) atbl)) = Sym "NIL"` by
         (ONCE_REWRITE_TAC [lookup_def] \\ FS []
          \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [GSYM isTrue_def]
          \\ `isTrue ((lookup (Sym "ERROR") atbl))` by
          (Cases_on `lookup (Sym "ERROR") atbl`
            \\ FULL_SIMP_TAC (srw_ss()) [isTrue_def,CDR_def])
          \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
        \\ FS [] \\ FULL_SIMP_TAC std_ss [GSYM list2sexp_def,len_thm] \\ FS [])
      \\ Q.PAT_X_ASSUM `MEM xx axioms` MP_TAC
      \\ ASM_SIMP_TAC std_ss [def_axiom_def]
      \\ SIMP_TAC std_ss [MEM_MAP]
      \\ HO_MATCH_MP_TAC (METIS_PROVE [] ``P x ==> (MEM x xs ==> ?y. P y /\ MEM y xs)``)
      \\ FS [f2sexp_def,t2sexp_def]
      \\ IMP_RES_TAC MEM_ftbl
      \\ IMP_RES_TAC MEM_MEM_ftbl
      \\ FS [] \\ FS [sexp2sexp_def]
      \\ Cases_on `MEM fname ["NOT";"RANK";"ORDP";"ORD<"]` THEN1 (FS [] \\ EVAL_TAC)
      \\ FS [fake_ftbl_entries_def] \\ FULL_SIMP_TAC std_ss
        [logic_function_namep_def,GSYM list2sexp_def,memberp_thm,MEM] \\ FS []
      \\ FS [func_syntax_ok_def,logic_func2sexp_def,str2func_def,logic_prim2sym_def]
      \\ IMP_RES_TAC fake_ftbl_entries \\ FS [fake_ftbl_entries_def])
    \\ Cases_on `MEM fname ["NOT";"RANK";"ORDP";"ORD<"]` THEN1
     (ASM_SIMP_TAC std_ss [func_definition_exists_def]
      \\ METIS_TAC [lookup_safe_init_ftbl_EXISTS,MEM])
    \\ `(logic_func2sexp (mFun fname) = Sym fname) /\
        func_syntax_ok (mFun fname)` by
     (FS [fake_ftbl_entries_def] \\ FULL_SIMP_TAC std_ss
        [logic_function_namep_def,GSYM list2sexp_def,memberp_thm,MEM] \\ FS []
      \\ FS [func_syntax_ok_def,logic_func2sexp_def,str2func_def]
      \\ IMP_RES_TAC fake_ftbl_entries \\ FS [fake_ftbl_entries_def])
    \\ `fname IN FDOM ctxt` by
     (CCONTR_TAC \\ Q.PAT_X_ASSUM `atbl_ok ctxt atbl` ASSUME_TAC
      \\ FULL_SIMP_TAC std_ss [atbl_ok_def]
      \\ POP_ASSUM (MP_TAC o Q.SPEC `mFun fname`)
      \\ FS [func_arity_def,CDR_lookup_NOT_NIL])
    \\ `?fparams fbody fsem. ctxt ' fname = (fparams,fbody,fsem)` by METIS_TAC [PAIR]
    \\ METIS_TAC [func_definition_exists_def])
  \\ `~MEM fname ["NOT";"RANK";"ORDP";"ORD<"]` by
   (STRIP_TAC \\ Q.PAT_X_ASSUM `atbl_ok ctxt atbl` ASSUME_TAC
    \\ FS [atbl_ok_def] THENL [
      POP_ASSUM (MP_TAC o Q.SPEC `mPrimitiveFun logic_NOT`)
      \\ FS [func_syntax_ok_def,isTrue_def,logic_func2sexp_def,
             logic_prim2sym_def,func_arity_def],
      POP_ASSUM (MP_TAC o Q.SPEC `mPrimitiveFun logic_RANK`)
      \\ FS [func_syntax_ok_def,isTrue_def,logic_func2sexp_def,
             logic_prim2sym_def,func_arity_def],
      POP_ASSUM (MP_TAC o Q.SPEC `mPrimitiveFun logic_ORDP`)
      \\ FS [func_syntax_ok_def,isTrue_def,logic_func2sexp_def,
             logic_prim2sym_def,func_arity_def],
      POP_ASSUM (MP_TAC o Q.SPEC `mPrimitiveFun logic_ORD_LESS`)
      \\ FS [func_syntax_ok_def,isTrue_def,logic_func2sexp_def,
             logic_prim2sym_def,func_arity_def]])
  \\ FS [if_lookup_def]
  \\ Q.EXISTS_TAC `(if_new_axiom,thms,if_new_atbl,checker,
       FST (define_safe ftbl (Sym fname) (list2sexp xs) body k io T))`
  \\ Q.ABBREV_TAC `ef = EvalFun fname (ctxt |+ (fname,MAP getSym xs,BODY_FUN b,ARB))`
  \\ Q.EXISTS_TAC `ctxt |+ (fname,MAP getSym xs,BODY_FUN b,ef)`
  \\ IMP_RES_TAC fake_ftbl_entries
  \\ STRIP_TAC THEN1
   (UNABBREV_ALL_TAC \\ FS [milawa_state_def,core_state_def] \\ FS [if_memberp_def]
    \\ FS [MEM,fake_ftbl_entries_def]
    \\ `f2sexp (Equal ((mApp (func2f (Fun fname)) (MAP mVar (MAP getSym xs)))) b) =
     Dot (Sym "PEQUAL*") (Dot
         (Dot (Sym fname) (list2sexp (MAP t2sexp (MAP mVar (MAP getSym xs)))))
         (Dot (t2sexp b) (Sym "NIL")))` by
    (FS [EVAL ``f2sexp (Equal ((mApp (func2f (Fun fname)) (MAP mVar (MAP getSym xs)))) b)``]
      \\ SRW_TAC [] [] \\ EVAL_TAC
      \\ FS [MEM,fake_ftbl_entries_def]
      \\ SRW_TAC [] [] \\ FS [logic_function_namep_def]
      \\ FULL_SIMP_TAC std_ss [GSYM list2sexp_def,memberp_thm,MEM] \\ FS [])
    \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ FS []
    \\ IMP_RES_TAC (logic_variable_listp_thm) \\ FS [] \\ SRW_TAC [] [] \\ FS [])
  \\ FULL_SIMP_TAC std_ss [milawa_inv_def]
  \\ `ALL_DISTINCT (MAP getSym xs)` by METIS_TAC [logic_variable_listp_ALL_DISTINCT_IMP]
  \\ `~(fname IN FDOM ctxt)` by
   (REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `atbl_ok ctxt atbl` MP_TAC
    \\ FS [atbl_ok_def] \\ Q.EXISTS_TAC `mFun fname`
    \\ FS [fake_ftbl_entries_def] \\ FULL_SIMP_TAC std_ss
         [logic_function_namep_def,GSYM list2sexp_def,memberp_thm,MEM] \\ FS []
    \\ STRIP_TAC THEN1 (EVAL_TAC \\ FS [])
    \\ ASM_SIMP_TAC std_ss [logic_func2sexp_def,MEM] \\ FS [isTrue_def]
    \\ FS [func_arity_def])
  \\ `!body. atbl_ok (ctxt |+ (fname,MAP getSym xs,body,ef)) if_new_atbl` by
   (FS [atbl_ok_def] \\ REPEAT STRIP_TAC \\ RES_TAC \\ Q.UNABBREV_TAC `if_new_atbl`
    \\ Cases_on `f` \\ FULL_SIMP_TAC std_ss [func_arity_def]
    \\ `!l. ~(logic_func2sexp (mPrimitiveFun l) = Sym fname)` by
       (FS [fake_ftbl_entries_def] \\ FULL_SIMP_TAC std_ss
         [logic_function_namep_def,GSYM list2sexp_def,memberp_thm,MEM] \\ FS []
        \\ Cases \\ EVAL_TAC \\ FS [])
    \\ ONCE_REWRITE_TAC [lookup_def] \\ FS []
    \\ `(logic_func2sexp (mFun s) = Sym fname) = (s = fname)` by
     (FULL_SIMP_TAC std_ss [logic_func2sexp_def] \\ SRW_TAC [] []
      \\ FS [fake_ftbl_entries_def] \\ FULL_SIMP_TAC std_ss
          [logic_function_namep_def,GSYM list2sexp_def,memberp_thm,MEM] \\ FS [])
    \\ FS [FDOM_FUPDATE,IN_INSERT,FAPPLY_FUPDATE_THM]
    \\ Cases_on `s = fname` \\ FS [LENGTH_MAP])
  \\ `atbl_ok (ctxt |+ (fname,MAP getSym xs,BODY_FUN b,ef)) if_new_atbl /\
      atbl_ok (ctxt |+ (fname,MAP getSym xs,NO_FUN,ef)) if_new_atbl` by METIS_TAC []
  \\ `thms_inv (ctxt |+ (fname,MAP getSym xs,BODY_FUN b,ef)) thms` by
   (FS [thms_inv_def,EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ IMP_RES_TAC MilawaTrue_new_definition \\ METIS_TAC [])
  \\ `thms_inv (ctxt |+ (fname,MAP getSym xs,BODY_FUN b,ef)) axioms` by
   (FS [thms_inv_def,EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ IMP_RES_TAC MilawaTrue_new_definition \\ METIS_TAC [])
  \\ FS []
  \\ `func2f (Fun fname) = mFun fname` by
       (FS [fake_ftbl_entries_def] \\ FULL_SIMP_TAC std_ss
          [logic_function_namep_def,GSYM list2sexp_def,memberp_thm,MEM,func2f_def])
  \\ `term_ok (ctxt |+ (fname,MAP getSym xs,NO_FUN,ef)) b /\
      EVERY (MilawaTrue (ctxt |+ (fname,MAP getSym xs,NO_FUN,ef)))
        (termination_obligations fname b (MAP getSym xs) m)` by
   (`term_ok (ctxt |+ (fname,MAP getSym xs,NO_FUN,ef)) b` by (IMP_RES_TAC logic_term_atblp_thm) \\ FS []
    \\ MP_TAC (logic_termination_obligations_thm
      |> Q.INST [`body`|->`b`,`name`|->`fname`,`formals`|->`MAP getSym xs`,
                 `ctxt`|->`ctxt |+ (fname,MAP getSym xs,NO_FUN,ef)`])
    \\ FS [FAPPLY_FUPDATE_THM,LENGTH_MAP]
    \\ MATCH_MP_TAC IMP_IMP
    \\ STRIP_TAC THEN1 (FS [logic_func2sexp_def]
      \\ FS [fake_ftbl_entries_def] \\ FULL_SIMP_TAC std_ss
          [logic_function_namep_def,GSYM list2sexp_def,memberp_thm,MEM] \\ FS [])
    \\ STRIP_TAC \\ FS [] \\ POP_ASSUM (K ALL_TAC)
    \\ STRIP_ASSUME_TAC (Q.SPEC `proof_list` anylist2sexp_EXISTS)
    \\ FS [] \\ IMP_RES_TAC logic_appeal_anylistp_thm
    \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (K ALL_TAC) \\ FS []
    \\ FS [logic_strip_conclusions_thm,MAP_f2sexp_11]
    \\ Q.PAT_X_ASSUM `MAP CONCL ts = bbb` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `isTrue bbb` MP_TAC
    \\ Q.PAT_X_ASSUM `SND (SND xxx)` MP_TAC
    \\ SIMP_TAC std_ss [AND_IMP_INTRO]
    \\ MATCH_MP_TAC core_check_proof_list_thm \\ FS []
    \\ STRIP_TAC THEN1 (MATCH_MP_TAC context_ok_None \\ FS [])
    \\ FS [thms_inv_def,EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ IMP_RES_TAC MilawaTrue_new_definition \\ METIS_TAC [])
  \\ `term_ok (ctxt |+ (fname,MAP getSym xs,BODY_FUN b,ef)) b` by (FS [EvalTerm_IGNORE_BODY])
  \\ `definition_ok (fname,MAP getSym xs,BODY_FUN b,ctxt)` by
   (FS [definition_ok_def,term_ok_IGNORE_SEM,MilawaTrue_IGNORE_SEM,
      EvalTerm_IGNORE_BODY] \\ Q.EXISTS_TAC `m` \\ FS []) \\ FS []
  \\ PUSH_STRIP_TAC THEN1 (METIS_TAC [definition_ok_BODY_FUN])
  \\ PUSH_STRIP_TAC THEN1
   (FS [context_inv_def] \\ STRIP_TAC \\ STRIP_TAC \\ Cases_on `fname = fname'`
    \\ FULL_SIMP_TAC (srw_ss()) [FAPPLY_FUPDATE_THM]
    THEN1 (Q.UNABBREV_TAC `ef` \\ FS [EvalFun_IGNORE_SEM])
    \\ REPEAT STRIP_TAC \\ FS [context_inv_def] \\ RES_TAC \\ FS []
    \\ `term_ok ctxt body'` by (FS [context_ok_def] \\ RES_TAC)
    \\ IMP_RES_TAC EvalFun_FUPDATE \\ FS [GSYM EvalTerm_FUPDATE])
  \\ PUSH_STRIP_TAC THEN1
   (IMP_RES_TAC similar_context_definition_ok
    \\ FS [similar_context_def,defun_ctxt_def,getSym_def,LET_DEF]
    \\ `~(fname IN FDOM ctxt UNION {"NOT"; "RANK"; "ORDP"; "ORD<"})` by FS [IN_INSERT,IN_UNION,NOT_IN_EMPTY] \\ FS [FDOM_FUPDATE]
    \\ FS [sexp2t_t2sexp_thm] \\ STRIP_TAC THEN1 (METIS_TAC [definition_ok_thm])
    \\ FS [FEVERY_DEF,FDOM_FUPDATE,IN_INSERT,FAPPLY_FUPDATE_THM] \\ STRIP_TAC
    \\ Cases_on `x' = fname` \\ FS []
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `FDOM simple_ctxt = FDOM ctxt` ASSUME_TAC \\ FS []
    \\ RES_TAC \\ POP_ASSUM MP_TAC
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ REPEAT STRIP_TAC
    \\ FS [])
  \\ PUSH_STRIP_TAC THEN1
   (Q.UNABBREV_TAC `if_new_atbl` \\ FS [atbl_inv_def,EVERY_DEF,sexp2list_def])
  \\ PUSH_STRIP_TAC THEN1
   (Q.UNABBREV_TAC `if_new_axiom`
    \\ `thms_inv (ctxt |+ (fname,MAP getSym xs,BODY_FUN b,ef)) (new_axiom::axioms)` suffices_by
    (STRIP_TAC THEN FS [thms_inv_def,EVERY_DEF] \\ SRW_TAC [] [EVERY_DEF])
    \\ FS [thms_inv_def,EVERY_DEF]
    \\ REVERSE (REPEAT STRIP_TAC) \\ Q.UNABBREV_TAC `new_axiom` THEN1
     (FS [formula_syntax_ok_def,term_syntax_ok_def,EVERY_MEM,MEM_MAP,func_syntax_ok_def]
      \\ FS [fake_ftbl_entries_def] \\ FULL_SIMP_TAC std_ss
            [logic_function_namep_def,GSYM list2sexp_def,memberp_thm,MEM,func2f_def]
      \\ FS [] \\ REPEAT STRIP_TAC \\ FS [term_syntax_ok_def]
      \\ IMP_RES_TAC logic_variable_listp_IMP_EVERY
      \\ FS [EVERY_MEM])
    \\ ((CONJUNCTS MilawaTrue_rules)
          |> filter (can (find_term (aconv ``BODY_FUN``) o concl))
          |> hd |> MATCH_MP_TAC)
    \\ FS [FDOM_FUPDATE,IN_INSERT,
         FAPPLY_FUPDATE_THM]
    \\ Q.EXISTS_TAC `m` \\ FULL_SIMP_TAC std_ss [])
  \\ PUSH_STRIP_TAC THEN1
   (Cases_on `(FST (SND (define_safe ftbl (Sym fname) (list2sexp xs) body k io T))) = k`
    \\ FULL_SIMP_TAC std_ss []
    \\ `?new_def. (FST (SND (define_safe ftbl (Sym fname) (list2sexp xs) body k io T))) =
                  add_def k new_def` by
      (FULL_SIMP_TAC std_ss [define_safe_def,LET_DEF] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `core_check_proof_inv checker k` MP_TAC
    \\ METIS_TAC [core_check_proof_inv_step])
  \\ PUSH_STRIP_TAC THEN1
   (FS [define_safe_def,LET_DEF]
    \\ Cases_on `isTrue (lookup_safe (Sym fname) ftbl)` \\ FS []
    \\ FS [ftbl_inv_def,getSym_def]
    \\ REVERSE STRIP_TAC THEN1
     (FS [sexp2list_def,EVERY_DEF]
      \\ ONCE_REWRITE_TAC [lookup_safe_def] \\ FS [EVERY_MEM]
      \\ REPEAT STRIP_TAC \\ SRW_TAC [] [] \\ FS [lookup_safe_EQ_MEM]
      \\ Q.EXISTS_TAC `SUC old` \\ FS [FUNPOW])
    \\ SIMP_TAC std_ss [sexp2list_def,EVERY_DEF]
    \\ STRIP_TAC THEN1
     (FS [LET_DEF,getSym_def,add_def_def,FDOM_FUNION,
        IN_UNION,FDOM_FEMPTY,FDOM_FUPDATE,
        IN_INSERT,FUNION_DEF,FAPPLY_FUPDATE_THM])
    \\ FS [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC THEN1
     (FS [LET_DEF,getSym_def,add_def_def,FDOM_FUNION,
        IN_UNION,FDOM_FEMPTY,FDOM_FUPDATE,
        IN_INSERT,FUNION_DEF,FAPPLY_FUPDATE_THM]))
  \\ PUSH_STRIP_TAC THEN1
   (SIMP_TAC std_ss [axioms_inv_def] \\ STRIP_TAC
    THEN1 (FULL_SIMP_TAC std_ss [EVERY_DEF,FDOM_FUPDATE,IN_INSERT,axioms_inv_def])
    \\ FS [axioms_inv_def,FDOM_FUPDATE,FAPPLY_FUPDATE_THM] \\ STRIP_TAC
    \\ REVERSE (Cases_on `name = fname`) \\ FS [IN_INSERT]
    \\ FS [func_definition_exists_NEQ] THEN1
     (REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `!name params body sem. bbb` IMP_RES_TAC
      \\ REVERSE (Cases_on `body'`) \\ FULL_SIMP_TAC std_ss [axioms_aux_def] THEN1
       (Q.EXISTS_TAC `raw_body` \\ POP_ASSUM MP_TAC \\ FS [] \\ STRIP_TAC
        \\ STRIP_TAC THEN1
          (FS [define_safe_def,LET_DEF]
           \\ Cases_on `isTrue (lookup_safe (Sym fname) ftbl)`
           \\ FS [sexp2list_def,MEM])
        \\ Q.UNABBREV_TAC `if_new_axiom` \\ METIS_TAC [MEM])
      \\ Q.EXISTS_TAC `raw_body` \\ POP_ASSUM MP_TAC \\ FS [] \\ STRIP_TAC
      \\ STRIP_TAC THEN1
        (FS [define_safe_def,LET_DEF]
         \\ Cases_on `isTrue (lookup_safe (Sym fname) ftbl)`
         \\ FS [sexp2list_def,MEM])
      \\ STRIP_TAC THEN1 (Q.UNABBREV_TAC `if_new_axiom` \\ METIS_TAC [MEM])
      \\ Cases_on `MEM name ["NOT"; "RANK"; "ORD<"; "ORDP"]`
      THEN1 (FS [logic_func_inv_def])
      \\ `name IN FDOM ctxt` by METIS_TAC [func_definition_exists_def]
      \\ MATCH_MP_TAC logic_func_inv_NEQ \\ FS [sexp2sexp_def]
      \\ FS [func_definition_exists_def]
      \\ METIS_TAC [context_ok_def])
    \\ FS [func_definition_exists_EQ,MEM,axioms_aux_def]
    \\ Q.EXISTS_TAC `body` \\ FS [] \\ REPEAT STRIP_TAC THEN1
     (FS [define_safe_def,LET_DEF]
      \\ Cases_on `isTrue (lookup_safe (Sym fname) ftbl)` \\ FS [sexp2list_def,MEM]
      \\ Q.PAT_X_ASSUM `lookup_safe (Sym fname) ftbl = bb` (ASSUME_TAC o GSYM)
      \\ FS [ftbl_inv_def] \\ FULL_SIMP_TAC std_ss [isTrue_lookup_safe])
    THEN1 (FS [sexp2sexp_def]) THEN1
     (FS [sexp2sexp_def]
      \\ Q.UNABBREV_TAC `if_new_axiom` \\ Q.UNABBREV_TAC `new_axiom`
      \\ `(func2f (Fun fname) = mFun fname) /\ (str2func fname = mFun fname)` by
       (FS [str2func_def,fake_ftbl_entries_def] \\ FULL_SIMP_TAC std_ss
         [logic_function_namep_def,GSYM list2sexp_def,memberp_thm,MEM,func2f_def])
      \\ FULL_SIMP_TAC std_ss [def_axiom_def]
      \\ SRW_TAC [] [])
    THEN1
     (MATCH_MP_TAC logic_func_inv_EQ
      \\ ASM_SIMP_TAC std_ss [logic_variable_listp_IMP_EVERY_Sym]
      \\ FS [EvalTerm_IGNORE_BODY,EvalFun_IGNORE_SEM]
      \\ REVERSE STRIP_TAC THEN1 (FS [sexp2sexp_def])
      \\ FS [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ MATCH_MP_TAC MilawaTrue_REPLACE_NO_FUN \\ FS [])
    \\ `~("ERROR" IN FDOM ((ctxt |+ (fname,MAP getSym xs,BODY_FUN b,ef))))` by
     (FULL_SIMP_TAC std_ss [FDOM_FUPDATE,IN_INSERT]
      \\ FULL_SIMP_TAC std_ss [atbl_ok_def] \\ REPEAT STRIP_TAC
      \\ Q.PAT_X_ASSUM `!f. func_syntax_ok f ==> bbb` (MP_TAC o Q.SPEC `mFun "ERROR"`)
      \\ FULL_SIMP_TAC (srw_ss()) [func_syntax_ok_def,MEM,logic_func2sexp_def]
      \\ FULL_SIMP_TAC std_ss [func_arity_def,FDOM_FUPDATE,IN_INSERT]
      \\ `lookup (Sym "ERROR") atbl = Sym "NIL"` by METIS_TAC [atbl_ftbl_inv_def,isTrue_def]
      \\ Q.UNABBREV_TAC `if_new_atbl`
      \\ ONCE_REWRITE_TAC [lookup_def] \\ FS [])
    \\ FS [sexp2sexp_def] \\ METIS_TAC [NOT_CAR_EQ_ERROR,EvalTerm_IGNORE_BODY])
  \\ PUSH_STRIP_TAC THEN1
   (FS [atbl_ftbl_inv_def] \\ Q.UNABBREV_TAC `if_new_atbl` \\ FS []
    \\ ONCE_REWRITE_TAC [lookup_def] \\ FS [] \\ STRIP_TAC
    \\ Cases_on `fname' = fname` \\ FS [] THEN1
     (FS [define_safe_def,LET_DEF]
      \\ Cases_on `isTrue (lookup_safe (Sym fname) ftbl)` \\ FS []
      \\ ASM_SIMP_TAC std_ss [lookup_safe_EQ_MEM]
      \\ FS [sexp2list_def,MAP,MEM]
      \\ ONCE_REWRITE_TAC [lookup_safe_def]
      \\ FS [] \\ FS [isTrue_def])
    \\ STRIP_TAC \\ RES_TAC
    \\ FS [define_safe_def,LET_DEF]
    \\ Cases_on `isTrue (lookup_safe (Sym fname) ftbl)` \\ FS []
    \\ FS [sexp2list_def,MAP])
  \\ STRIP_TAC THEN1
   (SIMP_TAC std_ss [runtime_inv_def] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [FDOM_FUPDATE]
    \\ REVERSE (Cases_on `fname = name`) \\ FULL_SIMP_TAC std_ss [] THEN1
     (FULL_SIMP_TAC std_ss [IN_INSERT,FAPPLY_FUPDATE_THM,runtime_inv_def]
      \\ Q.PAT_X_ASSUM `!name params. bbb` (MP_TAC o Q.SPEC `name`)
      \\ ASM_SIMP_TAC std_ss []
      \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`args`,`ok'`])
      \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
      \\ Q.EXISTS_TAC `ok2` \\ STRIP_TAC THEN1
       (MATCH_MP_TAC MR_ap_CTXT
        \\ FULL_SIMP_TAC std_ss []
        \\ RES_TAC \\ SIMP_TAC std_ss [define_safe_def,LET_DEF] \\ SRW_TAC [] []
        \\ METIS_TAC [MR_ev_add_def])
      \\ FULL_SIMP_TAC std_ss [MilawaTrueFun_def]
      \\ METIS_TAC [MilawaTrue_new_definition])
    \\ FULL_SIMP_TAC std_ss [IN_INSERT,FAPPLY_FUPDATE_THM]
    \\ Q.ABBREV_TAC `k2 = FST (SND (define_safe ftbl (Sym name) (list2sexp xs) body k io T))`
    \\ Q.ABBREV_TAC `ftbl2 = (FST (define_safe ftbl (Sym name) (list2sexp xs) body k io T))`
    \\ Q.ABBREV_TAC `ctxt2 = (ctxt |+ (name,params,body',sem))`
    \\ Q.PAT_X_ASSUM `xxx = body'` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [axioms_inv_def]
    \\ `func_definition_exists ctxt2 name params (BODY_FUN b) sem` by
     (FULL_SIMP_TAC std_ss [func_definition_exists_def]
      \\ Q.UNABBREV_TAC `ctxt2` \\ EVAL_TAC)
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss [axioms_aux_def]
    \\ Q.PAT_X_ASSUM `ftbl_inv k2 ftbl2` (fn th => ASSUME_TAC th THEN MP_TAC th)
    \\ SIMP_TAC std_ss [ftbl_inv_def,EVERY_MEM] \\ STRIP_TAC
    \\ RES_TAC \\ FS [LET_DEF,isTrue_def,getSym_def,MAP_getSym_Sym]
    \\ ONCE_REWRITE_TAC [MR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.PAT_X_ASSUM `logic_func_inv name ctxt2 raw_body` MP_TAC
    \\ SS [logic_func_inv_def,LET_DEF] \\ ASM_SIMP_TAC std_ss []
    \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `FunVarBind params args`)
    \\ `name IN FDOM ctxt2 /\
        (ctxt2 ' name = (params,BODY_FUN (term2t (sexp3term raw_body)),sem))` by
     (Q.UNABBREV_TAC `ctxt2`
      \\ FULL_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM,FDOM_FUPDATE,IN_INSERT])
    \\ `sem = EvalFun name ctxt2` by
     (FULL_SIMP_TAC std_ss [context_inv_def] \\ METIS_TAC [])
    \\ ASM_SIMP_TAC std_ss [EvalFun_def]
    \\ STRIP_TAC \\ SIMP_TAC std_ss [Eval_M_ap_def]
    \\ ONCE_REWRITE_TAC [M_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.ABBREV_TAC `result = (EvalTerm (FunVarBind params args,ctxt2)
                                (term2t (sexp3term raw_body)))`
    \\ `!a. M_ev name
            (term2t (sexp3term raw_body),FunVarBind params args,ctxt2) a =
            (result = a)` by METIS_TAC [M_ev_DETERMINISTIC]
    \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
    \\ `axioms_inv ctxt2 ftbl2 if_new_axiom` by
          FULL_SIMP_TAC (srw_ss()) [axioms_inv_def]
    \\ `EVERY (\x. x NOTIN FDOM ctxt2) fake_ftbl_entries` by
           METIS_TAC [fake_ftbl_entries_NOT_IN_CTXT]
    \\ `~("DEFUN" IN FDOM ctxt2) /\ ~("ERROR" IN FDOM ctxt2)` by
           FULL_SIMP_TAC std_ss [fake_ftbl_entries_def,EVERY_DEF]
    \\ IMP_RES_TAC term2t_sexp3term_LEMMA \\ FULL_SIMP_TAC std_ss []
    \\ Q.ABBREV_TAC `bb = sexp2term raw_body`
    \\ `funcs_ok bb` by METIS_TAC [funcs_ok_sexp2term]
    \\ `?ok2.
         MR_ev (term2term bb,VarBind params args,ctxt2,k2,ok') (result,ok2) /\
         (ok2 ==> MilawaTrue ctxt2 (Equal (inst_term (FunVarBind params args) (term2t bb)) (mConst result)))` suffices_by (STRIP_TAC THEN Q.EXISTS_TAC `ok2` \\ STRIP_TAC THEN1
          (DISJ1_TAC \\ REVERSE STRIP_TAC
           THEN1 (MATCH_MP_TAC (GEN_ALL MR_ev_term2term) \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [EvalTerm_IGNORE_BODY])
           \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [term2t_def]
           \\ Q.PAT_X_ASSUM `term2t (sexp3term raw_body) = xx` MP_TAC
           \\ SIMP_TAC std_ss []
           \\ Q.PAT_X_ASSUM `term_ok ctxt2 (mApp (func2f Error) (MAP (\a. term2t a) xs'))` MP_TAC
           \\ ASM_SIMP_TAC std_ss [term_ok_def,func2f_def,func_arity_def])
         \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [MilawaTrueFun_def]
         \\ MATCH_MP_TAC (GEN_ALL MilawaTrue_TRANS)
         \\ Q.EXISTS_TAC `(inst_term (FunVarBind params args) (term2t bb))`
         \\ ASM_SIMP_TAC std_ss []
         \\ `(Equal (mApp (mFun name) (MAP mConst args))
               (inst_term (FunVarBind params args) (term2t bb))) =
             formula_sub (ZIP(params,MAP mConst args))
               (Equal (mApp (mFun name) (MAP mVar params)) (term2t bb))` by
          (FULL_SIMP_TAC (srw_ss()) [formula_sub_def,term_sub_def,MAP_MAP_o,o_DEF]
           \\ ASM_SIMP_TAC std_ss [MAP_LOOKUP_LEMMA,inst_term_def]
           \\ FULL_SIMP_TAC std_ss [context_ok_def]
           \\ RES_TAC \\ IMP_RES_TAC (GSYM term_sub_EQ)
           \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `mConst o FunVarBind params args`)
           \\ FULL_SIMP_TAC std_ss [o_DEF,MAP_FunVarBind_LEMMA])
         \\ ASM_SIMP_TAC std_ss []
         \\ MATCH_MP_TAC (MilawaTrue_rules |> CONJUNCTS |> el 7)
         \\ STRIP_TAC THEN1
          (Q.UNABBREV_TAC `new_axiom`
           \\ FULL_SIMP_TAC std_ss [formula_sub_def,formula_ok_def,
                term_sub_def,term_ok_def,func_arity_def,LENGTH_MAP]
           \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_IMP]
           \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC term_ok_sub
           \\ FULL_SIMP_TAC std_ss [term_ok_def,EVERY_MEM,MEM_MAP,PULL_IMP]
           \\ Cases \\ ASM_SIMP_TAC std_ss [MEM_MAP,pairTheory.EXISTS_PROD,
            ZIP_MAP |> Q.SPECL [`xs`,`ys`] |> Q.ISPEC `I` |> SIMP_RULE std_ss [MAP_ID]]
           \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [term_ok_def])
         \\ FULL_SIMP_TAC std_ss [axioms_inv_def]
         \\ `axioms_aux name ctxt2 if_new_axiom ftbl2 params sem
              (BODY_FUN (term2t bb))` by METIS_TAC [func_definition_exists_def]
         \\ FULL_SIMP_TAC std_ss [axioms_aux_def,def_axiom_def]
         \\ `str2func name = mFun name` by (SRW_TAC [] [str2func_def])
         \\ FULL_SIMP_TAC std_ss [] \\ Q.UNABBREV_TAC `new_axiom`
         \\ FULL_SIMP_TAC std_ss [thms_inv_def,EVERY_MEM] \\ METIS_TAC [])
    \\ SIMP_TAC std_ss [term2term_def]
    \\ `core_assum k2` by
     (Q.UNABBREV_TAC `k2`
      \\ SIMP_TAC std_ss [define_safe_def,LET_DEF] \\ SRW_TAC [] []
      \\ Q.PAT_X_ASSUM `core_assum kk` MP_TAC
      \\ ONCE_REWRITE_TAC [milawa_initTheory.core_assum_def]
      \\ MATCH_MP_TAC (METIS_PROVE [] ``(!x. f a x ==> f b x) ==> (f a x ==> f b x)``)
      \\ SIMP_TAC std_ss [fns_assum_add_def_IMP])
    \\ MATCH_MP_TAC (GEN_ALL MR_ev_thm |> Q.SPECL [`result`,`name`,`k2`,`term2t bb`,`ctxt2`,`FunVarBind params args`,`ok'`,`VarBind params args`])
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ `ctxt2 \\ name = ctxt` by (Q.UNABBREV_TAC `ctxt2` \\ ASM_SIMP_TAC (srw_ss()) [DOMSUB_NOT_IN_DOM])
    \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [term_funs_def,axioms_inv_def] \\ REPEAT STRIP_TAC
      \\ `axioms_aux name' ctxt2 if_new_axiom ftbl2 params' sem'
          (BODY_FUN body'')` by METIS_TAC [func_definition_exists_def]
      \\ FULL_SIMP_TAC std_ss [axioms_aux_def,def_axiom_def]
      \\ `str2func name' = mFun name'` by
       (FULL_SIMP_TAC std_ss [EVERY_DEF,str2func_def] \\ SRW_TAC [] []
        \\ FULL_SIMP_TAC std_ss [])
      \\ FULL_SIMP_TAC std_ss [thms_inv_def,EVERY_MEM] \\ METIS_TAC [])
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [runtime_inv_def] \\ REPEAT STRIP_TAC
      \\ Q.UNABBREV_TAC `k2` \\ SRW_TAC [] [define_safe_def,LET_DEF]
      \\ METIS_TAC [MR_ev_add_def])
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [proof_in_full_ctxt_def] \\ REPEAT STRIP_TAC
      \\ Q.PAT_X_ASSUM `Abbrev (ctxt2 = pat)` (fn th =>
           ASSUME_TAC th THEN ONCE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] th])
      \\ METIS_TAC [MilawaTrue_new_definition])
    \\ NTAC 2 STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF]
    \\ `MEM v params` by FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [params_lemma])
  THEN1 (* core_assums *)
   (SIMP_TAC std_ss [define_safe_def,LET_DEF] \\ SRW_TAC [] []
    \\ Q.PAT_X_ASSUM `core_assum kk` MP_TAC
    \\ ONCE_REWRITE_TAC [milawa_initTheory.core_assum_def]
    \\ MATCH_MP_TAC (METIS_PROVE [] ``(!x. f a x ==> f b x) ==> (f a x ==> f b x)``)
    \\ SIMP_TAC std_ss [fns_assum_add_def_IMP]));


(* admit witness *)

val core_admit_witness_cmd = prove(
  ``list_exists 5 cmd ==>
    ?x name bound_var free_vars raw_body.
        cmd = list2sexp [x;name;bound_var;free_vars;raw_body]``,
  REPEAT STRIP_TAC \\ EVAL_TAC \\ Cases_on `cmd` \\ FS []
  \\ REPEAT ((Cases_on `S0` \\ FS []) ORELSE (Cases_on `S0'` \\ FS [])) \\ FS []);

val core_admit_witness_lemma = core_admit_witness_def
  |> SIMP_RULE std_ss [DISJ_EQ_IMP,GSYM if_memberp_def,GSYM if_lookup_def,LET_DEF]

val core_admit_witness_side_lemma = core_admit_witness_side_def
  |> SIMP_RULE std_ss [DISJ_EQ_IMP,GSYM AND_IMP_INTRO,LET_DEF,define_safe_side_def,LET_DEF]

val ALL_DISTINCT_MAP_Sym = prove(
  ``!xs. ALL_DISTINCT (MAP Sym xs) = ALL_DISTINCT xs``,
  Induct \\ FS [MAP,ALL_DISTINCT]);

val ALL_DISTINCT_LEMMA = prove(
  ``isTrue (logic_variable_listp (list2sexp xs)) /\ ALL_DISTINCT (Sym var::xs) ==>
    ALL_DISTINCT (var::MAP getSym xs)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC logic_variable_listp_IMP
  \\ FULL_SIMP_TAC std_ss [MAP_getSym_Sym]
  \\ FULL_SIMP_TAC std_ss [GSYM MAP,ALL_DISTINCT_MAP_Sym]);

val term_ok_IMP_FUPDATE = prove(
  ``!ctxt body.
      ~(n IN FDOM ctxt) /\ term_ok ctxt body ==> term_ok (ctxt |+ (n,x)) body``,
  HO_MATCH_MP_TAC term_ok_ind \\ SIMP_TAC std_ss [term_ok_def,EVERY_MEM]
  \\ REPEAT STRIP_TAC \\ Cases_on `fc`
  \\ FULL_SIMP_TAC std_ss [func_arity_def,FDOM_FUPDATE,IN_INSERT,
       FAPPLY_FUPDATE_THM] \\ METIS_TAC []);

val logic_variable_listp_NOT_NIL = prove(
  ``!xs. isTrue (logic_variable_listp (list2sexp xs)) ==>
         EVERY (\x. ~(getSym x = "NIL") /\ ~(getSym x = "T")) xs /\
         EVERY (\x. var_ok (getSym x)) xs``,
  Induct \\ SIMP_TAC std_ss [EVERY_DEF]
  \\ SIMP_TAC std_ss [Once logic_variable_listp_def] \\ FS [] \\ SRW_TAC [] []
  \\ FS [logic_variablep_def] \\ Cases_on `h` \\ FS [getSym_def,var_ok_def]
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC \\ FS [CONS_11]);

val witness_ctxt_def = Define `
  witness_ctxt ctxt cmd =
    let name = getSym (CAR (CDR cmd)) in
    let var = getSym (CAR (CDR (CDR cmd))) in
    let formals = MAP getSym (sexp2list (CAR (CDR (CDR (CDR cmd))))) in
    let prop = sexp2t (sexp2sexp (CAR (CDR (CDR (CDR (CDR cmd)))))) in
    let body = WITNESS_FUN prop var in
    let interp = @interp. context_ok (ctxt |+ (name,formals,body,interp)) in
      if name IN FDOM ctxt UNION {"NOT";"RANK";"ORDP";"ORD<"} then ctxt
      else ctxt |+ (name,formals,body,interp)`;

val core_admit_witness_thm = prove(
  ``milawa_inv ctxt simple_ctxt k (axioms,thms,atbl,checker,ftbl) ==>
    ?x k2 io2 ok2 result.
      core_admit_witness_side cmd (milawa_state (axioms,thms,atbl,checker,ftbl)) k io ok /\
      (core_admit_witness cmd (milawa_state (axioms,thms,atbl,checker,ftbl)) k io ok =
         (x,k2,io2,ok2)) /\
      (ok2 ==> (io2 = io) /\
               ?result ctxt. (x = milawa_state result) /\ milawa_inv ctxt (witness_ctxt simple_ctxt cmd) k2 result)``,
  FS [core_admit_witness_side_lemma,core_admit_witness_lemma,
      LET_DEF,milawa_state_def,core_state_def]
  \\ SRW_TAC [] [] \\ FS [] \\ FS [milawa_inv_def]
  THEN1 (SRW_TAC [] [define_safe_def] \\ FS [define_safe_def]
         \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [LET_DEF]
         \\ Q.UNABBREV_TAC `prev_def` \\ Q.UNABBREV_TAC `this_def`
         \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ IMP_RES_TAC core_admit_witness_cmd
  \\ IMP_RES_TAC SND_SND_SND_define_safe_IMP \\ FS []
  \\ `isTrue (logic_translate raw_body)` by
    (SIMP_TAC std_ss [isTrue_def] \\ REPEAT STRIP_TAC
     \\ FS [EVAL ``logic_termp (Sym "NIL")``])
  \\ FS [logic_translate_thm]
  \\ `?body. term_syntax_ok body /\ (sexp2sexp raw_body = t2sexp body)` by METIS_TAC [logic_termp_thm]
  \\ Q.PAT_X_ASSUM `free_vars' = list2sexp xs` ASSUME_TAC \\ FS []
  \\ FULL_SIMP_TAC std_ss [GSYM list2sexp_def,uniquep_thm] \\ FS []
  \\ `?fname. name = Sym fname` by
    (Cases_on `isSym name` \\ FS [logic_function_namep_def] \\ FS [isSym_thm])
  \\ FS [] \\ POP_ASSUM (K ALL_TAC) \\ Q.PAT_X_ASSUM `cmd = bbb` (K ALL_TAC)
  \\ `?var. bound_var = Sym var` by
    (Cases_on `isSym bound_var` \\ FS [logic_variablep_def] \\ FS [isSym_thm])
  \\ `set (Sym var::xs) = set (MAP Sym (var::MAP getSym xs))` by
     (IMP_RES_TAC logic_variable_listp_thm \\ FS [MAP])
  \\ FULL_SIMP_TAC std_ss [set_MAP_SUBSET] \\ POP_ASSUM (K ALL_TAC) \\ FS []
  \\ IMP_RES_TAC logic_term_atblp_thm
  \\ `~(fname = "ERROR")` by METIS_TAC [NAME_NOT_ERROR]
  \\ Q.ABBREV_TAC `new_axiom = def_axiom fname
       (MAP getSym xs,WITNESS_FUN body var,ARB)`
  \\ Q.ABBREV_TAC `if_new_axiom = if MEM new_axiom axioms then axioms else new_axiom :: axioms`
  \\ Q.ABBREV_TAC `if_new_atbl = if_lookup (Sym fname) atbl (Dot (Dot (Sym fname) (Val (LENGTH xs))) atbl)`
  \\ Cases_on `isTrue (lookup (Sym fname) atbl)` THEN1
   (Q.EXISTS_TAC `(axioms,thms,atbl,checker,ftbl)` \\ Q.EXISTS_TAC `ctxt`
    \\ FS [milawa_inv_def,milawa_state_def,core_state_def]
    \\ Q.UNABBREV_TAC `if_new_atbl` \\ FS [if_lookup_def]
    \\ FULL_SIMP_TAC std_ss [if_memberp_def]
    \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC]
    \\ Q.PAT_X_ASSUM `axioms_inv ctxt ftbl axioms` ASSUME_TAC
    \\ FS [atbl_ftbl_inv_def] \\ RES_TAC
    \\ FS [define_safe_ID]
    \\ `?fparams fbody fsem.
          func_definition_exists ctxt fname fparams fbody fsem` suffices_by (STRIP_TAC THEN REVERSE STRIP_TAC THEN1
       (SUFF_TAC ``fname IN FDOM (ctxt:context_type) UNION {"NOT";"RANK";"ORDP";"ORD<"}``
        THEN1 (FS [witness_ctxt_def,similar_context_def,LET_DEF,getSym_def])
        \\ FS [axioms_inv_def,EVERY_DEF,func_definition_exists_def,IN_UNION,IN_INSERT])
      \\ MATCH_MP_TAC (METIS_PROVE [] ``x ==> ((if x then y else z) = y)``)
      \\ FS [axioms_inv_def] \\ Cases_on `fbody`
      \\ RES_TAC \\ FS [axioms_aux_def] THEN1
       (IMP_RES_TAC MEM_ftbl
        \\ IMP_RES_TAC MEM_MEM_ftbl
        \\ FS [] \\ FS [sexp2sexp_def,witness_body_def])
      \\ Q.PAT_X_ASSUM `MEM xx axioms` MP_TAC
      \\ ASM_SIMP_TAC std_ss [def_axiom_def]
      \\ SIMP_TAC std_ss [MEM_MAP]
      \\ HO_MATCH_MP_TAC (METIS_PROVE [] ``P x ==> (MEM x xs ==> ?y. P y /\ MEM y xs)``)
      \\ FS [f2sexp_def,t2sexp_def]
      \\ IMP_RES_TAC MEM_ftbl
      \\ IMP_RES_TAC MEM_MEM_ftbl
      \\ FS [] \\ FS [sexp2sexp_def,witness_body_def,list2sexp_def,MAP,t2sexp_def]
      \\ Cases_on `MEM fname ["NOT";"RANK";"ORDP";"ORD<"]` THEN1 (FS [] \\ EVAL_TAC)
      \\ FS [fake_ftbl_entries_def] \\ FULL_SIMP_TAC std_ss
        [logic_function_namep_def,GSYM list2sexp_def,memberp_thm,MEM] \\ FS []
      \\ FS [func_syntax_ok_def,logic_func2sexp_def,str2func_def,logic_prim2sym_def]
      \\ IMP_RES_TAC fake_ftbl_entries \\ FS [fake_ftbl_entries_def])
    \\ Cases_on `MEM fname ["NOT";"RANK";"ORDP";"ORD<"]` THEN1
     (ASM_SIMP_TAC std_ss [func_definition_exists_def]
      \\ METIS_TAC [lookup_safe_init_ftbl_EXISTS,MEM])
    \\ `(logic_func2sexp (mFun fname) = Sym fname) /\
        func_syntax_ok (mFun fname)` by
     (FS [fake_ftbl_entries_def] \\ FULL_SIMP_TAC std_ss
        [logic_function_namep_def,GSYM list2sexp_def,memberp_thm,MEM] \\ FS []
      \\ FS [func_syntax_ok_def,logic_func2sexp_def,str2func_def]
      \\ IMP_RES_TAC fake_ftbl_entries \\ FS [fake_ftbl_entries_def])
    \\ `fname IN FDOM ctxt` by
     (CCONTR_TAC \\ Q.PAT_X_ASSUM `atbl_ok ctxt atbl` ASSUME_TAC
      \\ FULL_SIMP_TAC std_ss [atbl_ok_def]
      \\ POP_ASSUM (MP_TAC o Q.SPEC `mFun fname`)
      \\ FS [func_arity_def,CDR_lookup_NOT_NIL])
    \\ `?fparams fbody fsem. ctxt ' fname = (fparams,fbody,fsem)` by METIS_TAC [PAIR]
    \\ METIS_TAC [func_definition_exists_def])
  \\ `~MEM fname ["NOT";"RANK";"ORDP";"ORD<"]` by
   (STRIP_TAC \\ Q.PAT_X_ASSUM `atbl_ok ctxt atbl` ASSUME_TAC
    \\ FS [atbl_ok_def] THENL [
      POP_ASSUM (MP_TAC o Q.SPEC `mPrimitiveFun logic_NOT`)
      \\ FS [func_syntax_ok_def,isTrue_def,logic_func2sexp_def,
             logic_prim2sym_def,func_arity_def],
      POP_ASSUM (MP_TAC o Q.SPEC `mPrimitiveFun logic_RANK`)
      \\ FS [func_syntax_ok_def,isTrue_def,logic_func2sexp_def,
             logic_prim2sym_def,func_arity_def],
      POP_ASSUM (MP_TAC o Q.SPEC `mPrimitiveFun logic_ORDP`)
      \\ FS [func_syntax_ok_def,isTrue_def,logic_func2sexp_def,
             logic_prim2sym_def,func_arity_def],
      POP_ASSUM (MP_TAC o Q.SPEC `mPrimitiveFun logic_ORD_LESS`)
      \\ FS [func_syntax_ok_def,isTrue_def,logic_func2sexp_def,
             logic_prim2sym_def,func_arity_def]])
  \\ FS [if_lookup_def]
  \\ Q.ABBREV_TAC `r =
       (Dot (Sym "ERROR") (Dot (Dot (Sym "QUOTE") (Dot (Dot (Sym fname)
       (Dot (Sym var) (Dot (list2sexp xs) (Dot raw_body (Sym "NIL")))))
       (Sym "NIL"))) (Sym "NIL")))`
  \\ Q.EXISTS_TAC `(if_new_axiom,thms,if_new_atbl,checker,
       FST (define_safe ftbl (Sym fname) (list2sexp xs) r k io T))`
  \\ Q.ABBREV_TAC `ef = \args.
       @v. isTrue (EvalTerm (FunVarBind (var::MAP getSym xs) (v::args),ctxt) body)`
  \\ Q.EXISTS_TAC `ctxt |+ (fname,MAP getSym xs,WITNESS_FUN body var,ef)`
  \\ IMP_RES_TAC fake_ftbl_entries
  \\ STRIP_TAC THEN1
   (UNABBREV_ALL_TAC \\ FS [milawa_state_def,core_state_def] \\ FS [if_memberp_def]
    \\ FS [MEM,fake_ftbl_entries_def]
    \\ (EVAL ``f2sexp (def_axiom fname (MAP getSym xs,WITNESS_FUN body var,ARB))``
        |> GSYM |> MP_TAC) \\ FS [logic_func2sexp_def]
    \\ `~(fname = "NIL") /\ ~(fname = "QUOTE")` by
     (REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [logic_function_namep_def,GSYM list2sexp_def,
           memberp_thm,MEM] \\ FS []) \\ FS [] \\ STRIP_TAC \\ POP_ASSUM (K ALL_TAC)
    \\ SRW_TAC [] [] \\ FS [])
  \\ FULL_SIMP_TAC std_ss [milawa_inv_def]
  \\ `~(fname IN FDOM ctxt)` by
   (REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `atbl_ok ctxt atbl` MP_TAC
    \\ FS [atbl_ok_def] \\ Q.EXISTS_TAC `mFun fname`
    \\ FS [fake_ftbl_entries_def] \\ FULL_SIMP_TAC std_ss
         [logic_function_namep_def,GSYM list2sexp_def,memberp_thm,MEM] \\ FS []
    \\ STRIP_TAC THEN1 (EVAL_TAC \\ FS [])
    \\ ASM_SIMP_TAC std_ss [logic_func2sexp_def,MEM] \\ FS [isTrue_def]
    \\ FS [func_arity_def])
  \\ `atbl_ok (ctxt |+ (fname,MAP getSym xs,WITNESS_FUN body var,ef)) if_new_atbl` by
   (FS [atbl_ok_def] \\ REPEAT STRIP_TAC \\ RES_TAC \\ Q.UNABBREV_TAC `if_new_atbl`
    \\ Cases_on `f` \\ FULL_SIMP_TAC std_ss [func_arity_def]
    \\ `!l. ~(logic_func2sexp (mPrimitiveFun l) = Sym fname)` by
       (FS [fake_ftbl_entries_def] \\ FULL_SIMP_TAC std_ss
         [logic_function_namep_def,GSYM list2sexp_def,memberp_thm,MEM] \\ FS []
        \\ Cases \\ EVAL_TAC \\ FS []) \\ FS []
    \\ ONCE_REWRITE_TAC [lookup_def] \\ FS []
    \\ `(logic_func2sexp (mFun s) = Sym fname) = (s = fname)` by
     (FULL_SIMP_TAC std_ss [logic_func2sexp_def] \\ SRW_TAC [] []
      \\ FS [fake_ftbl_entries_def] \\ FULL_SIMP_TAC std_ss
          [logic_function_namep_def,GSYM list2sexp_def,memberp_thm,MEM] \\ FS [])
    \\ FS [FDOM_FUPDATE,IN_INSERT,FAPPLY_FUPDATE_THM]
    \\ Cases_on `s = fname` \\ FS [LENGTH_MAP])
  \\ `definition_ok (fname,MAP getSym xs,WITNESS_FUN body var,ctxt)` by
       (FS [definition_ok_def] \\ FS [ALL_DISTINCT_LEMMA]) \\ FS []
  \\ `thms_inv (ctxt |+ (fname,MAP getSym xs,WITNESS_FUN body var,ef)) thms` by
   (FS [thms_inv_def,EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ IMP_RES_TAC MilawaTrue_new_definition \\ METIS_TAC [])
  \\ `thms_inv (ctxt |+ (fname,MAP getSym xs,WITNESS_FUN body var,ef)) axioms` by
   (FS [thms_inv_def,EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ IMP_RES_TAC MilawaTrue_new_definition \\ METIS_TAC []) \\ FS []
  \\ PUSH_STRIP_TAC THEN1
   (Q.UNABBREV_TAC `ef` \\ MATCH_MP_TAC definition_ok_WITNESS_FUN
    \\ ASM_SIMP_TAC std_ss [])
  \\ PUSH_STRIP_TAC THEN1
   (FS [context_inv_def] \\ STRIP_TAC \\ STRIP_TAC \\ Cases_on `fname = fname'`
    \\ FULL_SIMP_TAC (srw_ss()) [FAPPLY_FUPDATE_THM] \\ REPEAT STRIP_TAC
    THEN1 (`term_ok ctxt body'` by (FS [context_ok_def] \\ RES_TAC \\ NO_TAC)
           \\ METIS_TAC [EvalFun_FUPDATE])
    THEN1 (Q.UNABBREV_TAC `ef` \\ FS [GSYM EvalTerm_FUPDATE])
    \\ REPEAT STRIP_TAC \\ FS [context_inv_def] \\ RES_TAC \\ FS []
    \\ `term_ok ctxt body'` by (FS [context_ok_def] \\ RES_TAC \\ NO_TAC)
    \\ FS [GSYM EvalTerm_FUPDATE])
  \\ PUSH_STRIP_TAC THEN1
   (IMP_RES_TAC similar_context_definition_ok
    \\ FS [similar_context_def,witness_ctxt_def,getSym_def,LET_DEF]
    \\ `~(fname IN FDOM ctxt UNION {"NOT"; "RANK"; "ORDP"; "ORD<"})` by FS [IN_INSERT,IN_UNION,NOT_IN_EMPTY] \\ FS [FDOM_FUPDATE]
    \\ FS [sexp2t_t2sexp_thm] \\ STRIP_TAC THEN1 (METIS_TAC [definition_ok_thm])
    \\ FS [FEVERY_DEF,FDOM_FUPDATE,IN_INSERT,FAPPLY_FUPDATE_THM] \\ STRIP_TAC
    \\ Cases_on `x' = fname` \\ FS []
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `FDOM simple_ctxt = FDOM ctxt` ASSUME_TAC \\ FS []
    \\ RES_TAC \\ POP_ASSUM MP_TAC
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ REPEAT STRIP_TAC
    \\ FS [])
  \\ PUSH_STRIP_TAC THEN1
   (Q.UNABBREV_TAC `if_new_atbl` \\ FS [atbl_inv_def,EVERY_DEF,sexp2list_def])
  \\ `func2f (Fun fname) = mFun fname` by
       (FS [fake_ftbl_entries_def] \\ FULL_SIMP_TAC std_ss
          [logic_function_namep_def,GSYM list2sexp_def,memberp_thm,MEM,func2f_def])
  \\ `str2func fname = mFun fname` by
       (FS [fake_ftbl_entries_def,str2func_def] \\ FULL_SIMP_TAC std_ss
          [logic_function_namep_def,GSYM list2sexp_def,memberp_thm,MEM,func2f_def])
  \\ PUSH_STRIP_TAC THEN1
   (Q.UNABBREV_TAC `if_new_axiom`
    \\ `thms_inv (ctxt |+ (fname,MAP getSym xs,WITNESS_FUN body var,ef)) (new_axiom::axioms)` suffices_by
    (STRIP_TAC THEN FS [thms_inv_def,EVERY_DEF] \\ SRW_TAC [] [EVERY_DEF])
    \\ FS [thms_inv_def,EVERY_DEF] \\ REPEAT STRIP_TAC \\ Q.UNABBREV_TAC `new_axiom`
    \\ FULL_SIMP_TAC std_ss [def_axiom_def] THEN1
     (((CONJUNCTS MilawaTrue_rules)
            |> filter (can (find_term (aconv ``WITNESS_FUN``) o concl))
            |> hd |> MATCH_MP_TAC)
      \\ Q.EXISTS_TAC `ef` \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT_LEMMA]
      \\ FS [FDOM_FUPDATE,IN_INSERT,FAPPLY_FUPDATE_THM]
      \\ MATCH_MP_TAC term_ok_IMP_FUPDATE \\ FS [])
    \\ FULL_SIMP_TAC std_ss [formula_syntax_ok_def,term_syntax_ok_def,LENGTH,
         LENGTH_MAP,ALL_DISTINCT_LEMMA,EVERY_DEF,func_syntax_ok_def,MEM]
    \\ FS [fake_ftbl_entries_def,str2func_def] \\ FULL_SIMP_TAC std_ss
          [logic_function_namep_def,GSYM list2sexp_def,memberp_thm,MEM,func2f_def]
    \\ FS [] \\ SIMP_TAC std_ss [EVERY_MEM,MEM_MAP] \\ REPEAT STRIP_TAC
    \\ FS [term_syntax_ok_def]
    \\ IMP_RES_TAC logic_variable_listp_NOT_NIL
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM,logic_variablep_EQ_var_ok])
  \\ PUSH_STRIP_TAC THEN1
   (Cases_on `(FST (SND (define_safe ftbl (Sym fname) (list2sexp xs) r k io T))) = k`
    \\ FULL_SIMP_TAC std_ss []
    \\ `?new_def. (FST (SND (define_safe ftbl (Sym fname) (list2sexp xs) r k io T))) =
                  add_def k new_def` by
      (FULL_SIMP_TAC std_ss [define_safe_def,LET_DEF] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `core_check_proof_inv checker k` MP_TAC
    \\ METIS_TAC [core_check_proof_inv_step])
  \\ PUSH_STRIP_TAC THEN1
   (FS [define_safe_def,LET_DEF]
    \\ Cases_on `isTrue (lookup_safe (Sym fname) ftbl)` \\ FS []
    \\ FS [ftbl_inv_def,getSym_def]
    \\ REVERSE STRIP_TAC THEN1
     (FS [sexp2list_def,EVERY_DEF]
      \\ ONCE_REWRITE_TAC [lookup_safe_def] \\ FS [EVERY_MEM]
      \\ REPEAT STRIP_TAC \\ SRW_TAC [] [] \\ FS [lookup_safe_EQ_MEM]
      \\ Q.EXISTS_TAC `SUC old` \\ FS [FUNPOW])
    \\ SIMP_TAC std_ss [sexp2list_def,EVERY_DEF]
    \\ STRIP_TAC THEN1
     (FS [LET_DEF,getSym_def,add_def_def,FDOM_FUNION,
        IN_UNION,FDOM_FEMPTY,FDOM_FUPDATE,
        IN_INSERT,FUNION_DEF,FAPPLY_FUPDATE_THM])
    \\ FS [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC THEN1
     (FS [LET_DEF,getSym_def,add_def_def,FDOM_FUNION,
        IN_UNION,FDOM_FEMPTY,FDOM_FUPDATE,
        IN_INSERT,FUNION_DEF,FAPPLY_FUPDATE_THM]))
  \\ PUSH_STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [axioms_inv_def] \\ STRIP_TAC
    THEN1 (FULL_SIMP_TAC (srw_ss()) [])
    \\ FS [axioms_inv_def,FDOM_FUPDATE,FAPPLY_FUPDATE_THM] \\ STRIP_TAC
    \\ REVERSE (Cases_on `name = fname`) \\ FS [IN_INSERT]
    \\ FS [func_definition_exists_NEQ] THEN1
     (REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `!name params body sem. bbb` IMP_RES_TAC
      \\ REVERSE (Cases_on `body'`) \\ FULL_SIMP_TAC std_ss [axioms_aux_def] THEN1
       (Q.EXISTS_TAC `raw_body'` \\ POP_ASSUM MP_TAC \\ FS [] \\ STRIP_TAC
        \\ STRIP_TAC THEN1
          (FS [define_safe_def,LET_DEF]
           \\ Cases_on `isTrue (lookup_safe (Sym fname) ftbl)`
           \\ FS [sexp2list_def,MEM])
        \\ Q.UNABBREV_TAC `if_new_axiom` \\ METIS_TAC [MEM])
      \\ Q.EXISTS_TAC `raw_body'` \\ POP_ASSUM MP_TAC \\ FS [] \\ STRIP_TAC
      \\ STRIP_TAC THEN1
        (FS [define_safe_def,LET_DEF]
         \\ Cases_on `isTrue (lookup_safe (Sym fname) ftbl)`
         \\ FS [sexp2list_def,MEM])
      \\ STRIP_TAC THEN1 (Q.UNABBREV_TAC `if_new_axiom` \\ METIS_TAC [MEM])
      \\ Cases_on `MEM name ["NOT"; "RANK"; "ORD<"; "ORDP"]`
      THEN1 (FS [logic_func_inv_def])
      \\ `name IN FDOM ctxt` by METIS_TAC [func_definition_exists_def]
      \\ MATCH_MP_TAC logic_func_inv_NEQ \\ FS [sexp2sexp_def]
      \\ FS [func_definition_exists_def]
      \\ METIS_TAC [context_ok_def])
    \\ FS [func_definition_exists_EQ,MEM,axioms_aux_def]
    \\ Q.EXISTS_TAC `raw_body` \\ FS [] \\ REPEAT STRIP_TAC THEN1
     (FS [define_safe_def,LET_DEF]
      \\ Cases_on `isTrue (lookup_safe (Sym fname) ftbl)` \\ FS [sexp2list_def,MEM]
      \\ FULL_SIMP_TAC std_ss [witness_body_def,list2sexp_def] \\ Q.UNABBREV_TAC `r`
      \\ IMP_RES_TAC logic_variable_listp_thm \\ ASM_SIMP_TAC std_ss []
      \\ Q.PAT_X_ASSUM `lookup_safe (Sym fname) ftbl = bb` (ASSUME_TAC o GSYM)
      \\ FS [ftbl_inv_def] \\ FULL_SIMP_TAC std_ss [isTrue_lookup_safe])
    THEN1 (FS [sexp2sexp_def]) THEN1
     (FS [sexp2sexp_def]
      \\ Q.UNABBREV_TAC `if_new_axiom` \\ Q.UNABBREV_TAC `new_axiom`
      \\ `(func2f (Fun fname) = mFun fname) /\ (str2func fname = mFun fname)` by
       (FS [str2func_def,fake_ftbl_entries_def] \\ FULL_SIMP_TAC std_ss
         [logic_function_namep_def,GSYM list2sexp_def,memberp_thm,MEM,func2f_def])
      \\ FULL_SIMP_TAC std_ss [def_axiom_def]
      \\ SRW_TAC [] []))
  \\ PUSH_STRIP_TAC THEN1
   (FS [atbl_ftbl_inv_def] \\ Q.UNABBREV_TAC `if_new_atbl` \\ FS []
    \\ ONCE_REWRITE_TAC [lookup_def] \\ FS [] \\ STRIP_TAC
    \\ Cases_on `fname' = fname` \\ FS [] THEN1
     (FS [define_safe_def,LET_DEF]
      \\ Cases_on `isTrue (lookup_safe (Sym fname) ftbl)` \\ FS []
      \\ ASM_SIMP_TAC std_ss [lookup_safe_EQ_MEM]
      \\ FS [sexp2list_def,MAP,MEM]
      \\ ONCE_REWRITE_TAC [lookup_safe_def]
      \\ FS [] \\ FS [isTrue_def])
    \\ STRIP_TAC \\ RES_TAC
    \\ FS [define_safe_def,LET_DEF]
    \\ Cases_on `isTrue (lookup_safe (Sym fname) ftbl)` \\ FS []
    \\ FS [sexp2list_def,MAP])
  \\ STRIP_TAC THEN1 (* runtime_inv *)
   (SIMP_TAC std_ss [runtime_inv_def] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [FDOM_FUPDATE]
    \\ REVERSE (Cases_on `fname = name`) \\ FULL_SIMP_TAC std_ss [] THEN1
     (FULL_SIMP_TAC std_ss [IN_INSERT,FAPPLY_FUPDATE_THM,runtime_inv_def]
      \\ `?ok2. MR_ap (Fun name,args,ARB,ctxt,k,ok') (sem args,ok2) /\
                (ok2 ==> MilawaTrueFun ctxt name args (sem args))` by METIS_TAC []
      \\ Q.EXISTS_TAC `ok2` \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC THEN1
       (MATCH_MP_TAC MR_ap_CTXT
        \\ FULL_SIMP_TAC std_ss []
        \\ RES_TAC \\ SIMP_TAC std_ss [define_safe_def,LET_DEF] \\ SRW_TAC [] []
        \\ METIS_TAC [MR_ev_add_def])
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [MilawaTrueFun_def]
      \\ METIS_TAC [MilawaTrue_new_definition])
    \\ FULL_SIMP_TAC std_ss [IN_INSERT,FAPPLY_FUPDATE_THM]
    \\ Q.ABBREV_TAC `k2 = FST (SND (define_safe ftbl (Sym name) (list2sexp xs) r k io T))`
    \\ Q.ABBREV_TAC `ftbl2 = (FST (define_safe ftbl (Sym name) (list2sexp xs) r k io T))`
    \\ Q.ABBREV_TAC `ctxt2 = (ctxt |+ (name,params,body',sem))`
    \\ Q.EXISTS_TAC `F` \\ SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [axioms_inv_def]
    \\ Q.PAT_X_ASSUM `xxx = body'` (ASSUME_TAC o GSYM)
    \\ `func_definition_exists ctxt2 name params (WITNESS_FUN body var) sem` by
     (FULL_SIMP_TAC std_ss [func_definition_exists_def]
      \\ Q.UNABBREV_TAC `ctxt2` \\ EVAL_TAC)
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss [axioms_aux_def]
    \\ FULL_SIMP_TAC std_ss [ftbl_inv_def,EVERY_MEM]
    \\ RES_TAC \\ FS [LET_DEF,isTrue_def,getSym_def,MAP_getSym_Sym]
    \\ ONCE_REWRITE_TAC [MR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SIMP_TAC std_ss [EVAL ``sexp2term (witness_body name var params raw_body')``]
    \\ SIMP_TAC (srw_ss()) []
    \\ Q.UNABBREV_TAC `ctxt2` \\ SIMP_TAC (srw_ss()) [])
  THEN1 (* core_assums *)
   (SIMP_TAC std_ss [define_safe_def,LET_DEF] \\ SRW_TAC [] []
    \\ Q.PAT_X_ASSUM `core_assum kk` MP_TAC
    \\ ONCE_REWRITE_TAC [milawa_initTheory.core_assum_def]
    \\ MATCH_MP_TAC (METIS_PROVE [] ``(!x. f a x ==> f b x) ==> (f a x ==> f b x)``)
    \\ SIMP_TAC std_ss [fns_assum_add_def_IMP]));


(* admit switch *)

val lookup_lemma1 = SR [] milawa_defsTheory.lookup_def
val lookup_lemma2 = lookup_lemma1 |> Q.INST [`x`|->`Sym t`] |> SR [isDot_def]
val lookup_lemma2a = lookup_lemma1 |> Q.INST [`x`|->`Val t`] |> SR [isDot_def]
val lookup_lemma3 = lookup_lemma1
   |> Q.INST [`x`|->`Dot (Dot (Sym s) y) z`,`a`|->`Sym t`]
   |> SR [isDot_def,CAR_def,CDR_def,SExp_11]

val lookup_provablep =
  ``lookup (Sym "LOGIC.PROVABLEP") init_ftbl``
  |> (ONCE_REWRITE_CONV [milawa_initTheory.init_ftbl_def] THENC
      REWRITE_CONV [lookup_lemma2,lookup_lemma3,CONS_11,NOT_CONS_NIL,NOT_NIL_CONS] THENC
      SIMP_CONV (srw_ss()) []);

val lookup_provablep_body = lookup_provablep |> concl |> dest_comb |> snd
  |> dest_comb |> snd |> dest_comb |> snd |> dest_comb |> fst |> dest_comb |> snd

val lookup_provablep_body_def = Define `
  lookup_provablep_body = ^lookup_provablep_body`;

val lookup_provablep_thm =
  REWRITE_RULE [GSYM lookup_provablep_body_def] lookup_provablep

val lookup_provable_witness =
  ``lookup (Sym "LOGIC.PROVABLE-WITNESS") init_ftbl``
  |> (ONCE_REWRITE_CONV [milawa_initTheory.init_ftbl_def] THENC
      REWRITE_CONV [lookup_lemma2,lookup_lemma3,CONS_11,NOT_CONS_NIL,NOT_NIL_CONS] THENC
      SIMP_CONV (srw_ss()) []);

val lookup_provable_witness_body = lookup_provable_witness |> concl
  |> dest_comb |> snd |> dest_comb |> snd |> dest_comb |> snd
  |> dest_comb |> fst |> dest_comb |> snd |> dest_comb |> snd
  |> dest_comb |> fst |> dest_comb |> snd
  |> dest_comb |> snd |> dest_comb |> fst |> dest_comb |> snd

val lookup_provable_witness_body_def = Define `
  lookup_provable_witness_body = ^lookup_provable_witness_body`;

val lookup_provable_witness_thm =
  REWRITE_RULE [GSYM lookup_provable_witness_body_def] lookup_provable_witness

val lookup_init_ftbl_lemma = prove(
  ``!ftbl.
      (lookup name ftbl = Dot name (Dot params (Dot body (Sym "NIL")))) ==>
      MEM (list2sexp [name; params; body]) (sexp2list ftbl)``,
  REVERSE Induct \\ FS [lookup_lemma2,lookup_lemma2a]
  \\ ONCE_REWRITE_TAC [lookup_def] \\ FS []
  \\ REVERSE (Cases_on `name = CAR ftbl`) \\ FS []
  THEN1 (REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss [sexp2list_def,MEM])
  \\ Cases_on `ftbl` \\ FS [sexp2list_def,MEM]);

val FUNPOW_CDR = prove(
  ``!n. FUNPOW CDR n (Sym "NIL") = Sym "NIL"``,
  Induct \\ FS [FUNPOW]);

val MEM_init_ftbl_IMP = prove(
  ``MEM x (sexp2list init_ftbl) /\ ftbl_inv k ftbl ==>
    MEM x (sexp2list ftbl)``,
  REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `MEM x (sexp2list init_ftbl)` MP_TAC
  \\ FULL_SIMP_TAC std_ss [ftbl_inv_def] \\ POP_ASSUM MP_TAC
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Q.SPEC_TAC (`ftbl`,`ftbl`)
  \\ Q.SPEC_TAC (`old`,`n`)
  \\ Induct \\ SIMP_TAC (srw_ss()) [FUNPOW]
  \\ Cases \\ FS [sexp2list_def,MEM,FUNPOW_CDR]
  \\ ONCE_REWRITE_TAC [milawa_initTheory.init_ftbl_def]
  \\ REWRITE_TAC [GSYM SExp_distinct]);

val MEM_EQ_APPEND = prove(
  ``!xs x. MEM x xs ==> ?ys zs. xs = ys ++ x :: zs``,
  Induct \\ SIMP_TAC std_ss [MEM] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [APPEND_NIL,APPEND]);

val MEM_ftbl_11 = prove(
  ``MEM (list2sexp [x1;x2;x3]) (sexp2list ftbl) /\ ftbl_inv k ftbl /\
    MEM (list2sexp [x1;y2;y3]) (sexp2list ftbl) ==>
    (x2=y2) /\ (x3=y3)``,
  SIMP_TAC std_ss [ftbl_inv_def] \\ STRIP_TAC
  \\ `?ys zs. sexp2list ftbl = ys ++ (list2sexp [x1; y2; y3]) :: zs` by
       METIS_TAC [MEM_EQ_APPEND]
  \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT_APPEND,MAP,CAR_def,MAP_APPEND,
       list2sexp_def,ALL_DISTINCT,MEM,MEM_APPEND,MEM_MAP,PULL_EXISTS_IMP]
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [CAR_def] \\ FS [] \\ METIS_TAC [CAR_def]);

val lookup_init_lemma = prove(
  ``(lookup name init_ftbl = Dot name (Dot params (Dot body (Sym "NIL")))) ==>
    MEM (list2sexp [name; params2; body2]) (sexp2list ftbl) /\ ftbl_inv k ftbl ==>
    (params2 = params) /\ (body2 = body)``,
  REPEAT STRIP_TAC
  \\ IMP_RES_TAC lookup_init_ftbl_lemma
  \\ IMP_RES_TAC MEM_init_ftbl_IMP
  \\ IMP_RES_TAC MEM_ftbl_11);

val core_admit_switch_lemma = prove(
  ``(@y. ~b /\ (x = y) \/ b /\ (~c /\ (x = y) \/ c /\ (y = d))) =
    if ~b then x else if ~c then x else d``,
  Cases_on `b` \\ Cases_on `c` \\ SIMP_TAC std_ss [])

val core_admit_switch_thm = prove(
  ``milawa_inv ctxt simple_ctxt k (axioms,thms,atbl,checker,ftbl) ==>
    ?x io2 ok2 result.
      core_admit_switch_side cmd (milawa_state (axioms,thms,atbl,checker,ftbl)) k io ok /\
      (core_admit_switch cmd (milawa_state (axioms,thms,atbl,checker,ftbl)) k io ok =
         (x,k,io2,ok2)) /\
      (ok2 ==> (io2 = io) /\
               ?result. (x = milawa_state result) /\ milawa_inv ctxt simple_ctxt k result)``,
  FS [core_admit_switch_def,LET_DEF,milawa_state_def,core_state_def,
      SIMP_RULE std_ss [DISJ_EQ_IMP,GSYM AND_IMP_INTRO,LET_DEF] core_admit_switch_side_def]
  \\ SRW_TAC [] [] \\ FS [] \\ FS []
  \\ Q.EXISTS_TAC `(axioms,thms,atbl,CAR (CDR cmd),ftbl)`
  \\ STRIP_TAC THEN1 (FS [milawa_state_def,core_state_def])
  \\ FS [milawa_inv_def]
  \\ `?name. CAR (CDR cmd) = Sym name` by
      (Cases_on `CAR (CDR cmd)` \\ FS [logic_function_namep_def])
  \\ FS [] \\ SIMP_TAC std_ss [core_check_proof_inv_def]
  \\ Q.EXISTS_TAC `name` \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
  \\ FS [logic_soundness_claim_def,logic_por_def]
  \\ `?g. Sym name = logic_func2sexp g` by
   (Cases_on `name = "NOT"` THEN1
      (Q.EXISTS_TAC `mPrimitiveFun logic_NOT` \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss [])
    \\ Cases_on `name = "RANK"` THEN1
      (Q.EXISTS_TAC `mPrimitiveFun logic_RANK` \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss [])
    \\ Cases_on `name = "ORDP"` THEN1
      (Q.EXISTS_TAC `mPrimitiveFun logic_ORDP` \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss [])
    \\ Cases_on `name = "ORD<"` THEN1
      (Q.EXISTS_TAC `mPrimitiveFun logic_ORD_LESS` \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss [])
    \\ Cases_on `name = "IF"` THEN1
      (Q.EXISTS_TAC `mPrimitiveFun logic_IF` \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss [])
    \\ FS [logic_function_namep_def]
    \\ FULL_SIMP_TAC std_ss [GSYM list2sexp_def,memberp_thm,MEM] \\ FS []
    \\ REVERSE (Cases_on `sym2prim name`) THEN1
     (Q.EXISTS_TAC `mPrimitiveFun (prim2p (THE (sym2prim name)))`
      \\ FULL_SIMP_TAC std_ss [sym2prim_def] \\ POP_ASSUM MP_TAC
      \\ SRW_TAC [] [] \\ EVAL_TAC)
    \\ Q.EXISTS_TAC `mFun name`
    \\ ASM_SIMP_TAC std_ss [logic_func2sexp_def,MEM]
    \\ SRW_TAC [] [] \\ POP_ASSUM MP_TAC \\ EVAL_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [GSYM list2sexp_def,
       GSYM (EVAL ``t2sexp (mVar "X")``),
       GSYM (EVAL ``t2sexp (mVar "ATBL")``),
       GSYM (EVAL ``t2sexp (mVar "THMS")``),
       GSYM (EVAL ``t2sexp (mVar "AXIOMS")``),
       GSYM (EVAL ``logic_func2sexp (mFun "LOGIC.PROVABLEP")``),
       GSYM (EVAL ``logic_func2sexp (mFun "LOGIC.APPEALP")``),
       GSYM (EVAL ``logic_func2sexp (mFun "LOGIC.CONCLUSION")``),
       EVAL ``t2sexp (mApp f [x1])`` |> REWRITE_RULE [GSYM list2sexp_def] |> GSYM,
       EVAL ``t2sexp (mApp f [x1;x2])`` |> REWRITE_RULE [GSYM list2sexp_def] |> GSYM,
       EVAL ``t2sexp (mApp f [x1;x2;x3])`` |> REWRITE_RULE [GSYM list2sexp_def] |> GSYM,
       EVAL ``t2sexp (mApp f [x1;x2;x3;x4])`` |> REWRITE_RULE [GSYM list2sexp_def] |> GSYM]
  \\ SIMP_TAC std_ss [CONJUNCT1 (GSYM t2sexp_def),GSYM f2sexp_def]
  \\ FS [MEM_MAP] \\ STRIP_TAC \\ FS [thms_inv_def,EVERY_MEM]
  \\ RES_TAC \\ POP_ASSUM MP_TAC \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (K ALL_TAC)
  \\ STRIP_TAC
  \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
  \\ FS [term_ok_def,formula_ok_def,EVERY_DEF,LENGTH,func_arity_def]
  \\ `g = mFun name` by
   (Cases_on `g`
    THEN1 (Cases_on `l` \\ FULL_SIMP_TAC std_ss [func_arity_def,primitive_arity_def])
    \\ SIMP_TAC (srw_ss()) [] \\ CCONTR_TAC
    \\ Q.PAT_X_ASSUM `isTrue (logic_function_namep (logic_func2sexp (mFun s)))` MP_TAC
    \\ SIMP_TAC std_ss []
    \\ ASM_SIMP_TAC std_ss [logic_func2sexp_def,MEM]
    \\ SRW_TAC [] []
    \\ FULL_SIMP_TAC (srw_ss()) [logic_func2sexp_def])
  \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [func_arity_def]
  \\ IMP_RES_TAC Milawa_SOUNDESS
  \\ FULL_SIMP_TAC std_ss [MilawaValid_def,EvalFormula_def,EvalTerm_def,
       EvalApp_def,MAP,LET_DEF]
  \\ `?x1 x2 appealp. ctxt ' "LOGIC.APPEALP" = (x1,x2,appealp)` by METIS_TAC [PAIR]
  \\ `?y1 y2 f. ctxt ' name = (y1,y2,f)` by METIS_TAC [PAIR]
  \\ `?z1 z2 provablep. ctxt ' "LOGIC.PROVABLEP" = (z1,z2,provablep)` by METIS_TAC [PAIR]
  \\ `?q1 q2 conclusion. ctxt ' "LOGIC.CONCLUSION" = (q1,q2,conclusion)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [formula_ok_def,term_ok_def,func_arity_def,EVERY_DEF,LENGTH]
  \\ FULL_SIMP_TAC std_ss [runtime_inv_def]
  \\ Q.PAT_X_ASSUM `!name params. bbb` (fn th => MP_TAC th THEN MP_TAC (Q.SPEC `name` th))
  \\ FS [] \\ STRIP_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`[x1;x2;x3;x4]`,`ok`])
  \\ SIMP_TAC std_ss [LENGTH] \\ REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`f [x1; x2; x3; x4]`,`ok2`] \\ ASM_SIMP_TAC std_ss []
  \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ FULL_SIMP_TAC std_ss [GSYM thms_inv_def,GSYM EVERY_MEM]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ FULL_SIMP_TAC std_ss [GSYM thms_inv_def]
  \\ REVERSE (Cases_on `ok2`) \\ FS [] THEN1 METIS_TAC [MR_IMP_R]
  \\ Q.PAT_X_ASSUM `!a:string->SExp.bbb` (MP_TAC o Q.SPEC `("X" =+ x1) (("AXIOMS" =+ x2)
      (("THMS" =+ x3) (("ATBL" =+ x4) (\x. ARB))))`)
  \\ FS [APPLY_UPDATE_THM] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT (Q.PAT_X_ASSUM `T` (K ALL_TAC))
  \\ FULL_SIMP_TAC std_ss [runtime_inv_def]
  \\ Q.PAT_X_ASSUM `!name params. bbb` (fn th => MP_TAC th THEN MP_TAC (Q.SPEC `name` th))
  \\ FS [] \\ STRIP_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`[x1;x2;x3;x4]`,`ok`])
  \\ SIMP_TAC std_ss [LENGTH] \\ STRIP_TAC \\ STRIP_TAC
  \\ `!w1. appealp [w1] = logic_appealp w1` by
   (REPEAT STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `"LOGIC.APPEALP"`) \\ FS []
    \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`[w1]`,`T`])
    \\ SIMP_TAC std_ss [LENGTH] \\ STRIP_TAC
    \\ IMP_RES_TAC (MR_IMP_R |> CONJUNCTS |> hd |> SPEC_ALL |> Q.INST [`f`|->`Fun (x::xs)`])
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `io`)
    \\ METIS_TAC [R_ap_T_11,R_ev_logic_appealp,PAIR_EQ,MR_IMP_R])
  \\ `!w1. conclusion [w1] = logic_conclusion w1` by
   (REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!name params body sem args ok. bbb` (MP_TAC o Q.SPEC `"LOGIC.CONCLUSION"`) \\ FS []
    \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`[w1]`,`T`])
    \\ SIMP_TAC std_ss [LENGTH] \\ STRIP_TAC
    \\ IMP_RES_TAC (MR_IMP_R |> CONJUNCTS |> hd |> SPEC_ALL |> Q.INST [`f`|->`Fun (x::xs)`])
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `io`)
    \\ METIS_TAC [R_ap_T_11,R_ev_logic_conclusion,PAIR_EQ,MR_IMP_R,
         logic_conclusion_def,SECOND_def])
  \\ FULL_SIMP_TAC std_ss [] \\ SIMP_TAC std_ss [DISJ_EQ_IMP]
  \\ SIMP_TAC std_ss [GSYM isTrue_def]
  \\ `R_ap (Fun name,[x1; x2; x3; x4],ARB,k,io,ok)
           (f [x1; x2; x3; x4],k,io,T)` by METIS_TAC [MR_IMP_R,APPEND_NIL]
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `isTrue (f [x1; x2; x3; x4])` \\ FS []
  \\ STRIP_TAC \\ STRIP_TAC
  \\ `func_definition_exists ctxt "LOGIC.PROVABLEP" z1 z2 provablep` by
    (FULL_SIMP_TAC std_ss [func_definition_exists_def])
  \\ FULL_SIMP_TAC std_ss [axioms_inv_def]
  \\ `axioms_aux "LOGIC.PROVABLEP" ctxt axioms ftbl z1 provablep z2` by FS []
  \\ REVERSE (Cases_on `z2`) THEN1
   (FULL_SIMP_TAC std_ss [axioms_aux_def,witness_body_def]
    \\ IMP_RES_TAC (MATCH_MP lookup_init_lemma lookup_provablep) \\ FS [])
  THEN1
   (FULL_SIMP_TAC std_ss [axioms_aux_def,witness_body_def]
    \\ IMP_RES_TAC (MATCH_MP lookup_init_lemma lookup_provablep) \\ FS [])
  \\ FULL_SIMP_TAC std_ss [axioms_aux_def,witness_body_def]
  \\ IMP_RES_TAC (MATCH_MP lookup_init_lemma lookup_provablep_thm) \\ FS []
  \\ `term_ok ctxt (term2t (sexp3term lookup_provablep_body))` by
        METIS_TAC [context_ok_def,context_inv_def]
  \\ `"LOGIC.PROVABLE-WITNESS" IN FDOM ctxt /\ (LENGTH (FST (ctxt ' "LOGIC.PROVABLE-WITNESS")) = 4) /\
      "LOGIC.PROOFP" IN FDOM ctxt /\ (LENGTH (FST (ctxt ' "LOGIC.PROOFP")) = 4)` by
        (POP_ASSUM MP_TAC \\ EVAL_TAC \\ SRW_TAC [] [])
  \\ `(provablep = EvalFun "LOGIC.PROVABLEP" ctxt)` by
        (FULL_SIMP_TAC std_ss [context_inv_def] \\ RES_TAC \\ ASM_REWRITE_TAC [])
  \\ Q.PAT_X_ASSUM `isTrue (logic_appealp x1) ==> bbb` MP_TAC
  \\ ASM_REWRITE_TAC [] \\ REWRITE_TAC [EvalFun_def,Eval_M_ap_def]
  \\ ONCE_REWRITE_TAC [M_ev_cases] \\ ASM_SIMP_TAC (srw_ss()) []
  \\ `?r1 r2 provable_witness. ctxt ' "LOGIC.PROVABLE-WITNESS" =
          (r1,r2,provable_witness)` by METIS_TAC [PAIR]
  \\ `?v1 v2 proofp. (ctxt ' "LOGIC.PROOFP" =
          (v1,v2,proofp))` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss []
  \\ `!w1 w2 w3 w4. proofp [w1;w2;w3;w4] = logic_proofp w1 w2 w3 w4` by
   (REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!name params body sem args ok. bbb` (MP_TAC o Q.SPEC `"LOGIC.PROOFP"`) \\ FS []
    \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`[w1;w2;w3;w4]`,`T`])
    \\ SIMP_TAC std_ss [LENGTH] \\ STRIP_TAC
    \\ IMP_RES_TAC (MR_IMP_R |> CONJUNCTS |> hd |> SPEC_ALL |> Q.INST [`f`|->`Fun (x::xs)`])
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `io`)
    \\ METIS_TAC [R_ap_T_11,R_ev_logic_proofp,PAIR_EQ,MR_IMP_R])
  \\ `?z11 z12 z13 z14. z1 = [z11;z12;z13;z14]` by
    (Cases_on `z1` \\ FS [MAP,list2sexp_def]
     \\ Cases_on `t` \\ FS [MAP,list2sexp_def]
     \\ Cases_on `t'` \\ FS [MAP,list2sexp_def]
     \\ Cases_on `t` \\ FS [MAP,list2sexp_def]
     \\ Cases_on `t'` \\ FS [MAP,list2sexp_def,CONS_11])
  \\ FS [MAP,FunVarBind_def]
  \\ ONCE_REWRITE_TAC [EVAL ``(term2t (sexp3term lookup_provablep_body))``]
  \\ NTAC 20 (ONCE_REWRITE_TAC [M_ev_cases] \\ ASM_SIMP_TAC (srw_ss())
                [FunVarBind_def,APPLY_UPDATE_THM])
  \\ SIMP_TAC (srw_ss()) [EVAL_PRIMITIVE_def,LISP_EQUAL_def]
  \\ `?prooff. provable_witness [CAR (CDR x1); x2; x3; x4] = prooff` by METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [core_admit_switch_lemma]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `isTrue (logic_appealp (a2sexp proof))` by ASM_SIMP_TAC std_ss [appeal_syntax_ok_thm]
  \\ FS [] \\ Cases_on `isTrue (logic_appealp prooff)` \\ FS []
  \\ Cases_on `isTrue
                 (logic_proofp prooff (list2sexp (MAP f2sexp axioms'))
                    (list2sexp (MAP f2sexp thms')) x4)` \\ FS []
  \\ FULL_SIMP_TAC std_ss [primitive_arity_def]
  \\ Q.PAT_X_ASSUM `bbb = prooff` MP_TAC
  \\ `func_definition_exists ctxt "LOGIC.PROVABLE-WITNESS" r1 r2 provable_witness` by
    (FULL_SIMP_TAC std_ss [func_definition_exists_def])
  \\ FULL_SIMP_TAC std_ss [axioms_inv_def]
  \\ `axioms_aux "LOGIC.PROVABLE-WITNESS" ctxt axioms ftbl r1 provable_witness r2` by FS []
  \\ Cases_on `r2` THEN1
   (FULL_SIMP_TAC std_ss [axioms_aux_def,witness_body_def]
    \\ IMP_RES_TAC (MATCH_MP lookup_init_lemma lookup_provable_witness) \\ FS [])
  \\ FULL_SIMP_TAC std_ss [axioms_aux_def,witness_body_def]
  \\ IMP_RES_TAC (MATCH_MP lookup_init_lemma lookup_provable_witness_thm) \\ FS []
  \\ FULL_SIMP_TAC (srw_ss()) [lookup_provable_witness_body_def]
  \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC \\ NTAC 6 (POP_ASSUM (K ALL_TAC))
  \\ Q.PAT_X_ASSUM `ctxt ' "LOGIC.PROVABLE-WITNESS" = bbb` MP_TAC
  \\ CONV_TAC (RATOR_CONV (RAND_CONV EVAL)) \\ STRIP_TAC \\ STRIP_TAC
  \\ `?r11 r12 r13 r14. r1 = [r11;r12;r13;r14]` by
    (Cases_on `r1` \\ FS [MAP,list2sexp_def]
     \\ Cases_on `t` \\ FS [MAP,list2sexp_def]
     \\ Cases_on `t'` \\ FS [MAP,list2sexp_def]
     \\ Cases_on `t` \\ FS [MAP,list2sexp_def]
     \\ Cases_on `t'` \\ FS [MAP,list2sexp_def,CONS_11])
  \\ FS [MAP]
  \\ Q.PAT_X_ASSUM `ctxt ' "LOGIC.PROVABLE-WITNESS" = bbb` MP_TAC
  \\ Q.PAT_ABBREV_TAC `wit = mApp xxx yyy` \\ STRIP_TAC
  \\ `(provable_witness = (\args. @v.
        isTrue (EvalTerm (FunVarBind ("PROOF"::r1) (v::args),ctxt) wit)))` by
         (FULL_SIMP_TAC std_ss [context_inv_def] \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [] \\ Q.UNABBREV_TAC `wit`
  \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (K ALL_TAC)
  \\ FULL_SIMP_TAC (srw_ss()) [EvalTerm_def,EvalApp_def,MAP,LET_DEF,EVAL_PRIMITIVE_def,
       FunVarBind_def,APPLY_UPDATE_THM]
  \\ ASM_SIMP_TAC std_ss [LISP_IF_def] \\ IMP_RES_TAC logic_appealp_thm
  \\ FS [] \\ METIS_TAC [logic_proofp_thm]);


(* admit eval *)

val logic_func2sexp_IN_core_initial_atbl = prove(
  ``!f. isTrue (lookup (logic_func2sexp f) core_initial_atbl) =
        ?p. f = mPrimitiveFun p``,
  Cases THEN1 (Cases_on `l` \\ SIMP_TAC (srw_ss()) [] \\ EVAL_TAC)
  \\ SIMP_TAC (srw_ss()) [logic_func2sexp_def]
  \\ SRW_TAC [] [] \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss []);

val core_eval_function_thm = prove(
  ``milawa_inv ctxt simple_ctxt k (axioms,thms,atbl,checker,ftbl) /\
    term_syntax_ok (mApp (mFun f) (MAP mConst xs)) /\
    term_ok ctxt (mApp (mFun f) (MAP mConst xs)) ==>
    ?res io2 ok2 k2.
      core_eval_function_side (t2sexp (mApp (mFun f) (MAP mConst xs))) k io ok /\
      (core_eval_function (t2sexp (mApp (mFun f) (MAP mConst xs))) k io ok =
         (res,k2,io2,ok2)) /\
      (ok2 ==> (io2 = io) /\ (k2 = k) /\
               MR_ap (Fun f,xs,ARB,ctxt,k,ok) (EvalApp((mFun f),xs,ctxt),T) /\
               (res = t2sexp (mConst (EvalApp((mFun f),xs,ctxt)))))``,
  SIMP_TAC std_ss [core_eval_function_def,core_eval_function_side_def]
  \\ FS [t2sexp_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [LENGTH,term_ok_def,func_arity_def,EVERY_DEF,LENGTH_MAP]
  \\ STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [func_arity_def]
  \\ `?x1 x2 x3. ctxt ' f = (x1,x2,x3)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [milawa_inv_def,runtime_inv_def]
  \\ `LENGTH xs = LENGTH x1` by FS []
  \\ RES_TAC \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `ok`)
  \\ FS [EvalApp_def,LET_DEF]
  \\ IMP_RES_TAC (CONJUNCT1 MR_IMP_R) \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `io`)
  \\ `(logic_func2sexp (mFun f) = Sym f)` by
   (FULL_SIMP_TAC std_ss [logic_func2sexp_def,MEM,term_syntax_ok_def,
      func_syntax_ok_def]) \\ FS []
  \\ IMP_RES_TAC Funcall_lemma
  \\ `funcall_ok (Sym f::xs) k io ok` by METIS_TAC [funcall_ok_def]
  \\ `ok2 ==> (funcall (Sym f::xs) k io ok = (x3 xs,k,STRCAT io io1,ok2))` by
   (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [funcall_def] \\ METIS_TAC [R_ap_T_11])
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `x1` \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,APPEND_NIL]
  THEN1 (STRIP_TAC \\ IMP_RES_TAC SND_SND_SND_funcall_IMP
         \\ FULL_SIMP_TAC std_ss [APPEND_NIL] \\ METIS_TAC [APPEND_NIL])
  \\ Cases_on `t` \\ Cases_on `t'` \\ FS [LENGTH,ADD1,APPEND_NIL,list2sexp_def]
  THEN1 (STRIP_TAC \\ IMP_RES_TAC SND_SND_SND_funcall_IMP
         \\ FULL_SIMP_TAC std_ss [APPEND_NIL] \\ METIS_TAC [APPEND_NIL])
  \\ Cases_on `t` \\ Cases_on `t''` \\ FS [LENGTH,ADD1,APPEND_NIL,list2sexp_def]
  THEN1 (STRIP_TAC \\ IMP_RES_TAC SND_SND_SND_funcall_IMP
         \\ FULL_SIMP_TAC std_ss [APPEND_NIL] \\ METIS_TAC [APPEND_NIL])
  \\ Cases_on `t'` \\ Cases_on `t` \\ FS [LENGTH,ADD1,APPEND_NIL,list2sexp_def]
  THEN1 (STRIP_TAC \\ IMP_RES_TAC SND_SND_SND_funcall_IMP
         \\ FULL_SIMP_TAC std_ss [APPEND_NIL] \\ METIS_TAC [APPEND_NIL])
  \\ Cases_on `t''` \\ Cases_on `t'` \\ FS [LENGTH,ADD1,APPEND_NIL,list2sexp_def]
  THEN1 (STRIP_TAC \\ IMP_RES_TAC SND_SND_SND_funcall_IMP
         \\ FULL_SIMP_TAC std_ss [APPEND_NIL] \\ METIS_TAC [APPEND_NIL])
  \\ Cases_on `t''` \\ Cases_on `t` \\ FS [LENGTH,ADD1,APPEND_NIL,list2sexp_def]
  THEN1 (STRIP_TAC \\ IMP_RES_TAC SND_SND_SND_funcall_IMP
         \\ FULL_SIMP_TAC std_ss [APPEND_NIL] \\ METIS_TAC [APPEND_NIL])
  \\ SIMP_TAC std_ss [GSYM ADD_ASSOC,DECIDE ``~(n + 6 = 2:num)``,
       DECIDE ``~(n + 6 = 3:num)``,DECIDE ``~(n + 6 = 4:num)``,
       DECIDE ``~(n + 6 = 5:num)``]);

val logic_constant_listp_thm = prove(
  ``!l. isTrue (logic_constant_listp (list2sexp (MAP t2sexp l))) ==>
        ?ts. l = MAP mConst ts``,
  Induct THEN1 (REPEAT STRIP_TAC \\ Q.EXISTS_TAC `[]` \\ EVAL_TAC)
  \\ FULL_SIMP_TAC std_ss [MAP,list2sexp_def] \\ FS []
  \\ SIMP_TAC std_ss [Once logic_constant_listp_def] \\ FS []
  \\ REVERSE (Cases_on `h`) \\ FS [t2sexp_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ Q.EXISTS_TAC `S'::ts` \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss []);

val core_admit_eval_thm = prove(
  ``milawa_inv ctxt simple_ctxt k (axioms,thms,atbl,checker,ftbl) ==>
    ?x io2 ok2 k2.
      core_admit_eval_side cmd (milawa_state (axioms,thms,atbl,checker,ftbl)) k io ok /\
      (core_admit_eval cmd (milawa_state (axioms,thms,atbl,checker,ftbl)) k io ok =
         (x,k2,io2,ok2)) /\
      (ok2 ==> (io2 = io) /\ (k2 = k) /\
               ?result. (x = milawa_state result) /\ milawa_inv ctxt simple_ctxt k result)``,
  SIMP_TAC std_ss [core_admit_eval_def,core_admit_eval_side_def,LET_DEF] \\ FS []
  \\ Q.ABBREV_TAC `lhs = CAR (CDR cmd)` \\ STRIP_TAC
  \\ Cases_on `isTrue (logic_termp lhs)` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `isTrue (logic_function_namep (CAR lhs))` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `isTrue (logic_constant_listp (CDR lhs))` \\ FS []
  \\ Cases_on `isTrue (logic_term_atblp lhs
      (CAR (CDR (CDR (milawa_state (axioms,thms,atbl,checker,ftbl))))))` \\ FS []
  \\ Cases_on `isTrue (lookup (CAR lhs) core_initial_atbl)` \\ FS []
  \\ IMP_RES_TAC logic_termp_thm
  \\ FULL_SIMP_TAC std_ss [milawa_state_def] \\ FS [core_state_def]
  \\ FULL_SIMP_TAC std_ss [milawa_inv_def]
  \\ IMP_RES_TAC logic_term_atblp_thm
  \\ Cases_on `t`
  \\ FS [t2sexp_def,logic_function_namep_def]
  \\ FULL_SIMP_TAC std_ss [GSYM list2sexp_def,memberp_thm,MEM]
  \\ FS [] \\ Cases_on `l0` THEN1
   (CCONTR_TAC
    \\ Q.PAT_X_ASSUM `~isTrue
          (lookup (logic_func2sexp (mPrimitiveFun l'))
             core_initial_atbl)` MP_TAC
    \\ Cases_on `l'` \\ EVAL_TAC)
  \\ FULL_SIMP_TAC std_ss [EXISTS_PROD,milawa_state_def,core_state_def]
  \\ FS [milawa_inv_def,MAP_f2sexp_11]
  \\ IMP_RES_TAC logic_constant_listp_thm \\ FULL_SIMP_TAC std_ss []
  \\ MP_TAC (core_eval_function_thm |> Q.INST [`xs`|->`ts`,`f`|->`s`])
  \\ FS [term_ok_def,term_syntax_ok_def,milawa_inv_def,t2sexp_def]
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `(Equal (mApp (mFun s) (MAP mConst ts))
       (mConst (EvalApp (mFun s,ts,ctxt))))::thms`
  \\ FS [list2sexp_def,MAP,f2sexp_def,t2sexp_def,thms_inv_def,EVERY_DEF]
  \\ FS [formula_syntax_ok_def,term_syntax_ok_def]
  \\ FS [runtime_inv_def,func_arity_def]
  \\ `?x1 x2 x3. ctxt ' s = (x1,x2,x3)` by METIS_TAC [PAIR]
  \\ FS [LENGTH_MAP] \\ `LENGTH ts = LENGTH x1` by METIS_TAC []
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [EvalApp_def,LET_DEF,MilawaTrueFun_def]
  \\ POP_ASSUM (MP_TAC o Q.SPEC `ok`) \\ STRIP_TAC
  \\ IMP_RES_TAC MR_ev_11_ALL
  \\ FULL_SIMP_TAC std_ss []);


(* admit print *)

val line_ok_def = Define `
  line_ok (ctxt,line) =
    (line = "") \/ (line = "NIL") \/
    (?p. context_ok ctxt /\ MilawaValid ctxt p /\
         (line = sexp2string (list2sexp [Sym "PRINT"; list2sexp [Sym "THEOREM"; f2sexp p]]))) \/
    (?n x y. line = sexp2string (list2sexp [Sym "PRINT"; list2sexp [Val n; x; y]]))`;

val output_to_string_def = Define `
  (output_to_string [] = "") /\
  (output_to_string (x::xs) = SND x ++ "\n" ++ output_to_string xs)`;

(*
val milawa_io_inv_def = Define `
  milawa_io_inv io =
    ?lines. EVERY output_line_ok lines /\
            (io = FOLDL (\(ctxt,x) y. x ++ y ++ "\n") "" lines)`;
*)

(*
val milawa_io_inv_UNFOLD = prove(
  ``milawa_io_inv io /\ output_line_ok line ==>
    milawa_io_inv (io ++ line ++ "\n")``,
  SIMP_TAC std_ss [milawa_io_inv_def] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `lines ++ [line]` \\ FULL_SIMP_TAC std_ss [EVERY_DEF,EVERY_APPEND]
  \\ FULL_SIMP_TAC std_ss [GSYM SNOC_APPEND,FOLDL_SNOC]);
*)

val print_thm_def = Define `
  print_thm ctxt cmd =
    (ctxt,sexp2string
      (list2sexp [Sym "PRINT"; list2sexp [Sym "THEOREM"; CAR (CDR cmd)]]))`;

val core_admit_print_thm = prove(
  ``milawa_inv ctxt simple_ctxt k (axioms,thms,atbl,checker,ftbl) ==>
    ?x io2 ok2.
      core_admit_print_side cmd (milawa_state (axioms,thms,atbl,checker,ftbl)) k io ok /\
      (core_admit_print cmd (milawa_state (axioms,thms,atbl,checker,ftbl)) k io ok =
         (x,k,io2,ok2)) /\
      (ok2 ==> (io2 = io ++ SND (print_thm simple_ctxt cmd) ++ "\n") /\
               line_ok (print_thm simple_ctxt cmd) /\
               (x = (milawa_state (axioms,thms,atbl,checker,ftbl))))``,
  FS [core_admit_print_def,LET_DEF,milawa_state_def,core_state_def,
      SIMP_RULE std_ss [DISJ_EQ_IMP,GSYM AND_IMP_INTRO,LET_DEF] core_admit_print_side_def]
  \\ Cases_on `list_exists 2 cmd` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `CAR cmd <> Sym "PRINT"` \\ ASM_REWRITE_TAC []
  THEN1 (SIMP_TAC std_ss [])
  \\ Cases_on `MEM (CAR (CDR cmd)) (MAP f2sexp axioms)` \\ FS []
  \\ Cases_on `MEM (CAR (CDR cmd)) (MAP f2sexp thms)` \\ FS []
  \\ (REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [GSYM list2sexp_def,APPEND_ASSOC]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND_11]
    \\ SIMP_TAC std_ss [line_ok_def,print_thm_def]
    \\ DISJ2_TAC \\ DISJ2_TAC \\ DISJ1_TAC
    \\ FULL_SIMP_TAC std_ss [MEM_MAP,milawa_inv_def,thms_inv_def,EVERY_MEM]
    \\ RES_TAC \\ `context_syntax_same ctxt simple_ctxt` by
         FS [context_syntax_same_def,similar_context_def]
    \\ `MilawaTrue simple_ctxt y` by METIS_TAC [MilawaTrue_context_syntax_same]
    \\ METIS_TAC [Milawa_SOUNDESS,similar_context_def]));


(* step case -- accept command *)

val core_accept_command_thm = prove(
  ``milawa_inv ctxt simple_ctxt k (axioms,thms,atbl,checker,ftbl) ==>
    core_accept_command_side cmd (milawa_state (axioms,thms,atbl,checker,ftbl)) k io ok /\
    ?x k2 io2 ok2 result ctxt.
      (core_accept_command cmd (milawa_state (axioms,thms,atbl,checker,ftbl)) k io ok =
         (x,k2,io2,ok2)) /\
      (ok2 ==> (x = milawa_state result) /\
               milawa_inv ctxt (if CAR cmd = Sym "DEFINE" then defun_ctxt simple_ctxt cmd else
                                if CAR cmd = Sym "SKOLEM" then witness_ctxt simple_ctxt cmd else
                                  simple_ctxt) k2 result /\
               ((CAR cmd = Sym "PRINT") ==> line_ok (print_thm simple_ctxt cmd)) /\
               (io2 = if CAR cmd = Sym "PRINT" then io ++ SND (print_thm simple_ctxt cmd) ++ "\n" else io))``,
  STRIP_TAC \\ STRIP_TAC THEN1
   (SIMP_TAC std_ss [core_accept_command_side_def]
    \\ IMP_RES_TAC core_admit_eval_thm
    \\ IMP_RES_TAC core_admit_switch_thm
    \\ IMP_RES_TAC core_admit_defun_thm
    \\ IMP_RES_TAC core_admit_witness_thm
    \\ IMP_RES_TAC core_admit_theorem_thm
    \\ IMP_RES_TAC core_admit_print_thm
    \\ METIS_TAC [])
  \\ SIMP_TAC std_ss [core_accept_command_def]
  \\ Cases_on `CAR cmd = Sym "VERIFY"` \\ FS [] \\ FULL_SIMP_TAC (srw_ss()) []
  THEN1 (METIS_TAC [core_admit_theorem_thm])
  \\ Cases_on `CAR cmd = Sym "DEFINE"` \\ FS [] \\ FULL_SIMP_TAC (srw_ss()) []
  THEN1 (METIS_TAC [core_admit_defun_thm])
  \\ Cases_on `CAR cmd = Sym "SKOLEM"` \\ FS [] \\ FULL_SIMP_TAC (srw_ss()) []
  THEN1 (METIS_TAC [core_admit_witness_thm])
  \\ Cases_on `CAR cmd = Sym "PRINT"` \\ FS [] \\ FULL_SIMP_TAC (srw_ss()) []
  THEN1 (METIS_TAC [core_admit_print_thm])
  \\ Cases_on `CAR cmd = Sym "SWITCH"` \\ FS [] \\ FULL_SIMP_TAC (srw_ss()) []
  THEN1 (METIS_TAC [core_admit_switch_thm])
  \\ Cases_on `CAR cmd = Sym "EVAL"` \\ FS [] \\ FULL_SIMP_TAC (srw_ss()) []
  THEN1 (METIS_TAC [core_admit_eval_thm]));


(* loop -- accept commands *)

val print_event_number_def = Define `
  print_event_number n cmd =
    (sexp2string (list2sexp    [Sym "PRINT";
                                LISP_CONS (Val n)
                                  (LISP_CONS (FIRST cmd)
                                     (LISP_CONS (SECOND cmd)
                                        (Sym "NIL")))]))`;

val milawa_command_def = Define `
  milawa_command ctxt cmd =
    if CAR cmd = Sym "DEFINE" then (defun_ctxt ctxt cmd,[]) else
    if CAR cmd = Sym "SKOLEM" then (witness_ctxt ctxt cmd,[]) else
    if CAR cmd = Sym "PRINT" then (ctxt,[print_thm ctxt cmd]) else (ctxt,[])`

val milawa_commands_def = tDefine "milawa_commands" `
  milawa_commands ctxt n cmds =
    if ~(isDot cmds) then [] else
      let cmd = CAR cmds in
      let l1 = [(ctxt,print_event_number n cmd)] in
      let (new_ctxt,l2) = milawa_command ctxt cmd in
        l1 ++ l2 ++ milawa_commands new_ctxt (n+1) (CDR cmds)`
 (WF_REL_TAC `measure (LSIZE o SND o SND)`
  \\ FULL_SIMP_TAC std_ss [isDot_thm] \\ REPEAT STRIP_TAC
  \\ FS [LSIZE_def] \\ DECIDE_TAC) |> SPEC_ALL;

val line_ok_print_event_number = prove(
  ``line_ok (simple_ctxt,print_event_number n cmds)``,
  FS [line_ok_def,print_event_number_def] \\ METIS_TAC []);

val isDot_milawa_state = prove(
  ``!state. isDot (milawa_state state)``,
  FULL_SIMP_TAC std_ss [FORALL_PROD] \\ EVAL_TAC \\ SIMP_TAC std_ss []);

val core_accept_commands_thm = prove(
  ``!cmds n state k io ok ctxt simple_ctxt.
      milawa_inv ctxt simple_ctxt k state /\ ok ==>
      core_accept_commands_side cmds (Val n) (milawa_state state) k io ok /\
      ?x k2 io2 ok2 result ctxt.
        (core_accept_commands cmds (Val n) (milawa_state state) k io ok = (x,k2,io2,ok2)) /\
        (ok2 ==> isDot x /\
                 let output = milawa_commands simple_ctxt n cmds in
                   EVERY line_ok output /\ (io2 = io ++ output_to_string output))``,
  REVERSE (Induct) \\ SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [core_accept_commands_def,core_accept_commands_side_def]
  \\ SIMP_TAC std_ss [Once milawa_commands_def] \\ FS []
  THEN1 (FS [LET_DEF,EVERY_DEF,output_to_string_def,MAP,FOLDL,APPEND_NIL,isDot_milawa_state])
  THEN1 (FS [LET_DEF,EVERY_DEF,output_to_string_def,MAP,FOLDL,APPEND_NIL,isDot_milawa_state])
  \\ FS [LET_DEF] \\ NTAC 7 STRIP_TAC
  \\ FS [GSYM print_event_number_def |> SR [list2sexp_def,LISP_CONS_def]]
  \\ Q.PAT_ABBREV_TAC `io3 = (STRCAT (STRCAT io xx) yy)`
  \\ `?result. core_accept_command cmds (milawa_state state) k io3 T = result` by FS []
  \\ `?x1 x2 x3 x4 x5. state = (x1,x2,x3,x4,x5)` by METIS_TAC [PAIR] \\ FS []
  \\ `?y1 y2 y3 y4. result = (y1,y2,y3,y4)` by METIS_TAC [PAIR] \\ FS []
  \\ Q.PAT_X_ASSUM `xxx yyy = (y1,y2,y3,y4)` MP_TAC
  \\ IMP_RES_TAC core_accept_command_thm \\ FS []
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`T`,`io3`,`cmds`]) \\ FS []
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ])) \\ STRIP_TAC \\ FS []
  \\ REVERSE (Cases_on `ok2`) THEN1
   (ONCE_REWRITE_TAC [core_accept_commands_side_def] \\ SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [core_accept_commands_def] \\ SIMP_TAC std_ss [])
  \\ FS []
  \\ Q.ABBREV_TAC `new_simple_ctxt = (if CAR cmds = Sym "DEFINE" then
           defun_ctxt simple_ctxt cmds
         else if CAR cmds = Sym "SKOLEM" then
           witness_ctxt simple_ctxt cmds
         else
           simple_ctxt)`
  \\ Q.PAT_X_ASSUM `!x1 x2 x3 x4. bbb`
       (MP_TAC o Q.SPECL [`1+n`,`result'`,`k2`,`io2`,`ctxt'`,`new_simple_ctxt`])
  \\ FS []
  \\ Q.PAT_X_ASSUM `io2 = if CAR cmds = Sym "PRINT" then xxx else yyy` (ASSUME_TAC o GSYM)
  \\ FS [] \\ REPEAT STRIP_TAC \\ FS []
  \\ STRIP_TAC \\ FS []
  \\ Q.PAT_X_ASSUM `EVERY P xs` MP_TAC
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ FS [EVERY_APPEND,EVERY_DEF,line_ok_print_event_number]
  \\ `(FST (milawa_command simple_ctxt cmds)) = new_simple_ctxt` by (FS [milawa_command_def] \\ Q.UNABBREV_TAC `new_simple_ctxt` \\ SRW_TAC [] [])
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ REPEAT STRIP_TAC THEN1 (FS [milawa_command_def] \\ SRW_TAC [] [])
  \\ Q.PAT_X_ASSUM `xxx = io2` (ASSUME_TAC o GSYM) \\ FS []
  \\ Q.UNABBREV_TAC `io3`
  \\ FULL_SIMP_TAC std_ss [output_to_string_def,APPEND]
  \\ `SND (milawa_command simple_ctxt cmds) =
      if CAR cmds = Sym "PRINT" then [print_thm simple_ctxt cmds] else []` by (SRW_TAC [] [milawa_command_def] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Cases_on `CAR cmds = Sym "PRINT"`
  \\ FS [APPEND_ASSOC,APPEND,output_to_string_def]);


(* initialisation of main loop *)

val lookup_safe_lemma1 = SR [] milawa_defsTheory.lookup_safe_def
val lookup_safe_lemma2 = lookup_safe_lemma1 |> Q.INST [`x`|->`Sym t`] |> SR [isDot_def]
val lookup_safe_lemma2a = lookup_safe_lemma1 |> Q.INST [`x`|->`Val t`] |> SR [isDot_def]
val lookup_safe_lemma3 = lookup_safe_lemma1
   |> Q.INST [`x`|->`Dot (Dot (Sym s) y) z`,`a`|->`Sym t`]
   |> SR [isDot_def,CAR_def,CDR_def,SExp_11]

val ftbl_prop_def = Define `
  ftbl_prop ftbl k =
   (EVERY
     (\x.
        isTrue (CDR x) ==>
        (let name = getSym (CAR x) in
         let formals = MAP getSym (sexp2list (CAR (CDR x))) in
         let body = sexp2term (CAR (CDR (CDR x)))
         in name IN FDOM k /\ (k ' name = (formals,body))))
       (sexp2list ftbl) /\ EVERY isDot (sexp2list ftbl)) /\
   ALL_DISTINCT (MAP CAR (sexp2list ftbl))`;

val define_safe_list =
  milawa_initTheory.define_safe_list_def
  |> concl |> dest_eq |> fst |> repeat (fst o dest_comb);

val define_safe_list_IMP_ok = prove(
  ``!defs ftbl k io ok.
      (^define_safe_list ftbl defs k io ok = (ftbl2,k2,io2,T)) ==> ok``,
  REVERSE Induct
  THEN1 (FS [Once milawa_initTheory.define_safe_list_def])
  THEN1 (FS [Once milawa_initTheory.define_safe_list_def])
  \\ ONCE_REWRITE_TAC [milawa_initTheory.define_safe_list_def]
  \\ SIMP_TAC std_ss [LET_DEF,EVAL ``isTrue (LISP_CONSP (Dot defs defs'))``]
  \\ CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV))
  \\ SIMP_TAC std_ss [CDR_def,CAR_def] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [milawa_initTheory.define_safe_def,LET_DEF]
  \\ METIS_TAC []);

val lookup_safe =
  milawa_initTheory.lookup_safe_def
  |> concl |> dest_eq |> fst |> repeat (fst o dest_comb);

val lookp_safe_EQ_NIL = prove(
  ``!y x. (^lookup_safe x y = Sym "NIL") ==>
          ~MEM x (MAP CAR (sexp2list y))``,
  REVERSE Induct \\ ONCE_REWRITE_TAC [milawa_initTheory.lookup_safe_def] \\ FS []
  \\ FS [sexp2list_def,MAP,MEM] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC std_ss [isDot_thm] \\ FS []);

val ftbl_prop_MAINTAINED = prove(
  ``!x y k x2 k2.
      (^define_safe_list y x k ARB T = (x2,k2,ARB,T)) /\ ftbl_prop y k ==>
      ftbl_prop x2 k2``,
  REVERSE Induct
  THEN1 (ONCE_REWRITE_TAC [milawa_initTheory.define_safe_list_def] \\ FS [])
  THEN1 (ONCE_REWRITE_TAC [milawa_initTheory.define_safe_list_def] \\ FS [])
  \\ ONCE_REWRITE_TAC [milawa_initTheory.define_safe_list_def] \\ FS [LET_DEF]
  \\ SIMP_TAC std_ss [milawa_initTheory.define_safe_def,LET_DEF]
  \\ NTAC 4 STRIP_TAC
  \\ Cases_on `isTrue (^lookup_safe (CAR x) y)` \\ FS []
  \\ REPEAT STRIP_TAC
  THEN1 (IMP_RES_TAC define_safe_list_IMP_ok \\ FS [] \\ RES_TAC)
  \\ IMP_RES_TAC define_safe_list_IMP_ok
  \\ Q.PAT_X_ASSUM `!y.bbb` MATCH_MP_TAC
  \\ Q.EXISTS_TAC `(Dot
       (Dot (CAR x) (Dot (CAR (CDR x)) (Dot (CAR (CDR (CDR x))) (Sym "NIL")))) y)`
  \\ Q.EXISTS_TAC `(add_def k
           (getSym (CAR x),MAP getSym (sexp2list (CAR (CDR x))),
            sexp2term (CAR (CDR (CDR x)))))` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [ftbl_prop_def,sexp2list_def,MAP,CAR_def,
        EVERY_DEF,isDot_def,ALL_DISTINCT,CDR_def] \\ FS [isTrue_def]
  \\ FULL_SIMP_TAC std_ss [add_def_def,FUNION_DEF,IN_UNION,LET_DEF,
        FDOM_FUPDATE,IN_INSERT,FAPPLY_FUPDATE_THM,FDOM_FEMPTY,NOT_IN_EMPTY]
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM,lookp_safe_EQ_NIL]);

val init_thm = prove(
  ``?result.
      (core_state core_initial_axioms (Sym "NIL") core_initial_atbl
                  (Sym "LOGIC.PROOFP") init_ftbl = milawa_state result) /\
      milawa_inv FEMPTY FEMPTY core_funs result``,
  Q.EXISTS_TAC `(MILAWA_AXIOMS,[],core_initial_atbl,Sym "LOGIC.PROOFP",init_ftbl)`
  \\ SIMP_TAC std_ss [milawa_state_def,MAP,list2sexp_def]
  \\ REPEAT STRIP_TAC THEN1
   (FS [core_state_def]
    \\ REWRITE_TAC [MILAWA_AXIOMS_def,MAP,f2sexp_def,t2sexp_def,APPEND,
         core_initial_axioms_def,SExp_11,GSYM list2sexp_def,app_thm,LISP_CONS_def]
    \\ SIMP_TAC std_ss [list2sexp_def,SExp_11,logic_func2sexp_def,
         logic_prim2sym_def,MAP,t2sexp_def]
    \\ REPEAT STRIP_TAC \\ CONV_TAC (RATOR_CONV EVAL) \\ REWRITE_TAC [])
  \\ SIMP_TAC std_ss [milawa_inv_def] \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC std_ss [context_ok_def,FDOM_FEMPTY,NOT_IN_EMPTY])
  THEN1 (FULL_SIMP_TAC std_ss [context_inv_def,FDOM_FEMPTY,NOT_IN_EMPTY])
  THEN1 (FS [similar_context_def,FDOM_FEMPTY,NOT_IN_EMPTY,FEVERY_DEF,context_ok_def])
  THEN1
   (SIMP_TAC std_ss [atbl_ok_def] \\ REVERSE Cases THEN1
     (FULL_SIMP_TAC std_ss [func_syntax_ok_def,MEM,logic_func2sexp_def]
      \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [] \\ EVAL_TAC)
    \\ Cases_on `l` \\ EVAL_TAC)
  THEN1 EVAL_TAC
  THEN1 EVAL_TAC
  THEN1
   (SIMP_TAC std_ss [thms_inv_def,EVERY_MEM] \\ REPEAT STRIP_TAC
    \\ `MilawaTrue FEMPTY e` by (METIS_TAC [MilawaTrue_rules])
    \\ FULL_SIMP_TAC std_ss [MILAWA_AXIOMS_def,MEM] \\ EVAL_TAC)
  THEN1
   (SIMP_TAC std_ss [core_check_proof_inv_init])
  THEN1
   (SIMP_TAC std_ss [ftbl_inv_def]
    \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ REVERSE STRIP_TAC
    THEN1 (Q.EXISTS_TAC `0` \\ SIMP_TAC std_ss [FUNPOW])
    \\ `EVERY (\s. lookup_safe (Sym s) init_ftbl = list2sexp [Sym s])
              fake_ftbl_entries` by
     (SIMP_TAC std_ss [fake_ftbl_entries_def,EVERY_DEF]
      \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [milawa_initTheory.init_ftbl_def]
      \\ REWRITE_TAC [lookup_safe_lemma3,CONS_11,NOT_CONS_NIL,NOT_NIL_CONS]
      \\ SIMP_TAC (srw_ss()) [list2sexp_def])
    \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
    \\ MP_TAC (Q.INST [`ok`|->`T`,`io`|->`ARB`] milawa_initTheory.milawa_init_evaluated)
    \\ SIMP_TAC std_ss [milawa_initTheory.milawa_init_def,GSYM ftbl_prop_def]
    \\ Q.PAT_ABBREV_TAC `pat = Dot x y`
    \\ `ftbl_prop pat init_fns` by
     (Q.UNABBREV_TAC `pat` \\ SIMP_TAC std_ss [ftbl_prop_def]
      \\ SIMP_TAC std_ss [sexp2list_def,EVERY_DEF,isDot_def,CDR_def,isTrue_def]
      \\ EVAL_TAC)
    \\ REPEAT STRIP_TAC \\ IMP_RES_TAC ftbl_prop_MAINTAINED \\ METIS_TAC [])
  THEN1
   (SIMP_TAC (srw_ss()) [axioms_inv_def]
    \\ SIMP_TAC std_ss [func_definition_exists_def,FDOM_FEMPTY,NOT_IN_EMPTY]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [logic_func_inv_def,axioms_aux_def]
    \\ Q.EXISTS_TAC `raw_body` \\ SIMP_TAC std_ss []
    \\ STRIP_TAC THEN1
     (REWRITE_TAC [milawa_initTheory.init_ftbl_def,sexp2list_def,list2sexp_def,MEM]
      \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
      \\ REWRITE_TAC [MEM] \\ STRIP_TAC
      \\ ASM_REWRITE_TAC [SExp_11,CONS_11,NOT_CONS_NIL,NOT_NIL_CONS]
      \\ SIMP_TAC (srw_ss()) []
      \\ REWRITE_TAC [milawa_initTheory.init_ftbl_def,lookup_safe_lemma3]
      \\ ASM_REWRITE_TAC [SExp_11,CONS_11,NOT_CONS_NIL,NOT_NIL_CONS]
      \\ SIMP_TAC (srw_ss()) [list2sexp_def])
    \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC std_ss [MEM]
    \\ REWRITE_TAC [milawa_initTheory.init_ftbl_def,lookup_safe_lemma3,
        NOT_CONS_NIL,NOT_NIL_CONS,CONS_11]
    \\ SIMP_TAC (srw_ss()) []
    \\ FS [] \\ SIMP_TAC (srw_ss()) []
    \\ Cases_on `params`
    \\ TRY (Cases_on `t`) \\ FS [MAP]
    \\ TRY (Cases_on `t`) \\ FS [MAP]
    \\ TRY (Cases_on `t'`) \\ FS [MAP]
    \\ SIMP_TAC std_ss [def_axiom_def]
    \\ REPEAT STRIP_TAC
    \\ EVAL_TAC)
  THEN1
   (SIMP_TAC std_ss [atbl_ftbl_inv_def]
    \\ REWRITE_TAC [core_initial_atbl_def,logic_initial_arity_table_def]
    \\ FULL_SIMP_TAC std_ss [GSYM list2sexp_def,app_thm,APPEND]
    \\ SIMP_TAC std_ss [list2sexp_def,GSYM alist2sexp_def]
    \\ SIMP_TAC std_ss [lookup_thm,LOOKUP_DOT_def,SExp_11]
    \\ SRW_TAC [] []
    \\ REWRITE_TAC [milawa_initTheory.init_ftbl_def,sexp2list_def,MEM,MAP,CAR_def]
    \\ FS [])
  THEN1
   (SIMP_TAC std_ss [runtime_inv_def,FDOM_FEMPTY,NOT_IN_EMPTY])
  THEN1
   (SIMP_TAC std_ss [milawa_initTheory.core_assum_thm]));


(* relating the above results to the main routine *)

val define_safe_list_side_tm =
  milawa_initTheory.define_safe_list_side_def
  |> SPEC_ALL |> concl |> dest_eq |> fst |> find_term is_const

val define_safe_list_side_thm = prove(
  ``!defs ftbl k io ok.
       ^define_safe_list_side_tm ftbl defs k io ok = T``,
  REVERSE Induct \\ SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [milawa_initTheory.define_safe_list_side_def] \\ FS []
  \\ FULL_SIMP_TAC std_ss [LET_DEF,milawa_initTheory.define_safe_side_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ SIMP_TAC std_ss []);

val milawa_init_side_thm = prove(
  ``milawa_init_side init_fns "NIL\nNIL\nNIL\nNIL\nNIL\n" T``,
  SIMP_TAC std_ss [milawa_initTheory.milawa_init_side_def]
  \\ SIMP_TAC std_ss [define_safe_list_side_thm]);

val compute_output_def = Define `
  compute_output cmds =
    [(FEMPTY,"NIL");(FEMPTY,"NIL");(FEMPTY,"NIL");(FEMPTY,"NIL");(FEMPTY,"NIL")] ++
    milawa_commands FEMPTY 1 cmds`;

val milawa_main_thm = prove(
  ``?ans k io ok.
      milawa_main_side cmds init_fns "NIL\nNIL\nNIL\nNIL\nNIL\n" T /\
      (milawa_main cmds init_fns "NIL\nNIL\nNIL\nNIL\nNIL\n" T = (ans,k,io,ok)) /\
      (ok ==> (ans = Sym "SUCCESS") /\
              let output = compute_output cmds in
                EVERY line_ok output /\ (io = output_to_string output))``,
  SIMP_TAC std_ss [milawa_main_def,milawa_main_side_def,LET_DEF]
  \\ SIMP_TAC std_ss [milawa_initTheory.milawa_init_evaluated]
  \\ STRIP_ASSUME_TAC init_thm \\ FULL_SIMP_TAC std_ss []
  \\ MP_TAC (core_accept_commands_thm
       |> Q.SPECL [`cmds`,`1`,`result`,`core_funs`,`"NIL\nNIL\nNIL\nNIL\nNIL\n"`,`T`,`FEMPTY`,`FEMPTY`])
  \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [milawa_initTheory.core_assum_thm]
  \\ FULL_SIMP_TAC std_ss [milawa_init_side_thm]
  \\ STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [isDot_thm,isTrue_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,compute_output_def,EVERY_DEF,EVERY_APPEND]
  \\ FS [line_ok_def] \\ FS [APPEND,output_to_string_def]);


(* overall soundness theorem *)

val milawa_main_soundness = store_thm("milawa_main_soundness",
  ``(read_sexps rest =
      [Dot (Sym "MILAWA-MAIN")
         (Dot (Dot (Sym "QUOTE") (Dot cmds (Sym "NIL"))) (Sym "NIL"))]) ==>
    ?io ok.
      R_exec (STRCAT MILAWA_CORE_TEXT rest,FEMPTY,"") (io,ok) /\
      (ok ==> let output = compute_output cmds in
                EVERY line_ok output /\
                (io = output_to_string output ++ "SUCCESS\n"))``,
  REPEAT STRIP_TAC \\ STRIP_ASSUME_TAC milawa_main_thm
  \\ IMP_RES_TAC (SIMP_RULE std_ss [milawa_initTheory.init_assum_thm]
       (Q.INST [`k`|->`init_fns`] R_ev_milawa_main))
  \\ POP_ASSUM (MP_TAC o Q.SPEC `FEMPTY`) \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (milawa_initTheory.milawa_init_expanded
        |> Q.INST [`io1`|->`""`] |> SIMP_RULE std_ss [APPEND])
  \\ Q.LIST_EXISTS_TAC [`STRCAT (STRCAT io (sexp2string ans)) "\n"`,`ok`]
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ SIMP_TAC std_ss [EVAL ``sexp2string (Sym "SUCCESS")``]
  \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]);


val _ = export_theory();
