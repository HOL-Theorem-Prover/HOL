
open HolKernel Parse boolLib bossLib; val _ = new_theory "milawa_ordinal";

open lisp_sexpTheory arithmeticTheory pred_setTheory ordinalNotationTheory;

val RW = REWRITE_RULE


val ORD_LT_def = tDefine "ORD_LT" `
  ORD_LT x y =
    if ~(isDot x) then
      (if isDot y then T else getVal x < getVal y)
    else if ~(isDot y) then
      F
    else if ~((CAR (CAR x)) = (CAR (CAR y))) then
      ORD_LT (CAR (CAR x))
             (CAR (CAR y))
    else if ~((CDR (CAR x)) = (CDR (CAR y))) then
      getVal (CDR (CAR x)) <
      getVal (CDR (CAR y))
    else
      ORD_LT (CDR x)
             (CDR y)`
 (WF_REL_TAC `measure (LSIZE o FST)`
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [isDot_thm] \\ Cases_on `a`
  \\ FULL_SIMP_TAC std_ss [CAR_def,CDR_def,LSIZE_def] \\ DECIDE_TAC);

val ORDP_def = tDefine "ORDP" `
  ORDP x =
    if ~(isDot x) then isVal x else
      isDot (CAR x) /\
      ORDP (CAR (CAR x)) /\
      ~((CAR (CAR x)) = Val 0) /\
      (0 < getVal (CDR (CAR x))) /\
      ORDP (CDR x) /\
      (if isDot (CDR x) then
         ORD_LT (CAR (CAR (CDR x)))
                (CAR (CAR x))
       else T)`
 (WF_REL_TAC `measure LSIZE`
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [isDot_thm] \\ Cases_on `a`
  \\ FULL_SIMP_TAC std_ss [CAR_def,CDR_def,LSIZE_def] \\ DECIDE_TAC);

val ORD_LESS_def = Define `
  ORD_LESS x y = ORDP x /\ ORDP y /\ ORD_LT x y`;

val ord2sexp_def = Define `
  (ord2sexp (End n) = Val n) /\
  (ord2sexp (Plus x n y) = Dot (Dot (ord2sexp x) (Val n)) (ord2sexp y))`;

val NOT_ord2sexp_Val_0 = prove(
  ``!x. ~(ord2sexp x = Val 0) = ~(x = End 0)``,
  Cases \\ SIMP_TAC (srw_ss()) [ord2sexp_def]);

val ORD_LT_IRREFL = prove(
  ``!x. ~(ORD_LT x x)``,
  REVERSE Induct
  \\ SIMP_TAC std_ss [Once ORDP_def,isDot_def,isVal_def,Once ORD_LT_def]
  \\ SIMP_TAC std_ss [CAR_def,CDR_def]
  \\ STRIP_TAC
  \\ SIMP_TAC std_ss [Once ORD_LT_def,isDot_def,CDR_def,CAR_def]
  \\ FULL_SIMP_TAC std_ss []);

val oless_IMP_ORD_LT = prove(
  ``!x y. oless x y ==> ORD_LT (ord2sexp x) (ord2sexp y)``,
  HO_MATCH_MP_TAC oless_ind \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [ord2sexp_def] \\ ONCE_REWRITE_TAC [ORD_LT_def]
  \\ ASM_SIMP_TAC (srw_ss()) [isDot_def,getVal_def,CAR_def,CDR_def,
       DECIDE ``n<m ==> ~(n=m:num)``]
  \\ Cases_on `ord2sexp x = ord2sexp y` \\ FULL_SIMP_TAC std_ss [ORD_LT_IRREFL]);

val ord_size_def = Define `
  (ord_size (End k) = 0:num) /\
  (ord_size (Plus x n y) = 1 + ord_size x + ord_size y)`;

val sexp2ord_def = tDefine "sexp2ord" `
  sexp2ord x = if ~(isDot x) then End (getVal x) else
                 Plus (sexp2ord (CAR (CAR x))) (getVal (CDR (CAR x)))
                      (sexp2ord (CDR x))`
 (WF_REL_TAC `measure LSIZE`
  \\ REPEAT STRIP_TAC \\ Cases_on `x` \\ REPEAT (Cases_on `S'`)
  \\ FULL_SIMP_TAC std_ss [isDot_def,CAR_def,CDR_def,LSIZE_def] \\ DECIDE_TAC);

val PULL_FORALL_IMP = METIS_PROVE [] ``(p ==> !x. q x) = !x. p ==> q x``;

val oless_IRREFL = prove(
  ``!x. ~(oless x x)``,
  Induct \\ ONCE_REWRITE_TAC [oless_cases] \\ ASM_SIMP_TAC (srw_ss()) []);

val ord2sexp_11 = prove(
  ``!x y. (ord2sexp x = ord2sexp y) ==> (x = y)``,
  Induct \\ Cases_on `y` \\ FULL_SIMP_TAC (srw_ss()) [ord2sexp_def]);

val ORD_LT_IMP_oless = prove(
  ``!x y. ORD_LT (ord2sexp x) (ord2sexp y) ==> oless x y``,
  completeInduct_on `ord_size x + ord_size y` \\ REPEAT STRIP_TAC
  \\ Cases_on `x` \\ Cases_on `y` \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [ord2sexp_def]
  \\ ONCE_REWRITE_TAC [oless_cases,ORD_LT_def]
  \\ FULL_SIMP_TAC (srw_ss()) [isDot_def,getVal_def,CAR_def,CDR_def]
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL_IMP]
  \\ Cases_on `o'' = o'` \\ FULL_SIMP_TAC std_ss [] THEN1
   (Cases_on `n' = n` \\ FULL_SIMP_TAC std_ss [oless_IRREFL]
    \\ Q.PAT_ASSUM `!x.bbb` MATCH_MP_TAC
    \\ FULL_SIMP_TAC std_ss [ord_size_def] \\ DECIDE_TAC)
  \\ `ord2sexp o' <> ord2sexp o''` by METIS_TAC [ord2sexp_11]
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `!x.bbb` MATCH_MP_TAC
  \\ FULL_SIMP_TAC std_ss [ord_size_def] \\ DECIDE_TAC);

val oless_EQ_ord2sexp = prove(
  ``!x y. oless x y = ORD_LT (ord2sexp x) (ord2sexp y)``,
  METIS_TAC [oless_IMP_ORD_LT,ORD_LT_IMP_oless]);

val is_ord_EQ_ORDP = prove(
  ``!x. is_ord x = ORDP (ord2sexp x)``,
  Induct THEN1
   (ONCE_REWRITE_TAC [is_ord_cases,ORDP_def] \\ SIMP_TAC (srw_ss()) []
    \\ SIMP_TAC std_ss [ord2sexp_def,isDot_def,isVal_def])
  \\ ONCE_REWRITE_TAC [is_ord_cases,ORDP_def]
  \\ ASM_SIMP_TAC (srw_ss()) [ord2sexp_def,isDot_def,CAR_def,CDR_def,getVal_def]
  \\ ASM_SIMP_TAC std_ss [NOT_ord2sexp_Val_0,oless_EQ_ord2sexp] \\ STRIP_TAC
  \\ Cases_on `ORDP (ord2sexp x) /\ x <> End 0 /\ 0 < n /\ ORDP (ord2sexp x')`
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `x'` THEN1
   (SIMP_TAC std_ss [ord2sexp_def,CAR_def,CDR_def,isDot_def,expt_def]
    \\ Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) [ord2sexp_def]
    \\ ONCE_REWRITE_TAC [ORD_LT_def]
    \\ FULL_SIMP_TAC std_ss [isDot_def,getVal_def] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [ord2sexp_def,CAR_def,CDR_def,expt_def,isDot_def]);

val ord2sexp_sexp2ord = prove(
  ``!x. ORDP x ==> (ord2sexp (sexp2ord x) = x)``,
  completeInduct_on `LSIZE x` \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL_IMP]
  \\ POP_ASSUM MP_TAC
  \\ REVERSE (Cases_on `x`)
  \\ ONCE_REWRITE_TAC [ORDP_def]
  \\ FULL_SIMP_TAC std_ss [isDot_def,isVal_def]
  \\ ONCE_REWRITE_TAC [sexp2ord_def]
  \\ FULL_SIMP_TAC std_ss [ord2sexp_def,isDot_def,getVal_def,CAR_def,CDR_def]
  \\ Cases_on `S'`
  \\ FULL_SIMP_TAC std_ss [ord2sexp_def,isDot_def,getVal_def,CAR_def,CDR_def]
  \\ Cases_on `S0'` \\ SIMP_TAC (srw_ss()) [getVal_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
  \\ Q.PAT_ASSUM `!x. bbb` MATCH_MP_TAC
  \\ ASM_SIMP_TAC std_ss [LSIZE_def] \\ DECIDE_TAC);

val WF_ORD_LESS = store_thm("WF_ORD_LESS",
  ``WF ORD_LESS``,
  ASSUME_TAC WF_ord_less
  \\ FULL_SIMP_TAC std_ss [prim_recTheory.WF_IFF_WELLFOUNDED,
       prim_recTheory.wellfounded_def,ord_less_def,is_ord_EQ_ORDP,oless_EQ_ord2sexp]
  \\ FULL_SIMP_TAC std_ss [ORD_LESS_def] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`sexp2ord o f`])
  \\ FULL_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `n`
  \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [ord2sexp_sexp2ord]);

val _ = export_theory();
