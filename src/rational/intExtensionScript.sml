(***************************************************************************
 *
 *  intExtensionScript.sml
 *
 *  extension of the theory of integers
 *  Jens Brandt
 *
 ***************************************************************************)

open HolKernel boolLib Parse bossLib;

open arithmeticTheory pairTheory integerTheory intLib
        EVAL_ringTheory EVAL_ringLib integerRingLib
        schneiderUtils;

val _ = new_theory "intExtension";

(*--------------------------------------------------------------------------*
   operations
 *--------------------------------------------------------------------------*)

Definition SGN_def:
  SGN x = if x = 0i then 0i else if x < 0i then ~1 else 1i
End

(*--------------------------------------------------------------------------
   INT_SGN_TOTAL : thm
   |- !a. (SGN a = ~1) \/ (SGN a = 0) \/ (SGN a = 1)
 *--------------------------------------------------------------------------*)

Theorem INT_SGN_TOTAL: !a. (SGN a = ~1) \/ (SGN a = 0) \/ (SGN a = 1)
Proof
  RW_TAC int_ss[SGN_def]
QED

Theorem INT_SGN_CASES:
  !a P. (SGN a = ~1 /\ a < 0 ==> P) /\ (SGN a = 0i /\ a = 0 ==> P) /\
        (SGN a = 1i /\ 0 < a ==> P) ==> P
Proof
  rw[] >> qspec_then ‘a’ strip_assume_tac INT_SGN_TOTAL >> gvs[] >>
  gvs[SGN_def,AllCaseEqs()] >> metis_tac[INT_LT_TOTAL]
QED

(*--------------------------------------------------------------------------
   linking ABS and SGN: |- ABS x = x * SGN x, |- ABS x * SGN x = x
 *--------------------------------------------------------------------------*)

Theorem ABS_EQ_MUL_SGN: ABS x = x * SGN x
Proof
  rw[SGN_def, INT_ABS, GSYM INT_NEG_RMUL]
QED

Theorem MUL_ABS_SGN: ABS x * SGN x = x
Proof
  rw[INT_ABS, SGN_def]
QED

Theorem ABS_SGN:
  ABS (SGN i) = if i = 0 then 0 else 1
Proof
  Cases_on `i` >> gvs[SGN_def]
QED

Theorem SGN_MUL_Num[simp]:
  SGN i * &Num i = i
Proof
  Cases_on `i` >> gvs[SGN_def] >>
  simp[INT_MUL_CALCULATE]
QED

(*--------------------------------------------------------------------------
   INT_MUL_POS_SIGN: thm
   |- !a b. 0 < a ==> 0 < b ==> 0 < a * b
 *--------------------------------------------------------------------------*)

Theorem INT_MUL_POS_SIGN: !a:int b:int. 0 < a ==> 0 < b ==> 0i < a * b
Proof
  rw[INT_MUL_SIGN_CASES]
QED

(*--------------------------------------------------------------------------
   INT_NE_IMP_LTGT: thm
   |- !x. ~(x = 0) = (0 < x) \/ (x < 0)
 *--------------------------------------------------------------------------*)

Theorem INT_NE_IMP_LTGT: !x:int. x <> 0 <=> 0 < x \/ x < 0
Proof
  metis_tac[INT_LT_TOTAL, INT_LT_REFL]
QED

(*--------------------------------------------------------------------------
   INT_NOTGT_IMP_EQLT : thm
   |- !n. ~(n < 0) = (0 = n) \/ 0 < n
 *--------------------------------------------------------------------------*)

Theorem INT_NOTGT_IMP_EQLT: !n:int. ~(n < 0) <=> (0 = n) \/ 0 < n
Proof
  metis_tac[INT_LT_TOTAL, INT_LT_REFL, INT_LT_TRANS]
QED

(*--------------------------------------------------------------------------
   INT_NOTPOS0_NEG : thm
   |- !a. ~(0 < a) ==> ~(a = 0) ==> 0 < ~a
 *--------------------------------------------------------------------------*)

val INT_NOTPOS0_NEG = store_thm("INT_NOTPOS0_NEG", ``!a. ~(0i<a) ==> ~(a=0i) ==> 0i<~a``,
        REPEAT STRIP_TAC THEN
        ONCE_REWRITE_TAC[GSYM INT_NEG_0] THEN
        REWRITE_TAC[INT_LT_NEG] THEN
        PROVE_TAC[INT_LT_TOTAL] );

(*--------------------------------------------------------------------------
   INT_NOT0_MUL : thm
   |- !a b. ~(a = 0) ==> ~(b = 0) ==> ~(a * b = 0)
 *--------------------------------------------------------------------------*)

Theorem INT_NOT0_MUL: !a b. ~(a=0i) ==> ~(b=0i) ==> ~(a*b=0i)
Proof
  PROVE_TAC[INT_ENTIRE]
QED

(*--------------------------------------------------------------------------
   INT_GT0_IMP_NOT0 : thm
   |- !a. 0 < a ==> ~(a = 0)
 *--------------------------------------------------------------------------*)

Theorem INT_GT0_IMP_NOT0: !a. 0i<a ==> ~(a=0i)
Proof
        REPEAT STRIP_TAC THEN
        ASM_CASES_TAC ``a = 0i`` THEN
        ASM_CASES_TAC ``a < 0i`` THEN
        PROVE_TAC[INT_LT_ANTISYM,INT_LT_TOTAL]
QED

(*--------------------------------------------------------------------------
   INT_NOTLTEQ_GT : thm
   |- !a. ~(a < 0) ==> ~(a = 0) ==> 0 < a
 *--------------------------------------------------------------------------*)

Theorem INT_NOTLTEQ_GT: !a:int. ~(a<0i) ==> a <> 0 ==> 0 < a
Proof
        PROVE_TAC[INT_LT_TOTAL]
QED

(*--------------------------------------------------------------------------
   INT_ABS_NOT0POS : thm
   |- !x. ~(x = 0) ==> 0 < ABS x
 *--------------------------------------------------------------------------*)

Theorem INT_ABS_NOT0POS = iffRL INT_ABS_0LT |> GEN_ALL

(*--------------------------------------------------------------------------
   INT_SGN_NOTPOSNEG : thm
   |- !x. ~(SGN x = ~1) ==> ~(SGN x = 1) ==> (SGN x = 0)
 *--------------------------------------------------------------------------*)

Theorem INT_SGN_NOTPOSNEG: !x. ~(SGN x = ~1) ==> ~(SGN x = 1) ==> (SGN x = 0)
Proof
  rw[SGN_def]
QED

(*--------------------------------------------------------------------------
   LESS_IMP_NOT_0 : thm
   |- !n. 0 < n ==> ~(n = 0)
 *--------------------------------------------------------------------------*)

val LESS_IMP_NOT_0 = store_thm("LESS_IMP_NOT_0", ``!n:int. 0i<n ==> ~(n=0i)``,
        GEN_TAC THEN
        ASM_CASES_TAC ``n=0i``
        THEN RW_TAC int_ss[] );

(*--------------------------------------------------------------------------
 *  INT_EQ_RMUL_EXP : thm
 *  |- !a b n. 0<n ==> ((a=b) = (a*n=b*n))
 *--------------------------------------------------------------------------*)

val INT_EQ_RMUL_EXP = store_thm("INT_EQ_RMUL_EXP", ``!a:int b:int n:int. 0<n ==> ((a=b) = (a*n=b*n))``,
        REPEAT STRIP_TAC
        THEN EQ_TAC
        THEN ASSUME_TAC (prove(``0i<n ==> ~(n=0i)``, ASM_CASES_TAC ``n=0i`` THEN RW_TAC int_ss[]))
        THEN ASSUME_TAC (SPEC ``n:int`` (SPEC ``b:int`` (SPEC ``a:int`` INT_EQ_RMUL_IMP)))
        THEN RW_TAC int_ss[] );

(*--------------------------------------------------------------------------
   INT_LT_RMUL_EXP : thm
   |- !a b n. !a b n. 0 < n ==> ((a < b) = (a * n < b * n))
 *--------------------------------------------------------------------------*)

val INT_LT_RMUL_EXP = store_thm("INT_LT_RMUL_EXP", ``!a:int b:int n:int. 0<n ==> ((a<b) = (a*n<b*n))``,
        REPEAT STRIP_TAC THEN
        ASSUME_TAC (UNDISCH_ALL (GSYM (SPEC ``b:int`` (SPEC ``a:int`` (SPEC ``n:int`` INT_LT_MONO))))) THEN
        RW_TAC int_ss[INT_MUL_SYM] );

(*--------------------------------------------------------------------------
   INT_GT_RMUL_EXP : thm
   |- !a b n. 0 < n ==> ((a > b) = (a * n > b * n))
 *--------------------------------------------------------------------------*)

val INT_GT_RMUL_EXP = store_thm("INT_GT_RMUL_EXP", ``!a:int b:int n:int. 0<n ==> ((a>b) = (a*n>b*n))``,
        REPEAT STRIP_TAC THEN
        REWRITE_TAC[int_gt] THEN
        ASSUME_TAC (UNDISCH_ALL (GSYM (SPEC ``a:int`` (SPEC ``b:int`` (SPEC ``n:int`` INT_LT_MONO))))) THEN
        RW_TAC int_ss[INT_MUL_SYM] );

(*--------------------------------------------------------------------------
   INT_ABS_CALCULATE_NEG : thm
   |- !a. a<0 ==> (ABS(a) = ~a)
 *--------------------------------------------------------------------------*)

val INT_ABS_CALCULATE_NEG = store_thm("INT_ABS_CALCULATE_NEG", ``!a. a<0 ==> (ABS(a) = ~a)``,
        GEN_TAC THEN
        STRIP_TAC THEN
        RW_TAC int_ss[INT_ABS] );

(*--------------------------------------------------------------------------
   INT_ABS_CALCULATE_0 : thm
   |- ABS 0i = 0i
 *--------------------------------------------------------------------------*)

val INT_ABS_CALCULATE_0 = store_thm("INT_ABS_CALCULATE_0", ``ABS 0i = 0i``,
        RW_TAC int_ss[INT_ABS] );

Theorem INT_ABS_CALCULATE_POS: !a. 0<a ==> (ABS(a) = a)
Proof
  RW_TAC int_ss[INT_ABS, INT_LT_GT]
QED

(*--------------------------------------------------------------------------
   INT_NOT0_SGNNOT0 : thm
   |- !x. ~(x = 0) ==> ~(SGN x = 0)
 *--------------------------------------------------------------------------*)

Theorem INT_NOT0_SGNNOT0:
  !x. ~(x = 0) ==> ~(SGN x = 0)
Proof
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPEC ``x:int`` INT_SGN_CASES) THEN
  REPEAT CONJ_TAC THEN
  STRIP_TAC  THEN
  RW_TAC intLib.int_ss []
QED

Theorem INT_SGN_CLAUSES:
  !x. (SGN x = ~1 <=> x < 0) /\ (SGN x = 0i <=> x = 0) /\
      (SGN x = 1i <=> 0 < x)
Proof
  GEN_TAC >> qspec_then ‘x’ strip_assume_tac INT_SGN_CASES >>
  rpt conj_tac >> pop_assum irule >> simp[] >>
  metis_tac[INT_LT_TRANS, INT_LT_REFL]
QED

Theorem INT_SGN_MUL2: !x y. SGN (x * y) = SGN x * SGN y
Proof
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SGN_def] THEN
  RW_TAC int_ss[] THEN
  UNDISCH_ALL_TAC THEN
  RW_TAC int_ss[INT_MUL_LZERO, INT_MUL_RZERO] THEN
  PROVE_TAC[INT_ENTIRE, INT_MUL_SIGN_CASES, INT_LT_ANTISYM, INT_LT_TOTAL]
QED

(*--------------------------------------------------------------------------
   INT_LT_ADD_NEG : thm
   |- !x y. x < 0i /\ y < 0i ==> x + y < 0i
 *--------------------------------------------------------------------------*)

Theorem INT_LT_ADD_NEG: !x y. x < 0i /\ y < 0i ==> x + y < 0i
Proof
        REWRITE_TAC[GSYM INT_NEG_GT0, INT_NEG_ADD] THEN
        PROVE_TAC[INT_LT_ADD]
QED


val _ = export_theory();
