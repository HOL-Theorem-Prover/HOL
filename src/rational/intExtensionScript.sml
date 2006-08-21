(***************************************************************************
 *
 *  intExtensionScript.sml
 *
 *  extension of the theory of integers
 *  Jens Brandt
 *
 ***************************************************************************)

open HolKernel boolLib Parse bossLib;

(* interactive mode
app load ["integerTheory","intLib",
"ringLib", "pairTheory",
	"integerRingTheory","integerRingLib",
	"schneiderUtils"];
*)
open
	arithmeticTheory pairTheory
	integerTheory intLib
	ringTheory ringLib integerRingLib
	schneiderUtils;

val _ = new_theory "intExtension";

(*--------------------------------------------------------------------------*
   operations
 *--------------------------------------------------------------------------*)

val SGN_def = Define `SGN x = (if x = 0i then 0i else (if x < 0i then ~1 else 1i))`;

(*--------------------------------------------------------------------------
   INT_MUL_POS_SIGN: thm
   |- !a b. 0 < a ==> 0 < b ==> 0 < a * b
 *--------------------------------------------------------------------------*)

val INT_MUL_POS_SIGN =
let
	val lemma01 = #2 (EQ_IMP_RULE (CONJUNCT1 (SPEC_ALL INT_MUL_SIGN_CASES)));
in
	store_thm("INT_MUL_POS_SIGN", ``!a:int b:int. 0i<a ==> 0i<b ==> 0i<a * b``, RW_TAC int_ss[lemma01])
end;

(*--------------------------------------------------------------------------
   INT_NE_IMP_LTGT: thm
   |- !x. ~(x = 0) = (0 < x) \/ (x < 0)
 *--------------------------------------------------------------------------*)

val INT_NE_IMP_LTGT = store_thm("INT_NE_IMP_LTGT", ``!x. ~(x=0i) = (0i<x) \/ (x<0i)``,
	GEN_TAC THEN
	EQ_TAC THENL
	[
		REWRITE_TAC[IMP_DISJ_THM] THEN
		PROVE_TAC[INT_LT_TOTAL]
	,
		PROVE_TAC[INT_LT_IMP_NE]
	] );

(*--------------------------------------------------------------------------
   INT_NOTGT_IMP_EQLT : thm
   |- !n. ~(n < 0) = (0 = n) \/ 0 < n
 *--------------------------------------------------------------------------*)

val  INT_NOTGT_IMP_EQLT = store_thm("INT_NOTGT_IMP_EQLT",``!n. ~(n < 0i) = (0i = n) \/ 0i < n``,
	GEN_TAC THEN
	EQ_TAC THEN
	STRIP_TAC THENL
	[
		LEFT_DISJ_TAC THEN
		PROVE_TAC[INT_LT_TOTAL]
	,
		PROVE_TAC[INT_LT_IMP_NE]
	,
		PROVE_TAC[INT_LT_GT]
	] );

(*--------------------------------------------------------------------------
   INT_NO_ZERODIV : thm
   |- !x y. (x = 0) \/ (y = 0) = (x * y = 0)
 *--------------------------------------------------------------------------*)

val INT_NO_ZERODIV = store_thm("INT_NO_ZERODIV", ``!x y. (x = 0i) \/ (y = 0i) = (x * y = 0i)``,
	REPEAT GEN_TAC THEN
	ASM_CASES_TAC ``x=0i`` THEN
	ASM_CASES_TAC ``y=0i`` THEN
	RW_TAC int_ss[INT_MUL_LZERO, INT_MUL_RZERO] THEN
	REWRITE_TAC[INT_NE_IMP_LTGT] THEN
	REWRITE_TAC[INT_MUL_SIGN_CASES] THEN
	PROVE_TAC[INT_LT_TOTAL] );

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

val INT_NOT0_MUL = store_thm("INT_NOT0_MUL", ``!a b. ~(a=0i) ==> ~(b=0i) ==> ~(a*b=0i)``,
	PROVE_TAC[INT_NO_ZERODIV] );

(*--------------------------------------------------------------------------
   INT_GT0_IMP_NOT0 : thm
   |- !a. 0 < a ==> ~(a = 0)
 *--------------------------------------------------------------------------*)

val INT_GT0_IMP_NOT0 = store_thm("INT_GT0_IMP_NOT0",``!a. 0i<a ==> ~(a=0i)``,
	REPEAT STRIP_TAC THEN
	ASM_CASES_TAC ``a = 0i`` THEN
	ASM_CASES_TAC ``a < 0i`` THEN
	PROVE_TAC[INT_LT_ANTISYM,INT_LT_TOTAL] );

(*--------------------------------------------------------------------------
   INT_NOTLTEQ_GT : thm
   |- !a. ~(a < 0) ==> ~(a = 0) ==> 0 < a
 *--------------------------------------------------------------------------*)

val INT_NOTLTEQ_GT = store_thm("INT_NOTLTEQ_GT", ``!a. ~(a<0i) ==> ~(a=0i) ==> 0i<a``,
	REPEAT STRIP_TAC THEN
	PROVE_TAC[INT_LT_TOTAL] );

(*--------------------------------------------------------------------------
   INT_ABS_NOT0POS : thm
   |- !x. ~(x = 0) ==> 0 < ABS x
 *--------------------------------------------------------------------------*)

val INT_ABS_NOT0POS = store_thm("INT_ABS_NOT0POS", ``!x:int. ~(x = 0i) ==> 0i < ABS x``,
	REPEAT STRIP_TAC THEN
	REWRITE_TAC[INT_ABS] THEN
	ASM_CASES_TAC ``x<0i`` THENL
	[
		RW_TAC int_ss[] THEN
		ONCE_REWRITE_TAC[GSYM INT_NEG_0] THEN
		REWRITE_TAC[INT_LT_NEG] THEN
		PROVE_TAC[]
	,
		RW_TAC int_ss[] THEN
		UNDISCH_TAC ``~(x < 0i)`` THEN
		UNDISCH_TAC ``~(x = 0i)`` THEN
		REWRITE_TAC[IMP_DISJ_THM] THEN
		PROVE_TAC[INT_LT_TOTAL]
	]);

(*--------------------------------------------------------------------------
   INT_SGN_NOTPOSNEG : thm
   |- !x. ~(SGN x = ~1) ==> ~(SGN x = 1) ==> (SGN x = 0)
 *--------------------------------------------------------------------------*)

val INT_SGN_NOTPOSNEG = store_thm("INT_SGN_NOTPOSNEG", ``!x. ~(SGN x = ~1) ==> ~(SGN x = 1) ==> (SGN x = 0)``,
	GEN_TAC THEN
	REWRITE_TAC[SGN_def] THEN
	RW_TAC int_ss[] );

(*--------------------------------------------------------------------------
   INT_SGN_CASES : thm
   |- !x P.
 	((SGN x=~1) /\ (x<0) ==> P) /\
 	((SGN x=0i) /\ (x=0) ==> P) /\
 	((SGN x=1i) /\ (0<x) ==> P) ==> P
 *--------------------------------------------------------------------------*)

val INT_SGN_CASES = store_thm("INT_SGN_CASES", ``!x P. ((SGN x=~1) /\ (x<0) ==> P) /\ ((SGN x=0i) /\ (x=0) ==> P) /\ ((SGN x=1i) /\ (0<x) ==> P) ==> P``,
	REPEAT GEN_TAC THEN
	ASM_CASES_TAC ``(SGN x=~1) /\ (x<0)`` THEN
	UNDISCH_HD_TAC THEN
	ASM_CASES_TAC ``(SGN x=1i) /\ (0<x)`` THEN
	UNDISCH_HD_TAC THEN
	REWRITE_TAC[SGN_def] THEN
	REWRITE_TAC[DE_MORGAN_THM] THEN
	RW_TAC int_ss[] THEN
	PROVE_TAC[INT_LT_TOTAL, INT_SGN_NOTPOSNEG] );

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

(*--------------------------------------------------------------------------
   INT_ABS_CALCULATE_POS : thm
   |- !a. 0<a ==> (ABS(a) = a)
 *--------------------------------------------------------------------------*)

val INT_ABS_CALCULATE_POS = store_thm("INT_ABS_CALCULATE_POS", ``!a. 0<a ==> (ABS(a) = a)``,
	GEN_TAC THEN
	STRIP_TAC THEN
	RW_TAC int_ss[INT_ABS, INT_LT_GT] );

(*--------------------------------------------------------------------------
   INT_NOT0_SGNNOT0 : thm
   |- !x. ~(x = 0) ==> ~(SGN x = 0)
 *--------------------------------------------------------------------------*)

val INT_NOT0_SGNNOT0 = store_thm("INT_NOT0_SGNNOT0", ``!x. ~(x = 0) ==> ~(SGN x = 0)``,
	REPEAT GEN_TAC THEN
	STRIP_TAC THEN
	MATCH_MP_TAC (SPEC ``x:int`` INT_SGN_CASES) THEN
	REPEAT CONJ_TAC THEN
	STRIP_TAC  THEN
	RW_TAC intLib.int_ss [] );

(*--------------------------------------------------------------------------
   INT_SGN_CLAUSES : thm
   |- !x. (SGN x = ~1) =
          (x < 0)) /\ ((SGN x = 0i) = (x = 0)) /\ ((SGN x = 1i) = (x > 0)
 *--------------------------------------------------------------------------*)

val INT_SGN_CLAUSES = store_thm("INT_SGN_CLAUSES", ``!x. ((SGN x = ~1) = (x < 0)) /\ ((SGN x = 0i) = (x = 0)) /\ ((SGN x = 1i) = (x > 0))``,
	GEN_TAC THEN
	RW_TAC int_ss[SGN_def] THEN
	REWRITE_TAC[int_gt] THEN
	PROVE_TAC[INT_LT_GT, INT_LT_TOTAL] );

(*--------------------------------------------------------------------------
   INT_SGN_MUL : thm
   |- !x1 x2 y1 y2. (SGN x1 = y1) ==> (SGN x2 = y2) ==>
                    (SGN (x1 * x2) = y1 * y2)
 *--------------------------------------------------------------------------*)

val INT_SGN_MUL = store_thm("INT_SGN_MUL", ``!x1 x2 y1 y2. (SGN x1 = y1) ==> (SGN x2 = y2) ==> (SGN (x1 * x2) = y1 * y2)``,
	REPEAT GEN_TAC THEN
	REWRITE_TAC[SGN_def] THEN
	RW_TAC int_ss[] THEN
	UNDISCH_ALL_TAC THEN
	RW_TAC int_ss[INT_MUL_LZERO, INT_MUL_RZERO] THEN
	PROVE_TAC[INT_NO_ZERODIV, INT_MUL_SIGN_CASES, INT_LT_ANTISYM, INT_LT_TOTAL] );

(*--------------------------------------------------------------------------
   INT_SGN_MUL2 : thm
   |- !x y. SGN (x * y) = SGN x * SGN y
 *--------------------------------------------------------------------------*)

val INT_SGN_MUL2 = store_thm("INT_SGN_MUL2", ``!x y. SGN (x * y) = SGN x * SGN y``,
	REPEAT GEN_TAC THEN
	REWRITE_TAC[SGN_def] THEN
	RW_TAC int_ss[] THEN
	UNDISCH_ALL_TAC THEN
	RW_TAC int_ss[INT_MUL_LZERO, INT_MUL_RZERO] THEN
	PROVE_TAC[INT_NO_ZERODIV, INT_MUL_SIGN_CASES, INT_LT_ANTISYM, INT_LT_TOTAL] );

(*--------------------------------------------------------------------------
   INT_SGN_TOTAL : thm
   |- !a. (SGN a = ~1) \/ (SGN a = 0) \/ (SGN a = 1)
 *--------------------------------------------------------------------------*)

val INT_SGN_TOTAL = store_thm("INT_SGN_TOTAL",``!a. (SGN a = ~1) \/ (SGN a = 0) \/ (SGN a = 1)``,
	GEN_TAC THEN
	REWRITE_TAC[SGN_def] THEN
	RW_TAC int_ss[] );

(*--------------------------------------------------------------------------
   INT_SGN_CASES : thm
   |- !a P. ((SGN a = ~1) ==> P) /\ ((SGN a = 0i) ==> P) /\
                                    ((SGN a = 1i) ==> P) ==> P
 *--------------------------------------------------------------------------*)

val INT_SGN_CASES = store_thm("INT_SGN_CASES", ``!a P. ((SGN a = ~1) ==> P) /\ ((SGN a = 0i) ==> P) /\ ((SGN a = 1i) ==> P) ==> P``,
	REPEAT GEN_TAC THEN
	ASM_CASES_TAC ``SGN a = ~1`` THEN
	ASM_CASES_TAC ``SGN a = 0i`` THEN
	ASM_CASES_TAC ``SGN a = 1i`` THEN
	UNDISCH_ALL_TAC THEN
	PROVE_TAC[INT_SGN_TOTAL] );

(*--------------------------------------------------------------------------
   INT_LT_ADD_NEG : thm
   |- !x y. x < 0i /\ y < 0i ==> x + y < 0i
 *--------------------------------------------------------------------------*)

val INT_LT_ADD_NEG = store_thm("INT_LT_ADD_NEG", ``!x y. x < 0i /\ y < 0i ==> x + y < 0i``,
	REWRITE_TAC[GSYM INT_NEG_GT0, INT_NEG_ADD] THEN
	PROVE_TAC[INT_LT_ADD] );


val _ = export_theory();

