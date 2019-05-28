(* ========================================================================== *)
(* FILE          : ttt_demoScript.sml                                         *)
(* DESCRIPTION   : TacticToe demo                                             *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University          *)
(* DATE          : 2019                                                       *)
(* ========================================================================== *)

open HolKernel boolLib bossLib tacticToe;

val _ = new_theory "ttt_demo";

(* --------------------------------------------------------------------------
   Record ancestries of the current theory.
   ------------------------------------------------------------------------- *)

(* val () = tttUnfold.ttt_record (); *)
(* load "tacticToe"; open tacticToe; *)

(* --------------------------------------------------------------------------
   Example 1: equations
   ------------------------------------------------------------------------- *)

(* ttt ([],``(2 * x + 1 = 3) ==> (x = 1)``); *)
val ex1 = store_thm("ex1",
  ``(2 * x + 1 = 3) ==> (x = 1)``,
  ASM_SIMP_TAC (bool_ss ++ old_ARITH_ss ++ numSimps.REDUCE_ss) []
  );

(* --------------------------------------------------------------------------
   Example 2: lists
   ------------------------------------------------------------------------- *)

(* ttt ([],``(!n. f n = c) ==> (MAP f ls = REPLICATE (LENGTH ls) c)``); *)
val ex2 = store_thm("ex2",
  ``(!n. f n = c) ==> (MAP f ls = REPLICATE (LENGTH ls) c)``,
  (ASM_SIMP_TAC (srw_ss () ++ boolSimps.LET_ss ++ ARITH_ss))
  [listTheory.LIST_EQ_REWRITE, rich_listTheory.EL_REPLICATE] THEN
  METIS_TAC [listTheory.EL_MAP]
  );

(* -------------------------------------------------------------------------
   Example 3: even numbers
   ------------------------------------------------------------------------- *)

(* ttt ([],``!n. EVEN n ==> ~(?m. n = 2 * m + 1)``); *)
val ex3 = store_thm("ex3",
  ``!n. EVEN n ==> ~(?m. n = 2 * m + 1)``,
  SIMP_TAC bool_ss [GSYM arithmeticTheory.ADD1] THEN
  REWRITE_TAC [arithmeticTheory.EVEN_EXISTS, arithmeticTheory.TIMES2] THEN
  METIS_TAC [arithmeticTheory.NOT_ODD_EQ_EVEN]
  );

(* --------------------------------------------------------------------------
   Example 4: set theory, count x = {0,1,2,...,x}
   -------------------------------------------------------------------------- *)

(* ttt ([],``count (n+m) DIFF count n = IMAGE ($+n) (count m)``); *)
val ex4 = store_thm("ex4",
  ``count (n+m) DIFF count n = IMAGE ($+n) (count m)``,
  SRW_TAC [ARITH_ss] [pred_setTheory.EXTENSION, EQ_IMP_THM] THEN
  Q.EXISTS_TAC `x - n` THEN SRW_TAC [ARITH_ss] []
  );

(* --------------------------------------------------------------------------
   Example 5: closed form sums. tactictoe was not able to minimize the proof.
   -------------------------------------------------------------------------- *)

open sum_numTheory;
(* ttt  ([],``!n. 2 * SUM (n+1) I = n * (n+1) ``); *)
val ex5 = store_thm("ex5",
  ``!n. 2 * SUM (n+1) I = n * (n+1)``,
  bossLib.Induct_on [HolKernel.QUOTE " (*#loc 26 15*)n"] THENL [BasicProvers.SRW_TAC [numSimps.ARITH_ss] [(DB.fetch "numpair" "tri_def"),
 arithmeticTheory.MULT_CLAUSES, arithmeticTheory.LEFT_ADD_DISTRIB] THEN
 metisTools.METIS_TAC [sum_numTheory.SUM_1, sum_numTheory.SUM_def_compute,
 sum_numTheory.SUM, sum_numTheory.SUM_EQUAL, sum_numTheory.SUM_FOLDL,
 sum_numTheory.SUM_LESS, sum_numTheory.SUM_MONO, sum_numTheory.SUM_ZERO,
 sum_numTheory.SUM_def, sum_numTheory.SUM_FUN_EQUAL,
 rich_listTheory.COUNT_LIST_GENLIST, pred_setTheory.PROD_SET_DEF,
 pred_setTheory.SUM_SET_DEF, listTheory.DROP_splitAtPki, combinTheory.I_DEF,
 combinTheory.I_THM], bossLib.Induct_on [HolKernel.QUOTE " (*#loc 26 15*)n"]
THENL [BasicProvers.SRW_TAC [numSimps.ARITH_ss] [(DB.fetch "numpair" "tri_def"),
 arithmeticTheory.MULT_CLAUSES, arithmeticTheory.LEFT_ADD_DISTRIB] THEN
 bossLib.ASM_SIMP_TAC bossLib.arith_ss [sum_numTheory.SUM_def_compute,
 sum_numTheory.SUM_1, sum_numTheory.SUM, sum_numTheory.SUM_EQUAL,
 sum_numTheory.SUM_FOLDL, sum_numTheory.SUM_FUN_EQUAL, sum_numTheory.SUM_LESS,
 sum_numTheory.SUM_MONO, sum_numTheory.SUM_ZERO, sum_numTheory.SUM_def,
 arithmeticTheory.DOUBLE_LT, arithmeticTheory.MOD_2, arithmeticTheory.TWO,
 arithmeticTheory.X_LT_X_SQUARED, ind_typeTheory.NUMPAIR,
 numeralTheory.TWO_EXP_THM], bossLib.ASM_SIMP_TAC bossLib.arith_ss
 [numeralTheory.iiSUC, sum_numTheory.SUM_def_compute, sum_numTheory.SUM_1,
 sum_numTheory.SUM_def, sum_numTheory.SUM_MONO, arithmeticTheory.ADD,
 arithmeticTheory.ADD_CLAUSES, numpairTheory.tri_def, sum_numTheory.SUM_FOLDL,
 sum_numTheory.SUM_EQUAL, sum_numTheory.SUM_FUN_EQUAL, sum_numTheory.SUM_ZERO,
 sum_numTheory.SUM_LESS, sum_numTheory.SUM, arithmeticTheory.MULT_CLAUSES,
 arithmeticTheory.FACT] THEN bossLib.SRW_TAC [bossLib.ARITH_ss] [(DB.fetch
 "sum_num" "SUM_def"),rich_listTheory.COUNT_LIST_SNOC, listTheory.FOLDL_SNOC]]]
);

val _ = export_theory();
