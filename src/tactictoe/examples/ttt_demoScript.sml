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

(* load "tacticToe"; open tacticToe; *)
(* load "tttUnfold"; val () = tttUnfold.ttt_record (); *)
(* mlibUseful.trace_level := 0; mesonLib.chatting := 0; *)

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

open listTheory

(* ttt ([],``(!n. f n = c) ==> (MAP f ls = REPLICATE (LENGTH ls) c)``); 
   ttt_mini ([],``(!n. f n = c) ==> (MAP f ls = REPLICATE (LENGTH ls) c)``); *)
val ex2 = store_thm("ex2",
  ``(!n. f n = c) ==> (MAP f ls = REPLICATE (LENGTH ls) c)``,
  (ASM_SIMP_TAC (srw_ss () ++ boolSimps.LET_ss ++ ARITH_ss))
  [LIST_EQ_REWRITE, rich_listTheory.EL_REPLICATE] THEN
  METIS_TAC [EL_MAP]
  );

(* --------------------------------------------------------------------------
   Example 3: set theory, count x = {0,1,2,...,x}
   -------------------------------------------------------------------------- *)

open pred_setTheory

(* ttt ([],``count (n+m) DIFF count n = IMAGE ($+n) (count m)``); *)
val ex4 = store_thm("ex4",
  ``count (n+m) DIFF count n = IMAGE ($+n) (count m)``,
  SRW_TAC [ARITH_ss] [EXTENSION, EQ_IMP_THM] THEN
  Q.EXISTS_TAC `x - n` THEN SRW_TAC [ARITH_ss] []
  );

(* --------------------------------------------------------------------------
   Example 4: sums
   -------------------------------------------------------------------------- *)

(* load "sum_numTheory"; open sum_numTheory; set_timeout 60.0; *)
open sum_numTheory

(* ttt  ([],``!n. 2 * SUM (n+1) I = n * (n+1) ``); *)
val ex5 = store_thm("ex5",
  ``!n. 2 * SUM (n+1) I = n * (n+1)``,
   Induct THENL 
   [REWRITE_TAC [numeralTheory.numeral_distrib] THEN SRW_TAC [] [SUM_1], 
    ASM_SIMP_TAC (srw_ss () ++ ARITH_ss) [ADD_CLAUSES] THEN 
      SRW_TAC [ARITH_ss] [SUM_def] THEN 
      SRW_TAC [ARITH_ss] [MULT_CLAUSES]]
);


val _ = export_theory();
