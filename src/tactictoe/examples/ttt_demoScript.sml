(* ========================================================================== *)
(* FILE          : ttt_demoScript.sml                                         *)
(* DESCRIPTION   : TacticToe demo                                             *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University          *)
(* DATE          : 2019                                                       *)
(* ========================================================================== *)

open HolKernel boolLib bossLib tacticToe;

val _ = new_theory "ttt_demo";

(* load "tacticToe"; open tacticToe; *)
(* mlibUseful.trace_level := 0; mesonLib.chatting := 0; *)

(* --------------------------------------------------------------------------
   Example 1: equations
   ------------------------------------------------------------------------- *)

(* ttt ([],``(2 * x + 1 = 3) ==> (x = 1)``); *)
val ex1 = store_thm("ex1",
  ``(2 * x + 1 = 3) ==> (x = 1)``,
  asm_simp_tac (bool_ss ++ old_ARITH_ss ++ numSimps.REDUCE_ss) []
  );

(* --------------------------------------------------------------------------
   Example 2: lists
   ------------------------------------------------------------------------- *)

open listTheory

(* ttt ([],``(!n. f n = c) ==> (MAP f ls = REPLICATE (LENGTH ls) c)``); *)
val ex2 = store_thm("ex2",
  ``(!n. f n = c) ==> (MAP f ls = REPLICATE (LENGTH ls) c)``,
  asm_simp_tac (srw_ss () ++ boolSimps.LET_ss ++ ARITH_ss) [LIST_EQ_REWRITE] >>
  metis_tac [EL_MAP, rich_listTheory.EL_REPLICATE]
  );

(* --------------------------------------------------------------------------
   Example 3: set theory, count x = {0,1,2,...,x}
   -------------------------------------------------------------------------- *)

open pred_setTheory

(* ttt ([],``count (n+m) DIFF count n = IMAGE ($+n) (count m)``); *)
val ex4 = store_thm("ex4",
  ``count (n+m) DIFF count n = IMAGE ($+n) (count m)``,
  srw_tac [ARITH_ss] [EXTENSION, EQ_IMP_THM] >>
  Q.EXISTS_TAC `x - n` >>
  srw_tac [ARITH_ss] []
  );

(* --------------------------------------------------------------------------
   Example 4: sums
   -------------------------------------------------------------------------- *)

(* load "sum_numTheory"; open sum_numTheory; set_timeout 60.0; *)
open sum_numTheory

(* ttt  ([],``!n. 2 * SUM (n+1) I = n * (n+1) ``); *)
val ex5 = store_thm("ex5",
  ``!n. 2 * SUM (n+1) I = n * (n+1)``,
  Induct >|
    [rewrite_tac [numeralTheory.numeral_distrib] >>
       srw_tac [] [SUM_1],
     asm_simp_tac (srw_ss () ++ ARITH_ss) [arithmeticTheory.ADD_CLAUSES] >>
       srw_tac [ARITH_ss] [SUM_def] >>
       srw_tac [ARITH_ss] [arithmeticTheory.MULT_CLAUSES]]
  );

val _ = export_theory();
