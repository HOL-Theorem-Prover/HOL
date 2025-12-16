(* ========================================================================== *)
(* FILE          : ttt_demoScript.sml                                         *)
(* DESCRIPTION   : TacticToe demo                                             *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University          *)
(* DATE          : 2019                                                       *)
(* ========================================================================== *)
Theory ttt_demo
Ancestors
  list pred_set sum_num
Libs
  tacticToe


(* load "tacticToe"; open tacticToe; *)
(* mlibUseful.trace_level := 0; mesonLib.chatting := 0; *)

(* --------------------------------------------------------------------------
   Example 1: equations
   ------------------------------------------------------------------------- *)

(* ttt ([],``(2 * x + 1 = 3) ==> (x = 1)``); *)
Theorem ex1:
    (2 * x + 1 = 3) ==> (x = 1)
Proof
  asm_simp_tac (bool_ss ++ old_ARITH_ss ++ numSimps.REDUCE_ss) []
QED

(* --------------------------------------------------------------------------
   Example 2: lists
   ------------------------------------------------------------------------- *)

(* ttt ([],``(!n. f n = c) ==> (MAP f ls = REPLICATE (LENGTH ls) c)``); *)
Theorem ex2:
    (!n. f n = c) ==> (MAP f ls = REPLICATE (LENGTH ls) c)
Proof
  asm_simp_tac (srw_ss () ++ boolSimps.LET_ss ++ ARITH_ss) [LIST_EQ_REWRITE] >>
  metis_tac [EL_MAP, rich_listTheory.EL_REPLICATE]
QED

(* --------------------------------------------------------------------------
   Example 3: set theory, count x = {0,1,2,...,x}
   -------------------------------------------------------------------------- *)

(* ttt ([],``count (n+m) DIFF count n = IMAGE ($+n) (count m)``); *)
Theorem ex4:
    count (n+m) DIFF count n = IMAGE ($+n) (count m)
Proof
  srw_tac [ARITH_ss] [EXTENSION, EQ_IMP_THM] >>
  Q.EXISTS_TAC `x - n` >>
  srw_tac [ARITH_ss] []
QED

(* --------------------------------------------------------------------------
   Example 4: sums
   -------------------------------------------------------------------------- *)

(* load "sum_numTheory"; open sum_numTheory; set_timeout 60.0; *)
(* ttt  ([],``!n. 2 * SUM (n+1) I = n * (n+1) ``); *)
Theorem ex5:
    !n. 2 * SUM (n+1) I = n * (n+1)
Proof
  Induct >|
    [rewrite_tac [numeralTheory.numeral_distrib] >>
       srw_tac [] [SUM_1],
     asm_simp_tac (srw_ss () ++ ARITH_ss) [arithmeticTheory.ADD_CLAUSES] >>
       srw_tac [ARITH_ss] [SUM_def] >>
       srw_tac [ARITH_ss] [arithmeticTheory.MULT_CLAUSES]]
QED

