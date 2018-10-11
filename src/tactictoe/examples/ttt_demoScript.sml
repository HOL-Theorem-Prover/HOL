(* ========================================================================== *)
(* FILE          : ttt_demoScript.sml                                         *)
(* DESCRIPTION   : TacticToe demo                                             *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2018                                                       *)
(* ========================================================================== *)

open HolKernel boolLib bossLib tacticToe;

val _ = new_theory "ttt_demo";

(* ---------------------------------------------------------------------------
   Record ancestries of the current theory. Takes a while.
   To rebuild tactictoe for a theory, delete the corresponding ttt.sml file.
   -------------------------------------------------------------------------- *)

val () = ttt_record ();

(* load "tacticToe"; open tacticToe; *)

(* ---------------------------------------------------------------------------
   Example 1: equations
   -------------------------------------------------------------------------- *)

(* ttt ([],``(2 * x + 1 = 3) ==> (x = 1)``); *)
val ex1 = store_thm("ex1",
  ``(2 * x + 1 = 3) ==> (x = 1)``,
  ASM_SIMP_TAC (bool_ss ++ old_ARITH_ss ++ numSimps.REDUCE_ss) []
  );

(* ---------------------------------------------------------------------------
   Example 2: lists
   -------------------------------------------------------------------------- *)

(* ttt ([],``(!n. f n = c) ==> (MAP f ls = REPLICATE (LENGTH ls) c)``); *)
val ex2 = store_thm("ex2",
  ``(!n. f n = c) ==> (MAP f ls = REPLICATE (LENGTH ls) c)``,
  (ASM_SIMP_TAC (srw_ss () ++ boolSimps.LET_ss ++ ARITH_ss)) [listTheory.LIST_EQ_REWRITE, rich_listTheory.EL_REPLICATE] THEN METIS_TAC [listTheory.EL_MAP]
  );

(* ---------------------------------------------------------------------------
   Example 3: even numbers
   -------------------------------------------------------------------------- *)

(* ttt ([],``!n. EVEN n ==> ~(?m. n = 2 * m + 1)``); *)
val ex3 = store_thm("ex3", 
  ``!n. EVEN n ==> ~(?m. n = 2 * m + 1)``,
  SIMP_TAC bool_ss [GSYM arithmeticTheory.ADD1] THEN REWRITE_TAC [arithmeticTheory.EVEN_EXISTS, arithmeticTheory.TIMES2] THEN METIS_TAC [arithmeticTheory.NOT_ODD_EQ_EVEN] 
  );

(* ---------------------------------------------------------------------------
   Example 4: set theory, count x = {0,1,2,...,x}
   -------------------------------------------------------------------------- *)

(* ttt ([],``count (n+m) DIFF count n = IMAGE ($+n) (count m)``); *)
val ex4 = store_thm("ex4", 
  ``count (n+m) DIFF count n = IMAGE ($+n) (count m)``,
  SRW_TAC [ARITH_ss] [pred_setTheory.EXTENSION, EQ_IMP_THM] THEN Q.EXISTS_TAC `x - n` THEN SRW_TAC [ARITH_ss] []
  );

(* ---------------------------------------------------------------------------
   Feel free to add your own test examples to contribute to the improvement of
   TacticToe.
   -------------------------------------------------------------------------- *)

val _ = export_theory();
