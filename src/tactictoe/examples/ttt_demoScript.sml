(* ========================================================================== *)
(* FILE          : ttt_demoScript.sml                                         *)
(* DESCRIPTION   : TacticToe demo                                             *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2018                                                       *)
(* ========================================================================== *)

(* ---------------------------------------------------------------------------
   Requirement:
     HOL version later than 16 February 2018
     (Reconfigure (poly --script tools/smart-configure.sml)
      and rebuild if your previous version was older.)
   -------------------------------------------------------------------------- *)

open HolKernel boolLib bossLib tacticToe;

val _ = new_theory "ttt_demo";

(* ---------------------------------------------------------------------------
   Record ancestries of the current theory. Takes a while.
   To rebuild tactictoe for a theory, delete the corresponding ttt.sml file.
   -------------------------------------------------------------------------- *)

val () = ttt_record ();

(* ---------------------------------------------------------------------------
   Example 1
   -------------------------------------------------------------------------- *)

val ex1 = store_thm("ex1",
  ``x > 9 ==> x > 8``,
  (* Run this tactic first, to generate the one below: 
     ttt ([],``x > 9 ==> x > 8``); *)
  (ASM_SIMP_TAC (srw_ss () ++ boolSimps.LET_ss ++ ARITH_ss)) []);

(* ---------------------------------------------------------------------------
   Example 2
   -------------------------------------------------------------------------- *)

val ex2 = store_thm("ex2",
  ``(!n. f n = c) ==> (MAP f ls = REPLICATE (LENGTH ls) c)``,
  (* ttt ([],``(!n. f n = c) ==> (MAP f ls = REPLICATE (LENGTH ls) c)``); *)
  (ASM_SIMP_TAC (srw_ss () ++ boolSimps.LET_ss ++ ARITH_ss)) 
  [listTheory.LIST_EQ_REWRITE, rich_listTheory.EL_REPLICATE] THEN
  SRW_TAC [] [listTheory.EL_MAP]);

(* ---------------------------------------------------------------------------
   Example 3
   -------------------------------------------------------------------------- *)

val ex3 = store_thm("ex3",
  ``!n. EVEN n ==> ~(?m. n = 2 * m + 1)``,
  (* ttt ([],``!n. EVEN n ==> ~(?m. n = 2 * m + 1)``); *)
  SIMP_TAC bool_ss [GSYM arithmeticTheory.ADD1] THEN
  PROVE_TAC [arithmeticTheory.EVEN_ODD, arithmeticTheory.ODD_DOUBLE]);

(* ---------------------------------------------------------------------------
   Example 4
   -------------------------------------------------------------------------- *)

val ex4 = store_thm("ex4",
  ``count n SUBSET count (n+m)``,
  (* ttt ([],``count n SUBSET count (n+m)``); *)
  ASM_SIMP_TAC numLib.std_ss 
    [pred_setTheory.SUBSET_DEF, 
     pred_setTheory.count_def,
     pred_setTheory.GSPECIFICATION] THEN
  METIS_TAC [arithmeticTheory.LESS_IMP_LESS_ADD]
);

(* ---------------------------------------------------------------------------
   Example 5
   -------------------------------------------------------------------------- *)

val ex5 = store_thm("ex5",
  ``count (n+m) DIFF count n = IMAGE ($+n) (count m)``,
  (* ttt ([],``count (n+m) DIFF count n = IMAGE ($+n) (count m)``); *)
  SRW_TAC [ARITH_ss] [pred_setTheory.EXTENSION, EQ_IMP_THM] THEN 
  Q.EXISTS_TAC `x - n` THEN 
  SRW_TAC [ARITH_ss] []
);

(* ---------------------------------------------------------------------------
   Example 6
   -------------------------------------------------------------------------- *)

val ex6 = store_thm("ex6",
  ``(MAP f1 ls = MAP f2 ls) /\ MEM x ls ==> (f1 x = f2 x)``,
  (* ttt ([],``(MAP f1 ls = MAP f2 ls) /\ MEM x ls ==> (f1 x = f2 x)``); *)
  SRW_TAC [] [listTheory.MAP_EQ_f]);

(* ---------------------------------------------------------------------------
   Example 7: failure
   -------------------------------------------------------------------------- *)

(*
val () = set_timeout 10.0;
val ex7 = store_thm("ex7",
  ``countable (UNIV:num list set)``
  ttt ([],``countable (UNIV:num list set)``); (* times out *));
*)

(* ---------------------------------------------------------------------------
   Feel free to add your own test examples to contribute to the improvement of
   TacticToe.
   -------------------------------------------------------------------------- *)

val _ = export_theory();
