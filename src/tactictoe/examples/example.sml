(* ========================================================================== *)
(* FILE          : examples.sml                                               *)
(* DESCRIPTION   : Examples for TacticToe                                     *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2018                                                       *)
(* ========================================================================== *)


(* ---------------------------------------------------------------------------
   Requirement: 
     HOL version later than 16 Februrary 2018
     Reconfiguring (poly < tools/smart-configure.sml)
     and rebuilding are necessary.
   -------------------------------------------------------------------------- *)

load "tacticToe";
open tacticToe;

(* ---------------------------------------------------------------------------
   Record ancestries of the current theory. Takes a while.
   To rebuild tactictoe for a theory, delete the corresponding ttt.sml file.
   -------------------------------------------------------------------------- *)

ttt_record ();

(* ---------------------------------------------------------------------------
   Example 1
   -------------------------------------------------------------------------- *)

ttt ([],``x > 9 ==> x > 8``);
(ASM_SIMP_TAC (srw_ss () ++ boolSimps.LET_ss ++ ARITH_ss)) []

(* ---------------------------------------------------------------------------
   Example 2
   -------------------------------------------------------------------------- *)

tactictoe ([],``(!n. f n = c) ==> (MAP f ls = REPLICATE (LENGTH ls) c)``);
(ASM_SIMP_TAC (srw_ss () ++ boolSimps.LET_ss ++ ARITH_ss))
[listTheory.LIST_EQ_REWRITE, ((fetch "rich_list" "EL_REPLICATE"))] THEN 
METIS_TAC [listTheory.EL_MAP]

(* ---------------------------------------------------------------------------
   Example 3
   -------------------------------------------------------------------------- *)

tactictoe ([],``!n. EVEN n ==> ~(?m. n = 2 * m + 1)``);
PROVE_TAC [(fetch "arithmetic" "ODD_EXISTS"), (fetch "arithmetic" "ADD1"), (fetch "arithmetic" "EVEN_ODD")]

(* ---------------------------------------------------------------------------
   Example 4
   -------------------------------------------------------------------------- *)

tactictoe ([], ``count n SUBSET count (n+m)``);
ASM_SIMP_TAC numLib.std_ss [(fetch "pred_set" "SUBSET_DEF"),
  (fetch "pred_set" "count_def"), (fetch "pred_set" "GSPECIFICATION")] THEN 
METIS_TAC [arithmeticTheory.LESS_IMP_LESS_ADD]


(* ---------------------------------------------------------------------------
   Example 5
   -------------------------------------------------------------------------- *)

tactictoe ([], ``count (n+m) DIFF count n = IMAGE ($+n) (count m)``);
SRW_TAC [ARITH_ss] [(fetch "pred_set" "EXTENSION"), EQ_IMP_THM] THEN 
Q.EXISTS_TAC `x - n` THEN 
SRW_TAC [ARITH_ss] []

(* ---------------------------------------------------------------------------
   Example 6
   -------------------------------------------------------------------------- *)

tactictoe ([], ``(MAP f1 ls = MAP f2 ls) /\ MEM x ls ==> (f1 x = f2 x)``);
SRW_TAC [] [listTheory.MAP_EQ_f]

(* ---------------------------------------------------------------------------
   Example 7: failure
   -------------------------------------------------------------------------- *)

set_timeout 60.0;
tactictoe ([], ``countable (UNIV:num list set)``);

(* ---------------------------------------------------------------------------
   Feel free to add your own test examples to contribute to the improvement of
   TacticToe.
   -------------------------------------------------------------------------- *)
