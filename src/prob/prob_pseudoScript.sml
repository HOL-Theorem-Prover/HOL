(* non-interactive mode
*)
open HolKernel Parse boolLib;

val _ = new_theory "prob_pseudo";

(* interactive mode
if !show_assums then () else
 (load "bossLib";
  load "realLib";
  load "arithmeticTheory";
  load "numTheory";
  load "pred_setTheory";
  load "ind_typeTheory";
  load "rich_listTheory";
  load "pairTheory";
  load "combinTheory";
  load "probUtil";
  load "boolean_sequenceTheory";
  load "boolean_sequenceTools";
  load "prob_extraTheory";
  load "prob_extraTools";
  show_assums := true);
*)

open bossLib arithmeticTheory numTheory realTheory seqTheory pred_setTheory
     ind_typeTheory listTheory rich_listTheory pairTheory combinTheory realLib
     probTools boolean_sequenceTheory boolean_sequenceTools prob_extraTheory
     prob_extraTools;

infixr 0 ++ << || ORELSEC ##;
infix 1 >> |->;
nonfix THEN THENL ORELSE;

val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

(* ------------------------------------------------------------------------- *)
(* The definition of the pseudo-random number generator.                     *)
(* ------------------------------------------------------------------------- *)

val pseudo_linear_hd_def = Define `pseudo_linear_hd = EVEN`;

val pseudo_linear_tl_def
  = Define `pseudo_linear_tl a b n x = (a * x + b) MOD (2 * n + 1)`;

(* ------------------------------------------------------------------------- *)
(* Theorems leading to:                                                      *)
(* 1. !phd ptl. ?g. !(x:'a). (SHD (g x) = phd x) /\ (STL (g x) = g (ptl x))  *)
(* ------------------------------------------------------------------------- *)

val PSEUDO_EXECUTE = prove
  (``!phd ptl. ?g. (!(x:'a). SHD (g x) = phd x)
                /\ (!(x:'a). STL (g x) = g (ptl x))``,
   RW_TAC std_ss []
   ++ Q.EXISTS_TAC `\x n. phd (FUNPOW ptl n x)`
   ++ ONCE_REWRITE_TAC [GSYM EQ_EXT_EQ]
   ++ RW_TAC std_ss [SHD_def, STL_def, FUNPOW]);

val PSEUDO_LINEAR1_EXECUTE = save_thm
  ("PSEUDO_LINEAR1_EXECUTE",
   Q.SPECL [`pseudo_linear_hd`, `pseudo_linear_tl 103 95 79`]
     (INST_TYPE [alpha |-> numSyntax.num] PSEUDO_EXECUTE));

val pseudo_linear1_def = new_specification
  ("pseudo_linear1_def", ["pseudo_linear1"], PSEUDO_LINEAR1_EXECUTE);

val pseudo_def = Define `pseudo = pseudo_linear1`;

val _ = export_theory ();




