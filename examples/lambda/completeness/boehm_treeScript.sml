(*---------------------------------------------------------------------------*
 * boehm_treeScript.sml: (Effective) Boehm Trees (Chapter 10 of [1])         *
 *---------------------------------------------------------------------------*)

open HolKernel boolLib Parse bossLib;

(* core theories *)
open optionTheory arithmeticTheory pred_setTheory listTheory rich_listTheory
     llistTheory relationTheory ltreeTheory pathTheory posetTheory hurdUtils;

open basic_swapTheory binderLib termTheory appFOLDLTheory chap2Theory
     chap3Theory head_reductionTheory standardisationTheory solvableTheory;

open pure_dBTheory;

val _ = new_theory "boehm_tree";

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val o_DEF = combinTheory.o_DEF; (* cannot directly open combinTheory *)

(* A dB-term M is hnf if its corresponding Lambda term is hnf *)
Overload dhnf = “\M. hnf (toTerm M)”

Theorem dhnf_fromTerm[simp] :
    !M. dhnf (fromTerm M) <=> hnf M
Proof
    rw [o_DEF]
QED

val _ = export_theory ();
val _ = html_theory "boehm_tree";

(* References:

   [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
       College Publications, London (1984).
 *)
