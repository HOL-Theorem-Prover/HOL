(*****************************************************************************)
(* Examples of M1                                                            *)
(*****************************************************************************)

(* Commands when run interactively:
quietdec := true;                                    (* Switch off output    *)

map load ["sexpTheory","imported_acl2Theory"];
open sexpTheory imported_acl2Theory;

quietdec := false;                                   (* Restore output       *)
*)


(******************************************************************************
* Boilerplate needed for compilation: open HOL4 systems modules.
******************************************************************************)
open HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories (including ratTheory from Jens Brandt).
******************************************************************************)

open sexpTheory imported_acl2Theory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Function to simplify imported ACL2
******************************************************************************)

val acl2_simp =
 SIMP_RULE
  list_ss
  ([let_simp,andl_fold,itel_fold,itel_append,
    forall2_thm,exists2_thm,forall_fold,exists_fold,
    implies,andl_simp,not_simp,t_nil]
   @
   (map GSYM [int_def,nat_def,List_def,asym_def,csym_def,ksym_def,osym_def]));

(******************************************************************************
M1 contains simplified definitions and theorems from other theories
******************************************************************************)

val Examples1 =
 [("exclaim_def",         acl2_simp exclaim_defun),
  ("ifact_def",           acl2_simp ifact_defun),
  ("ifact_lemma",         acl2_simp ifact_lemma_thm),
  ("ifact_is_factorial",  acl2_simp ifact_is_factorial_thm),
  ("ifact_correct",       acl2_simp ifact_correct_thm),
  ("repeat_def",          acl2_simp repeat_defun),
  ("ifact_sched_def",     acl2_simp ifact_sched_defun),
  ("test_ifact_examples", acl2_simp test_ifact_examples_thm)];

val Examples2 = map (I ## acl2_simp) (theorems "imported_acl2");

