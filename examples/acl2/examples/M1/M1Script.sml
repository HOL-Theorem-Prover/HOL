(*****************************************************************************)
(* Create "M1Theory"                                                         *)
(*****************************************************************************)

(* Commands when run interactively:
quietdec := true;                                    (* Switch off output    *)

map load ["imported_acl2Theory"];
open imported_acl2Theory;

quietdec := false;                                   (* Restore output       *)
*)


(******************************************************************************
* Boilerplate needed for compilation: open HOL4 systems modules.
******************************************************************************)
open HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories (including ratTheory from Jens Brandt).
******************************************************************************)

open stringLib complex_rationalTheory acl2_packageTheory sexp sexpTheory
     imported_acl2Theory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Start a new theory called M1
******************************************************************************)

val _ = new_theory "M1";

val simp_fn =
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

val exclaim_def =
 save_thm("exclaim_def", simp_fn exclaim_defun);

val ifact_def =
 save_thm("ifact_def", simp_fn ifact_defun);

val ifact_lemma =
 save_thm("ifact_lemma", simp_fn ifact_lemma_thm);

val ifact_is_factorial =
 save_thm("ifact_is_factorial", simp_fn ifact_is_factorial_thm);

val ifact_correct =
 save_thm("ifact_correct", simp_fn ifact_correct_thm);

val repeat_def =
 save_thm("repeat_def", simp_fn repeat_defun);

val ifact_sched_def =
 save_thm("ifact_sched_def", simp_fn ifact_sched_defun);

val test_ifact_examples =
 save_thm("test_ifact_examples", simp_fn test_ifact_examples_thm);

val _ = export_theory();
