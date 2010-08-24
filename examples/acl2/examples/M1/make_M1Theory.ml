(*****************************************************************************)
(* Create "M1Theory"                                                         *)
(*****************************************************************************)

quietdec := true;                                    (* Switch off output    *)

map load ["imported_acl2Theory","load_book"];
open imported_acl2Theory load_book;

quietdec := false;                                   (* Restore output       *)

(******************************************************************************
* Start a new theory called M1
******************************************************************************)

val _ = new_theory "M1";

(******************************************************************************
M1 contains simplified definitions and theorems from other theories
******************************************************************************)

val exclaim_def =
 save_thm("exclaim_def", load_simp_fn exclaim_defun);

val ifact_def =
 save_thm("ifact_def", load_simp_fn ifact_defun);

val ifact_lemma =
 save_thm("ifact_lemma", load_simp_fn ifact_lemma_thm);

val ifact_is_factorial =
 save_thm("ifact_is_factorial", load_simp_fn ifact_is_factorial_thm);

val ifact_correct =
 save_thm("ifact_correct", load_simp_fn ifact_correct_thm);

val repeat_def =
 save_thm("repeat_def", load_simp_fn repeat_defun);

val ifact_sched_def =
 save_thm("ifact_sched_def", load_simp_fn ifact_sched_defun);

val test_ifact_examples =
 save_thm("test_ifact_examples", load_simp_fn test_ifact_examples_thm);

val _ = export_theory();

val _ = compile_theory();
