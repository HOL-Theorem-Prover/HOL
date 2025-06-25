open HolKernel Parse boolLib bossLib;
open backendProofTheory backend_itreeProofTheory;

val _ = new_theory "cakeml_comp_thms";

(* check that there are no cheats in key theorems of CakeML *)

fun check_tag t = Tag.isEmpty t orelse Tag.isDisk t;
val check_thm = Lib.assert (check_tag o Thm.tag);

val _ = check_thm backendProofTheory.compile_correct;
val _ = check_thm backendProofTheory.compile_correct_is_safe_for_space;
val _ = check_thm backendProofTheory.compile_correct_eval;
val _ = check_thm backend_itreeProofTheory.itree_compile_correct;

val _ = export_theory();
