open HolKernel Parse boolLib
open parentLib

(* Name deliberately long enough that the .dat header's sexp printer
   wraps the (theory ...) sublist onto a new line, exercising the
   "(theory\n" case in HM_CacheFetch.extract_parents. *)
val _ = new_theory "wrapping_child";
val child_thm = save_thm("child_thm", parent_thm);
val _ = export_theory();
