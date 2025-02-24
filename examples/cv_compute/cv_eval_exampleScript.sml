(*
  Demonstrates use of cv_eval_raw_save
*)
open HolKernel Parse boolLib bossLib;
open cv_transLib cv_stdTheory

val _ = new_theory "cv_eval_example";

val (def, res) = cv_eval_raw_save "big_replicate" “REPLICATE 100000 T”
(* returns:
     def: ⊢ big_replicate = REPLICATE 100000 T
     res: ⊢ big_replicate = to_list cv$c2b (cv_big_replicate (Num 0))
   where cv_big_replicate is a constant holding the huge cv value *)

val res = cv_eval “LENGTH big_replicate”;
(* returns:
     res: ⊢ LENGTH big_replicate = 100000 *)

val _ = (max_print_depth := 10);
val _ = export_theory();
