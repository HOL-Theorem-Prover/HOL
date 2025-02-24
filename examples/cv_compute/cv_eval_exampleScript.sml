(*
  Demonstrates use of cv_eval_raw_save
*)
open HolKernel Parse boolLib bossLib;
open cv_transLib cv_stdTheory

val _ = new_theory "cv_eval_example";

Definition test_def:
  test n = if n = 0 then NONE else SOME (n+1, n+2, REPLICATE n T)
End

val _ = cv_trans test_def;

val pat = Some (Pair (Eval EVAL, Pair (Raw, Name "big_replicate")));

val res = cv_eval_pat pat “test 10000”;
(* returns:
     ⊢ test 10000 = SOME (10001,cv$c2n (Num 10002),big_replicate)
*)

val res = cv_eval “LENGTH big_replicate”;
(* returns:
     ⊢ LENGTH big_replicate = 10000
*)

val _ = (max_print_depth := 10);
val _ = export_theory();
