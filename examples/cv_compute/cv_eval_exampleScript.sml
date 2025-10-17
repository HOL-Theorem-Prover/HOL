(*
  Demonstrates use of cv_eval_pat
*)
Theory cv_eval_example
Ancestors
  cv_std
Libs
  cv_transLib

Definition test_def:
  test n = if n = 0 then NONE else SOME (n+1, n+2, REPLICATE n T)
End

val _ = cv_trans test_def;

(* The following example demonstrates that the given pattern,
   Some (Tuple ...), instructs cv_eval_pat what to do with the
   result of evaluation. In this example, we can see that the
   result must be a SOME containing a tuple and the elements
   of the tuple are handled as follows.
    - The first is just directly evaluated.
    - The second is left untouched after the raw cv computation.
    - The third is stored in a new constant, big_replicate, that
      can be used in subsequent calls to cv_trans, cv_eval, etc.
*)
val res = cv_eval_pat
            (Some (Tuple [Eval EVAL, Raw, Name "big_replicate"]))
            “test 10000”;
(* returns:
     ⊢ test 10000 = SOME (10001,cv$c2n (Num 10002),big_replicate)
*)

val res = cv_eval “LENGTH big_replicate”;
(* returns:
     ⊢ LENGTH big_replicate = 10000
*)

val _ = (max_print_depth := 10);
