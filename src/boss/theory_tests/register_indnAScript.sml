open HolKernel Parse boolLib bossLib;

val _ = new_theory "register_indnA";
val _ = add_ML_dependency "Werror"

Definition foo_def:
  foo [] = [] /\
  foo (h::t) = (h + 1) :: foo t
End

Definition foo_def[allow_rebind]:
  foo x 0 = x /\
  foo x (SUC n) = SUC (foo x n)
End

val _ = case DefnBase.lookup_indn “foo” of
          SOME (th,_) =>
            “!x:num n:num. P x n” ~~
            (th |> concl |> strip_forall |> #2 |> dest_imp |> #2)
        | NONE => raise Fail "Bad conclusion for foo induction theorem"

Definition bar_def[notuserdef]:
  bar x 0 = 0 /\
  bar x (SUC n) = foo x (bar x n)
End

Definition baz_def[notuserdef]:
  baz (x, 0) = 0 /\
  baz (x, SUC n) = foo x (baz(x, n))
End


val _ = export_theory();
