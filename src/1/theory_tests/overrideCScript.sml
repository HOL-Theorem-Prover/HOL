Theory overrideC[bare]
Ancestors
  overrideA
Libs
  HolKernel Parse boolLib testutils

(* Cross-theory redefinition attack, analogous to the bool$T paste
   attached to #2027 but targeting a user-defined parent's constant.
   overrideB is *not* an ancestor of overrideC on purpose: the
   original exploit needs to load overrideBTheory *after* the
   KernelSig entry for overrideA$c has been retired and replaced by
   a fresh, contradictory id.

   Under the new regime overrideA is sealed the moment it's loaded,
   and every route an attacker might take is now closed:
     (1) The definition principles `Thm.prim_*` no longer take a
         thyname argument, so the "just pass overrideA" form used by
         the paste is gone from the API entirely.
     (2) `Thm.setCT "overrideA"` — the workaround an attacker would
         use to swing the current-thy state before minting — raises
         because overrideA is sealed.
     (3) `Term.prim_new_const {Thy="overrideA",...}` and
         `Type.prim_new_type {Thy="overrideA",...}` — the raw kernel
         entry points — refuse for the same reason.
*)
val _ =
  if not (Thm.is_sealed "overrideA") then
    die "overrideA not sealed; test setup wrong"
  else ()

val _ = shouldfail
  {checkexn    = is_struct_HOL_ERR "Thm",
   printarg    = K "Thm.setCT to sealed parent theory refused",
   printresult = fn () => "<no exception>",
   testfn      = Thm.setCT}
  "overrideA"

val _ = shouldfail
  {checkexn    = is_struct_HOL_ERR "Term",
   printarg    = K "Term.prim_new_const into sealed parent theory refused",
   printresult = fn _ => "<no exception>",
   testfn      = fn knm => Term.prim_new_const knm Type.bool}
  {Thy = "overrideA", Name = "attacker"}

val _ = shouldfail
  {checkexn    = is_struct_HOL_ERR "Type",
   printarg    = K "Type.prim_new_type into sealed parent theory refused",
   printresult = fn () => "<no exception>",
   testfn      = fn knm => Type.prim_new_type knm 0}
  {Thy = "overrideA", Tyop = "attacker_ty"}

