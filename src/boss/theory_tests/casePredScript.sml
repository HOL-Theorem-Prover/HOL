open HolKernel Parse boolLib bossLib;

val _ = new_theory "casePred";

Theorem foo:
  (case x of [] => F | h::t => h) ==> x <> []
Proof
  rw[CasePred "list"]
QED

Theorem bar:
  (case x of SOME h::t => h | _ => F) ==> x <> [NONE]
Proof
  rw[CasePreds ["list","option"]]
QED

Theorem baz:
  (case x of SOME h::t => h | _ => F) ==> x <> [NONE]
Proof
  rw[AllCasePreds()]
QED

val _ = export_theory();
