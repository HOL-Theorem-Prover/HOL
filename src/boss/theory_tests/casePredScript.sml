Theory casePred

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

