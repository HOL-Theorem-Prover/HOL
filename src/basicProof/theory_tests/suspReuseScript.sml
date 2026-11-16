(*  Suspends, resumes and finalises reuse_thm, then suspends and
    resumes a different statement under the same name and label,
    leaving it pending.  suspCompact checks that only the second
    statement's adds stay in this theory's data. *)

Theory suspReuse[bare]

Libs HolKernel Parse boolLib markerLib

Theorem reuse_thm:
  p ==> T
Proof
  suspend "l"
QED

Resume reuse_thm[l]:
  strip_tac >> ACCEPT_TAC TRUTH
QED

Finalise reuse_thm

Theorem reuse_thm:
  q ==> T
Proof
  suspend "l"
QED

Resume reuse_thm[l]:
  strip_tac >> ACCEPT_TAC TRUTH
QED
