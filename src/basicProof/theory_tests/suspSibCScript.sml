(*  Sibling-finalise suspend/resume test, part 3 of 4.

    Resumes lab2 only, independently of suspSibB.
*)

Theory suspSibC[bare]
Ancestors suspSibA

Libs HolKernel Parse boolLib markerLib

Resume sib_thm[lab2]:
  RES_TAC
QED
