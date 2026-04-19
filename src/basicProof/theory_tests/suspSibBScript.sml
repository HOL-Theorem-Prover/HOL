(*  Sibling-finalise suspend/resume test, part 2 of 4.

    Resumes lab1 only.  Does not finalise — that's D's job.
*)

Theory suspSibB[bare]
Ancestors suspSibA

Libs HolKernel Parse boolLib markerLib

Resume sib_thm[lab1]:
  ASM_REWRITE_TAC[]
QED
