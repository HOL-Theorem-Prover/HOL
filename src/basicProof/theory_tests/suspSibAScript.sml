(*  Sibling-finalise suspend/resume test, part 1 of 4.

    A suspends a theorem with labels lab1 and lab2.  Siblings B and C
    resume one label each; grandchild D finalises.  Tests that the
    pure design in #1883 supports independent cross-file resumption.
*)

Theory suspSibA[bare]

Libs HolKernel Parse boolLib markerLib

Theorem sib_thm:
  p ∧ (p ⇒ q) ⇒ p ∧ q
Proof
  strip_tac >> conj_tac
  >- suspend "lab1"
  >- suspend "lab2"
QED
