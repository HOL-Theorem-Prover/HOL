Theory resumeFail[bare]

(* A failing Resume under --noqof must CHEAT and let the build continue.
   Issue #2074: the dump written on the way through used to be saved at a
   hard-coded hierarchy depth of 1, which demotes every deeper level of
   the running heap.  markerLib's AncestryData slots are identified by the
   generative exception constructors behind UniversalType.embed, so a
   resume in flight across that save met post-demotion identities and died
   with Option -- defeating the very flag meant to keep going.

   [bare] with an explicit Libs line, as the sibling suspension tests in
   src/basicProof/theory_tests use: this directory is built long before
   holTheory and bossLib exist, so the default Theory opens are not
   available. *)

Libs HolKernel Parse boolLib markerLib BasicProvers

Theorem lemma:
  T /\ T
Proof
  CONJ_TAC >- suspend "a" >- suspend "b"
QED

Resume lemma[a]:
  FAIL_TAC "deliberate"
QED

Resume lemma[b]:
  ACCEPT_TAC TRUTH
QED

Finalise lemma
