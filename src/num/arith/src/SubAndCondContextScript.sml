Theory SubAndCondContext[bare]
Libs
  HolKernel Parse boolLib

(* ------------------------------------------------------------------------- *)
(* CASES_ELIM: pull a boolean under a predicate through cases on that        *)
(* boolean.  Sub_and_cond.sml formerly proved this as it loaded.             *)
(* ------------------------------------------------------------------------- *)

Theorem CASES_ELIM:
  !P p. P p <=> (p ==> P T) /\ (~p ==> P F)
Proof
  REPEAT GEN_TAC THEN ASM_CASES_TAC ``p:bool`` THEN ASM_REWRITE_TAC []
QED
