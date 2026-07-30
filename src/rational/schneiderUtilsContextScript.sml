Theory schneiderUtilsContext[bare]
Libs
  HolKernel Parse boolLib

(* ------------------------------------------------------------------------- *)
(* Absorption lemmas schneiderUtils.sml formerly proved as it loaded.        *)
(* The third theorem (a case-split for booleans) is already in boolTheory as *)
(* FORALL_BOOL and is used directly there.                                   *)
(* ------------------------------------------------------------------------- *)

Theorem LEFT_ABSORB_DISJ:  !a b. a \/ b <=> a \/ (~a /\ b)
Proof
  REPEAT GEN_TAC THEN BOOL_CASES_TAC ``a:bool`` THEN REWRITE_TAC []
QED

Theorem RIGHT_ABSORB_DISJ:  !a b. a \/ b <=> (a /\ ~b) \/ b
Proof
  REPEAT GEN_TAC THEN BOOL_CASES_TAC ``b:bool`` THEN REWRITE_TAC []
QED
