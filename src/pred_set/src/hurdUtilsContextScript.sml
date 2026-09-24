Theory hurdUtilsContext[bare]
Libs
  HolKernel Parse boolLib

(* ------------------------------------------------------------------------- *)
(* Small boolean lemmas hurdUtils.sml formerly derived at load time via      *)
(* DECIDE (which fires TAUT_PROVE and hence prove).                          *)
(* ------------------------------------------------------------------------- *)

Theorem EQ_NEG_T:  !a. (~a <=> T) <=> (a <=> F)
Proof REPEAT STRIP_TAC THEN BOOL_CASES_TAC ``a:bool`` THEN REWRITE_TAC []
QED

Theorem EQ_NEG_F:  !a. (~a <=> F) <=> (a <=> T)
Proof REPEAT STRIP_TAC THEN BOOL_CASES_TAC ``a:bool`` THEN REWRITE_TAC []
QED

Theorem STRONG_CONJ_lem:  !a b. a /\ (a ==> b) ==> a /\ b
Proof REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN RES_TAC
QED
