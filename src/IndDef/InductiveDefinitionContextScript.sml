Theory InductiveDefinitionContext[bare]
Libs
  HolKernel Parse boolLib

(* ------------------------------------------------------------------------- *)
(* Monotonicity theorems InductiveDefinition.sml formerly proved as it       *)
(* loaded.                                                                   *)
(* ------------------------------------------------------------------------- *)

Theorem MONO_EXISTS:
  (!x:'a. P x ==> Q x) ==> ($? P ==> $? Q)
Proof
  DISCH_THEN (MP_TAC o HO_MATCH_MP boolTheory.MONO_EXISTS) THEN
  CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[]
QED

Theorem MONO_FORALL:
  (!x:'a. P x ==> Q x) ==> ($! P ==> $! Q)
Proof
  DISCH_THEN (MP_TAC o HO_MATCH_MP boolTheory.MONO_ALL) THEN
  CONV_TAC (ONCE_DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[]
QED

Theorem MONO_RESFORALL:
  (!x:'a. P' x ==> P x) /\ (!x. Q x ==> Q' x) ==>
    (RES_FORALL P Q ==> RES_FORALL P' Q')
Proof
  REWRITE_TAC [RES_FORALL_THM, IN_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
  REPEAT (FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_REWRITE_TAC []
QED

Theorem MONO_RESEXISTS:
  (!x:'a. P x ==> P' x) /\ (!x. Q x ==> Q' x) ==>
    (RES_EXISTS P Q ==> RES_EXISTS P' Q')
Proof
  REWRITE_TAC [RES_EXISTS_THM, IN_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC ``x:'a`` THEN RES_TAC THEN ASM_REWRITE_TAC []
QED
