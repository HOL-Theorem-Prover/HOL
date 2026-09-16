Theory pairToolsContext[bare]
Ancestors
  pair
Libs
  HolKernel Parse boolLib

(* ------------------------------------------------------------------------- *)
(* Lemmas pairTools.sml formerly proved as it loaded.                        *)
(* ------------------------------------------------------------------------- *)

Theorem ELIM_PEXISTS2:
  (?p:('a#'b). P (FST p) (SND p) p) <=> ?p1 p2. P p1 p2 (p1, p2)
Proof
  CONV_TAC (LHS_CONV (HO_REWR_CONV pairTheory.EXISTS_PROD)) THEN
  REWRITE_TAC [pairTheory.FST, pairTheory.SND]
QED

Theorem ELIM_PFORALL2:
  (!p:('a#'b). P (FST p) (SND p) p) <=> !p1 p2. P p1 p2 (p1, p2)
Proof
  CONV_TAC (LHS_CONV (HO_REWR_CONV pairTheory.FORALL_PROD)) THEN
  REWRITE_TAC [pairTheory.FST, pairTheory.SND]
QED

Theorem PFORALL_THM2:
  !P:'a->'b->bool. (!x. $! (P x)) <=> $! (UNCURRY P)
Proof
  GEN_TAC THEN
  Q.SUBGOAL_THEN `P = (\x y. P x y)`
     (fn thm => ONCE_ASM_REWRITE_TAC [thm])
  THEN1 (REWRITE_TAC [FUN_EQ_THM] THEN BETA_TAC THEN REWRITE_TAC []) THEN
  BETA_TAC THEN REWRITE_TAC [pairTheory.PFORALL_THM]
QED

Theorem PEXISTS_THM2:
  !P:'a->'b->bool. (?x. $? (P x)) <=> $? (UNCURRY P)
Proof
  GEN_TAC THEN
  Q.SUBGOAL_THEN `P = (\x y. P x y)`
     (fn thm => ONCE_ASM_REWRITE_TAC [thm])
  THEN1 (REWRITE_TAC [FUN_EQ_THM] THEN BETA_TAC THEN REWRITE_TAC []) THEN
  BETA_TAC THEN REWRITE_TAC [pairTheory.PEXISTS_THM]
QED
