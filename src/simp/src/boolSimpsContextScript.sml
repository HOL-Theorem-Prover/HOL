Theory boolSimpsContext[bare]
Ancestors
  combin
Libs
  HolKernel Parse boolLib

(* ------------------------------------------------------------------------- *)
(* Lemmas boolSimps.sml formerly proved as it loaded.                        *)
(* ------------------------------------------------------------------------- *)

Theorem literal_cong:
  (v:'a = v') ==> (literal_case (f:'a -> 'b) v = literal_case f (I v'))
Proof
  DISCH_THEN SUBST_ALL_TAC THEN
  REWRITE_TAC [literal_case_THM, combinTheory.I_THM]
QED

Theorem literal_I_thm:
  literal_case (f:'a -> 'b) (I x) = f x
Proof
  REWRITE_TAC [combinTheory.I_THM, literal_case_THM]
QED

Theorem let_cong:
  (v:'a = v') ==> (LET (f:'a -> 'b) v = LET f (I v'))
Proof
  DISCH_THEN SUBST_ALL_TAC THEN
  REWRITE_TAC [LET_THM, combinTheory.I_THM]
QED

Theorem let_I_thm:
  LET (f:'a -> 'b) (I x) = f x
Proof
  REWRITE_TAC [combinTheory.I_THM, LET_THM]
QED

Theorem NESTED_COND:
  !p (q:'a) (r:'a) s.
    (COND p (COND p q r) s = COND p q s) /\
    (COND p q (COND p r s) = COND p q s) /\
    (COND p (COND (~p) q r) s = COND p r s) /\
    (COND p q (COND (~p) r s) = COND p q r)
Proof
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC []
QED
