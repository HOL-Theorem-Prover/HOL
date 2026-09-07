Theory Canon_Port_Context[bare]
Ancestors
  combin
Libs
  HolKernel Parse boolLib tautLib

(* ------------------------------------------------------------------------- *)
(* Lemmas Canon_Port.sml formerly proved as it loaded.                       *)
(* ------------------------------------------------------------------------- *)

Theorem APP_EQ_I:  !(f:'a->'b) x. f x = I f x
Proof REWRITE_TAC[combinTheory.I_THM]
QED

Theorem NOT_EXISTS_UNIQUE_THM:
  ~(?!x:'a. P x) <=> (!x. ~P x) \/ ?x x'. P x /\ P x' /\ ~(x = x')
Proof
  REWRITE_TAC [EXISTS_UNIQUE_THM, DE_MORGAN_THM, NOT_EXISTS_THM] THEN
  CONV_TAC (REDEPTH_CONV NOT_FORALL_CONV) THEN
  REWRITE_TAC [NOT_IMP, CONJ_ASSOC]
QED

Theorem cp_not_not:   ~~p:bool <=> p
Proof tautLib.TAUT_TAC
QED

Theorem cp_not_and:   ~(p /\ q) <=> ~p \/ ~q
Proof tautLib.TAUT_TAC
QED

Theorem cp_not_or:    ~(p \/ q) <=> ~p /\ ~q
Proof tautLib.TAUT_TAC
QED

Theorem cp_not_imp:   ~(p ==> q) <=> p /\ ~q
Proof tautLib.TAUT_TAC
QED

Theorem cp_imp:       p ==> q <=> ~p \/ q
Proof tautLib.TAUT_TAC
QED

Theorem cp_not_eq_dnf: ~(p = q) <=> (p /\ ~q) \/ (~p /\ q)
Proof tautLib.TAUT_TAC
QED

Theorem cp_eq_dnf:     (p = q) <=> (p /\ q) \/ (~p /\ ~q)
Proof tautLib.TAUT_TAC
QED

Theorem cp_not_eq_cnf: ~(p = q) <=> (p \/ q) /\ (~p \/ ~q)
Proof tautLib.TAUT_TAC
QED

Theorem cp_eq_cnf:     (p = q) <=> (p \/ ~q) /\ (~p \/ q)
Proof tautLib.TAUT_TAC
QED

Theorem DELAMB_PTH:
  (((\x. s x) = t) <=> (!x:'a. s x:'b = t x)) /\
   ((s = \x. t x) <=> (!x. s x = t x))
Proof
  CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC THEN REWRITE_TAC []
QED

Theorem cp_cnf_l:  a \/ (b /\ c) <=> (a \/ b) /\ (a \/ c)
Proof tautLib.TAUT_TAC
QED

Theorem cp_cnf_r:  (a /\ b) \/ c <=> (a \/ c) /\ (b \/ c)
Proof tautLib.TAUT_TAC
QED

Theorem cp_refute:  p <=> ~p ==> F
Proof tautLib.TAUT_TAC
QED
