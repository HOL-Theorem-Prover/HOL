Theory canonContext[bare]
Ancestors
  combin
Libs
  HolKernel Parse boolLib tautLib

(* ------------------------------------------------------------------------- *)
(* Lemmas Canon.sml formerly proved as it loaded.  Doing it in a proper      *)
(* theory removes the load-order sensitivity flagged by TAC_PROOF's          *)
(* current-theory check.                                                     *)
(* ------------------------------------------------------------------------- *)

(* ONEWAY_SKOLEM_CONV support *)

Theorem pth1: (?x:'a. P) <=> P
Proof
  REWRITE_TAC[EXISTS_SIMP]
QED

Theorem pth2:  (z:'a = $@ P) ==> ($? P <=> P z)
Proof
  DISCH_THEN SUBST1_TAC THEN
  CONV_TAC (LAND_CONV (RATOR_CONV (REWR_CONV boolTheory.EXISTS_DEF) THENC
                       BETA_CONV)) THEN
  REFL_TAC
QED

(* NNF_CONV / NNF_SKOLEM_CONV support *)

Theorem pth_pimp:  (p ==> q) <=> q \/ ~p
Proof TAUT_TAC
QED

Theorem pth_peq1:  (p = q) <=> (p \/ ~q) /\ (~p \/ q)
Proof TAUT_TAC
QED

Theorem pth_peq2:  (p = q) <=> (p /\ q) \/ (~p /\ ~q)
Proof TAUT_TAC
QED

Theorem pth_pcond1: (if p then q else q') <=> (p \/ q') /\ (~p \/ q)
Proof TAUT_TAC
QED

Theorem pth_pcond2: (if p then q else q') <=> (p /\ q) \/ (~p /\ q')
Proof TAUT_TAC
QED

Theorem pth_nnot:  ~~p:bool <=> p
Proof TAUT_TAC
QED

Theorem pth_nand:  ~(p /\ q) <=> ~p \/ ~q
Proof TAUT_TAC
QED

Theorem pth_nor:   ~(p \/ q) <=> ~p /\ ~q
Proof TAUT_TAC
QED

Theorem pth_nimp:  ~(p ==> q) <=> ~q /\ p
Proof TAUT_TAC
QED

Theorem pth_neq1:  ~(p = q) <=> (p \/ q) /\ (~p \/ ~q)
Proof TAUT_TAC
QED

Theorem pth_neq2:  ~(p = q) <=> (p /\ ~q) \/ (~p /\ q)
Proof TAUT_TAC
QED

Theorem pth_ncond1: ~(if p then q else q') <=> (p \/ ~q') /\ (~p \/ ~q)
Proof TAUT_TAC
QED

Theorem pth_ncond2: ~(if p then q else q') <=> (p /\ ~q) \/ (~p /\ ~q')
Proof TAUT_TAC
QED

Theorem EXISTS_UNIQUE_THM2:
  !P. (?!x:'a. P x) <=> (?x. P x /\ !y. P y ==> (y = x))
Proof
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    Q.EXISTS_TAC `x` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[],
    CONJ_TAC THEN1 (Q.EXISTS_TAC `x` THEN ASM_REWRITE_TAC[]) THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN Q.EXISTS_TAC `x` THEN
    CONJ_TAC THENL [
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[],
      CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]
    ]
  ]
QED

Theorem LOCAL_COND_ELIM_THM1:
  !P:'a->bool. P(if a then b else c) <=> (~a \/ P(b)) /\ (a \/ P(c))
Proof
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]
QED

Theorem LOCAL_COND_ELIM_THM2:
  !P:'a->bool. P(if a then b else c) <=> a /\ P(b) \/ ~a /\ P(c)
Proof
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]
QED

(* PROP_CNF_CONV support *)

Theorem cnf_th1:  a \/ (b /\ c) <=> (a \/ b) /\ (a \/ c)
Proof TAUT_TAC
QED

Theorem cnf_th2:  (a /\ b) \/ c <=> (a \/ c) /\ (b \/ c)
Proof TAUT_TAC
QED

(* PROP_DNF_CONV support *)

Theorem dnf_th1:  a /\ (b \/ c) <=> (a /\ b) \/ (a /\ c)
Proof TAUT_TAC
QED

Theorem dnf_th2:  (a \/ b) /\ c <=> (a /\ c) \/ (b /\ c)
Proof TAUT_TAC
QED

(* REFUTE support *)

Theorem refute_pth:    (~p ==> F) ==> p
Proof TAUT_TAC
QED

Theorem refute_pth_d:  (a \/ b) /\ c <=> (a /\ c) \/ (b /\ c)
Proof TAUT_TAC
QED

(* EQ_ABS_CONV support *)

Theorem eq_abs_pth:  (f:'a->'b = \x. t x) <=> (!x. f x = t x)
Proof
  REWRITE_TAC[FUN_EQ_THM, BETA_THM]
QED

(* UNLAMB_CONV support *)

Theorem unlamb_pth:  P (t:'a) <=> (!x. (x = t) ==> P x)
Proof
  EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN REFL_TAC
QED

(* FOL_CONV / APP_CONV support *)

Theorem app_conv_th:  !(f:'a->'b) x. f x = combin$I f x
Proof
  REWRITE_TAC[combinTheory.I_THM]
QED

(* DISJ_ACI_RULE support *)

Theorem disj_aci_left:   ~(a \/ b) ==> ~a
Proof TAUT_TAC
QED

Theorem disj_aci_right:  ~(a \/ b) ==> ~b
Proof TAUT_TAC
QED

Theorem disj_aci_pth:    ~a ==> ~b ==> ~(a \/ b)
Proof TAUT_TAC
QED

Theorem disj_aci_neg:    (~a <=> ~b) ==> (a <=> b)
Proof TAUT_TAC
QED
