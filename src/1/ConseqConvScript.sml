Theory ConseqConv[bare]
Ancestors
  bool
Libs
  HolKernel Parse Drule Tactical Tactic Conv Rewrite

Theorem forall_eq_thm:
     (!s:'a. (P s = Q s)) ==> ((!s. P s) = (!s. Q s))
Proof
     STRIP_TAC THEN ASM_REWRITE_TAC[]
QED

Theorem exists_eq_thm:
     (!s:'a. (P s = Q s)) ==> ((?s. P s) = (?s. Q s))
Proof
     STRIP_TAC THEN ASM_REWRITE_TAC[]
QED


Theorem true_imp:   !t. t ==> T
Proof REWRITE_TAC[]
QED
Theorem false_imp:   !t. F ==> t
Proof REWRITE_TAC[]
QED


val NOT_CLAUSES_THML = CONJUNCTS NOT_CLAUSES
Theorem NOT_CLAUSES_X = el 1 NOT_CLAUSES_THML
Theorem NOT_CLAUSES_T = el 2 NOT_CLAUSES_THML
Theorem NOT_CLAUSES_F = el 3 NOT_CLAUSES_THML

Theorem IMP_CONG_conj_strengthen:
  !x x' y y'.
  ((y ==> (x' ==> x)) /\ (x' ==> (y' ==> y))) ==>
  ((x' /\ y') ==> (x /\ y))
Proof
Ho_Rewrite.REWRITE_TAC [FORALL_BOOL]
QED

Theorem IMP_CONG_conj_weaken:
  !x x' y y'.
  ((y ==> (x ==> x')) /\ (x' ==> (y ==> y'))) ==>
  ((x /\ y) ==> (x' /\ y'))
Proof
Ho_Rewrite.REWRITE_TAC [FORALL_BOOL]
QED


val AND_CLAUSES_THML =
     (CONJUNCTS (Ho_Rewrite.PURE_REWRITE_RULE [FORALL_AND_THM] AND_CLAUSES))

Theorem AND_CLAUSES_TX = el 1 AND_CLAUSES_THML;
Theorem AND_CLAUSES_XT = el 2 AND_CLAUSES_THML;
Theorem AND_CLAUSES_FX = el 3 AND_CLAUSES_THML;
Theorem AND_CLAUSES_XF = el 4 AND_CLAUSES_THML;
Theorem AND_CLAUSES_XX = el 5 AND_CLAUSES_THML;


Theorem IMP_CONG_disj_strengthen:
  !x x' y y'.
  ((~y ==> (x' ==> x)) /\ (~x' ==> (y' ==> y))) ==>
  ((x' \/ y') ==> (x \/ y))
Proof
Ho_Rewrite.REWRITE_TAC [FORALL_BOOL]
QED


Theorem IMP_CONG_disj_weaken:
  !x x' y y'.
  ((~y ==> (x ==> x')) /\ (~x' ==> (y ==> y'))) ==>
  ((x \/ y) ==> (x' \/ y'))
Proof
Ho_Rewrite.REWRITE_TAC [FORALL_BOOL]
QED


val OR_CLAUSES_THML =
     (CONJUNCTS (Ho_Rewrite.PURE_REWRITE_RULE [FORALL_AND_THM] OR_CLAUSES))

val OR_CLAUSES_TX = save_thm ("OR_CLAUSES_TX", el 1 OR_CLAUSES_THML)
val OR_CLAUSES_XT = save_thm ("OR_CLAUSES_XT", el 2 OR_CLAUSES_THML)
val OR_CLAUSES_FX = save_thm ("OR_CLAUSES_FX", el 3 OR_CLAUSES_THML)
val OR_CLAUSES_XF = save_thm ("OR_CLAUSES_XF", el 4 OR_CLAUSES_THML)
val OR_CLAUSES_XX = save_thm ("OR_CLAUSES_XX", el 5 OR_CLAUSES_THML)




Theorem IMP_CONG_imp_strengthen:
  !x x' y y'.
  ((x ==> (y' ==> y)) /\ (~y' ==> (x ==> x'))) ==>
  ((x' ==> y') ==> (x ==> y))
Proof
  Ho_Rewrite.REWRITE_TAC [FORALL_BOOL]
QED

Theorem IMP_CONG_imp_weaken:
  !x x' y y'.
  ((x ==> (y ==> y')) /\ (~y' ==> (x' ==> x))) ==>
  ((x ==> y) ==> (x' ==> y'))
Proof
  Ho_Rewrite.REWRITE_TAC [FORALL_BOOL]
QED


Theorem IMP_CONG_simple_imp_strengthen:
  !x x' y y'.
  ((x ==> x') /\ (x' ==> (y' ==> y))) ==>
  ((x' ==> y') ==> (x ==> y))
Proof
  Ho_Rewrite.REWRITE_TAC [FORALL_BOOL]
QED

Theorem IMP_CONG_simple_imp_weaken:
  !x x' y y'.
  ((x' ==> x) /\ (x' ==> (y ==> y'))) ==>
  ((x ==> y) ==> (x' ==> y'))
Proof
  Ho_Rewrite.REWRITE_TAC [FORALL_BOOL]
QED


val IMP_CLAUSES_THML =
     (CONJUNCTS (Ho_Rewrite.PURE_REWRITE_RULE [FORALL_AND_THM] IMP_CLAUSES))

val IMP_CLAUSES_TX = save_thm ("IMP_CLAUSES_TX", el 1 IMP_CLAUSES_THML)
val IMP_CLAUSES_XT = save_thm ("IMP_CLAUSES_XT", el 2 IMP_CLAUSES_THML)
val IMP_CLAUSES_FX = save_thm ("IMP_CLAUSES_FX", el 3 IMP_CLAUSES_THML)
val IMP_CLAUSES_XX = save_thm ("IMP_CLAUSES_XX", el 4 IMP_CLAUSES_THML)
val IMP_CLAUSES_XF = save_thm ("IMP_CLAUSES_XF", el 5 IMP_CLAUSES_THML)



Theorem IMP_CONG_cond_simple:
  !c x x' y y'.
  ((x' ==> x) /\ (y' ==> y)) ==>
  ((if c then x' else y') ==> (if c then x else y))
Proof
Ho_Rewrite.REWRITE_TAC [FORALL_BOOL]
QED

Theorem IMP_CONG_cond:
  !c x x' y y'.
  ((c ==> (x' ==> x)) /\ (~c ==> (y' ==> y))) ==>
  ((if c then x' else y') ==> (if c then x else y))
Proof
Ho_Rewrite.REWRITE_TAC [FORALL_BOOL]
QED



val COND_CLAUSES_THML =
     (CONJUNCTS (Ho_Rewrite.PURE_REWRITE_RULE [FORALL_AND_THM] COND_CLAUSES))
fun bool_save_thm (s,t) = store_thm (s, t, Ho_Rewrite.REWRITE_TAC [FORALL_BOOL])

val COND_CLAUSES_CT = save_thm ("COND_CLAUSES_CT", el 1 COND_CLAUSES_THML)
val COND_CLAUSES_CF = save_thm ("COND_CLAUSES_CF", el 2 COND_CLAUSES_THML)
val COND_CLAUSES_ID = save_thm ("COND_CLAUSES_ID", COND_ID)
val COND_CLAUSES_TT = bool_save_thm ("COND_CLAUSES_TT",
       ``!c x. (if c then T else x) = (~c ==> x)``)
val COND_CLAUSES_FT = bool_save_thm ("COND_CLAUSES_FT",
       ``!c x. (if c then x else T) = (c ==> x)``)
val COND_CLAUSES_TF = bool_save_thm ("COND_CLAUSES_TF",
       ``!c x. (if c then F else x) = (~c /\ x)``)
val COND_CLAUSES_FF = bool_save_thm ("COND_CLAUSES_FF",
       ``!c x. (if c then x else F) = (c /\ x)``)


val ASM_MARKER_DEF =
 Definition.new_definition
   ("ASM_MARKER_DEF", Term `ASM_MARKER = (\ (y:bool) x:bool. x)`);

Theorem ASM_MARKER_THM:
  !y x. ASM_MARKER y x = x
Proof
REWRITE_TAC[ASM_MARKER_DEF] THEN
BETA_TAC THEN REWRITE_TAC []
QED


