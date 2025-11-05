Theory dis_set
Ancestors
  string pred_set nomset list pair
Libs
  ramanaLib

val _ = metisTools.limit :=  { time = NONE, infs = SOME 5000 }

Definition dis_set_def:
  dis_set pi1 pi2 = { a | lswapstr pi1 a ≠ lswapstr pi2 a }
End

Theorem dis_set_SUBSET_patoms:
 dis_set pi1 pi2 SUBSET patoms pi1 UNION patoms pi2
Proof
SRW_TAC [][dis_set_def,EXTENSION,SUBSET_DEF] THEN
METIS_TAC [lswapstr_unchanged]
QED

val FINITE_dis_set = RWstore_thm(
"FINITE_dis_set",
`FINITE (dis_set pi1 pi2)`,
METIS_TAC [SUBSET_FINITE,FINITE_patoms,FINITE_UNION,dis_set_SUBSET_patoms]);

Theorem dis_set_eq_perms:
 p1 == q1 ⇒ p2 == q2 ⇒ (dis_set p1 p2 = dis_set q1 q2)
Proof
SRW_TAC [][dis_set_def,EXTENSION] THEN
METIS_TAC [pmact_permeq]
QED

Definition pnomsl_def[simp]:
  (pnomsl [] = []) ∧
  (pnomsl ((a1,a2)::t) = a1::a2::pnomsl t)
End

Theorem set_pnomsl_EQ_patoms:
 set (pnomsl pi) = patoms pi
Proof
Induct_on `pi` THEN ASM_SIMP_TAC (srw_ss()) [FORALL_PROD] THEN
SRW_TAC [][EXTENSION,DISJ_ASSOC]
QED

Theorem pnomsl_APPEND:
 pnomsl (l1 ++ l2) = pnomsl l1 ++ pnomsl l2
Proof
Induct_on `l1` THEN ASM_SIMP_TAC (srw_ss()) [FORALL_PROD]
QED

Definition DISTINCT_def[simp]:
  (DISTINCT [] = []) ∧
  (DISTINCT (h::t) = if MEM h t then DISTINCT t else (h::DISTINCT t))
End

Theorem MEM_DISTINCT:
 MEM e (DISTINCT ls) ⇔ MEM e ls
Proof
Induct_on `ls` THEN SRW_TAC [][] THEN METIS_TAC []
QED

Theorem ALL_DISTINCT_DISTINCT:
 ALL_DISTINCT (DISTINCT ls)
Proof
Induct_on `ls` THEN SRW_TAC [][] THEN
METIS_TAC [MEM_DISTINCT]
QED

Definition dis_list_def:
  dis_list pi1 pi2 =
    DISTINCT (FILTER (λa. lswapstr pi1 a ≠ lswapstr pi2 a)
                     (pnomsl (pi1 ++ pi2)))
End

Theorem dis_list_eq_dis_set:
 set (dis_list pi1 pi2) = dis_set pi1 pi2
Proof
SRW_TAC [][EXTENSION,EQ_IMP_THM] THENL [
  SRW_TAC [][dis_set_def] THEN
  FULL_SIMP_TAC (srw_ss()) [dis_list_def,MEM_DISTINCT,MEM_FILTER],
  FULL_SIMP_TAC (srw_ss()) [dis_set_def] THEN
  SRW_TAC [][dis_list_def,MEM_FILTER,MEM_DISTINCT] THEN
  FULL_SIMP_TAC(srw_ss()) [pmact_eql, GSYM pmact_decompose] THEN
  `x IN patoms (pi1⁻¹ ++ pi2)` by METIS_TAC [lswapstr_unchanged] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  FULL_SIMP_TAC (srw_ss()) [GSYM set_pnomsl_EQ_patoms,pnomsl_APPEND]
]
QED

Theorem dis_set_app_same:
 a IN dis_set (p1 ++ pi) (p2 ++ pi) ⇔ (lswapstr pi a) IN dis_set p1 p2
Proof
SRW_TAC [][dis_set_def,pmact_decompose]
QED

Theorem dis_set_app_same_left:
 a IN dis_set (pi ++ p1) (pi ++ p2) ⇔ a IN dis_set p1 p2
Proof
SRW_TAC [][dis_set_def,pmact_decompose]
QED

Theorem dis_set_comm:
 dis_set p1 p2 = dis_set p2 p1
Proof
SRW_TAC [][dis_set_def,EXTENSION,EQ_IMP_THM]
QED

