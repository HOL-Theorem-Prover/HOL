open HolKernel boolLib bossLib Parse stringTheory pred_setTheory nomsetTheory listTheory ramanaLib pairTheory

val _ = new_theory "dis_set"
val _ = metisTools.limit :=  { time = NONE, infs = SOME 5000 }

val dis_set_def = Define`
  dis_set pi1 pi2 = { a | perm_of pi1 a ≠ perm_of pi2 a }`

val dis_set_SUBSET_patoms = Q.store_thm(
"dis_set_SUBSET_patoms",
`dis_set pi1 pi2 SUBSET patoms pi1 UNION patoms pi2`,
SRW_TAC [][dis_set_def,EXTENSION,SUBSET_DEF] THEN
METIS_TAC [perm_of_unchanged]);

val FINITE_dis_set = RWstore_thm(
"FINITE_dis_set",
`FINITE (dis_set pi1 pi2)`,
METIS_TAC [SUBSET_FINITE,FINITE_patoms,FINITE_UNION,dis_set_SUBSET_patoms]);

val dis_set_eq_perms = Q.store_thm(
"dis_set_eq_perms",
`p1 == q1 ⇒ p2 == q2 ⇒ (dis_set p1 p2 = dis_set q1 q2)`,
SRW_TAC [][dis_set_def,EXTENSION] THEN
METIS_TAC [ntermTheory.lswapstr_eq_perms])

val pnomsl_def = RWDefine`
  (pnomsl [] = []) ∧
  (pnomsl ((a1,a2)::t) = a1::a2::pnomsl t)`;

val set_pnomsl_EQ_patoms = Q.store_thm(
"set_pnomsl_EQ_patoms",
`set (pnomsl pi) = patoms pi`,
Induct_on `pi` THEN ASM_SIMP_TAC (srw_ss()) [FORALL_PROD] THEN
SRW_TAC [][EXTENSION,DISJ_ASSOC]);

val pnomsl_APPEND = Q.store_thm(
"pnomsl_APPEND",
`pnomsl (l1 ++ l2) = pnomsl l1 ++ pnomsl l2`,
Induct_on `l1` THEN ASM_SIMP_TAC (srw_ss()) [FORALL_PROD]);

val DISTINCT_def = RWDefine`
  (DISTINCT [] = []) ∧
  (DISTINCT (h::t) = if MEM h t then DISTINCT t else (h::DISTINCT t))`;

val MEM_DISTINCT = Q.store_thm(
"MEM_DISTINCT",
`MEM e (DISTINCT ls) ⇔ MEM e ls`,
Induct_on `ls` THEN SRW_TAC [][] THEN METIS_TAC []);

val ALL_DISTINCT_DISTINCT = Q.store_thm(
"ALL_DISTINCT_DISTINCT",
`ALL_DISTINCT (DISTINCT ls)`,
Induct_on `ls` THEN SRW_TAC [][] THEN
METIS_TAC [MEM_DISTINCT]);

val dis_list_def = Define`
  dis_list pi1 pi2 = DISTINCT (FILTER (λa. perm_of pi1 a ≠ perm_of pi2 a) (pnomsl (pi1 ++ pi2)))`;

val dis_list_eq_dis_set = Q.store_thm(
"dis_list_eq_dis_set",
`set (dis_list pi1 pi2) = dis_set pi1 pi2`,
SRW_TAC [][EXTENSION,EQ_IMP_THM] THENL [
  SRW_TAC [][dis_set_def] THEN
  FULL_SIMP_TAC (srw_ss()) [dis_list_def,MEM_DISTINCT,MEM_FILTER],
  FULL_SIMP_TAC (srw_ss()) [dis_set_def] THEN
  SRW_TAC [][dis_list_def,MEM_FILTER,MEM_DISTINCT] THEN
  FULL_SIMP_TAC(srw_ss()) [basic_swapTheory.lswapstr_eqr] THEN
  FULL_SIMP_TAC(srw_ss()) [GSYM basic_swapTheory.lswapstr_APPEND] THEN
  `x IN patoms ((REVERSE pi2) ++ pi1)` by METIS_TAC [perm_of_unchanged] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  FULL_SIMP_TAC (srw_ss()) [GSYM set_pnomsl_EQ_patoms,pnomsl_APPEND]
]);

val dis_set_app_same = Q.store_thm(
"dis_set_app_same",
`a IN dis_set (p1 ++ pi) (p2 ++ pi) ⇔ (lswapstr pi a) IN dis_set p1 p2`,
SRW_TAC [][dis_set_def,ntermTheory.lswapstr_decompose])

val dis_set_app_same_left = Q.store_thm(
"dis_set_app_same_left",
`a IN dis_set (pi ++ p1) (pi ++ p2) ⇔ a IN dis_set p1 p2`,
SRW_TAC [][dis_set_def,ntermTheory.lswapstr_decompose])

val dis_set_comm = Q.store_thm(
"dis_set_comm",
`dis_set p1 p2 = dis_set p2 p1`,
SRW_TAC [][dis_set_def,EXTENSION,EQ_IMP_THM])

val _ = export_theory ();
