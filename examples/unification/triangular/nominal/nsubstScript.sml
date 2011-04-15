open HolKernel boolLib bossLib Parse finite_mapTheory arithmeticTheory prim_recTheory pred_setTheory relationTheory ntermTheory ramanaLib

val _ = new_theory "nsubst"

val _ = type_abbrev ("nsubst", ``:(num |-> 'a nterm)``);

val nvR_def = Define`
  nvR s y x = case FLOOKUP s x of SOME t -> y IN nvars t || _ -> F`;

val nwfs_def = Define`nwfs s = WF (nvR s)`;

val nwfs_FEMPTY = RWstore_thm(
"nwfs_FEMPTY",
`nwfs FEMPTY`,
SRW_TAC [][nwfs_def] THEN
Q_TAC SUFF_TAC `nvR FEMPTY = EMPTY_REL` THEN1 METIS_TAC [WF_EMPTY_REL] THEN
SRW_TAC [][FUN_EQ_THM,nvR_def])

val nwfs_no_cycles = Q.store_thm(
  "nwfs_no_cycles",
  `nwfs s <=> !v. ~(nvR s)^+ v v`,
  EQ_TAC THEN1 METIS_TAC [WF_TC,nwfs_def,WF_NOT_REFL] THEN
  SRW_TAC [] [nwfs_def,WF_IFF_WELLFOUNDED,wellfounded_def] THEN
  SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
  `!n. (f n) IN FDOM s /\ f (SUC n) IN nvars (s ' (f n))` by
    (STRIP_TAC THEN Q.PAT_ASSUM `!n.nvR s (f (SUC n)) (f n)` (Q.SPEC_THEN `n` MP_TAC)
     THEN FULL_SIMP_TAC (srw_ss()) [nvR_def] THEN Cases_on `FLOOKUP s (f n)` THEN
     Q.PAT_ASSUM `FLOOKUP s (f n) = Z` MP_TAC THEN SRW_TAC [] [FLOOKUP_DEF])
  THEN
  `!n m. (nvR s)^+ (f (SUC (n + m))) (f n)` by
    (REPEAT STRIP_TAC THEN Induct_on `m` THEN1
       (SRW_TAC [] [] THEN METIS_TAC [TC_SUBSET]) THEN
     Q.PAT_ASSUM `!n. f n IN FDOM s /\ Z` (Q.SPEC_THEN `SUC (n + m)` MP_TAC)
     THEN SRW_TAC [] [] THEN
     `(nvR s) (f (SUC (SUC (n + m)))) (f (SUC (n + m)))`
     by METIS_TAC [nvR_def,FLOOKUP_DEF] THEN
     METIS_TAC [TC_RULES,ADD_SUC])
  THEN
  `?n m. f (SUC (n + m)) = f n` by
    (`~INJ f (count (SUC (CARD (FDOM s)))) (FDOM s)`
         by (SRW_TAC [] [PHP,CARD_COUNT,COUNT_SUC,CARD_DEF]) THEN
     FULL_SIMP_TAC (srw_ss()) [INJ_DEF] THEN1 METIS_TAC [] THEN
     ASSUME_TAC (Q.SPECL [`x`,`y`] LESS_LESS_CASES) THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN1 METIS_TAC [] THENL [
       Q.EXISTS_TAC `x` THEN Q.EXISTS_TAC `y - x - 1`,
       Q.EXISTS_TAC `y` THEN Q.EXISTS_TAC `x - y - 1`
     ] THEN SRW_TAC [ARITH_ss] [ADD1])
  THEN METIS_TAC []);

val nwfs_SUBMAP = Q.store_thm(
"nwfs_SUBMAP",
`nwfs sx /\ s SUBMAP sx ==> nwfs s`,
SRW_TAC [][nwfs_def,SUBMAP_DEF] THEN
Q_TAC SUFF_TAC `!y x.nvR s y x ==> nvR sx y x`
  THEN1 METIS_TAC [WF_SUBSET] THEN
SRW_TAC [][nvR_def,FLOOKUP_DEF] THEN
METIS_TAC []);

val _ = export_theory ()
