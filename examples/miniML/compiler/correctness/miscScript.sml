open HolKernel bossLib boolLib boolSimps listTheory pred_setTheory finite_mapTheory alistTheory lcsymtacs
val _ = new_theory "misc"

(* Misc. lemmas (without any compiler constants) *)

val FOLDR_CONS_triple = store_thm(
"FOLDR_CONS_triple",
``!f ls a. FOLDR (\(x,y,z) w. f x y z :: w) a ls = (MAP (\(x,y,z). f x y z) ls)++a``,
GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
Q.X_GEN_TAC `p` THEN
PairCases_on `p` THEN
SRW_TAC[][])

val FOLDL2_FUPDATE_LIST = store_thm(
"FOLDL2_FUPDATE_LIST",
``!f1 f2 bs cs a. (LENGTH bs = LENGTH cs) ⇒
  (FOLDL2 (λfm b c. fm |+ (f1 b c, f2 b c)) a bs cs =
   a |++ ZIP (MAP2 f1 bs cs, MAP2 f2 bs cs))``,
SRW_TAC[][FUPDATE_LIST,FOLDL2_FOLDL,MAP2_MAP,ZIP_MAP,MAP_ZIP,
          rich_listTheory.FOLDL_MAP,rich_listTheory.LENGTH_MAP2,
          LENGTH_ZIP,pairTheory.LAMBDA_PROD])

val FOLDL2_FUPDATE_LIST_paired = store_thm(
"FOLDL2_FUPDATE_LIST_paired",
``!f1 f2 bs cs a. (LENGTH bs = LENGTH cs) ⇒
  (FOLDL2 (λfm b (c,d). fm |+ (f1 b c d, f2 b c d)) a bs cs =
   a |++ ZIP (MAP2 (λb. UNCURRY (f1 b)) bs cs, MAP2 (λb. UNCURRY (f2 b)) bs cs))``,
rw[FOLDL2_FOLDL,MAP2_MAP,ZIP_MAP,MAP_ZIP,LENGTH_ZIP,
   pairTheory.UNCURRY,pairTheory.LAMBDA_PROD,FUPDATE_LIST,
   rich_listTheory.FOLDL_MAP])

val FOLDL_FUPDATE_LIST = store_thm(
"FOLDL_FUPDATE_LIST",
``!f1 f2 ls a. FOLDL (\fm k. fm |+ (f1 k, f2 k)) a ls =
  a |++ MAP (\k. (f1 k, f2 k)) ls``,
SRW_TAC[][FUPDATE_LIST,rich_listTheory.FOLDL_MAP])

val FUN_FMAP_FAPPLY_FEMPTY_FAPPLY = store_thm(
"FUN_FMAP_FAPPLY_FEMPTY_FAPPLY",
``FINITE s ==> (FUN_FMAP ($FAPPLY FEMPTY) s ' x = FEMPTY ' x)``,
Cases_on `x IN s` >>
rw[FUN_FMAP_DEF,NOT_FDOM_FAPPLY_FEMPTY])
val _ = export_rewrites["FUN_FMAP_FAPPLY_FEMPTY_FAPPLY"]

val FUPDATE_LIST_APPLY_NOT_MEM_matchable = store_thm(
"FUPDATE_LIST_APPLY_NOT_MEM_matchable",
``!kvl f k v. ~MEM k (MAP FST kvl) /\ (v = f ' k) ==> ((f |++ kvl) ' k = v)``,
PROVE_TAC[FUPDATE_LIST_APPLY_NOT_MEM])

val FST_triple = store_thm(
"FST_triple",
``(λ(n,ns,b). n) = FST``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val SND_triple = store_thm(
"SND_triple",
``(λ(n,ns,b). f ns b) = UNCURRY f o SND``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val FST_pair = store_thm(
"FST_pair",
``(λ(n,v). n) = FST``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val SND_pair = store_thm(
"SND_pair",
``(λ(n,v). v) = SND``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val SND_FST_pair = store_thm(
"SND_FST_pair",
``(λ((n,m),c).m) = SND o FST``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val set_MAP_FST_fmap_to_alist = store_thm(
"set_MAP_FST_fmap_to_alist",
``set (MAP FST (fmap_to_alist fm)) = FDOM fm``,
METIS_TAC[fmap_to_alist_to_fmap,FDOM_alist_to_fmap])
val _ = export_rewrites["set_MAP_FST_fmap_to_alist"]

val INJ_I = store_thm(
"INJ_I",
``∀s t. INJ I s t = s ⊆ t``,
SRW_TAC[][INJ_DEF,SUBSET_DEF])

val MAP_KEYS_I = store_thm(
"MAP_KEYS_I",
``∀fm. MAP_KEYS I fm = fm``,
rw[GSYM fmap_EQ_THM,MAP_KEYS_def,EXTENSION] >>
metis_tac[MAP_KEYS_def,INJ_I,SUBSET_UNIV,combinTheory.I_THM])
val _ = export_rewrites["MAP_KEYS_I"]

val MAP_EQ_ID = store_thm(
"MAP_EQ_ID",
``!f ls. (MAP f ls = ls) = (!x. MEM x ls ==> (f x = x))``,
PROVE_TAC[MAP_EQ_f,MAP_ID,combinTheory.I_THM])

(* TODO: move *)
val LIST_REL_EVERY_ZIP = store_thm(
"LIST_REL_EVERY_ZIP",
``!R l1 l2. LIST_REL R l1 l2 = ((LENGTH l1 = LENGTH l2) /\ EVERY (UNCURRY R) (ZIP (l1,l2)))``,
GEN_TAC THEN Induct THEN SRW_TAC[][LENGTH_NIL_SYM] THEN
SRW_TAC[][EQ_IMP_THM,LIST_REL_CONS1] THEN SRW_TAC[][] THEN
Cases_on `l2` THEN FULL_SIMP_TAC(srw_ss())[])

val MAP_ZIP_SND_triple = store_thm(
"MAP_ZIP_SND_triple",
``(LENGTH l1 = LENGTH l2) ⇒ (MAP (λ(x,y,z). f y z) (ZIP(l1,l2)) = MAP (UNCURRY f) l2)``,
strip_tac >> (
MAP_ZIP
|> Q.GEN`g`
|> Q.ISPEC `UNCURRY (f:'b->'c->'d)`
|> SIMP_RULE(srw_ss())[combinTheory.o_DEF,pairTheory.LAMBDA_PROD]
|> UNDISCH_ALL
|> CONJUNCTS
|> Lib.el 4
|> MATCH_ACCEPT_TAC))

val FUPDATE_LIST_APPLY_HO_THM = store_thm(
"FUPDATE_LIST_APPLY_HO_THM",
``∀P f kvl k.
(∃n. n < LENGTH kvl ∧ (k = EL n (MAP FST kvl)) ∧ P (EL n (MAP SND kvl)) ∧
     (∀m. n < m ∧ m < LENGTH kvl ⇒ EL m (MAP FST kvl) ≠ k)) ∨
(¬MEM k (MAP FST kvl) ∧ P (f ' k))
⇒ (P ((f |++ kvl) ' k))``,
metis_tac[FUPDATE_LIST_APPLY_MEM,FUPDATE_LIST_APPLY_NOT_MEM])

val LESS_1 = store_thm(
"LESS_1",
``x < 1 = (x = 0:num)``,
DECIDE_TAC)
val _ = export_rewrites["LESS_1"]

val FRANGE_FUPDATE_LIST_SUBSET = store_thm(
"FRANGE_FUPDATE_LIST_SUBSET",
``∀ls fm. FRANGE (fm |++ ls) ⊆ FRANGE fm ∪ (set (MAP SND ls))``,
Induct >- rw[FUPDATE_LIST_THM] >>
qx_gen_tac `p` >> qx_gen_tac `fm` >>
pop_assum (qspec_then `fm |+ p` mp_tac) >>
srw_tac[DNF_ss][SUBSET_DEF] >>
first_x_assum (qspec_then `x` mp_tac) >> fs[FUPDATE_LIST_THM] >>
rw[] >> fs[] >>
PairCases_on `p` >>
fsrw_tac[DNF_ss][FRANGE_FLOOKUP,FLOOKUP_UPDATE] >>
pop_assum mp_tac >> rw[] >>
PROVE_TAC[])

val IN_FRANGE_FUPDATE_LIST_suff = store_thm(
"IN_FRANGE_FUPDATE_LIST_suff",
``(∀v. v ∈ FRANGE fm ⇒ P v) ∧ (∀v. MEM v (MAP SND ls) ⇒ P v) ⇒
    ∀v. v ∈ FRANGE (fm |++ ls) ⇒ P v``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_FUPDATE_LIST_SUBSET) >>
PROVE_TAC[])

(* TODO: move *)
val IN_FRANGE = store_thm(
"IN_FRANGE",
``!f v. v IN FRANGE f = ?k. k IN FDOM f /\ (f ' k = v)``,
SRW_TAC[][FRANGE_DEF])

val FRANGE_FUNION_SUBSET = store_thm(
"FRANGE_FUNION_SUBSET",
``FRANGE (f1 ⊌ f2) ⊆ FRANGE f1 ∪ FRANGE f2``,
srw_tac[DNF_ss][FRANGE_DEF,SUBSET_DEF,FUNION_DEF] >>
PROVE_TAC[])

val FRANGE_DOMSUB_SUBSET = store_thm(
"FRANGE_DOMSUB_SUBSET",
``FRANGE (fm \\ k) ⊆ FRANGE fm``,
srw_tac[DNF_ss][FRANGE_DEF,SUBSET_DEF,DOMSUB_FAPPLY_THM] >>
PROVE_TAC[])

val FRANGE_DRESTRICT_SUBSET = store_thm(
"FRANGE_DRESTRICT_SUBSET",
``FRANGE (DRESTRICT fm s) ⊆ FRANGE fm``,
srw_tac[DNF_ss][FRANGE_DEF,SUBSET_DEF,DRESTRICT_DEF] >>
PROVE_TAC[])

val IN_FRANGE_FUNION_suff = store_thm(
"IN_FRANGE_FUNION_suff",
``(∀v. v ∈ FRANGE f1 ⇒ P v) ∧ (∀v. v ∈ FRANGE f2 ⇒ P v) ⇒
  (∀v. v ∈ FRANGE (f1 ⊌ f2) ⇒ P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_FUNION_SUBSET) >>
PROVE_TAC[])

val IN_FRANGE_DOMSUB_suff = store_thm(
"IN_FRANGE_DOMSUB_suff",
``(∀v. v ∈ FRANGE fm ⇒ P v) ⇒ (∀v. v ∈ FRANGE (fm \\ k) ⇒ P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_DOMSUB_SUBSET) >>
PROVE_TAC[])

val IN_FRANGE_DRESTRICT_suff = store_thm(
"IN_FRANGE_DRESTRICT_suff",
``(∀v. v ∈ FRANGE fm ⇒ P v) ⇒ (∀v. v ∈ FRANGE (DRESTRICT fm s) ⇒ P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_DRESTRICT_SUBSET) >>
PROVE_TAC[])

val exists_list_GENLIST = store_thm(
"exists_list_GENLIST",
``(∃ls. P ls) = (∃n f. P (GENLIST f n))``,
rw[EQ_IMP_THM] >- (
  map_every qexists_tac [`LENGTH ls`,`combin$C EL ls`] >>
  qmatch_abbrev_tac `P ls2` >>
  qsuff_tac `ls2 = ls` >- rw[] >>
  rw[LIST_EQ_REWRITE,Abbr`ls2`] ) >>
PROVE_TAC[])

val DRESTRICT_SUBMAP_gen = store_thm(
"DRESTRICT_SUBMAP_gen",
``f SUBMAP g ==> DRESTRICT f P SUBMAP g``,
SRW_TAC[][SUBMAP_DEF,DRESTRICT_DEF])

val DRESTRICT_SUBSET_SUBMAP = store_thm(
"DRESTRICT_SUBSET_SUBMAP",
``s1 SUBSET s2 ==> DRESTRICT f s1 SUBMAP DRESTRICT f s2``,
SRW_TAC[][SUBMAP_DEF,SUBSET_DEF,DRESTRICT_DEF])

val FUPDATE_SAME_APPLY = store_thm(
"FUPDATE_SAME_APPLY",
``(x = FST kv) \/ (fm1 ' x = fm2 ' x) ==> ((fm1 |+ kv) ' x = (fm2 |+ kv) ' x)``,
Cases_on `kv` >> rw[FAPPLY_FUPDATE_THM])

val FUPDATE_SAME_LIST_APPLY = store_thm(
"FUPDATE_SAME_LIST_APPLY",
``!kvl fm1 fm2 x. MEM x (MAP FST kvl) ==> ((fm1 |++ kvl) ' x = (fm2 |++ kvl) ' x)``,
ho_match_mp_tac SNOC_INDUCT >>
conj_tac >- rw[] >>
rw[FUPDATE_LIST,FOLDL_SNOC] >>
match_mp_tac FUPDATE_SAME_APPLY >>
qmatch_rename_tac `(y = FST p) \/ Z` ["Z"] >>
Cases_on `y = FST p` >> rw[] >>
first_x_assum match_mp_tac >>
fs[MEM_MAP] >>
PROVE_TAC[])

val DRESTRICTED_FUNION = store_thm(
"DRESTRICTED_FUNION",
``∀f1 f2 s. DRESTRICT (f1 ⊌ f2) s = DRESTRICT f1 s ⊌ DRESTRICT f2 (s DIFF FDOM f1)``,
rw[GSYM fmap_EQ_THM,DRESTRICT_DEF,FUNION_DEF] >> rw[] >>
rw[EXTENSION] >> PROVE_TAC[])

(* TODO: move *)
val OPTREL_refl = store_thm(
"OPTREL_refl",
``(!x. R x x) ==> !x. OPTREL R x x``,
strip_tac >> Cases >> rw[optionTheory.OPTREL_def])
val _ = export_rewrites["OPTREL_refl"]

(* TODO: move? *)
val ALOOKUP_NONE = store_thm(
"ALOOKUP_NONE",
``!l x. (ALOOKUP l x = NONE) = ~MEM x (MAP FST l)``,
SRW_TAC[][ALOOKUP_FAILS,MEM_MAP,pairTheory.FORALL_PROD])

val FOLDR_transitive_property = store_thm(
"FOLDR_transitive_property",
``!P ls f a. P [] a /\ (!n a. n < LENGTH ls /\ P (DROP (SUC n) ls) a ==> P (DROP n ls) (f (EL n ls) a)) ==> P ls (FOLDR f a ls)``,
GEN_TAC THEN Induct THEN SRW_TAC[][] THEN
`P ls (FOLDR f a ls)` by (
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SRW_TAC[][] THEN
  Q.MATCH_ASSUM_RENAME_TAC `P (DROP (SUC n) ls) b` [] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`,`b`] MP_TAC) THEN
  SRW_TAC[][] ) THEN
FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN
SRW_TAC[][])

val MEM_DROP = store_thm(
"MEM_DROP",
``!x ls n. MEM x (DROP n ls) = (n < LENGTH ls /\ (x = (EL n ls))) \/ MEM x (DROP (SUC n) ls)``,
GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
NTAC 2 GEN_TAC THEN
SIMP_TAC (srw_ss()) [] THEN
Cases_on `n` THEN SIMP_TAC (srw_ss()) [] THEN
PROVE_TAC[])

(* TODO: Move *)
val alist_to_fmap_PERM = store_thm(
"alist_to_fmap_PERM",
``∀l1 l2. PERM l1 l2 ∧ ALL_DISTINCT (MAP FST l1) ⇒ (alist_to_fmap l1 = alist_to_fmap l2)``,
let open sortingTheory in
qsuff_tac
  `∀l1 l2. PERM l1 l2 ⇒ ALL_DISTINCT (MAP FST l1) ⇒ PERM l1 l2 ∧ (alist_to_fmap l1 = alist_to_fmap l2)`
  >- rw[] >>
ho_match_mp_tac PERM_IND >>
fs[pairTheory.FORALL_PROD] >>
rw[] >> fs[] >- (
  fs[PERM_SWAP_AT_FRONT] )
>- (
  match_mp_tac FUPDATE_COMMUTES >> rw[] )
>- (
  PROVE_TAC[PERM_TRANS,ALL_DISTINCT_PERM,PERM_MAP] )
>- (
  PROVE_TAC[PERM_TRANS,ALL_DISTINCT_PERM,PERM_MAP] )
end)

(* TODO: move *)
val DROP_APPEND1 = rich_listTheory.BUTFIRSTN_APPEND1
val DROP_APPEND2 = rich_listTheory.BUTFIRSTN_APPEND2
val DROP_LENGTH_NIL = rich_listTheory.BUTFIRSTN_LENGTH_NIL

val MAP_values_fmap_to_alist = store_thm(
"MAP_values_fmap_to_alist",
``∀f fm. MAP (λ(k,v). (k, f v)) (fmap_to_alist fm) = fmap_to_alist (f o_f fm)``,
rw[fmap_to_alist_def,MAP_MAP_o,MAP_EQ_f])

val alist_to_fmap_MAP_matchable = store_thm(
"alist_to_fmap_MAP_matchable",
``∀f1 f2 al mal v. INJ f1 (set (MAP FST al)) UNIV ∧
  (mal = MAP (λ(x,y). (f1 x,f2 y)) al) ∧
  (v = MAP_KEYS f1 (f2 o_f alist_to_fmap al)) ⇒
  (alist_to_fmap mal = v)``,
METIS_TAC[alist_to_fmap_MAP])

val alist_to_fmap_MAP_values = store_thm(
"alist_to_fmap_MAP_values",
``∀f al. alist_to_fmap (MAP (λ(k,v). (k, f v)) al) = f o_f (alist_to_fmap al)``,
rw[] >>
Q.ISPECL_THEN [`I:γ->γ`,`f`,`al`] match_mp_tac alist_to_fmap_MAP_matchable >>
rw[INJ_I])

val FRANGE_alist_to_fmap_SUBSET = store_thm(
"FRANGE_alist_to_fmap_SUBSET",
``FRANGE (alist_to_fmap ls) ⊆ IMAGE SND (set ls)``,
srw_tac[DNF_ss][FRANGE_DEF,SUBSET_DEF,pairTheory.EXISTS_PROD] >>
qmatch_assum_rename_tac `MEM z (MAP FST ls)`[] >>
qexists_tac `z` >>
match_mp_tac alist_to_fmap_FAPPLY_MEM >>
rw[])

val FRANGE_FUPDATE_SUBSET = store_thm(
"FRANGE_FUPDATE_SUBSET",
``FRANGE (fm |+ kv) ⊆ FRANGE fm ∪ {SND kv}``,
Cases_on `kv` >>
rw[FRANGE_DEF,SUBSET_DEF,DOMSUB_FAPPLY_THM] >>
rw[] >> PROVE_TAC[])

val IN_FRANGE_alist_to_fmap_suff = store_thm(
"IN_FRANGE_alist_to_fmap_suff",
``(∀v. MEM v (MAP SND ls) ⇒ P v) ⇒ (∀v. v ∈ FRANGE (alist_to_fmap ls) ⇒ P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_alist_to_fmap_SUBSET) >>
fs[MEM_MAP] >>
PROVE_TAC[])

val IN_FRANGE_FUPDATE_suff = store_thm(
"IN_FRANGE_FUPDATE_suff",
`` (∀v. v ∈ FRANGE fm ⇒ P v) ∧ (P (SND kv))
⇒ (∀v. v ∈ FRANGE (fm |+ kv) ⇒ P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_FUPDATE_SUBSET) >>
fs[])

val DRESTRICT_FDOM = store_thm(
"DRESTRICT_FDOM",
``!f.DRESTRICT f (FDOM f) = f``,
SRW_TAC[][GSYM fmap_EQ_THM,DRESTRICT_DEF])

(* TODO: move? *)
val fmap_rel_def = Define`
  fmap_rel R f1 f2 = (FDOM f2 = FDOM f1) ∧ (∀x. x ∈ FDOM f1 ⇒ R (f1 ' x) (f2 ' x))`

val fmap_rel_FUPDATE_same = store_thm(
"fmap_rel_FUPDATE_same",
``fmap_rel R f1 f2 ∧ R v1 v2 ⇒ fmap_rel R (f1 |+ (k,v1)) (f2 |+ (k,v2))``,
rw[fmap_rel_def,FAPPLY_FUPDATE_THM] >> rw[])

val fmap_rel_FUPDATE_LIST_same = store_thm(
"fmap_rel_FUPDATE_LIST_same",
``∀R ls1 ls2 f1 f2.
  fmap_rel R f1 f2 ∧ (MAP FST ls1 = MAP FST ls2) ∧ (LIST_REL R (MAP SND ls1) (MAP SND ls2))
  ⇒ fmap_rel R (f1 |++ ls1) (f2 |++ ls2)``,
gen_tac >>
Induct >> Cases >> rw[FUPDATE_LIST_THM,LIST_REL_CONS1] >>
Cases_on `ls2` >> fs[FUPDATE_LIST_THM] >>
first_x_assum match_mp_tac >> fs[] >> rw[] >>
qmatch_assum_rename_tac `R a (SND b)`[] >>
Cases_on `b` >> fs[] >>
rw[fmap_rel_FUPDATE_same])

val fmap_rel_FEMPTY = store_thm(
"fmap_rel_FEMPTY",
``fmap_rel R FEMPTY FEMPTY``,
rw[fmap_rel_def])
val _ = export_rewrites["fmap_rel_FEMPTY"]

val fmap_rel_refl = store_thm(
"fmap_rel_refl",
``(∀x. R x x) ⇒ fmap_rel R x x``,
rw[fmap_rel_def])
val _ = export_rewrites["fmap_rel_refl"]

val fmap_rel_FUNION_rels = store_thm(
"fmap_rel_FUNION_rels",
``fmap_rel R f1 f2 ∧ fmap_rel R f3 f4 ⇒ fmap_rel R (f1 ⊌ f3) (f2 ⊌ f4)``,
rw[fmap_rel_def,FUNION_DEF] >> rw[])

val LEAST_BOUND = store_thm(
"LEAST_BOUND",
``∀P n. P n ⇒ ($LEAST P) ≤ n ∧ ($LEAST P = $LEAST (λm. P m ∧ m ≤ n))``,
rpt gen_tac >>
strip_tac >>
conj_tac >- (
  spose_not_then strip_assume_tac >>
  `n < $LEAST P` by DECIDE_TAC >>
  PROVE_TAC[whileTheory.LESS_LEAST] ) >>
qmatch_abbrev_tac `X = Y` >>
qunabbrev_tac`Y` >>
numLib.LEAST_ELIM_TAC >>
rw[Abbr`X`] >- (
  qexists_tac `n` >> rw[] ) >>
numLib.LEAST_ELIM_TAC >>
rw[] >- PROVE_TAC[] >>
qmatch_rename_tac `a = b`[] >>
Cases_on`b < a` >- PROVE_TAC[] >>
Cases_on`a < b` >- (
  res_tac >> DECIDE_TAC ) >>
DECIDE_TAC)

val ALOOKUP_ALL_DISTINCT_MEM = store_thm(
"ALOOKUP_ALL_DISTINCT_MEM",
``ALL_DISTINCT (MAP FST al) ∧ MEM (k,v) al ⇒
  (ALOOKUP al k = SOME v)``,
rw[ALOOKUP_LEAST_EL] >- (
  rw[MEM_MAP,pairTheory.EXISTS_PROD] >>
  PROVE_TAC[]) >>
fs[MEM_EL] >>
pop_assum (assume_tac o SYM) >>
qho_match_abbrev_tac `EL ($LEAST P) (MAP SND al) = v` >>
`P n` by (
  unabbrev_all_tac >> rw[EL_MAP] ) >>
qspecl_then [`P`,`n`] mp_tac LEAST_BOUND >> rw[] >>
numLib.LEAST_ELIM_TAC >>
conj_tac >- (
  qexists_tac `n` >> rw[] ) >>
rw[] >>
qmatch_rename_tac `EL m (MAP SND al) = v`[] >>
`m < LENGTH al` by DECIDE_TAC >>
fs[EL_ALL_DISTINCT_EL_EQ] >>
unabbrev_all_tac >> fs[] >>
`m = n` by PROVE_TAC[] >>
fs[EL_MAP])

val FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM = store_thm(
"FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM",
``!P ls k v fm. ALL_DISTINCT (MAP FST ls) ∧
  MEM (k,v) ls ∧
  P v ⇒
  P ((fm |++ ls) ' k)``,
rw[] >>
ho_match_mp_tac FUPDATE_LIST_APPLY_HO_THM >>
disj1_tac >>
fs[EL_ALL_DISTINCT_EL_EQ,MEM_EL] >>
qpat_assum `(k,v) = X` (assume_tac o SYM) >>
qexists_tac `n` >> rw[EL_MAP] >>
first_x_assum (qspecl_then [`n`,`m`] mp_tac) >>
rw[EL_MAP] >> spose_not_then strip_assume_tac >>
rw[] >> fs[])

val DRESTRICT_FDOM = store_thm(
"DRESTRICT_FDOM",
``DRESTRICT fm (FDOM fm) = fm``,
SRW_TAC[][GSYM fmap_EQ_THM,DRESTRICT_DEF])

val FRANGE_DRESTRICT_SUBSET = store_thm(
"FRANGE_DRESTRICT_SUBSET",
``FRANGE (DRESTRICT fm s) ⊆ FRANGE fm``,
SRW_TAC[][FRANGE_DEF,SUBSET_DEF,DRESTRICT_DEF] THEN
SRW_TAC[][] THEN PROVE_TAC[])

val DROP_NIL = store_thm(
"DROP_NIL",
``∀ls n. (DROP n ls = []) = (n ≥ LENGTH ls)``,
Induct >> rw[] >>
srw_tac[ARITH_ss][])

val EVERY2_MAP = store_thm("EVERY2_MAP",
  ``(EVERY2 P (MAP f l1) l2 = EVERY2 (λx y. P (f x) y) l1 l2) ∧
    (EVERY2 Q l1 (MAP g l2) = EVERY2 (λx y. Q x (g y)) l1 l2)``,
  rw[EVERY2_EVERY] >>
  Cases_on `LENGTH l1 = LENGTH l2` >> fs[] >>
  rw[ZIP_MAP,EVERY_MEM,MEM_MAP] >>
  srw_tac[DNF_ss][pairTheory.FORALL_PROD] >>
  PROVE_TAC[])

val FUNION_IDEMPOT = store_thm("FUNION_IDEMPOT",
  ``fm ⊌ fm = fm``,
  SRW_TAC[][GSYM fmap_EQ_THM,FUNION_DEF])

val FUNION_alist_to_fmap = store_thm("FUNION_alist_to_fmap",
  ``∀ls fm. alist_to_fmap ls ⊌ fm = fm |++ (REVERSE ls)``,
  Induct >- rw[FUNION_FEMPTY_1,FUPDATE_LIST] >>
  qx_gen_tac `p` >> PairCases_on `p` >>
  rw[FUPDATE_LIST_THM,alist_to_fmap_thm,FUPDATE_LIST_APPEND] >>
  rw[FUNION_FUPDATE_1])

val FUPDATE_LIST_ALL_DISTINCT_REVERSE = store_thm("FUPDATE_LIST_ALL_DISTINCT_REVERSE",
  ``∀ls. ALL_DISTINCT (MAP FST ls) ⇒ ∀fm. fm |++ (REVERSE ls) = fm |++ ls``,
  Induct >- rw[] >>
  qx_gen_tac `p` >> PairCases_on `p` >>
  rw[FUPDATE_LIST_APPEND,FUPDATE_LIST_THM] >>
  fs[] >>
  rw[FUPDATE_FUPDATE_LIST_COMMUTES])

val _ = export_theory()
