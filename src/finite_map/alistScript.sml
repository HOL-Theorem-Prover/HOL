open HolKernel boolLib bossLib Parse finite_mapTheory listTheory pred_setTheory sortingTheory lcsymtacs

val _ = new_theory "alist";

val _ = type_abbrev("alist",``:(('a # 'b) list)``);

val fmap_to_alist_def = Define`
  fmap_to_alist s = MAP (\k.(k,s ' k)) (SET_TO_LIST (FDOM s))`;

val fmap_to_alist_FEMPTY = store_thm(
  "fmap_to_alist_FEMPTY",
  ``(fmap_to_alist FEMPTY = [])``,
  SRW_TAC [][fmap_to_alist_def]);
val _ = export_rewrites ["fmap_to_alist_FEMPTY"]

val alist_to_fmap_def = Define`
  alist_to_fmap s = FOLDR (\(k,v) f.f|+(k,v)) FEMPTY s`;

val alist_to_fmap_thm = store_thm(
  "alist_to_fmap_thm",
  ``(alist_to_fmap [] = FEMPTY) /\
    (alist_to_fmap ((k,v)::t) = alist_to_fmap t |+ (k,v))``,
  SRW_TAC [][alist_to_fmap_def])
val _ = export_rewrites ["alist_to_fmap_thm"]

val ALOOKUP_def = Define`
  (ALOOKUP [] q = NONE) /\
  (ALOOKUP ((x,y)::t) q = if x = q then SOME y else ALOOKUP t q)`;
val _ = export_rewrites["ALOOKUP_def"];
val ALOOKUP_ind = theorem"ALOOKUP_ind";

val lemma = Q.prove(
`MAP (\k.(k,fm ' k)) (SET_TO_LIST (REST (FDOM fm))) =
 fmap_to_alist (fm \\ (CHOICE (FDOM fm)))`,
SRW_TAC [][fmap_to_alist_def,REST_DEF] THEN
MATCH_MP_TAC MAP_CONG THEN SRW_TAC [][DOMSUB_FAPPLY_THM]);

val ALOOKUP_FAILS = store_thm(
  "ALOOKUP_FAILS",
  ``(ALOOKUP l x = NONE) <=> !k v. MEM (k,v) l ==> k <> x``,
  Induct_on `l` THEN SRW_TAC [][] THEN
  Cases_on `h` THEN SRW_TAC [][] THEN METIS_TAC []);

val ALOOKUP_NONE = store_thm(
"ALOOKUP_NONE",
``!l x. (ALOOKUP l x = NONE) = ~MEM x (MAP FST l)``,
SRW_TAC[][ALOOKUP_FAILS,MEM_MAP,pairTheory.FORALL_PROD])

val ALOOKUP_TABULATE = store_thm(
  "ALOOKUP_TABULATE",
  ``ALL_DISTINCT l /\ MEM x l ==>
    (ALOOKUP (MAP (\k. (k, f k)) l) x = SOME (f x))``,
  Induct_on `l` THEN SRW_TAC [][]);

val ALOOKUP_EQ_FLOOKUP = Q.store_thm(
"ALOOKUP_EQ_FLOOKUP",
`(FLOOKUP (alist_to_fmap al) = ALOOKUP al) /\
 (ALOOKUP (fmap_to_alist fm) = FLOOKUP fm)`,
SRW_TAC [][FUN_EQ_THM] THEN Q.ID_SPEC_TAC `x` THENL [
  Q.ID_SPEC_TAC `al` THEN
  HO_MATCH_MP_TAC ALOOKUP_ind THEN
  SRW_TAC [][alist_to_fmap_def,ALOOKUP_def,FLOOKUP_UPDATE],

  SRW_TAC [][fmap_to_alist_def] THEN
  Cases_on `x IN FDOM fm` THEN SRW_TAC [][FLOOKUP_DEF] THENL [
    MATCH_MP_TAC ALOOKUP_TABULATE THEN SRW_TAC [][],
    SRW_TAC [][ALOOKUP_FAILS, MEM_MAP]
  ]
])
val _ = export_rewrites ["ALOOKUP_EQ_FLOOKUP"]

val MEM_fmap_to_alist = store_thm(
  "MEM_fmap_to_alist",
  ``MEM (x,y) (fmap_to_alist fm) = x IN FDOM fm /\ (fm ' x = y)``,
  SRW_TAC [][fmap_to_alist_def, MEM_MAP] THEN METIS_TAC []);

val MEM_fmap_to_alist_FLOOKUP = store_thm(
"MEM_fmap_to_alist_FLOOKUP",
``!p fm. MEM p (fmap_to_alist fm) = (FLOOKUP fm (FST p) = SOME (SND p))``,
Cases >> rw[MEM_fmap_to_alist,FLOOKUP_DEF])

val MEM_pair_fmap_to_alist_FLOOKUP = store_thm(
"MEM_pair_fmap_to_alist_FLOOKUP",
``!x y fm. MEM (x,y) (fmap_to_alist fm) = (FLOOKUP fm x = SOME y)``,
rw[MEM_fmap_to_alist_FLOOKUP])
val _ = export_rewrites ["MEM_pair_fmap_to_alist_FLOOKUP"]

val LENGTH_fmap_to_alist = store_thm(
"LENGTH_fmap_to_alist",
``!fm. LENGTH (fmap_to_alist fm) = CARD (FDOM fm)``,
rw[fmap_to_alist_def,SET_TO_LIST_CARD])
val _ = export_rewrites["LENGTH_fmap_to_alist"]

val fmap_to_alist_to_fmap = store_thm(
  "fmap_to_alist_to_fmap",
  ``alist_to_fmap (fmap_to_alist fm) = fm``,
  SRW_TAC [][FLOOKUP_EXT])
val _ = export_rewrites ["fmap_to_alist_to_fmap"]

val ALOOKUP_MEM = Q.store_thm(
"ALOOKUP_MEM",
`!al k v.(ALOOKUP al k = SOME v) ==> MEM (k,v) al`,
Induct THEN SRW_TAC [][] THEN
Cases_on `h` THEN POP_ASSUM MP_TAC THEN
SRW_TAC [][]);

val ALOOKUP_SOME_FAPPLY_alist_to_fmap = store_thm(
"ALOOKUP_SOME_FAPPLY_alist_to_fmap",
``!al k v. (ALOOKUP al k = SOME v) ==> (alist_to_fmap al ' k = v)``,
REPEAT STRIP_TAC THEN
Q_TAC SUFF_TAC `FLOOKUP (alist_to_fmap al) k = SOME v` THEN1
  SRW_TAC[][FLOOKUP_DEF,MEM_MAP] THEN
SRW_TAC[][])
val _ = export_rewrites["ALOOKUP_SOME_FAPPLY_alist_to_fmap"]

val alist_to_fmap_FAPPLY_MEM = store_thm(
"alist_to_fmap_FAPPLY_MEM",
``!al z. z IN FDOM (alist_to_fmap al) ==> MEM (z, (alist_to_fmap al) ' z) al``,
rpt strip_tac >>
match_mp_tac ALOOKUP_MEM >>
ONCE_REWRITE_TAC[SYM(CONJUNCT1 ALOOKUP_EQ_FLOOKUP)] >>
REWRITE_TAC[FLOOKUP_DEF] >> rw[])

val ALOOKUP_MAP = store_thm(
"ALOOKUP_MAP",
``!f al. ALOOKUP (MAP (\(x,y). (x,f y)) al) = OPTION_MAP f o (ALOOKUP al)``,
gen_tac >> Induct >- rw[FUN_EQ_THM] >> Cases >> rw[FUN_EQ_THM] >> rw[])

val FDOM_alist_to_fmap = Q.store_thm(
"FDOM_alist_to_fmap",
`!al.FDOM (alist_to_fmap al) = set (MAP FST al)`,
Induct THEN SRW_TAC [][alist_to_fmap_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [alist_to_fmap_def]);
val _ = export_rewrites["FDOM_alist_to_fmap"];

val alist_to_fmap_prefix = Q.store_thm(
"alist_to_fmap_prefix",
`!ls l1 l2.
 (alist_to_fmap l1 = alist_to_fmap l2) ==>
 (alist_to_fmap (ls ++ l1) = alist_to_fmap (ls ++ l2))`,
Induct THEN SRW_TAC [][] THEN
Cases_on `h` THEN SRW_TAC [][] THEN METIS_TAC []);

val alist_to_fmap_APPEND = store_thm(
"alist_to_fmap_APPEND",
``!l1 l2. alist_to_fmap (l1 ++ l2) = FUNION (alist_to_fmap l1) (alist_to_fmap l2)``,
Induct >- rw[FUNION_FEMPTY_1] >>
Cases >> rw[FUNION_FUPDATE_1])
val _ = export_rewrites["alist_to_fmap_APPEND"]

val ALOOKUP_prefix = Q.store_thm(
"ALOOKUP_prefix",
`!ls k ls2.
 ((ALOOKUP ls k = SOME v) ==>
  (ALOOKUP (ls ++ ls2) k = SOME v)) /\
 ((ALOOKUP ls k = NONE) ==>
  (ALOOKUP (ls ++ ls2) k = ALOOKUP ls2 k))`,
HO_MATCH_MP_TAC ALOOKUP_ind THEN
SRW_TAC [][]);

val ALOOKUP_APPEND = store_thm(
"ALOOKUP_APPEND",
``!l1 l2 k. ALOOKUP (l1 ++ l2) k = case ALOOKUP l1 k of SOME v => SOME v | NONE => ALOOKUP l2 k``,
rw[] >> Cases_on `ALOOKUP l1 k` >> rw[ALOOKUP_prefix])

val FUPDATE_LIST_EQ_APPEND_REVERSE = Q.store_thm(
"FUPDATE_LIST_EQ_APPEND_REVERSE",
`!ls fm. fm |++ ls = alist_to_fmap (REVERSE ls ++ fmap_to_alist fm)`,
Induct THEN1 SRW_TAC [][FUPDATE_LIST_THM,FUNION_FEMPTY_1] THEN
Cases THEN FULL_SIMP_TAC(srw_ss())[FUPDATE_LIST_THM] THEN
SRW_TAC[][FUNION_ASSOC,FUNION_FUPDATE_2,FUNION_FEMPTY_2,FUNION_FUPDATE_1])

val FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME = Q.store_thm(
"FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME",
`(ALOOKUP ls k = SOME v) ==> (FLOOKUP (fm |++ (REVERSE ls)) k = SOME v)`,
SRW_TAC [][FUPDATE_LIST_EQ_APPEND_REVERSE,FLOOKUP_DEF,FUNION_DEF,ALOOKUP_SOME_FAPPLY_alist_to_fmap,MEM_MAP,pairTheory.EXISTS_PROD] THEN
METIS_TAC [ALOOKUP_MEM]);

val FLOOKUP_FUPDATE_LIST_ALOOKUP_NONE = Q.store_thm(
"FLOOKUP_FUPDATE_LIST_ALOOKUP_NONE",
`(ALOOKUP ls k = NONE) ==> (FLOOKUP (fm |++ (REVERSE ls)) k = FLOOKUP fm k)`,
SRW_TAC [][FUPDATE_LIST_EQ_APPEND_REVERSE,FLOOKUP_DEF,FUNION_DEF,ALOOKUP_FAILS,MEM_MAP,pairTheory.EXISTS_PROD]);

val FUNION_alist_to_fmap = store_thm("FUNION_alist_to_fmap",
  ``!ls fm. FUNION (alist_to_fmap ls) fm = fm |++ (REVERSE ls)``,
  Induct THEN1 SRW_TAC[][FUNION_FEMPTY_1,FUPDATE_LIST] THEN
  Q.X_GEN_TAC `p` THEN PairCases_on `p` THEN
  SRW_TAC[][FUPDATE_LIST_THM,alist_to_fmap_thm,FUPDATE_LIST_APPEND] THEN
  SRW_TAC[][FUNION_FUPDATE_1])

val alist_to_fmap_MAP = store_thm(
"alist_to_fmap_MAP",
``!f1 f2 al. INJ f1 (set (MAP FST al)) UNIV ==>
 (alist_to_fmap (MAP (\(x,y). (f1 x, f2 y)) al) =
  MAP_KEYS f1 (f2 o_f alist_to_fmap al))``,
NTAC 2 GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
Cases THEN SRW_TAC[][INJ_INSERT] THEN
Q.MATCH_ABBREV_TAC `x = MAP_KEYS f1 ((f o_f (a \\ q)) |+ b)` THEN
`f o_f (a \\ q) = (f o_f a) \\ q` by SRW_TAC[][] THEN
POP_ASSUM SUBST1_TAC THEN
UNABBREV_ALL_TAC THEN
SRW_TAC[][GSYM FUPDATE_PURGE] THEN
Q.MATCH_ABBREV_TAC `x = MAP_KEYS f1 (fm |+ (k,v))` THEN
`INJ f1 (k INSERT FDOM fm) UNIV` by (
  SRW_TAC[][Abbr`fm`,INJ_INSERT] ) THEN
SRW_TAC[][MAP_KEYS_FUPDATE])

val alist_to_fmap_to_alist = store_thm(
"alist_to_fmap_to_alist",
``!al. fmap_to_alist (alist_to_fmap al) =
       MAP (\k. (k, THE (ALOOKUP al k))) (SET_TO_LIST (set (MAP FST al)))``,
SRW_TAC[][fmap_to_alist_def,MAP_EQ_f,MEM_MAP] THEN
Q.MATCH_ASSUM_RENAME_TAC `MEM p al` [] THEN
PairCases_on `p` THEN SRW_TAC[][] THEN
Cases_on `ALOOKUP al p0` THEN
IMP_RES_TAC ALOOKUP_FAILS THEN
SRW_TAC[][])

val alist_to_fmap_to_alist_PERM = store_thm(
"alist_to_fmap_to_alist_PERM",
``!al. ALL_DISTINCT (MAP FST al) ==>
       PERM (fmap_to_alist (alist_to_fmap al)) al``,
SRW_TAC[][alist_to_fmap_to_alist,ALL_DISTINCT_PERM_LIST_TO_SET_TO_LIST] THEN
MATCH_MP_TAC PERM_TRANS THEN
Q.EXISTS_TAC `MAP (\k. (k, THE (ALOOKUP al k))) (MAP FST al)` THEN
CONJ_TAC THEN1 (
  MATCH_MP_TAC PERM_MAP THEN
  SRW_TAC[][PERM_SYM] ) THEN
SRW_TAC[][MAP_MAP_o] THEN
FULL_SIMP_TAC (srw_ss()) [GSYM ALL_DISTINCT_PERM_LIST_TO_SET_TO_LIST] THEN
Q.MATCH_ABBREV_TAC `PERM ll al` THEN
Q_TAC SUFF_TAC `ll = al` THEN1 SRW_TAC[][] THEN
UNABBREV_ALL_TAC THEN
Induct_on `al` THEN1 SRW_TAC[][] THEN
Cases THEN SRW_TAC[][MEM_MAP] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q.MATCH_ASSUM_ABBREV_TAC `MAP f1 al = al` THEN
Q.MATCH_ABBREV_TAC `MAP f2 al = al` THEN
Q_TAC SUFF_TAC `!x. MEM x al ==> (f1 x = f2 x)` THEN1 PROVE_TAC[MAP_EQ_f] THEN
SRW_TAC[][Abbr`f1`,Abbr`f2`] THEN
PROVE_TAC[])

val ALOOKUP_LEAST_EL = store_thm(
"ALOOKUP_LEAST_EL",
``!ls k. ALOOKUP ls k = if MEM k (MAP FST ls) then
         SOME (EL (LEAST n. EL n (MAP FST ls) = k) (MAP SND ls))
         else NONE``,
Induct THEN1 SRW_TAC[][] THEN
Cases THEN SRW_TAC[][] THEN
FULL_SIMP_TAC(srw_ss())[MEM_MAP] THEN1 (
  numLib.LEAST_ELIM_TAC THEN
  SRW_TAC[][] THEN1
    (Q.EXISTS_TAC `0` THEN SRW_TAC[][]) THEN
  Cases_on `n` THEN SRW_TAC[][] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN
  SRW_TAC[][] ) THEN
numLib.LEAST_ELIM_TAC THEN
FULL_SIMP_TAC (srw_ss()) [MEM_EL] THEN
SRW_TAC[][] THEN1 (
  Q.EXISTS_TAC `n` THEN
  SRW_TAC[][EL_MAP] ) THEN
numLib.LEAST_ELIM_TAC THEN
SRW_TAC[][] THEN
Q.MATCH_ASSUM_RENAME_TAC `EL m (MAP FST ls) = FST (EL n ls)`[] THEN1 (
  Q.EXISTS_TAC `SUC m` THEN
  SRW_TAC[][] ) THEN
Cases_on `n < m` THEN1 METIS_TAC[EL_MAP] THEN
`m < LENGTH ls` by DECIDE_TAC THEN
FULL_SIMP_TAC(srw_ss())[EL_MAP] THEN
Q.MATCH_ASSUM_RENAME_TAC `EL z (h::MAP FST ls) = FST (EL n ls)`[] THEN
Cases_on `SUC n < z` THEN1 (
  RES_TAC THEN
  FULL_SIMP_TAC(srw_ss())[] THEN
  METIS_TAC[EL_MAP]) THEN
`z < SUC (LENGTH ls)` by DECIDE_TAC THEN
Cases_on `z` THEN FULL_SIMP_TAC (srw_ss()) [EL_MAP] THEN
Q.MATCH_RENAME_TAC `SND (EL m ls) = SND (EL z ls)`[] THEN
Cases_on `m < z` THEN1 (
  `SUC m < SUC z` by DECIDE_TAC THEN
  RES_TAC THEN
  FULL_SIMP_TAC(srw_ss())[] THEN
  METIS_TAC[EL_MAP] ) THEN
Cases_on `z < m` THEN1 METIS_TAC[EL_MAP] THEN
`m = z` by DECIDE_TAC THEN
SRW_TAC[][])

val ALOOKUP_ALL_DISTINCT_MEM = store_thm(
"ALOOKUP_ALL_DISTINCT_MEM",
``ALL_DISTINCT (MAP FST al) /\ MEM (k,v) al ==>
  (ALOOKUP al k = SOME v)``,
rw[ALOOKUP_LEAST_EL] >- (
  rw[MEM_MAP,pairTheory.EXISTS_PROD] >>
  PROVE_TAC[]) >>
fs[MEM_EL] >>
pop_assum (assume_tac o SYM) >>
qho_match_abbrev_tac `EL ($LEAST P) (MAP SND al) = v` >>
`P n` by (
  unabbrev_all_tac >> rw[EL_MAP] ) >>
qspecl_then [`P`,`n`] mp_tac whileTheory.LESS_LEAST >> rw[] >>
numLib.LEAST_ELIM_TAC >>
conj_tac >- (
  qexists_tac `n` >> rw[] ) >>
rw[] >>
qmatch_rename_tac `EL m (MAP SND al) = v`[] >>
`~(n < m)` by PROVE_TAC[] >>
`m < LENGTH al` by DECIDE_TAC >>
fs[EL_ALL_DISTINCT_EL_EQ] >>
unabbrev_all_tac >> fs[] >>
`m = n` by PROVE_TAC[] >>
fs[EL_MAP])

val ALL_DISTINCT_fmap_to_alist_keys = store_thm(
"ALL_DISTINCT_fmap_to_alist_keys",
``!fm. ALL_DISTINCT (MAP FST (fmap_to_alist fm))``,
qsuff_tac `!s fm. (s = FDOM fm) ==> ALL_DISTINCT (MAP FST (fmap_to_alist fm))`
  >- rw[] >>
ho_match_mp_tac SET_TO_LIST_IND >> rw[] >>
fs[fmap_to_alist_def] >>
Cases_on `FDOM fm = {}` >- rw[] >> fs[] >>
rw[Once SET_TO_LIST_THM] >- (
  rw[MEM_MAP,CHOICE_NOT_IN_REST,MAP_MAP_o,pairTheory.EXISTS_PROD] ) >>
first_x_assum (qspec_then `fm \\ (CHOICE (FDOM fm))` mp_tac) >>
rw[REST_DEF,MAP_MAP_o] >>
qmatch_assum_abbrev_tac `ALL_DISTINCT (MAP f1 ls)` >>
qmatch_abbrev_tac `ALL_DISTINCT (MAP f2 ls)` >>
qsuff_tac `MAP f2 ls = MAP f1 ls` >- rw[] >>
rw[MAP_EQ_f,Abbr`f1`,Abbr`f2`,Abbr`ls`,DOMSUB_FAPPLY_THM])
val _ = export_rewrites["ALL_DISTINCT_fmap_to_alist_keys"]

val fmap_to_alist_inj = store_thm(
"fmap_to_alist_inj",
``!f1 f2. (fmap_to_alist f1 = fmap_to_alist f2) ==> (f1 = f2)``,
rw[] >>
qmatch_assum_abbrev_tac `af1 = af2` >>
qsuff_tac `alist_to_fmap af1 = alist_to_fmap af2` >- metis_tac[fmap_to_alist_to_fmap] >>
rw[GSYM fmap_EQ_THM,pairTheory.EXISTS_PROD,MEM_MAP,MEM_fmap_to_alist])

val fmap_to_alist_preserves_FDOM = store_thm(
"fmap_to_alist_preserves_FDOM",
``!fm1 fm2. (FDOM fm1 = FDOM fm2) ==> (MAP FST (fmap_to_alist fm1) = MAP FST (fmap_to_alist fm2))``,
qsuff_tac `
  !s fm1 fm2. (FDOM fm1 = s) /\ (FDOM fm2 = s) ==>
              (MAP FST (fmap_to_alist fm1) = MAP FST (fmap_to_alist fm2))`
  >- rw[] >>
ho_match_mp_tac SET_TO_LIST_IND >> rw[] >>
fs[fmap_to_alist_def] >>
Cases_on `FDOM fm2 = {}` >- rw[] >> fs[] >>
`FDOM fm1 <> {}` by rw[] >>
rw[Once SET_TO_LIST_THM,SimpLHS] >>
rw[Once SET_TO_LIST_THM,SimpRHS] >>
first_x_assum (qspec_then `fm1 \\ (CHOICE (FDOM fm2))` mp_tac) >>
disch_then (qspec_then `fm2 \\ (CHOICE (FDOM fm2))` mp_tac) >>
rw[REST_DEF,MAP_MAP_o] >>
qmatch_assum_abbrev_tac `MAP f1 ls = MAP f2 ls` >>
qmatch_abbrev_tac `MAP f3 ls = MAP f4 ls` >>
qsuff_tac `(MAP f3 ls = MAP f1 ls) /\ (MAP f4 ls = MAP f2 ls)` >- rw[] >>
rw[MAP_EQ_f,Abbr`f1`,Abbr`f2`,Abbr`f3`,Abbr`f4`,Abbr`ls`,DOMSUB_FAPPLY_THM])

val PERM_fmap_to_alist = store_thm(
"PERM_fmap_to_alist",
``PERM (fmap_to_alist fm1) (fmap_to_alist fm2) = (fm1 = fm2)``,
rw[EQ_IMP_THM] >>
qmatch_assum_abbrev_tac `PERM af1 af2` >>
qsuff_tac `alist_to_fmap af1 = alist_to_fmap af2` >-
  metis_tac[fmap_to_alist_to_fmap] >>
`FDOM (alist_to_fmap af1) = FDOM (alist_to_fmap af2)` by (
  rw[] >>
  match_mp_tac PERM_LIST_TO_SET >>
  match_mp_tac sortingTheory.PERM_MAP >>
  rw[] ) >>
qmatch_abbrev_tac `ff1 = ff2` >>
qsuff_tac `fmap_to_alist ff1 = fmap_to_alist ff2` >-
  metis_tac[fmap_to_alist_inj] >>
Q.ISPEC_THEN `FST` match_mp_tac INJ_MAP_EQ >>
reverse conj_tac >- (
  match_mp_tac fmap_to_alist_preserves_FDOM >>
  rw[Abbr`ff1`,Abbr`ff2`]) >>
rw[INJ_DEF,Abbr`ff1`,Abbr`ff2`,MEM_fmap_to_alist_FLOOKUP] >>
Cases_on `x` >> Cases_on `y` >> fs[] >>
imp_res_tac ALOOKUP_MEM >>
imp_res_tac MEM_PERM >>
`ALL_DISTINCT (MAP FST af1) /\ ALL_DISTINCT (MAP FST af2)`
  by rw[ALL_DISTINCT_fmap_to_alist_keys,Abbr`af1`,Abbr`af2`] >>
fs[EL_ALL_DISTINCT_EL_EQ,MEM_EL,EL_MAP] >>
rw[] >>
qmatch_rename_tac `r1 = r2`[] >>
qmatch_assum_rename_tac `(q,r1) = EL n1 afx`[] >>
qmatch_assum_rename_tac `(q,r2) = EL n2 afy`[] >>
rpt (qpat_assum `(X,Y) = EL N Z` (assume_tac o SYM)) >>
`LENGTH afy = LENGTH afx` by rw[PERM_LENGTH] >> fs[] >>
metis_tac[pairTheory.PAIR_EQ,pairTheory.FST])

val alist_to_fmap_PERM = store_thm(
"alist_to_fmap_PERM",
``!l1 l2. PERM l1 l2 /\ ALL_DISTINCT (MAP FST l1) ==> (alist_to_fmap l1 = alist_to_fmap l2)``,
rpt strip_tac >>
match_mp_tac (fst (EQ_IMP_RULE PERM_fmap_to_alist)) >>
metis_tac[PERM_TRANS,PERM_SYM,ALL_DISTINCT_PERM,PERM_MAP,alist_to_fmap_to_alist_PERM])

val _ = export_theory ();
