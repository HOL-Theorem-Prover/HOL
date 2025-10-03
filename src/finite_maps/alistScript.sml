Theory alist
Ancestors
  finite_map list rich_list pred_set sorting pair relation
Libs
  boolSimps

val _ = diminish_srw_ss ["NORMEQ"]

val _ = type_abbrev("alist",``:(('a # 'b) list)``);

Definition fmap_to_alist_def:
  fmap_to_alist s = MAP (\k.(k,s ' k)) (SET_TO_LIST (FDOM s))
End

Theorem fmap_to_alist_FEMPTY:
    (fmap_to_alist FEMPTY = [])
Proof
  SRW_TAC [][fmap_to_alist_def]
QED
val _ = export_rewrites ["fmap_to_alist_FEMPTY"]

Definition alist_to_fmap_def:
  alist_to_fmap s = FOLDR (\(k,v) f.f|+(k,v)) FEMPTY s
End

Theorem alist_to_fmap_thm:
    (alist_to_fmap [] = FEMPTY) /\
    (alist_to_fmap ((k,v)::t) = alist_to_fmap t |+ (k,v))
Proof
  SRW_TAC [][alist_to_fmap_def]
QED
val _ = export_rewrites ["alist_to_fmap_thm"]

Definition ALOOKUP_def:
  (ALOOKUP [] q = NONE) /\
  (ALOOKUP ((x,y)::t) q = if x = q then SOME y else ALOOKUP t q)
End
val _ = export_rewrites["ALOOKUP_def"];
val ALOOKUP_ind = theorem"ALOOKUP_ind";

val lemma = Q.prove(
`MAP (\k.(k,fm ' k)) (SET_TO_LIST (REST (FDOM fm))) =
 fmap_to_alist (fm \\ (CHOICE (FDOM fm)))`,
SRW_TAC [][fmap_to_alist_def,REST_DEF] THEN
MATCH_MP_TAC MAP_CONG THEN SRW_TAC [][DOMSUB_FAPPLY_THM]);

Theorem ALOOKUP_FAILS:
    (ALOOKUP l x = NONE) <=> !k v. MEM (k,v) l ==> k <> x
Proof
  Induct_on `l` THEN SRW_TAC [][] THEN
  Cases_on `h` THEN SRW_TAC [][] THEN METIS_TAC []
QED

Theorem ALOOKUP_NONE:
  !l x. (ALOOKUP l x = NONE) = ~MEM x (MAP FST l)
Proof
SRW_TAC[][ALOOKUP_FAILS,MEM_MAP,pairTheory.FORALL_PROD]
QED

Theorem ALOOKUP_TABULATE:
    MEM x l ==>
    (ALOOKUP (MAP (\k. (k, f k)) l) x = SOME (f x))
Proof
  Induct_on `l` THEN SRW_TAC [][]
QED

Theorem ALOOKUP_EQ_FLOOKUP:
 (FLOOKUP (alist_to_fmap al) = ALOOKUP al) /\
 (ALOOKUP (fmap_to_alist fm) = FLOOKUP fm)
Proof
SRW_TAC [][FUN_EQ_THM] THEN Q.ID_SPEC_TAC `x` THENL [
  Q.ID_SPEC_TAC `al` THEN
  HO_MATCH_MP_TAC ALOOKUP_ind THEN
  SRW_TAC [][alist_to_fmap_def,ALOOKUP_def,FLOOKUP_UPDATE],

  SRW_TAC [][fmap_to_alist_def] THEN
  Cases_on `x IN FDOM fm` THEN SRW_TAC [][FLOOKUP_DEF] THENL [
    MATCH_MP_TAC ALOOKUP_TABULATE THEN SRW_TAC [][],
    SRW_TAC [][ALOOKUP_FAILS, MEM_MAP]
  ]
]
QED
val _ = export_rewrites ["ALOOKUP_EQ_FLOOKUP"]

Theorem MEM_fmap_to_alist:
    MEM (x,y) (fmap_to_alist fm) <=> x IN FDOM fm /\ (fm ' x = y)
Proof
  SRW_TAC [][fmap_to_alist_def, MEM_MAP] THEN METIS_TAC []
QED

Theorem MEM_fmap_to_alist_FLOOKUP:
  !p fm. MEM p (fmap_to_alist fm) = (FLOOKUP fm (FST p) = SOME (SND p))
Proof
Cases >> rw[MEM_fmap_to_alist,FLOOKUP_DEF]
QED

Theorem MEM_pair_fmap_to_alist_FLOOKUP:
  !x y fm. MEM (x,y) (fmap_to_alist fm) = (FLOOKUP fm x = SOME y)
Proof
rw[MEM_fmap_to_alist_FLOOKUP]
QED
val _ = export_rewrites ["MEM_pair_fmap_to_alist_FLOOKUP"]

Theorem LENGTH_fmap_to_alist:
  !fm. LENGTH (fmap_to_alist fm) = CARD (FDOM fm)
Proof
rw[fmap_to_alist_def,SET_TO_LIST_CARD]
QED
val _ = export_rewrites["LENGTH_fmap_to_alist"]

Theorem fmap_to_alist_to_fmap:
    alist_to_fmap (fmap_to_alist fm) = fm
Proof
  SRW_TAC [][FLOOKUP_EXT]
QED
val _ = export_rewrites ["fmap_to_alist_to_fmap"]

Theorem ALOOKUP_MEM:
 !al k v.(ALOOKUP al k = SOME v) ==> MEM (k,v) al
Proof
Induct THEN SRW_TAC [][] THEN
Cases_on `h` THEN POP_ASSUM MP_TAC THEN
SRW_TAC [][]
QED

Theorem ALOOKUP_SOME_FAPPLY_alist_to_fmap:
  !al k v. (ALOOKUP al k = SOME v) ==> (alist_to_fmap al ' k = v)
Proof
REPEAT STRIP_TAC THEN
Q_TAC SUFF_TAC `FLOOKUP (alist_to_fmap al) k = SOME v` THEN1
  SRW_TAC[][FLOOKUP_DEF,MEM_MAP] THEN
SRW_TAC[][]
QED
val _ = export_rewrites["ALOOKUP_SOME_FAPPLY_alist_to_fmap"]

Theorem alist_to_fmap_FAPPLY_MEM:
  !al z. z IN FDOM (alist_to_fmap al) ==> MEM (z, (alist_to_fmap al) ' z) al
Proof
rpt strip_tac >>
match_mp_tac ALOOKUP_MEM >>
ONCE_REWRITE_TAC[SYM(CONJUNCT1 ALOOKUP_EQ_FLOOKUP)] >>
REWRITE_TAC[FLOOKUP_DEF] >> rw[]
QED

Theorem ALOOKUP_MAP:
  !f al. ALOOKUP (MAP (\(x,y). (x,f y)) al) = OPTION_MAP f o (ALOOKUP al)
Proof
gen_tac >> Induct >- rw[FUN_EQ_THM] >> Cases >> rw[FUN_EQ_THM] >> rw[]
QED

Theorem ALOOKUP_MAP_2:
  !f al x.
    ALOOKUP (MAP (\ (x,y). (x,f x y)) al) x =
    OPTION_MAP (f x) (ALOOKUP al x)
Proof
  gen_tac >> Induct >> simp[] >> Cases >> simp[] >> srw_tac[][]
QED

Theorem FDOM_alist_to_fmap:
 !al.FDOM (alist_to_fmap al) = set (MAP FST al)
Proof
Induct THEN SRW_TAC [][alist_to_fmap_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [alist_to_fmap_def]
QED
val _ = export_rewrites["FDOM_alist_to_fmap"];

Theorem alist_to_fmap_prefix:
 !ls l1 l2.
 (alist_to_fmap l1 = alist_to_fmap l2) ==>
 (alist_to_fmap (ls ++ l1) = alist_to_fmap (ls ++ l2))
Proof
Induct THEN SRW_TAC [][] THEN
Cases_on `h` THEN SRW_TAC [][] THEN METIS_TAC []
QED

Theorem alist_to_fmap_APPEND:
  !l1 l2. alist_to_fmap (l1 ++ l2) = FUNION (alist_to_fmap l1) (alist_to_fmap l2)
Proof
Induct >- rw[FUNION_FEMPTY_1] >>
Cases >> rw[FUNION_FUPDATE_1]
QED
val _ = export_rewrites["alist_to_fmap_APPEND"]

Theorem ALOOKUP_prefix:
 !ls k ls2.
 ((ALOOKUP ls k = SOME v) ==>
  (ALOOKUP (ls ++ ls2) k = SOME v)) /\
 ((ALOOKUP ls k = NONE) ==>
  (ALOOKUP (ls ++ ls2) k = ALOOKUP ls2 k))
Proof
HO_MATCH_MP_TAC ALOOKUP_ind THEN
SRW_TAC [][]
QED

Theorem ALOOKUP_APPEND:
  !l1 l2 k. ALOOKUP (l1 ++ l2) k = case ALOOKUP l1 k of SOME v => SOME v | NONE => ALOOKUP l2 k
Proof
rw[] >> Cases_on `ALOOKUP l1 k` >> rw[ALOOKUP_prefix]
QED

Theorem FUPDATE_LIST_EQ_APPEND_REVERSE:
 !ls fm. fm |++ ls = alist_to_fmap (REVERSE ls ++ fmap_to_alist fm)
Proof
Induct THEN1 SRW_TAC [][FUPDATE_LIST_THM,FUNION_FEMPTY_1] THEN
Cases THEN FULL_SIMP_TAC(srw_ss())[FUPDATE_LIST_THM] THEN
SRW_TAC[][FUNION_ASSOC,FUNION_FUPDATE_2,FUNION_FEMPTY_2,FUNION_FUPDATE_1]
QED

Theorem FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME:
 (ALOOKUP ls k = SOME v) ==> (FLOOKUP (fm |++ (REVERSE ls)) k = SOME v)
Proof
SRW_TAC [][FUPDATE_LIST_EQ_APPEND_REVERSE,FLOOKUP_DEF,FUNION_DEF,ALOOKUP_SOME_FAPPLY_alist_to_fmap,MEM_MAP,pairTheory.EXISTS_PROD] THEN
METIS_TAC [ALOOKUP_MEM]
QED

Theorem FLOOKUP_FUPDATE_LIST_ALOOKUP_NONE:
 (ALOOKUP ls k = NONE) ==> (FLOOKUP (fm |++ (REVERSE ls)) k = FLOOKUP fm k)
Proof
SRW_TAC [][FUPDATE_LIST_EQ_APPEND_REVERSE,FLOOKUP_DEF,FUNION_DEF,ALOOKUP_FAILS,MEM_MAP,pairTheory.EXISTS_PROD]
QED

Theorem FUNION_alist_to_fmap:
    !ls fm. FUNION (alist_to_fmap ls) fm = fm |++ (REVERSE ls)
Proof
  Induct THEN1 SRW_TAC[][FUNION_FEMPTY_1,FUPDATE_LIST] THEN
  Q.X_GEN_TAC `p` THEN PairCases_on `p` THEN
  SRW_TAC[][FUPDATE_LIST_THM,alist_to_fmap_thm,FUPDATE_LIST_APPEND] THEN
  SRW_TAC[][FUNION_FUPDATE_1]
QED

Theorem alist_to_fmap_MAP:
  !f1 f2 al. INJ f1 (set (MAP FST al)) UNIV ==>
 (alist_to_fmap (MAP (\ (x,y). (f1 x, f2 y)) al) =
  MAP_KEYS f1 (f2 o_f alist_to_fmap al))
Proof
NTAC 2 GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
Cases THEN SRW_TAC[][INJ_INSERT] THEN
Q.MATCH_ABBREV_TAC `x = MAP_KEYS f1 ((f o_f a) |+ b)` THEN
UNABBREV_ALL_TAC THEN
SRW_TAC[][GSYM FUPDATE_PURGE] THEN
Q.MATCH_ABBREV_TAC `x = MAP_KEYS f1 (fm |+ (k,v))` THEN
`INJ f1 (k INSERT FDOM fm) UNIV` by (
  SRW_TAC[][Abbr`fm`,INJ_INSERT] ) THEN
SRW_TAC[][MAP_KEYS_FUPDATE]
QED

Theorem alist_to_fmap_to_alist:
  !al. fmap_to_alist (alist_to_fmap al) =
       MAP (\k. (k, THE (ALOOKUP al k))) (SET_TO_LIST (set (MAP FST al)))
Proof
SRW_TAC[][fmap_to_alist_def,MAP_EQ_f,MEM_MAP] THEN
Q.MATCH_ASSUM_RENAME_TAC `MEM p al` THEN
PairCases_on `p` THEN SRW_TAC[][] THEN
Cases_on `ALOOKUP al p0` THEN
IMP_RES_TAC ALOOKUP_FAILS THEN
SRW_TAC[][]
QED

Theorem alist_to_fmap_to_alist_PERM:
  !al. ALL_DISTINCT (MAP FST al) ==>
       PERM (fmap_to_alist (alist_to_fmap al)) al
Proof
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
PROVE_TAC[]
QED

Theorem ALOOKUP_LEAST_EL:
  !ls k. ALOOKUP ls k = if MEM k (MAP FST ls) then
         SOME (EL (LEAST n. EL n (MAP FST ls) = k) (MAP SND ls))
         else NONE
Proof
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
Q.MATCH_ASSUM_RENAME_TAC `EL m (MAP FST ls) = FST (EL n ls)` THEN1 (
  Q.EXISTS_TAC `SUC m` THEN
  SRW_TAC[][] ) THEN
Cases_on `n < m` THEN1 METIS_TAC[EL_MAP] THEN
`m < LENGTH ls` by DECIDE_TAC THEN
FULL_SIMP_TAC(srw_ss())[EL_MAP] THEN
Q.MATCH_ASSUM_RENAME_TAC `EL z (h::MAP FST ls) = FST (EL n ls)` THEN
Cases_on `SUC n < z` THEN1 (
  RES_TAC THEN
  FULL_SIMP_TAC(srw_ss())[] THEN
  METIS_TAC[EL_MAP]) THEN
`z < SUC (LENGTH ls)` by DECIDE_TAC THEN
Cases_on `z` THEN FULL_SIMP_TAC (srw_ss()) [EL_MAP] THEN
Q.MATCH_RENAME_TAC `SND (EL m ls) = SND (EL z ls)` THEN
Cases_on `m < z` THEN1 (
  `SUC m < SUC z` by DECIDE_TAC THEN
  RES_TAC THEN
  FULL_SIMP_TAC(srw_ss())[] THEN
  METIS_TAC[EL_MAP] ) THEN
Cases_on `z < m` THEN1 METIS_TAC[EL_MAP] THEN
`m = z` by DECIDE_TAC THEN
SRW_TAC[][]
QED

Theorem ALOOKUP_ALL_DISTINCT_MEM:
  ALL_DISTINCT (MAP FST al) /\ MEM (k,v) al ==>
  (ALOOKUP al k = SOME v)
Proof
rw[ALOOKUP_LEAST_EL] >- (
  rw[MEM_MAP,pairTheory.EXISTS_PROD] >>
  PROVE_TAC[]) >>
fs[MEM_EL] >>
pop_assum (assume_tac o SYM) >>
qho_match_abbrev_tac `EL ($LEAST P) (MAP SND al) = v` >>
`P n` by (
  unabbrev_all_tac >> rw[EL_MAP] ) >>
qspecl_then [`P`,`n`] mp_tac WhileTheory.LESS_LEAST >> rw[] >>
numLib.LEAST_ELIM_TAC >>
conj_tac >- (
  qexists_tac `n` >> rw[] ) >>
rw[] >>
qmatch_rename_tac `EL m (MAP SND al) = v` >>
`~(n < m)` by PROVE_TAC[] >>
`m < LENGTH al` by DECIDE_TAC >>
fs[EL_ALL_DISTINCT_EL_EQ] >>
unabbrev_all_tac >> fs[] >>
`m = n` by PROVE_TAC[] >>
fs[EL_MAP]
QED

Theorem ALL_DISTINCT_fmap_to_alist_keys:
  !fm. ALL_DISTINCT (MAP FST (fmap_to_alist fm))
Proof
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
rw[MAP_EQ_f,Abbr`f1`,Abbr`f2`,Abbr`ls`,DOMSUB_FAPPLY_THM]
QED
val _ = export_rewrites["ALL_DISTINCT_fmap_to_alist_keys"]

Theorem fmap_to_alist_inj:
  !f1 f2. (fmap_to_alist f1 = fmap_to_alist f2) ==> (f1 = f2)
Proof
rw[] >>
qmatch_assum_abbrev_tac `af1 = af2` >>
qsuff_tac `alist_to_fmap af1 = alist_to_fmap af2` >- metis_tac[fmap_to_alist_to_fmap] >>
simp[GSYM fmap_EQ_THM,pairTheory.EXISTS_PROD,MEM_MAP,MEM_fmap_to_alist]
QED

Theorem fmap_to_alist_preserves_FDOM:
  !fm1 fm2. (FDOM fm1 = FDOM fm2) ==> (MAP FST (fmap_to_alist fm1) = MAP FST (fmap_to_alist fm2))
Proof
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
rw[MAP_EQ_f,Abbr`f1`,Abbr`f2`,Abbr`f3`,Abbr`f4`,Abbr`ls`,DOMSUB_FAPPLY_THM]
QED

Theorem PERM_fmap_to_alist:
  PERM (fmap_to_alist fm1) (fmap_to_alist fm2) = (fm1 = fm2)
Proof
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
qmatch_rename_tac `r1 = r2` >>
qmatch_assum_rename_tac `(q,r1) = EL n1 afx` >>
qmatch_assum_rename_tac `(q,r2) = EL n2 afy` >>
rpt (qpat_x_assum `(X,Y) = EL N Z` (assume_tac o SYM)) >>
`LENGTH afy = LENGTH afx` by rw[PERM_LENGTH] >> fs[] >>
metis_tac[pairTheory.PAIR_EQ,pairTheory.FST]
QED

Theorem alist_to_fmap_PERM:
  !l1 l2. PERM l1 l2 /\ ALL_DISTINCT (MAP FST l1) ==> (alist_to_fmap l1 = alist_to_fmap l2)
Proof
rpt strip_tac >>
match_mp_tac (fst (EQ_IMP_RULE PERM_fmap_to_alist)) >>
metis_tac[PERM_TRANS,PERM_SYM,ALL_DISTINCT_PERM,PERM_MAP,alist_to_fmap_to_alist_PERM]
QED

(*---------------------------------------------------------------------------*)
(* Various lemmas from the CakeML project https://cakeml.org                 *)
(*---------------------------------------------------------------------------*)

Theorem ALOOKUP_ALL_DISTINCT_EL:
    !ls n. n < LENGTH ls /\ ALL_DISTINCT (MAP FST ls) ==>
           (ALOOKUP ls (FST (EL n ls)) = SOME (SND (EL n ls)))
Proof
  Induct >> simp[] >>
  Cases >> simp[] >>
  Cases >> simp[] >>
  rw[] >> fs[MEM_MAP] >>
  metis_tac[MEM_EL]
QED

Theorem ALOOKUP_ZIP_MAP_SND:
    !l1 l2 k f.
      (LENGTH l1 = LENGTH l2) ==>
      (ALOOKUP (ZIP(l1,MAP f l2)) = OPTION_MAP f o (ALOOKUP (ZIP(l1,l2))))
Proof
  Induct >> simp[LENGTH_NIL,LENGTH_NIL_SYM,FUN_EQ_THM] >>
  gen_tac >> Cases >> simp[] >> rw[] >> rw[]
QED

Theorem ALOOKUP_FILTER:
    !ls x. ALOOKUP (FILTER (\(k,v). P k) ls) x =
           if P x then ALOOKUP ls x else NONE
Proof
  Induct >> simp[] >> Cases >> simp[] >> rw[] >> fs[] >> metis_tac[]
QED

Theorem ALOOKUP_APPEND_same:
    !l1 l2 l.
      (ALOOKUP l1 = ALOOKUP l2) ==> (ALOOKUP (l1 ++ l) = ALOOKUP (l2 ++ l))
Proof
  rw[ALOOKUP_APPEND,FUN_EQ_THM]
QED

Theorem ALOOKUP_IN_FRANGE:
    !ls k v. (ALOOKUP ls k = SOME v) ==> v IN FRANGE (alist_to_fmap ls)
Proof
  Induct >> simp[] >> Cases >> simp[] >> rw[] >>
  simp[IN_FRANGE,DOMSUB_FAPPLY_THM] >>
  full_simp_tac std_ss [Once(SYM (CONJUNCT1 ALOOKUP_EQ_FLOOKUP)),FLOOKUP_DEF] >>
  fs[] >> METIS_TAC[]
QED

Theorem FRANGE_alist_to_fmap_SUBSET:
  FRANGE (alist_to_fmap ls) SUBSET IMAGE SND (set ls)
Proof
srw_tac[DNF_ss][FRANGE_DEF,SUBSET_DEF,pairTheory.EXISTS_PROD] >>
qmatch_assum_rename_tac `MEM z (MAP FST ls)` >>
qexists_tac `z` >>
match_mp_tac alist_to_fmap_FAPPLY_MEM >>
rw[]
QED

Theorem IN_FRANGE_alist_to_fmap_suff:
  (!v. MEM v (MAP SND ls) ==> P v) ==>
  (!v. v IN FRANGE (alist_to_fmap ls) ==> P v)
Proof
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_alist_to_fmap_SUBSET) >>
fs[MEM_MAP] >>
PROVE_TAC[]
QED

Theorem alist_to_fmap_MAP_matchable:
  !f1 f2 al mal v. INJ f1 (set (MAP FST al)) UNIV /\
  (mal = MAP (\(x,y). (f1 x,f2 y)) al) /\
  (v = MAP_KEYS f1 (f2 o_f alist_to_fmap al)) ==>
  (alist_to_fmap mal = v)
Proof
METIS_TAC[alist_to_fmap_MAP]
QED

Theorem MAP_values_fmap_to_alist:
  !f fm. MAP (\(k,v). (k, f v)) (fmap_to_alist fm) = fmap_to_alist (f o_f fm)
Proof
rw[fmap_to_alist_def,MAP_MAP_o,MAP_EQ_f]
QED

val INJ_I = prove (
``!s t. INJ I s t <=> s SUBSET t``,
SRW_TAC[][INJ_DEF,SUBSET_DEF])

Theorem MAP_KEYS_I[simp]:
  !fm. MAP_KEYS I fm = fm
Proof
rw[GSYM fmap_EQ_THM,MAP_KEYS_def,EXTENSION] >>
metis_tac[MAP_KEYS_def,INJ_I,SUBSET_UNIV,combinTheory.I_THM]
QED

Theorem alist_to_fmap_MAP_values:
  !f (al:('c,'a) alist).
   alist_to_fmap (MAP (\(k,v). (k, f v)) al) = f o_f (alist_to_fmap al)
Proof
rw[] >>
Q.ISPECL_THEN [`I:'c->'c`,`f`,`al`] match_mp_tac alist_to_fmap_MAP_matchable >>
SRW_TAC[][INJ_DEF,SUBSET_DEF,MAP_KEYS_I]
QED

Theorem set_MAP_FST_fmap_to_alist[simp]:
  set (MAP FST (fmap_to_alist fm)) = FDOM fm
Proof
METIS_TAC[fmap_to_alist_to_fmap,FDOM_alist_to_fmap]
QED

Theorem alookup_distinct_reverse:
 !l k. ALL_DISTINCT (MAP FST l) ==> (ALOOKUP (REVERSE l) k = ALOOKUP l k)
Proof
 Induct_on `l` >>
 rw [] >>
 PairCases_on `h` >>
 fs [] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [ALOOKUP_APPEND] >>
 rw [] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [] >>
 imp_res_tac ALOOKUP_MEM >>
 fs [MEM_MAP] >>
 metis_tac [FST]
QED

Theorem flookup_fupdate_list:
 !l k m.
  FLOOKUP (m |++ l) k =
  case ALOOKUP (REVERSE l) k of
     | SOME v => SOME v
     | NONE => FLOOKUP m k
Proof
 ho_match_mp_tac ALOOKUP_ind >>
 rw [FUPDATE_LIST_THM, ALOOKUP_def, FLOOKUP_UPDATE] >>
 BasicProvers.FULL_CASE_TAC >>
 fs [ALOOKUP_APPEND] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [FLOOKUP_UPDATE] >>
 rw [] >>
 imp_res_tac FLOOKUP_FUPDATE_LIST_ALOOKUP_NONE >>
 imp_res_tac FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME >>
 fs [FLOOKUP_UPDATE]
QED

Theorem fupdate_list_funion:
  !m l. m|++l = FUNION (FEMPTY |++l) m
Proof
 Induct_on `l`
 >- rw [FUPDATE_LIST, FUNION_FEMPTY_1] >>
 REWRITE_TAC [FUPDATE_LIST_THM] >>
 rpt GEN_TAC >>
 pop_assum (qspecl_then [`m|+h`] mp_tac) >>
 rw [] >>
 rw [FLOOKUP_EXT, FUN_EQ_THM, FLOOKUP_FUNION] >>
 BasicProvers.EVERY_CASE_TAC >>
 PairCases_on `h` >>
 fs [FLOOKUP_UPDATE, flookup_fupdate_list] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs []
QED

Theorem mem_to_flookup:
 !x y l. ALL_DISTINCT (MAP FST l) /\ MEM (x,y) l ==> (FLOOKUP (FEMPTY |++ l) x = SOME y)
Proof
 Induct_on `l` >>
 rw [] >>
 fs [flookup_fupdate_list] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [ALOOKUP_APPEND] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [] >>
 imp_res_tac ALOOKUP_MEM >>
 imp_res_tac alookup_distinct_reverse >>
 fs [] >>
 res_tac >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [MEM_MAP] >>
 rw [] >>
 metis_tac [FST]
QED

Theorem alookup_filter:
 !f l x. ALOOKUP l x = ALOOKUP (FILTER (\(x',y). x = x') l) x
Proof
 Induct_on `l` >>
 rw [ALOOKUP_def] >>
 PairCases_on `h` >>
 fs []
QED

Definition alist_range_def:
alist_range m = { v | ?k. ALOOKUP m k = SOME v }
End

(* Sorting and permutation based stuff *)

Theorem alookup_stable_sorted:
 !R sort x l.
  transitive R /\ total R /\
  STABLE sort (inv_image R FST)
  ==>
  (ALOOKUP (sort (inv_image R FST) l) x = ALOOKUP l x)
Proof
 rw [] >>
 ONCE_REWRITE_TAC [alookup_filter] >>
 fs [STABLE_DEF, SORTS_DEF] >>
 pop_assum (mp_tac o GSYM o Q.SPEC `(\(x',y). x = x')`) >>
 rw [] >>
 match_mp_tac (METIS_PROVE [] ``(x = x') ==> (f x y = f x' y)``) >>
 pop_assum match_mp_tac >>
 rw [] >>
 PairCases_on `x'` >>
 PairCases_on `y` >>
 fs [transitive_def, total_def] >>
 metis_tac []
QED

Theorem ALOOKUP_ALL_DISTINCT_PERM_same:
    !l1 l2. ALL_DISTINCT (MAP FST l1) /\ PERM (MAP FST l1) (MAP FST l2) /\
            (set l1 = set l2) ==> (ALOOKUP l1 = ALOOKUP l2)
Proof
  simp[EXTENSION] >>
  rw[FUN_EQ_THM] >>
  Cases_on`ALOOKUP l2 x` >- (
    imp_res_tac ALOOKUP_FAILS >>
    imp_res_tac MEM_PERM >>
    fs[FORALL_PROD,MEM_MAP,EXISTS_PROD] >>
    metis_tac[ALOOKUP_FAILS] ) >>
  qmatch_assum_rename_tac`ALOOKUP l2 x = SOME p` >>
  imp_res_tac ALOOKUP_MEM >>
  `ALL_DISTINCT (MAP FST l2)` by (
    metis_tac[ALL_DISTINCT_PERM]) >>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
  metis_tac[]
QED

Theorem FEVERY_alist_to_fmap:
  EVERY P ls ==> FEVERY P (alist_to_fmap ls)
Proof
  Induct_on`ls` \\ simp[FORALL_PROD]
  \\ rw[FEVERY_ALL_FLOOKUP,FLOOKUP_UPDATE]
  \\ pop_assum mp_tac \\ rw[] \\ fs[]
  \\ imp_res_tac ALOOKUP_MEM \\ fs[EVERY_MEM]
QED

Theorem ALL_DISTINCT_FEVERY_alist_to_fmap:
  ALL_DISTINCT (MAP FST ls) ==>
   (FEVERY P (alist_to_fmap ls) <=> EVERY P ls)
Proof
  Induct_on`ls` \\ simp[FORALL_PROD]
  \\ rw[FEVERY_ALL_FLOOKUP,FLOOKUP_UPDATE] \\ fs[FEVERY_ALL_FLOOKUP]
  \\ rw[EQ_IMP_THM]
  \\ pop_assum mp_tac \\ rw[] \\ fs[MEM_MAP,EXISTS_PROD]
  \\ metis_tac[ALOOKUP_MEM]
QED

Definition AFUPDKEY_def:
  (AFUPDKEY k f [] = []) /\
  (AFUPDKEY k f ((k',v)::rest) =
     if k = k' then (k,f v)::rest
     else (k',v) :: AFUPDKEY k f rest)
End

val AFUPDKEY_ind = theorem"AFUPDKEY_ind";

Theorem AFUPDKEY_ALOOKUP:
  ALOOKUP (AFUPDKEY k2 f al) k1 =
    case ALOOKUP al k1 of
        NONE => NONE
      | SOME v => if k1 = k2 then SOME (f v) else SOME v
Proof
  Induct_on `al` >> simp[AFUPDKEY_def, FORALL_PROD] >> rw[]
  >- (Cases_on `ALOOKUP al k1` >> simp[]) >>
  simp[]
QED

Theorem MAP_FST_AFUPDKEY[simp]:
  MAP FST (AFUPDKEY f k alist) = MAP FST alist
Proof
  Induct_on `alist` >> simp[AFUPDKEY_def, FORALL_PROD] >> rw[]
QED

Theorem AFUPDKEY_unchanged:
  !k f alist.
   (!v. (ALOOKUP alist k = SOME v) ==> (f v = v))
   ==> (AFUPDKEY k f alist = alist)
Proof
  ho_match_mp_tac AFUPDKEY_ind
  \\ rw[AFUPDKEY_def]
QED

Theorem AFUPDKEY_o:
  AFUPDKEY k f1 (AFUPDKEY k f2 al) = AFUPDKEY k (f1 o f2) al
Proof
  Induct_on `al` >> simp[AFUPDKEY_def, FORALL_PROD] >>
  rw[AFUPDKEY_def]
QED

Theorem AFUPDKEY_eq:
  !k f1 l f2.
   (!v. (ALOOKUP l k = SOME v) ==> (f1 v = f2 v))
   ==> (AFUPDKEY k f1 l = AFUPDKEY k f2 l)
Proof
  ho_match_mp_tac AFUPDKEY_ind \\ rw[AFUPDKEY_def]
QED

Theorem AFUPDKEY_I:
  AFUPDKEY n I = I
Proof
  simp[FUN_EQ_THM]
  \\ Induct
  \\ simp[AFUPDKEY_def,FORALL_PROD]
QED

Theorem LENGTH_AFUPDKEY[simp]:
  !ls. LENGTH (AFUPDKEY k f ls) = LENGTH ls
Proof
  Induct \\ simp[AFUPDKEY_def]
  \\ Cases \\ rw[AFUPDKEY_def]
QED

Theorem AFUPDKEY_comm:
 !k1 k2 f1 f2 l. k1 <> k2 ==>
  (AFUPDKEY k2 f2 (AFUPDKEY k1 f1 l) =
   AFUPDKEY k1 f1 (AFUPDKEY k2 f2 l))
Proof
  Induct_on`l` >> rw[] >> fs[AFUPDKEY_def] >>
  Cases_on`h`>> fs[AFUPDKEY_def] >>
  CASE_TAC >> fs[AFUPDKEY_def] >>
  CASE_TAC >> fs[AFUPDKEY_def]
QED

Definition ADELKEY_def:
  ADELKEY k alist = FILTER (\p. FST p <> k) alist
End

Theorem MEM_ADELKEY[simp]:
  !al. MEM (k1,v) (ADELKEY k2 al) <=> k1 <> k2 /\ MEM (k1,v) al
Proof
  Induct >> simp[ADELKEY_def, FORALL_PROD] >>
  rw[MEM_FILTER] >> metis_tac[]
QED

Theorem ALOOKUP_ADELKEY:
  !al. ALOOKUP (ADELKEY k1 al) k2
       = if k1 = k2 then NONE else ALOOKUP al k2
Proof
  simp[ADELKEY_def] >> Induct >>
  simp[FORALL_PROD] >> rw[] >> simp[]
QED

Theorem ADELKEY_AFUPDKEY_same[simp]:
  !fd f ls. ADELKEY fd (AFUPDKEY fd f ls) = ADELKEY fd ls
Proof
  ho_match_mp_tac AFUPDKEY_ind
  \\ rw[AFUPDKEY_def,ADELKEY_def]
QED

Theorem ADELKEY_unchanged:
  !x ls. ((ADELKEY x ls = ls) <=> ~MEM x (MAP FST ls))
Proof
  simp[MEM_MAP, ADELKEY_def, FORALL_PROD] >>
  Induct_on‘ls’ >> simp[AllCaseEqs(), FORALL_PROD] >>
  ‘!P h. FILTER P ls <> h::ls’
    by (rpt strip_tac >>
        ‘LENGTH (h::ls) <= LENGTH ls’ by metis_tac[LENGTH_FILTER_LEQ] >>
        fs[]) >>
  simp[] >> metis_tac[]
QED

Theorem ADELKEY_AFUPDKEY:
  !ls f x y. x <> y ==>
    (ADELKEY x (AFUPDKEY y f ls) = (AFUPDKEY y f (ADELKEY x ls)))
Proof
  Induct >>  rw[ADELKEY_def,AFUPDKEY_def] >>
  Cases_on`h` >> fs[AFUPDKEY_def] >> TRY CASE_TAC >> fs[ADELKEY_def]
QED

Theorem FLOOKUP_FUPDATE_LIST:
  !xs k m. FLOOKUP (m |++ xs) k =
           case ALOOKUP (REVERSE xs) k of
           | NONE => FLOOKUP m k
           | SOME x => SOME x
Proof
  Induct \\ fs [FUPDATE_LIST,pairTheory.FORALL_PROD,ALOOKUP_APPEND]
  \\ fs [FLOOKUP_UPDATE] \\ rw [] \\ fs []
  \\ Cases_on ‘ALOOKUP (REVERSE xs) k’ \\ fs []
QED
