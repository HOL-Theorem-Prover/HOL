open HolKernel boolLib bossLib Parse finite_mapTheory listTheory pred_setTheory

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
val _ = export_rewrites ["MEM_fmap_to_alist"]

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

val FDOM_alist_to_fmap = Q.store_thm(
"FDOM_alist_to_fmap",
`!al.FDOM (alist_to_fmap al) = set (MAP FST al)`,
Induct THEN SRW_TAC [][alist_to_fmap_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [alist_to_fmap_def]);

val alist_to_fmap_prefix = Q.store_thm(
"alist_to_fmap_prefix",
`!ls l1 l2.
 (alist_to_fmap l1 = alist_to_fmap l2) ==>
 (alist_to_fmap (ls ++ l1) = alist_to_fmap (ls ++ l2))`,
Induct THEN SRW_TAC [][] THEN
Cases_on `h` THEN SRW_TAC [][] THEN METIS_TAC []);

val FUPDATE_LIST_EQ_APPEND_REVERSE = Q.store_thm(
"FUPDATE_LIST_EQ_APPEND_REVERSE",
`!ls fm. fm |++ ls = alist_to_fmap (REVERSE ls ++ fmap_to_alist fm)`,
Induct THEN SRW_TAC [][FUPDATE_LIST_THM] THEN
Cases_on `h` THEN
Q.MATCH_ABBREV_TAC `alist_to_fmap (X ++ l1) = alist_to_fmap (X ++ Y ++ l2)` THEN
Q_TAC SUFF_TAC `alist_to_fmap (X ++ l1) = alist_to_fmap (X ++ (Y ++ l2))`
THEN1 METIS_TAC [APPEND_ASSOC] THEN
MATCH_MP_TAC alist_to_fmap_prefix THEN
UNABBREV_ALL_TAC THEN
SRW_TAC [][]);

val ALOOKUP_prefix = Q.store_thm(
"ALOOKUP_prefix",
`!ls k ls2.
 ((ALOOKUP ls k = SOME v) ==>
  (ALOOKUP (ls ++ ls2) k = SOME v)) /\
 ((ALOOKUP ls k = NONE) ==>
  (ALOOKUP (ls ++ ls2) k = ALOOKUP ls2 k))`,
HO_MATCH_MP_TAC ALOOKUP_ind THEN
SRW_TAC [][]);

val FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME = Q.store_thm(
"FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME",
`(ALOOKUP ls k = SOME v) ==> (FLOOKUP (fm |++ (REVERSE ls)) k = SOME v)`,
SRW_TAC [][FUPDATE_LIST_EQ_APPEND_REVERSE] THEN
METIS_TAC [ALOOKUP_prefix]);

val FLOOKUP_FUPDATE_LIST_ALOOKUP_NONE = Q.store_thm(
"FLOOKUP_FUPDATE_LIST_ALOOKUP_NONE",
`(ALOOKUP ls k = NONE) ==> (FLOOKUP (fm |++ (REVERSE ls)) k = FLOOKUP fm k)`,
SRW_TAC [][FUPDATE_LIST_EQ_APPEND_REVERSE] THEN
SRW_TAC [][ALOOKUP_prefix] THEN
METIS_TAC [ALOOKUP_EQ_FLOOKUP,fmap_to_alist_to_fmap]);

val _ = export_theory ();

