open HolKernel bossLib boolLib pred_setTheory lcsymtacs
val _ = new_theory "fset"

val num_set_foldl_raw_def = tDefine "num_set_foldl_raw"`
num_set_foldl_raw f a s =
if FINITE s then if s = {} then a else
let n = LEAST n. n ∈ s in num_set_foldl_raw f (f a n) (s DELETE n)
else ARB` (
WF_REL_TAC `measure (CARD o SND o SND)` >>
simp_tac bool_ss [GSYM AND_IMP_INTRO] >>
ho_match_mp_tac FINITE_INDUCT >>
rw[] >> numLib.LEAST_ELIM_TAC >>
rw[] >> PROVE_TAC[])

val num_set_foldl_exists = prove(
``∃fold. ∀s. FINITE s ⇒ ∀f a. fold f a s =
  if s = {} then a else
  let n = LEAST n. n ∈ s in
  fold f (f a n) (s DELETE n)``,
qexists_tac `num_set_foldl_raw` >>
rw[Once num_set_foldl_raw_def] >>
qsuff_tac `s ≠ {} ⇒ (n = n')` >> rw[] >>
prove_tac[NOT_IN_FINITE,INFINITE_NUM_UNIV,MEMBER_NOT_EMPTY])
val num_set_foldl_def = new_specification(
"num_set_foldl_def",["num_set_foldl"],num_set_foldl_exists)

(* TODO: move to list theory *)
val FOLDL2_def = Define`
  (FOLDL2 f a (b::bs) (c::cs) = FOLDL2 f (f a b c) bs cs) /\
  (FOLDL2 f a bs cs = a)`

val EVERY2_def = Define`
  (EVERY2 P (a::as) (b::bs) = P a b /\ EVERY2 P as bs) /\
  (EVERY2 P as bs = (as = []) /\ (bs = []))`
val _ = export_rewrites["EVERY2_def"]

val EVERY2_cong = store_thm(
"EVERY2_cong",
``!l1 l1' l2 l2' P P'.
  (l1 = l1') /\ (l2 = l2') /\
  (!x y. MEM x l1' /\ MEM y l2' ==> (P x y = P' x y)) ==>
  (EVERY2 P l1 l2 = EVERY2 P' l1' l2')``,
Induct THEN SIMP_TAC (srw_ss()) [EVERY2_def] THEN
GEN_TAC THEN Cases THEN SRW_TAC[][EVERY2_def] THEN
METIS_TAC[])
val _ = DefnBase.export_cong "EVERY2_cong"

val EVERY2_LENGTH = store_thm(
"EVERY2_LENGTH",
``!P l1 l2. EVERY2 P l1 l2 ==> (LENGTH l1 = LENGTH l2)``,
GEN_TAC THEN Induct THEN SRW_TAC[][EVERY2_def] THEN
Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()) [EVERY2_def])

val EVERY2_mono = store_thm(
"EVERY2_mono",
``(!x y. P x y ==> Q x y)
  ==> EVERY2 P l1 l2 ==> EVERY2 Q l1 l2``,
STRIP_TAC THEN
MAP_EVERY Q.ID_SPEC_TAC [`l2`,`l1`] THEN
Induct THEN
SRW_TAC [][EVERY2_def] THEN
IMP_RES_TAC EVERY2_LENGTH THEN
Cases_on `l2` THEN
FULL_SIMP_TAC (srw_ss()) [EVERY2_def])
val _ = export_mono "EVERY2_mono"

val _ = export_theory();
