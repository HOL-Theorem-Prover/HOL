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

val _ = export_theory();
