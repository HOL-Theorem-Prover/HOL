open HolKernel bossLib boolLib pred_setTheory lcsymtacs
val _ = new_theory "fset"

val f = ``λp n. WHILE ($~ o p) SUC n``
fun l q = ``∀p n. ^q p n = if p n then n else ^q p (n + (1:num))``
val least_aux_WHILE = prove(l f,
rw[] >> rw[Once whileTheory.WHILE,arithmeticTheory.ADD1])
val x = genvar (type_of f)
val least_aux_exists = prove(mk_exists(x,l x),
exists_tac f >> ACCEPT_TAC least_aux_WHILE)
val least_aux_def = new_specification("least_aux_def",["least_aux"],least_aux_exists)

val least_aux_LEAST = store_thm(
"least_aux_LEAST",
``(∃n. p n) ∧ (∃n. ¬ (p n)) ⇒ (least_aux p 0 = LEAST n. p n)``,
strip_tac >> numLib.LEAST_ELIM_TAC >>
rw[] >- prove_tac[] >>
qmatch_rename_tac `least_aux p 0 = m` [] >>
qsuff_tac `∀n. n ≤ m ⇒ (least_aux p n = m)` >- rw[] >>
Induct_on `m-n` >> rw[] >- (
  qmatch_assum_rename_tac `q ≤ m` [] >>
  `q = m` by DECIDE_TAC >>
  rw[Once least_aux_def] ) >>
qmatch_assum_rename_tac `q ≤ m` [] >>
`q < m` by DECIDE_TAC >>
`¬p q` by res_tac >>
rw[Once least_aux_def] >>
first_x_assum (match_mp_tac o MP_CANON) >>
rw[] >> DECIDE_TAC)

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
  let n = least_aux (λn. n ∈ s) 0 in
  fold f (f a n) (s DELETE n)``,
qexists_tac `num_set_foldl_raw` >>
rw[Once num_set_foldl_raw_def] >>
qsuff_tac `s ≠ {} ⇒ (n = n')` >> rw[] >>
unabbrev_all_tac >>
ho_match_mp_tac (GSYM least_aux_LEAST) >>
prove_tac[NOT_IN_FINITE,INFINITE_NUM_UNIV,MEMBER_NOT_EMPTY])
val num_set_foldl_def = new_specification(
"num_set_foldl_def",["num_set_foldl"],num_set_foldl_exists)

val _ = export_theory();
