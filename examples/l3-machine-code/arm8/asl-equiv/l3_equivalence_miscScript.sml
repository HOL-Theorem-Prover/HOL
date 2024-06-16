open HolKernel boolLib bossLib Parse BasicProvers dep_rewrite
open wordsTheory bitstringTheory integer_wordTheory listTheory rich_listTheory
     integerTheory arithmeticTheory realTheory intrealTheory
open wordsLib bitstringLib intLib

val _ = new_theory "l3_equivalence_misc";

val _ = wordsLib.output_words_as_bin();
val _ = wordsLib.guess_lengths();

val _ = numLib.temp_prefer_num();
val _ = intLib.deprecate_int()

val _ = augment_srw_ss [
    bitstringLib.v2w_n2w_ss,
    bitstringLib.BITSTRING_GROUND_ss,
    wordsLib.WORD_ss
  ];

(****************************************)

Theorem PAD_LEFT_0[simp]:
  PAD_LEFT e 0 acc = acc
Proof
  rw[PAD_LEFT]
QED

Theorem n2v:
  (n2v 0 = [F]) ∧
  (n2v 1 = [T]) ∧
  (2 ≤ n ⇒ n2v n = (n2v (n DIV 2)) ++ [n MOD 2 ≠ 0])
Proof
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  completeInduct_on `n` >> rw[] >>
  simp[n2v_def, boolify_reverse_map, numposrepTheory.num_to_bin_list_def] >>
  rw[Once numposrepTheory.n2l_def]
QED

Theorem LENGTH_n2v:
  LENGTH (n2v n) = if n = 0 then 1 else SUC (LOG 2 n)
Proof
  completeInduct_on `n` >>
  IF_CASES_TAC >> gvs[n2v] >>
  DEP_ONCE_REWRITE_TAC[logrootTheory.LOG_RWT] >> simp[] >>
  IF_CASES_TAC >> gvs[]
  >- (`n = 1` by DECIDE_TAC >> pop_assum SUBST_ALL_TAC >> gvs[n2v]) >>
  gvs[NOT_LESS, n2v] >>
  IF_CASES_TAC >> gvs[DIV_EQ_0]
QED

Theorem PAD_LEFT:
  PAD_LEFT e n l = (REPLICATE (n - LENGTH l) e) ++ l
Proof
  Cases_on `n ≤ LENGTH l` >> rw[PAD_LEFT]
  >- (
    pop_assum mp_tac >> once_rewrite_tac[GSYM SUB_EQ_0] >>
    disch_then SUBST_ALL_TAC >> simp[]
    ) >>
  rw[LIST_EQ_REWRITE, EL_REPLICATE]
QED

Theorem bitify_APPEND:
  ∀l1 l2 a. bitify a (l1 ++ l2) = bitify (bitify a l1) l2
Proof
  rw[bitify_reverse_map]
QED

Theorem v2n_APPEND:
  ∀a b. v2n (a ++ b) = v2n b + (2 ** LENGTH b * v2n a)
Proof
  rw[v2n_def, bitify_APPEND] >>
  rw[bitify_reverse_map] >>
  gvs[numposrepTheory.num_from_bin_list_def, numposrepTheory.l2n_APPEND]
QED

Theorem v2n:
  v2n [] = 0 ∧
  v2n (b::bs) = if b then 2 ** LENGTH bs + v2n bs else v2n bs
Proof
  rw[] >> once_rewrite_tac[CONS_APPEND] >>
  once_rewrite_tac[v2n_APPEND] >> simp[]
QED

Theorem v2n_SNOC:
  v2n [] = 0 ∧
  v2n (SNOC b bs) = 2 * v2n bs + if b then 1 else 0
Proof
  rw[SNOC_APPEND, v2n_APPEND]
QED

Theorem v2n_0:
  ∀bs. v2n bs = 0 ⇔ EVERY $¬ bs
Proof
  Induct >> rw[v2n]
QED

Theorem n2v_TIMES2:
  ∀n. n2v (2 * n) = if n = 0 then n2v 0 else n2v n ++ [F]
Proof
  Cases >> gvs[] >> rw[n2v] >>
  once_rewrite_tac[MULT_COMM] >> simp[MULT_DIV]
QED

Theorem n2v_2_POW:
  ∀n. n2v (2 ** n) = T::REPLICATE n F
Proof
  Induct >> rw[EXP, n2v_TIMES2] >>
  rewrite_tac[GSYM REPLICATE, GSYM SNOC_REPLICATE] >> simp[]
QED

Theorem LENGTH_n2v_v2n:
  LENGTH (n2v (v2n bs)) = if EVERY $¬ bs then 1 else SUC (LOG 2 (v2n bs))
Proof
  rw[LENGTH_n2v, v2n_0]
QED

Theorem v2n_MOD2[simp]:
  ∀n. v2n [n MOD 2 ≠ 0] = n MOD 2
Proof
  rw[] >> Cases_on `n MOD 2` >> gvs[] >> rename1 `SUC m` >>
  Cases_on `m` >> gvs[] >> ARITH_TAC
QED

Theorem MOD2_v2n[simp]:
  ∀l. (v2n l MOD 2 ≠ 0) = if l = [] then F else LAST l
Proof
  Cases using SNOC_CASES >> gvs[v2n_SNOC] >> rw[]
QED

Theorem n2v_alt:
  ∀n. n ≠ 0 ⇒ ∃bs. n2v n = T::bs ∧ v2n bs + 2 ** LENGTH bs = n
Proof
  strip_tac >> completeInduct_on `n` >> rw[] >>
  Cases_on `n` >> rw[n2v] >> rename1 `SUC m` >>
  Cases_on `m` >> rw[n2v] >>
  last_x_assum $ qspec_then `SUC (SUC n) DIV 2` mp_tac >> simp[] >>
  impl_tac >- ARITH_TAC >>
  rw[] >> simp[v2n_APPEND] >>
  qmatch_goalsub_abbrev_tac `m MOD _` >>
  qspec_then `m` assume_tac bitTheory.DIV_MULT_THM2 >>
  qpat_x_assum `_ = m DIV 2` $ assume_tac o GSYM >>
  pop_assum SUBST_ALL_TAC >> gvs[LEFT_ADD_DISTRIB, EXP_ADD] >>
  qsuff_tac `m MOD 2 ≤ m` >> rw[] >> gvs[] >> ARITH_TAC
QED

Theorem n2v_v2n_lemma_T[local]:
  ∀a. n2v (v2n (T::a)) = T::a
Proof
  strip_tac >> completeInduct_on `LENGTH a` >> rw[] >>
  simp[v2n] >>
  Cases_on `LENGTH a` >> gvs[ADD1, EXP_ADD] >>
  DEP_ONCE_REWRITE_TAC[n2v] >> simp[] >>
  conj_tac >- (Cases_on `2 ** n` >> gvs[]) >>
  Cases_on `a` using SNOC_CASES >> gvs[] >>
  last_x_assum $ qspec_then `LENGTH l` assume_tac >> gvs[] >>
  pop_assum $ qspec_then `l` assume_tac >> gvs[] >>
  simp[v2n_APPEND, ADD_DIV_RWT] >>
  once_rewrite_tac[MULT_COMM] >> simp[MULT_DIV] >>
  `v2n [x] DIV 2 = 0` by (Cases_on `x` >> gvs[]) >> simp[] >> gvs[v2n, ADD1]
QED

Theorem LOG_2_v2n_T:
  LOG 2 (v2n (T::rest)) = LENGTH rest
Proof
  rw[v2n] >> qspec_then `rest` assume_tac v2n_lt >>
  simp[logrootTheory.LOG_ADD]
QED

Theorem LENGTH_n2v_v2n_LESS:
  ∀bs. LENGTH (n2v (v2n bs)) ≤ if bs = [] then 1 else LENGTH bs
Proof
  rw[LENGTH_n2v_v2n] >> gvs[]
  >- (Cases_on `bs` >> gvs[]) >>
  gvs[combinTheory.o_DEF, EXISTS_MEM] >>
  last_x_assum mp_tac >> rw[Once MEM_SPLIT_APPEND_first] >>
  `v2n (pfx ++ [T] ++ sfx) = v2n (T::sfx)` by (
    once_rewrite_tac[GSYM APPEND_ASSOC] >>
    rewrite_tac[Once v2n_APPEND] >> simp[] >> gvs[v2n_0, EVERY_MEM]) >>
  simp[LOG_2_v2n_T]
QED

Theorem fixwidth_REPLICATE:
  ∀len l. fixwidth len l =
    if LENGTH l ≤ len then REPLICATE (len - LENGTH l) F ++ l
    else DROP (LENGTH l - len) l
Proof
  rw[fixwidth, GSYM pad_left_extend, PAD_LEFT] >>
  `len = LENGTH l` by gvs[]
  >- gvs[] >>
  pop_assum SUBST_ALL_TAC >> gvs[]
QED

Theorem fixwidth_REPLICATE_alt:
  ∀len l. fixwidth len l =
    if LENGTH l < len then REPLICATE (len - LENGTH l) F ++ l
    else DROP (LENGTH l - len) l
Proof
  rw[fixwidth, GSYM pad_left_extend, PAD_LEFT]
QED

Theorem fixwidth_APPEND:
  ∀l1 n l2.
  LENGTH l2 ≤ n ⇒
    fixwidth n (l1 ++ l2) = fixwidth (n - LENGTH l2) l1 ++ l2
Proof
  rw[fixwidth_REPLICATE, DROP_APPEND]
  >- (irule FALSITY >> ARITH_TAC) >>
  `LENGTH l2 - n = 0` by gvs[] >> pop_assum SUBST_ALL_TAC >> simp[]
QED

Theorem n2v_v2n:
  ∀a. a ≠ [] ⇒ a = fixwidth (LENGTH a) (n2v (v2n a))
Proof
  rw[] >> `1 ≤ LENGTH a` by (Cases_on `a` >> gvs[]) >>
  Cases_on `v2n a < 2`
  >- (
    reverse $ gvs[wordsTheory.NUMERAL_LESS_THM, fixwidth_REPLICATE]
    >- (
      rewrite_tac[GSYM SNOC_APPEND] >> rewrite_tac[SNOC_REPLICATE] >>
      rw[LIST_EQ_REWRITE, EL_REPLICATE] >> gvs[v2n_0, EVERY_EL]
      ) >>
    Cases_on `a` using SNOC_CASES >> gvs[v2n_SNOC] >>
    `v2n l = 0` by (Cases_on `v2n l` >> gvs[] >> every_case_tac >> gvs[]) >>
    gvs[] >> every_case_tac >> gvs[v2n_0] >>
    rw[LIST_EQ_REWRITE, EL_REPLICATE] >> gvs[EVERY_EL]
    ) >>
  simp[fixwidth_REPLICATE] >>
  qspec_then `a` assume_tac LENGTH_n2v_v2n_LESS >> gvs[] >>
  Cases_on `EVERY $¬ a` >> rw[] >- gvs[GSYM v2n_0] >>
  gvs[combinTheory.o_DEF, EXISTS_MEM] >>
  pop_assum mp_tac >> simp[Once MEM_SPLIT_APPEND_first] >> strip_tac >> gvs[] >>
  `v2n (pfx ++ [T] ++ sfx) = v2n (T::sfx)` by (
    once_rewrite_tac[GSYM APPEND_ASSOC] >>
    rewrite_tac[Once v2n_APPEND] >> simp[] >> gvs[v2n_0, EVERY_MEM]) >>
  simp[n2v_v2n_lemma_T, LOG_2_v2n_T, ADD1] >>
  rw[LIST_EQ_REWRITE, EL_REPLICATE] >>
  gvs[MEM_EL] >> metis_tac[]
QED

Theorem add_COMM:
  ∀a b. add a b = add b a
Proof
  rw[add_def] >> rw[Once MAX_COMM]
QED

Theorem add_F:
  ∀a. add [F] a = if a = [] then [F] else a
Proof
  simp[add_def, zero_extend_def, PAD_LEFT] >> rw[] >>
  `MAX 1 (LENGTH a) = LENGTH a` by (Cases_on `a` >> gvs[MAX_DEF]) >>
  pop_assum SUBST_ALL_TAC >>
  qspecl_then [`LENGTH a`,`n2v (v2n a)`] assume_tac fixwidth_REPLICATE >>
  qspec_then `a` assume_tac LENGTH_n2v_v2n_LESS >> gvs[] >>
  metis_tac[n2v_v2n]
QED

Theorem n2v_ADD:
  ∀a b. n2v (a + b) = add (n2v a) (n2v b)
Proof
  Induct >> rw[]
  >- (
    simp[add_F] >> IF_CASES_TAC >> gvs[] >>
    Cases_on `b` >> gvs[] >> Cases_on `n` >> gvs[n2v]
    ) >>
  simp[add_def, zero_extend_def, PAD_LEFT] >>
  simp[LENGTH_n2v] >> IF_CASES_TAC >> gvs[] >>
  rpt $ irule_at Any logrootTheory.LOG_LE_MONO >> simp[]
QED

Theorem v2n_add:
  v2n (add as bs) = v2n as + v2n bs
Proof
  rw[add_def, zero_extend_def, PAD_LEFT] >>
  rename1 `REPLICATE foo _` >> Induct_on `foo` >> gvs[v2n]
QED

Theorem LENGTH_add_MAX:
  LENGTH (add as bs) =
    MAX (MAX (LENGTH as) (LENGTH bs)) (LENGTH (n2v (v2n as + v2n bs)))
Proof
  rw[add_def, zero_extend_def, PAD_LEFT, MAX_DEF]
QED

Theorem bool_list_eq:
  ∀as bs.
    as = bs ⇔ v2n as = v2n bs ∧ LENGTH as = LENGTH bs
Proof
  rw[] >> eq_tac >> rw[] >>
  qspec_then `as` assume_tac $ GSYM n2v_v2n >>
  qspec_then `bs` assume_tac $ GSYM n2v_v2n >>
  Cases_on `as = []` >> gvs[] >>
  Cases_on `bs = []` >> gvs[]
QED

Theorem LOG_2_ADD1_lemma[local]:
  ∀a n. 2 ** n ≤ a ∧ a < 2 ** (SUC n) - 1 ⇒ LOG 2 a = LOG 2 (a + 1)
Proof
  rw[] >> `LOG 2 a = n` by (irule logrootTheory.LOG_UNIQUE >> simp[]) >>
  pop_assum SUBST_ALL_TAC >> irule EQ_SYM >>
  irule logrootTheory.LOG_UNIQUE >> simp[]
QED

Theorem LOG_2_ADD1:
  ∀a. a ≠ 0 ∧ (∀n. a ≠ 2 ** SUC n - 1) ⇒ LOG 2 a = LOG 2 (a + 1)
Proof
  rw[] >> irule LOG_2_ADD1_lemma >>
  qspecl_then [`2`,`a`] assume_tac logrootTheory.LOG >> gvs[] >>
  goal_assum $ drule_at Any >>
  last_x_assum $ qspec_then `LOG 2 a` assume_tac >> ARITH_TAC
QED

Theorem v2n_EVERY_T:
  ∀bs. EVERY (λx. x) bs ⇔ v2n bs = 2 ** LENGTH bs - 1
Proof
  Induct >> rw[v2n] >> gvs[] >> simp[ADD1, EXP_ADD] >>
  qspec_then `bs` assume_tac v2n_lt >> gvs[]
QED

Theorem LOG_LT:
  n < b ** e ∧ 0 < n ∧ 1 < b ⇒ LOG b n < e
Proof
  rw[] >> qspecl_then [`b`,`n`] assume_tac logrootTheory.LOG >> gvs[] >>
  irule_at Any $ iffRL logrootTheory.LT_EXP_ISO >>
  goal_assum drule >> ARITH_TAC
QED

Theorem v2n_REPLICATE_F:
  ∀l. v2n (REPLICATE l F) = 0
Proof
  Induct >> rw[v2n]
QED

Theorem extract_all_bits:
  ∀a. ((dimindex(:α) - 1) >< 0) (a : α word) = a
Proof
  rw[] >> irule WORD_EXTRACT_ID >>
  assume_tac w2n_lt >> gvs[dimword_def, arithmeticTheory.ADD1] >>
  assume_tac EXISTS_HB >> gvs[]
QED

Theorem HD_MAP:
  l ≠ [] ⇒ HD (MAP f l) = f (HD l)
Proof
  Cases_on `l` >> rw[]
QED

Theorem v2w_word1_eq[simp]:
  (∀b. v2w [b] : word1 = 0w ⇔ ¬b) ∧
  (∀b. v2w [b] : word1 = 1w ⇔ b)
Proof
  conj_tac >> Cases >> gvs[]
QED

Theorem extract_bit:
  ∀i w. i < dimindex (:α) ⇒ (i >< i) w : 1 word = v2w [word_bit i (w : α word)]
Proof
  rw[] >> bitstringLib.Cases_on_v2w `w` >>
  simp[word_extract_v2w] >>
  irule $ iffLR WORD_EQ >> rw[] >>
  simp[bit_v2w, testbit_el, word_bits_v2w, field_def, shiftr_def, fixwidth] >>
  simp[DROP_TAKE, TAKE1, HD_DROP] >>
  Cases_on `EL (dimindex (:α) - (i + 1)) v` >> gvs[] >> WORD_DECIDE_TAC
QED

Theorem extract_bit_64:
  ∀i w. i < 64 ⇒ (i >< i) w : 1 word = v2w [word_bit i (w : 64 word)]
Proof
  rw[extract_bit]
QED

Theorem w2v_not_NIL:
  ∀w. w2v w ≠ []
Proof
  rw[] >> qsuff_tac `LENGTH (w2v w) ≠ 0` >- rw[] >>
  rewrite_tac[length_w2v] >> assume_tac EXISTS_HB >> gvs[]
QED

Theorem word_ror_alt:
  ∀r (a : α word).  r < dimindex (:α) ⇒
    a ⇄ r = a ≪ (dimindex (:α) − r) ‖ a ⋙ r
Proof
  rw[] >> bitstringLib.Cases_on_v2w `a` >> gvs[] >>
  simp[word_ror_v2w, rotate_def] >> IF_CASES_TAC >> gvs[] >>
  simp[word_lsl_v2w, word_lsr_v2w, rotate_def, word_or_v2w] >>
  simp[Once v2w_11] >> simp[field_def, ADD1] >>
  `shiftr v 0 = v` by simp[shiftr_def] >> simp[fixwidth] >>
  simp[bor_def, bitwise_def, shiftl_def, shiftr_def, PAD_LEFT, PAD_RIGHT, MAX_DEF] >>
  simp[fixwidth_REPLICATE, GSYM MAP_DROP, GSYM ZIP_DROP, DROP_APPEND] >>
  `dimindex (:α) − r − dimindex (:α) = 0` by ARITH_TAC >> simp[] >>
  rw[LIST_EQ_REWRITE, EL_DROP, EL_MAP, EL_ZIP, EL_APPEND_EQN, EL_REPLICATE] >> rw[]
QED

Theorem FLAT_REPLICATE_singleton[simp]:
  FLAT (REPLICATE n [e]) = REPLICATE n e
Proof
  Induct_on `n` >> rw[]
QED

Theorem w2i_alt_def:
  ∀w. w2i w = if word_msb w then -&w2n (word_abs w) else &w2n (word_abs w)
Proof
  rw[word_abs_def, word_msb_neg, integer_wordTheory.w2i_def]
QED

Theorem word_quot_alt_def:
  ∀a b. word_quot a b =
    let d = n2w (w2n (word_abs a) DIV w2n (word_abs b)) in
    if word_msb a ∧ word_msb b then d
    else if word_msb a then -d
    else if word_msb b then -d
    else d
Proof
  rw[word_quot_def, word_div_def, word_abs_def, word_msb_neg] >> gvs[] >>
  metis_tac[WORD_SUB_INTRO]
QED

Theorem INT_DIV_NEGL:
  ∀n m. m ≠ 0 ⇒
    -&n / &m = if n MOD m = 0 then -&(n DIV m) else -&((n DIV m) + 1) :int
Proof
  rw[] >> rw[int_div, ZERO_DIV] >> gvs[] >> ARITH_TAC
QED

Theorem INT_CEILING_NEG_DIV:
  ∀a b. b ≠ 0 ⇒ ⌈-&a / &b⌉ = -⌊&a / &b⌋
Proof
  rw[] >> rw[INT_CEILING_INT_FLOOR, INT_FLOOR_EQNS, INT_DIV_NEGL] >> gvs[]
  >- (
    qpat_x_assum `_ = _ / _` mp_tac >> simp[] >>
    once_rewrite_tac[GSYM neg_rat] >> simp[] >>
    simp[REAL_EQ_RDIV_EQ] >>
    gvs[MOD_EQ_0_DIVISOR]
    )
  >- (
    qpat_x_assum `_ ≠ _ / _` mp_tac >> simp[] >>
    once_rewrite_tac[GSYM neg_rat] >> simp[] >>
    simp[REAL_EQ_RDIV_EQ] >>
    qspec_then `b` assume_tac $ cj 1 DIVISION >> gvs[] >>
    pop_assum $ qspec_then `a` assume_tac >> gvs[]
    )
  >- ARITH_TAC
QED

Theorem v2w_fixwidth_dimindex:
  dimindex(:α) ≤ l ⇒
  v2w (fixwidth l v) : α word = v2w v
Proof
  rw[GSYM WORD_EQ, bit_v2w] >>
  Cases_on `x < LENGTH v` >> gvs[NOT_LESS, testbit_geq_len] >>
  simp[testbit_el, fixwidth_REPLICATE, Once COND_RAND,
       EL_APPEND_EQN, rich_listTheory.EL_REPLICATE, EL_DROP]
QED

Theorem TAKE_REPLICATE:
  TAKE n (REPLICATE m e) = REPLICATE (MIN n m) e
Proof
  rw[LIST_EQ_REWRITE, MIN_DEF, EL_TAKE,
     rich_listTheory.EL_REPLICATE, LENGTH_TAKE_EQ]
QED

Theorem MAX_ALT_DEF:
  MAX a b = if a ≤ b then b else a
Proof
  rw[MAX_DEF] >> gvs[]
QED

Theorem MIN_ALT_DEF:
  MIN a b = if a ≤ b then a else b
Proof
  rw[MIN_DEF] >> gvs[]
QED

Theorem w2n_word_abs_lt:
  ∀w. w2n (word_abs w : α word) ≤ 2 ** (dimindex(:α) - 1)
Proof
  rw[] >> simp[integer_wordTheory.word_abs_w2i, dimword_def] >>
  qspec_then `w` assume_tac integer_wordTheory.w2i_ge >>
  qspec_then `w` assume_tac integer_wordTheory.w2i_le >>
  gvs[INT_MAX_def, wordsTheory.INT_MIN_def] >>
  rename1 `ABS a` >>
  qmatch_abbrev_tac ‘N MOD D1 ≤ D2’ >>
  ‘D2 < D1’ by simp[Abbr‘D1’, Abbr‘D2’] >>
  ‘N ≤ D2’ by (simp[Abbr‘N’, Abbr‘D2’] >> Cases_on ‘a’ >> gs[INT_SUB]) >>
  simp[]
QED

(* copied from HOL/examples/machine-code/hoare-triple/addressScript.sml  *)
Theorem word_arith_lemma2:
  ∀n m. n2w n - (n2w m) : α word =
    if n < m then - (n2w (m - n)) else n2w (n - m)
Proof
  REPEAT STRIP_TAC \\ Cases_on `n < m` \\ ASM_REWRITE_TAC []
  \\ FULL_SIMP_TAC bool_ss [NOT_LESS,LESS_EQ]
  \\ FULL_SIMP_TAC bool_ss [LESS_EQ_EXISTS,ADD1,DECIDE ``n+1+p-n = 1+p:num``]
  \\ REWRITE_TAC [GSYM word_add_n2w,WORD_SUB_PLUS,WORD_SUB_REFL]
  \\ REWRITE_TAC [GSYM WORD_SUB_PLUS]
  \\ REWRITE_TAC [word_sub_def,WORD_ADD_0,DECIDE ``m+p-m=p:num``]
  \\ REWRITE_TAC [GSYM WORD_ADD_ASSOC] \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ REWRITE_TAC [GSYM word_sub_def,WORD_SUB_ADD]
QED

Triviality v2n_add_less_limit:
  ∀xs. EXISTS I xs ⇒  v2n (MAP $¬ xs) + 1 < 2 ** LENGTH xs
Proof
  rw[] >> gvs[] >>
  `v2n (MAP $¬ xs) ≠ 2 ** LENGTH (MAP $¬ xs) - 1` by (
    gvs[GSYM v2n_EVERY_T, EXISTS_MAP, EXISTS_MEM]) >>
  qspec_then `MAP $¬ xs` assume_tac v2n_lt >> gvs[]
QED

Theorem v2n_add_v2n_not:
  ∀xs. v2n xs + v2n (MAP $¬ xs) = 2 ** LENGTH xs - 1
Proof
  Induct using SNOC_INDUCT >> rw[v2n_SNOC, MAP_SNOC] >> simp[EXP] >>
  rewrite_tac[ADD_ASSOC] >> rewrite_tac[GSYM LEFT_ADD_DISTRIB] >>
  first_x_assum SUBST1_TAC >> simp[] >>
  simp[LEFT_ADD_DISTRIB] >>
  qmatch_goalsub_abbrev_tac `foo - 1` >>
  qsuff_tac `1 ≤ foo` >> rw[] >> unabbrev_all_tac >> simp[]
QED

Theorem forall_fixwidth:
  ∀n. (∀xs. LENGTH xs = n ⇒ P xs) ⇒ (∀xs. P (fixwidth n xs))
Proof
  rw []
QED

Theorem neg_v2n_lemma:
  -n2w (v2n xs) =
    if v2n (fixwidth (dimindex(:α)) xs) = 0 then v2w (REPLICATE (dimindex (:α)) F)
    else v2w (add (MAP $¬ (fixwidth (dimindex(:α)) xs)) [T]) : α word
Proof
  irule EQ_TRANS >> qexists_tac `-n2w (v2n (fixwidth (dimindex(:α)) xs))` >>
  conj_tac
  >- (
    rewrite_tac[WORD_EQ_NEG, bitstringTheory.n2w_v2n] >>
    rewrite_tac[v2w_11] >> gvs[]
    ) >>
  qid_spec_tac `xs` >>
  ho_match_mp_tac $ Q.SPEC `dimindex(:α)` forall_fixwidth >> rw[v2n_0]
  >- (
    qsuff_tac `v2n xs = 0` >> rw[REPLICATE_compute] >> simp[v2n_0] >>
    rw[v2w_def] >> simp[testbit] >> simp[EL_REPLICATE] >> WORD_DECIDE_TAC
    ) >>
  gvs[word_2comp_n2w, GSYM bitstringTheory.n2w_v2n,
      add_def, zero_extend_def, PAD_LEFT, GSYM REPLICATE_GENLIST,
      v2n_APPEND, v2n_REPLICATE_F, MOD_MOD, dimword_def] >>
  qspec_then `xs` assume_tac v2n_lt >> gvs[] >>
  `v2n xs ≠ 0` by gvs[v2n_0, EXISTS_MEM, EVERY_MEM] >>
  `EXISTS I xs` by gvs[EXISTS_MEM] >>
  drule v2n_add_less_limit >> rw[] >>
  gvs[SUB_RIGHT_EQ] >> rewrite_tac[ADD_ASSOC] >> simp[v2n_add_v2n_not]
QED

Theorem LENGTH_add:
  LENGTH (add (MAP $¬ ys) [T]) = if EXISTS I ys then LENGTH ys else LENGTH ys + 1
Proof
  rw[] >> gvs[]
  >- (
    gvs[LENGTH_add_MAX] >> reverse $ rw[MAX_DEF] >- gvs[] >>
    qpat_x_assum `LENGTH _ < _` mp_tac >>
    simp[LENGTH_n2v, NOT_LESS, LE_LT1, ADD1] >>
    irule LOG_LT >> simp[v2n_add_less_limit]
    ) >>
  Cases_on `ys` using SNOC_CASES >> gvs[] >>
  simp[add_def, MAX_DEF, ADD1] >>
  qmatch_goalsub_abbrev_tac `v2n foo` >>
  `v2n foo = 2 ** LENGTH foo - 1` by (
    unabbrev_all_tac >> simp[GSYM v2n_EVERY_T] >> gvs[EVERY_MAP, EVERY_MEM]) >>
  unabbrev_all_tac >> simp[ADD1] >>
  `1 < 2 ** (LENGTH l + 1)` by rw[GSYM ADD1, EXP] >> simp[] >>
  simp[n2v_2_POW, zero_extend_def, PAD_LEFT]
QED

Triviality LENGTH_ADD:
  ∀m n. LENGTH xs = m + n ⇔
        ∃ys zs. LENGTH ys = m ∧ LENGTH zs = n ∧ xs = ys ++ zs
Proof
  Induct_on ‘xs’ \\ fs [] \\ rw []
  \\ Cases_on ‘m’ \\ fs [] \\ fs [ADD1] \\ rw []
  \\ asm_rewrite_tac [DECIDE “m + 1 = k + (n + 1) ⇔  m = n + k:num”]
  \\ rw [] \\ eq_tac \\ rw []
  THEN1 (qexists_tac ‘h::ys’ \\ fs [ADD1])
  \\ Cases_on ‘ys’ \\ gvs [ADD1]
  \\ metis_tac []
QED

Theorem LENGTH_eq_64 = “LENGTH xs = 64”
  |> (SIMP_CONV std_ss [LENGTH_EQ_NUM_compute]
      THENC SIMP_CONV bool_ss [PULL_EXISTS]);

Theorem LENGTH_eq_128 = “LENGTH xs = 128”
  |> SIMP_CONV std_ss
        [LENGTH_eq_64,PULL_EXISTS,APPEND,
        LENGTH_ADD |> Q.SPECL [‘64’,‘64’] |> SIMP_RULE std_ss []];

Theorem v2w_TAKE_64_fixwidth_128:
  v2w (TAKE 64 (fixwidth 128 xs)) = (127 >< 64) (n2w (v2n xs):word128) : word64
Proof
  simp_tac std_ss [fcpTheory.CART_EQ]
  \\ once_rewrite_tac [bitstringTheory.word_index_v2w]
  \\ fs [word_extract_def,w2w,word_bits_def,fcpTheory.FCP_BETA,n2w_v2n]
  \\ once_rewrite_tac [bitstringTheory.word_index_v2w] \\ fs [] \\ rw []
  \\ ‘testbit (i + 64) xs = testbit (i + 64) (fixwidth 128 xs)’ by (
        simp[testbit, el_fixwidth] >> rw[] >> eq_tac >> rw[])
  \\ fs []
  \\ qid_spec_tac ‘xs’
  \\ ho_match_mp_tac $ Q.SPEC `128` forall_fixwidth
  \\ strip_tac
  \\ rename [‘LENGTH ys = _’]
  \\ pop_assum kall_tac
  \\ strip_tac
  \\ gvs [LENGTH_eq_128]
  \\ Cases_on ‘i’ THEN1 EVAL_TAC
  \\ rpt (Cases_on ‘n’ THEN1 EVAL_TAC
          \\ Cases_on ‘n'’ THEN1 EVAL_TAC
          \\ fs [ADD1])
QED

Theorem v2w_REPLICATE_F[simp]:
  v2w (REPLICATE n F ++ l) = v2w l
Proof
  srw_tac[fcpLib.FCP_ss][v2w_def] >>
  simp[testbit, EL_APPEND_EQN, EL_REPLICATE] >> eq_tac >> rw[]
QED

Theorem v2w_PAD_LEFT[simp]:
  v2w (PAD_LEFT F n l) = v2w l
Proof
  srw_tac[fcpLib.FCP_ss][v2w_def] >>
  simp[testbit, PAD_LEFT, EL_APPEND_EQN, EL_REPLICATE] >> eq_tac >> rw[]
QED

Theorem sw2sw_word1:
  sw2sw (1w : word1) = -1w : α word ∧
  sw2sw (0w : word1) = 0w : α word
Proof
  `0b1w : 1 word = -1w` by simp[] >>
  pop_assum SUBST_ALL_TAC >> rewrite_tac[sw2sw_word_T] >> simp[]
QED

Theorem v2n_w2v[simp]:
  v2n (w2v w) = w2n w
Proof
  Cases_on_v2w `w` >>
  simp[w2n_v2w, bitTheory.MOD_2EXP_def] >>
  DEP_REWRITE_TAC[LESS_MOD] >> simp[v2n_lt] >>
  simp[w2v_v2w]
QED

Theorem v2n_DROP_w2v:
  v2n (DROP n (w2v (w: α word))) = w2n w MOD 2 ** (dimindex(:α) - n)
Proof
  rw[] >> Cases_on_v2w `w` >>
  simp[w2n_v2w, bitTheory.MOD_2EXP_def] >>
  simp[w2v_v2w] >>
  `v2n v MOD 2 ** LENGTH v = v2n v` by (
    DEP_ONCE_REWRITE_TAC[LESS_MOD] >> simp[v2n_lt]) >>
  simp[] >>
  rpt $ pop_assum kall_tac >> map_every qid_spec_tac [`v`,`n`] >>
  Induct >> rw[v2n_lt] >>
  Cases_on `v` >> rw[v2n] >>
  DEP_ONCE_REWRITE_TAC[GSYM bitTheory.MOD_PLUS_RIGHT] >> conj_tac >- simp[] >>
  qsuff_tac `2 ** LENGTH t MOD 2 ** (LENGTH t - n) = 0`
  >- (disch_then SUBST_ALL_TAC >> simp[]) >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `_ MOD _ ** foo` >>
  `foo ≤ LENGTH t` by (unabbrev_all_tac >> gvs[]) >>
  drule LESS_EQUAL_ADD >> rw[] >> gvs[] >>
  rpt $ pop_assum kall_tac >>
  Induct_on `p` >> simp[ADD1] >>
  map_every (rewrite_tac o single) [ADD_ASSOC, GSYM ADD1, EXP] >>
  DEP_ONCE_REWRITE_TAC[GSYM MOD_TIMES2] >> simp[]
QED

Theorem MOD_ADDITION:
  0 < c ⇒
  (a + b) MOD c =
    if a MOD c + b MOD c < c then a MOD c + b MOD c else
    a MOD c + b MOD c - c
Proof
  rw[] >- (DEP_ONCE_REWRITE_TAC[GSYM MOD_PLUS] >> simp[]) >>
  gvs[NOT_LESS] >>
  `a MOD c + b MOD c < c + c` by (
    qspecl_then [`a`,`c`] assume_tac MOD_LESS >>
    qspecl_then [`b`,`c`] assume_tac MOD_LESS >> simp[]) >>
  qabbrev_tac `ab = a MOD c + b MOD c` >>
  DEP_ONCE_REWRITE_TAC[GSYM MOD_PLUS] >> simp[] >>
  drule LESS_EQUAL_ADD >> rw[] >> simp[]
QED

Theorem MOD_SUBTRACT:
  0 < c ⇒
  (a - b) MOD c =
    if a ≤ b then 0
    else if b MOD c ≤ a MOD c then a MOD c - b MOD c
    else c + a MOD c - b MOD c
Proof
  rw[MAX_DEF, MIN_DEF] >> gvs[NOT_LESS_EQUAL] >>
  last_x_assum assume_tac >> drule LESS_ADD >> rw[] >> gvs[] >>
  gvs[MOD_ADDITION] >> rw[] >> gvs[NOT_LESS, SUB_LEFT_LESS_EQ] >>
  qpat_x_assum `_ ≤ _` mp_tac >> simp[NOT_LESS_EQUAL]
QED

Theorem ZIP_REPLICATE:
  ∀n x y. ZIP (REPLICATE n x, REPLICATE n y) = REPLICATE n (x,y)
Proof
  Induct >> rw[]
QED


(****************************************)

val _ = export_theory();

