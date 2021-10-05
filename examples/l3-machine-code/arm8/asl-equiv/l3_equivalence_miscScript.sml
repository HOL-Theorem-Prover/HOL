open HolKernel boolLib bossLib Parse BasicProvers dep_rewrite
open wordsTheory bitstringTheory integer_wordTheory listTheory rich_listTheory
     integerTheory arithmeticTheory realTheory intrealTheory
open wordsLib bitstringLib intLib

val _ = new_theory "l3_equivalence_misc";

val _ = wordsLib.output_words_as_bin();
val _ = wordsLib.guess_lengths();

val _ = numLib.prefer_num();
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

Theorem LENGTH_add:
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
  irule $ iffLR WORD_EQ >> rw[] >> Cases_on `x` >> gvs[] >>
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
  rename1 `ABS a` >> qmatch_goalsub_abbrev_tac `dim - 1` >>
  `0 < dim` by (unabbrev_all_tac >> gvs[]) >> qpat_x_assum `Abbrev _` kall_tac >>
  `ABS a ≤ 2 ** (dim - 1)` by (
    simp[INT_ABS_LE] >> Cases_on `dim` >> gvs[ADD1] >>
    last_x_assum kall_tac >> ARITH_TAC) >>
  ntac 2 $ last_x_assum kall_tac >>
  qspec_then `a` assume_tac INT_ABS_POS >> rename1 `Num posve` >>
  Cases_on `posve` >> gvs[] >> Cases_on `dim` >> gvs[EXP]
QED

(****************************************)

val _ = export_theory();

