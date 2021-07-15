open HolKernel boolLib bossLib Parse BasicProvers dep_rewrite
open armv86aTheory armv86a_terminationTheory armv86a_typesTheory
open arm8Theory arm8Lib arm8_stepTheory arm8_stepLib
open wordsTheory bitstringTheory listTheory rich_listTheory
open integerTheory int_arithTheory arithmeticTheory
open wordsLib bitstringLib intLib

val _ = new_theory "l3_equivalence_lemmas";
val _ = set_grammar_ancestry ["arm8_step", "arm8", "armv86a_termination"];

val _ = wordsLib.output_words_as_bin();
val _ = wordsLib.guess_lengths();

val _ = numLib.prefer_num();
val _ = intLib.deprecate_int()

val _ = Globals.show_assums := false;

val _ = augment_srw_ss [
    bitstringLib.v2w_n2w_ss,
    bitstringLib.BITSTRING_GROUND_ss,
    wordsLib.WORD_ss
  ];

(******************************************************************************)

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


(******************************************************************************)

Theorem shiftr:
  shiftr w i = w >>> (nat_of_int i)
Proof
  EVAL_TAC
QED

Theorem shiftl:
  shiftl w i = w << (nat_of_int i)
Proof
  EVAL_TAC
QED

Theorem nat_of_int:
  nat_of_int i = if i < 0 then 0 else Num i
Proof
  rw[sail2_valuesTheory.nat_of_int_def, INT_ABS]
QED

Theorem nat_of_int_Num[simp]:
  0 ≤ i ⇒ nat_of_int i = Num i
Proof
  rw[nat_of_int] >> ARITH_TAC
QED

Theorem bools_of_nat_aux_def:
  ∀ len n acc.
    bools_of_nat_aux len n acc = fixwidth (nat_of_int len) (n2v n) ++ acc
Proof
  ho_match_mp_tac sail2_valuesAuxiliaryTheory.bools_of_nat_aux_ind_rw >>
  rw[] >> Cases_on `len = 0` >>
  rw[Once sail2_valuesAuxiliaryTheory.bools_of_nat_aux_rw, nat_of_int] >>
  gvs[INT_NOT_LE]
  >- (simp[fixwidth_REPLICATE, DROP_LENGTH_NIL])
  >- (simp[fixwidth_REPLICATE, DROP_LENGTH_NIL])
  >- (irule FALSITY >> ARITH_TAC)
  >- (irule FALSITY >> ARITH_TAC)
  >- (irule FALSITY >> ARITH_TAC)
  >- (irule FALSITY >> ARITH_TAC) >>
  `Num (len - 1) = Num len - 1` by ARITH_TAC >> pop_assum SUBST_ALL_TAC >>
  Cases_on `n < 2` >> gvs[]
  >- (
    gvs[NUMERAL_LESS_THM, n2v, fixwidth_REPLICATE] >>
      (
      IF_CASES_TAC >> gvs[SUB_LEFT_LESS, NOT_LESS]
      >- (
        Cases_on `Num len` >> gvs[ADD1] >>
        simp[GSYM SNOC_APPEND] >> Cases_on `n` >> gvs[]
        )
      >- (`Num len = 1 ∨ Num len = 2` by ARITH_TAC >> gvs[PAD_LEFT] >> EVAL_TAC)
      )
    ) >>
  gvs[SUB_LEFT_LESS, NOT_LESS] >>
  drule (cj 3 n2v) >> strip_tac >> simp[] >>
  DEP_REWRITE_TAC[fixwidth_APPEND] >> simp[] >> ARITH_TAC
QED

Theorem bools_of_nat:
  ∀ len n.
    bools_of_nat len n = fixwidth (nat_of_int len) (n2v n)
Proof
  rw[sail2_valuesTheory.bools_of_nat_def, bools_of_nat_aux_def]
QED

Theorem add_one_bool_ignore_overflow_def:
  (add_one_bool_ignore_overflow [] = []) ∧
  (∀x xs. add_one_bool_ignore_overflow (SNOC x xs) =
    if x then SNOC F (add_one_bool_ignore_overflow xs)
    else SNOC T xs)
Proof
  simp[sail2_valuesTheory.add_one_bool_ignore_overflow_def] >>
  ntac 2 $ simp[Once sail2_valuesTheory.add_one_bool_ignore_overflow_aux_def] >>
  rw[]
QED

Theorem add_one_bool_ignore_overflow:
  ∀a.
    add_one_bool_ignore_overflow a =
      if EVERY I a then (REPLICATE (LENGTH a) F) else add a [T]
Proof
  Induct using SNOC_INDUCT >> rw[] >> gvs[]
  >- rw[add_one_bool_ignore_overflow_def]
  >- (
    once_rewrite_tac[GSYM SNOC_APPEND] >>
    rewrite_tac[add_one_bool_ignore_overflow_def] >> simp[] >>
    once_rewrite_tac[GSYM SNOC_APPEND] >> rewrite_tac[SNOC_REPLICATE] >>
    simp[GSYM ADD1]
    )
  >- (
    every_case_tac >> gvs[EVERY_MEM, EXISTS_MEM] >> res_tac >>
    once_rewrite_tac[GSYM SNOC_APPEND] >>
    rewrite_tac[add_one_bool_ignore_overflow_def] >> rw[]
    >- (
      rw[bool_list_eq, v2n_APPEND, v2n_add, LENGTH_add] >>
      `MAX (LENGTH a) 1 = LENGTH a ∧ MAX (LENGTH a + 1) 1 = LENGTH a + 1` by (
        rw[MAX_DEF] >> Cases_on `a` >> gvs[]) >>
      rw[] >> simp[LENGTH_n2v] >>
      `LOG 2 (2 * v2n a + 2) = SUC $ LOG 2 (v2n a + 1)` by
        simp[GSYM logrootTheory.LOG_MULT] >>
      simp[ADD1, MAX_DEF]
      )
    >- (
      rw[bool_list_eq] >- rw[v2n_APPEND, v2n_add] >>
      simp[LENGTH_add] >>
      `MAX (LENGTH a + 1) 1 = LENGTH a + 1` by (
        rw[MAX_DEF] >> Cases_on `a` >> gvs[]) >>
      `v2n (a ++ [F]) + 1 = v2n (a ++ [T])` by simp[v2n_APPEND] >> simp[] >>
      qspec_then `a ++ [T]` assume_tac LENGTH_n2v_v2n_LESS >> gvs[MAX_DEF]
      )
    )
  >- (
    once_rewrite_tac[GSYM SNOC_APPEND] >>
    rewrite_tac[add_one_bool_ignore_overflow_def] >> rw[] >>
    rw[bool_list_eq] >- rw[v2n_APPEND, v2n_add] >>
    simp[LENGTH_add] >>
    `MAX (LENGTH a + 1) 1 = LENGTH a + 1` by (
      rw[MAX_DEF] >> Cases_on `a` >> gvs[]) >>
    `v2n (a ++ [F]) + 1 = v2n (a ++ [T])` by simp[v2n_APPEND] >> simp[] >>
    qspec_then `a ++ [T]` assume_tac LENGTH_n2v_v2n_LESS >> gvs[MAX_DEF]
    )
QED

Theorem nat_of_bools_aux:
  ∀bs aux. nat_of_bools_aux aux bs = v2n (n2v aux ++ bs)
Proof
  Induct >> rw[sail2_valuesTheory.nat_of_bools_aux_def, v2n_APPEND, v2n, EXP]
QED

Theorem nat_of_bools[simp]:
  nat_of_bools = v2n
Proof
  rw[FUN_EQ_THM, sail2_valuesTheory.nat_of_bools_def, nat_of_bools_aux, v2n]
QED

Theorem bools_of_int_def:
  ∀ len n.
    bools_of_int len n =
      let bs = fixwidth (nat_of_int len) (n2v (Num (ABS n))) in
      if 0 ≤ n then bs
      else if v2n bs = 0 then REPLICATE (nat_of_int len) F else
      add (MAP $¬ bs) [T]
Proof
  rw[sail2_valuesTheory.bools_of_int_def, bools_of_nat]
  >- (irule FALSITY >> ARITH_TAC)
  >- (irule FALSITY >> ARITH_TAC)
  >- (irule FALSITY >> ARITH_TAC)
  >- gvs[v2n_0, add_one_bool_ignore_overflow, EVERY_MAP, SF ETA_ss]
  >- (
    gvs[v2n_0, add_one_bool_ignore_overflow, EVERY_MAP, SF ETA_ss] >>
    IF_CASES_TAC >> gvs[combinTheory.o_DEF, EVERY_MEM, EXISTS_MEM]
    )
QED

Theorem LENGTH_bools_of_int:
  LENGTH (bools_of_int len n) = nat_of_int len
Proof
  rw[sail2_valuesTheory.bools_of_int_def, LENGTH_add] >>
  gvs[nat_of_int, bools_of_nat] >> rw[]
  >- simp[fixwidth_def, DROP_LENGTH_NIL, add_one_bool_ignore_overflow] >>
  Cases_on `len = 0`
  >- gvs[fixwidth_def, DROP_LENGTH_NIL, add_one_bool_ignore_overflow] >>
  simp[add_one_bool_ignore_overflow, EVERY_MAP, SF ETA_ss] >>
  IF_CASES_TAC >> gvs[combinTheory.o_DEF, LENGTH_add] >>
  `MAX (Num len) 1 = Num len` by (simp[MAX_DEF] >> ARITH_TAC) >> simp[] >>
  qmatch_goalsub_abbrev_tac `MAP _ fix` >>
  `fix ≠ []` by (
    qsuff_tac `LENGTH fix ≠ 0` >- rw[] >>
    unabbrev_all_tac >> rewrite_tac[length_fixwidth] >> ARITH_TAC) >>
  qspec_then `MAP $¬ fix` assume_tac LENGTH_n2v_v2n_LESS >> gvs[] >>
  qsuff_tac `LENGTH (n2v (v2n (MAP $¬ fix) + 1)) ≤ LENGTH fix`
  >- (unabbrev_all_tac >> rw[] >> gvs[length_fixwidth] >> rw[MAX_DEF]) >>
  simp[LENGTH_n2v, v2n_0, EVERY_MAP, GSYM LESS_EQ] >>
  `LENGTH fix = Num len` by (unabbrev_all_tac >> gvs[length_fixwidth]) >> rw[] >>
  irule LOG_LT >> simp[] >> gvs[GSYM SUB_LEFT_LESS] >>
  qspec_then `MAP $¬ fix` assume_tac v2n_lt >> gvs[] >>
  qsuff_tac `v2n (MAP $¬ fix) ≠ 2 ** Num len - 1` >- (rw[] >> gvs[]) >>
  CCONTR_TAC >> qspec_then `MAP $¬ fix` assume_tac $ v2n_EVERY_T >> gvs[] >>
  gvs[EVERY_MAP, EXISTS_MEM, EVERY_MEM]
QED

Theorem v2n_fixwidth:
  v2n (fixwidth l n) = (v2n n) MOD (2 ** l)
Proof
  rw[fixwidth_REPLICATE, v2n_APPEND, v2n_REPLICATE_F]
  >- (
    qspec_then `n` assume_tac v2n_lt >>
    irule LESS_LESS_EQ_TRANS >> goal_assum drule >>
    irule_at Any $ iffLR logrootTheory.LE_EXP_ISO >> simp[]
    ) >>
  `∃a b. n = a ++ b ∧ LENGTH b = l` by (
    gvs[NOT_LESS_EQUAL] >>
    qexistsl_tac [`TAKE (LENGTH n - l) n`,`DROP (LENGTH n - l) n`] >> simp[]) >>
  gvs[DROP_APPEND, DROP_LENGTH_NIL, v2n_APPEND, v2n_lt]
QED

(*
Theorem bools_of_int:
  ∀len n.
    nat_of_int len ≤ dimindex (:α) ⇒
    bools_of_int len n = fixwidth (nat_of_int len) $
      w2v (i2w n : α word)
Proof
  rw[bool_list_eq, LENGTH_bools_of_int] >>
  rw[bools_of_int_def, v2n_fixwidth, v2n_REPLICATE_F] >> (* TODO *)
QED



Theorem get_slice_int:
  get_slice_int hi i lo = ARB (i2w i)
Proof
  simp[sail2_operators_mwordsTheory.get_slice_int_def] >>
  simp[sail2_operatorsTheory.get_slice_int_bv_def] >>
  simp[sail2_valuesTheory.instance_Sail2_values_Bitvector_Machine_word_mword_dict_def] >>
  simp[sail2_valuesTheory.subrange_list_def, sail2_valuesTheory.subrange_list_dec_def] >>
  simp[sail2_valuesTheory.subrange_list_inc_def] >>
  simp[bools_of_int_def] >> rw[]
  gvs[nat_of_int]
  simp[nat_of_int]
  f "bools_of_int"
  type_of ``bools_of_int``
  find_consts ``:bool list -> 'a word``
  f "v2w"

  f "subrange_list"
  f "instance_Sail2_values_Bitvector_Machine_word_mword_dict"
  f "get_slice_int"
QED
*)

Theorem bool_of_bitU_bitU_of_bool[simp]:
  bool_of_bitU (bitU_of_bool b) = SOME b
Proof
  Cases_on `b` >>
  rw[sail2_valuesTheory.bitU_of_bool_def, sail2_valuesTheory.bool_of_bitU_def]
QED

Theorem HD_MAP:
  l ≠ [] ⇒ HD (MAP f l) = f (HD l)
Proof
  Cases_on `l` >> rw[]
QED

(******************************************************************************)

val _ = export_theory ();
