open HolKernel boolLib bossLib Parse BasicProvers dep_rewrite
open armv86aTheory armv86a_terminationTheory armv86a_typesTheory
open arm8Theory arm8Lib arm8_stepTheory arm8_stepLib
open wordsTheory bitstringTheory listTheory rich_listTheory
open integerTheory int_arithTheory arithmeticTheory
open wordsLib bitstringLib intLib
open l3_equivalence_miscTheory

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


(********************* Word operations *******************)

Theorem shiftr[simp]:
  shiftr w i = w >>> (nat_of_int i)
Proof
  EVAL_TAC
QED

Theorem shiftl[simp]:
  shiftl w i = w << (nat_of_int i)
Proof
  EVAL_TAC
QED

Theorem nat_of_int[simp]:
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
      rw[bool_list_eq, v2n_APPEND, v2n_add, LENGTH_add_MAX] >>
      `MAX (LENGTH a) 1 = LENGTH a ∧ MAX (LENGTH a + 1) 1 = LENGTH a + 1` by (
        rw[MAX_DEF] >> Cases_on `a` >> gvs[]) >>
      rw[] >> simp[LENGTH_n2v] >>
      `LOG 2 (2 * v2n a + 2) = SUC $ LOG 2 (v2n a + 1)` by
        simp[GSYM logrootTheory.LOG_MULT] >>
      simp[ADD1, MAX_DEF]
      )
    >- (
      rw[bool_list_eq] >- rw[v2n_APPEND, v2n_add] >>
      simp[LENGTH_add_MAX] >>
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
    simp[LENGTH_add_MAX] >>
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
  >- (irule FALSITY >> ARITH_TAC)
  >- (irule FALSITY >> ARITH_TAC)
  >- gvs[v2n_0, add_one_bool_ignore_overflow, EVERY_MAP, SF ETA_ss]
  >- (
    gvs[v2n_0, add_one_bool_ignore_overflow, EVERY_MAP, SF ETA_ss] >>
    IF_CASES_TAC >> gvs[combinTheory.o_DEF, EVERY_MEM, EXISTS_MEM]
    )
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
  rw[sail2_valuesTheory.bools_of_int_def, LENGTH_add_MAX] >>
  gvs[nat_of_int, bools_of_nat] >> rw[]
  >- simp[fixwidth_def, DROP_LENGTH_NIL, add_one_bool_ignore_overflow]
  >- simp[fixwidth_def, DROP_LENGTH_NIL, add_one_bool_ignore_overflow] >>
  Cases_on `len = 0`
  >- gvs[fixwidth_def, DROP_LENGTH_NIL, add_one_bool_ignore_overflow] >>
  simp[add_one_bool_ignore_overflow, EVERY_MAP, SF ETA_ss] >>
  IF_CASES_TAC >> gvs[combinTheory.o_DEF, LENGTH_add_MAX] >>
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

Theorem ROR[simp]:
  ROR (a : α word) b = word_ror a (Num (b % &dimindex (:α)))
Proof
  simp[ROR_def, sail2_operators_mwordsTheory.or_vec_def] >>
  assume_tac $ EXISTS_HB >> gvs[] >>
  IF_CASES_TAC >> gvs[] >>
  qspecl_then [`b`,`&dimindex (:α)`] assume_tac INT_MOD_BOUNDS >> gvs[] >>
  IF_CASES_TAC >> gvs[] >- (irule FALSITY >> ARITH_TAC) >>
  IF_CASES_TAC >> gvs[] >- (irule FALSITY >> ARITH_TAC) >>
  qpat_abbrev_tac `rot = b % _` >>
  `∃r. rot = &r` by ARITH_TAC >> pop_assum SUBST_ALL_TAC >> gvs[INT_SUB] >>
  simp[word_ror_alt]
QED

Theorem repeat[simp]:
  ∀n e. repeat e n = FLAT $ REPLICATE (nat_of_int n) e
Proof
  rw[Once sail2_valuesAuxiliaryTheory.repeat_rw]
  >- (`n = 0` by ARITH_TAC >> simp[])
  >- (irule FALSITY >> ARITH_TAC)
  >- (irule FALSITY >> ARITH_TAC) >>
  qsuff_tac `∀m e. repeat e &m = FLAT $ REPLICATE m e`
  >- (`∃m. n = &SUC m` by ARITH_TAC >> gvs[INT_SUB]) >>
  Induct >> rw[Once sail2_valuesAuxiliaryTheory.repeat_rw, INT_SUB]
QED

Theorem integer_subrange_pos:
  lo ≤ hi ∧ hi - lo + 1 = dimindex(:α) ⇒
  integer_subrange (&i) (&hi) (&lo) : α word =
  v2w (field hi lo (fixwidth (hi + 1) (n2v i)))
Proof
  simp[integer_subrange_def] >>
  simp[INT_SUB_CALCULATE, INT_ADD_CALCULATE] >>
  rewrite_tac [``get_slice_int (&dimindex(:α)) (&i) (&lo)`` |>
    SIMP_CONV (srw_ss()) [
      sail2_operators_mwordsTheory.get_slice_int_def,
      sail2_operatorsTheory.get_slice_int_bv_def,
      sail2_valuesTheory.instance_Sail2_values_Bitvector_Machine_word_mword_dict_def,
      bools_of_int_def,
      sail2_valuesTheory.subrange_list_def,
      sail2_valuesTheory.subrange_list_dec_def,
      sail2_valuesTheory.subrange_list_inc_def
      ]] >>
  LET_ELIM_TAC >>
  `hi' = &hi` by (unabbrev_all_tac >> ARITH_TAC) >> pop_assum SUBST_ALL_TAC >>
  `¬(&hi + 1i < 0)` by (unabbrev_all_tac >> ARITH_TAC) >> gvs[] >>
  gvs[INT_ADD_CALCULATE] >>
  `top = &hi` by (unabbrev_all_tac >> gvs[] >> ARITH_TAC) >> gvs[] >>
  unabbrev_all_tac >> gvs[INT_ADD_CALCULATE, INT_SUB_CALCULATE] >>
  qmatch_goalsub_abbrev_tac `TAKE len` >>
  `0 < len` by (unabbrev_all_tac >> gvs[]) >>
  `TAKE len (fixwidth (hi + 1) (n2v i)) =
    shiftr (fixwidth (hi + 1) (n2v i)) lo` by simp[shiftr_def] >>
  pop_assum SUBST_ALL_TAC >>
  `shiftr (fixwidth (hi + 1) (n2v i)) lo =
   field hi lo (fixwidth (hi + 1) (n2v i))` by simp[field_def, ADD1] >>
  pop_assum $ SUBST_ALL_TAC >> simp[]
QED

Theorem integer_subrange_neg:
  lo ≤ hi ∧ hi - lo + 1 = dimindex(:α) ⇒
  integer_subrange (-&i) (&hi) (&lo) : α word =
  if i MOD 2 ** (hi + 1) = 0 then 0w else
  v2w (field hi lo (add (MAP $¬ (fixwidth (hi + 1) (n2v i))) [T]))
Proof
  simp[integer_subrange_def] >>
  simp[INT_SUB_CALCULATE, INT_ADD_CALCULATE] >>
  rewrite_tac [``get_slice_int (&dimindex(:α)) (-&i) (&lo)`` |>
    SIMP_CONV (srw_ss()) [
      sail2_operators_mwordsTheory.get_slice_int_def,
      sail2_operatorsTheory.get_slice_int_bv_def,
      sail2_valuesTheory.instance_Sail2_values_Bitvector_Machine_word_mword_dict_def,
      bools_of_int_def,
      sail2_valuesTheory.subrange_list_def,
      sail2_valuesTheory.subrange_list_dec_def,
      sail2_valuesTheory.subrange_list_inc_def
      ]] >>
  LET_ELIM_TAC >>
  `hi' = &hi` by (unabbrev_all_tac >> ARITH_TAC) >> pop_assum SUBST_ALL_TAC >>
  `¬(&hi + 1i < 0)` by (unabbrev_all_tac >> ARITH_TAC) >> gvs[] >>
  gvs[INT_ADD_CALCULATE] >>
  `LENGTH bs' = LENGTH bs` by (
    unabbrev_all_tac >> every_case_tac >> gvs[v2n_0, combinTheory.o_DEF] >>
    qmatch_goalsub_abbrev_tac `add neg` >>
    `EXISTS $¬ neg` by (unabbrev_all_tac >> gvs[EXISTS_MEM, MEM_MAP]) >>
    simp[LENGTH_add_MAX] >>
    `MAX (LENGTH neg) 1 = LENGTH neg` by (unabbrev_all_tac >> simp[MAX_DEF]) >>
    pop_assum SUBST_ALL_TAC >> simp[MAX_DEF, LENGTH_n2v] >>
    reverse IF_CASES_TAC >> gvs[] >- (unabbrev_all_tac >> simp[]) >>
    Cases_on `v2n neg = 0` >- (unabbrev_all_tac >> gvs[]) >>
    irule FALSITY >> qpat_x_assum `_ < _` mp_tac >> simp[NOT_LESS, LE_LT1, ADD1] >>
    irule LOG_LT >> simp[] >>
    qspec_then `neg` assume_tac v2n_lt >>
    qsuff_tac `v2n neg ≠ 2 ** LENGTH neg - 1` >> rw[] >> gvs[] >>
    simp[GSYM v2n_EVERY_T, combinTheory.o_DEF] >> gvs[EXISTS_MEM]) >>
  gvs[] >>
  `top = &hi` by (unabbrev_all_tac >> every_case_tac >> gvs[] >> ARITH_TAC) >>
  gvs[] >>
  unabbrev_all_tac >> gvs[INT_ADD_CALCULATE, INT_SUB_CALCULATE, v2n_fixwidth] >>
  IF_CASES_TAC >> gvs[]
  >- (
    simp[fixwidth_REPLICATE] >>
    map_every (once_rewrite_tac o single) [
      GSYM SNOC_APPEND, rich_listTheory.SNOC_REPLICATE, Once ADD1] >>
    simp[TAKE_REPLICATE, MIN_ALT_DEF] >>
    srw_tac[fcpLib.FCP_ss][v2w_def] >>
    simp[testbit_el, rich_listTheory.EL_REPLICATE, word_0]
    ) >>
  IF_CASES_TAC >> gvs[]
  >- (
    simp[TAKE_REPLICATE, MIN_ALT_DEF] >>
    srw_tac[fcpLib.FCP_ss][v2w_def] >>
    simp[testbit_el, rich_listTheory.EL_REPLICATE, word_0]
    ) >>
  qmatch_goalsub_abbrev_tac `TAKE len foo` >>
  `0 < len` by (unabbrev_all_tac >> gvs[]) >>
  `TAKE len foo = shiftr foo lo` by (unabbrev_all_tac >> simp[shiftr_def]) >>
  pop_assum SUBST_ALL_TAC >>
  `shiftr foo lo = field hi lo foo` by (unabbrev_all_tac >> simp[field_def]) >>
  pop_assum $ SUBST_ALL_TAC >> simp[]
QED

Theorem OPTION_MAP_just_list:
  ∀l.  EVERY IS_SOME l ⇒ just_list l = SOME (MAP THE l)
Proof
  Induct >> rw[] >>
  simp[Once sail2_valuesTheory.just_list_def] >> TOP_CASE_TAC >> gvs[]
QED


(********************* Monad lemmas *******************)

Theorem bindS = sail2_state_monadTheory.bindS_def;

Theorem seqS =
  sail2_state_monadTheory.seqS_def |> SIMP_RULE std_ss [bindS, FUN_EQ_THM];

Theorem failS = sail2_state_monadTheory.failS_def;

Theorem returnS = sail2_state_monadTheory.returnS_def;

Theorem bindS_returnS[simp]:
  bindS (returnS a) f = f a
Proof
  rw[FUN_EQ_THM, bindS, returnS]
QED

Theorem seqS_returnS[simp]:
  seqS (returnS a) f = f
Proof
  rw[FUN_EQ_THM, bindS, seqS, returnS]
QED

Theorem returnS_bindS:
  ∀f a x s.
  x s = returnS a s ⇒
  bindS x f s = f a s
Proof
  rw[bindS, returnS]
QED

Theorem returnS_bindS_unit = returnS_bindS |> INST_TYPE [gamma |-> ``:unit``]

Theorem seqS_bindS_assoc[simp]:
  ∀x f g. seqS (bindS x (λx. f x)) g = bindS x (λx. seqS (f x) g)
Proof
  rw[FUN_EQ_THM, seqS, bindS] >>
  CASE_TAC >> gvs[] >> CASE_TAC >> gvs[]
QED

Theorem bindS_bindS_assoc[simp]:
  ∀x f g. bindS (bindS x (λx. f x)) g = bindS x (λx. bindS (f x) g)
Proof
  rw[FUN_EQ_THM, bindS] >>
  CASE_TAC >> gvs[] >> CASE_TAC >> gvs[]
QED

Theorem bindS_seqS_assoc[simp]:
  ∀x f g.  bindS (seqS x f) g = seqS x (bindS f g)
Proof
  rw[FUN_EQ_THM, bindS, seqS] >>
  CASE_TAC >> gvs[] >> CASE_TAC >> gvs[]
QED

Theorem bindS_seqS_assoc'[simp]:
  ∀f g h.
    (λx. bindS (seqS (f x) (g x)) h) = (λx. seqS (f x) (bindS (g x) h))
Proof
  rw[FUN_EQ_THM, bindS, seqS] >>
  CASE_TAC >> gvs[] >> CASE_TAC >> gvs[]
QED

Theorem seqS_seqS_assoc[simp]:
  ∀f g h.
    seqS (seqS f g) h = seqS f (seqS g h)
Proof
  rw[FUN_EQ_THM, seqS] >> every_case_tac >> gvs[]
QED

Theorem maybe_failS_SOME[simp]:
  maybe_failS msg (SOME v) = returnS v
Proof
  simp[sail2_state_monadTheory.maybe_failS_def]
QED

Theorem try_catchS_returnS[simp]:
  try_catchS (returnS v) h = returnS v
Proof
  rw[FUN_EQ_THM, sail2_state_monadTheory.try_catchS_def, returnS]
QED

Theorem liftRS_returnS[simp]:
  liftRS (returnS v) = returnS v
Proof
  simp[sail2_state_monadTheory.liftRS_def]
QED


(********************* Other lemmas *******************)

Theorem SetTheFlags_F[simp]:
  ∀rest s. SetTheFlags (F, rest) s = s
Proof
  PairCases >> rw[SetTheFlags_def]
QED

Theorem ByteList_w2v_byte[simp]:
  ByteList (w2v (w : word8)) = [w2v w]
Proof
  qspec_then `w` mp_tac length_w2v >>
  rewrite_tac[dimindex_8, LENGTH_EQ_NUM_compute] >> strip_tac >>
  last_x_assum mp_tac >> rw[LENGTH_EQ_NUM_compute] >>
  simp[ByteList_def]
QED

Theorem ByteList_APPEND_bytes:
  ∀l1 l2. LENGTH l1 = 8 ⇒ ByteList (l1 ++ l2) = l1::ByteList l2
Proof
  rw[LENGTH_EQ_NUM_compute] >> simp[Once ByteList_def]
QED

Theorem asl_extract_flags[simp]:
  (3 >< 3) (v2w [n;z;c;v] : word4) = v2w [n] : word1 ∧
  (2 >< 2) (v2w [n;z;c;v] : word4) = v2w [z] : word1 ∧
  (1 >< 1) (v2w [n;z;c;v] : word4) = v2w [c] : word1 ∧
  (0 >< 0) (v2w [n;z;c;v] : word4) = v2w [v] : word1
Proof
  EVAL_TAC
QED

(* Ported from CakeML *)
Theorem DecodeBitMasks_SOME:
  ∀r s. ∃wmask :word64 tmask.
    DecodeBitMasks (1w, s, r, F) = SOME (wmask, tmask)
Proof
  simp[DecodeBitMasks_def, HighestSetBit_def] >>
  blastLib.FULL_BBLAST_TAC >> rw[] >>
  Cases_on_word_value `s` >> EVAL_TAC
QED

(* Ported from CakeML *)
Theorem Decode_T_EncodeBitMask:
  ∀w :word64 n s r.
    EncodeBitMask w = SOME (n, s, r)
  ⇒ ∃v. DecodeBitMasks (n, s, r, T) = SOME (w, v)
Proof
  lrw[EncodeBitMask_def, EncodeBitMaskAux_def] >>
  rpt (full_case_tac >> gvs[])
QED

Theorem l3_asl_DecodeBitMasks:
  ∀n s r b res : (word64 # word64).
    DecodeBitMasks (n,s,r,b) = SOME res
  ⇒ DecodeBitMasks 64 n s r b = returnS res
Proof
  cheat (* TODO *)
QED

Theorem HasArchVersion_T[simp]:
  ∀version. HasArchVersion version = T
Proof
  simp [
    armv86aTheory.CFG_ID_AA64PFR0_EL1_EL0_def,
    armv86aTheory.CFG_ID_AA64PFR0_EL1_EL1_def,
    armv86aTheory.CFG_ID_AA64PFR0_EL1_EL2_def,
    armv86aTheory.CFG_ID_AA64PFR0_EL1_EL3_def,
    armv86aTheory.CFG_ID_AA64PFR0_EL1_MPAM_def,
    armv86aTheory.CFG_ID_AA64PFR1_EL1_MPAM_frac_def,
    armv86aTheory.HasArchVersion_def,
    armv86aTheory.v81_implemented_def,
    armv86aTheory.v82_implemented_def,
    armv86aTheory.v83_implemented_def,
    armv86aTheory.v84_implemented_def,
    armv86aTheory.v85_implemented_def,
    armv86aTheory.v86_implemented_def
  ] >>
  Cases >> simp[]
QED

Theorem byte_chunks_NONE:
  ∀l. LENGTH l MOD 8 ≠ 0 ⇔ byte_chunks l = NONE
Proof
  gen_tac >> completeInduct_on `LENGTH l` >> rw[] >> gvs[PULL_FORALL] >>
  Cases_on `l` >> rw[] >- simp[sail2_valuesTheory.byte_chunks_def] >>
  Cases_on `t` >> rw[] >- simp[sail2_valuesTheory.byte_chunks_def] >>
  Cases_on `t'` >> rw[] >- simp[sail2_valuesTheory.byte_chunks_def] >>
  Cases_on `t` >> rw[] >- simp[sail2_valuesTheory.byte_chunks_def] >>
  Cases_on `t'` >> rw[] >- simp[sail2_valuesTheory.byte_chunks_def] >>
  Cases_on `t` >> rw[] >- simp[sail2_valuesTheory.byte_chunks_def] >>
  Cases_on `t'` >> rw[] >- simp[sail2_valuesTheory.byte_chunks_def] >>
  Cases_on `t` >> rw[] >- simp[sail2_valuesTheory.byte_chunks_def] >>
  simp[Once sail2_valuesTheory.byte_chunks_def] >> gvs[ADD1]
QED

Theorem byte_chunks_MAP:
  ∀f l. byte_chunks (MAP f l) = OPTION_MAP (MAP (MAP f)) (byte_chunks l)
Proof
  rw[] >> Cases_on `LENGTH l MOD 8 ≠ 0` >> gvs[]
  >- (`LENGTH (MAP f l) MOD 8 ≠ 0` by gvs[] >> gvs[byte_chunks_NONE]) >>
  gvs[MOD_EQ_0_DIVISOR] >>
  pop_assum mp_tac >> map_every qid_spec_tac [`l`,`d`] >>
  Induct >> rw[] >- simp[sail2_valuesTheory.byte_chunks_def] >>
  gvs[ADD1, LEFT_ADD_DISTRIB] >>
  pop_assum mp_tac >> once_rewrite_tac[ADD_COMM] >> rw[LENGTH_EQ_NUM_compute] >>
  simp[] >>
  once_rewrite_tac[sail2_valuesTheory.byte_chunks_def] >> simp[] >>
  Cases_on `byte_chunks l2` >> gvs[]
QED

Theorem byte_chunks_ByteList:
  ∀n l.  LENGTH l = n * 8 ⇒ byte_chunks l = SOME $ ByteList l
Proof
  Induct >> rw[]
  >- simp[Once sail2_valuesTheory.byte_chunks_def, Once ByteList_def] >>
  gvs[ADD1, LEFT_ADD_DISTRIB] >>
  pop_assum mp_tac >> once_rewrite_tac[ADD_COMM] >> rw[LENGTH_EQ_NUM_compute] >>
  simp[Once sail2_valuesTheory.byte_chunks_def] >>
  simp[SimpRHS, Once ByteList_def]
QED

Theorem LENGTH_ByteList:
  ∀l. LENGTH (ByteList l) =
    if LENGTH l MOD 8 = 0 then LENGTH l DIV 8 else LENGTH l DIV 8 + 1
Proof
  gen_tac >> completeInduct_on `LENGTH l` >> rw[] >> gvs[PULL_FORALL] >>
  simp[Once ByteList_def] >> every_case_tac >> gvs[ADD1] >>
  DEP_REWRITE_TAC[ADD_DIV_RWT] >> simp[]
QED

Theorem w2v_reverse_endianness0_64:
  w2v (reverse_endianness0 (w : word64)) = BigEndianReverse (w2v w)
Proof
  rw[reverse_endianness0_def, BigEndianReverse_def] >>
  simp[
    sail2_operators_mwordsTheory.subrange_vec_dec_def,
    sail2_operators_mwordsTheory.concat_vec_def
    ] >>
  qspec_then `w` assume_tac length_w2v >> gvs[SimpRHS] >>
  gvs[LENGTH_EQ_NUM_compute] >> simp[ByteList_def] >>
  pop_assum mp_tac >> EVAL_TAC >> blastLib.BBLAST_TAC
QED

Theorem extract_bits_reverse_endianness0_64:
  ∀v:word64.
    (7  >< 0)  (reverse_endianness0 v) = (63 >< 56) v ∧
    (15 >< 8)  (reverse_endianness0 v) = (55 >< 48) v ∧
    (23 >< 16) (reverse_endianness0 v) = (47 >< 40) v ∧
    (31 >< 24) (reverse_endianness0 v) = (39 >< 32) v ∧
    (39 >< 32) (reverse_endianness0 v) = (31 >< 24) v ∧
    (47 >< 40) (reverse_endianness0 v) = (23 >< 16) v ∧
    (55 >< 48) (reverse_endianness0 v) = (15 >< 8) v ∧
    (63 >< 56) (reverse_endianness0 v) = (7  >< 0) v
Proof
  rw[] >> simp[reverse_endianness0_def] >>
  simp[
    sail2_operators_mwordsTheory.subrange_vec_dec_def,
    sail2_operators_mwordsTheory.concat_vec_def
    ] >>
  blastLib.BBLAST_TAC
QED

Theorem list_combine:
  ∀l1 l2.
    list_combine l1 l2 =
      if LENGTH l1 < LENGTH l2 then ZIP (l1, TAKE (LENGTH l1) l2)
      else if LENGTH l2 < LENGTH l1 then ZIP (TAKE (LENGTH l2) l1, l2)
      else ZIP (l1,l2)
Proof
  Induct >> rw[lem_listTheory.list_combine_def] >> CASE_TAC >> gvs[]
QED

(****************************************)

val _ = export_theory ();
