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

(****************************************)

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

(****************************************)

val _ = export_theory ();
