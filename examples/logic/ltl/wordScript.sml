Theory word
Ancestors
  pred_set

val _ = Datatype` word = WORD (num -> 'a set)`;

val suff_def = Define `suff (WORD f) n = WORD (\x. f (n+x))`;

val at_def = Define `at (WORD f) n = f n`;

val word_range_def = Define `word_range w = {x | ?i. at w i = x }`;

val AT_SUFF_LEMM = store_thm
  ("AT_SUFF_LEMM",
   ``!w n i. at (suff w n) i = at w (i + n)``,
   rw[] >> Cases_on `w`
   >> fs[at_def, suff_def]
  );

val SUFF_SUFF_LEMM = store_thm
  ("SUFF_SUFF_LEMM",
   ``!w t1 t2. suff (suff w t1) t2 = suff w (t1+t2)``,
  Cases_on `w` >> SIMP_TAC arith_ss [suff_def]);

val SUFF_0_LEMM = store_thm
  ("SUFF_0_LEMM",
   ``!w. suff w 0 = w``,
  Cases_on `w` >> SIMP_TAC arith_ss [suff_def, ETA_THM]);

val WORD_RANGE_SUFF_LEMM = store_thm
  ("WORD_RANGE_SUFF_LEMM",
   ``!w n. word_range (suff w n) ⊆ word_range w``,
   fs[word_range_def, SUBSET_DEF] >> metis_tac[AT_SUFF_LEMM]
  );

val AT_WORD_RANGE = store_thm
  ("AT_WORD_RANGE",
  ``!w i. at w i ∈ word_range w``,
  rw[word_range_def] >> metis_tac[word_range_def]
  );

