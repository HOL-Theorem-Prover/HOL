Theory word
Ancestors
  pred_set

Datatype:  word = WORD (num -> 'a set)
End

Definition suff_def:   suff (WORD f) n = WORD (\x. f (n+x))
End

Definition at_def:   at (WORD f) n = f n
End

Definition word_range_def:   word_range w = {x | ?i. at w i = x }
End

Theorem AT_SUFF_LEMM:
     !w n i. at (suff w n) i = at w (i + n)
Proof
   rw[] >> Cases_on `w`
   >> fs[at_def, suff_def]
QED

Theorem SUFF_SUFF_LEMM:
     !w t1 t2. suff (suff w t1) t2 = suff w (t1+t2)
Proof
  Cases_on `w` >> SIMP_TAC arith_ss [suff_def]
QED

Theorem SUFF_0_LEMM:
     !w. suff w 0 = w
Proof
  Cases_on `w` >> SIMP_TAC arith_ss [suff_def, ETA_THM]
QED

Theorem WORD_RANGE_SUFF_LEMM:
     !w n. word_range (suff w n) ⊆ word_range w
Proof
   fs[word_range_def, SUBSET_DEF] >> metis_tac[AT_SUFF_LEMM]
QED

Theorem AT_WORD_RANGE:
    !w i. at w i ∈ word_range w
Proof
  rw[word_range_def] >> metis_tac[word_range_def]
QED

