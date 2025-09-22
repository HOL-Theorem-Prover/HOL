Theory kolmog_prior
Ancestors
  kolmog_incomputable plain_kolmog_inequalities transc

Theorem univ_prior_pos:
  ∀x. 0 < 2 rpow (-&(KC U x))
Proof
  rw[] >> `0r < 2` by fs[] >> fs[transcTheory.RPOW_POS_LT]
QED



