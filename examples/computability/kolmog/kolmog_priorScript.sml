open HolKernel Parse boolLib bossLib;
open kolmog_incomputableTheory;
open plain_kolmog_inequalitiesTheory;
open transcTheory;

val _ = new_theory "kolmog_prior";




Theorem univ_prior_pos:
  ∀x. 0 < 2 rpow (-&(KC U x))
Proof
  rw[] >> `0r < 2` by fs[] >> fs[transcTheory.RPOW_POS_LT]
QED



val _ = export_theory();

