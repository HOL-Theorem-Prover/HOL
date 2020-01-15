open HolKernel Parse boolLib bossLib;
open kolmog_incomputableTheory;

val _ = new_theory "kolmog_prior";

(*

val _ = overload_on ("UKC",``(λx. THE (kolmog_complexity (x:num) (U:bool list -> num option ) ))``)

Theorem univ_prior_pos:
  0 < 2 rpow (-&(UKC x))
Proof
  `0r < 2` by fs[] >> fs[transcTheory.RPOW_POS_LT]
QED

*)

val _ = export_theory();

