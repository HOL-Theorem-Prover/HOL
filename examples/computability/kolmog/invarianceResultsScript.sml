open HolKernel Parse boolLib bossLib;
open kolmogorov_complexityTheory pred_setTheory

val _ = new_theory "invarianceResults";





(* Invariance theorem *)


Theorem invariance_theorem:
  ∀U T. univ_rf U ==> ∃C. ∀x. (core_complexity U x) <= 
                              (core_complexity (λy. on2bl (recPhi [T;bl2n y])) x) + (C U T)
Proof
  rw[univ_rf_def,core_complexity_def] >>  fs[univ_rf_def] >>
  `∃g. ∀x. on2bl (Phi T' x) = U (g++ (n2bl x))` by fs[] >>
  qexists_tac`λx y. SOME (LENGTH g)` >> rw[]
  >- (`univ_rf U` by fs[univ_rf_def] >>`{p| U p = SOME x} <> {}` by fs[univ_rf_nonempty] >> fs[])
  >- (`MIN_SET (IMAGE LENGTH {p | U p = SOME x}) ∈
        IMAGE LENGTH ({p | U p = SOME x})` by fs[MIN_SET_LEM] >> fs[IMAGE_DEF] >>
      qabbrev_tac`U_x = x'` >>
      `MIN_SET (IMAGE LENGTH {y | U (g ++ y) = SOME x}) ∈
        IMAGE LENGTH ({y | U (g ++ y) = SOME x})` by fs[MIN_SET_LEM] >> fs[IMAGE_DEF] >>
      qabbrev_tac`T_x = x''` >>
      `{LENGTH y | U (g ++ y) = SOME x} <> {}` by (fs[EXTENSION] >> qexists_tac`T_x`>>fs[])>>
      qabbrev_tac`a=LENGTH g` >>
      `a + MIN_SET {b | b ∈  {LENGTH y | U (g ++ y) = SOME x}} =
        MIN_SET {a + b | b ∈  {LENGTH y | U (g ++ y) = SOME x}}` by fs[MIN_SET_ladd] >>
      fs[] >>
      `{LENGTH p | U p = SOME x} <> {}` by (`IMAGE LENGTH { p | U p = SOME x} ≠ ∅` by
        fs[IMAGE_EQ_EMPTY] >>
        `{LENGTH p | p ∈ {q | U q= SOME x}} ≠ ∅` by metis_tac[IMAGE_DEF] >> fs[]) >>
      `MIN_SET {LENGTH p | U p = SOME x} ∈ {LENGTH p | U p = SOME x} ∧
        ∀q. q ∈ {LENGTH p | U p = SOME x} ⇒ MIN_SET {LENGTH p | U p = SOME x} ≤ q` by
        fs[MIN_SET_LEM] >>
      `MIN_SET {LENGTH x' | U x' = SOME x} ≤
       MIN_SET {a + b | (∃y. b = LENGTH y ∧ U (g ++ y) = SOME x)}` suffices_by fs[]>>
      irule SUBSET_MIN_SET >> rw[]
      >- (fs[EXTENSION] >> qexists_tac`T_x`>>fs[])
      >- (rw[SUBSET_DEF] >>qexists_tac`g++y`>>fs[Abbr`a`] )  )
QED


(* Cleaned up invariance theorem *)

Definition indexes_of_def:
  indexes_of V = {k | V = (λy. on2bl (recPhi [k;bl2n y]))}
End

Theorem clean_invariance_theorem:
  ∀U V. univ_rf U ∧ (i ∈ indexes_of V ) ==> ∃C. ∀x. (core_complexity U x) <= (core_complexity V x) + (C U i)
Proof
  rw[indexes_of_def] >> qspecl_then [`U`,`i`] mp_tac invariance_theorem >> rw[]
QED



val _ = export_theory();

