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

(*

Theorem univ_rf_recfn:
  univ_rf U ==> ∃i.  ∀x. (λy. on2bl (Phi i (bl2n y))) = U
Proof
  rw[FUN_EQ_THM,univ_rf_def]
QED

Theorem clean_univ_invariance_theorem:
  ∀U V. univ_rf U ∧ univ_rf V ==> ∃C. ∀x. (KC U x) <= (KC V x) + (C U V)
Proof
  rw[KC_def,univ_rf_def,core_complexity_def] >>  fs[univ_rf_def] >>
  ‘∀x. {p | V p = SOME x} ≠ ∅’ by (rw[] >> `univ_rf V` by fs[univ_rf_def] >>
    `{p| V p = SOME x} <> {}` by fs[univ_rf_nonempty] >> fs[]) >>
  ‘∀x. {p | U p = SOME x} ≠ ∅’ by (rw[] >> `univ_rf U` by fs[univ_rf_def] >>
    `{p| U p = SOME x} <> {}` by fs[univ_rf_nonempty] >> fs[]) >> fs[] >>
  CCONTR_TAC >> fs[arithmeticTheory.NOT_LESS_EQUAL] >>
  ‘∀x. Phi print_index x = SOME x’  by metis_tac[print_index_correct] >>
  ‘∃g1. ∀x. on2bl (Phi print_index x) = U (g1 ++ (n2bl x))’ by fs[] >>
  ‘∃g2. ∀x. on2bl (Phi print_index x) = V (g2 ++ (n2bl x))’ by fs[] >>
  ‘∃x. MIN_SET {LENGTH p | V p = SOME x} + 2*(LENGTH g1 + LENGTH g2) <
       MIN_SET {LENGTH p | U p = SOME x}’ by fs[] >>
  ‘Phi print_index (bl2n x) = SOME (bl2n x)’ by fs[] >>
  ‘on2bl (Phi print_index (bl2n x)) = on2bl (SOME (bl2n x))’ by metis_tac[] >>
  ‘U (g1 ++ x) = SOME x’ by (rfs[on2bl_def] >> ‘SOME (n2bl (bl2n x)) = U (g1 ++(n2bl (bl2n x)))’ by fs[] >> fs[]) >>
  ‘V (g2 ++ x) = SOME x’ by (rfs[on2bl_def] >> ‘SOME (n2bl (bl2n x)) = V (g2 ++(n2bl (bl2n x)))’ by fs[] >> fs[]) >>
  ‘univ_rf U ’ by fs[univ_rf_def] >>
  ‘univ_rf V ’ by fs[univ_rf_def] >>

  ‘MIN_SET {LENGTH p | U p = SOME x} <= LENGTH (g1++x)’ by
    (DEEP_INTRO_TAC MIN_SET_ELIM >>
     rw[EXTENSION, SIMP_RULE (srw_ss()) [EXTENSION] univ_rf_nonempty] >>
     ‘(∃p. LENGTH g1 + LENGTH x = LENGTH p ∧ U p = SOME x)’ by (qexists_tac‘(g1++x)’ >>rw[]) >>
     metis_tac[] ) >>
  ‘MIN_SET {LENGTH p | V p = SOME x} + 2*(LENGTH g1 + LENGTH g2) < LENGTH (g1++x)’ by
    (fs[arithmeticTheory.LESS_TRANS]) >>
  ‘MIN_SET {LENGTH p | V p = SOME x}  <= LENGTH (g2++x)’ by
    (DEEP_INTRO_TAC MIN_SET_ELIM >>
     rw[EXTENSION, SIMP_RULE (srw_ss()) [EXTENSION] univ_rf_nonempty] >>
     ‘(∃p. LENGTH g2 + LENGTH x = LENGTH p ∧ V p = SOME x)’ by (qexists_tac‘(g2++x)’ >>rw[]) >>
     metis_tac[]) >>
   rename[‘p1 + 2*(LENGTH g1 + LENGTH g2) < p2’,‘p1 + 2*(LENGTH g1 + LENGTH g2) < LENGTH (g1++x)’] >>
  ‘p1 + 2*(LENGTH g1 + LENGTH g2) + p1 < LENGTH (g1 ++x) + LENGTH (g2 ++ x)’ by fs[] >> fs[]
  ‘(LENGTH g1 + LENGTH g2) <= LENGTH (g1++x) - LENGTH (g2++x)’ by
    (‘p1 + (LENGTH g1 + LENGTH g2) <= LENGTH (g1++x)’ by fs[] >>
     ‘(p1 + (LENGTH g1 + LENGTH g2)) - p1 <= LENGTH (g1++x) - LENGTH (g2 ++ x)’ by )
 
QED
*)

val _ = export_theory();

