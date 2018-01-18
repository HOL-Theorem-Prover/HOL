open HolKernel Parse bossLib boolLib relationTheory

val _ = new_theory "relationTheoryHelper"

val RTC_TRANSITIVE = store_thm
  ("RTC_TRANSITIVE",
  ``!R a b c. R^* a b ∧ R^* b c ==> R^* a c``,
   metis_tac[RTC_TRANSITIVE,transitive_def]
  );

val REFL_THM = store_thm
  ("REFL_THM",
   ``!R. reflexive R = !x y. R x x``,
   fs[reflexive_def]
  );

val TRANS_THM = store_thm
  ("TRANS_THM",
   ``!R. transitive R = !x y z. R x y ∧ R y z ==> R x z``,
   fs[transitive_def]
  );

val SYMM_THM = store_thm
  ("SYMM_THM",
   ``!R. symmetric R = (!x y. R x y =  R y x)``,
    fs[symmetric_def]
  );

val _ = export_theory();
