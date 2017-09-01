open HolKernel Parse bossLib boolLib relationTheory

val _ = new_theory "relationTheoryHelper"

val RTC_TRANSITIVE = store_thm
  ("RTC_TRANSITIVE",
  ``!R a b c. R^* a b ∧ R^* b c ==> R^* a c``,
   metis_tac[RTC_TRANSITIVE,transitive_def]
  );

val _ = export_theory();
