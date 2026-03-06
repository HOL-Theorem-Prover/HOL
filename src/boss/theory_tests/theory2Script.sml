Theory theory2
Ancestors
  theory1

val _ = Feedback.WARNINGs_as_ERRs := true

Theorem thm1 = EVAL ``f 64``
Theorem thm2 = SIMP_CONV (srw_ss()) [] ``f 32``

