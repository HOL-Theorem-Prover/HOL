Theory theory2
Ancestors
  theory1

val _ = Feedback.WARNINGs_as_ERRs := true

val thm1 = save_thm("thm1", EVAL ``f 64``)
val thm2 = save_thm("thm2", SIMP_CONV (srw_ss()) [] ``f 32``)

