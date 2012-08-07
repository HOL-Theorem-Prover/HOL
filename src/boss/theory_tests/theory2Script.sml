open HolKernel Parse boolLib bossLib

open theory1Theory

val _ = Feedback.WARNINGs_as_ERRs := true

val _ = new_theory "theory2"

val thm1 = save_thm("thm1", EVAL ``f 64``)
val thm2 = save_thm("thm2", SIMP_CONV (srw_ss()) [] ``f 32``)

val _ = export_theory()
