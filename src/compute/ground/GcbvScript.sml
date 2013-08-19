open HolKernel boolLib bossLib
val _ = new_theory"Gcbv"
val VALUE_def = Define`VALUE = I`
val VALUE_thm = store_thm("VALUE_thm",``∀x. x = VALUE x``,SRW_TAC[][VALUE_def])
val _ = export_theory()
