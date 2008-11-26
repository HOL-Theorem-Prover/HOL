open HolKernel Parse boolLib numLib quotient BasicProvers

val _ = temp_remove_termtok {term_name = "<=>", tok = "<=>"}
val _ = hide "<=>"
val eq_def = new_definition("eq_def", ``<=> n m = (n MOD 3 = m MOD 3)``);

val eq_equiv = prove(``!n m. <=> n m = (<=> n = <=> m)``,
                     SRW_TAC [][EQ_IMP_THM, FUN_EQ_THM, eq_def])

val _ = define_quotient_type "mod3" "abs_mod3" "rep_mod3" eq_equiv



