open HolKernel bossLib boolLib pred_setTheory lcsymtacs

val _ = new_theory "countable"

val count_num2_def = Define`
  count_num2 = @f. INJ f ((UNIV:num set) CROSS (UNIV:num set)) (UNIV:num set)`

val INJ_count_num2 = store_thm(
"INJ_count_num2",
``INJ count_num2 (UNIV CROSS UNIV) UNIV``,
rw[count_num2_def] >>
SELECT_ELIM_TAC >> rw[] >>
metis_tac [cross_countable,num_countable,countable_def])

val _ = export_theory ()
