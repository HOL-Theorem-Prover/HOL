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

val count_num2_inj_rwt = store_thm(
"count_num2_inj_rwt",
``(count_num2 x = count_num2 y) = (x = y)``,
ASSUME_TAC INJ_count_num2 >>
fs[INJ_DEF,EQ_IMP_THM])
val _ = export_rewrites["count_num2_inj_rwt"]

val _ = export_theory ()
