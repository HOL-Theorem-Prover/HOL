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

val count_num_aux_def = Define`
  count_num_aux (n:num) = n`;

val count_num_aux_inj = store_thm(
"count_num_aux_inj",
``INJ count_num_aux UNIV UNIV``,
rw[INJ_DEF,count_num_aux_def])

val count_char_aux_def = Define`
  count_char_aux = ORD`;

val count_char_aux_inj = store_thm(
"count_char_aux_inj",
``INJ count_char_aux UNIV UNIV``,
rw[INJ_DEF,count_char_aux_def,stringTheory.ORD_11]);

open integerTheory arithmeticTheory

val count_int_aux_def = Define`
  count_int_aux i = if 0 ≤ i then 2 * (Num i) else SUC (2 * (Num (-i)))`

val count_int_aux_inj = store_thm(
"count_int_aux_inj",
``INJ count_int_aux UNIV UNIV``,
fs[INJ_DEF,count_int_aux_def] >>
srw_tac[][EQ_MULT_LCANCEL] >>
metis_tac [
INT_LE_NEGTOTAL,
NUM_OF_INT,
NUM_POSINT_EXISTS,
INT_EQ_NEG,
EVEN_ODD,
ODD_DOUBLE,
EVEN_DOUBLE])

val _ = export_theory ()
