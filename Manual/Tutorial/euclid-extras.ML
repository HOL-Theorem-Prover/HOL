val DIVIDES_ZERO = store_thm
 ("DIVIDES_ZERO",
  ``!x. 0 divides x <=> (x = 0)``,
  METIS_TAC [divides_def,MULT_CLAUSES]);

val DIVIDES_ONE = store_thm
 ("DIVIDES_ONE",
  ``!x. x divides 1 <=> (x = 1)``,
  METIS_TAC [divides_def,MULT_CLAUSES,MULT_EQ_1]);

val DIVIDES_REFL = store_thm
 ("DIVIDES_REFL",
  ``!x. x divides x``,
  METIS_TAC [divides_def,MULT_CLAUSES]);

val DIVIDES_TRANS = store_thm
 ("DIVIDES_TRANS",
  ``!a b c. a divides b /\ b divides c ==> a divides c``,
  METIS_TAC [divides_def,MULT_ASSOC]);

val DIVIDES_ADD = store_thm
("DIVIDES_ADD",
 ``!d a b. d divides a /\ d divides b ==> d divides (a + b)``,
 METIS_TAC[divides_def,LEFT_ADD_DISTRIB]);

val DIVIDES_SUB = store_thm
 ("DIVIDES_SUB",
  ``!d a b. d divides a /\ d divides b ==> d divides (a - b)``,
  METIS_TAC [divides_def,LEFT_SUB_DISTRIB]);

val DIVIDES_ADDL = store_thm
 ("DIVIDES_ADDL",
  ``!d a b. d divides a /\ d divides (a + b) ==> d divides b``,
  METIS_TAC [ADD_SUB,ADD_SYM,DIVIDES_SUB]);

val DIVIDES_LMUL = store_thm
 ("DIVIDES_LMUL",
  ``!d a x. d divides a ==> d divides (x * a)``,
  METIS_TAC [divides_def,MULT_ASSOC,MULT_SYM]);

val DIVIDES_RMUL = store_thm
 ("DIVIDES_RMUL",
  ``!d a x. d divides a ==> d divides (a * x)``,
  METIS_TAC [MULT_SYM,DIVIDES_LMUL]);
