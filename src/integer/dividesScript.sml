structure dividesScript =
struct

open HolKernel boolLib TotalDefn BasicProvers numLib arithmeticTheory
open SingleStep

infix THEN THENC THENL;
infix 8 by;

val arith_ss = simpLib.++(bool_ss, numSimps.ARITH_ss)
val ARW = RW_TAC arith_ss

val _ = new_theory "divides";

val DIVIDES = Define `divides a b = ?q. b = q*a`;

val ALL_DIVIDES_0 = store_thm("ALL_DIVIDES_0",
                        Term `!a. divides a 0`,
                        PROVE_TAC[DIVIDES,MULT_CLAUSES]);

val DIVIDES_REFL = store_thm("DIVIDES_REFL",
			Term `!a. divides a a`,
                        PROVE_TAC[DIVIDES,MULT_CLAUSES]);

val ONE_DIVIDES_ALL = store_thm("ONE_DIVIDES_ALL",
                        Term `!a. divides 1 a`,
                        PROVE_TAC[DIVIDES,MULT_CLAUSES]);

val DIVIDES_ADD_1 = store_thm("DIVIDES_ADD_1",
                        Term `!a b c. divides a b /\ divides a c ==> divides a (b+c)`,
                        PROVE_TAC[DIVIDES,RIGHT_ADD_DISTRIB]);


val DIVIDES_ADD_2 = store_thm("DIVIDES_ADD_2",
                        Term `!a b c. divides a b /\ divides a (b+c) ==> divides a c`,
                        ARW[DIVIDES] THEN EXISTS_TAC (Term `q' - q`) THEN ARW[RIGHT_SUB_DISTRIB]);

val DIVIDES_SUB = store_thm("DIVIDES_SUB",
                        Term `!a b c. divides a b /\ divides a c ==> divides a (b-c)`,
                        PROVE_TAC[DIVIDES,RIGHT_SUB_DISTRIB]);

val DIVIDES_LE = store_thm("DIVIDES_LE",
  Term `!a b. 0<b /\ divides a b ==> a <= b`,
  Cases_on `a` THEN ARW[DIVIDES] THEN Cases_on `q` THENL [
    PROVE_TAC [MULT_CLAUSES,prim_recTheory.LESS_REFL],
    ARW[MULT_CLAUSES]
  ]);

val NOT_LT_DIV = store_thm("NOT_LT_DIV",
                        Term `!a b. 0<b /\ b<a ==> ~(divides a b)`,
                         PROVE_TAC[DIVIDES_LE,LESS_EQ_ANTISYM]);

val DIVIDES_ANTISYM = store_thm("DIVIDES_ANTISYM",
                        Term `!a b. divides a b /\ divides b a ==> (a = b)`,
                        REPEAT Cases
                          THEN TRY (ARW[DIVIDES] THEN NO_TAC)
                          THEN PROVE_TAC [LESS_EQUAL_ANTISYM,
                                    DIVIDES_LE,prim_recTheory.LESS_0]);

val DIVIDES_TRANS = store_thm(
  "DIVIDES_TRANS",
  ``!p q r. divides p q ==> divides q r ==> divides p r``,
  ARW [DIVIDES] THEN PROVE_TAC [MULT_ASSOC]);

val DIVIDES_MULT = store_thm("DIVIDES_MULT",
                              Term `!a b c. divides a b ==> divides a (b*c)`,
                              PROVE_TAC[DIVIDES,MULT_SYM,MULT_ASSOC]);

val DIVIDES_FACT = store_thm(
  "DIVIDES_FACT",
  Term `!b. 0<b ==> divides b (FACT b)`,
  Cases_on `b` THEN ARW[FACT, DIVIDES] THEN PROVE_TAC [MULT_COMM]);

open simpLib
val DIVIDES_MULT_LEFT = store_thm(
  "DIVIDES_MULT_LEFT",
  ``!n m. divides (n * m) m = (m = 0) \/ (n = 1)``,
  SIMP_TAC arith_ss [FORALL_AND_THM, EQ_IMP_THM, DISJ_IMP_THM,
                     ALL_DIVIDES_0, DIVIDES_REFL] THEN
  SIMP_TAC bool_ss [DIVIDES] THEN REPEAT STRIP_TAC THEN
  `m * 1 = m * (n * q)` by (POP_ASSUM (CONV_TAC o LAND_CONV o
                                       ONCE_REWRITE_CONV o C cons []) THEN
                            ASM_SIMP_TAC bool_ss [MULT_CLAUSES] THEN
                            CONV_TAC (AC_CONV(MULT_ASSOC, MULT_COMM))) THEN
  `(m = 0) \/ (n * q = 1)` by PROVE_TAC [EQ_MULT_LCANCEL] THEN
  ASM_SIMP_TAC bool_ss [] THEN
  PROVE_TAC [MULT_EQ_1]);

val _ = export_theory();

end;


