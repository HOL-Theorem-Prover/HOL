structure dividesScript =
struct

open HolKernel Parse boolLib bossLib numLib
     arithmeticTheory factorialTheory;

val ARW = RW_TAC arith_ss;

val _ = new_theory "divides";

val DIVIDES = Define `divides a b = ?q. b = q*a`;

val ALL_DIVIDES_0 = store_thm("ALL_DIVIDES_0",
                        Term `!a. divides a 0`,
                        PROVE_TAC[DIVIDES,MULT_CLAUSES]);

val DIVIDES_REF = store_thm("DIVIDES_REF",
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

(* Changed for Taupo 1 vs. Athabasca 2
   Original:
val DIVIDES_LE = store_thm("DIVIDES_LE",
                        Term `!a b. 0<b /\ divides a b ==> a <= b`,
                        Cases_on `a` THEN ARW[DIVIDES]
                        THEN Cases_on `q` THEN ARW[MULT_CLAUSES]);
*)

val DIVIDES_LE = store_thm("DIVIDES_LE",
                   Term `!a b. 0<b /\ divides a b ==> a <= b`,
                   Cases_on `a` THEN ARW[DIVIDES]
                    THEN Cases_on `q`
                    THENL [PROVE_TAC [MULT_CLAUSES,prim_recTheory.LESS_REFL],
                           ARW[MULT_CLAUSES]]);

val NOT_LT_DIV = store_thm("NOT_LT_DIV",
                        Term `!a b. 0<b /\ b<a ==> ~(divides a b)`,
                         PROVE_TAC[DIVIDES_LE,LESS_EQ_ANTISYM]);

(* Changed for Taupo 1 *)
val DIVIDES_ANTISYM = store_thm("DIVIDES_ANTISYM",
                        Term `!a b. divides a b /\ divides b a ==> (a = b)`,
                        REPEAT Cases
                          THEN TRY (ARW[DIVIDES] THEN NO_TAC)
                          THEN PROVE_TAC [LESS_EQUAL_ANTISYM,
                                    DIVIDES_LE,prim_recTheory.LESS_0]);

val DIVIDES_MULT = store_thm("DIVIDES_MULT",
                              Term `!a b c. divides a b ==> divides a (b*c)`,
                              PROVE_TAC[DIVIDES,MULT_SYM,MULT_ASSOC]);

val DIVIDES_FACT = store_thm("DIVIDES_FACT",
                              Term `!b. 0<b ==> divides b (fact b)`,
                              Cases_on `b` THEN ARW[fact_def] THEN
                              PROVE_TAC [DIVIDES, MULT_COMM]);


val _ = export_theory();

end;


