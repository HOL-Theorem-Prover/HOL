structure fermatScript =
struct

(* For interactive use:

 app load ["bossLib", "Q", "numLib",
     "gcdTheory", "primeTheory", "dividesTheory", "factorialTheory",
     "binomialTheory", "congruentTheory", "summationTheory", "powerTheory"] ;
*)

open HolKernel Parse boolLib bossLib
     numLib arithmeticTheory prim_recTheory
     gcdTheory primeTheory dividesTheory factorialTheory
     binomialTheory congruentTheory summationTheory powerTheory ;

val ARW = RW_TAC arith_ss;

val _ = new_theory "fermat";

val DIV_FACT = store_thm("DIV_FACT",
			Term `!p n. prime p /\ 0 <n /\ divides p (fact n)
                                ==> ?k. 0<k /\ k <= n /\ divides p k`,
                        Induct_on `n` THEN ARW[fact_def]
                        THEN Cases_on `divides p (SUC n)` THENL[
                          EXISTS_TAC (Term `SUC n`) THEN ARW[],
                          IMP_RES_TAC P_EUCLIDES THEN TRY (PROVE_TAC[])
                            THEN `0 < n` by ALL_TAC
                            THENL [
                              Cases_on `n=0` THEN ARW[]
                                THEN `~(divides p (fact 0))` by REWRITE_TAC[fact_def, ONE]
                                THEN PROVE_TAC[],
                              RES_TAC THEN EXISTS_TAC (Term `k:num`) THEN ARW[]
                            ]
                        ]
                        );

val DIV_FACT_LESS = store_thm("DIV_FACT_LESS",
                              Term `!p n. prime p /\ divides p (fact n) ==> p <= n`,
                              Cases_on `n` THENL[
                                ARW[fact_def]
                                  THEN `p <= 1` by ARW[DIVIDES_LE]
                                  THEN Cases_on `p=1`
                                  THEN ARW[NOT_PRIME_1] THEN PROVE_TAC[NOT_PRIME_1],
                                ARW[] THEN `0 < SUC n'` by ARW[]
                                  THEN PROVE_TAC[DIV_FACT,DIVIDES_LE,LESS_EQ_TRANS]
                              ]
                              );


val P_DIV_BINOMIAL = store_thm("P_DIV_BINOMIAL",
			Term `!p n. prime p /\ 0<n /\ n<p ==>  divides p (binomial p n)`,
                        ARW[]
                        THEN `0<p` by (Cases_on `p=0` THEN ARW[] THEN PROVE_TAC[NOT_PRIME_0])
                        THEN `divides p ((binomial ((p-n)+n) n) * (fact (p-n) * fact n))` by ARW[BINOMIAL_FACT,DIVIDES_FACT]
                        THEN  Cases_on `divides p (fact (p-n) * fact n)`
                        THENL [
                          Cases_on `divides p (fact n)` THENL [
                            `p <= n` by PROVE_TAC[DIV_FACT_LESS] THEN PROVE_TAC[NOT_LESS],
                            Cases_on `divides p (fact (p-n))` THENL [
                              `p <= p-n` by PROVE_TAC[DIV_FACT_LESS]
                                 THEN PROVE_TAC[SUB_LESS_EQ,NOT_LESS_EQ,SUB_EQ_EQ_0,LESS_EQUAL_ANTISYM]
                               ,
                               IMP_RES_TAC P_EUCLIDES THEN PROVE_TAC[]
                            ]
                          ]
                          ,
                          IMP_RES_TAC P_EUCLIDES THEN TRY (PROVE_TAC[])
                            THEN (POP_ASSUM MP_TAC) THEN ARW[SUB_ADD]
                        ]
                      );

val FERMAT_1 = store_thm(
  "FERMAT_1",
  Term `!p k. prime p
               ==>
              congruent (power (k+1) p)
                        (power k p + 1) p`,
  Cases_on `p` THEN REWRITE_TAC[NOT_PRIME_0]
  THEN Cases_on `n`
  THEN REWRITE_TAC[NOT_PRIME_1, SYM ONE]
  THEN ARW[EXP_PASCAL]
  THEN ONCE_REWRITE_TAC[SUMMATION_1]
  THEN ARW[SUMMATION_2,BINOMIAL_DEF1,MULT_CLAUSES,POWER_1,ADD_CLAUSES]
  THEN ARW[BINOMIAL_DEF3,power_def]
  THEN MATCH_MP_TAC CONGRUENT_ADD THEN ARW[CONGRUENT_REF]
  THEN `1=0+1` by ARW[]
  THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC[th])
  THEN MATCH_MP_TAC CONGRUENT_ADD
  THEN ARW[CONGRUENT_REF]
  THEN MATCH_MP_TAC (SIMP_RULE std_ss [] (Q.SPECL
       [`n'`, `SUC 0`,
        `\k'. binomial (SUC(SUC n')) k'
               * power k (SUC(SUC n') - k')`,
        `\a. congruent a 0 (SUC (SUC n'))`] INV_SUMMATION))
  THEN ARW[ADD_CLAUSES] THENL [
    PROVE_TAC[CONGRUENT_ADD,ADD_CLAUSES],
   `divides (SUC (SUC n')) (binomial (SUC(SUC n')) (k' + 1))`
     by ARW[P_DIV_BINOMIAL]
    THEN PROVE_TAC[CONGRUENT_MULT_0,DIVIDES_CONGRUENT,ADD1]
  ]);


val FERMAT_2 = store_thm("FERMAT_2",
                             Term `!k p. prime p ==> congruent (power k p) k p`,
                             Induct_on `k` THEN Cases_on `p` THEN ARW[POWER_0,NOT_PRIME_0,CONGRUENT_REF]
                             THEN `congruent (power (k+1) (SUC n)) ((power k (SUC n))+1) (SUC n)` by PROVE_TAC[FERMAT_1]
                             THEN `SUC k = k+1` by ARW[]
                             THEN `congruent ((power k (SUC n))+1) (k+1) (SUC n)` by PROVE_TAC[CONGRUENT_REF,CONGRUENT_ADD]
                             THEN PROVE_TAC[CONGRUENT_REF,CONGRUENT_ADD,CONGRUENT_TRANS]);


val FERMAT = store_thm("FERMAT",
                        Term `!k p. prime p ==> congruent (power k (p-1)) 1 p \/ divides p k`,
                        Cases_on `k` THEN Cases_on `p` THEN ARW[power_def,CONGRUENT_REF,ALL_DIVIDES_0]
                        THEN Cases_on `divides (SUC n') (SUC n)` THEN ARW[]
                        THEN `SUC n <= power (SUC n) (SUC n')` by ARW[POWER_LE]
                        THEN `divides (SUC n) ((power (SUC n) (SUC n')) - (SUC n))`
                           by ARW[DIVIDES_SUB,DIVIDES_REF,power_def,DIVIDES_MULT,MULT_SYM]
                        THEN POP_ASSUM MP_TAC THEN ARW[divides_def]
                        THEN `divides (SUC n') (q * SUC n)` by PROVE_TAC[CONGRUENT_DIVIDES,FERMAT_2]
                        THEN `gcd (SUC n) (SUC n') = 1` by PROVE_TAC[PRIME_GCD,GCD_SYM]
                        THEN `divides (SUC n') q` by PROVE_TAC[L_EUCLIDES,MULT_SYM]
                        THEN POP_ASSUM MP_TAC THEN ARW[divides_def,congruent_def]
                        THEN EXISTS_TAC (Term `0`) THEN EXISTS_TAC (Term `q':num`) THEN ARW[MULT_CLAUSES]
                        THEN `((power (SUC n) n' -1)*(SUC n)) = (q' * SUC n') * (SUC n)`
                           by (REWRITE_TAC[RIGHT_SUB_DISTRIB] THEN PROVE_TAC[power_def,MULT_SYM,MULT_LEFT_1])
                        THEN `(power (SUC n) n' -1) = q' + q'* n'` by PROVE_TAC[ MULT_SUC_EQ,MULT_SYM,MULT_CLAUSES]
                        THEN `1 <= power (SUC n) n'` by PROVE_TAC[POWER_LE_1]
                        THEN ARW[SUB_ADD]
                        );

val _ = export_theory();

end;
