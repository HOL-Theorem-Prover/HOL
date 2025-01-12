(* interactive mode
app load ["bossLib","gcdTheory","powerTheory","summationTheory",
          "binomialTheory","congruentTheory"];
quietdec := true;
*)

open HolKernel Parse boolLib
open bossLib numLib arithmeticTheory prim_recTheory
     gcdTheory dividesTheory
     binomialTheory congruentTheory summationTheory powerTheory ;

(*
quietdec := false;
*)

val ARW = RW_TAC arith_ss;

val _ = new_theory "fermat";

val FACT_def = ONCE_REWRITE_RULE [MULT_COMM] FACT;

val DIV_FACT = store_thm("DIV_FACT",
                        Term `!p n. prime p /\ 0 <n /\ divides p (FACT n)
                                ==> ?k. 0<k /\ k <= n /\ divides p k`,
                        Induct_on `n` THEN ARW[FACT_def]
                        THEN Cases_on `divides p (SUC n)` THENL[
                          EXISTS_TAC (Term `SUC n`) THEN ARW[],
                          IMP_RES_TAC P_EUCLIDES THEN TRY (PROVE_TAC[])
                            THEN sg `0 < n`
                            THENL [
                              Cases_on `n=0` THEN ARW[]
                                THEN `~(divides p (FACT 0))`
                                 by (REWRITE_TAC[FACT_def, ONE]
                                       THEN PROVE_TAC[]),
                              RES_TAC THEN EXISTS_TAC (Term `k:num`) THEN ARW[]
                            ]
                        ]
                        );

val DIV_FACT_LESS = store_thm("DIV_FACT_LESS",
                              Term `!p n. prime p /\ divides p (FACT n) ==> p <= n`,
                              Cases_on `n` THENL[
                                ARW[FACT_def]
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
                        THEN `divides p ((binomial ((p-n)+n) n) * (FACT (p-n) * FACT n))` by ARW[BINOMIAL_FACT,DIVIDES_FACT]
                        THEN  Cases_on `divides p (FACT (p-n) * FACT n)`
                        THENL [
                          Cases_on `divides p (FACT n)` THENL [
                            `p <= n` by PROVE_TAC[DIV_FACT_LESS] THEN PROVE_TAC[NOT_LESS],
                            Cases_on `divides p (FACT (p-n))` THENL [
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

val FERMAT_1 = store_thm
  ("FERMAT_1",
   Term
   `!p k.
      prime p ==>
      congruent ((k + 1) EXP p) (k EXP p + 1) p`,
   Cases_on `p` THEN REWRITE_TAC[NOT_PRIME_0]
   THEN REWRITE_TAC[NOT_PRIME_1, SYM ONE]
   THEN ARW[EXP_PASCAL, GSYM ADD1]
   THEN ONCE_REWRITE_TAC[SUMMATION_1]
   THEN ONCE_REWRITE_TAC [SUMMATION_2]
   THEN ARW[BINOMIAL_DEF1,MULT_CLAUSES,POWER_1,ADD_CLAUSES]
   THEN ARW[BINOMIAL_DEF3,power_def, ADD1]
   THEN MATCH_MP_TAC CONGRUENT_ADD
   THEN ARW[CONGRUENT_REF]
   THEN `1=0+1` by ARW[]
   THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC[th])
   THEN MATCH_MP_TAC CONGRUENT_ADD
   THEN ARW[CONGRUENT_REF]
   THEN MATCH_MP_TAC
     (BETA_RULE
      (Q.SPECL
       [`n`, `1`,
        `\k'. k EXP (n + 1 - k') * binomial (n + 1) k'`,
        `\a. congruent a 0 (n + 1)`] INV_SUMMATION))
     THEN ARW[ADD_CLAUSES, CONGRUENT_REF] THENL
     [PROVE_TAC[CONGRUENT_ADD,ADD_CLAUSES],
      `divides (SUC n) (binomial (n + 1) (k' + 1))`
      by ARW[GSYM ADD1, P_DIV_BINOMIAL]
      THEN PROVE_TAC[CONGRUENT_MULT_0,DIVIDES_CONGRUENT,ADD1,MULT_COMM]
      ]
     );


val FERMAT_2 = store_thm("FERMAT_2",
                             Term `!k p. prime p ==> congruent ($EXP k p) k p`,
                             Induct_on `k` THEN Cases_on `p` THEN ARW[POWER_0,NOT_PRIME_0,CONGRUENT_REF]
                             THEN `congruent ($EXP (k+1) (SUC n)) (($EXP k (SUC n))+1) (SUC n)` by PROVE_TAC[FERMAT_1]
                             THEN `SUC k = k+1` by ARW[]
                             THEN `congruent (($EXP k (SUC n))+1) (k+1) (SUC n)` by PROVE_TAC[CONGRUENT_REF,CONGRUENT_ADD]
                             THEN PROVE_TAC[CONGRUENT_REF,CONGRUENT_ADD,CONGRUENT_TRANS]);


val FERMAT = store_thm("FERMAT",
                        Term `!k p. prime p ==> congruent ($EXP k (p-1)) 1 p \/ divides p k`,
                        Cases_on `k` THEN Cases_on `p` THEN ARW[power_def,CONGRUENT_REF,ALL_DIVIDES_0]
                        THEN Cases_on `divides (SUC n') (SUC n)` THEN ARW[]
                        THEN `SUC n <= $EXP (SUC n) (SUC n')` by ARW[POWER_LE]
                        THEN `divides (SUC n) (($EXP (SUC n) (SUC n')) - (SUC n))`
                           by ARW[DIVIDES_SUB,DIVIDES_REFL,power_def,DIVIDES_MULT,MULT_SYM]
                        THEN POP_ASSUM MP_TAC THEN ARW[divides_def]
                        THEN `divides (SUC n') (q * SUC n)` by PROVE_TAC[CONGRUENT_DIVIDES,FERMAT_2]
                        THEN `gcd (SUC n) (SUC n') = 1` by PROVE_TAC[PRIME_GCD,GCD_SYM]
                        THEN `divides (SUC n') q` by PROVE_TAC[L_EUCLIDES,MULT_SYM]
                        THEN POP_ASSUM MP_TAC THEN ARW[divides_def,congruent_def]
                        THEN EXISTS_TAC (Term `0`) THEN EXISTS_TAC (Term `q':num`) THEN ARW[MULT_CLAUSES]
                        THEN `(($EXP (SUC n) n' -1)*(SUC n)) = (q' * SUC n') * (SUC n)`
                           by (REWRITE_TAC[RIGHT_SUB_DISTRIB] THEN PROVE_TAC[power_def,MULT_SYM,MULT_LEFT_1])
                        THEN `($EXP (SUC n) n' -1) = q' + q'* n'` by PROVE_TAC[ MULT_SUC_EQ,MULT_SYM,MULT_CLAUSES]
                        THEN `1 <= $EXP (SUC n) n'` by PROVE_TAC[POWER_LE_1]
                        THEN ARW[SUB_ADD]
                        );

val _ = export_theory();
