structure binomialScript =
struct

open HolKernel Parse basicHol90Lib bossLib
     arithmeticTheory 
     factorialTheory powerTheory summationTheory ;

infix THEN THENC THENL;
infix 8 by;

val ARW = RW_TAC arith_ss;

val _ = new_theory "binomial";


val BINOMIAL = 
 Define 
     `(binomial a 0  = 1) 
  /\  (binomial 0 (SUC b) = 0)
  /\  (binomial (SUC a) (SUC b) = binomial a (SUC b) + binomial a b)`;


val BINOMIAL_DEF1 = store_thm("BINOMIAL_DEF1",
                        Term `!a. binomial a 0 = 1`,
                        Cases_on `a` THEN REWRITE_TAC[BINOMIAL]);

val BINOMIAL_DEF2 = store_thm("BINOMIAL_DEF2",
			Term `!a b. a < b ==> (binomial a b = 0)`,
                        Induct_on `a` THEN Cases_on `b` 
                        THEN REWRITE_TAC[BINOMIAL] THEN ARW[]);

val BINOMIAL_DEF3 = store_thm("BINOMIAL_DEF3",
			Term `!a. binomial a a = 1`,
                        Induct_on `a` THEN REWRITE_TAC[BINOMIAL]
                        THEN ARW[BINOMIAL_DEF2]);

val BINOMIAL_DEF4 = store_thm("BINOMIAL_DEF4",
			Term `!a b. binomial (SUC a) (SUC b) 
                                       = 
                                    binomial a (SUC b) + binomial a b`,
                        REWRITE_TAC[BINOMIAL]);

val BINOMIAL_FACT = store_thm("BINOMIAL_FACT",
Term `!a b. binomial (a+b) b * (fact a * fact b) 
              = 
            fact (a+b)`,
Induct_on `b`
  THENL [
    REWRITE_TAC[BINOMIAL_DEF1,fact_def,ADD_CLAUSES,MULT_CLAUSES],
    Induct_on `a` 
      THENL [
        REWRITE_TAC[BINOMIAL_DEF3,fact_def,ADD_CLAUSES,MULT_CLAUSES],
        `SUC a + SUC b = SUC (SUC a + b)` by ARW[ADD_CLAUSES]
            THEN ASM_REWRITE_TAC[BINOMIAL_DEF4,RIGHT_ADD_DISTRIB]
             THEN `binomial (SUC a + b) (SUC b) * (fact (SUC a) * fact (SUC b))
                    =
                   (binomial (a + SUC b) (SUC b) * (fact a * fact (SUC b)))
                   * SUC a` 
               by REWRITE_TAC[fact_def,ADD_CLAUSES]
             THENL [
               PROVE_TAC[MULT_ASSOC,MULT_SYM],
               ASM_REWRITE_TAC[] 
                 THEN `binomial (SUC a + b) b * (fact (SUC a) * fact (SUC b))
                         =
                       (binomial (SUC a + b) b * (fact (SUC a) * fact b))
                        * SUC b` 
                   by REWRITE_TAC[fact_def,ADD_CLAUSES]
                 THENL [
                   PROVE_TAC[MULT_ASSOC,MULT_SYM],
                   ASM_REWRITE_TAC
                      [ADD_CLAUSES,SYM(SPEC_ALL LEFT_ADD_DISTRIB),fact_def]
                 ]
             ]
      ]
  ]
);


val EXP_PASCAL = store_thm("EXP_PASCAL",
Term `!a b n. 
        power (a+b) n 
          = 
        summation n 0 
          (\k. binomial n k * (power a (n-k) * power b k))`,
Induct_on `n` 
 THENL [
  ARW[power_def,summation_def,BINOMIAL_DEF1],
  Cases_on `n`
   THENL [
     ARW [power_def,summation_def,BINOMIAL_DEF1,BINOMIAL_DEF3,MULT_CLAUSES] 
       THEN REWRITE_TAC[power_def,ONE,MULT_CLAUSES,ADD_CLAUSES],
     ONCE_REWRITE_TAC[power_def] 
       THEN ASM_REWRITE_TAC[RIGHT_ADD_DISTRIB,SUMMATION_TIMES]
       THEN REPEAT STRIP_TAC
       THEN `summation (SUC n') 0
               (\n. a * (binomial (SUC n') n * (power a (SUC n' - n) * power b n)))
              =
             a * power a (SUC n') +
             summation n' 1
               (\n. a * (binomial(SUC n') n * (power a (SUC n' - n) * power b n)))`
         by ARW[SUMMATION_1,BINOMIAL_DEF1,power_def,MULT_CLAUSES,ONE]
       THEN `summation (SUC n') 0  
              (\n. b * (binomial(SUC n') n * (power a (SUC n' - n) * power b n)))
               =
             summation n' 0  
               (\n. b * (binomial(SUC n') n * (power a (SUC n' - n) * power b n)))
               + b * power b (SUC n')`
         by ARW [SUMMATION_2,BINOMIAL_DEF1,
                 BINOMIAL_DEF3,power_def,MULT_CLAUSES,ONE]
       THEN BETA_TAC THEN ASM_REWRITE_TAC[]
       THEN REWRITE_TAC[Q.SPECL[`n'`,`0`] SUMMATION_SHIFT] THEN BETA_TAC
       THEN `(a * power a (SUC n') 
             + (summation n' 1 
                 (\n. a * (binomial(SUC n') n * (power a (SUC n' - n) * power b n)))
             + (summation n' (SUC 0)
                 (\n. b * (binomial(SUC n') (n-1) * (power a (SUC n' - (n-1)) * power b (n-1))))
             + b * power b (SUC n'))))
          =
             (a * power a (SUC n') 
             + (summation n' 1 
                 (\n. binomial (SUC (SUC n')) n * (power a (SUC (SUC n') - n) * power b n))
             + b * power b (SUC n')))` by ALL_TAC
       THENL [
        ARW [ONE,SUMMATION_ADD]
          THEN MATCH_MP_TAC SUMMATION_EXT 
          THEN ARW[ADD_CLAUSES,Q.SPEC`SUC n'` BINOMIAL_DEF4,RIGHT_ADD_DISTRIB]
          THEN POP_ASSUM MP_TAC THEN REPEAT (POP_ASSUM (K ALL_TAC)) 
          THEN DISCH_TAC
          THEN `SUC n' - k = SUC (n' - k)` by ARW[]
          THEN ASM_REWRITE_TAC[power_def] 
          THEN MATCH_MP_TAC (DECIDE `(x=q) /\ (y=p) ==> (x + y = p + q)`)
          THEN PROVE_TAC [MULT_SYM,MULT_ASSOC],
         ASM_REWRITE_TAC [GSYM ADD_ASSOC]
          THEN ARW[Q.SPEC`SUC n'` SUMMATION_1, Q.SPEC`n'` SUMMATION_2]
          THEN ARW[power_def,BINOMIAL_DEF1,MULT_CLAUSES,ADD_CLAUSES]
          THEN ARW[power_def,BINOMIAL_DEF3,MULT_CLAUSES]
          THEN ONCE_REWRITE_TAC[SUMMATION_SHIFT_P] THEN BETA_TAC
          THEN REWRITE_TAC[ONE]
          THEN MATCH_MP_TAC SUMMATION_EXT 
          THEN ARW[ADD_SUB]
       ]
   ]
 ]);

val _ = export_theory();

end;
