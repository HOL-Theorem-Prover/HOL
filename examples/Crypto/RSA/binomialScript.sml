(* interactive mode
app load ["bossLib","summationTheory","powerTheory"];
quietdec := true;
*)

open HolKernel Parse boolLib
open bossLib arithmeticTheory powerTheory summationTheory ;

(*
quietdec := false;
*)

val ARW = RW_TAC arith_ss;

val _ = new_theory "binomial";

val FACT_def = ONCE_REWRITE_RULE [MULT_COMM] FACT;

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
Term `!a b. binomial (a+b) b * (FACT a * FACT b)
              =
            FACT (a+b)`,
Induct_on `b`
  THENL [
    REWRITE_TAC[BINOMIAL_DEF1,FACT,ADD_CLAUSES,MULT_CLAUSES],
    Induct_on `a`
      THENL [
        REWRITE_TAC[BINOMIAL_DEF3,FACT,ADD_CLAUSES,MULT_CLAUSES],
        `SUC a + SUC b = SUC (SUC a + b)` by ARW[ADD_CLAUSES]
          THEN ASM_REWRITE_TAC[BINOMIAL_DEF4,RIGHT_ADD_DISTRIB]
          THEN `binomial (SUC a + b) (SUC b) * (FACT (SUC a) * FACT (SUC b))
                 =
                (binomial (a + SUC b) (SUC b) * (FACT a * FACT (SUC b)))
                * SUC a`
             by (REWRITE_TAC[FACT_def,ADD_CLAUSES]
                          THEN PROVE_TAC[MULT_ASSOC,MULT_SYM])
          THEN ASM_REWRITE_TAC[]
          THEN `binomial (SUC a + b) b * (FACT (SUC a) * FACT (SUC b))
                      =
                (binomial (SUC a + b) b * (FACT (SUC a) * FACT b)) * SUC b`
             by (REWRITE_TAC[FACT_def,ADD_CLAUSES]
                   THEN PROVE_TAC[MULT_ASSOC,MULT_SYM])
          THEN ASM_REWRITE_TAC
                 [ADD_CLAUSES,SYM(SPEC_ALL LEFT_ADD_DISTRIB),FACT_def]
      ]
  ]
);


val EXP_PASCAL = store_thm("EXP_PASCAL",
Term `!a b n.
        (a + b) EXP n
          =
        summation 0 (n + 1)
          (\k. binomial n k * (a EXP (n-k) * b EXP k))`,
Induct_on `n`
 THENL [
  RW_TAC bool_ss [power_def,summation_def,BINOMIAL_DEF1, GSYM ADD1]
       THEN ARW[],
  ONCE_REWRITE_TAC[power_def]
       THEN ASM_REWRITE_TAC[RIGHT_ADD_DISTRIB,SUMMATION_TIMES,GSYM ADD1]
       THEN REPEAT STRIP_TAC
       THEN POP_ASSUM (K ALL_TAC)
       THEN `summation 0 (SUC n)
               (\k. a * (binomial n k * (a EXP (n - k) * b EXP k)))
              =
             a * a EXP n +
             summation 1 n
               (\k. a * (binomial n k * (a EXP (n - k) * b EXP k)))`
         by (RW_TAC bool_ss
               [SUMMATION_1,BINOMIAL_DEF1,power_def,MULT_CLAUSES,ONE]
             THEN ARW [])
       THEN `summation 0 (SUC n)
              (\k. b * (binomial n k * (a EXP (n - k) * b EXP k)))
               =
             summation 0 n
               (\k. b * (binomial n k * (a EXP (n - k) * b EXP k)))
               + b * b EXP n`
         by (RW_TAC bool_ss [SUMMATION_2,BINOMIAL_DEF1,
                             power_def,MULT_CLAUSES,ONE]
             THEN ARW [BINOMIAL_DEF3])
       THEN BETA_TAC THEN ASM_REWRITE_TAC[]
       THEN POP_ASSUM_LIST (K ALL_TAC)
       THEN MP_TAC (Q.SPECL[`n`,`0`] SUMMATION_SHIFT)
       THEN DISCH_THEN (fn th => REWRITE_TAC [th])
       THEN BETA_TAC
       THEN sg `(a * a EXP n
             + (summation 1 n
                 (\k. a * (binomial n k * (a EXP (n - k) * b EXP k)))
             + (summation (SUC 0) n
                 (\n'. b * (binomial n (n'-1) *
                           (a EXP (n-(n'-1)) * b EXP (n' - 1))))
             + b * b EXP n)))
          =
             (a * a EXP n
             + (summation 1 n
                 (\k. binomial (SUC n) k * (a EXP (SUC n - k) * b EXP k))
             + b * b EXP n))`
       THENL [
        ARW[]
          THEN RW_TAC bool_ss [ONE, SUMMATION_ADD]
          THEN MATCH_MP_TAC SUMMATION_EXT
          THEN ARW[ADD_CLAUSES,Q.SPEC`n` BINOMIAL_DEF4,RIGHT_ADD_DISTRIB]
          THEN `n - k = SUC (n - SUC k)` by ARW[]
          THEN ASM_REWRITE_TAC[power_def]
          THEN `!x y p q : num. (x = q) /\ (y = p) ==> (x + y = p + q)`
               by DECIDE_TAC
          THEN POP_ASSUM MATCH_MP_TAC
          THEN PROVE_TAC [MULT_SYM,MULT_ASSOC],
         POP_ASSUM (fn th => REWRITE_TAC [th, GSYM ADD_ASSOC])
          THEN ARW[Q.SPEC`SUC n` SUMMATION_1, Q.SPEC`n` SUMMATION_2]
          THEN ARW[power_def,BINOMIAL_DEF1,MULT_CLAUSES,ADD_CLAUSES]
          THEN ARW[GSYM ADD1,BINOMIAL_DEF3,power_def]
       ]
   ]
 );

val _ = export_theory();
