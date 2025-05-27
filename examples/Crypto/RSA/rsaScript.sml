(* interactive mode
app load ["bossLib","gcdTheory","powerTheory","summationTheory",
          "binomialTheory","congruentTheory","fermatTheory"];
quietdec := true;
*)

open HolKernel Parse boolLib bossLib numLib
     arithmeticTheory prim_recTheory
     gcdTheory dividesTheory
     binomialTheory congruentTheory summationTheory powerTheory fermatTheory;

(*
quietdec := false;
*)

val ARW = RW_TAC arith_ss;

val _ = new_theory "rsa";


val GCD_PQ = prove(Term `!p q. prime p /\ prime q /\ ~(p = q)
                                ==>
                               (gcd p q = 1)`,
                         ARW[]
                         THEN `~(divides p q)` by PROVE_TAC[prime_def]
                         THEN PROVE_TAC[PRIME_GCD]);


val CHINESE = store_thm("CHINESE",
                        Term `!p q a b. prime p /\ prime q /\
                                        ~(p=q) /\ b <= a   /\
                                        congruent a b p    /\
                                        congruent a b q
                                           ==>
                                        congruent a b (p*q)`,
                        ARW[]
                        THEN `divides q (a-b)` by ARW[CONGRUENT_DIVIDES]
                        THEN POP_ASSUM MP_TAC THEN ARW[divides_def]
                        THEN `divides p (a-b)` by ARW[CONGRUENT_DIVIDES]
                        THEN POP_ASSUM MP_TAC THEN ARW[divides_def]
                        THEN `divides p (q'*q)` by PROVE_TAC[divides_def,MULT_COMM]
                        THEN `divides p q'` by PROVE_TAC[MULT_SYM,L_EUCLIDES,GCD_PQ]
                        THEN POP_ASSUM MP_TAC THEN ARW[divides_def]
                        THEN ARW[congruent_def]
                        THEN EXISTS_TAC (Term `0`)
                        THEN EXISTS_TAC (Term `q''':num`)
                        THEN ARW[MULT_CLAUSES]
                        THEN PROVE_TAC[ADD_SYM,SUB_ADD,MULT_ASSOC]);


val PRIME_2_OR_MORE = prove(Term `!p. prime p ==> 2 <= p`,
                            Cases_on `p` THEN REWRITE_TAC[NOT_PRIME_0]
                            THEN Cases_on `n` THEN ARW[]
                            THEN MP_TAC NOT_PRIME_1
                            THEN REWRITE_TAC[ONE]);

val PHI_GT_1 = prove(Term `!p q. prime p /\ prime q /\ ~(p=q)
                                   ==>
                                 1 < (p-1) * (q-1)`,
                     ARW[] THEN `2 <= p` by ARW[PRIME_2_OR_MORE]
                     THEN `2 <= q` by ARW[PRIME_2_OR_MORE]
                     THEN Cases_on `p` THEN ARW[]
                     THEN Cases_on `n` THEN ARW[]
                     THEN Cases_on `q` THEN ARW[]
                     THEN Cases_on `n'` THEN ARW[MULT_CLAUSES]);


val RSA_CORRECT = store_thm("RSA_CORRECT",
                     Term `!p q e d w.
                              prime p /\ prime q /\ ~(p=q) /\
                              congruent (e*d) 1 ((p-1)*(q-1))
                                   ==>
                              congruent ($EXP ($EXP w e) d) w (p*q)`,
                     ARW[POWER_POWER]
                     THEN `1 <= e*d` by PROVE_TAC[POWER_LE,CONGRUENT_LE_1,PHI_GT_1,MULT_COMM]
                     THEN `0 < e*d` by DECIDE_TAC
                     THEN `divides ((p-1)*(q-1)) ((e*d)-1)` by PROVE_TAC[CONGRUENT_DIVIDES,MULT_COMM]
                     THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[divides_def] THEN STRIP_TAC
                     THEN MATCH_MP_TAC CHINESE THEN ARW[]
                     THENL [
                      PROVE_TAC[POWER_LE, MULT_COMM],
                      Cases_on `divides p w`
                        THENL [
                          PROVE_TAC[CONGRUENT_TRANS,CONGRUENT_SYM,POWER_0,CONGRUENT_POWER,DIVIDES_CONGRUENT,MULT_COMM],ALL_TAC
                        ]
                        THEN `congruent ($EXP w (p-1)) 1 p` by PROVE_TAC[FERMAT]
                        THEN `congruent ($EXP ($EXP w (p-1)) (q' * (q-1))) 1 p` by PROVE_TAC[CONGRUENT_POWER,POWER_1]
                        THEN `congruent ($EXP w (e*d-1)) 1 p` by PROVE_TAC[POWER_POWER,MULT_ASSOC,MULT_SYM]
                        THEN `congruent (w * $EXP w (e*d -1)) w p` by PROVE_TAC[CONGRUENT_TIMES,MULT_SYM,MULT_LEFT_1]
                        THEN PROVE_TAC[SUB_ADD,power_def,ADD1,MULT_COMM]
                      ,
                      Cases_on `divides q w`
                        THENL [
                          PROVE_TAC[CONGRUENT_TRANS,CONGRUENT_SYM,POWER_0,CONGRUENT_POWER,DIVIDES_CONGRUENT,MULT_COMM],ALL_TAC
                        ]
                        THEN `congruent ($EXP w (q-1)) 1 q` by PROVE_TAC[FERMAT]
                        THEN `congruent ($EXP ($EXP w (q - 1)) (q' * (p - 1))) 1 q` by PROVE_TAC[CONGRUENT_POWER,POWER_1]
                        THEN `congruent ($EXP w (e*d-1)) 1 q` by PROVE_TAC[POWER_POWER,MULT_ASSOC,MULT_SYM]
                        THEN `congruent (w * $EXP w (e*d -1)) w q` by PROVE_TAC[CONGRUENT_TIMES,MULT_SYM,MULT_LEFT_1]
                        THEN PROVE_TAC[SUB_ADD,power_def,ADD1,MULT_COMM]
                     ]
                  );


val _ = export_theory();
