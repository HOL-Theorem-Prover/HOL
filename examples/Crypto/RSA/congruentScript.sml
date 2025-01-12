(* interactive mode
app load ["bossLib","gcdTheory","powerTheory","summationTheory"];
quietdec := true;
*)

open HolKernel Parse boolLib bossLib
     numLib arithmeticTheory prim_recTheory
     gcdTheory powerTheory summationTheory dividesTheory;

(*
quietdec := false;
*)

val ARW = RW_TAC arith_ss;

val _ = new_theory "congruent";


val CONGRUENT = Define `congruent a b n = ?c d. a+c*n = b+d*n`;


val CONGRUENT_REF = store_thm("CONGRUENT_REF",
                        Term `!a n. congruent a a n`,
                        PROVE_TAC[CONGRUENT]);

val CONGRUENT_SYM = store_thm("CONGRUENT_SYM",
                        Term `!a b n. congruent a b n = congruent b a n`,
                        PROVE_TAC[CONGRUENT]);

val CONGRUENT_TRANS = store_thm("CONGRUENT_TRANS",
                        Term `!a b c n. congruent a b n /\ congruent b c n
                                ==> congruent a c n`,
                        ARW[CONGRUENT]
                        THEN EXISTS_TAC (Term `c'+c''`)
                        THEN EXISTS_TAC (Term `d+d'`)
                        THEN ARW[RIGHT_ADD_DISTRIB]
                      );

val CONGRUENT_MULT_0 = store_thm("CONGRUENT_MULT_0",
                        Term `!a b n. congruent a 0 n ==> congruent (a*b) 0 n`,
                        ARW[CONGRUENT]
                        THEN EXISTS_TAC (Term `b*c`)
                        THEN EXISTS_TAC (Term `b*d`)
                        THEN PROVE_TAC[RIGHT_ADD_DISTRIB,MULT_ASSOC,MULT_SYM]);

val CONGRUENT_ADD = store_thm("CONGRUENT_ADD",
                        Term `!a b c d n. congruent a b n /\ congruent c d n
                                 ==> congruent (a+c) (b+d) n`,
                        ARW[CONGRUENT]
                        THEN EXISTS_TAC (Term `c'+c''`)
                        THEN EXISTS_TAC (Term `d'+d''`)
                        THEN ARW[RIGHT_ADD_DISTRIB]);


val CONGRUENT_TIMES = store_thm("CONGRUENT_TIMES",
                        Term `!a b c n. congruent a b n
                                         ==>
                                        congruent (a*c) (b*c) n`,
                        ARW[CONGRUENT]
                        THEN EXISTS_TAC (Term `c'*c`)
                        THEN EXISTS_TAC (Term `d*c`)
                        THEN  ARW[RIGHT_ADD_DISTRIB]
                        THEN `a*c + (c' * c) * n = (a+c'*n)*c`
                          by PROVE_TAC[MULT_ASSOC,MULT_SYM,RIGHT_ADD_DISTRIB]
                        THEN POP_ASSUM MP_TAC
                        THEN ARW[]);

val CONGRUENT_MULT = store_thm("CONGRUENT_MULT",
                        Term `!a b c d n. congruent a b n /\ congruent c d n
                                            ==>
                                          congruent (a*c) (b*d) n`,
                        ARW[CONGRUENT]
                        THEN EXISTS_TAC (Term `a*c''+c*c'+c'*c''*n`)
                        THEN EXISTS_TAC (Term `b*d''+d*d'+d'*d''*n`)
                        THEN `(a * c + (a * c'' + c * c' + c' * c'' * n) * n)
                                 =
                              (a + c' * n) * (c + c'' * n)`
                          by ARW[RIGHT_ADD_DISTRIB,LEFT_ADD_DISTRIB,MULT_ASSOC]
                        THEN ARW[]
                        THEN ARW[LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB,MULT_ASSOC]
                        THEN PROVE_TAC[MULT_SYM,MULT_ASSOC]
                     );


val CONGRUENT_POWER = store_thm("CONGRUENT_POWER",
                        Term `!a b c n. congruent a b n
                                           ==>
                                        congruent ($EXP a c) ($EXP b c) n`,
                        Induct_on `c` THEN
                        PROVE_TAC[power_def,CONGRUENT_MULT,CONGRUENT_REF]);


val CONGRUENT_LE_EX = store_thm("CONGRUENT_LE_EX",
                        Term `!a b n. b <= a /\ congruent a b n
                                          ==>
                                      ?c. a = b + c*n`,
                        ARW[CONGRUENT]
                        THEN EXISTS_TAC (Term `d-c`)
                        THEN ARW[RIGHT_SUB_DISTRIB]
                     );
val CONGRUENT_LE_1 = store_thm("CONGRUENT_LE_1",
                        Term `!a n. 1 < n /\ congruent a 1 n ==> 1 <= a`,
                        Cases_on `a` THEN ARW[CONGRUENT]
                        THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC
                        THEN `(c-d)*n = 1`
                          by (ASM_REWRITE_TAC[RIGHT_SUB_DISTRIB] THEN ARW[])
                        THEN ARW[RIGHT_SUB_DISTRIB]
                        THEN PROVE_TAC[MULT_EQ_1, LESS_REFL]
                     );

val DIVIDES_CONGRUENT = store_thm("DIVIDES_CONGRUENT",
                        Term `!a n. divides n a = congruent a 0 n`,
                        ARW[] THEN
                        `divides n a ==> congruent a 0 n`
                          by (ARW[divides_def,CONGRUENT]
                               THEN EXISTS_TAC (Term `0`)
                               THEN EXISTS_TAC (Term`q:num`) THEN ARW[]) THEN
                        `congruent a 0 n ==> divides n a`
                          by (ARW[divides_def,CONGRUENT]
                               THEN EXISTS_TAC (Term `d-c`) THEN ARW[]) THEN
                        PROVE_TAC[]
                     );

val CONGRUENT_DIVIDES = store_thm("CONGRUENT_DIVIDES",
                        Term `!a b n. b <= a /\ congruent a b n
                                           ==>
                                      divides n (a-b)`,
                         ARW[] THEN IMP_RES_TAC CONGRUENT_LE_EX
                         THEN ARW[DIVIDES_MULT,ADD_SUB]
                         THEN PROVE_TAC[DIVIDES_MULT,ADD_SUB,
                                        DIVIDES_REFL,MULT_SYM]);

val _ = export_theory();
