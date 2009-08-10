structure gcdScript =
struct

open HolKernel Parse boolLib bossLib
     arithmeticTheory dividesTheory primeTheory;

infix THEN THENC THENL;
infix 8 by;

val ARW = RW_TAC arith_ss;

val _ = new_theory "gcd";

val IS_GCD = Define `is_gcd a b c
                        =
                     divides c a /\
                     divides c b /\
                     !d. divides d a /\ divides d b ==> divides d c`;


val IS_GCD_UNIC = store_thm("IS_GCD_UNIC",
                        Term `!a b c d. is_gcd a b c /\ is_gcd a b d ==> (c = d)`,
                        PROVE_TAC[IS_GCD,DIVIDES_ANTISYM]);

val IS_GCD_REF = store_thm("IS_GCD_REF",
			Term `!a. is_gcd a a a`,
                        PROVE_TAC[IS_GCD,DIVIDES_REF]);

val IS_GCD_SYM = store_thm("IS_GCD_SYM",
			Term `!a b c. (is_gcd a b c) = is_gcd b a c`,
                        PROVE_TAC[IS_GCD]);

val IS_GCD_0R = store_thm("IS_GCD_0R",
			Term `!a. is_gcd a 0 a`,
                        PROVE_TAC[IS_GCD,DIVIDES_REF,ALL_DIVIDES_0]);

val IS_GCD_0L = store_thm("IS_GCD_0R",
			Term `!a. is_gcd 0 a a`,
                        PROVE_TAC[IS_GCD,DIVIDES_REF,ALL_DIVIDES_0]);

val PRIME_IS_GCD = store_thm("PRIME_IS_GCD",
                        Term `!p b. prime p ==> divides p b \/ is_gcd p b 1`,
                        ARW[] THEN Cases_on `divides p b` THEN ARW[]
                        THEN ARW[IS_GCD,ONE_DIVIDES_ALL]
                        THEN Cases_on `d=1` THEN ARW[ONE_DIVIDES_ALL]
                        THEN PROVE_TAC[prime_def]);

val IS_GCD_MINUS_L = store_thm("IS_GCD_MINUS_L",
                            Term `!a b c. b <= a /\ is_gcd (a-b) b c ==> is_gcd a b c`,
                            ARW[IS_GCD] THENL [
                              PROVE_TAC[SUB_ADD,DIVIDES_ADD_1],
                              PROVE_TAC[SUB_ADD,DIVIDES_ADD_2,ADD_SYM]
                            ]
                     );

val IS_GCD_MINUS_R = store_thm("IS_GCD_MINUS_R",
                            Term `!a b c. a <= b /\ is_gcd a (b-a) c ==> is_gcd a b c`,
                            PROVE_TAC[IS_GCD_MINUS_L,IS_GCD_SYM]
                     );

val GCD =
 Define
     `(gcd 0 y = y)
 /\   (gcd (SUC x) 0 = SUC x)
 /\   (gcd (SUC x) (SUC y) = if y <= x then gcd (x-y) (SUC y)
                                       else gcd (SUC x) (y-x))`;

val gcd_ind = GEN_ALL (fetch "-" "gcd_ind");


val GCD_IS_GCD = store_thm("GCD_IS_GCD",
                           Term`!a b. is_gcd a b (gcd a b)`,
                           recInduct gcd_ind THEN ARW [GCD] THEN
                           PROVE_TAC [IS_GCD_0L,IS_GCD_0R,
                                      IS_GCD_MINUS_L,IS_GCD_MINUS_R,
                                      DECIDE``~(y<=x) ==> SUC x <= SUC y``,
                                      LESS_EQ_MONO,SUB_MONO_EQ]);

val GCD_REF = store_thm("GCD_REF",
                        Term `!a. gcd a a = a`,
                        PROVE_TAC[GCD_IS_GCD,IS_GCD_UNIC,IS_GCD_REF]);

val GCD_SYM = store_thm("GCD_SYM",
                        Term `!a b. gcd a b = gcd b a`,
                        PROVE_TAC[GCD_IS_GCD,IS_GCD_UNIC,IS_GCD_SYM]);

val GCD_0R = store_thm("GCD_0R",
                        Term `!a. gcd a 0 = a`,
                        PROVE_TAC[GCD_IS_GCD,IS_GCD_UNIC,IS_GCD_0R]);

val GCD_0L = store_thm("GCD_0L",
                        Term `!a. gcd 0 a = a`,
                        PROVE_TAC[GCD_IS_GCD,IS_GCD_UNIC,IS_GCD_0L]);

val GCD_0L = store_thm("GCD_0L",
                        Term `!a. gcd 0 a = a`,
                        PROVE_TAC[GCD_IS_GCD,IS_GCD_UNIC,IS_GCD_0L]);

val GCD_ADD_R = store_thm("GCD_ADD_R",
                        Term `!a b. gcd a (a+b) = gcd a b`,
                        ARW[] THEN MATCH_MP_TAC (SPECL[Term `a:num`, Term `a+b`] IS_GCD_UNIC)
                        THEN ARW[GCD_IS_GCD,SPECL [Term `a:num`, Term `a+b`] IS_GCD_MINUS_R]
                );

val GCD_ADD_L = store_thm("GCD_ADD_L",
                        Term `!a b. gcd (a+b) a = gcd a b`,
                        PROVE_TAC[GCD_SYM,GCD_ADD_R]
                );

val PRIME_GCD = store_thm("PRIME_GCD",
                        Term `!p b. prime p ==> divides p b \/ (gcd p b = 1)`,
                        PROVE_TAC[PRIME_IS_GCD,GCD_IS_GCD,IS_GCD_UNIC]);

val EUCLIDES_AUX = prove(Term
`!a b c d. divides c (d*a) /\ divides c (d*b)
               ==>
             divides c (d*gcd a b)`,
recInduct gcd_ind THEN ARW [GCD]
  THEN Q.PAT_ASSUM `$! M` MATCH_MP_TAC
  THENL [`?z. x = y+z` by (Q.EXISTS_TAC `x-y` THEN DECIDE_TAC),
         `?z. y = x+z` by (Q.EXISTS_TAC `y-x` THEN DECIDE_TAC)]
  THEN RW_TAC std_ss [DECIDE ``(x + y) - x = y``]
  THEN PROVE_TAC [DIVIDES_ADD_2,ADD_ASSOC,MULT_CLAUSES,
                  ADD_CLAUSES,LEFT_ADD_DISTRIB]);


val L_EUCLIDES = store_thm("L_EUCLIDES",
                           Term `!a b c. (gcd a b = 1) /\ divides b (a*c) ==> divides b c`,
                           ARW[]
                           THEN `c=c* gcd a b` by ARW[MULT_CLAUSES]
                           THEN ONCE_ASM_REWRITE_TAC[]
                           THEN PROVE_TAC[EUCLIDES_AUX,DIVIDES_MULT,MULT_SYM,DIVIDES_REF]);


val P_EUCLIDES = store_thm("P_EUCLIDES",
                           Term `!p a b. prime p /\ divides p (a*b)
                                           ==>
                                         divides p a \/ divides p b`,
                           ARW[] THEN Cases_on `divides p a` THEN ARW[]
                           THEN `gcd p a = 1` by PROVE_TAC[GCD_IS_GCD,IS_GCD_UNIC,PRIME_GCD]
                           THEN PROVE_TAC[L_EUCLIDES,GCD_SYM]
                           );

val _ = export_theory();

end;
