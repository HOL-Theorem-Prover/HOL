structure gcdScript =
struct

open HolKernel Parse boolLib bossLib
     arithmeticTheory dividesTheory primeTheory;

open simpLib boolSimps
infix ++

infix THEN THENC THENL;
infix 8 by;

val ARW = RW_TAC arith_ss;

val _ = new_theory "gcd";

val IS_GCD = Define `is_gcd a b c
                        =
                     divides c a /\
                     divides c b /\
                     !d. divides d a /\ divides d b ==> divides d c`;


val IS_GCD_UNIQUE = store_thm("IS_GCD_UNIQUE",
  Term `!a b c d. is_gcd a b c /\ is_gcd a b d ==> (c = d)`,
  PROVE_TAC[IS_GCD,DIVIDES_ANTISYM]);

val IS_GCD_REF = store_thm(
  "IS_GCD_REF",
  Term `!a. is_gcd a a a`,
  PROVE_TAC[IS_GCD,DIVIDES_REFL]);

val IS_GCD_SYM = store_thm("IS_GCD_SYM",
			Term `!a b c. (is_gcd a b c) = is_gcd b a c`,
                        PROVE_TAC[IS_GCD]);

val IS_GCD_0R = store_thm("IS_GCD_0R",
			Term `!a. is_gcd a 0 a`,
                        PROVE_TAC[IS_GCD,DIVIDES_REFL,ALL_DIVIDES_0]);

val IS_GCD_0L = store_thm("IS_GCD_0R",
			Term `!a. is_gcd 0 a a`,
                        PROVE_TAC[IS_GCD,DIVIDES_REFL,ALL_DIVIDES_0]);

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

val gcd_ind = GEN_ALL (theorem "gcd_ind");


val GCD_IS_GCD = store_thm("GCD_IS_GCD",
                           Term`!a b. is_gcd a b (gcd a b)`,
                           recInduct gcd_ind THEN ARW [GCD] THEN
                           PROVE_TAC [IS_GCD_0L,IS_GCD_0R,
                                      IS_GCD_MINUS_L,IS_GCD_MINUS_R,
                                      DECIDE(Term`~(y<=x) ==> SUC x <= SUC y`),
                                      LESS_EQ_MONO,SUB_MONO_EQ]);

val GCD_REF = store_thm("GCD_REF",
                        Term `!a. gcd a a = a`,
                        PROVE_TAC[GCD_IS_GCD,IS_GCD_UNIQUE,IS_GCD_REF]);

val GCD_SYM = store_thm("GCD_SYM",
                        Term `!a b. gcd a b = gcd b a`,
                        PROVE_TAC[GCD_IS_GCD,IS_GCD_UNIQUE,IS_GCD_SYM]);

val GCD_0R = store_thm("GCD_0R",
                        Term `!a. gcd a 0 = a`,
                        PROVE_TAC[GCD_IS_GCD,IS_GCD_UNIQUE,IS_GCD_0R]);

val GCD_0L = store_thm("GCD_0L",
                        Term `!a. gcd 0 a = a`,
                        PROVE_TAC[GCD_IS_GCD,IS_GCD_UNIQUE,IS_GCD_0L]);

val GCD_ADD_R = store_thm("GCD_ADD_R",
                        Term `!a b. gcd a (a+b) = gcd a b`,
                        ARW[] THEN MATCH_MP_TAC (SPECL[Term `a:num`, Term `a+b`] IS_GCD_UNIQUE)
                        THEN ARW[GCD_IS_GCD,SPECL [Term `a:num`, Term `a+b`] IS_GCD_MINUS_R]
                );

val GCD_ADD_L = store_thm("GCD_ADD_L",
                        Term `!a b. gcd (a+b) a = gcd a b`,
                        PROVE_TAC[GCD_SYM,GCD_ADD_R]
                );

val GCD_EQ_0 = store_thm(
  "GCD_EQ_0",
  ``!n m. (gcd n m = 0) = (n = 0) /\ (m = 0)``,
  SIMP_TAC std_ss [EQ_IMP_THM, FORALL_AND_THM, GCD] THEN
  HO_MATCH_MP_TAC gcd_ind THEN SIMP_TAC arith_ss [GCD]);

val PRIME_GCD = store_thm("PRIME_GCD",
                        Term `!p b. prime p ==> divides p b \/ (gcd p b = 1)`,
                        PROVE_TAC[PRIME_IS_GCD,GCD_IS_GCD,IS_GCD_UNIQUE]);

val EUCLIDES_AUX = prove(Term
`!a b c d. divides c (d*a) /\ divides c (d*b)
               ==>
             divides c (d*gcd a b)`,
recInduct gcd_ind THEN ARW [GCD]
  THEN Q.PAT_ASSUM `$! M` MATCH_MP_TAC
  THENL [`?z. x = y+z` by (Q.EXISTS_TAC `x-y` THEN DECIDE_TAC),
         `?z. y = x+z` by (Q.EXISTS_TAC `y-x` THEN DECIDE_TAC)]
  THEN RW_TAC std_ss [DECIDE (Term`(x + y) - x = y`)]
  THEN PROVE_TAC [DIVIDES_ADD_2,ADD_ASSOC,MULT_CLAUSES,
                  ADD_CLAUSES,LEFT_ADD_DISTRIB]);


val L_EUCLIDES = store_thm("L_EUCLIDES",
  Term `!a b c. (gcd a b = 1) /\ divides b (a*c) ==> divides b c`,
  ARW[]
  THEN `c=c* gcd a b` by ARW[MULT_CLAUSES]
  THEN ONCE_ASM_REWRITE_TAC[]
  THEN PROVE_TAC[EUCLIDES_AUX,DIVIDES_MULT,MULT_SYM,DIVIDES_REFL]);


val P_EUCLIDES = store_thm(
  "P_EUCLIDES",
  Term `!p a b. prime p /\ divides p (a*b)
                  ==>
                divides p a \/ divides p b`,
  ARW[] THEN Cases_on `divides p a` THEN ARW[] THEN
  `gcd p a = 1` by PROVE_TAC[GCD_IS_GCD,IS_GCD_UNIQUE,PRIME_GCD] THEN
  PROVE_TAC[L_EUCLIDES,GCD_SYM]);


val gcd_lemma1 = prove(
  ``!mx n m.
       (mx = MAX m n) /\
       (gcd m n = 1) /\ ~(m = 0) /\ ~(n = 0) ==>
       ?p q. p * m = q * n + 1``,
  GEN_TAC THEN completeInduct_on `mx` THEN
  REPEAT STRIP_TAC THEN ARW[] THEN
  Cases_on `m = n` THENL [
    `m = 1` by PROVE_TAC [GCD_REF] THEN ARW[],
    ALL_TAC
  ] THEN
  `MIN m n < MAX m n` by PROVE_TAC [MIN_MAX_LT] THEN
  `?k. MAX m n = MIN m n + (k + 1)` by PROVE_TAC [LESS_ADD_1] THEN
  Q.ABBREV_TAC `j = k + 1` THEN
  `~(j = 0)` by ARW[] THEN
  `~(MIN m n = 0)` by PROVE_TAC
                       [BETA_RULE (Q.SPEC `\x. ~(x = 0)` MIN_MAX_PRED)] THEN
  `j < MAX m n` by ARW[] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `MAX j (MIN m n)` MP_TAC) THEN
  `MAX j (MIN m n) < MAX m n` by
     PROVE_TAC [BETA_RULE (Q.SPEC `\x. x < MAX m n` MIN_MAX_PRED)] THEN
  DISCH_THEN (fn th1 => POP_ASSUM (ASSUME_TAC o MP th1)) THEN
  Q.ABBREV_TAC `i = MIN m n` THEN
  FIRST_X_ASSUM (fn th => MP_TAC (Q.SPECL [`i`, `j`] th) THEN
                          MP_TAC (Q.SPECL [`j`, `i`] th)) THEN
  ASM_SIMP_TAC std_ss [MAX_COMM] THEN
  Cases_on `m < n` THENL [
    FULL_SIMP_TAC std_ss [MIN_DEF, MAX_DEF] THEN
    `gcd i j = 1` by PROVE_TAC [GCD_ADD_R, GCD_REF] THEN
    ASM_SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY Q.EXISTS_TAC [`p + q`, `q`],
    `n < m` by ARW[] THEN FULL_SIMP_TAC std_ss [MIN_DEF, MAX_DEF] THEN
    `gcd j i = 1` by PROVE_TAC [GCD_ADD_L, GCD_REF, GCD_SYM] THEN
    ASM_SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY Q.EXISTS_TAC [`p`, `p + q`]
  ] THEN
  ASM_REWRITE_TAC [RIGHT_ADD_DISTRIB, LEFT_ADD_DISTRIB] THEN
  SIMP_TAC arith_ss []);

val gcd_lemma = SIMP_RULE bool_ss [] gcd_lemma1;

val FACTOR_OUT_GCD = store_thm(
  "FACTOR_OUT_GCD",
  ``!n m. ~(n = 0) /\ ~(m = 0) ==>
          ?p q. (n = p * gcd n m) /\ (m = q * gcd n m) /\
                (gcd p q = 1)``,
  REPEAT STRIP_TAC THEN
  `divides (gcd n m) n` by PROVE_TAC [GCD_IS_GCD, IS_GCD] THEN
  `divides (gcd n m) m` by PROVE_TAC [GCD_IS_GCD, IS_GCD] THEN
  `?k. k * gcd n m = n` by PROVE_TAC [divides_def] THEN
  `?j. j * gcd n m = m` by PROVE_TAC [divides_def] THEN
  MAP_EVERY Q.EXISTS_TAC [`k`, `j`] THEN
  ASM_REWRITE_TAC [] THEN
  SPOSE_NOT_THEN ASSUME_TAC THEN
  `divides (gcd k j) k` by PROVE_TAC [GCD_IS_GCD, IS_GCD] THEN
  `divides (gcd k j) j` by PROVE_TAC [GCD_IS_GCD, IS_GCD] THEN
  `?u. u * gcd k j = k` by PROVE_TAC [divides_def] THEN
  `?v. v * gcd k j = j` by PROVE_TAC [divides_def] THEN
  `divides (gcd k j * gcd n m) n` by
     PROVE_TAC [MULT_ASSOC, divides_def] THEN
  `divides (gcd k j * gcd n m) m` by
     PROVE_TAC [MULT_ASSOC, divides_def] THEN
  `divides (gcd k j * gcd n m) (gcd n m)`
     by PROVE_TAC [GCD_IS_GCD, IS_GCD] THEN
  `gcd n m = 0` by PROVE_TAC [DIVIDES_MULT_LEFT] THEN
  FULL_SIMP_TAC std_ss [GCD_EQ_0]);

val LINEAR_GCD = store_thm(
  "LINEAR_GCD",
  ``!n m. ~(n = 0) ==> ?p q. p * n = q * m + gcd m n``,
  REPEAT STRIP_TAC THEN
  Cases_on `m = 0` THENL [
    POP_ASSUM SUBST1_TAC THEN ARW[GCD] THEN PROVE_TAC [MULT_CLAUSES],
    ALL_TAC
  ] THEN
  MP_TAC (Q.SPECL [`m`, `n`] FACTOR_OUT_GCD) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (Q.X_CHOOSE_THEN `i` (Q.X_CHOOSE_THEN `j` STRIP_ASSUME_TAC)) THEN
  Q.ABBREV_TAC `g = gcd m n` THEN
  ASM_REWRITE_TAC [] THEN
  `!p. p * (j * g) = g * (p * j)` by
     (GEN_TAC THEN CONV_TAC (AC_CONV(MULT_ASSOC, MULT_COMM))) THEN
  POP_ASSUM (REWRITE_TAC o C cons []) THEN
  `!q. q * (i * g) + g = g * (q * i + 1)` by
     (GEN_TAC THEN REWRITE_TAC [LEFT_ADD_DISTRIB, EQ_ADD_RCANCEL,
                                MULT_RIGHT_1] THEN
      CONV_TAC (AC_CONV(MULT_ASSOC, MULT_COMM))) THEN
  POP_ASSUM (REWRITE_TAC o C cons []) THEN
  SIMP_TAC std_ss [EQ_MULT_LCANCEL, EXISTS_OR_THM] THEN
  `~(i = 0)` by (STRIP_TAC THEN FULL_SIMP_TAC arith_ss []) THEN
  `~(j = 0)` by (STRIP_TAC THEN FULL_SIMP_TAC arith_ss []) THEN
  PROVE_TAC [GCD_SYM, gcd_lemma]);

val gcd_lemma0 = prove(
  ``!a b. gcd a b = if b <= a then gcd (a - b) b
                    else gcd a (b - a)``,
  Cases THEN SIMP_TAC arith_ss [] THEN
  Cases THEN SIMP_TAC arith_ss [] THEN
  REWRITE_TAC [GCD]);

val gcd_lemma = prove(
  ``!n a b. n * b <= a ==> (gcd a b = gcd (a - n * b) b)``,
  Induct THENL [
    SIMP_TAC arith_ss [],
    SIMP_TAC std_ss [MULT_CLAUSES] THEN REPEAT STRIP_TAC THEN
    `n * b <= a` by ASM_SIMP_TAC arith_ss [] THEN
    SIMP_TAC std_ss [SUB_PLUS] THEN
    Q.SPECL_THEN [`a - n * b`, `b`] MP_TAC gcd_lemma0 THEN
    ASM_SIMP_TAC arith_ss []
  ]);

val GCD_EFFICIENTLY = store_thm(
  "GCD_EFFICIENTLY",
  ``!a b.
       gcd a b = if a = 0 then b
                 else gcd (b MOD a) a``,
  REPEAT STRIP_TAC THEN
  Cases_on `a = 0` THENL [
    ASM_SIMP_TAC arith_ss [GCD_0L],
    ALL_TAC
  ] THEN Cases_on `b = 0` THENL [
    ASM_SIMP_TAC arith_ss [GCD_0L, GCD_0R, ZERO_MOD],
    ALL_TAC
  ] THEN
  Q.SPEC_THEN `a` MP_TAC DIVISION THEN
  ASM_SIMP_TAC arith_ss [] THEN
  DISCH_THEN (Q.SPEC_THEN `b` STRIP_ASSUME_TAC) THEN
  Q.ABBREV_TAC `q = b DIV a` THEN Q.ABBREV_TAC `r = b MOD a` THEN
  NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  `q * a <= q * a + r` by SIMP_TAC arith_ss [] THEN
  POP_ASSUM (SUBST_ALL_TAC o ONCE_REWRITE_RULE [GCD_SYM] o
             MATCH_MP gcd_lemma) THEN
  SIMP_TAC std_ss [DECIDE (Term`(x:num) + y - x = y`)] THEN
  CONV_TAC (RAND_CONV (REWR_CONV GCD_SYM)) THEN REWRITE_TAC []);

val _ = export_theory();

end;
