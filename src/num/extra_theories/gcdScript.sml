structure gcdScript =
struct

open HolKernel Parse boolLib TotalDefn BasicProvers SingleStep
     arithmeticTheory dividesTheory simpLib boolSimps;

val arith_ss = bool_ss ++ numSimps.ARITH_ss

val ARW = RW_TAC arith_ss

val DECIDE = Drule.EQT_ELIM o Arith.ARITH_CONV;

fun DECIDE_TAC (g as (asl,_)) =
  ((MAP_EVERY UNDISCH_TAC (filter numSimps.is_arith asl) THEN
    CONV_TAC Arith.ARITH_CONV)
   ORELSE tautLib.TAUT_TAC) g;

val _ = new_theory "gcd";

val IS_GCD = Q.new_definition
 ("is_gcd_def",
  `is_gcd a b c = divides c a /\
                  divides c b /\
                  !d. divides d a /\ divides d b ==> divides d c`);


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

val gcd_ind = GEN_ALL (DB.fetch "-" "gcd_ind");


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
  SIMP_TAC bool_ss [EQ_IMP_THM, FORALL_AND_THM, GCD] THEN
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
  THEN RW_TAC bool_ss [DECIDE (Term`(x + y) - x = y`)]
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
  FULL_SIMP_TAC bool_ss [GCD_EQ_0]);

open labelLib

val simple_facts = map DECIDE [``~(x = y) /\ x < y = ~(y - x = 0)``,
                               ``x < y = ~(y <= x)``,
                               ``x <= y = (x = y) \/ (x < y)``]

(* proof of LINEAR_GCD{_AUX} due to Laurent Thery *)
val LINEAR_GCD_AUX = prove(
 ``!m n. ~(n = 0)/\ ~(m = 0) ==>
      (?p q. p * n = q * m + gcd m n) /\ ?p q. p * m = q * n + gcd m n``,
 recInduct gcd_ind THEN SIMP_TAC bool_ss [DECIDE ``~(SUC x = 0)``] THEN
 REPEAT (GEN_TAC ORELSE DISCH_THEN STRIP_ASSUME_TAC) THEN
 Q.PAT_ASSUM `y <= x ==> P x y` (ASSUME_NAMED_TAC "ind_le") THEN
 Q.PAT_ASSUM `~(y <= x) ==> P x y` (ASSUME_NAMED_TAC "ind_nle") THEN
 Cases_on `x=y` THEN1 (CONJ_TAC THEN MAP_EVERY Q.EXISTS_TAC [`1`,`0`] THEN
                       ASM_SIMP_TAC arith_ss [GCD_REF]) THEN
 Cases_on `x < y` THEN ASM_SIMP_TAC arith_ss [GCD] THENL [
   `SUC y = (y - x) + SUC x` by ARW [],
   `SUC x = (x - y) + SUC y` by ARW []
 ] THEN REPEAT CONJ_TAC THENL [
   `?p q. p * (y - x) = q * SUC x + gcd (SUC x) (y - x)` by
       PROVE_TAC (LB "ind_nle"::simple_facts) THEN
   MAP_EVERY Q.EXISTS_TAC [`p`, `p + q`],
   `?p q. p * SUC x = q * (y - x) + gcd (SUC x) (y - x)` by
       PROVE_TAC (LB "ind_nle"::simple_facts) THEN
   MAP_EVERY Q.EXISTS_TAC [`p + q`, `q`],
   `?p q. p * SUC y = q * (x - y) + gcd (x - y) (SUC y)` by
       PROVE_TAC (LB "ind_le"::simple_facts) THEN
   MAP_EVERY Q.EXISTS_TAC [`p + q`, `q`],
   `?p q. p * (x - y) = q * SUC y + gcd (x - y) (SUC y)` by
       PROVE_TAC (LB "ind_le"::simple_facts) THEN
   MAP_EVERY Q.EXISTS_TAC [`p`, `p + q`]
 ] THEN
 ASM_SIMP_TAC bool_ss [RIGHT_ADD_DISTRIB, LEFT_ADD_DISTRIB] THEN
 SIMP_TAC arith_ss []);

val LINEAR_GCD= store_thm(
  "LINEAR_GCD",
  ``!n m. ~(n = 0) ==> ?p q. p * n = q * m + gcd m n``,
  REPEAT STRIP_TAC THEN Cases_on `m=0` THENL [
    Q.EXISTS_TAC `1` THEN ARW[GCD_0L],
    PROVE_TAC[LINEAR_GCD_AUX]
  ]);

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
    SIMP_TAC bool_ss [MULT_CLAUSES] THEN REPEAT STRIP_TAC THEN
    `n * b <= a` by ASM_SIMP_TAC arith_ss [] THEN
    SIMP_TAC bool_ss [SUB_PLUS] THEN
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
  `(b = (b DIV a) * a + b MOD a) /\ b MOD a < a`
    by (MATCH_MP_TAC DIVISION THEN ASM_SIMP_TAC arith_ss []) THEN
  Q.ABBREV_TAC `q = b DIV a` THEN Q.ABBREV_TAC `r = b MOD a` THEN
  NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  `q * a <= q * a + r` by SIMP_TAC arith_ss [] THEN
  POP_ASSUM (SUBST_ALL_TAC o ONCE_REWRITE_RULE [GCD_SYM] o
             MATCH_MP gcd_lemma) THEN
  ASM_SIMP_TAC bool_ss [DECIDE (Term`(x:num) + y - x = y`)] THEN
  SIMP_TAC bool_ss [GCD_SYM]);

val _ = computeLib.add_persistent_funs [("GCD_EFFICIENTLY",GCD_EFFICIENTLY)];

val _ = export_theory();

end;
