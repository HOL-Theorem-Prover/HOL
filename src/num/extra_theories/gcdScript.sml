structure gcdScript =
struct

open HolKernel Parse boolLib TotalDefn BasicProvers
     arithmeticTheory dividesTheory simpLib boolSimps
     Induction;

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


val GCD_IS_GCD = 
  store_thm("GCD_IS_GCD",
     ``!a b. is_gcd a b (gcd a b)``,
   recInduct gcd_ind THEN ARW [GCD] THEN
   PROVE_TAC [IS_GCD_0L,IS_GCD_0R,IS_GCD_MINUS_L,
              IS_GCD_MINUS_R, DECIDE(Term`~(y<=x) ==> SUC x <= SUC y`),
              LESS_EQ_MONO,SUB_MONO_EQ]);

val GCD_THM = REWRITE_RULE [GCD_IS_GCD] (Q.SPECL [`m`,`n`,`gcd m n`] IS_GCD);

val GCD_REF = store_thm("GCD_REF",
                        Term `!a. gcd a a = a`,
                        PROVE_TAC[GCD_IS_GCD,IS_GCD_UNIQUE,IS_GCD_REF]);
val _ = export_rewrites ["GCD_REF"]

val GCD_SYM = store_thm("GCD_SYM",
                        Term `!a b. gcd a b = gcd b a`,
                        PROVE_TAC[GCD_IS_GCD,IS_GCD_UNIQUE,IS_GCD_SYM]);

val GCD_0R = store_thm("GCD_0R",
                        Term `!a. gcd a 0 = a`,
                        PROVE_TAC[GCD_IS_GCD,IS_GCD_UNIQUE,IS_GCD_0R]);
val _ = export_rewrites ["GCD_0R"]

val GCD_0L = store_thm("GCD_0L",
                        Term `!a. gcd 0 a = a`,
                        PROVE_TAC[GCD_IS_GCD,IS_GCD_UNIQUE,IS_GCD_0L]);
val _ = export_rewrites ["GCD_0L"]

val GCD_ADD_R = store_thm("GCD_ADD_R",
                        Term `!a b. gcd a (a+b) = gcd a b`,
                        ARW[] THEN MATCH_MP_TAC (SPECL[Term `a:num`, Term `a+b`] IS_GCD_UNIQUE)
                        THEN ARW[GCD_IS_GCD,SPECL [Term `a:num`, Term `a+b`] IS_GCD_MINUS_R]
                );

val GCD_ADD_R_THM = save_thm(
  "GCD_ADD_R_THM",
  CONJ GCD_ADD_R (ONCE_REWRITE_RULE [ADD_COMM] GCD_ADD_R))
val _ = export_rewrites ["GCD_ADD_R_THM"]

val GCD_ADD_L = store_thm("GCD_ADD_L",
                        Term `!a b. gcd (a+b) a = gcd a b`,
                        PROVE_TAC[GCD_SYM,GCD_ADD_R]
                );

val GCD_ADD_L_THM = save_thm(
 "GCD_ADD_L_THM",
 CONJ GCD_ADD_L (ONCE_REWRITE_RULE [ADD_COMM] GCD_ADD_L))
val _ = export_rewrites ["GCD_ADD_L_THM"]

val GCD_EQ_0 = store_thm(
  "GCD_EQ_0",
  ``!n m. (gcd n m = 0) = (n = 0) /\ (m = 0)``,
  HO_MATCH_MP_TAC gcd_ind THEN SRW_TAC [][GCD]);
val _ = export_rewrites ["GCD_EQ_0"]

val GCD_1 = store_thm(
  "GCD_1",
  ``(gcd 1 x = 1) /\ (gcd x 1 = 1)``,
  Q_TAC SUFF_TAC `!m n. (m = 1) ==> (gcd m n = 1)`
        THEN1 PROVE_TAC [GCD_SYM] THEN
  HO_MATCH_MP_TAC gcd_ind THEN SRW_TAC [][GCD]);
val _ = export_rewrites ["GCD_1"]

val PRIME_GCD = store_thm("PRIME_GCD",
                        Term `!p b. prime p ==> divides p b \/ (gcd p b = 1)`,
                        PROVE_TAC[PRIME_IS_GCD,GCD_IS_GCD,IS_GCD_UNIQUE]);

val EUCLIDES_AUX = prove(Term
`!a b c d. divides c (d*a) /\ divides c (d*b)
               ==>
             divides c (d*gcd a b)`,
recInduct gcd_ind THEN SRW_TAC [][GCD]
  THEN FIRST_X_ASSUM MATCH_MP_TAC
  THENL [`?z. x = y+z` by (Q.EXISTS_TAC `x-y` THEN DECIDE_TAC),
         `?z. y = x+z` by (Q.EXISTS_TAC `y-x` THEN DECIDE_TAC)]
  THEN RW_TAC bool_ss [DECIDE (Term`(x + y) - x = y`)]
  THEN FULL_SIMP_TAC (srw_ss()) [MULT_CLAUSES, LEFT_ADD_DISTRIB]
  THEN PROVE_TAC [DIVIDES_ADD_2,ADD_ASSOC]);


val L_EUCLIDES = store_thm("L_EUCLIDES",
  Term `!a b c. (gcd a b = 1) /\ divides b (a*c) ==> divides b c`,
  ARW[]
  THEN `c = c * gcd a b` by ARW[MULT_CLAUSES]
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
  `divides (gcd n m) n` by PROVE_TAC [GCD_THM] THEN
  `divides (gcd n m) m` by PROVE_TAC [GCD_THM] THEN
  `?k. k * gcd n m = n` by PROVE_TAC [divides_def] THEN
  `?j. j * gcd n m = m` by PROVE_TAC [divides_def] THEN
  MAP_EVERY Q.EXISTS_TAC [`k`, `j`] THEN
  ASM_REWRITE_TAC [] THEN
  SPOSE_NOT_THEN ASSUME_TAC THEN
  `divides (gcd k j) k` by PROVE_TAC [GCD_THM] THEN
  `divides (gcd k j) j` by PROVE_TAC [GCD_THM] THEN
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

val lexnum_induct =
    (SIMP_RULE (srw_ss()) [pairTheory.FORALL_PROD, pairTheory.LEX_DEF] o
     Q.SPEC `UNCURRY P` o
     SIMP_RULE bool_ss [pairTheory.WF_LEX, prim_recTheory.WF_LESS] o
     ISPEC ``(<) LEX (<)``) relationTheory.WF_INDUCTION_THM

(* an induction principle for GCD like situations without any SUCs and without
   any subtractions *)
val GCD_SUCfree_ind = store_thm(
  "GCD_SUCfree_ind",
  ``!P. (!y. P 0 y) /\ (!x y. P x y ==> P y x) /\ (!x. P x x) /\
        (!x y. 0 < x /\ 0 < y /\ P x y ==> P x (x + y)) ==>
        !m n. P m n``,
  GEN_TAC THEN STRIP_TAC THEN
  HO_MATCH_MP_TAC lexnum_induct THEN
  REPEAT STRIP_TAC THEN Cases_on `m = 0` THEN1 SRW_TAC [][] THEN
  Cases_on `m = n` THEN1 SRW_TAC [][] THEN
  `0 < m` by DECIDE_TAC THEN
  Cases_on `m < n` THENL [
    Q_TAC SUFF_TAC `?z. (n = m + z) /\ 0 < z /\ z < n`
          THEN1 metisLib.METIS_TAC [] THEN
    Q.EXISTS_TAC `n - m` THEN DECIDE_TAC,
    `n < m` by DECIDE_TAC THEN SRW_TAC [][]
  ])

(* proof of LINEAR_GCD{_AUX} due to Laurent Thery *)
val LINEAR_GCD_AUX = prove(
  ``!m n. ~(n = 0) /\ ~(m = 0) ==>
          (?p q. p * n = q * m + gcd m n) /\ ?p q. p * m = q * n + gcd m n``,
  HO_MATCH_MP_TAC GCD_SUCfree_ind THEN
  SRW_TAC [][LEFT_ADD_DISTRIB] THEN
  RULE_ASSUM_TAC (REWRITE_RULE [DECIDE ``0 < x = ~(x = 0)``]) THENL [
    PROVE_TAC [GCD_SYM],
    PROVE_TAC [GCD_SYM],
    MAP_EVERY Q.EXISTS_TAC [`1`,`0`] THEN SRW_TAC [][],
    `?a b. a * n = b * m + gcd m n` by PROVE_TAC [] THEN
    MAP_EVERY Q.EXISTS_TAC [`a`, `a + b`],

    `?a b. a * m = b * n + gcd m n` by PROVE_TAC [] THEN
    MAP_EVERY Q.EXISTS_TAC [`a + b`, `b`],

    `?a b. a * n = b * m + gcd m n` by PROVE_TAC [] THEN
    MAP_EVERY Q.EXISTS_TAC [`a`, `a + b`],

    `?a b. a * m = b * n + gcd m n` by PROVE_TAC [] THEN
    MAP_EVERY Q.EXISTS_TAC [`a + b`, `b`]
  ] THEN
  ASM_SIMP_TAC bool_ss [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] THEN
  SIMP_TAC (bool_ss ++ numSimps.ARITH_ss) [])


val LINEAR_GCD = store_thm(
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

open numSimps metisLib;

val GCD_EFFICIENTLY = store_thm(
  "GCD_EFFICIENTLY",
  ``!a b.
       gcd a b = if a = 0 then b
                 else gcd (b MOD a) a``,
  REPEAT STRIP_TAC THEN Cases_on `a = 0` THEN1 SRW_TAC [][] THEN
  Cases_on `b = 0` THEN1 SRW_TAC [ARITH_ss][] THEN
  `(b = (b DIV a) * a + b MOD a) /\ b MOD a < a`
    by (MATCH_MP_TAC DIVISION THEN DECIDE_TAC) THEN
  Q.ABBREV_TAC `q = b DIV a` THEN Q.ABBREV_TAC `r = b MOD a` THEN
  markerLib.RM_ALL_ABBREVS_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  `q * a <= q * a + r` by DECIDE_TAC THEN
  `gcd a (q * a + r) = gcd a (q * a + r - q * a)`
     by METIS_TAC [GCD_SYM, gcd_lemma] THEN
  ASM_SIMP_TAC bool_ss [DECIDE (Term`(x:num) + y - x = y`)] THEN
  SIMP_TAC bool_ss [GCD_SYM]);

val _ = computeLib.add_persistent_funs [("GCD_EFFICIENTLY",GCD_EFFICIENTLY)];

val lcm_def = Define`
  lcm m n = if (m = 0) \/ (n = 0) then 0 else (m * n) DIV gcd m n
`;

val _ = computeLib.add_persistent_funs
      [("GCD_EFFICIENTLY",GCD_EFFICIENTLY),
       ("lcm_def", lcm_def)];

val LCM_IS_LEAST_COMMON_MULTIPLE = store_thm(
  "LCM_IS_LEAST_COMMON_MULTIPLE",
  ``divides m (lcm m n) /\ divides n (lcm m n) /\
    !p. divides m p /\ divides n p ==> divides (lcm m n) p``,
  SIMP_TAC (srw_ss()) [lcm_def] THEN
  Cases_on `m = 0` THEN1 SRW_TAC [][ALL_DIVIDES_0] THEN
  Cases_on `n = 0` THEN1 SRW_TAC [][ALL_DIVIDES_0] THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  Q.ABBREV_TAC `g = gcd m n` THEN
  `?c d. (m = c * g) /\ (n = d * g) /\ (gcd c d = 1)`
      by METIS_TAC [FACTOR_OUT_GCD] THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN STRIP_TAC THEN
  `c * g * (d * g) DIV g = c * g * d`
     by (MATCH_MP_TAC DIV_UNIQUE THEN Q.EXISTS_TAC `0` THEN
         FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [ZERO_LESS_MULT]) THEN
  REPEAT CONJ_TAC THENL [
    SRW_TAC [][divides_def] THEN Q.EXISTS_TAC `d` THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    SRW_TAC [][divides_def] THEN Q.EXISTS_TAC `c` THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [],
    REPEAT STRIP_TAC THEN
    `?a b. (p = a * (c * g)) /\ (p = b * (d * g))`
       by PROVE_TAC [divides_def] THEN
    SRW_TAC [][] THEN
    `0 < g` by FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [MULT_EQ_0] THEN
    `b * d = a * c`
       by (`b * (d * g) = g * (b * d)` by DECIDE_TAC THEN
           `a * (c * g) = g * (a * c)` by DECIDE_TAC THEN
           `g * (b * d) = g * (a * c)` by DECIDE_TAC THEN
           POP_ASSUM MP_TAC THEN SIMP_TAC (srw_ss()) [EQ_MULT_LCANCEL] THEN
           SRW_TAC [ARITH_ss][]) THEN
    Q_TAC SUFF_TAC `divides d a`
          THEN1 (SRW_TAC [][divides_def] THEN
                 Q.EXISTS_TAC `q` THEN DECIDE_TAC) THEN
    `divides d (a * c)` by PROVE_TAC [divides_def] THEN
    PROVE_TAC [L_EUCLIDES, MULT_COMM]
  ]);

val LCM_0 = store_thm(
  "LCM_0",
  ``(lcm 0 x = 0) /\ (lcm x 0 = 0)``,
  SRW_TAC [][lcm_def]);
val _ = export_rewrites ["LCM_0"]

val LCM_1 = store_thm(
  "LCM_1",
  ``(lcm 1 x = x) /\ (lcm x 1 = x)``,
  SRW_TAC [][lcm_def])
val _ = export_rewrites ["LCM_1"]

val LCM_COMM = store_thm(
  "LCM_COMM",
  ``lcm a b = lcm b a``,
  SRW_TAC [][lcm_def, GCD_SYM, MULT_COMM]);

val LCM_LE = store_thm(
  "LCM_LE",
  ``0 < m /\ 0 < n ==> (m <= lcm m n) /\ (m <= lcm n m)``,
  SIMP_TAC (srw_ss() ++ ARITH_ss) [lcm_def, GCD_SYM] THEN
  `divides (gcd m n) n` by METIS_TAC [GCD_IS_GCD, IS_GCD] THEN
  Q.ABBREV_TAC `g = gcd m n` THEN
  `?a. n = a * g` by METIS_TAC [divides_def] THEN
  STRIP_TAC THEN SRW_TAC [][] THEN
  `0 < g` by FULL_SIMP_TAC (srw_ss()) [ZERO_LESS_MULT] THEN
  `m * (a * g) DIV g = m * a` by METIS_TAC [MULT_DIV, MULT_ASSOC] THEN
  Q_TAC SUFF_TAC `1 <= a` THEN1 METIS_TAC [LE_MULT_LCANCEL, MULT_CLAUSES] THEN
  FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [ZERO_LESS_MULT]);
val _ = export_rewrites ["LCM_LE"]

val LCM_LEAST = store_thm(
  "LCM_LEAST",
  ``0 < m /\ 0 < n ==>
       !p. 0 < p /\ p < lcm m n ==> ~(divides m p) \/ ~(divides n p)``,
  REPEAT STRIP_TAC THEN SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
  `divides (lcm m n) p` by METIS_TAC [LCM_IS_LEAST_COMMON_MULTIPLE] THEN
  `lcm m n <= p` by METIS_TAC [DIVIDES_LE] THEN
  DECIDE_TAC);


val GCD_COMMON_FACTOR = store_thm("GCD_COMMON_FACTOR",
  ``!m n k. gcd (k * m) (k * n) = k * gcd m n``,
  HO_MATCH_MP_TAC GCD_SUCfree_ind
  THEN REPEAT STRIP_TAC
  THEN1 REWRITE_TAC [GCD,MULT_CLAUSES]
  THEN1 METIS_TAC [GCD_SYM]
  THEN1 REWRITE_TAC [GCD_REF]
  THEN ASM_REWRITE_TAC [LEFT_ADD_DISTRIB,GCD_ADD_R]);

val GCD_EQ_IS_GCD = prove(
  ``!m n. (gcd m n = k) = is_gcd m n k``,
  METIS_TAC [GCD_IS_GCD,IS_GCD_UNIQUE]);

val divides_IMP = prove(
  ``!m n p. divides m n ==> divides m (p * n)``,
  REWRITE_TAC [divides_def] THEN REPEAT STRIP_TAC
  THEN ASM_REWRITE_TAC [MULT_ASSOC] THEN METIS_TAC []);

val GCD_CANCEL_MULT = store_thm("GCD_CANCEL_MULT",
  ``!m n k. (gcd m k = 1) ==> (gcd m (k * n) = gcd m n)``,
  REPEAT STRIP_TAC  
  THEN REWRITE_TAC [GCD_EQ_IS_GCD,IS_GCD,GCD_THM]
  THEN REPEAT STRIP_TAC  
  THEN1 (MATCH_MP_TAC divides_IMP THEN REWRITE_TAC [GCD_THM])
  THEN REVERSE (`divides d n` by ALL_TAC) THEN1 METIS_TAC [GCD_THM]
  THEN MATCH_MP_TAC L_EUCLIDES
  THEN Q.EXISTS_TAC `k`
  THEN ASM_REWRITE_TAC []
  THEN FULL_SIMP_TAC bool_ss [IS_GCD,GCD_EQ_IS_GCD,ONE_DIVIDES_ALL]   
  THEN REPEAT STRIP_TAC
  THEN Q.PAT_ASSUM `!d.bbb` MATCH_MP_TAC
  THEN IMP_RES_TAC DIVIDES_TRANS
  THEN ASM_REWRITE_TAC []);

val ODD_IMP_GCD_CANCEL_EVEN = prove(
  ``!n. ODD n ==> (gcd n (2 * m) = gcd n m)``,
  REPEAT STRIP_TAC
  THEN MATCH_MP_TAC GCD_CANCEL_MULT
  THEN ONCE_REWRITE_TAC [GCD_SYM]
  THEN REVERSE (`~divides 2 n` by ALL_TAC)
  THEN1 (MP_TAC (Q.SPEC `n` (MATCH_MP PRIME_GCD PRIME_2))
         THEN ASM_REWRITE_TAC [])
  THEN REWRITE_TAC [divides_def]
  THEN ONCE_REWRITE_TAC [MULT_COMM]
  THEN REWRITE_TAC [GSYM EVEN_EXISTS]
  THEN FULL_SIMP_TAC bool_ss [ODD_EVEN]);

val BINARY_GCD = store_thm("BINARY_GCD",
  ``!m n. 
      (EVEN m /\ EVEN n ==> (gcd m n = 2 * gcd (m DIV 2) (n DIV 2))) /\ 
      (EVEN m /\ ODD n ==> (gcd m n = gcd (m DIV 2) n))``,
  SIMP_TAC bool_ss [EVEN_EXISTS] THEN REVERSE (REPEAT STRIP_TAC)
  THEN `0 < 2` by (MATCH_MP_TAC PRIME_POS THEN REWRITE_TAC [PRIME_2])
  THEN FULL_SIMP_TAC bool_ss [GCD_COMMON_FACTOR,
         ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV,
         ONCE_REWRITE_RULE [GCD_SYM] ODD_IMP_GCD_CANCEL_EVEN]);

val _ = export_theory();

end;
