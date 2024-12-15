(* ------------------------------------------------------------------------- *)
(* Elementary Number Theory - a collection of useful results for numbers     *)
(* (gcd = greatest common divisor)                                           *)
(*                                                                           *)
(* Author: (Joseph) Hing-Lun Chan (Australian National University, 2019)     *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib BasicProvers

open prim_recTheory arithmeticTheory dividesTheory simpLib boolSimps
     Induction TotalDefn numSimps metisLib;

val arith_ss = srw_ss() ++ ARITH_ss;
val std_ss = arith_ss;
val ARW = RW_TAC arith_ss

val DECIDE = Drule.EQT_ELIM o Arith.ARITH_CONV;

fun DECIDE_TAC (g as (asl,_)) =
  ((MAP_EVERY UNDISCH_TAC (filter is_arith asl) THEN
    CONV_TAC Arith.ARITH_CONV)
   ORELSE tautLib.TAUT_TAC) g;

val decide_tac = DECIDE_TAC;
val metis_tac = METIS_TAC;
val rw = SRW_TAC [ARITH_ss];
val qabbrev_tac = Q.ABBREV_TAC;
fun simp l = ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) l;
fun fs l = FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) l;

val _ = new_theory "gcd";

val is_gcd_def = Q.new_definition
 ("is_gcd_def",
  `is_gcd a b c <=> divides c a /\ divides c b /\
                    !d. divides d a /\ divides d b ==> divides d c`);

val IS_GCD = is_gcd_def;

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

val IS_GCD_0L = store_thm("IS_GCD_0L",
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

Overload coprime = “\x y. gcd x y = 1” (* from examples/algebra *)

val GCD_IS_GCD =
  store_thm("GCD_IS_GCD",
     ``!a b. is_gcd a b (gcd a b)``,
   recInduct gcd_ind THEN ARW [GCD] THEN
   PROVE_TAC [IS_GCD_0L,IS_GCD_0R,IS_GCD_MINUS_L,
              IS_GCD_MINUS_R, DECIDE(Term`~(y<=x) ==> SUC x <= SUC y`),
              LESS_EQ_MONO,SUB_MONO_EQ]);

val GCD_THM = REWRITE_RULE [GCD_IS_GCD] (Q.SPECL [`m`,`n`,`gcd m n`] IS_GCD);

val GCD_IS_GREATEST_COMMON_DIVISOR = save_thm(
  "GCD_IS_GREATEST_COMMON_DIVISOR",
  REWRITE_RULE [IS_GCD] GCD_IS_GCD)


val GCD_REF = store_thm("GCD_REF",
                        Term `!a. gcd a a = a`,
                        PROVE_TAC[GCD_IS_GCD,IS_GCD_UNIQUE,IS_GCD_REF]);
val _ = export_rewrites ["GCD_REF"]

val GCD_SYM = store_thm("GCD_SYM",
                        Term `!a b. gcd a b = gcd b a`,
                        PROVE_TAC[GCD_IS_GCD,IS_GCD_UNIQUE,IS_GCD_SYM]);

(* |- gcd a b = gcd b a *)
val GCD_COMM = save_thm("GCD_COMM", GCD_SYM |> SPEC_ALL);

val GCD_0R = store_thm("GCD_0R",
                        Term `!a. gcd a 0 = a`,
                        PROVE_TAC[GCD_IS_GCD,IS_GCD_UNIQUE,IS_GCD_0R]);
val _ = export_rewrites ["GCD_0R"]

val GCD_0L = store_thm("GCD_0L",
                        Term `!a. gcd 0 a = a`,
                        PROVE_TAC[GCD_IS_GCD,IS_GCD_UNIQUE,IS_GCD_0L]);
val _ = export_rewrites ["GCD_0L"]

(* Theorem: (gcd 0 x = x) /\ (gcd x 0 = x) *)
(* Proof: by GCD_0L, GCD_0R *)
val GCD_0 = store_thm(
  "GCD_0",
  ``!x. (gcd 0 x = x) /\ (gcd x 0 = x)``,
  rw_tac std_ss[GCD_0L, GCD_0R]);

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

Theorem GCD_EQ_0[simp]:
  !n m. (gcd n m = 0) <=> (n = 0) /\ (m = 0)
Proof HO_MATCH_MP_TAC gcd_ind THEN SRW_TAC [][GCD]
QED

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

Theorem divides_coprime_mul:
  !n m k. gcd n m = 1 ==> (divides n (m * k) <=> divides n k)
Proof
  srw_tac[][] >> eq_tac >> srw_tac[][]
  >- (full_simp_tac bool_ss [Once GCD_SYM] >> drule L_EUCLIDES >> srw_tac[][])
  >- (drule dividesTheory.DIVIDES_MULT >> simp_tac bool_ss [Once MULT_COMM])
QED

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
  RULE_ASSUM_TAC (REWRITE_RULE [DECIDE ``0 < x <=> ~(x = 0)``]) THENL [
    PROVE_TAC [GCD_SYM],
    PROVE_TAC [GCD_SYM],
    MAP_EVERY Q.EXISTS_TAC [`1`,`0`] THEN SRW_TAC [][],
    `?a b. a * n = b * m + gcd m n` by PROVE_TAC [] THEN
    MAP_EVERY Q.EXISTS_TAC [`a`, `a + b`],

    `?a b. a * m = b * n + gcd m n` by PROVE_TAC [] THEN
    MAP_EVERY Q.EXISTS_TAC [`a + b`, `b`]
  ] THEN
  ASM_SIMP_TAC bool_ss [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] THEN
  SIMP_TAC (bool_ss ++ numSimps.ARITH_ss) []);


val LINEAR_GCD = store_thm(
  "LINEAR_GCD",
  ``!n m. ~(n = 0) ==> ?p q. p * n = q * m + gcd m n``,
  REPEAT STRIP_TAC THEN Cases_on `m=0` THENL [
    Q.EXISTS_TAC `1` THEN ARW[GCD_0L],
    PROVE_TAC[LINEAR_GCD_AUX]
  ]);

(* Theorem: 0 < j ==> ?p q. p * j = q * k + gcd j k *)
(* Proof: by LINEAR_GCD, GCD_SYM *)
val GCD_LINEAR = store_thm(
  "GCD_LINEAR",
  ``!j k. 0 < j ==> ?p q. p * j = q * k + gcd j k``,
  metis_tac[LINEAR_GCD, GCD_SYM, NOT_ZERO]);

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

val lcm_def = Define`
  lcm m n = if (m = 0) \/ (n = 0) then 0 else (m * n) DIV gcd m n
`;

val _ = computeLib.add_persistent_funs
      ["GCD_EFFICIENTLY"
      ,"lcm_def"];

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

(* |- !a b. lcm a b = lcm b a *)
val LCM_SYM = save_thm("LCM_SYM", LCM_COMM |> GEN ``b:num`` |> GEN ``a:num``);

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
  THEN `divides d n` suffices_by METIS_TAC [GCD_THM]
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
  THEN `~divides 2 n` suffices_by
       (STRIP_TAC
        THEN MP_TAC (Q.SPEC `n` (MATCH_MP PRIME_GCD PRIME_2))
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

Theorem gcd_LESS_EQ:
  !m n. n <> 0 ==> gcd m n <= n
Proof
  recInduct gcd_ind >> srw_tac[][] >> rewrite_tac[GCD] >>
  IF_CASES_TAC >> FULL_SIMP_TAC (srw_ss()) [] >>
  irule LESS_EQ_TRANS >> goal_assum drule >>
  rewrite_tac[SUB_RIGHT_LESS_EQ] >>
  rewrite_tac[Once ADD_COMM] >>
  rewrite_tac[ADD_CLAUSES] >>
  rewrite_tac[ADD_SUC] >>
  rewrite_tac[LESS_EQ_ADD]
QED

(* ------------------------------------------------------------------------- *)
(* Basic GCD, LCM Theorems (from examples/algebra)                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: If 0 < n, 0 < m, let g = gcd n m, then 0 < g and n MOD g = 0 and m MOD g = 0 *)
(* Proof:
   0 < n ==> n <> 0, 0 < m ==> m <> 0,              by NOT_ZERO_LT_ZERO
   hence  g = gcd n m <> 0, or 0 < g.               by GCD_EQ_0
   g = gcd n m ==> (g divides n) /\ (g divides m)   by GCD_IS_GCD, is_gcd_def
               ==> (n MOD g = 0) /\ (m MOD g = 0)   by DIVIDES_MOD_0
*)
val GCD_DIVIDES = store_thm(
  "GCD_DIVIDES",
  ``!m n. 0 < n /\ 0 < m ==> 0 < gcd n m /\ (n MOD (gcd n m) = 0) /\ (m MOD (gcd n m) = 0)``,
  ntac 3 strip_tac >>
  conj_asm1_tac >-
  metis_tac[GCD_EQ_0, NOT_ZERO_LT_ZERO] >>
  metis_tac[GCD_IS_GCD, is_gcd_def, DIVIDES_MOD_0]);

(* Theorem: gcd n (gcd n m) = gcd n m *)
(* Proof:
   If n = 0,
      gcd 0 (gcd n m) = gcd n m   by GCD_0L
   If m = 0,
      gcd n (gcd n 0)
    = gcd n n                     by GCD_0R
    = n = gcd n 0                 by GCD_REF
   If n <> 0, m <> 0, d <> 0      by GCD_EQ_0
   Since d divides n, n MOD d = 0
     gcd n d
   = gcd d n             by GCD_SYM
   = gcd (n MOD d) d     by GCD_EFFICIENTLY, d <> 0
   = gcd 0 d             by GCD_DIVIDES
   = d                   by GCD_0L
*)
val GCD_GCD = store_thm(
  "GCD_GCD",
  ``!m n. gcd n (gcd n m) = gcd n m``,
  rpt strip_tac >>
  Cases_on `n = 0` >- rw[] >>
  Cases_on `m = 0` >- rw[] >>
  `0 < n /\ 0 < m` by decide_tac >>
  metis_tac[GCD_SYM, GCD_EFFICIENTLY, GCD_DIVIDES, GCD_EQ_0, GCD_0L]);

(* Theorem: GCD m n * LCM m n = m * n *)
(* Proof:
   By lcm_def:
   lcm m n = if (m = 0) \/ (n = 0) then 0 else m * n DIV gcd m n
   If m = 0,
   gcd 0 n * lcm 0 n = n * 0 = 0 = 0 * n, hence true.
   If n = 0,
   gcd m 0 * lcm m 0 = m * 0 = 0 = m * 0, hence true.
   If m <> 0, n <> 0,
   gcd m n * lcm m n = gcd m n * (m * n DIV gcd m n) = m * n.
*)
val GCD_LCM = store_thm(
  "GCD_LCM",
  ``!m n. gcd m n * lcm m n = m * n``,
  rw[lcm_def] >>
  `0 < m /\ 0 < n` by decide_tac >>
  `0 < gcd m n /\ (n MOD gcd m n = 0)` by rw[GCD_DIVIDES] >>
  qabbrev_tac `d = gcd m n` >>
  `m * n = (m * n) DIV d * d + (m * n) MOD d` by rw[DIVISION] >>
  `(m * n) MOD d = 0` by metis_tac[MOD_TIMES2, ZERO_MOD, MULT_0] >>
  metis_tac[ADD_0, MULT_COMM]);

(* temporarily make divides an infix *)
val _ = temp_set_fixity "divides" (Infixl 480); (* relation is 450, +/- is 500, * is 600. *)

(* Theorem: m divides (lcm m n) /\ n divides (lcm m n) *)
(* Proof: by LCM_IS_LEAST_COMMON_MULTIPLE *)
val LCM_DIVISORS = store_thm(
  "LCM_DIVISORS",
  ``!m n. m divides (lcm m n) /\ n divides (lcm m n)``,
  rw[LCM_IS_LEAST_COMMON_MULTIPLE]);

(* Theorem: m divides p /\ n divides p ==> (lcm m n) divides p *)
(* Proof: by LCM_IS_LEAST_COMMON_MULTIPLE *)
val LCM_IS_LCM = store_thm(
  "LCM_IS_LCM",
  ``!m n p. m divides p /\ n divides p ==> (lcm m n) divides p``,
  rw[LCM_IS_LEAST_COMMON_MULTIPLE]);

(* Theorem: (lcm m n = 0) <=> ((m = 0) \/ (n = 0)) *)
(* Proof:
   If part: lcm m n = 0 ==> m = 0 \/ n = 0
      By contradiction, suppse m = 0 /\ n = 0.
      Then gcd m n = 0                     by GCD_EQ_0
       and m * n = 0                       by MULT_EQ_0
       but (gcd m n) * (lcm m n) = m * n   by GCD_LCM
        so RHS <> 0, but LHS = 0           by MULT_0
       This is a contradiction.
   Only-if part: m = 0 \/ n = 0 ==> lcm m n = 0
      True by LCM_0
*)
val LCM_EQ_0 = store_thm(
  "LCM_EQ_0",
  ``!m n. (lcm m n = 0) <=> ((m = 0) \/ (n = 0))``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `(gcd m n) * (lcm m n) = m * n` by rw[GCD_LCM] >>
    `gcd m n <> 0` by rw[GCD_EQ_0] >>
    `m * n <> 0` by rw[MULT_EQ_0] >>
    metis_tac[MULT_0],
    rw[LCM_0],
    rw[LCM_0]
  ]);

(* Theorem: lcm a a = a *)
(* Proof:
  If a = 0,
     lcm 0 0 = 0                      by LCM_0
  If a <> 0,
     (gcd a a) * (lcm a a) = a * a    by GCD_LCM
             a * (lcm a a) = a * a    by GCD_REF
                   lcm a a = a        by MULT_LEFT_CANCEL, a <> 0
*)
val LCM_REF = store_thm(
  "LCM_REF",
  ``!a. lcm a a = a``,
  metis_tac[num_CASES, LCM_0, GCD_LCM, GCD_REF, MULT_LEFT_CANCEL]);

(* Theorem: a divides n /\ b divides n ==> (lcm a b) divides n *)
(* Proof: same as LCM_IS_LCM *)
val LCM_DIVIDES = store_thm(
  "LCM_DIVIDES",
  ``!n a b. a divides n /\ b divides n ==> (lcm a b) divides n``,
  rw[LCM_IS_LCM]);
(*
> LCM_IS_LCM |> ISPEC ``a:num`` |> ISPEC ``b:num`` |> ISPEC ``n:num`` |> GEN_ALL;
val it = |- !n b a. a divides n /\ b divides n ==> lcm a b divides n: thm
*)

(* Theorem: 0 < m \/ 0 < n ==> 0 < gcd m n *)
(* Proof: by GCD_EQ_0, NOT_ZERO_LT_ZERO *)
val GCD_POS = store_thm(
  "GCD_POS",
  ``!m n. 0 < m \/ 0 < n ==> 0 < gcd m n``,
  metis_tac[GCD_EQ_0, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < m /\ 0 < n ==> 0 < lcm m n *)
(* Proof: by LCM_EQ_0, NOT_ZERO_LT_ZERO *)
val LCM_POS = store_thm(
  "LCM_POS",
  ``!m n. 0 < m /\ 0 < n ==> 0 < lcm m n``,
  metis_tac[LCM_EQ_0, NOT_ZERO_LT_ZERO]);

(* Theorem: n divides m <=> gcd n m = n *)
(* Proof:
   If part:
     n divides m ==> ?k. m = k * n   by divides_def
       gcd n m
     = gcd n (k * n)
     = gcd (n * 1) (n * k)      by MULT_RIGHT_1, MULT_COMM
     = n * gcd 1 k              by GCD_COMMON_FACTOR
     = n * 1                    by GCD_1
     = n                        by MULT_RIGHT_1
   Only-if part: gcd n m = n ==> n divides m
     If n = 0, gcd 0 m = m      by GCD_0L
     But gcd n m = n = 0        by givien
     hence m = 0,
     and 0 divides 0 is true    by DIVIDES_REFL
     If n <> 0,
       If m = 0, LHS true       by GCD_0R
                 RHS true       by ALL_DIVIDES_0
       If m <> 0,
       then 0 < n and 0 < m,
       gcd n m = gcd (m MOD n) n       by GCD_EFFICIENTLY
       if (m MOD n) = 0
          then n divides m             by DIVIDES_MOD_0
       If (m MOD n) <> 0,
       so (m MOD n) MOD (gcd n m) = 0  by GCD_DIVIDES
       or (m MOD n) MOD n = 0          by gcd n m = n, given
       or  m MOD n = 0                 by MOD_MOD
       contradicting (m MOD n) <> 0, hence true.
*)
val divides_iff_gcd_fix = store_thm(
  "divides_iff_gcd_fix",
  ``!m n. n divides m <=> (gcd n m = n)``,
  rw[EQ_IMP_THM] >| [
    `?k. m = k * n` by rw[GSYM divides_def] >>
    `gcd n m = gcd (n * 1) (n * k)` by rw[MULT_COMM] >>
    rw[GCD_COMMON_FACTOR, GCD_1],
    Cases_on `n = 0` >-
    metis_tac[GCD_0L, DIVIDES_REFL] >>
    Cases_on `m = 0` >-
    metis_tac[GCD_0R, ALL_DIVIDES_0] >>
    `0 < n /\ 0 < m` by decide_tac >>
    Cases_on `m MOD n = 0` >-
    metis_tac[DIVIDES_MOD_0] >>
    `0 < m MOD n` by decide_tac >>
    metis_tac[GCD_EFFICIENTLY, GCD_DIVIDES, MOD_MOD]
  ]);

(* Theorem: !m n. n divides m <=> (lcm n m = m) *)
(* Proof:
   If n = 0,
      n divides m <=> m = 0         by ZERO_DIVIDES
      and lcm 0 0 = 0 = m           by LCM_0
   If n <> 0,
     gcd n m * lcm n m = n * m      by GCD_LCM
     If part: n divides m ==> (lcm n m = m)
        Then gcd n m = n            by divides_iff_gcd_fix
        so   n * lcm n m = n * m    by above
                 lcm n m = m        by MULT_LEFT_CANCEL, n <> 0
     Only-if part: lcm n m = m ==> n divides m
        If m = 0, n divdes 0 = true by ALL_DIVIDES_0
        If m <> 0,
        Then gcd n m * m = n * m    by above
          or     gcd n m = n        by MULT_RIGHT_CANCEL, m <> 0
          so     n divides m        by divides_iff_gcd_fix
*)
val divides_iff_lcm_fix = store_thm(
  "divides_iff_lcm_fix",
  ``!m n. n divides m <=> (lcm n m = m)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  metis_tac[ZERO_DIVIDES, LCM_0] >>
  metis_tac[GCD_LCM, MULT_LEFT_CANCEL, MULT_RIGHT_CANCEL, divides_iff_gcd_fix, ALL_DIVIDES_0]);

(* ------------------------------------------------------------------------- *)
(* Consequences of Coprime.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: coprime n x /\ coprime n y ==> coprime n (x * y) *)
(* Proof:
   gcd n x = 1 ==> no common factor between x and n
   gcd n y = 1 ==> no common factor between y and n
   Hence there is no common factor between (x * y) and n, or gcd n (x * y) = 1

   gcd n (x * y) = gcd n y     by GCD_CANCEL_MULT, since coprime n x.
                 = 1           by given
*)
val PRODUCT_WITH_GCD_ONE = store_thm(
  "PRODUCT_WITH_GCD_ONE",
  ``!n x y. coprime n x /\ coprime n y ==> coprime n (x * y)``,
  metis_tac[GCD_CANCEL_MULT]);

(* Theorem: For 0 < n, coprime n x ==> coprime n (x MOD n) *)
(* Proof:
   Since n <> 0,
   1 = gcd n x            by given
     = gcd (x MOD n) n    by GCD_EFFICIENTLY
     = gcd n (x MOD n)    by GCD_SYM
*)
val MOD_WITH_GCD_ONE = store_thm(
  "MOD_WITH_GCD_ONE",
  ``!n x. 0 < n /\ coprime n x ==> coprime n (x MOD n)``,
  rpt strip_tac >>
  `0 <> n` by decide_tac >>
  metis_tac[GCD_EFFICIENTLY, GCD_SYM]);

(* Theorem: (c = gcd a b) <=>
            c divides a /\ c divides b /\ !x. x divides a /\ x divides b ==> x divides c *)
(* Proof:
   By GCD_IS_GREATEST_COMMON_DIVISOR
       (gcd a b) divides a     [1]
   and (gcd a b) divides b     [2]
   and !p. p divides a /\ p divides b ==> p divides (gcd a b)   [3]
   Hence if part is true, and for the only-if part,
   We have c divides (gcd a b)   by [3] above,
       and (gcd a b) divides c   by [1], [2] and the given implication
   Therefore c = gcd a b         by DIVIDES_ANTISYM
*)
val GCD_PROPERTY = store_thm(
  "GCD_PROPERTY",
  ``!a b c. (c = gcd a b) <=>
   c divides a /\ c divides b /\ !x. x divides a /\ x divides b ==> x divides c``,
  rw[GCD_IS_GREATEST_COMMON_DIVISOR, DIVIDES_ANTISYM, EQ_IMP_THM]);

(* Theorem: gcd a (gcd b c) = gcd (gcd a b) c *)
(* Proof:
   Since (gcd a (gcd b c)) divides a    by GCD_PROPERTY
         (gcd a (gcd b c)) divides b    by GCD_PROPERTY, DIVIDES_TRANS
         (gcd a (gcd b c)) divides c    by GCD_PROPERTY, DIVIDES_TRANS
         (gcd (gcd a b) c) divides a    by GCD_PROPERTY, DIVIDES_TRANS
         (gcd (gcd a b) c) divides b    by GCD_PROPERTY, DIVIDES_TRANS
         (gcd (gcd a b) c) divides c    by GCD_PROPERTY
   We have
         (gcd (gcd a b) c) divides (gcd b c)           by GCD_PROPERTY
     and (gcd (gcd a b) c) divides (gcd a (gcd b c))   by GCD_PROPERTY
    Also (gcd a (gcd b c)) divides (gcd a b)           by GCD_PROPERTY
     and (gcd a (gcd b c)) divides (gcd (gcd a b) c)   by GCD_PROPERTY
   Therefore gcd a (gcd b c) = gcd (gcd a b) c         by DIVIDES_ANTISYM
*)
val GCD_ASSOC = store_thm(
  "GCD_ASSOC",
  ``!a b c. gcd a (gcd b c) = gcd (gcd a b) c``,
  rpt strip_tac >>
  `(gcd a (gcd b c)) divides a` by metis_tac[GCD_PROPERTY] >>
  `(gcd a (gcd b c)) divides b` by metis_tac[GCD_PROPERTY, DIVIDES_TRANS] >>
  `(gcd a (gcd b c)) divides c` by metis_tac[GCD_PROPERTY, DIVIDES_TRANS] >>
  `(gcd (gcd a b) c) divides a` by metis_tac[GCD_PROPERTY, DIVIDES_TRANS] >>
  `(gcd (gcd a b) c) divides b` by metis_tac[GCD_PROPERTY, DIVIDES_TRANS] >>
  `(gcd (gcd a b) c) divides c` by metis_tac[GCD_PROPERTY] >>
  `(gcd (gcd a b) c) divides (gcd a (gcd b c))` by metis_tac[GCD_PROPERTY] >>
  `(gcd a (gcd b c)) divides (gcd (gcd a b) c)` by metis_tac[GCD_PROPERTY] >>
  rw[DIVIDES_ANTISYM]);

(* Note:
   With identity by GCD_1: (gcd 1 x = 1) /\ (gcd x 1 = 1)
   GCD forms a monoid in numbers.
*)

(* Theorem: gcd a (gcd b c) = gcd b (gcd a c) *)
(* Proof:
     gcd a (gcd b c)
   = gcd (gcd a b) c    by GCD_ASSOC
   = gcd (gcd b a) c    by GCD_SYM
   = gcd b (gcd a c)    by GCD_ASSOC
*)
val GCD_ASSOC_COMM = store_thm(
  "GCD_ASSOC_COMM",
  ``!a b c. gcd a (gcd b c) = gcd b (gcd a c)``,
  metis_tac[GCD_ASSOC, GCD_SYM]);

(* Theorem: (c = lcm a b) <=>
            a divides c /\ b divides c /\ !x. a divides x /\ b divides x ==> c divides x *)
(* Proof:
   By LCM_IS_LEAST_COMMON_MULTIPLE
       a divides (lcm a b)    [1]
   and b divides (lcm a b)    [2]
   and !p. a divides p /\ divides b p ==> divides (lcm a b) p  [3]
   Hence if part is true, and for the only-if part,
   We have c divides (lcm a b)   by implication and [1], [2]
       and (lcm a b) divides c   by [3]
   Therefore c = lcm a b         by DIVIDES_ANTISYM
*)
val LCM_PROPERTY = store_thm(
  "LCM_PROPERTY",
  ``!a b c. (c = lcm a b) <=>
   a divides c /\ b divides c /\ !x. a divides x /\ b divides x ==> c divides x``,
  rw[LCM_IS_LEAST_COMMON_MULTIPLE, DIVIDES_ANTISYM, EQ_IMP_THM]);

(* Theorem: lcm a (lcm b c) = lcm (lcm a b) c *)
(* Proof:
   Since a divides (lcm a (lcm b c))   by LCM_PROPERTY
         b divides (lcm a (lcm b c))   by LCM_PROPERTY, DIVIDES_TRANS
         c divides (lcm a (lcm b c))   by LCM_PROPERTY, DIVIDES_TRANS
         a divides (lcm (lcm a b) c)   by LCM_PROPERTY, DIVIDES_TRANS
         b divides (lcm (lcm a b) c)   by LCM_PROPERTY, DIVIDES_TRANS
         c divides (lcm (lcm a b) c)   by LCM_PROPERTY
   We have
         (lcm b c) divides (lcm (lcm a b) c)           by LCM_PROPERTY
     and (lcm a (lcm b c)) divides (lcm (lcm a b) c)   by LCM_PROPERTY
    Also (lcm a b) divides (lcm a (lcm b c))           by LCM_PROPERTY
     and (lcm (lcm a b) c) divides (lcm a (lcm b c))   by LCM_PROPERTY
    Therefore lcm a (lcm b c) = lcm (lcm a b) c        by DIVIDES_ANTISYM
*)
val LCM_ASSOC = store_thm(
  "LCM_ASSOC",
  ``!a b c. lcm a (lcm b c) = lcm (lcm a b) c``,
  rpt strip_tac >>
  `a divides (lcm a (lcm b c))` by metis_tac[LCM_PROPERTY] >>
  `b divides (lcm a (lcm b c))` by metis_tac[LCM_PROPERTY, DIVIDES_TRANS] >>
  `c divides (lcm a (lcm b c))` by metis_tac[LCM_PROPERTY, DIVIDES_TRANS] >>
  `a divides (lcm (lcm a b) c)` by metis_tac[LCM_PROPERTY, DIVIDES_TRANS] >>
  `b divides (lcm (lcm a b) c)` by metis_tac[LCM_PROPERTY, DIVIDES_TRANS] >>
  `c divides (lcm (lcm a b) c)` by metis_tac[LCM_PROPERTY] >>
  `(lcm a (lcm b c)) divides (lcm (lcm a b) c)` by metis_tac[LCM_PROPERTY] >>
  `(lcm (lcm a b) c) divides (lcm a (lcm b c))` by metis_tac[LCM_PROPERTY] >>
  rw[DIVIDES_ANTISYM]);

(* Note:
   With the identity by LCM_0: (lcm 0 x = 0) /\ (lcm x 0 = 0)
   LCM forms a monoid in numbers.
*)

(* Theorem: lcm a (lcm b c) = lcm b (lcm a c) *)
(* Proof:
     lcm a (lcm b c)
   = lcm (lcm a b) c   by LCM_ASSOC
   = lcm (lcm b a) c   by LCM_COMM
   = lcm b (lcm a c)   by LCM_ASSOC
*)
val LCM_ASSOC_COMM = store_thm(
  "LCM_ASSOC_COMM",
  ``!a b c. lcm a (lcm b c) = lcm b (lcm a c)``,
  metis_tac[LCM_ASSOC, LCM_COMM]);

(* Theorem: b <= a ==> gcd (a - b) b = gcd a b *)
(* Proof:
     gcd (a - b) b
   = gcd b (a - b)         by GCD_SYM
   = gcd (b + (a - b)) b   by GCD_ADD_L
   = gcd (a - b + b) b     by ADD_COMM
   = gcd a b               by SUB_ADD, b <= a.

Note: If a < b, a - b = 0  for num, hence gcd (a - b) b = gcd 0 b = b.
*)
val GCD_SUB_L = store_thm(
  "GCD_SUB_L",
  ``!a b. b <= a ==> (gcd (a - b) b = gcd a b)``,
  metis_tac[GCD_SYM, GCD_ADD_L, ADD_COMM, SUB_ADD]);

(* Theorem: a <= b ==> gcd a (b - a) = gcd a b *)
(* Proof:
     gcd a (b - a)
   = gcd (b - a) a         by GCD_SYM
   = gcd b a               by GCD_SUB_L
   = gcd a b               by GCD_SYM
*)
val GCD_SUB_R = store_thm(
  "GCD_SUB_R",
  ``!a b. a <= b ==> (gcd a (b - a) = gcd a b)``,
  metis_tac[GCD_SYM, GCD_SUB_L]);

(* Theorem: prime a ==> a divides b iff a divides b ** n for any n *)
(* Proof:
   by induction on n.
   Base case: 0 < 0 ==> (a divides b <=> a divides (b ** 0))
     True since 0 < 0 is False.
   Step case: 0 < n ==> (a divides b <=> a divides (b ** n)) ==>
              0 < SUC n ==> (a divides b <=> a divides (b ** SUC n))
     i.e. 0 < n ==> (a divides b <=> a divides (b ** n))==>
                    a divides b <=> a divides (b * b ** n)    by EXP
     If n = 0, b ** 0 = 1   by EXP
     Hence true.
     If n <> 0, 0 < n,
     If part: a divides b /\ 0 < n ==> (a divides b <=> a divides (b ** n)) ==> a divides (b ** n)
       True by DIVIDES_MULT.
     Only-if part: a divides (b * b ** n) /\ 0 < n ==> (a divides b <=> a divides (b ** n)) ==> a divides (b ** n)
       Since prime a, a divides b, or a divides (b ** n)  by P_EUCLIDES
       Either case is true.
*)
val DIVIDES_EXP_BASE = store_thm(
  "DIVIDES_EXP_BASE",
  ``!a b n. prime a /\ 0 < n ==> (a divides b <=> a divides (b ** n))``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw[EXP] >>
  Cases_on `n = 0` >-
  rw[EXP] >>
  `0 < n` by decide_tac >>
  rw[EQ_IMP_THM] >-
  metis_tac[DIVIDES_MULT] >>
  `a divides b \/ a divides (b ** n)` by rw[P_EUCLIDES] >>
  metis_tac[]);

(* Theorem: coprime m n ==> LCM m n = m * n *)
(* Proof:
   By GCD_LCM, with gcd m n = 1.
*)
val LCM_COPRIME = store_thm(
  "LCM_COPRIME",
  ``!m n. coprime m n ==> (lcm m n = m * n)``,
  metis_tac[GCD_LCM, MULT_LEFT_1]);

(* Theorem: 0 < m ==> (gcd m n = gcd m (n MOD m)) *)
(* Proof:
     gcd m n
   = gcd (n MOD m) m       by GCD_EFFICIENTLY, m <> 0
   = gcd m (n MOD m)       by GCD_SYM
*)
val GCD_MOD = store_thm(
  "GCD_MOD",
  ``!m n. 0 < m ==> (gcd m n = gcd m (n MOD m))``,
  rw[Once GCD_EFFICIENTLY, GCD_SYM]);

(* Theorem: 0 < m ==> (gcd n m = gcd (n MOD m) m) *)
(* Proof: by GCD_MOD, GCD_COMM *)
val GCD_MOD_COMM = store_thm(
  "GCD_MOD_COMM",
  ``!m n. 0 < m ==> (gcd n m = gcd (n MOD m) m)``,
  metis_tac[GCD_MOD, GCD_COMM]);

(* Theorem: gcd a (b * a + c) = gcd a c *)
(* Proof:
   If a = 0,
      Then b * 0 + c = c             by arithmetic
      Hence trivially true.
   If a <> 0,
      gcd a (b * a + c)
    = gcd ((b * a + c) MOD a) a      by GCD_EFFICIENTLY, 0 < a
    = gcd (c MOD a) a                by MOD_TIMES, 0 < a
    = gcd a c                        by GCD_EFFICIENTLY, 0 < a
*)
val GCD_EUCLID = store_thm(
  "GCD_EUCLID",
  ``!a b c. gcd a (b * a + c) = gcd a c``,
  rpt strip_tac >>
  Cases_on `a = 0` >-
  rw[] >>
  metis_tac[GCD_EFFICIENTLY, MOD_TIMES, NOT_ZERO_LT_ZERO]);

(* Theorem: gcd (b * a + c) a = gcd a c *)
(* Proof: by GCD_EUCLID, GCD_SYM *)
val GCD_REDUCE = store_thm(
  "GCD_REDUCE",
  ``!a b c. gcd (b * a + c) a = gcd a c``,
  rw[GCD_EUCLID, GCD_SYM]);

(* Theorem alias *)
Theorem GCD_REDUCE_BY_COPRIME = GCD_CANCEL_MULT;
(* val GCD_REDUCE_BY_COPRIME =
   |- !m n k. coprime m k ==> gcd m (k * n) = gcd m n: thm *)

(* ------------------------------------------------------------------------- *)
(* Coprime Theorems (from examples/algebra)                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: coprime n (n + 1) *)
(* Proof:
   Since n < n + 1 ==> n <= n + 1,
     gcd n (n + 1)
   = gcd n (n + 1 - n)      by GCD_SUB_R
   = gcd n 1                by arithmetic
   = 1                      by GCD_1
*)
val coprime_SUC = store_thm(
  "coprime_SUC",
  ``!n. coprime n (n + 1)``,
  rw[GCD_SUB_R]);

(* Theorem: 0 < n ==> coprime n (n - 1) *)
(* Proof:
     gcd n (n - 1)
   = gcd (n - 1) n             by GCD_SYM
   = gcd (n - 1) (n - 1 + 1)   by SUB_ADD, 0 <= n
   = 1                         by coprime_SUC
*)
val coprime_PRE = store_thm(
  "coprime_PRE",
  ``!n. 0 < n ==> coprime n (n - 1)``,
  metis_tac[GCD_SYM, coprime_SUC, DECIDE``!n. 0 < n ==> (n - 1 + 1 = n)``]);

(* Theorem: coprime 0 n ==> n = 1 *)
(* Proof:
   gcd 0 n = n    by GCD_0L
           = 1    by coprime 0 n
*)
val coprime_0L = store_thm(
  "coprime_0L",
  ``!n. coprime 0 n <=> (n = 1)``,
  rw[GCD_0L]);

(* Theorem: coprime n 0 ==> n = 1 *)
(* Proof:
   gcd n 0 = n    by GCD_0L
           = 1    by coprime n 0
*)
val coprime_0R = store_thm(
  "coprime_0R",
  ``!n. coprime n 0 <=> (n = 1)``,
  rw[GCD_0R]);

(* Theorem: (coprime 0 n <=> n = 1) /\ (coprime n 0 <=> n = 1) *)
(* Proof: by coprime_0L, coprime_0R *)
Theorem coprime_0:
  !n. (coprime 0 n <=> n = 1) /\ (coprime n 0 <=> n = 1)
Proof
  simp[coprime_0L, coprime_0R]
QED

(* Theorem: coprime x y = coprime y x *)
(* Proof:
         coprime x y
   means gcd x y = 1
      so gcd y x = 1   by GCD_SYM
    thus coprime y x
*)
val coprime_sym = store_thm(
  "coprime_sym",
  ``!x y. coprime x y = coprime y x``,
  rw[GCD_SYM]);

(* Theorem: coprime k n /\ n <> 1 ==> k <> 0 *)
(* Proof: by coprime_0L *)
val coprime_neq_1 = store_thm(
  "coprime_neq_1",
  ``!n k. coprime k n /\ n <> 1 ==> k <> 0``,
  fs[coprime_0L]);

(* Theorem: coprime k n /\ 1 < n ==> 0 < k *)
(* Proof: by coprime_neq_1 *)
val coprime_gt_1 = store_thm(
  "coprime_gt_1",
  ``!n k. coprime k n /\ 1 < n ==> 0 < k``,
  metis_tac[coprime_neq_1, NOT_ZERO_LT_ZERO, DECIDE``~(1 < 1)``]);

(* Note:  gcd (c ** n) m = gcd c m  is false when n = 0, where c ** 0 = 1. *)

(* Theorem: coprime c m ==> !n. coprime (c ** n) m *)
(* Proof: by induction on n.
   Base case: coprime (c ** 0) m
     Since c ** 0 = 1         by EXP
     and coprime 1 m is true  by GCD_1
   Step case: coprime c m /\ coprime (c ** n) m ==> coprime (c ** SUC n) m
     coprime c m means
     coprime m c              by GCD_SYM

       gcd m (c ** SUC n)
     = gcd m (c * c ** n)     by EXP
     = gcd m (c ** n)         by GCD_CANCEL_MULT, coprime m c
     = 1                      by induction hypothesis
     Hence coprime m (c ** SUC n)
     or coprime (c ** SUC n) m  by GCD_SYM
*)
val coprime_exp = store_thm(
  "coprime_exp",
  ``!c m. coprime c m ==> !n. coprime (c ** n) m``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[EXP, GCD_1] >>
  metis_tac[EXP, GCD_CANCEL_MULT, GCD_SYM]);

(* Theorem: coprime a b ==> !n. coprime a (b ** n) *)
(* Proof: by coprime_exp, GCD_SYM *)
val coprime_exp_comm = store_thm(
  "coprime_exp_comm",
  ``!a b. coprime a b ==> !n. coprime a (b ** n)``,
  metis_tac[coprime_exp, GCD_SYM]);

(* Theorem: coprime x z /\ coprime y z ==> coprime (x * y) z *)
(* Proof:
   By GCD_CANCEL_MULT:
   |- !m n k. coprime m k ==> (gcd m (k * n) = gcd m n)
   Hence follows by coprime_sym.
*)
val coprime_product_coprime = store_thm(
  "coprime_product_coprime",
  ``!x y z. coprime x z /\ coprime y z ==> coprime (x * y) z``,
  metis_tac[GCD_CANCEL_MULT, GCD_SYM]);

(* Theorem: coprime z x /\ coprime z y ==> coprime z (x * y) *)
(* Proof:
   Note gcd z x = 1         by given
    ==> gcd z (x * y)
      = gcd z y             by GCD_CANCEL_MULT
      = 1                   by given
*)
val coprime_product_coprime_sym = store_thm(
  "coprime_product_coprime_sym",
  ``!x y z. coprime z x /\ coprime z y ==> coprime z (x * y)``,
  rw[GCD_CANCEL_MULT]);
(* This is the same as PRODUCT_WITH_GCD_ONE *)

(* Theorem: coprime x z ==> (coprime y z <=> coprime (x * y) z) *)
(* Proof:
   If part: coprime x z /\ coprime y z ==> coprime (x * y) z
      True by coprime_product_coprime
   Only-if part: coprime x z /\ coprime (x * y) z ==> coprime y z
      Let d = gcd y z.
      Then d divides z /\ d divides y     by GCD_PROPERTY
        so d divides (x * y)              by DIVIDES_MULT, MULT_COMM
        or d divides (gcd (x * y) z)      by GCD_PROPERTY
           d divides 1                    by coprime (x * y) z
       ==> d = 1                          by DIVIDES_ONE
        or coprime y z                    by notation
*)
val coprime_product_coprime_iff = store_thm(
  "coprime_product_coprime_iff",
  ``!x y z. coprime x z ==> (coprime y z <=> coprime (x * y) z)``,
  rw[EQ_IMP_THM] >-
  rw[coprime_product_coprime] >>
  qabbrev_tac `d = gcd y z` >>
  metis_tac[GCD_PROPERTY, DIVIDES_MULT, MULT_COMM, DIVIDES_ONE]);

(* Theorem: a divides n /\ b divides n /\ coprime a b ==> (a * b) divides n *)
(* Proof: by LCM_COPRIME, LCM_DIVIDES *)
val coprime_product_divides = store_thm(
  "coprime_product_divides",
  ``!n a b. a divides n /\ b divides n /\ coprime a b ==> (a * b) divides n``,
  metis_tac[LCM_COPRIME, LCM_DIVIDES]);

(* Theorem: 0 < m /\ coprime m n ==> coprime m (n MOD m) *)
(* Proof:
     gcd m n
   = if m = 0 then n else gcd (n MOD m) m    by GCD_EFFICIENTLY
   = gcd (n MOD m) m                         by decide_tac, m <> 0
   = gcd m (n MOD m)                         by GCD_SYM
   Hence true since coprime m n <=> gcd m n = 1.
*)
val coprime_mod = store_thm(
  "coprime_mod",
  ``!m n. 0 < m /\ coprime m n ==> coprime m (n MOD m)``,
  metis_tac[GCD_EFFICIENTLY, GCD_SYM, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < m ==> (coprime m n = coprime m (n MOD m)) *)
(* Proof: by GCD_MOD *)
val coprime_mod_iff = store_thm(
  "coprime_mod_iff",
  ``!m n. 0 < m ==> (coprime m n = coprime m (n MOD m))``,
  rw[Once GCD_MOD]);

(* Theorem: 1 < n /\ coprime n k /\ 1 < p /\ p divides n ==> ~(p divides k) *)
(* Proof:
   First, 1 < n ==> n <> 0 and n <> 1
   If k = 0, gcd n k = n        by GCD_0R
   But coprime n k means gcd n k = 1, so k <> 0.
   By contradiction.
   If p divides k, and given p divides n,
   then p divides gcd n k = 1   by GCD_IS_GREATEST_COMMON_DIVISOR, n <> 0 and k <> 0
   or   p = 1                   by DIVIDES_ONE
   which contradicts 1 < p.
*)
val coprime_factor_not_divides = store_thm(
  "coprime_factor_not_divides",
  ``!n k. 1 < n /\ coprime n k ==> !p. 1 < p /\ p divides n ==> ~(p divides k)``,
  rpt strip_tac >>
  `n <> 0 /\ n <> 1 /\ p <> 1` by decide_tac >>
  metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR, DIVIDES_ONE, GCD_0R]);

(* Theorem: m divides n ==> !k. coprime n k ==> coprime m k *)
(* Proof:
   Let d = gcd m k.
   Then d divides m /\ d divides k    by GCD_IS_GREATEST_COMMON_DIVISOR
    ==> d divides n                   by DIVIDES_TRANS
     so d divides 1                   by GCD_IS_GREATEST_COMMON_DIVISOR, coprime n k
    ==> d = 1                         by DIVIDES_ONE
*)
val coprime_factor_coprime = store_thm(
  "coprime_factor_coprime",
  ``!m n. m divides n ==> !k. coprime n k ==> coprime m k``,
  rpt strip_tac >>
  qabbrev_tac `d = gcd m k` >>
  `d divides m /\ d divides k` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `d divides n` by metis_tac[DIVIDES_TRANS] >>
  `d divides 1` by metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR] >>
  rw[GSYM DIVIDES_ONE]);

(* Idea: common factor of two coprime numbers. *)

(* Theorem: coprime a b /\ c divides a /\ c divides b ==> c = 1 *)
(* Proof:
   Note c divides gcd a b      by GCD_PROPERTY
     or c divides 1            by coprime a b
     so c = 1                  by DIVIDES_ONE
*)
Theorem coprime_common_factor:
  !a b c. coprime a b /\ c divides a /\ c divides b ==> c = 1
Proof
  metis_tac[GCD_PROPERTY, DIVIDES_ONE]
QED

(* Theorem: prime p /\ ~(p divides n) ==> coprime p n *)
(* Proof:
   Since divides p 0, so n <> 0.    by ALL_DIVIDES_0
   If n = 1, certainly coprime p n  by GCD_1
   If n <> 1,
   Let gcd p n = d.
   Since d divides p                by GCD_IS_GREATEST_COMMON_DIVISOR
     and prime p                    by given
      so d = 1 or d = p             by prime_def
     but d <> p                     by divides_iff_gcd_fix
   Hence d = 1, or coprime p n.
*)
val prime_not_divides_coprime = store_thm(
  "prime_not_divides_coprime",
  ``!n p. prime p /\ ~(p divides n) ==> coprime p n``,
  rpt strip_tac >>
  `n <> 0` by metis_tac[ALL_DIVIDES_0] >>
  Cases_on `n = 1` >-
  rw[] >>
  `0 < p` by rw[PRIME_POS] >>
  `p <> 0` by decide_tac >>
  metis_tac[prime_def, divides_iff_gcd_fix, GCD_IS_GREATEST_COMMON_DIVISOR]);

(* Theorem: prime p /\ ~(coprime p n) ==> p divides n *)
(* Proof:
   Let d = gcd p n.
   Then d divides p        by GCD_IS_GREATEST_COMMON_DIVISOR
    ==> d = p              by prime_def
   Thus p divides n        by divides_iff_gcd_fix

   Or: this is just the inverse of prime_not_divides_coprime.
*)
val prime_not_coprime_divides = store_thm(
  "prime_not_coprime_divides",
  ``!n p. prime p /\ ~(coprime p n) ==> p divides n``,
  metis_tac[prime_not_divides_coprime]);

(* Theorem: 1 < n /\ prime p /\ p divides n ==> !k. coprime n k ==> coprime p k *)
(* Proof:
   Since coprime n k /\ p divides n
     ==> ~(p divides k)               by coprime_factor_not_divides
    Then prime p /\ ~(p divides k)
     ==> coprime p k                  by prime_not_divides_coprime
*)
val coprime_prime_factor_coprime = store_thm(
  "coprime_prime_factor_coprime",
  ``!n p. 1 < n /\ prime p /\ p divides n ==> !k. coprime n k ==> coprime p k``,
  metis_tac[coprime_factor_not_divides, prime_not_divides_coprime, ONE_LT_PRIME]);

(* This is better:
coprime_factor_coprime
|- !m n. m divides n ==> !k. coprime n k ==> coprime m k
*)

(* Idea: a characterisation of the coprime property of two numbers. *)

(* Theorem: coprime m n <=> !p. prime p ==> ~(p divides m /\ p divides n) *)
(* Proof:
   If part: coprime m n /\ prime p ==> ~(p divides m) \/ ~(p divides n)
      By contradiction, suppose p divides m /\ p divides n.
      Then p = 1                   by coprime_common_factor
      This contradicts prime p     by NOT_PRIME_1
   Only-if part: !p. prime p ==> ~(p divides m) \/ ~(p divides m) ==> coprime m n
      Let d = gcd m n.
      By contradiction, suppose d <> 1.
      Then ?p. prime p /\ p divides d    by PRIME_FACTOR, d <> 1.
       Now d divides m /\ d divides n    by GCD_PROPERTY
        so p divides m /\ p divides n    by DIVIDES_TRANS
      This contradicts the assumption.
*)
Theorem coprime_by_prime_factor:
  !m n. coprime m n <=> !p. prime p ==> ~(p divides m /\ p divides n)
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[coprime_common_factor, NOT_PRIME_1] >>
  qabbrev_tac `d = gcd m n` >>
  spose_not_then strip_assume_tac >>
  `?p. prime p /\ p divides d` by rw[PRIME_FACTOR] >>
  `d divides m /\ d divides n` by metis_tac[GCD_PROPERTY] >>
  metis_tac[DIVIDES_TRANS]
QED

(* Idea: coprime_by_prime_factor with reduced testing of primes, useful in practice. *)

(* Theorem: 0 < m /\ 0 < n ==>
           (coprime m n <=>
           !p. prime p /\ p <= m /\ p <= n ==> ~(p divides m /\ p divides n)) *)
(* Proof:
   If part: coprime m n /\ prime p /\ ... ==> ~(p divides m) \/ ~(p divides n)
      By contradiction, suppose p divides m /\ p divides n.
      Then p = 1                   by coprime_common_factor
      This contradicts prime p     by NOT_PRIME_1
   Only-if part: !p. prime p /\ p <= m /\ p <= n ==> ~(p divides m) \/ ~(p divides m) ==> coprime m n
      Let d = gcd m n.
      By contradiction, suppose d <> 1.
      Then ?p. prime p /\ p divides d    by PRIME_FACTOR, d <> 1.
       Now d divides m /\ d divides n    by GCD_PROPERTY
        so p divides m /\ p divides n    by DIVIDES_TRANS
      Thus p <= m /\ p <= n              by DIVIDES_LE, 0 < m, 0 < n
      This contradicts the assumption.
*)
Theorem coprime_by_prime_factor_le:
  !m n. 0 < m /\ 0 < n ==>
        (coprime m n <=>
        !p. prime p /\ p <= m /\ p <= n ==> ~(p divides m /\ p divides n))
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[coprime_common_factor, NOT_PRIME_1] >>
  qabbrev_tac `d = gcd m n` >>
  spose_not_then strip_assume_tac >>
  `?p. prime p /\ p divides d` by rw[PRIME_FACTOR] >>
  `d divides m /\ d divides n` by metis_tac[GCD_PROPERTY] >>
  `0 < p` by rw[PRIME_POS] >>
  metis_tac[DIVIDES_TRANS, DIVIDES_LE]
QED

(* Note: counter-example for converse: gcd 3 11 = 1, but ~(3 divides 10). *)

(* Theorem: 0 < m /\ n divides m ==> coprime n (PRE m) *)
(* Proof:
   Since n divides m
     ==> ?q. m = q * n      by divides_def
    Also 0 < m means m <> 0,
     ==> ?k. m = SUC k      by num_CASES
               = k + 1      by ADD1
      so m - k = 1, k = PRE m.
    Let d = gcd n k.
    Then d divides n /\ d divides k     by GCD_IS_GREATEST_COMMON_DIVISOR
     and d divides n ==> d divides m    by DIVIDES_MULTIPLE, m = q * n
      so d divides (m - k)              by DIVIDES_SUB
      or d divides 1                    by m - k = 1
     ==> d = 1                          by DIVIDES_ONE
*)
val divides_imp_coprime_with_predecessor = store_thm(
  "divides_imp_coprime_with_predecessor",
  ``!m n. 0 < m /\ n divides m ==> coprime n (PRE m)``,
  rpt strip_tac >>
  `?q. m = q * n` by rw[GSYM divides_def] >>
  `m <> 0` by decide_tac >>
  `?k. m = k + 1` by metis_tac[num_CASES, ADD1] >>
  `(k = PRE m) /\ (m - k = 1)` by decide_tac >>
  qabbrev_tac `d = gcd n k` >>
  `d divides n /\ d divides k` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `d divides m` by rw[DIVIDES_MULTIPLE] >>
  `d divides (m - k)` by rw[DIVIDES_SUB] >>
  metis_tac[DIVIDES_ONE]);

(* Theorem: coprime p n ==> (gcd (p * m) n = gcd m n) *)
(* Proof:
   Note coprime p n means coprime n p     by GCD_SYM
     gcd (p * m) n
   = gcd n (p * m)                        by GCD_SYM
   = gcd n p                              by GCD_CANCEL_MULT
*)
val gcd_coprime_cancel = store_thm(
  "gcd_coprime_cancel",
  ``!m n p. coprime p n ==> (gcd (p * m) n = gcd m n)``,
  rw[GCD_CANCEL_MULT, GCD_SYM]);

(* The following is a direct, but tricky, proof of the above result *)

(* Theorem: coprime p n ==> (gcd (p * m) n = gcd m n) *)
(* Proof:
     gcd (p * m) n
   = gcd (p * m) (n * 1)            by MULT_RIGHT_1
   = gcd (p * m) (n * (gcd m 1))    by GCD_1
   = gcd (p * m) (gcd (n * m) n)    by GCD_COMMON_FACTOR
   = gcd (gcd (p * m) (n * m)) n    by GCD_ASSOC
   = gcd (m * (gcd p n)) n          by GCD_COMMON_FACTOR, MULT_COMM
   = gcd (m * 1) n                  by coprime p n
   = gcd m n                        by MULT_RIGHT_1

   Simple proof of GCD_CANCEL_MULT:
   (a*c, b) = (a*c , b*1) = (a * c, b * (c, 1)) = (a * c, b * c, b) = ((a, b) * c, b) = (c, b) since (a,b) = 1.
*)
Theorem gcd_coprime_cancel[allow_rebind]:
  !m n p. coprime p n ==> (gcd (p * m) n = gcd m n)
Proof
  rpt strip_tac >>
  ‘gcd (p * m) n = gcd (p * m) (n * (gcd m 1))’ by rw[GCD_1] >>
  ‘_ = gcd (p * m) (gcd (n * m) n)’ by rw[GSYM GCD_COMMON_FACTOR] >>
  ‘_ = gcd (gcd (p * m) (n * m)) n’ by rw[GCD_ASSOC] >>
  ‘_ = gcd m n’ by rw[GCD_COMMON_FACTOR, MULT_COMM] >>
  rw[]
QED

(* Theorem: prime p /\ prime q /\ p <> q ==> coprime p q *)
(* Proof:
   Let d = gcd p q.
   By contradiction, suppose d <> 1.
   Then d divides p /\ d divides q   by GCD_PROPERTY
     so d = 1 or d = p               by prime_def
    and d = 1 or d = q               by prime_def
    But p <> q                       by given
     so d = 1, contradicts d <> 1.
*)
val primes_coprime = store_thm(
  "primes_coprime",
  ``!p q. prime p /\ prime q /\ p <> q ==> coprime p q``,
  spose_not_then strip_assume_tac >>
  qabbrev_tac `d = gcd p q` >>
  `d divides p /\ d divides q` by metis_tac[GCD_PROPERTY] >>
  metis_tac[prime_def]);

(* Theorem: prime p ==> p cannot divide k! for p > k.
            prime p /\ k < p ==> ~(p divides (FACT k)) *)
(* Proof:
   Since all terms of k! are less than p, and p has only 1 and p as factor.
   By contradiction, and induction on k.
   Base case: prime p ==> 0 < p ==> p divides (FACT 0) ==> F
     Since FACT 0 = 1              by FACT
       and p divides 1 <=> p = 1   by DIVIDES_ONE
       but prime p ==> 1 < p       by ONE_LT_PRIME
       so this is a contradiction.
   Step case: prime p /\ k < p ==> p divides (FACT k) ==> F ==>
              SUC k < p ==> p divides (FACT (SUC k)) ==> F
     Since FACT (SUC k) = SUC k * FACT k    by FACT
       and prime p /\ p divides (FACT (SUC k))
       ==> p divides (SUC k),
        or p divides (FACT k)               by P_EUCLIDES
     But SUC k < p, so ~(p divides (SUC k)) by NOT_LT_DIVIDES
     Hence p divides (FACT k) ==> F         by induction hypothesis
*)
val PRIME_BIG_NOT_DIVIDES_FACT = store_thm(
  "PRIME_BIG_NOT_DIVIDES_FACT",
  ``!p k. prime p /\ k < p ==> ~(p divides (FACT k))``,
  (spose_not_then strip_assume_tac) >>
  Induct_on `k` >| [
    rw[FACT] >>
    metis_tac[ONE_LT_PRIME, LESS_NOT_EQ],
    rw[FACT] >>
    (spose_not_then strip_assume_tac) >>
    `k < p /\ 0 < SUC k` by decide_tac >>
    metis_tac[P_EUCLIDES, NOT_LT_DIVIDES]
  ]);

(* Theorem: n divides m ==> coprime n (SUC m) *)
(* Proof:
   If n = 0,
     then m = 0      by ZERO_DIVIDES
     gcd 0 (SUC 0)
   = SUC 0           by GCD_0L
   = 1               by ONE
   If n = 1,
      gcd 1 (SUC m) = 1      by GCD_1
   If n <> 0,
     gcd n (SUC m)
   = gcd ((SUC m) MOD n) n   by GCD_EFFICIENTLY
   = gcd 1 n                 by n divides m
   = 1                       by GCD_1
*)
val divides_imp_coprime_with_successor = store_thm(
  "divides_imp_coprime_with_successor",
  ``!m n. n divides m ==> coprime n (SUC m)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[GSYM ZERO_DIVIDES] >>
  Cases_on `n = 1` >-
  rw[] >>
  `0 < n /\ 1 < n` by decide_tac >>
  `m MOD n = 0` by rw[GSYM DIVIDES_MOD_0] >>
  `(SUC m) MOD n = (m + 1) MOD n` by rw[ADD1] >>
  `_ = (m MOD n + 1 MOD n) MOD n` by rw[MOD_PLUS] >>
  `_ = (0 + 1) MOD n` by rw[ONE_MOD] >>
  `_ = 1` by rw[ONE_MOD] >>
  metis_tac[GCD_EFFICIENTLY, GCD_1]);

(* ------------------------------------------------------------------------- *)
(* Consequences of Coprime.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: If 1 < n, !x. coprime n x ==> 0 < x /\ 0 < x MOD n *)
(* Proof:
   If x = 0, gcd n x = n. But n <> 1, hence x <> 0, or 0 < x.
   x MOD n = 0 ==> x a multiple of n ==> gcd n x = n <> 1  if n <> 1.
   Hence if 1 < n, coprime n x ==> x MOD n <> 0, or 0 < x MOD n.
*)
val MOD_NONZERO_WHEN_GCD_ONE = store_thm(
  "MOD_NONZERO_WHEN_GCD_ONE",
  ``!n. 1 < n ==> !x. coprime n x ==> 0 < x /\ 0 < x MOD n``,
  ntac 4 strip_tac >>
  conj_asm1_tac >| [
    `1 <> n` by decide_tac >>
    `x <> 0` by metis_tac[GCD_0R] >>
    decide_tac,
    `1 <> n /\ x <> 0` by decide_tac >>
    `?k q. k * x = q * n + 1` by metis_tac[LINEAR_GCD] >>
    `(k*x) MOD n = 1` by rw_tac std_ss[MOD_MULT] >>
    spose_not_then strip_assume_tac >>
    `(x MOD n = 0) /\ 0 < n /\ 1 <> 0` by decide_tac >>
    metis_tac[MOD_MULTIPLE_ZERO, MULT_COMM]
  ]);

(* Theorem: If 1 < n, coprime n x ==> ?k. ((k * x) MOD n = 1) /\ coprime n k *)
(* Proof:
       gcd n x = 1 ==> x <> 0               by GCD_0R
   Also,
       gcd n x = 1
   ==> ?k q. k * x = q * n + 1              by LINEAR_GCD
   ==> (k * x) MOD n = (q * n + 1) MOD n    by arithmetic
   ==> (k * x) MOD n = 1                    by MOD_MULT, 1 < n.

   Let g = gcd n k.
   Since 1 < n, 0 < n.
   Since q * n+1 <> 0, x <> 0, k <> 0, hence 0 < k.
   Hence 0 < g /\ (n MOD g = 0) /\ (k MOD g = 0)    by GCD_DIVIDES.
   Or  n = a * g /\ k = b * g    for some a, b.
   Therefore:
        (b * g) * x = q * (a * g) + 1
        (b * x) * g = (q * a) * g + 1      by arithmetic
   Hence g divides 1, or g = 1     since 0 < g.
*)
val GCD_ONE_PROPERTY = store_thm(
  "GCD_ONE_PROPERTY",
  ``!n x. 1 < n /\ coprime n x ==> ?k. ((k * x) MOD n = 1) /\ coprime n k``,
  rpt strip_tac >>
  `n <> 1` by decide_tac >>
  `x <> 0` by metis_tac[GCD_0R] >>
  `?k q. k * x = q * n + 1` by metis_tac[LINEAR_GCD] >>
  `(k * x) MOD n = 1` by rw_tac std_ss[MOD_MULT] >>
  `?g. g = gcd n k` by rw[] >>
  `n <> 0 /\ q*n + 1 <> 0` by decide_tac >>
  `k <> 0` by metis_tac[MULT_EQ_0] >>
  `0 < g /\ (n MOD g = 0) /\ (k MOD g = 0)` by metis_tac[GCD_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `g divides n /\ g divides k` by rw[DIVIDES_MOD_0] >>
  `g divides (n * q) /\ g divides (k*x)` by rw[DIVIDES_MULT] >>
  `g divides (n * q + 1)` by metis_tac [MULT_COMM] >>
  `g divides 1` by metis_tac[DIVIDES_ADD_2] >>
  metis_tac[DIVIDES_ONE]);

(* Theorem: LCM (k * m) (k * n) = k * LCM m n *)
(* Proof:
   If m = 0 or n = 0, LHS = 0 = RHS.
   If m <> 0 and n <> 0,
     lcm (k * m) (k * n)
   = (k * m) * (k * n) / gcd (k * m) (k * n)    by GCD_LCM
   = (k * m) * (k * n) / k * (gcd m n)          by GCD_COMMON_FACTOR
   = k * m * n / (gcd m n)
   = k * LCM m n                                by GCD_LCM
*)
val LCM_COMMON_FACTOR = store_thm(
  "LCM_COMMON_FACTOR",
  ``!m n k. lcm (k * m) (k * n) = k * lcm m n``,
  rpt strip_tac >>
  `k * (k * (m * n)) = (k * m) * (k * n)` by rw_tac arith_ss[] >>
  `_ = gcd (k * m) (k * n) * lcm (k * m) (k * n) ` by rw[GCD_LCM] >>
  `_ = k * (gcd m n) * lcm (k * m) (k * n)` by rw[GCD_COMMON_FACTOR] >>
  `_ = k * ((gcd m n) * lcm (k * m) (k * n))` by rw_tac arith_ss[] >>
  Cases_on `k = 0` >-
  rw[] >>
  `(gcd m n) * lcm (k * m) (k * n) = k * (m * n)` by metis_tac[MULT_LEFT_CANCEL] >>
  `_ = k * ((gcd m n) * (lcm m n))` by rw_tac std_ss[GCD_LCM] >>
  `_ = (gcd m n) * (k * (lcm m n))` by rw_tac arith_ss[] >>
  Cases_on `n = 0` >-
  rw[] >>
  metis_tac[MULT_LEFT_CANCEL, GCD_EQ_0]);

(* Theorem: coprime a b ==> !c. lcm (a * c) (b * c) = a * b * c *)
(* Proof:
     lcm (a * c) (b * c)
   = lcm (c * a) (c * b)     by MULT_COMM
   = c * (lcm a b)           by LCM_COMMON_FACTOR
   = (lcm a b) * c           by MULT_COMM
   = a * b * c               by LCM_COPRIME
*)
val LCM_COMMON_COPRIME = store_thm(
  "LCM_COMMON_COPRIME",
  ``!a b. coprime a b ==> !c. lcm (a * c) (b * c) = a * b * c``,
  metis_tac[LCM_COMMON_FACTOR, LCM_COPRIME, MULT_COMM]);

(* Theorem: 0 < n /\ m MOD n = 0 ==> gcd m n = n *)
(* Proof:
   Since m MOD n = 0
         ==> n divides m     by DIVIDES_MOD_0
   Hence gcd m n = gcd n m   by GCD_SYM
                 = n         by divides_iff_gcd_fix
*)
val GCD_MULTIPLE = store_thm(
  "GCD_MULTIPLE",
  ``!m n. 0 < n /\ (m MOD n = 0) ==> (gcd m n = n)``,
  metis_tac[DIVIDES_MOD_0, divides_iff_gcd_fix, GCD_SYM]);

(* Theorem: gcd (m * n) n = n *)
(* Proof:
     gcd (m * n) n
   = gcd (n * m) n          by MULT_COMM
   = gcd (n * m) (n * 1)    by MULT_RIGHT_1
   = n * (gcd m 1)          by GCD_COMMON_FACTOR
   = n * 1                  by GCD_1
   = n                      by MULT_RIGHT_1
*)
val GCD_MULTIPLE_ALT = store_thm(
  "GCD_MULTIPLE_ALT",
  ``!m n. gcd (m * n) n = n``,
  rpt strip_tac >>
  `gcd (m * n) n = gcd (n * m) n` by rw[MULT_COMM] >>
  `_ = gcd (n * m) (n * 1)` by rw[] >>
  rw[GCD_COMMON_FACTOR]);

(* ------------------------------------------------------------------------- *)
(* Modulo Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Idea: eliminate modulus n when a MOD n = b MOD n. *)

(* Theorem: 0 < n /\ b <= a ==> (a MOD n = b MOD n <=> ?c. a = b + c * n) *)
(* Proof:
   If part: a MOD n = b MOD n ==> ?c. a = b + c * n
      Note ?c. a = c * n + b MOD n       by MOD_EQN
       and b = (b DIV n) * n + b MOD n   by DIVISION
      Let q = b DIV n,
      Then q * n <= c * n                by LE_ADD_RCANCEL, b <= a
           a
         = c * n + (b - q * n)           by above
         = b + (c * n - q * n)           by arithmetic, q * n <= c * n
         = b + (c - q) * n               by RIGHT_SUB_DISTRIB
      Take (c - q) as c.
   Only-if part: (b + c * n) MOD n = b MOD n
      This is true                       by MOD_TIMES
*)
Theorem MOD_MOD_EQN:
  !n a b. 0 < n /\ b <= a ==> (a MOD n = b MOD n <=> ?c. a = b + c * n)
Proof
  rw[EQ_IMP_THM] >| [
    `?c. a = c * n + b MOD n` by metis_tac[MOD_EQN] >>
    `b = (b DIV n) * n + b MOD n` by rw[DIVISION] >>
    qabbrev_tac `q = b DIV n` >>
    `q * n <= c * n` by metis_tac[LE_ADD_RCANCEL] >>
    `a = b + (c * n - q * n)` by decide_tac >>
    `_ = b + (c - q) * n` by decide_tac >>
    metis_tac[],
    simp[]
  ]
QED

(* Idea: a convenient form of MOD_PLUS. *)

(* Theorem: 0 < n ==> (x + y) MOD n = (x + y MOD n) MOD n *)
(* Proof:
   Let q = y DIV n, r = y MOD n.
   Then y = q * n + r              by DIVISION, 0 < n
        (x + y) MOD n
      = (x + (q * n + r)) MOD n    by above
      = (q * n + (x + r)) MOD n    by arithmetic
      = (x + r) MOD n              by MOD_PLUS, MOD_EQ_0
*)
Theorem MOD_PLUS2:
  !n x y. 0 < n ==> (x + y) MOD n = (x + y MOD n) MOD n
Proof
  rpt strip_tac >>
  `y = (y DIV n) * n + y MOD n` by metis_tac[DIVISION] >>
  simp[]
QED

(* Theorem: If n > 0, a MOD n = b MOD n ==> (a - b) MOD n = 0 *)
(* Proof:
   a = (a DIV n)*n + (a MOD n)   by DIVISION
   b = (b DIV n)*n + (b MOD n)   by DIVISION
   Hence  a - b = ((a DIV n) - (b DIV n))* n
                = a multiple of n
   Therefore (a - b) MOD n = 0.
*)
val MOD_EQ_DIFF = store_thm(
  "MOD_EQ_DIFF",
  ``!n a b. 0 < n /\ (a MOD n = b MOD n) ==> ((a - b) MOD n = 0)``,
  rpt strip_tac >>
  `a = a DIV n * n + a MOD n` by metis_tac[DIVISION] >>
  `b = b DIV n * n + b MOD n` by metis_tac[DIVISION] >>
  `a - b = (a DIV n - b DIV n) * n` by rw_tac arith_ss[] >>
  metis_tac[MOD_EQ_0]);
(* Note: The reverse is true only when a >= b:
         (a-b) MOD n = 0 cannot imply a MOD n = b MOD n *)

(* Theorem: if n > 0, a >= b, then (a - b) MOD n = 0 <=> a MOD n = b MOD n *)
(* Proof:
         (a-b) MOD n = 0
   ==>   n divides (a-b)   by MOD_0_DIVIDES
   ==>   (a-b) = k*n       for some k by divides_def
   ==>       a = b + k*n   need b <= a to apply arithmeticTheory.SUB_ADD
   ==> a MOD n = b MOD n   by arithmeticTheory.MOD_TIMES

   The converse is given by MOD_EQ_DIFF.
*)
val MOD_EQ = store_thm(
  "MOD_EQ",
  ``!n a b. 0 < n /\ b <= a ==> (((a - b) MOD n = 0) <=> (a MOD n = b MOD n))``,
  rw[EQ_IMP_THM] >| [
    `?k. a - b = k * n` by metis_tac[DIVIDES_MOD_0, divides_def] >>
    `a = k*n + b` by rw_tac arith_ss[] >>
    metis_tac[MOD_TIMES],
    metis_tac[MOD_EQ_DIFF]
  ]);

(* Theorem: [Euclid's Lemma] A prime a divides product iff the prime a divides factor.
            [in MOD notation] For prime p, x*y MOD p = 0 <=> x MOD p = 0 or y MOD p = 0 *)
(* Proof:
   The if part is already in P_EUCLIDES:
   !p a b. prime p /\ divides p (a * b) ==> p divides a \/ p divides b
   Convert the divides to MOD by DIVIDES_MOD_0.
   The only-if part is:
   (1) divides p x ==> divides p (x * y)
   (2) divides p y ==> divides p (x * y)
   Both are true by DIVIDES_MULT: !a b c. a divides b ==> a divides (b * c).
   The symmetry of x and y can be taken care of by MULT_COMM.
*)
val EUCLID_LEMMA = store_thm(
  "EUCLID_LEMMA",
  ``!p x y. prime p ==> (((x * y) MOD p = 0) <=> (x MOD p = 0) \/ (y MOD p = 0))``,
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  rw[GSYM DIVIDES_MOD_0, EQ_IMP_THM] >>
  metis_tac[P_EUCLIDES, DIVIDES_MULT, MULT_COMM]);

(* Idea: For prime p, FACT (p-1) MOD p <> 0 *)

(* Theorem: prime p /\ n < p ==> FACT n MOD p <> 0 *)
(* Proof:
   Note 1 < p                  by ONE_LT_PRIME
   By induction on n.
   Base: 0 < p ==> (FACT 0 MOD p = 0) ==> F
      Note FACT 0 = 1          by FACT_0
       and 1 MOD p = 1         by LESS_MOD, 1 < p
       and 1 = 0 is F.
   Step: n < p ==> (FACT n MOD p = 0) ==> F ==>
         SUC n < p ==> (FACT (SUC n) MOD p = 0) ==> F
      If n = 0, SUC 0 = 1      by ONE
         Note FACT 1 = 1       by FACT_1
          and 1 MOD p = 1      by LESS_MOD, 1 < p
          and 1 = 0 is F.
      If n <> 0, 0 < n.
             (FACT (SUC n)) MOD p = 0
         <=> (SUC n * FACT n) MOD p = 0      by FACT
         Note (SUC n) MOD p <> 0             by MOD_LESS, SUC n < p
          and (FACT n) MOD p <> 0            by induction hypothesis
           so (SUC n * FACT n) MOD p <> 0    by EUCLID_LEMMA
         This is a contradiction.
*)
Theorem FACT_MOD_PRIME:
  !p n. prime p /\ n < p ==> FACT n MOD p <> 0
Proof
  rpt strip_tac >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  Induct_on `n` >-
  simp[FACT_0] >>
  Cases_on `n = 0` >-
  simp[FACT_1] >>
  rw[FACT] >>
  `n < p` by decide_tac >>
  `(SUC n) MOD p <> 0` by fs[] >>
  metis_tac[EUCLID_LEMMA]
QED

val _ = export_theory();
