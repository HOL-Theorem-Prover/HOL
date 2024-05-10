open HolKernel Parse boolLib BasicProvers;

open arithmeticTheory dividesTheory pred_setTheory gcdTheory simpLib metisLib
     TotalDefn;

local open numSimps; in end;

val ARITH_ss = numSimps.ARITH_ss;
val arith_ss = srw_ss() ++ ARITH_ss;
val std_ss = arith_ss;

val zDefine =
   Lib.with_flag (computeLib.auto_import_definitions, false) TotalDefn.Define;

fun DECIDE_TAC (g as (asl,_)) =
  ((MAP_EVERY UNDISCH_TAC (filter numSimps.is_arith asl) THEN
    CONV_TAC Arith.ARITH_CONV)
   ORELSE tautLib.TAUT_TAC) g;

val decide_tac = DECIDE_TAC;
val metis_tac = METIS_TAC;
val qabbrev_tac = Q.ABBREV_TAC;
val qexists_tac = Q.EXISTS_TAC;
val rw = SRW_TAC [ARITH_ss];

val _ = new_theory "gcdset";

val gcdset_def = new_definition(
  "gcdset_def",
  ``gcdset s =
      if (s = {}) \/ (s = {0}) then 0
      else MAX_SET ({ n | n <= MIN_SET (s DELETE 0) } INTER
                    { d | !e. e IN s ==> divides d e })``);

val FINITE_LEQ_MIN_SET = prove(
  ``FINITE { n | n <= MIN_SET (s DELETE 0) }``,
  Q_TAC SUFF_TAC `
    { n | n <= MIN_SET (s DELETE 0) } = count (MIN_SET (s DELETE 0) + 1)
  ` THEN1 SRW_TAC [][] THEN
  SRW_TAC [ARITH_ss][EXTENSION]);

val NON_EMPTY_INTERSECTION = prove(
  ``s <> {} /\ s <> {0} ==>
    { n | n <= MIN_SET (s DELETE 0) } INTER
    { d | !e. e IN s ==> divides d e}  <> {}``,
  STRIP_TAC THEN SIMP_TAC (srw_ss()) [EXTENSION] THEN Q.EXISTS_TAC `1` THEN
  SRW_TAC [][] THEN DEEP_INTRO_TAC MIN_SET_ELIM THEN
  SRW_TAC [ARITH_ss][EXTENSION] THEN
  FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN METIS_TAC []);

val gcdset_divides = store_thm(
  "gcdset_divides",
  ``!e. e IN s ==> divides (gcdset s) e``,
  SRW_TAC[][gcdset_def] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  DEEP_INTRO_TAC MAX_SET_ELIM THEN
  ASM_SIMP_TAC (srw_ss()) [FINITE_INTER, FINITE_LEQ_MIN_SET,
                           NON_EMPTY_INTERSECTION]);

val DECIDE = numLib.ARITH_PROVE
val gcdset_greatest = store_thm(
  "gcdset_greatest",
  ``(!e. e IN s ==> divides g e) ==> divides g (gcdset s)``,
  SRW_TAC [][gcdset_def] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  DEEP_INTRO_TAC MAX_SET_ELIM THEN
  ASM_SIMP_TAC (srw_ss()) [NON_EMPTY_INTERSECTION, FINITE_LEQ_MIN_SET] THEN
  Q.X_GEN_TAC `m` THEN REPEAT STRIP_TAC THEN
  Q.ABBREV_TAC `L = lcm g m` THEN
  `(!e. e IN s ==> divides L e) /\ divides m L /\ divides g L`
    by METIS_TAC [gcdTheory.LCM_IS_LEAST_COMMON_MULTIPLE] THEN
  `?x. x IN s /\ x <> 0`
    by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN METIS_TAC []) THEN
  `L <= MIN_SET (s DELETE 0)`
    by (DEEP_INTRO_TAC MIN_SET_ELIM THEN SRW_TAC [][EXTENSION]
          THEN1 METIS_TAC [] THEN
        METIS_TAC [DIVIDES_LE, DECIDE ``x <> 0 <=> 0 < x``]) THEN
  `L <= m` by METIS_TAC[] THEN
  Q_TAC SUFF_TAC `0 < m /\ 0 < g` THEN1
    METIS_TAC [LCM_LE, DECIDE ``x <= y /\ y <= x ==> (x = y)``] THEN
  METIS_TAC [ZERO_DIVIDES, DECIDE ``x <> 0 <=> 0 < x``]);

val gcdset_EMPTY = store_thm(
  "gcdset_EMPTY",
  ``gcdset {} = 0``,
  SRW_TAC [][gcdset_def]);
val _ = export_rewrites ["gcdset_EMPTY"]

val gcdset_INSERT = store_thm(
  "gcdset_INSERT",
  ``gcdset (x INSERT s) = gcd x (gcdset s)``,
  Q.MATCH_ABBREV_TAC `G1 = G2` THEN
  `(!e. e IN s ==> divides G1 e) /\ divides G1 x`
     by METIS_TAC [IN_INSERT, gcdset_divides] THEN
  `divides G2 x /\ divides G2 (gcdset s)`
     by METIS_TAC [GCD_IS_GCD, is_gcd_def] THEN
  MATCH_MP_TAC DIVIDES_ANTISYM THEN CONJ_TAC THENL [
    Q_TAC SUFF_TAC `divides G1 (gcdset s)` THEN1
       METIS_TAC [GCD_IS_GCD, is_gcd_def] THEN
    SRW_TAC [][gcdset_greatest],
    Q_TAC SUFF_TAC `!e. e IN s ==> divides G2 e` THEN1
       METIS_TAC [IN_INSERT, gcdset_greatest] THEN
    METIS_TAC [gcdset_divides, DIVIDES_TRANS]
  ]);
val _ = export_rewrites ["gcdset_INSERT"]

(* ------------------------------------------------------------------------- *)
(* Naturals -- counting from 1 rather than 0, and inclusive.                 *)
(* ------------------------------------------------------------------------- *)

(* Overload the set of natural numbers (like count) *)
val _ = overload_on("natural", ``\n. IMAGE SUC (count n)``);

(* Theorem: j IN (natural n) <=> 0 < j /\ j <= n *)
(* Proof:
   Note j <> 0                     by natural_not_0
       j IN (natural n)
   ==> j IN IMAGE SUC (count n)    by notation
   ==> ?x. x < n /\ (j = SUC x)    by IN_IMAGE
   Since SUC x <> 0                by numTheory.NOT_SUC
   Hence j <> 0,
     and x  < n ==> SUC x < SUC n  by LESS_MONO_EQ
      or j < SUC n                 by above, j = SUC x
    thus j <= n                    by prim_recTheory.LESS_THM
*)
val natural_element = store_thm(
  "natural_element",
  ``!n j. j IN (natural n) <=> 0 < j /\ j <= n``,
  rw[EQ_IMP_THM] >>
  `j <> 0` by decide_tac >>
  `?m. j = SUC m` by metis_tac[num_CASES] >>
  `m < n` by decide_tac >>
  metis_tac[]);

(* Theorem: natural n = {j| 0 < j /\ j <= n} *)
(* Proof: by natural_element, IN_IMAGE *)
val natural_property = store_thm(
  "natural_property",
  ``!n. natural n = {j| 0 < j /\ j <= n}``,
  rw[EXTENSION, natural_element]);

(* Theorem: FINITE (natural n) *)
(* Proof: FINITE_COUNT, IMAGE_FINITE *)
val natural_finite = store_thm(
  "natural_finite",
  ``!n. FINITE (natural n)``,
  rw[]);

(* Theorem: CARD (natural n) = n *)
(* Proof:
     CARD (natural n)
   = CARD (IMAGE SUC (count n))  by notation
   = CARD (count n)              by CARD_IMAGE_SUC
   = n                           by CARD_COUNT
*)
val natural_card = store_thm(
  "natural_card",
  ``!n. CARD (natural n) = n``,
  rw[CARD_IMAGE_SUC]);

(* Theorem: 0 NOTIN (natural n) *)
(* Proof: by NOT_SUC *)
val natural_not_0 = store_thm(
  "natural_not_0",
  ``!n. 0 NOTIN (natural n)``,
  rw[]);

(* Theorem: natural 0 = {} *)
(* Proof:
     natural 0
   = IMAGE SUC (count 0)    by notation
   = IMAGE SUC {}           by COUNT_ZERO
   = {}                     by IMAGE_EMPTY
*)
val natural_0 = store_thm(
  "natural_0",
  ``natural 0 = {}``,
  rw[]);

(* Theorem: natural 1 = {1} *)
(* Proof:
     natural 1
   = IMAGE SUC (count 1)    by notation
   = IMAGE SUC {0}          by count_add1
   = {SUC 0}                by IMAGE_DEF
   = {1}                    by ONE
*)
val natural_1 = store_thm(
  "natural_1",
  ``natural 1 = {1}``,
  rw[EXTENSION, EQ_IMP_THM]);

(* Theorem: 0 < n ==> 1 IN (natural n) *)
(* Proof: by natural_element, LESS_OR, ONE *)
val natural_has_1 = store_thm(
  "natural_has_1",
  ``!n. 0 < n ==> 1 IN (natural n)``,
  rw[natural_element]);

(* Theorem: 0 < n ==> n IN (natural n) *)
(* Proof: by natural_element *)
val natural_has_last = store_thm(
  "natural_has_last",
  ``!n. 0 < n ==> n IN (natural n)``,
  rw[natural_element]);

(* Theorem: natural (SUC n) = (SUC n) INSERT (natural n) *)
(* Proof:
       natural (SUC n)
   <=> {j | 0 < j /\ j <= (SUC n)}              by natural_property
   <=> {j | 0 < j /\ (j <= n \/ (j = SUC n))}   by LE
   <=> {j | j IN (natural n) \/ (j = SUC n)}    by natural_property
   <=> (SUC n) INSERT (natural n)               by INSERT_DEF
*)
val natural_suc = store_thm(
  "natural_suc",
  ``!n. natural (SUC n) = (SUC n) INSERT (natural n)``,
  rw[EXTENSION, EQ_IMP_THM]);

(* temporarily make divides an infix *)
val _ = temp_set_fixity "divides" (Infixl 480);

(* Theorem: 0 < n /\ a IN (natural n) /\ b divides a ==> b IN (natural n) *)
(* Proof:
   By natural_element, this is to show:
   (1) 0 < a /\ b divides a ==> 0 < b
       True by divisor_pos
   (2) 0 < a /\ b divides a ==> b <= n
       Since b divides a
         ==> b <= a                     by DIVIDES_LE, 0 < a
         ==> b <= n                     by LESS_EQ_TRANS
*)
val natural_divisor_natural = store_thm(
  "natural_divisor_natural",
  ``!n a b. 0 < n /\ a IN (natural n) /\ b divides a ==> b IN (natural n)``,
  rw[natural_element] >-
  metis_tac[divisor_pos] >>
  metis_tac[DIVIDES_LE, LESS_EQ_TRANS]);

(* Theorem: 0 < n /\ 0 < a /\ b IN (natural n) /\ a divides b ==> (b DIV a) IN (natural n) *)
(* Proof:
   Let c = b DIV a.
   By natural_element, this is to show:
      0 < a /\ 0 < b /\ b <= n /\ a divides b ==> 0 < c /\ c <= n
   Since a divides b ==> b = c * a               by DIVIDES_EQN, 0 < a
      so b = a * c                               by MULT_COMM
      or c divides b                             by divides_def
    Thus 0 < c /\ c <= b                         by divides_pos
      or c <= n                                  by LESS_EQ_TRANS
*)
val natural_cofactor_natural = store_thm(
  "natural_cofactor_natural",
  ``!n a b. 0 < n /\ 0 < a /\ b IN (natural n) /\ a divides b ==> (b DIV a) IN (natural n)``,
  rewrite_tac[natural_element] >>
  ntac 4 strip_tac >>
  qabbrev_tac `c = b DIV a` >>
  `b = c * a` by rw[GSYM DIVIDES_EQN, Abbr`c`] >>
  `c divides b` by metis_tac[divides_def, MULT_COMM] >>
  `0 < c /\ c <= b` by metis_tac[divides_pos] >>
  decide_tac);

(* Theorem: 0 < n /\ a divides n /\ b IN (natural n) /\ a divides b ==> (b DIV a) IN (natural (n DIV a)) *)
(* Proof:
   Let c = b DIV a.
   By natural_element, this is to show:
      0 < n /\ a divides b /\ 0 < b /\ b <= n /\ a divides b ==> 0 < c /\ c <= n DIV a
   Note 0 < a                                    by ZERO_DIVIES, 0 < n
   Since a divides b ==> b = c * a               by DIVIDES_EQN, 0 < a [1]
      or c divides b                             by divides_def, MULT_COMM
    Thus 0 < c, since 0 divides b means b = 0.   by ZERO_DIVIDES, b <> 0
     Now n = (n DIV a) * a                       by DIVIDES_EQN, 0 < a [2]
    With b <= n, c * a <= (n DIV a) * a          by [1], [2]
   Hence c <= n DIV a                            by LE_MULT_RCANCEL, a <> 0
*)
val natural_cofactor_natural_reduced = store_thm(
  "natural_cofactor_natural_reduced",
  ``!n a b. 0 < n /\ a divides n /\
           b IN (natural n) /\ a divides b ==> (b DIV a) IN (natural (n DIV a))``,
  rewrite_tac[natural_element] >>
  ntac 4 strip_tac >>
  qabbrev_tac `c = b DIV a` >>
  `a <> 0` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
  `(b = c * a) /\ (n = (n DIV a) * a)` by rw[GSYM DIVIDES_EQN, Abbr`c`] >>
  `c divides b` by metis_tac[divides_def, MULT_COMM] >>
  `0 < c` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
  metis_tac[LE_MULT_RCANCEL]);

(* ------------------------------------------------------------------------- *)
(* Coprimes                                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define the coprimes set: integers from 1 to n that are coprime to n *)
(*
val coprimes_def = zDefine `
   coprimes n = {j | 0 < j /\ j <= n /\ coprime j n}
`;
*)
(* Note: j <= n ensures that coprimes n is finite. *)
(* Note: 0 < j is only to ensure  coprimes 1 = {1} *)
val coprimes_def = zDefine `
   coprimes n = {j | j IN (natural n) /\ coprime j n}
`;
(* use zDefine as this is not computationally effective. *)

(* Theorem: j IN coprimes n <=> 0 < j /\ j <= n /\ coprime j n *)
(* Proof: by coprimes_def, natural_element *)
val coprimes_element = store_thm(
  "coprimes_element",
  ``!n j. j IN coprimes n <=> 0 < j /\ j <= n /\ coprime j n``,
  (rw[coprimes_def, natural_element] >> metis_tac[]));

(* Theorem: coprimes n = (natural n) INTER {j | coprime j n} *)
(* Proof: by coprimes_def, EXTENSION, IN_INTER *)
val coprimes_alt = store_thm(
  "coprimes_alt[compute]",
  ``!n. coprimes n = (natural n) INTER {j | coprime j n}``,
  rw[coprimes_def, EXTENSION]);
(* This is effective, put in computeLib. *)

(*
> EVAL ``coprimes 10``;
val it = |- coprimes 10 = {9; 7; 3; 1}: thm
*)

(* Theorem: coprimes n SUBSET natural n *)
(* Proof: by coprimes_def, SUBSET_DEF *)
val coprimes_subset = store_thm(
  "coprimes_subset",
  ``!n. coprimes n SUBSET natural n``,
  rw[coprimes_def, SUBSET_DEF]);

(* Theorem: FINITE (coprimes n) *)
(* Proof:
   Since (coprimes n) SUBSET (natural n)   by coprimes_subset
     and !n. FINITE (natural n)            by natural_finite
      so FINITE (coprimes n)               by SUBSET_FINITE
*)
val coprimes_finite = store_thm(
  "coprimes_finite",
  ``!n. FINITE (coprimes n)``,
  metis_tac[coprimes_subset, natural_finite, SUBSET_FINITE]);

(* Theorem: coprimes 0 = {} *)
(* Proof:
   By coprimes_element, 0 < j /\ j <= 0,
   which is impossible, hence empty.
*)
val coprimes_0 = store_thm(
  "coprimes_0",
  ``coprimes 0 = {}``,
  rw[coprimes_element, EXTENSION]);

(* Theorem: coprimes 1 = {1} *)
(* Proof:
   By coprimes_element, 0 < j /\ j <= 1,
   Only possible j is 1, and gcd 1 1 = 1.
 *)
val coprimes_1 = store_thm(
  "coprimes_1",
  ``coprimes 1 = {1}``,
  rw[coprimes_element, EXTENSION]);

(* Theorem: 0 < n ==> 1 IN (coprimes n) *)
(* Proof: by coprimes_element, GCD_1 *)
val coprimes_has_1 = store_thm(
  "coprimes_has_1",
  ``!n. 0 < n ==> 1 IN (coprimes n)``,
  rw[coprimes_element]);

(* Theorem: (coprimes n = {}) <=> (n = 0) *)
(* Proof:
   If part: coprimes n = {} ==> n = 0
      By contradiction.
      Suppose n <> 0, then 0 < n.
      Then 1 IN (coprimes n)    by coprimes_has_1
      hence (coprimes n) <> {}  by MEMBER_NOT_EMPTY
      This contradicts (coprimes n) = {}.
   Only-if part: n = 0 ==> coprimes n = {}
      True by coprimes_0
*)
val coprimes_eq_empty = store_thm(
  "coprimes_eq_empty",
  ``!n. (coprimes n = {}) <=> (n = 0)``,
  rw[EQ_IMP_THM] >-
  metis_tac[coprimes_has_1, MEMBER_NOT_EMPTY, NOT_ZERO_LT_ZERO] >>
  rw[coprimes_0]);

(* Theorem: 0 NOTIN (coprimes n) *)
(* Proof:
   By coprimes_element, 0 < j /\ j <= n,
   Hence j <> 0, or 0 NOTIN (coprimes n)
*)
val coprimes_no_0 = store_thm(
  "coprimes_no_0",
  ``!n. 0 NOTIN (coprimes n)``,
  rw[coprimes_element]);

(* Theorem: 1 < n ==> n NOTIN coprimes n *)
(* Proof:
   By coprimes_element, 0 < j /\ j <= n /\ gcd j n = 1
   If j = n,  1 = gcd j n = gcd n n = n     by GCD_REF
   which is excluded by 1 < n, so j <> n.
*)
val coprimes_without_last = store_thm(
  "coprimes_without_last",
  ``!n. 1 < n ==> n NOTIN coprimes n``,
  rw[coprimes_element]);

(* Theorem: n IN coprimes n <=> (n = 1) *)
(* Proof:
   By coprimes_element, 0 < j /\ j <= n /\ gcd j n = 1
   If n IN coprimes n, 1 = gcd j n = gcd n n = n     by GCD_REF
   If n = 1, 0 < n, n <= n, and gcd n n = n = 1      by GCD_REF
*)
val coprimes_with_last = store_thm(
  "coprimes_with_last",
  ``!n. n IN coprimes n <=> (n = 1)``,
  rw[coprimes_element]);

(* Theorem: 1 < n ==> (n - 1) IN (coprimes n) *)
(* Proof: by coprimes_element, coprime_PRE, GCD_SYM *)
val coprimes_has_last_but_1 = store_thm(
  "coprimes_has_last_but_1",
  ``!n. 1 < n ==> (n - 1) IN (coprimes n)``,
  rpt strip_tac >>
  `0 < n /\ 0 < n - 1` by decide_tac >>
  rw[coprimes_element, coprime_PRE, GCD_SYM]);

(* Theorem: 1 < n ==> !j. j IN coprimes n ==> j < n *)
(* Proof:
   Since j IN coprimes n ==> j <= n    by coprimes_element
   If j = n, then gcd n n = n <> 1     by GCD_REF
   Thus j <> n, or j < n.              or by coprimes_without_last
*)
val coprimes_element_less = store_thm(
  "coprimes_element_less",
  ``!n. 1 < n ==> !j. j IN coprimes n ==> j < n``,
  metis_tac[coprimes_element, coprimes_without_last, LESS_OR_EQ]);

(* Theorem: 1 < n ==> !j. j IN coprimes n <=> j < n /\ coprime j n *)
(* Proof:
   If part: j IN coprimes n ==> j < n /\ coprime j n
      Note 0 < j /\ j <= n /\ coprime j n      by coprimes_element
      By contradiction, suppose n <= j.
      Then j = n, but gcd n n = n <> 1         by GCD_REF
   Only-if part: j < n /\ coprime j n ==> j IN coprimes n
      This is to show:
           0 < j /\ j <= n /\ coprime j n      by coprimes_element
      By contradiction, suppose ~(0 < j).
      Then j = 0, but gcd 0 n = n <> 1         by GCD_0L
*)
val coprimes_element_alt = store_thm(
  "coprimes_element_alt",
  ``!n. 1 < n ==> !j. j IN coprimes n <=> j < n /\ coprime j n``,
  rw[coprimes_element] >>
  `n <> 1` by decide_tac >>
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `j = n` by decide_tac >>
    metis_tac[GCD_REF],
    spose_not_then strip_assume_tac >>
    `j = 0` by decide_tac >>
    metis_tac[GCD_0L]
  ]);

(* Theorem: 1 < n ==> (MAX_SET (coprimes n) = n - 1) *)
(* Proof:
   Let s = coprimes n, m = MAX_SET s.
    Note (n - 1) IN s     by coprimes_has_last_but_1, 1 < n
   Hence s <> {}          by MEMBER_NOT_EMPTY
     and FINITE s         by coprimes_finite
   Since !x. x IN s ==> x < n         by coprimes_element_less, 1 < n
    also !x. x < n ==> x <= (n - 1)   by SUB_LESS_OR
   Therefore MAX_SET s = n - 1        by MAX_SET_TEST
*)
val coprimes_max = store_thm(
  "coprimes_max",
  ``!n. 1 < n ==> (MAX_SET (coprimes n) = n - 1)``,
  rpt strip_tac >>
  qabbrev_tac `s = coprimes n` >>
  `(n - 1) IN s` by rw[coprimes_has_last_but_1, Abbr`s`] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `FINITE s` by rw[coprimes_finite, Abbr`s`] >>
  `!x. x IN s ==> x < n` by rw[coprimes_element_less, Abbr`s`] >>
  `!x. x < n ==> x <= (n - 1)` by decide_tac >>
  metis_tac[MAX_SET_TEST]);

(* ------------------------------------------------------------------------- *)
(* Set GCD as Big Operator                                                   *)
(* ------------------------------------------------------------------------- *)

(* Big Operators:
SUM_IMAGE_DEF   |- !f s. SIGMA f s = ITSET (\e acc. f e + acc) s 0: thm
PROD_IMAGE_DEF  |- !f s. PI f s = ITSET (\e acc. f e * acc) s 1: thm
*)

(* Define big_gcd for a set *)
val big_gcd_def = Define`
    big_gcd s = ITSET gcd s 0
`;

(* Theorem: big_gcd {} = 0 *)
(* Proof:
     big_gcd {}
   = ITSET gcd {} 0    by big_gcd_def
   = 0                 by ITSET_EMPTY
*)
val big_gcd_empty = store_thm(
  "big_gcd_empty",
  ``big_gcd {} = 0``,
  rw[big_gcd_def, ITSET_EMPTY]);

(* Theorem: big_gcd {x} = x *)
(* Proof:
     big_gcd {x}
   = ITSET gcd {x} 0    by big_gcd_def
   = gcd x 0            by ITSET_SING
   = x                  by GCD_0R
*)
val big_gcd_sing = store_thm(
  "big_gcd_sing",
  ``!x. big_gcd {x} = x``,
  rw[big_gcd_def, ITSET_SING]);

(* Theorem: FINITE s /\ x NOTIN s ==> (big_gcd (x INSERT s) = gcd x (big_gcd s)) *)
(* Proof:
   Note big_gcd s = ITSET gcd s 0                   by big_lcm_def
   Since !x y z. gcd x (gcd y z) = gcd y (gcd x z)  by GCD_ASSOC_COMM
   The result follows                               by ITSET_REDUCTION
*)
val big_gcd_reduction = store_thm(
  "big_gcd_reduction",
  ``!s x. FINITE s /\ x NOTIN s ==> (big_gcd (x INSERT s) = gcd x (big_gcd s))``,
  rw[big_gcd_def, ITSET_REDUCTION, GCD_ASSOC_COMM]);

(* Theorem: FINITE s ==> !x. x IN s ==> (big_gcd s) divides x *)
(* Proof:
   By finite induction on s.
   Base: x IN {} ==> big_gcd {} divides x
      True since x IN {} = F                           by MEMBER_NOT_EMPTY
   Step: !x. x IN s ==> big_gcd s divides x ==>
         e NOTIN s /\ x IN (e INSERT s) ==> big_gcd (e INSERT s) divides x
      Since e NOTIN s,
         so big_gcd (e INSERT s) = gcd e (big_gcd s)   by big_gcd_reduction
      By IN_INSERT,
      If x = e,
         to show: gcd e (big_gcd s) divides e, true    by GCD_IS_GREATEST_COMMON_DIVISOR
      If x <> e, x IN s,
         to show gcd e (big_gcd s) divides x,
         Since (big_gcd s) divides x                   by induction hypothesis, x IN s
           and (big_gcd s) divides gcd e (big_gcd s)   by GCD_IS_GREATEST_COMMON_DIVISOR
            so gcd e (big_gcd s) divides x             by DIVIDES_TRANS
*)
val big_gcd_is_common_divisor = store_thm(
  "big_gcd_is_common_divisor",
  ``!s. FINITE s ==> !x. x IN s ==> (big_gcd s) divides x``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  metis_tac[MEMBER_NOT_EMPTY] >>
  metis_tac[big_gcd_reduction, IN_INSERT, GCD_IS_GREATEST_COMMON_DIVISOR, DIVIDES_TRANS]);

(* Theorem: FINITE s ==> !m. (!x. x IN s ==> m divides x) ==> m divides (big_gcd s) *)
(* Proof:
   By finite induction on s.
   Base: m divides big_gcd {}
      Since big_gcd {} = 0                        by big_gcd_empty
      Hence true                                  by ALL_DIVIDES_0
   Step: !m. (!x. x IN s ==> m divides x) ==> m divides big_gcd s ==>
         e NOTIN s /\ !x. x IN e INSERT s ==> m divides x ==> m divides big_gcd (e INSERT s)
      Note x IN e INSERT s ==> x = e \/ x IN s    by IN_INSERT
      Put x = e, then m divides e                 by x divides m, x = e
      Put x IN s, then m divides big_gcd s        by induction hypothesis
      Therefore, m divides gcd e (big_gcd s)      by GCD_IS_GREATEST_COMMON_DIVISOR
             or  m divides big_gcd (e INSERT s)   by big_gcd_reduction, e NOTIN s
*)
val big_gcd_is_greatest_common_divisor = store_thm(
  "big_gcd_is_greatest_common_divisor",
  ``!s. FINITE s ==> !m. (!x. x IN s ==> m divides x) ==> m divides (big_gcd s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[big_gcd_empty] >>
  metis_tac[big_gcd_reduction, GCD_IS_GREATEST_COMMON_DIVISOR, IN_INSERT]);

(* Theorem: FINITE s ==> !x. big_gcd (x INSERT s) = gcd x (big_gcd s) *)
(* Proof:
   If x IN s,
      Then (big_gcd s) divides x          by big_gcd_is_common_divisor
           gcd x (big_gcd s)
         = gcd (big_gcd s) x              by GCD_SYM
         = big_gcd s                      by divides_iff_gcd_fix
         = big_gcd (x INSERT s)           by ABSORPTION
   If x NOTIN s, result is true           by big_gcd_reduction
*)
val big_gcd_insert = store_thm(
  "big_gcd_insert",
  ``!s. FINITE s ==> !x. big_gcd (x INSERT s) = gcd x (big_gcd s)``,
  rpt strip_tac >>
  Cases_on `x IN s` >-
  metis_tac[big_gcd_is_common_divisor, divides_iff_gcd_fix, ABSORPTION, GCD_SYM] >>
  rw[big_gcd_reduction]);

(* Theorem: big_gcd {x; y} = gcd x y *)
(* Proof:
     big_gcd {x; y}
   = big_gcd (x INSERT y)          by notation
   = gcd x (big_gcd {y})           by big_gcd_insert
   = gcd x (big_gcd {y INSERT {}}) by notation
   = gcd x (gcd y (big_gcd {}))    by big_gcd_insert
   = gcd x (gcd y 0)               by big_gcd_empty
   = gcd x y                       by gcd_0R
*)
val big_gcd_two = store_thm(
  "big_gcd_two",
  ``!x y. big_gcd {x; y} = gcd x y``,
  rw[big_gcd_insert, big_gcd_empty]);

(* Theorem: FINITE s ==> (!x. x IN s ==> 0 < x) ==> 0 < big_gcd s *)
(* Proof:
   By finite induction on s.
   Base: {} <> {} /\ !x. x IN {} ==> 0 < x ==> 0 < big_gcd {}
      True since {} <> {} = F
   Step: s <> {} /\ (!x. x IN s ==> 0 < x) ==> 0 < big_gcd s ==>
         e NOTIN s /\ e INSERT s <> {} /\ !x. x IN e INSERT s ==> 0 < x ==> 0 < big_gcd (e INSERT s)
      Note 0 < e /\ !x. x IN s ==> 0 < x   by IN_INSERT
      If s = {},
           big_gcd (e INSERT {})
         = big_gcd {e}                     by IN_INSERT
         = e > 0                           by big_gcd_sing
      If s <> {},
        so 0 < big_gcd s                   by induction hypothesis
       ==> 0 < gcd e (big_gcd s)           by GCD_EQ_0
        or 0 < big_gcd (e INSERT s)        by big_gcd_insert
*)
val big_gcd_positive = store_thm(
  "big_gcd_positive",
  ``!s. FINITE s /\ s <> {} /\ (!x. x IN s ==> 0 < x) ==> 0 < big_gcd s``,
  `!s. FINITE s ==> s <> {} /\ (!x. x IN s ==> 0 < x) ==> 0 < big_gcd s` suffices_by rw[] >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[] >>
  `0 < e /\ (!x. x IN s ==> 0 < x)` by rw[] >>
  Cases_on `s = {}` >-
  rw[big_gcd_sing] >>
  metis_tac[big_gcd_insert, GCD_EQ_0, NOT_ZERO_LT_ZERO]);

(* Theorem: FINITE s /\ s <> {} ==> !k. big_gcd (IMAGE ($* k) s) = k * big_gcd s *)
(* Proof:
   By finite induction on s.
   Base: {} <> {} ==> ..., must be true.
   Step: s <> {} ==> !!k. big_gcd (IMAGE ($* k) s) = k * big_gcd s ==>
         e NOTIN s ==> big_gcd (IMAGE ($* k) (e INSERT s)) = k * big_gcd (e INSERT s)
      If s = {},
         big_gcd (IMAGE ($* k) (e INSERT {}))
       = big_gcd (IMAGE ($* k) {e})        by IN_INSERT, s = {}
       = big_gcd {k * e}                   by IMAGE_SING
       = k * e                             by big_gcd_sing
       = k * big_gcd {e}                   by big_gcd_sing
       = k * big_gcd (e INSERT {})         by IN_INSERT, s = {}
     If s <> {},
         big_gcd (IMAGE ($* k) (e INSERT s))
       = big_gcd ((k * e) INSERT (IMAGE ($* k) s))   by IMAGE_INSERT
       = gcd (k * e) (big_gcd (IMAGE ($* k) s))      by big_gcd_insert
       = gcd (k * e) (k * big_gcd s)                 by induction hypothesis
       = k * gcd e (big_gcd s)                       by GCD_COMMON_FACTOR
       = k * big_gcd (e INSERT s)                    by big_gcd_insert
*)
val big_gcd_map_times = store_thm(
  "big_gcd_map_times",
  ``!s. FINITE s /\ s <> {} ==> !k. big_gcd (IMAGE ($* k) s) = k * big_gcd s``,
  `!s. FINITE s ==> s <> {} ==> !k. big_gcd (IMAGE ($* k) s) = k * big_gcd s` suffices_by rw[] >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[] >>
  Cases_on `s = {}` >-
  rw[big_gcd_sing] >>
  `big_gcd (IMAGE ($* k) (e INSERT s)) = gcd (k * e) (k * big_gcd s)` by rw[big_gcd_insert] >>
  `_ = k * gcd e (big_gcd s)` by rw[GCD_COMMON_FACTOR] >>
  `_ = k * big_gcd (e INSERT s)` by rw[big_gcd_insert] >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* Set LCM as Big Operator                                                   *)
(* ------------------------------------------------------------------------- *)

(* big_lcm s = ITSET (\e x. lcm e x) s 1 = ITSET lcm s 1, of course! *)
val big_lcm_def = Define`
    big_lcm s = ITSET lcm s 1
`;

(* Theorem: big_lcm {} = 1 *)
(* Proof:
     big_lcm {}
   = ITSET lcm {} 1     by big_lcm_def
   = 1                  by ITSET_EMPTY
*)
val big_lcm_empty = store_thm(
  "big_lcm_empty",
  ``big_lcm {} = 1``,
  rw[big_lcm_def, ITSET_EMPTY]);

(* Theorem: big_lcm {x} = x *)
(* Proof:
     big_lcm {x}
   = ITSET lcm {x} 1     by big_lcm_def
   = lcm x 1             by ITSET_SING
   = x                   by LCM_1
*)
val big_lcm_sing = store_thm(
  "big_lcm_sing",
  ``!x. big_lcm {x} = x``,
  rw[big_lcm_def, ITSET_SING]);

(* Theorem: FINITE s /\ x NOTIN s ==> (big_lcm (x INSERT s) = lcm x (big_lcm s)) *)
(* Proof:
   Note big_lcm s = ITSET lcm s 1                   by big_lcm_def
   Since !x y z. lcm x (lcm y z) = lcm y (lcm x z)  by LCM_ASSOC_COMM
   The result follows                               by ITSET_REDUCTION
*)
val big_lcm_reduction = store_thm(
  "big_lcm_reduction",
  ``!s x. FINITE s /\ x NOTIN s ==> (big_lcm (x INSERT s) = lcm x (big_lcm s))``,
  rw[big_lcm_def, ITSET_REDUCTION, LCM_ASSOC_COMM]);

(* Theorem: FINITE s ==> !x. x IN s ==> x divides (big_lcm s) *)
(* Proof:
   By finite induction on s.
   Base: x IN {} ==> x divides big_lcm {}
      True since x IN {} = F                           by MEMBER_NOT_EMPTY
   Step: !x. x IN s ==> x divides big_lcm s ==>
         e NOTIN s /\ x IN (e INSERT s) ==> x divides big_lcm (e INSERT s)
      Since e NOTIN s,
         so big_lcm (e INSERT s) = lcm e (big_lcm s)   by big_lcm_reduction
      By IN_INSERT,
      If x = e,
         to show: e divides lcm e (big_lcm s), true    by LCM_DIVISORS
      If x <> e, x IN s,
         to show x divides lcm e (big_lcm s),
         Since x divides (big_lcm s)                   by induction hypothesis, x IN s
           and (big_lcm s) divides lcm e (big_lcm s)   by LCM_DIVISORS
            so x divides lcm e (big_lcm s)             by DIVIDES_TRANS
*)
val big_lcm_is_common_multiple = store_thm(
  "big_lcm_is_common_multiple",
  ``!s. FINITE s ==> !x. x IN s ==> x divides (big_lcm s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  metis_tac[MEMBER_NOT_EMPTY] >>
  metis_tac[big_lcm_reduction, IN_INSERT, LCM_DIVISORS, DIVIDES_TRANS]);

(* Theorem: FINITE s ==> !m. (!x. x IN s ==> x divides m) ==> (big_lcm s) divides m *)
(* Proof:
   By finite induction on s.
   Base: big_lcm {} divides m
      Since big_lcm {} = 1                        by big_lcm_empty
      Hence true                                  by ONE_DIVIDES_ALL
   Step: !m. (!x. x IN s ==> x divides m) ==> big_lcm s divides m ==>
         e NOTIN s /\ !x. x IN e INSERT s ==> x divides m ==> big_lcm (e INSERT s) divides m
      Note x IN e INSERT s ==> x = e \/ x IN s    by IN_INSERT
      Put x = e, then e divides m                 by x divides m, x = e
      Put x IN s, then big_lcm s divides m        by induction hypothesis
      Therefore, lcm e (big_lcm s) divides m      by LCM_IS_LEAST_COMMON_MULTIPLE
             or  big_lcm (e INSERT s) divides m   by big_lcm_reduction, e NOTIN s
*)
val big_lcm_is_least_common_multiple = store_thm(
  "big_lcm_is_least_common_multiple",
  ``!s. FINITE s ==> !m. (!x. x IN s ==> x divides m) ==> (big_lcm s) divides m``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[big_lcm_empty] >>
  metis_tac[big_lcm_reduction, LCM_IS_LEAST_COMMON_MULTIPLE, IN_INSERT]);

(* Theorem: FINITE s ==> !x. big_lcm (x INSERT s) = lcm x (big_lcm s) *)
(* Proof:
   If x IN s,
      Then x divides (big_lcm s)          by big_lcm_is_common_multiple
           lcm x (big_lcm s)
         = big_lcm s                      by divides_iff_lcm_fix
         = big_lcm (x INSERT s)           by ABSORPTION
   If x NOTIN s, result is true           by big_lcm_reduction
*)
val big_lcm_insert = store_thm(
  "big_lcm_insert",
  ``!s. FINITE s ==> !x. big_lcm (x INSERT s) = lcm x (big_lcm s)``,
  rpt strip_tac >>
  Cases_on `x IN s` >-
  metis_tac[big_lcm_is_common_multiple, divides_iff_lcm_fix, ABSORPTION] >>
  rw[big_lcm_reduction]);

(* Theorem: big_lcm {x; y} = lcm x y *)
(* Proof:
     big_lcm {x; y}
   = big_lcm (x INSERT y)          by notation
   = lcm x (big_lcm {y})           by big_lcm_insert
   = lcm x (big_lcm {y INSERT {}}) by notation
   = lcm x (lcm y (big_lcm {}))    by big_lcm_insert
   = lcm x (lcm y 1)               by big_lcm_empty
   = lcm x y                       by LCM_1
*)
val big_lcm_two = store_thm(
  "big_lcm_two",
  ``!x y. big_lcm {x; y} = lcm x y``,
  rw[big_lcm_insert, big_lcm_empty]);

(* Theorem: FINITE s ==> (!x. x IN s ==> 0 < x) ==> 0 < big_lcm s *)
(* Proof:
   By finite induction on s.
   Base: !x. x IN {} ==> 0 < x ==> 0 < big_lcm {}
      big_lcm {} = 1 > 0     by big_lcm_empty
   Step: (!x. x IN s ==> 0 < x) ==> 0 < big_lcm s ==>
         e NOTIN s /\ !x. x IN e INSERT s ==> 0 < x ==> 0 < big_lcm (e INSERT s)
      Note 0 < e /\ !x. x IN s ==> 0 < x   by IN_INSERT
        so 0 < big_lcm s                   by induction hypothesis
       ==> 0 < lcm e (big_lcm s)           by LCM_EQ_0
        or 0 < big_lcm (e INSERT s)        by big_lcm_insert
*)
val big_lcm_positive = store_thm(
  "big_lcm_positive",
  ``!s. FINITE s ==> (!x. x IN s ==> 0 < x) ==> 0 < big_lcm s``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[big_lcm_empty] >>
  `0 < e /\ (!x. x IN s ==> 0 < x)` by rw[] >>
  metis_tac[big_lcm_insert, LCM_EQ_0, NOT_ZERO_LT_ZERO]);

(* Theorem: FINITE s /\ s <> {} ==> !k. big_lcm (IMAGE ($* k) s) = k * big_lcm s *)
(* Proof:
   By finite induction on s.
   Base: {} <> {} ==> ..., must be true.
   Step: s <> {} ==> !!k. big_lcm (IMAGE ($* k) s) = k * big_lcm s ==>
         e NOTIN s ==> big_lcm (IMAGE ($* k) (e INSERT s)) = k * big_lcm (e INSERT s)
      If s = {},
         big_lcm (IMAGE ($* k) (e INSERT {}))
       = big_lcm (IMAGE ($* k) {e})        by IN_INSERT, s = {}
       = big_lcm {k * e}                   by IMAGE_SING
       = k * e                             by big_lcm_sing
       = k * big_lcm {e}                   by big_lcm_sing
       = k * big_lcm (e INSERT {})         by IN_INSERT, s = {}
     If s <> {},
         big_lcm (IMAGE ($* k) (e INSERT s))
       = big_lcm ((k * e) INSERT (IMAGE ($* k) s))   by IMAGE_INSERT
       = lcm (k * e) (big_lcm (IMAGE ($* k) s))      by big_lcm_insert
       = lcm (k * e) (k * big_lcm s)                 by induction hypothesis
       = k * lcm e (big_lcm s)                       by LCM_COMMON_FACTOR
       = k * big_lcm (e INSERT s)                    by big_lcm_insert
*)
val big_lcm_map_times = store_thm(
  "big_lcm_map_times",
  ``!s. FINITE s /\ s <> {} ==> !k. big_lcm (IMAGE ($* k) s) = k * big_lcm s``,
  `!s. FINITE s ==> s <> {} ==> !k. big_lcm (IMAGE ($* k) s) = k * big_lcm s` suffices_by rw[] >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[] >>
  Cases_on `s = {}` >-
  rw[big_lcm_sing] >>
  `big_lcm (IMAGE ($* k) (e INSERT s)) = lcm (k * e) (k * big_lcm s)` by rw[big_lcm_insert] >>
  `_ = k * lcm e (big_lcm s)` by rw[LCM_COMMON_FACTOR] >>
  `_ = k * big_lcm (e INSERT s)` by rw[big_lcm_insert] >>
  rw[]);

val _ = export_theory()
