open HolKernel Parse boolLib BasicProvers;

open simpLib computeLib prim_recTheory arithmeticTheory boolSimps
     metisLib numLib TotalDefn;

val CALC = EQT_ELIM o reduceLib.REDUCE_CONV;
val ARITH_TAC = CONV_TAC Arith.ARITH_CONV;
val DECIDE = EQT_ELIM o Arith.ARITH_CONV;

fun DECIDE_TAC (g as (asl,_)) =
  ((MAP_EVERY UNDISCH_TAC (filter numSimps.is_arith asl) THEN
    CONV_TAC Arith.ARITH_CONV)
   ORELSE tautLib.TAUT_TAC) g;

val decide_tac = DECIDE_TAC;
val metis_tac = METIS_TAC;
val arith_ss = numLib.arith_ss;
val rw = srw_tac[];
val qabbrev_tac = Q.ABBREV_TAC;
val qspec_then = Q.SPEC_THEN;

fun simp ths = asm_simp_tac (srw_ss() ++ numSimps.ARITH_ss) ths
fun gvs ths = global_simp_tac {droptrues = true, elimvars = true,
                               oldestfirst = true, strip = true}
                              (srw_ss() ++ numSimps.ARITH_ss) ths

fun fs l = FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) l;

val op >~ = Q.>~

val ARW = RW_TAC arith_ss;

local open numeralTheory in end;
  (* concession to Holmake's flawed dependency analysis, which doesn't
     spot this problem *)

val _ = new_theory "divides";

val divides_def = Q.new_definition
  ("divides_def",
   `divides a b = ?q. b = q*a`);

val ALL_DIVIDES_0 = store_thm
("ALL_DIVIDES_0",
 ``!a. divides a 0``,
 METIS_TAC[divides_def,MULT_CLAUSES])
 before
 export_rewrites ["ALL_DIVIDES_0"];

val ZERO_DIVIDES = store_thm(
  "ZERO_DIVIDES",
  ``divides 0 m = (m = 0)``,
  SRW_TAC [][divides_def])
  before
  export_rewrites ["ZERO_DIVIDES"];

val DIVIDES_REFL = store_thm
("DIVIDES_REFL",
 ``!a. divides a a``,
 METIS_TAC[divides_def,MULT_CLAUSES])
 before
 export_rewrites ["DIVIDES_REFL"];

val DIVIDES_TRANS = store_thm
 ("DIVIDES_TRANS",
  ``!a b c. divides a b /\ divides b c ==> divides a c``,
  METIS_TAC [divides_def,MULT_ASSOC]);

val ONE_DIVIDES_ALL = store_thm
("ONE_DIVIDES_ALL",
 ``!a. divides 1 a``,
 METIS_TAC[divides_def,MULT_CLAUSES])
 before
 export_rewrites ["ONE_DIVIDES_ALL"];

val DIVIDES_ONE = store_thm
 ("DIVIDES_ONE",
  ``!x. divides x 1 = (x = 1)``,
  METIS_TAC [divides_def,MULT_CLAUSES,MULT_EQ_1])
  before
  export_rewrites ["DIVIDES_ONE"];

val DIVIDES_ADD_1 = store_thm
("DIVIDES_ADD_1",
 ``!a b c. divides a b /\ divides a c ==> divides a (b+c)``,
 METIS_TAC[divides_def,RIGHT_ADD_DISTRIB]);

val DIVIDES_ADD_2 = store_thm
("DIVIDES_ADD_2",
 ``!a b c. divides a b /\ divides a (b+c) ==> divides a c``,
 ARW[divides_def] THEN EXISTS_TAC ``q' - q`` THEN ARW[RIGHT_SUB_DISTRIB]);

val DIVIDES_SUB = store_thm
("DIVIDES_SUB",
 ``!a b c. divides a b /\ divides a c ==> divides a (b-c)``,
 METIS_TAC[divides_def,RIGHT_SUB_DISTRIB]);

val DIVIDES_LE = store_thm
("DIVIDES_LE",
 ``!a b. 0<b /\ divides a b ==> a <= b``,
 Cases_on `a` THEN ARW[divides_def] THEN Cases_on `q` THENL
 [METIS_TAC [MULT_CLAUSES,LESS_REFL],
  ARW[MULT_CLAUSES]]);

val DIVIDES_LEQ_OR_ZERO = store_thm
 ("DIVIDES_LEQ_OR_ZERO",
  ``!m n. divides m n ==> m <= n \/ (n = 0)``,
  ARW [divides_def]
     THEN Cases_on `q`
     THEN ARW [MULT_CLAUSES]);

val NOT_LT_DIVIDES = store_thm
("NOT_LT_DIVIDES",
 ``!a b. 0<b /\ b<a ==> ~(divides a b)``,
 METIS_TAC[DIVIDES_LE,LESS_EQ_ANTISYM]);

val DIVIDES_ANTISYM = store_thm
("DIVIDES_ANTISYM",
 ``!a b. divides a b /\ divides b a ==> (a = b)``,
 REPEAT Cases
  THEN TRY (ARW[divides_def] THEN NO_TAC)
  THEN METIS_TAC [LESS_EQUAL_ANTISYM,DIVIDES_LE,prim_recTheory.LESS_0]);

val DIVIDES_MULT = store_thm
("DIVIDES_MULT",
 ``!a b c. divides a b ==> divides a (b*c)``,
  METIS_TAC[divides_def,MULT_SYM,MULT_ASSOC]);

val DIVIDES_MULT_LEFT = store_thm(
  "DIVIDES_MULT_LEFT",
  ``!n m. divides (n * m) m <=> (m = 0) \/ (n = 1)``,
  SIMP_TAC arith_ss [FORALL_AND_THM, EQ_IMP_THM, DISJ_IMP_THM,
                     ALL_DIVIDES_0, DIVIDES_REFL] THEN
  SIMP_TAC bool_ss [divides_def] THEN REPEAT STRIP_TAC THEN
  `m * 1 = m * (n * q)` by
     (POP_ASSUM (CONV_TAC o LAND_CONV o
                 ONCE_REWRITE_CONV o C cons []) THEN
      ASM_SIMP_TAC bool_ss [MULT_CLAUSES] THEN
      CONV_TAC (AC_CONV(MULT_ASSOC, MULT_COMM))) THEN
  `(m = 0) \/ (n * q = 1)` by METIS_TAC [EQ_MULT_LCANCEL] THEN
  ASM_SIMP_TAC bool_ss [] THEN
  METIS_TAC [MULT_EQ_1]);

val DIVIDES_EXP = Q.prove
(`!a b x. 0 < x /\ divides a b ==> divides a (b ** x)`,
 Cases_on `x` THEN RW_TAC arith_ss [EXP] THEN METIS_TAC [DIVIDES_MULT]);

val DIVIDES_FACT = store_thm
("DIVIDES_FACT",
 ``!b. 0<b ==> divides b (FACT b)``,
 Cases_on `b` THEN ARW[FACT, divides_def] THEN METIS_TAC [MULT_COMM]);

Theorem LEQ_DIVIDES_FACT:
  !m n. 0 < m /\ m <= n ==> divides m (FACT n)
Proof
  RW_TAC arith_ss  [LESS_EQ_EXISTS] >>
  Q.RENAME_TAC [‘divides m (FACT (m + d))’] >>
  Induct_on ‘d’ >>
  METIS_TAC [FACT, LESS_REFL, num_CASES, DIVIDES_MULT,
             MULT_COMM, DIVIDES_REFL, ADD_CLAUSES]
QED

(* Idea: a convenient form of divides_def. *)

(* Theorem: n divides (m * n) /\ n divides (n * m) *)
(* Proof: by divides_def. *)
Theorem factor_divides[simp]:
  !m n. divides n (m * n) /\ divides n (n * m)
Proof
  METIS_TAC[divides_def, MULT_COMM]
QED

Theorem EXP_DIVIDES:
  divides (a ** b) (a ** c) <=>
    b <= c \/ a = 0 /\ 0 < c \/ a = 0 /\ b = 0 \/ a = 1
Proof
  SRW_TAC [][divides_def, EQ_IMP_THM] >> simp[] >~
  [‘a ** c = r * a ** b’]
  >- (Cases_on ‘a = 0’ >> gvs[] >> CCONTR_TAC >>
      gvs[NOT_LESS, NOT_LESS_EQUAL] >>
      ‘?d. b = c + d /\ 0 < d’ by (Q.EXISTS_TAC ‘b - c’ >> simp[]) >>
      gvs[EXP_ADD] >>
      ‘a ** c = 0 \/ r * a ** d = 1’
        by (irule $ iffLR EQ_MULT_LCANCEL >> REWRITE_TAC [MULT_RIGHT_1] >>
            Q.PAT_X_ASSUM ‘a ** c = _’ (fn th => CONV_TAC (RHS_CONV (K th))) >>
            simp[]) >>
      gvs[]) >~
  [‘b <= c’]
  >- (gvs[LESS_EQ_EXISTS, EXP_ADD] >> METIS_TAC[MULT_COMM]) >>
  Q.EXISTS_TAC ‘0’ >> simp[]
QED

Theorem DIVIDES_MOD_0:
  !p n. 0 < p ==> (divides p n <=> n MOD p = 0)
Proof
  SRW_TAC[][divides_def, EQ_IMP_THM, PULL_EXISTS] >>
  Q.EXISTS_TAC ‘n DIV p’ >>
  METIS_TAC [ADD_CLAUSES, DIVISION]
QED

Theorem DIVIDES_DIV:
  !p n. 0 < p /\ divides p n ==> p * (n DIV p) = n
Proof
  rpt strip_tac >> drule_then (Q.SPEC_THEN ‘n’ strip_assume_tac) DIVISION >>
  drule_all_then assume_tac DIVIDES_MOD_0 >> gvs[]
QED

Theorem DIVIDES_COMMON_MULT_I:
  !a b c. divides a b ==> divides (c * a) (c * b)
Proof
  SRW_TAC[][divides_def] >> simp[EXISTS_OR_THM]
QED

Theorem DIVIDES_MULT_RCANCEL:
  !a b c. c <> 0 ==> (divides (a * c) (b * c) <=> divides a b)
Proof
  SRW_TAC[][divides_def, EQ_IMP_THM] >> gvs[EXISTS_OR_THM] >>
  ‘b * c = (a * q) * c’ by METIS_TAC[MULT_ASSOC, MULT_COMM] >>
  METIS_TAC[EQ_MULT_RCANCEL]
QED

Theorem DIVIDES_MULT_LCANCEL:
  !a b c. c <> 0 ==> (divides (c * a) (c * b) <=> divides a b)
Proof
  METIS_TAC[MULT_COMM, DIVIDES_MULT_RCANCEL]
QED

Theorem DIVIDES_PROD:
  !a b c d. divides a c /\ divides b d ==> divides (a * b) (c * d)
Proof
  SRW_TAC[][divides_def] >> Q.RENAME_TAC [‘(q1 * a) * (q2 * b)’] >>
  Q.EXISTS_TAC ‘q1 * q2’ >> simp[]
QED

(*---------------------------------------------------------------------------*)
(* Definition and trivial facts about primality.                             *)
(*---------------------------------------------------------------------------*)

val prime_def = Q.new_definition
("prime_def",
 `prime a <=> a <> 1 /\ !b. divides b a ==> (b=a) \/ (b=1)`);


val NOT_PRIME_0 = Q.store_thm
 ("NOT_PRIME_0",
  `~prime 0`,
  ARW [prime_def, ALL_DIVIDES_0])
  before
  export_rewrites ["NOT_PRIME_0"];

val NOT_PRIME_1 = Q.store_thm
 ("NOT_PRIME_1",
  `~prime 1`,
  ARW [prime_def, DIVIDES_LE])
  before
  export_rewrites ["NOT_PRIME_1"];

val PRIME_2 = store_thm
 ("PRIME_2",
  ``prime 2``,
  RW_TAC arith_ss  [prime_def] THEN
  `0 < b /\ b <= 2` by METIS_TAC [DIVIDES_LE, ZERO_DIVIDES,
                                  CALC ``0<2``,NOT_ZERO_LT_ZERO] THEN
  NTAC 2 (POP_ASSUM MP_TAC) THEN ARITH_TAC)
  before
  export_rewrites ["PRIME_2"];

val PRIME_3 = Q.store_thm
("PRIME_3",
 `prime 3`,
  RW_TAC arith_ss  [prime_def] THEN
  `b <= 3` by RW_TAC arith_ss [DIVIDES_LE] THEN
  `(b=0) \/ (b=1) \/ (b=2) \/ (b=3)` by (POP_ASSUM MP_TAC THEN ARITH_TAC) THEN
  RW_TAC arith_ss [] THENL
  [FULL_SIMP_TAC arith_ss [ZERO_DIVIDES],
   FULL_SIMP_TAC arith_ss [divides_def]])
  before
  export_rewrites ["PRIME_3"];

val PRIME_POS = store_thm
 ("PRIME_POS",
  ``!p. prime p ==> 0<p``,
  Cases THEN RW_TAC arith_ss [NOT_PRIME_0]);

val ONE_LT_PRIME = Q.store_thm
("ONE_LT_PRIME",
 `!p. prime p ==> 1 < p`,
 METIS_TAC [NOT_PRIME_0, NOT_PRIME_1,
            DECIDE ``(p=0) \/ (p=1) \/ 1 < p``]);

Theorem prime_divides_only_self:
  !m n. prime m /\ prime n /\ divides m n ==> m=n
Proof
  RW_TAC arith_ss [divides_def] THEN
  `m<>1` by METIS_TAC [NOT_PRIME_0,NOT_PRIME_1] THEN
  SIMP_TAC (srw_ss()) [] THEN
  Q.PAT_X_ASSUM `prime (m*q)` MP_TAC THEN
  RW_TAC arith_ss [prime_def, divides_def, PULL_EXISTS] THEN
  METIS_TAC []
QED

Theorem prime_MULT:
  !n m. prime (n * m) <=>
        ((n <= m ==> (n = 1 /\ prime m)) /\
         (m <= n ==> (m = 1 /\ prime n)))
Proof
  `!m n. m <= n ==> (prime (m * n) <=> m = 1 /\ prime n)`
  suffices_by METIS_TAC[LESS_EQ_CASES, MULT_COMM]
  \\ gen_tac
  \\ Cases_on`m = 0` \\ ASM_SIMP_TAC arith_ss [NOT_PRIME_0]
  \\ RW_TAC arith_ss [EQ_IMP_THM]
  \\ FULL_SIMP_TAC arith_ss [prime_def]
  >- (
    `divides m (m * n)` by METIS_TAC[factor_divides]
    \\ CCONTR_TAC
    \\ `m = m * n` by METIS_TAC[]
    \\ `~(m < m * n)` by DECIDE_TAC
    \\ FULL_SIMP_TAC arith_ss [])
  \\ rpt strip_tac \\ FULL_SIMP_TAC arith_ss []
  \\ Cases_on`b=1` \\ ASM_SIMP_TAC arith_ss []
  \\ `divides b (m * n)` by METIS_TAC[DIVIDES_MULT, MULT_COMM]
  \\ `b = m * n` by METIS_TAC[]
  \\ FULL_SIMP_TAC arith_ss [DIVIDES_MULT_LEFT]
QED

(*---------------------------------------------------------------------------*)
(* Every number has a prime factor, except for 1. The proof proceeds by a    *)
(* complete induction on n, and then considers cases on whether n is prime   *)
(* or not. The first case (n is prime) is trivial. In the second case, there *)
(* must be an x that divides n, and x is not 1 or n. By DIVIDES_LEQ_OR_ZERO, *)
(* n=0 or x <= n. If n=0, then 2 is a prime that divides 0. On the other     *)
(* hand, if x <= n, there are two cases: if x<n then we can use the i.h. and *)
(* by transitivity of divides we are done; otherwise, if x=n, then we have   *)
(* a contradiction with the fact that x is not 1 or n.                       *)
(*                                                                           *)
(* In the following proof, METIS_TAC automatically considers cases on        *)
(* whether n is prime or not.                                                *)
(*---------------------------------------------------------------------------*)

val PRIME_FACTOR = store_thm
 ("PRIME_FACTOR",
  ``!n. ~(n = 1) ==> ?p. prime p /\ divides p n``,
  completeInduct_on `n` THEN
  METIS_TAC [DIVIDES_REFL, prime_def, LESS_OR_EQ, PRIME_2,
             DIVIDES_LEQ_OR_ZERO, DIVIDES_TRANS, ALL_DIVIDES_0]);

(*---------------------------------------------------------------------------*)
(* For every number there is a larger prime.                                    *)
(*---------------------------------------------------------------------------*)

val EUCLID = store_thm
("EUCLID",
 ``!n. ?p. n < p /\ prime p``,
CCONTR_TAC
THEN
   `?n. !p. n < p ==> ~prime p`  by METIS_TAC[]                  THEN
   `~(FACT n + 1 = 1)`           by RW_TAC arith_ss
                                    [FACT_LESS,NOT_ZERO_LT_ZERO] THEN
   `?p. prime p /\
        divides p (FACT n + 1)`  by METIS_TAC [PRIME_FACTOR]     THEN
   `0 < p`                       by METIS_TAC [PRIME_POS]        THEN
   `p <= n`                      by METIS_TAC [NOT_LESS]         THEN
   `divides p (FACT n)`          by METIS_TAC [LEQ_DIVIDES_FACT] THEN
   `divides p 1`                 by METIS_TAC [DIVIDES_ADD_2]    THEN
   `p = 1`                       by METIS_TAC [DIVIDES_ONE]      THEN
   `~prime p`                    by METIS_TAC [NOT_PRIME_1]
);

(*---------------------------------------------------------------------------*)
(* The sequence of primes.                                                   *)
(*---------------------------------------------------------------------------*)

val PRIMES_def = new_recursive_definition
 {name = "PRIMES_def",
  rec_axiom = prim_recTheory.num_Axiom,
  def = ``(PRIMES 0 = 2) /\
          (PRIMES (SUC n) = LEAST p. prime p /\ PRIMES n < p)``};

val primePRIMES = Q.store_thm
("primePRIMES",
 `!n. prime (PRIMES n)`,
 Cases THEN RW_TAC arith_ss [PRIMES_def,PRIME_2] THEN
 LEAST_ELIM_TAC THEN
 RW_TAC bool_ss [] THEN
 METIS_TAC [EUCLID]);

val INFINITE_PRIMES = Q.store_thm
("INFINITE_PRIMES",
 `!n. PRIMES n < PRIMES (SUC n)`,
 RW_TAC arith_ss [PRIMES_def] THEN
 LEAST_ELIM_TAC THEN
 RW_TAC bool_ss [] THEN
 METIS_TAC [EUCLID]);

val LT_PRIMES = Q.store_thm
("LT_PRIMES",
 `!m n. m < n ==> PRIMES m < PRIMES n`,
 Induct_on `n` THEN RW_TAC arith_ss [] THEN
 METIS_TAC [INFINITE_PRIMES,LESS_TRANS,LESS_THM]);

val PRIMES_11 = Q.store_thm
("PRIMES_11",
 `!m n. (PRIMES m = PRIMES n) ==> (m=n)`,
 METIS_TAC [DECIDE ``a < b ==> a<>b``,LT_PRIMES,
            DECIDE `` !m n. m < n \/ (m=n) \/ n < m``]);

val INDEX_LESS_PRIMES = Q.store_thm
("INDEX_LESS_PRIMES",
 `!n. n < PRIMES n`,
 Induct THEN RW_TAC arith_ss [PRIMES_def] THEN
 LEAST_ELIM_TAC THEN CONJ_TAC THENL
 [METIS_TAC [INFINITE_PRIMES,primePRIMES], RW_TAC arith_ss []]);

val EUCLID_PRIMES = Q.store_thm
("EUCLID_PRIMES",
 `!n. ?i. n < PRIMES i`,
 SPOSE_NOT_THEN (MP_TAC o REWRITE_RULE [NOT_LESS]) THEN STRIP_TAC THEN
 METIS_TAC [INDEX_LESS_PRIMES,DECIDE ``a <= b /\ b < a ==> F``]);

val NEXT_LARGER_PRIME = Q.store_thm
("NEXT_LARGER_PRIME",
 `!n. ?i. n < PRIMES i /\ !j. j < i ==> PRIMES j <= n`,
 GEN_TAC THEN METIS_TAC [HO_MATCH_MP WOP (SPEC_ALL EUCLID_PRIMES),NOT_LESS]);

val PRIMES_NO_GAP = Q.store_thm
("PRIMES_NO_GAP",
 `!n p. PRIMES n < p /\ p < PRIMES (SUC n) /\ prime p ==> F`,
 RW_TAC bool_ss [PRIMES_def,GSYM IMP_DISJ_THM] THEN POP_ASSUM MP_TAC THEN
 LEAST_ELIM_TAC THEN METIS_TAC[INFINITE_PRIMES,primePRIMES]);

val PRIMES_ONTO = Q.store_thm
("PRIMES_ONTO",
 `!p. prime p ==> ?i. PRIMES i = p`,
 SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
 STRIP_ASSUME_TAC (Q.SPEC `p` NEXT_LARGER_PRIME) THEN
 Cases_on `i` THENL
 [METIS_TAC [DECIDE``p < 2 <=> (p=0) \/ (p=1)``,
             NOT_PRIME_0,NOT_PRIME_1,PRIME_2,PRIMES_def],
  `PRIMES n < p` by METIS_TAC [DECIDE ``n < SUC n``,LESS_OR_EQ] THEN
  METIS_TAC [PRIMES_NO_GAP]]);

val PRIME_INDEX = Q.store_thm
("PRIME_INDEX",
 `!p. prime p = ?i. p = PRIMES i`,
 METIS_TAC [PRIMES_ONTO,primePRIMES]);

val ONE_LT_PRIMES = Q.store_thm
("ONE_LT_PRIMES",
 `!n. 1 < PRIMES n`,
  METIS_TAC [primePRIMES, NOT_PRIME_0, NOT_PRIME_1,
             DECIDE ``(x=0) \/ (x=1) \/ 1<x``]);

val ZERO_LT_PRIMES = Q.store_thm
("ZERO_LT_PRIMES",
 `!n. 0 < PRIMES n`,
  METIS_TAC [LESS_TRANS, ONE_LT_PRIMES, DECIDE ``0 < 1``]);

(* Theorem: !n. ?p. prime p /\ n < p *)
(* Proof:
   Since ?i. n < PRIMES i   by NEXT_LARGER_PRIME
     and prime (PRIMES i)   by primePRIMES
   Take p = PRIMES i.
*)
val prime_always_bigger = store_thm(
  "prime_always_bigger",
  ``!n. ?p. prime p /\ n < p``,
  metis_tac[NEXT_LARGER_PRIME, primePRIMES]);

(*---------------------------------------------------------------------------*)
(* Directly computable version of divides                                    *)
(*---------------------------------------------------------------------------*)

Theorem compute_divides[compute]:
  !a b. divides a b =
        if a=0 then (b=0)
        else if a=1 then T
        else if b=0 then T
        else b MOD a = 0
Proof
  RW_TAC arith_ss [divides_def]
  THEN EQ_TAC
  THEN RW_TAC arith_ss [] THENL [
    Cases_on ‘q’ THENL [
      RW_TAC arith_ss [],
      ‘0<a’ by RW_TAC arith_ss [] THEN
      METIS_TAC [MOD_MULT, MULT_SYM, ADD_CLAUSES]
    ],
    Q.EXISTS_TAC ‘b’ THEN RW_TAC arith_ss [],
    Q.EXISTS_TAC ‘0’ THEN RW_TAC arith_ss [],
    ‘0<a’ by RW_TAC arith_ss [] THEN
    METIS_TAC [BETA_RULE (Q.SPECL[‘\x. (x = 0)’,‘b’,‘a’] MOD_P),MULT_COMM,
               ADD_CLAUSES]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* DIVIDES Theorems (from examples/algebra)                                  *)
(* ------------------------------------------------------------------------- *)

(* temporarily make divides an infix *)
val _ = temp_set_fixity "divides" (Infixl 480);

(* Theorem: 0 < n ==> ((m DIV n = 0) <=> m < n) *)
(* Proof:
   If part: 0 < n /\ m DIV n = 0 ==> m < n
      Since m = m DIV n * n + m MOD n) /\ (m MOD n < n)   by DIVISION, 0 < n
         so m = 0 * n + m MOD n            by m DIV n = 0
              = 0 + m MOD n                by MULT
              = m MOD n                    by ADD
      Since m MOD n < n, m < n.
   Only-if part: 0 < n /\ m < n ==> m DIV n = 0
      True by LESS_DIV_EQ_ZERO.
*)
val DIV_EQUAL_0 = store_thm(
  "DIV_EQUAL_0",
  ``!m n. 0 < n ==> ((m DIV n = 0) <=> m < n)``,
  rw[EQ_IMP_THM] >-
  metis_tac[DIVISION, MULT, ADD] >>
  rw[LESS_DIV_EQ_ZERO]);
(* This is an improvement of
   arithmeticTheory.DIV_EQ_0 = |- 1 < b ==> (n DIV b = 0 <=> n < b) *)

(* Theorem: 0 < m /\ m <= n ==> 0 < n DIV m *)
(* Proof:
   Note n = (n DIV m) * m + n MOD m /\
        n MDO m < m                            by DIVISION, 0 < m
    ==> n MOD m < n                            by m <= n
   Thus 0 < (n DIV m) * m                      by inequality
     so 0 < n DIV m                            by ZERO_LESS_MULT
*)
Theorem DIV_POS:
  !m n. 0 < m /\ m <= n ==> 0 < n DIV m
Proof
  rpt strip_tac >>
  imp_res_tac (DIVISION |> SPEC_ALL) >>
  first_x_assum (qspec_then `n` strip_assume_tac) >>
  first_x_assum (qspec_then `n` strip_assume_tac) >>
  `0 < (n DIV m) * m` by decide_tac >>
  metis_tac[ZERO_LESS_MULT]
QED

(* Theorem: 0 < z ==> (x DIV z = y DIV z <=> x - x MOD z = y - y MOD z) *)
(* Proof:
   Note x = (x DIV z) * z + x MOD z            by DIVISION
    and y = (y DIV z) * z + y MDO z            by DIVISION
        x DIV z = y DIV z
    <=> (x DIV z) * z = (y DIV z) * z          by EQ_MULT_RCANCEL
    <=> x - x MOD z = y - y MOD z              by arithmetic
*)
Theorem DIV_EQ:
  !x y z. 0 < z ==> (x DIV z = y DIV z <=> x - x MOD z = y - y MOD z)
Proof
  rpt strip_tac >>
  `x = (x DIV z) * z + x MOD z` by simp[DIVISION] >>
  `y = (y DIV z) * z + y MOD z` by simp[DIVISION] >>
  `x DIV z = y DIV z <=> (x DIV z) * z = (y DIV z) * z` by simp[] >>
  decide_tac
QED

(* Theorem: a MOD n + b < n ==> (a + b) DIV n = a DIV n *)
(* Proof:
   Note 0 < n                                  by a MOD n + b < n
     a + b
   = ((a DIV n) * n + a MOD n) + b             by DIVISION, 0 < n
   = (a DIV n) * n + (a MOD n + b)             by ADD_ASSOC

   If a MOD n + b < n,
   Then (a + b) DIV n = a DIV n /\
        (a + b) MOD n = a MOD n + b            by DIVMOD_UNIQ
*)
Theorem ADD_DIV_EQ:
  !n a b. a MOD n + b < n ==> (a + b) DIV n = a DIV n
Proof
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  `a = (a DIV n) * n + a MOD n` by simp[DIVISION] >>
  `a + b = (a DIV n) * n + (a MOD n + b)` by decide_tac >>
  metis_tac[DIVMOD_UNIQ]
QED

(* Theorem: 0 < y /\ x <= y * z ==> x DIV y <= z *)
(* Proof:
             x <= y * z
   ==> x DIV y <= (y * z) DIV y      by DIV_LE_MONOTONE, 0 < y
                = z                  by MULT_TO_DIV
*)
val DIV_LE = store_thm(
  "DIV_LE",
  ``!x y z. 0 < y /\ x <= y * z ==> x DIV y <= z``,
  metis_tac[DIV_LE_MONOTONE, MULT_TO_DIV]);

(* Theorem: 0 < n ==> !x y. (x * n = y) ==> (x = y DIV n) *)
(* Proof:
     x = (x * n + 0) DIV n     by DIV_MULT, 0 < n
       = (x * n) DIV n         by ADD_0
*)
val DIV_SOLVE = store_thm(
  "DIV_SOLVE",
  ``!n. 0 < n ==> !x y. (x * n = y) ==> (x = y DIV n)``,
  metis_tac[DIV_MULT, ADD_0]);

(* Theorem: 0 < n ==> !x y. (n * x = y) ==> (x = y DIV n) *)
(* Proof: by DIV_SOLVE, MULT_COMM *)
val DIV_SOLVE_COMM = store_thm(
  "DIV_SOLVE_COMM",
  ``!n. 0 < n ==> !x y. (n * x = y) ==> (x = y DIV n)``,
  rw[DIV_SOLVE, MULT_TO_DIV]);

(* Theorem: 1 < n ==> (1 DIV n = 0) *)
(* Proof:
   Since  1 = (1 DIV n) * n + (1 MOD n)   by DIVISION, 0 < n.
     and  1 MOD n = 1                     by ONE_MOD, 1 < n.
    thus  (1 DIV n) * n = 0               by arithmetic
      or  1 DIV n = 0  since n <> 0       by MULT_EQ_0
*)
val ONE_DIV = store_thm(
  "ONE_DIV",
  ``!n. 1 < n ==> (1 DIV n = 0)``,
  rpt strip_tac >>
  `0 < n /\ n <> 0` by decide_tac >>
  `1 = (1 DIV n) * n + (1 MOD n)` by rw[DIVISION] >>
  `_ = (1 DIV n) * n + 1` by rw[ONE_MOD] >>
  `(1 DIV n) * n = 0` by decide_tac >>
  metis_tac[MULT_EQ_0]);

(* Theorem: ODD n ==> !m. m divides n ==> ODD m *)
(* Proof:
   Since m divides n
     ==> ?q. n = q * m      by divides_def
   By contradiction, suppose ~ODD m.
   Then EVEN m              by ODD_EVEN
    and EVEN (q * m) = EVEN n    by EVEN_MULT
     or ~ODD n                   by ODD_EVEN
   This contradicts with ODD n.
*)
val DIVIDES_ODD = store_thm(
  "DIVIDES_ODD",
  ``!n. ODD n ==> !m. m divides n ==> ODD m``,
  metis_tac[divides_def, EVEN_MULT, EVEN_ODD]);

(* Note: For EVEN n, m divides n cannot conclude EVEN m.
Example: EVEN 2 or ODD 3 both divides EVEN 6.
*)

(* Theorem: EVEN m ==> !n. m divides n ==> EVEN n*)
(* Proof:
   Since m divides n
     ==> ?q. n = q * m      by divides_def
   Given EVEN m
    Then EVEN (q * m) = n   by EVEN_MULT
*)
val DIVIDES_EVEN = store_thm(
  "DIVIDES_EVEN",
  ``!m. EVEN m ==> !n. m divides n ==> EVEN n``,
  metis_tac[divides_def, EVEN_MULT]);

(* Theorem: EVEN n = 2 divides n *)
(* Proof:
       EVEN n
   <=> n MOD 2 = 0     by EVEN_MOD2
   <=> 2 divides n     by DIVIDES_MOD_0, 0 < 2
*)
val EVEN_ALT = store_thm(
  "EVEN_ALT",
  ``!n. EVEN n = 2 divides n``,
  rw[EVEN_MOD2, DIVIDES_MOD_0]);

(* Theorem: ODD n = ~(2 divides n) *)
(* Proof:
   Note n MOD 2 < 2    by MOD_LESS
    and !x. x < 2 <=> (x = 0) \/ (x = 1)   by arithmetic
       ODD n
   <=> n MOD 2 = 1     by ODD_MOD2
   <=> ~(2 divides n)  by DIVIDES_MOD_0, 0 < 2
   Or,
   ODD n = ~(EVEN n)        by ODD_EVEN
         = ~(2 divides n)   by EVEN_ALT
*)
val ODD_ALT = store_thm(
  "ODD_ALT",
  ``!n. ODD n = ~(2 divides n)``,
  metis_tac[EVEN_ODD, EVEN_ALT]);

(* Theorem: 0 < n ==> !q. (q DIV n) * n <= q *)
(* Proof:
   Since q = (q DIV n) * n + q MOD n  by DIVISION
    Thus     (q DIV n) * n <= q       by discarding remainder
*)
val DIV_MULT_LE = store_thm(
  "DIV_MULT_LE",
  ``!n. 0 < n ==> !q. (q DIV n) * n <= q``,
  rpt strip_tac >>
  `q = (q DIV n) * n + q MOD n` by rw[DIVISION] >>
  decide_tac);

(* Theorem: 0 < n ==> !q. n divides q <=> ((q DIV n) * n = q) *)
(* Proof:
   If part: n divides q ==> q DIV n * n = q
     q = (q DIV n) * n + q MOD n  by DIVISION
       = (q DIV n) * n + 0        by MOD_EQ_0_DIVISOR, divides_def
       = (q DIV n) * n            by ADD_0
   Only-if part: q DIV n * n = q ==> n divides q
     True by divides_def
*)
val DIV_MULT_EQ = store_thm(
  "DIV_MULT_EQ",
  ``!n. 0 < n ==> !q. n divides q <=> ((q DIV n) * n = q)``,
  metis_tac[divides_def, DIVISION, MOD_EQ_0_DIVISOR, ADD_0]);
(* same as DIVIDES_EQN below *)

(* Theorem: 0 < x /\ 0 < y /\ x <= y ==> !n. n DIV y <= n DIV x *)
(* Proof:
   If n DIV y = 0,
      Then 0 <= n DIV x is trivially true.
   If n DIV y <> 0,
     (n DIV y) * x <= (n DIV y) * y        by LE_MULT_LCANCEL, x <= y, n DIV y <> 0
                   <= n                    by DIV_MULT_LE
  Hence        (n DIV y) * x <= n          by LESS_EQ_TRANS
  Then ((n DIV y) * x) DIV x <= n DIV x    by DIV_LE_MONOTONE
  or                 n DIV y <= n DIV x    by MULT_DIV
*)
val DIV_LE_MONOTONE_REVERSE = store_thm(
  "DIV_LE_MONOTONE_REVERSE",
  ``!x y. 0 < x /\ 0 < y /\ x <= y ==> !n. n DIV y <= n DIV x``,
  rpt strip_tac >>
  Cases_on `n DIV y = 0` >-
  decide_tac >>
  `(n DIV y) * x <= (n DIV y) * y` by rw[LE_MULT_LCANCEL] >>
  `(n DIV y) * y <= n` by rw[DIV_MULT_LE] >>
  `(n DIV y) * x <= n` by decide_tac >>
  `((n DIV y) * x) DIV x <= n DIV x` by rw[DIV_LE_MONOTONE] >>
  metis_tac[MULT_DIV]);

(* Theorem: n divides m <=> (m = (m DIV n) * n) *)
(* Proof:
   Since n divides m <=> m MOD n = 0     by DIVIDES_MOD_0
     and m = (m DIV n) * n + (m MOD n)   by DIVISION
   If part: n divides m ==> m = m DIV n * n
      This is true                       by ADD_0
   Only-if part: m = m DIV n * n ==> n divides m
      Since !x y. x + y = x <=> y = 0    by ADD_INV_0
   The result follows.
*)
val DIVIDES_EQN = store_thm(
  "DIVIDES_EQN",
  ``!n. 0 < n ==> !m. n divides m <=> (m = (m DIV n) * n)``,
  metis_tac[DIVISION, DIVIDES_MOD_0, ADD_0, ADD_INV_0]);

(* Theorem: 0 < n ==> !m. n divides m <=> (m = n * (m DIV n)) *)
(* Proof: vy DIVIDES_EQN, MULT_COMM *)
val DIVIDES_EQN_COMM = store_thm(
  "DIVIDES_EQN_COMM",
  ``!n. 0 < n ==> !m. n divides m <=> (m = n * (m DIV n))``,
  rw_tac std_ss[DIVIDES_EQN, MULT_COMM]);

(* Theorem: 0 < n /\ n <= m ==> ((m - n) DIV n = m DIV n - 1) *)
(* Proof:
   Apply DIV_SUB |> GEN_ALL |> SPEC ``1`` |> REWRITE_RULE[MULT_RIGHT_1];
   val it = |- !n m. 0 < n /\ n <= m ==> ((m - n) DIV n = m DIV n - 1): thm
*)
val SUB_DIV = save_thm("SUB_DIV",
    DIV_SUB |> GEN ``n:num`` |> GEN ``m:num`` |> GEN ``q:num`` |> SPEC ``1``
            |> REWRITE_RULE[MULT_RIGHT_1]);
(* val SUB_DIV = |- !m n. 0 < n /\ n <= m ==> ((m - n) DIV n = m DIV n - 1): thm *)

(* Theorem: 0 < n ==> !k m. (m MOD n = 0) ==> ((k * n = m) <=> (k = m DIV n)) *)
(* Proof:
   Note m MOD n = 0
    ==> n divides m            by DIVIDES_MOD_0, 0 < n
    ==> m = (m DIV n) * n      by DIVIDES_EQN, 0 < n
       k * n = m
   <=> k * n = (m DIV n) * n   by above
   <=>     k = (m DIV n)       by EQ_MULT_RCANCEL, n <> 0.
*)
val DIV_EQ_MULT = store_thm(
  "DIV_EQ_MULT",
  ``!n. 0 < n ==> !k m. (m MOD n = 0) ==> ((k * n = m) <=> (k = m DIV n))``,
  rpt strip_tac >>
  `n <> 0` by decide_tac >>
  `m = (m DIV n) * n` by rw[GSYM DIVIDES_EQN, DIVIDES_MOD_0] >>
  metis_tac[EQ_MULT_RCANCEL]);

(* Theorem: 0 < n ==> !k m. (m MOD n = 0) ==> (k * n < m <=> k < m DIV n) *)
(* Proof:
       k * n < m
   <=> k * n < (m DIV n) * n    by DIVIDES_EQN, DIVIDES_MOD_0, 0 < n
   <=>     k < m DIV n          by LT_MULT_RCANCEL, n <> 0
*)
val MULT_LT_DIV = store_thm(
  "MULT_LT_DIV",
  ``!n. 0 < n ==> !k m. (m MOD n = 0) ==> (k * n < m <=> k < m DIV n)``,
  metis_tac[DIVIDES_EQN, DIVIDES_MOD_0, LT_MULT_RCANCEL, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < n ==> !k m. (m MOD n = 0) ==> (m <= n * k <=> m DIV n <= k) *)
(* Proof:
       m <= n * k
   <=> (m DIV n) * n <= n * k   by DIVIDES_EQN, DIVIDES_MOD_0, 0 < n
   <=> (m DIV n) * n <= k * n   by MULT_COMM
   <=>       m DIV n <= k       by LE_MULT_RCANCEL, n <> 0
*)
val LE_MULT_LE_DIV = store_thm(
  "LE_MULT_LE_DIV",
  ``!n. 0 < n ==> !k m. (m MOD n = 0) ==> (m <= n * k <=> m DIV n <= k)``,
  metis_tac[DIVIDES_EQN, DIVIDES_MOD_0, MULT_COMM, LE_MULT_RCANCEL, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < m ==> ((n DIV m = 0) /\ (n MOD m = 0) <=> (n = 0)) *)
(* Proof:
   If part: (n DIV m = 0) /\ (n MOD m = 0) ==> (n = 0)
      Note n DIV m = 0 ==> n < m        by DIV_EQUAL_0
      Thus n MOD m = n                  by LESS_MOD
        or n = 0
   Only-if part: 0 DIV m = 0            by ZERO_DIV
                 0 MOD m = 0            by ZERO_MOD
*)
Theorem DIV_MOD_EQ_0:
  !m n. 0 < m ==> ((n DIV m = 0) /\ (n MOD m = 0) <=> (n = 0))
Proof
  rpt strip_tac >>
  rw[EQ_IMP_THM] >>
  metis_tac[DIV_EQUAL_0, LESS_MOD]
QED

(* Theorem: 0 < n /\ a ** n divides b ==> a divides b *)
(* Proof:
   Note ?k. n = SUC k              by num_CASES, n <> 0
    and ?q. b = q * (a ** n)       by divides_def
              = q * (a * a ** k)   by EXP
              = (q * a ** k) * a   by arithmetic
   Thus a divides b                by divides_def
*)
Theorem EXP_divides : (* was: EXP_DIVIDES *)
    !a b n. 0 < n /\ a ** n divides b ==> a divides b
Proof
  rpt strip_tac >>
  `?k. n = SUC k` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO] >>
  `?q. b = q * a ** n` by rw[GSYM divides_def] >>
  `_ = q * (a * a ** k)` by rw[EXP] >>
  `_ = (q * a ** k) * a` by decide_tac >>
  metis_tac[divides_def]
QED

(* Theorem: n divides m ==> !k. n divides (k * m) *)
(* Proof:
   n divides m ==> ?q. m = q * n   by divides_def
   Hence k * m = k * (q * n)
               = (k * q) * n       by MULT_ASSOC
   or n divides (k * m)            by divides_def
*)
val DIVIDES_MULTIPLE = store_thm(
  "DIVIDES_MULTIPLE",
  ``!m n. n divides m ==> !k. n divides (k * m)``,
  metis_tac[divides_def, MULT_ASSOC]);

val divisor_pos = store_thm(
  "divisor_pos",
  ``!m n. 0 < n /\ m divides n ==> 0 < m``,
  metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < n /\ m divides n ==> 0 < m /\ m <= n *)
(* Proof:
   Since 0 < n /\ m divides n,
    then 0 < m           by divisor_pos
     and m <= n          by DIVIDES_LE
*)
val divides_pos = store_thm(
  "divides_pos",
  ``!m n. 0 < n /\ m divides n ==> 0 < m /\ m <= n``,
  metis_tac[divisor_pos, DIVIDES_LE]);

(* Theorem: 0 < n /\ m divides n ==> (n DIV (n DIV m) = m) *)
(* Proof:
   Since 0 < n /\ m divides n, 0 < m       by divisor_pos
   Hence n = (n DIV m) * m                 by DIVIDES_EQN, 0 < m
    Note 0 < n DIV m, otherwise contradicts 0 < n      by MULT
     Now n = m * (n DIV m)                 by MULT_COMM
           = m * (n DIV m) + 0             by ADD_0
   Therefore n DIV (n DIV m) = m           by DIV_UNIQUE
*)
val divide_by_cofactor = store_thm(
  "divide_by_cofactor",
  ``!m n. 0 < n /\ m divides n ==> (n DIV (n DIV m) = m)``,
  rpt strip_tac >>
  `0 < m` by metis_tac[divisor_pos] >>
  `n = (n DIV m) * m` by rw[GSYM DIVIDES_EQN] >>
  `0 < n DIV m` by metis_tac[MULT, NOT_ZERO_LT_ZERO] >>
  `n = m * (n DIV m) + 0` by metis_tac[MULT_COMM, ADD_0] >>
  metis_tac[DIV_UNIQUE]);

(* Theorem: 0 < n ==> !a b. a divides b ==> a divides b ** n *)
(* Proof:
   Since 0 < n, n = SUC m for some m.
    thus b ** n = b ** (SUC m)
                = b * b ** m    by EXP
   Now a divides b means
       ?k. b = k * a            by divides_def
    so b ** n
     = k * a * b ** m
     = (k * b ** m) * a         by MULT_COMM, MULT_ASSOC
   Hence a divides (b ** n)     by divides_def
*)
val divides_exp = store_thm(
  "divides_exp",
  ``!n. 0 < n ==> !a b. a divides b ==> a divides b ** n``,
  rw_tac std_ss[divides_def] >>
  `n <> 0` by decide_tac >>
  `?m. n = SUC m` by metis_tac[num_CASES] >>
  `(q * a) ** n = q * a * (q * a) ** m` by rw[EXP] >>
  `_ = q * (q * a) ** m * a` by rw[MULT_COMM, MULT_ASSOC] >>
  metis_tac[]);

(* Note; converse need prime divisor:
DIVIDES_EXP_BASE |- !a b n. prime a /\ 0 < n ==> (a divides b <=> a divides b ** n)
Counter-example for a general base: 12 divides 36 = 6^2, but ~(12 divides 6)
*)

(* Better than: DIVIDES_ADD_1 |- !a b c. a divides b /\ a divides c ==> a divides b + c *)

(* Theorem: c divides a /\ c divides b ==> !h k. c divides (h * a + k * b) *)
(* Proof:
   Since c divides a, ?u. a = u * c     by divides_def
     and c divides b, ?v. b = v * c     by divides_def
      h * a + k * b
    = h * (u * c) + k * (v * c)         by above
    = h * u * c + k * v * c             by MULT_ASSOC
    = (h * u + k * v) * c               by RIGHT_ADD_DISTRIB
   Hence c divides (h * a + k * b)      by divides_def
*)
val divides_linear = store_thm(
  "divides_linear",
  ``!a b c. c divides a /\ c divides b ==> !h k. c divides (h * a + k * b)``,
  rw_tac std_ss[divides_def] >>
  metis_tac[RIGHT_ADD_DISTRIB, MULT_ASSOC]);

(* Theorem: c divides a /\ c divides b ==> !h k d. (h * a = k * b + d) ==> c divides d *)
(* Proof:
   If c = 0,
      0 divides a ==> a = 0     by ZERO_DIVIDES
      0 divides b ==> b = 0     by ZERO_DIVIDES
      Thus d = 0                by arithmetic
      and 0 divides 0           by ZERO_DIVIDES
   If c <> 0, 0 < c.
      c divides a ==> (a MOD c = 0)  by DIVIDES_MOD_0
      c divides b ==> (b MOD c = 0)  by DIVIDES_MOD_0
      Hence 0 = (h * a) MOD c        by MOD_TIMES2, ZERO_MOD
              = (0 + d MOD c) MOD c  by MOD_PLUS, MOD_TIMES2, ZERO_MOD
              = d MOD c              by MOD_MOD
      or c divides d                 by DIVIDES_MOD_0
*)
val divides_linear_sub = store_thm(
  "divides_linear_sub",
  ``!a b c. c divides a /\ c divides b ==> !h k d. (h * a = k * b + d) ==> c divides d``,
  rpt strip_tac >>
  Cases_on `c = 0` >| [
    `(a = 0) /\ (b = 0)` by metis_tac[ZERO_DIVIDES] >>
    `d = 0` by rw_tac arith_ss[] >>
    rw[],
    `0 < c` by decide_tac >>
    `(a MOD c = 0) /\ (b MOD c = 0)` by rw[GSYM DIVIDES_MOD_0] >>
    `0 = (h * a) MOD c` by metis_tac[MOD_TIMES2, ZERO_MOD, MULT_0] >>
    `_ = (0 + d MOD c) MOD c` by metis_tac[MOD_PLUS, MOD_TIMES2, ZERO_MOD, MULT_0] >>
    `_ = d MOD c` by rw[MOD_MOD] >>
    rw[DIVIDES_MOD_0]
  ]);

(* ------------------------------------------------------------------------- *)
(* Factorial                                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FACT 0 = 1 *)
(* Proof: by FACT *)
val FACT_0 = store_thm(
  "FACT_0",
  ``FACT 0 = 1``,
  EVAL_TAC);

(* Theorem: FACT 1 = 1 *)
(* Proof:
     FACT 1
   = FACT (SUC 0)      by ONE
   = (SUC 0) * FACT 0  by FACT
   = (SUC 0) * 1       by FACT
   = 1                 by ONE
*)
val FACT_1 = store_thm(
  "FACT_1",
  ``FACT 1 = 1``,
  EVAL_TAC);

(* Theorem: FACT 2 = 2 *)
(* Proof:
     FACT 2
   = FACT (SUC 1)      by TWO
   = (SUC 1) * FACT 1  by FACT
   = (SUC 1) * 1       by FACT_1
   = 2                 by TWO
*)
val FACT_2 = store_thm(
  "FACT_2",
  ``FACT 2 = 2``,
  EVAL_TAC);

(* Theorem: (FACT n = 1) <=> n <= 1 *)
(* Proof:
   If n = 0,
      LHS = (FACT 0 = 1) = T         by FACT_0
      RHS = 0 <= 1 = T               by arithmetic
   If n <> 0, n = SUC m              by num_CASES
      LHS = FACT (SUC m) = 1
        <=> (SUC m) * FACT m = 1     by FACT
        <=> SUC m = 1 /\ FACT m = 1  by  MULT_EQ_1
        <=> m = 0  /\ FACT m = 1     by m = PRE 1 = 0
        <=> m = 0                    by FACT_0
      RHS = SUC m <= 1
        <=> ~(1 <= m)                by NOT_LEQ
        <=> m < 1                    by NOT_LESS_EQUAL
        <=> m = 0                    by arithmetic
*)
val FACT_EQ_1 = store_thm(
  "FACT_EQ_1",
  ``!n. (FACT n = 1) <=> n <= 1``,
  rpt strip_tac >>
  Cases_on `n` >>
  rw[FACT_0] >>
  rw[FACT] >>
  `!m. SUC m <= 1 <=> (m = 0)` by decide_tac >>
  metis_tac[FACT_0]);

(* Theorem: (FACT n = n) <=> (n = 1) \/ (n = 2) *)
(* Proof:
   If part: (FACT n = n) ==> (n = 1) \/ (n = 2)
      Note n <> 0           by FACT_0: FACT 0 = 1
       ==> ?m. n = SUC m    by num_CASES
      Thus SUC m * FACT m = SUC m       by FACT
                          = SUC m * 1   by MULT_RIGHT_1
       ==> FACT m = 1                   by EQ_MULT_LCANCEL, SUC_NOT
        or m <= 1           by FACT_EQ_1
      Thus m = 0 or 1       by arithmetic
        or n = 1 or 2       by ONE, TWO

   Only-if part: (FACT 1 = 1) /\ (FACT 2 = 2)
      Note FACT 1 = 1       by FACT_1
       and FACT 2 = 2       by FACT_2
*)
val FACT_EQ_SELF = store_thm(
  "FACT_EQ_SELF",
  ``!n. (FACT n = n) <=> (n = 1) \/ (n = 2)``,
  rw[EQ_IMP_THM] >| [
    `n <> 0` by metis_tac[FACT_0, DECIDE``1 <> 0``] >>
    `?m. n = SUC m` by metis_tac[num_CASES] >>
    fs[FACT] >>
    `FACT m = 1` by metis_tac[MULT_LEFT_1, EQ_MULT_RCANCEL, SUC_NOT] >>
    `m <= 1` by rw[GSYM FACT_EQ_1] >>
    decide_tac,
    rw[FACT_1],
    rw[FACT_2]
  ]);

(* Theorem: 0 < n ==> n <= FACT n *)
(* Proof:
   Note n <> 0             by 0 < n
    ==> ?m. n = SUC m      by num_CASES
   Thus FACT n
      = FACT (SUC m)       by n = SUC m
      = (SUC m) * FACT m   by FACT_LESS: 0 < FACT m
      >= (SUC m)           by LE_MULT_CANCEL_LBARE
      >= n                 by n = SUC m
*)
val FACT_GE_SELF = store_thm(
  "FACT_GE_SELF",
  ``!n. 0 < n ==> n <= FACT n``,
  rpt strip_tac >>
  `?m. n = SUC m` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO] >>
  rw[FACT] >>
  rw[FACT_LESS]);

(* Theorem: 0 < n ==> (FACT (n-1) = FACT n DIV n) *)
(* Proof:
   Since  n = SUC(n-1)                 by SUC_PRE, 0 < n.
     and  FACT n = n * FACT (n-1)      by FACT
                 = FACT (n-1) * n      by MULT_COMM
                 = FACT (n-1) * n + 0  by ADD_0
   Hence  FACT (n-1) = FACT n DIV n    by DIV_UNIQUE, 0 < n.
*)
val FACT_DIV = store_thm(
  "FACT_DIV",
  ``!n. 0 < n ==> (FACT (n-1) = FACT n DIV n)``,
  rpt strip_tac >>
  `n = SUC(n-1)` by decide_tac >>
  `FACT n = n * FACT (n-1)` by metis_tac[FACT] >>
  `_ = FACT (n-1) * n + 0` by rw[MULT_COMM] >>
  metis_tac[DIV_UNIQUE]);

val _ = export_theory();
