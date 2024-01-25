open HolKernel Parse boolLib simpLib BasicProvers
     prim_recTheory arithmeticTheory boolSimps
     metisLib numLib;

val CALC = EQT_ELIM o reduceLib.REDUCE_CONV;
val ARITH_TAC = CONV_TAC Arith.ARITH_CONV;
val DECIDE = EQT_ELIM o Arith.ARITH_CONV;

val arith_ss = numLib.arith_ss;

fun simp ths = asm_simp_tac (srw_ss() ++ numSimps.ARITH_ss) ths
fun gvs ths = global_simp_tac {droptrues = true, elimvars = true,
                               oldestfirst = true, strip = true}
                              (srw_ss() ++ numSimps.ARITH_ss) ths
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

val LEQ_DIVIDES_FACT = store_thm
 ("LEQ_DIVIDES_FACT",
  ``!m n. 0 < m /\ m <= n ==> divides m (FACT n)``,
  RW_TAC arith_ss  [LESS_EQ_EXISTS]
   THEN Induct_on `p`
   THEN METIS_TAC [FACT, LESS_REFL, num_CASES, DIVIDES_MULT,
                   MULT_COMM, DIVIDES_REFL, ADD_CLAUSES]);

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

val _ = export_theory();
