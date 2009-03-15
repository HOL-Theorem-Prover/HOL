structure dividesScript =
struct

open HolKernel Parse boolLib simpLib BasicProvers
     prim_recTheory arithmeticTheory boolSimps SingleStep metisLib;

val CALC = EQT_ELIM o reduceLib.REDUCE_CONV;
val ARITH_TAC   = CONV_TAC Arith.ARITH_CONV;

val arith_ss = simpLib.++(bool_ss, numSimps.ARITH_ss);

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
  ``!n m. divides (n * m) m = (m = 0) \/ (n = 1)``,
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

(*---------------------------------------------------------------------------*)
(* Definition and trivial facts about primality.                             *)
(*---------------------------------------------------------------------------*)

val prime_def = Q.new_definition
("prime_def",
 `prime a = ~(a=1) /\ !b. divides b a ==> (b=a) \/ (b=1)`);


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

val PRIME_POS = store_thm
 ("PRIME_POS",
  ``!p. prime p ==> 0<p``,
  Cases THEN RW_TAC arith_ss [NOT_PRIME_0]);


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
(* A sequence of primes.                                                     *)
(*                                                                           *)
(*     PRIMES_def = |- !n. n < PRIMES n /\ prime (PRIMES n)                  *)
(*                                                                           *)
(* PRIMES is not computed, it just exists!  Also, it's not *the* sequence of *)
(* primes, because                                                           *)
(*                                                                           *)
(*   prime n ==> ?i. n = PRIMES(i)                                           *)
(*                                                                           *)
(* isn't provable. For example, can't prove that 2 is in the sequence.       *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

val PRIMES_def = new_specification
("PRIMES",
 ["PRIMES"],
  SIMP_RULE bool_ss [SKOLEM_THM] EUCLID);


(*---------------------------------------------------------------------------*)
(* Directly computable version of divides                                    *)
(*---------------------------------------------------------------------------*)

val compute_divides = Q.store_thm
("compute_divides",
 `!a b. divides a b =
        if a=0 then (b=0) else
        if a=1 then T else
        if b=0 then T else
        (b MOD a = 0)`,
  RW_TAC arith_ss [divides_def]
   THEN EQ_TAC
   THEN RW_TAC arith_ss [] THENL
   [Cases_on `q` THENL
     [RW_TAC arith_ss [],
      `0<a` by RW_TAC arith_ss [] THEN
      METIS_TAC [MOD_MULT, MULT_SYM, ADD_CLAUSES]],
    Q.EXISTS_TAC `b` THEN RW_TAC arith_ss [],
    Q.EXISTS_TAC `0` THEN RW_TAC arith_ss [],
    `0<a` by RW_TAC arith_ss [] THEN
     let val MOD_P_inst = BETA_RULE (Q.SPECL[`\x. (x = 0)`,`b`,`a`] MOD_P)
     in METIS_TAC [MOD_P_inst,MULT_SYM, ADD_CLAUSES]
     end]);

val _ = 
 computeLib.add_persistent_funs
     [("compute_divides",compute_divides)];

val _ = export_theory();

end
