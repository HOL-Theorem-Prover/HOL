(*===========================================================================*)
(* Euclid's theorem: for every prime, there is another one that is larger.   *)
(* This proof has been excerpted and adapted from John Harrison's proof of   *)
(* a special case (n=4) of Fermat's Last Theorem.                            *)
(*                                                                           *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* First, open some relevant context, the theory of arithmetic. This theory  *)
(* is already present, but the ML module arithmeticTheory needs to be opened *)
(* before the definitions and theorems of the theory are available without   *)
(* supplying the "arithmeticTheory." prefix.
(*---------------------------------------------------------------------------*)

open arithmeticTheory

(*---------------------------------------------------------------------------*)
(* Divisibility.                                                             *)
(*---------------------------------------------------------------------------*)

val divides_def = 
 Define 
  `divides a b = ?x. b = a * x`;

set_fixity "divides" (Infixr 450);

(*---------------------------------------------------------------------------*)
(* Primality.                                                                *)
(*---------------------------------------------------------------------------*)

val prime_def = 
 Define 
   `prime p = ~(p=1) /\ !x. x divides p ==> (x=1) \/ (x=p)`;

(*---------------------------------------------------------------------------*)
(* A sequence of basic theorems about the "divides" relation.                *)
(*---------------------------------------------------------------------------*)

val DIVIDES_0 = store_thm
 ("DIVIDES_0",
  ``!x. x divides 0``,
  METIS_TAC [divides_def,MULT_CLAUSES]);

val DIVIDES_ZERO = store_thm
 ("DIVIDES_ZERO",
  ``!x. 0 divides x = (x = 0)``,
  METIS_TAC [divides_def,MULT_CLAUSES]);

val DIVIDES_ONE = store_thm
 ("DIVIDES_ONE",
  ``!x. x divides 1 = (x = 1)``,
  METIS_TAC [divides_def,MULT_CLAUSES,MULT_EQ_1]);

val DIVIDES_REFL = store_thm
 ("DIVIDES_REFL",
  ``!x. x divides x``,
  METIS_TAC [divides_def,MULT_CLAUSES]);

val DIVIDES_TRANS = store_thm
 ("DIVIDES_TRANS",
  ``!a b c. a divides b /\ b divides c ==> a divides c``,
  METIS_TAC [divides_def,MULT_ASSOC]);

val DIVIDES_ADD = store_thm
("DIVIDES_ADD",
 ``!d a b. d divides a /\ d divides b ==> d divides (a + b)``,
 METIS_TAC[divides_def,LEFT_ADD_DISTRIB]);

val DIVIDES_SUB = store_thm
 ("DIVIDES_SUB",
  ``!d a b. d divides a /\ d divides b ==> d divides (a - b)``,
  METIS_TAC [divides_def,LEFT_SUB_DISTRIB]);

val DIVIDES_ADDL = store_thm
 ("DIVIDES_ADDL",
  ``!d a b. d divides a /\ d divides (a + b) ==> d divides b``,
  METIS_TAC [ADD_SUB,ADD_SYM,DIVIDES_SUB]);

val DIVIDES_LMUL = store_thm
 ("DIVIDES_LMUL",
  ``!d a x. d divides a ==> d divides (x * a)``,
  METIS_TAC [divides_def,MULT_ASSOC,MULT_SYM]);

val DIVIDES_RMUL = store_thm
 ("DIVIDES_RMUL",
  ``!d a x. d divides a ==> d divides (a * x)``,
  METIS_TAC [MULT_SYM,DIVIDES_LMUL]);

val DIVIDES_LE = store_thm
 ("DIVIDES_LE",
  ``!m n. m divides n ==> m <= n \/ (n = 0)``,
  RW_TAC arith_ss  [divides_def]
     THEN Cases_on `x`
     THEN RW_TAC arith_ss  [MULT_CLAUSES]);

(*---------------------------------------------------------------------------*)
(* Various proofs of the same formula                                        *)
(*---------------------------------------------------------------------------*)

val DIVIDES_FACT = store_thm
 ("DIVIDES_FACT",
  ``!m n. 0 < m /\ m <= n ==> m divides (FACT n)``,
  RW_TAC arith_ss  [LESS_EQ_EXISTS]
   THEN Induct_on `p`
   THEN RW_TAC arith_ss  [FACT,ADD_CLAUSES]
   THENL [Cases_on `m`, ALL_TAC]
   THEN METIS_TAC [FACT, DECIDE ``!x. ~(x < x)``,
                   DIVIDES_RMUL, DIVIDES_LMUL, DIVIDES_REFL]);

val DIVIDES_FACT = store_thm
 ("DIVIDES_FACT",
  ``!m n. 0 < m /\ m <= n ==> m divides (FACT n)``,
  RW_TAC arith_ss  [LESS_EQ_EXISTS]
   THEN Induct_on `p`
   THEN RW_TAC arith_ss  [FACT,ADD_CLAUSES]
   THEN METIS_TAC [FACT, DECIDE ``!x. ~(x < x)``, num_CASES,
                    DIVIDES_RMUL, DIVIDES_LMUL, DIVIDES_REFL]);

val DIVIDES_FACT = store_thm
 ("DIVIDES_FACT",
  ``!m n. 0 < m /\ m <= n ==> m divides (FACT n)``,
  RW_TAC arith_ss  [LESS_EQ_EXISTS]
   THEN Induct_on `p`
   THEN METIS_TAC [FACT, DECIDE ``!x. ~(x < x)``, num_CASES,
                   DIVIDES_RMUL,DIVIDES_LMUL,DIVIDES_REFL,ADD_CLAUSES]);


val DIVIDES_FACT = prove
(``!m n. 0 < m /\ m <= n ==> m divides (FACT n)``,
Induct_on `n - m`
 THEN RW_TAC arith_ss  [] THENL
 [`m = n`         by DECIDE_TAC THEN
  `?k. m = SUC k` by METIS_TAC[num_CASES,prim_recTheory.LESS_REFL]
     THEN METIS_TAC[FACT,DIVIDES_RMUL,DIVIDES_REFL],
  `0 < n`         by DECIDE_TAC THEN
  `?k. n = SUC k` by METIS_TAC [num_CASES,prim_recTheory.LESS_REFL]
   THEN RW_TAC arith_ss  [FACT, DIVIDES_RMUL]]);


(*---------------------------------------------------------------------------*)
(* Zero and one are not prime, but two is.  All primes are positive.         *)
(*---------------------------------------------------------------------------*)

val NOT_PRIME_0 = store_thm
 ("NOT_PRIME_0",
  ``~prime 0``,
  RW_TAC arith_ss  [prime_def,DIVIDES_0]);

val NOT_PRIME_1 = store_thm
 ("NOT_PRIME_1",
  ``~prime 1``,
  RW_TAC arith_ss  [prime_def]);

val PRIME_2 = store_thm
 ("PRIME_2",
  ``prime 2``,
  RW_TAC arith_ss  [prime_def] THEN
  METIS_TAC [DIVIDES_LE, DIVIDES_ZERO,
             DECIDE``~(2=1) /\ ~(2=0) /\ (x<=2 = (x=0) \/ (x=1) \/ (x=2))``]);

val PRIME_POS = store_thm
 ("PRIME_POS",
  ``!p. prime p ==> 0<p``,
  Cases THEN RW_TAC arith_ss [NOT_PRIME_0]);

(*---------------------------------------------------------------------------*)
(* Every number has a prime factor, except for 1. The proof proceeds by a    *)
(* "complete" induction on n, and then considers cases on whether n is       *)
(* prime or not. The first case (n is prime) is trivial. In the second case, *)
(* there must be an "x" that divides n, and x is not 1 or n. By DIVIDES_LE,  *)
(* n=0 or x <= n. If n=0, then 2 is a prime that divides 0. On the other     *)
(* hand, if x <= n, there are two cases: if x<n then we can use the i.h. and *)
(* by transitivity of divides we are done; otherwise, if x=n, then we have   *)
(* a contradiction with the fact that x is not 1 or n.                       *)
 *---------------------------------------------------------------------------*)

val PRIME_FACTOR = store_thm
 ("PRIME_FACTOR",
  ``!n. ~(n = 1) ==> ?p. prime p /\ p divides n``,
  completeInduct_on `n`
   THEN RW_TAC arith_ss  []
   THEN Cases_on `prime n` THENL
   [METIS_TAC [DIVIDES_REFL],
    `?x. x divides n /\ ~(x=1) /\ ~(x=n)` by METIS_TAC[prime_def] THEN 
    METIS_TAC [LESS_OR_EQ, PRIME_2,
               DIVIDES_LE, DIVIDES_TRANS, DIVIDES_0]]);

(*---------------------------------------------------------------------------*)
(* In the following proof, METIS_TAC automatically considers cases on        *)
(* whether n is prime or not.                                                *)
(*---------------------------------------------------------------------------*)

val PRIME_FACTOR = store_thm
 ("PRIME_FACTOR",
  ``!n. ~(n = 1) ==> ?p. prime p /\ p divides n``,
  completeInduct_on `n` THEN 
  METIS_TAC [DIVIDES_REFL,prime_def,LESS_OR_EQ, PRIME_2,
             DIVIDES_LE, DIVIDES_TRANS, DIVIDES_0]);


(*---------------------------------------------------------------------------*)
(* Every number has a prime greater than it.                                 *)
(* Proof.                                                                    *)
(* Suppose not; then there's an n such that all p greater than n are not     *)
(* prime. Consider FACT(n) + 1: it's not equal to 1, so there's a prime q    *)
(* that divides it. q also divides FACT n because q is less-than-or-equal    *)
(* to n. By DIVIDES_ADDL, this means that q=1. But then q is not prime,      *)
(* which is a contradiction.                                                 *)
(*---------------------------------------------------------------------------*)

val EUCLID = store_thm
 ("EUCLID",
  ``!n. ?p. n < p /\ prime p``,
  SPOSE_NOT_THEN STRIP_ASSUME_TAC
   THEN MP_TAC (SPEC ``FACT n + 1`` PRIME_FACTOR)
   THEN RW_TAC arith_ss  [FACT_LESS, DECIDE ``~(x=0) = 0<x``]
   THEN METIS_TAC [DIVIDES_FACT, DIVIDES_ADDL, DIVIDES_ONE,
                   NOT_PRIME_1, NOT_LESS, PRIME_POS]);


(*---------------------------------------------------------------------------*)
(* The previous proof is somewhat unsatisfactory, because its structure gets *)
(* hidden in the invocations of the automated reasoners. An assertional      *)
(* style allows a presentation that mirrors the informal proof.              *)
(*---------------------------------------------------------------------------*)

val EUCLID_AGAIN = prove (``!n. ?p. n < p /\ prime p``,
CCONTR_TAC
THEN
   `?n. !p. n < p ==> ~prime p`  by METIS_TAC[]              THEN
   `~(FACT n + 1 = 1)`           by RW_TAC arith_ss [FACT_LESS,
                                    DECIDE ``~(x=0) = 0<x``] THEN
   `?p. prime p /\
        p divides (FACT n + 1)`  by METIS_TAC [PRIME_FACTOR] THEN
   `0 < p`                       by METIS_TAC [PRIME_POS]    THEN
   `p <= n`                      by METIS_TAC [NOT_LESS]     THEN
   `p divides FACT n`            by METIS_TAC [DIVIDES_FACT] THEN
   `p divides 1`                 by METIS_TAC [DIVIDES_ADDL] THEN
   `p = 1`                       by METIS_TAC [DIVIDES_ONE]  THEN
   `~prime p`                    by METIS_TAC [NOT_PRIME_1]
THEN
METIS_TAC[]);
