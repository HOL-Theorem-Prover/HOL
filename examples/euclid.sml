(*===========================================================================*)
(* Euclid's theorem: for every prime, there is another one that is larger.   *)
(* This proof has been excerpted and adapted from John Harrison's proof of   *)
(* a special case (n=4) of Fermat's Last Theorem.                            *)
(*                                                                           *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* First, open required context: the theory of arithmetic. This theory is    *)
(* automatically loaded when HOL starts, but the ML module arithmeticTheory  *)
(* needs to be opened before the definitions and theorems of the theory are  *)
(* available without supplying the "arithmeticTheory." prefix.               *)
(*---------------------------------------------------------------------------*)

open arithmeticTheory;

(*---------------------------------------------------------------------------*)
(* Divisibility.                                                             *)
(*---------------------------------------------------------------------------*)

set_fixity "divides" (Infix(NONASSOC, 450));

Definition divides_def:
  a divides b <=> ?x. b = a * x
End

(*---------------------------------------------------------------------------*)
(* Primality.                                                                *)
(*---------------------------------------------------------------------------*)

Definition prime_def:
  prime p <=> p <> 1 /\ !x. x divides p ==> (x = 1) \/ (x = p)
End

(*---------------------------------------------------------------------------*)
(* A sequence of basic theorems about the "divides" relation.                *)
(*---------------------------------------------------------------------------*)

Theorem DIVIDES_ZERO:
  !x. x divides 0
Proof
  metis_tac [divides_def,MULT_CLAUSES]
QED

Theorem ZERO_DIVIDES:
  !x. 0 divides x <=> x = 0
Proof
  metis_tac [divides_def,MULT_CLAUSES]
QED

Theorem DIVIDES_ONE:
 !x. x divides 1 <=> x = 1
Proof
  metis_tac [divides_def,MULT_CLAUSES,MULT_EQ_1]
QED

Theorem DIVIDES_REFL :
 !x. x divides x
Proof
  metis_tac [divides_def,MULT_CLAUSES]
QED

Theorem DIVIDES_TRANS :
 !a b c. a divides b /\ b divides c ==> a divides c
Proof
  metis_tac [divides_def,MULT_ASSOC]
QED

Theorem DIVIDES_ADD :
 !d a b. d divides a /\ d divides b ==> d divides (a + b)
Proof
 metis_tac[divides_def,LEFT_ADD_DISTRIB]
QED

Theorem DIVIDES_SUB :
  !d a b. d divides a /\ d divides b ==> d divides (a - b)
Proof
  metis_tac [divides_def,LEFT_SUB_DISTRIB]
QED

Theorem DIVIDES_ADDL :
  !d a b. d divides a /\ d divides (a + b) ==> d divides b
Proof
  metis_tac [ADD_SUB,ADD_SYM,DIVIDES_SUB]
QED

Theorem DIVIDES_LMUL :
  !d a x. d divides a ==> d divides (x * a)
Proof
  metis_tac [divides_def,MULT_ASSOC,MULT_SYM]
QED

Theorem DIVIDES_RMUL :
  !d a x. d divides a ==> d divides (a * x)
Proof
  metis_tac [MULT_SYM,DIVIDES_LMUL]
QED

Theorem DIVIDES_LE :
  !a b. a divides b ==> (0 < a ∧ a <= b) \/ b = 0
Proof
  rw [divides_def] >> rw[]
QED

(*---------------------------------------------------------------------------*)
(* Various proofs of the same formula                                        *)
(*---------------------------------------------------------------------------*)

Theorem LE_DIVIDES_FACT :
  !m n. 0 < m /\ m <= n ==> m divides (FACT n)
Proof
  rw [LESS_EQ_EXISTS]
   >> Induct_on `p`
   >> rw [FACT,ADD_CLAUSES]
   >> Cases_on `m`
   >> metis_tac [FACT, DECIDE ``!x. ~(x < x)``,
                 DIVIDES_RMUL, DIVIDES_LMUL, DIVIDES_REFL]
QED

Theorem DIVIDES_FACT:
  ∀n. 0 < n ==> n divides (FACT n)
Proof
  Cases
   >> rw[FACT]
   >> rename1 ‘SUC n’
   >> irule DIVIDES_LMUL
   >> metis_tac [DIVIDES_REFL]
QED

Theorem LE_DIVIDES_FACT :
  !m n. 0 < m /\ m <= n ==> m divides (FACT n)
Proof
  rw [LESS_EQ_EXISTS]
  >> Induct_on `p`
  >> fs [FACT,ADD_CLAUSES]
     >- metis_tac [DIVIDES_FACT]
     >- metis_tac [DIVIDES_RMUL]
QED

Theorem LE_DIVIDES_FACT :
  !m n. 0 < m /\ m <= n ==> m divides (FACT n)
Proof
  `!m p. 0 < m ==> m divides FACT (m + p)`
     suffices_by metis_tac[LESS_EQ_EXISTS]
   >> Induct_on `p`
   >> rw [FACT,ADD_CLAUSES]
   >> metis_tac [FACT, DECIDE ``!x. ~(x < x)``, num_CASES,
                 DIVIDES_RMUL, DIVIDES_LMUL, DIVIDES_REFL]
QED

Theorem LE_DIVIDES_FACT :
  !m n. 0 < m /\ m <= n ==> m divides (FACT n)
Proof
  rw [LESS_EQ_EXISTS]
   >> Induct_on `p`
   >> metis_tac [FACT, DECIDE ``!x. ~(x < x)``, num_CASES,
                 DIVIDES_RMUL,DIVIDES_LMUL,DIVIDES_REFL,ADD_CLAUSES]
QED

Theorem LE_DIVIDES_FACT :
  !m n. 0 < m /\ m <= n ==> m divides (FACT n)
Proof
  Induct_on `n - m` >> rw []
  >- metis_tac [EQ_LESS_EQ,DIVIDES_FACT]
  >- (`?k. n = SUC k` by (Cases_on `n` >> fs[])
      >> rw [FACT, DIVIDES_RMUL])
QED

(*---------------------------------------------------------------------------*)
(* Zero and one are not prime, but two is.  All primes are positive.         *)
(*---------------------------------------------------------------------------*)

Theorem NOT_PRIME_0 :
  ~prime 0
Proof
  rw [prime_def,DIVIDES_ZERO]
QED

Theorem NOT_PRIME_1 :
  ~prime 1
Proof
 rw [prime_def]
QED

Theorem PRIME_2 :
 prime 2
Proof
  rw [prime_def] >> drule DIVIDES_LE >> rw[]
QED

Theorem PRIME_POS :
  !p. prime p ==> 0 < p
Proof
  Cases >> rw [NOT_PRIME_0]
QED

(*---------------------------------------------------------------------------*)
(* Every number has a prime factor, except for 1. The proof proceeds by a    *)
(* complete induction on n, and then considers cases on whether n is         *)
(* prime or not. The first case (n is prime) is trivial. In the second case, *)
(* there must be an x that divides n, and x is not 1 or n. By DIVIDES_LE,    *)
(* n=0 or x <= n. If n=0, then 2 is a prime that divides 0. On the other     *)
(* hand, if x <= n, there are two cases: if x<n then we can use the i.h. and *)
(* by transitivity of divides we are done; otherwise, if x=n, then we have   *)
(* a contradiction with the fact that x is not 1 or n.                       *)
(*---------------------------------------------------------------------------*)

Theorem PRIME_FACTOR :
  !n. ~(n = 1) ==> ?p. prime p /\ p divides n
Proof
  completeInduct_on `n` >> rw [] >>
  Cases_on `prime n`
   >- metis_tac [DIVIDES_REFL]
   >- (`?x. x divides n /\ x<>1 /\ x<>n` by metis_tac[prime_def]
       >> metis_tac [LESS_OR_EQ, PRIME_2,
                     DIVIDES_LE, DIVIDES_TRANS, DIVIDES_ZERO])
QED

(*---------------------------------------------------------------------------*)
(* In the following proof, metis_tac automatically considers cases on        *)
(* whether n is prime or not.                                                *)
(*---------------------------------------------------------------------------*)

Theorem PRIME_FACTOR :
  !n. n<>1 ==> ?p. prime p /\ p divides n
Proof
  completeInduct_on `n` >>
  metis_tac [prime_def,LESS_OR_EQ, PRIME_2,
             DIVIDES_REFL,DIVIDES_LE, DIVIDES_TRANS, DIVIDES_ZERO]
QED

(*---------------------------------------------------------------------------*)
(* Every number has a prime greater than it.                                 *)
(* Proof.                                                                    *)
(* Suppose not; then there's an n such that all p greater than n are not     *)
(* prime. Consider FACT(n) + 1: it's not equal to 1, so there's a prime q    *)
(* that divides it. q also divides FACT n because q <= n. By DIVIDES_ADDL,   *)
(* this means that q=1. But then q is not prime, a contradiction.            *)
(*---------------------------------------------------------------------------*)

Theorem EUCLID :
 !n. ?p. n < p /\ prime p
Proof
  spose_not_then strip_assume_tac
   >> mp_tac (SPEC ``FACT n + 1`` PRIME_FACTOR)
   >> rw [FACT_LESS, DECIDE ``x <> 0 <=> 0 < x``]
   >> metis_tac [LE_DIVIDES_FACT, DIVIDES_ADDL, DIVIDES_ONE,
                 NOT_PRIME_1, NOT_LESS, PRIME_POS]
QED


(*---------------------------------------------------------------------------*)
(* The previous proof is somewhat unsatisfactory, because its structure gets *)
(* hidden in the invocations of the automated reasoners. An assertional      *)
(* style allows a presentation that mirrors the informal proof.              *)
(*---------------------------------------------------------------------------*)

Theorem EUCLID_AGAIN[local]:
  !n. ?p. n < p /\ prime p
Proof
   CCONTR_TAC >>
   `?n. !p. n < p ==> ~prime p`
                      by metis_tac[] >>
   `FACT n + 1 ≠ 1`   by rw [FACT_LESS, DECIDE ``x<>0 <=> 0<x``] >>
   ‘∃p. prime p ∧ p divides (FACT n + 1)’
                      by metis_tac [PRIME_FACTOR]    >>
   `0 < p`            by metis_tac [PRIME_POS]       >>
   `p divides FACT n` by metis_tac [NOT_LESS,LE_DIVIDES_FACT] >>
   `p divides 1`      by metis_tac [DIVIDES_ADDL]    >>
   `p = 1`            by metis_tac [DIVIDES_ONE]     >>
   `~prime p`         by metis_tac [NOT_PRIME_1]     >>
   metis_tac[]
QED
