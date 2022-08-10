(** Taken from the HOL4 distribution (original file: HOL4/examples/euclid.sml **)

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

open BasicProvers Defn HolKernel Parse Conv SatisfySimps Tactic monadsyntax
     boolTheory bossLib arithmeticTheory;

open LassieLib arithTacticsLib;

val _ = new_theory "caseStudy1Euclid";

val _ = LassieLib.loadJargon "Arithmetic";
(*---------------------------------------------------------------------------*)
(* Divisibility.                                                             *)
(*---------------------------------------------------------------------------*)

set_fixity "divides" (Infix(NONASSOC, 450));

Definition divides_def:
(a divides b) = (? x. b = a * x)
End


(*---------------------------------------------------------------------------*)
(* Primality.                                                                *)
(*---------------------------------------------------------------------------*)

Definition prime_def:
  prime p = (p<>1 /\ !x . x divides p ==> (x=1) \/ (x=p))
End

(*---------------------------------------------------------------------------*)
(* A sequence of basic theorems about the "divides" relation.                *)
(*---------------------------------------------------------------------------*)

Theorem DIVIDES_0:
  ! x . x divides 0
Proof
  LassieLib.nltac `
    [divides_def, MULT_CLAUSES] solves the goal.`
  (* metis_tac [divides_def,MULT_CLAUSES] *)
QED

Theorem DIVIDES_ZERO:
  ! x . (0 divides x) = (x = 0)
Proof
  LassieLib.nltac `
    [divides_def, MULT_CLAUSES] solves the goal.`
  (* metis_tac [divides_def,MULT_CLAUSES] *)
QED

Theorem DIVIDES_ONE:
  ! x . (x divides 1) = (x = 1)
Proof
  LassieLib.nltac
    `[divides_def, MULT_CLAUSES, MULT_EQ_1] solves the goal.`
  (* metis_tac [divides_def,MULT_CLAUSES,MULT_EQ_1] *)
QED

Theorem DIVIDES_REFL:
  ! x . x divides x
Proof
  LassieLib.nltac `
    [divides_def, MULT_CLAUSES] solves the goal.`
  (* metis_tac [divides_def,MULT_CLAUSES] *)
QED

Theorem DIVIDES_TRANS:
  ! a b c . a divides b /\ b divides c ==> a divides c
Proof
  LassieLib.nltac `
    [divides_def, MULT_ASSOC] solves the goal.`
  (* metis_tac [divides_def,MULT_ASSOC] *)
QED

Theorem DIVIDES_ADD:
  ! d a b . d divides a /\ d divides b ==> d divides (a + b)
Proof
  LassieLib.nltac `
    [divides_def, LEFT_ADD_DISTRIB] solves the goal.`
  (* metis_tac [divides_def, LEFT_ADD_DISTRIB] *)
QED

Theorem DIVIDES_SUB:
  !d a b . d divides a /\ d divides b ==> d divides (a - b)
Proof
  LassieLib.nltac `
    [divides_def, LEFT_SUB_DISTRIB] solves the goal.`
  (* metis_tac [divides_def,LEFT_SUB_DISTRIB] *)
QED

Theorem DIVIDES_ADDL:
  !d a b . d divides a /\ d divides (a + b) ==> d divides b
Proof
  LassieLib.nltac `
    [ADD_SUB, ADD_SYM, DIVIDES_SUB] solves the goal.`
  (* metis_tac [ADD_SUB,ADD_SYM,DIVIDES_SUB] *)
QED

Theorem DIVIDES_LMUL:
  !d a x . d divides a ==> d divides (x * a)
Proof
  LassieLib.nltac `
    [divides_def, MULT_ASSOC, MULT_SYM] solves the goal.`
  (* metis_tac [divides_def,MULT_ASSOC,MULT_SYM] *)
QED

Theorem DIVIDES_RMUL:
  !d a x . d divides a ==> d divides (a * x)
Proof
  LassieLib.nltac `
    [MULT_SYM,DIVIDES_LMUL] solves the goal.`
  (* metis_tac [MULT_SYM,DIVIDES_LMUL] *)
QED

Theorem DIVIDES_LE:
  !m n . m divides n ==> m <= n \/ (n = 0)
Proof
  LassieLib.nltac ‘
            rewrite [divides_def].
            [] solves the goal.’
  (* rw [divides_def] >> rw[] *)
QED

(*---------------------------------------------------------------------------*)
(* Various proofs of the same formula                                        *)
(*---------------------------------------------------------------------------*)
val NOT_X_LE = save_thm ("NOT_X_LE", DECIDE ``! x. ~(x < x)``);

Theorem DIVIDES_FACT:
  !m n . 0 < m /\ m <= n ==> m divides (FACT n)
Proof
  LassieLib.nltac ‘
    rewrite [LESS_EQ_EXISTS].
    perform an induction on 'p'.
    [FACT, NOT_X_LE, num_CASES, DIVIDES_RMUL, DIVIDES_LMUL, DIVIDES_REFL, ADD_CLAUSES]
      solves the goal.’
  (*
  rw  [LESS_EQ_EXISTS]
   >> Induct_on `p`
   >> metis_tac [FACT, DECIDE ``!x. ~(x < x)``, num_CASES,
                   DIVIDES_RMUL,DIVIDES_LMUL,DIVIDES_REFL,ADD_CLAUSES] *)
QED

(*---------------------------------------------------------------------------*)
(* Zero and one are not prime, but two is.  All primes are positive.         *)
(*---------------------------------------------------------------------------*)

Theorem NOT_PRIME_0:
  ~prime 0
Proof
  LassieLib.nltac `rewrite [prime_def, DIVIDES_0].`
  (* rw  [prime_def,DIVIDES_0] *)
QED

Theorem NOT_PRIME_1:
  ~prime 1
Proof
  LassieLib.nltac `rewrite [prime_def].`
  (* rw  [prime_def] *)
QED

val two_prime_eqs = curry save_thm "two_prime_eqs" (DECIDE ``~(2=1) /\ ~(2=0) /\ ((x <=2) = (x = 0) \/ (x = 1) \/  (x = 2))``);

Theorem PRIME_2:
  prime 2
Proof
  LassieLib.nltac `
    rewrite [prime_def].
    [DIVIDES_LE, DIVIDES_ZERO, two_prime_eqs] solves the goal.`
  (* rw  [prime_def] >>
  metis_tac [DIVIDES_LE, DIVIDES_ZERO,
             DECIDE``~(2=1) /\ ~(2=0) /\ (x<=2 = (x=0) \/ (x=1) \/ (x=2))``] *)
QED

Theorem PRIME_POS:
  !p . prime p ==> 0<p
Proof
  LassieLib.nltac `perform a case split. rewrite [NOT_PRIME_0].`
  (* Cases >> rw [NOT_PRIME_0] *)
QED

(*---------------------------------------------------------------------------*)
(* Every number has a prime factor, except for 1. The proof proceeds by a    *)
(* "complete" induction on n, and then considers cases on whether n is       *)
(* prime or not. The first case (n is prime) is trivial. In the second case, *)
(* there must be an "x" that divides n, and x is not 1 or n. By DIVIDES_LE,  *)
(* n=0 or x <= n. If n=0, then 2 is a prime that divides 0. On the other     *)
(* hand, if x <= n, there are two cases: if x<n then we can use the i.h. and *)
(* by transitivity of divides we are done; otherwise, if x=n, then we have   *)
(* a contradiction with the fact that x is not 1 or n.                       *)
(*---------------------------------------------------------------------------*)

Theorem PRIME_FACTOR:
  !n . ~(n = 1) ==> ?p . prime p /\ p divides n
Proof
  LassieLib.nltac ‘
    Complete Induction on 'n'.
    rewrite [].
    perform a case split for 'prime n'.
    Goal 1. [DIVIDES_REFL] solves the goal. End.
    Goal 1.
      show '? x. x divides n and x <> 1 and x <> n' using (follows from [prime_def]).
      [LESS_OR_EQ, PRIME_2, DIVIDES_LE, DIVIDES_TRANS, DIVIDES_0] solves the goal.
    End.’
  (*
   completeInduct_on `n`
   >> rw  []
   >> Cases_on `prime n` >|
   [metis_tac [DIVIDES_REFL],
    `?x. x divides n /\ x<>1 /\ x<>n` by metis_tac[prime_def] >>
    metis_tac [LESS_OR_EQ, PRIME_2,
               DIVIDES_LE, DIVIDES_TRANS, DIVIDES_0]] *)
QED

(*---------------------------------------------------------------------------*)
(* In the following proof, metis_tac automatically considers cases on        *)
(* whether n is prime or not.                                                *)
(*---------------------------------------------------------------------------*)

Theorem PRIME_FACTOR:
 !n . n<>1 ==> ?p . prime p /\ p divides n
Proof
  LassieLib.nltac ‘
    Complete Induction on 'n'.
    [DIVIDES_REFL,prime_def,LESS_OR_EQ, PRIME_2,
             DIVIDES_LE, DIVIDES_TRANS, DIVIDES_0] solves the goal.’
  (*
  completeInduct_on `n` >>
  metis_tac [DIVIDES_REFL,prime_def,LESS_OR_EQ, PRIME_2,
             DIVIDES_LE, DIVIDES_TRANS, DIVIDES_0] *)
QED

(*---------------------------------------------------------------------------*)
(* Every number has a prime greater than it.                                 *)
(* Proof.                                                                    *)
(* Suppose not; then there's an n such that all p greater than n are not     *)
(* prime. Consider FACT(n) + 1: it's not equal to 1, so there's a prime q    *)
(* that divides it. q also divides FACT n because q is less-than-or-equal    *)
(* to n. By DIVIDES_ADDL, this means that q=1. But then q is not prime,      *)
(* which is a contradiction.                                                 *)
(*---------------------------------------------------------------------------*)

val neq_zero = curry save_thm "neq_zero" (DECIDE ``~(x=0) = (0 < x)``);

Theorem EUCLID:
  !n . ?p . n < p /\ prime p
Proof
  LassieLib.nltac‘
    suppose not. simplify.
    we can derive 'FACT n + 1 <> 1' from [FACT_LESS, neq_zero].
    thus PRIME_FACTOR for 'FACT n + 1'.
    we further know '?q. prime q and q divides (FACT n + 1)'.
    show 'q <= n' using [NOT_LESS_EQUAL].
    show '0 < q' using [PRIME_POS] .
    show 'q divides FACT n' using [DIVIDES_FACT].
    show 'q=1' using [DIVIDES_ADDL, DIVIDES_ONE].
    show 'prime 1' using (simplify).
    [NOT_PRIME_1] solves the goal.’
  (*
  spose_not_then strip_assume_tac
   >> mp_tac (SPEC ``FACT n + 1`` PRIME_FACTOR)
   >> rw  [FACT_LESS, DECIDE ``~(x=0) = (0<x)``]
   >> metis_tac [DIVIDES_FACT, DIVIDES_ADDL, DIVIDES_ONE,
                 NOT_PRIME_1, NOT_LESS, PRIME_POS] *)
QED

val _ = export_theory();
