(* ------------------------------------------------------------------------- *)
(* The Fibonacci Numbers/Series/Sequence [1]                                 *)
(*                                                                           *)
(* Some lemmas are ported from HOL-Light's "Examples/gcdrecurrence.ml".      *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory hurdUtils numLib realTheory realLib intLib;

val _ = intLib.deprecate_int ();
val _ = numLib.prefer_num ();

val _ = new_theory "fibonacci";

val num_INDUCTION = numTheory.INDUCTION;
val ARITH_RULE    = numLib.DECIDE;

(* 0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, ... *)
Definition fib_def :
    fib (n :num) = if n = 0 then (0 :num) else
                   if n = 1 then 1 else fib (n - 1) + fib (n - 2)
End

Overload Fibonacci[inferior] = “fib”

Theorem fib :
    fib 0 = 0 /\ fib 1 = 1 /\ !n. fib(n + 2) = fib(n + 1) + fib(n)
Proof
    rpt STRIP_TAC
 >> rw [Once fib_def]
QED

(* NOTE: This was in "examples/misc/fibmod3Script.sml", where Fib is defined
   differently: Fib(0) = Fib(1) = 1, i.e. Fib(n) = fib (SUC n) in this theory.
 *)
Theorem fibmod:
  ∀n. EVEN (fib (SUC n)) ⇔ n MOD 3 = 2
Proof
  recInduct fib_ind >> rw[] >>
  ONCE_REWRITE_TAC [fib_def] >> rw[] >>
  gs[EVEN_ADD, ADD1] >>
  Cases_on ‘n’ >> gs [ADD1] \\
  Cases_on ‘n'’ >> gs [fib, ADD1] >> ARITH_TAC
QED

Theorem FIB_EQ_0 :
    !n. fib n = 0 <=> n = 0
Proof
  HO_MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[fib] THEN
  HO_MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[fib, ARITH_RULE “SUC(SUC n) = n + 2”, ADD_EQ_0] THEN
  SIMP_TAC arith_ss[ADD1, ADD_EQ_0, fib]
QED

Theorem FIB_EQ_1 :
    !n. fib n = 1 <=> n = 1 \/ n = 2
Proof
  HO_MATCH_MP_TAC num_INDUCTION THEN SIMP_TAC arith_ss[fib] THEN
  HO_MATCH_MP_TAC num_INDUCTION THEN SIMP_TAC arith_ss[fib] THEN
  REWRITE_TAC[fib, ARITH_RULE “SUC(SUC n) = n + 2”, ADD1] THEN
  RW_TAC arith_ss[FIB_EQ_0, ADD_EQ_0, ARITH_RULE
   “m + n = 1 <=> m = 0 /\ n = 1 \/ m = 1 /\ n = 0”]
QED

Theorem FIB_MONO_SUC :
    !n. fib n <= fib (SUC n)
Proof
    rpt STRIP_TAC
 >> ‘n = 0 \/ 0 < n’ by rw []
 >- simp [fib]
 >> qabbrev_tac ‘k = n - 1’
 >> ‘n = k + 1’ by rw [Abbr ‘k’]
 >> rw [ADD1, fib]
QED

Theorem FIB_INCREASES_LE :
    !m n. m <= n ==> fib m <= fib n
Proof
  HO_MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
  REWRITE_TAC[LE_REFL, LE_TRANS, FIB_MONO_SUC]
QED

Theorem FIB_INCREASES_LT :
    !m n. 2 <= m /\ m < n ==> fib m < fib n
Proof
  INDUCT_TAC THEN RW_TAC arith_ss [ADD1] THEN
  Q_TAC (TRANS_TAC LTE_TRANS) `fib(m + 2)` THEN
  reverse CONJ_TAC
  >- (MATCH_MP_TAC FIB_INCREASES_LE >> rw []) \\
  REWRITE_TAC[fib, ARITH_RULE “m < m + n <=> ~(n = 0)”, FIB_EQ_0] THEN
  ASM_ARITH_TAC
QED

val _ = export_theory ();

(* References:

  [1] https://en.wikipedia.org/wiki/Fibonacci_sequence
*)
