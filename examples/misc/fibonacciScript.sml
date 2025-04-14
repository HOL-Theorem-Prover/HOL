(* ------------------------------------------------------------------------- *)
(* The Fibonacci Numbers/Series/Sequence [1]                                 *)
(*                                                                           *)
(* Some lemmas are ported from HOL-Light's "Examples/gcdrecurrence.ml".      *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory hurdUtils numLib realTheory realLib iterateTheory;

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
  Cases_on ‘n'’ >> gs [fib, ADD1] >> intLib.ARITH_TAC
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
  Q.PAT_X_ASSUM ‘2 <= m + 1’ MP_TAC THEN ARITH_TAC
QED

(* ----------------------------------------------------------------------
    computing fibonacci numbers without taking an exponential amount of
    time over it.

    Proof translates to a WHILE-loop because I can't figure out the
    corresponding induction hypothesis, even as the loop invariant is
    quite obvious.  Counting down (rather than up) in the loop is slightly
    awkward, and perhaps this would make the inductive hypothesis worse.
    Throwing away components of the triple can't help either; the invariant
    sees starting and finishing values for all three.
   ---------------------------------------------------------------------- *)

Definition fibA_def[simp]:
  fibA 0 p t = t ∧
  fibA (SUC n) p t = fibA n t (t + p)
End

Definition fastfib_def:
  fastfib n = if n = 0 then 0 else fibA (n - 1) 0 1
End

Overload Gd[local] = “λ(i:num,p:num,t:num). 0 < i”
Overload Body[local] = “(λ(i:num,p:num,t:num). i - 1, t, t + p)”
Overload Inv[local] =
  “λL (i:num,p:num,t:num). i ≤ L ∧ p = fib (L - i) ∧ t = fib (L - i + 1)”

Theorem fibA_thm:
  fibA i p t = SND (SND (WHILE Gd Body (i,p,t)))
Proof
  map_every qid_spec_tac [‘p’, ‘t’] >> Induct_on ‘i’ >> simp[] >>
  simp [Once whileTheory.WHILE, SimpRHS]
QED

Theorem WHILE_correct:
  HOARE_SPEC (Inv L) (WHILE Gd Body) (λs. Inv L s ∧ ¬Gd s)
Proof
  irule whileTheory.WHILE_RULE >> conj_tac
  >- (qexists_tac ‘inv_image $< FST’ >>
      simp[pairTheory.FORALL_PROD, relationTheory.WF_inv_image]) >>
  simp[pairTheory.FORALL_PROD, whileTheory.HOARE_SPEC_DEF] >>
  rpt strip_tac >> simp[Once fib_def, SimpRHS]
QED

Theorem fastfib_correct:
  fastfib n = fib n
Proof
  rw[fastfib_def, fibA_thm]
  >- simp[Once fib_def] >>
  qmatch_abbrev_tac ‘SND (SND (prog _)) = _’>>
  assume_tac (GEN_ALL $ SRULE[whileTheory.HOARE_SPEC_DEF] WHILE_correct) >>
  gvs[] >>
  ‘Inv (n - 1) (n - 1, 0, 1)’
    by (simp[] >> conj_tac >> simp[Once fib_def]) >>
  first_x_assum dxrule >>
  ‘∃i' p' t'. prog (n - 1, 0, 1) = (i',p',t')’ by metis_tac[pairTheory.PAIR] >>
  simp[]
QED

(*
lo, exponential speedup

 time EVAL “fastfib 10”
 time EVAL “fib 10”  (* 0.006s *)

 time EVAL “fib 20”      (* 0.55s *)
 time EVAL “fastfib 20”  (* 0.0012s *)

 time EVAL “fib 25”      (* 5.9s *)
 time EVAL “fastfib 25”  (* 0.00204s *)
*)

val _ = export_theory ();

(* References:

  [1] https://en.wikipedia.org/wiki/Fibonacci_sequence

 *)
