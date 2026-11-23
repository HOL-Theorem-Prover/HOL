(* ========================================================================= *)
(* FILE          : hh02_arithScript.sml                                      *)
(* DESCRIPTION   : HolyHammer examples: natural numbers                      *)
(* ADAPTED FROM  : an example from Thibault Gauthier's HolyHammer demo.      *)
(*                                                                           *)
(* Every proof below calls the hammer: each hh runs HolyHammer when the      *)
(* theory is built, so building needs a prover (see README.md).  The         *)
(* comment after each hh is the verified, minimised proof that               *)
(* HolyHammer printed when the example was written.                          *)
(* ========================================================================= *)
Theory hh02_arith
Ancestors
  arithmetic divides gcd
Libs
  holyHammer

(* -------------------------------------------------------------------------
   Natural-number arithmetic splits into two kinds of goal.

   Linear arithmetic (+, -, <, constants) is decided by DECIDE_TAC and
   intLib.ARITH_TAC; do not use the hammer for it.

   Everything else (multiplication, DIV and MOD, EXP, divisibility,
   parity, gcd, primes) is outside those decision procedures, and the
   library has a lemma for almost every fact you might need.  That is
   the kind of goal shown here.  The provers do not "know" arithmetic: to
   them, + and * are uninterpreted function symbols, and all the
   arithmetic knowledge comes from the selected library lemmas.
   ------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------
   Rings without negation: subtraction and distributivity
   ------------------------------------------------------------------------- *)

Theorem exp_sub_mul:
  a <= b ==> g ** (b - a) * g ** a = g ** b
Proof
  hh
  (* metis_tac [SUB_ADD, EXP_ADD] *)
QED

Theorem sub_sub_add:
  (a - b) - c = a - (b + c)
Proof
  hh
  (* metis_tac [SUB_RIGHT_SUB] *)
QED

Theorem mul_sub_distrib:
  a * (b - c) = a * b - a * c
Proof
  hh
  (* metis_tac [LEFT_SUB_DISTRIB] *)
QED

Theorem le_mul_right:
  x <= y ==> x * z <= y * z
Proof
  hh
  (* metis_tac [LESS_MONO_MULT] *)
QED

Theorem mul_cancel_left:
  0 < x /\ x * y = x * z ==> y = z
Proof
  hh
  (* metis_tac [MULT_LEFT_CANCEL, NOT_ZERO_LT_ZERO] *)
QED

Theorem max_plus_min:
  MAX a b + MIN a b = a + b
Proof
  hh
  (* metis_tac [MAX_ALT, MIN_ALT, ADD_SYM] *)
QED

(* A non-linear identity.  simp [], metis_tac [] and DECIDE_TAC all fail
   on it.  The hammer has to do real equational reasoning with seven
   lemmas, including the binary numeral encoding (BIT1, BIT2,
   NUMERAL_DEF), which is how the provers learn that 2 = 1 + 1.  It took
   about ten seconds. *)
Theorem suc_squared:
  SUC n ** 2 = n ** 2 + 2 * n + 1
Proof
  hh
  (* metis_tac [ADD_CLAUSES, MULT_CLAUSES, RIGHT_ADD_DISTRIB, EXP_2,
                NUMERAL_DEF, BIT1, BIT2] *)
QED

(* -------------------------------------------------------------------------
   Division and modulus
   ------------------------------------------------------------------------- *)

Theorem mul_div_cancel:
  0 < n ==> (m * n) DIV n = m
Proof
  hh
  (* metis_tac [MULT_DIV] *)
QED

Theorem div_mul_le:
  0 < n ==> (m DIV n) * n <= m
Proof
  hh
  (* metis_tac [DIV_MULT_LE] *)
QED

Theorem half_le:
  n DIV 2 <= n
Proof
  hh
  (* metis_tac [numeralTheory.numeral_lt, NUMERAL_DEF, ALT_ZERO,
                DIV_LESS_EQ] *)
QED

Theorem mod_bound:
  0 < n ==> m MOD n < n
Proof
  hh
  (* metis_tac [MOD_LESS] *)
QED

Theorem mod_add_multiple:
  0 < n ==> (m * n + k) MOD n = k MOD n
Proof
  hh
  (* metis_tac [MOD_TIMES] *)
QED

Theorem mod_add:
  0 < n ==> (a + b) MOD n = (a MOD n + b MOD n) MOD n
Proof
  hh
  (* metis_tac [MOD_PLUS] *)
QED

(* Adding the divisor adds one to the quotient.  The library states the
   general version, (r * n + m) DIV n = r + m DIV n (ADD_DIV_ADD_DIV);
   the hammer instantiated it with r = 1. *)
Theorem add_div_self:
  0 < n ==> (m + n) DIV n = m DIV n + 1
Proof
  hh
  (* metis_tac [ADD_SYM, MULT_CLAUSES, ADD_DIV_ADD_DIV] *)
QED

(* -------------------------------------------------------------------------
   Parity
   ------------------------------------------------------------------------- *)

(* The product of two consecutive numbers is even: EVEN_MULT reduces it
   to "n is even or n + 1 is even", and EVEN with ADD1 finishes.  Again,
   simp [] and metis_tac [] alone do not prove it. *)
Theorem even_consecutive_product:
  EVEN (n * (n + 1))
Proof
  hh
  (* metis_tac [EVEN, EVEN_MULT, ADD1] *)
QED

Theorem even_then_odd:
  EVEN n ==> ~EVEN (n + 1)
Proof
  hh
  (* metis_tac [EVEN, ADD1] *)
QED

Theorem odd_product:
  ODD (m * n) <=> ODD m /\ ODD n
Proof
  hh
  (* metis_tac [ODD_MULT] *)
QED

Theorem odd_iff_mod_two:
  ODD n <=> n MOD 2 = 1
Proof
  hh
  (* metis_tac [MOD_2, ONE, EVEN_ODD, SUC_NOT] *)
QED

Theorem even_linear_comb:
  EVEN m /\ EVEN n ==> EVEN (m * k + n)
Proof
  hh
  (* metis_tac [EVEN_MULT, EVEN_ADD] *)
QED

Theorem even_half_double:
  EVEN n ==> (n DIV 2) * 2 = n
Proof
  hh
  (* metis_tac [MULT_COMM, EVEN_EXISTS, MULT_DIV_2] *)
QED

(* Parity and divisibility are separate theories; the bridge between
   them is EVEN_ALT in dividesTheory. *)
Theorem divides_two_even:
  divides 2 n <=> EVEN n
Proof
  hh
  (* metis_tac [EVEN_ALT] *)
QED

(* -------------------------------------------------------------------------
   Divisibility, gcd and primes
   ------------------------------------------------------------------------- *)

Theorem divides_sum:
  divides a b /\ divides a c ==> divides a (b + c)
Proof
  hh
  (* metis_tac [DIVIDES_ADD_1] *)
QED

Theorem divides_multiple:
  divides a b ==> divides a (b * c)
Proof
  hh
  (* metis_tac [DIVIDES_MULT] *)
QED

Theorem divisor_le:
  0 < b /\ divides a b ==> a <= b
Proof
  hh
  (* metis_tac [prim_recTheory.LESS_REFL, DIVIDES_LEQ_OR_ZERO] *)
QED

(* gcdTheory states this with the arguments of gcd swapped
   (GCD_ADD_R_THM); the hammer adds GCD_SYM. *)
Theorem gcd_add_left:
  gcd (a + b) b = gcd a b
Proof
  hh
  (* metis_tac [GCD_SYM, GCD_ADD_R_THM] *)
QED

Theorem gcd_common_factor:
  gcd (k * a) (k * b) = k * gcd a b
Proof
  hh
  (* metis_tac [GCD_COMMON_FACTOR] *)
QED

(* Euclid's lemma, in two flavours. *)
Theorem euclid_prime:
  prime p /\ divides p (a * b) /\ ~divides p a ==> divides p b
Proof
  hh
  (* metis_tac [P_EUCLIDES] *)
QED

Theorem euclid_coprime:
  gcd a b = 1 /\ divides a (b * c) ==> divides a c
Proof
  hh
  (* metis_tac [L_EUCLIDES, GCD_SYM] *)
QED

Theorem prime_coprime_or_divides:
  prime p ==> gcd p n = 1 \/ divides p n
Proof
  hh
  (* metis_tac [PRIME_GCD] *)
QED

(* -------------------------------------------------------------------------
   Powers and factorials
   ------------------------------------------------------------------------- *)

Theorem two_exp_strict_mono:
  m < n ==> 2 ** m < 2 ** n
Proof
  hh
  (* metis_tac [NUMERAL_DEF, numeralTheory.numeral_lt, EXP_BASE_LT_MONO] *)
QED

Theorem lt_exp_self:
  1 < b ==> n < b ** n
Proof
  hh
  (* metis_tac [X_LT_EXP_X] *)
QED

Theorem exp_exp_mul:
  (a ** m) ** n = a ** (n * m)
Proof
  hh
  (* metis_tac [EXP_EXP_MULT, MULT_COMM] *)
QED

Theorem fact_positive:
  0 < FACT n
Proof
  hh
  (* metis_tac [FACT_LESS] *)
QED
