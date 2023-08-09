(* ------------------------------------------------------------------------- *)
(* The Helper File                                                           *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "helperTwosq";

(* ------------------------------------------------------------------------- *)


(* open dependent theories *)
val _ = load("helperFunctionTheory");
open helperFunctionTheory;
open helperSetTheory;
open helperNumTheory;

(* arithmeticTheory -- load by default *)
open arithmeticTheory pred_setTheory;
open dividesTheory;
open gcdTheory; (* for GCD_IS_GREATEST_COMMON_DIVISOR *)

val _ = load("logPowerTheory");
open logPowerTheory; (* for SQRT *)

open whileTheory; (* for HOARE_SPEC_DEF *)


(* ------------------------------------------------------------------------- *)
(* Helper Theorems Documentation                                             *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   pairing f         = !u x y. f u x /\ f u y ==> x = y
   unique_bool f a b = f a b /\ !x y. f x y ==> (x = a) /\ (y = b)
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   Number Theorems:
   prime_non_quad    |- !p. prime p ==> ~(4 divides p)
   prime_mod_eq_0    |- !p q. prime p /\ 1 < q ==> (p MOD q = 0 <=> q = p)
   even_by_mod_4     |- !n. EVEN n <=> n MOD 4 = 0 \/ n MOD 4 = 2
   odd_by_mod_4      |- !n. ODD n <=> n MOD 4 = 1 \/ n MOD 4 = 3
   mod_4_even        |- !n. EVEN n <=> n MOD 4 IN {0; 2}
   mod_4_odd         |- !n. ODD n <=> n MOD 4 IN {1; 3}
   mod_4_square      |- !n. n ** 2 MOD 4 IN {0; 1}
   mod_4_not_squares |- !n. n MOD 4 = 3 ==> !x y. n <> x ** 2 + y ** 2

   Arithmetic Theorems:
   four_squares_identity     |- !a b c d. b * d <= a * c ==>
                                  (a ** 2 + b ** 2) * (c ** 2 + d ** 2) =
                                  (a * d + b * c) ** 2 + (a * c - b * d) ** 2
   four_squares_identity_alt |- !a b c d. a * c <= b * d ==>
                                  (a ** 2 + b ** 2) * (c ** 2 + d ** 2) =
                                  (a * d + b * c) ** 2 + (b * d - a * c) ** 2

   Square Sum Theorems:
   squares_sum_eq_0          |- !a b. a ** 2 + b ** 2 = 0 <=> a = 0 /\ b = 0
   squares_sum_identity_1    |- !a b c d. a ** 2 + b ** 2 = c ** 2 + d ** 2 ==>
                                         (a * d - b * c) * (a * d + b * c) =
                                         (a ** 2 + b ** 2) * (d ** 2 - b ** 2)
   squares_sum_identity_2    |- !a b c d. a ** 2 + b ** 2 = c ** 2 + d ** 2 ==>
                                         (b * c - a * d) * (a * d + b * c) =
                                         (a ** 2 + b ** 2) * (b ** 2 - d ** 2)
   squares_sum_inequality    |- !a b c d. a ** 2 + b ** 2 = c ** 2 + d ** 2 /\
                                          0 < b /\ 0 < d ==> a * c < a ** 2 + b ** 2
   squares_sum_inequality_1  |- !a b c d. a ** 2 + b ** 2 = c ** 2 + d ** 2 /\
                                          0 < b /\ 0 < c ==> a * d < a ** 2 + b ** 2
   squares_sum_inequality_2  |- !a b c d. a ** 2 + b ** 2 = c ** 2 + d ** 2 /\
                                          0 < a /\ 0 < d ==> b * c < a ** 2 + b ** 2
   squares_sum_prime_coprime |- !p a b. prime p /\ p = a ** 2 + b ** 2 ==> coprime a b
   squares_sum_prime_thm     |- !p a b c d. prime p /\
                                          p = a ** 2 + b ** 2 /\ p = c ** 2 + d ** 2 /\
                                          a * d = b * c ==> a = c /\ b = d

   Set Theorems:
   doublet_eq          |- !a b c d. {a; b} = {c; d} <=> a = c /\ b = d \/ a = d /\ b = c
   doublet_finite      |- !a b. FINITE {a; b}
   doublet_card        |- !a b. a <> b ==> CARD {a; b} = 2
   partition_three_special_card
                       |- !s a b c. FINITE s /\ s = a UNION b UNION c /\
                                    a INTER b = {} /\ b INTER c = {} /\ a INTER c = {} /\
                                    CARD a = CARD c ==> CARD s = 2 * CARD a + CARD b
   set_partition_bij_card
                     |- !f s a b. FINITE s /\ s = a UNION b /\ a INTER b = {} /\ BIJ f a b ==>
                                  CARD s = 2 * CARD a
   set_partition_bij_card_even
                     |- !f s a b. FINITE s /\ s = a UNION b /\ a INTER b = {} /\ BIJ f a b ==>
                                  EVEN (CARD s)
   set_partition_bij_give_bij
                     |- !f s t a b c d. s = a UNION b /\ a INTER b = {} /\
                                        t = c UNION d /\ c INTER d = {} /\
                                        BIJ f a d /\ BIJ f b c ==> BIJ f s t

   WHILE Loop Specification:
   WHILE_RULE_PRE_POST
                     |- (!x. Invariant x /\ Guard x ==> Measure (Command x) < Measure x) /\
                        (!x. Precond x ==> Invariant x) /\
                        (!x. Invariant x /\ ~Guard x ==> Postcond x) /\
                        HOARE_SPEC (\x. Invariant x /\ Guard x) Command Invariant ==>
                        HOARE_SPEC Precond (WHILE Guard Command) Postcond

   Pair exists and exists uniquely:
   pair_exists_iff         |- !f. (?(u,v). f u v) <=> ?u v. f u v
   pair_exists_unique_imp  |- !f. (?!(u,v). f u v) ==> ?!u v. f u v

   Pairing Function:
   pair_exists_unique_fun  |- !f. (?!(u,v). f u v) ==> pairing f
   pair_exists_unique_thm  |- !f. (?!(u,v). f u v) <=> (?!u v. f u v) /\ pairing f
   pair_exists_unique_thm_1|- !f. (?!(u,v). f u v) ==> (?!u v. f u v) /\ pairing f
   pair_exists_unique_thm_2|- !f. (?!u v. f u v) /\ pairing f ==> ?!(u,v). f u v
   pair_exists_unique_alt  |- !f. pairing f ==> ((?!(u,v). f u v) <=> ?!u v. f u v)

   Unique Boolean Function:
   unique_bool_unique_values |- !f a b. unique_bool f a b ==> ?!u v. f u v
   unique_bool_unique_pair   |- !f a b. unique_bool f a b ==> ?!(u,v). f u v

   An Example:
   pairing_for_less          |- !m. (!x y. x < m /\ y < m ==> x = y) ==> m <= 1
   exists_unique_values_less |- (?!m n. n < m) <=> T
   exists_unique_pair_less   |- (?!(m,n). n < m) <=> F

*)

(* ------------------------------------------------------------------------- *)
(* Arithmetic Theorems                                                       *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Number Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* remove overload of TWICE, SQ *)
val _ = clear_overloads_on "TWICE";
val _ = clear_overloads_on "SQ";

(* Overloading for a square n *)
(* val _ = overload_on ("square", ``\n:num. ?k. n = k ** 2``); *)
(* Make square in computeLib, cannot be an overload. *)
(* see square_def in logPowerTheory. *)

(* Theorem: prime p ==> ~(4 divides p) *)
(* Proof:
   By contradiction, suppose 4 divides p.
   Then p = 4        by prime_def
          = 2 * 2    by arithmetic
   Thus p = 2        by divides_def, prime_def
    ==> 4 = 2, which is a contradiction.
*)
Theorem prime_non_quad:
  !p. prime p ==> ~(4 divides p)
Proof
  rpt strip_tac >>
  `4 <> 1 /\ 2 <> 1` by fs[] >>
  `p = 4` by metis_tac[prime_def] >>
  `_ = 2 * 2` by decide_tac >>
  `p = 2` by metis_tac[divides_def, prime_def] >>
  fs[]
QED

(* Theorem: prime p /\ 1 < q ==> (p MOD q = 0 <=> q = p) *)
(* Proof:
   If part: p MOD q = 0 ==> q = p
      Note q divides p       by DIVIDES_MOD_0
       and q <> 1            by 1 < q
        so q = p             by prime_def
   Only-if part: q = p ==> p MOD q = 0
      This is true           by DIVMOD_ID, by 0 < q.
*)
Theorem prime_mod_eq_0:
  !p q. prime p /\ 1 < q ==> (p MOD q = 0 <=> q = p)
Proof
  rw[EQ_IMP_THM] >>
  `q divides p` by rw[DIVIDES_MOD_0] >>
  `q <> 1` by decide_tac >>
  metis_tac[prime_def]
QED

(* Theorem: EVEN n <=> n MOD 4 = 0 \/ n MOD 4 = 2 *)
(* Proof:
   Since 2 divides 4                        by divides_def
   Hence (n MOD 4) MOD 2 = n MOD 2          by DIVIDES_MOD_MOD
   If part: EVEN n ==> (n MOD 4 = 0) \/ (n MOD 4 = 2)
      Note EVEN n ==> n MOD 2 = 0           by EVEN_MOD2
      By contradiction, suppose (n MOD 4 <> 0) /\ (n MOD 4 <> 2).
      Since n MOD 4 < 4              by MOD_LESS
         so n MOD 4 = 1 or n MOD 4 = 3.
      If n MOD 4 = 1,
         Then (n MOD 4) MOD 2 = 1 MOD 2 = 1 <> 0, a contradiction.
      If n MOD 4 = 3,
         Then (n MOD 4) MOD 2 = 3 MOD 2 = 1 <> 0, a contradiction.
   Only-if part: (n MOD 4 = 0) \/ (n MOD 4 = 2) ==> EVEN n
      If n MOD 4 = 0,
         Then n MOD 2 = 0 MOD 2 = 0
           so EVEN n                 by EVEN_DOUBLE
      If n MOD 4 = 2,
         Then n MOD 2 = 2 MOD 2 = 0
           so EVEN n                 by EVEN_DOUBLE
*)
Theorem even_by_mod_4:
  !n. EVEN n <=> n MOD 4 = 0 \/ n MOD 4 = 2
Proof
  rpt strip_tac >>
  `2 divides 4` by rw[divides_def] >>
  `n MOD 2 = (n MOD 4) MOD 2` by rw[DIVIDES_MOD_MOD] >>
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `n MOD 2 = 0` by rw[GSYM EVEN_MOD2] >>
    `n <> 0` by metis_tac[ZERO_MOD, DECIDE``0 < 4``] >>
    `n MOD 4 < 4` by rw[MOD_LESS] >>
    `(n MOD 4 = 1) \/ (n MOD 4 = 3)` by decide_tac >| [
      `1 MOD 2 = 1` by rw[] >>
      fs[],
      `3 MOD 2 = 1` by rw[] >>
      fs[]
    ],
    `0 MOD 2 = 0` by rw[] >>
    fs[EVEN_MOD2],
    `2 MOD 2 = 0` by rw[] >>
    fs[EVEN_MOD2]
  ]
QED

(* Theorem: ODD n <=> n MOD 4 = 1 \/ n MOD 4 = 3 *)
(* Proof:
   Since 2 divides 4                        by divides_def
   Hence (n MOD 4) MOD 2 = n MOD 2          by DIVIDES_MOD_MOD
   If part: ODD n ==> (n MOD 4 = 1) \/ (n MOD 4 = 3)
      Note ODD n ==> n MOD 2 = 1           by ODD_MOD2
      By contradiction, suppose (n MOD 4 <> 1) /\ (n MOD 4 <> 3).
      Since n MOD 4 < 4              by MOD_LESS
         so n MOD 4 = 0 or n MOD 4 = 2.
      If n MOD 4 = 0,
         Then n MOD 2 = 0 MOD 2 = 0 <> 1, a contradiction.
      If n MOD 4 = 2,
         Then n MOD 2 = 2 MOD 2 = 0 <> 1, a contradiction.
   Only-if part: (n MOD 4 = 1) \/ (n MOD 4 = 3) ==> ODD n
      If n MOD 4 = 1,
         Then n MOD 2 = 1 MOD 1 = 1
           so ODD n                  by ODD_MOD2
      If n MOD 4 = 3,
         Then n MOD 2 = 3 MOD 1 = 1
           so ODD n                  by ODD_MOD2
*)
Theorem odd_by_mod_4:
  !n. ODD n <=> n MOD 4 = 1 \/ n MOD 4 = 3
Proof
  rpt strip_tac >>
  `2 divides 4` by rw[divides_def] >>
  `n MOD 2 = (n MOD 4) MOD 2` by rw[DIVIDES_MOD_MOD] >>
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `n MOD 2 = 1` by rw[GSYM ODD_MOD2] >>
    `n <> 0` by metis_tac[EVEN_0, EVEN_ODD] >>
    `n MOD 4 < 4` by rw[MOD_LESS] >>
    `(n MOD 4 = 0) \/ (n MOD 4 = 2)` by decide_tac >| [
      `0 MOD 2 = 0` by rw[] >>
      fs[],
      `2 MOD 2 = 0` by rw[] >>
      fs[]
    ],
    `1 MOD 2 = 1` by rw[] >>
    fs[ODD_MOD2],
    `3 MOD 2 = 1` by rw[] >>
    fs[ODD_MOD2]
  ]
QED

(* Theorem: EVEN n <=> n MOD 4 IN {0; 2} *)
(* Proof:
       EVEN n
   <=> ?k. n = 2 * k                   by EVEN_EXISTS
   <=> ?k. n MOD 4
         = (2 * k) MOD 4
         = (2 * k MOD 4) MOD 4         by MOD_TIMES
         = (0 or 2 or 4 or 6) MOD 4    by MOD_LESS
         = 0 or 2                      by arithmetic
*)
Theorem mod_4_even:
  !n. EVEN n <=> n MOD 4 IN {0; 2}
Proof
  rw[EVEN_EXISTS, EQ_IMP_THM] >| [
    `(2 * m) MOD 4 = (2 * m MOD 4) MOD 4` by rw[MOD_TIMES] >>
    `m MOD 4 < 4` by rw[] >>
    qabbrev_tac `x = m MOD 4` >>
    (`(x = 0) \/ (x = 1) \/ (x = 2) \/ (x = 3)` by decide_tac >> rfs[]),
    fs[MOD_EQN] >>
    qexists_tac `2 * c` >>
    decide_tac,
    fs[MOD_EQN] >>
    qexists_tac `2 * c + 1` >>
    decide_tac
  ]
QED

(* Theorem: ODD n <=> n MOD 4 IN {1; 3} *)
(* Proof:
       ODD n
   <=> ~EVEN n                  by EVEN_ODD
   <=> n MOD 4 NOTIN {0; 2}     by mod_4_even
   <=> n MOD 4 IN {1; 3}        by MOD_LESS
*)
Theorem mod_4_odd:
  !n. ODD n <=> n MOD 4 IN {1; 3}
Proof
  rpt strip_tac >>
  `n MOD 4 < 4` by rw[] >>
  `n MOD 4 NOTIN {0; 2} <=> n MOD 4 IN {1; 3}` by rw[] >>
  metis_tac[mod_4_even, EVEN_ODD]
QED

(* Theorem: (n ** 2) MOD 4 IN {0; 1} *)
(* Proof:
   Let m = n MOD 4.
   Then m < 4           by MOD_LESS
        (n ** 2) MOD 4
      = m ** 2 MOD 4    by MOD_EXP
      = 0 ** 2 MOD 4 or
        1 ** 2 MOD 4 or
        2 ** 2 MOD 4 or
        3 ** 2 MOD 4    by m < 4
      = 0 or 1          by arithmetic
*)
Theorem mod_4_square:
  !n. (n ** 2) MOD 4 IN {0; 1}
Proof
  rpt strip_tac >>
  qabbrev_tac `m = n MOD 4` >>
  `m < 4` by rw[MOD_LESS, Abbr`m`] >>
  `(n ** 2) MOD 4 = m ** 2 MOD 4` by rw[MOD_EXP, Abbr`m`] >>
  (`(m = 0) \/ (m = 1) \/ (m = 2) \/ (m = 3)` by decide_tac >> fs[])
QED

(* Theorem: n MOD 4 = 3 ==> !x y. n <> x ** 2 + y ** 2 *)
(* Proof:
   By contradiction, suppose n = x ** 2 + y ** 2.
      n MOD 4
    = (x ** 2 + y ** 2) MOD 4
    = ((x ** 2) MOD 4 + (y ** 2) MOD 4) MOD 4    by MOD_PLUS
    = (0 or 1 + 0 or 1) MOD 4                    by mod_4_square
    = (0 or 1 or 2) MOD 4                        by arithmetic
   This contradicts n MOD 4 = 3.
*)
Theorem mod_4_not_squares:
  !n. n MOD 4 = 3 ==> !x y. n <> x ** 2 + y ** 2
Proof
  rpt strip_tac >>
  qabbrev_tac `a = x ** 2` >>
  qabbrev_tac `b = y ** 2` >>
  `n MOD 4 = ((a MOD 4) + (b MOD 4)) MOD 4` by rw[MOD_PLUS] >>
  `a MOD 4 IN {0; 1} /\ b MOD 4 IN {0; 1}` by rw[mod_4_square, Abbr`a`, Abbr`b`] >>
  fs[]
QED


(* ------------------------------------------------------------------------- *)
(* Arithmetic Theorems                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: b * d <= a * c ==>
            (a ** 2 + b ** 2) * (c ** 2 + d ** 2) =
            (a * d + b * c) ** 2 + (a * c - b * d) ** 2 *)
(* Proof:
     (a * d + b * c) ** 2 + (a * c - b * d) ** 2
   = (a * d) ** 2 + (b * c) ** 2 + 2 * (a * d) * (b * c) +       by binomial_add
     (a * c) ** 2 + (b * d) ** 2 - 2 * (a * c) * (b * d)         by binomial_sub
   = (a * d) ** 2 + (b * c) ** 2 + (a * c) ** 2 + (b * d) ** 2   by arithmetic
   = a ** 2 * c ** 2 + a ** 2 * d ** 2 + b ** 2 * c ** 2 + b ** 2 * d ** 2
   = a ** 2 * (c ** 2 + d ** 2) + b ** 2 * (c ** 2 + d ** 2)
   = (a ** 2 + b ** 2) * (c ** 2 + d ** 2)
*)
Theorem four_squares_identity:
  !a b c d. b * d <= a * c ==>
            (a ** 2 + b ** 2) * (c ** 2 + d ** 2) =
            (a * d + b * c) ** 2 + (a * c - b * d) ** 2
Proof
  rpt strip_tac >>
  `(a * d + b * c) ** 2 + (a * c - b * d) ** 2
  = (a * d) ** 2 + (b * c) ** 2 + 2 * (a * d) * (b * c) +
    ((a * c) ** 2 + (b * d) ** 2 - 2 * (a * c) * (b * d))` by rw[binomial_add, binomial_sub] >>
  `_ = (a * d) ** 2 + (b * c) ** 2 + 2 * (a * d) * (b * c) +
        ((a * c) ** 2 + (b * d) ** 2) - 2 * (a * c) * (b * d)` by rw[binomial_means, LESS_EQ_ADD_SUB] >>
  `_ = (a * d) ** 2 + (b * c) ** 2 + (a * c) ** 2 + (b * d) ** 2 +
         2 * a * b * c * d - 2 * a * b * c * d` by decide_tac >>
  `_ = (a * d) ** 2 + (b * c) ** 2 + (a * c) ** 2 + (b * d) ** 2` by decide_tac >>
  `_ = a ** 2 * c ** 2 + a ** 2 * d ** 2 + b ** 2 * c ** 2 + b ** 2 * d ** 2` by rw[EXP_BASE_MULT] >>
  `_ = a ** 2 * (c ** 2 + d ** 2) + b ** 2 * (c ** 2 + d ** 2)` by decide_tac >>
  `_ = (a ** 2 + b ** 2) * (c ** 2 + d ** 2)` by decide_tac >>
  decide_tac
QED

(* Theorem: a * c <= b * d ==>
            (a ** 2 + b ** 2) * (c ** 2 + d ** 2) =
            (a * d + b * c) ** 2 + (b * d - a * c) ** 2 *)
(* Proof: by four_squares_identity, ADD_COMM *)
Theorem four_squares_identity_alt:
  !a b c d. a * c <= b * d ==>
            (a ** 2 + b ** 2) * (c ** 2 + d ** 2) =
            (a * d + b * c) ** 2 + (b * d - a * c) ** 2
Proof
  metis_tac[four_squares_identity, ADD_COMM]
QED

(* ------------------------------------------------------------------------- *)
(* Squares Sum Theorems                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: a ** 2 + b ** 2 = 0 <=> a = 0 /\ b = 0 *)
(* Proof:
       a ** 2 + b ** 2 = 0
   <=> a ** 2 = 0 /\ b ** 2 = 0    by ADD_EQ_0
   <=> a * a = 0  /\ b * b = 0     by EXP_2
   <=> a = 0      /\ b = 0         by MULT_EQ_0
*)
Theorem squares_sum_eq_0:
  !a b. a ** 2 + b ** 2 = 0 <=> a = 0 /\ b = 0
Proof
  rw[EQ_IMP_THM]
QED

(* Theorem: a ** 2 + b ** 2 = c ** 2 + d ** 2 ==>
           (a * d - b * c) * (a * d + b * c) =
           (a ** 2 + b ** 2) * (d ** 2 - b ** 2) *)
(* Proof:
   Let p = a ** 2 + b ** 2,
   then p = c ** 2 + d ** 2.
        (a * d - b * c) * (a * d + b * c)
      = (a * d) * (a * d) - (b * c) * (b * c)      by difference_of_squares_alt
      = (a * a) * (d * d) - (c * c) * (b * b)      by arithmetic
      = (p - b * b) * d * d - (p - d * d) * b * b  by EXP_2
      = (p * d * d - b * b * d * d) - (p * b * b - d * d * b * b)
      = p * d * d - b * b * d * d + d * d * b * b - p * b * b
      = p * d * d - p * b * b
      = p * (d * d - b * b)
      = p * (d ** 2 - b ** 2)                      by EXP_2
*)
Theorem squares_sum_identity_1:
  !a b c d. a ** 2 + b ** 2 = c ** 2 + d ** 2 ==>
            (a * d - b * c) * (a * d + b * c) =
            (a ** 2 + b ** 2) * (d ** 2 - b ** 2)
Proof
  rpt strip_tac >>
  qabbrev_tac `p = a ** 2 + b ** 2` >>
  `(a * d - b * c) * (a * d + b * c) = (a * d) * (a * d) - (b * c) * (b * c)` by rw[difference_of_squares_alt] >>
  `_ = (a * a) * (d * d) - (c * c) * (b * b)` by fs[] >>
  `_ = (a ** 2) * (d ** 2) - (c ** 2) * (b ** 2)` by fs[GSYM EXP_2] >>
  `_ = (p - b ** 2) * d ** 2 - (p - d ** 2) * b ** 2` by fs[Abbr`p`] >>
  `_ = (p - b * b) * d * d - (p - d * d) * b * b` by fs[GSYM EXP_2] >>
  `_ = (p * d * d - b * b * d * d) - (p * b * b - d * d * b * b)` by decide_tac >>
  `_ = p * d * d - b * b * d * d + d * d * b * b - p * b * b` by simp[] >>
  `_ = p * d * d - p * b * b` by simp[] >>
  `_ = p * (d * d - b * b)` by decide_tac >>
  fs[GSYM EXP_2]
QED

(* Theorem: a ** 2 + b ** 2 = c ** 2 + d ** 2 ==>
           (b * c - a * d) * (a * d + b * c) =
           (a ** 2 + b ** 2) * (b ** 2 - d ** 2) *)
(* Proof:
   Let p = a ** 2 + b ** 2,
   then p = c ** 2 + d ** 2.
        (b * c - a * d) * (a * d + b * c)
      = (b * c) * (b * c) - (a * d) * (a * d)       by difference_of_squares_alt
      = (c * c) * (b * b) - (a * a) * (d * d)       by arithmetic
      = (p - d * d) * b * b - (p - b * b) * d * d   by EXP_2
      = (p * b * b - d * d * b * b) - (p * d * d - b * b * d * d)
      = p * b * b - d * d * b * b + b * b * d * d - p * d * d
                                                    by SUB_SUB, b * b <= p
      = p * b * b - p * d * d
      = p * (b * b - d * d)
      = p * (b ** 2 - d ** 2)
*)
Theorem squares_sum_identity_2:
  !a b c d. a ** 2 + b ** 2 = c ** 2 + d ** 2 ==>
            (b * c - a * d) * (a * d + b * c) =
            (a ** 2 + b ** 2) * (b ** 2 - d **  2)
Proof
  rpt strip_tac >>
  qabbrev_tac `p = a ** 2 + b ** 2` >>
  `(b * c - a * d) * (a * d + b * c) = (b * c) * (b * c) - (a * d) * (a * d)` by rw[difference_of_squares_alt] >>
  `_ = (c * c) * (b * b) - (a * a) * (d * d)` by fs[] >>
  `_ = (c ** 2) * (b ** 2) - (a ** 2) * (d ** 2)` by fs[GSYM EXP_2] >>
  `_ = (p - d ** 2) * b * b - (p - b ** 2) * d * d` by fs[Abbr`p`] >>
  `_ = (p - d * d) * b * b - (p - b * b) * d * d` by fs[GSYM EXP_2] >>
  `_ = (p * b * b - d * d * b * b) - (p * d * d - b * b * d * d)` by simp[] >>
  `_ = p * b * b - d * d * b * b + b * b * d * d - p * d * d` by simp[SUB_SUB, GSYM EXP_2, Abbr`p`] >>
  `_ = p * b * b - p * d * d` by simp[] >>
  `_ = p * (b * b - d * d)` by decide_tac >>
  simp[GSYM EXP_2]
QED

(* Theorem: a ** 2 + b ** 2 = c ** 2 + d ** 2 /\ 0 < b /\ 0 < d ==>
            a * c < a ** 2 + b ** 2 *)
(* Proof:
   Let p = a ** 2 + b ** 2,
   then p = c ** 2 + d ** 2.
   Note         a * a < p          by 0 < b, so 0 < b ** 2
    and         c * c < p          by 0 < d, so 0 < d ** 2
     so a * a * c * c < p * p      by LT_MONO_MULT2
     or  (a * c) ** 2 < p ** 2     by EXP_2
   Hence        a * c < p          by EXP_EXP_LT_MONO
*)
Theorem squares_sum_inequality:
  !a b c d. a ** 2 + b ** 2 = c ** 2 + d ** 2 /\ 0 < b /\ 0 < d ==>
            a * c < a ** 2 + b ** 2
Proof
  rpt strip_tac >>
  qabbrev_tac `p = a ** 2 + b ** 2` >>
  `p = a * a + b * b` by simp[Abbr`p`] >>
  `p = c * c + d * d` by rfs[] >>
  `0 < b * b /\ 0 < d * d` by rfs[] >>
  `a * a < p /\ c * c < p` by decide_tac >>
  `a * a * (c * c) < p * p` by rw[LT_MONO_MULT2] >>
  `(a * c) * (a * c) < p * p` by decide_tac >>
  metis_tac[EXP_EXP_LT_MONO, EXP_2, DECIDE``0 < 2``]
QED

(* Theorem: a ** 2 + b ** 2 = c ** 2 + d ** 2 /\ 0 < b /\ 0 < c ==>
            a * d < a ** 2 + b ** 2 *)
(* Proof:
   Let p = a ** 2 + b ** 2,
   then p = c ** 2 + d ** 2.
   Note         a * a < p          by 0 < b, so 0 < b ** 2
    and         d * d < p          by 0 < c, so 0 < c ** 2
     so a * a * d * d < p * p      by LT_MONO_MULT2
     or  (a * d) ** 2 < p ** 2     by EXP_2
   Hence        a * d < p          by EXP_EXP_LT_MONO
*)
Theorem squares_sum_inequality_1:
  !a b c d. a ** 2 + b ** 2 = c ** 2 + d ** 2 /\ 0 < b /\ 0 < c ==>
            a * d < a ** 2 + b ** 2
Proof
  rpt strip_tac >>
  qabbrev_tac `p = a ** 2 + b ** 2` >>
  `p = a * a + b * b` by simp[Abbr`p`] >>
  `p = c * c + d * d` by rfs[] >>
  `0 < b * b /\ 0 < c * c` by rfs[] >>
  `a * a < p /\ d * d < p` by decide_tac >>
  `a * a * (d * d) = (a * d) * (a * d)` by simp[] >>
  `a * a * (d * d) < p * p` by rw[LT_MONO_MULT2] >>
  metis_tac[EXP_EXP_LT_MONO, EXP_2, DECIDE``0 < 2``]
QED

(* Theorem: a ** 2 + b ** 2 = c ** 2 + d ** 2 /\ 0 < a /\ 0 < d ==>
            b * c < a ** 2 + b ** 2 *)
(* Proof: by squares_sum_inequality_1, ADD_COMM *)
Theorem squares_sum_inequality_2:
  !a b c d. a ** 2 + b ** 2 = c ** 2 + d ** 2 /\ 0 < a /\ 0 < d ==>
            b * c < a ** 2 + b ** 2
Proof
  metis_tac[squares_sum_inequality_1, ADD_COMM]
QED

(* Theorem: prime p /\ p = a ** 2 + b ** 2 ==> coprime a b *)
(* Proof:
   Let g = gcd a b.
   Then g divides a /\ g divides b          by GCD_IS_GREATEST_COMMON_DIVISOR
    ==> ?h k. (a = h * g) /\ (b = k * g)    by divides_def
   Now  p = a * a + b * b                   by EXP_2
          = (h * g) * (h * g) + (k * g) * (k * g)
          = (h * h + k * k) * (g * g)       by arithmetic
   Hence g * g divides p                    by divides_def
      or g * g = 1                          by prime_def, prime_non_square, square_def
     ==> g = 1                              by SQ_EQ_1
*)
Theorem squares_sum_prime_coprime:
  !p a b. prime p /\ p = a ** 2 + b ** 2 ==> coprime a b
Proof
  rpt strip_tac >>
  qabbrev_tac `g = gcd a b` >>
  `g divides a /\ g divides b` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`g`] >>
  `?h k. (a = h * g) /\ (b = k * g)` by metis_tac[divides_def] >>
  `p = a * a + b * b` by simp[] >>
  `_ = (h * g) * (h * g) + (k * g) * (k * g)` by metis_tac[] >>
  `_ = (h * h + k * k) * (g * g)` by simp[] >>
  `g * g divides p` by metis_tac[divides_def] >>
  `g * g = 1` by metis_tac[prime_def, prime_non_square, square_def] >>
  fs[SQ_EQ_1]
QED

(* Theorem: prime p /\ p = a ** 2 + b ** 2 /\ p = c ** 2 + d ** 2 /\
            a * d = b * c ==> a = c /\ b = d *)
(* Proof:
   Note p <> 0               by NOT_PRIME_0
    and a <> 0               by prime_non_square, square_def, MULT_EQ_0
    and gcd a b = 1          by squares_sum_prime_coprime
    Now a divides (b * c)    by divides_def, MULT_COMM, a * d = b * c
     so a divides c          by euclid_coprime, GCD_SYM
    ==> ?k. c = k * a        by divides_def
   Thus d * a = b * (k * a)
              = (k * b) * a
     or d = k * b            by EQ_MULT_RCANCEL, a <> 0

        p = c * c + d * d    by EXP_2
          = (k * a) * (k * a) + (k * b) * (k * b)
          = k * k * (a * a + b * b)
          = k * k * p
   Thus k * k = 1            by EQ_MULT_RCANCEL
     so k = 1                by MULT_EQ_1
   Hence c = k * a = a, d = k * b = b.
*)
Theorem squares_sum_prime_thm:
  !p a b c d. prime p /\
              p = a ** 2 + b ** 2 /\ p = c ** 2 + d ** 2 /\
              a * d = b * c ==> a = c /\ b = d
Proof
  spose_not_then strip_assume_tac >>
  qabbrev_tac `p = a ** 2 + b ** 2` >>
  `p <> 0` by metis_tac[NOT_PRIME_0] >>
  `a <> 0` by metis_tac[prime_non_square, square_def, EXP_2, MULT_EQ_0, ADD] >>
  `gcd a b = 1` by metis_tac[squares_sum_prime_coprime] >>
  `a divides (b * c)` by metis_tac[divides_def, MULT_COMM] >>
  `a divides c` by metis_tac[euclid_coprime, GCD_SYM] >>
  `?k. c = k * a` by metis_tac[divides_def] >>
  `d * a = b * (k * a)` by fs[] >>
  `_ = (k * b) * a` by fs[] >>
  `d = k * b` by metis_tac[EQ_MULT_RCANCEL] >>
  `p = c * c + d * d` by simp[] >>
  `_ = (k * a) * (k * a) + (k * b) * (k * b)` by metis_tac[] >>
  `_ = k * k * (a * a + b * b)` by decide_tac >>
  `_ = k * k * p` by fs[Abbr`p`] >>
  `k * k = 1` by metis_tac[EQ_MULT_RCANCEL, MULT_LEFT_1] >>
  metis_tac[MULT_EQ_1, MULT_LEFT_1]
QED

(* ------------------------------------------------------------------------- *)
(* Set Theorems                                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: {a; b} = {c; d} <=> a = c /\ b = d \/ a = d /\ b = c *)
(* Proof: by EXTENSION. *)
Theorem doublet_eq:
  !a b c d. {a; b} = {c; d} <=> a = c /\ b = d \/ a = d /\ b = c
Proof
  simp[EXTENSION] >>
  metis_tac[]
QED

(* Theorem: FINITE {a; b} *)
(* Proof:
   Since {a; b} = b INSERT (a INSERT {})  by notation
     and FINITE {}         by FINITE_EMPTY
   hence FINITE {a; b}     by FINITE_INSERT
*)
Theorem doublet_finite:
  !a b. FINITE {a; b}
Proof
  rw[]
QED

(* Theorem: a <> b ==> CARD {a; b} = 2 *)
(* Proof:
   Since {a; b} = b INSERT (a INSERT {})  by notation
     and CARD {} = 0          by CARD_EMPTY
   hence CARD {a; b} = 2      by CARD_DEF
*)
Theorem doublet_card:
  !a b. a <> b ==> CARD {a; b} = 2
Proof
  rw[]
QED

(* Theorem: FINITE s /\ s = a UNION b UNION c /\
            a INTER b = {} /\ b INTER c = {} /\ a INTER c = {} /\
            CARD a = CARD c ==> CARD s = 2 * CARD a + CARD b *)
(* Proof:
   Note FINITE a /\ FINITE b /\ FINITE c        by FINITE_UNION
    and a INTER b INTER c = EMPTY               by INTER_EMPTY
        CARD s
      = CARD (a UNION b UNION c)                by s = a UNION b UNION c
      = CARD a + CARD b + CARD c + CARD (a INTER b INTER c)
        - CARD (a INTER b) - CARD (b INTER c) - CARD (a INTER c)
                                                by CARD_UNION_3_EQN
      = CARD a + CARD b + CARD c                by CARD_EMPTY
      = CARD a + CARD b + CARD a                by CARD c = CARD a
      = 2 * CARD a + CARD b                     by arithmetic
*)
Theorem partition_three_special_card:
  !s a b c. FINITE s /\ s = a UNION b UNION c /\
            a INTER b = {} /\ b INTER c = {} /\ a INTER c = {} /\
            CARD a = CARD c ==> CARD s = 2 * CARD a + CARD b
Proof
  rpt strip_tac >>
  `FINITE a /\ FINITE b /\ FINITE c` by metis_tac[FINITE_UNION] >>
  rw[CARD_UNION_3_EQN]
QED

(* Theorem: FINITE s /\ s = a UNION b /\ a INTER b = {} /\ BIJ f a b ==>
            CARD s = 2 * CARD a *)
(* Proof:
   Note a SUBSET s /\ b SUBSET s    by SUBSET_UNION
     so FINITE a /\ FINITE b        by SUBSET_FINITE
    Now BIJ f a b                   by given
    ==> CARD a = CARD b             by FINITE_BIJ_CARD
        CARD s
      = CARD a + CARD b - CARD (a INTER b)   by CARD_UNION_EQN
      = CARD a + CARD a                      by CARD_EMPTY
      = 2 * CARD a                           by arithmetic
*)
Theorem set_partition_bij_card:
  !f s a b. FINITE s /\ s = a UNION b /\ a INTER b = {} /\ BIJ f a b ==>
            CARD s = 2 * CARD a
Proof
  rpt strip_tac >>
  `FINITE a /\ FINITE b` by metis_tac[SUBSET_UNION, SUBSET_FINITE] >>
  `CARD a = CARD b` by metis_tac[FINITE_BIJ_CARD] >>
  `CARD s = CARD a + CARD a` by rw[CARD_UNION_EQN] >>
  decide_tac
QED

(* Theorem: FINITE s /\ (s = a UNION b) /\ (a INTER b = EMPTY) /\ BIJ f a b ==>
            EVEN (CARD s) *)
(* Proof:
   Note CARD s = 2 * CARD a    by set_partition_bij_card
    ==> EVEN (CARD s)          by EVEN_DOUBLE
*)
Theorem set_partition_bij_card_even:
  !f s a b. FINITE s /\ s = a UNION b /\ a INTER b = {} /\ BIJ f a b ==>
            EVEN (CARD s)
Proof
  metis_tac[set_partition_bij_card, EVEN_DOUBLE]
QED

(* Theorem: s = a UNION b /\ a INTER b = {} /\
            t = c UNION d /\ c INTER d = {} /\
            BIJ f a d /\ BIJ f b c ==> BIJ f s t *)
(* Proof: by BIJ_DEF, SURJ_DEF, INJ_DEF *)
Theorem set_partition_bij_give_bij:
  !f s t a b c d.
       s = a UNION b /\ a INTER b = {} /\
       t = c UNION d /\ c INTER d = {} /\
       BIJ f a d /\ BIJ f b c ==> BIJ f s t
Proof
  (rw[BIJ_DEF, SURJ_DEF, INJ_DEF] >> simp[]) >>
  metis_tac[IN_INTER, MEMBER_NOT_EMPTY]
QED

(* ------------------------------------------------------------------------- *)
(* WHILE Loop Specification.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Taken from ringInstances, for multiplicative order computation by WHILE. *)

(* HOL4 can evaluate WHILE directly:

> EVAL ``WHILE (\i. i <= 4) SUC 1``;
val it = |- WHILE (\i. i <= 4) SUC 1 = 5: thm
*)

(*
For WHILE Guard Cmd,
we want to show:
   {Pre-condition} WHILE Guard Command {Post-condition}

> WHILE_RULE;
val it = |- !R B C. WF R /\ (!s. B s ==> R (C s) s) ==>
     HOARE_SPEC (\s. P s /\ B s) C P ==>
     HOARE_SPEC P (WHILE B C) (\s. P s /\ ~B s): thm

> HOARE_SPEC_DEF;
val it = |- !P C Q. HOARE_SPEC P C Q <=> !s. P s ==> Q (C s): thm
*)

(* Idea: For a command Command on x,
         if x is invariant and allowed by guard before command,
           and keeps the invariant after the command,
         then putting command in WHILE loop with guard to continue
         will transform x from Precond to Postcond, when:
              (a) invariant and guard implies a shrinking measure,
              (b) pre-condition implies invariant,
              (c) invarant and opposite of guard implies post-condition
*)

(* Theorem: (!x. Invariant x /\ Guard x ==> Measure (Command x) < Measure x) /\
            (!x. Precond x ==> Invariant x) /\
            (!x. Invariant x /\ ~Guard x ==> Postcond x) /\
            HOARE_SPEC (\x. Invariant x /\ Guard x) Command Invariant ==>
            HOARE_SPEC Precond (WHILE Guard Command) Postcond *)
(* Proof:
   By HOARE_SPEC_DEF, change the goal to show:
      !s. Invariant s ==> Postcond (WHILE Guard Command s)
   By complete induction on (Measure s).
   After rewrite by WHILE, this is to show:
      Postcond (if Guard s then WHILE Guard Command (Command s) else s)
   If Guard s,
      With Invariant s,
       ==> Postcond (WHILE Guard Command (Command s))
                              by induction hypothesis
   If ~(Guard s),
      With Invariant s,
       ==> Postcond s         by given
*)
Theorem WHILE_RULE_PRE_POST:
  (!x. Invariant x /\ Guard x ==> Measure (Command x) < Measure x) /\
  (!x. Precond x ==> Invariant x) /\
  (!x. Invariant x /\ ~Guard x ==> Postcond x) /\
  HOARE_SPEC (\x. Invariant x /\ Guard x) Command Invariant ==>
  HOARE_SPEC Precond (WHILE Guard Command) Postcond
Proof
  simp[HOARE_SPEC_DEF] >>
  rpt strip_tac >>
  `!s. Invariant s ==> Postcond (WHILE Guard Command s)` suffices_by metis_tac[] >>
  Q.UNDISCH_THEN `Precond s` (K ALL_TAC) >>
  rpt strip_tac >>
  completeInduct_on `Measure s` >>
  rpt strip_tac >>
  fs[PULL_FORALL] >>
  first_x_assum (qspec_then `Measure` assume_tac) >>
  rfs[] >>
  ONCE_REWRITE_TAC[WHILE] >>
  Cases_on `Guard s` >-
  simp[] >>
  simp[]
QED

(* ------------------------------------------------------------------------- *)
(* Pair exists and exists uniquely.                                          *)
(* ------------------------------------------------------------------------- *)

(* Idea: a pair exists iff two values exists. *)

(* Theorem: !f. (?(u,v). f u v) <=> ?u v. f u v *)
(* Proof:
   Let x = (u,v). This is to show:
       ?x. f (FST x) (SND x) <=> ?u v. f u v
   If part: ?x. f (FST x) (SND x) ==> ?u v. f u v
      Let u = FST x, v = (SND x).
   Only-if part: ?u v. f u v ==> ?x. f (FST x) (SND x)
      Let x = (u,v).
*)
Theorem pair_exists_iff:
  !f. (?(u,v). f u v) <=> ?u v. f u v
Proof
  rw[pairTheory.ELIM_UNCURRY, EQ_IMP_THM] >-
  metis_tac[] >>
  qexists_tac `(u,v)` >>
  simp[]
QED

(* Idea: a pair exists uniquely implies two values exists uniquely. *)

(* Theorem: !f. (?!(u,v). f u v) ==> ?!u v. f u v *)
(* Proof:
   Let x = (u,v). This is to show:
       ?!x. f (FST x) (SND x) ==> ?!u v. f u v
   By EXISTS_UNIQUE_THM, we have:
       f (FST x) (SND x)
   and !x y. f (FST x) (SND x) /\ f (FST y) (SND y) ==> x = y   ...[1]
   Also by EXISTS_UNIQUE_THM on ?!u, need to show:
   (1) ?u. ?!v. f u v
       Let u = FST x. Remains to show: ?!v. f u v
       By EXISTS_UNIQUE_THM on ?!v, need to show:
       (1.1) ?v. f (FST x) v
             Let v = SND x, true by f (FST x) (SND x).
       (1.2) f (FST x) v /\ f (FST x) v' ==> v = v'
             Let u = FST x, to show: f u v /\ f u v' ==> v = v'
             Thus (u,v) = (u,v')     by unique property [1], (u,v) and (u,v').
             so v = v'               by PAIR_FST_SND_EQ
   (2) ?!v. f u v /\ ?!v. f u' v ==> u = u'
       Note ?v. f u v                by EXISTS_UNIQUE_THM
        and ?v'. f u' v'`            by EXISTS_UNIQUE_THM
       Thus (u,v) = (u',v')          by unique property [1], (u,v) and (u',v')
         so u = u'                   by PAIR_FST_SND_EQ
*)
Theorem pair_exists_unique_imp:
  !f. (?!(u,v). f u v) ==> ?!u v. f u v
Proof
  rw[pairTheory.ELIM_UNCURRY] >>
  fs[Once EXISTS_UNIQUE_THM] >>
  rpt strip_tac >| [
    qexists_tac `FST x` >>
    simp[EXISTS_UNIQUE_THM] >>
    rpt strip_tac >-
    metis_tac[] >>
    qabbrev_tac `u = FST x` >>
    first_x_assum (qspecl_then [`(u,v)`, `(u,v')`] strip_assume_tac) >>
    fs[],
    `?v v'. f u v /\ f u' v'` by metis_tac[EXISTS_UNIQUE_THM] >>
    first_x_assum (qspecl_then [`(u,v)`, `(u',v')`] strip_assume_tac) >>
    fs[]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* Pairing Function.                                                         *)
(* ------------------------------------------------------------------------- *)

(* Overload a pairing function *)
Overload pairing = ``\f. !u x y. f u x /\ f u y ==> x = y``;

(* Idea: a pair exists uniquely implies a pairing function. *)

(* Theorem: !f. (?!(u,v). f u v) ==> pairing f *)
(* Proof:
   Let x = (u,v). This is to show:
       ?!x. f (FST x) (SND x) /\ f u x /\ f u y ==> x = y  by pairing
   By EXISTS_UNIQUE_THM, we have
       ?z. f (FST z) (SND z)
   and !x y. f (FST x) (SND x) /\ f (FST y) (SND y) ==> x = y ... [1]
   Thus (u,x) = (u,y)              by unique property [1], (u,x) and (u,y)
     so x = y                      by PAIR_FST_SND_EQ
*)
Theorem pair_exists_unique_fun:
  !f. (?!(u,v). f u v) ==> pairing f
Proof
  rw[pairTheory.ELIM_UNCURRY] >>
  fs[EXISTS_UNIQUE_THM] >>
  first_x_assum (qspecl_then [`(u,x)`, `(u,y)`] strip_assume_tac) >>
  fs[]
QED

(* Idea: a pair exists uniquely iff two unique values and a pairing function. *)

(* Theorem: !f. (?!(u,v). f u v) <=> (?!u v. f u v) /\ pairing f *)
(* Proof:
   If part: (?!(u,v). f u v) ==> (?!u v. f u v) /\ pairing f
      Note ?!u v. f u v            by pair_exists_unique_imp
       and pairing f               by pair_exists_unique_fun
   Only-if part: (?!u v. f u v) /\ pairing f ==> (?!(u,v). f u v)
      Let x = (u,v). This is to show: ?!x. f (FST x) (SND x)
      By EXISTS_UNIQUE_THM for ?!u, we have:
           ?!v. f u v
       and !u u'. (?!v. f u v) /\ (?!v. f u' v) ==> u = u'
      Also by EXISTS_UNIQUE_THM, need to show:
      (1) ?x. f (FST x) (SND x)
          Note ?v. f u v                             by EXISTS_UNIQUE_THM
          Let x = (u,v), with FST x = u, SND x = v   by PAIR
      (2) f (FST x) (SND x) /\ f (FST y) (SND y) ==> x = y
          Let x = (a,b), y = (c,d), to show: f a b /\ f c d ==> (a,b) = (c,d)
          By EXISTS_UNIQUE_THM for ?!v, we have:
              f u v
          and !u u'. ((?v. f u v) /\ !v v'. f u v /\ f u v' ==> v = v') /\
                      (?v. f u' v) /\ (!v v'. f u' v /\ f u' v' ==> v = v') ==>
                      u = u'
          Thus a = c            by above property, u = a, u' = c, pairing f.
           and b = d            by pairing f
            so (a,b) = (c,d)    by PAIR_FST_SND_EQ
*)
Theorem pair_exists_unique_thm:
  !f. (?!(u,v). f u v) <=> (?!u v. f u v) /\ pairing f
Proof
  rw[EQ_IMP_THM] >-
  simp[pair_exists_unique_imp] >-
  metis_tac[pair_exists_unique_fun] >>
  rw[pairTheory.ELIM_UNCURRY] >>
  fs[Once EXISTS_UNIQUE_THM] >>
  rpt strip_tac >| [
    `?v. f u v` by metis_tac[EXISTS_UNIQUE_THM] >>
    qexists_tac `(u,v)` >>
    simp[],
    fs[EXISTS_UNIQUE_THM] >>
    qabbrev_tac `a = FST x` >>
    qabbrev_tac `b = SND x` >>
    qabbrev_tac `c = FST x'` >>
    qabbrev_tac `d = SND x'` >>
    first_x_assum (qspecl_then [`a`, `c`] strip_assume_tac) >>
    `a = c` by prove_tac[] >>
    `b = d` by metis_tac[] >>
    metis_tac[pairTheory.PAIR_FST_SND_EQ]
  ]
QED

(* Extract theorems *)
(* If part of pair_exists_unique_thm *)
Theorem pair_exists_unique_thm_1 =
        pair_exists_unique_thm |> SPEC_ALL |> #1 o EQ_IMP_RULE |> GEN_ALL;
(* Only-if part of pair_exists_unique_thm *)
Theorem pair_exists_unique_thm_2 =
        pair_exists_unique_thm |> SPEC_ALL |> #2 o EQ_IMP_RULE |> GEN_ALL;
(*
val pair_exists_unique_thm_1 =
   |- !f. (?!(u,v). f u v) ==> (?!u v. f u v) /\ pairing f: thm
val pair_exists_unique_thm_2 =
   |- !f. (?!u v. f u v) /\ pairing f ==> ?!(u,v). f u v: thm
*)

(* Idea: for a pairing function, exists unique pair iff exists unique two values. *)

(* Theorem: !f. pairing f ==> ((?!(u,v). f u v) <=> ?!u v. f u v) *)
(* Proof:
   If part: pairing f /\ ?!(u,v). f u v ==> ?!u v. f u v
      Note ?!(u,v). f u v ==> ?!u v. f u v  by pair_exists_unique_imp
      There is no need to use pairing f.
   Only-if part: pairing f /\ ?!u v. f u v ==> ?!(u,v). f u v
      This is true by only-if part of pair_exists_unique_thm.
*)
Theorem pair_exists_unique_alt:
  !f. pairing f ==> ((?!(u,v). f u v) <=> ?!u v. f u v)
Proof
  rw[EQ_IMP_THM] >-
  simp[pair_exists_unique_imp] >>
  irule pair_exists_unique_thm_2 >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------- *)
(* Unique Boolean Function.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Overload a unique boolean function *)
Overload unique_bool = ``\f a b. f a b /\ !x y. f x y ==> (x = a) /\ (y = b)``;

(* Idea: a unique function (f a b) has two unique values. *)

(* Theorem: !f a b. unique_bool f a b ==> ?!u v. f u v *)
(* Proof:
   By EXISTS_UNIQUE_THM for ?!u, to show:
   (1) ?u. ?!v. f u v
       Let u = a. By EXISTS_UNIQUE_THM for ?!v, to show:
       (1.1) ?v. f a v,                  true by takeing v = b.
       (1.2) f a v /\ f a v' ==> v = v', true by unique_bool property
   (2) ?!v. f u v /\ ?!v. f u' v ==> u = u'
       Note ?v. f u v                    by EXISTS_UNIQUE_THM
        and ?v'. f u' v'                 by EXISTS_UNIQUE_THM
        But u = a and u' = a, so u = u'  by unique_bool property
*)
Theorem unique_bool_unique_values:
  !f a b. unique_bool f a b ==> ?!u v. f u v
Proof
  rpt strip_tac >>
  rw[Once EXISTS_UNIQUE_THM] >| [
    qexists_tac `a` >>
    rw[EXISTS_UNIQUE_THM] >-
    metis_tac[] >>
    metis_tac[],
    metis_tac[EXISTS_UNIQUE_THM]
  ]
QED

(* Idea: a unique function (f a b) has a unique pair. *)

(* Theorem: !f a b. unique_bool f a b ==> ?!(u,v). f u v *)
(* Proof:
   Let x = (u,v). This is to show: ?!x. f (FST x) (SND x)
   By EXISTS_UNIQUE_THM, this is to show:
   (1) ?x. f (FST x) (SND x), true by taking x = (a,b).
   (2) f (FST x) (SND x) /\ f (FST y) (SND y) ==> x = y
       Note FST x = a = FST y      by unique_bool property
        and SND x = b = SND y      by unique_bool property
         so x = y                  by PAIR_FST_SND_EQ
*)
Theorem unique_bool_unique_pair:
  !f a b. unique_bool f a b ==> ?!(u,v). f u v
Proof
  rw[pairTheory.ELIM_UNCURRY] >>
  simp[EXISTS_UNIQUE_THM] >>
  rpt strip_tac >| [
    qexists_tac `(a,b)` >>
    simp[],
    metis_tac[pairTheory.PAIR_FST_SND_EQ]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* An Example: exists unique values not equivalent to exists unique pair.    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: !m. (!x y. x < m /\ y < m ==> x = y ) ==> m <= 1 *)
(* Proof:
   By contradiction, suppose 1 < m.
   Then 0 < m and 1 < m, but 0 <> 1.
   Hence true.
*)
Theorem pairing_for_less:
  !m. (!x y. x < m /\ y < m ==> x = y ) ==> m <= 1
Proof
  spose_not_then strip_assume_tac >>
  `0 < m /\ 1 < m` by decide_tac >>
  metis_tac[ONE_NOT_ZERO]
QED

(* Theorem: (?!m n. n < m) <=> T *)
(* Proof:
   By EXISTS_UNIQUE_THM for ?!m, this is to show:
   (1) ?m. ?!n. n < m
       This is asking for an m such that only one n < m.
       Take m = 1. By EXISTS_UNIQUE_THM for ?!n, this is to show:
       (1.1) ?n. n < 1,                      true by 0 < 1
       (1.2) !x y. x < 1 /\ y < 1 ==> x = y, true by x = y = 0.
   (2) ?!n. n < m /\ ?!n. n < m' ==> m = m'
       Note m <= 1         by EXISTS_UNIQUE_THM, pairing_for_less
        and m' <= 1        by EXISTS_UNIQUE_THM, pairing_for_less
       With n < m and n < m', m <> 0 and m' <> 0.
         so m = 1 = m'.
*)
Theorem exists_unique_values_less:
  (?!m n. n < m) <=> T
Proof
  rw[Once EXISTS_UNIQUE_THM] >| [
    qexists_tac `1` >>
    simp[EXISTS_UNIQUE_THM],
    fs[EXISTS_UNIQUE_THM] >>
    `m <= 1 /\ m' <= 1` by rw[pairing_for_less] >>
    decide_tac
  ]
QED

(* Theorem: (?!(m,n). n < m) <=> F *)
(* Proof:
   Let x = (u,v). This is to show: ~?!x. SND x < FST x
   By EXISTS_UNIQUE_THM, by contradiction, this is to show:
      SND x < FST x /\
      !x y. SND x < FST x /\ SND y < FST y ==> x = y ==> F
      Let x = (1,0), y = (2,1),
      but x <> y       by PAIR_FST_SND_EQ
*)
Theorem exists_unique_pair_less:
  (?!(m,n). n < m) <=> F
Proof
  rw[pairTheory.ELIM_UNCURRY] >>
  rw[EXISTS_UNIQUE_THM] >>
  spose_not_then strip_assume_tac >>
  first_x_assum (qspecl_then [`(1,0)`, `(2,1)`] strip_assume_tac) >>
  fs[]
QED


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
