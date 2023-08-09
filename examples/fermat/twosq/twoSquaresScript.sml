(* ------------------------------------------------------------------------- *)
(* Windmills of the minds: Fermat's Two Squares Theorem                      *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "twoSquares";

(* ------------------------------------------------------------------------- *)


(* open dependent theories *)
(* arithmeticTheory -- load by default *)

(* val _ = load "windmillTheory"; *)
open helperTwosqTheory;
open helperNumTheory;
open helperSetTheory;
open helperFunctionTheory;
open arithmeticTheory pred_setTheory;
open dividesTheory; (* for divides_def, prime_def *)
open logPowerTheory; (* for prime_non_square *)

open windmillTheory;

(* val _ = load "involuteFixTheory"; *)
open involuteTheory; (* for involute_bij *)
open involuteFixTheory;

(* val _ = load "iterateComposeTheory"; *)
open iterationTheory;
open iterateComposeTheory;

(* val _ = load "iterateComputeTheory"; *)
open iterateComputeTheory;

(* for later computation *)
open listTheory;
open rich_listTheory; (* for MAP_REVERSE *)
open helperListTheory; (* for listRangeINC_LEN *)
open listRangeTheory; (* for listRangeINC_CONS *)

(* for group action *)
(* val _ = load "involuteActionTheory"; *)
open involuteActionTheory;
open groupActionTheory;
open groupInstancesTheory;

(* for pairs *)
open pairTheory; (* for ELIM_UNCURRY, PAIR_FST_SND_EQ, PAIR_EQ, FORALL_PROD *)


(* ------------------------------------------------------------------------- *)
(* Windmills of the minds Documentation                                      *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   Helper Theorems:

   Two Squares Fixes:
   zagier_fixes_prime
                   |- !p. prime p /\ (p MOD 4 = 1) ==>
                          (fixes zagier (mills p) = {(1,1,p DIV 4)})

   Fermat Two-Squares Uniqueness:
   fermat_two_squares_unique_thm
                   |- !p a b c d. prime p /\ (p = a ** 2 + b ** 2) /\
                         (p = c ** 2 + d ** 2) ==> ({a; b} = {c; d})
   fermat_two_squares_unique_odd_even
                   |- !p a b c d. prime p /\
                         ODD a /\ EVEN b /\ (p = a ** 2 + b ** 2) /\
                         ODD c /\ EVEN d /\ (p = c ** 2 + d ** 2) ==>
                         (a = c) /\ (b = d)
   flip_fixes_prime_card_upper
                   |- !p. prime p /\ (p MOD 4 = 1) ==> CARD (fixes flip (mills p)) <= 1


   Fermat Two-Squares Existence:
   fermat_two_squares_exists_windmill
                   |- !p. prime p /\ (p MOD 4 = 1) ==> ?x y. p = windmill (x, y, y)
   fermat_two_squares_exists_odd_even
                   |- !p. prime p /\ (p MOD 4 = 1) ==>
                          ?(u,v). ODD u /\ EVEN v /\ (p = u ** 2 + v ** 2)

   Fermat Two-Squares Theorem:
   flip_fixes_prime_sing
                   |- !p. prime p /\ (p MOD 4 = 1) ==> SING (fixes flip (mills p))
   flip_fixes_prime|- !p. prime p /\ (p MOD 4 = 1) ==>
                          (let u = (1,1,p DIV 4) ;
                               n = iterate_period (zagier o flip) u
                            in fixes flip (mills p) = {FUNPOW (zagier o flip) (HALF n) u})
   flip_fixes_prime_alt
                   |- !p u n. prime p /\ (p MOD 4 = 1) /\ (u = (1,1,p DIV 4)) /\
                              (n = iterate_period (zagier o flip) u) ==>
                              (fixes flip (mills p) = {FUNPOW (zagier o flip) (HALF n) u}
   fermat_two_squares_thm
                   |- !p. prime p /\ (p MOD 4 = 1) ==>
                          ?!(u,v). ODD u /\ EVEN v /\ (p = u ** 2 + v ** 2)
   fermat_two_squares_iff
                   |- !p. prime p ==> ((p MOD 4 = 1) <=>
                                      ?!(u,v). ODD u /\ EVEN v /\ (p = u ** 2 + v ** 2))

   Fermat Two-Squares Algorithm:
   zagier_flip_1_1_z_period
                   |- !z. (iterate_period (zagier o flip) (1,1,z) = 1) <=> (z = 1)
   flip_fixes_iterates_prime
                   |- !p u n g. prime p /\ (p MOD 4 = 1) /\ (u = (1,1,p DIV 4)) /\
                                (n = iterate_period (zagier o flip) u) /\
                                (g = (\(x,y,z). y <> z)) ==>
                                ~g (FUNPOW (zagier o flip) (HALF n) u) /\
                                !j. j < HALF n ==> g (FUNPOW (zagier o flip) j u)
   Computation by WHILE loop:
   found_def       |- !x y z. found (x,y,z) <=> (y = z)
   found_not       |- $~ o found = (\(x,y,z). y <> z)
   two_sq_def      |- !n. two_sq n = WHILE ($~ o found) (zagier o flip) (1,1,n DIV 4)
   two_sq_alt      |- !n. two_sq n = WHILE (\(x,y,z). y <> z) (zagier o flip) (1,1,n DIV 4)
   two_sq_thm      |- !p. prime p /\ (p MOD 4 = 1) ==> two_sq p IN fixes flip (mills p)
   two_sq_while_hoare
                   |- !p. prime p /\ (p MOD 4 = 1) ==>
                          HOARE_SPEC (fixes zagier (mills p))
                                     (WHILE ($~ o found) (zagier o flip))
                                     (fixes flip (mills p))
   two_sq_while_thm|- !p. prime p /\ (p MOD 4 = 1) ==>
                          (let (x,y,z) = WHILE ($~ o found) (zagier o flip) (1,1,p DIV 4)
                            in p = x ** 2 + (y + z) ** 2)
   two_squares_def |- !n. two_squares n = (let (x,y,z) = two_sq n in (x,y + z))
   two_squares_thm |- !p. prime p /\ (p MOD 4 = 1) ==>
                          (let (u,v) = two_squares p in p = u ** 2 + v ** 2)

   Fermat's Two Squares Theorem by Group Action:

   Relation to Fixes and Pairs:
   involute_fixed_points_eq_fixes
                   |- !f X. f involute X ==>
                            fixed_points (FUNPOW f) Z2 X = fixes f X
   involute_multi_orbits_union_eq_pairs
                   |- !f X. f involute X ==>
                            BIGUNION (multi_orbits (FUNPOW f) Z2 X) = pairs f X

   Fermat's Two-Squares Theorem (Existence):
   zagier_fixed_points_sing
                   |- !p. prime p /\ (p MOD 4 = 1) ==>
                         (fixed_points (FUNPOW zagier) Z2 (mills p) = {(1,1,p DIV 4)})
   fermat_two_squares_exists_alt
                   |- !p. prime p /\ (p MOD 4 = 1) ==> ?(u,v). p = u ** 2 + v ** 2
*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Two Squares Fixes.                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: prime p /\ (p MOD 4 = 1) ==> (fixes zagier (mills p) = {(1,1,p DIV 4)}) *)
(* Proof:
   Let s = mills p,
       k = p DIV 4,
       a = fixes zagier s.
   The goal becomes: a = {(1,1,k)}

   Use EXTENSION to show two sets are equal:
   (1) (x,y,z) IN a ==> x = 1, y = 1, z = k.
       Note (x,y,z) IN s /\
            zagier (x,y,z) = (x,y,z)  by fixes_element
        but x <> 0                    by mills_prime_triple_nonzero
         so x = y                     by zagier_fix
        Now p = windmill (x, x, z)    by mills_element
        ==> x = 1, y = 1, z = k       by windmill_trivial_prime
   (2) (1,1,k) IN a
       Note p = k * 4 + p MOD 4       by DIVISION
              = 4 * k + 1             by p MOD 4 = 1
              = windmill (1, 1, k)    by windmill_trivial
         so (1,1,k) IN s              by mills_element
        and zagier (1,1,k) = (1,1,k)  by zagier_1_1_z
        ==> (1,1,k) IN a              by fixes_element
*)
Theorem zagier_fixes_prime:
  !p. prime p /\ (p MOD 4 = 1) ==> (fixes zagier (mills p) = {(1,1,p DIV 4)})
Proof
  rpt strip_tac >>
  qabbrev_tac `s = mills p` >>
  qabbrev_tac `k = p DIV 4` >>
  qabbrev_tac `a = fixes zagier s` >>
  simp[EXTENSION, FORALL_PROD, EQ_IMP_THM] >>
  ntac 5 strip_tac >| [
    `(p_1,p_1',p_2) IN s /\ (zagier (p_1,p_1',p_2) = (p_1,p_1',p_2))` by metis_tac[fixes_element] >>
    `p_1 = p_1'` by metis_tac[zagier_fix, mills_prime_triple_nonzero] >>
    metis_tac[windmill_trivial_prime, mills_element],
    `p = k * 4 + p MOD 4` by rw[DIVISION, Abbr`k`] >>
    `_ = windmill (1, 1, k)` by rw[windmill_trivial] >>
    `(1,1,k) IN s` by rw[mills_element, Abbr`s`] >>
    fs[fixes_element, zagier_1_1_z, Abbr`a`]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* Fermat Two-Squares Uniqueness.                                            *)
(* ------------------------------------------------------------------------- *)


(* Theorem: prime p /\ (p = a ** 2 + b ** 2) /\ (p = c ** 2 + d ** 2) ==>
          ({a; b} = {c; d}) *)
(* Proof:
   This is to show:
        (a = c) /\ (b = d)
     \/ (a = d) /\ (b = c)                 by doublet_eq

   Step 1: basic properties
   Note 0 < p                              by NOT_PRIME_0
    and 0 < a /\ 0 < b /\ 0 < c /\ 0 < d   by SQ_0, prime_non_square, square_def
    and a * d < p                          by squares_sum_inequality, ADD_COMM
    and b * c < p                          by squares_sum_inequality, ADD_COMM

   Step 2: use identities and prime divisibility
   Note (a * d - b * c) * (a * d + b * c)
      = (d ** 2 - b ** 2) * p              by squares_sum_identity_1
    and (b * c - a * d) * (a * d + b * c)
      = (b ** 2 - d ** 2) * p              by squares_sum_identity_2
   Thus p divides (a * d - b * c) * (a * d + b * c)   by divides_def
    and p divides (b * c - a * d) * (a * d + b * c)   by divides_def
    ==> (p divides (a * d - b * c) /\ p divides (b * c - a * d))
      \/ p divides (a * d + b * c)                    by euclid_prime

   Case: p divides a * d - b * c /\ p divides b * c - a * d
   Note a * d - b * c < p             by a * d < p
    and b * c - a * d < p             by b * c < p
   Thus (a * d - b * c = 0)           by DIVIDES_LEQ_OR_ZERO
    and (b * c - a * d = 0)           by DIVIDES_LEQ_OR_ZERO
    ==> a * d = b * c                 by arithmetic
   Hence (a = c) and (b = d)          by squares_sum_prime_thm

   Case: p divides a * d + b * c
   Note 0 < (a * d + b * c) < 2 * p   by a * d < p, b * c < p, and a,b,c,d <> 0
   Thus a * d + b * c = p             by divides_eq_thm
   For four_squares_identity, break into cases:
   If b * d <= a * c,
      Note p ** 2
         = p * p                      by EXP_2
         = (a ** 2 + b ** 2) * (c ** 2 + d ** 2)
         = p ** 2 + (a * c - b * d) ** 2
                                      by four_squares_identity
      Thus (a * c - b * d) ** 2 = 0   by EQ_ADD_LCANCEL
        or a * c - b * d = 0          by EXP_2_EQ_0
       ==> a * c = b * d              by b * d <= a * c
       ==> (a = c) /\ (b = d)         by squares_sum_prime_thm, ADD_COMM
   If a * c <= b * d,
      Note p ** 2
         = p * p                      by EXP_2
         = (a ** 2 + b ** 2) * (c ** 2 + d ** 2)
         = p ** 2 + (b * d - a * c) ** 2
                                      by four_squares_identity_alt
      Thus (b * d - a * c) ** 2 = 0   by EQ_ADD_LCANCEL
        or b * d - a * c = 0          by EXP_2_EQ_0
       ==> a * c = b * d              by a * c <= b * d
       ==> (a = c) /\ (b = d)         by squares_sum_prime_thm, ADD_COMM
*)
Theorem fermat_two_squares_unique_thm:
  !p a b c d. prime p /\ (p = a ** 2 + b ** 2) /\ (p = c ** 2 + d ** 2) ==>
               ({a; b} = {c; d})
Proof
  rpt strip_tac >>
  simp[doublet_eq] >>
  spose_not_then strip_assume_tac >>
  `0 < p` by metis_tac[NOT_PRIME_0, NOT_ZERO] >>
  `0 < a /\ 0 < b /\ 0 < c /\ 0 < d` by metis_tac[SQ_0, prime_non_square, square_def, EXP_2, ADD, ADD_0, NOT_ZERO] >>
  `a * d < p` by metis_tac[squares_sum_inequality, ADD_COMM] >>
  `b * c < p` by metis_tac[squares_sum_inequality, ADD_COMM] >>
  `(a * d - b * c) * (a * d + b * c) = (d ** 2 - b ** 2) * p` by rw[squares_sum_identity_1] >>
  `(b * c - a * d) * (a * d + b * c) = (b ** 2 - d ** 2) * p` by rw[squares_sum_identity_2] >>
  `p divides (a * d - b * c) * (a * d + b * c)` by metis_tac[divides_def] >>
  `p divides (b * c - a * d) * (a * d + b * c)` by metis_tac[divides_def] >>
  `(p divides (a * d - b * c) /\ p divides (b * c - a * d)) \/ p divides (a * d + b * c)` by metis_tac[euclid_prime] >| [
    `a * d - b * c < p /\ b * c - a * d < p` by fs[] >>
    `(a * d - b * c = 0) /\ (b * c - a * d = 0)` by metis_tac[DIVIDES_LEQ_OR_ZERO, NOT_LESS] >>
    `a * d = b * c` by fs[] >>
    metis_tac[squares_sum_prime_thm],
    `a * d + b * c = p` by
  (`a * d + b * c < 2 * p` by fs[] >>
    `0 < a * d + b * c` by metis_tac[MULT, ADD_EQ_0, MULT_EQ_0, NOT_ZERO] >>
    rw[divides_eq_thm]) >>
    Cases_on `b * d <= a * c` >| [
      `p ** 2 = (a ** 2 + b ** 2) * (c ** 2 + d ** 2)` by fs[] >>
      `_ = p ** 2 + (a * c - b * d) ** 2` by rfs[four_squares_identity] >>
      `(a * c - b * d) ** 2 = 0` by metis_tac[EQ_ADD_LCANCEL, ADD_0] >>
      `a * c - b * d = 0` by metis_tac[EXP_2_EQ_0] >>
      `a * c = b * d` by fs[] >>
      metis_tac[squares_sum_prime_thm, ADD_COMM],
      `p ** 2 = (a ** 2 + b ** 2) * (c ** 2 + d ** 2)` by fs[] >>
      `_ = p ** 2 + (b * d - a * c) ** 2` by rfs[four_squares_identity_alt] >>
      `(b * d - a * c) ** 2 = 0` by metis_tac[EQ_ADD_LCANCEL, ADD_0] >>
      `b * d - a * c = 0` by metis_tac[EXP_2_EQ_0] >>
      `a * c = b * d` by fs[] >>
      metis_tac[squares_sum_prime_thm, ADD_COMM]
    ]
  ]
QED


(* Theorem: prime p /\ ODD a /\ EVEN b /\ (p = a ** 2 + b ** 2) /\
            ODD c /\ EVEN d /\ (p = c ** 2 + d ** 2) ==> ((a = c) /\ (b = d)) *)
(* Proof:
   Note {a; b} = {c; d}                          by fermat_two_squares_unique_thm
   Thus (a = c) /\ (b = d) \/ (a = d) /\ (b = c) by EXTENSION
   But (a <> d) \/ (b <> c)                      by EVEN_ODD
    so (a = c) /\ (b = d).
*)
Theorem fermat_two_squares_unique_odd_even:
  !p a b c d. prime p /\ ODD a /\ EVEN b /\ (p = a ** 2 + b ** 2) /\
               ODD c /\ EVEN d /\ (p = c ** 2 + d ** 2) ==> ((a = c) /\ (b = d))
Proof
  ntac 7 strip_tac >>
  `{a; b} = {c; d}` by fs[fermat_two_squares_unique_thm] >>
  fs[EXTENSION] >>
  metis_tac[EVEN_ODD]
QED

(* Theorem: prime p /\ (p MOD 4 = 1) ==> CARD (fixes flip (mills p)) <= 1 *)
(* Proof:
   Let s = mills p,
       b = fixes flip s.
   The goal is: CARD b <= 1.
   By contradiction, suppose CARD b > 1.
   Then CARD b <> 0,
     so ?u. u IN b             by CARD_EMPTY, MEMBER_NOT_EMPTY
   Note u IN s                 by fixes_element
    and ?x y. u = (x,y,y)      by triple_parts, flip_fix
   Thus p = windmill (x, y, y) by mills_element

   Also CARD b <> 1,
   Then ~SING b                by SING_CARD_1
     so b <> EMPTY             by MEMBER_NOT_EMPTY
    and ?v. v IN b /\ v <> u   by SING_ONE_ELEMENT, b <> EMPTY
   Note v IN s                 by fixes_element
    and ?h k. v = (h,k,k)      by triple_parts, flip_fix
   Thus p = windmill (h, k, k) by mills_element

   Let c = 2 * y,
       d = 2 * k.
    Now ODD p                  by odd_by_mod_4, p MOD 4 = 1
    and (p = x ** 2 + c ** 2) /\ ODD x   by windmill_x_y_y
    and (p = h ** 2 + d ** 2) /\ ODD h   by windmill_x_y_y
    but EVEN c /\ EVEN d                 by EVEN_DOUBLE
    ==> (x = h) /\ (c = d)     by fermat_two_squares_unique_odd_even
     so (x = h) /\ (y = k)     by EQ_MULT_LCANCEL
     or v = u                  by PAIR_EQ
   This contradicts v <> u.
*)
Theorem flip_fixes_prime_card_upper:
  !p. prime p /\ (p MOD 4 = 1) ==> CARD (fixes flip (mills p)) <= 1
Proof
  rpt strip_tac >>
  qabbrev_tac `s = mills p` >>
  qabbrev_tac `b = fixes flip s` >>
  spose_not_then strip_assume_tac >>
  `CARD b <> 0 /\ CARD b <> 1` by decide_tac >>
  `?u. u IN b` by metis_tac[CARD_EMPTY, MEMBER_NOT_EMPTY] >>
  `u IN s /\ ?x y. u = (x,y,y)` by metis_tac[fixes_element, triple_parts, flip_fix] >>
  `p = windmill (x, y, y)` by fs[mills_element, Abbr`s`] >>
  `~SING b` by metis_tac[SING_CARD_1] >>
  `b <> EMPTY` by metis_tac[MEMBER_NOT_EMPTY] >>
  `?v. v IN b /\ v <> u` by metis_tac[SING_ONE_ELEMENT] >>
  `v IN s /\ ?h k. v = (h,k,k)` by metis_tac[fixes_element, triple_parts, flip_fix] >>
  `p = windmill (h, k, k)` by fs[mills_element, Abbr`s`] >>
  qabbrev_tac `c = 2 * y` >>
  qabbrev_tac `d = 2 * k` >>
  `ODD p` by rfs[odd_by_mod_4] >>
  `(p = x ** 2 + c ** 2) /\ ODD x` by metis_tac[windmill_x_y_y] >>
  `(p = h ** 2 + d ** 2) /\ ODD h` by metis_tac[windmill_x_y_y] >>
  `EVEN c /\ EVEN d` by rw[EVEN_DOUBLE, Abbr`c`, Abbr`d`] >>
  `(x = h) /\ (c = d)` by metis_tac[fermat_two_squares_unique_odd_even] >>
  `y = k` by fs[Abbr`c`, Abbr`d`] >>
  metis_tac[PAIR_EQ]
QED

(* ------------------------------------------------------------------------- *)
(* Fermat Two-Squares Existence.                                             *)
(* ------------------------------------------------------------------------- *)


(* Theorem: prime p /\ (p MOD 4 = 1) ==> ?x y. p = windmill (x, y, y) *)
(* Proof:
   Let m = mills p, the solutions (x,y,z) of p = x ** 2 + 4 * y * z.
   Note ~square p                 by prime_non_square
     so FINITE m                  by mills_non_square_finite
    and zagier involute m         by zagier_involute_mills_prime
    and flip involute m           by flip_involute_mills

   Now work out fixed points:
   Let a = fixes zagier m, b = fixes flip m.
   Let k = p DIV 4.
   Then a = {(1,1,k)}                  by zagier_fixes_prime

   The punch line:
   Note ODD (CARD a) <=> ODD (CARD b)  by involute_two_fixes_both_odd
    now CARD a = 1                     by CARD_SING
     so ODD (CARD b)                   by ODD_1
    ==> CARD b <> 0                    by ODD
     or b <> EMPTY                     by CARD_EMPTY
   Thus ? (x, y, z) IN b               by MEMBER_NOT_EMPTY
    and (x, y, z) IN m /\
        (flip (x, y, z) = (x, y, z))   by fixes_element
     so y = z                          by flip_fix
     or (x,y,y) in m                   by above
   Thus p = windmill (x, y, y)         by mills_element
*)
Theorem fermat_two_squares_exists_windmill:
  !p. prime p /\ (p MOD 4 = 1) ==> ?x y. p = windmill (x, y, y)
Proof
  rpt strip_tac >>
  qabbrev_tac `m = mills p` >>
  `~square p` by metis_tac[prime_non_square] >>
  `FINITE m` by fs[mills_non_square_finite, Abbr`m`] >>
  `zagier involute m` by metis_tac[zagier_involute_mills_prime] >>
  `flip involute m` by metis_tac[flip_involute_mills] >>
  qabbrev_tac `a = fixes zagier m` >>
  qabbrev_tac `b = fixes flip m` >>
  qabbrev_tac `k = p DIV 4` >>
  `a = {(1,1,k)}` by rw[zagier_fixes_prime, Abbr`a`, Abbr`m`] >>
  `CARD a = 1` by rw[] >>
  `ODD (CARD a) <=> ODD (CARD b)` by rw[involute_two_fixes_both_odd, Abbr`a`, Abbr`b`] >>
  `ODD (CARD b)` by metis_tac[ODD_1] >>
  `CARD b <> 0` by metis_tac[ODD] >>
  `b <> EMPTY` by metis_tac[CARD_EMPTY] >>
  `?t. t IN b` by rw[MEMBER_NOT_EMPTY] >>
  `?x y z. t = (x, y, z)` by rw[triple_parts] >>
  `t IN m /\ (flip (x, y, z) = (x, y, z))` by metis_tac[fixes_element] >>
  `y = z` by fs[flip_fix] >>
  metis_tac[mills_element]
QED


(* Theorem: prime p /\ (p MOD 4 = 1) ==>
            ?(u,v). ODD u /\ EVEN v /\ (p = u ** 2 + v ** 2) *)
(* Proof:
   Note ?x y. p = windmill (x, y, y)      by fermat_two_squares_exists_windmill
                = x ** 2 + (2 * y) ** 2   by windmill_by_squares
   Put (u, v) = (x, 2 * y).
   Remains to show: ODD u /\ EVEN v.
   Note EVEN v                            by EVEN_DOUBLE
    and EVEN (v * v)                      by EVEN_MULT
   Also p = u ** 2 + v ** 2               by above
          = u * u + v * v                 by EXP_2
     or p - u * u = v * v                 by arithmetic
    Now ODD p                             by odd_by_mod_4, p MOD 4 = 1
     so ODD (u * u)                       by EVEN_SUB, EVEN_ODD
     or ODD u                             by ODD_MULT
*)
Theorem fermat_two_squares_exists_odd_even:
  !p. prime p /\ (p MOD 4 = 1) ==>
   ?(u,v). ODD u /\ EVEN v /\ (p = u ** 2 + v ** 2)
Proof
  rw[ELIM_UNCURRY] >>
  `?x y. p = windmill (x, y, y)` by rw[fermat_two_squares_exists_windmill] >>
  `_ = x ** 2 + (2 * y) ** 2` by rw[windmill_by_squares] >>
  qabbrev_tac `u = x` >>
  qabbrev_tac `v = 2 * y` >>
  qexists_tac `(u,v)` >>
  rfs[] >>
  `EVEN v` by rw[EVEN_DOUBLE, Abbr`v`] >>
  `EVEN (v * v)` by rw[EVEN_MULT] >>
  `ODD p` by rw[odd_by_mod_4] >>
  `p = u * u + v * v` by simp[] >>
  `u * u <= p` by decide_tac >>
  `v * v = p - u * u` by decide_tac >>
  `ODD (u * u)` by metis_tac[EVEN_SUB, EVEN_ODD] >>
  fs[ODD_MULT]
QED

(* ------------------------------------------------------------------------- *)
(* Fermat Two-Squares Theorem.                                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: prime p /\ (p MOD 4 = 1) ==> SING (fixes flip (mills p)) *)
(* Proof:
   Let s = mills p,
       b = fixes flip s.
   The goal is: SING b.
   Note ?x y. p = windmill (x, y, y)
                            by fermat_two_squares_exists_windmill
    Let u = (x,y,y).
   Then u IN s              by mills_element
    and u IN b              by fixes_element, flip_fix
   By SING_DEF, EXTENSION, this is to show:
      !t. t IN b ==> t = u.
   Note t IN s              by fixes_element
    and ?h k. t = (h,k,k)   by triple_parts, flip_fix
   Thus p = windmill (h, k, k) by mills_element

   Let c = 2 * y,
       d = 2 * k.
    Now ODD p               by odd_by_mod_4, p MOD 4 = 1
    and (p = x ** 2 + c ** 2) /\ ODD x   by windmill_x_y_y
    and (p = h ** 2 + d ** 2) /\ ODD h   by windmill_x_y_y
    but EVEN c /\ EVEN d                 by EVEN_DOUBLE
    ==> (x = h) /\ (c = d)  by fermat_two_squares_unique_odd_even
     so (x = h) /\ (y = k)  by EQ_MULT_LCANCEL
     or t = u.
*)
Theorem flip_fixes_prime_sing:
  !p. prime p /\ (p MOD 4 = 1) ==> SING (fixes flip (mills p))
Proof
  rpt strip_tac >>
  `?x y. p = windmill (x, y, y)` by rw[fermat_two_squares_exists_windmill] >>
  qabbrev_tac `s = mills p` >>
  qabbrev_tac `b = fixes flip s` >>
  qabbrev_tac `u = (x,y,y)` >>
  `u IN s` by rw[mills_element, Abbr`u`, Abbr`s`] >>
  `u IN b` by metis_tac[fixes_element, triple_parts, flip_fix] >>
  simp[SING_DEF, EXTENSION] >>
  qexists_tac `u` >>
  (rewrite_tac[EQ_IMP_THM] >> simp[]) >>
  rpt strip_tac >>
  `x' IN s /\ ?h k. x' = (h,k,k)` by metis_tac[fixes_element, triple_parts, flip_fix] >>
  `p = windmill (h, k, k)` by fs[mills_element, Abbr`s`] >>
  qabbrev_tac `c = 2 * y` >>
  qabbrev_tac `d = 2 * k` >>
  `ODD p` by rfs[odd_by_mod_4] >>
  `(p = x ** 2 + c ** 2) /\ ODD x` by metis_tac[windmill_x_y_y] >>
  `(p = h ** 2 + d ** 2) /\ ODD h` by metis_tac[windmill_x_y_y] >>
  `EVEN c /\ EVEN d` by rw[EVEN_DOUBLE, Abbr`c`, Abbr`d`] >>
  `(x = h) /\ (c = d)` by metis_tac[fermat_two_squares_unique_odd_even] >>
  `y = k` by fs[Abbr`c`, Abbr`d`] >>
  simp[Abbr`u`]
QED

(* Theorem: prime p /\ (p MOD 4 = 1) ==>
            (fixes flip (mills p) =
               {(let u = (1,1,p DIV 4) ;
                     n = iterate_period (zagier o flip) u
                  in FUNPOW (zagier o flip) (HALF n) u)}) *)
(* Proof:
   Let s = mills p,
       v = FUNPOW (zagier o flip) (HALF n) u,
       a = fixes zagier s,
       b = fixes flip s.
   The goal is: b = {v}.

   Note a = {u}              by zagier_fixes_prime
     so u IN a               by IN_SING
   Also ~square p            by prime_non_square
     so FINITE s             by mills_non_square_finite
    ==> zagier involute s    by zagier_involute_mills_prime
    and flip involute s      by flip_involute_mills
    ==> ODD n                by involute_involute_fix_sing_period_odd
     so v IN b               by involute_involute_fix_orbit_fix_odd
   Thus b = {v}              by flip_fixes_prime_sing, SING_DEF, IN_SING
*)
Theorem flip_fixes_prime:
  !p. prime p /\ (p MOD 4 = 1) ==>
       let u = (1, 1, p DIV 4);
           n = iterate_period (zagier o flip) u
        in fixes flip (mills p) = {FUNPOW (zagier o flip) (n DIV 2) u}
Proof
  rw_tac bool_ss[] >>
  qabbrev_tac `s = mills p` >>
  qabbrev_tac `v = FUNPOW (zagier o flip) (HALF n) u` >>
  qabbrev_tac `a = fixes zagier s` >>
  qabbrev_tac `b = fixes flip s` >>
  `a = {u}` by metis_tac[zagier_fixes_prime] >>
  `u IN a` by fs[] >>
  `~square p` by metis_tac[prime_non_square] >>
  `FINITE s` by fs[mills_non_square_finite, Abbr`s`] >>
  `zagier involute s` by metis_tac[zagier_involute_mills_prime] >>
  `flip involute s` by metis_tac[flip_involute_mills] >>
  drule_then strip_assume_tac involute_involute_fix_sing_period_odd >>
  last_x_assum (qspecl_then [`zagier`, `flip`, `n`, `u`] strip_assume_tac) >>
  `ODD n` by rfs[] >>
  drule_then strip_assume_tac involute_involute_fix_orbit_fix_odd >>
  last_x_assum (qspecl_then [`zagier`, `flip`, `n`, `u`] strip_assume_tac) >>
  `v IN b` by rfs[] >>
  metis_tac[flip_fixes_prime_sing, SING_DEF, IN_SING]
QED

(* Theorem: prime p /\ (p MOD 4 = 1) /\ (u = (1, 1, p DIV 4)) /\
           (n = iterate_period (zagier o flip) u) ==>
           (fixes flip (mills p) = {FUNPOW (zagier o flip) (n DIV 2) u}) *)
(* Proof: by flip_fixes_prime *)
Theorem flip_fixes_prime_alt:
  !p u n. prime p /\ (p MOD 4 = 1) /\ (u = (1, 1, p DIV 4)) /\
           (n = iterate_period (zagier o flip) u) ==>
           (fixes flip (mills p) = {FUNPOW (zagier o flip) (n DIV 2) u})
Proof
  metis_tac[flip_fixes_prime]
QED


(* Theorem: !p. prime p /\ (p MOD 4 = 1) ==>
            ?!(u,v). ODD u /\ EVEN v /\ (p = u ** 2 + v ** 2) *)
(* Proof:
   Existence part    by fermat_two_squares_exists_odd_even
   Uniqueness part   by fermat_two_squares_unique_odd_even
*)
Theorem fermat_two_squares_thm:
  !p. prime p /\ (p MOD 4 = 1) ==>
   ?!(u,v). ODD u /\ EVEN v /\ (p = u ** 2 + v ** 2)
Proof
  rw[ELIM_UNCURRY] >>
  rw[EXISTS_UNIQUE_THM] >| [
    drule_then strip_assume_tac fermat_two_squares_exists_odd_even >>
    first_x_assum (drule_all_then strip_assume_tac) >>
    fs[ELIM_UNCURRY] >>
    metis_tac[],
    metis_tac[fermat_two_squares_unique_odd_even, PAIR_FST_SND_EQ]
  ]
QED


(* Theorem: prime p ==>
            ((p MOD 4 = 1) <=> ?!(u,v). ODD u /\ EVEN v /\ (p = u ** 2 + v ** 2)) *)
(* Proof:
   If part: p MOD 4 = 1 ==> ?!(u,v). ODD u /\ EVEN v /\ (p = u ** 2 + v ** 2)
      This is true                       by fermat_two_squares_thm
   Only-if part: ?!(u,v). ODD u /\ EVEN v /\ (p = u ** 2 + v ** 2) ==> p MOD 4 = 1
      Note ?(u,v). ODD u /\ EVEN v /\
                  (p = u ** 2 + v ** 2)  by EXISTS_UNIQUE_THM
       but ODD (u ** 2)                  by ODD_EXP
       and EVEN (v ** 2)                 by EVEN_EXP
      Thus ODD p                         by ODD_ADD, EVEN_ODD
        so p MOD 4 = 1 or p MOD 4 = 3    by mod_4_odd
       but p MOD 4 <> 3                  by mod_4_not_squares
       ==> p MOD 4 = 1
*)
Theorem fermat_two_squares_iff:
  !p. prime p ==>
  ((p MOD 4 = 1) <=> ?!(u,v). ODD u /\ EVEN v /\ (p = u ** 2 + v ** 2))
Proof
  rw[EQ_IMP_THM] >-
  rw[fermat_two_squares_thm] >>
  fs[ELIM_UNCURRY, EXISTS_UNIQUE_THM] >>
  `p MOD 4 = 1` suffices_by simp[] >>
  qabbrev_tac `u = FST x` >>
  qabbrev_tac `v = SND x` >>
  `ODD (u ** 2)` by rw[ODD_EXP] >>
  `EVEN (v ** 2)` by rw[EVEN_EXP] >>
  `ODD p` by fs[ODD_ADD, EVEN_ODD] >>
  `(p MOD 4 = 1) \/ (p MOD 4 = 3)` by fs[mod_4_odd] >>
  fs[mod_4_not_squares]
QED

(* ------------------------------------------------------------------------- *)
(* Fermat Two-Squares Algorithm.                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (iterate_period (zagier o flip) (1,1,z) = 1) <=> (z = 1) *)
(* Proof:
   By iterate_period_thm, this is to show:
   (1) zagier (flip (1,1,z)) = (1,1,z) ==> z = 1
       This is true                by zagier_flip_1_1_z
   (2) zagier (flip (1,1,1)) = (1,1,1)
       This is true                by zagier_flip_1_1_z
*)
Theorem zagier_flip_1_1_z_period:
  !z. (iterate_period (zagier o flip) (1,1,z) = 1) <=> (z = 1)
Proof
  rw[iterate_period_thm, zagier_flip_1_1_z]
QED

(* Theorem: prime p /\ (p MOD 4 = 1) /\ (u = (1, 1, p DIV 4)) /\
            (n = iterate_period (zagier o flip) u) /\ (g = \(x,y,z). y <> z) ==>
            !j. j < n DIV 2 ==> g (FUNPOW (zagier o flip) j u) /\
            ~g (FUNPOW (zagier o flip) (n DIV 2) u) *)
(* Proof:
   Let s = mills p,
       f = zagier o flip,
       h = n DIV 2,
       v = FUNPOW f h u.
   The goal is: ~g v /\ !j. j < h ==> g (FUNPOW f j u)

   Note ~square p                 by prime_non_square
     so FINITE s                  by mills_non_square_finite
    and zagier involute s         by zagier_involute_mills_prime
    and flip involute s           by flip_involute_mills
     so f PERMUTES s              by involute_involute_permutes
   Also u IN s                    by mills_element_trivial
    and 0 < n                     by iterate_period_pos
     so h < n                     by HALF_LT, 0 < n

   Without assuming the following:
   Note fixes flip s = {v}        by flip_fixes_prime
   But use:
   Note fixes zagier s = {u}      by zagier_fixes_prime
     so ODD n                     by involute_involute_fix_sing_period_odd
   Then use involute_involute_fix_odd_period_fix:
   !j. j < n ==> (FUNPOW (zagier o flip) j u IN fixes flip s <=> (j = h))

   Case: n = 1,
   Then h = 0                     by HALF_EQ_0, n <> 0
     so v = u                     by FUNPOW_0
          = (1,1,1)               by zagier_flip_1_1_z_period
     or ~g v                      by definition of g
    and the other case needs j < 0, which is irrelevant.

   Case: n <> 1.
    and h <> 0, so 0 < h          by HALF_EQ_0

   Claim: ~g v
   Note 0 < h < n,
     so v IN fixes flip s         by involute_involute_fix_odd_period_fix
    Now ?x y z. v = (x,y,z)       by triple_parts
    and y = z                     by fixes_element, flip_fix
     or ~g v                      by definition of g

   Claim: !j. j < h ==> g (FUNPOW f j u)
   By contradiction, suppose ?j. j < h /\ ~g (FUNPOW f j u).
   Let w = FUNPOW f j u.
   Note ?x y z. w = (x,y,z)       by triple_parts
     so y = z                     by ~g w
    Now w IN s                    by FUNPOW_closure
    and flip w = w                by flip_fix
    ==> w IN (fixes flip u}       by fixes_element
   Then j = h                     by involute_involute_fix_odd_period_fix, j < n
   which contradicts j < h.
*)
Theorem flip_fixes_iterates_prime:
  !p u n g. prime p /\ (p MOD 4 = 1) /\ (u = (1, 1, p DIV 4)) /\
             (n = iterate_period (zagier o flip) u) /\ (g = \(x,y,z). y <> z) ==>
             (~g (FUNPOW (zagier o flip) (n DIV 2) u) /\
              (!j. j < n DIV 2 ==> g (FUNPOW (zagier o flip) j u)))
Proof
  ntac 5 strip_tac >>
  qabbrev_tac `f = zagier o flip` >>
  qabbrev_tac `s = mills p` >>
  qabbrev_tac `h = n DIV 2` >>
  qabbrev_tac `v = FUNPOW f h u` >>
  `~square p` by rw[prime_non_square] >>
  `FINITE s` by metis_tac[mills_non_square_finite] >>
  `zagier involute s` by metis_tac[zagier_involute_mills_prime] >>
  `flip involute s` by metis_tac[flip_involute_mills] >>
  `fixes zagier s = {u}` by metis_tac[zagier_fixes_prime] >>
  qabbrev_tac `X = (u = (1,1,p DIV 4))` >>
  qabbrev_tac `Y = (n = iterate_period f u)` >>
  qabbrev_tac `Z = (g = (\(x,y,z). y <> z))` >>
  drule_then strip_assume_tac involute_involute_fix_sing_period_odd >>
  last_x_assum (qspecl_then [`zagier`, `flip`, `n`, `u`] strip_assume_tac) >>
  rfs[] >>
  `f PERMUTES s` by fs[involute_involute_permutes, Abbr`f`] >>
  `u IN s` by rw[mills_element_trivial, Abbr`s`, Abbr`X`] >>
  `0 < n` by metis_tac[iterate_period_pos] >>
  `h < n` by rw[HALF_LT, Abbr`h`] >>
  Cases_on `n = 1` >| [
    `h = 0` by rw[Abbr`h`] >>
    `v = u` by rw[Abbr`v`] >>
    `_ = (1,1,1)` by metis_tac[zagier_flip_1_1_z_period] >>
    rfs[Abbr`Z`],
    `h <> 0` by rw[HALF_EQ_0, Abbr`h`] >>
    `0 < h` by decide_tac >>
    drule_then strip_assume_tac involute_involute_fix_odd_period_fix >>
    last_x_assum (qspecl_then [`zagier`, `flip`, `n`, `u`] strip_assume_tac) >>
    rfs[] >>
    qunabbrev_tac `Z` >>
    `~g v` by
  (`FUNPOW (zagier o flip) h u IN fixes flip s <=> (h = HALF n)` by metis_tac[] >>
    `v IN fixes flip s` by metis_tac[] >>
    `?x y z. v = (x,y,z)` by rw[triple_parts] >>
    `y = z` by metis_tac[fixes_element, flip_fix] >>
    fs[]) >>
    rpt strip_tac >>
    spose_not_then strip_assume_tac >>
    qabbrev_tac `w = FUNPOW f j u` >>
    `?x y z. w = (x,y,z)` by rw[triple_parts] >>
    `~g w <=> (y = z)` by fs[] >>
    `y = z` by fs[] >>
    `w IN s` by rw[FUNPOW_closure, Abbr`w`] >>
    `w IN (fixes flip s)` by fs[flip_fix, fixes_element] >>
    `FUNPOW (zagier o flip) j u IN fixes flip s <=> (j = HALF n)` by metis_tac[LESS_TRANS] >>
    `j = h` by metis_tac[] >>
    decide_tac
  ]
QED

(* This proof is using:
   involute_involute_fix_odd_period_fix.
   In part4, there is another proof using:
   flip_fixes_prime, which depends on fermat_two_squares_unique_odd_even.
*)

(* ------------------------------------------------------------------------- *)
(* Computation by WHILE loop.                                                *)
(* ------------------------------------------------------------------------- *)

(* Define the exit condition *)
Definition found_def:
    found (x:num, y:num, z:num) <=> (y = z)
End

(* Theorem: $~ o found = (\(x,y,z). y <> z) *)
(* Proof: by found_def, FUN_EQ_THM. *)
Theorem found_not:
  $~ o found = (\(x,y,z). y <> z)
Proof
  rw[found_def, FORALL_PROD, FUN_EQ_THM]
QED

(* Idea: use WHILE for search. Develop theory in iterateCompute. *)

(* Compute two squares of Fermat's theorem by WHILE loop. *)
Definition two_sq_def:
    two_sq n = WHILE ($~ o found) (zagier o flip) (1,1,n DIV 4)
End

(*
> EVAL ``two_sq 5``; = (1,2): thm   (1,1,1)
> EVAL ``two_sq 13``; = (3,2): thm  (3,1,1)
> EVAL ``two_sq 17``; = (1,4): thm  (1,2,2)
> EVAL ``two_sq 29``; = (5,2): thm  (5,1,1)
> EVAL ``two_sq 97``; = (9,4): thm  (9,2,2)
*)

(* Theorem: two_sq n = WHILE (\(x,y,z). y <> z) (zagier o flip) (1, 1, n DIV 4) *)
(* Proof: by two_sq_def, found_not. *)
Theorem two_sq_alt:
  !n. two_sq n = WHILE (\(x,y,z). y <> z) (zagier o flip) (1, 1, n DIV 4)
Proof
  simp[two_sq_def, found_not]
QED

(* Using direct WHILE, no need for Hoare specification. *)

(* Theorem: prime p /\ (p MOD 4 = 1) ==> two_sq p IN fixes flip (mills p) *)
(* Proof:
   Let s = mills p,
       f = zagier o flip,
       u = (1,1,p DIV 4),
       n = iterate_period f u.
   By two_sq_def, this is to show: WHILE ($~ o found) f u IN fixes flip s

   Note (~) o found = (\t. flip t <> t)    by found_def, flip_def, FUN_EQ_THM
   Thus the goal is: WHILE (\t. flip t <> t) f u IN fixes flip s

   Note ~square p               by prime_non_square
     so FINITE s                by mills_non_square_finite
    and zagier involute s       by zagier_involute_mills_prime
    and flip involute s         by flip_involute_mills
   also fixes zagier s = {u}    by zagier_fixes_prime
     so u IN fixes zagier s     by IN_SING
    and ODD n                   by involute_involute_fix_sing_period_odd
    ==> WHILE (\y. flip y <> y) f u IN fixes flip s
                                by involute_involute_fix_odd_period_fix_while
*)
Theorem two_sq_thm:
  !p. prime p /\ (p MOD 4 = 1) ==> two_sq p IN fixes flip (mills p)
Proof
  rw[two_sq_def] >>
  qabbrev_tac `s = mills p` >>
  qabbrev_tac `f = zagier o flip` >>
  qabbrev_tac `u = (1,1,p DIV 4)` >>
  qabbrev_tac `n = iterate_period f u` >>
  `(~) o found = \t. flip t <> t` by
  (rw[FUN_EQ_THM] >>
  `?x y z. t = (x,y,z)` by rw[triple_parts] >>
  rw[found_def, flip_def]) >>
  simp[] >>
  assume_tac (involute_involute_fix_odd_period_fix_while |> ISPEC ``zagier``) >>
  last_x_assum (qspecl_then [`flip`, `s`, `n`, `u`] strip_assume_tac) >>
  `~square p` by rw[prime_non_square] >>
  `FINITE s` by rw[mills_non_square_finite, Abbr`s`] >>
  `zagier involute s` by metis_tac[zagier_involute_mills_prime] >>
  `flip involute s` by metis_tac[flip_involute_mills] >>
  `fixes zagier s = {u}` by rw[zagier_fixes_prime, Abbr`s`, Abbr`u`] >>
  drule_then strip_assume_tac involute_involute_fix_sing_period_odd >>
  last_x_assum (qspecl_then [`zagier`, `flip`, `n`, `u`] strip_assume_tac) >>
  rfs[Abbr`f`]
QED

(* Very good -- nice and simple! *)

(* Theorem: prime p /\ (p MOD 4 = 1) ==>
            HOARE_SPEC (fixes zagier (mills p))
                       (WHILE ($~ o found) (zagier o flip))
                       (fixes flip (mills p)) *)
(* Proof:
   Let s = mills p,
       f = zagier o flip,
       u = (1,1,p DIV 4),
       n = iterate_period f u,
       h = n DIV 2,
       v = FUNPOW f h u,
       g = $~ o found,  use ~g to exit WHILE loop,
       a = fixes zagier s,
       b = fixes flip s.
   The goal is: HOARE_SPEC a (WHILE g f) b

   Note a = {u}             by zagier_fixes_prime
    and b = {v}             by flip_fixes_prime

   If n = 1, that is, period = 1 for prime p = 5.
   then u = (1,1,1)         by zagier_flip_1_1_z_period, triple_parts
     so ~g u                by definition of g, found_def
    but u IN s              by mills_element_trivial
     so u IN b              by fixes_element, flip_fix
    ==> b = a               by EQUAL_SING, IN_SING
   Thus HOARE_SPEC {u} (WHILE g f) {u}
                            by iterate_while_hoare_0
     or HOARE_SPEC a (WHILE g f) b.

   If n <> 1,
   Note ~square p           by prime_non_square
     so FINITE s            by mills_non_square_finite
    and zagier involute s   by zagier_involute_mills_prime
    and flip involute s     by flip_involute_mills
     so f PERMUTES s        by involute_involute_permutes
   Also 0 < n               by iterate_period_pos, u IN s
    and ODD n               by involute_involute_fix_sing_period_odd
     so n <> 2              by EVEN_2, ODD_EVEN
    ==> 1 + h < n           by HALF_ADD1_LT, 2 < n
     or h < n - 1           by arithmetic

    Now ~g v /\ (!j. j < h ==> g (FUNPOW f j u))
                                      by flip_fixes_iterates_prime, found_not
    Thus HOARE_SPEC a (WHILE g f) b   by iterate_while_hoare
*)
Theorem two_sq_while_hoare:
  !p. prime p /\ (p MOD 4 = 1) ==>
       HOARE_SPEC (fixes zagier (mills p))
                  (WHILE ($~ o found) (zagier o flip))
                  (fixes flip (mills p))
Proof
  rpt strip_tac >>
  qabbrev_tac `s = mills p` >>
  qabbrev_tac `f = zagier o flip` >>
  qabbrev_tac `u = (1,1,p DIV 4)` >>
  qabbrev_tac `n = iterate_period f u` >>
  qabbrev_tac `h = n DIV 2` >>
  qabbrev_tac `v = FUNPOW f h u` >>
  qabbrev_tac `g = $~ o found` >>
  qabbrev_tac `a = fixes zagier s` >>
  qabbrev_tac `b = fixes flip s` >>
  `u IN s` by rw[mills_element_trivial, Abbr`u`, Abbr`s`] >>
  `a = {u}` by rw[zagier_fixes_prime, Abbr`a`, Abbr`u`, Abbr`s`] >>
  `b = {v}` by metis_tac[flip_fixes_prime, SING_DEF] >>
  Cases_on `n = 1` >| [
    `u = (1,1,1)` by metis_tac[zagier_flip_1_1_z_period, triple_parts] >>
    `~g u` by fs[found_def, Abbr`g`] >>
    `u IN s` by rw[mills_element_trivial, Abbr`u`, Abbr`s`] >>
    `u IN b` by rw[fixes_element, flip_fix, Abbr`b`] >>
    `b = a` by metis_tac[EQUAL_SING, IN_SING] >>
    rw[iterate_while_hoare_0],
    `~square p` by rw[prime_non_square] >>
    `FINITE s` by metis_tac[mills_non_square_finite] >>
    `zagier involute s` by metis_tac[zagier_involute_mills_prime] >>
    `flip involute s` by metis_tac[flip_involute_mills] >>
    `f PERMUTES s` by fs[involute_involute_permutes, Abbr`f`] >>
    `0 < n` by metis_tac[iterate_period_pos] >>
    drule_then strip_assume_tac involute_involute_fix_sing_period_odd >>
    last_x_assum (qspecl_then [`zagier`, `flip`, `n`, `u`] strip_assume_tac) >>
    `ODD n` by rfs[] >>
    `n <> 2` by metis_tac[EVEN_2, ODD_EVEN] >>
    `1 + h < n` by rw[HALF_ADD1_LT, Abbr`h`] >>
    `h < n - 1` by decide_tac >>
    drule_then strip_assume_tac iterate_while_hoare >>
    last_x_assum (qspecl_then [`u`, `f`, `n-1`, `n`, `g`, `h`] strip_assume_tac) >>
    `~g v /\ (!j. j < h ==> g (FUNPOW f j u))` by metis_tac[found_not, flip_fixes_iterates_prime] >>
    rfs[]
  ]
QED

(* Theorem: prime p /\ (p MOD 4 = 1) ==>
            let (x,y,z) = WHILE ($~ o found) (zagier o flip) (1,1,p DIV 4)
            in p = x ** 2 + (y + z) ** 2 *)
(* Proof:
   Let s = mills p,
       u = (1,1,p DIV 4),
       a = fixes zagier s,
       b = fixes flip s.

   Note HOARE_SPEC a
        (WHILE ($~ o found) (zagier o flip)) b
                                  by two_sq_while_hoare
    and a = {u}                   by zagier_fixes_prime

   By HOARE_SPEC_DEF, this is to show:
   !s. a s ==> b (WHILE ($~ o found) (zagier o flip) s)
   Thus s = u                     by IN_SING, function as set
   Let w = WHILE ($~ o found) (zagier o flip) u.
   Then ?x y z. w = (x,y,z)       by triple_parts
    and w IN b                    by b w, function as set
     so w IN s /\ y = z           by fixes_element, flip_fix
   Thus p
      = windmill (x, y, z)        by mills_element, w IN s
      = windmill (x, y, y)        by y = z
      = x ** 2 + (2 * y) ** 2     by windmill_by_squares
      = x ** 2 + (y + z) ** 2     by arithmetic, y = z
*)
Theorem two_sq_while_thm:
  !p. prime p /\ (p MOD 4 = 1) ==>
       let (x,y,z) = WHILE ($~ o found) (zagier o flip) (1,1,p DIV 4)
        in p = x ** 2 + (y + z) ** 2
Proof
  rw_tac bool_ss[] >>
  drule_then strip_assume_tac two_sq_while_hoare >>
  rfs[whileTheory.HOARE_SPEC_DEF] >>
  qabbrev_tac `u = (1,1,p DIV 4)` >>
  `fixes zagier (mills p) = {u}` by rw[zagier_fixes_prime, Abbr`u`] >>
  last_x_assum (qspecl_then [`u`] strip_assume_tac) >>
  `(x,y,z) IN fixes flip (mills p)` by rfs[SPECIFICATION] >>
  `(x,y,z) IN (mills p) /\ (y = z)` by fs[fixes_element, flip_fix] >>
  metis_tac[mills_element, windmill_by_squares, DECIDE``y + y = 2 * y``]
QED

(* A beautiful theorem! *)

(* Define the algorithm. *)
Definition two_squares_def:
    two_squares n = let (x,y,z) = two_sq n in (x, y + z)
End

(*
> EVAL ``two_squares 5``; = (1,2)
> EVAL ``two_squares 13``; = (3,2)
> EVAL ``two_squares 17``; = (1,4)
> EVAL ``two_squares 29``; = (5,2)
> EVAL ``two_squares 97``;  = (9,4)
> EVAL ``MAP two_squares [5; 13; 17; 29; 37; 41; 53; 61; 73; 89; 97]``;
= [(1,2); (3,2); (1,4); (5,2); (1,6); (5,4); (7,2); (5,6); (3,8); (5,8); (9,4)]: thm
*)

(* Theorem: prime p /\ (p MOD 4 = 1) ==>
            let (u,v) = two_squares p in (p = u ** 2 + v ** 2) *)
(* Proof: by two_squares_def, two_sq_def, two_sq_while_thm. *)
Theorem two_squares_thm:
  !p. prime p /\ (p MOD 4 = 1) ==>
          let (u,v) = two_squares p in (p = u ** 2 + v ** 2)
Proof
  rw[two_squares_def, two_sq_def] >>
  drule_then strip_assume_tac two_sq_while_thm >>
  qabbrev_tac `loop = WHILE ($~ o found) (zagier o flip) (1,1,p DIV 4)` >>
  `?x y z. loop = (x,y,z)` by fs[triple_parts] >>
  fs[]
QED

(* Another proof of the same theorem, using two_sq_thm. *)

(* Theorem: prime p /\ (p MOD 4 = 1) ==>
            let (u,v) = two_squares p in (p = u ** 2 + v ** 2) *)
(* Proof:
   Let t = two_sq p.
   Then t IN fixes flip (mills p)        by two_sq_thm
    and ?x y z. t = (x,y,z)              by triple_parts
    ==> (x,y,z) IN mills p /\ (y = z)    by fixes_element, flip_fix
     so p = windmill (x, y, y)           by mills_element
          = x ** 2 + (2 * y) ** 2        by windmill_by_squares
          = x ** 2 + (y + z) ** 2        by y = z
          = u ** 2 + v ** 2              by two_squares_def
*)
Theorem two_squares_thm:
  !p. prime p /\ (p MOD 4 = 1) ==>
          let (u,v) = two_squares p in (p = u ** 2 + v ** 2)
Proof
  rw[two_squares_def] >>
  qabbrev_tac `t = two_sq p` >>
  `t IN fixes flip (mills p)` by rw[two_sq_thm, Abbr`t`] >>
  `?x y z. t = (x,y,z)` by rw[triple_parts] >>
  `(x,y,z) IN mills p /\ (y = z)` by fs[fixes_element, flip_fix] >>
  `p = windmill (x, y, y)` by fs[mills_element] >>
  simp[windmill_by_squares]
QED

(* ------------------------------------------------------------------------- *)
(* Fermat's Two Squares Theorem by Group Action.                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Relation to Fixes and Pairs.                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: f involute X ==> fixed_points (FUNPOW f) Z2 X = fixes f X *)
(* Proof:
   By fixed_points_def, fixes_def, EXTENSION, this is to show:
   (1) !a. a < 2 ==> (FUNPOW f a x = x) ==> f x = x
       Note f x = FUNPOW f 1 x = x          by FUNPOW_1, 1 < 2
   (2) f x = x ==> !a. a < 2 ==> FUNPOW f a x = x
       When a = 0, FUNPOW f 0 x = x         by FUNPOW_0
       When a = 1, FUNPOW f 1 x = f x = x   by FUNPOW_1, f x = x
*)
Theorem involute_fixed_points_eq_fixes:
  !f X. f involute X ==> fixed_points (FUNPOW f) Z2 X = fixes f X
Proof
  rw[fixed_points_def, fixes_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[FUNPOW_1, DECIDE``1 < 2``] >>
  (`a = 0 \/ a = 1` by decide_tac >> simp[])
QED

(* Theorem: f involute X ==> BIGUNION (multi_orbits (FUNPOW f) Z2 X) = pairs f X *)
(* Proof:
   By multi_orbits_def, pairs_def, BIGUNION, EXTENSION, this is to show:
   (1) x IN e /\ e IN orbits (FUNPOW f) Z2 X /\ ~SING e ==> x IN X /\ f x <> x
       Note x IN X                           by involute_orbits_element_element
        and e = orbit (FUNPOW f) Z2 x        by involute_orbits_element_is_orbit
       By contradiction, suppose f x = x,
       Then e = {x}                          by involute_orbit_fixed
       with contradicts ~SING e              by SING
   (2) x IN X /\ f x <> x ==> ?e. x IN e /\ e IN orbits (FUNPOW f) Z2 X /\ ~SING e
       Let e = {x; f x}.
       Then x IN e, and ~SING e              by f x <> x
       The goal is to show: {x; f x} IN orbits (FUNPOW f) Z2 X

       Note {x; f x}
          = orbit (FUNPOW f) Z2 x            by involute_orbit_not_fixed
       which is IN orbits (FUNPOW f) Z2 X    by funpow_orbit_in_orbits
*)
Theorem involute_multi_orbits_union_eq_pairs:
  !f X. f involute X ==> BIGUNION (multi_orbits (FUNPOW f) Z2 X) = pairs f X
Proof
  rw[multi_orbits_def, pairs_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[involute_orbits_element_element] >-
 (`x IN X` by metis_tac[involute_orbits_element_element] >>
  `s = orbit (FUNPOW f) Z2 x` by metis_tac[involute_orbits_element_is_orbit] >>
  metis_tac[involute_orbit_fixed, SING]) >>
  qexists_tac `{x; f x}` >>
  simp[] >>
  `{x; f x} = orbit (FUNPOW f) Z2 x` by metis_tac[involute_orbit_not_fixed] >>
  rw[funpow_orbit_in_orbits]
QED

(* ------------------------------------------------------------------------- *)
(* Fermat's Two-Squares Theorem (Existence)                                  *)
(* ------------------------------------------------------------------------- *)

(* With zagier and flip both involutions on (mills p),
    and zagier with a unique fixed point,
   this implies flip has at least a fixed point,
   giving the existence of Fermat's two squares.
*)

(* Proof based on involute_two_fixed_points_both_odd *)

(* Theorem: prime p /\ p MOD 4 = 1 ==>
            fixed_points (FUNPOW zagier) Z2 (mills p) = {(1,1,p DIV 4)} *)
(* Proof:
   By fixes_def, mills_def, this is to show:
   (1) p = windmill (x, y, z) /\ zagier (x,y,z) = (x,y,z) ==> (x,y,z) = (1,1,p DIV 4)
       Note ~square p                 by prime_non_square
        and x <> 0                    by mills_element, mills_triple_nonzero
         so x = y                     by zagier_fix
        ==> (x,y,z) = (1,1,p DIV 4)   by windmill_trivial_prime
   (2) p MOD 4 = 1 ==> p = windmill (1, 1, p DIV 4)
       This is true                   by windmill_trivial_prime
   (3) a < 2 ==> FUNPOW zagier p (1,1,p DIV 4) = (1,1,p DIV 4)
       When a = 0, true               by FUNPOW_0
       When a = 1, true               by FUNPOW_1, zagier_fix
*)
Theorem zagier_fixed_points_sing:
  !p. prime p /\ p MOD 4 = 1 ==>
      fixed_points (FUNPOW zagier) Z2 (mills p) = {(1,1,p DIV 4)}
Proof
  rw[fixed_points_def, mills_def, Zadd_element, EXTENSION] >>
  simp[EQ_IMP_THM] >>
  rpt strip_tac >| [
    rename1 ‘x = (x',y,z)’ >>
    `~square p` by metis_tac[prime_non_square] >>
    `p MOD 4 <> 0` by decide_tac >>
    `zagier x = x` by metis_tac[FUNPOW_1, DECIDE``1 < 2``] >>
    `x' = y` by metis_tac[zagier_fix, mills_element, mills_triple_nonzero] >>
    metis_tac[windmill_trivial_prime],
    metis_tac[windmill_trivial_prime],
    (`a = 0 \/ a = 1` by decide_tac >> fs[zagier_fix])
  ]
QED

(* A better proof of the same theorem *)

(* Theorem: prime p /\ p MOD 4 = 1 ==>
            fixed_points (FUNPOW zagier) Z2 (mills p) = {(1,1,p DIV 4)} *)
(* Proof:
   Let X = mills p, a = fixed_points (FUNPOW zagier) Z2 X.
   The goal is: a = {(1,1,p DIV 4)}.

   Note zagier involute X           by zagier_involute_mills_prime

   By EXTENSION, this is to show:
   (1) t IN X ==> t = (1,1,p DIV 4)
       Note t IN X                  by involute_fixed_points_element_element
        and zagier t = t            by involute_fixed_points
        Now ~square p               by prime_non_square
         so ?x y z. t = (x, y, z)   by triple_parts
        and x <> 0                  by mills_triple_nonzero, ~square p, p MOD 4 = 1
        ==> x = y                   by zagier_fix
       Note p = windmill (x, y, z)      by mills_element
        ==> (x,y,z) = (1,1,p DIV 4) by windmill_trivial_prime

   (2) (1,1,p DIV 4) IN a
       Note (1,1,p DIV 4) IN X      by mills_element_trivial
        and zagier (1,1,p DIV 4)
          = zagier (1,1,p DIV 4)    by zagier_1_1_z
         so (1,1,p DIV 4) IN a      by involute_fixed_points_iff
*)
Theorem zagier_fixed_points_sing:
  !p. prime p /\ p MOD 4 = 1 ==>
      fixed_points (FUNPOW zagier) Z2 (mills p) = {(1,1,p DIV 4)}
Proof
  rpt strip_tac >>
  qabbrev_tac `X = mills p` >>
  qabbrev_tac `a = fixed_points (FUNPOW zagier) Z2 X` >>
  `zagier involute X` by  metis_tac[zagier_involute_mills_prime] >>
  rw[EXTENSION, EQ_IMP_THM] >| [
    `x IN X` by metis_tac[involute_fixed_points_element_element] >>
    `zagier x = x` by metis_tac[involute_fixed_points] >>
    `?x1 y z. x = (x1, y, z)` by rw[triple_parts] >>
    `x1 <> 0` by metis_tac[mills_triple_nonzero, prime_non_square, ONE_NOT_ZERO] >>
    `x1 = y` by fs[zagier_fix] >>
    metis_tac[windmill_trivial_prime, mills_element],
    `(1,1,p DIV 4) IN X` by rw[mills_element_trivial, Abbr`X`] >>
    metis_tac[zagier_1_1_z, involute_fixed_points_iff]
  ]
QED

(* Theorem: prime p /\ p MOD 4 = 1 ==> ?(u,v). p = u ** 2 + v ** 2 *)
(* Proof:
   Let X = mills p, the solutions (x,y,z) of p = x ** 2 + 4 * y * z.
   Note ~square p                      by prime_non_square
     so FINITE X                       by mills_non_square_finite
    Now !x y z. (x,y,z) IN X ==>
        x <> 0 /\ y <> 0 /\ z <> 0     by mills_triple_nonzero
    and zagier involute X              by zagier_involute_mills_prime
    and flip involute X                by flip_involute_mills

   Let a = fixed_points (FUNPOW zagier) Z2 X,
       b = fixed_points (FUNPOW flip) Z2 X.
   Then ODD (CARD a) <=> ODD (CARD b)  by involute_two_fixed_points_both_odd

   The punch line:
   Let k = p DIV 4.
   Then a = {(1,1,k)}                  by zagier_fixed_points_sing
   Thus CARD a = 1                     by CARD_SING
     so ODD (CARD b)                   by ODD_1, above
    ==> CARD b <> 0                    by EVEN_0
     or b <> EMPTY                     by CARD_EMPTY
   thus ?x y z. (x,y,z) IN b           by MEMBER_NOT_EMPTY, triple_parts
     so flip (x, y, z) = (x, y, z)     by involute_fixed_points
    ==> y = z                          by flip_fix
   Note (x,y,z) IN X                   by fixed_points_element
   Put (u,v) = (x,2 * y).
   Then p = u ** 2 + v ** 2            by mills_element, windmill_by_squares
*)
Theorem fermat_two_squares_exists_alt:
  !p. prime p /\ p MOD 4 = 1 ==> ?(u,v). p = u ** 2 + v ** 2
Proof
  rw[ELIM_UNCURRY] >>
  qabbrev_tac `X = mills p` >>
  `~square p` by metis_tac[prime_non_square] >>
  `FINITE X` by fs[mills_non_square_finite, Abbr`X`] >>
  `zagier involute X` by metis_tac[zagier_involute_mills_prime] >>
  `flip involute X` by metis_tac[flip_involute_mills] >>
  qabbrev_tac `a = fixed_points (FUNPOW zagier) Z2 X` >>
  qabbrev_tac `b = fixed_points (FUNPOW flip) Z2 X` >>
  `ODD (CARD a) <=> ODD (CARD b)` by rw[involute_two_fixed_points_both_odd, Abbr`a`, Abbr`b`] >>
  qabbrev_tac `k = p DIV 4` >>
  `a = {(1,1,k)}` by rw[zagier_fixed_points_sing, Abbr`a`, Abbr`X`, Abbr`k`] >>
  `CARD a = 1` by rw[] >>
  `CARD b <> 0` by metis_tac[ODD_1, EVEN_0, ODD_EVEN] >>
  `b <> EMPTY` by metis_tac[CARD_EMPTY] >>
  `?x y z. (x,y,z) IN b` by metis_tac[MEMBER_NOT_EMPTY, triple_parts] >>
  `flip (x, y, z) = (x, y, z)` by metis_tac[involute_fixed_points] >>
  `y = z` by fs[flip_fix] >>
  `(x,y,z) IN X` by fs[fixed_points_element, Abbr`b`] >>
  qexists_tac `(x, 2 * y)` >>
  simp[] >>
  metis_tac[mills_element, windmill_by_squares]
QED

(* Very good! *)

(* ------------------------------------------------------------------------- *)
(* References                                                                *)
(* ------------------------------------------------------------------------- *)

(*

Biscuits of Number Theory (Arthur T. BenjamIN snd Ezra Brown editors)
ISBN: 9780883853405
Part IV: Sum of Squares and Polygonal Numbers
p.143
A One-Sentence Proof that Every Prime p = 1 (mod 4) is a Sum of Two Squares
Don Zagier


An Algorithm to List All the Fixed-Point Free Involutions on a Finite Set
Cyril Prissette (20 Jun 2010)
https://hal.archives-ouvertes.fr/hal-00493605/document

The One-Sentence Proof in Multiple Sentences
Marcel Moosbrugger (Feb 3, 2020)
https://medium.com/cantors-paradise/the-one-sentence-proof-in-multiple-sentences-ab2657efc576

*)


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
