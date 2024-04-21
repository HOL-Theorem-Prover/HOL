(* ------------------------------------------------------------------------- *)
(* Fermat's Two Squares Theorem: a proof using corner shapes.                *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "corner";

(* ------------------------------------------------------------------------- *)

open arithmeticTheory pred_setTheory dividesTheory gcdsetTheory numberTheory
     pairTheory combinatoricsTheory;

open helperTwosqTheory;

open quarityTheory;

(* val _ = load "involuteFixTheory"; *)
open involuteTheory;
open involuteFixTheory;

val _ = temp_overload_on("SQ", ``\n. n * (n :num)``);
val _ = temp_overload_on("HALF", ``\n. n DIV 2``);
val _ = temp_overload_on("TWICE", ``\n. 2 * n``);

(* ------------------------------------------------------------------------- *)
(* Fermat Two Squares by Corners Documentation                               *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   Helper Theorems:
   quadruples_parts    |- !q. ?a x b y. q = (a,x,b,y)

   The set of corner pieces:
   corners_def         |- !n. corners n = {(a,x,b,y) | n = a * x + b * y /\ 0 < x /\ 0 < y /\ 0 < a /\ a < b}
   corners_subset      |- !n. corners n SUBSET (let s = count (n + 1) in s CROSS s CROSS s CROSS s)
   corners_finite      |- !n. FINITE (corners n)
   corners_empty       |- !n. corners n = {} <=> n <= 2

   Conjugation of corners:
   conjugate_def       |- !a x b y. conjugate (a,x,b,y) = (y,b - a,y + x,a)
   conjugate_involute  |- !a b x y. a < b ==> conjugate (conjugate (a,x,b,y)) = (a,x,b,y)
   conjugate_involute_corners
                       |- !n. conjugate involute (corners n)
   conjugate_fix       |- !a b x y. conjugate (a,x,b,y) = (a,x,b,y) <=> a = y /\ b = x + y
   conjugate_fix_lt    |- !a b x y. a < b ==> (conjugate (a,x,b,y) = (a,x,b,y) <=> x = b - a /\ y = a)
   corners_conjugate_fixes
                       |- !n a b. fixes conjugate (corners n) =
                                  {(a,b - a,b,a) | n = a * (2 * b - a) /\ 0 < a /\ a < b}

   Transpose of corners:
   transpose_def       |- !a x b y. transpose (a,x,b,y) =
                                    if x < y then (x,a,y,b)
                                    else if y < x then (y,b,x,a)
                                    else (a,x,b,y)
   transpose_involute  |- !a b x y. a < b ==> transpose (transpose (a,x,b,y)) = (a,x,b,y)
   transpose_involute_corners
                       |- !n. transpose involute (corners n)
   transpose_fix       |- !a x b y. transpose (a,x,b,y) = (a,x,b,y) <=>
                                    if x < y then x = a /\ y = b
                                    else if y < x then x = b /\ y = a
                                    else T
   corners_less_fix_def    |- !n. corners_less_fix n = {(a,a,b,b) | n = a ** 2 + b ** 2 /\ 0 < a /\ a < b}
   corners_more_fix_def    |- !n. corners_more_fix n = {(a,b,b,a) | n = 2 * a * b /\ 0 < a /\ a < b}
   corners_eq_fix_def      |- !n. corners_eq_fix n = {(a,c,b,c) | n = (a + b) * c /\ 0 < a /\ a < b /\ 0 < c}
   corners_less_fix_element|- !n q. q IN corners_less_fix n <=>
                                    ?a b. q = (a,a,b,b) /\ n = a ** 2 + b ** 2 /\ 0 < a /\ a < b
   corners_more_fix_element|- !n q. q IN corners_more_fix n <=>
                                    ?a b. q = (a,b,b,a) /\ n = 2 * a * b /\ 0 < a /\ a < b
   corners_eq_fix_element  |- !n q. q IN corners_eq_fix n <=>
                                    ?a b c. q = (a,c,b,c) /\ n = (a + b) * c /\ 0 < a /\ a < b /\ 0 < c
   corners_less_fix_subset |- !n. corners_less_fix n SUBSET corners n
   corners_more_fix_subset |- !n. corners_more_fix n SUBSET corners n
   corners_eq_fix_subset   |- !n. corners_eq_fix n SUBSET corners n
   corners_less_fix_finite |- !n. FINITE (corners_less_fix n)
   corners_more_fix_finite |- !n. FINITE (corners_more_fix n)
   corners_eq_fix_finite   |- !n. FINITE (corners_eq_fix n)
   corners_more_fix_empty  |- !n. ODD n ==> corners_more_fix n = {}
   corners_more_fix_eq_empty
                           |- !n. corners_more_fix n = {} <=> n = 0 \/ n = 2 \/ ODD n
   corners_transpose_fixes |- !n. fixes transpose (corners n) =
                                  corners_less_fix n UNION corners_more_fix n UNION corners_eq_fix n
   corners_transpose_fixes_subset  |- !n. fixes transpose (corners n) SUBSET corners n
   corners_transpose_fixes_finite  |- !n. FINITE (fixes transpose (corners n))
   corners_transpose_fixes_card    |- !n. CARD (fixes transpose (corners n)) =
                                          CARD (corners_less_fix n) +
                                          CARD (corners_more_fix n) +
                                          CARD (corners_eq_fix n)

   Fermat's Two Squares Theorem:
   prime_corners_eq_fix        |- !p. prime p ==>
                                      corners_eq_fix p = {(a,1,b,1) | p = a + b /\ 0 < a /\ a < b}
   prime_corners_eq_fix_eqn    |- !p. prime p ==>
                                      corners_eq_fix p = IMAGE (\a. (a,1,p - a,1)) (natural (HALF (p - 1)))
   prime_corners_eq_fix_card   |- !p. prime p ==> CARD (corners_eq_fix p) = HALF (p - 1)
   prime_corners_conjugate_fixes
                               |- !p. prime p ==> fixes conjugate (corners p) =
                                      if p = 2 then {} else {(1,HALF (p - 1),HALF (p + 1),1)}
   prime_corners_more_fix      |- !p. prime p ==> corners_more_fix p = {}
   tik_prime_corners_less_fix  |- !p. tik p /\ prime p ==> corners_less_fix p <> {}
   fermat_two_squares_by_corners
                               |- !p. tik p /\ prime p ==> ?a b. p = a ** 2 + b ** 2 /\ a < b

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ?a x b y. q = (a,x,b,y) *)
(* Proof: by a = FST q, x = FST (SND q), etc. *)
Theorem quadruples_parts:
  !q: num # num # num # num. ?a x b y. q = (a,x,b,y)
Proof
  metis_tac[PAIR]
QED

(* ------------------------------------------------------------------------- *)
(* The set of corner pieces.                                                 *)
(* ------------------------------------------------------------------------- *)

(*
Geometrically a corner piece looks like the Greek captial letter Γ:

               b                                    y       x
       +-----------------+                      +-------+----------+
       |                 |                      |       |          |
       |                 | y                    |       |          | a
       +-----------+-----+      conjugation   b |       |          |
       |           |                            |       +----------+
       |           | x                          |       |
       |           |                            |       |
       +-----------+                            +-------+
             a

So that the area corresponds to a number n = a * x + b * y.
The conditions 0 < x, 0 < y, 0 < a < b makes a valid shape, with a corner near the top-left.

The conjugation η : (a,x,b,y) → (y,b-a,y+x,a), a reflection about the slanting diagonal,
is an involution.

*)

(* Define the set of corner pieces for n *)
Definition corners_def[nocompute]:
   corners n = {(a,x,b,y) | n = a * x + b * y /\ 0 < x /\ 0 < y /\ 0 < a /\ a < b }
End
(* use [nocompute] as this is not effective. *)

(* Theorem: (a,x,b,y) IN corners n <=> n = a * x + b * y /\ 0 < x /\ 0 < y /\ 0 < a /\ a < b *)
(* Proof: by corners_def. *)
Theorem corners_element:
  !n a b x y. (a,x,b,y) IN corners n <=> n = a * x + b * y /\ 0 < x /\ 0 < y /\ 0 < a /\ a < b
Proof
  simp[corners_def]
QED

(* Theorem: corners n SUBSET (let s = count (n + 1) in s CROSS s CROSS s CROSS s) *)
(* Proof:
   By SUBSET_DEF, IN_COUNT, IN_CROSS, this is to show:
      (a,x,b,y) IN corners n ==> a <= n /\ b <= n /\ x <= n /\ y <= n
   Note n = a * x + b * y          by corners_def
     so a * x <= n                 by inequality
    and b * y <= n                 by inequality
    ==> x <= n /\ y <= n           by MULT_LE_IMP_LE
    and a <= n /\ b <= n           by MULT_LE_IMP_LE, MULT_COMM
*)
Theorem corners_subset:
  !n. corners n SUBSET (let s = count (n + 1) in s CROSS s CROSS s CROSS s)
Proof
  simp[SUBSET_DEF, FORALL_PROD] >>
  ntac 6 strip_tac >>
  rename1 `(a,x,b,y) IN _` >>
  fs[corners_def] >>
  `0 < b` by decide_tac >>
  `0 < n` by metis_tac[ADD_EQ_0, MULT_EQ_0, NOT_ZERO] >>
  `a <= n /\ x <= n /\ b <= n /\ y <= n` suffices_by simp[] >>
  `a * x <= n /\ b * y <= n` by decide_tac >>
  metis_tac[MULT_LE_IMP_LE, MULT_COMM]
QED

(* Theorem: FINITE (corners n) *)
(* Proof:
   Let s = count (n + 1),
       t = s CROSS s CROSS s CROSS s.
   Note (corners n) SUBSET t       by corners_subset
    and FINITE s                   by FINITE_COUNT
     so FINITE t                   by FINITE_CROSS
    ==> FINITE (corners n)         by SUBSET_FINITE
*)
Theorem corners_finite:
  !n. FINITE (corners n)
Proof
  metis_tac[corners_subset, FINITE_COUNT, FINITE_CROSS, SUBSET_FINITE]
QED

(* Theorem: corners n = {} <=> n <= 2 *)
(* Proof:
   If part: corners n = {} ==> n <= 2
      By contradiction, suppose ~(n <= 2).
      Then 2 < n                               by inequality
        so n = 1 * 1 + (n - 1) * 1             by arithmetic
       and 1 < n - 1                           by inequality
       ==> (1,1,n - 1,1) IN corners n          by corners_def
      This contradicts corners n = {}          by MEMBER_NOT_EMPTY
   Only-if part: n <= 2 ==> corners n = {}
      By contradiction, suppose corners n <> {}.
      Then ?q. q = (a,x,b,y) IN corners n      by MEMBER_NOT_EMPTY
       and n = a * x + b * y /\ 0 < a /\ a < b by corners_def
       Now 0 < b, given 0 < x /\ 0 < y         by inequality, 0 < a < b
        so 0 < a * x /\ 0 < b * y              by LESS_MULT2
       ==> 2 <= a * x + b * y                  by arithmetic
       This makes n = 2                        by 2 <= n <= 2
       ==> a * x = 1 /\ b * y = 1              by ADD_EQ_2
       ==> a = 1     /\ b = 1                  by MULT_EQ_1
       This contradicts a < b                  by LESS_REFL
*)
Theorem corners_empty:
  !n. corners n = {} <=> n <= 2
Proof
  rw[EXTENSION, EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `2 < n` by decide_tac >>
    `n = 1 * 1 + (n - 1) * 1 /\ 1 < n - 1` by decide_tac >>
    `(1,1,n - 1,1) IN corners n` by fs[corners_def] >>
    metis_tac[],
    spose_not_then strip_assume_tac >>
    rename1 `q IN _` >>
    fs[corners_def] >>
    `0 < b` by decide_tac >>
    `0 < a * x /\ 0 < b * y` by simp[] >>
    `n = 2` by decide_tac >>
    metis_tac[ADD_EQ_2, MULT_EQ_1, DECIDE``~(1 < 1)``]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* Conjugation of corners.                                                   *)
(* ------------------------------------------------------------------------- *)

(* Define the conjugate of a corner piece. *)
Definition conjugate_def:
   conjugate (a, x, b, y) = (y, b - a, y + x, a)
End

(* Theorem: a < b ==> conjugate (conjugate (a, x, b, y)) = (a, x, b, y) *)
(* Proof:
     conjugate (conjugate (a, x, b, y))
   = conjugate (y, b - a, y + x, a)            by conjugate_def
   = (a, (y + x) - y, a + (b - a), y)          by conjugate_def
   = (a, x, b, y)                              by arithmetic
*)
Theorem conjugate_involute:
  !a b x y. a < b ==> conjugate (conjugate (a, x, b, y)) = (a, x, b, y)
Proof
  simp[conjugate_def]
QED

(* Theorem: conjugate involute (corners n) *)
(* Proof:
   Note q = (a,x,b,y) with 0 < a /\ a < b /\ 0 < x /\ 0 < y /\
        n = a * x + b * y                      by corners_def
    and conjugate q = (y,b-a,y+x,a)            by conjugate_def
        y * (b - a) + (y + x) * a
      = y * b - y * a + y * a + x * a          by arithmetic
      = y * b + x * a                          by arithmetic
      = a * x + b * y = n
    and 0 < b - a                              by a < b
    and 0 < y + x                              by 0 < x, 0 < y
     so conjuate q IN corners n                by corners_def
    and conjugate (conjugate q) = q            by conjugate_involute, a < b
*)
Theorem conjugate_involute_corners:
  !n. conjugate involute (corners n)
Proof
  ntac 3 strip_tac >>
  rename1 `q IN _` >>
  fs[corners_def] >>
  strip_tac >| [
    map_every qexists_tac [`y`, `b-a`, `y+x`, `a`] >>
    simp[conjugate_def] >>
    `y * a < y * b` by fs[] >>
    `a * (x + y) + y * (b - a) = a * x + a * y + (y * b - y * a)` by simp[] >>
    decide_tac,
    simp[conjugate_involute]
  ]
QED

(* Theorem: conjugate (a,x,b,y) = (a,x,b,y) <=> (a = y /\ b = x + y) *)
(* Proof:
     (a,x,b,y)
   = conjugate (a,x,b,y)           by assumption
   = (y,b - a,y + x,a)             by conjugate_def
   ==> a = y,
       x = b = a,
       b = y + x,
       y = a                       by equating components
   ==> a = y, b = x + y            by arithmetic
*)
Theorem conjugate_fix:
  !a b x y. conjugate (a,x,b,y) = (a,x,b,y) <=> (a = y /\ b = x + y)
Proof
  simp[conjugate_def]
QED

(* Theorem: a < b ==> (conjugate (a,x,b,y) = (a,x,b,y) <=> (x = b - a /\ y = a)) *)
(* Proof:
       conjugate (a,x,b,y) = (a,x,b,y)
   <=> a = y /\ b = x + y                      by conjugate_fix
   <=> y = a /\ x + a = b                      by y = a
   <=> y = a /\ x = b - a                      by arithmetic, a < b
*)
Theorem conjugate_fix_lt:
  !a b x y. a < b ==> (conjugate (a,x,b,y) = (a,x,b,y) <=> (x = b - a /\ y = a))
Proof
  simp[conjugate_def]
QED

(* Theorem: fixes conjugate (corners n) =
            {(a,b - a,b,a) | n = a * (2 * b - a) /\ 0 < a /\ a < b} *)
(* Proof:
   By fixes_def, EXTENSION, this is to show:
   (1) q IN corners n /\ conjugate q = q ==>
       ?a b. q = (a,b - a,b,a) /\ n = a * (2 * b - a) /\ 0 < a /\ a < b
       Note q = (a,x,b,y) /\ n = a * x + b * y /\ a < b  by corners_def
        and conjugate q = q ==> x = b - a /\ y = a       by conjugate_fix_lt
            n = a * x + b * y
              = a * (b - a) + b * a                      by above
              = a * b + a * (b - a)                      by ADD_COMM, MULT_COMM
              = a * (b + (b - a))                        by LEFT_ADD_DISTRIB
              = a * (2 * b - a)                          by arithmetic
   (2) n = a * (2 * b - a) /\ q = (a,b - a,b,a) /\ 0 < a /\ a < b ==>
       q IN corners n /\ conjugate q = q
       Note n = a * (2 * b - a)
              = a * (b + (b - a))                        by arithmetic, a < b
              = a * b + a * (b - a)                      by LEFT_ADD_DISTRIB
              = a * (b - a) + b * a                      by MULT_COMM, ADD_COMM
         so q = (a, b - a, b, a) IN corners n            by corners_def
        and conjugate q = q                              by conjugate_fix_lt
*)
Theorem corners_conjugate_fixes:
  !n a b. fixes conjugate (corners n) =
            {(a,b - a,b,a) | n = a * (2 * b - a) /\ 0 < a /\ a < b}
Proof
  rw[fixes_def, EXTENSION, EQ_IMP_THM] >| [
    rename1 `q IN _` >>
    fs[corners_def] >>
    `x = b - a /\ y = a` by rfs[conjugate_fix_lt] >>
    simp[] >>
    simp[GSYM LEFT_ADD_DISTRIB],
    simp[corners_def] >>
    simp[GSYM LEFT_ADD_DISTRIB],
    simp[conjugate_fix_lt]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* Transpose of corners.                                                     *)
(* ------------------------------------------------------------------------- *)

(* Define the transpose of a corner piece. *)
Definition transpose_def:
   transpose (a:num, x, b:num, y) = if x < y then (x, a, y, b)
                                    else if y < x then (y, b, x, a)
                                    else (a, x, b, y)
End

(* Theorem: a < b ==> transpose (transpose (a,x,b,y)) = (a,x,b,y) *)
(* Proof:
   If x < y,  transpose (transpose (a,x,b,y))
            = transpose (x,a,y,b)              by transpose_def, x < y
            = (a,x,b,y)                        by transpose_def, a < b
   If y < x,  transpose (transpose (a,x,b,y))
            = transpose (y,b,x,a)              by transpose_def, y < x
            = (a,x,b,y)                        by transpose_def, a < b
   If x = y,  transpose (transpose (a,x,b,y))
            = transpose (a,x,b,y)              by transpose_def, x = y
            = (a,x,b,y)                        by transpose_def, x = y
*)
Theorem transpose_involute:
  !a b x y. a < b ==> transpose (transpose (a,x,b,y)) = (a,x,b,y)
Proof
  rw[transpose_def]
QED

(* Theorem: transpose involute (corners n) *)
(* Proof:
   Note q = (a,x,b,y) with 0 < a /\ a < b /\ 0 < x /\ 0 < y /\
        n = a * x + b * y                      by corners_def
   If x < y, transpose q = (x,a,y,b)           by transpose_def
        x * a + y * b
      = a * x + b * y = n                      by MULT_COMM
     so transpose q IN corners n               by corners_def
   If y > x, transpose q = (y,b,x,a)           by transpose_def
        y * b + x * a
      = a * x + b * y = n                      by ADD_COMM, MULT_COMM
     so transpose q IN corners n               by corners_def
   If x = y, transpose q = (a,y,b,x)           by transpose_def
        a * y + b * x
      = a * x + b * y = n                      by x = y
     so transpose q IN corners n               by corners_def
   Also transpose (transpose q) = q            by transpose_involute, a < b
*)
Theorem transpose_involute_corners:
  !n. transpose involute (corners n)
Proof
  ntac 3 strip_tac >>
  rename1 `q IN _` >>
  fs[corners_def] >>
  strip_tac >| [
    `x < y \/ y < x \/ x = y` by simp[num_nchotomy] >| [
      map_every qexists_tac [`x`, `a`, `y`, `b`] >>
      simp[transpose_def],
      map_every qexists_tac [`y`, `b`, `x`, `a`] >>
      simp[transpose_def],
      map_every qexists_tac [`a`, `y`, `b`, `x`] >>
      simp[transpose_def]
    ],
    simp[transpose_involute]
  ]
QED

(* Theorem: transpose (a,x,b,y) = (a,x,b,y) <=>
             if x < y then x = a /\ y = b else if y < x then x = b /\ y = a else T *)
(* Proof:
   If x < y,
        transpose (a,x,b,y) = (a,x,b,y)
   <=>            (x,a,y,b) = (a,x,b,y)        by transpose_def, x < y
   <=>             x = a /\ y = b              by equating components
   If y < x,
        transpose (a,x,b,y) = (a,x,b,y)
   <=>            (y,b,x,a) = (a,x,b,y)        by transpose_def, y < x
   <=>             y = a /\ x = b              by equating components
   If x = y,
        transpose (a,x,b,y) = (a,x,b,y)
   <=>            (a,x,b,y) = (a,x,b,y)        by transpose_def, x = y
   which is always true.
*)
Theorem transpose_fix:
  !a x b y. transpose (a,x,b,y) = (a,x,b,y) <=>
             if x < y then x = a /\ y = b else if y < x then x = b /\ y = a else T
Proof
  rw[transpose_def]
QED

(* Define the sets of transpose fixes in corners. *)

Definition corners_less_fix_def[nocompute]:
   corners_less_fix n = {(a,a,b,b) | n = a ** 2 + b ** 2 /\ 0 < a /\ a < b }
End

Definition corners_more_fix_def[nocompute]:
   corners_more_fix n = {(a,b,b,a) | n = 2 * a * b /\ 0 < a /\ a < b }
End

Definition corners_eq_fix_def[nocompute]:
   corners_eq_fix n = {(a,c,b,c) | n = (a + b) * c /\ 0 < a /\ a < b /\ 0 < c }
End

(* Theorem: q IN (corners_less_fix n) <=> ?a b. q = (a,a,b,b) /\ n = a ** 2 + b ** 2 /\ 0 < a /\ a < b *)
(* Proof: by corners_less_fix_def. *)
Theorem corners_less_fix_element:
  !n q. q IN (corners_less_fix n) <=> ?a b. q = (a,a,b,b) /\ n = a ** 2 + b ** 2 /\ 0 < a /\ a < b
Proof
  simp[corners_less_fix_def]
QED

(* Theorem: q IN (corners_more_fix n) <=> ?a b. q = (a,b,b,a) /\ n = 2 * a * b /\ 0 < a /\ a < b *)
(* Proof: by corners_more_fix_def. *)
Theorem corners_more_fix_element:
  !n q. q IN (corners_more_fix n) <=> ?a b. q = (a,b,b,a) /\ n = 2 * a * b /\ 0 < a /\ a < b
Proof
  simp[corners_more_fix_def]
QED

(* Theorem: q IN (corners_eq_fix n) <=> ?a b c. q = (a,c,b,c) /\ n = (a + b) * c /\ 0 < a /\ a < b /\ 0 < c *)
(* Proof: by corners_eq_fix_def. *)
Theorem corners_eq_fix_element:
  !n q. q IN (corners_eq_fix n) <=> ?a b c. q = (a,c,b,c) /\ n = (a + b) * c /\ 0 < a /\ a < b /\ 0 < c
Proof
  simp[corners_eq_fix_def] >>
  metis_tac[]
QED

(* Theorem: corners_less_fix n SUBSET corners n *)
(* Proof:
   By SUBSET_DEF, this is to show:
      q IN (corners_less_fix n) ==> q IN (corners n)
   Note ?a b. q = (a,a,b,b) /\
              n = a ** 2 + b ** 2 /\ 0 < a /\ a < b    by corners_less_fix_def
    and       n = a * a + b * b                        by EXP_2
    Let x = a, y = b,
    then q = (a,x,b,y) IN corners n                    by corners_def
*)
Theorem corners_less_fix_subset:
  !n. corners_less_fix n SUBSET corners n
Proof
  rw[corners_less_fix_def, corners_def, SUBSET_DEF]
QED

(* Theorem: corners_more_fix n SUBSET corners n *)
(* Proof:
   By SUBSET_DEF, this is to show:
      q IN (corners_more_fix n) ==> q IN (corners n)
   Note ?a b. q = (a,b,b,a) /\
              n = 2 * a * b /\ 0 < a /\ a < b          by corners_more_fix_def
    and       n = a * b + b * a                        by arithmetic
    Let x = b, y = a,
    then q = (a,x,b,y) IN corners n                    by corners_def
*)
Theorem corners_more_fix_subset:
  !n. corners_more_fix n SUBSET corners n
Proof
  rw[corners_more_fix_def, corners_def, SUBSET_DEF]
QED

(* Theorem: corners_eq_fix n SUBSET corners n *)
(* Proof:
   By SUBSET_DEF, this is to show:
      q IN (corners_eq_fix n) ==> q IN (corners n)
   Note ?a b. q = (a,c,b,c) /\
              n = (a + b) * c /\ 0 < a /\ a < b        by corners_eq_fix_def
    and       n = a * c + b * c                        by RIGHT_ADD_DISTRIB
    Let x = c, y = c,
    then q = (a,x,b,y) IN corners n                    by corners_def
*)
Theorem corners_eq_fix_subset:
  !n. corners_eq_fix n SUBSET corners n
Proof
  rw[corners_eq_fix_def, corners_def, SUBSET_DEF]
QED

(* Theorem: FINITE (corners_less_fix n) *)
(* Proof:
   Note (corners_less_fix n) SUBSET (corners n)        by corners_less_fix_subset
    and FINITE (corners n)                             by corners_finite
     so FINITE (corners_less_fix n)                    by SUBSET_FINITE
*)
Theorem corners_less_fix_finite:
  !n. FINITE (corners_less_fix n)
Proof
  metis_tac[corners_less_fix_subset, corners_finite, SUBSET_FINITE]
QED

(* Theorem: FINITE (corners_more_fix n) *)
(* Proof:
   Note (corners_more_fix n) SUBSET (corners n)        by corners_more_fix_subset
    and FINITE (corners n)                             by corners_finite
     so FINITE (corners_more_fix n)                    by SUBSET_FINITE
*)
Theorem corners_more_fix_finite:
  !n. FINITE (corners_more_fix n)
Proof
  metis_tac[corners_more_fix_subset, corners_finite, SUBSET_FINITE]
QED

(* Theorem: FINITE (corners_eq_fix n) *)
(* Proof:
   Note (corners_eq_fix n) SUBSET (corners n)          by corners_eq_fix_subset
    and FINITE (corners n)                             by corners_finite
     so FINITE (corners_eq_fix n)                      by SUBSET_FINITE
*)
Theorem corners_eq_fix_finite:
  !n. FINITE (corners_eq_fix n)
Proof
  metis_tac[corners_eq_fix_subset, corners_finite, SUBSET_FINITE]
QED


(* Theorem: ODD n ==> corners_more_fix n = {} *)
(* Proof:
   By contradiction, suppose corners_more_fix n <> {}.
   Then ?q. q = (a,b,b,a) /\
            n = 2 * a * b /\ 0 < a /\ a < b    by corners_more_fix_def
    ==> EVEN n                                 by EVEN_DOUBLE
   This contradicts ODD n                      by ODD_EVEN
*)
Theorem corners_more_fix_empty:
  !n. ODD n ==> corners_more_fix n = {}
Proof
  rw[corners_more_fix_def, EXTENSION] >>
  fs[EVEN_DOUBLE, ODD_EVEN]
QED

(* Theorem: corners_more_fix n = {} <=> n = 0 \/ n = 2 \/ ODD n *)
(* Proof:
   If part: corners_more_fix n = {} ==> n = 0 \/ n = 2 \/ ODD n
      By contradiction, suppose ~ODD n /\ n <> 0 /\ n <> 2.
      Then EVEN n                              by ODD_EVEN
        so ?k. n = 2 * k                       by EVEN_EXISTS
       and 1 < k                               by n <> 0, n <> 2
       Now n = 2 * 1 * k                       by arithmetic
       ==> (1,k,k,1) IN corners_more_fix n     by corners_more_fix_def
      This contradicts corners_more_fix n = {} by MEMBER_NOT_EMPTY
   Only-if part: n = 0 \/ n = 2 \/ ODD n ==> corners_more_fix n = {}
     This case ODD n is true                   by corners_more_fix_empty
     For other cases, by contradiction, suppose corners_more_fix n <> {}.
     Then ?q. q = (a,b,b,a) /\
              n = 2 * a * b /\ 0 < a /\ a < b  by corners_more_fix_def
       so a * b = HALF n                       by HALF_TWICE
      For n = 0, HALF 0 = 0.
          this makes a = 0 \/ b = 0            by MULT_EQ_0
           but contradicts either 0 < a or a < b.
      For n = 2, HALF 2 = 1.
          this makes a = 1 /\ b = 1            by MULT_EQ_1
           but contradicts a < b.
*)
Theorem corners_more_fix_eq_empty:
  !n. corners_more_fix n = {} <=> (n = 0 \/ n = 2 \/ ODD n)
Proof
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `?k. n = 2 * k` by fs[ODD_EVEN, EVEN_EXISTS] >>
    `k <> 0 /\ k <> 1` by decide_tac >>
    `1 < k /\ n = 2 * 1 * k` by decide_tac >>
    `(1,k,k,1) IN corners_more_fix n` by rfs[corners_more_fix_def] >>
    rfs[],
    rw[corners_more_fix_def],
    rw[corners_more_fix_def],
    simp[corners_more_fix_empty]
  ]
QED

(* Theorem: fixes transpose (corners n) =
            (corners_less_fix n) UNION (corners_more_fix n) UNION (corners_eq_fix n) *)
(* Proof:
   By fixes_def, IN_UNION, EXTENSION, this is to show:
   (1) q IN corners n /\ transpose q = q ==>
       q IN (corners_less_fix n) \/ q IN (corners_more_fix n) \/ q IN (corners_eq_fix n)
       Note q = (a,x,b,y) /\
            n = a * x + b * y /\ 0 < a /\ a < b        by corners_def
       If x < y,
          Then transpose q = q ==> x = a /\ y = b      by transpose_fix
            so n = a * a + b * b = a ** 2 + b ** 2     by EXP_2
           ==> q IN (corners_less_fix n)               by corners_less_fix_def
       If y < x,
          Then transpose q = q ==> x = b /\ y = a      by transpose_fix
            so n = a * b + b * a = 2 * a * b           by arithmetic
           ==> q IN (corners_more_fix n)               by corners_more_fix_def
       If x = y,
          Then transpose q = q ==> T                   by transpose_fix
            so n = a * x + b * x = (a + b) * x         by RIGHT_ADD_DISTRIB
           ==> q IN (corners_eq_fix n)                 by corners_eq_fix_def
   (2) q IN (corners_less_fix n) ==> q IN corners n /\ transpose q = q
       Note q IN corners n                             by corners_less_fix_subset, SUBSET_DEF
        and q = (a,x,b,y) with x = a /\ y = b /\ a < b by corners_less_fix_def
         so transpose q = q                            by transpose_fix, x < y
   (3) q IN (corners_more_fix n) ==> q IN corners n /\ transpose q = q
       Note q IN corners n                             by corners_more_fix_subset, SUBSET_DEF
        and q = (a,x,b,y) with x = b /\ y = a /\ a < b by corners_more_fix_def
         so transpose q = q                            by transpose_fix, y < x
   (4) q IN (corners_eq_fix n) ==> q IN corners n /\ transpose q = q
       Note q IN corners n                             by corners_eq_fix_subset, SUBSET_DEF
        and q = (a,x,b,y) with x = y /\ a < b          by corners_eq_fix_def
         so transpose q = q                            by transpose_fix, x = y
*)
Theorem corners_transpose_fixes:
  !n. fixes transpose (corners n) =
        (corners_less_fix n) UNION (corners_more_fix n) UNION (corners_eq_fix n)
Proof
  rw[fixes_def, EXTENSION, EQ_IMP_THM] >| [
    rename1 `q IN _` >>
    fs[corners_def] >>
    `x < y \/ y < x \/ x = y` by simp[num_nchotomy] >| [
      rfs[transpose_fix, corners_less_fix_def] >>
      fs[],
      rfs[transpose_fix, corners_more_fix_def] >>
      fs[],
      rfs[transpose_fix, corners_eq_fix_def]
    ],
    metis_tac[corners_less_fix_subset, SUBSET_DEF],
    fs[corners_less_fix_def, transpose_fix],
    metis_tac[corners_more_fix_subset, SUBSET_DEF],
    fs[corners_more_fix_def, transpose_fix],
    metis_tac[corners_eq_fix_subset, SUBSET_DEF],
    fs[corners_eq_fix_def, transpose_fix]
  ]
QED

(* Theorem: fixes transpose (corners n) SUBSET corners n *)
(* Proof:
   Let s = fixes transpose (corners n),
       u = corners_less_fix n,
       v = corners_more_fix n,
       w = corners_eq_fix n.
   Note s = u UNION v UNION w      by corners_transpose_fixes
    and u SUBSET (corners n)       by corners_less_fix_subset
    and v SUBSET (corners n)       by corners_more_fix_subset
    and w SUBSET (corners n)       by corners_eq_fix_subset
    ==> s SUBSET (corners n)       by SUBSET_UNION
*)
Theorem corners_transpose_fixes_subset:
  !n. fixes transpose (corners n) SUBSET corners n
Proof
  rw[corners_transpose_fixes, corners_less_fix_subset, corners_more_fix_subset, corners_eq_fix_subset]
QED

(* Theorem: FINITE (fixes transpose (corners n)) *)
(* Proof:
   Let s = fixes transpose (corners n).
   Note s SUBSET corners n         by corners_transpose_fixes_subset
    and FINITE (corners n)         by corners_finite
     so FINITE s                   by SUBSET_FINITE
*)
Theorem corners_transpose_fixes_finite:
  !n. FINITE (fixes transpose (corners n))
Proof
  metis_tac[corners_transpose_fixes_subset, corners_finite, SUBSET_FINITE]
QED

(* Theorem: CARD (fixes transpose (corners n)) =
            CARD (corners_less_fix n) + CARD (corners_more_fix n) + CARD (corners_eq_fix n) *)
(* Proof:
   Let s = fixes transpose (corners n),
       u = corners_less_fix n,
       v = corners_more_fix n,
       w = corners_eq_fix n.
   Note s = u UNION v UNION w                  by corners_transpose_fixes
    and FINITE s                               by corners_transpose_fixes_finite
     so FINITE u /\ FINITE v /\ FINITE w       by FINITE_UNION
   Also DISJOINT u v as (a,a,b,b) <> (a,b,b,a) by DISJOINT_ALT, corners_less_fix_def, corners_more_fix_def
    and DISJOINT v w as (a,b,b,a) <> (a,c,b,c) by DISJOINT_ALT, corners_more_fix_def, corners_eq_fix_def
    and DISJOINT u w as (a,a,b,b) <> (a,c,b,c) by DISJOINT_ALT, corners_less_fix_def, corners_eq_fix_def
   ==> CARD s = CARD u + CARD v + CARD w       by CARD_UNION_3_DISJOINT
*)
Theorem corners_transpose_fixes_card:
  !n. CARD (fixes transpose (corners n)) =
        CARD (corners_less_fix n) + CARD (corners_more_fix n) + CARD (corners_eq_fix n)
Proof
  rpt strip_tac >>
  qabbrev_tac `s = fixes transpose (corners n)` >>
  qabbrev_tac `u = corners_less_fix n` >>
  qabbrev_tac `v = corners_more_fix n` >>
  qabbrev_tac `w = corners_eq_fix n` >>
  `s = u UNION v UNION w` by simp[corners_transpose_fixes, Abbr`s`, Abbr`u`, Abbr`v`, Abbr`w`] >>
  `FINITE s` by simp[corners_transpose_fixes_finite, Abbr`s`] >>
  `FINITE u /\ FINITE v /\ FINITE w` by rfs[] >>
  `DISJOINT u v` by
  (rw[DISJOINT_ALT, corners_less_fix_def, corners_more_fix_def, Abbr`u`, Abbr`v`] >>
  decide_tac) >>
  `DISJOINT v w` by
    (rw[DISJOINT_ALT, corners_more_fix_def, corners_eq_fix_def, Abbr`v`, Abbr`w`] >>
  decide_tac) >>
  `DISJOINT u w` by
      (rw[DISJOINT_ALT, corners_less_fix_def, corners_eq_fix_def, Abbr`u`, Abbr`w`] >>
  decide_tac) >>
  simp[CARD_UNION_3_DISJOINT]
QED

(* This is a good result. *)


(* ------------------------------------------------------------------------- *)
(* Fermat's Two Squares Theorem.                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: prime p ==> corners_eq_fix p = {(a,1,b,1) | p = a + b /\ 0 < a /\ a < b} *)
(* Proof:
   By corners_eq_fix_def, EXTENSION, this is to show:
      p = (a + b) * c ==> c = 1
   By contradiction, suppose c <> 1.
   Then c divides p                by divides_def
    ==> c = p                      by prime_def, x <> 1
   Note 0 < p                      by PRIME_POS
     so a + b = 1                  by MULT_EQ_SELF
   This contradicts 0 < a, 0 < b   by arithmetic
*)
Theorem prime_corners_eq_fix:
  !p. prime p ==> corners_eq_fix p = {(a,1,b,1) | p = a + b /\ 0 < a /\ a < b}
Proof
  rw[corners_eq_fix_def, EXTENSION, EQ_IMP_THM] >>
  qabbrev_tac `p = c * (a + b)` >>
  spose_not_then strip_assume_tac >>
  `c divides p` by fs[divides_def, Abbr`p`] >>
  `c = p` by metis_tac[prime_def] >>
  `0 < p` by simp[PRIME_POS] >>
  `a + b = 1` by fs[Abbr`p`] >>
  decide_tac
QED

(* Theorem: prime p ==>
            corners_eq_fix p = IMAGE (\a. (a,1,p - a, 1)) (natural (HALF (p - 1))) *)
(* Proof:
   Let s = {(a,1,b,1) | p = a + b /\ 0 < a /\ a < b},
       t = IMAGE (\a. (a,1,p - a, 1)) (natural (HALF (p - 1)))
   Note corners_eq p = s                       by prime_corners_eq_fix
   Thus only need to show: s = t
   By EXTENSION, this is to show:
   (1) (a,1,b,1) IN s ==> (a,1,b,1) IN t
       By IN_IMAGE, this is to show:
          p = a + b /\ 0 < a /\ a < b ==> ?x. a = SUC x /\ x < HALF (p - 1)
       Note ?k. a = SUC k                      by SUC_EXISTS, 0 < a
                  = k + 1                      by ADD1
        Now 0 < p                              by PRIME_POS
        and a + a < a + b = p                  by LT_ADD_LCANCEL
         or (k + 1) + (k + 1) < p              by above
         or   2 * k + 1 < p - 1                by arithmetic
        ==>           k < HALF (p - 1)         by HALF_ODD_LT
        Let x = k, then x < HALF (p - 1).
   (2) (a,1,b,1) IN t ==> (a,1,b,1) IN s
       By IN_IMAGE, this is to show:
          ?a. 0 < a /\ a <= HALF (p - 1) ==> p = a + (p - a) /\ a < p - a
       Note 1 < p                              by ONE_LT_PRIME
         so 0 < p - 1                          by inequality
        and ?q. p - 1 = SUC q                  by SUC_EXISTS, 0 < p - 1
        and ?k. a = SUC k                      by SUC_EXISTS, 0 < a
        Now     k < HALF (SUC q)               by SUC k <= HALF (p - 1)
        ==> 2 * k + 1 <= q                     by HALF_SUC_LE
         or 2 * k + 2 <= q + 1 = p - 1         by ADD1
         or      2 * a < p                     by a = SUC k
         or      a + a < p                     by arithmetic
         so a < p - a, and p = a + (p - a).
*)
Theorem prime_corners_eq_fix_eqn:
  !p. prime p ==> corners_eq_fix p = IMAGE (\a. (a,1,p - a, 1)) (natural (HALF (p - 1)))
Proof
  rpt strip_tac >>
  `{(a,1,b,1) | p = a + b /\ 0 < a /\ a < b} = IMAGE (\a. (a,1,p - a, 1)) (natural (HALF (p - 1)))` suffices_by simp[prime_corners_eq_fix] >>
  rw[EXTENSION, EQ_IMP_THM] >| [
    `?k. a = SUC k` by simp[SUC_EXISTS] >>
    `a + a < a + b` by fs[] >>
    qabbrev_tac `p = a + b` >>
    `0 < p` by fs[PRIME_POS] >>
    `2 * k + 1 < p - 1` by decide_tac >>
    metis_tac[HALF_ODD_LT],
    rename1 `k < _` >>
    `1 < p` by simp[ONE_LT_PRIME] >>
    `0 < p - 1` by decide_tac >>
    `?q. p - 1 = SUC q` by simp[SUC_EXISTS] >>
    `2 * k + 1 <= q` by fs[HALF_SUC_LE] >>
    `2 * SUC k < p` by decide_tac >>
    qabbrev_tac `a = SUC k` >>
    decide_tac
  ]
QED

(* Theorem: prime p ==> CARD (corners_eq_fix p) = HALF (p - 1) *)
(* Proof:
   Let s = natural (HALF (p - 1)),
       t = univ(:num # num # num # num),
       f = (\a. (a,1,p - a,1)).
    Note FINITE s                  by natural_finite
     and INJ f s t                 by INJ_DEF, equating components
         CARD (corners_eq p)
       = CARD (IMAGE f s)          by prime_corners_eq_fix_eqn
       = CARD s                    by INJ_CARD_IMAGE
       = HALF (p - 1)              by natural_card
*)
Theorem prime_corners_eq_fix_card:
  !p. prime p ==> CARD (corners_eq_fix p) = HALF (p - 1)
Proof
  rpt strip_tac >>
  imp_res_tac prime_corners_eq_fix_eqn >>
  qabbrev_tac `s = natural (HALF (p - 1))` >>
  qabbrev_tac `f = \a. (a,1,p - a,1)` >>
  `FINITE s` by simp[natural_finite, Abbr`s`] >>
  `INJ f s univ(:num # num # num # num)` by rw[INJ_DEF, Abbr`f`] >>
  metis_tac[INJ_CARD_IMAGE, natural_card]
QED

(* Theorem: prime p ==> fixes conjugate (corners p) =
            if p = 2 then {} else {(1, HALF (p - 1), HALF (p + 1),1)} *)
(* Proof:
   If p = 2,
      Then corners 2 = {}                      by corners_empty, 2 <= p
        so fixes conjugate {} = {}             by fixes_empty
   Otherwise p <> 2.
   Let s = {(a,b - a,b,a) | p = a * (2 * b - a) /\ 0 < a /\ a < b}.
   Then fixes conjugate (corners n) = s        by corners_conjugate_fixes
   The goal is to show:
       s = {(1, HALF (p - 1), HALF (p + 1),1)}
   By EXTENSION, this is to show:
   (1) p = a * (2 * b - a) /\ 0 < a /\ a < b ==>
       a = 1, b - 1 = HALF (p - 1), b = HALF (p + 1)
       Note 2 * b - a = b + (b - a)            by arithmetic
         so 2 * b - a <> 1                     by 0 < a, a < b
        But (2 * b - a) divides p              by divides_def
         so 2 * b - a = p                      by prime_def
        ==> a = 1                              by MULT_EQ_SELF
       Thus  2 * b = p + 1                     by arithmetic
        and  2 * (b - 1) = p - 1               by LEFT_SUB_DISTRIB
        ==> b = HALF (p + 1) /\                by HALF_TWICE
            b - 1 = HALF (p - 1)               by HALF_TWICE
   (2) a = 1 /\ b = HALF (p + 1) ==> p = a * (2 * b - a) /\ a < b
       This is to show:
            p = 2 * HALF (p + 1) - 1           by putting a = 1
        and 1 < HALF (p + 1)                   by putting b = HALF (p + 1)
       Note ~EVEN p                            by EVEN_PRIME, p <> 2
         so ODD p                              by ODD_EVEN
       thus ?k. p = 2 * k + 1                  by ODD_EXISTS
       and   HALF (p + 1)
           = HALF (2 * k + 2)                  by arithmetic
           = HALF (2 * (k + 1))                by LEFT_ADD_DISTRIB
           = k + 1                             by HALF_TWICE
        so   2 * HALF (p + 1) - 1
           = 2 * (k + 1) - 1                   by above
           = 2 * k + 1                         by LEFT_ADD_DISTRIB
           = p
      Also p <> 1                              by NOT_PRIME_1
        so k <> 0                              by p = 2 * k + 1
       ==> 1 < k + 1 = HALF (p + 1)            by inequality
*)
Theorem prime_corners_conjugate_fixes:
  !p. prime p ==> fixes conjugate (corners p) =
                    if p = 2 then {} else {(1, HALF (p - 1), HALF (p + 1),1)}
Proof
  rpt strip_tac >>
  Cases_on `p = 2` >-
  metis_tac[corners_empty, fixes_empty, LESS_EQ_REFL] >>
  qabbrev_tac `s = {(a,b - a,b,a) | p = a * (2 * b - a) /\ 0 < a /\ a < b}` >>
  `s = {(1,HALF (p - 1),HALF (p + 1),1)}` suffices_by simp[corners_conjugate_fixes, Abbr`s`] >>
  simp[Abbr`s`, EXTENSION, EQ_IMP_THM] >>
  ntac 3 strip_tac >| [
    simp[] >>
    `2 * b - a <> 1` by decide_tac >>
    `2 * b - a = p` by metis_tac[divides_def, prime_def] >>
    `a = 1` by fs[] >>
    `2 * b = p + 1` by decide_tac >>
    `2 * (b - 1) = p - 1` by decide_tac >>
    metis_tac[HALF_TWICE],
    `ODD p` by metis_tac[EVEN_PRIME, ODD_EVEN] >>
    `?k. p = 2 * k + 1` by metis_tac[ODD_EXISTS, ADD1] >>
    `p - 1 = 2 * k /\ p + 1 = 2 * (k + 1)` by decide_tac >>
    `k <> 0` by metis_tac[MULT_0, ADD, NOT_PRIME_1] >>
    simp[HALF_TWICE]
  ]
QED

(* Theorem: prime p ==> corners_more_fix p = {} *)
(* Proof:
   If EVEN p,
      Then p = 2                               by EVEN_PRIME
        so corners_more_fix p = {}             by corners_more_fix_eq_empty
   Otherwise ~EVEN p,
       Then ODD p                              by ODD_EVEN
         so corners_more_fix p = {}            by corners_more_fix_empty
*)
Theorem prime_corners_more_fix:
  !p. prime p ==> corners_more_fix p = {}
Proof
  rpt strip_tac >>
  `EVEN p \/ ODD p` by simp[EVEN_OR_ODD] >-
  metis_tac[corners_more_fix_eq_empty, EVEN_PRIME] >>
  simp[corners_more_fix_empty]
QED

(* Theorem: tik p /\ prime p ==> corners_less_fix p <> {} *)
(* Proof:
   Let s = fixes conjugate (corners p),
       t = fixes transpose (corners p),
       u = corners_less_fix p,
       v = corners_more_fix p,
       w = corners_eq_fix p.
   By contradiction, assume u = {}.

   Claim: ODD (CARD t)
   Proof: Note ODD p                           by odd_tik_tok
            so p <> 2                          by EVEN_2, ODD_EVEN
           ==> CARD s = 1                      by prime_corners_conjugate_fixes, CARD_SING
            or ODD (CARD s)                    by ODD_1
           Now FINITE (corners p)              by corners_finite
           and conjugate involute (corners p)  by conjugate_involute_corners
           and transpose involute (corners p)  by transpose_involute_corners
           ==> ODD (CARD t)                    by involute_two_fixes_both_odd, [1]

   Claim: EVEN (CARD w)
   Proof: Note ?k. p = 4 * k + 1               by tik_exists
           and CARD w = HALF (p - 1)           by prime_corners_eq_fix_card, prime p
                      = HALF (4 * k)           by above
                      = HALF (2 * (2 * k))     by arithmetic
                      = 2 * k                  by HALF_TWICE
          ==> EVEN (CARD w)                    by EVEN_DOUBLE, [2]

   Note CARD u = 0                             by assumption, u = {}, CARD_EMPTY
    and CARD v = 0                             by prime_corners_more_fix, CARD_EMPTY
    Now CARD t = CARD u + CARD v + CARD w      by corners_transpose_fixes_card
               = CARD w                        by above
    But ODD (CARD t) /\ EVEN (CARD w)          by [1], [2]
   This is a contradiction                     by ODD_EVEN
*)
Theorem tik_prime_corners_less_fix:
  !p. tik p /\ prime p ==> corners_less_fix p <> {}
Proof
  rpt strip_tac >>
  qabbrev_tac `s = fixes conjugate (corners p)` >>
  qabbrev_tac `t = fixes transpose (corners p)` >>
  qabbrev_tac `u = corners_less_fix p` >>
  qabbrev_tac `v = corners_more_fix p` >>
  qabbrev_tac `w = corners_eq_fix p` >>
  `ODD (CARD t)` by
  (`p <> 2` by metis_tac[odd_tik_tok, EVEN_2, ODD_EVEN] >>
  `CARD s = 1` by fs[prime_corners_conjugate_fixes, Abbr`s`] >>
  `ODD (CARD s)` by simp[ODD_1] >>
  `FINITE (corners p)` by simp[corners_finite] >>
  `conjugate involute (corners p)` by metis_tac[conjugate_involute_corners] >>
  `transpose involute (corners p)` by metis_tac[transpose_involute_corners] >>
  metis_tac[involute_two_fixes_both_odd]) >>
  `EVEN (CARD w)` by
    (`?k. p = 4 * k + 1` by simp[tik_exists] >>
  `p - 1 = 2 * (2 * k)` by decide_tac >>
  `HALF (p - 1) = 2 * k` by metis_tac[HALF_TWICE] >>
  fs[prime_corners_eq_fix_card, EVEN_DOUBLE, Abbr`w`]) >>
  `CARD u = 0` by fs[] >>
  `CARD v = 0` by simp[prime_corners_more_fix, Abbr`v`] >>
  metis_tac[corners_transpose_fixes_card, ADD, ODD_EVEN]
QED

(* Theorem: tik p /\ prime p ==> ?a b. p = a ** 2 + b ** 2 /\ a < b *)
(* Proof:
   Let s = corners_less_fix p.
   Note s <> {}                                by tik_prime_corners_less_fix
    ==> ?q. q IN s                             by MEMBER_NOT_EMPTY
    ==> ?a b. q = (a,a,b,b) /\
              p = a ** 2 + b ** 2 /\ a < b     by corners_less_fix_def
   Take these values of a and b.
*)
Theorem fermat_two_squares_by_corners:
  !p. tik p /\ prime p ==> ?a b. p = a ** 2 + b ** 2 /\ a < b
Proof
  rpt strip_tac >>
  imp_res_tac tik_prime_corners_less_fix >>
  fs[corners_less_fix_def, EXTENSION] >>
  map_every qexists_tac [`a`,`b`] >>
  simp[]
QED

(* A fine adaptation of the partition proof by David Christopher. *)

(* ------------------------------------------------------------------------- *)
(* References                                                                *)
(* ------------------------------------------------------------------------- *)

(*

A partition-theoretic proof of Fermat’s Two Squares Theorem
A. David Christopher (31 December 2015)
https://www.sciencedirect.com/science/article/pii/S0012365X15004355
Antony David Christopher - Assistant Professor
https://americancollege.edu.in/wp-content/uploads/2015/06/A.David-Christopher.pdf
10. “A partition-theoretic proof of Fermat’ s Two Squares Theorem”, Discrete Mathematics, 339 (2016) 1410–1411.

Formal verification of Zagier’s one-sentence proof
Guillaume Dubach & Fabian Mühlböck (21 March 2021)
https://arxiv.org/abs/2103.11389

An Algorithm to List All the Fixed-Point Free Involutions on a Finite Set
Cyril Prissette (20 June 2010)
https://hal.archives-ouvertes.fr/hal-00493605/document

The One-Sentence Proof in Multiple Sentences
Marcel Moosbrugger (3 February 2020)
https://medium.com/cantors-paradise/the-one-sentence-proof-in-multiple-sentences-ab2657efc576

*)


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
