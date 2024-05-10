(* ------------------------------------------------------------------------- *)
(* Quarity - Number Types under Modulo 4.                                    *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

open arithmeticTheory pred_setTheory pairTheory listTheory rich_listTheory
     listRangeTheory dividesTheory gcdTheory logrootTheory numberTheory
     combinatoricsTheory primeTheory;

open helperTwosqTheory windmillTheory;

(* declare new theory at start *)
val _ = new_theory "quarity";

(* ------------------------------------------------------------------------- *)

val _ = temp_overload_on("SQ", ``\n. n * (n :num)``);
val _ = temp_overload_on("HALF", ``\n. n DIV 2``);
val _ = temp_overload_on("TWICE", ``\n. 2 * n``);

(* ------------------------------------------------------------------------- *)
(* Quarity Documentation                                                     *)
(* ------------------------------------------------------------------------- *)
(* Overloads:
   tik n          = n MOD 4 = 1
   tok n          = n MOD 4 = 3
   zig n          = n MOD 4 = 0
   zag n          = n MOD 4 = 2
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   Quarity of a number: tik, tok, zig, zag:
   parity_cases            |- !n. EVEN n \/ ODD n
   quarity_cases           |- !n. zig n \/ zag n \/ tik n \/ tok n
   zig_exists              |- !n. zig n ==> ?k. n = 4 * k
   zag_exists              |- !n. zag n ==> ?k. n = 4 * k + 2
   tik_exists              |- !n. tik n ==> ?k. n = 4 * k + 1
   tok_exists              |- !n. tok n ==> ?k. n = 4 * k + 3
   square_mod_4            |- !n. zig (n ** 2) \/ tik (n ** 2)
   tok_not_square          |- !n. tok n ==> ~square n
   zag_not_square          |- !n. zag n ==> ~square n
   tik_non_square          |- !n. tik n /\ ~square n ==> n = 5 \/ 12 < n
   odd_tik_tok             |- !n. ODD n <=> tik n \/ tok n
   even_zig_zag            |- !n. EVEN n <=> zig n \/ zag n
   odd_eq_two_sq_sum       |- !m n. ODD (m ** 2 + n ** 2) <=> (ODD m <=> EVEN n)
   even_eq_two_sq_sum      |- !m n. EVEN (m ** 2 + n ** 2) <=> (EVEN m <=> EVEN n)
   sum_of_squares_mod_4    |- !n m. zig (n ** 2 + m ** 2) \/
                                    tik (n ** 2 + m ** 2) \/
                                    zag (n ** 2 + m ** 2)
   tok_not_sum_of_squares  |- !n. tok n ==> !x y. n <> x ** 2 + y ** 2
   tik_div_4               |- !n. tik n ==> (n - 1) DIV 4 = n DIV 4
   tik_sub_odd_sq_mod_4    |- !n m. tik n /\ ODD m ==> (n - m ** 2) MOD 4 = 0
   tik_sub_odd_sq_div_4    |- !n m. tik n /\ ~square n /\ ODD m /\ m <= SQRT n ==> 0 < (n - m ** 2) DIV 4
   zig_sub_even_sq_mod_4   |- !n m. zig n /\ EVEN m ==> zig (n - m ** 2)
   zig_sub_even_sq_div_4   |- !n m.  zig n /\ ~square n /\ EVEN m /\ m <= SQRT n ==>  0 < (n - m ** 2) DIV 4
   mills_tok_empty         |- !n. tok n ==> mills n = {}
   mills_zag_empty         |- !n. zag n ==> mills n = {}
   mills_tik_nonempty      |- !n. tik n ==> mills n <> {}
   windmill_mind_odd       |- !n x y z. tik n /\ n = windmill (x, y, z) ==> ODD x /\ x <= SQRT n
   windmill_mind_even      |- !n x y z. zig n /\ n = windmill (x, y, z) ==> EVEN x /\ x <= SQRT n

   Computation of (mills n):
   odds_to_def             |- !n. odds_to n = {x | ODD x /\ x <= n}
   odds_to_element         |- !n x. x IN odds_to n <=> ODD x /\ x <= n
   odds_to_eqn             |- !n. odds_to n = IMAGE (\j. if ODD j then j else 1) (natural n)
!  odds_to_thm             |- !n. odds_to n = IMAGE (\j. 2 * j + 1) (count (HALF (n + 1)))
   odds_to_subset_count    |- !n. odds_to n SUBSET count (n + 1)
   odds_to_finite          |- !n. FINITE (odds_to n)
   odds_to_card            |- !n. CARD (odds_to n) = HALF (n + 1)

   evens_to_def            |- !n. evens_to n = {x | EVEN x /\ x <= n}
   evens_to_element        |- !n x. x IN evens_to n <=> EVEN x /\ x <= n
   evens_to_eqn            |- !n. evens_to n = IMAGE (\j. if EVEN j then j else 0) (count (n + 1))
!  evens_to_thm            |- !n. evens_to n = IMAGE (\j. 2 * j) (count (HALF (n + 2)))
   evens_to_subset_count   |- !n. evens_to n SUBSET count (n + 1)
   evens_to_finite         |- !n. FINITE (evens_to n)
   evens_to_card           |- !n. CARD (evens_to n) = HALF (n + 2)

   factor_pair_def         |- !n. factor_pair n = if n = 0 then {} else IMAGE (\j. (j, n DIV j)) (divisors n)
   factor_pair_0           |- factor_pair 0 = {}
   factor_pair_empty       |- !n. factor_pair n = {} <=> n = 0
   factor_pair_nonzero_element
                           |- !n p q. 0 < n ==> ((p,q) IN factor_pair n <=> n = p * q)

   Windmills for tiks:
   mills_tik_def           |- !n. mills_tik n =
                                  BIGUNION
                                     (IMAGE (\x. IMAGE (\p. (x,p)) (factor_pair ((n - x * x) DIV 4)))
                                            (odds_to (SQRT n)))
   mills_tik_eqn           |- !n. tik n /\ ~square n ==> mills n = mills_tik n
!  mills_odd_eqn           |- !n. mills n = if tok n then {}
                                            else if tik n /\ ~square n then mills_tik n
                                            else mills n
   mills_tok_card          |- !n. tok n ==> CARD (mills n) = 0
   mills_tik_card          |- !n. tik n /\ ~square n ==>
                                  CARD (mills n) = SIGMA (\x. CARD (divisors ((n - x ** 2) DIV 4))) (odds_to (SQRT n))
   mills_tik_card_upper_thm    |- !n. tik n /\ ~square n ==>
                                      CARD (mills n) <= SIGMA (\x. 2 * SQRT ((n - x ** 2) DIV 4)) (odds_to (SQRT n))
   mills_tik_card_upper_tight  |- !n. tik n /\ ~square n ==>
                                      CARD (mills n) <= 2 * SQRT (n DIV 4) * HALF (1 + SQRT n)
   mills_tik_card_upper        |- !n. tik n /\ ~square n ==> CARD (mills n) <= n

   Windmills for zigs:
   mills_zig_def           |- !n. mills_zig n =
                                  BIGUNION
                                     (IMAGE (\x. IMAGE (\p. (x,p)) (factor_pair ((n - x * x) DIV 4)))
                                            (evens_to (SQRT n)))
   mills_zig_eqn           |- !n. zig n /\ ~square n ==> mills n = mills_zig n
!  mills_even_eqn          |- !n. mills n = if zig n /\ ~square n then mills_zig n
                                            else if zag n then {}
                                            else mills n
   mills_zag_card          |- !n. zag n ==> CARD (mills n) = 0
   mills_zig_card          |- !n. zig n /\ ~square n ==>
                                  CARD (mills n) = SIGMA (\x. CARD (divisors ((n - x ** 2) DIV 4))) (evens_to (SQRT n))
   mills_zig_card_upper_thm    |- !n. zig n /\ ~square n ==>
                                      CARD (mills n) <= SIGMA (\x. 2 * SQRT ((n - x ** 2) DIV 4)) (evens_to (SQRT n))
   mills_zig_card_upper_tight  |- !n. zig n /\ ~square n ==>
                                      CARD (mills n) <= 2 * SQRT (n DIV 4) * HALF (2 + SQRT n)
   mills_zig_card_upper        |- !n. zig n /\ ~square n ==> CARD (mills n) <= n

   Windmills for squares:
   mills_square_def            |- !n. mills_square n = {(x,y,z) | n = windmill (x, y, z) /\ y * z = 0}
   mills_square_element        |- !n x y z. (x,y,z) IN mills_square n <=> n = windmill (x, y, z) /\ (y = 0 \/ z = 0)
   mills_tik_square_eqn        |- !n. tik n /\ square n ==> mills n = mills_tik n UNION mills_square n
   mills_zig_square_eqn        |- !n. zig n /\ square n ==> mills n = mills_zig n UNION mills_square n

   Computation of (mills n) in general:
!  mills_eqn               |- !n. mills n = if square n then mills n
                                       else if zig n then mills_zig n
                                       else if tik n then mills_tik n else {}
   mills_card_upper        |- !n. ~square n ==> CARD (mills n) <= n

   Search for Sum of Squares:
   two_sq_sum_def          |- !n. two_sq_sum n = {(x,y) | n = x ** 2 + y ** 2}
   two_sq_sum_element      |- !n x y. (x,y) IN two_sq_sum n <=> n = x ** 2 + y ** 2
   two_sq_sum_subset       |- !n. two_sq_sum n SUBSET count (1 + SQRT n) CROSS count (1 + SQRT n)
   two_sq_sum_finite       |- !n. FINITE (two_sq_sum n)
!  two_sq_sum_eqn          |- !n. two_sq_sum n = BIGUNION (IMAGE
                                    (\x. (let m = n - x * x;
                                              y = SQRT m
                                           in if y * y = m then {(x,y)} else {}))
                                    (upto (SQRT n)))
   two_sq_sum_tok          |- !n. tok n ==> two_sq_sum n = {}

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Helpers: to move to somewhere else *)

(* ------------------------------------------------------------------------- *)
(* Quarity of a number: tik, tok, zig, zag.                                  *)
(* ------------------------------------------------------------------------- *)

(* Overload the four types under modulo 4. *)
Overload "tik" = ``\n. n MOD 4 = 1``;
Overload "tok" = ``\n. n MOD 4 = 3``;
Overload "zig" = ``\n. n MOD 4 = 0``;
Overload "zag" = ``\n. n MOD 4 = 2``;

(* Some thoughts.

Under MOD 4, there are 4 types of numbers:

The odds:
Those with n MOD 4 = 1, the tiks. They have windmills, first square is 1, next square is 9.
                                  Nonsquares have finite (mills n), by odds_to (SQRT n).
Those with n MOD 4 = 3, the toks. They have no windmils, as ODD x, and (x ** 2) MOD 4 = 1, not 3.
                                  Same reason shows ODD n cannot be sums of two squares.
The evens:
Those with n MOD 4 = 0, the zigs. They have windmills, with EVEM (can be 0) minds, first square 0, next square 4.
                                  Nonsquares have finite (mills n), by evens_to (SQRT n).
Those with n MOD 4 = 2, the zags. They hae no windmills, as EVEN x, and (x ** 2) MDO 4 = 0, ot 2.
                                  However, EVEN n can be a sum of two odd squares, not from windmill: 10 = 1 + 9.

Is it worth to define (evens_to m), and study (mills n) for zig n? Yes! Have a picture of (mills n) for all n.
See evens_to_def.

*)

(* Theorem alias *)
Theorem parity_cases = arithmeticTheory.EVEN_OR_ODD;
(* val parity_cases = |- !n. EVEN n \/ ODD n: thm *)

(* Theorem: zig n \/ zag n \/ tik n \/ tok n *)
(* Proof:
   By contradiction, suppose n MOD 4 is not 0, 1, 2, 3.
   Then n MOD 4 >= 4, or ~(n MOD 4 < 4)        by arithmetic
   This contradicts n MOD 4 < 4                by MOD_LESS
*)
Theorem quarity_cases:
  !n. zig n \/ zag n \/ tik n \/ tok n
Proof
  spose_not_then strip_assume_tac >>
  `~(n MOD 4 < 4)` by decide_tac >>
  fs[MOD_LESS]
QED

(* Theorem: zig n ==> ?k. n = 4 * k *)
(* Proof:
   Let k = n DIV 4.
   Then n = k * 4 + (n MOD 4)      by DIVISION
          = 4 * k + 0              by MULT_COMM
          = 4 * k                  by ADD_0
*)
Theorem zig_exists:
  !n. zig n ==> ?k. n = 4 * k
Proof
  metis_tac[DIVISION, MULT_COMM, ADD_0, DECIDE``0 < 4``]
QED

(* Theorem: zag n ==> ?k. n = 4 * k + 2 *)
(* Proof:
   Let k = n DIV 4.
   Then n = k * 4 + (n MOD 4)      by DIVISION
          = 4 * k + 2              by MULT_COMM
*)
Theorem zag_exists:
  !n. zag n ==> ?k. n = 4 * k + 2
Proof
  metis_tac[DIVISION, MULT_COMM, DECIDE``0 < 4``]
QED

(* Theorem: tik n ==> ?k. n = 4 * k + 1 *)
(* Proof:
   Let k = n DIV 4.
   Then n = k * 4 + (n MOD 4)      by DIVISION
          = 4 * k + 1              by MULT_COMM
*)
Theorem tik_exists:
  !n. tik n ==> ?k. n = 4 * k + 1
Proof
  metis_tac[DIVISION, MULT_COMM, DECIDE``0 < 4``]
QED

(* Theorem: tok n ==> ?k. n = 4 * k + 3 *)
(* Proof:
   Let k = n DIV 4.
   Then n = k * 4 + (n MOD 4)      by DIVISION
          = 4 * k + 3              by MULT_COMM
*)
Theorem tok_exists:
  !n. tok n ==> ?k. n = 4 * k + 3
Proof
  metis_tac[DIVISION, MULT_COMM, DECIDE``0 < 4``]
QED

(* Idea: the possible MOD 4 values of a square. *)

(* Theorem: zig (n ** 2) \/ tik (n ** 2) *)
(* Proof:
   Note n ** 2 MOD 4 IN {0; 1}     by mod_4_square
   Hence true.
 *)
Theorem square_mod_4:
  !n. zig (n ** 2) \/ tik (n ** 2)
Proof
  assume_tac mod_4_square >>
  fs[]
QED

(* Idea: therefore, tok and zag cannot be squares. *)

(* Theorem: tok n ==> ~square n *)
(* Proof:
   By contradiction, assume square n.
   Then ?k. n = k ** 2                   by square_alt
    and n MOD 4 = 3 is a contradiction   by square_mod_4
*)
Theorem tok_not_square:
  !n. tok n ==> ~square n
Proof
  metis_tac[square_alt, square_mod_4, DECIDE``3 <> 0 /\ 3 <> 1``]
QED

(* Theorem: zag n ==> ~square n *)
(* Proof:
   By contradiction, assume square n.
   Then ?k. n = k ** 2                   by square_alt
    and n MOD 4 = 2 is a contradiction   by square_mod_4
*)
Theorem zag_not_square:
  !n. zag n ==> ~square n
Proof
  metis_tac[square_alt, square_mod_4, DECIDE``2 <> 0 /\ 2 <> 1``]
QED

(*
> EVAL ``MAP (\n. (n, tik n, ~square n)) [0 .. 20]``;
  = [(0,F,F); (1,T,F); (2,F,T); (3,F,T); (4,F,F); (5,T,T); (6,F,T); (7,F,T);
     (8,F,T); (9,T,F); (10,F,T); (11,F,T); (12,F,T); (13,T,T); (14,F,T); (15,F,T);
     (16,F,F); (17,T,T); (18,F,T); (19,F,T); (20,F,T)]: thm
Examples of tik and squares:
> EVAL ``FILTER (\j. tik j /\ square j) [0 .. 30]``;  = [1; 9; 25]
Examples of tiks and non-squares:
> EVAL ``FILTER (\j. tik j /\ ~square j) [0 .. 30]``; = [5; 13; 17; 21; 29]
For the proof below:
> EVAL ``FILTER (\j. tik j /\ ~square j /\ j <> 5) [0 .. 12]``; = []
*)

(* Idea: if n is a tik and not a square, either n = 5, or 13 <= n. *)

(* Theorem: tik n /\ ~square n ==> n = 5 \/ 12 < n *)
(* Proof:
   By contradiction, suppose n <> 5 /\ n <= 12.
   Let ls = FILTER (\j. tik j /\ ~square j /\ j <> 5) [0 .. 12].
   Then MEM n [0 .. 12]            by listRangeINC_MEM
     so MEM n ls                   by MEM_FILTER
     or ls <> []                   by NIL_NO_MEM
   This contradicts ls = []        by EVAL
*)
Theorem tik_non_square:
  !n. tik n /\ ~square n ==> n = 5 \/ 12 < n
Proof
  spose_not_then strip_assume_tac >>
  `n <= 12` by decide_tac >>
  `FILTER (\j. tik j /\ ~square j /\ j <> 5) [0 .. 12] = []` by EVAL_TAC >>
  qabbrev_tac `ls = FILTER (\j. tik j /\ ~square j /\ j <> 5) [0 .. 12]` >>
  `MEM n ls` by fs[MEM_FILTER, Abbr`ls`] >>
  rfs[NIL_NO_MEM]
QED

(* Theorem: ODD n <=> (tik n \/ tok n) *)
(* Proof:
   If part: ODD n ==> (tik n \/ tok n)
      Note ?k. n = 2 * k + 1                   by ODD_EXISTS, ADD1
      If EVEN k,
         then ?h. k = 2 * h                    by EVEN_EXISTS
           so     n = 2 * (2 * h) + 1          by above
                    = 4 * h + 1                by arithmetic
         thus tik n                            by n MOD 4 = 1
      Otherwise, ~EVEN k means ODD k           by ODD_EVEN
         then ?h. k = 2 * h + 1                by ODD_EXISTS
           so     n = 2 * (2 * h + 1) + 1      by above
                     = 4 * h + 3               by arithmetic
         thus tok n                            by n MOD 4 = 3

   Only-if part: (tik n \/ tok n) ==> ODD n
      If tik n, then ?k. n = 4 * k + 1         by tik_exists
                  or n = SUC (2 * (2 * k))     by arithmetic, ADD1
                  so ODD n                     by ODD_EXISTS
      If tok n, then ?k. n = 4 * k + 3         by tok_exists
                  or n = SUC (2 * (2 * k + 1)) by arithmetic, ADD1
                  so ODD n                     by ODD_EXISTS
*)
Theorem odd_tik_tok:
  !n. ODD n <=> (tik n \/ tok n)
Proof
  rw[EQ_IMP_THM] >| [
    `?k. n = 2 * k + 1` by metis_tac[ODD_EXISTS, ADD1] >>
    Cases_on `EVEN k` >| [
      `?h. k = 2 * h` by metis_tac[EVEN_EXISTS] >>
      simp[],
      `?h. k = 2 * h + 1` by metis_tac[ODD_EXISTS, ADD1, ODD_EVEN] >>
      `n = 4 * h + 3` by fs[] >>
      simp[]
    ],
    `?k. n = 4 * k + 1` by simp[tik_exists] >>
    `_ = SUC (2 * (2 * k))` by simp[ADD1] >>
    metis_tac[ODD_EXISTS],
    `?k. n = 4 * k + 3` by simp[tok_exists] >>
    `_ = SUC (2 * (2 * k + 1))` by simp[ADD1] >>
    metis_tac[ODD_EXISTS]
  ]
QED

(* Theorem: EVEN n <=> (zig n \/ zag n) *)
(* Proof:
   If part: EVEN n ==> (zig n \/ zag n)
      Note ?k. n = 2 * k                       by EVEN_EXISTS
      If EVEN k,
         then ?h. k = 2 * h                    by EVEN_EXISTS
           so     n = 2 * (2 * h)              by above
                    = 4 * h                    by arithmetic
         thus zig n                            by n MOD 4 = 0
      Otherwise, ~EVEN k means ODD k           by ODD_EVEN
         then ?h. k = 2 * h + 1                by ODD_EXISTS
           so     n = 2 * (2 * h + 1)          by above
                     = 4 * h + 2               by arithmetic
         thus zag n                            by n MOD 4 = 2

   Only-if part: (zig n \/ zag n) ==> EVEN n
      If zig n, then ?k. n = 4 * k             by zig_exists
                  or n = (2 * (2 * k))         by arithmetic
                  so EVEN n                    by EVEN_EXISTS
      If zag n, then ?k. n = 4 * k + 2         by zag_exists
                  or n = 2 * (2 * k + 1)       by arithmetic
                  so EVEN n                    by EVEN_EXISTS
*)
Theorem even_zig_zag:
  !n. EVEN n <=> (zig n \/ zag n)
Proof
  rw[EQ_IMP_THM] >| [
    `?k. n = 2 * k` by metis_tac[EVEN_EXISTS] >>
    Cases_on `EVEN k` >| [
      `?h. k = 2 * h` by metis_tac[EVEN_EXISTS] >>
      simp[],
      `?h. k = 2 * h + 1` by metis_tac[ODD_EXISTS, ADD1, ODD_EVEN] >>
      `n = 4 * h + 2` by fs[] >>
      simp[]
    ],
    `?k. n = 4 * k` by simp[zig_exists] >>
    `_ = 2 * (2 * k)` by simp[] >>
    metis_tac[EVEN_EXISTS],
    `?k. n = 4 * k + 2`  by simp[zag_exists] >>
    `_ = 2 * (2 * k + 1)` by simp[] >>
    metis_tac[EVEN_EXISTS]
  ]
QED

(* Theorem: ODD (x ** 2 + y ** 2) <=> (ODD x <=> EVEN y) *)
(* Proof:
       ODD (m ** 2 + n ** 2)
   <=> ODD (m ** 2) <=> EVEN (n ** 2)         by ODD_ADD, ODD_EVEN
   <=> ODD m <=> EVEN n                       by ODD_SQ, EVEN_DQ
*)
Theorem odd_eq_two_sq_sum:
  !m n. ODD (m ** 2 + n ** 2) <=> (ODD m <=> EVEN n)
Proof
  metis_tac[ODD_SQ, EVEN_SQ, ODD_ADD, ODD_EVEN]
QED

(* Theorem: EVEN (m ** 2 + n ** 2) <=> (EVEN m <=> EVEN n) *)
(* Proof:
       EVEN (m ** 2 + n ** 2)
   <=> EVEN (m ** 2) <=> EVEN (n ** 2)         by EVEN_ADD
   <=> EVEN m <=> EVEN n                       by EVEN_DQ
*)
Theorem even_eq_two_sq_sum:
  !m n. EVEN (m ** 2 + n ** 2) <=> (EVEN m <=> EVEN n)
Proof
  metis_tac[EVEN_SQ, EVEN_ADD]
QED

(* Idea: the possible MOD 4 values of a sum of squares. *)

(* Theorem: zig (n ** 2 + m ** 2) \/ tik (n ** 2 + m ** 2) \/ zag (n ** 2 + m ** 2) *)
(* Proof:
   Note n ** 2 MOD 4 IN {0; 1}     by mod_4_square
    and m ** 2 MOD 4 IN {0; 1}     by mod_4_square
   Hence possible sum of squares in MOD 4 are:
        0 + 0 = 0,
        0 + 1 = 1,
        1 + 0 = 1,
        1 + 1 = 2.
 *)
Theorem sum_of_squares_mod_4:
  !n m. zig (n ** 2 + m ** 2) \/ tik (n ** 2 + m ** 2) \/ zag (n ** 2 + m ** 2)
Proof
  rpt strip_tac >>
  assume_tac mod_4_square >>
  `0 < 4 /\ 1 < 4 /\ 0 + 0 = 0 /\ 0 + 1 = 1 /\ 1 + 0 = 1 /\ 1 + 1 = 2` by decide_tac >>
  `(zig (n ** 2) \/ tik (n ** 2)) /\ (zig (m ** 2) \/ tik (m ** 2))` by fs[] >-
  metis_tac[MOD_PLUS, ZERO_MOD] >-
  metis_tac[MOD_PLUS, ZERO_MOD, ONE_MOD] >-
  metis_tac[MOD_PLUS, ONE_MOD, ZERO_MOD] >>
  `2 MOD 4 = 2` by simp[] >>
  metis_tac[MOD_PLUS, ONE_MOD]
QED

(* Theorem: tok n ==> !x y. n <> x ** 2 + y ** 2 *)
(* Proof:
   By contradiction,
   suppose n = x ** 2 + y ** 2.
   Then tok n contradicts sum_of_squares_mod_4.
*)
Theorem tok_not_sum_of_squares:
  !n. tok n ==> !x y. n <> x ** 2 + y ** 2
Proof
  spose_not_then strip_assume_tac >>
  metis_tac[sum_of_squares_mod_4, DECIDE``3 <> 0 /\ 3 <> 1 /\ 3 <> 2``]
QED
(* This is the same as: helperTwosqTheory.mod_4_not_squares *)

(* Theorem: tik n ==> (n - 1) DIV 4 = n DIV 4 *)
(* Proof:
   Let k = n DIV 4.
   Then n = 4 * k + 1              by DIVISION, tik n.
     so k = (n - 1) DIV 4          by arithmetic
*)
Theorem tik_div_4:
  !n. tik n ==> (n - 1) DIV 4 = n DIV 4
Proof
  rpt strip_tac >>
  qabbrev_tac `k = n DIV 4` >>
  `n = 4 * k + 1` by metis_tac[DIVISION, MULT_COMM, DECIDE``0 < 4``] >>
  simp[]
QED

(* Idea: If n = 4k + 1, and x is odd, then (n - x ** 2) is a multiple of 4. *)

(* Theorem: tik n /\ ODD m ==> (n - m ** 2) MOD 4 = 0 *)
(* Proof:
   Note ?k. m = 2 * k + 1          by ODD_EXISTS, ADD1
   so   m ** 2
      = m * m                      by EXP_2
      = (2 * k + 1) * (2 * k + 1)  by above
      = 4 * k * k + 4 * k + 1      by arithmetic
      = 4 * (k * k + k) + 1        by arithmetic
   Thus (m ** 2) MOD 4 = 1         by MOD_PLUS
   Hence (n - m ** 2) MOD 4 = 0    by MOD_EQ_DIFF
*)
Theorem tik_sub_odd_sq_mod_4:
  !n m. tik n /\ ODD m ==> (n - m ** 2) MOD 4 = 0
Proof
  rpt strip_tac >>
  `?k. m = 2 * k + 1` by metis_tac[ODD_EXISTS, ADD1] >>
  `m ** 2 = m * m` by simp[] >>
  `_ = (2 * k + 1) * (2 * k + 1)` by fs[] >>
  `_ = 4 * (k * k + k) + 1` by decide_tac >>
  `(m ** 2) MOD 4 = 1` by simp[] >>
  simp[MOD_EQ_DIFF]
QED
(* move to: helperTwosqTheory. *)

(* Theorem: tik n /\ ~square n /\ ODD m /\ m <= SQRT n ==> 0 < (n - m ** 2) DIV 4 *)
(* Proof:
   Let k = n - m ** 2.
   This is to show: 0 < k DIV 4.
   By contradiction, assume k DIV 4 = 0.
   Note k MOD 4 = 0                by tik_sub_odd_sq_mod_4
     k
   = (k DIV 4) * 4 + (k MOD 4)     by DIVISION
   = 0 * 4 + 0 = 0                 by arithmetic
   Now m ** 2 <= (SQRT n) ** 2     by EXP_EXP_LE_MONO_IMP, m <= SQRT n
   and (SQRT n) ** 2 <= n          by SQRT_PROPERTY
    so m ** 2 <= n                 by ineqaulities
   Thus k = 0 means m ** 2 = n,
   giving square n                 by square_eqn
   This contradicts ~square n.
*)
Theorem tik_sub_odd_sq_div_4:
  !n m. tik n /\ ~square n /\ ODD m /\ m <= SQRT n ==> 0 < (n - m ** 2) DIV 4
Proof
  spose_not_then strip_assume_tac >>
  qabbrev_tac `k = n - m ** 2` >>
  `k DIV 4 = 0` by decide_tac >>
  `k MOD 4 = 0` by rw[tik_sub_odd_sq_mod_4, Abbr`k`] >>
  `k = 0` by metis_tac[DIVISION, MULT, ADD_0, DECIDE``0 < 4``] >>
  `m ** 2 <= (SQRT n) ** 2` by simp[] >>
  `(SQRT n) ** 2 <= n` by rw[SQRT_PROPERTY] >>
  qunabbrev_tac `k` >>
  `n = m ** 2` by decide_tac >>
  fs[square_eqn]
QED
(* move to: helperTwosqTheory. *)

(* Theorem: zig n /\ EVEN m ==> (n - m ** 2) MOD 4 = 0 *)
(* Proof:
   Note ?k. m = 2 * k              by EVEN_EXISTS
   so   m ** 2
      = m * m                      by EXP_2
      = (2 * k) * (2 * k)          by above
      = 4 * k * k                  by arithmetic
   Thus (m ** 2) MOD 4 = 0         by MOD_PLUS
   Hence (n - m ** 2) MOD 4 = 0    by MOD_EQ_DIFF
*)
Theorem zig_sub_even_sq_mod_4:
  !n m. zig n /\ EVEN m ==> (n - m ** 2) MOD 4 = 0
Proof
  rpt strip_tac >>
  `?k. m = 2 * k` by metis_tac[EVEN_EXISTS] >>
  `m ** 2 = m * m` by simp[] >>
  `_ = 4 * k * k` by rw[] >>
  `(m ** 2) MOD 4 = 0` by simp[] >>
  simp[MOD_EQ_DIFF]
QED
(* move to: helperTwosqTheory. *)

(* Theorem: zig n /\ ~square n /\ EVEN m /\ m <= SQRT n ==> 0 < (n - m ** 2) DIV 4 *)
(* Proof:
   Let k = n - m ** 2.
   This is to show: 0 < k DIV 4.
   By contradiction, assume k DIV 4 = 0.
   Note k MOD 4 = 0                by zig_sub_even_sq_mod_4
     k
   = (k DIV 4) * 4 + (k MOD 4)     by DIVISION
   = 0 * 4 + 0 = 0                 by arithmetic
   Now m ** 2 <= (SQRT n) ** 2     by EXP_EXP_LE_MONO_IMP, m <= SQRT n
   and (SQRT n) ** 2 <= n          by SQRT_PROPERTY
    so m ** 2 <= n                 by ineqaulities
   Thus k = 0 means m ** 2 = n,
   giving square n                 by square_eqn
   This contradicts ~square n.
*)
Theorem zig_sub_even_sq_div_4:
  !n m. zig n /\ ~square n /\ EVEN m /\ m <= SQRT n ==> 0 < (n - m ** 2) DIV 4
Proof
  spose_not_then strip_assume_tac >>
  qabbrev_tac `k = n - m ** 2` >>
  `k DIV 4 = 0` by decide_tac >>
  `k MOD 4 = 0` by rw[zig_sub_even_sq_mod_4, Abbr`k`] >>
  `k = 0` by metis_tac[DIVISION, MULT, ADD_0, DECIDE``0 < 4``] >>
  `m ** 2 <= (SQRT n) ** 2` by simp[] >>
  `(SQRT n) ** 2 <= n` by rw[SQRT_PROPERTY] >>
  qunabbrev_tac `k` >>
  `n = m ** 2` by decide_tac >>
  fs[square_eqn]
QED
(* move to: helperTwosqTheory. *)

(* Theorem: tok n ==> mills n = {} *)
(* Proof:
   By contradiction, suppose mills n <> {}.
   Then ?x y z. n = windmill (x, y, z)             by mills_element, MEMBER_NOT_EMPTY
     or         n = x ** 2 + 4 * y * z         by windmill_def
     so   n MOD 4
        = (x ** 2 + 4 * y * z) MOD 4           by above
        = (x ** 2) MOD 4                       by arithmetic
     But (x ** 2) MOD 4 IN {0; 1}              by mod_4_square
    This is a contradiction.
*)
Theorem mills_tok_empty:
  !n. tok n ==> mills n = {}
Proof
  spose_not_then strip_assume_tac >>
  `?x y z. n = windmill (x, y, z)` by metis_tac[mills_element, triple_parts, MEMBER_NOT_EMPTY] >>
  fs[windmill_def] >>
  assume_tac mod_4_square >>
  `3 NOTIN {0; 1}` by simp[] >>
  metis_tac[]
QED

(* Theorem: zag n ==> mills n = {} *)
(* Proof:
   By contradiction, suppose (mills n) <> {}.
   Then ?(x,y,z). n = windmill (x, y, z)           by MEMBER_NOT_EMPTY
                    = x ** 2 + 4 * y * z       by windmill_def, mills_def
   Note EVEN n                                 by even_zig_zag
    and EVEN 4 * y * z = 2 * (2 * y * z)       by EVEN_EXISTS
     so EVEN x ** 2                            by EVEN_SUB, EVEN n
     or EVEN x                                 by EVEN_SQ
    ==> ?h. x = 2 * h                          by EVEN_EXISTS
        and x ** 2 = 4 * h ** 2                by arithmetic
         so n = 4 * (h ** 2 + y * z)           by above
   This makes n MOD 4 = 0                      by arithmetic
   which is a contradiction.
*)
Theorem mills_zag_empty:
  !n. zag n ==> mills n = {}
Proof
  spose_not_then strip_assume_tac >>
  `EVEN n` by simp[even_zig_zag] >>
  `?x y z. n = windmill (x, y, z)` by metis_tac[MEMBER_NOT_EMPTY, mills_element, triple_parts] >>
  `_ = x ** 2 + 4 * y * z` by simp[windmill_def] >>
  `EVEN (4 * y * z)` by metis_tac[EVEN_EXISTS, DECIDE``4 * y * z = 2 * (2 * y * z)``] >>
  `x ** 2 = n - 4 * y * z` by decide_tac >>
  `EVEN (x ** 2)` by fs[EVEN_SUB] >>
  `EVEN x` by fs[EVEN_SQ] >>
  `?h. x = 2 * h` by metis_tac[EVEN_EXISTS] >>
  `x ** 2 = (2 * h) * (2 * h)` by metis_tac[EXP_2] >>
  `_ = 4 * h * h` by decide_tac >>
  `n = 4 * (h * h + y * z)` by decide_tac >>
  `n MOD 4 = 0` by fs[] >>
  decide_tac
QED

(* Theorem alias *)
Theorem mills_tik_nonempty = windmillTheory.mills_non_empty;
(* val mills_tik_nonempty = |- !n. tik n ==> mills n <> {}: thm *)

(* Theorem: tik n /\ n = windmill (x, y, z) ==> ODD x /\ x <= SQRT n *)
(* Proof:
   Note n = x ** 2 + 4 * y * z                 by windmill_def
   By contradiction, suppose EVEN x.
   Then ?k. x = 2 * k                          by EVEN_EXISTS
            n = (2 * k) ** 2 + 4 * y * z
              = 4 * (k ** 2 + y * z)           by arithmetic
         so n MOD 4 = 0                        by MOD_EQ_0
   This contradicts tik n.

   Also   x ** 2 <= n                          by arithmetic
   Thus        x <= SQRT n                     by SQRT_LE, SQRT_SQ
*)
Theorem windmill_mind_odd:
  !n x y z. tik n /\ n = windmill (x, y, z) ==> ODD x /\ x <= SQRT n
Proof
  rpt strip_tac >| [
    spose_not_then strip_assume_tac >>
    `?k. x = 2 * k` by metis_tac[EVEN_EXISTS, ODD_EVEN] >>
    fs[windmill_def] >>
    `(2 * k) ** 2 = 4 * k ** 2` by simp[Once EXP_2] >>
    fs[],
    fs[windmill_def] >>
    `x ** 2 <= n` by decide_tac >>
    metis_tac[SQRT_LE, SQRT_SQ, EXP_2]
  ]
QED

(* Theorem: zig n /\ n = windmill (x, y, z) ==> EVEN x /\ x <= SQRT n *)
(* Proof:
   Note n = x ** 2 + 4 * y * z                 by windmill_def
   By contradiction, suppose ODD x.
   Then ?k. x = 2 * k + 1                      by ODD_EXISTS
            n = (2 * k + 1) ** 2 + 4 * y * z
              = 4 * k ** 2 + 4 * k + 1 + 4 * y * z
              = 4 * (k ** 2 + k + y * z) + 1   by arithmetic
         so n MOD 4 = 1                        by arithmetic
   This contradicts zig n.

   Also   x ** 2 <= n                          by arithmetic
   Thus        x <= SQRT n                     by SQRT_LE, SQRT_SQ
*)
Theorem windmill_mind_even:
  !n x y z. zig n /\ n = windmill (x, y, z) ==> EVEN x /\ x <= SQRT n
Proof
  rpt strip_tac >| [
    spose_not_then strip_assume_tac >>
    `?k. x = 2 * k + 1` by metis_tac[ODD_EXISTS, ODD_EVEN, ADD1] >>
    fs[windmill_def] >>
    `(2 * k + 1) ** 2 = 4 * k ** 2 + 4 * k + 1` by simp[SUM_SQUARED, Once EXP_2] >>
    fs[],
    fs[windmill_def] >>
    `x ** 2 <= n` by decide_tac >>
    metis_tac[SQRT_LE, SQRT_SQ, EXP_2]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* Computation of (mills n)                                                  *)
(* ------------------------------------------------------------------------- *)

(* Idea:

Consider only odd n.
If n = 4k + 3, either undefined or empty.
If n = 4k + 1, if square n, this method gives only triple (SQRT n, 0, 0), not others.

var mills = {}
For (odd x starting from 1) {
  if (x * x = n) mills.insert([x, 0, 0]) break
  if (x * x > n) break
  let p = (n - x * x) DIV 4,
      q = list of divisors of p,
  for each divisor y, mills.insert([x,y,z]) where z = p DIV y.
}
return mills.

*)

(*

> mills(17)
[ [ 1, 1, 4 ],
  [ 1, 4, 1 ],
  [ 1, 2, 2 ],
  [ 3, 1, 2 ],
  [ 3, 2, 1 ] ]

get a set of odds below (SQRT n)

EVAL ``count (SQRT 17)``;
|- count (SQRT 17) = {3; 2; 1; 0}

EVAL ``IMAGE (\j. if ODD j then j else 1) (count (SQRT 17))``;
|- IMAGE (\j. if ODD j then j else 1) (count (SQRT 17)) = {3; 1}

get a set of pairs [x, (n - x * x) DIV 4]

EVAL ``let n = 17 in IMAGE (\j. if ODD j then [j; (n - j * j) DIV 4] else [1; (n - 1) DIV 4]) (count (SQRT n))``;
|- ... = {[3; 2]; [1; 4]};

given n, get a set of pair [d, n DIV d], that is, a pair of factor and cofactor.

EVAL ``let n = 10 in IMAGE (\j. [j; n DIV j]) (divisors n)``;
|- ... = = {[10; 1]; [5; 2]; [2; 5]; [1; 10]}

Expand pairs [x, (n - x * x) DIV 4] to triple [x,y,z]

EVAL ``IMAGE (\x. IMAGE (\l. x::l) (factor_pair ((17 - x * x) DIV 4))) {3; 1}``;
|- ... = {{[3; 2; 1]; [3; 1; 2]}; {[1; 4; 1]; [1; 2; 2]; [1; 1; 4]}}

EVAL ``let n = 17 in IMAGE (\x. IMAGE (\l. x::l) (factor_pair ((n - x * x) DIV 4))) (IMAGE (\j. if ODD j then j else 1) (count (SQRT n)))``;
|- ... = {{[3; 2; 1]; [3; 1; 2]}; {[1; 4; 1]; [1; 2; 2]; [1; 1; 4]}}

*)

(* Define the set of odd numbers up to n *)
Definition odds_to_def[nocompute]:
    odds_to n = {x | ODD x /\ x <= n}
End
(* use [nocompute] as this is not effective. *)

(* Theorem: x IN odds_to n <=> ODD x /\ x <= n *)
(* Proof: by odds_to_def.*)
Theorem odds_to_element:
  !n x. x IN odds_to n <=> ODD x /\ x <= n
Proof
  simp[odds_to_def]
QED

(* Idea: use (natural n) and apply filter to select the odds. *)
(* Note: this works, but not good as twice amount is generated and half is filtered away.
         Too many tests, making the process slow.
         Also, the map is not injective, no good for estimating size. *)

(* Theorem: odds_to n = IMAGE (\j. if ODD j then j else 1) (natural n) *)
(* Proof:
   Let s = IMAGE (\j. if ODD j then j else 1) (natural n).
   By odds_to_def, EXTENSION, EQ_IMP_THM, this is to show:
   (1) ODD x /\ x <= n ==> x IN s
       This is to show:
       ?j. x = (if ODD j then j else 1) /\ ?k. j = SUC k /\ k < n
       Let j = x, the first one is true        by ODD x
       Let k = PRE x.
       By ODD x, 0 < x                         by ODD
       so SUC (PRE x) = x                      by SUC_PRE, 0 < x
       and x <= n ==> PRE x < n                by PRE_LESS
   (2) x IN s ==> ODD x /\ x <= n
       Note ?z. z IN (natural n) /\
                x = if (ODD z then z else 1)   by IN_IMAGE
        and 0 < z /\ z <= n                    by natural_element
        ==> 0 < n                              by ineqaulities
       If ODD z, x = z, so ODD x and x <= n.
       If ~ODD z, then x = 1, so ODD 1 and 1 <= n.
*)
Theorem odds_to_eqn:
  !n. odds_to n = IMAGE (\j. if ODD j then j else 1) (natural n)
Proof
  (rw[odds_to_def, EXTENSION, EQ_IMP_THM] >> rw[]) >>
  qexists_tac `x` >>
  simp[] >>
  `0 < x` by metis_tac[ODD, NOT_ZERO] >>
  qexists_tac `PRE x` >>
  decide_tac
QED

(* Idea: use (count (HALF (n + 1))) to generate the odds directly. *)
(* Note: this is fast, and the map is injective, good for estimating size. *)

(* Theorem: odds_to n = IMAGE (\j. 2 * j + 1) (count (HALF (n + 1)) *)
(* Proof:
   If-part: x IN odds_to n ==> x IN IMAGE (\j. 2 * j + 1) (count (HALF (n + 1)))
      Note ODD x /\ x <= n               by odds_to_def
      Let j = HALF x,
      Then x = 2 * j + 1                 by ODD_HALF
       and 2 * j + 1 < n + 1             by x <= n
        so         j < HALF (n + 1)      by HALF_ODD_LT
        or j IN count (HALF (n + 1))     by IN_COUNT
       giving x as its image.
   Only-if part: x IN IMAGE (\j. 2 * j + 1) (count (HALF (n + 1))) ==> x IN odds_to n
      Note j < HALF (SUC n)              by IN_COUNT, ADD1
        so 2 * j + 1 <= n                by HALF_SUC_LE
       and ODD (2 * j + 1)               by ODD_EXISTS, ADD1
      Thus (2 * j + 1) IN odds_to n      by odds_to_def
*)
Theorem odds_to_thm[compute]:
  !n. odds_to n = IMAGE (\j. 2 * j + 1) (count (HALF (n + 1)))
Proof
  rw[EXTENSION, odds_to_def, EQ_IMP_THM] >| [
    qexists_tac `HALF x` >>
    imp_res_tac ODD_HALF >>
    `x < n + 1` by decide_tac >>
    simp[HALF_ODD_LT],
    metis_tac[ODD_EXISTS, ADD1],
    simp[HALF_SUC_LE, ADD1]
  ]
QED
(* put in computeLib *)

(*
EVAL ``odds_to 10``;
|- odds_to 10 = {9; 7; 5; 3; 1}

EVAL ``odds_to 11``;
|- odds_to 11 = {11; 9; 7; 5; 3; 1}
*)

(* Theorem: odds_to n SUBSET count (n + 1) *)
(* Proof:
   Let x IN (odds_to n)
   Then ODD x /\ x <= n                  by odds_to_def
     so x < n + 1                        by inequality
     or x IN count (n + 1)               by IN_COUNT
   Thus odds_to n SUBSET count (n + 1)   by SUBSET_DEF
*)
Theorem odds_to_subset_count:
  !n. odds_to n SUBSET count (n + 1)
Proof
  rw[odds_to_def, SUBSET_DEF]
QED

(* Theorem: FINITE (odds_to n) *)
(* Proof:
   Note odds_to n SUBSET count (n + 1)         by odds_to_subset_count
    and FINITE (count (n + 1))                 by FINITE_COUNT
     so FINITE (odds_to n)                     by SUBSET_FINITE
*)
Theorem odds_to_finite:
  !n. FINITE (odds_to n)
Proof
  metis_tac[odds_to_subset_count, FINITE_COUNT, SUBSET_FINITE]
QED

(* Theorem: CARD (odds_to n) = HALF (n + 1) *)
(* Proof:
   Let f = \j. 2 * j + 1,
       m = HALF (n + 1).
   Then odds_to n = IMAGE f (count m)          by odds_to_thm
    and FINITE (count m)                       by FINITE_COUNT
    and INJ f (count m) univ(:num)             by INJ_DEF, arithmetic

        CARD (odds_to n)
      = CARD (IMAGE f (count m))               by above
      = CARD (count m)                         by INJ_CARD_IMAGE_EQN
      = m                                      by CARD_COUNT
      = HALF (n + 1)                           by ADD1
*)
Theorem odds_to_card:
  !n. CARD (odds_to n) = HALF (n + 1)
Proof
  rpt strip_tac >>
  assume_tac odds_to_thm >>
  first_x_assum (qspec_then `n` strip_assume_tac) >>
  qabbrev_tac `f = \j. 2 * j + 1` >>
  qabbrev_tac `m = HALF (SUC n)` >>
  `INJ f (count m) univ(:num)` by rw[INJ_DEF, Abbr`f`] >>
  fs[INJ_CARD_IMAGE_EQN, ADD1]
QED

(* Define the set of even numbers up to n *)
Definition evens_to_def[nocompute]:
    evens_to n = {x | EVEN x /\ x <= n}
End
(* use [nocompute] as this is not effective. *)

(* Theorem: x IN evens_to n <=> EVEN x /\ x <= n *)
(* Proof: by evens_to_def.*)
Theorem evens_to_element:
  !n x. x IN evens_to n <=> EVEN x /\ x <= n
Proof
  simp[evens_to_def]
QED

(* Idea: use (count (n+1)) and apply filter to select the evens. *)
(* Note: this works, but not good as twice amount is generated and half is filtered away.
         Too many tests, making the process slow.
         Also, the map is not injective, no good for estimating size. *)

(* Theorem: evens_to n = IMAGE (\j. if EVEN j then j else 0) (count (n+1)) *)
(* Proof:
   Let s = IMAGE (\j. if EVEN j then j else 0) (count (n+1)).
   By evens_to_def, EXTENSION, EQ_IMP_THM, this is to show:
   (1) EVEN x /\ x <= n ==> x IN s
       This is to show:
       ?j. x = (if EVEN j then j else 0) /\ j < n + 1
       Let j = x, the first one is true        by EVEN x
       and x <= n means x < n + 1              by arithmetic
   (2) x IN s ==> EVEN x /\ x <= n
       Note ?z. z IN (count (n+1)) /\
                x = if (EVEN z then z else 0)  by IN_IMAGE
        and z < n + 1                          by IN_COUNT
        ==> z <= n                             by arithmetic
       If EVEN z, x = z, so EVEN x and x <= n.
       If ~EVEN z, then x = 0, so EVEN 0 and 0 <= n.
*)
Theorem evens_to_eqn:
  !n. evens_to n = IMAGE (\j. if EVEN j then j else 0) (count (n+1))
Proof
  (rw[evens_to_def, EXTENSION, EQ_IMP_THM] >> rw[]) >>
  qexists_tac `x` >>
  simp[]
QED

(* Idea: use (count (HALF (n + 1))) to generate the evens directly. *)
(* Note: this is fast, and the map is injective, good for estimating size. *)

(* Theorem: evens_to n = IMAGE (\j. 2 * j) (count (HALF (n + 2))) *)
(* Proof:
   If-part: x IN evens_to n ==> x IN IMAGE (\j. 2 * j) (count (HALF (n + 2)))
      Note EVEN x /\ x <= n              by evens_to_def
      Let j = HALF x,
      Then x = 2 * j                     by EVEN_HALF
       and     2 * j < SUC n             by x <= n
        so     j + j < n + 1             by arithmetic
       and     j + 1 < (n + 2) - j       by arithmetic
        so         j < HALF (n + 2)      by LESS_HALF_IFF
        or j IN count (HALF (n + 2))     by IN_COUNT
       giving x as its image.
   Only-if part: x IN IMAGE (\j. 2 * j) (count (HALF (n + 2))) ==> x IN evens_to n
      Note j < HALF (n + 2)              by IN_COUNT
        so j + 1 < (n + 2) - j           by LESS_HALF_IFF
        or j + j < n + 1                 by arithmetic
        or 2 * j <= n                    by arithmetic
       and EVEN (2 * j)                  by EVEN_EXISTS
      Thus (2 * j) IN evens_to n         by evns_to_def
*)
Theorem evens_to_thm[compute]:
  !n. evens_to n = IMAGE (\j. 2 * j) (count (HALF (n + 2)))
Proof
  rw[EXTENSION, evens_to_def, EQ_IMP_THM] >| [
    qexists_tac `HALF x` >>
    imp_res_tac EVEN_HALF >>
    simp[] >>
    qabbrev_tac `j = HALF x` >>
    `j + 1 < (n + 2) - j` by decide_tac >>
    simp[LESS_HALF_IFF],
    metis_tac[EVEN_EXISTS],
    `j + 1 < (n + 2) - j` by fs[LESS_HALF_IFF] >>
    decide_tac
  ]
QED
(* put in computeLib *)

(*
EVAL ``evens_to 10``;
|- evens_to 10 = {10; 8; 6; 4; 2; 0}

EVAL ``evens_to 11``;
|- evens_to 11 = {10; 8; 6; 4; 2; 0}
*)

(* Theorem: (evens_to n) SUBSET (count (n + 1)) *)
(* Proof:
   Let x IN (evens_to n)
   Then EVEN x /\ x <= n                       by evens_to_def
    so x < n + 1                               by arithmetic
     so x IN (count (n + 1))                   by IN_COUNT
   Thus (evens_to n) SUBSET (count (n + 1))    by SUBSET_DEF
*)
Theorem evens_to_subset_count:
  !n. (evens_to n) SUBSET (count (n + 1))
Proof
  rw[evens_to_def, SUBSET_DEF]
QED

(* Theorem: FINITE (evens_to n) *)
(* Proof:
   Note (evens_to n) SUBSET (count (n + 1))    by evens_to_subset_count
      and FINITE (count n)                     by FINITE_COUNT;
     so FINITE (evens_to n)                    by SUBSET_FINITE
*)
Theorem evens_to_finite:
  !n. FINITE (evens_to n)
Proof
  metis_tac[evens_to_subset_count, FINITE_COUNT, SUBSET_FINITE]
QED

(* Theorem: CARD (evens_to n) = HALF (n + 2) *)
(* Proof:
   Let f = \j. 2 * j,
       m = HALF (n + 2).
   Then evens_to n = IMAGE f (count m)         by evens_to_thm
    and FINITE (count m)                       by FINITE_COUNT
    and INJ f (count m) univ(:num)             by INJ_DEF, arithmetic

        CARD (evens_to n)
      = CARD (IMAGE f (count m))               by above
      = CARD (count m)                         by INJ_CARD_IMAGE_EQN
      = m                                      by CARD_COUNT
      = HALF (n + 2)                           by arithmetic
*)
Theorem evens_to_card:
  !n. CARD (evens_to n) = HALF (n + 2)
Proof
  rpt strip_tac >>
  assume_tac evens_to_thm >>
  first_x_assum (qspec_then `n` strip_assume_tac) >>
  qabbrev_tac `f = \j. 2 * j` >>
  qabbrev_tac `m = HALF (n + 2)` >>
  `INJ f (count m) univ(:num)` by rw[INJ_DEF, Abbr`f`] >>
  fs[INJ_CARD_IMAGE_EQN]
QED

(* Define the set of factor-cofactor pairs *)
Definition factor_pair_def:
   factor_pair n = IMAGE (\j. (j, n DIV j)) (divisors n)
End
(* When n = 0, divisors 0 = {} making factor_pair 0 = {}. *)

(*
EVAL ``factor_pair 10``;
|- factor_pair 10 = {(10,1); (5,2); (2,5); (1,10)}

EVAL ``factor_pair 6``;
|- factor_pair 6 = {(6,1); (3,2); (2,3); (1,6)}

EVAL ``factor_pair 0``;
|- factor_pair 0 = {}

*)

(* Theorem: factor_pair 0 = {} *)
(* Proof:
     factor_pair 0
   = IMAGE (\j. (j, n DIV j)) (divisors 0)     by factor_pair_def
   = IMAGE (\j. (j, n DIV j)) {}               by divisors_0
   = {}                                        by IMAGE_EMPTY
*)
Theorem factor_pair_0:
  factor_pair 0 = {}
Proof
  simp[factor_pair_def, divisors_0]
QED

(* Theorem: factor_pair n = {} <=> n = 0 *)
(* Proof:
   Let f = \j. (j, n DIV j).
       factor_pair n = {}
   <=> IMAGE f (divisors n) = {}   by factor_pair_def
   <=> divisors n = {}             by IMAGE_EQ_EMPTY
   <=> n = 0                       by divisors_eq_empty
*)
Theorem factor_pair_empty:
  !n. factor_pair n = {} <=> n = 0
Proof
  rw[factor_pair_def, divisors_eq_empty]
QED

(* Theorem: 0 < n ==> ((p, q) IN factor_pair n <=> n = p * q) *)
(* Proof:
   By factor_pair_def, this is to show:
      q = n DIV p /\ p IN divisors n <=> n = p * q
   If part: q = n DIV p /\ p IN divisors n ==> n = p * q
      Note 0 < p /\ p <= n /\ p divides n      by divisors_def
        so p * q = p * (n DIV p) = n           by DIVIDES_FACTORS, 0 < n
   Only-if part: n = p * q ==> q = n DIV p /\ p IN divisors n
      Note 0 < p                               by MULT_EQ_0
        so q = n DIV p                         by MULT_TO_DIV
      Also p divides n                         by divides_def
        so p IN divisors n                     by divisors_element_alt, 0 < n
*)
Theorem factor_pair_nonzero_element:
  !n p q. 0 < n ==> ((p, q) IN factor_pair n <=> n = p * q)
Proof
  rw[factor_pair_def, EQ_IMP_THM] >| [
    rfs[divisors_def] >>
    simp[DIVIDES_FACTORS],
    `0 < p` by metis_tac[MULT_EQ_0, NOT_ZERO] >>
    simp[MULT_TO_DIV],
    qabbrev_tac `n = p * q` >>
    `p divides n` by fs[divides_def, Abbr`n`] >>
    simp[divisors_element_alt]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* Windmills for tiks.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Define the set of windmill triples for tiks. *)
Definition mills_tik_def:
   mills_tik n = BIGUNION (IMAGE (\x. IMAGE (\p. (x,p)) (factor_pair ((n - x * x) DIV 4))) (odds_to (SQRT n)))
End

(*
EVAL ``mills_tik 17``;
|- mills_tik 17 = {(3,2,1); (3,1,2); (1,4,1); (1,2,2); (1,1,4)}

EVAL ``mills_tik 37``;
|- mills_tik 37 = {(5,3,1); (5,1,3); (3,7,1); (3,1,7); (1,9,1); (1,3,3); (1,1,9)}

EVAL ``mills_tik 25``;
|- mills_tik 25 = {(3,4,1); (3,2,2); (3,1,4); (1,6,1); (1,3,2); (1,2,3); (1,1,6)}

EVAL ``GENLIST (\k. let n = 4 * k + 1 in (n, CARD (mills_tik n), HALF n)) 5``;
|- ... = [(1,0,0); (5,1,2); (9,2,4); (13,3,6); (17,5,8)]

EVAL ``GENLIST (\k. let n = 4 * k + 1 in (n, CARD (mills_tik n), HALF n)) 10``;
|- ... = [(1,0,0); (5,1,2); (9,2,4); (13,3,6); (17,5,8);
          (21,4,10); (25,7,12); (29,5,14); (33,10,16); (37,7,18)]
*)

(* Idea: make (mills n) computable for tiks. *)

(* Theorem: tik n /\ ~square n ==> mills n = mills_tik n *)
(* Proof:
   By EXTENSION, EQ_IMP_THM, this is to show:
   (1) tik n /\ ~square n /\ t IN mills n ==> t IN mills_tik n
       Note t = (x,y,z) and n = windmill (x, y, z)           by mills_def
       By mills_tik def, this is to show:
          ?s. (x,y,z) IN s /\
          ?q. s = IMAGE (\p. (q,p)) (factor_pair ((n - q ** 2) DIV 4)) /\ q IN odds_to (SQRT n)
       Let s = IMAGE (\p. (x,p)) (factor_pair ((n - x ** 2) DIV 4)),
       To show: (x,y,z) IN IMAGE (\p. (x,p)) (factor_pair ((n - x ** 2) DIV 4))
       Note y * z = (n - x ** 2) DIV 4                   by windmill_yz_product
        and y * z <> 0                                   by windmill_nonsquare, ~square n
       By factor_pair_def, this is to show:
       (1) z = (n - x ** 2) DIV 4 DIV y
       (2) y IN divisors ((n - x ** 2) DIV 4)
       Both are true                                     by windmill_arm_divisors, ~square n

       Let q = x.
       Note ODD x /\ x <= SQRT n                         by windmill_mind_odd, tik n
       Thus x IN odds_to (SQRT n)                        by odds_to_def
   (2) tik n /\ ~square n /\ t IN mills_tik n ==> t IN mills n
       Note ?x y z. t = (x, y, z)                        by triple_parts
       need to show: n = windmill (x, y, z)                  by mills_def
       By mills_tik_def, factor_pair_def, odds_to_def, we have:
       (x,y,z) IN IMAGE (\p. (q,p))
                        (IMAGE (\j. (j,(n - q ** 2) DIV 4 DIV j))
                        (divisors ((n - q ** 2) DIV 4)))
        where q IN odds_to (SQRT n)

       Note ODD q /\ q <= SQRT n                         by odds_to_def
        and (n - q ** 2) MOD 4 = 0                       by tik_sub_odd_sq_mod_4
       Let k = (n - q ** 2) DIV 4.
       Then 0 < k                                        by tik_sub_odd_sq_div_4, tik n, ~square n
       Goal becomes: (x,y,z) IN IMAGE (\p. (q,p)) (IMAGE (\j. (j,k DIV j)) (divisors k)) ==> n = windmill (x, y, z).

       Note n - q ** 2 = k * 4                           by DIVISION, (n - q ** 2) MOD 4 = 0
         so n = q ** 2 + 4 * k                           by arithmetic

       By IN_IMAGE, x = q,
        and 0 < y /\ y <= k /\ y divides k               by divisors_def
       with z = k DIV y                                  by function application
        and k = y * z                                    by DIVIDES_FACTORS, 0 < y
         so n = x ** 2 + 4 * y * z IN windmill n         by windmill_def
*)
Theorem mills_tik_eqn:
  !n. tik n /\ ~square n ==> mills n = mills_tik n
Proof
  rw[EXTENSION, EQ_IMP_THM] >| [
    rename1 `t IN _` >>
    fs[mills_def] >>
    `(x,y,z) IN mills_tik n` suffices_by metis_tac[] >>
    qabbrev_tac `foo = (n = windmill (x, y, z))` >>
    simp[mills_tik_def] >>
    qexists_tac `IMAGE (\p. (x,p)) (factor_pair ((n - x ** 2) DIV 4))` >>
    rpt strip_tac >| [
      `(n - x ** 2) DIV 4 <> 0` by metis_tac[windmill_yz_product, windmill_nonsquare] >>
      simp[factor_pair_def] >>
      simp[Abbr`foo`] >>
      imp_res_tac windmill_arm_divisors >>
      fs[LET_THM] >>
      metis_tac[],
      qexists_tac `x` >>
      simp[] >>
      simp[odds_to_def] >>
      metis_tac[windmill_mind_odd]
    ],
    rename1 `t IN _` >>
    `?x y z. t = (x,y,z)` by simp[triple_parts] >>
    fs[mills_def] >>
    fs[mills_tik_def, factor_pair_def] >>
    rename1 `q IN _` >>
    `ODD q /\ q <= SQRT n` by fs[odds_to_def] >>
    qabbrev_tac `k = (n - q ** 2) DIV 4` >>
    `0 < k` by simp[tik_sub_odd_sq_div_4, Abbr`k`] >>
    fs[] >>
    `(n - q ** 2) MOD 4 = 0` by simp[tik_sub_odd_sq_mod_4] >>
    `n - q ** 2 = k * 4` by metis_tac[DIVISION, ADD_0, DECIDE ``0 < 4``] >>
    `n = 4 * k + q ** 2` by decide_tac >>
    fs[divisors_def, windmill_def] >>
    simp[DIVIDES_FACTORS]
  ]
QED

(* This is a fantastic result! *)

(* Theorem: mills n = if tok n then {}
                 else if tik n /\ ~square n then mills_tik n else mills n *)
(* Proof:
   Note if (tok n), then mills n = {}            by mills_tok_empty
    and if (tik n) and ~square n,
        mills n = mills_tik n                           by mills_tik_eqn
*)
Theorem mills_odd_eqn[compute]:
  !n. mills n = if tok n then {}
                 else if tik n /\ ~square n then mills_tik n
                 else mills n
Proof
  rw[mills_tok_empty, mills_tik_eqn]
QED
(* put in computeLib *)

(*
> EVAL ``mills 13``;
val it = |- mills 13 = {(3,1,1); (1,3,1); (1,1,3)}: thm
> EVAL ``mills 17``;
val it = |- mills 17 = {(3,2,1); (3,1,2); (1,4,1); (1,2,2); (1,1,4)}: thm
> EVAL ``mills 21``;
val it = |- mills 21 = {(3,3,1); (3,1,3); (1,5,1); (1,1,5)}: thm

> EVAL ``mills 37``;
val it = |- mills 37 =
      {(5,3,1); (5,1,3); (3,7,1); (3,1,7); (1,9,1); (1,3,3); (1,1,9)}: thm
> EVAL ``mills 97``;
val it = |- mills 97 =
      {(9,4,1); (9,2,2); (9,1,4); (7,12,1); (7,6,2); (7,4,3); (7,3,4);
       (7,2,6); (7,1,12); (5,18,1); (5,9,2); (5,6,3); (5,3,6); (5,2,9);
       (5,1,18); (3,22,1); (3,11,2); (3,2,11); (3,1,22); (1,24,1); (1,12,2);
       (1,8,3); (1,6,4); (1,4,6); (1,3,8); (1,2,12); (1,1,24)}: thm
*)

(* Theorem: tok n ==> CARD (mills n) = 0 *)
(* Proof:
   Since tok n, mills n = {}       by mills_tok_empty
   Thus CARD (mills n) = 0         by CARD_EMPTY
*)
Theorem mills_tok_card:
  !n. tok n ==> CARD (mills n) = 0
Proof
  rw[mills_tok_empty]
QED

(* Theorem: tik n /\ ~square n ==>
            CARD (mills n) = SIGMA (\x. CARD (divisors ((n - x ** 2) DIV 4))) (odds_to (SQRT n)) *)
(* Proof:
   Note mills n = mills_tik n                   by mills_tik_eqn
   Expand by mills_tik_def.
   Let s = odds_to (SQRT n),
       f = \x. IMAGE (\p. (x,p)) (factor_pair ((n - x ** 2) DIV 4)),
       P = IMAGE f s.

   Note FINITE s                               by odds_to_finite
    and FINITE P                               by IMAGE_FINITE
   Also EVERY_FINITE P                         by IMAGE_FINITE, factor_pair_def, divisors_finite


   Claim: PAIR_DISJOINT P
   Proof: By DISJOINT_ALT, this is to show:
          x IN s /\ u = IMAGE (\p. (x,p)) (factor_pair ((n - x ** 2) DIV 4)) /\
          y IN s /\ v = IMAGE (\p. (y,p)) (factor_pair ((n - y ** 2) DIV 4)) /\
          u <> v /\ z IN u /\ z IN v ==> F
          Note ?p. z = (x,p)                   by IN_IMAGE, z IN u
           and ?q. z = (y,q)                   by IN_IMAGE, z IN v
            so x = y                           by equating FST z
           ==> u = v, contradicts u <> v       [1]

   Claim: INJ f s univ(:num # num # num -> bool)
   Proof: By INJ_DEF, factor_pair_def, this is to show:
          x IN odds_to (SQRT n) /\
          y IN odds_to (SQRT n) /\
          IMAGE (\p. (x,p)) (IMAGE (\j. (j,k DIV j)) (divisors k)) =
          IMAGE (\p. (y,p)) (IMAGE (\j. (j,h DIV j)) (divisors h))
          ==> x = y, where k = (n - x ** 2) DIV 4, h = (n - y ** 2) DIV 4.
          Note 0 < k                           by tik_sub_odd_sq_div_4, odds_to_def
            so 1 IN divisors k                 by divisors_has_1
          Thus (x,1,k) IN first IMAGE          by IN_IMAGE
            or (x,1,k) IN second IMAGE         by first IMAGE = second IMAGE
            so x = y                           by FST of second IMAGE, [2]

    Claim: !x. x IN s ==>
            (CARD o f) x = (\x. CARD (divisors ((n - x ** 2) DIV 4))) x
    Proof: Let k = (n - x ** 2) DIV 4,
               t = IMAGE (\j. (j,k DIV j)) (divisors k).
           Note 0 < k                          by tik_sub_odd_sq_div_4, odds_to_def
           By factor_pair_def, this is to show:
           CARD (IMAGE (\p. (x,p)) t) = CARD (divisors k)

            Now FINITE t                                   by IMAGE_FINITE, divisors_finite
            and INJ (\p. (x,p)) t univ(:num # num # num)   by INJ_DEF, FST
             so CARD (IMAGE (\p. (x,p)) t) = CARD t        by INJ_CARD_IMAGE_EQN

           Let f = \j. (j,k DIV j).
           Note FINITE (divisors k)                        by divisors_finite, 0 < k
            and INJ f (divisors k) univ(:num # num)        by INJ_DEF, FST
             so CARD t = CARD (divisors k)                 by INJ_CARD_IMAGE_EQN, [3]

       CARD (BIGUNION P)
     = SIGMA CARD P                                        by CARD_BIGUNION_PAIR_DISJOINT, [1]
     = SIGMA CARD (IMAGE f s)                              by above
     = SIGMA (CARD o f) s                                  by SUM_IMAGE_INJ_o, [2]
     = SIGMA (\x. CARD (divisors ((n - x ** 2) DIV 4))) s  by SIGMA_CONG, [3]
*)
Theorem mills_tik_card:
  !n. tik n /\ ~square n ==>
        CARD (mills n) = SIGMA (\x. CARD (divisors ((n - x ** 2) DIV 4))) (odds_to (SQRT n))
Proof
  rpt strip_tac >>
  imp_res_tac mills_tik_eqn >>
  fs[mills_tik_def] >>
  qabbrev_tac `s = odds_to (SQRT n)` >>
  qabbrev_tac `f = \x. IMAGE (\p. (x,p)) (factor_pair ((n - x ** 2) DIV 4))` >>
  qabbrev_tac `P = IMAGE f s` >>
  `FINITE s` by rw[odds_to_finite, Abbr`s`] >>
  `FINITE P` by fs[Abbr`P`] >>
  `EVERY_FINITE P` by
  (fs[Abbr`P`] >>
  rpt strip_tac >>
  fs[factor_pair_def, divisors_finite, Abbr`f`]) >>
  `PAIR_DISJOINT P` by
    (fs[DISJOINT_ALT, Abbr`P`] >>
  rpt strip_tac >>
  fs[Abbr`f`] >>
  `?p. x'' = (x,p)` by metis_tac[IN_IMAGE] >>
  `?q. x'' = (x',q)` by metis_tac[IN_IMAGE] >>
  `x = x'` by fs[] >>
  metis_tac[]) >>
  `INJ f s univ(:num # num # num -> bool)` by
      (rw[INJ_DEF, odds_to_def, factor_pair_def, Abbr`f`, Abbr`s`] >>
  qabbrev_tac `k = (n - x ** 2) DIV 4` >>
  qabbrev_tac `k' = (n - x' ** 2) DIV 4` >>
  `0 < k` by simp[tik_sub_odd_sq_div_4, Abbr`k`] >>
  `0 < k'` by simp[tik_sub_odd_sq_div_4, Abbr`k'`] >>
  `1 IN divisors k` by simp[divisors_has_1] >>
  `(x,1,k) IN IMAGE (\p. (x,p)) (IMAGE (\j. (j,k DIV j)) (divisors k))` by simp[] >>
  `(x,1,k) IN IMAGE (\p. (x',p)) (IMAGE (\j. (j,k' DIV j)) (divisors k'))` by metis_tac[] >>
  fs[]) >>
  imp_res_tac CARD_BIGUNION_PAIR_DISJOINT >>
  `_ = SIGMA CARD (IMAGE f s)` by simp[Abbr`P`] >>
  `_ = SIGMA (CARD o f) s` by simp[SUM_IMAGE_INJ_o] >>
  `SIGMA (CARD o f) s = SIGMA (\x. CARD (divisors ((n - x ** 2) DIV 4))) s` suffices_by simp[] >>
  irule SIGMA_CONG >>
  rw[odds_to_def, Abbr`s`] >>
  `0 < (n - x ** 2) DIV 4` by simp[tik_sub_odd_sq_div_4] >>
  rw[factor_pair_def, Abbr`f`] >>
  qabbrev_tac `k = (n - x ** 2) DIV 4` >>
  qabbrev_tac `t = IMAGE (\j. (j,k DIV j)) (divisors k)` >>
  `FINITE t` by simp[divisors_finite, Abbr`t`] >>
  `INJ (\p. (x,p)) t univ(:num # num # num)` by rw[INJ_DEF, Abbr`t`] >>
  `CARD (IMAGE (\p. (x,p)) t) = CARD t` by rw[INJ_CARD_IMAGE_EQN] >>
  qabbrev_tac `f = \j. (j,k DIV j)` >>
  `CARD (IMAGE f (divisors k)) = CARD (divisors k)` suffices_by simp[Abbr`t`] >>
  `FINITE (divisors k)` by simp[divisors_finite] >>
  `INJ f (divisors k) univ(:num # num)` by rw[INJ_DEF, Abbr`f`] >>
  simp[INJ_CARD_IMAGE_EQN]
QED

(* This is really good! *)

(* Theorem: tik n /\ ~square n ==>
            CARD (mills n) <= SIGMA (\x. 2 * SQRT ((n - x ** 2) DIV 4)) (odds_to (SQRT n)) *)
(* Proof:
   Let s = odds_to (SQRT n),
       f = \x. CARD (divisors ((n - x ** 2) DIV 4)),
       g = \x. 2 * SQRT ((n - x ** 2) DIV 4).
   Then CARD (mills n) =  SIGMA f s            by mills_tik_card
    and FINITE s                               by odds_to_finite

   Claim: !x. x IN s ==> f x <= g x
   Proof: Let k = (n - x ** 2) DIV 4.
          This is to show:
          x IN s ==> CARD (divisors k) <= 2 * SQRT k
          which is true                        by divisors_card_upper, [1]

   Therefore, CARD (mills n) <= SIGMA f s      by SIGMA_LE_SIGMA, [1]
*)
Theorem mills_tik_card_upper_thm:
  !n. tik n /\ ~square n ==>
        CARD (mills n) <= SIGMA (\x. 2 * SQRT ((n - x ** 2) DIV 4)) (odds_to (SQRT n))
Proof
  rpt strip_tac >>
  imp_res_tac mills_tik_card >>
  qabbrev_tac `s = odds_to (SQRT n)` >>
  qabbrev_tac `f = \x. CARD (divisors ((n - x ** 2) DIV 4))` >>
  qabbrev_tac `g = \x. 2 * SQRT ((n - x ** 2) DIV 4)` >>
  `FINITE s` by simp[odds_to_finite, Abbr`s`] >>
  `!x. x IN s ==> f x <= g x` by simp[divisors_card_upper, Abbr`f`, Abbr`g`] >>
  simp[SIGMA_LE_SIGMA]
QED

(* Theorem: tik n /\ ~square n ==>
            CARD (mills n) <= 2 * SQRT (n DIV 4) * HALF (1 + SQRT n) *)
(* Proof:
   Let s = odds_to (SQRT n),
       f = \x. 2 * SQRT ((n - x ** 2) DIV 4),
       k = 2 * SQRT (n DIV 4),
       g = \x. k.
   Then FINITE s                               by odds_to_finite
    and CARD (mills n) <= SIGMA f s            by mills_tik_card_upper_thm

   Claim: !x. x IN s ==> f x <= g x
   Proof: Let h = (n - x ** 2) DIV 4.
          Note n - x ** 2 <= n                 by arithmetic
           ==>      h <= n DIV 4               by DIV_LE_MONOTONE
           ==> SQRT h <= SQRT (n DIV 4)        by SQRT_LE
           ==>    f x <= g x                   by LE_MULT_LCANCEL, [1]

    Note !x. x IN s ==> g x = k                by function g

    CARD (mills n) <= SIGMA f s                by above
                   <= SIGMA g s                by SIGMA_LE_SIGMA, [1]
                    = k * CARD s               by SIGMA_CONSTANT
                    = k * (HALF (1 + SQRT n))  by odds_to_card
*)
Theorem mills_tik_card_upper_tight:
  !n. tik n /\ ~square n ==>
        CARD (mills n) <= 2 * SQRT (n DIV 4) * HALF (1 + SQRT n)
Proof
  rpt strip_tac >>
  imp_res_tac mills_tik_card_upper_thm >>
  qabbrev_tac `s = odds_to (SQRT n)` >>
  qabbrev_tac `k = 2 * SQRT (n DIV 4)` >>
  qabbrev_tac `f = \x. 2 * SQRT ((n - x ** 2) DIV 4)` >>
  qabbrev_tac `g = \x:num. k` >>
  `!x. x IN s ==> f x <= g x` by
  (rw[odds_to_def, Abbr`f`, Abbr`g`, Abbr`s`] >>
  `n - x ** 2 <= n` by decide_tac >>
  qabbrev_tac `h = (n - x ** 2) DIV 4` >>
  `h <= n DIV 4` by simp[DIV_LE_MONOTONE, Abbr`h`] >>
  `SQRT h <= SQRT (n DIV 4)` by simp[SQRT_LE] >>
  simp[Abbr`k`]) >>
  `FINITE s` by simp[odds_to_finite, Abbr`s`] >>
  `SIGMA f s <= SIGMA g s` by simp[SIGMA_LE_SIGMA] >>
  `!x. x IN s ==> g x = k` by simp[Abbr`g`] >>
  `SIGMA g s = k * CARD s` by simp[SIGMA_CONSTANT] >>
  `CARD s = HALF (1 + SQRT n)` by simp[odds_to_card, Abbr`s`] >>
  fs[]
QED


(* Theorem: tik n /\ ~square n ==> CARD (mills n) <= n *)
(* Proof:
   Let k = n DIV 4.
   Note 2 * SQRT k <= SQRT (4 * k)                 by SQRT_MULT_LE, 4 = 2 ** 2
    and HALF (1 + SQRT n) <= SQRT n                by HALF_SUC

        CARD (mills n)
     <= 2 * SQRT k * HALF (1 + SQRT n)             by mills_tik_card_upper_tight
     <= SQRT (4 * k) * SQRT n                      by LE_MONO_MULT2
     <= SQRT (4 * k + 1) * SQRT n                  by SQRT_LE
      = SQRT n * SQRT n                            by n = 4 * k + 1
     <= n                                          by SQ_SQRT_LE
*)
Theorem mills_tik_card_upper:
  !n. tik n /\ ~square n ==> CARD (mills n) <= n
Proof
  rpt strip_tac >>
  imp_res_tac mills_tik_card_upper_tight >>
  qabbrev_tac `k = n DIV 4` >>
  `2 * SQRT k <= SQRT n` by
  (`2 ** 2 = 4` by simp[] >>
  `2 = SQRT 4` by metis_tac[SQRT_OF_SQ] >>
  `2 * SQRT k <= SQRT (4 * k)` by metis_tac[SQRT_MULT_LE] >>
  `n = 4 * k + 1` by metis_tac[DIVISION, MULT_COMM, DECIDE ``0 < 4``] >>
  `4 * k < n` by decide_tac >>
  `SQRT (4 * k) <= SQRT n` by simp[SQRT_LT] >>
  decide_tac) >>
  `HALF (1 + SQRT n) <= SQRT n` by metis_tac[HALF_SUC, ADD1, ADD_COMM] >>
  `2 * SQRT k * HALF (1 + SQRT n) <= SQRT n * SQRT n` by simp[LE_MONO_MULT2] >>
  `SQRT n * SQRT n <= n` by simp[SQ_SQRT_LE] >>
  decide_tac
QED

(* Not a tight bound, but a clean result. *)

(* ------------------------------------------------------------------------- *)
(* Windmills for zigs.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Define the set of windmill triples for zigs. *)
Definition mills_zig_def:
   mills_zig n = BIGUNION (IMAGE (\x. IMAGE (\p. (x,p)) (factor_pair ((n - x * x) DIV 4))) (evens_to (SQRT n)))
End

(*
EVAL ``mills_zig 8``;
|- mills_zig 8 = {(2,1,1); (0,2,1); (0,1,2)}

EVAL ``mills_zig 32``;
|- mills_zig 32 = {(4,4,1); (4,2,2); (4,1,4); (2,7,1); (2,1,7); (0,8,1); (0,4,2); (0,2,4); (0,1,8)}

EVAL ``mills_zig 20``;
   |- mills_zig 20 = {(4,1,1); (2,4,1); (2,2,2); (2,1,4); (0,5,1); (0,1,5)}

EVAL ``mills_zig 24``;
|- mills_zig 24 = {(4,2,1); (4,1,2); (2,5,1); (2,1,5); (0,6,1); (0,3,2); (0,2,3); (0,1,6)}

EVAL ``GENLIST (\k. let n = 4 * k in (n, CARD (mills_zig n), HALF n)) 5``;
|- ... = [(0,0,0); (4,1,2); (8,3,4); (12,4,6); (16,5,8)]

EVAL ``GENLIST (\k. let n = 4 * k in (n, CARD (mills_zig n), HALF n)) 10``;
|- ... = [(0,0,0); (4,1,2); (8,3,4); (12,4,6); (16,5,8); (20,6,10);
          (24,8,12); (28,8,14); (32,9,16); (36,9,18)]
*)

(* Idea: make (mills n) computable for zigs. *)

(* Theorem: zig n /\ ~square n ==> mills n = mills_zig n *)
(* Proof:
   By EXTENSION, EQ_IMP_THM, this is to show:
   (1) zig n /\ ~square n /\ t IN mills n ==> t IN mills_zig n
       Note t = (x,y,z) and n = windmill (x, y, z)           by mills_def
       By mills_zig def, this is to show:
          ?s. (x,y,z) IN s /\
          ?q. s = IMAGE (\p. (q,p)) (factor_pair ((n - q ** 2) DIV 4)) /\ q IN evens_to (SQRT n)
       Let s = IMAGE (\p. (x,p)) (factor_pair ((n - x ** 2) DIV 4)),
       To show: (x,y,z) IN IMAGE (\p. (x,p)) (factor_pair ((n - x ** 2) DIV 4))
       Note y * z = (n - x ** 2) DIV 4                   by windmill_yz_product
        and y * z <> 0                                   by windmill_nonsquare, ~square n
       By factor_pair_def, this is to show:
       (1) z = (n - x ** 2) DIV 4 DIV y
       (2) y IN divisors ((n - x ** 2) DIV 4)
       Both are true                                     by windmill_arm_divisors, ~square n

       Let q = x.
       Note ODD x /\ x <= SQRT n                         by windmill_mind_odd, tik n
       Thus x IN odds_to (SQRT n)                        by odds_to_def
   (2) zig n /\ ~square n /\ t IN mills_zig n ==> t IN mills n
       Note ?x y z. t = (x, y, z)                        by triple_parts
       need to show: n = windmill (x, y, z)                  by mills_def
       By mills_zig_def, factor_pair_def, evens_to_def, we have:
       (x,y,z) IN IMAGE (\p. (q,p))
                        (IMAGE (\j. (j,(n - q ** 2) DIV 4 DIV j))
                        (divisors ((n - q ** 2) DIV 4)))
        where q IN odds_to (SQRT n)

       Note EVEN q /\ q <= SQRT n                        by evens_to_def
        and (n - q ** 2) MOD 4 = 0                       by zig_sub_even_sq_mod_4
       Let k = (n - q ** 2) DIV 4.
       Then 0 < k                                        by zig_sub_even_sq_div_4, zig n, ~square n
       Goal becomes: (x,y,z) IN IMAGE (\p. (q,p)) (IMAGE (\j. (j,k DIV j)) (divisors k)) ==> n = windmill (x, y, z).

       Note n - q ** 2 = k * 4                           by DIVISION, (n - q ** 2) MOD 4 = 0
         so n = q ** 2 + 4 * k                           by arithmetic

       By IN_IMAGE, x = q,
        and 0 < y /\ y <= k /\ y divides k               by divisors_def
       with z = k DIV y                                  by function application
        and k = y * z                                    by DIVIDES_FACTORS, 0 < y
         so n = x ** 2 + 4 * y * z IN windmill n         by windmill_def
*)
Theorem mills_zig_eqn:
  !n. zig n /\ ~square n ==> mills n = mills_zig n
Proof
  rw[EXTENSION, EQ_IMP_THM] >| [
    rename1 `t IN _` >>
    fs[mills_def] >>
    `(x,y,z) IN mills_zig n` suffices_by metis_tac[] >>
    qabbrev_tac `foo = (n = windmill (x, y, z))` >>
    simp[mills_zig_def] >>
    qexists_tac `IMAGE (\p. (x,p)) (factor_pair ((n - x ** 2) DIV 4))` >>
    rpt strip_tac >| [
      `(n - x ** 2) DIV 4 <> 0` by metis_tac[windmill_yz_product, windmill_nonsquare] >>
      simp[factor_pair_def] >>
      simp[Abbr`foo`] >>
      imp_res_tac windmill_arm_divisors >>
      fs[LET_THM] >>
      metis_tac[],
      qexists_tac `x` >>
      simp[] >>
      simp[evens_to_def] >>
      metis_tac[windmill_mind_even]
    ],
    rename1 `t IN _` >>
    `?x y z. t = (x,y,z)` by simp[triple_parts] >>
    fs[mills_def] >>
    fs[mills_zig_def, factor_pair_def] >>
    rename1 `q IN _` >>
    `EVEN q /\ q <= SQRT n` by fs[evens_to_def] >>
    qabbrev_tac `k = (n - q ** 2) DIV 4` >>
    `0 < k` by simp[zig_sub_even_sq_div_4, Abbr`k`] >>
    fs[] >>
    `(n - q ** 2) MOD 4 = 0` by simp[zig_sub_even_sq_mod_4] >>
    `n - q ** 2 = k * 4` by metis_tac[DIVISION, ADD_0, DECIDE ``0 < 4``] >>
    `n = 4 * k + q ** 2` by decide_tac >>
    fs[divisors_def, windmill_def] >>
    simp[DIVIDES_FACTORS]
  ]
QED

(* This is a fantastic result! *)

(* Theorem: mills n = if zig n /\ ~square n then mills_zig n
                 else if zag n then {} else mills n *)
(* Proof:
   Note if (zig n) and ~square n,
        mills n = mills_zig n                           by mills_zig_eqn
    and if (zag n) and, then mills n = {}               by mills_zag_empty
*)
Theorem mills_even_eqn[compute]:
  !n. mills n = if zig n /\ ~square n then mills_zig n
                 else if zag n then {}
                 else mills n
Proof
  rw[mills_zig_eqn, mills_zag_empty]
QED
(* put in computeLib *)

(*
> EVAL ``mills 12``;
val it = |- mills 12 = {(2,2,1); (2,1,2); (0,3,1); (0,1,3)}: thm
> EVAL ``mills 20``;
val it = |- mills 20 = {(4,1,1); (2,4,1); (2,2,2); (2,1,4); (0,5,1); (0,1,5)}: thm
> EVAL ``mills 24``;
val it = |- mills 24 = {(4,2,1); (4,1,2); (2,5,1); (2,1,5); (0,6,1); (0,3,2); (0,2,3); (0,1,6)}: thm

> EVAL ``mills 40``;
val it = |- mills 40 =
      {(6,1,1); (4,6,1); (4,3,2); (4,2,3); (4,1,6); (2,9,1); (2,3,3);
       (2,1,9); (0,10,1); (0,5,2); (0,2,5); (0,1,10)}: thm
> EVAL ``mills 96``;
val it = |- mills 96 =
      {(8,8,1); (8,4,2); (8,2,4); (8,1,8); (6,15,1); (6,5,3); (6,3,5);
       (6,1,15); (4,20,1); (4,10,2); (4,5,4); (4,4,5); (4,2,10); (4,1,20);
       (2,23,1); (2,1,23); (0,24,1); (0,12,2); (0,8,3); (0,6,4); (0,4,6);
       (0,3,8); (0,2,12); (0,1,24)}: thm
*)

(* Theorem: zag n ==> CARD (mills n) = 0 *)
(* Proof:
   Since zag n, mills n = {}       by mills_zag_empty
   Thus CARD (mills n) = 0         by CARD_EMPTY
*)
Theorem mills_zag_card:
  !n. zag n ==> CARD (mills n) = 0
Proof
  rw[mills_zag_empty]
QED

(* Theorem: zig n /\ ~square n ==>
            CARD (mills n) = SIGMA (\x. CARD (divisors ((n - x ** 2) DIV 4))) (evens_to (SQRT n)) *)
(* Proof:
   Note mills n = mills_zig n                  by mills_zig_eqn
   Expand by mills_zig_def.
   Let s = evens_to (SQRT n),
       f = \x. IMAGE (\p. (x,p)) (factor_pair ((n - x ** 2) DIV 4)),
       P = IMAGE f s.

   Note FINITE s                               by evens_to_finite
    and FINITE P                               by IMAGE_FINITE
   Also EVERY_FINITE P                         by IMAGE_FINITE, factor_pair_def, divisors_finite

   Claim: PAIR_DISJOINT P
   Proof: By DISJOINT_ALT, this is to show:
          x IN s /\ u = IMAGE (\p. (x,p)) (factor_pair ((n - x ** 2) DIV 4)) /\
          y IN s /\ v = IMAGE (\p. (y,p)) (factor_pair ((n - y ** 2) DIV 4)) /\
          u <> v /\ z IN u /\ z IN v ==> F
          Note ?p. z = (x,p)                   by IN_IMAGE, z IN u
           and ?q. z = (y,q)                   by IN_IMAGE, z IN v
            so x = y                           by equating FST z
           ==> u = v, contradicts u <> v       [1]

   Claim: INJ f s univ(:num # num # num -> bool)
   Proof: By INJ_DEF, factor_pair_def, this is to show:
          x IN evens_to (SQRT n) /\
          y IN evens_to (SQRT n) /\
          IMAGE (\p. (x,p)) (IMAGE (\j. (j,k DIV j)) (divisors k)) =
          IMAGE (\p. (y,p)) (IMAGE (\j. (j,h DIV j)) (divisors h))
          ==> x = y, where k = (n - x ** 2) DIV 4, h = (n - y ** 2) DIV 4.
          Note 0 < k                           by zig_sub_even_sq_div_4, evens_to_def
            so 1 IN divisors k                 by divisors_has_1
          Thus (x,1,k) IN first IMAGE          by IN_IMAGE
            or (x,1,k) IN second IMAGE         by first IMAGE = second IMAGE
            so x = y                           by FST of second IMAGE, [2]

    Claim: !x. x IN s ==>
            (CARD o f) x = (\x. CARD (divisors ((n - x ** 2) DIV 4))) x
    Proof: Let k = (n - x ** 2) DIV 4,
               t = IMAGE (\j. (j,k DIV j)) (divisors k).
           By factor_pair_def, this is to show:
           CARD (IMAGE (\p. (x,p)) t) = CARD (divisors k)

            Now FINITE t                                   by IMAGE_FINITE, divisors_finite
            and INJ (\p. (x,p)) t univ(:num # num # num)   by INJ_DEF, FST
             so CARD (IMAGE (\p. (x,p)) t) = CARD t        by INJ_CARD_IMAGE_EQN

           Let f = \j. (j,k DIV j).
           Note FINITE (divisors k)                        by divisors_finite
            and INJ f (divisors k) univ(:num # num)        by INJ_DEF, FST
             so CARD t = CARD (divisors k)                 by INJ_CARD_IMAGE_EQN, [3]

       CARD (BIGUNION P)
     = SIGMA CARD P                                        by CARD_BIGUNION_PAIR_DISJOINT, [1]
     = SIGMA CARD (IMAGE f s)                              by above
     = SIGMA (CARD o f) s                                  by SUM_IMAGE_INJ_o, [2]
     = SIGMA (\x. CARD (divisors ((n - x ** 2) DIV 4))) s  by SIGMA_CONG, [3]
*)
Theorem mills_zig_card:
  !n. zig n /\ ~square n ==>
        CARD (mills n) = SIGMA (\x. CARD (divisors ((n - x ** 2) DIV 4))) (evens_to (SQRT n))
Proof
  rpt strip_tac >>
  imp_res_tac mills_zig_eqn >>
  fs[mills_zig_def] >>
  qabbrev_tac `s = evens_to (SQRT n)` >>
  qabbrev_tac `f = \x. IMAGE (\p. (x,p)) (factor_pair ((n - x ** 2) DIV 4))` >>
  qabbrev_tac `P = IMAGE f s` >>
  `FINITE s` by rw[evens_to_finite, Abbr`s`] >>
  `FINITE P` by fs[Abbr`P`] >>
  `EVERY_FINITE P` by
  (fs[Abbr`P`] >>
  rpt strip_tac >>
  fs[factor_pair_def, divisors_finite, Abbr`f`]) >>
  `PAIR_DISJOINT P` by
    (fs[DISJOINT_ALT, Abbr`P`] >>
  rpt strip_tac >>
  fs[Abbr`f`] >>
  `?p. x'' = (x,p)` by metis_tac[IN_IMAGE] >>
  `?q. x'' = (x',q)` by metis_tac[IN_IMAGE] >>
  `x = x'` by fs[] >>
  metis_tac[]) >>
  `INJ f s univ(:num # num # num -> bool)` by
      (rw[INJ_DEF, evens_to_def, factor_pair_def, Abbr`f`, Abbr`s`] >>
  qabbrev_tac `k = (n - x ** 2) DIV 4` >>
  qabbrev_tac `k' = (n - x' ** 2) DIV 4` >>
  `0 < k` by simp[zig_sub_even_sq_div_4, Abbr`k`] >>
  `0 < k'` by simp[zig_sub_even_sq_div_4, Abbr`k'`] >>
  fs[] >>
  `1 IN divisors k` by simp[divisors_has_1] >>
  `(x,1,k) IN IMAGE (\p. (x,p)) (IMAGE (\j. (j,k DIV j)) (divisors k))` by simp[] >>
  `(x,1,k) IN IMAGE (\p. (x',p)) (IMAGE (\j. (j,k' DIV j)) (divisors k'))` by metis_tac[] >>
  fs[]) >>
  imp_res_tac CARD_BIGUNION_PAIR_DISJOINT >>
  `_ = SIGMA CARD (IMAGE f s)` by simp[Abbr`P`] >>
  `_ = SIGMA (CARD o f) s` by simp[SUM_IMAGE_INJ_o] >>
  `SIGMA (CARD o f) s = SIGMA (\x. CARD (divisors ((n - x ** 2) DIV 4))) s` suffices_by simp[] >>
  irule SIGMA_CONG >>
  rw[evens_to_def, Abbr`s`] >>
  rw[factor_pair_def, Abbr`f`] >>
  qabbrev_tac `k = (n - x ** 2) DIV 4` >>
  qabbrev_tac `t = IMAGE (\j. (j,k DIV j)) (divisors k)` >>
  `FINITE t` by simp[divisors_finite, Abbr`t`] >>
  `INJ (\p. (x,p)) t univ(:num # num # num)` by rw[INJ_DEF, Abbr`t`] >>
  `CARD (IMAGE (\p. (x,p)) t) = CARD t` by rw[INJ_CARD_IMAGE_EQN] >>
  qabbrev_tac `f = \j. (j,k DIV j)` >>
  `CARD (IMAGE f (divisors k)) = CARD (divisors k)` suffices_by simp[Abbr`t`] >>
  `FINITE (divisors k)` by simp[divisors_finite] >>
  `INJ f (divisors k) univ(:num # num)` by rw[INJ_DEF, Abbr`f`] >>
  simp[INJ_CARD_IMAGE_EQN]
QED

(* This is really good! *)

(* Theorem: zig n /\ ~square n ==>
            CARD (mills n) <= SIGMA (\x. 2 * SQRT ((n - x ** 2) DIV 4)) (evens_to (SQRT n)) *)
(* Proof:
   Let s = evens_to (SQRT n),
       f = \x. CARD (divisors ((n - x ** 2) DIV 4)),
       g = \x. 2 * SQRT ((n - x ** 2) DIV 4).
   Then CARD (mills n) =  SIGMA f s            by mills_zig_card
    and FINITE s                               by evens_to_finite

   Claim: !x. x IN s ==> f x <= g x
   Proof: Let k = (n - x ** 2) DIV 4.
          This is to show:
          x IN s ==> CARD (divisors k) <= 2 * SQRT k
          which is true                        by divisors_card_upper, [1]

   Therefore, CARD (mills n) <= SIGMA f s      by SIGMA_LE_SIGMA, [1]
*)
Theorem mills_zig_card_upper_thm:
  !n. zig n /\ ~square n ==>
        CARD (mills n) <= SIGMA (\x. 2 * SQRT ((n - x ** 2) DIV 4)) (evens_to (SQRT n))
Proof
  rpt strip_tac >>
  imp_res_tac mills_zig_card >>
  qabbrev_tac `s = evens_to (SQRT n)` >>
  qabbrev_tac `f = \x. CARD (divisors ((n - x ** 2) DIV 4))` >>
  qabbrev_tac `g = \x. 2 * SQRT ((n - x ** 2) DIV 4)` >>
  `FINITE s` by simp[evens_to_finite, Abbr`s`] >>
  `!x. x IN s ==> f x <= g x` by simp[divisors_card_upper, Abbr`f`, Abbr`g`] >>
  simp[SIGMA_LE_SIGMA]
QED

(* Theorem: zig n /\ ~square n ==>
            CARD (mills n) <= 2 * SQRT (n DIV 4) * HALF (2 + SQRT n) *)
(* Proof:
   Let s = evens_to (SQRT n),
       f = \x. 2 * SQRT ((n - x ** 2) DIV 4),
       k = 2 * SQRT (n DIV 4),
       g = \x. k.
   Then FINITE s                               by evens_to_finite
    and CARD (mills n) <= SIGMA f s            by mills_zig_card_upper_thm

   Claim: !x. x IN s ==> f x <= g x
   Proof: Let h = (n - x ** 2) DIV 4.
          Note n - x ** 2 <= n                 by arithmetic
           ==>      h <= n DIV 4               by DIV_LE_MONOTONE
           ==> SQRT h <= SQRT (n DIV 4)        by SQRT_LE
           ==>    f x <= g x                   by LE_MULT_LCANCEL, [1]

    Note !x. x IN s ==> g x = k                by function g

    CARD (mills n) <= SIGMA f s                by above
                   <= SIGMA g s                by SIGMA_LE_SIGMA, [1]
                    = k * CARD s               by SIGMA_CONSTANT
                    = k * (HALF (2 + SQRT n))  by evens_to_card
*)
Theorem mills_zig_card_upper_tight:
  !n. zig n /\ ~square n ==>
        CARD (mills n) <= 2 * SQRT (n DIV 4) * HALF (2 + SQRT n)
Proof
  rpt strip_tac >>
  imp_res_tac mills_zig_card_upper_thm >>
  qabbrev_tac `s = evens_to (SQRT n)` >>
  qabbrev_tac `k = 2 * SQRT (n DIV 4)` >>
  qabbrev_tac `f = \x. 2 * SQRT ((n - x ** 2) DIV 4)` >>
  qabbrev_tac `g = \x:num. k` >>
  `!x. x IN s ==> f x <= g x` by
  (rw[evens_to_def, Abbr`f`, Abbr`g`, Abbr`s`] >>
  `n - x ** 2 <= n` by decide_tac >>
  qabbrev_tac `h = (n - x ** 2) DIV 4` >>
  `h <= n DIV 4` by simp[DIV_LE_MONOTONE, Abbr`h`] >>
  `SQRT h <= SQRT (n DIV 4)` by simp[SQRT_LE] >>
  simp[Abbr`k`]) >>
  `FINITE s` by simp[evens_to_finite, Abbr`s`] >>
  `SIGMA f s <= SIGMA g s` by simp[SIGMA_LE_SIGMA] >>
  `!x. x IN s ==> g x = k` by simp[Abbr`g`] >>
  `SIGMA g s = k * CARD s` by simp[SIGMA_CONSTANT] >>
  `CARD s = HALF (2 + SQRT n)` by simp[evens_to_card, Abbr`s`] >>
  fs[]
QED


(* Theorem: zig n /\ ~square n ==> CARD (mills n) <= n *)
(* Proof:
   Let k = n DIV 4.
   Note 2 * SQRT k <= SQRT (4 * k)                 by SQRT_MULT_LE, 4 = 2 ** 2
   Also square 0                                   by square_0
   Thus SQRT n <> 0                                by SQRT_EQ_0, ~square n
     so HALF (1 + SQRT n) <= SQRT n                by HALF_SUC_SUC, 0 < SQRT n

        CARD (mills n)
     <= 2 * SQRT k * HALF (2 + SQRT n)             by mills_zig_card_upper_tight
     <= SQRT (4 * k) * SQRT n                      by LE_MONO_MULT2
      = SQRT n * SQRT n                            by n = 4 * k
     <= n                                          by SQ_SQRT_LE
*)
Theorem mills_zig_card_upper:
  !n. zig n /\ ~square n ==> CARD (mills n) <= n
Proof
  rpt strip_tac >>
  imp_res_tac mills_zig_card_upper_tight >>
  qabbrev_tac `k = n DIV 4` >>
  `2 * SQRT k <= SQRT n` by
  (`2 ** 2 = 4` by simp[] >>
  `2 = SQRT 4` by metis_tac[SQRT_OF_SQ] >>
  `2 * SQRT k <= SQRT (4 * k)` by metis_tac[SQRT_MULT_LE] >>
  `n = 4 * k` by metis_tac[DIVISION, MULT_COMM, ADD_0, DECIDE ``0 < 4``] >>
  `4 * k <= n` by decide_tac >>
  `SQRT (4 * k) <= SQRT n` by simp[SQRT_LE] >>
  decide_tac) >>
  `square 0` by simp[square_0] >>
  `SQRT n <> 0` by metis_tac[SQRT_EQ_0] >>
  `SUC (SUC (SQRT n)) = 2 + SQRT n` by decide_tac >>
  `HALF (2 + SQRT n) <= SQRT n` by metis_tac[HALF_SUC_SUC, NOT_ZERO] >>
  `2 * SQRT k * HALF (2 + SQRT n) <= SQRT n * SQRT n` by simp[LE_MONO_MULT2] >>
  `SQRT n * SQRT n <= n` by simp[SQ_SQRT_LE] >>
  decide_tac
QED

(* Not a tight bound, but a clean result. *)

(* ------------------------------------------------------------------------- *)
(* Windmills for squares.                                                    *)
(* ------------------------------------------------------------------------- *)

(* The infinite portion of trivial windmills for squares. *)

(* Define the set of square windmills, without arms. *)
Definition mills_square_def[nocompute]:
    mills_square n = {(x,y,z) | n = windmill (x, y, z) /\ y * z = 0}
End
(* use [nocompute] as this is not effective. *)

(* Theorem: (x, y, z) IN mills_square n <=> n = windmill (x, y, z) /\ (y = 0 \/ z = 0) *)
(* Proof: by mills_square_def, MULT_EQ_0. *)
Theorem mills_square_element:
  !n x y z. (x, y, z) IN mills_square n <=> n = windmill (x, y, z) /\ (y = 0 \/ z = 0)
Proof
  simp[mills_square_def]
QED

(* Theorem: tik n /\ square n ==> mills n = (mills_tik n) UNION (mills_square n) *)
(* Proof:
   If part: t IN mills n ==> t IN (mills_tik n) or t IN (mills_square n)
      Note ?x y z. t = (x,y,z)                 by triple_parts
       and n = windmill (x, y, z)                  by windmill_def
      The goal is: (x,y,z) IN mills_tik n \/ (x,y,z) IN mills_square n
      If y = 0 \/ z = 0,
         Then (x,y,z) IN mills_square n        by mills_square_def
      If ~(y = 0 \/ z = 0),
         By mills_tik_def, this is to show:
         ?s. (x,y,z) IN s /\
         ?q. s = IMAGE (\p. (q,p)) (factor_pair ((n - q ** 2) DIV 4)) /\
             q IN odds_to (SQRT n)
         Let k = (n - x ** 2) DIV 4,
             s = IMAGE (\p. (x,p)) (factor_pair k).
         Note 0 < k                            by windmill_yz_eq_0, ~(y = 0 \/ z = 0)
         By factor_pair_def, this is to show:
              z = k DIV y /\ y IN divisors k
         But y * z = k                         by windmill_yz_product
         and 0 < y                             by MULT_EQ_0, 0 < k
          so z = k DIV y                       by DIV_SOLVE_COMM, 0 < y
         and y divides k                       by factor_divides
          so y IN divisors k                   by divisors_element_alt, 0 < k

         Next, let q = x.
         By odds_to_def, this is to show:
            ODD x /\ x <= SQRT n, true         by windmill_mind_odd

   Only-if part: t IN (mills_tik n) or t IN (mills_square n) ==> t IN mills n
      Note ?x y z. t = (x,y,z)                 by triple_parts
      If (x,y,z) IN (mills_tik n),
         Let k = (n - x ** 2) DIV 4).
         Then (x,y,z) IN s = IMAGE (\p. (x,p)) (factor_pair k)
          and x IN odds_to (SQRT n)            by mills_tik_def
        By mills_def, this is to show:
           n = windmill (x, y, z)
        Note (y,z) IN factor_pair k            by IN_IMAGE
          so factor_pair k <> {}               by MEMBER_NOT_EMPTY
         ==> 0 < k                             by factor_pair_empty, NOT_ZERO
        Thus y * z = k                         by factor_pair_nonzero_element, 0 < k
         and ODD x /\ x <= SQRT n              by odds_to_def
         Now (n - x ** 2) MOD 4 = 0            by tik_sub_odd_sq_mod_4
          so n - x ** 2 = 4 * k                by DIVISION, ADD_0
          or n = x ** 2 + 4 * y * z            by arithmetic
         ==> n = windmill (x, y, z)                by windmill_def
     If (x,y,z) IN (mills_square n),
        Then n = windmill (x, y, z) /\ y * z = 0   by mills_square_def
         ==> (x,y,z) IN mills n                by mills_def
*)
Theorem mills_tik_square_eqn:
  !n. tik n /\ square n ==> mills n = (mills_tik n) UNION (mills_square n)
Proof
  rw[EXTENSION, EQ_IMP_THM] >| [
    rename1 `t IN _` >>
    fs[mills_def] >>
    qabbrev_tac `foo = (n = windmill (x, y, z))` >>
    `(x,y,z) IN mills_tik n \/ (x,y,z) IN mills_square n` suffices_by metis_tac[] >>
    simp[mills_tik_def, mills_square_def] >>
    (Cases_on `y = 0 \/ z = 0` >> simp[]) >>
    qexists_tac `IMAGE (\p. (x,p)) (factor_pair ((n - x ** 2) DIV 4))` >>
    rpt strip_tac >| [
      qabbrev_tac `k = (n - x ** 2) DIV 4` >>
      `0 < k` by metis_tac[windmill_yz_eq_0, NOT_ZERO] >>
      simp[factor_pair_def] >>
      `y * z = k` by simp[windmill_yz_product, Abbr`k`] >>
      `0 < y` by metis_tac[MULT_EQ_0, NOT_ZERO] >>
      `z = k DIV y` by fs[DIV_SOLVE_COMM] >>
      metis_tac[divisors_element_alt, factor_divides],
      qexists_tac `x` >>
      simp[odds_to_def] >>
      metis_tac[windmill_mind_odd]
    ],
    rename1 `t IN _` >>
    fs[mills_tik_def] >>
    qabbrev_tac `k = (n - x ** 2) DIV 4` >>
    simp[mills_def] >>
    rename1 `q IN _` >>
    `?x y z. t = (x, y, z)` by simp[triple_parts] >>
    map_every qexists_tac [`x`, `y`, `z`] >>
    simp[] >>
    `q = x /\ (y,z) IN factor_pair k` by fs[] >>
    `0 < k` by metis_tac[factor_pair_empty, NOT_ZERO, MEMBER_NOT_EMPTY] >>
    `y * z = k` by fs[factor_pair_nonzero_element, Abbr`k`] >>
    fs[odds_to_def] >>
    `(n - x ** 2) MOD 4 = 0` by simp[tik_sub_odd_sq_mod_4] >>
    `n - x ** 2 = 4 * k` by metis_tac[DIVISION, MULT_COMM, ADD_0, DECIDE``0 < 4``] >>
    simp[windmill_def],
    fs[mills_square_def, mills_def]
  ]
QED

(* Theorem: zig n /\ square n ==> mills n = (mills_zig n) UNION (mills_square n) *)
(* Proof:
   If part: t IN mills n ==> t IN (mills_zig n) or t IN (mills_square n)
      Note ?x y z. t = (x,y,z)                 by triple_parts
       and n = windmill (x, y, z)                  by windmill_def
      The goal is: (x,y,z) IN mills_tik n \/ (x,y,z) IN mills_square n
      If y = 0 \/ z = 0,
         Then (x,y,z) IN mills_square n        by mills_square_def
      If ~(y = 0 \/ z = 0),
         By mills_zig_def, this is to show:
         ?s. (x,y,z) IN s /\
         ?q. s = IMAGE (\p. (q,p)) (factor_pair ((n - q ** 2) DIV 4)) /\
             q IN evens_to (SQRT n)
         Let k = (n - x ** 2) DIV 4,
             s = IMAGE (\p. (x,p)) (factor_pair k).
         Note 0 < k                            by windmill_yz_eq_0, ~(y = 0 \/ z = 0)
         By factor_pair_def, this is to show:
              z = k DIV y /\ y IN divisors k
         But y * z = k                         by windmill_yz_product
         and 0 < y                             by MULT_EQ_0, 0 < k
          so z = k DIV y                       by DIV_SOLVE_COMM, 0 < y
         and y divides k                       by factor_divides
          so y IN divisors k                   by divisors_element_alt, 0 < k

         Next, let q = x.
         By evens_to_def, this is to show:
            EVEN x /\ x <= SQRT n, true         by windmill_mind_even

   Only-if part: t IN (mills_zig n) or t IN (mills_square n) ==> t IN mills n
      Note ?x y z. t = (x,y,z)                 by triple_parts
      If (x,y,z) IN (mills_tik n),
         Let k = (n - x ** 2) DIV 4).
         Then (x,y,z) IN s = IMAGE (\p. (x,p)) (factor_pair k)
          and x IN evens_to (SQRT n)           by mills_zig_def
        By mills_def, this is to show:
           n = windmill (x, y, z)
        Note (y,z) IN factor_pair k            by IN_IMAGE
          so factor_pair k <> {}               by MEMBER_NOT_EMPTY
         ==> 0 < k                             by factor_pair_empty, NOT_ZERO
        Thus y * z = k                         by factor_pair_nonzero_element, 0 < k
         and EVEN x /\ x <= SQRT n             by evens_to_def
         Now (n - x ** 2) MOD 4 = 0            by zig_sub_even_sq_mod_4
          so n - x ** 2 = 4 * k                by DIVISION, ADD_0
          or n = x ** 2 + 4 * y * z            by arithmetic
         ==> n = windmill (x, y, z)                by windmill_def
     If (x,y,z) IN (mills_square n),
        Then n = windmill (x, y, z) /\ y * z = 0   by mills_square_def
         ==> (x,y,z) IN mills n                by mills_def
*)
Theorem mills_zig_square_eqn:
  !n. zig n /\ square n ==> mills n = (mills_zig n) UNION (mills_square n)
Proof
  rw[EXTENSION, EQ_IMP_THM] >| [
    rename1 `t IN _` >>
    fs[mills_def] >>
    qabbrev_tac `foo = (n = windmill (x, y, z))` >>
    `(x,y,z) IN mills_zig n \/ (x,y,z) IN mills_square n` suffices_by metis_tac[] >>
    simp[mills_zig_def, mills_square_def] >>
    (Cases_on `y = 0 \/ z = 0` >> simp[]) >>
    qexists_tac `IMAGE (\p. (x,p)) (factor_pair ((n - x ** 2) DIV 4))` >>
    rpt strip_tac >| [
      qabbrev_tac `k = (n - x ** 2) DIV 4` >>
      `0 < k` by metis_tac[windmill_yz_eq_0, NOT_ZERO] >>
      simp[factor_pair_def] >>
      `y * z = k` by simp[windmill_yz_product, Abbr`k`] >>
      `0 < y` by metis_tac[MULT_EQ_0, NOT_ZERO] >>
      `z = k DIV y` by fs[DIV_SOLVE_COMM] >>
      metis_tac[divisors_element_alt, factor_divides],
      qexists_tac `x` >>
      simp[evens_to_def] >>
      metis_tac[windmill_mind_even]
    ],
    rename1 `t IN _` >>
    fs[mills_zig_def] >>
    qabbrev_tac `k = (n - x ** 2) DIV 4` >>
    simp[mills_def] >>
    rename1 `q IN _` >>
    `?x y z. t = (x, y, z)` by simp[triple_parts] >>
    map_every qexists_tac [`x`, `y`, `z`] >>
    simp[] >>
    `q = x /\ (y,z) IN factor_pair k` by fs[] >>
    `0 < k` by metis_tac[factor_pair_empty, NOT_ZERO, MEMBER_NOT_EMPTY] >>
    `y * z = k` by fs[factor_pair_nonzero_element, Abbr`k`] >>
    fs[evens_to_def] >>
    `(n - x ** 2) MOD 4 = 0` by simp[zig_sub_even_sq_mod_4] >>
    `n - x ** 2 = 4 * k` by metis_tac[DIVISION, MULT_COMM, ADD_0, DECIDE``0 < 4``] >>
    simp[windmill_def],
    fs[mills_square_def, mills_def]
  ]
QED

(* Theorem: (mills_tik n) INTER (mills_square n) = {} *)
(* Proof:
   By EXTENSION, this is to show:
      t IN mills_tik n /\ t IN mills_square n ==> F.
   Let t = (x,y,z)                             by triple_parts
   Then n = windmill (x, y, z) /\ y * z = 0        by mills_square_def
     so n = x ** 2 + 4 * y * z = x ** 2        by windmill_def
   Let k = (n - x ** 2) DIV 4, then k = 0      by above
   By mills_tik_def, t IN mills_tik n
   ==> ?q. t IN IMAGE (\p. (q,p)) (factor_pair ((n - q * q) DIV 4)) /\
           q IN odds_to (SQRT n).
    so q = x                                   by comparing FST
   and (y,z) IN factor_pair k                  by comparing SND, above
   But k = 0, so factor_pair k = {}            by factor_pair_empty
   This is a contradiction                     by MEMBER_NOT_EMPTY
*)
Theorem mills_tik_not_mills_square:
  !n. (mills_tik n) INTER (mills_square n) = {}
Proof
  rw[EXTENSION, mills_square_def] >>
  spose_not_then strip_assume_tac >>
  rename1 `t IN _` >>
  rename1 `t = (x,_,_)` >>
  `n = x ** 2` by simp[windmill_def] >>
  qabbrev_tac `foo = (n = windmill (x, y, z))` >>
  qabbrev_tac `goo = (n = x ** 2)` >>
  fs[mills_tik_def] >>
  rename1 `q IN _` >>
  `q = x /\ (y,z) IN factor_pair ((n - x ** 2) DIV 4)` by fs[] >>
  `(n - x ** 2) DIV 4 = 0` by simp[Abbr`goo`] >>
  metis_tac[factor_pair_empty, MEMBER_NOT_EMPTY]
QED

(* Theorem: (mills_zig n) INTER (mills_square n) = {} *)
(* Proof:
   By EXTENSION, this is to show:
      t IN mills_zig n /\ t IN mills_square n ==> F.
   Let t = (x,y,z)                             by triple_parts
   Then n = windmill (x, y, z) /\ y * z = 0        by mills_square_def
     so n = x ** 2 + 4 * y * z = x ** 2        by windmill_def
   Let k = (n - x ** 2) DIV 4, then k = 0      by above
   By mills_zig_def, t IN mills_zig n
   ==> ?q. t IN IMAGE (\p. (q,p)) (factor_pair ((n - q * q) DIV 4)) /\
           q IN evens_to (SQRT n).
    so q = x                                   by comparing FST
   and (y,z) IN factor_pair k                  by comparing SND, above
   But k = 0, so factor_pair k = {}            by factor_pair_empty
   This is a contradiction                     by MEMBER_NOT_EMPTY
*)
Theorem mills_zig_not_mills_square:
  !n. (mills_zig n) INTER (mills_square n) = {}
Proof
  rw[EXTENSION, mills_square_def] >>
  spose_not_then strip_assume_tac >>
  rename1 `t IN _` >>
  rename1 `t = (x,_,_)` >>
  `n = x ** 2` by simp[windmill_def] >>
  qabbrev_tac `foo = (n = windmill (x, y, z))` >>
  qabbrev_tac `goo = (n = x ** 2)` >>
  fs[mills_zig_def] >>
  rename1 `q IN _` >>
  `q = x /\ (y,z) IN factor_pair ((n - x ** 2) DIV 4)` by fs[] >>
  `(n - x ** 2) DIV 4 = 0` by simp[Abbr`goo`] >>
  metis_tac[factor_pair_empty, MEMBER_NOT_EMPTY]
QED

(* ------------------------------------------------------------------------- *)
(* Computation of (mills n) in general.                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: mills n = if (square n) then mills n
                      else if zig n then mills_zig n
                      else if tik n then mills_tik n else {} *)
(* Proof:
   When ~square n,
   tik n ==> mills n = mills_tik n             by mills_tik_eqn
   zig n ==> mills n = mills_zig n             by mills_zig_eqn
   Otherwise zag n \/ tok n                    by quarity_cases
   zag n ==> mills n = {}                      by mills_zag_empty
   tok n ==> mills n = {}                      by mills_tok_empty
*)
Theorem mills_eqn[compute]:
  !n. mills n = if (square n) then mills n
                 else if zig n then mills_zig n
                 else if tik n then mills_tik n
                 else {}
Proof
  rw[mills_zig_eqn, mills_tik_eqn] >>
  metis_tac[quarity_cases, mills_zag_empty, mills_tok_empty]
QED
(* put in computeLib *)

(* Theorem: ~square n ==> CARD (mills n) <= n *)
(* Proof:
   By mills_eqn, for ~square n,
   tik n ==> CARD (mills n) <= n               by mills_tik_card_upper
   zig n ==> CARD (mills n) <= n               by mills_zig_card_upper
   Otherwise,
             CARD (mills n)
           = CARD {} = 0 <= n                  by CARD_EMPTY
*)
Theorem mills_card_upper:
  !n. ~square n ==> CARD (mills n) <= n
Proof
  rpt strip_tac >>
  `0 <= n` by decide_tac >>
  metis_tac[mills_eqn, mills_tik_card_upper, mills_zig_card_upper, CARD_EMPTY]
QED

(* ------------------------------------------------------------------------- *)
(* Search for Sum of Squares                                                 *)
(* ------------------------------------------------------------------------- *)

(*
> EVAL ``let n = 65 in BIGUNION (IMAGE (\x. let m = n - x * x; k = SQRT m in if k * k = m then {(x, k); (k, x)} else {}) (odds_to (SQRT n)))``; = {(7,4); (4,7); (1,8); (8,1)}

> EVAL ``let n = 58 in BIGUNION (IMAGE (\x. let m = n - x * x; k = SQRT m in if k * k = m then {(x, k); (k, x)} else {}) (odds_to (SQRT n)))``; = {(3,7); (7,3)}

> EVAL ``let n = 20 in BIGUNION (IMAGE (\x. let m = n - x * x; k = SQRT m in if k * k = m then {(x, k); (k, x)} else {}) (evens_to (SQRT n)))``; = {(2,4); (4,2)}

> EVAL ``let n = 25 in BIGUNION (IMAGE (\x. let m = n - x * x; k = SQRT m in if k * k = m then {(x, k); (k, x)} else {}) (odds_to (SQRT n)))``; = {(5,0); (0,5); (3,4); (4,3)}


> EVAL ``let n = 65 in BIGUNION (IMAGE (\x. let m = n - x * x; y = SQRT m in if y * y = m then {(x, y)} else {}) (upto (SQRT n)))``; = {(8,1); (7,4); (4,7); (1,8)}
> EVAL ``let n = 25 in BIGUNION (IMAGE (\x. let m = n - x * x; y = SQRT m in if y * y = m then {(x, y)} else {}) (upto (SQRT n)))``; = {(5,0); (4,3); (3,4); (0,5)}
> EVAL ``let n = 25 in BIGUNION (IMAGE (\x. let m = n - x * x; y = SQRT m in if y * y = m then {(x, y)} else {}) (upto (SQRT n)))``; = {(5,0); (4,3); (3,4); (0,5)}
> EVAL ``let n = 100 in BIGUNION (IMAGE (\x. let m = n - x * x; y = SQRT m in if y * y = m then {(x, y)} else {}) (upto (SQRT n)))``; = {(10,0); (8,6); (6,8); (0,10)}

*)

(* Define the set of pairs for sum of two squares for n. *)
Definition two_sq_sum_def[nocompute]:
    two_sq_sum n = {(x, y) | n = x ** 2 + y ** 2}
End
(* use [nocompute] as this is not effective. *)

(* Theorem: (x,y) IN two_sq_sum n <=> n = x ** 2 + y ** 2 *)
(* Proof: by two_sq_sum_def.*)
Theorem two_sq_sum_element:
  !n x y. (x,y) IN two_sq_sum n <=> n = x ** 2 + y ** 2
Proof
  simp[two_sq_sum_def]
QED

(* Theorem: two_sq_sum n SUBSET (count (1 + SQRT n)) CROSS (count (1 + SQRT n)) *)
(* Proof:
   By SUBSET_DEF, this is to show:
      p IN two_sq_sum n ==> p IN (count (1 + SQRT n)) CROSS (count (1 + SQRT n))
   Note p = (x,y) where n = x ** 2 + y ** 2    by two_sq_sum_def
     so x ** 2 <= n /\ y ** 2 <= n             by inequalities
    ==> x <= SQRT n /\ y <= SQRT n             by SQRT_OF_SQ, SQRT_LE
     or x < 1 + SQRT n /\ y < 1 + SQRT n       by LT_SUC_LE
     or (x,y) IN (count (1 + SQRT n)) CROSS (count (1 + SQRT n))
                                               by IN_COUNT, IN_CROSS
*)
Theorem two_sq_sum_subset:
  !n. two_sq_sum n SUBSET (count (1 + SQRT n)) CROSS (count (1 + SQRT n))
Proof
  rw_tac std_ss[SUBSET_DEF] >>
  rename1 `p IN _` >>
  fs[two_sq_sum_def] >>
  qabbrev_tac `k = SQRT n` >>
  `x <= k /\ y <= k` suffices_by metis_tac[LT_SUC_LE, ADD1] >>
  `x ** 2 <= n /\ y ** 2 <= n` by decide_tac >>
  metis_tac[SQRT_OF_SQ, SQRT_LE]
QED

(* Theorem: FINITE (two_sq_sum n) *)
(* Proof:
   Let s = count (1 + SQRT n).
   Note two_sq_sum n SUBSET s CROSS s          by two_sq_sum_subset
     so FINITE s                               by FINITE_COUNT
    and FINITE (s CROSS s)                     by FINITE_CROSS
    ==> FINITE (two_sq_sum n)                  by SUBSET_FINITE
*)
Theorem two_sq_sum_finite:
  !n. FINITE (two_sq_sum n)
Proof
  metis_tac[two_sq_sum_subset, SUBSET_FINITE, FINITE_CROSS, FINITE_COUNT]
QED

(* Theorem: tik n ==> two_sq_sum n = BIGUNION (IMAGE
            (\x. let m = n - x * x; y = SQRT m in if y * y = m then {(x, y); (y, x)} else {})
            (odds_to (SQRT n))) *)
(* Proof:
   Let f = \x. let m = n - x * x; y = SQRT m in if y * y = m then {(x, y); (y, x)} else {}.
   The goal is: two_sq_sum n = BIGUNION (IMAGE f (upto (SQRT n)))
   By EXTENSION, this is to show:
   (1) p IN two_sq_sum ==> p IN BIGUNION (IMAGE f (odds_to (SQRT n)))
       By two_sq_sum_def, IN_BIGUNION, this is to show:
       p = (x,y) /\  n = x ** 2 + y ** 2 ==>
       ?s. (x,y) IN s /\ ?z. s = f z /\ z < SUC (SQRT n)
       Let s = {(x,y)}.
       Then (x,y) IN s is true                 by IN_SING
       Let z = x.
       Then m = n - x * x = n - x ** 2         by EXP_2
              = y ** 2                         by n = x ** 2 + y **2
         so y = SQRT m                         by SQRT_OF_SQ
       thus f z = f x = {(x,y)} = s.
        and x ** 2 <= n                        by arithmetic
         so      x <= SQRT n                   by SQRT_OF_SQ, SQRT_LE
         or      x < SUC (SQRT n)              by LESS_EQ_IMP_LESS_SUC
   (2) p IN BIGUNION (IMAGE f (odds_to (SQRT n))) ==> p IN two_sq_sum
       By IN_BIGUNION, two_sq_sum_def, this is to show:
          p IN s /\ s = f x /\ x < SUC (SQRT n)
          ==> ?x y. p = (x,y) /\ n = x ** 2 + y ** 2
       Note s = f x <> {}                      by MEMBER_NOT_EMPTY
         so y = SQRT m /\ y * y = m            by function f
         or y ** 2 = n - x ** 2                by EXP_2
        Now x < SUC (SQRT n)
        ==> x <= SQRT n                        by inequality
         so x ** 2 <= (SQRT n) ** 2 <= n       by EXP_EXP_LE_MONO, SQRT_PROPERTY
        ==> n = x ** 2 + y ** 2                by arithmetic
      Pick these x, y for p = (x,y).
*)
Theorem two_sq_sum_eqn[compute]:
  !n. two_sq_sum n =
        BIGUNION (IMAGE
           (\x. let m = n - x * x; y = SQRT m in if y * y = m then {(x, y)} else {})
           (upto (SQRT n)))
Proof
  rpt strip_tac >>
  qabbrev_tac `f = \x. let m = n - x * x; y = SQRT m in if y * y = m then {(x, y)} else {}` >>
  rw_tac std_ss[EXTENSION, EQ_IMP_THM] >| [
    rename1 `p IN _` >>
    fs[two_sq_sum_def] >>
    qexists_tac `{(x,y)}` >>
    simp[] >>
    qexists_tac `x` >>
    rfs[SQRT_OF_SQ, Abbr`f`] >>
    `x ** 2 <= n` by decide_tac >>
    `x <= SQRT n` by metis_tac[SQRT_OF_SQ, SQRT_LE] >>
    rfs[],
    rename1 `p IN _` >>
    fs[two_sq_sum_def, Abbr`f`] >>
    qabbrev_tac `y = SQRT (n - x ** 2)` >>
    `s = {(x,y)} /\ y ** 2 = n - x ** 2` by metis_tac[MEMBER_NOT_EMPTY] >>
    map_every qexists_tac [`x`, `y`] >>
    `x <= SQRT n` by decide_tac >>
    `x ** 2 <= (SQRT n) ** 2` by fs[] >>
    `(SQRT n) ** 2 <= n` by simp[SQRT_PROPERTY] >>
    `n = x ** 2 + y ** 2` by decide_tac >>
    fs[]
  ]
QED
(* put in computeLib *)

(*
> EVAL ``two_sq_sum 64``;
val it = |- two_sq_sum 64 = {(8,0); (0,8)}: thm
> EVAL ``two_sq_sum 65``;
val it = |- two_sq_sum 65 = {(8,1); (7,4); (4,7); (1,8)}: thm
> EVAL ``two_sq_sum 66``;
val it = |- two_sq_sum 66 = {}: thm
> EVAL ``two_sq_sum 67``;
val it = |- two_sq_sum 67 = {}: thm
> EVAL ``two_sq_sum 68``;
val it = |- two_sq_sum 68 = {(8,2); (2,8)}: thm
> EVAL ``two_sq_sum 69``;
val it = |- two_sq_sum 69 = {}: thm
> EVAL ``two_sq_sum 70``;
val it = |- two_sq_sum 70 = {}: thm
> EVAL ``two_sq_sum 71``;
val it = |- two_sq_sum 71 = {}: thm
> EVAL ``two_sq_sum 72``;
val it = |- two_sq_sum 72 = {(6,6)}: thm
*)

(* Theorem: tok n ==> two_sq_sum n = {} *)
(* Proof:
   By contradiction, suppose two_sq_sum n <> {}.
   Then ?(x,y). n = x ** 2 + y ** 2            by MEMBER_NOT_EMPTY, two_sq_sum_def
   This is a contradiction                     by tok_not_sum_of_squares
*)
Theorem two_sq_sum_tok:
  !n. tok n ==> two_sq_sum n = {}
Proof
  rw[EXTENSION, two_sq_sum_def, tok_not_sum_of_squares]
QED



(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
