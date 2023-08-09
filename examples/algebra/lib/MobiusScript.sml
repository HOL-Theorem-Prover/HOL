(* ------------------------------------------------------------------------- *)
(* Mobius Function and Inversion.                                            *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "Mobius";

(* ------------------------------------------------------------------------- *)



open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory;
open prim_recTheory arithmeticTheory dividesTheory gcdTheory;

open helperNumTheory helperSetTheory helperListTheory;

open GaussTheory;
open EulerTheory;


(* ------------------------------------------------------------------------- *)
(* Mobius Function and Inversion Documentation                               *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   sq_free s          = {n | n IN s /\ square_free n}
   non_sq_free s      = {n | n IN s /\ ~(square_free n)}
   even_sq_free s     = {n | n IN (sq_free s) /\ EVEN (CARD (prime_factors n))}
   odd_sq_free s      = {n | n IN (sq_free s) /\ ODD (CARD (prime_factors n))}
   less_divisors n    = {x | x IN (divisors n) /\ x <> n}
   proper_divisors n  = {x | x IN (divisors n) /\ x <> 1 /\ x <> n}
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Square-free Number and Square-free Sets:
   square_free_def     |- !n. square_free n <=> !p. prime p /\ p divides n ==> ~(p * p divides n)
   square_free_1       |- square_free 1
   square_free_prime   |- !n. prime n ==> square_free n

   sq_free_element     |- !s n. n IN sq_free s <=> n IN s /\ square_free n
   sq_free_subset      |- !s. sq_free s SUBSET s
   sq_free_finite      |- !s. FINITE s ==> FINITE (sq_free s)
   non_sq_free_element |- !s n. n IN non_sq_free s <=> n IN s /\ ~square_free n
   non_sq_free_subset  |- !s. non_sq_free s SUBSET s
   non_sq_free_finite  |- !s. FINITE s ==> FINITE (non_sq_free s)
   sq_free_split       |- !s. (s = sq_free s UNION non_sq_free s) /\
                              (sq_free s INTER non_sq_free s = {})
   sq_free_union       |- !s. s = sq_free s UNION non_sq_free s
   sq_free_inter       |- !s. sq_free s INTER non_sq_free s = {}
   sq_free_disjoint    |- !s. DISJOINT (sq_free s) (non_sq_free s)

   Prime Divisors of a Number and Partitions of Square-free Set:
   prime_factors_def      |- !n. prime_factors n = {p | prime p /\ p IN divisors n}
   prime_factors_element  |- !n p. p IN prime_factors n <=> prime p /\ p <= n /\ p divides n
   prime_factors_subset   |- !n. prime_factors n SUBSET divisors n
   prime_factors_finite   |- !n. FINITE (prime_factors n)

   even_sq_free_element    |- !s n. n IN even_sq_free s <=> n IN s /\ square_free n /\ EVEN (CARD (prime_factors n))
   even_sq_free_subset     |- !s. even_sq_free s SUBSET s
   even_sq_free_finite     |- !s. FINITE s ==> FINITE (even_sq_free s)
   odd_sq_free_element     |- !s n. n IN odd_sq_free s <=> n IN s /\ square_free n /\ ODD (CARD (prime_factors n))
   odd_sq_free_subset      |- !s. odd_sq_free s SUBSET s
   odd_sq_free_finite      |- !s. FINITE s ==> FINITE (odd_sq_free s)
   sq_free_split_even_odd  |- !s. (sq_free s = even_sq_free s UNION odd_sq_free s) /\
                                  (even_sq_free s INTER odd_sq_free s = {})
   sq_free_union_even_odd  |- !s. sq_free s = even_sq_free s UNION odd_sq_free s
   sq_free_inter_even_odd  |- !s. even_sq_free s INTER odd_sq_free s = {}
   sq_free_disjoint_even_odd  |- !s. DISJOINT (even_sq_free s) (odd_sq_free s)

   Less Divisors of a number:
   less_divisors_element       |- !n x. x IN less_divisors n <=> 0 < x /\ x < n /\ x divides n
   less_divisors_0             |- less_divisors 0 = {}
   less_divisors_1             |- less_divisors 1 = {}
   less_divisors_subset_divisors
                               |- !n. less_divisors n SUBSET divisors n
   less_divisors_finite        |- !n. FINITE (less_divisors n)
   less_divisors_prime         |- !n. prime n ==> (less_divisors n = {1})
   less_divisors_has_1         |- !n. 1 < n ==> 1 IN less_divisors n
   less_divisors_nonzero       |- !n x. x IN less_divisors n ==> 0 < x
   less_divisors_has_cofactor  |- !n d. 1 < d /\ d IN less_divisors n ==> n DIV d IN less_divisors n

   Proper Divisors of a number:
   proper_divisors_element     |- !n x. x IN proper_divisors n <=> 1 < x /\ x < n /\ x divides n
   proper_divisors_0           |- proper_divisors 0 = {}
   proper_divisors_1           |- proper_divisors 1 = {}
   proper_divisors_subset      |- !n. proper_divisors n SUBSET less_divisors n
   proper_divisors_finite      |- !n. FINITE (proper_divisors n)
   proper_divisors_not_1       |- !n. 1 NOTIN proper_divisors n
   proper_divisors_by_less_divisors
                               |- !n. proper_divisors n = less_divisors n DELETE 1
   proper_divisors_prime       |- !n. prime n ==> (proper_divisors n = {})
   proper_divisors_has_cofactor|- !n d. d IN proper_divisors n ==> n DIV d IN proper_divisors n
   proper_divisors_min_gt_1    |- !n. proper_divisors n <> {} ==> 1 < MIN_SET (proper_divisors n)
   proper_divisors_max_min     |- !n. proper_divisors n <> {} ==>
                                      (MAX_SET (proper_divisors n) = n DIV MIN_SET (proper_divisors n)) /\
                                      (MIN_SET (proper_divisors n) = n DIV MAX_SET (proper_divisors n))

   Useful Properties of Less Divisors:
   less_divisors_min             |- !n. 1 < n ==> (MIN_SET (less_divisors n) = 1)
   less_divisors_max             |- !n. MAX_SET (less_divisors n) <= n DIV 2
   less_divisors_subset_natural  |- !n. less_divisors n SUBSET natural (n DIV 2)

   Properties of Summation equals Perfect Power:
   perfect_power_special_inequality  |- !p. 1 < p ==> !n. p * (p ** n - 1) < (p - 1) * (2 * p ** n)
   perfect_power_half_inequality_1   |- !p n. 1 < p /\ 0 < n ==> 2 * p ** (n DIV 2) <= p ** n
   perfect_power_half_inequality_2   |- !p n. 1 < p /\ 0 < n ==>
                                        (p ** (n DIV 2) - 2) * p ** (n DIV 2) <= p ** n - 2 * p ** (n DIV 2)
   sigma_eq_perfect_power_bounds_1   |- !p. 1 < p ==>
                          !f. (!n. 0 < n ==> (p ** n = SIGMA (\d. d * f d) (divisors n))) ==>
                              (!n. 0 < n ==> n * f n <= p ** n) /\
                               !n. 0 < n ==> p ** n - 2 * p ** (n DIV 2) < n * f n
   sigma_eq_perfect_power_bounds_2   |- !p. 1 < p ==>
                          !f. (!n. 0 < n ==> (p ** n = SIGMA (\d. d * f d) (divisors n))) ==>
                              (!n. 0 < n ==> n * f n <= p ** n) /\
                               !n. 0 < n ==> (p ** (n DIV 2) - 2) * p ** (n DIV 2) < n * f n

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Mobius Function and Inversion                                             *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Square-free Number and Square-free Sets                                   *)
(* ------------------------------------------------------------------------- *)

(* Define square-free number *)
val square_free_def = Define`
    square_free n = !p. prime p /\ p divides n ==> ~(p * p divides n)
`;

(* Theorem: square_free 1 *)
(* Proof:
       square_free 1
   <=> !p. prime p /\ p divides 1 ==> ~(p * p divides 1)    by square_free_def
   <=> prime 1 ==> ~(1 * 1 divides 1)                       by DIVIDES_ONE
   <=> F ==> ~(1 * 1 divides 1)                             by NOT_PRIME_1
   <=> T                                                    by false assumption
*)
val square_free_1 = store_thm(
  "square_free_1",
  ``square_free 1``,
  rw[square_free_def]);

(* Theorem: prime n ==> square_free n *)
(* Proof:
       square_free n
   <=> !p. prime p /\ p divides n ==> ~(p * p divides n)   by square_free_def
   By contradiction, suppose (p * p divides n).
   Since p divides n ==> (p = n) \/ (p = 1)                by prime_def
     and p * p divides  ==> (p * p = n) \/ (p * p = 1)     by prime_def
     but p <> 1                                            by prime_def
      so p * p <> 1              by MULT_EQ_1
    Thus p * p = n = p,
      or p = 0 \/ p = 1          by SQ_EQ_SELF
     But p <> 0                  by NOT_PRIME_0
     and p <> 1                  by NOT_PRIME_1
    Thus there is a contradiction.
*)
val square_free_prime = store_thm(
  "square_free_prime",
  ``!n. prime n ==> square_free n``,
  rw_tac std_ss[square_free_def] >>
  spose_not_then strip_assume_tac >>
  `p * p = p` by metis_tac[prime_def, MULT_EQ_1] >>
  metis_tac[SQ_EQ_SELF, NOT_PRIME_0, NOT_PRIME_1]);

(* Overload square-free filter of a set *)
val _ = overload_on("sq_free", ``\s. {n | n IN s /\ square_free n}``);

(* Overload non-square-free filter of a set *)
val _ = overload_on("non_sq_free", ``\s. {n | n IN s /\ ~(square_free n)}``);

(* Theorem: n IN sq_free s <=> n IN s /\ square_free n *)
(* Proof: by notation. *)
val sq_free_element = store_thm(
  "sq_free_element",
  ``!s n. n IN sq_free s <=> n IN s /\ square_free n``,
  rw[]);

(* Theorem: sq_free s SUBSET s *)
(* Proof: by SUBSET_DEF *)
val sq_free_subset = store_thm(
  "sq_free_subset",
  ``!s. sq_free s SUBSET s``,
  rw[SUBSET_DEF]);

(* Theorem: FINITE s ==> FINITE (sq_free s) *)
(* Proof: by sq_free_subset, SUBSET_FINITE *)
val sq_free_finite = store_thm(
  "sq_free_finite",
  ``!s. FINITE s ==> FINITE (sq_free s)``,
  metis_tac[sq_free_subset, SUBSET_FINITE]);

(* Theorem: n IN non_sq_free s <=> n IN s /\ ~(square_free n) *)
(* Proof: by notation. *)
val non_sq_free_element = store_thm(
  "non_sq_free_element",
  ``!s n. n IN non_sq_free s <=> n IN s /\ ~(square_free n)``,
  rw[]);

(* Theorem: non_sq_free s SUBSET s *)
(* Proof: by SUBSET_DEF *)
val non_sq_free_subset = store_thm(
  "non_sq_free_subset",
  ``!s. non_sq_free s SUBSET s``,
  rw[SUBSET_DEF]);

(* Theorem: FINITE s ==> FINITE (non_sq_free s) *)
(* Proof: by non_sq_free_subset, SUBSET_FINITE *)
val non_sq_free_finite = store_thm(
  "non_sq_free_finite",
  ``!s. FINITE s ==> FINITE (non_sq_free s)``,
  metis_tac[non_sq_free_subset, SUBSET_FINITE]);

(* Theorem: (s = (sq_free s) UNION (non_sq_free s)) /\ ((sq_free s) INTER (non_sq_free s) = {}) *)
(* Proof:
   This is to show:
   (1) s = (sq_free s) UNION (non_sq_free s)
       True by EXTENSION, IN_UNION.
   (2) (sq_free s) INTER (non_sq_free s) = {}
       True by EXTENSION, IN_INTER
*)
val sq_free_split = store_thm(
  "sq_free_split",
  ``!s. (s = (sq_free s) UNION (non_sq_free s)) /\ ((sq_free s) INTER (non_sq_free s) = {})``,
  (rw[EXTENSION] >> metis_tac[]));

(* Theorem: s = (sq_free s) UNION (non_sq_free s) *)
(* Proof: extract from sq_free_split. *)
val sq_free_union = save_thm("sq_free_union", sq_free_split |> SPEC_ALL |> CONJUNCT1 |> GEN_ALL);
(* val sq_free_union = |- !s. s = sq_free s UNION non_sq_free s: thm *)

(* Theorem: (sq_free s) INTER (non_sq_free s) = {} *)
(* Proof: extract from sq_free_split. *)
val sq_free_inter = save_thm("sq_free_inter", sq_free_split |> SPEC_ALL |> CONJUNCT2 |> GEN_ALL);
(* val sq_free_inter = |- !s. sq_free s INTER non_sq_free s = {}: thm *)

(* Theorem: DISJOINT (sq_free s) (non_sq_free s) *)
(* Proof: by DISJOINT_DEF, sq_free_inter. *)
val sq_free_disjoint = store_thm(
  "sq_free_disjoint",
  ``!s. DISJOINT (sq_free s) (non_sq_free s)``,
  rw_tac std_ss[DISJOINT_DEF, sq_free_inter]);

(* ------------------------------------------------------------------------- *)
(* Prime Divisors of a Number and Partitions of Square-free Set              *)
(* ------------------------------------------------------------------------- *)

(* Define the prime divisors of a number *)
val prime_factors_def = zDefine`
    prime_factors n = {p | prime p /\ p IN (divisors n)}
`;
(* use zDefine as this cannot be computed. *)
(* prime_divisors is used in triangle.hol *)

(* Theorem: p IN prime_factors n <=> prime p /\ p <= n /\ p divides n *)
(* Proof:
       p IN prime_factors n
   <=> prime p /\ p IN (divisors n)                by prime_factors_def
   <=> prime p /\ 0 < p /\ p <= n /\ p divides n   by divisors_def
   <=> prime p /\ p <= n /\ p divides n            by PRIME_POS
*)
Theorem prime_factors_element:
  !n p. p IN prime_factors n <=> prime p /\ p <= n /\ p divides n
Proof
  rw[prime_factors_def, divisors_def] >>
  metis_tac[PRIME_POS]
QED

(* Theorem: (prime_factors n) SUBSET (divisors n) *)
(* Proof:
       p IN (prime_factors n)
   ==> p IN (divisors n)                         by prime_factors_def
   Hence (prime_factors n) SUBSET (divisors n)   by SUBSET_DEF
*)
val prime_factors_subset = store_thm(
  "prime_factors_subset",
  ``!n. (prime_factors n) SUBSET (divisors n)``,
  rw[prime_factors_def, SUBSET_DEF]);

(* Theorem: FINITE (prime_factors n) *)
(* Proof:
   Since (prime_factors n) SUBSET (divisors n)   by prime_factors_subset
     and FINITE (divisors n)                     by divisors_finite
    Thus FINITE (prime_factors n)                by SUBSET_FINITE
*)
val prime_factors_finite = store_thm(
  "prime_factors_finite",
  ``!n. FINITE (prime_factors n)``,
  metis_tac[prime_factors_subset, divisors_finite, SUBSET_FINITE]);

(* Overload even square-free filter of a set *)
val _ = overload_on("even_sq_free", ``\s. {n | n IN (sq_free s) /\ EVEN (CARD (prime_factors n))}``);

(* Overload odd square-free filter of a set *)
val _ = overload_on("odd_sq_free", ``\s. {n | n IN (sq_free s) /\ ODD (CARD (prime_factors n))}``);

(* Theorem: n IN even_sq_free s <=> n IN s /\ square_free n /\ EVEN (CARD (prime_factors n)) *)
(* Proof: by notation. *)
val even_sq_free_element = store_thm(
  "even_sq_free_element",
  ``!s n. n IN even_sq_free s <=> n IN s /\ square_free n /\ EVEN (CARD (prime_factors n))``,
  (rw[] >> metis_tac[]));

(* Theorem: even_sq_free s SUBSET s *)
(* Proof: by SUBSET_DEF *)
val even_sq_free_subset = store_thm(
  "even_sq_free_subset",
  ``!s. even_sq_free s SUBSET s``,
  rw[SUBSET_DEF]);

(* Theorem: FINITE s ==> FINITE (even_sq_free s) *)
(* Proof: by even_sq_free_subset, SUBSET_FINITE *)
val even_sq_free_finite = store_thm(
  "even_sq_free_finite",
  ``!s. FINITE s ==> FINITE (even_sq_free s)``,
  metis_tac[even_sq_free_subset, SUBSET_FINITE]);

(* Theorem: n IN odd_sq_free s <=> n IN s /\ square_free n /\ ODD (CARD (prime_factors n)) *)
(* Proof: by notation. *)
val odd_sq_free_element = store_thm(
  "odd_sq_free_element",
  ``!s n. n IN odd_sq_free s <=> n IN s /\ square_free n /\ ODD (CARD (prime_factors n))``,
  (rw[] >> metis_tac[]));

(* Theorem: odd_sq_free s SUBSET s *)
(* Proof: by SUBSET_DEF *)
val odd_sq_free_subset = store_thm(
  "odd_sq_free_subset",
  ``!s. odd_sq_free s SUBSET s``,
  rw[SUBSET_DEF]);

(* Theorem: FINITE s ==> FINITE (odd_sq_free s) *)
(* Proof: by odd_sq_free_subset, SUBSET_FINITE *)
val odd_sq_free_finite = store_thm(
  "odd_sq_free_finite",
  ``!s. FINITE s ==> FINITE (odd_sq_free s)``,
  metis_tac[odd_sq_free_subset, SUBSET_FINITE]);

(* Theorem: (sq_free s = (even_sq_free s) UNION (odd_sq_free s)) /\
            ((even_sq_free s) INTER (odd_sq_free s) = {}) *)
(* Proof:
   This is to show:
   (1) sq_free s = even_sq_free s UNION odd_sq_free s
       True by EXTENSION, IN_UNION, EVEN_ODD.
   (2) even_sq_free s INTER odd_sq_free s = {}
       True by EXTENSION, IN_INTER, EVEN_ODD.
*)
val sq_free_split_even_odd = store_thm(
  "sq_free_split_even_odd",
  ``!s. (sq_free s = (even_sq_free s) UNION (odd_sq_free s)) /\
       ((even_sq_free s) INTER (odd_sq_free s) = {})``,
  (rw[EXTENSION] >> metis_tac[EVEN_ODD]));

(* Theorem: sq_free s = (even_sq_free s) UNION (odd_sq_free s) *)
(* Proof: extract from sq_free_split_even_odd. *)
val sq_free_union_even_odd =
    save_thm("sq_free_union_even_odd", sq_free_split_even_odd |> SPEC_ALL |> CONJUNCT1 |> GEN_ALL);
(* val sq_free_union_even_odd =
   |- !s. sq_free s = even_sq_free s UNION odd_sq_free s: thm *)

(* Theorem: (even_sq_free s) INTER (odd_sq_free s) = {} *)
(* Proof: extract from sq_free_split_even_odd. *)
val sq_free_inter_even_odd =
    save_thm("sq_free_inter_even_odd", sq_free_split_even_odd |> SPEC_ALL |> CONJUNCT2 |> GEN_ALL);
(* val sq_free_inter_even_odd =
   |- !s. even_sq_free s INTER odd_sq_free s = {}: thm *)

(* Theorem: DISJOINT (even_sq_free s) (odd_sq_free s) *)
(* Proof: by DISJOINT_DEF, sq_free_inter_even_odd. *)
val sq_free_disjoint_even_odd = store_thm(
  "sq_free_disjoint_even_odd",
  ``!s. DISJOINT (even_sq_free s) (odd_sq_free s)``,
  rw_tac std_ss[DISJOINT_DEF, sq_free_inter_even_odd]);

(* ------------------------------------------------------------------------- *)
(* Less Divisors of a number.                                                *)
(* ------------------------------------------------------------------------- *)

(* Overload the set of divisors less than n *)
val _ = overload_on("less_divisors", ``\n. {x | x IN (divisors n) /\ x <> n}``);

(* Theorem: x IN (less_divisors n) <=> (0 < x /\ x < n /\ x divides n) *)
(* Proof: by divisors_element. *)
val less_divisors_element = store_thm(
  "less_divisors_element",
  ``!n x. x IN (less_divisors n) <=> (0 < x /\ x < n /\ x divides n)``,
  rw[divisors_element, EQ_IMP_THM]);

(* Theorem: less_divisors 0 = {} *)
(* Proof: by divisors_element. *)
val less_divisors_0 = store_thm(
  "less_divisors_0",
  ``less_divisors 0 = {}``,
  rw[divisors_element]);

(* Theorem: less_divisors 1 = {} *)
(* Proof: by divisors_element. *)
val less_divisors_1 = store_thm(
  "less_divisors_1",
  ``less_divisors 1 = {}``,
  rw[divisors_element]);

(* Theorem: (less_divisors n) SUBSET (divisors n) *)
(* Proof: by SUBSET_DEF *)
val less_divisors_subset_divisors = store_thm(
  "less_divisors_subset_divisors",
  ``!n. (less_divisors n) SUBSET (divisors n)``,
  rw[SUBSET_DEF]);

(* Theorem: FINITE (less_divisors n) *)
(* Proof:
   Since (less_divisors n) SUBSET (divisors n)   by less_divisors_subset_divisors
     and FINITE (divisors n)                     by divisors_finite
      so FINITE (proper_divisors n)              by SUBSET_FINITE
*)
val less_divisors_finite = store_thm(
  "less_divisors_finite",
  ``!n. FINITE (less_divisors n)``,
  metis_tac[divisors_finite, less_divisors_subset_divisors, SUBSET_FINITE]);

(* Theorem: prime n ==> (less_divisors n = {1}) *)
(* Proof:
   Since prime n
     ==> !b. b divides n ==> (b = n) \/ (b = 1)   by prime_def
   But (less_divisors n) excludes n               by less_divisors_element
   and 1 < n                                      by ONE_LT_PRIME
   Hence less_divisors n = {1}
*)
val less_divisors_prime = store_thm(
  "less_divisors_prime",
  ``!n. prime n ==> (less_divisors n = {1})``,
  rpt strip_tac >>
  `!b. b divides n ==> (b = n) \/ (b = 1)` by metis_tac[prime_def] >>
  rw[less_divisors_element, EXTENSION, EQ_IMP_THM] >| [
    `x <> n` by decide_tac >>
    metis_tac[],
    rw[ONE_LT_PRIME]
  ]);

(* Theorem: 1 < n ==> 1 IN (less_divisors n) *)
(* Proof:
       1 IN (less_divisors n)
   <=> 1 < n /\ 1 divides n     by less_divisors_element
   <=> T                        by ONE_DIVIDES_ALL
*)
val less_divisors_has_1 = store_thm(
  "less_divisors_has_1",
  ``!n. 1 < n ==> 1 IN (less_divisors n)``,
  rw[less_divisors_element]);

(* Theorem: x IN (less_divisors n) ==> 0 < x *)
(* Proof: by less_divisors_element. *)
val less_divisors_nonzero = store_thm(
  "less_divisors_nonzero",
  ``!n x. x IN (less_divisors n) ==> 0 < x``,
  rw[less_divisors_element]);

(* Theorem: 1 < d /\ d IN (less_divisors n) ==> (n DIV d) IN (less_divisors n) *)
(* Proof:
      d IN (less_divisors n)
  ==> d IN (divisors n)                   by less_divisors_subset_divisors
  ==> (n DIV d) IN (divisors n)           by divisors_has_cofactor
   Note 0 < d /\ d <= n ==> 0 < n         by divisors_element
   Also n DIV d < n                       by DIV_LESS, 0 < n /\ 1 < d
   thus n DIV d <> n                      by LESS_NOT_EQ
  Hence (n DIV d) IN (less_divisors n)    by notation
*)
val less_divisors_has_cofactor = store_thm(
  "less_divisors_has_cofactor",
  ``!n d. 1 < d /\ d IN (less_divisors n) ==> (n DIV d) IN (less_divisors n)``,
  rw[divisors_has_cofactor, divisors_element, DIV_LESS, LESS_NOT_EQ]);

(* ------------------------------------------------------------------------- *)
(* Proper Divisors of a number.                                              *)
(* ------------------------------------------------------------------------- *)

(* Overload the set of proper divisors of n *)
val _ = overload_on("proper_divisors", ``\n. {x | x IN (divisors n) /\ x <> 1 /\ x <> n}``);

(* Theorem: x IN (proper_divisors n) <=> (1 < x /\ x < n /\ x divides n) *)
(* Proof:
   Since x IN (divisors n)
     ==> 0 < x /\ x <= n /\ x divides n  by divisors_element
   Since x <= n but x <> n, x < n.
   With x <> 0 /\ x <> 1 ==> 1 < x.
*)
val proper_divisors_element = store_thm(
  "proper_divisors_element",
  ``!n x. x IN (proper_divisors n) <=> (1 < x /\ x < n /\ x divides n)``,
  rw[divisors_element, EQ_IMP_THM]);

(* Theorem: proper_divisors 0 = {} *)
(* Proof: by proper_divisors_element. *)
val proper_divisors_0 = store_thm(
  "proper_divisors_0",
  ``proper_divisors 0 = {}``,
  rw[proper_divisors_element, EXTENSION]);

(* Theorem: proper_divisors 1 = {} *)
(* Proof: by proper_divisors_element. *)
val proper_divisors_1 = store_thm(
  "proper_divisors_1",
  ``proper_divisors 1 = {}``,
  rw[proper_divisors_element, EXTENSION]);

(* Theorem: (proper_divisors n) SUBSET (less_divisors n) *)
(* Proof: by SUBSET_DEF *)
val proper_divisors_subset = store_thm(
  "proper_divisors_subset",
  ``!n. (proper_divisors n) SUBSET (less_divisors n)``,
  rw[SUBSET_DEF]);

(* Theorem: FINITE (proper_divisors n) *)
(* Proof:
   Since (proper_divisors n) SUBSET (less_divisors n) by proper_divisors_subset
     and FINITE (less_divisors n)                     by less_divisors_finite
      so FINITE (proper_divisors n)                   by SUBSET_FINITE
*)
val proper_divisors_finite = store_thm(
  "proper_divisors_finite",
  ``!n. FINITE (proper_divisors n)``,
  metis_tac[less_divisors_finite, proper_divisors_subset, SUBSET_FINITE]);

(* Theorem: 1 NOTIN (proper_divisors n) *)
(* Proof: proper_divisors_element *)
val proper_divisors_not_1 = store_thm(
  "proper_divisors_not_1",
  ``!n. 1 NOTIN (proper_divisors n)``,
  rw[proper_divisors_element]);

(* Theorem: proper_divisors n = (less_divisors n) DELETE 1 *)
(* Proof:
      proper_divisors n
    = {x | x IN (divisors n) /\ x <> 1 /\ x <> n}   by notation
    = {x | x IN (divisors n) /\ x <> n} DELETE 1    by IN_DELETE
    = (less_divisors n) DELETE 1
*)
val proper_divisors_by_less_divisors = store_thm(
  "proper_divisors_by_less_divisors",
  ``!n. proper_divisors n = (less_divisors n) DELETE 1``,
  rw[divisors_element, EXTENSION, EQ_IMP_THM]);

(* Theorem: prime n ==> (proper_divisors n = {}) *)
(* Proof:
      proper_divisors n
    = (less_divisors n) DELETE 1  by proper_divisors_by_less_divisors
    = {1} DELETE 1                by less_divisors_prime, prime n
    = {}                          by SING_DELETE
*)
val proper_divisors_prime = store_thm(
  "proper_divisors_prime",
  ``!n. prime n ==> (proper_divisors n = {})``,
  rw[proper_divisors_by_less_divisors, less_divisors_prime]);

(* Theorem: d IN (proper_divisors n) ==> (n DIV d) IN (proper_divisors n) *)
(* Proof:
   Let e = n DIV d.
   Since d IN (proper_divisors n)
     ==> 1 < d /\ d < n                   by proper_divisors_element
     and d IN (less_divisors n)           by proper_divisors_subset
      so e IN (less_divisors n)           by less_divisors_has_cofactor
     and 0 < e                            by less_divisors_nonzero
   Since d divides n                      by less_divisors_element
      so n = e * d                        by DIV_MULT_EQ, 0 < d
    thus e <> 1 since n <> d              by MULT_LEFT_1
    With 0 < e /\ e <> 1
     ==> e IN (proper_divisors n)         by proper_divisors_by_less_divisors, IN_DELETE
*)
val proper_divisors_has_cofactor = store_thm(
  "proper_divisors_has_cofactor",
  ``!n d. d IN (proper_divisors n) ==> (n DIV d) IN (proper_divisors n)``,
  rpt strip_tac >>
  qabbrev_tac `e = n DIV d` >>
  `1 < d /\ d < n` by metis_tac[proper_divisors_element] >>
  `d IN (less_divisors n)` by metis_tac[proper_divisors_subset, SUBSET_DEF] >>
  `e IN (less_divisors n)` by rw[less_divisors_has_cofactor, Abbr`e`] >>
  `0 < e` by metis_tac[less_divisors_nonzero] >>
  `0 < d /\ n <> d` by decide_tac >>
  `e <> 1` by metis_tac[less_divisors_element, DIV_MULT_EQ, MULT_LEFT_1] >>
  metis_tac[proper_divisors_by_less_divisors, IN_DELETE]);

(* Theorem: (proper_divisors n) <> {} ==> 1 < MIN_SET (proper_divisors n) *)
(* Proof:
   Let s = proper_divisors n.
   Since !x. x IN s ==> 1 < x        by proper_divisors_element
     But MIN_SET s IN s              by MIN_SET_IN_SET
   Hence 1 < MIN_SET s               by above
*)
val proper_divisors_min_gt_1 = store_thm(
  "proper_divisors_min_gt_1",
  ``!n. (proper_divisors n) <> {} ==> 1 < MIN_SET (proper_divisors n)``,
  metis_tac[MIN_SET_IN_SET, proper_divisors_element]);

(* Theorem: (proper_divisors n) <> {} ==>
            (MAX_SET (proper_divisors n) = n DIV (MIN_SET (proper_divisors n))) /\
            (MIN_SET (proper_divisors n) = n DIV (MAX_SET (proper_divisors n)))     *)
(* Proof:
   Let s = proper_divisors n, b = MIN_SET s.
   By MAX_SET_ELIM, this is to show:
   (1) FINITE s, true                     by proper_divisors_finite
   (2) s <> {} /\ x IN s /\ !y. y IN s ==> y <= x ==> x = n DIV b /\ b = n DIV x
       Note s <> {} ==> n <> 0            by proper_divisors_0
        Let m = n DIV b.
       Note n DIV x IN s                  by proper_divisors_has_cofactor, 0 < n, 1 < b.
       Also b IN s /\ b <= x              by MIN_SET_IN_SET, s <> {}
       thus 1 < b                         by proper_divisors_min_gt_1
         so m IN s                        by proper_divisors_has_cofactor, 0 < n, 1 < x.
         or 1 < m                         by proper_divisors_nonzero
        and m <= x                        by implication, x = MAX_SET s.
       Thus n DIV x <= n DIV m            by DIV_LE_MONOTONE_REVERSE [1], 0 < x, 0 < m.
        But n DIV m
          = n DIV (n DIV b) = b           by divide_by_cofactor, b divides n.
         so n DIV x <= b                  by [1]
      Since b <= n DIV x                  by MIN_SET_PROPERTY, b = MIN_SET s, n DIV x IN s.
         so n DIV x = b                   by LESS_EQUAL_ANTISYM (gives second subgoal)
      Hence m = n DIV b
              = n DIV (n DIV x) = x       by divide_by_cofactor, x divides n (gives first subgoal)
*)
val proper_divisors_max_min = store_thm(
  "proper_divisors_max_min",
  ``!n. (proper_divisors n) <> {} ==>
       (MAX_SET (proper_divisors n) = n DIV (MIN_SET (proper_divisors n))) /\
       (MIN_SET (proper_divisors n) = n DIV (MAX_SET (proper_divisors n)))``,
  ntac 2 strip_tac >>
  qabbrev_tac `s = proper_divisors n` >>
  qabbrev_tac `b = MIN_SET s` >>
  DEEP_INTRO_TAC MAX_SET_ELIM >>
  strip_tac >-
  rw[proper_divisors_finite, Abbr`s`] >>
  ntac 3 strip_tac >>
  `n <> 0` by metis_tac[proper_divisors_0] >>
  `b IN s /\ b <= x` by rw[MIN_SET_IN_SET, Abbr`b`] >>
  `1 < b` by rw[proper_divisors_min_gt_1, Abbr`s`, Abbr`b`] >>
  `0 < n /\ 1 < x` by decide_tac >>
  qabbrev_tac `m = n DIV b` >>
  `m IN s /\ (n DIV x) IN s` by rw[proper_divisors_has_cofactor, Abbr`m`, Abbr`s`] >>
  `1 < m` by metis_tac[proper_divisors_element] >>
  `0 < x /\ 0 < m` by decide_tac >>
  `n DIV x <= n DIV m` by rw[DIV_LE_MONOTONE_REVERSE] >>
  `b divides n /\ x divides n` by metis_tac[proper_divisors_element] >>
  `n DIV m = b` by rw[divide_by_cofactor, Abbr`m`] >>
  `b <= n DIV x` by rw[MIN_SET_PROPERTY, Abbr`b`] >>
  `b = n DIV x` by rw[LESS_EQUAL_ANTISYM] >>
  `m = x` by rw[divide_by_cofactor, Abbr`m`] >>
  decide_tac);

(* This is a milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Useful Properties of Less Divisors                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < n ==> (MIN_SET (less_divisors n) = 1) *)
(* Proof:
   Let s = less_divisors n.
   Since 1 < n ==> 1 IN s         by less_divisors_has_1
      so s <> {}                  by MEMBER_NOT_EMPTY
     and !y. y IN s ==> 0 < y     by less_divisors_nonzero
      or !y. y IN s ==> 1 <= y    by LESS_EQ
   Hence 1 = MIN_SET s            by MIN_SET_TEST
*)
val less_divisors_min = store_thm(
  "less_divisors_min",
  ``!n. 1 < n ==> (MIN_SET (less_divisors n) = 1)``,
  metis_tac[less_divisors_has_1, MEMBER_NOT_EMPTY,
             MIN_SET_TEST, less_divisors_nonzero, LESS_EQ, ONE]);

(* Theorem: MAX_SET (less_divisors n) <= n DIV 2 *)
(* Proof:
   Let s = less_divisors n, m = MAX_SET s.
   If s = {},
      Then m = MAX_SET {} = 0          by MAX_SET_EMPTY
       and 0 <= n DIV 2 is trivial.
   If s <> {},
      Then n <> 0 /\ n <> 1            by less_divisors_0, less_divisors_1
   Note 1 IN s                         by less_divisors_has_1
   Consider t = s DELETE 1.
   Then t = proper_divisors n          by proper_divisors_by_less_divisors
   If t = {},
      Then s = {1}                     by DELETE_EQ_SING
       and m = 1                       by SING_DEF, IN_SING (same as MAX_SET_SING)
     Since 2 <= n                      by 1 < n
      thus n DIV n <= n DIV 2          by DIV_LE_MONOTONE_REVERSE
        or n DIV n = 1 = m <= n DIV 2  by DIVMOD_ID, 0 < n
   If t <> {},
      Let b = MIN_SET t
      Then MAX_SET t = n DIV b         by proper_divisors_max_min, t <> {}
     Since MIN_SET s = 1               by less_divisors_min, 1 < n
       and FINITE s                    by less_divisors_finite
       and s <> {1}                    by DELETE_EQ_SING
      thus m = MAX_SET t               by MAX_SET_DELETE, s <> {1}

       Now 1 < b                       by proper_divisors_min_gt_1
        so 2 <= b                      by LESS_EQ, 1 < b
     Hence n DIV b <= n DIV 2          by DIV_LE_MONOTONE_REVERSE
       or        m <= n DIV 2          by m = MAX_SET t = n DIV b
*)

Theorem less_divisors_max:
  !n. MAX_SET (less_divisors n) <= n DIV 2
Proof
  rpt strip_tac >>
  qabbrev_tac `s = less_divisors n` >>
  qabbrev_tac `m = MAX_SET s` >>
  Cases_on `s = {}` >- rw[MAX_SET_EMPTY, Abbr`m`] >>
  `n <> 0 /\ n <> 1` by metis_tac[less_divisors_0, less_divisors_1] >>
  `1 < n` by decide_tac >>
  `1 IN s` by rw[less_divisors_has_1, Abbr`s`] >>
  qabbrev_tac `t = proper_divisors n` >>
  `t = s DELETE 1`  by rw[proper_divisors_by_less_divisors, Abbr`t`, Abbr`s`] >>
  Cases_on `t = {}` >| [
    `s = {1}` by rfs[] >>
    `m = 1` by rw[MAX_SET_SING, Abbr`m`] >>
    `(2 <= n) /\ (0 < 2) /\ (0 < n) /\ (n DIV n = 1)` by rw[] >>
    metis_tac[DIV_LE_MONOTONE_REVERSE],
    qabbrev_tac `b = MIN_SET t` >>
    `MAX_SET t = n DIV b` by metis_tac[proper_divisors_max_min] >>
    `MIN_SET s = 1` by rw[less_divisors_min, Abbr`s`] >>
    `FINITE s` by rw[less_divisors_finite, Abbr`s`] >>
    `s <> {1}` by metis_tac[DELETE_EQ_SING] >>
    `m = MAX_SET t` by metis_tac[MAX_SET_DELETE] >>
    `1 < b` by rw[proper_divisors_min_gt_1, Abbr`b`, Abbr`t`] >>
    `2 <= b /\ (0 < b) /\ (0 < 2)` by decide_tac >>
    `n DIV b <= n DIV 2` by rw[DIV_LE_MONOTONE_REVERSE] >>
    decide_tac
  ]
QED

(* Theorem: (less_divisors n) SUBSET (natural (n DIV 2)) *)
(* Proof:
   Let s = less_divisors n
   If n = 0 or n - 1,
   Then s = {}                        by less_divisors_0, less_divisors_1
    and {} SUBSET t, for any t.       by EMPTY_SUBSET
   If n <> 0 and n <> 1, 1 < n.
   Note FINITE s                      by less_divisors_finite
    and x IN s ==> x <= MAX_SET s     by MAX_SET_PROPERTY, FINITE s
    But MAX_SET s <= n DIV 2          by less_divisors_max
   Thus x IN s ==> x <= n DIV 2       by LESS_EQ_TRANS
   Note s <> {}                       by MEMBER_NOT_EMPTY, x IN s
    and x IN s ==> MIN_SET s <= x     by MIN_SET_PROPERTY, s <> {}
  Since 1 = MIN_SET s, 1 <= x         by less_divisors_min, 1 < n
   Thus 0 < x <= n DIV 2              by LESS_EQ
     or x IN (natural (n DIV 2))      by natural_element
*)
val less_divisors_subset_natural = store_thm(
  "less_divisors_subset_natural",
  ``!n. (less_divisors n) SUBSET (natural (n DIV 2))``,
  rpt strip_tac >>
  qabbrev_tac `s = less_divisors n` >>
  qabbrev_tac `m = n DIV 2` >>
  Cases_on `(n = 0) \/ (n = 1)` >-
  metis_tac[less_divisors_0, less_divisors_1, EMPTY_SUBSET] >>
  `1 < n` by decide_tac >>
  rw_tac std_ss[SUBSET_DEF] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `FINITE s` by rw[less_divisors_finite, Abbr`s`] >>
  `x <= MAX_SET s` by rw[MAX_SET_PROPERTY] >>
  `MIN_SET s <= x` by rw[MIN_SET_PROPERTY] >>
  `MAX_SET s <= m` by rw[less_divisors_max, Abbr`s`, Abbr`m`] >>
  `MIN_SET s = 1` by rw[less_divisors_min, Abbr`s`] >>
  `0 < x /\ x <= m` by decide_tac >>
  rw[natural_element]);

(* ------------------------------------------------------------------------- *)
(* Properties of Summation equals Perfect Power                              *)
(* ------------------------------------------------------------------------- *)

(* Idea for the theorem below (for m = n DIV 2 when applied in bounds):
      p * (p ** m - 1) / (p - 1)
   <  p * p ** m / (p - 1)        discard subtraction
   <= p * p ** m / (p / 2)        replace by smaller denominator
    = 2 * p ** m                  double division and cancel p
   or p * (p ** m - 1) < (p - 1) * 2 * p ** m
*)

(* Theorem: 1 < p ==> !n. p * (p ** n - 1) < (p - 1) * (2 * p ** n) *)
(* Proof:
   Let q = p ** n
   Then 1 <= q                       by ONE_LE_EXP, 0 < p
     so p <= p * q                   by LE_MULT_LCANCEL, p <> 0
   Also 1 < p ==> 2 <= p             by LESS_EQ
     so 2 * q <= p * q               by LE_MULT_RCANCEL, q <> 0
   Thus   LHS
        = p * (q - 1)
        = p * q - p                  by LEFT_SUB_DISTRIB
    And   RHS
        = (p - 1) * (2 * q)
        = p * (2 * q) - 2 * q        by RIGHT_SUB_DISTRIB
        = 2 * (p * q) - 2 * q        by MULT_ASSOC, MULT_COMM
        = (p * q + p * q) - 2 * q    by TIMES2
        = (p * q - p + p + p * q) - 2 * q  by SUB_ADD, p <= p * q
        = LHS + p + p * q - 2 * q    by above
        = LHS + p + (p * q - 2 * q)  by LESS_EQ_ADD_SUB, 2 * q <= p * q
        = LHS + p + (p - 2) * q      by RIGHT_SUB_DISTRIB

    Since 0 < p                      by 1 < p
      and 0 <= (p - 2) * q           by 2 <= p
    Hence LHS < RHS                  by discarding positive terms
*)
val perfect_power_special_inequality = store_thm(
  "perfect_power_special_inequality",
  ``!p. 1 < p ==> !n. p * (p ** n - 1) < (p - 1) * (2 * p ** n)``,
  rpt strip_tac >>
  qabbrev_tac `q = p ** n` >>
  `p <> 0 /\ 2 <= p` by decide_tac >>
  `1 <= q` by rw[ONE_LE_EXP, Abbr`q`] >>
  `p <= p * q` by rw[] >>
  `2 * q <= p * q` by rw[] >>
  qabbrev_tac `l = p * (q - 1)` >>
  qabbrev_tac `r = (p - 1) * (2 * q)` >>
  `l = p * q - p` by rw[Abbr`l`] >>
  `r = p * (2 * q) - 2 * q` by rw[Abbr`r`] >>
  `_ = 2 * (p * q) - 2 * q` by rw[] >>
  `_ = (p * q + p * q) - 2 * q` by rw[] >>
  `_ = (p * q - p + p + p * q) - 2 * q` by rw[] >>
  `_ = l + p + p * q - 2 * q` by rw[] >>
  `_ = l + p + (p * q - 2 * q)` by rw[] >>
  `_ = l + p + (p - 2) * q` by rw[] >>
  decide_tac);

(* Theorem: 1 < p /\ 1 < n ==>
            p ** (n DIV 2) * p ** (n DIV 2) <= p ** n /\
            2 * p ** (n DIV 2) <= p ** (n DIV 2) * p ** (n DIV 2) *)
(* Proof:
   Let m = n DIV 2, q = p ** m.
   The goal becomes: q * q <= p ** n /\ 2 * q <= q * q.
      Note 1 < p ==> 0 < p.
   First goal: q * q <= p ** n
      Then 0 < q                    by EXP_POS, 0 < p
       and 2 * m <= n               by DIV_MULT_LE, 0 < 2.
      thus p ** (2 * m) <= p ** n   by EXP_BASE_LE_MONO, 1 < p.
     Since p ** (2 * m)
         = p ** (m + m)             by TIMES2
         = q * q                    by EXP_ADD
      Thus q * q <= p ** n          by above

   Second goal: 2 * q <= q * q
     Since 1 < n, so 2 <= n         by LESS_EQ
        so 2 DIV 2 <= n DIV 2       by DIV_LE_MONOTONE, 0 < 2.
        or 1 <= m, i.e. 0 < m       by DIVMOD_ID, 0 < 2.
      Thus 1 < q                    by ONE_LT_EXP, 1 < p, 0 < m.
        so 2 <= q                   by LESS_EQ
       and 2 * q <= q * q           by MULT_RIGHT_CANCEL, q <> 0.
     Hence 2 * q <= p ** n          by LESS_EQ_TRANS
*)
val perfect_power_half_inequality_lemma = prove(
  ``!p n. 1 < p /\ 1 < n ==>
         p ** (n DIV 2) * p ** (n DIV 2) <= p ** n /\
         2 * p ** (n DIV 2) <= p ** (n DIV 2) * p ** (n DIV 2)``,
  ntac 3 strip_tac >>
  qabbrev_tac `m = n DIV 2` >>
  qabbrev_tac `q = p ** m` >>
  strip_tac >| [
    `0 < p /\ 0 < 2` by decide_tac >>
    `0 < q /\ q <> 0` by rw[EXP_POS, Abbr`q`] >>
    `2 * m <= n` by metis_tac[DIV_MULT_LE, MULT_COMM] >>
    `p ** (2 * m) <= p ** n` by rw[EXP_BASE_LE_MONO] >>
    `p ** (2 * m) = p ** (m + m)` by rw[] >>
    `_ = q * q` by rw[EXP_ADD, Abbr`q`] >>
    decide_tac,
    `2 <= n /\ 0 < 2` by decide_tac >>
    `1 <= m` by metis_tac[DIV_LE_MONOTONE, DIVMOD_ID] >>
    `0 < m` by decide_tac >>
    `1 < q` by rw[ONE_LT_EXP, Abbr`q`] >>
    rw[]
  ]);

(* Theorem: 1 < p /\ 0 < n ==> 2 * p ** (n DIV 2) <= p ** n *)
(* Proof:
   Let m = n DIV 2, q = p ** m.
   The goal becomes: 2 * q <= p ** n
   If n = 1,
      Then m = 0                    by ONE_DIV, 0 < 2.
       and q = 1                    by EXP
       and p ** n = p               by EXP_1
     Since 1 < p ==> 2 <= p         by LESS_EQ
     Hence 2 * q <= p = p ** n      by MULT_RIGHT_1
   If n <> 1, 1 < n.
      Then q * q <= p ** n /\
           2 * q <= q * q           by perfect_power_half_inequality_lemma
     Hence 2 * q <= p ** n          by LESS_EQ_TRANS
*)
val perfect_power_half_inequality_1 = store_thm(
  "perfect_power_half_inequality_1",
  ``!p n. 1 < p /\ 0 < n ==> 2 * p ** (n DIV 2) <= p ** n``,
  rpt strip_tac >>
  qabbrev_tac `m = n DIV 2` >>
  qabbrev_tac `q = p ** m` >>
  Cases_on `n = 1` >| [
    `m = 0` by rw[Abbr`m`] >>
    `(q = 1) /\ (p ** n = p)` by rw[Abbr`q`] >>
    `2 <= p` by decide_tac >>
    rw[],
    `1 < n` by decide_tac >>
    `q * q <= p ** n /\ 2 * q <= q * q` by rw[perfect_power_half_inequality_lemma, Abbr`q`, Abbr`m`] >>
    decide_tac
  ]);

(* Theorem: 1 < p /\ 0 < n ==> (p ** (n DIV 2) - 2) * p ** (n DIV 2) <= p ** n - 2 * p ** (n DIV 2) *)
(* Proof:
   Let m = n DIV 2, q = p ** m.
   The goal becomes: (q - 2) * q <= p ** n - 2 * q
   If n = 1,
      Then m = 0                    by ONE_DIV, 0 < 2.
       and q = 1                    by EXP
       and p ** n = p               by EXP_1
     Since 1 < p ==> 2 <= p         by LESS_EQ
        or 0 <= p - 2               by SUB_LEFT_LESS_EQ
     Hence (q - 2) * q = 0 <= p - 2
   If n <> 1, 1 < n.
      Then q * q <= p ** n /\ 2 * q <= q * q   by perfect_power_half_inequality_lemma
      Thus q * q - 2 * q <= p ** n - 2 * q     by LE_SUB_RCANCEL, 2 * q <= q * q
        or   (q - 2) * q <= p ** n - 2 * q     by RIGHT_SUB_DISTRIB
*)
val perfect_power_half_inequality_2 = store_thm(
  "perfect_power_half_inequality_2",
  ``!p n. 1 < p /\ 0 < n ==> (p ** (n DIV 2) - 2) * p ** (n DIV 2) <= p ** n - 2 * p ** (n DIV 2)``,
  rpt strip_tac >>
  qabbrev_tac `m = n DIV 2` >>
  qabbrev_tac `q = p ** m` >>
  Cases_on `n = 1` >| [
    `m = 0` by rw[Abbr`m`] >>
    `(q = 1) /\ (p ** n = p)` by rw[Abbr`q`] >>
    `0 <= p - 2 /\ (1 - 2 = 0)` by decide_tac >>
    rw[],
    `1 < n` by decide_tac >>
    `q * q <= p ** n /\ 2 * q <= q * q` by rw[perfect_power_half_inequality_lemma, Abbr`q`, Abbr`m`] >>
    decide_tac
  ]);

(* Already in pred_setTheory:
SUM_IMAGE_SUBSET_LE;
!f s t. FINITE s /\ t SUBSET s ==> SIGMA f t <= SIGMA f s: thm
SUM_IMAGE_MONO_LESS_EQ;
|- !s. FINITE s ==> (!x. x IN s ==> f x <= g x) ==> SIGMA f s <= SIGMA g s: thm
*)

(* Theorem: 1 < p ==> !f. (!n. 0 < n ==> (p ** n = SIGMA (\d. d * f d) (divisors n))) ==>
            (!n. 0 < n ==> n * (f n) <= p ** n) /\
            (!n. 0 < n ==> p ** n - 2 * p ** (n DIV 2) < n * (f n)) *)
(* Proof:
   Step 1: prove a specific lemma for sum decomposition
   Claim: !n. 0 < n ==> (divisors n DIFF {n}) SUBSET (natural (n DIV 2)) /\
          (p ** n = SIGMA (\d. d * f d) (divisors n)) ==>
          (p ** n = n * f n + SIGMA (\d. d * f d) (divisors n DIFF {n}))
   Proof: Let s = divisors n, a = {n}, b = s DIFF a, m = n DIV 2.
          Then b = less_divisors n        by EXTENSION,IN_DIFF
           and b SUBSET (natural m)       by less_divisors_subset_natural
          This gives the first part.
          For the second part:
          Note a SUBSET s                 by divisors_has_last, SUBSET_DEF
           and b SUBSET s                 by DIFF_SUBSET
          Thus s = b UNION a              by UNION_DIFF, a SUBSET s
           and DISJOINT b a               by DISJOINT_DEF, EXTENSION
           Now FINITE s                   by divisors_finite
            so FINITE a /\ FINITE b       by SUBSET_FINITE, by a SUBSEt s /\ b SUBSET s

               p ** n
             = SIGMA (\d. d * f d) s              by implication
             = SIGMA (\d. d * f d) (b UNION a)    by above, s = b UNION a
             = SIGMA (\d. d * f d) b + SIGMA (\d. d * f d) a   by SUM_IMAGE_DISJOINT, FINITE a /\ FINITE b
             = SIGMA (\d. d * f d) b + n * f n    by SUM_IMAGE_SING
             = n * f n + SIGMA (\d. d * f d) b    by ADD_COMM
          This gives the second part.

   Step 2: Upper bound, to show: !n. 0 < n ==> n * f n <= p ** n
           Let b = divisors n DIFF {n}
           Since n * f n + SIGMA (\d. d * f d) b = p ** n    by lemma
           Hence n * f n <= p ** n                           by 0 <= SIGMA (\d. d * f d) b

   Step 3: Lower bound, to show: !n. 0 < n ==> p ** n - p ** (n DIV 2) <= n * f n
           Let s = divisors n, a = {n}, b = s DIFF a, m = n DIV 2.
            Note b SUBSET (natural m) /\
                 (p ** n = n * f n + SIGMA (\d. d * f d) b)  by lemma
           Since FINITE (natural m)                          by natural_finite
            thus SIGMA (\d. d * f d) b
              <= SIGMA (\d. d * f d) (natural m)             by SUM_IMAGE_SUBSET_LE [1]
            Also !d. d IN (natural m) ==> 0 < d              by natural_element
             and !d. 0 < d ==> d * f d <= p ** d             by upper bound (Step 2)
            thus !d. d IN (natural m) ==> d * f d <= p ** d  by implication
           Hence SIGMA (\d. d * f d) (natural m)
              <= SIGMA (\d. p ** d) (natural m)              by SUM_IMAGE_MONO_LESS_EQ [2]
             Now 1 < p ==> 0 < p /\ (p - 1) <> 0             by arithmetic

             (p - 1) * SIGMA (\d. d * f d) b
          <= (p - 1) * SIGMA (\d. d * f d) (natural m)       by LE_MULT_LCANCEL, [1]
          <= (p - 1) * SIGMA (\d. p ** d) (natural m)        by LE_MULT_LCANCEL, [2]
           = p * (p ** m - 1)                                by sigma_geometric_natural_eqn
           < (p - 1) * (2 * p ** m)                          by perfect_power_special_inequality

             (p - 1) * SIGMA (\d. d * f d) b < (p - 1) * (2 * p ** m)   by LESS_EQ_LESS_TRANS
             or        SIGMA (\d. d * f d) b < 2 * p ** m               by LT_MULT_LCANCEL, (p - 1) <> 0

            But 2 * p ** m <= p ** n                         by perfect_power_half_inequality_1, 1 < p, 0 < n
           Thus p ** n = p ** n - 2 * p ** m + 2 * p ** m    by SUB_ADD, 2 * p ** m <= p ** n
       Combinig with lemma,
           p ** n - 2 * p ** m + 2 * p ** m < n * f n + 2 * p ** m
             or         p ** n - 2 * p ** m < n * f n        by LESS_MONO_ADD_EQ, no condition
*)
Theorem sigma_eq_perfect_power_bounds_1:
  !p.
    1 < p ==>
    !f. (!n. 0 < n ==> (p ** n = SIGMA (\d. d * f d) (divisors n))) ==>
        (!n. 0 < n ==> n * (f n) <= p ** n) /\
        (!n. 0 < n ==> p ** n - 2 * p ** (n DIV 2) < n * (f n))
Proof
  ntac 4 strip_tac >>
  ‘∀n. 0 < n ==>
       (divisors n DIFF {n}) SUBSET (natural (n DIV 2)) /\
       (p ** n = SIGMA (\d. d * f d) (divisors n) ==>
        p ** n = n * f n + SIGMA (\d. d * f d) (divisors n DIFF {n}))’
    by (ntac 2 strip_tac >>
        qabbrev_tac `s = divisors n` >>
        qabbrev_tac `a = {n}` >>
        qabbrev_tac `b = s DIFF a` >>
        qabbrev_tac `m = n DIV 2` >>
        `b = less_divisors n` by rw[EXTENSION, Abbr`b`, Abbr`a`, Abbr`s`] >>
        `b SUBSET (natural m)` by metis_tac[less_divisors_subset_natural] >>
        strip_tac >- rw[] >>
        `a SUBSET s` by rw[divisors_has_last, SUBSET_DEF, Abbr`s`, Abbr`a`] >>
        `b SUBSET s` by rw[Abbr`b`] >>
        `s = b UNION a` by rw[UNION_DIFF, Abbr`b`] >>
        `DISJOINT b a`
          by (rw[DISJOINT_DEF, Abbr`b`, EXTENSION] >> metis_tac[]) >>
        `FINITE s` by rw[divisors_finite, Abbr`s`] >>
        `FINITE a /\ FINITE b` by metis_tac[SUBSET_FINITE] >>
        strip_tac >>
        `_ = SIGMA (\d. d * f d) (b UNION a)` by metis_tac[Abbr`s`] >>
        `_ = SIGMA (\d. d * f d) b + SIGMA (\d. d * f d) a`
          by rw[SUM_IMAGE_DISJOINT] >>
        `_ = SIGMA (\d. d * f d) b + n * f n` by rw[SUM_IMAGE_SING, Abbr`a`] >>
        rw[]) >>
  conj_asm1_tac >| [
    rpt strip_tac >>
    `p ** n = n * f n + SIGMA (\d. d * f d) (divisors n DIFF {n})` by rw[] >>
    decide_tac,
    rpt strip_tac >>
    qabbrev_tac `s = divisors n` >>
    qabbrev_tac `a = {n}` >>
    qabbrev_tac `b = s DIFF a` >>
    qabbrev_tac `m = n DIV 2` >>
    `b SUBSET (natural m) /\ (p ** n = n * f n + SIGMA (\d. d * f d) b)`
      by rw[Abbr`s`, Abbr`a`, Abbr`b`, Abbr`m`] >>
    `FINITE (natural m)` by rw[natural_finite] >>
    `SIGMA (\d. d * f d) b <= SIGMA (\d. d * f d) (natural m)`
      by rw[SUM_IMAGE_SUBSET_LE] >>
    `!d. d IN (natural m) ==> 0 < d` by rw[natural_element] >>
    `SIGMA (\d. d * f d) (natural m) <= SIGMA (\d. p ** d) (natural m)`
      by rw[SUM_IMAGE_MONO_LESS_EQ] >>
    `0 < p /\ (p - 1) <> 0` by decide_tac >>
    `(p - 1) * SIGMA (\d. p ** d) (natural m) = p * (p ** m - 1)`
      by rw[sigma_geometric_natural_eqn] >>
    `p * (p ** m - 1) < (p - 1) * (2 * p ** m)`
      by rw[perfect_power_special_inequality] >>
    `SIGMA (\d. d * f d) b < 2 * p ** m`
      by metis_tac[LE_MULT_LCANCEL, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS,
                   LT_MULT_LCANCEL] >>
    `p ** n < n * f n + 2 * p ** m` by decide_tac >>
    `2 * p ** m <= p ** n` by rw[perfect_power_half_inequality_1, Abbr`m`] >>
    decide_tac
  ]
QED

(* Theorem: 1 < p ==> !f. (!n. 0 < n ==> (p ** n = SIGMA (\d. d * f d) (divisors n))) ==>
            (!n. 0 < n ==> n * (f n) <= p ** n) /\
            (!n. 0 < n ==> (p ** (n DIV 2) - 2) * p ** (n DIV 2) < n * (f n)) *)
(* Proof:
   For the first goal: (!n. 0 < n ==> n * (f n) <= p ** n)
       True by sigma_eq_perfect_power_bounds_1.
   For the second goal: (!n. 0 < n ==> (p ** (n DIV 2) - 2) * p ** (n DIV 2) < n * (f n))
       Let m = n DIV 2.
       Then p ** n - 2 * p ** m < n * (f n)                     by sigma_eq_perfect_power_bounds_1
        and (p ** m - 2) * p ** m <= p ** n - 2 * p ** m        by perfect_power_half_inequality_2
      Hence (p ** (n DIV 2) - 2) * p ** (n DIV 2) < n * (f n)   by LESS_EQ_LESS_TRANS
*)
val sigma_eq_perfect_power_bounds_2 = store_thm(
  "sigma_eq_perfect_power_bounds_2",
  ``!p. 1 < p ==> !f. (!n. 0 < n ==> (p ** n = SIGMA (\d. d * f d) (divisors n))) ==>
   (!n. 0 < n ==> n * (f n) <= p ** n) /\
   (!n. 0 < n ==> (p ** (n DIV 2) - 2) * p ** (n DIV 2) < n * (f n))``,
  rpt strip_tac >-
  rw[sigma_eq_perfect_power_bounds_1] >>
  qabbrev_tac `m = n DIV 2` >>
  `p ** n - 2 * p ** m < n * (f n)` by rw[sigma_eq_perfect_power_bounds_1, Abbr`m`] >>
  `(p ** m - 2) * p ** m <= p ** n - 2 * p ** m` by rw[perfect_power_half_inequality_2, Abbr`m`] >>
  decide_tac);

(* This is a milestone theorem. *)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
