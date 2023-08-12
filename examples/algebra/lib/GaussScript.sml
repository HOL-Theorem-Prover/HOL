(* ------------------------------------------------------------------------- *)
(* Gauss' Little Theorem.                                                    *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "Gauss";

(* ------------------------------------------------------------------------- *)


(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open arithmeticTheory pred_setTheory listTheory;

(* Get dependent theories in lib *)
(* val _ = load "helperListTheory"; *)
open helperListTheory;

(* val _ = load "EulerTheory"; *)
open EulerTheory;
(* (* val _ = load "helperFunctionTheory"; -- in EulerTheory *) *)
(* (* val _ = load "helperNumTheory"; -- in helperFunctionTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in helperFunctionTheory *) *)
open helperNumTheory helperSetTheory helperFunctionTheory;

(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open dividesTheory gcdTheory;

(* for SQRT and related theorems *)
(* val _ = load "logPowerTheory"; *)
open logrootTheory logPowerTheory;


(* ------------------------------------------------------------------------- *)
(* Gauss' Little Theorem                                                     *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported, ! in computeLib):

   Helper Theorems:

   Coprimes:
   coprimes_def      |- !n. coprimes n = {j | j IN natural n /\ coprime j n}
   coprimes_element  |- !n j. j IN coprimes n <=> 0 < j /\ j <= n /\ coprime j n
!  coprimes_alt      |- !n. coprimes n = natural n INTER {j | coprime j n}
   coprimes_thm      |- !n. coprimes n = set (FILTER (\j. coprime j n) (GENLIST SUC n))
   coprimes_subset   |- !n. coprimes n SUBSET natural n
   coprimes_finite   |- !n. FINITE (coprimes n)
   coprimes_0        |- coprimes 0 = {}
   coprimes_1        |- coprimes 1 = {1}
   coprimes_has_1    |- !n. 0 < n ==> 1 IN coprimes n
   coprimes_eq_empty |- !n. (coprimes n = {}) <=> (n = 0)
   coprimes_no_0     |- !n. 0 NOTIN coprimes n
   coprimes_without_last |- !n. 1 < n ==> n NOTIN coprimes n
   coprimes_with_last    |- !n. n IN coprimes n <=> (n = 1)
   coprimes_has_last_but_1  |- !n. 1 < n ==> n - 1 IN coprimes n
   coprimes_element_less    |- !n. 1 < n ==> !j. j IN coprimes n ==> j < n
   coprimes_element_alt     |- !n. 1 < n ==> !j. j IN coprimes n <=> j < n /\ coprime j n
   coprimes_max      |- !n. 1 < n ==> (MAX_SET (coprimes n) = n - 1)
   coprimes_eq_Euler |- !n. 1 < n ==> (coprimes n = Euler n)
   coprimes_prime    |- !n. prime n ==> (coprimes n = residue n)

   Coprimes by a divisor:
   coprimes_by_def     |- !n d. coprimes_by n d = if 0 < n /\ d divides n then coprimes (n DIV d) else {}
   coprimes_by_element |- !n d j. j IN coprimes_by n d <=> 0 < n /\ d divides n /\ j IN coprimes (n DIV d)
   coprimes_by_finite  |- !n d. FINITE (coprimes_by n d)
   coprimes_by_0       |- !d. coprimes_by 0 d = {}
   coprimes_by_by_0    |- !n. coprimes_by n 0 = {}
   coprimes_by_by_1    |- !n. 0 < n ==> (coprimes_by n 1 = coprimes n)
   coprimes_by_by_last |- !n. 0 < n ==> (coprimes_by n n = {1})
   coprimes_by_by_divisor  |- !n d. 0 < n /\ d divides n ==> (coprimes_by n d = coprimes (n DIV d))
   coprimes_by_eq_empty    |- !n d. 0 < n ==> ((coprimes_by n d = {}) <=> ~(d divides n))

   GCD Equivalence Class:
   gcd_matches_def       |- !n d. gcd_matches n d = {j | j IN natural n /\ (gcd j n = d)}
!  gcd_matches_alt       |- !n d. gcd_matches n d = natural n INTER {j | gcd j n = d}
   gcd_matches_element   |- !n d j. j IN gcd_matches n d <=> 0 < j /\ j <= n /\ (gcd j n = d)
   gcd_matches_subset    |- !n d. gcd_matches n d SUBSET natural n
   gcd_matches_finite    |- !n d. FINITE (gcd_matches n d)
   gcd_matches_0         |- !d. gcd_matches 0 d = {}
   gcd_matches_with_0    |- !n. gcd_matches n 0 = {}
   gcd_matches_1         |- !d. gcd_matches 1 d = if d = 1 then {1} else {}
   gcd_matches_has_divisor     |- !n d. 0 < n /\ d divides n ==> d IN gcd_matches n d
   gcd_matches_element_divides |- !n d j. j IN gcd_matches n d ==> d divides j /\ d divides n
   gcd_matches_eq_empty        |- !n d. 0 < n ==> ((gcd_matches n d = {}) <=> ~(d divides n))

   Phi Function:
   phi_def           |- !n. phi n = CARD (coprimes n)
   phi_thm           |- !n. phi n = LENGTH (FILTER (\j. coprime j n) (GENLIST SUC n))
   phi_fun           |- phi = CARD o coprimes
   phi_pos           |- !n. 0 < n ==> 0 < phi n
   phi_0             |- phi 0 = 0
   phi_eq_0          |- !n. (phi n = 0) <=> (n = 0)
   phi_1             |- phi 1 = 1
   phi_eq_totient    |- !n. 1 < n ==> (phi n = totient n)
   phi_prime         |- !n. prime n ==> (phi n = n - 1)
   phi_2             |- phi 2 = 1
   phi_gt_1          |- !n. 2 < n ==> 1 < phi n
   phi_le            |- !n. phi n <= n
   phi_lt            |- !n. 1 < n ==> phi n < n

   Divisors:
   divisors_def            |- !n. divisors n = {d | 0 < d /\ d <= n /\ d divides n}
   divisors_element        |- !n d. d IN divisors n <=> 0 < d /\ d <= n /\ d divides n
   divisors_element_alt    |- !n. 0 < n ==> !d. d IN divisors n <=> d divides n
   divisors_has_element    |- !n d. d IN divisors n ==> 0 < n
   divisors_has_1          |- !n. 0 < n ==> 1 IN divisors n
   divisors_has_last       |- !n. 0 < n ==> n IN divisors n
   divisors_not_empty      |- !n. 0 < n ==> divisors n <> {}
   divisors_0              |- divisors 0 = {}
   divisors_1              |- divisors 1 = {1}
   divisors_eq_empty       |- !n. divisors n = {} <=> n = 0
!  divisors_eqn            |- !n. divisors n =
                                  IMAGE (\j. if j + 1 divides n then j + 1 else 1) (count n)
   divisors_has_factor     |- !n p q. 0 < n /\ n = p * q ==> p IN divisors n /\ q IN divisors n
   divisors_has_cofactor   |- !n d. d IN divisors n ==> n DIV d IN divisors n
   divisors_delete_last    |- !n. divisors n DELETE n = {m | 0 < m /\ m < n /\ m divides n}
   divisors_nonzero        |- !n d. d IN divisors n ==> 0 < d
   divisors_subset_natural |- !n. divisors n SUBSET natural n
   divisors_finite         |- !n. FINITE (divisors n)
   divisors_divisors_bij   |- !n. (\d. n DIV d) PERMUTES divisors n

   An upper bound for divisors:
   divisor_le_cofactor_ge  |- !n p. 0 < p /\ p divides n /\ p <= SQRT n ==> SQRT n <= n DIV p
   divisor_gt_cofactor_le  |- !n p. 0 < p /\ p divides n /\ SQRT n < p ==> n DIV p <= SQRT n
   divisors_cofactor_inj   |- !n. INJ (\j. n DIV j) (divisors n) univ(:num)
   divisors_card_upper     |- !n. CARD (divisors n) <= TWICE (SQRT n)

   Gauss' Little Theorem:
   gcd_matches_divisor_element  |- !n d. d divides n ==>
                                   !j. j IN gcd_matches n d ==> j DIV d IN coprimes_by n d
   gcd_matches_bij_coprimes_by  |- !n d. d divides n ==>
                                   BIJ (\j. j DIV d) (gcd_matches n d) (coprimes_by n d)
   gcd_matches_bij_coprimes     |- !n d. 0 < n /\ d divides n ==>
                                   BIJ (\j. j DIV d) (gcd_matches n d) (coprimes (n DIV d))
   divisors_eq_gcd_image        |- !n. divisors n = IMAGE (gcd n) (natural n)
   gcd_eq_equiv_class           |- !n d. feq_class (gcd n) (natural n) d = gcd_matches n d
   gcd_eq_equiv_class_fun       |- !n. feq_class (gcd n) (natural n) = gcd_matches n
   gcd_eq_partition_by_divisors |- !n. partition (feq (gcd n)) (natural n) =
                                       IMAGE (gcd_matches n) (divisors n)
   gcd_eq_equiv_on_natural      |- !n. feq (gcd n) equiv_on natural n
   sum_over_natural_by_gcd_partition
                                |- !f n. SIGMA f (natural n) =
                                         SIGMA (SIGMA f) (partition (feq (gcd n)) (natural n))
   sum_over_natural_by_divisors |- !f n. SIGMA f (natural n) =
                                         SIGMA (SIGMA f) (IMAGE (gcd_matches n) (divisors n))
   gcd_matches_from_divisors_inj         |- !n. INJ (gcd_matches n) (divisors n) univ(:num -> bool)
   gcd_matches_and_coprimes_by_same_size |- !n. CARD o gcd_matches n = CARD o coprimes_by n
   coprimes_by_with_card      |- !n. 0 < n ==> CARD o coprimes_by n =
                                               (\d. phi (if d IN divisors n then n DIV d else 0))
   coprimes_by_divisors_card  |- !n x. x IN divisors n ==>
                                       (CARD o coprimes_by n) x = (\d. phi (n DIV d)) x
   Gauss_little_thm           |- !n. SIGMA phi (divisors n) = n

   Euler phi function is multiplicative for coprimes:
   coprimes_mult_by_image
                       |- !m n. coprime m n ==>
                                coprimes (m * n) =
                                IMAGE (\(x,y). if m * n = 1 then 1 else (x * n + y * m) MOD (m * n))
                                      (coprimes m CROSS coprimes n)
   coprimes_map_cross_inj
                       |- !m n. coprime m n ==>
                                INJ (\(x,y). if m * n = 1 then 1 else (x * n + y * m) MOD (m * n))
                                    (coprimes m CROSS coprimes n) univ(:num)
   phi_mult            |- !m n. coprime m n ==> phi (m * n) = phi m * phi n
   phi_primes_distinct |- !p q. prime p /\ prime q /\ p <> q ==> phi (p * q) = (p - 1) * (q - 1)

   Euler phi function for prime powers:
   multiples_upto_def  |- !m n. m multiples_upto n = {x | m divides x /\ 0 < x /\ x <= n}
   multiples_upto_element
                       |- !m n x. x IN m multiples_upto n <=> m divides x /\ 0 < x /\ x <= n
   multiples_upto_alt  |- !m n. m multiples_upto n = {x | ?k. x = k * m /\ 0 < x /\ x <= n}
   multiples_upto_element_alt
                       |- !m n x. x IN m multiples_upto n <=> ?k. x = k * m /\ 0 < x /\ x <= n
   multiples_upto_eqn  |- !m n. m multiples_upto n = {x | m divides x /\ x IN natural n}
   multiples_upto_0_n  |- !n. 0 multiples_upto n = {}
   multiples_upto_1_n  |- !n. 1 multiples_upto n = natural n
   multiples_upto_m_0  |- !m. m multiples_upto 0 = {}
   multiples_upto_m_1  |- !m. m multiples_upto 1 = if m = 1 then {1} else {}
   multiples_upto_thm  |- !m n. m multiples_upto n =
                                if m = 0 then {} else IMAGE ($* m) (natural (n DIV m))
   multiples_upto_subset
                       |- !m n. m multiples_upto n SUBSET natural n
   multiples_upto_finite
                       |- !m n. FINITE (m multiples_upto n)
   multiples_upto_card |- !m n. CARD (m multiples_upto n) = if m = 0 then 0 else n DIV m
   coprimes_prime_power|- !p n. prime p ==>
                                coprimes (p ** n) = natural (p ** n) DIFF p multiples_upto p ** n
   phi_prime_power     |- !p n. prime p ==> phi (p ** SUC n) = (p - 1) * p ** n
   phi_prime_sq        |- !p. prime p ==> phi (p * p) = p * (p - 1)
   phi_primes          |- !p q. prime p /\ prime q ==>
                                phi (p * q) = if p = q then p * (p - 1) else (p - 1) * (q - 1)

   Recursive definition of phi:
   rec_phi_def      |- !n. rec_phi n = if n = 0 then 0
                                  else if n = 1 then 1
                                  else n - SIGMA (\a. rec_phi a) {m | m < n /\ m divides n}
   rec_phi_0        |- rec_phi 0 = 0
   rec_phi_1        |- rec_phi 1 = 1
   rec_phi_eq_phi   |- !n. rec_phi n = phi n

   Useful Theorems:
   coprimes_from_not_1_inj     |- INJ coprimes (univ(:num) DIFF {1}) univ(:num -> bool)
   divisors_eq_image_gcd_upto  |- !n. 0 < n ==> divisors n = IMAGE (gcd n) (upto n)
   gcd_eq_equiv_on_upto        |- !n. feq (gcd n) equiv_on upto n
   gcd_eq_upto_partition_by_divisors
                               |- !n. 0 < n ==>
                                      partition (feq (gcd n)) (upto n) =
                                      IMAGE (preimage (gcd n) (upto n)) (divisors n)
   sum_over_upto_by_gcd_partition
                               |- !f n. SIGMA f (upto n) =
                                        SIGMA (SIGMA f) (partition (feq (gcd n)) (upto n))
   sum_over_upto_by_divisors   |- !f n. 0 < n ==>
                                        SIGMA f (upto n) =
                                        SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (upto n)) (divisors n))

   divisors_eq_image_gcd_count |- !n. divisors n = IMAGE (gcd n) (count n)
   gcd_eq_equiv_on_count       |- !n. feq (gcd n) equiv_on count n
   gcd_eq_count_partition_by_divisors
                               |- !n. partition (feq (gcd n)) (count n) =
                                      IMAGE (preimage (gcd n) (count n)) (divisors n)
   sum_over_count_by_gcd_partition
                               |- !f n. SIGMA f (count n) =
                                        SIGMA (SIGMA f) (partition (feq (gcd n)) (count n))
   sum_over_count_by_divisors  |- !f n. SIGMA f (count n) =
                                        SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (count n)) (divisors n))

   divisors_eq_image_gcd_natural
                               |- !n. divisors n = IMAGE (gcd n) (natural n)
   gcd_eq_natural_partition_by_divisors
                               |- !n. partition (feq (gcd n)) (natural n) =
                                      IMAGE (preimage (gcd n) (natural n)) (divisors n)
   sum_over_natural_by_preimage_divisors
                               |- !f n. SIGMA f (natural n) =
                                        SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (natural n)) (divisors n))
   sum_image_divisors_cong     |- !f g. f 0 = g 0 /\ (!n. SIGMA f (divisors n) = SIGMA g (divisors n)) ==> f = g
*)

(* Theory:

Given the set natural 6 = {1, 2, 3, 4, 5, 6}
Every element has a gcd with 6: IMAGE (gcd 6) (natural 6) = {1, 2, 3, 2, 1, 6} = {1, 2, 3, 6}.
Thus the original set is partitioned by gcd: {{1, 5}, {2, 4}, {3}, {6}}
Since (gcd 6) j is a divisor of 6, and they run through all possible divisors of 6,
  SIGMA f (natural 6)
= f 1 + f 2 + f 3 + f 4 + f 5 + f 6
= (f 1 + f 5) + (f 2 + f 4) + f 3 + f 6
= (SIGMA f {1, 5}) + (SIGMA f {2, 4}) + (SIGMA f {3}) + (SIGMA f {6})
= SIGMA (SIGMA f) {{1, 5}, {2, 4}, {3}, {6}}
= SIGMA (SIGMA f) (partition (feq (natural 6) (gcd 6)) (natural 6))

SIGMA:('a -> num) -> ('a -> bool) -> num
SIGMA (f:num -> num):(num -> bool) -> num
SIGMA (SIGMA (f:num -> num)) (s:(num -> bool) -> bool):num

How to relate this to (divisors n) ?
First, observe   IMAGE (gcd 6) (natural 6) = divisors 6
and partition {{1, 5}, {2, 4}, {3}, {6}} = IMAGE (preimage (gcd 6) (natural 6)) (divisors 6)

  SIGMA f (natural 6)
= SIGMA (SIGMA f) (partition (feq (natural 6) (gcd 6)) (natural 6))
= SIGMA (SIGMA f) (IMAGE (preimage (gcd 6) (natural 6)) (divisors 6))

divisors n:num -> bool
preimage (gcd n):(num -> bool) -> num -> num -> bool
preimage (gcd n) (natural n):num -> num -> bool
IMAGE (preimage (gcd n) (natural n)) (divisors n):(num -> bool) -> bool

How to relate this to (coprimes d), where d divides n ?
Note {1, 5} with (gcd 6) j = 1, equals to (coprimes (6 DIV 1)) = coprimes 6
     {2, 4} with (gcd 6) j = 2, BIJ to {2/2, 4/2} with gcd (6/2) (j/2) = 1, i.e {1, 2} = coprimes 3
     {3} with (gcd 6) j = 3, BIJ to {3/3} with gcd (6/3) (j/3) = 1, i.e. {1} = coprimes 2
     {6} with (gcd 6) j = 6, BIJ to {6/6} with gcd (6/6) (j/6) = 1, i.e. {1} = coprimes 1
Hence CARD {{1, 5}, {2, 4}, {3}, {6}} = CARD (partition)
    = CARD {{1, 5}/1, {2,4}/2, {3}/3, {6}/6} = CARD (reduced-partition)
    = CARD {(coprimes 6/1) (coprimes 6/2) (coprimes 6/3) (coprimes 6/6)}
    = CARD {(coprimes 6) (coprimes 3) (coprimes 2) (coprimes 1)}
    = SIGMA (CARD (coprimes d)), over d divides 6)
    = SIGMA (phi d), over d divides 6.
*)


(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Coprimes                                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define the coprimes set: integers from 1 to n that are coprime to n *)
(*
val coprimes_def = zDefine `
   coprimes n = {j | 0 < j /\ j <= n /\ coprime j n}
`;
*)
(* Note: j <= n ensures that coprimes n is finite. *)
(* Note: 0 < j is only to ensure  coprimes 1 = {1} *)
val coprimes_def = zDefine `
   coprimes n = {j | j IN (natural n) /\ coprime j n}
`;
(* use zDefine as this is not computationally effective. *)

(* Theorem: j IN coprimes n <=> 0 < j /\ j <= n /\ coprime j n *)
(* Proof: by coprimes_def, natural_element *)
val coprimes_element = store_thm(
  "coprimes_element",
  ``!n j. j IN coprimes n <=> 0 < j /\ j <= n /\ coprime j n``,
  (rw[coprimes_def, natural_element] >> metis_tac[]));

(* Theorem: coprimes n = (natural n) INTER {j | coprime j n} *)
(* Proof: by coprimes_def, EXTENSION, IN_INTER *)
val coprimes_alt = store_thm(
  "coprimes_alt[compute]",
  ``!n. coprimes n = (natural n) INTER {j | coprime j n}``,
  rw[coprimes_def, EXTENSION]);
(* This is effective, put in computeLib. *)

(*
> EVAL ``coprimes 10``;
val it = |- coprimes 10 = {9; 7; 3; 1}: thm
*)

(* Theorem: coprimes n = set (FILTER (\j. coprime j n) (GENLIST SUC n)) *)
(* Proof:
     coprimes n
   = (natural n) INTER {j | coprime j n}             by coprimes_alt
   = (set (GENLIST SUC n)) INTER {j | coprime j n}   by natural_thm
   = {j | coprime j n} INTER (set (GENLIST SUC n))   by INTER_COMM
   = set (FILTER (\j. coprime j n) (GENLIST SUC n))  by LIST_TO_SET_FILTER
*)
val coprimes_thm = store_thm(
  "coprimes_thm",
  ``!n. coprimes n = set (FILTER (\j. coprime j n) (GENLIST SUC n))``,
  rw[coprimes_alt, natural_thm, INTER_COMM, LIST_TO_SET_FILTER]);

(* Theorem: coprimes n SUBSET natural n *)
(* Proof: by coprimes_def, SUBSET_DEF *)
val coprimes_subset = store_thm(
  "coprimes_subset",
  ``!n. coprimes n SUBSET natural n``,
  rw[coprimes_def, SUBSET_DEF]);

(* Theorem: FINITE (coprimes n) *)
(* Proof:
   Since (coprimes n) SUBSET (natural n)   by coprimes_subset
     and !n. FINITE (natural n)            by natural_finite
      so FINITE (coprimes n)               by SUBSET_FINITE
*)
val coprimes_finite = store_thm(
  "coprimes_finite",
  ``!n. FINITE (coprimes n)``,
  metis_tac[coprimes_subset, natural_finite, SUBSET_FINITE]);

(* Theorem: coprimes 0 = {} *)
(* Proof:
   By coprimes_element, 0 < j /\ j <= 0,
   which is impossible, hence empty.
*)
val coprimes_0 = store_thm(
  "coprimes_0",
  ``coprimes 0 = {}``,
  rw[coprimes_element, EXTENSION]);

(* Theorem: coprimes 1 = {1} *)
(* Proof:
   By coprimes_element, 0 < j /\ j <= 1,
   Only possible j is 1, and gcd 1 1 = 1.
 *)
val coprimes_1 = store_thm(
  "coprimes_1",
  ``coprimes 1 = {1}``,
  rw[coprimes_element, EXTENSION]);

(* Theorem: 0 < n ==> 1 IN (coprimes n) *)
(* Proof: by coprimes_element, GCD_1 *)
val coprimes_has_1 = store_thm(
  "coprimes_has_1",
  ``!n. 0 < n ==> 1 IN (coprimes n)``,
  rw[coprimes_element]);

(* Theorem: (coprimes n = {}) <=> (n = 0) *)
(* Proof:
   If part: coprimes n = {} ==> n = 0
      By contradiction.
      Suppose n <> 0, then 0 < n.
      Then 1 IN (coprimes n)    by coprimes_has_1
      hence (coprimes n) <> {}  by MEMBER_NOT_EMPTY
      This contradicts (coprimes n) = {}.
   Only-if part: n = 0 ==> coprimes n = {}
      True by coprimes_0
*)
val coprimes_eq_empty = store_thm(
  "coprimes_eq_empty",
  ``!n. (coprimes n = {}) <=> (n = 0)``,
  rw[EQ_IMP_THM] >-
  metis_tac[coprimes_has_1, MEMBER_NOT_EMPTY, NOT_ZERO_LT_ZERO] >>
  rw[coprimes_0]);

(* Theorem: 0 NOTIN (coprimes n) *)
(* Proof:
   By coprimes_element, 0 < j /\ j <= n,
   Hence j <> 0, or 0 NOTIN (coprimes n)
*)
val coprimes_no_0 = store_thm(
  "coprimes_no_0",
  ``!n. 0 NOTIN (coprimes n)``,
  rw[coprimes_element]);

(* Theorem: 1 < n ==> n NOTIN coprimes n *)
(* Proof:
   By coprimes_element, 0 < j /\ j <= n /\ gcd j n = 1
   If j = n,  1 = gcd j n = gcd n n = n     by GCD_REF
   which is excluded by 1 < n, so j <> n.
*)
val coprimes_without_last = store_thm(
  "coprimes_without_last",
  ``!n. 1 < n ==> n NOTIN coprimes n``,
  rw[coprimes_element]);

(* Theorem: n IN coprimes n <=> (n = 1) *)
(* Proof:
   By coprimes_element, 0 < j /\ j <= n /\ gcd j n = 1
   If n IN coprimes n, 1 = gcd j n = gcd n n = n     by GCD_REF
   If n = 1, 0 < n, n <= n, and gcd n n = n = 1      by GCD_REF
*)
val coprimes_with_last = store_thm(
  "coprimes_with_last",
  ``!n. n IN coprimes n <=> (n = 1)``,
  rw[coprimes_element]);

(* Theorem: 1 < n ==> (n - 1) IN (coprimes n) *)
(* Proof: by coprimes_element, coprime_PRE, GCD_SYM *)
val coprimes_has_last_but_1 = store_thm(
  "coprimes_has_last_but_1",
  ``!n. 1 < n ==> (n - 1) IN (coprimes n)``,
  rpt strip_tac >>
  `0 < n /\ 0 < n - 1` by decide_tac >>
  rw[coprimes_element, coprime_PRE, GCD_SYM]);

(* Theorem: 1 < n ==> !j. j IN coprimes n ==> j < n *)
(* Proof:
   Since j IN coprimes n ==> j <= n    by coprimes_element
   If j = n, then gcd n n = n <> 1     by GCD_REF
   Thus j <> n, or j < n.              or by coprimes_without_last
*)
val coprimes_element_less = store_thm(
  "coprimes_element_less",
  ``!n. 1 < n ==> !j. j IN coprimes n ==> j < n``,
  metis_tac[coprimes_element, coprimes_without_last, LESS_OR_EQ]);

(* Theorem: 1 < n ==> !j. j IN coprimes n <=> j < n /\ coprime j n *)
(* Proof:
   If part: j IN coprimes n ==> j < n /\ coprime j n
      Note 0 < j /\ j <= n /\ coprime j n      by coprimes_element
      By contradiction, suppose n <= j.
      Then j = n, but gcd n n = n <> 1         by GCD_REF
   Only-if part: j < n /\ coprime j n ==> j IN coprimes n
      This is to show:
           0 < j /\ j <= n /\ coprime j n      by coprimes_element
      By contradiction, suppose ~(0 < j).
      Then j = 0, but gcd 0 n = n <> 1         by GCD_0L
*)
val coprimes_element_alt = store_thm(
  "coprimes_element_alt",
  ``!n. 1 < n ==> !j. j IN coprimes n <=> j < n /\ coprime j n``,
  rw[coprimes_element] >>
  `n <> 1` by decide_tac >>
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `j = n` by decide_tac >>
    metis_tac[GCD_REF],
    spose_not_then strip_assume_tac >>
    `j = 0` by decide_tac >>
    metis_tac[GCD_0L]
  ]);

(* Theorem: 1 < n ==> (MAX_SET (coprimes n) = n - 1) *)
(* Proof:
   Let s = coprimes n, m = MAX_SET s.
    Note (n - 1) IN s     by coprimes_has_last_but_1, 1 < n
   Hence s <> {}          by MEMBER_NOT_EMPTY
     and FINITE s         by coprimes_finite
   Since !x. x IN s ==> x < n         by coprimes_element_less, 1 < n
    also !x. x < n ==> x <= (n - 1)   by SUB_LESS_OR
   Therefore MAX_SET s = n - 1        by MAX_SET_TEST
*)
val coprimes_max = store_thm(
  "coprimes_max",
  ``!n. 1 < n ==> (MAX_SET (coprimes n) = n - 1)``,
  rpt strip_tac >>
  qabbrev_tac `s = coprimes n` >>
  `(n - 1) IN s` by rw[coprimes_has_last_but_1, Abbr`s`] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `FINITE s` by rw[coprimes_finite, Abbr`s`] >>
  `!x. x IN s ==> x < n` by rw[coprimes_element_less, Abbr`s`] >>
  `!x. x < n ==> x <= (n - 1)` by decide_tac >>
  metis_tac[MAX_SET_TEST]);

(* Relate coprimes to Euler totient *)

(* Theorem: 1 < n ==> (coprimes n = Euler n) *)
(* Proof:
   By Euler_def, this is to show:
   (1) x IN coprimes n ==> 0 < x, true by coprimes_element
   (2) x IN coprimes n ==> x < n, true by coprimes_element_less
   (3) x IN coprimes n ==> coprime n x, true by coprimes_element, GCD_SYM
   (4) 0 < x /\ x < n /\ coprime n x ==> x IN coprimes n
       That is, to show: 0 < x /\ x <= n /\ coprime x n.
       Since x < n ==> x <= n   by LESS_IMP_LESS_OR_EQ
       Hence true by GCD_SYM
*)
val coprimes_eq_Euler = store_thm(
  "coprimes_eq_Euler",
  ``!n. 1 < n ==> (coprimes n = Euler n)``,
  rw[Euler_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[coprimes_element] >-
  rw[coprimes_element_less] >-
  metis_tac[coprimes_element, GCD_SYM] >>
  metis_tac[coprimes_element, GCD_SYM, LESS_IMP_LESS_OR_EQ]);

(* Theorem: prime n ==> (coprimes n = residue n) *)
(* Proof:
   Since prime n ==> 1 < n     by ONE_LT_PRIME
   Hence   coprimes n
         = Euler n             by coprimes_eq_Euler
         = residue n           by Euler_prime
*)
val coprimes_prime = store_thm(
  "coprimes_prime",
  ``!n. prime n ==> (coprimes n = residue n)``,
  rw[ONE_LT_PRIME, coprimes_eq_Euler, Euler_prime]);

(* ------------------------------------------------------------------------- *)
(* Coprimes by a divisor                                                     *)
(* ------------------------------------------------------------------------- *)

(* Define the set of coprimes by a divisor of n *)
val coprimes_by_def = Define `
    coprimes_by n d = if (0 < n /\ d divides n) then coprimes (n DIV d) else {}
`;

(*
EVAL ``coprimes_by 10 2``; = {4; 3; 2; 1}
EVAL ``coprimes_by 10 5``; = {1}
*)

(* Theorem: j IN (coprimes_by n d) <=> (0 < n /\ d divides n /\ j IN coprimes (n DIV d)) *)
(* Proof: by coprimes_by_def, MEMBER_NOT_EMPTY *)
val coprimes_by_element = store_thm(
  "coprimes_by_element",
  ``!n d j. j IN (coprimes_by n d) <=> (0 < n /\ d divides n /\ j IN coprimes (n DIV d))``,
  metis_tac[coprimes_by_def, MEMBER_NOT_EMPTY]);

(* Theorem: FINITE (coprimes_by n d) *)
(* Proof:
   From coprimes_by_def, this follows by:
   (1) !k. FINITE (coprimes k)  by coprimes_finite
   (2) FINITE {}                by FINITE_EMPTY
*)
val coprimes_by_finite = store_thm(
  "coprimes_by_finite",
  ``!n d. FINITE (coprimes_by n d)``,
  rw[coprimes_by_def, coprimes_finite]);

(* Theorem: coprimes_by 0 d = {} *)
(* Proof: by coprimes_by_def *)
val coprimes_by_0 = store_thm(
  "coprimes_by_0",
  ``!d. coprimes_by 0 d = {}``,
  rw[coprimes_by_def]);

(* Theorem: coprimes_by n 0 = {} *)
(* Proof:
     coprimes_by n 0
   = if 0 < n /\ 0 divides n then coprimes (n DIV 0) else {}
   = 0 < 0 then coprimes (n DIV 0) else {}    by ZERO_DIVIDES
   = {}                                       by prim_recTheory.LESS_REFL
*)
val coprimes_by_by_0 = store_thm(
  "coprimes_by_by_0",
  ``!n. coprimes_by n 0 = {}``,
  rw[coprimes_by_def]);

(* Theorem: 0 < n ==> (coprimes_by n 1 = coprimes n) *)
(* Proof:
   Since 1 divides n       by ONE_DIVIDES_ALL
       coprimes_by n 1
     = coprimes (n DIV 1)  by coprimes_by_def
     = coprimes n          by DIV_ONE, ONE
*)
val coprimes_by_by_1 = store_thm(
  "coprimes_by_by_1",
  ``!n. 0 < n ==> (coprimes_by n 1 = coprimes n)``,
  rw[coprimes_by_def]);

(* Theorem: 0 < n ==> (coprimes_by n n = {1}) *)
(* Proof:
   Since n divides n       by DIVIDES_REFL
       coprimes_by n n
     = coprimes (n DIV n)  by coprimes_by_def
     = coprimes 1          by DIVMOD_ID, 0 < n
     = {1}                 by coprimes_1
*)
val coprimes_by_by_last = store_thm(
  "coprimes_by_by_last",
  ``!n. 0 < n ==> (coprimes_by n n = {1})``,
  rw[coprimes_by_def, coprimes_1]);

(* Theorem: 0 < n /\ d divides n ==> (coprimes_by n d = coprimes (n DIV d)) *)
(* Proof: by coprimes_by_def *)
val coprimes_by_by_divisor = store_thm(
  "coprimes_by_by_divisor",
  ``!n d. 0 < n /\ d divides n ==> (coprimes_by n d = coprimes (n DIV d))``,
  rw[coprimes_by_def]);

(* Theorem: 0 < n ==> ((coprimes_by n d = {}) <=> ~(d divides n)) *)
(* Proof:
   If part: 0 < n /\ coprimes_by n d = {} ==> ~(d divides n)
      By contradiction. Suppose d divides n.
      Then d divides n and 0 < n means
           0 < d /\ d <= n                           by divides_pos, 0 < n
      Also coprimes_by n d = coprimes (n DIV d)      by coprimes_by_def
        so coprimes (n DIV d) = {} <=> n DIV d = 0   by coprimes_eq_empty
      Thus n < d                                     by DIV_EQUAL_0
      which contradicts d <= n.
   Only-if part: 0 < n /\ ~(d divides n) ==> coprimes n d = {}
      This follows by coprimes_by_def
*)
val coprimes_by_eq_empty = store_thm(
  "coprimes_by_eq_empty",
  ``!n d. 0 < n ==> ((coprimes_by n d = {}) <=> ~(d divides n))``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `0 < d /\ d <= n` by metis_tac[divides_pos] >>
    `n DIV d = 0` by metis_tac[coprimes_by_def, coprimes_eq_empty] >>
    `n < d` by rw[GSYM DIV_EQUAL_0] >>
    decide_tac,
    rw[coprimes_by_def]
  ]);

(* ------------------------------------------------------------------------- *)
(* GCD Equivalence Class                                                     *)
(* ------------------------------------------------------------------------- *)

(* Define the set of values with the same gcd *)
val gcd_matches_def = zDefine `
    gcd_matches n d = {j| j IN (natural n) /\ (gcd j n = d)}
`;
(* use zDefine as this is not computationally effective. *)

(* Theorem: gcd_matches n d = (natural n) INTER {j | gcd j n = d} *)
(* Proof: by gcd_matches_def *)
Theorem gcd_matches_alt[compute]:
  !n d. gcd_matches n d = (natural n) INTER {j | gcd j n = d}
Proof
  simp[gcd_matches_def, EXTENSION]
QED

(*
EVAL ``gcd_matches 10 2``; = {8; 6; 4; 2}
EVAL ``gcd_matches 10 5``; = {5}
*)

(* Theorem: j IN gcd_matches n d <=> 0 < j /\ j <= n /\ (gcd j n = d) *)
(* Proof: by gcd_matches_def *)
val gcd_matches_element = store_thm(
  "gcd_matches_element",
  ``!n d j. j IN gcd_matches n d <=> 0 < j /\ j <= n /\ (gcd j n = d)``,
  rw[gcd_matches_def, natural_element]);

(* Theorem: (gcd_matches n d) SUBSET (natural n) *)
(* Proof: by gcd_matches_def, SUBSET_DEF *)
val gcd_matches_subset = store_thm(
  "gcd_matches_subset",
  ``!n d. (gcd_matches n d) SUBSET (natural n)``,
  rw[gcd_matches_def, SUBSET_DEF]);

(* Theorem: FINITE (gcd_matches n d) *)
(* Proof:
   Since (gcd_matches n d) SUBSET (natural n)   by coprimes_subset
     and !n. FINITE (natural n)                 by natural_finite
      so FINITE (gcd_matches n d)               by SUBSET_FINITE
*)
val gcd_matches_finite = store_thm(
  "gcd_matches_finite",
  ``!n d. FINITE (gcd_matches n d)``,
  metis_tac[gcd_matches_subset, natural_finite, SUBSET_FINITE]);

(* Theorem: gcd_matches 0 d = {} *)
(* Proof:
       j IN gcd_matches 0 d
   <=> 0 < j /\ j <= 0 /\ (gcd j 0 = d)   by gcd_matches_element
   Since no j can satisfy this, the set is empty.
*)
val gcd_matches_0 = store_thm(
  "gcd_matches_0",
  ``!d. gcd_matches 0 d = {}``,
  rw[gcd_matches_element, EXTENSION]);

(* Theorem: gcd_matches n 0 = {} *)
(* Proof:
       x IN gcd_matches n 0
   <=> 0 < x /\ x <= n /\ (gcd x n = 0)        by gcd_matches_element
   <=> 0 < x /\ x <= n /\ (x = 0) /\ (n = 0)   by GCD_EQ_0
   <=> F                                       by 0 < x, x = 0
   Hence gcd_matches n 0 = {}                  by EXTENSION
*)
val gcd_matches_with_0 = store_thm(
  "gcd_matches_with_0",
  ``!n. gcd_matches n 0 = {}``,
  rw[EXTENSION, gcd_matches_element]);

(* Theorem: gcd_matches 1 d = if d = 1 then {1} else {} *)
(* Proof:
       j IN gcd_matches 1 d
   <=> 0 < j /\ j <= 1 /\ (gcd j 1 = d)   by gcd_matches_element
   Only j to satisfy this is j = 1.
   and d = gcd 1 1 = 1                    by GCD_REF
   If d = 1, j = 1 is the only element.
   If d <> 1, the only element is taken out, set is empty.
*)
val gcd_matches_1 = store_thm(
  "gcd_matches_1",
  ``!d. gcd_matches 1 d = if d = 1 then {1} else {}``,
  rw[gcd_matches_element, EXTENSION]);

(* Theorem: 0 < n /\ d divides n ==> d IN (gcd_matches n d) *)
(* Proof:
   Note  0 < n /\ d divides n
     ==> 0 < d, and d <= n           by divides_pos
     and gcd d n = d                 by divides_iff_gcd_fix
   Hence d IN (gcd_matches n d)      by gcd_matches_element
*)
val gcd_matches_has_divisor = store_thm(
  "gcd_matches_has_divisor",
  ``!n d. 0 < n /\ d divides n ==> d IN (gcd_matches n d)``,
  rw[gcd_matches_element] >-
  metis_tac[divisor_pos] >-
  rw[DIVIDES_LE] >>
  rw[GSYM divides_iff_gcd_fix]);

(* Theorem: j IN (gcd_matches n d) ==> d divides j /\ d divides n *)
(* Proof:
   If j IN (gcd_matches n d), gcd j n = d    by gcd_matches_element
   This means d divides j /\ d divides n     by GCD_IS_GREATEST_COMMON_DIVISOR
*)
val gcd_matches_element_divides = store_thm(
  "gcd_matches_element_divides",
  ``!n d j. j IN (gcd_matches n d) ==> d divides j /\ d divides n``,
  metis_tac[gcd_matches_element, GCD_IS_GREATEST_COMMON_DIVISOR]);

(* Theorem: 0 < n ==> ((gcd_matches n d = {}) <=> ~(d divides n)) *)
(* Proof:
   If part: 0 < n /\ (gcd_matches n d = {}) ==> ~(d divides n)
      By contradiction, suppose d divides n.
      Then d IN gcd_matches n d               by gcd_matches_has_divisor
      This contradicts gcd_matches n d = {}   by MEMBER_NOT_EMPTY
   Only-if part: 0 < n /\ ~(d divides n) ==> (gcd_matches n d = {})
      By contradiction, suppose gcd_matches n d <> {}.
      Then ?j. j IN (gcd_matches n d)         by MEMBER_NOT_EMPTY
      Giving d divides j /\ d divides n       by gcd_matches_element_divides
      This contradicts ~(d divides n).
*)
val gcd_matches_eq_empty = store_thm(
  "gcd_matches_eq_empty",
  ``!n d. 0 < n ==> ((gcd_matches n d = {}) <=> ~(d divides n))``,
  rw[EQ_IMP_THM] >-
  metis_tac[gcd_matches_has_divisor, MEMBER_NOT_EMPTY] >>
  metis_tac[gcd_matches_element_divides, MEMBER_NOT_EMPTY]);

(* ------------------------------------------------------------------------- *)
(* Phi Function                                                              *)
(* ------------------------------------------------------------------------- *)

(* Define the Euler phi function from coprime set *)
val phi_def = Define `
   phi n = CARD (coprimes n)
`;
(* Since (coprimes n) is computable, phi n is now computable *)

(*
> EVAL ``phi 10``;
val it = |- phi 10 = 4: thm
*)

(* Theorem: phi n = LENGTH (FILTER (\j. coprime j n) (GENLIST SUC n)) *)
(* Proof:
   Let ls = FILTER (\j. coprime j n) (GENLIST SUC n).
   Note ALL_DISTINCT (GENLIST SUC n)       by ALL_DISTINCT_GENLIST, SUC_EQ
   Thus ALL_DISTINCT ls                    by FILTER_ALL_DISTINCT
     phi n = CARD (coprimes n)             by phi_def
           = CARD (set ls)                 by coprimes_thm
           = LENGTH ls                     by ALL_DISTINCT_CARD_LIST_TO_SET
*)
val phi_thm = store_thm(
  "phi_thm",
  ``!n. phi n = LENGTH (FILTER (\j. coprime j n) (GENLIST SUC n))``,
  rpt strip_tac >>
  qabbrev_tac `ls = FILTER (\j. coprime j n) (GENLIST SUC n)` >>
  `ALL_DISTINCT ls` by rw[ALL_DISTINCT_GENLIST, FILTER_ALL_DISTINCT, Abbr`ls`] >>
  `phi n = CARD (coprimes n)` by rw[phi_def] >>
  `_ = CARD (set ls)` by rw[coprimes_thm, Abbr`ls`] >>
  `_ = LENGTH ls` by rw[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  decide_tac);

(* Theorem: phi = CARD o coprimes *)
(* Proof: by phi_def, FUN_EQ_THM *)
val phi_fun = store_thm(
  "phi_fun",
  ``phi = CARD o coprimes``,
  rw[phi_def, FUN_EQ_THM]);

(* Theorem: 0 < n ==> 0 < phi n *)
(* Proof:
   Since 1 IN coprimes n       by coprimes_has_1
      so coprimes n <> {}      by MEMBER_NOT_EMPTY
     and FINITE (coprimes n)   by coprimes_finite
   hence phi n <> 0            by CARD_EQ_0
      or 0 < phi n
*)
val phi_pos = store_thm(
  "phi_pos",
  ``!n. 0 < n ==> 0 < phi n``,
  rpt strip_tac >>
  `coprimes n <> {}` by metis_tac[coprimes_has_1, MEMBER_NOT_EMPTY] >>
  `FINITE (coprimes n)` by rw[coprimes_finite] >>
  `phi n <> 0` by rw[phi_def, CARD_EQ_0] >>
  decide_tac);

(* Theorem: phi 0 = 0 *)
(* Proof:
     phi 0
   = CARD (coprimes 0)   by phi_def
   = CARD {}             by coprimes_0
   = 0                   by CARD_EMPTY
*)
val phi_0 = store_thm(
  "phi_0",
  ``phi 0 = 0``,
  rw[phi_def, coprimes_0]);

(* Theorem: (phi n = 0) <=> (n = 0) *)
(* Proof:
   If part: (phi n = 0) ==> (n = 0)    by phi_pos, NOT_ZERO_LT_ZERO
   Only-if part: phi 0 = 0             by phi_0
*)
val phi_eq_0 = store_thm(
  "phi_eq_0",
  ``!n. (phi n = 0) <=> (n = 0)``,
  metis_tac[phi_0, phi_pos, NOT_ZERO_LT_ZERO]);

(* Theorem: phi 1 = 1 *)
(* Proof:
     phi 1
   = CARD (coprimes 1)    by phi_def
   = CARD {1}             by coprimes_1
   = 1                    by CARD_SING
*)
val phi_1 = store_thm(
  "phi_1",
  ``phi 1 = 1``,
  rw[phi_def, coprimes_1]);

(* Theorem: 1 < n ==> (phi n = totient n) *)
(* Proof:
      phi n
    = CARD (coprimes n)     by phi_def
    = CARD (Euler n )       by coprimes_eq_Euler
    = totient n             by totient_def
*)
val phi_eq_totient = store_thm(
  "phi_eq_totient",
  ``!n. 1 < n ==> (phi n = totient n)``,
  rw[phi_def, totient_def, coprimes_eq_Euler]);

(* Theorem: prime n ==> (phi n = n - 1) *)
(* Proof:
   Since prime n ==> 1 < n   by ONE_LT_PRIME
   Hence   phi n
         = totient n         by phi_eq_totient
         = n - 1             by Euler_card_prime
*)
val phi_prime = store_thm(
  "phi_prime",
  ``!n. prime n ==> (phi n = n - 1)``,
  rw[ONE_LT_PRIME, phi_eq_totient, Euler_card_prime]);

(* Theorem: phi 2 = 1 *)
(* Proof:
   Since prime 2               by PRIME_2
      so phi 2 = 2 - 1 = 1     by phi_prime
*)
val phi_2 = store_thm(
  "phi_2",
  ``phi 2 = 1``,
  rw[phi_prime, PRIME_2]);

(* Theorem: 2 < n ==> 1 < phi n *)
(* Proof:
   Note 1 IN (coprimes n)        by coprimes_has_1, 0 < n
    and (n - 1) IN (coprimes n)  by coprimes_has_last_but_1, 1 < n
    and n - 1 <> 1               by 2 < n
    Now FINITE (coprimes n)      by coprimes_finite]
    and {1; (n-1)} SUBSET (coprimes n)   by SUBSET_DEF, above
   Note CARD {1; (n-1)} = 2      by CARD_INSERT, CARD_EMPTY, TWO
   thus 2 <= CARD (coprimes n)   by CARD_SUBSET
     or 1 < phi n                by phi_def
*)
val phi_gt_1 = store_thm(
  "phi_gt_1",
  ``!n. 2 < n ==> 1 < phi n``,
  rw[phi_def] >>
  `0 < n /\ 1 < n /\ n - 1 <> 1` by decide_tac >>
  `1 IN (coprimes n)` by rw[coprimes_has_1] >>
  `(n - 1) IN (coprimes n)` by rw[coprimes_has_last_but_1] >>
  `FINITE (coprimes n)` by rw[coprimes_finite] >>
  `{1; (n-1)} SUBSET (coprimes n)` by rw[SUBSET_DEF] >>
  `CARD {1; (n-1)} = 2` by rw[] >>
  `2 <= CARD (coprimes n)` by metis_tac[CARD_SUBSET] >>
  decide_tac);

(* Theorem: phi n <= n *)
(* Proof:
   Note phi n = CARD (coprimes n)    by phi_def
    and coprimes n SUBSET natural n  by coprimes_subset
    Now FINITE (natural n)           by natural_finite
    and CARD (natural n) = n         by natural_card
     so CARD (coprimes n) <= n       by CARD_SUBSET
*)
val phi_le = store_thm(
  "phi_le",
  ``!n. phi n <= n``,
  metis_tac[phi_def, coprimes_subset, natural_finite, natural_card, CARD_SUBSET]);

(* Theorem: 1 < n ==> phi n < n *)
(* Proof:
   Note phi n = CARD (coprimes n)    by phi_def
    and 1 < n ==> !j. j IN coprimes n ==> j < n     by coprimes_element_less
    but 0 NOTIN coprimes n           by coprimes_no_0
     or coprimes n SUBSET (count n) DIFF {0}  by SUBSET_DEF, IN_DIFF
    Let s = (count n) DIFF {0}.
   Note {0} SUBSET count n           by SUBSET_DEF]);
     so count n INTER {0} = {0}      by SUBSET_INTER_ABSORPTION
    Now FINITE s                     by FINITE_COUNT, FINITE_DIFF
    and CARD s = n - 1               by CARD_COUNT, CARD_DIFF, CARD_SING
     so CARD (coprimes n) <= n - 1   by CARD_SUBSET
     or phi n < n                    by arithmetic
*)
val phi_lt = store_thm(
  "phi_lt",
  ``!n. 1 < n ==> phi n < n``,
  rw[phi_def] >>
  `!j. j IN coprimes n ==> j < n` by rw[coprimes_element_less] >>
  `!j. j IN coprimes n ==> j <> 0` by metis_tac[coprimes_no_0] >>
  qabbrev_tac `s = (count n) DIFF {0}` >>
  `coprimes n SUBSET s` by rw[SUBSET_DEF, Abbr`s`] >>
  `{0} SUBSET count n` by rw[SUBSET_DEF] >>
  `count n INTER {0} = {0}` by metis_tac[SUBSET_INTER_ABSORPTION, INTER_COMM] >>
  `FINITE s` by rw[Abbr`s`] >>
  `CARD s = n - 1` by rw[Abbr`s`] >>
  `CARD (coprimes n) <= n - 1` by metis_tac[CARD_SUBSET] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Divisors                                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define the set of divisors of a number. *)
Definition divisors_def[nocompute]:
   divisors n = {d | 0 < d /\ d <= n /\ d divides n}
End
(* use [nocompute] as this is not computationally effective. *)
(* Note: use of 0 < d to have positive divisors, as only 0 divides 0. *)
(* Note: use of d <= n to give divisors_0 = {}, since ALL_DIVIDES_0. *)
(* Note: for 0 < n, d <= n is redundant, as DIVIDES_LE implies it. *)

(* Theorem: d IN divisors n <=> 0 < d /\ d <= n /\ d divides n *)
(* Proof: by divisors_def *)
Theorem divisors_element:
  !n d. d IN divisors n <=> 0 < d /\ d <= n /\ d divides n
Proof
  rw[divisors_def]
QED

(* Theorem: 0 < n ==> !d. d IN divisors n <=> d divides n *)
(* Proof:
   If part: d IN divisors n ==> d divides n
      This is true                 by divisors_element
   Only-if part: 0 < n /\ d divides n ==> d IN divisors n
      Since 0 < n /\ d divides n
        ==> 0 < d /\ d <= n        by divides_pos
      Hence d IN divisors n        by divisors_element
*)
Theorem divisors_element_alt:
  !n. 0 < n ==> !d. d IN divisors n <=> d divides n
Proof
  metis_tac[divisors_element, divides_pos]
QED

(* Theorem: d IN divisors n ==> 0 < n *)
(* Proof:
   Note 0 < d /\ d <= n /\ d divides n         by divisors_def
     so 0 < n                                  by inequality
*)
Theorem divisors_has_element:
  !n d. d IN divisors n ==> 0 < n
Proof
  simp[divisors_def]
QED

(* Theorem: 0 < n ==> 1 IN (divisors n) *)
(* Proof:
    Note 1 divides n         by ONE_DIVIDES_ALL
   Hence 1 IN (divisors n)   by divisors_element_alt
*)
Theorem divisors_has_1:
  !n. 0 < n ==> 1 IN (divisors n)
Proof
  simp[divisors_element_alt]
QED

(* Theorem: 0 < n ==> n IN (divisors n) *)
(* Proof:
    Note n divides n         by DIVIDES_REFL
   Hence n IN (divisors n)   by divisors_element_alt
*)
Theorem divisors_has_last:
  !n. 0 < n ==> n IN (divisors n)
Proof
  simp[divisors_element_alt]
QED

(* Theorem: 0 < n ==> divisors n <> {} *)
(* Proof: by divisors_has_last, MEMBER_NOT_EMPTY *)
Theorem divisors_not_empty:
  !n. 0 < n ==> divisors n <> {}
Proof
  metis_tac[divisors_has_last, MEMBER_NOT_EMPTY]
QED

(* Theorem: divisors 0 = {} *)
(* Proof: by divisors_def, 0 < d /\ d <= 0 is impossible. *)
Theorem divisors_0:
  divisors 0 = {}
Proof
  simp[divisors_def]
QED

(* Theorem: divisors 1 = {1} *)
(* Proof: by divisors_def, 0 < d /\ d <= 1 ==> d = 1. *)
Theorem divisors_1:
  divisors 1 = {1}
Proof
  rw[divisors_def, EXTENSION]
QED

(* Theorem: divisors n = {} <=> n = 0 *)
(* Proof:
   By EXTENSION, this is to show:
   (1) divisors n = {} ==> n = 0
       By contradiction, suppose n <> 0.
       Then 1 IN (divisors n)                  by divisors_has_1
       This contradicts divisors n = {}        by MEMBER_NOT_EMPTY
   (2) n = 0 ==> divisors n = {}
       This is true                            by divisors_0
*)
Theorem divisors_eq_empty:
  !n. divisors n = {} <=> n = 0
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[divisors_has_1, MEMBER_NOT_EMPTY, NOT_ZERO] >>
  simp[divisors_0]
QED

(* Idea: a method to evaluate divisors. *)

(* Theorem: divisors n = IMAGE (\j. if (j + 1) divides n then j + 1 else 1) (count n) *)
(* Proof:
   Let f = \j. if (j + 1) divides n then j + 1 else 1.
   If n = 0,
        divisors 0
      = {d | 0 < d /\ d <= 0 /\ d divides 0}   by divisors_def
      = {}                                     by 0 < d /\ d <= 0
      = IMAGE f {}                             by IMAGE_EMPTY
      = IMAGE f (count 0)                      by COUNT_0
   If n <> 0,
        divisors n
      = {d | 0 < d /\ d <= n /\ d divides n}   by divisors_def
      = {d | d <> 0 /\ d <= n /\ d divides n}  by 0 < d
      = {k + 1 | (k + 1) <= n /\ (k + 1) divides n}
                                               by num_CASES, d <> 0
      = {k + 1 | k < n /\ (k + 1) divides n}   by arithmetic
      = IMAGE f {k | k < n}                    by IMAGE_DEF
      = IMAGE f (count n)                      by count_def
*)
Theorem divisors_eqn[compute]:
  !n. divisors n = IMAGE (\j. if (j + 1) divides n then j + 1 else 1) (count n)
Proof
  (rw[divisors_def, EXTENSION, EQ_IMP_THM] >> rw[]) >>
  `?k. x = SUC k` by metis_tac[num_CASES, NOT_ZERO] >>
  qexists_tac `k` >>
  fs[ADD1]
QED

(*
> EVAL ``divisors 3``; = {3; 1}: thm
> EVAL ``divisors 4``; = {4; 2; 1}: thm
> EVAL ``divisors 5``; = {5; 1}: thm
> EVAL ``divisors 6``; = {6; 3; 2; 1}: thm
> EVAL ``divisors 7``; = {7; 1}: thm
> EVAL ``divisors 8``; = {8; 4; 2; 1}: thm
> EVAL ``divisors 9``; = {9; 3; 1}: thm
*)

(* Idea: each factor of a product divides the product. *)

(* Theorem: 0 < n /\ n = p * q ==> p IN divisors n /\ q IN divisors n *)
(* Proof:
   Note 0 < p /\ 0 < q             by MULT_EQ_0
     so p <= n /\ q <= n           by arithmetic
    and p divides n                by divides_def
    and q divides n                by divides_def, MULT_COMM
    ==> p IN divisors n /\
        q IN divisors n            by divisors_element_alt, 0 < n
*)
Theorem divisors_has_factor:
  !n p q. 0 < n /\ n = p * q ==> p IN divisors n /\ q IN divisors n
Proof
  (rw[divisors_element_alt] >> metis_tac[MULT_EQ_0, NOT_ZERO])
QED

(* Idea: when factor divides, its cofactor also divides. *)

(* Theorem: d IN divisors n ==> (n DIV d) IN divisors n *)
(* Proof:
   Note 0 < d /\ d <= n /\ d divides n         by divisors_def
    and 0 < n                                  by 0 < d /\ d <= n
     so 0 < n DIV d                            by DIV_POS, 0 < n
    and n DIV d <= n                           by DIV_LESS_EQ, 0 < d
    and n DIV d divides n                      by DIVIDES_COFACTOR, 0 < d
     so (n DIV d) IN divisors n                by divisors_def
*)
Theorem divisors_has_cofactor:
  !n d. d IN divisors n ==> (n DIV d) IN divisors n
Proof
  simp [divisors_def] >>
  ntac 3 strip_tac >>
  `0 < n` by decide_tac >>
  rw[DIV_POS, DIV_LESS_EQ, DIVIDES_COFACTOR]
QED

(* Theorem: (divisors n) DELETE n = {m | 0 < m /\ m < n /\ m divides n} *)
(* Proof:
     (divisors n) DELETE n
   = {m | 0 < m /\ m <= n /\ m divides n} DELETE n     by divisors_def
   = {m | 0 < m /\ m <= n /\ m divides n} DIFF {n}     by DELETE_DEF
   = {m | 0 < m /\ m <> n /\ m <= n /\ m divides n}    by IN_DIFF
   = {m | 0 < m /\ m < n /\ m divides n}               by LESS_OR_EQ
*)
Theorem divisors_delete_last:
  !n. (divisors n) DELETE n = {m | 0 < m /\ m < n /\ m divides n}
Proof
  rw[divisors_def, EXTENSION, EQ_IMP_THM]
QED

(* Theorem: d IN (divisors n) ==> 0 < d *)
(* Proof: by divisors_def. *)
Theorem divisors_nonzero:
  !n d. d IN (divisors n) ==> 0 < d
Proof
  simp[divisors_def]
QED

(* Theorem: (divisors n) SUBSET (natural n) *)
(* Proof:
   By SUBSET_DEF, this is to show:
       x IN (divisors n) ==> x IN (natural n)
       x IN (divisors n)
   ==> 0 < x /\ x <= n /\ x divides n          by divisors_element
   ==> 0 < x /\ x <= n
   ==> x IN (natural n)                        by natural_element
*)
Theorem divisors_subset_natural:
  !n. (divisors n) SUBSET (natural n)
Proof
  rw[divisors_element, natural_element, SUBSET_DEF]
QED

(* Theorem: FINITE (divisors n) *)
(* Proof:
   Since (divisors n) SUBSET (natural n)       by divisors_subset_natural
     and FINITE (naturnal n)                   by natural_finite
      so FINITE (divisors n)                   by SUBSET_FINITE
*)
Theorem divisors_finite:
  !n. FINITE (divisors n)
Proof
  metis_tac[divisors_subset_natural, natural_finite, SUBSET_FINITE]
QED

(* Theorem: BIJ (\d. n DIV d) (divisors n) (divisors n) *)
(* Proof:
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) d IN divisors n ==> n DIV d IN divisors n
       This is true                                       by divisors_has_cofactor
   (2) d IN divisors n /\ d' IN divisors n /\ n DIV d = n DIV d' ==> d = d'
       d IN divisors n ==> d divides n /\ 0 < d           by divisors_element
       d' IN divisors n ==> d' divides n /\ 0 < d'        by divisors_element
       Also d IN divisors n ==> 0 < n                     by divisors_has_element
       Hence n = (n DIV d) * d  and n = (n DIV d') * d'   by DIVIDES_EQN
       giving   (n DIV d) * d = (n DIV d') * d'
       Now (n DIV d) <> 0, otherwise contradicts n <> 0   by MULT
       Hence                d = d'                        by EQ_MULT_LCANCEL
   (3) same as (1), true                                  by divisors_has_cofactor
   (4) x IN divisors n ==> ?d. d IN divisors n /\ (n DIV d = x)
       Note x IN divisors n ==> x divides n               by divisors_element
        and 0 < n                                         by divisors_has_element
       Let d = n DIV x.
       Then d IN divisors n                               by divisors_has_cofactor
       and  n DIV d = n DIV (n DIV x) = x                 by divide_by_cofactor, 0 < n
*)
Theorem divisors_divisors_bij:
  !n. (\d. n DIV d) PERMUTES divisors n
Proof
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >-
  rw[divisors_has_cofactor] >-
 (`n = (n DIV d) * d` by metis_tac[DIVIDES_EQN, divisors_element] >>
  `n = (n DIV d') * d'` by metis_tac[DIVIDES_EQN, divisors_element] >>
  `0 < n` by metis_tac[divisors_has_element] >>
  `n DIV d <> 0` by metis_tac[MULT, NOT_ZERO] >>
  metis_tac[EQ_MULT_LCANCEL]) >-
  rw[divisors_has_cofactor] >>
  `0 < n` by metis_tac[divisors_has_element] >>
  metis_tac[divisors_element, divisors_has_cofactor, divide_by_cofactor]
QED

(* ------------------------------------------------------------------------- *)
(* An upper bound for divisors.                                              *)
(* ------------------------------------------------------------------------- *)

(* Idea: if a divisor of n is less or equal to (SQRT n), its cofactor is more or equal to (SQRT n) *)

(* Theorem: 0 < p /\ p divides n /\ p <= SQRT n ==> SQRT n <= (n DIV p) *)
(* Proof:
   Let m = SQRT n, then p <= m.
   By contradiction, suppose (n DIV p) < m.
   Then  n = (n DIV p) * p         by DIVIDES_EQN, 0 < p
          <= (n DIV p) * m         by p <= m
           < m * m                 by (n DIV p) < m
          <= n                     by SQ_SQRT_LE
   giving n < n, which is a contradiction.
*)
Theorem divisor_le_cofactor_ge:
  !n p. 0 < p /\ p divides n /\ p <= SQRT n ==> SQRT n <= (n DIV p)
Proof
  rpt strip_tac >>
  qabbrev_tac `m = SQRT n` >>
  spose_not_then strip_assume_tac >>
  `n = (n DIV p) * p` by rfs[DIVIDES_EQN] >>
  `(n DIV p) * p <= (n DIV p) * m` by fs[] >>
  `(n DIV p) * m < m * m` by fs[] >>
  `m * m <= n` by simp[SQ_SQRT_LE, Abbr`m`] >>
  decide_tac
QED

(* Idea: if a divisor of n is greater than (SQRT n), its cofactor is less or equal to (SQRT n) *)

(* Theorem: 0 < p /\ p divides n /\ SQRT n < p ==> (n DIV p) <= SQRT n *)
(* Proof:
   Let m = SQRT n, then m < p.
   By contradiction, suppose m < (n DIV p).
   Let q = (n DIV p).
   Then SUC m <= p, SUC m <= q     by m < p, m < q
   and   n = q * p                 by DIVIDES_EQN, 0 < p
          >= (SUC m) * (SUC m)     by LESS_MONO_MULT2
           = (SUC m) ** 2          by EXP_2
           > n                     by SQRT_PROPERTY
   which is a contradiction.
*)
Theorem divisor_gt_cofactor_le:
  !n p. 0 < p /\ p divides n /\ SQRT n < p ==> (n DIV p) <= SQRT n
Proof
  rpt strip_tac >>
  qabbrev_tac `m = SQRT n` >>
  spose_not_then strip_assume_tac >>
  `n = (n DIV p) * p` by rfs[DIVIDES_EQN] >>
  qabbrev_tac `q = n DIV p` >>
  `SUC m <= p /\ SUC m <= q` by decide_tac >>
  `(SUC m) * (SUC m) <= q * p` by simp[LESS_MONO_MULT2] >>
  `n < (SUC m) * (SUC m)` by metis_tac[SQRT_PROPERTY, EXP_2] >>
  decide_tac
QED

(* Idea: for (divisors n), the map (\j. n DIV j) is injective. *)

(* Theorem: INJ (\j. n DIV j) (divisors n) univ(:num) *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) !x. x IN (divisors n) ==> (\j. n DIV j) x IN univ(:num)
       True by types, n DIV j is a number, with type :num.
   (2) !x y. x IN (divisors n) /\ y IN (divisors n) /\ n DIV x = n DIV y ==> x = y
       Note x divides n /\ 0 < x /\ x <= n     by divisors_def
        and y divides n /\ 0 < y /\ x <= n     by divisors_def
        Let p = n DIV x, q = n DIV y.
       Note 0 < n                              by divisors_has_element
       then 0 < p, 0 < q                       by DIV_POS, 0 < n
       Then  n = p * x = q * y                 by DIVIDES_EQN, 0 < x, 0 < y
        But          p = q                     by given
         so          x = y                     by EQ_MULT_LCANCEL
*)
Theorem divisors_cofactor_inj:
  !n. INJ (\j. n DIV j) (divisors n) univ(:num)
Proof
  rw[INJ_DEF, divisors_def] >>
  `n = n DIV j * j` by fs[GSYM DIVIDES_EQN] >>
  `n = n DIV j' * j'` by fs[GSYM DIVIDES_EQN] >>
  `0 < n` by fs[GSYM divisors_has_element] >>
  metis_tac[EQ_MULT_LCANCEL, DIV_POS, NOT_ZERO]
QED

(* Idea: an upper bound for CARD (divisors n).

To prove: 0 < n ==> CARD (divisors n) <= 2 * SQRT n
Idea of proof:
   Consider the two sets,
      s = {x | x IN divisors n /\ x <= SQRT n}
      t = {x | x IN divisors n /\ SQRT n <= x}
   Note s SUBSET (natural (SQRT n)), so CARD s <= SQRT n.
   Also t SUBSET (natural (SQRT n)), so CARD t <= SQRT n.
   There is a bijection between the two parts:
      BIJ (\j. n DIV j) s t
   Now divisors n = s UNION t
      CARD (divisors n)
    = CARD s + CARD t - CARD (s INTER t)
   <= CARD s + CARD t
   <= SQRT n + SQRT n
    = 2 * SQRT n

   The BIJ part will be quite difficult.
   So the actual proof is a bit different.
*)

(* Theorem: CARD (divisors n) <= 2 * SQRT n *)
(* Proof:
   Let m = SQRT n,
       d = divisors n,
       s = {x | x IN d /\ x <= m},
       f = \j. n DIV j,
       t = IMAGE f s.

   Claim: s SUBSET natural m
   Proof: By SUBSET_DEF, this is to show:
             x IN d /\ x <= m ==> ?y. x = SUC y /\ y < m
          Note 0 < x               by divisors_nonzero
          Let y = PRE x.
          Then x = SUC (PRE x)     by SUC_PRE
           and PRE x < x           by PRE_LESS
            so PRE x < m           by inequality, x <= m

   Claim: BIJ f s t
   Proof: Note s SUBSET d          by SUBSET_DEF
           and INJ f d univ(:num)  by divisors_cofactor_inj
            so INJ f s univ(:num)  by INJ_SUBSET, SUBSET_REFL
           ==> BIJ f s t           by INJ_IMAGE_BIJ_ALT

   Claim: d = s UNION t
   Proof: By EXTENSION, EQ_IMP_THM, this is to show:
          (1) x IN divisors n ==> x <= m \/ ?j. x = n DIV j /\ j IN divisors n /\ j <= m
              If x <= m, this is trivial.
              Otherwise, m < x.
              Let j = n DIV x.
              Then x = n DIV (n DIV x)         by divide_by_cofactor
               and (n DIV j) IN divisors n     by divisors_has_cofactor
               and (n DIV j) <= m              by divisor_gt_cofactor_le
          (2) j IN divisors n ==> n DIV j IN divisors n
              This is true                     by divisors_has_cofactor

    Now FINITE (natural m)         by natural_finite
     so FINITE s                   by SUBSET_FINITE
    and FINITE t                   by IMAGE_FINITE
     so CARD s <= m                by CARD_SUBSET, natural_card
   Also CARD t = CARD s            by FINITE_BIJ_CARD

        CARD d <= CARD s + CARD t  by CARD_UNION_LE, d = s UNION t
               <= m + m            by above
                = 2 * m            by arithmetic
*)
Theorem divisors_card_upper:
  !n. CARD (divisors n) <= 2 * SQRT n
Proof
  rpt strip_tac >>
  qabbrev_tac `m = SQRT n` >>
  qabbrev_tac `d = divisors n` >>
  qabbrev_tac `s = {x | x IN d /\ x <= m}` >>
  qabbrev_tac `f = \j. n DIV j` >>
  qabbrev_tac `t = (IMAGE f s)` >>
  `s SUBSET (natural m)` by
  (rw[SUBSET_DEF, Abbr`s`] >>
  `0 < x` by metis_tac[divisors_nonzero] >>
  qexists_tac `PRE x` >>
  simp[]) >>
  `BIJ f s t` by
    (simp[Abbr`t`] >>
  irule INJ_IMAGE_BIJ_ALT >>
  `s SUBSET d` by rw[SUBSET_DEF, Abbr`s`] >>
  `INJ f d univ(:num)` by metis_tac[divisors_cofactor_inj] >>
  metis_tac[INJ_SUBSET, SUBSET_REFL]) >>
  `d = s UNION t` by
      (rw[EXTENSION, Abbr`d`, Abbr`s`, Abbr`t`, Abbr`f`, EQ_IMP_THM] >| [
    (Cases_on `x <= m` >> simp[]) >>
    qexists_tac `n DIV x` >>
    `0 < x /\ x <= n /\ x divides n` by fs[divisors_element] >>
    simp[divide_by_cofactor, divisors_has_cofactor] >>
    `m < x` by decide_tac >>
    simp[divisor_gt_cofactor_le, Abbr`m`],
    simp[divisors_has_cofactor]
  ]) >>
  `FINITE (natural m)` by simp[natural_finite] >>
  `FINITE s /\ FINITE t` by metis_tac[SUBSET_FINITE, IMAGE_FINITE] >>
  `CARD s <= m` by metis_tac[CARD_SUBSET, natural_card] >>
  `CARD t = CARD s` by metis_tac[FINITE_BIJ_CARD] >>
  `CARD d <= CARD s + CARD t` by metis_tac[CARD_UNION_LE] >>
  decide_tac
QED

(* This is a remarkable result! *)


(* ------------------------------------------------------------------------- *)
(* Gauss' Little Theorem                                                     *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* Gauss' Little Theorem: sum of phi over divisors                           *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* Gauss' Little Theorem: A general theory on sum over divisors              *)
(* ------------------------------------------------------------------------- *)

(*
Let n = 6. (divisors 6) = {1, 2, 3, 6}
  IMAGE coprimes (divisors 6)
= {coprimes 1, coprimes 2, coprimes 3, coprimes 6}
= {{1}, {1}, {1, 2}, {1, 5}}   <-- will collapse
  IMAGE (preimage (gcd 6) (count 6)) (divisors 6)
= {{preimage in count 6 of those gcd 6 j = 1},
   {preimage in count 6 of those gcd 6 j = 2},
   {preimage in count 6 of those gcd 6 j = 3},
   {preimage in count 6 of those gcd 6 j = 6}}
= {{1, 5}, {2, 4}, {3}, {6}}
= {1x{1, 5}, 2x{1, 2}, 3x{1}, 6x{1}}
!s. s IN (IMAGE (preimage (gcd n) (count n)) (divisors n))
==> ?d. d divides n /\ d < n /\ s = preimage (gcd n) (count n) d
==> ?d. d divides n /\ d < n /\ s = IMAGE (TIMES d) (coprimes ((gcd n d) DIV d))

  IMAGE (feq_class (count 6) (gcd 6)) (divisors 6)
= {{feq_class in count 6 of those gcd 6 j = 1},
   {feq_class in count 6 of those gcd 6 j = 2},
   {feq_class in count 6 of those gcd 6 j = 3},
   {feq_class in count 6 of those gcd 6 j = 6}}
= {{1, 5}, {2, 4}, {3}, {6}}
= {1x{1, 5}, 2x{1, 2}, 3x{1}, 6x{1}}
That is:  CARD {1, 5} = CARD (coprime 6) = CARD (coprime (6 DIV 1))
          CARD {2, 4} = CARD (coprime 3) = CARD (coprime (6 DIV 2))
          CARD {3} = CARD (coprime 2) = CARD (coprime (6 DIV 3)))
          CARD {6} = CARD (coprime 1) = CARD (coprime (6 DIV 6)))

*)
(* Note:
   In general, what is the condition for:  SIGMA f s = SIGMA g t ?
   Conceptually,
       SIGMA f s = f s1 + f s2 + f s3 + ... + f sn
   and SIGMA g t = g t1 + g t2 + g t3 + ... + g tm

SUM_IMAGE_eq_SUM_MAP_SET_TO_LIST

Use disjoint_bigunion_card
|- !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P ==> (CARD (BIGUNION P) = SIGMA CARD P)
If a partition P = {s | condition on s} the element s = IMAGE g t
e.g.  P = {{1, 5} {2, 4} {3} {6}}
        = {IMAGE (TIMES 1) (coprimes 6/1),
           IMAGE (TIMES 2) (coprimes 6/2),
           IMAGE (TIMES 3) (coprimes 6/3),
           IMAGE (TIMES 6) (coprimes 6/6)}
        =  IMAGE (\d. TIMES d o coprimes (6/d)) {1, 2, 3, 6}

*)

(* Theorem: d divides n ==> !j. j IN gcd_matches n d ==> j DIV d IN coprimes_by n d *)
(* Proof:
   When n = 0, gcd_matches 0 d = {}       by gcd_matches_0, hence trivially true.
   Otherwise,
   By coprimes_by_def, this is to show:
      0 < n /\ d divides n ==> !j. j IN gcd_matches n d ==> j DIV d IN coprimes (n DIV d)
   Note j IN gcd_matches n d
    ==> d divides j               by gcd_matches_element_divides
   Also d IN gcd_matches n d      by gcd_matches_has_divisor
     so 0 < d /\ (d = gcd j n)    by gcd_matches_element
     or d <> 0 /\ (d = gcd n j)   by GCD_SYM
   With the given d divides n,
        j = d * (j DIV d)         by DIVIDES_EQN, MULT_COMM, 0 < d
        n = d * (n DIV d)         by DIVIDES_EQN, MULT_COMM, 0 < d
  Hence d = d * gcd (n DIV d) (j DIV d)        by GCD_COMMON_FACTOR
     or d * 1 = d * gcd (n DIV d) (j DIV d)    by MULT_RIGHT_1
  giving    1 = gcd (n DIV d) (j DIV d)        by EQ_MULT_LCANCEL, d <> 0
      or    coprime (j DIV d) (n DIV d)        by GCD_SYM
   Also j IN natural n            by gcd_matches_subset, SUBSET_DEF
  Hence 0 < j DIV d /\ j DIV d <= n DIV d      by natural_cofactor_natural_reduced
     or j DIV d IN coprimes (n DIV d)          by coprimes_element
*)
val gcd_matches_divisor_element = store_thm(
  "gcd_matches_divisor_element",
  ``!n d. d divides n ==> !j. j IN gcd_matches n d ==> j DIV d IN coprimes_by n d``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  metis_tac[gcd_matches_0, NOT_IN_EMPTY] >>
  `0 < n` by decide_tac >>
  rw[coprimes_by_def] >>
  `d divides j` by metis_tac[gcd_matches_element_divides] >>
  `0 < d /\ 0 < j /\ j <= n /\ (d = gcd n j)` by metis_tac[gcd_matches_has_divisor, gcd_matches_element, GCD_SYM] >>
  `d <> 0` by decide_tac >>
  `(j = d * (j DIV d)) /\ (n = d * (n DIV d))` by metis_tac[DIVIDES_EQN, MULT_COMM] >>
  `coprime (n DIV d) (j DIV d)` by metis_tac[GCD_COMMON_FACTOR, MULT_RIGHT_1, EQ_MULT_LCANCEL] >>
  `0 < j DIV d /\ j DIV d <= n DIV d` by metis_tac[natural_cofactor_natural_reduced, natural_element] >>
  metis_tac[coprimes_element, GCD_SYM]);

(* Theorem: d divides n ==> BIJ (\j. j DIV d) (gcd_matches n d) (coprimes_by n d) *)
(* Proof:
   When n = 0, gcd_matches 0 d = {}       by gcd_matches_0
           and coprimes_by 0 d = {}       by coprimes_by_0, hence trivially true.
   Otherwise,
   By definitions, this is to show:
   (1) j IN gcd_matches n d ==> j DIV d IN coprimes_by n d
       True by gcd_matches_divisor_element.
   (2) j IN gcd_matches n d /\ j' IN gcd_matches n d /\ j DIV d = j' DIV d ==> j = j'
      Note j IN gcd_matches n d /\ j' IN gcd_matches n d
       ==> d divides j /\ d divides j'             by gcd_matches_element_divides
      Also d IN (gcd_matches n d)                  by gcd_matches_has_divisor
        so 0 < d                                   by gcd_matches_element
      Thus j = (j DIV d) * d                       by DIVIDES_EQN, 0 < d
       and j' = (j' DIV d) * d                     by DIVIDES_EQN, 0 < d
      Since j DIV d = j' DIV d, j = j'.
   (3) same as (1), true by gcd_matches_divisor_element,
   (4) d divides n /\ x IN coprimes_by n d ==> ?j. j IN gcd_matches n d /\ (j DIV d = x)
       Note x IN coprimes (n DIV d)                by coprimes_by_def
        ==> 0 < x /\ x <= n DIV d /\ (coprime x (n DIV d))  by coprimes_element
        And d divides n /\ 0 < n
        ==> 0 < d /\ d <> 0                        by ZERO_DIVIDES, 0 < n
       Giving (x * d) DIV d = x                    by MULT_DIV, 0 < d
        Let j = x * d. so j DIV d = x              by above
       Then d divides j                            by divides_def
        ==> j = (j DIV d) * d                      by DIVIDES_EQN, 0 < d
       Note d divides n
        ==> n = (n DIV d) * d                      by DIVIDES_EQN, 0 < d
      Hence gcd j n
          = gcd (d * (j DIV d)) (d * (n DIV d))    by MULT_COMM
          = d * gcd (j DIV d) (n DIV d)            by GCD_COMMON_FACTOR
          = d * gcd x (n DIV d)                    by x = j DIV d
          = d * 1                                  by coprime x (n DIV d)
          = d                                      by MULT_RIGHT_1
      Since j = x * d, 0 < j                       by MULT_EQ_0, 0 < x, 0 < d
       Also x <= n DIV d
       means j DIV d <= n DIV d                    by x = j DIV d
          so (j DIV d) * d <= (n DIV d) * d        by LE_MULT_RCANCEL, d <> 0
          or             j <= n                    by above
      Hence j IN gcd_matches n d                   by gcd_matches_element
*)
val gcd_matches_bij_coprimes_by = store_thm(
  "gcd_matches_bij_coprimes_by",
  ``!n d. d divides n ==> BIJ (\j. j DIV d) (gcd_matches n d) (coprimes_by n d)``,
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    `gcd_matches n d = {}` by rw[gcd_matches_0] >>
    `coprimes_by n d = {}` by rw[coprimes_by_0] >>
    rw[],
    `0 < n` by decide_tac >>
    rw[BIJ_DEF, INJ_DEF, SURJ_DEF, EQ_IMP_THM] >-
    rw[GSYM gcd_matches_divisor_element] >-
    metis_tac[gcd_matches_element_divides, gcd_matches_has_divisor, gcd_matches_element, DIVIDES_EQN] >-
    rw[GSYM gcd_matches_divisor_element] >>
    `0 < x /\ x <= n DIV d /\ (coprime x (n DIV d))` by metis_tac[coprimes_by_def, coprimes_element] >>
    `0 < d /\ d <> 0` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
    `(x * d) DIV d = x` by rw[MULT_DIV] >>
    qabbrev_tac `j = x * d` >>
    `d divides j` by metis_tac[divides_def] >>
    `(n = (n DIV d) * d) /\ (j = (j DIV d) * d)` by rw[GSYM DIVIDES_EQN] >>
    `gcd j n = d` by metis_tac[GCD_COMMON_FACTOR, MULT_COMM, MULT_RIGHT_1] >>
    `0 < j` by metis_tac[MULT_EQ_0, NOT_ZERO] >>
    `j <= n` by metis_tac[LE_MULT_RCANCEL] >>
    metis_tac[gcd_matches_element]
  ]);

(* Theorem: 0 < n /\ d divides n ==> BIJ (\j. j DIV d) (gcd_matches n d) (coprimes (n DIV d)) *)
(* Proof: by gcd_matches_bij_coprimes_by, coprimes_by_by_divisor *)
val gcd_matches_bij_coprimes = store_thm(
  "gcd_matches_bij_coprimes",
  ``!n d. 0 < n /\ d divides n ==> BIJ (\j. j DIV d) (gcd_matches n d) (coprimes (n DIV d))``,
  metis_tac[gcd_matches_bij_coprimes_by, coprimes_by_by_divisor]);

(* Note: it is not useful to show:
         CARD o (gcd_matches n) = CARD o coprimes,
   as FUN_EQ_THM will demand:  CARD (gcd_matches n x) = CARD (coprimes x),
   which is not possible.
*)

(* Theorem: divisors n = IMAGE (gcd n) (natural n) *)
(* Proof:
     divisors n
   = {d | 0 < d /\ d <= n /\ d divides n}       by divisors_def
   = {d | d IN (natural n) /\ d divides n}      by natural_element
   = {d | d IN (natural n) /\ (gcd d n = d)}    by divides_iff_gcd_fix
   = {d | d IN (natural n) /\ (gcd n d = d)}    by GCD_SYM
   = {gcd n d | d | d IN (natural n)}           by replacemnt
   = IMAGE (gcd n) (natural n)                  by IMAGE_DEF
   The replacemnt requires:
       d IN (natural n) ==> gcd n d IN (natural n)
       d IN (natural n) ==> gcd n (gcd n d) = gcd n d
   which are given below.

   Or, by divisors_def, natuarl_elemnt, IN_IMAGE, this is to show:
   (1) 0 < x /\ x <= n /\ x divides n ==> ?y. (x = gcd n y) /\ 0 < y /\ y <= n
       Note x divides n ==> gcd x n = x         by divides_iff_gcd_fix
         or                 gcd n x = x         by GCD_SYM
       Take this x, and the result follows.
   (2) 0 < y /\ y <= n ==> 0 < gcd n y /\ gcd n y <= n /\ gcd n y divides n
       Note 0 < n                               by arithmetic
        and gcd n y divides n                   by GCD_IS_GREATEST_COMMON_DIVISOR, 0 < n
        and 0 < gcd n y                         by GCD_EQ_0, n <> 0
        and gcd n y <= n                        by DIVIDES_LE, 0 < n
*)
Theorem divisors_eq_gcd_image:
  !n. divisors n = IMAGE (gcd n) (natural n)
Proof
  rw_tac std_ss[divisors_def, GSPECIFICATION, EXTENSION, IN_IMAGE, natural_element, EQ_IMP_THM] >| [
    `0 < n` by decide_tac >>
    metis_tac[divides_iff_gcd_fix, GCD_SYM],
    metis_tac[GCD_EQ_0, NOT_ZERO],
    `0 < n` by decide_tac >>
    metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR, DIVIDES_LE],
    metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR]
  ]
QED

(* Theorem: feq_class (gcd n) (natural n) d = gcd_matches n d *)
(* Proof:
     feq_class (gcd n) (natural n) d
   = {x | x IN natural n /\ (gcd n x = d)}   by feq_class_def
   = {j | j IN natural n /\ (gcd j n = d)}   by GCD_SYM
   = gcd_matches n d                         by gcd_matches_def
*)
val gcd_eq_equiv_class = store_thm(
  "gcd_eq_equiv_class",
  ``!n d. feq_class (gcd n) (natural n) d = gcd_matches n d``,
  rewrite_tac[gcd_matches_def] >>
  rw[EXTENSION, GCD_SYM, in_preimage]);

(* Theorem: feq_class (gcd n) (natural n) = gcd_matches n *)
(* Proof: by FUN_EQ_THM, gcd_eq_equiv_class *)
val gcd_eq_equiv_class_fun = store_thm(
  "gcd_eq_equiv_class_fun",
  ``!n. feq_class (gcd n) (natural n) = gcd_matches n``,
  rw[FUN_EQ_THM, gcd_eq_equiv_class]);

(* Theorem: partition (feq (gcd n)) (natural n) = IMAGE (gcd_matches n) (divisors n) *)
(* Proof:
     partition (feq (gcd n)) (natural n)
   = IMAGE (equiv_class (feq (gcd n)) (natural n)) (natural n)      by partition_elements
   = IMAGE ((feq_class (gcd n) (natural n)) o (gcd n)) (natural n)  by feq_class_fun
   = IMAGE ((gcd_matches n) o (gcd n)) (natural n)       by gcd_eq_equiv_class_fun
   = IMAGE (gcd_matches n) (IMAGE (gcd n) (natural n))   by IMAGE_COMPOSE
   = IMAGE (gcd_matches n) (divisors n)                  by divisors_eq_gcd_image, 0 < n
*)
Theorem gcd_eq_partition_by_divisors:
  !n. partition (feq (gcd n)) (natural n) = IMAGE (gcd_matches n) (divisors n)
Proof
  rpt strip_tac >>
  qabbrev_tac `f = gcd n` >>
  qabbrev_tac `s = natural n` >>
  `partition (feq f) s = IMAGE (equiv_class (feq f) s) s` by rw[partition_elements] >>
  `_ = IMAGE ((feq_class f s) o f) s` by rw[feq_class_fun] >>
  `_ = IMAGE ((gcd_matches n) o f) s` by rw[gcd_eq_equiv_class_fun, Abbr`f`, Abbr`s`] >>
  `_ = IMAGE (gcd_matches n) (IMAGE f s)` by rw[IMAGE_COMPOSE] >>
  `_ = IMAGE (gcd_matches n) (divisors n)` by rw[divisors_eq_gcd_image, Abbr`f`, Abbr`s`] >>
  simp[]
QED

(* Theorem: (feq (gcd n)) equiv_on (natural n) *)
(* Proof:
   By feq_equiv |- !s f. feq f equiv_on s
   Taking s = upto n, f = natural n.
*)
val gcd_eq_equiv_on_natural = store_thm(
  "gcd_eq_equiv_on_natural",
  ``!n. (feq (gcd n)) equiv_on (natural n)``,
  rw[feq_equiv]);

(* Theorem: SIGMA f (natural n) = SIGMA (SIGMA f) (partition (feq (gcd n)) (natural n)) *)
(* Proof:
   Let g = gcd n, s = natural n.
   Since FINITE s               by natural_finite
     and (feq g) equiv_on s     by feq_equiv
   The result follows           by set_sigma_by_partition
*)
val sum_over_natural_by_gcd_partition = store_thm(
  "sum_over_natural_by_gcd_partition",
  ``!f n. SIGMA f (natural n) = SIGMA (SIGMA f) (partition (feq (gcd n)) (natural n))``,
  rw[feq_equiv, natural_finite, set_sigma_by_partition]);

(* Theorem: SIGMA f (natural n) = SIGMA (SIGMA f) (IMAGE (gcd_matches n) (divisors n)) *)
(* Proof:
     SIGMA f (natural n)
   = SIGMA (SIGMA f) (partition (feq (gcd n)) (natural n)) by sum_over_natural_by_gcd_partition
   = SIGMA (SIGMA f) (IMAGE (gcd_matches n) (divisors n))  by gcd_eq_partition_by_divisors
*)
Theorem sum_over_natural_by_divisors:
  !f n. SIGMA f (natural n) = SIGMA (SIGMA f) (IMAGE (gcd_matches n) (divisors n))
Proof
  simp[sum_over_natural_by_gcd_partition, gcd_eq_partition_by_divisors]
QED

(* Theorem: INJ (gcd_matches n) (divisors n) univ(num) *)
(* Proof:
   By INJ_DEF, this is to show:
      x IN divisors n /\ y IN divisors n /\ gcd_matches n x = gcd_matches n y ==> x = y
    Note 0 < x /\ x <= n /\ x divides n        by divisors_def
    also 0 < y /\ y <= n /\ y divides n        by divisors_def
   Hence (gcd x n = x) /\ (gcd y n = y)        by divides_iff_gcd_fix
     ==> x IN gcd_matches n x                  by gcd_matches_element
      so x IN gcd_matches n y                  by gcd_matches n x = gcd_matches n y
    with gcd x n = y                           by gcd_matches_element
    Therefore y = gcd x n = x.
*)
Theorem gcd_matches_from_divisors_inj:
  !n. INJ (gcd_matches n) (divisors n) univ(:num -> bool)
Proof
  rw[INJ_DEF] >>
  fs[divisors_def] >>
  `(gcd x n = x) /\ (gcd y n = y)` by rw[GSYM divides_iff_gcd_fix] >>
  metis_tac[gcd_matches_element]
QED

(* Theorem: CARD o (gcd_matches n) = CARD o (coprimes_by n) *)
(* Proof:
   By composition and FUN_EQ_THM, this is to show:
      !x. CARD (gcd_matches n x) = CARD (coprimes_by n x)
   If x divides n,
      Then BIJ (\j. j DIV x) (gcd_matches n x) (coprimes_by n x)  by gcd_matches_bij_coprimes_by
      Also FINITE (gcd_matches n x)                               by gcd_matches_finite
       and FINITE (coprimes_by n x)                               by coprimes_by_finite
      Hence CARD (gcd_matches n x) = CARD (coprimes_by n x)       by FINITE_BIJ_CARD_EQ
   If ~(x divides n),
      If n = 0,
         then gcd_matches 0 x = {}      by gcd_matches_0
          and coprimes_by 0 x = {}      by coprimes_by_0
         Hence true.
      If n <> 0,
         then gcd_matches n x = {}      by gcd_matches_eq_empty, 0 < n
          and coprimes_by n x = {}      by coprimes_by_eq_empty, 0 < n
         Hence CARD {} = CARD {}.
*)
val gcd_matches_and_coprimes_by_same_size = store_thm(
  "gcd_matches_and_coprimes_by_same_size",
  ``!n. CARD o (gcd_matches n) = CARD o (coprimes_by n)``,
  rw[FUN_EQ_THM] >>
  Cases_on `x divides n` >| [
    `BIJ (\j. j DIV x) (gcd_matches n x) (coprimes_by n x)` by rw[gcd_matches_bij_coprimes_by] >>
    `FINITE (gcd_matches n x)` by rw[gcd_matches_finite] >>
    `FINITE (coprimes_by n x)` by rw[coprimes_by_finite] >>
    metis_tac[FINITE_BIJ_CARD_EQ],
    Cases_on `n = 0` >-
    rw[gcd_matches_0, coprimes_by_0] >>
    `gcd_matches n x = {}` by rw[gcd_matches_eq_empty] >>
    `coprimes_by n x = {}` by rw[coprimes_by_eq_empty] >>
    rw[]
  ]);

(* Theorem: 0 < n ==> (CARD o (coprimes_by n) = \d. phi (if d IN (divisors n) then n DIV d else 0)) *)
(* Proof:
   By FUN_EQ_THM,
      CARD o (coprimes_by n) x
    = CARD (coprimes_by n x)       by composition, combinTheory.o_THM
    = CARD (if x divides n then coprimes (n DIV x) else {})    by coprimes_by_def, 0 < n
    If x divides n,
       then x <= n                 by DIVIDES_LE
        and 0 < x                  by divisor_pos, 0 < n
         so x IN (divisors n)      by divisors_element
       CARD o (coprimes_by n) x
     = CARD (coprimes (n DIV x))
     = phi (n DIV x)               by phi_def
    If ~(x divides n),
       x NOTIN (divisors n)        by divisors_element
       CARD o (coprimes_by n) x
     = CARD {}
     = 0                           by CARD_EMPTY
     = phi 0                       by phi_0
    Hence the same function as:
    \d. phi (if d IN (divisors n) then n DIV d else 0)
*)
Theorem coprimes_by_with_card:
  !n. 0 < n ==> (CARD o (coprimes_by n) = \d. phi (if d IN (divisors n) then n DIV d else 0))
Proof
  rw[coprimes_by_def, phi_def, divisors_def, FUN_EQ_THM] >>
  metis_tac[DIVIDES_LE, divisor_pos, coprimes_0]
QED

(* Theorem: x IN (divisors n) ==> (CARD o (coprimes_by n)) x = (\d. phi (n DIV d)) x *)
(* Proof:
   Since x IN (divisors n) ==> x divides n     by divisors_element
       CARD o (coprimes_by n) x
     = CARD (coprimes (n DIV x))               by coprimes_by_def
     = phi (n DIV x)                           by phi_def
*)
Theorem coprimes_by_divisors_card:
  !n x. x IN (divisors n) ==> (CARD o (coprimes_by n)) x = (\d. phi (n DIV d)) x
Proof
  rw[coprimes_by_def, phi_def, divisors_def]
QED

(*
SUM_IMAGE_CONG |- (s1 = s2) /\ (!x. x IN s2 ==> (f1 x = f2 x)) ==> (SIGMA f1 s1 = SIGMA f2 s2)
*)

(* Theorem: SIGMA phi (divisors n) = n *)
(* Proof:
   Note INJ (gcd_matches n) (divisors n) univ(:num -> bool)  by gcd_matches_from_divisors_inj
    and (\d. n DIV d) PERMUTES (divisors n)              by divisors_divisors_bij
   n = CARD (natural n)                                  by natural_card
     = SIGMA CARD (partition (feq (gcd n)) (natural n))  by partition_CARD
     = SIGMA CARD (IMAGE (gcd_matches n) (divisors n))   by gcd_eq_partition_by_divisors
     = SIGMA (CARD o (gcd_matches n)) (divisors n)       by sum_image_by_composition
     = SIGMA (CARD o (coprimes_by n)) (divisors n)       by gcd_matches_and_coprimes_by_same_size
     = SIGMA (\d. phi (n DIV d)) (divisors n)            by SUM_IMAGE_CONG, coprimes_by_divisors_card
     = SIGMA phi (divisors n)                            by sum_image_by_permutation
*)
Theorem Gauss_little_thm:
  !n. SIGMA phi (divisors n) = n
Proof
  rpt strip_tac >>
  `FINITE (natural n)` by rw[natural_finite] >>
  `(feq (gcd n)) equiv_on (natural n)` by rw[gcd_eq_equiv_on_natural] >>
  `INJ (gcd_matches n) (divisors n) univ(:num -> bool)` by rw[gcd_matches_from_divisors_inj] >>
  `(\d. n DIV d) PERMUTES (divisors n)` by rw[divisors_divisors_bij] >>
  `FINITE (divisors n)` by rw[divisors_finite] >>
  `n = CARD (natural n)` by rw[natural_card] >>
  `_ = SIGMA CARD (partition (feq (gcd n)) (natural n))` by rw[partition_CARD] >>
  `_ = SIGMA CARD (IMAGE (gcd_matches n) (divisors n))` by rw[gcd_eq_partition_by_divisors] >>
  `_ = SIGMA (CARD o (gcd_matches n)) (divisors n)` by prove_tac[sum_image_by_composition] >>
  `_ = SIGMA (CARD o (coprimes_by n)) (divisors n)` by rw[gcd_matches_and_coprimes_by_same_size] >>
  `_ = SIGMA (\d. phi (n DIV d)) (divisors n)` by rw[SUM_IMAGE_CONG, coprimes_by_divisors_card] >>
  `_ = SIGMA phi (divisors n)` by metis_tac[sum_image_by_permutation] >>
  decide_tac
QED

(* This is a milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Euler phi function is multiplicative for coprimes.                        *)
(* ------------------------------------------------------------------------- *)

(*
EVAL ``coprimes 2``; = {1}
EVAL ``coprimes 3``; = {2; 1}
EVAL ``coprimes 6``; = {5; 1}

Let ϕ(n) = the set of remainders coprime to n and not exceeding n.
Then ϕ(2) = {1}, ϕ(3) = {1,2}
We shall show ϕ(6) = {z = (3 * x + 2 * y) mod 6 | x ∈ ϕ(2), y ∈ ϕ(3)}.
(1,1) corresponds to z = (3 * 1 + 2 * 1) mod 6 = 5, right!
(1,2) corresponds to z = (3 * 1 + 2 * 2) mod 6 = 1, right!
*)

(* Idea: give an expression for coprimes (m * n). *)

(* Theorem: coprime m n ==>
            coprimes (m * n) =
            IMAGE (\(x,y). if (m * n = 1) then 1 else (x * n + y * m) MOD (m * n))
                  ((coprimes m) CROSS (coprimes n)) *)
(* Proof:
   Let f = \(x,y). if (m * n = 1) then 1 else (x * n + y * m) MOD (m * n).
   If m = 0 or n = 0,
      When m = 0, to show:
           coprimes 0 = IMAGE f ((coprimes 0) CROSS (coprimes n))
           RHS
         = IMAGE f ({} CROSS (coprimes n))     by coprimes_0
         = IMAGE f {}                          by CROSS_EMPTY
         = {}                                  by IMAGE_EMPTY
         = LHS                                 by coprimes_0
      When n = 0, to show:
           coprimes 0 = IMAGE f ((coprimes m) CROSS (coprimes 0))
           RHS
         = IMAGE f ((coprimes n) CROSS {})     by coprimes_0
         = IMAGE f {}                          by CROSS_EMPTY
         = {}                                  by IMAGE_EMPTY
         = LHS                                 by coprimes_0

   If m = 1, or n = 1,
      When m = 1, to show:
           coprimes n = IMAGE f ((coprimes 1) CROSS (coprimes n))
           RHS
         = IMAGE f ({1} CROSS (coprimes n))    by coprimes_1
         = IMAGE f {(1,y) | y IN coprimes n}   by IN_CROSS
         = {if n = 1 then 1 else (n + y) MOD n | y IN coprimes n}
                                               by IN_IMAGE
         = {1} if n = 1, or {y MOD n | y IN coprimes n} if 1 < n
         = {1} if n = 1, or {y | y IN coprimes n} if 1 < n
                                               by coprimes_element_alt, LESS_MOD, y < n
         = LHS                                 by coprimes_1
      When n = 1, to show:
           coprimes m = IMAGE f ((coprimes m) CROSS (coprimes 1))
           RHS
         = IMAGE f ((coprimes m) CROSS {1})    by coprimes_1
         = IMAGE f {(x,1) | x IN coprimes m}   by IN_CROSS
         = {if m = 1 then 1 else (x + m) MOD m | x IN coprimes m}
                                               by IN_IMAGE
         = {1} if m = 1, or {x MOD m | x IN coprimes m} if 1 < m
         = {1} if m = 1, or {x | x IN coprimes m} if 1 < m
                                               by coprimes_element_alt, LESS_MOD, x < m
         = LHS                                 by coprimes_1

   Now, 1 < m, 1 < n, and 0 < m, 0 < n.
   Therefore 1 < m * n, and 0 < m * n.         by MULT_EQ_1, MULT_EQ_0
   and function f = \(x,y). (x * n + y * m) MOD (m * n).
   If part: z IN coprimes (m * n) ==>
            ?x y. z = (x * n + y * m) MOD (m * n) /\ x IN coprimes m /\ y IN coprimes n
      Note z < m * n /\ coprime z (m * n)      by coprimes_element_alt, 1 < m * n
       for x < m /\ coprime x m, and y < n /\ coprime y n
                                               by coprimes_element_alt, 1 < m, 1 < n
       Now ?p q. (p * m + q * n) MOD (m * n)
               = z MOD (m * n)                 by coprime_multiple_linear_mod_prod
               = z                             by LESS_MOD, z < m * n
      Note ?h x. p = h * n + x /\ x < n        by DA, 0 < n
       and ?k y. q = k * m + y /\ y < m        by DA, 0 < m
           z
         = (p * m + q * n) MOD (m * n)         by above
         = (h * n * m + x * m + k * m * n + y * n) MOD (m * n)
         = ((x * m + y * n) + (h + k) * (m * n)) MOD (m * n)
         = (x * m + y * n) MOD (m * n)         by MOD_PLUS2, MOD_EQ_0
      Take these x and y, but need to show:
      (1) coprime x n
          Let g = gcd x n,
          Then g divides x /\ g divides n      by GCD_PROPERTY
            so g divides (m * n)               by DIVIDES_MULTIPLE
            so g divides z                     by divides_linear, mod_divides_divides
           ==> g = 1, or coprime x n           by coprime_common_factor
      (2) coprime y m
          Let g = gcd y m,
          Then g divides y /\ g divides m      by GCD_PROPERTY
            so g divides (m * n)               by DIVIDES_MULTIPLE
            so g divides z                     by divides_linear, mod_divides_divides
           ==> g = 1, or coprime y m           by coprime_common_factor

   Only-if part: coprime m n /\ x IN coprimes m /\ y IN coprimes n ==>
                 (x * n + y * m) MOD (m * n) IN coprimes (m * n)
       Note x < m /\ coprime x m               by coprimes_element_alt, 1 < m
        and y < n /\ coprime y n               by coprimes_element_alt, 1 < n
       Let z = x * m + y * n.
       Then coprime z (m * n)                  by coprime_linear_mult
         so coprime (z MOD (m * n)) (m * n)    by GCD_MOD_COMM
        and z MOD (m * n) < m * n              by MOD_LESS, 0 < m * n
*)
Theorem coprimes_mult_by_image:
  !m n. coprime m n ==>
        coprimes (m * n) =
        IMAGE (\(x,y). if (m * n = 1) then 1 else (x * n + y * m) MOD (m * n))
              ((coprimes m) CROSS (coprimes n))
Proof
  rpt strip_tac >>
  Cases_on `m = 0 \/ n = 0` >-
  fs[coprimes_0] >>
  Cases_on `m = 1 \/ n = 1` >| [
    fs[coprimes_1] >| [
      rw[EXTENSION, pairTheory.EXISTS_PROD] >>
      Cases_on `n = 1` >-
      simp[coprimes_1] >>
      fs[coprimes_element_alt] >>
      metis_tac[LESS_MOD],
      rw[EXTENSION, pairTheory.EXISTS_PROD] >>
      Cases_on `m = 1` >-
      simp[coprimes_1] >>
      fs[coprimes_element_alt] >>
      metis_tac[LESS_MOD]
    ],
    `m * n <> 0 /\ m * n <> 1` by rw[] >>
    `1 < m /\ 1 < n /\ 1 < m * n` by decide_tac >>
    rw[EXTENSION, pairTheory.EXISTS_PROD] >>
    rw[EQ_IMP_THM] >| [
      rfs[coprimes_element_alt] >>
      `1 < m /\ 1 < n /\ 0 < m /\ 0 < n /\ 0 < m * n` by decide_tac >>
      `?p q. (p * m + q * n) MOD (m * n) = x MOD (m * n)` by rw[coprime_multiple_linear_mod_prod] >>
      `?h u. p = h * n + u /\ u < n` by metis_tac[DA] >>
      `?k v. q = k * m + v /\ v < m` by metis_tac[DA] >>
      `p * m + q * n = h * n * m + u * m + k * m * n + v * n` by simp[] >>
      `_ = (u * m + v * n) + (h + k) * (m * n)` by simp[] >>
      `(u * m + v * n) MOD (m * n) = x MOD (m * n)` by metis_tac[MOD_PLUS2, MOD_EQ_0, ADD_0] >>
      `_ = x` by rw[] >>
      `coprime u n` by
  (qabbrev_tac `g = gcd u n` >>
      `0 < g` by rw[GCD_POS, Abbr`g`] >>
      `g divides u /\ g divides n` by metis_tac[GCD_PROPERTY] >>
      `g divides (m * n)` by rw[DIVIDES_MULTIPLE] >>
      `g divides x` by metis_tac[divides_linear, MULT_COMM, mod_divides_divides] >>
      metis_tac[coprime_common_factor]) >>
      `coprime v m` by
    (qabbrev_tac `g = gcd v m` >>
      `0 < g` by rw[GCD_POS, Abbr`g`] >>
      `g divides v /\ g divides m` by metis_tac[GCD_PROPERTY] >>
      `g divides (m * n)` by metis_tac[DIVIDES_MULTIPLE, MULT_COMM] >>
      `g divides x` by metis_tac[divides_linear, MULT_COMM, mod_divides_divides] >>
      metis_tac[coprime_common_factor]) >>
      metis_tac[MULT_COMM],
      rfs[coprimes_element_alt] >>
      `0 < m * n` by decide_tac >>
      `coprime (m * p_2 + n * p_1) (m * n)` by metis_tac[coprime_linear_mult, MULT_COMM] >>
      metis_tac[GCD_MOD_COMM]
    ]
  ]
QED

(* Yes! a milestone theorem. *)

(* Idea: in coprimes (m * n), the image map is injective. *)

(* Theorem: coprime m n ==>
            INJ (\(x,y). if (m * n = 1) then 1 else (x * n + y * m) MOD (m * n))
                ((coprimes m) CROSS (coprimes n)) univ(:num) *)
(* Proof:
   Let f = \(x,y). if m * n = 1 then 1 else (x * n + y * m) MOD (m * n).
   To show: coprime m n ==> INJ f ((coprimes m) CROSS (coprimes n)) univ(:num)
   If m = 0, or n = 0,
      When m = 0,
           INJ f ((coprimes 0) CROSS (coprimes n)) univ(:num)
       <=> INJ f ({} CROSS (coprimes n)) univ(:num)      by coprimes_0
       <=> INJ f {} univ(:num)                           by CROSS_EMPTY
       <=> T                                             by INJ_EMPTY
      When n = 0,
           INJ f ((coprimes m) CROSS (coprimes 0)) univ(:num)
       <=> INJ f ((coprimes m) CROSS {}) univ(:num)      by coprimes_0
       <=> INJ f {} univ(:num)                           by CROSS_EMPTY
       <=> T                                             by INJ_EMPTY

   If m = 1, or n = 1,
      When m = 1,
           INJ f ((coprimes 1) CROSS (coprimes n)) univ(:num)
       <=> INJ f ({1} CROSS (coprimes n)) univ(:num)     by coprimes_1
       If n = 1, this is
           INJ f ({1} CROSS {1}) univ(:num)              by coprimes_1
       <=> INJ f {(1,1)} univ(:num)                      by CROSS_SINGS
       <=> T                                             by INJ_DEF
       If n <> 1, this is by INJ_DEF:
       to show: !p q. p IN coprimes n /\ q IN coprimes n ==> p MOD n = q MOD n ==> p = q
       Now p < n /\ q < n                                by coprimes_element_alt, 1 < n
       With p MOD n = q MOD n, so p = q                  by LESS_MOD
      When n = 1,
           INJ f ((coprimes m) CROSS (coprimes 1)) univ(:num)
       <=> INJ f ((coprimes m) CROSS {1}) univ(:num)     by coprimes_1
       If m = 1, this is
           INJ f ({1} CROSS {1}) univ(:num)              by coprimes_1
       <=> INJ f {(1,1)} univ(:num)                      by CROSS_SINGS
       <=> T                                             by INJ_DEF
       If m <> 1, this is by INJ_DEF:
       to show: !p q. p IN coprimes m /\ q IN coprimes m ==> p MOD m = q MOD m ==> p = q
       Now p < m /\ q < m                                by coprimes_element_alt, 1 < m
       With p MOD m = q MOD m, so p = q                  by LESS_MOD

   Now 1 < m and 1 < n, so 1 < m * n           by MULT_EQ_1, MULT_EQ_0
   By INJ_DEF, coprimes_element_alt, this is to show:
      !x y u v. x < m /\ coprime x m /\ y < n /\ coprime y n /\
                u < m /\ coprime u m /\ v < n /\ coprime v n /\
                (x * n + y * m) MOD (m * n) = (u * n + v * m) MOD (m * n)
            ==> x = u /\ y = v
   Note x * n < n * m                          by LT_MULT_RCANCEL, 0 < n, x < m
    and v * m < n * m                          by LT_MULT_RCANCEL, 0 < m, v < n
   Thus (y * m + (n * m - v * m)) MOD (n * m)
      = (u * n + (n * m - x * n)) MOD (n * m)      by mod_add_eq_sub
    Now y * m + (n * m - v * m) = m * (n + y - v)  by arithmetic
    and u * n + (n * m - x * n) = n * (m + u - x)  by arithmetic
    and 0 < n + y - v /\ n + y - v < 2 * n         by y < n, v < n
    and 0 < m + u - x /\ m + u - x < 2 * m         by x < m, u < m
    ==> n + y - v = n /\ m + u - x = m             by mod_mult_eq_mult
    ==> n + y = n + v /\ m + u = m + x             by arithmetic
    ==> y = v /\ x = u                             by EQ_ADD_LCANCEL
*)
Theorem coprimes_map_cross_inj:
  !m n. coprime m n ==>
        INJ (\(x,y). if (m * n = 1) then 1 else (x * n + y * m) MOD (m * n))
            ((coprimes m) CROSS (coprimes n)) univ(:num)
Proof
  rpt strip_tac >>
  qabbrev_tac `f = \(x,y). if m * n = 1 then 1 else (x * n + y * m) MOD (m * n)` >>
  Cases_on `m = 0 \/ n = 0` >-
  fs[coprimes_0] >>
  Cases_on `m = 1 \/ n = 1` >| [
    fs[coprimes_1, INJ_DEF, pairTheory.FORALL_PROD, Abbr`f`] >| [
      (Cases_on `n = 1` >> simp[coprimes_1]) >>
      fs[coprimes_element_alt],
      (Cases_on `m = 1` >> simp[coprimes_1]) >>
      fs[coprimes_element_alt]
    ],
    `m * n <> 0 /\ m * n <> 1` by rw[] >>
    `1 < m /\ 1 < n /\ 1 < m * n` by decide_tac >>
    simp[INJ_DEF, pairTheory.FORALL_PROD] >>
    ntac 6 strip_tac >>
    rfs[coprimes_element_alt, Abbr`f`] >>
    `0 < m /\ 0 < n /\ 0 < m * n` by decide_tac >>
    `n * p_1 < n * m /\ m * p_2' < n * m` by simp[] >>
    `(m * p_2 + (n * m - m * p_2')) MOD (n * m) =
    (n * p_1' + (n * m - n * p_1)) MOD (n * m)` by simp[GSYM mod_add_eq_sub] >>
    `m * p_2 + (n * m - m * p_2') = m * (n + p_2 - p_2')` by decide_tac >>
    `n * p_1' + (n * m - n * p_1) = n * (m + p_1' - p_1)` by decide_tac >>
    `0 < n + p_2 - p_2' /\ n + p_2 - p_2' < 2 * n` by decide_tac >>
    `0 < m + p_1' - p_1 /\ m + p_1' - p_1 < 2 * m` by decide_tac >>
    `n + p_2 - p_2' = n /\ m + p_1' - p_1 = m` by metis_tac[mod_mult_eq_mult, MULT_COMM] >>
    simp[]
  ]
QED

(* Another milestone theorem! *)

(* Idea: Euler phi function is multiplicative for coprimes. *)

(* Theorem: coprime m n ==> phi (m * n) = phi m * phi n *)
(* Proof:
   Let f = \(x,y). if m * n = 1 then 1 else (x * n + y * m) MOD (m * n),
       u = coprimes m,
       v = coprimes n.
   Then coprimes (m * n) = IMAGE f (u CROSS v) by coprimes_mult_by_image
    and INJ f (u CROSS v) univ(:num)           by coprimes_map_cross_inj
   Note FINITE u /\ FINITE v                   by coprimes_finite
     so FINITE (u CROSS v)                     by FINITE_CROSS
        phi (m * n)
      = CARD (coprimes (m * n))                by phi_def
      = CARD (IMAGE f (u CROSS v))             by above
      = CARD (u CROSS v)                       by INJ_CARD_IMAGE
      = (CARD u) * (CARD v)                    by CARD_CROSS
      = phi m * phi n                          by phi_def
*)
Theorem phi_mult:
  !m n. coprime m n ==> phi (m * n) = phi m * phi n
Proof
  rw[phi_def] >>
  imp_res_tac coprimes_mult_by_image >>
  imp_res_tac coprimes_map_cross_inj >>
  qabbrev_tac `f = \(x,y). if m * n = 1 then 1 else (x * n + y * m) MOD (m * n)` >>
  qabbrev_tac `u = coprimes m` >>
  qabbrev_tac `v = coprimes n` >>
  `FINITE u /\ FINITE v` by rw[coprimes_finite, Abbr`u`, Abbr`v`] >>
  `FINITE (u CROSS v)` by rw[] >>
  metis_tac[INJ_CARD_IMAGE, CARD_CROSS]
QED

(* This is the ultimate goal! *)

(* Idea: an expression for phi (p * q) with distinct primes p and q. *)

(* Theorem: prime p /\ prime q /\ p <> q ==> phi (p * q) = (p - 1) * (q - 1) *)
(* Proof:
   Note coprime p q        by primes_coprime
        phi (p * q)
      = phi p * phi q      by phi_mult
      = (p - 1) * (q - 1)  by phi_prime
*)
Theorem phi_primes_distinct:
  !p q. prime p /\ prime q /\ p <> q ==> phi (p * q) = (p - 1) * (q - 1)
Proof
  simp[primes_coprime, phi_mult, phi_prime]
QED

(* ------------------------------------------------------------------------- *)
(* Euler phi function for prime powers.                                      *)
(* ------------------------------------------------------------------------- *)

(*
EVAL ``coprimes 9``; = {8; 7; 5; 4; 2; 1}
EVAL ``divisors 9``; = {9; 3; 1}
EVAL ``IMAGE (\x. 3 * x) (natural 3)``; = {9; 6; 3}
EVAL ``IMAGE (\x. 3 * x) (natural 9)``; = {27; 24; 21; 18; 15; 12; 9; 6; 3}

> EVAL ``IMAGE ($* 3) (natural (8 DIV 3))``; = {6; 3}
> EVAL ``IMAGE ($* 3) (natural (9 DIV 3))``; = {9; 6; 3}
> EVAL ``IMAGE ($* 3) (natural (10 DIV 3))``; = {9; 6; 3}
> EVAL ``IMAGE ($* 3) (natural (12 DIV 3))``; = {12; 9; 6; 3}
*)

(* Idea: develop a special set in anticipation for counting. *)

(* Define the set of positive multiples of m, up to n *)
val multiples_upto_def = zDefine`
    multiples_upto m n = {x | m divides x /\ 0 < x /\ x <= n}
`;
(* use zDefine as this is not effective for evalutaion. *)
(* make this an infix operator *)
val _ = set_fixity "multiples_upto" (Infix(NONASSOC, 550)); (* higher than arithmetic op 500. *)

(*
> multiples_upto_def;
val it = |- !m n. m multiples_upto n = {x | m divides x /\ 0 < x /\ x <= n}: thm
*)

(* Theorem: x IN m multiples_upto n <=> m divides x /\ 0 < x /\ x <= n *)
(* Proof: by multiples_upto_def. *)
Theorem multiples_upto_element:
  !m n x. x IN m multiples_upto n <=> m divides x /\ 0 < x /\ x <= n
Proof
  simp[multiples_upto_def]
QED

(* Theorem: m multiples_upto n = {x | ?k. x = k * m /\ 0 < x /\ x <= n} *)
(* Proof:
     m multiples_upto n
   = {x | m divides x /\ 0 < x /\ x <= n}      by multiples_upto_def
   = {x | ?k. x = k * m /\ 0 < x /\ x <= n}    by divides_def
*)
Theorem multiples_upto_alt:
  !m n. m multiples_upto n = {x | ?k. x = k * m /\ 0 < x /\ x <= n}
Proof
  rw[multiples_upto_def, EXTENSION] >>
  metis_tac[divides_def]
QED

(* Theorem: x IN m multiples_upto n <=> ?k. x = k * m /\ 0 < x /\ x <= n *)
(* Proof: by multiples_upto_alt. *)
Theorem multiples_upto_element_alt:
  !m n x. x IN m multiples_upto n <=> ?k. x = k * m /\ 0 < x /\ x <= n
Proof
  simp[multiples_upto_alt]
QED

(* Theorem: m multiples_upto n = {x | m divides x /\ x IN natural n} *)
(* Proof:
     m multiples_upto n
   = {x | m divides x /\ 0 < x /\ x <= n}      by multiples_upto_def
   = {x | m divides x /\ x IN natural n}       by natural_element
*)
Theorem multiples_upto_eqn:
  !m n. m multiples_upto n = {x | m divides x /\ x IN natural n}
Proof
  simp[multiples_upto_def, natural_element, EXTENSION]
QED

(* Theorem: 0 multiples_upto n = {} *)
(* Proof:
     0 multiples_upto n
   = {x | 0 divides x /\ 0 < x /\ x <= n}      by multiples_upto_def
   = {x | x = 0 /\ 0 < x /\ x <= n}            by ZERO_DIVIDES
   = {}                                        by contradiction
*)
Theorem multiples_upto_0_n:
  !n. 0 multiples_upto n = {}
Proof
  simp[multiples_upto_def, EXTENSION]
QED

(* Theorem: 1 multiples_upto n = natural n *)
(* Proof:
     1 multiples_upto n
   = {x | 1 divides x /\ x IN natural n}       by multiples_upto_eqn
   = {x | T /\ x IN natural n}                 by ONE_DIVIDES_ALL
   = natural n                                 by EXTENSION
*)
Theorem multiples_upto_1_n:
  !n. 1 multiples_upto n = natural n
Proof
  simp[multiples_upto_eqn, EXTENSION]
QED

(* Theorem: m multiples_upto 0 = {} *)
(* Proof:
     m multiples_upto 0
   = {x | m divides x /\ 0 < x /\ x <= 0}      by multiples_upto_def
   = {x | m divides x /\ F}                    by arithmetic
   = {}                                        by contradiction
*)
Theorem multiples_upto_m_0:
  !m. m multiples_upto 0 = {}
Proof
  simp[multiples_upto_def, EXTENSION]
QED

(* Theorem: m multiples_upto 1 = if m = 1 then {1} else {} *)
(* Proof:
     m multiples_upto 1
   = {x | m divides x /\ 0 < x /\ x <= 1}      by multiples_upto_def
   = {x | m divides x /\ x = 1}                by arithmetic
   = {1} if m = 1, {} otherwise                by DIVIDES_ONE
*)
Theorem multiples_upto_m_1:
  !m. m multiples_upto 1 = if m = 1 then {1} else {}
Proof
  rw[multiples_upto_def, EXTENSION] >>
  spose_not_then strip_assume_tac >>
  `x = 1` by decide_tac >>
  fs[]
QED

(* Idea: an expression for (m multiples_upto n), for direct evaluation. *)

(* Theorem: m multiples_upto n =
            if m = 0 then {}
            else IMAGE ($* m) (natural (n DIV m)) *)
(* Proof:
   If m = 0,
      Then 0 multiples_upto n = {} by multiples_upto_0_n
   If m <> 0.
      By multiples_upto_alt, EXTENSION, this is to show:
      (1) 0 < k * m /\ k * m <= n ==>
          ?y. k * m = m * y /\ ?x. y = SUC x /\ x < n DIV m
          Note k <> 0              by MULT_EQ_0
           and k <= n DIV m        by X_LE_DIV, 0 < m
            so k - 1 < n DIV m     by arithmetic
          Let y = k, x = k - 1.
          Note SUC x = SUC (k - 1) = k = y.
      (2) x < n DIV m ==> ?k. m * SUC x = k * m /\ 0 < m * SUC x /\ m * SUC x <= n
          Note SUC x <= n DIV m    by arithmetic
            so m * SUC x <= n      by X_LE_DIV, 0 < m
           and 0 < m * SUC x       by MULT_EQ_0
          Take k = SUC x, true     by MULT_COMM
*)
Theorem multiples_upto_thm[compute]:
  !m n. m multiples_upto n =
        if m = 0 then {}
        else IMAGE ($* m) (natural (n DIV m))
Proof
  rpt strip_tac >>
  Cases_on `m = 0` >-
  fs[multiples_upto_0_n] >>
  fs[multiples_upto_alt, EXTENSION] >>
  rw[EQ_IMP_THM] >| [
    qexists_tac `k` >>
    simp[] >>
    `0 < k /\ 0 < m` by metis_tac[MULT_EQ_0, NOT_ZERO] >>
    `k <= n DIV m` by rw[X_LE_DIV] >>
    `k - 1 < n DIV m` by decide_tac >>
    qexists_tac `k - 1` >>
    simp[],
    `SUC x'' <= n DIV m` by decide_tac >>
    `m * SUC x'' <= n` by rfs[X_LE_DIV] >>
    simp[] >>
    metis_tac[MULT_COMM]
  ]
QED

(*
EVAL ``3 multiples_upto 9``; = {9; 6; 3}
EVAL ``3 multiples_upto 11``; = {9; 6; 3}
EVAL ``3 multiples_upto 12``; = {12; 9; 6; 3}
EVAL ``3 multiples_upto 13``; = {12; 9; 6; 3}
*)

(* Theorem: m multiples_upto n SUBSET natural n *)
(* Proof: by multiples_upto_eqn, SUBSET_DEF. *)
Theorem multiples_upto_subset:
  !m n. m multiples_upto n SUBSET natural n
Proof
  simp[multiples_upto_eqn, SUBSET_DEF]
QED

(* Theorem: FINITE (m multiples_upto n) *)
(* Proof:
   Let s = m multiples_upto n
   Note s SUBSET natural n     by multiples_upto_subset
    and FINITE natural n       by natural_finite
     so FINITE s               by SUBSET_FINITE
*)
Theorem multiples_upto_finite:
  !m n. FINITE (m multiples_upto n)
Proof
  metis_tac[multiples_upto_subset, natural_finite, SUBSET_FINITE]
QED

(* Theorem: CARD (m multiples_upto n) = if m = 0 then 0 else n DIV m *)
(* Proof:
   If m = 0,
        CARD (0 multiples_upto n)
      = CARD {}                    by multiples_upto_0_n
      = 0                          by CARD_EMPTY
   If m <> 0,
      Claim: INJ ($* m) (natural (n DIV m)) univ(:num)
      Proof: By INJ_DEF, this is to show:
             !x. x IN (natural (n DIV m)) /\
                 m * x = m * y ==> x = y, true     by EQ_MULT_LCANCEL, m <> 0
      Note FINITE (natural (n DIV m))              by natural_finite
        CARD (m multiples_upto n)
      = CARD (IMAGE ($* m) (natural (n DIV m)))    by multiples_upto_thm, m <> 0
      = CARD (natural (n DIV m))                   by INJ_CARD_IMAGE
      = n DIV m                                    by natural_card
*)
Theorem multiples_upto_card:
  !m n. CARD (m multiples_upto n) = if m = 0 then 0 else n DIV m
Proof
  rpt strip_tac >>
  Cases_on `m = 0` >-
  simp[multiples_upto_0_n] >>
  simp[multiples_upto_thm] >>
  `INJ ($* m) (natural (n DIV m)) univ(:num)` by rw[INJ_DEF] >>
  metis_tac[INJ_CARD_IMAGE, natural_finite, natural_card]
QED

(* Idea: an expression for the set of coprimes of a prime power. *)

(* Theorem: prime p ==>
            coprimes (p ** n) = natural (p ** n) DIFF p multiples_upto (p ** n) *)
(* Proof:
   If n = 0,
      LHS = coprimes (p ** 0)
          = coprimes 1             by EXP_0
          = {1}                    by coprimes_1
      RHS = natural (p ** 0) DIFF p multiples_upto (p ** 0)
          = natural 1 DIFF p multiples_upto 1
          = natural 1 DIFF {}      by multiples_upto_m_1, NOT_PRIME_1
          = {1} DIFF {}            by natural_1
          = {1} = LHS              by DIFF_EMPTY
   If n <> 0,
      By coprimes_def, multiples_upto_def, EXTENSION, this is to show:
         coprime (SUC x) (p ** n) <=> ~(p divides SUC x)
      This is true                 by coprime_prime_power
*)
Theorem coprimes_prime_power:
  !p n. prime p ==>
        coprimes (p ** n) = natural (p ** n) DIFF p multiples_upto (p ** n)
Proof
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    `p <> 1` by metis_tac[NOT_PRIME_1] >>
    simp[coprimes_1, multiples_upto_m_1, natural_1, EXP_0],
    rw[coprimes_def, multiples_upto_def, EXTENSION] >>
    (rw[EQ_IMP_THM] >> rfs[coprime_prime_power])
  ]
QED

(* Idea: an expression for phi of a prime power. *)

(* Theorem: prime p ==> phi (p ** SUC n) = (p - 1) * p ** n *)
(* Proof:
   Let m = SUC n,
       u = natural (p ** m),
       v = p multiples_upto (p ** m).
   Note 0 < p                      by PRIME_POS
    and FINITE u                   by natural_finite
    and v SUBSET u                 by multiples_upto_subset

     phi (p ** m)
   = CARD (coprimes (p ** m))      by phi_def
   = CARD (u DIFF v)               by coprimes_prime_power
   = CARD u - CARD v               by SUBSET_DIFF_CARD
   = p ** m - CARD v               by natural_card
   = p ** m - (p ** m DIV p)       by multiples_upto_card, p <> 0
   = p ** m - p ** n               by EXP_SUC_DIV, 0 < p
   = p * p ** n - p ** n           by EXP
   = (p - 1) * p ** n              by RIGHT_SUB_DISTRIB
*)
Theorem phi_prime_power:
  !p n. prime p ==> phi (p ** SUC n) = (p - 1) * p ** n
Proof
  rpt strip_tac >>
  qabbrev_tac `m = SUC n` >>
  qabbrev_tac `u = natural (p ** m)` >>
  qabbrev_tac `v = p multiples_upto (p ** m)` >>
  `0 < p` by rw[PRIME_POS] >>
  `FINITE u` by rw[natural_finite, Abbr`u`] >>
  `v SUBSET u` by rw[multiples_upto_subset, Abbr`v`, Abbr`u`] >>
  `phi (p ** m) = CARD (coprimes (p ** m))` by rw[phi_def] >>
  `_ = CARD (u DIFF v)` by rw[coprimes_prime_power, Abbr`u`, Abbr`v`] >>
  `_ = CARD u - CARD v` by rw[SUBSET_DIFF_CARD] >>
  `_ = p ** m - (p ** m DIV p)` by rw[natural_card, multiples_upto_card, Abbr`u`, Abbr`v`] >>
  `_ = p ** m - p ** n` by rw[EXP_SUC_DIV, Abbr`m`] >>
  `_ = p * p ** n - p ** n` by rw[GSYM EXP] >>
  `_ = (p - 1) * p ** n` by decide_tac >>
  simp[]
QED

(* Yes, a spectacular theorem! *)

(* Idea: specialise phi_prime_power for prime squared. *)

(* Theorem: prime p ==> phi (p * p) = p * (p - 1) *)
(* Proof:
     phi (p * p)
   = phi (p ** 2)          by EXP_2
   = phi (p ** SUC 1)      by TWO
   = (p - 1) * p ** 1      by phi_prime_power
   = p * (p - 1)           by EXP_1
*)
Theorem phi_prime_sq:
  !p. prime p ==> phi (p * p) = p * (p - 1)
Proof
  rpt strip_tac >>
  `phi (p * p) = phi (p ** SUC 1)` by rw[] >>
  simp[phi_prime_power]
QED

(* Idea: Euler phi function for a product of primes. *)

(* Theorem: prime p /\ prime q ==>
            phi (p * q) = if p = q then p * (p - 1) else (p - 1) * (q - 1) *)
(* Proof:
   If p = q, phi (p * p) = p * (p - 1)         by phi_prime_sq
   If p <> q, phi (p * q) = (p - 1) * (q - 1)  by phi_primes_distinct
*)
Theorem phi_primes:
  !p q. prime p /\ prime q ==>
        phi (p * q) = if p = q then p * (p - 1) else (p - 1) * (q - 1)
Proof
  metis_tac[phi_prime_sq, phi_primes_distinct]
QED

(* Finally, another nice result. *)

(* ------------------------------------------------------------------------- *)
(* Recursive definition of phi                                               *)
(* ------------------------------------------------------------------------- *)

(* Define phi by recursion *)
Definition rec_phi_def:
  rec_phi n = if n = 0 then 0
         else if n = 1 then 1
         else n - SIGMA rec_phi { m | m < n /\ m divides n}
Termination
  WF_REL_TAC `$< : num -> num -> bool` >> srw_tac[][]
End
(* This is the recursive form of Gauss' Little Theorem:  n = SUM phi m, m divides n *)

(* Just using Define without any condition will trigger:

Initial goal:

?R. WF R /\ !n a. n <> 0 /\ n <> 1 /\ a IN {m | m < n /\ m divides n} ==> R a n

Unable to prove termination!

Try using "TotalDefn.tDefine <name> <quotation> <tac>".

The termination goal has been set up using Defn.tgoal <defn>.

So one can set up:
g `?R. WF R /\ !n a. n <> 0 /\ n <> 1 /\ a IN {m | m < n /\ m divides n} ==> R a n`;
e (WF_REL_TAC `$< : num -> num -> bool`);
e (srw[][]);

which gives the tDefine solution.
*)

(* Theorem: rec_phi 0 = 0 *)
(* Proof: by rec_phi_def *)
val rec_phi_0 = store_thm(
  "rec_phi_0",
  ``rec_phi 0 = 0``,
  rw[rec_phi_def]);

(* Theorem: rec_phi 1 = 1 *)
(* Proof: by rec_phi_def *)
val rec_phi_1 = store_thm(
  "rec_phi_1",
  ``rec_phi 1 = 1``,
  rw[Once rec_phi_def]);

(* Theorem: rec_phi n = phi n *)
(* Proof:
   By complete induction on n.
   If n = 0,
      rec_phi 0 = 0      by rec_phi_0
                = phi 0  by phi_0
   If n = 1,
      rec_phi 1 = 1      by rec_phi_1
                = phi 1  by phi_1
   Othewise, 0 < n, 1 < n.
      Let s = {m | m < n /\ m divides n}.
      Note s SUBSET (count n)       by SUBSET_DEF
      thus FINITE s                 by SUBSET_FINITE, FINITE_COUNT
     Hence !m. m IN s
       ==> (rec_phi m = phi m)      by induction hypothesis
      Also n NOTIN s                by EXTENSION
       and n INSERT s
         = {m | m <= n /\ m divides n}
         = {m | 0 < m /\ m <= n /\ m divides n}      by divisor_pos, 0 < n
         = divisors n               by divisors_def, EXTENSION, LESS_OR_EQ

        rec_phi n
      = n - (SIGMA rec_phi s)       by rec_phi_def
      = n - (SIGMA phi s)           by SUM_IMAGE_CONG, rec_phi m = phi m
      = (SIGMA phi (divisors n)) - (SIGMA phi s)           by Gauss' Little Theorem
      = (SIGMA phi (n INSERT s)) - (SIGMA phi s)           by divisors n = n INSERT s
      = (phi n + SIGMA phi (s DELETE n)) - (SIGMA phi s)   by SUM_IMAGE_THM
      = (phi n + SIGMA phi s) - (SIGMA phi s)              by DELETE_NON_ELEMENT
      = phi n                                              by ADD_SUB
*)
Theorem rec_phi_eq_phi:
  !n. rec_phi n = phi n
Proof
  completeInduct_on `n` >>
  Cases_on `n = 0` >-
  rw[rec_phi_0, phi_0] >>
  Cases_on `n = 1` >-
  rw[rec_phi_1, phi_1] >>
  `0 < n /\ 1 < n` by decide_tac >>
  qabbrev_tac `s = {m | m < n /\ m divides n}` >>
  qabbrev_tac `t = SIGMA rec_phi s` >>
  `!m. m IN s <=> m < n /\ m divides n` by rw[Abbr`s`] >>
  `!m. m IN s ==> (rec_phi m = phi m)` by rw[] >>
  `t = SIGMA phi s` by rw[SUM_IMAGE_CONG, Abbr`t`] >>
  `s SUBSET (count n)` by rw[SUBSET_DEF] >>
  `FINITE s` by metis_tac[SUBSET_FINITE, FINITE_COUNT] >>
  `n NOTIN s` by rw[] >>
  (`n INSERT s = divisors n` by (rw[divisors_def, EXTENSION] >> metis_tac[divisor_pos, LESS_OR_EQ, DIVIDES_REFL])) >>
  `n = SIGMA phi (divisors n)` by rw[Gauss_little_thm] >>
  `_ = phi n + SIGMA phi (s DELETE n)` by rw[GSYM SUM_IMAGE_THM] >>
  `_ = phi n + t` by metis_tac[DELETE_NON_ELEMENT] >>
  `rec_phi n = n - t` by metis_tac[rec_phi_def] >>
  decide_tac
QED


(* ------------------------------------------------------------------------- *)
(* Useful Theorems (not used).                                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: INJ (coprimes) (univ(:num) DIFF {1}) univ(:num -> bool) *)
(* Proof:
   By INJ_DEF, this is to show:
      x <> 1 /\ y <> 1 /\ coprimes x = coprimes y ==> x = y
   If x = 0, then y = 0              by coprimes_eq_empty
   If y = 0, then x = 0              by coprimes_eq_empty
   If x <> 0 and y <> 0,
      with x <> 1 and y <> 1         by given
      then 1 < x and 1 < y.
      Since MAX_SET (coprimes x) = x - 1    by coprimes_max, 1 < x
        and MAX_SET (coprimes y) = y - 1    by coprimes_max, 1 < y
         If coprimes x = coprimes y,
                 x - 1 = y - 1       by above
      Hence          x = y           by CANCEL_SUB
*)
val coprimes_from_not_1_inj = store_thm(
  "coprimes_from_not_1_inj",
  ``INJ (coprimes) (univ(:num) DIFF {1}) univ(:num -> bool)``,
  rw[INJ_DEF] >>
  Cases_on `x = 0` >-
  metis_tac[coprimes_eq_empty] >>
  Cases_on `y = 0` >-
  metis_tac[coprimes_eq_empty] >>
  `1 < x /\ 1 < y` by decide_tac >>
  `x - 1 = y - 1` by metis_tac[coprimes_max] >>
  decide_tac);
(* Not very useful. *)

(* Here is group of related theorems for (divisors n):
   divisors_eq_image_gcd_upto
   divisors_eq_image_gcd_count
   divisors_eq_image_gcd_natural

   This first one is proved independently, then the second and third are derived.
   Of course, the best is the third one, which is now divisors_eq_gcd_image (above)
   Here, I rework all proofs of these three from divisors_eq_gcd_image,
   so divisors_eq_image_gcd_natural = divisors_eq_gcd_image.
*)

(* Theorem: 0 < n ==> divisors n = IMAGE (gcd n) (upto n) *)
(* Proof:
   Note gcd n 0 = n                                by GCD_0
    and n IN divisors n                            by divisors_has_last, 0 < n
     divisors n
   = (gcd n 0) INSERT (divisors n)                 by ABSORPTION
   = (gcd n 0) INSERT (IMAGE (gcd n) (natural n))  by divisors_eq_gcd_image
   = IMAGE (gcd n) (0 INSERT (natural n))          by IMAGE_INSERT
   = IMAGE (gcd n) (upto n)                        by upto_by_natural
*)
Theorem divisors_eq_image_gcd_upto:
  !n. 0 < n ==> divisors n = IMAGE (gcd n) (upto n)
Proof
  rpt strip_tac >>
  `IMAGE (gcd n) (upto n) = IMAGE (gcd n) (0 INSERT natural n)` by simp[upto_by_natural] >>
  `_ = (gcd n 0) INSERT (IMAGE (gcd n) (natural n))` by fs[] >>
  `_ = n INSERT (divisors n)` by fs[divisors_eq_gcd_image] >>
  metis_tac[divisors_has_last, ABSORPTION]
QED

(* Theorem: (feq (gcd n)) equiv_on (upto n) *)
(* Proof:
   By feq_equiv |- !s f. feq f equiv_on s
   Taking s = upto n, f = gcd n.
*)
val gcd_eq_equiv_on_upto = store_thm(
  "gcd_eq_equiv_on_upto",
  ``!n. (feq (gcd n)) equiv_on (upto n)``,
  rw[feq_equiv]);

(* Theorem: 0 < n ==> partition (feq (gcd n)) (upto n) = IMAGE (preimage (gcd n) (upto n)) (divisors n) *)
(* Proof:
   Let f = gcd n, s = upto n.
     partition (feq f) s
   = IMAGE (preimage f s o f) s                      by feq_partition
   = IMAGE (preimage f s) (IMAGE f s)                by IMAGE_COMPOSE
   = IMAGE (preimage f s) (IMAGE (gcd n) (upto n))   by expansion
   = IMAGE (preimage f s) (divisors n)               by divisors_eq_image_gcd_upto, 0 < n
*)
val gcd_eq_upto_partition_by_divisors = store_thm(
  "gcd_eq_upto_partition_by_divisors",
  ``!n. 0 < n ==> partition (feq (gcd n)) (upto n) = IMAGE (preimage (gcd n) (upto n)) (divisors n)``,
  rpt strip_tac >>
  qabbrev_tac `f = gcd n` >>
  qabbrev_tac `s = upto n` >>
  `partition (feq f) s = IMAGE (preimage f s o f) s` by rw[feq_partition] >>
  `_ = IMAGE (preimage f s) (IMAGE f s)` by rw[IMAGE_COMPOSE] >>
  rw[divisors_eq_image_gcd_upto, Abbr`f`, Abbr`s`]);

(* Theorem: SIGMA f (upto n) = SIGMA (SIGMA f) (partition (feq (gcd n)) (upto n)) *)
(* Proof:
   Let g = gcd n, s = upto n.
   Since FINITE s               by upto_finite
     and (feq g) equiv_on s     by feq_equiv
   The result follows           by set_sigma_by_partition
*)
val sum_over_upto_by_gcd_partition = store_thm(
  "sum_over_upto_by_gcd_partition",
  ``!f n. SIGMA f (upto n) = SIGMA (SIGMA f) (partition (feq (gcd n)) (upto n))``,
  rw[feq_equiv, set_sigma_by_partition]);

(* Theorem: 0 < n ==> SIGMA f (upto n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (upto n)) (divisors n)) *)
(* Proof:
     SIGMA f (upto n)
   = SIGMA (SIGMA f) (partition (feq (gcd n)) (upto n))                by sum_over_upto_by_gcd_partition
   = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (upto n)) (divisors n))  by gcd_eq_upto_partition_by_divisors, 0 < n
*)
val sum_over_upto_by_divisors = store_thm(
  "sum_over_upto_by_divisors",
  ``!f n. 0 < n ==> SIGMA f (upto n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (upto n)) (divisors n))``,
  rw[sum_over_upto_by_gcd_partition, gcd_eq_upto_partition_by_divisors]);

(* Similar results based on count *)

(* Theorem: divisors n = IMAGE (gcd n) (count n) *)
(* Proof:
   If n = 0,
      LHS = divisors 0 = {}                      by divisors_0
      RHS = IMAGE (gcd 0) (count 0)
          = IMAGE (gcd 0) {}                     by COUNT_0
          = {} = LHS                             by IMAGE_EMPTY
  If n <> 0, 0 < n.
     divisors n
   = IMAGE (gcd n) (upto n)                      by divisors_eq_image_gcd_upto, 0 < n
   = IMAGE (gcd n) (n INSERT (count n))          by upto_by_count
   = (gcd n n) INSERT (IMAGE (gcd n) (count n))  by IMAGE_INSERT
   = n INSERT (IMAGE (gcd n) (count n))          by GCD_REF
   = (gcd n 0) INSERT (IMAGE (gcd n) (count n))  by GCD_0R
   = IMAGE (gcd n) (0 INSERT (count n))          by IMAGE_INSERT
   = IMAGE (gcd n) (count n)                     by IN_COUNT, ABSORPTION, 0 < n.
*)
Theorem divisors_eq_image_gcd_count:
  !n. divisors n = IMAGE (gcd n) (count n)
Proof
  rpt strip_tac >>
  Cases_on `n = 0` >-
  simp[divisors_0] >>
  `0 < n` by decide_tac >>
  `divisors n = IMAGE (gcd n) (upto n)` by rw[divisors_eq_image_gcd_upto] >>
  `_ = IMAGE (gcd n) (n INSERT (count n))` by rw[upto_by_count] >>
  `_ = n INSERT (IMAGE (gcd n) (count n))` by rw[GCD_REF] >>
  `_ = (gcd n 0) INSERT (IMAGE (gcd n) (count n))` by rw[GCD_0R] >>
  `_ = IMAGE (gcd n) (0 INSERT (count n))` by rw[] >>
  metis_tac[IN_COUNT, ABSORPTION]
QED

(* Theorem: (feq (gcd n)) equiv_on (count n) *)
(* Proof:
   By feq_equiv |- !s f. feq f equiv_on s
   Taking s = upto n, f = count n.
*)
val gcd_eq_equiv_on_count = store_thm(
  "gcd_eq_equiv_on_count",
  ``!n. (feq (gcd n)) equiv_on (count n)``,
  rw[feq_equiv]);

(* Theorem: partition (feq (gcd n)) (count n) = IMAGE (preimage (gcd n) (count n)) (divisors n) *)
(* Proof:
   Let f = gcd n, s = count n.
     partition (feq f) s
   = IMAGE (preimage f s o f) s                      by feq_partition
   = IMAGE (preimage f s) (IMAGE f s)                by IMAGE_COMPOSE
   = IMAGE (preimage f s) (IMAGE (gcd n) (count n))  by expansion
   = IMAGE (preimage f s) (divisors n)               by divisors_eq_image_gcd_count
*)
Theorem gcd_eq_count_partition_by_divisors:
  !n. partition (feq (gcd n)) (count n) = IMAGE (preimage (gcd n) (count n)) (divisors n)
Proof
  rpt strip_tac >>
  qabbrev_tac `f = gcd n` >>
  qabbrev_tac `s = count n` >>
  `partition (feq f) s = IMAGE (preimage f s o f) s` by rw[feq_partition] >>
  `_ = IMAGE (preimage f s) (IMAGE f s)` by rw[IMAGE_COMPOSE] >>
  rw[divisors_eq_image_gcd_count, Abbr`f`, Abbr`s`]
QED

(* Theorem: SIGMA f (count n) = SIGMA (SIGMA f) (partition (feq (gcd n)) (count n)) *)
(* Proof:
   Let g = gcd n, s = count n.
   Since FINITE s               by FINITE_COUNT
     and (feq g) equiv_on s     by feq_equiv
   The result follows           by set_sigma_by_partition
*)
val sum_over_count_by_gcd_partition = store_thm(
  "sum_over_count_by_gcd_partition",
  ``!f n. SIGMA f (count n) = SIGMA (SIGMA f) (partition (feq (gcd n)) (count n))``,
  rw[feq_equiv, set_sigma_by_partition]);

(* Theorem: SIGMA f (count n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (count n)) (divisors n)) *)
(* Proof:
     SIGMA f (count n)
   = SIGMA (SIGMA f) (partition (feq (gcd n)) (count n))                by sum_over_count_by_gcd_partition
   = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (count n)) (divisors n))  by gcd_eq_count_partition_by_divisors
*)
Theorem sum_over_count_by_divisors:
  !f n. SIGMA f (count n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (count n)) (divisors n))
Proof
  rw[sum_over_count_by_gcd_partition, gcd_eq_count_partition_by_divisors]
QED

(* Similar results based on natural *)

(* Theorem: divisors n = IMAGE (gcd n) (natural n) *)
(* Proof:
   If n = 0,
      LHS = divisors 0 = {}                      by divisors_0
      RHS = IMAGE (gcd 0) (natural 0)
          = IMAGE (gcd 0) {}                     by natural_0
          = {} = LHS                             by IMAGE_EMPTY
  If n <> 0, 0 < n.
     divisors n
   = IMAGE (gcd n) (upto n)                        by divisors_eq_image_gcd_upto, 0 < n
   = IMAGE (gcd n) (0 INSERT natural n)            by upto_by_natural
   = (gcd 0 n) INSERT (IMAGE (gcd n) (natural n))  by IMAGE_INSERT
   = n INSERT (IMAGE (gcd n) (natural n))          by GCD_0L
   = (gcd n n) INSERT (IMAGE (gcd n) (natural n))  by GCD_REF
   = IMAGE (gcd n) (n INSERT (natural n))          by IMAGE_INSERT
   = IMAGE (gcd n) (natural n)                     by natural_has_last, ABSORPTION, 0 < n.
*)
Theorem divisors_eq_image_gcd_natural:
  !n. divisors n = IMAGE (gcd n) (natural n)
Proof
  rpt strip_tac >>
  Cases_on `n = 0` >-
  simp[divisors_0, natural_0] >>
  `0 < n` by decide_tac >>
  `divisors n = IMAGE (gcd n) (upto n)` by rw[divisors_eq_image_gcd_upto] >>
  `_ = IMAGE (gcd n) (0 INSERT (natural n))` by rw[upto_by_natural] >>
  `_ = n INSERT (IMAGE (gcd n) (natural n))` by rw[GCD_0L] >>
  `_ = (gcd n n) INSERT (IMAGE (gcd n) (natural n))` by rw[GCD_REF] >>
  `_ = IMAGE (gcd n) (n INSERT (natural n))` by rw[] >>
  metis_tac[natural_has_last, ABSORPTION]
QED
(* This is the same as divisors_eq_gcd_image *)

(* Theorem: partition (feq (gcd n)) (natural n) = IMAGE (preimage (gcd n) (natural n)) (divisors n) *)
(* Proof:
   Let f = gcd n, s = natural n.
     partition (feq f) s
   = IMAGE (preimage f s o f) s                        by feq_partition
   = IMAGE (preimage f s) (IMAGE f s)                  by IMAGE_COMPOSE
   = IMAGE (preimage f s) (IMAGE (gcd n) (natural n))  by expansion
   = IMAGE (preimage f s) (divisors n)                 by divisors_eq_image_gcd_natural
*)
Theorem gcd_eq_natural_partition_by_divisors:
  !n. partition (feq (gcd n)) (natural n) = IMAGE (preimage (gcd n) (natural n)) (divisors n)
Proof
  rpt strip_tac >>
  qabbrev_tac `f = gcd n` >>
  qabbrev_tac `s = natural n` >>
  `partition (feq f) s = IMAGE (preimage f s o f) s` by rw[feq_partition] >>
  `_ = IMAGE (preimage f s) (IMAGE f s)` by rw[IMAGE_COMPOSE] >>
  rw[divisors_eq_image_gcd_natural, Abbr`f`, Abbr`s`]
QED

(* Theorem: SIGMA f (natural n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (natural n)) (divisors n)) *)
(* Proof:
     SIGMA f (natural n)
   = SIGMA (SIGMA f) (partition (feq (gcd n)) (natural n))                by sum_over_natural_by_gcd_partition
   = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (natural n)) (divisors n))  by gcd_eq_natural_partition_by_divisors
*)
Theorem sum_over_natural_by_preimage_divisors:
  !f n. SIGMA f (natural n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (natural n)) (divisors n))
Proof
  rw[sum_over_natural_by_gcd_partition, gcd_eq_natural_partition_by_divisors]
QED

(* Theorem: (f 0 = g 0) /\ (!n. SIGMA f (divisors n) = SIGMA g (divisors n)) ==> (f = g) *)
(* Proof:
   By FUN_EQ_THM, this is to show: !x. f x = g x.
   By complete induction on x.
   Let s = divisors x, t = s DELETE x.
   If x = 0, f 0 = g 0 is true            by given
   Otherwise x <> 0.
   Then x IN s                            by divisors_has_last, 0 < x
    and s = x INSERT t /\ x NOTIN t       by INSERT_DELETE, IN_DELETE
   Note FINITE s                          by divisors_finite
     so FINITE t                          by FINITE_DELETE

   Claim: SIGMA f t = SIGMA g t
   Proof: By SUM_IMAGE_CONG, this is to show:
             !z. z IN t ==> (f z = g z)
          But z IN s <=> 0 < z /\ z <= x /\ z divides x     by divisors_element
           so z IN t <=> 0 < z /\ z < x /\ z divides x      by IN_DELETE
          ==> f z = g z                                     by induction hypothesis, [1]

   Now      SIGMA f s = SIGMA g s         by implication
   or f x + SIGMA f t = g x + SIGMA g t   by SUM_IMAGE_INSERT
   or             f x = g x               by [1], SIGMA f t = SIGMA g t
*)
Theorem sum_image_divisors_cong:
  !f g. (f 0 = g 0) /\ (!n. SIGMA f (divisors n) = SIGMA g (divisors n)) ==> (f = g)
Proof
  rw[FUN_EQ_THM] >>
  completeInduct_on `x` >>
  qabbrev_tac `s = divisors x` >>
  qabbrev_tac `t = s DELETE x` >>
  (Cases_on `x = 0` >> simp[]) >>
  `x IN s` by rw[divisors_has_last, Abbr`s`] >>
  `s = x INSERT t /\ x NOTIN t` by rw[Abbr`t`] >>
  `SIGMA f t = SIGMA g t` by
  ((irule SUM_IMAGE_CONG >> simp[]) >>
  rw[divisors_element, Abbr`t`, Abbr`s`]) >>
  `FINITE t` by rw[divisors_finite, Abbr`t`, Abbr`s`] >>
  `SIGMA f s = f x + SIGMA f t` by rw[SUM_IMAGE_INSERT] >>
  `SIGMA g s = g x + SIGMA g t` by rw[SUM_IMAGE_INSERT] >>
  `SIGMA f s = SIGMA g s` by metis_tac[] >>
  decide_tac
QED
(* But this is not very useful! *)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
