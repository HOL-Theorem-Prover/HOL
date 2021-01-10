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
   divisors_def            |- !n. divisors n = {d | d <= n /\ d divides n}
   divisors_element        |- !n d. d IN divisors n <=> d <= n /\ d divides n
   divisors_element_alt    |- !n. 0 < n ==> !d. d IN divisors n <=> d divides n
   divisors_has_one        |- !n. 0 < n ==> 1 IN divisors n
   divisors_has_last       |- !n. n IN divisors n
   divisors_not_empty      |- !n. divisors n <> {}
!  divisors_eqn            |- !n. divisors n =
                                  if n = 0 then {0}
                                  else IMAGE (\j. if j + 1 divides n then j + 1 else 1) (count n)
   divisors_cofactor       |- !n d. 0 < n /\ d IN divisors n ==> n DIV d IN divisors n
   divisors_delete_last    |- !n. 0 < n ==> (divisors n DELETE n = {m | m < n /\ m divides n})
   divisors_nonzero        |- !n. 0 < n ==> !d. d IN divisors n ==> 0 < d
   divisors_has_cofactor   |- !n. 0 < n ==> !d. d IN divisors n ==> n DIV d IN divisors n
   divisors_subset_upto    |- !n. divisors n SUBSET upto n
   divisors_subset_natural |- !n. 0 < n ==> divisors n SUBSET natural n
   divisors_finite         |- !n. FINITE (divisors n)
   divisors_0              |- divisors 0 = {0}
   divisors_1              |- divisors 1 = {1}
   divisors_has_0          |- !n. 0 IN divisors n <=> (n = 0)
   divisors_divisors_bij   |- !n. 0 < n ==> (\d. n DIV d) PERMUTES divisors n

   Gauss' Little Theorem:
   gcd_matches_divisor_element  |- !n d. d divides n ==>
                                   !j. j IN gcd_matches n d ==> j DIV d IN coprimes_by n d
   gcd_matches_bij_coprimes_by  |- !n d. d divides n ==>
                                   BIJ (\j. j DIV d) (gcd_matches n d) (coprimes_by n d)
   gcd_matches_bij_coprimes     |- !n d. 0 < n /\ d divides n ==>
                                   BIJ (\j. j DIV d) (gcd_matches n d) (coprimes (n DIV d))
   divisors_eq_gcd_image    |- !n. 0 < n ==> (divisors n = IMAGE (gcd n) (natural n))
   gcd_eq_equiv_class       |- !n d. feq_class (gcd n) (natural n) d = gcd_matches n d
   gcd_eq_equiv_class_fun   |- !n. feq_class (gcd n) (natural n) = gcd_matches n
   gcd_eq_partition_by_divisors |- !n. 0 < n ==> (partition (feq (gcd n)) (natural n) =
                                   IMAGE (gcd_matches n) (divisors n))
   gcd_eq_equiv_on_natural        |- !n. feq (gcd n) equiv_on natural n
   sum_over_natural_by_gcd_partition
                                  |- !f n. SIGMA f (natural n) =
                                           SIGMA (SIGMA f) (partition (feq (gcd n)) (natural n))
   sum_over_natural_by_divisors   |- !f n. SIGMA f (natural n) =
                                              SIGMA (SIGMA f) (IMAGE (gcd_matches n) (divisors n))
   gcd_matches_from_divisors_inj  |- !n. INJ (gcd_matches n) (divisors n) univ(:num -> bool)
   gcd_matches_and_coprimes_by_same_size |- !n. CARD o gcd_matches n = CARD o coprimes_by n
   coprimes_by_with_card      |- !n. 0 < n ==> (CARD o coprimes_by n =
                                               (\d. phi (if d IN divisors n then n DIV d else 0)))
   coprimes_by_divisors_card  |- !n. 0 < n ==> !x. x IN divisors n ==>
                                               ((CARD o coprimes_by n) x = (\d. phi (n DIV d)) x)
   Gauss_little_thm           |- !n. n = SIGMA phi (divisors n)

   Recursive definition of phi:
   rec_phi_def      |- !n. rec_phi n = if n = 0 then 0
                                  else if n = 1 then 1
                                  else n - SIGMA (\a. rec_phi a) {m | m < n /\ m divides n}
   rec_phi_0        |- rec_phi 0 = 0
   rec_phi_1        |- rec_phi 1 = 1
   rec_phi_eq_phi   |- !n. rec_phi n = phi n

   Not Used:
   coprimes_from_notone_inj       |- INJ coprimes (univ(:num) DIFF {1}) univ(:num -> bool)
   divisors_eq_image_gcd_upto     |- !n. divisors n = IMAGE (gcd n) (upto n)
   gcd_eq_equiv_on_upto           |- !n. feq (gcd n) equiv_on upto n
   gcd_eq_upto_partition_by_divisors   |- !n. partition (feq (gcd n)) (upto n) =
                                          IMAGE (preimage (gcd n) (upto n)) (divisors n)
   sum_over_upto_by_gcd_partition |- !f n. SIGMA f (upto n) =
                                           SIGMA (SIGMA f) (partition (feq (gcd n)) (upto n))
   sum_over_upto_by_divisors      |- !f n. SIGMA f (upto n) =
                                           SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (upto n)) (divisors n))

   divisors_eq_image_gcd_count    |- !n. 0 < n ==> (divisors n = IMAGE (gcd n) (count n))
   gcd_eq_equiv_on_count          |- !n. feq (gcd n) equiv_on count n
   gcd_eq_count_partition_by_divisors  |- !n. 0 < n ==> (partition (feq (gcd n)) (count n) =
                                          IMAGE (preimage (gcd n) (count n)) (divisors n))
   sum_over_count_by_gcd_partition     |- !f n. SIGMA f (count n) =
                                          SIGMA (SIGMA f) (partition (feq (gcd n)) (count n))
   sum_over_count_by_divisors     |- !f n. 0 < n ==> (SIGMA f (count n) =
                                     SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (count n)) (divisors n)))

   divisors_eq_image_gcd_natural  |- !n. 0 < n ==> (divisors n = IMAGE (gcd n) (natural n))
   gcd_eq_natural_partition_by_divisors   |- !n. 0 < n ==> (partition (feq (gcd n)) (natural n) =
                                             IMAGE (preimage (gcd n) (natural n)) (divisors n))
   sum_over_natural_by_preimage_divisors  |- !f n. 0 < n ==> (SIGMA f (natural n) =
                                     SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (natural n)) (divisors n)))
   sum_image_divisors_cong        |- !f g. (f 1 = g 1) /\
                                           (!n. SIGMA f (divisors n) = SIGMA g (divisors n)) ==> (f = g)
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
      Thus n < d         by DIV_EQ_0
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
    `n < d` by rw[GSYM DIV_EQ_0] >>
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
val divisors_def = zDefine `
   divisors n = {d | d <= n /\ d divides n}
`;
(* use zDefine as this is not computationally effective. *)
(* Note: use of d <= n to give bounded divisors, so that divisors_0 = {0} only. *)
(* Note: for 0 < n, d <= n is redundant, as DIVIDES_LE implies it. *)

(* Theorem: d IN divisors n <=> d <= n /\ d divides n *)
(* Proof: by divisors_def *)
val divisors_element = store_thm(
  "divisors_element",
  ``!n d. d IN divisors n <=> d <= n /\ d divides n``,
  rw[divisors_def]);

(* Theorem: 0 < n ==> !d. d IN divisors n <=> d divides n *)
(* Proof:
   If part: d IN divisors n ==> d divides n
      True by divisors_element
   Only-if part: 0 < n /\ d divides n ==> d IN divisors n
      Since 0 < n /\ d divides n
        ==> 0 < d /\ d <= n      by divides_pos
       Hence d IN divisors n     by divisors_element
*)
val divisors_element_alt = store_thm(
  "divisors_element_alt",
  ``!n. 0 < n ==> !d. d IN divisors n <=> d divides n``,
  metis_tac[divisors_element, divides_pos]);

(* Theorem: 0 < n ==> 1 IN (divisors n) *)
(* Proof:
    Note 0 < n ==> 1 <= n    by arithmetic
     and 1 divides n         by ONE_DIVIDES_ALL
   Hence 1 IN (divisors n)   by divisors_element
*)
val divisors_has_one = store_thm(
  "divisors_has_one",
  ``!n. 0 < n ==> 1 IN (divisors n)``,
  rw[divisors_element]);

(* Theorem: n IN (divisors n) *)
(* Proof: by divisors_element *)
val divisors_has_last = store_thm(
  "divisors_has_last",
  ``!n. n IN (divisors n)``,
  rw[divisors_element]);

(* Theorem: divisors n <> {} *)
(* Proof: by divisors_has_last, MEMBER_NOT_EMPTY *)
val divisors_not_empty = store_thm(
  "divisors_not_empty",
  ``!n. divisors n <> {}``,
  metis_tac[divisors_has_last, MEMBER_NOT_EMPTY]);

(* Idea: a method to evaluate divisors. *)

(* Theorem: divisors n =
            if n = 0 then {0}
            else IMAGE (\j. if (j + 1) divides n then j + 1 else 1) (count n) *)
(* Proof:
   If n = 0,
        divisors 0
      = {d | d <= 0 /\ d divides 0}      by divisors_def
      = {0}                              by d <= 0, and ALL_DIVIDES_0
   If n <> 0,
        divisors n
      = {d | d <= n /\ d divides n}      by divisors_def
      = {d | d <> 0 /\ d <= n /\ d divides n}
                                         by ZERO_DIVIDES
      = {k + 1 | (k + 1) <= n /\ (k + 1) divides n}
                                         by num_CASES, d <> 0
      = {k + 1 | k < n /\ (k + 1) divides n}
                                         by arithmetic
      = IMAGE (\j. if (j + 1) divides n then j + 1 else 1) {k | k < n}
                                         by IMAGE_DEF
      = IMAGE (\j. if (j + 1) divides n then j + 1 else 1) (count n)
                                         by count_def
*)
Theorem divisors_eqn[compute]:
  !n. divisors n =
       if n = 0 then {0}
       else IMAGE (\j. if (j + 1) divides n then j + 1 else 1) (count n)
Proof
  (rw[divisors_def, EXTENSION, EQ_IMP_THM] >> rw[]) >>
  `x <> 0` by metis_tac[ZERO_DIVIDES] >>
  `?k. x = SUC k` by metis_tac[num_CASES] >>
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

(* Idea: when factor divides, its cofactor also divides. *)

(* Theorem: 0 < n /\ d IN divisors n ==> (n DIV d) IN divisors n *)
(* Proof:
   Note d <= n /\ d divides n      by divisors_def
     so 0 < d                      by ZERO_DIVIDES
    and n DIV d <= n               by DIV_LESS_EQ, 0 < d
    and n DIV d divides n          by DIVIDES_COFACTOR, 0 < d
*)
Theorem divisors_cofactor:
  !n d. 0 < n /\ d IN divisors n ==> (n DIV d) IN divisors n
Proof
  simp [divisors_def] >>
  ntac 3 strip_tac >>
  `0 < d` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
  rw[DIV_LESS_EQ, DIVIDES_COFACTOR]
QED

(* Theorem: 0 < n ==> ((divisors n) DELETE n = {m | m < n /\ m divides n}) *)
(* Proof:
     (divisors n) DELETE n
   = {m | m <= n /\ m divides n} DELETE n     by divisors_def
   = {m | m <= n /\ m divides n} DIFF {n}     by DELETE_DEF
   = {m | m <> n /\ m <= n /\ m divides n}    by IN_DIFF
   = {m | m < n /\ m divides n}               by LESS_OR_EQ
*)
val divisors_delete_last = store_thm(
  "divisors_delete_last",
  ``!n. 0 < n ==> ((divisors n) DELETE n = {m | m < n /\ m divides n})``,
  rw[divisors_def, EXTENSION, EQ_IMP_THM]);

(* Theorem: 0 < n ==> !d. d IN (divisors n) ==> 0 < d *)
(* Proof:
   Since d IN (divisors n), d divides n      by divisors_element
   By contradiction, if d = 0, then n = 0    by ZERO_DIVIDES
   This contradicts 0 < n.
*)
val divisors_nonzero = store_thm(
  "divisors_nonzero",
  ``!n. 0 < n ==> !d. d IN (divisors n) ==> 0 < d``,
  metis_tac[divisors_element, ZERO_DIVIDES, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < n ==> !d. d IN divisors n ==> n DIV d IN divisors n *)
(* Proof:
   By divisors_element, this is to show:
      0 < n /\ d <= n /\ d divides n ==> n DIV d <= n /\ n DIV d divides n
   Since 0 < n /\ d divides n ==> 0 < d   by divisor_pos
      so n = (n DIV d) * d                by DIVIDES_EQN, 0 < d
           = d * (n DIV d)                by MULT_COMM
   Hence (n DIV d) divides n              by divides_def
     and (n DIV d) <= n                   by DIVIDES_LE, 0 < n
*)
val divisors_has_cofactor = store_thm(
  "divisors_has_cofactor",
  ``!n. 0 < n ==> !d. d IN divisors n ==> n DIV d IN divisors n``,
  rewrite_tac[divisors_element] >>
  ntac 4 strip_tac >>
  `0 < d` by metis_tac[divisor_pos] >>
  `n = (n DIV d) * d` by rw[GSYM DIVIDES_EQN] >>
  `_ = d * (n DIV d)` by rw[MULT_COMM] >>
  metis_tac[divides_def, DIVIDES_LE]);

(* Theorem: divisors n SUBSET upto n *)
(* Proof: by divisors_def, SUBSET_DEF *)
val divisors_subset_upto = store_thm(
  "divisors_subset_upto",
  ``!n. divisors n SUBSET upto n``,
  rw[divisors_def, SUBSET_DEF]);

(* Theorem: 0 < n ==> (divisors n) SUBSET (natural n) *)
(* Proof:
   By SUBSET_DEF, this is to show:
      x IN (divisors n) ==> x IN (natural n)
   Since x IN (divisors n)
     ==> x <= n /\ x divides n    by divisors_element
     ==> x <= n /\ 0 < x          since n <> 0, so x <> 0 by ZERO_DIVIDES
     ==> x IN (natural n)         by natural_element
*)
val divisors_subset_natural = store_thm(
  "divisors_subset_natural",
  ``!n. 0 < n ==> (divisors n) SUBSET (natural n)``,
  rw[divisors_element, natural_element, SUBSET_DEF] >>
  metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO]);

(* Theorem: FINITE (divisors n) *)
(* Proof:
   Since (divisors n) SUBSET count (SUC n)   by divisors_subset_upto
     and FINITE (count (SUC n))              by FINITE_COUNT
      so FINITE (divisors n)                 by SUBSET_FINITE
*)
val divisors_finite = store_thm(
  "divisors_finite",
  ``!n. FINITE (divisors n)``,
  metis_tac[divisors_subset_upto, SUBSET_FINITE, FINITE_COUNT]);

(* Theorem: divisors 0 = {0} *)
(* Proof: divisors_def *)
val divisors_0 = store_thm(
  "divisors_0",
  ``divisors 0 = {0}``,
  rw[divisors_def]);

(* Theorem: divisors 1 = {1} *)
(* Proof: divisors_def *)
val divisors_1 = store_thm(
  "divisors_1",
  ``divisors 1 = {1}``,
  rw[divisors_def, EXTENSION]);

(* Theorem: 0 IN divisors n <=> (n = 0) *)
(* Proof:
       0 IN divisors n
   <=> 0 <= n /\ 0 divides n    by divisors_element
   <=> n = 0                    by ZERO_DIVIDES
*)
val divisors_has_0 = store_thm(
  "divisors_has_0",
  ``!n. 0 IN divisors n <=> (n = 0)``,
  rw[divisors_element]);

(* Theorem: 0 < n ==> BIJ (\d. n DIV d) (divisors n) (divisors n) *)
(* Proof:
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) d IN divisors n ==> n DIV d IN divisors n
       True by divisors_has_cofactor.
   (2) d IN divisors n /\ d' IN divisors n /\ n DIV d = n DIV d' ==> d = d'
       d IN divisors n ==> d divides n /\ 0 < d           by divisors_element, divisor_pos
       d' IN divisors n ==> d' divides n /\ 0 < d'        by divisors_element, divisor_pos
       Hence n = (n DIV d) * d  and n = (n DIV d') * d'   by DIVIDES_EQN
       giving   (n DIV d) * d = (n DIV d') * d'
       Now (n DIV d) <> 0, otherwise contradicts 0 < n    by MULT
       Hence                d = d'                        by EQ_MULT_LCANCEL
   (3) same as (1), true by divisors_has_cofactor.
   (4) x IN divisors n ==> ?d. d IN divisors n /\ (n DIV d = x)
       x IN divisors n ==> x divides n                    by divisors_element
       Let d = n DIV x.
       Then d IN divisors n                               by divisors_has_cofactor
       and  n DIV d = n DIV (n DIV x) = x                 by divide_by_cofactor
*)
val divisors_divisors_bij = store_thm(
  "divisors_divisors_bij",
  ``!n. 0 < n ==> BIJ (\d. n DIV d) (divisors n) (divisors n)``,
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >-
  rw[divisors_has_cofactor] >-
 (`n = (n DIV d) * d` by metis_tac[DIVIDES_EQN, divisors_element, divisor_pos] >>
  `n = (n DIV d') * d'` by metis_tac[DIVIDES_EQN, divisors_element, divisor_pos] >>
  `n DIV d <> 0` by metis_tac[MULT, NOT_ZERO_LT_ZERO] >>
  metis_tac[EQ_MULT_LCANCEL]) >-
  rw[divisors_has_cofactor] >>
  metis_tac[divisors_element, divisors_has_cofactor, divide_by_cofactor]);

(*
> divisors_divisors_bij;
val it = |- !n. 0 < n ==> (\d. n DIV d) PERMUTES divisors n: thm
*)

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

(* Theorem: 0 < n ==> (divisors n = IMAGE (gcd n) (natural n)) *)
(* Proof:
     divisors n
   = {d | d <= n /\ d divides n}                by divisors_def
   = {d | 0 < d /\ d <= n /\ d divides n}       by divisor_pos
   = {d | d IN (natural n) /\ d divides n}      by natural_element
   = {d | d IN (natural n) /\ (gcd d n = d)}    by divides_iff_gcd_fix
   = {d | d IN (natural n) /\ (gcd n d = d)}    by GCD_SYM
   = {gcd n d | d | d IN (natural n)}           by replacemnt
   = IMAGE (gcd n) (natural n)                  by IMAGE_DEF

   Or, by divisors_def, natuarl_elemnt, IN_IMAGE, this is to show:
   (1) 0 < n /\ x <= n /\ x divides n ==> ?x'. (x = gcd n x') /\ 0 < x' /\ x' <= n
       Note x divides n ==> 0 < x               by divisor_pos
       Also x divides n ==> gcd x n = x         by divides_iff_gcd_fix
         or                 gcd n x = x         by GCD_SYM
       Take this x, and the result follows.
   (2) 0 < n /\ 0 < x' /\ x' <= n ==> gcd n x' <= n /\ gcd n x' divides n
       Note gcd n x' divides n                  by GCD_IS_GREATEST_COMMON_DIVISOR
        and gcd n x' <= n                       by DIVIDES_LE, 0 < n.
*)
val divisors_eq_gcd_image = store_thm(
  "divisors_eq_gcd_image",
  ``!n. 0 < n ==> (divisors n = IMAGE (gcd n) (natural n))``,
  rw_tac std_ss[divisors_def, GSPECIFICATION, EXTENSION, IN_IMAGE, natural_element, EQ_IMP_THM] >-
  metis_tac[divisor_pos, divides_iff_gcd_fix, GCD_SYM] >-
  metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR, DIVIDES_LE] >>
  metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR]);

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
  rewrite_tac[feq_class_def, gcd_matches_def] >>
  rw[EXTENSION, GCD_SYM]);

(* Theorem: feq_class (gcd n) (natural n) = gcd_matches n *)
(* Proof: by FUN_EQ_THM, gcd_eq_equiv_class *)
val gcd_eq_equiv_class_fun = store_thm(
  "gcd_eq_equiv_class_fun",
  ``!n. feq_class (gcd n) (natural n) = gcd_matches n``,
  rw[FUN_EQ_THM, gcd_eq_equiv_class]);

(* Theorem: 0 < n ==> (partition (feq (gcd n)) (natural n) = IMAGE (gcd_matches n) (divisors n)) *)
(* Proof:
     partition (feq (gcd n)) (natural n)
   = IMAGE (equiv_class (feq (gcd n)) (natural n)) (natural n)    by partition_elements
   = IMAGE ((feq_class (gcd n) (natural n)) o (gcd n)) (natural n)  by feq_class_fun
   = IMAGE ((gcd_matches n) o (gcd n)) (natural n)       by gcd_eq_equiv_class_fun
   = IMAGE (gcd_matches n) (IMAGE (gcd n) (natural n))   by IMAGE_COMPOSE
   = IMAGE (gcd_matches n) (divisors n)      by divisors_eq_gcd_image, 0 < n
*)
val gcd_eq_partition_by_divisors = store_thm(
  "gcd_eq_partition_by_divisors",
  ``!n. 0 < n ==> (partition (feq (gcd n)) (natural n) = IMAGE (gcd_matches n) (divisors n))``,
  rpt strip_tac >>
  qabbrev_tac `f = gcd n` >>
  qabbrev_tac `s = natural n` >>
  `partition (feq f) s = IMAGE (equiv_class (feq f) s) s` by rw[partition_elements] >>
  `_ = IMAGE ((feq_class f s) o f) s` by rw[feq_class_fun] >>
  `_ = IMAGE ((gcd_matches n) o f) s` by rw[gcd_eq_equiv_class_fun, Abbr`f`, Abbr`s`] >>
  `_ = IMAGE (gcd_matches n) (IMAGE f s)` by rw[IMAGE_COMPOSE] >>
  `_ = IMAGE (gcd_matches n) (divisors n)` by rw[divisors_eq_gcd_image, Abbr`f`, Abbr`s`] >>
  rw[]);

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
   If n = 0,
      LHS = SIGMA f (natural 0)
          = SIGMA f {}             by natural_0
          = 0                      by SUM_IMAGE_EMPTY
      RHS = SIGMA (SIGMA f) (IMAGE (gcd_matches 0) (divisors 0))
          = SIGMA (SIGMA f) (IMAGE (gcd_matches 0) {0})   by divisors_0
          = SIGMA (SIGMA f) {gcd_matches 0 0}             by IMAGE_SING
          = SIGMA (SIGMA f) {{}}                          by gcd_matches_0
          = SIGMA f {}                                    by SUM_IMAGE_SING
          = 0 = LHS                                       by SUM_IMAGE_EMPTY
   Otherwise 0 < n,
     SIGMA f (natural n)
   = SIGMA (SIGMA f) (partition (feq (gcd n)) (natural n)) by sum_over_natural_by_gcd_partition
   = SIGMA (SIGMA f) (IMAGE (gcd_matches n) (divisors n))  by gcd_eq_partition_by_divisors, 0 < n
*)
val sum_over_natural_by_divisors = store_thm(
  "sum_over_natural_by_divisors",
  ``!f n. SIGMA f (natural n) = SIGMA (SIGMA f) (IMAGE (gcd_matches n) (divisors n))``,
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    `natural n = {}` by rw_tac std_ss[natural_0] >>
    `divisors n = {0}` by rw_tac std_ss[divisors_0] >>
    `IMAGE (gcd_matches n) (divisors n) = {{}}` by rw[gcd_matches_0] >>
    rw[SUM_IMAGE_SING],
    rw[sum_over_natural_by_gcd_partition, gcd_eq_partition_by_divisors]
  ]);

(* Theorem: 0 < n ==> INJ (gcd_matches n) (divisors n) univ(num) *)
(* Proof:
   By INJ_DEF, this is to show:
      x IN divisors n /\ y IN divisors n /\ gcd_matches n x = gcd_matches n y ==> x = y
   If n = 0,
      then divisors n = {}                by divisors_0
      hence trivially true.
   Otherwise 0 < n,
    Note x IN divisors n
     ==> x <= n /\ x divides n            by divisors_element
    also y IN divisors n
     ==> y <= n /\ y divides n            by divisors_element
   Hence (gcd x n = x) /\ (gcd y n = y)   by divides_iff_gcd_fix
   Since x divides n,  0 < x              by divisor_pos, 0 < n
   Giving x IN gcd_matches n x            by gcd_matches_element
       so x IN gcd_matches n y            by gcd_matches n x = gcd_matches n y
     with gcd x n = y                     by gcd_matches_element
   Therefore y = gcd x n = x.
*)
val gcd_matches_from_divisors_inj = store_thm(
  "gcd_matches_from_divisors_inj",
  ``!n. INJ (gcd_matches n) (divisors n) univ(:num -> bool)``,
  rw[INJ_DEF] >>
  Cases_on `n = 0` >>
  fs[divisors_0] >>
  `0 < n` by decide_tac >>
  `x <= n /\ x divides n /\ y <= n /\ y divides n` by metis_tac[divisors_element] >>
  `(gcd x n = x) /\ (gcd y n = y)` by rw[GSYM divides_iff_gcd_fix] >>
  metis_tac[divisor_pos, gcd_matches_element]);

(* Theorem: 0 < n ==> (CARD o (gcd_matches n) = CARD o (coprimes_by n)) *)
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

(* HERE; to fix! *)

(* Theorem: 0 < n ==> (CARD o (coprimes_by n) = \d. phi (if d IN (divisors n) then n DIV d else 0)) *)
(* Proof:
   By FUN_EQ_THM,
      CARD o (coprimes_by n) x
    = CARD (coprimes_by n x)       by composition, combinTheory.o_THM
    = CARD (if x divides n then coprimes (n DIV x) else {})    by coprimes_by_def, 0 < n
    If x divides n,
       x <= n                      by DIVIDES_LE
       so x IN (divisors n)        by divisors_element
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
val coprimes_by_with_card = store_thm(
  "coprimes_by_with_card",
  ``!n. 0 < n ==> (CARD o (coprimes_by n) = \d. phi (if d IN (divisors n) then n DIV d else 0))``,
  rw[coprimes_by_def, phi_def, divisors_def, FUN_EQ_THM] >>
  metis_tac[DIVIDES_LE, coprimes_0]);

(* Theorem: 0 < n ==> !x. x IN (divisors n) ==> ((CARD o (coprimes_by n)) x = (\d. phi (n DIV d)) x) *)
(* Proof:
   Since x IN (divisors n) ==> x divides n    by divisors_element
       CARD o (coprimes_by n) x
     = CARD (coprimes (n DIV x))   by coprimes_by_def
     = phi (n DIV x)               by phi_def
*)
val coprimes_by_divisors_card = store_thm(
  "coprimes_by_divisors_card",
  ``!n. 0 < n ==> !x. x IN (divisors n) ==> ((CARD o (coprimes_by n)) x = (\d. phi (n DIV d)) x)``,
  rw[coprimes_by_def, phi_def, divisors_def]);

(*
SUM_IMAGE_CONG |- (s1 = s2) /\ (!x. x IN s2 ==> (f1 x = f2 x)) ==> (SIGMA f1 s1 = SIGMA f2 s2)
*)

(* Theorem: n = SIGMA phi (divisors n) *)
(* Proof:
   If n = 0,
        SIGMA phi (divisors 0)
      = SIGMA phi {0}               by divisors_0
      = phi 0                       by SUM_IMAGE_SING
      = 0                           by phi_0
   If n <> 0, 0 < n.
   Note INJ (gcd_matches n) (divisors n) univ(:num -> bool)  by gcd_matches_from_divisors_inj
    and (\d. n DIV d) PERMUTES (divisors n)              by divisors_divisors_bij, 0 < n
   n = CARD (natural n)                                  by natural_card
     = SIGMA CARD (partition (feq (gcd n)) (natural n))  by partition_CARD
     = SIGMA CARD (IMAGE (gcd_matches n) (divisors n))   by gcd_eq_partition_by_divisors
     = SIGMA (CARD o (gcd_matches n)) (divisors n)       by sum_image_by_composition
     = SIGMA (CARD o (coprimes_by n)) (divisors n)       by gcd_matches_and_coprimes_by_same_size
     = SIGMA (\d. phi (n DIV d)) (divisors n)            by SUM_IMAGE_CONG, coprimes_by_divisors_card
     = SIGMA phi (divisors n)                            by sum_image_by_permutation
*)
val Gauss_little_thm = store_thm(
  "Gauss_little_thm",
  ``!n. n = SIGMA phi (divisors n)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[divisors_0, SUM_IMAGE_SING, phi_0] >>
  `0 < n` by decide_tac >>
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
  rw[]);

(* This is a milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Recursive definition of phi                                               *)
(* ------------------------------------------------------------------------- *)

(* Define phi by recursion *)
val rec_phi_def = tDefine "rec_phi" `
  rec_phi n = if n = 0 then 0
         else if n = 1 then 1
         else n - SIGMA rec_phi { m | m < n /\ m divides n}`
  (WF_REL_TAC `$< : num -> num -> bool` >> srw_tac[][]);
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
   Othewise,
      Let s = {m | m < n /\ m divides n}.
      Note s SUBSET (count n)       by SUBSET_DEF
      thus FINITE s                 by SUBSET_FINITE, FINITE_COUNT
     Hence !m. m IN s
       ==> (rec_phi m = phi m)      by induction hypothesis
      Also n NOTIN s                by EXTENSION
       and n INSERT s
         = {m | m <= n /\ m divides n}
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
val rec_phi_eq_phi = store_thm(
  "rec_phi_eq_phi",
  ``!n. rec_phi n = phi n``,
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
  (`n INSERT s = divisors n` by (rw[divisors_def, EXTENSION] >> metis_tac[LESS_OR_EQ, DIVIDES_REFL])) >>
  `n = SIGMA phi (divisors n)` by rw[Gauss_little_thm] >>
  `_ = phi n + SIGMA phi (s DELETE n)` by rw[GSYM SUM_IMAGE_THM] >>
  `_ = phi n + t` by metis_tac[DELETE_NON_ELEMENT] >>
  `rec_phi n = n - t` by metis_tac[rec_phi_def] >>
  decide_tac);


(* ------------------------------------------------------------------------- *)
(* Not Used                                                                  *)
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
val coprimes_from_notone_inj = store_thm(
  "coprimes_from_notone_inj",
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

(* Theorem: divisors n = IMAGE (gcd n) (upto n) *)
(* Proof:
     divisors n
   = {d | d <= n /\ d divides n}      by divisors_def
   = {d | d <= n /\ (gcd d n = d)}    by divides_iff_gcd_fix
   = {d | d <= n /\ (gcd n d = d)}    by GCD_SYM
   = {gcd n d | d | d <= n}           by replacemnt
   = IMAGE (gcd n) {d | d <= n}       by IMAGE_DEF
   = IMAGE (gcd n) (count (SUC n))    by count_def
   = IMAGE (gcd n) (upto n)           by notation

   By divisors_def, IN_IMAGE and EXTENSION, this is to show:
   (1) x <= n /\ x divides n ==> ?x'. (x = gcd n x') /\ x' < SUC n
       x <= n ==> x < SUC n           by LESS_EQ_IMP_LESS_SUC
       x divides n ==> x = gcd x n    by divides_iff_gcd_fix
                         = gcd n x    by GCD_SYM
   (2) x' < SUC n ==> gcd n x' <= n /\ gcd n x' divides n
       gcd n x' divides n             by GCD_IS_GREATEST_COMMON_DIVISOR
       If n = 0, x' < 1.
          That is, x' = 0             by arithmetic
           so gcd 0 0 = 0 <= 0        by GCD_0R
          and 0 divides 0             by ZERO_DIVIDES
       If n <> 0, 0 < n.
          gcd n x' divides n
          ==> gcd n x' <= n           by DIVIDES_LE
*)
val divisors_eq_image_gcd_upto = store_thm(
  "divisors_eq_image_gcd_upto",
  ``!n. divisors n = IMAGE (gcd n) (upto n)``,
  rw[divisors_def, EXTENSION, EQ_IMP_THM] >| [
    `x < SUC n` by decide_tac >>
    metis_tac[divides_iff_gcd_fix, GCD_SYM],
    Cases_on `n = 0` >| [
      `x' = 0` by decide_tac >>
      `gcd 0 0 = 0` by rw[GCD_0R] >>
      rw[],
      `0 < n` by decide_tac >>
      `(gcd n x') divides n` by rw[GCD_IS_GREATEST_COMMON_DIVISOR] >>
      rw[DIVIDES_LE]
    ],
    rw[GCD_IS_GREATEST_COMMON_DIVISOR]
  ]);

(* Theorem: (feq (gcd n)) equiv_on (upto n) *)
(* Proof:
   By feq_equiv |- !s f. feq f equiv_on s
   Taking s = upto n, f = gcd n.
*)
val gcd_eq_equiv_on_upto = store_thm(
  "gcd_eq_equiv_on_upto",
  ``!n. (feq (gcd n)) equiv_on (upto n)``,
  rw[feq_equiv]);

(* Theorem: partition (feq (gcd n)) (upto n) = IMAGE (preimage (gcd n) (upto n)) (divisors n) *)
(* Proof:
   Let f = gcd n, s = upto n.
     partition (feq f) s
   = IMAGE (preimage f s o f) s                      by feq_partition_by_preimage
   = IMAGE (preimage f s) (IMAGE f s)                by IMAGE_COMPOSE
   = IMAGE (preimage f s) (IMAGE (gcd n) (upto n))   by expansion
   = IMAGE (preimage f s) (divisors n)               by divisors_eq_image_gcd_upto
*)
val gcd_eq_upto_partition_by_divisors = store_thm(
  "gcd_eq_upto_partition_by_divisors",
  ``!n. partition (feq (gcd n)) (upto n) = IMAGE (preimage (gcd n) (upto n)) (divisors n)``,
  rpt strip_tac >>
  qabbrev_tac `f = gcd n` >>
  qabbrev_tac `s = upto n` >>
  `partition (feq f) s = IMAGE (preimage f s o f) s` by rw[feq_partition_by_preimage] >>
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

(* Theorem: SIGMA f (upto n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (upto n)) (divisors n)) *)
(* Proof:
     SIGMA f (upto n)
   = SIGMA (SIGMA f) (partition (feq (gcd n)) (upto n))                by sum_over_upto_by_gcd_partition
   = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (upto n)) (divisors n))  by gcd_eq_upto_partition_by_divisors
*)
val sum_over_upto_by_divisors = store_thm(
  "sum_over_upto_by_divisors",
  ``!f n. SIGMA f (upto n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (upto n)) (divisors n))``,
  rw[sum_over_upto_by_gcd_partition, gcd_eq_upto_partition_by_divisors]);

(* Similar results based on count *)

(* Theorem: 0 < n ==> (divisors n = IMAGE (gcd n) (count n)) *)
(* Proof:
     divisors n
   = IMAGE (gcd n) (upto n)                      by divisors_eq_image_gcd_upto
   = IMAGE (gcd n) (n INSERT (count n))          by upto_by_count
   = (gcd n n) INSERT (IMAGE (gcd n) (count n))  by IMAGE_INSERT
   = n INSERT (IMAGE (gcd n) (count n))          by GCD_REF
   = (gcd n 0) INSERT (IMAGE (gcd n) (count n))  by GCD_0R
   = IMAGE (gcd n) (0 INSERT (count n))          by IMAGE_INSERT
   = IMAGE (gcd n) (count n)                     by IN_COUNT, ABSORPTION, 0 < n.
*)
val divisors_eq_image_gcd_count = store_thm(
  "divisors_eq_image_gcd_count",
  ``!n. 0 < n ==> (divisors n = IMAGE (gcd n) (count n))``,
  rpt strip_tac >>
  `divisors n = IMAGE (gcd n) (upto n)` by rw[divisors_eq_image_gcd_upto] >>
  `_ = IMAGE (gcd n) (n INSERT (count n))` by rw[upto_by_count] >>
  `_ = n INSERT (IMAGE (gcd n) (count n))` by rw[GCD_REF] >>
  `_ = (gcd n 0) INSERT (IMAGE (gcd n) (count n))` by rw[GCD_0R] >>
  `_ = IMAGE (gcd n) (0 INSERT (count n))` by rw[] >>
  metis_tac[IN_COUNT, ABSORPTION]);

(* Theorem: (feq (gcd n)) equiv_on (count n) *)
(* Proof:
   By feq_equiv |- !s f. feq f equiv_on s
   Taking s = upto n, f = count n.
*)
val gcd_eq_equiv_on_count = store_thm(
  "gcd_eq_equiv_on_count",
  ``!n. (feq (gcd n)) equiv_on (count n)``,
  rw[feq_equiv]);

(* Theorem: 0 < n ==> (partition (feq (gcd n)) (count n) = IMAGE (preimage (gcd n) (count n)) (divisors n)) *)
(* Proof:
   Let f = gcd n, s = count n.
     partition (feq f) s
   = IMAGE (preimage f s o f) s                      by feq_partition_by_preimage
   = IMAGE (preimage f s) (IMAGE f s)                by IMAGE_COMPOSE
   = IMAGE (preimage f s) (IMAGE (gcd n) (count n))  by expansion
   = IMAGE (preimage f s) (divisors n)               by divisors_eq_image_gcd_count, 0 < n
*)
val gcd_eq_count_partition_by_divisors = store_thm(
  "gcd_eq_count_partition_by_divisors",
  ``!n. 0 < n ==> (partition (feq (gcd n)) (count n) = IMAGE (preimage (gcd n) (count n)) (divisors n))``,
  rpt strip_tac >>
  qabbrev_tac `f = gcd n` >>
  qabbrev_tac `s = count n` >>
  `partition (feq f) s = IMAGE (preimage f s o f) s` by rw[feq_partition_by_preimage] >>
  `_ = IMAGE (preimage f s) (IMAGE f s)` by rw[IMAGE_COMPOSE] >>
  rw[divisors_eq_image_gcd_count, Abbr`f`, Abbr`s`]);

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

(* Theorem: 0 < n ==> (SIGMA f (count n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (count n)) (divisors n))) *)
(* Proof:
     SIGMA f (count n)
   = SIGMA (SIGMA f) (partition (feq (gcd n)) (count n))                by sum_over_count_by_gcd_partition
   = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (count n)) (divisors n))  by gcd_eq_count_partition_by_divisors
*)
val sum_over_count_by_divisors = store_thm(
  "sum_over_count_by_divisors",
  ``!f n. 0 < n ==> (SIGMA f (count n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (count n)) (divisors n)))``,
  rw[sum_over_count_by_gcd_partition, gcd_eq_count_partition_by_divisors]);

(* Similar results based on natural *)

(* Theorem: 0 < n ==> (divisors n = IMAGE (gcd n) (natural n)) *)
(* Proof:
     divisors n
   = IMAGE (gcd n) (upto n)                      by divisors_eq_image_gcd_upto
   = IMAGE (gcd n) (0 INSERT natural n)          by upto_by_natural
   = (gcd 0 n) INSERT (IMAGE (gcd n) (natural n))  by IMAGE_INSERT
   = n INSERT (IMAGE (gcd n) (natural n))          by GCD_0L
   = (gcd n n) INSERT (IMAGE (gcd n) (natural n))  by GCD_REF
   = IMAGE (gcd n) (n INSERT (natural n))          by IMAGE_INSERT
   = IMAGE (gcd n) (natural n)                     by natural_has_last, ABSORPTION, 0 < n.
*)
val divisors_eq_image_gcd_natural = store_thm(
  "divisors_eq_image_gcd_natural",
  ``!n. 0 < n ==> (divisors n = IMAGE (gcd n) (natural n))``,
  rpt strip_tac >>
  `divisors n = IMAGE (gcd n) (upto n)` by rw[divisors_eq_image_gcd_upto] >>
  `_ = IMAGE (gcd n) (0 INSERT (natural n))` by rw[upto_by_natural] >>
  `_ = n INSERT (IMAGE (gcd n) (natural n))` by rw[GCD_0L] >>
  `_ = (gcd n n) INSERT (IMAGE (gcd n) (natural n))` by rw[GCD_REF] >>
  `_ = IMAGE (gcd n) (n INSERT (natural n))` by rw[] >>
  metis_tac[natural_has_last, ABSORPTION]);

(* Theorem: 0 < n ==> (partition (feq (gcd n)) (natural n) = IMAGE (preimage (gcd n) (natural n)) (divisors n)) *)
(* Proof:
   Let f = gcd n, s = natural n.
     partition (feq f) s
   = IMAGE (preimage f s o f) s                        by feq_partition_by_preimage
   = IMAGE (preimage f s) (IMAGE f s)                  by IMAGE_COMPOSE
   = IMAGE (preimage f s) (IMAGE (gcd n) (natural n))  by expansion
   = IMAGE (preimage f s) (divisors n)                 by divisors_eq_image_gcd_natural, 0 < n
*)
val gcd_eq_natural_partition_by_divisors = store_thm(
  "gcd_eq_natural_partition_by_divisors",
  ``!n. 0 < n ==> (partition (feq (gcd n)) (natural n) = IMAGE (preimage (gcd n) (natural n)) (divisors n))``,
  rpt strip_tac >>
  qabbrev_tac `f = gcd n` >>
  qabbrev_tac `s = natural n` >>
  `partition (feq f) s = IMAGE (preimage f s o f) s` by rw[feq_partition_by_preimage] >>
  `_ = IMAGE (preimage f s) (IMAGE f s)` by rw[IMAGE_COMPOSE] >>
  rw[divisors_eq_image_gcd_natural, Abbr`f`, Abbr`s`]);

(* Theorem: 0 < n ==> (SIGMA f (natural n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (natural n)) (divisors n))) *)
(* Proof:
     SIGMA f (natural n)
   = SIGMA (SIGMA f) (partition (feq (gcd n)) (natural n))                by sum_over_natural_by_gcd_partition
   = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (natural n)) (divisors n))  by gcd_eq_natural_partition_by_divisors
*)
val sum_over_natural_by_preimage_divisors = store_thm(
  "sum_over_natural_by_preimage_divisors",
  ``!f n. 0 < n ==> (SIGMA f (natural n) = SIGMA (SIGMA f) (IMAGE (preimage (gcd n) (natural n)) (divisors n)))``,
  rw[sum_over_natural_by_gcd_partition, gcd_eq_natural_partition_by_divisors]);

(* Theorem: (f 1 = g 1) /\ (!n. SIGMA f (divisors n) = SIGMA g (divisors n)) ==> (f = g) *)
(* Proof:
   By FUN_EQ_THM, this is to show: !x. f x = g x.
   By complete induction on x.
   Let s = divisors x, t = s DELETE x.
   Then x IN s                            by divisors_has_last
    and (s = x INSERT t) /\ x NOTIN t     by INSERT_DELETE, IN_DELETE
   Note FINITE s                          by divisors_finite
     so FINITE t                          by FINITE_DELETE

   Claim: SIGMA f t = SIGMA g t
   Proof: By SUM_IMAGE_CONG, this is to show:
             !z. z IN t ==> (f z = g z)
          But z IN s <=> z <= x /\ z divides x     by divisors_element
           so z IN t <=> z < x /\ z divides x      by IN_DELETE
          ==> f z = g z                            by induction hypothesis

   Now      SIGMA f s = SIGMA g s         by implication
   or f x + SIGMA f t = g x + SIGMA g t   by SUM_IMAGE_INSERT
   or             f x = g x               by SIGMA f t = SIGMA g t
*)
Theorem sum_image_divisors_cong:
  !f g. f 1 = g 1 /\ (!n. SIGMA f (divisors n) = SIGMA g (divisors n)) ==>
        f = g
Proof
  rw[FUN_EQ_THM] >>
  completeInduct_on `x` >>
  qabbrev_tac `s = divisors x` >>
  qabbrev_tac `t = s DELETE x` >>
  `x IN s` by rw[divisors_has_last, Abbr`s`] >>
  `(s = x INSERT t) /\ x NOTIN t` by rw[Abbr`t`] >>
  `SIGMA f t = SIGMA g t`
    by (irule SUM_IMAGE_CONG >> simp[] >>
        rw[divisors_element, Abbr`t`, Abbr`s`]) >>
  `FINITE t` by rw[divisors_finite, Abbr`t`, Abbr`s`] >>
  `SIGMA f s = f x + SIGMA f t` by simp[SUM_IMAGE_INSERT] >>
  `SIGMA g s = g x + SIGMA g t` by simp[SUM_IMAGE_INSERT] >>
  `SIGMA f s = SIGMA g s` by metis_tac[] >>
  decide_tac
QED
(* But this is not very useful! *)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
