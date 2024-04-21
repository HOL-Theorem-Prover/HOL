(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem - Binomial Proof.                                 *)
(* ------------------------------------------------------------------------- *)

(*

Fermat's Little Theorem (Binomial proof)
========================================
To prove:  a^p = a  (mod p)   for prime p
Proof:
   By induction on a.

   Base case: 0^p = 0 (mod p)
      true by arithmetic.
   Step case: k^p = k (mod p)  ==> (k+1)^p = (k+1) (mod p)
      (k+1)^p
    = SUM (GENLIST (\j. (binomial p j)* k**(p-j) * 1**j) (SUC p))    by binomial_thm
    = SUM (GENLIST (\j. (binomial p j)* k**(p-j)) (SUC p))           by arithmetic

   By prime_iff_divides_binomials,
      prime p <=> 1 < p /\ (!j. 0 < j /\ j < p ==> divides p (binomial p j));
   Therefore in mod p,
      (k+1)^p = k^p + 1^p    (mod p)   just first and last terms
              = k   + 1^p    (mod p)   by induction hypothesis
              = k + 1                  by arithmetic
*)

(*===========================================================================*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

open arithmeticTheory dividesTheory numberTheory combinatoricsTheory;

(* declare new theory at start *)
val _ = new_theory "FLTbinomial";

(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem by Binomial Documentation                         *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   From helpers:
   PRIME_FACTOR_PROPER |- !n. 1 < n /\ ~prime n ==> ?p. prime p /\ p < n /\ p divides n
   MULTIPLE_INTERVAL   |- !n m. n divides m ==>
                          !x. m - n < x /\ x < m + n /\ n divides x ==> x = m
   PROD_SET_EUCLID     |- !s. FINITE s ==>
                          !p. prime p /\ p divides PROD_SET s ==> ?b. b IN s /\ p divides b
   PRIME_BIG_NOT_DIVIDES_FACT
                       |- !p k. prime p /\ k < p ==> ~(p divides FACT k)
   FACT_EQ_PROD        |- !n. FACT n = PROD_SET (IMAGE SUC (count n))
   FACT_REDUCTION      |- !n m. m < n ==>
                               FACT n = PROD_SET (IMAGE SUC (count n DIFF count m)) * FACT m

   From binomial:
   prime_divides_binomials
                       |- !n. prime n ==> 1 < n /\
                              !k. 0 < k /\ k < n ==> n divides binomial n k
   prime_divisor_property
                       |- !n p. 1 < n /\ p < n /\ prime p /\ p divides n ==>
                              ~(p divides FACT (n - 1) DIV FACT (n - p))
   divides_binomials_imp_prime
                       |- !n. 1 < n /\
                             (!k. 0 < k /\ k < n ==> n divides binomial n k) ==> prime n
   prime_iff_divides_binomials
                       |- !n. prime n <=>
                              1 < n /\ !k. 0 < k /\ k < n ==> n divides binomial n k
   binomial_range_shift|- !n. 0 < n ==> ((!k. 0 < k /\ k < n ==> binomial n k MOD n = 0) <=>
                              !h. h < PRE n ==> binomial n (SUC h) MOD n = 0)
   binomial_mod_zero   |- !n. 0 < n ==> !k. binomial n k MOD n = 0 <=>
                              !x y. (binomial n k * x ** (n - k) * y ** k) MOD n = 0
   binomial_range_shift_alt
                       |- !n. 0 < n ==>
                             ((!k. 0 < k /\ k < n ==> !x y. (binomial n k * x ** (n - k) * y ** k) MOD n = 0) <=>
                              !h. h < PRE n ==> !x y. (binomial n (SUC h) * x ** (n - SUC h) * y ** SUC h) MOD n = 0)
   binomial_mod_zero_alt
                       |- !n. 0 < n ==> ((!k. 0 < k /\ k < n ==> binomial n k MOD n = 0) <=>
                          !x y. SUM (GENLIST ((\k. (binomial n k * x ** (n - k) * y ** k) MOD n) o SUC) (PRE n)) = 0)
   binomial_thm_prime  |- !p. prime p ==> !x y. (x + y) ** p MOD p = (x ** p + y ** p) MOD p

   Application:
   fermat_little_thm   |- !p a. prime p ==> a ** p MOD p = a MOD p
*)

(* Part 1: Basic ----------------------------------------------------------- *)

(* Part 2: General Theory -------------------------------------------------- *)

(* Part 3: Actual Proof ---------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem                                                   *)
(* ------------------------------------------------------------------------- *)

(* Idea: (Fermat's Little Theorem by Binomial)
         for prime p, a ** p = a (mod p). *)

(* Theorem: prime p ==> a ** p MOD p = a MOD p *)
(* Proof:
   Note 0 < p                               by PRIME_POS
   By induction on a.
   Base: 0 ** p MOD p = 0 MOD p, true       by ZERO_EXP, 0 < p
   Step: a ** p MOD p = a MOD p ==>
         (SUC a) ** p MOD p = (SUC a) MOD p

     (SUC a) ** p MOD p
   = (a + 1) ** p MOD p                     by ADD1
   = (a ** p + 1 ** p) MOD p                by binomial_thm_prime
   = (a ** p MOD p + 1 ** p MOD p) MOD p    by MOD_PLUS, 0 < p
   = (a MOD p + 1 ** p MOD p) MOD p         by induction hypothesis
   = (a MOD p + 1 MOD p) MOD p              by EXP_1
   = (a + 1) MOD p                          by MOD_PLUS, 0 < p
   = (SUC a) MOD p                          by ADD1
*)
Theorem fermat_little_thm:
  !p a. prime p ==> a ** p MOD p = a MOD p
Proof
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  `p <> 0` by decide_tac >>
  Induct_on `a` >-
  simp[ZERO_EXP] >>
  metis_tac[binomial_thm_prime, MOD_PLUS, EXP_1, ADD1]
QED

(* Part 4: End ------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
