(* ------------------------------------------------------------------------- *)
(* AKS Parameter.                                                            *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "computeParam";

(* ------------------------------------------------------------------------- *)

open jcLib;

open prim_recTheory pred_setTheory listTheory arithmeticTheory logrootTheory
     dividesTheory gcdTheory numberTheory combinatoricsTheory primeTheory;

(* Get dependent theories local *)
open computeOrderTheory;
open monoidTheory ringTheory;

val _ = temp_overload_on("SQ", ``\n. n * (n :num)``);
val _ = temp_overload_on("HALF", ``\n. n DIV 2``);
val _ = temp_overload_on("TWICE", ``\n. 2 * n``);

val _ = intLib.deprecate_int ();

(* ------------------------------------------------------------------------- *)
(* AKS Parameter Documentation                                               *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   param_search_result =
       nice num
     | good num
     | bad
*)
(* Definitions and Theorems (# are exported):

   Prime Candidates:
   prime_candidates_def         |- !n m. prime_candidates n m =
                        {k | prime k /\ ~(k divides n) /\ !j. 0 < j /\ j < m ==> ~(k divides (n ** j - 1))
   prime_candidates_element     |- !n m k. k IN prime_candidates n m <=>
                             prime k /\ ~(k divides n) /\ !j. 0 < j /\ j < m ==> ~(k divides (n ** j - 1))
   prime_candidates_property    |- !n m k. k IN prime_candidates n m ==> prime k /\ coprime k n /\ m <= ordz k n
   prime_candidates_not_empty   |- !n m. 1 < n /\ 0 < m ==> prime_candidates n m <> {}
   ZN_order_big_enough          |- !n m. 1 < n /\ 0 < m ==> ?k. prime k /\ coprime k n /\ m <= ordz k n

   Coprime Candidates:
   coprime_candidates_def       |- !n m. coprime_candidates n m =
                                   {k | coprime k n /\ !j. 0 < j /\ j < m ==> ~(k divides (n ** j - 1))}
   coprime_candidates_element   |- !n m k. k IN coprime_candidates n m <=>
                                        coprime k n /\ !j. 0 < j /\ j < m ==> ~(k divides n ** j - 1)
   coprime_candidates_property  |- !n m. 1 < n /\ 1 < m ==> !k. k IN coprime_candidates n m ==>
                                         coprime k n /\ m <= ordz k n
   coprime_candidates_not_empty |- !n m. 1 < n /\ 0 < m ==> coprime_candidates n m <> {}
   coprime_candidates_ne_0      |- !n m. 1 < n ==> 0 NOTIN coprime_candidates n m
   coprime_candidates_ne_1      |- !n m. 1 < m ==> 1 NOTIN coprime_candidates n m
   ZN_order_good_enough         |- !n m. 1 < n /\ 1 < m ==> ?k. 1 < k /\ coprime k n /\ m <= ordz k n

   Smallest Candidate
   least_prime_candidates_property    |- !n m. 1 < n /\ 0 < m ==> !h. prime h /\ coprime h n /\
                                               h < MIN_SET (prime_candidates n m) ==>
                                               ?j. 0 < j /\ j < m /\ h divides (n ** j - 1)
   least_coprime_candidates_property  |- !n m. 1 < n /\ 1 < m ==> !h. 1 < h /\ coprime h n /\
                                               h < MIN_SET (coprime_candidates n m) ==>
                                               ?j. 0 < j /\ j < m /\ h divides (n ** j - 1):

   Power Factors and Product:
   power_factors_def        |- !n m. power_factors n m = {n ** j - 1 | 0 < j /\ j < m}
   power_factors_element    |- !n m x. x IN power_factors n m <=> ?j. (x = n ** j - 1) /\ 0 < j /\ j < m
   power_factors_alt        |- !n m. power_factors n m = IMAGE (\k. n ** k - 1) (residue m)
   power_factors_finite     |- !n m. FINITE (power_factors n m)
   power_factors_nonempty   |- !n m. 1 < m ==> power_factors n m <> {}
   power_factors_sing       |- !m. 1 < m ==> (power_factors 1 m = {0})
   power_factors_element_nonzero  |- !n m. 1 < n ==> 0 NOTIN power_factors n m
   power_factors_image_suc  |- !n. 0 < n ==> !m. IMAGE SUC (power_factors n m) = IMAGE (\j. n ** j) (residue m)

   Product of Power Factors:
   product_factors_def       |- !n m. product_factors n m = PROD_SET (power_factors n m)
   product_factors_zero      |- !m. 1 < m ==> (product_factors 1 m = 0)
   proudct_factors_prime_divisor_property   |- !n p. 0 < n /\ prime p ==>
                                !m. p divides (product_factors n m) ==> ordz p n < m
   proudct_factors_coprime_divisor_property  |- !n p. 1 < p /\ coprime p n ==>
                                !m. ordz p n < m ==> p divides (product_factors n m)
   product_factors_divisors  |- !n m k. 1 < k /\ coprime k n /\ ordz k n < m ==> k divides (product_factors n m)
   product_factors_pos       |- !n m. 1 < n ==> 0 < product_factors n m
   product_factors_upper     |- !n m. 1 < n /\ 1 < m ==> product_factors n m < n ** (m ** 2 DIV 2)

   Non-dividing coprimes of Product of Power Factors:
   power_factors_coprime_nondivisor_def      |- !n m. power_factors_coprime_nondivisor n m =
                                                 {x | coprime x n /\ ~(x divides (product_factors n m))}
   power_factors_coprime_nondivisor_element  |- !n m x. x IN power_factors_coprime_nondivisor n m <=>
                                                        coprime x n /\ ~(x divides (product_factors n m))
   power_factors_coprime_nondivisor_property |- !n m. 1 < m ==>
                                                !x. x IN power_factors_coprime_nondivisor n m ==> 1 < x
   power_factors_coprime_nondivisor_nonempty |- !n m. 1 < n /\ 1 < m ==>
                                                      power_factors_coprime_nondivisor n m <> {}
   power_factors_coprime_nondivisor_order    |- !n m. 1 < m ==>
                                                !k. k IN power_factors_coprime_nondivisor n m ==> m <= ordz k n

   Common Multiples of Residue n:
   residue_common_multiple_def      |- !n. residue_common_multiple n =
                                           {m | 0 < m /\ !j. j IN residue n ==> j divides m}
   residue_common_multiple_element  |- !n m. m IN residue_common_multiple n <=>
                                             0 < m /\ !j. 1 < j /\ j < n ==> j divides m
   residue_common_multiple_nonempty |- !n. residue_common_multiple n <> {}
   residue_common_multiple_nonzero  |- !n. 0 NOTIN residue_common_multiple n
   residue_common_multiple_has_multiple  |- !n m. m IN residue_common_multiple n ==>
                                            !k. 0 < k ==> k * m IN residue_common_multiple n
   residue_common_multiple_has_sub  |- !n a b. b < a /\ a IN residue_common_multiple n /\
                                               b IN residue_common_multiple n ==>
                                               a - b IN residue_common_multiple n
   residue_common_multiple_element_1 |- !n m. 1 < n ==>
                              (m IN residue_common_multiple n <=> 0 < m /\ !j. 1 < j /\ j < n ==> j divides m)

   Least Common Multiple of Residue n:
   residue_lcm_def         |- !n. residue_lcm n = MIN_SET (residue_common_multiple n)
   residue_lcm_divides_common_multiple
                           |- !n m. m IN residue_common_multiple n ==> (residue_lcm n) divides m
   residue_lcm_property    |- !n c. (c = residue_lcm n) <=> c IN residue_common_multiple n /\
                                    !m. m IN residue_common_multiple n ==> c divides m
   residue_lcm_alt         |- !n. 1 < n ==> (residue_lcm n = list_lcm (leibniz_vertical (n - 2)))
   residue_lcm_eq_list_lcm |- !n. 1 < n ==> (residue_lcm n = list_lcm [1 .. (n - 1)])

   Bounds for Residue LCM:
   product_factors_lower        |- !n m k. 1 < n /\ 1 < m /\ 1 < k /\
                                    (!j. 1 < j /\ j < k ==> coprime j n /\ ordz j n < m) ==>
                                    residue_lcm k <= product_factors n m
   residue_lcm_upper            |- !n m k. 1 < n /\ 1 < m /\ 1 < k /\
                                    (!j. 1 < j /\ j < k ==> coprime j n /\ ordz j n < m) ==>
                                    residue_lcm k < n ** (m ** 2 DIV 2)
   residue_lcm_lower            |- !n. 1 < n ==> 2 ** (n - 2) <= residue_lcm n
   ZN_order_modulus_upper       |- !n m k. 1 < n /\ 1 < m /\ 1 < k /\
                                    (!j. 1 < j /\ j < k ==> coprime j n /\ ordz j n < m) ==>
                                    k < 2 + SUC (LOG2 n) * (m ** 2 DIV 2)
   ZN_order_modulus_exists      |- !n m. 1 < n /\ 1 < m ==> ?k. 1 < k /\ k < 2 + SUC (LOG2 n) * (m ** 2 DIV 2) /\
                                    (coprime k n ==> m <= ordz k n)
   ZN_order_modulus_exists_alt  |- !n m. 1 < n /\ 1 < m ==> ?k. 1 < k /\ k < 2 + SUC (LOG2 n) * (m ** 2 DIV 2) /\
                                    (gcd k n <> 1 \/ m <= ordz k n)
   ZN_order_modulus_when_prime  |- !n m k. 0 < n /\ prime k /\ m <= ordz k n ==> ~(k divides (product_factors n m))

   ZN bounds based on upper logarithm:
   ZN_order_modulus_upper_1         |- !n m k. 1 < n /\ 1 < m /\ 1 < k /\
                                       (!j. 1 < j /\ j < k ==> coprime j n /\ ordz j n < m) ==>
                                        k < 2 + ulog n * HALF (m ** 2)
   ZN_order_modulus_exists_1        |- !n m. 1 < n /\ 1 < m ==>
                                       ?k. 1 < k /\ k < 2 + ulog n * HALF (m ** 2) /\
                                           (gcd k n <> 1 \/ m <= ordz k n)
   ZN_order_modulus_upper_2         |- !n m k. 1 < n /\ 1 < m /\ 1 < k /\
                                       (!j. 1 < j /\ j < k ==> ~(j divides n) /\ ordz j n < m) ==>
                                        k < 2 + HALF (m ** 2) * ulog n
   ZN_order_modulus_exists_2        |- !n m. 1 < n /\ 1 < m ==>
                                       ?k. 1 < k /\ k < 2 + HALF (m ** 2) * ulog n /\
                                           (k divides n \/ m <= ordz k n)
   ZN_order_modulus_upper_3         |- !n m k c. 1 < n /\ 1 < m /\
                                       (!k. 1 < k /\ k <= c ==> ~(k divides n) /\ ordz k n < m) ==>
                                        c < 1 + HALF (m ** 2) * ulog n
   ZN_order_modulus_exists_3        |- !n m c. 1 < n /\ 1 < m /\ 1 + HALF (m ** 2) * ulog n <= c ==>
                                           ?k. 1 < k /\ k <= c /\ (k divides n \/ m <= ordz k n)
   ZN_order_modulus_exists_4        |- !n m c. 1 < n /\ 1 < m /\ (c = 1 + HALF (m ** 2) * ulog n) ==>
                                           ?k. 1 < k /\ k <= c /\ (k divides n \/ m <= ordz k n)
   ZN_order_condition_property      |- !n k. 1 < n /\ coprime k n /\
                                             TWICE (SUC (LOG2 n)) ** 2 <= ordz k n ==>
                                             TWICE (SQRT (phi k)) * SUC (LOG2 n) <= phi k
   ZN_order_condition_property_0    |- !n k. 1 < n /\ coprime k n ==>
                                       !h. 0 < h /\ h ** 2 <= ordz k n ==>
                                           SQRT (phi k) * h <= phi k
   ZN_order_condition_property_1    |- !n k. 1 < n /\ coprime k n /\
                                             SUC (LOG2 n) ** 2 <= ordz k n ==>
                                             SQRT (phi k) * SUC (LOG2 n) <= phi k
   ZN_order_condition_property_2    |- !n k. 1 < n /\ coprime k n /\
                                             ulog n ** 2 <= ordz k n ==>
                                             SQRT (phi k) * ulog n <= phi k
   ZN_order_condition_property_3    |- !n k. 1 < n /\ coprime k n /\
                                          TWICE (ulog n) ** 2 <= ordz k n ==>
                                          TWICE (SQRT (phi k)) * ulog n <= phi k

   AKS Parameter Search:
   aks_param_search_def  |- !n m k c. aks_param_search n m k c =
                                      if c < k then bad
                                      else if k divides n then nice k
                                      else if m <= k /\ m <= ordz_compute k n then good k
                                      else aks_param_search n m (k + 1) c
   aks_param_def         |- !n. aks_param n =
                                    if n <= 2 then nice n
                                    else aks_param_search n (SQ (ulog n)) 2 (1 + HALF (ulog n ** 5))
   aks_param_alt         |- !n. aks_param n =
                                    (let m = ulog n ;
                                         c = 1 + HALF (m ** 5)
                                      in if m <= 1 then nice n else aks_param_search n (SQ m) 2 c)
   aks_param_search_alt  |- !n m k c. aks_param_search n m k c =
                                      if c < k then bad
                                      else if k divides n then nice k
                                      else if m <= k /\ m <= ordz k n then good k
                                      else aks_param_search n m (k + 1) c
   aks_param_0           |- aks_param 0 = nice 0
   aks_param_1           |- aks_param 1 = nice 1
   aks_param_2           |- aks_param 2 = nice 2
   aks_param_search_bad      |- !n m k c. 0 < k /\ (aks_param_search n m k c = bad) ==>
                                !j. k <= j /\ j <= c ==> ~(j divides n) /\ ordz j n < m
   aks_param_search_not_bad  |- !n m k j c. k <= j /\ j <= c /\ (j divides n \/ m <= ordz j n) ==>
                                            (k = 0) \/ aks_param_search n m k c <> bad
   aks_param_search_success  |- !n m c. 1 < n /\ 1 < m /\ 1 + HALF (m ** 2) * ulog n <= c ==>
                                        aks_param_search n m 2 c <> bad
   aks_param_exists          |- !n. aks_param n <> bad

   aks_param_search_nice     |- !n m h c k. (aks_param_search n m h c = nice k) ==>
                                            h <= k /\ k divides n /\ !j. h <= j /\ j < k ==> ~(j divides n)
   aks_param_search_nice_le  |- !n m k c. 0 < n /\ (aks_param_search n m 2 c = nice k) ==> k <= n
   aks_param_search_nice_bound
                             |- !n m k c j. (aks_param_search n m k c = nice j) ==> j <= c
   aks_param_search_nice_factor
                             |- !n m k c j. (aks_param_search n m k c = nice j) ==> j divides n
   aks_param_search_nice_coprime_all
                             |- !n m k c. (aks_param_search n m 2 c = nice k) ==>
                                !j. 1 < j /\ j < k ==> coprime j n
   aks_param_search_good     |- !n m h c k. (aks_param_search n m h c = good k) ==>
                                            h <= k /\ m <= ordz k n /\ !j. h <= j /\ j <= k ==> ~(j divides n)
   aks_param_search_good_lt  |- !n m k c. 1 < n /\ (aks_param_search n m 2 c = good k) ==> k < n
   aks_param_search_good_bound
                             |- !n m k c j. (aks_param_search n m k c = good j) ==> j <= c
   aks_param_search_good_coprime_all
                             |- !n m k c. (aks_param_search n m 2 c = good k) ==>
                                   1 < k /\ m <= ordz k n /\ !j. 1 < j /\ j <= k ==> coprime j n
   aks_param_nice            |- !n k. 1 < n /\ (aks_param n = nice k) ==>
                                      1 < k /\ k divides n /\ !j. 1 < j /\ j < k ==> ~(j divides n)
   aks_param_nice_alt        |- !n k. (aks_param n = nice k) ==>
                                      (if n <= 1 then k = n else 1 < k) /\ k divides n /\
                                      !j. 1 < j /\ j < k ==> ~(j divides n)
   aks_param_nice_le         |- !n k. (aks_param n = nice k) ==> k <= n
   aks_param_nice_bound      |- !n k. 2 < n /\ (aks_param n = nice k) ==> k <= 1 + HALF (ulog n ** 5)
   aks_param_nice_coprime_all|- !n k. (aks_param n = nice k) ==> !j. 1 < j /\ j < k ==> coprime j n
   aks_param_nice_for_prime  |- !n k. 1 < n /\ (aks_param n = nice k) ==> (prime n <=> (k = n))
   aks_param_good            |- !n k. (aks_param n = good k) ==>
                                         1 < k /\ SQ (ulog n) <= ordz k n /\ !j. 1 < j /\ j <= k ==> ~(j divides n)
   aks_param_good_lt         |- !n k. (aks_param n = good k) ==> k < n
   aks_param_good_bound      |- !n k. (aks_param n = good k) ==> k <= 1 + HALF (ulog n ** 5)
   aks_param_good_coprime_all|- !n k. (aks_param n = good k) ==> !j. 1 < j /\ j <= k ==> coprime j n
   aks_param_good_range      |- !n k. (aks_param n = good k) ==> 1 < n /\ 1 < k /\ k < n
   aks_param_good_coprime_order
                             |- !n k. (aks_param n = good k) ==>
                                       1 < k /\ k < n /\ coprime k n /\ ulog n ** 2 <= ordz k n

   AKS parameter search simplified:
   param_seek_def      |- !n m k c. param_seek m c n k =
                                      if c <= k then bad
                                      else if n MOD k = 0 then nice k
                                      else if m <= ordz k n then good k
                                      else param_seek m c n (k + 1)
   param_def           |- !n. param n =
                              if n <= 2 then nice n
                              else param_seek (SQ (ulog n)) (2 + HALF (ulog n ** 5)) n 2
   param_alt           |- !n. param n =
                              (let m = ulog n ;
                                   c = 2 + HALF (m ** 5)
                                in if m <= 1 then nice n else param_seek (SQ m) c n 2)
   param_seek_thm      |- !m c n k. 0 < k /\ k <= c ==>
                                    (param_seek m c n k = aks_param_search n m k (c - 1))
   param_eqn           |- !n. param n = aks_param n
   param_0             |- param 0 = nice 0
   param_1             |- param 1 = nice 1
   param_2             |- param 2 = nice 2
   param_nice_bound    |- !n k. 2 < n /\ (param n = nice k) ==> k <= 1 + HALF (ulog n ** 5)
   param_good_bound    |- !n k. (param n = good k) ==> k <= 1 + HALF (ulog n ** 5)
   param_exists        |- !n. param n <> bad
   param_nice_for_prime|- !n k. 1 < n /\ (param n = nice k) ==> (prime n <=> (k = n))
   param_good_range    |- !n k. (param n = good k) ==> 1 < n /\ 1 < k /\ k < n
*)

(* ------------------------------------------------------------------------- *)
(* AKS Parameter                                                             *)
(* ------------------------------------------------------------------------- *)

(* The AKS parameter k:
   prime k /\ (2 * SUC (LOG2 n)) ** 2 <= ordz k n
*)

(* Problem: Given n and m, find the smallest k such that ordz k n > m *)

(* Theory:
   Note that n is supposed to be large, k is small, the max m is also small.
     ordz k n
   = exponent j such that n ** j = 1 (mod k)      by definition of order
   = exponent j such that k divides (n ** j - 1)  by definition of mod k
   So try k = 1, 2, 3, ... successively
      If coprime k n, then n is invertible in (ZN k)  ... otherwise n is composite.
      Being invertibe, j = ordz k n exists ... j divides phi(k) by Euler-Fermat
      That is 0 < j < phi(k), j can be found by iteration.
      If j <= m, reject: next k, else accept: k found.
*)

(* More Theory:
   When found, k divides (n ** j - 1)  with j > m = 8, say.
   Since k is the smallest, this means:
         k does not divide (n ** 1 - 1), otherwise j = 1, but 1 < 8.
    also k does not divide (n ** 2 - 1), otherwise j = 2, but 2 < 8.
    also ...
    also k does not divide (n ** m - 1), otherwise j = m, but m = 8.
   Taken all together, k does not divide P = PROD (0 < j <= m) (n ** j - 1)
   or k is the smallest value not a factor of P.
   Of course, being the smallest value, k must be prime.
*)

(* Still More Theory:
   When found, k divides (n ** j - 1)  with j > m.
   Say k = 13, the smallest value not a factor of P = PROD (0 < j <= m) (n ** j - 1)
   Since k is the smallest, this must be due to:
         1 divides P, otherwise k = 1, but actually k = 13.
         2 divides P, otherwise k = 2, but actually k = 13.
         ....
        12 divides P, otherwise k = 12, but actually k = 13.
        and we know 13 is the smallest value not dividing P.
   That means,
        LCM (1..k) divides P = PROD (0 < j <= m) (n ** j - 1)
   Since divisor LCM (1..k) increases with k,
     but dividend P is fixed by n and m,
   Hence a suitable k will eventually be found if searching starts from 1, 2, ...
*)

(* Examples:

Let n = 97, m = 8.

n^1 - 1 = (2^5)(3)
n^2 - 1 = (2^6)(3)(7^2)
n^3 - 1 = (2^5)(3^2)(3169)
n^4 - 1 = (2^7)(3)(5)(7^2)(941)
n^5 - 1 = (2^5)(3)(11)(31)(262321)
n^6 - 1 = (2^6)(3^2)(7^2)(67)(139)(3169)
n^7 - 1 = (2^5)(3)(43)(967)(20241187)
n^8 - 1 = (2^8)(3)(5)(7^2)(233)(941)(189977)

So pick k = 13, the smallest prime not appearing. order_13(97) = order_13(6) = 12 > 8.

Let n = 98, m = 8.

n^1 - 1 = (97)
n^2 - 1 = (3^2)(11)(97)
n^3 - 1 = (31)(97)(313)
n^4 - 1 = (3^2)(5)(11)(17)(97)(113)
n^5 - 1 = (41)(97)(241)(9431)
n^6 - 1 = (3^3)(11)(31)(97)(313)(3169)
n^7 - 1 = (97)(239)(1303)(2873879)
n^8 - 1 = (3^2)(5)(11)(17)(97)(113)(401)(230017)

The smallest prime not appearing is k = 2, but n = 98 has no order in (ZN 2).
Need to pick k = 13, smallest coprime not appearing. order_13(98) = order_13(7) = 12 > 8.
Need to pick k = 13, smallest prime not dividing 98 and not appearing. order_13(98) = order_13(7) = 12 > 8.
Both are the same due to prime_not_divides_coprime: |- !n p. prime p /\ ~(p divides n) ==> coprime p
*)

(* ------------------------------------------------------------------------- *)
(* Prime Candidates                                                          *)
(* ------------------------------------------------------------------------- *)

(* Define the set of candidate primes *)
val prime_candidates_def = Define `
  prime_candidates (n:num) (m:num) =
    {k | prime k /\ ~(k divides n) /\ !j. 0 < j /\ j < m ==> ~(k divides (n ** j - 1))}
`;

(* Theorem: k IN (prime_candidates n m) <=>
           prime k /\ ~(k divides n) /\ !j. 0 < j /\ j < m ==> ~(k divides (n ** j - 1)) *)
(* Proof: by prime_candidates_def *)
val prime_candidates_element = store_thm(
  "prime_candidates_element",
  ``!n m k. k IN (prime_candidates n m) <=>
           prime k /\ ~(k divides n) /\ !j. 0 < j /\ j < m ==> ~(k divides (n ** j - 1))``,
  rw[prime_candidates_def]);

(* Theorem: k IN prime_candidates n m ==> prime k /\ coprime k n /\ m <= ordz k n *)
(* Proof:
   Expand by prime_candidates_def, this is to show:
   (1) prime k /\ ~(k divides n) ==> coprime k n
       True by prime_not_divides_coprime.
   (2) prime k /\ ~(k divides n) /\
       !j. 0 < j /\ j <= m ==> ~(k divides (n ** j - 1)) ==> m <= ordz k n
   Let h = ordz k n. To show: m <= h.
   Note prime k /\ ~(k divides n) ==> coprime k n   by prime_not_divides_coprime
   By contradiction. Suppose h < m.
   Then prime k ==> 1 < k                           by ONE_LT_PRIME
    and 1 < k /\ coprime k n
    ==> 0 < h /\ (n ** h MOD k = 1)                 by ZN_coprime_order_alt, 1 < k, coprime k n
   Thus 0 < h /\ h < m /\ (n ** h - 1) MOD k = 0    by MOD_EQ_DIFF, 0 < k
   or   0 < h /\ h < m /\ k divides (n ** h - 1)    by DIVIDES_MOD_0, 0 < k
   This is a contradiction with the implication when j = h.
*)
val prime_candidates_property = store_thm(
  "prime_candidates_property",
  ``!n m k. k IN prime_candidates n m ==> prime k /\ coprime k n /\ m <= ordz k n``,
  rw[prime_candidates_def] >-
  rw[prime_not_divides_coprime] >>
  qabbrev_tac `h = ordz k n` >>
  spose_not_then strip_assume_tac >>
  `coprime k n` by rw[prime_not_divides_coprime] >>
  `1 < k` by rw[ONE_LT_PRIME] >>
  `0 < h /\ (n ** h MOD k = 1)` by rw[ZN_coprime_order_alt, Abbr`h`] >>
  `0 < k /\ h < m` by decide_tac >>
  metis_tac[MOD_EQ_DIFF, DIVIDES_MOD_0, ONE_MOD]);

(* Theorem: 1 < n /\ 0 < m ==> prime_candidates n m <> {} *)
(* Proof:
   Expand by prime_candidates_def, this is to show:
   ?x. prime x /\ ~(x divides n) /\ !j. j <= m /\ x divides (n ** j - 1) ==> (j = 0)
   Let z = n ** m.
       ?p. prime p /\ z < p           by prime_always_bigger
   Take x = p. Need to show:
   (1) prime p /\ z < p ==> ~(p divides n)
       Since n <= z                   by X_LE_X_EXP, 0 < m
       n < p, or ~(p <= n)
       Hence ~(p divides n)           by DIVIDES_LE
   (2) p divides (n ** j - 1) ==> j = 0
       Note 0 < n ** j                by EXP_POS, 0 < n
            n ** j < z                by EXP_BASE_LT_MONO, 1 < n
         so n ** j - 1 < z
        and n ** j - 1 < p
       which means: ~(p <= n ** j - 1)
      Given p divides (n ** j - 1),
      this forces ~(0 < n ** j - 1)   by DIVIDES_LE
         or n ** j = 1
      Therefore j = 0                 by EXP_EQ_1, n <> 1
*)
val prime_candidates_not_empty = store_thm(
  "prime_candidates_not_empty",
  ``!n m. 1 < n /\ 0 < m ==> prime_candidates n m <> {}``,
  rw[prime_candidates_def, EXTENSION] >>
  `?x. prime x /\ ~(x divides n) /\ !j. j < m /\ x divides (n ** j - 1) ==> (j = 0)` suffices_by metis_tac[] >>
  qabbrev_tac `z = n ** m` >>
  `?p. prime p /\ z < p` by rw[prime_always_bigger] >>
  qexists_tac `p` >>
  `0 < n /\ n <> 1` by decide_tac >>
  rw[] >| [
    `n <= z` by rw[X_LE_X_EXP, Abbr`z`] >>
    `~(p <= n)` by decide_tac >>
    metis_tac[DIVIDES_LE],
    `0 < n ** j` by rw[EXP_POS] >>
    `n ** j < z` by rw[EXP_BASE_LT_MONO, Abbr`z`] >>
    `~(p <= n ** j - 1)` by decide_tac >>
    `~(0 < n ** j - 1)` by metis_tac[DIVIDES_LE] >>
    `n ** j = 1` by decide_tac >>
    metis_tac[EXP_EQ_1]
  ]);

(* Theorem: 1 < n /\ 0 < m ==> ?k. prime k /\ coprime k n /\ m <= ordz k n *)
(* Proof:
   Let s = prime_candidates n m
   With 1 < n /\ 0 < m, s <> {}     by prime_candidates_not_empty
     so MIN_SET s IN s              by MIN_SET_LEM
   Hence true with k = MIN_SET s    by prime_candidates_property
*)
val ZN_order_big_enough = store_thm(
  "ZN_order_big_enough",
  ``!n m. 1 < n /\ 0 < m ==> ?k. prime k /\ coprime k n /\ m <= ordz k n``,
  rpt strip_tac >>
  qabbrev_tac `s = prime_candidates n m` >>
  `s <> {}` by rw[prime_candidates_not_empty, Abbr`s`] >>
  `MIN_SET s IN s` by rw[MIN_SET_LEM] >>
  qexists_tac `MIN_SET s` >>
  metis_tac[prime_candidates_property]);

(* ------------------------------------------------------------------------- *)
(* Coprime Candidates                                                        *)
(* ------------------------------------------------------------------------- *)

(* Define the set of candidate coprimes *)
val coprime_candidates_def = Define `
  coprime_candidates (n:num) (m:num) =
    {k | coprime k n /\ !j. 0 < j /\ j < m ==> ~(k divides (n ** j - 1))}
`;

(* Theorem: k IN (coprime_candidates n m) <=> coprime k n /\ !j. 0 < j /\ j < m ==> ~(k divides (n ** j - 1)) *)
(* Proof: by coprime_candidates_def *)
val coprime_candidates_element = store_thm(
  "coprime_candidates_element",
  ``!n m k. k IN (coprime_candidates n m) <=> coprime k n /\ !j. 0 < j /\ j < m ==> ~(k divides (n ** j - 1))``,
  rw[coprime_candidates_def]);

(* Theorem: 1 < n /\ 1 < m ==>
   !k. k IN coprime_candidates n m ==> coprime k n /\ m <= ordz k n *)
(* Proof:
   Let h = ordz k n. By coprime_candidates_def, this is to show m <= h.
   By contradiction, suppose h < m.
   Note k <> 0                         by coprime_0L, n <> 1.
   Since 0 < 1 /\ 1 < m, ~k divides (n ** m - 1)    by implication
      so k <> 1                        by ONE_DIVIDES_ALL
   Hence 0 < k /\ 1 < k
   Now, 1 < k /\ coprime k n
   gives 0 < h /\ (n ** h MOD k = 1)   by ZN_coprime_order_alt
      or (n ** h - 1) MOD k = 0        by MOD_EQ_DIFF, k <> 0.
   meaning k divides (n ** h - 1)      by DIVIDES_MOD_0
   which contradicts the implication when j = h.
*)
val coprime_candidates_property = store_thm(
  "coprime_candidates_property",
  ``!n m. 1 < n /\ 1 < m ==>
   !k. k IN coprime_candidates n m ==> coprime k n /\ m <= ordz k n``,
  rw[coprime_candidates_def] >>
  qabbrev_tac `h = ordz k n` >>
  spose_not_then strip_assume_tac >>
  `n <> 1 /\ h < m /\ 0 < 1` by decide_tac >>
  `k <> 0` by metis_tac[coprime_0L] >>
  `k <> 1` by metis_tac[ONE_DIVIDES_ALL] >>
  `0 < k /\ 1 < k` by decide_tac >>
  `0 < h /\ (n ** h MOD k = 1)` by rw[ZN_coprime_order_alt, Abbr`h`] >>
  `(n ** h - 1) MOD k = 0` by rw[MOD_EQ_DIFF] >>
  metis_tac[DIVIDES_MOD_0]);

(* Theorem: 1 < n /\ 1 < m ==> coprime_candidates n m <> {} *)
(* Proof:
   By coprime_candidates_def, this is to show:
      ?x. coprime x n /\ !j. j < m /\ x divides (n ** j - 1) ==> (j = 0)
   Let z = n ** m.
       ?p. prime p /\ z < p           by prime_always_bigger
   Take x = p. Need to show:
   (1) prime p /\ z < p ==> coprime p n
       Since n <= z                   by X_LE_X_EXP, 0 < m
          so n < p
       Hence coprime p n              by prime_iff_coprime_all_lt
   (2) p divides (n ** j - 1) ==> j = 0
       Note 0 < n ** j                by EXP_POS, 0 < n
            n ** j < z                by EXP_BASE_LT_MONO, 1 < n
         so n ** j - 1 < z
        and n ** j - 1 < p
       which means: ~(p <= n ** j - 1)
      Given p divides (n ** j - 1),
      this forces ~(0 < n ** j - 1)   by DIVIDES_LE
         or n ** j = 1
      Therefore j = 0                 by EXP_EQ_1, n <> 1
*)
val coprime_candidates_not_empty = store_thm(
  "coprime_candidates_not_empty",
  ``!n m. 1 < n /\ 0 < m ==> coprime_candidates n m <> {}``,
  rw[coprime_candidates_def, EXTENSION] >>
  `?x. coprime x n /\ !j. j < m /\ x divides (n ** j - 1) ==> (j = 0)` suffices_by metis_tac[] >>
  qabbrev_tac `z = n ** m` >>
  `?p. prime p /\ z < p` by rw[prime_always_bigger] >>
  qexists_tac `p` >>
  `0 < n /\ n <> 1` by decide_tac >>
  rw[] >| [
    `n <= z` by rw[X_LE_X_EXP, Abbr`z`] >>
    `n < p` by decide_tac >>
    metis_tac[prime_iff_coprime_all_lt],
    `0 < n ** j` by rw[EXP_POS] >>
    `n ** j < z` by rw[EXP_BASE_LT_MONO, Abbr`z`] >>
    `~(p <= n ** j - 1)` by decide_tac >>
    `~(0 < n ** j - 1)` by metis_tac[DIVIDES_LE] >>
    `n ** j = 1` by decide_tac >>
    metis_tac[EXP_EQ_1]
  ]);

(* Theorem: 1 < n /\ 1 < m ==> 0 NOTIN coprime_candidates n m *)
(* Proof:
   By contradiction, suppose 0 IN coprime_candidates n m.
   Then coprime 0 n     by coprime_candidates_element
   But  gcd 0 n = n     by GCD_0L
   and  1 < n means n <> 1, so this is a contradiction.
*)
val coprime_candidates_ne_0 = store_thm(
  "coprime_candidates_ne_0",
  ``!n m. 1 < n ==> 0 NOTIN coprime_candidates n m``,
  spose_not_then strip_assume_tac >>
  `n <> 1` by decide_tac >>
  metis_tac[coprime_candidates_element, GCD_0L]);

(* Theorem: 1 < m ==> 1 NOTIN coprime_candidates n m *)
(* Proof:
   By contradiction, suppose 1 IN coprime_candidates n m.
   Then coprime 1 n is true   by GCD_1
   But Take j = 1, as 0 < 1 and 1 < m.
   and 1 divides (n ** j - 1)   by ONE_DIVIDES_ALL
   This is a contradiction.
*)
val coprime_candidates_ne_1 = store_thm(
  "coprime_candidates_ne_1",
  ``!n m. 1 < m ==> 1 NOTIN coprime_candidates n m``,
  metis_tac[coprime_candidates_element, ONE_DIVIDES_ALL, DECIDE``0 < 1``]);

(* Theorem: 1 < n /\ 1 < m ==> ?k. 1 < k /\ coprime k n /\ m <= ordz k n *)
(* Proof:
   Note 1 < m ==> 0 < m             by arithmetic
   Let s = coprime_candidates n m
   With 1 < n /\ 0 < m, s <> {}     by coprime_candidates_not_empty
     so MIN_SET s IN s              by MIN_SET_LEM
    and MIN_SET s <> 0              by coprime_candidates_ne_0, 1 < n
    and MIN_SET s <> 1              by coprime_candidates_ne_1, 1 < m
     so 1 < MIN_SET s               by arithmetic
   Hence true with k = MIN_SET s    by coprime_candidates_property, 1 < n, 1 < m
*)
val ZN_order_good_enough = store_thm(
  "ZN_order_good_enough",
  ``!n m. 1 < n /\ 1 < m ==> ?k. 1 < k /\ coprime k n /\ m <= ordz k n``,
  rpt strip_tac >>
  qabbrev_tac `s = coprime_candidates n m` >>
  `s <> {}` by rw[coprime_candidates_not_empty, Abbr`s`] >>
  `MIN_SET s IN s` by rw[MIN_SET_LEM] >>
  `MIN_SET s <> 0` by metis_tac[coprime_candidates_ne_0] >>
  `MIN_SET s <> 1` by metis_tac[coprime_candidates_ne_1] >>
  `1 < MIN_SET s` by decide_tac >>
  metis_tac[coprime_candidates_property]);

(* ------------------------------------------------------------------------- *)
(* Smallest Candidate                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: prime h /\ coprime h n /\ h < MIN_SET (prime_candidates n m) ==>
            ?j. 0 < j /\ j < m /\ h divides (n ** j - 1) *)
(* Proof:
   By contradiction, assume !j. 0 < j /\ j < m ==> ~(h divides (n ** j - 1)).
   Let k = MIN_SET (prime_candidates n m).
   Since MIN_SET (prime_candidates n m) <> {}         by prime_candidates_not_empty
         k IN (prime_candidates n m) and
         !x. x IN (prime_candidates n m) ==> k <= x   by MIN_SET_LEM
   But 1 < h                                          by ONE_LT_PRIME
   and coprime h n ==> ~(h divides n)                 by coprime_not_divides
   Hence h IN (prime_candidates n m)                  by prime_candidates_def
   The implication gives k <= h, which contradicts h < k.
*)
val least_prime_candidates_property = store_thm(
  "least_prime_candidates_property",
  ``!n m.  1 < n /\ 0 < m ==>
   !h. prime h /\ coprime h n /\ h < MIN_SET (prime_candidates n m) ==>
    ?j. 0 < j /\ j < m /\ h divides (n ** j - 1)``,
  rpt strip_tac >>
  qabbrev_tac `k = MIN_SET (prime_candidates n m)` >>
  `k IN (prime_candidates n m) /\ !x. x IN (prime_candidates n m) ==> k <= x` by rw[MIN_SET_LEM, prime_candidates_not_empty, Abbr`k`] >>
  `prime k /\ coprime k n /\ m <= ordz k n` by metis_tac[prime_candidates_property] >>
  spose_not_then strip_assume_tac >>
  `1 < h` by rw[ONE_LT_PRIME] >>
  `~(h divides n)` by rw[coprime_not_divides] >>
  `h IN (prime_candidates n m)` by rw[prime_candidates_def] >>
  `k <= h` by metis_tac[] >>
  decide_tac);

(* Theorem: 1 < h /\ coprime h n /\ h < MIN_SET (coprime_candidates n m) ==>
            ?j. 0 < j /\ j < m /\ h divides (n ** j - 1) *)
(* Proof:
   By contradiction, assume !j. 0 < j /\ j < m ==> ~(h divides (n ** j - 1)).
   Let k = MIN_SET (coprime_candidates n m).
   Since MIN_SET (coprime_candidates n m) <> {}         by coprime_candidates_not_empty
         k IN (coprime_candidates n m) and
         !x. x IN (coprime_candidates n m) ==> k <= x   by MIN_SET_LEM
   But 1 < h                                            by ONE_LT_PRIME
   and coprime h n ==> ~(h divides n)                   by coprime_not_divides
   Hence h IN (coprime_candidates n m)                  by coprime_candidates_def
   The implication gives k <= h, which contradicts h < k.
*)
val least_coprime_candidates_property = store_thm(
  "least_coprime_candidates_property",
  ``!n m.  1 < n /\ 1 < m ==>
   !h. 1 < h /\ coprime h n /\ h < MIN_SET (coprime_candidates n m) ==>
    ?j. 0 < j /\ j < m /\ h divides (n ** j - 1)``,
  rpt strip_tac >>
  qabbrev_tac `k = MIN_SET (coprime_candidates n m)` >>
  `0 < m` by decide_tac >>
  `k IN (coprime_candidates n m) /\ !x. x IN (coprime_candidates n m) ==> k <= x` by rw[MIN_SET_LEM, coprime_candidates_not_empty, Abbr`k`] >>
  `coprime k n /\ m <= ordz k n` by metis_tac[coprime_candidates_property] >>
  spose_not_then strip_assume_tac >>
  `~(h divides n)` by rw[coprime_not_divides] >>
  `h IN (coprime_candidates n m)` by rw[coprime_candidates_def] >>
  `k <= h` by metis_tac[] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Power Factors and Product                                                 *)
(* ------------------------------------------------------------------------- *)

(* Define set of factors *)
val power_factors_def = Define`
  power_factors n m = {n ** j - 1 | j | 0 < j /\ j < m}
`;

(* Theorem: x IN power_factors n m <=> ?j. (x = n ** j - 1) /\ 0 < j /\ j < m *)
(* Proof: by power_factors_def. *)
val power_factors_element = store_thm(
  "power_factors_element",
  ``!n m x. x IN power_factors n m <=> ?j. (x = n ** j - 1) /\ 0 < j /\ j < m``,
  rw[power_factors_def]);

(* Theorem: power_factors n m = IMAGE (\k. n ** k - 1) (residue m) *)
(* Proof:
   By power_factors_def and residue_def, this is to show:
   {n ** j - 1 | 0 < j /\ j < m} = IMAGE (\k. n ** k - 1) {i | 0 < i /\ i < m}
   which is true by IMAGE_DEF.
*)
val power_factors_alt = store_thm(
  "power_factors_alt",
  ``!n m. power_factors n m = IMAGE (\k. n ** k - 1) (residue m)``,
  rw[power_factors_def, residue_def, IMAGE_DEF]);

(* Theorem: FINITE (power_factors n m) *)
(* Proof:
   Since power_factors n m
       = IMAGE (\k. n ** k - 1) (residue m)   by power_factors_alt
     and FINITE (residue m)                   by residue_finite
   Hence FINITE (power_factors n m)           by IMAGE_FINITE
*)
val power_factors_finite = store_thm(
  "power_factors_finite",
  ``!n m. FINITE (power_factors n m)``,
  rw[power_factors_alt, residue_finite, IMAGE_FINITE]);

(* Theorem: 1 < m ==> (power_factors n m) <> {} *)
(* Proof:
   By power_factors_alt, this is to show: 1 < m ==> residue m <> {}
   This is true by residue_nonempty.
*)
val power_factors_nonempty = store_thm(
  "power_factors_nonempty",
  ``!n m. 1 < m ==> (power_factors n m) <> {}``,
  rw[power_factors_alt] >>
  rw[residue_nonempty]);

(* Theorem: 1 < m ==> (power_factors 1 m = {0}) *)
(* Proof:
   By power_factors_def and residue_def, this is to show: 1 < m ==> ?j. 0 < j /\ j < m
   Take j = 1, this is true.
*)
val power_factors_sing = store_thm(
  "power_factors_sing",
  ``!m. 1 < m ==> (power_factors 1 m = {0})``,
  rw[power_factors_def, residue_def, EXTENSION, SPECIFICATION, EQ_IMP_THM] >>
  metis_tac[DECIDE ``0 < 1``]);

(* Theorem: 1 < n ==> 0 NOTIN power_factors n m *)
(* Proof:
   By power_factors_def, this is to show: ~(n ** j <= 1) \/ (j = 0) \/ ~(j < m)
   By contradiction, this is to show: 1 < n /\ j <> 0 /\ j < m /\ n * j <= 1 ==> F
   Note 0 < m             by j <> /\ j < m
   Since 1 < n ** j       by ONE_LT_EXP, 1 < n, 0 < m
   This contradicts n * j <= 1.
*)
val power_factors_element_nonzero = store_thm(
  "power_factors_element_nonzero",
  ``!n m. 1 < n ==> 0 NOTIN power_factors n m``,
  rw[power_factors_def] >>
  spose_not_then strip_assume_tac >>
  `1 < n ** j` by rw[ONE_LT_EXP] >>
  decide_tac);

(* Theorem: 0 < n ==> !m. IMAGE SUC (power_factors n m) = IMAGE (\j. n ** j) (residue m) *)
(* Proof:
   Expanding by definitions, this is to show:
   (1) k <> 0 /\ k < m ==> ?j. (SUC (n ** k - 1) = n ** j) /\ j < m /\ j <> 0
       Take j = k, to show: SUC (n ** k - 1) = n ** k
       Since 0 < n ** k      by EXP_POS, 0 < n
         SUC (n ** k - 1)
       = SUC (PRE (n ** k))  by PRE_SUB1
       = n ** k              by SUC_PRE, 0 < n ** k
   (2) j < m /\ j <> 0 ==> ?x'. (n ** j = SUC x') /\ ?k. (x' = n ** k - 1) /\ k < m /\ k <> 0
       Take x' = PRE (n ** j)
       Since 0 < n ** j                   by EXP_POS, 0 < n
          so n ** j = SUC (PRE (n ** j))  by SUC_PRE
       Take k = j, to show: PRE (n ** j) = n ** j - 1
          which is true                   by PRE_SUB1
*)
val power_factors_image_suc = store_thm(
  "power_factors_image_suc",
  ``!n. 0 < n ==> !m. IMAGE SUC (power_factors n m) = IMAGE (\j. n ** j) (residue m)``,
  rw[power_factors_alt, residue_def, IMAGE_DEF, EXTENSION, EQ_IMP_THM] >| [
    qexists_tac `k` >>
    rw[] >>
    `0 < n ** k` by rw[] >>
    metis_tac[PRE_SUB1, PRE_SUC_EQ],
    qexists_tac `PRE (n ** j)` >>
    `0 < n ** j` by rw[] >>
    rw[GSYM SUC_PRE] >>
    qexists_tac `j` >>
    rw[PRE_SUB1]
  ]);

(* ------------------------------------------------------------------------- *)
(* Product of Power Factors                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define product of factors *)
val product_factors_def = Define`
  product_factors n m = PROD_SET (power_factors n m)
`;

(* Theorem: 1 < m ==> (product_factors 1 m = 0) *)
(* Proof:
   Since power_factors 1 m = {0}
     product_factors 1 m
   = PROD_SET (power_factors 1 m)  by product_factors_def
   = PROD_SET {0}                  by power_factors_sing
   = 0                             by PROD_SET_SING
*)
val product_factors_zero = store_thm(
  "product_factors_zero",
  ``!m. 1 < m ==> (product_factors 1 m = 0)``,
  rw[product_factors_def, power_factors_sing, PROD_SET_SING]);

(* Theorem: 0 < n /\ prime p ==> !m. p divides (product_factors n m) ==> (ordz p n) < m *)
(* Proof:
   Let s = power_factors n m
    Then FINITE (power_factors n m)               by power_factors_finite
      so ?b. b IN s /\ p divides b                by PROD_SET_EUCLID
      or ?j. (b = n ** j - 1) /\ 0 < j /\ j < m   by power_factors_element
    Now  p divides b means b MOD p = 0            by DIVIDES_MOD_0, 0 < p
     or  (n ** j - 1) MOD p = 0                   by b = n ** j - 1
     so  n ** j MOD p = 1                         by MOD_EQ, ONE_MOD
    Since  Ring (ZN p)                            by ZN_ring, 0 < p
       ==> Monoid (ZN p).prod                     by ring_mult_monoid
      Let  x = n MOD p, x IN (ZN p).carrier       by MOD_LESS, ZN_property
      and  ordz p n = ordz p x                    by ZN_order_mod, 0 < p
    Hence  (ordz p x) j divides                   by monoid_order_condition
       or  (ordz p n) <= j                        by DIVIDES_LE
       or  (ordz p n) < m                         by j < m
*)
val proudct_factors_prime_divisor_property = store_thm(
  "proudct_factors_prime_divisor_property",
  ``!n p. 0 < n /\ prime p ==> !m. p divides (product_factors n m) ==> (ordz p n) < m``,
  rw[product_factors_def] >>
  qabbrev_tac `s = power_factors n m` >>
  `FINITE s` by rw[power_factors_finite, Abbr`s`] >>
  `?b. b IN s /\ p divides b` by rw[PROD_SET_EUCLID] >>
  `?j. (b = n ** j - 1) /\ 0 < j /\ j < m` by metis_tac[power_factors_element] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `0 < p` by decide_tac >>
  `(n ** j - 1) MOD p = 0` by rw[GSYM DIVIDES_MOD_0] >>
  `0 < n ** j` by rw[EXP_POS] >>
  `1 <= n ** j` by decide_tac >>
  `n ** j MOD p = 1` by metis_tac[MOD_EQ, ONE_MOD] >>
  qabbrev_tac `x = n MOD p` >>
  `x < p` by rw[MOD_LESS, Abbr`x`] >>
  `x ** j MOD p = 1` by rw[Abbr`x`] >>
  `ordz p n = ordz p x` by rw_tac std_ss[ZN_order_mod, Abbr`x`] >>
  `Ring (ZN p)` by rw[ZN_ring] >>
  `Monoid (ZN p).prod /\ x IN (ZN p).prod.carrier` by rw[ZN_property, ring_mult_monoid] >>
  `p <> 1` by decide_tac >>
  `(ZN p).prod.id = 1` by rw[ZN_property] >>
  `(ordz p x) divides j` by metis_tac[monoid_order_condition, ZN_exp] >>
  `ordz p n <= j` by metis_tac[DIVIDES_LE] >>
  decide_tac);

(* Theorem: 1 < p /\ coprime p n ==> !m. (ordz p n) < m ==> p divides (product_factors n m) *)
(* Proof:
   Let s = power_factors n m
    Then FINITE s                        by power_factors_finite
   Let j = ordz p n
   Then 0 < j /\ (n ** j MOD p = 1)      by ZN_coprime_order_alt, 1 < p, coprime p n
     or (n ** j - 1) MOD p = 0           by MOD_EQ_DIFF, ONE_MOD, need 0 < p
    Let b = n ** j - 1, then b IN s      by power_factors_element, need j < m
    and p divides b                      by DIVIDES_MOD_0
   Hence  PROD_SET s
        = PROD_SET (b INSERT s)          by ABSORPTION
        = b * PROD_SET (s DELETE b)      by PROD_SET_THM, need FINITE s
        = PROD_SET (s DELETE b) * b      by MULT_COMM
   So   b divides (PROD_SET s)           by divides_def
   or   p divides (PROD_SET s)           by DIVIDES_TRANS
*)
val proudct_factors_coprime_divisor_property = store_thm(
  "proudct_factors_coprime_divisor_property",
  ``!n p. 1 < p /\ coprime p n ==> !m. (ordz p n) < m ==> p divides (product_factors n m)``,
  rw[product_factors_def] >>
  qabbrev_tac `s = power_factors n m` >>
  `FINITE s` by rw[power_factors_finite, Abbr`s`] >>
  qabbrev_tac `j = ordz p n` >>
  `0 < j /\ (n ** j MOD p = 1)` by rw[ZN_coprime_order_alt, Abbr`j`] >>
  `0 < p` by decide_tac >>
  `(n ** j - 1) MOD p = 0` by rw[MOD_EQ_DIFF, ONE_MOD] >>
  qabbrev_tac `b = n ** j - 1` >>
  `p divides b` by rw[DIVIDES_MOD_0, Abbr`b`] >>
  `b IN s` by metis_tac[power_factors_element] >>
  `b INSERT s = s` by rw[GSYM ABSORPTION] >>
  `PROD_SET s = b * PROD_SET (s DELETE b)` by rw[GSYM PROD_SET_THM] >>
  `b divides (PROD_SET s)` by metis_tac[divides_def, MULT_COMM] >>
  metis_tac[DIVIDES_TRANS]);

(* Theorem: 1 < k /\ coprime k n /\ ordz k n < m ==> k divides (product_factors n m) *)
(* Proof:
   By product_factors_def, this is to show:
      ordz k n < m ==> k divides (PROD_SET (power_factors n m))
   Let j = ordz k n
   Then 0 < j /\ (n ** j MOD k = 1)           by ZN_coprime_order_alt, 1 < k
     or (n ** j - 1) MOD k = 0                by MOD_EQ_DIFF, MOD_LESS, 0 < k
     or k divides (n ** j - 1)                by DIVIDES_MOD_0, 0 < k
   Since FINITE (power_factors n m            by power_factors_finite
     and (n ** j - 1) IN (power_factors n m)  by power_factors_element
   Hence  k divides (product_factors n m)     by PROD_SET_DIVISORS
*)
val product_factors_divisors = store_thm(
  "product_factors_divisors",
  ``!n m k. 1 < k /\ coprime k n /\ ordz k n < m ==> k divides (product_factors n m)``,
  rw[product_factors_def] >>
  qabbrev_tac `j = ordz k n` >>
  `0 < j /\ (n ** j MOD k = 1)` by rw[ZN_coprime_order_alt, Abbr`j`] >>
  `(n ** j - 1) MOD k = 0` by rw[MOD_EQ_DIFF, MOD_LESS] >>
  `k divides (n ** j - 1)` by rw[DIVIDES_MOD_0] >>
  metis_tac[PROD_SET_DIVISORS, power_factors_element, power_factors_finite]);

(* Theorem: 1 < n ==> 0 < product_factors n m *)
(* Proof:
   By product_factors_def, this is to show: 0 < PROD_SET (power_factors n m)
   Since FINITE (power_factors n m)             by power_factors_finite
     and 0 NOTIN power_factors n m              by power_factors_element_nonzero
   Hence 0 < PROD_SET (power_factors n m)       by PROD_SET_NONZERO
*)
val product_factors_pos = store_thm(
  "product_factors_pos",
  ``!n m. 1 < n ==> 0 < product_factors n m``,
  rw[product_factors_def] >>
  `FINITE (power_factors n m)` by rw[power_factors_finite] >>
  `0 NOTIN power_factors n m` by metis_tac[power_factors_element_nonzero] >>
  rw[PROD_SET_NONZERO]);

(* ------------------------------------------------------------------------- *)
(* Upper Bound of Product of Power Factors                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < n /\ 1 < m ==> product_factors n m < n ** ((m ** 2) DIV 2) *)
(* Proof:
   By product_factors_def, this is to show: PROD_SET (power_factors n m) < n ** (m ** 2 DIV 2)
   Let s = power_factors n m.
    Then FINITE s                               by power_factors_finite
     and s <> {}                                by power_factors_nonempty, 1 < m
    also 0 NOTIN s                              by power_factors_element_nonzero, 1 < n
   Hence PROD_SET s < PROD_SET (IMAGE SUC s)    by PROD_SET_LESS_SUC
     PROD_SET (IMAGE SUC s)
   = PROD_SET (IMAGE (\j. n ** j) (residue m))  by power_factors_image_suc, 0 < n
   = PROD_SET (IMAGE (\j. n ** j) (count m))    by PROD_SET_IMAGE_EXP_NONZERO
   = n ** SUM_SET (count m)                     by PROD_SET_IMAGE_EXP, 1 < n
   = n ** (m * (m - 1) DIV 2)                   by SUM_SET_COUNT

   Since m * (m - 1) < m * m = m ** 2           by EXP_2
      or m * (m - 1) <= m ** 2                  by LESS_IMP_LESS_OR_EQ
         (m * (m - 1)) DIV 2 <= (m ** 2) DIV 2  by DIV_LE_MONOTONE
      so n ** ((m * (m - 1)) DIV 2) <= n ** ((m ** 2) DIV 2)   by EXP_BASE_LE_MONO, 1 < n
   Therefore,
      PROD_SET s < PROD_SET (IMAGE SUC s)
                 = n ** (m * (m - 1) DIV 2)
                 <= n ** ((m ** 2) DIV 2)
   or PROD_SET s < n ** ((m ** 2) DIV 2)        by LESS_LESS_EQ_TRANS
*)
val product_factors_upper = store_thm(
  "product_factors_upper",
  ``!n m. 1 < n /\ 1 < m ==> product_factors n m < n ** ((m ** 2) DIV 2)``,
  rw[product_factors_def] >>
  qabbrev_tac `s = power_factors n m` >>
  `FINITE s` by rw[power_factors_finite, Abbr`s`] >>
  `s <> {}` by rw[power_factors_nonempty, Abbr`s`] >>
  `0 NOTIN s` by metis_tac[power_factors_element_nonzero] >>
  `PROD_SET s < PROD_SET (IMAGE SUC s)` by rw[PROD_SET_LESS_SUC] >>
  `0 < n /\ 0 < m` by decide_tac >>
  `PROD_SET (IMAGE SUC s) = PROD_SET (IMAGE (\j. n ** j) (residue m))` by rw[GSYM power_factors_image_suc] >>
  `_ = PROD_SET (IMAGE (\j. n ** j) (count m))` by rw[PROD_SET_IMAGE_EXP_NONZERO] >>
  `_ = n ** SUM_SET (count m)` by rw[PROD_SET_IMAGE_EXP] >>
  `_ = n ** (m * (m - 1) DIV 2)` by rw[SUM_SET_COUNT] >>
  `m * (m - 1) < m ** 2` by rw_tac std_ss[EXP_2] >>
  `(m * (m - 1)) DIV 2 <= (m ** 2) DIV 2` by rw[DIV_LE_MONOTONE, LESS_IMP_LESS_OR_EQ] >>
  `n ** ((m * (m - 1)) DIV 2) <= n ** ((m ** 2) DIV 2)` by rw[EXP_BASE_LE_MONO] >>
  metis_tac[LESS_LESS_EQ_TRANS]);

(* ------------------------------------------------------------------------- *)
(* Non-dividing coprimes of Product of Power Factors                         *)
(* ------------------------------------------------------------------------- *)

(* Define non-dividing coprimes *)
val power_factors_coprime_nondivisor_def = Define`
    power_factors_coprime_nondivisor n m = {x | coprime x n /\ ~(x divides (product_factors n m))}
`;

(* Theorem: x IN power_factors_coprime_nondivisor n m <=>
            coprime x n /\ ~(x divides (product_factors n m)) *)
(* Proof: by power_factors_coprime_nondivisor_def. *)
val power_factors_coprime_nondivisor_element = store_thm(
  "power_factors_coprime_nondivisor_element",
  ``!n m x. x IN power_factors_coprime_nondivisor n m <=>
           coprime x n /\ ~(x divides (product_factors n m))``,
  rw[power_factors_coprime_nondivisor_def]);

(* Theorem: 1 < m ==> !x. x IN power_factors_coprime_nondivisor n m ==> 1 < x *)
(* Proof:
   Since ~(x divides (product_factors n m))  by power_factors_coprime_nondivisor_element
         x <> 1                              by ONE_DIVIDES_ALL
      If x = 0, coprime x n ==> n = 1        by coprime_0L
    But then product_factors 1 m = 0         by product_factors_zero, 1 < m.
    making x divides (product_factors 1 m)   by ALL_DIVIDES_0
    Hence x <> 0. Overall, 1 < x.
*)
val power_factors_coprime_nondivisor_property = store_thm(
  "power_factors_coprime_nondivisor_property",
  ``!n m. 1 < m ==> !x. x IN power_factors_coprime_nondivisor n m ==> 1 < x``,
  rw[power_factors_coprime_nondivisor_element] >>
  `x <> 1` by metis_tac[ONE_DIVIDES_ALL] >>
  `x <> 0` by metis_tac[product_factors_zero, coprime_0L, ALL_DIVIDES_0] >>
  decide_tac);

(* Theorem: 1 < n /\ 1 < m ==> power_factors_coprime_nondivisor n m <> {} *)
(* Proof
   By power_factors_coprime_nondivisor_def, this is to show:
      1 < n /\ 1 < m ==> ?x. coprime x n /\ ~(x divides (product_factors n m))
   Let z = product_factors n m
       k = (m ** 2) DIV 2
   First, get the bounds of (product_factors n m):
      z < n ** k                  by product_factors_upper, 1 < n, 1 < m
      0 < z                       by product_factors_pos, 1 < n
      0 < 1 < k                   by ONE_LT_HALF_SQ
   Now, get a large prime,
      ?p. prime p /\ n < p        by NEXT_LARGER_PRIME, PRIME_INDEX
   Take x = p ** k, then
         coprime p n              by prime_coprime_all_lt, 0 < n /\ n < p
      or coprime (p ** k) n       by coprime_exp
    Also n ** k < p ** k          by EXP_EXP_LT_MONO, n < p /\ 0 < k
      so z < p ** k               by above
      or ~(p ** k <= z)
      or ~(divides (p ** k) z)    by DIVIDES_LE
*)
val power_factors_coprime_nondivisor_nonempty = store_thm(
  "power_factors_coprime_nondivisor_nonempty",
  ``!n m. 1 < n /\ 1 < m ==> power_factors_coprime_nondivisor n m <> {}``,
  rw[power_factors_coprime_nondivisor_def, EXTENSION] >>
  qabbrev_tac `z = product_factors n m` >>
  qabbrev_tac `k = (m ** 2) DIV 2` >>
  `z < n ** k` by rw[product_factors_upper, Abbr`z`, Abbr`k`] >>
  `0 < z` by rw[product_factors_pos, Abbr`z`] >>
  `1 < k` by rw[ONE_LT_HALF_SQ, Abbr`k`] >>
  `0 < k /\ 0 < n` by decide_tac >>
  `?p. prime p /\ n < p` by metis_tac[NEXT_LARGER_PRIME, PRIME_INDEX] >>
  `coprime p n` by rw[prime_coprime_all_lt] >>
  `coprime (p ** k) n` by rw[coprime_exp] >>
  `n ** k < p ** k` by rw_tac std_ss[EXP_EXP_LT_MONO] >>
  `~(p ** k <= z)` by decide_tac >>
  metis_tac[DIVIDES_LE]);

(* Theorem: Any power_factors_coprime_nondivisor has order at least m.
   1 < m ==> !k. k IN (power_factors_coprime_nondivisor n m) ==> m <= ordz k n *)
(* Proof
   Since coprime k n /\
        ~(k divides (product_factors n m)) by power_factors_coprime_nondivisor_element
     and 1 < k                             by power_factors_coprime_nondivisor_property, 1 < m
      so ~(ordz k n < m)                   by proudct_factors_coprime_divisor_property
      or m <= ordz k n
*)
val power_factors_coprime_nondivisor_order = store_thm(
  "power_factors_coprime_nondivisor_order",
  ``!n m. 1 < m ==> !k. k IN (power_factors_coprime_nondivisor n m) ==> m <= ordz k n``,
  rpt strip_tac >>
  `coprime k n /\ ~(k divides (product_factors n m))` by metis_tac[power_factors_coprime_nondivisor_element] >>
  `1 < k` by metis_tac[power_factors_coprime_nondivisor_property] >>
  `~(ordz k n < m)` by metis_tac[proudct_factors_coprime_divisor_property] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* LCM of coprimes divides Product of Power Factors                          *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Common Multiples of Residue n                                             *)
(* ------------------------------------------------------------------------- *)

(* Define Common Multiple of residue n *)
val residue_common_multiple_def = Define`
  residue_common_multiple n = {m | 0 < m /\ !j. j IN residue n ==> j divides m}
`;

(* Theorem: m IN residue_common_multiple n <=> 0 < m /\ !j. 0 < j /\ j < n ==> j divides m *)
(* Proof: by residue_common_multiple_def. *)
val residue_common_multiple_element = store_thm(
  "residue_common_multiple_element",
  ``!n m. m IN residue_common_multiple n <=> 0 < m /\ !j. 0 < j /\ j < n ==> j divides m``,
  rw[residue_common_multiple_def, residue_def]);

(* Theorem: residue_common_multiple n <> {} *)
(* Proof:
   By residue_common_multiple_def and residue_def, this is to show:
      ?x. x <> 0 /\ !j. ((j = 0) \/ ~(j < n)) \/ j divides x
   Let x = FACT n, this is to show:
   (1) FACT n <> 0, true by FACT_LESS.
   (2) ((j = 0) \/ ~(j < n)) \/ j divides (FACT n)
       By contradiction, to show: j <> 0 /\ j < n /\ ~(j divides (FACT n)) ==> F
       But  0 < j /\ j <= n ==> j divides (FACT n)  by LEQ_DIVIDES_FACT
       Hence true by contradiction.
*)
val residue_common_multiple_nonempty = store_thm(
  "residue_common_multiple_nonempty",
  ``!n. residue_common_multiple n <> {}``,
  rw[residue_common_multiple_def, residue_def, EXTENSION] >>
  qexists_tac `FACT n` >>
  rpt strip_tac >| [
    `0 < FACT n` by rw[FACT_LESS] >>
    decide_tac,
    spose_not_then strip_assume_tac >>
    `0 < j /\ j <= n` by decide_tac >>
    metis_tac[LEQ_DIVIDES_FACT]
  ]);

(* Theorem: 0 NOTIN residue_common_multiple n *)
(* Proof: by residue_common_multiple_def *)
val residue_common_multiple_nonzero = store_thm(
  "residue_common_multiple_nonzero",
  ``!n. 0 NOTIN residue_common_multiple n``,
  rw[residue_common_multiple_def]);

(* Theorem: m IN residue_common_multiple n ==>
            !k. 0 < k ==> k * m IN residue_common_multiple n *)
(* Proof:
   By residue_common_multiple_def, this is to show:
   (1) 0 < m /\ 0 < k ==> 0 < k * m
       True by ZERO_LESS_MULT.
   (2) j IN residue n /\ (!j. j IN residue n ==> j divides m) ==> j divides (k * m)
       Condition implies j divides m, hence true by DIVIDES_MULTIPLE.
*)
Theorem residue_common_multiple_has_multiple:
  !n m. m IN residue_common_multiple n ==>
        !k. 0 < k ==> k * m IN residue_common_multiple n
Proof
  rw[residue_common_multiple_def, DIVIDES_MULTIPLE]
QED

(* Theorem: b < a /\ a IN residue_common_multiple n /\ b IN residue_common_multiple n ==>
           (a - b) IN residue_common_multiple n *)
(* Proof:
   By residue_common_multiple_def, this is to show:
   (1) b < a ==> 0 < a - b
       True by arithmetic.
   (2) j IN residue n /\ (!j. j IN residue n ==> j divides a) /\
                         (!j. j IN residue n ==> j divides b) ==> j divides (a - b)
       Condition implies j divides a /\ j divides b, hence true by DIVIDES_SUB.
*)
val residue_common_multiple_has_sub = store_thm(
  "residue_common_multiple_has_sub",
  ``!n a b. b < a /\ a IN residue_common_multiple n /\ b IN residue_common_multiple n ==>
           (a - b) IN residue_common_multiple n``,
  rw[residue_common_multiple_def, DIVIDES_SUB]);

(* Theorem: m IN residue_common_multiple n <=> 0 < m /\ !j. 1 < j /\ j < n ==> j divides m *)
(* Proof:
   If part: m IN residue_common_multiple n ==> 0 < m /\ !j. 1 < j /\ j < n ==> j divides m
      True by residue_common_multiple_def, as that gives the range 0 < j /\ j < n.
   Only-if part: 0 < m /\ !j. 1 < j /\ j < n ==> j divides m ==> m IN residue_common_multiple n
   The implication    0 < m /\ !j. 1 < j /\ j < n ==> j divides m)
   can be extended to 0 < m /\ !j. 0 < j /\ j < n ==> j divides m)
   by putting j = 1, and 1 divides m is true       by ONE_DIVIDES_ALL, 1 < n.
   Thus m IN residue_common_multiple n.
*)
val residue_common_multiple_element_1 = store_thm(
  "residue_common_multiple_element_1",
  ``!n m. 1 < n ==> (m IN residue_common_multiple n <=> 0 < m /\ !j. 1 < j /\ j < n ==> j divides m)``,
  rw[residue_common_multiple_def, residue_def] >>
  rw[EQ_IMP_THM] >>
  Cases_on `j = 1` >> rw[]);

(* ------------------------------------------------------------------------- *)
(* Least Common Multiple of Residue n                                        *)
(* ------------------------------------------------------------------------- *)

(* Define LCM of 1..(n-1) = residue n *)
val residue_lcm_def = Define`
  residue_lcm n = MIN_SET (residue_common_multiple n)
`;

(* Theorem: The residue_lcm divides any common multiple
            m IN residue_common_multiple n ==> (residue_lcm n) divides m *)
(* Proof:
   By residue_lcm_def, this is to show:
      m IN residue_common_multiple n ==> (MIN_SET (residue_common_multiple n)) divides m
   Let s = residue_common_multiple n, k = MIN_SET s.
    Then m IN s ==> s <> {}                 by MEMBER_NOT_EMPTY
   Hence k IN s /\ !x. x IN s ==> k <= x    by MIN_SET_LEM
     and k IN s ==> 0 < k /\ !j. 0 < j /\ j < n ==> j divides k  by residue_common_multiple_element
   Now, ?r q. (m = q * k + r) /\ r < k      by DA, division algorithm
   If r = 0,
      then m = q * k                        by ADD_0
        or k divides m                      by divides_def
   If r <> 0, 0 < r.
      If q = 0,
        then m = r                          by MULT, ADD
          or r IN s, hence k <= r           by above
        This contradicts r < k.
      If q <> 0, 0 < q.
        q * k < m /\ (r = m - q * k)        by 0 < r
        q * k IN s                          by residue_common_multiple_has_multiple, MULT_COMM, 0 < q
        so r IN s, hence k <= r             by residue_common_multiple_has_sub, q * k < m
        or k <= r
        This contradicts r < k.
*)
val residue_lcm_divides_common_multiple = store_thm(
  "residue_lcm_divides_common_multiple",
  ``!n m. m IN residue_common_multiple n ==> (residue_lcm n) divides m``,
  rw[residue_lcm_def] >>
  qabbrev_tac `s = residue_common_multiple n` >>
  qabbrev_tac `k = MIN_SET s` >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `k IN s /\ !x. x IN s ==> k <= x` by rw[MIN_SET_LEM, Abbr`k`] >>
  `0 < k /\ !j. 0 < j /\ j < n ==> j divides k` by metis_tac[residue_common_multiple_element] >>
  `?r q. (m = q * k + r) /\ r < k` by rw[DA] >>
  Cases_on `r = 0` >| [
    `m = q * k` by decide_tac >>
    metis_tac[divides_def],
    Cases_on `q = 0` >| [
      `m = r` by rw[] >>
      `k <= r` by metis_tac[] >>
      decide_tac,
      `0 < q /\ 0 < r /\ q * k < m /\ (r = m - q * k)` by decide_tac >>
      `q * k IN s` by rw[residue_common_multiple_has_multiple, MULT_COMM, Abbr`s`] >>
      `r IN s` by rw[residue_common_multiple_has_sub, Abbr`s`] >>
      `k <= r` by metis_tac[] >>
      decide_tac
    ]
  ]);

(* ------------------------------------------------------------------------- *)
(* Relate Residue LCM to List LCM of Leibniz Triangle                        *)
(* ------------------------------------------------------------------------- *)

(*
Idea:
If 1...(n-1) divides c
and !m. 1...(n-1) divides m ==> c divides m
Then c = residue_lcm n.

Then prove that c = list_lcm (leibniz_vertical (n-1)).
*)

(* Note: the following proof repeats a bit of the previous proof. *)

(* Theorem: (c = residue_lcm n) <=>
            c IN (residue_common_multiple n) /\
            !m. m IN (residue_common_multiple n) ==> c divides m *)
(* Proof:
   Note residue_common_multiple n <> {}    by residue_common_multiple_nonempty
   By residue_lcm_def, this is to show:
   (1) MIN_SET (residue_common_multiple n) IN residue_common_multiple n
       True by MIN_SET_LEM.
   (2) m IN residue_common_multiple n ==> (MIN_SET (residue_common_multiple n)) divides m
       Let  c = MIN_SET (residue_common_multiple n)
       Then c IN residue_common_multiple n   by MIN_SET_LEM
         so 0 < c                            by residue_common_multiple_element
        and ?q r. m = q * c + r, with r < c  by DA, division algorithm, 0 < c.
       If r = 0,
         then m = q * c, so c divides m      by divides_def
       If r <> 0, 0 < r.
           and c <= m                        by MIN_SET_LEM
         hence q <> 0, otherwise m = r < c, a contradiction.
         Thus 0 < q,
         and q * c IN (residue_common_multiple n)  by residue_common_multiple_has_multiple
         Therefore, r = m - q * c, and q * c < m   by arithmetic
         so      r IN (residue_common_multiple n)  by residue_common_multiple_has_sub, q*c < m.
         giving  c <= r                      by MIN_SET_LEM
         which contradicts r < c.
   (3) !m. m IN residue_common_multiple n ==> c divides m ==> c = MIN_SET (residue_common_multiple n)
       Let z = MIN_SET (residue_common_multiple n)
       Then z IN residue_common_multiple n   by MIN_SET_LEM
        and z <= c                           by MIN_SET_LEM
        and 0 < z                            by residue_common_multiple_element
       With z IN residue_common_multiple n,
             divides c z                     by implication
       hence c <= z                          by DIVIDES_LE
       Therefore c = z                       by EQ_LESS_EQ
*)
val residue_lcm_property = store_thm(
  "residue_lcm_property",
  ``!n c. (c = residue_lcm n) <=>
      c IN (residue_common_multiple n) /\
      !m. m IN (residue_common_multiple n) ==> c divides m``,
  rpt strip_tac >>
  `residue_common_multiple n <> {}` by rw[residue_common_multiple_nonempty] >>
  rw[residue_lcm_def, EQ_IMP_THM] >| [
    rw[MIN_SET_LEM],
    qabbrev_tac `c = MIN_SET (residue_common_multiple n)` >>
    `c IN residue_common_multiple n` by rw[MIN_SET_LEM, Abbr`c`] >>
    `0 < c` by metis_tac[residue_common_multiple_element] >>
    `?r q. (m = q * c + r) /\ (r < c)` by rw[DA] >>
    Cases_on `r = 0` >| [
      `m = q * c` by decide_tac >>
      metis_tac[divides_def],
      `0 < r` by decide_tac >>
      `c <= m` by rw[MIN_SET_LEM, Abbr`c`] >>
      Cases_on `q = 0` >| [
        `m = r` by rw[] >>
        `m < c` by decide_tac >>
        decide_tac,
        `0 < q` by decide_tac >>
        `q * c IN (residue_common_multiple n)` by rw[residue_common_multiple_has_multiple] >>
        `(r = m - q * c) /\ q * c < m` by decide_tac >>
        `r IN (residue_common_multiple n)` by rw[residue_common_multiple_has_sub] >>
        `c <= r` by rw[MIN_SET_LEM, Abbr`c`] >>
        decide_tac
      ]
    ],
    qabbrev_tac `z = MIN_SET (residue_common_multiple n)` >>
    `z IN residue_common_multiple n` by rw[MIN_SET_LEM, Abbr`z`] >>
    `z <= c` by rw[MIN_SET_LEM, Abbr`z`] >>
    `0 < z` by metis_tac[residue_common_multiple_element] >>
    `c <= z` by rw[DIVIDES_LE] >>
    decide_tac
  ]);

(*
> |- !n. residue_lcm n = MIN_SET (residue_common_multiple n)
> |- !n. residue_common_multiple n = {m | 0 < m /\ !j. j IN residue n ==> j divides m}
> |- !n. residue n = {i | 0 < i /\ i < n}
Hence 1 < n for residue_lcm n to be defined, as MIN_SET {} is meaningless.
residue_lcm n = MIN_SET { commomn multiples of 1..(n-1) inclusive}
list_lcm (leibniz_vertical n) = least (common multiples of 1 to (n+1) inclusive)
so residue_lcm n = list_lcm (leibniz_vertical (n-2)) >= 2 ** (n-2) = (2 ** n)/4
*)

(* Theorem: 1 < n ==> (residue_lcm n = list_lcm (leibniz_vertical (n-2))) *)
(* Proof:
   Let c = list_lcm (leibniz_vertical (n-2)).
   Then 0 < c                              by list_lcm_pos, leibniz_vertical_pos
   We have !j. j < n <=> j <= SUC (n-2)    by 1 < n
        so !j. 0 < j /\ j < n <=> MEM j (leibniz_vertical (n-2))   by leibniz_vertical_mem
       and !j. 0 < j /\ j < n ==> j divides c                      by list_lcm_is_common_multiple
   Hence c IN (residue_common_multiple n)                          by residue_common_multiple_element
    Also !m. m IN (residue_common_multiple n)
         ==> 0 < m /\ (!j. MEM j (leibniz_vertical (n-2)) ==> j divides m) by residue_common_multiple_element
     and !m. m IN (residue_common_multiple n) ==> c divides m      by list_lcm_is_least_common_multiple
   Therefore c = residue_lcm n                                     by residue_lcm_property
*)
val residue_lcm_alt = store_thm(
  "residue_lcm_alt",
  ``!n. 1 < n ==> (residue_lcm n = list_lcm (leibniz_vertical (n-2)))``,
  rpt strip_tac >>
  qabbrev_tac `c = list_lcm (leibniz_vertical (n-2))` >>
  `0 < c` by rw[list_lcm_pos, leibniz_vertical_pos, Abbr`c`] >>
  `!j. j < n <=> j <= SUC (n-2)` by decide_tac >>
  `!j. 0 < j /\ j < n <=> MEM j (leibniz_vertical (n-2))` by rw[GSYM leibniz_vertical_mem] >>
  `!j. 0 < j /\ j < n ==> j divides c` by rw[list_lcm_is_common_multiple, Abbr`c`] >>
  metis_tac[residue_common_multiple_element, list_lcm_is_least_common_multiple, residue_lcm_property]);

(* Theorem: 1 < n ==> (residue_lcm n = lcm_run (n - 1)) *)
(* Proof: by residue_lcm_alt *)
val residue_lcm_eq_list_lcm = store_thm(
  "residue_lcm_eq_list_lcm",
  ``!n. 1 < n ==> (residue_lcm n = list_lcm [1 .. (n - 1)])``,
  rw[residue_lcm_alt]);

(* ------------------------------------------------------------------------- *)
(* Bounds for Residue LCM                                                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < n /\ 1 < m /\ 1 < k /\
            (!j. 1 < j /\ j < k ==> coprime j n /\ ordz j n < m) ==>
            residue_lcm k <= (product_factors n m) *)
(* Proof:
   Since !j. 1 < j /\ j < k /\ coprime j n /\ ordz j n < m
     ==> j divides (product_factors n m)                 by product_factors_divisors
    and  0 < product_factors n m                         by product_factors_pos, 1 < n
     so  (product_factors n m) IN residue_common_multiple k     by residue_common_multiple_element_1, 1 < k
   Hence (residue_lcm k) divides (product_factors n m)   by residue_lcm_divides_common_multiple
      or (residue_lcm k) <= (product_factors n m)        by DIVIDES_LE, 0 < product_factors n m
*)
val product_factors_lower = store_thm(
  "product_factors_lower",
  ``!n m k. 1 < n /\ 1 < m /\ 1 < k /\
   (!j. 1 < j /\ j < k ==> coprime j n /\ ordz j n < m) ==> residue_lcm k <= (product_factors n m)``,
  rpt strip_tac >>
  `!j. 1 < j /\ j < k /\ coprime j n /\ ordz j n < m ==> j divides (product_factors n m)` by rw[product_factors_divisors] >>
  `0 < product_factors n m` by rw[product_factors_pos] >>
  `(product_factors n m) IN residue_common_multiple k` by rw[residue_common_multiple_element_1] >>
  `(residue_lcm k) divides (product_factors n m)` by rw[residue_lcm_divides_common_multiple] >>
  rw[DIVIDES_LE]);

(* Theorem: 1 < n /\ 1 < m /\ 1 < k /\
            (!j. 1 < j /\ j < k ==> coprime j n /\ ordz j n < m) ==>
            residue_lcm k < n ** ((m ** 2) DIV 2) *)
(* Proof:
   Since (residue_lcm k) <= (product_factors n m)        by product_factors_lower
     and product_factors n m < n ** ((m ** 2) DIV 2)     by product_factors_upper
   Therefore (residue_lcm k) < n ** ((m ** 2) DIV 2)     by LESS_EQ_LESS_TRANS
*)
val residue_lcm_upper = store_thm(
  "residue_lcm_upper",
  ``!n m k. 1 < n /\ 1 < m /\ 1 < k /\
   (!j. 1 < j /\ j < k ==> coprime j n /\ ordz j n < m) ==>
   residue_lcm k < n ** ((m ** 2) DIV 2)``,
  metis_tac[product_factors_upper, product_factors_lower, LESS_EQ_LESS_TRANS]);

(* Theorem: 1 < n ==> 2 ** (n - 2) <= residue_lcm n *)
(* Proof:
     residue_lcm n
   = list_lcm (leibniz_vertical (n-2))   by residue_lcm_alt, 1 < n.
   >= 2 ** (n-2)                         by leibniz_vertical_lcm_lower
*)
val residue_lcm_lower = store_thm(
  "residue_lcm_lower",
  ``!n. 1 < n ==> 2 ** (n - 2) <= residue_lcm n``,
  rpt strip_tac >>
  `residue_lcm n = list_lcm (leibniz_vertical (n-2))` by rw[residue_lcm_alt] >>
  metis_tac[leibniz_vertical_lcm_lower]);

(* Question: How big must k be in order that m <= ordz k n ?
   Searching from k = 1, k = 2, etc.
   Consider the j's in (residue k), i.e. 0 < j < k.
   Assume for all such j, no such candidate k is found.
   That is, because for these j's, ordz j n < m.
   or the following condition is satisfied:
   !j. 0 < j /\ j < k /\ coprime j n /\ ordz j n < m
   This gives: residue_lcm k < n ** ((m ** 2) DIV 2)    by residue_lcm_upper, independent of k.
   But always: 2 ** (k-2) <= residue_lcm k              by residue_lcm_lower, increases with k.
   Also: n ** ((m ** 2) DIV 2) < 2 ** ((SUC (LOG2 n)) * ((m ** 2) DIV 2))  by integer arithmetic
   Therefore   2 ** (k-2) < 2 ** ((SUC (LOG2 n)) * ((m ** 2) DIV 2))
   or                k-2 < (SUC (LOG2 n)) * ((m ** 2) DIV 2)
   or                  k < (SUC (LOG2 n)) * ((m ** 2) DIV 2) + 2 = f n m
   This means, the situation is possible only because k < f n m.
   So if you search from k = 1, k = 2, up to k = f n m,
   Then such situations are impossible, or there is some k such that m <= ordz k n
*)

(* Theorem:  1 < n /\ 1 < m /\ 1 < k /\
             (!j. 1 < j /\ j < k /\ coprime j n /\ ordz j n < m) ==>
             k < 2 + SUC (LOG2 n) * (m ** 2 DIV 2) *)
(* Proof:
   Since residue_lcm k < n ** ((m ** 2) DIV 2)      by residue_lcm_upper, 1 < n, 1 < m
     and 2 ** (k-2) <= residue_lcm k                by residue_lcm_lower, 1 < k
   Step 1: show n ** ((m ** 2) DIV 2) < 2 ** SUC (LOG2 n)) ** ((m ** 2) DIV 2
   Since 1 < (m ** 2) DIV 2                         by ONE_LT_HALF_SQ, 1 < m
     and n < 2 ** SUC (LOG2 n)                      by LOG2_PROPERTY, 0 < n
      so n ** ((m ** 2) DIV 2)
         < (2 ** SUC (LOG2 n)) ** ((m ** 2) DIV 2)  by EXP_EXP_LT_MONO
         = 2 ** ((SUC (LOG2 n)) * ((m ** 2) DIV 2)) by EXP_EXP_MULT
   Step 2: conclusion
   Hence 2 ** (k-2) < 2 ** (SUC (LOG2 n) * (m ** 2 DIV 2))
      or k - 2 < SUC (LOG2 n) * (m ** 2 DIV 2)      by EXP_BASE_LT_MONO, 1 < 2
      or k < 2 + SUC (LOG2 n) * (m ** 2 DIV 2)      by arithmetic
*)
val ZN_order_modulus_upper = store_thm(
  "ZN_order_modulus_upper",
  ``!n m k. 1 < n /\ 1 < m /\ 1 < k /\
    (!j. 1 < j /\ j < k ==> coprime j n /\ ordz j n < m) ==>
    k < 2 + SUC (LOG2 n) * (m ** 2 DIV 2)``,
  rpt strip_tac >>
  `residue_lcm k < n ** ((m ** 2) DIV 2)` by rw[residue_lcm_upper] >>
  `2 ** (k-2) <= residue_lcm k` by rw[residue_lcm_lower] >>
  `1 < (m ** 2) DIV 2` by rw[ONE_LT_HALF_SQ] >>
  `0 < (m ** 2) DIV 2 /\ 0 < n /\ 0 < k` by decide_tac >>
  `n < 2 ** SUC (LOG2 n)` by rw[LOG2_PROPERTY] >>
  `n ** ((m ** 2) DIV 2) < (2 ** SUC (LOG2 n)) ** ((m ** 2) DIV 2)` by rw[EXP_EXP_LT_MONO] >>
  `(2 ** SUC (LOG2 n)) ** ((m ** 2) DIV 2) = 2 ** ((SUC (LOG2 n)) * ((m ** 2) DIV 2))` by rw[EXP_EXP_MULT] >>
  `2 ** (k - 2) < 2 ** (SUC (LOG2 n) * (m ** 2 DIV 2))` by decide_tac >>
  `k - 2 < SUC (LOG2 n) * (m ** 2 DIV 2)` by metis_tac[EXP_BASE_LT_MONO, DECIDE``1 < 2``] >>
  decide_tac);

(* Theorem: ZN modulus for order of n to be at least m exists.
            1 < n /\ 1 < m ==>
            ?k. 1 < k /\ k < 2 + SUC (LOG2 n) * (m ** 2 DIV 2) /\
            (coprime k n ==> m <= ordz k n) *)
(* Proof:
   Let h = 2 + SUC (LOG2 n) * (m ** 2 DIV 2)
   By contradiction, assume !k. 1 < k /\ k < h /\ ~(coprime k n ==> m <= ordz k n)).
    Since  1 < h       by arithmetic
      and ~(p => q) == ~(~p or q) == p and ~q,
    where ~(m <= ordz k n)) means ordz k n < m  by NOT_LESS_EQUAL
       so !k. 1 < k /\ k < h ==> coprime k n /\ ordz k n < m
   giving  h < h       by ZN_order_modulus_upper, 1 < h.
   which is false      by prim_recTheory.LESS_REFL
*)
val ZN_order_modulus_exists = store_thm(
  "ZN_order_modulus_exists",
  ``!n m. 1 < n /\ 1 < m ==>
    ?k. 1 < k /\ k < 2 + SUC (LOG2 n) * (m ** 2 DIV 2) /\ (coprime k n ==> m <= ordz k n)``,
  rpt strip_tac >>
  `1 < 2 + SUC (LOG2 n) * (m ** 2 DIV 2)` by decide_tac >>
  metis_tac[ZN_order_modulus_upper, NOT_LESS_EQUAL, DECIDE``!n. ~(n < n)``]);

(* Theorem: ZN modulus for order of n to be at least m exists.
            1 < n /\ 1 < m ==>
            ?k. 1 < k /\ k < 2 + SUC (LOG2 n) * (m ** 2 DIV 2) /\
            (~ coprime k n \/ m <= ordz k n) *)
(* Proof: by ZN_order_modulus_exists, and p ==> q == ~p or q. *)
val ZN_order_modulus_exists_alt = store_thm(
  "ZN_order_modulus_exists_alt",
  ``!n m. 1 < n /\ 1 < m ==>
    ?k. 1 < k /\ k < 2 + SUC (LOG2 n) * (m ** 2 DIV 2) /\ (~ coprime k n \/ m <= ordz k n)``,
  metis_tac[ZN_order_modulus_exists]);

(* Theorem: 0 < n /\ prime k /\ m <= ordz k n ==> ~(k divides (product_factors n m)) *)
(* Proof:
   Since p divides (product_factors n m) ==> ordz p n < m   by proudct_factors_prime_divisor_property
   So given m <= ordz k n, p divides (product_factors n m) is false.
*)
val ZN_order_modulus_when_prime = store_thm(
  "ZN_order_modulus_when_prime",
  ``!n m k. 0 < n /\ prime k /\ m <= ordz k n ==> ~(k divides (product_factors n m))``,
  metis_tac[proudct_factors_prime_divisor_property, DECIDE``!n m. ~(n < m) <=> m <= n``]);

(* ------------------------------------------------------------------------- *)
(* ZN bounds based on upper logarithm                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < n /\ 1 < m /\ 1 < k /\
            (!j. 1 < j /\ j < k ==> coprime j n /\ ordz j n < m) ==>
            k < 2 + (ulog n) * HALF (m ** 2) *)
(* Proof:
   Let h = HALF (m ** 2)
   Note residue_lcm k < n ** h               by residue_lcm_upper, 1 < n, 1 < m
    and 2 ** (k - 2) <= residue_lcm k        by residue_lcm_lower, 1 < k

   Step 1: show n ** h <= 2 ** ((ulog n) * h)
   Note      n <= 2 ** ulog n                by ulog_property, 0 < n
        n ** h <= (2 ** ulog n) ** h         by EXP_EXP_LE_MONO
                = 2 ** ((ulog n) * h))       by EXP_EXP_MULT

   Step 2: conclusion
   Hence 2 ** (k - 2) < 2 ** ((ulog n) * h)
      or        k - 2 < (ulog n) * h         by EXP_BASE_LT_MONO, 1 < 2
      or            k < 2 + (ulog n) * h     by arithmetic
*)
val ZN_order_modulus_upper_1 = store_thm(
  "ZN_order_modulus_upper_1",
  ``!n m k. 1 < n /\ 1 < m /\ 1 < k /\
    (!j. 1 < j /\ j < k ==> coprime j n /\ ordz j n < m) ==>
    k < 2 + (ulog n) * HALF (m ** 2)``,
  rpt strip_tac >>
  qabbrev_tac `h = HALF (m ** 2)` >>
  `residue_lcm k < n ** h` by rw[residue_lcm_upper, Abbr`h`] >>
  `2 ** (k - 2) <= residue_lcm k` by rw[residue_lcm_lower] >>
  `n <= 2 ** (ulog n)` by rw[ulog_property] >>
  `n ** h <= (2 ** ulog n) ** h` by rw[EXP_EXP_LE_MONO] >>
  `(2 ** ulog n) ** h = 2 ** ((ulog n) * h)` by rw[EXP_EXP_MULT] >>
  `2 ** (k - 2) < 2 ** ((ulog n) * h)` by decide_tac >>
  `k - 2 < (ulog n) * h` by metis_tac[EXP_BASE_LT_MONO, DECIDE``1 < 2``] >>
  decide_tac);

(* Theorem: ZN modulus for order of n to be at least m exists if coprime.
            1 < n /\ 1 < m ==>
            ?k. 1 < k /\ k < 2 + (ulog n) * HALF (m ** 2) /\ (~ coprime k n \/ m <= ordz k n) *)
(* Proof:
   Let h = 2 + (ulog n) * HALF (m ** 2).
   By contradiction, assume !k. 1 < k /\ k < h /\ ~(coprime k n ==> m <= ordz k n)).
    Since  1 < h             by arithmetic
      and ~(p => q) == ~(~p or q) == p and ~q,
    where ~(m <= ordz k n)) means ordz k n < m  by NOT_LESS_EQUAL
       so !k. 1 < k /\ k < h ==> coprime k n /\ ordz k n < m
   giving  h < h             by ZN_order_modulus_upper_1, 1 < h.
   which is false            by prim_recTheory.LESS_REFL
*)
val ZN_order_modulus_exists_1 = store_thm(
  "ZN_order_modulus_exists_1",
  ``!n m. 1 < n /\ 1 < m ==>
    ?k. 1 < k /\ k < 2 + (ulog n) * HALF (m ** 2) /\ (~ coprime k n \/ m <= ordz k n)``,
  rpt strip_tac >>
  `1 < 2 + (ulog n) * HALF (m ** 2)` by decide_tac >>
  metis_tac[ZN_order_modulus_upper_1, NOT_LESS_EQUAL, DECIDE``!n. ~(n < n)``]);

(* Theorem: 1 < n /\ 1 < m /\ 1 < k /\
            (!j. 1 < j /\ j < k ==> ~(j divides n) /\ ordz j n < m) ==>
            k < 2 + HALF (m ** 2) * (ulog n) *)
(* Proof: by coprime_by_le_not_divides, ZN_order_modulus_upper_1 *)
val ZN_order_modulus_upper_2 = store_thm(
  "ZN_order_modulus_upper_2",
  ``!n m k. 1 < n /\ 1 < m /\ 1 < k /\
    (!j. 1 < j /\ j < k ==> ~(j divides n) /\ ordz j n < m) ==>
    k < 2 + HALF (m ** 2) * (ulog n)``,
  rpt strip_tac >>
  `!j. 1 < j /\ j < k ==> coprime j n /\ ordz j n < m` by rw[coprime_by_le_not_divides] >>
  metis_tac[ZN_order_modulus_upper_1, MULT_COMM]);

(* Theorem: ZN modulus for order of n to be at least m exists if coprime.
            1 < n /\ 1 < m ==>
            ?k. 1 < k /\ k < 2 + HALF (m ** 2) * (ulog n) /\ (k divides n \/ m <= ordz k n) *)
(* Proof:
   Let h = 2 + HALF (m ** 2) * (ulog n).
   By contradiction, assume !k. 1 < k /\ k < h ==> ~(k divides n) /\ ~(m <= ordz k n).
    Since  1 < h             by arithmetic
      and ~(m <= ordz k n)) means ordz k n < m  by NOT_LESS_EQUAL
       so !k. 1 < k /\ k < h ==> ~(k divides n) /\ ordz k n < m
   giving  h < h             by ZN_order_modulus_upper_2, 1 < h.
   which is false            by prim_recTheory.LESS_REFL
*)
val ZN_order_modulus_exists_2 = store_thm(
  "ZN_order_modulus_exists_2",
  ``!n m. 1 < n /\ 1 < m ==>
    ?k. 1 < k /\ k < 2 + HALF (m ** 2) * (ulog n) /\ (k divides n \/ m <= ordz k n)``,
  rpt strip_tac >>
  `1 < 2 + HALF (m ** 2) * (ulog n)` by decide_tac >>
  metis_tac[ZN_order_modulus_upper_2, NOT_LESS_EQUAL, DECIDE``!n. ~(n < n)``]);

(* Theorem: 1 < n /\ 1 < m /\
            (!k. 1 < k /\ k <= c ==> ~(k divides n) /\ ordz k n < m) ==> c < 1 + HALF (m ** 2) * (ulog n) *)
(* Proof: by ZN_order_modulus_upper_2 *)
val ZN_order_modulus_upper_3 = store_thm(
  "ZN_order_modulus_upper_3",
  ``!n m k c. 1 < n /\ 1 < m /\
    (!k. 1 < k /\ k <= c ==> ~(k divides n) /\ ordz k n < m) ==> c < 1 + HALF (m ** 2) * (ulog n)``,
  rpt strip_tac >>
  `!j. 1 < j /\ j < c + 1 ==> ~(j divides n) /\ ordz j n < m` by rw[] >>
  (Cases_on `c = 0` >> simp[]) >>
  `1 < c + 1` by rw[] >>
  `c + 1 < 2 + HALF (m ** 2) * ulog n` by rw[ZN_order_modulus_upper_2] >>
  decide_tac);

(* Theorem: 1 < n /\ 1 < m /\ 1 + HALF (m ** 2) * (ulog n) <= c ==>
            ?k. 1 < k /\ k <= c /\ (k divides n \/ m <= ordz k n) *)
(* Proof: by ZN_order_modulus_upper_3 *)
val ZN_order_modulus_exists_3 = store_thm(
  "ZN_order_modulus_exists_3",
  ``!n m c. 1 < n /\ 1 < m /\ 1 + HALF (m ** 2) * (ulog n) <= c ==>
    ?k. 1 < k /\ k <= c /\ (k divides n \/ m <= ordz k n)``,
  spose_not_then strip_assume_tac >>
  `c < 1 + HALF (m ** 2) * ulog n` by metis_tac[ZN_order_modulus_upper_3, NOT_LESS_EQUAL] >>
  decide_tac);

(* Theorem: 1 < n /\ 1 < m /\ (c = 1 + HALF (m ** 2) * (ulog n)) ==>
            ?k. 1 < k /\ k <= c /\ (k divides n \/ m <= ordz k n) *)
(* Proof: by ZN_order_modulus_exists_3 *)
val ZN_order_modulus_exists_4 = store_thm(
  "ZN_order_modulus_exists_4",
  ``!n m c. 1 < n /\ 1 < m /\ (c = 1 + HALF (m ** 2) * (ulog n)) ==>
    ?k. 1 < k /\ k <= c /\ (k divides n \/ m <= ordz k n)``,
  rw[ZN_order_modulus_exists_3]);

(* The following is the generic form -- cannot move to ringInstances due to SQRT_LE, SQRT_OF_SQ, etc. *)

(* Theorem: 1 < n /\ coprime k n /\ (2 * SUC (LOG2 n)) ** 2 <= ordz k n ==>
            2 * (SQRT (phi k)) * SUC (LOG2 n) <= phi k *)
(* Proof:
   Let j = ordz k n
       s = 2 * (SQRT (phi k)) * SUC (LOG2 n)
   Note 0 < k                            by coprime_gt_1, 1 < n

   Step 1: show SQRT j <= SQRT (phi k)
   Since j divides (phi k)               by ZN_coprime_order_divides_phi, 0 < k, coprime k n
     and 0 < phi k                       by phi_pos, 0 < k
      so j <= phi k                      by DIVIDES_LE, 0 < phi k
    Thus SQRT j <= SQRT (phi k)          by SQRT_LE

   Step 2: show s <= SQRT (phi k) * SQRT (phi k)
   Since 0 < LOG2 n                          by LOG2_POS, 1 < n
      so 0 < 2 * SUC (LOG2 n)
    Now, 2 * (SUC (LOG2 n)) ** 2 <= j        by given
      so 2 * SUC (LOG2 n) <= SQRT j          by SQRT_OF_SQ, SQRT_LE, 0 < 2 * SUC (LOG2 n)
      or 2 * SUC (LOG2 n) <= SQRT (phi k)    from Step 1
   Given s = 2 * (SQRT (phi k)) * SUC (LOG2 n)
           = 2 * SUC (LOG2 n) * SQRT (phi k) by arithmetic
         s <= SQRT (phi k) * SQRT (phi k)    by LESS_MONO_MULT

   Step 3: conclude
   Since SQ (SQRT (phi k) <= phi k           by SQ_SQRT_LE
   Hence s <= phi k                          from Step 2
*)
val ZN_order_condition_property = store_thm(
  "ZN_order_condition_property",
  ``!n k. 1 < n /\ coprime k n /\ (2 * SUC (LOG2 n)) ** 2 <= ordz k n ==>
         2 * (SQRT (phi k)) * SUC (LOG2 n) <= phi k``,
  rpt strip_tac >>
  qabbrev_tac `j = ordz k n` >>
  qabbrev_tac `s = 2 * (SQRT (phi k)) * SUC (LOG2 n)` >>
  `0 < k` by metis_tac[coprime_gt_1] >>
  `j <= phi k` by
  (`j divides (phi k)` by rw[ZN_coprime_order_divides_phi, Abbr`j`] >>
  `0 < phi k` by rw[phi_pos] >>
  metis_tac[DIVIDES_LE]) >>
  `SQRT j <= SQRT (phi k)` by rw[SQRT_LE] >>
  `s <= SQRT (phi k) * SQRT (phi k)` by
    (`0 < LOG2 n` by rw[] >>
  `0 < 2 * SUC (LOG2 n)` by decide_tac >>
  `2 * SUC (LOG2 n) <= SQRT j` by metis_tac[SQRT_OF_SQ, SQRT_LE] >>
  `2 * SUC (LOG2 n) <= SQRT (phi k)` by decide_tac >>
  `s = 2 * SUC (LOG2 n) * SQRT (phi k)` by rw_tac arith_ss[Abbr`s`] >>
  rw[LESS_MONO_MULT]) >>
  `SQ (SQRT (phi k)) <= phi k` by rw[SQ_SQRT_LE] >>
  decide_tac);

(* Theorem: 1 < n /\ coprime k n ==>
            !h. 0 < h /\ h ** 2 <= ordz k n ==> (SQRT (phi k)) * h <= phi k *)
(* Proof:
   Idea:               h ** 2 <= ordz k n <= phi k     by ZN_coprime_order_divides_phi
   Taking square roots,     h <= SQRT (phi k)
   Thus      SQRT (phi k) * h <= SQRT (phi k) * SQRT (phi k)
     or      SQRT (phi k) * h <= phi k

   Let t = phi k, s = SQRT t * h.
   The goal becomes: s <= t.

   Note 0 < k                      by coprime_gt_1, 1 < n
    and 0 < t                      by phi_pos, 0 < k

   Note (ordz k n) divides t       by ZN_coprime_order_divides_phi, 0 < k /\ coprime k n
     so       ordz k n <= t        by DIVIDES_LE, 0 < t
     or         h ** 2 <= t        by given, h ** 2 <= ordz k n
    ==>  SQRT (h ** 2) <= SQRT t   by SQRT_LE
     or              h <= SQRT t   by SQRT_OF_SQ
    ==>     SQRT t * h <= SQRT t * SQRT t    by LESS_MONO_MULT
     or              s <= t        by SQ_SQRT_LE, notation
*)
val ZN_order_condition_property_0 = store_thm(
  "ZN_order_condition_property_0",
  ``!n k. 1 < n /\ coprime k n ==>
   !h. 0 < h /\ h ** 2 <= ordz k n ==> (SQRT (phi k)) * h <= phi k``,
  rpt strip_tac >>
  qabbrev_tac `t = phi k` >>
  qabbrev_tac `s = SQRT t * h` >>
  `0 < k` by metis_tac[coprime_gt_1] >>
  `0 < t` by rw[phi_pos, Abbr`t`] >>
  `(ordz k n) divides t` by rw[ZN_coprime_order_divides_phi, Abbr`t`] >>
  `ordz k n <= t` by rw[DIVIDES_LE] >>
  `h ** 2 <= t` by decide_tac >>
  `SQRT (h ** 2) <= SQRT t` by rw[SQRT_LE] >>
  `h <= SQRT t` by metis_tac[GSYM SQRT_LE, SQRT_OF_SQ] >>
  `s <= SQRT t * SQRT t` by rw[LESS_MONO_MULT, Abbr`s`] >>
  `SQ (SQRT t) <= t` by rw[SQ_SQRT_LE] >>
  decide_tac);

(* Theorem: 1 < n /\ coprime k n /\ (SUC (LOG2 n)) ** 2 <= ordz k n ==>
         SQRT (phi k) * SUC (LOG2 n) <= phi k *)
(* Proof: by ZN_order_condition_property_0 *)
val ZN_order_condition_property_1 = store_thm(
  "ZN_order_condition_property_1",
  ``!n k. 1 < n /\ coprime k n /\ (SUC (LOG2 n)) ** 2 <= ordz k n ==>
         SQRT (phi k) * SUC (LOG2 n) <= phi k``,
  rpt strip_tac >>
  `0 < SUC (LOG2 n)` by decide_tac >>
  metis_tac[ZN_order_condition_property_0]);

(* Theorem: 1 < n /\ coprime k n /\ (ulog n) ** 2 <= ordz k n ==>
            SQRT (phi k) * (ulog n) <= phi k *)
(* Proof:
   Note 0 < ulog n                         by ulog_pos, 1 < n
   Thus SQRT (phi k) * (ulog n) <= phi k   by ZN_order_condition_property_0
*)
val ZN_order_condition_property_2 = store_thm(
  "ZN_order_condition_property_2",
  ``!n k. 1 < n /\ coprime k n /\ (ulog n) ** 2 <= ordz k n ==>
         SQRT (phi k) * (ulog n) <= phi k``,
  metis_tac[ZN_order_condition_property_0, ulog_pos]);

(* Theorem: 1 < n /\ coprime k n /\ (2 * ulog n) ** 2 <= ordz k n ==>
            2 * SQRT (phi k) * (ulog n) <= phi k *)
(* Proof:
   Note 0 < ulog n                             by ulog_pos, 1 < n
     so 0 < 2 * ulog n                         by arithmetic
   Thus SQRT (phi k) * (2 * ulog n) <= phi k   by ZN_order_condition_property_0
     or   2 * SQRT (phi k) * ulog n <= phi k
*)
val ZN_order_condition_property_3 = store_thm(
  "ZN_order_condition_property_3",
  ``!n k. 1 < n /\ coprime k n /\ (2 * ulog n) ** 2 <= ordz k n ==>
             2 * SQRT (phi k) * ulog n <= phi k``,
  rpt strip_tac >>
  `0 < ulog n` by rw[ulog_pos] >>
  `0 < 2 * ulog n` by decide_tac >>
  `2 * SQRT (phi k) * ulog n = SQRT (phi k) * (2 * ulog n)` by decide_tac >>
  metis_tac[ZN_order_condition_property_0]);

(* ------------------------------------------------------------------------- *)
(* AKS Parameter Search                                                      *)
(* ------------------------------------------------------------------------- *)

(* Possible outcomes of search loop *)
val _ = Datatype `param_search_result =
       nice num    (* found an nice of type :num telling prime or composite *)
     | good num    (* found a good of type :num good for AKS *)
     | bad         (* when search exceeds the upper bound *)
`;

(* Note: pseudocode to search for parameter k.

Input: n, m
Output: 1 < k that either (gcd k n <> 1) or (m <= ordz k n)

k <- 2
while k < (2 + (ulog n) * HALF (m ** 2)) {
    if (gcd k n <> 1) exit
    if (m <= ordz k n) exit
    k <- k + 1
}

This version using divides:
k <- 2
while k < (2 + (ulog n) * HALF (m ** 2)) {
    if (k divides n) exit
    if (m <= ordz k n) exit
    k <- k + 1
}
The following theorem guarantees that either exit must occur within the while-loop.

ZN_order_modulus_exists_1
|- !n m. 1 < n /\ 1 < m ==>
   ?k. 1 < k /\ k < 2 + ulog n * HALF (m ** 2) /\ (gcd k n <> 1 \/ m <= ordz k n)

Usually m = (ulog n) ** 2, and m = 1 iff (ulog n = 1), iff n = 2.
In this case, there is no suitable parameter k,
so just make (gcd k n <> 1), e.g. take k = n.

Discussion
----------
The test for order: if (m <= ordz k n) exit
can be modified to: if (m <= k) and (m <= ordz k n) exit
that is, skipping computation of (ordz k n) when k < m.

This is due to ZN_order_lt |- !k n m. 0 < k /\ k < m ==> ordz k n < m
As the proof shows,
     (ordz k n <= phi k)   by ZN_order_upper, (ordz k n) divides (phi k)
and     (phi k <  k)       by phi_lt, 1 < k
 so   ordz k n < k
and if k < m, then ordz k n < m, no hope to have (m <= ordz k n).

This modification is used in the next version, with two loops.
*)

(* Pseudo-Code:
   AKSparam n =
       m <- SQ (ulog n)               // the order to exceed
       c <- 2 + HALF ((ulog n) ** 5)  // the upper limit
       k <- 2                         // search from 2 onwards
       loop:
          if (m <= k) goto next                  // to stage two
          if (n MOD k == 0) return 'nice' k      // a factor k
          k <- k + 1
          goto loop
       next:
          if (c < k) return 'bad'                // not found
          if (n MOD k == 0) return 'nice' k      // a factor k
          // Here k must be coprime to n, by no factor from 2 to k
          if (m <= order(k, n)) return 'good' k  // suitable k
          k <- k + 1
          goto next

   'bad': flag <- F, k <- 0
   'nice': flag <- F, k
   'good': flag <- T, k
*)

(* Define the search for AKS parameter: given n and m, returns k, with cutoff at c. *)
Definition aks_param_search_def:
    aks_param_search n m k c =
      if c < k then bad (* unreachable *)
      else if k divides n then nice k    (* if (k divides n) exit *)
      else if m <= k /\ m <= ordz_compute k n then good k  (* if (m <= ordz k n) exit *)
      else aks_param_search n m (k + 1) c  (* k <- k + 1 *)
Termination WF_REL_TAC `measure (λ(n, m, k, c). c + 1 - k)`
End
(* Check discussion in pseudo-code above for the good check: m <= k /\ m <= ordz_compute k n *)

(* Define the AKS parameter: given n, return k, for better estimate:
   In theory: c = 1 + (ulog n) * (HALF (SQ m))
   In practice:       (ulog n) * (HALF (SQ m)) <= HALF ((ulog n) * (SQ m))
                                                = HALF ((ulog n) ** 5)
   The last one is easier for the estimate: O((ulog n)^5)
   HALF_MULT  |- !m n. n * HALF m <= HALF (n * m)
*)
(*  Originally aks_param_search has
              if m <= 1 then nice n : special since HALF (m ** 2) will be 0
    SQ (ulog n) <= 1, ulog 0 = 0, ulog 1 = 0, ulog 2 = 1, ulog 3 = 2, n <= 2.
    The check is moved to here.
*)
val aks_param_def = Define `
    aks_param n = if n <= 2 then nice n
                  else aks_param_search n (SQ (ulog n)) 2 (1 + HALF ((ulog n) ** 5))
`;

(*
> EVAL ``aks_param 31``;
val it = |- aks_param 31 = good 29: thm
> EVAL ``aks_param 17``;
val it = |- aks_param 17 = nice 17: thm
> EVAL ``aks_param 95477``;
val it = |- aks_param 95477 = good 293: thm
> > EVAL ``MAP aks_param [0; 1; 2]``;
val it = |- MAP aks_param [0; 1; 2] = [nice 0; nice 1; nice 2]: thm
*)

(* Theorem: aks_param n =
            let m = ulog n;
                c = 1 + HALF (m ** 5)
             in if m <= 1 then nice n else aks_param_search n (SQ m) 2 c *)
(* Proof: by aks_param_def, ulog_le_1 *)
val aks_param_alt = store_thm(
  "aks_param_alt",
  ``!n. aks_param n =
       let m = ulog n;
           c = 1 + HALF (m ** 5)
        in if m <= 1 then nice n else aks_param_search n (SQ m) 2 c``,
  rw[aks_param_def, ulog_le_1]);

(* Theorem: aks_param_search n m k c =
            if c < k then bad
            else if k divides n then nice k
            else if m <= k /\ m <= ordz k n then good k
            else aks_param_search n m (k + 1) c *)
(* Proof: by aks_param_search_def, ordz_compute_eqn *)
val aks_param_search_alt = store_thm(
  "aks_param_search_alt",
  ``!n m k c. aks_param_search n m k c =
             if c < k then bad
             else if k divides n then nice k
             else if m <= k /\ m <= ordz k n then good k
             else aks_param_search n m (k + 1) c``,
  rw[Once aks_param_search_def, ordz_compute_eqn]);

(* Theorem: aks_param 0 = nice 0 *)
(* Proof: by aks_param_def, 0 <= 2. *)
val aks_param_0 = store_thm(
  "aks_param_0",
  ``aks_param 0 = nice 0``,
  rw[aks_param_def]);

(* Theorem: aks_param 1 = nice 1 *)
(* Proof: by aks_param_def, 1 <= 2. *)
val aks_param_1 = store_thm(
  "aks_param_1",
  ``aks_param 1 = nice 1``,
  rw[aks_param_def]);

(* Theorem: aks_param 2 = nice 2 *)
(* Proof: by aks_param_def, 2 <= 2. *)
val aks_param_2 = store_thm(
  "aks_param_2",
  ``aks_param 2 = nice 2``,
  rw[aks_param_def]);

(* Theorem: 0 < k /\ (aks_param_search n m k c = bad) ==>
            !j. k <= j /\ j <= c ==> ~(j divides n) /\ (ordz j n < m) *)
(* Proof:
   By aks_param_search_alt, and aks_param_search_ind induction, this is to show:
   (1) k <= j /\ j <= c /\ ~(k divides n) ==> ~(j divides n)
       If k = j, this is trivially true.
       If k <> j, then k < j, true by induction hypothesis, k + 1 <= j
   (2) k <= j /\ j <= c /\ ~(m <= k /\ m <= ordz k n) ==> ~(m <= ordz j n)
       If k = j,
          If m <= k, this is trivially true.
          If ~(m <= k), then k < m,
             By contradiction, suppose m <= ordz k n.
             Then ordz k n < k         by ZN_order_lt, 0 < k, k < m
             Hence there is a contradiction.
       If k <> j, then k < j, true by induction hypothesis, k + 1 <= j
*)
val aks_param_search_bad = store_thm(
  "aks_param_search_bad",
  ``!n m k c. 0 < k /\ (aks_param_search n m k c = bad) ==>
             !j. k <= j /\ j <= c ==> ~(j divides n) /\ (ordz j n < m)``,
  ho_match_mp_tac (theorem "aks_param_search_ind") >>
  (rpt gen_tac >> strip_tac) >>
  simp[Once aks_param_search_alt] >>
  rw[] >| [
    Cases_on `k = j` >-
    rw[] >>
    fs[ordz_compute_eqn],
    Cases_on `k = j` >| [
      Cases_on `m <= k` >-
      rw[] >>
      spose_not_then strip_assume_tac >>
      `ordz k n < m` by fs[ZN_order_lt] >>
      rw[],
      fs[ordz_compute_eqn]
    ]
  ]);

(* Theorem: k <= j /\ j <= c /\ (j divides n \/ m <= ordz j n) ==>
            (k = 0) \/ (aks_param_search n m k c <> bad) *)
(* Proof: by aks_param_search_bad *)
val aks_param_search_not_bad = store_thm(
  "aks_param_search_not_bad",
  ``!n m k j c. k <= j /\ j <= c /\ (j divides n \/ m <= ordz j n) ==>
    (k = 0) \/ (aks_param_search n m k c <> bad)``,
  metis_tac[aks_param_search_bad, NOT_ZERO_LT_ZERO, NOT_LESS_EQUAL]);

(* Theorem: 1 < n /\ 1 < m /\ 1 + HALF (m ** 2) * (ulog n) <= c ==> aks_param_search n m 2 c <> bad *)
(* Proof:
   Note ?k. 1 < k /\ k <= c /\ (k divides n \/ m <= ordz k n)
                                          by ZN_order_modulus_exists_3, 1 < m
    now 1 < k ==> 2 <= k,
    and k divides n ==> nice k <> bad     by aks_param_search_not_bad
     or m <= ordz k n ==> good k <> bad   by aks_param_search_not_bad
*)
val aks_param_search_success = store_thm(
  "aks_param_search_success",
  ``!n m c. 1 < n /\ 1 < m /\ 1 + HALF (m ** 2) * (ulog n) <= c ==>
           aks_param_search n m 2 c <> bad``,
  rpt strip_tac >>
  `?k. 1 < k /\ k <= c /\ (k divides n \/ m <= ordz k n)` by rw[ZN_order_modulus_exists_3] >| [
    `2 <= k /\ 2 <> 0` by decide_tac >>
    metis_tac[aks_param_search_not_bad],
    `2 <= k /\ 2 <> 0` by decide_tac >>
    metis_tac[aks_param_search_not_bad]
  ]);

(* Theorem: (aks_param_search n m k c = bad) /\ d <= c ==> (aks_param_search n m k d = bad) *)
(* Proof: by aks_param_search_def and its induction *)
val aks_param_search_bad_le = store_thm(
  "aks_param_search_bad_le",
  ``!n m k c d. (aks_param_search n m k c = bad) /\ d <= c ==>
                (aks_param_search n m k d = bad)``,
  ho_match_mp_tac (theorem "aks_param_search_ind") >>
  (rpt gen_tac >> strip_tac) >>
  simp[Once aks_param_search_def] >>
  rw[] >-
  rw[Once aks_param_search_def] >>
  rw[Once aks_param_search_def]);

(* Theorem: aks_param n <> bad *)
(* Proof:
   By aks_param_def, this is to show:
      aks_param_search n (SQ (ulog n)) 2 (1 + HALF (ulog n ** 5)) <> bad
   Let m = SQ (ulog n), k = 1 + HALF (m ** 2) * ulog n, c = 1 + HALF (ulog n ** 5).

   If n <= 2, aks_param n = nice <> bad       by aks_param_def
   Otherwise 2 < n, so 1 < m                  by ulog_sq_gt_1

   Claim: k <= c
   Proof: k = 1 + HALF ((SQ (ulog n)) ** 2) * ulog n     by notation
            = 1 + HALF (((ulog n) ** 2) ** 2) * ulog n   by EXP_2
            = 1 + ulog n * HALF ((ulog n) ** 4)          by EXP_EXP_MULT, MULT_COMM
            <= 1 + HALF (ulog n * (ulog n) ** 4)         by HALF_MULT
             = 1 + HALF ((ulog n) ** 5)                  by EXP
             = c                                         by notation

   The result follows             by aks_param_search_success
*)
val aks_param_exists = store_thm(
  "aks_param_exists",
  ``!n. aks_param n <> bad``,
  rw_tac std_ss[aks_param_def] >>
  qabbrev_tac `m = SQ (ulog n)` >>
  qabbrev_tac `k = 1 + HALF (m ** 2) * ulog n` >>
  qabbrev_tac `c = 1 + HALF (ulog n ** 5)` >>
  `1 < n /\ 2 < n` by decide_tac >>
  `1 < m` by fs[ulog_sq_gt_1, Abbr`m`] >>
  `k <= c` by
  (rw[Abbr`k`, Abbr`c`, Abbr`m`] >>
  `(ulog n ** 2) ** 2 = (ulog n) ** 4` by rw[GSYM EXP_EXP_MULT] >>
  metis_tac[HALF_MULT, EXP, DECIDE``SUC 4 = 5``]) >>
  metis_tac[aks_param_search_success]);

(* Theorem: (aks_param_search n m k_ c = nice k) ==>
            (h <= k /\ k divides n /\ (!j. h <= j /\ j < k ==> ~(j divides n))) *)
(* Proof:
   By aks_param_search_def, and aks_param_search_ind induction, this is to show:
   (1) k divides n ==> k divides n, true trivially.
   (2) ~(c < h) /\ ~(h divides n) /\ ~(m <= h /\ m <= ordz_compute h n) /\
       aks_param_search n m (h + 1) c = nice k /\ ~(h divides n) ==> h <= k
       Note !j. k + 1 <= j /\ j < k ==> ~(j divides n)    by induction hypothesis
       Take j = k + 1, then h + 1 <= k + 1, or h <= k.
   (3) h <= j /\ j < k /\ ~(h divides n) ==> ~(j divides n)
       If h = j, this is trivially true.
       If h <> j, then h < j, true by induction hypothesis, h + 1 <= j
*)
val aks_param_search_nice = store_thm(
  "aks_param_search_nice",
  ``!n m h c k. (aks_param_search n m h c = nice k) ==>
        (h <= k /\ k divides n /\ (!j. h <= j /\ j < k ==> ~(j divides n)))``,
  ho_match_mp_tac (theorem "aks_param_search_ind") >>
  (rpt gen_tac >> strip_tac) >>
  simp[Once aks_param_search_def] >>
  rw[] >-
  rw[] >-
  fs[] >>
  (Cases_on `h = j` >> fs[]));

(* Theorem: 0 < n /\ (aks_param_search n m 2 c = nice k) ==> k <= n *)
(* Proof:
   By contradiction, suppose ~(k <= n), or n < k.
   Then k divides n                by aks_param_search_nice
   But k divides n ==> k <= n      by DIVIDES_LE, 0 < n
   This is a contradiction.
*)
val aks_param_search_nice_le = store_thm(
  "aks_param_search_nice_le",
  ``!n m k c. 0 < n /\ (aks_param_search n m 2 c = nice k) ==> k <= n``,
  metis_tac[aks_param_search_nice, DIVIDES_LE]);

(* Theorem: (aks_param_search n m k c = nice j) ==> j <= c *)
(* Proof:
   By induction from aks_param_search_def, noting cases.
   The only case to give (nice j) is:
       ~(c < k) /\ k divides n
       giving (nice k), so j = k, and k <= c        by ~(c < k)
   Otherwise,
           aks_param_search n m k c = nice j
       <=> aks_param_search n m (k + 1) c = nice j  by aks_param_search_def
       ==> j <= c                                   by induction hypothesis
*)
val aks_param_search_nice_bound = store_thm(
  "aks_param_search_nice_bound",
  ``!n m k c j. (aks_param_search n m k c = nice j) ==> j <= c``,
  ho_match_mp_tac (theorem "aks_param_search_ind") >>
  rw[] >>
  Cases_on `c < k` >-
  fs[Once aks_param_search_def] >>
  Cases_on `k divides n` >-
  fs[Once aks_param_search_def] >>
  Cases_on `m <= k /\ m <= ordz_compute k n` >-
  fs[Once aks_param_search_def] >>
  fs[Once aks_param_search_def]);

(* Theorem: (aks_param_search n m k c = nice j) ==> j divides n *)
(* Proof: by aks_param_search_nice *)
val aks_param_search_nice_factor = store_thm(
  "aks_param_search_nice_factor",
  ``!n m k c j. (aks_param_search n m k c = nice j) ==> j divides n``,
  metis_tac[aks_param_search_nice, NOT_LESS]);

(* Theorem: (aks_param_search n m 2 c = nice k) ==> !j. 1 < j /\ j < k ==> coprime j n *)
(* Proof:
   By contradiction, suppose ?j. 1 < j /\ j < k, but ~(coprime j n).
   Note 2 <= k /\ k divides n /\
        (!j. 2 <= j /\ j < k ==> ~(j divides n))    by aks_param_search_nice

   Let d = gcd j n, then d <> 1.
   Note j <> 0                       by 1 < j
     so d <> 0                       by GCD_EQ_0
   Thus 2 <= d                       by d <> 0, d <> 1
    Now d divides j /\ d divides n   by GCD_PROPERTY
    ==> d <= j                       by DIVIDES_LE, 0 < j
     or d < k                        by LESS_EQ_LESS_TRANS
    ==> ~(d divides n)               by implication
    This contradicts d divides n.
*)
val aks_param_search_nice_coprime_all = store_thm(
  "aks_param_search_nice_coprime_all",
  ``!n m k c. (aks_param_search n m 2 c = nice k) ==> !j. 1 < j /\ j < k ==> coprime j n``,
  spose_not_then strip_assume_tac >>
  `2 <= k /\ k divides n /\ !j. 2 <= j /\ j < k ==> ~(j divides n)` by metis_tac[aks_param_search_nice] >>
  `2 <= j` by decide_tac >>
  qabbrev_tac `d = gcd j n` >>
  `j <> 0 /\ 0 < j` by decide_tac >>
  `d <> 0` by metis_tac[GCD_EQ_0] >>
  `2 <= d` by decide_tac >>
  `d divides j /\ d divides n` by metis_tac[GCD_PROPERTY] >>
  `d <= j` by rw[DIVIDES_LE] >>
  metis_tac[LESS_EQ_LESS_TRANS]);

(* Theorem: (aks_param_search n m h c = good k) ==>
            h <= k /\ m <= ordz k n /\ !j. h <= j /\ j <= k ==> ~(j divides n) *)
(* Proof:
   By aks_param_search_alt, and aks_param_search_ind induction, this is to show:
   (1) h <= j /\ j <= h /\ ~(h divides n) ==> ~(j divides n)
       Note j = h, hence true                   by h <= j /\ j <= h
   (2) ~(c < h) /\ ~(m <= h /\ m <= ordz h n) /\ (aks_param_search n m (h + 1) c = good k) /\ ~(h divides n) ==> h <= k
       Note !j. h + 1 <= j /\ m <= ordz j n     by induction hypothesis, ordz_compute_eqn
       Take j = k + 1, then h + 1 <= k + 1, or h <= k.
   (3) ~(c < h) /\ ~(m <= h /\ m <= ordz h n) /\ (aks_param_search n m (h + 1) c = good k) /\ ~(h divides n) ==> m <= ordz k n, true trivially.
       True                                     by induction hypothesis, ordz_compute_eqn
   (4) h <= j /\ j <= k /\ ~(h divides n) ==> ~(j divides n)
       If h = j, this is trivially true.
       If h <> j, then h < j, true by induction hypothesis, h + 1 <= j, ordz_compute_eqn
*)
val aks_param_search_good = store_thm(
  "aks_param_search_good",
  ``!n m h c k. (aks_param_search n m h c = good k) ==>
    h <= k /\ m <= ordz k n /\ !j. h <= j /\ j <= k ==> ~(j divides n)``,
  ho_match_mp_tac (theorem "aks_param_search_ind") >>
  (rpt gen_tac >> strip_tac) >>
  simp[Once aks_param_search_alt] >>
  rw[] >| [
    `j = h` by decide_tac >>
    rw[],
    fs[ordz_compute_eqn],
    fs[ordz_compute_eqn],
    (Cases_on `h = j` >> fs[ordz_compute_eqn])
  ]);

(* Theorem: 1 < n /\ (aks_param_search n m 2 c = good k) ==> k < n *)
(* Proof:
   By contradiction, suppose ~(k < n), or n <= k.
   Note n <> 1 /\ 2 <= n                          by 1 < n
    and !j. 2 <= j /\ j <= k ==> ~(j divides n)   by aks_param_search_good
   Putting j = n, this gives  ~(n divides n)      by implication
   This contradicts n divides n                   by DIVIDES_REFL
*)
val aks_param_search_good_lt = store_thm(
  "aks_param_search_good_lt",
  ``!n m k c. 1 < n /\ (aks_param_search n m 2 c = good k) ==> k < n``,
  spose_not_then strip_assume_tac >>
  `n <> 1 /\ 2 <= n /\ n <= k` by decide_tac >>
  metis_tac[aks_param_search_good, DIVIDES_REFL]);

(* Theorem: (aks_param_search n m k c = good j) ==> j <= c *)
(* Proof:
   By induction from aks_param_search_def, noting cases.
   The only case to give (good j) is:
       ~(c < k) /\ ~(k divides n) /\ m <= k /\ m <= ordz_compute k n
       giving (good k), so j = k, and k <= c        by ~(c < k)
   Otherwise,
           aks_param_search n m k c = good j
       <=> aks_param_search n m (k + 1) c = good j  by aks_param_search_def
       ==> j <= c                                   by induction hypothesis
*)
val aks_param_search_good_bound = store_thm(
  "aks_param_search_good_bound",
  ``!n m k c j. (aks_param_search n m k c = good j) ==> j <= c``,
  ho_match_mp_tac (theorem "aks_param_search_ind") >>
  rw[] >>
  Cases_on `c < k` >-
  fs[Once aks_param_search_def] >>
  Cases_on `k divides n` >-
  fs[Once aks_param_search_def] >>
  Cases_on `m <= k /\ m <= ordz_compute k n` >-
  fs[Once aks_param_search_def] >>
  fs[Once aks_param_search_def]);

(* Theorem: (aks_param_search n m 2 c = good k) ==>
            1 < k /\ m <= ordz k n /\ !j. 1 < j /\ j <= k ==> coprime j n *)
(* Proof
   Note 2 <= k /\ m <= ordz k n /\ !j. 2 <= j /\ j <= k ==> ~(j divides n)  by aks_param_search_good
   Thus to show:
   (1) 1 < k, true                       by 2 <= k.
   (2) m <= ordz k n, true               trivially.
   (3) 1 < j /\ j <= k ==> coprime j n
       Let d = gcd j n, then d <> 1.
       Note j <> 0                       by 1 < j
         so d <> 0                       by GCD_EQ_0
       Thus 2 <= d                       by d <> 0, d <> 1
        Now d divides j /\ d divides n   by GCD_PROPERTY
        ==> d <= j                       by DIVIDES_LE, 0 < j
         or d <= k                       by LESS_EQ_TRANS
        ==> ~(d divides n)               by implication
       This contradicts d divides n.
*)
val aks_param_search_good_coprime_all = store_thm(
  "aks_param_search_good_coprime_all",
  ``!n m k c. (aks_param_search n m 2 c = good k) ==>
    1 < k /\ m <= ordz k n /\ !j. 1 < j /\ j <= k ==> coprime j n``,
  rpt strip_tac >-
  metis_tac[aks_param_search_good, DECIDE``!n. 1 < n <=> 2 <= n``] >-
  metis_tac[aks_param_search_good] >>
  spose_not_then strip_assume_tac >>
  `2 <= k /\ !j. 2 <= j /\ j <= k ==> ~(j divides n)` by metis_tac[aks_param_search_good] >>
  qabbrev_tac `d = gcd j n` >>
  `j <> 0 /\ 0 < j` by decide_tac >>
  `d <> 0` by metis_tac[GCD_EQ_0] >>
  `2 <= d` by decide_tac >>
  `d divides j /\ d divides n` by metis_tac[GCD_PROPERTY] >>
  `d <= j` by rw[DIVIDES_LE] >>
  metis_tac[LESS_EQ_TRANS]);

(* Theorem: 1 < n /\ (aks_param n = nice k) ==> 1 < k /\ k divides n /\ !j. 1 < j /\ j < k ==> ~(j divides n) *)
(* Proof:
   If n = 2,
      Then aks_param 2 = nice 2     by aks_param_2
        or k = 2                    by nice k = nice 2
        so 2 divides 2              by DIVIDES_REFL
       and !j. 1 < j /\ j < 2 ==> ~(j divides n), as no j will satisfy the premise.
   If n <> 2,
      Then 2 < n                    by n <> 2, 1 < n
      Let m = SQ (ulog n), c = 1 + HALF ((ulog n) ** 5).
      Note aks_param_search n m 2 c
         = aks_param n              by aks_param_def, 2 < n
         = nice k                   by given
       ==> 2 <= k /\ k divides n /\ !j. 2 <= j /\ j < k ==> ~(j divides n)
                                    by aks_param_search_nice
        or 1 < k /\ k divides n /\ !j. 1 < j /\ j < k ==> ~(j divides n)
                                    by arithmetic
*)
val aks_param_nice = store_thm(
  "aks_param_nice",
  ``!n k. 1 < n /\ (aks_param n = nice k) ==>
         1 < k /\ k divides n /\ !j. 1 < j /\ j < k ==> ~(j divides n)``,
  ntac 3 strip_tac >>
  Cases_on `n = 2` >| [
    `nice 2 = nice k` by metis_tac[aks_param_2] >>
    `k = 2` by rw[] >>
    rw[],
    qabbrev_tac `m = SQ (ulog n)` >>
    qabbrev_tac `c = 1 + HALF ((ulog n) ** 5)` >>
    `~(n <= 2)` by decide_tac >>
    `aks_param_search n m 2 c = nice k` by metis_tac[aks_param_def] >>
    `2 <= k /\ k divides n /\ !j. 2 <= j /\ j < k ==> ~(j divides n)` by metis_tac[aks_param_search_nice] >>
    rw[]
  ]);

(* Theorem: (aks_param n = nice k) ==>
            (if n <= 1 then (k = n) else 1 < k) /\
            k divides n /\ !j. 1 < j /\ j < k ==> ~(j divides n) *)
(* Proof:
   If n = 0,
      Then aks_param 0 = nice 0     by aks_param_0
       and 0 divides 0, hence true.
   If n = 1,
      Then aks_param 1 = nice 1     by aks_param_1
       and 1 divides 1, hence true.
   Otherwise 1 < n, true            by aks_param_nice
*)
val aks_param_nice_alt = store_thm(
  "aks_param_nice_alt",
  ``!n k. (aks_param n = nice k) ==>
         (if n <= 1 then (k = n) else 1 < k) /\
         k divides n /\ !j. 1 < j /\ j < k ==> ~(j divides n)``,
  ntac 3 strip_tac >>
  (Cases_on `n <= 1` >> simp[]) >| [
    `(n = 0) \/ (n = 1)` by decide_tac >-
    fs[aks_param_0] >>
    fs[aks_param_1],
    metis_tac[aks_param_nice, NOT_LESS_EQUAL]
  ]);

(* Theorem: (aks_param n = nice k) ==> k <= n *)
(* Proof:
   Let m = SQ (ulog n), c = 2 + HALF ((ulog n) ** 5).
   If n <= 2,
      aks_param n = nice n       by aks_param_def
      so k = n, k <= n is true trivially.
   Otherwise 2 < n,
   Note aks_param_search n m 2 c
      = aks_param n              by aks_param_def, 2 < n
      = nice k                   by given
   Thus k <= n                   by aks_param_search_nice_le, 0 < n
*)
val aks_param_nice_le = store_thm(
  "aks_param_nice_le",
  ``!n k. (aks_param n = nice k) ==> k <= n``,
  rw[aks_param_def] >>
  `0 < n` by decide_tac >>
  metis_tac[aks_param_search_nice_le]);

(* Theorem: 2 < n /\ (aks_param n = nice k) ==> k <= 1 + HALF (ulog n ** 5) *)
(* Proof:
   Let c = 1 + HALF (ulog n ** 5).
   Note aks_param n = nice k
    <=> aks_param_search n (SQ (ulog n)) 2 c = nice k    by aks_param_def, 2 < n
    ==> k <= c                                           by aks_param_search_nice_bound
*)
val aks_param_nice_bound = store_thm(
  "aks_param_nice_bound",
  ``!n k. 2 < n /\ (aks_param n = nice k) ==> k <= 1 + HALF (ulog n ** 5)``,
  metis_tac[aks_param_def, aks_param_search_nice_bound, NOT_LESS]);

(* Theorem: (aks_param n = nice k) ==> !j. 1 < j /\ j < k ==> coprime j n *)
(* Proof:
   If n <= 2,
      Then aks_param n = nice n         by aks_param_def
      so k = n,
      and n = 0, or n = 1, or n = 2     by n <= 2
      and there is no j such that 1 < j /\ j < k.
   If ~(n <= 2),
      Then 2 < n                        by n <> 2, 1 < n
      Let m = SQ (ulog n), c = 1 + HALF ((ulog n) ** 5).
      Then aks_param n = nice k
       <=> aks_param_search n m 2 c = nice k
                                        by aks_param_def, 2 < n
      The result follows                by aks_param_search_nice_coprime_all
*)
val aks_param_nice_coprime_all = store_thm(
  "aks_param_nice_coprime_all",
  ``!n k. (aks_param n = nice k) ==> !j. 1 < j /\ j < k ==> coprime j n``,
  rw_tac std_ss[aks_param_def] >-
  decide_tac >>
  metis_tac[aks_param_search_nice_coprime_all]);

(* Theorem: 1 < n /\ (aks_param n = nice k) ==> (prime n <=> (k = n)) *)
(* Proof:
   If part: prime n ==> k = n
      Note 1 < k /\ k divides n              by aks_param_nice
        or n <> 1 /\ k <> 1                  by 1 < n, 1 < k
      Thus k = n                             by prime_def, k divides n, prime n.
   Only-if part: k = n ==> prime n
      Note !j. 1 < j /\ j < n ==> ~(j divides n)  by aks_param_nice, k = n
       ==> prime n                                by prime_iff_no_proper_factor
*)
val aks_param_nice_for_prime = store_thm(
  "aks_param_nice_for_prime",
  ``!n k. 1 < n /\ (aks_param n = nice k) ==> (prime n <=> (k = n))``,
  rw_tac std_ss[EQ_IMP_THM] >-
  metis_tac[aks_param_nice, prime_def, LESS_NOT_EQ] >>
  rw[aks_param_nice, prime_iff_no_proper_factor]);

(* Theorem: (aks_param n = good k) ==>
            1 < k /\ SQ (ulog n) <= ordz k n /\ !j. 1 < j /\ j <= k ==> ~(j divides n) *)
(* Proof:
   If n <= 2, aks_param n = nice k <> good k.
   Otherwise,
   Let m = SQ (ulog n), c = 1 + HALF ((ulog n) ** 5).
   Note aks_param_search n m 2 c
      = aks_param n              by aks_param_def, 2 < n
      = good k                   by given
   Thus 2 <= k /\ m <= ordz k n /\ !j. 2 <= j /\ j <= k ==> ~(j divides n)
                                 by aks_param_search_good
     or 1 < k /\ m <= ordz k n /\ !j. 1 < j /\ j <= k ==> ~(j divides n)
                                 by arithmetic
*)
val aks_param_good = store_thm(
  "aks_param_good",
  ``!n k. (aks_param n = good k) ==>
         1 < k /\ SQ (ulog n) <= ordz k n /\ !j. 1 < j /\ j <= k ==> ~(j divides n)``,
  ntac 3 strip_tac >>
  qabbrev_tac `m = SQ (ulog n)` >>
  qabbrev_tac `c = 1 + HALF ((ulog n) ** 5)` >>
  Cases_on `n <= 2` >-
  fs[aks_param_def] >>
  `aks_param_search n m 2 c = good k` by metis_tac[aks_param_def] >>
  `2 <= k /\ m <= ordz k n /\ !j. 2 <= j /\ j <= k ==> ~(j divides n)` by metis_tac[aks_param_search_good] >>
  rw[]);

(* Theorem: (aks_param n = good k) ==> k < n *)
(* Proof: by aks_param_def, aks_param_search_good_lt *)
val aks_param_good_lt = store_thm(
  "aks_param_good_lt",
  ``!n k. (aks_param n = good k) ==> k < n``,
  rw[aks_param_def] >>
  `1 < n` by decide_tac >>
  metis_tac[aks_param_search_good_lt]);

(* Theorem: (aks_param n = good k) ==> k <= 1 + HALF (ulog n ** 5) *)
(* Proof:
   If n <= 2, aks_param n = nice n <> good k   by aks_param_def
   Otherwise,
   Let c = 1 + HALF (ulog n ** 5).
       aks_param n = good k
   <=> aks_param_search n (SQ (ulog n)) 2 c = good k    by aks_param_def, 2 < n
   ==> k <= c                                           by aks_param_search_good_bound
*)
val aks_param_good_bound = store_thm(
  "aks_param_good_bound",
  ``!n k. (aks_param n = good k) ==> k <= 1 + HALF (ulog n ** 5)``,
  rw_tac std_ss[aks_param_def] >>
  metis_tac[aks_param_search_good_bound]);

(* Theorem: (aks_param n = good k) ==> 1 < k /\ SQ (ulog n) <= ordz k n /\ !j. 1 < j /\ j <= k ==> coprime j n *)
(* Proof: by aks_param_def, aks_param_search_good_coprime_all *)
val aks_param_good_coprime_all = store_thm(
  "aks_param_good_coprime_all",
  ``!n k. (aks_param n = good k) ==> !j. 1 < j /\ j <= k ==> coprime j n``,
  rw_tac std_ss[aks_param_def] >>
  metis_tac[aks_param_search_good_coprime_all]);

(* Theorem: (aks_param n = good k) ==> 1 < n /\ 1 < k /\ k < n *)
(* Proof:
   Claim: 1 < n
   Proof: By contradiction, suppose ~(1 < n).
          Then n = 0 \/ n = 1                  by arithmetic
           But aks_param n = nice n <> good k  by aks_param_0, aks_param_1

   Thus 1 < n                           by Claim
     so 1 < k                           by aks_param_good
    and k < n                           by aks_param_good_lt, 1 < n
*)
val aks_param_good_range = store_thm(
  "aks_param_good_range",
  ``!n k. (aks_param n = good k) ==> 1 < n /\ 1 < k /\ k < n``,
  ntac 3 strip_tac >>
  `1 < n` by
  (spose_not_then strip_assume_tac >>
  `aks_param n = nice n` by metis_tac[aks_param_0, aks_param_1, DECIDE``~(1 < n) <=> (n = 0) \/ (n = 1)``] >>
  `!n k. good n <> nice k` by rw[] >>
  metis_tac[]) >>
  metis_tac[aks_param_good, aks_param_good_lt]);

(* Theorem: (aks_param n = good k) ==> 1 < k /\ k < n /\ coprime k n /\ (ulog n) ** 2 <= ordz k n *)
(* Proof: by aks_param_good, aks_param_good_range, aks_param_good_coprime_all *)
val aks_param_good_coprime_order = store_thm(
  "aks_param_good_coprime_order",
  ``!n k. (aks_param n = good k) ==> 1 < k /\ k < n /\ coprime k n /\ (ulog n) ** 2 <= ordz k n``,
  metis_tac[aks_param_good_range, aks_param_good, EXP_2, aks_param_good_coprime_all, LESS_EQ_REFL]);

(* ------------------------------------------------------------------------- *)
(* AKS parameter search simplified                                           *)
(* ------------------------------------------------------------------------- *)
(*
val aks_param_search_def = tDefine "aks_param_search"  `
    aks_param_search n m k c =
           if c < k then bad (* unreachable *)
      else if k divides n then nice k    (* if (k divides n) exit *)
      else if m <= k /\ m <= ordz_compute k n then good k  (* if (m <= ordz k n) exit *)
      else aks_param_search n m (k + 1) c  (* k <- k + 1 *)
`(WF_REL_TAC `measure (\(n, m, k, c). c + 1 - k)`);
val aks_param_def = Define `
    aks_param n = if n <= 2 then nice n
                  else aks_param_search n (SQ (ulog n)) 2 (1 + HALF ((ulog n) ** 5))
`;
*)
(* Note: the simplified version is better for analysis:
   (1) Have k = 0 check, so that k divides n is replaced by (n MOD k = 0).
   (2) Have c <= k, which replaces the calling c by incrementing 1.
   (3) Skip m <= k, which is an optimisation by ZN_order_le: ordz k n <= k when 0 < k.
*)
(* Define the parameter seek loop *)
(*
val param_seek_def = tDefine "param_seek" `
  param_seek m c n k =
       if k = 0 then bad
  else if c <= k then bad
  else if n MOD k = 0 then nice k (* same as k divides n when k <> 0 *)
  else if m <= ordz k n then good k
  else param_seek m c n (k + 1)
`(WF_REL_TAC `measure (\(m,c,n,k). c - k)`);
*)
(* Skip k = 0 check, as caller uses k = 2 *)
Definition param_seek_def:
  param_seek m c n k =
       if c <= k then bad
  else if n MOD k = 0 then nice k (* same as k divides n when k <> 0 *)
  else if m <= ordz k n then good k
  else param_seek m c n (k + 1)
Termination WF_REL_TAC `measure (λ(m,c,n,k). c - k)`
End

(* Define the caller to parameter seek loop *)
val param_def = Define`
    param n = if n <= 2 then nice n
                  else param_seek (SQ (ulog n)) (2 + HALF ((ulog n) ** 5)) n 2
`;
(* Note: 2 + HALF ((ulog n) ** 5) is one more than aks_param *)

(*
> EVAL ``param 31``;
val it = |- param 31 = good 29: thm
*)

(* Theorem: param n = let m = ulog n;
                             c = 2 + HALF (m ** 5)
                          in if m <= 1 then nice n else param_seek (SQ m) c n 2 *)
(* Proof: by param_def, ulog_le_1 *)
val param_alt = store_thm(
  "param_alt",
  ``!n. param n =
          let m = ulog n;
              c = 2 + HALF (m ** 5)
           in if m <= 1 then nice n else param_seek (SQ m) c n 2``,
  rw[param_def, ulog_le_1]);

(* Theorem: 0 < k /\ k <= c ==> (param_seek m c n k = aks_param_search n m k c) *)
(* Proof:
   Note k divides n <=> (n MOD k = 0)    by DIVIDES_MOD_0, 0 < k.
   By induction from param_seek_def, to show successive cases:
   (1) c <= k, means c - 1 < k           by 0 < c
         param_seek m c n k
       = bad                             by param_seek_def
       = aks_param_search n m k (c - 1)  by aks_param_search_def, c - 1 < k.
   (2) n MOD k = 0
       Note k divides n                  by DIVIDES_MOD_0, 0 < k
         param_seek m c n k
       = nice k                          by param_seek_def
       = aks_param_search n m k (c - 1)  by aks_param_search_def, k divides n
   (3) m <= ordz k n
       Note ~(k divides n)               by DIVIDES_MOD_0, 0 < k
       Note ordz k n <= k                by ZN_order_le, 0 < k
         so m <= k                       by LESS_EQ_TRANS
         param_seek m c n k
       = good k                          by param_seek_def
       = aks_param_search n m k (c - 1)  by aks_param_search_alt, m <= k /\ m <= ordz k n
   (4) Otherwise,
       Note k <= c - 1                   by ~(c <= k), or k < c
         or ~(c - 1 < k)
         param_seek m c n k
       = param_seek m c n (k + 1)              by param_seek_def
       = aks_param_search n m (k + 1) (c - 1)  by induction hypothesis
       = aks_param_search n m k (c - 1)        by aks_param_search_alt, ~(c - 1 < k)
*)
val param_seek_thm = store_thm(
  "param_seek_thm",
  ``!m c n k. 0 < k /\ k <= c ==> (param_seek m c n k = aks_param_search n m k (c - 1))``,
  ho_match_mp_tac (theorem "param_seek_ind") >>
  rw[] >>
  `k divides n <=> (n MOD k = 0)` by rw[DIVIDES_MOD_0] >>
  rw[Once param_seek_def] >-
  rw[Once aks_param_search_def] >-
  rw[Once aks_param_search_alt] >-
 (`ordz k n <= k` by rw[ZN_order_le] >>
  `m <= k` by decide_tac >>
  rw[Once aks_param_search_alt]) >>
  `~(c - 1 < k)` by decide_tac >>
  metis_tac[aks_param_search_alt]);

(* Theorem: param n = aks_param n *)
(* Proof:
   If n <= 2, param n = nice n = aks_param n                  by param_def, aks_param_def
   Otherwise,
     param n
   = param_seek (SQ (ulog n)) (2 + HALF (ulog n ** 5)) n 2    by param_def
   = aks_param_search n m 2 (1 + HALF (ulog n ** 5)           by param_seek_thm, 0 < 2
   = aks_param n                                              by aks_param_def
*)
val param_eqn = store_thm(
  "param_eqn",
  ``!n. param n = aks_param n``,
  rw[param_def, param_seek_thm, aks_param_def]);

(* Obtain theorems *)

val param_0 = save_thm("param_0", aks_param_0 |> SIMP_RULE bool_ss [GSYM param_eqn]);
(* val param_0 = |- param 0 = nice 0: thm *)

val param_1 = save_thm("param_1", aks_param_1 |> SIMP_RULE bool_ss [GSYM param_eqn]);
(* val param_1 = |- param 1 = nice 1: thm *)

val param_2 = save_thm("param_2", aks_param_2 |> SIMP_RULE bool_ss [GSYM param_eqn]);
(* val param_2 = |- param 2 = nice 2: thm *)

val param_nice_bound = save_thm("param_nice_bound",
    aks_param_nice_bound |> SIMP_RULE bool_ss [GSYM param_eqn]);
(*
val param_nice_bound =
   |- !n k. 2 < n /\ (param n = nice k) ==> k <= 1 + HALF (ulog n ** 5): thm
*)

val param_good_bound = save_thm("param_good_bound",
    aks_param_good_bound |> SIMP_RULE bool_ss [GSYM param_eqn]);
(*
val param_good_bound =
   |- !n k. (param n = good k) ==> k <= 1 + HALF (ulog n ** 5): thm
*)

val param_exists = save_thm("param_exists",
    aks_param_exists |> SIMP_RULE bool_ss [GSYM param_eqn]);
(*
val param_exists = |- !n. param n <> bad: thm
*)

val param_nice_for_prime = save_thm("param_nice_for_prime",
    aks_param_nice_for_prime |> SIMP_RULE bool_ss [GSYM param_eqn]);
(*
val param_nice_for_prime = |- !n k. 1 < n /\ (param n = nice k) ==> (prime n <=> (k = n)): thm
*)

(* The following is absent:
val param_good_for_prime = save_thm("param_good_for_prime",
    aks_param_good_for_prime |> SIMP_RULE bool_ss [GSYM param_eqn]);
giving
val param_good_for_prime =
   |- !n k. (param n = good k) /\ power_free n ==>
          (prime n <=> poly_intro_checks n k (SQRT (phi k) * ulog n)): thm

This is because:
(1) aks_param_good_for_prime is in AKSclean, due to poly_intro_checks.
(2) (param n) corresponds to poly_intro_checks n k k, not the range indicated.
*)

val param_good_range = save_thm("param_good_range",
    aks_param_good_range |> SIMP_RULE bool_ss [GSYM param_eqn]);
(*
val param_good_range =
   |- !n k. (param n = good k) ==> 1 < n /\ 1 < k /\ k < n: thm
*)


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
