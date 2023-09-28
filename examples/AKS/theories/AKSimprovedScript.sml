(* ------------------------------------------------------------------------- *)
(* AKS Bounds Improvement                                                    *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "AKSimproved";

(* ------------------------------------------------------------------------- *)

open jcLib;

(* Get dependent theories local *)
open AKSrevisedTheory;
open AKStheoremTheory;
open AKSmapsTheory;
open AKSsetsTheory;
open AKSintroTheory;
open AKSshiftTheory;

(* Get polynomial theory of Ring *)
open polynomialTheory polyWeakTheory polyRingTheory polyFieldTheory;
open polyDivisionTheory polyBinomialTheory polyEvalTheory;

open polyMonicTheory;

open polyFieldDivisionTheory;
open polyFieldModuloTheory;
open polyRingModuloTheory;
open polyIrreducibleTheory;
open polyMapTheory;

open polyRootTheory;
open polyDividesTheory;
open polyProductTheory;
open polyGCDTheory;

open monoidTheory groupTheory ringTheory fieldTheory;

open subgroupTheory;
open groupOrderTheory;
open monoidOrderTheory;
open fieldMapTheory;
open ringUnitTheory;

(* open dependent theories *)
open prim_recTheory pred_setTheory listTheory arithmeticTheory;

(* Get dependent theories in lib *)
open helperNumTheory helperSetTheory helperListTheory;
open helperFunctionTheory;

open dividesTheory gcdTheory;

open triangleTheory;
open binomialTheory;

open ringBinomialTheory;
open ringDividesTheory;

open monoidInstancesTheory;
open groupInstancesTheory;
open ringInstancesTheory;
open fieldInstancesTheory;
open groupOrderTheory;
open monoidOrderTheory;

open groupCyclicTheory;

open fieldBinomialTheory;

open fieldIdealTheory;

open fieldOrderTheory;

open fieldProductTheory;

open logPowerTheory;
open computeBasicTheory;
open computeOrderTheory;
open computePolyTheory;
open computeRingTheory;
open computeParamTheory;
open computeAKSTheory;

(* (* val _ = load "ffUnityTheory"; *) *)
open ffBasicTheory;
open ffAdvancedTheory;
open ffPolyTheory;
open ffUnityTheory;
open ffCycloTheory;

open ffExistTheory;
open ffConjugateTheory;
open ffMasterTheory;
open ffMinimalTheory;

(* (* val _ = load "GaussTheory"; *) *)
open EulerTheory;
open GaussTheory;


(* ------------------------------------------------------------------------- *)
(* AKS Bounds Improvement Documentation                                      *)
(* ------------------------------------------------------------------------- *)
(* Datatype and Overloading:
*)
(* Definitions and Theorems (# are exported):

   Improve Bounds for AKS Theorem:
   AKS_main_thm_0b     |- !r k z. FiniteField r /\ (CARD R = char r) /\ 1 < ordz k (char r) /\
                                  mifactor z (unity k) /\ (forderz X = k) ==>
                              !n. 1 < k /\ char r divides n /\ k < char r /\
                                  SUC (LOG2 n) ** 2 <= ordz k n /\
                                  poly_intro_range r k n (SQRT (phi k) * SUC (LOG2 n)) ==>
                                  perfect_power n (char r)
   AKS_main_thm_0b_alt |- !r k z. FiniteField r /\ (CARD R = char r) /\ 1 < ordz k (char r) /\
                                  mifactor z (unity k) /\ 1 < deg z /\ (forderz X = k) ==>
                              !n. char r divides n /\ k < char r /\
                                  SUC (LOG2 n) ** 2 <= ordz k n /\
                                  poly_intro_range r k n (SQRT (phi k) * SUC (LOG2 n)) ==>
                                  perfect_power n (char r)
   AKS_main_thm_1b     |- !r k z. FiniteField r /\ (CARD R = char r) /\ 1 < ordz k (char r) /\
                                  mifactor z (unity k) /\ (forderz X = k) ==>
                              !n. 0 < n /\ 0 < k /\ char r divides n /\ k < char r /\
                                  SUC (LOG2 n) ** 2 <= ordz k n /\
                                  poly_intro_range r k n (SQRT (phi k) * SUC (LOG2 n)) ==>
                                  perfect_power n (char r)
   AKS_main_thm_2b     |- !r. FiniteField r /\ (CARD R = char r) ==>
                          !k n. 0 < k /\ 1 < ordz k (char r) /\ char r divides n /\
                                k < char r /\ SUC (LOG2 n) ** 2 <= ordz k n /\
                                poly_intro_range r k n (SQRT (phi k) * SUC (LOG2 n)) ==>
                                perfect_power n (char r)
   AKS_main_thm_3b     |- !n k. 1 < n /\ 0 < k /\ (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\
                                SUC (LOG2 n) ** 2 <= ordz k n /\
                                poly_intro_range (ZN n) k n (SQRT (phi k) * SUC (LOG2 n)) ==>
                            ?p. prime p /\ perfect_power n p
   AKS_main_thm_7b     |- !n. prime n <=> power_free n /\
                          ?k. 0 < k /\ (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                              SUC (LOG2 n) ** 2 <= ordz k n /\
                              (k < n ==> poly_intro_range (ZN n) k n (SQRT (phi k) * SUC (LOG2 n)))
   AKS_main_thm_8b     |- !n. prime n <=> power_free n /\
                          ?k. 0 < k /\ (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                              SUC (LOG2 n) ** 2 <= ordz k n /\
                              (k < n ==> poly_intro_checks n k (SQRT (phi k) * SUC (LOG2 n)))

   AKS Theorems improved using upper logarithm:
   AKS_main_ulog_0b    |- !r k z. FiniteField r /\ (CARD R = char r) /\ 1 < ordz k (char r) /\
                                  mifactor z (unity k) /\ forderz X = k ==>
                          !n. 1 < k /\ 0 < n /\ char r divides n /\ k < char r /\
                              ulog n ** 2 <= ordz k n /\
                              poly_intro_range r k n (SQRT (phi k) * ulog n) ==>
                              perfect_power n (char r)
   AKS_main_ulog_0b_alt|- !r k z. FiniteField r /\ (CARD R = char r) /\ 1 < ordz k (char r) /\
                                  mifactor z (unity k) /\ 1 < deg z /\ forderz X = k ==>
                          !n. 0 < n /\ char r divides n /\ k < char r /\
                              ulog n ** 2 <= ordz k n /\
                              poly_intro_range r k n (SQRT (phi k) * ulog n) ==>
                              perfect_power n (char r)
   AKS_main_ulog_1b    |- !r k z. FiniteField r /\ (CARD R = char r) /\ 1 < ordz k (char r) /\
                                  mifactor z (unity k) /\ forderz X = k ==>
                          !n. 0 < n /\ 0 < k /\ char r divides n /\ k < char r /\
                              ulog n ** 2 <= ordz k n /\
                              poly_intro_range r k n (SQRT (phi k) * ulog n) ==>
                              perfect_power n (char r)
   AKS_main_ulog_2b    |- !r. FiniteField r /\ (CARD R = char r) ==>
                          !n k. 0 < n /\ 0 < k /\ 1 < ordz k (char r) /\ char r divides n /\
                                k < char r /\ ulog n ** 2 <= ordz k n /\
                                poly_intro_range r k n (SQRT (phi k) * ulog n) ==>
                                perfect_power n (char r)
   AKS_main_ulog_3b    |- !n k. 1 < n /\ 0 < k /\ (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\
                                ulog n ** 2 <= ordz k n /\
                                poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n) ==>
                            ?p. prime p /\ perfect_power n p
   AKS_main_ulog_7b    |- !n. prime n <=> power_free n /\
                          ?k. 0 < k /\ ulog n ** 2 <= ordz k n /\
                              (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                              (k < n ==> poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n))
   AKS_main_ulog_8b    |- !n. prime n <=> power_free n /\
                          ?k. 0 < k /\ ulog n ** 2 <= ordz k n /\
                              (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                              (k < n ==> poly_intro_checks n k (SQRT (phi k) * ulog n))

   Using passChecks:
   aks_main_thm_0b     |- !r k z. FiniteField r /\ (CARD R = char r) /\ 1 < ordz k (char r) /\
                                  mifactor z (unity k) /\ (forderz X = k) ==>
                          !n a s. 1 < k /\ (a = SUC (LOG2 n) ** 2) /\
                                  (s = SQRT (phi k) * SUC (LOG2 n)) /\
                                  passChecks r n a k s ==> perfect_power n (char r)
   aks_main_thm_0b_alt |- !r k z. FiniteField r /\ (CARD R = char r) /\ 1 < ordz k (char r) /\
                                  mifactor z (unity k) /\ 1 < deg z /\ (forderz X = k) ==>
                          !n a s. (a = SUC (LOG2 n) ** 2) /\
                                  (s = SQRT (phi k) * SUC (LOG2 n)) /\
                                  passChecks r n a k s ==> perfect_power n (char r)
   aks_main_thm_1b     |- !r k z. FiniteField r /\ (CARD R = char r) /\ 1 < ordz k (char r) /\
                                  mifactor z (unity k) /\ (forderz X = k) ==>
                          !n a s. 0 < n /\ 0 < k /\ (a = SUC (LOG2 n) ** 2) /\
                                  (s = SQRT (phi k) * SUC (LOG2 n)) /\
                                  passChecks r n a k s ==> perfect_power n (char r)
   aks_main_thm_2b     |- !r. FiniteField r /\ (CARD R = char r) ==>
                          !n a k s. 0 < k /\ 1 < ordz k (char r) /\
                                    (a = SUC (LOG2 n) ** 2) /\
                                    (s = SQRT (phi k) * SUC (LOG2 n)) /\
                                    passChecks r n a k s ==> perfect_power n (char r)
   aks_main_thm_3b     |- !n a k s. 1 < n /\ 0 < k /\
                                    (a = SUC (LOG2 n) ** 2) /\
                                    (s = SQRT (phi k) * SUC (LOG2 n)) /\
                                    (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\ a <= ordz k n /\
                                    poly_intro_range (ZN n) k n s ==>
                                ?p. prime p /\ perfect_power n p
   aks_main_thm_7b     |- !n. prime n <=> power_free n /\
                          ?a k s. 0 < k /\ (a = SUC (LOG2 n) ** 2) /\
                                  (s = SQRT (phi k) * SUC (LOG2 n)) /\
                                  (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                                  a <= ordz k n /\ (k < n ==> poly_intro_range (ZN n) k n s)
   aks_main_thm_8b     |- !n. prime n <=> power_free n /\
                          ?a k s. 0 < k /\ (a = SUC (LOG2 n) ** 2) /\
                                  (s = SQRT (phi k) * SUC (LOG2 n)) /\
                                  (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                                  a <= ordz k n /\ (k < n ==> poly_intro_checks n k s)

   aks_main_ulog_0b    |- !r k z. FiniteField r /\ (CARD R = char r) /\ 1 < ordz k (char r) /\
                                  mifactor z (unity k) /\ (forderz X = k) ==>
                          !n a s. 0 < n /\ 1 < k /\ (a = ulog n ** 2) /\
                                  (s = SQRT (phi k) * ulog n) /\
                                  passChecks r n a k s ==> perfect_power n (char r)
   aks_main_ulog_0b_alt|- !r k z. FiniteField r /\ (CARD R = char r) /\ 1 < ordz k (char r) /\
                                  mifactor z (unity k) /\ 1 < deg z /\ (forderz X = k) ==>
                          !n a s. 0 < n /\ (a = ulog n ** 2) /\ (s = SQRT (phi k) * ulog n) /\
                                  passChecks r n a k s ==> perfect_power n (char r)
   aks_main_ulog_1b    |- !r k z. FiniteField r /\ (CARD R = char r) /\ 1 < ordz k (char r) /\
                                  mifactor z (unity k) /\ (forderz X = k) ==>
                          !n a s. 0 < n /\ 0 < k /\ (a = ulog n ** 2) /\
                                  (s = SQRT (phi k) * ulog n) /\
                                  passChecks r n a k s ==> perfect_power n (char r)
   aks_main_ulog_2b    |- !r. FiniteField r /\ (CARD R = char r) ==>
                          !n a k s. 0 < n /\ 0 < k /\ 1 < ordz k (char r) /\
                                    (a = ulog n ** 2) /\ (s = SQRT (phi k) * ulog n) /\
                                    passChecks r n a k s ==> perfect_power n (char r)
   aks_main_ulog_3b    |- !n a k s. 1 < n /\ 0 < k /\
                                    (a = ulog n ** 2) /\ (s = SQRT (phi k) * ulog n) /\
                                    (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\
                                    a <= ordz k n /\ poly_intro_range (ZN n) k n s ==>
                                ?p. prime p /\ perfect_power n p
   aks_main_ulog_7b    |- !n. prime n <=> power_free n /\
                          ?a k s. 0 < k /\ (a = ulog n ** 2) /\
                                  (s = SQRT (phi k) * ulog n) /\ a <= ordz k n /\
                                  (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                                  (k < n ==> poly_intro_range (ZN n) k n s)
   aks_main_ulog_8b    |- !n. prime n <=> power_free n /\
                          ?a k s. 0 < k /\ (a = ulog n ** 2) /\
                                  (s = SQRT (phi k) * ulog n) /\ a <= ordz k n /\
                                  (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                                  (k < n ==> poly_intro_checks n k s)

*)

(* The formalisation of AKS algorithm depends the following:

(0) The ingredients of AKS algorithm
aks_thm  |- !n. prime n <=> aks n
aks_def  |- !n. aks n <=> power_free n /\
                          case aks_param n of
                            nice j => j = n
                          | good k => k < n ==>
                                      !c. 0 < c /\ c <= 2 * SQRT k * SUC (LOG2 n) ==>
                                          (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k))
                          | bad => F
(1) There exists a suitable AKS parameter
aks_param_exists |- !n. aks_param n <> bad
aks_param_def    |- !n. aks_param n = aks_param_search n (SQ (ulog n)) 2 (2 + ulog n * HALF (SQ (ulog n) ** 2))
(2) The AKS polynomial identity checks can be shifted
First, there is a homomorphism between (ZN n) and (ZN p), where prime p divides n:
> ZN_to_ZN_ring_homo |> SPEC ``n:num`` |> SPEC ``p:num``;
val it = |- 0 < n /\ 0 < p /\ p divides n ==> RingHomo (\x. x MOD p) (ZN n) (ZN p): thm
And the ring homomorphism preserves introspective relationship:
poly_ring_homo_intro   |- !r s f. Ring r /\ Ring s /\ RingHomo f r s /\ s.prod.id <> s.sum.id ==>
                          !k. 0 < k ==> !n p. n intro p /\ f (lead p) <> s.sum.id ==> poly_intro s k n p_
Thus giving:
> ring_homo_intro_ZN_to_ZN_X_add_c |> SPEC ``n:num`` |> SPEC ``p:num``;
val it = |- 0 < n /\ 1 < p /\ p divides n ==> !k s. 0 < k /\ s < p ==>
            !h c. 0 < c /\ c <= s /\ poly_intro (ZN n) k h (x+ n c) ==> poly_intro (ZN p) k h (x+ p c): thm
(3) The idea of introspective indexes
poly_intro_mult   |- !r. Ring r /\ #1 <> #0 ==> !k p n m. n intro p /\ m intro p ==> n * m intro p
Thus if introspective indexes have seeds n m, the set will grow.
poly_intro_X_add_c_prime_char_1   |- !r. FiniteField r ==> !k. 0 < k ==> !c. char r intro X + |c|
This gives the introspective index seeds: n and (char r).
poly_intro_X_add_c_prime_char_3   |- !r. FiniteField r ==> !k. coprime k (CARD R) /\ 1 < ordz k (CARD R) ==>
                                     !n. char r divides n /\ n intro X + |c| ==> n DIV char r intro X + |c|
This gives the introspective index seeds: n and n DIV (char r).
(4) The construction of introspective sets
setN_def  |- !r k s. N = {m | coprime m k /\ !c. 0 < c /\ c <= s ==> m intro X + |c|}
setP_def  |- !r k s. P = {p | poly p /\ !m. m IN N ==> m intro p}
Finite versions:
modN_def  |- !r k s. M = IMAGE (\m. m MOD k) N
modP_def  |- !r k s h. Q h = IMAGE (\p. p % h) P

Now estimate the size of these finite sets:
modN_card_lower        |- !r k s. Ring r /\ #1 <> #0 /\ 1 < k ==> !n. n IN N ==> ordz k n <= CARD M
modN_card_upper        |- !r k s. 1 < k ==> CARD M < k
modN_card_upper_better |- !r k s. 1 < k ==> CARD M <= phi k

modP_card_lower_0      |- !r k s z. FiniteField r /\ mifactor z (unity k)s 1 < deg z /\
                           (forderz X = k) /\ s < char r ==> 2 ** MIN s (CARD M) <= CARD (Q z)
modP_card_upper_max    |- !r k s z. FiniteField r /\ mifactor z (unity k) ==> CARD (Q z) <= CARD R ** deg z

(5) The injective maps between finite sets

reduceP_mod_modP_inj_1
|- !r k s z. Field r /\ 0 < k /\ mifactor z (unity k) /\ (forderz X = k) ==> INJ (\p. p % z) PM (Q z)
This will establish modP_card_lower_0

reduceN_mod_modN_inj_2
|- !r k s z. Field r /\ mifactor z (unity k) ==>
          !p q. 1 < p /\ 1 < q /\ p IN N /\ q IN N /\ (p * q) ** SQRT (CARD M) < CARD (Q z) ==>
              INJ (\m. m MOD k) (NM p q (SQRT (CARD M))) M
This will help the punch line.

(6) Punch line: n must be a perfect power of its prime factor.
Let t = CARD M.
We have  n ** SQRT t < 2 ** MIN s t             by modN_card_in_exp_lt_bound_1, 1 < k, n IN N
We have  2 ** MIN s t <= CARD (Q z)             by modP_card_lower_0, 0 < s, s < p
Thus (a) INJ (\m. m MOD k) (NM p q (SQRT t)) M  by reduceN_mod_modN_inj_2, 1 < p, 1 < q

If ~perfect_power n p,
    Then CARD (NM p q (SQRT t)) = (SUC (SQRT t)) ** 2   by reduceN_card, 1 < k, perfect_power_cofactor
     But t < (SUC (SQRT t)) ** 2                        by modN_finite, SQRT_PROPERTY
Thus (b) CARD M = t < CARD (NM p q (SQRT t))

Note (a) and (b) violates the Pigeonhole Principle:
PHP |- !f s t. FINITE t /\ CARD t < CARD s ==> ~INJ f s t

(7) Analysis of AKS Main Theorem

The Basic AKS Main Theorem:
(1) Version 2B
    * Given 1 < n,
    * If you can find a SimpleFiniteField r = FiniteField r /\ (CARD R = char r)
         and (char r) divides n,
    * and a parameter k such that k < (char r) /\ (LOG2 n + 1) ** 2 <= ordz k n
    * and you verify all the identities !c. 0 < c /\ c <= SQRT (phi k) * (LOG2 n + 1) ==> n intro X + |c|
    * Then perfect_power n (char r)
> AKS_main_thm_2b;
val it = |- !r. FiniteField r /\ (CARD R = char r) ==>
            !k n. 1 < n /\ char r divides n /\ 1 < k /\ k < char r /\
                  coprime k n /\ 1 < ordz k (char r) /\ (LOG2 n + 1) ** 2 <= ordz k n /\
                  poly_intro_range r k n (SQRT (phi k) * (LOG2 n + 1)) ==> perfect_power n (char r): thm
[Proof]
   Let p = char r, s = SQRT (phi k) * (LOG2 n + 1).
   Then prime p                              by finite_field_char

   If n = p, true                            by perfect_power_self
   If n <> p,
      Let q = n DIV p, t = CARD M
      Note n IN N                            by setN_element
      Also p IN N                            by coprime_prime_factor_coprime, poly_intro_X_add_c_prime_char
      Then q IN N                            by coprime_product_coprime_iff, poly_intro_X_add_c_prime_char_3

      Step 1: Apply modN_card_in_exp_lt_bound_1
      Note n ** SQRT t < 2 ** MIN s t        by modN_card_in_exp_lt_bound_1, 1 < k, n IN N

      Step 2: Apply modP_card_lower
      Note 0 < s                             by TWICE_SQRT_TIMES_SUC_LOG2, 0 < k
       and s < p                             by ZN_order_condition_property_1, phi_lt, and given k < char r
      Also ?z. mifactor z (unity k) /\ (deg z = ordz k p) /\ (forderz X = k) by poly_unity_special_factor_exists
       ==> 2 ** MIN s t <= CARD (Q z)        by modP_card_lower_0, s < p

      Step 3: Apply reduceN_mod_modN_inj_2
       Note         n ** SQRT t < CARD (Q z)              by Step 1, Step 2
         so (p * q) ** (SQRT t) < CARD (Q z)              by n = p * q
      Hence INJ (\m. m MOD k) (NM p q (SQRT t)) M         by reduceN_mod_modN_inj_2, 1 < p, 1 < q

      Step 4: Apply reduceN_card
      By contradiction, assume ~perfect_power n p.
      Then ~perfect_power q p                             by perfect_power_cofactor
       and CARD (NM p q (SQRT t)) = (SUC (SQRT t)) ** 2   by reduceN_card, 1 < k, ~perfect_power q p
      Note t < (SUC (SQRT t)) ** 2                        by modN_finite, SQRT_PROPERTY
      Overall,  t < CARD (NM p q (SQRT t))

      Step 5: Conclusion
      We have INJ (\m. m MOD k) (NM p q (SQRT t)) M       by Step 3
      But     CARD M = t < CARD (NM p q (SQRT t))         by Step 4
      This violates the Pigeonhole Principle:
      PHP |- !f s t. FINITE t /\ CARD t < CARD s ==> ~INJ f s t

      Therefore, perfect_power n p.

(2) Since we can pick the prime (char r) above as a prime factor of n, we have Version 3B:
> AKS_main_thm_3b;
val it = |- !n k. 1 < n /\ 0 < k /\ (LOG2 n + 1) ** 2 <= ordz k n /\
                  (!j. 0 < j /\ j <= k ==> ~(j divides n)) /\
                  poly_intro_range (ZN n) k n (SQRT (phi k) * SUC (LOG2 n)) ==>
                  ?p. prime p /\ perfect_power n p: thm
(3) Therefore if the parameter k can be found, AKS will be fine:
> AKS_main_thm_7b;
val it = |- !n. prime n <=> power_free n /\
                            ?k. 0 < k /\ (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                                SUC (LOG2 n) ** 2 <= ordz k n /\
                     (k < n ==> poly_intro_range (ZN n) k n (SQRT (phi k) * SUC (LOG2 n))): thm
And parameter k can indeed be found.

Concerning the complexity,
(1) Perfect power test
(2) AKS parameter search
(3) Polynomial Modulo computation

*)

(* ------------------------------------------------------------------------- *)
(* Helpers                                                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < k ==> 0 < SQRT (phi k) * SUC (LOG2 n) *)
(* Proof:
   Note k <> 0                               by 0 < k
   Thus phi k <> 0                           by phi_eq_0
   Thus SQRT (phi k) <> 0                    by SQRT_EQ_0
   Also LOG2 n + 1 <> 0                      by arithmetic
    ==> SQRT (phi k) * (LOG2 n + 1) <> 0     by MULT_EQ_0
*)
val SQRT_TIMES_SUC_LOG2 = store_thm(
  "SQRT_TIMES_SUC_LOG2",
  ``!k n. 0 < k ==> 0 < SQRT (phi k) * SUC (LOG2 n)``,
  rpt strip_tac >>
  `0 < SUC (LOG2 n)` by decide_tac >>
  metis_tac[MULT_EQ_0, phi_eq_0, SQRT_EQ_0, NOT_ZERO]);

(* ------------------------------------------------------------------------- *)
(* Improve Bounds for AKS Theorem (using cofactor)                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Note: The constants are improved using p IN N and (q = n DIV p) IN N.     *)
(* Pros                                                                      *)
(* . constants a, s are half of those in unimproved version.                 *)
(* Cons                                                                      *)
(* . need 1 < ordz k p and CARD R = char r, so only simple finite fields.    *)
(* . need a prime p factor of n with 1 < ordz k p to build the finite field. *)
(* ------------------------------------------------------------------------- *)


(* Theorem: The AKS Main Theorem (Version 0)
   Assume there is FiniteField r with (char r) dividing n,
               and (unity k) having a monic irreducible factor z,
             where k is the order of X in the PolyModRing by z,
              then if k satisfies further conditions,
                  and n intro (X + |c|) for 0 < c <= s,
                  up to a limit s determined by k and n,
                  then n must be a perfect power of (char r).
   Note: (char r) of FiniteField r is always a prime.
*)
(* Proof:
   Let a = (SUC (LOG2 n)) ** 2,
       s = (SQRT (phi k)) * (SUC (LOG2 n)),
       p = char r.
   Then prime p                   by finite_field_char

   If n = p,
      Then perfect_power n p      by  perfect_power_self
   If n <> p,
      Note p <= n                 by DIVIDES_LE, p divides n
        so p < n                  by p <> n
       and MAX p n = n            by MAX_DEF

      Some assertions:
      Note 1 < p                  by ONE_LT_PRIME
       and 0 < k                  by 1 < k
       Now coprime k n            by ZN_order_eq_0, 0 < k, 0 < ordz k n
      Thus n <> 0                 by coprime_0R, k <> 1
       and n <> 1                 by DIVIDES_ONE, p <> n
        so 1 < n and 0 < n        by n <> 0, n <> 1
      Also coprime n k            by coprime_sym

      Let t = CARD M

      Step 1: Apply modN_card_in_exp_lt_bound_1
      Since n IN N                           by setN_element
      Then n ** SQRT t < 2 ** MIN s t        by modN_card_in_exp_lt_bound_1, 1 < k

      Step 2: Apply modP_card_lower_1
      Since 0 < s                            by SQRT_TIMES_SUC_LOG2, 0 < k
       Also s <= phi k <= k                  by ZN_order_condition_property, phi_le, 1 < n
         so s < char r                       by given k < char r
      gives 2 ** MIN s t <= CARD (Q z)       by modP_card_lower_1, forderz X = k
      Thus  n ** (2 * SQRT t) < CARD (Q z)   by LESS_LESS_EQ_TRANS

     Introduce q:
     Let q = n DIV p.
     Then p * q = n                          by DIVIDES_EQN_COMM, 0 < p
     Note q <> 0                             by MULT_EQ_0, n <> 0
      and q <> 1                             by MULT_RIGHT_1, n <> p
       so 1 < q                              by q <> 0, q <> 1
     Also coprime p k                        by coprime_prime_factor_coprime, prime p, 1 < n
      ==> p IN N /\ q IN N                       by setN_has_char_and_cofactor, 1 < ordz k p
     Thus INJ (\m. m MOD k) (NM p q (SQRT t)) M  by reduceN_mod_modN_inj_2, 1 < q

      Step 3: Apply reduceN_mod_modN_inj_2
      Since coprime p k                            by coprime_prime_factor_coprime
            p IN N                                 by setN_has_char, coprime p k
      Hence INJ (\m. m MOD k) (NM p n (SQRT t)) M  by reduceN_mod_modN_inj_2, 1 < q

      Step 4: Apply reduceN_card
      By contradiction, assume ~perfect_power n p.
      Then ~perfect_power q            by perfect_power_cofactor, 0 < p, ~perfect_power n p
       Now FINITE M                    by modN_finite, 0 < k
       and t < (SUC (SQRT t)) ** 2     by SQRT_PROPERTY, 0 < t
             = CARD (NM p q (SQRT t))  by reduceN_card, 0 < k, 1 < q, ~perfect_power q p
      Thus t < CARD (NM p q (SQRT t))  by above

      Step 5: Conclusion
      This violates the Pigeonhole Principle:
      PHP |- !f s t. FINITE t /\ CARD t < CARD s ==> ~INJ f s t

      Therefore, perfect_power n p.
*)
val AKS_main_thm_0b = store_thm(
  "AKS_main_thm_0b",
  ``!(r:'a field) k z. FiniteField r /\ (CARD R = char r) /\ (* simple field *)
          1 < ordz k (char r) /\ (* additional condition for using q = n DIV p *)
          mifactor z (unity k) /\ (forderz X = k) ==>
   !n. 1 < k /\ (char r) divides n /\ k < char r /\
           (SUC (LOG2 n)) ** 2 <= ordz k n /\ (* conditions on n, k *)
           poly_intro_range r k n (SQRT (phi k) * (SUC (LOG2 n))) (* AKS tests *)
       ==> perfect_power n (char r)``,
  rpt strip_tac >>
  qabbrev_tac `p = char r` >>
  qabbrev_tac `a = (SUC (LOG2 n)) ** 2` >>
  qabbrev_tac `s = (SQRT (phi k)) * (SUC (LOG2 n))` >>
  `prime p` by rw[finite_field_char, Abbr`p`] >>
  Cases_on `n = p` >-
  rw[perfect_power_self] >>
  `0 < k` by decide_tac >>
  `coprime n k` by
  (`0 < a` by rw[Abbr`a`] >>
  `ordz k n <> 0` by decide_tac >>
  metis_tac[ZN_order_eq_0, coprime_sym]) >>
  `n <> 0` by metis_tac[GCD_0, LESS_NOT_EQ] >>
  `n <> 1` by metis_tac[DIVIDES_ONE] >>
  `0 < n /\ 1 < n` by decide_tac >>
  `p <= n` by rw[DIVIDES_LE] >>
  `p < n` by decide_tac >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `Field r /\ FINITE R` by metis_tac[FiniteField_def] >>
  `Ring r` by rw[] >>
  qabbrev_tac `t = CARD M` >>
  `n IN N` by rw[setN_element] >>
  `n ** SQRT t < 2 ** MIN s t` by rw[modN_card_in_exp_lt_bound_1, Abbr`t`, Abbr`a`, Abbr`s`] >>
  `0 < s` by metis_tac[SQRT_TIMES_SUC_LOG2] >>
  `s <= phi k` by rw[ZN_order_condition_property_1, coprime_sym, Abbr`a`, Abbr`s`] >>
  `phi k <= k` by rw[phi_le] >>
  `s < p` by decide_tac >>
  `2 ** MIN s t <= CARD (Q z)` by rw[modP_card_lower_1, Abbr`t`, Abbr`p`] >>
  `n ** SQRT t < CARD (Q z)` by decide_tac >>
  qabbrev_tac `q = n DIV p` >>
  `0 < p` by decide_tac >>
  `n = p * q` by rw[GSYM DIVIDES_EQN_COMM, Abbr`q`] >>
  `q <> 0` by metis_tac[MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
  `q <> 1` by metis_tac[MULT_RIGHT_1] >>
  `1 < q` by decide_tac >>
  `coprime p k` by metis_tac[coprime_prime_factor_coprime] >>
  `p IN N /\ q IN N` by metis_tac[setN_has_char_and_cofactor, coprime_sym] >>
  `INJ (\m. m MOD k) (NM p q (SQRT t)) M` by metis_tac[reduceN_mod_modN_inj_2] >>
  spose_not_then strip_assume_tac >>
  `~perfect_power q p` by rfs[perfect_power_cofactor] >>
  `FINITE M` by rw[modN_finite] >>
  `CARD (NM p q (SQRT t)) = (SUC (SQRT t)) ** 2` by metis_tac[reduceN_card] >>
  `t < (SUC (SQRT t)) ** 2` by rw[SQRT_PROPERTY] >>
  `t < CARD (NM p q (SQRT t))` by decide_tac >>
  metis_tac[PHP]);

(* Theorem: The AKS Main Theorem (Version 0) *)
(* Proof:
   Note 1 < k           by poly_X_order_gt_1
   The result follows   by AKS_main_thm_0b
*)
val AKS_main_thm_0b_alt = store_thm(
  "AKS_main_thm_0b_alt",
  ``!(r:'a field) k z. FiniteField r /\ (CARD R = char r) /\ 1 < ordz k (char r) /\
          mifactor z (unity k) /\ 1 < deg z /\ (forderz X = k) ==>
      !n. (char r) divides n /\ k < char r /\ (SUC (LOG2 n)) ** 2 <= ordz k n /\ (* conditions on n, k *)
          poly_intro_range r k n (SQRT (phi k) * SUC (LOG2 n)) (* AKS tests *)
      ==> perfect_power n (char r)``,
  metis_tac[AKS_main_thm_0b, poly_X_order_gt_1]);

(* Theorem: The AKS Main Theorem (Version 1)
   Assume there is FiniteField r with (char r) dividing n,
               and (unity k) having a monic irreducible factor z,
             where k is the order of X in the PolyModRing by z,
              then if k satisfies further conditions,
                  and n intro (X + |c|) for 0 < c <= s,
                  up to a limit s determined by k and n,
                  then n must be a perfect power of (char r).
   Note: (char r) of FiniteField r is always a prime.
*)
(* Proof:
   Note 1 < char r                     by finite_field_char_gt_1
     so n <> 1                         by DIVIDES_ONE, 1 < char r
   Note 1 < (SUC (LOG2 n)) ** 2        by LOG2_SUC_SQ, 1 < n
     so ordz k n <> 1                  by 1 < a <= ordz k n
    ==> k <> 1                         by ZN_order_mod_1
   Thus 1 < k                          by k <> 0, k <> 1
   The result follows                  by AKS_main_thm_0b
*)
val AKS_main_thm_1b = store_thm(
  "AKS_main_thm_1b",
  ``!(r:'a field) k z. FiniteField r /\ (CARD R = char r) /\ 1 < ordz k (char r) /\
           mifactor z (unity k) /\ (forderz X = k) ==>
    !n. 0 < n /\ 0 < k /\ (char r) divides n /\ k < char r /\
        (SUC (LOG2 n)) ** 2 <= ordz k n /\ (* conditions on n, k *)
        poly_intro_range r k n (SQRT (phi k) * SUC (LOG2 n)) (* AKS tests *)
    ==> perfect_power n (char r)``,
  rpt strip_tac >>
  `1 < char r` by rw[finite_field_char_gt_1] >>
  `n <> 1` by metis_tac[DIVIDES_ONE, LESS_NOT_EQ] >>
  `1 < (SUC (LOG2 n)) ** 2` by rw[LOG2_SUC_SQ] >>
  `ordz k n <> 1` by decide_tac >>
  `k <> 1` by metis_tac[ZN_order_mod_1] >>
  `1 < k` by decide_tac >>
  metis_tac[AKS_main_thm_0b]);

(* Theorem: The AKS Main Theorem (Version 2)
   Assume there is FiniteField r with (CARD R = char r) and (char r) dividing n,
               and a k with 1 < k < (char r) and coprime k n,
              then if k satisfies further conditions,
                  and n intro (X + |c|) for 0 < c <= s,
                  up to a limit s determined by k and n,
                  then n must be a perfect power of (char r).
   Note: (char r) of FiniteField r is always prime.
*)
(* Proof:
   Let p = char r.
   Then ?z. mifactor z (unity k) /\ forderz X = k)
                              by poly_unity_special_factor_exists_1, 0 < k, 1 < ordz k p
   Note prime p               by finite_field_char
     so 1 < p                 by ONE_LT_PRIME
    ==> k <> 1                by ZN_order_mod_1, 1 < ordz k p, 1 < p
   Thus 1 < k                 by 0 < k, k <> 1
   The result follows         by AKS_main_thm_0b
*)
val AKS_main_thm_2b = store_thm(
  "AKS_main_thm_2b",
  ``!(r:'a field). FiniteField r /\ (CARD R = char r) ==>
   !n k. 0 < k /\ 1 < ordz k (char r) /\
         (char r) divides n /\ k < char r /\
         (SUC (LOG2 n)) ** 2 <= ordz k n /\ (* conditions on n, k *)
         poly_intro_range r k n (SQRT (phi k) * SUC (LOG2 n)) (* AKS tests *)
     ==> perfect_power n (char r)``,
  rpt strip_tac >>
  qabbrev_tac `p = char r` >>
  `?z. mifactor z (unity k) /\ (forderz X = k)` by metis_tac[poly_unity_special_factor_exists_1] >>
  `k <> 1` by
  (`prime p` by rw[finite_field_char, Abbr`p`] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  metis_tac[ZN_order_mod_1, LESS_NOT_EQ]) >>
  `1 < k` by decide_tac >>
  metis_tac[AKS_main_thm_0b]);

(* Theorem: The AKS Main Theorem (Version 3)
   Given a number n > 1,
   If there are numbers k and s such that:
      1 < k, order of n in (ZN k) >= (SUC (LOG2 n))^2
      s = sqrt(phi k) SUC(LOG2 n)
      for all nonzero j <= k, coprime j n
      for all nonzero c <= s, poly_intro (ZN n) k n (zx+ c)
   Then n must be a perfect power of a prime p.
*)
(* Proof:
   If n is prime,
      Let prime p = n,
      Then n = p ** 1                    by perfect_power_self
   If n is not prime,
       Let a = (SUC (LOG2 n)) ** 2,
           s = SQRT (phi k) * SUC (LOG2 n).
      Then 1 < a                         by LOG2_SUC_SQ, 1 < n
        so 1 < ordz k n                  by a <= ordz k n
       ==> ?p. prime p /\ p divides n /\ 1 < ordz k p
                                         by ZN_order_gt_1_property, 0 < k

      Take this prime p.
      Then 1 < p                         by ONE_LT_PRIME
       and k < p                         by implication: 1 < p /\ p <= k ==> ~(p divides n)

      Also k <> 1                        by ZN_order_mod_1, 1 < ordz k n
      Thus coprime k n                   by coprime_by_le_not_divides, 1 < k
       and s <= phi k                    by ZN_order_condition_property_1, 1 < n, coprime k n
       and phi k <= k                    by phi_le
        so s < p                         by s <= phi k <= k < p

      Note FiniteField (ZN p)               by ZN_finite_field, prime p
       and char (ZN p) = p                  by ZN_char, 0 < p
       and CARD (ZN p).carrier = p          by ZN_card
      Now, poly_intro_range (ZN n) k n s    by given
      Thus poly_intro_range (ZN p) k n s    by ring_homo_intro_ZN_to_ZN_X_add_c, s < p

      The result follows                    by AKS_main_thm_2b, k < p
*)
val AKS_main_thm_3b = store_thm(
  "AKS_main_thm_3b",
  ``!n k. 1 < n /\ 0 < k /\
         (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\ (* check on k, gives k < p later *)
         (SUC (LOG2 n)) ** 2 <= ordz k n /\ (* condition on k *)
         poly_intro_range (ZN n) k n (SQRT (phi k) * SUC (LOG2 n)) (* AKS tests *)
     ==> ?p. prime p /\ perfect_power n p``,
  rpt strip_tac >>
  Cases_on `prime n` >-
  metis_tac[perfect_power_self] >>
  qabbrev_tac `a = (SUC (LOG2 n)) ** 2` >>
  qabbrev_tac `s = SQRT (phi k) * SUC (LOG2 n)` >>
  `1 < a` by rw[LOG2_SUC_SQ, Abbr`a`] >>
  `1 < ordz k n` by decide_tac >>
  `?p. prime p /\ p divides n /\ 1 < ordz k p` by rw[ZN_order_gt_1_property] >>
  qexists_tac `p` >>
  simp[] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `k < p` by metis_tac[NOT_LESS] >>
  `s < p` by
  (`k <> 1` by metis_tac[ZN_order_mod_1, LESS_NOT_EQ] >>
  `coprime k n` by rw[coprime_by_le_not_divides] >>
  `s <= phi k` by metis_tac[ZN_order_condition_property_1] >>
  `phi k <= k` by rw[phi_le] >>
  decide_tac) >>
  `0 < n` by decide_tac >>
  `poly_intro_range (ZN p) k n s` by metis_tac[ring_homo_intro_ZN_to_ZN_X_add_c] >>
  `FiniteField (ZN p)` by rw[ZN_finite_field] >>
  `char (ZN p) = p` by rw[ZN_char] >>
  `CARD (ZN p).carrier = p` by rw[ZN_card] >>
  metis_tac[AKS_main_thm_2b]);

(* Theorem: The AKS Main Theorem (Version 7)
   A number n is prime iff
     power-free n,
     there is number k such that:
      0 < k
      and order of n in (ZN k) >= (SUC (LOG2 n)) ** 2
      and for all nonzero j < MIN (SUC k) n, coprime j n  (with MIN hidden)
      and if k < n, let s = sqrt(phi k) SUC (LOG2 n),
          then for all nonzero c <= s, poly_intro (ZN n) k n (zx+ c)
*)
(* Proof:
   If part: prime n ==> power_free n /\ (?k s. ... )
      This is to show:
      (1) prime n ==> power_free n, true      by prime_is_power_free
      (2) ?k. 0 < k /\ ...
          Let a = (SUC (LOG2 n)) ** 2.
          Then 1 < n                          by ONE_LT_PRIME
           and 1 < a                          by LOG2_SUC_SQ, 1 < n
            so ?k. 1 < k /\ coprime k n /\ m <= ordz k n
                                              by ZN_order_good_enough, 1 < n, 1 < a
          Take this k, the subgoals are:
          (1) prime n /\ 1 < j /\ j <= k /\ j < n ==> ~(j divides n)
              Ignore j <= k, this is true     by prime_def
          (2) prime n /\ 0 < c /\ c <= s ==> poly_intro (ZN n) k n (x+ n c)
              where s = SQRT (phi k) * SUC (LOG2 n)
               Note Ring (ZN n)               by ZN_ring, 0 < n
                    char (ZN n) = n           by ZN_char, 0 < n
                ==> poly_intro (ZN n) k n (x+ n c)
                                              by poly_intro_X_add_c_prime_char, 0 < k, n <> 1

   Only-if part: power_free n /\ (?k. 0 < k /\ ... ) ==> prime n
      Note 1 < n                              by power_free_gt_1
      If k < n,
         Let s = SQRT (phi k) * SUC (LOG2 n).
         (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) becomes
         (!j. 1 < j /\ j <= k ==> ~(j divides n))       as j <= k /\ k < n ==> j < n
         with poly_intro_range (ZN n) k n s
         Therefore ?p. prime p /\ perfect_power n p     by AKS_main_thm_3b
            But power_free n ==> p = n                  by power_free_perfect_power
          Hence prime n.
      Otherwise, ~(k < n), or n <= k
         (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) becomes
         (!j. 0 < j /\ j < n ==> ~(j divides n))        as j < n /\ n <= k ==> j < k, or j <= k
          Hence prime n                                 by prime_iff_no_proper_factor
*)
val AKS_main_thm_7b = store_thm(
  "AKS_main_thm_7b",
  ``!n. prime n <=> power_free n /\
   ?k. 0 < k /\ (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
       (SUC (LOG2 n)) ** 2 <= ordz k n /\
       (k < n ==> poly_intro_range (ZN n) k n (SQRT (phi k) * SUC (LOG2 n)))``,
  rw_tac bool_ss[EQ_IMP_THM] >-
  rw[prime_is_power_free] >-
 (qabbrev_tac `a = (SUC (LOG2 n)) ** 2` >>
  `1 < n` by rw[ONE_LT_PRIME] >>
  `1 < a` by rw[LOG2_SUC_SQ, Abbr`a`] >>
  `?k. 1 < k /\ coprime k n /\ a <= ordz k n` by rw[ZN_order_good_enough] >>
  qexists_tac `k` >>
  simp[] >>
  rw_tac std_ss[] >-
  metis_tac[prime_def, LESS_NOT_EQ] >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `char (ZN n) = n` by rw[ZN_char] >>
  `0 < k /\ n <> 1` by decide_tac >>
  metis_tac[poly_intro_X_add_c_prime_char, ZN_property]) >>
  `1 < n` by rw[power_free_gt_1] >>
  Cases_on `k < n` >| [
    `!j. 1 < j /\ j <= k ==> 1 < j /\ j <= k /\ j < n` by decide_tac >>
    metis_tac[AKS_main_thm_3b, power_free_perfect_power],
    `!j. 1 < j /\ j < n ==> 1 < j /\ j <= k /\ j < n` by decide_tac >>
    metis_tac[prime_iff_no_proper_factor]
  ]);

(* Theorem: This is Version 7 with poly_intro made explicit:
            prime n <=> power_free n /\
            (?k. 0 < k /\ (SUC (LOG2 n)) ** 2 <= ordz k n /\ (* property of k *)
             (!j. 0 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\ (* checks on k, hidden MIN *)
             (k < n ==> poly_intro_checks n k (SQRT (phi k) * SUC (LOG2 n)))) *)
(* Proof:
   Note  1 < n ==> 0 < n                              by arithmetic
   also  power_free n ==> 1 < n ==> 0 < n             by power_free_gt_1
    and  0 < n ==> Ring (ZN n)                        by ZN_ring, 0 < n
   together with poly_intro_X_add_c, this is true     by AKS_main_thm_7b
*)
val AKS_main_thm_8b = store_thm(
  "AKS_main_thm_8b",
  ``!n. prime n <=> power_free n /\
   ?k. 0 < k /\ (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\ (* checks on k, hidden MIN *)
       (SUC (LOG2 n)) ** 2 <= ordz k n /\ (* property of k *)
       (k < n ==> !c. 0 < c /\ c <= SQRT (phi k) * SUC (LOG2 n) ==>  (* AKS checks *)
                  ((x+^ n c n) == (x^+ n c n)) (pmod (ZN n) (x^- n k)))``,
  rpt strip_tac >>
  `!n. 1 < n ==> 0 < n` by decide_tac >>
  `!n. 0 < n ==> Ring (ZN n)` by rw[ZN_ring] >>
  metis_tac[AKS_main_thm_7b, poly_intro_X_add_c, power_free_gt_1]);

(* ------------------------------------------------------------------------- *)
(* AKS Theorems with bounds improved using upper logarithm                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: The AKS Main Theorem (Version 0)
   Assume there is FiniteField r with (char r) dividing n,
               and (unity k) having a monic irreducible factor z,
             where k is the order of X in the PolyModRing by z,
              then if k satisfies further conditions,
                  and n intro (X + |c|) for 0 < c <= s,
                  up to a limit s determined by k and n,
                  then n must be a perfect power of (char r).
   Note: (char r) of FiniteField r is always a prime.
*)
(* Proof:
   Let a = (ulog n) ** 2,
       s = (SQRT (phi k)) * ulog n,
       p = char r.
   Then prime p                   by finite_field_char

   If n = p,
      Then perfect_power n p      by  perfect_power_self
   If n <> p,
      Note p <= n                 by DIVIDES_LE, p divides n
        so p < n                  by p <> n
       and n <> 1                 by DIVIDES_ONE, p <> n

   If perfect_power n 2
      Then ?e. n = 2 ** e         by perfect_power_def
       and e <> 0                 by EXP_0, n <> 1
       ==> p divides 2            by prime_divides_power, e <> 0
       ==> p = 2                  by prime_divides_prime, PRIME_2
      Hence perfect_power n p     by p = 2

   Otherwise, ~perfect_power n 2.
      Some assertions:
      Note 1 < n                  by DIVIDES_ONE, n <> p
       and 1 < p                  by ONE_LT_PRIME

      Let t = CARD M

      Step 1: Apply modN_card_in_exp_lt_bound_3
      Since n IN N                           by setN_element
       Then n ** (SQRT t) < 2 ** MIN s t     by modN_card_in_exp_lt_bound_3, ~perfect_power n 2

      Step 2: Apply modP_card_lower_0
      Since 0 < SQRT (phi k) * ulog n        by sqrt_phi_times_ulog, 0 < k, 1 < n
        and 0 < s                            by arithmetic
       Also s <= phi k <= k                  by ZN_order_condition_property_3, phi_le, 1 < n
         so s < p                            by given k < p = char r
      gives 2 ** MIN s t <= CARD (Q z)       by modP_card_lower_1, 0 < s, s < char r
      Thus  n ** (SQRT t) < CARD (Q z)       by LESS_LESS_EQ_TRANS

      Step 3: Apply reduceN_mod_modN_inj_2
      Introduce q:
      Let q = n DIV p.
      Then p * q = n                         by DIVIDES_EQN_COMM, 0 < p
      Note q <> 0                            by MULT_EQ_0, n <> 0
       and q <> 1                            by MULT_RIGHT_1, n <> p
        so 1 < q                             by q <> 0, q <> 1
      Also coprime p k                       by coprime_prime_factor_coprime, prime p, 1 < n
       ==> p IN N /\ q IN N                       by setN_has_char_and_cofactor, 1 < ordz k p
      Thus INJ (\m. m MOD k) (NM p q (SQRT t)) M  by reduceN_mod_modN_inj_2, 1 < q

      Step 4: Apply reduceN_card
      By contradiction, assume ~perfect_power n p.
      Then ~perfect_power q            by perfect_power_cofactor, 0 < p, ~perfect_power n p
       Now FINITE M                    by modN_finite, 0 < k
       and t < (SUC (SQRT t)) ** 2     by SQRT_PROPERTY, 0 < t
             = CARD (NM p q (SQRT t))  by reduceN_card, 0 < k, 1 < q, ~perfect_power q p
      Thus t < CARD (NM p q (SQRT t))  by above

      Step 5: Conclusion
      This violates the Pigeonhole Principle:
      PHP |- !f s t. FINITE t /\ CARD t < CARD s ==> ~INJ f s t

      Therefore, perfect_power n p.
*)
val AKS_main_ulog_0b = store_thm(
  "AKS_main_ulog_0b",
  ``!(r:'a field) k z. FiniteField r /\ (CARD R = char r) /\ (* just simple fields *)
           1 < ordz k (char r) /\ (* parameter k *)
           mifactor z (unity k) /\ (forderz X = k) ==>
       !n. 0 < n /\ 1 < k /\ (* 0 < n to keep 0 < a *)
           (char r) divides n /\ k < char r /\ (ulog n) ** 2 <= ordz k n /\ (* conditions on n, k *)
           poly_intro_range r k n (SQRT (phi k) * ulog n) (* AKS tests *)
       ==> perfect_power n (char r)``,
  rpt strip_tac >>
  qabbrev_tac `a = (ulog n) ** 2` >>
  qabbrev_tac `s = (SQRT (phi k)) * ulog n` >>
  qabbrev_tac `p = char r` >>
  `prime p` by rw[finite_field_char, Abbr`p`] >>
  Cases_on `n = p` >-
  rw[perfect_power_self] >>
  `n <> 1` by metis_tac[DIVIDES_ONE] >>
  `1 < k` by rw[poly_X_order_gt_1] >>
  `0 < k /\ 0 < n /\ 1 < n` by decide_tac >>
  `coprime n k` by
  (`0 < a` by rw[ulog_pos, MULT_POS, Abbr`a`] >>
  `ordz k n <> 0` by decide_tac >>
  metis_tac[ZN_order_eq_0, coprime_sym]) >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `p <= n` by rw[DIVIDES_LE] >>
  `p < n` by decide_tac >>
  Cases_on `perfect_power n 2` >| [
    `?e. n = 2 ** e` by rw[GSYM perfect_power_def] >>
    `e <> 0` by metis_tac[EXP_0, NOT_LESS] >>
    `p divides 2` by fs[prime_divides_power] >>
    `p = 2` by rw[GSYM prime_divides_prime, PRIME_2] >>
    decide_tac,
    `Field r /\ FINITE R` by metis_tac[FiniteField_def] >>
    `Ring r` by rw[] >>
    `n IN N` by rw[setN_element] >>
    qabbrev_tac `t = CARD M` >>
    `n ** SQRT t < 2 ** MIN s t` by rw[modN_card_in_exp_lt_bound_3, Abbr`t`, Abbr`a`, Abbr`s`] >>
    `0 < s` by metis_tac[sqrt_phi_times_ulog] >>
    `s <= phi k` by metis_tac[ZN_order_condition_property_2, coprime_sym] >>
    `phi k <= k` by rw[phi_le] >>
    `s < p` by decide_tac >>
    `2 ** MIN s t <= CARD (Q z)` by rw[modP_card_lower_1, Abbr`t`, Abbr`p`, Abbr`s`] >>
    `n ** SQRT t < CARD (Q z)` by decide_tac >>
    qabbrev_tac `q = n DIV p` >>
    `p * q = n` by rw[GSYM DIVIDES_EQN_COMM, Abbr`q`] >>
    `q <> 0` by metis_tac[MULT_EQ_0, NOT_ZERO] >>
    `q <> 1` by metis_tac[MULT_RIGHT_1] >>
    `1 < q` by decide_tac >>
    `coprime p k` by metis_tac[coprime_prime_factor_coprime] >>
    `p IN N /\ q IN N` by metis_tac[setN_has_char_and_cofactor, coprime_sym] >>
    `INJ (\m. m MOD k) (NM p q (SQRT t)) M` by metis_tac[reduceN_mod_modN_inj_2] >>
    spose_not_then strip_assume_tac >>
    `~perfect_power q p` by rfs[perfect_power_cofactor] >>
    `FINITE M` by rw[modN_finite] >>
    `CARD (NM p q (SQRT t)) = (SUC (SQRT t)) ** 2` by metis_tac[reduceN_card] >>
    `t < (SUC (SQRT t)) ** 2` by rw[SQRT_PROPERTY] >>
    `t < CARD (NM p q (SQRT t))` by decide_tac >>
    metis_tac[PHP]
  ]);

(* Theorem: The AKS Main Theorem (Version 0) *)
(* Proof:
   Note 1 < k           by poly_X_order_gt_1
   The result follows   by AKS_main_ulog_0b
*)
val AKS_main_ulog_0b_alt = store_thm(
  "AKS_main_ulog_0b_alt",
  ``!(r:'a field) k z. FiniteField r /\ (CARD R = char r) /\ (* just simple fields *)
           1 < ordz k (char r) /\ (* parameter k *)
           mifactor z (unity k) /\ 1 < deg z /\ (forderz X = k) ==>
       !n. 0 < n /\ (* 0 < n to keep 0 < a *)
           (char r) divides n /\ k < char r /\ (ulog n) ** 2 <= ordz k n /\ (* conditions on n, k *)
           poly_intro_range r k n (SQRT (phi k) * ulog n) (* AKS tests *)
       ==> perfect_power n (char r)``,
  metis_tac[AKS_main_ulog_0b, poly_X_order_gt_1]);

(* Theorem: The AKS Main Theorem (Version 1) *)
(* Proof:
   Let p = char r.
   Then prime p               by finite_field_char
     so 1 < p                 by ONE_LT_PRIME
   Thus n <> 1                by DIVIDES_ONE, p divides n, 1 < p

   If n = 2,
      Note prime 2            by PRIME_2
       ==> p = 2              by prime_divides_prime, p divides n
      Hence true              by perfect_power_self
   Otherwise, n <> 2,
   Thus 2 < n                 by 0 < n, n <> 1, n <> 2
     so 1 < (ulog n) ** 2     by ulog_sq_gt_1, 2 < n
     so ordz k n <> 1         by 1 < (ulog n) ** 2 <= ordz k n
    ==> k <> 1                by ZN_order_mod_1
   Thus 1 < k                 by k <> 0, k <> 1
   The result follows         by AKS_main_ulog_0b
*)
val AKS_main_ulog_1b = store_thm(
  "AKS_main_ulog_1b",
  ``!(r:'a field) k z. FiniteField r /\ (CARD R = char r) /\ 1 < ordz k (char r) /\
           mifactor z (unity k) /\ (forderz X = k) ==>
    !n. 0 < n /\ 0 < k /\ (char r) divides n /\ k < char r /\
        (ulog n) ** 2 <= ordz k n /\ (* conditions on n, k *)
        poly_intro_range r k n (SQRT (phi k) * ulog n) (* AKS tests *)
    ==> perfect_power n (char r)``,
  rpt strip_tac >>
  qabbrev_tac `p = char r` >>
  `prime p` by rw[finite_field_char, Abbr`p`] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `n <> 1` by metis_tac[DIVIDES_ONE, LESS_NOT_EQ] >>
  Cases_on `n = 2` >| [
    `p = 2` by metis_tac[prime_divides_prime, PRIME_2] >>
    rw[perfect_power_self],
    `1 < (ulog n) ** 2` by rw[ulog_sq_gt_1] >>
    `ordz k n <> 1` by decide_tac >>
    `k <> 1` by metis_tac[ZN_order_mod_1] >>
    `1 < k` by decide_tac >>
    metis_tac[AKS_main_ulog_0b]
  ]);

(* Theorem: The AKS Main Theorem (in generic FiniteField)
   Assume there is FiniteField r with (CARD R = char r) and (char r) dividing n,
               and a k with 1 < k < (char r) and coprime k n,
              then if k satisfies further conditions,
                  and n intro (X + |c|) for 0 < c <= s,
                  up to a limit s determined by k and n,
                  then n must be a perfect power of (char r).
   Note: (char r) of FiniteField r is always prime.
*)
(* Theorem: FiniteField r /\ (CARD R = char r) ==>
            !n k. 0 < n /\ 0 < k /\ 1 < ordz k (char r) /\
                  char r divides n /\ k < char r /\
                  (ulog n) ** 2 <= ordz k n /\
                  poly_intro_range r k n (SQRT (phi k) * (ulog n)) ==>
                  perfect_power n (char r) *)
(* Proof:
   Let p = char r.
   Then ?z. mifactor z (unity k) /\ (forderz X = k)
                              by poly_unity_special_factor_exists_1, 0 < k, 1 < ordz k p
   Note prime p               by finite_field_char
     so 1 < p                 by ONE_LT_PRIME
    ==> k <> 1                by ZN_order_mod_1, 1 < ordz k p, 1 < p
   Thus 1 < k                 by 0 < k, k <> 1
   The result follows         by AKS_main_ulog_0b
*)
val AKS_main_ulog_2b = store_thm(
  "AKS_main_ulog_2b",
  ``!r:'a field. FiniteField r /\ (CARD R = char r) ==>
   !n k. 0 < n /\ 0 < k /\ 1 < ordz k (char r) /\ char r divides n /\ k < char r /\
         (ulog n) ** 2 <= ordz k n /\
         poly_intro_range r k n (SQRT (phi k) * (ulog n))
     ==> perfect_power n (char r)``,
  rpt strip_tac >>
  qabbrev_tac `p = char r` >>
  `?z. mifactor z (unity k) /\ (forderz X = k)` by metis_tac[poly_unity_special_factor_exists_1] >>
  `k <> 1` by
  (`prime p` by rw[finite_field_char, Abbr`p`] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  metis_tac[ZN_order_mod_1, LESS_NOT_EQ]) >>
  `1 < k` by decide_tac >>
  metis_tac[AKS_main_ulog_0b]);

(* A streamlined proof of the same theorem.

   Idea: derive a contradiction by the following:
      (A) show   n ** SQRT t < 2 ** MIN s t   when (ulog n) ** 2 <= ordz k n
      (B) show   2 ** MIN s t <= n ** SQRT t  if ~(perfect_power n p)
*)

(* Theorem: FiniteField r /\ (CARD R = char r) ==>
            0 < n /\ 0 < k /\ 1 < ordz k (char r) /\ char r divides n /\
            k < char r /\ (ulog n) ** 2 <= ordz k n /\
            poly_intro_range r k n (SQRT (phi k) * (ulog n))
        ==> perfect_power n (char r) *)
(* Proof:
   Let p = char r, a = (ulog n) ** 2, s = SQRT (phi k) * ulog n.
   Note prime p                by finite_field_char
   and the goal is: perfect_power n p.

   Some assertions:
   Note 1 < p                  by ONE_LT_PRIME
     so n <> 1                 by DIVIDES_ONE, p divides n, 1 < p
   also k <> 1                 by ZN_order_mod_1, 1 < ordz k p
   Thus 1 < n /\ 1 < k         by 0 < n, 0 < k, n <> 1, k <> 1

   If perfect_power n 2,
      Note prime 2             by PRIME_2
      Thus p = 2               by perfect_power_def, prime_divides_prime_power
        or perfect_power n p   by above

   If ~(perfect_power n 2),
      Note 0 < a               by ulog_pos, 1 < n
        so ordz k n <> 0       by 0 < a <= ordz k n
      Thus coprime n k         by ZN_order_eq_0, by 0 < k

      Let t = CARD M.

      The strategy is to prove in two parts:
      (A) show   n ** SQRT t < 2 ** MIN s t   when (ulog n) ** 2 <= ordz k n
      (B) show   2 ** MIN s t <= n ** SQRT t  if ~(perfect_power n p)
      Clearly, they are contradictory unless (perfect_power n p).

      Part A:
      Note n IN N                      by setN_element, coprime n k, poly_intro_range r k n s
       ==> n ** SQRT t < 2 ** MIN s t  by modN_card_in_exp_lt_bound_3, (ulog n) ** 2 <= ordz k n, n IN N. [1]

      Part B:
      Step 1: show 2 ** MIN s t <= CARD (Q z).
      Note ?z. forderz X = k /\
               mifactor z (unity k)    by poly_unity_special_factor_exists, 0 < k
      Also 0 < s                       by sqrt_phi_times_ulog, 0 < k, 1 < n
       and s <= phi k                  by ZN_order_condition_property_2, 1 < n, coprime k n
       and phi k < k                   by phi_lt, 1 < k
       ==> s < k                       by s <= phi k, phi k < k
        or s < p                       by s < k, k < p = char r
      Thus 2 ** MIN s t <= CARD (Q z)  by modP_card_lower_1, 0 < s, s < p, ?z.  [2]

      Step 2: show CARD (Q z) <= n ** SQRT t
       Now coprime k p                 by coprime_prime_factor_coprime, prime p, p divides n, coprime n k
       By contradiction, suppose ~perfect_power n p.
       Then CARD (Q z) <= n ** SQRT t  by modP_card_upper_better, n IN N, ~perfect_power n p. [3]

      This leads to a contradiction, as [1], [2] and [3] are incompatible.
*)

(* This is a much shorter proof of the AKS main theorem! *)

(* Another proof.
   This is closer to the usual proof, e.g. in AKS paper or Terence Tao's proof.

   Idea:
   This second proof aims at showing (a) (b) are incompatible:
   (a) 2 ** MIN s t <= n ** SQRT t  if ~(perfect_power n p)
       from: 2 ** MIN s t <= CARD (Q z)    by modP_card_lower_1
             CARD (Q z) <= n ** SQRT t     by modP_card_upper_better
   (b) n ** SQRT t < 2 ** MIN s t          by modN_card_in_exp_lt_bound_3
*)

(* Theorem: FiniteField r /\ (CARD R = char r) ==>
           !n k. 0 < k /\ 1 < ordz k (char r) /\ char r divides n /\
                 k < char r /\ SUC (LOG2 n) ** 2 <= ordz k n /\
                 poly_intro_range r k n (SQRT (phi k) * SUC (LOG2 n)) ==>
                 perfect_power n (char r) *)
(* Proof:
   Let p = char r, a = (ulog n) ** 2, s = SQRT (phi k) * ulog n.
   Note prime p                by finite_field_char
   and the goal is: perfect_power n p.

   Some assertions:
   Note 1 < p                  by ONE_LT_PRIME
     so n <> 1                 by DIVIDES_ONE, p divides n, 1 < p
   also k <> 1                 by ZN_order_mod_1, 1 < ordz k p
   Thus 1 < n /\ 1 < k         by 0 < n, 0 < k, n <> 1, k <> 1

   If perfect_power n 2,
      Note prime 2             by PRIME_2
      Thus p = 2               by perfect_power_def, prime_divides_prime_power
        or perfect_power n p   by above

   If ~(perfect_power n 2),
      Note 0 < a               by ulog_pos, 1 < n
        so ordz k n <> 0       by 0 < a <= ordz k n
      Thus coprime n k         by ZN_order_eq_0, by 0 < k

      Let t = CARD M.

      The strategy is to prove in two parts:
      (A) show   2 ** MIN s t <= n ** SQRT t  if ~(perfect_power n p)
      (B) show   n ** SQRT t < 2 ** MIN s t   when (ulog n) ** 2 <= ordz k n
      Clearly, they are contradictory unless (perfect_power n p).

      Note n IN N                      by setN_element, coprime n k, poly_intro_range r k n s
      Part A:
      Step 1: show 2 ** MIN s t <= CARD (Q z).
      Note ?z. forderz X = k /\
               mifactor z (unity k)    by poly_unity_special_factor_exists, 0 < k
      Also 0 < s                       by sqrt_phi_times_ulog, 0 < k, 1 < n
       and s <= phi k                  by ZN_order_condition_property_2, 1 < n, coprime k n
       and phi k < k                   by phi_lt, 1 < k
       ==> s < k                       by s <= phi k, phi k < k
        or s < p                       by s < k, k < p = char r
      Thus 2 ** MIN s t <= CARD (Q z)  by modP_card_lower_1, 0 < s, s < p, ?z. [1]

      Step 2: show CARD (Q z) <= n ** SQRT t
       Now coprime k p                 by coprime_prime_factor_coprime, prime p, p divides n, coprime n k
       By contradiction, suppose ~perfect_power n p.
       Then CARD (Q z) <= n ** SQRT t  by modP_card_upper_better, n IN N, ~perfect_power n p. [2]
      Thus 2 ** MIN s t <= n ** SQRT t by [1] and [2] .. [A]

      Part B:
      Note n ** SQRT t < 2 ** MIN s t  by modN_card_in_exp_lt_bound_3, (ulog n) ** 2 <= ordz k n, n IN N. [B]

      This leads to a contradiction, as [A] and [B] are incompatible.
*)

(* Idea:
   The third proof derives a contradiction by:
   (a) 2 ** MIN s t < CARD (Q z)     by modP_card_lower_better
   (b) CARD (Q z) <= 2 ** MIN s t    by modP_card_upper_better_3
   where t = CARD M, s = SQRT (phi k) * ulog n,
         z by poly_unity_special_factor_exists.
*)

(* Theorem: FiniteField r /\ (CARD R = char r) ==>
            !n k. 0 < k /\ 1 < ordz k (char r) /\ char r divides n /\
                  k < char r /\ SUC (LOG2 n) ** 2 <= ordz k n /\
                  poly_intro_range r k n (SQRT (phi k) * SUC (LOG2 n)) ==>
                  perfect_power n (char r) *)
(* Proof:
   Let p = char r, s = SQRT (phi k) * ulog n.
   The goal is: perfect_power n p
   Note prime p                by finite_field_char

   Some assertions:
   Note 1 < p                  by ONE_LT_PRIME
     so n <> 1                 by DIVIDES_ONE, p divides n, 1 < p
   also k <> 1                 by ZN_order_mod_1, 1 < ordz k p
   Thus 1 < n /\ 1 < k         by 0 < n, 0 < k, n <> 1, k <> 1

   If perfect_power n 2,
      then n = 2 ** e for some e     by perfect_power_def
       and prime 2                   by PRIME_2
       but p divides (2 ** e)        by p divides n
        so p = 2                     by prime_divides_prime_power
        or perfect_power n p         by perfect_power n 2

   If ~perfect_power n 2,
      Note 0 < a               by ulog_pos, 1 < n
        so ordz k n <> 0       by 0 < a <= ordz k n
      Thus coprime n k         by ZN_order_eq_0, by 0 < k

      Let t = CARD M.
      Note n IN N              by setN_element, GCD_SYM, coprime n k, poly_intro_range r k n s

      Claim: 1 < n /\ 1 < k
      Proof: Note 1 < p              by ONE_LT_PRIME, prime p.
               so k <> 1             by ZN_order_mod_1, 1 < ordz k p, 1 < p
              and n <> 1             by DIVIDES_ONE, p divides n, 1 < p
             Thus k <> 0 /\ n <> 0   by coprime_0L, coprime_0R
               or 1 < n /\ 1 < k     by both not 0 and not 1

      Thus 0 < k                     by 1 < k
       ==> ?z. mifactor z (unity k) /\ (deg z = ordz k p) /\ (forderz X = k)
                                     by poly_unity_special_factor_exists, 0 < k, 1 < ordz k p
      Now we can talk about (Q z),
      and derive two incompatible claims about its cardinality.

      The first claim just requires ~perfect_power n 2.
      Claim: 2 ** MIN s t < CARD (Q z)       as [A]
      Proof: In order to apply modP_card_lower_better, need to show:
             (1) 0 < s /\ s < p
                 Note 0 < s                  by sqrt_phi_times_ulog, 0 < k, 1 < n
                  and s <= phi k             by ZN_order_condition_property_2, 1 < n, coprime k n
                  and phi k < k              by phi_lt, 1 < k
                   so s < k                  by above
                   or s < p                  by k < p = char r
             (2) 1 < t
                 Note n <> 2                 by perfect_power_self], ~perfect_power n 2
                  ==> 1 < (ulog n) ** 2      by ulog_sq_gt_1, 2 < n
                 Thus 1 < ordz k n           by 1 < (ulog n) ** 2 <= ordz k n
                  and ordz k n <= t          by modN_card_lower, 1 < ordz k n, n IN N
                   so 1 < t                  by 1 < ordz k n <= t

      The second claim just requires ~perfect_power n p.
      Claim: CARD (Q z) <= 2 ** MIN s t      as [B]
      Proof: Note coprime k p                by coprime_prime_factor_coprime, prime p, p divides n, coprime n k
             Thus CARD (Q z) <= 2 ** MIN s t by modP_card_upper_better_3, coprime k p

      Since [A] and [B] are contradictory, the proof is complete.
*)

(* Theorem: The AKS Main Theorem (no mention of FiniteField, but mentions (ZN n))
   Given a number n > 1,
   If there are numbers k and s such that:
      1 < k, order of n in (ZN k) >= (log n)^2
      s = sqrt(phi k) (log n)
      for all nonzero j <= k, coprime j n
      for all nonzero c <= s, poly_intro (ZN n) k n (zx+ c)
   Then n must be a perfect power of a prime p.
*)
(* Theorem: 1 < n /\ 0 < k /\ (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\
            ulog n ** 2 <= ordz k n /\ poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n)
        ==> ?p. prime p /\ perfect_power n p *)
(* Proof:
   If prime n
      Take p = n, then perfect_power n p     by perfect_power_self
   If ~prime n,
      Then n <> 2                            by PRIME_2
      Thus 2 < n                             by 1 < n, n <> 2
        so 1 < (ulog n) ** 2                 by ulog_sq_gt_1, 2 < n
        or 1 < ordz k n                      by 1 < (ulog n) ** 2 <= ordz k n
       ==> ?p. prime p /\ p divides n /\ 1 < ordz k p
                                             by ZN_order_gt_1_property, 0 < k, 1 < ordz k n
      Take this prime p.
      Some assertions:
      Note 1 < p             by ONE_LT_PRIME
       and k < p             by otherwise, 1 < p /\ p <= k ==> ~(p divides n)
      also k <> 1            by ZN_order_mod_1, 1 < ordz k p, 1 < p
        so 1 < k             by 0 < k, k <> 1

       Let s = SQRT (phi k) * (ulog n).
      Note coprime k n       by coprime_by_le_not_divides, 1 < k
       and s <= phi k        by ZN_order_condition_property_2, 1 < n, coprime k n
       and phi k < k         by 1 < k
        so s < p             by s <= phi k, phi k < k, k < p

       Now poly_intro_range (ZN n) k n s    by given
        so poly_intro_range (ZN p) k n s    by ring_homo_intro_ZN_to_ZN_X_add_c, 1 < k, s < p

      Note FiniteField (ZN p)         by ZN_finite_field, prime p
       and char (ZN p) = p            by ZN_char, 0 < p
       and CARD (ZN p).carrier = p    by ZN_card
       ==> perfect_power n p          by AKS_main_ulog_2b, k < p
*)
val AKS_main_ulog_3b = store_thm(
  "AKS_main_ulog_3b",
  ``!n k. 1 < n /\ 0 < k /\ (* 1 < n to squeeze 2 < n *)
         (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\ (* check on k, gives k < p later *)
         (ulog n) ** 2 <= ordz k n /\ (* condition on k and n *)
         poly_intro_range (ZN n) k n (SQRT (phi k) * (ulog n)) (* AKS tests *)
     ==> ?p. prime p /\ perfect_power n p``,
  rpt strip_tac >>
  Cases_on `prime n` >-
  metis_tac[perfect_power_self] >>
  `n <> 2` by metis_tac[PRIME_2] >>
  `?p. prime p /\ p divides n /\ 1 < ordz k p` by
  (`1 < (ulog n) ** 2` by rw[ulog_sq_gt_1] >>
  `1 < ordz k n` by decide_tac >>
  rw[ZN_order_gt_1_property]) >>
  qexists_tac `p` >>
  simp[] >>
  `0 < n` by decide_tac >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `k < p` by metis_tac[NOT_LESS] >>
  `k <> 1` by metis_tac[ZN_order_mod_1, LESS_NOT_EQ] >>
  `1 < k` by decide_tac >>
  qabbrev_tac `s = SQRT (phi k) * (ulog n)` >>
  `s < p` by
    (`coprime k n` by rw[coprime_by_le_not_divides] >>
  `s <= phi k` by metis_tac[ZN_order_condition_property_2] >>
  `phi k < k` by rw[phi_lt] >>
  decide_tac) >>
  `poly_intro_range (ZN p) k n s` by metis_tac[ring_homo_intro_ZN_to_ZN_X_add_c] >>
  `FiniteField (ZN p)` by rw[ZN_finite_field] >>
  `char (ZN p) = p` by rw[ZN_char] >>
  `CARD (ZN p).carrier = p` by rw[ZN_card] >>
  metis_tac[AKS_main_ulog_2b]);

(* Theorem: The AKS Main Theorem (primality testing version)
   A number n is prime iff
     n > 1, and power-free n,
     there is number k such that:
      1 < k
      and order of n in (ZN k) >= (log n)^2
      and for all nonzero j < MIN (SUC k) n, ~(j divides n)  (with MIN hidden)
      and if k < n, let s = sqrt(phi k) (log n),
          then for all nonzero c <= s, poly_intro (ZN n) k n (zx+ c)
*)
(* Theorem: prime n <=> power_free n /\
            ?k. 0 < k /\ ulog n ** 2 <= ordz k n /\
              (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
              (k < n ==> poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n)) *)
(* Proof:
   If part: prime n ==> power_free n /\ (?k. ... )
      This is to show:
      (1) prime n ==> power_free n, true      by prime_is_power_free
      (2) ?k. 1 < k /\ ...
          If n = 2,
             Then ulog 2 = 1                  by ulog_2
             Take k = 3.
             Note (2 ** 1) MOD 3 = 2          by EXP_1
              and (2 ** 2) MOD 3 = 1          by EXP_2
              and !j. 0 < j /\ j < 2 <=> (j = 1)   by range
             Thus ordz 3 2 = 2                by ZN_order_test_1
             Also !j. 1 < j /\ j <= 3 /\ j < 2  has no valid j,
              and 3 > 2, so there is no polynomial introspective check.
          If n <> 2,
          Let a = (ulog n) ** 2
          Note 1 < n                          by ONE_LT_PRIME
           and 1 < a                          by ulog_sq_gt_1, 2 < n
            so ?k. 1 < k /\ coprime k n /\ m <= ordz k n
                                              by ZN_order_good_enough, 1 < n, 1 < a
          Take this k, let s = SQRT (phi k) * (ulog n).
          The subgoals are:
          (1) prime n /\ 0 < j /\ j <= k /\ j < n ==> ~(j divides n)
              Ignore j <= k, this is true     by prime_def
          (2) prime n /\ 0 < c /\ c <= s ==> poly_intro (ZN n) k n (x+ n c)
              Note 0 < k                      by 1 < k
               and Ring (ZN n)                by ZN_ring, 0 < n
               and char (ZN n) = n            by ZN_char, 0 < n
               ==> poly_intro (ZN n) k n (x+ n c)  by poly_intro_X_add_c_prime_char, 0 < k

   Only-if part: power_free n /\ (?k. 1 < k /\ ... ) ==> prime n
      Note 1 < n                              by power_free_gt_1
      If k < n,
         Let s = SQRT (phi k) * (ulog n).
         (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) becomes
         (!j. 0 < j /\ j <= k ==> ~(j divides n))       as j <= k /\ k < n ==> j < n
         with poly_intro_range (ZN n) k n s
          ==> ?p. prime p /\ perfect_power n p          by AKS_main_ulog_3b
          But power_free n ==> p = n                    by power_free_perfect_power
          Hence prime n.
      Otherwise, ~(k < n),
         (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) becomes
         (!j. 0 < j /\ j < n ==> ~(j divides n))        as j < n /\ n <= k ==> j < k, or j <= k
          Hence prime n                                 by prime_iff_no_proper_factor
*)
val AKS_main_ulog_7b = store_thm(
  "AKS_main_ulog_7b",
  ``!n. prime n <=> power_free n /\
   ?k. 0 < k /\ (ulog n) ** 2 <= ordz k n /\
       (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
       (k < n ==> poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n))``,
  rw_tac bool_ss[EQ_IMP_THM] >-
  rw[prime_is_power_free] >-
 (qabbrev_tac `a = (ulog n) ** 2` >>
  `1 < n` by rw[ONE_LT_PRIME] >>
  Cases_on `n = 2` >| [
    `a = 1` by rw[ulog_2, Abbr`a`] >>
    qexists_tac `3` >>
    simp[] >>
    `(2 ** 1) MOD 3 = 2` by rw[] >>
    `(2 ** 2) MOD 3 = 1` by rw[] >>
    `1 < 3 /\ 0 < 2 /\ 2 <> 1 /\ 0 <> 1 /\ !j. 0 < j /\ j < 2 <=> (j = 1)` by decide_tac >>
    `ordz 3 2 = 2` by metis_tac[ZN_order_test_1] >>
    decide_tac,
    `1 < a` by rw[ulog_sq_gt_1, Abbr`a`] >>
    `?k. 1 < k /\ coprime k n /\ a <= ordz k n` by rw[ZN_order_good_enough] >>
    qexists_tac `k` >>
    qabbrev_tac `s = SQRT (phi k) * (ulog n)` >>
    (rw_tac std_ss[] >> simp[]) >-
    metis_tac[prime_def, LESS_NOT_EQ] >>
    `0 < k` by decide_tac >>
    `Ring (ZN n)` by rw[ZN_ring] >>
    `char (ZN n) = n` by rw[ZN_char] >>
    metis_tac[poly_intro_X_add_c_prime_char, ZN_property]
  ]) >>
  `1 < n` by rw[power_free_gt_1] >>
  Cases_on `k < n` >| [
    `!j. 1 < j /\ j <= k ==> 1 < j /\ j <= k /\ j < n` by decide_tac >>
    metis_tac[AKS_main_ulog_3b, power_free_perfect_power],
    `!j. 1 < j /\ j < n ==> 1 < j /\ j <= k /\ j < n` by decide_tac >>
    metis_tac[prime_iff_no_proper_factor]
  ]);

(* Theorem: This is previous version with poly_intro made explicit:
            prime n <=> power_free n /\
            ?k. 0 < k /\ ulog n ** 2 <= ordz k n /\
                (!j. 0 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                (k < n ==> poly_intro_checks n k (SQRT (phi k) * ulog n)) *)
(* Proof:
   Note  1 < n ==> 0 < n                              by arithmetic
   also  power_free n ==> 1 < n ==> 0 < n             by power_free_gt_1
    and  0 < n ==> Ring (ZN n)                        by ZN_ring, 0 < n
   together with poly_intro_X_add_c, this is true     by AKS_main_ulog_7b
*)
val AKS_main_ulog_8b = store_thm(
  "AKS_main_ulog_8b",
  ``!n. prime n <=> power_free n /\
   ?k. 0 < k /\ (ulog n) ** 2 <= ordz k n /\ (* property of k *)
       (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\ (* checks on k, hidden MIN *)
       (k < n ==> poly_intro_checks n k (SQRT (phi k) * ulog n))``,
  rpt strip_tac >>
  `!n. 1 < n ==> 0 < n` by decide_tac >>
  `!n. 0 < n ==> Ring (ZN n)` by rw[ZN_ring] >>
  metis_tac[AKS_main_ulog_7b, poly_intro_X_add_c, power_free_gt_1]);

(* ------------------------------------------------------------------------- *)
(* Using passChecks                                                          *)
(* ------------------------------------------------------------------------- *)

(* Overload to simplify presentation *)
(* val _ = overload_on("passChecks",
  ``\(r:'a ring) n a k s.
         (char r) divides n /\ k < char r /\ a <= ordz k n /\ poly_intro_range r k n s``); *)
(* val _ = clear_overloads_on "passChecks"; *)

(* Use lowercase aks_main_thm with AKS_main_thm as they are really similar. *)

val aks_main_thm_0b = store_thm(
  "aks_main_thm_0b",
  ``!(r:'a field) k z. FiniteField r /\ (CARD R = char r) /\ (* simple field *)
          1 < ordz k (char r) /\ (* additional condition for using q = n DIV p *)
          mifactor z (unity k) /\ (forderz X = k) ==>
   !n a s. 1 < k /\ (a = (SUC (LOG2 n)) ** 2) /\
           (s = SQRT (phi k) * (SUC (LOG2 n))) /\
           passChecks r n a k s
       ==> perfect_power n (char r)``,
  metis_tac[AKS_main_thm_0b]);

val aks_main_thm_0b_alt = store_thm(
  "aks_main_thm_0b_alt",
  ``!(r:'a field) k z. FiniteField r /\ (CARD R = char r) /\ 1 < ordz k (char r) /\
           mifactor z (unity k) /\ 1 < deg z /\ (forderz X = k) ==>
   !n a s. (a = (SUC (LOG2 n)) ** 2) /\
           (s = SQRT (phi k) * (SUC (LOG2 n))) /\
           passChecks r n a k s ==>
           perfect_power n (char r)``,
  metis_tac[AKS_main_thm_0b_alt]);

val aks_main_thm_1b = store_thm(
  "aks_main_thm_1b",
  ``!(r:'a field) k z. FiniteField r /\ (CARD R = char r) /\ 1 < ordz k (char r) /\
           mifactor z (unity k) /\ (forderz X = k) ==>
   !n a s. 0 < n /\ 0 < k /\ (a = (SUC (LOG2 n)) ** 2) /\
           (s = SQRT (phi k) * (SUC (LOG2 n))) /\
           passChecks r n a k s
       ==> perfect_power n (char r)``,
  metis_tac[AKS_main_thm_1b]);

val aks_main_thm_2b = store_thm(
  "aks_main_thm_2b",
  ``!(r:'a field). FiniteField r /\ (CARD R = char r) ==>
   !n a k s. 0 < k /\ 1 < ordz k (char r) /\
             (a = (SUC (LOG2 n)) ** 2) /\
             (s = SQRT (phi k) * (SUC (LOG2 n))) /\
             passChecks r n a k s
         ==> perfect_power n (char r)``,
  metis_tac[AKS_main_thm_2b]);

val aks_main_thm_3b = store_thm(
  "aks_main_thm_3b",
  ``!n a k s. 1 < n /\ 0 < k /\ (a = (SUC (LOG2 n)) ** 2) /\
             (s = SQRT (phi k) * (SUC (LOG2 n))) /\
             (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\
             a <= ordz k n /\ poly_intro_range (ZN n) k n s
         ==> ?p. prime p /\ perfect_power n p``,
  metis_tac[AKS_main_thm_3b]);

val aks_main_thm_7b = store_thm(
  "aks_main_thm_7b",
  ``!n. prime n <=> power_free n /\
   ?a k s. 0 < k /\ (a = (SUC (LOG2 n)) ** 2) /\
           (s = SQRT (phi k) * (SUC (LOG2 n))) /\
           (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\ a <= ordz k n /\
           (k < n ==> poly_intro_range (ZN n) k n s)``,
  metis_tac[AKS_main_thm_7b]);

val aks_main_thm_8b = store_thm(
  "aks_main_thm_8b",
  ``!n. prime n <=> power_free n /\
   ?a k s. 0 < k /\ (a = (SUC (LOG2 n)) ** 2) /\
            (s = SQRT (phi k) * (SUC (LOG2 n))) /\
            (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\ a <= ordz k n /\
            (k < n ==> poly_intro_checks n k s)``,
  metis_tac[AKS_main_thm_8b]);

val aks_main_ulog_0b = store_thm(
  "aks_main_ulog_0b",
  ``!(r:'a field) k z. FiniteField r /\ (CARD R = char r) /\ 1 < ordz k (char r) /\
           mifactor z (unity k) /\ (forderz X = k) ==>
   !n a s. 0 < n /\ 1 < k /\ (* 0 < n to keep 0 < a *)
           (a = (ulog n) ** 2) /\
           (s = SQRT (phi k) * ulog n) /\
           passChecks r n a k s
       ==> perfect_power n (char r)``,
  metis_tac[AKS_main_ulog_0b]);

val aks_main_ulog_0b_alt = store_thm(
  "aks_main_ulog_0b_alt",
  ``!(r:'a field) k z. FiniteField r /\ (CARD R = char r) /\ 1 < ordz k (char r) /\
           mifactor z (unity k) /\ 1 < deg z /\ (forderz X = k) ==>
   !n a s. 0 < n /\ (* 0 < n to keep 0 < a *)
           (a = (ulog n) ** 2) /\
           (s = SQRT (phi k) * ulog n) /\
           passChecks r n a k s
       ==> perfect_power n (char r)``,
  metis_tac[AKS_main_ulog_0b_alt]);

val aks_main_ulog_1b = store_thm(
  "aks_main_ulog_1b",
  ``!(r:'a field) k z. FiniteField r /\ (CARD R = char r) /\ 1 < ordz k (char r) /\
           mifactor z (unity k) /\ (forderz X = k) ==>
   !n a s. 0 < n /\ 0 < k /\ (a = (ulog n) ** 2) /\
           (s = SQRT (phi k) * ulog n) /\
           passChecks r n a k s
       ==> perfect_power n (char r)``,
  metis_tac[AKS_main_ulog_1b]);

val aks_main_ulog_2b = store_thm(
  "aks_main_ulog_2b",
  ``!r:'a field. FiniteField r /\ (CARD R = char r) ==>
   !n a k s. 0 < n /\ 0 < k /\ 1 < ordz k (char r) /\
             (a = (ulog n) ** 2) /\
             (s = SQRT (phi k) * ulog n) /\
             passChecks r n a k s
         ==> perfect_power n (char r)``,
  metis_tac[AKS_main_ulog_2b]);

val aks_main_ulog_3b = store_thm(
  "aks_main_ulog_3b",
  ``!n a k s. 1 < n /\ 0 < k /\
             (a = (ulog n) ** 2) /\
             (s = SQRT (phi k) * ulog n) /\
             (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\
             a <= ordz k n /\ poly_intro_range (ZN n) k n s
         ==> ?p. prime p /\ perfect_power n p``,
  metis_tac[AKS_main_ulog_3b]);

val aks_main_ulog_7b = store_thm(
  "aks_main_ulog_7b",
  ``!n. prime n <=> power_free n /\
   ?a k s. 0 < k /\ (a = (ulog n) ** 2) /\
           (s = SQRT (phi k) * ulog n) /\ a <= ordz k n /\
           (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
           (k < n ==> poly_intro_range (ZN n) k n s)``,
  metis_tac[AKS_main_ulog_7b]);

val aks_main_ulog_8b = store_thm(
  "aks_main_ulog_8b",
  ``!n. prime n <=> power_free n /\
   ?a k s. 0 < k /\ (a = (ulog n) ** 2) /\
           (s = SQRT (phi k) * ulog n) /\ a <= ordz k n /\
           (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
           (k < n ==> poly_intro_checks n k s)``,
  metis_tac[AKS_main_ulog_8b]);



(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
