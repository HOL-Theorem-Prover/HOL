(* ------------------------------------------------------------------------- *)
(* AKS Main Theorem.                                                         *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "AKStheorem";

(* ------------------------------------------------------------------------- *)

open jcLib;

(* open dependent theories *)
open prim_recTheory pred_setTheory listTheory arithmeticTheory logrootTheory
     dividesTheory gcdTheory numberTheory listRangeTheory combinatoricsTheory
     primeTheory;

(* Get dependent theories local *)
open AKSmapsTheory;
open AKSsetsTheory;
open AKSintroTheory;
open AKSshiftTheory;

open computeRingTheory;
open computeParamTheory;

open monoidTheory groupTheory ringTheory ringUnitTheory;

open fieldTheory;

(* Get polynomial theory of Ring *)
open polynomialTheory polyWeakTheory polyRingTheory polyDivisionTheory
     polyBinomialTheory;

open polyMonicTheory;

open polyFieldTheory;
open polyFieldDivisionTheory;
open polyFieldModuloTheory;
open polyIrreducibleTheory;
open polyCyclicTheory;

open subgroupTheory;
open groupOrderTheory;

open ringBinomialTheory;
open ringDividesTheory;

open groupInstancesTheory;
open ringInstancesTheory;
open fieldInstancesTheory;

open ffBasicTheory;
open ffAdvancedTheory;
open ffPolyTheory;
open ffUnityTheory;
open ffExistTheory;

val _ = temp_overload_on("SQ", ``\n. n * (n :num)``);
val _ = temp_overload_on("HALF", ``\n. n DIV 2``);
val _ = temp_overload_on("TWICE", ``\n. 2 * n``);

(* ------------------------------------------------------------------------- *)
(* AKS Main Theorem Documentation                                            *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   passChecks r n a k s = (char r) divides n /\ k < char r /\
                          a <= ordz k n /\ poly_intro_range r k n s
*)
(* Definitions and Theorems (# are exported):

   Helper:
   TWICE_SQRT_TIMES_SUC_LOG2 |- !k n. 0 < k ==> 0 < TWICE (SQRT (phi k)) * SUC (LOG2 n)
   sqrt_phi_times_ulog       |- !k n. 0 < k /\ 1 < n ==> 0 < SQRT (phi k) * ulog n
   sqrt_phi_times_ulog_le    |- !n k. 0 < k /\ 1 < n /\ coprime k n /\
                                      ulog n ** 2 <= ordz k n ==>
                                      SQRT (phi k) * ulog n <= phi k
   sqrt_phi_times_ulog_less  |- !n k. 0 < k /\ 1 < n /\ coprime k n /\
                                      ulog n ** 2 <= ordz k n ==>
                                      SQRT (phi k) * ulog n <= k
   sqrt_phi_times_ulog_lt    |- !n k. 1 < k /\ 1 < n /\ coprime k n /\
                                      ulog n ** 2 <= ordz k n ==>
                                      SQRT (phi k) * ulog n < k

   AKS Main Theorem:
   AKS_main_thm_0    |- !r k z. FiniteField r /\ mifactor z (unity k) /\ forderz X = k ==>
                        !n. 1 < k /\ char r divides n /\ k < char r /\
                            TWICE (SUC (LOG2 n)) ** 2 <= ordz k n /\
                            poly_intro_range r k n (TWICE (SQRT (phi k)) * SUC (LOG2 n)) ==>
                            perfect_power n (char r)

   AKS_main_thm_0_alt|- !r k z. FiniteField r /\ mifactor z (unity k) /\ 1 < deg z /\ forderz X = k ==>
                        !n. char r divides n /\ k < char r /\
                            TWICE (SUC (LOG2 n)) ** 2 <= ordz k n /\
                            poly_intro_range r k n (TWICE (SQRT (phi k)) * SUC (LOG2 n)) ==>
                            perfect_power n (char r)

   AKS_main_thm_1    |- !r k z. FiniteField r /\ mifactor z (unity k) /\ forderz X = k ==>
                        !n. 0 < k /\ char r divides n /\ k < char r /\
                            TWICE (SUC (LOG2 n)) ** 2 <= ordz k n /\
                            poly_intro_range r k n (TWICE (SQRT (phi k)) * SUC (LOG2 n)) ==>
                            perfect_power n (char r)

   AKS_main_thm_2    |- !r n k. FiniteField r /\ prime k /\ char r divides n /\ k < char r /\
                                TWICE (SUC (LOG2 n)) ** 2 <= ordz k n /\
                                poly_intro_range r k n (TWICE (SQRT (phi k)) * SUC (LOG2 n)) ==>
                                perfect_power n (char r)

   AKS_main_thm_3    |- !n k. 1 < n /\ prime k /\ (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\
                              TWICE (SUC (LOG2 n)) ** 2 <= ordz k n /\
                              poly_intro_range (ZN n) k n (TWICE (SQRT (phi k)) * SUC (LOG2 n)) ==>
                          ?p. prime p /\ perfect_power n p

   AKS_main_thm_4    |- !n. power_free n ==>
                        !k. prime k /\ TWICE (SUC (LOG2 n)) ** 2 <= ordz k n /\ k < n ==>
                           (prime n <=> (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\
                            poly_intro_range (ZN n) k n (TWICE (SQRT (phi k)) * SUC (LOG2 n)))

   AKS_main_thm_5    |- !n k. power_free n /\ prime k /\ TWICE (SUC (LOG2 n)) ** 2 <= ordz k n /\
                              (!j. 1 < j /\ j <= MIN k n ==> ~(j divides n)) ==>
                              (prime n <=> k < n /\
                               poly_intro_range (ZN n) k n (TWICE (SQRT (phi k)) * SUC (LOG2 n)))

   AKS_main_thm_6    |- !n k. prime k /\ TWICE (SUC (LOG2 n)) ** 2 <= ordz k n /\
                              (!j. 1 < j /\ j <= MIN k n ==> ~(j divides n)) ==>
                              (prime n <=> power_free n /\ k < n /\
                               poly_intro_range (ZN n) k n (TWICE (SQRT (phi k)) * SUC (LOG2 n)))

   AKS_main_thm_7    |- !n. prime n <=> power_free n /\
                        ?k. prime k /\ TWICE (SUC (LOG2 n)) ** 2 <= ordz k n /\
                            (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                            (k < n ==> poly_intro_range (ZN n) k n (TWICE (SQRT (phi k)) * SUC (LOG2 n)))
   AKS_main_thm_8    |- !n. prime n <=> power_free n /\
                        ?k. prime k /\ TWICE (SUC (LOG2 n)) ** 2 <= ordz k n /\
                            (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                            (k < n ==> poly_intro_checks n k (TWICE (SQRT (phi k)) * SUC (LOG2 n)))

   AKS_main_thm_if   |- !n. prime n ==> power_free n /\
                        ?k. prime k /\ TWICE (SUC (LOG2 n)) ** 2 <= ordz k n /\
                            (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                            (k < n ==> poly_intro_range (ZN n) k n (TWICE (SQRT (phi k)) * SUC (LOG2 n)))
   AKS_main_thm_only_if
                     |- !n. power_free n /\
                            (?k. prime k /\ TWICE (SUC (LOG2 n)) ** 2 <= ordz k n /\
                            (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                            (k < n ==> poly_intro_range (ZN n) k n (TWICE (SQRT (phi k)) * SUC (LOG2 n))))
                        ==> prime n

   AKS Main Theorem based on upper logarithm:
   AKS_main_ulog_0     |- !r k z. FiniteField r /\ mifactor z (unity k) /\ forderz X = k ==>
                          !n. 0 < n /\ 1 < k /\ char r divides n /\ k < char r /\
                              TWICE (ulog n) ** 2 <= ordz k n /\
                              poly_intro_range r k n (TWICE (SQRT (phi k)) * ulog n) ==>
                              perfect_power n (char r)
   AKS_main_ulog_0_alt |- !r k z. FiniteField r /\ mifactor z (unity k) /\ 1 < deg z /\ forderz X = k ==>
                          !n. 0 < n /\ char r divides n /\ k < char r /\
                              TWICE (ulog n) ** 2 <= ordz k n /\
                              poly_intro_range r k n (TWICE (SQRT (phi k)) * ulog n) ==>
                              perfect_power n (char r)
   AKS_main_ulog_1     |- !r k z. FiniteField r /\ mifactor z (unity k) /\ forderz X = k ==>
                          !n. 0 < n /\ 0 < k /\ char r divides n /\ k < char r /\
                              TWICE (ulog n) ** 2 <= ordz k n /\
                              poly_intro_range r k n (TWICE (SQRT (phi k)) * ulog n) ==>
                              perfect_power n (char r)
   AKS_main_ulog_2     |- !r n k. FiniteField r /\ 0 < n /\ prime k /\ char r divides n /\
                                  k < char r /\ TWICE (ulog n) ** 2 <= ordz k n /\
                                  poly_intro_range r k n (TWICE (SQRT (phi k)) * ulog n) ==>
                                  perfect_power n (char r)
   AKS_main_ulog_3     |- !n k. 1 < n /\ prime k /\ (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\
                                TWICE (ulog n) ** 2 <= ordz k n /\
                                poly_intro_range (ZN n) k n (TWICE (SQRT (phi k)) * ulog n) ==>
                            ?p. prime p /\ perfect_power n p
   AKS_main_ulog_4     |- !n. power_free n ==>
                          !k. prime k /\ TWICE (ulog n) ** 2 <= ordz k n /\ k < n ==>
                             (prime n <=> (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\
                              poly_intro_range (ZN n) k n (TWICE (SQRT (phi k)) * ulog n))
   AKS_main_ulog_5     |- !n k. power_free n /\ prime k /\ TWICE (ulog n) ** 2 <= ordz k n /\
                                (!j. 1 < j /\ j <= MIN k n ==> ~(j divides n)) ==>
                                (prime n <=> k < n /\
                                 poly_intro_range (ZN n) k n (TWICE (SQRT (phi k)) * ulog n))
   AKS_main_ulog_6     |- !n k. prime k /\ TWICE (ulog n) ** 2 <= ordz k n /\
                                (!j. 1 < j /\ j <= MIN k n ==> ~(j divides n)) ==>
                                (prime n <=> power_free n /\ k < n /\
                                 poly_intro_range (ZN n) k n (TWICE (SQRT (phi k)) * ulog n))
   AKS_main_ulog_7     |- !n. prime n <=> power_free n /\
                          ?k. prime k /\ TWICE (ulog n) ** 2 <= ordz k n /\
                              (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                              (k < n ==>
                               poly_intro_range (ZN n) k n (TWICE (SQRT (phi k)) * ulog n))
   AKS_main_ulog_8     |- !n. prime n <=> power_free n /\
                          ?k. prime k /\ TWICE (ulog n) ** 2 <= ordz k n /\
                              (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                              (k < n ==>
                               poly_intro_checks n k (TWICE (SQRT (phi k)) * ulog n))

   Using passChecks:
   aks_main_thm_0      |- !r k z. FiniteField r /\ mifactor z (unity k) /\ (forderz X = k) ==>
                          !n a s. 1 < k /\ (a = TWICE (SUC (LOG2 n)) ** 2) /\
                                  (s = TWICE (SQRT (phi k)) * SUC (LOG2 n)) /\
                                  passChecks r n a k s ==> perfect_power n (char r)
   aks_main_thm_0_alt  |- !r k z. FiniteField r /\
                                  mifactor z (unity k) /\ 1 < deg z /\ (forderz X = k) ==>
                          !n a s. (a = TWICE (SUC (LOG2 n)) ** 2) /\
                                  (s = TWICE (SQRT (phi k)) * SUC (LOG2 n)) /\
                                  passChecks r n a k s ==> perfect_power n (char r)
   aks_main_thm_1      |- !r k z. FiniteField r /\ mifactor z (unity k) /\ (forderz X = k) ==>
                          !n a s. 0 < k /\ (a = TWICE (SUC (LOG2 n)) ** 2) /\
                                  (s = TWICE (SQRT (phi k)) * SUC (LOG2 n)) /\
                                  passChecks r n a k s ==> perfect_power n (char r)
   aks_main_thm_2      |- !r n a k s. FiniteField r /\ prime k /\
                                      (a = TWICE (SUC (LOG2 n)) ** 2) /\
                                      (s = TWICE (SQRT (phi k)) * SUC (LOG2 n)) /\
                                      passChecks r n a k s ==> perfect_power n (char r)
   aks_main_thm_3      |- !n a k s. 1 < n /\ prime k /\ (a = TWICE (SUC (LOG2 n)) ** 2) /\
                                    (s = TWICE (SQRT (phi k)) * SUC (LOG2 n)) /\
                                    (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\
                                    a <= ordz k n /\ poly_intro_range (ZN n) k n s ==>
                                ?p. prime p /\ perfect_power n p
   aks_main_thm_7      |- !n. prime n <=> power_free n /\
                          ?a k s. (a = TWICE (SUC (LOG2 n)) ** 2) /\ prime k /\
                                  (s = TWICE (SQRT (phi k)) * SUC (LOG2 n)) /\ a <= ordz k n /\
                                  (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                                  (k < n ==> poly_intro_range (ZN n) k n s)
   aks_main_thm_8      |- !n. prime n <=> power_free n /\
                          ?a k s. (a = TWICE (SUC (LOG2 n)) ** 2) /\ prime k /\
                                  (s = TWICE (SQRT (phi k)) * SUC (LOG2 n)) /\ a <= ordz k n /\
                                  (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                                  (k < n ==> poly_intro_checks n k s)

   aks_main_ulog_0     |- !r k z. FiniteField r /\ mifactor z (unity k) /\ (forderz X = k) ==>
                          !n a s. 1 < k /\ 0 < n /\ (a = TWICE (ulog n) ** 2) /\
                                  (s = TWICE (SQRT (phi k)) * ulog n) /\
                                  passChecks r n a k s ==> perfect_power n (char r)
   aks_main_ulog_0_alt |- !r k z. FiniteField r /\
                                  mifactor z (unity k) /\ 1 < deg z /\ (forderz X = k) ==>
                          !n a s. 0 < n /\ (a = TWICE (ulog n) ** 2) /\
                                  (s = TWICE (SQRT (phi k)) * ulog n) /\
                                  passChecks r n a k s ==> perfect_power n (char r)
   aks_main_ulog_1     |- !r k z. FiniteField r /\ mifactor z (unity k) /\ (forderz X = k) ==>
                          !n a s. 0 < n /\ 0 < k /\ (a = TWICE (ulog n) ** 2) /\
                                  (s = TWICE (SQRT (phi k)) * ulog n) /\
                                  passChecks r n a k s ==> perfect_power n (char r)
   aks_main_ulog_2     |- !r n a k s. FiniteField r /\ 0 < n /\ prime k /\
                                      (a = TWICE (ulog n) ** 2) /\
                                      (s = TWICE (SQRT (phi k)) * ulog n) /\
                                      passChecks r n a k s ==> perfect_power n (char r)
   aks_main_ulog_3     |- !n a k s. 1 < n /\ prime k /\ (a = TWICE (ulog n) ** 2) /\
                                    (s = TWICE (SQRT (phi k)) * ulog n) /\
                                    (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\
                                    a <= ordz k n /\ poly_intro_range (ZN n) k n s ==>
                                ?p. prime p /\ perfect_power n p
   aks_main_ulog_7     |- !n. prime n <=> power_free n /\
                          ?a k s. (a = TWICE (ulog n) ** 2) /\ prime k /\
                                  (s = TWICE (SQRT (phi k)) * ulog n) /\ a <= ordz k n /\
                                  (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                                  (k < n ==> poly_intro_range (ZN n) k n s)
   aks_main_ulog_8     |- !n. prime n <=> power_free n /\
                          ?a k s. (a = TWICE (ulog n) ** 2) /\ prime k /\
                                  (s = TWICE (SQRT (phi k)) * ulog n) /\ a <= ordz k n /\
                                  (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                                  (k < n ==> poly_intro_checks n k s)
*)

(* ------------------------------------------------------------------------- *)
(* Helpers                                                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < k ==> 0 < TWICE (SQRT (phi k)) * SUC (LOG2 n) *)
(* Proof:
   Note phi k <> 0                              by phi_eq_0, 0 < k
   Thus SQRT (phi k) <> 0                       by SQRT_EQ_0
    and 2 * (SQRT (phi k)) <> 0                 by MULT_EQ_0
   Also SUC (LOG2 n) <> 0                       by SUC_NOT
    ==> 2 * (SQRT (phi k)) * SUC (LOG2 n) <> 0  by MULT_EQ_0
*)
val TWICE_SQRT_TIMES_SUC_LOG2 = store_thm(
  "TWICE_SQRT_TIMES_SUC_LOG2",
  ``!k n. 0 < k ==> 0 < TWICE (SQRT (phi k)) * SUC (LOG2 n)``,
  rpt strip_tac >>
  `0 < SUC (LOG2 n)` by rw[] >>
  `0 < SQRT (phi k)` by metis_tac[phi_eq_0, SQRT_EQ_0, NOT_ZERO] >>
  rw[MULT_POS]);

(* Theorem: 0 < k /\ 1 < n ==> 0 < SQRT (phi k) * ulog n *)
(* Proof:
   Note k <> 0                         by 0 < k
     so phi k <> 0                     by phi_eq_0
   Thus SQRT (phi k) <> 0              by SQRT_EQ_0
   Also ulog n <> 0                    by ulog_pos, 1 < n
    ==> SQRT (phi k) * ulog n <> 0     by MULT_EQ_0
*)
val sqrt_phi_times_ulog = store_thm(
  "sqrt_phi_times_ulog",
  ``!k n. 0 < k /\ 1 < n ==> 0 < SQRT (phi k) * ulog n``,
  metis_tac[MULT_EQ_0, phi_eq_0, SQRT_EQ_0, ulog_pos, NOT_ZERO]);

(* Theorem: 0 < k /\ 1 < n /\ coprime k n /\ ulog n ** 2 <= ordz k n ==>
            SQRT (phi k) * ulog n <= phi k *)
(* Proof:
   Let s = SQRT (phi k) * ulog n.
   Then 0 < s                       by sqrt_phi_times_ulog, 0 < k, 1 < n
    and s <= phi k                  by ZN_order_condition_property_2, 1 < n, coprime k n
*)
val sqrt_phi_times_ulog_le = store_thm(
  "sqrt_phi_times_ulog_le",
  ``!n k. 0 < k /\ 1 < n /\ coprime k n /\ ulog n ** 2 <= ordz k n ==>
         SQRT (phi k) * ulog n <= phi k``,
  rw[sqrt_phi_times_ulog, ZN_order_condition_property_2]);

(* Theorem: 0 < k /\ 1 < n /\ coprime k n /\ ulog n ** 2 <= ordz k n ==>
            SQRT (phi k) * ulog n <= k *)
(* Proof:
   Let s = SQRT (phi k) * ulog n.
   Then s <= phi k               by sqrt_phi_times_ulog_le
    and phi k <= k               by phi_le
    ==> s <= k                   by s <= phi k, phi k <= k
*)
val sqrt_phi_times_ulog_less = store_thm(
  "sqrt_phi_times_ulog_less",
  ``!n k. 0 < k /\ 1 < n /\ coprime k n /\ ulog n ** 2 <= ordz k n ==>
         SQRT (phi k) * ulog n <= k``,
  metis_tac[sqrt_phi_times_ulog_le, phi_le, LESS_EQ_TRANS]);

(* Theorem: 1 < k /\ 1 < n /\ coprime k n /\ ulog n ** 2 <= ordz k n ==>
            SQRT (phi k) * ulog n < k *)
(* Proof:
   Let s = SQRT (phi k) * ulog n.
   Then s <= phi k               by sqrt_phi_times_ulog_le
    and phi k < k                by phi_lt, 1 < k
    ==> s < k                    by s <= phi k, phi k < k
*)
val sqrt_phi_times_ulog_lt = store_thm(
  "sqrt_phi_times_ulog_lt",
  ``!n k. 1 < k /\ 1 < n /\ coprime k n /\ ulog n ** 2 <= ordz k n ==>
         SQRT (phi k) * ulog n < k``,
  rpt strip_tac >>
  `SQRT (phi k) * ulog n <= phi k` by rw[sqrt_phi_times_ulog_le] >>
  `phi k < k` by rw[phi_lt] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Note: The constants in this script are based only on n IN N and p IN N.   *)
(*       The constants can be improved using p IN N and (q = n DIV p) IN N.  *)
(* Pros                                                                      *)
(* . any prime p factor of n can be used to build the finite field.          *)
(* . just need 1 < ordz k n, which follows when a <= ordz k n and 1 < a      *)
(* Cons                                                                      *)
(* . constants a, s are twice of the optimal in improved version.            *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* AKS Main Theorem                                                          *)
(* ------------------------------------------------------------------------- *)

(* AKS Main Theorem -- Version 0
   If there is a FiniteField r,
   and (char r) divides the given number n,
   ...
   then n must be a perfect power of (char r).
*)

(* Idea:

With suitable parameters,
MAX p q ** (2 * SQRT (CARD M)) < CARD (Q z) is satisfied,
and INJ (\m. m MOD k) (NM p q (SQRT (CARD M))) M

If prime p /\ p divides q /\ ~perfect_power q p,
      CARD (NM p q (SQRT (CARD M)))
    = (SUC (SQRT (CARD M))) ** 2
    > CARD M                       by n < (SUC (SQRT n)) ** 2
By Pigeonhole Principle, no INJ is possible.
*)

(* Note:
   This basic version does not require  CARD R = char r, 1 < ordz k (char r),
   because it assumes the existence of the special factor z.
   Later, need 1 < ordz k (CARD R) to gives the special factor z.
*)

(* Idea:
   Consider the two sets: (NM p n (SQRT (CARD M))) and M
   If a special z exists, INJ (\m. m MOD k) (NM p n (SQRT (CARD M))) M
   If ~perfect_power n p,     CARD M < CARD (NM p n (SQRT (CARD M)))
   This violates the Pigeonhole Principle.
*)

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
   Let a = (2 * SUC (LOG2 n)) ** 2,
       s = 2 * (SQRT (phi k)) * (SUC (LOG2 n)),
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

      Step 1: Apply modN_card_in_exp_lt_bound_0
      Since n IN N                           by setN_element
      Then n ** (2 * SQRT t) < 2 ** MIN s t  by modN_card_in_exp_lt_bound_0, 1 < k

      Step 2: Apply modP_card_lower_1
      Since 0 < s                            by TWICE_SQRT_TIMES_SUC_LOG2, 0 < k
       Also s <= phi k <= k                  by ZN_order_condition_property, phi_le, 1 < n
         so s < char r                       by given k < char r
      gives 2 ** MIN s t <= CARD (Q z)       by modP_card_lower_1, forderz X = k
      Thus  n ** (2 * SQRT t) < CARD (Q z)   by LESS_LESS_EQ_TRANS

      Step 3: Apply reduceN_mod_modN_inj_0
      Since coprime p k, since prime p       by coprime_prime_factor_coprime
            !c. p intro X + |c|              by poly_intro_X_add_c_prime_char
         so p IN N                           by setN_element
      Hence INJ (\m. m MOD k) (NM p n (SQRT t)) M
                                             by reduceN_mod_modN_inj_1, p IN N, n IN N

      Step 4: Apply reduceN_card
      By contradiction, assume ~perfect_power n p.
      Then CARD (NM p n (SQRT t)) = (SUC (SQRT t)) ** 2    by reduceN_card
      Now  FINITE M                                        by modN_finite
      and  t < (SUC (SQRT t)) ** 2                         by SQRT_PROPERTY
      Overall,  t < CARD (NM p n (SQRT t))

      Step 5: Conclusion
      This violates the Pigeonhole Principle:
      PHP |- !f s t. FINITE t /\ CARD t < CARD s ==> ~INJ f s t

      Therefore, perfect_power n p.
*)
val AKS_main_thm_0 = store_thm(
  "AKS_main_thm_0",
  ``!(r:'a field) k z. FiniteField r /\
          mifactor z (unity k) /\ (forderz X = k) ==>
   !n. 1 < k /\ (char r) divides n /\ k < char r /\
           (2 * SUC (LOG2 n)) ** 2 <= ordz k n /\ (* conditions on n, k *)
           poly_intro_range r k n (2 * (SQRT (phi k)) * (SUC (LOG2 n))) (* AKS tests *)
       ==> perfect_power n (char r)``,
  rpt strip_tac >>
  qabbrev_tac `p = char r` >>
  qabbrev_tac `a = (2 * SUC (LOG2 n)) ** 2` >>
  qabbrev_tac `s = 2 * (SQRT (phi k)) * (SUC (LOG2 n))` >>
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
  `MAX p n = n` by rw[MAX_DEF] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `Field r /\ FINITE R` by metis_tac[FiniteField_def] >>
  `Ring r` by rw[] >>
  qabbrev_tac `t = CARD M` >>
  `n IN N` by rw[setN_element] >>
  `n ** (2 * SQRT t) < 2 ** MIN s t` by rw[modN_card_in_exp_lt_bound_0, Abbr`t`, Abbr`a`, Abbr`s`] >>
  `0 < s` by metis_tac[TWICE_SQRT_TIMES_SUC_LOG2] >>
  `s <= phi k` by rw[ZN_order_condition_property, coprime_sym, Abbr`a`, Abbr`s`] >>
  `phi k <= k` by rw[phi_le] >>
  `s < p` by decide_tac >>
  `2 ** MIN s t <= CARD (Q z)` by rw[modP_card_lower_1, Abbr`t`, Abbr`p`] >>
  `n ** (2 * SQRT t) < CARD (Q z)` by decide_tac >>
  `coprime p k` by metis_tac[coprime_prime_factor_coprime] >>
  `!c:num. p intro X + |c|` by rw[poly_intro_X_add_c_prime_char, Abbr`p`] >>
  `p IN N` by rw[setN_element] >>
  `INJ (\m. m MOD k) (NM p n (SQRT t)) M` by metis_tac[reduceN_mod_modN_inj_1] >>
  spose_not_then strip_assume_tac >>
  `CARD (NM p n (SQRT t)) = (SUC (SQRT t)) ** 2` by metis_tac[reduceN_card] >>
  `FINITE M` by rw[modN_finite] >>
  `t < (SUC (SQRT t)) ** 2` by rw[SQRT_PROPERTY] >>
  `t < CARD (NM p n (SQRT t))` by decide_tac >>
  metis_tac[PHP]);
(* This is the original version based on forderz X = k. *)

(* Theorem: The AKS Main Theorem (Version 0) *)
(* Proof:
   Note 1 < k           by poly_X_order_gt_1
   The result follows   by AKS_main_thm_0
*)
val AKS_main_thm_0_alt = store_thm(
  "AKS_main_thm_0_alt",
  ``!(r:'a field) k z. FiniteField r /\
          mifactor z (unity k) /\ 1 < deg z /\ (forderz X = k) ==>
      !n. (char r) divides n /\ k < char r /\ (2 * SUC (LOG2 n)) ** 2 <= ordz k n /\ (* conditions on n, k *)
          poly_intro_range r k n (2 * (SQRT (phi k)) * (SUC (LOG2 n))) (* AKS tests *)
      ==> perfect_power n (char r)``,
  metis_tac[AKS_main_thm_0, poly_X_order_gt_1]);

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
   Let a = (2 * SUC (LOG2 n)) ** 2.
   Note 0 < SUC (LOG2 n)               by SUC_NOT
     so 1 < 2 * SUC (LOG2 n)           by arithmetic
    and 1 < a                          by ONE_LT_EXP
     so ordz k n <> 1                  by 1 < a <= ordz k n
    ==> k <> 1                         by ZN_order_mod_1
   Thus 1 < k                          by k <> 0, k <> 1
   The result follows                  by AKS_main_thm_0
*)
val AKS_main_thm_1 = store_thm(
  "AKS_main_thm_1",
  ``!(r:'a field) k z. FiniteField r /\
           mifactor z (unity k) /\ (forderz X = k) ==>
    !n. 0 < k /\ (char r) divides n /\ k < char r /\
        (2 * SUC (LOG2 n)) ** 2 <= ordz k n /\ (* conditions on n, k *)
        poly_intro_range r k n (2 * (SQRT (phi k)) * (SUC (LOG2 n))) (* AKS tests *)
    ==> perfect_power n (char r)``,
  rpt strip_tac >>
  `1 < (2 * SUC (LOG2 n)) ** 2` by rw[ONE_LT_EXP] >>
  `ordz k n <> 1` by decide_tac >>
  `k <> 1` by metis_tac[ZN_order_mod_1] >>
  `1 < k` by decide_tac >>
  metis_tac[AKS_main_thm_0]);

(* Theorem: The AKS Main Theorem (Version 2)
   Assume there is FiniteField r with (char r) dividing n,
               and a prime k with k < (char r),
              then if k satisfies further conditions,
                  and n intro (X + |c|) for 0 < c <= s,
                  up to a limit s determined by k and n,
                  then n must be a perfect power of (char r).
   Note: (char r) of FiniteField r is always prime.
*)
(* Proof:
   Note 1 < k                            by ONE_LT_PRIME
   Thus ?z. mifactor z (unity k) /\ z <> unity 1
                                         by poly_unity_irreducible_factor_exists, 1 < k, k < char r
    Now deg (unity k) = k                by poly_unity_deg
     so 0 < deg (unity k)                by 1 < k
    and 0 < deg z                        by poly_irreducible_deg_nonzero, ipoly z
   Thus (X ** k == |1|) (pm (unity k))   by poly_unity_pmod_eqn
    ==> (X ** k == |1|) (pm z)           by poly_field_mod_eq_divisor, z <> |0|, unity k <> |0|
    ==> forderz X = k                    by poly_X_order_prime_condition, (X ** k == |1|) (pm z)
   The result follows                    by AKS_main_thm_0
*)
val AKS_main_thm_2 = store_thm(
  "AKS_main_thm_2",
  ``!(r:'a field) n k. FiniteField r /\
        prime k /\ (char r) divides n /\ k < char r /\ (* conditions on n, k *)
        (2 * SUC (LOG2 n)) ** 2 <= ordz k n /\ (* parameter k *)
        poly_intro_range r k n (2 * (SQRT (phi k)) * (SUC (LOG2 n))) (* AKS tests *)
    ==> perfect_power n (char r)``,
  rpt strip_tac >>
  `Field r` by rw[finite_field_is_field] >>
  `1 < k` by rw[ONE_LT_PRIME] >>
  `?z. mifactor z (unity k) /\ z <> unity 1` by rw[poly_unity_irreducible_factor_exists] >>
  `deg (unity k) = k` by rw[] >>
  `0 < k` by decide_tac >>
  `0 < deg z` by rw[poly_irreducible_deg_nonzero] >>
  `poly (unity k) /\ poly z /\ poly (X ** k) /\ poly |1|` by rw[] >>
  `(X ** k == |1|) (pm (unity k))` by rw[poly_unity_pmod_eqn] >>
  `(X ** k == |1|) (pm z)` by metis_tac[poly_field_mod_eq_divisor, poly_deg_zero, NOT_ZERO] >>
  `forderz X = k` by rw[poly_X_order_prime_condition] >>
  metis_tac[AKS_main_thm_0]);

(* Note:
Another route using poly_unity_irreducible_factor_with_order:
|- !r n. Field r /\ 1 < n /\ n < char r ==>
     ?z. mifactor z (unity n) /\ forderz X divides n

is appealing but quite difficult because we need to show (forderz X <> 1).
we could make use of (forderz (X % z) = forderz X), and show that forderz (X % z) <> 1.
but we need to show (X % z <> |1|), the only element with order 1 in Group ((PolyModRing r z).prod excluding |0|).
I can prove: poly_order_eq_1
|- !r. Field r ==> !z. monic z /\ ipoly z ==>
   !p. poly p /\ forderz p = 1 ==> p % z = |0| \/ p % z = |1|
Thus showing X % z <> |0| and X % z <> |1| will prove (forderz X <> 1).
This can be modelled along the proof of poly_X_order_prime_condition,
but we need to know: z <> unity 1.

This amounts to show that:

if monic z, ipoly z  divides (unity k), (unity k) % z = |0|,
and deg z = 1, then z = unity 1.
need to show: (unity k) has no multiple roots, or (unity k) has only 1 real root, 1.
(not entirely true, X ** 2 - |1| has +1 and -1, but we are not using integers, etc.)

ffUnityTheory
poly_unity_irreducible_factor_deg_1
|- !r. Field r ==>
   !n h. mifactor h (unity n) /\ deg h = 1 ==>
    ?c. c IN R /\ h = factor c /\ c ** n = #1

Still this is very hard.
The only way out seems to invoke ffAdvancedTheory: cyclotomic factors of (unity k).
From there, (unity k = product of irreducibles = product of cyclotomic factors).
Although cyclotomic factors may or may not be irreducible, there is hope to solve.

Clearly, X % z = |0|  means X = q * z,  which is very odd.
Also, X % z = |1| means X = q * z + |1|, which is almost impossible.
*)

(* ------------------------------------------------------------------------- *)
(* Improvements for Version 2                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: The AKS Main Theorem (Version 3)
   Given a number n > 1,
   If there are numbers k and s such that:
      k is prime
      order of n in (ZN k) >= (2 log n)^2
      s = 2 sqrt(phi k) (log n)
      for all nonzero j <= k, coprime j n
      for all nonzero c <= s, poly_intro (ZN n) k n (zx+ c)
   Then n must be a perfect power of a prime p.
*)
(* Proof:
   If n is prime,
      Let prime p = n, then n = p ** 1      by perfect_power_self
   If n is not prime,
      There is a prime p such that
      p < n, and p divides n                by PRIME_FACTOR_PROPER

   Note 1 < k and 1 < p                     by ONE_LT_PRIME
   Thus k < p                               by implication, p divides n.

   Note FiniteField (ZN p)                  by ZN_finite_field, prime p
    and char (ZN p) = p                     by ZN_char, p < p

   Let s = 2 * (SQRT (phi k)) * (SUC (LOG2 n)).
   Since coprime k n                        by coprime_by_le_not_divides, 1 < k
     and s <= phi k                         by ZN_order_condition_property, 1 < n
     and phi k <= k                         by phi_le
      so s < p                              by k < p
    With poly_intro_range (ZN n) k n s      by given
    Thus poly_intro_range (ZN p) k n s      by ring_homo_intro_ZN_to_ZN_X_add_c, s < p

   Thus all conditions for AKS_main_thm_2 are fulfilled,
   and taking this prime p, the result follows by AKS_main_thm_2, k < p.
*)
val AKS_main_thm_3 = store_thm(
  "AKS_main_thm_3",
  ``!n k. 1 < n /\ prime k /\ (* property of k *)
       (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\ (* later this gives k < p *)
       (2 * SUC (LOG2 n)) ** 2 <= ordz k n /\ (* condition on k *)
       poly_intro_range (ZN n) k n (2 * (SQRT (phi k)) * (SUC (LOG2 n))) (* AKS tests in (ZN n) *)
      ==> ?p. prime p /\ perfect_power n p``,
  rpt strip_tac >>
  Cases_on `prime n` >-
  metis_tac[perfect_power_self] >>
  `?p. prime p /\ p < n /\ p divides n` by rw[PRIME_FACTOR_PROPER] >>
  qexists_tac `p` >>
  simp[] >>
  `1 < k /\ 1 < p` by rw[ONE_LT_PRIME] >>
  `0 < n /\ 0 < k` by decide_tac >>
  `k < p` by metis_tac[NOT_LESS] >>
  qabbrev_tac `s = 2 * (SQRT (phi k)) * (SUC (LOG2 n))` >>
  `s < p` by
  (`coprime k n` by rw[coprime_by_le_not_divides] >>
  `s <= phi k` by metis_tac[ZN_order_condition_property] >>
  `phi k <= k` by rw[phi_le] >>
  decide_tac) >>
  `poly_intro_range (ZN p) k n s` by metis_tac[ring_homo_intro_ZN_to_ZN_X_add_c] >>
  `FiniteField (ZN p)` by rw[ZN_finite_field] >>
  `char (ZN p) = p` by rw[ZN_char] >>
  metis_tac[AKS_main_thm_2]);

(* ------------------------------------------------------------------------- *)
(* Bidirectional AKS Main Theorem                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: The AKS Main Theorem (Version 4)
   Given a power-free number n,
   If there are numbers k and s such that:
      k is prime
      order of n in (ZN k) >= (2 log n)^2
      s = 2 sqrt(phi k) (log n)
      and k < n
   Then n is prime iff
      for all nonzero j <= k, ~(j divides n)
      for all nonzero c <= s, poly_intro (ZN n) k n (zx+ c)
*)
(* Proof:
   Let s = 2 * (SQRT (phi k)) * (SUC (LOG2 n)).
   If part: prime n ==> checks (1) (2)
      (1) prime n ==> 1 < j /\ j <= k ==> ~(j divides n)
          Since prime n and k < n, this is true        by prime_def
      (2) prime n ==> !c. 0 < c /\ c <= s ==> poly_intro (ZN n) k n (x+ n c)
          Since 1 < n                                  by power_free_gt_1
            and 1 < k                                  by ONE_LT_PRIME
             so Ring (ZN n)                            by ZN_ring, 0 < n
            and char (ZN n) = n                        by ZN_char, 0 < n
          The result follows                           by poly_intro_X_add_c_prime_char, 0 < k
   Only-if part: checks (1) (2) ==> prime n
      Note 1 < n                                       by power_free_gt_1
      Thus ?p. prime p /\ perfect_power n p            by AKS_main_thm_3, 1 < n
      Then p = n                                       by power_free_perfect_power
      Hence prime n.
*)
val AKS_main_thm_4 = store_thm(
  "AKS_main_thm_4",
  ``!n. power_free n ==> (* condition on n *)
   !k. prime k /\ (2 * SUC (LOG2 n)) ** 2 <= ordz k n /\ (* property of k *)
         k < n ==> (* simple check on k *)
   (prime n <=> ((!j. 1 < j /\ j <= k ==> ~(j divides n)) /\ (* checks on k *)
                 poly_intro_range (ZN n) k n (2 * (SQRT (phi k)) * (SUC (LOG2 n)))))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    `j < n` by decide_tac >>
    metis_tac[prime_def, LESS_NOT_EQ],
    `1 < n /\ 1 < k` by rw[power_free_gt_1, ONE_LT_PRIME] >>
    `0 < n /\ 0 < k` by decide_tac >>
    `Ring (ZN n)` by rw[ZN_ring] >>
    `char (ZN n) = n` by rw[ZN_char] >>
    metis_tac[poly_intro_X_add_c_prime_char],
    `1 < n` by rw[power_free_gt_1] >>
    `?p. prime p /\ perfect_power n p` by metis_tac[AKS_main_thm_3] >>
    metis_tac[power_free_perfect_power]
  ]);

(* Theorem: The AKS Main Theorem (Version 5)
   Given a power-free number n,
   If there are numbers k and s such that:
      k is prime
      order of n in (ZN k) >= (2 log n)^2
      s = 2 sqrt(phi k) (log n)
      and for all nonzero j <= MIN k n, coprime j n
   Then n is prime iff
      k < n and
      for all nonzero c <= s, poly_intro (ZN n) k n (zx+ c)
*)
(* Proof:
   Let s = 2 * (SQRT (phi k)) * (SUC (LOG2 n)).
   Note 1 < n                       by power_free_gt_1
   If part: prime n ==> k < n /\ poly_intro_range (ZN n) k n s)
      This is to show:
      (1) k < n
          By contradiction, suppose n <= k, then MIN k n = n
          With 1 < n, and n <= n    by LESS_OR_EQ
          giving ~(n divides n)     by check on k
          But n divides n           by DIVIDES_REFL
          Hence a contradiction.
      (3) prime n /\ 0 < c /\ c <= s ==> poly_intro (ZN n) k n (x+ n c)
          Since Ring (ZN n)         by ZN_ring, 0 < n
            and char (ZN n) = n     by ZN_char, 0 < n
           Now  0 < k               by PRIME_POS
           Hence the result is true by poly_intro_X_add_c_prime_char, 0 < k
   Only-if part: k < n /\ poly_intro_range (ZN n) k n s) ==> prime n
      Note k < n means MIN k n = k              by MIN_DEF
      Thus ?p. prime p /\ perfect_power n p     by AKS_main_thm_3, 1 < n
      Then p = n                                by power_free_perfect_power
      Hence prime n.
*)
val AKS_main_thm_5 = store_thm(
  "AKS_main_thm_5",
  ``!n k. power_free n /\ (* condition on n *)
           prime k /\ (2 * SUC (LOG2 n)) ** 2 <= ordz k n /\ (* property of k *)
           (!j. 1 < j /\ j <= (MIN k n) ==> ~(j divides n)) ==> (* checks on k *)
   (prime n <=> (k < n /\ poly_intro_range (ZN n) k n (2 * (SQRT (phi k)) * (SUC (LOG2 n)))))``,
  rpt strip_tac >>
  `1 < n` by rw[power_free_gt_1] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `MIN k n = n` by rw[MIN_DEF] >>
    metis_tac[LESS_OR_EQ, DIVIDES_REFL],
    `1 < n /\ 1 < k` by rw[power_free_gt_1, ONE_LT_PRIME] >>
    `0 < n /\ 0 < k` by decide_tac >>
    `Ring (ZN n)` by rw[ZN_ring] >>
    `char (ZN n) = n` by rw[ZN_char] >>
    metis_tac[poly_intro_X_add_c_prime_char],
    `MIN k n = k` by rw[MIN_DEF] >>
    `?p. prime p /\ perfect_power n p` by metis_tac[AKS_main_thm_3] >>
    metis_tac[power_free_perfect_power]
  ]);

(* Theorem: The AKS Main Theorem (Version 6)
   Given a number n > 1,
   If there are numbers k and s such that:
      k is prime
      order of n in (ZN k) >= (2 log n)^2
      s = 2 sqrt(phi k) (log n)
      and for all nonzero j <= MIN k n, coprime j n
   Then n is prime iff
      n is power-free, and
      k < n and
      for all nonzero c <= s, poly_intro (ZN n) k n (zx+ c)
*)
(* Proof:
   Let s = 2 * (SQRT (phi k)) * (SUC (LOG2 n)).
   If part: prime n ==>
            power-free n /\ k < n /\ !c. 0 < c /\ c <= s ==> poly_intro (ZN n) k n (x+ n c)
      This is to show:
      (1) power-free n
          True by prime_is_power_free.
      (2) k < n
          By contradiction, suppose n <= k, then MIN k n = n
          With 1 < n, and n <= n    by LESS_OR_EQ
          giving ~(n divides n)     by check on k
          But n divides n           by DIVIDES_REFL
          Hence a contradiction.
      (3) prime n /\ 0 < c /\ c <= s ==> poly_intro (ZN n) k n (x+ n c)
          Note 0 < n, 0 < k         by PRIME_POS
          Since Ring (ZN n)         by ZN_ring, 0 < n
            and char (ZN n) = n     by ZN_char, 0 < n
           Hence the result is true by poly_intro_X_add_c_prime_char, 0 < k
   Only-if part: power-free n /\ k < n /\ poly_intro_range (ZN n) k n s) ==> prime n
      Since !j. 1 < j /\ j <= k ==>
                1 < j /\ j <= k /\ j <= n      by k < n
      Thus ?p. prime p /\ perfect_power n p    by AKS_main_thm_3
      Then p = n                               by power_free_perfect_power
      Hence prime n.
*)
val AKS_main_thm_6 = store_thm(
  "AKS_main_thm_6",
  ``!n k. prime k /\ (2 * SUC (LOG2 n)) ** 2 <= ordz k n /\ (* property of k *)
         (!j. 1 < j /\ j <= (MIN k n) ==> ~(j divides n)) ==> (* checks on k *)
   (prime n <=> (power_free n /\ k < n /\
                 poly_intro_range (ZN n) k n (2 * (SQRT (phi k)) * (SUC (LOG2 n)))))``,
  rw_tac std_ss[EQ_IMP_THM] >-
  rw[prime_is_power_free] >-
 (spose_not_then strip_assume_tac >>
  `1 < n` by rw[ONE_LT_PRIME] >>
  `n <= k /\ n <= n` by decide_tac >>
  metis_tac[DIVIDES_REFL]) >-
 (`0 < n /\ 0 < k` by rw[PRIME_POS] >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `char (ZN n) = n` by rw[ZN_char] >>
  metis_tac[poly_intro_X_add_c_prime_char]) >>
  `1 < n` by rw[power_free_gt_1] >>
  `!j. 1 < j /\ j <= k ==> 1 < j /\ j <= k /\ j <= n` by decide_tac >>
  metis_tac[AKS_main_thm_3, power_free_perfect_power]);

(*
What happens when k >= n ?
In this case, if !j. 0 < j /\ j < n ==> coprime n j, then n must be prime, else not prime.
*)

(* Theorem: The AKS Main Theorem (Version 7)
   A number n is prime iff
     n > 1, and power-free n,
     there is number k such that:
      k is prime
      and order of n in (ZN k) >= (2 log n)^2
      and for all nonzero j < MIN (SUC k) n, coprime j n  (with MIN hidden)
      and if k < n, let s = 2 sqrt(phi k) (log n),
          then for all nonzero c <= s, poly_intro (ZN n) k n (zx+ c)
*)
(* Proof:
   Let s = 2 * (SQRT (phi k)) * (SUC (LOG2 n)).
   If part: prime n ==> power_free n /\ (?k s. ... )
      This is to show:
      (1) prime n ==> power_free n, true      by prime_is_power_free.
      (2) ?k. prime k /\ ...
          Let m = (2 * SUC (LOG2 n)) ** 2
          Then prime n ==> 0 < n              by PRIME_POS
           and 4 <= m, or 0 < m               by LOG2_SUC_TWICE_SQ, 0 < n
            so ?k. prime k /\ coprime k n /\ m <= ordz k n
                                              by ZN_order_big_enough
          Take this k, there are 2 goals:
          (1) prime n /\ 1 < j /\ j <= k /\ j < n ==> ~(j divides n)
              By contradiction, suppose j divides n.
              Then j = 1 or j = n             by prime_def
              This contradicts 1 < j and j < n.
          (2) prime n /\ 0 < c /\ c <= s ==> poly_intro (ZN n) k n (x+ n c)
              where s = 2 * SQRT (phi k) * (log n)
              Note 0 < n and 0 < k            by PRIME_POS
              Thus Ring (ZN n)                by ZN_ring, 0 < n
               and char (ZN n) = n            by ZN_char, 0 < n
              Hence poly_intro (ZN n) k n (x+ n c)
                                              by poly_intro_X_add_c_prime_char, 0 < k
   Only-if part: power_free n /\ (?k s. ... ) ==> prime n
      Note 1 < n                                        by power_free_gt_1
      If k < n,
         (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) becomes
         (!j. 1 < j /\ j <= k ==> ~(j divides n))       as j <= k /\ k < n ==> j < n
         with !c. 0 < c /\ c <= s ==> poly_intro (ZN n) k n (x+ n c)))
         Therefore ?p. prime p /\ perfect_power n p     by AKS_main_thm_3
            But power_free n ==> p = n                  by power_free_perfect_power
          Hence prime n.
      Otherwise, ~(k < n),
         (!j. 0 < j /\ j <= k /\ j < n ==> ~(j divides n)) becomes
         (!j. 0 < j /\ j < n ==> ~(j divides n))        as j < n /\ n <= k ==> j < k, or j <= k
         Hence prime n                                  by prime_iff_no_proper_factor
*)
val AKS_main_thm_7 = store_thm(
  "AKS_main_thm_7",
  ``!n. prime n <=> power_free n /\
  (?k. prime k /\
       (2 * SUC (LOG2 n)) ** 2 <= ordz k n /\ (* property of k *)
       (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\ (* checks on k, hidden MIN *)
       (k < n ==> (* polynomial identity checks only when k < n *)
        poly_intro_range (ZN n) k n (2 * SQRT (phi k) * SUC (LOG2 n))))``,
  rw_tac bool_ss[EQ_IMP_THM] >-
  rw[prime_is_power_free] >-
 (qabbrev_tac `m = (2 * SUC (LOG2 n)) ** 2` >>
  `0 < n /\ 1 < n` by rw[PRIME_POS, ONE_LT_PRIME] >>
  `4 <= m` by rw[LOG2_SUC_TWICE_SQ, Abbr`m`] >>
  `0 < m` by decide_tac >>
  `?k. prime k /\ coprime k n /\ m <= ordz k n` by rw[ZN_order_big_enough] >>
  qexists_tac `k` >>
  rw_tac std_ss[] >-
  metis_tac[prime_def, LESS_NOT_EQ] >>
  `0 < k` by rw[PRIME_POS] >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `char (ZN n) = n` by rw[ZN_char] >>
  metis_tac[poly_intro_X_add_c_prime_char]) >>
  `1 < n` by rw[power_free_gt_1] >>
  Cases_on `k < n` >| [
    `!j. 1 < j /\ j <= k ==> 1 < j /\ j <= k /\ j < n` by decide_tac >>
    metis_tac[AKS_main_thm_3, power_free_perfect_power],
    `!j. 1 < j /\ j < n ==> 1 < j /\ j <= k /\ j < n` by decide_tac >>
    metis_tac[prime_iff_no_proper_factor]
  ]);

(* Theorem: This is Version 7 with poly_intro made explicit. *)
(* Proof:
   Note  prime k ==> 0 < k                            by PRIME_POS
   also  power_free n ==> 1 < n ==> 0 < n /\ n <> 1   by power_free_gt_1
    and  0 < n ==> Ring (ZN n)                        by ZN_ring, 0 < n
   together with poly_intro_X_add_c, this is true     by AKS_main_thm_7
*)
val AKS_main_thm_8 = store_thm(
  "AKS_main_thm_8",
  ``!n. prime n <=> power_free n /\
  (?k. prime k /\
       (2 * SUC (LOG2 n)) ** 2 <= ordz k n /\ (* property of k *)
       (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\ (* checks on k, hidden MIN *)
       (k < n ==> !c. 0 < c /\ c <= 2 * SQRT (phi k) * SUC (LOG2 n) ==>  (* AKS checks *)
                  ((x+^ n c n) == (x^+ n c n)) (pmod (ZN n) (x^- n k))))``,
  rpt strip_tac >>
  `!k. prime k ==> 0 < k` by rw[PRIME_POS] >>
  `!n. 1 < n ==> 0 < n` by decide_tac >>
  `!n. 0 < n ==> Ring (ZN n)` by rw[ZN_ring] >>
  metis_tac[AKS_main_thm_7, poly_intro_X_add_c, power_free_gt_1]);

(* The IF part of AKS_main_thm_7 *)
val AKS_main_thm_if = store_thm(
  "AKS_main_thm_if",
  ``!n. prime n ==> power_free n /\
        (?k. prime k /\
             (2 * SUC (LOG2 n)) ** 2 <= ordz k n /\ (* property of k *)
             (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\ (* checks on k *)
             (k < n ==> (* if k < n  *)
              poly_intro_range (ZN n) k n (2 * SQRT (phi k) * SUC (LOG2 n))))``,
    rw[GSYM AKS_main_thm_7]);

(* The ONLY-IF part of AKS_main_thm_7 *)
val AKS_main_thm_only_if = store_thm(
  "AKS_main_thm_only_if",
  ``!n. power_free n /\
        (?k. prime k /\
             (2 * SUC (LOG2 n)) ** 2 <= order (ZN k).prod n /\ (* property of k *)
             (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\ (* checks on k *)
             (k < n ==> (* if k < n  *)
              poly_intro_range (ZN n) k n (2 * SQRT (phi k) * SUC (LOG2 n))))
       ==> prime n``,
    rw[GSYM AKS_main_thm_7]);

(* ------------------------------------------------------------------------- *)
(* AKS Main Theorem based on upper logarithm                                 *)
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
   Let a = (2 * ulog n) ** 2,
       s = 2 * SQRT (phi k) * ulog n,
       p = char r.
   Then prime p                   by finite_field_char

   If n = p,
      Then perfect_power n p      by perfect_power_self
   If n <> p,
      Note p <= n                 by DIVIDES_LE, p divides n
        so p < n                  by p <> n

      Some assertions:
      Note n <> 1                 by DIVIDES_ONE, p divides n, p <> n
       and 1 < k and 0 < k        by poly_X_order_gt_1, properties of z
       Now coprime k n            by ZN_order_eq_0, 0 < k, 0 < ordz k n
      Thus n <> 0                 by coprime_0R, k <> 1
        so 1 < n and 0 < n        by n <> 0, n <> 1
       and 1 < p                  by ONE_LT_PRIME
      Also coprime n k            by coprime_sym

      Let t = CARD M

      Step 1: Apply modN_card_in_exp_lt_bound_4
      If perfect_power n 2,
      Then n = 2 ** e           by perfect_power_def
        so p = 2                by prime_divides_prime_power, p divides n
        or perfect_power n p    by p = 2
      Otherwise, ~perfect_power n 2.

      If perfect_power n 2,
      Then n = 2 ** e           by perfect_power_def
        so p = 2                by prime_divides_prime_power, p divides n
        or perfect_power n p    by p = 2

      If ~perfect_power n 2,
      Since n IN N                            by setN_element
       Then n ** (2 * SQRT t) < 2 ** MIN s t  by modN_card_in_exp_lt_bound_4

      Step 2: Apply modP_card_lower_1
      Since 0 < SQRT (phi k) * ulog n        by sqrt_phi_times_ulog, 0 < k, 1 < n
        and 0 < s                            by arithmetic
       Also s <= phi k <= k                  by ZN_order_condition_property_3, phi_le, 1 < n
         so s < p                            by given k < p = char r
        and 1 < t                            by modN_card_gt_1_by_ulog, 1 < k, 1 < n, n IN N
      gives 2 ** MIN s t <= CARD (Q z)       by modP_card_lower_1, 1 < t
      Thus  n ** (2 * SQRT t) < CARD (Q z)   by LESS_LESS_EQ_TRANS

      Step 3: Apply reduceN_mod_modN_inj_1
      Since coprime p k                            by coprime_prime_factor_coprime
            p IN N                                 by setN_has_char, coprime p k
      Hence INJ (\m. m MOD k) (NM p n (SQRT t)) M  by reduceN_mod_modN_inj_1

      Step 4: Apply reduceN_card
      By contradiction, assume ~perfect_power n p.
      Then CARD (NM p n (SQRT t)) = (SUC (SQRT t)) ** 2    by reduceN_card
      Now  FINITE M                                        by modN_finite
      and  t < (SUC (SQRT t)) ** 2                         by SQRT_PROPERTY
      Overall,  t < CARD (NM p n (SQRT t))

      Step 5: Conclusion
      This violates the Pigeonhole Principle:
      PHP |- !f s t. FINITE t /\ CARD t < CARD s ==> ~INJ f s t

      Therefore, perfect_power n p.
*)
val AKS_main_ulog_0 = store_thm(
  "AKS_main_ulog_0",
  ``!(r:'a field) k z. FiniteField r /\
           mifactor z (unity k) /\ (forderz X = k) ==>
      !n. 0 < n /\ (* to keep 0 < ulog n, with n <> 1 *)
          1 < k /\ (char r) divides n /\ k < char r /\
          (2 * ulog n) ** 2 <= ordz k n /\ (* conditions on n, k *)
          poly_intro_range r k n (2 * SQRT (phi k) * ulog n) (* AKS tests *)
      ==> perfect_power n (char r)``,
  rpt strip_tac >>
  qabbrev_tac `p = char r` >>
  qabbrev_tac `a = (2 * ulog n) ** 2` >>
  qabbrev_tac `s = 2 * (SQRT (phi k)) * ulog n` >>
  `prime p` by rw[finite_field_char, Abbr`p`] >>
  Cases_on `n = p` >-
  rw[perfect_power_self] >>
  Cases_on `perfect_power n 2` >-
  metis_tac[perfect_power_def, prime_divides_prime_power, PRIME_2] >>
  `n <> 1` by metis_tac[DIVIDES_ONE] >>
  `0 < k /\ 1 < n` by decide_tac >>
  `coprime n k` by
  (`0 < a` by rw[ulog_pos, MULT_POS, Abbr`a`] >>
  `ordz k n <> 0` by decide_tac >>
  metis_tac[ZN_order_eq_0, coprime_sym]) >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `p <= n` by rw[DIVIDES_LE] >>
  `p < n` by decide_tac >>
  `MAX p n = n` by rw[MAX_DEF] >>
  qabbrev_tac `t = CARD M` >>
  `Field r` by rw[finite_field_is_field] >>
  `Ring r` by rw[] >>
  `n IN N` by rw[setN_element] >>
  `n ** (2 * SQRT t) < 2 ** MIN s t` by metis_tac[modN_card_in_exp_lt_bound_4] >>
  `0 < SQRT (phi k) * ulog n` by metis_tac[sqrt_phi_times_ulog] >>
  `0 < s` by fs[Abbr`s`] >>
  `s <= phi k` by rw[ZN_order_condition_property_3, coprime_sym, Abbr`a`, Abbr`s`] >>
  `phi k <= k` by rw[phi_le] >>
  `s < p` by decide_tac >>
  `1 < t` by metis_tac[modN_card_gt_1_by_ulog] >>
  `2 ** MIN s t <= CARD (Q z)` by fs[modP_card_lower_1, Abbr`t`, Abbr`p`] >>
  `n ** (2 * SQRT t) < CARD (Q z)` by decide_tac >>
  `coprime p k` by metis_tac[coprime_prime_factor_coprime] >>
  `p IN N` by rw[setN_has_char, Abbr`p`] >>
  `INJ (\m. m MOD k) (NM p n (SQRT t)) M` by metis_tac[reduceN_mod_modN_inj_1] >>
  spose_not_then strip_assume_tac >>
  `CARD (NM p n (SQRT t)) = (SUC (SQRT t)) ** 2` by metis_tac[reduceN_card] >>
  `FINITE M` by rw[modN_finite] >>
  `t < (SUC (SQRT t)) ** 2` by rw[SQRT_PROPERTY] >>
  `t < CARD (NM p n (SQRT t))` by decide_tac >>
  metis_tac[PHP]);

(* Theorem: The AKS Main Theorem (Version 0) *)
(* Proof:
   Note 1 < k           by poly_X_order_gt_1
   The result follows   by AKS_main_ulog_0

   Note: This can be proved directly via:
         n ** (2 * SQRT t) <= 2 ** MIN s t            by modN_card_in_exp_le_bound_0
         2 ** MIN s t < CARD (Q z)                    by modP_card_lower_better, 1 < deg z
         to have: n ** (2 * SQRT t) < CARD (Q z)
         and: INJ (\m. m MOD k) (NM p n (SQRT t)) M   by reduceN_mod_modN_inj_0, 1 < deg z
         avoid the technical glitch of splitting by (perfect_power n 2).
*)
val AKS_main_ulog_0_alt = store_thm(
  "AKS_main_ulog_0_alt",
  ``!(r:'a field) k z. FiniteField r /\
           mifactor z (unity k) /\ 1 < deg z /\ (forderz X = k) ==>
      !n. 0 < n /\ (* to keep 0 < ulog n, with n <> 1 *)
          (char r) divides n /\ k < char r /\
          (2 * ulog n) ** 2 <= ordz k n /\ (* conditions on n, k *)
          poly_intro_range r k n (2 * SQRT (phi k) * ulog n) (* AKS tests *)
      ==> perfect_power n (char r)``,
  metis_tac[AKS_main_ulog_0, poly_X_order_gt_1]);

(* Theorem: The AKS Main Theorem (Version 1) *)
(* Proof:
   Let a = (2 * ulog n) ** 2, p = char r.
   Note prime p                  by finite_field_char
     so 1 < p                    by ONE_LT_PRIME
    ==> n <> 1                   by DIVIDES_ONE
   Thus 1 < n                    by 0 < n, n <> 1
    ==> 4 <= a                   by ulog_twice_sq, 1 < n
     or 1 < a                    by arithmetic
     so ordz k n <> 1            by 1 < a <= ordz k n
    ==> k <> 1                   by ZN_order_mod_1
   Thus 1 < k                    by k <> 0, k <> 1
   The result follows            by AKS_main_ulog_0
*)
val AKS_main_ulog_1 = store_thm(
  "AKS_main_ulog_1",
  ``!(r:'a field) k z. FiniteField r /\
           mifactor z (unity k) /\ (forderz X = k) ==>
    !n. 0 < n /\ 0 < k /\ (char r) divides n /\ k < char r /\
        (2 * ulog n) ** 2 <= ordz k n /\ (* conditions on n, k *)
        poly_intro_range r k n (2 * (SQRT (phi k)) * ulog n) (* AKS tests *)
    ==> perfect_power n (char r)``,
  rpt strip_tac >>
  qabbrev_tac `p = char r` >>
  `prime p` by rw[finite_field_char, Abbr`p`] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `n <> 1` by metis_tac[DIVIDES_ONE, LESS_NOT_EQ] >>
  `1 < n` by decide_tac >>
  `4 <= (2 * ulog n) ** 2` by rw[ulog_twice_sq] >>
  `ordz k n <> 1` by decide_tac >>
  `k <> 1` by metis_tac[ZN_order_mod_1] >>
  `1 < k` by decide_tac >>
  metis_tac[AKS_main_ulog_0]);

(* Theorem: The AKS Main Theorem (Version 2) *)
(* Proof:
   Note 1 < k                            by ONE_LT_PRIME
   Thus ?z. mifactor z (unity k) /\ z <> unity 1
                                         by poly_unity_irreducible_factor_exists, 1 < k, k < char r
    Now deg (unity k) = k                by poly_unity_deg
     so 0 < deg (unity k)                by 1 < k
    and 0 < deg z                        by poly_irreducible_deg_nonzero, ipoly z
   Thus (X ** k == |1|) (pm (unity k))   by poly_unity_pmod_eqn
    ==> (X ** k == |1|) (pm z)           by poly_field_mod_eq_divisor, z <> |0| , unity k <> |0|
    ==> forderz X = k                    by poly_X_order_prime_condition, (X ** k == |1|) (pm z)
   The result follows                    by AKS_main_ulog_0
*)
val AKS_main_ulog_2 = store_thm(
  "AKS_main_ulog_2",
  ``!(r:'a field) n k. FiniteField r /\
        0 < n /\ prime k /\ (char r) divides n /\ k < char r /\ (* conditions on n, k *)
        (2 * ulog n) ** 2 <= ordz k n /\ (* parameter k *)
        poly_intro_range r k n (2 * (SQRT (phi k)) * ulog n) (* AKS tests *)
    ==> perfect_power n (char r)``,
  rpt strip_tac >>
  `Field r` by rw[finite_field_is_field] >>
  `1 < k` by rw[ONE_LT_PRIME] >>
  `?z. mifactor z (unity k) /\ z <> unity 1` by rw[poly_unity_irreducible_factor_exists] >>
  `deg (unity k) = k` by rw[] >>
  `0 < k` by decide_tac >>
  `0 < deg z` by rw[poly_irreducible_deg_nonzero] >>
  `poly (unity k) /\ poly z /\ poly (X ** k) /\ poly |1|` by rw[] >>
  `(X ** k == |1|) (pm (unity k))` by rw[poly_unity_pmod_eqn] >>
  `(X ** k == |1|) (pm z)` by metis_tac[poly_field_mod_eq_divisor, poly_deg_zero, NOT_ZERO] >>
  `forderz X = k` by rw[poly_X_order_prime_condition] >>
  metis_tac[AKS_main_ulog_0]);

(* Theorem: The AKS Main Theorem (Version 3) *)
(* Proof:
   If n is prime,
      Let prime p = n, then n = p ** 1      by perfect_power_self
   If n is not prime,
      There is a prime p such that
      p < n, and p divides n                by PRIME_FACTOR_PROPER

   Note 1 < k and 1 < p                     by ONE_LT_PRIME
   Thus k < p                               by implication, p divides n.

   Note FiniteField (ZN p)                  by ZN_finite_field, prime p
    and char (ZN p) = p                     by ZN_char, p < p

   Let s = 2 * (SQRT (phi k)) * ulog n.
   Since coprime k n                        by coprime_by_le_not_divides, 1 < k
     and s <= phi k                         by ZN_order_condition_property_3, 1 < n
     and phi k <= k                         by phi_le
      so s < p                              by k < p
    With poly_intro_range (ZN n) k n s      by given
    Thus poly_intro_range (ZN p) k n s      by ring_homo_intro_ZN_to_ZN_X_add_c, s < p

   Thus all conditions for AKS_main_ulog_2 are fulfilled,
   and taking this prime p, the result follows by AKS_main_ulog_2, k < p.
*)
val AKS_main_ulog_3 = store_thm(
  "AKS_main_ulog_3",
  ``!n k. 1 < n /\ prime k /\ (* property of k *)
       (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\ (* later this gives k < p *)
       (2 * ulog n) ** 2 <= ordz k n /\ (* condition on k *)
       poly_intro_range (ZN n) k n (2 * (SQRT (phi k)) * ulog n) (* AKS tests in (ZN n) *)
      ==> ?p. prime p /\ perfect_power n p``,
  rpt strip_tac >>
  Cases_on `prime n` >-
  metis_tac[perfect_power_self] >>
  `?p. prime p /\ p < n /\ p divides n` by rw[PRIME_FACTOR_PROPER] >>
  qexists_tac `p` >>
  simp[] >>
  `1 < k /\ 1 < p` by rw[ONE_LT_PRIME] >>
  `0 < n /\ 0 < k` by decide_tac >>
  `k < p` by metis_tac[NOT_LESS] >>
  qabbrev_tac `s = 2 * (SQRT (phi k)) * ulog n` >>
  `s < p` by
  (`coprime k n` by rw[coprime_by_le_not_divides] >>
  `s <= phi k` by metis_tac[ZN_order_condition_property_3] >>
  `phi k <= k` by rw[phi_le] >>
  decide_tac) >>
  `poly_intro_range (ZN p) k n s` by metis_tac[ring_homo_intro_ZN_to_ZN_X_add_c] >>
  `FiniteField (ZN p)` by rw[ZN_finite_field] >>
  `char (ZN p) = p` by rw[ZN_char] >>
  metis_tac[AKS_main_ulog_2]);

(* Theorem: The AKS Main Theorem (Version 4) *)
(* Proof:
   Let s = 2 * (SQRT (phi k)) * ulog n.
   If part: prime n ==> checks (1) (2)
      (1) prime n ==> 1 < j /\ j <= k ==> ~(j divides n)
          Since prime n and k < n, this is true        by prime_def
      (2) prime n ==> !c. 0 < c /\ c <= s ==> poly_intro (ZN n) k n (x+ n c)
          Since 1 < n                                  by power_free_gt_1
            and 1 < k                                  by ONE_LT_PRIME
             so Ring (ZN n)                            by ZN_ring, 0 < n
            and char (ZN n) = n                        by ZN_char, 0 < n
          The result follows                           by poly_intro_X_add_c_prime_char, 0 < k
   Only-if part: checks (1) (2) ==> prime n
      Note 1 < n                                       by power_free_gt_1
      Thus ?p. prime p /\ perfect_power n p            by AKS_main_ulog_3, 1 < n
      Then p = n                                       by power_free_perfect_power
      Hence prime n.
*)
val AKS_main_ulog_4 = store_thm(
  "AKS_main_ulog_4",
  ``!n. power_free n ==> (* condition on n *)
   !k. prime k /\ (2 * ulog n) ** 2 <= ordz k n /\ (* property of k *)
         k < n ==> (* simple check on k *)
   (prime n <=> ((!j. 1 < j /\ j <= k ==> ~(j divides n)) /\ (* checks on k *)
                 poly_intro_range (ZN n) k n (2 * (SQRT (phi k)) * ulog n)))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    `j < n` by decide_tac >>
    metis_tac[prime_def, LESS_NOT_EQ],
    `1 < n /\ 1 < k` by rw[power_free_gt_1, ONE_LT_PRIME] >>
    `0 < n /\ 0 < k` by decide_tac >>
    `Ring (ZN n)` by rw[ZN_ring] >>
    `char (ZN n) = n` by rw[ZN_char] >>
    metis_tac[poly_intro_X_add_c_prime_char],
    `1 < n` by rw[power_free_gt_1] >>
    `?p. prime p /\ perfect_power n p` by metis_tac[AKS_main_ulog_3] >>
    metis_tac[power_free_perfect_power]
  ]);

(* Theorem: The AKS Main Theorem (Version 5) *)
(* Proof:
   Let s = 2 * (SQRT (phi k)) * ulog n.
   Note 1 < n                       by power_free_gt_1
   If part: prime n ==> k < n /\ poly_intro_range (ZN n) k n s)
      This is to show:
      (1) k < n
          By contradiction, suppose n <= k, then MIN k n = n
          With 1 < n, and n <= n    by LESS_OR_EQ
          giving ~(n divides n)     by check on k
          But n divides n           by DIVIDES_REFL
          Hence a contradiction.
      (3) prime n /\ 0 < c /\ c <= s ==> poly_intro (ZN n) k n (x+ n c)
          Since Ring (ZN n)         by ZN_ring, 0 < n
            and char (ZN n) = n     by ZN_char, 0 < n
           Now  0 < k               by PRIME_POS
           Hence the result is true by poly_intro_X_add_c_prime_char, 0 < k
   Only-if part: k < n /\ poly_intro_range (ZN n) k n s) ==> prime n
      Note k < n means MIN k n = k              by MIN_DEF
      Thus ?p. prime p /\ perfect_power n p     by AKS_main_ulog_3, 1 < n
      Then p = n                                by power_free_perfect_power
      Hence prime n.
*)
val AKS_main_ulog_5 = store_thm(
  "AKS_main_ulog_5",
  ``!n k. power_free n /\ (* condition on n *)
         prime k /\ (2 * ulog n) ** 2 <= ordz k n /\ (* property of k *)
         (!j. 1 < j /\ j <= (MIN k n) ==> ~(j divides n)) ==> (* checks on k *)
   (prime n <=> (k < n /\ poly_intro_range (ZN n) k n (2 * (SQRT (phi k)) * ulog n)))``,
  rpt strip_tac >>
  `1 < n` by rw[power_free_gt_1] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `MIN k n = n` by rw[MIN_DEF] >>
    metis_tac[LESS_OR_EQ, DIVIDES_REFL],
    `1 < n /\ 1 < k` by rw[power_free_gt_1, ONE_LT_PRIME] >>
    `0 < n /\ 0 < k` by decide_tac >>
    `Ring (ZN n)` by rw[ZN_ring] >>
    `char (ZN n) = n` by rw[ZN_char] >>
    metis_tac[poly_intro_X_add_c_prime_char],
    `MIN k n = k` by rw[MIN_DEF] >>
    `?p. prime p /\ perfect_power n p` by metis_tac[AKS_main_ulog_3] >>
    metis_tac[power_free_perfect_power]
  ]);

(* Theorem: The AKS Main Theorem (Version 6) *)
(* Proof:
   Let s = 2 * (SQRT (phi k)) * ulog n.
   If part: prime n ==>
            power-free n /\ k < n /\ !c. 0 < c /\ c <= s ==> poly_intro (ZN n) k n (x+ n c)
      This is to show:
      (1) power-free n
          True by prime_is_power_free.
      (2) k < n
          By contradiction, suppose n <= k, then MIN k n = n
          With 1 < n, and n <= n    by LESS_OR_EQ
          giving ~(n divides n)     by check on k
          But n divides n           by DIVIDES_REFL
          Hence a contradiction.
      (3) prime n /\ 0 < c /\ c <= s ==> poly_intro (ZN n) k n (x+ n c)
          Note 0 < n, 0 < k         by PRIME_POS
          Since Ring (ZN n)         by ZN_ring, 0 < n
            and char (ZN n) = n     by ZN_char, 0 < n
           Hence the result is true by poly_intro_X_add_c_prime_char, 0 < k
   Only-if part: power-free n /\ k < n /\ poly_intro_range (ZN n) k n s) ==> prime n
      Since !j. 1 < j /\ j <= k ==>
                1 < j /\ j <= k /\ j <= n      by k < n
      Thus ?p. prime p /\ perfect_power n p    by AKS_main_ulog_3
      Then p = n                               by power_free_perfect_power
      Hence prime n.
*)
val AKS_main_ulog_6 = store_thm(
  "AKS_main_ulog_6",
  ``!n k. prime k /\ (2 * ulog n) ** 2 <= ordz k n /\ (* property of k *)
         (!j. 1 < j /\ j <= (MIN k n) ==> ~(j divides n)) ==> (* checks on k *)
   (prime n <=> (power_free n /\ k < n /\
                 poly_intro_range (ZN n) k n (2 * (SQRT (phi k)) * ulog n)))``,
  rw_tac std_ss[EQ_IMP_THM] >-
  rw[prime_is_power_free] >-
 (spose_not_then strip_assume_tac >>
  `1 < n` by rw[ONE_LT_PRIME] >>
  `n <= k /\ n <= n` by decide_tac >>
  metis_tac[DIVIDES_REFL]) >-
 (`0 < n /\ 0 < k` by rw[PRIME_POS] >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `char (ZN n) = n` by rw[ZN_char] >>
  metis_tac[poly_intro_X_add_c_prime_char]) >>
  `1 < n` by rw[power_free_gt_1] >>
  `!j. 1 < j /\ j <= k ==> 1 < j /\ j <= k /\ j <= n` by decide_tac >>
  metis_tac[AKS_main_ulog_3, power_free_perfect_power]);

(* Theorem: The AKS Main Theorem (Version 7) *)
(* Proof:
   Let s = 2 * (SQRT (phi k)) * ulog n.
   If part: prime n ==> power_free n /\ (?k s. ... )
      This is to show:
      (1) prime n ==> power_free n, true      by prime_is_power_free.
      (2) ?k. prime k /\ ...
          Let m = (2 * ulog n) ** 2
          Then prime n ==> 1 < n              by ONE_LT_PRIME
           and 4 <= m, or 0 < m               by ulog_twice_sq, 1 < n
            so ?k. prime k /\ coprime k n /\ m <= ordz k n
                                              by ZN_order_big_enough
          Take this k, there are 2 goals:
          (1) prime n /\ 1 < j /\ j <= k /\ j < n ==> ~(j divides n)
              By contradiction, suppose j divides n.
              Then j = 1 or j = n             by prime_def
              This contradicts 1 < j and j < n.
          (2) prime n /\ 0 < c /\ c <= s ==> poly_intro (ZN n) k n (x+ n c)
              where s = 2 * SQRT (phi k) * (log n)
              Note 0 < n and 0 < k            by PRIME_POS
              Thus Ring (ZN n)                by ZN_ring, 0 < n
               and char (ZN n) = n            by ZN_char, 0 < n
              Hence poly_intro (ZN n) k n (x+ n c)
                                              by poly_intro_X_add_c_prime_char, 0 < k
   Only-if part: power_free n /\ (?k s. ... ) ==> prime n
      Note 1 < n                                        by power_free_gt_1
      If k < n,
         (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) becomes
         (!j. 1 < j /\ j <= k ==> ~(j divides n))       as j <= k /\ k < n ==> j < n
         with !c. 0 < c /\ c <= s ==> poly_intro (ZN n) k n (x+ n c)))
         Therefore ?p. prime p /\ perfect_power n p     by AKS_main_ulog_3
            But power_free n ==> p = n                  by power_free_perfect_power
          Hence prime n.
      Otherwise, ~(k < n),
         (!j. 0 < j /\ j <= k /\ j < n ==> ~(j divides n)) becomes
         (!j. 0 < j /\ j < n ==> ~(j divides n))        as j < n /\ n <= k ==> j < k, or j <= k
         Hence prime n                                  by prime_iff_no_proper_factor
*)
val AKS_main_ulog_7 = store_thm(
  "AKS_main_ulog_7",
  ``!n. prime n <=> power_free n /\
  (?k. prime k /\
       (2 * ulog n) ** 2 <= ordz k n /\ (* property of k *)
       (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\ (* checks on k, hidden MIN *)
       (k < n ==> (* polynomial identity checks only when k < n *)
        poly_intro_range (ZN n) k n (2 * SQRT (phi k) * ulog n)))``,
  rw_tac bool_ss[EQ_IMP_THM] >-
  rw[prime_is_power_free] >-
 (qabbrev_tac `m = (2 * ulog n) ** 2` >>
  `1 < n` by rw[ONE_LT_PRIME] >>
  `4 <= m` by rw[ulog_twice_sq, Abbr`m`] >>
  `0 < m` by decide_tac >>
  `?k. prime k /\ coprime k n /\ m <= ordz k n` by rw[ZN_order_big_enough] >>
  qexists_tac `k` >>
  rw_tac std_ss[] >-
  metis_tac[prime_def, LESS_NOT_EQ] >>
  `0 < k` by rw[PRIME_POS] >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `char (ZN n) = n` by rw[ZN_char] >>
  metis_tac[poly_intro_X_add_c_prime_char]) >>
  `1 < n` by rw[power_free_gt_1] >>
  Cases_on `k < n` >| [
    `!j. 1 < j /\ j <= k ==> 1 < j /\ j <= k /\ j < n` by decide_tac >>
    metis_tac[AKS_main_ulog_3, power_free_perfect_power],
    `!j. 1 < j /\ j < n ==> 1 < j /\ j <= k /\ j < n` by decide_tac >>
    metis_tac[prime_iff_no_proper_factor]
  ]);

(* Theorem: This is Version 7 with poly_intro made explicit. *)
(* Proof:
   Note prime k ==> 0 < k                            by PRIME_POS
   also power_free n ==> 1 < n ==> 0 < n /\ n <> 1   by power_free_gt_1
    and 0 < n ==> Ring (ZN n)                        by ZN_ring, 0 < n
   together with poly_intro_X_add_c, this is true    by AKS_main_ulog_7
*)
val AKS_main_ulog_8 = store_thm(
  "AKS_main_ulog_8",
  ``!n. prime n <=> power_free n /\
  (?k. prime k /\
       (2 * ulog n) ** 2 <= ordz k n /\ (* property of k *)
       (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\ (* checks on k, hidden MIN *)
       (k < n ==> !c. 0 < c /\ c <= 2 * SQRT (phi k) * ulog n ==>  (* AKS checks *)
                  ((x+^ n c n) == (x^+ n c n)) (pmod (ZN n) (x^- n k))))``,
  rpt strip_tac >>
  `!k. prime k ==> 0 < k` by rw[PRIME_POS] >>
  `!n. 1 < n ==> 0 < n /\ n <> 1` by decide_tac >>
  `!n. 0 < n ==> Ring (ZN n)` by rw[ZN_ring] >>
  metis_tac[AKS_main_ulog_7, poly_intro_X_add_c, power_free_gt_1]);

(* ------------------------------------------------------------------------- *)
(* Using passChecks                                                          *)
(* ------------------------------------------------------------------------- *)

(* Overload to simplify presentation *)
val _ = overload_on("passChecks",
  ``\(r:'a ring) n a k s.
         (char r) divides n /\ k < char r /\ a <= ordz k n /\ poly_intro_range r k n s``);
(* val _ = clear_overloads_on "passChecks"; *)

(* Use lowercase aks_main_thm with AKS_main_thm as they are really similar. *)

val aks_main_thm_0 = store_thm(
  "aks_main_thm_0",
  ``!(r:'a field) k z. FiniteField r /\
          mifactor z (unity k) /\ (forderz X = k) ==>
   !n a s. 1 < k /\ (a = (2 * SUC (LOG2 n)) ** 2) /\
           (s = 2 * (SQRT (phi k)) * (SUC (LOG2 n))) /\ passChecks r n a k s
       ==> perfect_power n (char r)``,
  metis_tac[AKS_main_thm_0]);

val aks_main_thm_0_alt = store_thm(
  "AKS_main_thm_0a_alt",
  ``!(r:'a field) k z. FiniteField r /\
          mifactor z (unity k) /\ 1 < deg z /\ (forderz X = k) ==>
   !n a s. (a = (2 * SUC (LOG2 n)) ** 2) /\
           (s = 2 * (SQRT (phi k)) * (SUC (LOG2 n))) /\
           passChecks r n a k s
           ==> perfect_power n (char r)``,
  metis_tac[AKS_main_thm_0_alt]);

val aks_main_thm_1 = store_thm(
  "aks_main_thm_1",
  ``!(r:'a field) k z. FiniteField r /\
           mifactor z (unity k) /\ (forderz X = k) ==>
   !n a s. 0 < k /\ (a = (2 * SUC (LOG2 n)) ** 2) /\ (* parameter a *)
           (s = 2 * (SQRT (phi k)) * (SUC (LOG2 n))) /\ (* parameter s *)
           passChecks r n a k s
       ==> perfect_power n (char r)``,
  metis_tac[AKS_main_thm_1]);

val aks_main_thm_2 = store_thm(
  "aks_main_thm_2",
  ``!(r:'a field) n a k s. FiniteField r /\
        prime k /\ (a = (2 * SUC (LOG2 n)) ** 2) /\ (* parameter a *)
        (s = 2 * (SQRT (phi k)) * (SUC (LOG2 n))) /\ (* parameter s *)
        passChecks r n a k s
    ==> perfect_power n (char r)``,
  metis_tac[AKS_main_thm_2]);

val aks_main_thm_3 = store_thm(
  "aks_main_thm_3",
  ``!n a k s. 1 < n /\ prime k /\ (* property of k *)
        (a = (2 * SUC (LOG2 n)) ** 2) /\ (* parameter a *)
        (s = 2 * (SQRT (phi k)) * (SUC (LOG2 n))) /\ (* parameter s *)
        (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\ (* later this gives k < p *)
        a <= ordz k n /\ (* condition on k *)
        poly_intro_range (ZN n) k n s (* AKS tests in (ZN n) *)
    ==> ?p. prime p /\ perfect_power n p``,
  metis_tac[AKS_main_thm_3]);

val aks_main_thm_7 = store_thm(
  "aks_main_thm_7",
  ``!n. prime n <=> power_free n /\
  (?a k s. (a = (2 * SUC (LOG2 n)) ** 2) /\
           prime k /\ (s = 2 * SQRT (phi k) * SUC (LOG2 n)) /\
           a <= ordz k n /\ (* property of k *)
           (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\ (* checks on k, hidden MIN *)
  (k < n ==> poly_intro_range (ZN n) k n s))``,
  metis_tac[AKS_main_thm_7]);

val aks_main_thm_8 = store_thm(
  "aks_main_thm_8",
  ``!n. prime n <=> power_free n /\
   (?a k s. (a = (2 * SUC (LOG2 n)) ** 2) /\ prime k /\
            (s = 2 * SQRT (phi k) * SUC (LOG2 n)) /\
            a <= ordz k n /\ (* property of k *)
            (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\ (* checks on k, hidden MIN *)
            (k < n ==> poly_intro_checks n k s))``,
  metis_tac[AKS_main_thm_8]);

(* ------------------------------------------------------------------------- *)
(* Using upper logarithm                                                     *)
(* ------------------------------------------------------------------------- *)

val aks_main_ulog_0 = store_thm(
  "aks_main_ulog_0",
  ``!(r:'a field) k z. FiniteField r /\
           mifactor z (unity k) /\ (forderz X = k) ==>
   !n a s. 1 < k /\ 0 < n /\ (a = (2 * ulog n) ** 2) /\ (* to keep 0 < a *)
           (s = 2 * SQRT (phi k) * ulog n) /\ passChecks r n a k s
       ==> perfect_power n (char r)``,
  metis_tac[AKS_main_ulog_0]);

val aks_main_ulog_0_alt = store_thm(
  "aks_main_ulog_0_alt",
  ``!(r:'a field) k z. FiniteField r /\
           mifactor z (unity k) /\ 1 < deg z /\ (forderz X = k) ==>
   !n a s. 0 < n /\ (a = (2 * ulog n) ** 2) /\ (* to keep 0 < a *)
           (s = 2 * SQRT (phi k) * ulog n) /\ passChecks r n a k s
       ==> perfect_power n (char r)``,
  metis_tac[AKS_main_ulog_0_alt]);

val aks_main_ulog_1 = store_thm(
  "aks_main_ulog_1",
  ``!(r:'a field) k z. FiniteField r /\
           mifactor z (unity k) /\ (forderz X = k) ==>
   !n a s. 0 < n /\ 0 < k /\ (a = (2 * ulog n) ** 2) /\
           (s = 2 * SQRT (phi k) * ulog n) /\ passChecks r n a k s
       ==> perfect_power n (char r)``,
  metis_tac[AKS_main_ulog_1]);

val aks_main_ulog_2 = store_thm(
  "aks_main_ulog_2",
  ``!(r:'a field) n a k s. FiniteField r /\
         0 < n /\ prime k /\ (a = (2 * ulog n) ** 2) /\
         (s = 2 * SQRT (phi k) * ulog n) /\ passChecks r n a k s
     ==> perfect_power n (char r)``,
  metis_tac[AKS_main_ulog_2]);

val aks_main_ulog_3 = store_thm(
  "aks_main_ulog_3",
  ``!n a k s. 1 < n /\ prime k /\ (a = (2 * ulog n) ** 2) /\ (s = 2 * SQRT (phi k) * ulog n) /\
             (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\
             a <= ordz k n /\ poly_intro_range (ZN n) k n s
         ==> ?p. prime p /\ perfect_power n p``,
  metis_tac[AKS_main_ulog_3]);

val aks_main_ulog_7 = store_thm(
  "aks_main_ulog_7",
  ``!n. prime n <=> power_free n /\
   (?a k s. (a = (2 * ulog n) ** 2) /\ prime k /\ (s = 2 * SQRT (phi k) * ulog n) /\
            a <= ordz k n /\
            (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
            (k < n ==> poly_intro_range (ZN n) k n s))``,
  metis_tac[AKS_main_ulog_7]);

val aks_main_ulog_8 = store_thm(
  "aks_main_ulog_8",
  ``!n. prime n <=> power_free n /\
  (?a k s. (a = (2 * ulog n) ** 2) /\ prime k /\ (s = 2 * SQRT (phi k) * ulog n) /\
           a <= ordz k n /\ (* property of k *)
           (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
           (k < n ==> poly_intro_checks n k s))``,
  metis_tac[AKS_main_ulog_8]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
