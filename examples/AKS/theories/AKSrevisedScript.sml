(* ------------------------------------------------------------------------- *)
(* AKS parameter k revised (not required to be prime)                        *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "AKSrevised";

(* ------------------------------------------------------------------------- *)

open jcLib;

(* open dependent theories *)
open prim_recTheory pred_setTheory listTheory arithmeticTheory numberTheory
     combinatoricsTheory dividesTheory gcdTheory primeTheory;

(* Get dependent theories local *)
open AKStheoremTheory;
open AKSmapsTheory;
open AKSsetsTheory;
open AKSintroTheory;
open AKSshiftTheory;
open computeParamTheory;

(* Get polynomial theory of Ring *)
open polynomialTheory polyWeakTheory polyRingTheory polyFieldTheory;
open polyDivisionTheory polyBinomialTheory polyEvalTheory;
open polyMonicTheory;
open polyFieldDivisionTheory;
open polyFieldModuloTheory;
open polyIrreducibleTheory;
open polyMapTheory;
open polyRootTheory;
open polyDividesTheory;

open monoidTheory groupTheory ringTheory fieldTheory;
open fieldMapTheory;
open fieldInstancesTheory;
open fieldBinomialTheory;
open fieldIdealTheory;
open fieldOrderTheory;
open fieldProductTheory;

open ffBasicTheory;
open ffAdvancedTheory;
open ffPolyTheory;
open ffUnityTheory;
open ffCycloTheory;

open ffExistTheory;
open ffConjugateTheory;
open ffMasterTheory;
open ffMinimalTheory;

val _ = intLib.deprecate_int ();

(* ------------------------------------------------------------------------- *)
(* AKS parameter k revised (not required to be prime) Documentation          *)
(* ------------------------------------------------------------------------- *)
(* Datatype and Overloading:
*)
(* Definitions and Theorems (# are exported):

   A revised proof of AKS Main Theorem:
   AKS_main_thm_2a   |- !r. FiniteField r /\ (CARD R = char r) ==>
                        !k n. 0 < k /\ 1 < ordz k (char r) /\ char r divides n /\
                              k < char r /\ TWICE (SUC (LOG2 n)) ** 2 <= ordz k n /\
                              poly_intro_range r k n (TWICE (SQRT (phi k)) * SUC (LOG2 n)) ==>
                              perfect_power n (char r)
   AKS_main_thm_3a   |- !n k. 1 < n /\ 0 < k /\ (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\
                              TWICE (SUC (LOG2 n)) ** 2 <= ordz k n /\
                              poly_intro_range (ZN n) k n (TWICE (SQRT (phi k)) * SUC (LOG2 n)) ==>
                          ?p. prime p /\ perfect_power n p
   AKS_main_thm_7a   |- !n. prime n <=> power_free n /\
                        ?k. 0 < k /\ TWICE (SUC (LOG2 n)) ** 2 <= ordz k n /\
                            (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                            (k < n ==> poly_intro_range (ZN n) k n (TWICE (SQRT (phi k)) * SUC (LOG2 n)))
   AKS_main_thm_8a   |- !n. prime n <=> power_free n /\
                        ?k. 0 < k /\ TWICE (SUC (LOG2 n)) ** 2 <= ordz k n /\
                            (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                            (k < n ==> poly_intro_checks n k (TWICE (SQRT (phi k)) * SUC (LOG2 n)))

   Using upper logarithm:
   AKS_main_ulog_2a  |- !r. FiniteField r /\ (CARD R = char r) ==>
                        !k n. 0 < n /\ 0 < k /\ 1 < ordz k (char r) /\ char r divides n /\
                              k < char r /\ TWICE (ulog n) ** 2 <= ordz k n /\
                              poly_intro_range r k n (TWICE (SQRT (phi k)) * ulog n) ==>
                              perfect_power n (char r)
   AKS_main_ulog_3a  |- !n k. 1 < n /\ 0 < k /\ (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\
                              TWICE (ulog n) ** 2 <= ordz k n /\
                              poly_intro_range (ZN n) k n (TWICE (SQRT (phi k)) * ulog n) ==>
                          ?p. prime p /\ perfect_power n p
   AKS_main_ulog_7a  |- !n. prime n <=> power_free n /\
                        ?k. 0 < k /\ TWICE (ulog n) ** 2 <= ordz k n /\
                            (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                            (k < n ==> poly_intro_range (ZN n) k n (TWICE (SQRT (phi k)) * ulog n))
   AKS_main_ulog_8a  |- !n. prime n <=> power_free n /\
                        ?k. 0 < k /\ TWICE (ulog n) ** 2 <= ordz k n /\
                            (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                            (k < n ==> poly_intro_checks n k (TWICE (SQRT (phi k)) * ulog n))

   Using passChecks:
   aks_main_thm_2a   |- !r. FiniteField r /\ (CARD R = char r) ==>
                        !n a k s. 0 < k /\ 1 < ordz k (char r) /\
                                  (a = TWICE (SUC (LOG2 n)) ** 2) /\
                                  (s = TWICE (SQRT (phi k)) * SUC (LOG2 n)) /\
                                  passChecks r n a k s ==> perfect_power n (char r)
   aks_main_thm_3a   |- !n a k s. 1 < n /\ 0 < k /\
                                  (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\
                                  (a = TWICE (SUC (LOG2 n)) ** 2) /\
                                  (s = TWICE (SQRT (phi k)) * SUC (LOG2 n)) /\
                                  a <= ordz k n /\ poly_intro_range (ZN n) k n s ==>
                              ?p. prime p /\ perfect_power n p
   aks_main_thm_7a   |- !n. prime n <=> power_free n /\
                        ?a k s. 0 < k /\ (a = TWICE (SUC (LOG2 n)) ** 2) /\
                                (s = TWICE (SQRT (phi k)) * SUC (LOG2 n)) /\ a <= ordz k n /\
                                (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                                (k < n ==> poly_intro_range (ZN n) k n s)
   aks_main_thm_8a   |- !n. prime n <=> power_free n /\
                        ?a k s. 0 < k /\ (a = TWICE (SUC (LOG2 n)) ** 2) /\
                                (s = TWICE (SQRT (phi k)) * SUC (LOG2 n)) /\ a <= ordz k n /\
                                (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                                (k < n ==> poly_intro_checks n k s)

   aks_main_ulog_2a  |- !r. FiniteField r /\ (CARD R = char r) ==>
                        !n a k s. 0 < n /\ 0 < k /\ 1 < ordz k (char r) /\
                                  (a = TWICE (ulog n) ** 2) /\
                                  (s = TWICE (SQRT (phi k)) * ulog n) /\
                                  passChecks r n a k s ==> perfect_power n (char r)
   aks_main_ulog_3a  |- !n a k s. 1 < n /\ 0 < k /\ (a = TWICE (ulog n) ** 2) /\
                                  (s = TWICE (SQRT (phi k)) * ulog n) /\
                                  (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\ a <= ordz k n /\
                                  poly_intro_range (ZN n) k n s ==>
                              ?p. prime p /\ perfect_power n p
   aks_main_ulog_7a  |- !n. prime n <=> power_free n /\
                        ?a k s. 0 < k /\ (a = TWICE (ulog n) ** 2) /\
                                (s = TWICE (SQRT (phi k)) * ulog n) /\ a <= ordz k n /\
                                (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                                (k < n ==> poly_intro_range (ZN n) k n s)
   aks_main_ulog_8a  |- !n. prime n <=> power_free n /\
                        ?a k s. 0 < k /\ (a = TWICE (ulog n) ** 2) /\
                                (s = TWICE (SQRT (phi k)) * ulog n) /\ a <= ordz k n /\
                                (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                                (k < n ==> poly_intro_checks n k s)

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* A revised proof of AKS Main Theorem                                       *)
(* ------------------------------------------------------------------------- *)

(* This revised version works because of the following (in ffExist):

   Nonlinear Monic Irreducible factor of (unity n) with order X = n:
   poly_unity_special_factor_exists_0
         |- !r. FiniteField r ==> !n. 0 < n /\ 1 < ordz n (CARD R) ==>
            ?h. mifactor h (unity n) /\ (deg h = ordz n (CARD R)) /\
                poly_roots (PolyModRing r h) (lift h) SUBSET
                   orders ((PolyModRing r h).prod excluding |0|) n
   poly_unity_special_factor_exists
         |- !r. FiniteField r ==> !n. 0 < n /\ 1 < ordz n (CARD R) ==>
            ?h. mifactor h (unity n) /\ (deg h = ordz n (CARD R)) /\
                (order ((PolyModRing r h).prod excluding |0|) X = n)
*)

(* Direct Proof -- with just coprime k n *)

(* Note: from 1 < k /\ coprime k n /\ 1 < ordz k n,
   apply the following to obtain: p divides n /\ 1 < ordz k p:

> ZN_order_gt_1_property;
val it = |- !m n. 0 < m /\ 1 < ordz m n ==> ?p. prime p /\ p divides n /\ 1 < ordz m p: thm

If requires, apply the following to obtain: coprime k p
but this can be easily obtained by k < char r.

> coprime_prime_factor_coprime;
val it = |- !n p. 1 < n /\ prime p /\ p divides n ==> !k. coprime n k ==> coprime p k: thm
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
   Note 1 < ordz k (CARD R)         by 1 < ordz k (char r), char r = CARD R
    ==> ?z. mifactor z (unity k) /\ (forderz X = k)
                                    by poly_unity_special_factor_exists
   The result follows               by AKS_main_thm_1
*)
val AKS_main_thm_2a = store_thm(
  "AKS_main_thm_2a",
  ``!(r:'a field). FiniteField r /\ (CARD R = char r) ==> (* condition on r *)
   !k n. 0 < k /\ 1 < ordz k (char r) /\
         (char r) divides n /\ k < char r /\
         (2 * SUC (LOG2 n)) ** 2 <= ordz k n /\ (* conditions on n, k *)
         poly_intro_range r k n (2 * SQRT (phi k) * SUC (LOG2 n)) (* AKS tests *)
     ==> perfect_power n (char r)``,
  metis_tac[AKS_main_thm_1, poly_unity_special_factor_exists]);

(* Theorem: The AKS Main Theorem (Version 3)
   Given a number n > 1,
   If there are numbers k and s such that:
      1 < k
      order of n in (ZN k) >= (2 (SUC (LOG2 n))) ** 2
      s = 2 sqrt(phi k) (SUC (LOG2 n))
      for all nonzero j <= k, coprime j n
      for all nonzero c <= s, poly_intro (ZN n) k n (zx+ c)
   Then n must be a perfect power of a prime p.
*)
(* Proof:
   If n is prime,
      Let prime p = n,
      then n = p ** 1                       by perfect_power_self
   If n is not prime,
      Step 0: find a suitable prime
      Note 1 < 2 * SUC (LOG2 n)             by 0 < SUC (LOG2 n)
       Let a = (2 * SUC (LOG2 n)) ** 2.
      Then 1 < a                            by ONE_LT_EXP
        so 1 < ordz k n                     by a <= ordz k n
       ==> ?p. prime p /\ p divides n /\
               1 < ordz k p                 by ZN_order_gt_1_property, 0 < k
      Take this prime p.

      Let s = 2 * SQRT (phi k) * SUC (LOG2 n).
      Note 1 < p            by ONE_LT_PRIME, prime p
       ==> k < p            by implication: 1 < p /\ p <= k ==> ~(p divides n)
      Also k <> 1           by ZN_order_mod_1, 1 < ordz k n
       ==> coprime k n      by coprime_by_le_not_divides, 1 < k
      Thus s <= phi k       by ZN_order_condition_property, 1 < n, coprime k n
       and phi k <= k       by phi_le
        so s < p            by s <= phi k <= k < p
      Now, poly_intro_range (ZN n) k n s    by given
           poly_intro_range (ZN p) k n s    by ring_homo_intro_ZN_to_ZN_X_add_c

      The result follows                    by AKS_main_thm_2a
*)
val AKS_main_thm_3a = store_thm(
  "AKS_main_thm_3a",
  ``!n k. 1 < n /\ 0 < k /\
         (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\ (* check on k, gives k < p later *)
         (2 * SUC (LOG2 n)) ** 2 <= ordz k n /\ (* condition on k *)
         poly_intro_range (ZN n) k n (2 * SQRT (phi k) * SUC (LOG2 n)) (* AKS tests *)
     ==> ?p. prime p /\ perfect_power n p``,
  rpt strip_tac >>
  Cases_on `prime n` >-
  metis_tac[perfect_power_self] >>
  qabbrev_tac `a = (2 * SUC (LOG2 n)) ** 2` >>
  qabbrev_tac `s = 2 * SQRT (phi k) * SUC (LOG2 n)` >>
  `1 < a` by rw[ONE_LT_EXP, Abbr`a`] >>
  `1 < ordz k n` by decide_tac >>
  `?p. prime p /\ p divides n /\ 1 < ordz k p` by rw[ZN_order_gt_1_property] >>
  qexists_tac `p` >>
  simp[] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `k < p` by metis_tac[NOT_LESS] >>
  `s < p` by
  (`k <> 1` by metis_tac[ZN_order_mod_1, LESS_NOT_EQ] >>
  `coprime k n` by rw[coprime_by_le_not_divides] >>
  `s <= phi k` by metis_tac[ZN_order_condition_property] >>
  `phi k <= k` by rw[phi_le] >>
  decide_tac) >>
  `0 < n` by decide_tac >>
  `poly_intro_range (ZN p) k n s` by metis_tac[ring_homo_intro_ZN_to_ZN_X_add_c] >>
  `FiniteField (ZN p)` by rw[ZN_finite_field] >>
  `char (ZN p) = p` by rw[ZN_char] >>
  `CARD (ZN p).carrier = p` by rw[ZN_card] >>
  metis_tac[AKS_main_thm_2a]);

(* Theorem: The AKS Main Theorem (Version 7)
   A number n is prime iff
     power-free n,
     there is number k such that:
      1 < k
      and order of n in (ZN k) >= (2 (SUC (LOG2 n)))^2
      and for all nonzero j < MIN (SUC k) n, coprime j n  (with MIN hidden)
      and if k < n, let s = 2 sqrt(phi k) (SUC (LOG2 n)),
          then for all nonzero c <= s, poly_intro (ZN n) k n (zx+ c)
*)
(* Proof:
   If part: prime n ==> power_free n /\ (?k s. ... )
      This is to show:
      (1) prime n ==> power_free n, true      by prime_is_power_free.
      (2) ?k. 1 < k /\ ...
          Let a = (2 * SUC (LOG2 n)) ** 2.
          Then 1 < n                          by ONE_LT_PRIME, prime n
           and 1 < a                          by ONE_LT_EXP, 0 < SUC (LOG2 n)
            so ?k. 1 < k /\ coprime k n /\ m <= ordz k n  by ZN_order_good_enough, 1 < n, 1 < a
          Take this k, the subgoals are:
          (1) prime n /\ 1 < j /\ j <= k /\ j < n ==> ~(j divides n)
              Ignore j <= k, this is true     by prime_def
          (2) prime n /\ 0 < c /\ c <= s ==> poly_intro (ZN n) k n (x+ n c)
              where s = 2 * SQRT (phi k) * SUC (LOG2 n).
               Note 1 < n                     by ONE_LT_PRIME, prime n
                and 0 < k                     by 1 < k
                Now Ring (ZN n)               by ZN_ring, 0 < n
                    char (ZN n) = n           by ZN_char, 0 < n
               Thus poly_intro (ZN n) k n (x+ n c)
                                              by poly_intro_X_add_c_prime_char, 0 < k

   Only-if part: power_free n /\ (?k. 1 < k /\ ... ) ==> prime n
      Note 1 < n                                        by power_free_gt_1
      If k < n,
         (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) becomes
         (!j. 1 < j /\ j <= k ==> ~(j divides n))       as j <= k /\ k < n ==> j < n
         with poly_intro_range (ZN n) k n s
         Therefore ?p. prime p /\ perfect_power n p     by AKS_main_thm_3a
            But power_free n ==> p = n                  by power_free_perfect_power
          Hence prime n.
      Otherwise, ~(k < n),
         (!j. 0 < j /\ j <= k /\ j < n ==> ~(j divides n)) becomes
         (!j. 0 < j /\ j < n ==> ~(j divides n))        as j < n /\ n <= k ==> j < k, or j <= k
          Hence prime n                                 by prime_iff_no_proper_factor
*)
val AKS_main_thm_7a = store_thm(
  "AKS_main_thm_7a",
  ``!n. prime n <=> power_free n /\
   ?k. 0 < k /\ (2 * SUC (LOG2 n)) ** 2 <= ordz k n /\
       (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
       (k < n ==> poly_intro_range (ZN n) k n (2 * SQRT (phi k) * SUC (LOG2 n)))``,
  rw_tac bool_ss[EQ_IMP_THM] >-
  rw[prime_is_power_free] >-
 (qabbrev_tac `a = (2 * SUC (LOG2 n)) ** 2` >>
  `1 < n` by rw[ONE_LT_PRIME] >>
  `1 < a` by rw[ONE_LT_EXP, Abbr`a`] >>
  `?k. 1 < k /\ coprime k n /\ a <= ordz k n` by rw[ZN_order_good_enough, Abbr`a`] >>
  qexists_tac `k` >>
  qabbrev_tac `s = 2 * SQRT (phi k) * SUC (LOG2 n)` >>
  (rw_tac std_ss[] >> simp[]) >-
  metis_tac[prime_def, LESS_NOT_EQ] >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `char (ZN n) = n` by rw[ZN_char] >>
  `0 < k` by decide_tac >>
  metis_tac[poly_intro_X_add_c_prime_char]) >>
  `1 < n` by rw[power_free_gt_1] >>
  Cases_on `k < n` >| [
    `!j. 1 < j /\ j <= k ==> 1 < j /\ j <= k /\ j < n` by decide_tac >>
    metis_tac[AKS_main_thm_3a, power_free_perfect_power],
    `!j. 1 < j /\ j < n ==> 1 < j /\ j <= k /\ j < n` by decide_tac >>
    metis_tac[prime_iff_no_proper_factor]
  ]);

(* This is a major theorem -- AKS without prime k! *)

(* Theorem: This is Version 7 with poly_intro made explicit. *)
(* Proof:
   Note  1 < k ==> 0 < k                              by arithmetic
   also  power_free n ==> 1 < n ==> 0 < n             by power_free_gt_1
    and  0 < n ==> Ring (ZN n)                        by ZN_ring, 0 < n
   together with poly_intro_X_add_c, this is true     by AKS_main_thm_7a
*)
val AKS_main_thm_8a = store_thm(
  "AKS_main_thm_8a",
  ``!n. prime n <=> power_free n /\
  (?k. 0 < k /\ (2 * SUC (LOG2 n)) ** 2 <= ordz k n /\ (* property of k *)
       (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\ (* checks on k, hidden MIN *)
       (k < n ==> poly_intro_checks n k (2 * SQRT (phi k) * SUC (LOG2 n)))) (* AKS checks *)``,
  rpt strip_tac >>
  `!n. 1 < n ==> 0 < n` by decide_tac >>
  `!n. 0 < n ==> Ring (ZN n)` by rw[ZN_ring] >>
  metis_tac[AKS_main_thm_7a, poly_intro_X_add_c, power_free_gt_1]);

(* ------------------------------------------------------------------------- *)
(* Using upper logarithm                                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: The AKS Main Theorem (Version 2) *)
(* Proof:
   Note 1 < ordz k (CARD R)         by 1 < ordz k (char r), char r = CARD R
    ==> ?z. mifactor z (unity k) /\ (forderz X = k)
                                    by poly_unity_special_factor_exists
   The result follows               by AKS_main_ulog_1
*)
val AKS_main_ulog_2a = store_thm(
  "AKS_main_ulog_2a",
  ``!(r:'a field). FiniteField r /\ (CARD R = char r) ==> (* condition on r *)
   !k n. 0 < n /\ 0 < k /\ 1 < ordz k (char r) /\
         (char r) divides n /\ k < char r /\
         (2 * ulog n) ** 2 <= ordz k n /\ (* conditions on n, k *)
         poly_intro_range r k n (2 * SQRT (phi k) * ulog n) (* AKS tests *)
     ==> perfect_power n (char r)``,
  metis_tac[AKS_main_ulog_1, poly_unity_special_factor_exists]);

(* Theorem: The AKS Main Theorem (Version 3) *)
(* Proof:
   If n is prime,
      Let prime p = n,
      then n = p ** 1                       by perfect_power_self
   If n is not prime,
      Step 0: find a suitable prime
      Note 0 < ulog n                       by ulog_pos, 1 < n
        so 1 < 2 * ulog n                   by 0 < ulog n
       Let a = (2 * ulog n) ** 2.
      Then 1 < a                            by ONE_LT_EXP
        so 1 < ordz k n                     by a <= ordz k n
       ==> ?p. prime p /\ p divides n /\
               1 < ordz k p                 by ZN_order_gt_1_property, 0 < k
      Take this prime p.

      Let s = 2 * SQRT (phi k) * ulog n.
      Note 1 < p            by ONE_LT_PRIME, prime p
       ==> k < p            by implication: 1 < p /\ p <= k ==> ~(p divides n)
      Also k <> 1           by ZN_order_mod_1, 1 < ordz k n
       ==> coprime k n      by coprime_by_le_not_divides, 1 < k
      Thus s <= phi k       by ZN_order_condition_property_3, 1 < n, coprime k n
       and phi k <= k       by phi_le
        so s < p            by s <= phi k <= k < p
      Now, poly_intro_range (ZN n) k n s    by given
           poly_intro_range (ZN p) k n s    by ring_homo_intro_ZN_to_ZN_X_add_c

      The result follows                    by AKS_main_ulog_2a
*)
val AKS_main_ulog_3a = store_thm(
  "AKS_main_ulog_3a",
  ``!n k. 1 < n /\ 0 < k /\
         (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\ (* check on k, gives k < p later *)
         (2 * ulog n) ** 2 <= ordz k n /\ (* condition on k *)
         poly_intro_range (ZN n) k n (2 * SQRT (phi k) * ulog n) (* AKS tests *)
     ==> ?p. prime p /\ perfect_power n p``,
  rpt strip_tac >>
  Cases_on `prime n` >-
  metis_tac[perfect_power_self] >>
  qabbrev_tac `a = (2 * ulog n) ** 2` >>
  qabbrev_tac `s = 2 * SQRT (phi k) * ulog n` >>
  `0 < ulog n` by rw[ulog_pos] >>
  `1 < a` by rw[ONE_LT_EXP, Abbr`a`] >>
  `1 < ordz k n` by decide_tac >>
  `?p. prime p /\ p divides n /\ 1 < ordz k p` by rw[ZN_order_gt_1_property] >>
  qexists_tac `p` >>
  simp[] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `k < p` by metis_tac[NOT_LESS] >>
  `s < p` by
  (`k <> 1` by metis_tac[ZN_order_mod_1, LESS_NOT_EQ] >>
  `coprime k n` by rw[coprime_by_le_not_divides] >>
  `s <= phi k` by metis_tac[ZN_order_condition_property_3] >>
  `phi k <= k` by rw[phi_le] >>
  decide_tac) >>
  `0 < n` by decide_tac >>
  `poly_intro_range (ZN p) k n s` by metis_tac[ring_homo_intro_ZN_to_ZN_X_add_c] >>
  `FiniteField (ZN p)` by rw[ZN_finite_field] >>
  `char (ZN p) = p` by rw[ZN_char] >>
  `CARD (ZN p).carrier = p` by rw[ZN_card] >>
  metis_tac[AKS_main_ulog_2a]);

(* Theorem: The AKS Main Theorem (Version 7) *)
(* Proof:
   If part: prime n ==> power_free n /\ (?k s. ... )
      This is to show:
      (1) prime n ==> power_free n, true      by prime_is_power_free.
      (2) ?k. 1 < k /\ ...
          Let a = (2 * ulog n) ** 2.
          Then 1 < n                          by ONE_LT_PRIME, prime n
           and 1 < a                          by ONE_LT_EXP, 0 < SUC (LOG2 n)
            so ?k. 1 < k /\ coprime k n /\ m <= ordz k n  by ZN_order_good_enough, 1 < n, 1 < a
          Take this k, the subgoals are:
          (1) prime n /\ 1 < j /\ j <= k /\ j < n ==> ~(j divides n)
              Ignore j <= k, this is true     by prime_def
          (2) prime n /\ 0 < c /\ c <= s ==> poly_intro (ZN n) k n (x+ n c)
              where s = 2 * SQRT (phi k) * ulog n.
               Note 1 < n                     by ONE_LT_PRIME, prime n
                and 0 < k                     by 1 < k
                Now Ring (ZN n)               by ZN_ring, 0 < n
                    char (ZN n) = n           by ZN_char, 0 < n
               Thus poly_intro (ZN n) k n (x+ n c)
                                              by poly_intro_X_add_c_prime_char, 0 < k

   Only-if part: power_free n /\ (?k. 1 < k /\ ... ) ==> prime n
      Note 1 < n                                        by power_free_gt_1
      If k < n,
         (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) becomes
         (!j. 1 < j /\ j <= k ==> ~(j divides n))       as j <= k /\ k < n ==> j < n
         with poly_intro_range (ZN n) k n s
         Therefore ?p. prime p /\ perfect_power n p     by AKS_main_ulog_3a
            But power_free n ==> p = n                  by power_free_perfect_power
          Hence prime n.
      Otherwise, ~(k < n),
         (!j. 0 < j /\ j <= k /\ j < n ==> ~(j divides n)) becomes
         (!j. 0 < j /\ j < n ==> ~(j divides n))        as j < n /\ n <= k ==> j < k, or j <= k
          Hence prime n                                 by prime_iff_no_proper_factor
*)
val AKS_main_ulog_7a = store_thm(
  "AKS_main_ulog_7a",
  ``!n. prime n <=> power_free n /\
   ?k. 0 < k /\ (2 * ulog n) ** 2 <= ordz k n /\
       (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
       (k < n ==> poly_intro_range (ZN n) k n (2 * SQRT (phi k) * ulog n))``,
  rw_tac bool_ss[EQ_IMP_THM] >-
  rw[prime_is_power_free] >-
 (qabbrev_tac `a = (2 * ulog n) ** 2` >>
  `1 < n` by rw[ONE_LT_PRIME] >>
  `0 < ulog n` by rw[ulog_pos] >>
  `1 < a` by rw[ONE_LT_EXP, Abbr`a`] >>
  `?k. 1 < k /\ coprime k n /\ a <= ordz k n` by rw[ZN_order_good_enough, Abbr`a`] >>
  qexists_tac `k` >>
  qabbrev_tac `s = 2 * SQRT (phi k) * ulog n` >>
  (rw_tac std_ss[] >> simp[]) >-
  metis_tac[prime_def, LESS_NOT_EQ] >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `char (ZN n) = n` by rw[ZN_char] >>
  `0 < k` by decide_tac >>
  metis_tac[poly_intro_X_add_c_prime_char]) >>
  `1 < n` by rw[power_free_gt_1] >>
  Cases_on `k < n` >| [
    `!j. 1 < j /\ j <= k ==> 1 < j /\ j <= k /\ j < n` by decide_tac >>
    metis_tac[AKS_main_ulog_3a, power_free_perfect_power],
    `!j. 1 < j /\ j < n ==> 1 < j /\ j <= k /\ j < n` by decide_tac >>
    metis_tac[prime_iff_no_proper_factor]
  ]);

(* This is a major theorem -- AKS without prime k! *)

(* Theorem: This is Version 7 with poly_intro made explicit. *)
(* Proof:
   Note  1 < k ==> 0 < k                              by arithmetic
   also  power_free n ==> 1 < n ==> 0 < n             by power_free_gt_1
    and  0 < n ==> Ring (ZN n)                        by ZN_ring, 0 < n
   together with poly_intro_X_add_c, this is true     by AKS_main_ulog_7a
*)
val AKS_main_ulog_8a = store_thm(
  "AKS_main_ulog_8a",
  ``!n. prime n <=> power_free n /\
  (?k. 0 < k /\ (2 * ulog n) ** 2 <= ordz k n /\ (* property of k *)
       (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\ (* checks on k, hidden MIN *)
       (k < n ==> poly_intro_checks n k (2 * SQRT (phi k) * ulog n))) (* AKS checks *)``,
  rpt strip_tac >>
  `!n. 1 < n ==> 0 < n` by decide_tac >>
  `!n. 0 < n ==> Ring (ZN n)` by rw[ZN_ring] >>
  metis_tac[AKS_main_ulog_7a, poly_intro_X_add_c, power_free_gt_1]);

(* ------------------------------------------------------------------------- *)
(* Using passChecks                                                          *)
(* ------------------------------------------------------------------------- *)

(* Overload to simplify presentation *)
(* val _ = overload_on("passChecks",
  ``\(r:'a ring) n a k s.
         (char r) divides n /\ k < char r /\ a <= ordz k n /\ poly_intro_range r k n s``); *)
(* val _ = clear_overloads_on "passChecks"; *)

(* Use lowercase aks_main_thm with AKS_main_thm as they are really similar. *)

val aks_main_thm_2a = store_thm(
  "aks_main_thm_2a",
  ``!(r:'a field). FiniteField r /\ (CARD R = char r) ==>
   !n a k s.  0 < k /\ 1 < ordz k (char r) /\
              (a = (2 * SUC (LOG2 n)) ** 2) /\
              (s = 2 * (SQRT (phi k)) * SUC (LOG2 n)) /\
              passChecks r n a k s ==>
              perfect_power n (char r)``,
  metis_tac[AKS_main_thm_2a]);

val aks_main_thm_3a = store_thm(
  "aks_main_thm_3a",
  ``!n a k s. 1 < n /\ 0 < k /\
             (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\
             (a = (2 * SUC (LOG2 n)) ** 2) /\
             (s = 2 * (SQRT (phi k)) * SUC (LOG2 n)) /\
             a <= ordz k n /\ poly_intro_range (ZN n) k n s ==>
         ?p. prime p /\ perfect_power n p``,
  metis_tac[AKS_main_thm_3a]);

val aks_main_thm_7a = store_thm(
  "aks_main_thm_7a",
  ``!n. prime n <=> power_free n /\
   ?a k s. 0 < k /\ (a = (2 * SUC (LOG2 n)) ** 2) /\
           (s = 2 * (SQRT (phi k)) * SUC (LOG2 n)) /\ a <= ordz k n /\
           (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
           (k < n ==> poly_intro_range (ZN n) k n s)``,
  metis_tac[AKS_main_thm_7a]);

val aks_main_thm_8a = store_thm(
  "aks_main_thm_8a",
  ``!n. prime n <=> power_free n /\
   ?a k s. 0 < k /\ (a = (2 * SUC (LOG2 n)) ** 2) /\
           (s = 2 * (SQRT (phi k)) * SUC (LOG2 n)) /\ a <= ordz k n /\
           (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
           (k < n ==> poly_intro_checks n k s)``,
  metis_tac[AKS_main_thm_8a]);

val aks_main_ulog_2a = store_thm(
  "aks_main_ulog_2a",
  ``!(r:'a field). FiniteField r /\ (CARD R = char r) ==>
   !n a k s. 0 < n /\ 0 < k /\ 1 < ordz k (char r) /\
             (a = (2 * ulog n) ** 2) /\
             (s = 2 * (SQRT (phi k)) * ulog n) /\
             passChecks r n a k s ==>
             perfect_power n (char r)``,
  metis_tac[AKS_main_ulog_2a]);

val aks_main_ulog_3a = store_thm(
  "aks_main_ulog_3a",
  ``!n a k s. 1 < n /\ 0 < k /\ (a = (2 * ulog n) ** 2) /\
             (s = 2 * (SQRT (phi k)) * ulog n) /\
             (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\ a <= ordz k n /\
             poly_intro_range (ZN n) k n s ==>
         ?p. prime p /\ perfect_power n p``,
  metis_tac[AKS_main_ulog_3a]);

val aks_main_ulog_7a = store_thm(
  "aks_main_ulog_7a",
  ``!n. prime n <=> power_free n /\
   ?a k s. 0 < k /\ (a = (2 * ulog n) ** 2) /\
           (s = 2 * (SQRT (phi k)) * ulog n) /\ a <= ordz k n /\
           (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
           (k < n ==> poly_intro_range (ZN n) k n s)``,
  metis_tac[AKS_main_ulog_7a]);

val aks_main_ulog_8a = store_thm(
  "aks_main_ulog_8a",
  ``!n. prime n <=> power_free n /\
   ?a k s. 0 < k /\ (a = (2 * ulog n) ** 2) /\
           (s = 2 * (SQRT (phi k)) * ulog n) /\ a <= ordz k n /\
           (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
           (k < n ==> poly_intro_checks n k s)``,
  metis_tac[AKS_main_ulog_8a]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
