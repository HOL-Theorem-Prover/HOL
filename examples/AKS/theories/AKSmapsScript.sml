(* ------------------------------------------------------------------------- *)
(* Mappings for Introspective Sets                                           *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "AKSmaps";

(* ------------------------------------------------------------------------- *)

open jcLib;

(* open dependent theories *)
open prim_recTheory pred_setTheory listTheory arithmeticTheory numberTheory
     logrootTheory combinatoricsTheory dividesTheory gcdTheory primeTheory;

(* Get dependent theories local *)
open AKSsetsTheory;
open AKSintroTheory;

open monoidTheory groupTheory ringTheory fieldTheory;

(* Get polynomial theory of Ring *)
open polynomialTheory polyWeakTheory polyRingTheory polyDivisionTheory;
open polyBinomialTheory polyEvalTheory;

open polyDividesTheory;
open polyMonicTheory;
open polyRootTheory;
open polyProductTheory;

open polyFieldTheory;
open polyFieldDivisionTheory;
open polyFieldModuloTheory;
open polyRingModuloTheory;
open polyModuloRingTheory;
open polyIrreducibleTheory;

open fieldInstancesTheory;

open ffBasicTheory;
open ffAdvancedTheory;
open ffPolyTheory;
open ffUnityTheory;

val _ = intLib.deprecate_int ();

(* ------------------------------------------------------------------------- *)
(* Mappings for Introspective Sets Documentation                             *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported):

   Injective Map into (Q z):
   setP_poly_mod_eq           |- !r k s. Ring r /\ 0 < k ==>
                                 !p q. p IN P /\ q IN P /\ (p == q) (pm (unity k)) ==>
                                 !m. m IN N ==> (peval (p - q) (X ** m) == |0|) (pm (unity k))
   setP_poly_mod_divisor_eq   |- !r k s z. Ring r /\ 0 < k /\ ulead z /\ (unity k % z = |0|) ==>
                                 !p q. p IN P /\ q IN P /\ (p == q) (pm z) ==>
                                 !m. m IN N ==> (peval (p - q) (X ** m) == |0|) (pm z)
   setP_poly_modN_eq          |- !r k s. Ring r /\ 0 < k ==>
                                 !p q. p IN P /\ q IN P /\ (p == q) (pm (unity k)) ==>
                                 !n. n IN M ==> (peval (p - q) (X ** n) == |0|) (pm (unity k))
   setP_poly_modN_divisor_eq  |- !r k s z. Ring r /\ 0 < k /\ ulead z /\ (unity k % z = |0|) ==>
                                 !p q. p IN P /\ q IN P /\ (p == q) (pm z) ==>
                                 !n. n IN M ==> (peval (p - q) (X ** n) == |0|) (pm z)
   setP_mod_eq_gives_modN_roots
                              |- !r k s z. Field r /\ 0 < k /\ mifactor z (unity k) ==>
                                 !p q. p IN P /\ q IN P /\ (p == q) (pm z) ==>
                                 !n. n IN M ==> rootz (lift (p - q)) (X ** n % z)
   reduceP_mod_modP_inj_0     |- !r k s z. FiniteField r /\ mifactor z (unity k) /\ 1 < deg z /\
                                           (forderz X = k) ==> INJ (\p. p % z) PM (Q z)
   reduceP_mod_modP_inj_1     |- !r k s z. Field r /\ 0 < k /\ mifactor z (unity k) /\
                                           (forderz X = k) ==> INJ (\p. p % z) PM (Q z)

   Elements of Reduced Set P as roots:
   setP_element_as_root_mod_unity  |- !r k s. Ring r /\ 0 < k ==>
                                      !n m. n IN N /\ m IN N /\ (n MOD k = m MOD k) ==>
                                      !p. p IN P ==> (peval (X ** n - X ** m) p == |0|) (pm (unity k))
   setP_element_as_root_mod_unity_factor
                                   |- !r k s z. Field r /\ 0 < k /\ mifactor z (unity k) ==>
                                      !n m. n IN N /\ m IN N /\ (n MOD k = m MOD k) ==>
                                      !p. p IN P ==> (peval (X ** n - X ** m) p == |0|) (pm z)
   setN_mod_eq_gives_modP_roots_0  |- !r k s z. Ring r /\ 0 < k /\ mifactor z (unity k) /\ 1 < deg z ==>
                                      !n m. n IN N /\ m IN N /\ (n MOD k = m MOD k) ==>
                                      !p. p IN Q z ==> rootz (lift (X ** n - X ** m)) p
   setN_mod_eq_gives_modP_roots_1  |- !r k s z. Field r /\ 0 < k /\ mifactor z (unity k) ==>
                                      !n m. n IN N /\ m IN N /\ (n MOD k = m MOD k) ==>
                                      !p. p IN Q z ==> rootz (lift (X ** n - X ** m)) p
   setN_mod_eq_gives_modP_roots_2  |- !r k s z. Field r /\ 0 < k /\ mifactor z (unity k) ==>
                                      !n m. n IN N /\ m IN N /\ (n MOD k = m MOD k) ==>
                                            Q z SUBSET rootsz (lift (X ** n - X ** m))
   setN_mod_eq_gives_modP_roots    |- !r k s z. Field r /\ 0 < k /\ mifactor z (unity k) ==>
                                      !n m. n IN N /\ m IN N /\ (n MOD k = m MOD k) ==>
                                      !p. p IN Q z ==> (peval (X ** n - X ** m) p == |0|) (pm z)

   Injective Map into M:
   reduceN_mod_modN_inj_0   |- !r k s z. Field r /\ mifactor z (unity k) /\ 1 < deg z ==>
                               !p q. 1 < p /\ 1 < q /\ p IN N /\ q IN N /\
                                     MAX p q ** TWICE (SQRT (CARD M)) < CARD (Q z) ==>
                                     INJ (\m. m MOD k) (NM p q (SQRT (CARD M))) M
   reduceN_mod_modN_inj_1   |- !r k s z. Field r /\ mifactor z (unity k) ==>
                               !p q. 1 < p /\ 1 < q /\ p IN N /\ q IN N /\
                                     MAX p q ** TWICE (SQRT (CARD M)) < CARD (Q z) ==>
                                     INJ (\m. m MOD k) (NM p q (SQRT (CARD M))) M
   reduceN_mod_modN_inj_2   |- !r k s z. Field r /\ mifactor z (unity k) ==>
                               !p q. 1 < p /\ 1 < q /\ p IN N /\ q IN N /\
                                     (p * q) ** SQRT (CARD M) < CARD (Q z) ==>
                                     INJ (\m. m MOD k) (NM p q (SQRT (CARD M))) M

   Polynomial Product map to Power set of Monomials:
   set_of_X_add_c_subset_setP_0  |- !r k s. Ring r ==>
                                    !t. t SUBSET IMAGE SUC (count s) ==>
                                        IMAGE (\c. X + |c|) t SUBSET P
   set_of_X_add_c_subset_setP    |- !r k s. Ring r ==>
                                    !h t. t SUBSET IMAGE SUC (count (MIN s h)) ==>
                                          IMAGE (\c. X + |c|) t SUBSET P
   poly_prod_set_in_setP         |- !r k s. Ring r /\ 0 < k ==>
                                    !t. FINITE t /\ t SUBSET P ==> PPROD t IN P
   reduceP_poly_subset_reduceP_0 |- !r k s. Ring r /\ 0 < k /\ s < CARD M /\ CARD M < char r ==>
                                             PPM s SUBSET PM
   reduceP_poly_subset_reduceP   |- !r k s. Ring r /\ 0 < k /\ 0 < s /\ s < char r ==>
                                             PPM (MIN s (CARD M)) SUBSET PM

   Lower Bound for (Q z) by Combinatorics:
   modP_card_lower_0 |- !r k s z. FiniteField r /\ mifactor z (unity k) /\ 1 < deg z /\
                                  (forderz X = k) /\ 0 < s /\ s < char r ==>
                                  2 ** MIN s (CARD M) <= CARD (Q z)
   modP_card_lower_1 |- !r k s z. FiniteField r /\ mifactor z (unity k) /\
                                  (forderz X = k) /\ 1 < k /\ 0 < s /\ s < char r ==>
                                  2 ** MIN s (CARD M) <= CARD (Q z)

   Improvements for Version 2:
   poly_order_prime_condition_0  |- !r. Field r ==> !z. monic z /\ ipoly z ==>
                                    !p. poly p /\ deg p < deg z /\ p <> |0| /\ p <> |1| ==>
                                    !k. prime k /\ (p ** k == |1|) (pm z) ==> (forderz p = k)
   poly_order_prime_condition    |- !r. Field r ==> !z. monic z /\ ipoly z ==>
                                    !p. poly p /\ p % z <> |0| /\ p % z <> |1| ==>
                                    !k. prime k /\ (p ** k == |1|) (pm z) ==> (forderz p = k)
   poly_X_order_prime_condition  |- !r. Field r ==> !z. monic z /\ ipoly z /\ z <> unity 1 ==>
                                    !k. prime k /\ (X ** k == |1|) (pm z) ==> (forderz X = k)
   reduceP_mod_modP_inj_2 |- !r k s z. Field r /\ prime k /\ mifactor z (unity k) /\ z <> unity 1 ==>
                                        INJ (\p. p % z) PM (Q z)
   modP_card_lower_2      |- !r k s z. FiniteField r /\ prime k /\ 0 < s /\ s < char r /\
                                       mifactor z (unity k) /\ z <> unity 1 ==>
                                       2 ** MIN s (CARD M) <= CARD (Q z)

   Upper Bound for (Q z) by Roots:
   modP_card_upper_better    |- !r k n s z. FiniteField r /\ coprime k (CARD R) /\ 1 < ordz k (CARD R) /\
          char r divides n /\ n IN N /\ ~perfect_power n (char r) /\ mifactor z (unity k) ==>
          CARD (Q z) <= n ** SQRT (CARD M)
   modP_card_upper_better_1  |- !r k n s z. FiniteField r /\ coprime k (CARD R) /\ 1 < ordz k (CARD R) /\
          char r divides n /\ n IN N /\ ~perfect_power n (char r) /\ mifactor z (unity k) ==>
          CARD (Q z) <= 2 ** (SQRT (CARD M) * ulog n)
   modP_card_upper_better_2  |- !r k n s z. FiniteField r /\ coprime k (CARD R) /\ 1 < ordz k (CARD R) /\
          char r divides n /\ n IN N /\ ~perfect_power n (char r) /\ mifactor z (unity k) ==>
          CARD (Q z) <= 2 ** (SQRT (phi k) * ulog n)

   Better Lower Bound for (Q z):
   modP_card_lower_better    |- !r k s z. FiniteField r /\ mifactor z (unity k) /\ 1 < deg z /\
                                          (forderz X = k) /\ 1 < CARD M /\ 0 < s /\ s < char r ==>
                                          2 ** MIN s (CARD M) < CARD (Q z)
   modP_card_range           |- !r k n s z. FiniteField r /\ coprime k (CARD R) /\
                                            1 < ordz k (CARD R) /\ char r divides n /\
                                            n IN N /\ ~perfect_power n (char r) /\
                                            0 < s /\ s < char r /\ mifactor z (unity k) /\ 1 < deg z /\
                                            (forderz X = k) /\ 1 < CARD M ==>
                               2 ** MIN s (CARD M) < CARD (Q z) /\ CARD (Q z) <= n ** SQRT (CARD M)

   Exponent bounds for (CARD M):
   modN_card_with_ulog_le_min_1
                    |- !r. Ring r ==>
                       !k n s. 1 < k /\ n IN N /\ ulog n ** 2 <= ordz k n ==>
                               SQRT (CARD M) * ulog n <= MIN (SQRT (phi k) * ulog n) (CARD M)
   modN_card_with_ulog_le_min_2
                    |- !r. Ring r ==>
                       !k n s. 1 < k /\ n IN N /\ TWICE (ulog n) ** 2 <= ordz k n ==>
                               TWICE (SQRT (CARD M)) * ulog n <= MIN (TWICE (SQRT (phi k)) * ulog n) (CARD M)
   modN_card_in_exp_lt_bound_0
                    |- !r. Ring r ==>
                       !k n s. 1 < k /\ 1 < n /\ n IN N /\
                               TWICE (SUC (LOG2 n)) ** 2 <= ordz k n ==>
                     n ** TWICE (SQRT (CARD M)) < 2 ** MIN (TWICE (SQRT (phi k)) * SUC (LOG2 n)) (CARD M)
   modN_card_in_exp_lt_bound_1
                    |- !r. Ring r ==>
                       !k n s. 1 < k /\ 1 < n /\ n IN N /\ (SUC (LOG2 n)) ** 2 <= ordz k n ==>
                               n ** (SQRT (CARD M)) < 2 ** MIN (SQRT (phi k) * SUC (LOG2 n)) (CARD M)
   modN_card_in_exp_lt_bound_2
                    |- !r. Ring r ==>
                       !k n s. 1 < k /\ 1 < n /\ n IN N ==>
                       !h. 0 < h /\ n < 2 ** h /\ h ** 2 <= ordz k n ==>
                           n ** SQRT (CARD M) < 2 ** MIN (SQRT (phi k) * h) (CARD M)
   modN_card_in_exp_lt_bound_3
                    |- !r. Ring r ==>
                       !k n s. 1 < k /\ 1 < n /\
                           ~perfect_power n 2 /\ n IN N /\ ulog n ** 2 <= ordz k n ==>
                           n ** SQRT (CARD M) < 2 ** MIN (SQRT (phi k) * ulog n) (CARD M)
   modN_card_in_exp_lt_bound_3_alt
                    |- !r. Ring r ==>
                       !n a k s. 1 < k /\ 1 < n /\ ~perfect_power n 2 /\
                                 (a = ulog n ** 2) /\ (s = SQRT (phi k) * ulog n) /\
                                 a <= ordz k n /\ n IN N ==>
                                 n ** SQRT (CARD M) < 2 ** MIN s (CARD M)
   modN_card_in_exp_lt_bound_4
                    |- !r. Ring r ==>
                       !k n s. 1 < k /\ 1 < n /\ ~perfect_power n 2 /\ n IN N /\
                               TWICE (ulog n) ** 2 <= ordz k n ==>
                               n ** TWICE (SQRT (CARD M)) < 2 ** MIN (TWICE (SQRT (phi k)) * ulog n) (CARD M)
   modN_card_in_exp_le_bound_0
                    |- !r. Ring r ==>
                       !k n s. 1 < k /\ 1 < n /\ n IN N /\ TWICE (ulog n) ** 2 <= ordz k n ==>
                               n ** TWICE (SQRT (CARD M)) <= 2 ** MIN (TWICE (SQRT (phi k)) * ulog n) (CARD M)
   modN_card_in_exp_le_bound_1
                    |- !r. Ring r ==>
                       !k n s. 1 < k /\ n IN N ==>
                       !h. 0 < h /\ n <= 2 ** h /\ h ** 2 <= ordz k n ==>
                           n ** SQRT (CARD M) <= 2 ** MIN (SQRT (phi k) * h) (CARD M)
   modN_card_in_exp_le_bound_2
                    |- !r. Ring r ==>
                       !k n s. 1 < k /\ 1 < n /\ n IN N /\ ulog n ** 2 <= ordz k n ==>
                               n ** SQRT (CARD M) <= 2 ** MIN (SQRT (phi k) * ulog n) (CARD M)
   modP_card_upper_better_3
                    |- !r k n s z. FiniteField r /\ coprime k (CARD R) /\ 1 < ordz k (CARD R) /\
                                   char r divides n /\ n IN N /\ ~perfect_power n (char r) /\
                                   mifactor z (unity k) /\ ulog n ** 2 <= ordz k n ==>
                                   CARD (Q z) <= 2 ** MIN (SQRT (phi k) * ulog n) (CARD M)
   modP_card_lower_better_3
                    |- !r k n s z. FiniteField r /\ mifactor z (unity k) /\ 1 < deg z /\
                                   (forderz X = k) /\ 1 < n /\ n IN N /\ ulog n ** 2 <= ordz k n /\
                                   (s = SQRT (phi k) * ulog n) /\ s < char r ==>
                                   n ** SQRT (CARD M) < CARD (Q z)
*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Injective Map into (Q z)                                                  *)
(* ------------------------------------------------------------------------- *)

(*
p IN PM /\ q IN PM /\ p % h = q % h ==> peval p X = peval q X
p IN PM /\ q IN PM /\ p % h = q % h ==> p = q  by above, poly_peval_by_X
*)

(* Theorem: !p q. p IN P /\ q IN P /\ (p == q) (pm (unity k)) ==>
            !m. m IN N ==> (peval (p - q) (X ** m) == |0|) (pm (unity k)) *)
(* Proof:
   We have:
      p IN P ==> poly p /\ m intro p       by setP_element
      q IN P ==> poly q /\ m intro q       by setP_element
   Let u = unity k,
     Then ulead u                          by poly_unity_ulead, 0 < k
     Now  (p == q) (pm u) ==> (p ** m == q ** m) (pm u)  by pmod_exp_eq
    LHS:  (p ** m == peval p (X ** m)) (pm u)            by poly_intro_def
    RHS:  (q ** m == peval q (X ** m)) (pm u)            by poly_intro_def
    Hence (peval p (X ** m) == peval q (X ** m)) (pm u)  by poly_mod_eq_eq
      and (peval (p - q) (X ** m) == |0|) (pm u)         by poly_mod_peval_eq
*)
val setP_poly_mod_eq = store_thm(
  "setP_poly_mod_eq",
  ``!(r:'a ring) k s:num. Ring r /\ 0 < k ==>
    !p q. p IN P /\ q IN P /\ (p == q) (pm (unity k)) ==>
    !m. m IN N ==> (peval (p - q) (X ** m) == |0|) (pm (unity k))``,
  rpt strip_tac >>
  `poly p /\ m intro p` by metis_tac[setP_element] >>
  `poly q /\ m intro q` by metis_tac[setP_element] >>
  qabbrev_tac `u = unity k` >>
  `poly X /\ ulead u` by rw[poly_unity_ulead, Abbr`u`] >>
  `(p ** m == q ** m) (pm u)` by rw[pmod_exp_eq] >>
  `(p ** m == peval p (X ** m)) (pm u)` by metis_tac[poly_intro_def] >>
  `(q ** m == peval q (X ** m)) (pm u)` by metis_tac[poly_intro_def] >>
  `!h n. poly h ==> poly (h ** n)` by rw[] >>
  `(peval p (X ** m) == peval q (X ** m)) (pm u)` by prove_tac[poly_mod_eq_eq, poly_peval_poly] >>
  rw[GSYM poly_mod_peval_eq]);

(* Theorem: 0 < k /\ ulead z /\ ((unity k) % h = |0|) ==>
            !p q. p IN P /\ q IN P /\ (p == q) (pm h) ==>
            !m. m IN N ==> (peval (p - q) (X ** m) == |0|) (pm h) *)
(* Proof:
   We have:
      p IN P ==> poly p /\ m intro p                     by setP_element
      q IN P ==> poly q /\ m intro q                     by setP_element
   and #1 <> #0                                          by poly_deg_pos_ring_one_ne_zero
   Let u = unity k, and pmonic u                         by poly_unity_pmonic, #1 <> #0
     Now  (p == q) (pm z) ==>  (p ** m == q ** m) (pm z) by pmod_exp_eq
     LHS: (p ** m == peval p (X ** m)) (pm u)            by poly_intro_def
     i.e. (p ** m == peval p (X ** m)) (pm z)            by poly_mod_eq_divisor
     RHS: (q ** m == peval q (X ** m)) (pm u)            by poly_intro_def
     i.e. (q ** m == peval q (X ** m)) (pm z)            by poly_mod_eq_divisor
    Hence (peval p (X ** m) == peval q (X ** m)) (pm z)  by poly_mod_eq_eq
      and (peval (p - q) (X ** m) == |0|) (pm z)         by poly_mod_peval_eq
*)
val setP_poly_mod_divisor_eq = store_thm(
  "setP_poly_mod_divisor_eq",
  ``!(r:'a ring) k s:num z. Ring r /\ 0 < k /\ ulead z /\ ((unity k) % z = |0|) ==>
    !p q. p IN P /\ q IN P /\ (p == q) (pm z) ==>
    !m. m IN N ==> (peval (p - q) (X ** m) == |0|) (pm z)``,
  rpt strip_tac >>
  `poly p /\ m intro p` by metis_tac[setP_element] >>
  `poly q /\ m intro q` by metis_tac[setP_element] >>
  qabbrev_tac `u = unity k` >>
  `poly X /\ ulead u` by rw[poly_unity_ulead, Abbr`u`] >>
  `(p ** m == q ** m) (pm z)` by rw[pmod_exp_eq] >>
  `(p ** m == peval p (X ** m)) (pm u)` by metis_tac[poly_intro_def] >>
  `(q ** m == peval q (X ** m)) (pm u)` by metis_tac[poly_intro_def] >>
  `!z n. poly z ==> poly (z ** n)` by rw[] >>
  `!u v. poly u /\ poly v ==> poly (peval u v)` by rw[] >>
  `(p ** m == peval p (X ** m)) (pm z)` by metis_tac[poly_mod_eq_divisor] >>
  `(q ** m == peval q (X ** m)) (pm z)` by metis_tac[poly_mod_eq_divisor] >>
  `(peval p (X ** m) == peval q (X ** m)) (pm z)` by prove_tac[poly_mod_eq_eq] >>
  rw[GSYM poly_mod_peval_eq]);

(* Theorem: 0 < k ==> !p q. p IN P /\ q IN P /\ (p == q) (pm (unity k)) ==>
            !n. n IN M ==> (peval (p - q) (X ** n) == |0|) (pm (unity k)) *)
(* Proof:
   For n in M, there is m IN N such that n = m MOD k,    by modN_element
   We have:
      p IN P ==> poly p /\ m intro p                     by setP_element
      q IN P ==> poly q /\ m intro q                     by setP_element
   Let u = unity k,
     Then ulead u                                        by poly_unity_ulead, 0 < k
     Now  (p == q) (pm u) ==> (p ** m == q ** m) (pm u)  by pmod_exp_eq
    LHS:  (p ** m == peval p (X ** m)) (pm u)            by poly_intro_def
    RHS:  (q ** m == peval q (X ** m)) (pm u)            by poly_intro_def
    Hence (peval p (X ** m) == peval q (X ** m)) (pm u)  by poly_mod_eq_eq
      But (X ** m == X ** n) (pm u)                      by poly_unity_exp_mod, 0 < k
       so (peval p (X ** m) == peval p (X ** n)) (pm u)  by poly_peval_mod_eq
      and (peval q (X ** m) == peval q (X ** n)) (pm u)  by poly_peval_mod_eq
    Hence (peval p (X ** n) == peval q (X ** n)) (pm u)  by poly_mod_eq_eq
       or (peval (p - q) (X ** n) == |0|) (pm u)         by poly_mod_peval_eq
*)
val setP_poly_modN_eq = store_thm(
  "setP_poly_modN_eq",
  ``!(r:'a ring) k s:num. Ring r /\ 0 < k ==>
    !p q. p IN P /\ q IN P /\ (p == q) (pm (unity k)) ==>
    !n. n IN M ==> (peval (p - q) (X ** n) == |0|) (pm (unity k))``,
  rpt strip_tac >>
  `?m. m IN N /\ (n = m MOD k)` by metis_tac[modN_element] >>
  `poly p /\ m intro p` by metis_tac[setP_element] >>
  `poly q /\ m intro q` by metis_tac[setP_element] >>
  qabbrev_tac `u = unity k` >>
  `poly X /\ ulead u` by rw[poly_unity_ulead, Abbr`u`] >>
  `(p ** m == q ** m) (pm u)` by rw[pmod_exp_eq] >>
  `(p ** m == peval p (X ** m)) (pm u)` by metis_tac[poly_intro_def] >>
  `(q ** m == peval q (X ** m)) (pm u)` by metis_tac[poly_intro_def] >>
  `poly (p ** m) /\ poly (q ** m) /\ poly (peval p (X ** m)) /\ poly (peval p (X ** n)) /\ poly (peval q (X ** m)) /\ poly (peval q (X ** n))` by rw[] >>
  `(peval p (X ** m) == peval q (X ** m)) (pm u)` by prove_tac[poly_mod_eq_eq] >>
  `(X ** m == X ** n) (pm u)` by rw[poly_unity_exp_mod, Abbr`u`] >>
  `(peval p (X ** m) == peval p (X ** n)) (pm u)` by rw[poly_peval_mod_eq] >>
  `(peval q (X ** m) == peval q (X ** n)) (pm u)` by rw[poly_peval_mod_eq] >>
  `(peval p (X ** n) == peval q (X ** n)) (pm u)` by prove_tac[poly_mod_eq_eq] >>
  rw[GSYM poly_mod_peval_eq]);

(* Theorem: ((unity k) % z = |0|) /\ p IN P /\ q IN P /\ (p == q) (pm z) ==>
            !n. n IN M ==> (peval (p - q) (X ** n) == |0|) (pm z) *)
(* Proof:
   For n in M, there is m IN N such that n = m MOD k,    by modN_element
   We have:
      p IN P ==> poly p /\ m intro p                     by setP_element
      q IN P ==> poly q /\ m intro q                     by setP_element
   Let u = unity k,
   Then ulead u                                          by poly_unity_ulead, 0 < k
   Also (X ** m == X ** n) (pm u) since n = m MOD k      by poly_unity_exp_mod, 0 < k [1]

   By m intro p:
          (p ** m == peval p (X ** m)) (pm u)            by poly_intro_def
      and (peval p (X ** m) == peval p (X ** n)) (pm u)  by poly_peval_mod_eq from [1]
      ==> (p ** m == peval p (X ** n)) (pm u)            by poly_mod_transitive
      ==> (p ** m == peval p (X ** n)) (pm z)            by poly_mod_eq_divisor [2]
   Similarly, by m intro q:
          (q ** m == peval q (X ** m)) (pm u)            by poly_intro_def
      and (peval q (X ** m) == peval q (X ** n)) (pm u)  by poly_peval_mod_eq from [1]
      ==> (q ** m == peval q (X ** n)) (pm u)            by poly_mod_transitive
      ==> (q ** m == peval q (X ** n)) (pm z)            by poly_mod_eq_divisor [3]
     Now,
          (p == q) (pm z)
     ==>  (p ** m == q ** m) (pm z)                      by pmod_exp_eq
    Hence (peval p (X ** n) == peval q (X ** n)) (pm z)  by poly_mod_eq_eq from [2], [3]
       or (peval (p - q) (X ** n) == |0|) (pm z)         by poly_mod_peval_eq
*)
val setP_poly_modN_divisor_eq = store_thm(
  "setP_poly_modN_divisor_eq",
  ``!(r:'a ring) k s:num z. Ring r /\ 0 < k /\ ulead z /\ ((unity k) % z = |0|) ==>
     !p q. p IN P /\ q IN P /\ (p == q) (pm z) ==>
       !n. n IN M ==> (peval (p - q) (X ** n) == |0|) (pm z)``,
  rpt strip_tac >>
  `?m. m IN N /\ (n = m MOD k)` by metis_tac[modN_element] >>
  `poly p /\ m intro p` by metis_tac[setP_element] >>
  `poly q /\ m intro q` by metis_tac[setP_element] >>
  qabbrev_tac `u = unity k` >>
  `poly X /\ ulead u` by rw[poly_unity_ulead, Abbr`u`] >>
  `!x. poly x ==> !n. poly (x ** n)` by rw[] >>
  `!x. poly x ==> poly (peval p x) /\ poly (peval q x)` by rw[] >>
  `(X ** m == X ** n) (pm u)` by rw[poly_unity_exp_mod, Abbr`u`] >>
  `(p ** m == peval p (X ** m)) (pm u)` by metis_tac[poly_intro_def] >>
  `(peval p (X ** m) == peval p (X ** n)) (pm u)` by rw[poly_peval_mod_eq] >>
  `(p ** m == peval p (X ** n)) (pm z)` by metis_tac[poly_mod_transitive, poly_mod_eq_divisor] >>
  `(q ** m == peval q (X ** m)) (pm u)` by metis_tac[poly_intro_def] >>
  `(peval q (X ** m) == peval q (X ** n)) (pm u)` by rw[poly_peval_mod_eq] >>
  `(q ** m == peval q (X ** n)) (pm z)` by metis_tac[poly_mod_transitive, poly_mod_eq_divisor] >>
  `(p ** m == q ** m) (pm z)` by rw[pmod_exp_eq] >>
  `(peval p (X ** n) == peval q (X ** n)) (pm z)` by prove_tac[poly_mod_eq_eq] >>
  rw[GSYM poly_mod_peval_eq]);

(*
Given:
setP_poly_mod_eq
|- !r k s. Ring r /\ #1 <> #0 ==>
     !p q. p IN P /\ q IN P /\ (p == q) (pm (unity k)) ==>
       !m. m IN N ==> (peval (p - q) (X ** m) == |0|) (pm (unity k)): thm

To prove:
not setP_poly_mod_divisor_eq
|- !r k s z. Ring r /\ #1 <> #0 /\ pmonic z /\ (unity k % z = |0|) ==>
          !p q. p IN P /\ q IN P /\ (p == q) (pm z) ==>
              !m. m IN N ==> (peval (p - q) (X ** m) == |0|) (pm z): thm

but setP_poly_modN_divisor_eq
|- !r k s z. Ring r /\ #1 <> #0 /\ pmonic z /\ (unity k % z = |0|) ==>
          !p q. p IN P /\ q IN P /\ (p == q) (pm z) ==>
              !n. n IN M ==> (peval (p - q) (X ** n) == |0|) (pm z): thm
*)

(* Theorem: 0 < k /\ mifactor z (unity k) ==> !p q. p IN P /\ q IN P /\ (p == q) (pm z) ==>
            !n. n IN M ==> rootz (lift (p - q)) (X ** n % z) *)
(* Proof:
   p IN P ==> poly p                         by setP_element_poly
   q IN P ==> poly q                         by setP_element_poly
   Let d = p - q.
   Now, n IN M and (p == q) (pm z)
   ==> (peval d (X ** n) == |0|) (pm z)      by setP_poly_modN_divisor_eq
   ==> ((peval d (X ** n)) % z = |0|)        by pmod_zero
   ==> rootz (lift (p - q)) (X ** n % z)     by poly_mod_lift_root_X_exp
*)
val setP_mod_eq_gives_modN_roots = store_thm(
  "setP_mod_eq_gives_modN_roots",
  ``!(r:'a field) k s:num z. Field r /\ 0 < k /\ mifactor z (unity k) ==>
   !p q. p IN P /\ q IN P /\ (p == q) (pm z) ==>
   !n. n IN M ==> rootz (lift (p - q)) (X ** n % z)``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  `pmonic z` by metis_tac[poly_monic_irreducible_factor] >>
  qabbrev_tac `d = p - q` >>
  `poly p /\ poly q /\ poly d` by metis_tac[setP_element_poly, poly_sub_poly] >>
  metis_tac[setP_poly_modN_divisor_eq, pmod_zero, poly_mod_lift_root_X_exp]);

(* Theorem: mifactor z (unity k) /\ 1 < deg z /\ (forderz X = k) ==> INJ (\p. p % z) PM (Q z) *)
(* Proof:
   Since 1 < deg z ==> 0 < deg z,
         monic z ==> pmonic z           by notation
     and 0 < k                          by poly_X_order_nonzero
   Let u = unity k,
      (X ** k == |1|) (pm u)            by poly_unity_pmod_eqn, 0 < k
   By INJ_DEF, this is to show:
   (1) p IN PM ==> p % z IN Q z
       True by reduceP_element_mod.
   (2) p IN PM /\ p' IN PM /\ p % z = p' % z ==> p = p'
       Let d = p - p'.
       We have  poly p and poly p'      by reduceP_element_poly
                poly d                  by poly_sub_poly
       If d = |0|,
          |0| = p - p' ==> p = p'       by poly_sub_eq_zero
       If d <> |0|,
       Show that: !n. n IN M ==> X ** n % z is a root of (lift d):
          p IN P and p' IN P                   by reduceP_subset_setP, SUBSET_DEF
          (p == p') (pm z) and (u % z = |0|)   by pmod_def_alt
          Hence  !n. n IN M
             ==> rootz (lift d) (X ** n % z)   by setP_mod_eq_gives_modN_roots
       Next, show that:
          INJ (\n. X ** n % z) M (rootsz (lift d))
          By INJ_DEF, this is to show:
          (1) X ** n % z IN rootsz (lift d)
              Since  rootz (lift d) (X ** n % z)   by above
                     deg (X ** n % z) < deg z      by poly_deg_mod_less
                     (X ** n % z) IN Rz            by poly_mod_ring_element
              Hence  X ** n % h IN rootsz (lift d) by poly_roots_member
          (2) n IN M /\ n' IN M /\ X ** n % z = X ** n' % z ==> n = n'
              n IN M ==> n < k                     by modN_element_less
              n' IN M ==> n' < k                   by modN_element_less
                  X ** n % z = X ** n' % z
              ==> (X ** n == X ** n') (pm z)       by pmod_def_alt
              Hence  n = n'                        by poly_mod_field_exp_eq_0
       Apply INJ_CARD:
          |- !f s t. INJ f s t /\ FINITE t ==> CARD s <= CARD t
          First show: FINITE (rootsz (lift d))
             Since Field (PolyModRing r z)           by poly_mod_irreducible_field
                   polyz (lift d)                    by poly_mod_lift_poly
                   |0|z = []                         by poly_ring_property
                   lift d <> |0|z                    by poly_lift_eq_zero, poly_zero
             Hence FINITE (rootsz (lift d))          by poly_roots_finite
         Therefore CARD M <= CARD (rootsz (lift d))  by INJ_CARD
       Apply poly_roots_count
              |- !r. Field r ==> !p. poly p /\ p <> |0| ==> CARD (roots p) <= deg p
              With polyz (lift d)                    by poly_mod_lift_poly, above
                   lift d <> |0|z                    by poly_lift_eq_zero, above
                   CARD (rootsz (lift d)) <= degz (lift d)
                                                     by poly_roots_count
               But degz (lift d) = deg d             by poly_mod_lift_deg
             Hence CARD M <= deg d                   by LESS_EQ_TRANS
      Get a contradiction:
          p IN PM ==> deg p < CARD M                 by reduceP_element
          p' IN PM ==> deg p' < CARD M               by reduceP_element
          deg d <= MAX (deg p) (deg p')              by poly_deg_sub
      or  deg d < CARD M                             by MAX_LE, LESS_EQ_LESS_TRANS
       Which contradicts CARD M <= deg d             from above.
*)
val reduceP_mod_modP_inj_0 = store_thm(
  "reduceP_mod_modP_inj_0",
  ``!(r:'a field) k s:num z. FiniteField r /\ mifactor z (unity k) /\ 1 < deg z /\
          (forderz X = k) ==> INJ (\p. p % z) PM (Q z)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `pmonic z` by rw[] >>
  `0 < k` by rw[poly_X_order_nonzero] >>
  qabbrev_tac `u = unity k` >>
  `(X ** k == |1|) (pm u)` by rw[poly_unity_pmod_eqn, Abbr`u`] >>
  rw_tac bool_ss[INJ_DEF] >-
  metis_tac[reduceP_element_mod] >>
  qabbrev_tac `k = forderz X` >>
  `?d. d = p - p'` by rw[] >>
  `poly p /\ poly p' /\ poly d` by metis_tac[reduceP_element_poly, poly_sub_poly] >>
  Cases_on `d = |0|` >-
  metis_tac[poly_sub_eq_zero] >>
  `p IN P /\ p' IN P` by metis_tac[reduceP_subset_setP, SUBSET_DEF] >>
  `(p == p') (pm z)` by rw[pmod_def_alt] >>
  `INJ (\n. X ** n % z) M (rootsz (lift d))` by
  (rw_tac bool_ss[INJ_DEF] >| [
    qabbrev_tac `d = p - p'` >>
    `rootz (lift d) (X ** n % z)` by metis_tac[setP_mod_eq_gives_modN_roots] >>
    rw[poly_roots_member, poly_deg_mod_less, poly_mod_ring_element],
    `n < k /\ n' < k` by metis_tac[modN_element_less] >>
    `(X ** n == X ** n') (pm z)` by rw[pmod_def_alt] >>
    metis_tac[poly_mod_field_exp_eq_0]
  ]) >>
  `Field (PolyModRing r z)` by rw[poly_mod_irreducible_field] >>
  `polyz (lift d)` by rw[poly_mod_lift_poly] >>
  `lift d <> |0|z` by metis_tac[poly_lift_eq_zero, poly_zero, poly_ring_property] >>
  `FINITE (rootsz (lift d))` by rw[poly_roots_finite] >>
  `CARD M <= CARD (rootsz (lift d))` by metis_tac[INJ_CARD] >>
  `CARD (rootsz (lift d)) <= degz (lift d)` by metis_tac[poly_roots_count] >>
  `degz (lift d) = deg d` by rw[poly_mod_lift_deg] >>
  `CARD M <= deg d` by metis_tac[LESS_EQ_TRANS] >>
  `deg p < CARD M` by metis_tac[reduceP_element] >>
  `deg p' < CARD M` by metis_tac[reduceP_element] >>
  `deg d <= MAX (deg p) (deg p')` by metis_tac[poly_deg_sub] >>
  `deg d < CARD M` by metis_tac[MAX_LE, LESS_EQ_LESS_TRANS] >>
  `~(CARD M <= deg d)` by decide_tac);
(* Not in use now *)

(* Theorem: mifactor z (unity k) /\ (forderz X = k) ==> INJ (\p. p % z) PM (Q z) *)
(* Proof:
   Since 0 < deg z                      by mifactor z (unity k)
     and monic z ==> pmonic z           by notation
     and 0 < k                          by poly_X_order_nonzero
   Let u = unity k,
      (X ** k == |1|) (pm u)            by poly_unity_pmod_eqn, #1 <> #0, 0 < k.
   By INJ_DEF, this is to show:
   (1) p IN PM ==> p % h IN Q h
       True by reduceP_element_mod.
   (2) p IN PM /\ p' IN PM /\ p % h = p' % h ==> p = p'
       Let d = p - p'.
       We have  poly p and poly p'      by reduceP_element_poly
                poly d                  by poly_sub_poly
       If d = |0|,
          |0| = p - p' ==> p = p'       by poly_sub_eq_zero
       If d <> |0|,
       Show that: !n. n IN M ==> X ** n % h is a root of (lift d):
          p IN P and p' IN P                       by reduceP_subset_setP, SUBSET_DEF
          (p == p') (pm z) and (z % z = |0|)       by pmod_def_alt
          Hence  !n. n IN M
             ==> rootz (lift d) (X ** n % h)       by setP_mod_eq_gives_modN_roots
       Next, show that:
          INJ (\n. X ** n % h) M (rootsz (lift d))
          By INJ_DEF, this is to show:
          (1) X ** n % h IN rootsz (lift d)
              Since  rootz (lift d) (X ** n % h)   by above
                     deg (X ** n % h) < deg h      by poly_deg_mod_less
                     (X ** n % h) IN Rz            by poly_mod_ring_element
              Hence  X ** n % h IN rootsz (lift d) by poly_roots_member
          (2) n IN M /\ n' IN M /\ X ** n % h = X ** n' % h ==> n = n'
              n IN M ==> n < k                     by modN_element_less
              n' IN M ==> n' < k                   by modN_element_less
                  X ** n % z = X ** n' % z
              ==> (X ** n == X ** n') (pm z)       by pmod_def_alt
              Since z <> X                         by poly_unity_irreducible_factor_not_X
              Hence  n = n'                        by poly_mod_field_exp_eq_1
       Apply INJ_CARD:
          |- !f s t. INJ f s t /\ FINITE t ==> CARD s <= CARD t
          First show: FINITE (rootsz (lift d))
             Since Field (PolyModRing r z)           by poly_mod_irreducible_field
                   polyz (lift d)                    by poly_mod_lift_poly
                   |0|z = []                         by poly_ring_property
                   lift d <> |0|z                    by poly_lift_eq_zero, poly_zero
             Hence FINITE (rootsz (lift d))          by poly_roots_finite
         Therefore CARD M <= CARD (rootsz (lift d))  by INJ_CARD
       Apply poly_roots_count
              |- !r. Field r ==> !p. poly p /\ p <> |0| ==> CARD (roots p) <= deg p
              With polyz (lift d)                    by poly_mod_lift_poly, above
                   lift d <> |0|z                    by poly_lift_eq_zero, above
                   CARD (rootsz (lift d)) <= degz (lift d)
                                                     by poly_roots_count
               But degz (lift d) = deg d             by poly_mod_lift_deg
             Hence CARD M <= deg d                   by LESS_EQ_TRANS
      Get a contradiction:
          p IN PM ==> deg p < CARD M                 by reduceP_element
          p' IN PM ==> deg p' < CARD M               by reduceP_element
          deg d <= MAX (deg p) (deg p')              by poly_deg_sub
      or  deg d < CARD M                             by MAX_LE, LESS_EQ_LESS_TRANS
       Which contradicts CARD M <= deg d             from above.
*)
val reduceP_mod_modP_inj_1 = store_thm(
  "reduceP_mod_modP_inj_1",
  ``!(r:'a field) k s:num z. Field r /\ 0 < k /\ mifactor z (unity k) /\
                 (forderz X = k) ==> INJ (\p. p % z) PM (Q z)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `pmonic z` by metis_tac[poly_monic_irreducible_factor] >>
  qabbrev_tac `u = unity k` >>
  `(X ** k == |1|) (pm u)` by rw[poly_unity_pmod_eqn, Abbr`u`] >>
  rw_tac bool_ss[INJ_DEF] >-
  metis_tac[reduceP_element_mod] >>
  qabbrev_tac `k = forderz X` >>
  `?d. d = p - p'` by rw[] >>
  `poly p /\ poly p' /\ poly d` by metis_tac[reduceP_element_poly, poly_sub_poly] >>
  Cases_on `d = |0|` >-
  metis_tac[poly_sub_eq_zero] >>
  `p IN P /\ p' IN P` by metis_tac[reduceP_subset_setP, SUBSET_DEF] >>
  `(p == p') (pm z)` by rw[pmod_def_alt] >>
  `INJ (\n. X ** n % z) M (rootsz (lift d))` by
  (rw_tac bool_ss[INJ_DEF] >| [
    qabbrev_tac `d = p - p'` >>
    `rootz (lift d) (X ** n % z)` by metis_tac[setP_mod_eq_gives_modN_roots] >>
    rw[poly_roots_member, poly_deg_mod_less, poly_mod_ring_element],
    `n < k /\ n' < k` by metis_tac[modN_element_less] >>
    `(X ** n == X ** n') (pm z)` by rw[pmod_def_alt] >>
    `z <> X` by metis_tac[poly_unity_irreducible_factor_not_X] >>
    metis_tac[poly_mod_field_exp_eq_1]
  ]) >>
  `Field (PolyModRing r z)` by rw[poly_mod_irreducible_field] >>
  `polyz (lift d)` by rw[poly_mod_lift_poly] >>
  `lift d <> |0|z` by metis_tac[poly_lift_eq_zero, poly_zero, poly_ring_property] >>
  `FINITE (rootsz (lift d))` by rw[poly_roots_finite] >>
  `CARD M <= CARD (rootsz (lift d))` by metis_tac[INJ_CARD] >>
  `CARD (rootsz (lift d)) <= degz (lift d)` by metis_tac[poly_roots_count] >>
  `degz (lift d) = deg d` by rw[poly_mod_lift_deg] >>
  `CARD M <= deg d` by metis_tac[LESS_EQ_TRANS] >>
  `deg p < CARD M` by metis_tac[reduceP_element] >>
  `deg p' < CARD M` by metis_tac[reduceP_element] >>
  `deg d <= MAX (deg p) (deg p')` by metis_tac[poly_deg_sub] >>
  `deg d < CARD M` by metis_tac[MAX_LE, LESS_EQ_LESS_TRANS] >>
  `~(CARD M <= deg d)` by decide_tac);
(* for Version 1 *)

(* ------------------------------------------------------------------------- *)
(* Elements of Reduced Set P as roots.                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < k ==> !m n. n IN N /\ m IN N /\ (n MOD k = m MOD k) ==>
            !p. p IN P ==> (peval (X ** n - X ** m) p == |0|) (pm (unity k)) *)
(* Proof:
   For p IN P,
   ==> poly q /\ n intro p /\ m intro p       by setP_element
   If #1 = #0,
      Then |1| = |0|                          by poly_one_eq_poly_zero
       But poly (peval (X ** n - X ** m) p)   by poly_peval_poly, poly_sub_poly, poly_X_exp
        so peval (X ** n - X ** m) p = |0|    by poly_one_eq_zero
      Hence true                              by poly_mod_reflexive
   If #1 <> #0,
   Let u = unity k, and pmonic u                         by poly_unity_pmonic, 0 < k, #1 <> #0
   Since n MOD k = m MOD k,                              by given
   hence (X ** n == X ** m) (pm u)                       by poly_unity_exp_mod_eq

   We also have:
        (p ** n == peval p (X ** n)) (pm u)              by poly_intro_def
        (p ** m == peval p (X ** m)) (pm u)              by poly_intro_def
   But (X ** n == X ** m) (pm z) gives
         (peval p (X ** n) == peval p (X ** m)) (pm u)   by poly_peval_mod_eq
     ==> (p ** n == p ** m) (pm u)                       by poly_mod_eq_eq
     ==> (p ** n - p ** m == |0|) (pm u)                 by poly_pmod_sub_eq_zero
        peval (X ** n - X ** m) p
      = (peval (X ** n) p - peval (X ** m) p)            by poly_peval_sub
      = (p ** n - p ** m)                                by poly_peval_X_exp
   Hence  (peval (X ** n - X ** m) p == |0|) (pm u)
*)
val setP_element_as_root_mod_unity = store_thm(
  "setP_element_as_root_mod_unity",
  ``!(r:'a ring) k s:num. Ring r /\ 0 < k ==>
   !n m. n IN N /\ m IN N /\ (n MOD k = m MOD k) ==>
   !p. p IN P ==> (peval (X ** n - X ** m) p == |0|) (pm (unity k))``,
  rpt strip_tac >>
  `poly p /\ n intro p /\ m intro p` by metis_tac[setP_element] >>
  Cases_on `#1 = #0` >| [
    `poly (peval (X ** n - X ** m) p)` by rw[] >>
    metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero, poly_mod_reflexive],
    qabbrev_tac `u = unity k` >>
    `poly X /\ poly (peval p (X ** n)) /\ poly (peval p (X ** m)) /\ poly |1| /\ pmonic u` by rw[poly_unity_pmonic, Abbr`u`] >>
    `!p. poly p ==> !n. poly (p ** n)` by rw[] >>
    `(X ** n == X ** m) (pm u)` by metis_tac[poly_unity_exp_mod_eq] >>
    `(peval p (X ** n) == p ** n) (pm u)` by metis_tac[poly_intro_def, poly_mod_symmetric] >>
    `(peval p (X ** m) == p ** m) (pm u)` by metis_tac[poly_intro_def, poly_mod_symmetric] >>
    `(peval p (X ** n) == peval p (X ** m)) (pm u)` by rw[poly_peval_mod_eq] >>
    `(p ** n == p ** m) (pm u)` by prove_tac[poly_mod_eq_eq] >>
    `(p ** n - p ** m == |0|) (pm u)` by rw[GSYM poly_pmod_sub_eq_zero] >>
    `peval (X ** n - X ** m) p = p ** n - p ** m` by rw[poly_peval_sub, poly_peval_X_exp] >>
    metis_tac[]
  ]);

(* Theorem: 0 < k /\ mifactor z (unity k) ==>
            !n m. n IN N /\ m IN N /\ (n MOD k = m MOD k) ==>
            !p. p IN P ==> (peval (X ** n - X ** m) p == |0|) (pm z) *)
(* Proof:
   First, pmonic z, since  ipoly z ==> 0 < deg z         by poly_irreducible_deg_nonzero
   For p IN P,
   ==> poly q /\ n intro p /\ m intro p                  by setP_element
   Let u = unity k, and pmonic u                         by poly_unity_pmonic, 0 < k
   With the given,
          (peval (X ** n - X ** m) p == |0|) (pm u)      by setP_element_as_root_mod_unity
   Hence  (peval (X ** n - X ** m) p == |0|) (pm z)      by poly_mod_eq_divisor
*)
val setP_element_as_root_mod_unity_factor = store_thm(
  "setP_element_as_root_mod_unity_factor",
  ``!(r:'a field) k s:num z. Field r /\ 0 < k /\ mifactor z (unity k) ==>
   !n m. n IN N /\ m IN N /\ (n MOD k = m MOD k) ==>
   !p. p IN P ==> (peval (X ** n - X ** m) p == |0|) (pm z)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `pmonic z` by metis_tac[poly_monic_irreducible_factor] >>
  `poly p /\ n intro p /\ m intro p` by metis_tac[setP_element] >>
  qabbrev_tac `u = unity k` >>
  `pmonic u` by rw[poly_unity_pmonic, Abbr`u`] >>
  `(peval (X ** n - X ** m) p == |0|) (pm u)` by metis_tac[setP_element_as_root_mod_unity] >>
  `poly (peval (X ** n - X ** m) p) /\ poly |0|` by rw[] >>
  metis_tac[poly_mod_eq_divisor]);

(* Theorem: 0 < k /\ mifactor z (unity k) /\ 1 < deg z ==>
            !n m. n IN N /\ m IN N /\ (n MOD k = m MOD k) ==>
            !p. p IN (Q z) ==> rootz (lift (X ** n - X ** m)) p *)
(* Proof:
   Note 0 < deg z                 by 1 < deg z
     so pmonic z                  by poly_monic_pmonic
    and #1 <> #0                  by poly_deg_pos_ring_one_ne_zero, 0 < deg z

   For p IN (Q z), there is q IN P such that p = q % z,  by modP_element
   We have:
      q IN P ==> poly q /\ n intro q                     by setP_element
      q IN P ==> poly q /\ m intro q                     by setP_element

   Let u = unity k, and pmonic u                         by poly_unity_pmonic, 0 < k, #1 <> #0
   Since n MOD k = m MOD k,                              by given
   Hence (X ** n == X ** m) (pm z)                       by poly_unity_exp_mod_eq
     and (peval (X ** n - X ** m) q == |0|) (pm u)       by setP_element_as_root_mod_unity
      or (peval (X ** n - X ** m) q == |0|) (pm z)       by poly_mod_eq_divisor
   Let d = X ** n - X ** m, (peval d q == |0|) (pm z)    by above
     or (peval d q) % z = |0|                            by pmod_zero
   Since (peval d p) % z = (peval d q) % z               by poly_peval_mod
     and deg p < deg z                                   by poly_deg_mod_less
      or p is a root of d, of degree limited by n, m.    by poly_mod_lift_root_by_mod_peval
*)
val setN_mod_eq_gives_modP_roots_0 = store_thm(
  "setN_mod_eq_gives_modP_roots_0",
  ``!(r:'a ring) k s:num z. Ring r /\ 0 < k /\ mifactor z (unity k) /\ 1 < deg z ==>
   !n m. n IN N /\ m IN N /\ (n MOD k = m MOD k) ==>
   !p. p IN Q z ==> rootz (lift (X ** n - X ** m)) p``,
  rpt strip_tac >>
  `pmonic z` by rw[] >>
  `0 < deg z` by decide_tac >>
  `#1 <> #0` by metis_tac[poly_deg_pos_ring_one_ne_zero] >>
  `!p. poly p ==> !n. poly (p ** n)` by rw[] >>
  `!p q. poly p /\ poly q ==> poly (peval p q)` by rw[] >>
  qabbrev_tac `d = X ** n - X ** m` >>
  `poly X /\ poly d` by rw[Abbr`d`] >>
  `?q. q IN P /\ (p = q % z)` by rw[GSYM modP_element] >>
  `poly q` by metis_tac[setP_element] >>
  `n intro q /\ m intro q` by metis_tac[setP_element] >>
  qabbrev_tac `u = unity k` >>
  `pmonic u` by rw[poly_unity_pmonic, Abbr`u`] >>
  `(peval d q == |0|) (pm u)` by metis_tac[setP_element_as_root_mod_unity] >>
  `(peval d q == |0|) (pm z)` by metis_tac[poly_mod_eq_divisor, poly_peval_poly, poly_zero_poly] >>
  `(peval d q) % z = |0|` by rw[GSYM pmod_zero] >>
  rw[poly_peval_mod, poly_deg_mod_less, poly_mod_lift_root_by_mod_peval]);
(* Not in use now *)

(*
Note: setN_mod_eq_gives_modP_roots_0
|- !r k s z. Ring r /\ 0 < k /\ mifactor z (unity k) /\ 1 < deg z ==>
          !n m. n IN N /\ m IN N /\ (n MOD k = m MOD k) ==>
              !p. p IN Q z ==> rootz (lift (X ** n - X ** m)) p
Note: originally 1 < deg h for pmonic h with 0 < 1
Now use: poly_irreducible_deg_nonzero |- !r p. Field r /\ ipoly p ==> 0 < deg p
This needs Field r due to essential use of poly_field_units, which uses properties of inverse.
*)

(* Theorem: Field r /\ 0 < k /\ mifactor z (unity k) ==>
   !n m. n IN N /\ m IN N /\ (n MOD k = m MOD k) ==>
   !p. p IN Q z ==> rootz (lift (X ** n - X ** m)) p *)
(* Proof:
   First, pmonic z, since  ipoly h ==> 0 < deg z         by poly_irreducible_deg_nonzero
   For p IN Q z, there is q IN P such that p = q % z,    by modP_element
   We have:
      q IN P ==> poly q /\ n intro q                     by setP_element
      q IN P ==> poly q /\ m intro q                     by setP_element

   Let u = unity k, and pmonic u                         by poly_unity_pmonic, 0 < k, #1 <> #0
   Since n MOD k = m MOD k,                              by given
   Hence (X ** n == X ** m) (pm u)                       by poly_unity_exp_mod_eq
     and (peval (X ** n - X ** m) q == |0|) (pm u)       by setP_element_as_root_mod_unity
      or (peval (X ** n - X ** m) q == |0|) (pm z)       by poly_mod_eq_divisor
   Let d = X ** n - X ** m,
    Then (peval d q == |0|) (pm z)                       by above
     or (peval d q) % z = |0|                            by pmod_zero
   Since (peval d p) % z = (peval d q) % z               by poly_peval_mod
     and deg p < deg z                                   by poly_deg_mod_less
      or p is a root of d, of degree limited by n, m.    by poly_mod_lift_root_by_mod_peval
*)
val setN_mod_eq_gives_modP_roots_1 = store_thm(
  "setN_mod_eq_gives_modP_roots_1",
  ``!(r:'a field) k s:num z. Field r /\ 0 < k /\ mifactor z (unity k) ==>
   !n m. n IN N /\ m IN N /\ (n MOD k = m MOD k) ==>
   !p. p IN Q z ==> rootz (lift (X ** n - X ** m)) p``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `d = X ** n - X ** m` >>
  `poly X /\ poly (X ** n) /\ poly (X ** m) /\ poly d` by rw[Abbr`d`] >>
  `pmonic z` by rw[poly_irreducible_deg_nonzero] >>
  `?q. q IN P /\ (p = q % z)` by rw[GSYM modP_element] >>
  `poly q` by metis_tac[setP_element_poly] >>
  `n intro q /\ m intro q` by metis_tac[setP_element] >>
  qabbrev_tac `u = unity k` >>
  `pmonic u` by rw[poly_unity_pmonic, Abbr`u`] >>
  `(peval d q == |0|) (pm u)` by metis_tac[setP_element_as_root_mod_unity] >>
  `(peval d q == |0|) (pm z)` by metis_tac[poly_mod_eq_divisor, poly_peval_poly, poly_zero_poly] >>
  `(peval d q) % z = |0|` by rw[GSYM pmod_zero] >>
  rw[poly_peval_mod, poly_deg_mod_less, poly_mod_lift_root_by_mod_peval]);
(* for Version 1 *)

(* Theorem: Field r /\ 0 < k /\ mifactor z (unity k) ==>
            !n m. n IN N /\ m IN N /\ (n MOD k = m MOD k) ==>
                  (Q z) SUBSET rootsz (lift (X ** n - X ** m)) *)
(* Proof:
   Note ipoly z ==> pmonic z                 by poly_irreducible_pmonic, Field r
   By poly_roots_member, SUBSET_DEF, this is to show:
   (1) x IN Q z ==> x IN Rz
       Note poly x /\ deg x < deg z          by modP_element_poly
       Thus x IN Rz                          by poly_mod_ring_element
   (2) x IN Q z ==> rootz (lift (X ** n - X ** m)) x
       This is true                          by setN_mod_eq_gives_modP_roots_1
*)
val setN_mod_eq_gives_modP_roots_2 = store_thm(
  "setN_mod_eq_gives_modP_roots_2",
  ``!r:'a field k s:num z. Field r /\ 0 < k /\ mifactor z (unity k) ==>
   !n m. n IN N /\ m IN N /\ (n MOD k = m MOD k) ==>
         (Q z) SUBSET rootsz (lift (X ** n - X ** m))``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  `pmonic z` by rw[poly_irreducible_pmonic] >>
  rw_tac std_ss[poly_roots_member, SUBSET_DEF] >-
  metis_tac[modP_element_poly, poly_mod_ring_element, NOT_ZERO] >>
  metis_tac[setN_mod_eq_gives_modP_roots_1]);

(* Theorem: 0 < k /\ mifactor z (unity k) ==>
   !n m. n IN N /\ m IN N /\ (n MOD k = m MOD k) ==>
   !p. p IN Q z ==> (peval (X ** n - X ** m) p == |0|) (pm z) *)
(* Proof:
   First, pmonic z, since  ipoly z ==> 0 < deg z         by poly_irreducible_deg_nonzero
   For p IN Q z, there is q IN P such that p = q % z,    by modP_element
   We have:
      q IN P ==> poly q /\ n intro q                     by setP_element
      q IN P ==> poly q /\ m intro q                     by setP_element

   Let u = unity k, and pmonic u                         by poly_unity_pmonic, 0 < k, #1 <> #0
   Since n MOD k = m MOD k,                              by given
   Hence (X ** n == X ** m) (pm u)                       by poly_unity_exp_mod_eq
     and (peval (X ** n - X ** m) q == |0|) (pm u)       by setP_element_as_root_mod_unity
      or (peval (X ** n - X ** m) q == |0|) (pm z)       by poly_mod_eq_divisor
   Let d = X ** n - X ** m,
    Then (peval d q == |0|) (pm z)                       by above
   Since (peval d p) % h = (peval d q) % z               by poly_peval_mod
      or (peval d p == peval d q) (pm z)                 by pmod_def_alt
   Hence (peval d p == |0|) (pm z)                       by poly_mod_transitive
*)
val setN_mod_eq_gives_modP_roots = store_thm(
  "setN_mod_eq_gives_modP_roots",
  ``!(r:'a field) k s:num z. Field r /\ 0 < k /\ mifactor z (unity k) ==>
   !n m. n IN N /\ m IN N /\ (n MOD k = m MOD k) ==>
   !p. p IN Q z ==> (peval (X ** n - X ** m) p == |0|) (pm z)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `d = X ** n - X ** m` >>
  `poly X /\ poly (X ** n) /\ poly (X ** m) /\ poly d` by rw[Abbr`d`] >>
  `pmonic z` by rw[poly_irreducible_deg_nonzero] >>
  `?q. q IN P /\ (p = q % z)` by rw[GSYM modP_element] >>
  `poly q` by metis_tac[setP_element_poly] >>
  `n intro q /\ m intro q` by metis_tac[setP_element] >>
  qabbrev_tac `u = unity k` >>
  `pmonic u` by rw[poly_unity_pmonic, Abbr`u`] >>
  `poly (peval d p) /\ poly (peval d q) /\ poly |0|` by rw[] >>
  `(peval d q == |0|) (pm u)` by metis_tac[setP_element_as_root_mod_unity] >>
  `(peval d q == |0|) (pm z)` by metis_tac[poly_mod_eq_divisor] >>
  `(peval d p == peval d q) (pm z)` by rw[poly_peval_mod, pmod_def_alt] >>
  metis_tac[poly_mod_transitive]);
(* for showing root by peval *)

(* ------------------------------------------------------------------------- *)
(* Injective Map into M                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: mifactor z (unity k) /\ 1 < deg z ==>
            1 < p /\ 1 < q /\ p IN N /\ q IN N /\
            (MAX p q) ** (2 * (SQRT (CARD M))) < CARD (Q z) ==>
            INJ (\m. m MOD k) (NM p q (SQRT (CARD M))) M *)
(* Proof:
   Let t = CARD M.
   First, since 1 < deg z means 0 < deg z, we have pmonic z.
   Also   p IN N ==> coprime p k           by setN_element_coprime
   With   1 < p, that is p <> 1, k <> 0    by coprime_0R
   Thus   0 < k.

   By INJ_DEF, this is to show:
   (1) m IN NM p q (SQRT t) ==> m MOD k IN M
           m IN NM p q (SQRT t)
       ==> m IN N           by reduceN_element_in_setN
       ==> m MOD k IN M     by setN_element_mod
   (2) m IN NM p q (SQRT t) /\ m' IN NM p q (SQRT t) ==> m = m'
       By contradiction.
       Suppose m <> m', then X ** m <> X ** m'     by poly_X_exp_eq
       Let d = X ** m - X ** m', then d <> |0|     by poly_sub_eq_zero
       m IN NM p q (SQRT t) ==> m IN N             by reduceN_element_in_setN
       m' IN NM p q (SQRT t) ==> m' IN N           by reduceN_element_in_setN
       Hence !p. p IN (Q z)
          ==> rootz (lift d) p                     by setN_mod_eq_gives_modP_roots_0
       Now, poly d ==> polyz (lift d)              by poly_mod_lift_poly
        So  (Q z) SUBSET Rz                        by modP_element_poly
       Thus (Q z) SUBSET rootsz (lift d)           by poly_roots_has_subset
       Given ipoly z,
             Field (PolyModRing r z)               by poly_mod_irreducible_field
       Since d <> |0|,
             lift d <> |0|z                        by poly_lift_eq_zero, poly_ring_property
        Thus FINITE (rootsz (lift d))              by poly_roots_finite
       Hence CARD (Q z) <= CARD (rootsz (lift d))  by CARD_SUBSET
       Since degz (lift d) = deg d                 by poly_mod_lift_deg
             CARD (rootsz (lift d)) <= deg d       by poly_roots_count
         Now deg d
          <= MAX (deg (X ** m) (deg (X ** m')      by poly_deg_sub
           = MAX m m'                              by poly_deg_X_exp
       Since  !m n. m IN NM p q n ==>
                    m <= (MAX p q) ** (2 * n)      by reduceN_element_upper
         Thus MAX m m'
           <= (MAX p q) ** (2 * SQRT t)            by MAX_LE
       Overall,
             deg d <= (MAX p q) ** (2 * SQRT t)
             CARD (Q z) <= (MAX p q) ** (2 * SQRT t)
       which contradicts the given: (MAX p q) ** (2 * SQRT t) < CARD (Q z).
*)
val reduceN_mod_modN_inj_0 = store_thm(
  "reduceN_mod_modN_inj_0",
  ``!(r:'a field) k s:num z. Field r /\ mifactor z (unity k) /\ 1 < deg z ==>
   !p q. 1 < p /\ 1 < q /\ p IN N /\ q IN N /\
        (MAX p q) ** (2 * (SQRT (CARD M))) < CARD (Q z) ==>
        INJ (\m. m MOD k) (NM p q (SQRT (CARD M))) M``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `pmonic z` by rw[] >>
  qabbrev_tac `t = CARD M` >>
  `0 < k` by metis_tac[setN_element_coprime, coprime_0R, LESS_NOT_EQ, NOT_ZERO_LT_ZERO] >>
  rw_tac bool_ss[INJ_DEF] >-
  metis_tac[reduceN_element_in_setN, setN_element_mod] >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `d = X ** m - X ** m'` >>
  `poly X /\ poly (X ** m) /\ poly (X ** m') /\ poly d` by rw[Abbr`d`] >>
  `d <> |0|` by rw[poly_X_exp_eq, poly_sub_eq_zero, Abbr`d`] >>
  `m IN N` by metis_tac[reduceN_element_in_setN] >>
  `m' IN N` by metis_tac[reduceN_element_in_setN] >>
  `!p. p IN Q z ==> rootz (lift d) p` by metis_tac[setN_mod_eq_gives_modP_roots_0] >>
  `polyz (lift d)` by rw[poly_mod_lift_poly] >>
  `deg z <> 0` by decide_tac >>
  `Q z SUBSET Rz` by prove_tac[modP_element_poly, poly_mod_ring_element, SUBSET_DEF] >>
  `Q z SUBSET rootsz (lift d)` by rw[poly_roots_has_subset] >>
  `Field (PolyModRing r z)` by rw[poly_mod_irreducible_field] >>
  `lift d <> |0|z` by metis_tac[poly_lift_eq_zero, poly_zero, poly_ring_property] >>
  `FINITE (rootsz (lift d))` by rw[poly_roots_finite] >>
  `CARD (Q z) <= CARD (rootsz (lift d))` by rw[CARD_SUBSET] >>
  `degz (lift d) = deg d` by rw[poly_mod_lift_deg] >>
  `CARD (rootsz (lift d)) <= deg d` by metis_tac[poly_roots_count] >>
  `deg d <= MAX m m'` by metis_tac[poly_deg_sub, poly_deg_X_exp, Abbr`d`] >>
  `MAX m m' <= (MAX p q) ** (2 * SQRT t)` by rw[reduceN_element_upper] >>
  `~(MAX p q ** (2 * SQRT t) < CARD (Q z))` by decide_tac);
(* Not used now *)

(* Theorem: mifactor z (unity k) ==> 1 < p /\ 1 < q /\ p IN N /\ q IN N /\
            (MAX p q) ** (2 * (SQRT (CARD M))) < CARD (Q z) ==>
            INJ (\m. m MOD k) (NM p q (SQRT (CARD M))) M *)
(* Proof:
   First, pmonic z, since  ipoly z ==> 0 < deg z     by poly_irreducible_deg_nonzero
   Let t = CARD M.
   Since p IN N, coprime p k                         by setN_element_coprime
   Given 1 < p, so p <> 1, hence k <> 0              by coprime_0R
      or 0 < k.
   By INJ_DEF, this is to show:
   (1) m IN NM p q (SQRT t) ==> m MOD k IN M
           m IN NM p q (SQRT t)
       ==> m IN N                                    by reduceN_element_in_setN
       ==> m MOD k IN M                              by setN_element_mod
   (2) m IN NM p q (SQRT t) /\ m' IN NM p q (SQRT t) ==> m = m'
       By contradiction.
       Suppose m <> m', then X ** m <> X ** m'       by poly_X_exp_eq
       Let d = X ** m - X ** m', then d <> |0|       by poly_sub_eq_zero
       m IN NM p q (SQRT t) ==> m IN N               by reduceN_element_in_setN
       m' IN NM p q (SQRT t) ==> m' IN N             by reduceN_element_in_setN
       Hence !p. p IN (Q z)
          ==> rootz (lift d) p                       by setN_mod_eq_gives_modP_roots_1
       Now, poly d ==> polyz (lift d)                by poly_mod_lift_poly
        So  (Q z) SUBSET Rz                          by modP_element_poly
       Thus (Q z) SUBSET rootsz (lift d)             by poly_roots_has_subset
       Given ipoly z,
             Field (PolyModRing r z)                 by poly_mod_irreducible_field
       Since d <> |0|,
             lift d <> |0|z                          by poly_lift_eq_zero, poly_ring_property
        Thus FINITE (rootsz (lift d))                by poly_roots_finite
       Hence CARD (Q z) <= CARD (rootsz (lift d))    by CARD_SUBSET
       Since degz (lift d) = deg d                   by poly_mod_lift_deg
             CARD (rootsz (lift d)) <= deg d         by poly_roots_count
         Now deg d
          <= MAX (deg (X ** m) (deg (X ** m')        by poly_deg_sub
                    = MAX m m'                       by poly_deg_X_exp
       Since !m n. m IN NM p q n ==>
                     m <= (MAX p q) ** (2 * n)       by reduceN_element_upper
        Thus MAX m m' <= (MAX p q) ** (2 * SQRT t)   by MAX_LE
       Overall,
             deg d <= (MAX p q) ** (2 * SQRT t)
             CARD (Q z) <= (MAX p q) ** (2 * SQRT t)
       which contradicts the given: (MAX p q) ** (2 * SQRT t) < CARD (Q z).
*)
val reduceN_mod_modN_inj_1 = store_thm(
  "reduceN_mod_modN_inj_1",
  ``!(r:'a field) k s:num z. Field r /\ mifactor z (unity k) ==>
   !p q. 1 < p /\ 1 < q /\ p IN N /\ q IN N /\
   (MAX p q) ** (2 * (SQRT (CARD M))) < CARD (Q z) ==>
   INJ (\m. m MOD k) (NM p q (SQRT (CARD M))) M``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `pmonic z` by rw[poly_irreducible_deg_nonzero] >>
  `0 < k` by metis_tac[setN_element_coprime, coprime_0R, LESS_NOT_EQ, NOT_ZERO_LT_ZERO] >>
  qabbrev_tac `t = CARD M` >>
  rw_tac bool_ss[INJ_DEF] >-
  metis_tac[reduceN_element_in_setN, setN_element_mod] >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `d = X ** m - X ** m'` >>
  `poly X /\ poly (X ** m) /\ poly (X ** m') /\ poly d` by rw[Abbr`d`] >>
  `d <> |0|` by rw[poly_X_exp_eq, poly_sub_eq_zero, Abbr`d`] >>
  `m IN N` by metis_tac[reduceN_element_in_setN] >>
  `m' IN N` by metis_tac[reduceN_element_in_setN] >>
  `!p. p IN Q z ==> rootz (lift d) p` by metis_tac[setN_mod_eq_gives_modP_roots_1] >>
  `polyz (lift d)` by rw[poly_mod_lift_poly] >>
  `deg z <> 0` by decide_tac >>
  `Q z SUBSET Rz` by prove_tac[modP_element_poly, poly_mod_ring_element, SUBSET_DEF] >>
  `Q z SUBSET rootsz (lift d)` by rw[poly_roots_has_subset] >>
  `Field (PolyModRing r z)` by rw[poly_mod_irreducible_field] >>
  `lift d <> |0|z` by metis_tac[poly_lift_eq_zero, poly_zero, poly_ring_property] >>
  `FINITE (rootsz (lift d))` by rw[poly_roots_finite] >>
  `CARD (Q z) <= CARD (rootsz (lift d))` by rw[CARD_SUBSET] >>
  `degz (lift d) = deg d` by rw[poly_mod_lift_deg] >>
  `CARD (rootsz (lift d)) <= deg d` by metis_tac[poly_roots_count] >>
  `deg d <= MAX m m'` by metis_tac[poly_deg_sub, poly_deg_X_exp, Abbr`d`] >>
  `MAX m m' <= (MAX p q) ** (2 * SQRT t)` by rw[reduceN_element_upper] >>
  `~(MAX p q ** (2 * SQRT t) < CARD (Q z))` by decide_tac);

(* Theorem: mifactor z (unity k) ==>
            !p q. 1 < p /\ 1 < q /\ p IN N /\ q IN N /\ (p * q) ** (SQRT (CARD M)) < CARD (Q z) ==>
            INJ (\m. m MOD k) (NM p q (SQRT (CARD M))) M *)
(* Proof:
   First, pmonic z, since  ipoly z ==> 0 < deg z         by poly_irreducible_deg_nonzero
   Let t = CARD M.
   Since p IN N, coprime p k                             by setN_element_coprime
   Given 1 < p, so p <> 1, hence k <> 0, or 0 < k        by coprime_0R
   By INJ_DEF, this is to show:
   (1) m IN NM p q (SQRT t) ==> m MOD k IN M
           m IN NM p q (SQRT t)
       ==> m IN N                                        by reduceN_element_in_setN
       ==> m MOD k IN M                                  by setN_element_mod
   (2) m IN NM p q (SQRT t) /\ m' IN NM p q (SQRT t) ==> m = m'
       By contradiction.
       Suppose m <> m', then X ** m <> X ** m'           by poly_X_exp_eq
       Let d = X ** m - X ** m', then d <> |0|           by poly_sub_eq_zero
       m IN NM p q (SQRT t) ==> m IN N                   by reduceN_element_in_setN
       m' IN NM p q (SQRT t) ==> m' IN N                 by reduceN_element_in_setN
       Hence !p. p IN (Q z)
          ==> rootz (lift d) p                           by setN_mod_eq_gives_modP_roots_1
       Now, poly d ==> polyz (lift d)                    by poly_mod_lift_poly
        So  (Q z) SUBSET Rz                              by modP_element_poly
       Thus (Q z) SUBSET rootsz (lift d)                 by poly_roots_has_subset
       Given ipoly z,
             Field (PolyModRing r z)                     by poly_mod_irreducible_field
       Since d <> |0|,
             lift d <> |0|z                              by poly_lift_eq_zero, poly_ring_property
        Thus FINITE (rootsz (lift d))                    by poly_roots_finite
       Hence CARD (Q z) <= CARD (rootsz (lift d))        by CARD_SUBSET
       Since degz (lift d) = deg d                       by poly_mod_lift_deg
             CARD (rootsz (lift d)) <= deg d             by poly_roots_count
         Now deg d <= MAX (deg (X ** m) (deg (X ** m')   by poly_deg_sub
                    = MAX m m'                           by poly_deg_X_exp
       Since !m n. m IN NM p q n ==> m <= (p * q) ** n   by reduceN_element_upper_better
        Thus MAX m m' <= (p * q) ** (SQRT t)             by MAX_LE
       Overall,
             deg d <= (p * q) ** (SQRT t)
             CARD (Q z) <= (p * q) ** (SQRT t)
       which contradicts the given: (p * q) ** (SQRT t) < CARD (Q z).
*)
val reduceN_mod_modN_inj_2 = store_thm(
  "reduceN_mod_modN_inj_2",
  ``!(r:'a field) k s:num z. Field r /\ mifactor z (unity k) ==>
   !p q. 1 < p /\ 1 < q /\ p IN N /\ q IN N /\
   (p * q) ** (SQRT (CARD M)) < CARD (Q z) ==>
   INJ (\m. m MOD k) (NM p q (SQRT (CARD M))) M``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `pmonic z` by rw[poly_irreducible_deg_nonzero] >>
  `0 < k` by metis_tac[setN_element_coprime, coprime_0R, LESS_NOT_EQ, NOT_ZERO_LT_ZERO] >>
  qabbrev_tac `t = CARD M` >>
  rw_tac bool_ss[INJ_DEF] >-
  metis_tac[reduceN_element_in_setN, setN_element_mod] >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `d = X ** m - X ** m'` >>
  `poly X /\ poly (X ** m) /\ poly (X ** m') /\ poly d` by rw[Abbr`d`] >>
  `d <> |0|` by rw[poly_X_exp_eq, poly_sub_eq_zero, Abbr`d`] >>
  `m IN N` by metis_tac[reduceN_element_in_setN] >>
  `m' IN N` by metis_tac[reduceN_element_in_setN] >>
  `!p. p IN Q z ==> rootz (lift d) p` by metis_tac[setN_mod_eq_gives_modP_roots_1] >>
  `polyz (lift d)` by rw[poly_mod_lift_poly] >>
  `deg z <> 0` by decide_tac >>
  `Q z SUBSET Rz` by prove_tac[modP_element_poly, poly_mod_ring_element, SUBSET_DEF] >>
  `Q z SUBSET rootsz (lift d)` by rw[poly_roots_has_subset] >>
  `Field (PolyModRing r z)` by rw[poly_mod_irreducible_field] >>
  `lift d <> |0|z` by metis_tac[poly_lift_eq_zero, poly_zero, poly_ring_property] >>
  `FINITE (rootsz (lift d))` by rw[poly_roots_finite] >>
  `CARD (Q z) <= CARD (rootsz (lift d))` by rw[CARD_SUBSET] >>
  `degz (lift d) = deg d` by rw[poly_mod_lift_deg] >>
  `CARD (rootsz (lift d)) <= deg d` by metis_tac[poly_roots_count] >>
  `deg d <= MAX m m'` by metis_tac[poly_deg_sub, poly_deg_X_exp, Abbr`d`] >>
  `MAX m m' <= (p * q) ** (SQRT t)` by rw[reduceN_element_upper_better] >>
  `~((p * q) ** (SQRT t) < CARD (Q z))` by decide_tac);

(* ------------------------------------------------------------------------- *)
(* Polynomial Product map to Power set of Monomials                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: t SUBSET (IMAGE SUC (count s)) ==> (IMAGE (\c. X + |c|) t) SUBSET P *)
(* Proof:
   By setP_def and SUBSET_DEF, this is to show:
   (1) poly (X + |c|)
       True by poly_X_add_c.
   (2) m IN N ==> m intro X + |c|
       ?n. (c = SUC n) /\ n < s  by the given condition
       Hence 0 < c and c = SUC n <= s,
       Thus true by setN_element.
*)
val set_of_X_add_c_subset_setP_0 = store_thm(
  "set_of_X_add_c_subset_setP_0",
  ``!(r:'a ring) k s:num. Ring r ==>
   !t. t SUBSET (IMAGE SUC (count s)) ==> (IMAGE (\c. X + |c|) t) SUBSET P``,
  rw[setP_def, SUBSET_DEF] >-
  rw[] >>
  `?n. (c = SUC n) /\ n < s` by rw[] >>
  `0 < c /\ c <= s` by decide_tac >>
  metis_tac[setN_element]);

(* Theorem: t SUBSET (IMAGE SUC (count (MIN s h))) ==> (IMAGE (\c. X + |c|) t) SUBSET P *)
(* Proof:
   By setP_def and SUBSET_DEF, this is to show:
   (1) poly (X + |c|)
       True by poly_X_add_c.
   (2) m IN N ==> m intro X + |c|
       ?n. (c = SUC n) /\ n < s /\ n < CARD M  by the given condition
       Hence 0 < c and SUC n < SUC s, or c <= s,
       Thus true by setN_element.
*)
val set_of_X_add_c_subset_setP = store_thm(
  "set_of_X_add_c_subset_setP",
  ``!(r:'a ring) k s:num. Ring r ==>
   !h t. t SUBSET (IMAGE SUC (count (MIN s h))) ==> (IMAGE (\c. X + |c|) t) SUBSET P``,
  rw[setP_def, SUBSET_DEF] >-
  rw[] >>
  `?n. (c = SUC n) /\ n < s /\ n < h` by rw[] >>
  `0 < c /\ c <= s` by decide_tac >>
  metis_tac[setN_element]);

(* Theorem: Ring r /\ 0 < k ==> !t. FINITE t /\ t SUBSET P ==> PPROD t IN P *)
(* Proof:
   By complete induction on t.
   If t = {},
      PPROD {} = |1|   by poly_prod_set_empty
      and |1| IN P     by setP_has_one, 0 < k
      Hence true.
   If t <> {},
      t = (CHOICE t) INSERT (REST t)    by CHOICE_INSERT_REST
        PPROD t
      = PPROD ((CHOICE t) INSERT (REST t))
      = (CHOICE t) * PPROD z ((REST t) DELETE (CHOICE t)    by poly_prod_set_thm
      = (CHOICE t) * PPROD z (REST t    by CHOICE_NOT_IN_REST, DELETE_NON_ELEMENT
      Since (CHOICE t) IN t             by CHOICE_DEF
        and t SUBSET P                  by given
            (CHOICE t) IN P             by SUBSET_DEF
       also PPROD z (REST t) IN P       by induction hypothesis
      !p. p IN P ==> poly p ==> p IN (PolyRing r).carrier by setP_element_poly, poly_ring_element
      Hence (CHOICE t) * PPROD z (REST t) IN P            by setP_closure
*)
val poly_prod_set_in_setP = store_thm(
  "poly_prod_set_in_setP",
  ``!(r:'a ring) k s:num. Ring r /\ 0 < k ==>
   !t. FINITE t /\ t SUBSET P ==> PPROD t IN P``,
  rpt strip_tac >>
  completeInduct_on `CARD t` >>
  rule_assum_tac(SIMP_RULE bool_ss[GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO]) >>
  rw_tac std_ss[] >>
  Cases_on `t = {}` >-
  rw[poly_prod_set_empty, setP_has_one] >>
  `t = (CHOICE t) INSERT (REST t)` by rw[CHOICE_INSERT_REST] >>
  `CHOICE t IN t` by rw[CHOICE_DEF] >>
  `CHOICE t IN P` by metis_tac[SUBSET_DEF] >>
  `CARD (REST t) < CARD t` by rw[CARD_REST, DECIDE ``!n. n <> 0 ==> n - 1 < n``] >>
  `(REST t) SUBSET P` by metis_tac[REST_SUBSET, SUBSET_TRANS] >>
  `PPROD (REST t) IN P` by rw[] >>
  `poly (CHOICE t)` by metis_tac[setP_element_poly] >>
  `P SUBSET (PolyRing r).carrier` by metis_tac[setP_element_poly, poly_ring_element, SUBSET_DEF] >>
  `(REST t) SUBSET (PolyRing r).carrier` by metis_tac[SUBSET_TRANS] >>
  `!p. p IN (REST t) ==> poly p` by metis_tac[poly_ring_element, SUBSET_DEF] >>
  `PPROD t = PPROD ((CHOICE t) INSERT (REST t))` by metis_tac[] >>
  `_ = (CHOICE t) * PPROD ((REST t) DELETE (CHOICE t))` by rw[poly_prod_set_thm] >>
  `_ = (CHOICE t) * PPROD (REST t)` by metis_tac[CHOICE_NOT_IN_REST, DELETE_NON_ELEMENT] >>
  rw[setP_closure]);

(*
INSERT_SUBSET;
val it = |- !x s t. x INSERT s SUBSET t <=> x IN t /\ s SUBSET t: thm
CARD_INSERT;
val it = |- !s. FINITE s ==> !x. CARD (x INSERT s) = if x IN s then CARD s else SUC (CARD s): thm
*)

(* The idea:
Let p = |0|.
 Then p NOTIN (PPM (MIN s (CARD M)))           by reduceP_poly_has_no_zero
Since p IN PM                                  by reduceP_has_zero
  and (PPM (MIN s (CARD M))) SUBSET PM,
Hence (p INSERT (PPM (MIN s (CARD M)))) SUBSET SUBSET PM.
But CARD (p INSERT (PPM (MIN s (CARD M))))
  = SUC (CARD (PPM (MIN s (CARD M))))  since p NOTIN the set,
  = SUC (PRE (2 ** MIN s (CARD M))))           by reduceP_poly_card
  = 2 ** MIN s (CARD M))                       by SUC_PRE
*)

(* Theorem: 0 < k /\ s < CARD M /\ CARD M < char r ==> PPM s SUBSET PM *)
(* Proof:
   Note char r <> 1        by s < CARD M /\ CARD M < char r
   Thus #1 <> #0           by ring_char_eq_1
   This is to show:
      s' IN PPOW (IMAGE SUC (count s)) ==>
      PPROD (IMAGE (\c. X + |c|) s') IN PM
       s' IN PPOW (IMAGE SUC (count s))
   ==> s' PSUBSET (IMAGE SUC (count s))   by IN_PPOW
   ==> s' SUBSET (IMAGE SUC (count s))    by PSUBSET_DEF
   Since FINITE (count s)                 by FINITE_COUNT
      so FINITE (IMAGE SUC (count s))     by IMAGE_FINITE
     and FINITE s'                        by SUBSET_FINITE
   To show IN PM,
   (1) PPROD (IMAGE (\c. X + |c|) s') IN P
       Since s' SUBSET (IMAGE SUC (count s))
             IMAGE (\c. X + |c|) s' SUBSET P          by set_of_X_add_c_subset_setP_0
         and FINITE (IMAGE (\c. X + |c|) s')          by IMAGE_FINITE
       Now by poly_prod_set_in_setP,
         !t. FINITE t /\ t SUBSET P ==> PPROD t IN P
       Hence true.
   (2) deg (PPROD (IMAGE (\c. X + |c|) s')) < CARD M
       Since FINITE (IMAGE SUC (count s))
         and FINITE s', this gives:
       MAX_SET s' <= MAX_SET (IMAGE SUC (count s))    by SUBSET_MAX_SET
       Since MAX_SET (IMAGE SUC (count s))
             = s                                      by MAX_SET_IMAGE_SUC_COUNT
             < char r                                 by given
       we have MAX_SET s' < char r
       Therefore,
          deg (PPROD (IMAGE (\c. X + |c|) s')) = CARD s'  by poly_prod_set_image_X_add_c_deg, #1 <> #0
       Let q = PPROD (IMAGE (\c. X + |c|) s')
       This is to show: deg q < CARD M
       Now, since SUC is injective,
         CARD (IMAGE SUC (count s))
       = CARD (count s)              by FINITE_CARD_IMAGE
       = s                           by CARD_COUNT
       < CARD M                      by given
       Since s' PSUBSET IMAGE SUC count s)
       Hence CARD s' < CARD (IMAGE SUC (count s))   by CARD_PSUBSET
       Therefore deg (PPROD (IMAGE (\c. X + |c|) s')) < CARD M.
*)
val reduceP_poly_subset_reduceP_0 = store_thm(
  "reduceP_poly_subset_reduceP_0",
  ``!(r:'a ring) k s. Ring r /\ 0 < k /\ s < CARD M /\ CARD M < char r ==>
                     PPM s SUBSET PM``,
  rpt strip_tac >>
  `char r <> 1` by decide_tac >>
  `#1 <> #0` by rw[GSYM ring_char_eq_1] >>
  rw_tac std_ss[reduceP_poly_def, SUBSET_DEF, IN_IMAGE] >>
  `s' PSUBSET (IMAGE SUC (count s))` by rw[GSYM IN_PPOW] >>
  `s' SUBSET (IMAGE SUC (count s))` by metis_tac[PSUBSET_DEF] >>
  `FINITE (IMAGE SUC (count s))` by rw[] >>
  `FINITE s'` by metis_tac[SUBSET_FINITE] >>
  rw_tac std_ss[reduceP_element] >| [
    `IMAGE (\c. X + |c|) s' SUBSET P` by metis_tac[set_of_X_add_c_subset_setP_0] >>
    `FINITE (IMAGE (\c. X + |c|) s')` by metis_tac[IMAGE_FINITE] >>
    rw[poly_prod_set_in_setP],
    `MAX_SET s' <= MAX_SET (IMAGE SUC (count s))` by rw[SUBSET_MAX_SET] >>
    `MAX_SET (IMAGE SUC (count s)) = s` by rw[MAX_SET_IMAGE_SUC_COUNT] >>
    `MAX_SET s' < char r` by decide_tac >>
    `deg (PPROD (IMAGE (\c. X + |c|) s')) = CARD s'` by rw[poly_prod_set_image_X_add_c_deg] >>
    qabbrev_tac `q = PPROD (IMAGE (\c. X + |c|) s')` >>
    `CARD (IMAGE SUC (count s)) = s` by rw[FINITE_CARD_IMAGE] >>
    `CARD s' < CARD (IMAGE SUC (count s))` by rw[CARD_PSUBSET] >>
    decide_tac
  ]);

(*
The theorem above is reasonable, since PPM s takes (X + 1) ... (X + s) to form products.
If s >= CARD M, then the product will have degree >= CARD M, not an element of PM.

The theorem above is not very useful, as we cannot confirm s < CARD M.
Later, s = SQRT (phi k) * ulog n is fixed, but only known to be s <= phi k.
Also, the best one can show is that CARD M <= phi k,
so it is possible, but not necessarily, that s < CARD M.

*)

(*
reduceP_def        |- !r k s. PM = {p | p IN P /\ deg p < CARD M}
reduceP_poly_def   |- !r n. PPM n = IMAGE (\s. PPIMAGE (\c. X + |c|) s) (PPOW (natural n))
*)

(* Theorem: 0 < k /\ 0 < s /\ s < char r ==> PPM (MIN s (CARD M)) SUBSET PM *)
(* Proof:
   Note char r <> 1            by 0 < s /\ s < char r
   Thus #1 <> #0               by ring_char_eq_1
   Let t = CARD M, and z = MIN s t.
   Note z <= s, and z <= t     by MIN_DEF
   This is to show:
      s' IN PPOW (IMAGE SUC (count z)) ==>
      PPROD (IMAGE (\c. X + |c|) s') IN PM
       s' IN PPOW (IMAGE SUC (count z))
   ==> s' PSUBSET (IMAGE SUC (count z))   by IN_PPOW
   ==> s' SUBSET (IMAGE SUC (count z))    by PSUBSET_DEF
   Since FINITE (count z)                 by FINITE_COUNT
      so FINITE (IMAGE SUC (count z))     by IMAGE_FINITE
     and FINITE s'                        by SUBSET_FINITE
   To show IN PM,
   (1) PPROD (IMAGE (\c. X + |c|) s') IN P
       Since s' SUBSET (IMAGE SUC (count z))
             IMAGE (\c. X + |c|) s' SUBSET P         by set_of_X_add_c_subset_setP
         and FINITE (IMAGE (\c. X + |c|) s')         by IMAGE_FINITE
       Now by poly_prod_set_in_setP,
         !t. FINITE t /\ t SUBSET P ==> PPROD t IN P
       Hence true.
   (2) deg (PPROD (IMAGE (\c. X + |c|) s')) < t
       Since FINITE (IMAGE SUC (count z))
         and FINITE s', this gives:
       MAX_SET s' <= MAX_SET (IMAGE SUC (count z))    by SUBSET_MAX_SET
       Since MAX_SET (IMAGE SUC (count z))
             = z                                      by MAX_SET_IMAGE_SUC_COUNT
             <= s < char r                            by given
       we have MAX_SET s' < char r
       Therefore,
          deg (PPROD (IMAGE (\c. X + |c|) s')) = CARD s'  by poly_prod_set_image_X_add_c_deg
       Let q = PPROD (IMAGE (\c. X + |c|) s')
       This is to show: deg q < CARD M
       Now, since SUC is injective,
         CARD (IMAGE SUC (count z))
       = CARD (count z)                               by FINITE_CARD_IMAGE
       = z                                            by CARD_COUNT
       Since s' PSUBSET IMAGE SUC count z)
       Hence CARD s' < CARD (IMAGE SUC (count z))     by CARD_PSUBSET
       Therefore deg (PPROD (IMAGE (\c. X + |c|) s')) < z <= t.
*)
val reduceP_poly_subset_reduceP = store_thm(
  "reduceP_poly_subset_reduceP",
  ``!(r:'a ring) k s:num. Ring r /\ 0 < k /\ 0 < s /\ s < char r ==>
     PPM (MIN s (CARD M)) SUBSET PM``,
  rpt strip_tac >>
  `char r <> 1` by decide_tac >>
  `#1 <> #0` by rw[GSYM ring_char_eq_1] >>
  qabbrev_tac `t = CARD M` >>
  qabbrev_tac `z = MIN s t` >>
  `z <= s /\ z <= t` by rw[Abbr`z`, Abbr`t`] >>
  rw_tac std_ss[reduceP_poly_def, SUBSET_DEF, IN_IMAGE] >>
  `s' PSUBSET (IMAGE SUC (count z))` by rw[GSYM IN_PPOW] >>
  `s' SUBSET (IMAGE SUC (count z))` by metis_tac[PSUBSET_DEF] >>
  `FINITE (IMAGE SUC (count z))` by rw[] >>
  `FINITE s'` by metis_tac[SUBSET_FINITE] >>
  rw_tac std_ss[reduceP_element] >| [
    `IMAGE (\c. X + |c|) s' SUBSET P` by metis_tac[set_of_X_add_c_subset_setP] >>
    `FINITE (IMAGE (\c. X + |c|) s')` by metis_tac[IMAGE_FINITE] >>
    rw[poly_prod_set_in_setP],
    `MAX_SET s' <= MAX_SET (IMAGE SUC (count z))` by rw[SUBSET_MAX_SET] >>
    `MAX_SET (IMAGE SUC (count z)) = z` by rw[MAX_SET_IMAGE_SUC_COUNT] >>
    `MAX_SET s' < char r` by decide_tac >>
    `deg (PPROD (IMAGE (\c. X + |c|) s')) = CARD s'` by rw[poly_prod_set_image_X_add_c_deg] >>
    qabbrev_tac `q = PPROD (IMAGE (\c. X + |c|) s')` >>
    `CARD (IMAGE SUC (count z)) = z` by rw[FINITE_CARD_IMAGE] >>
    `CARD s' < CARD (IMAGE SUC (count z))` by rw[CARD_PSUBSET] >>
    decide_tac
  ]);

(* ------------------------------------------------------------------------- *)
(* Lower Bound for (Q z) by Combinatorics                                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: mifactor z (unity k) /\ 1 < deg z /\
            (forderz X = k) /\ s < char r ==> 2 ** (MIN s (CARD M)) <= CARD (Q z) *)
(* Proof:
   First, 1 < k  by poly_X_order_gt_1, hence 0 < k.
   Let n = MIN s (CARD M).

   Given the conditions,
      INJ (\p. p % z) PM (Q z)              by reduceP_mod_modP_inj_0
   Now, FINITE (Q z)                        by modP_finite
   Hence  FINITE PM                         by FINITE_INJ
     and  CARD PM <= CARD (Q z)             by INJ_CARD
     But  PPM n SUBSET PM                   by reduceP_poly_subset_reduceP, 0 < k, 0 < s, s < char r.
     and  |0| IN PM                         by reduceP_has_zero, 1 < k.
   Hence ( |0| INSERT PPM n) SUBSET PM      by INSERT_SUBSET
   So CARD ( |0| INSERT PPM n) <= CARD PM   by CARD_SUBSET
   Since |0| NOTIN PPM n                    by reduceP_poly_has_no_zero
     and FINITE (PPM n)                     by reduceP_poly_finite
     CARD ( |0| INSERT PPM n)
   = SUC (CARD (PPM n))                     by CARD_INSERT, since p NOTIN the set
   = SUC (PRE (2 ** n))                     by reduceP_poly_card
   = 2 ** n                                 by SUC_PRE, with 0 < 2 ** n by ZERO_LT_EXP.
   Hence  2 ** n <= CARD (Q z)              by LESS_EQ_TRANS
*)
val modP_card_lower_0 = store_thm(
  "modP_card_lower_0",
  ``!(r:'a field) k s z. FiniteField r /\ mifactor z (unity k) /\ 1 < deg z /\
       (forderz X = k) /\ 0 < s /\ s < char r ==> 2 ** (MIN s (CARD M)) <= CARD (Q z)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `FiniteRing r` by rw[FiniteRing_def] >>
  `pmonic z` by metis_tac[poly_monic_irreducible_factor] >>
  `INJ (\p. p % z) PM (Q z)` by rw[reduceP_mod_modP_inj_0] >>
  `FINITE (Q z)` by rw[modP_finite, DECIDE``0 < 1``] >>
  `FINITE PM` by rw[reduceP_finite] >>
  `CARD PM <= CARD (Q z)` by metis_tac[INJ_CARD] >>
  `1 < k` by rw[poly_X_order_gt_1] >>
  `|0| IN PM` by rw[reduceP_has_zero] >>
  qabbrev_tac `n = MIN s (CARD M)` >>
  `0 < k` by decide_tac >>
  `PPM n SUBSET PM` by rw[reduceP_poly_subset_reduceP, Abbr`n`] >>
  `( |0| INSERT PPM n) SUBSET PM` by rw[INSERT_SUBSET] >>
  `CARD ( |0| INSERT PPM n) <= CARD PM` by rw[CARD_SUBSET] >>
  `n <= s` by rw[Abbr`n`] >>
  `n < char r` by decide_tac >>
  `|0| NOTIN PPM n` by rw[reduceP_poly_has_no_zero] >>
  `FINITE (PPM n)` by rw[reduceP_poly_finite] >>
  `CARD ( |0| INSERT PPM n) = SUC (CARD (PPM n))` by metis_tac[CARD_INSERT] >>
  `_ = SUC (PRE (2 ** n))` by rw[reduceP_poly_card] >>
  `_ = 2 ** n` by metis_tac[SUC_PRE, ZERO_LT_EXP, DECIDE``0 < 2``] >>
  decide_tac);
(* Not in use now *)

(* Theorem: mifactor z (unity k) /\ (forderz X = k) /\
            1 < k /\ 0 < s /\ s < char r ==> 2 ** (MIN s (CARD M)) <= CARD (Q z) *)
(* Proof:
   First, 1 < k  by given, hence 0 < k.
   Let n = MIN s (CARD M).

   Given the conditions,
      INJ (\p. p % z) PM (Q z)              by reduceP_mod_modP_inj_1, 0 < k.
   Now, FINITE (Q z)                        by modP_finite
   Hence  FINITE PM                         by FINITE_INJ
     and  CARD PM <= CARD (Q z)             by INJ_CARD
     But  PPM n SUBSET PM                   by reduceP_poly_subset_reduceP, 0 < k, 0 < s, s < char r.
     and  |0| IN PM                         by reduceP_has_zero, 1 < k.
   Hence ( |0| INSERT PPM n) SUBSET PM      by INSERT_SUBSET
   So CARD ( |0| INSERT PPM n) <= CARD PM   by CARD_SUBSET
   Since |0| NOTIN PPM n                    by reduceP_poly_has_no_zero
     and FINITE (PPM n)                     by reduceP_poly_finite
     CARD ( |0| INSERT PPM n)
   = SUC (CARD (PPM n))                     by CARD_INSERT, since p NOTIN the set
   = SUC (PRE (2 ** n))                     by reduceP_poly_card
   = 2 ** n                                 by SUC_PRE, with 0 < 2 ** n by ZERO_LT_EXP.
   Hence  2 ** n <= CARD (Q z)              by LESS_EQ_TRANS
*)
val modP_card_lower_1 = store_thm(
  "modP_card_lower_1",
  ``!(r:'a field) k s:num z. FiniteField r /\ mifactor z (unity k) /\ (forderz X = k) /\
         1 < k /\ 0 < s /\ s < char r ==> 2 ** (MIN s (CARD M)) <= CARD (Q z)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `FiniteRing r` by rw[FiniteRing_def] >>
  `pmonic z` by metis_tac[poly_monic_irreducible_factor] >>
  `0 < k` by decide_tac >>
  `INJ (\p. p % z) PM (Q z)` by rw[reduceP_mod_modP_inj_1] >>
  `FINITE (Q z)` by rw[modP_finite] >>
  `FINITE PM` by rw[reduceP_finite] >>
  `CARD PM <= CARD (Q z)` by metis_tac[INJ_CARD] >>
  `|0| IN PM` by rw[reduceP_has_zero] >>
  qabbrev_tac `n = MIN s (CARD M)` >>
  `PPM n SUBSET PM` by rw[reduceP_poly_subset_reduceP, Abbr`n`] >>
  `( |0| INSERT PPM n) SUBSET PM` by rw[INSERT_SUBSET] >>
  `CARD ( |0| INSERT PPM n) <= CARD PM` by rw[CARD_SUBSET] >>
  `n <= s` by rw[Abbr`n`] >>
  `n < char r` by decide_tac >>
  `|0| NOTIN PPM n` by rw[reduceP_poly_has_no_zero] >>
  `FINITE (PPM n)` by rw[reduceP_poly_finite] >>
  `CARD ( |0| INSERT PPM n) = SUC (CARD (PPM n))` by metis_tac[CARD_INSERT] >>
  `_ = SUC (PRE (2 ** n))` by rw[reduceP_poly_card] >>
  `_ = 2 ** n` by metis_tac[SUC_PRE, ZERO_LT_EXP, DECIDE``0 < 2``] >>
  decide_tac);
(* for version 1 *)

(* ------------------------------------------------------------------------- *)
(* Improvements for Version 2                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: poly p /\ deg p < deg z /\ p <> |0| /\ p <> |1| ==>
           !k. prime k /\ (p ** k == |1|) (pm z) ==> (forderz p = k) *)
(* Proof:
   Let h = forderz p.
   First, (PolyModRing r z).sum.id = |0|                      by poly_mod_ring_ids
     and  ((PolyModRing r z).prod excluding |0|).id = |1|     by poly_mod_prod_nonzero_id
     Now, FiniteField (PolyModRing r z)                       by poly_mod_irreducible_finite_field
     and  FiniteGroup ((PolyModRing r z).prod excluding |0|)  by finite_field_alt
   Since  deg p < deg z and p <> |0|                          by given
          p IN ((PolyModRing r z).prod excluding |0|).carrier by poly_mod_ring_property, excluding_def
   Hence  ((PolyModRing r z).prod excluding |0|).exp p k
         = (p ** k) % z                 by poly_mod_exp_alt
         = |1| % z                      by pmod_def_alt
         = |1|                          by poly_mod_one

   Therefore   h divides k              by group_order_condition
   which means h = 1, or h = k          by prime_def
   But h = 1 ==> p = |1|                by group_order_eq_1
   which is excluded by p <> |1|.
*)
val poly_order_prime_condition_0 = store_thm(
  "poly_order_prime_condition_0",
  ``!r:'a field. Field r ==> !z. monic z /\ ipoly z ==>
   !p. poly p /\ deg p < deg z /\ p <> |0| /\ p <> |1| ==>
   !k. prime k /\ (p ** k == |1|) (pm z) ==> (forderz p = k)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `0 < deg z` by rw[poly_irreducible_deg_nonzero] >>
  `pmonic z` by rw[] >>
  qabbrev_tac `h = forderz p` >>
  `(PolyModRing r z).sum.id = |0|` by metis_tac[poly_mod_ring_ids] >>
  `((PolyModRing r z).prod excluding |0|).id = |1|` by rw[poly_mod_prod_nonzero_id] >>
  `Group ((PolyModRing r z).prod excluding |0|)` by metis_tac[poly_mod_prod_group] >>
  (`p IN ((PolyModRing r z).prod excluding |0|).carrier` by (rw[poly_mod_ring_property, excluding_def] >> metis_tac[poly_zero])) >>
  `((PolyModRing r z).prod excluding |0|).exp p k = (p ** k) % z` by rw[poly_mod_exp_alt] >>
  `_ = |1| % z` by rw[GSYM pmod_def_alt] >>
  `_ = |1|` by rw[] >>
  metis_tac[group_order_condition, prime_def, group_order_eq_1]);
(* Not in use now *)

(* Theorem: poly p /\ p % z <> |0| /\ p % z <> |1| ==>
           !k. prime k /\ (p ** k == |1|) (pm z) ==> (forderz p = k) *)
(* Proof:
   Let h = forderz p = forderz (p % z)                              by poly_order_eq_poly_mod_order
   First, (PolyModRing r z).sum.id = |0|                            by poly_mod_ring_ids
     and  ((PolyModRing r z).prod excluding |0|).id = |1|           by poly_mod_prod_nonzero_id
     Now, Group ((PolyModRing r z).prod excluding |0|)              by poly_mod_prod_group
   Since  deg (p % z) < deg z                                       by poly_deg_mod_less
     and  p % z <> |0|                                              by given
          p % z IN ((PolyModRing r z).prod excluding |0|).carrier   by poly_mod_ring_property, excluding_def
   Given  (p ** k == |1|) (pm z)
   means  (p ** k) % z = |1| % z        by pmod_def_alt
                       = |1|            by poly_deg_one, poly_mod_less
   Hence  ((PolyModRing r z).prod excluding |0|).exp (p % z) k
         = (p % z) ** k % z             by poly_mod_exp_alt
         = (p ** k) % z                 by poly_mod_exp
         = |1|                          by above

   Therefore   h divides k              by group_order_condition
   which means h = 1, or h = k          by prime_def
   But h = 1 ==> p % z = |1|            by group_order_eq_1
   which is excluded by p % z <> |1|.
*)
val poly_order_prime_condition = store_thm(
  "poly_order_prime_condition",
  ``!r:'a field. Field r ==> !z. monic z /\ ipoly z ==>
   !p. poly p /\ p % z <> |0| /\ p % z <> |1| ==>
   !k. prime k /\ (p ** k == |1|) (pm z) ==> (forderz p = k)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `0 < deg z` by rw[poly_irreducible_deg_nonzero] >>
  `pmonic z` by rw[] >>
  qabbrev_tac `h = forderz p` >>
  `forderz (p % z) = h` by rw[poly_order_eq_poly_mod_order, Abbr`h`] >>
  `(PolyModRing r z).sum.id = |0|` by metis_tac[poly_mod_ring_ids] >>
  `((PolyModRing r z).prod excluding |0|).id = |1|` by rw[poly_mod_prod_nonzero_id] >>
  `Group ((PolyModRing r z).prod excluding |0|)` by metis_tac[poly_mod_prod_group] >>
  (`p % z IN ((PolyModRing r z).prod excluding |0|).carrier` by (rw[poly_mod_ring_property, excluding_def, poly_deg_mod_less] >> metis_tac[poly_zero])) >>
  `(p ** k) % z = |1|` by metis_tac[pmod_def_alt, poly_one_poly, poly_deg_one, poly_mod_less] >>
  `((PolyModRing r z).prod excluding |0|).exp (p % z) k = ((p % z) ** k) % z` by rw[poly_mod_exp_alt] >>
  `_ = (p ** k) % z` by rw[GSYM poly_mod_exp] >>
  `_ = |1|` by rw[] >>
  `h divides k` by metis_tac[group_order_condition] >>
  `(h = 1) \/ (h = k)` by metis_tac[prime_def] >>
  metis_tac[group_order_eq_1]);

(* Theorem: monic z /\ ipoly z /\ z <> unity 1 ==>
            !k. prime k /\ (X ** k == |1|) (pm z) ==> (forderz X = k) *)
(* Proof:
   First, 0 < deg z                      by poly_irreducible_deg_nonzero
   Hence  pmonic z                       by notation
   Show z <> X
      Since prime k, 0 < k               by PRIME_POS
        and pmonic X                     by poly_deg_X, poly_monic_X
      Given (X ** k == |1|) (pm z),
      This is X ** k % z = |1|           by pmod_def_alt
      But  X ** k % X = |0|              by poly_mod_exp, poly_div_mod_id
      If z = X, this means |0| = |1|
      which is not possible for Field    by poly_one_eq_poly_zero
   With z <> X, and z <> unity 1         by given
   We claim: X % z <> |0|
             If deg z = 1, z = factor c  by poly_monic_deg1_factor
             and X % z = c * |1|         by poly_factor_divides_X
             This equals |0| when c = #0 by poly_cmult_lzero
             but this makes z = X        by poly_sub_rzero
             which contradicts z <> X.
             If 1 < deg z, X % z = X     by poly_mod_less
             and X <> |0| as they differ in degree.
        and: X % z <> |1|
             If deg z = 1, z = factor c  by poly_monic_deg1_factor
             and X % z = c * |1|         by poly_factor_divides_X
             This equals |1| when c = #1 by poly_cmult_lone
             but this makes z = unity 1  by poly_unity_1
             which contradicts z <> unity 1
             If 1 < deg z, X % z = X     by poly_mod_less
             and X <> |1| as they differ in degree.
   Hence X % z <> |0|, and X % z <> |1|.
   and the result follows by poly_order_prime_condition.
*)
val poly_X_order_prime_condition = store_thm(
  "poly_X_order_prime_condition",
  ``!r:'a field. Field r ==> !z. monic z /\ ipoly z /\ z <> unity 1 ==>
   !k. prime k /\ (X ** k == |1|) (pm z) ==> (forderz X = k)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `0 < deg z` by rw[poly_irreducible_deg_nonzero] >>
  `pmonic z` by rw[] >>
  `poly X` by rw[] >>
  `0 < k` by rw[PRIME_POS] >>
  `k <> 0` by decide_tac >>
  `pmonic X` by rw[] >>
  `X ** k % z = |1|` by metis_tac[pmod_def_alt, poly_one_poly, poly_deg_one, poly_mod_less] >>
  `X ** k % X = |0|` by metis_tac[poly_mod_exp, poly_div_mod_id, poly_zero_exp, poly_mod_zero] >>
  `z <> X` by metis_tac[poly_one_eq_poly_zero] >>
  `X % z <> |0| /\ X % z <> |1|` by
  (rw_tac std_ss[] >| [
    Cases_on `deg z = 1` >| [
      `?c. c IN R /\ (z = factor c)` by rw[poly_monic_deg1_factor] >>
      `c <> #0` by metis_tac[poly_factor_alt, poly_cmult_lzero, poly_sub_rzero, poly_one_poly] >>
      rw[poly_factor_divides_X],
      `1 < deg z` by decide_tac >>
      rw[poly_mod_less]
    ],
    Cases_on `deg z = 1` >| [
      `?c. c IN R /\ (z = factor c)` by rw[poly_monic_deg1_factor] >>
      `c <> #1` by metis_tac[poly_factor_alt, poly_cmult_lone, poly_one_poly, poly_unity_1] >>
      rw[poly_factor_divides_X, poly_one],
      `1 < deg z` by decide_tac >>
      rw[poly_mod_less, poly_one, poly_unity_1]
    ]
  ]) >>
  rw[poly_order_prime_condition]);

(* Theorem: prime k /\ mifactor z (unity k) /\ z <> unity 1 ==> INJ (\p. p % z) PM (Q z) *)
(* Proof:
   Since ipoly z ==> 0 < deg z          by poly_irreducible_deg_nonzero
         monic z ==> pmonic z
     and 0 < k                          by PRIME_POS
   Let u = unity k, and pmonic u        by poly_unity_pmonic
   Since (X ** k == |1|) (pm u)         by poly_unity_pmod_eqn, 0 < k
         (X ** k == |1|) (pm z)         by poly_mod_eq_divisor
     ==> forderz X = k                  by poly_X_order_prime_condition, z <> unity 1
   The result follows                   by reduceP_mod_modP_inj_1
*)
val reduceP_mod_modP_inj_2 = store_thm(
  "reduceP_mod_modP_inj_2",
  ``!(r:'a field) k s:num z. Field r /\
    prime k /\ mifactor z (unity k) /\ z <> unity 1 ==> INJ (\p. p % z) PM (Q z)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `0 < deg z` by rw[poly_irreducible_deg_nonzero] >>
  `pmonic z` by rw[] >>
  qabbrev_tac `u = unity k` >>
  `0 < k` by rw[PRIME_POS] >>
  `poly X /\ poly |1| /\ poly (X ** k) /\ pmonic u` by rw[poly_unity_pmonic, Abbr`u`] >>
  `(X ** k == |1|) (pm u)` by metis_tac[poly_unity_pmod_eqn] >>
  `(X ** k == |1|) (pm z)` by metis_tac[poly_mod_eq_divisor] >>
  `forderz X = k` by rw[poly_X_order_prime_condition] >>
  rw[reduceP_mod_modP_inj_1]);
(* for version 2 *)

(* Theorem: prime k /\ 0 < s /\ s < char r /\ mifactor z (unity k) /\ z <> unity 1 ==>
            2 ** (MIN s (CARD M)) <= CARD (Q z) *)
(* Proof:
   First, 1 < k  by ONE_LT_PRIME, hence 0 < k.
   Let n = MIN s (CARD M).

   Given the conditions,
      INJ (\p. p % z) PM (Q z)             by reduceP_mod_modP_inj_2
   Now, FINITE (Q z)                       by modP_finite
   Hence  FINITE PM                        by FINITE_INJ
     and  CARD PM <= CARD (Q z)            by INJ_CARD
     But  PPM n SUBSET PM                  by reduceP_poly_subset_reduceP, 0 < k, 0 < s, s < char r
     and  |0| IN PM                        by reduceP_has_zero
   Hence ( |0| INSERT PPM n) SUBSET PM     by INSERT_SUBSET
   So CARD ( |0| INSERT PPM n) <= CARD PM  by CARD_SUBSET
   Since |0| NOTIN PPM n                   by reduceP_poly_has_no_zero
     and FINITE (PPM n)                    by reduceP_poly_finite
     CARD ( |0| INSERT PPM n)
   = SUC (CARD (PPM n))                    by CARD_INSERT, since p NOTIN the set
   = SUC (PRE (2 ** n))                    by reduceP_poly_card
   = 2 ** n                                by SUC_PRE, with 0 < 2 ** n by ZERO_LT_EXP.
   Hence  2 ** n <= CARD (Q z)             by LESS_EQ_TRANS
*)
val modP_card_lower_2 = store_thm(
  "modP_card_lower_2",
  ``!(r:'a field) k s:num z. FiniteField r /\ prime k /\ 0 < s /\ s < char r /\
     mifactor z (unity k) /\ z <> unity 1 ==> 2 ** (MIN s (CARD M)) <= CARD (Q z)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `FiniteRing r` by rw[FiniteRing_def] >>
  `pmonic z` by metis_tac[poly_monic_irreducible_factor] >>
  `INJ (\p. p % z) PM (Q z)` by rw[reduceP_mod_modP_inj_2] >>
  `FINITE (Q z)` by rw[modP_finite] >>
  `FINITE PM` by rw[reduceP_finite] >>
  `CARD PM <= CARD (Q z)` by metis_tac[INJ_CARD] >>
  `1 < k` by rw[ONE_LT_PRIME] >>
  `|0| IN PM` by rw[reduceP_has_zero] >>
  qabbrev_tac `n = MIN s (CARD M)` >>
  `0 < k` by decide_tac >>
  `PPM n SUBSET PM` by rw[reduceP_poly_subset_reduceP, Abbr`n`] >>
  `( |0| INSERT PPM n) SUBSET PM` by rw[INSERT_SUBSET] >>
  `CARD ( |0| INSERT PPM n) <= CARD PM` by rw[CARD_SUBSET] >>
  `n <= s` by rw[Abbr`n`] >>
  `n < char r` by decide_tac >>
  `|0| NOTIN PPM n` by rw[reduceP_poly_has_no_zero] >>
  `FINITE (PPM n)` by rw[reduceP_poly_finite] >>
  `CARD ( |0| INSERT PPM n) = SUC (CARD (PPM n))` by metis_tac[CARD_INSERT] >>
  `_ = SUC (PRE (2 ** n))` by rw[reduceP_poly_card] >>
  `_ = 2 ** n` by metis_tac[SUC_PRE, ZERO_LT_EXP, DECIDE``0 < 2``] >>
  decide_tac);
(* for version 2 *)

(* ------------------------------------------------------------------------- *)
(* Upper Bound for (Q z) by Roots.                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: coprime k (CARD R) /\ 1 < ordz k (CARD R) /\
            char r divides n /\ n IN N /\ ~perfect_power n (char r) /\ mifactor z (unity k) ==>
            CARD (Q z) <= n ** SQRT (CARD M) *)
(* Proof:
   Let p = char r, q = n DIV p, t = CARD M.
   The goal is: CARD (Q z) <= n ** SQRT t

   Step 0: useful bits
   Note prime p           by finite_field_char
     so 1 < p and 0 < p   by ONE_LT_PRIME
    and n = p * q         by DIVIDES_EQN_COMM, 0 < p
   Note 1 < CARD R        by finite_field_card_gt_1
     so 1 < k             by ZN_order_with_coprime_1
   Note n <> p            by perfect_power_self, ~perfect_power n p
    and coprime n k       by setN_element, n IN N
     so n <> 0            by GCD_0, k <> 1
     or q <> 0            by MULT_EQ_0, 0 < n, 0 < p
    and q <> 1            by MULT_RIGHT_1, n <> p
    ==> 1 < q             by q <> 0, q <> 1
   Note p IN N /\ q IN N  by setN_has_char_and_cofactor

   Let u = NM p q (SQRT t).
   Step 1: A collision with m1 IN u, m2 IN u, m1 <> m2, but m1 MOD k = m2 MOD k.
   Note ~perfect_power q p             by perfect_power_cofactor, 0 < p, ~perfect_power n p
    ==> CARD u = (SUC (SQRT t)) ** 2   by reduceN_card, ADD1, 0 < k, prime p, 1 < q, ~perfect_power q p
    Now FINITE M                       by modN_finite, 0 < k
     so t < (SUC (SQRT t)) ** 2        by SQRT_PROPERTY
     or t < CARD u                     by above
    ==> ~INJ (\m. m MOD k) u M         by PHP
    By INJ_DEF, such a collision exists if m IN u ==> m MOD k IN M.
    But m IN u ==> m IN N              by reduceN_element_in_setN
               ==> m MOD k IN M        by setN_element_mod

   Let f = PolyModRing r z, d = lift (X ** m1 - X ** m2).
   Step 2: properties of quotient field and special polynomial z.
   Note Field f                        by poly_mod_irreducible_field
    and poly (X ** m1 - X ** m2)       by poly_sub_poly
    and 0 < deg h                      by poly_irreducible_deg_nonzero, ipoly h
    ==> Poly f d                       by poly_mod_lift_poly, 0 < deg h
   Also X ** m1 <> X ** m2             by poly_X_exp_eq, m1 <> m2
   thus X ** m1 - X ** m2 <> |0|       by poly_sub_eq_zero
    ==> d <> poly_zero f               by poly_mod_lift_eq_zero

   Step 3: CARD (Q z) <= Deg f d
   Note m1 IN N /\ m2 IN N             by reduceN_element_in_setN, 0 < k, p IN N, q IN N
    ==> Q z SUBSET poly_roots f d      by setN_mod_eq_gives_modP_roots_2
   Also FINITE (poly_roots f d)        by poly_roots_finite, Poly f d, d <> poly_zero f
   Thus CARD (Q z)
     <= CARD (poly_roots f d)          by CARD_SUBSET
     <= Deg f d                        by poly_roots_count

   Step 4: Deg f d <= n ** SQRT t
   Note Deg f d
      = deg (X ** m1 - X ** m2)        by poly_mod_lift_deg
     <= MAX (deg (X ** m1)) (deg (X ** m2))  by poly_deg_sub
      = MAX m1 m2                      by poly_deg_X_exp
    Now m1 <= n ** SQRT t              by reduceN_element_upper_better
    and m2 <= n ** SQRT t              by reduceN_element_upper_better
   Thus MAX m1 m2 <= n ** SQRT t       by MAX_LE

  Therefore, CARD (Q z) <= n ** SQRT t by [3], [4]
*)
val modP_card_upper_better = store_thm(
  "modP_card_upper_better",
  ``!r:'a field k n s:num z. FiniteField r /\ coprime k (CARD R) /\ 1 < ordz k (CARD R) /\
         char r divides n /\ n IN N /\ ~perfect_power n (char r) /\ mifactor z (unity k) ==>
         CARD (Q z) <= n ** SQRT (CARD M)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `p = char r` >>
  qabbrev_tac `q = n DIV p` >>
  qabbrev_tac `t = CARD M` >>
  `prime p` by rw[finite_field_char, Abbr`p`] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `0 < p` by decide_tac >>
  `n = p * q` by metis_tac[DIVIDES_EQN_COMM] >>
  `1 < k` by metis_tac[ZN_order_with_coprime_1, finite_field_card_gt_1] >>
  `0 < k` by decide_tac >>
  `1 < q` by
  (`n <> p` by metis_tac[perfect_power_self] >>
  `n <> 0` by metis_tac[GCD_0, setN_element, DECIDE``1 < k ==> k <> 1``] >>
  `q <> 0` by metis_tac[MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
  `q <> 1` by metis_tac[MULT_RIGHT_1] >>
  decide_tac) >>
  `p IN N /\ q IN N` by metis_tac[setN_has_char_and_cofactor] >>
  qabbrev_tac `u = NM p q (SQRT t)` >>
  `?m1 m2. m1 IN u /\ m2 IN u /\ m1 <> m2 /\ (m1 MOD k = m2 MOD k)` by
    (`~perfect_power q p` by metis_tac[perfect_power_cofactor] >>
  `CARD u = (SUC (SQRT t)) ** 2` by metis_tac[reduceN_card, ADD1] >>
  `FINITE M` by rw[modN_finite] >>
  `t < (SUC (SQRT t)) ** 2` by rw[SQRT_PROPERTY] >>
  `t < CARD u` by decide_tac >>
  `~INJ (\m. m MOD k) u M` by metis_tac[PHP] >>
  fs[INJ_DEF] >-
  metis_tac[reduceN_element_in_setN, setN_element_mod] >>
  metis_tac[]
  ) >>
  qabbrev_tac `f = PolyModRing r z` >>
  qabbrev_tac `d = lift (X ** m1 - X ** m2)` >>
  `Field f` by rw[poly_mod_irreducible_field, Abbr`f`] >>
  `Poly f d` by
      (`poly (X ** m1 - X ** m2)` by rw[] >>
  `0 < deg z` by rw[poly_irreducible_deg_nonzero] >>
  rw[poly_mod_lift_poly, Abbr`f`, Abbr`d`]) >>
  `d <> poly_zero f` by
        (`X ** m1 <> X ** m2` by rw[poly_X_exp_eq] >>
  `X ** m1 - X ** m2 <> |0|` by rw[poly_sub_eq_zero] >>
  rw[poly_mod_lift_eq_zero, Abbr`f`, Abbr`d`]) >>
  `CARD (Q z) <= Deg f d` by
          (`m1 IN N /\ m2 IN N` by metis_tac[reduceN_element_in_setN] >>
  `Q z SUBSET poly_roots f d` by rw[setN_mod_eq_gives_modP_roots_2, Abbr`f`, Abbr`d`] >>
  `FINITE (poly_roots f d)` by rw[poly_roots_finite] >>
  `CARD (Q z) <= CARD (poly_roots f d)` by rw[CARD_SUBSET] >>
  `CARD (poly_roots f d) <= Deg f d` by rw[poly_roots_count] >>
  decide_tac) >>
  `Deg f d <= n ** SQRT t` by
            (`Deg f d = deg (X ** m1 - X ** m2)` by metis_tac[poly_mod_lift_deg] >>
  `deg (X ** m1 - X ** m2) <= MAX (deg (X ** m1)) (deg (X ** m2))` by rw[poly_deg_sub] >>
  `MAX (deg (X ** m1)) (deg (X ** m2)) = MAX m1 m2` by rw[] >>
  `m1 <= n ** SQRT t /\ m2 <= n ** SQRT t` by rw[reduceN_element_upper_better] >>
  `MAX m1 m2 <= n ** SQRT t` by rw[] >>
  decide_tac) >>
  decide_tac);

(* This is the usual story in conventional proofs of the AKS theorem! *)

(*
This upper bound is also independent of the range s of polynomial checks.
Although M = N MOD k, and N is the introspective exponents valid for all the range s,
N consists only of 4 seeds: 1, p = char r, q = n DIV p, n, all valid for any range s.
And (CARD M <= phi k) by modN_card_upper_better.
*)

(* Theorem: coprime k (CARD R) /\ 1 < ordz k (CARD R) /\
            char r divides n /\ n IN N /\ ~perfect_power n (char r) /\ mifactor z (unity k) ==>
            CARD (Q z) <= 2 ** (SQRT (CARD M) * ulog n) *)
(* Proof:
   Note 1 < CARD R             by finite_field_card_gt_1
     so 1 < k                  by ZN_order_with_coprime_1
   Note coprime n k            by setN_element
   Thus n <> 0                 by GCD_0, k <> 1

   Let t = CARD M.
       CARD (Q z)
    <= n ** SQRT t                    by modP_card_upper_better
    <= (2 ** ulog n) ** SQRT t        by ulog_property, 0 < n
     = 2 ** (ulog n * SQRT t)         by EXP_EXP_MULT
     = 2 ** (SQRT t * ulog n)         by arithmetic
*)
val modP_card_upper_better_1 = store_thm(
  "modP_card_upper_better_1",
  ``!r:'a field k n s:num z. FiniteField r /\ coprime k (CARD R) /\ 1 < ordz k (CARD R) /\
         char r divides n /\ n IN N /\ ~perfect_power n (char r) /\ mifactor z (unity k) ==>
         CARD (Q z) <= 2 ** (SQRT (CARD M) * ulog n)``,
  rpt strip_tac >>
  `1 < k` by metis_tac[ZN_order_with_coprime_1, finite_field_card_gt_1] >>
  `n <> 0` by metis_tac[GCD_0, setN_element, LESS_NOT_EQ] >>
  qabbrev_tac `t = CARD M` >>
  `CARD (Q z) <= n ** SQRT t` by rw[modP_card_upper_better, Abbr`t`] >>
  `n ** SQRT t <= (2 ** ulog n) ** SQRT t` by rw[ulog_property] >>
  `(2 ** ulog n) ** SQRT t = 2 ** (ulog n * SQRT t)` by rw[EXP_EXP_MULT] >>
  `_ = 2 ** (SQRT t * ulog n)` by rw[] >>
  decide_tac);

(* Theorem: coprime k (CARD R) /\ 1 < ordz k (CARD R) /\
            char r divides n /\ n IN N /\ ~perfect_power n (char r) /\ mifactor z (unity k) ==>
            CARD (Q z) <= 2 ** (SQRT (phi k) * ulog n) *)
(* Proof:
   Note 1 < CARD R             by finite_field_card_gt_1
     so 1 < k                  by ZN_order_with_coprime_1

   Let t = CARD M.
       CARD (Q z)
    <= 2 ** (SQRT t * ulog n)         by modP_card_upper_better_1, 1 < k
    <= 2 ** (SQRT (phi k) * ulog n)   by modN_card_upper_better, EXP_BASE_LE_MONO
*)
val modP_card_upper_better_2 = store_thm(
  "modP_card_upper_better_2",
  ``!r:'a field k n s:num z. FiniteField r /\ coprime k (CARD R) /\ 1 < ordz k (CARD R) /\
         char r divides n /\ n IN N /\ ~perfect_power n (char r) /\ mifactor z (unity k) ==>
         CARD (Q z) <= 2 ** (SQRT (phi k) * ulog n)``,
  rpt strip_tac >>
  `1 < k` by metis_tac[ZN_order_with_coprime_1, finite_field_card_gt_1] >>
  qabbrev_tac `t = CARD M` >>
  `CARD (Q z) <= 2 ** (SQRT t * ulog n)` by rw[modP_card_upper_better_1, Abbr`t`] >>
  `SQRT t <= SQRT (phi k)` by rw[modN_card_upper_better, SQRT_LE, Abbr`t`] >>
  `2 ** (SQRT t * ulog n) <= 2 ** (SQRT (phi k) * ulog n)` by rw[] >>
  decide_tac);

(*
This clearly shows that the upper bound is independent of the range s of polynomial checks.
*)

(* ------------------------------------------------------------------------- *)
(* Better Lower Bound for (Q z).                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: mifactor z (unity k) /\ 1 < deg z /\
            (forderz X = k) /\ 1 < CARD M /\ 0 < s /\ s < char r ==> 2 ** (MIN s (CARD M)) < CARD (Q z) *)
(* Proof:
   First, 1 < k  by poly_X_order_gt_1.
   Let n = MIN s (CARD M).

   Given the conditions,
      INJ (\p. p % z) PM (Q z)        by reduceP_mod_modP_inj_0
   Now, FINITE (Q z)                  by modP_finite
   Hence  FINITE PM                   by FINITE_INJ
     and  CARD PM <= CARD (Q z)       by INJ_CARD
     But  PPM n SUBSET PM             by reduceP_poly_subset_reduceP, 0 < k, 0 < s, s < char
     and  |0| IN PM                   by reduceP_has_zero
     and  X IN PM                     by reduceP_has_X
   Hence X INSERT |0| INSERT PPM n SUBSET PM         by INSERT_SUBSET
   So CARD (X INSERT |0| INSERT PPM n) <= CARD PM    by CARD_SUBSET

   Since |0| NOTIN PPM n              by reduceP_poly_has_no_zero
     and   X NOTIN PPM n              by reduceP_poly_has_no_X
     and FINITE (PPM n)               by reduceP_poly_finite
     CARD (X INSERT |0| INSERT PPM n)
   = SUC (SUC (CARD (PPM n)))         by CARD_INSERT, since X, 0 NOTIN the set
   = SUC (SUC (PRE (2 ** n)))         by reduceP_poly_card
   = SUC (2 ** n)                     by SUC_PRE, with 0 < 2 ** n by ZERO_LT_EXP.
   Hence  SUC (2 ** n) <= CARD (Q z)  by LESS_EQ_TRANS
      or       2 ** n  <  CARD (Q z)  by LESS_SUC, x < SUC x
*)
val modP_card_lower_better = store_thm(
  "modP_card_lower_better",
  ``!(r:'a field) k s:num z. FiniteField r /\ mifactor z (unity k) /\ 1 < deg z /\
    (forderz X = k) /\ 1 < CARD M /\ 0 < s /\ s < char r ==> 2 ** (MIN s (CARD M)) < CARD (Q z)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `FiniteRing r` by rw[FiniteRing_def] >>
  `pmonic z` by metis_tac[poly_monic_irreducible_factor] >>
  `INJ (\p. p % z) PM (Q z)` by rw[reduceP_mod_modP_inj_0] >>
  `FINITE (Q z)` by rw[modP_finite] >>
  `FINITE PM` by metis_tac[FINITE_INJ] >>
  `CARD PM <= CARD (Q z)` by metis_tac[INJ_CARD] >>
  `1 < k` by rw[poly_X_order_gt_1] >>
  `|0| IN PM` by rw[reduceP_has_zero] >>
  `0 < k` by decide_tac >>
  `X IN PM` by rw[reduceP_has_X] >>
  qabbrev_tac `n = MIN s (CARD M)` >>
  `PPM n SUBSET PM` by rw[reduceP_poly_subset_reduceP, Abbr`n`] >>
  `(X INSERT |0| INSERT PPM n) SUBSET PM` by rw[INSERT_SUBSET] >>
  `CARD (X INSERT |0| INSERT PPM n) <= CARD PM` by rw[CARD_SUBSET] >>
  `n <= s` by rw[Abbr`n`] >>
  `n < char r` by decide_tac >>
  `|0| NOTIN PPM n` by rw[reduceP_poly_has_no_zero] >>
  `X NOTIN PPM n` by rw[reduceP_poly_has_no_X] >>
  `FINITE (PPM n)` by rw[reduceP_poly_finite] >>
  `CARD ( |0| INSERT PPM n) = SUC (CARD (PPM n))` by rw[CARD_INSERT] >>
  `CARD (X INSERT |0| INSERT PPM n) = SUC (SUC (CARD (PPM n)))` by rw[CARD_INSERT] >>
  `_ = SUC (SUC (PRE (2 ** n)))` by rw[reduceP_poly_card] >>
  `_ = SUC (2 ** n)` by metis_tac[SUC_PRE, ZERO_LT_EXP, DECIDE``0 < 2``] >>
  decide_tac);

(* Theorem: FiniteField r /\ coprime k (CARD R) /\ 1 < ordz k (CARD R) /\
         char r divides n /\ n IN N /\ ~perfect_power n (char r) /\ 0 < s /\ s < char r /\
         mifactor z (unity k) /\ 1 < deg z /\ (forderz X = k) /\
         1 < CARD M ==> 2 ** MIN s (CARD M) < CARD (Q z) /\ CARD (Q z) <= n ** SQRT (CARD M) *)
(* Proof:
   Note 1 < CARD R             by finite_field_card_gt_1
     so 1 < k                  by ZN_order_with_coprime_1
   The lower bound follows     by modP_card_lower_better, 1 < CARD M
   The upper bound follows     by modP_card_upper_better
*)
val modP_card_range = store_thm(
  "modP_card_range",
  ``!r:'a field k n s:num z. FiniteField r /\ coprime k (CARD R) /\ 1 < ordz k (CARD R) /\
         char r divides n /\ n IN N /\ ~perfect_power n (char r) /\ 0 < s /\ s < char r /\
         mifactor z (unity k) /\ 1 < deg z /\ (forderz X = k) /\
         1 < CARD M ==> 2 ** MIN s (CARD M) < CARD (Q z) /\ CARD (Q z) <= n ** SQRT (CARD M)``,
  ntac 6 strip_tac >>
  `1 < k` by metis_tac[ZN_order_with_coprime_1, finite_field_card_gt_1] >>
  rw[modP_card_lower_better, modP_card_upper_better]);

(* ------------------------------------------------------------------------- *)
(* Exponent bounds for (CARD M)                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r ==>
    !k n s. 1 < k /\ n IN N /\ 1 < k /\ n IN N /\ (ulog n) ** 2 <= ordz k n  ==>
            SQRT (CARD M) * ulog n <= MIN (SQRT (phi k) * ulog n) (CARD M) *)
(* Proof:
   Let t = CARD M
       h = ordz k n
       m = ulog n
       c = SQRT (phi k) * m
   and the goal: SQRT t * m <= MIN c

   Step 1: SQRT t * m <= c
          Note              t <= phi k          by modN_card_upper_better
            so         SQRT t <= SQRT (phi k)   by SQRT_LE
          ===>  c = SQRT (phi k) * m            by notation
                 >= SQRT t * m                  by arithmetic

   Step 2: SQRT t * m <= t
          Note            h <= t                by modN_card_lower, 1 < k, Ring r
           and            m <= SQRT h           by SQRT_LE, SQRT_OF_SQ, m ** 2 <= h
           ==> t >= (SQRT t) * (SQRT t)         by SQ_SQRT_LE
                 >= (SQRT t) * (SQRT h)         by SQRT_LE, h <= t
                 >= SQRT t * m                  by above

          Hence SQRT t * m <= MIN c t           by MIN_DEF
*)
val modN_card_with_ulog_le_min_1 = store_thm(
  "modN_card_with_ulog_le_min_1",
  ``!r:'a ring. Ring r ==>
   !k n s:num. 1 < k /\ n IN N /\ (ulog n) ** 2 <= ordz k n  ==>
               SQRT (CARD M) * ulog n <= MIN (SQRT (phi k) * ulog n) (CARD M)``,
  rpt strip_tac >>
  qabbrev_tac `t = CARD M` >>
  qabbrev_tac `h = ordz k n` >>
  qabbrev_tac `m = ulog n` >>
  qabbrev_tac `c = SQRT (phi k) * m` >>
  `SQRT t * m <= c` by
  (`t <= phi k` by rw[modN_card_upper_better, Abbr`t`] >>
  `SQRT t <= SQRT (phi k)` by rw[SQRT_LE] >>
  rw_tac arith_ss[Abbr`c`]) >>
  `SQRT t * m <= t` by
    (`h <= t` by rw[modN_card_lower, Abbr`h`, Abbr`t`] >>
  `SQRT h <= SQRT t` by rw[SQRT_LE] >>
  `(SQRT h) * (SQRT t) <= (SQRT t) * (SQRT t)` by rw_tac arith_ss[] >>
  `m <= SQRT h` by metis_tac[SQRT_LE, SQRT_OF_SQ] >>
  `m * SQRT t <= SQRT h * SQRT t` by rw_tac arith_ss[] >>
  `(SQRT t) * (SQRT t) <= t` by rw[SQ_SQRT_LE] >>
  decide_tac) >>
  metis_tac[MIN_DEF]);

(* Theorem: Ring r ==>
    !k n s. 1 < k /\ n IN N /\ (2 * ulog n) ** 2 <= ordz k n  ==>
            2 * SQRT (CARD M) * ulog n <= MIN (2 * SQRT (phi k) * ulog n) (CARD M) *)
(* Proof:
   Let t = CARD M
       h = ordz k n
       m = ulog n
       c = 2 * SQRT (phi k) * m
   and the goal:  2 * SQRT t * m <= MIN c

   Step 1: 2 * SQRT t * m <= c
          Note              t <= phi k             by modN_card_upper_better
            so         SQRT t <= SQRT (phi k)      by SQRT_LE
          ===>  c = 2 * SQRT (phi k) * m           by notation
                 >= 2 * SQRT t * m                 by arithmetic

   Step 2: 2 * SQRT t * m <= t
          Note            h <= t                   by modN_card_lower, 1 < k, Ring r
           and        2 * m <= SQRT h              by SQRT_LE, SQRT_OF_SQ, (2 * m) ** 2 <= h
           ==> t >= (SQRT t) * (SQRT t)            by SQ_SQRT_LE
                 >= (SQRT h) * (SQRT t)            by SQRT_LE, h <= t
                 >= 2 * m * SQRT t                 by above
                  = 2 * SQRT t * m

          Hence 2 * SQRT t * m <= MIN c t          by MIN_DEF
*)
val modN_card_with_ulog_le_min_2 = store_thm(
  "modN_card_with_ulog_le_min_2",
  ``!r:'a ring. Ring r ==>
   !k n s:num. 1 < k /\ n IN N /\ (2 * ulog n) ** 2 <= ordz k n  ==>
               2 * SQRT (CARD M) * ulog n <= MIN (2 * SQRT (phi k) * ulog n) (CARD M)``,
  rpt strip_tac >>
  qabbrev_tac `t = CARD M` >>
  qabbrev_tac `h = ordz k n` >>
  qabbrev_tac `m = ulog n` >>
  qabbrev_tac `c = 2 * SQRT (phi k) * m` >>
  `2 * SQRT t * m <= c` by
  (`t <= phi k` by rw[modN_card_upper_better, Abbr`t`] >>
  `SQRT t <= SQRT (phi k)` by rw[SQRT_LE] >>
  rw_tac arith_ss[Abbr`c`]) >>
  `2 * SQRT t * m <= t` by
    (`h <= t` by rw[modN_card_lower, Abbr`h`, Abbr`t`] >>
  `SQRT h <= SQRT t` by rw[SQRT_LE] >>
  `(SQRT h) * (SQRT t) <= (SQRT t) * (SQRT t)` by rw_tac arith_ss[] >>
  `2 * m <= SQRT h` by metis_tac[SQRT_LE, SQRT_OF_SQ] >>
  `2 * m * SQRT t <= SQRT h * SQRT t` by rw_tac arith_ss[] >>
  `(SQRT t) * (SQRT t) <= t` by rw[SQ_SQRT_LE] >>
  decide_tac) >>
  metis_tac[MIN_DEF]);

(*
> reduceN_mod_modN_inj_1;
val it = |- !r k s z. Field r /\ mifactor z (unity k) ==>
          !p q. 1 < p /\ 1 < q /\ p IN N /\ q IN N /\
                MAX p q ** TWICE (SQRT (CARD M)) < CARD (Q z) ==>
                INJ (\m. m MOD k) (NM p q (SQRT (CARD M))) M: thm

> reduceP_mod_modP_inj_1;
val it = |- !r k s z. Field r /\ 0 < k /\ mifactor z (unity k) /\ (forderz X = k) ==>
                      INJ (\p. p % z) PM (Q z): thm

Since:
> modN_card_upper;
val it = |- !r k s. 1 < k ==> CARD M < k: thm
> modN_card_lower;
val it = |- !r k s. Ring r /\ #1 <> #0 /\ 1 < k ==>
            !n. n IN N ==> order (ZN k).prod n <= CARD M: thm
> modP_card_upper_max;
val it = |- !r k s z. FiniteField r /\ mifactor z (unity k) ==>
                      CARD (Q z) <= CARD R ** deg z: thm
> modP_card_lower_1;
val it = |- !r k s z. FiniteField r /\ mifactor z (unity k) /\ (forderz X = k) /\
                      1 < k /\ s < char r ==> 2 ** MIN s (CARD M) <= CARD (Q z): thm

The condition in reduceN_mod_modN_inj_1 can be satisfied if:
            MAX p q ** (2 * SQRT (CARD M)) < 2 ** MIN s (CARD M)

Later, will pick p = p IN N, and q = n IN N. Better: q = n DIV p IN N.
*)

(* ------------------------------------------------------------------------- *)
(* Less-than Bounds                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < k /\ 1 < n /\ n IN N /\ (2 * SUC (LOG2 n)) ** 2 <= ordz k n  ==>
            n ** (2 * SQRT (CARD M)) < 2 ** MIN (2 * (SQRT (phi k)) * SUC (LOG2 n)) (CARD M) *)
(* Proof:
   Let t = CARD M
       h = ordz k n
       m = SUC (LOG2 n)
       c = 2 * (SQRT (phi k)) * m
   and the goal:  n ** (2 * SQRT t) < 2 ** MIN c t
   Thus    c = 2 * SQRT k * m            by given
    and   (2 * m) ** 2 <= h              by given
                       <= t <= phi k     by modN_card_lower, modN_card_upper_better, 1 < k
   also     n < 2 ** m                   by LOG, this is critical.

   Taking square roots,
        SQRT h <= SQRT t <= SQRT (phi k) by SQRT_LE
     SQRT ((2 * m) ** 2) <= SQRT h       by SQRT_LE
   or              2 * m <= SQRT h       by SQRT_OF_SQ

   First, show m * (2 * SQRT t) <= MIN c t
      Since c = 2 * SQRT (phi k) * m
              >= 2 * SQRT t * m          by SQRT t <= SQRT (phi k)
              = m * (2 * SQRT t)         by arithmetic
      Also  t >= (SQRT t) * (SQRT t)     by SQ_SQRT_LE
              >= (SQRT h) * (SQRT t)     by SQRT h <= SQRT t
              >= 2 * m * (SQRT t)        by 2 * m <= SQRT h
               = m * (2 * SQRT t)        by arithmetic
      Hence m * (2 * SQRT t) <= MIN c t  by MIN_DEF

   From   m * (2 * SQRT t) <= MIN c t
       2 ** (m * (2 * SQRT t)) <= 2 ** MIN c t        by EXP_BASE_LE_MONO
   or  (2 ** m) ** (2 * SQRT t) <= 2 ** MIN c t       by EXP_EXP_MULT
   Now     n < 2 ** m                                 by LOG (from above)
        n ** (2 * SQRT t) < (2 ** m) ** (2 * SQRT t)  by EXP_EXP_LT_MONO
   Overall,  n ** (2 * SQRT t) < 2 ** MIN c t
*)
val modN_card_in_exp_lt_bound_0 = store_thm(
  "modN_card_in_exp_lt_bound_0",
  ``!r:'a ring. Ring r ==>
   !k n s:num. 1 < k /\ 1 < n /\ n IN N /\ (2 * SUC (LOG2 n)) ** 2 <= ordz k n  ==>
             n ** (2 * SQRT (CARD M)) < 2 ** MIN (2 * (SQRT (phi k)) * SUC (LOG2 n)) (CARD M)``,
  rpt strip_tac >>
  qabbrev_tac `t = CARD M` >>
  qabbrev_tac `h = ordz k n` >>
  qabbrev_tac `m = SUC (LOG2 n)` >>
  qabbrev_tac `c = 2 * (SQRT (phi k)) * m` >>
  `h <= t` by rw[modN_card_lower, Abbr`h`, Abbr`t`] >>
  `t <= phi k` by rw[modN_card_upper_better, Abbr`t`] >>
  `0 < m` by rw[LESS_SUC, Abbr`m`] >>
  `m <> 0 /\ 0 < k /\ 0 < n` by decide_tac >>
  `2 * m <> 0 /\ (2 * m) ** 2 <> 0` by metis_tac[EXP_EQ_0, MULT_EQ_0, DECIDE``0 < 2 /\ 0 <> 2``] >>
  `0 < 2 * m /\ 0 < t` by decide_tac >>
  `2 * m <= SQRT h` by metis_tac[SQRT_LE, SQRT_OF_SQ] >>
  `SQRT t <= SQRT (phi k)` by rw[SQRT_LE] >>
  `SQRT h <= SQRT t` by rw[SQRT_LE] >>
  `m * (2 * SQRT t) <= c` by rw_tac arith_ss[Abbr`c`] >>
  `(SQRT t) * (SQRT t) <= t` by rw[SQ_SQRT_LE] >>
  `(SQRT h) * (SQRT t) <= (SQRT t) * (SQRT t)` by rw_tac arith_ss[] >>
  `m * 2 * (SQRT t) <= SQRT h * SQRT t` by rw_tac arith_ss[] >>
  `m * (2 * SQRT t) <= t` by decide_tac >>
  `m * (2 * SQRT t) <= MIN c t` by metis_tac[MIN_DEF] >>
  `2 ** (m * (2 * SQRT t)) <= 2 ** MIN c t` by rw[EXP_BASE_LE_MONO] >>
  `2 ** (m * (2 * SQRT t)) = (2 ** m) ** (2 * SQRT t)` by rw[EXP_EXP_MULT] >>
  `n < 2 ** m` by rw[LOG2_PROPERTY, Abbr`m`] >>
  `0 < 2 * SQRT t` by metis_tac[SQRT_EQ_0, MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
  `n ** (2 * SQRT t) < (2 ** m) ** (2 * SQRT t)` by rw[EXP_EXP_LT_MONO] >>
  decide_tac);

(* Theorem: 1 < k /\ 1 < n /\ n IN N /\ (SUC (LOG2 n)) ** 2 <= ordz k n ==>
            n ** (SQRT (CARD M)) < 2 ** MIN (SQRT (phi k) * SUC (LOG2 n)) (CARD M) *)
(* Proof:
   Let t = CARD M, h = ordz k n, m = SUC (LOG2 n), c = SQRT (phi k) * m.
   and the goal is: n ** SQRT t < 2 ** MIN s t

   The strategy is to prove in two steps:
   (1) show   n ** SQRT t < 2 ** (m * SQRT t)
   (2) show                 2 ** (m * SQRT t) <= 2 ** MIN c t

   Step 0: some useful bits, show h <= t and 0 < t
   Since m = LOG2 n + 1, 0 < m /\ m <> 0         by arithmetic
      so m ** 2 <> 0                             by EXP_2, MULT_EQ_0, m <> 0
    Note h <= t                                  by modN_card_lower, 1 < k, n IN N
      so 0 < n /\ 0 < t                          by 1 < n, 0 <> m ** 2 <= h (given), h <= t

   Step 1: show n ** SQRT t < 2 ** (m * SQRT t)       [1]
    Note 0 < SQRT t                              by SQRT_EQ_0, MULT_EQ_0, 0 < t
     and n < 2 ** m                              by LOG2_PROPERTY, ADD1, 0 < n
     ==> n ** SQRT t < (2 ** m) ** SQRT t        by EXP_EXP_LT_MONO, 0 < SQRT t
     and 2 ** (m * SQRT t) = (2 ** m) ** SQRT t  by EXP_EXP_MULT
    Thus n ** SQRT t < 2 ** (m * SQRT t)         by arithmetic

   Step 2: show 2 ** (m * SQRT t) <= 2 ** MIN s t     [2]
   Since base 2 is the same, we can just show:
         m * SQRT t <= MIN c t                   by EXP_BASE_LE_MONO
   Easy part: show m * SQRT t <= c
        Note      t <= phi k                     by modN_card_upper_better, 1 < k
         ==> SQRT t <= SQRT (phi k)              by SQRT_LE, t <= phi k
          or m * SQRT t <= c                     by c = SQRT (phi k) * m
   Hard part: show m * SQRT t <= t
        Since    m ** 2 <= h
         ==>          m <= SQRT h                by SQRT_LE, SQRT_OF_SQ
         or  m * SQRT t <= SQRT h * SQRT t       by arithmetic
        But      SQRT h <= SQRT t                by SQRT_LE, h <= t
         so SQRT h * SQRT t <= SQRT t * SQRT t   by SQRT h <= SQRT t
        and SQRT t * SQRT t <= t                 by SQ_SQRT_LE
        Overall, m * SQRT t <= t                 by combining above

    With m * SQRT t <= c /\ m * SQRT t <= t
     ==> m * SQRT t <= MIN c t                   by MIN_DEF

   Combining [1] and [2], the result follows.
*)
val modN_card_in_exp_lt_bound_1 = store_thm(
  "modN_card_in_exp_lt_bound_1",
  ``!r:'a ring. Ring r ==>
   !k n s:num. 1 < k /\ 1 < n /\ n IN N /\ (SUC (LOG2 n)) ** 2 <= ordz k n ==>
         n ** (SQRT (CARD M)) < 2 ** MIN (SQRT (phi k) * SUC (LOG2 n)) (CARD M)``,
  rpt strip_tac >>
  qabbrev_tac `t = CARD M` >>
  qabbrev_tac `m = SUC (LOG2 n)` >>
  qabbrev_tac `h = ordz k n` >>
  qabbrev_tac `c = SQRT (phi k) * m` >>
  `h <= t` by rw[modN_card_lower, Abbr`h`, Abbr`t`] >>
  `0 < m /\ m <> 0` by rw[LESS_SUC, Abbr`m`] >>
  `m ** 2 <> 0` by metis_tac[EXP_2, MULT_EQ_0] >>
  `0 < n /\ 0 < t` by decide_tac >>
  `n ** SQRT t < 2 ** (m * SQRT t)` by
  (`0 < SQRT t` by metis_tac[SQRT_EQ_0, MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
  `n < 2 ** m` by metis_tac[LOG2_PROPERTY, ADD1] >>
  `n ** SQRT t < (2 ** m) ** SQRT t` by rw[EXP_EXP_LT_MONO] >>
  `2 ** (m * SQRT t) = (2 ** m) ** SQRT t` by rw[EXP_EXP_MULT] >>
  decide_tac) >>
  `2 ** (m * SQRT t) <= 2 ** MIN c t` by
    (`m * SQRT t <= MIN c t` suffices_by rw[EXP_BASE_LE_MONO] >>
  `t <= phi k` by rw[modN_card_upper_better, Abbr`t`] >>
  `SQRT t <= SQRT (phi k)` by rw[SQRT_LE] >>
  `m * SQRT t <= c` by rw_tac arith_ss[Abbr`c`] >>
  `m <= SQRT h` by metis_tac[SQRT_LE, SQRT_OF_SQ] >>
  `m * SQRT t <= SQRT h * SQRT t` by rw_tac arith_ss[] >>
  `SQRT h <= SQRT t` by rw[SQRT_LE] >>
  `SQRT h * SQRT t <= SQRT t * SQRT t` by rw_tac arith_ss[] >>
  `SQRT t * SQRT t <= t` by rw[SQ_SQRT_LE] >>
  `m * SQRT t <= t` by decide_tac >>
  metis_tac[MIN_DEF]) >>
  decide_tac);

(* Theorem: 1 < k /\ n IN N ==>
            !h. 0 < h /\ n < 2 ** h /\ h ** 2 <= ordz k n ==>
                n ** SQRT (CARD M) < 2 ** MIN (SQRT (phi k) * h) (CARD M) *)
(* Proof:
   Let t = CARD M, p = SQRT (phi k) * h, q = ordz k n
   Then the goal is: n ** SQRT t < 2 ** MIN p t

   The strategy is to prove in two steps:
   (1) show   n ** SQRT t < 2 ** (h * SQRT t)
   (2) show                 2 ** (h * SQRT t) <= 2 ** MIN p t

   Step 0: some useful bits, show q <= t and 0 < t
    Note q <= t                                  by modN_card_lower, 1 < k, n IN N
     and h <> 0                                  by 0 < h
      so h ** 2 <> 0                             by EXP_2, MULT_EQ_0, h <> 0
      so 0 < t                                   by 0 <> h ** 2 <= q (given), q <= t

   Step 1: show n ** SQRT t < 2 ** (h * SQRT t)       [1]
    Note 0 < SQRT t                              by SQRT_EQ_0, MULT_EQ_0, 0 < t
     and n < 2 ** h                              by given
     ==> n ** SQRT t < (2 ** h) ** SQRT t        by EXP_EXP_LT_MONO, 0 < SQRT t
     and             = 2 ** (h * SQRT t)         by EXP_EXP_MULT
    Thus n ** SQRT t < 2 ** (h * SQRT t)         by inequalities

   Step 2: show 2 ** (h * SQRT t) <= 2 ** MIN p t     [2]
   Since base 2 is the same, we can just show:
             h * SQRT t <= MIN p t               by EXP_BASE_LE_MONO
   Easy part: show h * SQRT t <= p
        Note          t <= phi k                 by modN_card_upper_better, 1 < k
         ==>     SQRT t <= SQRT (phi k)          by SQRT_LE, t <= phi k
          or h * SQRT t <= p                     by p = SQRT (phi k) * h
   Hard part: show h * SQRT t <= t
        Since    h ** 2 <= q                     by given
         ==>          h <= SQRT q                by SQRT_LE, SQRT_OF_SQ
        Note          q <= t                     by modN_card_lower, above
         ==>     SQRT q <= SQRT t                by SQRT_LE, q <= t

        Thus h * SQRT t <= SQRT q * SQRT t       by LESS_MONO_MULT
                        <= SQRT t * SQRT t       by LESS_MONO_MULT
                        <= t                     by SQ_SQRT_LE

    With both (h * SQRT t <= p) /\ (h * SQRT t <= t)
     ==> h * SQRT t <= MIN s t                   by MIN_DEF

   Combining [1] and [2], the result follows.
*)
val modN_card_in_exp_lt_bound_2 = store_thm(
  "modN_card_in_exp_lt_bound_2",
  ``!r:'a ring. Ring r ==> !k n s:num. 1 < k /\ n IN N ==>
   !h. 0 < h /\ n < 2 ** h /\ h ** 2 <= ordz k n ==>
       n ** SQRT (CARD M) < 2 ** MIN (SQRT (phi k) * h) (CARD M)``,
  rpt strip_tac >>
  qabbrev_tac `t = CARD M` >>
  qabbrev_tac `p = SQRT (phi k) * h` >>
  qabbrev_tac `q = ordz k n` >>
  `q <= t` by rw[modN_card_lower, Abbr`q`, Abbr`t`] >>
  `h <> 0` by decide_tac >>
  `h ** 2 <> 0` by metis_tac[EXP_2, MULT_EQ_0] >>
  `0 < t` by decide_tac >>
  `n ** SQRT t < 2 ** (h * SQRT t)` by
  (`0 < SQRT t` by metis_tac[SQRT_EQ_0, MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
  `n ** SQRT t < (2 ** h) ** SQRT t` by rw[EXP_EXP_LT_MONO] >>
  `(2 ** h) ** SQRT t = 2 ** (h * SQRT t)` by rw[EXP_EXP_MULT] >>
  decide_tac) >>
  `2 ** (h * SQRT t) <= 2 ** MIN p t` by
    (`h * SQRT t <= MIN p t` suffices_by rw[EXP_BASE_LE_MONO] >>
  `t <= phi k` by rw[modN_card_upper_better, Abbr`t`] >>
  `SQRT t <= SQRT (phi k)` by rw[SQRT_LE] >>
  `h * SQRT t <= p` by rw_tac arith_ss[Abbr`p`] >>
  `h <= SQRT q` by metis_tac[SQRT_LE, SQRT_OF_SQ] >>
  `h * SQRT t <= SQRT q * SQRT t` by rw_tac arith_ss[] >>
  `SQRT q <= SQRT t` by rw[SQRT_LE] >>
  `SQRT q * SQRT t <= SQRT t * SQRT t` by rw_tac arith_ss[] >>
  `SQRT t * SQRT t <= t` by rw[SQ_SQRT_LE] >>
  `h * SQRT t <= t` by decide_tac >>
  metis_tac[MIN_DEF]) >>
  decide_tac);

(* Theorem: 1 < k /\ 1 < n /\ ~(perfect_power n 2) /\ n IN N /\ (ulog n) ** 2 <= ordz k n ==>
            n ** SQRT (CARD M) < 2 ** MIN (SQRT (phi k) * (ulog n)) (CARD M) *)
(* Proof:
   Note 0 < ulog n            by ulog_pos, 1 < n
    and n < 2 ** (ulog n)     by ulog_property_not_exact, ~(perfect_power 2 n)
   Let h = ulog n in modN_card_in_exp_lt_bound_2, the result follows.
*)
val modN_card_in_exp_lt_bound_3 = store_thm(
  "modN_card_in_exp_lt_bound_3",
  ``!r:'a ring. Ring r ==>
   !k n s:num. 1 < k /\ 1 < n /\ ~(perfect_power n 2) /\ n IN N /\ (ulog n) ** 2 <= ordz k n ==>
         n ** SQRT (CARD M) < 2 ** MIN (SQRT (phi k) * (ulog n)) (CARD M)``,
  rw[modN_card_in_exp_lt_bound_2, ulog_property_not_exact]);

(* Theorem: Ring r ==>
   !k n s. 1 < k /\ 1 < n /\ ~(perfect_power n 2) /\
           n IN N /\ (ulog n) ** 2 <= ordz k n /\
           (s = SQRT (phi k) * (ulog n)) ==>
           n ** SQRT (CARD M) < 2 ** MIN s (CARD M) *)
(* Proof: by modN_card_in_exp_lt_bound_3 *)
val modN_card_in_exp_lt_bound_3_alt = store_thm(
  "modN_card_in_exp_lt_bound_3_alt",
  ``!r:'a ring. Ring r ==>
   !n a k s. 1 < k /\ 1 < n /\ ~(perfect_power n 2) /\
          (a = (ulog n) ** 2) /\ (s = SQRT (phi k) * (ulog n)) /\
           a <= ordz k n /\ n IN N ==>
           n ** SQRT (CARD M) < 2 ** MIN s (CARD M)``,
  rw[modN_card_in_exp_lt_bound_3]);

(* Theorem: Ring r ==>
   !k n s. 1 < k /\ 1 < n /\ ~perfect_power n 2 /\ n IN N /\
        (2 * ulog n) ** 2 <= ordz k n ==>
        n ** (2 * SQRT (CARD M)) < 2 ** MIN (2 * SQRT (phi k) * ulog n) (CARD M) *)
(* Proof:
   Let t = CARD M
       h = ordz k n
       m = ulog n
       c = 2 * SQRT (phi k) * m
   and the goal:  n ** (2 * SQRT t) < 2 ** MIN c t

   This is proved by two parts:
   (1) n ** (2 * SQRT t) < (2 ** m) ** (2 * SQRT t)
   (2) (2 ** m) ** (2 * SQRT t) <= 2 ** MIN c t

   Claim: n ** (2 * SQRT t) < (2 ** m) ** (2 * SQRT t)
   Proof: Note ~perfect_power n 2                            by given
           ==>                 n < 2 ** m                    by ulog_property_not_exact
          Thus n ** (2 * SQRT t) < (2 ** m) ** (2 * SQRT t)  by EXP_EXP_LT_MONO, (1)

   Claim: (2 ** m) ** (2 * SQRT t) <= 2 ** MIN c t
   Proof: Note         2 * (SQRT t) * m <= MIN c t           by modN_card_with_ulog_le_min_2
            so  2 ** (2 * (SQRT t) * m) <= 2 ** MIN c t      by EXP_BASE_LE_MONO
            or (2 ** m) ** (2 * SQRT t) <= 2 ** MIN c t      by EXP_EXP_MULT, (2)

   Overall,  n ** (2 * SQRT t) < 2 ** MIN c t                by (1), (2)
*)
val modN_card_in_exp_lt_bound_4 = store_thm(
  "modN_card_in_exp_lt_bound_4",
  ``!(r:'a ring). Ring r ==>
   !k n s:num. 1 < k /\ 1 < n /\ ~perfect_power n 2 /\ n IN N /\
        (2 * ulog n) ** 2 <= ordz k n ==>
        n ** (2 * SQRT (CARD M)) < 2 ** MIN (2 * SQRT (phi k) * ulog n) (CARD M)``,
  rpt strip_tac >>
  qabbrev_tac `t = CARD M` >>
  qabbrev_tac `h = ordz k n` >>
  qabbrev_tac `m = ulog n` >>
  qabbrev_tac `c = 2 * SQRT (phi k) * m` >>
  `n ** (2 * SQRT t) < (2 ** m) ** (2 * SQRT t)` by
  (`n < 2 ** m` by rw[ulog_property_not_exact, Abbr`m`] >>
  `0 < m` by rw[ulog_pos, MULT_POS, Abbr`m`] >>
  `(2 * m) ** 2 <> 0` by rw[] >>
  `h <= t` by rw[modN_card_lower, Abbr`h`, Abbr`t`] >>
  `0 < t` by decide_tac >>
  `0 < SQRT t` by metis_tac[SQRT_EQ_0, MULT_EQ_0, NOT_ZERO] >>
  rw[EXP_EXP_LT_MONO]) >>
  `2 * (SQRT t) * m <= MIN c t` by rw[modN_card_with_ulog_le_min_2, Abbr`t`, Abbr`h`, Abbr`m`, Abbr`c`] >>
  `2 ** (2 * (SQRT t) * m) <= 2 ** MIN c t` by rw[EXP_BASE_LE_MONO] >>
  `2 ** (2 * (SQRT t) * m) = 2 ** (m * (2 * SQRT t))` by decide_tac >>
  `_ = (2 ** m) ** (2 * SQRT t)` by rw[EXP_EXP_MULT] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Less-than-or-equal Bounds                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r ==>
   !k n s. 1 < k /\ 1 < n /\ n IN N /\ (2 * ulog n) ** 2 <= ordz k n  ==>
        n ** (2 * SQRT (CARD M)) <= 2 ** MIN (2 * SQRT (phi k) * ulog n) (CARD M) *)
(* Proof:
   Let t = CARD M
       h = ordz k n
       m = ulog n
       c = 2 * SQRT (phi k) * m
   and the goal:  n ** (2 * SQRT t) <= 2 ** MIN c t

   This is proved by two parts:
   (1) n ** (2 * SQRT t) <= (2 ** m) ** (2 * SQRT t)
   (2) (2 ** m) ** (2 * SQRT t) <= 2 ** MIN c t

   Claim: n ** (2 * SQRT t) <= (2 ** m) ** (2 * SQRT t)
   Proof: Note                 n <= 2 ** m                    by ulog_property
          Thus n ** (2 * SQRT t) <= (2 ** m) ** (2 * SQRT t)  by EXP_EXP_LE_MONO, (1)

   Claim: (2 ** m) ** (2 * SQRT t) <= 2 ** MIN c t
   Proof: Note         2 * (SQRT t) * m <= MIN c t            by modN_card_with_ulog_le_min_2
            so  2 ** (2 * (SQRT t) * m) <= 2 ** MIN c t       by EXP_BASE_LE_MONO
            or (2 ** m) ** (2 * SQRT t) <= 2 ** MIN c t       by EXP_EXP_MULT, (2)

   Overall,  n ** (2 * SQRT t) <= 2 ** MIN c t                by (1), (2)
*)
val modN_card_in_exp_le_bound_0 = store_thm(
  "modN_card_in_exp_le_bound_0",
  ``!r:'a ring. Ring r ==>
   !k n s:num. 1 < k /\ 1 < n /\ n IN N /\ (2 * ulog n) ** 2 <= ordz k n  ==>
        n ** (2 * SQRT (CARD M)) <= 2 ** MIN (2 * SQRT (phi k) * ulog n) (CARD M)``,
  rpt strip_tac >>
  qabbrev_tac `t = CARD M` >>
  qabbrev_tac `h = ordz k n` >>
  qabbrev_tac `m = ulog n` >>
  qabbrev_tac `c = 2 * SQRT (phi k) * m` >>
  `n ** (2 * SQRT t) <= (2 ** m) ** (2 * SQRT t)` by
  (`n <= 2 ** m` by rw[ulog_property, Abbr`m`] >>
  rw[EXP_EXP_LE_MONO]) >>
  `2 * (SQRT t) * m <= MIN c t` by rw[modN_card_with_ulog_le_min_2, Abbr`t`, Abbr`h`, Abbr`m`, Abbr`c`] >>
  `2 ** (2 * (SQRT t) * m) <= 2 ** MIN c t` by rw[EXP_BASE_LE_MONO] >>
  `2 ** (2 * (SQRT t) * m) = 2 ** (m * (2 * SQRT t))` by decide_tac >>
  `_ = (2 ** m) ** (2 * SQRT t)` by rw[EXP_EXP_MULT] >>
  decide_tac);

(* Theorem: 1 < k /\ n IN N ==> !h. 0 < h /\ n <= 2 ** h /\ h ** 2 <= ordz k n ==>
            n ** SQRT (CARD M) <= 2 ** MIN (SQRT (phi k) * h) (CARD M) *)
(* Proof:
   Let t = CARD M, p = SQRT (phi k) * h, q = ordz k n
   Then the goal is: n ** SQRT t < 2 ** MIN p t

   The strategy is to prove in two steps:
   (1) show   n ** SQRT t < 2 ** (h * SQRT t)
   (2) show                 2 ** (h * SQRT t) <= 2 ** MIN p t

   Step 0: some useful bits, show q <= t and 0 < t
    Note q <= t                                  by modN_card_lower, 1 < k, n IN N
     and h <> 0                                  by 0 < h
      so h ** 2 <> 0                             by EXP_2, MULT_EQ_0, h <> 0
      so 0 < t                                   by 0 <> h ** 2 <= q (given), q <= t

   Step 1: show n ** SQRT t < 2 ** (h * SQRT t)       [1]
    Note SQRT t <> 0                             by SQRT_EQ_0, MULT_EQ_0, 0 < t
     and n <= 2 ** h                             by given
     ==> n ** SQRT t <= (2 ** h) ** SQRT t       by EXP_EXP_LE_MONO, SQRT t <> 0
     and             = 2 ** (h * SQRT t)         by EXP_EXP_MULT
    Thus n ** SQRT t <= 2 ** (h * SQRT t)        by inequalities

   Step 2: show 2 ** (h * SQRT t) <= 2 ** MIN p t     [2]
   Since base 2 is the same, we can just show:
             h * SQRT t <= MIN p t               by EXP_BASE_LE_MONO
   Easy part: show h * SQRT t <= p
        Note          t <= phi k                 by modN_card_upper_better, 1 < k
         ==>     SQRT t <= SQRT (phi k)          by SQRT_LE, t <= phi k
          or h * SQRT t <= p                     by p = SQRT (phi k) * h
   Hard part: show h * SQRT t <= t
        Since    h ** 2 <= q                     by given
         ==>          h <= SQRT q                by SQRT_LE, SQRT_OF_SQ
        Note          q <= t                     by modN_card_lower, above
         ==>     SQRT q <= SQRT t                by SQRT_LE, q <= t

        Thus h * SQRT t <= SQRT q * SQRT t       by LESS_MONO_MULT
                        <= SQRT t * SQRT t       by LESS_MONO_MULT
                        <= t                     by SQ_SQRT_LE

    With both (h * SQRT t <= p) /\ (h * SQRT t <= t)
     ==> h * SQRT t <= MIN s t                   by MIN_DEF

   Combining [1] and [2], the result follows.
*)
val modN_card_in_exp_le_bound_1 = store_thm(
  "modN_card_in_exp_le_bound_1",
  ``!r:'a ring. Ring r ==> !k n s:num. 1 < k /\ n IN N ==>
   !h. 0 < h /\ n <= 2 ** h /\ h ** 2 <= ordz k n ==>
       n ** SQRT (CARD M) <= 2 ** MIN (SQRT (phi k) * h) (CARD M)``,
  rpt strip_tac >>
  qabbrev_tac `t = CARD M` >>
  qabbrev_tac `p = SQRT (phi k) * h` >>
  qabbrev_tac `q = ordz k n` >>
  `q <= t` by rw[modN_card_lower, Abbr`q`, Abbr`t`] >>
  `h <> 0` by decide_tac >>
  `h ** 2 <> 0` by metis_tac[EXP_2, MULT_EQ_0] >>
  `t <> 0` by decide_tac >>
  `n ** SQRT t <= 2 ** (h * SQRT t)` by
  (`SQRT t <> 0` by metis_tac[SQRT_EQ_0, MULT_EQ_0] >>
  `n ** SQRT t <= (2 ** h) ** SQRT t` by rw[EXP_EXP_LE_MONO] >>
  `(2 ** h) ** SQRT t = 2 ** (h * SQRT t)` by rw[EXP_EXP_MULT] >>
  decide_tac) >>
  `2 ** (h * SQRT t) <= 2 ** MIN p t` by
    (`h * SQRT t <= MIN p t` suffices_by rw[EXP_BASE_LE_MONO] >>
  `t <= phi k` by rw[modN_card_upper_better, Abbr`t`] >>
  `SQRT t <= SQRT (phi k)` by rw[SQRT_LE] >>
  `h * SQRT t <= p` by rw_tac arith_ss[Abbr`p`] >>
  `h <= SQRT q` by metis_tac[SQRT_LE, SQRT_OF_SQ] >>
  `h * SQRT t <= SQRT q * SQRT t` by rw_tac arith_ss[] >>
  `SQRT q <= SQRT t` by rw[SQRT_LE] >>
  `SQRT q * SQRT t <= SQRT t * SQRT t` by rw_tac arith_ss[] >>
  `SQRT t * SQRT t <= t` by rw[SQ_SQRT_LE] >>
  `h * SQRT t <= t` by decide_tac >>
  metis_tac[MIN_DEF]) >>
  decide_tac);

(* Theorem: 1 < k /\ 1 < n /\ n IN N /\ (ulog n) ** 2 <= ordz k n ==>
            n ** SQRT (CARD M) <= 2 ** MIN (SQRT (phi k) * (ulog n)) (CARD M) *)
(* Proof:
   Note 0 < ulog n            by ulog_pos, 1 < n
    and n <= 2 ** (ulog n)    by ulog_property, 0 < n
   Let h = ulog n in modN_card_in_exp_le_bound_1, the result follows.
*)
val modN_card_in_exp_le_bound_2 = store_thm(
  "modN_card_in_exp_le_bound_2",
  ``!r:'a ring. Ring r ==>
   !k n s:num. 1 < k /\ 1 < n /\ n IN N /\ (ulog n) ** 2 <= ordz k n ==>
         n ** SQRT (CARD M) <= 2 ** MIN (SQRT (phi k) * (ulog n)) (CARD M)``,
  rw[modN_card_in_exp_le_bound_1, ulog_property]);

(* Theorem: coprime k (CARD R) /\ 1 < ordz k (CARD R) /\
         char r divides n /\ n IN N /\ ~perfect_power n (char r) /\ mifactor z (unity k) /\
         ulog n ** 2 <= ordz k n ==>
         CARD (Q z) <= 2 ** MIN (SQRT (phi k) * ulog n) (CARD M) *)
(* Proof:
   Note 1 < CARD R          by finite_field_card_gt_1
     so 1 < k               by ZN_order_with_coprime_1
   Also n <> 0              by setN_has_no_0, 1 < k
    and char r <> 1         by field_char_ne_1
     so n <> 1              by DIVIDES_ONE
    ==> 1 < n               by n <> 0, n <> 1
   Let u = SQRT (phi k) * ulog n, t = CARD M.
        CARD (Q z)
     <= n ** SQRT t         by modP_card_upper_better
     <= 2 ** MIN u t        by modN_card_in_exp_le_bound_2
  The result follows        by LESS_EQ_TRANS
*)
val modP_card_upper_better_3 = store_thm(
  "modP_card_upper_better_3",
  ``!r:'a field k n s:num z. FiniteField r /\ coprime k (CARD R) /\ 1 < ordz k (CARD R) /\
         char r divides n /\ n IN N /\ ~perfect_power n (char r) /\ mifactor z (unity k) /\
         ulog n ** 2 <= ordz k n ==>
         CARD (Q z) <= 2 ** MIN (SQRT (phi k) * ulog n) (CARD M)``,
  rpt (stripDup[FiniteField_def]) >>
  `1 < CARD R` by rw[finite_field_card_gt_1] >>
  `1 < k` by metis_tac[ZN_order_with_coprime_1] >>
  `1 < n` by
  (`n <> 0` by metis_tac[setN_has_no_0] >>
  `n <> 1` by metis_tac[DIVIDES_ONE, field_char_ne_1] >>
  decide_tac) >>
  qabbrev_tac `u = SQRT (phi k) * ulog n` >>
  qabbrev_tac `t = CARD M` >>
  `CARD (Q z) <= n ** SQRT t` by rw[modP_card_upper_better, Abbr`t`] >>
  `n ** SQRT t <= 2 ** MIN u t` by rw[modN_card_in_exp_le_bound_2, Abbr`u`, Abbr`t`] >>
  decide_tac);

(* Theorem: FiniteField r /\
         mifactor z (unity k) /\ 1 < deg z /\ (forderz X = k) /\ (* conditions on z *)
         1 < n /\ n IN N /\ (ulog n) ** 2 <= ordz k n /\ (* conditions on n *)
         (s = SQRT (phi k) * ulog n) /\ s < char r ==> n ** SQRT (CARD M) < CARD (Q z) *)
(* Proof:
   Note n <> 0 and n <> 1      by 1 < n
   Thus ulog n <> 0            by ulog_eq_0
   Also 1 < k                  by poly_X_order_gt_1, ipoly z
   Note (ulog n) ** 2 <> 0     by SQ_EQ_0, EXP_2
     so ordz k n <> 0          by (ulog n) ** 2 <= ordz k n

   Claim: ordz k n <> 1
   Proof: If n = 2,
             By contradiction, assue ordz k n = 1.
             Then k divides 2 ** 1 - 1     by ZN_order_divisibility, 0 < k
             Thus k = 1                    by DIVIDES_ONE
             which contradicts 1 < k.
          If n <> 2,
             Then ulog n <> 1              by ulog_eq_1
               so (ulog n) ** 2 <> 1       by SQ_EQ_1
               or ordz k n <> 1            by (ulog n) ** 2 <= ordz k n

   Therefore, 1 < ordz k n                 by ordz k n <> 0, ordz k n <> 1
   Note ordz k n <= CARD M                 by modN_card_lower
   Thus 1 < CARD M                         by 1 < ordz k n

   Claim: 0 < s
   Proof: Note k <> 0                      by 1 < k
           ==> phi k <> 0                  by phi_eq_0
           ==> SQRT (phi k) <> 0           by SQRT_EQ_0
          Thus s <> 0                      by s = SQRT (phi k) * ulog n), MULT_EQ_0
            or 0 < s

   Thus 2 ** MIN s (CARD M) < CARD (Q z)   by modP_card_lower_better
   Note n <= 2 ** ulog n                   by ulog_property
   Thus n ** SQRT (CARD M) <= 2 ** MIN s (CARD M)
                                           by modN_card_in_exp_le_bound_1
   The result follows.
*)
val modP_card_lower_better_3 = store_thm(
  "modP_card_lower_better_3",
  ``!r:'a field k n s z. FiniteField r /\
         mifactor z (unity k) /\ 1 < deg z /\ (forderz X = k) /\ (* conditions on z *)
         1 < n /\ n IN N /\ (ulog n) ** 2 <= ordz k n /\ (* conditions on n *)
         (s = SQRT (phi k) * ulog n) /\ s < char r ==> n ** SQRT (CARD M) < CARD (Q z)``,
  rpt (stripDup[FiniteField_def]) >>
  `ulog n <> 0` by metis_tac[ulog_eq_0, DECIDE``1n < n ==> ~(n = 0) /\ ~(n = 1)``] >>
  `0 < ulog n` by decide_tac >>
  `1 < k` by rw[poly_X_order_gt_1] >>
  `1 < ordz k n` by
  (`(ulog n) ** 2 <> 0` by metis_tac[SQ_EQ_0, EXP_2] >>
  `ordz k n <> 0` by decide_tac >>
  `ordz k n <> 1` by
    (Cases_on `n = 2` >| [
    spose_not_then strip_assume_tac >>
    `0 < k` by decide_tac >>
    `k divides 2 ** 1 - 1` by metis_tac[ZN_order_divisibility] >>
    fs[DIVIDES_ONE],
    `ulog n <> 1` by fs[ulog_eq_1] >>
    `(ulog n) ** 2 <> 1` by fs[SQ_EQ_1] >>
    decide_tac
  ]) >>
  decide_tac) >>
  `ordz k n <= CARD M` by rw[modN_card_lower] >>
  `1 < CARD M` by decide_tac >>
  `0 < s` by
    (`k <> 0` by decide_tac >>
  `phi k <> 0` by rw[phi_eq_0] >>
  `SQRT (phi k) <> 0` by metis_tac[SQRT_EQ_0] >>
  `s <> 0` by metis_tac[MULT_EQ_0] >>
  decide_tac) >>
  `2 ** MIN s (CARD M) < CARD (Q z)` by rw[modP_card_lower_better] >>
  `n <= 2 ** ulog n` by rw[ulog_property] >>
  `n ** SQRT (CARD M) <= 2 ** MIN s (CARD M)` by rw[modN_card_in_exp_le_bound_1] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
