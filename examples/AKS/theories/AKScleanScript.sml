(* ------------------------------------------------------------------------- *)
(* AKS Clean Presentation                                                    *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "AKSclean";

(* ------------------------------------------------------------------------- *)

open jcLib;

(* open dependent theories *)
open prim_recTheory pred_setTheory listTheory arithmeticTheory logrootTheory
     numberTheory combinatoricsTheory dividesTheory gcdTheory primeTheory;

(* Get dependent theories local *)
open AKSimprovedTheory;
open AKSrevisedTheory;
open AKStheoremTheory;
open AKSmapsTheory;
open AKSsetsTheory;
open AKSintroTheory;
open AKSshiftTheory;

open countAKSTheory; (* for aks0_eq_aks *)

open fieldInstancesTheory;
open ringInstancesTheory;
open groupInstancesTheory; (* for Estar_group *)
open monoidTheory; (* for Monoid_def *)
open subgroupTheory; (* for Subgroup_def *)
open groupOrderTheory; (* for Generated_subset_group *)

open polyRingModuloTheory; (* for poly_mod_ring_has_monomials *)
open polyFieldModuloTheory; (* for poly_mod_prod_group *)
open polyIrreducibleTheory; (* for poly_irreducible_poly *)

open computeBasicTheory;
open computeOrderTheory;
open computePolyTheory;
open computeRingTheory;
open computeParamTheory;
open computeAKSTheory;

val _ = temp_overload_on("SQ", ``\n. n * (n :num)``);
val _ = temp_overload_on("HALF", ``\n. n DIV 2``);
val _ = temp_overload_on("TWICE", ``\n. 2 * n``);

(* ------------------------------------------------------------------------- *)
(* AKS Clean Presentation Documentation                                      *)
(* ------------------------------------------------------------------------- *)
(* Datatype and Overloading:
*)
(* Definitions and Theorems (# are exported):

   Helpers:

   A modular proof of AKS Main Theorem:
   aks_criteria_def  |- !r n k. aks_criteria r n k <=>
                                0 < n /\ 0 < k /\ 1 < ordz k (char r) /\ char r divides n /\
                                k < char r /\ ulog n ** 2 <= ordz k n /\
                                poly_intro_range r k n (SQRT (phi k) * ulog n)
   aks_checks_def    |- !n k. aks_checks n k <=>
                              1 < k /\ (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                              ulog n ** 2 <= ordz k n /\
                              (k < n ==> poly_intro_checks n k (SQRT (phi k) * ulog n))
   aks_checks_alt    |- !n k. aks_checks n k <=>
                              1 < k /\ ulog n ** 2 <= ordz k n /\
                              (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                              (k < n ==> poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n))
   aks_checks_gives_aks_criteria
                     |- !n k. k < n /\ aks_checks n k ==>
                        ?p. prime p /\ aks_criteria (ZN p) n k
   aks_criteria_ZN   |- !p n k. 0 < p /\ aks_criteria (ZN p) n k ==>
                                0 < n /\ 0 < k /\ 1 < ordz k p /\ p divides n /\
                                k < p /\ ulog n ** 2 <= ordz k n /\
                                poly_intro_range (ZN p) k n (SQRT (phi k) * ulog n)
   aks_main_punch    |- !r. FiniteField r /\ (CARD R = char r) ==>
                        !n k. aks_criteria r n k ==> perfect_power n (char r)
   aks_main_punch_alt|- !r. FiniteField r /\ (CARD R = char r) ==>
                        !n k. 0 < n /\ 0 < k /\ 1 < ordz k (char r) /\ char r divides n /\
                              k < char r /\ ulog n ** 2 <= ordz k n /\
                              poly_intro_range r k n (SQRT (phi k) * ulog n) ==>
                              perfect_power n (char r)
   aks_main_punch_thm|- !r. FiniteField r /\ (CARD R = char r) ==>
                        !n a k s. 0 < n /\ 0 < k /\ 1 < ordz k (char r) /\ char r divides n /\
                                  k < char r /\ (a = ulog n ** 2) /\ (s = SQRT (phi k) * ulog n) /\
                                  a <= ordz k n /\ poly_intro_range r k n s ==>
                                  perfect_power n (char r)
   aks_main_punch_ZN |- !p n a k s. prime p /\ 0 < n /\ 0 < k /\ 1 < ordz k p /\ p divides n /\
                                    k < p /\ a = ulog n ** 2 /\ s = SQRT (phi k) * ulog n /\
                                    a <= ordz k n /\ poly_intro_range (ZN p) k n s ==>
                                    perfect_power n p
   aks_main_step     |- !n k. k < n /\ aks_checks n k ==> ?p. prime p /\ perfect_power n p
   aks_when_prime    |- !n. prime n ==> ?k. aks_checks n k
   aks_main_theorem_1|- !n. prime n ==> power_free n /\ ?k. aks_checks n k
   aks_main_theorem_2|- !n k. power_free n /\ aks_checks n k ==> prime n
   aks_main_theorem  |- !n. prime n <=> power_free n /\ ?k. aks_checks n k

   AKS algorithm based on parameter search:
   aks_def     |- !n. aks n <=> power_free n /\
                                case aks_param n of
                                  nice j => j = n
                                | good k => poly_intro_checks n k (SQRT (phi k) * ulog n)
                                | bad => F
   aks_eval    |- !n. aks n <=> power_free n /\
                                case aks_param n of
                                  nice j => j = n
                                | good k =>
                                    EVERY (\c. (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k)))
                                          [1 .. SQRT (phi k) * ulog n]
                                | bad => F
   aks_param_good_for_prime
               |- !n k. (aks_param n = good k) /\ power_free n ==>
                        (prime n <=> poly_intro_checks n k (SQRT (phi k) * ulog n))
   aks_param_good_gives_checks_eq_checks
               |- !n k. (aks_param n = good k) ==>
                        (poly_intro_checks n k (SQRT (phi k) * ulog n) <=>
                         1 < n /\ k < n /\ aks_checks n k)
   aks_param_good_intro_limit
               |- !n k. 1 < n /\ (aks_param n = good )k ==> SQRT (phi k) * ulog n <= k
   aks_param_good_intro_limit_alt
               |- !n k s. 1 < n /\ (aks_param n = good k) /\ (s = SQRT (phi k) * ulog n) ==>
                          s <= k
   aks_alt_if  |- !n. aks n ==> power_free n /\ ?k. aks_checks n k
   aks_alt     |- !n. aks n <=> power_free n /\ ?k. aks_checks n k
   aks_theorem |- !n. prime n <=> aks n
   aks_thm_1   |- !n. prime n ==> aks n
   aks_thm_2   |- !n. aks n ==> prime n
   aks_thm     |- !n. prime n <=> aks n
   aks_eqn     |- !n. prime n <=> power_free n /\
                                  case aks_param n of
                                    nice j => j = n
                                  | good k => poly_intro_checks n k (SQRT (phi k) * ulog n)
                                  | bad => F

   Introspective Computations in a Ring:
   unity_mod_intro_eqn      |- !r. Ring r /\ #1 <> #0 ==> !k n. 1 < k /\ 0 < n ==>
                               !c. unity_mod_intro r k n c <=> n intro X + |c|
   unity_mod_intro_range_alt|- !r. Ring r /\ #1 <> #0 ==> !k n. 1 < k /\ 0 < n ==>
                               !m. unity_mod_intro_range r k n m <=> poly_intro_range r k n m
   unity_mod_intro_range_eqn|- !n k. 1 < n /\ 1 < k ==>
                               !m. unity_mod_intro_range (ZN n) k n m <=> poly_intro_checks n k m

   Direct Computations using ZN Polynomials:
   ZN_unity_mod_intro_eqn |- !n k. 1 < n /\ 1 < k ==>
                             !c. unity_mod_intro (ZN n) k n c <=> poly_intro (ZN n) k n (x+ n c)
   ZN_unity_mod_intro_range_eqn
                          |- !n k. 1 < n /\ 1 < k ==>
                             !c. unity_mod_intro_range (ZN n) k n c <=> poly_intro_range (ZN n) k n c
   ZN_poly_intro_eqn      |- !n k. 1 < n /\ 1 < k ==>
                             !c. ZN_poly_intro n k c <=> poly_intro (ZN n) k n (x+ n c)
   ZN_poly_intro_thm      |- !n k. 1 < n /\ 1 < k ==>
                             !c. ZN_poly_intro n k c <=> (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k))
   ZN_poly_intro_range_eqn|- !n k. 1 < n /\ 1 < k ==>
                             !m. ZN_poly_intro_range n k m <=> poly_intro_checks n k m
   aks_param_good_for_prime_alt
                          |- !n k. (aks_param n = good k) /\ power_free n ==>
                                   (prime n <=> ZN_poly_intro_range n k (sqrt_compute (phi_compute k) * ulog n))
   poly_introM_value_alt  |- !n k c. 1 < n /\ 1 < k ==>
                                     (valueOf (poly_introM n k c) <=> poly_intro (ZN n) k n (x+ n c))
   poly_intro_rangeM_value_alt
                          |- !n k c. 1 < n /\ 1 < k ==>
                             (valueOf (poly_intro_rangeM n k c) <=> poly_intro_range (ZN n) k n c)

   AKS Algorithm:
   aks_compute_alt      |- !n. aks_compute n <=> aks n
   aks_compute_thm      |- !n. aks n <=> aks_compute n
   aks_compute_eqn      |- !n. prime n <=> aks_compute n

   AKS Algorithm (Direct Version):
   aks_algo_def      |- !n. aks_algo n <=> power_free_check n /\
                               case aks_param n of
                                nice j => j = n
                              | good k => ZN_poly_intro_range n k (sqrt_compute (phi_compute k) * ulog n)
                              | bad => F
   aks_algo_alt      |- !n. aks_algo n <=> aks n
   aks_algo_eqn      |- !n. prime n <=> aks_algo n

   Another Story:
   aks_ring_criteria_def
                     |- !r n k. aks_ring_criteria r n k <=>
                                0 < n /\ 1 < k /\ k < char r /\ ulog n ** 2 <= ordz k n /\
                                poly_intro_range r k n (SQRT (phi k) * ulog n)
   aks_field_criteria_def
                     |- !r n k. aks_field_criteria r n k <=>
                                0 < n /\ 0 < k /\ 1 < ordz k (char r) /\
                                char r divides n /\ k < char r /\ ulog n ** 2 <= ordz k n /\
                                poly_intro_range r k n (SQRT (phi k) * ulog n)
   aks_field_criteria_alt
                     |- !r n k. aks_field_criteria r n k <=> aks_criteria r n k
   aks_decide_def    |- !n. aks_decide n <=>
                            case aks_param n of
                              nice j => j = n
                            | good k => poly_intro_checks n k (SQRT (phi k) * ulog n)
                            | bad => F
   aks_decide_alt    |- !n. aks_decide n <=>
                            case aks_param n of
                              nice j => j = n
                            | good k => poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n)
                            | bad => F
   aks_by_decide     |- !n. aks n <=> power_free n /\ aks_decide n

   aks_param_good_gives_checks_eq_ring_criteria
                     |- !n k. (aks_param n = good k) ==>
                              (poly_intro_checks n k (SQRT (phi k) * ulog n) <=>
                              aks_ring_criteria (ZN n) n k)
   aks_decide_meets_ring_criteria
                     |- !n. aks_decide n <=>
                            case aks_param n of
                              nice j => j = n
                            | good k => aks_ring_criteria (ZN n) n k
                            | bad => F
   aks_decide_meets_checks
                     |- !n. aks_decide n <=>
                            case aks_param n of
                              nice j => j = n
                            | good k => 1 < n /\ k < n /\ aks_checks n k
                            | bad => F
   aks_param_good_with_checks_implies_criteria
                     |- !n k. (aks_param n = good k) /\
                              poly_intro_checks n k (SQRT (phi k) * ulog n) ==>
                          ?p. prime p /\ aks_criteria (ZN p) n k
   aks_decide_implies_criteria
                     |- !n. aks_decide n ==>
                            case aks_param n of
                              nice j => j = n
                            | good k => ?p. prime p /\ aks_criteria (ZN p) n k
                            | bad => F
   aks_decide_prime  |- !n. prime n ==> aks_decide n
   aks_thm_easy      |- !n. prime n ==> power_free n /\ aks_decide n
   aks_thm_hard      |- !n. power_free n /\ aks_decide n ==> prime n
   aks_thm_iff       |- !n. prime n <=> power_free n /\ aks_decide n
   aks_param_good_for_prime_check
                     |- !n k. power_free n /\ (aks_param n = good k) ==>
                             (prime n <=> poly_intro_checks n k (SQRT (phi k) * ulog n))
   aks_param_good_for_prime_range
                     |- !n k. power_free n /\ (aks_param n = good k) ==>
                              (prime n <=> poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n))
   aks_param_good_with_range_prime
                     |- !n k. power_free n /\ (aks_param n = good k) /\
                              poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n) ==> prime n
   aks_param_good_with_range_prime_alt
                     |- !n k s. power_free n /\ (aks_param n = good k) /\
                                (s = SQRT (phi k) * ulog n) /\ poly_intro_range (ZN n) k n s ==>
                                prime n
   aks_param_good_with_range_implies_criteria
                     |- !n k. (aks_param n = good k) /\
                              poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n) ==>
                          ?p. prime p /\ aks_criteria (ZN p) n k
   aks_param_good_poly_intro_range
                     |- !n k. (aks_param n = good k) ==>
                        !m. poly_intro_range (ZN n) k n m <=> poly_intro_checks n k m
   aks_by_poly_intro_range
                     |- !n. aks n <=> power_free n /\
                                 case aks_param n of
                                   nice j => (j = n)
                                 | good k => poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n)
                                 | bad => F

   Variations of AKS algorithm:
   aks_variation_thm |- !n limit. (!k. 0 < k /\ (ulog n) ** 2 <= ordz k n ==>
                                       SQRT (phi k) * ulog n <= limit k n) ==>
                                  (prime n <=> power_free n /\
                                               case aks_param n of
                                                 nice j => j = n
                                               | good k => poly_intro_checks n k (limit k n)
                                               | bad => F)
   aks_variation_1   |- !n. prime n <=> power_free n /\
                                        case aks_param n of
                                          nice j => j = n
                                        | good k => poly_intro_checks n k (SQRT k * ulog n)
                                        | bad => F
   aks_variation_2   |- !n. prime n <=> power_free n /\
                                        case aks_param n of
                                          nice j => j = n
                                        | good k => poly_intro_checks n k (k * ulog n)
                                        | bad => F
   aks_variation_3   |- !n. prime n <=> power_free n /\
                                        case aks_param n of
                                          nice j => j = n
                                        | good k => poly_intro_checks n k k
                                        | bad => F
   aks0_eqn          |- !n. aks0 n <=> power_free_test n /\
                                       case param n of
                                         nice j => j = n
                                       | good k => poly_intro_checks n k k
                                       | bad => F
   aks0_thm          |- !n. prime n <=> aks0 n
   aks0_eq_aks       |- !n. aks0 n <=> aks n
   aksM_value_alt    |- !n. valueOf (aksM n) <=> aks n
   aksM_thm_alt      |- !n. (valueOf (aksM n) <=> aks n) /\
                            stepsOf o aksM IN big_O (\n. ulog n ** 21)

   The Reduced Modular Set:
   reducePQ_def      |- !p q k. reducePQ p q k = {(p ** i * q ** j) MOD k | 0 <= i /\ 0 <= j}
   reducePQ_alt      |- !p q k. reducePQ p q k =
                                IMAGE (\(i,j). (p ** i * q ** j) MOD k) (univ(:num) CROSS univ(:num))
   reducePQ_element  |- !p q k x. x IN reducePQ p q k <=> ?i j. x = (p ** i * q ** j) MOD k
   reducePQ_has_one  |- !p q k. 1 MOD k IN reducePQ p q k
   reducePQ_nonempty |- !p q k. reducePQ p q k <> {}
   reducePQ_has_1    |- !p q k. 1 < k ==> 1 IN reducePQ p q k
   reducePQ_subset   |- !p q k. 0 < k ==> reducePQ p q k SUBSET count k
   reducePQ_finite   |- !p q k. 0 < k ==> FINITE (reducePQ p q k)
   reducePQ_upper    |- !p q k. 0 < k ==> CARD (reducePQ p q k) <= k

   Monoids of Set N and M:
   monoidN_def       |- !r k s. monoidN r k s = <|carrier := N; op := $*; id := 1|>
   monoidN_monoid    |- !r k s. Ring r /\ 0 < k ==> Monoid (monoidN r k s)
   monoidM_def       |- !r k s. monoidM r k s =
                               <|carrier := M; op := (\x y. (x * y) MOD k); id := 1|>
   monoidM_property  |- !r k s. ((monoidM r k s).carrier = M) /\
                                (!x. x IN (monoidM r k s).carrier <=> x IN M) /\
                                (!x y. x IN (monoidM r k s).carrier /\ y IN (monoidM r k s).carrier ==>
                                       ((monoidM r k s).op x y = (x * y) MOD k)) /\
                                       ((monoidM r k s).id = 1)
   monoidM_monoid    |- !r k s. Ring r /\ 1 < k ==> Monoid (monoidM r k s)
   monoidM_finite_monoid    |- !r k s. Ring r /\ 1 < k ==> FiniteMonoid (monoidM r k s)

   Introspective Monomials in Quotient Ring:
   intro_monomials_def      |- !r n k. intro_monomials r n k = {X + |c| | c | n intro X + |c|}
   intro_monomials_alt      |- !r n k. intro_monomials r n k = IMAGE (\c. X + |c|) {c | n intro X + |c|}
   intro_monomials_element  |- !r n k p. p IN intro_monomials r n k <=> ?c. (p = X + |c|) /\ n intro p
   intro_monomials_subset   |- !r n k z. Ring r /\ poly z /\ 1 < deg z ==>
                            intro_monomials r n k SUBSET ((PolyModRing r z).prod excluding |0|).carrier
   intro_monomials_group_def        |- !r n k z. intro_monomials_group r n k z =
                         Generated_subset ((PolyModRing r z).prod excluding |0|) (intro_monomials r n k)
   intro_monomials_group_group      |- !r n k z. Field r /\ ipoly z /\ 1 < deg z ==>
                                                 Group (intro_monomials_group r n k z):
   intro_monomials_group_subgroup   |- !r n k z. Field r /\ ipoly z /\ 1 < deg z ==>
                                    intro_monomials_group r n k z <= (PolyModRing r z).prod excluding |0|

   intro_exp_mod_def           |- !r k s. intro_exp_mod r k s =
                                          {m MOD k | m | coprime m k /\ poly_intro_range r k m s}
   intro_exp_mod_element       |- !r k s n. n IN intro_exp_mod r k s <=>
                                  ?m. (n = m MOD k) /\ coprime m k /\ poly_intro_range r k m s
   intro_exp_mod_thm           |- !r k s. intro_exp_mod r k s = M
   intro_exp_mod_has_char_mod  |- !r k s. FiniteField r /\ 0 < k /\ coprime (char r) k ==>
                                          char r MOD k IN intro_exp_mod r k s
   intro_exp_mod_closure       |- !r k s. Ring r /\ 0 < k ==>
                                  !m n. m IN intro_exp_mod r k s /\ n IN intro_exp_mod r k s ==>
                                        (m * n) MOD k IN intro_exp_mod r k s
   intro_exp_mod_has_product   |- !r k s. Ring r /\ 0 < k ==>
                                  !m n. m IN intro_exp_mod r k s /\ n IN intro_exp_mod r k s ==>
                                        (m * n) MOD k IN intro_exp_mod r k s
   intro_exp_mod_subset_euler  |- !r k s. 1 < k ==> intro_exp_mod r k s SUBSET Euler k
   intro_exp_mod_group_def     |- !r k s. intro_exp_mod_group r k s =
                                          Generated_subset (Estar k) (intro_exp_mod r k s)
   intro_exp_mod_group_group      |- !r k s. 1 < k ==> Group (intro_exp_mod_group r k s)
   intro_exp_mod_group_subgroup   |- !r k s. 1 < k ==> intro_exp_mod_group r k s <= Estar k
*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* A modular proof of AKS Main Theorem                                       *)
(* ------------------------------------------------------------------------- *)

(* AKS_main_ulog_2b;
val it = |- !r. FiniteField r /\ (CARD R = char r) ==>
          !n k. 0 < n /\ 0 < k /\ 1 < ordz k (char r) /\ char r divides n /\
                k < char r /\ ulog n ** 2 <= ordz k n /\
                poly_intro_range r k n (SQRT (phi k) * ulog n) ==>
                perfect_power n (char r): thm
*)

(* Collect all AKS checks for introspective in a general FiniteField r *)
val aks_criteria_def = Define`
   aks_criteria (r:'a field) n k <=>
      0 < n /\ 0 < k /\ (* both positive *)
      1 < ordz k (char r) /\ char r divides n /\ k < char r /\ (* involving (char r) *)
      ulog n ** 2 <= ordz k n /\ (* use of a = ulog n ** 2 *)
      poly_intro_range r k n (SQRT (phi k) * ulog n) (* use of s = SQRT (phi k) * ulog n *)
`;
(* FiniteField r will be (ZN p) where p divides n *)
(* 1 < ordz k (char r) gives 1 < k, by ZN_order_mod_1 *)
(* Use poly_intro_range for theory criteria in a Ring r *)

(*
AKS_main_ulog_3b
val it = |- !n k. 1 < n /\ 0 < k /\ (!j. 1 < j /\ j <= k ==> ~(j divides n)) /\
                  ulog n ** 2 <= ordz k n /\
                  poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n) ==>
              ?p. prime p /\ perfect_power n p: thm
*)

(* Collect the actual AKS checks, given n and parameter k. *)
val aks_checks_def = Define`
   aks_checks n k <=>
      1 < k /\
      (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\  (* divisibility checks *)
      ulog n ** 2 <= ordz k n /\  (* condition on k *)
      (k < n ==> poly_intro_checks n k (SQRT (phi k) * ulog n)) (* introspective checks *)
`;
(* Use poly_intro_checks for actual checks by algorithm. *)
(* 0 < k is required for ZN_intro_eqn, to convert poly_intro_range to poly_intro_checks. *)
(* Note: later (ZN n) is not supposed to be the FiniteField r. *)

(* Theorem: aks_checks n k <=> 1 < k /\ ulog n ** 2 <= ordz k n /\
          (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
          (k < n ==> poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n)) *)
(* Proof:
   By aks_checks_def, this is true   by ZN_intro_eqn, 0 < k, 0 < n.
*)
val aks_checks_alt = store_thm(
  "aks_checks_alt",
  ``!n k. aks_checks n k <=>
         (1 < k /\ ulog n ** 2 <= ordz k n /\
         (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
         (k < n ==> poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n)))``,
  rpt strip_tac >>
  `!n k. 1 < k /\ k < n ==> 0 < k /\ 0 < n` by decide_tac >>
  metis_tac[aks_checks_def, ZN_intro_eqn]);

(* The following is effectively the shifting from (ZN n) ring to (ZN p) finite field. *)

(* Theorem: k < n /\ aks_checks n k ==> ?p. prime p /\ aks_criteria (ZN p) n k *)
(* Proof:
   By aks_checks_alt, aks_criteria_def, this is to show:
   ?p. prime p /\ k < char (ZN p) /\ coprime n k /\
     char (ZN p) divides n /\ 1 < ordz k (char (ZN p)) /\
     poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n)

   Let a = (ulog n) ** 2,
       s = SQRT (phi k) * (ulog n).
   If n = 2,
      Take p = 2.
      Then prime 2             by PRIME_2, for prime p
       and char (ZN 2) = 2     by ZN_char
      Thus 2 divides 2         by DIVIDES_REFL, for char (ZN p) divides n
      With 1 < k /\ k < n as precondition,
      There are no such k to invalidate other results invoking k, thus true.
   If n <> 2,
   Then 1 < a                  by ulog_sq_gt_1, 2 < n
     so 1 < ordz k n           by a <= ordz k n
    ==> ?p. prime p /\ p divides n /\ 1 < ordz k p
                               by ZN_order_gt_1_property, 0 < k /\ 1 < ordz k n
   Note 0 < p                  by PRIME_POS
     so char (ZN p) = p        by ZN_char, 0 < p

   Take this prime p.
   Note 1 < n                  by 1 < k /\ k < n
   The subgoals are:
   (1) k < p
       Note !j. 1 < j /\ j <= k ==> ~(j divides n)
                               by k < n
       Also 1 < p              by ONE_LT_PRIME
       thus k < p              by 1 < p /\ p <= k ==> ~(p divides n)
   (2) poly_intro_range (ZN p) k n s
       Note 0 < n and 0 < k    by 1 < n, 1 < k
       Note coprime k n        by coprime_by_le_not_divides, 1 < k
        and s <= phi k         by ZN_order_condition_property_2, 1 < n, coprime k n
        but phi k <= k         by phi_le
         so s < p              by s <= phi k <= k < p
        Now poly_intro_range (ZN n) k n s   by implication, k < n
        ==> poly_intro_range (ZN p) k n s   by ring_homo_intro_ZN_to_ZN_X_add_c, s < p, 0 < n, 0 < k
*)
val aks_checks_gives_aks_criteria = store_thm(
  "aks_checks_gives_aks_criteria",
  ``!n k. k < n /\ aks_checks n k ==> ?p. prime p /\ aks_criteria (ZN p) n k``,
  rw_tac std_ss[aks_checks_alt, aks_criteria_def] >>
  Cases_on `n = 2` >| [
    qexists_tac `2` >>
    `prime 2` by rw[PRIME_2] >>
    `char (ZN 2) = 2` by rw[ZN_char] >>
    decide_tac,
    qabbrev_tac `a = (ulog n) ** 2` >>
    qabbrev_tac `s = SQRT (phi k) * (ulog n)` >>
    `1 < a` by rw[ulog_sq_gt_1, Abbr`a`] >>
    `1 < ordz k n` by decide_tac >>
    `?p. prime p /\ p divides n /\ 1 < ordz k p` by rw[ZN_order_gt_1_property] >>
    `1 < p` by rw[ONE_LT_PRIME] >>
    `char (ZN p) = p` by rw[ZN_char] >>
    qexists_tac `p` >>
    simp[] >>
    `k < p` by
  (`!j. 1 < j /\ j <= k ==> 1 < j /\ j <= k /\ j < n` by decide_tac >>
    metis_tac[NOT_LESS, LESS_EQ_REFL]) >>
    simp[] >>
    `s < p` by
    (`1 < n` by decide_tac >>
    `coprime k n` by rw[coprime_by_le_not_divides] >>
    `s <= phi k` by metis_tac[ZN_order_condition_property_2] >>
    `phi k <= k` by rw[phi_le] >>
    decide_tac) >>
    `0 < k /\ 0 < n` by decide_tac >>
    metis_tac[ring_homo_intro_ZN_to_ZN_X_add_c]
  ]);

(* Theorem: 0 < p /\ aks_criteria (ZN p) n k ==>
            0 < n /\ 0 < k /\ 1 < ordz k p /\
            p divides n /\ k < p /\ ulog n ** 2 <= ordz k n /\
            poly_intro_range (ZN p) k n (SQRT (phi k) * ulog n) *)
(* Proof:
   Let r = ZN p.
   Then char (ZN p) = p      by ZN_char, 0 < p

   aks_criteria_def |> ISPEC ``(ZN p)``;
   val it = |- !n k. aks_criteria (ZN p) n k <=>
          0 < n /\ 0 < k /\ 1 < ordz k (char (ZN p)) /\
          char (ZN p) divides n /\ k < char (ZN p) /\
          ulog n ** 2 <= ordz k n /\
          poly_intro_range (ZN p) k n (SQRT (phi k) * ulog n)
*)
val aks_criteria_ZN = store_thm(
  "aks_criteria_ZN",
  ``!p n k. 0 < p /\ aks_criteria (ZN p) n k ==>
           0 < n /\ 0 < k /\ 1 < ordz k p /\
           p divides n /\ k < p /\ ulog n ** 2 <= ordz k n /\
           poly_intro_range (ZN p) k n (SQRT (phi k) * ulog n)``,
  metis_tac[aks_criteria_def, ZN_char]);

(* Theorem: FiniteField r /\ (CARD R = char r) ==>
            !n k. aks_criteria r n k ==> perfect_power n (char r) *)
(* Proof:
   After expanding by aks_criteria_def,
   this is just AKS_main_ulog_2b in disguise.
*)
val aks_main_punch = store_thm(
  "aks_main_punch",
  ``!r:'a field. FiniteField r /\ (CARD R = char r) ==>
   !n k. aks_criteria r n k ==> perfect_power n (char r)``,
  metis_tac[aks_criteria_def, AKS_main_ulog_2b]);

(* This is the basic punch line. *)

(* Theorem: FiniteField r /\ (CARD R = char r) ==>
            !n k. 0 < n /\ 0 < k /\ 1 < ordz k (char r) /\
                  char r divides n /\ k < char r /\
                  ulog n ** 2 <= ordz k n /\
                  poly_intro_range r k n (SQRT (phi k) * ulog n)
              ==> perfect_power n (char r) *)
(* Proof:
   This is just AKS_main_ulog_2b to fit aks_criteria.
*)
val aks_main_punch_alt = store_thm(
  "aks_main_punch_alt",
  ``!r:'a field. FiniteField r /\ (CARD R = char r) ==>
   !n k. 0 < n /\ 0 < k /\ 1 < ordz k (char r) /\
         char r divides n /\ k < char r /\
         ulog n ** 2 <= ordz k n /\
         poly_intro_range r k n (SQRT (phi k) * ulog n)
     ==> perfect_power n (char r)``,
  metis_tac[AKS_main_ulog_2b]);

(* Theorem: FiniteField r /\ (CARD R = char r) ==>
   !n a k s. 0 < n /\ 0 < k /\ 1 < ordz k (char r) /\
             char r divides n /\ k < char r /\
             (a = ulog n ** 2) /\ (s = SQRT (phi k) * ulog n) /\
              a <= ordz k n /\ poly_intro_range r k n s
          ==> perfect_power n (char r) *)
(* Proof: another format for aks_main_punch_alt. *)
val aks_main_punch_thm = store_thm(
  "aks_main_punch_thm",
  ``!r:'a field. FiniteField r /\ (CARD R = char r) ==>
   !n a k s. 0 < n /\ 0 < k /\ 1 < ordz k (char r) /\
         char r divides n /\ k < char r /\
         (a = ulog n ** 2) /\ (s = SQRT (phi k) * ulog n) /\
         a <= ordz k n /\ poly_intro_range r k n s
     ==> perfect_power n (char r)``,
  metis_tac[aks_main_punch_alt]);

(* Theorem: prime p /\ 0 < n /\ 0 < k /\
            1 < ordz k p /\ p divides n /\ k < p /\
            (a = ulog n ** 2) /\ (s = SQRT (phi k) * ulog n) /\
             a <= ordz k n /\ poly_intro_range (ZN p) k n s
         ==> perfect_power n p *)
(* Proof:
   Let r = ZN p.
   Then FiniteField r        by ZN_finite_field, prime p
    and CARD R = p           by ZN_card
    and char r = p           by ZN_char, 0 < p
   Hence true                by aks_main_punch_alt
*)
val aks_main_punch_ZN = store_thm(
  "aks_main_punch_ZN",
  ``!p n a k s. prime p /\ 0 < n /\ 0 < k /\
               1 < ordz k p /\ p divides n /\ k < p /\
               (a = ulog n ** 2) /\ (s = SQRT (phi k) * ulog n) /\
               a <= ordz k n /\ poly_intro_range (ZN p) k n s
           ==> perfect_power n p``,
  rpt strip_tac >>
  `FiniteField (ZN p)` by rw[ZN_finite_field] >>
  `CARD (ZN p).carrier = p` by rw[ZN_card] >>
  `char (ZN p) = p` by rw[ZN_char] >>
  metis_tac[aks_main_punch_alt]);


(* Theorem: k < n /\ aks_checks n k ==> ?p. prime p /\ perfect_power n p *)
(* Proof:
   Note aks_checks n k
    ==> ?p. prime p /\ aks_criteria (ZN p) n k   by aks_checks_gives_aks_criteria, k < n
    Now 0 < p                      by PRIME_POS
    and CARD (ZN p).carrier = p    by ZN_card
    and char (ZN p) = p            by ZN_char, 0 < p
    and FiniteField (ZN p)         by ZN_finite_field, prime p
   Take this prime p,
   Then perfect_power n p          by aks_main_punch
*)
val aks_main_step = store_thm(
  "aks_main_step",
  ``!n k. k < n /\ aks_checks n k ==> ?p. prime p /\ perfect_power n p``,
  rpt strip_tac >>
  `?p. prime p /\ aks_criteria (ZN p) n k` by rw[aks_checks_gives_aks_criteria] >>
  `0 < p` by rw[PRIME_POS] >>
  `CARD (ZN p).carrier = p` by rw[ZN_card] >>
  `char (ZN p) = p` by rw[ZN_char] >>
  `FiniteField (ZN p)` by rw[ZN_finite_field] >>
  metis_tac[aks_main_punch]);

(* Theorem: For prime n, there is always a k that gives aks_checks n k.
            prime n ==> ?k. aks_checks n k *)
(* Proof:
   If n = 2,
   Take k = 3 to meet aks_checks 2 3:
   (1) (ulog 2) ** 2 <= ordz 3 2
       Note ulog 2 = 1                 by ulog_2
        and (2 ** 1) MOD 3 = 2         by EXP_1
        and (2 ** 2) MOD 3 = 1         by EXP_2
        and !j. 0 < j /\ j < 2 <=> (j = 1)   by range
       Thus ordz 3 2 = 2               by ZN_order_test_1
   (2) 1 < j /\ j <= 3 /\ j < 2 ==> ~(j divides 2)
       There is no j to invalidate this.
   And 3 > 2, so there is no polynomial introspective check.

   If n <> 2,
   Note prime n ==> 0 < n              by PRIME_POS
    Let a = (ulog n) ** 2,
        s = SQRT (phi k) * (ulog n).
   Then 1 < a                          by ulog_sq_gt_1, 2 < n
     so ?k. 1 < k /\ coprime k n /\ a <= ordz k n
                                       by ZN_order_good_enough, 1 < n, 1 < a

   Take this k, the subgoals by aks_checks_alt are:
   (1) prime n /\ 0 < j /\ j <= k /\ j < n ==> ~(j divides n)
       Ignore j <= k, this is true  by prime_def
   (2) prime n /\ 0 < c /\ c <= s ==> poly_intro (ZN n) k n (x+ n c)
       Note 0 < k                             by 1 < k
         so poly_intro (ZN n) k n (x+ n c)    by ZN_intro_by_prime, 0 < c
*)
val aks_when_prime = store_thm(
  "aks_when_prime",
  ``!n. prime n ==> ?k. aks_checks n k``,
  rpt strip_tac >>
  Cases_on `n = 2` >| [
    qexists_tac `3` >>
    rw[ulog_2, aks_checks_alt] >>
    `(2 ** 1) MOD 3 = 2` by rw[] >>
    `(2 ** 2) MOD 3 = 1` by rw[] >>
    `1 < 3 /\ 0 < 2 /\ 2 <> 1 /\ 0 <> 1 /\ !j. 0 < j /\ j < 2 <=> (j = 1)` by decide_tac >>
    `ordz 3 2 = 2` by metis_tac[ZN_order_test_1] >>
    decide_tac,
    qabbrev_tac `a = (ulog n) ** 2` >>
    `1 < n` by rw[ONE_LT_PRIME] >>
    `1 < a` by rw[ulog_sq_gt_1, Abbr`a`] >>
    `?k. 1 < k /\ coprime k n /\ a <= ordz k n` by rw[ZN_order_good_enough] >>
    qexists_tac `k` >>
    rw_tac std_ss[aks_checks_alt] >-
    metis_tac[prime_def, LESS_NOT_EQ] >>
    rw[ZN_intro_by_prime]
  ]);

(* Theorem: prime n ==> power_free n /\ ?k. aks_checks n k *)
(* Proof:
   If part: prime n ==> power_free n /\ ?k. aks_checks n k
      Given prime n,
         so prower_free n         by prime_is_power_free
        and ?k. aks_checks n k    by aks_when_prime
*)
val aks_main_theorem_1 = store_thm(
  "aks_main_theorem_1",
  ``!n. prime n ==> power_free n /\ ?k. aks_checks n k``,
  rw[prime_is_power_free, aks_when_prime]);

(* Therefore:
Since prime 7, power_free 7, ?k. aks_checks 7 k.
But ~prime 10, power_free 10, there is no such k for aks_checks 10 k.
*)

(* Theorem: power_free n /\ aks_checks n k ==> prime n *)
(* Proof:
   Only-if part: power_free n /\ ?k. aks_checks n k ==> prime n
      Note 1 < n                  by power_free_gt_1
      From aks_checks_def, we know only a parameter k,
      but we don't know whether k < n or not.
      If k < n,
         Then ?p. prime p /\ perfect_power n p   by aks_main_step, 1 < n
          ==> p = n, or prime n                  by power_free_perfect_power
      If ~(k < n),
         Then n <= k, or j <= k /\ j < n is redundant,
         That is, !j. 1 < j /\ j < n ==> 1 < j /\ j <= k /\ j < n
         Combine with aks_checks_def implication:
                  !j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)
         This gives: !j. 1 < j /\ j < n ==> ~(j divides n)
         Thus prime n                            by prime_iff_no_proper_factor, 1 < n
*)
val aks_main_theorem_2 = store_thm(
  "aks_main_theorem_2",
  ``!n k. power_free n /\ aks_checks n k ==> prime n``,
  rpt strip_tac >>
  `1 < n` by rw[power_free_gt_1] >>
  Cases_on `k < n` >-
  metis_tac[aks_main_step, power_free_perfect_power] >>
  fs[aks_checks_def] >>
  `!j. 1 < j /\ j < n ==> 1 < j /\ j <= k /\ j < n` by decide_tac >>
  metis_tac[prime_iff_no_proper_factor]);

(* Theorem: [The AKS Main Theorem]
            prime n <=> power_free n /\ ?k. aks_checks n k *)
(* Proof:
   If part: prime n ==> power_free n /\ ?k. aks_checks n k
      True by aks_main_theorem_1.
   Only-if part: power_free n /\ ?k. aks_checks n k ==> prime n
      True by aks_main_theorem_2.
*)
val aks_main_theorem = store_thm(
  "aks_main_theorem",
  ``!n. prime n <=> power_free n /\ ?k. aks_checks n k``,
  metis_tac[aks_main_theorem_1, aks_main_theorem_2]);

(* ------------------------------------------------------------------------- *)
(* AKS algorithm based on parameter search                                   *)
(* ------------------------------------------------------------------------- *)

(* Express AKS algorithm in terms of possible results of AKS parameter search. *)
val aks_def = zDefine`
    aks n <=>
       power_free n /\         (* power_free n implies 1 < n *)
       case aks_param n of     (* search for AKS parameter given n *)
         nice j => (j = n)     (* found j that will show n prime or composite directly *)
       | good k =>             (* found k with m <= ordz k n, where m = (ulog n) ** 2 *)
            poly_intro_checks n k (SQRT (phi k) * ulog n)
       | bad => F              (* impossible *)
`;
(* Note: use zDefine to avoid putting into computeLib by default,
   as poly_intro_checks uses !c. 0 < c /\ c <= m ==> ((x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k))
   which is symbolic.

EVAL ``aks_param 31``; = good 29
EVAL ``SQRT (phi 29) * ulog 31``; = 25
EVAL ``(x+^ 31 1 31 == x^+ 31 1 31) (pmod (ZN 31) (x^- 31 29))``; <=> T
EVAL ``(x+^ 31 2 31 == x^+ 31 2 31) (pmod (ZN 31) (x^- 31 29))``; <=> T
EVAL ``!c. 0 < c /\ c <= 25 ==> ((x+^ 31 c 31 == x^+ 31 c 31) (pmod (ZN 31) (x^- 31 29)))``;
-- symbolic evaluation with c

EVAL ``let c = 2 in (x+^ 31 c 31 == x^+ 31 c 31) (pmod (ZN 31) (x^- 31 29))``;
EVAL ``let c = 10 in (x+^ 31 c 31 == x^+ 31 c 31) (pmod (ZN 31) (x^- 31 29))``;
EVAL ``let c = 20 in (x+^ 31 c 31 == x^+ 31 c 31) (pmod (ZN 31) (x^- 31 29))``;
EVAL ``let c = 25 in (x+^ 31 c 31 == x^+ 31 c 31) (pmod (ZN 31) (x^- 31 29))``;
all return T.

> time EVAL ``aks_compute 5``;
runtime: 0.01082s,    gctime: 0.00082s,     systime: 0.00072s.
val it = |- aks_compute 5 <=> T: thm
> time EVAL ``aks_compute 31``;
runtime: 56.2s,    gctime: 5.5s,     systime: 4.1s.
val it = |- aks_compute 31 <=> T: thm
*)

(*
EVAL ``aks_param 31``; = good 29
EVAL ``SQRT (phi 29) * ulog 31``; = 25
EVAL ``poly_intro_checks 31 29 25``; -- symbolic by for all
*)

(* Theorem: aks n <=> power_free n /\
                      case aks_param n of
                        nice j => j = n
                      | good k =>
                        EVERY (\c. (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k)))
                              [1 .. (SQRT (phi k) * ulog n)]
                      | bad => F *)
(* Proof: by aks_def, poly_intro_checks_thm] *)
val aks_eval = store_thm(
  "aks_eval[compute]",
  ``!n. aks n <=> power_free n /\
                 case aks_param n of
                   nice j => j = n
                 | good k =>
                   (* poly_intro_checks n k (SQRT (phi k) * ulog n) *)
                   EVERY (\c. (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k)))
                         [1 .. (SQRT (phi k) * ulog n)]
                 | bad => F``,
  simp[aks_def, poly_intro_checks_thm]);

(*
EVAL ``aks 7``; <=> T
EVAL ``aks 17``; <=> T
EVAL ``aks 27``; <=> F
EVAL ``aks 31``; <=> T
time EVAL ``aks 31``; <=> T
runtime: 24.7s,    gctime: 2.6s,     systime: 1.7s.
val it = |- aks 31 <=> T: thm
> time EVAL ``aks 97``;
runtime: 9m01s,    gctime: 52.4s,     systime: 32.7s.
val it = |- aks 97 <=> T: thm

This makes (aks_compute n) redundant.
*)

(* Theorem: (aks_param n = good k) /\ power_free n ==>
            (prime n <=> poly_intro_checks n k (SQRT (phi k) * ulog n)) *)
(* Proof:
   Note aks_param 0 = nice 0           by aks_param_0
    and aks_param 1 = nice 1           by aks_param_1
   Let s = SQRT (phi k) * (ulog n).
   Thus 1 < n                          by n <> 0, n <> 1
   If part: prime n ==> poly_intro_checks n k s
      Note 1 < k                       by aks_param_good, 1 < n, aks_param n = good k
      Thus 0 < k                       by ONE_LT_POS
      Hence result is true             by ZN_intro_checks_by_prime, 0 < k

   Only-if part: poly_intro_checks n k s ==> prime n
    Now 1 < k /\ (ulog n) ** 2 <= ordz k n /\ !j. 1 < j /\ j <= k ==> ~(j divides n)
                                                     by aks_param_good, EXP_2
     or !j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)
                                                     just more conditions
   With poly_intro_checks n k s                      by given
    ==> prime n                                      by AKS_main_ulog_8b, 0 < k
*)
val aks_param_good_for_prime = store_thm(
  "aks_param_good_for_prime",
  ``!n k. (aks_param n = good k) /\ power_free n ==>
   (prime n <=> poly_intro_checks n k (SQRT (phi k) * ulog n))``,
  rpt strip_tac >>
  qabbrev_tac `s = SQRT (phi k) * (ulog n)` >>
  `!n k. nice n <> good k` by rw[] >>
  `n <> 0 /\ n <> 1` by metis_tac[aks_param_0, aks_param_1] >>
  `1 < n` by decide_tac >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    `0 < k` by metis_tac[aks_param_good, ONE_LT_POS] >>
    metis_tac[ZN_intro_checks_by_prime],
    `1 < k /\ (ulog n) ** 2 <= ordz k n /\ !j. 1 < j /\ j <= k ==> ~(j divides n)` by metis_tac[aks_param_good, EXP_2] >>
    `0 < k` by decide_tac >>
    metis_tac[AKS_main_ulog_8b]
  ]);

(* Theorem: (aks_param n = good k) ==>
            (poly_intro_checks n k (SQRT (phi k) * ulog n) = (1 < n /\ k < n /\ aks_checks n k)) *)
(* Proof:
   Note 1 < n /\ 1 < k /\ k < n                  by aks_param_good_range
     so !m. poly_intro_checks n k m
          = poly_intro_range (ZN n) k n m        by ZN_intro_range_eqn, 1 < k /\ k < n
   Also !j. 1 < j /\ j <= k ==> ~(j divides n)   by aks_param_good
    and ulog n ** 2 <= ordz k n                  by aks_param_good, EXP_2
   Thus aks_checks n k                           by aks_checks_def
    The converse is true                         by aks_checks_def
*)
val aks_param_good_gives_checks_eq_checks = store_thm(
  "aks_param_good_gives_checks_eq_checks",
  ``!n k. (aks_param n = good k) ==>
         (poly_intro_checks n k (SQRT (phi k) * ulog n) = (1 < n /\ k < n /\ aks_checks n k))``,
  rpt strip_tac >>
  `!j. 1 < j /\ j <= k ==> ~(j divides n)` by rw_tac std_ss[aks_param_good] >>
  `ulog n ** 2 <= ordz k n` by rw_tac std_ss[aks_param_good, EXP_2] >>
  `1 < n /\ 1 < k /\ k < n` by metis_tac[aks_param_good_range] >>
  `!j. 1 < j /\ j <= k /\ j < n ==> 1 < j /\ j < n` by decide_tac >>
  rw_tac std_ss[aks_checks_def, ZN_intro_range_eqn]);

(* Theorem: 1 < n /\ (aks_param n = good k) ==> SQRT (phi k) * ulog n <= k *)
(* Proof: by aks_param_good_coprime_order, sqrt_phi_times_ulog_less *)
val aks_param_good_intro_limit = store_thm(
  "aks_param_good_intro_limit",
  ``!n k. 1 < n /\ (aks_param n = good k) ==> SQRT (phi k) * ulog n <= k``,
  metis_tac[aks_param_good_coprime_order, sqrt_phi_times_ulog_less, ONE_LT_POS]);

(* Theorem: 1 < n /\ (aks_param n = good k) /\ (s = SQRT (phi k) * ulog n) ==> s <= k *)
(* Proof: by aks_param_good_intro_limit *)
val aks_param_good_intro_limit_alt = store_thm(
  "aks_param_good_intro_limit_alt",
  ``!n k s. 1 < n /\ (aks_param n = good k) /\ (s = SQRT (phi k) * ulog n) ==> s <= k``,
  metis_tac[aks_param_good_intro_limit]);

(* Theorem: aks n ==> power_free n /\ ?k. aks_checks n k *)
(* This is if-part of aks_alt, just by definitions. *)
(* Proof:
   Expand by aks_def,
   Consider cases of aks_param n, this is to show:
   (1) power_free n /\ aks_param n = nice n' ==> ?k. aks_checks n k
       Note power_free n ==> 1 < n                      by power_free_gt_1
           aks_param n = nice n'
       ==> (n' = n)
       <=> prime n                                      by aks_param_nice_for_prime, 1 < n
       ==> ?k. aks_checks n k                           by aks_when_prime
   (2) power_free /\ aks_param n = good n' ==> ?k. aks_checks n k
           aks_param n = good n'
       ==> poly_intro_checks n n' s                     where s = SQRT (phi k) * ulog n
       ==> aks_checks n n'                              by aks_param_good_gives_checks_eq_checks
   (3) aks_param n = bad ==> ...
       True, since aks_param n <> bad                   by aks_param_exists
*)
val aks_alt_if = store_thm(
  "aks_alt_if",
  ``!n. aks n ==> power_free n /\ ?k. aks_checks n k``,
  rw_tac std_ss[aks_def] >>
  Cases_on `aks_param n` >| [
    `n' = n` by fs[] >>
    `1 < n` by rw[power_free_gt_1] >>
    `prime n` by metis_tac[aks_param_nice_for_prime] >>
    metis_tac[aks_when_prime],
    `poly_intro_checks n n' (SQRT (phi n') * ulog n)` by fs[] >>
    metis_tac[aks_param_good_gives_checks_eq_checks],
    metis_tac[aks_param_exists]
  ]);

(* Theorem: aks n = power_free n /\ ?k. aks_checks n k *)
(* Proof:
   Expand by aks_def,
   Consider cases of aks_param n, this is to show:
   (1) aks_param n = nice n' ==>
       power_free n /\ (n' = n) <=> power_free n /\ ?k. aks_checks n k
       Note power_free n ==> 1 < n                      by power_free_gt_1
           aks_param n = nice n'
       ==> (n' = n) <=> prime n                         by aks_param_nice_for_prime, 1 < n
                    <=> ?k. aks_checks n k              by aks_main_theorem
   (2) aks_param n = good n' ==>
         power_free n /\
         (!c. 0 < c /\ c <= SQRT (phi n') * ulog n ==> (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n n'))) <=>
         power_free n /\ ?k. aks_checks n k
           aks_param n = good n'
       ==> (!c. 0 < c /\ .... ) <=> prime n             by aks_param_good_for_prime
                                <=> ?k. aks_checks n k  by aks_main_theorem
   (3) aks_param n = bad ==> ...
       True, since aks_param n <> bad                   by aks_param_exists
*)
val aks_alt = store_thm(
  "aks_alt",
  ``!n. aks n <=> power_free n /\ ?k. aks_checks n k``,
  rw_tac std_ss[aks_def] >>
  Cases_on `aks_param n` >| [
    rw_tac std_ss[] >>
    metis_tac[aks_param_nice_for_prime, aks_main_theorem, power_free_gt_1],
    rw_tac std_ss[] >>
    metis_tac[aks_param_good_for_prime, aks_main_theorem],
    metis_tac[aks_param_exists]
  ]);

(* Theorem: prime n = aks n *)
(* Proof:
       prime n
   <=> power_free n /\ ?k. aks_checks n k   by aks_main_theorem
   <=> aks n                                by aks_alt
*)
val aks_theorem = store_thm(
  "aks_theorem",
  ``!n. prime n = aks n``,
  rw[aks_alt, aks_main_theorem]);

(* A major milestone -- first proof of the AKS theorem! *)

(*
The following is a direct proof, without aks_main_theorem.
If part is the easy direction.
Only-if part uses aks_param_good_for_prime, relies on AKS_main_ulog_8b.
*)

(* Theorem: prime n ==> aks n *)
(* This is the if part of aks_thm *)
(* Proof:
   If part: prime n ==> aks n
      By aks_def, the subgoals are:
      (1) prime n ==> power_free n, true            by prime_is_power_free
      (2) prime n ==> case aks_param n of ...
          Note 1 < n                                by ONE_LT_PRIME

          Consider cases of aks_param n, this is to show:
          (1) aks_param n = nice n' ==> n' = n
              By contradiction, suppose n' <> n.
              Note 1 < n' /\ n' divides n           by aks_param_nice, 1 < n
               ==> n' = 1, divisor of prime         by prime_def, prime n
               ==> 1 < 1                            by above
              This is a contradiction.

          (2) aks_param n = good n' ==> poly_intro_checks n n' (SQRT (phi n') * ulog n)
              Note 1 < n'                           by aks_param_good
                so 0 < n'                           by arithmetic
              This is true                          by ZN_intro_checks_by_prime, 0 < n'

          (3) aks_param n = bad ==> F
              Note aks_param n <> bad               by aks_param_exists
              This is a contradiction, hence true.
*)
val aks_thm_1 = store_thm(
  "aks_thm_1",
  ``!n. prime n ==> aks n``,
  rw_tac std_ss[aks_def] >-
  rw[prime_is_power_free] >>
  `1 < n` by rw[ONE_LT_PRIME] >>
  Cases_on `aks_param n` >| [
    simp[] >>
    spose_not_then strip_assume_tac >>
    `1 < n' /\ n' divides n` by metis_tac[aks_param_nice] >>
    `n' = 1` by metis_tac[prime_def] >>
    decide_tac,
    rw_tac std_ss[] >>
    `0 < n'` by metis_tac[aks_param_good_range, ONE_LT_POS] >>
    metis_tac[ZN_intro_checks_by_prime],
    metis_tac[aks_param_exists]
  ]);

(* Theorem: aks n ==> prime n *)
(* This is the only-if part of aks_thm *)
(* Proof:
   Only-if part: aks n ==> prime n
      Expand by aks_def,
      Note power_free n ==> 1 < n                      by power_free_gt_1
      Consider cases of aks_param n, this is to show:
      (1) aks_param n = nice n' ==> prime n
          Note n' = n                                  by case of nice n'
           ==> prime n                                 by aks_param_nice_for_prime, 1 < n

      (2) aks_param n = good n' ==> prime n
          Let s = SQRT (phi n') * (ulog n),
          Then poly_intro_checks n n' s                by case of good n'
           ==> prime n                                 by aks_param_good_for_prime

      (3) aks_param n = bad ==> prime n
          The premise is false, hence true             by aks_param_exists
*)
val aks_thm_2 = store_thm(
  "aks_thm_2",
  ``!n. aks n ==> prime n``,
  rw_tac std_ss[aks_def] >>
  `1 < n` by rw[power_free_gt_1] >>
  Cases_on `aks_param n` >| [
    `n' = n` by fs[] >>
    metis_tac[aks_param_nice_for_prime],
    qabbrev_tac `s = SQRT (phi n') * (ulog n)` >>
    `poly_intro_checks n n' s` by fs[] >>
    metis_tac[aks_param_good_for_prime],
    metis_tac[aks_param_exists]
  ]);

(* Theorem: prime n = aks n *)
(* Proof:
   If part: prime n ==> aks n, true        by aks_thm_1
   Only-if part: aks n ==> prime n, true   by aks_thm_2
*)
val aks_thm = store_thm(
  "aks_thm",
  ``!n. prime n = aks n``,
  metis_tac[aks_thm_1, aks_thm_2]);

(* This is the ultimate theorem of AKS! *)

(* Theorem: prime n <=> power_free n /\
            case aks_param n of
               nice j => j = n
             | good k => poly_intro_checks n k (SQRT (phi k) * ulog n)
             | bad => F *)
(* Proof: by aks_thm, aks_def *)
val aks_eqn = store_thm(
  "aks_eqn",
  ``!n. prime n <=> power_free n /\
                   case aks_param n of
                     nice j => j = n
                   | good k => poly_intro_checks n k (SQRT (phi k) * ulog n)
                   | bad => F``,
  rw_tac std_ss[aks_thm, aks_def]);

(*
Although these set of iff-theorems look impressive:

aks_alt  |- !n. aks n <=> power_free n /\ ?k. aks_checks n k
aks_main_theorem   |- !n. prime n <=> power_free n /\ ?k. aks_checks n k
Thus
aks_thm  |- !n. prime n <=> aks n
It looks like that the first one:
aks_alt  can be proved purely by definitions.
But this is not the case.

What happens is this:
(1) prime n ==> aks n        aks_thm_1
    This is the EASY part.
    no deep theory.
    just ZN_intro_checks_by_prime      for any range.
Then the HARD part:
(2) aks n ==>
    power_free n /\ ?k. aks_checks n k    aks_alt_if
    This part can be shown purely from definitions
(3) power_free n /\ aks_checks n k ==> prime n    aks_main_theorem_2
    This is the part that needs aks_main_theorem,
    in the following sense:
aks_checks_gives_aks_criteria
|- !n k. k < n /\ aks_checks n k ==>
     ?p. prime p /\ aks_criteria (ZN p) n k
This is the shift, then
aks_main_punch
|- !r. FiniteField r /\ (CARD R = char r) ==>
   !n k. aks_criteria r n k ==> perfect_power n (char r)
which makes n a prime power, so
power_free_perfect_power
|- !m n. power_free n /\ perfect_power n m ==> (n = m)

Such a route is taken up in aks_decide.
*)

(* ------------------------------------------------------------------------- *)
(* Correctness of Introspective Computations                                 *)
(* ------------------------------------------------------------------------- *)

(* These requires poly_intro_X_add_c, poly_intro_range, poly_intro_checks. *)

(* Theorem: Ring r /\ #1 <> #0 ==> !k n. 1 < k /\ 0 < n ==>
            !c:num. unity_mod_intro r k n c = (n intro (X + |c|)) *)
(* Proof:
       unity_mod_intro r k n c
   <=> ((X + |c|) ** n == X ** n + |c|) (pm z)    by unity_mod_intro_alt
   <=> n intro (X + |c|)                          by poly_intro_X_add_c
*)
val unity_mod_intro_eqn = store_thm(
  "unity_mod_intro_eqn",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !k n. 1 < k /\ 0 < n ==>
   !c:num. unity_mod_intro r k n c <=> n intro (X + |c|)``,
  rw[unity_mod_intro_alt, poly_intro_X_add_c]);

(* Theorem: Ring r /\ #1 <> #0 ==> !k n. 1 < k /\ 0 < n ==>
           !m. unity_mod_intro_range r k n m = poly_intro_range r k n m *)
(* Proof:
   By induction on m.
   Base: unity_mod_intro_range r k n 0 <=> 0 < k /\ !c. 0 < c /\ c <= 0 ==> n intro X + |c|
      LHS = T                  by unity_mod_intro_range_def
      For RHS, there is no c such that 0 < c /\ c <= 0, hence also T for implication.
   Step: unity_mod_intro_range r k n m <=> 0 < k /\ !c. 0 < c /\ c <= m ==> n intro X + |c| ==>
         unity_mod_intro_range r k n (SUC m) <=> 0 < k /\ !c. 0 < c /\ c <= SUC m ==> n intro X + |c|
          unity_mod_intro_range r k n (SUC m)
      <=> unity_mod_intro r k n (SUC m) /\
          unity_mod_intro_range r k n m                 by unity_mod_intro_range_def
      <=> n intro (X + (poly_num r (SUC m))) /\
          unity_mod_intro_range r k n m                 by unity_mod_intro_eqn
      <=> n intro (X + (poly_num r (SUC m))) /\
          !c. 0 < c /\ c <= m ==> n intro X + |c|       by induction hypothesis
      <=> !c. 0 < c /\ c <= SUC m ==> n intro X + |c|   by merging indexes
*)
val unity_mod_intro_range_alt = store_thm(
  "unity_mod_intro_range_alt",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !k n. 1 < k /\ 0 < n ==>
   !m. unity_mod_intro_range r k n m = poly_intro_range r k n m``,
  rpt strip_tac >>
  Induct_on `m` >-
  rw[unity_mod_intro_range_def] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    `unity_mod_intro r k n (SUC m) /\ unity_mod_intro_range r k n m` by metis_tac[unity_mod_intro_range_def] >>
    `n intro X + ### (SUC m)` by rw[GSYM unity_mod_intro_eqn] >>
    metis_tac[DECIDE``j <= SUC m ==> j <= m \/ (j = SUC m)``],
    `unity_mod_intro_range r k n m /\ n intro X + ###(SUC m)` by rw[] >>
    metis_tac[unity_mod_intro_range_def, unity_mod_intro_eqn]
  ]);

(* Theorem: 1 < n /\ 1 < k ==>
            !m. unity_mod_intro_range (ZN n) k n m = poly_intro_checks n k m *)
(* Proof:
   Note 0 < n                 by 1 < n
   Thus Ring (ZN n)           by ZN_ring, 0 < n
    and (ZN n).sum.id = 0 /\
        (ZN n).prod.id = 1    by ZN_ids_alt, 1 < n
       unity_mod_intro_range (ZN n) k n m
   <=> poly_intro_range (ZN n) k n m      by unity_mod_intro_range_alt, Ring (ZN n)
   <=> poly_intro_checks n k m            by poly_intro_X_add_c
*)
val unity_mod_intro_range_eqn = store_thm(
  "unity_mod_intro_range_eqn",
  ``!n k. 1 < n /\ 1 < k ==>
   !m. unity_mod_intro_range (ZN n) k n m = poly_intro_checks n k m``,
  rpt strip_tac >>
  `0 < n /\ 0 < k` by decide_tac >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `((ZN n).sum.id = 0) /\ ((ZN n).prod.id = 1) /\ 1 <> 0` by rw[ZN_ids_alt] >>
  rw_tac std_ss[unity_mod_intro_range_alt, poly_intro_X_add_c]);

(* ------------------------------------------------------------------------- *)
(* Correctness of Direct Computation                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < n /\ 1 < k ==>
        !c. unity_mod_intro (ZN n) k n c = poly_intro (ZN n) k n (x+ n c) *)
(* Proof:
   Note Ring (ZN n)                       by ZN_ring, 0 < n
    and (ZN n).prod.id <> (ZN n).sum.id   by ZN_ids_alt, 1 < n

     unity_mod_intro (ZN n) k n c
   = poly_intro (ZN n) k n (x+ n c)       by unity_mod_intro_eqn, 1 < k, 0 < n, Ring (ZN n)
*)
val ZN_unity_mod_intro_eqn = store_thm(
  "ZN_unity_mod_intro_eqn",
  ``!n k. 1 < n /\ 1 < k ==> !c. unity_mod_intro (ZN n) k n c = poly_intro (ZN n) k n (x+ n c)``,
  rpt strip_tac >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `(ZN n).prod.id <> (ZN n).sum.id` by rw[ZN_ids_alt] >>
  rw[unity_mod_intro_eqn]);

(* Theorem: 1 < n /\ 1 < k ==>
        !c. unity_mod_intro_range (ZN n) k n c = poly_intro_range (ZN n) k n  *)
(* Proof:
   Note Ring (ZN n)                       by ZN_ring, 0 < n
    and (ZN n).prod.id <> (ZN n).sum.id   by ZN_ids_alt, 1 < n

     unity_mod_intro_range (ZN n) k n c
   = poly_intro (ZN n) k n (x+ n c)       by unity_mod_intro_range_alt, 1 < k, 0 < n, Ring (ZN n)
*)
val ZN_unity_mod_intro_range_eqn = store_thm(
  "ZN_unity_mod_intro_range_eqn",
  ``!n k. 1 < n /\ 1 < k ==>
   !c. unity_mod_intro_range (ZN n) k n c = poly_intro_range (ZN n) k n c``,
  rpt strip_tac >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `(ZN n).prod.id <> (ZN n).sum.id` by rw[ZN_ids_alt] >>
  rw[unity_mod_intro_range_alt]);

(* Theorem: 1 < n /\ 1 < k ==> !c. ZN_poly_intro n k c = poly_intro (ZN n) k n (x+ n c) *)
(* Proof:
     ZN_poly_intro n k c
   = unity_mod_intro (ZN n) k n c     by ZN_poly_intro_alt, 1 < n, 0 < k
   = poly_intro (ZN n) k n (x+ n c)   by ZN_unity_mod_intro_eqn, 1 < k, 1 < n
*)
val ZN_poly_intro_eqn = store_thm(
  "ZN_poly_intro_eqn",
  ``!n k. 1 < n /\ 1 < k ==> !c. ZN_poly_intro n k c = poly_intro (ZN n) k n (x+ n c)``,
  rw[ZN_poly_intro_alt, ZN_unity_mod_intro_eqn]);

(* Theorem: 1 < n /\ 1 < k ==> !c. ZN_poly_intro n k c = (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k)) *)
(* Proof:
   Note Ring (ZN n)                       by ZN_ring, 0 < n
    and (ZN n).prod.id <> (ZN n).sum.id   by ZN_ids_alt, 1 < n

     ZN_poly_intro n k c
   = poly_intro (ZN n) k n (x+ n c)                    by ZN_poly_intro_eqn, 1 < k, 1 < n
   = (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k))  by poly_intro_X_add_c, Ring (ZN n)
*)
val ZN_poly_intro_thm = store_thm(
  "ZN_poly_intro_thm",
  ``!n k. 1 < n /\ 1 < k ==> !c. ZN_poly_intro n k c = (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k))``,
  rpt strip_tac >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `(ZN n).prod.id <> (ZN n).sum.id` by rw[ZN_ids_alt] >>
  metis_tac[ZN_poly_intro_eqn, poly_intro_X_add_c, ONE_LT_POS]);

(* Theorem: 1 < n /\ 1 < k ==> !m. ZN_poly_intro_range n k m = poly_intro_checks n k m *)
(* Proof:
     ZN_poly_intro_range n k m
   = unity_mod_intro_range (ZN n) k n m   by ZN_poly_intro_range_alt, 1 < n, 0 < k
   = poly_intro_checks n k m              by unity_mod_intro_range_eqn, 1 < n, 1 < k
*)
val ZN_poly_intro_range_eqn = store_thm(
  "ZN_poly_intro_range_eqn",
  ``!n k. 1 < n /\ 1 < k ==> !m. ZN_poly_intro_range n k m = poly_intro_checks n k m``,
  metis_tac[ZN_poly_intro_range_alt, unity_mod_intro_range_eqn, ONE_LT_POS]);

(* Theorem: (aks_param n = good k) /\ power_free n ==>
            (prime n = ZN_poly_intro_range n k (sqrt_compute (phi_compute k) * ulog n)) *)
(* Proof:
   With (aks_param n = good k) /\ power_free n,
   Note n <> 0, n <> 1               by aks_param_0, aks_param_1
     so 1 < n                        by n <> 0, n <> 1
   Also 1 < k                        by aks_param_good

       prime n
     = !c. 0 < c /\ c <= SQRT (phi k) * ulog n ==> (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k)))
                                   by aks_param_good_for_prime
     = !c. 0 < c /\ c <= SQRT (phi k) * ulog n ==> ZN_poly_intro n k c    by ZN_poly_intro_thm, 1 < n, 1 < k
     = ZN_poly_intro_range n k (SQRT (phi k) * ulog n)                    by ZN_poly_intro_range_thm
     = ZN_poly_intro_range n k (sqrt_compute (phi_compute k) * ulog n)    by sqrt_compute_eqn, phi_compute_eqn
*)
val aks_param_good_for_prime_alt = store_thm(
  "aks_param_good_for_prime_alt",
  ``!n k. (aks_param n = good k) /\ power_free n ==>
          (prime n = ZN_poly_intro_range n k (sqrt_compute (phi_compute k) * ulog n))``,
  rpt strip_tac >>
  `!n k. good n <> nice k` by rw[] >>
  `n <> 0 /\ n <> 1` by metis_tac[aks_param_0, aks_param_1] >>
  `1 < n` by decide_tac >>
  `1 < k` by metis_tac[aks_param_good] >>
  metis_tac[aks_param_good_for_prime, ZN_poly_intro_thm, ZN_poly_intro_range_thm, sqrt_compute_eqn, phi_compute_eqn]);

(* Theorem: 1 < n /\ 1 < k ==>
    (valueOf (poly_introM n k c) <=> poly_intro (ZN n) k n (x+ n c)) *)
(* Proof:
     valueOf (poly_introM n k c)
   = unity_mod_intro (ZN n) k n c     by poly_introM_value, 0 < n
   = poly_intro (ZN n) k n (x+ n c)   by ZN_unity_mod_intro_eqn, 1 < k, 1 < n
*)
val poly_introM_value_alt = store_thm(
  "poly_introM_value_alt",
  ``!n k c. 1 < n /\ 1 < k ==>
    (valueOf (poly_introM n k c) <=> poly_intro (ZN n) k n (x+ n c))``,
  rw[poly_introM_value, ZN_unity_mod_intro_eqn]);

(* Theorem: 1 < n /\ 1 < k ==>
    (valueOf (poly_intro_rangeM n k c) <=> poly_intro_range (ZN n) k n c) *)
(* Proof:
     valueOf (poly_intro_rangeM n k c)
   = unity_mod_intro_range (ZN n) k n c   by poly_intro_rangeM_value, 0 < n
   = poly_intro_range (ZN n) k n c        by ZN_unity_mod_intro_range_eqn, 1 < k, 1 < n
*)
val poly_intro_rangeM_value_alt = store_thm(
  "poly_intro_rangeM_value_alt",
  ``!n k c. 1 < n /\ 1 < k ==>
    (valueOf (poly_intro_rangeM n k c) <=> poly_intro_range (ZN n) k n c)``,
  rw[poly_intro_rangeM_value, ZN_unity_mod_intro_range_eqn]);

(* ------------------------------------------------------------------------- *)
(* Correctness of AKS Computation                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: aks_compute n = aks n *)
(* Proof:
   If power_free n,
        aks_compute n
      = case aks_param n of
          nice j => j = n
        | good k => unity_mod_intro_range (ZN n) k n (sqrt_compute (phi_compute k) * (ulog n))
        | bad => F               by aks_compute_def
      = case aks_param n of
          nice j => j = n
        | good k => 1 < k /\ !c. 0 < c /\ c <= SQRT (phi k) * (ulog n) ==>
                             (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k)))
        | bad => F               by unity_mod_intro_range_eqn, sqrt_compute_eqn, phi_compute_eqn
                                    and 1 < k by aks_param_good, 1 < n by power_free_gt_1
      = case aks_param n of
          nice j => j = n
        | good k => !c. 0 < c /\ c <= SQRT (phi k) * (ulog n) ==>
                             (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k)))
        | bad => F               by 1 < k implied
      = aks n                    by aks_def
   If ~(power_free n),
      Then aks_compute n = F     by aks_compute_def, power_free_check_eqn
       and aks n = F             by aks_def
*)
val aks_compute_alt = store_thm(
  "aks_compute_alt",
  ``!n. aks_compute n = aks n``,
  rpt strip_tac >>
  Cases_on `power_free n` >| [
    rw_tac std_ss[aks_compute_def, aks_def, power_free_check_eqn] >>
    Cases_on `aks_param n` >-
    fs[] >-
   (rw_tac std_ss[] >>
    `1 < n` by rw[power_free_gt_1] >>
    metis_tac[aks_param_good, unity_mod_intro_range_eqn, sqrt_compute_eqn, phi_compute_eqn]) >>
    fs[],
    metis_tac[aks_compute_def, aks_def, power_free_check_eqn]
  ]);

(* Theorem: aks n = aks_compute n *)
(* Proof: by aks_compute_alt *)
val aks_compute_thm = store_thm(
  "aks_compute_thm",
  ``!n. aks n = aks_compute n``,
  rw[aks_compute_alt]);

(* Theorem: prime n = aks_compute n *)
(* Proof:
       prime n
   <=> aks n               by aks_thm
   <=> aks_compute n       by aks_compute_alt
*)
val aks_compute_eqn = store_thm(
  "aks_compute_eqn",
  ``!n. prime n = aks_compute n``,
  rw_tac std_ss[aks_thm, aks_compute_alt]);

(* Another major milestone theorem! *)

(* ------------------------------------------------------------------------- *)
(* AKS Algorithm (Direct Version)                                            *)
(* ------------------------------------------------------------------------- *)

(* Express AKS algorithm using direct polynomial modular computations in (ZN n). *)
val aks_algo_def = Define`
    aks_algo n <=> power_free_check n /\
       case aks_param n of     (* search for AKS parameter given n *)
         nice j => (j = n)     (* found j that will show n prime or composite directly *)
       | good k => ZN_poly_intro_range n k ((sqrt_compute (phi_compute k)) * (ulog n))
                               (* found k with m <= ordz k n, where m = (ulog n) ** 2 *)
         (* !c. 0 < c /\ c <= SQRT (phi k) * (LOG2 n + 1) ==> (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k)) *)
       | bad => F              (* impossible *)
`;

(*
> EVAL ``aks_algo 2``; --> T
> EVAL ``aks_algo 3``; --> T
> EVAL ``aks_algo 4``; --> F
> EVAL ``aks_algo 5``; --> T
> EVAL ``aks_algo 6``; --> F
> EVAL ``aks_algo 7``; --> T
> EVAL ``aks_algo 8``; --> F
> EVAL ``aks_algo 9``; --> F
> EVAL ``aks_algo 10``; --> F
> EVAL ``aks_algo 11``; --> T
> EVAL ``aks_algo 12``; --> F
> EVAL ``aks_algo 13``; --> T
> EVAL ``aks_algo 31``; --> T (a long time)

> time EVAL ``aks_algo 31``;
runtime: 37.2s,    gctime: 0.14086s,     systime: 0.18451s.
val it = |- aks_algo 31 <=> T: thm
> time EVAL ``aks_compute 31``;
runtime: 45.9s,    gctime: 0.15122s,     systime: 0.21741s.
val it = |- aks_compute 31 <=> T: thm
*)

(* Theorem: aks_algo n = aks n *)
(* Proof:
   If power_free n,
        aks_algo n
      = case aks_param n of
          nice j => j = n
        | good k => ZN_poly_intro_range n k (sqrt_compute (phi_compute k) * (ulog n))
        | bad => F               by aks_algo_def
      = case aks_param n of
          nice j => j = n
        | good k => unity_mod_intro_range (ZN n) k n (sqrt_compute (phi_compute k) * (ulog n))
        | bad => F               by ZN_poly_intro_range_alt, 0 < k by 1 < k, 1 < k by aks_param_good
      = case aks_param n of
          nice j => j = n
        | good k => 1 < k /\ !c. 0 < c /\ c <= SQRT (phi k) * (ulog n) ==>
                             (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k)))
        | bad => F               by unity_mod_intro_range_eqn, sqrt_compute_eqn,
                                    phi_compute_eqn, power_free_gt_1
      = case aks_param n of
          nice j => j = n
        | good k => !c. 0 < c /\ c <= SQRT (phi k) * (ulog n) ==>
                             (x+^ n c n == x^+ n c n) (pmod (ZN n) (x^- n k)))
        | bad => F               by 1 < k implied
      = aks n                    by aks_def
   If ~(power_free n),
      Then aks_algo n = F        by aks_algo_def, power_free_check_eqn
       and aks n = F             by aks_def
*)
val aks_algo_alt = store_thm(
  "aks_algo_alt",
  ``!n. aks_algo n = aks n``,
  rpt strip_tac >>
  Cases_on `power_free n` >| [
    rw_tac std_ss[aks_algo_def, aks_def, power_free_check_eqn] >>
    Cases_on `aks_param n` >-
    simp[] >-
   (rw_tac std_ss[] >>
    `1 < n` by rw[power_free_gt_1] >>
    `1 < n'` by metis_tac[aks_param_good] >>
    `0 < n'` by decide_tac >>
    metis_tac[ZN_poly_intro_range_alt, unity_mod_intro_range_eqn, sqrt_compute_eqn, phi_compute_eqn]) >>
    simp[],
    metis_tac[aks_algo_def, aks_def, power_free_check_eqn]
  ]);

(* Theorem: prime n = aks_algo n *)
(* Proof:
       prime n
   <=> aks n            by aks_thm
   <=> aks_algo n       by aks_algo_alt
*)
val aks_algo_eqn = store_thm(
  "aks_algo_eqn",
  ``!n. prime n = aks_algo n``,
  rw_tac std_ss[aks_thm, aks_algo_alt]);

(* Another major milestone theorem, easy! *)

(* ------------------------------------------------------------------------- *)
(* Another Story                                                             *)
(* ------------------------------------------------------------------------- *)

(*
Something like this would be good:
   prime n = power_free n /\ aks_checks n

If part: prime n ==> power_free n /\ aks_checks n

Only-if part: power_free n /\ aks_checks n ==> prime n
aks_checks n ==> aks_criteria n ==> ?p e. prime p /\ (n = p ** e)
power_free n /\ ?p e. prime p /\ (n = p ** e) ==> (n = p), hence prime n.

Currently,
aks_main_theorem  |- !n. prime n <=> power_free n /\ ?k. aks_checks n k
aks_when_prime    |- !n. prime n ==> ?k. aks_checks n k
aks_checks_gives_aks_criteria
                  |- !n k. k < n /\ aks_checks n k ==> ?p. prime p /\ aks_criteria (ZN p) n k
aks_main_punch    |- !r. FiniteField r /\ (CARD R = char r) ==>
                     !n k. 1 < n /\ aks_criteria r n k ==> perfect_power n (char r)
aks_main_punch |> ISPEC ``ZN p``;
                  |- FiniteField (ZN p) /\ (CARD (ZN p).carrier = char (ZN p)) ==>
                     !n k. 1 < n /\ aks_criteria (ZN p) n k ==> perfect_power n (char (ZN p))

However, aks_checks is something computable, but not the actual computation.
aks_checks_alt    |- !n k. aks_checks n k <=>
                           1 < k /\ ulog n ** 2 <= ordz k n /\
                           (!j. 1 < j /\ j <= k /\ j < n ==> ~(j divides n)) /\
                           (k < n ==> poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n))
The actual computation is in:
aks_def |- !n. aks n <=>
                        power_free n /\
                        case aks_param n of
                          nice j => j = n
                        | good k => poly_intro_checks n k (SQRT (phi k) * ulog n)
                        | bad => F
although I do have:
aks_alt  |- !n. aks n <=> power_free n /\ ?k. aks_checks n k
aks_thm  |- !n. prime n <=> aks n

Let aks_decide n = case aks_param n of ...
Then  power_free n /\ aks_decide n = power_free n /\ ?k. aks_checks n k
  or  aks_decide n = ?k. aks_checks n k          (actual computation to ideal computation)
If that k has: k < n, we can show:
      aks_decide n = ?p. prime p /\ aks_criteria (ZN p) n k  (actual computation to shifted criteria)

Try this:
- rename aks_criteria  as aks_field_criteria
- introduce               aks_ring_criteria
- see if  aks_criteria -> aks_ring_criteria
- perhaps old way:  n -> ?k. aks_checks k -> ?k. aks_ring_criteria (ZN n) n k
                                          -> ?p. prime p /\aks_field_criteria (ZN p) n k
- perhaps new way:  n -> aks_decide n -> ?k. aks_ring_criteria (ZN n) n k
                                      -> ?p. prime p /\aks_field_criteria (ZN p) n k
- and  aks_compute n = aks_decide n
*)

(* Define AKS criteria in a ring *)
val aks_ring_criteria_def = Define`
    aks_ring_criteria (r:'a ring) n k <=>
        0 < n /\ 1 < k /\ k < char r /\ ulog n ** 2 <= ordz k n /\
        poly_intro_range r k n (SQRT (phi k) * ulog n)
`;
(* Note: r is supposed to be (ZN n) *)

(* Define AKS criteria in a field *)
val aks_field_criteria_def = Define`
    aks_field_criteria (r:'a field) n k <=>
        0 < n /\ 0 < k /\ 1 < ordz k (char r) /\
        char r divides n /\ k < char r /\ ulog n ** 2 <= ordz k n /\
        poly_intro_range r k n (SQRT (phi k) * ulog n)
`;
(* Note: r is supposed to be (ZN p) *)
(* 1 < ordz k (char r) gives 1 < k, by ZN_order_mod_1 *)

(* Theorem: aks_field_criteria r n k = aks_criteria r n k *)
(* Proof: by aks_field_criteria_def, aks_criteria_def *)
val aks_field_criteria_alt = store_thm(
  "aks_field_criteria_alt",
  ``!(r:'a field) n k. aks_field_criteria r n k = aks_criteria r n k``,
  rw_tac std_ss[aks_field_criteria_def, aks_criteria_def]);

(* Define aks_decide *)
val aks_decide_def = Define`
    aks_decide n <=>
    case aks_param n of
      nice j => j = n
    | good k => poly_intro_checks n k (SQRT (phi k) * ulog n)
    | bad => F
`;

(* Theorem: aks_decide n = case aks_param n of
                             nice j => j = n
                           | good k => poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n)
                           | bad => F *)
(* Proof:
   By aks_decide_def, this is to show:
   (case aks_param n of nice j => j = n | good k => poly_intro_checks n k (SQRT (phi k) * ulog n)| bad => F) =
   (case aks_param n of nice j => j = n | good k => poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n)| bad => F)
   If aks_param n = nice j, true
   If aks_param n = good k,
      If n = 0 \/ n = 1,
         aks_param n = nice n <> good k     by aks_param_0, aks_param_1
      Otherwise, 1 < n,
         so 1 < k                           by aks_param_good
        and k < n                           by aks_param_good_lt, 1 < n
        ==> poly_intro_checks n k m
          = poly_intro_range (ZN n) k n m   by ZN_intro_range_eqn, 0 < k /\ 0 < n
   If aks_param n = bad, both false.
*)
val aks_decide_alt = store_thm(
  "aks_decide_alt",
  ``!n. aks_decide n <=>
       case aks_param n of
         nice j => j = n
       | good k => poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n)
       | bad => F``,
  rpt strip_tac >>
  `(case aks_param n of nice j => j = n | good k => poly_intro_checks n k (SQRT (phi k) * ulog n)| bad => F) =
    (case aks_param n of nice j => j = n | good k => poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n)| bad => F)` suffices_by rw_tac std_ss[aks_decide_def] >>
  Cases_on `aks_param n` >-
  rw_tac std_ss[] >-
 (Cases_on `n <= 1` >| [
    `aks_param n = nice n` by metis_tac[aks_param_0, aks_param_1, LE_ONE] >>
    `!n k. good n <> nice k` by rw[] >>
    metis_tac[],
    `1 < n` by decide_tac >>
    `1 < n' /\ n' < n` by metis_tac[aks_param_good, aks_param_good_lt] >>
    `0 < n' /\ 0 < n` by decide_tac >>
    rw_tac std_ss[ZN_intro_range_eqn]
  ]) >>
  rw_tac std_ss[]);

(* Theorem: aks n <=> power_free n /\ aks_decide n *)
(* Proof: by aks_def, aks_decide_def *)
val aks_by_decide = store_thm(
  "aks_by_decide",
  ``!n. aks n <=> power_free n /\ aks_decide n``,
  rw[aks_def, aks_decide_def]);

(*
Still only indirect, no direct: ZN_poly_intro  to poly_intro (ZN n)
ZN_poly_intro_range_alt   |- !m k. 1 < m /\ 0 < k ==> !n. ZN_poly_intro_range m k n <=> unity_mod_intro_range (ZN m) k m n
unity_mod_intro_range_alt |- !r. Ring r /\ #1 <> #0 ==> !k n. 1 < k /\ 0 < n ==> !m. unity_mod_intro_range r k n m <=> poly_intro_range r k n m
Only:
ZN_poly_intro_range_eqn   |- !n k. 1 < n /\ 1 < k ==> !m. ZN_poly_intro_range n k m <=> poly_intro_checks n k m
where
ZN_poly_intro_range_thm  |- !m k n. ZN_poly_intro_range m k n <=> !c. 0 < c /\ c <= n ==> ZN_poly_intro m k c
ZN_poly_intro_def  |- !m k c. ZN_poly_intro m k c <=> (ZN_poly_monomial m k c **z m = ZN_poly_special m k m c)

So far:
1 < n           OK
power_free n    OK
aks_decide n -- by definition,
      nice j => j = n
    | good k => poly_intro_checks n k (SQRT (phi k) * ulog n)
by aks_decide_alt
         nice j => j = n
       | good k => poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n)
suppose to have: aks_ring_criteria (ZN n) n k
suppose to have: aks_field_criteria (ZN p) n k
aks_main_punch |> ISPEC ``ZN p``;
                  |- FiniteField (ZN p) /\ (CARD (ZN p).carrier = char (ZN p)) ==>
                     !n k. 1 < n /\ aks_criteria (ZN p) n k ==> perfect_power n (char (ZN p))
therefore n = p, a prime.
*)

(* Theorem: (aks_param n = good k) ==>
            (poly_intro_checks n k (SQRT (phi k) * ulog n) = aks_ring_criteria (ZN n) n k) *)
(* Proof:
   Note 1 < n /\ 1 < k /\ k < n                 by aks_param_good_range
     so char (ZN n) = n                         by ZN_char, 0 < n
    and !j. 1 < j /\ j <= k ==> ~(j divides n)  by aks_param_good, 1 < k
    and ulog n ** 2 <= ordz k n                 by aks_param_good, EXP_2
    and !m. poly_intro_checks n k m
          = poly_intro_range (ZN n) k n m       by ZN_intro_range_eqn, 0 < k /\ k < n
    ==> aks_ring_criteria (ZN n) n k            by aks_ring_criteria_def
    The converse is true                        by aks_ring_criteria_def
*)
val aks_param_good_gives_checks_eq_ring_criteria = store_thm(
  "aks_param_good_gives_checks_eq_ring_criteria",
  ``!n k. (aks_param n = good k) ==>
         (poly_intro_checks n k (SQRT (phi k) * ulog n) = aks_ring_criteria (ZN n) n k)``,
  rpt strip_tac >>
  `1 < n /\ 1 < k /\ k < n` by metis_tac[aks_param_good_range] >>
  `char (ZN n) = n` by rw[ZN_char] >>
  `!j. 1 < j /\ j <= k ==> ~(j divides n)` by rw_tac std_ss[aks_param_good] >>
  `ulog n ** 2 <= ordz k n` by rw_tac std_ss[aks_param_good, EXP_2] >>
  `0 < k /\ 0 < n` by decide_tac >>
  rw_tac std_ss[aks_ring_criteria_def, ZN_intro_range_eqn]);

(* Theorem: aks_decide n =
            case aks_param n of
              nice j => j = n
            | good k => aks_ring_criteria (ZN n) n k
            | bad => F *)
(* Proof:
   By aks_decide_def, this is to show:
    (case aks_param n of nice j => j = n | good k => poly_intro_checks n k (SQRT (phi k) * ulog n)| bad => F) =
    (case aks_param n of nice j => j = n | good k => aks_ring_criteria (ZN n) n k| bad => F)
   If aks_param n = nice j, true
   If aks_param n = good k, true            by aks_param_good_gives_checks_eq_ring_criteria
   If aks_param n = bad, both false.
*)
val aks_decide_meets_ring_criteria = store_thm(
  "aks_decide_meets_ring_criteria",
  ``!n. aks_decide n <=>
       case aks_param n of
         nice j => j = n
       | good k => aks_ring_criteria (ZN n) n k
       | bad => F
``,
  rpt strip_tac >>
  `(case aks_param n of nice j => j = n | good k => poly_intro_checks n k (SQRT (phi k) * ulog n)| bad => F) =
    (case aks_param n of nice j => j = n | good k => aks_ring_criteria (ZN n) n k| bad => F)` suffices_by rw_tac std_ss[aks_decide_def] >>
  Cases_on `aks_param n` >-
  rw_tac std_ss[] >-
  rw_tac std_ss[aks_param_good_gives_checks_eq_ring_criteria] >>
  rw_tac std_ss[]);

(* For old version *)

(* Theorem: aks_decide n =
            case aks_param n of nice j => j = n | good k => 1 < n /\ k < n /\ aks_checks n k | bad => F *)
(* Proof:
   By aks_decide_def, this is to show:
    (case aks_param n of nice j => j = n | good k => poly_intro_checks n k (SQRT (phi k) * ulog n)| bad => F) =
    (case aks_param n of nice j => j = n | good k => 1 < n /\ k < n /\ aks_checks n k| bad => F)
   If aks_param n = nice j, true
   If aks_param n = good k, true    by aks_param_good_gives_checks_eq_checks
   If aks_param n = bad, both false.
*)
val aks_decide_meets_checks = store_thm(
  "aks_decide_meets_checks",
  ``!n. aks_decide n <=>
       case aks_param n of
         nice j => j = n
       | good k => 1 < n /\ k < n /\ aks_checks n k
       | bad => F
``,
  rpt strip_tac >>
  `(case aks_param n of nice j => j = n | good k => poly_intro_checks n k (SQRT (phi k) * ulog n)| bad => F) =
    (case aks_param n of nice j => j = n | good k => 1 < n /\ k < n /\ aks_checks n k| bad => F)` suffices_by rw_tac std_ss[aks_decide_def] >>
  Cases_on `aks_param n` >-
  rw_tac std_ss[] >-
  rw_tac std_ss[aks_param_good_gives_checks_eq_checks] >>
  rw_tac std_ss[]);

(* Now follows with old: aks_checks_gives_aks_criteria to bypass aks_checks, which is a bit ugly. *)

(* Theorem: (aks_param n = good k) /\ poly_intro_checks n k (SQRT (phi k) * ulog n) ==>
            ?p. prime p /\ aks_criteria (ZN p) n k *)
(* Proof: by aks_param_good_gives_checks_eq_checks, aks_checks_gives_aks_criteria *)
val aks_param_good_with_checks_implies_criteria = store_thm(
  "aks_param_good_with_checks_implies_criteria",
  ``!n k. (aks_param n = good k) /\ poly_intro_checks n k (SQRT (phi k) * ulog n) ==>
   ?p. prime p /\ aks_criteria (ZN p) n k``,
  metis_tac[aks_param_good_gives_checks_eq_checks, aks_checks_gives_aks_criteria]);

(* Theorem: aks_decide n ==>
            case aks_param n of
              nice j => j = n
            | good k => ?p. prime p /\ aks_criteria (ZN p) n k
            | bad => F *)
(* Proof:
   By aks_decide_def,
   If aks_param n = nice j, true
   If aks_param n = good k, true    by aks_param_good_with_checks_implies_criteria
   If aks_param n = bad, both false.
*)
val aks_decide_implies_criteria = store_thm(
  "aks_decide_implies_criteria",
  ``!n. aks_decide n ==>
       case aks_param n of
         nice j => j = n
       | good k => ?p. prime p /\ aks_criteria (ZN p) n k
       | bad => F
``,
  rw_tac std_ss[aks_decide_def] >>
  Cases_on `aks_param n` >-
  fs[] >-
  fs[aks_param_good_with_checks_implies_criteria] >>
  fs[]);

(* Theorem: prime n ==> aks_decide n *)
(* Proof:
   By aks_decide_def,
   If aks_param n = nice j, true by aks_param_nice_for_prime, ONE_LT_PRIME
   If aks_param n = good k, true by aks_param_good_for_prime, prime_is_power_free
   If aks_param n = bad,    true by aks_param_exists, no bad
*)
val aks_decide_prime = store_thm(
  "aks_decide_prime",
  ``!n. prime n ==> aks_decide n``,
  rw_tac std_ss[aks_decide_def] >>
  Cases_on `aks_param n` >| [
    rw_tac std_ss[] >>
    rw[GSYM aks_param_nice_for_prime, ONE_LT_PRIME],
    rw_tac std_ss[] >>
    metis_tac[aks_param_good_for_prime, prime_is_power_free],
    metis_tac[aks_param_exists]
  ]);

(* Theorem: prime n ==> power_free n /\ aks_decide n *)
(* Proof:
   This is to show:
   (1) prime n ==> power_free n, true   by prime_is_power_free
   (2) prime n ==> aks_decide n, true   by aks_decide_prime
*)
val aks_thm_easy = store_thm(
  "aks_thm_easy",
  ``!n. prime n ==> power_free n /\ aks_decide n``,
  rpt strip_tac >-
  rw[prime_is_power_free] >>
  rw[aks_decide_prime]);

(* Theorem: power_free n /\ aks_decide n ==> prime n *)
(* Proof:
   By aks_decide_def,
   Note power_free n ==> 1 < n      by power_free_gt_1
   If aks_param n = nice j, true    by aks_param_nice_for_prime, 1 < n
   If aks_param n = good k, true    by aks_param_good_for_prime
   If aks_param n = bad, true       by aks_param_exists, no bad
*)
val aks_thm_hard = store_thm(
  "aks_thm_hard",
  ``!n. power_free n /\ aks_decide n ==> prime n``,
  rw_tac std_ss[aks_decide_def] >>
  `1 < n` by rw[power_free_gt_1] >>
  Cases_on `aks_param n` >| [
    rw_tac std_ss[] >>
    `n' = n` by fs[] >>
    metis_tac[aks_param_nice_for_prime],
    rw_tac std_ss[] >>
    `poly_intro_checks n n' (SQRT (phi n') * ulog n)` by fs[] >>
    metis_tac[aks_param_good_for_prime],
    metis_tac[aks_param_exists]
  ]);

(* Theorem: prime n = (power_free n /\ aks_decide n) *)
(* Proof: by aks_thm_easy, aks_thm_hard *)
val aks_thm_iff = store_thm(
  "aks_thm_iff",
  ``!n. prime n = (power_free n /\ aks_decide n)``,
  metis_tac[aks_thm_easy, aks_thm_hard]);

(* Can the critical theorems be proved without the big-guns?
aks_param_nice_for_prime     by aks_param_nice_coprime_all
aks_param_good_for_prime     by AKS_main_ulog_8b (can this be done by aks_main_theorem?)
*)

(* Another proof of aks_param_good_for_prime:
val it = |- !n k. (aks_param n = good k) /\ power_free n ==>
                  (prime n <=> poly_intro_checks n k (SQRT (phi k) * ulog n)): thm
*)

(* Theorem: power_free n /\ (aks_param n = good k) ==> (prime n = poly_intro_checks n k (SQRT (phi k) * ulog n)) *)
(* Proof:
   Let m = SQRT (phi k) * (ulog n).
   Note 1 < n /\ 1 < k /\ k < n                     by aks_param_good_range

   If part: prime n ==> poly_intro_checks n k m
      Note poly_intro (ZN n) k n (x+ n c)           by ZN_intro_range_by_prime, 0 < k
      Thus poly_intro_checks n k m                  by ZN_intro_eqn, 1 < k, k < n

   Only-if part: poly_intro_checks n k m ==> prime n
      Note ?p. prime p /\ aks_criteria (ZN p) n k   by aks_param_good_with_checks_implies_criteria
       Now FiniteField (ZN p)                       by ZN_finite_field, prime p
       and CARD (ZN p).carrier = p                  by ZN_card
       and char (ZN p) = p                          by ZN_char, PRIME_POS
       ==> perfect_power n p                        by aks_main_punch, 1 < n
       ==> n = p, hence prime n                     by power_free_perfect_power
*)
val aks_param_good_for_prime_check = store_thm(
  "aks_param_good_for_prime_check",
  ``!n k. power_free n /\ (aks_param n = good k) ==>
         (prime n = poly_intro_checks n k (SQRT (phi k) * ulog n))``,
  rpt strip_tac >>
  qabbrev_tac `m = SQRT (phi k) * (ulog n)` >>
  `1 < n /\ 1 < k /\ k < n` by metis_tac[aks_param_good_range] >>
  rw_tac std_ss[EQ_IMP_THM] >-
  metis_tac[ZN_intro_range_by_prime, ZN_intro_eqn, ONE_LT_POS] >>
  `?p. prime p /\ aks_criteria (ZN p) n k` by rw[aks_param_good_with_checks_implies_criteria] >>
  `FiniteField (ZN p)` by rw[ZN_finite_field] >>
  `CARD (ZN p).carrier = p` by rw[ZN_card] >>
  `char (ZN p) = p` by rw[ZN_char, PRIME_POS] >>
  metis_tac[aks_main_punch, power_free_perfect_power]);

(* This is the proof I want! -- another milestone. *)

(* Theorem: power_free n /\ (aks_param n = good k) ==> (prime n = poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n)) *)
(* Proof:
   Let m = SQRT (phi k) * ulog n.
   Note 1 < k /\ k < n                     by aks_param_good_range
     or 0 < k /\ k < n                     by arithmetic
   Thus prime n = poly_intro_checks n k m  by aks_param_good_for_prime_check, ZN_intro_range_eqn
*)
val aks_param_good_for_prime_range = store_thm(
  "aks_param_good_for_prime_range",
  ``!n k. power_free n /\ (aks_param n = good k) ==>
         (prime n = poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n))``,
  metis_tac[aks_param_good_for_prime_check, aks_param_good_range, ZN_intro_range_eqn, ONE_LT_POS]);

(* Theorem: power_free n /\ (aks_param n = good k) ==> (prime n = poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n)) *)
(* Proof: by aks_param_good_for_prime_range. *)
val aks_param_good_with_range_prime = store_thm(
  "aks_param_good_with_range_prime",
  ``!n k. power_free n /\ (aks_param n = good k) /\
         poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n) ==> prime n``,
  metis_tac[aks_param_good_for_prime_range]);

(* Theorem variation *)
val aks_param_good_with_range_prime_alt = store_thm(
  "aks_param_good_with_range_prime_alt",
  ``!n k s. power_free n /\ (aks_param n = good k) /\ (s = SQRT (phi k) * ulog n) /\
           poly_intro_range (ZN n) k n s ==> prime n``,
  rw[aks_param_good_with_range_prime]);

(* Theorem: (aks_param n = good k) /\ poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n) ==>
            ?p. prime p /\ aks_criteria (ZN p) n k *)
(* Proof:
   Note 1 < k /\ k < n                          by aks_param_good_range
   Thus ?p. prime p /\ aks_criteria (ZN p) n k  by aks_param_good_with_checks_implies_criteria,
                                                   ZN_intro_range_eqn
*)
val aks_param_good_with_range_implies_criteria = store_thm(
  "aks_param_good_with_range_implies_criteria",
  ``!n k. (aks_param n = good k) /\ poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n) ==>
         ?p. prime p /\ aks_criteria (ZN p) n k``,
  metis_tac[aks_param_good_with_checks_implies_criteria, aks_param_good_range, ZN_intro_range_eqn, ONE_LT_POS]);

(* Theorem: (aks_param n = good k) ==>
        !m. poly_intro_range (ZN n) k n m <=> poly_intro_checks n k m *)
(* Proof:
   Note 1 < k /\ k < n    by aks_param_good_coprime_order
     so 0 < k             by 1 < k
   The result follows     by ZN_intro_range_eqn
*)
val aks_param_good_poly_intro_range = store_thm(
  "aks_param_good_poly_intro_range",
  ``!n k. (aks_param n = good k) ==>
   !m. poly_intro_range (ZN n) k n m <=> poly_intro_checks n k m``,
  rpt strip_tac >>
  `1 < k /\ k < n` by metis_tac[aks_param_good_coprime_order] >>
  `0 < k` by decide_tac >>
  rw[ZN_intro_range_eqn]);

(* Theorem: aks n <=> power_free n /\
        case aks_param n of
           nice j => (j = n)
        | good k => poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n)
        | bad => F *)
(* Proof: by aks_def, aks_param_good_poly_intro_range *)
val aks_by_poly_intro_range = store_thm(
  "aks_by_poly_intro_range",
  ``!n. aks n <=> power_free n /\
        case aks_param n of
           nice j => (j = n)
        | good k => poly_intro_range (ZN n) k n (SQRT (phi k) * ulog n)
        | bad => F``,
  rpt strip_tac >>
  Cases_on `aks_param n` >-
  rw[aks_def] >-
  rw[aks_def, aks_param_good_poly_intro_range] >>
  rw[aks_def]);

(* ------------------------------------------------------------------------- *)
(* Variations of AKS algorithm                                               *)
(* ------------------------------------------------------------------------- *)

(*
These variations concerns the choice of the upper limit
in polynomial introspective checks of the AKS algorithm.
*)

(* Theorem: (!k. 0 < k /\ (ulog n) ** 2 <= ordz k n ==> SQRT (phi k) * ulog n <= limit k n) ==>
            (prime n <=> power_free n /\
                         case aks_param n of
                           nice j => j = n
                         | good k => poly_intro_checks n k (limit k n)
                         | bad => F) *)
(* Proof:
   If part: prime n ==> power_free n /\ case aks_param n of ...
      The subgoals are:
      (1) prime n ==> power_free n, true            by prime_is_power_free
      (2) prime n ==> case aks_param n of ...
          Note 1 < n                                by ONE_LT_PRIME

          Consider cases of aks_param n, this is to show:
          (1) aks_param n = nice n' ==> n' = n
              By contradiction, suppose n' <> n.
              Note 1 < n' /\ n' divides n           by aks_param_nice, 1 < n
               ==> n' = 1, divisor of prime         by prime_def, prime n
               ==> 1 < 1                            by above
              This is a contradiction.

          (2) aks_param n = good n' ==> poly_intro_checks n n' (SQRT n' * ulog n)
              Note 1 < n'                           by aks_param_good
                so 0 < n'                           by arithmetic
              This is true                          by ZN_intro_range_by_prime_alt, 0 < n'

          (3) aks_param n = bad ==> F
              Note aks_param n <> bad               by aks_param_exists
              This is a contradiction, hence true.

   Only-if part: power_free n /\ case aks_param n of ... ==> prime n
      Note 1 < n                                       by power_free_gt_1
      Conside cases of aks_param n, this is to show:
      (1) aks_param n = nice n' ==> prime n
          Note n' = n                                  by case of nice n'
           ==> prime n                                 by aks_param_nice_for_prime, 1 < n

      (2) aks_param n = good n' ==> prime n
          Let m = limit n' n, s = SQRT (phi n') * (ulog n),
          Note 0 < n' /\ SQ (ulog n) <= ordz n' n      by aks_param_good
           ==> s <= m                                  by limit implication condition
          Thus poly_intro_checks n n' m                by case of good n'
           ==> poly_intro_checks n n' s                by LESS_EQ_TRANS
           ==> prime n                                 by aks_param_good_for_prime

      (3) aks_param n = bad ==> prime n
          The premise is false, hence true             by aks_param_exists
*)
val aks_variation_thm = store_thm(
  "aks_variation_thm",
  ``!n limit. (!k. 0 < k /\ (ulog n) ** 2 <= ordz k n ==>
                  SQRT (phi k) * ulog n <= limit k n) ==>
         (prime n <=> power_free n /\
          case aks_param n of
            nice j => j = n
          | good k => poly_intro_checks n k (limit k n)
          | bad => F)``,
  rw_tac std_ss[EQ_IMP_THM] >-
  rw[prime_is_power_free] >-
 (Cases_on `aks_param n` >| [
    simp[] >>
    spose_not_then strip_assume_tac >>
    `1 < n` by rw[ONE_LT_PRIME] >>
    `1 < n' /\ n' divides n` by metis_tac[aks_param_nice] >>
    `n' = 1` by metis_tac[prime_def] >>
    decide_tac,
    rw_tac std_ss[] >>
    `0 < n'` by metis_tac[aks_param_good, ONE_LT_POS] >>
    metis_tac[ZN_intro_range_by_prime_alt],
    metis_tac[aks_param_exists]
  ]) >>
  `1 < n` by rw[power_free_gt_1] >>
  Cases_on `aks_param n` >| [
    `n' = n` by fs[] >>
    metis_tac[aks_param_nice_for_prime],
    qabbrev_tac `s = SQRT (phi n') * (ulog n)` >>
    qabbrev_tac `m = limit n' n` >>
    `0 < n' /\ (ulog n) ** 2 <= ordz n' n` by metis_tac[aks_param_good, ONE_LT_POS, EXP_2] >>
    `s <= m` by rw[Abbr`s`, Abbr`m`] >>
    `poly_intro_checks n n' s` by fs[] >>
    metis_tac[aks_param_good_for_prime],
    metis_tac[aks_param_exists]
  ]);

(* Theorem: prime n <=> power_free n /\
            case aks_param n of
              nice j => j = n
            | good k => poly_intro_checks n k (SQRT k * ulog n)
            | bad => F *)

(* Proof:
   Let limit = \k n. SQRT k * ulog n.
   Note !k. phi k <= k                       by phi_le
     so !k. SQRT (phi k) <= SQRT k           by SQRT_LE
     or !k. SQRT (phi k) * ulog n <= f k n   by LESS_MONO_MULT
   The result follows                        by aks_variation_thm
*)
val aks_variation_1 = store_thm(
  "aks_variation_1",
  ``!n. prime n <=> power_free n /\
                   case aks_param n of
                     nice j => j = n
                   | good k => poly_intro_checks n k (SQRT k * ulog n)
                   | bad => F``,
  rw_tac std_ss[aks_variation_thm, phi_le, SQRT_LE]);

(* Theorem: prime n <=> power_free n /\
            case aks_param n of
              nice j => j = n
            | good k => poly_intro_checks n k (SQRT k * ulog n)
            | bad => F *)
(* Proof:
   Let limit = \k n. k * ulog n.
   Note !k. phi k <= k                           by phi_le
     so !k. SQRT (phi k) <= SQRT k               by SQRT_LE
    but !k. SQRT k <= k                          by SQRT_LE_SELF
     so !k. SQRT (phi k) <= k                    by LESS_EQ_TRANS
     or !k. SQRT (phi k) * ulog n <= k * ulog n  by LESS_MONO_MULT
                                   =limit k n
   The result follows                            by aks_variation_thm
*)
val aks_variation_2 = store_thm(
  "aks_variation_2",
  ``!n. prime n <=> power_free n /\
                   case aks_param n of
                     nice j => j = n
                   | good k => poly_intro_checks n k (k * ulog n)
                   | bad => F``,
  rw_tac std_ss[] >>
  qabbrev_tac `limit = \k n. k * ulog n` >>
  `!k. SQRT (phi k) * ulog n <= limit k n` by
  (rpt strip_tac >>
  rw_tac std_ss[Abbr`limit`] >>
  `SQRT (phi k) <= SQRT k` by rw[phi_le, SQRT_LE] >>
  `SQRT k <= k` by rw[SQRT_LE_SELF] >>
  decide_tac) >>
  assume_tac aks_variation_thm >>
  first_x_assum (qspecl_then [`n`, `limit`] strip_assume_tac) >>
  fs[]);

(* Theorem: prime n <=> power_free n /\
            case aks_param n of
              nice j => j = n
            | good k => poly_intro_checks n k k
            | bad => F *)
(* Proof:
   Let limit = \k n. k.
   Claim: !k. 0 < k /\ (ulog n) ** 2 <= ordz k n ==> SQRT (phi k) * ulog n <= limit k n
   Proof: Note ordz k n <= k                 by ZN_order_le, 0 < k
          Thus        ulog n ** 2 <= k       by EXP_2, SQ (ulog n) <= ordz k n
            or SQRT (ulog n ** 2) <= SQRT k  by SQRT_LE
            or             ulog n <= SQRT k  by SQRT_EXP_2, [1]
          Note        phi k <= k             by phi_le
          Thus SQRT (phi k) <= SQRT k        by SQRT_LE, [2]
          Overall,
          SQRT (phi k) * ulog n <= SQ (SQRT k)       by LE_MONO_MULT2, [1], [2]
          and                      SQ (SQRT k) <= k  by SQ_SQRT_LE
          SQRT (phi k) * ulog n <= k = limit k n     by LESS_EQ_TRANS

   The result follows                        by aks_variation_thm, claim.
*)
val aks_variation_3 = store_thm(
  "aks_variation_3",
  ``!n. prime n <=> power_free n /\
                   case aks_param n of
                     nice j => j = n
                   | good k => poly_intro_checks n k k
                   | bad => F``,
  rw_tac std_ss[] >>
  qabbrev_tac `limit = \k:num n:num. k` >>
  `!k. 0 < k /\ (ulog n) ** 2 <= ordz k n ==>
           SQRT (phi k) * ulog n <= limit k n` by
  (rpt strip_tac >>
  rw_tac std_ss[Abbr`limit`] >>
  `ordz k n <= k` by rw[ZN_order_le] >>
  `ulog n ** 2 <= k` by decide_tac >>
  `ulog n <= SQRT k` by metis_tac[SQRT_EXP_2, SQRT_LE] >>
  `SQRT (phi k) <= SQRT k` by rw[phi_le, SQRT_LE] >>
  `SQRT (phi k) * ulog n <= SQRT k * SQRT k` by rw[LE_MONO_MULT2] >>
  `SQ (SQRT k) <= k` by rw[SQ_SQRT_LE] >>
  decide_tac) >>
  assume_tac aks_variation_thm >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  fs[Abbr`limit`]);

(* Theorem: aks0 n <=> power_free_test n /\
                 case param n of
                   nice j => j = n
                 | good k => poly_intro_checks n k k
                 | bad => F *)
(* Proof:
   By aks0_def, and work on the case (good k).
   To apply unity_mod_intro_range_eqn,
   need 1 < n, provided        by power_free_gt_1
    and 1 < k, provided        by param_good_range
*)
val aks0_eqn = store_thm(
  "aks0_eqn",
  ``!n. aks0 n <=> power_free_test n /\
                  case param n of
                    nice j => j = n
                  | good k => poly_intro_checks n k k
                  | bad => F``,
  rw_tac std_ss[aks0_def] >>
  (Cases_on `param n` >> rw_tac std_ss[]) >>
  metis_tac[power_free_gt_1, param_good_range, unity_mod_intro_range_eqn]);

(* Theorem: prime n <=> aks0 n *)
(* Proof:
   By aks0_alt, this is to show:
      prime n <=> power_free n /\
                  case aks_param n of
                    nice j => j = n
                  | good k => unity_mod_intro_range (ZN n) k n k
                  | bad => F

   Note prime n <=> power_free n /\
                  case aks_param n of
                    nice j => j = n
                  | good k => poly_intro_checks n k k
                  | bad => F                 by aks_variation_3

   If aks_param n = nice j, this is true.
   If aks_param n = bad, this is true.
   If aks_param n = good k,
      Then 1 < k                             by aks_param_good
       and 1 < n                             by power_free_gt_1
      Thus 1 < n /\ unity_mod_intro_range (ZN n) k n k
       <=> 1 < n /\ poly_intro_checks n k k  by unity_mod_intro_range_eqn
      Hence true.
*)
val aks0_thm = store_thm(
  "aks0_thm",
  ``!n. prime n <=> aks0 n``,
  rw[aks0_alt] >>
  assume_tac aks_variation_3 >>
  first_x_assum (qspec_then `n` strip_assume_tac) >>
  Cases_on `aks_param n` >-
  fs[] >-
 (`prime n <=> power_free n /\ poly_intro_checks n n' n'` by rw[] >>
  `prime n <=> power_free n /\ unity_mod_intro_range (ZN n) n' n n'` suffices_by rw[] >>
  `1 < n'` by metis_tac[aks_param_good] >>
  metis_tac[unity_mod_intro_range_eqn, power_free_gt_1]) >>
  fs[]);

(* This is really spectacular! *)

(* Theorem: aks0 n = aks n *)
(* Proof: by aks0_thm, aks_thm *)
val aks0_eq_aks = store_thm(
  "aks0_eq_aks",
  ``!n. aks0 n = aks n``,
  rw[GSYM aks0_thm, aks_thm]);

(* Theorem: valueOf(aksM n) = aks n *)
(* Proof: aksM_value, aks0_eq_aks *)
val aksM_value_alt = store_thm(
  "aksM_value_alt",
  ``!n. valueOf(aksM n) = aks n``,
  rw[aksM_value, aks0_eq_aks]);

(* Theorem: (valueOf (aksM n) <=> aks n) /\
            (stepsOf o aksM) IN big_O (\n. ulog n ** 21) *)
(* Proof: by aksM_value_alt, aksM_steps_big_O *)
val aksM_thm_alt = store_thm(
  "aksM_thm_alt",
  ``!n. (valueOf (aksM n) <=> aks n) /\ (stepsOf o aksM) IN big_O (\n. ulog n ** 21)``,
  metis_tac[aksM_value_alt, aksM_steps_big_O]);


(* ------------------------------------------------------------------------- *)
(* Terence Tao's Approach                                                    *)
(* ------------------------------------------------------------------------- *)

(*

Terence Tao's argument: his good r is my good k.
Let F be a field extension of F_p by a primitive r-th root of unity X,
thus F = F_p[X]/h(X) for some factor h(X) in F_p[X] of the r-th cyclotomic polynomial Phi_r(X).

Let G SUBSET F^* be the multiplicative group generated by the quantities X + a for introspective a's: 1 <= a <= A, where A = O(r (log n) ** O(1)).
Observe that z ** m = phi_m(z) for all z IN G.       <-- z is a polynomial.
phi_m is the ring homomorphism that sends X to X ** m.
i.e. phi_m (X + a) = X ** m + a, and introspective is: (X + a) ** m = phi_m (X + a).

Suppose that there are exactly t residue classes modulo r of the form (p^i (n/p)^j mod r) for i,j >= 0.
Thus t < r.

Upper bound on G: CARD G <= n ** sqrt(t)    by Pigeonhole collision giving m and m', and the polynomial z ** m - z ** m'.
Lower bound on G: 2 ** t < CARD G.          by A > 2 * r > 2 * t, and 2 ** t ways to pick the product P(X) of less than t of the quantities X + 1, ..., X + A, allowing repeititions.

Punch line:
Since n has order greater than (log n) ** 2 in (Z/rZ)^*,
t is at least (log n) ** 2, which gives 2 ** t > n ** sqrt(t), a contradiction.

*)

(* Given n, and a good k, construct a finite field for the AKS theory. *)
(* There is a prime factor p of n, this gives a finite field F_p to start with.
   The FiniteField r below will be F_p.
*)

(*
-- need to define a set-generated group, not subset_group.
The subset s does not form a group.
But the subset s generates a group.
-- a generated subset of a group is always a group
*)

(* ------------------------------------------------------------------------- *)
(* The Reduced Modular Set.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Defined the reduced set of p q by MOD k, where p is an introspective seed, q = n DIV p *)
(*
val reducePQ_def = Define`
    reducePQ (p:num) (q:num) (k:num) = {(p ** i * q ** j) MOD k | i IN univ(num) /\ j IN univ(num)}
`;
*)
val reducePQ_def = Define`
    reducePQ (p:num) (q:num) (k:num) = {(p ** i * q ** j) MOD k | 0 <= i /\ 0 <= j}
`;
(* Another presentation:
val reducePQ_def = Define`
    reducePQ (p:num) (q:num) (k:num) = {(p ** i * q ** j) MOD k | i, j | 0 <= i /\ 0 <= j}
`;
*)

(* The cardinality of reducePQ p q k.

For n = 10 = 2 * 5 = p * q, k = 7.

    5 ** 4 MOD 7 = 1
    ------------------------------------------------------------    +
    5 ** 3 MOD 7 = 6  6             5             3             |
    5 ** 2 MOD 7 = 4  4             1             2             |
    5 ** 1 MOD 7 = 5  5             3             6             |
    5 ** 0 MOD 7 = 1  1             2             4             |
                      1 =           2 =           4 =           |  1 =
                      2 ** 0 MOD 7  2 ** 1 MOD 7  2 ** 2 MOD 7  |  2 ** 3 MOD 7
    Therefore CARD (reducePQ 2 5 7) = CARD {1; 2; 3; 4; 5; 6} = 6

For n = 12 = 2 * 6 = p * q, k = 7.

    6 ** 2 MOD 7 = 1
    ------------------------------------------------------------    +
    6 ** 1 MOD 7 = 6  6             5             3             |
    6 ** 0 MOD 7 = 1  1             2             4             |
                      1 =           2 =           4 =           |  1 =
                      2 ** 0 MOD 7  2 ** 1 MOD 7  2 ** 2 MOD 7  |  2 ** 3 MOD 7
    Therefore CARD (reducePQ 2 6 7) = CARD {1; 2; 3; 4; 5; 6} = 6

For n = 10 = 2 * 5 = p * q, k = 6.

    5 ** 2 MOD 6 = 1
    ------------------------------------------------------------    +
    5 ** 1 MOD 6 = 5  5             4             2             |
    5 ** 0 MOD 6 = 1  1             2             4             |
                      1 =           2 =           4 =           |  2 =
                      2 ** 0 MOD 6  2 ** 1 MOD 6  2 ** 2 MOD 6  |  2 ** 3 MOD 6
    Therefore CARD (reducePQ 2 5 6) = CARD {1; 2; 4; 5} = 4
*)

(* Theorem: reducePQ p q k = IMAGE (\(i, j). (p ** i * q ** j) MOD k) (univ(num) CROSS univ(num)) *)
(* Proof: by reducePQ_def, IN_IMAGE, IN_CROSS. *)
val reducePQ_alt = store_thm(
  "reducePQ_alt",
  ``!p q k. reducePQ p q k = IMAGE (\(i, j). (p ** i * q ** j) MOD k) (univ(num) CROSS univ(num))``,
  rw[reducePQ_def, EXTENSION, EQ_IMP_THM] >| [
    qexists_tac `(i, j)` >>
    rw[],
    rw[pairTheory.UNCURRY] >>
    metis_tac[]
  ]);

(* Theorem: !x. x IN reducePQ p q k <=> ?i j. x = (p ** i * q ** j) MOD k *)
(* Proof: by reducePQ_def, IN_IMAGE *)
val reducePQ_element = store_thm(
  "reducePQ_element",
  ``!p q k. !x. x IN reducePQ p q k <=> ?i j. x = (p ** i * q ** j) MOD k``,
  rw[reducePQ_def]);

(* Theorem: 1 < k ==> 1 IN (reducePQ p q k) *)
(* Proof:
   Let e = (p ** 0 * q ** 0) MOD k.
   Then e IN (reducePQ p q k)         by reducePQ_element
    but e = (p ** 0 * q ** 0) MOD k
          = (1 * 1) MOD k             by EXP_0
          = 1 MOD k                   by MULT_RIGHT_1
*)
val reducePQ_has_one = store_thm(
  "reducePQ_has_one",
  ``!p q k. 1 MOD k IN (reducePQ p q k)``,
  rpt strip_tac >>
  qabbrev_tac `e = (p ** 0 * q ** 0) MOD k` >>
  `e IN (reducePQ p q k)` by metis_tac[reducePQ_element] >>
  `e = 1 MOD k` by rw[Abbr`e`] >>
  fs[]);

(* Theorem: (reducePQ p q k) <> {} *)
(* Proof:
   Note 1 MOD k IN (reducePQ p q k)   by reducePQ_has_one
    ==> (reducePQ p q k) <> {}        by MEMBER_NOT_EMPTY
*)
val reducePQ_nonempty = store_thm(
  "reducePQ_nonempty",
  ``!p q k. (reducePQ p q k) <> {}``,
  metis_tac[reducePQ_has_one, MEMBER_NOT_EMPTY]);

(* Theorem: 1 < k ==> 1 IN (reducePQ p q k) *)
(* Proof:
   Note 1 MOD k IN (reducePQ p q k)   by reducePQ_has_one
    and 1 MOD k = 1                   by ONE_MOD, 1 < k
*)
val reducePQ_has_1 = store_thm(
  "reducePQ_has_1",
  ``!p q k. 1 < k ==> 1 IN (reducePQ p q k)``,
  metis_tac[reducePQ_has_one, ONE_MOD]);

(* Theorem: 0 < k ==> (reducePQ p q k) SUBSET (count k) *)
(* Proof:
   Note !n. n MOD k < k                      by MOD_LESS, 0 < k
   Thus (reducePQ p q k) SUBSET (count k)    by reducePQ_def, SUBSET_DEF
*)
val reducePQ_subset = store_thm(
  "reducePQ_subset",
  ``!p q k. 0 < k ==> (reducePQ p q k) SUBSET (count k)``,
  rw[reducePQ_def, SUBSET_DEF] >>
  rw[MOD_LESS]);

(* Theorem: 0 < k ==> FINITE (reducePQ p q k) *)
(* Proof:
   Note (reducePQ p q k) SUBSET (count k)    by reducePQ_subset, 0 < k
    and FINITE (count k)                     by FINITE_COUNT
    ==> FINITE (reducePQ p q k)              by SUBSET_FINITE
*)
val reducePQ_finite = store_thm(
  "reducePQ_finite",
  ``!p q k. 0 < k ==> FINITE (reducePQ p q k)``,
  metis_tac[reducePQ_subset, SUBSET_FINITE, FINITE_COUNT]);

(* Theorem: 0 < k ==> CARD (reducePQ p q k) <= k *)
(* Proof:
   Note (reducePQ p q k) SUBSET (count k)         by reducePQ_subset, 0 < k
    and FINITE (count k)                          by FINITE_COUNT
    ==> CARD (reducePQ p q k) <= CARD (count k)   by CARD_SUBSET
     or CARD (reducePQ p q k) <= k                by CARD_COUNT
*)
val reducePQ_upper = store_thm(
  "reducePQ_upper",
  ``!p q k. 0 < k ==> CARD (reducePQ p q k) <= k``,
  metis_tac[reducePQ_subset, FINITE_COUNT, CARD_COUNT, CARD_SUBSET]);

(* This is the simplest estimate, unconditional. *)


(* ------------------------------------------------------------------------- *)
(* Monoids of Set N and M                                                    *)
(* ------------------------------------------------------------------------- *)

(* The monoid of set N *)
val monoidN_def = Define `
  monoidN (r:'a ring) (k:num) (s:num) = <| carrier := N; op := $*; id := 1 |>
`;

(* Theorem: 0 < k ==> Monoid (monoidN r k s) *)
(* Proof:
   Expanding by definitions, this is to show:
   (1) x IN N /\ y IN N ==> x * y IN N
       True by setN_closure.
   (2) x IN N /\ y IN N /\ z IN N ==> x * y * z = x * (y * z)
       True by MULT_ASSOC.
   (3) 1 IN N
       True by setN_has_1, 0 < k.
*)
val monoidN_monoid = store_thm(
  "monoidN_monoid",
  ``!(r:'a ring) (k s):num. Ring r /\ 0 < k ==> Monoid (monoidN r k s)``,
  rw_tac std_ss[Monoid_def, monoidN_def] >-
  rw[setN_closure] >-
  rw[MULT_ASSOC] >>
  rw[setN_has_1]);

(* The monoid of set M *)
val monoidM_def = Define `
  monoidM (r:'a ring) (k:num) (s:num) = <| carrier := M; op := (\x y. (x * y) MOD k); id := 1 |>
`;

(* Theorem: Properties of monoidM *)
(* Proof: by monoidM_def. *)
val monoidM_property = store_thm(
  "monoidM_property",
  ``!(r:'a ring) (k s):num.
     ((monoidM r k s).carrier = M) /\
     (!x. x IN (monoidM r k s).carrier <=> x IN M) /\
     (!x y. x IN (monoidM r k s).carrier /\ y IN (monoidM r k s).carrier ==> ((monoidM r k s).op x y = (x * y) MOD k)) /\
     ((monoidM r k s).id = 1)``,
  rw[monoidM_def]);

(* Theorem: 1 < k ==> Monoid (monoidM r k s) *)
(* Proof:
   By definitions, this is to show:
   (1) x IN M /\ y IN M ==> (x * y) MOD k IN M
       True by modN_closure.
   (2) ((x * y) MOD k * z) MOD k = (x * (y * z) MOD k) MOD k
       Since M SUBSET count k             by modN_subset_count
       hence x < k /\ y < k /\ z < k      by SUBSET_DEF, IN_COUNT
       True by MOD_MULT_ASSOC.
   (3) 1 IN M
       True by modN_has_1.
   (4) (monoidM r k s).op 1 x = x
       Since 1 IN M  by modN_has_1,
       this is to show: 1 * x = x and x < k
       True by MULT_LEFT_1, IN_COUNT.
   (5) (monoidM r k s).op x 1 = x
       Since 1 IN M  by modN_has_1,
       this is to show: x * 1 = x and x < k
       True by MULT_RIGHT_1, IN_COUNT.
*)
val monoidM_monoid = store_thm(
  "monoidM_monoid",
  ``!(r:'a ring) (k s):num. Ring r /\ 1 < k ==> Monoid (monoidM r k s)``,
  rpt strip_tac >>
  `0 < k` by decide_tac >>
  rw_tac std_ss[Monoid_def, monoidM_property] >-
  rw[modN_closure] >-
 (`(x * y) MOD k IN M` by rw[modN_closure] >>
  `(y * z) MOD k IN M` by rw[modN_closure] >>
  rw_tac std_ss[monoidM_property] >>
  `M SUBSET count k` by rw[modN_subset_count] >>
  `x < k /\ y < k /\ z < k` by metis_tac[SUBSET_DEF, IN_COUNT] >>
  rw[MOD_MULT_ASSOC]) >-
  rw[modN_has_1] >-
 (`1 IN M` by rw[modN_has_1] >>
  rw_tac std_ss[monoidM_property] >>
  `M SUBSET (count k)` by rw[modN_subset_count] >>
  metis_tac[SUBSET_DEF, IN_COUNT]) >>
  `1 IN M` by rw[modN_has_1] >>
  rw_tac std_ss[monoidM_property] >>
  `M SUBSET (count k)` by rw[modN_subset_count] >>
  metis_tac[SUBSET_DEF, IN_COUNT]);

(* Theorem: 1 < k ==> FiniteMonoid (monoidN r k s) *)
(* Proof:
   By FiniteMonoid_def, this is to show:
   (1) Monoid (monoidM r k s)
       True by monoidM_monoid.
   (2) FINITE (monoidM r k s).carrier
       i.e. to show: FINITE (M)     by monoidM_def
       Since M SUBSET (count k)     by modN_subset_count
*)
val monoidM_finite_monoid = store_thm(
  "monoidM_finite_monoid",
  ``!(r:'a ring) (k s):num. Ring r /\ 1 < k ==> FiniteMonoid (monoidM r k s)``,
  rw[FiniteMonoid_def] >-
  rw[monoidM_monoid] >>
  rw[monoidM_def] >>
  `0 < k` by decide_tac >>
  metis_tac[modN_subset_count, FINITE_COUNT, SUBSET_FINITE]);

(* ------------------------------------------------------------------------- *)
(* Introspective Monomials in Quotient Ring.                                 *)
(* ------------------------------------------------------------------------- *)

(* Define the set of monomials introspective with n, in MOD (unity k). *)
val intro_monomials_def = Define`
    intro_monomials (r:'a ring) (n:num) (k:num) = {X + |c| | c:num | n intro (X + |c|)}
`;

(* Theorem: intro_monomials r n k = IMAGE (\c:num. X + |c|) {c | c:num | (n intro (X + |c|))} *)
(* Proof: by intro_monomials_def, EXTENSION. *)
val intro_monomials_alt = store_thm(
  "intro_monomials_alt",
  ``!(r:'a ring) n k. intro_monomials r n k = IMAGE (\c:num. X + |c|) {c | c:num | (n intro (X + |c|))}``,
  rw[intro_monomials_def, EXTENSION]);

(* Theorem: p IN (intro_monomials r n k) <=> ?c:num. (p = X + |c|) /\ n intro p *)
(* Proof: by intro_monomials_def *)
val intro_monomials_element = store_thm(
  "intro_monomials_element",
  ``!(r:'a ring) n k p. p IN (intro_monomials r n k) <=> ?c:num. (p = X + |c|) /\ n intro p``,
  rw[intro_monomials_def] >>
  metis_tac[]);

(* Theorem: Ring r /\ poly z /\ 1 < deg z ==>
            intro_monomials r n k SUBSET ((PolyModRing r z).prod excluding |0|).carrier *)
(* Proof: by SUBSET_DEF, intro_monomials_element, poly_mod_ring_has_monomials *)
val intro_monomials_subset = store_thm(
  "intro_monomials_subset",
  ``!(r:'a ring) n k z. Ring r /\ poly z /\ 1 < deg z ==>
       intro_monomials r n k SUBSET ((PolyModRing r z).prod excluding |0|).carrier``,
  rw_tac std_ss[SUBSET_DEF, intro_monomials_element] >>
  metis_tac[poly_mod_ring_has_monomials]);

(* Define the subgroup of introspective monomials in the quotient field by poly z. *)
val intro_monomials_group_def = Define`
    intro_monomials_group (r:'a ring) (n:num) (k:num) (z:'a poly) =
       Generated_subset ((PolyModRing r z).prod excluding |0|) (intro_monomials r n k)
`;

(* Theorem: Field r /\ ipoly z /\ 1 < deg z ==> Group (intro_monomials_group r n k z) *)
(* Proof:
   Let e = PolyModRing r z, s = intro_monomials r n k.
   By intro_monomials_group_def, Generated_subset_group, this is to show:
   (1) Group (e.prod excluding |0|)
       This is true               by poly_mod_prod_group, ipoly z
   (2) s SUBSET (e.prod excluding |0|).carrier
       Note poly z                by poly_irreducible_poly
       This is true               by intro_monomials_subset, poly z
*)
val intro_monomials_group_group = store_thm(
  "intro_monomials_group_group",
  ``!(r:'a ring) n k z. Field r /\ ipoly z /\ 1 < deg z ==> Group (intro_monomials_group r n k z)``,
  rw_tac std_ss[intro_monomials_group_def] >>
  (irule Generated_subset_group >> rpt conj_tac) >-
  rw[poly_mod_prod_group] >>
  rw[intro_monomials_subset, poly_irreducible_poly]);

(* Theorem: Field r /\ ipoly z /\ 1 < deg z ==>
            (intro_monomials_group r n k z) <= ((PolyModRing r z).prod excluding |0|) *)
(* Proof:
   Let e = PolyModRing r z.
   By Subgroup_def, this is to show:
   (1) Group (intro_monomials_group r n k z)
       This is true                        by intro_monomials_group_group
   (2) Group ((PolyModRing r z).prod excluding |0|)
       This is true                        by poly_mod_prod_group, ipoly z
   (3) (intro_monomials_group r n k z).carrier SUBSET (e.prod excluding |0|).carrier
       Note poly z                by poly_irreducible_poly
       This is true               by intro_monomials_subset, poly z
   (4) (intro_monomials_group r n k z).op = (e.prod excluding |0|).op
       This is true               by intro_monomials_group_def, Generated_subset_def
*)
val intro_monomials_group_subgroup = store_thm(
  "intro_monomials_group_subgroup",
  ``!(r:'a ring) n k z. Field r /\ ipoly z /\ 1 < deg z ==>
    (intro_monomials_group r n k z) <= ((PolyModRing r z).prod excluding |0|)``,
  rpt strip_tac >>
  qabbrev_tac `e = PolyModRing r z` >>
  rw_tac std_ss[Subgroup_def] >-
  rw[intro_monomials_group_group] >-
  rw[poly_mod_prod_group, Abbr`e`] >-
 (rw_tac std_ss[intro_monomials_group_def] >>
  (irule Generated_subset_subset >> rpt conj_tac) >-
  rw[poly_mod_prod_group, Abbr`e`] >>
  rw[intro_monomials_subset, poly_irreducible_poly, Abbr`e`]) >>
  rw[intro_monomials_group_def, Generated_subset_def, Abbr`e`]);

(* Since it is a subgroup of a cyclic group, it must be also cyclic. *)
(* Will this help in estimating the CARD of its carrier cardinality? *)

(*
All elements of (intro_monomials_group r n k z)
are roots of (lifted) z ** m1 - z ** m2, where m1 MOD k = m2 MOD k.
*)

(* Define the introspective exponents, reduced by MOD k *)
val intro_exp_mod_def = Define`
    intro_exp_mod (r:'a ring) k s = {m MOD k | m | coprime m k /\ poly_intro_range r k m s}
`;
(* This is actually modN r k s = M *)

(* Theorem: n IN intro_exp_mod r k s <=> ?m. (n = m MOD k) /\ coprime m k /\ poly_intro_range r k m s *)
(* Proof: by intro_exp_mod_def *)
val intro_exp_mod_element = store_thm(
  "intro_exp_mod_element",
  ``!r:'a ring k s n. n IN intro_exp_mod r k s <=> ?m. (n = m MOD k) /\ coprime m k /\ poly_intro_range r k m s``,
  rw[intro_exp_mod_def]);

(* Theorem: intro_exp_mod r k s = modN r k s *)
(* Proof: by intro_exp_mod_def, modN_def, setN_def *)
val intro_exp_mod_thm = store_thm(
  "intro_exp_mod_thm",
  ``!r:'a ring k s. intro_exp_mod r k s = modN r k s``,
  rw[intro_exp_mod_def, modN_def, setN_def, EXTENSION]);

(* Theorem: FiniteField r /\ 0 < k /\ coprime (char r) k ==> ((char r) MOD k) IN (intro_exp_mod r k s) *)
(* Proof: by intro_exp_mod_element, poly_intro_range_char *)
val intro_exp_mod_has_char_mod = store_thm(
  "intro_exp_mod_has_char_mod",
  ``!r:'a field k s. FiniteField r /\ 0 < k /\ coprime (char r) k ==> ((char r) MOD k) IN (intro_exp_mod r k s)``,
  metis_tac[intro_exp_mod_element, poly_intro_range_char]);

(* Theorem: Ring r /\ 0 < k ==>
            !m n. m IN (intro_exp_mod r k s) /\ n IN (intro_exp_mod r k s) ==>
                  ((m * n) MOD k) IN (intro_exp_mod r k s) *)
(* Proof:
   Note m IN (intro_exp_mod r k s)
    ==> ?m1. (m = m1 MOD k) /\ coprime m1 k /\ poly_intro_range r k m1 s  by intro_exp_mod_element
    and n IN (intro_exp_mod r k s)
    ==> ?n1. (n = n1 MOD k) /\ coprime n1 k /\ poly_intro_range r k n1 s  by intro_exp_mod_element
   Note coprime (m1 * n1) k                        by coprime_product_coprime
    and poly_intro_range r k (m1 * n1) s           by poly_intro_range_product
    and (m1 * n1) MOD k = (m * n) MOD k            by MOD_TIMES2, 0 < k
   Thus ((m * n) MOD k) IN (intro_exp_mod r k s)   by intro_exp_mod_element
*)
val intro_exp_mod_closure = store_thm(
  "intro_exp_mod_closure",
  ``!r:'a ring k s. Ring r /\0 < k ==>
   !m n. m IN (intro_exp_mod r k s) /\ n IN (intro_exp_mod r k s) ==>
         ((m * n) MOD k) IN (intro_exp_mod r k s)``,
  rpt strip_tac >>
  `?m1. (m = m1 MOD k) /\ coprime m1 k /\ poly_intro_range r k m1 s` by rw[GSYM intro_exp_mod_element] >>
  `?n1. (n = n1 MOD k) /\ coprime n1 k /\ poly_intro_range r k n1 s` by rw[GSYM intro_exp_mod_element] >>
  `coprime (m1 * n1) k` by rw[coprime_product_coprime] >>
  `poly_intro_range r k (m1 * n1) s` by metis_tac[poly_intro_range_product] >>
  `(m1 * n1) MOD k = (m * n) MOD k` by rw[MOD_TIMES2] >>
  metis_tac[intro_exp_mod_element]);

(* Theorem alias *)
val intro_exp_mod_has_product = save_thm("intro_exp_mod_has_product", intro_exp_mod_closure);
(* val intro_exp_mod_has_product =
   |- !r k s. Ring r /\ 0 < k ==>
      !m n. m IN intro_exp_mod r k s /\ n IN intro_exp_mod r k s ==> (m * n) MOD k IN intro_exp_mod r k s: thm *)

(* Theorem: 1 < k ==> (intro_exp_mod r k s) SUBSET (Euler k) *)
(* Proof: by intro_exp_mod_thm, modN_subset_euler *)
val intro_exp_mod_subset_euler = store_thm(
  "intro_exp_mod_subset_euler",
  ``!r:'a ring k s. 1 < k ==> (intro_exp_mod r k s) SUBSET (Euler k)``,
  rw[intro_exp_mod_thm, modN_subset_euler]);

(* Define the subgroup generated by (intro_exp_mod r k s) *)
val intro_exp_mod_group_def = Define`
    intro_exp_mod_group (r:'a ring) k s = Generated_subset (Estar k) (intro_exp_mod r k s)
`;

(* Theorem: 1 < k ==> Group (intro_exp_mod_group r k s) *)
(* Proof:
   By intro_exp_mod_group_def, Generated_subset_group, this is to show:
   (1) Group (Estar k), true                  by Estar_group, 1 < k
   (2) intro_exp_mod r k s SUBSET (Estar k).carrier
       Note (Estar k).carrier = Euler k       by Estar_property
       The result follows                     by intro_exp_mod_subset_euler, 1 < k
*)
val intro_exp_mod_group_group = store_thm(
  "intro_exp_mod_group_group",
  ``!r:'a ring k s. 1 < k ==> Group (intro_exp_mod_group r k s)``,
  rw[intro_exp_mod_group_def] >>
  (irule Generated_subset_group >> rpt conj_tac) >-
  rw[Estar_group] >>
  rw[Estar_property, intro_exp_mod_subset_euler]);

(* Theorem: 1 < k ==> (intro_exp_mod_group r k s) <= Estar k *)
(* Proof:
   By intro_exp_mod_group_def, Generated_subset_subgroup, this is to show:
   (1) Group (Estar k), true                  by Estar_group, 1 < k
   (2) intro_exp_mod r k s SUBSET (Estar k).carrier
       Note (Estar k).carrier = Euler k       by Estar_property
       The result follows                     by intro_exp_mod_subset_euler, 1 < k
*)
val intro_exp_mod_group_subgroup = store_thm(
  "intro_exp_mod_group_subgroup",
  ``!r:'a ring k s. 1 < k ==> (intro_exp_mod_group r k s) <= Estar k``,
  rw[intro_exp_mod_group_def] >>
  (irule Generated_subset_subgroup >> rpt conj_tac) >-
  rw[Estar_group] >>
  rw[Estar_property, intro_exp_mod_subset_euler]);

(* This is a finite subgroup, and Estar_card |- !n. CARD (Estar n).carrier = totient n *)



(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
