(* ------------------------------------------------------------------------- *)
(* Finite Group Order                                                        *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "groupOrder";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory dividesTheory gcdTheory
     numberTheory combinatoricsTheory;

open monoidTheory;

open groupTheory groupMapTheory subgroupTheory;

(* ------------------------------------------------------------------------- *)
(* Finite Group Order Documentation                                          *)
(* ------------------------------------------------------------------------- *)
(* Overloads:
   gen a     = Generated g a
   Gen a     = (Generated g a).carrier
   uroots n  = roots_of_unity g n
   gen_set s = Generated_subset g s
*)
(* Definitions and Theorems (# are exported):

   Finite Group:
   finite_group_card_pos  |- !g. FiniteGroup g ==> 0 < CARD G
   finite_group_exp_not_distinct
                          |- !g. FiniteGroup g ==> !x. x IN G ==> ?h k. (x ** h = x ** k) /\ h <> k
   finite_group_exp_period_exists
                          |- !g. FiniteGroup g ==> !x. x IN G ==> ?k. 0 < k /\ (x ** k = #e)

   Finite Group Order:
   group_order_nonzero    |- !g. FiniteGroup g ==> !x. x IN G ==> ord x <> 0
   group_order_pos        |- !g. FiniteGroup g ==> !x. x IN G ==> 0 < ord x
   group_order_property   |- !g. FiniteGroup g ==> !x. x IN G ==> 0 < ord x /\ (x ** ord x = #e)
   group_order_inv        |- !g. Group g ==> !x. x IN G /\ 0 < ord x ==> ( |/ x = x ** (ord x - 1))
   group_exp_mod          |- !g. Group g ==> !x. x IN G /\ 0 < ord x ==> !n. x ** n = x ** (n MOD ord x)

   Characterization of Group Order:
   group_order_thm        |- !g n. 0 < n ==>
                             !x. (ord x = n) <=> (x ** n = #e) /\ !m. 0 < m /\ m < n ==> x ** m <> #e
   group_order_unique     |- !g. Group g ==> !x. x IN G ==>
                             !m n. m < ord x /\ n < ord x ==> (x ** m = x ** n) ==> (m = n)
   group_exp_equal        |- !g x. Group g /\ x IN G ==>
                             !n m. n < ord x /\ m < ord x /\ (x ** n = x ** m) ==> (n = m)
   finite_group_order     |- !g. FiniteGroup g ==> !x. x IN G ==>
                             !n. (ord x = n) ==>
                                 0 < n /\ (x ** n = #e) /\ !m. 0 < m /\ m < n ==> x ** m <> #e
   finite_group_primitive_property
                          |- !g. FiniteGroup g ==> !z. z IN G /\ (ord z = CARD G) ==>
                                                   !x. x IN G ==> ?n. x = z ** n

   Lifting Theorems from Monoid Order:
#  group_order_id         |- !g. Group g ==> (ord #e = 1)
   group_order_eq_1       |- !g. Group g ==> !x. x IN G ==> ((ord x = 1) <=> (x = #e))
   group_order_condition  |- !g. Group g ==> !x. x IN G ==> !m. (x ** m = #e) <=> (ord x) divides m
   group_order_power_eq_0 |- !g. Group g ==> !x. x IN G ==> !k. (ord (x ** k) = 0) <=> 0 < k /\ (ord x = 0)
   group_order_power      |- !g. Group g ==> !x. x IN G ==> !k. ord (x ** k) * gcd (ord x) k = ord x
   group_order_power_eqn  |- !g. Group g ==> !x k. x IN G /\ 0 < k ==> (ord (x ** k) = ord x DIV gcd k (ord x))
   group_order_power_coprime
                          |- !g. Group g ==> !x. x IN G ==>
                                             !n. coprime n (ord x) ==> (ord (x ** n) = ord x)
   group_order_cofactor   |- !g. Group g ==> !x n. x IN G /\ 0 < ord x /\ n divides ord x ==>
                                                   (ord (x ** (ord x DIV n)) = n)
   group_order_divisor    |- !g. Group g ==>!x m. x IN G /\ 0 < ord x /\ m divides ord x ==>
                                            ?y. y IN G /\ (ord y = m)
   group_order_common     |- !g. Group g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) ==>
                                 ?z. z IN G /\ (ord z * gcd (ord x) (ord y) = lcm (ord x) (ord y))
   group_order_common_coprime
                          |- !g. Group g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) /\
                                 coprime (ord x) (ord y) ==> ?z. z IN G /\ (ord z = ord x * ord y)
   group_orders_eq_1      |- !g. Group g ==> (orders g 1 = {#e})
   group_order_divides_exp     |- !g x. Group g /\ x IN G ==> !n. (x ** n = #e) <=> ord x divides n
   group_exp_mod_order         |- !g. Group g ==> !x. x IN G /\ 0 < ord x ==> !n. x ** n = x ** (n MOD ord x)
   group_order_divides_maximal |- !g. FiniteAbelianGroup g ==>  !x. x IN G ==> (ord x) divides (maximal_order g)
   abelian_group_order_common  |- !g. AbelianGroup g ==> !x y. x IN G /\ y IN G ==>
                                      ?z. z IN G /\ (ord z * gcd (ord x) (ord y) = lcm (ord x) (ord y))
   abelian_group_order_common_coprime
                               |- !g. AbelianGroup g ==> !x y. x IN G /\ y IN G /\
                                      coprime (ord x) (ord y) ==> ?z. z IN G /\ (ord z = ord x * ord y)

   Order of Inverse:
   group_inv_order           |- !g x. Group g /\ x IN G ==> (ord ( |/ x) = ord x)
   monoid_inv_order_property |- !g. FiniteMonoid g ==> !x. x IN G* ==> 0 < ord x /\ (x ** ord x = #e)
   monoid_inv_order          |- !g x. Monoid g /\ x IN G* ==> (ord ( |/ x) = ord x)

   The generated subgroup by a group element:
   Generated_def          |- !g a. gen a = <|carrier := {x | ?k. x = a ** k}; op := $*; id := #e|>
   generated_element      |- !g a x. x IN Gen a <=> ?n. x = a ** n
   generated_property     |- !g a. ((gen a).op = $* ) /\ ((gen a).id = #e)
   generated_carrier      |- !g a. a IN G ==> (Gen a = IMAGE ($** a) univ(:num))
   generated_gen_element  |- !g. Group g ==> !x. x IN G ==> x IN (Gen x)
   generated_carrier_has_id    |- !g a. #e IN Gen a
   generated_id_carrier   |- !g. Group g ==> (Gen #e = {#e})
   generated_id_subgroup  |- !g. Group g ==> gen #e <= g
   generated_group        |- !g a. FiniteGroup g /\ a IN G ==> Group (gen a)
   generated_subset       |- !g a. Group g /\ a IN G ==> Gen a SUBSET G
   generated_subgroup     |- !g a. FiniteGroup g /\ a IN G ==> gen a <= g
   generated_group_finite |- !g a. FiniteGroup g /\ a IN G ==> FINITE (Gen a)
   generated_finite_group |- !g a. FiniteGroup g /\ a IN G ==> FiniteGroup (gen a)
   generated_exp          |- !g a z. a IN G /\ z IN Gen a ==> !n. (gen a).exp z n = z ** n
   group_order_to_generated_bij
                          |- !g a. Group g /\ a IN G /\ 0 < ord a ==>
                                   BIJ (\n. a ** n) (count (ord a)) (Gen a)
   generated_group_card   |- !g a. Group g /\ a IN G /\ 0 < ord a ==> (CARD (Gen a) = ord a)
   generated_carrier_as_image  |- !g. Group g ==> !a. a IN G /\ 0 < ord a ==>
                                       (Gen a = IMAGE (\j. a ** j) (count (ord a)))

   Group Order and Divisibility:
   group_order_divides    |- !g. FiniteGroup g ==> !x. x IN G ==> (ord x) divides (CARD G)
   finite_group_Fermat    |- !g a. FiniteGroup g /\ a IN G ==> (a ** CARD G = #e)
   generated_Fermat       |- !g a. FiniteGroup g /\ a IN G ==>
                             !x. x IN (Gen a) ==> (x ** CARD (Gen a) = #e)
   group_exp_eq_condition |- !g x. Group g /\ x IN G /\ 0 < ord x ==>
                             !n m. (x ** n = x ** m) <=> (n MOD ord x = m MOD ord x)
   group_order_power_eq_order  |- !g x. Group g /\ x IN G /\ 0 < ord x ==>
                                  !k. (ord (x ** k) = ord x) <=> coprime k (ord x)
   group_order_exp_cofactor    |- !g x n. Group g /\ x IN G /\ 0 < ord x /\ n divides ord x ==>
                                          (ord (x ** (ord x DIV n)) = n)

   Roots of Unity form a Subgroup:
   roots_of_unity_def     |- !g n. uroots n =
                                   <|carrier := {x | x IN G /\ (x ** n = #e)}; op := $*; id := #e|>
   roots_of_unity_element |- !g n x. x IN (uroots n).carrier <=> x IN G /\ (x ** n = #e)
   roots_of_unity_subset  |- !g n. (uroots n).carrier SUBSET G
   roots_of_unity_0       |- !g. (uroots 0).carrier = G
   group_uroots_has_id    |- !g. Group g ==> !n. #e IN (uroots n).carrier
   group_uroots_subgroup  |- !g. AbelianGroup g ==> !n. uroots n <= g
   group_uroots_group     |- !g. AbelianGroup g ==> !n. Group (uroots n)

   Subgroup generated by a subset of a Group:
   Generated_subset_def      |- !g s. gen_set s =
                                    <|carrier := BIGINTER (IMAGE (\h. H) {h | h <= g /\ s SUBSET H});
                                      op := $*; id := #e|>
   Generated_subset_property |- !g s.
        ((gen_set s).carrier = BIGINTER (IMAGE (\h. H) {h | h <= g /\ s SUBSET H})) /\
        ((gen_set s).op = $* ) /\ ((gen_set s).id = #e)
   Generated_subset_has_set  |- !g s. s SUBSET (gen_set s).carrier
   Generated_subset_subset   |- !g s. Group g /\ s SUBSET G ==> (gen_set s).carrier SUBSET G
   Generated_subset_group    |- !g s. Group g /\ SUBSET G ==> Group (gen_set s)
   Generated_subset_subgroup |- !g s. Group g /\ s SUBSET G ==> gen_set s <= g
   Generated_subset_exp      |- !g s. (gen_set s).exp = $**
   Generated_subset_gen      |- !g a. FiniteGroup g /\ a IN G ==> (gen_set (Gen a) = gen a)
*)

(* ------------------------------------------------------------------------- *)
(* Finite Group.                                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteGroup g ==> 0 < CARD G *)
(* Proof:
   Since FiniteGroup g
     ==> Group g /\ FINITE G      by FiniteGroup_def
      so G <> {}                  by group_carrier_nonempty
    thus CARD G <> 0              by CARD_EQ_0, FINITE G
      or 0 < CARD G               by NOT_ZERO_LT_ZERO
*)
val finite_group_card_pos = store_thm(
  "finite_group_card_pos",
  ``!g:'a group. FiniteGroup g ==> 0 < CARD G``,
  metis_tac[FiniteGroup_def, group_carrier_nonempty, CARD_EQ_0, NOT_ZERO_LT_ZERO]);

(* Theorem: For FINITE Group g and x IN G, x ** n cannot be all distinct. *)
(* Proof: by finite_monoid_exp_not_distinct. *)
val finite_group_exp_not_distinct = store_thm(
  "finite_group_exp_not_distinct",
  ``!g:'a group. FiniteGroup g ==> !x. x IN G ==> ?h k. (x ** h = x ** k) /\ h <> k``,
  rw[finite_monoid_exp_not_distinct, finite_group_is_finite_monoid]);

(* Theorem: For FINITE Group g and x IN G, there is k > 0 such that x ** k = #e. *)
(* Proof:
   Since G is FINITE,
   ?m n. m <> n and x ** m = x ** n      by finite_group_exp_not_distinct
   Assume m < n, then x ** (n-m) = #e    by group_exp_eq
   The case m > n is symmetric.

   Note: Probably can be improved to bound k <= CARD G.
*)
val finite_group_exp_period_exists = store_thm(
  "finite_group_exp_period_exists",
  ``!g:'a group. FiniteGroup g ==> !x. x IN G ==> ?k. 0 < k /\ (x ** k = #e)``,
  rpt strip_tac >>
  `?m n. m <> n /\ (x ** m = x ** n)` by metis_tac[finite_group_exp_not_distinct] >>
  Cases_on `m < n` >| [
    `0 < n-m` by decide_tac,
    `n < m /\ 0 < m-n` by decide_tac
  ] >> metis_tac[group_exp_eq, FiniteGroup_def]);

(* ------------------------------------------------------------------------- *)
(* Finite Group Order                                                        *)
(* ------------------------------------------------------------------------- *)

(* Note:

(Z, $+ ) and (Z, $* ) are examples of infinite group with non-identity elements of order 0.
(Power set of an infinite set, symmetric difference) is an example of an infinite group with non-identity elements of order 2.

Although FiniteGroup g implies 0 < ord x
group_order_nonzero |- !g. FiniteGroup g ==> !x. x IN G ==> 0 < ord x
even infinite groups can have 0 < ord x.

Thus if the theorem only needs 0 < ord x, there is no need for FiniteGroup g.
*)

(* Theorem: FiniteGroup g ==> !x. x IN G ==> ord x <> 0 *)
(* Proof:
   By contradiction. Suppose ord x = 0.
   Then !n. 0 < n ==> x ** n <> #e    by order_eq_0
    But ?k. 0 < k /\ (x ** k = #e)    by finite_group_exp_period_exists
   Hence a contradiction.
*)
val group_order_nonzero = store_thm(
  "group_order_nonzero",
  ``!g:'a group. FiniteGroup g ==> !x. x IN G ==> ord x <> 0``,
  spose_not_then strip_assume_tac >>
  `ord x = 0` by decide_tac >>
  metis_tac[order_eq_0, finite_group_exp_period_exists]);

(* Theorem: FiniteGroup g ==> !x. x IN G ==> 0 < ord x *)
(* Proof: by group_order_nonzero *)
val group_order_pos = store_thm(
  "group_order_pos",
  ``!g:'a group. FiniteGroup g ==> !x. x IN G ==> 0 < ord x``,
  metis_tac[group_order_nonzero, NOT_ZERO_LT_ZERO]);

(* Theorem: The finite group element order m satisfies: 0 < m and x ** m = #e. *)
(* Proof: by group_order_pos, order_property. *)
val group_order_property = store_thm(
  "group_order_property",
  ``!g:'a group. FiniteGroup g ==> !x. x IN G ==> 0 < ord x /\ (x ** ord x = #e)``,
  rw[group_order_pos, order_property]);

(* Theorem: For Group g, if 0 < m, |/ x = x ** (m-1) where m = ord x *)
(* Proof:
   Let y = x ** ((ord x) - 1).
   x * y = x ** (SUC (ord x - 1))   by group_exp_SUC
         = x ** ord x               by 0 < ord x
         = #e                       by order_property
   Thus |/ x = y                    by group_rinv_unique
*)
val group_order_inv = store_thm(
  "group_order_inv",
  ``!g:'a group. Group g ==> !x. x IN G /\ 0 < ord x ==> ( |/x = x ** ((ord x)-1))``,
  rpt strip_tac >>
  qabbrev_tac `y = x ** ((ord x) - 1)` >>
  `y IN G` by rw[Abbr`y`] >>
  `SUC ((ord x) - 1) = ord x` by decide_tac >>
  `x * y = x ** (ord x)` by metis_tac[group_exp_SUC] >>
  metis_tac[group_rinv_unique, order_property]);

(* Theorem: For Group g, if 0 < m, x ** n = x ** (n mod m), where m = ord x *)
(* Proof:
   Let m = ord x.
     x ** n
   = x ** (m * q + r)            by division: n = q * m + r
   = x ** (m * q) * (x ** r)     by group_exp_add
   = ((x ** m) ** q) * (x ** r)  by group_exp_mult
   = (#e ** q) * (x ** r)        by order_property
   = #e * (x ** r)               by group_id_exp
   = x ** r                      by group_lid
*)
val group_exp_mod = store_thm(
  "group_exp_mod",
  ``!g:'a group. Group g ==> !x. x IN G /\ 0 < ord x ==> !n. x ** n = x ** (n MOD ord x)``,
  rpt strip_tac >>
  qabbrev_tac `m = ord x` >>
  `x ** m = #e` by rw[order_property, Abbr`m`] >>
  `n = (n DIV m) * m + (n MOD m)` by rw[DIVISION] >>
  `_ = m * (n DIV m) + (n MOD m)` by decide_tac >>
  metis_tac[group_exp_add, group_exp_mult, group_id_exp, group_lid, group_exp_element]);

(* ------------------------------------------------------------------------- *)
(* Characterization of Group Order                                           *)
(* ------------------------------------------------------------------------- *)

(* A characterization of group order without reference to period. *)

(* Theorem: If 0 < n, ord x = n iff x ** n = #e with 0 < n, and !m < n, x ** m <> #e. *)
(* Proof: true by order_thm. *)
val group_order_thm = store_thm(
  "group_order_thm",
  ``!g:'a group. !n. 0 < n ==>
   !x. (ord x = n) <=> (x ** n = #e) /\ (!m. 0 < m /\ m < n ==> (x ** m) <> #e)``,
  rw[order_thm]);

(* Theorem: For Group g, m, n < (ord x), x ** m = x ** n ==> m = n *)
(* Proof:
   Otherwise x ** (m-n) = #e by group_exp_eq,
   contradicting minimal nature of element order.
*)
val group_order_unique = store_thm(
  "group_order_unique",
  ``!g:'a group. Group g ==> !x. x IN G ==>
   !m n. m < ord x /\ n < ord x /\ (x ** m = x ** n) ==> (m = n)``,
  spose_not_then strip_assume_tac >>
  Cases_on `m < n` >| [
    `0 < n-m /\ n-m < ord x` by decide_tac,
    `n < m /\ 0 < m-n /\ m-n < ord x` by decide_tac
  ] >>
  metis_tac[group_exp_eq, order_minimal]);

(* Theorem: Group g /\ x IN G ==> !n m. n < ord x /\ m < ord x /\ (x ** n = x ** m) ==> (n = m) *)
(* Proof: by group_order_unique *)
val group_exp_equal = store_thm(
  "group_exp_equal",
  ``!(g:'a group) x. Group g /\ x IN G ==>
   !n m. n < ord x /\ m < ord x /\ (x ** n = x ** m) ==> (n = m)``,
  metis_tac[group_order_unique]);

(* Theorem: [property of finite group order]
   For x IN G, if (ord x = n), 0 < n /\ (x ** n = #e) /\ (!m. 0 < m /\ m < n ==> (x ** m) <> #e
*)
(* Proof:
   ord x = n ==> 0 < n /\ x ** n = #e                  by group_order_property
   ord x = n ==> !m. 0 < m /\ m < n ==> x ** m <> #e   by order_minimal
*)
val finite_group_order = store_thm(
  "finite_group_order",
  ``!g:'a group. FiniteGroup g ==> !x. x IN G ==>
      !n. (ord x = n) ==> (0 < n /\ (x ** n = #e) /\ (!m. 0 < m /\ m < n ==> (x ** m) <> #e))``,
  metis_tac[group_order_property, order_minimal]);

(* Theorem: FiniteGroup g /\ !z. z IN G /\ (ord z = CARD G) ==>
            !x. x IN G ==> ?n. n < CARD G /\ (x = z ** n) *)
(* Proof:
   By order g z = CARD G, all powers of z are distinct.
   By FiniteGroup g, all powers of z = permutation of element.
   Hence each element is some power of z.
   Or,
   Let f = \n. z ** n
   Then INJ f (count (CARD G)) G         by INJ_DEF, group_order_unique
   Now  FINITE (count (CARD G))          by FINITE_COUNT
        CARD (count (CARD G)) = CARD G   by CARD_COUNT
    so  SURJ f (count (CARD G)) G        by FINITE_INJ_AS_SURJ, FINITE G
   i.e. IMAGE f (count (CARD G)) = G     by IMAGE_SURJ
   Hence ?n. n < CARD G /\ x = z ** n    by IN_IMAGE, IN_COUNT
*)
val finite_group_primitive_property = store_thm(
  "finite_group_primitive_property",
  ``!g:'a group. FiniteGroup g ==> !z. z IN G /\ (ord z = CARD G) ==>
   (!x. x IN G ==> ?n. n < CARD G /\ (x = z ** n))``,
  rpt (stripDup[FiniteGroup_def]) >>
  qabbrev_tac `f = \n. z ** n` >>
  `INJ f (count (CARD G)) G` by
  (rw[INJ_DEF, Abbr`f`] >>
  metis_tac[group_order_unique]) >>
  `FINITE (count (CARD G))` by rw[] >>
  `CARD (count (CARD G)) = CARD G` by rw[] >>
  `SURJ f (count (CARD G)) G` by rw[FINITE_INJ_AS_SURJ] >>
  `IMAGE f (count (CARD G)) = G` by rw[GSYM IMAGE_SURJ] >>
  metis_tac[IN_IMAGE, IN_COUNT]);

(* ------------------------------------------------------------------------- *)
(* Lifting Theorems from Monoid Order                                        *)
(* ------------------------------------------------------------------------- *)

(* Lifting Monoid Order theorem for Group Order.
   from: !g:'a monoid. Monoid g ==> ....
     to: !g:'a group.  Group g ==> ....
    via: !g:'a group.  Group g ==> Monoid g
*)
local
val gim = group_is_monoid |> SPEC_ALL |> UNDISCH
in
fun lift_monoid_order_thm suffix = let
   val mth = DB.fetch "monoid" ("monoid_order_" ^ suffix)
   val mth' = mth |> SPEC_ALL
in
   save_thm("group_order_" ^ suffix, gim |> MP mth' |> DISCH_ALL |> GEN_ALL)
end
end; (* local *)

(* Theorem: ord #e = 1 *)
val group_order_id = lift_monoid_order_thm "id";
(* > val group_order_id = |- !g. Group g ==> (ord #e = 1): thm *)

(* export simple result *)
val _ = export_rewrites ["group_order_id"];

(* Theorem: x IN G ==> ord x = 1 <=> x = #e *)
val group_order_eq_1 = lift_monoid_order_thm "eq_1";
(* > val group_order_eq_1 = |- !g. Group g ==> !x. x IN G ==> ((ord x = 1) <=> (x = #e)): thm *)

(* Theorem: x IN G ==> !m. (x ** m = #e) <=> (ord x) divides m *)
val group_order_condition = lift_monoid_order_thm "condition";
(* > val group_order_condition = |- !g. Group g ==> !x. x IN G ==> !m. (x ** m = #e) <=> ord x divides m: thm *)

(* Theorem: x IN G ==> !k. (ord (x ** k) = 0) <=> 0 < k /\ (ord x = 0) *)
val group_order_power_eq_0 = lift_monoid_order_thm "power_eq_0";
(* > val group_order_power_eq_0 = |- !g. Group g ==>
     !x. x IN G ==> !k. (ord (x ** k) = 0) <=> 0 < k /\ (ord x = 0): thm *)

(* Theorem: x IN G ==> !k. ord (x ** k) = ord x / gcd(ord x, k) *)
val group_order_power = lift_monoid_order_thm "power";
(* > val group_order_power = |- !g. Group g ==> !x. x IN G ==> !k. ord (x ** k) * gcd (ord x) k = ord x: thm *)

(* Theorem: x IN G ==> !k. ord (x ** k) = ord x / gcd(ord x, k) *)
val group_order_power_eqn = lift_monoid_order_thm "power_eqn";
(* > val group_order_power_eqn = |- !g. Group g ==> !x k. x IN G /\ 0 < k ==> (ord (x ** k) = ord x DIV (gcd k (ord x))): thm *)

(* Theorem: x IN G ==> !k. ord (x ** k) = ord x / gcd(ord x, k) *)
val group_order_power_coprime = lift_monoid_order_thm "power_coprime";
(* > val group_order_power_coprime =
   |- !g. Group g ==> !x. x IN G ==> !n. coprime n (ord x) ==> (ord (x ** n) = ord x): thm *)

(* Theorem: x IN G ==> !k. ord (x ** k) = ord x / gcd(ord x, k) *)
val group_order_cofactor = lift_monoid_order_thm "cofactor";
(* > val group_order_cofactor = |- !g. Group g ==> !x n. x IN G /\ 0 < ord x /\ n divides ord x ==>
        (ord (x ** (ord x DIV n)) = n): thm *)

(* Theorem: If x IN G with ord x = n, and m divides n, then G contains an element of order m. *)
val group_order_divisor = lift_monoid_order_thm "divisor";
(* > val group_order_divisor = |- !g. Group g ==>
     !x m. x IN G /\ 0 < ord x /\ m divides ord x ==> ?y. y IN G /\ (ord y = m): thm *)

(* Theorem: If x * y = y * x, and n = ord x, m = ord y,
            then there exists z IN G such that ord z = (lcm n m) / (gcd n m) *)
val group_order_common = lift_monoid_order_thm "common";
(* > val group_order_common = |- !g. Group g ==>
         !x y. x IN G /\ y IN G /\ (x * y = y * x) ==>
         ?z. z IN G /\ (ord z * gcd (ord x) (ord y) = lcm (ord x) (ord y)): thm *)
(* Note:
   This is interesting, but this z has a 'smaller' order: (lcm n m) / (gcd n m).

   The theorem that is desired is:
   Theorem: If x * y = y * x, and n = ord x, m = ord y, then there exists z IN G such that ord z = (lcm n m)

   But this needs another method.
   However, a restricted form of this theorem is still useful.
*)

(* Theorem: If x * y = y * x, and n = ord x, m = ord y, and gcd n m = 1,
            then there exists z IN G with ord z = (lcm n m) *)
val group_order_common_coprime = lift_monoid_order_thm "common_coprime";
(* > val group_order_common_coprime = |- !g. Group g ==>
         !x y. x IN G /\ y IN G /\ (x * y = y * x) /\ coprime (ord x) (ord y) ==>
         ?z. z IN G /\ (ord z = ord x * ord y): thm *)

(* Theorem: Group g ==> (orders g 1 = {#e}) *)
(* Proof: by group_is_monoid, orders_eq_1 *)
val group_orders_eq_1 = store_thm(
  "group_orders_eq_1",
  ``!g:'a group. Group g ==> (orders g 1 = {#e})``,
  rw[group_is_monoid, orders_eq_1]);

(* Theorem: Group g /\ x IN G ==> !n. (x ** n = #e) <=> (ord x) divides n *)
(* Proof: by group_order_condition *)
val group_order_divides_exp = store_thm(
  "group_order_divides_exp",
  ``!(g:'a group) x. Group g /\ x IN G ==> !n. (x ** n = #e) <=> (ord x) divides n``,
  rw[group_order_condition]);

(* Another proof of subgroup_order in subgroupTheory. *)

(* Theorem: h <= g ==> !x. x IN H ==> (order h x = ord x) *)
(* Proof:
   h <= g means Group g /\ Group h /\ H SUBSET G   by Subgroup_def
   Let x IN H, then x IN G                         by SUBSET_DEF
   x ** (order h x) = #e /\ x ** (ord x) = #e      by order_property
   Therefore
   (ord x) (order h x) divides           by group_order_condition, 1st one
   (order h x) divides (ord x)           by group_order_condition, 2nd one
   Hence order h x = ord x               by DIVIDES_ANTISYM
*)
(* keep subgroupTheory.subgroup_order *)
val subgroup_order = prove(
  ``!g h:'a group. h <= g ==> !x. x IN H ==> (order h x = ord x)``,
  rpt strip_tac >>
  `Group g /\ Group h /\ H SUBSET G /\ (h.op = g.op) /\ (h.id = #e)` by metis_tac[Subgroup_def, subgroup_id] >>
  `!x. x IN H ==> x IN G` by metis_tac[SUBSET_DEF] >>
  `!x. x IN H ==> !n. h.exp x n = x ** n` by metis_tac[subgroup_exp] >>
  metis_tac[order_property, group_order_condition, DIVIDES_ANTISYM]);

(* Theorem: Group g ==> !x. x IN G /\ 0 < ord x ==> !n. x ** n = x ** (n MOD (ord x)) *)
(* Proof: by monoid_exp_mod_order, group_is_monoid *)
val group_exp_mod_order = store_thm(
  "group_exp_mod_order",
  ``!g:'a group. Group g ==> !x. x IN G /\ 0 < ord x ==> !n. x ** n = x ** (n MOD (ord x))``,
  metis_tac[monoid_exp_mod_order, group_is_monoid]);

(* Theorem: In a Finite Abelian Group, every order divides the maximal order.
            FiniteAbelianGroup g ==> !x. x IN G ==> ord x divides maximal_order g *)
(* Proof:
   Since 0 < ord x     by group_order_pos
   The result is true  by monoid_order_divides_maximal
*)
val group_order_divides_maximal = store_thm(
  "group_order_divides_maximal",
  ``!g:'a group. FiniteAbelianGroup g ==> !x. x IN G ==> (ord x) divides (maximal_order g)``,
  metis_tac[monoid_order_divides_maximal, group_order_pos, finite_group_is_finite_monoid,
             FiniteAbelianGroup_def_alt, FiniteAbelianMonoid_def_alt]);

(* Theorem: AbelianGroup g ==> !x y. x IN G /\ y IN G ==>
            ?z. z IN G /\ (ord z * gcd (ord x) (ord y) = lcm (ord x) (ord y)) *)
(* Proof: by AbelianGroup_def, group_order_common *)
val abelian_group_order_common = store_thm(
  "abelian_group_order_common",
  ``!g:'a group. AbelianGroup g ==> !x y. x IN G /\ y IN G ==>
   ?z. z IN G /\ (ord z * gcd (ord x) (ord y) = lcm (ord x) (ord y))``,
  rw[AbelianGroup_def, group_order_common]);

(* Theorem: AbelianGroup g ==> !x y. x IN G /\ y IN G /\ coprime (ord x) (ord y) ==>
            ?z. z IN G /\ (ord z = ord x * ord y) *)
(* Proof: by AbelianGroup_def, group_order_common_coprime *)
val abelian_group_order_common_coprime = store_thm(
  "abelian_group_order_common_coprime",
  ``!g:'a group. AbelianGroup g ==> !x y. x IN G /\ y IN G /\ coprime (ord x) (ord y) ==>
   ?z. z IN G /\ (ord z = ord x * ord y)``,
  rw[AbelianGroup_def, group_order_common_coprime]);

(* ------------------------------------------------------------------------- *)
(* Order of Inverse                                                          *)
(* ------------------------------------------------------------------------- *)

(*
group_order_inv
|- !g. Group g ==> !x. x IN G /\ 0 < ord x ==> ( |/ x = x ** (ord x - 1))
*)

(* Theorem: Group g /\ x IN G ==> (ord ( |/ x) = ord x) *)
(* Proof:
   Let n = ord x.
   If n = 0,
      Let m = ord ( |/ x).
      By contradiction, suppose m <> 0.
      Then #e = ( |/ x) ** m               by order_property
              = |/ (x ** m)                by group_inv_exp
      Thus x ** m = |/ #e                  by group_inv_inv
                  = #e                     by group_inv_id
      This contradicts ord x = n = 0       by order_eq_0, 0 < m

   Otherwise n <> 0, or 0 < n              by NOT_ZERO_LT_ZERO
     ord ( |/ x)
   = ord ( |/ x) * 1                       by MULT_RIGHT_1
   = ord ( |/ x) * gcd n (n - 1)           by coprime_PRE, 0 < n
   = ord (x ** (n - 1)) * gcd n (n - 1)    by group_order_inv
   = n                                     by group_order_power
*)
val group_inv_order = store_thm(
  "group_inv_order",
  ``!(g:'a group) x. Group g /\ x IN G ==> (ord ( |/ x) = ord x)``,
  rpt strip_tac >>
  qabbrev_tac `n = ord x` >>
  Cases_on `n = 0` >| [
    simp[] >>
    spose_not_then strip_assume_tac >>
    qabbrev_tac `m = ord ( |/ x)` >>
    `#e = ( |/ x) ** m` by rw[order_property, Abbr`m`] >>
    `_ = |/ (x ** m)` by rw[group_inv_exp] >>
    `x ** m = #e` by metis_tac[group_inv_inv, group_inv_id, group_exp_element] >>
    `0 < m` by decide_tac >>
    metis_tac[order_eq_0],
    `0 < n` by decide_tac >>
    metis_tac[MULT_RIGHT_1, coprime_PRE, group_order_inv, group_order_power]
  ]);

(*
> group_order_property |> ISPEC ``Invertibles g``;
val it = |- FiniteGroup (Invertibles g) ==> !x. x IN (Invertibles g).carrier ==>
     0 < order (Invertibles g) x /\
     ((Invertibles g).exp x (order (Invertibles g) x) = (Invertibles g).id): thm
*)

(* Theorem: FiniteMonoid g ==> !x. x IN G* ==> 0 < ord x /\ (x ** ord x = #e) *)
(* Proof:
   Note FiniteGroup (Invertibles g)        by finite_monoid_invertibles_is_finite_group
    and (Invertibles g).carrier = G*       by Invertibles_carrier
    ==> 0 < order (Invertibles g) x  /\
        (Invertibles g).exp x (order (Invertibles g) x) =
         (Invertibles g).id                by group_order_property
    But order (Invertibles g) x = ord x    by Invertibles_order
    and (Invertibles g).id = #e            by Invertibles_property
    and (Invertibles g).exp = $**          by Invertibles_property
    ==> 0 < ord x /\ x ** ord x = #e       by above
*)
val monoid_inv_order_property = store_thm(
  "monoid_inv_order_property",
  ``!g:'a monoid. FiniteMonoid g ==> !x. x IN G* ==> 0 < ord x /\ (x ** ord x = #e)``,
  ntac 4 strip_tac >>
  `FiniteGroup (Invertibles g)` by rw[finite_monoid_invertibles_is_finite_group] >>
  metis_tac[group_order_property, Invertibles_order, Invertibles_property]);

(*
This proof is quite complicated:
* The invertibles of monoid form a group.
* For a finite group, finite_group_Fermat |- !g a. FiniteGroup g /\ a IN G ==> (a ** CARD G = #e)
* Thus   a ** (CARD G - 1) = |/ a
*    ord ( |/ a) = ord (a ** (CARD G - 1)) * gcd (ord a) (CARD G - 1) = ord a
* because (ord a) divides (CARD G), gcd (ord a) (CARD G - 1) = 1, and ord ( |/ a) = ord a.
*)

(*
> group_inv_order |> ISPEC ``Invertibles g``;
val it = |- FiniteGroup (Invertibles g) ==> !x. x IN (Invertibles g).carrier ==>
     (order (Invertibles g) ((Invertibles g).inv x) = order (Invertibles g) x): thm
*)

(* Theorem: Monoid g /\ x IN G* ==> (ord ( |/ x) = ord x) *)
(* Proof:
   Note Group (Invertibles g)                  by monoid_invertibles_is_group
    and (Invertibles g).carrier = G*           by Invertibles_carrier
    ==> order (Invertibles g) ((Invertibles g).inv x)
      = order (Invertibles g) x                by group_inv_order
    But !x. order (Invertibles g) x = ord x    by Invertibles_order
    and (Invertibles g).inv x = |/ x           by Invertibles_inv
    ==> ord ( |/ x) = ord x                    by above
*)
val monoid_inv_order = store_thm(
  "monoid_inv_order",
  ``!(g:'a monoid) x. Monoid g /\ x IN G* ==> (ord ( |/ x) = ord x)``,
  rpt strip_tac >>
  `Group (Invertibles g)` by rw[monoid_invertibles_is_group] >>
  `(Invertibles g).carrier = G*` by rw[Invertibles_carrier] >>
  `(Invertibles g).inv x = |/ x` by metis_tac[Invertibles_inv] >>
  metis_tac[group_inv_order, Invertibles_order]);

(* ------------------------------------------------------------------------- *)
(* Application of Finite Group element order:                                *)
(* The generated subgroup by a group element.                                *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The Subgroup <a> of any element a of Group g.                             *)
(* ------------------------------------------------------------------------- *)

(* Define the generator group, the exponential group of an element a of group g *)
val Generated_def = Define`
  Generated g a : 'a group =
    <| carrier := {x | ?k. x = a ** k };
            op := g.op;
            id := g.id
     |>
`;
(*
- type_of ``Generated g a``;
> val it = ``:'a group`` : hol_type
*)


(* overload on generated group and its carrier *)
val _ = overload_on("gen", ``Generated g``);
val _ = overload_on("Gen", ``\a. (Generated g a).carrier``);

(* Theorem: x IN Gen a <=> ?n. x = a ** n *)
(* Proof: by Generated_def *)
val generated_element = store_thm(
  "generated_element",
  ``!g:'a group. !a x. x IN Gen a <=> ?n. x = a ** n``,
  rw[Generated_def]);

(* Theorem: ((gen a).op = g.op) /\ ((gen a).id = #e) *)
(* Proof: by Generated_def. *)
val generated_property = store_thm(
  "generated_property",
  ``!(g:'a group) a. ((gen a).op = g.op) /\ ((gen a).id = #e)``,
  rw[Generated_def]);

(* Theorem: !a. a IN G ==> (Gen a = IMAGE (g.exp a) univ(:num)) *)
(* Proof: by Generated_def, EXTENSION *)
val generated_carrier = store_thm(
  "generated_carrier",
  ``!(g:'a group) a. a IN G ==> (Gen a = IMAGE (g.exp a) univ(:num))``,
  rw[Generated_def, EXTENSION]);

(* Theorem: Group g ==> !x. x IN G ==> x IN (Gen x) *)
(* Proof: by Generated_def, group_exp_1 *)
val generated_gen_element = store_thm(
  "generated_gen_element",
  ``!g:'a group. Group g ==> !x. x IN G ==> x IN (Gen x)``,
  rw[Generated_def] >>
  metis_tac[group_exp_1]);

(* Theorem: #e IN (Gen a) *)
(* Proof:
   Note a ** 0 = #e    by group_exp_0
    ==> #e IN (Gen a)  by generated_element
*)
val generated_carrier_has_id = store_thm(
  "generated_carrier_has_id",
  ``!g:'a group. !a. #e IN (Gen a)``,
  metis_tac[generated_element, group_exp_0]);

(* Theorem: Group g ==> (Gen #e = {#e}) *)
(* Proof:
     Gen #e
   = {x | ?k. x = #e ** k}     by Generated_def
   = {x | x = #e}              by group_id_exp, Group g
   = {#e}                      by EXTENSION
*)
val generated_id_carrier = store_thm(
  "generated_id_carrier",
  ``!g:'a group. Group g ==> (Gen #e = {#e})``,
  rw[Generated_def, EXTENSION]);

(* Theorem: Group g ==> gen #e <= g *)
(* Proof:
   Note Gen #e = {#e}            by generated_id_carrier, Group g
   By subgroup_alt, this is to show:
   (1) Gen #e <> {}, true        by NOT_SING_EMPTY
   (2) (Gen #e) SUBSET G, true   by group_id_element, SUBSET_DEF
   (3) (gen #e).op = $*, true    by generated_property
   (4) (gen #e).id = #e, true    by generated_property
   (5) x IN (Gen #e) /\ y IN (Gen #e) ==> x * |/ y IN (Gen #e)
       Note x = #e /\ y = #e     by IN_SING
         so x * |/ y = #e        by group_inv_id, group_id_id
         or x * |/ y IN (Gen #e) by IN_SING
*)
val generated_id_subgroup = store_thm(
  "generated_id_subgroup",
  ``!g:'a group. Group g ==> gen #e <= g``,
  rw[generated_id_carrier, subgroup_alt, generated_property]);

(* Note for the next theorem:
   FINITE is required to have the order m, giving the inverse.
   INFINITE would require two generators: a and |/ a.
   For example, (Z, $+) is a group, but (gen 1 = naturals) is not a group.
   Also (gen 2 = multples of 2) is not a group, but (gen 2 -2) is a group.
   Indeed, Z = gen 1 -1, but our generated_def has only one generator.

   Can define |/a = a ** -1, but that would require exponents to be :int, not :num
*)

(* Theorem: For a FINITE group g, the generated group of a in G is a group *)
(* Proof:
   This is to show:
   (1) ?k''. a ** k * a ** k' = a ** k''   by group_exp_add
   (2) a ** k * a ** k' * a ** k'' = a ** k * (a ** k' * a ** k'')  by group_assoc
   (3) ?k. #e = a ** k                     by group_exp_0, a ** 0 = #e.
   (4) #e * a ** k = a ** k                by group_lid
   (5) ?y. (?k'. y = a ** k') /\ (y * a ** k = #e)
       There is m = ord a with the property 0 < m
                                           by group_order_pos
          |/ (a ** k)
        = ( |/a) ** k                      by group_exp_inv
        = (a ** (m-1)) ** k                by group_order_inv
        = a ** ((m-1) * k)                 by group_exp_mult
        Pick k' = (m-1) * k, and y = a ** k' = |/ (a ** k).
*)
val generated_group = store_thm(
  "generated_group",
  ``!(g:'a group) a. FiniteGroup g /\ a IN G ==> Group (gen a)``,
  rpt (stripDup[FiniteGroup_def]) >>
  rw_tac std_ss[group_def_alt, Generated_def, RES_FORALL_THM, GSPECIFICATION] >-
  metis_tac[group_exp_add] >-
  rw_tac std_ss[group_assoc, group_exp_element] >-
  metis_tac[group_exp_0] >-
  rw_tac std_ss[group_lid, group_exp_element] >>
  `0 < ord a` by rw[group_order_pos] >>
  metis_tac[group_order_inv, group_exp_inv, group_exp_mult, group_linv, group_exp_element]);

(* Theorem: Group g /\ a IN G ==> (Gen a) SUBSET G *)
(* Proof:
   x IN (Gen a) ==> ?n. x = a ** n          by Generated_def
   a IN G ==> a ** n IN G                   by group_exp_element
   Hence (Gen a) SUBSET G                   by SUBSET_DEF
*)
val generated_subset = store_thm(
  "generated_subset",
  ``!(g:'a group) a. Group g /\ a IN G ==> (Gen a) SUBSET G``,
  rw[Generated_def, SUBSET_DEF] >>
  rw[]);

(* Theorem: The generated group <a> for a IN G is subgroup of G. *)
(* Proof:
   Essentially this is to prove:
   (1) Group (gen a)              true by generated_group.
   (2) (Gen a) SUBSET G           true by generated_subset
   (3) gen a).op x y = x * y      true by Generated_def.
*)
val generated_subgroup = store_thm(
  "generated_subgroup",
  ``!(g:'a group) a. FiniteGroup g /\ a IN G ==> Subgroup (gen a) g``,
  rpt (stripDup[FiniteGroup_def]) >>
  rw_tac std_ss[Subgroup_def, SUBSET_DEF, GSPECIFICATION] >-
  rw_tac std_ss[generated_group] >-
  metis_tac[generated_subset, SUBSET_DEF] >>
  rw_tac std_ss[Generated_def]);

(* Theorem: FiniteGroup g /\ a IN G ==> FINITE (Gen a) *)
(* Proof:
   FiniteGroup g ==> Group g /\ FINITE G  by FiniteGroup_def
   Group g ==> (Gen a) SUBSET G           by generated_subset
   Hence FINITE (Gen a)                   by SUBSET_FINITE
*)
val generated_group_finite = store_thm(
  "generated_group_finite",
  ``!(g:'a group) a. FiniteGroup g /\ a IN G ==> FINITE (Gen a)``,
  metis_tac[FiniteGroup_def, generated_subset, SUBSET_FINITE]);

(* Theorem: FiniteGroup g /\ a IN G ==> FiniteGroup (gen a) *)
(* Proof:
   FiniteGroup g ==> FINITE (Gen a)   by generated_group_finite
   FiniteGroup g ==> Group (gen a)    by generated_group
   and FiniteGroup (gen a)            by FiniteGroup_def
*)
val generated_finite_group = store_thm(
  "generated_finite_group",
  ``!(g:'a group) a. FiniteGroup g /\ a IN G ==> FiniteGroup (gen a)``,
  rw[FiniteGroup_def, generated_group, generated_group_finite]);

(* Theorem: a IN G /\ z IN (Gen a) ==> !n. (gen a).exp z n = z ** n *)
(* Proof:
     (gen a).exp z n
   = FUNPOW ((gen a).op z) n (gen a).id    by monoid_exp_def
   = FUNPOW (g.op z) n (g.id)              by Generated_def
   = g.exp z n                             by monoid_exp_def
   = z ** n                                by notation
*)
val generated_exp = store_thm(
  "generated_exp",
  ``!g:'a group. !a z. a IN G /\ z IN (Gen a) ==> !n. (gen a).exp z n = z ** n``,
  rw[Generated_def, monoid_exp_def]);

(* Theorem: There is a bijection from (count m) to (gen a), where m = ord x and 0 < m *)
(* Proof:
   The map (\n. a ** n) from (count m) to (gen a) is bijective:
   (1) surjective because x in (gen a) means ?k. x = a ** k = a ** (k mod m), so take n = k mod m.
       This is group_exp_mod.
   (2) injective because a ** m = a ** n ==> m = n,
       otherwise a ** (m-n) = #e, contradicting minimal nature of m.
       This is group_order_unique.

   Essentially this is to prove:
   (1) a IN G /\ n < ord a ==> ?k. a ** n = a ** k,             just take k = n.
   (2) n < ord a /\ n' < ord a /\ a ** n = a ** n' ==> n = n',  true by group_order_unique
   (3) same as (1)
   (4) a IN G ==> ?n. n < ord a /\ (a ** n = a ** k),           true by group_exp_mod, n = k mod order.
*)
val group_order_to_generated_bij = store_thm(
  "group_order_to_generated_bij",
  ``!(g:'a group) a. Group g /\ a IN G /\ 0 < ord a ==> BIJ (\n. a ** n) (count (ord a)) (Gen a)``,
  rpt strip_tac >>
  rw[BIJ_DEF, SURJ_DEF, INJ_DEF, Generated_def] >-
  metis_tac[] >-
  metis_tac[group_order_unique] >-
  metis_tac[] >>
  metis_tac[group_exp_mod, MOD_LESS]);

(* Theorem: The order of the generated_subgroup is the order of its element *)
(* Proof:
   Note BIJ (\n. a**n) (count (ord a)) (Gen a)  by group_order_to_generated_bij
    and FINITE (count (ord a))                  by FINITE_COUNT
    and CARD (count (ord a)) = ord a            by CARD_COUNT
   Thus CARD (Gen a) = ord a                    by FINITE_BIJ
*)
val generated_group_card = store_thm(
  "generated_group_card",
  ``!(g:'a group) a. Group g /\ a IN G /\ 0 < ord a ==> (CARD (Gen a) = ord a)``,
  metis_tac[group_order_to_generated_bij, FINITE_BIJ, FINITE_COUNT, CARD_COUNT]);

(* Theorem: Group g ==> !a. a IN G /\ 0 < ord a ==> (Gen a = IMAGE (\j. a ** j) (count (ord a))) *)
(* Proof:
   By generated_carrier, IN_IMAGE and IN_COUNT, this is to show:
   (1) a IN G /\ 0 < ord a ==> ?j. (a ** x' = a ** j) /\ j < ord a
       Take j = x' MOD (ord a).
       Then j < ord a                by MOD_LESS
        and a ** x' = a ** j         by group_exp_mod
   (2) ?x'. a ** j = a ** x'
       Take x' = j.
*)
val generated_carrier_as_image = store_thm(
  "generated_carrier_as_image",
  ``!g:'a group. Group g ==> !a. a IN G /\ 0 < ord a ==>
               (Gen a = IMAGE (\j. a ** j) (count (ord a)))``,
  rw[generated_carrier, EXTENSION, EQ_IMP_THM] >-
  metis_tac[group_exp_mod, MOD_LESS] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* Group Order and Divisibility                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: For FiniteGroup g g, if x IN G, (ord x) divides (CARD G) *)
(* Proof:
   By applying Lagrange theorem to the generated subgroup of the element x:
   Note gen x <= g              by generated_subgroup
   Thus CARD (Gen x)) (CARD G)  by Lagrange_thm
    Now 0 < ord x               by group_order_pos
    and CARD (Gen x)) = ord x   by generated_group_card
   The result follows.
*)
val group_order_divides = store_thm(
  "group_order_divides",
  ``!g:'a group. FiniteGroup g ==> !x. x IN G ==> (ord x) divides (CARD G)``,
  rpt (stripDup[FiniteGroup_def]) >>
  `gen x <= g` by rw[generated_subgroup] >>
  `(CARD (Gen x)) divides (CARD G)` by rw[Lagrange_thm] >>
  metis_tac[generated_group_card, group_order_pos]);

(* Theorem: For FiniteGroup g, a IN G ==> a ** (CARD g) = #e *)
(* Proof:
   Note (ord a) divides (CARD G)     by group_order_divides
     or ?k. CARD G = (ord a) * k     by divides_def, MULT_COMM

     a ** (CARD G)
   = a ** ((ord a) * k)         by above
   = (a ** (ord a)) ** k        by group_exp_mult
   = (#e) ** k                  by order_property
   = #e                         by group_id_exp
*)
val finite_group_Fermat = store_thm(
  "finite_group_Fermat",
  ``!(g:'a group) a. FiniteGroup g /\ a IN G ==> (a ** (CARD G) = #e)``,
  rpt (stripDup[FiniteGroup_def]) >>
  `(ord a) divides (CARD G)` by rw[group_order_divides] >>
  `?k. CARD G = (ord a) * k` by rw[GSYM divides_def] >>
  metis_tac[group_exp_mult, group_id_exp, order_property]);

(* Theorem: x IN (Gen a) ==> (x ** (CARD (Gen a)) = #e) *)
(* Proof:
   Given FiniteGroup g /\ a IN G
      so FiniteGroup (gen a)             by generated_finite_group
     ==> (gen a).exp x (CARD (Gen a)) = (gen a).id
                                         by finite_group_Fermat
     Now (gen a).id = #e                 by generated_property
     and !n. (gen a).exp x n = x ** n    by generated_exp
   The result follows.
*)
val generated_Fermat = store_thm(
  "generated_Fermat",
  ``!(g:'a group) a. FiniteGroup g /\ a IN G ==>
   !x. x IN (Gen a) ==> (x ** (CARD (Gen a)) = #e)``,
  rpt strip_tac >>
  `FiniteGroup (gen a)` by rw[generated_finite_group] >>
  `(gen a).id = #e` by rw[generated_property] >>
  `!n. (gen a).exp x n = x ** n` by rw[generated_exp] >>
  metis_tac[finite_group_Fermat]);

(* Theorem: Group g /\ x IN G /\ 0 < ord x ==>
           !n m. (x ** n = x ** m) <=> (n MOD (ord x) = m MOD (ord x)) *)
(* Proof:
   Note x ** n = x ** (n MOD (ord x))    by group_exp_mod
    and x ** m = x ** (m MOD (ord x))    by group_exp_mod
   If part: x ** n = x ** m ==> n MOD ord x = m MOD ord x
      Since n MOD ord x < ord x          by MOD_LESS
        and m MOD ord x < ord x          by MOD_LESS
        ==> n MOD ord x = m MOD ord x    by group_exp_equal
   Only-if part: trivially true.
*)
val group_exp_eq_condition = store_thm(
  "group_exp_eq_condition",
  ``!(g:'a group) x. Group g /\ x IN G /\ 0 < ord x ==>
     !n m. (x ** n = x ** m) <=> (n MOD (ord x) = m MOD (ord x))``,
  metis_tac[group_exp_mod, group_exp_equal, MOD_LESS]);

(* ------------------------------------------------------------------------- *)
(* Finite Group Order                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Group g /\ x IN G /\ 0 < ord x ==>
            !k. (ord (x ** k) = ord x) <=> coprime k (ord x) *)
(* Proof:
   If part: ord (x ** k) = ord x ==> coprime k (ord x)
       Note ord (x ** k) * gcd k (ord x) = ord x       by group_order_power, GCD_SYM
         or      (ord x) * gcd k (ord x) = ord x       by ord (x ** k) = ord x
         or      (ord x) * gcd k (ord x) = ord x * 1   by MULT_RIGHT_1
        Therefore gcd k (ord x) = 1                    by MULT_RIGHT_ID
               or coprime k (ord x)                    by notation
   Only-if part: coprime k (ord x) ==> ord (x ** k) = ord x
       Note ord (x ** k) * gcd k (ord x) = ord x       by group_order_power, GCD_SYM
        but coprime k (ord x) means gcd k (ord x) = 1  by notation
      Hence ord (x ** k) = ord x                       by MULT_RIGHT_1
*)
val group_order_power_eq_order = store_thm(
  "group_order_power_eq_order",
  ``!(g:'a group) x. Group g /\ x IN G /\ 0 < ord x ==>
   !k. (ord (x ** k) = ord x) <=> coprime k (ord x)``,
  rpt strip_tac >>
  `ord (x ** k) * gcd k (ord x) = ord x` by metis_tac[group_order_power, GCD_SYM] >>
  rw[EQ_IMP_THM] >-
  metis_tac[MULT_RIGHT_ID] >>
  fs[]);

(* Theorem: Group g /\ x IN G /\ 0 < ord x /\ n divides (ord x) ==>
            (ord (x ** ((ord x) DIV n)) = n) *)
(* Proof:
   Let m = ord x, k = m DIV n.
   Note n divides m ==> 0 < n        by ZERO_DIVIDES, m <> 0
    and n divides m ==> m = k * n    by DIVIDES_EQN, 0 < n
   thus k <> 0                       by MULT_0, m <> 0
    Now ord (x ** k) * gcd m k = m   by group_order_power
    but m = n * k                    by MULT_COMM
     so gcd m k = k                  by GCD_MULTIPLE_ALT
  Hence ord (x ** k) = n             by EQ_MULT_RCANCEL
*)
val group_order_exp_cofactor = store_thm(
  "group_order_exp_cofactor",
  ``!(g:'a group) x n. Group g /\ x IN G /\ 0 < ord x /\ n divides (ord x) ==>
        (ord (x ** ((ord x) DIV n)) = n)``,
  rpt strip_tac >>
  qabbrev_tac `m = ord x` >>
  qabbrev_tac `k = m DIV n` >>
  `ord (x ** k) * gcd m k = m` by rw[group_order_power, Abbr`m`] >>
  `m <> 0` by decide_tac >>
  `n <> 0` by metis_tac[ZERO_DIVIDES] >>
  `m = k * n` by rw[GSYM DIVIDES_EQN, Abbr`k`] >>
  `_ = n * k` by rw[MULT_COMM] >>
  `k <> 0` by metis_tac[MULT_0] >>
  metis_tac[GCD_MULTIPLE_ALT, EQ_MULT_RCANCEL]);

(* ------------------------------------------------------------------------- *)
(* Roots of Unity form a Subgroup                                            *)
(* ------------------------------------------------------------------------- *)

(* Define n-th roots of unity *)
val roots_of_unity_def = Define`
  roots_of_unity (g:'a group) (n:num):'a group =
     <| carrier := {x | x IN G /\ (x ** n = #e)};
             op := g.op;
             id := #e
      |>
`;
(* Overload root of unity *)
val _ = overload_on ("uroots", ``roots_of_unity g``);

(*
> roots_of_unity_def;
val it = |- !g n. uroots n = <|carrier := {x | x IN G /\ (x ** n = #e)}; op := $*; id := #e|>: thm
*)

(* Theorem: x IN (uroots n).carrier <=> x IN G /\ (x ** n = #e) *)
(* Proof: by roots_of_unity_def *)
val roots_of_unity_element = store_thm(
  "roots_of_unity_element",
  ``!g:'a group. !n x. x IN (uroots n).carrier <=> x IN G /\ (x ** n = #e)``,
  rw[roots_of_unity_def]);

(* Theorem: (uroots n).carrier SUBSET G *)
(* Proof: by roots_of_unity_element, SUBSET_DEF. *)
val roots_of_unity_subset = store_thm(
  "roots_of_unity_subset",
  ``!g:'a group. !n. (uroots n).carrier SUBSET G``,
  rw[roots_of_unity_element, SUBSET_DEF]);

(* Theorem: (uroots 0).carrier = G *)
(* Proof:
   (uroots 0).carrier = {x | x IN G /\ (x ** 0 = #e)}   by roots_of_unity_def
   Since   x ** 0 = #e                                  by group_exp_0
   (uroots 0).carrier = {x | x IN G /\ T} = G           by EXTENSION
*)
val roots_of_unity_0 = store_thm(
  "roots_of_unity_0",
  ``!g:'a group. (uroots 0).carrier = G``,
  rw[roots_of_unity_def]);

(* Theorem: #e IN (uroots n).carrier *)
(* Proof: by group_id_exp. *)
val group_uroots_has_id = store_thm(
  "group_uroots_has_id",
  ``!g:'a group. Group g ==> !n. #e IN (uroots n).carrier``,
  rw[roots_of_unity_def]);

(* Theorem: AbelianGroup g ==> uroots n <= g *)
(* Proof:
   By subgroup_alt, roots_of_unity_def, this is to show:
   (1) ?x. x IN G /\ (x ** n = #e)
       Since #e IN G   by group_id_element
       This is true    by group_id_exp
   (2) x ** n = #e /\ y ** n = #e ==> (x * |/ y) ** n = #e
         (x * |/ y) ** n
       = (x ** n) * ( |/ y) ** n   by group_comm_op_exp
       = (x ** n) * |/ (y ** n)    by group_inv_exp
       = #e * |/ #e                by x, y IN uroots n
       = #e * #e                   by group_inv_exp
       = #e                        by group_id_id
*)
val group_uroots_subgroup = store_thm(
  "group_uroots_subgroup",
  ``!g:'a group. AbelianGroup g ==> !n. uroots n <= g``,
  rw[AbelianGroup_def] >>
  rw[subgroup_alt, roots_of_unity_def, EXTENSION, SUBSET_DEF] >-
  metis_tac[group_id_element, group_id_exp] >>
  rw[group_inv_exp, group_inv_id, group_comm_op_exp]);

(* Theorem: AbelianGroup g ==> !n. Group (uroots n) *)
(* Proof: by group_uroots_subgroup, Subgroup_def *)
Theorem group_uroots_group:
  !g:'a group. AbelianGroup g ==> !n. Group (uroots n)
Proof
  metis_tac[group_uroots_subgroup, Subgroup_def]
QED

(* Is this true: Group g ==> !n. Group (uroots n) *)
(* No? *)

(* Theorem: AbelianGroup g ==> !n. Group (uroots n) *)
(* Proof:
   By roots_of_unity_def, group_def_alt, this is to show:
   (1) x ** n = #e /\ y ** n = #e ==> (x * y) ** n = #e,  true by group_comm_op_exp
   (2) z * (x * y) = x * (y * z)
         z * (x * y)
       = (z * x) * y            by group_assoc
       = (x * z) * y            by commutativity condition
       = x * (z * y)            by group_assoc
       = x * (y * z)            by commutativity condition
   (3) x ** n = #e ==> ?y. (y IN G /\ (y ** n = #e)) /\ (y * x = #e)
       Let m = ord x.
       Then m divides n         by group_order_divides_exp
       Note ord ( |/ x) = m     by group_inv_order
       Thus ( |/ x) ** n = #e   by group_order_divides_exp
       Take y = |/ x, then true by group_linv
*)
Theorem group_uroots_group[allow_rebind]:
  !g:'a group. AbelianGroup g ==> !n. Group (uroots n)
Proof
  rw[AbelianGroup_def] >>
  rw[roots_of_unity_def, group_def_alt]
  >- rw[group_comm_op_exp]
  >- metis_tac[group_assoc] >>
  metis_tac[group_order_divides_exp, group_inv_order, group_linv,
            group_inv_element]
QED

(* ------------------------------------------------------------------------- *)
(* Subgroup generated by a subset of a Group.                                *)
(* ------------------------------------------------------------------------- *)

(* Define the group generated by a subset of the group carrier *)
val Generated_subset_def = Define`
    Generated_subset (g:'a group) (s:'a -> bool) =
        <|carrier := BIGINTER (IMAGE (\h. H) {h | h <= g /\ s SUBSET H}); op := g.op; id := #e|>
`;
(* Note: this is the minimal subgroup containing the subset. *)
(* Similar to subgroup_big_intersect_def in subgroup theory. *)
val _ = overload_on("gen_set", ``Generated_subset (g:'a group)``);

(* Theorem: ((gen_set s).carrier = BIGINTER (IMAGE (\h. H) {h | h <= g /\ s SUBSET H})) /\
            ((gen_set s).op = g.op) /\ ((gen_set s).id = #e) *)
(* Proof: by Generated_subset_def *)
val Generated_subset_property = store_thm(
  "Generated_subset_property",
  ``!(g:'a group) s. ((gen_set s).carrier = BIGINTER (IMAGE (\h. H) {h | h <= g /\ s SUBSET H})) /\
                    ((gen_set s).op = g.op) /\ ((gen_set s).id = #e)``,
  rw[Generated_subset_def]);

(* Theorem: s SUBSET (gen_set s).carrier *)
(* Proof: by Generated_subset_def, SUBSET_DEF *)
val Generated_subset_has_set = store_thm(
  "Generated_subset_has_set",
  ``!(g:'a group) s. s SUBSET (gen_set s).carrier``,
  rw[Generated_subset_def, SUBSET_DEF] >>
  simp[]);

(* Theorem: Group g /\ s SUBSET G ==> (gen_set s).carrier SUBSET G *)
(* Proof:
   By Generated_subset_def, this is to show:
      BIGINTER (IMAGE (\h. H) {h | h <= g /\ s SUBSET H}) SUBSET G
   By BIGINTER_SUBSET, this is to show:
      ?t. t IN IMAGE (\h. H) {h | h <= g /\ s SUBSET H} /\ t SUBSET G
   By IN_IMAGE, this is,
      ?t. (?h. t = H /\ h <= g /\ s SUBSET H) /\ t SUBSET G
   or ?h. h <= g /\ s SUBSET H     by subgroup_carrier_subset
   Take h = g,
   Then g <= g                     by subgroup_refl
    and s SUBSET G                 by given
*)
Theorem Generated_subset_subset:
  !(g:'a group) s. Group g /\ s SUBSET G ==> (gen_set s).carrier SUBSET G
Proof
  rw[Generated_subset_def] >>
  irule BIGINTER_SUBSET >>
  csimp[subgroup_carrier_subset, PULL_EXISTS] >>
  metis_tac[subgroup_refl]
QED

(* Theorem: Group g /\ s SUBSET G ==> Group (gen_set s) *)
(* Proof:
   Let t = {h | h <= g /\ s SUBSET H}.
   By group_def_alt, Generated_subset_def, this is to show:
   (1) h IN t ==> x * y IN H
       Note h <= g                by definition of t
       Thus x IN H /\ y IN H      by implication
        ==> h.op x y IN H         by subgroup_property, group_op_element
         or x * y IN H            by subgroup_property
   (2) x * y * z = x * (y * z)
       Note g <= g                       by subgroup_refl
         so g IN t                       by definition of t
       Thus x IN G /\ y IN G /\ z IN G   by implication
       The result follows                by group_assoc
   (3) h IN t ==> #e IN H
       Note h <= g                by definition of t
        ==> h.id IN H             by subgroup_property, group_id_element
         or #e IN H               by subgroup_id
   (4) #e * x = x
       Note g <= g                by subgroup_refl
         so g IN t                by definition of t
       Thus x IN G                by implication
       The result follows         by group_id
   (5) ?y. (!P. (?h. (P = H) /\ h IN {h | h <= g /\ s SUBSET H}) ==> y IN P) /\ (y * x = #e)
       Note g <= g                by subgroup_refl
         so g IN t                by definition of t
       Thus x IN G                by implication
        ==> |/ x IN G             by group_inv_element
        and ( |/ x) * x = #e      by group_linv
       Let y = |/ x.
       Need to show: h IN t ==> y IN H.
       But h IN t ==> h <= g      by definition of t
       Thus x IN H                by implication
         so h.inv x IN H          by subgroup_property, group_inv_element
         or |/ x = y IN H         by subgroup_inv
*)
val Generated_subset_group = store_thm(
  "Generated_subset_group",
  ``!(g:'a group) s. Group g /\ s SUBSET G ==> Group (gen_set s)``,
  rpt strip_tac >>
  rw_tac std_ss[group_def_alt, Generated_subset_def, IN_BIGINTER, IN_IMAGE] >| [
    `h <= g` by fs[] >>
    `x IN H /\ y IN H` by metis_tac[] >>
    metis_tac[subgroup_property, group_op_element],
    `g <= g` by rw[subgroup_refl] >>
    `g IN {h | h <= g /\ s SUBSET H}` by rw[] >>
    `x IN G /\ y IN G /\ z IN G` by metis_tac[] >>
    rw[group_assoc],
    `h <= g` by fs[] >>
    metis_tac[subgroup_property, subgroup_id, group_id_element],
    `g <= g` by rw[subgroup_refl] >>
    `g IN {h | h <= g /\ s SUBSET H}` by rw[] >>
    `x IN G` by metis_tac[] >>
    rw[],
    `g <= g` by rw[subgroup_refl] >>
    `g IN {h | h <= g /\ s SUBSET H}` by rw[] >>
    `x IN G` by metis_tac[] >>
    `|/ x IN G` by rw[] >>
    `( |/ x) * x = #e` by rw[] >>
    qexists_tac `|/ x` >>
    rw[] >>
    `h IN {h | h <= g /\ s SUBSET H}` by rw[] >>
    `x IN H` by metis_tac[] >>
    metis_tac[subgroup_property, subgroup_inv, group_inv_element]
  ]);

(* Theorem: Group g /\ s SUBSET G ==> (gen_set s) <= g *)
(* Proof:
   By Subgroup_def, this is to show:
   (1) Group (gen_set s), true              by Generated_subset_group
   (2) (gen_set s).carrier SUBSET G, true   by Generated_subset_subset
   (3) (gen_set s).op = $*, true            by Generated_subset_property
*)
val Generated_subset_subgroup = store_thm(
  "Generated_subset_subgroup",
  ``!(g:'a group) s. Group g /\ s SUBSET G ==> (gen_set s) <= g``,
  rw[Subgroup_def] >-
  rw[Generated_subset_group] >-
  rw[Generated_subset_subset] >>
  rw[Generated_subset_property]);

(* Theorem: Group g /\ s SUBSET G ==> (gen_set s) <= g *)
(* Proof: by Generated_subset_def, monoid_exp_def, FUN_EQ_THM *)
val Generated_subset_exp = store_thm(
  "Generated_subset_exp",
  ``!(g:'a group) s. (gen_set s).exp = g.exp``,
  rw[Generated_subset_def, monoid_exp_def, FUN_EQ_THM]);

(* Theorem: FiniteGroup g /\ a IN G ==> (gen_set (Gen a) = gen a) *)
(* Proof:
   By Generated_def, Generated_subset_def, SUBSET_DEF, EXTENSION,
   this is to show:
   (1) a IN G /\
       !P. (?h. (!x. (x IN P ==> x IN H) /\ (x IN H ==> x IN P)) /\
                h <= g /\ !x. (?k. x = a ** k) ==> x IN H) ==> x IN P
       ==> ?k. x = a ** k
       Take P = Gen a, and h = gen a.
       Note h <= g             by generated_subgroup
        and ?k. x = a ** k     by generated_element
       Take this k, the result follows.
   (2) a IN G /\ !x. (?k. x = a ** k) ==> x IN H /\
                 !x'. (x' IN P ==> x' IN H) /\ (x' IN H ==> x' IN P)
       ==> a ** k IN P
       Let x = a ** k.
       Note x IN H       by the first implication,
       Thus x IN P       by the second implication.
*)
val Generated_subset_gen = store_thm(
  "Generated_subset_gen",
  ``!(g:'a group) a. FiniteGroup g /\ a IN G ==> (gen_set (Gen a) = gen a)``,
  rpt (stripDup[FiniteGroup_def]) >>
  rw[Generated_def, Generated_subset_def, SUBSET_DEF, EXTENSION] >>
  rw[EQ_IMP_THM] >| [
    last_x_assum (qspecl_then [`Gen a`] strip_assume_tac) >>
    `gen a <= g` by rw[generated_subgroup] >>
    metis_tac[generated_element],
    metis_tac[]
  ]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
