(* ------------------------------------------------------------------------- *)
(* Finite Field: Unity Polynomial                                            *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ffUnity";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open arithmeticTheory pred_setTheory listTheory dividesTheory gcdTheory
     gcdsetTheory numberTheory combinatoricsTheory primeTheory;

open ffPolyTheory ffAdvancedTheory ffBasicTheory;
open ffCycloTheory;
open ffMasterTheory;

(* Open theories in order *)
open monoidTheory groupTheory ringTheory fieldTheory;
open groupOrderTheory;
open subgroupTheory;

open groupInstancesTheory ringInstancesTheory fieldInstancesTheory;
open groupCyclicTheory;

(* (* val _ = load "ringBinomialTheory"; *) *)
open ringBinomialTheory;
open ringDividesTheory;
open ringIdealTheory;
open ringUnitTheory;

open fieldOrderTheory;
open fieldMapTheory;

(* Get polynomial theory of Ring *)
open polynomialTheory polyWeakTheory polyRingTheory polyDivisionTheory polyBinomialTheory;

(* (* val _ = load "polyFieldModuloTheory"; *) *)
open polyFieldTheory;
open polyFieldDivisionTheory;
open polyFieldModuloTheory;
open polyRingModuloTheory;
open polyModuloRingTheory;

open polyEvalTheory;
open polyRootTheory;

(* (* val _ = load "polyGCDTheory"; *) *)
open polyDividesTheory;
open polyMonicTheory;
open polyProductTheory;
open polyIrreducibleTheory;
open polyGCDTheory;

(* val _ = load "polyCyclicTheory"; *)
open polyCyclicTheory; (* for poly_unity_irreducible_factor_exists *)

(* ------------------------------------------------------------------------- *)
(* Finite Field Unity Polynomial Documentation                               *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported):

   Unity Factor of Master Polynomial:
   poly_master_by_poly_unity   |- !r. FiniteField r ==> (master (CARD R) = X * unity (CARD R+))

   Roots of Unity of Field Order:
   poly_unity_order_has_root          |- !r. Field r ==> !x. x IN R ==> root (unity (forder x)) x
   poly_unity_order_has_all_roots     |- !r. Field r ==> !x. x IN R /\ x <> #0 ==>
                                         !j. root (unity (forder x)) (x ** j)
   poly_unity_roots_generator         |- !r. FiniteField r ==> !z. z IN R /\ z <> #0 ==>
                                             (roots (unity (forder z)) = (Generated f* z).carrier)
   poly_roots_of_unity_by_generator   |- !r. FiniteField r ==> !z. z IN R /\ z <> #0 ==>
                                             (roots (unity (forder z)) = (Generated f* z).carrier)

   poly_unity_roots_as_image   |- !r. FiniteField r ==> !z. z IN R /\ z <> #0 ==>
                                      (roots (unity (forder z)) = IMAGE (\j. z ** j) (count (forder z)))
   poly_unity_order_roots_bij  |- !r. FiniteField r ==> !z. z IN R /\ z <> #0 ==>
                                      BIJ (\j. z ** j) (count (forder z)) (roots (unity (forder z)))

   Field Equal Order Structure (continued):
   poly_unity_roots_eqn  |- !r. Field r ==> !n. 0 < n ==>
                            !z. z IN R /\ (forder z = n) ==> (roots (unity n) = IMAGE (\j. z ** j) (count n))
   field_order_equal_eqn |- !r. Field r ==> !n. 0 < n ==>
                            !x. x IN forder_eq n ==> (forder_eq n = IMAGE (\j. x ** j) (coprimes n))
   field_order_equal_card_eqn  |- !r. Field r ==> !n. 0 < n ==>
                                      (CARD (forder_eq n) = 0) \/ (CARD (forder_eq n) = phi n)
   field_order_equal_nonempty  |- !r. FiniteField r ==>
                                  !n. 0 < n ==> (forder_eq n <> {} <=> n divides CARD R+)
   finite_field_mult_group_is_cyclic    |- !r. FiniteField r ==> cyclic f*

   Finite Field Orders dependent on Unity:
   field_order_eq_order             |- !r. FiniteField r ==> !x y. x IN R /\ y IN R /\
                                           (forder x = forder y) ==> ?j. y = x ** j
   field_nonzero_order_eq_order     |- !r. FiniteField r ==> !x. x IN R /\ x <> #0 ==>
                                       !y. y IN R /\ (forder x = forder y) ==> ?j. j < forder x /\ (y = x ** j)
   field_order_equal_card           |- !r. FiniteField r ==> !n. 0 < n ==>
                                           (CARD (forder_eq n) = if n divides CARD R+ then phi n else 0)
   field_order_equals_coprimes_bij  |- !r. FiniteField r ==> !n x. 0 < n /\ x IN forder_eq n ==>
                                           BIJ (\j. x ** j) (coprimes n) (forder_eq n)
   field_order_equal_card_choices   |- !r. FiniteField r ==> !n. 0 < n ==>
                                           (CARD (forder_eq n) = 0) \/ (CARD (forder_eq n) = phi n)
   field_orders_card                |- !r. FiniteField r ==>
                                       !n. CARD (orders f* n) = if n divides CARD R+ then phi n else 0
   field_orders_subset_unity_roots  |- !r. FiniteField r ==>
                                       !m n. m divides n ==> orders f* m SUBSET roots (unity n)
   field_orders_eq                  |- !r. FiniteField r ==> !n. n divides CARD R+ ==>
                                       !m. (orders f* n = orders f* m) <=> (m = n)
   subfield_orders_equal            |- !r s. FiniteField r /\ s <<= r ==>
                                       !n. n divides CARD B* ==> (orders s* n = orders f* n)
   field_order_divides_iff          |- !r. FiniteField r ==> !n. (?x. x IN R+ /\ (forder x = n)) <=> n divides CARD R+
   field_order_exists               |- !r. FiniteField r ==> !n. (?x. x IN R+ /\ (forder x = n)) <=> n divides CARD R+


   Unity Polynomial as Product of Cyclotomic Polynomials:
   poly_cyclo_eq                    |- !r. FiniteField r ==> !n. n divides CARD R+ ==>
                                       !m. (cyclo m = cyclo n) <=> (m = n)
   poly_cyclo_deg_eqn               |- !r. FiniteField r ==>
                                       !n. deg (cyclo n) = if n divides CARD R+ then phi n else 0
   poly_cyclo_eq_poly_one           |- !r. FiniteField r ==> !n. ~(n divides CARD R+) ==> (cyclo n = |1|)
   poly_cyclo_divides_poly_unity    |- !r. FiniteField r ==> !m n. m divides n ==> cyclo m pdivides unity n
   poly_unity_eq_poly_cyclo_product |- !r. FiniteField r ==> !n. n divides CARD R+ ==>
                                           (unity n = PPIMAGE cyclo (divisors n))
   poly_unity_eq_poly_cyclo_product_special
                                    |- !r. FiniteField r ==> (unity (CARD R+) = PPIMAGE cyclo (divisors (CARD R+)))
   poly_unity_eq_poly_cyclo_product_special_alt
                                    |- !r. FiniteField r ==> (unity (CARD R+) = PPROD {cyclo n | n | n IN divisors (CARD R+)})
   poly_unity_eq_poly_cyclo_product_alt
                                    |- !r n. FiniteField r /\ n divides CARD R+ ==> (unity n = PPROD {cyclo k | k IN divisors n})

   Roots of Unity is a Subgroup:
   poly_unity_roots_subgroup  |- !r. Field r ==> !n. 0 < n ==> subset_group f* (roots (unity n)) <= f*

   Subfield Classification:
   finite_field_subfield_exists_by_field_order
                |- !r. FiniteField r ==> !n. (?s. s <<= r /\ (fdim s = n)) <=>
                                              ?x. x IN R+ /\ (forder x = char r ** n - 1)
   finite_field_subfield_exists_by_field_orders
                |- !r. FiniteField r ==> !n. (?s. s <<= r /\ (fdim s = n)) <=>
                                              orders f* (char r ** n - 1) <> {}
   finite_field_subfield_existence_alt
                |- !r. FiniteField r ==> !n. (?s. s <<= r /\ (fdim s = n)) <=> n divides fdim r

   Unity Polynomial as Modulus:
   poly_unity_pmod_eqn    |- !r. Ring r ==> !k. (X ** k == |1|) (pm (unity k))
   poly_unity_exp_mod     |- !r. Ring r ==> !k. 0 < k ==>
                             !m. (X ** m == X ** (m MOD k)) (pm (unity k))
   poly_unity_exp_mod_eq  |- !r. Ring r ==> !k. 0 < k ==>
                             !n m. (n MOD k = m MOD k) ==> (X ** n == X ** m) (pm (unity k))
   poly_unity_irreducible_factor_not_X
                          |- !r. Field r ==> !n. 0 < n ==>
                                             !h. mifactor h (unity n) ==> h <> X
   poly_unity_irreducible_factor_deg_1
                          |- !r. Field r ==> !n h. mifactor h (unity n) /\ (deg h = 1) ==>
                                             ?c. c IN R /\ (h = factor c) /\ (c ** n = #1)
   poly_unity_irreducible_factor_with_order
                          |- !r n. Field r /\ 1 < n /\ n < char r ==>
                               ?z. mifactor z (unity n) /\ forderz X divides n

   Roots of Unity:
   poly_unity_peval_root_nonzero
                          |- !r z. Ring r /\ pmonic z ==>
                             !n p. 0 < n /\ poly p /\ (peval (unity n) p == |0|) (pm z) ==> p <> |0|
   poly_roots_of_unity_element
                          |- !r z. Field r /\ monic z /\ ipoly z ==>
                             !p n. p IN (roots_of_unity ((PolyModRing r z).prod excluding |0|) n).carrier <=>
                                   poly p /\ p <> |0| /\ deg p < deg z /\ (peval (unity n) p == |0|) (pm z)
   poly_roots_of_unity_carrier
                          |- !r z. Field r /\ monic z /\ ipoly z ==> !n. 0 < n ==>
                                 ((roots_of_unity ((PolyModRing r z).prod excluding |0|) n).carrier =
                                  poly_roots (PolyModRing r z) (lift (unity n)))

   Unity primitive roots:
   poly_primitive_root_of_unity_exists
                          |- !r. FiniteField r ==>
                             !n z. 1 < n /\ n < char r /\ (z = unity n) ==>
                             ?h t. mifactor h z /\ poly t /\ t <> |0| /\ deg t < deg h /\
                                   poly_root (PolyModRing r h) (lift z) t /\
                                   (order ((PolyModRing r h).prod excluding |0|) t =
                                    CARD (poly_roots (PolyModRing r h) (lift z)))

*)

(* ------------------------------------------------------------------------- *)
(* Unity Factor of Master Polynomial                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==> (master (CARD R) = X * unity (CARD R+)) *)
(* Proof:
   Note CARD R = SUC (CARD R+)                  by finite_field_carrier_card
   Thus master (CARD R) = X * unity (CARD R+)   by poly_master_factors_alt
*)
val poly_master_by_poly_unity = store_thm(
  "poly_master_by_poly_unity",
  ``!r:'a field. FiniteField r ==> (master (CARD R) = X * unity (CARD R+))``,
  rpt (stripDup[FiniteField_def]) >>
  `CARD R = SUC (CARD R+)` by rw[finite_field_carrier_card] >>
  rw_tac std_ss[poly_master_factors_alt, field_is_ring]);

(* Note:
polyGCDTheory.poly_master_factors;
val it = |- !r. Ring r ==> !n. 0 < n ==> (master n = X * unity (n - 1)): thm
AKSmasterTheory.poly_ff_master_has_factor_X;
val it = |- !r. FiniteRing r ==> !n. ff_master n = X * unity (CARD R ** n - 1): thm
*)

(* ------------------------------------------------------------------------- *)
(* Roots of Unity of Field Order                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r ==> !x. x IN R ==> root (unity (forder x)) x *)
(* Proof:
   Let k = forder x.
   Since x ** k = #1          by field_order_eqn
   Hence  root (unity k) x    by poly_unity_root_property
*)
val poly_unity_order_has_root = store_thm(
  "poly_unity_order_has_root",
  ``!r:'a field. Field r ==> !x. x IN R ==> root (unity (forder x)) x``,
  rw[field_order_eqn, poly_unity_root_property]);

(* Theorem: Field r ==> !x. x IN R /\ x <> #0 ==> !j. root (unity (forder x)) (x ** j) *)
(* Proof:
   Let k = forder x.
   Note x IN R ==> x ** j IN R        by field_exp_element
         (x ** j) ** k
       = (x ** k) ** j                by field_exp_mult_comm
       = #1 ** j                      by field_order_eqn
       = #1                           by field_one_exp
    Hence root (unity k) (x ** j)     by poly_unity_root_property
*)
val poly_unity_order_has_all_roots = store_thm(
  "poly_unity_order_has_all_roots",
  ``!r:'a field. Field r ==> !x. x IN R /\ x <> #0 ==> !j. root (unity (forder x)) (x ** j)``,
  rpt strip_tac >>
  qabbrev_tac `k = forder x` >>
  `x ** j IN R` by rw[] >>
  `(x ** j) ** k = (x ** k) ** j` by rw[field_exp_mult_comm] >>
  `_ = #1 ** j` by metis_tac[field_order_eqn] >>
  `_ = #1` by rw[] >>
  metis_tac[poly_unity_root_property, field_is_ring]);

(* Theorem: !z. z IN R /\ z <> #0 ==> (roots (unity (forder z)) = (Generated f* z).carrier) *)
(* Proof:
   Let k = forder z, g = Generated f* z.
   z IN R /\ z <> #0 ==> z IN F*            by field_nonzero_alt
   FiniteField r ==> FiniteGroup f*         by finite_field_mult_finite_group
                 ==> Group f*               by finite_group_is_group
                 ==> CARD G = k             by generated_group_card, group_order_pos, FiniteGroup f*

   First, show: !x. x IN G ==> (x ** k = #1)
   Since FiniteGroup g                      by generated_finite_group
     and (f*.id = #1) /\ (f*.exp = $** )    by field_nonzero_mult_property
   Hence !x. x IN G ==> (x ** k = #1)       by generated_Fermat, FiniteGroup g

   Next, show: G SUBSET roots (unity k)
     i.e., x IN G ==> x IN roots (unity k)  by SUBSET_DEF
     Since x IN G ==> x IN F*               by generated_subset, SUBSET_DEF
       and x IN F* ==> x IN R+              by field_mult_carrier
       and x IN R+ ==> x IN R               by field_nonzero_element
     Now  (root (unity k) x
          <=> (x ** k = #1))                by poly_unity_root_property, x IN R.
     Hence x IN roots (unity k)             by poly_roots_member

   Next, show: roots (unity k) SUBSET G, i.e. x IN roots (unity k) ==> x IN G.
     By contradiction, assume x NOTIN G.
      Then x IN (roots (unity k)) DIFF G    by IN_DIFF
        so (roots (unity k)) DIFF G <> {}   by MEMBER_NOT_EMPTY
       and G <> roots (unity k)             by DIFF_EQ_EMPTY
     Since G SUBSET roots (unity k)         by above,
        so G PSUBSET roots (unity k)        by PSUBSET_DEF
       Now roots (unity k) SUBSET R         by poly_roots_member, SUBSET_DEF
        so FINITE (roots (unity k))         by SUBSET_FINITE, FINITE R.
     Hence CARD G < CARD (roots (unity k))  by CARD_PSUBSET
        or k < CARD (roots (unity k))       by above, CARD G = k, [1].
     Since deg (unity k) = k                by poly_unity_deg
       and 0 < k                            by group_order_pos, FiniteGroup f*, k <> 0
        so unity k <> |0|                   by poly_unity_eq_zero, Ring r, #1 <> #0.
      Thus CARD (roots (unity k)) <= k      by poly_roots_count
      which contradicts [1] above.

   Since G SUBSET roots (unity k) /\ roots (unity k) SUBSET G
   Hence G = roots (unity k)                by SUBSET_ANTISYM
*)
val poly_unity_roots_generator = store_thm(
  "poly_unity_roots_generator",
  ``!r:'a field. FiniteField r ==> !z. z IN R /\ z <> #0 ==>
    (roots (unity (forder z)) = (Generated f* z).carrier)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `k = forder z` >>
  qabbrev_tac `g = Generated f* z` >>
  `FiniteGroup f*` by rw[finite_field_mult_finite_group] >>
  `Group f*` by rw[finite_group_is_group] >>
  `z IN F*` by rw[field_nonzero_alt] >>
  `CARD G = k` by rw[generated_group_card, group_order_pos, Abbr`g`, Abbr`k`] >>
  `!x. x IN G ==> (x ** k = #1)` by
  (rpt strip_tac >>
  `FiniteGroup g` by rw[generated_finite_group, Abbr`g`] >>
  metis_tac[generated_Fermat, field_nonzero_mult_property]) >>
  `G SUBSET roots (unity k)` by
    (rw_tac std_ss[SUBSET_DEF] >>
  qabbrev_tac `k = CARD G` >>
  `x IN R` by metis_tac[generated_subset, SUBSET_DEF, field_mult_carrier, field_nonzero_element] >>
  metis_tac[poly_roots_member, poly_unity_root_property, field_is_ring]) >>
  `roots (unity k) SUBSET G` by
      (rw_tac std_ss[SUBSET_DEF] >>
  qabbrev_tac `k = CARD G` >>
  spose_not_then strip_assume_tac >>
  `x IN roots (unity k) DIFF G` by rw[Abbr`k`] >>
  `G <> roots (unity k)` by metis_tac[MEMBER_NOT_EMPTY, DIFF_EQ_EMPTY] >>
  `G PSUBSET roots (unity k)` by rw[PSUBSET_DEF] >>
  `FINITE (roots (unity k))` by metis_tac[poly_roots_member, SUBSET_DEF, SUBSET_FINITE] >>
  `k < CARD (roots (unity k))` by metis_tac[CARD_PSUBSET] >>
  `poly (unity k) /\ (deg (unity k) = k)` by rw[poly_unity_deg] >>
  `k <> 0` by metis_tac[group_order_pos, NOT_ZERO_LT_ZERO] >>
  `unity k <> |0|` by metis_tac[poly_unity_eq_zero, field_is_ring, field_one_ne_zero] >>
  `CARD (roots (unity k)) <= k` by metis_tac[poly_roots_count] >>
  decide_tac) >>
  rw[SUBSET_ANTISYM]);

(* Another proof of the same theorem *)

(* Theorem: !z. z IN R /\ z <> #0 ==> (roots (unity (forder z)) = (Generated f* z).carrier) *)
(* Proof:
   FiniteField r ==> Field r /\ FINITE R        by FiniteField_def
   z IN R /\ z <> #0 ==> z IN F*                by field_nonzero_alt
   Let k = forder z, g = Generated f* z, to show: G = roots (unity k).
   Since FiniteField r
     ==> FiniteGroup f*                         by finite_field_mult_finite_group
     ==> FiniteGroup g                          by generated_finite_group
     ==> Group f*                               by finite_group_is_group
   hence CARD G = k                             by generated_group_card, group_order_pos

   First, show: G SUBSET roots (unity k)
      By SUBSET_DEF, this is to show: x IN G ==> x IN roots (unity k)
      Since x IN G,
         so g.exp x (CARD G) = g.id             by finite_group_Fermat
         or       f*.exp x k = f*.id            by generated_property, generated_exp
         or           x ** k = #1               by field_nonzero_mult_property
         or      x ** k - #1 = #0               by field_sub_eq_zero
        Now x IN R because:
            Since g <= f*                       by generated_subgroup
               so x IN F*                       by subgroup_element
             then x IN R+                       by field_mult_carrier
               or x IN R                        by field_nonzero_element
        Since x IN R,
           eval (unity k) x = x ** k - #1 = #0  by poly_unity_eval
        so root (unity k) x                     by poly_root_def
        or x IN roots (unity k)                 by poly_roots_member

   Next, show: CARD G = CARD (roots (unity k))
      Since poly (unity k)                           by poly_unity_poly
      Need to show: unity k <> |0|, because:
         Since 0 < k                                 by group_order_pos
           and deg (unity k) = k                     by poly_unity_deg
            so unity k <> |0|                        by poly_deg_zero
      From poly (unity k) /\ unity k <> |0|,
       ==> FINITE (roots (unity k))                  by poly_roots_finite

      From G SUBSET roots (unity k),
       ==> CARD G <= CARD (roots (unity k))          by CARD_SUBSET
        or      k <= CARD (roots (unity k))          by generated_group_card
       But CARD (roots (unity k)) <= deg (unity k) by poly_roots_count
        or CARD (roots (unity k)) <= k               by poly_unity_deg

      Therefore, k = CARD (roots (unity k))          by arithmetic
         or CARD G = CARD (roots (unity k))          by generated_group_card

   Overall, G SUBSET roots (unity k) and CARD G = CARD (roots (unity k)).
       With FINITE (roots (unity k)),
        and FINITE G                                 by SUBSET_FINITE
      Hence G = roots (unity k)                      by SUBSET_EQ_CARD
*)
val poly_roots_of_unity_by_generator = store_thm(
  "poly_roots_of_unity_by_generator",
  ``!r:'a field. FiniteField r ==> !z. z IN R /\ z <> #0 ==>
      (roots (unity (forder z)) = (Generated f* z).carrier)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `k = forder z` >>
  qabbrev_tac `g = Generated f* z` >>
  `FiniteGroup f*` by rw[finite_field_mult_finite_group] >>
  `z IN F*` by rw[field_nonzero_alt] >>
  `FiniteGroup g` by rw[generated_finite_group, Abbr`g`] >>
  `Group f*` by rw[finite_group_is_group] >>
  `CARD G = k` by rw[generated_group_card, group_order_pos, Abbr`k`, Abbr`g`] >>
  `G SUBSET roots (unity k)` by
  (rw_tac std_ss[SUBSET_DEF] >>
  qabbrev_tac `k = forder z` >>
  `x ** k = #1` by metis_tac[finite_group_Fermat, field_nonzero_mult_property, generated_property, generated_exp] >>
  `g <= f*` by rw[generated_subgroup, Abbr`g`] >>
  `x IN R` by metis_tac[subgroup_element, field_mult_carrier, field_nonzero_element] >>
  `root (unity k) x` by metis_tac[poly_unity_eval, poly_root_def, ring_sub_eq_zero, ring_one_element] >>
  metis_tac[poly_roots_member]) >>
  `poly (unity k)` by rw[poly_unity_poly] >>
  `0 < k` by rw[group_order_pos, Abbr`k`] >>
  `deg (unity k) = k` by rw[] >>
  `unity k <> |0|` by metis_tac[poly_deg_zero, NOT_ZERO_LT_ZERO] >>
  `FINITE (roots (unity k))` by rw[poly_roots_finite] >>
  `CARD G <= CARD (roots (unity k))` by rw[CARD_SUBSET] >>
  `CARD (roots (unity k)) <= deg (unity k)` by rw[poly_roots_count] >>
  `CARD (roots (unity k)) = k` by decide_tac >>
  metis_tac[SUBSET_EQ_CARD, SUBSET_FINITE]);

(* Theorem: FiniteField r ==> !z. z IN R /\ z <> #0 ==>
            (roots (unity (forder z)) = IMAGE (\j. z ** j) (count (forder z))) *)
(* Proof:
   Since FiniteField r ==> FiniteGroup f*       by finite_field_mult_finite_group
    also z IN R /\ z <> #0 ==> z IN F*          by field_nonzero_alt
     and 0 < ord z                              by group_order_pos
     roots (unity (forder z))
   = (Generated f* z).carrier                   by poly_unity_roots_generator
   = IMAGE (\j. f*.exp z j) (count (forder z))  by generated_carrier_as_image
   = IMAGE (\j. z ** j) (count (forder z))      by field_nonzero_mult_property
*)
val poly_unity_roots_as_image = store_thm(
  "poly_unity_roots_as_image",
  ``!r:'a field. FiniteField r ==> !z. z IN R /\ z <> #0 ==>
        (roots (unity (forder z)) = IMAGE (\j. z ** j) (count (forder z)))``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteGroup f*` by rw[finite_field_mult_finite_group] >>
  `Group f*` by rw[finite_group_is_group] >>
  `z IN F*` by rw[field_nonzero_alt] >>
  rw[poly_unity_roots_generator, generated_carrier_as_image, group_order_pos, field_nonzero_mult_property]);

(* Theorem: FiniteField r ==> !z. z IN R /\ z <> #0 ==>
            BIJ (\j. z ** j) (count (forder z)) (roots (unity (forder z))) *)
(* Proof:
   Since FiniteField r ==> FiniteGroup f*       by finite_field_mult_finite_group
    also z IN R /\ z <> #0 ==> z IN F*          by field_nonzero_alt
      so (roots (unity (forder z))
       = (Generated f* z).carrier)              by poly_unity_roots_generator
   Note: group_order_to_generated_bij |> ISPEC ``f*`` |> SPEC ``z``;
   val it = |- Group f* /\ z IN F* /\ 0 < forder z ==>
               BIJ (\n. f*.exp z n) (count (forder z)) (Generated f* z).carrier: thm
   Apply field_nonzero_mult_property, group_order_pos.
*)
val poly_unity_order_roots_bij = store_thm(
  "poly_unity_order_roots_bij",
  ``!r:'a field. FiniteField r ==> !z. z IN R /\ z <> #0 ==>
       BIJ (\j. z ** j) (count (forder z)) (roots (unity (forder z)))``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteGroup f*` by rw[finite_field_mult_finite_group] >>
  `Group f*` by rw[finite_group_is_group] >>
  `z IN F*` by rw[field_nonzero_alt] >>
  `(roots (unity (forder z)) = (Generated f* z).carrier)` by rw[poly_unity_roots_generator] >>
  metis_tac[group_order_to_generated_bij, group_order_pos, field_nonzero_mult_property]);

(* ------------------------------------------------------------------------- *)
(* Field Equal Order Structure (continued)                                   *)
(* ------------------------------------------------------------------------- *)

(*
Here is the continuation of fieldOrderTheory.field_order_equal_contains
|- !r. Field r ==> !n. 0 < n ==>
   !x. x IN forder_eq n ==> IMAGE (\j. x ** j) (coprimes n) SUBSET forder_eq n

Note: IMAGE (\j. x ** j) (coprimes n) = {x ** j | j | j IN coprimes n}
For the stronger result:
!r:'a field. FiniteField r ==> !n. 0 < n ==>
   !x. x IN (forder_eq n) ==> (forder_eq n = IMAGE (\j. x ** j) (coprimes n))

We really need ffUnity, for the following:
(1) If (forder x = n),
    then every element y of order n is somewhere in the set s = {1, x, x ** 2, ...., x ** (n-1)}
    although not all n of them have order n.
    This is because:
    (a) any z IN R with (forder z = n) has z ** n = #1, hence a root of (unity n = X ** n - |1|).
    (b) all z IN s are roots of (unity n = X ** n - |1|).
        and there are no more roots:
        poly_roots_count |- !r. Field r ==> !p. poly p /\ p <> |0| ==> CARD (roots p) <= deg p
(2) Since every possible element y of order n is somewhere in the set s,
    and only index j with coprime j n can have order n by field_order_power_coprime,
    there are exactly (phi n) elements of order n, if there is at least one.
*)

(* Theorem: Field r ==> !n. 0 < n ==>
            !z. z IN R /\ (forder z = n) ==> (roots (unity n) = IMAGE (\j. z ** j) (count n)) *)
(* Proof:
   Note z <> #0                      by field_order_zero, 0 < n
    ==> z IN R+                      by field_nonzero_eq
   Let s = IMAGE (\j. z ** j) (count n).
   The goal is: roots (unity n) = s

   Claim: s SUBSET roots (unity n)
   Proof: By SUBSET_DEF, IN_IMAGE, poly_roots_member, this is to show:
          (1) z IN R ==> z ** j IN R, true   by field_exp_element
          (2) z IN R ==> root (unity n) (z ** j)
              Let m = gcd j n, x = z ** j.
              Then x IN R                    by field_exp_element
               and (forder x) * m = n        by field_order_power
                   x ** n
                 = x ** (forder x * m)       by above
                 = (x ** (forder x)) ** m    by field_exp_mult
                 = #1 ** m                   by field_order_eqn
                 = #1                        by field_one_exp
              Thus root (unity n) x          by poly_unity_root_property

   Claim: CARD s = n
   Proof: First, we show that INJ (\j. z ** j) (count n) UNIV
          By INJ_DEF, this is to show:
             j < n /\ j' < n /\ z ** j = z ** j' ==> j = j'
          Note n = forder z, so this follows by field_nonzero_exp_eq
          Note FINITE (count n)                     by FINITE_COUNT
          Thus CARD s
             = CARD (IMAGE (\j. z ** j) (count n))  by notation
             = CARD (count n)                       by INJ_CARD_IMAGE_EQN
             = n                                    by CARD_COUNT

   Assert: unity n can only have at most n roots
   Let p = unity n.
   By contradiction, suppose roots p <> s.
   Then s PSUBSET roots p             by PSUBSET_DEF, s SUBSET roots p
   Note poly p                        by poly_unity_poly
    and deg p = n                     by poly_unity_deg
    ==> p <> |0|                      by poly_deg_zero, 0 < n
   Thus FINITE (roots p)              by poly_roots_finite, poly p, p <> |0|
    ==> CARD s < CARD (roots p)       by CARD_PSUBSET, FINITE (roots p)
    But CARD (roots p) <= deg p       by poly_roots_count, poly p, p <> |0|
   This is a contradiction.
*)
val poly_unity_roots_eqn = store_thm(
  "poly_unity_roots_eqn",
  ``!r:'a field. Field r ==> !n. 0 < n ==>
   !z. z IN R /\ (forder z = n) ==> (roots (unity n) = IMAGE (\j. z ** j) (count n))``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `z <> #0` by metis_tac[field_order_zero, NOT_ZERO_LT_ZERO] >>
  `z IN R+` by rw[field_nonzero_eq] >>
  qabbrev_tac `s = IMAGE (\j. z ** j) (count n)` >>
  `s SUBSET roots (unity n)` by
  (rw_tac std_ss[SUBSET_DEF, IN_IMAGE, poly_roots_member, Abbr`s`] >-
  rw[] >>
  qabbrev_tac `n = forder z` >>
  qabbrev_tac `m = gcd j n` >>
  qabbrev_tac `x = z ** j` >>
  `x IN R` by rw[Abbr`x`] >>
  `(forder x) * m = n` by rw[field_order_power, Abbr`x`, Abbr`m`, Abbr`n`] >>
  `x ** n = x ** (forder x * m)` by rw[] >>
  `_ = (x ** (forder x)) ** m` by rw[field_exp_mult] >>
  `_ = #1 ** m` by rw[field_order_eqn] >>
  `_ = #1` by rw[] >>
  rw[poly_unity_root_property]
  ) >>
  `INJ (\j. z ** j) (count n) UNIV` by
    (rw[INJ_DEF] >>
  metis_tac[field_nonzero_exp_eq]) >>
  `CARD s = n` by rw[INJ_CARD_IMAGE_EQN, Abbr`s`] >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `p = unity n` >>
  `s PSUBSET roots p` by rw[PSUBSET_DEF] >>
  `poly p /\ (deg p = n)` by rw[Abbr`p`] >>
  `p <> |0|` by metis_tac[poly_deg_zero, NOT_ZERO_LT_ZERO] >>
  `FINITE (roots p)` by rw[poly_roots_finite] >>
  `CARD s < CARD (roots p)` by rw[CARD_PSUBSET] >>
  `CARD (roots p) <= deg p` by rw[poly_roots_count] >>
  decide_tac);

(* This is equivalent to poly_unity_roots_as_image, but not using any generator for unity roots:
poly_unity_roots_eqn
|- !r. Field r ==> !n. 0 < n ==>
   !z. z IN R /\ (forder z = n) ==> (roots (unity n) = IMAGE (\j. z ** j) (count n))
poly_unity_roots_as_image
|- !r. FiniteField r ==> !z. z IN R /\ z <> #0 ==>
       (roots (unity (forder z)) = IMAGE (\j. z ** j) (count (forder z)))
*)

(* Theorem: Field r ==> !n. 0 < n ==>
            !x. x IN (forder_eq n) ==> (forder_eq n = IMAGE (\j. x ** j) (coprimes n)) *)
(* Proof:
   By SUBSET_ANTISYM, this is to show:
   (1) IMAGE (\j. x ** j) (coprimes n) SUBSET forder_eq n
       This is true                     by field_order_equal_contains
   (2) forder_eq n SUBSET IMAGE (\j. x ** j) (coprimes n)
       By SUBSET_DEF, this is to show:
          x IN forder_eq n /\ x' IN forder_eq n ==> ?j. (x' = x ** j) /\ j IN coprimes n
       Note x IN R /\ forder x = n      by field_order_equal_element
        and x' IN R /\ forder x' = n    by field_order_equal_element

       If n = 1,
          Then (x = #1) /\ (x' = #1)    by field_order_eq_1
          also 1 IN coprimes n          by coprimes_has_1, 0 < n
           and #1 ** 1 = #1             by field_exp_1
          Take j = 1, the result follows.
       If n <> 1, then 1 < n.
          Note roots (unity n) = IMAGE (\j. x ** j) (count n)   by poly_unity_roots_eqn
           and root (unity n) x'        by poly_unity_order_has_root
            or x' IN roots (unity n)    by poly_roots_member
          Thus ?j. j < n /\ (x' = x ** j)          by IN_IMAGE, IN_COUNT
           ==> (forder x') * gcd j n = forder x    by field_order_power
            or           n * gcd j n = n           by above
           ==> coprime j n              by MULT_RIGHT_ID
            or j IN coprimes n          by coprimes_element_alt, 1 < n
*)
val field_order_equal_eqn = store_thm(
  "field_order_equal_eqn",
  ``!r:'a field. Field r ==> !n. 0 < n ==>
   !x. x IN (forder_eq n) ==> (forder_eq n = IMAGE (\j. x ** j) (coprimes n))``,
  rpt strip_tac >>
  (irule (GSYM SUBSET_ANTISYM) >> rpt conj_tac) >-
  rw[field_order_equal_contains] >>
  rw[SUBSET_DEF] >>
  fs[field_order_equal_element] >>
  Cases_on `n = 1` >| [
    `(x = #1) /\ (x' = #1)` by rw[GSYM field_order_eq_1] >>
    `1 IN coprimes n` by rw[coprimes_has_1] >>
    metis_tac[field_exp_1],
    `1 < n` by decide_tac >>
    `roots (unity n) = IMAGE (\j. x ** j) (count n)` by rw[poly_unity_roots_eqn] >>
    `x' IN roots (unity n)` by rw[poly_unity_order_has_root, poly_roots_member] >>
    `?j. j < n /\ (x' = x ** j)` by metis_tac[IN_IMAGE, IN_COUNT] >>
    `n * gcd j n = n` by metis_tac[field_order_power] >>
    `coprime j n` by metis_tac[MULT_RIGHT_ID] >>
    metis_tac[coprimes_element_alt]
  ]);

(* This is equivalent to field_order_eq_order, but does not using poly_unity_roots_as_image

field_order_equal_eqn
|- !r. Field r ==> !n. 0 < n ==>
   !x. x IN forder_eq n ==> (forder_eq n = IMAGE (\j. x ** j) (coprimes n))
field_order_eq_order
|- !r. FiniteField r ==> !x y. x IN R /\ y IN R /\ (forder x = forder y) ==> ?j. y = x ** j
*)

(* Theorem: Field r ==> !n. 0 < n ==> (CARD (forder_eq n) = 0) \/ (CARD (forder_eq n) = phi n) *)
(* Proof:
   If forder_eq n = {},
      Then CARD (forder_eq n)
         = CARD {} = 0                  by CARD_EMPTY
   If forder_eq n <> {},
      If n = 1,
         Then CARD (forder_eq 1)
            = CARD {#1}                 by field_order_equal_of_1
            = 1                         by CARD_SING
            = phi 1                     by phi_1
      If n <> 1, then 1 < n.
         Note ?x. x IN forder_eq n      by MEMBER_NOT_EMPTY
          ==> (forder_eq n = IMAGE (\j. x ** j) (coprimes n)  field_order_equal_eqn

         Claim: INJ (\j. x ** j) (coprimes n) UNIV
         Proof: By coprimes_element_alt, INJ_DEF, this is to show:
                   j < n /\ j' < n /\ x ** j = x ** j' ==> j = j'
                Note x IN R+ /\ (forder x = n)  by field_order_equal_element_nonzero, 0 < n
                Thus j = j'                     by field_nonzero_exp_eq

         Note FINITE (coprimes n)       by coprimes_finite
              CARD (forder_eq n)
            = CARD (IMAGE (\j. x ** j) (coprimes n))  by field_order_equal_eqn
            = CARD (coprimes n)         by INJ_CARD_IMAGE_EQN, FINITE (coprimes n)
            = phi n                     by phi_def
*)
val field_order_equal_card_eqn = store_thm(
  "field_order_equal_card_eqn",
  ``!r:'a field. Field r ==> !n. 0 < n ==> (CARD (forder_eq n) = 0) \/ (CARD (forder_eq n) = phi n)``,
  rpt strip_tac >>
  Cases_on `forder_eq n = {}` >-
  rw[] >>
  Cases_on `n = 1` >-
  rw[field_order_equal_of_1, phi_1] >>
  `1 < n` by decide_tac >>
  `?x. x IN forder_eq n` by rw[MEMBER_NOT_EMPTY] >>
  `INJ (\j. x ** j) (coprimes n) UNIV` by
  (rw[coprimes_element_alt, INJ_DEF] >>
  `x IN R+ /\ (forder x = n)` by metis_tac[field_order_equal_element_nonzero] >>
  metis_tac[field_nonzero_exp_eq]) >>
  `FINITE (coprimes n)` by rw[coprimes_finite] >>
  metis_tac[phi_def, field_order_equal_eqn, INJ_CARD_IMAGE_EQN]);

(* This is better than field_order_equal_card_choices:
field_order_equal_card_eqn
|- !r. Field r ==> !n. 0 < n ==> (CARD (forder_eq n) = 0) \/ (CARD (forder_eq n) = phi n)
field_order_equal_card_choices
|- !r. FiniteField r ==> !n. 0 < n ==> (CARD (forder_eq n) = 0) \/ (CARD (forder_eq n) = phi n)
*)

(* Theorem: FiniteField r ==> !n. 0 < n ==> (forder_eq n <> {} <=> n divides (CARD R+)) *)
(* Proof:
   If part: forder_eq n <> {} ==> n divides (CARD R+)
      Note ?x. x IN forder_eq n        by MEMBER_NOT_EMPTY
       and x IN R+ /\ (forder x = n)   by field_order_equal_element_nonzero, 0 < n
       ==> n divides (CARD R+)         by field_order_divides
   Only-if part: n divides (CARD R+) ==> forder_eq n <> {}
      By contradiction, suppose forder_eq n = {}.

      Let m = CARD R+, s = divisors m.
      Then 0 < m                       by field_nonzero_card_pos
       and FINITE s                    by divisors_finite

      Step 1: partition s
      Let u = {n | n IN s /\ forder_eq n = {}},
          v = {n | n IN s /\ forder_eq n <> {}}.
      Then FINITE u /\ FINITE v /\ split s u v   by finite_partition_by_predicate

      Step 2: get an equation for m
      Claim: SIGMA (CARD o forder_eq) u = 0

      Proof: Note !x. x IN u
                   (CARD o forder_eq) x
                 = CARD (forder_eq x)      by o_THM
                 = CARD {}                 by x IN u
                 = 0                       by CARD_EMPTY
                 = (K 0) x                 by K_THM

             Thus SIGMA (CARD o forder_eq) u
                 = SIGMA (K 0) u           by SUM_IMAGE_CONG
                 = 0 * CARD u              by SUM_IMAGE_CONSTANT
                 = 0                       by MULT

      Claim: SIGMA (CARD o forder_eq) v = SIGMA phi v
      Proof: Note !x. x IN s /\ forder_eq x <> {}
              ==> CARD (forder_eq x) <> 0          by field_order_equal_finite, CARD_EQ_0
              and 0 < x                            by divisors_nonzero, x IN s
               so CARD (forder_eq x) = phi x       by field_order_equal_card_eqn
               or (CARD o forder_eq) x = phi x     by o_THM

             Thus SIGMA (CARD o forder_eq) v
                = SIGMA phi v                      by SUM_IMAGE_CONG

      Therefore,
             m = SIGMA (CARD o forder_eq) s        by field_order_equal_over_divisors_sigma_card
               = SIGMA (CARD o forder_eq) u + SIGMA (CARD o forder_eq) v   by SUM_IMAGE_DISJOINT
               = 0 + SIGMA phi v                   by Claims
               = SIGMA phi v                       by arithmetic, [1]

      Step 3: get a contradiction
      Note n <= m                        by DIVIDES_LE, n divides m
        so n IN s                        by divisors_element_alt, 0 < m
       ==> forder n IN u                 by IN_IMAGE
        or u <> {}                       by MEMBER_NOT_EMPTY
       ==> v <> s                        by finite_partition_property
       But v SUBSET s                    by SUBSET_UNION
        so v PSUBSET s                   by PSUBSET_DEF, v <> s
      Also !x. x IN s ==> phi x <> 0     by phi_eq_0, divisors_nonzero
      Thus SIGMA phi v < SIGMA phi s     by SUM_IMAGE_PSUBSET_LT, [2]

       Now SIGMA phi s = m               by Gauss_little_thm
      Therefore m < m                    by [1], [2]
      This is impossible, a contradiction.
*)
val field_order_equal_nonempty = store_thm(
  "field_order_equal_nonempty",
  ``!r:'a field. FiniteField r ==> !n. 0 < n ==> (forder_eq n <> {} <=> n divides (CARD R+))``,
  rpt (stripDup[FiniteField_def]) >>
  rw[EQ_IMP_THM] >| [
    `?x. x IN forder_eq n` by rw[MEMBER_NOT_EMPTY] >>
    `x IN R+ /\ (forder x = n)` by metis_tac[field_order_equal_element_nonzero] >>
    rw[field_order_divides],
    spose_not_then strip_assume_tac >>
    qabbrev_tac `m = CARD R+` >>
    qabbrev_tac `s = divisors m` >>
    `0 < m` by rw[field_nonzero_card_pos, Abbr`m`] >>
    `FINITE s` by rw[divisors_finite, Abbr`s`] >>
    qabbrev_tac `u = {n | n IN s /\ (forder_eq n = {})}` >>
    qabbrev_tac `v = {n | n IN s /\ forder_eq n <> {}}` >>
    `!n. n IN u <=> n IN s /\ (forder_eq n = {})` by rw[Abbr`u`] >>
    `!n. n IN v <=> n IN s /\ forder_eq n <> {}` by rw[Abbr`v`] >>
    `FINITE u /\ FINITE v /\ split s u v` by metis_tac[finite_partition_by_predicate] >>
    `SIGMA (CARD o forder_eq) u = 0` by
  (`!x. x IN u ==> (CARD o forder_eq) x = (K 0) x` by metis_tac[CARD_EMPTY, IN_IMAGE, combinTheory.K_THM, combinTheory.o_THM] >>
    `SIGMA (CARD o forder_eq) u = SIGMA (K 0) u` by metis_tac[SUM_IMAGE_CONG] >>
    rw[SUM_IMAGE_CONSTANT]) >>
    `SIGMA (CARD o forder_eq) v = SIGMA phi v` by
    ((irule SUM_IMAGE_CONG >> rpt conj_tac) >| [
      rw_tac std_ss[] >>
      `CARD (forder_eq x) <> 0` by metis_tac[field_order_equal_finite, CARD_EQ_0] >>
      `0 < x` by metis_tac[divisors_nonzero] >>
      metis_tac[field_order_equal_card_eqn],
      decide_tac
    ]) >>
    `m = SIGMA (CARD o forder_eq) s` by rw[field_order_equal_over_divisors_sigma_card, Abbr`s`, Abbr`m`] >>
    `_ = SIGMA phi v` by rw[SUM_IMAGE_DISJOINT] >>
    `n IN s` by rw[divisors_element_alt, Abbr`s`] >>
    `u <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
    `v <> s` by metis_tac[finite_partition_property] >>
    `v PSUBSET s` by metis_tac[PSUBSET_DEF, SUBSET_UNION] >>
    `!x. x IN s ==> phi x <> 0` by metis_tac[phi_eq_0, divisors_nonzero, NOT_ZERO] >>
    `SIGMA phi v < SIGMA phi s` by metis_tac[SUM_IMAGE_PSUBSET_LT] >>
    `SIGMA phi s = m` by rw[Gauss_little_thm, Abbr`s`] >>
    decide_tac
  ]);

(* Note: due to the use of the preceding field_order_equal_card_eqn, this is still in ffUnity. *)

(* This is a major milestone achievement! *)

(* Theorem: FiniteField r ==> cyclic f* *)
(* Proof:
   Note FiniteGroup f*               by finite_field_mult_finite_group
    and F* = R+                      by field_mult_carrier
   Let n = CARD R+.
   Then 0 < n                        by field_nonzero_card_pos
    Now n divides n                  by DIVIDES_REFL
    ==> forder_eq n <> {}            by field_order_equal_nonempty, 0 < n
    ==> ?z. z IN forder_eq n         by MEMBER_NOT_EMPTY
     or z IN R+ /\ (forder z = n)    by field_order_equal_element_nonzero, 0 < n
   Thus cyclic f*                    by cyclic_finite_alt
*)
val finite_field_mult_group_is_cyclic = store_thm(
  "finite_field_mult_group_is_cyclic",
  ``!r:'a field. FiniteField r ==> cyclic f*``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteGroup f*` by rw[finite_field_mult_finite_group] >>
  `F* = R+` by rw[field_mult_carrier] >>
  qabbrev_tac `n = CARD R+` >>
  `0 < n` by rw[field_nonzero_card_pos, Abbr`n`] >>
  `forder_eq n <> {}` by rw[field_order_equal_nonempty] >>
  `?z. z IN forder_eq n` by rw[MEMBER_NOT_EMPTY] >>
  `z IN R+ /\ (forder z = n)` by metis_tac[field_order_equal_element_nonzero] >>
  metis_tac[cyclic_finite_alt]);

(* This is a significant milestone theorem, the same as:

ffAdvancedTheory.finite_field_mult_group_cyclic |- !r. FiniteField r ==> cyclic f*

Note: ffUnity uses ffAdvanced, not the other way round.
*)

(* ------------------------------------------------------------------------- *)
(* Finite Field Orders dependent on Unity                                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==> !x y. x IN R /\ y IN R /\ (forder x = forder y) ==> ?j. y = x ** j *)
(* Proof:
   If x = #0,
      then forder x = 0              by field_order_eq_0
        so forder y = 0 ==> y = #0   by field_order_eq_0
      Take j = 1, then #0 ** 1 = #0  by field_exp_1
   If x <> #0,
   Let k = forder x.
   Since root (unity (forder y)) y   by poly_unity_order_has_root
      so root (unity k) y            by forder x = forder y
      or y IN roots (unity k)        by poly_roots_member
      or y IN IMAGE (\j. x ** j) (count k)   by poly_unity_roots_as_image
   hence ?j. y = x ** j                      by IN_IMAGE
*)
val field_order_eq_order = store_thm(
  "field_order_eq_order",
  ``!r:'a field. FiniteField r ==> !x y. x IN R /\ y IN R /\ (forder x = forder y) ==> ?j. y = x ** j``,
  rpt (stripDup[FiniteField_def]) >>
  Cases_on `x = #0` >| [
    `y = #0` by metis_tac[field_order_eq_0] >>
    metis_tac[field_exp_1],
    qabbrev_tac `k = forder x` >>
    `y IN roots (unity k)` by metis_tac[poly_roots_member, poly_unity_order_has_root] >>
    metis_tac[poly_unity_roots_as_image, IN_IMAGE]
  ]);

(* Theorem: FiniteField r ==> !x. x IN R /\ x <> #0 ==>
            !y. y IN R /\ (forder x = forder y) ==> ?j. j < forder x /\ (y = x ** j) *)
(* Proof:
   Let k = forder x.
   Since root (unity (forder y)) y         by poly_unity_order_has_root
      so root (unity k) y                  by forder x = forder y
      or y IN roots (unity k)              by poly_roots_member
      or y IN IMAGE (\j. x ** j) (count k) by poly_unity_roots_as_image
   hence ?j. j < k /\ (y = x ** j)         by IN_IMAGE, IN_COUNT
*)
val field_nonzero_order_eq_order = store_thm(
  "field_nonzero_order_eq_order",
  ``!r:'a field. FiniteField r ==> !x. x IN R /\ x <> #0 ==>
   !y. y IN R /\ (forder x = forder y) ==> ?j. j < forder x /\ (y = x ** j)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `k = forder x` >>
  `y IN roots (unity k)` by metis_tac[poly_roots_member, poly_unity_order_has_root] >>
  metis_tac[poly_unity_roots_as_image, IN_IMAGE, IN_COUNT]);

(* Theorem: FiniteField r ==>
            !n. 0 < n ==> (CARD (forder_eq n) = if (n divides CARD R+ ) then phi n else 0) *)
(* Proof:
   Since cyclic f*         by finite_field_mult_group_cyclic
     and F* = R+           by field_mult_carrier
     and R+ SUBSET R       by field_nonzero_element, SUBSET_DEF
      so FINITE F*         by SUBSET_FINITE
    with 0 < n,
         forder_eq n = orders f* n    by field_order_equal_eq_orders
    The result follows     by cyclic_orders_card
*)
val field_order_equal_card = store_thm(
  "field_order_equal_card",
  ``!r:'a field. FiniteField r ==>
   !n. 0 < n ==> (CARD (forder_eq n) = if (n divides CARD R+ ) then phi n else 0)``,
  rpt (stripDup[FiniteField_def]) >>
  `cyclic f*` by rw[finite_field_mult_group_cyclic] >>
  `(F* = R+) /\ FINITE F*` by metis_tac[field_mult_carrier, field_nonzero_element, SUBSET_DEF, SUBSET_FINITE] >>
  rw[field_order_equal_eq_orders, cyclic_orders_card]);

(* Theorem: FiniteField r ==> !n x. 0 < n /\ x IN (forder_eq n) ==>
            BIJ (\j. x ** j) (coprimes n) (forder_eq n) *)
(* Proof:
   Since x IN (forder_eq n)
      so x IN R /\ forder x = n                by field_order_equal_element

   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) x IN R /\ j IN coprimes n ==> x ** j IN forder_eq n
       Since j IN coprimes n,
          so 0 < j /\ j <= n /\ coprime j n    by coprimes_element
        thus forder (x ** j) = n               by field_order_power_eq_order
          or x ** j IN forder_eq n             by field_order_equal_element
   (2) j IN coprimes n /\ j' IN coprimes n /\ x ** j = x ** j' ==> j = j'
       If n = 1,
          coprimes 1 = {1}                     by coprimes_1
          j = 1 and j' = 1                     by IN_SING
          so j = j'.
       If n <> 1, 1 < n.
          j < n and j' < n                     by coprimes_element_less
          j = j'                               by field_nonzero_exp_eq
   (3) same as (1).
   (4) x IN forder_eq n /\ x' IN forder_eq n ==> ?j. j IN coprimes n /\ (x ** j = x')
       If n = 1,
          forder_eq 1 = {#1}                   by field_order_equal_of_1
          x = #1 and x' = #1 = x               by IN_SING
         Take j = 1,
         then 1 IN coprimes 1                  by coprimes_1, IN_SING
         and  x ** 1 = x'                      by field_exp_1
       If n <> 1,
         then x' IN R and forder x' = n        by field_order_equal_element
         thus ?j. j < n /\ (x' = x ** j)       by field_nonzero_order_eq_order
        Since x' <> #1 since forder #1 = 1     by field_order_one
           so j <> 0, or 0 < j                 by field_exp_0
         also j < n ==> j <= n                 by LESS_IMP_LESS_OR_EQ
          Now coprime j n                      by field_order_power_eq_order
        Hence j IN coprimes n                  by coprimes_element
*)
val field_order_equals_coprimes_bij = store_thm(
  "field_order_equals_coprimes_bij",
  ``!r:'a field. FiniteField r ==> !n x. 0 < n /\ x IN (forder_eq n) ==>
       BIJ (\j. x ** j) (coprimes n) (forder_eq n)``,
  rpt (stripDup[FiniteField_def, field_order_equal_element]) >>
  `n <> 0` by decide_tac >>
  `x <> #0` by rw[GSYM field_order_eq_0] >>
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >| [
    qabbrev_tac `n = forder x` >>
    `coprime j n` by metis_tac[coprimes_element] >>
    `forder (x ** j) = n` by rw[field_order_power_eq_order, Abbr`n`] >>
    metis_tac[field_order_equal_element, field_exp_element],
    qabbrev_tac `n = forder x` >>
    Cases_on `n = 1` >-
    metis_tac[coprimes_1, IN_SING] >>
    `1 < n` by decide_tac >>
    metis_tac[coprimes_element_less, field_nonzero_exp_eq, field_nonzero_eq],
    qabbrev_tac `n = forder x` >>
    `coprime j n` by metis_tac[coprimes_element] >>
    `forder (x ** j) = n` by rw[field_order_power_eq_order, Abbr`n`] >>
    metis_tac[field_order_equal_element, field_exp_element],
    qabbrev_tac `n = forder x` >>
    Cases_on `n = 1` >| [
      `(x = #1) /\ (x' = #1)` by metis_tac[field_order_equal_of_1, IN_SING] >>
      `1 IN coprimes 1` by metis_tac[coprimes_1, IN_SING] >>
      metis_tac[field_exp_1],
      `x' IN R /\ (forder x' = n)` by metis_tac[field_order_equal_element] >>
      `?j. j < n /\ (x' = x ** j)` by metis_tac[field_nonzero_order_eq_order] >>
      `x' <> #1` by metis_tac[field_order_one] >>
      `j <> 0` by metis_tac[field_exp_0] >>
      `0 < j /\ j <= n` by decide_tac >>
      metis_tac[coprimes_element, field_order_power_eq_order]
    ]
  ]);

(* Theorem: FiniteField r ==> !n. 0 < n ==> (CARD (forder_eq n) = 0) \/ (CARD (forder_eq n) = phi n) *)
(* Proof:
   Let s = forder_eq n.
   If s = {},
      then CARD s = 0             by CARD_EMPTY
   If s <> {},
      then ?z. z IN s             by MEMBER_NOT_EMPTY
        so BIJ (\j. z ** j) (coprimes n) s   by field_order_equals_coprimes_bij
       Now FINITE (coprimes n)    by coprimes_finite
       and FINITE s               by field_order_equal_finite
     Hence CARD s
         = CARD (coprimes n)      by FINITE_BIJ_CARD_EQ
         = phi n                  by phi_def
*)
val field_order_equal_card_choices = store_thm(
  "field_order_equal_card_choices",
  ``!r:'a field. FiniteField r ==> !n. 0 < n ==> (CARD (forder_eq n) = 0) \/ (CARD (forder_eq n) = phi n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `s = forder_eq n` >>
  Cases_on `s = {}` >-
  rw[] >>
  rw[CARD_EQ_0, field_order_equal_finite, Abbr`s`] >>
  `?z. z IN (forder_eq n)` by rw[MEMBER_NOT_EMPTY] >>
  `BIJ (\j. z ** j) (coprimes n) (forder_eq n)` by rw[field_order_equals_coprimes_bij] >>
  `FINITE (coprimes n)` by rw[coprimes_finite] >>
  `FINITE (forder_eq n)` by rw[field_order_equal_finite] >>
  metis_tac[FINITE_BIJ_CARD_EQ, phi_def]);

(* Theorem: FiniteField r ==> !n. CARD (orders f* n) = if (n divides CARD R+ ) then phi n else 0 *)
(* Proof:
   Note cyclic f*            by finite_field_mult_group_cyclic
    and FINITE R+            by field_nonzero_finite
    and F* = R+              by field_mult_carrier
   The result follows        by cyclic_orders_card

> cyclic_orders_card |> ISPEC ``f*``;
val it = |- cyclic f* /\ FINITE F* ==>
   !n. CARD (orders f* n) = if n divides CARD F* then phi n else 0: thm
*)
val field_orders_card = store_thm(
  "field_orders_card",
  ``!r:'a field. FiniteField r ==> !n. CARD (orders f* n) = if (n divides CARD R+ ) then phi n else 0``,
  rw[cyclic_orders_card, field_mult_carrier, field_nonzero_finite, finite_field_mult_group_cyclic, FiniteField_def]);

(* Theorem: FiniteField r ==> !m n. m divides n ==> (cyclo m) pdivides (unity n) *)
(* Proof:
   By SUBSET_DEF, this is to show:
   !x. x IN (orders f* m) ==> x IN roots (unity n)

   Since m divides n
     ==> ?q. n = q * m        by divides_def
     Now x IN (orders f* m)
     ==> forder x = m         by field_orders_element_order
     and x IN R+              by field_orders_nonzero_element
      so x IN R               by field_nonzero_element

         x ** n
       = x ** (m * q)         by n = q * n, MULT_COMM
       = (x ** m) ** q        by field_exp_mult, x IN R
       = #1 ** q              by field_order_property, x IN R+
       = #1                   by field_one_exp

    Thus root (unity n) x     by poly_unity_root_property
      or x IN roots (unity n) by poly_roots_member, x IN R
*)
val field_orders_subset_unity_roots = store_thm(
  "field_orders_subset_unity_roots",
  ``!r:'a field. FiniteField r ==> !m n. m divides n ==> (orders f* m) SUBSET roots (unity n)``,
  rpt (stripDup[FiniteField_def]) >>
  rw_tac std_ss[SUBSET_DEF] >>
  `?q. n = q * m` by rw[GSYM divides_def] >>
  `forder x = m` by rw[field_orders_element_order] >>
  `x IN R+` by metis_tac[field_orders_nonzero_element] >>
  `x IN R` by rw[field_nonzero_element] >>
  `x ** n = x ** (m * q)` by rw_tac std_ss[MULT_COMM] >>
  `_ = (x ** m) ** q` by rw[field_exp_mult] >>
  `_ = #1` by rw[field_order_property] >>
  `root (unity n) x` by rw[poly_unity_root_property] >>
  rw[poly_roots_member]);

(* Theorem: FiniteField r ==> !n. n divides (CARD R+) ==> !m. (orders f* n = orders f* m) <=> (m = n) *)
(* Proof:
   Note 0 < CARD R+                    by field_nonzero_card_pos
   Also n divides CARD R+ ==> 0 < n    by ZERO_DIVIDES
    ==> CARD (orders f* n) = phi n     by field_orders_card
    and 0 < phi n                      by phi_pos, 0 < n
   Thus (orders f* n) <> {}            by CARD_EQ_0
    ==> ?x. x IN (orders f* n)         by MEMBER_NOT_EMPTY
    and     x IN (orders f* m)         by given equal sets
     so  forder x = m, forder x = n    by field_orders_element_order
     or m = forder x = n
*)
val field_orders_eq = store_thm(
  "field_orders_eq",
  ``!r:'a field. FiniteField r ==> !n. n divides (CARD R+) ==>
   !m. (orders f* n = orders f* m) <=> (m = n)``,
  rpt (stripDup[FiniteField_def]) >>
  rw[EQ_IMP_THM] >>
  `0 < CARD R+` by rw[field_nonzero_card_pos] >>
  `0 < n` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `CARD (orders f* n) = phi n` by rw[field_orders_card] >>
  `0 < phi n` by rw[phi_pos] >>
  `CARD (orders f* n) <> 0` by decide_tac >>
  `FINITE (orders f* n)` by rw[field_orders_finite] >>
  metis_tac[field_orders_element_order, CARD_EQ_0, MEMBER_NOT_EMPTY]);

(* Theorem: FiniteField r /\ s <<= r ==>
            !n. n divides (CARD B* ) ==> ((orders s* n) = (orders f* n)) *)
(* Proof:
   Note FiniteField s                        by subfield_finite_field
    and (orders s* n) SUBSET (orders f* n)   by subfield_orders_subset
   Note 0 < CARD B*                          by field_nonzero_card_pos, field_mult_carrier
    ==> 0 < n                                by ZERO_DIVIDES, NOT_ZERO_LT_ZERO
   Thus CARD (orders s* n) = phi n           by field_orders_card, field_mult_carrier, 0 < n
    Now CARD B* divides CARD F*              by finite_field_subfield_nonzero_card_divides
    ==> n divides CARD F*                    by DIVIDES_TRANS
   Thus CARD (orders f* n) = phi n           by field_orders_card, field_mult_carrier, 0 < n
   Note FINITE (orders f* n)                 by field_orders_finite
    and FINITE (orders s* n)                 by SUBSET_FINITE
   ==> (orders s* n) = (orders f* n)         by SUBSET_EQ_CARD
*)
val subfield_orders_equal = store_thm(
  "subfield_orders_equal",
  ``!(r:'a field) s. FiniteField r /\ s <<= r ==>
   !n. n divides (CARD B* ) ==> ((orders s* n) = (orders f* n))``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteField s` by metis_tac[subfield_finite_field] >>
  `(orders s* n) SUBSET (orders f* n)` by rw[subfield_orders_subset] >>
  `0 < CARD B*` by rw[field_nonzero_card_pos, field_mult_carrier] >>
  `0 < n` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `CARD (orders s* n) = phi n` by metis_tac[field_orders_card, field_mult_carrier] >>
  `CARD B* divides CARD F*` by rw[finite_field_subfield_nonzero_card_divides] >>
  `n divides CARD F*` by metis_tac[DIVIDES_TRANS] >>
  `CARD (orders f* n) = phi n` by metis_tac[field_orders_card, field_mult_carrier] >>
  rw[field_orders_finite, SUBSET_EQ_CARD]);

(* Theorem: FiniteField r ==> !n. (?x. x IN R+ /\ (forder x = n)) <=> n divides (CARD R+) *)
(* Proof:
   If part: x IN R+ /\ forder x = n ==> n divides (CARD R+), true  by field_order_divides
   Only-if part: n divides (CARD R+) ==> ?x. x IN R+ /\ (forder x = n)
      Note 0 < CARD R+                   by field_nonzero_card_pos
       ==> 0 < n                         by ZERO_DIVIDES, NOT_ZERO_LT_ZERO, 0 < CARD R+
      Thus CARD (orders f* n) = phi n    by field_orders_card, 0 < n
       and 0 < phi n                     by phi_pos, 0 < n
        so CARD (orders f* n) <> 0       by NOT_ZERO_LT_ZERO
      Note FINITE (orders f* n)          by field_orders_finite
        so (orders f* n) <> {}           by CARD_EQ_0
       ==> ?x. x IN orders f* n          by MEMBER_NOT_EMPTY
       ==> x IN R+ /\ (forder x = n)     by field_orders_element_property
*)
val field_order_divides_iff = store_thm(
  "field_order_divides_iff",
  ``!r:'a field. FiniteField r ==> !n. (?x. x IN R+ /\ (forder x = n)) <=> n divides (CARD R+)``,
  rpt (stripDup[FiniteField_def]) >>
  rw[EQ_IMP_THM] >-
  rw[field_order_divides] >>
  `0 < CARD R+` by rw[field_nonzero_card_pos] >>
  `0 < n` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `CARD (orders f* n) = phi n` by metis_tac[field_orders_card] >>
  `0 < phi n` by rw[phi_pos] >>
  `FINITE (orders f* n)` by rw[field_orders_finite] >>
  `?x. x IN orders f* n` by metis_tac[CARD_EQ_0, NOT_ZERO_LT_ZERO, MEMBER_NOT_EMPTY] >>
  metis_tac[field_orders_element_property]);

(* Theorem alias *)
val field_order_exists = save_thm("field_order_exists", field_order_divides_iff);

(* ------------------------------------------------------------------------- *)
(* Unity Polynomial as Product of Cyclotomic Polynomials                     *)
(* ------------------------------------------------------------------------- *)

(* Note:
   These properties of cyclotomic polynomials depends on field_orders_eq,
   which depends on the roots of Unity, the unity polynomial.
*)

(* Theorem: FiniteField r ==> !n. n divides CARD R+ ==> !m. (cyclo m = cyclo n) <=> (m = n) *)
(* Proof:
    Let s = (orders f* m), t = (orders f* n).
   Then FINITE s /\ FINITE t          by field_orders_finite
    and s SUBSET R /\ t SUBSET R      by field_orders_subset_carrier

          cyclo m = cyclo n
   <=> PIFACTOR s = PIFACTOR t        by poly_cyclo_def
   <=>          s = t                 by poly_prod_factors_eq
   <=>          m = n                 by field_orders_eq, n divides CARD R+
*)
val poly_cyclo_eq = store_thm(
  "poly_cyclo_eq",
  ``!r:'a field. FiniteField r ==> !n. n divides CARD R+ ==> !m. (cyclo m = cyclo n) <=> (m = n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `s = (orders f* m)` >>
  qabbrev_tac `t = (orders f* n)` >>
  `FINITE s /\ FINITE t` by rw[field_orders_finite, Abbr`s`, Abbr`t`] >>
  `s SUBSET R /\ t SUBSET R` by rw[field_orders_subset_carrier, Abbr`s`, Abbr`t`] >>
  metis_tac[poly_cyclo_def, poly_prod_factors_eq, field_orders_eq]);

(* Theorem: FiniteField r ==> !n. deg (cyclo n) = if n divides CARD F* then phi n else 0) *)
(* Proof:
   If n = 0,
      Note 0 < CARD R+            by field_nonzero_card_pos
      thus ~(0 divides CARD R+)   by ZERO_DIVIDES

        deg (cyclo 0)
      = deg |1|              by poly_cyclo_0
      = 0                    by poly_deg_0
      the same as formula.
   If n <> 0,
      Then 0 < n,
        deg (cyclo n)
      = CARD (orders f* n)   by poly_cyclo_deg
      = the formula          by field_orders_card 0 < n
*)
val poly_cyclo_deg_eqn = store_thm(
  "poly_cyclo_deg_eqn",
  ``!r:'a field. FiniteField r ==> !n. deg (cyclo n) = if n divides CARD R+ then phi n else 0``,
  rpt (stripDup[FiniteField_def]) >>
  Cases_on `n = 0` >| [
    `0 < CARD R+` by rw[field_nonzero_card_pos] >>
    `~(0 divides CARD R+)` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
    rw[poly_cyclo_0],
    `0 < n` by decide_tac >>
    metis_tac[poly_cyclo_deg, field_orders_card]
  ]);

(* Theorem: FiniteField r ==> !n. ~(n divides CARD R+) ==> (cyclo n = |1|) *)
(* Proof:
   Note monic (cyclo n)         by poly_cyclo_monic
    and deg (cyclo n) = 0       by poly_cyclo_deg_eqn, ~(n divides CARD R+)
    ==> cyclo n = |1|           by poly_monic_deg_0
*)
val poly_cyclo_eq_poly_one = store_thm(
  "poly_cyclo_eq_poly_one",
  ``!r:'a field. FiniteField r ==> !n. ~(n divides CARD R+) ==> (cyclo n = |1|)``,
  rpt (stripDup[FiniteField_def]) >>
  `monic (cyclo n)` by rw[poly_cyclo_monic] >>
  `deg (cyclo n) = 0` by rw[poly_cyclo_deg_eqn] >>
  rw[GSYM poly_monic_deg_0]);

(* Theorem: FiniteField r ==> !m n. m divides n ==> (cyclo m) pdivides (unity n) *)
(* Proof:
   Note (orders f* m) SUBSET roots (unity n)        by field_orders_subset_unity_roots
    and poly (unity n)                              by poly_unity_poly
    ==> PIFACTOR (orders f* m) pdivides (unity n)   by poly_prod_factors_divides
     or (cyclo m) pdivides (unity n)                by poly_cyclo_def
*)
val poly_cyclo_divides_poly_unity = store_thm(
  "poly_cyclo_divides_poly_unity",
  ``!r:'a field. FiniteField r ==> !m n. m divides n ==> (cyclo m) pdivides (unity n)``,
  rpt (stripDup[FiniteField_def]) >>
  `(orders f* m) SUBSET roots (unity n)` by rw[field_orders_subset_unity_roots] >>
  `PIFACTOR (orders f* m) pdivides (unity n)` by rw[poly_prod_factors_divides] >>
  metis_tac[poly_cyclo_def]);

(* Theorem: FiniteField r ==> !n. n divides CARD R+ ==> (unity n = PPIMAGE cyclo (divisors n)) *)
(* Proof:
    Let p = PPIMAGE cyclo (divisors n).
    Let s = IMAGE cyclo (divisors n)
   Note FINITE (divisors n)                          by divisors_finite
     so FINITE s                                     by IMAGE_FINITE
    and mset s                                       by poly_cyclo_monic, IN_IMAGE

   Step 1: show p pdivides (unity n)
   Note pcoprime_set s                               by poly_cyclo_image_coprime_set
    and poly (unity n)                               by poly_unity_poly
   Also !p. p IN s
    ==> ?m. m IN (divisors n) /\ p = cyclo m         by IN_IMAGE
    ==>     m divides n /\ p = cyclo m               by divisors_element
    ==>     m divides (CARD R+) /\ p = cyclo m       by DIVIDES_TRANS
    ==>     p pdivides (unity n)                     by poly_cyclo_divides_poly_unity
    Thus PPROD s pdivides (unity n)                  by poly_prod_coprime_set_divides
      or p pdivides (unity n)                        by notation

   Step 2: show deg p = deg (unity n)
   Note !m. m IN (divisors n)
     ==> m divides n                                 by divisors_element
     ==> m divides (CARD R+)                         by DIVIDES_TRANS
     ==> (deg (cyclo m) = phi m)                     by poly_cyclo_deg_eqn
     ==> (deg o cyclo) m = phi m                     by o_THM
    Also !x y. x IN (divisors n) /\ y IN (divisors n)
     ==> x divides n /\ y divides n                  by divisors_element
     ==> x divides (CARD R+) /\ y divides (CARD R+)  by DIVIDES_TRANS
     ==> cyclo x = cyclo y <=> x = y                 by poly_cyclo_eq
     and cyclo x and cyclo y IN univ(:'a poly)       by IN_UNIV
    Thus INJ cyclo (divisors n) univ(:'a poly)       by INJ_DEF
     and FINITE (divisors n)                         by divisors_finite

        deg p
      = deg (PPROD s)                                by notation
      = SIGMA deg s                                  by poly_monic_prod_set_deg
      = SIGMA deg (IMAGE cyclo (divisors n))         by notation
      = SIGMA (deg o cyclo) (divisors n)             by sum_image_by_composition, INJ above
      = SIGMA phi (divisors n)                       by SUM_IMAGE_CONG, above
      = n                                            by Gauss_little_thm
      = deg (unity n)                                by poly_unity_deg

   Step 3: conclude
   Note monic p                                      by poly_monic_prod_set_monic, miset s
   Note 0 < CARD R+                                  by field_nonzero_card_pos
   thus 0 < n                                        by ZERO_DIVIDES
    ==> monic (unity n)                              by poly_unity_monic, 0 < n

   With monic p /\ monic (unity n)                   by above
    and deg p = deg (unity n)                        by Step 2
    and p pdivides (unity n)                         by Step 1
    ==> p = (unity n)                                by poly_monic_divides_eq_deg_eq
*)
val poly_unity_eq_poly_cyclo_product = store_thm(
  "poly_unity_eq_poly_cyclo_product",
  ``!r:'a field. FiniteField r ==> !n. n divides CARD R+ ==> (unity n = PPIMAGE cyclo (divisors n))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `p = PPIMAGE cyclo (divisors n)` >>
  qabbrev_tac `s = IMAGE cyclo (divisors n)` >>
  `FINITE s` by rw[divisors_finite, Abbr`s`] >>
  `mset s` by metis_tac[poly_cyclo_monic, IN_IMAGE] >>
  `p pdivides (unity n)` by
  (`pcoprime_set s` by rw[poly_cyclo_image_coprime_set, Abbr`s`] >>
  `poly (unity n)` by rw[] >>
  `!p. p IN s ==> p pdivides (unity n)` by prove_tac[IN_IMAGE, divisors_element, poly_cyclo_divides_poly_unity, DIVIDES_TRANS] >>
  rw[poly_prod_coprime_set_divides, Abbr`p`]) >>
  `deg p = deg (unity n)` by
    (`!m. m IN (divisors n) ==> (deg (cyclo m) = phi m)` by metis_tac[divisors_element, poly_cyclo_deg_eqn, DIVIDES_TRANS] >>
  (`INJ cyclo (divisors n) univ(:'a poly)` by (rw[INJ_DEF] >> metis_tac[divisors_element, poly_cyclo_eq, DIVIDES_TRANS])) >>
  `FINITE (divisors n)` by rw[divisors_finite] >>
  `deg p = SIGMA deg s` by rw[poly_monic_prod_set_deg, Abbr`p`] >>
  `_ = SIGMA (deg o cyclo) (divisors n)` by rw[GSYM sum_image_by_composition] >>
  `_ = SIGMA phi (divisors n)` by rw[SUM_IMAGE_CONG] >>
  rw[Gauss_little_thm, poly_unity_deg]) >>
  `monic p` by rw[poly_monic_prod_set_monic, Abbr`p`] >>
  `0 < CARD R+` by rw[field_nonzero_card_pos] >>
  `0 < n` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `monic (unity n)` by rw[] >>
  metis_tac[poly_monic_divides_eq_deg_eq]);

(* This is a major milestone theorem! *)

(* Theorem: FiniteField r ==> (unity (CARD R+) = PPIMAGE cyclo (divisors (CARD R+))) *)
(* Proof: by poly_unity_eq_poly_cyclo_product, DIVIDES_REFL *)
val poly_unity_eq_poly_cyclo_product_special = store_thm(
  "poly_unity_eq_poly_cyclo_product_special",
  ``!r:'a field. FiniteField r ==> (unity (CARD R+) = PPIMAGE cyclo (divisors (CARD R+)))``,
  rw_tac std_ss[poly_unity_eq_poly_cyclo_product, DIVIDES_REFL]);

(* Theorem: FiniteField r ==> (unity (CARD R+) = PPROD {cyclo n | n IN divisors (CARD R+)}) *)
(* Proof:
      unity (CARD R+)
    = PPIMAGE cyclo (divisors (CARD R+))          by poly_unity_eq_poly_cyclo_product_special
    = PPROD {cyclo n | n IN divisors (CARD R+)}   by IMAGE_DEF
*)
val poly_unity_eq_poly_cyclo_product_special_alt = store_thm(
  "poly_unity_eq_poly_cyclo_product_special_alt",
  ``!r:'a field. FiniteField r ==> (unity (CARD R+) = PPROD {cyclo n | n | n IN divisors (CARD R+)})``,
  rpt strip_tac >>
  `unity (CARD R+) = PPIMAGE cyclo (divisors (CARD R+))` by rw[poly_unity_eq_poly_cyclo_product_special] >>
  `IMAGE cyclo (divisors (CARD R+)) = {cyclo n | n IN divisors (CARD R+)}` by rw[IMAGE_DEF] >>
  rw[]);

(* Theorem: FiniteField r /\ n divides CARD R+ ==> (unity n = PPROD {cyclo k | k IN divisors n}) *)
(* Proof:
      unity n
    = PPIMAGE cyclo (divisors n)          by poly_unity_eq_poly_cyclo_product
    = PPROD {cyclo k | k IN divisors n}   by IMAGE_DEF
*)
val poly_unity_eq_poly_cyclo_product_alt = store_thm(
  "poly_unity_eq_poly_cyclo_product_alt",
  ``!(r:'a field) n. FiniteField r /\ n divides CARD R+ ==> (unity n = PPROD {cyclo k | k IN divisors n})``,
  rpt strip_tac >>
  `unity n = PPIMAGE cyclo (divisors n)` by rw[poly_unity_eq_poly_cyclo_product] >>
  `IMAGE cyclo (divisors n) = {cyclo k | k IN divisors n}` by rw[IMAGE_DEF] >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* Roots of Unity is a Subgroup                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r ==> !n. 0 < n ==> (subset_group f* (roots (unity n))) <= f* *)
(* Proof:
   By subset_group_subgroup, this is to show:
   (1) roots (unity n) SUBSET F*
       Note roots (unity n) SUBSET R      by poly_roots_subset
        and #0 NOTIN roots (unity n)      by poly_unity_roots_nonzero, poly_roots_member, 0 < n
        and F* = R+                       by field_mult_carrier
        ==> roots (unity n) SUBSET F*     by field_nonzero_eq, SUBSET_DEF
   (2) roots (unity n) <> {}, true        by poly_unity_roots_nonempty
   (3) Group f*, true                     by field_mult_group
   (4) !x y. x IN roots (unity n) /\ y IN roots (unity n) ==> f*.op x (f*.inv y) IN roots (unity n)
       Note f*.op = $*                    by field_nonzero_mult_property
        and x IN R /\ y IN R              by poly_roots_member
       Also #0 NOTIN roots (unity n)      by poly_unity_root_nonzero, poly_roots_member, 0 < n
        ==> y IN R+                       by field_nonzero_eq, poly_roots_member
        ==> f*.inv y = |/ y               by field_mult_inv
        ==> f*.inv y IN R                 by field_inv_element, y IN R+
       By poly_roots_member, this is to show:
       (1) x * f*.inv y IN R
           Thus x * f*.inv y IN R              by field_mult_element, x IN R
       (2) root (unity n) x /\ root (unity n) y ==> root (unity n) (x * f*.inv y)
           Note x ** n = #1                    by poly_unity_root_property, x IN R
            and y ** n = #1                    by poly_unity_root_property, y IN R
           Thus (f*.inv y) ** n = #1           by field_inv_exp, y IN R+
            ==> (x * (f*.inv y)) ** n = #1     by field_mult_exp
             or root (unity n) (x * f*.inv y)  by poly_unity_root_property
*)
val poly_unity_roots_subgroup = store_thm(
  "poly_unity_roots_subgroup",
  ``!r:'a field. Field r ==> !n. 0 < n ==> (subset_group f* (roots (unity n))) <= f*``,
  rpt strip_tac >>
  (REVERSE (irule subset_group_subgroup >> rpt conj_tac)) >| [
    `roots (unity n) SUBSET R` by rw[poly_roots_subset] >>
    `#0 NOTIN roots (unity n)` by rw[poly_unity_root_nonzero, poly_roots_member] >>
    `F* = R+` by rw[field_mult_carrier] >>
    metis_tac[field_nonzero_eq, SUBSET_DEF],
    rw[poly_unity_roots_nonempty],
    rw[field_mult_group],
    rpt strip_tac >>
    `#0 NOTIN roots (unity n)` by rw[poly_unity_root_nonzero, poly_roots_member] >>
    `x IN R /\ y IN R /\ y IN R+` by metis_tac[field_nonzero_eq, poly_roots_member] >>
    `(f*.inv y) IN R` by rw_tac std_ss[field_inv_element, field_mult_inv] >>
    rw_tac std_ss[poly_roots_member, field_nonzero_mult_property] >-
    rw[] >>
    `Ring r` by rw[] >>
    `(x ** n = #1) /\ (y ** n = #1)` by metis_tac[poly_unity_root_property, poly_roots_member] >>
    `(f*.inv y) ** n = #1` by rw[field_inv_exp, field_mult_inv] >>
    `(x * (f*.inv y)) ** n = #1` by rw[field_mult_exp] >>
    rw[poly_unity_root_property]
  ]);

(* ------------------------------------------------------------------------- *)
(* Subfield Classification - by field orders                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==>
            !n. (?s. s <<= r /\ (fdim s = n)) <=> ?x. x IN R+ /\ (forder x = char r ** n - 1) *)
(* Proof:
   Let p = char r.
   If part: s <<= r ==> ?x. x IN R+ /\ (forder x = p ** fdim s - 1)
   Idea: A subfield is a finite field, so it has a primitive.
         The primitive is in R+, with order = CARD B*

      Note FiniteField s            by subfield_finite_field
       and B* = ring_nonzero s      by field_mult_carrier
      Note ?x. x IN B* /\ (order s* x = CARD B* )  by field_order_exists, DIVIDES_REFL, FiniteField s
       and order s* x = forder x    by subfield_order, field_nonzero_element
           CARD B*
         = CARD B - 1               by finite_field_nonzero_carrier_card
         = p ** fdim s - 1          by finite_field_card_alt, subfield_char
       and x IN B* ==> x IN R+      by subfield_nonzero_element
      Take this x, the result follows.

   Only-if part: x IN R+ /\ (forder x = p ** n - 1) ==> ?s. s <<= r /\ (fdim s = n)
   Idea: forder x = k means x ** j for j = 1 to k  are distinct.
         These are roots of X ** k - |1|, and no more since CARD (roots p) <= deg p when p <> |0|.
         Add in #0, then {#0} UNION (roots (unity k)) = roots (master (k + 1)).
         The roots of (master (k + 1) forms a subfield.
         Take s = subset_field r (roots (master (k + 1))),
         Express CARD B to find the dimension (fdim s = n).

      Let k = p ** n - 1.
      Note n <> 0                            by field_order_eq_0, field_nonzero_eq, EXP_0
       and 1 < p                             by finite_field_char_gt_1
        so 1 < p ** n                        by ONE_LT_EXP
      Thus 0 < k /\ (p ** n = k + 1)         by arithmetic
      Take s = subset_field r (roots (master (k + 1))).
      Then s <<= r                           by poly_master_roots_subfield
      The remaining goal: fdim s = n
      Note B = roots (master (k + 1))        by subset_field_property
             = {#0} UNION roots (unity k)    by poly_master_roots_by_unity_roots_alt
      Also FINITE (roots (unity k))          by poly_unity_roots_finite, 0 < k
       and FINITE {#0}                       by FINITE_SING
       and DISJOINT {#0} (roots (unity k))   by poly_unity_roots_no_zero, IN_DISJOINT
       ==> FINITE B                          by FINITE_UNION
       ==> FiniteField s                     by FiniteField_def

      Since roots (unity k)
          = (Generated f* x).carrier         by poly_unity_roots_generator, field_nonzero_eq
            CARD B
          = 1 + CARD (roots (unity k))       by CARD_UNION_DISJOINT, CARD_SING
          = 1 + k                            by generated_group_card, field_mult_group, field_mult_carrier
        ==> fdim s = n                       by finite_field_dim_eq, subfield_char, ADD_COMM
*)
val finite_field_subfield_exists_by_field_order = store_thm(
  "finite_field_subfield_exists_by_field_order",
  ``!r:'a field. FiniteField r ==>
   !n. (?s. s <<= r /\ (fdim s = n)) <=> ?x. x IN R+ /\ (forder x = char r ** n - 1)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `p = char r` >>
  rw[EQ_IMP_THM] >| [
    `FiniteField s` by metis_tac[subfield_finite_field] >>
    `B* = ring_nonzero s` by rw[field_mult_carrier] >>
    `?x. x IN B* /\ (order s* x = CARD B* )` by metis_tac[field_order_exists, DIVIDES_REFL] >>
    `order s* x = forder x` by metis_tac[subfield_order, field_nonzero_element] >>
    `CARD B = p ** fdim s` by rw[finite_field_card_alt, subfield_char, Abbr`p`] >>
    `CARD B* = CARD B - 1` by rw[finite_field_nonzero_carrier_card] >>
    metis_tac[subfield_nonzero_element],
    qabbrev_tac `k = p ** n - 1` >>
    `n <> 0` by metis_tac[field_order_eq_0, field_nonzero_eq, EXP_0, DECIDE``1 - 1 = 0``] >>
    `1 < p ** n` by rw[finite_field_char_gt_1, ONE_LT_EXP, Abbr`p`] >>
    `0 < k /\ (p ** n = k + 1)` by rw[Abbr`k`] >>
    qabbrev_tac `s = subset_field r (roots (master (k + 1)))` >>
    `s <<= r` by metis_tac[poly_master_roots_subfield, Abbr`s`] >>
    qexists_tac `s` >>
    simp[] >>
    `B = roots (master (k + 1))` by rw_tac std_ss[subset_field_property, Abbr`s`] >>
    `_ = {#0} UNION roots (unity k)` by rw[poly_master_roots_by_unity_roots_alt] >>
    `FINITE (roots (unity k)) /\ FINITE {#0}` by rw[poly_unity_roots_finite] >>
    `DISJOINT {#0} (roots (unity k))` by rw[poly_unity_roots_no_zero] >>
    `FINITE B` by metis_tac[FINITE_UNION] >>
    `FiniteField s` by metis_tac[FiniteField_def] >>
    `roots (unity k) = (Generated f* x).carrier` by metis_tac[poly_unity_roots_generator, field_nonzero_eq] >>
    `CARD B = 1 + CARD (roots (unity k))` by metis_tac[CARD_UNION_DISJOINT, CARD_SING] >>
    `_ = 1 + k` by metis_tac[generated_group_card, field_mult_group, field_mult_carrier] >>
    metis_tac[finite_field_dim_eq, subfield_char, ADD_COMM]
  ]);

(* Theorem: FiniteField r ==>
            !n. (?s. s <<= r /\ (fdim s = n)) <=> (orders f* (char r ** n - 1) <> EMPTY) *)
(* Proof:
   Let p = char r.
       ?s. s <<= r /\ (fdim s = n))
   <=> ?x. x IN R+ /\ (forder x = p ** n - 1)    by finite_field_subfield_exists_by_field_order
   <=> (orders f* (p ** n - 1)) <> {}            by field_orders_element_property, MEMBER_NOT_EMPTY
*)
val finite_field_subfield_exists_by_field_orders = store_thm(
  "finite_field_subfield_exists_by_field_orders",
  ``!r:'a field. FiniteField r ==>
   !n. (?s. s <<= r /\ (fdim s = n)) <=> (orders f* (char r ** n - 1) <> EMPTY)``,
  rpt (stripDup[FiniteField_def]) >>
  metis_tac[finite_field_subfield_exists_by_field_order, field_orders_element_property, MEMBER_NOT_EMPTY]);

(* Theorem: FiniteField r ==> !n. (?s. s <<= r /\ (fdim s = n)) <=> n divides fdim r *)
(* Proof:
   Let p = char r.
   Then 1 < p                                    by finite_field_char_gt_1
    and CARD R+ = p ** fdim r - 1                by finite_field_mult_carrier_card_alt
       ?s. s <<= r /\ (fdim s = n))
   <=> (orders f* (p ** n - 1)) <> {}            by finite_field_subfield_exists_by_field_orders
   <=> (p ** n - 1) divides (p ** fdim r - 1)    by finite_field_orders_nonempty_iff
   <=> n divides (fdim r)                        by power_predecessor_divisibility, 1 < p
*)
val finite_field_subfield_existence_alt = store_thm(
  "finite_field_subfield_existence_alt",
  ``!r:'a field. FiniteField r ==> !n. (?s. s <<= r /\ (fdim s = n)) <=> n divides fdim r``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `p = char r` >>
  `1 < p` by rw[finite_field_char_gt_1, Abbr`p`] >>
  `CARD R+ = p ** fdim r - 1` by rw[finite_field_mult_carrier_card_alt, Abbr`p`] >>
  `(?s. s <<= r /\ (fdim s = n)) <=>
    (orders f* (p ** n - 1)) <> {}` by metis_tac[finite_field_subfield_exists_by_field_orders] >>
  `_ = (p ** n - 1) divides (p ** fdim r - 1)` by rw[GSYM finite_field_orders_nonempty_iff] >>
  `_ = n divides (fdim r)` by rw[power_predecessor_divisibility] >>
  metis_tac[]);

(* Another route to arrive at this subfield classification theorem. *)

(* ------------------------------------------------------------------------- *)
(* Unity Polynomial as Modulus                                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (X ** k == |1|) (pm (unity k)) *)
(* Proof:
   If k = 0,
      Then X ** k = |1| = |1|       by poly_exp_0
      Hence true                    by poly_mod_reflexive
   Otherwise, 0 < k,
   Let z = unity k,
    Then  ulead z                   by poly_unity_ulead, 0 < k
   Since  z % z = |0|               by poly_div_mod_id
      so  (z == |0|) (pm z)         by pmod_zero
    Hence (X ** k == |1|) (pm z)    by poly_pmod_sub_eq_zero
*)
val poly_unity_pmod_eqn = store_thm(
  "poly_unity_pmod_eqn",
  ``!r:'a ring. Ring r ==> !k. (X ** k == |1|) (pm (unity k))``,
  rpt strip_tac >>
  Cases_on `k = 0` >-
  rw[poly_mod_reflexive] >>
  qabbrev_tac `z = unity k` >>
  `poly X /\ poly (X ** k) /\ poly |1| /\ ulead z` by rw[poly_unity_ulead, Abbr`z`] >>
  `z % z = |0|` by rw[poly_div_mod_id] >>
  `(z == |0|) (pm z)` by rw[pmod_zero] >>
  rw[poly_pmod_sub_eq_zero, Abbr`z`]);

(* Theorem: 0 < k /\ (X ** k == |1|) (pm z) ==> !m. (X ** m == X ** (m MOD k)) (pm z)  *)
(* Proof:
   Let z = unity k,
    Then ulead z                by poly_unity_ulead, 0 < k
   Since 0 < k, m = m DIV k * k + m MOD k   by DIVISION
   or  m = q * k + n            where q = m DIV k, n = m MOD k.
     X ** m
   = X ** (q * k + n)           by above
   = X ** (k * q + n)           by MULT_COMM
   = X ** (k * q) * X ** n      by poly_exp_add
   = (X ** k) ** q * (X ** n)   by poly_exp_mult
   == |1| ** q * (X ** n)       by poly_unity_pmod_eqn, X ** k == |1| (pm z)
   = |1| * (X ** n)             by poly_one_exp
   = X ** n                     by poly_mult_lone
   Hence overall,
   (X ** m == X ** (m MOD k)) (pm z)  by pmod_exp_eq, poly_mod_reflexive, pmod_mult.
   Or, apply poly_pmod_exp_mod and poly_unity_pmod_eqn.
*)
val poly_unity_exp_mod = store_thm(
  "poly_unity_exp_mod",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==>
    !m. (X ** m == X ** (m MOD k)) (pm (unity k))``,
  rw[poly_pmod_exp_mod, poly_unity_pmod_eqn]);

(* Theorem: 0 < k ==> (n MOD k = m MOD k) ==> (X ** n == X ** m) (pm z) *)
(* Proof:
   Let z = unity k, and pmonic z               by poly_unity_pmonic
   Since  (X ** n == X ** (n MOD k)) (pm z)    by poly_unity_exp_mod
     and  (X ** m == X ** (m MOD k)) (pm z)    by poly_unity_exp_mod
   Since  n MOD k = m MOD k                    by given
   Hence  (X ** n == X ** m) (pm z)            by poly_mod_transitive, poly_mod_symmetric
   Or, apply poly_pmod_exp_mod_eq and poly_unity_pmod_eqn.
*)
val poly_unity_exp_mod_eq = store_thm(
  "poly_unity_exp_mod_eq",
  ``!r:'a ring. Ring r ==> !k. 0 < k ==>
    !n m. (n MOD k = m MOD k) ==> (X ** n == X ** m) (pm (unity k))``,
  metis_tac[poly_pmod_exp_mod_eq, poly_unity_lead, poly_X, poly_unity_poly, poly_unity_pmod_eqn, ring_unit_one]);

(* Theorem: Field r ==> !n. 0 < n ==> !h. mifactor h (unity n) ==> h <> X *)
(* Proof:
   By contradiction. Suppose h = X.
   Let z = unity n.
   Then  (X ** n == |1|) (pm z)    by poly_unity_pmod_eqn
     or  (X ** n == |1|) (pm h)    by poly_mod_eq_divisor, z % h = |0|
     so  (h ** n == |1|) (pm h)    by h = X.
    But  h % h = |0|               by poly_div_mod_id
     or  (h == |0|) (pm h)         by pmod_zero
     so  (h ** n == |0|) (pm h)    by pmod_exp_eq, poly_zero_exp
   This means  |1| % h = |0| % h   by pmod_def_alt
           or      |1| = |0|       by poly_mod_one, poly_mod_zero
   which violates #1 <> #0         by poly_one_eq_poly_zero
*)
val poly_unity_irreducible_factor_not_X = store_thm(
  "poly_unity_irreducible_factor_not_X",
  ``!r:'a field. Field r ==> !n. 0 < n ==> !h. mifactor h (unity n) ==> h <> X``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `z = unity n` >>
  `pmonic z` by rw[poly_unity_pmonic, Abbr`z`] >>
  `pmonic h` by rw[poly_irreducible_deg_nonzero] >>
  `poly X /\ poly (X ** n) /\ poly |1| /\ poly |0|` by rw[] >>
  `(X ** n == |1|) (pm z)` by rw[poly_unity_pmod_eqn, Abbr`z`] >>
  `(X ** n == |1|) (pm h)` by metis_tac[poly_mod_eq_divisor] >>
  `n <> 0` by decide_tac >>
  `(h == |0|) (pm h)` by metis_tac[poly_div_mod_id, pmod_zero] >>
  `(h ** n == |0|) (pm h)` by metis_tac[pmod_exp_eq, poly_zero_exp] >>
  `|1| = |0|` by metis_tac[pmod_def_alt, poly_mod_one, poly_mod_zero] >>
  metis_tac[poly_one_eq_poly_zero]);

(* Theorem: !n h. mifactor h (unity n) /\ (deg h = 1) ==>
            ?c. c IN R /\ (h = factor c) /\ (c ** n = #1) *)
(* Proof:
       mifactor h (unity n)
   ==> monic h /\ (unity n) % h = |0|   by notation
       monic h /\ (deg h = 1)
   ==> ?c. c IN R /\ (h = factor c)     by poly_monic_deg1_factor
       (unity n) % (factor c) = |0|
   ==> root (unity n) c                 by poly_root_thm
   ==> eval (unity n) c = #0            by poly_root_def
   But eval (unity n) c = c ** n - #1   by poly_unity_eval
   Thus c ** n = #1                     by ring_sub_eq_zero
*)
val poly_unity_irreducible_factor_deg_1 = store_thm(
  "poly_unity_irreducible_factor_deg_1",
  ``!r:'a field. Field r ==> !n h. mifactor h (unity n) /\ (deg h = 1) ==>
    ?c. c IN R /\ (h = factor c) /\ (c ** n = #1)``,
  rpt strip_tac >>
  `?c. c IN R /\ (h = factor c)` by rw[poly_monic_deg1_factor] >>
  `root (unity n) c` by rw[poly_root_thm] >>
  `#0 = eval (unity n) c` by rw[GSYM poly_root_def] >>
  `_ = c ** n - #1` by rw[poly_unity_eval] >>
  `Ring r /\ c ** n IN R /\ #1 IN R` by rw[] >>
  metis_tac[ring_sub_eq_zero]);

(* Theorem: Field r /\ 1 < n /\ n < char r ==>
            ?z. mifactor z (unity n) /\ (forderz X) divides n *)
(* Proof:
   Note ?z. mifactor z (unity n) /\ z <> unity 1
                                         by poly_unity_irreducible_factor_exists
   Take this z, the goal is: forderz X divides n.

   Note 0 < n = deg (unity n)            by poly_unity_deg, 1 < n
    and 0 < deg z                        by poly_irreducible_deg_nonzero, ipoly z
   Thus z <> |0| and (unity n) <> |0|    by poly_deg_zero
   Also (X ** k == |1|) (pm (unity n))   by poly_unity_pmod_eqn
    ==> (X ** k == |1|) (pm z)           by poly_field_mod_eq_divisor, z <> |0|, unity n <> |0|
   Thus (forderz X) divides n            by poly_X_order_divides
*)
val poly_unity_irreducible_factor_with_order = store_thm(
  "poly_unity_irreducible_factor_with_order",
  ``!(r:'a field) n. Field r /\ 1 < n /\ n < char r ==>
     ?z. mifactor z (unity n) /\ (forderz X) divides n``,
  rpt strip_tac >>
  `?z. mifactor z (unity n) /\ z <> unity 1` by rw[poly_unity_irreducible_factor_exists] >>
  qexists_tac `z` >>
  rw_tac bool_ss[] >>
  `deg (unity n) = n` by rw[] >>
  `0 < n` by decide_tac >>
  `0 < deg z` by rw[poly_irreducible_deg_nonzero] >>
  `poly (unity n) /\ poly z /\ poly (X ** n) /\ poly |1|` by rw[] >>
  `z <> |0| /\ (unity n) <> |0|` by metis_tac[poly_deg_zero, NOT_ZERO] >>
  `(X ** n == |1|) (pm (unity n))` by rw[poly_unity_pmod_eqn] >>
  `(X ** n == |1|) (pm z)` by metis_tac[poly_field_mod_eq_divisor] >>
  rw[poly_X_order_divides]);

(* ------------------------------------------------------------------------- *)
(* Roots of Unity                                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: poly p /\ (peval (unity n) p == |0|) (pm z) ==> p <> |0| *)
(* Proof:
     Note #1 <> #0                             by poly_deg_pos_ring_one_ne_zero, 0 < deg z
     By contradiction, suppose p = |0|.
     Then deg |0| = 0                          by poly_deg_zero
       so (peval (unity n) |0| == |0|) (pm z)  by above
      But   peval (unity n) |0|
          = |0| ** n - |1|                     by poly_peval_X_exp_n_sub_c, poly_ring_sum_1
          = |0| - |1|                          by poly_zero_exp, 0 < n.
     Therefore ( |0| - |1| == |0|) (pm z)      by above
            or ( |0| == |1|) (pm z)            by pmod_zero, pmod_eq
            or ( |1| == |0|) (pm z)            by poly_mod_symmetric
            or |0| = |1|                       by pmod_zero, poly_mod_one
     This implies #1 = #0, a contradiction     by poly_zero_eq_one
*)
val poly_unity_peval_root_nonzero = store_thm(
  "poly_unity_peval_root_nonzero",
  ``!r:'a ring z. Ring r /\ pmonic z ==>
   !n p. 0 < n /\ poly p /\ (peval (unity n) p == |0|) (pm z) ==> p <> |0|``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac[poly_deg_pos_ring_one_ne_zero] >>
  `n <> 0` by decide_tac >>
  `deg |0| = 0` by rw[] >>
  `peval (unity n) |0| = |0| ** n - |1|` by metis_tac[poly_peval_X_exp_n_sub_c, poly_ring_sum_1] >>
  `_ = |0| - |1|` by rw[poly_zero_exp] >>
  `( |0| - |1| == |0|) (pm z)` by metis_tac[] >>
  `( |0| == |1|) (pm z)` by metis_tac[pmod_zero, pmod_eq, poly_one_poly, poly_sub_poly] >>
  `|0| = |1|` by metis_tac[pmod_zero, poly_mod_symmetric, poly_one_poly, poly_mod_one] >>
  metis_tac[poly_zero_eq_one]);

(* Theorem: p IN (roots_of_unity ((PolyModRing r z).prod excluding |0|) n).carrier <=>
         (poly p /\ p <> |0| /\ deg p < deg z /\ (peval (unity n) p == |0|) (pm z)) *)
(* Proof:
   First, pmonic z             by poly_monic_irreducible_property
      Let g = (PolyModRing r z).prod excluding |0|
     Then g.id = |1|           by poly_mod_prod_nonzero_id, 0 < deg z
          p IN (roots_of_unity g n).carrier
      <=> p IN g.carrier /\ (g.exp p n = |1|)                        by roots_of_unity_element
      <=> poly p /\ p <> |0| /\ deg p < deg z /\ (g.exp p n = |1|)   by poly_mod_ring_nonzero_element, 0 < deg z
      <=> poly p /\ p <> |0| /\ deg p < deg z /\ ((p ** n) % z = |1|)                by poly_mod_exp_alt
      <=> poly p /\ p <> |0| /\ deg p < deg z /\ ((p ** n) % z = |1| % z)            by poly_mod_one
      <=> poly p /\ p <> |0| /\ deg p < deg z /\ ((p ** n - |1|) % z = |0|)          by poly_mod_eq
      <=> poly p /\ p <> |0| /\ deg p < deg z /\ (p ** n - |1| == |0|) (pm z)        by pmod_zero
      <=> poly p /\ p <> |0| /\ deg p < deg z /\ (peval (unity n) p == |0|) (pm z)   by poly_peval_X_exp_n_sub_c
*)
val poly_roots_of_unity_element = store_thm(
  "poly_roots_of_unity_element",
  ``!r:'a field z. Field r /\ monic z /\ ipoly z ==>
   !p n. p IN (roots_of_unity ((PolyModRing r z).prod excluding |0|) n).carrier <=>
         (poly p /\ p <> |0| /\ deg p < deg z /\ (peval (unity n) p == |0|) (pm z))``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `pmonic z` by rw[poly_monic_irreducible_property] >>
  qabbrev_tac `g = (PolyModRing r z).prod excluding |0|` >>
  `g.id = |1|` by rw[poly_mod_prod_nonzero_id, Abbr`g`] >>
  `p IN (roots_of_unity g n).carrier <=> p IN g.carrier /\ (g.exp p n = |1|)` by rw[roots_of_unity_element] >>
  `_ = (poly p /\ p <> |0| /\ deg p < deg z /\ (g.exp p n = |1|))` by metis_tac[poly_mod_ring_nonzero_element] >>
  `_ = (poly p /\ p <> |0| /\ deg p < deg z /\ ((p ** n) % z = |1|))` by metis_tac[poly_mod_exp_alt] >>
  `_ = (poly p /\ p <> |0| /\ deg p < deg z /\ ((p ** n) % z = |1| % z))` by rw[poly_mod_one] >>
  `_ = (poly p /\ p <> |0| /\ deg p < deg z /\ ((p ** n - |1|) % z = |0|))` by metis_tac[poly_mod_eq, poly_exp_poly, poly_one_poly] >>
  `_ = (poly p /\ p <> |0| /\ deg p < deg z /\ (p ** n - |1| == |0|) (pm z))` by metis_tac[pmod_zero, poly_exp_poly, poly_one_poly, poly_sub_poly] >>
  `_ = (poly p /\ p <> |0| /\ deg p < deg z /\ (peval (unity n) p == |0|) (pm z))` by metis_tac[poly_peval_X_exp_n_sub_c, poly_ring_sum_1] >>
  rw[]);

(* Theorem: 0 < n ==> (((roots_of_unity ((PolyModRing r z).prod excluding |0|) n).carrier =
                         poly_roots (PolyModRing r z) (lift (unity n)))) *)
(* Proof:
   Note pmonic z                  by poly_monic_irreducible_property
   After expanding by definitons, this is to show:
   !x. x IN (roots_of_unity ((PolyModRing r z).prod excluding |0|) n).carrier <=>
       x IN (PolyModRing r z).carrier /\ poly_root (PolyModRing r z) (lift (unity n)) x
   Now, p IN (roots_of_unity ((PolyModRing r z).prod excluding |0|) n).carrier <=>
        poly p /\ p <> |0| /\ deg p < deg z /\
        (peval (unity n) p == |0|) (pm z)                            by poly_roots_of_unity_element
   Also p IN (PolyModRing r z).carrier <=> poly p /\ deg p < deg z   by poly_mod_ring_element
   And  poly x /\ poly p /\ deg p < deg z ==>
        (poly_root (PolyModRing r z) (lift x) p <=> (peval x p % z = |0|))      by poly_mod_lift_root_by_mod_peval
     or (poly_root (PolyModRing r z) (lift x) p <=> (peval x p == |0|) (pm z))  by pmod_zero
   Also poly p /\ (peval (unity n) p == |0|) (pm z) ==> p <> |0|                by poly_unity_peval_root_nonzero
   Therefore every property is satisfied for the equality.
*)
val poly_roots_of_unity_carrier = store_thm(
  "poly_roots_of_unity_carrier",
  ``!r:'a field z. Field r /\ monic z /\ ipoly z ==>
   !n. 0 < n ==> (((roots_of_unity ((PolyModRing r z).prod excluding |0|) n).carrier =
                    poly_roots (PolyModRing r z) (lift (unity n))))``,
  rw_tac std_ss[poly_roots_def, GSPECIFICATION, EXTENSION] >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `pmonic z` by rw[poly_monic_irreducible_property] >>
  `!p n. p IN (roots_of_unity ((PolyModRing r z).prod excluding |0|) n).carrier <=>
          poly p /\ p <> |0| /\ deg p < deg z /\ (peval (unity n) p == |0|) (pm z)` by rw[GSYM poly_roots_of_unity_element] >>
  `!p. p IN (PolyModRing r z).carrier <=> poly p /\ deg p < deg z` by rw[poly_mod_ring_element] >>
  `!x p. poly x /\ poly p /\ deg p < deg z ==> (poly_root (PolyModRing r z) (lift x) p <=> (peval x p == |0|) (pm z))` by rw[poly_mod_lift_root_by_mod_peval, pmod_zero] >>
  `poly (unity n)` by rw[] >>
  metis_tac[poly_unity_peval_root_nonzero]);

(* ------------------------------------------------------------------------- *)
(* Unity primitive roots                                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < n /\ n < char r /\ (z = unity n) ==>
            ?h t. mifactor h z /\ poly t /\ t <> |0| /\ deg t < deg h /\
                 poly_root (PolyModRing r h) (lift z) t /\
                 (order ((PolyModRing r h).prod excluding |0|) t = CARD (poly_roots (PolyModRing r h) (lift z))) *)
(* Proof:
   Given z = unity n,
         ?h. mifactor h (unity n) /\ h <> unity 1    by poly_unity_irreducible_factor_exists
     and pmonic h                                    by poly_monic_irreducible_property
   Since FiniteField r /\ monic z /\ ipoly z,
         Field (PolyModRing r z)   by poly_mod_irreducible_finite_field
     Let g = (PolyModRing r h).prod excluding |0|
    Then Group g is cyclic         by finite_field_mult_group_cyclic
     Now by cyclic_uroots_has_primitive,
     ?t. t IN (roots_of_unity g n).carrier /\ (order g t = CARD (roots_of_unity g n).carrier)
    First,  t IN (roots_of_unity g n).carrier
    means poly t /\ t <> |0| /\ deg t < deg h /\ (peval z t == |0|) (pm h)      by poly_roots_of_unity_element
      or  peval z t % h = |0|                                                   by pmod_zero
      or  poly_root (PolyModRing r h) (lift z) t                                by poly_mod_lift_root_by_mod_peval
    Next, (roots_of_unity g n).carrier = poly_roots (PolyModRing r h) (lift z)  by poly_roots_of_unity_carrier
    Therefore all requirements are satisfied.
*)
val poly_primitive_root_of_unity_exists = store_thm(
  "poly_primitive_root_of_unity_exists",
  ``!r:'a field. FiniteField r ==> !n z. 1 < n /\ n < char r /\ (z = unity n) ==>
    ?h t. mifactor h z /\ poly t /\ t <> |0| /\ deg t < deg h /\
         poly_root (PolyModRing r h) (lift z) t /\ (* a root of unity *)
         (order ((PolyModRing r h).prod excluding |0|) t =
          CARD (poly_roots (PolyModRing r h) (lift z)))``,
  rpt (stripDup[FiniteField_def]) >>
  `?h. mifactor h (unity n) /\ h <> unity 1` by rw[poly_unity_irreducible_factor_exists] >>
  `pmonic h` by rw[poly_monic_irreducible_property] >>
  `FiniteField (PolyModRing r h)` by rw[poly_mod_irreducible_finite_field] >>
  `Field (PolyModRing r h) /\ FINITE (PolyModRing r h).carrier` by metis_tac[FiniteField_def] >>
  `(PolyModRing r h).sum.id = |0|` by rw[poly_mod_ring_ids] >>
  qabbrev_tac `g = (PolyModRing r h).prod excluding |0|` >>
  `cyclic g` by metis_tac[finite_field_mult_group_cyclic] >>
  `FINITE g.carrier` by rw[excluding_def, Abbr`g`] >>
  `?t. t IN (roots_of_unity g n).carrier /\ (order g t = CARD (roots_of_unity g n).carrier)` by rw[cyclic_uroots_has_primitive] >>
  `poly t /\ t <> |0| /\ deg t < deg h /\ (peval z t == |0|) (pm h)` by metis_tac[poly_roots_of_unity_element] >>
  `poly z` by rw[] >>
  `Ring r` by rw[] >>
  `peval z t % h = |0|` by rw[GSYM pmod_zero] >>
  `poly_root (PolyModRing r h) (lift z) t` by rw[poly_mod_lift_root_by_mod_peval] >>
  `0 < n` by decide_tac >>
  metis_tac[poly_roots_of_unity_carrier]);

(*
Picture of roots_of_unity in various Finite Fields

In Z_2, 0 is never an n-th root, 1 = -1 is always an n-th root.
X^1 - 1 = (X - 1)(cyclic 1) = (X - 1)|1|                             1 1st-root. order_2(1) = 1 (split)
X^2 - 1 = (X - 1)(cyclic 2) = (X - 1)(X + 1) = (X - 1)^2             1 double 2nd-root. order_2(2) = none
X^3 - 1 = (X - 1)(cyclic 3) = (X - 1)(X^2 + X + 1)                   1 3rd-root. order_3(2) = 2, order_2(3) = order_2(1) = 1
X^4 - 1 = (X - 1)(cyclic 4) = (X - 1)(X + 1)^3 = (X - 1)^4           1 order-4 4th-root. order_2(4) = none
X^5 - 1 = (X - 1)(cyclic 5) = (X - 1)(X^4 + X^3 + X^2 + X + 1)       1 5th-root. order_5(2) = 4, order_2(5) = 1
X^6 - 1 = (X - 1)(cyclic 6) = (X - 1)(X + 1)(X^2 + X + 1)^2 = (X - 1)^2(X^2 + X + 1)^2
                                                                     1 double 6th-root. order_6(2) = none
X^7 - 1 = (X - 1)(cyclic 7) = (X - 1)(X^6 + X^5 + X^4 + X^3 + X^2 + X + 1)
                                                                     1 7th-root. order_7(2) = 3, order_2(7) = 1
X^8 - 1 = (X - 1)(cyclic 8) = (X - 1)(X + 1)^7 = (X - 1)^8           1 order-8 8th-root. order_8(2) = none
X^9 - 1 = (X - 1)(cyclic 9) = (X - 1)(X^6 + X^3 + 1)(X^2 + X + 1)    1 9th-root. order_9(2) = 6, order_2(9) = 1

Field r = Z_2, 0 < n ==> CARD (roots_of_unity r.prod n).carrier = 1.
Z_2 = {0, 1} = {0, exp(i * 2 * pi)} = origin + unity

In Z_3, 0 is never an n-th root, 1 is always an n-th root, 2 = -1 is an n-th root when n is even.
X^1 - 1 = (X - 1)(cyclic 1) = (X - 1)|1|                             1 1st-root. order_3(1) = 1
X^2 - 1 = (X - 1)(cyclic 2) = (X - 1)(X + 1) = (X - 1)(X - 2)        2 2nd-roots. order_2(3) = 1. order_3(2) = 2 (split)
X^3 - 1 = (X - 1)(cyclic 3) = (X - 1)(X + 2)^2 = (X - 1)^3           1 order-3 3rd-root. order_3(3) = none
X^4 - 1 = (X - 1)(cyclic 4) = (X - 1)(X + 1)(X^2 + 1)                2 4th-roots. order_4(3) = 2. order_3(4) = 1
X^5 - 1 = (X - 1)(cyclic 5) = (X - 1)(X^4 + X^3 + X^2 + X + 1)       1 5th-root. order_5(3) = 4. order_3(5) = 2
X^6 - 1 = (X - 1)(cyclic 6) = (X - 1)(X + 2)^2 (X + 1)^3 = (X - 1)^3(X + 1)^3  2 order-3 6th-roots. order_6(3) = none
X^7 - 1 = (X - 1)(cyclic 7) = (X - 1)(X^6 + X^5 + X^4 + X^3 + X^2 + X + 1)     1 7th-root. order_7(3) = 6. order_3(7) = 1
X^8 - 1 = (X - 1)(cyclic 8) = (X - 1)(X + 1)(X^2 + 2X + 2)(X^2 + X + 2)(X^2 + 1) 2 8th-roots. order_8(3) = 2. order_3(8) = 2
X^9 - 1 = (X - 1)(cyclic 9) = (X - 1)(X + 2)^8 = (X - 1)^9           1 order-9 9th-root. order_9(3) = none

Field r = Z_3, 0 < n ==> CARD (roots_of_unity r.prod n).carrier = if (n MOD 2 = 0) then 2 else 1.
Z_3 = {0, 1, -1} = {0, exp(i * 2pi/2), exp(i * 2 * 2pi/2)} = {0, -1, (-1)^2 = 1} = origin + dipole

In F_4, 0 is never an n-th root, 1 = -1 is always an n-th root, a and b are cubic-roots: a^3 = a*a^2 = a*b = 1.
X^1 - 1 = (X - 1)(cyclic 1) = (X - 1)|1|                             1 1st-root. order_4(1) = 1
X^2 - 1 = (X - 1)(cyclic 2) = (X - 1)(X + 1) = (X - 1)^2             1 double 2nd-roots. order_4(2) = none.
X^3 - 1 = (X - 1)(cyclic 3) = (X - 1)(X - a)(X - b)                  3 3rd-roots. order_4(3) = 2. order_3(4) = 1 (split)
X^4 - 1 = (X - 1)(cyclic 4) = (X - 1)(X + 1)^3 = (X - 1)^4           1 order-4 4th=root. order_4(4) = none
X^5 - 1 = (X - 1)(cyclic 5) = (X - 1)(X^2 + aX + 1)(X^2 + bX + 1)    1 5th-root. order_5(4) = 2. order_4(5) = 1.
X^6 - 1 = (X - 1)(cyclic 6) = (X - 1)(X - 1)(X - a)^2(X - b)^2       3 double 6th-roots. order_6(4) = none.
X^7 - 1 = (X - 1)(cyclic 7) = (X - 1)(X^3 + X^2 + 1)(X^3 + X + 1)    1 7th-root. order_7(4) = 3. order_3(7) = 1.
X^8 - 1 = (X - 1)(cyclic 8) = (X - 1)???                             1 8th-root. order_8(4) = none.
X^9 - 1 = (X - 1)(cyclic 9) = (X - 1)(X - 1)^2(X - a)^3(X - b)^3     3 9th-roots. order_9(4) = 3. order_4(9) = 1.

Field r = F_4, 0 < n ==> CARD (roots_of_unity r.prod n).carrier = if (n MOD 3 = 0) then 3 else 1.
F_4 = {0, 1, w, w^2} = {0, exp(i * 2pi/3), exp(i * 2 * 2pi/3), exp(i * 3 * 2pi/3)} = {0, w, w^2, w^3=1}
    = origin + triangle

In Z_5 = {0, 1, 2, 3, 4}
X^1 - 1 = (X - 1)(cyclic 1) = (X - 1)|1|                                      1 1st-root. order_5(1) = 1
X^2 - 1 = (X - 1)(cyclic 2) = (X - 1)(X + 1) = (X - 1)(X - 4)                 2 2nd-roots. order_5(2) = 4. order_2(5) = 1.
X^3 - 1 = (X - 1)(cyclic 3) = (X - 1)(X^2 + X + 1)                            1 3rd-root. order_5(3) = 4. order_3(5) = 2.
X^4 - 1 = (X - 1)(cyclic 4) = (X - 1)(X - 2)(X - 3)(X - 4)                    4 4th-roots. order_5(4) = 2. order_4(5) = 1. (split)
X^5 - 1 = (X - 1)(cyclic 5) = (X - 1)(X + 4)^4 = (X - 1)^5                    1 order-5 5th-root. rorder_5(5) = none
X^6 - 1 = (X - 1)(cyclic 6) = (X - 1)(X^2 + 4X + 1)(X^2 + X + 1)(X + 1)       2 6-th roots.  order_6(5) = 2. order_5(6) = 1.
X^7 - 1 = (X - 1)(cyclic 7) = (X - 1)(X^6 + X^5 + X^4 + X^3 + X^2 + X + 1)    1 7th-root. order_7(5) = 6.order_6(5) = 2.
X^8 - 1 = (X - 1)(cyclic 8) = (X - 1)(X^2 + 3)(X^2 + 2)(X + 3)(X + 2)(X + 1)  3 8th-roots, order_8(5) = 2. order_5(8) = 4
X^9 - 1 = (X - 1)(cyclic 9) = (X - 1)(X^6 + X^3 + 1)(X^2 + X + 1)             1 9th-root. order_9(5) = 6. order_5(9) = 2.

Field r = Z_5, 0 < n ==> CARD (roots_of_unity r.prod n).carrier = if (n MOD 4 = 0) then 4 else 1 -- not so simple.
Z_5 = {0, 1, -1, i, -i} = {0, exp(i * 2pi/4), exp(i * 2 * 2pi/4), exp(i * 3 * 2pi/4), exp(i * 4 * 2pi/4)}
    = {0, i, i^2=-1, i^3=-i, i^4=1} = origin + square

In Z_7 = {0, 1, 2, 3, 4, 5, 6}
X^1 - 1 = (X - 1)(cyclic 1) = (X - 1)|1|                                        1 1st-root. order_7(1) = 1
X^2 - 1 = (X - 1)(cyclic 2) = (X - 1)(X + 1) = (X - 1)(X - 5)                   2 2nd-roots. order_7(2) = 3. order_2(7) = 1.
X^3 - 1 = (X - 1)(cyclic 3) = (X - 1)(X + 5)(X + 3) = (X - 1)(X - 2)(X - 4)     3 3rd-roots. order_7(3) = 6. order_3(7) = 1
X^4 - 1 = (X - 1)(cyclic 4) = (X - 1)(X^2 + 1)(X + 1) = (X - 1)(X - 6)(X^2 + 1) 2 4th-roots. order_7(4) = 3. order_4(7) = 2
X^5 - 1 = (X - 1)(cyclic 5) = (X - 1)(X^4 + X^3 + X^2 + X + 1)                  1 5th-root. order_7(5) = 6. order_5(7) = 4
X^6 - 1 = (X - 1)(cyclic 6) = (X - 1)(X - 2)(X - 3)(X - 4)(X - 5)(X - 6)        6 6th-roots. order_7(6) = 2. order_6(7) = 1 (split)
X^7 - 1 = (X - 1)(cyclic 7) = (X - 1)(X + 6)^6 = (X - 1)^7                      1 order-6 7th-root. order_7(7) = none.
X^8 - 1 = (X - 1)(cyclic 8) = (X - 1)(X^2 + 4X + 1)(X^2 + 3X + 1)(X^2 + 1)(X + 1) 2 8th-roots. order_7(8) = 1. order_8(7) = 2
X^9 - 1 = (X - 1)(cyclic 9) = (X - 1)(X^3 + 5)(X^3 + 3)(X + 5)(X + 3)             3 9th-roots. order_7(9) = 3. order_9(7) = 3

Z_7 = {0, exp(i * 2pi/6), exp(i * 2 * 2pi/6), exp(i * 3 * 2pi/6), exp(i * 4 * 2pi/6), exp(i * 5 * 2pi/6), exp(i * 6 * 2pi/6)}
    = origin + hexagon

F_9 = {0, exp(i * k * 2pi/8) where k = 1, 2, 3, 4, 5, 6, 7, 8} = origin + octagon
    = {0, e, e^2 = i, e^3, e^4 = -1, e^5, e^6 = -i, e^7, e^8 = 1}
    = {0, e, i, ie, -1, -e, -1, -ie, 1}
X^1 - 1 = (X - 1)(cyclic 1) = (X - 1)|1|                                        1 1st-root. order_9(1) = 1
X^2 - 1 = (X - 1)(cyclic 2) = (X - 1)(X + 1)                                    2 2nd-roots. order_9(2) = 6. order_2(9) = 1.
X^3 - 1 = (X - 1)(cyclic 3) = (X - 1)(X^2 + X + 1)
X^4 - 1 = (X - 1)(cyclic 4) = (X - 1)(X + 1)(X^2 + 1)
X^5 - 1 = (X - 1)(cyclic 5) = (X - 1)
X^6 - 1 = (X - 1)(cyclic 6) = (X - 1)
X^7 - 1 = (X - 1)(cyclic 7) = (X - 1)
X^8 - 1 = (X - 1)(cyclic 8) = (X - 1) (split)
X^9 - 1 = (X - 1)(cyclic 9) = (X - 1)^9

*)



(*
Another view on Roots of Unity.

Take Field r = Z_2 = {0, 1}
Q. What are the square roots in r ?
A. Square roots are solutions of (x^2 - 1 = 0) in r.
   Since x^2 - 1 = (x - 1)^2  in r = Z_2,
   There are two square roots in r: 1 doubled, (or 1 and -1 = 1).
Q. What are the cube roots in r ?
A. Cube roots are solutions of (x^3 - 1 = 0) in r.
   Since x^3 - 1 = (x - 1)(x^2 + x + 1), and (x^2 + x + 1) is irreducible,
   Only 1 cube root in r: 1.
Q. That means r is too small. Can we make r bigger to have 3 cube roots ?
A. (Galois)
   Easy. Invent an imaginary w with the property w^3 = 1 (implicitly w <> 1, w^2 <> 1, only w^3 = 1).
   That is, adjoin r with w, a primitive cube root of unity.
   To form a field, add to r all the possible sums and products with w. The result:
   [0,0] --> 0
   [1,0] --> 1
   [0,1] --> w
   [1,1] --> w+1
   This system Z_2[w] is isomorphic to F_4, and in F_4, x^3 - 1 = (x - 1)(x - w)(x - w^2),
   so F_4 has 3 cube roots: 1, w, w^2.
A. (Cauchy)
   Hold on. Since x^3 - 1 = (x - 1)(x^2 + x + 1), and (x^2 + x + 1) is irreducible,
   Let h = x^2 + x + 1, and consider the system Z_2[x]/h. This quotient structure is:
   [0,0] --> 0
   [1,0] --> 1
   [0,1] --> x
   [1,1] --> x+1
   This system Z_2[x]/h is (again) isomorphic to F_4, with 3 cube roots: 1, x, x^2.

Q. How about 4th roots of unity?
A. Well, x^4 - 1 = (x^2 - 1)(x^2 + 1) = (x - 1)^2(x + 1)^2 = (x - 1)^4, so 4 roots: 1 with multiplicity 4.

Q. How about 5th roots of unity?
A. Well, x^5 - 1 = (x - 1) h, where h = (x^4 + x^3 + x^2 + x + 1) is irreducible. Only 1 5th-root.
   Adjoin a primitive 5th-root of unity, or form the quotient field by h, get the structure:
   [0,0,0,0] --> 0
   ...
   [1,1,1,1] --> x^3 + x^2 + x + 1
   This is isomorphic to F_(2^4) = F_16, with 15 nonzero elements.
   Indeed ((F_16).prod - 0) with 15 elements is cyclic, so it has a generator t, order t = 15.
   Therefore element w = t^3 has order 15/3 = 5, and the 5 5th-roots in F_16 are: t^3, t^6, t^9, t^12, t^15 = 1.

Q. How about k-th roots of unity?
A. Well, x^k - 1 = (x - 1)(cyclic k), and (cyclic k) must have an irreducible factor h.
   Adjoin a primitive k-th root of unity, or form the quotient field by h, get the structure:
   [0,0,0,..,0] --> 0
   ...
   [1,1,1,..,1] --> x^d + ... + 1  where d = deg h.
   This is isomorphic to F_(2^d), with 2^d - 1 nonzero elements.
   The multiplicative group of F_(2^d) is cyclic, with a generator t, order t = 2^d - 1.
   Now, k must divide 2^d - 1, so that w = t^(2^d - 1 DIV k) will have order w = k.
   Is this always true? a Theorem?
   Yes, since t^(order t) = 1. If k does not divide (order t), there is no way 1 is a cubic root.
*)

(*
Picture:  F* = {s, s^2, s^3, ...... , s^(order g s) = 1}, all distinct, order g s = CARD (F* )
I know:       ?             t = s^j, j divides (order g s), t ** n = 1.
Since j divides (order g s), let (order g s) = m * j.
Then      t, t^2, t^3, ..., t^m = 1 are distinct roots of z = X^n - |1|
Is there any t^u = 1 with u < m ?
If there is, 1 = t^u = (s^j)^u = s^(j * u)   j * u < j * m = (order g s), but (order g s) is minimal!

However, this only shows (ord t = m), which can be shown by other means.
What I want is: ord t = n.
Since  t^n = 1, and none of other t^u = 1, can I conclude n = m ?
Only catch: n can be a multiple of m.
How about, once s is known, let t = s^((order g s) DIV n)  assume n divides (order g s).
Then t, t^2, t^3, .., t^n = 1 are distinct roots of z = X^n - |1|,
so (ord t = n).
But how to assert: n divides (order g s) = CARD G ?
Well, the n distinct roots form a subgroup of g, hence n divides (CARD G)
-- but this is after we know n divides (CARD G) !
CARD G = (char r)^(deg h) - 1

Example, r = Z_2, looking for 6-th roots.
X^6 - 1 = (X^3 - 1)^2  hence roots: only 3 cubic roots, each with multiplicity 2.
If looking for n-th roots, not coprime n 2, i.e. gcd n 2 <> 1, then since prime 2, g n 2 = 2, or n = q * 2
X^n - 1 = X^(q * 2) - 1 = (X^q)^2 - 1 = (X^q - 1)^2, hence roots: all q roots, each doubled.
If looking for n-th roots, coprime n 2, i.e. coprime n (char r).
coprime (char r) (CARD G), does that implies coprime n (CARD G) ?
gcd (a b) = 1, gcd (b c) = 1, gcd (a c) = ?
gcd (4 3) = 1, gcd (3 8) = 1, gcd (4 8) = 2.
n divides (CARD G) must be given as a condition.
or just require (order t = CARD (roots z)).
*)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
