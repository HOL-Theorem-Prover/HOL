(* ------------------------------------------------------------------------- *)
(* Finite Field: Master Polynomial                                           *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ffMaster";

(* ------------------------------------------------------------------------- *)



(* val _ = load "jcLib"; *)
open jcLib;

(* val _ = load "SatisfySimps"; (* for SatisfySimps.SATISFY_ss *) *)

(* Loading theories *)
(* (* val _ = load "ffCycloTheory"; *) *)
(* val _ = load "ffPolyTheory"; *)
open ffBasicTheory;
open ffAdvancedTheory;
open ffPolyTheory;

(* Open theories in order *)

(* open dependent theories *)
open arithmeticTheory pred_setTheory listTheory;
(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open dividesTheory gcdTheory;

(* Get dependent theories in lib *)
(* (* val _ = load "helperNumTheory"; -- in monoidTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in monoidTheory *) *)
(* (* val _ = load "helperFunctionTheory"; -- in ringTheory *) *)
(* (* val _ = load "helperListTheory"; -- in polyRingTheory *) *)
open helperNumTheory helperSetTheory helperListTheory helperFunctionTheory;

(* Get dependent theories local *)
(* (* val _ = load "groupInstancesTheory"; -- in ringInstancesTheory *) *)
(* (* val _ = load "ringInstancesTheory"; *) *)
(* (* val _ = load "fieldInstancesTheory"; *) *)
open monoidTheory groupTheory ringTheory fieldTheory;
open monoidOrderTheory groupOrderTheory;
open subgroupTheory;

open groupInstancesTheory ringInstancesTheory fieldInstancesTheory;
open groupCyclicTheory;

open ringBinomialTheory;
open ringDividesTheory;
open ringIdealTheory;
open ringUnitTheory;

(* Get polynomial theory of Ring *)
open polynomialTheory polyWeakTheory polyRingTheory polyDivisionTheory polyBinomialTheory;

open polyFieldTheory;
open polyFieldDivisionTheory;
open polyFieldModuloTheory;
open polyModuloRingTheory;

open polyMonicTheory;
open polyProductTheory;
open polyDividesTheory;
open polyGCDTheory;
open polyIrreducibleTheory;

(* (* val _ = load "polyMapTheory"; *) *)
open monoidMapTheory groupMapTheory ringMapTheory fieldMapTheory;
open polyMapTheory;

open polyDerivativeTheory;
open polyEvalTheory;
open polyRootTheory;
open binomialTheory;

open GaussTheory;
open EulerTheory;

(* val _ = load "fieldBinomialTheory"; *)
open fieldBinomialTheory; (* for finite_field_freshman_all *)

(* (* val _ = load "MobiusTheory"; *) *)


(* ------------------------------------------------------------------------- *)
(* Finite Field Master Polynomial Documentation                              *)
(* ------------------------------------------------------------------------- *)
(* Overload:
   poly_psi r n    = PPROD (monic_irreducibles_degree r n)
   Psi n           = poly_psi r n
*)
(* Definitions and Theorems (# are exported):

   Master Polynomial and its roots:
   poly_master_root_all       |- !r. FiniteField r ==> !x. x IN R ==> root (master (CARD R)) x
   poly_master_roots_all      |- !r. FiniteField r ==> (roots (master (CARD R)) = R)
   poly_master_subfield_root  |- !r s. s <<= r ==> !x. x IN B ==>
                                 !n. poly_root s (Master s n) x <=> root (master n) x
   poly_master_coprime_diff   |- !r. FiniteField r ==> !n. 0 < n ==>
                                     pgcd (master (CARD R ** n)) (diff (master (CARD R ** n))) ~~ |1|
   poly_master_prod_set_over_natural_monic   |- !r. FiniteField r ==>
                                                !n. monic (PPIMAGE (\k. master (CARD R ** k)) (natural n))
   poly_master_prod_set_over_natural_poly    |- !r. FiniteField r ==>
                                                !n. poly (PPIMAGE (\k. master (CARD R ** k)) (natural n))
   poly_master_prod_set_over_natural_nonzero |- !r. FiniteField r ==>
                                                !n. PPIMAGE (\k. master (CARD R ** k)) (natural n) <> |0|
   poly_master_prod_set_over_natural_deg     |- !r. FiniteField r ==> (let m = CARD R in
                                                !n. deg (PPIMAGE (\k. master (m ** k)) (natural n)) =
                                                    m * (m ** n - 1) DIV (m - 1))

   Irreducible Factors of Master Polynomial:
   poly_ulead_divides_master_condition
                                    |- !r. Ring r ==> !p. ulead p ==>
                                       !n. p pdivides master n <=> (X ** n == X) (pm p)
   poly_irreducible_divides_master  |- !r. FiniteField r ==> !p. monic p /\ ipoly p ==>
                                           p pdivides master (CARD R ** deg p)
   poly_mod_master_root_condition   |- !r. Field r ==> !p. monic p /\ ipoly p ==>
                                       !x. x IN (PolyModRing r p).carrier ==>
         !n. poly_root (PolyModRing r p) (Master (PolyModRing r p) n) x <=> (x ** n == x) (pm p)
   poly_mod_poly_sum_gen       |- !r. Ring r ==>!p. pmonic p ==> !f. poly_fun f ==>
                                  !n. poly_sum (GENLIST f n) % p = poly_sum (GENLIST (\k. f k % p) n) % p
   poly_irreducible_master_factor_all_roots
                               |- !r. FiniteField r ==> !p. monic p /\ ipoly p ==>
                                  !n. p pdivides master (CARD R ** n) ==>
                                      (PolyModRing r p).carrier SUBSET
                                       poly_roots (PolyModRing r p) (Master (PolyModRing r p) (CARD R ** n))
   poly_irreducible_master_factor_deg
                               |- !r. FiniteField r ==> !p. monic p /\ ipoly p ==>
                                  !n. 0 < n /\ p pdivides master (CARD R ** n) ==> deg p <= n
   poly_irreducible_master_divisibility
                               |- !r. FiniteField r ==> !p. monic p /\ ipoly p ==>
                                  !n. p pdivides master (CARD R ** n) <=> deg p divides n
   poly_irreducible_master_subfield_divisibility
                               |- !r s. FiniteField r /\ s <<= r ==> !p. monic p /\ IPoly s p ==>
                                        (p pdivides master (CARD R) <=> deg p divides (r <:> s))

   Master as Product of Factors:
   poly_master_eq_root_factor_product
                               |- !r. FiniteField r ==> (master (CARD R) = PPROD (IMAGE factor R))
   poly_master_eq_root_factor_product_alt
                               |- !r. FiniteField r ==> (master (CARD R) = PPROD {X - c * |1| | c | c IN R})

   Subfield Conditions:
   subfield_element_condition  |- !r. FiniteField r ==> !s. s <<= r ==>
                                  !x. x IN R ==> (x IN B <=> (x ** CARD B = x))
   subfield_poly_condition     |- !r. FiniteField r ==> !s. s <<= r ==>
                                  !p. poly p ==> (Poly s p <=> (p ** CARD B = peval p (X ** CARD B)))

   Sets of Monic Irreducible Polynomials:
   monic_irreducibles_degree_def     |- !r n. monic_irreducibles_degree r n =
                                              {p | monic p /\ ipoly p /\ (deg p = n)}
   monic_irreducibles_bounded_def    |- !r n. monic_irreducibles_bounded r n =
                                              BIGUNION (IMAGE (monic_irreducibles_degree r) (divisors n))
   monic_irreducibles_degree_member  |- !r n p. p IN monic_irreducibles_degree r n <=>
                                                monic p /\ ipoly p /\ (deg p = n)
   monic_irreducibles_bounded_member |- !r n p. Field r ==>
                                                (p IN monic_irreducibles_bounded r n <=>
                                                 monic p /\ ipoly p /\ deg p <= n /\ deg p divides n)
   monic_irreducibles_degree_finite  |- !r. FINITE R /\ #0 IN R ==>
                                        !n. FINITE (monic_irreducibles_degree r n)
   monic_irreducibles_bounded_finite |- !r. FINITE R /\ #0 IN R ==>
                                        !n. FINITE (monic_irreducibles_bounded r n)
   monic_irreducibles_degree_0       |- !r. Field r ==> (monic_irreducibles_degree r 0 = {}
   monic_irreducibles_degree_1       |- !r. Field r ==> (monic_irreducibles_degree r 1 = IMAGE factor R)
   monic_irreducibles_bounded_0      |- !r. Field r ==> (monic_irreducibles_bounded r 0 = {})
   monic_irreducibles_bounded_1      |- !r. Field r ==> (monic_irreducibles_bounded r 1 = IMAGE factor R)
   monic_irreducibles_degree_monic_irreducible_set
                                          |- !r n. miset (monic_irreducibles_degree r n)
   monic_irreducibles_degree_monic_set    |- !r n. mset (monic_irreducibles_degree r n)
   monic_irreducibles_degree_poly_set     |- !r n. pset (monic_irreducibles_degree r n)
   monic_irreducibles_degree_coprime_set  |- !r. Field r ==> !n. pcoprime_set (monic_irreducibles_degree r n)
   monic_irreducibles_bounded_coprime_set |- !r. Field r ==> !n. pcoprime_set (monic_irreducibles_bounded r n)

   Product of Monic Irreducibles of the same degree:
   monic_irreducibles_degree_prod_set_monic   |- !r. FiniteRing r ==> !n. monic (Psi n)
   monic_irreducibles_degree_prod_set_poly    |- !r. FiniteRing r ==> !n. poly (Psi n)
   monic_irreducibles_degree_prod_set_nonzero |- !r. FiniteRing r /\ #1 <> #0 ==> !n. Psi n <> |0|

   Master Polynomial as Product of Monic Irreducibles:
   poly_master_subfield_factors           |- !r. FiniteField r ==> !s. s <<= r ==> !n. 0 < n ==>
                                   (Master s (CARD B ** n) = poly_prod_set s (monic_irreducibles_bounded s n))
   poly_master_subfield_factors_alt       |- !r s n. FiniteField r /\ s <<= r /\ 0 < n ==>
                                     (master (CARD B ** n) = poly_prod_set s (monic_irreducibles_bounded s n))
   poly_master_monic_irreducible_factors  |- !r. FiniteField r ==> !n. 0 < n ==>
                                               (master (CARD R ** n) = PPROD (monic_irreducibles_bounded r n))
   poly_master_eq_irreducibles_product    |- !r. FiniteField r ==> !s. s <<= r ==>
                                  (master (CARD R) = poly_prod_set s (monic_irreducibles_bounded s (r <:> s)))

   Counting Monic Irreducible Polynomials:
   monic_irreducibles_count_def   |- !r n. monic_irreducibles_count r n = CARD (monic_irreducibles_degree r n)
   monic_irreducibles_degree_prod_set_deg
                                  |- !r. FiniteRing r ==> !n. deg (Psi n) = n * monic_irreducibles_count r n
   monic_irreducibles_degree_prod_set_deg_fun  |- !r. FiniteRing r ==>
                       (deg o PPROD o monic_irreducibles_degree r = (\d. d * monic_irreducibles_count r d))
   monic_irreducibles_degree_disjoint
         |- !r n m. n <> m ==> DISJOINT (monic_irreducibles_degree r n) (monic_irreducibles_degree r m)
   monic_irreducibles_degree_pair_disjoint
         |- !r n. PAIR_DISJOINT (IMAGE (monic_irreducibles_degree r) (divisors n))
   monic_irreducibles_degree_prod_set_divisor  |- !r. FiniteField r ==> !p. monic p /\ ipoly p ==>
                                                  !n. p pdivides Psi n <=> p IN monic_irreducibles_degree r n
   monic_irreducibles_degree_poly_prod_inj  |- !r. FiniteField r ==>
                           !n. INJ PPROD (IMAGE (monic_irreducibles_degree r) (divisors n)) univ(:'a poly)
   monic_irreducibles_degree_nonempty_inj  |- !r s. FINITE s /\
                                              (!d. d IN s ==> monic_irreducibles_degree r d <> {}) ==>
                                              INJ (monic_irreducibles_degree r) s univ(:'a poly -> bool)
   monic_irreducibles_bounded_prod_set     |- !r. FiniteField r ==> !n. PPROD (monic_irreducibles_bounded r n) =
                                                  PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) (divisors n))
   monic_irreducibles_bounded_prod_set_deg |- !r. FiniteField r ==>
                                              !n. deg (PPROD (monic_irreducibles_bounded r n)) =
                                                  SIGMA (\d. d * monic_irreducibles_count r d) (divisors n)

   Finite Field and Subfield Order:
   finite_subfield_card_exp_eqn  |- !r. FiniteField r ==> !s. s <<= r ==> !n. 0 < n ==>
                                 (CARD B ** n = SIGMA (\d. d * monic_irreducibles_count s d) (divisors n))
   finite_field_card_exp_eqn     |- !r. FiniteField r ==> !n. 0 < n ==>
                                 (CARD R ** n = SIGMA (\d. d * monic_irreducibles_count r d) (divisors n))

   Roots of Master is a Subfield:
   poly_master_roots_char_n_zero  |- !r. FiniteField r ==> !n. #0 IN roots (master (char r ** n))
   poly_master_roots_add_root     |- !r. FiniteField r ==> !n. (let p = master (char r ** n) in
                                     !x y. x IN roots p /\ y IN roots p ==> x + y IN roots p)
   poly_master_roots_sub_root     |- !r. FiniteField r ==> !n. (let p = master (char r ** n) in
                                     !x y. x IN roots p /\ y IN roots p ==> x - y IN roots p)
   poly_master_roots_neg_root     |- !r. FiniteField r ==> !n. (let p = master (char r ** n) in
                                     !x. x IN roots p ==> -x IN roots p)
   poly_master_roots_mult_root    |- !r. Field r ==> !n. (let p = master (char r ** n) in
                                     !x y. x IN roots p /\ y IN roots p ==> x * y IN roots p)
   poly_master_roots_inv_root     |- !r. Field r ==> !n. (let p = master (char r ** n) in
                                     !x. x IN roots p /\ x <> #0 ==> |/ x IN roots p)
   poly_master_roots_div_root     |- !r. Field r ==> !n. (let p = master (char r ** n) in
                                     !x y. x IN roots p /\ y IN roots p /\ y <> #0 ==> x * |/ y IN roots p)
   poly_master_roots_sum_abelian_group
                                  |- !r. FiniteField r ==>
                                     !n. AbelianGroup (subset_field r (roots (master (char r ** n)))).sum
   poly_master_roots_prod_abelian_group
                                  |- !r. FiniteField r ==> !n. (let p = master (char r ** n) in
                AbelianGroup ((subset_field r (roots p)).prod excluding (subset_field r (roots p)).sum.id))
   poly_master_roots_field        |- !r. FiniteField r ==>
                                     !n. Field (subset_field r (roots (master (char r ** n))))
   poly_master_roots_finite_field |- !r. FiniteField r ==>
                                     !n. FiniteField (subset_field r (roots (master (char r ** n))))
   poly_master_roots_subfield     |- !r. FiniteField r ==>
                                     !n. subset_field r (roots (master (char r ** n))) <<= r
   poly_master_roots_subfield_iso_field
                                  |- !r. FiniteField r ==>
                                         FieldIso I (subset_field r (roots (master (char r ** fdim r)))) r
   poly_master_roots_subfield_isomorphism
                                  |- !r. FiniteField r ==>
                                         r =ff= subset_field r (roots (master (char r ** fdim r)))

   Useful Results:
   poly_master_subfield_eq_monic_irreducibles_prod_image
                          |- !r s n. FiniteField r /\ s <<= r /\ 0 < n ==> (master (CARD B ** n) =
               poly_prod_image s (poly_prod_set s) (IMAGE (monic_irreducibles_degree s) (divisors n)))
   poly_master_subfield_eq_monic_irreducibles_prod_image_alt_1
                          |- !r s n. FiniteField r /\ s <<= r /\ 0 < n ==>
                             (master (CARD B ** n) =  poly_prod_set s {poly_psi s d | d IN divisors n})
   poly_master_subfield_eq_monic_irreducibles_prod_image_alt_2
                          |- !r s n. FiniteField r /\ s <<= r /\ 0 < n ==>
                             (master (CARD B ** n) = poly_prod_set s {poly_psi s d | d divides n})
   poly_master_eq_monic_irreducibles_prod_image
                          |- !r. FiniteField r ==> !n. 0 < n ==>
             (master (CARD R ** n) = PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) (divisors n)))
   poly_master_eq_monic_irreducibles_prod_image_alt_1
                          |- !r n. FiniteField r /\ 0 < n ==>
                                   (master (CARD R ** n) = PPROD {Psi d | d IN divisors n})
   poly_master_eq_monic_irreducibles_prod_image_alt_2
                          |- !r n. FiniteField r /\ 0 < n ==>
                                   (master (CARD R ** n) = PPROD {Psi d | d divides n})

   Monic Irreducible Products:
   monic_irreducibles_degree_prod_set_image_monic_set
                         |- !r. FiniteRing r ==>
                            !n. mset (IMAGE PPROD (IMAGE (monic_irreducibles_degree r) (natural n)))
   monic_irreducibles_degree_prod_set_image_monic
                         |- !r.  FiniteRing r ==>
                            !n. monic (PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) (natural n)))
   monic_irreducibles_degree_prod_set_image_poly
                         |- !r. FiniteRing r ==>
                            !n. poly (PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) (natural n)))
   monic_irreducibles_degree_prod_set_image_nonzero
                         |- !r. FiniteRing r /\ #1 <> #0 ==>
                            !n. PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) (natural n)) <> |0|

   Existence of Monic Irreducible by Master Polynomial:
   monic_irreducibles_degree_prod_set_divides_master
                         |- !r. FiniteField r ==> !n. Psi n pdivides master (CARD R ** n)
   poly_master_divides_monic_irreducibles_degree_prod_set_image
                         |- !r. FiniteField r ==> !n. 0 < n ==>
                                master (CARD R ** n) pdivides
                                PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) (natural n))
   monic_irreducibles_degree_prod_set_image_divides_master_image
                         |- !r. FiniteField r ==> !s. FINITE s ==>
                                PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) s) pdivides
                                PPIMAGE (\n. master (CARD R ** n)) s
   poly_monic_irreducible_exists_alt
                         |- !r. FiniteField r ==> !n. 0 < n ==> ?p. monic p /\ ipoly p /\ (deg p = n)

   Finite Field Subgroup and Master Polynomial:
   field_subgroup_master_roots   |- !r g. FiniteField r /\ g <= f* ==> (roots (master (CARD G + 1)) = G UNION {#0})

   Finite Field Subgroup Field:
   subgroup_field_def            |- !r g. subgroup_field r g =
                                          <|carrier := G UNION {#0};
                                                sum := <|carrier := G UNION {#0}; op := $+; id := #0|>;
                                               prod := g including #0
                                           |>
   subgroup_field_property       |- !r g. ((subgroup_field r g).carrier = G UNION {#0}) /\
                                          ((subgroup_field r g).sum.carrier = G UNION {#0}) /\
                                          ((subgroup_field r g).prod.carrier = G UNION {#0}) /\
                                          ((subgroup_field r g).sum.op = $+) /\
                                          ((subgroup_field r g).sum.id = #0)
   subgroup_field_sum_property   |- !r g. ((subgroup_field r g).sum.op = $+) /\
                                          ((subgroup_field r g).sum.id = #0)
   subgroup_field_prod_property  |- !r g. Field r /\ g <= f* ==>
                                          ((subgroup_field r g).prod.op = $* ) /\
                                          ((subgroup_field r g).prod.id = #1)
   subgroup_field_ids            |- !r g. Field r /\ g <= f* ==>
                                          ((subgroup_field r g).sum.id = #0) /\
                                          ((subgroup_field r g).prod.id = #1)
   subgroup_field_card           |- !r g. FiniteGroup g /\ #0 NOTIN G ==>
                                          (CARD (subgroup_field r g).carrier = CARD G + 1)
   subgroup_field_has_ids        |- !r g. Field r /\ g <= f* ==> #0 IN G UNION {#0} /\ #1 IN G UNION {#0}
   subgroup_field_element        |- !r g. Field r /\ g <= f* ==> !x. x IN G UNION {#0} ==> x IN R
   subgroup_field_mult_element   |- !r g. Field r /\ g <= f* ==>
                                    !x y. x IN G UNION {#0} /\ y IN G UNION {#0} ==> x * y IN G UNION {#0}
   subgroup_field_exp_element    |- !r g. Field r /\ g <= f* ==>
                                    !x. x IN G UNION {#0} ==> !n. x ** n IN G UNION {#0}
   subgroup_field_inv_element    |- !r g. Field r /\ g <= f* ==> !x. x IN G ==> |/ x IN G

   Subgroup Field Additive Closure:
   subgroup_field_element_iff_master_root  |- !r g. FiniteField r /\ g <= f* ==>
                                              !x. x IN G UNION {#0} <=> x IN R /\ (x ** (CARD G + 1) = x)
   subgroup_field_add_element    |- !r g. FiniteField r /\ g <= f* ==> !n. (CARD G = char r ** n - 1) ==>
                                    !x y. x IN G UNION {#0} /\ y IN G UNION {#0} ==> x + y IN G UNION {#0}
   subgroup_field_sub_element    |- !r g. FiniteField r /\ g <= f* ==> !n. (CARD G = char r ** n - 1) ==>
                                    !x y. x IN G UNION {#0} /\ y IN G UNION {#0} ==> x - y IN G UNION {#0}
   subgroup_field_neg_element    |- !r g. FiniteField r /\ g <= f* ==> !n. (CARD G = char r ** n - 1) ==>
                                    !x. x IN G UNION {#0} ==> -x IN G UNION {#0}

   Subgroup Field Properties:
   subgroup_field_prod_abelian_monoid  |- !r g. Field r /\ g <= f* ==> AbelianMonoid (subgroup_field r g).prod
   subgroup_field_prod_monoid          |- !r g. Field r /\ g <= f* ==> Monoid (subgroup_field r g).prod
   subgroup_field_sum_abelian_group    |- !r g. FiniteField r /\ g <= f* ==> !n. (CARD G = char r ** n - 1) ==>
                                                AbelianGroup (subgroup_field r g).sum
   subgroup_field_sum_group            |- !r g. FiniteField r /\ g <= f* ==> !n. (CARD G = char r ** n - 1) ==>
                                                Group (subgroup_field r g).sum
   subgroup_field_ring       |- !r g. FiniteField r /\ g <= f* ==> !n. (CARD G = char r ** n - 1) ==>
                                      Ring (subgroup_field r g)
   subgroup_field_field      |- !r g. FiniteField r /\ g <= f* ==> !n. (CARD G = char r ** n - 1) ==>
                                      Field (subgroup_field r g)
   subgroup_field_subfield   |- !r g. Field r /\ g <= f* ==> subfield (subgroup_field r g) r

   Subfield Classification:
   finite_field_subfield_gives_subgroup
                |- !r s. FiniteField r /\ s <<= r ==> ?g. g <= f* /\ (CARD G = char r ** fdim s - 1)
   finite_field_subgroup_gives_subfield
                |- !r. FiniteField r ==> !g n. g <= f* /\ (CARD G = char r ** n - 1) ==>
                                         ?s. s <<= r /\ (fdim s = n)
   finite_field_subfield_exists_iff_subgroup_exists
                |- !r. FiniteField r ==> !n. (?s. s <<= r /\ (fdim s = n)) <=>
                                              ?g. g <= f* /\ (CARD G = char r ** n - 1)
   finite_field_subfield_exists_condition
                |- !r. FiniteField r ==> !n. (?s. s <<= r /\ (fdim s = n)) <=> n divides fdim r

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Master Polynomial: X ** (CARD R) - X  and its roots.                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==> !x. x IN R ==> root (master (CARD R)) x *)
(* Proof:
   FiniteField r ==> Field r             by FiniteField_def
       root (master (CARD R)) x
   <=> x ** (CARD R) = x                 by poly_master_root
   <=> T                                 by finite_field_fermat_thm
*)
val poly_master_root_all = store_thm(
  "poly_master_root_all",
  ``!r:'a field. FiniteField r ==> !x. x IN R ==> root (master (CARD R)) x``,
  rw[FiniteField_def, poly_master_root, finite_field_fermat_thm]);

(* Theorem: FiniteField r ==> (roots (master (CARD R)) = R) *)
(* Proof:
   By poly_roots_def, this is to show:
   {x | x IN R /\ root (X ** CARD R - X) x} = R
   which is true by poly_master_root_all.
*)
val poly_master_roots_all = store_thm(
  "poly_master_roots_all",
  ``!r:'a field. FiniteField r ==> (roots (master (CARD R)) = R)``,
  rw_tac std_ss[poly_roots_def, GSPECIFICATION, EXTENSION] >>
  metis_tac[poly_master_root_all]);

(* Theorem: s <<= r ==> !x. x IN B ==> !n. poly_root s (Master s n) x <=> root (master n) x *)
(* Proof:
   Note  x IN B == x IN R     by subfield_element
   Given poly_root s (Master s n) x
     <=> s.prod.exp x n = x   by poly_master_root
     <=> x ** n = x           by subfield_exp
     <=> root (master n) x    by poly_master_root
*)
val poly_master_subfield_root = store_thm(
  "poly_master_subfield_root",
  ``!(r s):'a field. s <<= r ==> !x. x IN B ==> !n. poly_root s (Master s n) x <=> root (master n) x``,
  metis_tac[subfield_element, poly_master_root, subfield_exp, field_is_ring]);

(* Theorem: FiniteField r ==>
            !n. 0 < n ==> pgcd (master (CARD R ** n)) (diff (master (CARD R ** n))) ~~ |1| *)
(* Proof:
   Let b = CARD R ** n, p = master b, c = char r.
   Then poly p                by poly_master_poly
    and prime c               by finite_field_char
    and 1 < c                 by ONE_LT_PRIME,
   also ?m. 0 < m /\ (CARD R = c ** m   by finite_field_card
   thus b = (c ** m) ** n
          = c ** (m * n)      by EXP_EXP_MULT
    Note m * n <> 0           by MULT_EQ_0, m <> 0
    Thus diff p = -|1|        by poly_diff_master_char_exp, m * n <> 0
     Now upoly |1|            by poly_unit_one
     and upoly (-|1|)         by poly_unit_neg
   Hence pgcd p (diff p)
       = pgcd p (-|1|) ~~ |1| by poly_gcd_unit
*)
val poly_master_coprime_diff = store_thm(
  "poly_master_coprime_diff",
  ``!r:'a field. FiniteField r ==>
   !n. 0 < n ==> pgcd (master (CARD R ** n)) (diff (master (CARD R ** n))) ~~ |1|``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `b = CARD R ** n` >>
  qabbrev_tac `p = master b` >>
  qabbrev_tac `c = char r` >>
  `1 < c` by rw[finite_field_char, ONE_LT_PRIME, Abbr`c`] >>
  `?m. 0 < m /\ (CARD R = c ** m)` by rw[finite_field_card, Abbr`c`] >>
  `b = c ** (m * n)` by rw[EXP_EXP_MULT, Abbr`b`] >>
  `m * n <> 0` by metis_tac[MULT_EQ_0, NOT_ZERO_LT_ZERO] >>
  `diff p = -|1|` by rw[poly_diff_master_char_exp, Abbr`p`, Abbr`c`] >>
  `upoly |1|` by rw[poly_unit_one] >>
  `upoly (-|1|)` by rw[poly_unit_neg] >>
  rw[poly_gcd_unit, Abbr`p`]);

(* Theorem: FiniteField r ==> !n. monic (PPIMAGE (\k. master (CARD R ** k)) (natural n)) *)
(* Proof:
   Let m = CARD R.
   Then 1 < m                   by finite_field_card_gt_1
   Let f = \k. master (m ** k), s = IMAGE f (natural n).
   Note FINITE (natural n)      by natural_finite
     so FINITE s                by IMAGE_FINITE
   Note !k. k IN (natural n)
        ==> 0 < k               by natural_element
        ==> 1 < m ** k          by ONE_LT_EXP, 1 < m
     so mset s                  by IN_IMAGE, poly_master_monic, 1 < m ** k for k IN (natural n)
   Thus monic (PPROD s)         by poly_monic_prod_set_monic
*)
val poly_master_prod_set_over_natural_monic = store_thm(
  "poly_master_prod_set_over_natural_monic",
  ``!r:'a field. FiniteField r ==> !n. monic (PPIMAGE (\k. master (CARD R ** k)) (natural n))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `m = CARD R` >>
  `1 < m` by rw[finite_field_card_gt_1, Abbr`m`] >>
  qabbrev_tac `f = \k. master (m ** k)` >>
  qabbrev_tac `s = IMAGE f (natural n)` >>
  `FINITE (natural n)` by rw[natural_finite] >>
  `FINITE s` by rw[Abbr`s`] >>
  `mset s` by metis_tac[IN_IMAGE, poly_master_monic, natural_element, ONE_LT_EXP] >>
  rw[poly_monic_prod_set_monic]);

(* Theorem: FiniteField r ==> !n. poly (PPIMAGE (\k. master (CARD R ** k)) (natural n)) *)
(* Proof: by poly_master_prod_set_over_natural_monic, poly_monic_poly *)
val poly_master_prod_set_over_natural_poly = store_thm(
  "poly_master_prod_set_over_natural_poly",
  ``!r:'a field. FiniteField r ==> !n. poly (PPIMAGE (\k. master (CARD R ** k)) (natural n))``,
  rw_tac std_ss[poly_master_prod_set_over_natural_monic, poly_monic_poly]);

(* Theorem: FiniteField r ==> !n. PPIMAGE (\k. master (CARD R ** k)) (natural n) <> |0| *)
(* Proof: by poly_master_prod_set_over_natural_monic, poly_monic_nonzero *)
val poly_master_prod_set_over_natural_nonzero = store_thm(
  "poly_master_prod_set_over_natural_nonzero",
  ``!r:'a field. FiniteField r ==> !n. PPIMAGE (\k. master (CARD R ** k)) (natural n) <> |0|``,
  rw_tac std_ss[poly_master_prod_set_over_natural_monic, poly_monic_nonzero, finite_field_is_field, field_one_ne_zero]);

(* Theorem: FiniteField r ==> let m = CARD R in
            !n. deg (PPIMAGE (\k. master (m ** k)) (natural n)) = m * (m ** n - 1) DIV (m - 1) *)
(* Proof:
   Let m = CARD R.
   Then 1 < m                   by finite_field_card_gt_1
   Let f = \k. master (m ** k), s = IMAGE f (natural n).
   Note FINITE (natural n)      by natural_finite
     so FINITE s                by IMAGE_FINITE
   also mset s                  by IN_IMAGE, poly_master_monic, natural_element, ONE_LT_EXP

   Claim: INJ f (natural n) UNIV
   Proof: by INJ_DEF, this is to show:
          (1) k IN natural n ==> master (m ** k) IN univ(:'a poly)
              True              by poly_master_poly, IN_UNIV
          (2) k IN natural n /\ k' IN natural n /\ master (m ** k) = master (m ** k') ==> k = k'
              Note m ** k = m ** k'   by poly_master_eq
               ==>      k = k'        by EXP_BASE_INJECTIVE, 1 < m

   Claim: !k. k IN (natural n) ==> ((deg o f) k = (\k. m ** k) k)
   Proof: By FUN_EQ_THM, this is to show:
             k IN natural n ==> deg (master (m ** k)) = m ** k
          Note 0 < k                by natural_element
            so 1 < m ** k           by ONE_LT_EXP, 1 < m
          Thus true                 by poly_master_deg, 1 < m ** k

        deg (PPROD s)
      = SIGMA deg s                       by poly_monic_prod_set_deg, mset s
      = SIGMA deg (IMAGE f (natural n))   by notation
      = SIGMA (deg o f) (natural n)       by sum_image_by_composition
      = SIGMA (\k. m ** k) (natural n)    by SIGMA_CONG
      = m * (m ** n - 1) DIV (m - 1)      by sigma_geometric_natural, 1 < m
*)
val poly_master_prod_set_over_natural_deg = store_thm(
  "poly_master_prod_set_over_natural_deg",
  ``!r:'a field. FiniteField r ==> let m = CARD R in
   !n. deg (PPIMAGE (\k. master (m ** k)) (natural n)) = m * (m ** n - 1) DIV (m - 1)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  rw_tac std_ss[] >>
  `1 < m` by rw[finite_field_card_gt_1, Abbr`m`] >>
  qabbrev_tac `f = \k. master (m ** k)` >>
  qabbrev_tac `s = IMAGE f (natural n)` >>
  `FINITE (natural n)` by rw[natural_finite] >>
  `FINITE s` by rw[Abbr`s`] >>
  `!k. f k = master (m ** k)` by rw[Abbr`f`] >>
  `mset s` by metis_tac[IN_IMAGE, poly_master_monic, natural_element, ONE_LT_EXP] >>
  `INJ f (natural n) UNIV` by
  (rw_tac std_ss[INJ_DEF, Abbr`f`] >-
  rw[poly_master_poly] >>
  `m ** k = m ** k'` by metis_tac[poly_master_eq] >>
  metis_tac[EXP_BASE_INJECTIVE]
  ) >>
  `!k. k IN (natural n) ==> ((deg o f) k = (\k. m ** k) k)` by
    (rw_tac std_ss[FUN_EQ_THM, Abbr`f`] >>
  metis_tac[poly_master_deg, natural_element, ONE_LT_EXP]) >>
  `deg (PPROD s) = SIGMA deg s` by rw[poly_monic_prod_set_deg] >>
  `_ = SIGMA deg (IMAGE f (natural n))` by rw[Abbr`s`] >>
  `_ = SIGMA (deg o f) (natural n)` by rw[sum_image_by_composition] >>
  `_ = SIGMA (\k. m ** k) (natural n)` by rw[SIGMA_CONG] >>
  `_ = m * (m ** n - 1) DIV (m - 1)` by rw[sigma_geometric_natural] >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* Irreducible Factors of Master Polynomial                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r ==> !p. ulead p ==> !n. p pdivides (master n) <=> (X ** n == X) (pm p) *)
(* Proof:
       p pdivides (master n)
   <=> master n % p = |0|        by poly_divides_alt
   <=> (X ** n - X) % p = |0|    by notation
   <=> (X ** n) % p = X % p      by poly_mod_eq
   <=> (X ** n == X) (pm p)      by pmod_def_alt
*)
val poly_ulead_divides_master_condition = store_thm(
  "poly_ulead_divides_master_condition",
  ``!r:'a ring. Ring r ==>
   !p. ulead p ==> !n. p pdivides (master n) <=> (X ** n == X) (pm p)``,
  rpt strip_tac >>
  `poly X /\ poly (master n)` by rw[] >>
  `p pdivides (master n) <=> (master n % p = |0|)` by rw_tac std_ss[poly_divides_alt] >>
  `_ = ((X ** n) % p = X % p)` by rw_tac std_ss[poly_mod_eq, poly_exp_poly] >>
  `_ = (X ** n == X) (pm p)` by rw_tac std_ss[pmod_def_alt] >>
  rw[]);

(* Theorem: FiniteField r ==> !p. monic p /\ ipoly p ==> p pdivides (master (CARD R ** deg p)) *)
(* Proof:
   Since FieldField r /\ monic p /\ ipoly p
     ==> FiniteField (PolyModRing r p)                  by poly_mod_irreducible_finite_field
     and (X % p) IN (PolyModRing r p).carrier           by poly_mod_ring_element
   Hence X % p
       = (PolyModRing r p).prod.exp (X % p) (CARD (PolyModRing r p).carrier)   by finite_field_fermat_thm
       = (X ** (CARD (PolyModRing r p).carrier)) % p    by poly_mod_field_exp
       = (X ** (CARD R ** deg p)) % p                   by poly_mod_irreducible_field_card
   Giving  (X ** (CARD R ** deg p) == X) (pm p)         by pmod_def_alt
       or  p pdivides (master (CARD R ** deg p))        by poly_ulead_divides_master_condition
*)
val poly_irreducible_divides_master = store_thm(
  "poly_irreducible_divides_master",
  ``!r:'a field. FiniteField r ==> !p. monic p /\ ipoly p ==> p pdivides (master (CARD R ** deg p))``,
  rpt (stripDup[FiniteField_def]) >>
  `pmonic p` by rw[poly_monic_irreducible_property] >>
  `poly X /\ poly (X % p) /\ deg (X % p) < deg p` by rw[poly_deg_mod_less] >>
  `FiniteField (PolyModRing r p)` by rw[poly_mod_irreducible_finite_field] >>
  `(X % p) IN (PolyModRing r p).carrier` by rw[poly_mod_ring_element] >>
  `X % p = (PolyModRing r p).prod.exp (X % p) (CARD (PolyModRing r p).carrier)` by rw[finite_field_fermat_thm] >>
  `_ = X ** (CARD (PolyModRing r p).carrier) % p` by rw[poly_mod_field_exp] >>
  `_ = X ** (CARD R ** deg p) % p` by metis_tac[poly_mod_irreducible_field_card] >>
  `(X ** (CARD R ** deg p) == X) (pm p)` by rw[pmod_def_alt] >>
  rw[poly_ulead_divides_master_condition]);

(* This is a small milestone theorem. The big one is: poly_irreducible_master_divisibility *)

(* Theorem: Field r ==> !p. monic p /\ ipoly p ==> !x. x IN (PolyModRing r p).carrier ==>
            !n. poly_root (PolyModRing r p) (Master (PolyModRing r p) n) x <=> (x ** n == x) (pm p) *)
(* Proof:
   Since monic p /\ ipoly p ==> pmonic p        by poly_monic_irreducible_property
    then Ring (PolyModRing r p)                 by poly_mod_ring_ring, pmonic p
    Also x IN (PolyModRing r p).carrier
     ==> poly x /\ deg x < deg p                by poly_mod_ring_element
    thus x % p = x                              by poly_mod_less
   Apply: poly_master_root |> ISPEC ``PolyModRing r z``;
       poly_root (PolyModRing r p) (Master (PolyModRing r p) n) x
   <=> (PolyModRing r p).prod.exp x n = x               by poly_master_root
   <=> (PolyModRing r p).prod.exp (x % p) n = (x % p)   by above
   <=>                           x ** n % p = x % p     by poly_mod_field_exp
   <=>                          (x ** n == x) (pm p)    by pmod_def_alt
*)
val poly_mod_master_root_condition = store_thm(
  "poly_mod_master_root_condition",
  ``!r:'a field. Field r ==> !p. monic p /\ ipoly p ==> !x. x IN (PolyModRing r p).carrier ==>
   !n. poly_root (PolyModRing r p) (Master (PolyModRing r p) n) x <=> (x ** n == x) (pm p)``,
  rpt strip_tac >>
  `pmonic p` by rw[poly_monic_irreducible_property] >>
  `Ring r /\ Ring (PolyModRing r p)` by rw[poly_mod_ring_ring] >>
  `poly x /\ deg x < deg p` by metis_tac[poly_mod_ring_element, NOT_ZERO] >>
  `x % p = x` by rw[poly_mod_less] >>
  `!n. (PolyModRing r p).prod.exp (x % p) n = (x ** n) % p` by rw[poly_mod_field_exp] >>
  metis_tac[poly_master_root, pmod_def_alt]);

(* Theorem: Ring r ==> !p. pmonic p ==>
           !f. poly_fun f ==> !n. (poly_sum (GENLIST f n)) % p = poly_sum (GENLIST (\k. (f k) % p) n) % p *)
(* Proof:
   By induction on n.
   Base case: poly_sum (GENLIST f 0) % p = poly_sum (GENLIST (\k. f k % p) 0) % p
        poly_sum (GENLIST f 0) % p
      = poly_sum [] % p                      by GENLIST_0
      = poly_sum (GENLIST (\k. f k % p) 0)   by GENLIST_0
   Step case: poly_sum (GENLIST f n) % p = poly_sum (GENLIST (\k. f k % p) n) % p ==>
              poly_sum (GENLIST f (SUC n)) % p = poly_sum (GENLIST (\k. f k % p) (SUC n)) % p
        poly_sum (GENLIST f (SUC n)) % p
      = (poly_sum (GENLIST f n) + f n) % p                         by poly_sum_decompose_last
      = (poly_sum (GENLIST f n) % p + (f n) % p) % p               by poly_mod_add, ulead p
      = (poly_sum (GENLIST (\k. f k % p) n) % p + (f n) % p) % p   by induction hypothesis
      = (poly_sum (GENLIST (\k. f k % p) n) + (f n) % p) % p       by poly_mod_mod, ulead p
      = poly_sum (GENLIST (\k. f k % p) (SUC n)) % p               by poly_sum_decompose_last
*)
val poly_mod_poly_sum_gen = store_thm(
  "poly_mod_poly_sum_gen",
  ``!r:'a ring. Ring r ==> !p. ulead p ==>
   !f. poly_fun f ==> !n. (poly_sum (GENLIST f n)) % p = poly_sum (GENLIST (\k. (f k) % p) n) % p``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw_tac std_ss[GENLIST_0] >>
  `poly (poly_sum (GENLIST f n)) /\ poly (f n)` by rw[] >>
  `poly_fun ((\k. f k % p))` by rw[poly_mod_poly, poly_ring_element] >>
  `poly (poly_sum (GENLIST (\k. f k % p) n)) /\ poly ((f n) % p)` by rw[poly_mod_poly] >>
  `poly_sum (GENLIST f (SUC n)) % p = (poly_sum (GENLIST f n) + f n) % p` by rw_tac std_ss[poly_sum_decompose_last] >>
  `_ = (poly_sum (GENLIST f n) % p + (f n) % p) % p` by rw_tac std_ss[poly_mod_add] >>
  `_ = (poly_sum (GENLIST (\k. f k % p) n) % p + (f n) % p) % p` by rw[] >>
  `_ = (poly_sum (GENLIST (\k. f k % p) n) % p + ((f n) % p) % p) % p` by rw_tac std_ss[poly_mod_mod] >>
  `_ = (poly_sum (GENLIST (\k. f k % p) n) + (f n) % p) % p` by rw_tac std_ss[poly_mod_add, poly_mod_poly] >>
  `_ = poly_sum (GENLIST (\k. f k % p) (SUC n)) % p` by rw_tac std_ss[poly_sum_decompose_last] >>
  rw[]);

(* The following theorem extends:
> poly_irreducible_divides_master;
val it = |- !r. FiniteField r ==> !p. monic p /\ ipoly p ==> p pdivides master (CARD R ** deg p): thm
to an iff-condition, making use of:
> poly_master_divisibility;
val it = |- !r. Field r ==> !k. 1 < k ==> !n m. master (k ** n) pdivides master (k ** m) <=> n divides m: thm
> poly_master_gcd_identity;
val it = |- !r. Field r ==> !k n m. pgcd (master (k ** n)) (master (k ** m)) ~~ master (k ** gcd n m): thm
*)

(* This is the core part of poly_irreducible_master_divisibility. *)

(* Theorem: FiniteField r ==> !p. monic p /\ ipoly p ==>
            !n. p pdivides (master (CARD R ** n)) ==>
   (PolyModRing r p).carrier SUBSET poly_roots (PolyModRing r p) (Master ((PolyModRing r p)) (CARD R ** n)) *)
(* Proof:
   Let s = PolyModRing r p, b = CARD R ** n.
   By SUBSET_DEF, poly_roots_member, this is to show:
   !x. x IN s.carrier ==> poly_root s (Master s b) x

   Note x IN s.carrier ==> poly x             by poly_mod_ring_element
    and pmonic p                              by poly_monic_irreducible_property
   Also poly_fun (\k. x ' k * X ** k)         by poly_ring_element
    and poly_fun (\k. x ' k * (X ** b) ** k)  by poly_ring_element
    Now p pdivides (master b)                 by given
     so (X ** b == X) (pm p)                  by poly_ulead_divides_master_condition

    Let c = char r
   Then ?m. 0 < m /\ (CARD R = c ** m)        by finite_field_card
    and b = (CARD R) ** n = c ** (m * n)      by EXP_EXP_MULT
   Also prime c                               by finite_field_char, FiniteField r
    and rfun (\k. x ' k)                      by poly_coeff_ring_fun
    and poly (X % p)                          by poly_mod_poly, pmonic p

        x ** b % p
      = (poly_sum (GENLIST (\k. x ' k * X ** k) (SUC (deg x)))) ** b % p             by poly_eq_poly_sum
      = poly_sum (GENLIST (\k. (x ' k * X ** k) ** b) (SUC (deg x))) % p             by poly_sum_freshman_all, b = c ** (m * n)
      = poly_sum (GENLIST (\k. (x ' k) ** b * (X ** k) ** b) (SUC (deg x))) % p      by poly_cmult_exp
      = poly_sum (GENLIST (\k. (x ' k) * (X ** k) ** b) (SUC (deg x))) % p           by finite_field_fermat_all, b = (CARD R) ** n
      = poly_sum (GENLIST (\k. x ' k * (X ** b) ** k) (SUC (deg x))) % p             by poly_exp_mult_comm]
      = poly_sum (GENLIST (\k. (x ' k * (X ** b) ** k) % p) (SUC (deg x))) % p       by poly_mod_poly_sum_gen
      = poly_sum (GENLIST (\k. (x ' k * ((X ** b) ** k % p)) % p) (SUC (deg x))) % p by poly_mod_cmult
      = poly_sum (GENLIST (\k. (x ' k * (((X ** b) % p) ** k % p)) % p) (SUC (deg x))) % p  by poly_mod_exp
      = poly_sum (GENLIST (\k. (x ' k * ((X % p) ** k % p)) % p) (SUC (deg x))) % p  by pmod_def_alt, (X ** b == X) (pm p)
      = poly_sum (GENLIST (\k. (x ' k * (X ** k % p)) % p) (SUC (deg x))) % p        by poly_mod_exp
      = poly_sum (GENLIST (\k. (x ' k * X ** k) % p) (SUC (deg x))) % p              by poly_mod_cmult
      = poly_sum (GENLIST (\k. x ' k * X ** k) (SUC (deg x))) % p                    by poly_mod_poly_sum_gen
      = x % p                                                                        by poly_eq_poly_sum

     Therefore, (x ** b == x) (pm p)          by pmod_def_alt, x ** b % p = x % p
     Hence  poly_root s (Master s b) x        by poly_mod_master_root_condition
*)
val poly_irreducible_master_factor_all_roots = store_thm(
  "poly_irreducible_master_factor_all_roots",
  ``!r:'a field. FiniteField r ==> !p. monic p /\ ipoly p ==>
   !n. p pdivides (master (CARD R ** n)) ==>
       (PolyModRing r p).carrier SUBSET poly_roots (PolyModRing r p) (Master ((PolyModRing r p)) (CARD R ** n))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `poly X /\ poly |1| /\ !k. poly (X ** k)` by rw[] >>
  qabbrev_tac `s = PolyModRing r p` >>
  qabbrev_tac `b = CARD R ** n` >>
  rw_tac std_ss[SUBSET_DEF, poly_roots_member] >>
  `poly x` by metis_tac[poly_mod_ring_element] >>
  `pmonic p` by rw[poly_monic_irreducible_property] >>
  `poly_fun (\k. x ' k * X ** k)` by rw[poly_ring_element] >>
  `poly_fun (\k. x ' k * (X ** b) ** k)` by rw[poly_ring_element] >>
  `(X ** b == X) (pm p)` by rw[GSYM poly_ulead_divides_master_condition] >>
  qabbrev_tac `c = char r` >>
  `?m. 0 < m /\ (CARD R = c ** m)` by rw[finite_field_card, Abbr`c`] >>
  `b = c ** (m * n)` by rw[EXP_EXP_MULT, Abbr`b`] >>
  `prime c` by rw[finite_field_char, Abbr`c`] >>
  `rfun (\k. x ' k)` by rw[poly_coeff_ring_fun] >>
  `poly (X % p)` by rw[] >>
  `x ** b % p = (poly_sum (GENLIST (\k. x ' k * X ** k) (SUC (deg x)))) ** b % p` by rw[GSYM poly_eq_poly_sum] >>
  `_ = poly_sum (GENLIST (\k. (x ' k * X ** k) ** b) (SUC (deg x))) % p` by rw[poly_sum_freshman_all, Abbr`c`] >>
  `_ = poly_sum (GENLIST (\k. (x ' k) ** b * (X ** k) ** b) (SUC (deg x))) % p` by rw[poly_cmult_exp] >>
  `_ = poly_sum (GENLIST (\k. (x ' k) * (X ** k) ** b) (SUC (deg x))) % p` by rw[finite_field_fermat_all, Abbr`b`] >>
  `_ = poly_sum (GENLIST (\k. x ' k * (X ** b) ** k) (SUC (deg x))) % p` by rw_tac std_ss[poly_exp_mult_comm] >>
  `_ = poly_sum (GENLIST (\k. (x ' k * (X ** b) ** k) % p) (SUC (deg x))) % p` by rw_tac std_ss[poly_mod_poly_sum_gen, Abbr`b`] >>
  `_ = poly_sum (GENLIST (\k. (x ' k * ((X ** b) ** k % p)) % p) (SUC (deg x))) % p` by rw[GSYM poly_mod_cmult] >>
  `_ = poly_sum (GENLIST (\k. (x ' k * (((X ** b) % p) ** k % p)) % p) (SUC (deg x))) % p` by rw[GSYM poly_mod_exp] >>
  `_ = poly_sum (GENLIST (\k. (x ' k * ((X % p) ** k % p)) % p) (SUC (deg x))) % p` by metis_tac[pmod_def_alt] >>
  `_ = poly_sum (GENLIST (\k. (x ' k * (X ** k % p)) % p) (SUC (deg x))) % p` by rw[GSYM poly_mod_exp] >>
  `_ = poly_sum (GENLIST (\k. (x ' k * X ** k) % p) (SUC (deg x))) % p` by rw[GSYM poly_mod_cmult] >>
  `_ = poly_sum (GENLIST (\k. x ' k * X ** k) (SUC (deg x))) % p` by rw[GSYM poly_mod_poly_sum_gen] >>
  `_ = x % p` by metis_tac[poly_eq_poly_sum] >>
  `(x ** b == x) (pm p)` by rw[pmod_def_alt] >>
  rw[poly_mod_master_root_condition, Abbr`s`]);

(* This is a simple consequence of the above theorem *)

(* Theorem: FiniteField r ==> !p. monic p /\ ipoly p ==>
            !n. 0 < n /\ p pdivides (master (CARD R ** n)) ==> deg p <= n *)
(* Proof:
   Step 1: show (CARD R) ** n <> 1
   Note 1 < CARD R                                by finite_field_card_gt_1
     so 1 < CARD R ** n                           by ONE_LT_EXP, 0 < n
     or CARD R ** n <> 1                          by arithmetic

   Step 2: Apply poly_irreducible_master_factor_all_roots
   Let s = PolyModRing r p, t = Master s (CARD R ** n).
   Note FiniteField s                             by poly_mod_irreducible_finite_field
     so Field s                                   by finite_field_is_field
    ==> s.carrier SUBSET poly_roots s t           by poly_irreducible_master_factor_all_roots

   Step 3: Apply poly_roots_count
   Note Poly s t                                  by poly_master_poly
    and t <> poly_zero s                          by poly_master_eq_zero, field_one_ne_zero
   Thus FINITE (poly_roots s t)                   by poly_roots_finite, t <> poly_zero s
    ==> CARD s.carrier <= CARD (poly_roots s t)   by CARD_SUBSET
    But CARD (poly_roots s t) <= poly_deg s t     by poly_roots_count

   Step 4: Compute  CARD s.carrier and poly_deg s t
    Let d = deg p.
   Then 0 < d                                     by poly_irreducible_deg_nonzero
    and CARD s.carrier = CARD R ** d              by poly_mod_ring_card, 0 < d
   also poly_deg s t = CARD R ** n                by poly_master_deg, 1 < CARD R ** n

   Thus CARD R ** d <= CARD R ** n                by LESS_EQ_TRANS, from 3 and 4.
     or           d <= n                          by EXP_BASE_LE_MONO, 1 < CARD R
*)
val poly_irreducible_master_factor_deg = store_thm(
  "poly_irreducible_master_factor_deg",
  ``!r:'a field. FiniteField r ==> !p. monic p /\ ipoly p ==>
   !n. 0 < n /\ p pdivides (master (CARD R ** n)) ==> deg p <= n``,
  rpt (stripDup[FiniteField_def]) >>
  `1 < CARD R` by rw[finite_field_card_gt_1] >>
  `1 < CARD R ** n` by rw[ONE_LT_EXP] >>
  `CARD R ** n <> 1 /\ n <> 0` by decide_tac >>
  qabbrev_tac `s = PolyModRing r p` >>
  qabbrev_tac `t = Master s (CARD R ** n)` >>
  `FiniteField s` by rw[poly_mod_irreducible_finite_field, Abbr`s`] >>
  `Field s /\ Ring s /\ Ring r` by rw[finite_field_is_field] >>
  `s.carrier SUBSET poly_roots s t` by rw[poly_irreducible_master_factor_all_roots, Abbr`s`, Abbr`t`] >>
  `Poly s t` by rw[Abbr`t`] >>
  `t <> poly_zero s` by metis_tac[poly_master_eq_zero, field_one_ne_zero] >>
  `FINITE (poly_roots s t)` by rw[poly_roots_finite] >>
  `CARD s.carrier <= CARD (poly_roots s t)` by rw[CARD_SUBSET] >>
  `CARD (poly_roots s t) <= poly_deg s t` by rw[poly_roots_count] >>
  qabbrev_tac `d = deg p` >>
  `0 < d` by rw[poly_irreducible_deg_nonzero, Abbr`d`] >>
  `CARD s.carrier = CARD R ** d` by metis_tac[poly_mod_ring_card, FiniteRing_def] >>
  `poly_deg s t = CARD R ** n` by metis_tac[poly_master_deg, field_one_ne_zero] >>
  `CARD R ** d <= CARD R ** n` by metis_tac[LESS_EQ_TRANS] >>
  metis_tac[EXP_BASE_LE_MONO]);

(* Theorem: FiniteField r ==> !p. monic p /\ ipoly p ==>
            !n. p pdivides (master (CARD R ** n)) <=> (deg p) divides n *)
(* Proof:
   If part: p pdivides (master (CARD R ** n)) ==> (deg p) divides n

      Step 1: Show p pdivides master (CARD R ** (gcd d n)).
      Method: By poly_master_gcd_identity.

        Let d = deg p, u = master (CARD R ** d), v = master (CARD R ** n)
      Since p pdivides u                    by poly_irreducible_divides_master
        and p pdivides v                    by given
      hence p pdivides (pgcd u v)           by poly_gcd_is_gcd
        But pgcd u v
          = pgcd (master (CARD R ** d)) (master (CARD R ** n))
          ~~ master (CARD R ** (gcd d n))   by poly_master_gcd_identity
        Let e = gcd d n, q = master (CARD R ** e)
       Then pgcd u v ~~ q                   by poly_master_gcd_identity
        and p pdivides q                    by poly_unit_eq_divisor, poly_gcd_poly, poly_master_poly

      Step 2: Show e = gcd d n = d, so that d divides n.
      Method: By d <= e, and e <= d, so e = d.

      Note 0 < e                            by GCD_EQ_0, 0 < d
      Then d <= e                           by poly_irreducible_master_factor_deg
       But e divides d                      by GCD_IS_GREATEST_COMMON_DIVISOR
        so e <= d                           by DIVIDES_LE, 0 < d
      Hence e = d                           by EQ_LESS_EQ
         or d divides n                     by divides_iff_gcd_fix

   Only-if part: (deg p) divides n ==> p pdivides (master (CARD R ** n))
      Let d = deg p, u = master (CARD R ** d), v = master (CARD R ** n)
      Since p pdivides u                    by poly_irreducible_divides_master
        and u pdivides v                    by poly_master_divisibility, d divides n
      hence p pdivides v                    by poly_divides_transitive
*)
val poly_irreducible_master_divisibility = store_thm(
  "poly_irreducible_master_divisibility",
  ``!r:'a field. FiniteField r ==> !p. monic p /\ ipoly p ==>
   !n. p pdivides (master (CARD R ** n)) <=> (deg p) divides n``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r` by rw[] >>
  qabbrev_tac `d = deg p` >>
  qabbrev_tac `u = master (CARD R ** d)` >>
  qabbrev_tac `v = master (CARD R ** n)` >>
  `p pdivides u` by rw[poly_irreducible_divides_master, Abbr`u`, Abbr`d`] >>
  `pmonic p` by rw[poly_monic_irreducible_property] >>
  `poly u /\ poly v` by rw[Abbr`u`, Abbr`v`] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    `p pdivides (pgcd u v)` by rw[poly_gcd_is_gcd] >>
    qabbrev_tac `e = gcd d n` >>
    qabbrev_tac `q = master (CARD R ** e)` >>
    `pgcd u v ~~ q` by rw[poly_master_gcd_identity, Abbr`u`, Abbr`v`, Abbr`q`, Abbr`e`] >>
    `p pdivides q` by metis_tac[poly_unit_eq_divisor, poly_gcd_poly, poly_master_poly] >>
    `0 < e` by metis_tac[GCD_EQ_0, NOT_ZERO_LT_ZERO] >>
    `d <= e` by rw[poly_irreducible_master_factor_deg, Abbr`d`] >>
    `e divides d` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`e`] >>
    `e <= d` by metis_tac[DIVIDES_LE] >>
    `e = d` by decide_tac >>
    rw[divides_iff_gcd_fix],
    `1 < CARD R` by rw[finite_field_card_gt_1] >>
    `u pdivides v` by rw[poly_master_divisibility, Abbr`u`, Abbr`v`] >>
    metis_tac[poly_divides_transitive]
  ]);

(* This is a milestone theorem. *)

(* Theorem: FiniteField r /\ s <<= r ==> !p. monic p /\ IPoly s p ==>
            (p pdivides (master (CARD B ** (r <:> s))) <=> deg p divides (r <:> s)) *)
(* Proof:
   Note FiniteField s          by subfield_finite_field
    and s <= r                 by subfield_is_subring
   Note Poly s p               by poly_irreducible_poly, by IPoly s p
    and Monic s p              by subring_poly_monic_iff, Poly s p
   Note deg p = Deg s p        by subring_poly_deg
     so 0 < deg p              by poly_irreducible_deg_nonzero, by IPoly s p
     or 0 < Deg s p            by subring_poly_deg
   Thus Pmonic s p             by poly_monic_pmonic
   Let q = master (CARD R).
   Then Poly s q               by poly_master_spoly
    and q = Master s (CARD R)  by subring_poly_master
   Thus p pdivides q <=> poly_divides s p (Master s (CARD R))  by subring_poly_divides_iff
    Now CARD R = CARD B ** (r <:> s)                           by finite_subfield_card_eqn
     so p pdivides q <=> deg p divides (r <:> s)               by poly_irreducible_master_divisibility

poly_irreducible_master_divisibility |> ISPEC ``s:'a field``;
|- FiniteField s ==> !p. Monic s p /\ IPoly s p ==>
                     !n. poly_divides s p (Master s (CARD B ** n)) <=> Deg s p divides n
*)
val poly_irreducible_master_subfield_divisibility = store_thm(
  "poly_irreducible_master_subfield_divisibility",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !p. monic p /\ IPoly s p ==>
   (p pdivides (master (CARD R)) <=> deg p divides (r <:> s))``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteField s` by metis_tac[subfield_finite_field] >>
  `s <= r` by rw[subfield_is_subring] >>
  `Poly s p` by rw[poly_irreducible_poly] >>
  `Monic s p` by metis_tac[subring_poly_monic_iff] >>
  `deg p = Deg s p` by rw[subring_poly_deg] >>
  `0 < deg p` by rw[poly_irreducible_deg_nonzero] >>
  `Pmonic s p` by metis_tac[poly_monic_pmonic, subring_poly_deg] >>
  qabbrev_tac `q = master (CARD R)` >>
  `Poly s q` by rw[poly_master_spoly, Abbr`q`] >>
  `CARD R = CARD B ** (r <:> s)` by rw[finite_subfield_card_eqn] >>
  metis_tac[poly_irreducible_master_divisibility, subring_poly_divides_iff, subring_poly_master]);

(* ------------------------------------------------------------------------- *)
(* Master as Product of Factors                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==> (master (CARD R) = PPROD (IMAGE factor R)) *)
(* Proof:
   Since FiniteField r
     ==> 1 < CARD R                                 by finite_field_card_gt_1
     and monic (master (CARD R))                    by poly_master_monic, 1 < CARD R
     and deg (master (CARD R)) = CARD R             by poly_master_deg, 1 < CARD R
     Now roots (master (CARD R)) = R                by poly_master_roots_all
      so CARD R = CARD (roots (master (CARD R)))    by above
   Hence master (CARD R)
       = poly_factors (master (CARD R))             by poly_prod_factor_roots_eq_poly
       = PPROD (IMAGE factor R)                     by notation
*)
val poly_master_eq_root_factor_product = store_thm(
  "poly_master_eq_root_factor_product",
  ``!r:'a field. FiniteField r ==> (master (CARD R) = PPROD (IMAGE factor R))``,
  rpt (stripDup[FiniteField_def]) >>
  `roots (master (CARD R)) = R` by rw[poly_master_roots_all] >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `1 < CARD R` by rw[finite_field_card_gt_1] >>
  `monic (master (CARD R))` by rw[poly_master_monic] >>
  `deg (master (CARD R)) = CARD R` by rw[poly_master_deg] >>
  metis_tac[poly_prod_factor_roots_eq_poly]);

(* Theorem: FiniteField r ==> (master (CARD R) = PPROD {X - c * |1| | c | c IN R}) *)
(* Proof:
   Note 1 < CARD R                          by finite_field_card_gt_1
    and roots (master (CARD R)) = R         by poly_master_roots_all
   Also monic (master (CARD R))             by poly_master_monic, 1 < CARD R
    and deg (master (CARD R)) = CARD R      by poly_master_deg
        master (CARD R)
      = PPROD {X - c * |1| | c | c IN R}    by poly_eq_prod_factor_roots_alt
*)
val poly_master_eq_root_factor_product_alt = store_thm(
  "poly_master_eq_root_factor_product_alt",
  ``!r:'a field. FiniteField r ==> (master (CARD R) = PPROD {X - c * |1| | c | c IN R})``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `1 < CARD R` by rw[finite_field_card_gt_1] >>
  `roots (master (CARD R)) = R` by rw[poly_master_roots_all] >>
  `monic (master (CARD R))` by rw[] >>
  `deg (master (CARD R)) = CARD R` by rw[] >>
  metis_tac[poly_eq_prod_factor_roots_alt]);


(* ------------------------------------------------------------------------- *)
(* Subfield Conditions                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==> !s. s <<= r ==>
            !x. x IN R ==> (x IN B <=> (x ** CARD B = x)) *)
(* Proof:
   Since FiniteField r, FiniteField s      by subfield_finite_field
   If part: x IN B ==> x ** CARD B = x
      True by finite_field_fermat_thm, subfield_exp.
   Only-if part: x IN R /\ x ** CARD B = x ==> x IN B
      Let n = CARD B, p = master n.
      Then !y. y IN B ==> poly_root s (master s n) y   by poly_master_root_all
        or !y. y IN B ==> root p y                     by poly_master_subfield_root
        or !y. y IN B ==> y IN (roots p)               by poly_roots_member, subfield_element
        so B SUBSET (roots p)                          by SUBSET_DEF
       But x IN R /\ x ** n = x            by given
        so root p x                        by poly_master_root
        or x IN (roots p)                  by poly_roots_member
      By contradiction, suppose x NOTIN B.
      Then B <> roots p                    by x IN (roots p)
        so B PSUBSET (roots p)             by PSUBSET_DEF
       Now poly p                          by poly_master_poly
       and 1 < n                           by finite_field_card_gt_1
       and p <> |0|                        by poly_master_eq_zero, n <> 1.
        so FINITE (roots p)                by poly_roots_finite, p <> |0|
      Thus n < CARD (roots p)              by CARD_PSUBSET
        so deg p = n                       by poly_master_deg, 1 < n
      Thus CARD (roots p) <= n             by poly_roots_count, p <> |0|
      This contradicts n < CARD (roots p).
*)
val subfield_element_condition = store_thm(
  "subfield_element_condition",
  ``!r:'a field. FiniteField r ==> !s. s <<= r ==>
   !x. x IN R ==> (x IN B <=> (x ** CARD B = x))``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteField s` by metis_tac[subfield_finite_field] >>
  rw[EQ_IMP_THM] >-
  metis_tac[finite_field_fermat_thm, subfield_exp] >>
  `Ring r /\ Ring s` by rw[] >>
  qabbrev_tac `n = CARD B` >>
  qabbrev_tac `p = master n` >>
  `!y. y IN B ==> root p y` by metis_tac[poly_master_root_all, poly_master_subfield_root] >>
  `B SUBSET (roots p)` by metis_tac[poly_roots_member, SUBSET_DEF, subfield_element] >>
  `x IN roots p` by rw[poly_master_root, poly_roots_member, Abbr`p`, Abbr`n`] >>
  spose_not_then strip_assume_tac >>
  `B <> roots p` by metis_tac[] >>
  `B PSUBSET (roots p)` by rw[PSUBSET_DEF] >>
  `poly p` by rw[Abbr`p`] >>
  `1 < n` by rw[finite_field_card_gt_1, Abbr`n`] >>
  `n <> 1` by decide_tac >>
  `p <> |0|` by metis_tac[poly_master_eq_zero, field_one_ne_zero] >>
  `deg p = n` by rw[poly_master_deg, Abbr`p`, Abbr`n`] >>
  `FINITE (roots p)` by rw[poly_roots_finite] >>
  `n < CARD (roots p)` by rw[CARD_PSUBSET, Abbr`n`] >>
  `CARD (roots p) <= n` by metis_tac[poly_roots_count] >>
  decide_tac);

(* This is a milestone theorem. *)

(* Theorem: FiniteField r ==> !s. s <<= r ==>
            !p. poly p ==> (Poly s p <=> (p ** CARD B = peval p (X ** CARD B))) *)
(* Proof:
   Note FiniteField s              by subfield_finite_field
    and char s = char r            by subfield_char
   Let m = CARD B, c = char r.
   Then prime c                    by finite_field_char
    and ?d. 0 < d /\ (m = c ** d)  by finite_field_card

   Step 1: compute p ** m
       Let n = SUC (deg p).
  Claim 1: p ** m = poly_sum (GENLIST (\k. (p ' k) ** m * (X ** m) ** k) n)
    Proof: Let f = \k. p ' k, then rfun f                           by poly_coeff_ring_fun
           p ** m
         = (poly_sum (GENLIST (\k. p ' k * X ** k) n)) ** m         by poly_eq_poly_sum
         = (poly_sum (GENLIST (\k. f k * X ** k) n)) ** m           by FUN_EQ_THM, poly_cmult_exp, poly_exp_mult_comm
         = poly_sum (GENLIST (\k. f k * X ** k) ** m) n)            by poly_sum_freshman_all
         = poly_sum (GENLIST (\k. (f k) ** m * (X ** k) ** m) n)    by EXP_BASE_MULT
         = poly_sum (GENLIST (\k. (f k) ** m * (X ** m) ** k) n)    by MULT_COMM
         = poly_sum (GENLIST (\k. (p ' k) ** m * (X ** m) ** k) n)  by f = \k. p ' k

   If part: Poly s p ==> p ** m = peval p (X ** m)
      Since Poly s p
        ==> !k. p ' k IN B                by subfield_eq_subring, subring_poly_coeff, poly_coeff_element
        ==> !k. (p ' k) ** m = p ' k      by finite_field_fermat_thm, subfield_exp [1]
       Thus peval p (X ** m)
          = poly_sum (GENLIST (\k. p ' k * (X ** m) ** k) (SUC (deg p)))  by poly_peval_by_poly_sum
          = p ** m                        by Step 1

   Only-if part: p ** m = peval p (X ** m) ==> Poly s p
       Let q = poly_sum (GENLIST (\k. (p ' k) ** m * X ** k) n)
   Step 2: compute peval q (X ** m)
  Claim 2: peval q (X ** m) = poly_sum (GENLIST (\k. (p ' k) ** m * (X ** m) ** k) n)
    Proof: Note rfun (\k. (p ' k) ** m)                             by ring_fun_def, poly_coeff_element
           Let g = (\k. (p ' k) ** m * X ** k), then poly_fun g     by poly_fun_from_ring_fun
           peval q (X ** m)
         = poly_sum (MAP (\x. peval x (X ** m)) (GENLIST g n))      by poly_peval_poly_sum_gen, poly_fun g
         = poly_sum (GENLIST ((\x. peval x (X ** m)) o g) n)        by MAP_GENLIST
         = poly_sum (GENLIST (\k. (p ' k) ** m * (X ** m) ** k) n)  by FUN_EQ_THM, poly_peval_cmult, poly_peval_X_exp

     Hence p ** m = peval q (X ** m)      by Claim 1, Claim 2, [*]
     Since deg (X ** m) = m               by poly_deg_X_exp
       and 0 < m                          by finite_field_card_pos
      With p ** m = peval p (X ** m)      by given
       ==> peval q (X ** m) = peval p (X ** m)    by [*]
       ==> q = p                          by poly_peval_eq, 0 < deg (X ** m)

  Claim 3: !k. q ' k = (p ' k) ** m
    Proof: If p = |0|,
              Then q = |0|,
                so (p ' k = #0) /\ (q ' k = #0)     by poly_coeff_zero
               and (p ' k) ** m = #0                by field_zero_exp, m <> 0
             Hence true.
           If p <> |0|,
              If deg p < k,
                 Then (p ' k = #0) /\ (q ' k = #0)   by poly_coeff_nonzero
                  and (p ' k) ** m = #0              by field_zero_exp, m <> 0
                 Hence true.
              If ~(deg p < k),
                 Let f = \k. p ' k ** m
                 Then rfun f              by ring_fun_def, poly_coeff_element, ring_exp_element
                  and f (deg p)
                    = p ' (deg p) ** m
                    = (lead p) ** m       by poly_coeff_lead, p <> |0|
                    <> #0                 by field_exp_eq_zero, poly_lead_nonzero
                      q ' k
                    = f k                 by poly_sum_gen_coeff
                    = (p ' k) ** m

     Hence !k. q ' k = (p ' k) ** m       by Claim 3, [1]
      Also !k. q ' k = p ' k              by q = p, [2]
      Thus !k. (p ' k) ** m = p ' k       by [1], [2]
       Now !k. p ' k IN R                 by poly_coeff_element
      thus !k. p ' k IN B                 by subfield_element_condition
     Hence cpoly r s p                    by common_poly_alt
        or Poly s p                       by subring_poly_alt
*)
val subfield_poly_condition = store_thm(
  "subfield_poly_condition",
  ``!r:'a field. FiniteField r ==> !s. s <<= r ==>
   !p. poly p ==> (Poly s p <=> (p ** CARD B = peval p (X ** CARD B)))``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteField s` by metis_tac[subfield_finite_field] >>
  `Ring r /\ Ring s /\ #1 <> #0` by rw[] >>
  qabbrev_tac `m = CARD B` >>
  qabbrev_tac `c = char r` >>
  `poly X /\ poly (X ** m)` by rw[] >>
  `prime c` by rw[finite_field_char, Abbr`c`] >>
  `char s = c` by rw[subfield_char, Abbr`c`] >>
  `?d. 0 < d /\ (m = c ** d)` by metis_tac[finite_field_card] >>
  `0 < m` by rw[finite_field_card_pos, Abbr`m`] >>
  `m <> 0` by decide_tac >>
  qabbrev_tac `n = SUC (deg p)` >>
  `p ** m = poly_sum (GENLIST (\k. (p ' k) ** m * (X ** m) ** k) n)` by
  (`rfun \k. p ' k` by rw[poly_coeff_ring_fun] >>
  `p ** m = poly_sum (GENLIST (\k. p ' k * X ** k) n) ** m` by rw[GSYM poly_eq_poly_sum, Abbr`n`] >>
  `_ = poly_sum (GENLIST (\k. (p ' k * X ** k) ** m) n)` by rw[poly_sum_freshman_all, Abbr`c`] >>
  `_ = poly_sum (GENLIST (\k. (p ' k) ** m * (X ** m) ** k) n)` by rw[FUN_EQ_THM, poly_cmult_exp, poly_exp_mult_comm] >>
  rw[]) >>
  rewrite_tac[EQ_IMP_THM] >>
  rpt strip_tac >| [
    `!k. p ' k IN B` by metis_tac[subfield_eq_subring, subring_poly_coeff, poly_coeff_element] >>
    `!k. (p ' k) ** m = p ' k` by metis_tac[finite_field_fermat_thm, subfield_exp] >>
    rw[poly_peval_by_poly_sum],
    qabbrev_tac `q = poly_sum (GENLIST (\k. (p ' k) ** m * X ** k) n)` >>
    `deg (X ** m) = m` by rw[] >>
    `poly q` by rw[poly_sum_poly, poly_list_gen_from_ring_fun, Abbr`q`] >>
    `peval p (X ** m) = peval q (X ** m)` by
  (qabbrev_tac `f = (\k. (p ' k) ** m * X ** k)` >>
    `poly_fun f` by rw[poly_fun_from_ring_fun, Abbr`f`] >>
    `(\x. peval x (X ** m)) o f = (\k. (p ' k) ** m * (X ** m) ** k)` by rw[FUN_EQ_THM, poly_peval_cmult, poly_peval_X_exp, Abbr`f`] >>
    `peval q (X ** m) = poly_sum (GENLIST ((\x. peval x (X ** m)) o f) n)` by rw[poly_peval_poly_sum_gen, MAP_GENLIST, Abbr`q`] >>
    qabbrev_tac `g = (\k. p ' k ** m * (X ** m) ** k)` >>
    metis_tac[]) >>
    `q = p` by metis_tac[poly_peval_eq] >>
    `!k. q ' k = (p ' k) ** m` by
    (rpt strip_tac >>
    Cases_on `p = |0|` >-
    rw[field_zero_exp] >>
    Cases_on `deg p < k` >-
    rw[poly_coeff_nonzero, field_zero_exp] >>
    qabbrev_tac `f = \k. p ' k ** m` >>
    `rfun f` by metis_tac[ring_fun_def, poly_coeff_element, ring_exp_element] >>
    `f (deg p) = p ' (deg p) ** m` by rw[Abbr`f`] >>
    `_ = (lead p) ** m` by metis_tac[poly_coeff_lead] >>
    `lead p IN R` by rw[] >>
    `f (deg p) <> #0` by metis_tac[field_exp_eq_zero, poly_lead_nonzero] >>
    `GENLIST (\k. p ' k ** m * X ** k) n = GENLIST (\k. f k * X ** k) (SUC (deg p))` by rw[] >>
    `q = poly_sum (GENLIST (\k. f k * X ** k) (SUC (deg p)))` by metis_tac[] >>
    `q ' k = f k` by rw[poly_sum_gen_coeff] >>
    rw[]
    ) >>
    `!k. p ' k IN B` by metis_tac[poly_coeff_element, subfield_element_condition] >>
    metis_tac[subfield_is_subring, subring_poly_alt, common_poly_alt]
  ]);

(* Another milestone theorem! *)

(* ------------------------------------------------------------------------- *)
(* Sets of Monic Irreducible Polynomials                                     *)
(* ------------------------------------------------------------------------- *)

(* Define the set of monic irreducibles in a field, with degree equal to n *)
val monic_irreducibles_degree_def = Define`
    monic_irreducibles_degree (r:'a field) (n:num) = {p | monic p /\ ipoly p /\ (deg p = n)}
`;

(* Define the set of monic irreducibles in a field, with degree dividing n *)
val monic_irreducibles_bounded_def = Define`
    monic_irreducibles_bounded (r:'a field) (n:num) =
    BIGUNION (IMAGE (monic_irreducibles_degree r) (divisors n))
`;

(* Theorem: p IN (monic_irreducibles_degree r n) <=> monic p /\ ipoly p /\ (deg p = n) *)
(* Proof: by monic_irreducibles_degree_def *)
val monic_irreducibles_degree_member = store_thm(
  "monic_irreducibles_degree_member",
  ``!(r:'a field) n p. p IN (monic_irreducibles_degree r n) <=> monic p /\ ipoly p /\ (deg p = n)``,
  rw[monic_irreducibles_degree_def]);

(* Theorem: Field r ==> (p IN (monic_irreducibles_bounded r n) <=>
            monic p /\ ipoly p /\ (deg p <= n) /\ (deg p) divides n) *)
(* Proof:
   Note 0 < deg p                                by poly_irreducible_deg_nonzero
       p IN (monic_irreducibles_bounded r n)
   <=> p IN BIGUNION (IMAGE (monic_irreducibles_degree r) (divisors n))        by monic_irreducibles_bounded_def
   <=> ?s. p IN s /\ s IN (IMAGE (monic_irreducibles_degree r) (divisors n))   by IN_BIGUNION
   Take s = monic_irreducibles_degree r (deg p),
   Then p IN s
    <=> monic p /\ ipoly p /\ (deg p = deg p)    by monic_irreducibles_degree_member
    and s IN (IMAGE (monic_irreducibles_degree r) (divisors n))
    <=> (deg p) IN (divisors n)
    <=> (deg p <= n) /\ (deg p) divides n        by divisors_element
*)
val monic_irreducibles_bounded_member = store_thm(
  "monic_irreducibles_bounded_member",
  ``!(r:'a field) n p. Field r ==>
      (p IN (monic_irreducibles_bounded r n) <=>
       monic p /\ ipoly p /\ (deg p <= n) /\ (deg p) divides n)``,
  (rw[monic_irreducibles_bounded_def, monic_irreducibles_degree_member, divisors_element, EXTENSION, EQ_IMP_THM] >> simp[]) >>
  qexists_tac `monic_irreducibles_degree r (deg p)` >>
  simp[monic_irreducibles_degree_member] >>
  qexists_tac `deg p` >>
  simp[poly_irreducible_deg_nonzero]);

(* Theorem: FINITE R /\ #0 IN R ==> !n. FINITE (monic_irreducibles_degree r n) *)
(* Proof:
   Let s = monic_irreducibles_degree r n, m = SUC n.
    Then n < m                                  by LESS_SUC
     and !p. p IN s ==> poly p /\ deg p < m     by monic_irreducibles_degree_member, poly_monic_poly
    Thus s SUBSET {p | poly p /\ deg p < m}     by SUBSET_DEF
     Now FINITE {p | poly p /\ deg p < m}       by poly_truncated_by_degree_finite
   Hence FINITE s                               by SUBSET_FINITE
*)
val monic_irreducibles_degree_finite = store_thm(
  "monic_irreducibles_degree_finite",
  ``!r:'a ring. FINITE R /\ #0 IN R ==> !n. FINITE (monic_irreducibles_degree r n)``,
  rpt strip_tac >>
  `n < SUC n` by decide_tac >>
  qabbrev_tac `s = monic_irreducibles_degree r n` >>
  qabbrev_tac `m = SUC n` >>
  `!p. p IN s ==> poly p /\ deg p < m` by metis_tac[monic_irreducibles_degree_member, poly_monic_poly] >>
  `s SUBSET {p | poly p /\ deg p < m}` by rw[SUBSET_DEF] >>
  `FINITE {p | poly p /\ deg p < m}` by rw[poly_truncated_by_degree_finite] >>
  metis_tac[SUBSET_FINITE]);

(* Theorem: FINITE R /\ #0 IN R ==> !n. FINITE (monic_irreducibles_bounded r n) *)
(* Proof:
   By monic_irreducibles_bounded_def, this is to show:
      FINITE (BIGUNION (IMAGE (monic_irreducibles_degree r) (divisors n)))
   By FINITE_BIGUNION, this is to show:
   (1) FINITE (IMAGE (monic_irreducibles_degree r) (divisors n))
       Since FINITE (divisors n)          by divisors_finite
       Hence true                         by IMAGE_FINITE
   (2) EVERY_FINITE (IMAGE (monic_irreducibles_degree r) (divisors n))
       That is, !x. x IN (divisors n), FINITE (monic_irreducibles_degree r x)   by IN_IMAGE
       This is true                       by monic_irreducibles_degree_finite
*)
val monic_irreducibles_bounded_finite = store_thm(
  "monic_irreducibles_bounded_finite",
  ``!r:'a ring. FINITE R /\ #0 IN R ==> !n. FINITE (monic_irreducibles_bounded r n)``,
  rw[monic_irreducibles_bounded_def] >-
  rw[divisors_finite] >>
  rw[monic_irreducibles_degree_finite]);

(* Theorem: Field r ==> (monic_irreducibles_degree r 0 = {}) *)
(* Proof:
   By contradiction, suppose monic_irreducibles_degree r 0 <> {}.
   Then ?p. p IN (monic_irreducibles_degree r 0)    by MEMBER_NOT_EMPTY
     or ?p. monic p /\ ipoly p /\ (deg p = 0)       by monic_irreducibles_degree_member
    But monic p /\ ipoly p ==> 0 < deg p            by poly_irreducible_deg_nonzero
    This contradicts deg p = 0.
*)
val monic_irreducibles_degree_0 = store_thm(
  "monic_irreducibles_degree_0",
  ``!r:'a field. Field r ==> (monic_irreducibles_degree r 0 = {})``,
  rw[monic_irreducibles_degree_member, EXTENSION] >>
  spose_not_then strip_assume_tac >>
  `0 < deg x` by rw[poly_irreducible_deg_nonzero] >>
  decide_tac);

(* Theorem: Field r ==> (monic_irreducibles_degree r 1 = IMAGE factor R) *)
(* Proof:
   By monic_irreducibles_degree_member, this is to show;
   (1) monic x /\ (deg x = 1) ==> ?x'. (x = factor x') /\ x' IN R
       True            by poly_monic_deg1_factor
   (2) x' IN R ==> monic (factor x')
       True            by poly_factor_monic
   (3) x' IN R ==> ipoly (factor x')
       Since poly (factor x')         by poly_factor_poly
         and deg (factor x') = 1      by poly_deg_factor
       Hence true                     by poly_deg_1_irreducible
   (4) x' IN R ==> deg (factor x') = 1
       True            by poly_deg_factor
*)
val monic_irreducibles_degree_1 = store_thm(
  "monic_irreducibles_degree_1",
  ``!r:'a field. Field r ==> (monic_irreducibles_degree r 1 = IMAGE factor R)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  rw[monic_irreducibles_degree_member, EXTENSION, EQ_IMP_THM] >-
  metis_tac[poly_monic_deg1_factor] >-
  rw[poly_factor_monic] >-
  metis_tac[poly_factor_poly, poly_deg_factor, poly_deg_1_irreducible] >>
  rw[poly_deg_factor]);

(* Theorem: Field r ==> (monic_irreducibles_bounded r 0 = {}) *)
(* Proof:
   Since x IN (monic_irreducibles_bounded r 0)
     <=> monic x /\ ipoly x /\ deg x <= 0 /\ deg x divides 0  by monic_irreducibles_bounded_member
     <=> monic x /\ ipoly x /\ (deg x = 0)                    by ALL_DIVIDES_0
     <=> x IN (monic_irreducibles_degree r 0)                 by monic_irreducibles_degree_member
   Hence  (monic_irreducibles_bounded r 0)
        = (monic_irreducibles_degree r 0)                     by EXTENSION
        = {}                                                  by monic_irreducibles_degree_0
*)
val monic_irreducibles_bounded_0 = store_thm(
  "monic_irreducibles_bounded_0",
  ``!r:'a field. Field r ==> (monic_irreducibles_bounded r 0 = {})``,
  rpt strip_tac >>
  `(monic_irreducibles_bounded r 0) = (monic_irreducibles_degree r 0)`
    by rw[monic_irreducibles_bounded_member, monic_irreducibles_degree_member,
          EXTENSION, EQ_IMP_THM] >>
  rw[monic_irreducibles_degree_0]);

(* Theorem: Field r ==> (monic_irreducibles_bounded r 1 = IMAGE factor R) *)
(* Proof:
   Since x IN (monic_irreducibles_bounded r 1)
     <=> monic x /\ ipoly x /\ deg x <= 1 /\ deg x divides 1  by monic_irreducibles_bounded_member
     <=> monic x /\ ipoly x /\ (deg x = 1)                    by DIVIDES_ONE
     <=> x IN (monic_irreducibles_degree r 1)                 by monic_irreducibles_degree_member
   Hence  (monic_irreducibles_bounded r 1)
        = (monic_irreducibles_degree r 1)                     by EXTENSION
        = IMAGE factor R                                      by monic_irreducibles_degree_1
*)
val monic_irreducibles_bounded_1 = store_thm(
  "monic_irreducibles_bounded_1",
  ``!r:'a field. Field r ==> (monic_irreducibles_bounded r 1 = IMAGE factor R)``,
  rpt strip_tac >>
  `(monic_irreducibles_bounded r 1) = (monic_irreducibles_degree r 1)`
    by rw[monic_irreducibles_bounded_member, monic_irreducibles_degree_member,
          DIVIDES_ONE, EXTENSION, EQ_IMP_THM] >>
  rw[monic_irreducibles_degree_1]);

(* Theorem: miset (monic_irreducibles_degree r n) *)
(* Proof: by monic_irreducibles_degree_member *)
val monic_irreducibles_degree_monic_irreducibles_set = store_thm(
  "monic_irreducibles_degree_monic_irreducibles_set",
  ``!r:'a ring. !n. miset (monic_irreducibles_degree r n)``,
  rw_tac std_ss[monic_irreducibles_degree_member]);

(* Theorem: mset (monic_irreducibles_degree r n) *)
(* Proof: by monic_irreducibles_degree_member *)
val monic_irreducibles_degree_monic_set = store_thm(
  "monic_irreducibles_degree_monic_set",
  ``!r:'a ring. !n. mset (monic_irreducibles_degree r n)``,
  rw_tac std_ss[monic_irreducibles_degree_member]);

(* Theorem: pset (monic_irreducibles_degree r n) *)
(* Proof: by monic_irreducibles_degree_monic_set, monic_set_poly_set *)
val monic_irreducibles_degree_poly_set = store_thm(
  "monic_irreducibles_degree_poly_set",
  ``!r:'a ring. !n. pset (monic_irreducibles_degree r n)``,
  metis_tac[monic_irreducibles_degree_monic_set, monic_set_poly_set]);

(* Theorem: Field r ==> !n. pcoprime_set (monic_irreducibles_degree r n) *)
(* Proof:
   By poly_coprime_set_def, this is to show:
   (1) p IN monic_irreducibles_degree r n ==> poly p
       Note p IN monic_irreducibles_degree r n
        ==> monic p                                    by monic_irreducibles_degree_member
        ==> poly p                                     by poly_monic_poly
   (2) p IN monic_irreducibles_degree r n /\ q IN monic_irreducibles_degree r n /\ p <> q ==> pcoprime p q
       Note p, q IN monic_irreducibles_degree r n
        ==> monic p /\ ipoly p /\ monic q /\ ipoly q   by monic_irreducibles_degree_member
       With p <> q ==> pcoprime p q                    by poly_monic_irreducibles_coprime
*)
val monic_irreducibles_degree_coprime_set = store_thm(
  "monic_irreducibles_degree_coprime_set",
  ``!r:'a field. Field r ==> !n. pcoprime_set (monic_irreducibles_degree r n)``,
  rw_tac std_ss[poly_coprime_set_def] >-
  metis_tac[monic_irreducibles_degree_member, poly_monic_poly] >>
  metis_tac[monic_irreducibles_degree_member, poly_monic_irreducibles_coprime]);

(* Theorem: Field r ==> !n. pcoprime_set (monic_irreducibles_bounded r n) *)
(* Proof:
   By poly_coprime_set_def, this is to show:
   (1) p IN monic_irreducibles_bounded r n ==> poly p
       Note p IN monic_irreducibles_bounded r n
        ==> monic p                                    by monic_irreducibles_bounded_member
        ==> poly p                                     by poly_monic_poly
   (2) p IN monic_irreducibles_bounded r n /\ q IN monic_irreducibles_bounded r n /\ p <> q ==> pcoprime p q
       Note p, q IN monic_irreducibles_bounded r n
        ==> monic p /\ ipoly p /\ monic q /\ ipoly q   by monic_irreducibles_bounded_member
       With p <> q ==> pcoprime p q                    by poly_monic_irreducibles_coprime
*)
val monic_irreducibles_bounded_coprime_set = store_thm(
  "monic_irreducibles_bounded_coprime_set",
  ``!r:'a field. Field r ==> !n. pcoprime_set (monic_irreducibles_bounded r n)``,
  rw_tac std_ss[poly_coprime_set_def] >-
  metis_tac[monic_irreducibles_bounded_member, poly_monic_poly] >>
  metis_tac[monic_irreducibles_bounded_member, poly_monic_irreducibles_coprime]);

(* ------------------------------------------------------------------------- *)
(* Product of Monic Irreducibles of the same degree                          *)
(* ------------------------------------------------------------------------- *)

(* Overload on the product of monic irreducibles of same degree *)
val _ = overload_on("poly_psi", ``\(r:'a ring) n. PPROD (monic_irreducibles_degree r n)``);
val _ = overload_on("Psi", ``poly_psi r``);

(* Theorem: FiniteRing r ==> !n. monic (Psi n) *)
(* Proof:
   Let s = monic_irreducibles_degree r n.
   Then FINITE s          by monic_irreducibles_degree_finite, FINITE R
    and mset s            by monic_irreducibles_degree_member
    ==> monic (PPROD s)   by poly_monic_prod_set_monic
     or monic (Psi n)     by notation
*)
val monic_irreducibles_degree_prod_set_monic = store_thm(
  "monic_irreducibles_degree_prod_set_monic",
  ``!r:'a ring. FiniteRing r ==> !n. monic (Psi n)``,
  rw[FiniteRing_def] >>
  qabbrev_tac `s = monic_irreducibles_degree r n` >>
  `FINITE s` by rw[monic_irreducibles_degree_finite, Abbr`s`] >>
  `mset s` by metis_tac[monic_irreducibles_degree_member] >>
  rw[poly_monic_prod_set_monic]);

(* Theorem: FiniteRing r ==> !n. poly (Psi n) *)
(* Proof: by monic_irreducibles_degree_prod_set_monic, poly_monic_poly *)
val monic_irreducibles_degree_prod_set_poly = store_thm(
  "monic_irreducibles_degree_prod_set_poly",
  ``!r:'a ring. FiniteRing r ==> !n. poly (Psi n)``,
  rw_tac std_ss[monic_irreducibles_degree_prod_set_monic, poly_monic_poly]);

(* Theorem: FiniteRing r /\ #1 <> #0 ==> !n. Psi n <> |0| *)
(* Proof: by monic_irreducibles_degree_prod_set_monic, poly_monic_nonzero *)
val monic_irreducibles_degree_prod_set_nonzero = store_thm(
  "monic_irreducibles_degree_prod_set_nonzero",
  ``!r:'a ring. FiniteRing r /\ #1 <> #0 ==> !n. Psi n <> |0|``,
  rw_tac std_ss[monic_irreducibles_degree_prod_set_monic, poly_monic_nonzero]);

(* ------------------------------------------------------------------------- *)
(* Master Polynomial as Product of Monic Irreducibles.                       *)
(* ------------------------------------------------------------------------- *)

(* Note:
The following result is easy (?) if we know the degrees are equal.
However, we want to use the result to show that the degrees are equal,
so the proof cannot rely on this.
Instead, the strategy goes like this:
- (PPROD s) divides master, so master = (q) * (PPROD s)
- By poly_ulead_divides_master_condition, only members of s can divide master.
- By pgcd master D(master) ~~ |1|, only s divides master, no s ** k with 1 < k divides master.
- Hence upoly q, which means q = |1| since (monic master) and (monic (PPROD s)).
*)

(* Theorem: FiniteField r ==> !s. s <<= r ==>
            !n. 0 < n ==> (Master s (CARD B ** n) = poly_prod_set s (monic_irreducibles_bounded s n)) *)
(* Proof:
   Note FiniteField s        by subfield_finite_field
    and FINITE B             by FiniteField_def
   Let b = monic_irreducibles_bounded s n,
       p = poly_prod_set s b,
       m = Master s (CARD B ** n).
   The goal: m = p
   The idea: (1) show: p pdivides m, then m = u * p for some u.
             (2) show: upoly u, then m ~~ p.
             (3) show: monic p /\ monic m, then m = p.
             Of course, all these happen in s, the subfield of r.

   Step 0, show basic results
    Note FINITE b                 by monic_irreducibles_bounded_finite, 0 < n, FINITE B
    Note 1 < CARD B               by finite_field_card_gt_1
    thus 1 < CARD B ** n          by ONE_LT_EXP, 0 < n
   Hence poly_monic s m           by poly_master_monic, , 1 < CARD B ** n
     and !p. p IN b ==> monic p   by monic_irreducibles_bounded_member
   Hence poly_monic s p           by poly_monic_prod_set_monic

   Step 1, show: poly_divides s p m
   By poly_prod_coprime_set_divides, this is to show:
   (1) !p. p IN b ==> poly_divides s p m
        Note p IN b
         ==> poly_monic s p /\ IPoly s p /\
             (poly_deg s p) divides n      by monic_irreducibles_bounded_member
       Hence poly_divides s p m            by poly_irreducible_master_divisibility
   (2) poly_coprime_set s b                by monic_irreducibles_bounded_coprime_set

   Step 2, show: unit_eq (PolyRing s) m p
   By poly_coprime_diff_unit_eq_prod_set, this is to show:
   (1) !p. poly_monic s p /\ IPoly s p /\ poly_divides s p m ==> p IN b
       Since poly_divides s p m
         ==> poly_deg s p divides n        by poly_irreducible_master_divisibility
        thus poly_deg s p <= n             by DIVIDES_LE, 0 < n
        With poly_monic s p /\ IPoly s p   by given
       Hence p IN b                        by monic_irreducibles_bounded_member
   (2) !p. p IN b ==> Poly s p             by monic_irreducibles_bounded_member, poly_monic_poly
   (3) poly_gcd s m (poly_diff s m) IN (Invertibles (PolyRing s).prod).carrier
       Effectively this says: pcoprime m (diff m) in subfield s.
       Since poly_gcd s m (poly_diff s m) ~~ |1|   by poly_master_coprime_diff
       Hence the result follows                    by poly_gcd_one_coprime

   Step 3, conclude: m = p
       With poly_monic s m                         by above
        and poly_monic s p                         by above
      Hence unit_eq (PolyRing s) m p ==> (m = p)   by poly_unit_eq_monic_eq
*)
val poly_master_subfield_factors = store_thm(
  "poly_master_subfield_factors",
  ``!r:'a field. FiniteField r ==> !s. s <<= r ==>
    !n. 0 < n ==> (Master s (CARD B ** n) = poly_prod_set s (monic_irreducibles_bounded s n))``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteField s` by metis_tac[subfield_finite_field] >>
  `FINITE B` by metis_tac[FiniteField_def] >>
  qabbrev_tac `b = monic_irreducibles_bounded s n` >>
  qabbrev_tac `p = poly_prod_set s b` >>
  qabbrev_tac `m = Master s (CARD B ** n)` >>
  `FINITE b` by rw[monic_irreducibles_bounded_finite, Abbr`b`] >>
  `1 < CARD B` by rw[finite_field_card_gt_1] >>
  `1 < CARD B ** n` by rw[ONE_LT_EXP] >>
  `poly_monic s m` by rw[poly_master_monic, Abbr`m`] >>
  `poly_monic s p` by rw[poly_monic_prod_set_monic, monic_irreducibles_bounded_member, Abbr`b`, Abbr`p`] >>
  `poly_divides s p m` by
  ((qunabbrev_tac `p` >> irule poly_prod_coprime_set_divides >> rpt conj_tac  >> simp[]) >-
  metis_tac[monic_irreducibles_bounded_member, poly_irreducible_master_divisibility] >>
  rw[monic_irreducibles_bounded_coprime_set, Abbr`b`]
  ) >>
  `unit_eq (PolyRing s) m p` by
    ((qunabbrev_tac `p` >> irule poly_coprime_diff_unit_eq_prod_set >> rpt conj_tac >> simp[]) >-
  metis_tac[monic_irreducibles_bounded_member, poly_irreducible_master_divisibility, DIVIDES_LE] >-
  rw[Abbr`b`, monic_irreducibles_bounded_member] >>
  rw[poly_master_coprime_diff, poly_gcd_one_coprime, Abbr`m`]
  ) >>
  metis_tac[poly_unit_eq_monic_eq, field_is_ring]);

(* Theorem: FiniteField r /\ s <<= r /\ 0 < n ==>
            (master (CARD B ** n) = poly_prod_set s (monic_irreducibles_bounded s n)) *)
(* Proof: by poly_master_subfield_factors, subring_poly_master *)
val poly_master_subfield_factors_alt = store_thm(
  "poly_master_subfield_factors_alt",
  ``!(r s):'a field n. FiniteField r /\ s <<= r /\ 0 < n ==>
                      (master (CARD B ** n) = poly_prod_set s (monic_irreducibles_bounded s n))``,
  metis_tac[poly_master_subfield_factors, subring_poly_master, subfield_is_subring]);

(* This is a milestone theorem. *)

(* Theorem: FiniteField r ==> !n. 0 < n ==> (master (CARD R ** n) = PPROD (monic_irreducibles_bounded r n)) *)
(* Proof: by poly_master_subfield_factors, taking s = r. *)
val poly_master_monic_irreducible_factors = store_thm(
  "poly_master_monic_irreducible_factors",
  ``!r:'a field. FiniteField r ==>
   !n. 0 < n ==> (master (CARD R ** n) = PPROD (monic_irreducibles_bounded r n))``,
  metis_tac[poly_master_subfield_factors, finite_field_is_field, subfield_refl]);

(* Theorem: FiniteField r ==> !s. s <<= r ==>
            (master (CARD R) = poly_prod_set s (monic_irreducibles_bounded s (r <:> s))) *)
(* Proof:
   Since Master s (CARD R) = master (CARD R)    by subring_poly_master
     and (CARD R = (CARD B) ** (r <:> s))
     and 0 < (r <:> s)                          by finite_subfield_card_eqn
   The result follows                           by poly_master_subfield_factors
*)
val poly_master_eq_irreducibles_product = store_thm(
  "poly_master_eq_irreducibles_product",
  ``!r:'a field. FiniteField r ==> !s. s <<= r ==>
       (master (CARD R) = poly_prod_set s (monic_irreducibles_bounded s (r <:> s)))``,
  rpt (stripDup[FiniteField_def]) >>
  `s <= r` by rw[subfield_is_subring] >>
  `Master s (CARD R) = master (CARD R)` by rw[subring_poly_master] >>
  `(CARD R = CARD B ** (r <:> s)) /\ 0 < (r <:> s)` by rw[finite_subfield_card_eqn] >>
  metis_tac[poly_master_subfield_factors]);

(* ------------------------------------------------------------------------- *)
(* Counting Monic Irreducible Polynomials                                    *)
(* ------------------------------------------------------------------------- *)

(* Define the count of monic irreducible polynomials of a fixed degree in subfield *)
val monic_irreducibles_count_def = Define`
    monic_irreducibles_count (r:'a ring) n = CARD (monic_irreducibles_degree r n)
`;

(* Theorem: FiniteRing r ==> !n. deg (Psi n) = n * (monic_irreducibles_count r n) *)
(* Proof:
   Let s = monic_irreducibles_degree r n.
   Then FINITE s                              by monic_irreducibles_degree_finite
    and !p. p IN s ==> monic p                by monic_irreducibles_degree_member
   also !p. p IN s ==> deg p = n              by monic_irreducibles_degree_member
   Thus deg (PPROD s)
      = SIGMA deg s                           by poly_monic_prod_set_deg
      = n * CARD s                            by SIGMA_CONSTANT
      = n * (monic_irreducibles_count r n)    by monic_irreducibles_count_def
*)
val monic_irreducibles_degree_prod_set_deg = store_thm(
  "monic_irreducibles_degree_prod_set_deg",
  ``!r:'a ring. FiniteRing r ==> !n. deg (Psi n) = n * (monic_irreducibles_count r n)``,
  rw[FiniteRing_def] >>
  `#0 IN R` by rw[] >>
  qabbrev_tac `s = monic_irreducibles_degree r n` >>
  `FINITE s` by rw[monic_irreducibles_degree_finite, Abbr`s`] >>
  `!p. p IN s ==> monic p /\ (deg p = n)` by rw[monic_irreducibles_degree_member, Abbr`s`] >>
  `deg (PPROD s) = SIGMA deg s` by rw[poly_monic_prod_set_deg] >>
  `_  = n * CARD s` by rw[SIGMA_CONSTANT] >>
  rw[monic_irreducibles_count_def, Abbr`s`]);

(* Theorem: FiniteRing r ==>
   (deg o PPROD o monic_irreducibles_degree r = (\d. d * (monic_irreducibles_count r d))) *)
(* Proof:
   Since (deg o PPROD o monic_irreducibles_degree r) n
        = deg (Psi n)                                     by application
        = n * monic_irreducibles_count r n                by monic_irreducibles_degree_prod_set_deg
        = (\d. d * (monic_irreducibles_count r d)) n      by application
   Hence the functions are equal                          by FUN_EQ_THM
*)
val monic_irreducibles_degree_prod_set_deg_fun = store_thm(
  "monic_irreducibles_degree_prod_set_deg_fun",
  ``!r:'a ring. FiniteRing r ==>
   (deg o PPROD o monic_irreducibles_degree r = (\d. d * (monic_irreducibles_count r d)))``,
  rw[monic_irreducibles_degree_prod_set_deg, FUN_EQ_THM]);

(* Theorem: n <> m ==> DISJOINT (monic_irreducibles_degree r n) (monic_irreducibles_degree r m) *)
(* Proof:
   Let s = monic_irreducibles_degree r n
       t = monic_irreducibles_degree r m
   By contradiction, suppose ~(DISJOINT s t),
     or s INTER t <> {}        by DISJOINT_DEF
   Then ?e. e IN (s INTER t)   by MEMBER_NOT_EMPTY
     or ?e. e IN s /\ e IN t   by IN_INTER
   Thus e IN s ==> deg e = n   by monic_irreducibles_degree_member
    and e IN t ==> deg e = m   by monic_irreducibles_degree_member
   This contradicts n <> m.
*)
val monic_irreducibles_degree_disjoint = store_thm(
  "monic_irreducibles_degree_disjoint",
  ``!r:'a ring. !n m. n <> m ==> DISJOINT (monic_irreducibles_degree r n) (monic_irreducibles_degree r m)``,
  metis_tac[DISJOINT_DEF, IN_INTER, MEMBER_NOT_EMPTY, monic_irreducibles_degree_member]);

(* Theorem: PAIR_DISJOINT (IMAGE (monic_irreducibles_degree r) (divisors n)) *)
(* Proof:
   Let s = monic_irreducibles_degree r x
       t = monic_irreducibles_degree r x'
   By IN_IMAGE, this is to show:
      x IN divisors n /\ x' IN divisors n /\ s <> t ==> DISJOINT s t
   Since s <> t ==> x <> x', hence true   by monic_irreducibles_degree_disjoint
*)
val monic_irreducibles_degree_pair_disjoint = store_thm(
  "monic_irreducibles_degree_pair_disjoint",
  ``!r:'a ring. !n. PAIR_DISJOINT (IMAGE (monic_irreducibles_degree r) (divisors n))``,
  metis_tac[IN_IMAGE, monic_irreducibles_degree_disjoint]);

(* Theorem: FiniteField r ==> !p. monic p /\ ipoly p ==>
            !n. p pdivides Psi n <=> p IN (monic_irreducibles_degree r n) *)
(* Proof:
   Let s = monic_irreducibles_degree r n.
    Note FINITE s                          by monic_irreducibles_degree_finite
     and miset s                           by monic_irreducibles_degree_member
   Hence p pdivides PPROD s ==> p IN s     by poly_prod_monic_irreducible_set_divisor
*)
val monic_irreducibles_degree_prod_set_divisor = store_thm(
  "monic_irreducibles_degree_prod_set_divisor",
  ``!r:'a ring. FiniteField r ==> !p. monic p /\ ipoly p ==>
   !n. p pdivides Psi n <=> p IN (monic_irreducibles_degree r n)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #0 IN R` by rw[] >>
  qabbrev_tac `s = monic_irreducibles_degree r n` >>
  `FINITE s` by rw[monic_irreducibles_degree_finite, Abbr`s`] >>
  `miset s` by rw[monic_irreducibles_degree_member, Abbr`s`] >>
  rw[poly_prod_monic_irreducible_set_divisor]);

(* Theorem: FiniteField r ==>
            !n. INJ PPROD (IMAGE (monic_irreducibles_degree r) (divisors n)) univ(:'a poly) *)
(* Proof:
   Let s = monic_irreducibles_degree r x
       t = monic_irreducibles_degree r y
   By INJ_DEF, this is to show:
      x IN divisors n /\ y IN divisors n /\ (PPROD s = PPROD t) ==> (s = t)
   Since FINITE s /\ FINITE t       by monic_irreducibles_degree_finite
     and miset s /\ miset t         by monic_irreducibles_degree_member
    With PPROD s = PPROD t          by given
   Hence s = t                      by poly_prod_monic_irreducible_set_eq
*)
val monic_irreducibles_degree_poly_prod_inj = store_thm(
  "monic_irreducibles_degree_poly_prod_inj",
  ``!r:'a field. FiniteField r ==> !n. INJ PPROD (IMAGE (monic_irreducibles_degree r) (divisors n)) univ(:'a poly)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #0 IN R` by rw[] >>
  rw[INJ_DEF] >>
  qabbrev_tac `s = monic_irreducibles_degree r x'` >>
  qabbrev_tac `t = monic_irreducibles_degree r x''` >>
  `FINITE s /\ FINITE t` by rw[monic_irreducibles_degree_finite, Abbr`s`, Abbr`t`] >>
  `miset s /\ miset t` by rw[monic_irreducibles_degree_member, Abbr`s`, Abbr`t`] >>
  metis_tac[poly_prod_monic_irreducible_set_eq]);

(* Note:
   This assertion: INJ (monic_irreducibles_degree r) (divisors n) univ(:'a poly -> bool)
   is vital for the last step of monic_irreducibles_bounded_prod_set_deg.
   This is valid only if !d. monic_irreducibles_degree r d <> {}.
   However, this is precisely the result we want after having this degree expression,
   (then compare to the degree of master equation, apply Mobius Inversion, etc.)
   If we know !d. monic_irreducibles_degree r d <> {}, we don't need to get into this
   trouble to establish (monic_irreducibles_count r n)!

   So, how to get around this obstacle?
   The strategy is this:
   For the image of the map, IMAGE (monic_irreducibles_degree r) (divisors n)
   assume that for some divisors d of n, monic_irreducibles_degree r d = {}
   then for other divisors d of n, monic_irreducibles_degree r d <> {}
   Partition (divisors n) into these two parts, then the image is split into two:
     IMAGE (monic_irreducibles_degree r) (divisors n)
   = IMAGE (monic_irreducibles_degree r) (part1 UNION part2)
   = IMAGE (monic_irreducibles_degree r) (part1) UNION
     IMAGE (monic_irreducibles_degree r) (part2)          by IMAGE_UNION
   Since these two images are disjoint, the sum splits into two.
   The first sum is zero, since PPROD {} = |1|, and deg |1| = 0.
   The second sum can apply INJ, since monic_irreducibles_degree r d <> {} by construction.
*)

(* Theorem: !s. FINITE s /\ (!d. d IN s ==> monic_irreducibles_degree r d <> {}) ==>
            INJ (monic_irreducibles_degree r) s univ(:'a poly -> bool) *)
(* Proof:
   By INJ_DEF, this is to show:
      x IN divisors n /\ y IN divisors n /\
      monic_irreducibles_degree r x = monic_irreducibles_degree r y ==> x = y
   Let s = monic_irreducibles_degree r x,
       t = monic_irreducibles_degree r y.
   By contradiction, assume x <> y.
   Then DISJOINT s t            by monic_irreducibles_degree_disjoint
     or s INTER t = {}          by DISJOINT_DEF
   Given s = t, s INTER t = s   by INTER_IDEMPOT
   This gives s = {},
   which contradicts s <> {}    by given implication.
*)
val monic_irreducibles_degree_nonempty_inj = store_thm(
  "monic_irreducibles_degree_nonempty_inj",
  ``!r:'a ring. !s. FINITE s /\ (!d. d IN s ==> monic_irreducibles_degree r d <> {}) ==>
    INJ (monic_irreducibles_degree r) s univ(:'a poly -> bool)``,
  rw[INJ_DEF] >>
  metis_tac[monic_irreducibles_degree_disjoint, INTER_IDEMPOT, DISJOINT_DEF]);

(* Theorem: SIGMA (deg o PPROD) (IMAGE (monic_irreducibles_degree r) (divisors n)) =
            SIGMA (deg o PPROD o monic_irreducibles_degree r) (divisors n) *)
(* Proof:
   Let s = divisors n,
       f = deg o PPROD,
       g = monic_irreducibles_degree r.
   The goal is to show: SIGMA f (IMAGE g s) = SIGMA (deg o PPROD o g) s
   Use sum_image_by_composition_with_partial_inj.

    Now FINITE s                          by divisors_finite
    and f {}
      = (deg o PPROD) {}                  by notation of f
      = deg (PPROD {})                    by function application
      = deg |1|                           by poly_prod_set_empty
      = 0                                 by poly_deg_one
   Also !t. FINITE t /\ (!x. x IN t ==> g x <> {}) ==>
        INJ g t univ(:'a poly -> bool)    by monic_irreducibles_degree_nonempty_inj
   Hence  SIGMA f (IMAGE g s)
        = SIGMA (f o g) s                 by sum_image_by_composition_with_partial_inj
        = SIGMA ((deg o PPROD) o g) s     by notation of f
        = SIGMA (deg o PPROD o g) s       by combinTheory.o_ASSOC
*)
val monic_irreducibles_degree_poly_prod_deg_sum = store_thm(
  "monic_irreducibles_degree_poly_prod_deg_sum",
  ``!r:'a ring. !n. SIGMA (deg o PPROD) (IMAGE (monic_irreducibles_degree r) (divisors n)) =
                   SIGMA (deg o PPROD o monic_irreducibles_degree r) (divisors n)``,
  rpt strip_tac >>
  rewrite_tac[combinTheory.o_ASSOC] >>
  (irule sum_image_by_composition_with_partial_inj >> rpt conj_tac) >-
  rw_tac std_ss[monic_irreducibles_degree_nonempty_inj] >-
  rw_tac std_ss[divisors_finite] >>
  rw_tac std_ss[poly_prod_set_empty, poly_deg_one]);

(* Note:
   Again, the following is easy (?) if we know (monic_irreducibles_degree r n) is nonempty,
   which gives an easy proof of the fact: INJ (monic_irreducibles_degree r) (divisors n) univ(:'a poly -> bool).
   However, we would like to use this result to establish (monic_irreducibles_degree r n) is nonempty.
   How to overcome this obstacle? Use the magic of monic_irreducibles_degree_poly_prod_deg_sum above!
*)

(* Next is the first part of monic_irreducibles_bounded_prod_set_deg *)

(* Theorem: FiniteField r ==> !n. PPROD (monic_irreducibles_bounded r n) =
                                  PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) (divisors n)) *)
(* Proof:
   Let P = IMAGE (monic_irreducibles_degree r) (divisors n).
   Since FINITE (divisors n)                 by divisors_finite
      so FINITE P                            by IMAGE_FINITE
    Also EVERY_FINITE P                      by monic_irreducibles_degree_finite, IN_IMAGE, FINITE R /\ #0 IN R
     and PAIR_DISJOINT P                     by monic_irreducibles_degree_pair_disjoint
     and EVERY_PSET P                        by monic_irreducibles_degree_member, IN_IMAGE, poly_monic_poly
    Note poly_set_multiplicative_fun r PPROD by poly_prod_set_mult_fun, Ring r
     and INJ PPROD P univ(:'a poly)          by monic_irreducibles_degree_poly_prod_inj, FiniteField r
    Also FINITE (IMAGE PPROD P)              by IMAGE_FINITE
     and mset (IMAGE PPROD P)                by poly_monic_prod_set_monic, monic_irreducibles_degree_member

     PPROD (monic_irreducibles_bounded r n)
   = PPROD (BIGUNION P)                      by monic_irreducibles_bounded_def
   = PPROD (IMAGE PPROD P)                   by poly_disjoint_bigunion_mult_fun
*)
val monic_irreducibles_bounded_prod_set = store_thm(
  "monic_irreducibles_bounded_prod_set",
  ``!r:'a field. FiniteField r ==> !n. PPROD (monic_irreducibles_bounded r n) =
                                      PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) (divisors n))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #0 IN R` by rw[] >>
  qabbrev_tac `P = IMAGE (monic_irreducibles_degree r) (divisors n)` >>
  `FINITE (divisors n)` by rw[divisors_finite] >>
  `FINITE P` by rw[Abbr`P`] >>
  `EVERY_FINITE P` by metis_tac[monic_irreducibles_degree_finite, IN_IMAGE] >>
  `PAIR_DISJOINT P` by metis_tac[monic_irreducibles_degree_pair_disjoint] >>
  `EVERY_PSET P` by metis_tac[monic_irreducibles_degree_member, IN_IMAGE, poly_monic_poly] >>
  `poly_set_multiplicative_fun r PPROD` by rw[poly_prod_set_mult_fun] >>
  `INJ PPROD P univ(:'a poly)` by rw[monic_irreducibles_degree_poly_prod_inj, Abbr`P`] >>
  `FINITE (IMAGE PPROD P)` by rw[] >>
  `mset (IMAGE PPROD P)` by prove_tac[poly_monic_prod_set_monic, monic_irreducibles_degree_member, IN_IMAGE] >>
  metis_tac[monic_irreducibles_bounded_def, poly_disjoint_bigunion_mult_fun]);

(* Theorem: FiniteField r ==> !n. deg (PPROD (monic_irreducibles_bounded r n)) =
                                  SIGMA (\d. d * (monic_irreducibles_count r d)) (divisors n) *)
(* Proof:
   Note FiniteField r ==> FiniteRing r    by finite_field_is_finite_ring
                                          for monic_irreducibles_degree_prod_set_deg_fun
   Let P = IMAGE (monic_irreducibles_degree r) (divisors n).
   Since FINITE (divisors n)              by divisors_finite
      so FINITE P                         by IMAGE_FINITE
    Also EVERY_FINITE P                   by monic_irreducibles_degree_finite, IN_IMAGE, FINITE R /\ #0 IN R
     and PAIR_DISJOINT P                  by monic_irreducibles_degree_pair_disjoint
     and EVERY_PSET P                     by monic_irreducibles_degree_member, IN_IMAGE, poly_monic_poly
    Note poly_set_multiplicative_fun r PPROD    by poly_prod_set_mult_fun, Ring r
     and INJ PPROD P univ(:'a poly)       by monic_irreducibles_degree_poly_prod_inj, FiniteField r
    Also FINITE (IMAGE PPROD P)           by IMAGE_FINITE
     and mset (IMAGE PPROD P)             by poly_monic_prod_set_monic, monic_irreducibles_degree_member

     deg (PPROD (monic_irreducibles_bounded r n))
   = deg (PPROD (BIGUNION P))                                         by monic_irreducibles_bounded_def
   = deg (PPROD (IMAGE PPROD P))                                      by poly_disjoint_bigunion_mult_fun
   = SIGMA deg (IMAGE PPROD P)                                        by poly_monic_prod_set_deg
   = SIGMA (deg o PPROD) P                                            by sum_image_by_composition, INJ PPROD
   = SIGMA (deg o PPROD o monic_irreducibles_degree r) (divisors n)   by monic_irreducibles_degree_poly_prod_deg_sum
   = SIGMA  (\d. d * (monic_irreducibles_count r d)) (divisors n)     by monic_irreducibles_degree_prod_set_deg_fun
*)
val monic_irreducibles_bounded_prod_set_deg = store_thm(
  "monic_irreducibles_bounded_prod_set_deg",
  ``!r:'a field. FiniteField r ==> !n. deg (PPROD (monic_irreducibles_bounded r n)) =
    SIGMA (\d. d * (monic_irreducibles_count r d)) (divisors n)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #0 IN R` by rw[] >>
  `FiniteRing r` by rw[finite_field_is_finite_ring] >>
  qabbrev_tac `P = IMAGE (monic_irreducibles_degree r) (divisors n)` >>
  `FINITE (divisors n)` by rw[divisors_finite] >>
  `FINITE P` by rw[Abbr`P`] >>
  `EVERY_FINITE P` by metis_tac[monic_irreducibles_degree_finite, IN_IMAGE] >>
  `PAIR_DISJOINT P` by metis_tac[monic_irreducibles_degree_pair_disjoint] >>
  `EVERY_PSET P` by metis_tac[monic_irreducibles_degree_member, IN_IMAGE, poly_monic_poly] >>
  `poly_set_multiplicative_fun r PPROD` by rw[poly_prod_set_mult_fun] >>
  `INJ PPROD P univ(:'a poly)` by rw[monic_irreducibles_degree_poly_prod_inj, Abbr`P`] >>
  `FINITE (IMAGE PPROD P)` by rw[] >>
  `mset (IMAGE PPROD P)` by prove_tac[poly_monic_prod_set_monic, monic_irreducibles_degree_member, IN_IMAGE] >>
  `deg (PPROD (monic_irreducibles_bounded r n)) = deg (PPROD (BIGUNION P))` by rw[monic_irreducibles_bounded_def, Abbr`P`] >>
  `_ = deg (PPROD (IMAGE PPROD P))` by metis_tac[poly_disjoint_bigunion_mult_fun] >>
  `_ = SIGMA deg (IMAGE PPROD P)` by rw[poly_monic_prod_set_deg] >>
  `_ = SIGMA (deg o PPROD) P` by rw[sum_image_by_composition] >>
  `_ = SIGMA ((deg o PPROD) o monic_irreducibles_degree r) (divisors n)` by rw[monic_irreducibles_degree_poly_prod_deg_sum, Abbr`P`] >>
  `_ = SIGMA  (\d. d * (monic_irreducibles_count r d)) (divisors n)` by rw[monic_irreducibles_degree_prod_set_deg_fun] >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* Finite Field and Subfield Order                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==> !s. s <<= r ==>
            !n. 0 < n ==> (CARD B ** n = SIGMA (\d. d * (monic_irreducibles_count s d)) (divisors n)) *)
(* Proof:
   Note FiniteField s              by subfield_finite_field
     so 1 < CARD B                 by finite_field_card_gt_1, FiniteField s
    and 1 < CARD B ** n            by ONE_LT_EXP, 1 < CARD B, 0 < n

      CARD B ** n
    = poly_deg s (Master s (CARD B ** n))                             by poly_master_deg
    = poly_deg s (poly_prod_set s (monic_irreducibles_bounded s n))   by poly_master_subfield_factors
    = SIGMA (\d. d * (monic_irreducibles_count s d)) (divisors n)     by monic_irreducibles_bounded_prod_set_deg
*)
val finite_subfield_card_exp_eqn = store_thm(
  "finite_subfield_card_exp_eqn",
  ``!r:'a field. FiniteField r ==> !s. s <<= r ==>
   !n. 0 < n ==> (CARD B ** n = SIGMA (\d. d * (monic_irreducibles_count s d)) (divisors n))``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteField s` by metis_tac[subfield_finite_field] >>
  `1 < CARD B` by rw[finite_field_card_gt_1] >>
  `1 < CARD B ** n` by rw[ONE_LT_EXP] >>
  `Ring s /\ s.prod.id <> s.sum.id` by rw[] >>
  metis_tac[poly_master_deg, poly_master_subfield_factors, monic_irreducibles_bounded_prod_set_deg]);

(* Theorem: FiniteField r ==>
            !n. 0 < n ==> (CARD R ** n = SIGMA (\d. d * (monic_irreducibles_count r d)) (divisors n)) *)
(* Proof:
   Since FiniteField r
     ==> Field r         by finite_field_is_field
     and subfield r r    by subfield_refl
   This is true          by finite_subfield_card_exp_eqn
*)
val finite_field_card_exp_eqn = store_thm(
  "finite_field_card_exp_eqn",
  ``!r:'a field. FiniteField r ==>
   !n. 0 < n ==> (CARD R ** n = SIGMA (\d. d * (monic_irreducibles_count r d)) (divisors n))``,
  metis_tac[finite_field_is_field, subfield_refl, finite_subfield_card_exp_eqn]);

(* This is a milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Roots of Master is a Subfield                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==> !n. #0 IN roots (master ((char r) ** n)) *)
(* Proof:
   Let m = (char r) ** n, p = master m.
   Note 0 < char r           by finite_field_char_pos, FiniteField r
     so 0 < m                by EXP_POS, 0 < char r
   Thus root p #0            by poly_master_root_zero
     or #0 IN roots p        by poly_roots_member
*)
val poly_master_roots_char_n_zero = store_thm(
  "poly_master_roots_char_n_zero",
  ``!r:'a field. FiniteField r ==> !n. #0 IN roots (master ((char r) ** n))``,
  rpt (stripDup[FiniteField_def]) >>
  `0 < (char r) ** n` by rw[finite_field_char_pos, EXP_POS] >>
  rw[poly_master_root_zero, poly_roots_member]);

(* Theorem: FiniteField r ==> !n. let p = master ((char r) ** n) in
            !x y. x IN roots p /\ y IN roots p ==> (x + y) IN roots p *)
(* Proof:
   Let m = (char r) ** n, p = master m.
   Then x IN R /\ (x ** m = x)            by poly_master_roots
    and y IN R /\ (y ** m = y)            by poly_master_roots
    Now x + y IN R                        by field_add_element
    and (x + y) ** m
      = x ** m + y ** m                   by finite_field_freshman_all, FiniteField r
      = x + y                             by above
   Thus (x + y) IN roots p                by poly_master_roots
*)
val poly_master_roots_add_root = store_thm(
  "poly_master_roots_add_root",
  ``!r:'a field. FiniteField r ==> !n. let p = master ((char r) ** n) in
   !x y. x IN roots p /\ y IN roots p ==> (x + y) IN roots p``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = (char r) ** n` >>
  rw_tac std_ss[] >>
  `Ring r` by rw[] >>
  `x IN R /\ (x ** m = x)` by metis_tac[poly_master_roots] >>
  `y IN R /\ (y ** m = y)` by metis_tac[poly_master_roots] >>
  `x + y IN R` by rw[] >>
  `(x + y) ** m = x ** m + y ** m` by rw[finite_field_freshman_all, Abbr`m`] >>
  `_ = x + y` by rw[] >>
  metis_tac[poly_master_roots]);

(* Theorem: FiniteField r ==> !n. let p = master ((char r) ** n) in
            !x y. x IN roots p /\ y IN roots p ==> (x - y) IN roots p *)
(* Proof:
   Let m = (char r) ** n, p = master m.
   Then x IN R /\ (x ** m = x)            by poly_master_roots
    and y IN R /\ (y ** m = y)            by poly_master_roots
    Now x - y IN R                        by field_sub_element
    and (x - y) ** m
      = x ** m - y ** m                   by finite_field_freshman_all_sub, FiniteField r
      = x - y                             by above
   Thus (x - y) IN roots p                by poly_master_roots
*)
val poly_master_roots_sub_root = store_thm(
  "poly_master_roots_sub_root",
  ``!r:'a field. FiniteField r ==> !n. let p = master ((char r) ** n) in
   !x y. x IN roots p /\ y IN roots p ==> (x - y) IN roots p``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = (char r) ** n` >>
  rw_tac std_ss[] >>
  `Ring r` by rw[] >>
  `x IN R /\ (x ** m = x)` by metis_tac[poly_master_roots] >>
  `y IN R /\ (y ** m = y)` by metis_tac[poly_master_roots] >>
  `x - y IN R` by rw[] >>
  `(x - y) ** m = x ** m - y ** m` by rw[finite_field_freshman_all_sub, Abbr`m`] >>
  `_ = x - y` by rw[] >>
  metis_tac[poly_master_roots]);

(* Theorem: FiniteField r ==> !n. let p = master ((char r) ** n) in !x. x IN roots p ==> -x IN roots p *)
(* Proof:
   Let m = (char r) ** n, p = master m.
   Then 0 < char r            by finite_field_char_pos, FiniteField r
     so 0 < m                 by EXP_POS
   Thus #0 IN roots p         by poly_master_root_zero, poly_roots_member
   Also x IN R                by poly_master_roots
    and #0 - x = -x           by field_zero_sub
   Thus -x IN roots p         by poly_master_roots_sub_root
*)
val poly_master_roots_neg_root = store_thm(
  "poly_master_roots_neg_root",
  ``!r:'a field. FiniteField r ==> !n. let p = master ((char r) ** n) in !x. x IN roots p ==> -x IN roots p``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = (char r) ** n` >>
  rw_tac std_ss[] >>
  `Ring r /\ #0 IN R` by rw[] >>
  `0 < m` by rw[finite_field_char_pos, EXP_POS, Abbr`m`] >>
  `#0 IN roots p` by rw[poly_master_root_zero, poly_roots_member, Abbr`p`] >>
  `x IN R` by metis_tac[poly_master_roots] >>
  `#0 - x = -x` by rw[field_zero_sub] >>
  metis_tac[poly_master_roots_sub_root]);

(* Theorem: Field r ==> !n. let p = master ((char r) ** n) in
            !x y. x IN roots p /\ y IN roots p ==> (x * y) IN roots p *)
(* Proof:
   Let m = (char r) ** n, p = master m.
   Then x IN R /\ (x ** m = x)            by poly_master_roots
    and y IN R /\ (y ** m = y)            by poly_master_roots
    Now x * y IN R                        by field_mult_element
    and (x * y) ** m
      = x ** m * y ** m                   by field_mult_exp, Field r
      = x * y                             by above
   Thus (x * y) IN roots p                by poly_master_roots
*)
val poly_master_roots_mult_root = store_thm(
  "poly_master_roots_mult_root",
  ``!r:'a field. Field r ==> !n. let p = master ((char r) ** n) in
   !x y. x IN roots p /\ y IN roots p ==> (x * y) IN roots p``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = (char r) ** n` >>
  rw_tac std_ss[] >>
  `Ring r` by rw[] >>
  `x IN R /\ (x ** m = x)` by metis_tac[poly_master_roots] >>
  `y IN R /\ (y ** m = y)` by metis_tac[poly_master_roots] >>
  `x * y IN R` by rw[] >>
  `(x * y) ** m = x ** m * y ** m` by rw[field_mult_exp] >>
  `_ = x * y` by rw[] >>
  metis_tac[poly_master_roots]);

(* Theorem: Field r ==> !n. let p = master ((char r) ** n) in
            !x. x IN roots p /\ x <> #0 ==> |/ x IN roots p *)
(* Proof:
   Let m = (char r) ** n, p = master m.
   Then x IN R /\ (x ** m = x)    by poly_master_roots
    ==> x IN R+                   by field_nonzero_eq, x <> #0
    ==> |/ x IN R                 by field_inv_element
    Now ( |/ x) ** m
      = |/ (x ** m)               by field_inv_exp
      = |/ x                      by above
   Thus |/ x IN roots p           by poly_master_roots
*)
val poly_master_roots_inv_root = store_thm(
  "poly_master_roots_inv_root",
  ``!r:'a field. Field r ==> !n. let p = master ((char r) ** n) in
   !x. x IN roots p /\ x <> #0 ==> |/ x IN roots p``,
  rpt strip_tac >>
  qabbrev_tac `m = (char r) ** n` >>
  rw_tac std_ss[] >>
  `Ring r` by rw[] >>
  `x IN R /\ (x ** m = x)` by metis_tac[poly_master_roots] >>
  `x IN R+` by rw[field_nonzero_eq] >>
  `|/ x IN R` by rw[field_inv_element] >>
  `( |/ x) ** m = |/ (x ** m)` by rw[field_inv_exp] >>
  `_ = |/ x` by rw[] >>
  metis_tac[poly_master_roots]);

(* Theorem: Field r ==> !n. let p = master ((char r) ** n) in
            !x y. x IN roots p /\ y IN roots p /\ y <> #0 ==> (x * |/ y) IN roots p *)
(* Proof: by poly_master_roots_mult_root, poly_master_roots_inv_root *)
val poly_master_roots_div_root = store_thm(
  "poly_master_roots_div_root",
  ``!r:'a field. Field r ==> !n. let p = master ((char r) ** n) in
   !x y. x IN roots p /\ y IN roots p /\ y <> #0 ==> (x * |/ y) IN roots p``,
  metis_tac[poly_master_roots_mult_root, poly_master_roots_inv_root]);

(* Theorem: FiniteField r ==> !n. AbelianGroup (subset_field r (roots (master ((char r) ** n)))).sum *)
(* Proof:
   Let m = (char r) ** n, p = master m.
   By AbelianGroup_def, group_def_alt, subset_field_property, this is to show:
   (1) x IN roots p /\ y IN roots p ==> x + y IN roots p
       This is true                     by poly_master_roots_add_root
   (2) x IN roots p /\ y IN roots p /\ z IN roots p ==> x + y + z = x + (y + z)
       Note x IN R /\ y IN R /\ z IN R  by poly_roots_element
         so x + y + z = x + (y + z)     by field_add_assoc
   (3) #0 IN roots p, true              by poly_master_roots_char_n_zero
   (4) x IN roots p ==> #0 + x = x
       Note x IN R                      by poly_roots_element
         so #0 + x = x                  by field_add_lzero
   (5) x IN roots p ==> ?y. y IN roots p /\ (y + x = #0)
       Let y = -x,
       Then -x IN roots p               by poly_master_roots_neg_root
        and x IN R                      by poly_roots_element
         so -x + x = #0                 by field_add_lneg
   (6) x IN roots p /\ y IN roots p ==> x + y = y + x
       Note x IN R /\ y IN R            by poly_roots_element
         so x + y = y + x               by field_add_comm
*)
val poly_master_roots_sum_abelian_group = store_thm(
  "poly_master_roots_sum_abelian_group",
  ``!r:'a field. FiniteField r ==> !n. AbelianGroup (subset_field r (roots (master ((char r) ** n)))).sum``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = (char r) ** n` >>
  qabbrev_tac `p = master m` >>
  rw_tac std_ss[AbelianGroup_def, group_def_alt, subset_field_property] >-
  metis_tac[poly_master_roots_add_root] >-
  metis_tac[field_add_assoc, poly_roots_element] >-
  rw[poly_master_roots_char_n_zero, Abbr`p`, Abbr`m`] >-
  metis_tac[field_add_lzero, poly_roots_element] >-
  metis_tac[poly_master_roots_neg_root, field_add_lneg, poly_roots_element] >>
  metis_tac[field_add_comm, poly_roots_element]);

(* Theorem: FiniteField r ==> !n. let p = master ((char r) ** n) in
            AbelianGroup ((subset_field r (roots p)).prod excluding (subset_field r (roots p)).sum.id) *)
(* Proof:
   Let m = (char r) ** n, p = master m.
   Let s = roots p DELETE #0
   Then !x. x IN s <=> x IN roots p /\ x <> #0   by DELETE_DEF
   By AbelianGroup_def, group_def_alt, excluding_def, subset_field_property, this is to show:
   (1) x IN roots p /\ y IN roots p ==> x * y IN roots p
       This is true                     by poly_master_roots_mult_root
   (2) x IN roots p /\ y IN roots p /\ x <> #0 /\ y <> #0 ==> x * y <> #0
       This is true                     by field_mult_eq_zero, poly_roots_element
   (3) x IN roots p /\ y IN roots p /\ z IN roots p ==> x * y * z = x * (y * z)
       Note x IN R /\ y IN R /\ z IN R  by poly_roots_element
         so x + y + z = x + (y + z)     by field_mult_assoc
   (4) #1 IN roots p
       This is true                     by poly_master_root_one, poly_roots_member
   (5) #1 <> #0, true                   by field_one_ne_zero
   (6) x IN roots p ==> #1 * x = x
       Note x IN R                      by poly_roots_element
         so #1 * x = x                  by field_mult_lone
   (7) x IN roots p /\ x <> #0 ==> ?y. (y IN roots p /\ y <> #0) /\ (y * x = #1)
       Note x IN R                      by poly_roots_element
        and x IN R+                     by field_nonzero_eq
       Let y = |/ x,
       Then |/ x IN roots p             by poly_master_roots_inv_root
        and |/ x IN R+, or |/ x <> #0   by field_inv_nonzero
         so |/ x * x = #1               by field_mult_linv
   (8) x IN roots p /\ y IN roots p ==> x * y = y * x
       Note x IN R /\ y IN R            by poly_roots_element
         so x * y = y * x               by field_mult_comm
*)
val poly_master_roots_prod_abelian_group = store_thm(
  "poly_master_roots_prod_abelian_group",
  ``!r:'a field. FiniteField r ==> !n. let p = master ((char r) ** n) in
       AbelianGroup ((subset_field r (roots p)).prod excluding (subset_field r (roots p)).sum.id)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = (char r) ** n` >>
  rw_tac std_ss[] >>
  qabbrev_tac `s = roots p DELETE #0` >>
  `!x. x IN s <=> x IN roots p /\ x <> #0` by rw[Abbr`s`] >>
  rw_tac std_ss[AbelianGroup_def, group_def_alt, excluding_def, GSYM DELETE_DEF, subset_field_property] >-
  metis_tac[poly_master_roots_mult_root] >-
  metis_tac[field_mult_eq_zero, poly_roots_element] >-
  metis_tac[field_mult_assoc, poly_roots_element] >-
  metis_tac[poly_master_root_one, poly_roots_member, field_one_element, field_is_ring] >-
  rw[] >-
  metis_tac[field_mult_lone, poly_roots_element] >-
  metis_tac[poly_master_roots_inv_root, poly_roots_element, field_inv_nonzero, field_mult_linv, field_nonzero_eq] >>
  metis_tac[field_mult_comm, poly_roots_element]);

(* Theorem: FiniteField r ==> !n. Field (subset_field r (roots (master ((char r) ** n)))) *)
(* Proof:
   Let m = (char r) ** n, p = master m.
   By field_def_alt, this is to show:
   (1) AbelianGroup (subset_field r (roots p)).sum
       This is true                  by poly_master_roots_sum_abelian_group
   (2) AbelianGroup ((subset_field r (roots p)).prod excluding (subset_field r (roots p)).sum.id)
       This is true                  by poly_master_roots_prod_abelian_group
   (3) (subset_field r (roots p)).sum.carrier = (subset_field r (roots p)).carrier
       This is true                  by subset_field_property
   (4) (subset_field r (roots p)).prod.carrier = (subset_field r (roots p)).carrier
       This is true                  by subset_field_property
   (5) x IN roots p ==> #0 * x = #0  by subset_field_property
       This is true                  by field_mult_lzero, poly_roots_element
   (6) x IN roots p /\ y IN roots p /\ z IN roots p ==> x * (y + z) = x * y + x * z  by subset_field_property
       This is true                  by field_mult_radd, poly_roots_element
*)
val poly_master_roots_field = store_thm(
  "poly_master_roots_field",
  ``!r:'a field. FiniteField r ==> !n. Field (subset_field r (roots (master ((char r) ** n))))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = (char r) ** n` >>
  qabbrev_tac `p = master m` >>
  rw_tac std_ss[field_def_alt] >-
  rw[poly_master_roots_sum_abelian_group, Abbr`p`, Abbr`m`] >-
  metis_tac[poly_master_roots_prod_abelian_group] >-
  rw_tac std_ss[subset_field_property] >-
  rw_tac std_ss[subset_field_property] >-
 (fs[subset_field_property] >>
  metis_tac[field_mult_lzero, poly_roots_element]) >>
  fs[subset_field_property] >>
  metis_tac[field_mult_radd, poly_roots_element]);

(* Theorem: FiniteField r ==> !n. FiniteField (subset_field r (roots (master (char r ** n)))) *)
(* Proof:
   Let s = subset_field r (roots (master (char r ** n))).
   Then Field s               by poly_master_roots_field
    and FINITE B              by poly_master_roots_finite_alt, subset_field_property
    ==> FiniteField s         by FiniteField_def
*)
val poly_master_roots_finite_field = store_thm(
  "poly_master_roots_finite_field",
  ``!r:'a field. FiniteField r ==> !n. FiniteField (subset_field r (roots (master (char r ** n))))``,
  rw_tac std_ss[poly_master_roots_finite_alt, poly_master_roots_field, subset_field_property, FiniteField_def]);

(* Theorem: FiniteField r ==> !n. subset_field r (roots (master ((char r) ** n))) <<= r *)
(* Proof:
   Let m = (char r) ** n, p = master m.
   This is to show:
   (1) Field (subset_field r (roots p)), true    by poly_master_roots_field
   (2) subfield (subset_field r (roots p)) r
       By subfield_def, FieldHomo_def, RingHomo_def, subset_field_property, this is to show:
       (1) x IN roots p ==> x IN R, true         by poly_roots_element
       (2) GroupHomo I (subset_field r (roots p)).sum r.sum
           By GroupHomo_def, subset_field_property, field_carriers, this is to show:
           (1) x IN roots p ==> x IN R, true     by poly_roots_element
       (3) MonoidHomo I (subset_field r (roots p)).prod r.prod
           By MonoidHomo_def, subset_field_property, field_carriers, this is to show:
           (1) x IN roots p ==> x IN R, true     by poly_roots_element
*)
val poly_master_roots_subfield = store_thm(
  "poly_master_roots_subfield",
  ``!r:'a field. FiniteField r ==> !n. subset_field r (roots (master ((char r) ** n))) <<= r``,
  strip_tac >>
  stripDup[FiniteField_def] >>
  strip_tac >>
  qabbrev_tac `m = (char r) ** n` >>
  qabbrev_tac `p = master m` >>
  rw_tac std_ss[] >-
  rw[poly_master_roots_field, Abbr`p`, Abbr`m`] >>
  rw_tac std_ss[subfield_def, FieldHomo_def, RingHomo_def, subset_field_property] >-
  metis_tac[poly_roots_element] >-
 (rw_tac std_ss[GroupHomo_def, subset_field_property, field_carriers] >>
  metis_tac[poly_roots_element]) >>
  rw_tac std_ss[MonoidHomo_def, subset_field_property, field_carriers] >>
  metis_tac[poly_roots_element]);

(* Theorem: FiniteField r ==> (FieldIso I (subset_field r (roots (master (char r ** (fdim r))))) r) *)
(* Proof:
   Let sm = subset_field r (roots (master (char r ** (fdim r)))).
   By subfield_carrier_antisym, this is to show:
   (1) R SUBSET sm.carrier
       By subset_field_property, SUBSET_DEF, this is to show:
          !x. x IN R ==> x IN roots (master (char r ** fdim r))
       Note R = roots (master (CARD R))    by poly_master_roots_all
        and CARD R = char r ** fdim r      by finite_field_card_eqn
       The assertion is true.
   (2) subfield sm r                       by poly_master_roots_subfield
*)
val poly_master_roots_subfield_iso_field = store_thm(
  "poly_master_roots_subfield_iso_field",
  ``!r:'a field. FiniteField r ==> (FieldIso I (subset_field r (roots (master (char r ** (fdim r))))) r)``,
  rpt strip_tac >>
  qabbrev_tac `sm = subset_field r (roots (master (char r ** (fdim r))))` >>
  (irule subfield_carrier_antisym >> rpt conj_tac) >| [
    rw_tac std_ss[subset_field_property, SUBSET_DEF, Abbr`sm`] >>
    `R = roots (master (CARD R))` by rw[poly_master_roots_all] >>
    `CARD R = char r ** fdim r` by rw[finite_field_card_eqn] >>
    metis_tac[],
    rw[poly_master_roots_subfield, Abbr`sm`]
  ]);

(* Theorem: FiniteField r ==> (FieldIso I (subset_field r (roots (master (char r ** (fdim r))))) r) *)
(* Proof:
   Let s = subset_field r (roots (master (char r ** (fdim r)))).
   Then FiniteField s            by poly_master_roots_finite_field
    and FieldIso I s r           by poly_master_roots_subfield_iso_field
    ==> FieldIso I r s           by field_iso_I_iso, finite_field_is_field
    Thus r =ff= d                by notation
*)
val poly_master_roots_subfield_isomorphism = store_thm(
  "poly_master_roots_subfield_isomorphism",
  ``!r:'a field. FiniteField r ==> (r =ff= (subset_field r (roots (master (char r ** (fdim r))))))``,
  metis_tac[poly_master_roots_subfield_iso_field, poly_master_roots_finite_field, field_iso_sym, finite_field_is_field]);

(* ------------------------------------------------------------------------- *)
(* Useful Results (for paper or proof investigation)                         *)
(* ------------------------------------------------------------------------- *)

(* The following is not that good:
   It only depends on FiniteField s, and monic_irreducibles_bounded_prod_set |> ISPEC ``s:'a field``
*)

(* Theorem: FiniteField r /\ s <<= r /\ 0 < n ==> (master (CARD B ** n) =
            poly_prod_image s (poly_prod_set s) (IMAGE (monic_irreducibles_degree s) (divisors n))) *)
(* Proof:
   Note FiniteField s                                  by subfield_finite_field
     master (CARD B ** n)
   = poly_prod_set s (monic_irreducibles_bounded s n)  by poly_master_subfield_factors_alt
   = poly_prod_image s (poly_prod_set s)
                       (IMAGE (monic_irreducibles_degree s) (divisors n))
                                                       by monic_irreducibles_bounded_prod_set
*)
val poly_master_subfield_eq_monic_irreducibles_prod_image = store_thm(
  "poly_master_subfield_eq_monic_irreducibles_prod_image",
  ``!(r s):'a field n. FiniteField r /\ s <<= r /\ 0 < n ==> (master (CARD B ** n) =
          poly_prod_image s (poly_prod_set s) (IMAGE (monic_irreducibles_degree s) (divisors n)))``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteField s` by metis_tac[subfield_finite_field] >>
  metis_tac[monic_irreducibles_bounded_prod_set, poly_master_subfield_factors_alt]);

(* Theorem: FiniteField r /\ s <<= r /\ 0 < n ==>
            (master (CARD B ** n) = poly_prod_set s {poly_psi s d | d IN divisors n}) *)
(* Proof: by poly_master_subfield_eq_monic_irreducibles_prod_image *)
val poly_master_subfield_eq_monic_irreducibles_prod_image_alt_1 = store_thm(
  "poly_master_subfield_eq_monic_irreducibles_prod_image_alt_1",
  ``!(r s):'a field n. FiniteField r /\ s <<= r /\ 0 < n ==>
          (master (CARD B ** n) = poly_prod_set s {poly_psi s d | d IN divisors n})``,
  rw[poly_master_subfield_eq_monic_irreducibles_prod_image] >>
  `IMAGE (poly_prod_set s) (IMAGE (monic_irreducibles_degree s) (divisors n)) = {poly_prod_set s (monic_irreducibles_degree s d) | d IN (divisors n)}` suffices_by rw[] >>
  rw[EXTENSION, EQ_IMP_THM] >| [
    qexists_tac `x''` >>
    `x' = monic_irreducibles_degree s x''` suffices_by rw[] >>
    rw[EXTENSION] >>
    metis_tac[],
    metis_tac[]
  ]);

(* Theorem: FiniteField r /\ s <<= r /\ 0 < n ==>
            (master (CARD B ** n) = poly_prod_set s {poly_psi s d | d divides n}) *)
(* Proof: by poly_master_subfield_eq_monic_irreducibles_prod_image *)
val poly_master_subfield_eq_monic_irreducibles_prod_image_alt_2 = store_thm(
  "poly_master_subfield_eq_monic_irreducibles_prod_image_alt_2",
  ``!(r s):'a field n. FiniteField r /\ s <<= r /\ 0 < n ==>
             (master (CARD B ** n) = poly_prod_set s {poly_psi s d | d divides n})``,
  rw[poly_master_subfield_eq_monic_irreducibles_prod_image] >>
  `IMAGE (poly_prod_set s) (IMAGE (monic_irreducibles_degree s) (divisors n)) = {poly_prod_set s (monic_irreducibles_degree s d) | d | d divides n}` suffices_by rw[] >>
  rw[EXTENSION, EQ_IMP_THM] >| [
    qexists_tac `x''` >>
    `x' = monic_irreducibles_degree s x''` suffices_by fs[divisors_def] >>
    rw[EXTENSION] >>
    metis_tac[],
    metis_tac[DIVIDES_LE, divisors_element_alt]
  ]);

(* Next is better than above. *)

(* Theorem: FiniteField r ==> !n. 0 < n ==>
    (master (CARD R ** n) = PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) (divisors n))) *)
(* Proof:
     master (CARD R ** n)
   = PPROD (monic_irreducibles_bounded r n)            by poly_master_monic_irreducible_factors
   = PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) (divisors n))
                                                       by monic_irreducibles_bounded_prod_set
*)
val poly_master_eq_monic_irreducibles_prod_image = store_thm(
  "poly_master_eq_monic_irreducibles_prod_image",
  ``!r:'a field. FiniteField r ==> !n. 0 < n ==>
    (master (CARD R ** n) = PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) (divisors n)))``,
  rw[poly_master_monic_irreducible_factors, monic_irreducibles_bounded_prod_set]);

(* Theorem: FiniteField r /\ 0 < n ==> (master (CARD R ** n) = PPROD {Psi d | d IN (divisors n)}) *)
(* Proof: by poly_master_eq_monic_irreducibles_prod_image *)
val poly_master_eq_monic_irreducibles_prod_image_alt_1 = store_thm(
  "poly_master_eq_monic_irreducibles_prod_image_alt_1",
  ``!(r:'a field) n. FiniteField r /\ 0 < n ==>
            (master (CARD R ** n) = PPROD {Psi d | d IN (divisors n)})``,
  rw[poly_master_eq_monic_irreducibles_prod_image] >>
  `IMAGE PPROD (IMAGE (monic_irreducibles_degree r) (divisors n)) = {PPROD (monic_irreducibles_degree r d) | d IN (divisors n)}` suffices_by rw[] >>
  rw[EXTENSION, EQ_IMP_THM] >| [
    qexists_tac `x''` >>
    `x' = monic_irreducibles_degree r x''` suffices_by rw[] >>
    rw[EXTENSION] >>
    metis_tac[],
    metis_tac[]
  ]);

(* Theorem: FiniteField r /\ 0 < n ==> (master (CARD R ** n) = PPROD {Psi d | d divides n}) *)
(* Proof: by poly_master_eq_monic_irreducibles_prod_image *)
val poly_master_eq_monic_irreducibles_prod_image_alt_2 = store_thm(
  "poly_master_eq_monic_irreducibles_prod_image_alt_2",
  ``!(r:'a field) n. FiniteField r /\ 0 < n ==> (master (CARD R ** n) = PPROD {Psi d | d divides n})``,
  rw[poly_master_eq_monic_irreducibles_prod_image] >>
  `IMAGE PPROD (IMAGE (monic_irreducibles_degree r) (divisors n)) = {PPROD (monic_irreducibles_degree r d) | d divides n}` suffices_by rw[] >>
  rw[EXTENSION, EQ_IMP_THM] >| [
    qexists_tac `x''` >>
    `x' = monic_irreducibles_degree r x''` suffices_by fs[divisors_def] >>
    rw[EXTENSION] >>
    metis_tac[],
    metis_tac[DIVIDES_LE, divisors_element_alt]
  ]);

(* ------------------------------------------------------------------------- *)
(* Monic Irreducible Products                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteRing r ==> !n. mset (IMAGE PPROD (IMAGE (monic_irreducibles_degree r) (natural n))) *)
(* Proof:
   Let f = monic_irreducibles_degree r, s = IMAGE PPROD (IMAGE f (natural n)).
   To show (mset s) is to show: !p. p IN s ==> monic p
   Note ?k. p = PPROD (f k)     by IN_IMAGE
   Note FINITE (f k)            by monic_irreducibles_degree_finite, FINITE R
    and mset (f k)              by monic_irreducibles_degree_member
    ==> monic (PPROD (f k))     by poly_monic_prod_set_monic
     or monic p                 by p = PPROD (f k)
*)
val monic_irreducibles_degree_prod_set_image_monic_set = store_thm(
  "monic_irreducibles_degree_prod_set_image_monic_set",
  ``!r:'a ring. FiniteRing r ==> !n. mset (IMAGE PPROD (IMAGE (monic_irreducibles_degree r) (natural n)))``,
  rpt (stripDup[FiniteRing_def]) >>
  qabbrev_tac `s = IMAGE PPROD (IMAGE (monic_irreducibles_degree r) (natural n))` >>
  `?k. p = PPROD (monic_irreducibles_degree r k)` by prove_tac[IN_IMAGE] >>
  `FINITE (monic_irreducibles_degree r k)` by rw[monic_irreducibles_degree_finite] >>
  `mset (monic_irreducibles_degree r k)` by metis_tac[monic_irreducibles_degree_member] >>
  rw[poly_monic_prod_set_monic]);

(* Theorem: FiniteRing r ==> !n. monic (PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) (natural n))) *)
(* Proof:
   Let f = monic_irreducibles_degree r, s = IMAGE PPROD (IMAGE f (natural n)).
   Note FINITE (natural n)             by natural_finite
    ==> FINITE (IMAGE f (natural n))   by IMAGE_FINITE
    ==> FINITE s                       by IMAGE_FINITE
   Note mset s                         by monic_irreducibles_degree_prod_set_image_monic_set
   Hence monic (PPROD s)               by poly_monic_prod_set_monic, mset s
*)
val monic_irreducibles_degree_prod_set_image_monic = store_thm(
  "monic_irreducibles_degree_prod_set_image_monic",
  ``!r:'a ring. FiniteRing r ==> !n. monic (PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) (natural n)))``,
  rpt (stripDup[FiniteRing_def]) >>
  qabbrev_tac `s = IMAGE PPROD (IMAGE (monic_irreducibles_degree r) (natural n))` >>
  `FINITE s` by rw[natural_finite, Abbr`s`] >>
  `mset s` by metis_tac[monic_irreducibles_degree_prod_set_image_monic_set] >>
  rw[poly_monic_prod_set_monic]);

(* Theorem: FiniteRing r ==> !n. poly (PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) (natural n))) *)
(* Proof: monic_irreducibles_degree_prod_set_image_monic, poly_monic_poly *)
val monic_irreducibles_degree_prod_set_image_poly = store_thm(
  "monic_irreducibles_degree_prod_set_image_poly",
  ``!r:'a ring. FiniteRing r ==> !n. poly (PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) (natural n)))``,
  rw_tac std_ss[monic_irreducibles_degree_prod_set_image_monic, poly_monic_poly]);

(* Theorem: FiniteRing r /\ #1 <> #0 ==>
           !n. PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) (natural n)) <> |0| *)
(* Proof: by monic_irreducibles_degree_prod_set_image_monic, poly_monic_nonzero *)
val monic_irreducibles_degree_prod_set_image_nonzero = store_thm(
  "monic_irreducibles_degree_prod_set_image_nonzero",
  ``!r:'a ring. FiniteRing r /\ #1 <> #0 ==>
   !n. PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) (natural n)) <> |0|``,
  rw_tac std_ss[monic_irreducibles_degree_prod_set_image_monic, poly_monic_nonzero]);

(* ------------------------------------------------------------------------- *)
(* Existence of Monic Irreducible by Master Polynomial                       *)
(* ------------------------------------------------------------------------- *)

(*
The Picture: Let s <<= r, both FiniteField s /\ FiniteField r.
             CARD R = (CARD B) ** d,   where d = r <:> s.

Note that    master (CARD R) = product of all monic irreducibles of degree k, k <= d, k divides d.
e.g. if d = 6,
            master (CARD R) = irreducibles of deg 1 *
                              irreducibles of deg 2 *
                              irreducibles of deg 3 *
                              irreducibles of deg 6

There are IPoly s p with deg 4, deg 5, deg 7, etc. but they are not included in master (CARD R).
However, by including all degrees from 1 to 6,
            master (CARD R) pdivides  PPROD (irreducibles of deg k) (1 to 6)

Now, if {irreducibles of deg 6} = {}, then
    PPROD (irreducibles of deg k) (1 to 6) = PPROD (irreducibles of deg k) (1 to 5) = q
Note that
    PPROD (ipoly of deg 1)  pdivides master (CARD B ** 1)  since it is PPROD ipoly deg (divisors of 1)
    PPROD (ipoly of deg 2)  pdivides master (CARD B ** 2)  since it is PPROD ipoly deg (divisors of 2)
    PPROD (ipoly of deg 3)  pdivides master (CARD B ** 3)  since it is PPROD ipoly deg (divisors of 3)
    ....
so  PPROD (irreducibles of deg k) (1 to 5) pdivides PPROD (master (CARD B ** k)) (1 to 5) = t.

Thus     master (CARD R) = master (CARD B ** d) pdivides q, and q pdivides t.
==>      CARD B ** d <= deg t,
However,
     deg t = sum of master degree
           = (CARD B) ** 1 + (CARD B) ** 2 + (CARD B) ** 3 + (CARD B) ** 4 + (CARD B) ** 5
           = ((CARD B) ** 6 - 1) / 5
           = ((CARD B) ** d - 1) / 5    d = 6
           < (CARD B) ** d,             which is impossible.

Another way to argue:
Let m = maximum degree of (subfield) irreducible in (big) field (CARD B) ** n,
        PPROD (ipoly of deg 1)  pdivides master (CARD B ** 1)
        PPROD (ipoly of deg 2)  pdivides master (CARD B ** 2)
...
        PPROD (ipoly of deg m)  pdivides master (CARD B ** m)
and no more for higher degree, since m is assumed maximum.
Hence,
       PPROD (PPROD (ipoly of degree k)) (1 to m)  pdivides PPROD (master (CARD B ** k)) (1 to m)
LHS is the product of all irreducibles, and PPROD (all irreducibles, each once) = master (CARD B ** n).
Thus    master (CARD B ** n)  pdivides PPROD (master (CARD B ** k)) (1 to m)
degree of LHS = a = CARD B ** n.
degree of RHS = b = CARD B ** 1 + CARD B ** 2 + ... + CARD B ** m
                  = [(CARD B) ** (m + 1) - 1] / [CARD B - 1]
                  < (CARD B) ** (m + 1) - 1    since 1 < CARD B.
For pdivides to hold, a <= b.
If m < n, then m + 1 <= n, b < CARD B ** n - 1
so a <= b implies CARD B ** n < CARD B ** n - 1, which is impossible.
Thus m = n, or there is an irreducible in the subfield of degree n.

*)

(* Theorem: FiniteField r ==> !n. Psi n pdivides (master (CARD R ** n)) *)
(* Proof:
   Let s = monic_irreducibles_degree r n, q = master (CARD R ** n).
   The goal is: PPROD s pdivides q.
   Note FINITE s                             by monic_irreducibles_degree_finite
    and pcoprime_set s                       by monic_irreducibles_degree_coprime_set
    and poly q                               by poly_master_poly
   Also !p. p IN s
    ==> monic p /\ ipoly p /\ (deg p = n)    by monic_irreducibles_degree_member
    ==> p pdivides q                         by poly_irreducible_divides_master
   Thus PPROD s pdivides q                   by poly_prod_coprime_set_divides
*)
val monic_irreducibles_degree_prod_set_divides_master = store_thm(
  "monic_irreducibles_degree_prod_set_divides_master",
  ``!r:'a field. FiniteField r ==>
   !n. Psi n pdivides (master (CARD R ** n))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `s = monic_irreducibles_degree r n` >>
  qabbrev_tac `q = master (CARD R ** n)` >>
  `FINITE s` by rw[monic_irreducibles_degree_finite, Abbr`s`] >>
  `pcoprime_set s` by rw[monic_irreducibles_degree_coprime_set, Abbr`s`] >>
  `poly q` by rw[Abbr`q`] >>
  `!p. p IN s ==> p pdivides q` by metis_tac[monic_irreducibles_degree_member, poly_irreducible_divides_master] >>
  rw[poly_prod_coprime_set_divides]);

(* Theorem: FiniteField r ==> !n. 0 < n ==>
            master (CARD R ** n) pdivides PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) (natural n)) *)
(* Proof:
   Let s = IMAGE PPROD (IMAGE (monic_irreducibles_degree r) (divisors n)),
       t = IMAGE PPROD (IMAGE (monic_irreducibles_degree r) (natural n)).
   By poly_master_eq_monic_irreducibles_prod_image, this is to show: PPROD s pdivides PPROD t

   Note FINITE (natural n)                by natural_finite
    ==> FINITE t                          by IMAGE_FINITE
   Note (divisors n) SUBSET (natural n)   by divisors_subset_natural
    ==> s SUBSET t                        by IMAGE_SUBSET
   Claim: pset t
   Proof: This is to show: poly (PPROD (monic_irreducibles_degree r (SUC x'')))
          Let u = monic_irreducibles_degree r (SUC x'').
          Note FINITE u                   by monic_irreducibles_degree_finite
           and pset u                     by monic_irreducibles_degree_poly_set
           ==> poly (PPROD u)             by poly_prod_set_poly

   Thus PPROD s pdivides PPROD t          by poly_prod_set_divides_prod_set, Claim
*)
val poly_master_divides_monic_irreducibles_degree_prod_set_image = store_thm(
  "poly_master_divides_monic_irreducibles_degree_prod_set_image",
  ``!r:'a field. FiniteField r ==> !n. 0 < n ==>
         master (CARD R ** n) pdivides PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) (natural n))``,
  rpt (stripDup[FiniteField_def]) >>
  rw[poly_master_eq_monic_irreducibles_prod_image] >>
  qabbrev_tac `s = IMAGE PPROD (IMAGE (monic_irreducibles_degree r) (divisors n))` >>
  qabbrev_tac `t = IMAGE PPROD (IMAGE (monic_irreducibles_degree r) (natural n))` >>
  `FINITE (natural n)` by rw[natural_finite] >>
  `FINITE t` by rw[Abbr`t`] >>
  `(divisors n) SUBSET (natural n)` by rw[divisors_subset_natural] >>
  `s SUBSET t` by rw[Abbr`s`, Abbr`t`] >>
  `pset t` by
  (rw[Abbr`t`] >>
  `FINITE (monic_irreducibles_degree r (SUC x''))` by rw[monic_irreducibles_degree_finite] >>
  `pset (monic_irreducibles_degree r (SUC x''))` by metis_tac[monic_irreducibles_degree_poly_set] >>
  rw[poly_prod_set_poly]) >>
  rw[poly_prod_set_divides_prod_set]);

(* Theorem: FiniteField r ==> !s. FINITE s ==>
            PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) s) pdivides
            PPIMAGE (\n. master (CARD R ** n)) s *)
(* Proof:
   Let f = \n. master (CARD R ** n), t = PPIMAGE f s.
       u = IMAGE PPROD (IMAGE (monic_irreducibles_degree r) s)
   The goal is to show: PPROD u pdivides t

   Step 1: properties of f and t
   Note FINITE (IMAGE f s)               by IMAGE_FINITE
    and pset (IMAGE f s)                 by IN_IMAGE, poly_master_poly
    ==> poly t                           by poly_prod_set_poly

   Step 2: properties of u
   Note FINITE u                         by IMAGE_FINITE
    and !n. FINITE (monic_irreducibles_degree r n)   by monic_irreducibles_degree_finite
    and !n. pset (monic_irreducibles_degree r n)     by monic_irreducibles_degree_poly_set
    ==> pset u                           by IN_IMAGE, poly_prod_set_poly
   Claim: pcoprime_set u
   Proof: By poly_coprime_set_def, this is to show:
             p IN u /\ q IN u /\ p <> q ==> pcomprime p q
          Note ?n. n IN s /\ (p = Psi n)                  by IN_IMAGE
           and ?m. m IN s /\ (q = Psi m)                  by IN_IMAGE
          Note miset (monic_irreducibles_degree r n)      by monic_irreducibles_degree_member
           and miset (monic_irreducibles_degree r m)      by monic_irreducibles_degree_member
           Now m <> n                                     by p <> q
          Thus DISJOINT (monic_irreducibles_degree r n)
                        (monic_irreducibles_degree r m)   by monic_irreducibles_degree_disjoint
           ==> pcomprime p q                              by poly_prod_monic_irreducible_set_coprime

   Step 3: assert p IN u ==> p pdivides t
   Claim: !p. p IN u ==> p pdivides t
   Proof: Note ?n. n IN s /\ (p = Psi n)           by IN_IMAGE
           and master (CARD R ** n) IN (IMAGE f s) by IN_IMAGE
           ==> master (CARD R ** n) pdivides t     by poly_prod_set_element_divides
           But p pdivides (master (CARD R ** n))   by monic_irreducibles_degree_prod_set_divides_master
           ==> p pdivides t                        by poly_divides_transitive

   Therefore PPROD u pdivides t                    by poly_prod_coprime_set_divides, claims.
*)
val monic_irreducibles_degree_prod_set_image_divides_master_image = store_thm(
  "monic_irreducibles_degree_prod_set_image_divides_master_image",
  ``!r:'a field. FiniteField r ==> !s. FINITE s ==>
   PPIMAGE PPROD (IMAGE (monic_irreducibles_degree r) s) pdivides PPIMAGE (\n. master (CARD R ** n)) s``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r` by rw[] >>
  qabbrev_tac `f = \n. master (CARD R ** n)` >>
  qabbrev_tac `t = PPIMAGE f s` >>
  qabbrev_tac `u = IMAGE PPROD (IMAGE (monic_irreducibles_degree r) s)` >>
  `!n. f n = master (CARD R ** n)` by rw[Abbr`f`] >>
  `FINITE (IMAGE f s)` by rw[] >>
  `pset (IMAGE f s)` by metis_tac[IN_IMAGE, poly_master_poly] >>
  `poly t` by metis_tac[poly_prod_set_poly] >>
  `FINITE u` by rw[Abbr`u`] >>
  `!n. FINITE (monic_irreducibles_degree r n)` by rw[monic_irreducibles_degree_finite] >>
  `!n. pset (monic_irreducibles_degree r n)` by metis_tac[monic_irreducibles_degree_poly_set] >>
  `pset u` by
  (rw_tac std_ss[Abbr`u`] >>
  metis_tac[IN_IMAGE, poly_prod_set_poly]) >>
  `pcoprime_set u` by
    (rw_tac std_ss[poly_coprime_set_def, Abbr`u`] >>
  `?n. n IN s /\ (p = Psi n)` by metis_tac[IN_IMAGE] >>
  `?m. m IN s /\ (q = Psi m)` by metis_tac[IN_IMAGE] >>
  `miset (monic_irreducibles_degree r n)` by rw[monic_irreducibles_degree_member] >>
  `miset (monic_irreducibles_degree r m)` by rw[monic_irreducibles_degree_member] >>
  `DISJOINT (monic_irreducibles_degree r n) (monic_irreducibles_degree r m)` by metis_tac[monic_irreducibles_degree_disjoint] >>
  rw[poly_prod_monic_irreducible_set_coprime]) >>
  `!p. p IN u ==> p pdivides t` by
      (rw_tac std_ss[Abbr`u`, Abbr`t`] >>
  `?n. n IN s /\ (p = Psi n)` by metis_tac[IN_IMAGE] >>
  `master (CARD R ** n) IN (IMAGE f s)` by metis_tac[IN_IMAGE] >>
  `p pdivides (master (CARD R ** n))` by rw[monic_irreducibles_degree_prod_set_divides_master] >>
  metis_tac[poly_prod_set_element_divides, poly_divides_transitive]) >>
  rw[poly_prod_coprime_set_divides]);

(* Theorem: FiniteField r ==> !n. 0 < n ==> ?p. monic p /\ ipoly p /\ (deg p = n) *)
(* Proof:
   By contradiction, suppose !p. monic p /\ ipoly p ==> deg p <> n.
   Let b = CARD R.
   Then 1 < b              by finite_field_card_gt_1
   Let m = n - 1,
   Then n = SUC m          by ADD1

   Let f = \k. master (b ** k), t = PPIMAGE f (natural m).
   Note 1 < b ** n                     by ONE_LT_EXP, 0 < n
    ==> monic (master (b ** n))        by poly_master_monic, 1 < b ** n
     so poly (master (b ** n))         by poly_monic_poly
   Note monic t                        by poly_master_prod_set_over_natural_monic
     so poly t /\ t <> |0|             by poly_monic_poly, poly_monic_nonzero

   Claim: master (b ** n) pdivides t
   Proof: Let g = monic_irreducibles_degree r, s = IMAGE PPROD (IMAGE g (natural m)).
          Then FINITE s                by natural_finite, IMAGE_FINITE
           and mset s                  by monic_irreducibles_degree_prod_set_image_monic_set
            so pset s                  by monic_set_poly_set
          Note master (b ** n) pdivides PPIMAGE PPROD (IMAGE g (natural (SUC m)))    ...(1)
                                       by poly_master_divides_monic_irreducibles_degree_prod_set_image, 0 < n
          Note that from contradiction hypothesis,
               g (SUC m) = {}          by monic_irreducibles_degree_member, MEMBER_NOT_EMPTY
               PPIMAGE PPROD (IMAGE g (natural (SUC m)))
             = PPROD (IMAGE PPROD (IMAGE g (natural (SUC m))))  by notation
             = PPROD (PPROD (g (SUC m)) INSERT s)        by natural_suc
             = PPROD (PPROD {}) INSERT s)                by above
             = PPROD ( |1| INSERT s)                      by poly_prod_set_empty
             = PPROD s                                   by poly_prod_set_with_one  ...(2)

          Note (PPROD s) pdivides t           by monic_irreducibles_degree_prod_set_image_divides_master_image
           and poly (PPROD s)                 by monic_irreducibles_degree_prod_set_image_poly
          Thus master (b ** n) pdivides t     by poly_divides_transitive, (1), (2), above.


  Next: compare degrees
  Note deg (master (b ** n)) = b ** n         by poly_master_deg, 1 < b ** n
   and deg t  = b * (b ** m - 1) DIV (b - 1)  by poly_master_prod_set_over_natural_deg
             <= b * (b ** m - 1)              by DIV_LESS_EQ
              = b * b ** m - b * 1            by LEFT_SUB_DISTRIB
              < b * b ** m                    by SUB_LESS
              = b ** n                        by EXP
   ==>  deg t < b ** n                        by above ... (3)
   But 0 < b ** n                             by EXP_POS, 0 < b
    so pmonic (master (b ** n))               by poly_monic_pmonic, 0 < b ** n
   ==> b ** n <= deg t                        by poly_field_divides_deg_le, t <> |0| ... (4)
   This contradicts deg t < b ** n            by (3), (4).
*)
val poly_monic_irreducible_exists_alt = store_thm(
  "poly_monic_irreducible_exists_alt",
  ``!r:'a field. FiniteField r ==> !n. 0 < n ==> ?p. monic p /\ ipoly p /\ (deg p = n)``,
  rpt (stripDup[FiniteField_def]) >>
  spose_not_then strip_assume_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `FiniteRing r` by metis_tac[FiniteRing_def] >>
  qabbrev_tac `b = CARD R` >>
  `1 < b` by rw[finite_field_card_gt_1, Abbr`b`] >>
  `n = SUC (n - 1)` by decide_tac >>
  qabbrev_tac `m = n - 1` >>
  qabbrev_tac `f = \k. master (b ** k)` >>
  qabbrev_tac `t = PPIMAGE f (natural m)` >>
  `!k. f k = master (b ** k)` by rw[Abbr`f`] >>
  `monic (master (b ** n))` by rw[poly_master_monic, ONE_LT_EXP] >>
  `poly (master (b ** n))` by rw[] >>
  `monic t` by rw[poly_master_prod_set_over_natural_monic, Abbr`t`, Abbr`f`, Abbr`b`] >>
  `poly t /\ t <> |0|` by metis_tac[poly_monic_poly, poly_monic_nonzero] >>
  `master (b ** n) pdivides t` by
  (qabbrev_tac `g = monic_irreducibles_degree r` >>
  qabbrev_tac `s = IMAGE PPROD (IMAGE g (natural m))` >>
  `master (b ** n) pdivides PPIMAGE PPROD (IMAGE g (natural (SUC m)))` by rw[poly_master_divides_monic_irreducibles_degree_prod_set_image, Abbr`b`, Abbr`g`] >>
  `PPIMAGE PPROD (IMAGE g (natural (SUC m))) = PPROD s` by
    (rw[natural_suc] >>
  `g (SUC m) = {}` by metis_tac[monic_irreducibles_degree_member, MEMBER_NOT_EMPTY] >>
  rw[poly_prod_set_empty] >>
  `FINITE s` by rw[natural_finite, Abbr`s`] >>
  `pset s` by metis_tac[monic_irreducibles_degree_prod_set_image_monic_set, monic_set_poly_set] >>
  rw[poly_prod_set_with_one]) >>
  `PPROD s pdivides t` by rw[monic_irreducibles_degree_prod_set_image_divides_master_image, Abbr`s`, Abbr`b`, Abbr`t`, Abbr`g`, Abbr`f`] >>
  `poly (PPROD s)` by rw[monic_irreducibles_degree_prod_set_image_poly, Abbr`s`, Abbr`g`] >>
  metis_tac[poly_divides_transitive]) >>
  `t = PPIMAGE (\k. master (b ** k)) (natural m)` by rw[Abbr`t`, Abbr`f`] >>
  `deg t = b * (b ** m - 1) DIV (b - 1)` by metis_tac[poly_master_prod_set_over_natural_deg] >>
  `deg t <= b * (b ** m - 1)` by rw[DIV_LESS_EQ] >>
  `b * (b ** m - 1) < b * b ** m` by rw[] >>
  `b * b ** m = b ** n` by metis_tac[EXP] >>
  `deg t < b ** n` by decide_tac >>
  `deg (master (b ** n)) = b ** n` by rw[poly_master_deg, ONE_LT_EXP] >>
  `pmonic (master (b ** n))` by rw[poly_monic_pmonic] >>
  `b ** n <= deg t` by metis_tac[poly_field_divides_deg_le] >>
  decide_tac);

(* Another proof of the existence of irreducible of a given degree, Yes! *)

(* poly_monic_irreducible_exists_alt:
   This proof is based on the fact that the master polynomial is the product of all monic irreducibles.
   Compare with the more advanced proof in ffExist: (poly_monic_irreducible_exists)
   That proof depends on counting the number of monic irreducibles.

   Used in ffConjugate: poly_unity_mod_exp_char_equal, as that script cannot use ffExist.
*)

(* ------------------------------------------------------------------------- *)
(* Finite Field Subgroup and Master Polynomial                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r /\ g <= f* ==> (roots (master (CARD G + 1)) = G UNION {#0}) *)
(* Proof:
   Let n = CARD G + 1, then 0 < n   by SUC_POS, ADD1
   Note FiniteGroup g               by field_subgroup_finite_group
     so FINITE G                    by FiniteGroup_def

   Claim: G UNION {#0} SUBSET roots (master n)
   Proof: By SUBSET_DEF, IN_UNION, IN_SING, this is to show:
   (1) x IN G ==> x IN roots (master n)
       Note x IN R                  by field_subgroup_element
         so x ** (CARD G) = #1      by finite_group_Fermat, field_subgroup_exp
            x ** n
          = x ** (SUC (CARD G))     by ADD1
          = x ** x ** (CARD G)      by field_exp_SUC
          = x ** #1                 by above
          = x                       by field_mult_rone
      Hence root (master n) x       by poly_master_root
         or x IN roots (master n)   by poly_roots_member
   (2) #0 IN roots (master n), true by poly_master_root_zero, 0 < n

   Now 0 < CARD G                   by finite_group_card_pos
    so 1 < n, or n <> 1, or 1 < n   by arithmetic
  Note poly (master n)              by poly_master_poly
   and master n <> |0|              by poly_master_eq_zero, n <> 1
   ==> FINITE (roots (master n))                        by poly_roots_finite
   ==> CARD (roots (master n)) <= deg (master n)        by poly_roots_count
    or CARD (roots (master n)) <= n                     by poly_master_deg, 1 < n

  Note G UNION {#0} SUBSET roots (master n)             by Claim
    so CARD (G UNION {#0}) <= CARD (roots (master n))   by CARD_SUBSET
   and CARD (G UNION {#0}) = n                          by field_subgroup_card
  Thus CARD (roots (master n)) = n                      by above
    or roots (master (CARD G + 1)) = G UNION {#0}       by SUBSET_EQ_CARD
*)
val field_subgroup_master_roots = store_thm(
  "field_subgroup_master_roots",
  ``!(r:'a field) (g:'a group). FiniteField r /\ g <= f* ==> (roots (master (CARD G + 1)) = G UNION {#0})``,
  rpt (stripDup[FiniteField_def, Subgroup_def]) >>
  `FINITE G /\ FiniteGroup g` by metis_tac[FiniteGroup_def, field_subgroup_finite_group] >>
  `0 < CARD G` by rw[finite_group_card_pos] >>
  `0 < CARD G + 1 /\ 1 < CARD G + 1 /\ CARD G + 1 <> 1` by decide_tac >>
  qabbrev_tac `n = CARD G + 1` >>
  `G UNION {#0} SUBSET roots (master n)` by
  (rw_tac std_ss[SUBSET_DEF, IN_UNION, IN_SING] >| [
    `x ** (CARD G) = #1` by metis_tac[finite_group_Fermat, field_subgroup_exp, field_subgroup_id] >>
    `x IN R` by metis_tac[field_subgroup_element] >>
    `x ** n = x ** (SUC (CARD G))` by rw_tac std_ss[ADD1, Abbr`n`] >>
    `_ = x` by rw[field_exp_SUC] >>
    rw[poly_master_root, poly_roots_member],
    rw[poly_master_root_zero, poly_roots_member]
  ]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `poly (master n) /\ master n <> |0|` by rw[poly_master_eq_zero] >>
  `FINITE (roots (master n))` by rw[poly_roots_finite] >>
  `CARD (roots (master n)) <= n ` by metis_tac[poly_roots_count, poly_master_deg] >>
  `CARD (G UNION {#0}) = n` by rw[field_subgroup_card, Abbr`n`] >>
  `CARD (G UNION {#0}) <= CARD (roots (master n))` by rw[CARD_SUBSET] >>
  `CARD (roots (master n)) = n` by decide_tac >>
  rw[SUBSET_EQ_CARD]);

(* This is the key theorem to show that g <= f* eventually guarantees additive closure. *)

(* ------------------------------------------------------------------------- *)
(* Finite Field Subgroup Field                                               *)
(* ------------------------------------------------------------------------- *)

(* Note:
   A subset_field, defined in fieldMap for sub-structures,
   takes a subset s of field elements to form a field.
   However, it is hard to ensure closure for addition and multiplication.

   Here we study subgroup_field: take g <= f* to form a field.
   This guarantees closure of multiplication.
   The closure of addition depends on the roots of the Master polynomial.
   see: subgroup_field_element_iff_master_root.
*)

(* Define the subgroup field: takes a multiplicative group and gives a field candidate *)
val subgroup_field_def = Define`
    subgroup_field (r:'a field) (g:'a group) =
    <| carrier := G UNION {#0};
           sum := <| carrier := G UNION {#0}; op := r.sum.op; id := #0 |>;
          prod := g including #0
     |>
`;

(* Theorem: properties of subgroup_field *)
(* Proof: by subgroup_field_def, including_def *)
val subgroup_field_property = store_thm(
  "subgroup_field_property",
  ``!(r:'a field) (g:'a group).
     ((subgroup_field r g).carrier = G UNION {#0}) /\
     ((subgroup_field r g).sum.carrier = G UNION {#0}) /\
     ((subgroup_field r g).prod.carrier = G UNION {#0}) /\
     ((subgroup_field r g).sum.op = r.sum.op) /\
     ((subgroup_field r g).sum.id = #0)``,
  rw_tac std_ss[subgroup_field_def, including_def]);

(* Theorem: ((subgroup_field r g).sum.op = r.sum.op) /\ ((subgroup_field r g).sum.id = #0) *)
(* Proof: by subgroup_field_property *)
val subgroup_field_sum_property = store_thm(
  "subgroup_field_sum_property",
  ``!(r:'a field) (g:'a group). ((subgroup_field r g).sum.op = r.sum.op) /\ ((subgroup_field r g).sum.id = #0)``,
  rw[subgroup_field_property]);

(* Theorem: Field r /\ g <= f* ==>
    ((subgroup_field r g).prod.op = r.prod.op) /\ ((subgroup_field r g).prod.id = #1) *)
(* Proof:
   This is to show:
   (1) (subgroup_field r g).prod.op = r.prod.op
        (subgroup_field r g).prod.op
      = (g including #0).op          by subgroup_field_def
      = g.op                         by including_def
      = f*.op                        by Subgroup_def, g <= f*
      = r.prod.op                    by field_nonzero_mult_property
   (2) (subgroup_field r g).prod.id = #1
        (subgroup_field r g).prod.id
      = (g including #0).id          by subgroup_field_def
      = g.id                         by including_def
      = f*.id                        by subgroup_id
      = #1                           by field_nonzero_mult_property
*)
val subgroup_field_prod_property = store_thm(
  "subgroup_field_prod_property",
  ``!(r:'a field) (g:'a group). Field r /\ g <= f* ==>
     ((subgroup_field r g).prod.op = r.prod.op) /\ ((subgroup_field r g).prod.id = #1)``,
  ntac 3 strip_tac >>
  `g.op = r.prod.op` by fs[Subgroup_def] >>
  `g.id = #1` by metis_tac[subgroup_id, field_nonzero_mult_property] >>
  rw_tac std_ss[subgroup_field_def, including_def]);

(* Theorem: Field r /\ g <= f* ==>
            ((subgroup_field r g).sum.id = #0) /\ ((subgroup_field r g).prod.id = #1) *)
(* Proof: by subgroup_field_sum_property, subgroup_field_prod_property *)
val subgroup_field_ids = store_thm(
  "subgroup_field_ids",
  ``!(r:'a field) (g:'a group). Field r /\ g <= f* ==>
     ((subgroup_field r g).sum.id = #0) /\ ((subgroup_field r g).prod.id = #1)``,
  rw_tac std_ss[subgroup_field_sum_property, subgroup_field_prod_property]);

(* Theorem: FiniteGroup g /\ #0 NOTIN G ==> (CARD (subgroup_field r g).carrier = CARD G + 1) *)
(* Proof:
   Note FINITE G     by FiniteGroup_def
    and (subgroup_field r g).carrier = G UNION {#0}    by subgroup_field_property
    but G INTER {#0} = {}                              by IN_INTER, IN_SING, MEMBER_NOT_EMPTY
        CARD (subgroup_field r g).carrier
      = CARD (G UNION {#0})
      = CARD G + CARD {#0} - CARD (G INTER {#0})       by CARD_UNION_EQN, FINITE_SING
      = CARD G + 1 - 0 = CARD G + 1                    by CARD_SING
*)
val subgroup_field_card = store_thm(
  "subgroup_field_card",
  ``!(r:'a field) g. FiniteGroup g /\ #0 NOTIN G ==> (CARD (subgroup_field r g).carrier = CARD G + 1)``,
  rpt (stripDup[FiniteGroup_def]) >>
  `(subgroup_field r g).carrier = G UNION {#0}` by rw[subgroup_field_property] >>
  `G INTER {#0} = {}` by metis_tac[IN_INTER, IN_SING, MEMBER_NOT_EMPTY] >>
  rw[CARD_UNION_EQN]);

(* Theorem: Field r /\ g <= f* ==> #0 IN G UNION {#0} /\ #1 IN G UNION {#0} *)
(* Proof:
   Note #1 IN G                       by field_subgroup_property
    ==> #1 IN G UNION {#0}            by IN_UNION
    and #0 IN G UNION {#0}            by IN_UNION, IN_SING
*)
val subgroup_field_has_ids = store_thm(
  "subgroup_field_has_ids",
  ``!(r:'a field) (g:'a group). Field r /\ g <= f* ==> #0 IN G UNION {#0} /\ #1 IN G UNION {#0}``,
  ntac 3 strip_tac >>
  metis_tac[field_subgroup_property, IN_UNION, IN_SING]);

(* Theorem: Field r /\ g <= f* ==> !x. x IN G UNION {#0} ==> x IN R *)
(* Proof:
   Note x IN G UNION {#0}
    ==> x IN G \/ (x = #0)    by IN_UNION, IN_SING
   If x IN G, x IN R          by field_subgroup_element
   If x = #0, #0 IN R         by field_zero_element
*)
val subgroup_field_element = store_thm(
  "subgroup_field_element",
  ``!(r:'a field) (g:'a group). Field r /\ g <= f* ==> !x. x IN G UNION {#0} ==> x IN R``,
  metis_tac[IN_UNION, IN_SING, field_zero_element, field_subgroup_element]);

(* Theorem: Field r /\ g <= f* ==> !x y. x IN G UNION {#0} /\ y IN G UNION {#0} ==> x * y IN G UNION {#0} *)
(* Proof:
   By IN_UNION, IN_SING, field_mult_lzero, field_mult_rzero, this is to show:
   (1) x IN G /\ y IN G ==> x * y IN G
       Note g <= f* ==> Group g   by Subgroup_def
       This is true               by group_op_element
*)
val subgroup_field_mult_element = store_thm(
  "subgroup_field_mult_element",
  ``!(r:'a field) (g:'a group). Field r /\ g <= f* ==>
   !x y. x IN G UNION {#0} /\ y IN G UNION {#0} ==> x * y IN G UNION {#0}``,
  rpt (stripDup[Subgroup_def]) >>
  `!x. x IN G ==> x IN R+` by metis_tac[SUBSET_DEF, field_mult_carrier] >>
  `!x. x IN R+ <=> x IN R /\ x <> #0` by rw[field_nonzero_eq] >>
  fs[] >>
  metis_tac[group_op_element]);

(* Theorem: Field r /\ g <= f* ==> !x. x IN G UNION {#0} ==> !n. x ** n IN G UNION {#0} *)
(* Proof:
   By IN_UNION, IN_SING, field_mult_lzero, field_mult_rzero, this is to show:
   (1) x IN G ==> x ** n IN G
       Note g <= f* ==> Group g   by Subgroup_def
       Thus g.exp x n IN G        by group_exp_element
            g.exp x n
          = f*.exp x n            by subgroup_exp
          = x ** n                by field_nonzero_mult_property
   (2) #0 ** n IN G \/ (#0 ** n = #0)
       If n = 0, #0 ** 0 = #1     by field_zero_exp
                 and #1 IN G      by field_subgroup_property
       If n <> 0, #0 ** n = #0    by field_zero_exp
*)
val subgroup_field_exp_element = store_thm(
  "subgroup_field_exp_element",
  ``!(r:'a field) (g:'a group). Field r /\ g <= f* ==>
   !x. x IN G UNION {#0} ==> !n. x ** n IN G UNION {#0}``,
  rpt (stripDup[Subgroup_def]) >>
  `!x. x IN G ==> x IN R+` by metis_tac[SUBSET_DEF, field_mult_carrier] >>
  `!x. x IN R+ <=> x IN R /\ x <> #0` by rw[field_nonzero_eq] >>
  fs[] >-
  metis_tac[group_exp_element, subgroup_exp, field_nonzero_mult_property] >>
  rw[field_zero_exp, field_subgroup_property]);

(* Theorem: Field r /\ g <= f* ==> !x. x IN G ==> |/ x IN G *)
(* Proof:
   Note g <= f* ==> Group g         by Subgroup_def
     so x IN G ==> g.inv x IN G     by group_inv_element
    and g.inv x = |/ x              by field_subgroup_inv
   Hence |/ x IN G.
*)
val subgroup_field_inv_element = store_thm(
  "subgroup_field_inv_element",
  ``!(r:'a field) (g:'a group). Field r /\ g <= f* ==> !x. x IN G ==> |/ x IN G``,
  metis_tac[Subgroup_def, field_subgroup_inv, group_inv_element]);

(* ------------------------------------------------------------------------- *)
(* Subgroup Field Additive Closure                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r /\ g <= f* ==>
            !x. x IN G UNION {#0} <=> x IN R /\ (x ** (CARD G + 1) = x) *)
(* Proof:
   Let n = CARD G + 1.
       x IN G UNION {#0}
   <=> x IN roots (master n)           by field_subgroup_master_roots
   <=> x IN R /\ root (master n) x     by poly_roots_member
   <=> x IN R /\ (x ** n = x)          by poly_master_root
*)
val subgroup_field_element_iff_master_root = store_thm(
  "subgroup_field_element_iff_master_root",
  ``!(r:'a field) (g:'a group). FiniteField r /\ g <= f* ==>
   !x. x IN G UNION {#0} <=> x IN R /\ (x ** (CARD G + 1) = x)``,
  metis_tac[field_subgroup_master_roots, poly_roots_member, poly_master_root, finite_field_is_field, field_is_ring]);

(* This is the more accessible form of field_subgroup_master_roots,
   the key to show that (subgroup_field r g).sum has additive closure.
*)

(* Theorem: FiniteField r /\ g <= f* ==> !n. (CARD G = (char r) ** n - 1) ==>
            !x y. x IN G UNION {#0} /\ y IN G UNION {#0} ==> x + y IN G UNION {#0} *)
(* Proof:
   Note FiniteGroup g                by field_subgroup_finite_group
     so 0 < CARD G                   by finite_group_card_pos, FiniteGroup g
    ==> (char r) ** n = CARD G + 1   by arithmetic, 0 < CARD G

    Now x IN R /\ y IN R             by subgroup_field_element
     so x + y IN R                   by field_add_element

    Let m = (char r) ** n.
        (x + y) ** m
      = x ** m + y ** m              by finite_field_freshman_all
      = x + y                        by subgroup_field_element_iff_master_root
   Thus x + y IN G UNION {#0}        by subgroup_field_element_iff_master_root
*)
val subgroup_field_add_element = store_thm(
  "subgroup_field_add_element",
  ``!(r:'a field) (g:'a group). FiniteField r /\ g <= f* ==> !n. (CARD G = (char r) ** n - 1) ==>
   !x y. x IN G UNION {#0} /\ y IN G UNION {#0} ==> x + y IN G UNION {#0}``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteGroup g` by metis_tac[field_subgroup_finite_group] >>
  `0 < CARD G` by rw[finite_group_card_pos] >>
  `(char r) ** n = CARD G + 1` by decide_tac >>
  `x IN R /\ y IN R` by metis_tac[subgroup_field_element] >>
  `x + y IN R` by rw[] >>
  metis_tac[finite_field_freshman_all, subgroup_field_element_iff_master_root]);

(* Theorem: FiniteField r /\ g <= f* ==> !n. (CARD G = (char r) ** n - 1) ==>
            !x y. x IN G UNION {#0} /\ y IN G UNION {#0} ==> x - y IN G UNION {#0} *)
(* Proof:
   Note FiniteGroup g                by field_subgroup_finite_group
     so 0 < CARD G                   by finite_group_card_pos, FiniteGroup g
    ==> (char r) ** n = CARD G + 1   by arithmetic, 0 < CARD G

    Now x IN R /\ y IN R             by subgroup_field_element
     so x - y IN R                   by field_sub_element

    Let m = (char r) ** n.
        (x - y) ** m
      = x ** m - y ** m              by finite_field_freshman_all_sub
      = x - y                        by subgroup_field_element_iff_master_root
   Thus x - y IN G UNION {#0}        by subgroup_field_element_iff_master_root
*)
val subgroup_field_sub_element = store_thm(
  "subgroup_field_sub_element",
  ``!(r:'a field) (g:'a group). FiniteField r /\ g <= f* ==> !n. (CARD G = (char r) ** n - 1) ==>
   !x y. x IN G UNION {#0} /\ y IN G UNION {#0} ==> x - y IN G UNION {#0}``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteGroup g` by metis_tac[field_subgroup_finite_group] >>
  `0 < CARD G` by rw[finite_group_card_pos] >>
  `(char r) ** n = CARD G + 1` by decide_tac >>
  `x IN R /\ y IN R` by metis_tac[subgroup_field_element] >>
  `x - y IN R` by rw[] >>
  metis_tac[finite_field_freshman_all_sub, subgroup_field_element_iff_master_root]);

(* Theorem: FiniteField r /\ g <= f* ==> !n. (CARD G = (char r) ** n - 1) ==>
            !x. x IN G UNION {#0} ==> -x IN G UNION {#0} *)
(* Proof:
   Note x IN R                       by subgroup_field_element
     so -x IN R                      by field_neg_element
   Also #0 IN G UNION {#0}           by IN_UNION, IN_SING
    and #0 - x = -x                  by field_zero_sub
   Since #0 - x IN G                 by subgroup_field_sub_element
      so -x IN G                     by above
*)
val subgroup_field_neg_element = store_thm(
  "subgroup_field_neg_element",
  ``!(r:'a field) (g:'a group). FiniteField r /\ g <= f* ==> !n. (CARD G = (char r) ** n - 1) ==>
   !x. x IN G UNION {#0} ==> -x IN G UNION {#0}``,
  rpt (stripDup[FiniteField_def]) >>
  `x IN R` by metis_tac[subgroup_field_element] >>
  `-x IN R` by rw[] >>
  `#0 IN G UNION {#0} /\ (-x = #0 - x)` by rw[] >>
  metis_tac[subgroup_field_sub_element]);

(* ------------------------------------------------------------------------- *)
(* Subgroup Field Properties                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r /\ g <= f* ==> AbelianMonoid (subgroup_field r g).prod *)
(* Proof:
   Note g <= f*
    ==> Group g /\ G SUBSET F*                 by Subgroup_def
   Thus !x. x IN G ==> x IN R+                 by SUBSET_DEF, field_mult_carrier
   Also !x. x IN R+ <=> x IN R /\ x <> #0      by field_nonzero_eq
   By AbelianMonoid_def, Monoid_def, subgroup_field_property, subgroup_field_prod_property, this is to show:
   (1) x IN G UNION {#0} /\ y IN G UNION {#0} ==> x * y IN G UNION {#0}
       This is true                            by subgroup_field_mult_element
   (2) x IN G UNION {#0} /\ y IN G UNION {#0} /\ z IN G UNION {#0} ==> x * y * z = x * (y * z)
       By IN_UNION, IN_SING, field_mult_lzero, field_mult_rzero, only need to show:
       x IN G /\ y IN G /\ z IN G ==> x * y * z = x * (y * z), true by group_assoc
   (3) #1 IN G UNION {#0}, true                by field_subgroup_property
   (4) x IN G UNION {#0} ==> #1 * x = x, true  by field_mult_lone
   (5) x IN G UNION {#0} ==> x * #1 = x, true  by field_mult_rone
   (6) x IN G UNION {#0} /\ y IN G UNION {#0} ==> x * y = y * x
       By IN_UNION, IN_SING, field_mult_lzero, field_mult_rzero, only need to show:
       x IN G /\ y IN G ==> x * y IN G
       Note AbelianGroup f*                    by field_subgroup_abelian_group
       Hence x IN G /\ y IN G ==> x * y IN G   by AbelianGroup_def
*)
val subgroup_field_prod_abelian_monoid = store_thm(
  "subgroup_field_prod_abelian_monoid",
  ``!(r:'a field) (g:'a group). Field r /\ g <= f* ==> AbelianMonoid (subgroup_field r g).prod``,
  rpt (stripDup[Subgroup_def]) >>
  `!x. x IN G ==> x IN R+` by metis_tac[SUBSET_DEF, field_mult_carrier] >>
  `!x. x IN R+ <=> x IN R /\ x <> #0` by rw[field_nonzero_eq] >>
  rw_tac std_ss[AbelianMonoid_def, Monoid_def, subgroup_field_property, subgroup_field_prod_property] >-
  rw[subgroup_field_mult_element] >-
 (fs[] >>
  metis_tac[group_assoc]) >-
  rw[field_subgroup_property] >-
  fs[] >-
  fs[] >>
  fs[] >>
  metis_tac[field_subgroup_abelian_group, AbelianGroup_def]);

(* Theorem: Field r /\ g <= f* ==> Monoid (subgroup_field r g).prod *)
(* Proof: by subgroup_field_prod_abelian_monoid, AbelianMonoid_def *)
val subgroup_field_prod_monoid = store_thm(
  "subgroup_field_prod_monoid",
  ``!(r:'a field) (g:'a group). Field r /\ g <= f* ==> Monoid (subgroup_field r g).prod``,
  metis_tac[subgroup_field_prod_abelian_monoid, AbelianMonoid_def]);

(* Theorem: FiniteField r /\ g <= f* ==>
            !n. (CARD G = (char r) ** n - 1) ==> AbelianGroup (subgroup_field r g).sum *)
(* Proof:
   Note g <= f*
    ==> Group g /\ G SUBSET F*                 by Subgroup_def
   Thus !x. x IN G ==> x IN R+                 by SUBSET_DEF, field_mult_carrier
   Also !x. x IN R+ <=> x IN R /\ x <> #0      by field_nonzero_eq
   By AbelianGroup_def, group_def_alt, subgroup_field_property, this is to show:
   (1) x IN G UNION {#0} /\ y IN G UNION {#0} ==> x + y IN G UNION {#0}
       This is true                            by subgroup_field_add_element
   (2) x IN G UNION {#0} /\ y IN G UNION {#0} /\ z IN G UNION {#0} ==> x + y + z = x + (y + z)
       Since x IN R /\ y IN R /\ z IN R        by subgroup_field_element
       Hence x + y + z = x + (y + z)           by field_add_assoc
   (3) #0 IN G UNION {#0}, true                by subgroup_field_has_ids
   (4) x IN G UNION {#0} ==> #0 + x = x
       Since x IN R                            by subgroup_field_element
       Hence #0 + x = x                        by field_add_lzero
   (5) x IN G UNION {#0} ==> ?y. y IN G UNION {#0} /\ (y + x = #0)
       Let y = -x,
       Then -x IN G UNION {#0}                 by subgroup_field_neg_element
        and -x + x = #0                        by field_add_lneg
   (6) x IN G UNION {#0} /\ y IN G UNION {#0} ==> x + y = y + x
       Since x IN R /\ y IN R                  by subgroup_field_element
       Hence x + y + z = x + (y + z)           by field_add_comm
*)
val subgroup_field_sum_abelian_group = store_thm(
  "subgroup_field_sum_abelian_group",
  ``!(r:'a field) (g:'a group). FiniteField r /\ g <= f* ==>
   !n. (CARD G = (char r) ** n - 1) ==> AbelianGroup (subgroup_field r g).sum``,
  rpt (stripDup[FiniteField_def, Subgroup_def]) >>
  `!x. x IN G ==> x IN R+` by metis_tac[SUBSET_DEF, field_mult_carrier] >>
  `!x. x IN R+ <=> x IN R /\ x <> #0` by rw[field_nonzero_eq] >>
  rw_tac std_ss[AbelianGroup_def, group_def_alt, subgroup_field_property] >-
  metis_tac[subgroup_field_add_element] >-
  metis_tac[field_add_assoc, subgroup_field_element] >-
  rw[] >-
  fs[] >-
  metis_tac[subgroup_field_neg_element, field_add_lneg, subgroup_field_element] >>
  metis_tac[field_add_comm, subgroup_field_element]);

(* Theorem: FiniteField r /\ g <= f* ==>
            !n. (CARD G = (char r) ** n - 1) ==> Group (subgroup_field r g).sum *)
(* Proof: by subgroup_field_sum_abelian_group, AbelianGroup_def *)
val subgroup_field_sum_group = store_thm(
  "subgroup_field_sum_group",
  ``!(r:'a field) (g:'a group). FiniteField r /\ g <= f* ==>
   !n. (CARD G = (char r) ** n - 1) ==> Group (subgroup_field r g).sum``,
  metis_tac[subgroup_field_sum_abelian_group, AbelianGroup_def]);

(* Theorem: FiniteField r /\ g <= f* ==>
            !n. (CARD G = (char r) ** n - 1) ==> Ring (subgroup_field r g) *)
(* Proof:
   By Ring_def, subgroup_field_property, subgroup_field_prod_property, this is to show:
   (1) AbelianGroup (subgroup_field r g).sum, true    by subgroup_field_sum_abelian_group
   (2) AbelianMonoid (subgroup_field r g).prod, true  by subgroup_field_prod_abelian_monoid
   (3) x IN G UNION {#0} /\ y IN G UNION {#0} /\ z IN G UNION {#0} ==> x * (y + z) = x * y + x * z
       Since x IN R /\ y IN R /\ z IN R               by subgroup_field_element
       Hence x * (y + z) = x * y + x * z              by field_mult_radd
*)
val subgroup_field_ring = store_thm(
  "subgroup_field_ring",
  ``!(r:'a field) (g:'a group). FiniteField r /\ g <= f* ==>
   !n. (CARD G = (char r) ** n - 1) ==> Ring (subgroup_field r g)``,
  rpt (stripDup[FiniteField_def]) >>
  rw_tac std_ss[Ring_def, subgroup_field_property, subgroup_field_prod_property] >-
  metis_tac[subgroup_field_sum_abelian_group] >-
  rw[subgroup_field_prod_abelian_monoid] >>
  metis_tac[field_mult_radd, subgroup_field_element]);

(* Theorem: FiniteField r /\ g <= f* ==>
            !n. (CARD G = (char r) ** n - 1) ==> Field (subgroup_field r g) *)
(* Proof:
   By field_def_by_inv, subgroup_field_property, subgroup_field_prod_property, this is to show:
   (1) Ring (subgroup_field r g), true         by subgroup_field_ring
   (2) #1 <> #0, true                          by field_one_ne_zero
   (3) x IN G UNION {#0} /\ x <> #0 ==> ?y. y IN G UNION {#0} /\ (x * y = #1)
       Note x IN G                             by IN_UNION, IN_SING, x <> #0
         so |/ x IN G                          by subgroup_field_inv_element
       Also x IN R+                            by field_subgroup_property, SUBSET_DEF
         so x * |/ x = #1                      by field_mult_rinv
       Take y = |/ x, then y IN G UNION {#0}   by IN_UNION
*)
val subgroup_field_field = store_thm(
  "subgroup_field_field",
  ``!(r:'a field) (g:'a group). FiniteField r /\ g <= f* ==>
   !n. (CARD G = (char r) ** n - 1) ==> Field (subgroup_field r g)``,
  rpt (stripDup[FiniteField_def]) >>
  rw_tac std_ss[field_def_by_inv, subgroup_field_property, subgroup_field_prod_property] >-
  metis_tac[subgroup_field_ring] >-
  rw[] >>
  `x IN G` by metis_tac[IN_UNION, IN_SING] >>
  `x IN R+` by metis_tac[field_subgroup_property, SUBSET_DEF] >>
  metis_tac[subgroup_field_inv_element, field_mult_rinv, IN_UNION]);

(* Theorem: Field r /\ g <= f* ==> subfield (subgroup_field r g) r *)
(* Proof:
   By subfield_def, FieldHomo_def, RingHomo_def, subgroup_field_property, this is to show:
   (1) x IN G UNION {#0} ==> x IN R, true          by subgroup_field_element
   (2) GroupHomo I (subgroup_field r g).sum r.sum
       By GroupHomo_def, subgroup_field_property, field_carriers, this is to show:
       (1) x IN G UNION {#0} ==> x IN R, true      by subgroup_field_element
       (2) x IN G UNION {#0} /\ y IN G UNION {#0} ==> (subgroup_field r g).sum.op x y = x + y
           This is true                            by subgroup_field_property
   (3) MonoidHomo I (subgroup_field r g).prod r.prod
       By MonoidHomo_def, subgroup_field_property, subgroup_field_prod_property, field_carriers, this is to show:
       (1) x IN G UNION {#0} ==> x IN R, true      by subgroup_field_element
       (2) x IN G UNION {#0} /\ y IN G UNION {#0} ==> (subgroup_field r g).prod.op x y = x * y
           This is true                            by subgroup_field_prod_property
       (3) (subgroup_field r g).prod.id = #1, true by subgroup_field_prod_property
*)
val subgroup_field_subfield = store_thm(
  "subgroup_field_subfield",
  ``!(r:'a field) (g:'a group). Field r /\ g <= f* ==> subfield (subgroup_field r g) r``,
  rw_tac std_ss[subfield_def, FieldHomo_def, RingHomo_def, subgroup_field_property] >-
  metis_tac[subgroup_field_element] >-
 (rw_tac std_ss[GroupHomo_def, subgroup_field_property, field_carriers] >>
  metis_tac[subgroup_field_element]) >>
  rw_tac std_ss[MonoidHomo_def, subgroup_field_property, subgroup_field_prod_property, field_carriers] >>
  metis_tac[subgroup_field_element]);

(* ------------------------------------------------------------------------- *)
(* Subfield Classification                                                   *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Subfield Classification - by subgroup                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r /\ s <<= r ==> ?g. g <= f* /\ (CARD G = (char r) ** (fdim s) - 1) *)
(* Proof:
   Note FiniteField s                 by subfield_finite_field
    ==> CARD B = char s ** fdim s     by finite_field_card_alt
               = char r ** fdim s     by subfield_char
   Also FINITE B                      by subfield_carrier_finite
    and #0 IN B                       by subfield_ids, field_zero_element
    ==> B INTER {#0} = {#0}           by INTER_SING

   Let g = subset_group f* (s.prod.carrier DIFF {#0}).
   Then g <= f*                       by subfield_mult_subset_group_subgroup
        CARD G
      = CARD (B DIFF {#0})            by subset_group_property
      = CARD B - CARD (B INTER {#0})  by CARD_DIFF_EQN, FINITE
      = CARD B - CARD {#0}            by above
      = CARD B - 1                    by CARD_SING
   Take this g, and the result follows.
*)
val finite_field_subfield_gives_subgroup = store_thm(
  "finite_field_subfield_gives_subgroup",
  ``!(r:'a field) s. FiniteField r /\ s <<= r ==> ?g. g <= f* /\ (CARD G = (char r) ** (fdim s) - 1)``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteField s` by metis_tac[subfield_finite_field] >>
  `CARD B = char r ** fdim s` by rw[finite_field_card_alt, subfield_char] >>
  `FINITE B` by metis_tac[subfield_carrier_finite] >>
  `#0 IN B` by metis_tac[subfield_ids, field_zero_element] >>
  `B INTER {#0} = {#0}` by rw[INTER_SING] >>
  qabbrev_tac `g = subset_group f* (s.prod.carrier DIFF {#0})` >>
  `g <= f*` by rw[subfield_mult_subset_group_subgroup, Abbr`g`] >>
  `G = B DIFF {#0}` by rw[subset_group_property, Abbr`g`] >>
  `CARD G = CARD B - 1` by rw[CARD_DIFF_EQN] >>
  metis_tac[]);

(* Theorem: FiniteField r ==> !g n. g <= f* /\ (CARD G = (char r) ** n - 1) ==>
            ?s. s <<= r /\ (fdim s = n) *)
(* Proof:
   Let p = char r.
   Then 1 < p                 by finite_field_char_gt_1
   Note FiniteGroup g         by field_subgroup_finite_group
    ==> Group g /\ FINITE G   by FiniteGroup_def
    Now G <> {}               by group_carrier_nonempty
     so CARD G <> 0           by CARD_EQ_0
    ==> n <> 0                by EXP_0, CARD G = (char r) ** n - 1
   Thus 1 < p ** n            by ONE_LT_EXP, 1 < p, n <> 0
     or p ** n = CARD G + 1   by 1 < p ** n

   Let s = subset_field r (roots (master (p ** n))).
   Then s <<= r                       by poly_master_roots_subfield
    and B = roots (master (p ** n))   by subset_field_property
   Note B = G UNION {#0}              by field_subgroup_master_roots
    and CARD B = CARD G + 1           by field_subgroup_card
               = p ** n               by above
    Now char s = p                    by subfield_char, s <<= r
    and FiniteField s                 by subfield_finite_field, s <= r
   ==> fdim s = n                     by finite_field_dim_eq
   Take this s, and the result follows.
*)
val finite_field_subgroup_gives_subfield = store_thm(
  "finite_field_subgroup_gives_subfield",
  ``!r:'a field. FiniteField r ==> !g n. g <= f* /\ (CARD G = (char r) ** n - 1) ==>
   ?s. s <<= r /\ (fdim s = n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `p = char r` >>
  `1 < p` by rw[finite_field_char_gt_1, Abbr`p`] >>
  `FiniteGroup g` by metis_tac[field_subgroup_finite_group] >>
  `Group g /\ FINITE G` by metis_tac[FiniteGroup_def] >>
  `CARD G <> 0` by metis_tac[group_carrier_nonempty, CARD_EQ_0] >>
  `n <> 0` by metis_tac[EXP_0, DECIDE``1 - 1 = 0``] >>
  `1 < p ** n` by rw[ONE_LT_EXP] >>
  `p ** n = CARD G + 1` by decide_tac >>
  qabbrev_tac `s = subset_field r (roots (master (p ** n)))` >>
  `s <<= r` by rw[poly_master_roots_subfield, Abbr`s`, Abbr`p`] >>
  `B = roots (master (p ** n))` by rw[GSYM subset_field_property, Abbr`s`] >>
  `B = G UNION {#0}` by metis_tac[field_subgroup_master_roots] >>
  `CARD B = p ** n` by metis_tac[field_subgroup_card] >>
  `char s = p` by rw[subfield_char, Abbr`p`] >>
  `FiniteField s` by metis_tac[subfield_finite_field] >>
  `fdim s = n` by metis_tac[finite_field_dim_eq] >>
  metis_tac[]);

(* Theorem: FiniteField r ==> !n. (?s. s <<= r /\ (fdim s = n)) <=> (?g. g <= f* /\ (CARD G = (char r) ** n - 1)) *)
(* Proof:
   If part: s <<= r /\ (fdim s = n)) ==> ?g. g <= f* /\ (CARD G = (char r) ** n - 1)
      This is true     by finite_field_subfield_gives_subgroup
   Only-if part: g <= f* /\ (CARD G = (char r) ** n - 1) ==> ?s. s <<= r /\ (fdim s = n)
      This is true     by finite_field_subgroup_gives_subfield
*)
val finite_field_subfield_exists_iff_subgroup_exists = store_thm(
  "finite_field_subfield_exists_iff_subgroup_exists",
  ``!r:'a field. FiniteField r ==>
   !n. (?s. s <<= r /\ (fdim s = n)) <=> (?g. g <= f* /\ (CARD G = (char r) ** n - 1))``,
  metis_tac[finite_field_subfield_gives_subgroup, finite_field_subgroup_gives_subfield]);

(* This is a major theorem. *)

(* Theorem: FiniteField r ==> !n. (?s. s <<= r /\ (fdim s = n)) <=> n divides fdim r *)
(* Proof:
   Note FINITE F*                   by field_nonzero_finite, field_mult_carrier
    and cyclic f*                   by finite_field_mult_group_cyclic
   Let p = char r, d = fdim r.
   Then 1 < p                       by finite_field_char_gt_1
    and CARD R = p ** d             by finite_field_card_alt

        ?s. s <<= r /\ (fdim s = n)
    <=> ?g. g <= f* /\ (CARD G = p ** n - 1)      by finite_field_subfield_exists_iff_subgroup_exists
    <=> (p ** n - 1) divides (CARD F* )           by cyclic_subgroup_condition, cyclic f*
    <=> (p ** n - 1) divides (p ** d - 1)         by finite_field_mult_carrier_card
    <=> n divides d                               by power_predecessor_divisibility
*)
val finite_field_subfield_exists_condition = store_thm(
  "finite_field_subfield_exists_condition",
  ``!r:'a field. FiniteField r ==> !n. (?s. s <<= r /\ (fdim s = n)) <=> n divides fdim r``,
  rpt (stripDup[FiniteField_def]) >>
  `FINITE F*` by rw[field_nonzero_finite, field_mult_carrier] >>
  `cyclic f*` by rw[finite_field_mult_group_cyclic] >>
  qabbrev_tac `p = char r` >>
  qabbrev_tac `d = fdim r` >>
  `1 < p` by rw[finite_field_char_gt_1, Abbr`p`] >>
  `CARD R = p ** d` by rw[finite_field_card_alt, Abbr`p`, Abbr`d`] >>
  `(?s. s <<= r /\ (fdim s = n)) <=> (?g. g <= f* /\ (CARD G = p ** n - 1))` by rw[finite_field_subfield_exists_iff_subgroup_exists, Abbr`p`] >>
  `_ = (p ** n - 1) divides (CARD F*)` by rw[cyclic_subgroup_condition] >>
  `_ = (p ** n - 1) divides (p ** d - 1)` by rw[finite_field_mult_carrier_card] >>
  `_ = n divides d` by rw[power_predecessor_divisibility] >>
  rw[]);

(* This is a really cute proof of the subfield criteria. *)


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
