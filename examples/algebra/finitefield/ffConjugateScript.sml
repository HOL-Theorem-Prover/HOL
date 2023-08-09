(* ------------------------------------------------------------------------- *)
(* Finite Field: Element Conjugates                                          *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ffConjugate";

(* ------------------------------------------------------------------------- *)


(* val _ = load "jcLib"; *)
open jcLib;

(* val _ = load "SatisfySimps"; (* for SatisfySimps.SATISFY_ss *) *)

(* Get dependent theories local *)
(* val _ = load "ffMinimalTheory"; *)
open ffBasicTheory;
open ffAdvancedTheory;
open ffPolyTheory;
open ffCycloTheory;
open ffUnityTheory;
open ffMasterTheory;
open ffMinimalTheory;

(* open dependent theories *)
open arithmeticTheory pred_setTheory listTheory;

(* Get dependent theories in lib *)
(* (* val _ = load "helperNumTheory"; -- in monoidTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in monoidTheory *) *)
(* (* val _ = load "helperFunctionTheory"; -- in ringTheory *) *)
(* (* val _ = load "helperListTheory"; -- in polyRingTheory *) *)
open helperNumTheory helperSetTheory helperListTheory helperFunctionTheory;

(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open dividesTheory gcdTheory;

(* (* val _ = load "groupInstancesTheory"; -- in ringInstancesTheory *) *)
(* (* val _ = load "ringInstancesTheory"; *) *)
(* (* val _ = load "fieldInstancesTheory"; *) *)
open monoidTheory groupTheory ringTheory fieldTheory;
open monoidOrderTheory groupOrderTheory;
open subgroupTheory;
open groupInstancesTheory ringInstancesTheory fieldInstancesTheory;

(* Get polynomial theory of Ring *)
(* (* val _ = load "polyFieldModuloTheory"; *) *)
open polynomialTheory polyWeakTheory polyRingTheory;
open polyDivisionTheory polyBinomialTheory;
open polyMonicTheory polyEvalTheory;
open polyFieldTheory;
open polyFieldDivisionTheory;
open polyFieldModuloTheory;
open fieldMapTheory;

open polyDividesTheory;
open polyMonicTheory;
open polyRootTheory;
open polyProductTheory;
open polyGCDTheory;
open polyIrreducibleTheory;

(* (* val _ = load "groupProductTheory"; *) *)
open groupProductTheory;
open fieldOrderTheory;

(* (* val _ = load "ringBinomialTheory"; *) *)
open ringBinomialTheory;
open ringDividesTheory;
open ringIdealTheory;
open ringUnitTheory;

open binomialTheory;
open GaussTheory;


(* ------------------------------------------------------------------------- *)
(* Finite Field Element Conjugates Documentation                             *)
(* ------------------------------------------------------------------------- *)
(* Overload:
   conj x n     = ring_conjugate r s x n
   Conj x       = ring_conjugates r s x
   x ~~ y       = eq_conj (r:'a ring) (s:'a ring) x y
*)
(* Definitions and Theorems (# are exported):

   Conjugate of an element:
   ring_conjugate_def      |- !r s x n. conj x n = x ** CARD B ** n
   ring_conjugate_element  |- !r s. Ring r ==> !x. x IN R ==> !n. conj x n IN R
   ring_conjugate_zero     |- !r s. Ring r /\ 0 < CARD B ==> !n. conj #0 n = #0
   ring_conjugate_one      |- !r s. Ring r ==> !n. conj #1 n = #1
   ring_conjugate_0        |- !r s. Ring r ==> !x. x IN R ==> (conj x 0 = x)

   Conjugates of an element:
   ring_conjugates_def     |- !r s x. Conj x = IMAGE (conj x) univ(:num)
   ring_conjugates_alt     |- !r s x. Conj x = {x ** CARD B ** n | n IN univ(:num)}
   ring_conjugates_member  |- !r s x y. y IN Conj x <=> ?n. y = conj x n
   ring_conjugates_subset  |- !r s. Ring r ==> !x. x IN R ==> Conj x SUBSET R
   ring_conjugates_finite  |- !r s. FiniteRing r ==> !x. x IN R ==> FINITE (Conj x)
   ring_conjugates_zero    |- !r s. Ring r /\ 0 < CARD B ==> (Conj #0 = {#0})
   ring_conjugates_one     |- !r s. Ring r ==> (Conj #1 = {#1})
   ring_conjugates_has_self         |- !r s. Ring r ==> !x. x IN R ==> x IN Conj x
   ring_conjugates_member_element   |- !r s. Ring r ==> !x. x IN R ==> !y. y IN Conj x ==> y IN R
   ring_conjugates_member_eqn       |- !r s x y. y IN Conj x <=> ?n. y = x ** CARD B ** n
   ring_conjugates_has_element_conjugate     |- !r. Ring r ==> !x. x IN R ==>
                                                !z. z IN Conj x ==> !n. conj z n IN Conj x
   ring_conjugates_subset_element_conjugates |- !r. Ring r ==> !x. x IN R ==>
                                                !z. z IN Conj x ==> Conj z SUBSET Conj x
   ring_conjugate_exp_subfield_card |- !r s. Ring r ==> !x. x IN R ==> !e. e IN Conj x ==> e ** CARD B IN Conj x
   ring_conjugate_exp_conjugate     |- !r s. Ring r ==> !x. x IN R ==> !e. e IN Conj x ==>
                                       !n. e ** CARD B ** n IN Conj x

   Cardinality of Conjugates:
   finite_field_conjugate_member_eqn     |- !r s. FiniteField r ==> !x. x IN R+ ==>
                                            !n. conj x n = x ** (CARD B ** n MOD forder x)
   finite_field_conjugate_zero           |- !r s. FiniteField r /\ s <<= r ==> !n. conj #0 n = #0
   finite_field_conjugate_eqn            |- !r s. FiniteField r /\ s <<= r ==>
                                            !x. x IN R ==> !n. conj x n = conj x (n MOD (r <:> s))
   finite_field_conjugate_eq_one         |- !r s. FiniteField r /\ s <<= r ==>
                                            !x. x IN R ==> !n. (conj x n = #1) <=> (x = #1)
   finite_field_conjugates_zero          |- !r s. FiniteField r /\ s <<= r ==> (Conj #0 = {#0})
   finite_field_conjugate_eq_zero        |- !r s. FiniteField r /\ s <<= r ==>
                                            !x. x IN R ==> !n. (conj x n = #0) <=> (x = #0)
   finite_field_conjugates_has_zero      |- !r s. FiniteField r /\ s <<= r ==>
                                            !x. x IN R ==> (#0 IN Conj x <=> (x = #0))
   finite_field_conjugates_subset        |- !r s. FiniteField r /\ s <<= r ==>
                                            !x. x IN R ==> Conj x SUBSET IMAGE (conj x) (count (r <:> s))
   finite_field_conjugates_card_upper    |- !r s. FiniteField r /\ s <<= r ==>
                                            !x. x IN R ==> CARD (Conj x) <= (r <:> s)
   finite_field_conjugates_exp_surj      |- !r s. FiniteField r /\ s <<= r ==>
                                            !x. x IN R ==> SURJ (\z. z ** CARD B) (Conj x) (Conj x)
   finite_field_conjugates_exp_image_eq  |- !r s. FiniteField r /\ s <<= r ==>
                                            !x. x IN R ==> (IMAGE (\z. z ** CARD B) (Conj x) = Conj x)

   Conjugate Properties:
   subfield_poly_conjugate_roots |- !r s. FiniteField r /\ s <<= r ==>
                                    !p. Poly s p ==> !x. x IN R /\ root p x ==> !n. root p (conj x n)
   subfield_conjugates_are_minimal_roots  |- !r. FiniteField r ==> !s. s <<= r ==>
                                             !x. x IN R ==> Conj x SUBSET roots (minimal x)
   finite_field_conjugate_order  |- !r s. FiniteField r /\ s <<= r ==> !n. forder (conj x n) = forder x
   finite_field_conjugates_order |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==>
                                    !y. y IN Conj x ==> (forder y = forder x)
   finite_field_conjugates_subset_orders  |- !r s. FiniteField r /\ s <<= r ==>
                                             !x n. x IN orders f* n ==> Conj x SUBSET orders f* n

   Product of Conjugate Factors:
   conjugate_factors_finite          |- !r s. FiniteRing r ==> !x. x IN R ==> FINITE (IMAGE factor (Conj x))
   conjugate_factors_member          |- !r s x p. p IN IMAGE factor (Conj x) ==> ?n. p = factor (conj x n)
   conjugate_factors_member_property |- !r s. Ring r /\ #1 <> #0 ==> !x. x IN R ==>
                        !p. p IN IMAGE factor (Conj x) ==> poly p /\ (deg p = 1) /\ (lead p = #1) /\ monic p
   poly_prod_conjugate_factors_monic |- !r s. FiniteField r ==> !x. x IN R ==> monic (PIFACTOR (Conj x))
   poly_prod_conjugate_factors_poly  |- !r s. FiniteField r ==> !x. x IN R ==> poly (PIFACTOR (Conj x))
   poly_prod_conjugate_factors_lead  |- !r s. FiniteField r ==> !x. x IN R ==> (lead (PIFACTOR (Conj x)) = #1)
   poly_prod_conjugate_factors_deg   |- !r s. FiniteField r ==> !x. x IN R ==> (deg (PIFACTOR (Conj x)) = CARD (Conj x))
   poly_prod_conjugate_factors_roots |- !r s. FiniteField r ==> !x. x IN R ==> (roots (PIFACTOR (Conj x)) = Conj x)

   Product of Conjugates is Subfield Polynomial:
   poly_factor_exp_eq       |- !r. FiniteField r ==> !x y. x IN R /\ y IN R ==>
                               !n. (factor x ** char r ** n = factor y ** char r ** n) <=> (x = y)
   poly_factor_map_exp_inj  |- !r. FiniteField r ==> !s. s SUBSET R ==>
                               !n. INJ (\p. p ** char r ** n) (IMAGE factor s) univ(:'a poly)
   poly_factor_exp_to_peval_factor    |- !r. FiniteField r ==> !c. c IN R ==>
                         !n. factor c ** char r ** n = peval (factor (c ** char r ** n)) (X ** char r ** n)
   poly_factor_conjugates_exp_inj     |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==>
                                               INJ (\p. p ** CARD B) (IMAGE factor (Conj x)) univ(:'a poly)
   poly_factor_conjugates_peval_inj   |- !r s. Ring r /\ #1 <> #0 ==> !x. x IN R ==>
                                 !q. poly q ==> INJ (\p. peval p q) (IMAGE factor (Conj x)) univ(:'a poly)
   finite_field_conjugates_exp_to_peval_images
                                      |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==>
                             (IMAGE ((\p. p ** CARD B) o factor) (Conj x) =
                              IMAGE ((\p. peval p (X ** CARD B)) o factor) (Conj x))
   poly_prod_factors_conjugates_subfield_poly
                                      |- !r s. FiniteField r /\ s <<= r ==>
                                           !x. x IN R ==> Poly s (PIFACTOR (Conj x))

   Minimal Polynomial as Product of Conjugates:
   poly_minimal_eq_factors_conjugates
                         |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> (minimal x = PIFACTOR (Conj x))
   poly_minimal_eq_factors_conjugates_alt
                         |- !r s. FiniteField r /\ s <<= r ==>
                            !x. x IN R ==> (minimal x = PPROD {X - c * |1| | c | c IN Conj x})
   poly_minimal_eq_factors_conjugates_compose
                         |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> (minimal x = ((\s. PIFACTOR s) o Conj) x)
   poly_minimal_roots    |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> (roots (minimal x) = Conj x)
   poly_minimal_deg      |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> (degree x = CARD (Conj x))

   Counting Conjugates:
   finite_field_conjugate_mod_order |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
                                       !n. conj x n = conj x (n MOD order (ZN (forder x)).prod (CARD B))
   finite_field_conjugates_member   |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
                             !y. y IN Conj x ==> ?n. n < order (ZN (forder x)).prod (CARD B) /\ (y = conj x n)
   finite_field_conjugates_member_order  |- !r s. FiniteField r /\ s <<= r ==>
                                            !x y. x IN R /\ y IN Conj x ==> (forder y = forder x)
   finite_field_conjugates_inj      |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
                                       INJ (conj x) (count (order (ZN (forder x)).prod (CARD B))) (Conj x)
   finite_field_conjugates_surj     |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
                                       SURJ (conj x) (count (order (ZN (forder x)).prod (CARD B))) (Conj x)
   finite_field_conjugates_bij      |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
                                       BIJ (conj x) (count (order (ZN (forder x)).prod (CARD B))) (Conj x)
   finite_field_conjugates_eq_image |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
                                       (Conj x = IMAGE (conj x) (count (order (ZN (forder x)).prod (CARD B))))
   finite_field_conjugates_card     |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
                                       (CARD (Conj x) = order (ZN (forder x)).prod (CARD B))

   Degree of Minimal Polynomial:
   poly_minimal_deg_eqn          |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
                                          (degree x = order (ZN (forder x)).prod (CARD B))
   poly_minimal_deg_divides_dim  |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==>
                                          degree x divides (r <:> s)

   Monic Irreducible to be Minimal Polynomial:
   poly_minimal_unique           |- !r s. FiniteField r /\ s <<= r ==> !p. monic p /\ IPoly s p ==>
                                    !x. x IN R ==> (root p x <=> (p = minimal x))
   subfield_monic_irreducible_by_conjugate_factors
                                 |- !r s. FiniteField r /\ s <<= r ==> !p. monic p /\ IPoly s p ==>
                                    !x. x IN R ==> (root p x <=> (p = PIFACTOR (Conj x)))
   poly_monic_irreducible_is_minimal_poly
                                 |- !r s. FiniteField r /\ s <<= r ==> !p. monic p /\ IPoly s p /\
                                          deg p divides (r <:> s) ==> ?x. x IN R /\ (p = minimal x)
   poly_monic_irreducible_minimal_condition
                                 |- !r s. FiniteField r /\ s <<= r ==> !p. monic p /\ IPoly s p /\
                                          deg p divides (r <:> s) <=> ?x. x IN R /\ (p = minimal x)
   poly_minimal_divides_master   |- !r s. FiniteField r /\ s <<= r ==>
                                    !x. x IN R ==> minimal x pdivides master (CARD R)
   poly_monic_irreducible_eq_minimal_poly
                                 |- !r s. FiniteField r /\ s <<= r ==>
                                    !p. monic p /\ IPoly s p /\ p pdivides master (CARD R) <=>
                                        ?x. x IN R /\ p = minimal x

   Orders Partition by Conjugates:
   eq_conj_def     |- !r s x y. x ~~ y <=> ?k. y = conj x k
   eq_conj_refl    |- !r s. Ring r ==> !x. x IN R ==> x ~~ x
   eq_conj_trans   |- !r s. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> x ~~ y /\ y ~~ z ==> x ~~ z
   eq_conj_sym     |- !r s. FiniteField r /\ s <<= r ==> !x y. x IN R /\ y IN R ==> x ~~ y ==> y ~~ x
   eq_conj_equiv_on_field_carrier   |- !r s. FiniteField r /\ s <<= r ==> $~~ equiv_on R
   eq_conj_equiv_on_orders          |- !r s. FiniteField r /\ s <<= r ==> !n. $~~ equiv_on orders f* n
   ring_conjugates_element   |- !r. Ring r ==> !x. x IN R ==> !y. y IN Conj x <=> y IN R /\ x ~~ y
   eq_conj_in_conjugates     |- !r s. Ring r ==> !x y. x IN R /\ y IN R ==> (x ~~ y <=> y IN Conj x)
   eq_conj_eq_conjugages     |- !r s. FiniteField r /\ s <<= r ==>
                                !x y. x IN R /\ y IN R ==> (x ~~ y <=> (Conj x = Conj y))
   eq_conj_eq_order          |- !r s. FiniteField r /\ s <<= r ==>
                                !x y. x IN R /\ y IN R /\ x ~~ y ==> (forder x = forder y)
   eq_conj_eq_poly_minimal   |- !r s. FiniteField r /\ s <<= r ==>
                                !x y. x IN R /\ y IN R ==> (x ~~ y <=> (minimal x = minimal y))
   eq_conj_partition_field_carrier  |- !r. Ring r ==> (partition $~~ R = IMAGE Conj R)
   eq_conj_partition_conjugates     |- !r s. FiniteField r /\ s <<= r ==>
                                       !n. partition $~~ (orders f* n) = IMAGE Conj (orders f* n)
   poly_prod_factors_conjugates_inj |- !r. Field r ==> !t. FINITE t /\ t SUBSET R ==>
                                           INJ (\s. PIFACTOR s) (partition $~~ t) univ(:'a poly)

   Master Polynomial as Product of Minimal Polynomial:
   poly_master_eq_poly_minimal_product
                     |- !r s. FiniteField r /\ s <<= r ==>
                               (master (CARD R) = PPIMAGE minimal R)
   poly_master_eq_poly_minimal_product_alt
                     |- !r s. FiniteField r /\ s <<= r ==>
                               (master (CARD R) = PPROD {minimal x | x | x IN R})

   Cyclotomic Polynomial as Product of Minimal Polynomial:
   poly_cyclo_eq_prod_factors_by_partition
                     |- !r s. FiniteField r /\ s <<= r ==>
                          !n. cyclo n = PPIMAGE (\s. PIFACTOR s) (partition $~~ (orders f* n))
   poly_cyclo_eq_poly_minimal_product
                     |- !r s. FiniteField r /\ s <<= r ==>
                          !n. cyclo n = PPIMAGE minimal (orders f* n)
   poly_cyclo_eq_poly_minimal_product_alt
                     |- !r s. FiniteField r /\ s <<= r ==>
                          !n. cyclo n = PPROD {minimal x | x | x IN orders f* n}
   poly_cyclo_spoly  |- !r s. FiniteField r /\ s <<= r ==> !n. Poly s (cyclo n)
   poly_cyclo_irreducible_factor_deg
                     |- !r s. FiniteField r /\ s <<= r ==> !p. monic p /\ IPoly s p ==>
                          !n. 0 < n /\ p pdivides cyclo n ==> (deg p = order (ZN n).prod (CARD B))
   poly_cyclo_irreducible_factor_deg_alt
                     |- !r. FiniteField r ==> !p. monic p /\ ipoly p ==>
                        !n. 0 < n /\ p pdivides cyclo n ==> (deg p = ordz n (CARD R))

   Special subfield factor of Cyclo and Unity polynomials:
   poly_cyclo_special_subfield_factor
                     |- !r s. FiniteField r /\ s <<= r /\ 1 < (r <:> s) ==>
                        !n. 0 < n /\ coprime n (CARD B) /\ (ordz n (CARD B) = r <:> s) ==>
                        ?h. monic h /\ IPoly s h /\ h pdivides cyclo n /\ (deg h = ordz n (CARD B))
   poly_unity_special_subfield_factor
                     |- !r s. FiniteField r /\ s <<= r /\ 1 < (r <:> s) ==>
                        !n. 0 < n /\ coprime n (CARD B) /\ (ordz n (CARD B) = r <:> s) ==>
                        ?h. monic h /\ IPoly s h /\ h pdivides unity n /\
                            (deg h = ordz n (CARD B)) /\ roots h SUBSET orders f* n

   Cyclo and Unity polynomials by Irreducible Factors:
   poly_cyclo_by_distinct_irreducibles
                     |- !r. FiniteField r ==> !n. n divides CARD R+ ==>
                        ?s. FINITE s /\ miset s /\ s <> {} /\ (cyclo n = PPROD s)
   poly_cyclo_mod_exp_char_eq
                     |- !r. FiniteField r ==> !n. n divides CARD R+ ==>
                        !p q. poly p /\ poly q /\ (p ** char r == q ** char r) (pm (cyclo n)) ==>
                                                  (p == q) (pm (cyclo n))
   poly_unity_by_distinct_irreducibles
                     |- !r. FiniteField r ==> !n. n divides CARD R+ ==>
                        ?s. FINITE s /\ miset s /\ s <> {} /\ (unity n = PPROD s)
   poly_unity_mod_exp_char_eq
                     |- !r. FiniteField r ==> !n. n divides CARD R+ ==>
                        !p q. poly p /\ poly q /\ (p ** char r == q ** char r) (pm (unity n)) ==>
                                                  (p == q) (pm (unity n))
   poly_unity_mod_exp_char_eq_zero
                     |- !r. FiniteField r ==> !n. n divides CARD R+ ==>
                        !p. poly p /\ (p ** char r == |0|) (pm (unity n)) ==>
                                      (p == |0|) (pm (unity n))
   poly_unity_mod_exp_char_equal
                     |- !r. FiniteField r ==> !n. coprime n (CARD R) /\ 1 < ordz n (CARD R) ==>
                        !p q. poly p /\ poly q /\ (p ** char r == q ** char r) (pm (unity n)) ==>
                                                  (p == q) (pm (unity n))
   poly_unity_mod_exp_char_equal_zero
                     |- !r. FiniteField r ==> !n. coprime n (CARD R) /\ 1 < ordz n (CARD R) ==>
                        !p. poly p /\ (p ** char r == |0|) (pm (unity n)) ==>
                                      (p == |0|) (pm (unity n))

   Unity Roots by Master Roots:
   poly_unity_roots_by_master_roots
                     |- !r. FiniteField r ==> (roots (unity (CARD R+)) = R+)
   poly_unity_eq_root_factor_product
                     |- !r. FiniteField r ==> (unity (CARD R+) = PIFACTOR R+)
   poly_unity_eq_root_factor_product_alt
                     |- !r. FiniteField r ==> (unity (CARD R+) = PPROD {X - c * |1| | c | c IN R+})
*)

(* ------------------------------------------------------------------------- *)
(* Conjugate of an element                                                   *)
(* ------------------------------------------------------------------------- *)

(* Define an element conjugate with respect to a subring *)
val ring_conjugate_def = Define `
    ring_conjugate (r:'a ring) (s:'a ring) (x: 'a) n = x ** ((CARD B) ** n)
`;
(* Overload on ring conjugate *)
val _ = overload_on("conj", ``ring_conjugate r s``);
(*
> ring_conjugate_def;
val it = |- !r s x n. conj x n = x ** CARD B ** n: thm
*)

(* Theorem: Ring r ==> !x. x IN R ==> !n. conj x n IN R *)
(* Proof: by ring_conjugate_def, ring_exp_element *)
val ring_conjugate_element = store_thm(
  "ring_conjugate_element",
  ``!(r s):'a ring. Ring r ==> !x. x IN R ==> !n. conj x n IN R``,
  rw[ring_conjugate_def]);

(* Theorem: Ring r /\ 0 < CARD B ==> !n. ring_conjugate r s #0 n = #0 *)
(* Proof:
   Note 0 < CARD B ==> 0 < CARD B ** n    by EXP_POS
     ring_conjugate r s #0 n
   = #0 ** CARD B ** n                    by ring_conjugate_def
   = #0                                   by ring_zero_exp, CARD B ** n <> 0.
*)
val ring_conjugate_zero = store_thm(
  "ring_conjugate_zero",
  ``!(r s):'a ring. Ring r /\ 0 < CARD B ==> !n. ring_conjugate r s #0 n = #0``,
  rw_tac std_ss[ring_conjugate_def] >>
  `0 < CARD B ** n` by rw[EXP_POS] >>
  `CARD B ** n <> 0` by decide_tac >>
  rw[ring_zero_exp]);

(* Theorem: Ring r ==> !n. ring_conjugate r s #1 n = #1 *)
(* Proof: by ring_conjugate_def, ring_one_exp *)
val ring_conjugate_one = store_thm(
  "ring_conjugate_one",
  ``!(r s):'a ring. Ring r ==> !n. ring_conjugate r s #1 n = #1``,
  rw[ring_conjugate_def]);

(* Theorem: Ring r ==> !x. x IN R ==> (conj x 0 = x) *)
(* Proof:
      conj x 0
    = x ** (CARD B ** 0)     by ring_conjugate_def
    = x ** 1                 by EXP
    = x                      by ring_exp_1
*)
val ring_conjugate_0 = store_thm(
  "ring_conjugate_0",
  ``!(r s):'a ring. Ring r ==> !x. x IN R ==> (conj x 0 = x)``,
  rw[ring_conjugate_def, EXP]);

(* ------------------------------------------------------------------------- *)
(* Conjugates of an element                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define the set of conjugates with respect to a subring *)
val ring_conjugates_def = Define `
    ring_conjugates (r:'a ring) (s:'a ring) (x: 'a) = IMAGE (conj x) univ(:num)
`;
(* Overload on ring conjugates *)
val _ = overload_on("Conj", ``ring_conjugates r s``);
(*
> ring_conjugates_def;
val it = |- !r s x. Conj x = IMAGE (conj x) univ(:num): thm
*)

(* Theorem: ring_conjugates r s x = {x ** CARD B ** n | n | n IN univ(:num)} *)
(* Proof: by ring_conjugates_def, ring_conjugate_def *)
val ring_conjugates_alt = store_thm(
  "ring_conjugates_alt",
  ``!(r:'a ring) s x. ring_conjugates r s x = {x ** CARD B ** n | n | n IN univ(:num)}``,
  rw[ring_conjugates_def, ring_conjugate_def, EXTENSION]);

(* Theorem: !x y. y IN Conj x <=> ?n. y = conj x n *)
(* Proof: by ring_conjugates_def, IN_IMAGE *)
val ring_conjugates_member = store_thm(
  "ring_conjugates_member",
  ``!(r s):'a ring. !x y. y IN Conj x <=> ?n. y = conj x n``,
  rw[ring_conjugates_def]);

(* Theorem: Ring r ==> !x. x IN R ==> (Conj x) SUBSET R *)
(* Proof:
       (Conj x) SUBSET R
   <=> !x. x IN (Conj x) ==> x IN R     by SUBSET_DEF
   <=> !x. x IN (IMAGE (conj x) univ(:num)) ==> x IN R   by ring_conjugates_def
   <=> !n. conj x n IN R                by IN_IMAGE
   which is true                        by ring_conjugate_element
*)
val ring_conjugates_subset = store_thm(
  "ring_conjugates_subset",
  ``!(r s):'a ring. Ring r ==> !x. x IN R ==> (Conj x) SUBSET R``,
  rw[ring_conjugates_def, SUBSET_DEF] >>
  metis_tac[ring_conjugate_element]);

(* Theorem: FiniteRing r ==> !x. x IN R ==> FINITE (Conj x) *)
(* Proof:
   Note FiniteRing r
    ==> Ring r /\ FINITE R       by FiniteRing_def
    Now (Conj x) SUBSET R        by ring_conjugates_subset
   Hence FINITE (Conj x)         by SUBSET_FINITE
*)
val ring_conjugates_finite = store_thm(
  "ring_conjugates_finite",
  ``!(r s):'a ring. FiniteRing r ==> !x. x IN R ==> FINITE (Conj x)``,
  metis_tac[FiniteRing_def, ring_conjugates_subset, SUBSET_FINITE]);

(* Theorem: Ring r /\ 0 < CARD B ==> (Conj #0 = {#0}) *)
(* Proof: by ring_conjugates_def, ring_conjugate_zero *)
val ring_conjugates_zero = store_thm(
  "ring_conjugates_zero",
  ``!(r s):'a ring. Ring r /\ 0 < CARD B ==> (Conj #0 = {#0})``,
  rw[ring_conjugates_def, EXTENSION] >>
  metis_tac[ring_conjugate_zero]);

(* Theorem: Ring r ==> (Conj #1 = {#1}) *)
(* Proof: by ring_conjugates_def, ring_conjugate_one *)
val ring_conjugates_one = store_thm(
  "ring_conjugates_one",
  ``!(r s):'a ring. Ring r ==> (Conj #1 = {#1})``,
  rw[ring_conjugates_def, EXTENSION] >>
  metis_tac[ring_conjugate_one]);

(* Theorem: Ring r ==> !x. x IN R ==> x IN (Conj x) *)
(* Proof:
   Since conj x 0 = x      by ring_conjugate_0
   Hence x IN (Conj x)     by ring_conjugates_member
*)
val ring_conjugates_has_self = store_thm(
  "ring_conjugates_has_self",
  ``!(r s):'a ring. Ring r ==> !x. x IN R ==> x IN (Conj x)``,
  metis_tac[ring_conjugates_member, ring_conjugate_0]);

(* Theorem: Ring r ==> !x. x IN R ==> !y. y IN Conj x ==> y IN R *)
(* Proof:
   Given y IN Conj x
     ==> ?n. y = conj x n  by ring_conjugates_member
     ==> y in R            by ring_conjugate_element
   Or,
   Since Conj x SUBSET R   by ring_conjugates_subset
      so result follows    by SUBSET_DEF
*)
val ring_conjugates_member_element = store_thm(
  "ring_conjugates_member_element",
  ``!(r s):'a ring. Ring r ==> !x. x IN R ==> !y. y IN Conj x ==> y IN R``,
  metis_tac[ring_conjugates_subset, SUBSET_DEF]);

(* Theorem: y IN Conj x <=> ?n. y = x ** ((CARD B) ** n) *)
(* Proof: by ring_conjugates_member, ring_conjugate_def *)
val ring_conjugates_member_eqn = store_thm(
  "ring_conjugates_member_eqn",
  ``!(r s):'a ring. !x y. y IN Conj x <=> ?n. y = x ** ((CARD B) ** n)``,
  rw[ring_conjugates_member, ring_conjugate_def]);

(* Theorem: Ring r ==> !x. x IN R ==> !z. z IN Conj x ==> !n. (conj z n) IN Conj x *)
(* Proof:
   By ring_conjugates_member, ring_conjugate_def, this is to show:
      ?n''. (x ** CARD B ** n) ** CARD B ** n' = x ** CARD B ** n''
     (x ** CARD B ** n) ** CARD B ** n'
   = x ** ((CARD B ** n) * (CARD B ** n'))    by ring_exp_mult
   = x ** (CARD B) ** (n + n')                by EXP_ADD
   Thus putting n'' = n + n' will make the result true.
*)
val ring_conjugates_has_element_conjugate = store_thm(
  "ring_conjugates_has_element_conjugate",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !z. z IN Conj x ==> !n. (conj z n) IN Conj x``,
  metis_tac[ring_conjugates_member, ring_conjugate_def, ring_exp_mult, EXP_ADD]);

(* Theorem: Ring r ==> !x. x IN R ==> !z. z IN Conj x ==> (Conj z) SUBSET (Conj x) *)
(* Proof:
   By SUBSET_DEF, this is to show: z IN Conj x /\ x' IN Conj z ==> x' IN Conj x
   Since x' IN Conj z,
     ==> ?n. x' = conj z n   by ring_conjugates_member
    then x' IN Conj x        by ring_conjugates_has_element_conjugate, z IN Conj x
*)
val ring_conjugates_subset_element_conjugates = store_thm(
  "ring_conjugates_subset_element_conjugates",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !z. z IN Conj x ==> (Conj z) SUBSET (Conj x)``,
  metis_tac[SUBSET_DEF, ring_conjugates_has_element_conjugate, ring_conjugates_member]);

(* Theorem: Ring r ==> !x. x IN R ==> !e. e IN Conj x ==> e ** (CARD B) IN Conj x *)
(* Proof:
       e IN Conj x
   <=> ?n. e = conj x n            by ring_conjugates_member
   <=> ?n. e = x ** (CARD B ** n)  by ring_conjugate_def
   Let m = CARD B.
       e ** m
     = (x ** (m ** n)) ** m        by above, e = x ** (m ** n)
     = x ** (m ** n * m)           by ring_exp_mult
     = x ** (m * m ** n)           by MULT_COMM
     = x ** (m ** SUC n)           by EXP
     = conj x (SUC n)              by ring_conjugate_def
  Hence e ** m IN Conj x           by ring_conjugates_member
*)
val ring_conjugate_exp_subfield_card = store_thm(
  "ring_conjugate_exp_subfield_card",
  ``!(r s):'a ring. Ring r ==> !x. x IN R ==> !e. e IN Conj x ==> e ** (CARD B) IN Conj x``,
  rw[ring_conjugates_def, ring_conjugate_def] >>
  qabbrev_tac `m = CARD B` >>
  `(x ** m ** x') ** m  = x ** ((m ** x') * m)` by rw[ring_exp_mult] >>
  `_ = x ** (m ** SUC x')` by rw_tac std_ss[EXP, MULT_COMM] >>
  metis_tac[]);

(* The following is a generalisation of ring_conjugate_exp_subfield_card *)

(* Theorem: Ring r ==> !x. x IN R ==> !e. e IN Conj x ==> !n. e ** CARD B ** n IN Conj x *)
(* Proof:
   Let m = CARD B.
       e IN Conj x
   ==> ?k. e = conj x k              by ring_conjugates_member
   ==> e = x ** (m ** k)             by ring_conjugate_def
       e ** (m ** n)
     = (x ** (m ** k)) ** (m ** n)   by above
     = x ** (m ** k * m ** n)        by ring_exp_mult
     = x ** (m ** (k + n))           by EXP_ADD
     = conj x (k + n)                by ring_conjugate_def
  Hence e ** (m ** n) IN Conj x      by ring_conjugates_member
*)
val ring_conjugate_exp_conjugate = store_thm(
  "ring_conjugate_exp_conjugate",
  ``!(r s):'a ring. Ring r ==> !x. x IN R ==> !e. e IN Conj x ==> !n. e ** CARD B ** n IN Conj x``,
  rw[ring_conjugates_member, ring_conjugate_def] >>
  metis_tac[ring_exp_mult, EXP_ADD]);

(* ------------------------------------------------------------------------- *)
(* Cardinality of Conjugates                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==> !x. x IN R+ ==> !n. conj x n = x ** ((CARD B ** n) MOD (forder x)) *)
(* Proof:
   Let m = CARD B.
       conj x n
     = x ** (m ** n)                   by ring_conjugate_def
     = x ** (m ** n MOD (forder x))    by finite_field_exp_mod_order, x IN R+
*)
val finite_field_conjugate_member_eqn = store_thm(
  "finite_field_conjugate_member_eqn",
  ``!(r s):'a field. FiniteField r ==> !x. x IN R+ ==> !n. conj x n = x ** ((CARD B ** n) MOD (forder x))``,
  metis_tac[ring_conjugate_def, finite_field_exp_mod_order]);

(* Theorem: FiniteField r /\ s <<= r  ==> !n. conj #0 n = #0 *)
(* Proof:
   Since 0 < CARD B           by finite_subfield_card_pos
      so !n. conj #0 n = #0   by ring_conjugate_zero
*)
val finite_field_conjugate_zero = store_thm(
  "finite_field_conjugate_zero",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !n. conj #0 n = #0``,
  metis_tac[finite_subfield_card_pos, ring_conjugate_zero, finite_field_is_field, field_is_ring]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==> !n. conj x n = conj x (n MOD (r <:> s)) *)
(* Proof:
   Let m = CARD B, d = (r <:> s).
   Then (CARD R = m ** d) /\ 0 < d                       by finite_subfield_card_eqn
     conj x n
   = x ** (m ** n)                                       by ring_conjugate_def
   = x ** (m ** ((n DIV d) * d + n MOD d))               by DIVISION
   = x ** (m ** (d * (n DIV d) + n MOD d))               by MULT_COMM
   = x ** (m ** (d * (n DIV d)) * m ** (n MOD d))        by EXP_ADD
   = x ** ((m ** d) ** (n DIV d) * m ** (n MOD d))       by EXP_EXP_MULT
   = (x ** ((m ** d) ** (n DIV d))) ** (m ** (n MOD d))  by field_exp_mult
   = (x ** ((CARD R) ** (n DIV d))) ** (m ** (n MOD d))  by above
   = x ** (m ** (n MOD d))                               by finite_field_fermat_all
   = conj x (n MOD d)                                    by ring_conjugate_def
*)
val finite_field_conjugate_eqn = store_thm(
  "finite_field_conjugate_eqn",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> !n. conj x n = conj x (n MOD (r <:> s))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = CARD B` >>
  qabbrev_tac `d = (r <:> s)` >>
  `(CARD R = m ** d) /\ 0 < d` by rw[finite_subfield_card_eqn, Abbr`m`, Abbr`d`] >>
  `conj x n = x ** m ** n` by rw[ring_conjugate_def] >>
  `_ = x ** m ** (d * (n DIV d) + n MOD d)` by metis_tac[DIVISION, MULT_COMM] >>
  `_ = x ** (m ** (d * (n DIV d)) * m ** (n MOD d))` by rw[EXP_ADD] >>
  `_ = x ** ((m ** d) ** (n DIV d) * m ** (n MOD d))` by rw[EXP_EXP_MULT] >>
  `_ = (x ** ((m ** d) ** (n DIV d))) ** (m ** (n MOD d))` by rw[field_exp_mult] >>
  `_ = x ** (m ** (n MOD d))` by metis_tac[finite_field_fermat_all] >>
  `_ = conj x (n MOD d)` by rw[ring_conjugate_def] >>
  rw[]);

(* Theorem:  FiniteField r /\ s <<= r ==>
             !x. x IN R ==> !n. (conj x n = #1) <=> (x = #1) *)
(* Proof:
   If part: conj x n = #1 ==> x = #1
      Let m = CARD B, d = (r <:> s)
      Then (CARD R = m ** d) /\ 0 < d   by finite_subfield_card_eqn
       and CARD R+ = CARD R - 1         by finite_field_nonzero_carrier_card
      Note x ** m ** n = #1             by ring_conjugate_def
      Since 0 < m                       by finite_subfield_card_pos
         so 0 < m ** n                  by EXP_POS
       thus x <> #0                     by field_zero_exp
         or x IN R+                     by field_nonzero_eq
        Now forder x divides CARD R+    by field_order_divides, x IN R+
        and forder x divides m ** n     by field_order_divides_exp, x IN R+
         so forder x divides gcd (m ** n) (m ** d - 1)   by GCD_IS_GREATEST_COMMON_DIVISOR
        But gcd (m ** n) (m ** d - 1) = 1                by coprime_power_and_power_predecessor, 0 < m, 0 < d
         so forder x = 1                by DIVIDES_ONE
         or x = #1                      by field_order_eq_1

   Only-if part: x = #1 ==> conj x n = #1
      True by ring_conjugate_one
*)
val finite_field_conjugate_eq_one = store_thm(
  "finite_field_conjugate_eq_one",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !x. x IN R ==> !n. (conj x n = #1) <=> (x = #1)``,
  rpt (stripDup[FiniteField_def]) >>
  rw[EQ_IMP_THM] >| [
    qabbrev_tac `m = CARD B` >>
    qabbrev_tac `d = (r <:> s)` >>
    `(CARD R = m ** d) /\ 0 < d` by rw[finite_subfield_card_eqn, Abbr`m`, Abbr`d`] >>
    `CARD R+ = CARD R - 1` by rw[finite_field_nonzero_carrier_card] >>
    `x ** m ** n = #1` by rw[GSYM ring_conjugate_def, Abbr`m`] >>
    `0 < m` by metis_tac[finite_subfield_card_pos] >>
    `0 < m ** n` by rw[EXP_POS] >>
    `x <> #0` by metis_tac[field_zero_exp, field_one_ne_zero, NOT_ZERO_LT_ZERO] >>
    `x IN R+` by rw[field_nonzero_eq] >>
    `forder x divides CARD R+` by rw[field_order_divides] >>
    `forder x divides m ** n` by rw[GSYM field_order_divides_exp] >>
    `gcd (m ** n) (m ** d - 1) = 1` by rw[coprime_power_and_power_predecessor] >>
    `forder x = 1` by metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR, DIVIDES_ONE] >>
    rw[GSYM field_order_eq_1],
    rw[ring_conjugate_one]
  ]);

(* This is an unexpected theorem, which leads to investigation of coprime_power_and_power_predecessor. *)

(* Theorem: FiniteField r ==> !s. s <<= r ==> (Conj #0 = {#0}) *)
(* Proof:
   Since 0 < CARD B           by finite_subfield_card_pos
      so Conj #0 = {#0}       by ring_conjugates_zero
*)
val finite_field_conjugates_zero = store_thm(
  "finite_field_conjugates_zero",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> (Conj #0 = {#0})``,
  metis_tac[finite_subfield_card_pos, ring_conjugates_zero, finite_field_is_field, field_is_ring]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==> !n. (conj x n = #0) <=> (x = #0) *)
(* Proof:
   Let m = CARD B.
   Then 0 < m                      by finite_subfield_card_pos
    and 0 < m ** n                 by EXP_POS
   Note conj x n = x ** m ** n     by ring_conjugate_def
   Thus conj x n = #0 <=> x = #0   by field_exp_eq_zero
*)
val finite_field_conjugate_eq_zero = store_thm(
  "finite_field_conjugate_eq_zero",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> !n. (conj x n = #0) <=> (x = #0)``,
  rpt (stripDup[FiniteField_def]) >>
  rw[ring_conjugate_def] >>
  qabbrev_tac `m = CARD B` >>
  `0 < m ** n` by metis_tac[finite_subfield_card_pos, EXP_POS] >>
  `m ** n <> 0` by decide_tac >>
  rw[field_exp_eq_zero]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==> (#0 IN (Conj x) <=> (x = #0)) *)
(* Proof:
       #0 IN Conj x
   <=> ?n. #0 = conj x n    by ring_conjugates_member
   <=> x = #0               by finite_field_conjugate_eq_zero
*)
val finite_field_conjugates_has_zero = store_thm(
  "finite_field_conjugates_has_zero",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> (#0 IN (Conj x) <=> (x = #0))``,
  metis_tac[ring_conjugates_member, finite_field_conjugate_eq_zero]);

(* Theorem: FiniteField r /\ s <<= r ==>
            !x. x IN R ==> (Conj x) SUBSET (IMAGE (conj x) (count (r <:> s))) *)
(* Proof:
   Let m = CARD B, d = (r <:> s).
   Then 0 < d                                      by finite_field_over_subfield_dim_pos
       y IN Conj x
   ==> ?n. y = conj x n                            by ring_conjugates_member
   ==>     y = conj x (n MOD d)                    by finite_field_conjugate_eqn
   Since n MOD d < d                               by MOD_LESS
      so y IN IMAGE (conj x) (count d)             by IN_IMAGE, IN_COUNT
   or (Conj x) SUBSET (IMAGE (conj x) (count d))   by SUBSET_DEF
*)
val finite_field_conjugates_subset = store_thm(
  "finite_field_conjugates_subset",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !x. x IN R ==> (Conj x) SUBSET (IMAGE (conj x) (count (r <:> s)))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = CARD B` >>
  qabbrev_tac `d = (r <:> s)` >>
  `0 < d` by rw[finite_field_over_subfield_dim_pos, Abbr`d`] >>
  rw[SUBSET_DEF] >>
  metis_tac[ring_conjugates_member, finite_field_conjugate_eqn, MOD_LESS]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==> CARD (Conj x) <= (r <:> s) *)
(* Proof:
   Let c = count (r <:> s).
   Then (Conj x) SUBSET (IMAGE (conj x) c)         by finite_field_conjugates_subset
    Now FINITE c                                   by FINITE_COUNT
     so FINITE (IMAGE (conj x) c)                  by IMAGE_FINITE
   thus CARD (Conj x) <= CARD (IMAGE (conj x) c)   by CARD_SUBSET
                      <= CARD c                    by CARD_IMAGE
                       = (r <:> s)                 by CARD_COUNT
*)
val finite_field_conjugates_card_upper = store_thm(
  "finite_field_conjugates_card_upper",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> CARD (Conj x) <= (r <:> s)``,
  rpt strip_tac >>
  qabbrev_tac `c = count (r <:> s)` >>
  `(Conj x) SUBSET (IMAGE (conj x) c)` by rw[finite_field_conjugates_subset, Abbr`c`] >>
  `FINITE (IMAGE (conj x) c)` by rw[Abbr`c`] >>
  `CARD (Conj x) <= CARD (IMAGE (conj x) c)` by rw[CARD_SUBSET] >>
  `CARD (IMAGE (conj x) c) <= CARD c` by rw[CARD_IMAGE, Abbr`c`] >>
  `CARD c = (r <:> s)` by rw[Abbr`c`] >>
  decide_tac);

(* Theorem: FiniteField r /\ s <<= r ==>
            !x. x IN R ==> SURJ (\z. z ** CARD B) (Conj x) (Conj x) *)
(* Proof:
   By SURJ_DEF, this is to show:
   (1) z IN Conj x ==> z ** CARD B IN Conj x, true by ring_conjugate_exp_subfield_card
   (2) x' IN Conj x ==> ?z. z IN Conj x /\ (z ** CARD B = x')
       Let m = CARD B, d = (r <:> s).
       Then (CARD R = m ** d) /\ 0 < d   by finite_subfield_card_eqn
       By ring_conjugates_member, ring_conjugate_def, this is to show:
          ?z. (?n'. z = x ** m ** n') /\ (z ** m = x ** m ** n)
       If n = 0, goal reduces to:
              ?z. (?n'. z = x ** m ** n') /\ (z ** m = x)  by EXP
          Since 0 < d, let d = SUC k     by num_CASES
          Take z = x ** m ** k, n' = k.
            z ** m
          = (x ** m ** k) ** m    by z = x ** m ** k
          = x ** (m ** k * m)     by ring_exp_mult
          = x ** (m * m ** k)     by MULT_COMM
          = x ** (m ** SUC k)     by EXP
          = x ** (m ** d)         by d = SUC k
          = x ** CARD R           by CARD R = m ** d
          = x                     by finite_field_fermat_thm

       If n <> 0,
          Then n = SUC k for some k   by num_CASES
          goal is: ?z. (?n'. z = x ** m ** k) /\ (z ** m = x ** m ** SUC k)
          Take z = x ** m ** k, n' = k.
            z ** m
          = (x ** m ** k) ** m    by z = x ** m ** k
          = x ** (m ** k * m)     by ring_exp_mult
          = x ** (m * m ** k)     by MULT_COMM
          = x ** (m ** SUC k)     by EXP
*)
val finite_field_conjugates_exp_surj = store_thm(
  "finite_field_conjugates_exp_surj",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !x. x IN R ==> SURJ (\z. z ** CARD B) (Conj x) (Conj x)``,
  rpt (stripDup[FiniteField_def]) >>
  rw[SURJ_DEF] >-
  rw[ring_conjugate_exp_subfield_card] >>
  qabbrev_tac `m = CARD B` >>
  qabbrev_tac `d = (r <:> s)` >>
  `(CARD R = m ** d) /\ 0 < d` by rw[finite_subfield_card_eqn, Abbr`m`, Abbr`d`] >>
  fs[ring_conjugates_member, ring_conjugate_def] >>
  Cases_on `n` >| [
    rw[EXP] >>
    `d <> 0` by decide_tac >>
    `?k. d = SUC k` by metis_tac[num_CASES] >>
    qexists_tac `x ** m ** k` >>
    rpt strip_tac >-
    metis_tac[] >>
    `(x ** m ** k) ** m = x ** (m ** k * m)` by rw[ring_exp_mult] >>
    `_ = x ** (m ** SUC k)` by rw_tac std_ss[EXP, MULT_COMM] >>
    `_ = x ** CARD R` by rw[] >>
    `_ = x` by rw[finite_field_fermat_thm] >>
    rw[],
    qexists_tac `x ** m ** n'` >>
    rpt strip_tac >-
    metis_tac[] >>
    `x ** m ** SUC n' = x ** (m ** n' * m)` by rw_tac std_ss[EXP, MULT_COMM] >>
    `_ = (x ** m ** n') ** m` by rw[ring_exp_mult] >>
    rw[]
  ]);

(* Theorem: FiniteField r /\ s <<= r ==>
            !x. x IN R ==> (IMAGE (\z. z ** CARD B) (Conj x) = Conj x) *)
(* Proof:
   Since SURJ (\z. z ** CARD B) (Conj x) (Conj x)   by finite_field_conjugates_exp_surj
   Hence IMAGE (\z. z ** CARD B) (Conj x) = Conj x  by IMAGE_SURJ
*)
val finite_field_conjugates_exp_image_eq = store_thm(
  "finite_field_conjugates_exp_image_eq",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !x. x IN R ==> (IMAGE (\z. z ** CARD B) (Conj x) = Conj x)``,
  rw[finite_field_conjugates_exp_surj, GSYM IMAGE_SURJ]);

(* ------------------------------------------------------------------------- *)
(* Conjugate Properties                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r /\ s <<= r ==> !p. Poly s p ==>
            !x. x IN R /\ root p x ==> !n. root p (conj x n) *)
(* Proof:
   Since FiniteField r
     ==> FiniteField s                  by subfield_finite_field
     ==> 0 < CARD B                     by finite_field_card_pos
   Given root p x
     ==> eval p x = #0                  by poly_root_def
     Now eval p (conj x n)
       = eval p (x ** CARD B ** n)      by ring_conjugate_def
       = (eval p x) ** CARD B ** n      by subfield_poly_eval_freshman_all
       = #0 ** CARD B ** n              by above
       = #0                             by field_zero_exp, CARD B <> 0
   Hence root p (conj x n)              by poly_root_def
*)
val subfield_poly_conjugate_roots = store_thm(
  "subfield_poly_conjugate_roots",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !p. Poly s p ==>
   !x. x IN R /\ root p x ==> !n. root p (conj x n)``,
  rw[poly_root_def, ring_conjugate_def, GSYM subfield_poly_eval_freshman_all] >>
  `FiniteField s` by metis_tac[subfield_finite_field] >>
  `0 < CARD B` by rw[finite_field_card_pos] >>
  `CARD B <> 0` by decide_tac >>
  rw[field_zero_exp, finite_field_is_field]);

(* Theorem: FiniteField r ==> !s. s <<= r ==> !x. x IN R ==> (Conj x) SUBSET (roots (minimal x)) *)
(* Proof:
   Let p = minimal x.
   Then Poly s p                 by poly_minimal_spoly
    and root p x                 by poly_minimal_has_element_root
   thus !n. root p (conj x n)    by subfield_poly_conjugate_roots
   Therefore,
        !z. z IN (Conj x) ==> z IN R /\ root p z   by ring_conjugates_member, ring_conjugate_element
     or !z. z IN (Conj x) ==> z IN roots p         by poly_roots_member
   Hence (Conj x) SUBSET roots p                   by SUBSET_DEF
*)
val subfield_conjugates_are_minimal_roots = store_thm(
  "subfield_conjugates_are_minimal_roots",
  ``!r:'a field. FiniteField r ==> !s. s <<= r ==> !x. x IN R ==> (Conj x) SUBSET (roots (minimal x))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `p = minimal x` >>
  `Poly s p` by rw[poly_minimal_spoly, Abbr`p`] >>
  `root p x` by rw[poly_minimal_has_element_root, Abbr`p`] >>
  `!n. root p (conj x n)` by rw[subfield_poly_conjugate_roots, Abbr`p`] >>
  `Ring r` by rw[] >>
  `!z. z IN (Conj x) ==> z IN R /\ root p z` by metis_tac[ring_conjugates_member, ring_conjugate_element] >>
  rw[poly_roots_member, SUBSET_DEF]);

(*
This is a weak result. To get: roots (minimal x) = Conj x
Either count (Conj x) and get degree x, or
This helps establish PPROD (IMAGE factor (Conj x)) pdivides p.
Then later, with p pdivides (PPROD (IMAGE factor (Conj x))) due to it being a Poly s.
*)

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==> !n. forder (conj x n) = forder x *)
(* Proof:
   Note FiniteField s               by subfield_finite_field
   If x = #0,
      Since 0 < CARD B              by finite_field_card_pos
      !n. conj #0 n = #0            by ring_conjugate_zero
      Hence equality is trivially true.
   If x <> #0,
      then x IN R+                  by field_nonzero_eq
       Note coprime a (CARD B ** n) by finite_field_order_coprime, x IN R+

      Since Group f*                by field_mult_group
        and x IN F*                 by field_mult_carrier
      Hence order r.prod (f*.exp x (CARD B ** n)) * (gcd a (CARD B ** n)) = a   by group_order_power
         or order r.prod (x ** CARD B ** n) * (gcd a (CARD B ** n)) = a         by field_nonzero_exp
         or order r.prod (x ** CARD B ** n) * 1 = a    by coprime a (CARD B) ** n
         or order r.prod (x ** CARD B ** n) = a        by MULT_RIGHT_1
         or       forder (conj x n) = forder x         by ring_conjugate_def
*)
val finite_field_conjugate_order = store_thm(
  "finite_field_conjugate_order",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> !n. forder (conj x n) = forder x``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r` by rw[] >>
  `FiniteField s` by metis_tac[subfield_finite_field] >>
  Cases_on `x = #0` >-
  rw_tac std_ss[finite_field_card_pos, ring_conjugate_zero] >>
  `x IN R+` by rw[field_nonzero_eq] >>
  qabbrev_tac `a = forder x` >>
  `coprime a (CARD B ** n)` by rw[finite_field_order_coprime, Abbr`a`] >>
  `Group f*` by rw[field_mult_group] >>
  `x IN F*` by rw[field_mult_carrier] >>
  metis_tac[group_order_power, field_nonzero_exp, ring_conjugate_def, MULT_RIGHT_1]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==> !n. forder (conj x n) = forder x *)
(* Proof:
   Since y IN (Conj x)
     ==> ?n. y = conj x n     by ring_conjugates_member
      so forder y = forder x  by finite_field_conjugate_order
*)
val finite_field_conjugates_order = store_thm(
  "finite_field_conjugates_order",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> !y. y IN (Conj x) ==> (forder y = forder x)``,
  metis_tac[ring_conjugates_member, finite_field_conjugate_order]);

(* Theorem: FiniteField r /\ s <<= r ==>
            !x n. x IN (orders f* n) ==> (Conj x) SUBSET (orders f* n) *)
(* Proof:
   By SUBSET_DEF, this is to show:
      !x. x IN orders f* n /\ x' IN Conj x ==> x' IN orders f* n
   Note x IN (orders f* n)
    ==> x IN R                  by field_orders_element
   Also x' IN Conj x
    ==> forder x' = forder x    by finite_field_conjugates_order, x IN R
    Now x IN R+                 by field_orders_nonzero_element
     so x <> #0                 by field_nonzero_eq
   Note x' IN R                 by ring_conjugates_member_element
     so x' <> #0                by field_order_eq_0
     or x' IN R+                by field_nonzero_eq
    ==> x' IN orders f* n       by field_orders_element_property
*)
val finite_field_conjugates_subset_orders = store_thm(
  "finite_field_conjugates_subset_orders",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !x n. x IN (orders f* n) ==> (Conj x) SUBSET (orders f* n)``,
  rpt (stripDup[FiniteField_def]) >>
  rw[SUBSET_DEF] >>
  `x IN R` by metis_tac[field_orders_element] >>
  `forder x' = forder x` by metis_tac[finite_field_conjugates_order] >>
  `x IN R+` by metis_tac[field_orders_nonzero_element] >>
  `x' IN R` by metis_tac[ring_conjugates_member_element, field_is_ring] >>
  `x' IN R+` by metis_tac[field_nonzero_eq, field_order_eq_0] >>
  metis_tac[field_orders_element_property]);

(* ------------------------------------------------------------------------- *)
(* Product of Conjugate Factors                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteRing r ==> !x. x IN R ==> FINITE (IMAGE factor (Conj x)) *)
(* Proof:
   Since FiniteRing r /\ x IN R ==> FINITE (Conj x)  by ring_conjugates_finite
   Hence FINITE (IMAGE factor (Conj x))              by IMAGE_FINITE
*)
val conjugate_factors_finite = store_thm(
  "conjugate_factors_finite",
  ``!(r s):'a ring. FiniteRing r ==> !x. x IN R ==> FINITE (IMAGE factor (Conj x))``,
  rw[ring_conjugates_finite]);

(* Theorem: !x p. p IN (IMAGE factor (Conj x)) ==> ?n. p = factor (conj x n) *)
(* Proof:
\      p IN (IMAGE factor (Conj x))
   <=> ?y. (p = factor y) /\ y IN (Conj x)   by IN_IMAGE
   <=> ?n. p = factor (conj x n)             by ring_conjugates_member
*)
val conjugate_factors_member = store_thm(
  "conjugate_factors_member",
  ``!(r s):'a ring. !x p. p IN (IMAGE factor (Conj x)) ==> ?n. p = factor (conj x n)``,
  metis_tac[ring_conjugates_member, IN_IMAGE]);

(* Theorem: Ring r /\ #1 <> #0 ==> !x. x IN R ==>
            !p. p IN (IMAGE factor (Conj x)) ==> poly p /\ (deg p = 1) /\ (lead p = #1) /\ monic p *)
(* Proof:
    Note p IN (IMAGE factor (Conj x))
     ==> ?n. p = factor (conj x n)     by conjugate_factors_member
     Now x IN R ==> conj x n IN R      by ring_conjugate_element
   Hence poly p                        by poly_factor_poly, #1 <> #0
     and deg p = 1                     by poly_deg_factor, #1 <> #0
     and lead p = #1                   by poly_factor_lead, #1 <> #0
     and monic p                       by poly_factor_monic, #1 <> #0
*)
val conjugate_factors_member_property = store_thm(
  "conjugate_factors_member_property",
  ``!(r s):'a ring. Ring r /\ #1 <> #0 ==> !x. x IN R ==>
   !p. p IN (IMAGE factor (Conj x)) ==> poly p /\ (deg p = 1) /\ (lead p = #1) /\ monic p``,
  ntac 7 strip_tac >>
  `?n. p = factor (conj x n)` by rw[conjugate_factors_member] >>
  `conj x n IN R` by rw[ring_conjugate_element] >>
  rw[poly_factor_poly, poly_factor_deg, poly_factor_lead, poly_factor_monic]);

(* Theorem: FiniteField r ==> !x. x IN R ==> monic (PIFACTOR (Conj x)) *)
(* Proof:
   Note poly (PIFACTOR (Conj x))
    <=> poly (PPROD (IMAGE factor (Conj x))           by notation
    Now FiniteRing r                                  by finite_field_is_finite_ring
     so FINITE (IMAGE factor (Conj x))                by conjugate_factors_finite, FiniteRing r
    and !p. p IN (IMAGE factor (Conj x)) ==> monic p  by conjugate_factors_member_property, Ring r, #1 <> #0
   Hence monic (PIFACTOR (Conj x))                    by poly_monic_prod_set_monic
*)
val poly_prod_conjugate_factors_monic = store_thm(
  "poly_prod_conjugate_factors_monic",
  ``!(r s):'a field. FiniteField r ==> !x. x IN R ==> monic (PIFACTOR (Conj x))``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteRing r` by rw[finite_field_is_finite_ring] >>
  `FINITE (IMAGE factor (Conj x))` by rw[conjugate_factors_finite] >>
  `Ring r /\ #1 <> #0` by rw[] >>
  metis_tac[poly_monic_prod_set_monic, conjugate_factors_member_property]);

(* Theorem: FiniteField r ==> !x. x IN R ==> poly (PIFACTOR (Conj x)) *)
(* Proof: by poly_prod_conjugate_factors_monic, poly_monic_poly *)
val poly_prod_conjugate_factors_poly = store_thm(
  "poly_prod_conjugate_factors_poly",
  ``!(r s):'a field. FiniteField r ==> !x. x IN R ==> poly (PIFACTOR (Conj x))``,
  rw[poly_prod_conjugate_factors_monic]);

(* Theorem: FiniteField r ==> !x. x IN R ==> (lead (PIFACTOR (Conj x)) = #1) *)
(* Proof: by poly_prod_conjugate_factors_monic, poly_monic_lead *)
val poly_prod_conjugate_factors_lead = store_thm(
  "poly_prod_conjugate_factors_lead",
  ``!(r s):'a field. FiniteField r ==> !x. x IN R ==> (lead (PIFACTOR (Conj x)) = #1)``,
  rw[poly_prod_conjugate_factors_monic]);

(* Theorem: FiniteField r ==> !x. x IN R ==> (deg (PIFACTOR (Conj x)) = CARD (Conj x)) *)
(* Proof:
    Note FiniteField r ==> FiniteRing r            by finite_field_is_finite_ring
      so FINITE (Conj x)                           by ring_conjugates_finite
     and (Conj x) SUBSET R                         by ring_conjugates_subset
   Hence deg (PIFACTOR (Conj x)) = CARD (Conj x)   by poly_prod_factors_deg
*)
val poly_prod_conjugate_factors_deg = store_thm(
  "poly_prod_conjugate_factors_deg",
  ``!(r s):'a field. FiniteField r ==> !x. x IN R ==> (deg (PIFACTOR (Conj x)) = CARD (Conj x))``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteRing r` by rw[finite_field_is_finite_ring] >>
  `FINITE (Conj x)` by rw[ring_conjugates_finite] >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `(Conj x) SUBSET R` by rw[ring_conjugates_subset] >>
  rw[poly_prod_factors_deg]);

(* Theorem: FiniteField r ==> !x. x IN R ==> (roots (PIFACTOR (Conj x)) = Conj x) *)
(* Proof:
    Note FiniteField r ==> FiniteRing r            by finite_field_is_finite_ring
      so FINITE (Conj x)                           by ring_conjugates_finite
     and (Conj x) SUBSET R                         by ring_conjugates_subset
   Hence roots (PIFACTOR (Conj x)) = Conj x        by poly_prod_factors_roots
*)
val poly_prod_conjugate_factors_roots = store_thm(
  "poly_prod_conjugate_factors_roots",
  ``!(r s):'a field. FiniteField r ==> !x. x IN R ==> (roots (PIFACTOR (Conj x)) = Conj x)``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteRing r` by rw[finite_field_is_finite_ring] >>
  `FINITE (Conj x)` by rw[ring_conjugates_finite] >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `(Conj x) SUBSET R` by rw[ring_conjugates_subset] >>
  rw[poly_prod_factors_roots]);

(* ------------------------------------------------------------------------- *)
(* Roots of Irreducible                                                      *)
(* ------------------------------------------------------------------------- *)

(*
Let F_q be a finite field, and h an irreducible in F_q[X], and m = deg h.
Then h has a root X in F_{q^m}.
Moreover, all the roots of h are simple (i.e. multiplicity = 1),
and the roots are given by the m distinct elements: X, X^q, X^{q^2}, ..., X^{q^m-1} of F_{q^m}.
*)

(* Key: If z is a root of h, z^q is also a root of h. *)

(* ------------------------------------------------------------------------- *)
(* Product of Conjugates is Subfield Polynomial                              *)
(* ------------------------------------------------------------------------- *)

(* Idea:
   We have:
   |- !r. FiniteField r ==> (master (CARD R) = PIFACTOR R)  by poly_master_eq_root_factor_product
   |- !r. FiniteField r ==> !s. s <<= r ==>
      !n. 0 < n ==> (Master s (CARD B ** n) = poly_prod_set s (monic_irreducibles_bounded s n))
                                                                  by poly_master_subfield_factors
   Since:
   |- !r. FiniteField r ==> !s. s <<= r ==> ?d. 0 < d /\ (CARD R = CARD B ** d)
                                                                  by finite_field_card_subfield
   So putting this dimension d (0 < d) to poly_master_subfield_factors,
            Master s (CARD R) = poly_prod_set s (monic_irreducibles_bounded s d))
   or        PIFACTOR R = poly_prod_set s (monic_irreducibles_bounded s d))

   Use this identity to deduce that:
      monic p /\ ipoly p ==> p = PIFACTOR (subset of R)
   Then the (subset of R) will be the roots of p in r,
   or (subset of R = roots p), which should be a set of conjugates.

   If deg p = d, the set of conjugates are all primitives of r.
*)

(* Theorem: FiniteField r ==> !x y. x IN R /\ y IN R ==>
            !n. ((factor x) ** (char r) ** n = (factor y) ** (char r) ** n) <=> (x = y) *)
(* Proof:
   If part: (factor x) ** (char r) ** n = (factor y) ** (char r) ** n ==> x = y
      Let m = (char r) ** n.
          eval ((factor x) ** m) #0
        = (eval (factor x) #0) ** m        by poly_eval_exp
        = (#0 - x) ** m                    by poly_eval_factor
        = (-x) ** m                        by field_zero_sub
      Similarly,
          eval ((factor y) ** m) #0
        = (-y) ** m
      Thus     (-x) ** m = (-y) ** m
      Since -x IN R /\ -y IN R             by field_neg_element
         so            -x = -y             by finite_field_element_eq_condition
         or             x = y              by field_neg_neg

   Only-if part: x = y ==> (factor x) ** (char r) ** n = (factor y) ** (char r) ** n
      This is trivially true.
*)
val poly_factor_exp_eq = store_thm(
  "poly_factor_exp_eq",
  ``!r:'a field. FiniteField r ==> !x y. x IN R /\ y IN R ==>
   !n. ((factor x) ** (char r) ** n = (factor y) ** (char r) ** n) <=> (x = y)``,
  rpt (stripDup[FiniteField_def]) >>
  rw[EQ_IMP_THM] >>
  qabbrev_tac `m = (char r) ** n` >>
  `!c. c IN R ==> (eval ((factor c) ** m) #0 = (-c) ** m)` by rw[poly_factor_poly, poly_eval_exp, poly_eval_factor] >>
  metis_tac[field_neg_element, finite_field_element_eq_condition, field_neg_neg]);

(* Theorem: FiniteField r ==> !s. s SUBSET R ==>
            !n. INJ (\p. p ** (char r) ** n) (IMAGE factor s) univ(:'a poly) *)
(* Proof:
   Let m = (char r) ** n
   By INJ_DEF and IN_IMAGE, this is to show:
   (1) x IN s ==> factor x ** m IN univ(:'a poly)
       Note x IN R                             by SUBSET_DEF
        ==> poly (factor x)                    by poly_factor_poly
        ==> poly (factor x ** m)               by poly_exp_poly
        ==> (factor x) ** m IN univ(:'a poly)  by IN_UNIV
   (2) x IN s /\ x' IN s /\ factor x ** m = factor x' ** m ==> factor x = factor x'
       Note x IN R /\ x' IN R                  by SUBSET_DEF
       The result follows                      by poly_factor_exp_eq
*)
val poly_factor_map_exp_inj = store_thm(
  "poly_factor_map_exp_inj",
  ``!r:'a field. FiniteField r ==> !s. s SUBSET R ==>
   !n. INJ (\p. p ** (char r) ** n) (IMAGE factor s) univ(:'a poly)``,
  rpt (stripDup[FiniteField_def]) >>
  rw[INJ_DEF] >>
  metis_tac[poly_factor_exp_eq, SUBSET_DEF]);

(* Theorem: FiniteField r ==> !c. c IN R ==>
            !n. (factor c) ** (char r) ** n = peval (factor (c ** (char r) ** n)) (X ** (char r) ** n) *)
(* Proof:
   Let m = (char r) ** n.
     (factor c) ** m
   = (X - c * |1|) ** m                    by poly_factor_alt
   = X ** m - (c * |1|) ** m               by poly_freshman_all_sub, prime (char r)
   = X ** m - (c ** m) * |1| ** m          by poly_cmult_exp
   = X ** m - (c ** m) * |1|               by poly_one_exp
   = peval (factor (c ** m)) (X ** m)      by poly_peval_factor_alt, c ** m IN R
*)
val poly_factor_exp_to_peval_factor = store_thm(
  "poly_factor_exp_to_peval_factor",
  ``!r:'a field. FiniteField r ==> !c. c IN R ==>
   !n. (factor c) ** (char r) ** n = peval (factor (c ** (char r) ** n)) (X ** (char r) ** n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = (char r) ** n` >>
  `prime (char r)` by rw[finite_field_char] >>
  `c ** m IN R` by rw[] >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `poly X /\ poly (X ** m) /\ poly |1| /\ poly (c * |1|)` by rw[] >>
  rw_tac std_ss[poly_factor_alt, poly_freshman_all_sub, poly_cmult_exp, poly_one_exp, poly_peval_factor_alt, Abbr`m`]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==>
            INJ (\p. p ** (CARD B)) (IMAGE factor (Conj x)) univ(:'a poly) *)
(* Proof:
   Note ?d. 0 < d /\ (CARD B = (char r) ** d)   by finite_field_subfield_card
   Since Conj x SUBSET R                        by ring_conjugates_subset
   The result follows                           by poly_factor_map_exp_inj
*)
val poly_factor_conjugates_exp_inj = store_thm(
  "poly_factor_conjugates_exp_inj",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==>
   INJ (\p. p ** (CARD B)) (IMAGE factor (Conj x)) univ(:'a poly)``,
  metis_tac[finite_field_subfield_card, ring_conjugates_subset,
             poly_factor_map_exp_inj, finite_field_is_field, field_is_ring]);

(* Theorem: Ring r /\ #1 <> #0 ==> !x. x IN R ==> !q. poly q ==>
            INJ (\p. peval p q) (IMAGE factor (Conj x)) univ(:'a poly) *)
(* Proof:
   Since Conj x SUBSET R    by ring_conjugates_subset
   The result follows       by poly_peval_factor_map_inj
*)
val poly_factor_conjugates_peval_inj = store_thm(
  "poly_factor_conjugates_peval_inj",
  ``!(r s):'a ring. Ring r /\ #1 <> #0 ==> !x. x IN R ==> !q. poly q ==>
   INJ (\p. peval p q) (IMAGE factor (Conj x)) univ(:'a poly)``,
  rw[poly_peval_factor_map_inj, ring_conjugates_subset]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==>
            (IMAGE ((\p. p ** (CARD B)) o factor) (Conj x) =
             IMAGE ((\p. peval p (X ** (CARD B))) o factor) (Conj x)) *)
(* Proof:
   Let m = CARD B.
   Then ?d. 0 < d /\ (m = (char r) ** d)   by finite_field_subfield_card
   By EXTENSION, IN_IMAGE, this is to show:
   (1) x'' IN Conj x ==> ?x'''. (factor x'' ** m = peval (factor x''') (X ** m)) /\ x''' IN Conj x
       Note x'' ** m IN Conj x             by ring_conjugate_exp_subfield_card
        and x'' IN R                       by ring_conjugates_member_element
       Take x''' = x'' ** m, then true     by poly_factor_exp_to_peval_factor
   (2) x'' IN Conj x ==> ?x'''. (peval (factor x'') (X ** m) = factor x''' ** m) /\ x''' IN Conj x
       Let f = (\z:'a. z ** m).
       Then SURJ f (Conj x) (Conj x)       by finite_field_conjugates_exp_surj
        ==> ?z. z IN Conj x /\ (x'' = f z) by SURJ_DEF
         or x'' = z ** m                   by function application
        Now z IN Conj x ==> z IN R         by ring_conjugates_member_element
       Take x''' = z, then true            by poly_factor_exp_to_peval_factor

   Note: This proof is tricky in (2), using finite_field_conjugates_exp_surj to find the candidate.
         Both (1) and (2) uses poly_factor_exp_to_peval_factor.
*)
val finite_field_conjugates_exp_to_peval_images = store_thm(
  "finite_field_conjugates_exp_to_peval_images",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==>
    (IMAGE ((\p. p ** (CARD B)) o factor) (Conj x) = IMAGE ((\p. peval p (X ** (CARD B))) o factor) (Conj x))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r` by rw[] >>
  qabbrev_tac `m = CARD B` >>
  rw_tac std_ss[IN_IMAGE, EXTENSION, EQ_IMP_THM] >| [
    `x'' ** m IN Conj x` by rw[ring_conjugate_exp_subfield_card, Abbr`m`] >>
    `x'' IN R` by metis_tac[ring_conjugates_member_element] >>
    metis_tac[poly_factor_exp_to_peval_factor, finite_field_subfield_card],
    qabbrev_tac `f = (\z:'a. z ** m)` >>
    `SURJ f (Conj x) (Conj x)` by rw[finite_field_conjugates_exp_surj, Abbr`f`, Abbr`m`] >>
    `?z. z IN Conj x /\ (x'' = f z)` by metis_tac[SURJ_DEF] >>
    `_ = z ** m` by rw[Abbr`f`] >>
    `z IN R` by metis_tac[ring_conjugates_member_element] >>
    metis_tac[poly_factor_exp_to_peval_factor, finite_field_subfield_card]
  ]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==> Poly s (PIFACTOR (Conj x)) *)
(* Proof:
   Let p = PIFACTOR (Conj x), m = CARD B.
   Note ?d. 0 < d /\ (m = (char r) ** d)       by finite_field_subfield_card
   Let ss = IMAGE factor (Conj x), q = X ** m.

   Step 1: compute p ** m
    Note FINITE ss                             by ring_conjugates_finite, finite_field_is_finite_ring
     and pset ss                               by ring_conjugates_member_element, poly_factor_poly
    Also poly p                                by poly_prod_set_poly
    thus INJ (\p. p ** m) ss univ(:'a poly)    by poly_factor_conjugates_exp_inj
         p ** m
       = (PPROD ss) ** m                       by notation
       = PPIMAGE (\p. p ** m) ss               by poly_prod_set_exp, INJ (\p. p ** m) ss univ(:'a poly)

   Step 2: compute peval p q
    Note poly q                                by poly_X, poly_exp_poly
     and INJ (\p. peval p q) ss univ(:'a poly) by poly_factor_conjugates_peval_inj
         peval p q
       = PPIMAGE (\p. peval p q) ss            by poly_peval_poly_prod, INJ (\p. peval p q) ss univ(:'a poly)

   Step 3: combine and conclude

       p ** m
     = (PIFACTOR (Conj x)) ** m                                by notation
     = PPIMAGE (\p. p ** m) (IMAGE factor (Conj x))            by poly_prod_set_exp, claim 1
     = PPIMAGE ((\p. p ** m) o factor) (Conj x)                by IMAGE_COMPOSE
     = PPIMAGE ((\p. peval p (X ** m)) o factor) (Conj x)      by finite_field_conjugates_exp_to_peval_images
     = PPIMAGE (\p. peval p (X ** m)) (IMAGE factor (Conj x))  by IMAGE_COMPOSE
     = peval (PIFACTOR (Conj x)) (X ** m)                      by poly_peval_poly_prod
     = peval p (X ** m)                                        by notation

    Hence Poly s p                             by subfield_poly_condition
*)
val poly_prod_factors_conjugates_subfield_poly = store_thm(
  "poly_prod_factors_conjugates_subfield_poly",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> Poly s (PIFACTOR (Conj x))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `p = PIFACTOR (Conj x)` >>
  qabbrev_tac `m = CARD B` >>
  `?d. 0 < d /\ (m = (char r) ** d)` by rw[finite_field_subfield_card, Abbr`m`] >>
  qabbrev_tac `ss = IMAGE factor (Conj x)` >>
  `FiniteRing r` by rw[finite_field_is_finite_ring] >>
  `FINITE ss` by rw[ring_conjugates_finite, Abbr`ss`] >>
  `pset ss` by
  (rw[Abbr`ss`] >>
  `Ring r /\ #1 <> #0` by rw[] >>
  metis_tac[ring_conjugates_member_element, poly_factor_poly]) >>
  `poly p` by rw[poly_prod_set_poly, Abbr`p`] >>
  `INJ (\p. p ** m) ss univ(:'a poly)` by rw[poly_factor_conjugates_exp_inj, Abbr`m`, Abbr`ss`] >>
  `p ** m = (PPROD ss) ** m` by rw[Abbr`ss`] >>
  `_ = PPIMAGE (\p. p ** m) ss` by rw[poly_prod_set_exp] >>
  `_ = PPIMAGE ((\p. p ** m) o factor) (Conj x)` by rw[IMAGE_COMPOSE, Abbr`ss`] >>
  qabbrev_tac `q = X ** m` >>
  `poly q` by rw[Abbr`q`] >>
  `INJ (\p. peval p q) ss univ(:'a poly)` by rw[poly_factor_conjugates_peval_inj, Abbr`ss`] >>
  `peval p q = PPIMAGE (\p. peval p q) ss` by rw[poly_peval_poly_prod, Abbr`p`] >>
  `_ = PPIMAGE ((\p. peval p q) o factor) (Conj x)` by rw[IMAGE_COMPOSE, Abbr`ss`] >>
  `p ** m = peval p q` by metis_tac[finite_field_conjugates_exp_to_peval_images] >>
  metis_tac[subfield_poly_condition]);

(* This is a major milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Minimal Polynomial as Product of Conjugates                               *)
(* ------------------------------------------------------------------------- *)

(* Idea:
From poly_minimal_spoly:
|- !r. FiniteField r ==> !s. s <<= r ==> !x. x IN R ==> Poly s (minimal x)
we know that (minimal x) is a subfield poly, with x itself as a root:
poly_minimal_has_element_root
|- !r. FiniteField r ==> !s. s <<= r ==> !x. x IN R ==> root (minimal x) x

From ffConjugate, we know the roots of a subfield poly:
subfield_poly_conjugate_roots
|- !r s. FiniteField r /\ s <<= r ==>
   !p. Poly s p ==> !x. x IN R /\ root p x ==> !n. root p (conj x n)
and the product of such conjuate factors: (PIFACTOR (Conj x)) has a number of useful properties:
poly_prod_conjugate_factors_monic   |- !r s. FiniteField r ==> !x. x IN R ==> monic (PIFACTOR (Conj x))
poly_prod_conjugate_factors_poly    |- !r s. FiniteField r ==> !x. x IN R ==> poly (PIFACTOR (Conj x))
poly_prod_conjugate_factors_lead    |- !r s. FiniteField r ==> !x. x IN R ==> (lead (PIFACTOR (Conj x)) = #1)
poly_prod_conjugate_factors_deg     |- !r s. FiniteField r ==> !x. x IN R ==> (deg (PIFACTOR (Conj x)) = CARD (Conj x))

Combining these two, we should be able to assert:
minimal x = PIFACTOR (Conj x), giving an explicit expression of the minimal polynomial.
*)

(* Note:
  The following theorem is easy (?) if we know:  (Conj x) = roots (minimal x)
  However, we actually want to derive this result from the theorem!
  Therefore, we need a different approach. The idea is:
  (1) (Conj x) SUBSET roots (minimal x)             by subfield_conjugates_are_minimal_roots
  (2) (PIFACTOR (Conj x)) pdivides (minimal x)      by poly_prod_factors_divides
  (3) (minimal x) pdivides (PIFACTOR (Conj x))      by poly_minimal_divides_subfield_poly
  With both monic polynomials, they must be equal   by poly_monic_divides_antisymmetric
*)

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==> (minimal x = PIFACTOR (Conj x)) *)
(* Proof:
   Let p = minimal x, q = PIFACTOR (Conj x).

   Step 1: show q pdivides p
   Note poly p                       by poly_minimal_poly
    and monic p                      by poly_minimal_monic
    and (Conj x) SUBSET (roots p)    by subfield_conjugates_are_minimal_roots
   Then monic q                      by poly_prod_conjugate_factors_monic
   thus q pdivides p                 by poly_prod_factors_divides

   Step 2: show p pdivides q
    Now Poly s q                     by poly_prod_factors_conjugates_subfield_poly
   Note x IN Conj x                  by ring_conjugates_has_self
    and Conj x = roots q             by poly_prod_conjugate_factors_roots
     so root q x                     by poly_roots_member
   thus p pdivides q                 by poly_minimal_divides_subfield_poly, Poly s q, root q x

  Step 3: conclude
  Hence p = q                        by poly_monic_divides_antisymmetric
*)
val poly_minimal_eq_factors_conjugates = store_thm(
  "poly_minimal_eq_factors_conjugates",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> (minimal x = PIFACTOR (Conj x))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `p = minimal x` >>
  qabbrev_tac `q = PIFACTOR (Conj x)` >>
  `monic p /\ poly p` by rw[poly_minimal_monic, Abbr`p`] >>
  `(Conj x) SUBSET (roots p)` by rw[subfield_conjugates_are_minimal_roots, Abbr`p`] >>
  `monic q /\ poly q` by rw[poly_prod_conjugate_factors_monic, Abbr`q`] >>
  `q pdivides p` by rw[poly_prod_factors_divides, Abbr`q`] >>
  `Poly s q` by rw[poly_prod_factors_conjugates_subfield_poly, Abbr`q`] >>
  `x IN Conj x` by rw[ring_conjugates_has_self] >>
  `Conj x = roots q` by rw[poly_prod_conjugate_factors_roots, Abbr`q`] >>
  `root q x` by metis_tac[poly_roots_member] >>
  `p pdivides q` by rw[poly_minimal_divides_subfield_poly, Abbr`p`] >>
  metis_tac[poly_monic_divides_antisymmetric, field_is_ring]);

(* This is a major milestone theorem. *)

(* Theorem: FiniteField r /\ s <<= r ==>
            !x. x IN R ==> (minimal x = PPROD {X - c * |1| | c | c  IN (Conj x)}) *)
(* Proof:
   Let t = {X - c * |1| | c | c IN Conj x}.
   Note t = IMAGE factor (Conj x)    by EXTENSION, IN_IMAGE, poly_factor_alt, ring_conjugates_member_element
        minimal x
      = PIFACTOR (Conj x)            by poly_minimal_eq_factors_conjugates
      = PPROD t                      by above
*)
val poly_minimal_eq_factors_conjugates_alt = store_thm(
  "poly_minimal_eq_factors_conjugates_alt",
  ``!(r:'a field) s. FiniteField r /\ s <<= r ==>
   !x. x IN R ==> (minimal x = PPROD {X - c * |1| | c | c  IN (Conj x)})``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  rw_tac std_ss[poly_minimal_eq_factors_conjugates] >>
  `IMAGE factor (Conj x) = {X - c * |1| | c | c IN Conj x}` suffices_by rw_tac std_ss[] >>
  rw_tac std_ss[EXTENSION, GSPECIFICATION, IN_IMAGE] >>
  metis_tac[poly_factor_alt, ring_conjugates_member_element]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==> (minimal x = (PIFACTOR o Conj) x) *)
(* Proof: by poly_minimal_eq_factors_conjugates, notation. *)
val poly_minimal_eq_factors_conjugates_compose = store_thm(
  "poly_minimal_eq_factors_conjugates_compose",
  ``!(r:'a field) s. FiniteField r /\ s <<= r ==> !x. x IN R ==> (minimal x = (PIFACTOR o Conj) x)``,
  rw_tac std_ss[poly_minimal_eq_factors_conjugates]);

(* Another proof of poly_minimal_one -- using theorem above. *)

(*
> ffMinimalTheory.poly_minimal_one;
val it = |- !r s. FiniteField r /\ s <<= r ==> (minimal #1 = X - |1|): thm
*)

(* Theorem: FiniteField r /\ s <<= r ==> (minimal #1 = X - |1|) *)
(* Proof:
     minimal #1
   = PIFACTOR (Conj #1)          by poly_minimal_eq_factors_conjugates
   = PIFACTOR {#1}               by ring_conjugates_one
   = factor #1                   by poly_prod_factors_sing
   = X - #1 * |1|                by poly_factor_alt
   = X - |1|                     by poly_cmult_lone
*)
val poly_minimal_one = prove( (* no need to store *)
  ``!(r s):'a ring. FiniteField r /\ s <<= r ==> (minimal #1 = X - |1|)``,
  rpt (stripDup[FiniteField_def]) >>
  `minimal #1 = PIFACTOR (Conj #1)` by rw[poly_minimal_eq_factors_conjugates] >>
  `_ = PIFACTOR {#1}` by rw[ring_conjugates_one] >>
  rw[poly_prod_factors_sing, poly_factor_alt]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==> (roots (minimal x) = Conj x) *)
(* Proof:
     roots (minimal x)
   = roots (PIFACTOR (Conj x))   by poly_minimal_eq_factors_conjugates
   = Conj x                      by poly_prod_conjugate_factors_roots
*)
val poly_minimal_roots = store_thm(
  "poly_minimal_roots",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> (roots (minimal x) = Conj x)``,
  rw_tac std_ss[poly_minimal_eq_factors_conjugates, poly_prod_conjugate_factors_roots]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==> (degree x = CARD (Conj x)) *)
(* Proof:
     degree x
   = deg (minimal x)           by notation
   = deg (PIFACTOR (Conj x))   by poly_minimal_eq_factors_conjugates
   = CARD (Conj x)             by poly_prod_conjugate_factors_deg
*)
val poly_minimal_deg = store_thm(
  "poly_minimal_deg",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> (degree x = CARD (Conj x))``,
  rw_tac std_ss[poly_minimal_eq_factors_conjugates, poly_prod_conjugate_factors_deg]);

(* ------------------------------------------------------------------------- *)
(* Counting Conjugates                                                       *)
(* ------------------------------------------------------------------------- *)

(* Note:
ZN_coprime_invertible        |- !n m. 1 < m /\ coprime m n ==> n MOD m IN (Invertibles (ZN m).prod).carrier
ZN_invertibles_finite_group  |- !n. 0 < n ==> FiniteGroup (Invertibles (ZN n).prod)
ZN_exp                       |- !n. 0 < n ==> !x k. (ZN n).prod.exp x k = x ** k MOD n
ZN_order_mod                 |- !n m. 0 < m ==> (order (ZN m).prod (n MOD m) = order (ZN m).prod n)
ZN_coprime_order_alt         |- !n m. 1 < m /\ coprime m n ==> 0 < order (ZN m).prod n /\ ...

Need to squeeze out more ZN_mult_* theorems from the proof below.
*)

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
            !n. conj x n = conj x (n MOD (order (ZN (forder x)).prod (CARD B))) *)
(* Proof:
   Let m = CARD B, ox = forder x, om = ordz ox m.
   Note 0 < ox /\ coprime ox m              by finite_field_order_property, x IN R+
        conj x n
      = x ** ((m ** n) MOD ox)              by finite_field_conjugate_member_eqn, x IN R+
      = x ** ((m ** (n MOD om)) MOD ox)     by ZN_coprime_exp_mod, 0 < ox, coprime ox m
      = conj x (n MOD om)                   by finite_field_conjugate_member_eqn, x IN R+
*)
val finite_field_conjugate_mod_order = store_thm(
  "finite_field_conjugate_mod_order",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
   !n. conj x n = conj x (n MOD (order (ZN (forder x)).prod (CARD B)))``,
  metis_tac[finite_field_order_property, finite_field_conjugate_member_eqn,
            ZN_coprime_exp_mod, finite_field_is_field]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
            !y. y IN Conj x ==> ?n. n < order (ZN (forder x)).prod (CARD B) /\ (y = conj x n) *)
(* Proof:
   Let m = CARD B, ox = forder x, om = ordz ox m.
   The goal is: ?n. n < om /\ (y = conj x n)
   Note x IN R                       by field_nonzero_element
     so ?n. y = conj x n             by ring_conjugates_member
              = conj x (n MOD om)    by finite_field_conjugate_mod_order, x IN R+, x <> #1
   If x = #1,
      Then ox = 1                    by field_order_eq_1, x = #1
       and om = 1                    by ZN_order_mod_1
        so n MOD 1 = 0               by MOD_1
        or y = conj x 0 = x          by ring_conjugate_0
      Take n = 0, the result is true
   If x <> #1,
      Then 0 < ox /\ coprime ox m    by finite_field_order_property, x IN R+
       and ox <> 1                   by field_order_eq_1, x <> #1
        so 0 < om                    by ZN_coprime_order_alt, 1 < ox /\ coprime ox m
      thus n MOD om < om             by MOD_LESS, 0 < om
      Take n = n MOD om, the result follows.
*)
val finite_field_conjugates_member = store_thm(
  "finite_field_conjugates_member",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
   !y. y IN Conj x ==> ?n. n < order (ZN (forder x)).prod (CARD B) /\ (y = conj x n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = CARD B` >>
  qabbrev_tac `ox = forder x` >>
  qabbrev_tac `om = ordz ox m` >>
  `x IN R` by rw[field_nonzero_element] >>
  `?n. y = conj x n` by rw[GSYM ring_conjugates_member] >>
  `_ = conj x (n MOD om)` by metis_tac[finite_field_conjugate_mod_order] >>
  Cases_on `x = #1` >| [
    `ox = 1` by rw[field_order_eq_1, Abbr`ox`] >>
    `om = 1` by rw[ZN_order_mod_1, Abbr`om`] >>
    `conj x 0 = x` by rw[ring_conjugate_0] >>
    metis_tac[MOD_1, DECIDE``0 < 1``],
    `0 < ox /\ coprime ox m` by metis_tac[finite_field_order_property] >>
    `ox <> 1` by rw[field_order_eq_1, Abbr`ox`] >>
    `1 < ox` by decide_tac >>
    metis_tac[ZN_coprime_order_alt, MOD_LESS]
  ]);

(* Theorem: FiniteField r /\ s <<= r ==> !x y. x IN R /\ y IN Conj x ==> (forder y = forder x) *)
(* Proof:
    Note y IN Conj x
     ==> ?n. y = conj x n     by ring_conjugates_member
   Hence forder y = forder x  by finite_field_conjugate_order
*)
val finite_field_conjugates_member_order = store_thm(
  "finite_field_conjugates_member_order",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !x y. x IN R /\ y IN Conj x ==> (forder y = forder x)``,
  rpt (stripDup[FiniteField_def]) >>
  `?n. y = conj x n` by rw[GSYM ring_conjugates_member] >>
  rw[finite_field_conjugate_order]);

(* Note:
> group_exp_equal |> ISPEC ``f*``;
val it = |- FiniteGroup f* ==> !x. x IN F* ==>
!n m. n < forder x /\ m < forder x /\ (f*.exp x n = f*.exp x m) ==> (n = m):
> group_exp_equal |> ISPEC ``Invertibles (ZN ox).prod``;
val it = |- FiniteGroup g ==>
   !x. x IN g.carrier ==> !n m. n < order g x /\ m < order g x /\ ((g.exp x n = (g.exp x m) ==> (n = m): thm
*)

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
            INJ (conj x) (count (order (ZN (forder x)).prod (CARD B))) (Conj x) *)
(* Proof:
   Let m = CARD B, ox = forder x, om = order (ZN ox).prod m.
   The goal is: INJ (conj x) (count om) (Conj x)

   Note x IN R                       by field_nonzero_element, x IN R+
   By INJ_DEF, this is to show:
   (1) x IN R /\ x' < om ==> conj x x' IN Conj x
       Since x IN Conj x             by ring_conjugates_has_self, x IN R
          so !n. conj x n IN Conj x  by ring_conjugates_has_element_conjugate
          or conj x x' IN Conj x
   (2) x IN R+ /\ x' < om /\ y < om /\ conj x x' = conj x y ==> x' = y
       If x = #1,
       Then ox = 1                   by field_order_eq_1, x = #1
        and om = 1                   by ZN_order_mod_1
       Since x' < 1, y < 1, both are 0, hence true.
       If x <> #1,
       Then ox <> 1                  by field_order_eq_1, x <> #1
        and 0 < ox /\ coprime ox m   by finite_field_order_property, x IN R+
         so 1 < ox                   by 0 < ox, ox <> 1
        and 0 < om                   by ZN_coprime_order_alt, 1 < ox /\ coprime ox m
         so !y. y MOD om < om        by MOD_LESS, 0 < om

       Step 1: apply group_exp_equal for FiniteGroup f*
       Note Group f*                 by field_mult_group
        and F* = R+                  by field_mult_carrier
       Note f*.exp = $**             by field_nonzero_mult_property

                            conj x x' = conj x y
        ==>            x ** (m ** x') = x ** (m ** y)             by ring_conjugate_def, x IN R
        ==>   x ** ((m ** x') MOD ox) = x ** ((m ** y) MOD ox)    by field_exp_mod_order, x IN R, 0 < ox
        ==>          (m ** x') MOD ox = (m ** y) MOD ox           by group_exp_equal, x IN R+
        ==>   m ** (x' MOD om) MOD ox = m ** (y MOD om) MOD ox    by ZN_coprime_exp_mod, 0 < ox, coprime ox m
        ==>          (m ** x') MOD ox = m ** y MOD ox             by LESS_MOD, 0 < om, x' < om, y < om
        ==> ((m MOD ox) ** x') MOD ox = ((m MOD ox) ** y) MOD ox  by EXP_MOD

       Step 2: apply group_exp_equal for Invertibles (ZN ox).prod
       Let g = Invertibles (ZN ox).prod, the Euler group.
       and z = m MOD ox.
       Then Group g                    by ZN_invertibles_group, 0 < ox
        ==> z IN g.carrier             by ZN_coprime_invertible, 1 < ox, coprime ox m
       Note om = order (ZN ox).prod m  by ZN_order_mod, 0 < ox
               = order g z             by ZN_invertibles_order, 0 < ox
       Note !x k. g.exp x k = (ZN ox).prod.exp x k         by Invertibles_property
        and !x k. (ZN ox).prod.exp x k = (x ** k) MOD ox   by ZN_exp

               (z ** x') MOD ox = (z ** y) MOD ox
            ==>      g.exp z x' = g.exp z y                by above
            ==>              x' = y                        by group_exp_equal, om = order g (z)
*)
val finite_field_conjugates_inj = store_thm(
  "finite_field_conjugates_inj",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
    INJ (conj x) (count (order (ZN (forder x)).prod (CARD B))) (Conj x)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = CARD B` >>
  qabbrev_tac `ox = forder x` >>
  qabbrev_tac `om = order (ZN ox).prod m` >>
  `x IN R` by rw[field_nonzero_element] >>
  rw[INJ_DEF] >-
  rw[ring_conjugates_has_self, ring_conjugates_has_element_conjugate] >>
  `(x' MOD om = x') /\ (y MOD om = y)` by rw[LESS_MOD] >>
  Cases_on `x = #1` >-
  metis_tac[field_order_eq_1, ZN_order_mod_1, MOD_1] >>
  `0 < ox /\ coprime ox m` by metis_tac[finite_field_order_property] >>
  `ox <> 1` by rw[field_order_eq_1, Abbr`ox`] >>
  `1 < ox` by decide_tac >>
  `Group f*` by rw[field_mult_group] >>
  `F* = R+` by rw[field_mult_carrier] >>
  qabbrev_tac `g = Invertibles (ZN ox).prod` >>
  qabbrev_tac `z = m MOD ox` >>
  `Group g` by rw[ZN_invertibles_group, Abbr`g`] >>
  `z IN g.carrier` by rw[ZN_coprime_invertible, Abbr`g`, Abbr`z`] >>
  `!x k. !x k. g.exp x k = (x ** k) MOD ox` by rw[Invertibles_property, ZN_exp, Abbr`g`] >>
  `f*.exp = $**` by rw[field_nonzero_mult_property] >>
  `om = order (ZN ox).prod m` by rw[ZN_order_mod, Abbr`om`] >>
  `_  = order g z` by rw[ZN_invertibles_order, Abbr`g`, Abbr`z`] >>
  `x ** (m ** x') = x ** (m ** y)` by rw[GSYM ring_conjugate_def, Abbr`m`] >>
  `x ** ((m ** x') MOD ox) = x ** ((m ** y) MOD ox)` by metis_tac[field_exp_mod_order] >>
  `(m ** x') MOD ox = (m ** y) MOD ox` by metis_tac[group_exp_equal, MOD_LESS] >>
  `(m ** x') MOD ox = (m ** y) MOD ox` by metis_tac[ZN_coprime_exp_mod, LESS_MOD] >>
  `(z ** x') MOD ox = (z ** y) MOD ox` by metis_tac[EXP_MOD] >>
  metis_tac[group_exp_equal]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
            SURJ (conj x) (count (order (ZN (forder x)).prod (CARD B))) (Conj x) *)
(* Proof:
   Let m = CARD B, ox = forder x, om = order (ZN ox).prod m.
   The goal is: SURJ (conj x) (count om) (Conj x)

   Note x IN R                           by field_nonzero_element, x IN R+
   By SURJ_DEF, this is to show:
   (1) x IN R /\ x' < om ==> conj x x' IN Conj x
       Since x IN Conj x                 by ring_conjugates_has_self, x IN R
          so !n. conj x n IN Conj x      by ring_conjugates_has_element_conjugate
          or conj x x' IN Conj x
   (2) x IN R+ /\ x' IN Conj x ==> ?y. y < om /\ (conj x y = x')
       Given x' IN Conj x
         ==> ?n. x' = conj x n           by ring_conjugates_member
                    = conj x (n MOD om)  by finite_field_conjugate_mod_order, x IN R+
       If x = #1,
       Then ox = 1                       by field_order_eq_1, x = #1
        and om = 1                       by ZN_order_mod_1
       Take y = 0, then y < om,
        and x' = conj x (0 MOD 1)
               = conj x 0                by MOD_1
       If x <> #1,
       Then ox <> 1                      by field_order_eq_1, x <> #1
        and 0 < ox /\ coprime ox m       by finite_field_order_property, x IN R+
         so 1 < ox                       by 0 < ox, ox <> 1
        and 0 < om                       by ZN_coprime_order_alt, 1 < ox, coprime ox m
       Thus (n MOD om) < om              by MOD_LESS, 0 < om
       Take y = n MOD om, the result follows.
*)
val finite_field_conjugates_surj = store_thm(
  "finite_field_conjugates_surj",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
    SURJ (conj x) (count (order (ZN (forder x)).prod (CARD B))) (Conj x)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = CARD B` >>
  qabbrev_tac `ox = forder x` >>
  qabbrev_tac `om = order (ZN ox).prod m` >>
  `x IN R` by rw[field_nonzero_element] >>
  rw[SURJ_DEF] >-
  rw[ring_conjugates_has_self, ring_conjugates_has_element_conjugate] >>
  `?n. x' = conj x n` by rw[GSYM ring_conjugates_member] >>
  `_ = conj x (n MOD om)` by metis_tac[finite_field_conjugate_mod_order] >>
  Cases_on `x = #1` >-
  metis_tac[field_order_eq_1, ZN_order_mod_1, MOD_1, DECIDE``0 < 1``] >>
  `0 < ox /\ coprime ox m` by metis_tac[finite_field_order_property] >>
  `ox <> 1` by rw[field_order_eq_1, Abbr`ox`] >>
  `1 < ox` by decide_tac >>
  `0 < om` by rw[ZN_coprime_order_alt, Abbr`om`] >>
  metis_tac[MOD_LESS]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
            BIJ (conj x) (count (order (ZN (forder x)).prod (CARD B))) (Conj x) *)
(* Proof: by BIJ_DEF, finite_field_conjugates_inj, finite_field_conjugates_surj *)
val finite_field_conjugates_bij = store_thm(
  "finite_field_conjugates_bij",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
    BIJ (conj x) (count (order (ZN (forder x)).prod (CARD B))) (Conj x)``,
  rw[BIJ_DEF, finite_field_conjugates_inj, finite_field_conjugates_surj]);

(* Note:
finite_field_conjugates_subset
|- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> Conj x SUBSET IMAGE (conj x) (count (r <:> s))
*)

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
            (Conj x = IMAGE (conj x) (count (order (ZN (forder x)).prod (CARD B)))) *)
(* Proof: by finite_field_conjugates_surj, IMAGE_SURJ *)
(* Note:
   Conj #0 = {#0}      by ring_conjugates_zero
   Conj #1 = {#1}      by ring_conjugates_one
*)
val finite_field_conjugates_eq_image = store_thm(
  "finite_field_conjugates_eq_image",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
    (Conj x = IMAGE (conj x) (count (order (ZN (forder x)).prod (CARD B))))``,
  rw[finite_field_conjugates_surj, GSYM IMAGE_SURJ]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
            (CARD (Conj x) = (order (ZN (forder x)).prod (CARD B))) *)
(* Proof:
   Let om = order (ZN (forder x)).prod (CARD B).
    Note x IN R                             by field_nonzero_element
     and FiniteRing r                       by FiniteRing_def
   Since FINITE (Conj x)                    by ring_conjugates_finite, x IN R
     and FINITE (count m)                   by FINITE_COUNT
     and BIJ (conj x) (count om) (Conj x)   by finite_field_conjugates_bij, x IN R+
      so CARD (Conj x)
       = CARD (count om)                    by FINITE_BIJ_CARD_EQ
       = om                                 by CARD_COUNT
*)
(* Note:
   CARD (Conj #0) = CARD {#0} = 1      by ring_conjugates_zero
   CARD (Conj #1) = CARD {#1} = 1      by ring_conjugates_one
*)
val finite_field_conjugates_card = store_thm(
  "finite_field_conjugates_card",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
    (CARD (Conj x) = order (ZN (forder x)).prod (CARD B))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `om = order (ZN (forder x)).prod (CARD B)` >>
  `x IN R` by rw[field_nonzero_element] >>
  `FINITE (Conj x)` by rw[ring_conjugates_finite, finite_field_is_finite_ring] >>
  `BIJ (conj x) (count om) (Conj x)` by rw[finite_field_conjugates_bij, Abbr`om`] >>
  metis_tac[FINITE_BIJ_CARD_EQ, FINITE_COUNT, CARD_COUNT]);

(* This is a milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Degree of Minimal Polynomial                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
            (degree x = order (ZN (forder x)).prod (CARD B)) *)
(* Proof:
   Note x IN R                              by field_nonzero_element
     degree x
   = deg (minimal x)                        by notation
   = CARD (Conj x)                          by poly_minimal_deg, x IN R
   = order (ZN (forder x)).prod (CARD B)    by finite_field_conjugates_card, x IN R+
*)
(* Note:
   deg (minimal #0) = deg X = 1            by poly_minimal_zero
   deg (minimal #1) = deg (X - |1|) = 1    by poly_minimal_one
*)
val poly_minimal_deg_eqn = store_thm(
  "poly_minimal_deg_eqn",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R+ ==>
    (degree x = order (ZN (forder x)).prod (CARD B))``,
  rpt (stripDup[FiniteField_def]) >>
  `x IN R` by rw[field_nonzero_element] >>
  rw[poly_minimal_deg, finite_field_conjugates_card]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==> degree x divides (r <:> s) *)
(* Proof:
   Let d = (r <:> s), om = order (ZN (forder x)).prod (CARD B).
   If x = #0,
        deg (minimal #0)
      = deg X              by poly_minimal_zero
      = 1                  by poly_deg_X
      and 1 divides d      by ONE_DIVIDES_ALL
   If x <> #0,
      Note x IN R+         by field_nonzero_eq
        degree x
      = deg (minimal x)    by notation
      = om                 by poly_minimal_deg_eqn
      and om divides d     by subfield_card_order_divides_dim
*)
val poly_minimal_deg_divides_dim = store_thm(
  "poly_minimal_deg_divides_dim",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> degree x divides (r <:> s)``,
  rpt (stripDup[FiniteField_def]) >>
  Cases_on `x = #0` >| [
    `deg (minimal #0) = 1` by rw[poly_minimal_zero] >>
    rw[ONE_DIVIDES_ALL],
    `x IN R+` by rw[field_nonzero_eq] >>
    rw[poly_minimal_deg_eqn, subfield_card_order_divides_dim]
  ]);

(* Another proof of the same theorem. *)

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==> degree x divides (r <:> s) *)
(* Proof:
   Let d = (r <:> s), om = order (ZN (forder x)).prod (CARD B).
   If x = #0,
        deg (minimal #0)
      = CARD (Conj #0)     by poly_minimal_deg
      = CARD {#0}          by ring_conjugates_zero
      = 1                  by CARD_SING
      and 1 divides d      by ONE_DIVIDES_ALL
   If x <> #0,
      Note x IN R+         by field_nonzero_eq
        degree x
      = deg (minimal x)    by notation
      = CARD (Conj x)      by poly_minimal_deg
      = om                 by finite_field_conjugates_card, x IN R+
      and om divides d     by subfield_card_order_divides_dim
*)
val poly_minimal_deg_divides_dim = store_thm(
  "poly_minimal_deg_divides_dim",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> degree x divides (r <:> s)``,
  rpt (stripDup[FiniteField_def]) >>
  `degree x = CARD (Conj x)` by rw[poly_minimal_deg] >>
  Cases_on `x = #0` >-
  rw[finite_field_conjugates_zero] >>
  `x IN R+` by rw[field_nonzero_eq] >>
  rw[finite_field_conjugates_card, subfield_card_order_divides_dim]);

(* Third proof of the same theorem, without counting conjugates. *)

(*
> poly_minimal_subfield_irreducible
val it = |- !r. FiniteField r ==> !s. s <<= r ==> !x. x IN R ==> IPoly s (minimal x)
> poly_irreducible_master_divisibility |> ISPEC ``s:'a field``;
val it = |- FiniteField s ==> !p. poly_monic s p /\ IPoly s p ==>
     !n. poly_divides s p (Master s (CARD B ** n)) <=> poly_deg s p divides n: thm
*)

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==> degree x divides (r <:> s) *)
(* Proof:
   Let p = minimal x, d = (r <:> s), q = Master s ((CARD B) ** d).

   Step 1: compute roots of master.
    Note q = master (CARD B ** d)        by subring_poly_master
           = master (CARD R)             by finite_subfield_card_eqn
           = PIFACTOR R                  by poly_master_eq_root_factor_product
    Thus roots q = roots (PIFACTOR R)    by above
                 = R                     by poly_prod_factors_roots, FINITE R

   Step 1: Show p pdivides (master (CARD R))
   Since p = PIFACTOR (Conj x)           by poly_minimal_eq_factors_conjugates
     and FINITE (Conj x)                 by ring_conjugates_finite
     and (Conj x) SUBSET R               by ring_conjugates_subset, x IN R
      so roots p = Conj x                by poly_prod_factors_roots, FINITE (Conj x)
      or (roots p) SUBSET R              by above
    Thus p pdivides (master (CARD R))    by poly_prod_factors_divisibility, FINITE R
      or p pdivides q

   Step 2: Apply poly_irreducible_master_divisibility
   Since IPoly p                         by poly_minimal_subfield_irreducible
     and Monic s p /\ 0 < deg p          by poly_minimal_subfield_property
     now deg p = Deg s p                 by subring_poly_deg
      so Ulead s p                       by poly_monic_ulead

   Given p pdivides q                    by above
      or poly_divides s p q              by subring_poly_divides_iff, Ulead s p
      or poly_divides s p (Master s (CARD B ** d))    by above, subring_poly_master
      so Deg s p divides d               by poly_irreducible_master_divisibility
      or deg p divides d                 by above, Deg s p = deg p
*)
val poly_minimal_deg_divides_dim = store_thm(
  "poly_minimal_deg_divides_dim",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R ==> degree x divides (r <:> s)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `p = minimal x` >>
  qabbrev_tac `d = (r <:> s)` >>
  qabbrev_tac `q = master (CARD B ** d)` >>
  `s <= r` by rw[subfield_is_subring] >>
  `q = Master s (CARD B ** d)` by rw[subring_poly_master, Abbr`q`] >>
  `CARD R = CARD B ** d` by rw[finite_subfield_card_eqn, Abbr`d`] >>
  `q = PIFACTOR R` by metis_tac[poly_master_eq_root_factor_product] >>
  `roots q = R` by rw[poly_prod_factors_roots] >>
  `p = PIFACTOR (Conj x)` by rw[poly_minimal_eq_factors_conjugates, Abbr`p`] >>
  `FINITE (Conj x)` by rw[ring_conjugates_finite, finite_field_is_finite_ring] >>
  `(Conj x) SUBSET R` by rw[ring_conjugates_subset] >>
  `(roots p) SUBSET R` by rw[poly_prod_factors_roots] >>
  `p pdivides q` by rw[poly_prod_factors_divisibility, Abbr`q`] >>
  `FiniteField s` by metis_tac[subfield_finite_field] >>
  `IPoly s p` by rw[poly_minimal_subfield_irreducible, Abbr`p`] >>
  `Monic s p /\ 0 < deg p` by metis_tac[poly_minimal_subfield_property] >>
  `deg p = Deg s p` by rw[subring_poly_deg] >>
  `Ulead s p` by rw[poly_monic_ulead] >>
  `Poly s q` by metis_tac[poly_master_poly, subring_poly_master] >>
  metis_tac[subring_poly_divides_iff, poly_irreducible_master_divisibility]);

(* ------------------------------------------------------------------------- *)
(* Monic Irreducible to be Minimal Polynomial                                *)
(* ------------------------------------------------------------------------- *)

(* Idea:
Target: In a subfield, monic s p /\ ipoly s p /\ (deg p) divides (r <:> s)
        ==> ?x. x IN R /\ (p = minimal x).

poly_master_eq_root_factor_product
   |- !r. FiniteField r ==> (master (CARD R) = PIFACTOR R)
poly_irreducible_master_divisibility
   |- !r. FiniteField r ==> !p. monic p /\ ipoly p ==> !n. p pdivides master (CARD R ** n) <=> deg p divides n
> poly_irreducible_master_divisibility |> ISPEC ``s:'a field``;
val it = |- FiniteField s ==>
   !p. poly_monic s p /\ irreducible (PolyRing s) p ==>
   !n. poly_divides s p (Master s (CARD B ** n)) <=> poly_deg s p divides n: thm
Put n = (r <:> s), this says:
In a finite subfield, poly_divides s p (Master s (CARD B ** (r <:> s))) <=> poly_deg s p divides (r <:> s)
Given poly_deg s p divides (r <:> s),
we know poly_divides s p (Master s (CARD R))  since CARD R = CARD B ** (r <:> s)  by finite_subfield_card_eqn
or      poly_divides s p (PPROD (IMAGE factor R))   since PIFACTOR R = PPROD (IMAGE factor R) by notation

poly_prod_monic_irreducible_set_divisor
   |- !r. Field r ==> !s. FINITE s /\ miset s ==>
       !p. monic p /\ ipoly p ==> (p pdivides PPROD s <=> p IN s)

This means p IN (IMAGE factor R). <- something's not right here!

Perhaps need       (PPROD (IMAGE factor t)) pdivides (PPROD (IMAGE factor s))  <=> t SUBSET s.
But even this t can be empty.
I need something like:       p pdivides (PPROD s) ==> p = PPROD t   where t SUBSET s.
And if deg p <> 0, then t <> {}.

In general, if I say: a subfield poly with (deg p) divides (r <:> s) has at least one root in R,
is this true?

Better use this:
Since p divides master,  master = q * p.
If each (factor x), which is irreducible, cannot divides p, it must divide q.
But if all (factor x), with x IN R divides q, then PIFACTOR R divides q.
or master divides q, so q = t * master.
Thus master = (t * master) * p,   or in Field r, t * p = |1|, meaning p is upoly, which is ~(ipoly).
by poly_irreducible_not_unit.
*)

(* Theorem: If a monic irreducible subfield poly has a root, it must be the minimal polynomial of the root.
            FiniteField r /\ s <<= r ==> !p. monic p /\ IPoly s p ==>
            !x. x IN R ==> (root p x <=> (p = minimal x)) *)
(* Proof:
   If part: root p x ==> (p = minimal x)
      Note IPoly s p ==> Poly s p      by poly_irreducible_poly
       and           ==> poly p        by subring_poly_poly
       and monic p ==> poly_monic s p  by subring_poly_monic_iff
      Let q = minimal x.
      With root p x, q pdivides p      by poly_minimal_divides_subfield_poly
       Now Monic s q /\ 0 < deg q      by poly_minimal_subfield_property
       and deg q = Deg s q             by subring_poly_deg
        so Pmonic s q                  by poly_monic_pmonic
       ==> poly_divides s q p          by subring_poly_divides_iff
       But q <> |1|                    by poly_minimal_ne_poly_one
       and poly_one s = |1|            by subring_poly_one
        so q = p                       by poly_monic_divides_monic_irreducible, q <> poly_one s

   Only-if part: (p = minimal x) ==> root p x
      True by poly_minimal_has_element_root.
*)
val poly_minimal_unique = store_thm(
  "poly_minimal_unique",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !p. monic p /\ IPoly s p ==>
   !x. x IN R ==> (root p x <=> (p = minimal x))``,
  rpt (stripDup[FiniteField_def]) >>
  rw[EQ_IMP_THM] >| [
    `s <= r` by rw[subfield_is_subring] >>
    `Poly s p /\ poly p` by rw[poly_irreducible_poly, subring_poly_poly] >>
    `poly_monic s p` by metis_tac[subring_poly_monic_iff] >>
    qabbrev_tac `q = minimal x` >>
    `q pdivides p` by rw[poly_minimal_divides_subfield_poly, Abbr`q`] >>
    `Monic s q /\ 0 < deg q` by metis_tac[poly_minimal_subfield_property] >>
    `deg q = Deg s q` by rw[subring_poly_deg] >>
    `Pmonic s q` by rw[poly_monic_pmonic] >>
    `poly_divides s q p` by metis_tac[subring_poly_divides_iff] >>
    `q <> |1|` by rw[poly_minimal_ne_poly_one, Abbr`q`] >>
    metis_tac[poly_monic_divides_monic_irreducible, subring_poly_one, field_is_ring],
    rw[poly_minimal_has_element_root]
  ]);

(* Theorem: FiniteField r /\ s <<= r ==> !p. monic p /\ IPoly s p ==>
            !x. x IN R ==> (root p x <=> (p = PIFACTOR (Conj x))) *)
(* Proof:
   Since root p x <=> (p = minimal x)         by poly_minimal_unique
     and minimal x = PIFACTOR (Conj x)        by poly_minimal_eq_factors_conjugates
      so root p x <=> (p = PIFACTOR (Conj x))
*)
val subfield_monic_irreducible_by_conjugate_factors = store_thm(
  "subfield_monic_irreducible_by_conjugate_factors",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !p. monic p /\ IPoly s p ==>
   !x. x IN R ==> (root p x <=> (p = PIFACTOR (Conj x)))``,
  metis_tac[poly_minimal_unique, poly_minimal_eq_factors_conjugates]);

(* Theorem: A monic irreducible subfield poly with degree divides the dimension must be a minimal polynomial.
            FiniteField r /\ s <<= r ==> !p. monic p /\ IPoly s p /\ (deg p) divides (r <:> s) ==>
            ?x. x IN R /\ (p = minimal x) *)
(* Proof:
   Let d = (r <:> s), q = Master s (CARD B ** d)
    Note q = Master s (CARD B ** d)
       = master (CARD B ** d)            by subring_poly_master
       = master (CARD R)                 by finite_subfield_card_eqn
       = PIFACTOR R                      by poly_master_eq_root_factor_product

    Note FiniteField s                   by subfield_finite_field
     and poly_deg s p = deg p            by subring_poly_deg
    Also Poly s p                        by poly_irreducible_poly
    thus poly_monic s p                  by subring_poly_monic_iff
     ==> poly_divides s p (Master s (CARD B ** d))  by poly_irreducible_master_divisibility
    Note Poly s q                        by poly_master_poly
     ==> p pdivdes PIFACTOR R            by subring_poly_divides

     But p <> poly_one s                 by poly_irreducible_ne_poly_one
      or p <> |1|                        by subring_poly_one
     and R SUBSET R                      by SUBSET_REFL
     ==> (roots p) INTER R <> {}         by poly_monic_divides_poly_prod_factors_property

   Hence ?x. x IN R /\ x IN (roots p)    by MEMBER_NOT_EMPTY, IN_INTER
      or     x IN R /\ root p x          by poly_roots_member
    Take this x, then p = minimal x      by poly_minimal_unique
*)
val poly_monic_irreducible_is_minimal_poly = store_thm(
  "poly_monic_irreducible_is_minimal_poly",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !p. monic p /\ IPoly s p /\ (deg p) divides (r <:> s) ==> ?x. x IN R /\ (p = minimal x)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `d = (r <:> s)` >>
  qabbrev_tac `q = Master s (CARD B ** d)` >>
  `s <= r` by rw[subfield_is_subring] >>
  `q = master (CARD B ** d)` by rw[subring_poly_master, Abbr`q`] >>
  `_ = master (CARD R)` by rw[GSYM finite_subfield_card_eqn, Abbr`d`] >>
  `_ = PIFACTOR R` by rw[poly_master_eq_root_factor_product] >>
  `FiniteField s` by metis_tac[subfield_finite_field] >>
  `poly_deg s p = deg p` by rw[subring_poly_deg] >>
  `Poly s p` by rw[poly_irreducible_poly] >>
  `poly_monic s p` by metis_tac[subring_poly_monic_iff] >>
  `poly_divides s p (Master s (CARD B ** d))` by rw[poly_irreducible_master_divisibility, Abbr`d`] >>
  `Poly s q` by rw[poly_master_poly, Abbr`q`] >>
  `p pdivides (PIFACTOR R)` by metis_tac[subring_poly_divides] >>
  `p <> |1|` by metis_tac[poly_irreducible_ne_poly_one, subring_poly_one] >>
  `(roots p) INTER R <> {}` by metis_tac[poly_monic_divides_poly_prod_factors_property, SUBSET_REFL] >>
  `?x. x IN R /\ x IN (roots p)` by metis_tac[MEMBER_NOT_EMPTY, IN_INTER] >>
  metis_tac[poly_minimal_unique, poly_roots_member]);

(* This is a major milestone theorem. *)

(* Theorem: A monic irreducible subfield poly with degree divides the dimension iff it is a minimal polynomial.
            FiniteField r /\ s <<= r ==> !p. monic p /\ IPoly s p /\ (deg p) divides (r <:> s) <=>
            ?x. x IN R /\ (p = minimal x) *)
(* Proof:
   If part: !p. monic p /\ IPoly s p /\ (deg p) divides (r <:> s) ==> ?x. x IN R /\ (p = minimal x)
      This is true                           by poly_monic_irreducible_is_minimal_poly
   Only-if part: x IN R /\ (p = minimal x) ==> monic p /\ IPoly s p /\ (deg p) divides (r <:> s)
      This is to show:
      (a) monic (minimal x), true            by poly_minimal_monic
      (b) IPoly s (minimal x), true          by poly_minimal_subfield_irreducible
      (c) degree x divides (r <:> s), true   by poly_minimal_deg_divides_dim
*)
val poly_monic_irreducible_minimal_condition = store_thm(
  "poly_monic_irreducible_minimal_condition",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !p. monic p /\ IPoly s p /\ (deg p) divides (r <:> s) <=> ?x. x IN R /\ (p = minimal x)``,
  rw[EQ_IMP_THM] >-
  rw[poly_monic_irreducible_is_minimal_poly] >-
  rw[poly_minimal_monic] >-
  rw[poly_minimal_subfield_irreducible] >>
  rw[poly_minimal_deg_divides_dim]);

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R ==> (minimal x) pdivides (master (CARD R)) *)
(* Proof:
   Let p = minimal x.
   Then monic p                        by poly_minimal_monic
    and IPoly s p                      by poly_minimal_subfield_irreducible
    and (deg p) divides (r <:> s)      by poly_minimal_deg_divides_dim
   Thus p pdivides (master (CARD R))   by poly_irreducible_master_subfield_divisibility
*)
val poly_minimal_divides_master = store_thm(
  "poly_minimal_divides_master",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !x. x IN R ==> (minimal x) pdivides (master (CARD R))``,
  rpt strip_tac >>
  `monic (minimal x)` by rw[poly_minimal_monic] >>
  `IPoly s (minimal x)` by rw[poly_minimal_subfield_irreducible] >>
  `degree x divides (r <:> s)` by rw[poly_minimal_deg_divides_dim] >>
  metis_tac[poly_irreducible_master_subfield_divisibility]);

(* Theorem: FiniteField r /\ s <<= r ==>
   !p. monic p /\ IPoly s p /\ p pdivides master (CARD R) <=> ?x. x IN R /\ (p = minimal x) *)
(* Proof:
   If part: monic p /\ IPoly s p /\ p pdivides master (CARD R) <=> ?x. x IN R /\ (p = minimal x)
      Note p pdivides master (CARD R)    by poly_irreducible_master_subfield_divisibility
        so ?x. x IN R /\ p = minimal x   by poly_monic_irreducible_is_minimal_poly
   Only-if part: x IN R ==> monic (minimal x) /\ IPoly s (minimal x) /\ (minimal x) pdivides master (CARD R)
      (1) monic (minimal x), true        by poly_minimal_monic
      (2) IPoly s (minimal x), true      by poly_minimal_subfield_irreducible
      (3) (minimal x) pdivides master (CARD R),
          This is true                   by poly_minimal_divides_master
*)
val poly_monic_irreducible_eq_minimal_poly = store_thm(
  "poly_monic_irreducible_eq_minimal_poly",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !p. monic p /\ IPoly s p /\ p pdivides master (CARD R) <=> ?x. x IN R /\ (p = minimal x)``,
  rpt strip_tac >>
  rw_tac std_ss[EQ_IMP_THM] >-
  metis_tac[poly_irreducible_master_subfield_divisibility, poly_monic_irreducible_is_minimal_poly] >-
  rw[poly_minimal_monic] >-
  rw[poly_minimal_subfield_irreducible] >>
  rw[poly_minimal_divides_master]);

(* ------------------------------------------------------------------------- *)
(* Orders Partition by Conjugates                                            *)
(* ------------------------------------------------------------------------- *)

(* Define the conjugate equivalence relation *)
val eq_conj_def = Define`
    eq_conj (r:'a ring) (s:'a ring) x y = ?k. y = conj x k
`;

(* Overload conjugate equivalennce relation *)
val _ = overload_on("~~", ``eq_conj (r:'a ring) (s:'a ring)``);
val _ = set_fixity "~~" (Infix(NONASSOC, 450)); (* same as relation *)
(* > eq_conj_def;
val it = |- !r s x y. x ~~ y <=> ?k. y = conj x k: thm *)

(* Theorem: Ring r ==> !x. x IN R ==> x ~~ x *)
(* Proof:
   Since conj x 0 = x      by ring_conjugate_0
      so x ~~ x            by eq_conj_def
*)
val eq_conj_refl = store_thm(
  "eq_conj_refl",
  ``!(r s):'a ring. Ring r ==> !x. x IN R ==> x ~~ x``,
  metis_tac[eq_conj_def, ring_conjugate_0]);

(* Theorem: Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((x ~~ y) /\ (y ~~ z) ==> (x ~~ z)) *)
(* Proof:
   Let m = CARD B.
   By eq_conj_def, ring_conjugate_def, this is to show:
   !x. x IN R ==> ?k''. (x ** m ** k) ** m ** k' = x ** m ** k''

   Let k'' = k + k'.
     (x ** m ** k) ** m ** k'
   = x ** (m ** k * m ** k')     by ring_exp_mult
   = x ** (m ** (k + k'))        by EXP_ADD
   = x ** m ** k''               by k'' = k + k'
*)
val eq_conj_trans = store_thm(
  "eq_conj_trans",
  ``!(r s):'a ring. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((x ~~ y) /\ (y ~~ z) ==> (x ~~ z))``,
  rw_tac std_ss[eq_conj_def, ring_conjugate_def] >>
  qabbrev_tac `m = CARD B` >>
  `(x ** m ** k) ** m ** k' = x ** (m ** k * m ** k')` by rw[] >>
  `_ = x ** (m ** (k + k'))` by rw_tac std_ss[EXP_ADD] >>
  metis_tac[]);

(* Theorem: FiniteField r /\ s <<= r ==> !x y. x IN R /\ y IN R ==> ((x ~~ y) ==> (y ~~ x) *)
(* Proof:
   Let m = CARD B.
   By eq_conj_def, ring_conjugate_def, this is to show:
   !x. x IN R ==> ?k'. x = (x ** m ** k) ** m ** k'
   Let d = (r <:> s), the dimension.
   Then CARD R = m ** d /\ 0 < d     by finite_subfield_card_eqn

   Let k' = d - (k MOD d).
   Note k MOD d < d               by MOD_LESS, 0 < d
     so (k' MOD d + k MOD d) MOD d = 0  by MOD_ADD_INV, 0 < d, k MOD d < d.
     or (k' + k) MOD d = 0        by MOD_PLUS, MOD_MOD, 0 < d
     or (k + k') MOD d = 0        by ADD_COMM
     or d divides (k + k')        by DIVIDES_MOD_0, 0 < d
     or ?c. k + k' = c * d        by divides_def

      (x ** m ** k) ** m ** k'
    = x ** (m ** k * m ** k')     by field_exp_mult
    = x ** (m ** (k + k'))        by EXP_ADD
    = x ** (m ** (c * d))         by above
    = x ** (m ** (d * c))         by MULT_COMM
    = x ** (m ** d) ** c          by EXP_EXP_MULT
    = x ** (CARD R) ** c          by above, finite_subfield_card_eqn
    = x                           by finite_field_fermat_all
*)
val eq_conj_sym = store_thm(
  "eq_conj_sym",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x y. x IN R /\ y IN R ==> ((x ~~ y) ==> (y ~~ x))``,
  rpt (stripDup[FiniteField_def]) >>
  fs[eq_conj_def, ring_conjugate_def] >>
  qabbrev_tac `m = CARD B` >>
  qabbrev_tac `d = (r <:> s)` >>
  `(CARD R = m ** d) /\ 0 < d` by rw[finite_subfield_card_eqn, Abbr`m`, Abbr`d`] >>
  `k MOD d < d` by rw[MOD_LESS] >>
  qexists_tac `d - (k MOD d)` >>
  `(k + (d - k MOD d)) MOD d = 0` by metis_tac[MOD_ADD_INV, MOD_PLUS, MOD_MOD, ADD_COMM] >>
  `d divides (k + (d - k MOD d))` by rw[DIVIDES_MOD_0] >>
  `?c. k + (d - k MOD d) = c * d` by rw[GSYM divides_def] >>
  `_ = d * c` by rw[] >>
  `(x ** m ** k) ** m ** (d - k MOD d) = x ** (m ** k * m ** (d - k MOD d))` by rw[field_exp_mult] >>
  `_ = x ** (m ** (k + (d - k MOD d)))` by rw_tac std_ss[EXP_ADD] >>
  `_ = x ** (m ** (d * c))` by rw[] >>
  `_ = x ** (m ** d) ** c` by rw[EXP_EXP_MULT] >>
  `_ = x ** (CARD R) ** c` by rw[] >>
  `_ = x` by rw[finite_field_fermat_all] >>
  rw[]);

(* Theorem: FiniteField r /\ s <<= r ==> $~~ equiv_on R *)
(* Proof:
   By equiv_on_def, this is to show:
   (1) x IN R ==> x ~~ x, true                                         by eq_conj_refl
   (2) x IN R /\ y IN R ==> (x ~~ y) <=> (y ~~ x), true                by eq_conj_sym
   (3) x IN R /\ y IN R /\ z IN R /\ x ~~ y /\ y ~~ z ==> x ~~ z, true by eq_conj_trans
*)
val eq_conj_equiv_on_field_carrier = store_thm(
  "eq_conj_equiv_on_field_carrier",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> $~~ equiv_on R``,
  rpt (stripDup[FiniteField_def]) >>
  rw[equiv_on_def] >-
  rw[eq_conj_refl] >-
  metis_tac[eq_conj_sym] >>
  metis_tac[eq_conj_trans, field_is_ring]);

(* Theorem: FiniteField r /\ s <<= r ==> !n. $~~ equiv_on (orders f* n) *)
(* Proof:
   Since $~~ equiv_on R              by eq_conj_equiv_on_field_carrier
     and (orders f* n) SUBSET R      by field_orders_subset_carrier
     ==> $~~ equiv_on (orders f* n)  by equiv_on_subset
*)
val eq_conj_equiv_on_orders = store_thm(
  "eq_conj_equiv_on_orders",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !n. $~~ equiv_on (orders f* n)``,
  metis_tac[field_orders_subset_carrier, eq_conj_equiv_on_field_carrier, equiv_on_subset]);

(* Theorem: Ring r ==> !x. x IN R ==> !y. y IN Conj x <=> y IN R /\ x ~~ y *)
(* Proof:
   If part: x IN R /\ y IN Conj x ==> y IN R /\ x ~~ y
      Note ?n. y = conj x n       by ring_conjugates_member
        so y IN R                 by ring_conjugate_element
       and x ~~ y                 by eq_conj_def
   Only-if part: x IN R /\ y IN R /\ x ~~ y ==> y IN Conj x
      Note ?k. y = conj x k       by eq_conj_def
        so y IN Conj x            by ring_conjugates_member
*)
val ring_conjugates_element = store_thm(
  "ring_conjugates_element",
  ``!(r s):'a ring. Ring r ==> !x. x IN R ==> !y. y IN Conj x <=> y IN R /\ x ~~ y``,
  metis_tac[ring_conjugates_member, ring_conjugate_element, eq_conj_def]);

(* Theorem: Ring r ==> !x y. x IN R /\ y IN R ==> (x ~~ y <=> y IN Conj x) *)
(* Proof: by eq_conj_def, ring_conjugates_member *)
val eq_conj_in_conjugates = store_thm(
  "eq_conj_in_conjugates",
  ``!(r s):'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> (x ~~ y <=> y IN Conj x)``,
  rw[eq_conj_def, ring_conjugates_member]);

(* Theorem: FiniteField r /\ s <<= r ==> !x y. x IN R /\ y IN R ==> (x ~~ y <=> (Conj x = Conj y)) *)
(* Proof:
   If part: x ~~ y ==> (Conj x = Conj y)
      By EXTENSION, this is to show:
      (1) x' IN Conj x /\ x ~~ y ==> x' IN Conj y
          Note x' IN Conj x
           ==> x' IN R             by ring_conjugates_member_element, x IN R
          Thus x ~~ x'             by eq_conj_in_conjugates, x' IN Conj x
         Since y ~~ x              by eq_conj_sym, FiniteField r /\ s <<= r
           ==> y ~~ x'             by eq_conj_trans
            or x' IN Conj y        by eq_conj_in_conjugates
      (2) x' IN Conj y /\ x ~~ y ==> x' IN Conj x
          Note x' IN Conj y
           ==> x' IN R             by ring_conjugates_member_element, y IN R
          Thus y ~~ x'             by eq_conj_in_conjugates, x' IN Conj y
           ==> x ~~ x'             by eq_conj_trans
            or x' IN Conj x        by eq_conj_in_conjugates

   Only-if part: (Conj x = Conj y) ==> x ~~ y
       Since y IN Conj y           by ring_conjugates_has_self
         ==> y IN Conj x           by Conj x = Conj y
         ==> x ~~ y                by eq_conj_in_conjugates
*)
val eq_conj_eq_conjugages = store_thm(
  "eq_conj_eq_conjugages",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
    !x y. x IN R /\ y IN R ==> (x ~~ y <=> (Conj x = Conj y))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r` by rw[] >>
  rw[EXTENSION, EQ_IMP_THM] >| [
    `x' IN R` by metis_tac[ring_conjugates_member_element] >>
    `x ~~ x'` by rw[eq_conj_in_conjugates] >>
    `y ~~ x'` by metis_tac[eq_conj_sym, eq_conj_trans] >>
    rw[GSYM eq_conj_in_conjugates],
    `x' IN R` by metis_tac[ring_conjugates_member_element] >>
    `y ~~ x'` by rw[eq_conj_in_conjugates] >>
    `x ~~ x'` by metis_tac[eq_conj_trans] >>
    rw[GSYM eq_conj_in_conjugates],
    rw[ring_conjugates_has_self, eq_conj_in_conjugates]
  ]);

(* Theorem: FiniteField r /\ s <<= r ==>
            !x y. x IN R /\ y IN R /\ x ~~ y ==> (forder x = forder y) *)
(* Proof:
   Note x ~~ y
    ==> ?k. y = conj x k       by eq_conj_def
        forder y
      = forder (conj x k)      by above
      = forder x               by finite_field_conjugate_order
*)
val eq_conj_eq_order = store_thm(
  "eq_conj_eq_order",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !x y. x IN R /\ y IN R /\ x ~~ y ==> (forder x = forder y)``,
  metis_tac[eq_conj_def, finite_field_conjugate_order]);

(* Theorem: FiniteField r /\ s <<= r ==>
            !x y. x IN R /\ y IN R ==> (x ~~ y <=> (minimal x = minimal y)) *)
(* Proof:
   If part: x ~~ y ==> (minimal x = minimal y)
      Let p = minimal x.
      Then monic p             by poly_minimal_monic
       and IPoly s p           by poly_minimal_subfield_irreducible
      Note y IN Conj y         by ring_conjugates_has_self
       But Conj y = Conj x     by eq_conj_eq_conjugages, x ~~ y
       and Conj x = roots p    by poly_minimal_roots
      Thus y IN root p
        or root p y            by poly_roots_member
       ==> p = minimal y       by poly_minimal_unique
      Or,
           x ~~ y
       ==> Conj x = Conj y                        by eq_conj_eq_conjugages
       ==> PIFACTOR (Conj x) = PIFACTOR (Conj y)
        or         minimal x = minimal y          by poly_minimal_eq_factors_conjugates

   Only-if part: (minimal x = minimal y) ==> x ~~ y
      Note y IN Conj y             by ring_conjugates_has_self
             = roots (minimal y)   by poly_minimal_roots
             = roots (minimal x)   by given
             = Conj x              by poly_minimal_roots
       ==> x ~~ y                  by eq_conj_in_conjugates

*)
val eq_conj_eq_poly_minimal = store_thm(
  "eq_conj_eq_poly_minimal",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !x y. x IN R /\ y IN R ==> (x ~~ y <=> (minimal x = minimal y))``,
  rpt (stripDup[FiniteField_def]) >>
  rw[EQ_IMP_THM] >-
  metis_tac[eq_conj_eq_conjugages, poly_minimal_eq_factors_conjugates] >>
  metis_tac[ring_conjugates_has_self, poly_minimal_roots, eq_conj_in_conjugates, field_is_ring]);

(* Theorem: Ring r ==> (partition $~~ R = IMAGE Conj R) *)
(* Proof: by partition_elements, ring_conjugates_element *)
val eq_conj_partition_field_carrier = store_thm(
  "eq_conj_partition_field_carrier",
  ``!r:'a ring. Ring r ==> (partition $~~ R = IMAGE Conj R)``,
  rw[partition_elements] >>
  rw[EXTENSION] >>
  metis_tac[ring_conjugates_element]);

(* Theorem: FiniteField r /\ s <<= r ==>
            !n. partition $~~ (orders f* n) = IMAGE Conj (orders f* n) *)
(* Proof:
   Let t = orders f* n, f = \x. equiv_class $~~ t x
   Since partition $~~ t = IMAGE f t                    by partition_elements
   The goal is: x IN IMAGE f t <=> x IN IMAGE Conj t    by EXTENSION

   Note !y. y IN t ==> (Conj y) SUBSET t            by finite_field_conjugates_subset_orders
    and t SUBSET R                                  by field_orders_subset_carrier

   Claim: !y z. y IN t /\ z IN t ==> ({y | y IN t /\ z ~~ y} = Conj z)
   Proof: by EXTENSION,
          x IN {y | y IN t /\ z ~~ y}
      <=> x IN t /\ z ~~ x
      <=> x IN t /\ x IN Conj z                     by eq_conj_in_conjugates, t SUBSET R
      <=> x IN (t INTER Conj z)                     by IN_INTER
      <=> x IN (Conj z) INTER t                     by INTER_COMM
      <=> x IN Conj z                               by SUBSET_INTER_ABSORPTION, (Conj y) SUBSET t

       x IN IMAGE f t
   <=> ?z. z IN t /\ (x = f z)                      by IN_IMAGE
   <=> ?z. z IN t /\ (x = {y | y IN t /\ z ~~ y})   by applying f
   <=> ?z. z IN t /\ (x = Conj z)                   by Claim
   <=> x IN IMAGE Conj t                            by IN_IMAGE
*)
val eq_conj_partition_conjugates = store_thm(
  "eq_conj_partition_conjugates",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !n. partition $~~ (orders f* n) = IMAGE Conj (orders f* n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = orders f* n` >>
  rw[partition_elements] >>
  rw_tac std_ss[EXTENSION] >>
  `!y. y IN t ==> (Conj y) SUBSET t` by rw[finite_field_conjugates_subset_orders, Abbr`t`] >>
  `!y z. y IN t /\ z IN t ==> ({y | y IN t /\ z ~~ y} = Conj z)` by
  (rw[EXTENSION] >>
  `Ring r` by rw[] >>
  `t SUBSET R` by rw[field_orders_subset_carrier, Abbr`t`] >>
  `x IN t /\ z ~~ x <=> x IN t /\ x IN Conj z` by metis_tac[eq_conj_in_conjugates, SUBSET_DEF] >>
  metis_tac[SUBSET_INTER_ABSORPTION, INTER_COMM, IN_INTER]) >>
  qabbrev_tac `f = \x. {y | y IN t /\ x ~~ y}` >>
  `x IN IMAGE f t <=> ?z. z IN t /\ (x = f z)` by metis_tac[IN_IMAGE] >>
  `_ = ?z. z IN t /\ (x = {y | y IN t /\ z ~~ y})` by rw[Abbr`f`] >>
  metis_tac[IN_IMAGE]);

(* Note: compare cyclic_orders_partition
|- !g. cyclic g /\ FINITE G ==> (partition (eq_order g) G = IMAGE (orders g) (divisors (CARD G)))
*)

(* Theorem: Field r ==> !t. FINITE t /\ t SUBSET R ==> INJ PIFACTOR (partition $~~ t) univ(:'a poly) *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) s' IN partition $~~ t ==> PIFACTOR s' IN univ(:'a poly), true  by IN_UNIV
   (2) s1 IN partition $~~ t /\ s2 IN partition $~~ t /\ PIFACTOR s1 = PIFACTOR s2 ==> s1 = s2
        and s' SUBSET t /\ s'' SUBSET t   by partition_SUBSET
       thus s' SUBSET R /\ s'' SUBSET R   by SUBSET_TRANS
        and FINITE s' /\ FINITE s''       by SUBSET_FINITE
       With PIFACTOR s1 = PIFACTOR s2     by given
        ==> s1 = s2                       by poly_prod_factors_eq
*)
val poly_prod_factors_conjugates_inj = store_thm(
  "poly_prod_factors_conjugates_inj",
  ``!r:'a field. Field r ==> !t. FINITE t /\ t SUBSET R ==> INJ PIFACTOR (partition $~~ t) UNIV``,
  rw[INJ_DEF] >>
  `s' SUBSET t /\ s'' SUBSET t` by metis_tac[partition_SUBSET] >>
  `s' SUBSET R /\ s'' SUBSET R` by metis_tac[SUBSET_TRANS] >>
  metis_tac[poly_prod_factors_eq, SUBSET_FINITE]);

(* ------------------------------------------------------------------------- *)
(* Master Polynomial as Product of Minimal Polynomial                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r /\ s <<= r ==> (master (CARD R) = PPIMAGE minimal R) *)
(* Proof:
   Note ring_set_multiplicative_fun r PIFACTOR   by poly_prod_factors_ring_mult_fun
    and R SUBSET R                               by SUBSET_REFL
    ==> INJ PIFACTOR (partition $~~ R) UNIV      by poly_prod_factors_conjugates_inj, R SUBSET R
   Also $~~ equiv_on R                           by eq_conj_equiv_on_field_carrier

     master (CARD R)
   = PIFACTOR R                                  by poly_master_eq_root_factor_product
   = PPIMAGE PIFACTOR (partition $~~ R)          by ring_prod_set_mult_fun_by_partition, $~~ equiv_on R
   = PPIMAGE PIFACTOR (IMAGE Conj R)             by eq_conj_partition_field_carrier
   = PPIMAGE (PIFACTOR o Conj) R                 by IMAGE_CONG, IMAGE_COMPOSE
   = PPIMAGE minimal R                           by poly_minimal_eq_factors_conjugates_compose, IMAGE_CONG
*)
val poly_master_eq_poly_minimal_product = store_thm(
  "poly_master_eq_poly_minimal_product",
  ``!(r:'a field) s. FiniteField r /\ s <<= r ==> (master (CARD R) = PPIMAGE minimal R)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r` by rw[] >>
  `ring_set_multiplicative_fun r PIFACTOR` by rw[poly_prod_factors_ring_mult_fun] >>
  `INJ PIFACTOR (partition $~~ R) UNIV` by rw[poly_prod_factors_conjugates_inj] >>
  `$~~ equiv_on R` by rw[eq_conj_equiv_on_field_carrier] >>
  `master (CARD R) = PIFACTOR R` by rw[poly_master_eq_root_factor_product] >>
  `_  = PPIMAGE PIFACTOR (partition $~~ R)` by rw[ring_prod_set_mult_fun_by_partition] >>
  `_ = PPIMAGE PIFACTOR (IMAGE Conj R)` by rw[eq_conj_partition_field_carrier] >>
  `_ = PPIMAGE minimal R` by metis_tac[poly_minimal_eq_factors_conjugates_compose, IMAGE_COMPOSE, IMAGE_CONG] >>
  rw[]);

(* This is a major alternative expression for master (CARD R) *)

(* Theorem: FiniteField r /\ s <<= r ==> (master (CARD R) = PPROD {minimal x | x | x IN R}) *)
(* Proof: by poly_master_eq_poly_minimal_product *)
val poly_master_eq_poly_minimal_product_alt = store_thm(
  "poly_master_eq_poly_minimal_product_alt",
  ``!(r:'a field) s. FiniteField r /\ s <<= r ==> (master (CARD R) = PPROD {minimal x | x | x IN R})``,
  rpt strip_tac >>
  `IMAGE minimal R = {minimal x | x | x IN R}` by rw[EXTENSION] >>
  metis_tac[poly_master_eq_poly_minimal_product]);

(* ------------------------------------------------------------------------- *)
(* Cyclotomic Polynomial as Product of Minimal Polynomial                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r /\ s <<= r ==>
            !n. cyclo n = PPIMAGE PIFACTOR (partition $~~ (orders f* n)) *)
(* Proof:
   Let t = orders f* n.
   Then cyclo n = PIFACTOR t             by poly_cyclo_def
   Thus the goal is: PIFACTOR t = PPIMAGE PIFACTOR (partition $~~ t)
   Note t SUBSET R                       by field_orders_subset_carrier
    ==> FINITE t                         by SUBSET_FINITE
   Also $~~ equiv_on t                   by eq_conj_equiv_on_orders, FiniteField r /\ s <<= r
    and ring_set_multiplicative_fun r PIFACTOR            by poly_prod_factors_ring_mult_fun
    and INJ PIFACTOR (partition $~~ t) univ(:'a poly)     by poly_prod_factors_conjugates_inj
    ==> PIFACTOR t = PPIMAGE PIFACTOR (partition $~~ t)   by ring_prod_set_mult_fun_by_partition
*)
val poly_cyclo_eq_prod_factors_by_partition = store_thm(
  "poly_cyclo_eq_prod_factors_by_partition",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !n. cyclo n = PPIMAGE PIFACTOR (partition $~~ (orders f* n))``,
  rpt (stripDup[FiniteField_def]) >>
  rw[poly_cyclo_def] >>
  qabbrev_tac `t = orders f* n` >>
  `t SUBSET R` by rw[field_orders_subset_carrier, Abbr`t`] >>
  `FINITE t` by metis_tac[SUBSET_FINITE] >>
  `$~~ equiv_on t` by rw[eq_conj_equiv_on_orders, Abbr`t`] >>
  `ring_set_multiplicative_fun r PIFACTOR` by rw[poly_prod_factors_ring_mult_fun] >>
  `INJ PIFACTOR (partition $~~ t) univ(:'a poly)` by rw[poly_prod_factors_conjugates_inj] >>
  rw[ring_prod_set_mult_fun_by_partition]);

(* This is the first alternative expression for cyclo n *)

(* Theorem: FiniteField r /\ s <<= r ==> !n. cyclo n = PPIMAGE minimal (orders f* n) *)
(* Proof:
   Let t = orders f* n.
   Note !x. x IN t ==> x IN R                by field_orders_element

     cyclo n
   = PPIMAGE PIFACTOR (partition $~~ t)      by poly_cyclo_eq_prod_factors_by_partition
   = PPIMAGE PIFACTOR (IMAGE Conj t)         by eq_conj_partition_conjugates
   = PPROD (IMAGE PIFACTOR (IMAGE Conj t))   by notation
   = PPROD (IMAGE (PIFACTOR o Conj) t)       by IMAGE_COMPOSE
   = PPROD (IMAGE minimal t)                 by poly_minimal_eq_factors_conjugates_compose, IMAGE_CONG
   = PPIMAGE minimal t                       by notation
*)
val poly_cyclo_eq_poly_minimal_product = store_thm(
  "poly_cyclo_eq_poly_minimal_product",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !n. cyclo n = PPIMAGE minimal (orders f* n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = orders f* n` >>
  qabbrev_tac `f = PIFACTOR o Conj` >>
  metis_tac[poly_cyclo_eq_prod_factors_by_partition, eq_conj_partition_conjugates,
             poly_minimal_eq_factors_conjugates_compose, IMAGE_COMPOSE, IMAGE_CONG, field_orders_element]);

(* This expression for (cyclo n) is a major result. *)

(* Theorem: FiniteField r /\ s <<= r ==> !n. cyclo n = PPROD {minimal x | x | x IN (orders f* n)} *)
(* Proof: by poly_cyclo_eq_poly_minimal_product *)
val poly_cyclo_eq_poly_minimal_product_alt = store_thm(
  "poly_cyclo_eq_poly_minimal_product_alt",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !n. cyclo n = PPROD {minimal x | x | x IN (orders f* n)}``,
  rpt strip_tac >>
  `IMAGE minimal (orders f* n) = {minimal x | x | x IN (orders f* n)}` by rw[EXTENSION] >>
  metis_tac[poly_cyclo_eq_poly_minimal_product]);

(* Theorem: FiniteField r /\ s <<= r ==> !n. Poly s (cyclo n) *)
(* Proof:
   Let t = orders f* n
   Then cyclo n = PPIMAGE minimal t         by poly_cyclo_eq_poly_minimal_product
   Note Ring r /\ s <= r                    by field_is_ring, subfield_is_subring
    and t SUBSET R                          by field_orders_subset_carrier
   thus FINITE t                            by SUBSET_FINITE
   Also !x. x IN t ==> Poly s (minimal x)   by poly_minimal_spoly, SUBSET_DEF
   Thus Poly s (cyclo n)                    by subring_poly_prod_set_spoly
*)
val poly_cyclo_spoly = store_thm(
  "poly_cyclo_spoly",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !n. Poly s (cyclo n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = orders f* n` >>
  `cyclo n = PPIMAGE minimal t` by rw[poly_cyclo_eq_poly_minimal_product, Abbr`t`] >>
  `Ring r /\ s <= r` by rw[subfield_is_subring] >>
  `t SUBSET R` by rw[field_orders_subset_carrier, Abbr`t`] >>
  `FINITE t` by metis_tac[SUBSET_FINITE] >>
  `!x. x IN t ==> Poly s (minimal x)` by metis_tac[poly_minimal_spoly, SUBSET_DEF] >>
  rw[subring_poly_prod_set_spoly]);

(* This simple result is actually a major theorem! *)

(* Theorem: FiniteField r /\ s <<= r ==> !p. monic p /\ ipoly p ==>
            !n. 0 < n /\ p pdivides (cyclo n) ==> (deg p = order (ZN n).prod (CARD B)) *)
(* Proof:
   Let t = IMAGE minimal (orders f* n).
   Claim: p IN t
   Proof: Note cyclo n = PPROD t         by poly_cyclo_eq_poly_minimal_product
           and FINITE (orders f* n)      by field_orders_finite
            so FINITE t                  by IMAGE_FINITE
           Now s <= r                    by subfield_is_subring
           and Poly s (cyclo n)          by poly_cyclo_spoly
           and Poly s p                  by poly_irreducible_poly
           ==> poly_monic s p            by subring_poly_monic_iff
           and 0 < deg p                 by poly_irreducible_deg_nonzero, subring_poly_deg
          Note poly_set s t              by monic_irreducible_set_poly_set
           and !p. p IN t
           ==> ?x. x IN (orders f* n) /\ p = minimal x  by IN_IMAGE
           ==>     x IN R /\ p = minimal x         by field_orders_element
           ==>     Monic s p /\ Ipoly s p          by poly_minimal_subfield_property, poly_minimal_subfield_irreducible
          Thus monic_irreducibles_set s t          by above
           ==> poly_set s t                        by monic_irreducible_set_poly_set
            so poly_divides s p (cyclo n)          by subring_poly_divides_iff, poly_monic_pmonic, subring_poly_deg
           and PPROD t = poly_prod_set s t         by subring_poly_prod_set
         Hence p IN t                              by poly_prod_monic_irreducible_set_divisor

   With p IN t                                by Claim
   Thus ?x. x IN (orders f* n) /\ (p = minimal x)   by IN_IMAGE
     or forder x = n /\ (p = minimal x)       by field_orders_element_order
   Note x IN (orders f* n) ==> x IN R+        by field_orders_nonzero_element

   If n = 1,
   Note that cyclo 1 = X - |1|                by poly_cyclo_1
     so deg (cyclo 1) = 1                     by poly_unity_deg, poly_unity_1
   Thus cyclo 1 <> |0|                        by poly_deg_zero
    ==> deg p <= 1                            by poly_field_divides_deg_le, poly_cyclo_poly
   Also 0 < deg p                             by poly_irreducible_deg_nonzero, subring_poly_deg
   Thus deg p = 1
              = order (ZN 1).prod (CARD B) by ZN_order_mod_1

   Otherwise, n <> 1, so x <> #1              by field_order_eq_1
        deg p
      = deg (minimal x)                       by above, p = minimal x
      = degree x                              by notation
      = order (ZN (forder x)).prod (CARD B)   by poly_minimal_deg_eqn, x <> #1
      = order (ZN n).prod (CARD B)            by above, forder x = n
*)
val poly_cyclo_irreducible_factor_deg = store_thm(
  "poly_cyclo_irreducible_factor_deg",
  ``!(r:'a field) s. FiniteField r /\ s <<= r ==> !p. monic p /\ IPoly s p ==>
   !n. 0 < n /\ p pdivides (cyclo n) ==> (deg p = order (ZN n).prod (CARD B))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = IMAGE minimal (orders f* n)` >>
  `p IN t` by
  (`cyclo n = PPROD t` by rw[poly_cyclo_eq_poly_minimal_product, Abbr`t`] >>
  `FINITE t` by rw[field_orders_finite, Abbr`t`] >>
  `s <= r` by rw[subfield_is_subring] >>
  `Poly s (cyclo n)` by rw[poly_cyclo_spoly] >>
  `Poly s p` by rw[poly_irreducible_poly] >>
  `poly_monic s p` by metis_tac[subring_poly_monic_iff] >>
  `0 < deg p` by metis_tac[poly_irreducible_deg_nonzero, subring_poly_deg] >>
  `monic_irreducibles_set s t` by metis_tac[field_orders_element, poly_minimal_subfield_property, poly_minimal_subfield_irreducible, IN_IMAGE] >>
  `poly_set s t` by rw[monic_irreducible_set_poly_set] >>
  metis_tac[poly_prod_monic_irreducible_set_divisor, subring_poly_divides_iff, poly_monic_pmonic, subring_poly_deg, subring_poly_prod_set]) >>
  `?x. x IN (orders f* n) /\ (p = minimal x)` by metis_tac[IN_IMAGE] >>
  `x IN R+` by metis_tac[field_orders_nonzero_element] >>
  `forder x = n` by rw[field_orders_element_order] >>
  Cases_on `n = 1` >| [
    `cyclo 1 = X - |1|` by rw[poly_cyclo_1] >>
    `Ring r /\ #1 <> #0` by rw[] >>
    `deg (cyclo 1) = 1` by metis_tac[poly_unity_deg, poly_unity_1] >>
    `cyclo 1 <> |0|` by metis_tac[poly_deg_zero, DECIDE``1 <> 0``] >>
    `deg p <= 1` by metis_tac[poly_field_divides_deg_le, poly_cyclo_poly, poly_monic_poly] >>
    `0 < deg p` by metis_tac[poly_irreducible_deg_nonzero, subring_poly_deg] >>
    `deg p = 1` by decide_tac >>
    rw[ZN_order_mod_1],
    `x <> #1` by metis_tac[field_nonzero_element, field_order_eq_1] >>
    rw[poly_minimal_deg_eqn]
  ]);

(* Theorem: FiniteField r ==>
            !p. monic p /\ ipoly p ==> !n. 0 < n /\ p pdivides cyclo n ==> (deg p = ordz n (CARD R)) *)
(* Proof: by poly_cyclo_irreducible_factor_deg, subfield_refl.

> poly_cyclo_irreducible_factor_deg |> ISPEC ``r:'a ring`` |> ISPEC ``r:'a ring``;
val it = |- FiniteField r /\ r <<= r ==> !p. monic p /\ ipoly p ==>
     !n. 0 < n /\ p pdivides cyclo n ==> (deg p = ordz n (CARD R)): thm
*)
val poly_cyclo_irreducible_factor_deg_alt = store_thm(
  "poly_cyclo_irreducible_factor_deg_alt",
  ``!r:'a field. FiniteField r ==>
   !p. monic p /\ ipoly p ==> !n. 0 < n /\ p pdivides cyclo n ==> (deg p = ordz n (CARD R))``,
  rw_tac std_ss[poly_cyclo_irreducible_factor_deg, subfield_refl, finite_field_is_field]);

(* ------------------------------------------------------------------------- *)
(* Special subfield factor of Cyclo and Unity polynomials                    *)
(* ------------------------------------------------------------------------- *)

(* Note:
By poly_cyclo_deg_eq_card_roots |- !r. FiniteField r ==> !n. deg (cyclo n) = CARD (roots (cyclo n))
That is, (cyclo n) always splits, in the 'big' Field r.
It is just that, by poly_cyclo_deg_eqn,
|- !r. FiniteField r ==> !n. deg (cyclo n) = if n divides CARD R+ then phi n else 0
That is, if (n divides CARD R+), (cyclo n) is interesting, with (phi n) roots, or (phi n) factors.
If ~(n divides CARD R+), (cyclo n = |1|), so it is not very interesting.
This is how (cyclo n) looks in the 'big' Field r.

However, in a subfield s <<= r, we have poly_cyclo_spoly
|- !r s. FiniteField r /\ s <<= r ==> !n. Poly s (cyclo n)
Now, as a subfield poly, it is not generally splitting.
What are its factors?

So far, we only have poly_cyclo_irreducible_factor_deg
|- !r s. FiniteField r /\ s <<= r ==> !p. monic p /\ IPoly s p ==>
   !n. 1 < n /\ p pdivides cyclo n ==> (deg p = ordz n (CARD B))

For the interesting case n divides CARD R+ ==> coprime n (SUC (CARD R+)) by divides_imp_coprime_with_successor
or coprime n (CARD R)                  by finite_field_carrier_card
Since (CARD R = CARD B ** (r <:> s)    by finite_subfield_card_eqn
we have coprime n (CARD B)             by coprime_iff_coprime_exp

Thus ordz n (CARD B) is well-defined (if it is not well-defined, it is 0, then deg p = |1|.)
Let m = CARD B. We have coprime n m.
Note ordz n m <> 0           by ZN_coprime_order_alt
If ordz n m = 1, then m MOD n = 1  by ZN_order_eq_1
or m = k * n + 1.
But 1 < m by finite_subfield_card_gt_1, so ordz n m <> 1.
Hence deg p <> 0, deg p <> 1, that means 1 < deg p.
*)


(*
By ZN_order_eq_1_by_prime_factors, if 1 < ordz k n, then ?p. prime p /\ p pdivides n /\ 1 < ordz k p
This prime p will be CARD B = p, and d = ordz k p will be the dimension (r <:> s).
With deg h = ordz k (CARD B), so 1 < deg h.
*)

(*
Let CARD R = 3 ** 2 = 9, then CARD R+ = 8.
1 < n /\ n divides 8 means n = 2, 4, 8.
Possible CARD B = 3 ** 1 = 3.
order (ZN 2).prod 3 = ord 2 3 = 1,  and 3^1 MOD 2 = 1.  <- 3 <> 1, but 3 MOD 2 = 1
order (ZN 4).prod 3 = ord 4 3 = 2,  and 3^2 MOD 4 = 1.
order (ZN 8).prod 3 = ord 8 3 = 2,  and 3^2 MOD 8 = 1.

Let CARD R = 3 ** 3 = 27, then CARD R+ = 26.
1 < n /\ n divides 26 means n = 2, 13, 26.
Possible CARD B = 3 ** 1 = 3.
order (ZN 2).prod 3 = ord 2 3 = 1,    and 3^1 MOD 2 = 1. <- 3 <> 1, but 3 MOD 2 = 1.
order (ZN 13).prod 3 = ord 13 3 = 3,  and 3^3 MOD 13 = 1.
order (ZN 26).prod 3 = ord 26 3 = 3,  and 3^3 MOD 26 = 1.

Let CARD R = 2 ** 3 = 8, then CARD R+ = 7.
1 < n /\ n divides 7 means n = 7.
Possible CARD B = 2 ** 1 = 2.
order (ZN 7).prod 2 = ord 7 2 = 3,    and 2^3 MOD 7 = 1.
*)

(* Theorem: FiniteField r /\ s <<= r /\ 1 < (r <:> s) ==>
            !n. 0 < n /\ coprime n (CARD B) /\ (ordz n (CARD B) = (r <:> s)) ==>
            ?h. monic h /\ IPoly s h /\ h pdivides (cyclo n) /\ (deg h = ordz n (CARD B)) *)
(* Proof:
   Let t = IMAGE minimal (orders f* n),
   Note cyclo n = PPROD t             by poly_cyclo_eq_poly_minimal_product
    and n divides (CARD R+)           by subfield_card_coprime_iff
    ==> (orders f* n) <> {}           by finite_field_orders_nonempty_iff, n divides (CARD R+)
     or ?x. x IN (orders f* n)        by MEMBER_NOT_EMPTY
    ==> x IN R+ /\ (forder x = n)     by field_orders_element_property
     or x IN R                        by field_nonzero_element
   Let h = minimal x, then it is to show:
   (1) monic (minimal x)              by poly_minimal_monic
   (2) IPoly s (minimal x)            by poly_minimal_subfield_irreducible
   (3) minimal x pdivides cyclo n
       Note h IN t                    by IN_IMAGE
        and FINITE (orders f* n)      by field_orders_finite
        ==> FINITE t                  by IMAGE_FINITE
       Also (orders f* n) SUBSET R    by field_orders_subset_carrier
        ==> pset t                    by poly_minimal_poly
         so h pdivdes PPROD t         by poly_prod_set_element_divides
   (4) degree x = ordz n (CARD B)
       This is true                   by poly_minimal_deg_eqn, x IN R+
*)
val poly_cyclo_special_subfield_factor = store_thm(
  "poly_cyclo_special_subfield_factor",
  ``!(r s):'a field. FiniteField r /\ s <<= r /\ 1 < (r <:> s) ==>
   !n. 0 < n /\ coprime n (CARD B) /\ (ordz n (CARD B) = (r <:> s)) ==>
   ?h. monic h /\ IPoly s h /\ h pdivides (cyclo n) /\ (deg h = ordz n (CARD B))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = IMAGE minimal (orders f* n)` >>
  `cyclo n = PPROD t` by rw[poly_cyclo_eq_poly_minimal_product, Abbr`t`] >>
  `n divides (CARD R+)` by metis_tac[subfield_card_coprime_iff] >>
  `?x. x IN (orders f* n)` by metis_tac[finite_field_orders_nonempty_iff, MEMBER_NOT_EMPTY] >>
  `x IN R+ /\ (forder x = n)` by metis_tac[field_orders_element_property] >>
  `x IN R` by rw[field_nonzero_element] >>
  qexists_tac `minimal x` >>
  rpt strip_tac >-
  rw[poly_minimal_monic] >-
  rw[poly_minimal_subfield_irreducible] >-
 (`(minimal x) IN t` by rw[Abbr`t`] >>
  `FINITE t` by rw[field_orders_finite, Abbr`t`] >>
  `pset t` by metis_tac[poly_minimal_poly, field_orders_element, IN_IMAGE] >>
  metis_tac[poly_prod_set_element_divides, field_is_ring]) >>
  rw[poly_minimal_deg_eqn]);

(* Theorem: FiniteField r /\ s <<= r /\ 1 < (r <:> s) ==>
            !n. 0 < n /\ coprime n (CARD B) /\ (ordz n (CARD B) = (r <:> s)) ==>
            ?h. monic h /\ IPoly s h /\ h pdivides (unity n) /\
               (deg h = ordz n (CARD B)) /\ (roots h) SUBSET (orders f* n) *)
(* Proof:
   Note poly (unity n)                         by poly_unity_poly
    and poly (cyclo n)                         by poly_cyclo_poly
    Now n divides n                            by DIVIDES_REFL
    ==> (cyclo n) pdivides (unity n)           by poly_cyclo_divides_poly_unity
   The conditions give
       ?h. monic h /\ IPoly s h /\ h pdivides (cyclo n) /\
          (deg h = ordz n (CARD B))            by poly_cyclo_special_subfield_factor
    and poly h                                 by poly_monic_poly
    Let this b h, this is to show:
    (1) h pdivides unity n
        Since h pdivides (cyclo n)             by above, poly_cyclo_special_subfield_factor
          and (cyclo n) pdivides (unity n)     by above, poly_cyclo_divides_poly_unity
          ==> h pdivides (unity n)             by poly_divides_transitive
    (2) roots h SUBSET orders f* n
        Note roots (cyclo n) = orders f* n     by poly_cyclo_roots
         and (roots h) SUBSET roots (cyclo n)  by poly_divides_share_roots
        ==> roots h SUBSET orders f* n         by abive, poly_cyclo_roots
*)
val poly_unity_special_subfield_factor = store_thm(
  "poly_unity_special_subfield_factor",
  ``!(r s):'a field. FiniteField r /\ s <<= r /\ 1 < (r <:> s) ==>
   !n. 0 < n /\ coprime n (CARD B) /\ (ordz n (CARD B) = (r <:> s)) ==>
   ?h. monic h /\ IPoly s h /\ h pdivides (unity n) /\
       (deg h = ordz n (CARD B)) /\ (roots h) SUBSET (orders f* n)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r` by rw[] >>
  `poly (unity n)` by rw[] >>
  `poly (cyclo n)` by rw[poly_cyclo_poly] >>
  `(cyclo n) pdivides (unity n)` by rw[poly_cyclo_divides_poly_unity, DIVIDES_REFL] >>
  `?h. monic h /\ IPoly s h /\ h pdivides (cyclo n) /\ (deg h = ordz n (CARD B))` by rw[poly_cyclo_special_subfield_factor] >>
  `poly h` by rw[] >>
  metis_tac[poly_divides_transitive, poly_divides_share_roots, poly_cyclo_roots]);

(* ------------------------------------------------------------------------- *)
(* Cyclo and Unity polynomials by Irreducible Factors                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==> !n. n divides CARD R+ ==>
            ?s. FINITE s /\ miset s /\ s <> {} /\ (cyclo n = PPROD s) *)
(* Proof:
   Let s = IMAGE factor (orders f* n).
   Then cyclo n = PPROD s               by poly_cyclo_def
   Note (orders f* n) SUBSET R          by field_orders_subset_carrier
    and FINITE (orders f* n)            by field_orders_finite
    and (orders f* n) <> {}             by finite_field_orders_nonempty_iff, n divides CARD R+
   Thus FINITE s                        by IMAGE_FINITE
    and miset s                         by poly_factor_image_monic_irreducibles_set
    and s <> {}                         by IMAGE_EMPTY
   Take this s, and the result follows.
*)
val poly_cyclo_by_distinct_irreducibles = store_thm(
  "poly_cyclo_by_distinct_irreducibles",
  ``!r:'a field. FiniteField r ==> !n. n divides CARD R+ ==>
   ?s. FINITE s /\ miset s /\ s <> {} /\ (cyclo n = PPROD s)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `s = IMAGE factor (orders f* n)` >>
  `(orders f* n) SUBSET R` by rw[field_orders_subset_carrier] >>
  `FINITE (orders f* n)` by rw[field_orders_finite] >>
  `(orders f* n) <> {}` by metis_tac[finite_field_orders_nonempty_iff] >>
  `FINITE s` by rw[Abbr`s`] >>
  `miset s` by metis_tac[poly_factor_image_monic_irreducibles_set] >>
  `s <> {}` by rw[Abbr`s`] >>
  metis_tac[poly_cyclo_def]);

(* Another proof of the same result *)

(* Check this out:
> poly_cyclo_eq_poly_minimal_product |> ISPEC ``r:'a field`` |> ISPEC ``r:'a field``;
val it = |- FiniteField r /\ r <<= r ==> !n. cyclo n = PPIMAGE (poly_minimal r r) (orders f* n): thm
> poly_minimal_monic |> ISPEC ``r:'a field`` |> ISPEC ``r:'a field``;
val it = |- FiniteField r /\ r <<= r ==> !x. x IN R ==> monic (poly_minimal r r x): thm
> poly_minimal_subfield_irreducible |> ISPEC ``r:'a field`` |> ISPEC ``r:'a field``;
val it = |- FiniteField r /\ r <<= r ==> !x. x IN R ==> ipoly (poly_minimal r r x): thm

However, what does (poly_minimal r r x) look like?
> poly_minimal_deg_eqn |> ISPEC ``r:'a field`` |> ISPEC ``r:'a field``;
val it = |- FiniteField r /\ r <<= r ==> !x. x IN R+ /\ x <> #1 ==>
            (deg (poly_minimal r r x) = ordz (forder x) (CARD R)): thm
*)

(* Theorem: FiniteField r ==> !n. n divides CARD R+ ==>
            ?s. FINITE s /\ miset s /\ s <> {} /\ (cyclo n = PPROD s) *)
(* Proof:
   Note r <<= r                    by subfield_refl
   Let s = IMAGE (poly_minimal r r) (orders f* n).
   Then cyclo n = PPROD s          by poly_cyclo_eq_poly_minimal_product
   Note FINITE (orders f* n)       by field_orders_finite
    ==> FINITE s                   by IMAGE_FINITE
   Also (orders f* n) SUBSET R     by field_orders_subset_carrier
    ==> miset s                    by poly_minimal_monic, poly_minimal_subfield_irreducible
    Now (orders f* n) <> {}        by finite_field_orders_nonempty_iff, n divides CARD R+
     so s <> {}                    by IMAGE_EQ_EMPTY
   Take this s, and the result follows.
*)
val poly_cyclo_by_distinct_irreducibles = store_thm(
  "poly_cyclo_by_distinct_irreducibles",
  ``!r:'a field. FiniteField r ==> !n. n divides CARD R+ ==>
   ?s. FINITE s /\ miset s /\ s <> {} /\ (cyclo n = PPROD s)``,
  rpt (stripDup[FiniteField_def]) >>
  `r <<= r` by rw[subfield_refl] >>
  qabbrev_tac `s = IMAGE (poly_minimal r r) (orders f* n)` >>
  `cyclo n = PPROD s` by rw[poly_cyclo_eq_poly_minimal_product, Abbr`s`] >>
  `FINITE (orders f* n)` by rw[field_orders_finite] >>
  `FINITE s` by rw[Abbr`s`] >>
  `(orders f* n) SUBSET R` by rw[field_orders_subset_carrier] >>
  `miset s` by metis_tac[poly_minimal_monic, poly_minimal_subfield_irreducible, IN_IMAGE, SUBSET_DEF] >>
  `(orders f* n) <> {}` by rw[GSYM finite_field_orders_nonempty_iff] >>
  `s <> {}` by rw[IMAGE_EQ_EMPTY, Abbr`s`] >>
  metis_tac[]);

(* Theorem: FiniteField r ==> !n. n divides CARD R+ ==>
            !p q. poly p /\ poly q /\ (p ** char r == q ** char r) (pm (cyclo n)) ==> (p == q) (pm (cyclo n)) *)
(* Proof:
   Note FiniteField r /\ n divides CARD R+
    ==> ?s. FINITE s /\ miset s /\ (cyclo n = PPROD s)  by poly_cyclo_by_distinct_irreducibles
    The result follows                                  by poly_distinct_irreducibles_mod_exp_char_eq
*)
val poly_cyclo_mod_exp_char_eq = store_thm(
  "poly_cyclo_mod_exp_char_eq",
  ``!r:'a field. FiniteField r ==> !n. n divides CARD R+ ==>
   !p q. poly p /\ poly q /\ (p ** char r == q ** char r) (pm (cyclo n)) ==> (p == q) (pm (cyclo n))``,
  metis_tac[poly_cyclo_by_distinct_irreducibles, poly_distinct_irreducibles_mod_exp_char_eq]);

(* Theorem: FiniteField r ==> !n. n divides CARD R+ ==>
            ?s. FINITE s /\ miset s /\ s <> {} /\ (unity n = PPROD s) *)
(* Proof:
   Let c = IMAGE cyclo (divisors n).
   Then unity n = PPROD c                      by poly_unity_eq_poly_cyclo_product, n divides CARD R+
   Note 0 < CARD R+                            by field_nonzero_card_pos
     so 0 < n                                  by ZERO_DIVIDES, CARD R+ <> 0

   Let f = \n. IMAGE factor (orders f* n), s = IMAGE f (divisors n).
   Claim: c = IMAGE PPROD s
   Proof: Note the following:
          !k. cyclo k = PPROD (f k)            by poly_cyclo_def
          !k. (orders f* k) SUBSET R           by field_orders_subset_carrier
      ==> !k. miset (f k)                      by poly_factor_image_monic_irreducibles_set
     Thus c = IMAGE (PPROD o f) (divisors n)   by FUN_EQ_THM
       or c = IMAGE PPROD s                    by IMAGE_COMPOSE

   Step 1: assert properties of s to apply poly_prod_disjoint_bigunion
   Note FINITE (divisors n)        by divisors_finite
     so FINITE s                   by IMAGE_FINITE
   Note !k. FINITE (orders f* k)   by field_orders_finite
     so EVERY_FINITE s             by IN_IMAGE, IMAGE_FINITE
   also !x. x IN s ==> miset x     by poly_factor_image_monic_irreducibles_set, IN_IMAGE

   Claim: PAIR_DISJOINT s
   Proof: This is to show: n' IN (divisors n) /\ n'' IN (divisors n) /\
          IMAGE factor (orders f* n') <> IMAGE factor (orders f* n'') ==>
          DISJOINT (IMAGE factor (orders f* n')) (IMAGE factor (orders f* n''))
     Note INJ factor R univ(:'a poly)     by poly_factor_injective
      and !k. orders f* k SUBSET R        by field_orders_subset_carrier
     By contradiction,
     suppose ~DISJOINT (IMAGE factor (orders f* n')) (IMAGE factor (orders f* n''))
     then ~DISJOINT (orders f* n') (orders f* n'')     by INJ_IMAGE_DISJOINT
      ==> n' = n''                                     by field_orders_disjoint
     This contradicts IMAGE factor (orders f* n') <> IMAGE factor (orders f* n'').

   Therefore, unity n = PPROD (BIGUNION s)        by poly_prod_disjoint_bigunion

   Step 2: assert properties of (BIGUNION s)
   Note FINITE (BIGUNION s)               by FINITE_BIGUNION, FINITE s /\ EVERY_FINITE s
    and miset (BIGUNION s)                by monic_irreducible_set_bigunion

   Claim: (BIGUNION s) <> {}
   Proof: By BIGUNION_EQ_EMPTY, this is to show:
      (1) s <> {}
          Since (divisors n) <> {}              by divisors_eq_empty, 0 < n
          Thus s = IMAGE f (divisors n) <> {}   by IMAGE_EQ_EMPTY
      (2) s <> {{}}
          Note !k. k IN (divisors n) ==> k divides n             by divisors_element_alt, 0 < n
                                     ==> k divides (CARD R+)     by DIVIDES_TRANS, 0 < n, n divides (CARD R+)
          Also !x. x IN s
           ==> ?k. k IN (divisors n) /\ (x = IMAGE factor (orders f* k))  by IN_IMAGE
           ==> x <> {}                    by finite_field_orders_nonempty_iff, IMAGE_EQ_EMPTY, k divides (CARD R+)
          Thus s <> {{}}                  by IN_SING

   Take (BIGUNION s), and the result follows.
*)
val poly_unity_by_distinct_irreducibles = store_thm(
  "poly_unity_by_distinct_irreducibles",
  ``!r:'a field. FiniteField r ==> !n. n divides CARD R+ ==>
   ?s. FINITE s /\ miset s /\ s <> {} /\ (unity n = PPROD s)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `c = IMAGE cyclo (divisors n)` >>
  `unity n = PPROD c` by rw[poly_unity_eq_poly_cyclo_product, Abbr`c`] >>
  `0 < CARD R+` by rw[field_nonzero_card_pos] >>
  `0 < n` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  qabbrev_tac `f = \n. IMAGE factor (orders f* n)` >>
  `!k. cyclo k = PPROD (f k)` by rw[poly_cyclo_def] >>
  `!k. (orders f* k) SUBSET R` by rw[field_orders_subset_carrier] >>
  `!k. miset (f k)` by metis_tac[poly_factor_image_monic_irreducibles_set] >>
  qabbrev_tac `s = IMAGE f (divisors n)` >>
  `c = IMAGE (PPROD o f) (divisors n)` by rw[Abbr`c`, FUN_EQ_THM] >>
  `c = IMAGE PPROD s` by rw[IMAGE_COMPOSE] >>
  `FINITE s` by rw[divisors_finite, Abbr`s`] >>
  `EVERY_FINITE s` by metis_tac[field_orders_finite, IN_IMAGE, IMAGE_FINITE] >>
  `!x. x IN s ==> miset x` by metis_tac[poly_factor_image_monic_irreducibles_set, IN_IMAGE] >>
  `PAIR_DISJOINT s` by
  (rw[Abbr`s`, Abbr`f`] >>
  `INJ factor R univ(:'a poly)` by rw[poly_factor_injective] >>
  metis_tac[field_orders_disjoint, field_orders_subset_carrier, INJ_IMAGE_DISJOINT]) >>
  `unity n = PPROD (BIGUNION s)` by metis_tac[poly_prod_disjoint_bigunion] >>
  `FINITE (BIGUNION s)` by rw[FINITE_BIGUNION] >>
  `(BIGUNION s) <> {}` by
    (rw[BIGUNION_EQ_EMPTY] >-
  rw[divisors_eq_empty, IMAGE_EQ_EMPTY, Abbr`s`] >>
  `!k. k IN (divisors n) ==> k divides (CARD R+)` by metis_tac[divisors_element_alt, DIVIDES_TRANS] >>
  `!n. f n = IMAGE factor (orders f* n)` by rw[Abbr`f`] >>
  `!x. x IN s ==> ?k. k IN (divisors n) /\ (x = IMAGE factor (orders f* k))` by metis_tac[IN_IMAGE] >>
  `!x. x IN s ==> x <> {}` by metis_tac[finite_field_orders_nonempty_iff, IMAGE_EQ_EMPTY] >>
  metis_tac[IN_SING]
  ) >>
  metis_tac[monic_irreducible_set_bigunion]);

(* Theorem: FiniteField r ==> !n. n divides CARD R+ ==>
            !p q. poly p /\ poly q /\ (p ** char r == q ** char r) (pm (unity n)) ==> (p == q) (pm (unity n)) *)
(* Proof: by poly_unity_by_distinct_irreducibles, poly_distinct_irreducibles_mod_exp_char_eq *)
val poly_unity_mod_exp_char_eq = store_thm(
  "poly_unity_mod_exp_char_eq",
  ``!r:'a field. FiniteField r ==> !n. n divides CARD R+ ==>
   !p q. poly p /\ poly q /\ (p ** char r == q ** char r) (pm (unity n)) ==> (p == q) (pm (unity n))``,
  metis_tac[poly_unity_by_distinct_irreducibles, poly_distinct_irreducibles_mod_exp_char_eq]);

(* Theorem: FiniteField r ==> !n. n divides CARD R+ ==>
        !p. poly p /\ (p ** char r == |0|) (pm (unity n)) ==> (p == |0|) (pm (unity n)) *)
(* Proof:
   Note poly |0|             by poly_zero_poly
    and 0 < char r           by finite_field_char_pos
    ==> |0| ** char r = |0|  by poly_zero_exp, char r <> 0
   The result follows        by poly_unity_mod_exp_char_eq
*)
val poly_unity_mod_exp_char_eq_zero = store_thm(
  "poly_unity_mod_exp_char_eq_zero",
  ``!r:'a field. FiniteField r ==> !n. n divides CARD R+ ==>
   !p. poly p /\ (p ** char r == |0|) (pm (unity n)) ==> (p == |0|) (pm (unity n))``,
  rpt (stripDup[FiniteField_def]) >>
  `poly |0|` by rw[] >>
  `0 < char r` by rw[finite_field_char_pos] >>
  `|0| ** char r = |0|` by rw[poly_zero_exp] >>
  rw_tac std_ss[poly_unity_mod_exp_char_eq]);

(* Theorem: FiniteField r ==>
        !n. coprime n (CARD R) /\ 1 < ordz n (CARD R) ==>
        !p q. poly p /\ poly q /\
              (p ** char r == q ** char r) (pm (unity n)) ==> (p == q) (pm (unity n)) *)
(* Proof:
   Let d = ordz n (CARD R), then 0 < d          by given, 1 < d
   Note 1 < CARD R                              by finite_field_card_gt_1
     so 1 < n, then 0 < n                       by ZN_order_with_coprime_1

   Step 1: get a field/subfield pair
   Note FiniteField r /\ 0 < d
    ==> ?z. monic z /\ ipoly z /\ (deg z = d)   by poly_monic_irreducible_exists_alt
    and pmonic z                                by poly_monic_irreducible_property

   Let t = PolyModRing r z, st = PolyModConst r z.
   Then FiniteField t                           by poly_mod_irreducible_finite_field
     so Field t                                 by finite_field_is_field
    and Field st                                by poly_mod_const_field
   Also st <<= t                                by poly_mod_const_subfield_poly_mod
    and st <= t                                 by subfield_is_subring
    and (t <:> st) = deg z                      by poly_mod_const_subfield_dim
    and CARD R = CARD st.carrier                by poly_mod_const_subfield_card
    ==> n divides CARD (ring_nonzero t)         by subfield_card_coprime_iff

   Let c = char r, u = unity n.
       p_ = lift p, q_ = lift q, u_ = lift u.
   The situation:
                                   t = PolyModRing r z, with n divides CARD (ring_nonzero t)
                                   |   (p_ **z c == q_ **z c) (pmod t u_) ==> (p_ == q_) (pmod t u_)
                                   |                   /\                      ||
                                   |                   ||                      ||
       r <-- FieldIso, f = up --> st = PolyModConst r z||                      ||
       start: (p ** c == q ** c) (pm u)
          ==> (p_ **z c == q_ **z c) (pmod t u_)       ||                      \/
         end: (p == q) (pm u) ----------------------------<== (p_ == q_) (pmod t u_)

   Step 2: apply poly_unity_mod_exp_char_eq
   Note pmonic (unity n)                        by poly_unity_pmonic, #1 <> #0 in a field
    and char t = char r                         by poly_mod_ring_char, pmonic z

        (p ** c == q ** c) (pm u)                    by given
    ==> (lift (p ** c) == lift (q ** c) (pmod t u_)  by poly_mod_lift_poly_mod
    ==> (p_ **z c == q_ **z c) (pmod t u_)           by poly_mod_lift_poly_exp
    ==> (p_ == q_) (pmod t u_)                       by poly_unity_mod_exp_char_eq
    ==> (p == q) (pm u)                              by poly_mod_lift_poly_poly_mod
*)
val poly_unity_mod_exp_char_equal = store_thm(
  "poly_unity_mod_exp_char_equal",
  ``!r:'a field. FiniteField r ==>
   !n. coprime n (CARD R) /\ 1 < ordz n (CARD R) ==>
   !p q. poly p /\ poly q /\
         (p ** char r == q ** char r) (pm (unity n)) ==> (p == q) (pm (unity n))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `d = ordz n (CARD R)` >>
  `1 < n` by metis_tac[ZN_order_with_coprime_1, finite_field_card_gt_1] >>
  `0 < n /\ 0 < d /\ d <> 1` by decide_tac >>
  `?z. monic z /\ ipoly z /\ (deg z = d)` by rw[poly_monic_irreducible_exists_alt] >>
  `pmonic z` by rw[poly_monic_irreducible_property] >>
  qabbrev_tac `t = PolyModRing r z` >>
  qabbrev_tac `st = PolyModConst r z` >>
  `FiniteField t` by rw[poly_mod_irreducible_finite_field, Abbr`t`] >>
  `Field t` by rw[finite_field_is_field] >>
  `Field st` by rw[poly_mod_const_field, Abbr`st`] >>
  `st <<= t` by rw[poly_mod_const_subfield_poly_mod, Abbr`t`, Abbr`st`] >>
  `st <= t` by rw[subfield_is_subring] >>
  `(t <:> st) = deg z` by rw[poly_mod_const_subfield_dim, Abbr`t`, Abbr`st`] >>
  `CARD R = CARD st.carrier` by rw[poly_mod_const_subfield_card, Abbr`st`] >>
  `n divides CARD (ring_nonzero t)` by metis_tac[subfield_card_coprime_iff] >>
  qabbrev_tac `c = char r` >>
  `char t = c` by rw[poly_mod_ring_char, Abbr`t`, Abbr`c`] >>
  `polyz (lift p)` by rw[poly_mod_lift_poly] >>
  `polyz (lift q)` by rw[poly_mod_lift_poly] >>
  `lift (p ** c) = (lift p) **z c` by rw[poly_mod_lift_poly_exp] >>
  `lift (q ** c) = (lift q) **z c` by rw[poly_mod_lift_poly_exp] >>
  `lift (unity n) = (unityz n)` by rw[poly_mod_lift_unity] >>
  `pmonic (unity n)` by rw[poly_unity_pmonic] >>
  `((lift p) **z c == (lift q) **z c) (pmod t (unityz n))` by metis_tac[poly_mod_lift_poly_mod, poly_exp_poly, field_is_ring] >>
  `(lift p == lift q) (pmod t (unityz n))` by metis_tac[poly_unity_mod_exp_char_eq] >>
  metis_tac[poly_mod_lift_poly_mod, field_is_ring]);

(* Theorem: FiniteField r ==> !n. coprime n (CARD R) /\ 1 < ordz n (CARD R) ==>
        !p. poly p /\ (p ** char r == |0|) (pm (unity n)) ==> (p == |0|) (pm (unity n)) *)
(* Proof:
   Note poly |0|             by poly_zero_poly
    and 0 < char r           by finite_field_char_pos
    ==> |0| ** char r = |0|  by poly_zero_exp, char r <> 0
   The result follows        by poly_unity_mod_exp_char_equal
*)
val poly_unity_mod_exp_char_equal_zero = store_thm(
  "poly_unity_mod_exp_char_equal_zero",
  ``!r:'a field. FiniteField r ==> !n. coprime n (CARD R) /\ 1 < ordz n (CARD R) ==>
   !p. poly p /\ (p ** char r == |0|) (pm (unity n)) ==> (p == |0|) (pm (unity n))``,
  rpt (stripDup[FiniteField_def]) >>
  `poly |0|` by rw[] >>
  `0 < char r` by rw[finite_field_char_pos] >>
  `|0| ** char r = |0|` by rw[poly_zero_exp] >>
  rw_tac std_ss[poly_unity_mod_exp_char_equal]);

(* ------------------------------------------------------------------------- *)
(* Unity Roots by Master Roots                                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==> (roots (unity (CARD R+)) = R+) *)
(* Proof:
   Let p = unity (CARD R+).
   Then poly X                by poly_X
    and poly p                by poly_unity_poly
   Note 0 < CARD R+           by field_nonzero_card_pos
     so #0 ** (CARD R+) = #0  by field_zero_exp
     or #0 NOTIN roots p      by poly_unity_root_property, poly_roots_member
        R+
      = R DIFF {#0}                            by field_nonzero_def
      = (roots (master (CARD R))) DIFF {#0}    by poly_master_roots_all
      = (roots (X * p)) DIFF {#0}              by poly_master_by_poly_unity
      = ((roots X) UNION (roots p)) DIFF {#0}  by poly_roots_mult
      = ({#0} UNION (roots p)) DIFF {#0}       by poly_roots_X
      = (roots p) DIFF {#0}                    by DIFF_SAME_UNION
      = (roots p) DELETE #0                    by DELETE_DEF
      = roots p                                by DELETE_NON_ELEMENT
*)
val poly_unity_roots_by_master_roots = store_thm(
  "poly_unity_roots_by_master_roots",
  ``!r:'a field. FiniteField r ==> (roots (unity (CARD R+)) = R+)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0 /\ #0 IN R` by rw[] >>
  qabbrev_tac `p = unity (CARD R+)` >>
  `poly X /\ poly p` by rw[Abbr`p`] >>
  `0 < CARD R+` by rw[field_nonzero_card_pos] >>
  `#0 ** (CARD R+) = #0` by metis_tac[field_zero_exp, NOT_ZERO_LT_ZERO] >>
  `#0 NOTIN roots p` by metis_tac[poly_unity_root_property, poly_roots_member] >>
  `R+ = R DIFF {#0}` by rw_tac std_ss[field_nonzero_def] >>
  `_ = (roots (master (CARD R))) DIFF {#0}` by rw_tac std_ss[poly_master_roots_all] >>
  `_ = (roots (X * p)) DIFF {#0}` by rw_tac std_ss[Once poly_master_by_poly_unity, Abbr`p`] >>
  `_ = ((roots X) UNION (roots p)) DIFF {#0}` by metis_tac[poly_roots_mult] >>
  `_ = ({#0} UNION (roots p)) DIFF {#0}` by rw[poly_roots_X] >>
  `_ = (roots p) DIFF {#0}` by rw[DIFF_SAME_UNION] >>
  `_ = (roots p) DELETE #0` by rw[DELETE_DEF] >>
  `_ = roots p` by metis_tac[DELETE_NON_ELEMENT] >>
  rw[]);

(* This is put here because, to be clean, ffUnity does not know about ffMaster.
   This script is the first one that knows about both ffUnity and ffMaster.
*)

(* Theorem: FiniteField r ==> (unity (CARD R+) = PIFACTOR R+) *)
(* Proof:
   Note 0 < CARD R+                      by field_nonzero_card_pos
    and roots (unity (CARD R+)) = R+     by poly_unity_roots_by_master_roots
   Also monic (unity (CARD R+))          by poly_unity_monic, 10 < CARD R+
    and deg (unity (CARD R+)) = CARD R+  by poly_unity_deg
   Thus unity (CARD R+) = PIFACTOR R+    by poly_eq_prod_factor_roots
*)
val poly_unity_eq_root_factor_product = store_thm(
  "poly_unity_eq_root_factor_product",
  ``!r:'a field. FiniteField r ==> (unity (CARD R+) = PIFACTOR R+)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `0 < CARD R+` by rw[field_nonzero_card_pos] >>
  `roots (unity (CARD R+)) = R+` by rw[poly_unity_roots_by_master_roots] >>
  `monic (unity (CARD R+))` by rw[] >>
  `deg (unity (CARD R+)) = CARD R+` by rw[] >>
  metis_tac[poly_eq_prod_factor_roots]);

(* Theorem: FiniteField r ==> (master (CARD R) = PPROD {X - c * |1| | c | c IN R}) *)
(* Proof:
   Note 0 < CARD R+                           by field_nonzero_card_pos
    and roots (unity (CARD R+)) = R+          by poly_unity_roots_by_master_roots
   Also monic (unity (CARD R+))               by poly_unity_monic, 10 < CARD R+
    and deg (unity (CARD R+)) = CARD R+       by poly_unity_deg
   Thus unity (CARD R+)
      = PPROD {X - c * |1| | c | c IN R+ }    by poly_eq_prod_factor_roots_alt
*)
val poly_unity_eq_root_factor_product_alt = store_thm(
  "poly_unity_eq_root_factor_product_alt",
  ``!r:'a field. FiniteField r ==> (unity (CARD R+) = PPROD {X - c * |1| | c | c IN R+})``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `0 < CARD R+` by rw[field_nonzero_card_pos] >>
  `roots (unity (CARD R+)) = R+` by rw[poly_unity_roots_by_master_roots] >>
  `monic (unity (CARD R+))` by rw[] >>
  `deg (unity (CARD R+)) = CARD R+` by rw[] >>
  metis_tac[poly_eq_prod_factor_roots_alt]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
