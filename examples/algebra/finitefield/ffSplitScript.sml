(* ------------------------------------------------------------------------- *)
(* Splitting Field.                                                          *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ffSplit";

(* ------------------------------------------------------------------------- *)



open jcLib;


(* Get dependent theories local *)
open ffBasicTheory;
open ffAdvancedTheory;
open ffPolyTheory;
open ffCycloTheory;
open ffConjugateTheory;
open ffMasterTheory;
open ffMinimalTheory;
open ffUnityTheory;
open ffExistTheory;
open ffExtendTheory;

open bagTheory; (* also has MEMBER_NOT_EMPTY *)

(* open dependent theories *)
open prim_recTheory pred_setTheory listTheory arithmeticTheory;

open helperNumTheory helperSetTheory helperListTheory helperFunctionTheory;

open dividesTheory gcdTheory;

open monoidTheory groupTheory ringTheory fieldTheory;
open monoidInstancesTheory;
open groupInstancesTheory;
open ringInstancesTheory;
open fieldInstancesTheory;
open ringUnitTheory;
open ringMapTheory fieldMapTheory;

open subgroupTheory;
open groupOrderTheory;
open fieldOrderTheory;

open groupCyclicTheory;

open ringBinomialTheory;

open polynomialTheory polyWeakTheory polyRingTheory polyFieldTheory;
open polyDivisionTheory polyBinomialTheory;
open polyDividesTheory;
open polyMonicTheory;
open polyRootTheory;
open polyFieldDivisionTheory;
open polyFieldModuloTheory;
open polyRingModuloTheory;
open polyModuloRingTheory;

open polyIrreducibleTheory;
open polyGCDTheory;
open polyMultiplicityTheory;
open polyMapTheory;

open polyProductTheory; (* for PPROD *)

open GaussTheory; (* for divisors *)


(* ------------------------------------------------------------------------- *)
(* Splitting Field Documentation                                             *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   splits p     = poly_splits (r:'a field) p
   down         = LINV up R
   FieldHigh n  = field_poly_extend_high (r:'a field) n
   FieldLow n   = field_poly_extend_low (r:'a field) n
   SplitHigh n  = FieldHigh (ordz n (CARD R))
   SplitLow n   = FieldLow (ordz n (CARD R))
   Phi n m      = MAP down (poly_cyclo (SplitHigh n) m)
   cyclo_ n     = poly_cyclo (r_:'b field) n
   mini n       = poly_mini r s n

   PHI k        = poly_PHI (r:'a field) (n:num) k
*)
(* Definitions and Theorems (# are exported):

   Helper:
   IN_SET_OF_BAG_NONZERO        |- !b x. x IN SET_OF_BAG b <=> b x <> 0
   BAG_CARD_EQ_CARD_SET_OF_BAG  |- !b. FINITE_BAG b ==> (!e. e ⋲ b ==> (b e = 1)) ==> (BAG_CARD b = CARD (SET_OF_BAG b))

   Bag of Roots:
   poly_root_multiplicity_mult_bag_union
                              |- !r. Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| ==>
                                     (multiplicity (p * q) = BAG_UNION (multiplicity p) (multiplicity q))
   poly_root_multiplicity_set_of_bag
                              |- !r. Ring r ==>
                                 !p. poly p /\ p <> |0| ==> (SET_OF_BAG (multiplicity p) = roots p)
   poly_root_multiplicity_finite_bag
                              |- !r. Field r ==> !p. poly p /\ p <> |0| ==> FINITE_BAG (multiplicity p)
   poly_root_multiplicity_factor_sing_bag
                              |- !r. Ring r /\ #1 <> #0 ==>
                                 !c. c IN R ==> (multiplicity (factor c) = {|c|})
   poly_root_multiplicity_nonzero_const_empty
                              |- !r. Ring r ==> !c. c IN R /\ c <> #0 ==> (multiplicity [c] = {||})

   Splitting Field of Polynomial:
   splitting_def               |- !r p. splitting r p <=> (deg p = BAG_CARD (multiplicity p))
   splitting_const             |- !r. Ring r ==> !c. c IN R /\ c <> #0 ==> splitting r [c]
   splitting_factor_splitting  |- !r. Field r ==> !c. c IN R ==>
                                  !p. poly p /\ p <> |0| /\ splitting r p ==> splitting r (factor c * p)
   poly_splitting_field_exists |- !r. FiniteField r /\ INFINITE univ(:'a) ==>
                                  !p. poly p /\ 0 < deg p ==>
                                  ?s t f. FieldIso f r s /\ s <<= t /\ FINITE C /\ splitting t (MAP f p)

   Finite Field Existence by Splitting Field:
   poly_separable_bag_of_roots             |- !r. Field r ==> !p. poly p /\ separable p ==>
                                                  (BAG_CARD (multiplicity p) = CARD (roots p))
   finite_field_prime_order_exists         |- !p. prime p /\ INFINITE univ(:'a) ==>
                                              ?r. FiniteField r /\ (CARD R = p)
   finite_field_prime_power_order_exists   |- !p n. prime p /\ 0 < n /\ INFINITE univ(:'a) ==>
                                                ?r. FiniteField r /\ (CARD R = p ** n)
   finite_field_is_master_splitting_field  |- !r. FiniteField r ==> splitting r (master (CARD R))

   Splitting Field of Polynomial (almost):
   splits_in_def          |- !p r. p splits_in r <=>
                             ?c. c IN R /\ c <> #0 /\ (p = c * PPIMAGE (\x. term p x) (roots p))
   splits_in_const        |- !r. Ring r ==> !c. c IN R /\ c <> #0 ==> [c] splits_in r
   splits_in_factor       |- !r. Ring r /\ #1 <> #0 ==> !c. c IN R ==> factor c splits_in r
   splits_in_factor_cmult |- !r. Field r ==> !b c. b IN R /\ b <> #0 /\ c IN R ==> b * factor c splits_in r
   splits_in_factor_const |- !r. Field r ==> !b c. b IN R /\ b <> #0 /\ c IN R ==> factor c * [b] splits_in r
   splits_in_factor_exp   |- !r. Field r ==> !b c. b IN R /\ b <> #0 /\ c IN R ==>
                                             !n. b * factor c ** n splits_in r

   Splitting Field of Polynomial (old):
   poly_splits_def        |- !r p. splits p <=> (CARD (roots p) = deg p)
   poly_splits_nonzero    |- !r. FiniteField r ==> !p. splits p ==> p <> |0|
   poly_zero_splits_not   |- !r. FiniteRing r ==> ~splits |0|
   poly_X_splits          |- !r. Ring r /\ #1 <> #0 ==> splits X
   poly_splits_mult       |- !r. Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| /\
                                 DISJOINT (roots p) (roots q) /\ splits p /\ splits q ==> splits (p * q)
   poly_splits_mult_each  |- !r. Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| /\
                                 DISJOINT (roots p) (roots q) /\ splits p /\ splits (p * q) ==> splits q
   poly_splits_mult_iff   |- !r. Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| /\
                                 DISJOINT (roots p) (roots q) /\ splits p ==> (splits (p * q) <=> splits q)

   Splitting Field of Unity Polynomial:
   poly_unity_splitting_condition  |- !r. FiniteField r ==>
                                      !n. 0 < n ==> (splits (unity n) <=> n divides CARD R+)

   Splitting Condition of Master Polynomial:
   poly_master_splitting_condition
                           |- !r. FiniteField r ==> !n. 0 < n ==> (splits (master n) <=> n - 1 divides CARD R+)
   poly_master_char_n_splitting
                           |- !r. FiniteField r ==> !n. splits (master (char r ** n)) <=> n divides fdim r

   Another proof of subfield existence:
   poly_master_roots_subfield_dim    |- !r. FiniteField r ==> !n. n divides fdim r ==>
                                            (fdim (subset_field r (roots (master (char r ** n)))) = n)
   finite_field_subfield_exists_iff  |- !r. FiniteField r ==>
                                        !n. n divides fdim r <=> ?s. s <<= r /\ (fdim s = n)

   Splitting Field Equivalence:
   poly_splits_factor_prod_deg     |- !r. Field r ==> !p. poly p /\ p <> |0| ==>
                                          (splits p <=> (deg (PFROOTS p) = deg p))
   poly_splits_monic_alt           |- !r. Field r ==> !p. monic p ==> (splits p <=> (p = PFROOTS p))

   Cyclotomic Factorisation of Unity Polynomial:

   Inverse Map for Field Isomorphism:
   field_iso_up_down        |- !r s. Field r /\ Field s ==> FieldIso (\e. up e) r s ==> FieldIso down s r
   field_iso_poly_up_down   |- !r s. (r === s) (\e. up e) ==>
                               !p q. poly p /\ (q = MAP (\e. up e) p) <=> Poly s q /\ (p = MAP down q)

   Polynomial Field Extension:
   field_poly_extend_exists   |- !r n. FiniteField r /\ 0 < n ==>
                                 ?t st. FiniteField t /\ st <<= t /\
                                        FieldIso (\e. up e) r st /\ ((t <:> st) = n) /\
                                        ?z. monic z /\ ipoly z /\ (deg z = n) /\
                                            (t = PolyModRing r z) /\ (st = PolyModConst r z)
   field_poly_extend_def      |- !r n. FiniteField r /\ 0 < n ==>
                                       FiniteField (FieldHigh n) /\ FieldLow n <<= FieldHigh n /\
                                       FieldIso (\e. up e) r (FieldLow n) /\ ((FieldHigh n <:> FieldLow n) = n) /\
                                       ?z. monic z /\ ipoly z /\ (deg z = n) /\
                                           (FieldHigh n = PolyModRing r z) /\ (FieldLow n = PolyModConst r z)
   field_poly_extend_property |- !r n. FiniteField r /\ 0 < n ==>
                                       (let t = FieldHigh n in let st = FieldLow n in
                                        FiniteField t /\ st <<= t /\ FieldIso (\e. up e) r st /\ ((t <:> st) = n))
   field_poly_extend_irreducible_exists
                              |- !r n. FiniteField r /\ 0 < n ==> ?z. monic z /\ ipoly z /\ (deg z = n) /\
                                       (FieldHigh n = PolyModRing r z) /\ (FieldLow n = PolyModConst r z)
   field_poly_extend_ids      |- !r n. FiniteField r /\ 0 < n ==>
                                 (let t = FieldHigh n in let st = FieldLow n in
                                  (st.sum.id = |0|) /\ (st.prod.id = |1|) /\
                                  (t.sum.id = |0|) /\ (t.prod.id = |1|))
   field_poly_extend_cards    |- !r n. FiniteField r /\ 0 < n ==>
                                       (CARD (FieldLow n).carrier = CARD R) /\
                                       (CARD (FieldHigh n).carrier = CARD R ** n)
   field_poly_extend_master   |- !r k. FiniteField r /\ 0 < k ==>
                                 (let t = FieldHigh k in let st = FieldLow k in
                                  !n. (Master t n = Master st n) /\
                                      (Master st n = MAP (\e. up e) (master n)) /\
                                      (master n = MAP down (Master st n)))
   field_poly_extend_unity    |- !r k. FiniteField r /\ 0 < k ==>
                                 (let t = FieldHigh k in let st = FieldLow k in
                                  !n. (Unity t n = Unity st n) /\
                                      (Unity st n = MAP (\e. up e) (unity n)) /\
                                      (unity n = MAP down (Unity st n)))

   Polynomial Splitting Field Extension:
   finite_field_card_coprime_pos     |- !r. FiniteField r ==> !n. coprime n (CARD R) ==> 0 < n
   field_split_extend_property       |- !r n. FiniteField r /\ coprime n (CARD R) ==>
                                        (let t = SplitHigh n in let st = SplitLow n in
                                         FiniteField t /\ st <<= t /\ FieldIso (\e. up e) r st /\
                                         ((t <:> st) = ordz n (CARD R)) /\ n divides CARD (ring_nonzero t))
   field_split_extend_irreducible_exist
                                     |- !r n. FiniteField r /\ coprime n (CARD R) ==>
                                        ?z. monic z /\ ipoly z /\ (deg z = ordz n (CARD R)) /\
                                            (SplitHigh n = PolyModRing r z) /\ (SplitLow n = PolyModConst r z)
   field_split_extend_ids            |- !r n. FiniteField r /\ coprime n (CARD R) ==>
                                        (let t = SplitHigh n in let st = SplitLow n in
                                         (st.sum.id = |0|) /\ (st.prod.id = |1|) /\
                                         (t.sum.id = |0|) /\ (t.prod.id = |1|))
   field_split_extend_cards          |- !r n. FiniteField r /\ coprime n (CARD R) ==>
                                              (CARD (SplitLow n).carrier = CARD R) /\
                                              (CARD (SplitHigh n).carrier = CARD R ** ordz n (CARD R))
   field_split_extend_master         |- !r k. FiniteField r /\ coprime k (CARD R) ==>
                                        (let t = SplitHigh k in let st = SplitLow k in
                                         !n. (Master t n = Master st n) /\
                                             (Master st n = MAP (\e. up e) (master n)) /\
                                             (master n = MAP down (Master st n)))
   field_split_extend_unity          |- !r k. FiniteField r /\ coprime k (CARD R) ==>
                                        (let t = SplitHigh k in let st = SplitLow k in
                                         !n. (Unity t n = Unity st n) /\
                                             (Unity st n = MAP (\e. up e) (unity n)) /\
                                             (unity n = MAP down (Unity st n)))
   field_split_extend_splits_unity   |- !r n. FiniteField r /\ coprime n (CARD R) ==>
                                        (let t = SplitHigh n in poly_splits t (Unity t n))
   field_split_extend_unity_factors  |- !r n. FiniteField r /\ coprime n (CARD R) ==>
                                        (let t = SplitHigh n in
                                         Unity t n = poly_prod_image t (poly_cyclo t) (divisors n))

   Cyclotomic Factorisation of Unity:
   poly_phi_poly        |- !r k. FiniteField r /\ coprime k (CARD R) ==> !n. poly (Phi k n)
   poly_phi_monic       |- !r k. FiniteField r /\ coprime k (CARD R) ==> !n. monic (Phi k n)
   poly_phi_deg         |- !r k. FiniteField r /\ coprime k (CARD R) ==> !n. deg (Phi k n) =
                                 if n divides CARD (ring_nonzero (SplitHigh k)) then phi n else 0
   poly_phi_deg_weak    |- !r k. FiniteField r /\ coprime k (CARD R) ==>
                           !n. n divides k ==> (deg (Phi k n) = phi n)
   poly_phi_up_cyclo    |- !r k. FiniteField r /\ coprime k (CARD R) ==>
                           !n. MAP (\e. up e) (Phi k n) = poly_cyclo (SplitHigh k) n
   poly_unity_cyclo_factors  |- !r n. FiniteField r /\ coprime n (CARD R) ==>
                                      (unity n = PPIMAGE (\m. Phi n m) (divisors n))
   poly_unity_cyclo_factors_alt
                             |- !r n. FiniteField r /\ coprime n (CARD R) ==>
                                      (unity n = PPROD {Phi n m | m | m IN divisors n})
   poly_phi_divides_unity    |- !r k. FiniteField r /\ coprime k (CARD R) ==>
                                !n. n divides k ==> Phi k n pdivides unity k /\ (deg (Phi k n) = phi n)
   poly_phi_root_order       |- !r k. FiniteField r /\ coprime k (CARD R) ==>
                                      (let t = SplitHigh k in
                                       !x n. x IN poly_roots t (MAP (\e. up e) (Phi k n)) ==>
                                             (order (t.prod excluding |0|) x = n))
   poly_unity_phi_factor_property    |- !r k. FiniteField r /\ coprime k (CARD R) ==> !n. n divides k ==>
                                              Phi k n pdivides unity k /\ (deg (Phi k n) = phi n) /\
                                              (let t = SplitHigh k in
                                               !x. x IN poly_roots t (MAP (\e. up e) (Phi k n)) ==>
                                                   (order (t.prod excluding |0|) x = n))
   poly_phi_irreducible_factor_deg   |- !r k. FiniteField r /\ coprime k (CARD R) ==>
                                        !p. monic p /\ ipoly p ==>
                                        !n. 0 < n /\ p pdivides Phi k n ==> (deg p = ordz n (CARD R))

   Unity Splitting Field:
   unity_splitting_field   |- !r. FiniteField r ==> !z. monic z /\ ipoly z ==>
                              !n. 0 < n /\ (deg z = ordz n (CARD R)) ==>
                                  poly_splits (PolyModRing r z) (unityz n)
   unity_splitting_deg_pos |- !r. FiniteField r ==> !n. splits (unity n) ==> 0 < n
   splitting_field_uroots_card
                           |- !r. Field r ==> !n. splits (unity n) <=> (CARD (roots (unity n)) = n)
   splitting_field_uroots_primitive
                           |- !r. FiniteField r ==> !n. splits (unity n) ==>
                              ?x. x IN roots (unity n) /\ (order f* x = n)
   poly_primitive_root_of_unity_order
                           |- !r. FiniteField r ==> !z. monic z /\ ipoly z ==>
                              !n. 0 < n /\ coprime n (CARD R) /\ (deg z = ordz n (CARD R)) ==>
                              ?p. poly p /\ p <> |0| /\ deg p < deg z /\
                                    (p ** n == |1|) (pm z) /\ (forderz p = n)

   More Field Isomorphism Theorems:
   field_iso_image_factor     |- !r r_ f. (r === r_) f ==> !s. s SUBSET R ==>
                                          (IMAGE (MAP f o factor) s = IMAGE factor_ (IMAGE f s))
   field_iso_image_factor_orders
                              |- !r r_ f. (r === r_) f ==>
                                 !n. IMAGE (MAP f o factor) (orders f* n) = IMAGE factor_ (orders f_* n)
   poly_set_image_factor      |- !r. Ring r /\ #1 <> #0 ==> !s. s SUBSET R ==> pset (IMAGE factor s)
   field_iso_poly_cyclo       |- !r r_ f. FiniteField r /\ (r === r_) f ==> !n. MAP f (cyclo n) = cyclo_ n
   poly_minimal_divides_cyclo_order
                              |- !r s. FiniteField r /\ s <<= r ==>
                                 !x. x IN R+ ==> minimal x pdivides cyclo (forder x)
   poly_minimal_root_order    |- !r s. FiniteField r /\ s <<= r ==>
                                 !x y. x IN R /\ y IN R /\ root (minimal x) y ==> (forder y = forder x)

   The Minimal Polynomial by Element Order:
   poly_mini_def              |- !r s n. mini n = minimal (CHOICE (orders f* n))
   poly_mini_in_image_minimal_orders
                              |- !r s. FiniteField r /\ s <<= r ==>
                                 !n. n divides CARD R+ ==> mini n IN IMAGE minimal (orders f* n)
   poly_mini_monic            |- !r s. FiniteField r /\ s <<= r ==> !n. n divides CARD R+ ==> monic (mini n)
   poly_mini_poly             |- !r s. FiniteField r /\ s <<= r ==> !n. n divides CARD R+ ==> poly (mini n)
   poly_mini_subfield_irreducible
                              |- !r s. FiniteField r /\ s <<= r ==> !n. n divides CARD R+ ==> IPoly s (mini n)
   poly_mini_subfield_poly    |- !r s. FiniteField r /\ s <<= r ==> !n. n divides CARD R+ ==> Poly s (mini n)
   poly_mini_subfield_monic   |- !r s. FiniteField r /\ s <<= r ==> !n. n divides CARD R+ ==> Monic s (mini n)
   poly_mini_deg                   |- !r s. FiniteField r /\ s <<= r ==>
                                      !n. n divides CARD R+ ==> (deg (mini n) = ordz n (CARD B))
   poly_mini_divides_poly_cyclo    |- !r s. FiniteField r /\ s <<= r ==>
                                      !n. n divides CARD R+ ==> mini n pdivides cyclo n
   poly_mini_divides_poly_unity    |- !r s. FiniteField r /\ s <<= r ==>
                                      !n. n divides CARD R+ ==> mini n pdivides unity n
   poly_mini_root_order            |- !r s. FiniteField r /\ s <<= r ==> !n. n divides CARD R+ ==>
                                      !x. x IN R /\ root (mini n) x ==> (forder x = n)

   Another Cyclotomic Factorisation of Unity Polynomial:
   poly_unity_splitting_field_exists
                                   |- !r n. FiniteField r /\ coprime n (CARD R) ==>
                                      ?t st. FiniteField t /\ st <<= t /\ FieldIso (\e. up e) r st /\
                                             poly_splits t (Unity t n)
   poly_unity_cyclo_factor_exists  |- !r n. FiniteField r /\ coprime n (CARD R) ==>
                                      ?f. (f 0 = |1|) /\ (f 1 = X - |1|) /\ (!k. monic (f k)) /\
                                          (!k. k divides n ==> (deg (f k) = phi k)) /\
                                          (unity n = PPIMAGE f (divisors n))
   poly_PHI_def    |- !r n. FiniteField r /\ coprime n (CARD R) ==>
                            (PHI 0 = |1|) /\ (PHI 1 = X - |1|) /\ (!k. monic (PHI k)) /\
                            (!k. k divides n ==> (deg (PHI k) = phi k)) /\
                            (unity n = PPIMAGE PHI (divisors n))
   poly_PHI_0      |- !r n. FiniteField r /\ coprime n (CARD R) ==> (PHI 0 = |1|)
   poly_PHI_1      |- !r n. FiniteField r /\ coprime n (CARD R) ==> (PHI 1 = X - |1|)
   poly_PHI_poly   |- !r n. FiniteField r /\ coprime n (CARD R) ==> !k. poly (PHI k)
   poly_PHI_monic  |- !r n. FiniteField r /\ coprime n (CARD R) ==> !k. monic (PHI k)
   poly_PHI_deg    |- !r n. FiniteField r /\ coprime n (CARD R) ==> !k. k divides n ==> (deg (PHI k) = phi k)
   poly_unity_eq_poly_PHI_product
                   |- !r n. FiniteField r /\ coprime n (CARD R) ==> (unity n = PPIMAGE PHI (divisors n))

*)

(* ------------------------------------------------------------------------- *)
(* Helper                                                                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: x IN SET_OF_BAG b <=> b x <> 0 *)
(* Proof: by definitions *)
val IN_SET_OF_BAG_NONZERO = store_thm(
  "IN_SET_OF_BAG_NONZERO",
  ``!b x. x IN SET_OF_BAG b <=> b x <> 0``,
  rw[SET_OF_BAG, BAG_IN, BAG_INN]);

(* Theorem: FINITE_BAG b ==> (!e. BAG_IN e b ==> (b e = 1)) ==> (BAG_CARD b = CARD (SET_OF_BAG b)) *)
(* Proof:
   By finite induction on b.
   Base: BAG_CARD {||} = CARD (SET_OF_BAG {||})
           BAG_CARD {||}
         = 0                       by BAG_CARD_EMPTY
         = CARD {}                 by CARD_EMPTY
         = CARD (SET_OF_BAG {||})  by SET_OF_BAG_EQ_EMPTY
   Step: (!e. BAG_IN e b ==> (b e = 1)) ==> (BAG_CARD b = CARD (SET_OF_BAG b)) ==>
         BAG_CARD (BAG_INSERT e b) = CARD (SET_OF_BAG (BAG_INSERT e b))
         After simplication by BAG_CARD_THM, BAG_INSERT, SET_OF_BAG_INSERT, BAG_IN, BAG_INN,
         This comes down to:
         (1) b e >= 1 ==> BAG_CARD b + 1 = CARD (SET_OF_BAG b)
             In this case, b e + 1 = 1     by implication.
             Thus b e = 0                  by arithmetic
             This contradicts b e >= 1.
         (2) ~(b e >= 1) ==> BAG_CARD b = CARD (SET_OF_BAG b)
             In this case, !e'. b e' >= 1 ==> (b e' = 1)   by implication
             Applying induction hypothesis, the result follows.
*)
val BAG_CARD_EQ_CARD_SET_OF_BAG = store_thm(
  "BAG_CARD_EQ_CARD_SET_OF_BAG",
  ``!b:'a bag. FINITE_BAG b ==> (!e. BAG_IN e b ==> (b e = 1)) ==> (BAG_CARD b = CARD (SET_OF_BAG b))``,
  Induct_on `FINITE_BAG` >>
  rpt strip_tac >-
  rw[] >>
  rw[BAG_CARD_THM] >>
  fs[BAG_INSERT, SET_OF_BAG_INSERT] >>
  fs[BAG_IN, BAG_INN, ADD1] >>
  rw[] >| [
    `b e + 1 = 1` by metis_tac[] >>
    decide_tac,
    metis_tac[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Bag of Roots                                                              *)
(* ------------------------------------------------------------------------- *)


(* Theorem: Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| ==>
            (multiplicity (p * q) = BAG_UNION (multiplicity p) (multiplicity q)) *)
(* Proof:
   By BAG_UNION, FUN_EQ_THM, this is to show:
      multiplicity (p * q) x = multiplicity p x + multiplicity q x
   This is true by poly_root_multiplicity_mult.
*)
val poly_root_multiplicity_mult_bag_union = store_thm(
  "poly_root_multiplicity_mult_bag_union",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| ==>
      (multiplicity (p * q) = BAG_UNION (multiplicity p) (multiplicity q))``,
  rw_tac std_ss[BAG_UNION, FUN_EQ_THM] >>
  rw[poly_root_multiplicity_mult]);

(* Theorem: poly p /\ p <> |0| ==> (SET_OF_BAG (multiplicity p) = roots p) *)
(* Proof:
   By EXTENSION, BAG_IN, BAG_INN, this is to show:
      multiplicity p x >= 1 <=> x IN roots p
   This is true by poly_root_multiplicity_eq_0.
*)
val poly_root_multiplicity_set_of_bag = store_thm(
  "poly_root_multiplicity_set_of_bag",
  ``!r:'a ring. Ring r ==>
   !p. poly p /\ p <> |0| ==> (SET_OF_BAG (multiplicity p) = roots p)``,
  rw_tac std_ss[EXTENSION, IN_SET_OF_BAG, BAG_IN, BAG_INN] >>
  metis_tac[poly_root_multiplicity_eq_0, DECIDE``x >= 1 <=> x <> 0``]);

(* Theorem: Field r ==> !p. poly p /\ p <> |0| ==> FINITE_BAG (multiplicity p) *)
(* Proof:
       FINITE_BAG (multiplicity p)
   <=> FINITE (SET_OF_BAG (multiplicity p))  by FINITE_SET_OF_BAG
   <=> FINITE (roots p)                      by poly_root_multiplicity_set_of_bag
   <=> T                                     by poly_roots_finite, p <> |0|
*)
val poly_root_multiplicity_finite_bag = store_thm(
  "poly_root_multiplicity_finite_bag",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==> FINITE_BAG (multiplicity p)``,
  rpt strip_tac >>
  rewrite_tac[GSYM FINITE_SET_OF_BAG] >>
  `SET_OF_BAG (multiplicity p) = roots p` by rw[poly_root_multiplicity_set_of_bag] >>
  metis_tac[poly_roots_finite]);

(* Theorem: Ring r /\ #1 <> #0 ==> !c. c IN R ==> (multiplicity (factor c) = {| c |}) *)
(* Proof:
   By BAG_INSERT, EMPTY_BAG, FUN_EQ_THM, this is to show:
      multiplicity (factor c) x = if x = c then 1 else 0
   By poly_root_multiplicity_factor, this is to show:
      x <> c ==> multiplicity (factor c) x = 0
   Note poly (factor c)                 by poly_factor_poly
    and factor c <> |0|                 by poly_factor_nonzero
   Also roots (factor c) = {c}          by poly_roots_factor
    But x NOTIN {c}                     by IN_SING, x <> c
    ==> multiplicity (factor c) x = 0   by poly_root_multiplicity_eq_0
*)
val poly_root_multiplicity_factor_sing_bag = store_thm(
  "poly_root_multiplicity_factor_sing_bag",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. c IN R ==> (multiplicity (factor c) = {| c |})``,
  rw_tac std_ss[BAG_INSERT, EMPTY_BAG, FUN_EQ_THM] >>
  rw[poly_root_multiplicity_factor] >>
  `poly (factor c) /\ factor c <> |0|` by rw[poly_factor_poly, poly_factor_nonzero] >>
  `roots (factor c) = {c}` by rw[poly_roots_factor] >>
  `x NOTIN {c}` by rw[] >>
  metis_tac[poly_root_multiplicity_eq_0]);

(* Theorem: c IN R /\ c <> #0 ==> (multiplicity [c] = {||}) *)
(* Proof:
   By EMPTY_BAG, FUN_EQ_THM, this is to show: multiplicity [c] x = 0
   This is true by poly_root_multiplicity_const.
*)
val poly_root_multiplicity_nonzero_const_empty = store_thm(
  "poly_root_multiplicity_nonzero_const_empty",
  ``!r:'a ring. Ring r ==> !c. c IN R /\ c <> #0 ==> (multiplicity [c] = {||})``,
  rw[EMPTY_BAG, FUN_EQ_THM] >>
  rw[poly_root_multiplicity_const]);

(* ------------------------------------------------------------------------- *)
(* Splitting Field of Polynomial                                             *)
(* ------------------------------------------------------------------------- *)

(* Note: multiplicity p x gives a number, so (multiplicity p) is a bag with members x. *)

(* Define bag splitting field *)
val splitting_def = Define`
    splitting (r:'a field) (p:'a poly) <=> (deg p = BAG_CARD (multiplicity p))
`;

(* Theorem: Ring r ==> !c. c IN R /\ c <> #0 ==> splitting r [c] *)
(* Proof:
   Note multiplicity [c] = {||}    by poly_root_multiplicity_nonzero_const_empty
    and BAG_CARD {||} = 0          by BAG_CARD_EMPTY
   also deg [c] = 0                by poly_deg_const
   Thus splitting r [c]            by splitting_def
*)
val splitting_const = store_thm(
  "splitting_const",
  ``!r:'a ring. Ring r ==> !c. c IN R /\ c <> #0 ==> splitting r [c]``,
  rw[splitting_def, poly_root_multiplicity_nonzero_const_empty]);

(* Theorem: Field r ==> !c. c IN R ==>
            !p. poly p /\ p <> |0| /\ splitting r p ==> splitting r (factor c * p) *)
(* Proof:
   By splitting_def, this is to show: deg (factor c * p) = BAG_CARD (multiplicity (factor c * p))
   Note poly (factor c)               by poly_factor_poly
    and factor c <> |0|               by poly_factor_nonzero
    and FINITE_BAG (multiplicity p)   by poly_root_multiplicity_finite_bag
      deg (factor c * p)
    = deg (factor c) + deg p          by poly_deg_mult_nonzero, Field r
    = 1 + deg p                       by poly_factor_deg
      BAG_CARD (multiplicity (factor c * p)
    = BAG_CARD (BAG_UNION (multiplicity (factor c)) (multiplicity p))  by poly_root_multiplicity_mult_bag_union
    = BAG_CARD (BAG_UNION {|c|} (multiplicity p))                      by poly_root_multiplicity_factor_sing_bag
    = BAG_CARD (BAG_INSERT c (multiplicity p))       by BAG_UNION_INSERT
    = BAG_CARD ((multiplicity p)) + 1                by BAG_CARD_THM
    = deg p + 1                                      by splitting_def, splitting r p
*)
val splitting_factor_splitting = store_thm(
  "splitting_factor_splitting",
  ``!r:'a field. Field r ==> !c. c IN R ==>
   !p. poly p /\ p <> |0| /\ splitting r p ==> splitting r (factor c * p)``,
  rw_tac std_ss[splitting_def] >>
  `poly (factor c)` by rw[poly_factor_poly] >>
  `factor c <> |0|` by rw[poly_factor_nonzero] >>
  simp[poly_deg_mult_nonzero, poly_root_multiplicity_mult_bag_union] >>
  `multiplicity (factor c) = {| c |}` by rw[poly_root_multiplicity_factor_sing_bag] >>
  simp[BAG_UNION_INSERT, BAG_CARD_THM, poly_root_multiplicity_finite_bag] >>
  rw[poly_factor_deg]);

(* Theorem: FiniteField r /\ INFINITE univ(:'a) ==> !p. poly p /\ 0 < deg p ==>
            ?(s:'a field) (t:'a field) f. FieldIso f r s /\ s <<= t /\ FINITE C /\ (splitting t (MAP f p)) *)
(* Proof:
   By complete induction on (deg p).
   Let v = deg p.
   Note 0 < v ==> ?n. v = SUC n    by num_CASES
   Also poly p /\ 0 < deg p        by given
    ==> ?s t f b. FieldIso f r s /\ s <<= t /\ FINITE C /\
                  b IN C /\ (poly_root t (MAP f p) b)           by poly_extension_field_exists

               t  <-- where (MAP f p) has a root b IN C
               |
        (r === s) f

   Let fp = MAP f p.
   Note s <= t                    by subfield_is_subring
    and p <> |0|                  by poly_deg_zero, 0 < deg p
    ==> fp <> poly_zero t         by field_iso_eq_poly_zero, poly_zero, MAP, field_one_ne_zero
   Thus Poly t fp                 by field_iso_poly, subring_poly_poly
    ==> ?q. Poly t q /\ (Deg t q = PRE (Deg t fp)) /\
        fp = poly_mult t q (poly_factor t b)    by poly_root_factor_eqn
           = poly_mult t (poly_factor t b) q    by poly_factor_poly, poly_mult_comm

   Let h = poly_factor t b.
   Then fp = poly_mult t h q
    and Deg t h = 1               by poly_factor_deg
    and poly_roots t h = {b}      by poly_factor_roots
    Now Deg t fp = deg p          by field_iso_poly_deg, subring_poly_deg
                 = SUC n          by deg p = v = SUC n
     so Deg t q = PRE (SUC n)     by above
                = n               by PRE
   Also n < v                     by LESS_SUC_REFL, v = SUC n
    and FiniteField t             by FiniteField_def, FINITE C

   If n = 0,
      Then q is a constant polynomial, so fp splits in t.
      Note Deg t q = n = 0        by above
       ==> ?e. e IN C /\ e <> t.sum.id /\ (q = [e])    by poly_deg_eq_0
      Thus splitting t q          by splitting_const
       ==> splitting t fp         by splitting_factor_splitting
      Take this s, t, f, and the result follows.

   If n <> 0, then 0 < n.
      Thus 0 < Deg t q            by Deg t q = n
      Apply induction hypothesis,
       ?s1 t1 f1. FieldIso f1 t s1 /\ s1 <<= t1 /\ FINITE t1.carrier /\
                  splitting t1 (MAP f1 q)         by induction hypothesis

               t1  <-- where (MAP f1 q) splits
               |
        (t === s1) f1

      Let fs = ring_homo_image f1 s s1.
      Then (s === fs) f1                          by field_iso_subfield_iso
       ==> FieldIso (f1 o f) r fs                 by field_iso_compose
      Thus fs <<= s1                              by subfield_field_iso_ring_homo_subfield
       ==> fs <<= t1                              by subfield_trans

      Part 1: examine the image of (fp = poly_mult t q h) in t1
      Let fq = MAP f1 q, fh = MAP f1 h.
      Note s1 <= t1                               by subfield_is_subring
      Thus Poly s1 fq /\ Poly s1 fh               by field_iso_poly, [1]
       and Poly t1 fq /\ Poly t1 fh               by subring_poly_poly, by [1]
      also MAP f1 fp = poly_mult t1 fh fq         by field_iso_poly_mult, subring_poly_mult, [1]
      Note MAP f1 fp <> poly_zero t1              by field_iso_eq_poly_zero, poly_zero, MAP
       ==> fq <> poly_zero t1 /\
           fh <> poly_zero t1                     by poly_mult_eq_zero

      Thus f1 b IN s1.carrier                     by field_iso_element
       and f1 b IN t1.carrier                     by subring_element
       ==> fh = poly_factor t1 (f1 b)             by field_iso_poly_factor, subring_poly_factor
      Thus splitting t1 (MAP f1 fp)               by splitting_factor_splitting

      Note MAP f1 fp = MAP (f1 o f) p             by MAP_COMPOSE, fp = MAP f p
      Take s1, t1, f1 o f, and the result follows.
*)
val poly_splitting_field_exists = store_thm(
  "poly_splitting_field_exists",
  ``!r:'a field. FiniteField r /\ INFINITE univ(:'a) ==> !p. poly p /\ 0 < deg p ==>
   ?(s:'a field) (t:'a field) f. FieldIso f r s /\ s <<= t /\ FINITE C /\ (splitting t (MAP f p))``,
  ntac 2 strip_tac >>
  completeInduct_on `deg p` >>
  rpt strip_tac >>
  `Field r /\ FINITE R` by metis_tac[FiniteField_def] >>
  `?n. v = SUC n` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO] >>
  `?(s:'a field) (t:'a field) f b.
    FieldIso f r s /\ s <<= t /\ FINITE C /\ b IN C /\ (poly_root t (MAP f p) b)` by rw[poly_extension_field_exists] >>
  qabbrev_tac `fp = MAP f p` >>
  `t.sum.id <> t.prod.id` by rw[] >>
  `s <= t` by rw[subfield_is_subring] >>
  `p <> |0|` by metis_tac[poly_deg_zero, NOT_ZERO_LT_ZERO] >>
  `fp <> poly_zero t` by metis_tac[field_iso_eq_poly_zero, poly_zero, MAP] >>
  `Poly t fp` by metis_tac[field_iso_poly, subring_poly_poly] >>
  qabbrev_tac `h = poly_factor t b` >>
  `Poly t h` by rw[poly_factor_poly, Abbr`h`] >>
  `?q. Poly t q /\ (Deg t q = PRE (Deg t fp)) /\ (fp = poly_mult t q h)` by rw[poly_root_factor_eqn, Abbr`fp`, Abbr`h`] >>
  `_ = poly_mult t h q` by rw[poly_mult_comm] >>
  `q <> poly_zero t /\ h <> poly_zero t` by metis_tac[poly_mult_eq_zero] >>
  `Deg t h = 1` by rw[poly_factor_deg, Abbr`h`] >>
  `poly_roots t h = {b}` by rw[poly_factor_roots, Abbr`h`] >>
  `Deg t fp = SUC n` by metis_tac[field_iso_poly_deg, subring_poly_deg] >>
  `(Deg t q = n) /\ (n < v)` by decide_tac >>
  `FiniteField t` by rw[FiniteField_def] >>
  Cases_on `n = 0` >| [
    `?e. e IN C /\ e <> t.sum.id /\ (q = [e])` by metis_tac[poly_deg_eq_0] >>
    `splitting t q` by rw[splitting_const] >>
    `splitting t fp` by rw[splitting_factor_splitting, Abbr`h`] >>
    metis_tac[],
    `0 < Deg t q` by decide_tac >>
    `?(s1:'a field) (t1:'a field) f1.
            FieldIso f1 t s1 /\ s1 <<= t1 /\ FINITE t1.carrier /\
            splitting t1 (MAP f1 q)` by rw[] >>
    qabbrev_tac `fs = ring_homo_image f1 s s1` >>
    `(s === fs) f1` by metis_tac[field_iso_subfield_iso] >>
    `FieldIso (f1 o f) r fs` by prove_tac[field_iso_compose] >>
    `fs <<= s1` by metis_tac[subfield_field_iso_ring_homo_subfield] >>
    `fs <<= t1` by metis_tac[subfield_trans] >>
    qabbrev_tac `fq = MAP f1 q` >>
    qabbrev_tac `fh = MAP f1 h` >>
    `s1 <= t1` by rw[subfield_is_subring] >>
    `Poly s1 fq /\ Poly s1 fh` by metis_tac[field_iso_poly] >>
    `Poly t1 fq /\ Poly t1 fh` by metis_tac[subring_poly_poly] >>
    `MAP f1 fp = poly_mult t1 fh fq` by metis_tac[field_iso_poly_mult, subring_poly_mult] >>
    `MAP f1 fp <> poly_zero t1` by metis_tac[field_iso_eq_poly_zero, poly_zero, MAP] >>
    `fq <> poly_zero t1 /\ fh <> poly_zero t1` by metis_tac[poly_mult_eq_zero] >>
    `f1 b IN s1.carrier /\ f1 b IN t1.carrier` by metis_tac[field_iso_element, subring_element] >>
    `fh = poly_factor t1 (f1 b)` by metis_tac[field_iso_poly_factor, subring_poly_factor] >>
    `splitting t1 (MAP f1 fp)` by rw[splitting_factor_splitting] >>
    `MAP f1 fp = MAP (f1 o f) p` by rw[GSYM MAP_COMPOSE] >>
    metis_tac[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Finite Field Existence by Splitting Field                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r ==> !p. poly p /\ separable p ==> (BAG_CARD (multiplicity p) = CARD (roots p))  *)
(* Proof:
   Let b = multiplicity p.
   By poly_separable_def, p <> |0|, and this is to show: BAG_CARD b = CARD (roots p)

   Claim: !e. BAG_IN e b ==> (b e = 1)
   Proof: By BAG_IN, BAG_INN, this is to show:
             multiplicity p e >= 1 ==> multiplicity p e = 1
          Note multiplicity p e <> 0    by multiplicity p e >= 1
           ==> e IN roots p             by poly_root_multiplicity_eq_0, p <> |0|
           ==> multiplicity p e = 1     by implication

   Note FINITE_BAG b                    by poly_root_multiplicity_finite_bag, p <> |0|
    and !e. BAG_IN e b ==> (b e = 1)    by above
        BAG_CARD b
      = CARD (SET_OF_BAG b)             by BAG_CARD_EQ_CARD_SET_OF_BAG
      = CARD (roots p)                  by poly_root_multiplicity_set_of_bag, p <> |0|
*)
val poly_separable_bag_of_roots = store_thm(
  "poly_separable_bag_of_roots",
  ``!r:'a field. Field r ==>
   !p. poly p /\ separable p ==> (BAG_CARD (multiplicity p) = CARD (roots p))``,
  rw_tac std_ss[poly_separable_def] >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `b = multiplicity p` >>
  `!e. BAG_IN e b ==> (b e = 1)` by
  (rw[BAG_IN, BAG_INN, Abbr`b`] >>
  `multiplicity p e <> 0` by decide_tac >>
  `e IN roots p` by metis_tac[poly_root_multiplicity_eq_0] >>
  rw[]) >>
  `FINITE_BAG b` by rw[poly_root_multiplicity_finite_bag, Abbr`b`] >>
  `BAG_CARD b = CARD (SET_OF_BAG b)` by rw[BAG_CARD_EQ_CARD_SET_OF_BAG] >>
  `_ = CARD (roots p)` by rw[poly_root_multiplicity_set_of_bag, Abbr`b`] >>
  rw[]);

(* Theorem: prime p /\ INFINITE univ(:'a) ==> ?r:'a field. FiniteField r /\ (CARD R = p) *)
(* Proof:
   Note FiniteField (ZN p)           by ZN_finite_field, prime p
    and CARD (ZN p).carrier = p      by ZN_card
    Let f = eqcard_bij (ZN p).carrier (clone (ZN p).carrier),
        r = homo_field (ZN p) f.
   Then FiniteField r /\ FieldIso f (ZN p) r    by finite_field_clone
    and FINITE (ZN p).carrier                   by FiniteField_def
   Thus CARD R = CARD ((ZN p).carrier)          by field_iso_card_eq
               = p                              by above
   Take this FiniteField r, the result follows.
*)
val finite_field_prime_order_exists = store_thm(
  "finite_field_prime_order_exists",
  ``!p. prime p /\ INFINITE univ(:'a) ==> ?r:'a field. FiniteField r /\ (CARD R = p)``,
  rpt strip_tac >>
  `FiniteField (ZN p)` by rw[ZN_finite_field] >>
  `CARD (ZN p).carrier = p` by rw[ZN_card] >>
  qabbrev_tac `f = eqcard_bij (ZN p).carrier (clone (ZN p).carrier)` >>
  qabbrev_tac `r = homo_field (ZN p) f` >>
  `FiniteField r /\ FieldIso f (ZN p) r` by metis_tac[finite_field_clone] >>
  metis_tac[field_iso_card_eq, FiniteField_def]);

(* Theorem: prime p /\ 0 < n /\ INFINITE univ(:'a) ==> ?r:'a field. FiniteField r /\ (CARD R = p ** n) *)
(* Proof:
   By finite_field_prime_order_exists,
      ?r:'a field. FiniteField r /\ (CARD R = p)
   Note char r = p     by finite_field_card_prime
   Let q = p * n, mq = master q.
   Note 1 < p          by ONE_LT_PRIME, prime p
     so 1 < q          by ONE_LT_EXP, 1 < p
    and q <> 0         by 1 < q

   Part 1: get splitting field of mq
   Note poly mq          by poly_master_poly
    and deg mq = q       by poly_master_deg, 1 < q
    ==> ?(s:'a field) (t:'a field) f. FieldIso f r s /\ s <<= t /\
        FINITE C /\ (splitting t (MAP f mq))    by poly_splitting_field_exists
   Thus FiniteField t    by FiniteField_def
    and char t = char s  by subfield_char
               = char r  by field_iso_char_eq
               = p       by above

   Part 2: get subfield of splitting field t
   Let fq = Master t q, sm = subset_field t (poly_roots t fq).
   Then sm <<= t         by poly_master_roots_subfield, char t = p
    and FiniteField sm   by subfield_finite_field

   Part 3: show that fq is separable
   Note s <= t                   by subfield_is_subring
    and t.prod.id <> t.sum.id    by field_one_ne_zero
    and MAP f mq = fq            by field_iso_poly_master, subring_poly_master
   Note poly_separable t fq      by poly_separable_master_char_exp
    and Poly t fq                by poly_master_poly

   Part 4: deduce cardinality of FiniteField sm
        CARD (sm.carrier)
      = CARD (poly_roots t fq)                   by subset_field_def
      = BAG_CARD (poly_root_multiplicity t fq)   by poly_separable_bag_of_roots, poly_separable t fq
      = Deg t fq                                 by splitting_def], splitting t fq
      = Deg s fq                 by subring_poly_deg
      = Deg s (MAP f mq)         by above
      = deg mq                   by field_iso_poly_deg
      = q                        by above

   Take FiniteField sm,
   with CARD (sm.carrier) = q
*)
val finite_field_prime_power_order_exists = store_thm(
  "finite_field_prime_power_order_exists",
  ``!p n. prime p /\ 0 < n /\ INFINITE univ(:'a) ==> ?r:'a field. FiniteField r /\ (CARD R = p ** n)``,
  rpt strip_tac >>
  `?r:'a field. FiniteField r /\ (CARD R = p)` by rw[finite_field_prime_order_exists] >>
  `char r = p` by rw[finite_field_card_prime] >>
  qabbrev_tac `q = p ** n` >>
  qabbrev_tac `mq = master q` >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `1 < q` by rw[ONE_LT_EXP, Abbr`q`] >>
  `q <> 0` by decide_tac >>
  `Field r /\ FINITE R` by metis_tac[FiniteField_def] >>
  `poly mq` by rw[poly_master_poly, Abbr`mq`] >>
  `deg mq = q` by rw[poly_master_deg, Abbr`mq`] >>
  `?(s:'a field) (t:'a field) f. FieldIso f r s /\ s <<= t /\
      FINITE C /\ (splitting t (MAP f mq))` by rw[poly_splitting_field_exists] >>
  `FiniteField t` by metis_tac[FiniteField_def] >>
  `char t = char r` by metis_tac[field_iso_char_eq, subfield_char] >>
  qabbrev_tac `fq = Master t q` >>
  qabbrev_tac `sm = subset_field t (poly_roots t fq)` >>
  `sm <<= t` by metis_tac[poly_master_roots_subfield] >>
  `FiniteField sm` by metis_tac[subfield_finite_field] >>
  `s <= t` by rw[subfield_is_subring] >>
  `t.prod.id <> t.sum.id` by rw[] >>
  `MAP f mq = fq` by metis_tac[field_iso_poly_master, subring_poly_master] >>
  `poly_separable t fq` by metis_tac[poly_separable_master_char_exp] >>
  `Poly t fq` by rw[poly_master_poly, Abbr`fq`] >>
  `CARD (sm.carrier) = CARD (poly_roots t fq)` by rw[subset_field_def, Abbr`sm`] >>
  `_ = BAG_CARD (poly_root_multiplicity t fq)` by rw[GSYM poly_separable_bag_of_roots] >>
  `_ = Deg t fq` by rw[GSYM splitting_def] >>
  `_ = deg (master q)` by metis_tac[field_iso_poly_deg, subring_poly_deg] >>
  metis_tac[]);

(* These are major milestones. *)

(* Theorem: FiniteField r ==> splitting r (master (CARD R)) *)
(* Proof:
   By splitting_def, this is to show:
      deg (master (CARD R)) = BAG_CARD (multiplicity (master (CARD R)))

   Let p = char r, d = fdim r.
   Then prime p                       by finite_field_char
    ==> 1 < p                         by ONE_LT_PRIME
   Note (CARD R = p ** d) /\ 0 < d    by finite_field_card_eqn
   Thus 1 < CARD R                    by ONE_LT_EXP
    and separable (master (CARD R))   by poly_separable_master_char_exp, 1 < p
   Hence,
        deg (master (CARD R))
      = CARD R                                     by poly_master_deg, 1 < CARD R
      = CARD (roots (master (CARD R)))             by poly_master_roots_all
      = BAG_CARD (multiplicity (master (CARD R)))  by poly_separable_bag_of_roots
*)
val finite_field_is_master_splitting_field = store_thm(
  "finite_field_is_master_splitting_field",
  ``!r:'a field. FiniteField r ==> splitting r (master (CARD R))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  rw_tac std_ss[splitting_def] >>
  qabbrev_tac `p = char r` >>
  qabbrev_tac `d = fdim r` >>
  `prime p` by rw[finite_field_char, Abbr`p`] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `(CARD R = p ** d) /\ 0 < d` by rw[finite_field_card_eqn, Abbr`p`, Abbr`d`] >>
  `1 < CARD R` by rw[ONE_LT_EXP] >>
  `separable (master (CARD R))` by metis_tac[poly_separable_master_char_exp] >>
  `deg (master (CARD R)) = CARD R` by rw[poly_master_deg] >>
  `_ = CARD (roots (master (CARD R)))` by rw[poly_master_roots_all] >>
  `_ = BAG_CARD (multiplicity (master (CARD R)))` by rw[poly_separable_bag_of_roots] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Splitting Field of Polynomial (almost)                                    *)
(* ------------------------------------------------------------------------- *)

(* Define another polynomial splitting field, counting root multiplicity. *)
val splits_in_def = Define`
    splits_in (p:'a poly) (r:'a field) <=>
    ?c. c IN R /\ c <> #0 /\ (p = c * PPIMAGE (\x. (factor x) ** (multiplicity p x)) (roots p))
`;
(* Note: c is just a nonzero constant, no requirement for invertible, i.e. upoly [c] is not required. *)

(* put splits_in as infix *)
val _ = set_fixity "splits_in" (Infix(NONASSOC, 450)); (* same as relation *)

(*
> splits_in_def;
val it = |- !p r. p splits_in r <=>
     ?c. c IN R /\ c <> #0 /\ (p = c * PPIMAGE (\x. factor x ** multiplicity p x) (roots p)): thm
*)

(*
(* SUM_SET (IMAGE (multiplicity p) (roots p)) = {multiplicity p x | x | root p x} *)
-- this is wrong: If all roots have multiplicity p x = 1, this gives SUM_SET {1} = 1 always.
SUM (MAP (multiplicity p) (set_to_list (roots p)))
or define by:
p ~~ PROD_SET (IMAGE (\x. (factor x) ** (multiplicity p x)) (roots p))
where c IN R, a constant, or using poly_unit_eq.
q ~~ PROD_SET (IMAGE (\x. (factor x) ** (multiplicity q x)) (roots q))

p * q ~~ PROD_SET (IMAGE (\x. (factor x) ** (multiplicity p x)) (roots p)) *
         PROD_SET (IMAGE (\x. (factor x) ** (multiplicity q x)) (roots q))

There is PROD_SET_PRODUCT_BY_PARTITION
poly_unit_eq_mult is common multiple only!
*)

(* Theorem: Ring r ==> !c. c IN R /\ c <> #0 ==> [c] splits_in r *)
(* Proof:
   Let f = \x. (factor x) ** (multiplicity p x).
   Note roots [c] = {}                   by poly_roots_const, c <> #0
        [c] = c * |1|                    by poly_cmult_one
            = c * PPIMAGE f {}           by poly_prod_image_empty
            = c * PPIMAGE f (roots [c])  by above
   Thus [c] splits_in r
*)
val splits_in_const = store_thm(
  "splits_in_const",
  ``!r:'a ring. Ring r ==> !c. c IN R /\ c <> #0 ==> [c] splits_in r``,
  rpt strip_tac >>
  `roots [c] = {}` by rw[poly_roots_const] >>
  `[c] = c * |1|` by rw[poly_cmult_one] >>
  metis_tac[splits_in_def, poly_prod_image_empty]);

(* Theorem: Ring r /\ #1 <> #0 ==> !c. c IN R ==> (factor c) splits_in r *)
(* Proof:
   Note poly (factor c)                     by poly_factor_poly
    and roots (factor c) = {c}              by poly_factor_roots
    and multiplicity (factor c) c = 1       by poly_root_multiplicity_factor

   Let f = \x. (factor x) ** (multiplicity (factor c) x).
   Then f c = (factor c) ** 1               by above
            = factor c                      by poly_exp_1

   Thus factor c
      = f c                                 by above
      = PPIMAGE f {c}                       by poly_prod_image_sing
      = PPIMAGE f (roots (factor c))        by above
      = #1 * PPIMAGE f (roots (factor c))   by poly_cmult_lone
   Thus (factor c) splits_in r              by ring_one_element
*)
val splits_in_factor = store_thm(
  "splits_in_factor",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. c IN R ==> (factor c) splits_in r``,
  rpt strip_tac >>
  `poly (factor c)` by rw[poly_factor_poly] >>
  `roots (factor c) = {c}` by rw[poly_factor_roots] >>
  `multiplicity (factor c) c = 1` by rw[poly_root_multiplicity_factor] >>
  qabbrev_tac `f = \x. (factor x) ** (multiplicity (factor c) x)` >>
  `f c = factor c` by rw[poly_exp_1, Abbr`f`] >>
  rw[splits_in_def, poly_prod_set_sing] >>
  `#1 IN R /\ (factor c = #1 * factor c)` by rw[] >>
  metis_tac[]);

(* Theorem: Field r ==> !b c. b IN R /\ b <> #0 /\ c IN R ==> (b * factor c) splits_in r *)
(* Proof:
   Let p = b * factor c.
   Note poly (factor c)                 by poly_factor_poly
    and factor c <> |0|                 by poly_factor_nonzero
    and poly p                          by poly_cmult_poly
   Note roots p = roots (factor c)      by poly_roots_cmult
    and roots (factor c) = {c}          by poly_roots_factor
   Also multiplicity (factor c) c = 1   by poly_root_multiplicity_factor
    and multiplicity p c
      = multiplicity (factor c) c = 1   by poly_root_multiplicity_cmult
   Let term p = \c. factor c ** multiplicity p c.
        IMAGE (term p) (roots p)
      = IMAGE (term p) roots (factor c)     by above
      = IMAGE (term p) {c}                  by above
      = term p c                            by IMAGE_SING
      = factor c ** multiplicity p c        by notation
      = factor c ** multiplicity (factor c) c   by above
      = term (factor c) c                   by notation
      = IMAGE (term (factor c)) {c}         by IMAGE_SING
      = IMAGE (term (factor c)) (roots (factor c))   by above

   Note (factor c) splits_in r          by splits_in_factor
    ==> ?e. e IN R /\ e <> #0 /\ (factor c = e * q)   by splits_in_def
    where q = PPIMAGE (\x. term (factor c) x) (roots (factor c)).
   Note poly q                          by poly_prod_term_roots_poly
        p = b * (e * q)                 by above
          = (b * e) * q                 by poly_cmult_cmult
    Now b * e IN R                      by field_op_element
    and b * e <> #0                     by field_mult_eq_zero, Field r
    Thus splits_in r                    by splits_in_def
*)
val splits_in_factor_cmult = store_thm(
  "splits_in_factor_cmult",
  ``!r:'a field. Field r ==> !b c. b IN R /\ b <> #0 /\ c IN R ==> (b * factor c) splits_in r``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `p = b * factor c` >>
  `poly (factor c)` by rw[poly_factor_poly] >>
  `poly p` by rw[Abbr`p`] >>
  `roots p = roots (factor c)` by rw[poly_roots_cmult, Abbr`p`] >>
  `roots (factor c) = {c}` by rw[poly_roots_factor] >>
  `multiplicity (factor c) c = 1` by rw[poly_root_multiplicity_factor] >>
  `multiplicity p c = 1` by rw[poly_root_multiplicity_cmult, Abbr`p`] >>
  `IMAGE (\x. (factor x) ** (multiplicity p x)) (roots (factor c)) =
    IMAGE (\x.  (factor x) ** (multiplicity (factor c) x)) (roots (factor c))` by rw[poly_roots_def, EXTENSION] >>
  qabbrev_tac `q = PPIMAGE (\x. factor x ** multiplicity (factor c) x) (roots (factor c))` >>
  `(factor c) splits_in r` by rw[splits_in_factor] >>
  `?e. e IN R /\ e <> #0 /\ (factor c = e * q)` by metis_tac[splits_in_def] >>
  `poly q` by rw[poly_prod_term_roots_poly, poly_factor_nonzero, Abbr`q`] >>
  `p = b * (e * q)` by rw[Abbr`p`] >>
  `_ = (b * e) * q` by rw[GSYM poly_cmult_cmult] >>
  `b * e IN R` by rw[] >>
  `b * e <> #0` by metis_tac[field_mult_eq_zero] >>
  metis_tac[splits_in_def]);

(* Theorem: Field r ==> !b c. b IN R /\ b <> #0 /\ c IN R ==> (factor c) * [b] splits_in r *)
(* Proof:
   Note poly [b]                        by poly_nonzero_element_poly, b <> #0
    and poly (factor c)                 by poly_factor_poly
        (factor c) * [b]
      = [b] * factor c                  by poly_mult_comm
      = b * factor c                    by poly_mult_lconst
   Thus (factor c) * [b] splits_in r    by splits_in_factor_cmult
*)
val splits_in_factor_const = store_thm(
  "splits_in_factor_const",
  ``!r:'a field. Field r ==> !b c. b IN R /\ b <> #0 /\ c IN R ==> (factor c) * [b] splits_in r``,
  rpt strip_tac >>
  `poly [b]` by rw[poly_nonzero_element_poly] >>
  `poly (factor c)` by rw[poly_factor_poly] >>
  `(factor c) * [b] = [b] * factor c` by rw[poly_mult_comm] >>
  `_ = b * factor c` by rw[poly_mult_lconst] >>
  rw[splits_in_factor_cmult]);

(* Theorem: Field r ==> !b c. b IN R /\ b <> #0 /\ c IN R ==> !n. b * (factor c ** n) splits_in r *)
(* Proof:
   If n = 0,
      Note b * factor c ** 0
         = b * |1|                by poly_exp_0
         = [b]                    by poly_cmult_one
       and [b] splits_in r        by splits_in_const

   If n <> 0, then 0 < n.
      Let p = b * (factor c) ** n.
      Note poly (factor c)        by poly_factor_poly
       and poly (factor c ** n)   by poly_exp_poly
       and poly p                 by poly_cmult_poly
           roots p
         = roots (factor c ** n)  by poly_roots_cmult
         = roots (factor c)       by poly_roots_exp, 0 < n
         = {c}                    by poly_roots_factor
      Note factor c <> |0|        by poly_factor_nonzero
       ==> factor c ** n <> |0|   by poly_exp_eq_zero, Field r
      Also multiplicity p c
         = multiplicity (factor c ** n) c   by poly_root_multiplicity_cmult
         = n * multiplicity (factor c) c    by poly_root_multiplicity_exp
         = n * 1 = n                        by poly_root_multiplicity_factor

      Let term p = \c. factor c ** multiplicity p c.
       p = b * term p c                     by notation
         = b * PPIMAGE (term p) {c}         by poly_prod_set_sing
         = b * PPIMAGE (term p) (roots p)   by above
      Hence p splits_in r                   by splits_in_def
*)
val splits_in_factor_exp = store_thm(
  "splits_in_factor_exp",
  ``!r:'a field. Field r ==> !b c. b IN R /\ b <> #0 /\ c IN R ==> !n. b * (factor c ** n) splits_in r``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  Cases_on `n = 0` >-
  rw[splits_in_const] >>
  `0 < n` by decide_tac >>
  qabbrev_tac `p = b * (factor c) ** n` >>
  `poly (factor c) /\ poly (factor c ** n) /\ poly p` by rw[poly_factor_poly, Abbr`p`] >>
  `roots p = roots (factor c ** n)` by rw[poly_roots_cmult, Abbr`p`] >>
  `_ = roots (factor c)` by rw[poly_roots_exp] >>
  `_ = {c}` by rw[poly_roots_factor] >>
  `factor c <> |0|` by rw[poly_factor_nonzero] >>
  `factor c ** n <> |0|` by metis_tac[poly_exp_eq_zero] >>
  `multiplicity p c = multiplicity (factor c ** n) c` by rw[poly_root_multiplicity_cmult, Abbr`p`] >>
  `_ = n * multiplicity (factor c) c` by rw[poly_root_multiplicity_exp] >>
  `_ = n` by rw[poly_root_multiplicity_factor] >>
  `p = b * (\x. factor x ** multiplicity p x) c` by rw[Abbr`p`] >>
  `_ = b * PPIMAGE (\x. factor x ** multiplicity p x) {c}` by rw[poly_prod_set_sing] >>
  `_ = b * PPIMAGE (\x. factor x ** multiplicity p x) (roots p)` by rw[] >>
  metis_tac[splits_in_def]);

(* ------------------------------------------------------------------------- *)
(* Splitting Field of Polynomial (old).                                      *)
(* ------------------------------------------------------------------------- *)

(* A polynomial splits in a field when its root count equals its degree. *)
val poly_splits_def = Define`
  poly_splits (r:'a field) (p:'a poly) <=> (CARD (roots p) = deg p)
`;
(* overload on poly_splits r *)
val _ = overload_on("splits", ``poly_splits r``);
(*
> poly_splits_def;
val it = |- !r p. splits p <=> (CARD (roots p) = deg p): thm
*)

(* Note: In the literature, this seems to be called a separable polynomial. *)

(* Theorem: FiniteField r ==> !p. splits p ==> p <> |0| *)
(* Proof:
   Note roots |0| = R      by poly_roots_zero
    and deg |0| = 0        by poly_deg_zero
   By contradiction, assume CARD (roots |0|) = 0.
   Then roots |0| = {}     by CARD_EQ_0, FINITE R.
   But #0 IN R             by field_zero_element
    so R <> {}             by MEMBER_NOT_EMPTY
   which contradicts R = {}.
*)
val poly_splits_nonzero = store_thm(
  "poly_splits_nonzero",
  ``!r:'a field. FiniteField r ==> !p. splits p ==> p <> |0|``,
  rw_tac std_ss[poly_splits_def, poly_roots_zero, poly_deg_zero, FiniteField_def] >>
  metis_tac[field_zero_element, MEMBER_NOT_EMPTY, CARD_EQ_0]);

(* Theorem: FiniteRing r ==> ~(splits |0|) *)
(* Proof:
   Note roots |0| = R                 by poly_roots_zero
    and deg |0| = 0                   by poly_deg_zero
    but 0 < CARD R                    by finite_ring_card_pos, FiniteRing r
   Thus CARD (roots |0|) <> deg |0|   by above
     or ~(splits |0|)                 by poly_splits_def
*)
val poly_zero_splits_not = store_thm(
  "poly_zero_splits_not",
  ``!r:'a ring. FiniteRing r ==> ~(splits |0|)``,
  rpt (stripDup[FiniteRing_def]) >>
  `roots |0| = R` by rw[poly_roots_zero] >>
  `deg |0| = 0` by rw[] >>
  `0 < CARD R` by rw[finite_ring_card_pos] >>
  metis_tac[poly_splits_def, NOT_ZERO_LT_ZERO]);

(* Theorem: Ring r /\ #1 <> #0 ==> splits X *)
(* Proof:
        CARD (roots X)
      = CARD {#0}                by poly_roots_X
      = 1                        by CARD_SING
      = deg X                    by poly_deg_X, #1 <> #0
     or splits X                 by poly_splits_def
*)
val poly_X_splits = store_thm(
  "poly_X_splits",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> splits X``,
  rpt strip_tac >>
  `roots X = {#0}` by rw[poly_roots_X] >>
  `deg X = 1` by rw[] >>
  rw[poly_splits_def]);

(* Theorem: Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| /\
            DISJOINT (roots p) (roots q) /\ splits p /\ splits q ==> splits (p * q) *)
(* Proof:
   Note FINITE (roots p)                 by poly_roots_finite, p <> |0|
    and FINITE (roots q)                 by poly_roots_finite, q <> |0|
     CARD (roots (p * q))
   = CARD ((roots p) UNION (roots q))    by poly_roots_mult
   = CARD (roots p) + CARD (roots q)     by CARD_UNION_DISJOINT
   = deg p + deg q                       by poly_splits_def
   = deg (p * q)                         by poly_deg_mult_nonzero, p <> |0|, q <> |0|
*)
val poly_splits_mult = store_thm(
  "poly_splits_mult",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| /\
                DISJOINT (roots p) (roots q) /\ splits p /\ splits q ==> splits (p * q)``,
  rw[poly_splits_def, poly_roots_finite, poly_roots_mult, CARD_UNION_DISJOINT, poly_deg_mult_nonzero]);

(* Theorem: Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| /\
            DISJOINT (roots p) (roots q) /\ splits p /\ splits (p * q) ==> splits q *)
(* Proof:
   Note FINITE (roots p)                 by poly_roots_finite, p <> |0|
    and FINITE (roots q)                 by poly_roots_finite, q <> |0|
     deg p + deq q
   = deg (p * q)                         by poly_deg_mult_nonzero, p <> |0|, q <> |0|
   = CARD (roots (p * q))                by poly_splits_def
   = CARD ((roots p) UNION (roots q))    by poly_roots_mult
   = CARD (roots p) + CARD (roots q)     by CARD_UNION_DISJOINT
   = deg p + CARD (roots q)              by poly_splits_def
   Hence CARD (roots q) = deq q          by arithmetic
      or splits q                        by poly_splits_def
*)
val poly_splits_mult_each = store_thm(
  "poly_splits_mult_each",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| /\
                DISJOINT (roots p) (roots q) /\ splits p /\ splits (p * q) ==> splits q``,
  rw_tac std_ss[poly_splits_def] >>
  `FINITE (roots p) /\ FINITE (roots q)` by rw[poly_roots_finite] >>
  `deg (p * q) = deg p + deg q` by rw[poly_deg_mult_nonzero] >>
  `CARD (roots (p * q)) = CARD ((roots p) UNION (roots q))` by rw[GSYM poly_roots_mult] >>
  `_ = CARD (roots p) + CARD (roots q)` by rw[CARD_UNION_DISJOINT] >>
  `_ = deg p + CARD (roots q)` by rw[poly_splits_def] >>
  decide_tac);

(* Theorem: Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| /\
            DISJOINT (roots p) (roots q) /\ splits p ==> (splits (p * q) <=> splits q) *)
(* Proof: by poly_splits_mult, poly_splits_mult_each *)
val poly_splits_mult_iff = store_thm(
  "poly_splits_mult_iff",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| /\
                DISJOINT (roots p) (roots q) /\ splits p ==> (splits (p * q) <=> splits q)``,
  metis_tac[poly_splits_mult, poly_splits_mult_each]);

(* ------------------------------------------------------------------------- *)
(* Splitting Field of Unity Polynomial.                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==> !n. 0 < n ==> (splits (unity n) <=> n divides (CARD R+)) *)
(* Proof:
       Note F* = R+                         by field_mult_carrier
      Since FiniteGroup f*                  by finite_field_mult_finite_group
         so Group f* /\ FINITE R+           by FiniteGroup_def
        and CARD R+ = (CARD R) - 1          by finite_field_nonzero_carrier_card

  If part: splits (unity n) ==> n divides CARD R+
       Note AbelianGroup f*                 by field_nonzero_mult_is_abelian_group
         so Group (roots_of_unity f* n)     by group_uroots_group, AbelianGroup f*
       Thus roots_of_unity f* n <= f*       by group_uroots_subgroup
        Now compute the cardinality of carriers to apply Lagrange_thm:
              CARD (roots_of_unity f* n).carrier
            = CARD (roots (unity n))        by field_uroots_are_roots, 0 < n
            = deg (unity n)                 by poly_splits_def
            = n                             by poly_unity_deg
        With roots_of_unity f* n <= f* and FINITE R+, by above,
       Hence n divides (CARD R+)            by Lagrange_thm

  Only-if part: n divides CARD R+ ==> splits (unity n)
     Let w = CARD R+
     Since ?y. y IN R+ /\ (order f* y = w)  by finite_field_mult_group_has_gen
     Given k divides (CARD R+),
           ?h. w = h * n                    by divides_def
        or h divides w                      by divides_def, MULT_COMM
      thus gcd w h = h                      by divides_iff_gcd_fix, GCD_SYM
       Now w <> 0                           by group_carrier_nonempty, CARD_EQ_0, FINITE F*
        so h <> 0                           by MULT
       Let z = f*.exp y h
      Thus (order f* z) * h = w             by group_order_power
        or order f* z = n                   by MULT_LEFT_CANCEL, MULT_COMM, h <> 0
     Since z IN F*                          by group_exp_element
        so Generated f* z <= f*             by generated_subgroup, z IN F*
       and CARD (Generated f* z).carrier = n   by generated_group_card, z IN F*
      also z IN R /\ z <> #0                by field_nonzero_eq, field_mult_carrier
     Therefore,
           CARD (roots (unity n))
         = CARD (Generated f* z).carrier    by poly_unity_roots_generator
         = n                                by above
         = deg (unity n)                    by poly_unity_deg
     Hence splits (unity n)                 by poly_splits_def
*)
val poly_unity_splitting_condition = store_thm(
  "poly_unity_splitting_condition",
  ``!r:'a field. FiniteField r ==> !n. 0 < n ==> (splits (unity n) <=> n divides (CARD R+))``,
  rpt (stripDup[FiniteField_def]) >>
  `F* = R+` by rw[field_mult_carrier] >>
  `FiniteGroup f*` by rw[finite_field_mult_finite_group] >>
  `Group f* /\ FINITE R+` by metis_tac[FiniteGroup_def] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    `AbelianGroup f*` by rw[field_nonzero_mult_is_abelian_group] >>
    `Group (roots_of_unity f* n)` by rw[group_uroots_group] >>
    `roots_of_unity f* n <= f*` by rw[group_uroots_subgroup] >>
    `(roots_of_unity f* n).carrier = roots (unity n)` by rw[field_uroots_are_roots] >>
    `Ring r /\ #1 <> #0` by rw[] >>
    `CARD (roots_of_unity f* n).carrier = n` by metis_tac[poly_splits_def, poly_unity_deg] >>
    metis_tac[Lagrange_thm],
    qabbrev_tac `w = CARD R+` >>
    `?y. y IN R+ /\ (order f* y = w)` by rw[finite_field_mult_group_has_gen, Abbr`w`] >>
    `?h. w = h * n` by rw[GSYM divides_def] >>
    `h divides w` by metis_tac[divides_def, MULT_COMM] >>
    `gcd w h = h` by metis_tac[divides_iff_gcd_fix, GCD_SYM] >>
    `w <> 0` by metis_tac[group_carrier_nonempty, CARD_EQ_0] >>
    `h <> 0` by metis_tac[MULT] >>
    qabbrev_tac `z = f*.exp y h` >>
    `(order f* z) * h = w` by metis_tac[group_order_power] >>
    `order f* z = n` by metis_tac[MULT_LEFT_CANCEL, MULT_COMM] >>
    `z IN R+` by metis_tac[group_exp_element] >>
    `z IN R /\ z <> #0` by metis_tac[field_nonzero_eq] >>
    `CARD (roots (unity n)) = CARD (Generated f* z).carrier` by rw[poly_unity_roots_generator] >>
    `_ = n` by rw[generated_group_card, Abbr`z`] >>
    `_ = deg (unity n)` by rw[] >>
    rw[poly_splits_def]
  ]);

(* This is a major theorem *)

(* ------------------------------------------------------------------------- *)
(* Splitting Condition of Master Polynomial                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==> !n. 0 < n ==> (splits (master n) <=> (n - 1) divides (CARD R+)) *)
(* Proof:
   If n = 1,
      Then n - 1 = 0.
      Note 0 < CARD R+                      by field_nonzero_card_pos
      Thus (n - 1) divdes CARD R+ = F       by ZERO_DIVIDES
      Note master 1 = |0|                   by poly_master_1
       and ~splits |0|                      by poly_zero_splits_not, FiniteRing r
        so splits (master 1) = F            by above
      Thus true.
   If n <> 1,
      Then 1 < n /\ 0 < n - 1               by 0 < n /\ n <> 1
       and master n = X * (unity (n - 1))   by poly_master_factors, 0 < n
      Note poly X                           by poly_X
       and poly (unity (n - 1))             by poly_unity_poly
       and X <> |0|                         by poly_X_nonzero
       and unity (n - 1) <> |0|             by poly_unity_eq_zero, n <> 0
      Also DISJOINT (roots X) (roots (unity (n - 1)))
                                            by poly_roots_X, DISJOINT_DEF, SING_INTER, poly_roots_member
       Now splits X                         by poly_X_splits
       and splits (roots (unity (n - 1))) = (n - 1) divides (CARD R+)  by poly_unity_splitting_condition
      Thus splits (master n) <=> (n - 1) divides (CARD R+)             by poly_splits_mult_iff
*)
val poly_master_splitting_condition = store_thm(
  "poly_master_splitting_condition",
  ``!r:'a field. FiniteField r ==> !n. 0 < n ==> (splits (master n) <=> (n - 1) divides (CARD R+))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  Cases_on `n = 1` >| [
    `master 1 = |0|` by rw[poly_master_1] >>
    `n - 1 = 0` by decide_tac >>
    `CARD R+ <> 0` by metis_tac[field_nonzero_card_pos, NOT_ZERO_LT_ZERO] >>
    metis_tac[poly_zero_splits_not, ZERO_DIVIDES, FiniteRing_def],
    `1 < n /\ 0 < n - 1` by decide_tac >>
    `master n = X * (unity (n - 1))` by rw_tac std_ss[poly_master_factors] >>
    `poly X /\ poly (unity (n - 1))` by rw[] >>
    `X <> |0| /\ unity (n - 1) <> |0|` by rw[poly_unity_eq_zero] >>
    `DISJOINT (roots X) (roots (unity (n - 1)))` by
  (rw_tac std_ss[poly_roots_X] >>
    `~(root (unity (n - 1)) #0)` by rw[poly_unity_root_nonzero] >>
    rw_tac std_ss[DISJOINT_DEF, EXTENSION, GSPECIFICATION] >>
    metis_tac[SING_INTER, poly_roots_member]) >>
    `splits X` by rw[poly_X_splits] >>
    metis_tac[poly_splits_mult_iff, poly_unity_splitting_condition]
  ]);

(* Another major theorem *)

(* Theorem: FiniteField r ==> !n. splits (master ((char r) ** n)) <=> n divides (fdim r) *)
(* Proof:
   Let c = char r, m = c ** n.
   If n = 0,
      Then m = 1                    by EXP_0
        so master 1 = |0|           by poly_master_1
       and ~(splits |0|)            by poly_zero_splits_not
       ==> splits (master 1) = F    by above
      Also 0 < fdim r               by finite_field_dim_pos
        so 0 divides (fdim r) = F   by ZERO_DIVIDES
      Hence true.
   If n <> 0,
      Note prime c                  by finite_field_char
        so 1 < c                    by ONE_LT_PRIME
       and 1 < m                    by ONE_LT_EXP, 1 < c

          splits (master m)
      <=> (m - 1) divides (CARD R+)                  by poly_master_splitting_condition, 0 < m
      <=> (m - 1) divides (CARD R - 1)               by finite_field_nonzero_carrier_card
      <=> (c ** n - 1) divides (c ** (fdim r) - 1)   by finite_field_card_eqn
      <=> n divides (fdim r)                         by power_predecessor_divisibility, 1 < c
*)
val poly_master_char_n_splitting = store_thm(
  "poly_master_char_n_splitting",
  ``!r:'a field. FiniteField r ==> !n. splits (master ((char r) ** n)) <=> n divides (fdim r)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `c = char r` >>
  qabbrev_tac `m = c ** n` >>
  Cases_on `n = 0` >| [
    `m = 1` by rw[Abbr`m`] >>
    `Ring r` by rw[] >>
    `FiniteRing r` by metis_tac[FiniteRing_def] >>
    `0 < fdim r` by metis_tac[finite_field_dim_pos] >>
    metis_tac[poly_master_1, poly_zero_splits_not, ZERO_DIVIDES, NOT_ZERO_LT_ZERO],
    `1 < c` by rw[finite_field_char, ONE_LT_PRIME, Abbr`c`] >>
    `1 < m` by rw[ONE_LT_EXP, Abbr`m`] >>
    `splits (master m) <=> (m - 1) divides (CARD R+)` by rw[poly_master_splitting_condition] >>
    `_ = (m - 1) divides (CARD R - 1)` by rw[finite_field_nonzero_carrier_card] >>
    `_ = (c ** n - 1) divides (c ** (fdim r) - 1)` by rw[finite_field_card_eqn, Abbr`m`, Abbr`c`] >>
    `_ = n divides (fdim r)` by rw[power_predecessor_divisibility] >>
    rw[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Another proof of subfield existence                                       *)
(* ------------------------------------------------------------------------- *)

(* This proof depends on the splitting condition of the master polynomial. *)

(* Theorem: FiniteField r ==> !n. n divides fdim r ==>
            (fdim (subset_field r (roots (master ((char r) ** n)))) = n) *)
(* Proof:
   Note 0 < fdim r               by finite_field_dim_pos
     so 0 < n                    by ZERO_DIVIIDES
   Let c = char r, m = c ** n, p = master m
   Note 1 < c                    by finite_field_char, ONE_LT_PRIME
     so 1 < m                    by ONE_LT_EXP, 0 < n
   Note n divides fdim r         by given
    ==> splits p                 by poly_master_char_n_splitting
     so CARD (roots p) = deg p   by poly_splits_def
                       = m       by poly_master_deg, 1 < m
   Note subset_field r (roots p) <<= r     by poly_master_roots_subfield
    and (subset_field r (roots p)).carrier = roots p       by subset_field_property
     so CARD (subset_field r (roots p)).carrier = c ** n   by above
   Note FiniteField (subset_field r (roots p))             by subfield_finite_field
    and char (subset_field r (roots p)) = c                by subfield_char
    ==> fdim (subset_field r (roots p)) = n                by finite_field_dim_eq
*)
val poly_master_roots_subfield_dim = store_thm(
  "poly_master_roots_subfield_dim",
  ``!r:'a field. FiniteField r ==> !n. n divides fdim r ==>
                (fdim (subset_field r (roots (master ((char r) ** n)))) = n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `c = char r` >>
  qabbrev_tac `m = c ** n` >>
  `0 < n` by metis_tac[finite_field_dim_pos, ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `1 < m` by rw[finite_field_char, ONE_LT_PRIME, ONE_LT_EXP, Abbr`m`, Abbr`c`] >>
  qabbrev_tac `p = master m` >>
  `deg p = m` by rw[poly_master_deg, Abbr`p`] >>
  `CARD (roots p) = m` by metis_tac[poly_master_char_n_splitting, poly_splits_def] >>
  `subset_field r (roots p) <<= r` by rw[poly_master_roots_subfield, Abbr`p`, Abbr`m`, Abbr`c`] >>
  metis_tac[finite_field_dim_eq, subfield_finite_field, subfield_char, subset_field_property]);

(* Theorem: FiniteField r ==> !n. n divides fdim r <=> ?s. s <<= r /\ (fdim s = n) *)
(* Proof:
   If part: n divides fdim r ==> ?s. (Field s /\ subfield s r) /\ (fdim s = n)
      Take s = subset_field r (roots (master ((char r) ** n)))
      Then s <<= r                  by poly_master_roots_subfield
       and fdim s = n               by poly_master_roots_subfield_dim
   Only-if part: subfield s r ==> fdim s divides fdim r
      True                          by finite_field_subfield_dim_divides
*)
val finite_field_subfield_exists_iff = store_thm(
  "finite_field_subfield_exists_iff",
  ``!r:'a field. FiniteField r ==> !n. n divides fdim r <=> ?s. s <<= r /\ (fdim s = n)``,
  metis_tac[poly_master_roots_subfield, poly_master_roots_subfield_dim, finite_field_subfield_dim_divides]);

(* ------------------------------------------------------------------------- *)
(* Splitting Field Equivalence.                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: poly p /\ p <> |0| ==> (splits p <=> (deg (PFROOTS p) = deg p)) *)
(* Proof:
     deg (PFROOTS p)
   = CARD (roots p)        by poly_PFROOTS_deg
   = deg p                 by poly_splits_def
*)
val poly_splits_factor_prod_deg = store_thm(
  "poly_splits_factor_prod_deg",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==> (splits p <=> (deg (PFROOTS p) = deg p))``,
  rw[poly_prod_factor_roots_deg, poly_splits_def]);

(*
poly_splits_def;
val it = |- !r p. splits p <=> (CARD (roots p) = deg p): thm
*)

(* Theorem: monic p ==> (splits p <=> (p = PFROOTS p)) *)
(* Proof:
   If part: splits p ==> (p = PFROOTS p)
      Since (PFROOTS p) pdivides p                by poly_prod_factor_roots_divides
            ?q. poly q /\ (p = q * (PFROOTS p))   by poly_divides_def
        Now monic p                               by given
        and monic (PFROOTS p)                     by poly_prod_factor_roots_monic
         so monic q                               by poly_monic_monic_mult, poly_mult_comm
      Since p <> |0|,
            q <> |0| and (PFROOTS p) <> |0|       by poly_mult_zero
       Also deg p = deg q + deq (PFROOTS p)       by poly_deg_mult_nonzero
       But  deg (PFROOTS p)
          = CARD (roots p)                        by poly_prod_factor_roots_deg
          = deg p                                 by poly_splits_def
      Therefore, deq q = 0.
      Hence q = |1|,                              by poly_monic_deg_0
         or p = PFROOTS p                         by poly_mult_lone
  Only-if part: (p = PFROOTS p) ==> split p
      Since deg p = deg (PFROOTS p)               by given
                  = CARD (roots p)                by poly_prod_factor_roots_deg
      Hence split p                               by poly_splits_def
*)
val poly_splits_monic_alt = store_thm(
  "poly_splits_monic_alt",
  ``!r:'a field. Field r ==> !p. monic p ==> (splits p <=> (p = PFROOTS p))``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0 ` by rw[] >>
  `poly p /\ p <> |0|` by rw[poly_monic_nonzero] >>
  `deg (PFROOTS p) = CARD (roots p)` by rw[poly_prod_factor_roots_deg] >>
  `poly (PFROOTS p)` by rw[] >>
  rw[poly_splits_def, EQ_IMP_THM] >| [
    `?q. poly q /\ (p = q * (PFROOTS p))` by rw[poly_prod_factor_roots_divides, GSYM poly_divides_def] >>
    `monic (PFROOTS p)` by rw[] >>
    `monic q` by metis_tac[poly_monic_monic_mult, poly_mult_comm] >>
    `q <> |0| /\ (PFROOTS p) <> |0|` by metis_tac[poly_mult_zero] >>
    `deg p = deg q + deg (PFROOTS p)` by metis_tac[poly_deg_mult_nonzero] >>
    `deg q = 0` by decide_tac >>
    `q = |1|` by rw[GSYM poly_monic_deg_0] >>
    metis_tac[poly_mult_lone],
    metis_tac[poly_splits_def]
  ]);

(* ------------------------------------------------------------------------- *)
(* Cyclotomic Factorisation of Unity Polynomial                              *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Inverse Map for Field Isomorphism                                         *)
(* ------------------------------------------------------------------------- *)

(* Introduce the opposite of up *)
val _ = overload_on("down", ``LINV up R``);

(*
> type_of ``up``;
val it = ``:'a -> 'a poly``: hol_type
> type_of ``down``;
val it = ``:'a poly -> 'a``: hol_type
*)

(* Theorem: Field r /\ Field s ==> (FieldIso up r s ==> FieldIso down s r) *)
(* Proof: by field_iso_sym *)
val field_iso_up_down = store_thm(
  "field_iso_up_down",
  ``!(r:'a field) s. Field r /\ Field s ==> (FieldIso up r s ==> FieldIso down s r)``,
  metis_tac[field_iso_sym]);

(* Theorem: Field r /\ Field s /\ FieldIso up r s ==>
            !p q. (poly p /\ (q = MAP up p)) <=> (Poly s q /\ (p = MAP down q)) *)
(* Proof:
   If part: poly p /\ (q = MAP up p) ==> Poly s q /\ (p = MAP down q)
      This is to show:
      (1) poly p ==> Poly s (MAP up p), true                   by field_iso_poly
      (2) poly p ==> p = MAP down (MAP up p), true             by field_iso_poly_inv
   Only-if part: Poly s q /\ (p = MAP down q) ==> poly p /\ (q = MAP up p)
      This is to show:
      (1) Poly s q ==> poly (MAP down q), true                 by field_iso_inverse_polynomial
      (2) Poly s q ==> q = MAP (\e. up e) (MAP down q), true   by field_iso_inverse_polynomial
*)
val field_iso_poly_up_down = store_thm(
  "field_iso_poly_up_down",
  ``!(r:'a field) s. Field r /\ Field s /\ FieldIso up r s ==>
     !p q. (poly p /\ (q = MAP up p)) <=> (Poly s q /\ (p = MAP down q))``,
  metis_tac[field_iso_poly, field_iso_poly_inv, field_iso_inverse_polynomial]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Field Extension                                                *)
(* ------------------------------------------------------------------------- *)

(*
poly_mod_irreducible_field
|- !r. Field r ==> !p. monic p /\ ipoly p ==> Field (PolyModRing r p)
poly_mod_const_field
|- !r. Field r ==> !z. monic z /\ ipoly z ==> Field (PolyModConst r z)
poly_mod_const_iso_field_alt
|- !r. Field r ==> !z. monic z /\ ipoly z ==> FieldIso (\e. up e) r (PolyModConst r z)
poly_mod_const_subfield_poly_mod
|- !r. Field r ==> !z. monic z /\ ipoly z ==> subfield (PolyModConst r z) (PolyModRing r z)
poly_mod_const_subfield_dim
|- !r. FiniteField r ==> !z. monic z /\ ipoly z ==> (PolyModRing r z <:> PolyModConst r z = deg z)
poly_monic_irreducible_exists
|- !r. FiniteField r ==> !n. 0 < n ==> ?p. monic p /\ ipoly p /\ (deg p = n)
*)

(* Theorem: FiniteField r /\ 0 < n ==>
            ?t st. FiniteField t /\ st <<= t /\ FieldIso up r st /\ ((t <:> st) = n) /\
            ?z. monic z /\ ipoly z /\ (deg z = n) /\ (t = PolyModRing r z) /\ (st = PolyModConst r z) *)
(* Proof:
   Note ?z. monic z /\ ipoly z /\ (deg z = n)    by poly_monic_irreducible_exists
   Let t = PolyModRing r z, st = PolyModConst r z.
   This is to show:
   (1) FiniteField (PolyModRing r z), true     by poly_mod_irreducible_finite_field
   (2) Field (PolyModRing r z), true           by poly_mod_irreducible_field
   (3) Field (PolyModConst r z), true          by poly_mod_const_field
   (4) subfield (PolyModConst r z) (PolyModRing r z), true          by poly_mod_const_subfield_poly_mod
   (5) FieldIso (\e. up e) r (PolyModConst r z), true               by poly_mod_const_iso_field_alt
   (6) deg z = n ==> PolyModRing r z <:> PolyModConst r z = n, true by poly_mod_const_subfield_dim
   (7) ?z. monic z /\ ipoly z /\ (deg z = n) /\ (t = PolyModRing r z) /\ (st = PolyModConst r z) Take the z.
*)
val field_poly_extend_exists = store_thm(
  "field_poly_extend_exists",
  ``!(r:'a field) n. FiniteField r /\ 0 < n ==>
   ?t st. FiniteField t /\ st <<= t /\ FieldIso up r st /\ ((t <:> st) = n) /\
   ?z. monic z /\ ipoly z /\ (deg z = n) /\ (t = PolyModRing r z) /\ (st = PolyModConst r z)``,
  rpt (stripDup[FiniteField_def]) >>
  `?z. monic z /\ ipoly z /\ (deg z = n)` by rw[poly_monic_irreducible_exists] >>
  qexists_tac `PolyModRing r z` >>
  qexists_tac `PolyModConst r z` >>
  rpt strip_tac >-
  rw[poly_mod_irreducible_finite_field] >-
  rw[poly_mod_irreducible_field] >-
  rw[poly_mod_const_field] >-
  rw[poly_mod_const_subfield_poly_mod] >-
  rw[poly_mod_const_iso_field_alt] >-
  rw[poly_mod_const_subfield_dim] >>
  metis_tac[]);

(* Apply Skolemization *)
val lemma = prove(
  ``!(r:'a field) n. ?t st. FiniteField r /\ 0 < n ==>
        FiniteField t /\ st <<= t /\ FieldIso up r st /\ ((t <:> st) = n) /\
        ?z. monic z /\ ipoly z /\ (deg z = n) /\ (t = PolyModRing r z) /\ (st = PolyModConst r z)``,
  metis_tac[field_poly_extend_exists]);
(* Define polynomial extension *)
(*
> SIMP_RULE bool_ss [SKOLEM_THM] lemma;
val it = |- ?f f'. !r n.
       FiniteField r /\ 0 < n ==>
       FiniteField (f r n) /\ f' r n <<= f r n /\
       FieldIso (\e. up e) r (f' r n) /\ (f r n <:> f' r n = n) /\
       ?z. monic z /\ ipoly z /\ (deg z = n) /\ (f r n = PolyModRing r z) /\ (f' r n = PolyModConst r z) : thm
> SIMP_RULE bool_ss [SKOLEM_THM] lemma |> CONV_RULE (RENAME_VARS_CONV ["fhigh", "flow"]);
*)
val field_poly_extend_def = new_specification(
  "field_poly_extend_def",
  ["field_poly_extend_high", "field_poly_extend_low"],
  SIMP_RULE bool_ss [SKOLEM_THM] lemma);
(*
val field_poly_extend_def =
   |- !r n. FiniteField r /\ 0 < n ==>
     FiniteField (field_poly_extend_high r n) /\
     field_poly_extend_low r n <<= field_poly_extend_high r n /\
     FieldIso (\e. up e) r (field_poly_extend_low r n) /\
     (field_poly_extend_high r n <:> field_poly_extend_low r n = n) /\
     ?z. monic z /\ ipoly z /\ (deg z = n) /\
       (field_poly_extend_high r n = PolyModRing r z) /\
       (field_poly_extend_low r n = PolyModConst r z) : thm
*)

(* Overload field_poly_extend_high and field_poly_extend_low *)
val _ = overload_on("FieldHigh", ``field_poly_extend_high r``);
val _ = overload_on("FieldLow", ``field_poly_extend_low r``);

(*
> field_poly_extend_def;
val it = |- !r n. FiniteField r /\ 0 < n ==>
     FiniteField (FieldHigh n) /\ FieldLow n <<= FieldHigh n /\
     FieldIso (\e. up e) r (FieldLow n) /\
     ((FieldHigh n <:> FieldLow n) = n) /\
     ?z. monic z /\ ipoly z /\ (deg z = n) /\
         (FieldHigh n = PolyModRing r z) /\ (FieldLow n = PolyModConst r z) : thm
*)

(* Theorem: FiniteField r /\ 0 < n ==> let t = FieldHigh n in let st = FieldLow n in
            FiniteField t /\ st <<= t /\ FieldIso up r st /\ ((t <:> st) = n) *)
(* Proof: by field_poly_extend_def *)
val field_poly_extend_property = store_thm(
  "field_poly_extend_property",
  ``!(r:'a field) n. FiniteField r /\ 0 < n ==> let t = FieldHigh n in let st = FieldLow n in
                    FiniteField t /\ st <<= t /\ FieldIso up r st /\ ((t <:> st) = n)``,
  rw[field_poly_extend_def]);

(* Theorem: FiniteField r /\ 0 < n ==> ?z. monic z /\ ipoly z /\ (deg z = n) /\
            (FieldHigh n = PolyModRing r z) /\ (FieldLow n = PolyModConst r z) *)
(* Proof: by field_poly_extend_def *)
val field_poly_extend_irreducible_exists = store_thm(
  "field_poly_extend_irreducible_exists",
  ``!(r:'a field) n. FiniteField r /\ 0 < n ==> ?z. monic z /\ ipoly z /\ (deg z = n) /\
                    (FieldHigh n = PolyModRing r z) /\ (FieldLow n = PolyModConst r z)``,
  rw[field_poly_extend_def]);

(* Theorem: FiniteField r /\ 0 < n ==> let t = FieldHigh n in let st = FieldLow n in
            (st.sum.id = |0|) /\ (st.prod.id = |1|) /\ (t.sum.id = |0|) /\ (t.prod.id = |1|) *)
(* Proof:
   Note st <<= t /\ FieldIso up r st      by field_poly_extend_property
   Therefore,
   (1) st.sum.id = |0|
         st.sum.id
       = up #0       by field_iso_ids
       = |0|         by up_zero
   (2) st.prod.id = |1|
         st.prod.id
       = up #1       by field_iso_ids
       = |1|         by up_one, field_one_ne_zero
   (3) t.sum.id = |0|
         t.sum.id
       = st.sum.id   by subfield_ids
       = up #0       by field_iso_ids
       = |0|         by up_zero
   (4) t.prod.id = |1|
         t.prod.id
       = st.prod.id  by subfield_ids
       = up #1       by field_iso_ids
       = |1|         by up_one, field_one_ne_zero
*)
val field_poly_extend_ids = store_thm(
  "field_poly_extend_ids",
  ``!(r:'a field) n. FiniteField r /\ 0 < n ==>
    let t = FieldHigh n in let st = FieldLow n in
    (st.sum.id = |0|) /\ (st.prod.id = |1|) /\ (t.sum.id = |0|) /\ (t.prod.id = |1|)``,
  ntac 3 (stripDup[FiniteField_def]) >>
  `(FieldLow n) <<= (FieldHigh n) /\ FieldIso up r (FieldLow n)` by metis_tac[field_poly_extend_property] >>
  qabbrev_tac `f = \e. up e` >>
  `!x. f x = up x` by rw[] >>
  metis_tac[subfield_ids, field_iso_ids, up_zero, up_one, field_one_ne_zero]);

(* Theorem: FiniteField r /\ 0 < n ==>
            (CARD (FieldLow n).carrier = CARD R) /\ (CARD (FieldHigh n).carrier = (CARD R) ** n) *)
(* Proof:
   Let t = FieldHigh n, st = FieldLow n.
   Then FiniteField t /\ st <<= t /\
        FieldIso up r st /\ ((t <:> st) = n)  by field_poly_extend_property
   Thus CARD st.carrier = CARD R              by field_iso_card_eq
    and CARD t.carrier = (CARD R) ** n        by finite_subfield_card_eqn
*)
val field_poly_extend_cards = store_thm(
  "field_poly_extend_cards",
  ``!(r:'a field) n. FiniteField r /\ 0 < n ==>
                    (CARD (FieldLow n).carrier = CARD R) /\
                    (CARD (FieldHigh n).carrier = (CARD R) ** n)``,
  metis_tac[field_poly_extend_property, finite_subfield_card_eqn, field_iso_card_eq, finite_field_is_field]);

(* Theorem: FiniteField r /\ 0 < k ==> let t = FieldHigh k in let st = FieldLow k in
            !n. (Master t n = Master st n) /\
                (Master st n = MAP up (master n)) /\ (master n = MAP down (Master st n)) *)
(* Proof:
   This is to show:
   (1) Master t n = Master st n
       Note st <<= t                          by field_poly_extend_property
         so st <= t                           by subfield_is_subring
       Thus Master t n = Master st n          by subring_poly_master
   (2) Master st n = MAP up (master n)
       Note st <<= t /\ FieldIso up r st      by field_poly_extend_property
       Thus Master st n = MAP up (master n)   by field_iso_poly_master
   (3) master n = MAP down (Master st n)
       Note st <<= t /\ FieldIso up r st      by field_poly_extend_property
       Thus Master st n = MAP up (master n)   by field_iso_poly_master
        Now poly (master n)                   by poly_master_poly
         so master n = MAP down (Master st n) by field_iso_poly_up_down
*)
val field_poly_extend_master = store_thm(
  "field_poly_extend_master",
  ``!(r:'a field) k. FiniteField r /\ 0 < k ==>
    let t = FieldHigh k in let st = FieldLow k in
    !n. (Master t n = Master st n) /\
        (Master st n = MAP up (master n)) /\ (master n = MAP down (Master st n))``,
  ntac 3 (stripDup[FiniteField_def]) >>
  rw_tac std_ss[] >| [
    `st <<= t` by metis_tac[field_poly_extend_property] >>
    rw[subring_poly_master, subfield_is_subring],
    `st <<= t /\ FieldIso up r st` by metis_tac[field_poly_extend_property] >>
    rw[field_iso_poly_master],
    `st <<= t /\ FieldIso up r st` by metis_tac[field_poly_extend_property] >>
    `Master st n = MAP up (master n)` by rw[field_iso_poly_master] >>
    `poly (master n)` by rw[] >>
    metis_tac[field_iso_poly_up_down]
  ]);

(* Theorem: FiniteField r /\ 0 < k ==> let t = FieldHigh k in let st = FieldLow k in
            !n. (Unity t n = Unity st n) /\
                (Unity st n = MAP up (unity n)) /\ (unity n = MAP down (Unity st n)) *)
(* Proof:
   This is to show:
   (1) Unity t n = Unity st n
       Note st <<= t                          by field_poly_extend_property
         so st <= t                           by subfield_is_subring
       Thus Unity t n = Unity st n            by subring_poly_unity
   (2) Unity st n = MAP up (unity n)
       Note st <<= t /\ FieldIso up r st      by field_poly_extend_property
       Thus Unity st n = MAP up (unity n)     by field_iso_poly_unity
   (3) unity n = MAP down (Unity st n)
       Note st <<= t /\ FieldIso up r st      by field_poly_extend_property
       Thus Unity st n = MAP up (unity n)     by field_iso_poly_unity
        Now poly (unity n)                    by poly_unity_poly
         so unity n = MAP down (Unity st n)   by field_iso_poly_up_down
*)
val field_poly_extend_unity = store_thm(
  "field_poly_extend_unity",
  ``!(r:'a field) k. FiniteField r /\ 0 < k ==>
    let t = FieldHigh k in let st = FieldLow k in
    !n. (Unity t n = Unity st n) /\
        (Unity st n = MAP up (unity n)) /\ (unity n = MAP down (Unity st n))``,
  ntac 3 (stripDup[FiniteField_def]) >>
  rw_tac std_ss[] >| [
    `st <<= t` by metis_tac[field_poly_extend_property] >>
    rw[subring_poly_unity, subfield_is_subring],
    `st <<= t /\ FieldIso up r st` by metis_tac[field_poly_extend_property] >>
    rw[field_iso_poly_unity],
    `st <<= t /\ FieldIso up r st` by metis_tac[field_poly_extend_property] >>
    `Unity st n = MAP up (unity n)` by rw[field_iso_poly_unity] >>
    `poly (unity n)` by rw[] >>
    metis_tac[field_iso_poly_up_down]
  ]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Splitting Field Extension                                      *)
(* ------------------------------------------------------------------------- *)

(* As we shall see, it is over FieldHigh (ordz n (CARD R)) that (unity n) splits *)

(* Define the coprime extension based on ordz n (CARD R) *)
val _ = overload_on("SplitHigh", ``\n. FieldHigh (ordz n (CARD R))``);
val _ = overload_on("SplitLow", ``\n. FieldLow (ordz n (CARD R))``);

(* Theorem: FiniteField r ==> !n. coprime n (CARD R) ==> 0 < n *)
(* Proof:
   By contradiction, suppose n = 0.
   Then CARD R = 1                   by coprime_0L
   But this contradicts 1 < CARD R   by finite_field_card_gt_1
*)
val finite_field_card_coprime_pos = store_thm(
  "finite_field_card_coprime_pos",
  ``!r:'a field. FiniteField r ==> !n. coprime n (CARD R) ==> 0 < n``,
  metis_tac[coprime_0L, finite_field_card_gt_1, LESS_NOT_EQ, NOT_LT_ZERO_EQ_ZERO]);

(* Theorem: FiniteField r /\ coprime n (CARD R) ==>
            let t = SplitHigh n in let st = SplitLow n in
            FiniteField t /\ st <<= t /\ FieldIso up r st /\
            ((t <:> st) = ordz n (CARD R)) /\ n divides (CARD (ring_nonzero t)) *)
(* Proof:
   Note 0 < n                                by finite_field_card_coprime_pos, coprime n (CARD R)
   Let d = ordz n (CARD R).
   Then 0 < d                                by ZN_coprime_order, 0 < n
    ==> FiniteField t /\ st <<= t /\
        FieldIso up r st /\ ((t <:> st) = d) by field_poly_extend_property

   Also CARD st.carrier = CARD R             by field_iso_card_eq
   Thus n divides (CARD (ring_nonzero t))    by subfield_card_coprime_iff
*)
val field_split_extend_property = store_thm(
  "field_split_extend_property",
  ``!(r:'a field) n. FiniteField r /\ coprime n (CARD R) ==>
   let t = SplitHigh n in let st = SplitLow n in
      FiniteField t /\ st <<= t /\ FieldIso up r st /\
      ((t <:> st) = ordz n (CARD R)) /\ n divides (CARD (ring_nonzero t))``,
  rpt (stripDup[FiniteField_def]) >>
  `0 < n` by metis_tac[finite_field_card_coprime_pos] >>
  qabbrev_tac `d = ordz n (CARD R)` >>
  `0 < d` by rw[ZN_coprime_order, Abbr`d`] >>
  qabbrev_tac `t = FieldHigh d` >>
  qabbrev_tac `st = FieldLow d` >>
  metis_tac[field_poly_extend_property, field_iso_card_eq, subfield_card_coprime_iff]);

(* Theorem: FiniteField r /\ coprime n (CARD R) ==>
            ?z. monic z /\ ipoly z /\ (deg z = ordz n (CARD R)) /\
                (SplitHigh n = PolyModRing r z) /\ (SplitLow n = PolyModConst r z) *)
(* Proof:
   Note 0 < n                                by finite_field_card_coprime_pos, coprime n (CARD R)
   Then 0 < ordz n (CARD R)                  by ZN_coprime_order, 0 < n
    ==> ?z. monic z /\ ipoly z /\ (deg z = ordz n (CARD R)) /\
           (t = PolyModRing r z) /\ (st = PolyModConst r z)   by field_poly_extend_irreducible_exists
*)
val field_split_extend_irreducible_exists = store_thm(
  "field_split_extend_irreducible_exists",
  ``!(r:'a field) n. FiniteField r /\ coprime n (CARD R) ==>
   ?z. monic z /\ ipoly z /\ (deg z = ordz n (CARD R)) /\
       (SplitHigh n = PolyModRing r z) /\ (SplitLow n = PolyModConst r z)``,
  metis_tac[finite_field_card_coprime_pos, ZN_coprime_order, field_poly_extend_irreducible_exists]);

(* Theorem: FiniteField r /\ coprime n (CARD R) ==> let t = SplitHigh n in let st = SplitLow n in
            (st.sum.id = |0|) /\ (st.prod.id = |1|) /\ (t.sum.id = |0|) /\ (t.prod.id = |1|) *)
(* Proof:
   Note 0 < n                                   by finite_field_card_coprime_pos, coprime n (CARD R)
   Let d = ordz n (CARD R).
   Then 0 < d                                   by ZN_coprime_order, 0 < n
    and t = SplitHigh n = FieldHigh d           by notation
    and st = SplitLow n = FieldLow d            by notation
    ==> (st.sum.id = |0|) /\ (st.prod.id = |1|) /\
        (t.sum.id = |0|) /\ (t.prod.id = |1|)   by field_poly_extend_ids
*)
val field_split_extend_ids = store_thm(
  "field_split_extend_ids",
  ``!(r:'a field) n. FiniteField r /\ coprime n (CARD R) ==>
    let t = SplitHigh n in let st = SplitLow n in
    (st.sum.id = |0|) /\ (st.prod.id = |1|) /\ (t.sum.id = |0|) /\ (t.prod.id = |1|)``,
  rpt (stripDup[FiniteField_def]) >>
  `0 < n` by metis_tac[finite_field_card_coprime_pos] >>
  `0 < ordz n (CARD R)` by rw[ZN_coprime_order] >>
  metis_tac[field_poly_extend_ids]);

(* Theorem: FiniteField r /\ coprime n (CARD R) ==>
            (CARD (SplitLow n).carrier = CARD R) /\ (CARD (SplitHigh n).carrier = (CARD R) ** (ordz n (CARD R))) *)
(* Proof:
   Let t = SplitHigh n, st = SplitLow n.
   Then FiniteField t /\ st <<= t /\
        FieldIso up r st /\ ((t <:> st) = ordz n (CARD R))  by field_split_extend_property
   Thus CARD st.carrier = CARD R                            by field_iso_card_eq
    and CARD t.carrier = (CARD R) ** ordz n (CARD R)        by finite_subfield_card_eqn
*)
val field_split_extend_cards = store_thm(
  "field_split_extend_cards",
  ``!(r:'a field) n. FiniteField r /\ coprime n (CARD R) ==>
                    (CARD (SplitLow n).carrier = CARD R) /\
                    (CARD (SplitHigh n).carrier = (CARD R) ** (ordz n (CARD R)))``,
  ntac 3 (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = SplitHigh n` >>
  qabbrev_tac `st = SplitLow n` >>
  `FiniteField t /\ st <<= t /\ FieldIso up r st /\ ((t <:> st) = ordz n (CARD R))` by metis_tac[field_split_extend_property] >>
  metis_tac[finite_subfield_card_eqn, field_iso_card_eq]);

(* Theorem: FiniteField r /\ coprime k (CARD R) ==>
            let t = SplitHigh k in let st = SplitLow k in
            !n. (Master t n = Master st n) /\
                (Master st n = MAP up (master n)) /\ (master n = MAP down (Master st n)) *)
(* Proof:
   Note 0 < k                 by finite_field_card_coprime_pos, coprime k (CARD R)
     so 0 < ordz k (CARD R)   by ZN_coprime_order, 0 < k
   Thus true                  by field_poly_extend_master, 0 < ordz k (CARD R)
*)
val field_split_extend_master = store_thm(
  "field_split_extend_master",
  ``!(r:'a field) k. FiniteField r /\ coprime k (CARD R) ==>
    let t = SplitHigh k in let st = SplitLow k in
    !n. (Master t n = Master st n) /\
        (Master st n = MAP up (master n)) /\ (master n = MAP down (Master st n))``,
  ntac 3 (stripDup[FiniteField_def]) >>
  `0 < k` by metis_tac[finite_field_card_coprime_pos] >>
  `0 < ordz k (CARD R)` by rw[ZN_coprime_order] >>
  metis_tac[field_poly_extend_master]);

(* Theorem: FiniteField r /\ coprime k (CARD R) ==>
            let t = SplitHigh k in let st = SplitLow k in
            !n. (Unity t n = Unity st n) /\
                (Unity st n = MAP up (unity n)) /\ (unity n = MAP down (Unity st n)) *)
(* Proof:
   Note 0 < k                 by finite_field_card_coprime_pos, coprime k (CARD R)
     so 0 < ordz k (CARD R)   by ZN_coprime_order, 0 < k
   Thus true                  by field_poly_extend_unity, 0 < ordz k (CARD R)
*)
val field_split_extend_unity = store_thm(
  "field_split_extend_unity",
  ``!(r:'a field) k. FiniteField r /\ coprime k (CARD R) ==>
    let t = SplitHigh k in let st = SplitLow k in
    !n. (Unity t n = Unity st n) /\
        (Unity st n = MAP up (unity n)) /\ (unity n = MAP down (Unity st n))``,
  ntac 3 (stripDup[FiniteField_def]) >>
  `0 < k` by metis_tac[finite_field_card_coprime_pos] >>
  `0 < ordz k (CARD R)` by rw[ZN_coprime_order] >>
  metis_tac[field_poly_extend_unity]);

(* Theorem: FiniteField r /\ coprime n (CARD R) ==>
            let t = SplitHigh n in poly_splits t (Unity t n) *)
(* Proof:
   Note 0 < n                                             by finite_field_card_coprime_pos
    and FiniteField t /\ n divides CARD (ring_nonzero t)  by field_split_extend_property
   Thus poly_splits t (Unity t n)                         by poly_unity_splitting_condition
*)
val field_split_extend_splits_unity = store_thm(
  "field_split_extend_splits_unity",
  ``!(r:'a field) n. FiniteField r /\ coprime n (CARD R) ==>
    let t = SplitHigh n in poly_splits t (Unity t n)``,
  rpt (stripDup[FiniteField_def]) >>
  rw_tac std_ss[] >>
  `0 < n` by metis_tac[finite_field_card_coprime_pos] >>
  `FiniteField t /\ n divides CARD (ring_nonzero t)` by metis_tac[field_split_extend_property] >>
  rw[poly_unity_splitting_condition]);

(* Theorem: FiniteField r /\ coprime n (CARD R) ==>
            let t = SplitHigh n in (Unity t n = poly_prod_image t (poly_cyclo t) (divisors n)) *)
(* Proof:
   Note FiniteField t /\ n divides CARD (ring_nonzero t)           by field_split_extend_property
    ==> Unity t n = poly_prod_image t (poly_cyclo t) (divisors n)  by poly_unity_eq_poly_cyclo_product
*)
val field_split_extend_unity_factors = store_thm(
  "field_split_extend_unity_factors",
  ``!(r:'a field) n. FiniteField r /\ coprime n (CARD R) ==>
    let t = SplitHigh n in (Unity t n = poly_prod_image t (poly_cyclo t) (divisors n))``,
  metis_tac[poly_unity_eq_poly_cyclo_product, field_split_extend_property]);

(* ------------------------------------------------------------------------- *)
(* Cyclotomic Factorisation of Unity                                         *)
(* ------------------------------------------------------------------------- *)

(* Overload the cyclotomic polynomials in original FiniteField r *)
val _ = overload_on("Phi", ``\n m. MAP down (poly_cyclo (SplitHigh n) m)``);

(* Theorem: FiniteField r /\ coprime k (CARD R) ==> !n. poly (Phi k n) *)
(* Proof:
   Let t = SplitHigh k, st = SplitLow k.
   Note FiniteField t /\ st <<= t /\ FieldIso up r st  by field_split_extend_property
   Thus Poly st (poly_cyclo t n)                       by poly_cyclo_spoly
    Now FieldIso down st r                             by field_iso_sym
     so poly (MAP down (poly_cyclo t n))               by field_iso_poly, field_iso_sym
     or poly (Phi k n)                                 by notation
*)
val poly_phi_poly = store_thm(
  "poly_phi_poly",
  ``!(r:'a field) k. FiniteField r /\ coprime k (CARD R) ==> !n. poly (Phi k n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = SplitHigh k` >>
  qabbrev_tac `st = SplitLow k` >>
  `FiniteField t /\ st <<= t /\ FieldIso up r st` by metis_tac[field_split_extend_property] >>
  metis_tac[poly_cyclo_spoly, field_iso_poly, field_iso_sym]);

(* Theorem: FiniteField r /\ coprime k (CARD R) ==> !n. monic (Phi k n) *)
(* Proof:
   Let t = SplitHigh k, st = SplitLow k.
   Note FiniteField t /\ st <<= t /\ FieldIso up r st  by field_split_extend_property
     so st <= t                                        by subfield_is_subring
   Thus Poly st (poly_cyclo t n)                       by poly_cyclo_spoly
    and Monic t (poly_cyclo t n)                       by poly_cyclo_monic
     so Monic st (poly_cyclo t n)                      by subring_poly_monic_iff
    Now FieldIso down st r                             by field_iso_sym
    ==> monic (MAP down (poly_cyclo t n))              by field_iso_poly_monic_iff
     or monic (Phi k n)                                by notation
*)
val poly_phi_monic = store_thm(
  "poly_phi_monic",
  ``!(r:'a field) k. FiniteField r /\ coprime k (CARD R) ==> !n. monic (Phi k n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = SplitHigh k` >>
  qabbrev_tac `st = SplitLow k` >>
  `FiniteField t /\ st <<= t /\ FieldIso up r st` by metis_tac[field_split_extend_property] >>
  `Poly st (poly_cyclo t n)` by rw[poly_cyclo_spoly] >>
  `Monic t (poly_cyclo t n)` by rw[poly_cyclo_monic] >>
  `Monic st (poly_cyclo t n)` by metis_tac[subring_poly_monic_iff, subfield_is_subring] >>
  metis_tac[field_iso_poly_monic_iff, field_iso_sym]);

(* Theorem: FiniteField r /\ coprime k (CARD R) ==>
            !n. deg (Phi k n) = if n divides (CARD (ring_nonzero (SplitHigh k))) then phi n else 0 *)
(* Proof:
   Let t = SplitHigh k, st = SplitLow k.
   Note FiniteField t /\ st <<= t /\ FieldIso up r st  by field_split_extend_property
     so st <= t                                        by subfield_is_subring

    Now FieldIso down st r               by field_iso_sym

        deg (Phi k n)
      = deg (MAP down (poly_cyclo t n))  by notation
      = Deg st (poly_cyclo t n)          by field_iso_poly_deg
      = Deg t (poly_cyclo t n)           by subring_poly_deg
      = if n divides (CARD (ring_nonzero t)) then phi n else 0   by poly_cyclo_deg_eqn
*)
val poly_phi_deg = store_thm(
  "poly_phi_deg",
  ``!(r:'a field) k. FiniteField r /\ coprime k (CARD R) ==>
   !n. deg (Phi k n) = if n divides (CARD (ring_nonzero (SplitHigh k))) then phi n else 0``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = SplitHigh k` >>
  qabbrev_tac `st = SplitLow k` >>
  `FiniteField t /\ st <<= t /\ FieldIso up r st` by metis_tac[field_split_extend_property] >>
  `deg (Phi k n) = Deg st (poly_cyclo t n)` by rw[field_iso_poly_deg, field_iso_sym] >>
  `_ = Deg t (poly_cyclo t n)` by rw[subring_poly_deg, subfield_is_subring] >>
  metis_tac[poly_cyclo_deg_eqn]);

(* Theorem: FiniteField r /\ coprime k (CARD R) ==> !n. n divides k ==> (deg (Phi k n) = phi n) *)
(* Proof:
   Let t = SplitHigh k.
   Note k divides CARD (ring_nonzero t)    by field_split_extend_property
   Thus n divides CARD (ring_nonzero t)    by DIVIDES_TRANS, n divides k
    ==> deg (Phi k n) = phi n              by poly_phi_deg
*)
val poly_phi_deg_weak = store_thm(
  "poly_phi_deg_weak",
  ``!(r:'a field) k. FiniteField r /\ coprime k (CARD R) ==> !n. n divides k ==> (deg (Phi k n) = phi n)``,
  rpt strip_tac >>
  `k divides CARD (ring_nonzero (SplitHigh k))` by metis_tac[field_split_extend_property] >>
  metis_tac[poly_phi_deg, DIVIDES_TRANS]);

(* Theorem: FiniteField r /\ coprime k (CARD R) ==> !n. MAP up (Phi k n) = poly_cyclo (SplitHigh k) n *)
(* Proof:
   Let t = SplitHigh k, st = SplitLow k.
   Note FiniteField t /\ st <<= t /\ FieldIso up r st  by field_split_extend_property
    Let p = (poly_cyclo t n).
    Now Poly st p                        by poly_cyclo_spoly
   Thus MAP up (MAP down p) = p          by field_iso_inverse_polynomial
*)
val poly_phi_up_cyclo = store_thm(
  "poly_phi_up_cyclo",
  ``!(r:'a field) k. FiniteField r /\ coprime k (CARD R) ==>
   !n. MAP up (Phi k n) = poly_cyclo (SplitHigh k) n``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = SplitHigh k` >>
  qabbrev_tac `st = SplitLow k` >>
  `FiniteField t /\ st <<= t /\ FieldIso up r st` by metis_tac[field_split_extend_property] >>
  `Poly st (poly_cyclo t n)` by rw[poly_cyclo_spoly] >>
  metis_tac[field_iso_inverse_polynomial]);

(* Theorem: FiniteField r /\ coprime n (CARD R) ==> (unity n = PPIMAGE (Phi n) (divisors n)) *)
(* Proof:
   Let t = SplitHigh n, st = SplitLow n.
   Then FiniteField t /\ st <<= t /\ FieldIso up r st  by field_split_extend_property
     so r <= t                      by subfield_is_subring
   Also FINITE (divisors n)         by divisors_finite

   Let p = IMAGE (poly_cyclo t) (divisors n).
   Then FINITE p                    by IMAGE_FINITE
    and poly_set st p               by poly_cyclo_spoly

     unity n
   = MAP down (Unity st n)          by field_split_extend_unity
   = MAP down (Unity t n)           by field_split_extend_unity
   = MAP down (poly_prod_image t (poly_cyclo t) (divisors n))  by field_split_extend_unity_factors
   = MAP down (poly_prod_set t p)   by notation
   = MAP down (poly_prod_set st p)  by subring_poly_prod_set, FINITE p, poly_set st p
   = PPIMAGE (MAP down) p           by field_iso_poly_prod_set, field_iso_sym
   = PPROD (IMAGE (MAP down) (IMAGE (poly_cyclo t) (divisors n)))  by notation
   = PPROD (IMAGE (\m. MAP down (poly_cyclo t m)) (divisors n))    by IMAGE_COMPOSE, FUN_EQ_THM
   = PPIMAGE (Phi n) (divisors n)   by notation
*)
val poly_unity_cyclo_factors = store_thm(
  "poly_unity_cyclo_factors",
  ``!(r:'a field) n. FiniteField r /\ coprime n (CARD R) ==> (unity n = PPIMAGE (Phi n) (divisors n))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = SplitHigh n` >>
  qabbrev_tac `st = SplitLow n` >>
  `FiniteField t /\ st <<= t /\ FieldIso up r st` by metis_tac[field_split_extend_property] >>
  `st <= t` by rw[subfield_is_subring] >>
  `FINITE (divisors n)` by rw[divisors_finite] >>
  qabbrev_tac `p = IMAGE (poly_cyclo t) (divisors n)` >>
  `FINITE p` by rw[Abbr`p`] >>
  `poly_set st p` by
  (`!x. x IN p <=> ?m. (x = poly_cyclo t m) /\ m IN (divisors n)` by rw[Abbr`p`] >>
  metis_tac[poly_cyclo_spoly]) >>
  (`!(f:'a poly -> 'a) (g:num -> 'a poly poly) s. IMAGE (MAP f) (IMAGE g s) = IMAGE (\m. MAP f (g m)) s` by (rw[IMAGE_COMPOSE, FUN_EQ_THM] >> metis_tac[])) >>
  metis_tac[field_split_extend_unity, field_split_extend_unity_factors, subring_poly_prod_set, field_iso_poly_prod_set, field_iso_sym]);

(* This is a milestone theorem! *)

(* Theorem: FiniteField r /\ coprime n (CARD R) ==>
            (unity n = PPROD {Phi n m | m | m IN (divisors n)}) *)
(* Proof: by poly_unity_cyclo_factors *)
val poly_unity_cyclo_factors_alt = store_thm(
  "poly_unity_cyclo_factors_alt",
  ``!(r:'a field) n. FiniteField r /\ coprime n (CARD R) ==>
                    (unity n = PPROD {Phi n m | m | m IN (divisors n)})``,
  rpt strip_tac >>
  `{Phi n m | m | m IN (divisors n)} = IMAGE (Phi n) (divisors n)` by rw[EXTENSION] >>
  simp[poly_unity_cyclo_factors]);

(* Theorem: FiniteField r /\ coprime k (CARD R) ==>
            !n. n divides k ==> (Phi k n) pdivides (unity k) /\ (deg (Phi k n) = phi n) *)
(* Proof:
   This is to show:
   (1) (Phi k n) pdivides (unity k)
       Let p = IMAGE (Phi k) (divisors k).
       Then unity k = PPROD p                 by poly_unity_cyclo_factors
       Note 0 < k                             by finite_field_card_coprime_pos
        Now n IN (divisors k)                 by divisors_element_alt
         so (Phi k n) IN p                    by IN_IMAGE
       Note FINITE (divisors k)               by divisors_finite
         so FINITE p                          by IMAGE_FINITE
        and pset p                            by poly_phi_poly
       Thus (Phi k n) pdivides (unity k)      by poly_prod_set_element_divides
   (2) n divides k ==> deg (Phi k n) = phi n
       True                                   by poly_phi_deg_weak
*)
val poly_phi_divides_unity = store_thm(
  "poly_phi_divides_unity",
  ``!(r:'a field) k. FiniteField r /\ coprime k (CARD R) ==>
   !n. n divides k ==> (Phi k n) pdivides (unity k) /\ (deg (Phi k n) = phi n)``,
  rpt (stripDup[FiniteField_def]) >| [
    qabbrev_tac `p = IMAGE (Phi k) (divisors k)` >>
    `!x. x IN p <=> ?m. (x = Phi k m) /\ m IN divisors k` by rw[Abbr`p`] >>
    `unity k = PPROD p` by rw[poly_unity_cyclo_factors] >>
    `0 < k` by metis_tac[finite_field_card_coprime_pos] >>
    `n IN (divisors k)` by rw[divisors_element_alt] >>
    `(Phi k n) IN p` by metis_tac[] >>
    `FINITE (divisors k)` by rw[divisors_finite] >>
    `FINITE p` by rw[Abbr`p`] >>
    `pset p` by metis_tac[poly_phi_poly] >>
    metis_tac[poly_prod_set_element_divides, field_is_ring],
    rw[poly_phi_deg_weak]
  ]);

(* Theorem: FiniteField r /\ coprime k (CARD R) ==> let t = SplitHigh k in
            !x n. x IN poly_roots t (MAP up (Phi k n)) ==> (order (t.prod excluding |0|) x = n) *)
(* Proof:
   Let st = SplitLow k.
   Note MAP (\e. up e) (Phi k n) = poly_cyclo t n     by poly_phi_up_cyclo
    and FiniteField t /\ r <<= t /\ FieldIso up r st  by field_split_extend_property
   Also t.sum.id = |0|                                by field_split_extend_ids
    Now Poly st (poly_cyclo t n)                      by poly_cyclo_spoly
   Thus order (t.prod excluding |0|) x = n            by poly_cyclo_root_order
*)
val poly_phi_root_order = store_thm(
  "poly_phi_root_order",
  ``!(r:'a field) k. FiniteField r /\ coprime k (CARD R) ==> let t = SplitHigh k in
    !x n. x IN poly_roots t (MAP up (Phi k n)) ==> (order (t.prod excluding |0|) x = n)``,
  rpt (stripDup[FiniteField_def]) >>
  rw_tac std_ss[poly_phi_up_cyclo] >>
  qabbrev_tac `st = SplitLow k` >>
  `FiniteField t /\ st <<= t /\ FieldIso up r st` by metis_tac[field_split_extend_property] >>
  `t.sum.id = |0|` by metis_tac[field_split_extend_ids] >>
  `Poly st (poly_cyclo t n)` by rw[poly_cyclo_spoly] >>
  metis_tac[poly_cyclo_root_order]);

(* Theorem: FiniteField r /\ coprime k (CARD R) ==>
            !n. n divides k ==> (Phi k n) pdivides (unity k) /\ (deg (Phi k n) = phi n) /\
                let t = SplitHigh k in
                !x. x IN poly_roots t (MAP up (Phi k n)) ==> (order (t.prod excluding |0|) x = n) *)
(* Proof: by poly_phi_divides_unity, poly_phi_root_order *)
val poly_unity_phi_factor_property = store_thm(
  "poly_unity_phi_factor_property",
  ``!(r:'a field) k. FiniteField r /\ coprime k (CARD R) ==>
   !n. n divides k ==> (Phi k n) pdivides (unity k) /\ (deg (Phi k n) = phi n) /\
   let t = SplitHigh k in
   !x. x IN poly_roots t (MAP up (Phi k n)) ==> (order (t.prod excluding |0|) x = n)``,
  metis_tac[poly_phi_divides_unity, poly_phi_root_order]);

(* Theorem: FiniteField r /\ coprime k (CARD R) ==>
            !p. monic p /\ ipoly p ==> !n. 0 < n /\ p pdivides (Phi k n) ==> (deg p = ordz n (CARD R)) *)
(* Proof:
   Let t = SplitHigh k, st = SplitLow k.
   Then FiniteField t /\ st <<= t /\ FieldIso up r st   by field_split_extend_property
     so st <= t            by subfield_is_subring
   Note poly p             by poly_monic_poly
    and poly (Phi k n)     by poly_phi_poly

   Step 1: Move to st = SplitLow k.
    Let q = MAP up p.
   Then poly_divides st q (MAP up (Phi k n))   by field_iso_poly_divides
     or poly_divides st q (poly_cyclo t n)     by poly_phi_up_cyclo
   Note deg p = Deg st q                       by field_iso_poly_deg
    and Monic st q                             by field_iso_poly_monic
    and IPoly st q                             by field_iso_poly_irreducible]

   Step 2: Move to t = SplitHigh k.
    Now Monic st q ==> Monic t q               by subring_poly_monic
    and Deg st q = Deg t q                     by subring_poly_deg
   Also Poly st q                              by poly_monic_poly
    and Poly st (poly_cyclo t n)               by poly_cyclo_spoly
   Thus poly_divides t q (poly_cyclo t n)      by subring_poly_divides

          deg p
        = ordz n (CARD st.carrier)             by poly_cyclo_irreducible_factor_deg
        = ordz n (CARD R)                      by field_iso_card_eq

poly_cyclo_irreducible_factor_deg |> ISPEC ``t:'a field`` |> ISPEC ``st:'a poly field``;
val it = |- FiniteField t /\ st <<= t ==>
            !p. Monic t p /\ IPoly st p ==> !n. 0 < n /\ poly_divides t p (poly_cyclo t n) ==>
                (Deg t p = ordz n (CARD st.carrier)): thm
*)
val poly_phi_irreducible_factor_deg = store_thm(
  "poly_phi_irreducible_factor_deg",
  ``!(r:'a field) k. FiniteField r /\ coprime k (CARD R) ==>
   !p. monic p /\ ipoly p ==> !n. 0 < n /\ p pdivides (Phi k n) ==> (deg p = ordz n (CARD R))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = SplitHigh k` >>
  qabbrev_tac `st = SplitLow k` >>
  `FiniteField t /\ st <<= t /\ FieldIso up r st` by metis_tac[field_split_extend_property] >>
  `st <= t` by rw[subfield_is_subring] >>
  qabbrev_tac `q = MAP up p` >>
  `poly p` by rw[] >>
  `poly (Phi k n)` by metis_tac[poly_phi_poly] >>
  `poly_divides st q (poly_cyclo t n)` by metis_tac[field_iso_poly_divides, poly_phi_up_cyclo] >>
  `deg p = Deg t q` by rw[field_iso_poly_deg, subring_poly_deg, Abbr`q`] >>
  `Monic st q /\ Monic t q /\ IPoly st q` by metis_tac[field_iso_poly_monic, subring_poly_monic, field_iso_poly_irreducible] >>
  `Poly st q /\ Poly st (poly_cyclo t n)` by rw[poly_cyclo_spoly] >>
  `poly_divides t q (poly_cyclo t n)` by metis_tac[subring_poly_divides] >>
  metis_tac[poly_cyclo_irreducible_factor_deg, field_iso_card_eq]);

(* ------------------------------------------------------------------------- *)
(* Unity Splitting Field                                                     *)
(* ------------------------------------------------------------------------- *)

(* Note: (unity n) splits if there is a factor. *)

(* Theorem: 0 < n /\ (deg z = order (ZN n).prod (CARD R)) ==>
            poly_splits (PolyModRing r z) (Unity (PolyModRing r z) n) *)
(* Proof:
   Let d = order (ZN n).prod (CARD R)
   Hence pmonic z                                      by poly_monic_irreducible_property
     and FiniteField (PolyModRing r z)                 by poly_mod_irreducible_finite_field
      so CARD (PolyModRing r z).carrier = CARD R ** d  by poly_mod_irreducible_field_card
      or n divides ((CARD R) ** d - 1)                 by ZN_order_divisibility, 0 < n
   Thus true by poly_unity_splitting_condition, 0 < n.
*)
val unity_splitting_field = store_thm(
  "unity_splitting_field",
  ``!r:'a field. FiniteField r ==> !z. monic z /\ ipoly z ==>
   !n. 0 < n /\ (deg z = ordz n (CARD R)) ==>
       poly_splits (PolyModRing r z) (Unity (PolyModRing r z) n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `d = order (ZN n).prod (CARD R)` >>
  `pmonic z` by rw[poly_monic_irreducible_property] >>
  `FiniteField (PolyModRing r z)` by rw[poly_mod_irreducible_finite_field] >>
  `CARD (PolyModRing r z).carrier = CARD R ** d` by rw[poly_mod_irreducible_field_card, Abbr`d`] >>
  `n divides ((CARD R) ** d - 1)` by rw[ZN_order_divisibility, Abbr`d`] >>
  metis_tac[poly_unity_splitting_condition, finite_field_nonzero_carrier_card]);

(* Theorem: FiniteField r ==> !n. splits (unity n) ==> 0 < n *)
(* Proof:
   By contradiction, assume n = 0.
     Then unity 0 = |0|           by unity_0
      and roots |0| = R           by poly_roots_zero
      Now FINITE R                by FiniteField_def
      and #1 IN R                 by field_one_element
    Hence R <> {}                 by MEMBER_NOT_EMPTY
       or CARD R <> 0             by CARD_EQ_0
      But deg |0| = 0             by poly_unity_deg, field_is_ring, field_one_ne_zero
   which contradicts
      CARD (roots |0|) = deg |0|  by poly_splits_def
*)
val unity_splitting_deg_pos = store_thm(
  "unity_splitting_deg_pos",
  ``!r:'a field. FiniteField r ==> !n. splits (unity n) ==> 0 < n``,
  rpt (stripDup[FiniteField_def]) >>
  spose_not_then strip_assume_tac >>
  `n = 0` by decide_tac >>
  `unity 0 = |0|` by rw[] >>
  `roots |0| = R` by rw[poly_roots_zero] >>
  `CARD R <> 0` by metis_tac[CARD_EQ_0, field_one_element, MEMBER_NOT_EMPTY] >>
  `deg |0| = 0` by rw[] >>
  metis_tac[poly_splits_def]);

(* Theorem: splits (unity n) <=> (CARD (roots (unity n)) = n) *)
(* Proof:
   Since splits (unity n)
     <=> CARD (roots (unity n)) = deg (unity n)    by poly_splits_def
                                = n                by poly_unity_deg
   The result follows.
*)
val splitting_field_uroots_card = store_thm(
  "splitting_field_uroots_card",
  ``!r:'a field. Field r ==> !n. splits (unity n) <=> (CARD (roots (unity n)) = n)``,
  rw[poly_splits_def, poly_unity_deg]);

(* Theorem: FiniteField r ==> !n. splits (unity n) ==> ?x. x IN roots (unity n) /\ (order f* x = n) *)
(* Proof:
   Note FiniteField r
        ==> Field r /\ FINITE R     by FiniteField_def
        ==> FiniteGroup f*          by finite_field_mult_finite_group
        ==> FINITE F*               by FiniteGroup_def
  Since 0 < n                       by unity_splitting_deg_pos
        (roots_of_unity f* n).carrier = roots (unity n)        by field_uroots_are_roots, 0 < n
    and CARD (roots (unity n)) = n  by splitting_field_uroots_card
    Now cyclic f*                   by finite_field_mult_group_cyclic
        ?x. x IN (roots_of_unity f* n).carrier and
            (order f* x = CARD (roots_of_unity f* n).carrier)  by cyclic_uroots_has_primitive
     or x IN roots (unity n) /\ (order f* x = n)
*)
val splitting_field_uroots_primitive = store_thm(
  "splitting_field_uroots_primitive",
  ``!r:'a field. FiniteField r ==> !n. splits (unity n) ==> ?x. x IN roots (unity n) /\ (order f* x = n)``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteGroup f*` by rw[finite_field_mult_finite_group] >>
  `FINITE F*` by metis_tac[FiniteGroup_def] >>
  `0 < n` by metis_tac[unity_splitting_deg_pos] >>
  `(roots_of_unity f* n).carrier = roots (unity n)` by rw[field_uroots_are_roots] >>
  `CARD (roots (unity n)) = n` by rw[GSYM splitting_field_uroots_card] >>
  `cyclic f*` by rw[finite_field_mult_group_cyclic] >>
  metis_tac[cyclic_uroots_has_primitive]);

(* Theorem: FiniteField r ==> !z. monic z /\ ipoly z ==>
            !n. 0 < n /\ coprime n (CARD R) /\ (deg z = ordz n (CARD R)) ==>
            ?p. poly p /\ p <> |0| /\ deg p < deg z /\ (p ** n == |1|) (pm z) /\ (forderz p = n) *)
(* Proof:
   Note FiniteField (PolyModRing r z)         by poly_mod_irreducible_finite_field
     so Ring (PolyModRing r z)                by FiniteField_def
    and 0 < deg z                             by poly_irreducible_deg_nonzero
    and (PolyModRing r z).sum.id = |0|        by poly_mod_ring_ids
    and (PolyModRing r z).prod.id = |1|       by poly_mod_ring_ids, deg z <> 0
    and (PolyModRing r z).prod.id IN (PolyModRing r z).carrier   by ring_one_element
   Since poly_splits (PolyModRing r z)
                     (Unity (PolyModRing r z) n)  by unity_splitting_field, 0 < n
         ?x. x IN poly_roots (PolyModRing r z)
                             (Unity (PolyModRing r z) n)       by splitting_field_uroots_primitive
     and (order ((PolyModRing r z).prod excluding |0|) x = n)  by poly_order_eq_poly_mod_order
      or poly_root (PolyModRing r z) (Unity (PolyModRing r z) n) x             by poly_roots_def
      or poly_eval (PolyModRing r z) (Unity (PolyModRing r z) n) x = |0|       by poly_root_def
      or ring_sub (PolyModRing r z) ((PolyModRing r z).prod.exp x n) |1| = |0| by poly_unity_eval
      or (PolyModRing r z).prod.exp x n = |1|                                  by ring_sub_eq_zero

     Now poly x /\ deg x < deg z              by poly_mod_ring_property, deg z <> 0
     and x % z = x                            by poly_mod_less, deg x < deg z
     and pmonic z                             by poly_monic_pmonic, 0 < deg z
   Since n <> 0                               by 0 < n
      so x <> |0|                             by poly_zero_order, pmonic z
    Thus (x ** n) % z = |1|                   by poly_mod_field_exp
                      = |1| % z               by poly_mod_one, field_is_ring
      or (x ** n == |1|) (pm z)               by pmod_def_alt
   Therefore, take p = x, and check conditions.
*)
val poly_primitive_root_of_unity_order = store_thm(
  "poly_primitive_root_of_unity_order",
  ``!r:'a field. FiniteField r ==> !z. monic z /\ ipoly z ==>
   !n. 0 < n /\ coprime n (CARD R) /\ (deg z = ordz n (CARD R)) ==>
   ?p. poly p /\ p <> |0| /\ deg p < deg z /\ (p ** n == |1|) (pm z) /\ (forderz p = n)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `FiniteField (PolyModRing r z)` by rw[poly_mod_irreducible_finite_field] >>
  `Ring (PolyModRing r z)` by metis_tac[FiniteField_def, field_is_ring] >>
  `0 < deg z` by rw[poly_irreducible_deg_nonzero] >>
  `deg z <> 0` by decide_tac >>
  `(PolyModRing r z).sum.id = |0|` by rw[poly_mod_ring_ids] >>
  `(PolyModRing r z).prod.id = |1|` by rw[poly_mod_ring_ids] >>
  `(PolyModRing r z).prod.id IN (PolyModRing r z).carrier` by rw[] >>
  `poly_splits (PolyModRing r z) (unityz n)` by rw[unity_splitting_field] >>
  `?x. x IN Rz /\ (x **z n -z |1| = |0|) /\ (forderz x = n)`
     by metis_tac[splitting_field_uroots_primitive, poly_order_eq_poly_mod_order,
                  poly_roots_member, poly_root_def, poly_unity_eval] >>
  `poly x /\ deg x < deg z` by metis_tac[poly_mod_ring_property] >>
  `x % z = x` by rw[poly_mod_less] >>
  `pmonic z` by rw[] >>
  `n <> 0` by decide_tac >>
  `x <> |0|` by metis_tac[poly_zero_order] >>
  `(x ** n) % z = |1|` by metis_tac[ring_sub_eq_zero, poly_mod_field_exp, ring_exp_element] >>
  metis_tac[pmod_def_alt, poly_mod_one]);

(* ------------------------------------------------------------------------- *)
(* More Field Isomorphism Theorems                                           *)
(* ------------------------------------------------------------------------- *)

(* Overload cyclotomic polynomial in another field *)
val _ = overload_on("cyclo_", ``poly_cyclo (r_:'b field)``);

(* Note:
poly_cyclo_def                      |- !r n. cyclo n = PIFACTOR (orders f* n)
poly_cyclo_eq_poly_minimal_product  |- !r s. FiniteField r /\ s <<= r ==>
                                       !n. cyclo n = PPIMAGE minimal (orders f* n)
Thus the picture is this:
In a FiniteField r, there is a bunch of elements with the same order n, say {a, b, c ...}
Then cyclo n = (X - a)(X - b)(X - c)...
But genarally, cyclo n is not irreducbile: it has factors.
This is because, although conjugate elements have the same order, same order does not imply being conjugates.
Thus {a, b, c ...} = {conjugates of a} + {conjugates of b} + ....
Each {conjugates of a}, by the same process of (X - a_1)...(X - a_j),
gives a minimal polynomial is the base field, which is irreducible.

Instead of saying: deg (Phi n n) = phi n > 0, thus it has a monic ipoly h, with deg h = ordz n (CARD R),
will it be possible to say: (Phi n n), from (SplitHigh n), has elements of order (ordz n (CARD R)).
Take the corresponding minimal polynomial, use MAP down to get a monic ipoly, and call it h?
*)

(* Theorem: (r === r_) f ==> !s. s SUBSET R ==>
            (IMAGE (MAP f o factor) s = IMAGE (factor_) (IMAGE f s)) *)
(* Proof:
   Note s SUBSET R ==> !x. x IN s ==> x IN R            by SUBSET_DEF
     IMAGE (MAP f o factor) s
   = IMAGE (MAP f) (IMAGE factor s)                     by IMAGE_COMPOSE
   = IMAGE f {factor a, factor b, factor c, ...}        by EXTENSION
   = {factor_ (f a), factor_ (f b), factor_ (f c), ...} by field_iso_poly_factor
   = IMAGE (factor_) (IMAGE f s)                        by EXTENSION
*)
val field_iso_image_factor = store_thm(
  "field_iso_image_factor",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==>
   !s. s SUBSET R ==> (IMAGE (MAP f o factor) s = IMAGE (factor_) (IMAGE f s))``,
  rw[EXTENSION] >>
  metis_tac[field_iso_poly_factor, SUBSET_DEF, MAP]);

(* Theorem: (r === r_) f ==>
            !n. IMAGE (MAP f o factor) (orders f* n) = IMAGE (factor_) (orders f_* n) *)
(* Proof:
   Note (orders f* n) SUBSET R                by field_orders_subset_carrier
     IMAGE (MAP f o factor) (orders f* n)
   = IMAGE (factor_) (IMAGE f (orders f* n))  by field_iso_image_factor
   = IMAGE (factor_) (orders f_* n)           by field_iso_orders
*)
val field_iso_image_factor_orders = store_thm(
  "field_iso_image_factor_orders",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==>
   !n. IMAGE (MAP f o factor) (orders f* n) = IMAGE (factor_) (orders f_* n)``,
  metis_tac[field_iso_image_factor, field_iso_orders, field_orders_subset_carrier]);

(* Theorem: Ring r /\ #1 <> #0 ==> !s. s SUBSET R ==> pset (IMAGE factor s) *)
(* Proof: by poly_map_factor, poly_map_image_poly_set *)
val poly_set_image_factor = store_thm(
  "poly_set_image_factor",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !s. s SUBSET R ==> pset (IMAGE factor s)``,
  metis_tac[poly_map_factor, poly_map_image_poly_set]);

(* Theorem: FiniteField r /\ (r === r_) f ==> !n. MAP f (cyclo n) = cyclo_ n *)
(* Proof:
   Let s = IMAGE factor (orders f* n).
   Note FINITE (orders f* n)     by field_orders_finite
   Then FINITE s                 by IMAGE_FINITE
    and (orders f* n) SUBSET R   by field_orders_subset_carrier
    ==> pset s                   by poly_set_image_factor

     MAP f (cyclo n)
   = MAP f (PIFACTOR (orders f* n))              by poly_cyclo_def
   = MAP f (PPIMAGE factor (orders f* n))        by notation
   = poly_prod_image r_ (MAP f) (IMAGE factor (orders f* n))    by field_iso_poly_prod_set
   = poly_prod_set r_ (IMAGE ((MAP f) o factor) (orders f* n))  by IMAGE_COMPOSE
   = poly_prod_set r_ (IMAGE (factor_) (orders f_* n))          by field_iso_image_factor_orders
   = poly_prod_factors r_ (orders f_* n)         by notation
   = cyclo_ n                                    by poly_cyclo_def
*)
val field_iso_poly_cyclo = store_thm(
  "field_iso_poly_cyclo",
  ``!(r:'a field) (r_:'b field) f. FiniteField r /\ (r === r_) f ==> !n. MAP f (cyclo n) = cyclo_ n``,
  rpt (stripDup[FiniteField_def]) >>
  rw[poly_cyclo_def] >>
  qabbrev_tac `s = IMAGE factor (orders f* n)` >>
  `FINITE (orders f* n)` by rw[field_orders_finite] >>
  `(orders f* n) SUBSET R` by rw[field_orders_subset_carrier] >>
  `FINITE s` by rw[Abbr`s`] >>
  `pset s` by metis_tac[poly_set_image_factor, field_is_ring, field_one_ne_zero] >>
  metis_tac[field_iso_poly_prod_set, field_iso_image_factor_orders, IMAGE_COMPOSE]);

(*
poly_minimal_divides_unity_order
|- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> minimal x pdivides unity (forder x)
poly_minimal_divides_cyclo_order -- missing!
*)

(* Theorem: FiniteField r /\ s <<= r ==> !x. x IN R+ ==> minimal x pdivides cyclo (forder x) *)
(* Proof:
   Let n = forder x, t = IMAGE minimal (orders f* n).
   Then cyclo n = PPROD t             by poly_cyclo_eq_poly_minimal_product
    and x IN orders f* n              by field_orders_element_property, x IN R+
     so (minimal x) IN t              by IN_IMAGE
   Note FINITE (orders f* n)          by field_orders_finite
     so FINITE t                      by IMAGE_FINITE
    and pset t                        by poly_map_image_poly_set, field_orders_subset_carrier, poly_minimal_poly
   Thus (minimal x) pdivides PPROD t  by poly_prod_set_element_divides
*)
val poly_minimal_divides_cyclo_order = store_thm(
  "poly_minimal_divides_cyclo_order",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !x. x IN R+ ==> minimal x pdivides cyclo (forder x)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `n = forder x` >>
  qabbrev_tac `t = IMAGE minimal (orders f* n)` >>
  `cyclo n = PPROD t` by rw[poly_cyclo_eq_poly_minimal_product, Abbr`t`] >>
  `x IN orders f* n` by rw[field_orders_element_property] >>
  `FINITE (orders f* n)` by rw[field_orders_finite] >>
  `FINITE t` by rw[Abbr`t`] >>
  `pset t` by metis_tac[poly_map_image_poly_set, field_orders_subset_carrier, poly_minimal_poly] >>
  rw[poly_prod_set_element_divides, Abbr`t`]);

(*
poly_minimal_roots
|- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> (roots (minimal x) = Conj x)
finite_field_conjugate_order
|- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> !n. forder (conj x n) = forder x
finite_field_conjugates_order
|- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> !y. y IN Conj x ==> (forder y = forder x)
*)

(* Theorem: FiniteField r /\ s <<= r ==>
            !x y. x IN R /\ y IN R /\ root (minimal x) y ==> (forder y = forder x) *)
(* Proof:
   Note y IN roots (minimal x)         by poly_roots_member
     so y IN Conj x                    by poly_minimal_roots
    ==> forder y = forder x            by finite_field_conjugates_order
*)
val poly_minimal_root_order = store_thm(
  "poly_minimal_root_order",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !x y. x IN R /\ y IN R /\ root (minimal x) y ==> (forder y = forder x)``,
  metis_tac[poly_roots_member, poly_minimal_roots, finite_field_conjugates_order]);

(* ------------------------------------------------------------------------- *)
(* The Minimal Polynomial by Element Order                                   *)
(* ------------------------------------------------------------------------- *)

(* Define the minimal polynomial from an element of order n *)
val poly_mini_def = Define`
    poly_mini (r:'a ring) (s:'a ring) n = poly_minimal r s (CHOICE (orders f* n))
`;

(* Overload on poly_mini *)
val _ = overload_on("mini", ``poly_mini r s``);

(*
Note: (mini n) is not unique, due to CHOICE -- that's why it is not in textbooks.
Given an element x IN R, we can write down its (minimal x).
However, given a number n, there is no single (mini n):
we need to find an x with (forder x = n), then find its (minimal x).
In fact, (mini n) = CHOICE (IMAGE minimal (orders f* n)) conceptually.
*)

(* Theorem: FiniteField r /\ s <<= r ==>
            !n. n divides CARD R+ ==> (mini n) IN (IMAGE minimal (orders f* n)) *)
(* Proof:
   Let t = orders f* n.
   Then t <> {}                                  by finite_field_orders_nonempty_iff, n divides CARD R+
     so CHOICE t IN t                            by CHOICE_DEF
    ==> minimal (CHOICE t) IN (IMAGE minimal t)  by IN_IMAGE
     or (mini n) IN (IMAGE minimal t)            by poly_mini_def
*)
val poly_mini_in_image_minimal_orders = store_thm(
  "poly_mini_in_image_minimal_orders",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !n. n divides CARD R+ ==> (mini n) IN (IMAGE minimal (orders f* n))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = orders f* n` >>
  `t <> {}` by rw[GSYM finite_field_orders_nonempty_iff, Abbr`t`] >>
  `CHOICE t IN t` by rw[CHOICE_DEF] >>
  metis_tac[poly_mini_def, IN_IMAGE]);

(* Theorem: FiniteField r /\ s <<= r ==> !n. n divides CARD R+ ==> monic (mini n) *)
(* Proof:
   Let t = orders f* n.
   Then t <> {}                     by finite_field_orders_nonempty_iff, n divides CARD R+
     so CHOICE t IN t               by CHOICE_DEF
    and CHOICE t IN R               by field_orders_element
   Thus monic (minimal (CHOICE t))  by poly_minimal_monic
     or monic (mini n)              by poly_mini_def
*)
val poly_mini_monic = store_thm(
  "poly_mini_monic",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !n. n divides CARD R+ ==> monic (mini n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = orders f* n` >>
  `t <> {}` by rw[GSYM finite_field_orders_nonempty_iff, Abbr`t`] >>
  `CHOICE t IN t` by rw[CHOICE_DEF] >>
  `CHOICE t IN R` by metis_tac[field_orders_element] >>
  rw[poly_minimal_monic, poly_mini_def, Abbr`t`]);

(* Theorem: FiniteField r /\ s <<= r ==> !n. n divides CARD R+ ==> monic (mini n) *)
(* Proof: by poly_mini_monic *)
val poly_mini_poly = store_thm(
  "poly_mini_poly",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !n. n divides CARD R+ ==> poly (mini n)``,
  rw[poly_mini_monic]);

(* Theorem: FiniteField r /\ s <<= r ==> !n. n divides CARD R+ ==> IPoly s (mini n) *)
(* Proof:
   Let t = orders f* n.
   Then t <> {}                       by finite_field_orders_nonempty_iff, n divides CARD R+
     so CHOICE t IN t                 by CHOICE_DEF
    and CHOICE t IN R                 by field_orders_element
   Thus IPoly s (minimal (CHOICE t))  by poly_minimal_subfield_irreducible
     or IPoly s (mini n)              by poly_mini_def
*)
val poly_mini_subfield_irreducible = store_thm(
  "poly_mini_subfield_irreducible",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !n. n divides CARD R+ ==> IPoly s (mini n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = orders f* n` >>
  `t <> {}` by rw[GSYM finite_field_orders_nonempty_iff, Abbr`t`] >>
  `CHOICE t IN t` by rw[CHOICE_DEF] >>
  `CHOICE t IN R` by metis_tac[field_orders_element] >>
  rw[poly_minimal_subfield_irreducible, poly_mini_def, Abbr`t`]);

(* Theorem: FiniteField r /\ s <<= r ==> !n. n divides CARD R+ ==> Poly s (mini n) *)
(* Proof: by poly_mini_subfield_irreducible, poly_irreducible_poly *)
val poly_mini_subfield_poly = store_thm(
  "poly_mini_subfield_poly",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !n. n divides CARD R+ ==> Poly s (mini n)``,
  rw[poly_mini_subfield_irreducible, poly_irreducible_poly]);

(* Theorem: FiniteField r /\ s <<= r ==> !n. n divides CARD R+ ==> Monic s (mini n) *)
(* Proof:
   Since Poly s (mini n)        by poly_mini_subfield_poly
     and monic (mini n)         by poly_mini_monic
    Thus Monic (mini n)         by subring_poly_monic_iff, subfield_is_subring
*)
val poly_mini_subfield_monic = store_thm(
  "poly_mini_subfield_monic",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !n. n divides CARD R+ ==> Monic s (mini n)``,
  metis_tac[poly_mini_monic, poly_mini_subfield_poly, subring_poly_monic_iff, subfield_is_subring]);

(* Theorem: FiniteField r /\ s <<= r ==> !n. n divides CARD R+ ==> (deg (mini n) = ordz n (CARD B)) *)
(* Proof:
   Let t = orders f* n.
   Then t <> {}                       by finite_field_orders_nonempty_iff, n divides CARD R+
     so CHOICE t IN t                 by CHOICE_DEF
    and CHOICE t IN R+                by field_orders_element_property
   Note forder (CHOICE t) = n         by field_orders_element_order
        deg (mini n)
      = deg (minimal (CHOICE t))           by poly_mini_def
      = ordz (forder (CHOICE t)) (CARD B)  by poly_minimal_deg_eqn, CHOICE t IN R+
      = ordz n (CARD B)                    by above
*)
val poly_mini_deg = store_thm(
  "poly_mini_deg",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==> !n. n divides CARD R+ ==> (deg (mini n) = ordz n (CARD B))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = orders f* n` >>
  `t <> {}` by rw[GSYM finite_field_orders_nonempty_iff, Abbr`t`] >>
  `CHOICE t IN t` by rw[CHOICE_DEF] >>
  `forder (CHOICE t) = n` by metis_tac[field_orders_element_order] >>
  `CHOICE t IN R+` by metis_tac[field_orders_element_property] >>
  rw[poly_minimal_deg_eqn, poly_mini_def, Abbr`t`]);

(* Theorem: FiniteField r /\ s <<= r ==>
            !n. n divides CARD R+ ==> (mini n) pdivides (cyclo n) *)
(* Proof:
   Let t = orders f* n.
   Then t <> {}                       by finite_field_orders_nonempty_iff, n divides CARD R+
     so CHOICE t IN t                 by CHOICE_DEF
    and CHOICE t IN R+                by field_orders_element_property
   Note forder (CHOICE t) = n         by field_orders_element_order
   Thus minimal (CHOICE t) pdivides (cyclo n)   by poly_minimal_divides_cyclo_order
     or (mini n) pdivides (cyclo n)   by poly_mini_def
*)
val poly_mini_divides_poly_cyclo = store_thm(
  "poly_mini_divides_poly_cyclo",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !n. n divides CARD R+ ==> (mini n) pdivides (cyclo n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = orders f* n` >>
  `t <> {}` by rw[GSYM finite_field_orders_nonempty_iff, Abbr`t`] >>
  `CHOICE t IN t` by rw[CHOICE_DEF] >>
  `CHOICE t IN R+` by metis_tac[field_orders_element_property] >>
  `forder (CHOICE t) = n` by metis_tac[field_orders_element_order] >>
  metis_tac[poly_minimal_divides_cyclo_order, poly_mini_def]);

(* Theorem: FiniteField r /\ s <<= r ==>
            !n. n divides CARD R+ ==> (mini n) pdivides (unity n) *)
(* Proof:
   Let t = orders f* n.
   Then t <> {}                       by finite_field_orders_nonempty_iff, n divides CARD R+
     so CHOICE t IN t                 by CHOICE_DEF
    and CHOICE t IN R                 by field_orders_element
   Note forder (CHOICE t) = n         by field_orders_element_order
   Thus minimal (CHOICE t) pdivides (unity n)   by poly_minimal_divides_unity_order
     or (mini n) pdivides (unity n)   by poly_mini_def
*)
val poly_mini_divides_poly_unity = store_thm(
  "poly_mini_divides_poly_unity",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !n. n divides CARD R+ ==> (mini n) pdivides (unity n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = orders f* n` >>
  `t <> {}` by rw[GSYM finite_field_orders_nonempty_iff, Abbr`t`] >>
  `CHOICE t IN t` by rw[CHOICE_DEF] >>
  `CHOICE t IN R` by metis_tac[field_orders_element] >>
  `forder (CHOICE t) = n` by metis_tac[field_orders_element_order] >>
  metis_tac[poly_minimal_divides_unity_order, poly_mini_def]);

(* Theorem: FiniteField r /\ s <<= r ==>
            !n. n divides CARD R+ ==> !x. x IN R /\ root (mini n) x ==> (forder x = n) *)
(* Proof:
   Let t = orders f* n.
   Then t <> {}                       by finite_field_orders_nonempty_iff, n divides CARD R+
     so CHOICE t IN t                 by CHOICE_DEF
    and CHOICE t IN R                 by field_orders_element
   Note root (minimal (CHOICE t)) x   by poly_mini_def
        forder x
      = forder (CHOICE t)             by poly_minimal_root_order
      = n                             by field_orders_element_order
*)
val poly_mini_root_order = store_thm(
  "poly_mini_root_order",
  ``!(r s):'a field. FiniteField r /\ s <<= r ==>
   !n. n divides CARD R+ ==> !x. x IN R /\ root (mini n) x ==> (forder x = n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `t = orders f* n` >>
  `t <> {}` by rw[GSYM finite_field_orders_nonempty_iff, Abbr`t`] >>
  `CHOICE t IN t` by rw[CHOICE_DEF] >>
  `CHOICE t IN R` by metis_tac[field_orders_element] >>
  `forder (CHOICE t) = n` by metis_tac[field_orders_element_order] >>
  metis_tac[poly_minimal_root_order, poly_mini_def]);

(* ------------------------------------------------------------------------- *)
(* Another Cyclotomic Factorisation of Unity Polynomial                      *)
(* ------------------------------------------------------------------------- *)

(* Note: this is the original approach. *)

(*
poly_unity_eq_poly_cyclo_product;
|- !r. FiniteField r ==> !n. n divides CARD R+ ==> (unity n = PPIMAGE cyclo (divisors n))
*)

(*
> poly_unity_splitting_condition |> ISPEC ``t:'a field``;
val it = |- FiniteField t ==> !n. 0 < n ==> (poly_splits t (Unity t n) <=> n divides CARD (ring_nonzero t)): thm
*)

(* Theorem: FiniteField r /\ coprime n (CARD R) ==>
            ?(t st):'a poly field. FiniteField t /\ st <<= t /\ FieldIso up r st /\ poly_splits t (Unity t n) *)
(* Proof:
   Note 1 < CARD R                  by finite_field_card_gt_1
     so coprime n (CARD R)          by given
    ==> n <> 0                      by GCD_0, CARD R <> 1
     or 0 < n                       by NOT_ZERO_LT_ZERO

   Step 1: Get a field/subfield pair
   Let d = if n = 1 then 1 else ordz n (CARD R)
   Then 0 < d always,                           by ZN_coprime_order_alt when n <> 1
    ==> ?z. monic z /\ ipoly z /\ (deg z = d)   by poly_monic_irreducible_exists, 0 < d
    and pmonic z                                by poly_monic_irreducible_property

   Let t = PolyModRing r z, st = PolyModConst r z.
   Then FiniteField t                           by poly_mod_irreducible_finite_field
     so Field t                                 by finite_field_is_field
    and Field st                                by poly_mod_const_field
   also st <<= t                                by poly_mod_const_subfield_poly_mod

   Claim: n divides CARD (ring_nonzero t)
   Proof: If n = 1, true                        by ONE_DIVIDES_ALL
          If n <> 1, then 1 < n.
          Note (t <:> st) = deg z               by poly_mod_const_subfield_dim
           and CARD R = CARD st.carrier         by poly_mod_const_subfield_card
          Thus n divides CARD (ring_nonzero t)  by subfield_card_coprime_iff

   Step 2: apply poly_unity_splitting_condition
   Taking this t and st, this is to show:
   (1) FieldIso up r st, true                   by poly_mod_const_iso_field
   (2) poly_splits t (Unity t n), true          by poly_unity_splitting_condition, 0 < n, and claim.
*)
val poly_unity_splitting_field_exists = store_thm(
  "poly_unity_splitting_field_exists",
  ``!(r:'a field) n. FiniteField r /\ coprime n (CARD R) ==>
   ?(t st):'a poly field. FiniteField t /\ st <<= t /\ FieldIso up r st /\ poly_splits t (Unity t n)``,
  rpt (stripDup[FiniteField_def]) >>
  `0 < n` by
  (`1 < CARD R` by rw[finite_field_card_gt_1] >>
  `CARD R <> 1` by decide_tac >>
  `n <> 0` by metis_tac[GCD_0] >>
  decide_tac) >>
  qabbrev_tac `d = if n = 1 then 1 else ordz n (CARD R)` >>
  `0 < d` by rw[ZN_coprime_order_alt, Abbr`d`] >>
  `?z. monic z /\ ipoly z /\ (deg z = d)` by rw[poly_monic_irreducible_exists] >>
  `pmonic z` by rw[poly_monic_irreducible_property] >>
  qabbrev_tac `t = PolyModRing r z` >>
  qabbrev_tac `st = PolyModConst r z` >>
  `FiniteField t` by rw[poly_mod_irreducible_finite_field, Abbr`t`] >>
  `Field t` by rw[finite_field_is_field] >>
  `Field st` by rw[poly_mod_const_field, Abbr`st`] >>
  `st <<= t` by rw[poly_mod_const_subfield_poly_mod, Abbr`t`, Abbr`st`] >>
  `n divides CARD (ring_nonzero t)` by
    (Cases_on `n = 1` >-
  rw[] >>
  `1 < n` by decide_tac >>
  `(t <:> st) = deg z` by rw[poly_mod_const_subfield_dim, Abbr`t`, Abbr`st`] >>
  `CARD R = CARD st.carrier` by rw[poly_mod_const_subfield_card, Abbr`st`] >>
  metis_tac[subfield_card_coprime_iff]
  ) >>
  metis_tac[poly_unity_splitting_condition, poly_mod_const_iso_field]);

(* Theorem: FiniteField r /\ coprime n (CARD R) ==>
            ?f:num -> 'a poly. (f 0 = |1|) /\ (f 1 = X - |1|) /\ (!k. monic (f k)) /\
                      (deg (f n) = phi n) /\ (unity n = PPIMAGE f (divisors n)) *)
(* Proof:
   Note 1 < CARD R                  by finite_field_card_gt_1
     so coprime n (CARD R)          by given
    ==> n <> 0                      by GCD_0, CARD R <> 1
     or 0 < n                       by NOT_ZERO_LT_ZERO

   Note ?(t st):'a poly field. FiniteField t /\ st <<= t /\
         FieldIso up r st /\ poly_splits t (Unity t n)    by poly_unity_splitting_field_exists
     so FieldIso (LINV up R) st r   by field_iso_sym
    and st <= t                     by subfield_is_subring, st <<= t
     so n divides CARD (ring_nonzero t)     by poly_unity_splitting_condition, 0 < n

   Let f = LINV up R, g = poly_cyclo t
   Take f = (MAP (LINV up R)) o (poly_cyclo t), this is to show:
   (1) (MAP f o g) 0 = |1|
         (MAP f o g) 0
       = MAP f (MAP g 0)            by MAP_MAP_o
       = MAP f (poly_cyclo t 0)     by notation
       = MAP f (poly_one st)        by poly_cyclo_0, subring_poly_ids
       = |1|                        by field_iso_poly_one
   (2) (MAP f o g) 1 = X - |1|
         (MAP f o g) 1
       = MAP f (MAP g 1)            by MAP_MAP_o
       = MAP f (poly_cyclo t 1)     by notation
       = MAP f (Unity t 1)          by poly_cyclo_1, poly_unity_1
       = MAP f (Unity st 1)         by subring_poly_unity
       = unity 1                    by field_iso_poly_unity
       = X - |1|                    by poly_unity_1
   (3) !k. monic ((MAP f o g) k)
       Note Monic st (g k)          by poly_cyclo_spoly, poly_cyclo_monic, subring_poly_monic_iff
         so Poly st (g k)           by poly_monic_poly
       Since (MAP f o g) k = MAP f (g k)    by MAP_MAP_o
       Hence monic ((MAP f o g) k)          by field_iso_poly_monic_iff
   (4) !k. k divides n ==> deg ((MAP f o g) k) = phi k
       Note k divides (CARD (ring_nonzero t))   by DIVIDES_TRANS
         deg ((MAP f o g) k)
       = deg (MAP f (MAP g k))                  by MAP_MAP_o
       = Deg st (g k)                           by field_iso_poly_deg
       = Deg t (g k)                            by subring_poly_deg
       = phi k                                  by poly_cyclo_deg_eqn, k divides (CARD (ring_nonzero t))
   (5) unity n = PPIMAGE (MAP f o g) (divisors n)
       Let s = IMAGE g (divisors n).
       Then FINITE s                            by divisors_finite, IMAGE_FINITE
        and pset s                              by poly_cyclo_spoly, IN_IMAGE

         unity n
       = MAP f (Unity st n)                     by field_iso_poly_unity
       = MAP f (Unity t n)                      by subring_poly_unity
       = MAP f (poly_prod_set t s)              by poly_unity_eq_poly_cyclo_product
       = MAP f (poly_prod_set st s)             by subring_poly_prod_set
       = PPIMAGE (MAP f) s                      by field_iso_poly_prod_set
       = PPIMAGE (MAP f o g) (divisors n)       by IMAGE_COMPOSE, notation
*)
val poly_unity_cyclo_factor_exists = store_thm(
  "poly_unity_cyclo_factor_exists",
  ``!(r:'a field) n. FiniteField r /\ coprime n (CARD R) ==>
   ?f:num -> 'a poly. (f 0 = |1|) /\ (f 1 = X - |1|) /\ (!k. monic (f k)) /\
                      (!k. k divides n ==> (deg (f k) = phi k)) /\ (unity n = PPIMAGE f (divisors n))``,
  rpt (stripDup[FiniteField_def]) >>
  `0 < n` by
  (`1 < CARD R` by rw[finite_field_card_gt_1] >>
  `CARD R <> 1` by decide_tac >>
  `n <> 0` by metis_tac[GCD_0] >>
  decide_tac) >>
  `?(t st):'a poly field. FiniteField t /\ st <<= t /\
         FieldIso up r st /\ poly_splits t (Unity t n)` by rw[poly_unity_splitting_field_exists] >>
  `FieldIso (LINV up R) st r` by rw[field_iso_sym] >>
  `st <= t` by rw[subfield_is_subring] >>
  `n divides CARD (ring_nonzero t)` by metis_tac[poly_unity_splitting_condition] >>
  qabbrev_tac `f = LINV up R` >>
  qabbrev_tac `g = poly_cyclo t` >>
  qexists_tac `(MAP f) o g` >>
  rpt strip_tac >| [
    `(MAP f o g) 0 = MAP f (poly_cyclo t 0)` by rw[Abbr`g`] >>
    `_ = MAP f (poly_one st)` by metis_tac[poly_cyclo_0, subring_poly_ids] >>
    `_ = |1|` by rw[field_iso_poly_one] >>
    rw[],
    `(MAP f o g) 1 = MAP f (poly_cyclo t 1)` by rw[Abbr`g`] >>
    `_ = MAP f (Unity t 1)` by metis_tac[poly_cyclo_1, poly_unity_1] >>
    `_ = MAP f (Unity st 1)` by metis_tac[subring_poly_unity] >>
    `_ = unity 1` by rw[field_iso_poly_unity] >>
    rw[poly_unity_1],
    `Monic st (g k)` by metis_tac[poly_cyclo_spoly, poly_cyclo_monic, subring_poly_monic_iff] >>
    `Poly st (g k)` by rw[] >>
    `(MAP f o g) k = MAP f (g k)` by rw[] >>
    metis_tac[field_iso_poly_monic_iff],
    `k divides (CARD (ring_nonzero t))` by metis_tac[DIVIDES_TRANS] >>
    `Deg st (g k) = Deg t (g k)` by rw[subring_poly_deg] >>
    `_ = phi k` by rw[poly_cyclo_deg_eqn, Abbr`g`] >>
    `(MAP f o g) k = MAP f (g k)` by rw[] >>
    metis_tac[field_iso_poly_deg],
    qabbrev_tac `s = IMAGE g (divisors n)` >>
    `FINITE s` by rw[divisors_finite, Abbr`s`] >>
    `poly_set st s` by metis_tac[poly_cyclo_spoly, IN_IMAGE] >>
    `unity n = MAP f (Unity st n)` by rw[field_iso_poly_unity, Abbr`f`] >>
    `_ = MAP f (Unity t n)` by metis_tac[subring_poly_unity] >>
    `_ = MAP f (poly_prod_set t s)` by rw[poly_unity_eq_poly_cyclo_product] >>
    `_ = MAP f (poly_prod_set st s)` by metis_tac[subring_poly_prod_set] >>
    `_ = PPIMAGE (MAP f) s` by rw[field_iso_poly_prod_set] >>
    `_ = PPIMAGE (MAP f o g) (divisors n)` by rw[IMAGE_COMPOSE, Abbr`s`] >>
    rw[]
  ]);

(* This is a major theorem *)

(* Apply Skolemization *)
val lemma = prove(
  ``!(r:'a field) n. ?f:num -> 'a poly. FiniteField r /\ coprime n (CARD R) ==>
    (f 0 = |1|) /\ (f 1 = X - |1|) /\ (!k. monic (f k)) /\
    (!k. k divides n ==> (deg (f k) = phi k)) /\ (unity n = PPIMAGE f (divisors n))``,
  metis_tac[poly_unity_cyclo_factor_exists]);
(* Define cyclotomic polynomial *)
(*
- SIMP_RULE bool_ss [SKOLEM_THM] lemma;
val it = |- ?f. !r n. FiniteField r /\ coprime n (CARD R) ==>
       (f r n 0 = |1|) /\ (f r n 1 = X - |1|) /\
       (!k. monic (f r n k)) /\ (!k. k divides n ==> (deg (f r n k) = phi k)) /\
       (unity n = PPIMAGE (f r n) (divisors n)): thm
*)
val poly_PHI_def = new_specification(
    "poly_PHI_def",
    ["poly_PHI"],
    SIMP_RULE bool_ss [SKOLEM_THM] lemma);
(*
> val poly_PHI_def =
   |- !r n. FiniteField r /\ coprime n (CARD R) ==>
     (poly_PHI r n 0 = |1|) /\ (poly_PHI r n 1 = X - |1|) /\
     (!k. monic (poly_PHI r n k)) /\ (!k. k divides n ==> (deg (poly_PHI r n k) = phi k)) /\
     (unity n = PPIMAGE (poly_PHI r n) (divisors n)): thm
*)

(* overload poly_PHI r n *)
val _ = overload_on("PHI", ``poly_PHI (r:'a field) (n:num)``);
(*
> poly_PHI_def;
val it = |- !r n. FiniteField r /\ coprime n (CARD R) ==>
     (PHI 0 = |1|) /\ (PHI 1 = X - |1|) /\ (!k. monic (PHI k)) /\
     (!k. k divides n ==> (deg (PHI k) = phi k)) /\ (unity n = PPIMAGE PHI (divisors n)): thm
*)

(* Theorem: FiniteField r /\ coprime n (CARD R) ==> (PHI 0 = |1|) *)
(* Proof: by poly_PHI_def *)
val poly_PHI_0 = store_thm(
  "poly_PHI_0",
  ``!r:'a field. !n. FiniteField r /\ coprime n (CARD R) ==> (PHI 0 = |1|)``,
  rw[poly_PHI_def]);

(* Theorem: FiniteField r /\ coprime n (CARD R) ==> (PHI 1 = X - |1|) *)
(* Proof: by poly_PHI_def *)
val poly_PHI_1 = store_thm(
  "poly_PHI_1",
  ``!r:'a field. !n. FiniteField r /\ coprime n (CARD R) ==> (PHI 1 = X - |1|)``,
  rw[poly_PHI_def]);

(* Theorem: FiniteField r /\ coprime n (CARD R) ==> !k. poly (PHI k) *)
(* Proof: by poly_PHI_def, poly_monic_poly *)
val poly_PHI_poly = store_thm(
  "poly_PHI_poly",
  ``!r:'a field. !n. FiniteField r /\ coprime n (CARD R) ==> !k. poly (PHI k)``,
  rw[poly_PHI_def]);

(* Theorem: FiniteField r /\ coprime n (CARD R) ==> !k. monic (PHI k) *)
(* Proof: by poly_PHI_def *)
val poly_PHI_monic = store_thm(
  "poly_PHI_monic",
  ``!r:'a field. !n. FiniteField r /\ coprime n (CARD R) ==> !k. monic (PHI k)``,
  rw[poly_PHI_def]);

(* Theorem: FiniteField r /\ coprime n (CARD R) ==> !k. k divides n ==> (deg (PHI k) = phi k) *)
(* Proof: by poly_PHI_def *)
val poly_PHI_deg = store_thm(
  "poly_PHI_deg",
  ``!r:'a field. !n. FiniteField r /\ coprime n (CARD R) ==> !k. k divides n ==> (deg (PHI k) = phi k)``,
  rw[poly_PHI_def]);

(* Theorem: FiniteField r /\ coprime n (CARD R) ==> (unity n = PPIMAGE PHI (divisors n)) *)
(* Proof: by poly_PHI_def *)
val poly_unity_eq_poly_PHI_product = store_thm(
  "poly_unity_eq_poly_PHI_product",
  ``!r:'a field. !n. FiniteField r /\ coprime n (CARD R) ==> (unity n = PPIMAGE PHI (divisors n))``,
  rw[poly_PHI_def]);

(* Compare this result with:
poly_unity_eq_poly_cyclo_product;
|- !r. FiniteField r ==> !n. n divides CARD R+ ==> (unity n = PPIMAGE cyclo (divisors n))
*)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
