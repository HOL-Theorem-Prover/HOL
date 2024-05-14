(* ------------------------------------------------------------------------- *)
(* Finite Field: Existence and Uniqueness                                    *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ffExist";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open arithmeticTheory pred_setTheory listTheory numberTheory dividesTheory
     combinatoricsTheory gcdTheory gcdsetTheory primeTheory cardinalTheory;

open ffBasicTheory;
open ffAdvancedTheory;
open ffPolyTheory;
open ffUnityTheory;
open ffCycloTheory;
open ffMinimalTheory;
open ffMasterTheory;
open ffConjugateTheory;

open monoidTheory groupTheory ringTheory fieldTheory;
open fieldOrderTheory;
open fieldInstancesTheory;

(* Get polynomial theory of Ring *)
open polynomialTheory polyWeakTheory polyRingTheory polyDivisionTheory polyBinomialTheory;
open polyMonicTheory polyEvalTheory;
open polyDividesTheory;
open polyMonicTheory;
open polyRootTheory;

open polyFieldTheory;
open polyFieldDivisionTheory;
open polyFieldModuloTheory;
open polyRingModuloTheory;
open polyModuloRingTheory;

open polyMapTheory;
open fieldMapTheory;

open polyGCDTheory;
open polyIrreducibleTheory;
open polyProductTheory;

open fieldBinomialTheory;

val _ = intLib.deprecate_int ();

(* ------------------------------------------------------------------------- *)
(* Finite Field Existence and Uniqueness Documentation                       *)
(* ------------------------------------------------------------------------- *)
(* Overload:
   r =| (s,f,s_) |= r_   = FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) /\
                           s <<= r /\ s_ <<= r_ /\ FieldIso f s s_
   minimal_          = poly_minimal (r_:'b field) (s_:'b field)
   Trinity r a b c   = X ** a + X ** b - X ** c
   trinity           = Trinity r
   trinity_          = Trinity (r_:'b ring)

   im f x            = field_iso_map r s r_ s_ f x
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:
   A_LIST_BIJ_A      |- INFINITE univ(:'a) ==> ?f. BIJ f univ(:'a poly) univ(:'a)
   A_LIST_INJ_A      |- INFINITE univ(:'a) ==> ?f. INJ f univ(:'a poly) univ(:'a)
   NUM_LIST_INJ_A    |- INFINITE univ(:'a) ==> ?f. INJ f univ(:num poly) univ(:'a)
   finite_set_exists |- !n. INFINITE univ(:'a) ==> ?s. FINITE s /\ (CARD s = n)

   Finite Field Cardinality:
   finite_field_card_eq_prime_power      |- !r. FiniteField r ==> ?p n. prime p /\ 0 < n /\ (CARD R = p ** n)

   Existence of Finite Field:
   poly_monic_irreducible_exists         |- !r. FiniteField r ==>
                                            !n. 0 < n ==> ?p. monic p /\ ipoly p /\ (deg p = n)
   finite_field_exists_condition         |- !r. FiniteField r ==>
                                            !n. 0 < n ==> ?s. FiniteField s /\ (CARD s.carrier = CARD R ** n)
   finite_field_card_prime_power_exists  |- !p n. prime p /\ 0 < n ==> ?r. FiniteField r /\ (CARD r.carrier = p ** n)

   Existence of Finite Field for infinite type:
   finite_field_by_inj_map      |- !r f. Field r /\ INJ f R univ(:'b) ==> ?r_. Field r_ /\ FieldIso f r r_
   finite_field_existence       |- !p n. prime p /\ 0 < n /\ INFINITE univ(:'a) ==>
                                   ?r. FiniteField r /\ (CARD R = p ** n)
   finite_field_existence_iff   |- INFINITE univ(:'a) ==> !q.
                                   (?p n. prime p /\ 0 < n /\ (q = p ** n)) <=> ?r. FiniteField r /\ (CARD R = q)
   poly_unity_eq_poly_prod_image_cyclo
                                |- !n. 0 < n /\ INFINITE univ(:'a) ==> ?r. unity n = PPIMAGE cyclo (divisors n)
   poly_unity_eq_poly_prod_image_cyclo_alt
                                |- !n. 0 < n /\ INFINITE univ(:'a) ==> ?r. unity n = PPROD {cyclo k | k IN divisors n}
   poly_unity_eq_poly_prod_image_cyclo_num
                                |- !n. 0 < n ==> ?r. Unity r n = poly_prod_set r {poly_cyclo r k | k IN divisors n}

   Correspondence between Finite Fields:

   Finite Field Mirror Element:
#  iso_subfields_def    |- !r s r_ s_ f. r =| (s,f,s_) |= r_ <=>
                           FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) /\
                           s <<= r /\ s_ <<= r_ /\ FieldIso f s s_
   finite_field_card_eq_subfield_iso_dim_eq |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> (r <:> s = r_ <:> s_)
   finite_field_element_mirror_exists
                        |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> !x. x IN R ==>
                           ?y. y IN R_ /\ (forder_ y = forder x) /\ (minimal_ y = MAP f (minimal x))
   finite_field_element_mirror_def
                        |- !r s r_ s_ f x. ?y. r =| (s,f,s_) |= r_ ==>
                           !x. x IN R ==> mirror f x IN R_ /\
                               (forder_ (mirror f x) = forder x) /\ (minimal_ (mirror f x) = MAP f (minimal x))
   finite_field_element_mirror_element
                        |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> !x. x IN R ==> mirror f x IN R_
   finite_field_element_mirror_order
                        |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> !x. x IN R ==> (forder_ (mirror f x) = forder x)
   finite_field_element_mirror_poly_minimal
                        |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> !x. x IN R ==>
                                         (minimal_ (mirror f x) = MAP f (minimal x))
   finite_field_element_mirror_zero    |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> (mirror f #0 = #0_)
   finite_field_element_mirror_one     |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> (mirror f #1 = #1_)
   finite_field_element_mirror_eq_zero |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==>
                                          !x. x IN R ==> ((mirror f x = #0_) <=> (x = #0))
   finite_field_element_mirror_eq_one  |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==>
                                          !x. x IN R ==> ((mirror f x = #1_) <=> (x = #1))
   finite_field_primitive_mirror_property  |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==>
                                mirror f (primitive r) IN R+_ /\ (forder_ (mirror f (primitive r)) = CARD R+_)
   finite_field_primitive_mirror           |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==>
                                              mirror f (primitive r) IN FPrimitives r_

   Trinity Polynomial:
   poly_trinity_poly  |- !r. Ring r ==> !a b c. poly (trinity a b c)
   poly_trinity_spoly |- !r s. s <= r ==> !a b c. Poly s (trinity a b c)
   poly_trinity_eval  |- !r. Ring r ==> !x. x IN R ==> !a b c. eval (trinity a b c) x = x ** a + x ** b - x ** c
   poly_trinity_root  |- !r. Ring r ==> !x. x IN R ==> !a b c. root (trinity a b c) x <=> (x ** a + x ** b = x ** c)
   subring_poly_trinity    |- !r s. s <= r ==> !a b c. Trinity s a b c = trinity a b c
   field_iso_poly_trinity  |- !r r_ f. (r === r_) f ==> !a b c. MAP f (trinity a b c) = trinity_ a b c

   Uniqueness of Finite Field:
   finite_field_isomorphic_GF_PF     |- !r. FiniteField r ==> GF (char r) =ff= PF r
   finite_field_isomorphic_ZN_PF     |- !r. FiniteField r ==> ZN (char r) =ff= PF r
   finite_field_isomorphic_GF_PF_alt |- !r. FiniteField r ==> PF r =ff= GF (char r)
   finite_field_isomorphic_ZN_PF_alt |- !r. FiniteField r ==> PF r =ff= ZN (char r)
   finite_field_prime_field_iso  |- !r r_. FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==>
                              FieldIso (##_ #1_ o LINV $## (GF (char r)).carrier) (PF r) (PF r_)
   finite_field_char_eq_prime_field_iso
                                 |- !r r_. FiniteField r /\ FiniteField r_ /\ (char r = char r_) ==>
                              FieldIso (##_ #1_ o LINV $## (ZN (char r)).carrier) (PF r) (PF r_):
   finite_field_prime_field_isomorphic
                         |- !r r_. FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==> PF r =ff= PF r_

   field_iso_map_def     |- !r s r_ s_ f x. im f x = if x = #0 then #0_ else mirror f (primitive r) **_ idx x
   field_iso_map_element |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> !x. x IN R ==> im f x IN R_
   field_iso_map_zero    |- !r s r_ s_ f. im f #0 = #0_
   field_iso_map_one     |- !r s r_ s_ f. FiniteField r ==> (im f #1 = #1_)
   field_iso_map_eq_zero |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> !x. x IN R ==> ((im f x = #0_) <=> (x = #0))
   field_iso_map_eq_one  |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> !x. x IN R ==> ((im f x = #1_) <=> (x = #1))
   field_iso_map_nonzero |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> !x. x IN R+ ==> im f x IN R+_
   field_iso_map_neg_one |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> (im f (-#1) = $-_ #1_)
   field_iso_map_mult    |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==>
                            !x y. x IN R /\ y IN R ==> (im f (x * y) = im f x *_ im f y)
   field_iso_map_neg     |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> !x. x IN R ==> (im f (-x) = $-_ (im f x))
   field_iso_map_add     |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==>
                            !x y. x IN R /\ y IN R ==> (im f (x + y) = im f x +_ im f y)
   field_iso_map_sub     |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==>
                            !x y. x IN R /\ y IN R ==> (im f (x - y) = im f x -_ im f y)
   field_iso_map_exp     |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==>
                            !x. x IN R ==> !n. im f (x ** n) = im f x **_ n
   field_iso_map_eq      |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==>
                            !x y. x IN R /\ y IN R /\ (im f x = im f y) ==> (x = y)
   field_iso_map_inj     |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> INJ (im f) R R_
   field_iso_map_surj    |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> SURJ (im f) R R_
   field_iso_map_bij     |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> BIJ (im f) R R_
   field_iso_map_monoid_homo  |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> MonoidHomo (im f) r.prod r_.prod
   field_iso_map_group_homo   |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> GroupHomo (im f) r.sum r_.sum
   field_iso_map_field_homo   |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> FieldHomo (im f) r r_
   field_iso_map_field_iso    |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> FieldIso (im f) r r_
   field_iso_map_spoly_root   |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> !p x. Poly s p /\ x IN R ==>
                                                  (root p x <=> root_ (MAP (im f) p) (im f x))

   finite_field_eq_card_iso   |- !r r_. FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==>
                FieldIso (field_iso_map r (PF r) r_ (PF r_) (##_ #1_ o LINV $## (GF (char r)).carrier)) r r_
   finite_field_eq_card_isomorphic
                              |- !r r_. FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==> r =ff= r_

   Useful Isomorphic Theorems:
   poly_mod_const_isomorphic_field    |- !r. Field r ==> !z. monic z /\ ipoly z ==> r =f= PolyModConst r z
   poly_mod_const_isomorphic_finite_field    |- !r. FiniteField r ==> !z. monic z /\ ipoly z ==>
                                                 r =ff= PolyModConst r z
   poly_mod_irreducible_eq_degree_iso |- !r. FiniteField r ==> !z h. monic z /\ ipoly z /\ monic h /\ ipoly h /\
                                            (deg z = deg h) ==> ?f. FieldIso f (PolyModRing r z) (PolyModRing r h)

   Classification of subfields of Finite Field:

   Finite Field Subfield Existence Criterion:
   finite_field_subfield_exists      |- !r. FiniteField r ==> !n. (CARD R = char r ** n) ==>
                                        !m. m divides n <=> ?s. s <<= r /\ (CARD B = char r ** m)
   finite_field_subfield_exists_alt  |- !r. FiniteField r ==>
                                        !n. n divides fdim r <=> ?s. s <<= r /\ (fdim s = n)
   finite_field_subfield_existence   |- !r. FiniteField r ==> !b n. (CARD R = b ** n) ==>
                                        !m. m divides n <=> ?s. s <<= r /\ (CARD B = b ** m)
   finite_field_subfield_exists_reverse
                                     |- !r n. FiniteField r /\ (CARD R = char r ** n) ==>
                                        !m. ?s. s <<= r /\ (CARD B = char r ** m) <=> m divides n
   finite_field_subfield_existence_reverse
                                     |- !r b n. FiniteField r /\ (CARD R = b ** n) ==>
                                        !m. ?s. s <<= r /\ (CARD B = b ** m) <=> m divides n

   Cloning Finite Field:
   finite_set_clone_exists    |- !s. INFINITE univ(:'b) ==> ?t. FINITE t /\ (CARD t = CARD s)
   clone_def                  |- !s. INFINITE univ(:'b) ==> FINITE (clone s) /\ (CARD (clone s) = CARD s)
   eqcard_bij_exists          |- !s t. FINITE s /\ FINITE t /\ (CARD s = CARD t) ==> ?f. BIJ f s t
   eqcard_bij_def             |- !s t. FINITE s /\ FINITE t /\ (CARD s = CARD t) ==> BIJ (eqcard_bij s t) s t
   finite_field_clone         |- !r. FiniteField r /\ INFINITE univ(:'b) ==>
                                     (let f = eqcard_bij R (clone R) in
                                      FiniteField (homo_field r f) /\ FieldIso f r (homo_field r f))
   finite_field_clone_exists  |- !r. FiniteField r /\ INFINITE univ(:'b) ==>
                                 ?r_ f. FiniteField r_ /\ FieldIso f r r_

   Bijective Images of Monoid and Ring:
   monoid_bij_image_def |- !f t g. monoid_bij_image f t g =
                                   <|carrier := IMAGE f G; op := (\x y. f (t x * t y)); id := f #e|>
   ring_bij_image_def   |- !f g r. ring_bij_image f g r =
                                   <|carrier := IMAGE f R;
                                         sum := monoid_bij_image f g r.sum;
                                        prod := monoid_bij_image f g r.prod
                                    |>
   monoid_bij_image_monoid  |- !g f t. Monoid g /\ (!x. f (t x) = x) /\ (!y. t (f y) = y) ==>
                                       Monoid (monoid_bij_image f t g)
   monoid_bij_image_group   |- !g f t. Group g /\ (!x. f (t x) = x) /\ (!y. t (f y) = y) ==>
                                       Group (monoid_bij_image f t g)
   monoid_bij_image_abelian_monoid |- !g f t. AbelianMonoid g /\ (!x. f (t x) = x) /\ (!y. t (f y) = y) ==>
                                              AbelianMonoid (monoid_bij_image f t g)
   monoid_bij_image_abelian_group  |- !g f t. AbelianGroup g /\ (!x. f (t x) = x) /\ (!y. t (f y) = y) ==>
                                              AbelianGroup (monoid_bij_image f t g)
   monoid_bij_image_with_excluding |- !r f g. Ring r /\ (!x. f (g x) = x) /\ (!y. g (f y) = y) ==>
     (monoid_bij_image f g f* = monoid_bij_image f g r.prod excluding (monoid_bij_image f g r.sum).id)
   ring_bij_image_ring        |- !r f g. Ring r /\ (!x. f (g x) = x) /\ (!y. g (f y) = y) ==>
                                         Ring (ring_bij_image f g r)
   ring_bij_image_field       |- !r f g. Field r /\ (!x. f (g x) = x) /\ (!y. g (f y) = y) ==>
                                         Field (ring_bij_image f g r)
   ring_bij_image_field_iso   |- !r f g. Field r /\ (!x. f (g x) = x) /\ (!y. g (f y) = y) ==>
                                         FieldIso f r (ring_bij_image f g r)
   field_exists_with_iso      |- univ(:'a) =~ univ(:'b) ==> !r. Field r ==>
                                         ?s f. Field s /\ FieldIso f r s

   Nonlinear Monic Irreducible factor of (unity n) with order X = n:
   poly_unity_special_factor_exists_0
                              |- !r. FiniteField r ==>
                                 !n. 0 < n /\ 1 < ordz n (CARD R) ==>
                                  ?h. mifactor h (unity n) /\ (deg h = ordz n (CARD R)) /\
                                      poly_roots (PolyModRing r h) (lift h) SUBSET
                                         orders ((PolyModRing r h).prod excluding |0|) n
   poly_unity_special_factor_exists
                              |- !r. FiniteField r ==>
                                 !n. 0 < n /\ 1 < ordz n (CARD R) ==>
                                 ?h. mifactor h (unity n) /\ (deg h = ordz n (CARD R)) /\
                                     (order ((PolyModRing r h).prod excluding |0|) X = n)
   poly_unity_special_factor_exists_1
                              |- !r k. FiniteField r /\ 0 < k /\ 1 < ordz k (CARD R) ==>
                                 ?z. mifactor z (unity k) /\ (deg z = ordz k (CARD R)) /\ (forderz X = k)
   poly_unity_special_factor_exists_alt
                              |- !r k. FiniteField r /\ 0 < k /\ 1 < ordz k (CARD R) ==>
                                   ?z. monic z /\ ipoly z /\ z pdivides unity k /\
                                       (deg z = ordz k (CARD R)) /\ (forderz X = k)
*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Note: These theorems require cardinalTheory. *)
(* Note: helperSet is basic, no cardinalTheory. *)

(* Theorem: INFINITE univ(:'a) ==> ?f. BIJ f univ(:'a list) univ(:'a) *)
(* Proof:
   Note univ(:'a poly) = list univ(:'a)           by UNIV_list
    and list univ(:'a) =~ univ(:'a)               by INFINITE_A_list_BIJ_A (same cardinality)
    ==> ?f. BIJ f (list univ(:'a)) univ(:'a)      by cardeq_def
*)
val A_LIST_BIJ_A = store_thm(
  "A_LIST_BIJ_A",
  ``INFINITE univ(:'a) ==> ?f. BIJ f univ(:'a list) univ(:'a)``,
  metis_tac[UNIV_list, INFINITE_A_list_BIJ_A, cardeq_def]);

(* Theorem: INFINITE univ(:'a) ==> ?f. INJ f univ(:'a list) univ(:'a) *)
(* Proof:
   Note ?f. BIJ f (list univ(:'a)) univ(:'a)      by A_LIST_BIJ_A
     or     INJ f (list univ(:'a)) univ(:'a)      by BIJ_DEF
*)
val A_LIST_INJ_A = store_thm(
  "A_LIST_INJ_A",
  ``INFINITE univ(:'a) ==> ?f. INJ f univ(:'a list) univ(:'a)``,
  metis_tac[A_LIST_BIJ_A, BIJ_DEF]);

(* Theorem: INFINITE univ(:'a)  ==> ?f. INJ f univ(:num list) univ(:'a) *)
(* Proof:
   Note INFINITE univ(:num)                       by INFINITE_NUM_UNIV
     so list univ(:num) =~ univ(:num)             by INFINITE_A_list_BIJ_A (same cardinality)
    Now univ(:'num poly) = list univ(:'num)       by UNIV_list
    ==> ?f. INJ f univ(:num) univ(:'a)            by infinite_num_inj, INFINITE univ(:'a)
    ==> ?g. BIJ g (list univ(:num)) univ(:num)    by cardeq_def
     or     INJ g (list univ(:num)) univ(:num)    by BIJ_DEF
    then INJ (g o f) (list univ(:num)) univ(:'a)  by INJ_COMPOSE
    Take g o f for the result.
*)
val NUM_LIST_INJ_A = store_thm(
  "NUM_LIST_INJ_A",
  ``INFINITE univ(:'a)  ==> ?f. INJ f univ(:num list) univ(:'a)``,
  strip_tac >>
  `list univ(:num) =~ univ(:num)` by metis_tac[INFINITE_A_list_BIJ_A, INFINITE_NUM_UNIV] >>
  rw[UNIV_list] >>
  `?f. INJ f univ(:num) univ(:'a)` by rw[GSYM infinite_num_inj] >>
  `?g. INJ g (list univ(:num)) univ(:num)` by metis_tac[cardeq_def, BIJ_DEF] >>
  metis_tac[INJ_COMPOSE]);

(* Theorem: INFINITE univ(:'a) ==> ?s:'a -> bool. FINITE s /\ (CARD s = n) *)
(* Proof:
    Note INFINITE univ(:'a)
     ==> ?f. INJ f univ(:num) univ(:'a)   by infinite_num_inj
    Take s = IMAGE f (count n).
    Note INJ f (count n) univ(:'a)        by INJ_SUBSET_UNIV
     and FINITE (count n)                 by FINITE_COUNT
     Now FINITE s                         by IMAGE_FINITE
         CARD s
       = CARD (IMAGE f (count n))         by notation
       = CARD (count n)                   by INJ_CARD_IMAGE_EQN, INJ f (count n) univ(:'a)
       = n                                by CARD_COUNT
*)
val finite_set_exists = store_thm(
  "finite_set_exists",
  ``!n. INFINITE univ(:'a) ==> ?s:'a -> bool. FINITE s /\ (CARD s = n)``,
  rpt strip_tac >>
  `?f. INJ f univ(:num) univ(:'a)` by rw[GSYM infinite_num_inj] >>
  qexists_tac `IMAGE f (count n)` >>
  `INJ f (count n) univ(:'a)` by rw[INJ_SUBSET_UNIV] >>
  rw[INJ_CARD_IMAGE_EQN]);

(* ------------------------------------------------------------------------- *)
(* Finite Field Cardinality                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==> ?p n. prime p /\ 0 < n /\ (CARD R = p ** n) *)
(* Proof:
   Note ?d. 0 < d /\ (CARD R = char r ** d)    by finite_field_card
    and prime (char r)                         by finite_field_char
   Thus take p = char r, n = d, and the result follows.
*)
val finite_field_card_eq_prime_power = store_thm(
  "finite_field_card_eq_prime_power",
  ``!r:'a field. FiniteField r ==> ?p n. prime p /\ 0 < n /\ (CARD R = p ** n)``,
  metis_tac[finite_field_card, finite_field_char]);

(* This simple result raises two questions:
   1. Is there some finite fields for each prime p and 0 < n?      This is existence.
   2. How many finite fields are there for each prime p and 0 < n? This is uniqueness.
*)

(* ------------------------------------------------------------------------- *)
(* Existence of Finite Field                                                 *)
(* ------------------------------------------------------------------------- *)

(* The existence of Finite Field depends on the following:

(1) There exists finite fields of cardinality a prime p.
ZN_field  |- !p. prime p ==> Field (ZN p)
ZN_card   |- !n. CARD (ZN n).carrier = n
GF_field  |- !p. prime p ==> Field (GF p)
GF_card   |- !n. CARD (GF n).carrier = n

(2) Given a FiniteField r, we can construct a quotient field (PolyModRing r z)
using an irreducible z in (PolyRing r), with cardinality (CARD R) ** (deg z).
poly_mod_irreducible_finite_field
|- !r. FiniteField r ==> !p. monic p /\ ipoly p ==> FiniteField (PolyModRing r p)
poly_mod_irreducible_field_card
|- !r. FiniteField r ==> !p. monic p /\ ipoly p ==> (CARD (PolyModRing r p).carrier = CARD R ** deg p)

(3) The number of subfield monic irreducible polynomials with degrees dividing dimension is implicitly counted,
giving implicitly the number of monic irreducibles in (PolyRing r) of any FiniteField r:
finite_subfield_card_exp_eqn
|- !r. FiniteField r ==> !s. s <<= r ==>
   !n. 0 < n ==> (CARD B ** n = SIGMA (\d. d * monic_irreducibles_count s d) (divisors n))
finite_field_card_exp_eqn (putting s = r in finite_subfield_card_exp_eqn)
|- !r. FiniteField r ==> !n. 0 < n ==> (CARD R ** n = SIGMA (\d. d * monic_irreducibles_count r d) (divisors n))

(4) The implicit relationship is enough to give the existence of monic irreducible of any degree,
thereby giving the existence of FiniteField r whenever CARD R = prime power:
poly_monic_irreducible_exists
|- !r. FiniteField r ==> !n. 0 < n ==> ?p. monic p /\ ipoly p /\ (deg p = n)
finite_field_exists_condition
|- !r. FiniteField r ==> !n. 0 < n ==> ?s. FiniteField s /\ (CARD s.carrier = CARD R ** n)

(5) Together with (1), this gives the existence of GF(p ** n), for every prime p and 0 < n.
finite_field_card_prime_power_exists
|- !p. prime p ==> !n. 0 < n ==> ?r. FiniteField r /\ (CARD r.carrier = p ** n)

However, this is FiniteField (r:num poly). To make a FiniteField (r:'a), we would need an infinite type:
INFINITE univ(:'a), which has the same cardinality as univ(:num poly), giving an injection:
NUM_LIST_INJ_A |- INFINITE univ(:'a) ==> ?f. INJ f univ(:num poly) univ(:'a)

This injection can be used to translate the FiniteField (r:num poly) to FiniteField (r:'a) via:
ring_inj_image_def  |- !r f. ring_inj_image r f =
     <|carrier := IMAGE f R;
           sum := <|carrier := IMAGE f R; op := (\x y. f (LINV f R x + LINV f R y)); id := f #0|>;
          prod := <|carrier := IMAGE f R; op := (\x y. f (LINV f R x * LINV f R y)); id := f #1|>
      |>

This gives finally:
finite_field_by_inj_map |- !r f. Field r /\ INJ f R univ(:'b) ==> ?r_. Field r_ /\ FieldIso f r r_
finite_field_existence  |- !p n. prime p /\ 0 < n /\ INFINITE univ(:'a) ==> ?r. FiniteField r /\ (CARD R = p ** n)

*)

(* Theorem: FiniteField r ==> !n. 0 < n ==> ?p. monic p /\ ipoly p /\ (deg p = n) *)
(* Proof:
   Let f = monic_irreducibles_count r, p = CARD R
   Since FieldField r
     ==> 1 < p                                            by finite_field_card_gt_1
     ==> !n. 0 < n ==>
         (p ** n = SIGMA (\d. d * f d) (divisors n))      by finite_field_card_exp_eqn
    With 0 < n,
     ==> (p ** (n DIV 2) - 2) * p ** (n DIV 2) < n * f n  by sigma_eq_perfect_power_bounds_2
      or n * f n <> 0
   Since n <> 0, f n <> 0                                 by MULT_EQ_0
     Now f n = CARD (monic_irreducibles_degree r n)       by monic_irreducibles_count_def
    Note FINITE (monic_irreducibles_count r n)            by monic_irreducibles_degree_finite
      so (monic_irreducibles_count r n) <> {}             by CARD_EQ_0
      or ?x. x IN (monic_irreducibles_count r n)          by MEMBER_NOT_EMPTY
      or ?x. monic x /\ ipoly x /\ (deg x = n)            by monic_irreducibles_degree_member
   Hence take this x as p.
*)
val poly_monic_irreducible_exists = store_thm(
  "poly_monic_irreducible_exists",
  ``!r:'a field. FiniteField r ==> !n. 0 < n ==> ?p. monic p /\ ipoly p /\ (deg p = n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `p = CARD R` >>
  qabbrev_tac `f = monic_irreducibles_count r` >>
  `1 < p` by rw[finite_field_card_gt_1, Abbr`p`] >>
  `!n. 0 < n ==> (p ** n = SIGMA (\d. d * f d) (divisors n))` by rw[finite_field_card_exp_eqn, Abbr`p`, Abbr`f`] >>
  `(p ** (n DIV 2) - 2) * p ** (n DIV 2) < n * f n` by metis_tac[sigma_eq_perfect_power_bounds_2] >>
  `n <> 0 /\ n * f n <> 0` by decide_tac >>
  qabbrev_tac `s = monic_irreducibles_degree r n` >>
  `f n = CARD s` by rw[monic_irreducibles_count_def, Abbr`f`] >>
  `FINITE s` by rw[monic_irreducibles_degree_finite, Abbr`s`] >>
  `s <> {}` by metis_tac[CARD_EQ_0, MULT_EQ_0] >>
  `?x. x IN s` by rw[MEMBER_NOT_EMPTY] >>
  metis_tac[monic_irreducibles_degree_member]);

(* poly_monic_irreducible_exists:
   This proof depends on counting the number of monic irreducibles.
   Compare this proof with the more elementary one in ffMaster (poly_monic_irreducible_exists_alt)
   which is based on the fact that the master polynomial is the product of all monic irreducibles.
*)

(* Theorem: FiniteField r ==>
            !n. 0 < n ==> ?s:'a poly field. FiniteField s /\ (CARD s.carrier = CARD R ** n) *)
(* Proof:
   Since FiniteField r
     ==> ?p. monic p /\ ipoly p /\ (deg p = n)               by poly_monic_irreducible_exists
    With monic p /\ ipoly p
     ==> FiniteField (PolyModRing r p)                       by poly_mod_irreducible_finite_field
     and CARD (PolyModRing r p).carrier = CARD R ** deg p    by poly_mod_irreducible_field_card
    Just take s = (PolyModRing r p).
*)
val finite_field_exists_condition = store_thm(
  "finite_field_exists_condition",
  ``!r:'a field. FiniteField r ==>
   !n. 0 < n ==> ?s:'a poly field. FiniteField s /\ (CARD s.carrier = CARD R ** n)``,
  metis_tac[poly_monic_irreducible_exists,
             poly_mod_irreducible_finite_field, poly_mod_irreducible_field_card]);

(* Theorem: prime p /\ 0 < n ==> ?r:num poly field. FiniteField r /\ (CARD r.carrier = p ** n) *)
(* Proof:
   Since prime p
     ==> FiniteField (GF p)                       by GF_finite_field
     and CARD (GF p).carrier = p                  by GF_card
   Hence ?s:num poly field. FiniteField s /\
         (CARD s.carrier = CARD r.carrier ** n)   by finite_field_exists_condition
*)
val finite_field_card_prime_power_exists = store_thm(
  "finite_field_card_prime_power_exists",
  ``!p n. prime p /\ 0 < n ==> ?r:num poly field. FiniteField r /\ (CARD r.carrier = p ** n)``,
  rpt strip_tac >>
  `FiniteField (GF p)` by rw[GF_finite_field] >>
  `CARD (GF p).carrier = p` by rw[GF_card] >>
  metis_tac[finite_field_exists_condition]);

(* This is a milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Existence of Finite Field for infinite type                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r /\ INJ f R univ(:'b) ==> ?r_:'b field. Field r_ /\ FieldIso f r r_ *)
(* Proof:
   Let r_ = ring_inj_image r f.
   Then Field r_          by field_inj_image_field
   For the remaining goal: FieldIso f r r_
    and by FieldIso_def, this is to show:
   (1) FieldHomo f r (ring_inj_image r f), true         by ring_inj_image_ring_homo, FieldHomo_def
   (2) BIJ f R (ring_inj_image r f).carrier
       Since (ring_inj_image r f).carrier = IMAGE f R   by ring_inj_image_def
          so BIJ f R (IMAGE f R)                        by INJ_IMAGE_BIJ_ALT
*)
val finite_field_by_inj_map = store_thm(
  "finite_field_by_inj_map",
  ``!(r:'a field) f. Field r /\ INJ f R univ(:'b) ==> ?r_:'b field. Field r_ /\ FieldIso f r r_``,
  rpt strip_tac >>
  qexists_tac `ring_inj_image r f` >>
  rw[field_inj_image_field] >>
  rw[FieldIso_def] >-
  rw[FieldHomo_def, ring_inj_image_ring_homo] >>
  rw[ring_inj_image_def, INJ_IMAGE_BIJ_ALT]);

(* Theorem: prime p /\ 0 < n /\ INFINITE univ(:'a) ==> ?r:'a field. FiniteField r /\ (CARD R = p ** n) *)
(* Proof:
   Given prime p /\ 0 < n,
     ==> ?nr. FiniteField nr /\ (CARD nr.carrier = p ** n)   by finite_field_card_prime_power_exists
     ==> Field nr /\ FINITE nr.carrier                       by FiniteField_def
     Now ?f. INJ f univ(:num poly) univ(:'a)                 by NUM_LIST_INJ_A
     and (nr.carrier) SUBSET univ(:num poly)                 by SUBSET_UNIV
     ==> INJ f (nr.carrier) univ(:'a)                        by INJ_SUBSET, SUBSET_REFL
    Thus ?r:'a field. Field r /\ FieldIso f nr r             by finite_field_by_inj_map
     and BIJ f nr.carrier R                                  by FieldIso_def
   Hence FINITE R                                            by BIJ_FINITE, FINITE nr.carrier
   Take this r,
    then FiniteField r due to Field r /\ FINITE R            by FiniteField_def
     and CARD R = CARD nr.carrier = p ** n                   by FINITE_BIJ_CARD_EQ
*)
val finite_field_existence = store_thm(
  "finite_field_existence",
  ``!p n. prime p /\ 0 < n /\ INFINITE univ(:'a) ==> ?r:'a field. FiniteField r /\ (CARD R = p ** n)``,
  rpt strip_tac >>
  `?nr:num poly field. FiniteField nr /\ (CARD nr.carrier = p ** n)` by rw[finite_field_card_prime_power_exists] >>
  `Field nr /\ FINITE nr.carrier` by metis_tac[FiniteField_def] >>
  `?f. INJ f univ(:num poly) univ(:'a)` by rw[NUM_LIST_INJ_A] >>
  `INJ f (nr.carrier) univ(:'a)` by metis_tac[INJ_SUBSET, SUBSET_UNIV, SUBSET_REFL] >>
  `?r:'a field. Field r /\ FieldIso f nr r` by rw[finite_field_by_inj_map] >>
  `BIJ f nr.carrier R` by metis_tac[FieldIso_def] >>
  `FINITE R` by metis_tac[BIJ_FINITE] >>
  metis_tac[FiniteField_def, FINITE_BIJ_CARD_EQ]);

(* Theorem: INFINITE univ(:'a) ==>
            !q. (?p n. prime p /\ 0 < n /\ (q = p ** n)) <=> (?r:'a field. FiniteField r /\ (CARD R = q)) *)
(* Proof:
   If part: prime p /\ 0 < n ==> ?r. FiniteField r /\ (CARD R = p ** n)
      This true                  by finite_field_existence
   Only-if part: FiniteField r ==> ?p n. prime p /\ 0 < n /\ (CARD R = p ** n)
      Note ?d. 0 < d /\ (CARD R = char r ** d)     by finite_field_card
       and prime (char r)                          by finite_field_char
      Take p = char r, n = d.
*)
val finite_field_existence_iff = store_thm(
  "finite_field_existence_iff",
  ``INFINITE univ(:'a) ==>
   !q. (?p n. prime p /\ 0 < n /\ (q = p ** n)) <=> (?r:'a field. FiniteField r /\ (CARD R = q))``,
  metis_tac[finite_field_existence, finite_field_card, finite_field_char]);

(* Theorem: 0 < n /\ INFINITE univ(:'a) ==> ?r:'a field. unity n = PPIMAGE cyclo (divisors n) *)
(* Proof:
   Note ?p. prime p /\ n < p       by prime_always_bigger
    and coprime p n                by prime_coprime_all_less, n <= n
     or coprime n p                by coprime_sym
    ==> 0 < ordz n p               by ZN_order_nonzero
   Let d = ordz n p.
   Then ?r:'a field. FiniteField r /\
              (CARD R = p ** d)         by finite_field_existence, 0 < p
   Note prime (char r)                  by finite_field_char
    and CARD R = (char r) ** (fdim r)   by finite_field_card_alt
    ==> (p = char r) /\ (d = fdim r)    by metis_tac[prime_powers_eq]);

   Let s = PF r.
   Then s <<= r /\ (CARD B = p)                by prime_field_subfield_property
    ==> n divides CARD R+                      by subfield_card_coprime_iff
   Take this FiniteField r,
   Then unity n = PPIMAGE cyclo (divisors n)   by poly_unity_eq_poly_cyclo_product
*)
val poly_unity_eq_poly_prod_image_cyclo = store_thm(
  "poly_unity_eq_poly_prod_image_cyclo",
  ``!n. 0 < n /\ INFINITE univ(:'a) ==> ?r:'a field. unity n = PPIMAGE cyclo (divisors n)``,
  rpt strip_tac >>
  `?p. prime p /\ n < p` by rw[prime_always_bigger] >>
  `coprime n p` by metis_tac[prime_coprime_all_less, LESS_EQ_REFL, coprime_sym] >>
  `0 < ordz n p` by metis_tac[ZN_order_nonzero, NOT_ZERO_LT_ZERO] >>
  qabbrev_tac `d = ordz n p` >>
  `?r:'a field. FiniteField r /\ (CARD R = p ** d)` by rw[finite_field_existence] >>
  `prime (char r)` by rw[finite_field_char] >>
  `CARD R = (char r) ** (fdim r)` by rw[GSYM finite_field_card_alt] >>
  `(p = char r) /\ (d = fdim r)` by metis_tac[prime_powers_eq] >>
  qabbrev_tac `s = PF r` >>
  `s <<= r /\ (CARD B = p)` by rw[prime_field_subfield_property, Abbr`s`] >>
  `n divides CARD R+` by metis_tac[subfield_card_coprime_iff] >>
  metis_tac[poly_unity_eq_poly_cyclo_product]);

(* Theorem: 0 < n /\ INFINITE univ(:'a) ==> ?r:'a field. unity n = PPROD {cyclo k | k IN (divisors n)} *)
(* Proof: by poly_unity_eq_poly_prod_image_cyclo, EXTENSION *)
val poly_unity_eq_poly_prod_image_cyclo_alt = store_thm(
  "poly_unity_eq_poly_prod_image_cyclo_alt",
  ``!n. 0 < n /\ INFINITE univ(:'a) ==> ?r:'a field. unity n = PPROD {cyclo k | k IN (divisors n)}``,
  rpt strip_tac >>
  `?r:'a field. unity n = PPIMAGE cyclo (divisors n)` by metis_tac[poly_unity_eq_poly_prod_image_cyclo] >>
  `IMAGE cyclo (divisors n) = {cyclo k | k IN (divisors n)}` by rw[EXTENSION] >>
  metis_tac[]);

(* Theorem: 0 < n ==> ?r:num field. Unity r n = poly_prod_set r {poly_cyclo r k | k IN (divisors n)} *)
(* Proof: by INFINITE_NUM_UNIV, poly_unity_eq_poly_prod_image_cyclo_alt *)
val poly_unity_eq_poly_prod_image_cyclo_num = store_thm(
  "poly_unity_eq_poly_prod_image_cyclo_num",
  ``!n. 0 < n ==> ?r:num field. Unity r n = poly_prod_set r {poly_cyclo r k | k IN (divisors n)}``,
  metis_tac[INFINITE_NUM_UNIV, poly_unity_eq_poly_prod_image_cyclo_alt]);

(* ------------------------------------------------------------------------- *)
(* Correspondence between Finite Fields                                      *)
(* ------------------------------------------------------------------------- *)

(* Idea:
We have:
(1) poly_minimal_deg_eqn          |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R+ /\ x <> #1 ==>
                                          (deg (minimal x) = order (ZN (forder x)).prod (CARD B))
(2) poly_minimal_deg_divides_dim  |- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==>
                                          deg (minimal x) divides (r <:> s)
Since (CARD R = CARD B ** (r <:> s))  by finite_subfield_card_eqn
or ?n m. 0 < n /\ 0 < m /\ (CARD R = char r ** n) /\ (CARD B = char r ** m) /\ m divides n  by finite_field_subfield_card_property
Can these be applied to (1), showing deg (minimal x) divides (r <:> s) explicitly?
Seems not.

The current thinking is: given x IN R, we know (forder x), and in most cases,
deg (minimal x) = order (ZN (forder x)).prod (CARD B)

Now, given a monic irreducible subfield poly IPoly p with (deg p) divides (r <:> s), we have:
(3) poly_monic_irreducible_is_minimal_poly |- !r s. FiniteField r /\ s <<= r ==> !p. monic p /\ IPoly s p /\
                                                   deg p divides (r <:> s) ==> ?x. x IN R /\ (p = minimal x)
What can we say about (forder x) ?. We only know that all the possible x in (3) are conjugates,
since (roots (minimal x) = Conj x)  by poly_minimal_roots,
and (!y. y IN (Conj x) ==> forder y = forder x) by finite_field_conjugates_order
And we know      deg p = order (ZN (forder x)).prod (CARD B),
But how to solve for (forder x) from (deg p)?

Try:     (CARD B) ** (deg p) == 1 (MOD (forder x))
or       (CARD B) ** (deg p) = q * (forder x) + 1
so           (forder x) = ((CARD B) ** (deg p) - 1) DIV q, for some q making (deg p) smallest.

group_order_exp_cofactor
|- !g. FiniteGroup g ==> !n z. z IN G /\ n divides ord z ==> (ord (z ** (ord z DIV n)) = n)

field_iso_poly_ring_iso
|- !r s. Field r /\ Field s ==> !f. FieldIso f r s ==> RingIso (\p. MAP f p) (PolyRing r) (PolyRing s)

Actually, it may be hard to get (forder x) from (deg p), but there is one narrow gap to exploit.
(from Timothy Murphy - Finite Field, Course MA364D)

Let z be primitive of FiniteField r.
Then in zp = (PF r) it has mz = (poly_minimal r (PF r) z), and Poly (PF r) mz.
Map this polynomial mz to FiniteField s. Let's say it is Poly (PF s) my.
Then my, with (deg my = deg mz), will divide (<s:(PF s)>), just as (deg mz) divides (<r:(PF r)>).
Thus my will have a root y in FiniteField s.
Claim: order y = order z.
First, mz divides (master (CARD R)), or (unity (CARD R+)),so z is a root of (unity (CARD R+)).
So (order z) <= (CARD R+). In fact, z being a primitive, (order z = CARD R+).
Similarly, my divides (Master s (CARD s.carrier)), or (Unity s (CARD R+)), since CARD R = CARD s.carrier.
so y is a root of (Unity s (CARD R+)), thus (order y) <= (CARD R+).
Assume c = (order y) < (CARD R+). Then  (y ** c = |1|) on the s-side.
Since iso preserves multiplication, (z ** c = |1|) on the r-side.
So (order z) divides c < (CARD R+), which is impossible.
Thus c = (order y) = CARD R+, or y is also a primitive of FiniteField s.
*)

(* Overloads for polynomials of type 'b *)
val _ = overload_on("minimal_", ``poly_minimal (r_:'b field) (s_:'b field)``);
(* This cannot be moved to ffPoly, since poly_minimal is defined in ffMinimal. *)

(* ------------------------------------------------------------------------- *)
(* Finite Field Mirror Element                                               *)
(* ------------------------------------------------------------------------- *)

(* Overload on finite fields of same cardinality with isomorphic subfields *)
(* Special syntax for pairs of field/subfields with isomorphic subfields *)
val _ = add_rule {
   block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0)),
        fixity = Infix(NONASSOC, 450), (* same as relation *)
   paren_style = OnlyIfNecessary,
   pp_elements = [HardSpace 1, TOK "=|", HardSpace 1, TM, BreakSpace(1,2), TOK "|=", BreakSpace(1,2)],
     term_name = "iso_subfields"
};

(* Define  pairs of field/subfields with isomorphic subfields *)
val iso_subfields_def = Define`
  r =| (s,f,s_) |= r_ <=> FiniteField (r:'a field) /\ FiniteField (r_:'b field) /\
        (CARD R = CARD R_) /\ s <<= r /\ s_ <<= r_ /\ FieldIso f s s_
`;

(* export definition *)
val _ = export_rewrites ["iso_subfields_def"];

(* Theorem: r =| (s, f, s_) |= r_ ==> ((r <:> s) = (r_ <:> s_)) *)
(* Proof:
   Note CARD R = (CARD B) ** (r <:> s)       by finite_subfield_card_eqn
    and CARD R_ = (CARD S_) ** (r_ <:> s_)   by finite_subfield_card_eqn
   Also 1 < CARD B                           by finite_subfield_card_gt_1
    and FINITE B                             by subfield_finite_field, FiniteField_def
  Given FieldIso f s s_
    ==> CARD B = CARD S_                     by field_iso_card_eq
  Hence (r <:> s) = (r_ <:> s_)              by EXP_BASE_INJECTIVE, 1 < CARD B
*)
val finite_field_card_eq_subfield_iso_dim_eq = store_thm(
  "finite_field_card_eq_subfield_iso_dim_eq",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s, f, s_) |= r_ ==> ((r <:> s) = (r_ <:> s_))``,
  rw[] >>
  `CARD R = (CARD B) ** (r <:> s)` by rw[finite_subfield_card_eqn] >>
  `CARD R_ = (CARD S_) ** (r_ <:> s_)` by rw[finite_subfield_card_eqn] >>
  `FINITE B` by metis_tac[subfield_finite_field, FiniteField_def] >>
  metis_tac[field_iso_card_eq, finite_subfield_card_gt_1, EXP_BASE_INJECTIVE]);

(* Theorem: r =| (s,f,s_) |= r_ ==>
            !x. x IN R ==> ?y. y IN R_ /\ (forder_ y = forder x) /\ (minimal_ y = MAP f (minimal x)) *)
(* Proof:
   Let p = minimal x.
   Since Poly s p                    by poly_minimal_spoly
     ==> Poly s_ p_                  by field_iso_poly
    Also IPoly s p                   by poly_minimal_subfield_irreducible
     ==> IPoly s_ p_                 by field_iso_poly_irreducible
    Note monic p                     by poly_minimal_monic
     ==> Monic s p                   by subring_poly_monic_iff
     ==> Monic s_ p_                 by field_iso_poly_monic
     ==> monic_ p_                   by field_iso_poly_monic_iff
    Also (r <:> s) = (r_ <:> s_)     by finite_field_card_eq_subfield_iso_dim_eq
     and deg_ p_ = deg p             by field_iso_poly_deg
    Note (deg p) divides (r <:> s)   by poly_minimal_deg_divides_dim
      so (deg_ p_) divides (r_ <:> s_)
   Hence ?y. y IN R_ /\ (p_ = minimal_ y)    by poly_monic_irreducible_is_minimal_poly
   It remains to show: forder_ y = forder x.
   Let oy = forder_ y, ox = forder x.

   If y = #0_,
      Then oy = 0                    by field_order_zero
      Then minimal_ #0_ = X_         by poly_minimal_zero
        so p_ = X_ ==> p = X         by field_iso_poly_X_iff, subring_poly_X
       ==> x = #0                    by poly_minimal_eq_X
        so ox = 0 = oy               by field_order_zero

   If y <> #0_,
      Then y IN R+_                  by field_nonzero_eq

   Step 1: oy divides ox
   Note p pdivides (unity ox)            by poly_minimal_divides_unity_order
    and Poly s (unity ox)                by poly_unity_spoly
    ==> poly_divides s p (unity ox)      by subring_poly_divides_iff, poly_monic_ulead
  Since MAP f (unity ox) = unity_ ox     by field_iso_poly_unity, subring_poly_unity
  Hence poly_divides s_ p_ (unity_ ox)   by field_iso_poly_divides_iff
   Note Poly s_ (unity_ ox)              by poly_unity_spoly
    ==> p_ pdivides_ (unity_ ox)         by subring_poly_divides

    Now root_ p_ y                       by poly_minimal_has_element_root
     so root_ (unity_ ox) y              by poly_divides_share_root, subring_poly_poly
     or y **_ ox = #1_                   by poly_unity_root_property
    ==> oy divides ox                    by field_order_divides_exp, y IN R+_

   Step 2: ox dividies oy
   Note p_ <> X_                         by poly_minimal_eq_X, y <> #0_
    ==> p <> X                           by field_iso_poly_X, subring_poly_X
    ==> x <> #0                          by poly_minimal_eq_X, p <> X
     or x IN R+                          by field_nonzero_eq

   Note p_ pdivides (unity_ oy)          by poly_minimal_divides_unity_order
    and Poly s_ (unity_ oy)              by poly_unity_spoly
    ==> poly_divides s_ p_ (unity_ oy)   by subring_poly_divides_iff, poly_monic_ulead
  Since MAP (unity oy) = unity_ oy       by field_iso_poly_unity, subring_poly_unity
  Hence poly_divides s p (unity oy)      by field_iso_poly_divides_iff
   Note Poly s (unity oy)                by poly_unity_spoly
    ==> p pdivides (unity oy)            by subring_poly_divides

    Now root p x                         by poly_minimal_has_element_root
     so root (unity oy) x                by poly_divides_share_root, subring_poly_poly
     or x ** oy = #1                     by poly_unity_root_property
    ==> ox divides oy                    by field_order_divides_exp, x IN R+

   Step 3: conclude
     With oy divides ox /\ ox divides oy
      ==> oy = ox                        by DIVIDES_ANTISYM
*)
val finite_field_element_mirror_exists = store_thm(
  "finite_field_element_mirror_exists",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==>
   !x. x IN R ==> ?y. y IN R_ /\ (forder_ y = forder x) /\ (minimal_ y = MAP f (minimal x))``,
  rpt (stripDup[iso_subfields_def]) >>
  qabbrev_tac `p = minimal x` >>
  `s <= r /\ s_ <= r_` by rw[subfield_is_subring] >>
  `Poly s p` by rw[poly_minimal_spoly, Abbr`p`] >>
  `Poly s_ p_` by metis_tac[field_iso_poly] >>
  `IPoly s p` by rw[poly_minimal_subfield_irreducible, Abbr`p`] >>
  `IPoly s_ p_` by metis_tac[field_iso_poly_irreducible] >>
  `monic p` by rw[poly_minimal_monic, Abbr`p`] >>
  `Monic s p` by metis_tac[subring_poly_monic_iff] >>
  `Monic s_ p_` by metis_tac[field_iso_poly_monic] >>
  `monic_ p_` by metis_tac[subring_poly_monic_iff] >>
  `deg_ p_ = deg p` by rw[field_iso_poly_deg] >>
  `(r <:> s) = (r_ <:> s_)` by metis_tac[finite_field_card_eq_subfield_iso_dim_eq] >>
  `(deg p) divides (r <:> s)` by metis_tac[poly_minimal_deg_divides_dim] >>
  `(deg_ p_) divides (r_ <:> s_)` by metis_tac[] >>
  `?y. y IN R_ /\ (p_ = minimal_ y)` by metis_tac[poly_monic_irreducible_is_minimal_poly] >>
  qexists_tac `y` >>
  rw[] >>
  qabbrev_tac `ox = forder x` >>
  qabbrev_tac `oy = forder_ y` >>
  Cases_on `y = #0_` >| [
    `oy = 0` by rw[field_order_zero, Abbr`oy`] >>
    `minimal_ #0_ = X_` by rw[poly_minimal_zero] >>
    `p = X` by metis_tac[field_iso_poly_X_iff, subring_poly_X] >>
    `x = #0` by metis_tac[poly_minimal_eq_X] >>
    rw[field_order_zero, Abbr`ox`],
    `y IN R+_` by rw[field_nonzero_eq] >>
    `Poly s (unity ox) /\ Poly s_ (unity_ ox)` by rw[poly_unity_spoly] >>
    `p pdivides (unity ox)` by rw[poly_minimal_divides_unity_order, Abbr`p`, Abbr`ox`] >>
    `poly_divides s p (unity ox)` by metis_tac[subring_poly_divides_iff, poly_monic_ulead] >>
    `poly_divides s_ p_ (unity_ ox)` by prove_tac[field_iso_poly_divides_iff, field_iso_poly_unity, subring_poly_unity] >>
    `p_ pdivides_ (unity_ ox)` by metis_tac[subring_poly_divides] >>
    `root_ p_ y ` by rw[poly_minimal_has_element_root] >>
    `root_ (unity_ ox) y` by metis_tac[poly_divides_share_root, subring_poly_poly] >>
    `y **_ ox = #1_` by rw[GSYM poly_unity_root_property] >>
    `oy divides ox` by rw[GSYM field_order_divides_exp, Abbr`oy`] >>
    `p_ <> X_` by metis_tac[poly_minimal_eq_X] >>
    `p <> X` by metis_tac[field_iso_poly_X, subring_poly_X] >>
    `x <> #0` by metis_tac[poly_minimal_eq_X] >>
    `x IN R+` by rw[field_nonzero_eq] >>
    `Poly s (unity oy) /\ Poly s_ (unity_ oy)` by rw[poly_unity_spoly] >>
    `p_ pdivides_ (unity_ oy)` by metis_tac[poly_minimal_divides_unity_order] >>
    `poly_divides s_ p_ (unity_ oy)` by metis_tac[subring_poly_divides_iff, poly_monic_ulead] >>
    `poly_divides s p (unity oy)` by prove_tac[field_iso_poly_divides_iff, field_iso_poly_unity, subring_poly_unity] >>
    `p pdivides (unity oy)` by metis_tac[subring_poly_divides] >>
    `root p x` by rw[poly_minimal_has_element_root, Abbr`p`] >>
    `root (unity oy) x` by metis_tac[poly_divides_share_root, subring_poly_poly] >>
    `x ** oy = #1` by rw[GSYM poly_unity_root_property] >>
    `ox divides oy` by rw[GSYM field_order_divides_exp, Abbr`ox`] >>
    rw[DIVIDES_ANTISYM]
  ]);

(* This is a major milestone theorem. *)

(* Apply Skolemization *)
val lemma = prove(
  ``!(r s):'a field (r_ s_):'b field (f:'a -> 'b) x. ?y. r =| (s,f,s_) |= r_ ==>
     x IN R ==> y IN R_ /\ (forder_ y = forder x) /\ (minimal_ y = MAP f (minimal x))``,
  metis_tac[finite_field_element_mirror_exists]);
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
(* Define finite field isomorphic mirror element *)
val finite_field_element_mirror_def = new_specification(
    "finite_field_element_mirror_def",
    ["finite_field_element_mirror"],
    lemma |> SIMP_RULE bool_ss [SKOLEM_THM]
          |> CONV_RULE (RENAME_VARS_CONV ["g"] (* to allow rename of f' back to f *)
                        THENC BINDER_CONV (RENAME_VARS_CONV ["r", "s", "r_", "s_", "f"])));
(* bool_ss for basic rules, (srw_ss()) for all rules. *)

(* overload on mirror element *)
val _ = overload_on("mirror",
    ``finite_field_element_mirror (r:'a field) (s:'a field) (r_:'b field) (s_:'b field)``);
(*
val finite_field_element_mirror_def =
   |- !r s r_ s_ f x. ?y. r =| (s,f,s_) |= r_ ==>
      !x. x IN R ==> mirror f x IN R_ /\ (forder_ (mirror f x) = forder x) /\
                     (minimal_ (mirror f x) = MAP f (minimal x)): thm
*)

(* Theorem: r =| (s,f,s_) |= r_ ==> !x. x IN R ==> (mirror f x) IN R_ *)
(* Proof: by finite_field_element_mirror_def *)
val finite_field_element_mirror_element = store_thm(
  "finite_field_element_mirror_element",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==> !x. x IN R ==> (mirror f x) IN R_``,
  metis_tac[finite_field_element_mirror_def]);

(* Theorem: r =| (s,f,s_) |= r_ ==> !x. x IN R ==> (forder_ (mirror f x) = forder x) *)
(* Proof: by finite_field_element_mirror_def *)
val finite_field_element_mirror_order = store_thm(
  "finite_field_element_mirror_order",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==>
   !x. x IN R ==> (forder_ (mirror f x) = forder x)``,
  metis_tac[finite_field_element_mirror_def]);

(* Theorem: r =| (s,f,s_) |= r_ ==> !x. x IN R ==> (minimal_ (mirror f x) = MAP f (minimal x)) *)
(* Proof: by finite_field_element_mirror_def *)
val finite_field_element_mirror_poly_minimal = store_thm(
  "finite_field_element_mirror_poly_minimal",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==>
   !x. x IN R ==> (minimal_ (mirror f x) = MAP f (minimal x))``,
  metis_tac[finite_field_element_mirror_def]);

(* Theorem: r =| (s,f,s_) |= r_ ==> (mirror f #0 = #0_) *)
(* Proof:
   Since (mirror f #0) IN R_       by finite_field_element_mirror_element
     and forder_ (mirror f #0)
       = forder #0                 by finite_field_element_mirror_order
       = 0                         by field_order_zero
    Thus mirror f #0 = #0_         by field_order_eq_0
*)
val finite_field_element_mirror_zero = store_thm(
  "finite_field_element_mirror_zero",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==> (mirror f #0 = #0_)``,
  rpt (stripDup[iso_subfields_def]) >>
  `(mirror f #0) IN R_` by rw[finite_field_element_mirror_element] >>
  `forder_ (mirror f #0) = forder #0` by rw[finite_field_element_mirror_order] >>
  metis_tac[field_order_eq_0, field_order_zero]);

(* Theorem: r =| (s,f,s_) |= r_ ==> (mirror f #1 = #1_) *)
(* Proof:
   Since (mirror f #1) IN R_       by finite_field_element_mirror_element
     and forder_ (mirror f #1)
       = forder #1                 by finite_field_element_mirror_order
       = 1                         by field_order_one
    Thus mirror f #1 = #1_         by field_order_eq_1
*)
val finite_field_element_mirror_one = store_thm(
  "finite_field_element_mirror_one",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==> (mirror f #1 = #1_)``,
  rpt (stripDup[iso_subfields_def]) >>
  `(mirror f #1) IN R_` by rw[finite_field_element_mirror_element] >>
  `forder_ (mirror f #1) = forder #1` by rw[finite_field_element_mirror_order] >>
  metis_tac[field_order_eq_1, field_order_one]);

(* Theorem: r =| (s,f,s_) |= r_ ==> !x. x IN R ==> ((mirror f x = #0_) <=> (x = #0)) *)
(* Proof:
   Since (mirror f x) IN R_                  by finite_field_element_mirror_element
     and forder_ (mirror f x) = forder x     by finite_field_element_mirror_order
     The result follows                      by field_order_eq_0
*)
val finite_field_element_mirror_eq_zero = store_thm(
  "finite_field_element_mirror_eq_zero",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==>
   !x. x IN R ==> ((mirror f x = #0_) <=> (x = #0))``,
  rpt (stripDup[iso_subfields_def]) >>
  metis_tac[field_order_eq_0, finite_field_element_mirror_element, finite_field_element_mirror_order]);

(* Theorem: r =| (s,f,s_) |= r_ ==> !x. x IN R ==> ((mirror f x = #1_) <=> (x = #1)) *)
(* Proof:
   Since (mirror f x) IN R_                  by finite_field_element_mirror_element
     and forder_ (mirror f x) = forder x     by finite_field_element_mirror_order
     The result follows                      by field_order_eq_1
*)
val finite_field_element_mirror_eq_one = store_thm(
  "finite_field_element_mirror_eq_one",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==>
   !x. x IN R ==> ((mirror f x = #1_) <=> (x = #1))``,
  rpt (stripDup[iso_subfields_def]) >>
  metis_tac[field_order_eq_1, finite_field_element_mirror_element, finite_field_element_mirror_order]);

(* Theorem: r =| (s,f,s_) |= r_ ==>
            (mirror f (primitive r)) IN R+_ /\ (forder_ (mirror f (primitive r)) = CARD R+_) *)
(* Proof:
   Since primitive r IN R+                 by field_primitive_nonzero
      so primitive r <> #0                 by field_nonzero_eq
    thus mirror f (primitive r) <> #0_     by finite_field_element_mirror_eq_zero
      or mirror f (primitive r) IN R+_     by field_nonzero_eq, finite_field_element_mirror_element

    Also primitive r IN R                  by field_nonzero_element
    thus (mirror f (primitive r)) IN R_    by finite_field_element_mirror_element
     and forder_ (mirror f (primitive r))
       = forder (primitive r)              by finite_field_element_mirror_order
       = CARD R+                           by field_primitive_order

    Note CARD R = CARD R_
     ==> SUC (CARD R+) = SUC (CARD R+_)    by finite_field_carrier_card
     ==>       CARD R+ = CARD R+_          by SUC_EQ
   Hence the result follows.
*)
val finite_field_primitive_mirror_property = store_thm(
  "finite_field_primitive_mirror_property",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==>
   (mirror f (primitive r)) IN R+_ /\ (forder_ (mirror f (primitive r)) = CARD R+_)``,
  ntac 6 (stripDup[iso_subfields_def]) >>
  qabbrev_tac `x = primitive r` >>
  qabbrev_tac `mx = mirror f x` >>
  `x IN R+` by rw[field_primitive_nonzero, Abbr`x`] >>
  `x <> #0 /\ x IN R` by metis_tac[field_nonzero_eq] >>
  `mx <> #0_` by rw[finite_field_element_mirror_eq_zero, Abbr`mx`] >>
  `mx IN R+_` by rw[finite_field_element_mirror_element, field_nonzero_eq, Abbr`mx`] >>
  `mx IN R_` by rw[finite_field_element_mirror_element, Abbr`mx`] >>
  `forder_ mx = forder x` by rw[finite_field_element_mirror_order, Abbr`mx`] >>
  `_ = CARD R+` by rw[field_primitive_order, Abbr`x`] >>
  `SUC (CARD R+) = SUC (CARD R+_)` by metis_tac[finite_field_carrier_card] >>
  `CARD R+ = CARD R+_` by decide_tac >>
  rw[]);

(* Theorem: r =| (s,f,s_) |= r_ ==> mirror f (primitive r) IN (FPrimitives r_) *)
(* Proof: by finite_field_primitive_mirror_property, field_primitives_element *)
val finite_field_primitive_mirror = store_thm(
  "finite_field_primitive_mirror",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==> mirror f (primitive r) IN (FPrimitives r_)``,
  rw[finite_field_primitive_mirror_property, field_primitives_element]);

(* ------------------------------------------------------------------------- *)
(* Trinity Polynomial: X ** a + X ** b - X ** c                              *)
(* ------------------------------------------------------------------------- *)

(* Overload for trinity polynomial *)
val _ = overload_on("Trinity", ``\(r:'a ring) a b c. X ** a + X ** b - X ** c``);
val _ = overload_on("trinity", ``Trinity (r:'a ring)``);
val _ = overload_on("trinity_", ``Trinity (r_:'b ring)``);

(* Theorem: Ring r ==> !a b c. poly (trinity a b c) *)
(* Proof:
   Since poly X                 by poly_X
     and !n. poly (X ** n)      by poly_exp_poly
      so poly (trinity a b c)   by poly_add_poly, poly_sub_poly
*)
val poly_trinity_poly = store_thm(
  "poly_trinity_poly",
  ``!r:'a ring. Ring r ==> !a b c. poly (trinity a b c)``,
  rw[]);

(* Theorem: s <= r ==> !a b c. Poly s (trinity a b c) *)
(* Proof:
   Since Poly s X                 by poly_X_spoly
     and !n. Poly s (X ** n)      by poly_exp_spoly
      so Poly s (trinity a b c)   by poly_add_spoly, poly_sub_spoly
*)
val poly_trinity_spoly = store_thm(
  "poly_trinity_spoly",
  ``!(r s):'a ring. s <= r ==> !a b c. Poly s (trinity a b c)``,
  rw_tac std_ss[poly_X_spoly, poly_exp_spoly, poly_add_spoly, poly_sub_spoly]);

(* Theorem: Ring r ==> !x. x IN R ==> !a b c. eval (trinity a b c) x = x ** a + x ** b - x ** c *)
(* Proof:
     eval (trinity a b c) x
   = eval (X ** a + X ** b - X ** c) x                     by notation
   = eval (X ** a) x + eval (X ** b) x - eval (X ** c) x   by poly_eval_add, poly_eval_sub
   = (eval X x) ** a + (eval X x) ** b - (eval X x) ** c   by poly_eval_exp
   = x ** a + x ** b - x ** c                              by poly_eval_X
*)
val poly_trinity_eval = store_thm(
  "poly_trinity_eval",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !a b c. eval (trinity a b c) x = x ** a + x ** b - x ** c``,
  rw[]);

(* Theorem: Ring r ==> !x. x IN R ==>
            !a b c. root (trinity a b c) x <=> (x ** a + x ** b = x ** c) *)
(* Proof:
       root (trinity a b c) x
   <=> eval (trinity a b c) x = #0     by poly_root_def
   <=> x ** a + x ** b - x ** c = #0   by poly_trinity_eval
   <=> x ** a + x ** b = x ** c        by ring_sub_eq_zero
*)
val poly_trinity_root = store_thm(
  "poly_trinity_root",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !a b c. root (trinity a b c) x <=> (x ** a + x ** b = x ** c)``,
  rw_tac std_ss[poly_root_def, poly_trinity_eval, ring_sub_eq_zero, ring_exp_element, ring_add_element]);

(* Theorem: s <= r ==> !a b c. Trinity s a b c = trinity a b c *)
(* Proof:
   Note Poly s X                                               by poly_X_spoly
    and Poly s (X ** a) /\ Poly s (X ** b) /\ Poly s (X ** c)  by poly_exp_spoly
    and Poly s (X ** a + X ** b)                               by poly_add_spoly

     Trinity s a b c
   = poly_sub s (poly_add s (poly_exp s (poly_shift s (poly_one s) 1) a)
                            (poly_exp s (poly_shift s (poly_one s) 1) b))
                (poly_exp s (poly_shift s (poly_one s) 1) c)   by notation
   = poly_sub s (poly_add s (poly_exp s X a) (poly_exp s X b))
                (poly_exp s X c)                            by subring_poly_X
   = poly_sub s (poly_add s (X ** a) (X ** b)) (X ** c)     by subring_poly_exp
   = poly_sub s ((X ** a) + (X ** b)) (X ** c)              by subring_poly_add
   = (X ** a) + (X ** b) - X ** c                           by subring_poly_sub
   = trinity a b c                                          by notation
*)
val subring_poly_trinity = store_thm(
  "subring_poly_trinity",
  ``!(r s):'a ring. s <= r ==> !a b c. Trinity s a b c = trinity a b c``,
  rpt strip_tac >>
  `Poly s X /\ Poly s (X ** a) /\ Poly s (X ** b) /\ Poly s (X ** c)` by rw[poly_X_spoly, poly_exp_spoly] >>
  `Poly s (X ** a + X ** b)` by rw[poly_add_spoly] >>
  metis_tac[subring_poly_X, subring_poly_exp, subring_poly_add, subring_poly_sub]);

(* Theorem: (r === r_) f ==> !a b c. MAP f (trinity a b c) = trinity_ a b c *)
(* Proof:
     MAP f (trinity a b c)
   = MAP f (X ** a + X ** b - X ** c)                           by notation
   = (MAP f (X ** a)) +_ (MAP f (X ** b)) -_ (MAP f (X ** c))   by field_iso_poly_add, field_iso_poly_sub
   = (MAP f X) **_ a +_ (MAP f X) **_ b -_ (MAP f X) **_ c      by field_iso_poly_exp
   = X_ **_ a +_ X_ **_ b -_ X_ **_ c                           by field_iso_poly_X
   = trinity_ a b c                                             by notation
*)
val field_iso_poly_trinity = store_thm(
  "field_iso_poly_trinity",
  ``!(r:'a field) (r_:'b field) f. (r === r_) f ==> !a b c. MAP f (trinity a b c) = trinity_ a b c``,
  rpt strip_tac >>
  `poly X /\ poly (X ** a) /\ poly (X ** b) /\ poly (X ** c) /\ poly (X ** a + X ** b)` by rw[] >>
  metis_tac[field_iso_poly_add, field_iso_poly_sub, field_iso_poly_exp, field_iso_poly_X]);

(* ------------------------------------------------------------------------- *)
(* Uniqueness of Finite Field (Part 1)                                       *)
(* ------------------------------------------------------------------------- *)

(* A finite field of cardinality (p ** n) is unique in the following sense:
   Two finite fields of same cardinality are isomorphic.
   This uniqueness of Finite Field depends on the following:

(1) Two finite fields of the same cardinality have the same characteristic:
finite_field_card_eq_char_eq
|- !r r_. FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==> (char r = char r_)

(2) Thus their prime fields, of cardinality equal to characteristic, are isomorphic:
finite_field_iso_GF_PF
|- !r. FiniteField r ==> FieldIso $## (GF (char r)) (PF r)
field_iso_iso
|- !r s. Field r /\ Field s ==> !f1 f2 t. FieldIso f1 r s /\ FieldIso f2 r t ==> FieldIso (f2 o LINV f1 R) s t

These isomorphic subfields provides a channel (or tunnel) to build an explicit map
to show that the original equal-cardinality finite fields. This is achieved in several stages.

(3) First, introduce the idea of iso_subfields pairs:
r =| (s,f,s_) |= r_   when two pairs of field-subfields are related by:
FiniteField (r:'a field) /\ FiniteField (r_:'b field) /\
 (CARD R = CARD R_) /\ s <<= r /\ s_ <<= r_ /\ FieldIso f s s_

(4) Show that Field s /\ Field s_ /\ FieldIso f s s_ will have the map f giving correspondences:
For elements:
   field_iso_zero    |- !r r_ f. (r === r_) f ==> (f #0 = #0_)
   field_iso_one     |- !r r_ f. (r === r_) f ==> (f #1 = #1_)
   field_iso_add     |- !r r_ f. (r === r_) f ==> !x y. x IN R /\ y IN R ==> (f (x + y) = f x +_ f y)
   field_iso_mult    |- !r r_ f. (r === r_) f ==> !x y. x IN R /\ y IN R ==> (f (x * y) = f x *_ f y)
   field_iso_neg     |- !r r_ f. (r === r_) f ==> !x. x IN R ==> (f (-x) = $-_ (f x))
   field_iso_sub     |- !r r_ f. (r === r_) f ==> !x y. x IN R /\ y IN R ==> (f (x - y) = f x -_ f y)
   field_iso_exp     |- !r r_ f. (r === r_) f ==> !x. x IN R ==> !n. f (x ** n) = f x **_ n
For polynomials:
   field_iso_poly          |- !r r_ f. (r === r_) f ==> !p. poly p ==> poly_ p_
   field_iso_poly_zero     |- !r r_ f. MAP f |0| = |0|_
   field_iso_poly_one      |- !r r_ f. (r === r_) f ==> (MAP f |1| = |1|_)
   field_iso_poly_add      |- !r r_ f. (r === r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p + q) = p_ +_ q_)
   field_iso_poly_neg      |- !r r_ f. (r === r_) f ==> !p. poly p ==> (MAP f (-p) = $-_ p_)
   field_iso_poly_sub      |- !r r_ f. (r === r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p - q) = p_ -_ q_)
   field_iso_poly_cmult    |- !r r_ f. (r === r_) f ==> !p c. poly p /\ c IN R ==> (MAP f (c * p) = f c *_ p_)
   field_iso_poly_shift    |- !r r_ f. (r === r_) f ==> !p n. MAP f (p >> n) = p_ >>_ n
   field_iso_poly_mult     |- !r r_ f. (r === r_) f ==> !p q. poly p /\ poly q ==> (MAP f (p * q) = p_ *_ q_)
   field_iso_poly_exp      |- !r r_ f. (r === r_) f ==> !p. poly p ==> !n. MAP f (p ** n) = p_ **_ n
   field_iso_poly_deg      |- !r r_ f p. deg_ p_ = deg p
   field_iso_poly_lead     |- !r r_ f. (r === r_) f ==> !p. lead_ p_ = f (lead p)

(5) More deeply, these polynomial correspondences are critical:
   field_iso_poly_X_iff       |- !r r_ f. (r === r_) f ==> !p. poly p ==> ((p_ = X_) <=> (p = X))
   field_iso_poly_unity       |- !r r_ f. (r === r_) f ==> !n. MAP f (unity n) = unity_ n
   field_iso_poly_master      |- !r r_ f. (r === r_) f ==> !n. MAP f (master n) = master_ n
   field_iso_poly_divides_iff |- !r r_ f. (r === r_) f ==> !p q. poly p /\ poly q ==> (p pdivides q <=> p_ pdivides_ q_)
   field_iso_poly_monic_iff   |- !r r_ f. (r === r_) f ==> !p. poly p ==> (monic p <=> monic_ p_)
   field_iso_poly_unit_iff    |- !r r_ f. (r === r_) f ==> !p. poly p ==> (upoly p <=> upoly_ p_)
   field_iso_poly_irreducible |- !r r_ f. (r === r_) f ==> !p. ipoly p ==> ipoly_ p_
   field_iso_poly_eval        |- !r r_ f. (r === r_) f ==> !p x. poly p /\ x IN R ==> (f (eval p x) = eval_ p_ (f x))
   field_iso_poly_root        |- !r r_ f. (r === r_) f ==> !p x. poly p /\ x IN R /\ root p x ==> root_ p_ (f x)

(6) These correspondences, combine with the following key:
poly_minimal_divides_unity_order
|- !r s. FiniteField r /\ s <<= r ==> !x. x IN R ==> minimal x pdivides unity (forder x)
gives for each field element its mirror, for a pair of field/subfields with iso_subfields:
finite_field_element_mirror_exists
|- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> !x. x IN R ==>
    ?y. y IN R_ /\ (forder_ y = forder x) /\ (minimal_ y = MAP f (minimal x))
The element y is defined as (mirror f x) via Skolemization.

(7) Take x as a primitive of one field, then (mirror f x) is another primitive on the other field:
finite_field_primitive_mirror
|- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> mirror f (primitive r) IN FPrimitives r_

This finally gives the field isomorphism map:
field_iso_map_def
|- !r s r_ s_ f x. im f x = if x = #0 then #0_ else mirror f (primitive r) **_ idx
where field_index_def
|- !r x. FiniteField r /\ x IN R+ ==> idx x < CARD R+ /\ (x = primitive r ** idx x)

(8) Then it is just a matter to show that (im f x) is really an isomorphism. First part is easy:
   field_iso_map_element |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> !x. x IN R ==> im f x IN R_
   field_iso_map_eq_zero |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> !x. x IN R ==> ((im f x = #0_) <=> (x = #0))
   field_iso_map_eq_one  |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> !x. x IN R ==> ((im f x = #1_) <=> (x = #1))
   field_iso_map_nonzero |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> !x. x IN R+ ==> im f x IN R+_

(9) Second part takes some effort:
   field_iso_map_neg_one |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> (im f (-#1) = $-_ #1_)
   field_iso_map_mult    |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> !x y. x IN R /\ y IN R ==> (im f (x * y) = im f x *_ im f y)
   field_iso_map_neg     |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> !x. x IN R ==> (im f (-x) = $-_ (im f x))

field_iso_map_neg_one needs a consideration on the field characteristic, since:
field_index_neg: !x. x IN R+ ==> (idx (-x) = if char r = 2 then idx x else (idx x + CARD R+ DIV 2) MOD CARD R+)
field_iso_map_mult is a simple consequence of field_exp_add: !n k. x ** (n + k) = x ** n * x ** k
field_iso_map_neg comes from -x = -#1 * x, and applying field_iso_map_mult and field_iso_map_neg_one.

(10) Third part is tough:
   field_iso_map_add     |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> !x y. x IN R /\ y IN R ==> (im f (x + y) = im f x +_ im f y)
   field_iso_map_sub     |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> !x y. x IN R /\ y IN R ==> (im f (x - y) = im f x -_ im f y)
   field_iso_map_eq      |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> !x y. x IN R /\ y IN R /\ (im f x = im f y) ==> (x = y)

field_iso_map_add needs the little theory of trinity polynomials:
Trinity = \(r:'a ring) a b c. X ** a + X ** b - X ** c
with poly_trinity_root: !x. x IN R ==> !a b c. root (trinity a b c) x <=> (x ** a + x ** b = x ** c)
When x IN R+ and y IN R+ give t = x + y,
if t <> #0, then t IN R+.
   Note that (trinity (idx x) (idx y) (idx t)) is a subfield poly with (primitive r) as a root.
   This allows the polynomial correspondence to give (trinity_ (idx x) (idx y) (idx t)),
   with (mirror f (primitive r)) as a root, eventually; thus giving (im f t = im f x +_ im f y).
If t = #0, then y = -x, so apply field_iso_map_neg to give (im f t = #0_ = im f x +_ im f y).

field_iso_map_sub comes from x - y = x + (-y), and applying field_iso_map_add, field_iso_map_neg.
field_iso_map_eq comes from x = y <=> x - y = #0, and applying field_iso_map_sub, field_iso_map_eq_zero.

(11) Once this is through, it remains to show:
   field_iso_map_inj     |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> INJ (im f) R R_
   field_iso_map_surj    |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> SURJ (im f) R R_
   field_iso_map_bij     |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> BIJ (im f) R R_

field_iso_map_inj just depends on field_iso_map_eq.
field_iso_map_surj follows by INJ (im f) R R_ with (CARD R = CARD R_).
field_iso_map_bij = field_iso_map_inj + field_iso_map_surj

(12) All these, combining with (2), lead to:
   field_iso_map_field_iso    |- !r s r_ s_ f. r =| (s,f,s_) |= r_ ==> FieldIso (im f) r r_
   finite_field_eq_card_iso   |- !r r_. FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==>
                FieldIso (field_iso_map r (PF r) r_ (PF r_) (##_ #1_ o LINV $## (GF (char r)).carrier)) r r_
   finite_field_eq_card_isomorphic
                              |- !r r_. FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==> r =ff= r_

Thus two finite fields with same cardinality are isomorphic.
*)

(* Theorem: FiniteField r ==> (GF (char r)) =ff= (PF (char r)) *)
(* Proof:
   By notation, this is to show:
   (1) FiniteField (GF (char r))
       Note prime (char r)             by finite_field_char
         so FiniteField (GF (char r))  by GF_finite_field, prime (char r)
   (2) FiniteField (PF r), true        by prime_field_finite_field
   (3) ?f. FieldIso f (GF (char r)) (PF r)
       Take f = $##, true              by finite_field_iso_GF_PF
*)
val finite_field_isomorphic_GF_PF = store_thm(
  "finite_field_isomorphic_GF_PF",
  ``!r:'a field. FiniteField r ==> (GF (char r)) =ff= (PF r)``,
  rpt strip_tac >-
  rw[GF_finite_field, finite_field_char] >-
  rw[prime_field_finite_field] >>
  metis_tac[finite_field_iso_GF_PF]);

(* Theorem: FiniteField r ==> (ZN (char r)) =ff= (PF (char r)) *)
(* Proof:
   By notation, this is to show:
   (1) FiniteField (ZN (char r))
       Note prime (char r)             by finite_field_char
         so FiniteField (ZN (char r))  by ZN_finite_field, prime (char r)
   (2) FiniteField (PF r), true        by prime_field_finite_field
   (3) ?f. FieldIso f (ZN (char r)) (PF r)
       Take f = $##, true              by finite_field_iso_ZN_PF
*)
val finite_field_isomorphic_ZN_PF = store_thm(
  "finite_field_isomorphic_ZN_PF",
  ``!r:'a field. FiniteField r ==> (ZN (char r)) =ff= (PF r)``,
  rpt strip_tac >-
  rw[ZN_finite_field, finite_field_char] >-
  rw[prime_field_finite_field] >>
  metis_tac[finite_field_iso_ZN_PF]);

(* Theorem: FiniteField r ==> (PF r) =ff= (GF (char r)) *)
(* Proof: by finite_field_isomorphic_GF_PF, field_iso_sym, finite_field_is_field *)
val finite_field_isomorphic_GF_PF_alt = store_thm(
  "finite_field_isomorphic_GF_PF_alt",
  ``!r:'a field. FiniteField r ==> (PF r) =ff= (GF (char r))``,
  metis_tac[finite_field_isomorphic_GF_PF, field_iso_sym, finite_field_is_field]);

(* Theorem: FiniteField r ==> (PF r) =ff= (ZN (char r)) *)
(* Proof: by finite_field_isomorphic_ZN_PF, field_iso_sym, finite_field_is_field *)
val finite_field_isomorphic_ZN_PF_alt = store_thm(
  "finite_field_isomorphic_ZN_PF_alt",
  ``!r:'a field. FiniteField r ==> (PF r) =ff= (ZN (char r))``,
  metis_tac[finite_field_isomorphic_ZN_PF, field_iso_sym, finite_field_is_field]);

(* Theorem: FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==>
            FieldIso ((##_ #1_) o (LINV $## (GF (char r)).carrier)) (PF r) (PF r_) *)
(* Proof:
   Note FieldIso $## (GF (char r)) (PF r)           by finite_field_iso_GF_PF
    and FieldIso (##_ #1_) (GF (char r_)) (PF r_)   by finite_field_iso_GF_PF
    Now char r = char r_                   by finite_field_card_eq_char_eq
    ==> GF (char r) = GF (char r_)
   Also prime (char r)                     by finite_field_char
    ==> Field (GF (char r))                by GF_field
    and Field (PF r)                       by prime_field_field
   Hence the result follows                by field_iso_iso
*)
val finite_field_prime_field_iso = store_thm(
  "finite_field_prime_field_iso",
  ``!(r:'a field) (r_:'b field). FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==>
   FieldIso ((##_ #1_) o (LINV $## (GF (char r)).carrier)) (PF r) (PF r_)``,
  rpt (stripDup[FiniteField_def]) >>
  `FieldIso $## (GF (char r)) (PF r)` by rw[finite_field_iso_GF_PF] >>
  `FieldIso (##_ #1_) (GF (char r_)) (PF r_)` by rw[finite_field_iso_GF_PF] >>
  `char r = char r_` by rw[finite_field_card_eq_char_eq] >>
  `prime (char r)` by rw[finite_field_char] >>
  `Field (GF (char r))` by rw[GF_field] >>
  `Field (PF r)` by rw[prime_field_field] >>
  rw[field_iso_iso]);

(* Theorem: FiniteField r /\ FiniteField r_ /\ (char r = char r_) ==>
            FieldIso ((##_ #1_) o (LINV $## (ZN (char r)).carrier)) (PF r) (PF r_) *)
(* Proof:
   Let p = char r.
   Note FieldIso $## (ZN p) (PF r)          by finite_field_iso_ZN_PF
    and FieldIso (##_ #1_) (ZN p) (PF r_)   by finite_field_iso_ZN_PF
   Also prime p                             by finite_field_char
    ==> Field (ZN p)                        by ZN_field
    and Field (PF r)                        by prime_field_field
   Hence the result follows                 by field_iso_iso
*)
val finite_field_char_eq_prime_field_iso = store_thm(
  "finite_field_char_eq_prime_field_iso",
  ``!(r:'a field) (r_:'b field). FiniteField r /\ FiniteField r_ /\ (char r = char r_) ==>
   FieldIso ((##_ #1_) o (LINV $## (ZN (char r)).carrier)) (PF r) (PF r_)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `p = char r` >>
  `FieldIso $## (ZN p) (PF r)` by rw[finite_field_iso_ZN_PF, Abbr`p`] >>
  `FieldIso (##_ #1_) (ZN p) (PF r_)` by rw[finite_field_iso_ZN_PF] >>
  `prime p` by rw[finite_field_char] >>
  `Field (ZN p)` by rw[ZN_field] >>
  `Field (PF r)` by rw[prime_field_field] >>
  rw[field_iso_iso]);

(* This is a milestone theorem. *)

(* Theorem: FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==> (PF r) =ff= (PF r_) *)
(* Proof:
   Note FiniteField (PF r) and FiniteField (PF r)  by prime_field_finite_field
   Hence the result follows                        by finite_field_prime_field_iso
*)
val finite_field_prime_field_isomorphic = store_thm(
  "finite_field_prime_field_isomorphic",
  ``!(r:'a field) (r_:'b field). FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==> (PF r) =ff= (PF r_)``,
  metis_tac[finite_field_prime_field_iso, prime_field_finite_field]);


(* ------------------------------------------------------------------------- *)
(* Finite Field Isomorphic Map                                               *)
(* ------------------------------------------------------------------------- *)

(* Idea:

Given two finite fields r, s of the same cardinality, CARD R = CARD Q.
each will have a primitive, say a = primitive r, and b = primitive s.
Consider the map: f = \x. s.prod.exp b (idx x).

If two nonzero x = a ** (idx x), y = a ** (idx y) in R, multiply to z = a ** (idx z),
Then x * y = z becomes a ** (idx x) * a ** (idx y) = a ** (idx z)
                         or   a ** (idx x + idx y) = a ** (idx z)
                         or         idx x + idx y = idx z
which gives idx x + idx y = idx z.
Hence  s.prod.ip (f x) (f y)
     = s.prod.ip (b ** (idx x)) (b ** (idx y))
     = b ** (idx x + idx y)
     = b ** idx z
     = f z

If two nonzero x = a ** (idx x), y = a ** (idx y) in R, add to z = a ** (idx z),
and z <> #0,
Then x + y = z becomes   a ** (idx x) + a ** (idx y) = a ** (idx z).
That means: primitive a is a root of the polynomial p = X ** (idx x) + X ** (idx y) - X ** (idx z).
But p is an spoly: Poly (PF r) p, since its coefficients are #1 and -#1, both in prime subfield.
-- Hence (minimal a) | p,   by poly_minimal_divides_subfield_poly.
-- need field_iso_map_one, and field_iso_map_neg_one
Then q = MAP f p will also be an spoly: Poly (PF s) q.
Since q is an spoly, minimal polynomial of b = primitive s will divide it, by poly_minimal_divides_subfield_poly
(minimal b) | q.
That is, b is a root of q, or b ** (idx x) + b ** (idx y) = b ** (idx z).
or f x + f y = f (x + y).

If z = #0,
If x = #0 or y = #0, this is trivial.
If x <> #0 and y <> #0, then x + y = #0 means:
If char r = 2, y = - x = x     in char r = 2,
so f (x + y) = f #0 = s.sum.id
   s.sum.op (f x) (f y) = s.sum.op (f x) (f x) = s.sum.id
If char r <> 2, -#1 = a ** (CARD R - 1) DIV 2.
   so f -#1 = b ** (CARD R - 1) DIV 2 = s.sum.inv (s.sum.id)
   s.sum.op (f x) (f -x)
 = s.sum.op (f x) (f -#1 * x)
 = s.sum.op (f x) (s.prod.op (f -#1) (f x))
 = s.sum.op (f x) (s.prod.op (s.sum.inv (s.sum.id)) (f x))
 = s.sum.op (f x) (s.sum.inv (f x))
 = s.sum.id = f (x + y)

*)

(* Idea:

Two finite fields r and s with the same number of elements CARD R = CARD s.carrier
are isomorphic when one primitive is mapped to another:
    f x = if x = #0 then s.sum.id else s.prod.exp (primitive s) (idx x)
That is,   #0 --> s.sum.id
           #1 --> s.prod.id
  and x IN R+ <=> x = z ** (idx x)      where z = primitive r.
   so   z ** (idx x) --> z' ** (idx)    where z' = primitive s.

However, need to show BIJ f and f preserves + and *.

That f preserves * is simple:   z ** (idx x) * z ** (idx y) = z ** (idx x + idx y)
       thus map to  z' ** (idx x + idx y) = z' ** (idx x) * z' ** (idx y)
But to show f preserves + is not straight-forward.
All you have is that, by field_add_element, if x + y <> 0,
    you only have: (x + y) = z ** (idx (x + y)),
    which maps to: z' ** (idx (x + y)).
We need to get the help from the minimal polynomial of z.
See Timothy Murphy: Finite Field (Course MA364D)  Chapter 9.
*)

(* Define the isomorphism between two fields:
          a map from r to r_, with (s === s_) f:
                #0 -> #0_
                x  -> mirror f (primitive r) **_ (idx x)
*)
val field_iso_map_def = Define`
    field_iso_map (r:'a field) (s:'a field) (r_:'b field) (s_:'b field) f x =
    if x = #0 then #0_ else (mirror f (primitive r)) **_ (idx x)
`;

(* Overload on image of field isomorphism *)
val _ = overload_on("im", ``field_iso_map (r:'a field) (s:'a field) (r_:'b field) (s_:'b field)``);
(*
> field_iso_map_def;
val it = |- !r s r_ s_ f x. im f x = if x = #0 then #0_ else mirror f (primitive r) **_ idx x: thm
*)

(* Theorem: r =| (s,f,s_) |= r_ ==> !x. x IN R ==> im f x IN R_ *)
(* Proof:
   By field_iso_map_def, this is to show:
   (1) #0_ IN R_, true                      by field_zero_element
   (2) mirror f (primitive r) **_ idx x IN R_
       Since primitive r IN R               by field_primitive_element
         and mirror f (primitive r) IN R_   by finite_field_element_mirror_element
       Hence im f x IN R                    by field_exp_element
*)
val field_iso_map_element = store_thm(
  "field_iso_map_element",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==> !x. x IN R ==> im f x IN R_``,
  rpt (stripDup[iso_subfields_def]) >>
  rw_tac std_ss[field_iso_map_def] >-
  rw[] >>
  rw[finite_field_element_mirror_element]);

(* Theorem: im f #0 = #0_ *)
(* Proof: by field_iso_map_def. *)
val field_iso_map_zero = store_thm(
  "field_iso_map_zero",
  ``!(r s):'a field (r_ s_):'b field f. im f #0 = #0_``,
  rw_tac std_ss[field_iso_map_def]);

(* Theorem: FiniteField r ==> (im f #1 = #1_) *)
(* Proof:
   Since #1 <> #0                          by field_one_ne_zero
   By field_iso_map_def, this is to show:
      mirror f (primitive r) **_ idx #1 = #1_

      mirror f (primitive r) **_ idx #1
    = mirror f (primitive r) **_ 0         by field_index_one, FiniteField r
    = #1_                                  by field_exp_0
*)
val field_iso_map_one = store_thm(
  "field_iso_map_one",
  ``!(r s):'a field (r_ s_):'b field f. FiniteField r ==> (im f #1 = #1_)``,
  rw_tac std_ss[FiniteField_def, field_iso_map_def, field_one_ne_zero, field_index_one, field_exp_0]);

(* Theorem: r =| (s,f,s_) |= r_ ==> !x. x IN R ==> ((im f x = #0_) <=> (x = #0)) *)
(* Proof:
   If part: im f x = #0_ ==> x = #0
      By contradiction, suppose x <> #0.
      Then im f x = (mirror f (primitive r)) **_ (idx x)   by field_iso_map_def
       Let z = primitive r
      Note z IN R+              by field_primitive_nonzero
        so z <> #0 /\ z IN R    by field_nonzero_eq
       ==> (mirror f z) <> #0_  by finite_field_element_mirror_eq_zero
      Note (mirror f z) IN R_   by finite_field_element_mirror_element
      Thus (mirror f z) **_ (idx x) <> #0_   by field_exp_eq_zero
      This contradicts im f x = #0_

   Only-if part: x = #0 ==> im f x = #0_
      True by field_iso_map_zero
*)
val field_iso_map_eq_zero = store_thm(
  "field_iso_map_eq_zero",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==>
   !x. x IN R ==> ((im f x = #0_) <=> (x = #0))``,
  rpt (stripDup[iso_subfields_def]) >>
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    qabbrev_tac `z = primitive r` >>
    `z IN R+` by rw[field_primitive_nonzero, Abbr`z`] >>
    `z <> #0 /\ z IN R` by metis_tac[field_nonzero_eq] >>
    `(mirror f z) <> #0_` by rw[finite_field_element_mirror_eq_zero] >>
    `(mirror f z) IN R_` by rw[finite_field_element_mirror_element] >>
    metis_tac[field_iso_map_def, field_exp_eq_zero],
    rw[field_iso_map_zero]
  ]);

(* Theorem: r =| (s,f,s_) |= r_ ==> !x. x IN R ==> ((im f x = #1_) <=> (x = #1)) *)
(* Proof:
   If part: im f x = #1_ ==> x = #1
      Since #1_ <> #0_          by field_one_ne_zero
         so x <> #0             by field_iso_map_eq_zero
         or x IN R+             by field_one_ne_zero
      Then im f x = (mirror f (primitive r)) **_ (idx x)   by field_iso_map_def
       Let z = (mirror f (primitive r)).
        so z **_ (idx x) = #1_            by im f x = #1_
      Note z IN R+_ /\ (forder_ z = CARD R+_)  by finite_field_primitive_mirror_property
       and CARD R+ = CARD R+_                  by finite_field_carrier_card, SUC_EQ
      Also idx x < CARD R+                     by field_index_def, x IN R+
       But (forder_ z) divides (idx x)         by field_order_divides_exp, z IN R+_
      This is impossible unless idx x = 0      by DIVIDES_LE
        or x = #1                              by field_index_eq_0

   Only-if part: x = #1 ==> im f x = #1_
      True by field_iso_map_one
*)
val field_iso_map_eq_one = store_thm(
  "field_iso_map_eq_one",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==>
   !x. x IN R ==> ((im f x = #1_) <=> (x = #1))``,
  rpt (stripDup[iso_subfields_def]) >>
  rw[EQ_IMP_THM] >| [
    `x <> #0 /\ x IN R+` by metis_tac[field_iso_map_eq_zero, field_one_ne_zero, field_nonzero_eq] >>
    qabbrev_tac `z = (mirror f (primitive r))` >>
    `z **_ (idx x) = #1_` by metis_tac[field_iso_map_def] >>
    `z IN R+_ /\ (forder_ z = CARD R+_)` by rw[finite_field_primitive_mirror_property, Abbr`z`] >>
    `CARD R+ = CARD R+_` by metis_tac[finite_field_carrier_card, SUC_EQ] >>
    `idx x < CARD R+` by rw[field_index_def] >>
    `idx x = 0` by
  (spose_not_then strip_assume_tac >>
    `0 < idx x` by decide_tac >>
    `(forder_ z) divides (idx x)` by rw[GSYM field_order_divides_exp] >>
    `(forder_ z) <= idx x` by rw[DIVIDES_LE] >>
    decide_tac) >>
    rw[GSYM field_index_eq_0],
    rw[field_iso_map_one]
  ]);

(* Theorem: r =| (s,f,s_) |= r_ ==> !x. x IN R+ ==> im f x IN R+_ *)
(* Proof:
     x IN R+
   <=> x IN R /\ x <> #0          by field_nonzero_eq
   Note x IN R ==> im f x IN R_   by field_iso_map_element
    and x <> #0 ==> im f x <> #0_ by field_iso_map_eq_zero
*)
val field_iso_map_nonzero = store_thm(
  "field_iso_map_nonzero",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==> !x. x IN R+ ==> im f x IN R+_``,
  rw_tac std_ss[field_nonzero_eq, field_iso_map_eq_zero, field_iso_map_element]);

(* Theorem: r =| (s,f,s_) |= r_ ==> (im f (-#1) = $-_ (#1_)) *)
(* Proof:
   Since CARD R = CARD R_
     ==> char r = char r_                by finite_field_card_eq_char_eq
    Also CARD R = SUC (CARD R+)          by finite_field_carrier_card
     and CARD R_ = SUC (CARD (R+_))      by finite_field_carrier_card
    thus CARD R+ = CARD (R+_)            by SUC_EQ

   If char r = 2,
        im f (-#1)
      = im f #1           by ring_char_2_neg_one
      = #1_               by field_iso_map_one
      = $-_ (#1_)         by ring_char_2_neg_one

   If char r <> 2,
      Since #1 IN R+                     by field_one_nonzero
        so -#1 IN R+                     by field_neg_nonzero
        or -#1 <> #0                     by field_nonzero_eq
      Note (mirror f (primitive r)) IN (FPrimitives r_)  by finite_field_primitive_mirror
        im f (-#1)
      = (mirror f (primitive r)) **_ (idx (-#1))       by field_iso_map_def, -#1 <> #0
      = (mirror f (primitive r)) **_ (CARD R+ DIV 2)   by field_index_neg_one
      = (mirror f (primitive r)) **_ (CARD R+_ DIV 2)  by above
      = $-_ (#1_)                        by finite_field_neg_one_alt, char r_ <> 2.
*)
val field_iso_map_neg_one = store_thm(
  "field_iso_map_neg_one",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==> (im f (-#1) = $-_ (#1_))``,
  rpt (stripDup[iso_subfields_def]) >>
  `char r = char r_` by rw[finite_field_card_eq_char_eq] >>
  `CARD R+ = CARD R+_` by metis_tac[finite_field_carrier_card, SUC_EQ] >>
  Cases_on `char r = 2` >-
  rw[ring_char_2_neg_one, field_iso_map_one] >>
  `-#1 <> #0` by rw[] >>
  `im f (-#1) = (mirror f (primitive r)) **_ (idx (-#1))` by metis_tac[field_iso_map_def] >>
  `_ = (mirror f (primitive r)) **_ (CARD (R+_) DIV 2)` by rw[field_index_neg_one] >>
  `(mirror f (primitive r)) IN (FPrimitives r_)` by rw[finite_field_primitive_mirror] >>
  metis_tac[finite_field_neg_one_alt]);

(* Theorem: r =| (s,f,s_) |= r_ ==> !x y. x IN R /\ y IN R ==> (im f (x * y) = (im f x) *_ (im f y)) *)
(* Proof:
   If x = #0,
      LHS = im f (#0 * y)
          = im f #0               by field_mult_lzero
          = #0_                   by field_iso_map_zero
      RHS = (im f #0) *_ (im f y)
          = #0_ *_ (im f y)       by field_iso_map_zero
          = #0_ = LHS             by field_mult_lzero
   If y = #0,
      Similar calculation using field_mult_rzero.
   If x <> #0 /\ y <> #0,
      Then x IN R+ /\ y IN R+                     by field_nonzero_eq
       and x * y <> #0                            by field_mult_eq_zero

       Let z = mirror f (primitive r)
      Then z IN R+_ /\ (forder_ z = CARD R+_)     by finite_field_primitive_mirror_property
       and z IN R_                                by field_nonzero_element

           im f (x * y)
         = z **_ (idx (x * y))                    by field_iso_map_def
         = z **_ ((idx x + idx y) MOD (CARD R+))  by field_index_mult, x IN R+, y IN R+
         = z **_ ((idx x + idx y) MOD (CARD R+_)) by finite_field_carrier_card, SUC_EQ
         = z **_ (idx x + idx y)                  by finite_field_exp_mod_order
         = z **_ (idx x) *_ z **_ (idx y)         by field_exp_add, z IN R_
         = (im f x) *_ (im f y)                   by field_iso_map_def
*)
val field_iso_map_mult = store_thm(
  "field_iso_map_mult",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==>
   !x y. x IN R /\ y IN R ==> (im f (x * y) = (im f x) *_ (im f y))``,
  rpt (stripDup[iso_subfields_def]) >>
  Cases_on `(x = #0) \/ (y = #0)` >-
  metis_tac[field_iso_map_zero, field_mult_eq_zero, field_iso_map_element] >>
  `x IN R+ /\ y IN R+` by metis_tac[field_nonzero_eq] >>
  `x * y <> #0` by metis_tac[field_mult_eq_zero] >>
  qabbrev_tac `z = mirror f (primitive r)` >>
  `z IN R+_ /\ (forder_ z = CARD R+_)` by rw[finite_field_primitive_mirror_property, Abbr`z`] >>
  `z IN R_` by rw[field_nonzero_element] >>
  `im f (x * y) = z **_ (idx (x * y))` by rw[field_iso_map_def, Abbr`z`] >>
  `_ = z **_ ((idx x + idx y) MOD (CARD R+))` by rw[field_index_mult] >>
  `_ = z **_ ((idx x + idx y) MOD (CARD R+_))` by metis_tac[finite_field_carrier_card, SUC_EQ] >>
  `_ = z **_ (idx x + idx y)` by metis_tac[finite_field_exp_mod_order] >>
  rw[field_exp_add, field_iso_map_def]);

(* Theorem: r =| (s,f,s_) |= r_ ==> !x. x IN R ==> (im f (-x) = $-_ (im f x)) *)
(* Proof:
   If x = #0,
        im f (-#0)
      = im f #0      by field_neg_zero
      = #0_          by field_iso_map_zero
      = $-_ (#0_)    by field_neg_zero
   If x <> #0,
      Then x IN R+               by field_nonzero_eq
       and -x <> #0              by field_neg_eq_zero
      Also char r = char r_      by finite_field_card_eq_char_eq
       and im f x IN R_          by field_iso_map_element

      Let z = mirror f (primitive r).
      If char r = 2,
        im f (-x)
      = z **_ (idx (-x))    by field_iso_map_def
      = z **_ (idx x)       by field_index_neg
      = im f x              by field_iso_map_def
      = $-_ (im f x)        by field_neg_char_2, char r_ = 2

      If char r <> 2,
      Then z IN R+_ /\ (forder_ z = CARD R+_)    by finite_field_primitive_mirror_property
       and CARD R+_ = CARD R+                    by finite_field_carrier_card, SUC_EQ
       and z IN R_                               by field_nonzero_element
        im f (-x)
      = z **_ (idx (-x))                     by field_iso_map_def
      = z **_ ((idx x + CARD R+ DIV 2) MOD CARD R+)   by field_index_neg
      = z **_ (idx x + CARD R+ DIV 2)        by finite_field_exp_mod_order
      = z **_ (idx x + idx (-#1))            by field_index_neg_one, char r_ <> 2
      = z **_ (idx x) *_ z **_ (idx (-#1))   by field_exp_add
      = (im f x) **_ z **_ (-#1))            by field_iso_map_def
      = z **_ ($-_ (#1_))                    by field_iso_map_neg_one
      = $-_ ((im f x) *_ (#1_))              by field_neg_mult
      = $-_ (im f x)                         by field_mult_rone
*)
val field_iso_map_neg = store_thm(
  "field_iso_map_neg",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==>
   !x. x IN R ==> (im f (-x) = $-_ (im f x))``,
  rpt (stripDup[iso_subfields_def]) >>
  Cases_on `x = #0` >-
  rw[field_iso_map_zero, field_neg_zero] >>
  `x IN R+` by rw[field_nonzero_eq] >>
  `-x <> #0` by rw[field_neg_eq_zero] >>
  `char r = char r_` by rw[finite_field_card_eq_char_eq] >>
  `im f x IN R_` by rw[field_iso_map_element] >>
  qabbrev_tac `z = mirror f (primitive r)` >>
  Cases_on `char r = 2` >| [
    `im f (-x) = z **_ (idx (-x))` by rw[field_iso_map_def, Abbr`z`] >>
    `_ = z **_ (idx x)` by rw[field_index_neg] >>
    `_ = im f x` by rw[field_iso_map_def] >>
    `_ = $-_ (im f x)` by rw[field_neg_char_2] >>
    rw[],
    `z IN R+_ /\ (forder_ z = CARD R+_)` by rw[finite_field_primitive_mirror_property, Abbr`z`] >>
    `_ = CARD R+` by metis_tac[finite_field_carrier_card, SUC_EQ] >>
    `z IN R_` by rw[field_nonzero_element] >>
    `im f (-x) = z **_ (idx (-x))` by rw[field_iso_map_def, Abbr`z`] >>
    `_ = z **_ ((idx x + CARD R+ DIV 2) MOD CARD R+)` by rw[field_index_neg] >>
    `_ = z **_ (idx x + CARD R+ DIV 2)` by metis_tac[finite_field_exp_mod_order] >>
    `_ = z **_ (idx x + idx (-#1))` by rw[field_index_neg_one] >>
    `_ = z **_ (idx x) *_ z **_ (idx (-#1))` by rw[field_exp_add] >>
    `_ = (im f x) *_ (im f (-#1))` by rw[field_iso_map_def] >>
    `_ = (im f x) *_ ($-_ (#1_))` by metis_tac[field_iso_map_neg_one] >>
    `_ = $-_ ((im f x) *_ (#1_))` by metis_tac[field_neg_mult, field_one_element] >>
    `_ = $-_ (im f x)` by rw[] >>
    rw[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Isomorphism preserves Addition                                            *)
(* ------------------------------------------------------------------------- *)

(* Note:
   To show that field_iso_map preserves addition, the idea is:
   (1) The two finite fields r and s have their prime fields isomorphic, by:
       finite_field_homo_GF_PF
       finite_field_iso_GF_PF
   (2) Hence (PolyRing (PF r)) and (PolyRing (PF s)) are isomorphic.
   (3) The isomorphism between PolyRing preserves polynomial divisibility.
   (4) Thus, assuming a, b, c IN R+ are related by   a + b = c
       Then  (z ** idx a) + (z ** idx b) = (z ** idx c)
       or z is a root of p = X ** idx a + X ** idx b - X ** idx c
       Since p is an element of (PolyRing (PF r)),
         and q = poly_minimal r (PF r) z is also an element of (PolyRing (PF r))
       Due to z is a root of p, q pdivides p, or
       ?t. t IN (PolyRing (PF r)) with p = t * q.
   (5) By the isomorphism between PolyRing, p' = t' * q' for (PolyRing (PF s)).
       and q' = poly_minimal s (PF s) z'.
       Now z' is a root of q', so z' is also a root of p'.
       Therefore  (z' ** idx a) + (z' ** idx b) = (z' ** idx c)   in (PolyRing (PF s))
       or  a' + b' = c'   in Field s.
*)

(* Theorem: r =| (s,f,s_) |= r_ ==> !x y. x IN R /\ y IN R ==> (im f (x + y) = (im f x) +_ (im f y)) *)
(* Proof:
   If x = #0,
      LHS = im f (#0 + y)
          = im f y            by field_add_lzero
      RHS = (im f #0) +_ (im f y)
          = #0_ +_ (im f y)   by field_iso_map_zero
          = im f y            by field_add_lzero
   If y = #0,
      Similar calculation using field_add_rzero.
   If x <> #0, y <> #0,
      Then x IN R+ /\ y IN R+                    by field_nonzero_eq

       Let z = primitive r, mz = mirror f (primitive r)
      Then mz IN R+_ /\ (forder_ mz = CARD R+_)  by finite_field_primitive_mirror_property
       and mz IN R_                              by field_nonzero_element
       and minimal_ mz = MAP f (minimal z)       by finite_field_element_mirror_poly_minimal

      Step: Consider the sum x + y
       Let t = x + y.
        If t = #0,
      Then y = -x                    by field_add_eq_zero
        so im f y
         = im f (-x)                 by y = -x
         = $-_ (im f x)              by field_iso_map_neg
     Since im f x IN R_ /\ im f y IN R_   by field_iso_map_element
        so im f x + im f y = #0_     by field_add_eq_zero
        or im f x + im f y = im f t  by field_iso_map_zero

        If t <> #0,
      Then x, y, t IN R+                                               by field_nonzero_eq
        so (x = z ** idx x) /\ (y = z ** idx y) /\ (t = z ** idx t)    by field_index_def
       and s <= r, s_ <= _r           by subfield_is_subring

      Step: Consider trinity (idx x) (idx y) (idx t)
       Let p = trinity (idx x) (idx y) (idx t)
             = X ** idx x + X ** idx y - X ** idx t    by notation
      Then x + y = t means
           z ** idx x + z ** idx y = z ** idx t
       ==> root p z                   by poly_trinity_root
     Since Poly s p                   by poly_trinity_spoly
        so (minimal z) pdivides p     by poly_minimal_divides_subfield_poly
      Note moinc (minimal z)          by poly_minimal_monic
        so Monic s (minimal z)        by poly_minimal_spoly, subring_poly_monic_iff
       ==> poly_divides s (minimal z) p      by subring_poly_divides_iff, poly_monic_ulead

      Step: Consider trinity_ (idx x) (idx y) (idx t)
       Let q = trinity_ (idx x) (idx y) (idx t)
      Then p_ = q                            by field_iso_poly_trinity, subring_poly_trinity
      Thus poly_divides s_ (minimal_ mz) q   by field_iso_poly_divides
       ==> (minimal_ mz) pdivides_ q         by subring_poly_divides, poly_minimal_spoly, poly_trinity_spoly

      Step: Conclude by root
       Now root_ (minimal_ mz) mz            by poly_minimal_has_element_root
        so root_ q mz                        by poly_divides_share_root, poly_minimal_poly, poly_trinity_poly
       ==> mz **_ (idx x) +_ mz **_ (idx y) = mz **_ (idx t)    by poly_trinity_root
        or (im f x) +_ (im f y) = im f t     by field_iso_map_def
*)
val field_iso_map_add = store_thm(
  "field_iso_map_add",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==>
   !x y. x IN R /\ y IN R ==> (im f (x + y) = (im f x) +_ (im f y))``,
  rpt (stripDup[iso_subfields_def]) >>
  Cases_on `x = #0` >-
  rw[field_iso_map_zero, field_iso_map_element] >>
  Cases_on `y = #0` >-
  rw[field_iso_map_zero, field_iso_map_element] >>
  `x IN R+ /\ y IN R+` by rw[field_nonzero_eq] >>
  qabbrev_tac `z = primitive r` >>
  qabbrev_tac `mz = mirror f z` >>
  `z IN R` by rw[field_primitive_element, Abbr`z`] >>
  `mz IN R_ /\ (minimal_ mz = MAP f (minimal z))` by metis_tac[finite_field_element_mirror_def] >>
  qabbrev_tac `t = x + y` >>
  `t IN R` by rw[Abbr`t`] >>
  Cases_on `t = #0` >| [
    `im f t = #0_` by rw[field_iso_map_zero] >>
    `y = -x` by rw[GSYM field_add_eq_zero] >>
    `im f y = $-_ (im f x)` by rw_tac std_ss[field_iso_map_neg] >>
    rw[field_add_eq_zero, field_iso_map_element],
    `t IN R+` by rw[field_nonzero_eq] >>
    `(x = z ** idx x) /\ (y = z ** idx y) /\ (t = z ** idx t)` by metis_tac[field_index_def] >>
    `s <= r /\ s_ <= r_` by rw[subfield_is_subring] >>
    qabbrev_tac `p = trinity (idx x) (idx y) (idx t)` >>
    `root p z` by metis_tac[poly_trinity_root] >>
    `Poly s p` by rw_tac std_ss[poly_trinity_spoly, Abbr`p`] >>
    `(minimal z) pdivides p` by rw[poly_minimal_divides_subfield_poly] >>
    `monic (minimal z)` by rw[poly_minimal_monic] >>
    `Monic s (minimal z)` by metis_tac[poly_minimal_spoly, subring_poly_monic_iff] >>
    `Poly s (minimal z)` by rw[] >>
    `poly_divides s (minimal z) p` by metis_tac[subring_poly_divides_iff, poly_monic_ulead] >>
    qabbrev_tac `q = trinity_ (idx x) (idx y) (idx t)` >>
    `p_ = q` by metis_tac[field_iso_poly_trinity, subring_poly_trinity] >>
    `poly_divides s_ (minimal_ mz) q` by metis_tac[field_iso_poly_divides] >>
    `Poly s_ (minimal_ mz)` by rw[poly_minimal_spoly] >>
    `Poly s_ q` by rw[poly_trinity_spoly, Abbr`q`] >>
    `(minimal_ mz) pdivides_ q` by metis_tac[subring_poly_divides] >>
    `root_ (minimal_ mz) mz` by rw[poly_minimal_has_element_root] >>
    `root_ q mz` by metis_tac[poly_divides_share_root, poly_minimal_poly, poly_trinity_poly] >>
    `mz **_ (idx x) +_ mz **_ (idx y) = mz **_ (idx t)` by rw[GSYM poly_trinity_root, Abbr`q`] >>
    rw[field_iso_map_def]
  ]);

(* This is a milestone theorem. *)

(* Theorem: r =| (s,f,s_) |= r_ ==> !x y. x IN R /\ y IN R ==> (im f (x - y) = (im f x) -_ (im f y)) *)
(* Proof:
   Note -y IN R                   by field_neg_element
     im f (x - y)
   = im f (x + -y)                by field_sub_def
   = (im f x) +_ (im f (-y))      by field_iso_map_add
   = (im f x) +_ ($-_ (im f y))   by field_iso_map_neg
   = (im f x) -_ (im f y)         by field_sub_def
*)
val field_iso_map_sub = store_thm(
  "field_iso_map_sub",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==>
   !x y. x IN R /\ y IN R ==> (im f (x - y) = (im f x) -_ (im f y))``,
  rw_tac std_ss[iso_subfields_def, field_neg_element, field_sub_def, field_iso_map_add, field_iso_map_neg]);

(* Theorem: r =| (s,f,s_) |= r_ ==> !x. x IN R ==> !n. im f (x ** n) = (im f x) **_ n *)
(* Proof:
   By induction on n.
   Base: im f (x ** 0) = im f x **_ 0
         im f (x ** 0)
       = im f #1          by field_exp_0
       = #1_              by field_iso_map_one
       = (im f x) **_ 0   by field_exp_0
   Step: im f (x ** n) = im f x **_ n ==> im f (x ** SUC n) = im f x **_ SUC n
       Note x ** n IN R                by field_exp_element
         im f (x ** SUC n)
       = im f (x * x ** n)             by field_exp_SUC
       = (im f x) *_ (im f (x ** n))   by field_iso_map_mult
       = (im f x) *_ (im f x) **_ n    by induction hypothesis
       = (im f x) **_ (SUC n)          by field_exp_SUC
*)
val field_iso_map_exp = store_thm(
  "field_iso_map_exp",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==>
   !x. x IN R ==> !n. im f (x ** n) = (im f x) **_ n``,
  rpt (stripDup[iso_subfields_def]) >>
  Induct_on `n` >-
  rw[field_iso_map_one] >>
  rw[field_iso_map_mult]);

(* Theorem: r =| (s,f,s_) |= r_ ==> !x y. x IN R /\ y IN R /\ (im f x = im f y) ==> (x = y) *)
(* Proof:
   Note im f x IN R_, im f y IN R_     by field_iso_map_element
    and x - y IN R                     by field_sub_element

       im f x = im f y
   <=> (im f x) -_ (im f y) = #0_      by field_sub_eq_zero
   <=>         im f (x - y) = #0_      by field_iso_map_sub
   <=>                x - y = #0       by field_iso_map_eq_zero
   <=>                    x = y        by field_sub_eq_zero
*)
val field_iso_map_eq = store_thm(
  "field_iso_map_eq",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==>
   !x y. x IN R /\ y IN R /\ (im f x = im f y) ==> (x = y)``,
  rpt (stripDup[iso_subfields_def]) >>
  `x - y IN R` by rw[] >>
  `im f x IN R_ /\ im f y IN R_` by rw[field_iso_map_element] >>
  `(im f x = im f y) <=> ((im f x) -_ (im f y) = #0_)` by rw[field_sub_eq_zero] >>
  `_ = (im f (x - y) = #0_)` by rw[field_iso_map_sub] >>
  `_ = (x - y = #0)` by rw[field_iso_map_eq_zero] >>
  `_ = (x = y)` by rw[field_sub_eq_zero] >>
  metis_tac[]);

(* Theorem: r =| (s,f,s_) |= r_ ==> INJ (im f) R R_ *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) x IN R ==> im f x IN R_, true                       by field_iso_map_element
   (2) x IN R /\ y IN R /\ im f x = im f y ==> x = y, true by field_iso_map_eq
*)
val field_iso_map_inj = store_thm(
  "field_iso_map_inj",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==> INJ (im f) R R_``,
  rpt (stripDup[iso_subfields_def]) >>
  rw_tac std_ss[INJ_DEF] >-
  rw[field_iso_map_element] >>
  metis_tac[field_iso_map_eq]);

(* Theorem: r =| (s,f,s_) |= r_ ==> SURJ (im f) R R_ *)
(* Proof:
   Note INJ (im f) R R_      by field_iso_map_inj
    and FINITE R             by FiniteField_def, FiniteField r
    and FINITE R_            by FiniteField_def, FiniteField r_
    and (CARD R = CARD R_)   by given
    ==> SURJ (im f) R R_     by FINITE_INJ_AS_SURJ
*)
val field_iso_map_surj = store_thm(
  "field_iso_map_surj",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==> SURJ (im f) R R_``,
  rpt (stripDup[iso_subfields_def, FiniteField_def]) >>
  (irule FINITE_INJ_AS_SURJ >> simp[]) >>
  rw[field_iso_map_inj]);

(* Theorem: r =| (s,f,s_) |= r_ ==> BIJ (im f) R R_ *)
(* Proof:
   Note INJ (im f) R R_      by field_iso_map_inj
    and SURJ (im f) R R_     by field_iso_map_surj
    ==> BIJ (im f) R R_      by BIJ_DEF
*)
val field_iso_map_bij = store_thm(
  "field_iso_map_bij",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==> BIJ (im f) R R_``,
  rw_tac std_ss[BIJ_DEF, field_iso_map_inj, field_iso_map_surj]);

(* Theorem: r =| (s,f,s_) |= r_ ==> MonoidHomo (im f) r.prod r_.prod *)
(* Proof:
   Note r.prod.carrier = R, r_.prod.carrier = R_                  by field_carriers
   By MonoidHomo_def, this is to show:
   (1) x IN R ==> im f x IN R_, true                              by field_iso_map_element
   (2) x IN R /\ y IN R ==> im f (x * y) = im f x *_ im f y, true by field_iso_map_mult
   (3) im f #1 = #1_, true                                        by field_iso_map_one
*)
val field_iso_map_monoid_homo = store_thm(
  "field_iso_map_monoid_homo",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==> MonoidHomo (im f) r.prod r_.prod``,
  rw_tac std_ss[iso_subfields_def, MonoidHomo_def, field_carriers, field_iso_map_element, field_iso_map_mult, field_iso_map_one]);

(* Theorem: r =| (s,f,s_) |= r_ ==> GroupHomo (im f) r.sum r_.sum *)
(* Proof:
   Note r.sum.carrier = R, r_.sum.carrier = R_                    by field_carriers
   By GroupHomo_def, this is to show:
   (1) x IN R ==> im f x IN R_, true                              by field_iso_map_element
   (2) x IN R /\ y IN R ==> im f (x + y) = im f x +_ im f y, true by field_iso_map_add
*)
val field_iso_map_group_homo = store_thm(
  "field_iso_map_group_homo",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==> GroupHomo (im f) r.sum r_.sum``,
  rw_tac std_ss[iso_subfields_def, GroupHomo_def, field_carriers, field_iso_map_element, field_iso_map_add]);

(* Theorem: r =| (s,f,s_) |= r_ ==> FieldHomo (im f) r r_ *)
(* Proof:
   By FieldHomo_def, RingHomo_def, this is to show:
   (1) x IN R ==> im f x IN R_, true          by field_iso_map_element
   (2) GroupHomo (im f) r.sum r_.sum, true    by field_iso_map_group_homo
   (3) MonoidHomo (im f) r.prod r_.prod, true by field_iso_map_monoid_homo
*)
val field_iso_map_field_homo = store_thm(
  "field_iso_map_field_homo",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==> FieldHomo (im f) r r_``,
  rw_tac std_ss[iso_subfields_def, FieldHomo_def, RingHomo_def, field_iso_map_element, field_iso_map_group_homo, field_iso_map_monoid_homo]);

(* Theorem: r =| (s,f,s_) |= r_ ==> FieldIso (im f) r r_ *)
(* Proof:
   By FieldIso_def, this is to show:
   (1) FieldHomo (im f) r r_, true by field_iso_map_field_homo
   (2) BIJ (im f) R R_, true       by field_iso_map_bij
*)
val field_iso_map_field_iso = store_thm(
  "field_iso_map_field_iso",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==> FieldIso (im f) r r_``,
  rw_tac std_ss[iso_subfields_def, FieldIso_def, field_iso_map_field_homo, field_iso_map_bij]);

(* This is a major milestone theorem. *)

(* Theorem: r =| (s,f,s_) |= r_ ==>
            !p x. Poly s p /\ x IN R ==> (root p x <=> root_ (MAP (im f) p) ((im f) x)) *)
(* Proof:
   Note s <= r                                         by subfield_is_subring
    and poly p                                         by subring_poly_poly
   Also FieldIso (im f) r r_                           by field_iso_map_field_iso
    ==> root p x <=> root_ (MAP (im f) p) ((im f) x)   by field_iso_poly_root_iff
*)
val field_iso_map_spoly_root = store_thm(
  "field_iso_map_spoly_root",
  ``!(r s):'a field (r_ s_):'b field f. r =| (s,f,s_) |= r_ ==>
   !p x. Poly s p /\ x IN R ==> (root p x <=> root_ (MAP (im f) p) ((im f) x))``,
  rpt (stripDup[iso_subfields_def]) >>
  `s <= r` by rw[subfield_is_subring] >>
  `poly p` by metis_tac[subring_poly_poly] >>
  `FieldIso (im f) r r_` by rw[field_iso_map_field_iso] >>
  rw[field_iso_poly_root_iff]);

(* Note: p_ = MAP f p <> MAP (im f) p
This is more useful if root p x <=> root_ p_ ((im f) x), but there is no hope.
Thus this result is regarded as rather ugly.
*)

(* ------------------------------------------------------------------------- *)
(* Uniqueness of Finite Field (Part 2)                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==>
            FieldIso (field_iso_map r (PF r) r_ (PF r_) (##_ #1_ o LINV $## (GF (char r)).carrier)) r r_ *)
(* Proof:
   Note (PF r) <<= r         by prime_field_is_subfield
    and (PF r_) <<= r_       by prime_field_is_subfield
    Now FieldIso (##_ #1_ o LINV $## (GF (char r)).carrier) (PF r) (PF r_)  by finite_field_prime_field_iso
   Thus the result follows   by field_iso_map_field_iso
*)
val finite_field_eq_card_iso = store_thm(
  "finite_field_eq_card_iso",
  ``!(r:'a field) (r_:'b field). FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==>
     FieldIso (field_iso_map r (PF r) r_ (PF r_) (##_ #1_ o LINV $## (GF (char r)).carrier)) r r_``,
  rw_tac std_ss[iso_subfields_def, prime_field_is_subfield, finite_field_prime_field_iso, field_iso_map_field_iso]);

(* Theorem: FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==> (r =ff= r_) *)
(* Proof: by finite_field_eq_card_iso *)
val finite_field_eq_card_isomorphic = store_thm(
  "finite_field_eq_card_isomorphic",
  ``!(r:'a field) (r_:'b field). FiniteField r /\ FiniteField r_ /\ (CARD R = CARD R_) ==> (r =ff= r_)``,
  metis_tac[finite_field_eq_card_iso]);

(* ------------------------------------------------------------------------- *)
(* Useful Isomorphic Theorems                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r ==> !z. monic z /\ ipoly z ==> r =f= (PolyModConst r z) *)
(* Proof:
   By notation, this is to show:
   (1) Field (PolyModConst r z), true by poly_mod_const_field
   (2) ?f. FieldIso f r (PolyModConst r z)
       Note pmonic z                  by poly_monic_irreducible_property
       Take f = up, true              by poly_mod_const_iso_field
*)
val poly_mod_const_isomorphic_field = store_thm(
  "poly_mod_const_isomorphic_field",
  ``!r:'a field. Field r ==> !z. monic z /\ ipoly z ==> r =f= (PolyModConst r z)``,
  rw_tac std_ss[] >-
  rw[poly_mod_const_field] >>
  metis_tac[poly_mod_const_iso_field, poly_monic_irreducible_property]);

(* Theorem: FiniteField r ==> !z. monic z /\ ipoly z ==> r =ff= (PolyModConst r z) *)
(* Proof: by poly_mod_const_finite_field,poly_mod_const_iso_field_alt  *)
val poly_mod_const_isomorphic_finite_field = store_thm(
  "poly_mod_const_isomorphic_finite_field",
  ``!r:'a field. FiniteField r ==> !z. monic z /\ ipoly z ==> r =ff= (PolyModConst r z)``,
  metis_tac[FiniteField_def, poly_mod_const_finite_field, poly_mod_const_iso_field_alt]);

(* Theorem: FiniteField r ==> !z h. monic z /\ ipoly z /\ monic h /\ ipoly h /\ (deg z = deg h) ==>
            ?f. FieldIso f (PolyModRing r z) (PolyModRing r h) *)
(* Proof:
   Note FiniteField (PolyModRing r z)   by poly_mod_irreducible_finite_field
    and FiniteField (PolyModRing r h)   by poly_mod_irreducible_finite_field
    Now 0 < deg z /\ 0 < deg h          by poly_irreducible_deg_nonzero
   Note FiniteRing r                    by finite_field_is_finite_ring
   Thus CARD Rz = CARD R ** deg z       by poly_mod_ring_card, FiniteRing r
    and CARD (PolyModRing r h).carrier = CARD R ** deg h      by poly_mod_ring_card
    ==> CARD (PolyModRing r h).carrier = CARD Rz
   Hence ?f. FieldIso f (PolyModRing r z) (PolyModRing r h)   by finite_field_eq_card_iso
*)
val poly_mod_irreducible_eq_degree_iso = store_thm(
  "poly_mod_irreducible_eq_degree_iso",
  ``!r:'a field. FiniteField r ==> !z h. monic z /\ ipoly z /\ monic h /\ ipoly h /\ (deg z = deg h) ==>
      ?f. FieldIso f (PolyModRing r z) (PolyModRing r h)``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteField (PolyModRing r z)` by rw[poly_mod_irreducible_finite_field] >>
  `FiniteField (PolyModRing r h)` by rw[poly_mod_irreducible_finite_field] >>
  `0 < deg z /\ 0 < deg h` by rw[poly_irreducible_deg_nonzero] >>
  `CARD (PolyModRing r h).carrier = CARD Rz` by rw[poly_mod_ring_card, finite_field_is_finite_ring] >>
  metis_tac[finite_field_eq_card_iso]);

(* ------------------------------------------------------------------------- *)
(* Classification of subfields of Finite Field                               *)
(* ------------------------------------------------------------------------- *)

(* Note: Subgroup in a finite field does not guarantee to give a subfield; that is,
multiplicative closure does not automatically give additive closure.

Example: IN F_9, the cyclic multiplicative group is C_8.
For a cyclic group, each divisor of its cardinality gives a subgroup, so
the C_8 has subgroups: C_1, C_2, C_4, and C_8.
Including back the zero, there are sets of cardinality 2, 3, 5, 9.
But 9 = 3^2, so it has only subfields of cardinality 3^1 = 3, 3^2 = 9.

Let F_9 = {0, a, a^2, a^3, a^4, a^5, a^6, a^7, a^8}, with a^8 = 1.
Then its subfield of 3 elements is G_3 = (F_9)^4 = {0, a^4, a^8}
Furthermore, all elements of F_9 are roots of x^9 - x = 0, where 9 = (char r)^2.
All elements of G_3 are roots of x^3 - x = 0, where 3 = (char)^1.
It is easy to see that G_3 is multiplicative closed:
    * | a^4  a^8 = 1
 ---------------
 a^4  |  1   a^4
 1    | a^4    1, so a^4 = -1

It is not so obvious, but it is true that G_3 is additive closed:

    + | 0   a^4 = -1  a^8 = 1
 ----------------------------
  0   |  0    -1        1
 -1   | -1     1        0
  1   |  1     0       -1

Since for char = 3, -1 + -1 = -2 = 1, 1 + 1 = 2 = -1.
*)

(* ------------------------------------------------------------------------- *)
(* Finite Field Subfield Existence Criterion                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==> !n. (CARD R = char r ** n) ==>
            !m. m divides n <=> ?s. s <<= r /\ (CARD B = char r ** m) *)
(* Proof:
   Let c = char r.
   Then prime c              by finite_field_char
    and 1 < c                by ONE_LT_PRIME
     so 0 < c                by arithmetic

   If part: m divides n ==> ?s. s <<= r /\ (CARD B = c ** m)
      Note 1 < CARD R        by finite_field_card_gt_1
        so n <> 0            by EXP, CARD R = char r ** n, CARD R <> 1

       Now cyclic f*         by finite_field_mult_group_cyclic
       and FINITE R+         by field_nonzero_finite
        or FINITE F*         by field_mult_carrier

       Now CARD F* = CARD R - 1            by finite_field_mult_carrier_card
        so (c ** m - 1) divides CARD F*    by power_predecessor_divisibility, 1 < c
       ==> ?g. g <= f* /\ (CARD G = c ** m - 1)   by cyclic_subgroup_condition

     Let s = subgroup_field r g
     Simplifying by subgroup_field_property, this is to show:
     (1) Field (subgroup_field r g), true    by subgroup_field_field
     (2) subfield (subgroup_field r g) r, true   by subgroup_field_subfield
     (3) CARD (G UNION {#0}) = c ** m
         Note 0 < c ** m                 by EXP_POS, 0 < c
           CARD (G UNION {#0})
         = CARD G + 1                    by field_subgroup_card
         = (c ** m - 1) + 1              by CARD G = c ** m - 1
         = c ** m                        by arithmetic, 0 < c ** m

   Only-if part: ?s. s <<= r /\ (CARD B = c ** m) ==> m divides n
      Note s <<= r
       ==> ?n' m'. 0 < n /\ 0 < m /\
           (CARD R = c ** n') /\ (CARD B = c ** m') /\
            m' divides n'                          by finite_field_subfield_card_property
      With CARD R = c ** n = c ** n' ==> n = n'    by EXP_BASE_INJECTIVE, 1 < c
       and CARD B = c ** m = c ** m' ==> m = m'    by EXP_BASE_INJECTIVE, 1 < c
      Thus m divides n                             by above
*)
val finite_field_subfield_exists = store_thm(
  "finite_field_subfield_exists",
  ``!r:'a field. FiniteField r ==> !n. (CARD R = char r ** n) ==>
   !m. m divides n <=> ?s. s <<= r /\ (CARD B = char r ** m)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `c = char r` >>
  `prime c` by rw[finite_field_char, Abbr`c`] >>
  `1 < c` by rw[ONE_LT_PRIME, Abbr`c`] >>
  rw[EQ_IMP_THM] >| [
    `1 < CARD R` by rw[finite_field_card_gt_1] >>
    `CARD R <> 1` by decide_tac >>
    `n <> 0` by metis_tac[EXP] >>
    `cyclic f*` by rw[finite_field_mult_group_cyclic] >>
    `FINITE F*` by rw[field_nonzero_finite, field_mult_carrier] >>
    `CARD F* = CARD R - 1` by rw[finite_field_mult_carrier_card] >>
    `(c ** m - 1) divides CARD F*` by rw[power_predecessor_divisibility] >>
    `?g. g <= f* /\ (CARD G = c ** m - 1)` by rw[cyclic_subgroup_condition] >>
    qexists_tac `subgroup_field r g` >>
    rw_tac std_ss[subgroup_field_property] >-
    metis_tac[subgroup_field_field] >-
    rw[subgroup_field_subfield] >>
    `0 < c` by decide_tac >>
    `0 < c ** m` by rw[EXP_POS] >>
    `CARD (G UNION {#0}) = (c ** m - 1) + 1` by rw[field_subgroup_card] >>
    decide_tac,
    metis_tac[finite_field_subfield_card_property, EXP_BASE_INJECTIVE]
  ]);

(* Note: This finite_field_subfield_exists_alt just uses finite_field_subfield_exists,
         There should be a better proof. *)

(* Theorem: FiniteField r ==> !n. n divides (fdim r) <=> ?s. s <<= r /\ (fdim s = n) *)
(* Proof:
   If part: n divides fdim r ==> ?s. (Field s /\ subfield s r) /\ (fdim s = n)
      Note CARD R = (char r) ** (fdim r)           by finite_field_card_eqn
       ==> ?s. s <<= r /\ (CARD B = char r ** n)   by finite_field_subfield_exists
       ==> FiniteField s                           by subfield_finite_field
        so char s = char r                         by subfield_char
        or CARD B = char s ** n                    by above
      Thus n = fdim s                              by finite_field_dim_eq
   Only-if part: subfield s r ==> fdim s divides fdim r
      Note FiniteField s                           by subfield_finite_field
       and char s = char r                         by subfield_char
       But CARD R = (char r) ** (fdim r)           by finite_field_card_eqn
       and CARD B = (char s) ** (fdim s)           by finite_field_card_eqn
       ==> (fdim s) divides (fdim r)               by finite_field_subfield_exists
*)
val finite_field_subfield_exists_alt = store_thm(
  "finite_field_subfield_exists_alt",
  ``!r:'a field. FiniteField r ==> !n. n divides (fdim r) <=> ?s. s <<= r /\ (fdim s = n)``,
  rpt (stripDup[FiniteField_def]) >>
  rw[EQ_IMP_THM] >| [
    `CARD R = (char r) ** (fdim r)` by rw[finite_field_card_eqn] >>
    `?s. s <<= r /\ (CARD B = char r ** n)` by metis_tac[finite_field_subfield_exists] >>
    `FiniteField s` by metis_tac[subfield_finite_field] >>
    `char s = char r` by rw[subfield_char] >>
    metis_tac[finite_field_dim_eq],
    `FiniteField s` by metis_tac[subfield_finite_field] >>
    `char s = char r` by rw[subfield_char] >>
    `CARD R = (char r) ** (fdim r)` by rw[finite_field_card_eqn] >>
    `CARD B = (char s) ** (fdim s)` by rw[finite_field_card_eqn] >>
    metis_tac[finite_field_subfield_exists]
  ]);

(* See another proof of finite_field_subfield_exists_alt in ffSplit, as finite_field_subfield_exists_iff. *)

(* Theorem: FiniteField r ==> !b n. (CARD R = b ** n) ==>
            !m. m divides n <=> ?s. s <<= r /\ (CARD B = b ** m) *)
(* Proof:
   Let c = char r.
   Then prime c                          by finite_field_char
    and ?d. 0 < d /\ (CARD R = c ** d)   by finite_field_card
   This gives:
        CARD R = b ** n = c ** d
    ==> ?k. (b = c ** k) /\ (k * n = d)  by power_eq_prime_power, prime c
   Note k <> 0                           by MULT, d <> 0

   If part: m divides n ==> ?s. s <<= r /\ (CARD B = (c ** k) ** m)
      Note b ** m
         = (c ** k) ** m                 by b = c ** k
         = c ** (k * m)                  by EXP_EXP_MULT
      Also m divides n
       ==> (k * m) divides (k * n)       by DIVIDES_MULTIPLE_IFF, k <> 0
      Thus ?s. s <<= r /\
           (CARD B = (c ** k) ** m)      by finite_field_subfield_exists

   Only-if part: subfield s r /\ CARD B = (c ** k) ** m ==> m divides n
      Note 1 < c                         by ONE_LT_PRIME, prime c
           CARD B
         = (c ** k) ** m
         = c ** (k * m)                  by EXP_EXP_MULT
      Thus k * m divides k * n           by finite_field_subfield_card_property, EXP_BASE_INJECTIVE, 1 < c
        or m divides n                   by DIVIDES_MULTIPLE_IFF, k <> 0
*)
val finite_field_subfield_existence = store_thm(
  "finite_field_subfield_existence",
  ``!r:'a field. FiniteField r ==> !b n. (CARD R = b ** n) ==>
   !m. m divides n <=> ?s. s <<= r /\ (CARD B = b ** m)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `c = char r` >>
  `prime c` by rw[finite_field_char, Abbr`c`] >>
  `?d. 0 < d /\ (CARD R = c ** d)` by rw[finite_field_card, Abbr`c`] >>
  `?k. (b = c ** k) /\ (k * n = d)` by rw[power_eq_prime_power] >>
  `d <> 0` by decide_tac >>
  `k <> 0` by metis_tac[MULT] >>
  rw[EQ_IMP_THM] >| [
    `(c ** k) ** m = c ** (k * m)` by rw[EXP_EXP_MULT] >>
    `k * m divides k * n` by metis_tac[DIVIDES_MULTIPLE_IFF] >>
    metis_tac[finite_field_subfield_exists],
    `1 < c` by rw[ONE_LT_PRIME, Abbr`c`] >>
    `(c ** k) ** m = c ** (k * m)` by rw[EXP_EXP_MULT] >>
    `k * m divides k * n` by metis_tac[finite_field_subfield_card_property, EXP_BASE_INJECTIVE] >>
    metis_tac[DIVIDES_MULTIPLE_IFF]
  ]);

(* This is a major theorem for the structure of subfields of finite fields. *)

(* Theorem: FiniteField r /\ (CARD R = (char r) ** n) ==>
            !m. ?s. s <<= r /\ (CARD B = (char r) ** m) <=> m divides n *)
(* Proof: by finite_field_subfield_exists *)
val finite_field_subfield_exists_reverse = store_thm(
  "finite_field_subfield_exists_reverse",
  ``!(r:'a field) n. FiniteField r /\ (CARD R = (char r) ** n) ==>
   !m. ?s. s <<= r /\ (CARD B = (char r) ** m) <=> m divides n``,
  metis_tac[finite_field_subfield_exists]);

(* Theorem: FiniteField r /\ (CARD R = b ** n) ==>
            !m. ?s. s <<= r /\ (CARD B = b ** m) <=> m divides n *)
(* Proof: by finite_field_subfield_existence *)
val finite_field_subfield_existence_reverse = store_thm(
  "finite_field_subfield_existence_reverse",
  ``!(r:'a field) b n. FiniteField r /\ (CARD R = b ** n) ==>
   !m. ?s. s <<= r /\ (CARD B = b ** m) <=> m divides n``,
  metis_tac[finite_field_subfield_existence]);

(* ------------------------------------------------------------------------- *)
(* Cloning Finite Field                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: INFINITE univ(:'b) ==> ?t:'b -> bool. FINITE t /\ (CARD t = CARD s) *)
(* Proof: by finite_set_exists, take n = CARD s. *)
val finite_set_clone_exists = store_thm(
  "finite_set_clone_exists",
  ``!s:'a -> bool. INFINITE univ(:'b) ==> ?t:'b -> bool. FINITE t /\ (CARD t = CARD s)``,
  rw[finite_set_exists]);

(* Apply Skolemization *)
val lemma = prove(
  ``!s:'a -> bool. ?t:'b -> bool. INFINITE univ(:'b) ==> FINITE t /\ (CARD t = CARD s)``,
  metis_tac[finite_set_clone_exists]);
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
(* Define clone of finite set *)
(*
- SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma;
> val it = |- ?f. !s. INFINITE univ(:'b) ==> FINITE (f s) /\ (CARD (f s) = CARD s): thm
*)
val clone_def = new_specification(
    "clone_def",
    ["clone"],
    SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma);
(*
> val clone_def = |- !s. INFINITE univ(:'b) ==> FINITE (clone s) /\ (CARD (clone s) = CARD s): thm
*)

(* Theorem: FINITE s /\ FINITE t /\ (CARD s = CARD t) ==> ?f. BIJ f s t *)
(* Proof:
   Note s =~ t                             by CARDEQ_CARD_EQN
    ==> ?f. BIJ f s t                      by cardeq_def, s =~ t
*)
val eqcard_bij_exists = store_thm(
  "eqcard_bij_exists",
  ``!s t. FINITE s /\ FINITE t /\ (CARD s = CARD t) ==> ?f. BIJ f s t``,
  rw[CARDEQ_CARD_EQN, GSYM cardeq_def]);

(* Apply Skolemization *)
val lemma = prove(
  ``!s t. ?f. FINITE s /\ FINITE t /\ (CARD s = CARD t) ==> BIJ f s t``,
  metis_tac[eqcard_bij_exists]);
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
(* Define bijection between sets of equal size. *)
(*
- SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma;
> val it = |- ?f. !s t. FINITE s /\ FINITE t /\ (CARD s = CARD t) ==> BIJ (f s t) s t: thm
*)
val eqcard_bij_def = new_specification(
    "eqcard_bij_def",
    ["eqcard_bij"],
    SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma);
(*
> val eqcard_bij_def = |- !s t. FINITE s /\ FINITE t /\ (CARD s = CARD t) ==> BIJ (eqcard_bij s t) s t: thm
*)

(* Theorem: FiniteField r /\ INFINITE univ(:'b) ==> ?r_:'b field. FiniteField r_ /\ (CARD R_ = CARD R) *)
(* Proof:
   Step 1: FieldHomo f r (homo_field r f)
   Note FINITE (clone R)                  by clone_def
    and CARD (clone R) = CARD R           by clone_def
   Thus BIJ f R (clone R)                 by eqcard_bij_def
     so INJ f R UNIV                      by BIJ_DEF, INJ_UNIV
   Note fR = IMAGE f R                    by homo_ring_property
     so FINITE fR                         by IMAGE_FINITE
    and CARD fR = CARD R                  by INJ_CARD_IMAGE_EQN, INJ f R univ(:'b)
    ==> FieldHomo f r (homo_field r f)    by homo_field_by_inj, INJ f R univ(:'b)

   Step 2: FiniteField (homo_field r f)
   Note #1 <> #0                           by field_one_ne_zero
     so f #1 <> f #0                       by INJ_DEF
    ==> Field (homo_field r f)             by homo_field_field
   Thus FiniteField (homo_field r f)       by FiniteRing_def, FINITE fR

   Step 3: FieldIso f r (homo_field r f)
   Note FieldHomo f r (homo_field r f)     by above
   just need to show: BIJ f R fR           by FieldIso_def
    Now SURJ f R (clone R)                 by BIJ_DEF
     so IMAGE f R = clone R                by IMAGE_SURJ
   Thus BIJ f R (clone R) ==> BIJ f R fR   by above, fR = IMAGE f R
*)
val finite_field_clone = store_thm(
  "finite_field_clone",
  ``!r:'a field. FiniteField r /\ INFINITE univ(:'b) ==>
   let (f:'a -> 'b) = eqcard_bij R (clone R) in
   FiniteField (homo_field r f) /\ FieldIso f r (homo_field r f)``,
  rpt (stripDup[FiniteField_def]) >>
  `FINITE (clone R)` by rw[clone_def] >>
  `CARD (clone R) = CARD R` by rw[clone_def] >>
  qabbrev_tac `f = eqcard_bij R (clone R)` >>
  `BIJ f R (clone R)` by rw[eqcard_bij_def, Abbr`f`] >>
  `INJ f R UNIV` by metis_tac[BIJ_DEF, INJ_UNIV] >>
  `fR = IMAGE f R` by rw[homo_ring_property] >>
  `FINITE fR` by rw[] >>
  `CARD fR = CARD R` by rw[INJ_CARD_IMAGE_EQN] >>
  `FieldHomo f r (homo_field r f)` by rw[homo_field_by_inj] >>
  rw_tac std_ss[] >| [
    `#0 IN R /\ #1 IN R /\ #1 <> #0` by rw[] >>
    `f #1 <> f #0` by metis_tac[INJ_DEF] >>
    rw[FiniteField_def, homo_field_field],
    rw[FieldIso_def] >>
    `SURJ f R (clone R)` by metis_tac[BIJ_DEF] >>
    `IMAGE f R = clone R` by metis_tac[IMAGE_SURJ |> ISPEC ``f:'a -> 'b`` |> ISPEC ``R`` |> ISPEC ``clone R``] >>
    rw[]
  ]);

(* Theorem: FiniteField r /\ INFINITE univ(:'b) ==> ?(r_:'b field) f. FiniteField r_ /\ FieldIso f r r_ *)
(* Proof: by finite_field_clone, take (homo_field r f) where f = eqcard_bij R (clone R) *)
val finite_field_clone_exists = store_thm(
  "finite_field_clone_exists",
  ``!r:'a field. FiniteField r /\ INFINITE univ(:'b) ==>
   ?(r_:'b field) f. FiniteField r_ /\ FieldIso f r r_``,
  metis_tac[finite_field_clone]);

(* ------------------------------------------------------------------------- *)
(* Bijective Images of Monoid and Ring.                                      *)
(* ------------------------------------------------------------------------- *)

(* Define a monoid bijective image *)
val monoid_bij_image_def = Define `
  monoid_bij_image (f:'a -> 'b) (t:'b -> 'a) (g:'a monoid) =
    <|carrier := IMAGE f G;
           op := (\x y. f (g.op (t x) (t y))); (* display as: op := (\x y. f (t x * t y)) *)
           id := f #e
     |>
`;

(* Define a ring bijective image *)
val ring_bij_image_def = Define `
  ring_bij_image (f:'a -> 'b) (g:'b -> 'a) (r:'a ring) =
     <| carrier := IMAGE f R;
            sum := monoid_bij_image f g r.sum;
           prod := monoid_bij_image f g r.prod
      |>
`;

(* Given a Monoid g, and two functions f t that undo each other,
   Then (f g) is a Monoid, with op := (\x y. f (t x * t y))      *)
(* Given a Monoid g, and a bijective function f,
   Then (f g) is a Monoid, with op := (\x y. f (f^-1 x * f^-1 y))  *)
(* Theorem: Monoid g /\ (!x. f (t x) = x) /\ (!y. t (f y) = y) ==>
            Monoid (monoid_bij_image f t g) *)
(* Proof:
   By Monoid_def, monoid_bij_image_def, this is to show:
   (1) x IN IMAGE f G /\ y IN IMAGE f G ==> f (t x * t y) IN IMAGE f G
       ?a. (x = f a) /\ a IN G       by IN_IMAGE
       ?b. (y = f b) /\ b IN G       by IN_IMAGE
       Hence  f (t x * t y)
            = f (t (f a) * t (f b))  by x = f a, y = f b
            = f (a * b)              by !y. t (f y) = y
       Since a * b IN G              by monoid_op_element
       f (a * b) IN IMAGE f G        by IN_IMAGE
   (2) x IN IMAGE f G /\ y IN IMAGE f G /\ z IN IMAGE f G ==> f (t x * t y * t z) = f (t x * (t y * t z))
       ?a. (x = f a) /\ a IN G       by IN_IMAGE
       ?b. (y = f b) /\ b IN G       by IN_IMAGE
       ?c. (z = f c) /\ c IN G       by IN_IMAGE
       Hence  t x * t y * t z
            = t (f a) * t (f b) * t (f c)    by x = f a, y = f b, z = f c
            = a * b * c                      by !y. t (f y) = y
            = a * (b * c)                    by monoid_assoc
            = t (f a) * (t (f b) * t (f c))  by !y. t (f y) = y
            = t x * (t y * t z)              by x = f a, y = f b, z = f c
       or f (t x * t y * t z) = f (t x * (t y * t z))
   (3) f #e IN IMAGE f G
       Since #e IN G          by monoid_id_element
       f #e IN IMAGE f G      by IN_IMAGE
   (4) x IN IMAGE f G ==> f (#e * t x) = x
       ?a. (x = f a) /\ a IN G       by IN_IMAGE
       Hence f (#e * t x)
           = f (#e * t (f a))        by x = f a
           = f (#e * a)              by !y. t (f y) = y
           = f a                     by monoid_id
           = x                       by x = f a
   (5) x IN IMAGE f G ==> f (t x * #e) = x
       ?a. (x = f a) /\ a IN G       by IN_IMAGE
       Hence f (t x * #e)
           = f (t (f a) * #e)        by x = f a
           = f (a * #e)              by !y. t (f y) = y
           = f a                     by monoid_id
           = x                       by x = f a
*)
val monoid_bij_image_monoid = store_thm(
  "monoid_bij_image_monoid",
  ``!(g:'a monoid) (f:'a -> 'b) (t:'b -> 'a). Monoid g /\ (!x. f (t x) = x) /\ (!y. t (f y) = y) ==>
     Monoid (monoid_bij_image f t g)``,
  rpt strip_tac >>
  rw_tac std_ss[Monoid_def, monoid_bij_image_def] >| [
    `?a. (x = f a) /\ a IN G` by rw[GSYM IN_IMAGE] >>
    `?b. (y = f b) /\ b IN G` by rw[GSYM IN_IMAGE] >>
    rw[],
    `?a. (x = f a) /\ a IN G` by rw[GSYM IN_IMAGE] >>
    `?b. (y = f b) /\ b IN G` by rw[GSYM IN_IMAGE] >>
    `?c. (z = f c) /\ c IN G` by rw[GSYM IN_IMAGE] >>
    rw[monoid_assoc],
    rw[],
    `?a. (x = f a) /\ a IN G` by rw[GSYM IN_IMAGE] >>
    rw[],
    `?a. (x = f a) /\ a IN G` by rw[GSYM IN_IMAGE] >>
    rw[]
  ]);

(* Given a Group g, and two functions f t that undo each other,
   Then (f g) is a Group, with op := (\x y. f (t x * t y))      *)
(* Given a Group g, and a bijective function f,
   Then (f g) is a Group, with op := (\x y. f (f^-1 x * f^-1 y))  *)
(* Theorem: Group g /\ (!x. f (t x) = x) /\ (!y. t (f y) = y) ==>
            Group (monoid_bij_image f t g) *)
(* Proof:
   By Group_def, this is to show:
   (1) Group g ==> Monoid (monoid_bij_image f t g)
       Group g ==> Monoid g                         by group_is_monoid
               ==> Monoid (monoid_bij_image f t g)  by monoid_bij_image_monoid
   (2) x' IN G ==> ?y. (?x. (y = f x) /\ x IN G) /\
                   (f (t (f x') * t y) = f #e) /\ (f (t y * t (f x')) = f #e)
       x' IN G ==> |/ x' IN G    by group_inv_element
       Let y = f ( |/ x')
       Then y = f x  with x = |/ x', and x IN G
        and f (t (f x') * t y)
          = f (t (f x') * t (f ( |/ x')))  by y = f ( |/ x')
          = f (x' * |/ x')                 by !y. t (f y) = y
          = f #e                           by group_inv_thm
        and f (t y * t (f x'))
          = f (t (f ( |/ x')) * t (f x'))  by y = f ( |/ x')
          = f ( |/ x' * x')                by !y. t (f y) = y
          = f #e                           by group_inv_thm
*)
val monoid_bij_image_group = store_thm(
  "monoid_bij_image_group",
  ``!(g:'a group) (f:'a -> 'b) (t:'b -> 'a). Group g /\ (!x. f (t x) = x) /\ (!y. t (f y) = y) ==>
     Group (monoid_bij_image f t g)``,
  rpt strip_tac >>
  rw_tac std_ss[Group_def] >-
  rw[monoid_bij_image_monoid] >>
  rw[monoid_invertibles_def, monoid_bij_image_def, EXTENSION, EQ_IMP_THM] >>
  `g.inv x' IN G` by rw[] >>
  qexists_tac `f (g.inv x')` >>
  metis_tac[group_inv_thm]);

(* Theorem: AbelianMonoid g /\ (!x. f (t x) = x) /\ (!y. t (f y) = y) ==>
            AbelianMonoid (monoid_bij_image f t g) *)
(* Proof:
   By AbelianMonoid_def, this is to show:
   (1) Monoid g ==> Monoid (monoid_bij_image f t g)
       True by monoid_bij_image_monoid.
   (2) x' IN G /\ x'' IN G /\ !x y. x IN G /\ y IN G ==> (x * y = y * x)
       ==> f (t (f x') * t (f x'')) = f (t (f x'') * t (f x'))
         f (t (f x') * t (f x''))
       = f (x' * x'')               by !y. t (f y) = y
       = f (x'' * x')               by commutativity condition
       = f (t (f x'') * t (f x'))   by !y. t (f y) = y
*)
val monoid_bij_image_abelian_monoid = store_thm(
  "monoid_bij_image_abelian_monoid",
  ``!(g:'a monoid) (f:'a -> 'b) (t:'b -> 'a). AbelianMonoid g /\ (!x. f (t x) = x) /\ (!y. t (f y) = y) ==>
     AbelianMonoid (monoid_bij_image f t g)``,
  rw[AbelianMonoid_def] >-
  rw[monoid_bij_image_monoid] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw[monoid_bij_image_def] >>
  rw[]);


(* Theorem: AbelianGroup g /\ (!x. f (t x) = x) /\ (!y. t (f y) = y) ==>
            AbelianGroup (monoid_bij_image f t g) *)
(* Proof:
   By AbelianGroup_def, this is to show:
   (1) Group g ==> Group (monoid_bij_image f t g)
       True by monoid_bij_image_group.
   (2) x' IN G /\ x'' IN G /\ !x y. x IN G /\ y IN G ==> (x * y = y * x)
       ==> f (t (f x') * t (f x'')) = f (t (f x'') * t (f x'))
         f (t (f x') * t (f x''))
       = f (x' * x'')               by !y. t (f y) = y
       = f (x'' * x')               by commutativity condition
       = f (t (f x'') * t (f x'))   by !y. t (f y) = y
*)
val monoid_bij_image_abelian_group = store_thm(
  "monoid_bij_image_abelian_group",
  ``!(g:'a group) (f:'a -> 'b) (t:'b -> 'a). AbelianGroup g /\ (!x. f (t x) = x) /\ (!y. t (f y) = y) ==>
     AbelianGroup (monoid_bij_image f t g)``,
  rw[AbelianGroup_def] >-
  rw[monoid_bij_image_group] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw[monoid_bij_image_def] >>
  rw[]);

(* Theorem: Ring r /\ (!x. f (g x) = x) /\ (!y. g (f y) = y) ==>
   (monoid_bij_image f g f* = monoid_bij_image f g r.prod excluding (monoid_bij_image f g r.sum).id) *)
(* Proof:
   By monoid_bij_image_def and excluding_def, this is to show:
      IMAGE f (R DIFF {#0}) = IMAGE f R DIFF {f #0}
   Expanding by definitions, this is to show:
   (1) x' IN R ==> ?x. (f x' = f x) /\ x IN R, true by taking x = x'.
   (2) x' IN R /\ x' <> #0 ==> f x' <> f #0
       By contradiction. Assume f x' = f #0.
       Then g (f x') = g (f #0),
         or      x' = #0            by !y. g (f y) = y
       which contradicts x' <> #0.
   (3) x' IN R /\ f x' <> f #0 ==> ?x''. (f x' = f x'') /\ x'' IN R /\ x'' <> #0
       Since x' = #0 ==>  f x' = f #0, the given means x' <> #0.
       Hence true by taking x'' = x'.
*)
val monoid_bij_image_with_excluding = store_thm(
  "monoid_bij_image_with_excluding",
  ``!(r:'a ring) (f:'a -> 'b) (g:'b -> 'a). Ring r /\ (!x. f (g x) = x) /\ (!y. g (f y) = y) ==>
   (monoid_bij_image f g f* = monoid_bij_image f g r.prod excluding (monoid_bij_image f g r.sum).id)``,
  rw[monoid_bij_image_def, excluding_def] >>
  rw[IMAGE_DEF, DIFF_DEF, EXTENSION, EQ_IMP_THM] >> metis_tac[]);

(* Given a Ring r, and two functions f g that undo each other,
   Then (f r) is a Ring, with op := (\x y. f (g x * g y))      *)
(* Given a Ring r, and a bijective function f,
   Then (f r) is a Ring, with op := (\x y. f (f^-1 x * f^-1 y))  *)
(* Theorem: Ring r /\ (!x. f (g x) = x) /\ (!y. g (f y) = y) ==>
            Ring (ring_bij_image f g r) *)
(* Proof:
   By Ring_def and ring_bij_image_def, this is to show:
   (1) AbelianGroup (monoid_bij_image f g r.sum)
           Ring r
       ==> AbelianGroup (r.sum)                         by ring_add_abelian_group
       ==> AbelianGroup (monoid_bij_image f g r.sum)    by monoid_bij_image_abelian_group
   (2) AbelianMonoid (monoid_bij_image f g r.prod)
           Ring r
       ==> AbelianMonoid (r.prod)                       by ring_mult_abelian_monoid
       ==> AbelianMonoid (monoid_bij_image f g r.prod)  by monoid_bij_image_abelian_monoid
   (3) (monoid_bij_image f g r.sum).carrier = IMAGE f R
         (monoid_bij_image f g r.sum).carrier
       = IMAGE f r.sum.carrier                          by monoid_bij_image_def
       = IMAGE f R                                      by ring_carriers
   (4) (monoid_bij_image f g r.prod).carrier = IMAGE f R
         (monoid_bij_image f g r.prod).carrier
       = IMAGE f r.prod.carrier                         by monoid_bij_image_def
       = IMAGE f R                                      by ring_carriers
   (5) x IN IMAGE f R /\ y IN IMAGE f R /\ z IN IMAGE f R ==>
       f (g x * (g y + g z)) = f (g x * g y + g x * g z)
       ?a. (x = f a) /\ a IN R       by IN_IMAGE
       ?b. (y = f b) /\ b IN R       by IN_IMAGE
       ?c. (z = f c) /\ c IN R       by IN_IMAGE
       Hence  g x * (g y + g z)
            = g (f a) * (g (f b) + g (f c))           by x = f a, y = f b, z = f c
            = a * (b + c)                             by !y. g (f y) = y
            = a * b + a * c                           by ring_mult_ladd
            = g (f a) * g (f b) + g (f a) * g (f c)   by !x. f (g x) = x
            = g x * g y + g x * g z                   by x = f a, y = f b, z = f c
       or f (g x * (g y + g z)) = f (g x * g y + g x * g z)
*)
val ring_bij_image_ring = store_thm(
  "ring_bij_image_ring",
  ``!(r:'a ring) (f:'a -> 'b) (g:'b -> 'a). Ring r /\ (!x. f (g x) = x) /\ (!y. g (f y) = y) ==>
     Ring (ring_bij_image f g r)``,
  rpt strip_tac >>
  rw_tac std_ss[Ring_def, ring_bij_image_def] >-
  rw[ring_add_abelian_group, monoid_bij_image_abelian_group] >-
  rw[ring_mult_abelian_monoid, monoid_bij_image_abelian_monoid] >-
  rw[monoid_bij_image_def] >-
  rw[monoid_bij_image_def] >>
  rw[monoid_bij_image_def] >>
  `?a. (x = f a) /\ a IN R` by rw[GSYM IN_IMAGE] >>
  `?b. (y = f b) /\ b IN R` by rw[GSYM IN_IMAGE] >>
  `?c. (z = f c) /\ c IN R` by rw[GSYM IN_IMAGE] >>
  rw[ring_mult_ladd]);

(* Given a Field r, and two functions f g that undo each other,
   Then (f r) is a Field, with op := (\x y. f (g x * g y))      *)
(* Given a Field r, and a bijective function f,
   Then (f r) is a Monoid, with op := (\x y. f (f^-1 x * f^-1 y))  *)
(* Theorem: Field r /\ (!x. f (g x) = x) /\ (!y. g (f y) = y) ==>
            Field (ring_bij_image f g r) *)
(* Proof:
   By Field_def, this is to show:
   (1) Ring (ring_bij_image f g r)
           Field r
       ==> Ring r                        by field_is_ring
       ==> Ring (ring_bij_image f g r)   by ring_bij_image_ring
   (2) Group ((ring_bij_image f g r).prod excluding (ring_bij_image f g r).sum.id)
           Field r
       ==> Group f*  by Field_def
       ==> Group (monoid_bij_image f g f* )   by monoid_bij_image_group
       ==> Group ((ring_bij_image f g r).prod excluding (ring_bij_image f g r).sum.id)
                                              by monoid_bij_image_with_excluding, field_is_ring
*)
val ring_bij_image_field = store_thm(
  "ring_bij_image_field",
  ``!(r:'a field) (f:'a -> 'b) (g:'b -> 'a). Field r /\ (!x. f (g x) = x) /\ (!y. g (f y) = y) ==>
     Field (ring_bij_image f g r)``,
  rpt strip_tac >>
  rw[Field_def, ring_bij_image_def, ring_bij_image_ring] >>
  metis_tac[Field_def, monoid_bij_image_group, monoid_bij_image_with_excluding]);

(* Theorem: Field r /\ (!x. f (g x) = x) /\ (!y. g (f y) = y) ==>
            FieldIso f r (ring_bij_image f g r) *)
(* Proof:
   By FieldIso_def, this is to show:
   (1) FieldHomo f r (ring_bij_image f g r)
       By FieldHomo_def and RingHomo_def, this is to show:
       (1) f x IN (ring_bij_image f g r).carrier
           This is to show f x IN IMAGE f R    by ring_bij_image_def
                     which is true             by IN_IMAGE
       (2) GroupHomo f r.sum (ring_bij_image f g r).sum
           True by GroupHomo_def, ring_bij_image_def, monoid_bij_image_def.
       (3) MonoidHomo f r.prod (ring_bij_image f g r).prod
           True by MonoidHomo_def, ring_bij_image_def, monoid_bij_image_def.
   (2) BIJ f R (ring_bij_image f g r).carrier
       By BIJ_DEF and INJ_DEF and SURJ_DEF, this is to show:
       (1) f x IN (ring_bij_image f g r).carrier, true by above.
       (2) f x = f y ==> x = y, true by !y. g (f y) = y.
       (3) same as (1)
       (4) x IN (ring_bij_image f g r).carrier ==> ?y. y IN R /\ (f y = x)
           That is, x IN IMAGE f R             by ring_bij_image_def
           ?a. x = f a /\ a IN R               by IN_IMAGE
           Hence true by taking y = a.
*)
val ring_bij_image_field_iso = store_thm(
  "ring_bij_image_field_iso",
  ``!(r:'a field) (f:'a -> 'b) (g:'b -> 'a). Field r /\ (!x. f (g x) = x) /\ (!y. g (f y) = y) ==>
     FieldIso f r (ring_bij_image f g r)``,
  rw[FieldIso_def] >| [
    rw[FieldHomo_def, RingHomo_def] >-
    rw[ring_bij_image_def] >-
    rw[GroupHomo_def, ring_bij_image_def, monoid_bij_image_def] >>
    rw[MonoidHomo_def, ring_bij_image_def, monoid_bij_image_def],
    rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >-
    rw[ring_bij_image_def] >-
    metis_tac[] >-
    rw[ring_bij_image_def] >>
    full_simp_tac (srw_ss())[ring_bij_image_def] >>
    metis_tac[]
  ]);

(* Theorem: univ(:'a) =~ univ(:'b) ==>
            !r:'a field. Field r ==> ?(s:'b field) f. Field s /\ FieldIso f r s *)
(* Proof:
   By cardeq_def and BIJ_IFF_INV, this is to show: ?s f. Field s /\ FieldIso f r s
   Let s = ring_bij_image f g r, using the same f.
   This reduces to show: Field r /\ !x. f (g x) = x /\ !x. g (f x) = x ==>
                         Field (ring_bij_image f g r) /\ FieldIso f r (ring_bij_image f g r)
   Field (ring_bij_image f g r)          by ring_bij_image_field.
   FieldIso f r (ring_bij_image f g r)   by ring_bij_image_field_iso
*)
val field_exists_with_iso = store_thm(
  "field_exists_with_iso",
  ``univ(:'a) =~ univ(:'b) ==> !r:'a field. Field r ==> ?(s:'b field) f. Field s /\ FieldIso f r s``,
  rw[cardeq_def, BIJ_IFF_INV] >>
  qexists_tac `ring_bij_image f g r` >>
  qexists_tac `f` >>
  rw[ring_bij_image_field, ring_bij_image_field_iso]);

(*
use BIJ_IFF_INV
INFINITE_A_list_BIJ_A
DB.match [] ``list``;
*)

(* ------------------------------------------------------------------------- *)
(* Nonlinear Monic Irreducible factor of (unity n) with order X = n          *)
(* ------------------------------------------------------------------------- *)

(*
> poly_unity_special_subfield_factor |> ISPEC ``t:'a poly field`` |> ISPEC ``st:'a poly field``;
val it = |- FiniteField t /\ st <<= t /\ 1 < (t <:> st) ==>
   !n. 1 < n /\ coprime n (CARD st.carrier) /\
     (ordz n (CARD st.carrier) = t <:> st) ==>
     ?h. Monic t h /\ IPoly st h /\ poly_divides t h (Unity t n) /\ 1 < Deg t h /\
       poly_roots t h SUBSET orders (t.prod excluding t.sum.id) n:
   thm
*)

(*
> poly_unity_special_subfield_factor;
val it = |- !r s. FiniteField r /\ s <<= r /\ 1 < (r <:> s) ==>
            !n. 1 < n /\ coprime n (CARD B) /\ (ordz n (CARD B) = r <:> s) ==>
       ?h. monic h /\ IPoly s h /\ h pdivides unity n /\ 1 < deg h /\ roots h SUBSET orders f* n: thm
*)

(* Theorem: FiniteField r ==> !n. 0 < n /\ 1 < ordz n (CARD R) ==>
            ?h. mifactor h (unity n) /\ (deg h = ordz n (CARD R)) /\
            (poly_roots (PolyModRing r h) (lift h)) SUBSET (orders ((PolyModRing r h).prod excluding |0|) n) *)
(* Proof:
   Let d = ordz n (CARD R).
   Since 1 < d, so n <> 1, or 1 < n              by ZN_order_mod_1, d <> 1
   Note ordz n (CARD R) <> 0                     by 1 < ordz n (CARD R)
     so coprime n (CARD R)                       by ZN_order_eq_0, 0 < n

   Step 1: get a field/subfield pair.
   Since 1 < d ==> 0 < d,
     ==> ?z. monic z /\ ipoly z /\ (deg z = d)   by poly_monic_irreducible_exists, 0 < d
     and pmonic z                                by poly_monic_irreducible_property

   Construct a field/subfield pair by z:
   Let t = PolyModRing r z, st = PolyModConst r z.
   Then FiniteField t                by poly_mod_irreducible_finite_field
     or Field t                      by finite_field_is_field
   also Field st                     by poly_mod_const_field
     so st <<= t                     by poly_mod_const_subfield_poly_mod
    and st <= t                      by subfield_is_subring
   Note (t <:> st) = deg z           by poly_mod_const_subfield_dim
    and CARD R = CARD st.carrier     by poly_mod_const_subfield_card
    and t.sum.id = |0|               by poly_mod_ring_ids

   Step 2: get a minimal polynomial k in st <<= t.
   With 1 < n /\ (ordz n (CARD B) = r <:> s) /\ coprime n (CARD R)  by given
    ==> n divides CARD (ring_nonzero t)            by subfield_card_coprime_iff
     so orders (t.prod excluding |0|) n <> {}      by finite_field_orders_nonempty_iff
    ==> ?x. x IN orders (t.prod excluding |0|) n   by MEMBER_NOT_EMPTY
   This gives the following properties of x:
        x IN ring_nonzero t /\
        (order (t.prod excluding |0|) x = n)       by field_orders_element_property
    and x IN t.carrier /\ x <> |0|                 by field_nonzero_eq
   also x <> t.prod.id                             by field_order_eq_1, n <> 1

    Let k = poly_minimal t st x.
   Derive properties of k:
   Note Poly st k                    by poly_minimal_spoly, x IN t.carrier
    and IPoly st k                   by poly_minimal_subfield_irreducible
    and Monic t k                    by poly_minimal_monic
    and Deg t k = d                  by poly_minimal_deg_eqn, x IN t.carrier /\ x <> t.prod.id
   also poly_divides t k (Unity t n) by poly_minimal_divides_unity_order

   Step 3: Use this k to get h such that k = lift h
   Note FieldIso up r st             by poly_mod_const_iso_field
    ==> FieldIso (LINV up R) st r    by field_iso_sym, useful later
   Hence ?h. poly h /\ (lift h = k)  by field_iso_inverse_poly, poly_lift_def, Poly st k, FieldIso up r st
     ==> deg h = d                   by poly_mod_lift_deg
     and MAP (LINV up R) k = h       by field_iso_poly_inv, poly_lift_def

   Now work on other subgoals for h, already have deg h = d.

   Step 4: show monic h
   Note Monic t k
    ==> Monic st k                   by subring_poly_monic_iff
    ==> monic h                      by field_iso_poly_monic

   Step 5: show ipoly h
   Note ipoly (MAP (LINV up R) k)    by field_iso_poly_irreducible, IPoly st k
     or ipoly h                      by above

   Step 6: show (unity n) % h = |0|
   Note ulead h                      by poly_monic_irreducible_property
    and Poly st (Unity t n)          by poly_unity_spoly
     so poly_divides st k (Unity t n)          by subring_poly_divides_iff, poly_monic_ulead, poly_divides t k (Unity t n)
   Note MAP (LINV up R) (Unity t n) = unity n  by subring_poly_unity, field_iso_poly_unity
     so (MAP (LINV up R) k) pdivides (MAP (LINV up R) (Unity t n))    by field_iso_poly_divides_iff
     or h pdivides (unity n)         by above
    ==> (unity n) % h = |0|          by poly_divides_alt, ulead h

   Step 7: setup another field/subfield pair based on h.
   Let u = PolyModRing r h, su = PolyModConst r h.
   Establish the pattern: t =| (st, I, su) |= u.

   Note FiniteField u                by poly_mod_irreducible_finite_field
     so Field u                      by finite_field_is_field
    and Field su                     by poly_mod_const_field
    ==> su <<= u                     by poly_mod_const_subfield_poly_mod
   Also FieldIso up r su             by poly_mod_const_iso_field
   With FieldIso up r st             by above
    ==> FieldIso I st su             by field_iso_eq
    Now CARD t.carrier = CARD R ** deg z     by poly_mod_ring_card, finite_field_is_finite_ring
    and CARD u.carrier = CARD R ** deg h     by poly_mod_ring_card, finite_field_is_finite_ring
   Hence t =| (st, I, su) |= u               by above, FiniteField t, FiniteField u

   The goal is now: poly_roots u k SUBSET orders (u.prod excluding |0|) n

   Step 8: Apply t =| (st, I, su) |= u and k = poly_minimal t st x to get this result.
   Let s = orders (u.prod excluding |0|) n.
   The goal becomes: poly_roots u k SUBSET s.

   Let f = finite_field_element_mirror t st u su I.
   Then poly_minimal u su (f x) = MAP I (poly_minimal t st x)  by finite_field_element_mirror_poly_minimal
     or k = poly_minimal u su (f x)  by MAP_ID
     so f x IN u.carrier             by finite_field_element_mirror_element
    and poly_roots u k = ring_conjugates u su (f x)   by poly_minimal_roots

   Replace the goal by:
        !y. y IN (poly_roots u k) ==> y IN s      by SUBSET_DEF
   Note u.sum.id = |0|                            by poly_mod_ring_ids
    Now order (u.prod excluding |0|) (f x) = n    by finite_field_element_mirror_order
    and (f x) <> |0|                              by finite_field_element_mirror_eq_zero
     so (f x) IN ring_nonzero u                   by field_nonzero_eq
    ==> (f x) IN s                                by field_orders_element_property
   With y IN (poly_roots u k)                     by given
     so y IN ring_conjugates u su (f x)           by above
    ==> order (u.prod excluding |0|) y = n        by finite_field_conjugates_member_order
   Note y <> |0|                                  by finite_field_conjugates_has_zero, f x <> |0|
    but y IN u.carrier                            by poly_roots_member, y IN (poly_roots u k)
     so y IN ring_nonzero u                       by field_nonzero_eq
    ==> y IN s                                    by field_orders_element_property
*)
val poly_unity_special_factor_exists_0 = store_thm(
  "poly_unity_special_factor_exists_0",
  ``!r:'a field. FiniteField r ==> !n. 0 < n /\ 1 < ordz n (CARD R) ==>
   ?h. mifactor h (unity n) /\ (deg h = ordz n (CARD R)) /\
    (poly_roots (PolyModRing r h) (lift h)) SUBSET (orders ((PolyModRing r h).prod excluding |0|) n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `d = ordz n (CARD R)` >>
  `0 < d /\ d <> 1` by decide_tac >>
  `n <> 1` by metis_tac[ZN_order_mod_1] >>
  `coprime n (CARD R)` by metis_tac[ZN_order_eq_0, DECIDE``1 < n ==> n <> 0``] >>
  `?z. monic z /\ ipoly z /\ (deg z = d)` by rw[poly_monic_irreducible_exists] >>
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
  `t.sum.id = |0|` by rw[poly_mod_ring_ids, Abbr`t`] >>
  `n divides CARD (ring_nonzero t)` by metis_tac[subfield_card_coprime_iff] >>
  `orders (t.prod excluding t.sum.id) n <> {}` by rw[GSYM finite_field_orders_nonempty_iff] >>
  `?x. x IN orders (t.prod excluding t.sum.id) n` by rw[MEMBER_NOT_EMPTY] >>
  `x IN ring_nonzero t /\ (order (t.prod excluding t.sum.id) x = n)` by metis_tac[field_orders_element_property] >>
  `x IN t.carrier /\ x <> t.sum.id` by metis_tac[field_nonzero_eq] >>
  `x <> t.prod.id` by metis_tac[field_order_eq_1] >>
  qabbrev_tac `k = poly_minimal t st x` >>
  `Poly st k` by rw[poly_minimal_spoly, Abbr`k`] >>
  `IPoly st k` by rw[poly_minimal_subfield_irreducible, Abbr`k`] >>
  `Monic t k` by rw[poly_minimal_monic, Abbr`k`] >>
  `Deg t k = d` by metis_tac[poly_minimal_deg_eqn] >>
  `poly_divides t k (Unity t n)` by rw[poly_minimal_divides_unity_order, Abbr`k`] >>
  `FieldIso up r st` by rw[poly_mod_const_iso_field, Abbr`st`] >>
  `FieldIso (LINV up R) st r` by rw[field_iso_sym] >>
  `?h. poly h /\ (lift h = k)` by metis_tac[field_iso_inverse_poly, poly_lift_def] >>
  `deg h = d` by metis_tac[field_orders_element_property, poly_mod_lift_deg] >>
  `MAP (LINV up R) k = h` by metis_tac[field_iso_poly_inv, poly_lift_def] >>
  `Monic st k` by metis_tac[subring_poly_monic_iff] >>
  `monic h` by metis_tac[field_iso_poly_monic] >>
  `ipoly h` by metis_tac[field_iso_poly_irreducible] >>
  qexists_tac `h` >>
  rpt strip_tac >-
  rw_tac std_ss[] >-
  rw_tac std_ss[] >-
 (`ulead h` by rw[poly_monic_irreducible_property] >>
  `Poly st (Unity t n)` by rw[poly_unity_spoly] >>
  `poly_divides st k (Unity t n)` by metis_tac[subring_poly_divides_iff, poly_monic_ulead] >>
  `MAP (LINV up R) (Unity t n) = unity n` by metis_tac[subring_poly_unity, field_iso_poly_unity] >>
  `h pdivides (unity n)` by prove_tac[field_iso_poly_divides_iff] >>
  rw[GSYM poly_divides_alt]) >-
  rw_tac std_ss[] >>
  qabbrev_tac `u = PolyModRing r h` >>
  qabbrev_tac `su = PolyModConst r h` >>
  `FiniteField u` by rw[poly_mod_irreducible_finite_field, Abbr`u`] >>
  `Field u` by rw[finite_field_is_field] >>
  `Field su` by rw[poly_mod_const_field, Abbr`su`] >>
  `su <<= u` by rw[poly_mod_const_subfield_poly_mod, Abbr`u`, Abbr`su`] >>
  `FieldIso up r su` by rw[poly_mod_const_iso_field, Abbr`su`] >>
  `FieldIso I st su` by metis_tac[field_iso_eq] >>
  `CARD t.carrier = CARD R ** deg z` by rw[poly_mod_ring_card, finite_field_is_finite_ring, Abbr`t`] >>
  `CARD u.carrier = CARD R ** deg h` by rw[poly_mod_ring_card, finite_field_is_finite_ring, Abbr`u`] >>
  `t =| (st, I, su) |= u` by rw[] >>
  qabbrev_tac `s = orders (u.prod excluding |0|) n` >>
  `poly_roots u k SUBSET s` suffices_by rw[] >>
  qabbrev_tac `f = finite_field_element_mirror t st u su I` >>
  `k = poly_minimal u su (f x)` by rw[finite_field_element_mirror_poly_minimal, Abbr`k`, Abbr`f`] >>
  `f x IN u.carrier` by rw[finite_field_element_mirror_element, Abbr`f`] >>
  `poly_roots u k = ring_conjugates u su (f x)` by rw[poly_minimal_roots] >>
  `!y. y IN (poly_roots u k) ==> y IN s` suffices_by rw[SUBSET_DEF] >>
  rpt strip_tac >>
  `u.sum.id = |0|` by rw[poly_mod_ring_ids, Abbr`u`] >>
  `order (u.prod excluding u.sum.id) (f x) = n` by rw[finite_field_element_mirror_order, Abbr`f`] >>
  `(f x) <> u.sum.id` by metis_tac[finite_field_element_mirror_eq_zero] >>
  `(f x) IN ring_nonzero u` by metis_tac[field_nonzero_eq] >>
  `(f x) IN s` by metis_tac[field_orders_element_property] >>
  `order (u.prod excluding u.sum.id) y = n` by metis_tac[finite_field_conjugates_member_order] >>
  `y <> u.sum.id` by metis_tac[finite_field_conjugates_has_zero] >>
  `y IN u.carrier` by metis_tac[poly_roots_member] >>
  metis_tac[field_orders_element_property, field_nonzero_eq]);

(* This is a milestone theorem, up to 75 assertion lines! *)

(* Theorem: FiniteField r ==> !n. 0 < n /\ 1 < ordz n (CARD R) ==>
            ?z. mifactor z (unity n) /\ (deg z = ordz n (CARD R)) /\ (forderz X = n) *)
(* Proof:
   With the given conditions, apply poly_unity_special_factor_exists_0,
        ?z. mifactor z (unity n) /\ (deg z = ordz n (CARD R)) /\
        (poly_roots (PolyModRing r z) (lift z)) SUBSET (orders ((PolyModRing r z).prod excluding |0|) n)

   Let u = (PolyModRing r z).
   Since deg z = ordz n (CARD R)
      so 1 < deg h                               by 1 < ordz n (CARD R)
     and poly z                                  by poly_monic_poly
     ==> poly_root u (lift z) X                  by poly_field_mod_lift_has_root_X, 1 < deg z
     Now poly X                                  by poly_X
     and deg X = 1                               by poly_deg_X
     ==> X IN u.carrier                          by poly_mod_ring_element, deg z <> 0
    Thus X IN poly_roots u (lift z)              by poly_roots_member, poly_root u (lift z) X
      or X IN orders (u.prod excluding |0|) n    by SUBSET_DEF
    Note Field u                                 by poly_mod_irreducible_field
     and u.sum.id = |0|                          by poly_mod_ring_ids
      so forderz X = n                           by field_orders_element_order
    Take this z, and the result follows.
*)
val poly_unity_special_factor_exists = store_thm(
  "poly_unity_special_factor_exists",
  ``!r:'a field. FiniteField r ==> !n. 0 < n /\ 1 < ordz n (CARD R) ==>
   ?z. mifactor z (unity n) /\ (deg z = ordz n (CARD R)) /\ (forderz X = n)``,
  rpt (stripDup[FiniteField_def]) >>
  `?z. mifactor z (unity n) /\ (deg z = ordz n (CARD R)) /\
    (poly_roots (PolyModRing r z) (lift z)) SUBSET (orders ((PolyModRing r z).prod excluding |0|) n)`
     by rw[poly_unity_special_factor_exists_0] >>
  qabbrev_tac `u = (PolyModRing r z)` >>
  `1 < deg z /\ deg z <> 0` by decide_tac >>
  `poly z` by rw[] >>
  `poly_root u (lift z) X` by metis_tac[poly_field_mod_lift_has_root_X] >>
  `poly X /\ (deg X = 1)` by rw[] >>
  `X IN u.carrier` by metis_tac[poly_mod_ring_element] >>
  `X IN poly_roots u (lift z)` by rw[poly_roots_member] >>
  `X IN orders (u.prod excluding |0|) n` by metis_tac[SUBSET_DEF] >>
  `Field u` by rw[poly_mod_irreducible_field, Abbr`u`] >>
  `forderz X = n` by metis_tac[field_orders_element_order, poly_mod_ring_ids] >>
  metis_tac[]);

(* The following is a direct proof of the result, incorporating poly_unity_special_factor_exists_0 *)

(* Theorem: FiniteField r ==> !n. 1 < n /\ 1 < ordz n (CARD R) ==>
            ?h. mifactor h (unity n) /\ (deg h = ordz n (CARD R)) /\
            (order ((PolyModRing r h).prod excluding |0|) X = n) *)
(* Proof:
   Let d = ordz n (CARD R).
   Since 1 < d, so n <> 1, or 1 < n              by ZN_order_mod_1, d <> 1
   Note ordz n (CARD R) <> 0                     by 1 < ordz n (CARD R)
     so coprime n (CARD R)                       by ZN_order_eq_0, 0 < n

   Step 1: get a field/subfield pair.
   Since 1 < d ==> 0 < d,
     ==> ?z. monic z /\ ipoly z /\ (deg z = d)   by poly_monic_irreducible_exists, 0 < d
     and pmonic z                                by poly_monic_irreducible_property

   Construct a field/subfield pair by z:
   Let t = PolyModRing r z, st = PolyModConst r z.
   Then FiniteField t                by poly_mod_irreducible_finite_field
     or Field t                      by finite_field_is_field
   also Field st                     by poly_mod_const_field
     so st <<= t                     by poly_mod_const_subfield_poly_mod
    and st <= t                      by subfield_is_subring
   Note (t <:> st) = deg z           by poly_mod_const_subfield_dim
    and CARD R = CARD st.carrier     by poly_mod_const_subfield_card
    and t.sum.id = |0|               by poly_mod_ring_ids

   Step 2: get a minimal polynomial k in st <<= t.
   With 1 < n /\ (ordz n (CARD B) = r <:> s) /\ coprime n (CARD R)  by given
    ==> n divides CARD (ring_nonzero t)            by subfield_card_coprime_iff
     so orders (t.prod excluding |0|) n <> {}      by finite_field_orders_nonempty_iff
    ==> ?x. x IN orders (t.prod excluding |0|) n   by MEMBER_NOT_EMPTY
   This gives the following properties of x:
        x IN ring_nonzero t /\
        (order (t.prod excluding |0|) x = n)       by field_orders_element_property
    and x IN t.carrier /\ x <> |0|                 by field_nonzero_eq
   also x <> t.prod.id                             by field_order_eq_1, n <> 1

    Let k = poly_minimal t st x.
   Derive properties of k:
   Note Poly st k                    by poly_minimal_spoly, x IN t.carrier
    and IPoly st k                   by poly_minimal_subfield_irreducible
    and Monic t k                    by poly_minimal_monic
    and Deg t k = d                  by poly_minimal_deg_eqn, x IN t.carrier /\ x <> t.prod.id
   also poly_divides t k (Unity t n) by poly_minimal_divides_unity_order

   Step 3: Use this k to get h such that k = lift h
   Note FieldIso up r st             by poly_mod_const_iso_field
    ==> FieldIso (LINV up R) st r    by field_iso_sym, useful later
   Hence ?h. poly h /\ (lift h = k)  by field_iso_inverse_poly, poly_lift_def, Poly st k, FieldIso up r st
     ==> deg h = d                   by poly_mod_lift_deg
     and MAP (LINV up R) k = h       by field_iso_poly_inv, poly_lift_def

   Now work on other subgoals for h, already have deg h = d.

   Step 4: show monic h
   Note Monic t k
    ==> Monic st k                   by subring_poly_monic_iff
    ==> monic h                      by field_iso_poly_monic

   Step 5: show ipoly h
   Note ipoly (MAP (LINV up R) k)    by field_iso_poly_irreducible, IPoly st k
     or ipoly h                      by above

   Step 6: show (unity n) % h = |0|
   Note ulead h                      by poly_monic_irreducible_property
    and Poly st (Unity t n)          by poly_unity_spoly
     so poly_divides st k (Unity t n)          by subring_poly_divides_iff, poly_monic_ulead, poly_divides t k (Unity t n)
   Note MAP (LINV up R) (Unity t n) = unity n  by subring_poly_unity, field_iso_poly_unity
     so (MAP (LINV up R) k) pdivides (MAP (LINV up R) (Unity t n))    by field_iso_poly_divides_iff
     or h pdivides (unity n)         by above
    ==> (unity n) % h = |0|          by poly_divides_alt, ulead h

   Step 7: setup another field/subfield pair based on h.
   Let u = PolyModRing r h, su = PolyModConst r h.
   Establish the pattern: t =| (st, I, su) |= u.

   Note FiniteField u                by poly_mod_irreducible_finite_field
     so Field u                      by finite_field_is_field
    and Field su                     by poly_mod_const_field
    ==> su <<= u                     by poly_mod_const_subfield_poly_mod
   Also FieldIso up r su             by poly_mod_const_iso_field
   With FieldIso up r st             by above
    ==> FieldIso I st su             by field_iso_eq
    Now CARD t.carrier = CARD R ** deg z     by poly_mod_ring_card, finite_field_is_finite_ring
    and CARD u.carrier = CARD R ** deg h     by poly_mod_ring_card, finite_field_is_finite_ring
   Hence t =| (st, I, su) |= u               by above, FiniteField t, FiniteField u

   The goal is now: order (u.prod excluding |0|) X = n

   Step 8: Apply t =| (st, I, su) |= u and k = poly_minimal t st x to get this result.
   Note 1 < deg h                    by deg h = d, 1 < d
    and poly h                       by poly_monic_poly
    ==> poly_root u k X              by poly_field_mod_lift_has_root_X, 1 < deg h
   Note poly X                       by poly_X
    and deg X = 1                    by poly_deg_X
     so X IN u.carrier               by poly_mod_ring_element, deg h <> 0
     or X IN poly_roots u k          by poly_roots_member, poly_root u k X

   Let f = finite_field_element_mirror t st u su I.
   Then poly_minimal u su (f x) = MAP I (poly_minimal t st x)  by finite_field_element_mirror_poly_minimal
     or k = poly_minimal u su (f x)  by MAP_ID
     so f x IN u.carrier             by finite_field_element_mirror_element
    and poly_roots u k = ring_conjugates u su (f x)   by poly_minimal_roots
   Thus X IN ring_conjugates u su (f x)               by above

   Now X and (f x) are conjugates, find order of (f x) to get order of X:
   Note u.sum.id = |0|                                by poly_mod_ring_ids
     so order (u.prod excluding |0|) (f x) = n        by finite_field_element_mirror_order
    ==> order (u.prod excluding |0|) X = n            by finite_field_conjugates_order
*)
Theorem poly_unity_special_factor_exists[allow_rebind]:
  !r:'a field. FiniteField r ==> !n. 0 < n /\ 1 < ordz n (CARD R) ==>
   ?h. mifactor h (unity n) /\ (deg h = ordz n (CARD R)) /\ (order ((PolyModRing r h).prod excluding |0|) X = n)
Proof
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `d = ordz n (CARD R)` >>
  `0 < d /\ d <> 1` by decide_tac >>
  `n <> 1` by metis_tac[ZN_order_mod_1] >>
  `coprime n (CARD R)` by metis_tac[ZN_order_eq_0, DECIDE``1 < n ==> n <> 0``] >>
  `?z. monic z /\ ipoly z /\ (deg z = d)` by rw[poly_monic_irreducible_exists] >>
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
  `t.sum.id = |0|` by rw[poly_mod_ring_ids, Abbr`t`] >>
  `n divides CARD (ring_nonzero t)` by metis_tac[subfield_card_coprime_iff] >>
  `orders (t.prod excluding t.sum.id) n <> {}` by rw[GSYM finite_field_orders_nonempty_iff] >>
  `?x. x IN orders (t.prod excluding t.sum.id) n` by rw[MEMBER_NOT_EMPTY] >>
  `x IN ring_nonzero t /\ (order (t.prod excluding t.sum.id) x = n)` by metis_tac[field_orders_element_property] >>
  `x IN t.carrier /\ x <> t.sum.id` by metis_tac[field_nonzero_eq] >>
  `x <> t.prod.id` by metis_tac[field_order_eq_1] >>
  qabbrev_tac `k = poly_minimal t st x` >>
  `Poly st k` by rw[poly_minimal_spoly, Abbr`k`] >>
  `IPoly st k` by rw[poly_minimal_subfield_irreducible, Abbr`k`] >>
  `Monic t k` by rw[poly_minimal_monic, Abbr`k`] >>
  `Deg t k = d` by metis_tac[poly_minimal_deg_eqn] >>
  `poly_divides t k (Unity t n)` by rw[poly_minimal_divides_unity_order, Abbr`k`] >>
  `FieldIso up r st` by rw[poly_mod_const_iso_field, Abbr`st`] >>
  `FieldIso (LINV up R) st r` by rw[field_iso_sym] >>
  `?h. poly h /\ (lift h = k)` by metis_tac[field_iso_inverse_poly, poly_lift_def] >>
  `deg h = d` by metis_tac[field_orders_element_property, poly_mod_lift_deg] >>
  `MAP (LINV up R) k = h` by metis_tac[field_iso_poly_inv, poly_lift_def] >>
  `Monic st k` by metis_tac[subring_poly_monic_iff] >>
  `monic h` by metis_tac[field_iso_poly_monic] >>
  `ipoly h` by metis_tac[field_iso_poly_irreducible] >>
  qexists_tac `h` >>
  rpt strip_tac >-
  rw_tac std_ss[] >-
  rw_tac std_ss[] >-
 (`ulead h` by rw[poly_monic_irreducible_property] >>
  `Poly st (Unity t n)` by rw[poly_unity_spoly] >>
  `poly_divides st k (Unity t n)` by metis_tac[subring_poly_divides_iff, poly_monic_ulead] >>
  `MAP (LINV up R) (Unity t n) = unity n` by metis_tac[subring_poly_unity, field_iso_poly_unity] >>
  `h pdivides (unity n)` by prove_tac[field_iso_poly_divides_iff] >>
  rw[GSYM poly_divides_alt]) >-
  rw_tac std_ss[] >>
  qabbrev_tac `u = PolyModRing r h` >>
  qabbrev_tac `su = PolyModConst r h` >>
  `FiniteField u` by rw[poly_mod_irreducible_finite_field, Abbr`u`] >>
  `Field u` by rw[finite_field_is_field] >>
  `Field su` by rw[poly_mod_const_field, Abbr`su`] >>
  `su <<= u` by rw[poly_mod_const_subfield_poly_mod, Abbr`u`, Abbr`su`] >>
  `FieldIso up r su` by rw[poly_mod_const_iso_field, Abbr`su`] >>
  `FieldIso I st su` by metis_tac[field_iso_eq] >>
  `CARD t.carrier = CARD R ** deg z` by rw[poly_mod_ring_card, finite_field_is_finite_ring, Abbr`t`] >>
  `CARD u.carrier = CARD R ** deg h` by rw[poly_mod_ring_card, finite_field_is_finite_ring, Abbr`u`] >>
  `t =| (st, I, su) |= u` by rw[] >>
  `1 < deg h /\ deg h <> 0` by decide_tac >>
  `poly h` by rw[] >>
  `poly_root u k X` by metis_tac[poly_field_mod_lift_has_root_X] >>
  `poly X /\ (deg X = 1)` by rw[] >>
  `X IN u.carrier` by metis_tac[poly_mod_ring_element] >>
  `X IN poly_roots u k` by rw[poly_roots_member] >>
  qabbrev_tac `f = finite_field_element_mirror t st u su I` >>
  `k = poly_minimal u su (f x)` by rw[finite_field_element_mirror_poly_minimal, Abbr`k`, Abbr`f`] >>
  `f x IN u.carrier` by rw[finite_field_element_mirror_element, Abbr`f`] >>
  `poly_roots u k = ring_conjugates u su (f x)` by rw[poly_minimal_roots] >>
  `X IN ring_conjugates u su (f x)` by metis_tac[] >>
  `u.sum.id = |0|` by rw[poly_mod_ring_ids, Abbr`u`] >>
  `order (u.prod excluding u.sum.id) (f x) = n` by rw[finite_field_element_mirror_order, Abbr`f`] >>
  metis_tac[finite_field_conjugates_order]
QED

(* This is the much sought-after theorem! *)

(* Theorem: FiniteField r /\ 0 < k /\ 1 < ordz k (CARD R) ==>
            ?z. mifactor z (unity k) /\ (deg z = ordz k (CARD R)) /\ (forderz X = k) *)
(* Proof: by poly_unity_special_factor_exists *)
val poly_unity_special_factor_exists_1 = store_thm(
  "poly_unity_special_factor_exists_1",
  ``!(r:'a field) k. FiniteField r /\ 0 < k /\ 1 < ordz k (CARD R) ==>
                ?z. mifactor z (unity k) /\ (deg z = ordz k (CARD R)) /\ (forderz X = k)``,
  metis_tac[poly_unity_special_factor_exists]);

(* This is good for pretty-printing. *)

(* Theorem: FiniteField r /\ 0 < k /\ 1 < ordz k (CARD R) ==>
     ?z. monic z /\ ipoly z /\ z pdivides (unity k) /\ (deg z = ordz k (CARD R)) /\ (forderz X = k) *)
(* Proof:
   Note ?z. mifactor z (unity k) /\ (deg z = ordz k (CARD R)) /\ (forderz X = k)
                                 by poly_unity_special_factor_exists
    Now 0 < deg z                by poly_irreducible_deg_nonzero
    and ulead z                  by poly_monic_pmonic, 0 < deg z
   Also z pdivides (unity k)     by poly_divides_alt, unity k % z = |0|
   Take this z, and the result follows.
*)
val poly_unity_special_factor_exists_alt = store_thm(
  "poly_unity_special_factor_exists_alt",
  ``!(r:'a field) k. FiniteField r /\ 0 < k /\ 1 < ordz k (CARD R) ==>
     ?z. monic z /\ ipoly z /\ z pdivides (unity k) /\
         (deg z = ordz k (CARD R)) /\ (forderz X = k)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ poly (unity k)` by rw[] >>
  `?z. mifactor z (unity k) /\ (deg z = ordz k (CARD R)) /\ (forderz X = k)` by metis_tac[poly_unity_special_factor_exists] >>
  `ulead z` by rw_tac std_ss[poly_monic_ulead] >>
  metis_tac[poly_divides_alt]);

(* Note: The existence of this special factor of (unity k)
   is critical in the correctness proof of the AKS algorithm.
*)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
