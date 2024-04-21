(* ------------------------------------------------------------------------- *)
(* Product of Polynomials                                                    *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polyProduct";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory listTheory arithmeticTheory numberTheory combinatoricsTheory
     dividesTheory gcdTheory gcdsetTheory;

open monoidTheory groupTheory ringTheory ringUnitTheory fieldTheory;

open subgroupTheory;
open groupOrderTheory;

(* val _ = load "groupProductTheory"; *)
open groupProductTheory;

open polyDividesTheory polyDivisionTheory;
open polynomialTheory polyWeakTheory polyRingTheory;

open polyMonicTheory;
open polyFieldTheory;
open polyFieldDivisionTheory;
open polyEvalTheory;
open polyRootTheory;

(* ------------------------------------------------------------------------- *)
(* Product of Polynomials Documentation                                      *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   poly_set r s               = !p. p IN s ==> poly p
   pset s                     = poly_set r s
   EVERY_PSET P               = !s. s IN P ==> pset s
   poly_map r f               = !x. x IN R ==> poly (f x)
   pmap f                     = poly_map r f
   PPROD s                    = poly_prod_set r s
   monic_set r s              = !p. p IN s ==> monic p
   mset r                     = monic_set r
   poly_prod_image r f s      = PPROD (IMAGE f s)
   PPIMAGE f s                = poly_prod_image r f s
   poly_prod_factors r s      = PPIMAGE factor s
   PIFACTOR s                 = poly_prod_factors r s
   poly_prod_factor_roots r p = PIFACTOR (roots p)
   PFROOTS p                  = poly_prod_factor_roots r p
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Polynomial Sets and Maps:
   poly_set_union_poly_set     |- !r s t. pset s /\ pset t <=> pset (s UNION t)
   poly_set_inter_poly_set     |- !r s t. pset s /\ pset t ==> pset (s INTER t)
   poly_set_bigunion_poly_set  |- !r s. EVERY_PSET s <=> pset (BIGUNION s)
   poly_set_biginter_poly_set  |- !r s. EVERY_PSET s /\ s <> {} ==> pset (BIGINTER s)
   poly_map_image_poly_set     |- !r s f. s SUBSET R /\ pmap f ==> pset (IMAGE f s)
   poly_map_factor             |- !r. Ring r /\ #1 <> #0 ==> pmap factor

   Polynomial Product of a set of Polynomials:
   poly_prod_set_def        |- !r s. PPROD s = GPROD_SET (PolyRing r).prod s
   poly_prod_set_empty      |- !r. PPROD {} = |1|
   poly_prod_set_property   |- !r. Ring r ==> !s. FINITE s /\ s SUBSET (PolyRing r).carrier ==>
                                                  PPROD s IN (PolyRing r).carrier
   poly_set_subset_poly_set |- !r s t. pset t /\ s SUBSET t ==> pset s
   poly_prod_set_poly       |- !r. Ring r ==> !s. FINITE s /\ pset s ==> poly (PPROD s)
   poly_prod_set_thm        |- !r. Ring r ==> !s. FINITE s /\ pset s ==>
                               !p. poly p ==> (PPROD (p INSERT s) = p * PPROD (s DELETE p))
   poly_prod_set_insert     |- !r. Ring r ==> !s. FINITE s /\ pset s ==>
                               !p. poly p /\ p NOTIN s ==> (PPROD (p INSERT s) = p * PPROD s)
   poly_prod_set_mult_eqn   |- !r. Ring r ==> !s t. FINITE s /\ FINITE t /\ pset s /\ pset t ==>
                                    (PPROD (s UNION t) * PPROD (s INTER t) = PPROD s * PPROD t)
   poly_prod_set_sing       |- !r. Ring r ==> !p. poly p ==> (PPROD {p} = p)
   poly_prod_set_by_partition        |- !r. Ring r ==> !s. FINITE s /\ pset s ==>
                                        !u v. s =|= u # v ==> (PPROD s = PPROD u * PPROD v)
   poly_prod_set_element_divides     |- !r. Ring r ==> !s. FINITE s /\ pset s ==>
                                        !p. p IN s ==> p pdivides PPROD s
   poly_prod_set_divides_prod_set    |- !r. Ring r ==> !s t. FINITE t /\ pset t /\ s SUBSET t ==>
                                            PPROD s pdivides PPROD t
   poly_prod_set_eq_zero     |- !r. Ring r ==> !s. FINITE s /\ pset s /\ |0| IN s ==> (PPROD s = |0|)
   poly_prod_set_with_zero   |- !r. Ring r ==> !s. FINITE s /\ pset s ==> (PPROD ( |0| INSERT s) = |0|)
   poly_prod_set_with_one    |- !r. Ring r ==> !s. FINITE s /\ pset s ==> (PPROD ( |1| INSERT s) = PPROD s)

   Polynomial Product of Monic Polynomials:
   monic_set_poly_set                |- !s. mset s ==> pset s
   monic_set_bigunion_monic_set      |- !r s. (!x. x IN s ==> mset x) ==> mset (BIGUNION s)
   poly_monic_prod_set_monic         |- !r. Ring r ==> !s. FINITE s /\ mset s ==> monic (PPROD s)
   poly_monic_prod_set_monomials_deg |- !r. Ring r ==> !s. FINITE s /\ mset s /\
                                            (!p. p IN s ==> (deg p = 1)) ==> (deg (PPROD s) = CARD s)
   poly_monic_prod_set_ulead   |- !r. Ring r ==> !s. FINITE s /\ mset s ==> ulead (PPROD s)
   poly_monic_prod_set_pmonic  |- !r. Ring r ==> !s. FINITE s /\ mset s /\
                                      (!p. p IN s ==> 0 < deg p) /\ s <> {} ==> pmonic (PPROD s)
   poly_monic_prod_set_deg     |- !r. Ring r ==> !s. FINITE s /\ mset s ==> (deg (PPROD s) = SIGMA deg s)

   Polynomial Sets for Field:
   poly_monic_prod_set_divides_one
                            |- !r. Field r ==> !s. FINITE s /\ mset s ==>
                                   (PPROD s pdivides |1| <=> PPROD s = |1|)
   poly_prod_set_nonzero    |- !r. Field r ==> !s. FINITE s /\ pset s /\
                                   (!p. p IN s ==> p <> |0|) ==> PPROD s <> |0|
   poly_prod_set_ulead      |- !r. Field r ==> !s. FINITE s /\ pset s /\
                                   (!p. p IN s ==> p <> |0|) ==> ulead (PPROD s)
   poly_prod_set_deg_lower  |- !r. Field r ==> !s. FINITE s /\ pset s /\
                                   (!p. p IN s ==> p <> |0|) ==> !p. p IN s ==> deg p <= deg (PPROD s)
   poly_prod_set_roots      |- !r. Field r ==> !s. FINITE s /\ pset s ==>
                                   (roots (PPROD s) = BIGUNION (IMAGE roots s))

   Product of Polynomial by function image:
   poly_prod_image_empty    |- !r f. PPIMAGE f {} = |1|
   poly_prod_image_sing     |- !r. Ring r ==> !f. pmap f ==> !x. x IN R ==> (PPIMAGE f {x} = f x)
   poly_prod_image_poly     |- !r. Ring r ==> !s f. FINITE s /\ s SUBSET R /\ pmap f ==> poly (PPIMAGE f s)
   poly_prod_set_exp        |- !r. Ring r ==> !s. FINITE s /\ pset s ==>
                               !n. INJ (\p. p ** n) s univ(:'a poly) ==> (PPROD s ** n = PPIMAGE (\p. p ** n) s)
   poly_peval_poly_prod     |- !r. Ring r ==> !s. FINITE s /\ pset s ==>
                               !q. poly q /\ INJ (\p. peval p q) s univ(:'a poly) ==>
                                   (peval (PPROD s) q = PPIMAGE (\p. peval p q) s)

   Product of Factors:
   poly_prod_factors_empty  |- !r. PIFACTOR {} = |1|
   poly_prod_factors_sing   |- !r. Ring r /\ #1 <> #0 ==> !c. c IN R ==> (PIFACTOR {c} = factor c)
   poly_prod_factors_poly   |- !r. Ring r /\ #1 <> #0 ==> !s. FINITE s /\ s SUBSET R ==> poly (PIFACTOR s)
   poly_prod_factors_monic  |- !r. Ring r /\ #1 <> #0 ==> !s. FINITE s /\ s SUBSET R ==> monic (PIFACTOR s)
   poly_prod_factors_deg    |- !r. Ring r /\ #1 <> #0 ==> !s. FINITE s /\ s SUBSET R ==> (deg (PIFACTOR s) = CARD s)
   poly_prod_factors_roots  |- !r. Field r ==> !s. FINITE s /\ s SUBSET R ==> (roots (PIFACTOR s) = s)
   poly_prod_factors_deg_eq_card_roots     |- !r. Field r ==> !s. FINITE s /\ s SUBSET R ==>
                                                  (deg (PIFACTOR s) = CARD (roots (PIFACTOR s)))
   poly_prod_factors_factor       |- !r. Field r ==> !s. FINITE s /\ s SUBSET R ==>
                                     !c. c IN R ==> (factor c pdivides PIFACTOR s <=> c IN s)
   poly_prod_factors_nonzero      |- !r. Field r ==> !s. FINITE s /\ s SUBSET R ==> PIFACTOR s <> |0|
   poly_prod_factors_divisibility |- !r. Field r ==> !s t. FINITE s /\ s SUBSET R /\ FINITE t /\ t SUBSET R ==>
                                                           (PIFACTOR t pdivides PIFACTOR s <=> t SUBSET s)


   Product of Factor of Roots:
#  poly_prod_factor_roots_empty   |- !r p. (roots p = {}) ==> (PFROOTS p = |1|)
#  poly_prod_factor_roots_poly    |- !r. Field r ==> !p. poly p /\ p <> |0| ==> poly (PFROOTS p)
#  poly_prod_factor_roots_monic   |- !r. Field r ==> !p. poly p /\ p <> |0| ==> monic (PFROOTS p)
   poly_prod_factor_roots_deg     |- !r. Field r ==> !p. poly p /\ p <> |0| ==> (deg (PFROOTS p) = CARD (roots p))
   poly_prod_factor_roots_roots   |- !r. Field r ==> !p. poly p /\ p <> |0| ==> (roots (PFROOTS p) = roots p)
   poly_prod_factor_roots_divides |- !r. Field r ==> !p. poly p /\ p <> |0| ==> PFROOTS p pdivides p
   poly_prod_factor_roots_eq_poly |- !r. Field r ==> !p. monic p /\ (deg p = CARD (roots p)) ==> (PFROOTS p = p)
   poly_prod_factor_roots_eq_poly_iff
                               |- !r. Field r ==> !p. monic p ==> ((p = PFROOTS p) <=> (deg p = CARD (roots p)))
   poly_eq_prod_factor_roots   |- !r. Field r ==> !p. monic p /\ (deg p = CARD (roots p)) ==> (p = PFROOTS p)
   poly_eq_prod_factor_roots_alt  |- !r. Field r ==> !p. monic p /\ (deg p = CARD (roots p)) ==>
                                         (p = PPROD {X - c * |1| | c | c IN roots p})
   poly_monic_divides_poly_prod_factors_property
                                  |- !r. Field r ==> !s. FINITE s /\ s SUBSET R ==>
                                     !p. monic p /\ p pdivides PIFACTOR s /\
                                         (roots p INTER s = {}) ==> (p = |1|)

   Multiplicative Function for Polynomial Set:
   poly_set_multiplicative_fun_def   |- !r f. poly_set_multiplicative_fun r f <=>
     (f {} = |1|) /\ (!s. FINITE s /\ pset s ==> poly (f s)) /\
     !s t. FINITE s /\ FINITE t /\ pset s /\ pset t ==> (f (s UNION t) * f (s INTER t) = f s * f t)
   poly_prod_set_mult_fun    |- !r. Ring r ==> poly_set_multiplicative_fun r PPROD
   poly_disjoint_bigunion_mult_fun
              |- !r. Ring r ==> !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P /\ EVERY_PSET P ==>
                 !f. poly_set_multiplicative_fun r f /\ INJ f P univ(:'a poly) ==> (f (BIGUNION P) = PPIMAGE f P)
   poly_prod_set_mult_fun_by_partition
              |- !r. Ring r ==> !RR s. FINITE s /\ pset s /\ RR equiv_on s ==>
                 !f. poly_set_multiplicative_fun r f /\ INJ f (partition RR s) univ(:'a poly) ==>
                                  (f s = PPIMAGE f (partition RR s))

   Multiplicative Function for Ring Set:
   ring_set_multiplicative_fun_def
        |- !r f. ring_set_multiplicative_fun r f <=>
                 (f {} = |1|) /\ (!s. FINITE s /\ s SUBSET R ==> poly (f s)) /\
           !s t. FINITE s /\ FINITE t /\ s SUBSET R /\ t SUBSET R ==> (f (s UNION t) * f (s INTER t) = f s * f t)
   ring_set_union_ring_set        |- !r s t. s SUBSET R /\ t SUBSET R <=> s UNION t SUBSET R
   ring_set_bigunion_ring_set     |- !r s. (!t. t IN s ==> t SUBSET R) <=> BIGUNION s SUBSET R
   ring_disjoint_bigunion_mult_fun
        |- !r. Ring r ==> !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P /\ (!s. s IN P ==> s SUBSET R) ==>
           !f. ring_set_multiplicative_fun r f /\ INJ f P univ(:'a poly) ==> (f (BIGUNION P) = PPIMAGE f P)
   ring_prod_set_mult_fun_by_partition
        |- !r. Ring r ==> !RR s. FINITE s /\ s SUBSET R /\ RR equiv_on s ==>
           !f. ring_set_multiplicative_fun r f /\ INJ f (partition RR s) univ(:'a poly) ==>
                               (f s = PPIMAGE f (partition RR s))

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems.                                                          *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Polynomial Sets and Maps.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Overload a set with polynomial elements *)
val _ = overload_on("poly_set", ``\(r:'a ring) s. !p. p IN s ==> poly p``);

(* Overload poly_set for ring r *)
val _ = overload_on("pset", ``poly_set r``);

(* Theorem: pset s /\ pset t ==> pset (s UNION t) *)
(* Proof: by IN_UNION *)
val poly_set_union_poly_set = store_thm(
  "poly_set_union_poly_set",
  ``!r:'a ring. !s t. pset s /\ pset t <=> pset (s UNION t)``,
  metis_tac[IN_UNION]);

(* Theorem: pset s /\ pset t ==> pset (s INTER t) *)
(* Proof: by IN_INTER *)
val poly_set_inter_poly_set = store_thm(
  "poly_set_inter_poly_set",
  ``!r:'a ring. !s t. pset s /\ pset t ==> pset (s INTER t)``,
  metis_tac[IN_INTER]);

(* Overload for every pset *)
val _ = overload_on("EVERY_PSET", ``\P. (!s. s IN P ==> pset s)``);

(* Theorem: EVERY_PSET s <=> pset (BIGUNION s) *)
(* Proof: by IN_BIGUNION *)
val poly_set_bigunion_poly_set = store_thm(
  "poly_set_bigunion_poly_set",
  ``!r:'a ring. !s. EVERY_PSET s <=> pset (BIGUNION s)``,
  metis_tac[IN_BIGUNION]);

(* Theorem: EVERY_PSET s /\ s <> {} ==> pset (BIGINTER s) *)
(* Proof: by IN_BIGINTER, MEMBER_NOT_EMPTY *)
val poly_set_biginter_poly_set = store_thm(
  "poly_set_biginter_poly_set",
  ``!r:'a ring. !s. EVERY_PSET s /\ s <> {} ==> pset (BIGINTER s)``,
  metis_tac[IN_BIGINTER, MEMBER_NOT_EMPTY]);

(* Overload a map with polynomial output *)
val _ = overload_on("poly_map", ``\(r:'a ring) f. !x. x IN R ==> poly (f x)``);

(* Overload poly_map for ring r *)
val _ = overload_on("pmap", ``poly_map r``);

(* Theorem: Ring r ==> !s f. s SUBSET R /\ pmap f ==> pset (IMAGE f s) *)
(* Proof:
       pset (IMAGE f s)
   <=> !p. p IN (IMAGE f s) ==> poly p           by notation
   <=> !p. ?x. x IN s /\ (p = f x) ==> poly p    by IN_IMAGE
   But x IN s ==> x IN R                         by SUBSET_DEF
   and x IN R ==> poly (f x)                     by notation
   Hence true.
*)
val poly_map_image_poly_set = store_thm(
  "poly_map_image_poly_set",
  ``!r:'a ring. !s f. s SUBSET R /\ pmap f ==> pset (IMAGE f s)``,
  (rw[SUBSET_DEF] >> rw[]));

(* Theorem: Ring r /\ #1 <> #0 ==> pmap factor *)
(* Proof:
       pmap factor
   <=> x. x IN R ==> poly (factor x)    by notation
   <=> T                                by poly_factor_poly
*)
val poly_map_factor = store_thm(
  "poly_map_factor",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> pmap factor``,
  rw[poly_factor_poly]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Product of a set of Polynomials                                *)
(* ------------------------------------------------------------------------- *)

(* Cardinality of Power Set:
> CARD_POW;
val it = |- !s. FINITE s ==> (CARD (POW s) = 2 ** CARD s): thm

> EVAL ``POW {0; 1}``;
val it = |- POW {0; 1} = {{0; 1}; {0}; {1}; {}}: thm
> EVAL ``POW (count 2)``;
val it = |- POW (count 2) = {{1; 0}; {1}; {0}; {}}: thm
> EVAL ``SUM_SET {}``;
val it = |- SUM_SET {} = 0: thm
> EVAL ``PROD_SET {}``;
val it = |- PROD_SET {} = PROD_SET {}: thm  -- need some work on computelib
> SUM_SET_THM;
val it = |- (SUM_SET {} = 0) /\ !x s. FINITE s ==> (SUM_SET (x INSERT s) = x + SUM_SET (s DELETE x)): thm
> PROD_SET_THM;
val it = |- (PROD_SET {} = 1) /\ !x s. FINITE s ==> (PROD_SET (x INSERT s) = x * PROD_SET (s DELETE x)): thm
> EVAL ``IMAGE (\s. SUM_SET s) (POW (count 2))``;
val it = |- IMAGE (\s. SUM_SET s) (POW (count 2)) = {1; 0}: thm -- need a BAG when not distinct.
> EVAL ``IMAGE (\s. prod s) (POW (count 2))``;
<<HOL message: inventing new type variable names: 'a>>
val it = |- IMAGE (\s. prod s) (POW (count 2)) = {prod {1; 0}; prod {1}; prod {0}; prod {}}: thm
> EVAL ``IMAGE (\s. prod s) (POW (IMAGE SUC (count 2)))``;
<<HOL message: inventing new type variable names: 'a>>
val it = |- IMAGE (\s. prod s) (POW (IMAGE SUC (count 2))) = {prod {2; 1}; prod {2}; prod {1}; prod {}}: thm

Better to define: prod s = PI (X + SUC c)  SUC c IN s, rather than PI (X + c) but using POW IMAGE SUC.

EVAL ``IMAGE (\s. IMAGE (\c. X + ###(SUC c)) s) (POW (count 2))``;
-- gives expansions of X and ###(SUC c)
-- easier to see the following:
> EVAL ``IMAGE (\s. IMAGE (\c. Y + (SUC c)) s) (POW (count 2))``;
val it = |- IMAGE (\s. IMAGE (\c. Y + SUC c) s) (POW (count 2)) =
   {{Y + 2; Y + 1}; {Y + 2}; {Y + 1}; {}}: thm

> EVAL ``IMAGE (\s. poly_prod (IMAGE (\c. Y + (SUC c)) s)) (POW (count 2))``;
<<HOL message: inventing new type variable names: 'a>>
val it = |- IMAGE (\s. poly_prod (IMAGE (\c. Y + SUC c) s)) (POW (count 2)) =
   {poly_prod {Y + 2; Y + 1}; poly_prod {Y + 2}; poly_prod {Y + 1}; poly_prod {}}: thm

*)

(* Define Polynomial Product of a set of Polynomials. *)
val poly_prod_set_def = Define`
   poly_prod_set (r:'a ring) (s:'a poly -> bool) = GPROD_SET (PolyRing r).prod s
`;

(* overload for poly_prod_set *)
val _ = overload_on ("PPROD", ``poly_prod_set r``);

(* Theorem: PPROD {} = |1| *)
(* Proof:
     PPROD {}
   = GPROD_SET (PolyRing r).prod {}     by poly_prod_set_def
   = GITSET (PolyRing r).prod {} |1|    by GPROD_SET_def
   = |1|                                by GITSET_EMPTY
*)
val poly_prod_set_empty = store_thm(
  "poly_prod_set_empty",
  ``!r:'a ring. PPROD {} = |1|``,
  rw[poly_prod_set_def, GPROD_SET_def, GITSET_EMPTY]);

(* Theorem: Ring r ==> FINITE s /\ s SUBSET (PolyRing r).carrier ==> poly (PPROD s) *)
(* Proof:
   Ring r ==> Ring (PolyRing r)                       by poly_add_mult_ring
   Ring r ==> AbelianMonoid (PolyRing r).prod         by poly_mult_abelian_monoid
   (PolyRing r).carrier = (PolyRing r).prod.carrier   by ring_carriers
   Now,
   PPROD s = GPROD_SET (PolyRing r).prod s            by poly_prod_set_def
   Hence PPROD s IN (PolyRing r).carrier              by GPROD_SET_PROPERTY
*)
val poly_prod_set_property = store_thm(
  "poly_prod_set_property",
  ``!r:'a ring. Ring r ==>
   !s. FINITE s /\ s SUBSET (PolyRing r).carrier ==> PPROD s IN (PolyRing r).carrier``,
  rw[poly_prod_set_def] >>
  `Ring (PolyRing r)` by rw[poly_add_mult_ring] >>
  `(PolyRing r).carrier = (PolyRing r).prod.carrier` by rw[ring_carriers] >>
  `AbelianMonoid (PolyRing r).prod` by rw[poly_mult_abelian_monoid] >>
  metis_tac[GPROD_SET_PROPERTY]);

(* Theorem: pset t /\ s SUBSET t ==> pset s *)
(* Proof: by SUBSET_DEF *)
val poly_set_subset_poly_set = store_thm(
  "poly_set_subset_poly_set",
  ``!r:'a ring. !s t. pset t /\ s SUBSET t ==> pset s``,
  rw_tac std_ss[SUBSET_DEF]);

(* Theorem: Ring r ==> FINITE s /\ pset s ==> poly (PPROD s) *)
(* Proof:
   Since poly p <=> p IN (PolyRing r).carrier   by poly_ring_element
     and p IN s ==> p IN (PolyRing r).carrier
         iff s SUBSET (PolyRing r).carrier      by SUBSET_DEF
   This is true                                 by poly_prod_set_property
*)
val poly_prod_set_poly = store_thm(
  "poly_prod_set_poly",
  ``!r:'a ring. Ring r ==> !s. FINITE s /\ pset s ==> poly (PPROD s)``,
  metis_tac[poly_prod_set_property, poly_ring_element, SUBSET_DEF]);

(* Theorem: Ring r ==> !s. FINITE s /\ pset s ==>
           !p. poly p ==> (PPROD (p INSERT s) = p * PPROD (s DELETE p)) *)
(* Proof:
   Ring r ==> Ring (PolyRing r)                       by poly_add_mult_ring
   Ring r ==> AbelianMonoid (PolyRing r).prod         by poly_mult_abelian_monoid
   (PolyRing r).carrier = (PolyRing r).prod.carrier   by ring_carriers
   Now,
   PPROD s = GPROD_SET (PolyRing r).prod s            by poly_prod_set_def
   s SUBSET (PolyRing r).carrier                      by poly_ring_element, SUBSET_DEF
   p IN (PolyRing r).carrier                          by poly_ring_element
   Hence result follows                               by GPROD_SET_THM
*)
val poly_prod_set_thm = store_thm(
  "poly_prod_set_thm",
  ``!r:'a ring. Ring r ==> !s. FINITE s /\ pset s ==>
   !p. poly p ==> (PPROD (p INSERT s) = p * PPROD (s DELETE p))``,
  rw[poly_prod_set_def] >>
  `Ring (PolyRing r)` by rw[poly_add_mult_ring] >>
  `(PolyRing r).carrier = (PolyRing r).prod.carrier` by rw[ring_carriers] >>
  `AbelianMonoid (PolyRing r).prod` by rw[poly_mult_abelian_monoid] >>
  `s SUBSET (PolyRing r).carrier /\ p IN (PolyRing r).carrier` by rw[poly_ring_element, SUBSET_DEF] >>
  metis_tac[GPROD_SET_THM]);

(* Theorem: Ring r ==> !s. FINITE s /\ pset s ==>
            !p. poly p /\ p NOTIN s ==> (PPROD (p INSERT s) = p * PPROD s) *)
(* Proof:
      PPROD (p INSERT s)
    = p * PPROD (s DELETE p)     by poly_prod_set_thm
    = p * PPROD s                by DELETE_NON_ELEMENT
*)
val poly_prod_set_insert = store_thm(
  "poly_prod_set_insert",
  ``!r:'a ring. Ring r ==> !s. FINITE s /\ pset s ==>
   !p. poly p /\ p NOTIN s ==> (PPROD (p INSERT s) = p * PPROD s)``,
  metis_tac[poly_prod_set_thm, DELETE_NON_ELEMENT]);

(* Theorem: Ring r ==> !s t. FINITE s /\ FINITE t /\ pset s /\ pset t ==>
            (PPROD (s UNION t) * PPROD (s INTER t) = PPROD s * PPROD t) *)
(* Proof:
   By finite induction on s.
   Base: PPROD ({} UNION t) * PPROD ({} INTER t) = PPROD {} * PPROD t
      Note poly (PPROD t)      by poly_prod_set_poly
        PPROD ({} UNION t) * PPROD ({} INTER t)
      = PPROD t * PPROD {}     by UNION_EMPTY, INTER_EMPTY
      = PPROD t * |1|          by poly_prod_set_empty
      = PPROD t                by poly_mult_rone
      = |1| * PPROD t          by poly_mult_lone
      = PPROD {} * PPROD t     by poly_prod_set_empty
   Step: e NOTIN s /\ pset (e INSERT s) ==>
         PPROD ((e INSERT s) UNION t) * PPROD ((e INSERT s) INTER t) = PPROD (e INSERT s) * PPROD t
      Note FINITE (s UNION t)  by FINITE_UNION
       and FINITE (s INTER t)  by FINITE_INTER
      also poly e /\ pset s    by IN_INSERT
       and pset (s UNION t)    by IN_UNION, or poly_set_union_poly_set
       and pset (s INTER t)    by IN_INTER, or poly_set_inter_poly_set
      also poly (PPROD (s UNION t))   by poly_prod_set_poly
       and poly (PPROD (s INTER t))   by poly_prod_set_poly
       and poly (PPROD s)             by poly_prod_set_poly
       and poly (PPROD t)             by poly_prod_set_poly
    Since INSERT_UNION and INSERT_INTER are based on whether e IN t,
    there are two cases.
    If e IN t,
       Then e NOTIN s INTER t         by IN_INTER

       PPROD ((e INSERT s) UNION t) * PPROD ((e INSERT s) INTER t)
     = PPROD (s UNION t) * PPROD (e INSERT (s INTER t))       by INSERT_UNION, INSERT_INTER
     = PPROD (s UNION t) * (e * PPROD (s INTER t))            by poly_prod_set_insert
     = e * (PPROD (s UNION t) * PPROD (s INTER t))            by poly_mult_assoc_comm
     = e * (PPROD s * PPROD t                                 by induction hypothesis
     = (e * PPROD s) * PPROD t                                by poly_mult_assoc
     = PPROD (e INSERT s) * PPROD t                           by poly_prod_set_insert
    If e NOTIN t,
       Then e NOTIN s UNION t         by IN_UNION

       PPROD ((e INSERT s) UNION t) * PPROD ((e INSERT s) INTER t)
     = PPROD (e INSERT (s UNION t)) * PPROD (s INTER t)       by INSERT_UNION, INSERT_INTER
     = e * PPROD (s UNION t) * PPROD (s INTER t)              by poly_prod_set_insert
     = e * (PPROD (s UNION t) * PPROD (s INTER t))            by poly_mult_assoc
     = e * (PPROD s * PPROD t)                                by induction hypothesis
     = (e * PPROD s) * PPROD t                                by poly_mult_assoc
     = PPROD (e INSERT s) * PPROD t                           by poly_prod_set_insert
*)
val poly_prod_set_mult_eqn = store_thm(
  "poly_prod_set_mult_eqn",
  ``!r:'a ring. Ring r ==> !s t. FINITE s /\ FINITE t /\ pset s /\ pset t ==>
    (PPROD (s UNION t) * PPROD (s INTER t) = PPROD s * PPROD t)``,
  ntac 2 strip_tac >>
  `!s. FINITE s ==> !t. FINITE t ==> pset s /\ pset t ==>
    (PPROD (s UNION t) * PPROD (s INTER t) = PPROD s * PPROD t)` suffices_by rw[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >| [
    simp[poly_prod_set_empty] >>
    rw[poly_prod_set_poly],
    `FINITE (s UNION t) /\ FINITE (s INTER t)` by rw[] >>
    `poly e /\ pset s` by rw[] >>
    `pset (s UNION t)` by metis_tac[IN_UNION] >>
    `pset (s INTER t)` by metis_tac[IN_INTER] >>
    `poly (PPROD (s UNION t)) /\ poly (PPROD (s INTER t))` by rw[poly_prod_set_poly] >>
    `poly (PPROD s) /\ poly (PPROD t)` by rw[poly_prod_set_poly] >>
    rw[INSERT_UNION, INSERT_INTER] >| [
      `e NOTIN s INTER t` by rw[] >>
      `PPROD (s UNION t) * PPROD (e INSERT s INTER t) = PPROD (s UNION t) * (e * PPROD (s INTER t))` by rw[poly_prod_set_insert] >>
      `_ = e * (PPROD (s UNION t) * PPROD (s INTER t))` by rw[poly_mult_assoc_comm] >>
      `_ = e * (PPROD s * PPROD t)` by rw[] >>
      `_ = (e * PPROD s) * PPROD t` by rw[poly_mult_assoc] >>
      `_ = PPROD (e INSERT s) * PPROD t` by rw[poly_prod_set_insert] >>
      rw[],
      `e NOTIN s UNION t` by rw[] >>
      `PPROD (e INSERT s UNION t) * PPROD (s INTER t) = e * PPROD (s UNION t) * PPROD (s INTER t)` by rw[poly_prod_set_insert] >>
      `_ = e * (PPROD (s UNION t) * PPROD (s INTER t))` by rw[poly_mult_assoc] >>
      `_ = e * (PPROD s * PPROD t)` by rw[] >>
      `_ = (e * PPROD s) * PPROD t` by rw[poly_mult_assoc] >>
      `_ = PPROD (e INSERT s) * PPROD t` by rw[poly_prod_set_insert] >>
      rw[]
    ]
  ]);

(* Theorem: Ring r ==> !p. poly p ==> (PPROD {p} = p) *)
(* Proof:
   Since FINITE {}            by FINITE_EMPTY
     and pset {}              by NOT_IN_EMPTY

     PPROD {p}
   = PPROD (p INSERT {})      by notation
   = p * PPROD ({} DELETE p)  by poly_prod_set_thm
   = p * PPROD {}             by DELETE_NON_ELEMENT
   = p * |1|                  by poly_prod_set_empty
   = p                        by poly_mult_rone
*)
val poly_prod_set_sing = store_thm(
  "poly_prod_set_sing",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (PPROD {p} = p)``,
  rw[poly_prod_set_thm, poly_prod_set_empty]);

(* Theorem: Ring r ==> !s. FINITE s /\ pset s ==> !u v. s =|= u # v ==> (PPROD s = PPROD u * PPROD v) *)
(* Proof:
   Note pset u /\ pset v           by poly_set_subset_poly_set, SUBSET_UNION
    and FINITE u /\ FINITE v       by FINITE_UNION
    ==> poly (PPROD s)             by poly_prod_set_poly
    and poly (PPROD u)             by poly_prod_set_poly
    and poly (PPROD v)             by poly_prod_set_poly
   Also PPROD (u INTER v) = |1|    by DISJOINT_DEF, poly_prod_set_empty
        PPROD s
      = PPROD s * |1|              by poly_mult_rone
      = PPROD u * PPROD v          by poly_prod_set_mult_eqn
*)
val poly_prod_set_by_partition = store_thm(
  "poly_prod_set_by_partition",
  ``!r:'a ring. Ring r ==> !s. FINITE s /\ pset s ==>
   !u v. s =|= u # v ==> (PPROD s = PPROD u * PPROD v)``,
  rpt strip_tac >>
  `pset u /\ pset v` by rw[poly_set_subset_poly_set] >>
  `FINITE u /\ FINITE v` by metis_tac[FINITE_UNION] >>
  `poly (PPROD s) /\ poly (PPROD u) /\ poly (PPROD v)` by rw[poly_prod_set_poly] >>
  `PPROD (u INTER v) = |1|` by metis_tac[DISJOINT_DEF, poly_prod_set_empty] >>
  metis_tac[poly_prod_set_mult_eqn, poly_mult_rone]);

(* Theorem: Ring r ==> !s. FINITE s /\ pset s ==> !p. p IN s ==> p pdivides (PPROD s) *)
(* Proof:
   Let t = s DELETE p.
   Since FINITE t                   by FINITE_DELETE
     and t SUBSET s                 by DELETE_SUBSET
     and !p. p IN t ==> poly p      by IN_DELETE
   Hence PPROD s
       = PPROD (p INSERT t)         by INSERT_DELETE
       = p * PPROD (t DELETE p)     by poly_prod_set_thm
       = p * PPROD (s DELETE p)     by DELETE_DELETE
       = PPROD t * p                by poly_mult_comm
   Now poly p /\ poly PPROD t       by poly_prod_set_poly
   Therefore p pdivides (PPROD s)   by poly_divides_def
*)
val poly_prod_set_element_divides = store_thm(
  "poly_prod_set_element_divides",
  ``!r:'a ring. Ring r ==> !s. FINITE s /\ pset s ==> !p. p IN s ==> p pdivides (PPROD s)``,
  rpt strip_tac >>
  qabbrev_tac `t = s DELETE p` >>
  `s = p INSERT t` by rw[Abbr`t`] >>
  `FINITE t` by rw[Abbr`t`] >>
  `t DELETE p = s DELETE p` by rw[Abbr`t`] >>
  `t SUBSET s` by rw[Abbr`t`] >>
  `!p. p IN t ==> poly p` by rw[Abbr`t`] >>
  `PPROD s = p * PPROD t` by rw[poly_prod_set_thm] >>
  `poly p /\ poly (PPROD t)` by rw[poly_prod_set_poly] >>
  metis_tac[poly_divides_def, poly_mult_comm]);

(* Theorem: Ring r ==> !s t. FINITE t /\ pset t /\ s SUBSET t ==> (PPROD s) pdivides (PPROD t) *)
(* Proof:
   Let d = t DIFF s.
   Then t =|= s # d                    by partition_by_subset
   Note pset s                         by poly_set_subset_poly_set
   Also d SUBSET t                     by DIFF_SUBSET
     so pset d                         by poly_set_subset_poly_set
   Note FINITE s                       by SUBSET_FINITE
    and FINITE d                       by FINITE_DIFF
   Thus poly (PPROD s)                 by poly_prod_set_poly
    and poly (PPROD t)                 by poly_prod_set_poly
    and poly (PPROD d)                 by poly_prod_set_poly
   Note PPROD t
      = PPROD s * PPROD d              by poly_prod_set_by_partition
      = PPROD d * PPROD s              by poly_mult_comm
   Thus (PPROD s) pdivides (PPROD t)   by poly_divides_def
*)
val poly_prod_set_divides_prod_set = store_thm(
  "poly_prod_set_divides_prod_set",
  ``!r:'a ring. Ring r ==> !s t. FINITE t /\ pset t /\ s SUBSET t ==> (PPROD s) pdivides (PPROD t)``,
  rpt strip_tac >>
  qabbrev_tac `d = t DIFF s` >>
  `t =|= s # d` by metis_tac[partition_by_subset] >>
  `pset s` by rw[poly_set_subset_poly_set] >>
  `pset d` by rw[poly_set_subset_poly_set, Abbr`d`] >>
  `FINITE s` by metis_tac[SUBSET_FINITE] >>
  `FINITE d` by rw[Abbr`d`] >>
  `poly (PPROD s) /\ poly (PPROD t) /\ poly (PPROD d)` by rw[poly_prod_set_poly] >>
  `PPROD t = PPROD s * PPROD d` by metis_tac[poly_prod_set_by_partition] >>
  metis_tac[poly_divides_def, poly_mult_comm]);

(* Theorem: Ring r ==> !s. FINITE s /\ pset s /\ |0| IN s ==> (PPROD s = |0|) *)
(* Proof:
   Let t = s DELETE |0|.
   Then s =|= { |0| } # t         by partition_by_element
        PPROD s
      = PPROD { |0| } * PPROD t   by poly_prod_set_by_partition
      = |0| * PPROD t             by poly_prod_set_sing, pset s
      = |0|                       by poly_mult_lzero
*)
val poly_prod_set_eq_zero = store_thm(
  "poly_prod_set_eq_zero",
  ``!r:'a ring. Ring r ==> !s. FINITE s /\ pset s /\ |0| IN s ==> (PPROD s = |0|)``,
  rpt strip_tac >>
  qabbrev_tac `t = s DELETE |0|` >>
  `s =|= { |0| } # t` by rw[partition_by_element, Abbr`t`] >>
  metis_tac[poly_prod_set_by_partition, poly_prod_set_sing, poly_mult_lzero]);

(* Theorem: Ring r ==> !s. FINITE s /\ pset s ==> (PPROD ( |0| INSERT s) = |0|) *)
(* Proof:
   Let t = |0| INSERT s.
   Then |0| IN t              by COMPONENT
    and FINITE t              by FINITE_INSERT
    and pset t                by IN_INSERT, poly_zero_poly
   Thus PPROD t = |0|         by poly_prod_set_eq_zero
*)
val poly_prod_set_with_zero = store_thm(
  "poly_prod_set_with_zero",
  ``!r:'a ring. Ring r ==> !s. FINITE s /\ pset s ==> (PPROD ( |0| INSERT s) = |0|)``,
  rpt strip_tac >>
  qabbrev_tac `t = |0| INSERT s` >>
  `|0| IN t` by rw[Abbr`t`] >>
  `FINITE t` by rw[Abbr`t`] >>
  `pset t` by metis_tac[IN_INSERT, poly_zero_poly] >>
  rw[poly_prod_set_eq_zero]);

(* Theorem: Ring r ==> !s. FINITE s /\ pset s ==> (PPROD ( |1| INSERT s) = PPROD s) *)
(* Proof:
   If |1| IN s,
      Then |1| INSERT s = s     by ABSORPTION
      Thus PPROD ( |1| INSERT s) = PPROD s
   If |1| NOTIN s,
      Note poly (PPROD s)       by poly_prod_set_poly
        PPROD ( |1| INSERT s)
      = |1| * PPROD s           by poly_prod_set_insert, poly_one_poly
      = PPROD s                 by poly_mult_lone
*)
val poly_prod_set_with_one = store_thm(
  "poly_prod_set_with_one",
  ``!r:'a ring. Ring r ==> !s. FINITE s /\ pset s ==> (PPROD ( |1| INSERT s) = PPROD s)``,
  rpt strip_tac >>
  Cases_on `|1| IN s` >-
  metis_tac[ABSORPTION] >>
  rw[poly_prod_set_poly, poly_prod_set_insert]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Product of Monic Polynomials                                   *)
(* ------------------------------------------------------------------------- *)

(* Overload for a set with every element monic *)
val _ = overload_on("monic_set", ``\(r:'a ring) s. (!p. p IN s ==> monic p)``);

(* Overload monic_set r *)
val _ = overload_on("mset", ``monic_set r``);

(* Theorem: mset s ==> pset s *)
(* Proof: by poly_monic_poly *)
val monic_set_poly_set = store_thm(
  "monic_set_poly_set",
  ``!s. mset s ==> pset s``,
  rw_tac std_ss[poly_monic_poly]);

(* Theorem: (!x. x IN s ==> mset x) ==> mset (BIGUNION s) *)
(* Proof: by IN_BIGUNION *)
val monic_set_bigunion_monic_set = store_thm(
  "monic_set_bigunion_monic_set",
  ``!(r:'a ring) s. (!x. x IN s ==> mset x) ==> mset (BIGUNION s)``,
  metis_tac[IN_BIGUNION]);

(* Theorem: Ring r ==> !s. FINITE s /\ mset s ==> monic (PPROD s) *)
(* Proof:
   By FINITE_INDUCT on s.
   Base case: monic (PPROD {})
      Since PPROD {} = |1|        by poly_prod_set_empty
        and monic |1|             by poly_monic_one
      Hence true.
   Step case: monic e /\ e NOTIN s ==> monic (PPROD (e INSERT s))
     Note pset s                  by poly_monic_poly
      and PPROD (e INSERT s)
        = e * PPROD s             by poly_prod_set_insert
      But monic (PPROD s)         by induction hypothesis
      Hence product is monic      by poly_monic_mult_monic
*)
val poly_monic_prod_set_monic = store_thm(
  "poly_monic_prod_set_monic",
  ``!r:'a ring. Ring r ==> !s. FINITE s /\ mset s ==> monic (PPROD s)``,
  ntac 2 strip_tac >>
  `!s. FINITE s ==> mset s ==> monic (PPROD s)` suffices_by rw[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rw[] >-
  rw[poly_prod_set_empty] >>
  `monic e /\ poly e` by rw[] >>
  `pset s` by rw[] >>
  `PPROD (e INSERT s) = e * PPROD (s DELETE e)` by rw[poly_prod_set_thm] >>
  `_ = e * PPROD s` by metis_tac[DELETE_NON_ELEMENT] >>
  rw[poly_monic_mult_monic]);

(* Theorem: Ring r ==> !s. FINITE s /\ mset s /\ (!p. p IN s ==> (deg p = 1)) ==> deg (PPROD s) = CARD s *)
(* Proof:
   By induction on (CARD s).
   If s = {}, to show: deg (PPROD {}) = CARD {}
     LHS = deg (PPROD {}))
         = deg |1|                   by poly_prod_set_empty
         = 0                         by poly_deg_one
         = CARD {}                   by CARD_EMPTY
         = RHS
   If s <> {}, let p = CHOICE s, t = REST s.
     Note that monic p                                   by CHOICE_DEF
           and !p. p IN t ==> monic p /\ (deg p = 1)     by REST_SUBSET
           and monic (PPROD t)                           by poly_monic_prod_set_monic
           and p NOTIN t                                 by CHOICE_NOT_IN_REST
       and !p. p IN t ==> poly p                         by poly_monic_poly
     LHS = deg (PPROD s)
         = deg (PPROD (p INSERT t))                      by CHOICE_INSERT_REST
         = deg (p * PPROD (t DELETE p))                  by poly_prod_set_thm
         = deg (p * PPROD t)                             by DELETE_NON_ELEMENT
         = deg p + deg (PPROD t)                         by poly_monic_deg_mult
         = deg p + CARD t                                by induction hypothesis
         = 1 + CARD t                                    by CHOICE_DEF
         = 1 + (CARD s - 1)                              by CARD_REST
         = CARD s                                        by arithmetic
         = RHS
*)
val poly_monic_prod_set_monomials_deg = store_thm(
  "poly_monic_prod_set_monomials_deg",
  ``!r:'a ring. Ring r ==> !s. FINITE s /\ mset s /\ (!p. p IN s ==> (deg p = 1)) ==>
      (deg (PPROD s) = CARD s)``,
  rpt strip_tac >>
  completeInduct_on `CARD s` >>
  rule_assum_tac(SIMP_RULE bool_ss[GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO]) >>
  rw_tac std_ss[] >>
  Cases_on `s = {}` >-
  rw[poly_prod_set_empty] >>
  `?p t. (p = CHOICE s) /\ (t = REST s) /\ (s = p INSERT t)` by rw[CHOICE_INSERT_REST] >>
  `CARD t < CARD s` by metis_tac[CARD_REST, CARD_EQ_0, DECIDE``!n. n <> 0 ==> n - 1 < n``] >>
  `FINITE t` by metis_tac[REST_SUBSET, SUBSET_FINITE] >>
  `mset t /\ !p. p IN t ==> (deg p = 1)` by rw[REST_SUBSET, SUBSET_DEF] >>
  `monic (PPROD t)` by rw[poly_monic_prod_set_monic] >>
  `pset t` by rw[] >>
  `deg (PPROD s) = deg (p * PPROD (t DELETE p))` by rw[poly_prod_set_thm] >>
  `_ = deg (p * PPROD t)` by metis_tac[CHOICE_NOT_IN_REST, DELETE_NON_ELEMENT] >>
  `_ = deg p + deg (PPROD t)` by rw[poly_monic_deg_mult] >>
  `_ = 1 + CARD t` by rw[] >>
  `_ = 1 + (CARD s - 1)` by metis_tac[CARD_REST] >>
  `_ = CARD s` by rw_tac arith_ss[] >>
  rw[]);

(* Theorem: FINITE s /\ mset s ==> ulead (PPROD s) *)
(* Proof:
   Note monic (PPROD s)      by poly_monic_prod_set_monic
     so ulead (PPROD s)      by poly_monic_poly, poly_monic_lead, ring_unit_one
*)
val poly_monic_prod_set_ulead = store_thm(
  "poly_monic_prod_set_ulead",
  ``!r:'a ring. Ring r ==> !s. FINITE s /\ mset s ==> ulead (PPROD s)``,
  rw[poly_monic_prod_set_monic, ring_unit_one]);

(* Theorem: FINITE s /\ (!z. z IN s ==> monic z /\ 0 < deg z) /\ s <> {} ==> pmonic (PPROD s) *)
(* Proof:
   This is to show:
   (1) poly (PPROD s)
       Since !z. z IN s ==> poly z    by poly_monic_poly
       Hence poly (PPROD s)           by poly_prod_set_poly
   (2) unit (lead (PPROD s))
       Since monic (PPROD s)                           by poly_monic_prod_set_monic
        thus lead (PPROD s) = #1                       by poly_monic_lead
          or unit (lead (PPROD s))                     by ring_unit_one
   (3) 0 < deg (PPROD s)
       By finite induction.
       Base case: {} <> {} ==> 0 < deg (PPROD {})
          Since {} <> {} is false, this is true.
       Step case: 0 < deg (PPROD (e INSERT s))
          Since !z. z IN s ==> monic z /\ 0 < deg z    by IN_INSERT
            and !z. z IN s ==> poly z                  by poly_monic_poly
            and e IN e INSERT s                        by COMPONENT
          If s = {},
             Then e INSERT s = e INSERT {} = {e}       by INSERT_SING_UNION, UNION_EMPTY
              and monic e /\ 0 < deg e                 by implication, e IN e INSERT s
            Since PPROD {e} = e                        by poly_prod_set_sing
            Hence 0 < deg (PPROD (e INSERT s))         by 0 < deg e
          If s <> {},
            Since PPROD (e INSERT s)
                = e * PPROD s                          by poly_prod_set_insert
            Since monic e /\ 0 < deg e                 by implication, e IN e INSERT s
              and monic (PPROD s)                      by poly_monic_prod_set_monic
              and 0 < deg (PPROD s)                    by induction hypothesis
             thus deg (e * PPROD s) = deg e + deg (PPROD s)   by poly_monic_deg_mult
            Hence 0 < deg (PPROD (e INSERT s))                by ADD_EQ_0
*)
val poly_monic_prod_set_pmonic = store_thm(
  "poly_monic_prod_set_pmonic",
  ``!r:'a ring. Ring r ==> !s. FINITE s /\ mset s /\
     (!p. p IN s ==> 0 < deg p) /\ s <> {} ==> pmonic (PPROD s)``,
  rpt strip_tac >-
  rw[poly_prod_set_poly] >-
 (`monic (PPROD s)` by rw[poly_monic_prod_set_monic] >>
  metis_tac[poly_monic_lead, ring_unit_one]) >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  qid_spec_tac `s` >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw[] >>
  `mset s /\ !p. p IN s ==> 0 < deg p` by rw[] >>
  `pset s` by rw[] >>
  `e IN e INSERT s` by rw[] >>
  Cases_on `s = {}` >-
  rw[poly_prod_set_sing] >>
  `PPROD (e INSERT s) = e * PPROD s` by rw[poly_prod_set_insert] >>
  `monic e /\ 0 < deg e` by rw[] >>
  `monic (PPROD s) /\ 0 < deg (PPROD s)` by rw[poly_monic_prod_set_monic] >>
  `deg (e * PPROD s) = deg e + deg (PPROD s)` by rw[poly_monic_deg_mult] >>
  metis_tac[ADD_EQ_0, NOT_ZERO]);

(* Theorem: Ring r ==> !s. FINITE s /\ mset s ==> (deg (PPROD s) = SIGMA deg s) *)
(* Proof:
   By finite induction on s.
   Base: deg (PPROD {}) = SIGMA deg {}
         deg (PPROD {})
       = deg |1|           by poly_prod_set_empty
       = 0                 by poly_deg_one
       = SIGMA deg {}      by SUM_IMAGE_EMPTY
   Step: e NOTIN s ==> deg (PPROD (e INSERT s)) = SIGMA deg (e INSERT s)
     Note !p. p IN s ==> monic p
      ==> !p. p IN s ==> poly p       by poly_monic_poly
     Given !p. p IN (e INSERT s) ==> monic p,
     Since e IN (e INSERT s)          by IN_INSERT
      thus monic e and poly e         by poly_monic_poly
       and monic (PPROD s)            by poly_monic_prod_set_monic

       deg (PPROD (e INSERT s))
     = deg (e * PPROD (s DELETE e))   by poly_prod_set_thm
     = deg (e * PPROD s)              by DELETE_NON_ELEMENT
     = deg e + deg (PPROD s)          by poly_monic_deg_mult
     = deg e + SIGMA deg s            by induction hypothesis
     = deg e + SIGMA deg (s DELETE e) by DELETE_NON_ELEMENT
     = SIGMA deg (e INSERT s)         by SUM_IMAGE_THM
*)
val poly_monic_prod_set_deg = store_thm(
  "poly_monic_prod_set_deg",
  ``!r:'a ring. Ring r ==> !s. FINITE s /\ mset s ==> (deg (PPROD s) = SIGMA deg s)``,
  ntac 2 strip_tac >>
  `!s. FINITE s ==> mset s ==> (deg (PPROD s) = SIGMA deg s)` suffices_by rw[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  rw[poly_prod_set_empty, SUM_IMAGE_EMPTY] >>
  `monic e /\ poly e` by rw[] >>
  `monic (PPROD s)` by rw[poly_monic_prod_set_monic] >>
  `mset s` by rw[] >>
  `s DELETE e = s` by metis_tac[DELETE_NON_ELEMENT] >>
  `deg (PPROD (e INSERT s)) = deg (e * PPROD s)` by rw[poly_prod_set_thm] >>
  `_ = deg e + deg (PPROD s)` by rw[poly_monic_deg_mult] >>
  `_ = deg e + SIGMA deg s` by rw[] >>
  `_ = SIGMA deg (e INSERT s)` by rw[SUM_IMAGE_THM] >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Sets for Field.                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FINITE s /\ (!z. z IN s ==> monic z) ==>
            (PPROD s) pdivides |1| <=> (PPROD s = |1|) *)
(* Proof:
   Note monic (PPROD s)           by poly_monic_prod_set_monic
   Thus (PPROD s) pdivides |1|
    <=> (PPROD s = |1|)           by poly_monic_divides_one
*)
val poly_monic_prod_set_divides_one = store_thm(
  "poly_monic_prod_set_divides_one",
  ``!r:'a field. Field r ==> !s. FINITE s /\ (!z. z IN s ==> monic z) ==>
   ((PPROD s) pdivides |1| <=> ((PPROD s) = |1|))``,
  rw[poly_monic_prod_set_monic, poly_monic_divides_one]);

(* Theorem: Field r ==> !s. FINITE s /\ pset s /\ (!p. p IN s ==> p <> |0|) ==> PPROD s <> |0| *)
(* Proof:
   By finite induction on s.
   Base: PPROD {} = |0| ==> F
      True by contradiction:
         PPROD {} = |1|        by poly_prod_set_empty
                 <> |0|        by poly_one_ne_poly_zero
   Step: e NOTIN s /\ PPROD (e INSERT s) = |0| ==> F
      Given !p. p IN e INSERT s ==> poly p /\ p <> |0|
        ==> poly e /\ e <> |0| /\
            pset s /\ !p. p IN s ==> p <> |0|   by IN_INSERT
       Thus PPROD (e INSERT s)
          = e * PPROD s               by poly_prod_set_insert
        Now PPROD s <> |0|            by induction hypothesis
        and poly (PPROD s)            by poly_prod_set_poly
      Hence e * PPROD s <> |0|        by poly_mult_eq_zero
      This contradicts PPROD (e INSERT s) = |0|.
*)
val poly_prod_set_nonzero = store_thm(
  "poly_prod_set_nonzero",
  ``!r:'a field. Field r ==> !s. FINITE s /\ pset s /\ (!p. p IN s ==> p <> |0|) ==> PPROD s <> |0|``,
  ntac 2 strip_tac >>
  `Ring r /\ #1 <> #0 /\ |1| <> |0|` by rw[] >>
  `!s. FINITE s ==> pset s /\ (!p. p IN s ==> p <> |0|) ==> PPROD s <> |0|` suffices_by rw[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  metis_tac[poly_prod_set_empty] >>
  `poly e /\ e <> |0| /\ pset s /\ !p. p IN s ==> p <> |0|` by rw[] >>
  `PPROD (e INSERT s) = e * PPROD s` by rw[GSYM poly_prod_set_insert] >>
  `poly (PPROD s)` by rw[poly_prod_set_poly] >>
  metis_tac[poly_mult_eq_zero]);

(* Theorem: Field r ==>
   !s. FINITE s /\ pset s /\ (!p. p IN s ==> p <> |0|) ==> ulead (PPROD s) *)
(* Proof:
   Let z = PPROD s.
   Then poly z          by poly_prod_set_poly
    and z <> |0|        by poly_prod_set_nonzero
   Thus ulead z         by poly_field_poly_ulead
*)
val poly_prod_set_ulead = store_thm(
  "poly_prod_set_ulead",
  ``!r:'a field. Field r ==>
   !s. FINITE s /\ pset s /\ (!p. p IN s ==> p <> |0|) ==> ulead (PPROD s)``,
  ntac 4 strip_tac >>
  qabbrev_tac `z = PPROD s` >>
  `poly z` by rw[poly_prod_set_poly, Abbr`z`] >>
  `z <> |0|` by fs[poly_prod_set_nonzero, Abbr`z`] >>
  rw[poly_field_poly_ulead]);

(* Theorem: Field r ==> !s. FINITE s /\ pset s /\ (!p. p IN s ==> p <> |0|) ==>
            !p. p IN s ==> deg p <= deg (PPROD s) *)
(* Proof:
   By finite induction on s.
   Base: p IN {} ==> deg p <= deg (PPROD {})
      True since p IN {} = F       by MEMBER_NOT_EMPTY
   Step: e NOTIN s ==> deg p <= deg (PPROD (e INSERT s))
      Given !p. p IN e INSERT s ==> poly p /\ p <> |0|
        ==> poly e /\ e <> |0| /\
            !p. p IN s ==> poly p /\ p <> |0|   by IN_INSERT
       Thus PPROD (e INSERT s)
          = e * PPROD s               by poly_prod_set_insert
        Now PPROD s <> |0|            by poly_prod_set_nonzero
        and poly (PPROD s)            by poly_prod_set_poly
      Hence deg (PPROD (e INSERT s))
          = deg e + deg (PPROD s)     by poly_deg_mult_nonzero, Field r [1]
      Since p IN e INSERT s, by IN_INSERT:
      If p = e,
         then deg e <= deg (PPROD (e INSERT s))           by [1] -> [2]
      If p <> e,
         then deg (PPROD s) <= deg (PPROD (e INSERT s))   by [1]
          and p IN s                                      by IN_INSERT
        hence deg p <= deg (PPROD s)                      by induction hypothesis
           or deg p <= deg (PPROD (e INSERT s))           by LESS_EQ_TRANS, from [2]
*)
val poly_prod_set_deg_lower = store_thm(
  "poly_prod_set_deg_lower",
  ``!r:'a field. Field r ==> !s. FINITE s /\ pset s /\ (!p. p IN s ==> p <> |0|) ==>
   !p. p IN s ==> deg p <= deg (PPROD s)``,
  ntac 2 strip_tac >>
  `Ring r` by rw[] >>
  `!s. FINITE s ==> pset s /\ (!p. p IN s ==> p <> |0|) ==>
    !p. p IN s ==> deg p <= deg (PPROD s)` suffices_by rw[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  metis_tac[MEMBER_NOT_EMPTY] >>
  `poly e /\ e <> |0| /\ pset s /\ !p. p IN s ==> p <> |0|` by rw[] >>
  `PPROD (e INSERT s) = e * PPROD s` by rw[poly_prod_set_insert] >>
  `poly (PPROD s)` by rw[poly_prod_set_poly] >>
  `PPROD s <> |0|` by metis_tac[poly_prod_set_nonzero] >>
  `deg (PPROD (e INSERT s)) = deg e + deg (PPROD s)` by metis_tac[poly_deg_mult_nonzero] >>
  Cases_on `p = e` >| [
    `deg e <= deg (PPROD (e INSERT s))` by decide_tac >>
    rw[],
    `deg (PPROD s) <= deg (PPROD (e INSERT s))` by decide_tac >>
    `p IN s` by metis_tac[IN_INSERT] >>
    `deg p <= deg (PPROD s)` by metis_tac[] >>
    decide_tac
  ]);

(* Theorem: Field r ==> !s. FINITE s /\ pset s ==> (roots (PPROD s) = BIGUNION (IMAGE roots s)) *)
(* Proof:
   By finite induction on s.
   Base: roots (PPROD {}) = BIGUNION (IMAGE roots {})
      LHS = roots (PPROD {})
          = roots |1|                 by poly_prod_set_empty
          = roots [#1]                by poly_one, #1 <> #0
          = {}                        by poly_roots_const, #1 <> #0
      RHS = BIGUNION (IMAGE roots {})
          = BIGUNION {}               by IMAGE_EMPTY
          = {}                        by BIGUNION_EMPTY
   Step: pset s ==> (roots (PPROD s) = BIGUNION (IMAGE roots s)) ==>
         e NOTIN s /\ pset (e INSERT s) ==> roots (PPROD (e INSERT s)) = BIGUNION (IMAGE roots (e INSERT s))
      Note pset (e INSERT s)
       ==> poly e /\ pset s           by IN_INSERT
      also poly (PPROD s)             by poly_prod_set_poly

            roots (PPROD (e INSERT s))
          = roots (e * PPROD s)                           by poly_prod_set_insert, e NOTIN s
          = (roots e) UNION (roots (PPROD s))             by poly_roots_mult
          = (roots e) UNION (BIGUNION (IMAGE roots s))    by induction hypothesis
          = BIGUNION ((roots e) INSERT (IMAGE roots s))   by BIGUNION_INSERT
          = BIGUNION (IMAGE roots (e INSERT s))           by IMAGE_INSERT
*)
val poly_prod_set_roots = store_thm(
  "poly_prod_set_roots",
  ``!r:'a field. Field r ==> !s. FINITE s /\ pset s ==> (roots (PPROD s) = BIGUNION (IMAGE roots s))``,
  ntac 2 strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `!s. FINITE s ==> pset s ==> (roots (PPROD s) = BIGUNION (IMAGE roots s))` suffices_by rw[] >>
  Induct_on `FINITE` >>
  rpt strip_tac >| [
    rw[poly_prod_set_empty] >>
    metis_tac[poly_roots_const, ring_one_element, poly_one],
    `poly e /\ pset s` by metis_tac[IN_INSERT] >>
    `poly (PPROD s)` by rw[poly_prod_set_poly] >>
    rw[poly_prod_set_insert, poly_roots_mult]
  ]);

(* ------------------------------------------------------------------------- *)
(* Product of Polynomial by function image.                                  *)
(* ------------------------------------------------------------------------- *)

(* Overload product of polynomials by function image *)
val _ = overload_on ("poly_prod_image", ``\(r:'a ring) f s. PPROD (IMAGE f s)``);

(* Overload on poly_prod_image r *)
val _ = overload_on ("PPIMAGE", ``\f s. PPROD (IMAGE f s)``);

(* Theorem: PPIMAGE f {} = |1| *)
(* Proof:
     PPIMAGE f {}
   = PPROD (IMAGE f {})     by notation
   = PPROD {}               by IMAGE_EMPTY
   = |1|                    by poly_prod_set_empty
*)
val poly_prod_image_empty = store_thm(
  "poly_prod_image_empty",
  ``!r:'a ring. !f. PPIMAGE f {} = |1|``,
  rw[poly_prod_set_empty]);

(* Theorem: Ring r ==> !f. pmap f ==> !x. x IN R ==> (PPIMAGE f {x} = f x) *)
(* Proof:
   Note poly (f x)          by notation, x IN R
     PPIMAGE f {x}
   = PPROD (IMAGE f {x})    by notation
   = PPROD {f x}            by IMAGE_SING
   = f x                    by poly_prod_set_sing
*)
val poly_prod_image_sing = store_thm(
  "poly_prod_image_sing",
  ``!r:'a ring. Ring r ==> !f. pmap f ==> !x. x IN R ==> (PPIMAGE f {x} = f x)``,
  rw[poly_prod_set_sing]);

(* Theorem: Ring r ==> !s f. FINITE s /\ s SUBSET R /\ pmap f ==> poly (PPIMAGE f s) *)
(* Proof:
   Note FINITE (IMAGE f s)                     by IMAGE_FINITE
     Now !p. p IN (IMAGE f s)
     ==> !p. ?x. x IN s /\ (p = f x)           by IN_IMAGE
     ==> !p. ?x. x IN R /\ (p = f x)           by SUBSET_DEF
     ==> !p. poly p                            by notation
    Thus pset (IMAGE f s)                      by notation
   Hence poly (PPROD (IMAGE f s))              by poly_prod_set_poly
      or poly (PPIMAGE f s)                    by notation
*)
val poly_prod_image_poly = store_thm(
  "poly_prod_image_poly",
  ``!r:'a ring. Ring r ==> !s f. FINITE s /\ s SUBSET R /\ pmap f ==> poly (PPIMAGE f s)``,
  rw[FiniteRing_def] >>
  `FINITE (IMAGE f s)` by rw[IMAGE_FINITE] >>
  `pset (IMAGE f s)` by metis_tac[IN_IMAGE, SUBSET_DEF] >>
  rw[poly_prod_set_poly]);

(* The following is a generalisation of poly_mult_exp.
   Note:
   The INJ requirement is needed due to:
   If s = {p, -p}, then
       (PPROD s) ** 2 = (- p * p) = p ** 4
   but PPROD (s ** 2) = PPROD {p ** 2} = p ** 2, as set will eliminate duplicates.
*)

(* Theorem: Ring r ==> !s. FINITE s /\ pset s ==>
            !n. INJ (\p. p ** n) s univ(:'a poly) ==> ((PPROD s) ** n = PPIMAGE (\p. p ** n) s) *)
(* Proof:
   By finite induction on s.
   Base: PPROD {} ** n = PPIMAGE (\p. p ** n) {}
      LHS = PPROD {} ** n
          = |1| ** n             by poly_prod_set_empty
          = |1|                  by poly_one_exp
      RHS = PPIMAGE (\p. p ** n) {}
          = PPROD (IMAGE (\p. p ** n) {})   by notation
          = PPROD {}             by IMAGE_EMPTY
          = |1|                  by poly_prod_set_empty
   Step: pset s /\ INJ (\p. p ** n) s univ(:'a poly) ==> !n. PPROD s ** n = PPIMAGE (\p. p ** n) s ==>
         e NOTIN s /\ pset (e INSERT s) /\ INJ (\p. p ** n) (e INSERT s) univ(:'a poly) ==>
           PPROD (e INSERT s) ** n = PPIMAGE (\p. p ** n) (e INSERT s)
     Note pset (e INSERT s)
      ==> poly e /\ pset s         by IN_INSERT
      and poly (PPROD s)           by poly_prod_set_poly
     Let t = IMAGE (\p. p ** n) s.
     Then FINITE t                 by IMAGE_FINITE
      and pset t                   by poly_exp_poly
      and INJ (\p. p ** n) s univ(:'a poly) /\
          e ** n NOTIN t           by INJ_INSERT

          PPROD (e INSERT s) ** n
        = (e * PPROD s) ** n                 by poly_prod_set_insert
        = e ** n * (PPROD s) ** n            by poly_mult_exp
        = e ** n * PPIMAGE (\p. p ** n) s    by induction hypothesis
        = e ** n * (PPROD t)                 by notation
        = PPROD (e ** n INSERT t)            by poly_prod_set_insert, e ** n NOTIN t
        = PPROD (IMAGE (\p. p ** n) (e INSERT s))    by IMAGE_INSERT
        = PPIMAGE (\p. p ** n) (e INSERT s)          by notation
*)
val poly_prod_set_exp = store_thm(
  "poly_prod_set_exp",
  ``!r:'a ring. Ring r ==> !s. FINITE s /\ pset s ==>
   !n. INJ (\p. p ** n) s univ(:'a poly) ==> ((PPROD s) ** n = PPIMAGE (\p. p ** n) s)``,
  ntac 2 strip_tac >>
  `!s. FINITE s ==> pset s ==> !n. INJ (\p. p ** n) s univ(:'a poly) ==> ((PPROD s) ** n = PPIMAGE (\p. p ** n) s)` suffices_by rw[] >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[poly_prod_set_empty] >>
  `poly e /\ pset s` by rw[] >>
  `poly (PPROD s)` by rw[poly_prod_set_poly] >>
  fs[INJ_INSERT] >>
  qabbrev_tac `t = IMAGE (\p. p ** n) s` >>
  `FINITE t` by rw[Abbr`t`] >>
  (`pset t` by (rw[Abbr`t`] >> rw[poly_exp_poly])) >>
  (`e ** n NOTIN t` by (rw[Abbr`t`] >> metis_tac[])) >>
  `PPROD (e INSERT s) ** n = (e * PPROD s) ** n` by rw[poly_prod_set_insert] >>
  `_ = e ** n * (PPROD s) ** n` by rw[poly_mult_exp] >>
  `_ = e ** n * PPROD t` by rw[Abbr`t`] >>
  rw[poly_prod_set_insert]);

(* The following is a generalisation of poly_peval_mult.
   The INJ requirement is due to (peval s) will eliminiate duplicates.
*)

(* Theorem: Ring r ==> !s. FINITE s /\ pset s ==> !q. poly q /\
            INJ (\p. peval p q) s univ(:'a poly) ==> (peval (PPROD s) q = PPROD (IMAGE (\p. peval p q) s)) *)
(* Proof:
   By finite induction on s.
   Base: peval (PPROD {}) q = PPIMAGE (\p. peval p q) {}
      LHS = peval (PPROD {}) q
          = pevel |1| q                        by poly_prod_set_empty
          = |1|                                by poly_peval_one
      RHS = PPIMAGE (\p. peval p q) {}
          = PPROD (IMAGE (\p. peval p q) {})   by notation
          = PPROD {}                           by IMAGE_EMPTY
          = |1|                                by poly_peval_one
   Step: pset s ==> !q. poly q /\ INJ (\p. peval p q) s univ(:'a poly) ==>
           (peval (PPROD s) q = PPIMAGE (\p. peval p q) s) ==>
         e NOTIN s /\ pset (e INSERT s) /\ INJ (\p. peval p q) (e INSERT s) univ(:'a poly) ==>
          peval (PPROD (e INSERT s)) q = PPIMAGE (\p. peval p q) (e INSERT s)

     Note pset (e INSERT s)
      ==> poly e /\ pset s               by IN_INSERT
      and poly (PPROD s)                 by poly_prod_set_poly
     Let t = IMAGE (\p. peval p q) s.
     Then FINITE t                       by IMAGE_FINITE
      and pset t                         by poly_peval_poly
      and INJ (\p. peval p q) s univ(:'a poly) /\
          peval e q NOTIN t              by INJ_INSERT

         peval (PPROD (e INSERT s)) q
       = peval (e * PPROD s) q                        by poly_prod_set_insert
       = (peval e q) * (peval (PPROD s) q)            by poly_peval_mult
       = (peval e q) * PPIMAGE (\p. peval p q) s      by induction hypothesis
       = (peval e q) * PPROD t                        by notation
       = PPROD ((peval e q) INSERT t)                 by poly_prod_set_insert, peval e q NOTIN t
       = PPROD (IMAGE (\p. peval p q) (e INSERT s))   by IMAGE_INSERT
       = PPIMAGE (\p. peval p q) (e INSERT s)         by notation
*)
val poly_peval_poly_prod = store_thm(
  "poly_peval_poly_prod",
  ``!r:'a ring. Ring r ==> !s. FINITE s /\ pset s ==> !q. poly q /\
    INJ (\p. peval p q) s univ(:'a poly) ==> (peval (PPROD s) q = PPROD (IMAGE (\p. peval p q) s))``,
  ntac 2 strip_tac >>
  `!s. FINITE s ==> pset s ==> !q. poly q /\ INJ (\p. peval p q) s univ(:'a poly) ==> (peval (PPROD s) q = PPROD (IMAGE (\p. peval p q) s))` suffices_by rw[] >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[poly_prod_set_empty] >>
  `poly e /\ pset s` by rw[] >>
  `poly (PPROD s)` by rw[poly_prod_set_poly] >>
  qabbrev_tac `t = IMAGE (\p. peval p q) s` >>
  `FINITE t` by rw[Abbr`t`] >>
  (`pset t` by (rw[Abbr`t`] >> rw[])) >>
  fs[INJ_INSERT] >>
  (`peval e q NOTIN t` by (rw[Abbr`t`] >> metis_tac[])) >>
  rw[poly_prod_set_insert, poly_peval_mult, poly_prod_set_insert]);

(* ------------------------------------------------------------------------- *)
(* Product of Factors.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Overload product of factors *)
val _ = overload_on("poly_prod_factors", ``\(r:'a ring) s. PPIMAGE factor s``);
val _ = overload_on("PIFACTOR", ``poly_prod_factors r``);

(* Theorem: PIFACTOR {} = |1| *)
(* Proof:
     PIFACTOR {}
   = PPROD (IMAGE factor {})     by notation
   = PPROD {}                    by IMAGE_EMPTY
   = |1|                         by poly_prod_set_empty
*)
val poly_prod_factors_empty = store_thm(
  "poly_prod_factors_empty",
  ``!r:'a ring. PIFACTOR {} = |1|``,
  rw[poly_prod_set_empty]);

(* Theorem: Ring r /\ #1 <> #0 ==> !c. c IN R ==> (PIFACTOR {c} = factor c) *)
(* Proof:
   Note poly (factor c)              by poly_factor_poly
     PIFACTOR {c}
   = PPROD (IMAGE factor {c})        by notation
   = PPROD {factor c}                by IMAGE_SING
   = factor c                        by poly_prod_set_sing
*)
val poly_prod_factors_sing = store_thm(
  "poly_prod_factors_sing",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. c IN R ==> (PIFACTOR {c} = factor c)``,
  rw[poly_factor_poly, poly_prod_set_sing]);

(* Theorem: Ring r /\ #1 <> #0 ==> !s. FINITE s /\ s SUBSET R ==> poly (PIFACTOR s) *)
(* Proof:
    Note !x. x IN s ==> x IN R   by SUBSET_DEF
    Thus pset (IMAGE factor s)   by IN_IMAGE, poly_factor_poly
   Hence poly (PIFACTOR s)       by poly_prod_set_poly
*)
val poly_prod_factors_poly = store_thm(
  "poly_prod_factors_poly",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !s. FINITE s /\ s SUBSET R ==> poly (PIFACTOR s)``,
  rpt strip_tac >>
  `pset (IMAGE factor s)` by metis_tac[SUBSET_DEF, IN_IMAGE, poly_factor_poly] >>
  rw[poly_prod_set_poly]);

(* Theorem: Ring r /\ #1 <> #0 ==> !s. FINITE s /\ s SUBSET R ==> monic (PIFACTOR s) *)
(* Proof:
    Note !x. x IN s ==> x IN R   by SUBSET_DEF
    Thus mset (IMAGE factor s)   by IN_IMAGE, poly_factor_monic
   Hence monic (PIFACTOR s)      by poly_monic_prod_set_monic
*)
val poly_prod_factors_monic = store_thm(
  "poly_prod_factors_monic",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !s. FINITE s /\ s SUBSET R ==> monic (PIFACTOR s)``,
  rpt strip_tac >>
  `mset (IMAGE factor s)` by metis_tac[SUBSET_DEF, IN_IMAGE, poly_factor_monic] >>
  rw[poly_monic_prod_set_monic]);

(* Theorem: Ring r /\ #1 <> #0 ==> !s. FINITE s /\ s SUBSET R ==> (deg (PIFACTOR s) = CARD s) *)
(* Proof:
   Note !x. x IN s ==> x IN R                   by SUBSET_DEF
    ==> mset (IMAGE factor s)                   by IN_IMAGE, poly_factor_monic
   Also INJ factor s univ(:'a poly)             by INJ_DEF, poly_factor_eq
    and !x. x IN s ==> ((deg o factor) x = 1)   by poly_deg_factor

      deg (PIFACTOR s)
    = SIGMA deg (IMAGE factor s)                by poly_monic_prod_set_deg
    = SIGMA (deg o factor) s                    by sum_image_by_composition
    = 1 * CARD s                                by SIGMA_CONSTANT
    = CARD s                                    by MULT_LEFT_1
*)
val poly_prod_factors_deg = store_thm(
  "poly_prod_factors_deg",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !s. FINITE s /\ s SUBSET R ==> (deg (PIFACTOR s) = CARD s)``,
  rpt strip_tac >>
  `!x. x IN s ==> x IN R` by metis_tac[SUBSET_DEF] >>
  `mset (IMAGE factor s)` by metis_tac[IN_IMAGE, poly_factor_monic] >>
  (`INJ factor s univ(:'a poly)` by (rw[INJ_DEF] >> metis_tac[poly_factor_eq])) >>
  `!x. x IN s ==> ((deg o factor) x = 1)` by rw[poly_deg_factor] >>
  `deg (PIFACTOR s) = SIGMA deg (IMAGE factor s)` by rw[poly_monic_prod_set_deg] >>
  `_ = SIGMA (deg o factor) s` by rw[sum_image_by_composition] >>
  `_ = 1 * CARD s` by rw[SIGMA_CONSTANT] >>
  decide_tac);

(* Theorem: Field r ==> !s. FINITE s /\ s SUBSET R ==> (roots (PIFACTOR s) = s) *)
(* Proof:
    Note !x. x IN s ==> x IN R   by SUBSET_DEF
    Thus pset (IMAGE factor s)   by IN_IMAGE, poly_factor_poly
     and FINITE (IMAGE factor s) by IMAGE_FINITE

      roots (PIFACTOR s)
    = roots (PPROD (IMAGE factor s))             by notation
    = BIGUNION (IMAGE roots (IMAGE factor s)))   poly_prod_set_roots
    = BIGUNION (IMAGE (roots o factor) s)        by IMAGE_COMPOSE
    = BIGUNION (IMAGE (\x. {x}) s)               by poly_roots_factor_image
    = s                                          by BIGUNION_ELEMENTS_SING
*)
val poly_prod_factors_roots = store_thm(
  "poly_prod_factors_roots",
  ``!r:'a field. Field r ==> !s. FINITE s /\ s SUBSET R ==> (roots (PIFACTOR s) = s)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `pset (IMAGE factor s)` by metis_tac[SUBSET_DEF, IN_IMAGE, poly_factor_poly] >>
  `FINITE (IMAGE factor s)` by rw[] >>
  `roots (PIFACTOR s) = BIGUNION (IMAGE roots (IMAGE factor s))` by rw[poly_prod_set_roots] >>
  `_ = BIGUNION (IMAGE (roots o factor) s)` by rw[IMAGE_COMPOSE] >>
  `_ = BIGUNION (IMAGE (\x. {x}) s)` by rw[poly_roots_factor_image] >>
  `_ = s` by rw[BIGUNION_ELEMENTS_SING] >>
  rw[]);

(* Theorem: Field r ==> !s. FINITE s /\ s SUBSET R ==> (deg (PIFACTOR s) = CARD (roots (PIFACTOR s))) *)
(* Proof:
     deg (PIFACTOR s)
   = CARD s                     by poly_prod_factors_deg
   = CARD (roots (PIFACTOR s))  by poly_prod_factors_roots
*)
val poly_prod_factors_deg_eq_card_roots = store_thm(
  "poly_prod_factors_deg_eq_card_roots",
  ``!r:'a field. Field r ==> !s. FINITE s /\ s SUBSET R ==>
          (deg (PIFACTOR s) = CARD (roots (PIFACTOR s)))``,
  rw[poly_prod_factors_deg, poly_prod_factors_roots]);

(* Note: This is worse than poly_prod_factors_deg before:
|- !r. Ring r /\ #1 <> #0 ==> !s. FINITE s /\ s SUBSET R ==> (deg (PIFACTOR s) = CARD s)
However, this result does show that (PIFACTOR s) is splitting, as deg p = CARD (roots p).
*)

(* Theorem: Field r ==> !s. FINITE s /\ s SUBSET R ==>
            !c. c IN R ==> ((factor c) pdivides (PIFACTOR s) <=> c IN s) *)
(* Proof:
   Note poly (PIFACTOR s)               by poly_prod_factors_poly
       c IN R /\ (factor c) pdivides (PIFACTOR s)
   <=> c IN (roots (PIFACTOR s))        by poly_root_factor
   <=> c IN s                           by poly_prod_factors_roots
*)
val poly_prod_factors_factor = store_thm(
  "poly_prod_factors_factor",
  ``!r:'a field. Field r ==> !s. FINITE s /\ s SUBSET R ==>
   !c. c IN R ==> ((factor c) pdivides (PIFACTOR s) <=> c IN s)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `poly (PIFACTOR s)` by rw[poly_prod_factors_poly] >>
  metis_tac[poly_root_factor, poly_prod_factors_roots]);

(* Theorem: Field r ==> !s. FINITE s /\ s SUBSET R ==> PIFACTOR s <> |0| *)
(* Proof:
   Note !x. x IN s ==> x IN R      by SUBSET_DEF
     so pset (IMAGE factor s)      by IN_IMAGE, poly_factor_poly
    and !p. p IN (IMAGE factor s) ==> p <> |0|   by IN_IMAGE, poly_factor_nonzero
   also FINITE (IMAGE factor s)    by IMAGE_FINITE
    ==> PIFACTOR s <> |0|          by poly_prod_set_nonzero
*)
val poly_prod_factors_nonzero = store_thm(
  "poly_prod_factors_nonzero",
  ``!r:'a field. Field r ==> !s. FINITE s /\ s SUBSET R ==> PIFACTOR s <> |0|``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `!x. x IN s ==> x IN R` by metis_tac[SUBSET_DEF] >>
  (`pset (IMAGE factor s)` by (rw[] >> rw[poly_factor_poly])) >>
  (`!p. p IN (IMAGE factor s) ==> p <> |0|` by (rw_tac std_ss[IN_IMAGE] >> rw[poly_factor_nonzero])) >>
  `FINITE (IMAGE factor s)` by rw[] >>
  metis_tac[poly_prod_set_nonzero]);

(* Theorem: Field r ==> !s t. FINITE s /\ s SUBSET R /\ FINITE t /\ t SUBSET R ==>
            ((PIFACTOR t) pdivides (PIFACTOR s) <=> t SUBSET s) *)
(* Proof:
   Let p = PIFACTOR t, q = PIFACTOR s.
   Note poly p /\ poly q       by poly_prod_factors_poly

   If part: p pdivides q ==> t SUBSET s
      Then ?u. poly u /\ (q = u * p)             by poly_divides_def
      thus roots q = (roots u) UNION (roots p)   by poly_roots_mult
        or (roots p) SUBSET (roots q)            by SUBSET_UNION
        or         t SUBSET s                    by poly_prod_factors_roots

   Only-if part: t SUBSET s ==> p pdivides q
      If t = {},
         Then p = |1|          by poly_prod_factors_empty
          and |1| pdivides q   by poly_one_divides_all
      If t <> {},
         Then CARD t <> 0      by CARD_EQ_0
        Since deg p = CARD t   by poly_prod_factors_deg
           so 0 < deg p        by above
         Note monic p          by poly_prod_factors_monic
           so pmonic p         by 0 < deg p
          ==> q = (q / p) * p + (q % p) /\ deg (q % p) < deg p   by poly_division

         Let v = q % p.
        Claim: v = |0|, so that p pdivides q       by poly_add_rzero, poly_divides_def
        Proof: By contradiction, suppose v <> |0|
          Note FINITE (roots v)                    by poly_roots_finite, v <> |0|
           and CARD (roots v) <= deg v             by poly_roots_count, v <> |0|

           Now (roots p) SUBSET (roots q)          by poly_prod_factors_roots, t SUBSET s
           and (roots p) SUBSET (roots v)          by poly_roots_remainder, (roots p) SUBSET (roots q)
          Thus CARD (roots p) <= CARD (roots v)    by CARD_SUBSET, FINITE (roots v)
           But CARD (roots p) = CARD t             by poly_prod_factors_roots
                              = deg p              by poly_prod_factors_deg
          Overall, deg p <= deg v,
          and this contradicts deg v < deg p.
*)
val poly_prod_factors_divisibility = store_thm(
  "poly_prod_factors_divisibility",
  ``!r:'a field. Field r ==> !s t. FINITE s /\ s SUBSET R /\ FINITE t /\ t SUBSET R ==>
   ((PIFACTOR t) pdivides (PIFACTOR s) <=> t SUBSET s)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  qabbrev_tac `p = PIFACTOR t` >>
  qabbrev_tac `q = PIFACTOR s` >>
  `poly p /\ poly q` by rw[poly_prod_factors_poly, Abbr`p`, Abbr`q`] >>
  rw[EQ_IMP_THM] >| [
    `?u. poly u /\ (q = u * p)` by rw[GSYM poly_divides_def] >>
    `roots q = (roots u) UNION (roots p)` by rw[poly_roots_mult] >>
    `(roots p) SUBSET (roots q)` by rw[] >>
    metis_tac[poly_prod_factors_roots],
    Cases_on `t = {}` >-
    rw[poly_prod_factors_empty, poly_one_divides_all, Abbr`p`] >>
    `CARD t <> 0` by rw[CARD_EQ_0] >>
    `deg p = CARD t` by rw[poly_prod_factors_deg, Abbr`p`] >>
    `0 < deg p` by decide_tac >>
    `monic p` by rw[poly_prod_factors_monic, Abbr`p`] >>
    `pmonic p` by rw[] >>
    `poly (q / p) /\ poly (q % p)` by rw[] >>
    qabbrev_tac `v = q % p` >>
    `(q = (q / p) * p + v) /\ deg v < deg p` by rw[poly_division, Abbr`v`] >>
    `v = |0|` by
  (spose_not_then strip_assume_tac >>
    `FINITE (roots v)` by rw[poly_roots_finite] >>
    `CARD (roots v) <= deg v` by rw[poly_roots_count] >>
    `deg p = CARD (roots p)` by rw[poly_prod_factors_roots, poly_prod_factors_deg, Abbr`p`] >>
    `(roots p) SUBSET (roots q)` by rw[poly_prod_factors_roots, Abbr`p`, Abbr`q`] >>
    `(roots p) SUBSET (roots v)` by rw[poly_roots_remainder, Abbr`v`] >>
    `CARD (roots p) <= CARD (roots v)` by rw[CARD_SUBSET] >>
    decide_tac) >>
    metis_tac[poly_divides_def, poly_add_rzero, poly_mult_poly]
  ]);

(* ------------------------------------------------------------------------- *)
(* Product of Factor of Roots.                                               *)
(* ------------------------------------------------------------------------- *)

(* Define poly_prod_factor_roots r p = (X - r_1)(X - r_2)...(X - r_n) where r_j are roots of p *)
(*
val poly_prod_factor_roots_def = Define`
  poly_prod_factor_roots (r:'a ring) (p:'a poly) = PPROD {factor c | c | c IN roots p}
`;
*)
(* overload on poly_prod_factor_roots r p *)
val _ = overload_on ("poly_prod_factor_roots", ``\(r:'a ring) p. PIFACTOR (roots p)``);
val _ = overload_on ("PFROOTS", ``poly_prod_factor_roots r``);

(* Theorem: (roots p = {}) ==> (PFROOTS p = |1|) *)
(* Proof:
    PFROOTS p
  = PIFACTOR (roots p)    by notation
  = PIFACTOR {}           by roots p = {}
  = |1|                   by poly_prod_image_empty
*)
val poly_prod_factor_roots_empty = store_thm(
  "poly_prod_factor_roots_empty",
  ``!r:'a ring. !p. (roots p = {}) ==> (PFROOTS p = |1|)``,
  metis_tac[poly_prod_image_empty]);

(* export simple results *)
val _ = export_rewrites["poly_prod_factor_roots_empty"];


(* Theorem: Field r ==> !p. poly p /\ p <> |0| ==> poly (PFROOTS p) *)
(* Proof:
     PFROOTS p
   = PIFACTOR (roots p)            by notation
   Now FINITE (roots p)            by poly_roots_finite, Field r, p <> |0|.
   and (roots p) SUBSET R          by poly_roots_member, SUBSET_DEF
    so poly (PIFACTOR (roots p))   by poly_prod_factors_poly
*)
val poly_prod_factor_roots_poly = store_thm(
  "poly_prod_factor_roots_poly",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==> poly (PFROOTS p)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `FINITE (roots p)` by rw[poly_roots_finite] >>
  `(roots p) SUBSET R` by rw[poly_roots_member, SUBSET_DEF] >>
  rw[poly_prod_factors_poly]);

(* export simple results *)
val _ = export_rewrites["poly_prod_factor_roots_poly"];

(* Theorem: poly p /\ p <> |0| ==> monic (PFROOTS p) *)
(* Proof:
     PFROOTS p
   = PIFACTOR (roots p)            by notation
   Now FINITE (roots p)            by poly_roots_finite, Field r, p <> |0|.
   and (roots p) SUBSET R          by poly_roots_member, SUBSET_DEF
    so monic (PIFACTOR (roots p))  by poly_prod_factors_monic
*)
val poly_prod_factor_roots_monic = store_thm(
  "poly_prod_factor_roots_monic",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==> monic (PFROOTS p)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `FINITE (roots p)` by rw[poly_roots_finite] >>
  `(roots p) SUBSET R` by rw[poly_roots_member, SUBSET_DEF] >>
  rw[poly_prod_factors_monic]);

(* export simple results *)
val _ = export_rewrites["poly_prod_factor_roots_monic"];

(* Theorem: Field r ==> !p. poly p /\ p <> |0| ==> (deg (PFROOTS p) = CARD (roots p)) *)
(* Proof:
     PFROOTS p
   = PIFACTOR (roots p)            by notation
   Now FINITE (roots p)            by poly_roots_finite, Field r, p <> |0|.
   and (roots p) SUBSET R          by poly_roots_member, SUBSET_DEF
    so deg (PIFACTOR (roots p)) = CARD (roots p)  by poly_prod_factors_deg
*)
val poly_prod_factor_roots_deg = store_thm(
  "poly_prod_factor_roots_deg",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==> (deg (PFROOTS p) = CARD (roots p))``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `FINITE (roots p)` by rw[poly_roots_finite] >>
  `(roots p) SUBSET R` by rw[poly_roots_member, SUBSET_DEF] >>
  rw[poly_prod_factors_deg]);

(* Theorem: Field r ==> !p. poly p /\ p <> |0| ==> (roots (PFROOTS p) = roots p) *)
(* Proof:
     PFROOTS p
   = PIFACTOR (roots p)            by notation
   Now FINITE (roots p)            by poly_roots_finite, Field r, p <> |0|.
   and (roots p) SUBSET R          by poly_roots_member, SUBSET_DEF
    so roots (PIFACTOR (roots p)) = roots p  by poly_prod_factors_roots
*)
val poly_prod_factor_roots_roots = store_thm(
  "poly_prod_factor_roots_roots",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==> (roots (PFROOTS p) = roots p)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `FINITE (roots p)` by rw[poly_roots_finite] >>
  `(roots p) SUBSET R` by rw[poly_roots_member, SUBSET_DEF] >>
  rw[poly_prod_factors_roots]);

(* Theorem: poly p /\ p <> |0| ==> (PFROOTS p) pdivides p *)
(* Proof:
   If there is no root for p,
          roots p = {}
      ==> PFROOTS p = |1|              by poly_prod_factor_roots_empty
      But |1| pdivides p               by poly_one_divides_all
      Hence (PFROOTS p) pdivides p.
   If there is a root for p,
      Since FINITE (roots p)                     by poly_roots_finite
         so CARD (roots p) <> 0                  by CARD_EQ_0
        Now monic (PFROOTS p)                    by poly_prod_factor_roots_monic
        and deg (PFROOTS p) = CARD (roots p)     by poly_prod_factor_roots_deg
         so 0 < deg (PFROOTS p)
      Hence pmonic (PFROOTS p),
         so p = s * (PFROOTS p) + t                     by poly_division_eqn
       with deg t < deg (PFROOTS p) = CARD (roots p)    by above, [1]
      If t = |0|,
            p = s * (PFROOTS p)                         by poly_add_rzero
         thus (PFROOTS p) pdivides p                    by poly_divides_def
      If t <> |0|,
      Then roots of p will give roots of t:
         Show: (roots p) SUBSET (roots t)
         Since t = p - s * (PFROOTS p)                  by poly_sub_eq_add
            or t = |1| * p + (-s) * (PFROOTS p)         by poly_mult_lone, poly_sub_def
           Now (roots p) SUBSET (roots (PFROOTS p))     by poly_prod_factor_roots_roots
          Thus (roots p) SUBSET (roots t)               by poly_roots_linear

      Now FINITE (roots t)                              by poly_roots_finite, t <> |0|
       so CARD (roots p) <= CARD (roots t)              by CARD_SUBSET, above, [2]
       or deg t < CARD (roots t)                        by [1], [2]
      But CARD (roots t) <= deg t                       by poly_roots_count
      so there is a contradiction.
*)
val poly_prod_factor_roots_divides = store_thm(
  "poly_prod_factor_roots_divides",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==> (PFROOTS p) pdivides p``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  Cases_on `roots p = {}` >-
  rw[poly_one_divides_all] >>
  `monic (PFROOTS p)` by rw[] >>
  `deg (PFROOTS p) = CARD (roots p)` by rw[poly_prod_factor_roots_deg] >>
  `FINITE (roots p)` by rw[poly_roots_finite] >>
  `CARD (roots p) <> 0` by rw[CARD_EQ_0] >>
  `0 < deg (PFROOTS p)` by decide_tac >>
  qabbrev_tac `q = (PFROOTS p)` >>
  `pmonic q` by rw[Abbr`q`] >>
  `?s t. poly s /\ poly t /\ (p = s * q + t) /\ (deg t < deg q)` by rw[poly_division_eqn] >>
  Cases_on `t = |0|` >-
  metis_tac[poly_divides_def, poly_mult_poly, poly_add_rzero] >>
  `(roots p) SUBSET (roots t)` by
  (qabbrev_tac `p = s * q + t` >>
  `t = p - s * q` by metis_tac[poly_sub_eq_add, poly_mult_poly] >>
  `t = |1| * p + (-s) * q` by rw[poly_sub_def] >>
  `(roots p) SUBSET (roots q)` by rw[poly_prod_factor_roots_roots, Abbr`q`] >>
  rw[poly_roots_linear]) >>
  `FINITE (roots t)` by rw[poly_roots_finite] >>
  `CARD (roots p) <= CARD (roots t)` by rw[CARD_SUBSET] >>
  `CARD (roots t) <= deg t` by rw[poly_roots_count] >>
  decide_tac);

(* Theorem: Field r ==> !p. monic p /\ (deg p = CARD (roots p)) ==> (PFROOTS p = p) *)
(* Proof:
   Since Field r /\ monic p
     ==> p <> |0|                            by poly_monic_nonzero
     ==> monic (PFROOTS p)                   by poly_prod_factor_roots_monic
     Now deg p = CARD (roots p)              by given
               = deg (PFROOTS p)             by poly_prod_factor_roots_deg
    Also PFROOTS p pdivides p                by poly_prod_factor_roots_divides
   Hence PFROOTS p = p                       by poly_monic_divides_eq_deg_eq
*)
val poly_prod_factor_roots_eq_poly = store_thm(
  "poly_prod_factor_roots_eq_poly",
  ``!r:'a field. Field r ==> !p. monic p /\ (deg p = CARD (roots p)) ==> (PFROOTS p = p)``,
  rpt strip_tac >>
  `p <> |0|` by rw[poly_monic_nonzero] >>
  `monic (PFROOTS p)` by rw[poly_prod_factor_roots_monic] >>
  `deg p = deg (PFROOTS p)` by rw[poly_prod_factor_roots_deg] >>
  `PFROOTS p pdivides p` by rw[poly_prod_factor_roots_divides] >>
  metis_tac[poly_monic_divides_eq_deg_eq]);

(* This is the better version of poly_prod_factor_roots_eq_poly
|- !r. Field r ==> !p. monic p /\ (deg p = CARD (roots p)) ==> (PFROOTS p = p)
*)

(* Theorem: Field r ==> !p. monic p ==> ((p = PFROOTS p) <=> (deg p = CARD (roots p))) *)
(* Proof:
   Since Field r /\ monic p
     ==> p <> |0|                            by poly_monic_nonzero
     ==> monic (PFROOTS p)                   by poly_prod_factor_roots_monic
    Note deg (PFROOTS p) = CARD (roots p)    by poly_prod_factor_roots_deg [1]
    Also PFROOTS p pdivides p                by poly_prod_factor_roots_divides
   If part: (p = PFROOTS p) ==> (deg p = CARD (roots p))
      True by [1] above.
   Only-if part: deg p = CARD (roots p) ==> p = PFROOTS p
      True by poly_monic_divides_eq_deg_eq
*)
val poly_prod_factor_roots_eq_poly_iff = store_thm(
  "poly_prod_factor_roots_eq_poly_iff",
  ``!r:'a field. Field r ==> !p. monic p ==> ((p = PFROOTS p) <=> (deg p = CARD (roots p)))``,
  rpt strip_tac >>
  `p <> |0|` by rw[poly_monic_nonzero] >>
  `monic (PFROOTS p)` by rw[poly_prod_factor_roots_monic] >>
  `deg (PFROOTS p) = CARD (roots p)` by rw[poly_prod_factor_roots_deg] >>
  `PFROOTS p pdivides p` by rw[poly_prod_factor_roots_divides] >>
  rw[EQ_IMP_THM] >-
  metis_tac[] >>
  metis_tac[poly_monic_divides_eq_deg_eq]);

(* Theorem: Field r ==> !p. monic p /\ (deg p = CARD (roots p)) ==> (p = PFROOTS p) *)
(* Proof: by poly_prod_factor_roots_eq_poly *)
val poly_eq_prod_factor_roots = store_thm(
  "poly_eq_prod_factor_roots",
  ``!r:'a field. Field r ==> !p. monic p /\ (deg p = CARD (roots p)) ==> (p = PFROOTS p)``,
  rw_tac std_ss[poly_prod_factor_roots_eq_poly]);

(* Theorem: Field r ==>
            !p. monic p /\ (deg p = CARD (roots p)) ==> (p = PPROD {X - c * |1| | c | c IN (roots p)}) *)
(* Proof:
   Note (roots p) SUBSET R                            by poly_roots_subset
   Then p = PFROOTS p                                 by poly_eq_prod_factor_roots
          = PPROD (IMAGE factor (roots p))            by notation
          = PPROD {X - c * |1| | c | c IN (roots p)   by poly_image_factor_subset
*)
val poly_eq_prod_factor_roots_alt = store_thm(
  "poly_eq_prod_factor_roots_alt",
  ``!r:'a field. Field r ==>
   !p. monic p /\ (deg p = CARD (roots p)) ==> (p = PPROD {X - c * |1| | c | c IN (roots p)})``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `(roots p) SUBSET R` by rw[poly_roots_subset] >>
  metis_tac[poly_eq_prod_factor_roots, poly_image_factor_subset]);

(* Theorem: Field r ==> !s. FINITE s /\ s SUBSET R ==>
            !p. monic p /\ p pdivides (PIFACTOR s) /\ ((roots p) INTER s = {}) ==> (p = |1|) *)
(* Proof:
    Note !x. x IN s ==> x IN R            by SUBSET_DEF
   Since (roots p) INTER s = {}           by given
     ==> !x. x IN s ==> ~(root p x)       by IN_INTER, poly_roots_member

   Step 1: show s SUBSET (roots t)
   Let q = PIFACTOR s.
    Then poly q                           by poly_prod_factors_poly
   Given p pdivides q
      so ?t. poly t /\ q = t * p          by poly_divides_def
      or !x. x IN s ==> eval q x = (eval t x) * (eval p x)   by poly_eval_mult
     But roots q = s       by poly_prod_factors_roots
      so !x. x IN s ==> eval q x = #0     by poly_root_def
     But ~(root p x), so eval p x <> #0   by poly_root_def
    Thus !x. x IN s ==> eval t x = #0     by field_mult_eq_zero
      or !x. x IN s ==> root t x          by poly_root_def
      so s SUBSET (roots t)

   Step 2: show q pdivides t
    Note q <> |0|                         by poly_prod_factors_nonzero
      so t <> |0|                         by poly_mult_lzero, q <> |0|
    thus FINITE (roots t)                 by poly_roots_finite, t <> |0|
    also (roots t) SUBSET R               by poly_roots_subset
     ==> q pdivides PIFACTOR (roots t)    by poly_prod_factors_divisibility
     but PIFACTOR (roots t) pdivides t    by poly_prod_factor_roots_divides
     and poly (PIFACTOR (roots t))        by poly_prod_factors_poly
      so q pdivides t                     by poly_divides_transitive

   Step 3: conclude
   Hence deg q <= deg t                   by poly_divides_deg_le
    Note p <> |0|                         by poly_monic_nonzero
     But deg q = deg t + deg p            by poly_deg_mult_nonzero, p <> |0|, t <> |0|
      so deg t + deg p <= deg t
     ==> deg p = 0
      or p = |1|                          by poly_monic_deg_0

   or for Step 3:
   this gives t = u * q,  so q = (u * q) * p, giving upoly p.
*)
val poly_monic_divides_poly_prod_factors_property = store_thm(
  "poly_monic_divides_poly_prod_factors_property",
  ``!r:'a field. Field r ==> !s. FINITE s /\ s SUBSET R ==>
   !p. monic p /\ p pdivides (PIFACTOR s) /\ ((roots p) INTER s = {}) ==> (p = |1|)``,
  rpt strip_tac >>
  `!x. x IN s ==> x IN R` by metis_tac[SUBSET_DEF] >>
  fs[EXTENSION, IN_INTER] >>
  `!x. x IN s ==> ~(root p x)` by metis_tac[poly_roots_member] >>
  qabbrev_tac `q = PIFACTOR s` >>
  `poly q` by rw[poly_prod_factors_poly, Abbr`q`] >>
  `?t. poly t /\ (q = t * p)` by rw[GSYM poly_divides_def] >>
  `s SUBSET (roots t)` by
  (rewrite_tac[poly_roots_member, SUBSET_DEF] >>
  rpt strip_tac >-
  rw[] >>
  `roots q = s` by rw[poly_prod_factors_roots, Abbr`q`] >>
  `root q x` by metis_tac[poly_roots_member] >>
  `eval q x = (eval t x) * (eval p x)` by rw[poly_eval_mult] >>
  `(eval q x = #0) /\ eval p x <> #0` by metis_tac[poly_root_def] >>
  `eval q x IN R /\ eval t x IN R /\ eval p x IN R` by rw[] >>
  `eval t x = #0` by metis_tac[field_mult_eq_zero] >>
  rw[poly_root_def]
  ) >>
  `q <> |0|` by metis_tac[poly_prod_factors_nonzero] >>
  `t <> |0|` by metis_tac[poly_mult_zero] >>
  `FINITE (roots t)` by rw[poly_roots_finite] >>
  `(roots t) SUBSET R` by rw[poly_roots_subset] >>
  `q pdivides PIFACTOR (roots t)` by rw[poly_prod_factors_divisibility, Abbr`q`] >>
  `PIFACTOR (roots t) pdivides t` by rw[poly_prod_factor_roots_divides] >>
  `poly (PIFACTOR (roots t))` by rw[poly_prod_factors_poly] >>
  `q pdivides t` by metis_tac[poly_divides_transitive, field_is_ring] >>
  `deg q <= deg t` by rw[poly_divides_deg_le] >>
  `p <> |0|` by rw[poly_monic_nonzero] >>
  `poly p` by rw[] >>
  `deg q = deg t + deg p` by rw[poly_deg_mult_nonzero] >>
  `deg p = 0` by decide_tac >>
  rw[GSYM poly_monic_deg_0]);

(* ------------------------------------------------------------------------- *)
(* Multiplicative Function for Polynomial Set                                *)
(* ------------------------------------------------------------------------- *)

(* Define a multiplicative function for poly_set *)
val poly_set_multiplicative_fun_def = Define`
   poly_set_multiplicative_fun (r:'a ring) f <=>
       (f {} = |1|) /\
       (!s. FINITE s /\ pset s ==> poly (f s)) /\
       (!s t. FINITE s /\ FINITE t /\ pset s /\ pset t ==> (f (s UNION t) * f (s INTER t) = f s * f t))
`;

(* Theorem: Ring r ==> poly_set_multiplicative_fun r PPROD *)
(* Proof:
   By poly_set_multiplicative_fun_def, this is to show:
   (1) PPROD {} = |1|,                                              by poly_prod_set_empty
   (2) FINITE s /\ pset s ==> poly (PPROD s)                        by poly_prod_set_poly
   (3) FINITE s /\ FINITE t /\ pset s /\ pset t ==>
       PPROD (s UNION t) * PPROD (s INTER t) = PPROD s * PPROD t    by poly_prod_set_mult_eqn
*)
val poly_prod_set_mult_fun = store_thm(
  "poly_prod_set_mult_fun",
  ``!r:'a ring. Ring r ==> poly_set_multiplicative_fun r PPROD``,
  rw[poly_set_multiplicative_fun_def, poly_prod_set_empty, poly_prod_set_poly, poly_prod_set_mult_eqn]);

(* Theorem: Ring r ==> !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P /\ EVERY_PSET P ==>
            !f. poly_set_multiplicative_fun r f /\ INJ f P univ(:'a poly) ==>
            (f (BIGUNION P) = PPROD (IMAGE f P)) *)
(* Proof:
   Apply finite induction on s.
   Base: f (BIGUNION {}) = PPIMAGE f {}
         f (BIGUNION {})
       = f {}                                   by BIGUNION_EMPTY
       = |1|                                    by poly_set_multiplicative_fun_def
       = PPROD {}                               by poly_prod_set_empty
       = PPROD (IMAGE f {})                     by IMAGE_EMPTY
   Step: e NOTIN P ==> f (BIGUNION (e INSERT P)) = PPIMAGE f (e INSERT P))
       Note FINITE e /\ EVERY_FINITE P          by IN_INSERT
        and pset e /\ !s. s IN P ==> pset s     by IN_INSERT
        and PAIR_DISJOINT P                     by IN_INSERT
        and !s. s IN P ==> DISJOINT e s         by IN_INSERT
       Also FINITE (BIGUNION P)                 by FINITE_BIGUNION
        and INJ f P univ(:'a poly) /\ f e IN univ(:'a poly)
            !y. y IN P /\ (f e = f y) ==> (e = y)  by INJ_INSERT
       thus f e NOTIN (IMAGE f P)               by IN_IMAGE, f e = f y ==> (e = y).
       Note f (e INTER (BIGUNION P)) = |1|      by DISJOINT_DEF, DISJOINT_BIGUNION, poly_set_multiplicative_fun_def
        and FINITE (IMAGE f P)                  by IMAGE_FINITE

        Now pset (BIGUNION P)                   by poly_set_bigunion_poly_set
       Then pset (e UNION (BIGUNION P))         by poly_set_union_poly_set
       Also FINITE (e UNION (BIGUNION P))       by FINITE_UNION
       Then poly (f e)                          by poly_set_multiplicative_fun_def
        and poly (f (e UNION (BIGUNION P)))     by poly_set_multiplicative_fun_def
       Also pset (IMAGE f P)                    by IN_IMAGE, INJ_DEF, IN_UNIV, poly_set_multiplicative_fun_def

         f (BIGUNION (e INSERT P))
       = f (e UNION BIGUNION P)                 by BIGUNION_INSERT
       = f (e UNION BIGUNION P) * |1|           by poly_mult_rone
       = f (e UNION BIGUNION P) * f (e INTER (BIGUNION P))    by above
       = f e * f (BIGUNION P)                   by poly_set_multiplicative_fun_def
       = f e * PPROD (IMAGE f P)                by induction hypothesis
       = PPROD (f e INSERT IMAGE f P)           by poly_prod_set_insert, f e NOTIN (IMAGE f P)
       = PPIMAGE f (e INSERT P)                 by IMAGE_INSERT
*)
val poly_disjoint_bigunion_mult_fun = store_thm(
  "poly_disjoint_bigunion_mult_fun",
  ``!r:'a ring. Ring r ==> !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P /\ EVERY_PSET P ==>
   !f. poly_set_multiplicative_fun r f /\ INJ f P univ(:'a poly) ==>
   (f (BIGUNION P) = PPROD (IMAGE f P))``,
  ntac 2 strip_tac >>
  `!P. FINITE P ==> EVERY_FINITE P /\ PAIR_DISJOINT P /\ EVERY_PSET P ==>
   !f. poly_set_multiplicative_fun r f /\ INJ f P univ(:'a poly) ==>
    (f (BIGUNION P) = PPROD (IMAGE f P))` suffices_by metis_tac[] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rpt strip_tac >-
  metis_tac[BIGUNION_EMPTY, poly_prod_set_empty, IMAGE_EMPTY, poly_set_multiplicative_fun_def] >>
  rw_tac std_ss[BIGUNION_INSERT, IMAGE_INSERT] >>
  `FINITE e /\ EVERY_FINITE P` by rw[] >>
  `pset e /\ EVERY_PSET P` by metis_tac[IN_INSERT] >>
  `(!s. s IN P ==> DISJOINT e s) /\ PAIR_DISJOINT P` by metis_tac[IN_INSERT] >>
  `FINITE (BIGUNION P)` by rw[FINITE_BIGUNION] >>
  `INJ f P univ(:'a poly) /\ f e NOTIN (IMAGE f P)` by metis_tac[INJ_INSERT, IN_IMAGE] >>
  `f (e INTER (BIGUNION P)) = |1|` by metis_tac[DISJOINT_DEF, DISJOINT_BIGUNION, poly_set_multiplicative_fun_def] >>
  `FINITE (IMAGE f P)` by rw[] >>
  `pset (BIGUNION P)` by metis_tac[poly_set_bigunion_poly_set] >>
  `pset (e UNION (BIGUNION P))` by prove_tac[poly_set_union_poly_set] >>
  `FINITE (e UNION (BIGUNION P))` by rw[] >>
  `poly (f e) /\ poly (f (e UNION (BIGUNION P)))` by prove_tac[poly_set_multiplicative_fun_def] >>
  `pset (IMAGE f P)` by prove_tac[IN_IMAGE, INJ_DEF, IN_UNIV, poly_set_multiplicative_fun_def] >>
  `f (e UNION BIGUNION P) = f (e UNION BIGUNION P) * |1|` by rw_tac std_ss[GSYM poly_mult_rone] >>
  `_ = f e * f (BIGUNION P)` by metis_tac[poly_set_multiplicative_fun_def] >>
  `_ = f e * PPROD (IMAGE f P)` by metis_tac[] >>
  `_ = PPROD (f e INSERT IMAGE f P)` by prove_tac[poly_prod_set_insert] >>
  metis_tac[]);

(* Apply poly_disjoint_bigunion_mult_fun:
|- !r. Ring r ==> !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P /\ EVERY_PSET P ==>
   !f. poly_set_multiplicative_fun r f /\ INJ f P univ(:'a poly) ==> (f (BIGUNION P) = PPIMAGE f P)
*)

(* Theorem: Ring r ==> !RR s. FINITE s /\ pset s /\ RR equiv_on s ==>
            !f. poly_set_multiplicative_fun r f /\ INJ f (partition RR s) univ(:'a poly) ==>
               (f s = PPIMAGE f (partition RR s)) *)
(* Proof:
     Let P = partition RR s, the goal is: f s = PPIMAGE f P.
    Note FINITE s
     ==> FINITE P /\ EVERY_FINITE P        by FINITE_partition
     and RR equiv_on s
     ==> BIGUNION P = s                    by BIGUNION_partition
     ==> PAIR_DISJOINT P                   by partition_elements_disjoint
    Also EVERY_PSET P                      by partition_elements, equiv_class_element
   Hence f (BIGUNION P) = PPIMAGE f P      by poly_disjoint_bigunion_mult_fun
      or f s = PPIMAGE f P                 by above, BIGUNION_partition
*)
val poly_prod_set_mult_fun_by_partition = store_thm(
  "poly_prod_set_mult_fun_by_partition",
  ``!r:'a ring. Ring r ==> !RR s. FINITE s /\ pset s /\ RR equiv_on s ==>
   !f. poly_set_multiplicative_fun r f /\ INJ f (partition RR s) univ(:'a poly) ==>
     (f s = PPIMAGE f (partition RR s))``,
  rpt strip_tac >>
  qabbrev_tac `P = partition RR s` >>
  `FINITE P /\ EVERY_FINITE P` by metis_tac[FINITE_partition] >>
  `BIGUNION P = s` by rw[BIGUNION_partition, Abbr`P`] >>
  `PAIR_DISJOINT P` by metis_tac[partition_elements_disjoint] >>
  (`EVERY_PSET P` by (rw[partition_elements, Abbr`P`] >> metis_tac[equiv_class_element])) >>
  metis_tac[poly_disjoint_bigunion_mult_fun]);


(* ------------------------------------------------------------------------- *)
(* Multiplicative Function for Ring Set                                      *)
(* ------------------------------------------------------------------------- *)

(* Define a multiplicative polynomial function for set of ring elements *)
val ring_set_multiplicative_fun_def = Define`
   ring_set_multiplicative_fun (r:'a ring) f <=>
       (f {} = |1|) /\
       (!s. FINITE s /\ s SUBSET R ==> poly (f s)) /\
       (!s t. FINITE s /\ FINITE t /\ s SUBSET R /\ t SUBSET R ==> (f (s UNION t) * f (s INTER t) = f s * f t))
`;

(* Theorem: s SUBSET R /\ t SUBSET R <=> (s UNION t) SUBSET R *)
(* Proof: by IN_UNION, SUBSET_DEF *)
val ring_set_union_ring_set = store_thm(
  "ring_set_union_ring_set",
  ``!r:'a ring. !s t. s SUBSET R /\ t SUBSET R <=> (s UNION t) SUBSET R``,
  rw[]);

(* Theorem: (!t. t IN s ==> t SUBSET R) <=> (BIGUNION s) SUBSET R *)
(* Proof: by IN_BIGUNION, ring_set_union_ring_set, SUBSET_DEF *)
val ring_set_bigunion_ring_set = store_thm(
  "ring_set_bigunion_ring_set",
  ``!r:'a ring. !s. (!t. t IN s ==> t SUBSET R) <=> (BIGUNION s) SUBSET R``,
  prove_tac[IN_BIGUNION, ring_set_union_ring_set, SUBSET_DEF]);

(* Theorem: Ring r ==> !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P /\ (!s. s IN P ==> s SUBSET R) ==>
            !f. ring_set_multiplicative_fun r f /\ INJ f P univ(:'a poly) ==>
            (f (BIGUNION P) = PPROD (IMAGE f P)) *)
(* Proof:
   Apply finite induction on s.
   Base: f (BIGUNION {}) = PPIMAGE f {}
         f (BIGUNION {})
       = f {}                                   by BIGUNION_EMPTY
       = |1|                                    by ring_set_multiplicative_fun_def
       = PPROD {}                               by poly_prod_set_empty
       = PPROD (IMAGE f {})                     by IMAGE_EMPTY
   Step: e NOTIN P ==> f (BIGUNION (e INSERT P)) = PPIMAGE f (e INSERT P))
       Note FINITE e /\ EVERY_FINITE P          by IN_INSERT
        and e SUBSET R /\ (!s. s IN P ==> s SUBSET R)     by IN_INSERT
        and PAIR_DISJOINT P                     by IN_INSERT
        and !s. s IN P ==> DISJOINT e s         by IN_INSERT
       Also FINITE (BIGUNION P)                 by FINITE_BIGUNION
        and INJ f P univ(:'a poly) /\ f e IN univ(:'a poly)
            !y. y IN P /\ (f e = f y) ==> (e = y)  by INJ_INSERT
       thus f e NOTIN (IMAGE f P)               by IN_IMAGE, f e = f y ==> (e = y).
       Note f (e INTER (BIGUNION P)) = |1|      by DISJOINT_DEF, DISJOINT_BIGUNION, ring_set_multiplicative_fun_def
        and FINITE (IMAGE f P)                  by IMAGE_FINITE

        Now (BIGUNION P) SUBSET R               by ring_set_bigunion_ring_set
       Then (e UNION (BIGUNION P)) SUBSET R     by ring_set_union_ring_set
       Also FINITE (e UNION (BIGUNION P))       by FINITE_UNION
       Then poly (f e)                          by ring_set_multiplicative_fun_def
        and poly (f (e UNION (BIGUNION P)))     by ring_set_multiplicative_fun_def
       Also pset (IMAGE f P)                    by IN_IMAGE, INJ_DEF, IN_UNIV, ring_set_multiplicative_fun_def

         f (BIGUNION (e INSERT P))
       = f (e UNION BIGUNION P)                 by BIGUNION_INSERT
       = f (e UNION BIGUNION P) * |1|           by poly_mult_rone
       = f (e UNION BIGUNION P) * f (e INTER (BIGUNION P))    by above
       = f e * f (BIGUNION P)                   by ring_set_multiplicative_fun_def
       = f e * PPROD (IMAGE f P)                by induction hypothesis
       = PPROD (f e INSERT IMAGE f P)           by poly_prod_set_insert, f e NOTIN (IMAGE f P)
       = PPIMAGE f (e INSERT P)                 by IMAGE_INSERT
*)
val ring_disjoint_bigunion_mult_fun = store_thm(
  "ring_disjoint_bigunion_mult_fun",
  ``!r:'a ring. Ring r ==> !P. FINITE P /\ EVERY_FINITE P /\ PAIR_DISJOINT P /\ (!s. s IN P ==> s SUBSET R) ==>
   !f. ring_set_multiplicative_fun r f /\ INJ f P univ(:'a poly) ==>
   (f (BIGUNION P) = PPROD (IMAGE f P))``,
  ntac 2 strip_tac >>
  `!P. FINITE P ==> EVERY_FINITE P /\ PAIR_DISJOINT P /\ (!s. s IN P ==> s SUBSET R) ==>
   !f. ring_set_multiplicative_fun r f /\ INJ f P univ(:'a poly) ==>
   (f (BIGUNION P) = PPROD (IMAGE f P))` suffices_by rw[] >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  metis_tac[BIGUNION_EMPTY, poly_prod_set_empty, IMAGE_EMPTY, ring_set_multiplicative_fun_def] >>
  rw_tac std_ss[BIGUNION_INSERT, IMAGE_INSERT] >>
  `FINITE e /\ EVERY_FINITE P` by rw[] >>
  `e SUBSET R /\ (!s. s IN P ==> s SUBSET R)` by metis_tac[IN_INSERT] >>
  `(!s. s IN P ==> DISJOINT e s) /\ PAIR_DISJOINT P` by metis_tac[IN_INSERT] >>
  `FINITE (BIGUNION P)` by rw[FINITE_BIGUNION] >>
  `INJ f P univ(:'a poly) /\ f e NOTIN (IMAGE f P)` by prove_tac[INJ_INSERT, IN_IMAGE] >>
  `f (e INTER (BIGUNION P)) = |1|` by metis_tac[DISJOINT_DEF, DISJOINT_BIGUNION, ring_set_multiplicative_fun_def] >>
  `FINITE (IMAGE f P)` by rw[] >>
  `(BIGUNION P) SUBSET R` by metis_tac[ring_set_bigunion_ring_set] >>
  `(e UNION (BIGUNION P)) SUBSET R` by metis_tac[ring_set_union_ring_set] >>
  `FINITE (e UNION (BIGUNION P))` by rw[] >>
  `poly (f e) /\ poly (f (e UNION (BIGUNION P)))` by metis_tac[ring_set_multiplicative_fun_def] >>
  `pset (IMAGE f P)` by prove_tac[IN_IMAGE, INJ_DEF, IN_UNIV, ring_set_multiplicative_fun_def] >>
  `f (e UNION BIGUNION P) = f (e UNION BIGUNION P) * |1|` by rw_tac std_ss[GSYM poly_mult_rone] >>
  `_ = f e * f (BIGUNION P)` by metis_tac[ring_set_multiplicative_fun_def] >>
  `_ = f e * PPROD (IMAGE f P)` by metis_tac[] >>
  `_ = PPROD (f e INSERT IMAGE f P)` by prove_tac[poly_prod_set_insert] >>
  metis_tac[]);

(* Theorem: Ring r ==> !RR s. FINITE s /\ s SUBSET R /\ RR equiv_on s ==>
            !f. field_set_multiplicative_fun r f /\ INJ f (partition RR s) univ(:'a poly) ==>
                (f s = PPIMAGE f (partition RR s)) *)
(* Proof:
     Let P = partition RR s, the goal is: f s = PPIMAGE f P.
    Note FINITE s
     ==> FINITE P /\ EVERY_FINITE P        by FINITE_partition
     and RR equiv_on s
     ==> BIGUNION P = s                    by BIGUNION_partition
     ==> PAIR_DISJOINT P                   by partition_elements_disjoint
    Also !s. s IN P ==> s SUBSET R         by partition_elements, equiv_class_element, SUBSET_DEF
   Hence f (BIGUNION P) = PPIMAGE f P      by ring_disjoint_bigunion_mult_fun
      or f s = PPIMAGE f P                 by above, BIGUNION_partition
*)
val ring_prod_set_mult_fun_by_partition = store_thm(
  "ring_prod_set_mult_fun_by_partition",
  ``!r:'a ring. Ring r ==> !RR s. FINITE s /\ s SUBSET R /\ RR equiv_on s ==>
   !f. ring_set_multiplicative_fun r f /\ INJ f (partition RR s) univ(:'a poly) ==>
     (f s = PPIMAGE f (partition RR s))``,
  rpt strip_tac >>
  qabbrev_tac `P = partition RR s` >>
  `FINITE P /\ EVERY_FINITE P` by metis_tac[FINITE_partition] >>
  `BIGUNION P = s` by rw[BIGUNION_partition, Abbr`P`] >>
  `PAIR_DISJOINT P` by metis_tac[partition_elements_disjoint] >>
  (`!s. s IN P ==> s SUBSET R` by (rw[partition_elements, Abbr`P`] >> metis_tac[equiv_class_element, SUBSET_DEF])) >>
  rw[ring_disjoint_bigunion_mult_fun]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
