(* ------------------------------------------------------------------------- *)
(* Finite Field: Instances                                                   *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ffInstances";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory arithmeticTheory listTheory numberTheory dividesTheory
     gcdTheory;

(* Get dependent theories local *)
(* val _ = load "ffBasicTheory"; *)
open ffBasicTheory;

open monoidTheory groupTheory ringTheory fieldTheory;
open groupOrderTheory;
open groupInstancesTheory ringInstancesTheory fieldInstancesTheory;

open polynomialTheory polyWeakTheory polyRingTheory;

open polyFieldTheory polyDivisionTheory polyFieldDivisionTheory;
open polyModuloRingTheory polyFieldModuloTheory;

(* (* val _ = load "polyIrreducibleTheory"; *) *)
open polyMonicTheory;
open polyRootTheory;
open polyIrreducibleTheory;

(* (* val _ = load "ringDividesTheory"; *) *)
open ringDividesTheory;
open ringIdealTheory;
open ringUnitTheory;
open subgroupTheory;
open quotientGroupTheory;

(* ------------------------------------------------------------------------- *)
(* Finite Field Instances Documentation                                      *)
(* ------------------------------------------------------------------------- *)
(* Overload:
   h            [1; 1; 1]  the irreducible polynomial: h = x^2 + x + 1
   GF_4         PolyModRing (GF 2) h
   H            poly_lift (GF 2) h
*)
(* Definitions and Theorems (# are exported):

   GF(2) -- Finite Field with 2 elements:
   GF_2_finite_field   |- FiniteField (GF 2)
   GF_2_field          |- Field (GF 2)
#  GF_2_carrier        |- (GF 2).carrier = {0; 1}
#  GF_2_zero           |- (GF 2).sum.id = 0
#  GF_2_one            |- (GF 2).prod.id = 1

   Irreducible Polynomial h in GF(2)[x]:
   GF_2_poly_ring      |- Ring (PolyRing (GF 2))
   GF_2_poly_h         |- Poly (GF 2) h
   GF_2_monic_h        |- poly_monic (GF 2) h
   GF_2_deg_h          |- poly_deg (GF 2) h = 2
   GF_2_roots_h        |- poly_roots (GF 2) h = {}
   GF_2_irreducible_h  |- irreducible (PolyRing (GF 2)) h

   Quotient Field by Irreducible Polynomial h:
   GF_2_quotient_field_by_h |- Field (PolyRing (GF 2) / principal_ideal (PolyRing (GF 2)) h)

   Polynomial Ring modulo Irreducible Polynomial h:
   GF_2_quotient_field_iso  |- FieldIso
                    (\x. coset (PolyRing (GF 2)).sum x (principal_ideal (PolyRing (GF 2)) h).carrier)
                                  GF_4
                                  (PolyRing (GF 2) / principal_ideal (PolyRing (GF 2)) h)
   GF_2_h_property          |- Poly (GF 2) h /\ Unit (GF 2) (Lead (GF 2) h) /\ 0 < Deg (GF 2) h

   GF(4) -- Finite Field with 4 elements:
   GF_4_ring            |- Ring GF_4
#  GF_4_sum_id          |- GF_4.sum.id = []
#  GF_4_prod_id         |- GF_4.prod.id = [1]
   GF_4_carrier         |- GF_4.carrier = {[]; [1]; [0; 1]; [1; 1]}
   GF_4_mult_1_1        |- GF_4.prod.op [1] [1] = [1]
   GF_4_mult_a_b        |- GF_4.prod.op [0; 1] [1; 1] = [1]
   GF_4_mult_b_a        |- GF_4.prod.op [1; 1] [0; 1] = [1]
   GF_4_prod_group      |- Group (GF_4.prod excluding [])
#  GF_4_field           |- Field GF_4

   Lifting h from GF(2)[x] to GF(4)[y]:
   GF_4_H_by_lift       |- H = [[1]; [1]; [1]]
   GF_4_elements        |- !x. x IN GF_4.carrier <=> (x = []) \/ (x = [1]) \/ (x = [0; 1]) \/ (x = [1; 1])
   GF_4_H_poly          |- Poly GF_4 H
   GF_4_H_ring_element  |- H IN (PolyRing GF_4).carrier
   GF_4_sum_1_1         |- GF_4.sum.op [1] [1] = []
   GF_4_sum_1_a         |- GF_4.sum.op [1] [0; 1] = [1; 1]
   GF_4_sum_1_b         |- GF_4.sum.op [1] [1; 1] = [0; 1]
   GF_4_sum_a_b         |- GF_4.sum.op [0; 1] [1; 1] = [1]
   GF_4_H_eval_at_0     |- poly_eval GF_4 H [] = [1]
   GF_4_H_eval_at_1     |- poly_eval GF_4 H [1] = [1]
   GF_4_H_eval_at_a     |- poly_eval GF_4 H [0; 1] = []
   GF_4_H_eval_at_b     |- poly_eval GF_4 H [1; 1] = []
   GF_4_H_root_a        |- poly_root GF_4 H [0; 1]
   GF_4_H_root_b        |- poly_root GF_4 H [1; 1]
   GF_4_H_roots         |- poly_roots GF_4 H = {[0; 1]; [1; 1]}
   GF_4_H_roots_card    |- CARD (poly_roots GF_4 H) = 2
   GF_4_H_deg           |- poly_deg GF_4 H = 2
   GF_4_sum_x_x         |- !x. x IN GF_4.carrier ==> (GF_4.sum.op x x = GF_4.sum.id)
   GF_4_neg             |- !x. x IN GF_4.carrier ==> (GF_4.sum.inv x = x)
   GF_4_poly_one        |- (PolyRing GF_4).prod.id = poly_lift (GF 2) GF_4.prod.id
   GF_4_add_x_0         |- !x. x IN GF_4.carrier ==> (GF_4.sum.op x [] = x)
   GF_4_add_0_x         |- !x. x IN GF_4.carrier ==> (GF_4.sum.op [] x = x)
   GF_4_add_1_0         |- GF_4.sum.op [1] [] = [1]
   GF_4_mult_x_1        |- !x. x IN GF_4.carrier ==> (GF_4.prod.op x [1] = x)
   GF_4_mult_1_x        |- !x. x IN GF_4.carrier ==> (GF_4.prod.op [1] x = x)
   GF_4_mult_a_1        |- GF_4.prod.op [0; 1] [1] = [0; 1]
   GF_4_mult_1_b        |- GF_4.prod.op [1] [1; 1] = [1; 1]
   GF_4_H_factors       |- H = (PolyRing GF_4).prod.op (poly_factor GF_4 [0; 1])
                                                       (poly_factor GF_4 [1; 1])
*)

(* ------------------------------------------------------------------------- *)
(* GF(2) -- Finite Field with 2 elements.                                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField (GF 2) *)
(* Proof:
   Since  prime 2     by PRIME_2
   Hence true by GF_finite_field.
*)
val GF_2_finite_field = store_thm(
  "GF_2_finite_field",
  ``FiniteField (GF 2)``,
  rw[PRIME_2, GF_finite_field]);

(* Theorem: Field (GF 2) *)
(* Proof: by GF_2_finite_field. *)
val GF_2_field = store_thm(
  "GF_2_field",
  ``Field (GF 2)``,
  metis_tac[GF_2_finite_field, FiniteField_def]);

(* Theorem: (GF 2).carrier = {0; 1} *)
(* Proof: by GF_def *)
val GF_2_carrier = store_thm(
  "GF_2_carrier",
  ``(GF 2).carrier = {0; 1}``,
  rw[GF_def, EXTENSION]);

(* Theorem: (GF 2).sum.id = 0 *)
(* Proof: by GF_def *)
val GF_2_zero = store_thm(
  "GF_2_zero",
  ``(GF 2).sum.id = 0``,
  rw[GF_def]);

(* Theorem: (GF 2).prod.id = 1 *)
(* Proof: by GF_def *)
val GF_2_one = store_thm(
  "GF_2_one",
  ``(GF 2).prod.id = 1``,
  rw[GF_def, including_def]);

(* export simple results *)
val _ = export_rewrites ["GF_2_carrier", "GF_2_zero", "GF_2_one"];

(* ------------------------------------------------------------------------- *)
(* Irreducible Polynomial h in GF(2)[x].                                     *)
(* ------------------------------------------------------------------------- *)

(* The irreducible polynomial: h = x^2 + x + 1 *)
val _ = temp_overload_on ("h", ``[1; 1; 1]``);

(* Theorem: Ring (PolyRing (GF 2)) *)
(* Proof:
   Since Field (GF 2)      by GF_2_field,
   hence Ring (GF 2)       by field_is_ring,
   thus true by poly_add_mult_ring.
*)
val GF_2_poly_ring = store_thm(
  "GF_2_poly_ring",
  ``Ring (PolyRing (GF 2))``,
  rw[GF_2_field, poly_add_mult_ring]);

(* Theorem: Poly (GF 2) h *)
(* Proof:
   By Poly_def, zero_poly_def, this is to show:
   (1) 1 IN (GF 2).carrier, true by GF_2_carrier.
   (2) 1 <> (GF 2).sum.id, true by GF_2_zero.
*)
val GF_2_poly_h = store_thm(
  "GF_2_poly_h",
  ``Poly (GF 2) h``,
  rw[Poly_def]);

(* Theorem: poly_monic (GF 2) h *)
(* Proof:
   By poly_monic_def, this is to show:
   (1) Poly (GF 2) h
       True by GF_2_poly_h
   (2) poly_lead (GF 2) h = (GF 2).prod.id
         poly_lead (GF 2) h
       = poly_lead (GF 2) [1; 1; 1]     by h
       = 1                              by poly_lead_def
       = (GF 2).prod.id                 by GF_2_one
 *)
val GF_2_monic_h = store_thm(
  "GF_2_monic_h",
  ``poly_monic (GF 2) h``,
  rw[poly_monic_def]);

(* Theorem: poly_deg (GF 2) h = 2 *)
(* Proof:
   By poly_deg_def, this is to show: PRE (LENGTH h) = 2
   But LENGTH h = 3        by LENGTH
   and PRE 3 = 2           by PRE
*)
val GF_2_deg_h = store_thm(
  "GF_2_deg_h",
  ``poly_deg (GF 2) h = 2``,
  rw[poly_deg_def]);

(* Theorem: poly_roots (GF 2) h = {} *)
(* Proof:
   Simplify by definitions, this is to show:
   x <> 0 /\ x <> 1 \/ (1 + ((1 + x MOD 2) MOD 2 * x) MOD 2) MOD 2 <> 0
   If x = 0,
      (1 + ((1 + x MOD 2) MOD 2 * x) MOD 2) MOD 2
    = (1 + ((1 + 0 MOD 2) MOD 2 * 0) MOD 2) MOD 2
    = (1 + 0 MOD 2) MOD 2                           by MULT_0
    = (1 + 0) MOD 2                                 by ZERO_MOD
    = 1 MOD 2                                       by ADD_0
    = 1 <> 0                                        by ONE_MOD
   If x <> 0, x = 1,
      (1 + ((1 + x MOD 2) MOD 2 * x) MOD 2) MOD 2
    = (1 + ((1 + 1 MOD 2) MOD 2 * 1) MOD 2) MOD 2
    = (1 + ((1 + 1 MOD 2) MOD 2) MOD 2) MOD 2       by MULT_RIGHT_1
    = (1 + ((1 + 1) MOD 2) MOD 2) MOD 2             by ONE_MOD
    = (1 + (2 MOD 2) MOD 2) MOD 2
    = (1 + 0 MOD 2) MOD 2                           by DIVMOD_ID
    = (1 + 0) MOD 2                                 by ZERO_MOD
    = 1 MOD 2                                       by ADD_0
    = 1 <> 0                                        by ONE_MOD
*)
Theorem GF_2_roots_h:
  poly_roots (GF 2) h = {}
Proof
  rw[GF_def, add_mod_def, mult_mod_def, including_def,
     poly_roots_def, poly_root_def, EXTENSION, GSPECIFICATION] >>
  strip_tac >> fs[]
QED

(*
- poly_deg_2_irreducible |> ISPEC ``(GF 2)``;
> val it = |- Field (GF 2) ==>
       !p. poly_monic (GF 2) p /\ (poly_deg (GF 2) p = 2) /\ (poly_roots (GF 2) p = {}) ==> irreducible (PolyRing (GF 2)) p : thm
*)

(* Theorem: irreducible (PolyRing (GF 2)) h *)
(* Proof:
   Field (GF 2)                           by GF_2_field
   poly_monic (GF 2) h                    by GF_2_monic_h
   poly_deg (GF 2) h = 2                  by GF_2_deg_h
   poly_roots (GF 2) h = {}               by GF_2_roots_h
   hence irreducible (PolyRing (GF 2)) p  by poly_deg_2_irreducible
*)
val GF_2_irreducible_h = store_thm(
  "GF_2_irreducible_h",
  ``irreducible (PolyRing (GF 2)) h``,
  rpt strip_tac >>
  `Field (GF 2)` by rw[GF_2_field] >>
  `poly_monic (GF 2) h` by rw[GF_2_monic_h] >>
  `poly_deg (GF 2) h = 2` by rw[GF_2_deg_h] >>
  `poly_roots (GF 2) h = {}` by rw[GF_2_roots_h] >>
  rw[poly_deg_2_irreducible]);

(* ------------------------------------------------------------------------- *)
(* Quotient Field by Irreducible Polynomial h.                               *)
(* ------------------------------------------------------------------------- *)

(*
- poly_irreducible_quotient_field |> ISPEC ``(GF 2)``;
> val it = |- Field (GF 2) ==> !p. irreducible (PolyRing (GF 2)) p ==>
              Field (PolyRing (GF 2) / principal_ideal (PolyRing (GF 2)) p) : thm
*)

(* Theorem: Field (PolyRing (GF 2) / principal_ideal (PolyRing (GF 2)) h) *)
(* Proof:
   Field (GF 2)                     by GF_2_field
   irreducible (PolyRing (GF 2)) h  by GF_2_irreducible_h
   thus true                        by poly_irreducible_quotient_field
*)
val GF_2_quotient_field_by_h = store_thm(
  "GF_2_quotient_field_by_h",
  ``Field (PolyRing (GF 2) / principal_ideal (PolyRing (GF 2)) h)``,
  rpt strip_tac >>
  `Field (GF 2)` by rw[GF_2_field] >>
  `irreducible (PolyRing (GF 2)) h` by rw[GF_2_irreducible_h] >>
  rw[poly_irreducible_quotient_field]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Ring modulo Irreducible Polynomial h.                          *)
(* ------------------------------------------------------------------------- *)

(* GF(4), with 4 elements *)
val _ = overload_on ("GF_4", ``PolyModRing (GF 2) h``);

(*
- poly_mod_ring_iso_quotient_ring |> ISPEC ``(GF 2)``;
> val it = |- Ring (GF 2) ==> !z. Poly (GF 2) z /\ 0 < poly_deg (GF 2) z /\
              poly_lead (GF 2) z IN (Invertibles (GF 2).prod).carrier ==>
         RingIso (\x. coset (PolyRing (GF 2)).sum x (principal_ideal (PolyRing (GF 2)) z).carrier)
                 (PolyModRing (GF 2) z)
                 (PolyRing (GF 2) / principal_ideal (PolyRing (GF 2)) z) : thm
- poly_quotient_field_iso_poly_mod |> ISPEC ``(GF 2)``;
> val it = |- Field (GF 2) ==> !z. poly_monic (GF 2) z /\ irreducible (PolyRing (GF 2)) z ==>
         FieldIso (\x. coset (PolyRing (GF 2)).sum x (principal_ideal (PolyRing (GF 2)) z).carrier)
                  (PolyModRing (GF 2) z)
                  (PolyRing (GF 2) / principal_ideal (PolyRing (GF 2)) z) : thm
- poly_monic_irreducible_property |> ISPEC ``(GF 2)``;
> val it = |- Field (GF 2) ==>
     !p. poly_monic (GF 2) p /\ irreducible (PolyRing (GF 2)) p ==>
         Poly (GF 2) p /\ 0 < poly_deg (GF 2) p /\
         poly_lead (GF 2) p IN (Invertibles (GF 2).prod).carrier : thm
*)

(* Theorem: FieldIso (\x. coset (PolyRing (GF 2)).sum x (principal_ideal (PolyRing (GF 2)) h).carrier)
                  (GF_4)
                  (PolyRing (GF 2) / principal_ideal (PolyRing (GF 2)) h) *)
(* Proof:
   Field (GF 2)                     by GF_2_field
   poly_monic (GF 2) h              by GF_2_monic_h
   irreducible (PolyRing (GF 2)) h  by GF_2_irreducible_h
   Hence true                       by poly_quotient_field_iso_poly_mod
*)
val GF_2_quotient_field_iso = store_thm(
  "GF_2_quotient_field_iso",
  ``FieldIso (\x. coset (PolyRing (GF 2)).sum x (principal_ideal (PolyRing (GF 2)) h).carrier)
            (GF_4)
            (PolyRing (GF 2) / principal_ideal (PolyRing (GF 2)) h)``,
  rpt strip_tac >>
  `Field (GF 2)` by rw[GF_2_field] >>
  `poly_monic (GF 2) h` by rw[GF_2_monic_h] >>
  `irreducible (PolyRing (GF 2)) h` by rw[GF_2_irreducible_h] >>
  rw[poly_quotient_field_iso_poly_mod]);

(* Theorem: Poly (GF 2) h /\ Unit (GF 2) (Lead (GF 2) h) /\ 0 < Deg (GF 2) h *)
(* Proof:
   Field (GF 2)                      by GF_2_field
   poly_monic (GF 2) p               by GF_2_monic_h
   irreducible (PolyRing (GF 2)) p   by GF_2_irreducible_h
   Hence true                        by poly_monic_irreducible_property
*)
val GF_2_h_property = store_thm(
  "GF_2_h_property",
  ``Poly (GF 2) h /\ Unit (GF 2) (Lead (GF 2) h) /\ 0 < Deg (GF 2) h``,
  rw_tac std_ss[GF_2_field, GF_2_monic_h, GF_2_irreducible_h, poly_monic_irreducible_property]);

(* ------------------------------------------------------------------------- *)
(* GF(4) -- Finite Field with 4 elements.                                    *)
(* ------------------------------------------------------------------------- *)

(*
- poly_mod_ring_ring |> ISPEC ``(GF 2)``;
> val it =  |- Ring (GF 2) ==> !z. Ulead (GF 2) z ==> Ring (PolyModRing (GF 2) z) : thm
*)

(* Theorem: Ring (GF_4) *)
(* Proof:
   Ring (GF 2)                                    by GF_2_field, field_is_ring
   Poly (GF 2) h /\ Unit (GF 2) (Lead (GF 2) h)   by GF_2_h_property
   Hence true                                     by poly_mod_ring_ring
*)
val GF_4_ring = store_thm(
  "GF_4_ring",
  ``Ring (GF_4)``,
  rw[GF_2_field, GF_2_h_property, poly_mod_ring_ring]);

(* Theorem: (GF_4).sum.id = [] *)
(* Proof:
     (GF_4).sum.id
   = (PolyRing (GF 2)).sum.id          by poly_mod_ring_def
   = []                                by poly_ring_def
*)
val GF_4_sum_id = store_thm(
  "GF_4_sum_id",
  ``(GF_4).sum.id = []``,
  rw[poly_mod_ring_def]);

(* Theorem: (GF_4).prod.id = [1] *)
(* Proof:
     (GF_4).prod.id
   = (PolyRing (GF 2)).prod.id          by poly_mod_ring_def
   = [1]                                by poly_ring_def
*)
val GF_4_prod_id = store_thm(
  "GF_4_prod_id",
  ``(GF_4).prod.id = [1]``,
  rw[poly_mod_ring_def, poly_ring_def]);


(* Theorem: (GF_4).carrier = {[], [1], [0;1], [1;1]} *)
(* Proof: Expand by poly_mod_ring_def, poly_remainders_def, and check each case. *)
val GF_4_carrier = store_thm(
  "GF_4_carrier",
  ``(GF_4).carrier = {[]; [1]; [0;1]; [1;1]}``,
  rw_tac std_ss[poly_mod_ring_def, poly_remainders_def, EXTENSION] >>
  rw[poly_deg_def, EQ_IMP_THM] >| [
    `?a t. x = a::t` by metis_tac[list_CASES] >>
    `a IN (GF 2).carrier /\ Poly (GF 2) t` by metis_tac[poly_cons_poly] >>
    Cases_on `t = []` >| [
      rw[] >>
      full_simp_tac std_ss[GF_2_carrier] >>
      `!x. x IN {0; 1} ==> (x = 0) \/ (x = 1)` by rw[] >>
      `poly_lead (GF 2) [a] = a` by rw[poly_lead_const] >>
      `[a] <> (PolyRing (GF 2)).sum.id` by rw[] >>
      `a <> 0` by metis_tac[poly_lead_nonzero, GF_2_zero] >>
      metis_tac[],
      `?b v. t = b::v` by metis_tac[list_CASES] >>
      `LENGTH t < 2` by metis_tac[LENGTH, prim_recTheory.PRE] >>
      `LENGTH t <> 0` by metis_tac[LENGTH_NIL] >>
      `LENGTH t = 1` by decide_tac >>
      `SUC (LENGTH v) = 1` by metis_tac[LENGTH] >>
      `LENGTH v = 0` by decide_tac >>
      `v = []` by metis_tac[LENGTH_NIL] >>
      `b IN (GF 2).carrier` by metis_tac[poly_cons_poly] >>
      `!z. z IN (GF 2).carrier <=> (z = 0) \/ (z = 1)` by rw[GF_2_carrier] >>
      `poly_lead (GF 2) x = b` by rw[poly_lead_def] >>
      `x <> (PolyRing (GF 2)).sum.id` by rw[] >>
      `poly_lead (GF 2) x <> 0` by metis_tac[poly_lead_nonzero, GF_2_zero] >>
      `b = 1` by metis_tac[] >>
      full_simp_tac std_ss[]
    ],
    rw[],
    rw[],
    rw[],
    rw[],
    rw[],
    rw[]
  ]);

(* TODO: poly_lead_nonzero nees GEN_ALL:
- poly_lead_nonzero;
> val it = |- !p. poly p /\ p <> |0| ==> lead p <> #0 : thm
- poly_lead_nonzero |> GEN_ALL;
> val it = |- !r p. poly p /\ p <> |0| ==> lead p <> #0 : thm
*)

(* Theorem: (GF_4).prod.op [1] [1] = [1] *)
(* Proof:
   Field (GF 2)                    by GF_2_field
   Poly (GF 2) h /\  0 < poly_deg (GF 2) h /\
      poly_lead (GF 2) h IN (Invertibles (GF 2).prod).carrier
                                   by GF_2_h_property
   Also Poly (GF 2) [1]            by poly_field_one_poly
    and poly_deg (GF 2) [1] = 0    by poly_deg_one
   Hence true                      by poly_mod_less.
*)
val GF_4_mult_1_1 = store_thm(
  "GF_4_mult_1_1",
  ``(GF_4).prod.op [1] [1] = [1]``,
  rw[poly_mod_ring_def, poly_ring_def, GF_mult] >>
  `Field (GF 2)` by rw[GF_2_field] >>
  `Poly (GF 2) h /\ 0 < poly_deg (GF 2) h /\ poly_lead (GF 2) h IN (Invertibles (GF 2).prod).carrier` by rw[GF_2_h_property] >>
  `Poly (GF 2) [1]` by rw[] >>
  `poly_deg (GF 2) [1] = 0` by rw[] >>
  rw[poly_mod_less]);

(* Theorem: (GF_4).prod.op [0;1] [1;1] = [1] *)
(* Proof:
   This is to show: poly_mod (GF 2) (poly_chop (GF 2) (weak_add (GF 2) [0; 0] (poly_shift (GF 2) [1; 1] 1))) h = [1]
   or, by EVAL, poly_mod (GF 2) [0; 1; 1] h = [1]
   Now  (PolyRing (GF 2)).sum.op h [1]
       = poly_chop (GF 2) (weak_add (GF 2) h [1])   by poly_ring_def
       = [0;1;1]                                    by EVAL
   Given Field (GF 2)                               by GF_2_field
   Hence true                                       by poly_field_add_mod
*)
val GF_4_mult_a_b = store_thm(
  "GF_4_mult_a_b",
  ``(GF_4).prod.op [0;1] [1;1] = [1]``,
  rw_tac std_ss[poly_ring_def, GF_mult] >>
  EVAL_TAC >>
  `(PolyRing (GF 2)).sum.op h [1] = poly_chop (GF 2) (weak_add (GF 2) h [1])` by rw_tac std_ss[poly_ring_def] >>
  `_ = [0;1;1]` by EVAL_TAC >>
  rw[GF_2_field, poly_field_add_mod]);

(* Theorem: (GF_4).prod.op [1;1] [0;1] = [1] *)
(* Proof:
   This is to show: poly_mod (GF 2) [0; 1; 1] h = [1]
   Now  (PolyRing (GF 2)).sum.op h [1]
       = poly_chop (GF 2) (weak_add (GF 2) h [1])   by poly_ring_def
       = [0;1;1]                                    by EVAL
   Given Field (GF 2)                               by GF_2_field
   Hence true                                       by poly_field_add_mod
*)
val GF_4_mult_b_a = store_thm(
  "GF_4_mult_b_a",
  ``(GF_4).prod.op [1;1] [0;1] = [1]``,
  rw_tac std_ss[poly_ring_def, GF_mult] >>
  EVAL_TAC >>
  `(PolyRing (GF 2)).sum.op h [1] = poly_chop (GF 2) (weak_add (GF 2) h [1])` by rw_tac std_ss[poly_ring_def] >>
  `_ = [0;1;1]` by EVAL_TAC >>
  rw[GF_2_field, poly_field_add_mod]);

(* Theorem: Group ((GF_4).prod excluding [] *)
(* Proof:
   Since Field (GF 2)                by GF_2_field
   poly_monic (GF 2) h               by GF_2_monic_h
   irreducible (PolyRing (GF 2)) h   by GF_2_irreducible_h
   Hence true                        by poly_mod_prod_group
*)
val GF_4_prod_group = store_thm(
  "GF_4_prod_group",
  ``Group ((GF_4).prod excluding [])``,
  `Field (GF 2)` by rw[GF_2_field] >>
  `poly_monic (GF 2) h` by rw[GF_2_monic_h] >>
  `irreducible (PolyRing (GF 2)) h` by rw[GF_2_irreducible_h] >>
  metis_tac[poly_mod_prod_group, poly_zero]);

(* Theorem: Field (GF_4) *)
(* Proof:
   Since Field (GF 2)                by GF_2_field
   poly_monic (GF 2) h               by GF_2_monic_h
   irreducible (PolyRing (GF 2)) h   by GF_2_irreducible_h
   Hence true                        by poly_mod_irreducible_field
*)
val GF_4_field = store_thm(
  "GF_4_field",
  ``Field (GF_4)``,
  `Field (GF 2)` by rw[GF_2_field] >>
  `poly_monic (GF 2) h` by rw[GF_2_monic_h] >>
  `irreducible (PolyRing (GF 2)) h` by rw[GF_2_irreducible_h] >>
  rw[poly_mod_irreducible_field]);

(* export simple results *)
val _ = export_rewrites ["GF_4_field", "GF_4_sum_id", "GF_4_prod_id"];

(* ------------------------------------------------------------------------- *)
(* Lifting h from GF(2)[x] to GF(4)[y]                                       *)
(* ------------------------------------------------------------------------- *)

(* H in GF(4)[y] = lift (GF 2) h, h in GF(2)[x] *)
val _ = temp_overload_on ("H", ``poly_lift (GF 2) h``);

(* Theorem: H = [[1]; [1]; [1]] *)
(* Proof: by EVAL. *)
val GF_4_H_by_lift = store_thm(
  "GF_4_H_by_lift",
  ``H = [[1]; [1]; [1]]``,
  EVAL_TAC);

(* Theorem: x IN (GF_4).carrier <=> (x = []) \/ (x = [1]) \/ (x = [0; 1]) \/ (x = [1; 1]) *)
(* Proof: by GF_4_carrier. *)
val GF_4_elements = store_thm(
  "GF_4_elements",
  ``!x. x IN (GF_4).carrier <=> (x = []) \/ (x = [1]) \/ (x = [0; 1]) \/ (x = [1; 1])``,
  rw[GF_4_carrier]);

(* Theorem: Poly (GF_4) H *)
(* Proof: by Poly_def. *)
val GF_4_H_poly = store_thm(
  "GF_4_H_poly",
  ``Poly (GF_4) H``,
  rw[Poly_def, GF_4_elements]);

(* Theorem: H IN (PolyRing GF_4).carrier *)
(* Proof:
   Since Poly (GF_4) H   by GF_4_H_poly,
   This is true          by poly_ring_element
*)
val GF_4_H_ring_element = store_thm(
  "GF_4_H_ring_element",
  ``H IN (PolyRing GF_4).carrier``,
  rw[GF_4_H_poly, poly_ring_element]);

(* Theorem: GF_4.sum.op [1] [1] = [] *)
(* Proof:
   By poly_mod_ring_def, this is to show:
   poly_mod (GF 2) ((PolyRing (GF 2)).sum.op [1] [1]) h = []
   Since (PolyRing (GF 2)).sum.op [1] [1] = []    by EVAL
   goal reduces to: poly_mod (GF 2) [] h = []
   This is true                                   by poly_zero_mod.
*)
val GF_4_sum_1_1 = store_thm(
  "GF_4_sum_1_1",
  ``GF_4.sum.op [1] [1] = []``,
  rw[poly_mod_ring_def] >>
  `(PolyRing (GF 2)).sum.op [1] [1] = []` by EVAL_TAC >>
  full_simp_tac std_ss[] >>
  `Ring (GF 2)` by rw[GF_2_field] >>
  `Poly (GF 2) h /\ 0 < poly_deg (GF 2) h /\ poly_lead (GF 2) h IN (Invertibles (GF 2).prod).carrier` by rw[GF_2_h_property] >>
  `(PolyRing (GF 2)).sum.id = []` by rw_tac std_ss[GF_4_ring, poly_ring_ids] >>
  metis_tac[poly_zero_mod]);

(* Theorem: GF_4.sum.op [1] [0;1] = [1;1] *)
(* Proof:
   By poly_mod_ring_def, this is to show:
   poly_mod (GF 2) ((PolyRing (GF 2)).sum.op [1] [0; 1]) h = [1; 1]
   Since (PolyRing (GF 2)).sum.op [1] [0; 1] = [1; 1]   by EVAL
   goal reduces to: poly_mod (GF 2) [1; 1] h = [1; 1]
   This is true                                   by poly_mod_less.
*)
val GF_4_sum_1_a = store_thm(
  "GF_4_sum_1_a",
  ``GF_4.sum.op [1] [0;1] = [1;1]``,
  rw[poly_mod_ring_def] >>
  `(PolyRing (GF 2)).sum.op [1] [0; 1] = [1; 1]` by EVAL_TAC >>
  full_simp_tac std_ss[] >>
  `Ring (GF 2)` by rw[GF_2_field] >>
  `Poly (GF 2) h /\ 0 < poly_deg (GF 2) h /\ poly_lead (GF 2) h IN (Invertibles (GF 2).prod).carrier` by rw[GF_2_h_property] >>
  rw[poly_mod_less]);

(* Theorem: GF_4.sum.op [1] [1;1] = [0;1] *)
(* Proof:
   By poly_mod_ring_def, this is to show:
   poly_mod (GF 2) ((PolyRing (GF 2)).sum.op [1] [1; 1]) h = [0; 1]
   Since (PolyRing (GF 2)).sum.op [1] [1; 1] = [0; 1]   by EVAL
   goal reduces to: poly_mod (GF 2) [0; 1] h = [0; 1]
   This is true                                         by poly_mod_less.
*)
val GF_4_sum_1_b = store_thm(
  "GF_4_sum_1_b",
  ``GF_4.sum.op [1] [1;1] = [0;1]``,
  rw[poly_mod_ring_def] >>
  `(PolyRing (GF 2)).sum.op [1] [1; 1] = [0; 1]` by EVAL_TAC >>
  full_simp_tac std_ss[] >>
  `Ring (GF 2)` by rw[GF_2_field] >>
  `Poly (GF 2) h /\ 0 < poly_deg (GF 2) h /\ poly_lead (GF 2) h IN (Invertibles (GF 2).prod).carrier` by rw[GF_2_h_property] >>
  rw[poly_mod_less]);

(* Theorem: GF_4.sum.op [0;1] [1;1] = [1] *)
(* Proof:
   By poly_mod_ring_def, this is to show:
   poly_mod (GF 2) ((PolyRing (GF 2)).sum.op [0; 1] [1; 1]) h = [1]
   Since (PolyRing (GF 2)).sum.op [0; 1] [1; 1] = [1]   by EVAL
   goal reduces to: poly_mod (GF 2) [1] h = [1]
   This is true                                         by poly_mod_less.
*)
val GF_4_sum_a_b = store_thm(
  "GF_4_sum_a_b",
  ``GF_4.sum.op [0;1] [1;1] = [1]``,
  rw[poly_mod_ring_def] >>
  `(PolyRing (GF 2)).sum.op [0; 1] [1; 1] = [1]` by EVAL_TAC >>
  full_simp_tac std_ss[] >>
  `Ring (GF 2)` by rw[GF_2_field] >>
  `Poly (GF 2) h /\ 0 < poly_deg (GF 2) h /\ poly_lead (GF 2) h IN (Invertibles (GF 2).prod).carrier` by rw[GF_2_h_property] >>
  rw[poly_mod_less]);

(* Theorem: poly_eval GF_4 H [] = [1] *)
(* Proof:
   By poly_eval_def, this is to show:
   GF_4.sum.op [1] (GF_4.prod.op (GF_4.sum.op [1] (GF_4.prod.op (GF_4.sum.op [1] (GF_4.prod.op [] [])) [])) []) = [1]
   True by field operations.
*)
val GF_4_H_eval_at_0 = store_thm(
  "GF_4_H_eval_at_0",
  ``poly_eval GF_4 H [] = [1]``,
  rw[poly_eval_def] >>
  metis_tac[GF_4_field, GF_4_elements, GF_4_sum_id, GF_4_prod_id, field_mult_rzero, field_add_rzero]);

(* Theorem: poly_eval GF_4 H [1] = [1] *)
(* Proof:
   By poly_eval_def, this is to show:
   GF_4.sum.op [1] (GF_4.prod.op (GF_4.sum.op [1] (GF_4.prod.op (GF_4.sum.op [1] (GF_4.prod.op [] [1])) [1])) [1]) = [1]
   This needs:
   GF_4.sum.op [1] [1] = [], true by GF_4_sum_1_1
   Hence true by field operations.
*)
val GF_4_H_eval_at_1 = store_thm(
  "GF_4_H_eval_at_1",
  ``poly_eval GF_4 H [1] = [1]``,
  rw[poly_eval_def] >>
  `GF_4.sum.op [1] [1] = []` by rw[GF_4_sum_1_1] >>
  metis_tac[GF_4_field, GF_4_elements, GF_4_sum_id, GF_4_prod_id, field_mult_lzero, field_mult_rone, field_add_rzero]);

(* Theorem: poly_eval GF_4 H [0;1] = [] *)
(* Proof:
   By poly_eval_def, this is to show:
   GF_4.sum.op [1] (GF_4.prod.op (GF_4.sum.op [1] (GF_4.prod.op (GF_4.sum.op [1] (GF_4.prod.op [] [0; 1])) [0; 1])) [0; 1]) = []
   This needs:
   GF_4.sum.op [1] [0;1] = [1;1],  true by GF_4_sum_1_a
   GF_4.prod.op [1;1] [0;1] = [1], true by GF_4_mult_b_a
   GF_4.sum.op [1] [1] = [],       true by GF_4_sum_1_1
   Hence true by field operations.
*)
val GF_4_H_eval_at_a = store_thm(
  "GF_4_H_eval_at_a",
  ``poly_eval GF_4 H [0; 1] = []``,
  rw[poly_eval_def] >>
  `GF_4.sum.op [1] [0;1] = [1;1]` by rw[GF_4_sum_1_a] >>
  `GF_4.prod.op [1;1] [0;1] = [1]` by rw[GF_4_mult_b_a] >>
  `GF_4.sum.op [1] [1] = []` by rw[GF_4_sum_1_1] >>
  metis_tac[GF_4_field, GF_4_elements, GF_4_sum_id, GF_4_prod_id, field_mult_lzero, field_mult_lone, field_add_rzero]);

(* Theorem: poly_eval GF_4 H [1;1] = [] *)
(* Proof:
   By poly_eval_def, this is to show:
   GF_4.sum.op [1] (GF_4.prod.op (GF_4.sum.op [1] (GF_4.prod.op (GF_4.sum.op [1] (GF_4.prod.op [] [1; 1])) [1; 1])) [1; 1]) = []
   This needs:
   GF_4.sum.op [1] [1;1] = [0;1],  true by GF_4_sum_1_b
   GF_4.prod.op [0;1] [1;1] = [1], true by GF_4_mult_a_b
   GF_4.sum.op [1] [1] = [],       true by GF_4_sum_1_1
   Hence true by field operations.
*)
val GF_4_H_eval_at_b = store_thm(
  "GF_4_H_eval_at_b",
  ``poly_eval GF_4 H [1;1] = []``,
  rw[poly_eval_def] >>
  `GF_4.sum.op [1] [1;1] = [0;1]` by rw[GF_4_sum_1_b] >>
  `GF_4.prod.op [0;1] [1;1] = [1]` by rw[GF_4_mult_a_b] >>
  `GF_4.sum.op [1] [1] = []` by rw[GF_4_sum_1_1] >>
  metis_tac[GF_4_field, GF_4_elements, GF_4_sum_id, GF_4_prod_id, field_mult_lzero, field_mult_lone, field_add_rzero]);

(* Theorem: poly_root (GF_4) H [0;1] *)
(* Proof: by GF_4_H_eval_at_a. *)
val GF_4_H_root_a = store_thm(
  "GF_4_H_root_a",
  ``poly_root (GF_4) H [0;1]``,
  rw_tac std_ss[poly_root_def, GF_4_H_eval_at_a, GF_4_sum_id]);

(* Theorem: poly_root (GF_4) H [1;1] *)
(* Proof: by GF_4_H_eval_at_b. *)
val GF_4_H_root_b = store_thm(
  "GF_4_H_root_b",
  ``poly_root (GF_4) H [1;1]``,
  rw_tac std_ss[poly_root_def, GF_4_H_eval_at_b, GF_4_sum_id]);

(* Theorem: poly_roots (GF_4) H = {[0;1]; [1;1]} *)
(* Proof:
   By GF_4_field and definitions, this is to show:
   (1) poly_root GF_4 H [] ==> F
       True by GF_4_H_eval_at_0.
   (2) poly_root GF_4 H [1] ==> F
       True by GF_4_H_eval_at_1.
   (3) poly_root GF_4 H [0; 1]
       True by GF_4_H_root_a.
   (4) poly_root GF_4 H [1; 1]
       True by GF_4_H_root_b.
*)
val GF_4_H_roots = store_thm(
  "GF_4_H_roots",
  ``poly_roots (GF_4) H = {[0;1]; [1;1]}``,
  `!x. x IN poly_roots (GF_4) H <=> (x = [0;1]) \/ (x = [1;1])` suffices_by rw[EXTENSION] >>
  `Field (GF_4)` by rw[GF_4_field] >>
  `(GF_4.sum.id = []) /\ (GF_4.prod.id = [1])` by rw[] >>
  `GF_4.sum.id <> GF_4.prod.id` by rw[] >>
  rw_tac std_ss[poly_roots_member, GF_4_elements, EQ_IMP_THM] >| [
    metis_tac[poly_root_def, GF_4_H_eval_at_0],
    metis_tac[poly_root_def, GF_4_H_eval_at_1],
    rw_tac std_ss[GF_4_H_root_a],
    rw_tac std_ss[GF_4_H_root_b]
  ]);

(* Theorem: CARD (poly_roots (GF_4) H) = 2 *)
(* Proof: by GF_4_H_roots. *)
val GF_4_H_roots_card = store_thm(
  "GF_4_H_roots_card",
  ``CARD (poly_roots (GF_4) H) = 2``,
  rw[GF_4_H_roots]);

(* Theorem: poly_deg (GF_4) H = 2 *)
(* Proof: by EVAL. *)
val GF_4_H_deg = store_thm(
  "GF_4_H_deg",
  ``poly_deg (GF_4) H = 2``,
  rw[]);

(* Theorem: x IN GF_4.carrier ==> GF_4.sum.op x x = GF_4.sum.id *)
(* Proof:
   This is because: x + x = 2 * x = 0   as 2 = 0 in (GF 2).
*)
val GF_4_sum_x_x = store_thm(
  "GF_4_sum_x_x",
  ``!x. x IN GF_4.carrier ==> (GF_4.sum.op x x = GF_4.sum.id)``,
  rpt strip_tac >>
  `Field (GF_4)` by rw[GF_4_field] >>
  `GF_4.sum.op x x = GF_4.prod.op (GF_4.sum.exp GF_4.prod.id 2) x` by rw_tac std_ss[field_single_add_single] >>
  `_ = GF_4.prod.op (GF_4.sum.op GF_4.prod.id GF_4.prod.id) x` by rw_tac std_ss[field_num_2] >>
  `_ = GF_4.prod.op (GF_4.sum.op [1] [1]) x` by rw_tac std_ss[GF_4_prod_id] >>
  `_ = GF_4.prod.op [] x` by rw_tac std_ss[GF_4_sum_1_1] >>
  `_ = GF_4.prod.op GF_4.sum.id x` by rw_tac std_ss[GF_4_sum_id] >>
  `_ = GF_4.sum.id` by rw_tac std_ss[field_mult_lzero] >>
  rw_tac std_ss[]);

(* Theorem: x IN GF_4.carrier ==> GF_4.sum.inv x = x *)
(* Proof: by GF_4_sum_x_x and field_add_eq_zero. *)
val GF_4_neg = store_thm(
  "GF_4_neg",
  ``!x. x IN GF_4.carrier ==> (GF_4.sum.inv x = x)``,
  rpt strip_tac >>
  `Field (GF_4)` by rw[GF_4_field] >>
  `GF_4.sum.op x x = GF_4.sum.id` by rw_tac std_ss[GF_4_sum_x_x] >>
  metis_tac[field_add_eq_zero]);

(* Theorem: (PolyRing GF_4).prod.id = lift (GF 2) GF_4.prod.id *)
(* Proof:
   By poly_ring_def, to show: poly_chop GF_4 [GF_4.prod.id] = lift GF_4.prod.id
   which is to show: [[1]] = lift [1]
   True by MAP.
*)
val GF_4_poly_one = store_thm(
  "GF_4_poly_one",
  ``(PolyRing GF_4).prod.id = poly_lift (GF 2) GF_4.prod.id``,
  rw[poly_ring_def]);

(* Theorem: x IN GF_4.carrier ==> GF_4.sum.op x [] = x *)
(* Proof:
   Given Field (GF_4)        by GF_4_field
     and GF_4.sum.id = []    by GF_4_sum_id
   Hence true                by field_add_rzero
*)
val GF_4_add_x_0 = store_thm(
  "GF_4_add_x_0",
  ``!x. x IN GF_4.carrier ==> (GF_4.sum.op x [] = x)``,
  `Field (GF_4)` by rw_tac std_ss[GF_4_field] >>
  `GF_4.sum.id = []` by rw_tac std_ss[GF_4_sum_id] >>
  metis_tac[field_add_rzero]);

(* Theorem: x IN GF_4.carrier ==> GF_4.sum.op [] x = x *)
(* Proof:
   Given Field (GF_4)           by GF_4_field
     and x + y = y + x          by field_add_comm
     and [] IN (GF_4).carrier   by GF_4_elements
   Hence true                   by GF_4_add_x_0
*)
val GF_4_add_0_x = store_thm(
  "GF_4_add_0_x",
  ``!x. x IN GF_4.carrier ==> (GF_4.sum.op [] x = x)``,
  `Field (GF_4)` by rw_tac std_ss[GF_4_field] >>
  `[] IN (GF_4).carrier` by rw_tac std_ss[GF_4_elements] >>
  metis_tac[GF_4_add_x_0, field_add_comm]);

(* Theorem: GF_4.sum.op [1] [] = [1] *)
(* Proof: by GF_4_add_x_0. *)
val GF_4_add_1_0 = store_thm(
  "GF_4_add_1_0",
  ``GF_4.sum.op [1] [] = [1]``,
  rw_tac std_ss[GF_4_elements, GF_4_add_x_0]);

(* Theorem: x IN GF_4.carrier ==> GF_4.prod.op x [1] = x *)
(* Proof:
   Given Field (GF_4)        by GF_4_field
     and GF_4.prod.id = [1]  by GF_4_prod_id
   Hence true                by field_mult_rone
*)
val GF_4_mult_x_1 = store_thm(
  "GF_4_mult_x_1",
  ``!x. x IN GF_4.carrier ==> (GF_4.prod.op x [1] = x)``,
  `Field (GF_4)` by rw_tac std_ss[GF_4_field] >>
  `GF_4.prod.id = [1]` by rw_tac std_ss[GF_4_prod_id] >>
  metis_tac[field_mult_rone]);

(* Theorem: x IN GF_4.carrier ==> GF_4.prod.op [1] x = x *)
(* Proof:
   Given Field (GF_4)           by GF_4_field
     and x * y = y * x          by field_mult_comm
     and [1] IN (GF_4).carrier  by GF_4_elements
   Hence true                   by GF_4_mult_x_1
*)
val GF_4_mult_1_x = store_thm(
  "GF_4_mult_1_x",
  ``!x. x IN GF_4.carrier ==> (GF_4.prod.op [1] x = x)``,
  `Field (GF_4)` by rw_tac std_ss[GF_4_field] >>
  `[1] IN (GF_4).carrier` by rw_tac std_ss[GF_4_elements] >>
  metis_tac[GF_4_mult_x_1, field_mult_comm]);

(* Theorem: GF_4.prod.op [0; 1] [1] = [0; 1] *)
(* Proof: by GF_4_mult_x_1. *)
val GF_4_mult_a_1 = store_thm(
  "GF_4_mult_a_1",
  ``GF_4.prod.op [0; 1] [1] = [0; 1]``,
  rw_tac std_ss[GF_4_elements, GF_4_mult_x_1]);

(* not successful:
GF_4_mult_x_1 |> SPEC ``[0; 1]`` |> UNDISCH |> PROVE_HYP (GF_4_elements |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH);
*)

(* Theorem: GF_4.prod.op [1] [1; 1] = [1; 1] *)
(* Proof: by GF_4_mult_1_x. *)
val GF_4_mult_1_b = store_thm(
  "GF_4_mult_1_b",
  ``GF_4.prod.op [1] [1; 1] = [1; 1] ``,
  rw_tac std_ss[GF_4_elements, GF_4_mult_1_x]);

(* Theorem: H = (PolyRing GF_4).prod.op (GF_4) (poly_factor (GF_4) [0;1]) (poly_factor (GF_4) [1;1]) *)
(* Proof:
   By definitions, this is to show:
   H = poly_chop GF_4 (weak_mult GF_4 [[0; 1]; [1]] [[1; 1]; [1]])
   True by computation.
*)
val GF_4_H_factors = store_thm(
  "GF_4_H_factors",
  ``H = (PolyRing GF_4).prod.op (poly_factor (GF_4) [0;1]) (poly_factor (GF_4) [1;1])``,
  rw_tac std_ss[poly_mult_def, poly_factor_def] >>
  `GF_4.sum.inv [0; 1] = [0; 1]` by rw_tac std_ss[GF_4_elements, GF_4_neg] >>
  `GF_4.sum.inv [1; 1] = [1; 1]` by rw_tac std_ss[GF_4_elements, GF_4_neg] >>
  `(PolyRing GF_4).prod.id = [[1]]` by rw_tac std_ss[poly_lift_def, GF_4_poly_one, GF_4_prod_id, GF_2_zero, MAP] >>
  rw_tac std_ss[] >>
  rw_tac std_ss[weak_mult_def, weak_cmult_def] >>
  `GF_4.prod.op [0; 1] [1; 1] = [1]` by rw_tac std_ss[GF_4_mult_a_b] >>
  `GF_4.prod.op [0; 1] [1] = [0; 1]` by rw_tac std_ss[GF_4_mult_a_1] >>
  `GF_4.prod.op [1] [1; 1] = [1; 1]` by rw_tac std_ss[GF_4_mult_1_b] >>
  `poly_shift GF_4 [] 1 = []` by rw_tac std_ss[poly_shift_of_zero] >>
  `GF_4.prod.op [1] [1] = [1]` by rw_tac std_ss[GF_4_mult_1_1] >>
  rw_tac std_ss[] >>
  rw_tac std_ss[weak_add_def] >>
  `poly_shift GF_4 [[1; 1]; [1]] 1 = [[]; [1; 1]; [1]]` by rw_tac std_ss[poly_shift_1, poly_ring_ids, GF_4_sum_id] >>
  rw_tac std_ss[weak_add_def] >>
  `GF_4.sum.op [1] [] = [1]` by rw_tac std_ss[GF_4_add_1_0] >>
  `GF_4.sum.op [0; 1] [1; 1] = [1]` by rw_tac std_ss[GF_4_sum_a_b] >>
  rw_tac std_ss[] >>
  rw[]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
