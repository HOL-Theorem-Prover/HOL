(* ------------------------------------------------------------------------- *)
(* Polynomial with coefficients from a Field                                 *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polyField";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory numberTheory combinatoricsTheory
     dividesTheory gcdTheory;

open monoidTheory groupTheory ringTheory integralDomainTheory fieldTheory;

(* (* val _ = load "polyWeakTheory"; *) *)
(* val _ = load "polyRingTheory"; *)
open polynomialTheory polyWeakTheory polyRingTheory;

(* ------------------------------------------------------------------------- *)
(* Polynomials over a Field F[x] Documentation                               *)
(* ------------------------------------------------------------------------- *)
(* Data type:
   A polynomial is just a list of coefficients from a Field r.
   Here a polynomial has no leading zeroes, i.e. not normalized.

   Overloads:
*)
(* Definitions and Theorems (# are exported):

   Polynomials over a Field (improves over R[x]):
#  poly_field_one_ne_zero  |- !r. Field r ==> |1| <> |0|
#  poly_field_one_poly     |- !r. Field r ==> poly |1|
   poly_field_one_nonzero  |- !r. Field r ==> ~zerop |1|

   Polynomial Scalar Multiplication (special role of c = #0  for F[x]):
   poly_field_weak_cmult_poly  |- !r. Field r ==> !p c. poly p /\ c IN R /\ c <> #0 ==> poly (c o p)
   poly_field_weak_cmult       |- !r. Field r ==> !p c. poly p /\ c IN R /\ c <> #0 ==> (c * p = c o p)
   poly_field_cmult_eq_zero    |- !r. Field r ==> !p c. poly p /\ c IN R ==>
                                                        ((c * p = |0|) <=> (p = |0|) \/ (c = #0))

   Polynomial Multiplication with zero product:
   poly_mult_eq_zero     |- !r. Field r ==> !p q. poly p /\ poly q ==>
                                                  ((p * q = |0|) <=> (p = |0|) \/ (q = |0|))

   Polynomials with Addition and Multiplication F[x] form an Integral Domain:
   poly_field_ring            |- !r. Field r ==> Ring (PolyRing r)
   poly_field_carriers        |- !r. ((PolyRing r).sum.carrier = (PolyRing r).carrier) /\
                                     ((PolyRing r).prod.carrier = (PolyRing r).carrier)
   poly_field_integral_domain |- !r. Field r ==> IntegralDomain (PolyRing r)

   Consequences of c * p = |0| <=> c = #0 or p = |0|:
   poly_cmult_eq         |- !r. Field r ==> !p q. poly p /\ poly q ==> !c. c IN R /\ c <> #0 ==> ((c * p = c * q) <=> (p = q))
   poly_cmult_inv_eq     |- !r. Field r ==> !p q. poly p /\ poly q ==> !c. c IN R+ ==> ((p = c * q) <=> (q = |/ c * p))

   Consequences of p * q = |0| <=> p = |0| or q = |0|:
   poly_mult_lcancel     |- !r. Field r ==> !p q t. poly p /\ poly q /\ poly t /\ t <> |0| ==> ((t * p = t * q) <=> (p = q))
   poly_mult_rcancel     |- !r. Field r ==> !p q t. poly p /\ poly q /\ poly t /\ t <> |0| ==> ((p * t = q * t) <=> (p = q))

   Consequences of c o p = c * p for c <> #0:
   poly_field_mult_cons  |- !r. Field r ==> !h t q. poly (h::t) /\ poly q ==> ((h::t) * q = h * q + (t * q) >> 1)
   poly_mult_eq_cmult    |- !r. Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| ==>
                                            !k. k IN R ==> ((p * q = k * q) <=> (p = [k]))
   poly_mult_lconst_swap |- !r. Field r ==> !c. c IN R /\ c <> #0 ==>
                                            !p q. poly p /\ poly q ==> ((p = [c] * q) <=> (q = [|/ c] * p))

   Polynomial Degree:
   poly_field_deg_cmult  |- !r. Field r ==> !p. poly p ==> !c. c IN R /\ c <> #0 ==> (deg (c * p) = deg p)
   poly_deg_mult_nonzero |- !r. Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| ==> (deg (p * q) = deg p + deg q)
   poly_field_deg_mult   |- !r. Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| ==> (deg (p * q) = deg p + deg q)

   Weak Multiplication in Field:
   poly_weak_mult_poly   |- !r. Field r ==> !p q. poly p /\ poly q ==> poly (p o q)
   poly_weak_mult        |- !r. Field r ==> !p q. poly p /\ poly q ==> (p * q = p o q)

   Polynomial leading coefficient:
#  poly_field_unit_lead  |- !r. Field r ==> !p. poly p /\ p <> |0| ==> unit (lead p)
#  poly_lead_cmult       |- !r. Field r ==> !p. poly p ==> !c::(R). lead (c * p) = c * lead p
#  poly_lead_mult        |- !r. Field r ==> !p q. poly p /\ poly q ==> (lead (p * q) = lead p * lead q)
   poly_lead_exp         |- !r. Field r ==> !p. poly p ==> !n. lead (p ** n) = lead p ** n
   poly_lead_cmult_equal |- !r. Field r ==> !p q.  poly p /\ poly q /\ q <> |0| ==>
                                            (lead p = lead (lead p * |/ (lead q) * q))

   Polynomial Exponentiation:
   poly_exp_eq_zero      |- !r. Field r ==> !p n. poly p /\ (p ** n = |0|) ==> (p = |0|)
   poly_exp_eq_zero_iff  |- !r. Field r ==> !p. poly p ==> !n. 0 < n ==> ((p ** n = |0|) <=> (p = |0|))
   poly_field_deg_exp    |- !r. Field r ==> !p. poly p ==> !n. deg (p ** n) = n * deg p

*)
(* ------------------------------------------------------------------------- *)
(* Polynomials over a Field.                                                 *)
(* ------------------------------------------------------------------------- *)

(*
This package derives the basic properties of polynomials, dependent on definitions;
specifically the normalization of polynomials to canonical form.

The polynomial package is intended to be built from these basic properties, without
dealing with normalization again.

There are several operations on polynomials:
* polynomial addition
* polynomial scalar multiplication
* polynomial negation
* polynomial shifts (i.e. multiply by X)
* polynomial multiplication
* polynomial division with remainder

Of these operations, only addition need to pay attention to normalization: first
perform pairwise add, then chop off any zerop leading coefficients.
Scalar multiplication can split to case of zerop scalar or non-zerop scalar: #0 * p = |0|, c * p <> |0| if c <> #0.
Negation of a polynomial never needs normalization.
Shifting of a polynomial never needs normalization.
Multiplication of polynomials is defined by addition of scalar multiplication and product with a shift, each already normalized.
Division of polynomials with remainder is defined by the Division Algorithm.

*)

(* ------------------------------------------------------------------------- *)
(* Polynomials over a Field (improves over R[x]).                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r ==> |1| <> |0| *)
(* Proof:
   Field r ==> Ring r     by field_is_ring
   Field r ==> #1 <> #0   by field_one_ne_zero
   hence true             by poly_one_ne_poly_zero
*)
val poly_field_one_ne_zero = store_thm(
  "poly_field_one_ne_zero",
  ``!r:'a field. Field r ==> |1| <> |0|``,
  rw[GSYM poly_one_ne_poly_zero]);

(* export simple result *)
val _ = export_rewrites ["poly_field_one_ne_zero"];

(* Theorem: Field r ==> poly |1| *)
(* Proof:
   Field r ==> Ring r     by field_is_ring
   hence true by          poly_one_poly
*)
val poly_field_one_poly = store_thm(
  "poly_field_one_poly",
  ``!r:'a field. Field r ==> poly |1|``,
  rw[]);

(* export simple result *)
val _ = export_rewrites ["poly_field_one_poly"];

(* Theorem: Field r ==> ~zerop |1| *)
(* Proof: by poly_nonzero_nonzero, poly_field_one_ne_zero. *)
val poly_field_one_nonzero = store_thm(
  "poly_field_one_nonzero",
  ``!r:'a field. Field r ==> ~zerop |1|``,
  metis_tac[poly_field_one_poly, poly_field_one_ne_zero, poly_nonzero_nonzero, poly_zero]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Scalar Multiplication (special role of c = #0  for F[x])       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: In F[x], c <> #0, poly p ==> poly (c o p) *)
(* Proof:
   If p = |0|, c o |0| = |0|, hence true.
   Since poly p = weak p /\ ((p = |0|) \/ LAST p <> #0)   by poly_def_alt
   LAST (c o p) = c * LAST p      by weak_cmult_map, LAST_MAP
                <> #0             by field_zero_product, c <> #0
   c o p = |0|  <=> p = |0|       by weak_cmult_eq_of_zero
   hence poly (c o p)             by poly_def_alt
*)
val poly_field_weak_cmult_poly = store_thm(
  "poly_field_weak_cmult_poly",
  ``!r:'a field. Field r ==> !p c. poly p /\ c IN R /\ c <> #0 ==> poly (c o p)``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[] >>
  metis_tac[poly_def_alt, field_zero_product, weak_last_element,
     poly_is_weak, weak_cmult_weak, field_is_ring, weak_cmult_map, LAST_MAP, poly_zero]);

(* Theorem: In F[x], c <> #0, poly p ==> c * p = c o p *)
(* Proof:
     c * p
   = chop (c o p)    by poly_cmult_def
   = c o p           by poly_field_weak_cmult_poly, poly_chop_poly
*)
val poly_field_weak_cmult = store_thm(
  "poly_field_weak_cmult",
  ``!r:'a field. Field r ==> !p c. poly p /\ c IN R /\ c <> #0 ==> (c * p = c o p)``,
  rw_tac std_ss[poly_cmult_def, poly_field_weak_cmult_poly, poly_chop_poly]);

(* Theorem: c * p = |0| <=> p = |0| or c = #0 *)
(* Proof:
   If part: c * p = |0| ==> p = |0| or c = #0
   By contradiction,
   suppose p <> |0| and c <> #0,
      |0| = c * p = c o p     by poly_field_weak_cmult, c <> #0
   ==> p = |0|                by weak_cmult_eq_zero
   contradicts p <> |0|.
   Only-if part:
      p = |0| or c = #0 ==> c * p = |0|
   If p = |0|, true by poly_cmult_zero.
   If c = #0, true by poly_cmult_lzero.

   Better:
   If c = #0,
     #0 * p = |0|      by poly_cmult_lzero
     hence true.
   If c <> #0,
       c * p = |0|
   <=> c o p = |0|     by poly_field_weak_cmult, c <> #0
   <=>     p = |0|     by weak_cmult_eq_zero
*)
val poly_field_cmult_eq_zero = store_thm(
  "poly_field_cmult_eq_zero",
  ``!r:'a field. Field r ==> !p c. poly p /\ c IN R ==>
           ((c * p = |0|) <=> (p = |0|) \/ (c = #0))``,
  rpt strip_tac >>
  Cases_on `c = #0` >-
  rw[] >>
  rw_tac std_ss[poly_field_weak_cmult, weak_cmult_eq_zero]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Multiplication with zero product.                              *)
(* ------------------------------------------------------------------------- *)

(*
Fundamentally, why does  p * q = |0| ==> p = |0| or q = |0| ?
This should come from:
- poly_mult_cross;
> val it = |- !f. Field r ==> !h k p q. poly (h::p) /\ poly (k::q) ==>
    ((h::p) * (k::q) = [h * k] + (h * q) >> 1 + (k * p) >> 1 + ((p * q) >> 1) >> 1) : thm

So it really is this:  [c1] + c2 * (p >> 1) + c3 * (q >> 1) + (p >> 1) * (q >> 1) = 0 means equal component is |0|.
or                     [c1] + (#0::p) + (#0::q) + (#0::(#0::r))) = |0| means each component is |0|
*)

(* The next theorem is closure of nonzero polynomial multiplication, crucial for showing a monoid and ring. *)
(* The fundamental reason why p <> |0| /\ q <> |0| ==> p * q <> |0| is this: constant term = product of constants. *)

(* Theorem: In F[x], p * q = |0| <=> p = |0| or q = |0| *)
(* Proof: by induction on p and q.
   Base case: ( |0| * q = |0|) <=> ( |0| = |0|) \/ (q = |0|)
      true by poly_mult_lzero.
   Step case: induct on q.
      Base case: (h::p) * |0| = |0|) <=> (h::p = |0|) \/ ( |0| = |0|)
         true by poly_mult_rzero.
      Step case: (p * q = |0|) <=> (p = |0|) \/ (q = |0|) ==>
                 (h::p) * (h'::q) = |0|) <=> (h::p = |0|) \/ (h'::q = |0|)
   Only goal is: (h::p) * (h'::q) = |0| <=> F
   Assume the contrary, i.e. h::p) * (h'::q) = |0|.
   Obviously,    (h::p) <> |0| and (h'::q) <> |0|

   If h = #0, p <> |0|          by poly_cons_property
     |0| = (h::p) * (h'::q)
   = (#0::p) * (h'::q)
   = (p >> 1) * (h'::q)         by poly_shift_1
   = (p * (h'::q)) >> 1         by poly_mult_shift_1_comm
   hence  p * (h'::q) = |0|     by poly_shift_eq_zero
   since p <> |0|, h'::q = |0|  by induction hypothesis, a contradiction.

   Similarly, if h' = #0 there will be a contradiction.

   When h <> #0 and h' <> #0, h * h' <> #0                            by field_zero_product
     (h::p) * (h'::q)
   = [h * h'] + ((h * q) >> 1 + (h' * p) >> 1 + ((p * q) >> 1) >> 1)  by poly_mult_cross
   = [h * h'] + (h * q + h' * p + (p * q) >> 1) >> 1                  by poly_add_shift_1, poly_add_poly
   <> |0|                                                             by poly_add_nonzero_const_shift_not_zero
   leads to contradiction with (h::p) * (h'::q) = |0|.
*)
val poly_mult_eq_zero = store_thm(
  "poly_mult_eq_zero",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> ((p * q = |0|) <=> (p = |0|) \/ (q = |0|))``,
  strip_tac >>
  strip_tac >>
  Induct >-
  metis_tac[poly_mult_lzero, poly_zero] >>
  strip_tac >>
  Induct >-
  metis_tac[poly_mult_rzero, poly_zero] >>
  rw_tac std_ss[poly_zero] >>
  (spose_not_then strip_assume_tac) >>
  `h::p <> [] /\ h'::q <> []` by rw_tac std_ss[] >>
  `h IN R /\ poly p /\ h' IN R /\ poly q` by metis_tac[poly_cons_poly] >>
  `Ring r` by rw_tac std_ss[field_is_ring] >>
  Cases_on `h = #0` >| [
    `p <> |0|` by metis_tac[poly_cons_property, poly_zero] >>
    `(h::p) * (h'::q) = (p * (h'::q)) >> 1` by rw_tac std_ss[poly_shift_1, poly_mult_shift_1_comm] >>
    metis_tac[poly_shift_eq_zero, poly_zero],
    Cases_on `h' = #0` >| [
      `q <> |0|` by metis_tac[poly_cons_property, poly_zero] >>
      `(h::p) * (h'::q) = ((h::p) * q) >> 1` by rw_tac std_ss[poly_shift_1, poly_mult_shift_1] >>
      metis_tac[poly_shift_eq_zero, poly_zero],
      `h * h' IN R /\ h * h' <> #0` by rw_tac std_ss[field_mult_element, field_zero_product] >>
      `poly [h*h'] /\ poly (h * q) /\ poly (h' * p) /\
       poly ((p * q) >> 1) /\ poly (h * q + h' * p + (p * q) >> 1)` by rw[] >>
      `(h::p) * (h'::q) = [h * h'] + ((h * q) >> 1 + (h' * p) >> 1 + ((p * q) >> 1) >> 1)` by metis_tac[poly_mult_cross] >>
      `_ = [h * h'] + (h * q + h' * p + (p * q) >> 1) >> 1` by rw_tac std_ss[poly_add_shift_1, poly_add_poly] >>
      metis_tac[poly_add_nonzero_const_shift_not_zero, poly_zero]
    ]
  ]);

(* The same proof basically works for an integral domain *)
Theorem poly_mult_eq_zero_domain:
  IntegralDomain r ==>
  !p q. poly p /\ poly q ==>
    ((poly_mult r p q = |0|) <=> (p = |0|) \/ (q = |0|))
Proof
  strip_tac >>
  Induct >-
  metis_tac[poly_mult_lzero, poly_zero] >>
  strip_tac >>
  Induct >-
  metis_tac[poly_mult_rzero, poly_zero] >>
  rw_tac std_ss[poly_zero] >>
  spose_not_then strip_assume_tac >>
  `h::p <> [] /\ h'::q <> []` by rw_tac std_ss[] >>
  `h IN R /\ poly p /\ h' IN R /\ poly q` by metis_tac[poly_cons_poly] >>
  `Ring r` by rw_tac std_ss[integral_domain_is_ring] >>
  Cases_on `h = #0` >- (
    `p <> |0|` by metis_tac[poly_cons_property, poly_zero] >>
    `(h::p) * (h'::q) = (p * (h'::q)) >> 1` by rw_tac std_ss[poly_shift_1, poly_mult_shift_1_comm] >>
    metis_tac[poly_shift_eq_zero, poly_zero] ) >>
  Cases_on `h' = #0` >- (
    `q <> |0|` by metis_tac[poly_cons_property, poly_zero] >>
    `(h::p) * (h'::q) = ((h::p) * q) >> 1` by rw_tac std_ss[poly_shift_1, poly_mult_shift_1] >>
    metis_tac[poly_shift_eq_zero, poly_zero] ) >>
  `h * h' IN R /\ h * h' <> #0` by metis_tac[ring_mult_element, IntegralDomain_def] >>
  `poly [h*h'] /\ poly (h * q) /\ poly (h' * p) /\
   poly ((p * q) >> 1) /\ poly (h * q + h' * p + (p * q) >> 1)` by rw[] >>
  `(h::p) * (h'::q) = [h * h'] + ((h * q) >> 1 + (h' * p) >> 1 + ((p * q) >> 1) >> 1)` by metis_tac[poly_mult_cross] >>
  `_ = [h * h'] + (h * q + h' * p + (p * q) >> 1) >> 1` by rw_tac std_ss[poly_add_shift_1, poly_add_poly] >>
  metis_tac[poly_add_nonzero_const_shift_not_zero, poly_zero]
QED

(* ------------------------------------------------------------------------- *)
(* Polynomials with Addition and Multiplication F[x] form an Integral Domain *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r ==> Ring (PolyRing r) *)
(* Proof: by field_is_ring, poly_ring_ring. *)
val poly_field_ring = store_thm(
  "poly_field_ring",
  ``!r:'a field. Field r ==> Ring (PolyRing r)``,
  rw[poly_ring_ring]);

(* Theorem: ((PolyRing r).sum.carrier = (PolyRing r).carrier) /\
            ((PolyRing r).prod.carrier = (PolyRing r).carrier) *)
val poly_field_carriers = save_thm("poly_field_carriers", poly_ring_carriers);
(* val poly_field_carriers =
   |- !r. ((PolyRing r).sum.carrier = (PolyRing r).carrier) /\
          ((PolyRing r).prod.carrier = (PolyRing r).carrier): thm *)

(* Theorem: polynomial additions and multiplications form an Integral Domain:
            Field r ==> IntegralDomain (PolyRing r) *)
(* Proof: by checking integral domain definition.
   (1) Ring (PolyRing r), poly_add_mult_ring.
   (2) |1| <> |0| by poly_field_one_ne_zero.
   (3) No zero divisor by poly_mult_eq_zero.
*)
val poly_field_integral_domain = store_thm(
  "poly_field_integral_domain",
  ``!r:'a field. Field r ==> IntegralDomain (PolyRing r)``,
  rw_tac std_ss[IntegralDomain_def, field_is_ring, poly_ring_element] >| [
    rw_tac std_ss[poly_add_mult_ring, field_is_ring],
    rw[],
    rw_tac std_ss[poly_mult_eq_zero]
  ]);

Theorem poly_integral_domain:
  IntegralDomain r ==> IntegralDomain (PolyRing r)
Proof
  rw[IntegralDomain_def]
  \\ simp[polyRingTheory.poly_ring_ring]
  >- ( imp_res_tac polynomialTheory.poly_one_ne_poly_zero \\ fs[] )
  \\ irule(SIMP_RULE(srw_ss())[]poly_mult_eq_zero_domain)
  \\ fs[IntegralDomain_def]
  \\ fs[poly_ring_def]
QED

(* ------------------------------------------------------------------------- *)
(* Consequences of c * p = |0| <=> c = #0 or p = |0|.                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: if c <> #0, then c * p = c * q  iff p = q *)
(* Proof:
       c * p = c * q
   <=> c * p - c * q = |0|   by poly_sub_eq_zero
   <=>   c * (p - q) = |0|   by poly_cmult_sub
   <=>         p - q = |0|   by poly_field_cmult_eq_zero, c <> #0
   <=>             p = q     by poly_sub_eq_zero
*)
val poly_cmult_eq = store_thm(
  "poly_cmult_eq",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==>
     !c. c IN R /\ c <> #0 ==> ((c * p = c * q) <=> (p = q))``,
  rw_tac std_ss[EQ_IMP_THM] >>
  `Ring r` by rw_tac std_ss[field_is_ring] >>
  `c * (p - q) = |0|` by rw[poly_sub_eq_zero] >>
  metis_tac[poly_sub_eq_zero, poly_field_cmult_eq_zero, poly_sub_poly]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==> !c. c IN R+ ==> ((p = c * q) <=> (q = |/c * p)) *)
(* Proof:
   Note c IN R             by field_nonzero_element
    and |/ c IN R          by field_inv_element, c IN R+
   If part: poly q /\ c IN R+ ==> q = |/ c * (c * q)
        |/ c * (c * q)
      = ( |/ c * c) * q    by poly_cmult_cmult
      = #1 * q = q         by field_mult_linv, poly_mult_lone
   Only-if part: poly p /\ c IN R+ ==> p = c * ( |/ c * p)
        c * ( |/ c * p)
      = (c * |/ c) * p     by poly_cmult_cmult
      = #1 * p = p         by field_mult_rinv, poly_mult_rone
*)
val poly_cmult_inv_eq = store_thm(
  "poly_cmult_inv_eq",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> !c. c IN R+ ==> ((p = c * q) <=> (q = |/c * p))``,
  rpt strip_tac >>
  `c IN R` by rw[field_nonzero_element] >>
  rw[EQ_IMP_THM] >-
  rw[poly_cmult_cmult, field_mult_linv] >>
  rw[poly_cmult_cmult, field_mult_rinv]);

(* ------------------------------------------------------------------------- *)
(* Consequences of p * q = |0| <=> p = |0| or q = |0|.                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: If t <> |0|,  t * p = t * q ==> p = q *)
(* Proof:
        t * p = t * q
   <=>  t * p - t * q = |0|     by poly_sub_eq_zero
   <=>    t * (p - q) = |0|     by poly_mult_rsub
   <=>          p - q = |0|     by poly_mult_eq_zero, t <> |0|
   <=>              p = q       by poly_sub_eq_zero
*)
val poly_mult_lcancel = store_thm(
  "poly_mult_lcancel",
  ``!r:'a field. Field r ==> !p q t. poly p /\ poly q /\ poly t /\
         t <> |0| ==> ((t * p = t * q) <=> (p = q))``,
  rw_tac std_ss[EQ_IMP_THM] >>
  `Ring r` by rw_tac std_ss[field_is_ring] >>
  `poly (t * p) /\ poly (t * q) /\ poly (p - q)` by rw[] >>
  `t * p - t * q = t * (p - q)` by rw_tac std_ss[poly_mult_rsub] >>
  metis_tac[poly_sub_eq_zero, poly_mult_eq_zero]);

(* Theorem: If t <> |0|,  p * t = q * t ==> p = q *)
(* Proof:
        p * t = q * t
   <=>  p * t - q * t = |0|     by poly_sub_eq_zero
   <=>    (p - q) * t = |0|     by poly_mult_lsub
   <=>          p - q = |0|     by poly_mult_eq_zero, t <> |0|
   <=>              p = q       by poly_sub_eq_zero
   Or, by poly_mult_lcancel, poly_mult_comm
*)
val poly_mult_rcancel = store_thm(
  "poly_mult_rcancel",
  ``!r:'a field. Field r ==> !p q t. poly p /\ poly q /\ poly t /\
         t <> |0| ==> ((p * t = q * t) <=> (p = q))``,
  metis_tac[poly_mult_lcancel, poly_mult_comm, field_is_ring]);

(* ------------------------------------------------------------------------- *)
(* Consequences of c o p = c * p for c <> #0.                                *)
(* ------------------------------------------------------------------------- *)

(* Need to lift a polyWeak theorem. *) (* Maybe not *)
(* val poly_chop_add_comm = lift_weak_poly_thm2 "poly_chop_add_comm"; *)
(* > val poly_chop_add_comm = |- !f. Field r ==> !p q. weak p /\ weak q ==> (chop (p || q) = chop (p || chop q)) : thm *)

(* Maybe:
- poly_mult_cons;
> val it = |- !r. Ring r ==> !t q. poly t /\ poly p ==> !h. h IN R ==> ((h::t) * p = h * p + (t * p) >> 1) : thm
*)

(* Theorem: (h::t) * q = h * q + (t * q) >> 1 *)
(* Proof:
   If h = #0,
      t <> |0|                      by poly_cons_property
      LHS = (#0::t) * q
          = (t >> 1) * q            by poly_shift_1
          = (t * q) >> 1            by poly_mult_shift_1_comm
          = #0 * q + (t * q) >> 1   by poly_cmult_lzero, poly_add_lzero
          = RHS
   If h <> #0,
     (h::t) * q
   = chop ((h::t) o q)                    by poly_mult_def
   = chop (h o q || (t o q) >> 1)         by weak_mult_cons
   = chop (h o q || chop ((t o q) >> 1))  by poly_chop_add_comm
   = chop (h o q || (chop (t o q) >> 1))  by poly_chop_shift
   = chop (h o q || (t * q) >> 1)         by poly_mult_def
   = chop (h * q || (t * q) >> 1)         by poly_field_weak_cmult, if h <> #0
   = h * q + (t * q) >> 1                 by poly_add_def
*)
val poly_field_mult_cons = store_thm(
  "poly_field_mult_cons",
  ``!r:'a field. Field r ==> !h t q. poly (h::t) /\ poly q ==> ((h::t) * q = h * q + (t * q) >> 1)``,
  rw_tac std_ss[poly_cons_poly] >>
  `poly (h::t)` by rw_tac std_ss[poly_cons_poly] >>
  `Ring r` by rw_tac std_ss[field_is_ring] >>
  Cases_on `h = #0` >| [
    `t <> []` by metis_tac[poly_cons_property] >>
    `(#0::t) = t >> 1` by rw_tac std_ss[poly_shift_1, poly_zero] >>
    metis_tac[poly_mult_shift_1_comm, poly_cmult_lzero, poly_add_lzero, poly_mult_poly, poly_shift_poly, poly_zero],
    `weak (h o q) /\ weak ((t o q) >> 1)` by rw[] >>
    rw_tac std_ss[poly_mult_def, poly_add_def, weak_mult_cons, poly_chop_add_comm, poly_field_weak_cmult, poly_chop_shift]
  ]);

(* Theorem: if  p <> |0|, q <> |0| then p * q = k * q  iff  p = [k]. *)
(* Proof:
   If-part:
   Since p <> |0| and q <> |0|,
         p * q <> |0|            by poly_mult_eq_zero
   hence k * q <> |0|
   or    k <> #0                 by poly_cmult_lzero

   Therefore  k * q = [k] * q    by poly_mult_lconst
   and  p * q = [k] * q
   or       p = [k]              by poly_mult_rcancel

   Only-if part: by poly_mult_lconst.
*)
val poly_mult_eq_cmult = store_thm(
  "poly_mult_eq_cmult",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| ==> !k. k IN R ==> ((p * q = k * q) <=> (p = [k]))``,
  metis_tac[poly_nonzero_element_poly, poly_mult_lconst, poly_mult_rcancel,
     poly_cmult_lzero, field_is_ring, poly_mult_eq_zero, poly_mult_lconst]);

(* Theorem: Field r ==> !c. c IN R /\ c <> #0 ==>
            !p q. poly p /\ poly q ==> ((p = [c] * q) <=> (q = [|/ c] * p)) *)
(* Proof:
   Since c IN R /\ c <> #0 ==> c IN R+   by field_nonzero_eq
      so |/ c IN R                       by field_inv_element, c IN R+
   If part: q = [|/ c] * ([c] * q)
        [|/ c] * ([c] * q)
      = |/ c * (c * q)                   by poly_mult_lconst
      = ( |/ c * c) * q                  by poly_cmult_cmult
      = #1 * q                           by field_mult_linv
      = q                                by poly_cmult_lone
   Only-if part: p = [c] * ([|/ c] * p)
        [c] * ([|/ c] * p)
      = c * ( |/ c * p)                  by poly_mult_lconst
      = (c * |/ c) * p                   by poly_cmult_cmult
      = #1 * p                           by field_mult_rinv
      = p                                by poly_cmult_lone
*)
val poly_mult_lconst_swap = store_thm(
  "poly_mult_lconst_swap",
  ``!r:'a field. Field r ==> !c. c IN R /\ c <> #0 ==>
   !p q. poly p /\ poly q ==> ((p = [c] * q) <=> (q = [|/ c] * p))``,
  rpt strip_tac >>
  `c IN R+` by rw[field_nonzero_eq] >>
  `|/ c IN R` by rw[field_inv_element] >>
  rw[EQ_IMP_THM] >-
  rw[poly_mult_lconst, poly_cmult_cmult, field_mult_linv] >>
  rw[poly_mult_lconst, poly_cmult_cmult, field_mult_rinv]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Degree                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: If c <> #0, deg (c * p) = deg p *)
(* Proof:
     deg (c * p)
   = deg (c o p)    by poly_field_weak_cmult
   = deg p          by poly_deg_weak_cmult
*)
val poly_field_deg_cmult = store_thm(
  "poly_field_deg_cmult",
  ``!r:'a field. Field r ==> !p. poly p ==> !c. c IN R /\ c <> #0 ==> (deg (c * p) = deg p)``,
  rw_tac std_ss[poly_field_weak_cmult, poly_deg_weak_cmult, poly_is_weak]);

(* The aim here is simple: to show: for p <> |0| and q <> |0|, deg (p * q) = deg p + deg q. *)

(* Theorem: p <> |0| and q <> |0| ==> deg (p * q) = deg p + deg q *)
(* Proof: by induction on p.
   Base case: p = |0| contradicts p <> |0|, hence true.
   Step case: deg (p * q) = deg p + deg q ==>
              !h. deg ((h::p) * q) = deg (h::p) + deg q
      If p = |0|,
      then h <> #0             by poly_cons_property
      LHS = deg ([h] * q)
          = deg (h * q)        by poly_mult_lconst
          = deg q              by poly_field_deg_cmult
          = deg [h] + deg q    by poly_deg_const, deg [h] = 0
          = RHS

      If p <> |0|,
      then p * q <> |0|        by poly_mult_eq_zero, since q <> |0|
      If h = #0,
      LHS = deg ((#0::p) * q)
          = deg ((p >> 1) * q)           by poly_shift_one, p <> |0|
          = deg (p * q) >> 1             by poly_mult_shift_1_comm
          = SUC (deg (p * q))            by poly_deg_shift_1, with p * q <> |0|
          = SUC (deg p + deg q)          by induction hypothesis
          = SUC (deg p) + deg q          by ADD
          = deg (#0::p) + deg q = RHS    by poly_deg_cons, p <> |0|
      If h <> #0,
      then  deg (h * q) = deg q          by poly_field_deg_cmult, h <> #0
      and   deg ((p * q) >> 1)
          = SUC (deg (p * q))            by poly_deg_shift_1, p * q <> |0|
          = SUC (deg p + deg q)          by induction hypothesis
      and  deg (h * q) < deg ((p * q) >> 1)   since  deg q  < SUC (deg p + deg q)

      LHS = deg ((h::p) * q)
          = deg (h * q + (p * q) >> 1)   by poly_field_mult_cons
          = SUC (deg p + deg q)          by poly_deg_add_less, deg (h * q) < deg ((p * q) >> 1)
          = SUC (deg p) + deg q          by ADD
          = deg (h::p) + deg q = RHS     by poly_deg_cons, p <> |0|
*)
val poly_deg_mult_nonzero = store_thm(
  "poly_deg_mult_nonzero",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| ==> (deg (p * q) = deg p + deg q)``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw_tac std_ss[poly_zero] >>
  rpt strip_tac >>
  `h IN R /\ poly p` by metis_tac[poly_cons_poly] >>
  `Ring r` by rw_tac std_ss[field_is_ring] >>
  Cases_on `p = |0|` >| [
    `h <> #0` by metis_tac[poly_cons_property, poly_zero] >>
    rw[poly_mult_lconst, poly_field_deg_cmult],
    `p * q <> |0|` by rw_tac std_ss[poly_mult_eq_zero] >>
    Cases_on `h = #0` >| [
      `#0::p = p >> 1` by rw_tac std_ss[poly_shift_1] >>
      `p >> 1 * q = (p * q) >> 1` by rw_tac std_ss[poly_mult_shift_1_comm] >>
      rw_tac std_ss[poly_deg_shift_1, poly_mult_poly, ADD],
      `deg q < SUC (deg p + deg q)` by decide_tac >>
      rw_tac std_ss[poly_field_deg_cmult, poly_deg_cons, poly_field_mult_cons,
        poly_deg_add_less, poly_deg_shift_1, poly_cmult_poly, poly_mult_poly, poly_shift_poly, ADD]
    ]
  ]);

(* This is a milestone theorem. *)

(* Theorem alias *)
val poly_field_deg_mult = save_thm("poly_field_deg_mult", poly_deg_mult_nonzero);
(*
val poly_field_deg_mult = |- !r. Field r ==>
    !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0| ==> (deg (p * q) = deg p + deg q): thm
*)

(* ------------------------------------------------------------------------- *)
(* Weak Multiplication in Field.                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: poly p /\ poly q ==> poly (p o q) *)
(* Proof: by induction on p.
   Base case: poly [] ==> poly ([] o q)
      true by weak_mult_of_lzero.
   Step case: poly (p o q) ==> poly ((h::p) o q)
   If h = #0, p <> |0|        by poly_cons_property, poly_zero
     (#0::p) o q
   = (p >> 1) o q             by poly_shift_1
   = (p o q) >> 1             by weak_mult_shift_1_comm, field_is_ring
   Since poly (p o q)         by induction hypothesis
   hence true                 by poly_shift_poly
   If h <> #0,
     poly (h o q)             by poly_field_weak_cmult_poly
     poly (p o q)             by induction hypothesis
     h o q = h * q, p o q = p * q    by poly_chop_poly
     If p = |0|, [h] o q = h o q     by weak_mult_const
     hence true by poly (h o q).
     If q = |0|, (h::p) o |0| = |0|  by weak_mult_rzero
     hence true by zero_poly_poly (or poly q).
     If p <> |0| and q <> |0|,
     p * q <> |0|             by poly_mult_eq_zero
     deg (h o q) = deg (h * q) = deg q           by poly_field_deg_cmult, need F[x]
     deg (p o q) = deg (p * q) = deg p + deg q   by poly_deg_mult_nonzero, need F[x], if p * q <> |0|
     deg ((p o q) >> 1) = SUC (deg p + deg q)      by poly_deg_shift_1
   hence deg (h o q) <> deg ((p o q) >> 1),
     (h::p) o q
   = h o q || (p o q) >> 1    by weak_mult_cons
   hence true                 by poly_weak_add_poly, degrees unequal.
*)
val poly_weak_mult_poly = store_thm(
  "poly_weak_mult_poly",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> poly (p o q)``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  rw_tac std_ss[poly_cons_poly] >>
  `poly (h::p)` by rw_tac std_ss[poly_cons_poly] >>
  `Ring r` by rw_tac std_ss[field_is_ring] >>
  `weak p /\ weak q /\ weak (h o q) /\ weak (p o q)` by rw[] >>
  Cases_on `h = #0` >-
  metis_tac[poly_cons_property, poly_shift_1, weak_mult_shift_1_comm, poly_shift_poly, poly_zero] >>
  `poly (h o q)` by rw_tac std_ss[poly_field_weak_cmult_poly] >>
  `poly (p o q)` by rw_tac std_ss[] >>
  `h o q = h * q` by rw_tac std_ss[poly_cmult_def, poly_chop_poly] >>
  `p o q = p * q` by rw_tac std_ss[poly_mult_def, poly_chop_poly] >>
  Cases_on `p = |0|` >-
  metis_tac[weak_mult_const, poly_zero] >>
  Cases_on `q = |0|` >-
  rw_tac std_ss[weak_mult_rzero] >>
  `p * q <> |0|` by rw_tac std_ss[poly_mult_eq_zero] >>
  `deg (h o q) = deg q` by rw_tac std_ss[poly_field_deg_cmult] >>
  `deg (p o q) = deg p + deg q` by rw_tac std_ss[poly_deg_mult_nonzero] >>
  `deg ((p o q) >> 1) = SUC (deg p + deg q)` by rw_tac std_ss[poly_deg_shift_1] >>
  `deg (h o q) <> deg ((p o q) >> 1)` by decide_tac >>
  `(h::p) o q = h o q || (p o q) >> 1` by rw_tac std_ss[weak_mult_cons] >>
  metis_tac[poly_weak_add_poly, poly_shift_poly]);

(* Theorem: poly p /\ poly q ==> p * q = p o q *)
(* Proof:
     p * q
   = chop (p o q)   by poly_mult_def
   = p o q          by poly_weak_mult_poly, poly_chop_poly
*)
val poly_weak_mult = store_thm(
  "poly_weak_mult",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> (p * q = p o q)``,
  rw_tac std_ss[poly_mult_def, poly_weak_mult_poly, poly_chop_poly]);

(* ------------------------------------------------------------------------- *)
(* Polynomial leading coefficient.                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r ==> !p. poly p /\ p <> |0| ==> unit (lead p) *)
(* Proof:
   Note lead p IN R      by poly_lead_element
    and lead p <> #0     by poly_lead_nonzero, p <> |0|
     so lead p IN R+     by field_nonzero_eq
     or unit (lead p)    by field_nonzero_unit
*)
val poly_field_unit_lead = store_thm(
  "poly_field_unit_lead",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==> unit (lead p)``,
  rpt strip_tac >>
  `lead p <> #0` by rw[poly_lead_nonzero] >>
  `lead p IN R+` by rw[field_nonzero_eq] >>
  rw[GSYM field_nonzero_unit]);

(* export simple result *)
val _ = export_rewrites ["poly_field_unit_lead"];

(* Theorem: poly p ==> lead (c * p) = c * lead p *)
(* Proof:
   If c = #0,
      lead (#0 * p) = lead |0|      by poly_cmult_lzero
                    = #0            by poly_lead_zero
                    = #0 * lead p   by field_mult_lzero
   If p = |0|,
      lead (c * |0|) = lead |0|     by poly_cmult_zero
                     = #0           by poly_lead_zero
                     = c * #0       by field_mult_rzero
                     = c * lead |0| by poly_lead_zero
   If c <> #0 and p <> |0|
     c * p <> |0|      by poly_field_cmult_eq_zero
     lead (c * p)
   = LAST (c * p)      by poly_lead_alt, c * p <> |0|
   = LAST (c o p)      by poly_field_weak_cmult, c <> #0
   = c * LAST p        by weak_cmult_map, LAST_MAP, poly_zero
   = c * lead p        by poly_lead_alt, p <> |0|
*)
val poly_lead_cmult = store_thm(
  "poly_lead_cmult",
  ``!r:'a field. Field r ==> !p. poly p ==> !c::(R). lead (c * p) = c * lead p``,
  rw_tac std_ss[RES_FORALL_THM] >>
  `Ring r` by rw_tac std_ss[field_is_ring] >>
  Cases_on `c = #0` >-
  rw[] >>
  Cases_on `p = |0|` >-
  rw[] >>
  metis_tac[poly_lead_alt, poly_field_cmult_eq_zero, poly_field_weak_cmult,
            poly_is_weak, weak_cmult_map, LAST_MAP, poly_zero]);

val _ = export_rewrites ["poly_lead_cmult"];

(* Theorem: p <> |0| and q <> |0| ==> lead (p * q) = lead p * lead q *)
(* Proof: (idea)
   First, p * q <> |0|                by poly_mult_eq_zero
     lead (p * q)
   = LAST (p * q)                     by poly_lead_alt, p * q <> |0|
   = EL (deg (p * q)) (p * q)         by poly_deg_eq_last_index, p * q <> |0|
   = EL (deg p + deg q) (p * q)       by poly_deg_mult_nonzero in F[x]
   = (EL (deg p) p) * (EL (deg q) q)  somehow by convolution element
   = LAST p * LAST q                  by poly_deg_eq_last_index, p <> |0|, q <> |0|
   = lead p * lead q                  by poly_lead_alt, p <> |0|, q <> |0|
*)
(* Proof: by induction on p.
   Base case: lead ([] * q) = lead [] * lead q
      true by poly_mult_lzero, poly_lead_zero, poly_zero.
   Step case: lead (p * q) = lead p * lead q ==>
              !h. lead ((h::p) * q) = lead (h::p) * deg q
      If q = |0|, true by poly_mult_rzero, poly_lead_zero.
      If p = |0|,
      then h <> #0                       by poly_cons_property
      LHS = lead ([h] * q)
          = lead (h * q)                 by poly_mult_lconst
          = h * lead q                   by poly_lead_cmult
          = lead [h] * deg q             by poly_lead_const, poly [h]
          = RHS

      If p <> |0|,
      If h = #0,
      LHS = lead ((#0::p) * q)
          = lead ((p >> 1) * q)          by poly_shift_1, p <> |0|
          = lead (p * q) >> 1            by poly_mult_shift_1_comm
          = lead (p * q)                 by poly_lead_shift, no need for p * q <> |0|
          = lead p * lead q              by induction hypothesis
          = lead (#0::p) * lead q = RHS  by poly_lead_cons, p <> |0|
      If h <> #0,
      then  deg (h * q) = deg q          by poly_field_deg_cmult, h <> #0
      and   deg ((p * q) >> 1)
          = SUC (deg (p * q))            by poly_shift_1, p * q <> |0| by poly_mult_eq_zero
          = SUC (deg p + deg q)          by poly_deg_mult_nonzero
      and  deg (h * q) < deg ((p * q) >> 1)   since  deg q  < SUC (deg p + deg q)

      LHS = lead ((h::p) * q)
          = lead (h * q + (p * q) >> 1)  by poly_field_mult_cons
          = lead ((p * q) >> 1)          by poly_lead_add_less, deg (h * q) < deg ((p * q) >> 1)
          = lead (p * q)                 by poly_lead_shift
          = lead p * lead q              by induction hypothesis
          = lead (h::p) * lead q = RHS   by poly_lead_cons, p <> |0|
*)
val poly_lead_mult = store_thm(
  "poly_lead_mult",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> (lead (p * q) = lead p * lead q)``,
  strip_tac >>
  strip_tac >>
  `Ring r` by rw_tac std_ss[field_is_ring] >>
  Induct >| [
    rpt strip_tac >>
    `lead ( |0| * q) = lead |0| * lead q` suffices_by rw_tac std_ss[poly_zero] >>
    rw[],
    rpt strip_tac >>
    `h IN R /\ poly p` by metis_tac[poly_cons_poly] >>
    Cases_on `q = |0|` >-
    rw_tac std_ss[poly_mult_rzero, poly_lead_zero, poly_is_weak, poly_lead_element, field_mult_rzero] >>
    Cases_on `p = |0|` >-
    rw[poly_mult_lconst] >>
    `poly (h * q) /\ poly (p * q) /\ poly ((p * q) >> 1)` by rw[] >>
    Cases_on `h = #0` >-
    metis_tac[poly_shift_1, poly_mult_shift_comm, poly_lead_shift, poly_lead_cons] >>
    `deg (h * q) = deg q` by rw_tac std_ss[poly_field_deg_cmult] >>
    `deg ((p * q) >> 1) = SUC (deg p + deg q)` by rw_tac std_ss[poly_deg_mult_nonzero, poly_deg_shift_1, poly_mult_eq_zero] >>
    `deg (h * q) < deg ((p * q) >> 1)` by decide_tac >>
    rw_tac std_ss[poly_field_mult_cons, poly_lead_add_less, poly_lead_shift, poly_lead_cons]
  ]);

(* export simple result *)
val _ = export_rewrites ["poly_lead_mult"];

(* Theorem: Field r ==> !p. poly p ==> !n. lead (p ** n) = (lead p) ** n *)
(* Proof:
   By induction on n.
   Base case: lead (p ** 0) = lead p ** 0
      LHS = lead (p ** 0)
          = lead |1|                 by poly_exp_0
          = #1                       by poly_lead_one
          = (lead p) ** 0            by ring_exp_0
          = RHS
   Step case: lead (p ** n) = lead p ** n ==> lead (p ** SUC n) = lead p ** SUC n
      LHS = lead (p ** SUC n)
          = lead (p * p ** n)        by poly_exp_SUC
          = lead p * lead (p ** n)   by poly_lead_mult, Field r.
          = lead p * (lead p) ** n   by induction hypothesis
          = (lead p) ** SUC n        by ring_exp_SUC
*)
val poly_lead_exp = store_thm(
  "poly_lead_exp",
  ``!r:'a field. Field r ==> !p. poly p ==> !n. lead (p ** n) = (lead p) ** n``,
  rpt strip_tac >>
  Induct_on `n`>>
  rw[]);

(* Theorem: poly p /\ poly q /\ q <> |0| ==> lead p = lead ((lead p) * |/ (lead q) * q) *)
(* Proof:
   Since lead q <> #0, |/ (lead q) exists.
   The result follows from poly_lead_cmult: lead (c * q) = c * lead q
*)
val poly_lead_cmult_equal = store_thm(
  "poly_lead_cmult_equal",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q /\ q <> |0| ==> (lead p = lead ((lead p) * |/ (lead q) * q))``,
  rpt strip_tac >>
  `lead p IN R /\ lead q IN R /\ lead q <> #0` by rw[] >>
  rw[field_nonzero_eq, field_mult_assoc]);

(* This is not true: in Z_9, lead ((3x+1)^2) = 6 see above, not 9. *)
(* Theorem: deg (p * p) = deg p + deg p. *)
(* Proof:
   If p = |0|, true         by poly_mult_lzero
   If p <> |0|,
     deg (p * p)
   = deg (chop (p o p))     by poly_mult_def
   <= deg (p o q)           by poly_deg_chop
   = deg p + deg q          by poly_deg_weak_mult, p <> |0| and q <> |0|
*)
(* This is not true: in Z_9, (3x + 1)^2 = 6x + 1. *)

(* Theorem: Ring r /\ poly p /\ p <> |0| ==> !n. 0 < n ==> lead (p ** n) = (lead p) ** n *)
(* Proof: by induction on n.
   Base case: 0 < 0 ==> lead (p ** 0) = lead p
     True by 0 < 0 = F.
   Step case: 0 < n ==> (lead (p ** n) = lead p) ==> 0 < SUC n ==> (lead (p ** SUC n) = lead p)
*)
(* This is not true: in Z_9, lead ((3x+1)^2) = 6 see above, not 9. *)

(* ------------------------------------------------------------------------- *)
(* Polynomial Exponentiation.                                                *)
(* ------------------------------------------------------------------------- *)

(* Note:
  The following theorem is trivial if    p ** (char r) = p.
  However, this can never be the case as the degree of both sides differ.
  The actual proof is therefore a bit involved.
*)

(* Theorem: Field r ==> !p n. poly p /\ (p ** n = |0|) ==> (p = |0|) *)
(* Proof:
   First, n <> 0 since
      p ** 0 = |1|            by poly_exp_0
             <> |0|           by poly_field_one_ne_zero, field_one_ne_zero
   Now poly p
    ==> lead p IN R           by poly_lead_element
    and lead p <> #0          by poly_lead_nonzero
   But #0 = lead |0|          by poly_lead_zero
          = lead (p ** n)     by given, p ** n = |0|
          = (lead p) ** n     by poly_lead_exp
   giving lead p = #0         by field_exp_eq_zero, n <> 0.
   This contradicts lead p <> #0.
*)
val poly_exp_eq_zero = store_thm(
  "poly_exp_eq_zero",
  ``!r:'a field. Field r ==> !p n. poly p /\ (p ** n = |0|) ==> (p = |0|)``,
  spose_not_then strip_assume_tac >>
  `(p ** 0 = |1|) /\ |1| <> |0|` by rw[] >>
  `lead p IN R /\ lead p <> #0 /\ (lead |0| = #0)` by rw[] >>
  metis_tac[field_exp_eq_zero, poly_lead_exp]);

(* Note: For the converse, p = |0| /\ n <> 0 ==> p ** n = |0|  by poly_zero_exp *)

(* Theorem: Field r ==> !p. poly p ==> 0 < n ==> ((p ** n = |0|) <=> (p = |0|)) *)
(* Proof:
   If part: 0 < n /\ (p ** n = |0|) ==> (p = |0|), true by poly_exp_eq_zero
   Only-if part: 0 < n ==> ( |0| ** n = |0|), true       by poly_zero_exp
*)
val poly_exp_eq_zero_iff = store_thm(
  "poly_exp_eq_zero_iff",
  ``!r:'a field. Field r ==> !p. poly p ==> !n. 0 < n ==> ((p ** n = |0|) <=> (p = |0|))``,
  rw_tac std_ss[EQ_IMP_THM] >-
  metis_tac[poly_exp_eq_zero] >>
  rw[poly_zero_exp]);

(* Note: This is not true for Ring r, e.g. (3x) ** 2 = |0| in Z_9 *)

(* Theorem: Field r ==> !p. poly p ==> !n. deg (p ** n) = n * deg p *)
(* Proof:
   If p = |0|,
        deg ( |0| ** n)
      = deg (if n = 0 then |1| else |0|)  by poly_zero_exp
      = 0            by poly_deg_zero, poly_deg_one
      = n * deg |0|  by poly_deg_zero
   If p <> |0|,
      By induction on n.
      Base: deg (p ** 0) = 0 * deg p
          deg (p ** 0)
        = deg |1|    by poly_exp_0
        = 0          by poly_deg_one
        = 0 * deg p  by MULT
      Step: deg (p ** n) = n * deg p ==> deg (p ** SUC n) = SUC n * deg p
        Note p <> |0| ==> p ** n <> |0|   by poly_exp_eq_zero
          deg (p ** SUC n)
        = deg (p * p ** n)       by poly_exp_SUC
        = deg p + deg (p ** n)   by poly_deg_mult_nonzero
        = deg p + n * deg p      by induction hypothesis
        = deg p + deg p * n      by MULT_COMM
        = deg p * SUC n          by MULT_SUC
        = SUC n * deg p          by MULT_COMM
*)
val poly_field_deg_exp = store_thm(
  "poly_field_deg_exp",
  ``!r:'a field. Field r ==> !p. poly p ==> !n. deg (p ** n) = n * deg p``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[poly_zero_exp] >>
  Induct_on `n` >-
  rw[] >>
  `p ** n <> |0|` by metis_tac[poly_exp_eq_zero] >>
  `poly (p ** n)` by rw[] >>
  `deg (p ** SUC n) = deg (p * p ** n)` by rw[] >>
  `_ = deg p + deg (p ** n)` by rw[poly_deg_mult_nonzero] >>
  metis_tac[MULT_SUC, MULT_COMM]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
