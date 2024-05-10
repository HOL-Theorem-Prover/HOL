(* ------------------------------------------------------------------------- *)
(* Polynomial with coefficients from a Ring                                  *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polyRing";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory arithmeticTheory listTheory rich_listTheory numberTheory
     dividesTheory combinatoricsTheory;

open monoidTheory groupTheory ringTheory;
open polynomialTheory polyWeakTheory;

val _ = temp_overload_on("SQ", ``\n. n * n``);
val _ = temp_overload_on("HALF", ``\n. n DIV 2``);
val _ = temp_overload_on("TWICE", ``\n. 2 * n``);

val _ = intLib.deprecate_int ();

(* ------------------------------------------------------------------------- *)
(* Polynomials over a Ring R[x] Documentation                                *)
(* ------------------------------------------------------------------------- *)
(* Data type:
   A polynomial is just a list of coefficients from a Ring r.
   Here a polynomial has no leading zeroes, i.e. not normalized.

   Overloads:
   - p        = (PolyRing r).sum.inv p
   p - q      = poly_sub r p q
*)
(* Definitions and Theorems (# are exported):

   Polynomials over a Ring:
   zero_poly_poly             |- !r. poly [] <=> T
   poly_cons_poly             |- !r h t. poly (h::t) <=> h IN R /\ poly t /\ ~zerop (h::t)
   poly_cons_not_zero         |- !h t. poly (h::t) ==> ~zerop (h::t)
   zero_poly_zero_poly        |- !p. poly p /\ zerop p ==> (p = [])
   zero_poly_eq_poly_zero     |- !p. poly p ==> (zerop p <=> (p = |0|))
   poly_nonzero_nonzero       |- !p. poly p /\ p <> [] ==> ~zerop p
   poly_property              |- !p. poly p ==> (p = []) \/ ~zerop p
   poly_nonzero_element_poly  |- !c. c IN R /\ c <> #0 <=> poly [c]
   poly_cons_last_nonzero     |- !h t. poly (h::t) ==> LAST (h::t) <> #0
   poly_cons_property         |- !h t. poly (h::t) ==> ~((h = #0) /\ (t = []))
   poly_nonzero_cons_poly     |- !r h p. h IN R /\ poly p /\ p <> |0| ==> poly (h::p)
   poly_pad_left_poly         |- !r. Ring r ==> !p n. poly p /\ p <> |0| ==> poly (PAD_LEFT #0 n p)

   Useful Theorems:
#  poly_one_poly         |- !r. Ring r ==> poly |1|
   poly_one_ne_zero      |- [#1] <> []
   poly_one_alt          |- !r. #1 <> #0 ==> ( |1| = [#1])
#  poly_one_nonzero      |- !r. Ring r /\ #1 <> #0 ==> ~zerop |1|

   Polynomials as weak polynomials:
#  poly_is_weak        |- !p. poly p ==> weak p
#  poly_chop_weak_poly |- !p. weak p ==> poly (chop p)
   poly_def_alt        |- !p. poly p <=> weak p /\ ((p = |0|) \/ LAST p <> #0)
   poly_every_element  |- !p. poly p ==> EVERY (\c. c IN R) p
   poly_every_mem      |- !r p. poly p ==> !x. MEM x p ==> x IN R

   Polynomial Normalization:
#  poly_chop_poly      |- !p. poly p ==> (chop p = p)
   poly_chop_eq_poly   |- !r. Ring r ==> !p. poly p <=> weak p /\ (chop p = p)
#  poly_chop_one       |- !r. Ring r /\ #1 <> #0 ==> (chop |1| = |1|)

   Polynomial Ring:
   poly_ring_property  |- !r. (!p. poly p <=> p IN (PolyRing r).carrier) /\
                              (!p. poly p <=> p IN (PolyRing r).sum.carrier) /\
                              (!p. poly p <=> p IN (PolyRing r).prod.carrier) /\
                              (!p q. p + q = chop (p || q)) /\
                              (!p q. p * q = chop (p o q)) /\
                              ( |0| = []) /\ ( |1| = chop [#1])
   poly_ring_carriers  |- !r. ((PolyRing r).sum.carrier = (PolyRing r).carrier) /\
                              ((PolyRing r).prod.carrier = (PolyRing r).carrier)
   poly_ring_element   |- !r. (!p. p IN (PolyRing r).carrier <=> poly p) /\
                              (!p. p IN (PolyRing r).sum.carrier <=> poly p) /\
                              (!p. p IN (PolyRing r).prod.carrier <=> poly p)

   Polynomial Addition:
#  poly_add_zero_zero  |- |0| + |0| = |0|
#  poly_add_lzero      |- !p. poly p ==> ( |0| + p = p)
#  poly_add_rzero      |- !p. poly p ==> (p + |0| = p)
   poly_add_zero       |- !r p. poly p ==> ( |0| + p = p) /\ (p + |0| = p)
#  poly_add_poly       |- !r. Ring r ==> !p q. poly p /\ poly q ==> poly (p + q)
   poly_add_comm       |- !r. Ring r ==> !p q. poly p /\ poly q ==> (p + q = q + p)
   poly_add_assoc      |- !r.  Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> (p + q + t = p + (q + t))
   poly_add_clauses    |- !r.  Ring r ==> !p q t. poly p /\ poly q /\ poly t ==>
                              ([] + p = p) /\ (p + [] = p) /\ (p + q = q + p) /\ (p + q + t = p + (q + t))

   Polynomial Negation (as inverse of polynomial addition):
   poly_negate_poly  |- !r. Ring r ==> !p. poly p ==> poly (neg p)
   poly_add_lnegate  |- !r. Ring r ==> !p. poly p ==> (neg p + p = |0|)
   poly_add_rnegate  |- !r. Ring r ==> !p. poly p ==> (p + neg p = |0|)

   Polynomial Additions form a Group:
   poly_add_group          |- !r. Ring r ==> Group (PolyRing r).sum
   poly_add_abelian_group  |- !r. Ring r ==> AbelianGroup (PolyRing r).sum

   Polynomial Multiplication (just for Monoid (PolyRing r).prod):
   poly_mult_const       |- !r. Ring r ==> !p. poly p ==> !c. c IN R ==> ([c] * p = chop [c] * p)
   poly_mult_const_comm  |- !r. Ring r ==> !p. poly p ==> !c. c IN R ==> (p * [c] = p * chop [c])
   poly_mult_const_const |- !r. Ring r ==> !h k. h IN R /\ k IN R ==> (chop [h] * chop [k] = chop [h * k])
#  poly_mult_lone        |- !r. Ring r ==> !p. poly p ==> ( |1| * p = p)
#  poly_mult_rone        |- !r. Ring r ==> !p. poly p ==> (p * |1| = p)
   poly_mult_one         |- !r. Ring r ==> !p. poly p ==> ( |1| * p = p) /\ (p * |1| = p)
#  poly_mult_poly        |- !r. Ring r ==> !p q. poly p /\ poly q ==> poly (p * q)
   poly_mult_comm        |- !r. Ring r ==> !p q. poly p /\ poly q ==> (p * q = q * p)
   poly_mult_assoc       |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> (p * q * t = p * (q * t))

   Polynomial Multiplications form a Monoid:
   poly_mult_monoid          |- !r. Ring r ==> Monoid (PolyRing r).prod
   poly_mult_abelian_monoid  |- !r. Ring r ==> AbelianMonoid (PolyRing r).prod

   Theorems on polynomial multiplication distributes over addition:
#  poly_mult_radd    |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> (p * (q + t) = p * q + p * t)
#  poly_mult_ladd    |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> ((p + q) * t = p * t + q * t)
   poly_mult_add     |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==>
                                       ((p + q) * t = p * t + q * t) /\ (p * (q + t) = p * q + p * t)

   Polynomials with Addition and Multiplication R[x] form a Ring:
   poly_add_mult_ring    |- !r. Ring r ==> Ring (PolyRing r)
   poly_ring_ring        |- !r. Ring r ==> Ring (PolyRing r)
#  poly_mult_one_one     |- !r. Ring r ==> ( |1| * |1| = |1|)
   poly_one_eq_zero      |- !r. Ring r ==> (( |1| = |0|) <=> !p. poly p ==> (p = |0|))
   poly_zero_eq_one      |- !r. Ring r ==> (( |0| = |1|) <=> (#0 = #1))
   poly_zero_all_poly    |- !r. Ring r ==> (#1 = #0 <=> !p. poly p ==> p = |0|)
   poly_deg_pos_ring_one_ne_zero
                         |- !r. Ring r ==> !p. poly p /\ 0 < deg p ==> #1 <> #0

   Polynomial Scalar Multiplication:
#  poly_cmult_zero      |- !c. c * |0| = |0|
   poly_cmult_of_zero   |- !c. c * [] = []
#  poly_cmult_lzero     |- !r. Ring r ==> !p. poly p ==> (#0 * p = |0|)
#  poly_cmult_poly      |- !r. Ring r ==> !p. poly p ==> !c. c IN R ==> poly (c * p)
   poly_cmult_const          |- !r. Ring r ==> !c h. c IN R /\ h IN R ==> (c * [h] = chop [c * h])
   poly_cmult_const_nonzero  |- !r h k. k * h <> #0 ==> (k * [h] = [k * h])

   Polynomial Addition:
#  poly_add_lzero_poly  |- !r. Ring r ==> !p q. poly p /\ zerop q ==> (q + p = p)
#  poly_add_rzero_poly  |- !r. Ring r ==> !p q. poly p /\ zerop q ==> (p + q = p)
   poly_add_const_const |- !r. Ring r ==> !h k. h IN R /\ k IN R ==> (chop [h] + chop [k] = chop [h + k])

   Polynomial Negation = Inverse of polynomial addition:
   poly_neg_def       |- !r. Ring r ==> !p. poly p ==> (-p = neg p)
#  poly_neg_zero      |- !r. Ring r ==> (-|0| = |0|)
#  poly_neg_of_zero   |- !r. Ring r ==> (-[] = [])
#  poly_neg_cons      |- !r. Ring r ==> !h t. poly (h::t) ==> (-(h::t) = -h::-t)
   poly_neg_clauses   |- !r. Ring r ==> (-|0| = |0|) /\ !h t. poly (h::t) ==> (-(h::t) = -h::-t)
#  poly_neg_poly      |- !r. Ring r ==> !p. poly p ==> poly (-p)
   poly_neg_eq_zero   |- !r. Ring r ==> !p. poly p ==> ((-p = |0|) <=> (p = |0|))
#  poly_neg_neg       |- !r. Ring r ==> !p. poly p ==> (--p = p)
   poly_neg_nonzero   |- !r. Ring r ==> !h. h IN R /\ h <> #0 ==> (-[h] = [-h])
   poly_chop_negate   |- !r. Ring r ==> !p. poly p ==> (chop (-p) = -chop p)
   poly_neg_const     |- !r. Ring r ==> !x. x IN R ==> (chop [-x] = -chop [x])
   poly_add_eq_zero   |- !r. Ring r ==> !p q. poly p /\ poly q ==> ((p + q = |0|) <=> (p = -q))
#  poly_add_lneg      |- !r. Ring r ==> !p. poly p ==> (-p + p = |0|)
#  poly_add_rneg      |- !r. Ring r ==> !p. poly p ==> (p + -p = |0|)
   poly_neg_add_comm  |- !r. Ring r ==> !p q. poly p /\ poly q ==> (-(p + q) = -q + -p)
#  poly_neg_add       |- !r. Ring r ==> !p q. poly p /\ poly q ==> (-(p + q) = -p + -q)
   poly_add_lcancel   |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> ((t + p = t + q) <=> (p = q))
   poly_add_rcancel   |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> ((p + t = q + t) <=> (p = q))

   Polynomial Subtraction:
#  poly_sub_def       |- !r p q. p - q = p + -q
   poly_sub_alt       |- !r p q. p - q = ring_sub (PolyRing r) p q
#  poly_sub_poly      |- !r. Ring r ==> !p q. poly p /\ poly q ==> poly (p - q)
#  poly_sub_lzero     |- !r. Ring r ==> !p. poly p ==> ( |0| - p = -p)
#  poly_sub_rzero     |- !r. Ring r ==> !p. poly p ==> (p - |0| = p)
   poly_sub_eq_zero   |- !r. Ring r ==> !p q. poly p /\ poly q ==> ((p - q = |0|) <=> (p = q))
   poly_sub_eq        |- !r. Ring r ==> !p. poly p ==> (p - p = |0|)
   poly_sub_lcancel   |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> ((t - p = t - q) <=> (p = q))
   poly_sub_rcancel   |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> ((p - t = q - t) <=> (p = q))

   Polynomial Addition and Subtraction:
   poly_neg_sub       |- !r. Ring r ==> !p q. poly p /\ poly q ==> (-(p - q) = q - p)
   poly_sub_eq_add    |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> ((p - q = t) <=> (p = q + t))
   poly_add_eq_sub    |- !r. Ring r ==> !p q t s. poly p /\ poly q /\ poly t /\ poly s ==>
                                                  ((p + t = q + s) <=> (p - q = s - t))
   poly_add_sub_assoc |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> (p + q - t = p + (q - t))
   poly_add_sub       |- !r. Ring r ==> !p q. poly p /\ poly q ==> (p + q - q = p)
   poly_add_sub_comm  |- !r. Ring r ==> !p q. poly p /\ poly q ==> (p + q - p = q)
   poly_sub_add       |- !r. Ring r ==> !p q. poly p /\ poly q ==> (p - q + q = p)
   poly_sub_plus      |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> (p - (q + t) = p - q - t)
   poly_sub_minus     |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> (p - (q - t) = p - q + t)

   Polynomial Scalar Multiplication:
   poly_cmult_add        |- !r. Ring r ==> !p q. poly p /\ poly q ==> !c. c IN R ==> (c * (p + q) = c * p + c * q)
   poly_add_cmult        |- !r. Ring r ==> !p. poly p ==> !b c. b IN R /\ c IN R ==> ((b + c) * p = b * p + c * p)
   poly_cmult_cmult      |- !r. Ring r ==> !p. poly p ==> !b c. b IN R /\ c IN R ==> (b * (c * p) = b * c * p)
   poly_cmult_cmult_comm |- !r. Ring r ==> !p. poly p ==> !b c. b IN R /\ c IN R ==> (b * (c * p) = c * (b * p))
#  poly_cmult_neg        |- !r. Ring r ==> !p. poly p ==> !c. c IN R ==> (c * -p = -c * p)
#  poly_neg_cmult        |- !r. Ring r ==> !p. poly p ==> !c. c IN R ==> (-c * p = -(c * p))
#  poly_cmult_sub        |- !r. Ring r ==> !p q. poly p /\ poly q ==> !c. c IN R ==> (c * (p - q) = c * p - c * q)

   Polynomial Shifts:
#  poly_shift_poly       |- !r. Ring r ==> !p n. poly p ==> poly (p >> n)
   poly_neg_shift        |- !r. Ring r ==> !p. poly p ==> !n. -p >> n = -(p >> n)
   poly_add_shift_1      |- !r. Ring r ==> !p q. (p + q) >> 1 = p >> 1 + q >> 1
   poly_add_shift        |- !r. Ring r ==> !p q n. (p + q) >> n = p >> n + q >> n
   poly_cmult_shift_1    |- !r. Ring r ==> !p. poly p ==> !c. c IN R ==> ((c * p) >> 1 = c * p >> 1)
   poly_cmult_shift      |- !r. Ring r ==> !p. poly p ==> !c. c IN R ==> !n. (c * p) >> n = c * p >> n

   Polynomial Multiplication:
#  poly_mult_lzero       |- !p. |0| * p = |0|
#  poly_mult_rzero       |- !p. p * |0| = |0|
   poly_mult_zero        |- !p. ( |0| * p = |0|) /\ (p * |0| = |0|)
   poly_mult_of_zero     |- !r p. (p * [] = []) /\ ([] * p = [])
   poly_mult_clauses     |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==>
                                           ( |0| * p = |0|) /\ (p * |0| = |0|) /\ ( |1| * p = p) /\
                                           (p * |1| = p) /\ (p * q = q * p) /\ (p * q * t = p * (q * t))
   poly_mult_assoc_comm  |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> (p * (q * t) = q * (p * t))

   Theorems on polynomial multiplication with shifting:
#  poly_mult_shift_1         |- !r. Ring r ==> !p q. poly p /\ poly q ==> ((p * q) >> 1 = p * q >> 1)
#  poly_mult_shift_1_comm    |- !r. Ring r ==> !p q. poly p /\ poly q ==> ((p * q) >> 1 = p >> 1 * q)
   poly_mult_shift           |- !r. Ring r ==> !p q. poly p /\ poly q ==> !n. (p * q) >> n = p * q >> n
   poly_mult_shift_comm      |- !r. Ring r ==> !p q. poly p /\ poly q ==> !n. (p * q) >> n = p >> n * q

   Theorems on polynomial multiplication with scalar multiplication:
#  poly_cmult_mult  |- !r. Ring r ==> !p q. poly p /\ poly q ==> !c. c IN R ==> (c * p * q = c * (p * q))
#  poly_cmult_one   |- !r. Ring r ==> !c. c IN R ==> (c * |1| = if c = #0 then [] else [c])
#  poly_cmult_lone  |- !r. Ring r ==> !p. poly p ==> (#1 * p = p)
   poly_cmult_alt   |- !r. Ring r ==> !c p. c IN R /\ poly p ==> (c * p = c * |1| * p)
   poly_mult_cmult  |- !r. Ring r ==> !c. c IN R ==> !p q. poly p /\ poly q ==> (p * (c * q) = c * p * q)

   Theorems on polynomial multiplication with negation:
#  poly_mult_lneg    |- !r. Ring r ==> !p q. poly p /\ poly q ==> (-p * q = -(p * q))
#  poly_mult_rneg    |- !r. Ring r ==> !p q. poly p /\ poly q ==> (p * -q = -(p * q))
   poly_neg_mult     |- !r. Ring r ==> !p q. poly p /\ poly q ==> (-(p * q) = -p * q) /\ (-(p * q) = p * -q)
   poly_mult_neg_neg |- !r. Ring r ==> !p q. poly p /\ poly q ==> (-p * -q = p * q)

   Theorems on polynomial distribution with subtraction:
#  poly_mult_rsub   |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> (p * (q - t) = p * q - p * t)
#  poly_mult_lsub   |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> ((p - q) * t = p * t - q * t)
   poly_mult_sub    |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==>
                                      (p * (q - t) = p * q - p * t) /\ ((p - q) * t = p * t - q * t)

   Cross-Multiplication of Polynomials:
   poly_mult_cross  |- !r. Ring r ==> !h k p q. poly (h::p) /\ poly (k::q) ==>
                        ((h::p) * (k::q) = [h * k] + ((h * q) >> 1 + (k * p) >> 1 + ((p * q) >> 1) >> 1))
   poly_cons_eq_add_shift  |- !r. Ring r ==> !h t. poly (h::t) ==> (h::t = [h] + t >> 1)
   poly_snoc_eq_add_shift  |- !r. Ring r ==>
                              !p c. poly p /\ c IN R /\ c <> #0 ==> (SNOC c p = p + [c] >> LENGTH p)
   poly_add_nonzero_const_shift_not_zero
                           |- !r. Ring r ==> !p. poly p ==> !c. c IN R /\ c <> #0 ==> [c] + p >> 1 <> |0|

   Theorems on polynomial degree (rely on poly):
   poly_deg_eq_zero  |- !p. poly p /\ (deg p = 0) ==> (p = |0|) \/ ?h. h IN R /\ h <> #0 /\ (p = [h])
   poly_deg_eq_0     |- !p. poly p ==> (p <> |0| /\ (deg p = 0) <=> ?c. c IN R /\ c <> #0 /\ (p = [c]))
   poly_deg_neg      |- !r. Ring r ==> !p. poly p ==> (deg (-p) = deg p)
   poly_deg_cmult    |- !r. Ring r ==> !p. poly p ==> !c. c IN R ==> deg (c * p) <= deg p
   poly_deg_eq       |- !r. Ring r ==> !p q. poly p /\ poly q /\ (p + q = |0|) ==> (deg p = deg q)
   poly_deg_equal    |- !r. Ring r ==> !p q. poly p /\ poly q /\ zerop (p + q) ==> (deg p = deg q)

   Degree of Polynomial Addition:
   poly_deg_add      |- !r. Ring r ==> !p q. poly p /\ poly q ==> deg (p + q) <= MAX (deg p) (deg q)
   poly_deg_sub      |- !r. Ring r ==> !p q. poly p /\ poly q ==> deg (p - q) <= MAX (deg p) (deg q)

   Degree of Polynomial Multiplication:
   poly_deg_mult     |- !r. Ring r ==> !p q. poly p /\ poly q ==> deg (p * q) <= deg p + deg q

   Polynomial leading coefficient:
#  poly_lead_element  |- !r. Ring r ==> !p. poly p ==> lead p IN R
#  poly_lead_nonzero  |- !p. poly p /\ p <> |0| ==> lead p <> #0
   poly_lead_eq_zero  |- !p. poly p ==> ((lead p = #0) <=> (p = |0|))
   poly_nonzero_lead_nonzero  |- !p. poly p /\ p <> |0| <=> weak p /\ lead p <> #0
   poly_lead_negate   |- !r. Ring r ==> !p. poly p ==> (lead (-p) = -lead p)

   Relationship of Polynomials with weak operations (via lead):
   weak_lead_cmult_nonzero |- !r. Ring r ==> !p c. weak p /\ c IN R /\ c * lead p <> #0 ==> (lead (c * p) = c * lead p)
   weak_deg_cmult_nonzero  |- !r. Ring r ==> !p c. weak p /\ c IN R /\ c * lead p <> #0 ==> (deg (c * p) = deg p)
   poly_weak_cmult_poly    |- !r. Ring r ==> !p. poly p ==> !c. c IN R /\ c * lead p <> #0 ==> poly (c o p)
   poly_weak_cmult         |- !r. Ring r ==> !p. poly p ==> !c. c IN R /\ c * lead p <> #0 ==> (c * p = c o p)
   poly_cmult_eq_zero      |- !r. Ring r ==> !p  poly p ==> !c. c IN R ==> (c * p = |0|) ==> (p = |0|) \/ (c * lead p = #0)

   weak_lead_weak_add      |- !r p q. weak p /\ weak q /\ deg p < deg q ==> (lead (p || q) = lead q)
   weak_lead_weak_mult_nonzero |- !r. Ring r ==> !p q. weak p /\ weak q /\ lead p * lead q <> #0 ==>
                                  (lead (p o q) = lead p * lead q)
   weak_lead_mult_nonzero      |- !r. Ring r ==> !p q. weak p /\ weak q /\ lead p * lead q <> #0 ==>
                                  (lead (p * q) = lead p * lead q)
   weak_deg_mult_nonzero       |- !r. Ring r ==> !p q. weak p /\ weak q /\ lead p * lead q <> #0 ==>
                                  (deg (p * q) = deg p + deg q)
   poly_weak_add_poly |- !r. Ring r ==> !p q. poly p /\ poly q /\ deg p <> deg q ==> poly (p || q)
   poly_weak_add      |- !r. Ring r ==> !p q. poly p /\ poly q /\ deg p <> deg q ==> (p + q = p || q)
   poly_lead_add_less |- !r. Ring r ==> !p q. poly p /\ poly q /\ deg p < deg q ==> (lead (p + q) = lead q)
   poly_lead_add_less_comm
                      |- !r. Ring r ==> !p q. poly p /\ poly q /\ deg q < deg p ==> (lead (p + q) = lead p)
   poly_deg_add_less  |- !r. Ring r ==> !p q. poly p /\ poly q /\ deg p < deg q ==> (deg (p + q) = deg q)
   poly_deg_add_less_comm |- !r. Ring r ==> !p q. poly p /\ poly q /\ deg q < deg p ==> (deg (p + q) = deg p)
   poly_deg_add_deg_zero  |- !r. Ring r ==> !p q. poly p /\ poly q /\ (deg p = 0) ==> (deg (p + q) = deg q)
   poly_lead_sub_less |- !r. Ring r ==> !p q. poly p /\ poly q /\ deg q < deg p ==> (lead (p - q) = lead p)
   poly_deg_sub_less  |- !r. Ring r ==> !p q. poly p /\ poly q /\ deg q < deg p ==> (deg (p - q) = deg p)
   poly_deg_sub_deg_zero  |- !r. Ring r ==> !p q. poly p /\ poly q /\ (deg q = 0) ==> (deg (p - q) = deg p)

   Polynomial Theorems -- CONS theorems and SING theorems:
   poly_mult_cons      |- !r. Ring r ==> !h t q. weak (h::t) /\ weak q ==>
                                          ((h::t) * q = h * q + (t * q) >> 1)
   poly_mult_cons_over |- !r. Ring r ==> !h t q. poly (h::t) /\ poly q ==>
                                          ((h::t) * q = h * q + (t * q) >> 1)
   poly_mult_lconst    |- !r. Ring r ==> !p. poly p ==> !k. k IN R ==> ([k] * p = k * p)
   poly_mult_rconst    |- !r. Ring r ==> !p. poly p ==> !k. k IN R ==> (p * [k] = k * p)

   Polynomial Exponentiation:
#  poly_exp_poly   |- !r. Ring r ==> !p. poly p ==> !n. poly (p ** n)
   poly_exp_suc    |- !r. Ring r ==> !p. poly p ==> !n. p ** SUC n = p ** n * p
#  poly_exp_0      |- !p. p ** 0 = |1|
#  poly_exp_1      |- !r. Ring r ==> !p. poly p ==> (p ** 1 = p)
   poly_exp_2      |- !r. Ring r ==> !p. poly p ==> (p ** 2 = p * p)
   poly_zero_exp   |- !r. Ring r ==> !n. |0| ** n = if n = 0 then |1| else |0|
#  poly_one_exp    |- !r. Ring r ==> !n. |1| ** n = |1|
   poly_neg_exp    |- !r. Ring r ==> !p. poly p ==> !n. -p ** n = if EVEN n then p ** n else -(p ** n)
   poly_exp_add    |- !r. Ring r ==> !p. poly p ==> !n m. p ** (n + m) = p ** n * p ** m
   poly_exp_mult   |- !r. Ring r ==> !p. poly p ==> !m n. p ** (n * m) = (p ** n) ** m
   poly_exp_mult_comm  |- !r. Ring r ==> !p. poly p ==> !m n. (p ** m) ** n = (p ** n) ** m
   poly_mult_exp   |- !r. Ring r ==> !p q. poly p /\ poly q ==> !n. (p * q) ** n = p ** n * q ** n
   poly_cmult_one_exp  |- !r. Ring r ==> !c. c IN R ==> !n. (c * |1|) ** n = c ** n * |1|
   poly_cmult_exp  |- !r. Ring r ==> !c p. c IN R /\ poly p ==> !n. (c * p) ** n = c ** n * p ** n
   poly_exp_const  |- !r. Ring r ==> !c. c IN R ==> !n. [c] ** n = chop [c ** n]
   poly_exp_even   |- !r. Ring r ==> !p. poly p ==> !n. EVEN n ==> (p ** n = (p * p) ** HALF n)
   poly_exp_odd    |- !r. Ring r ==> !p. poly p ==> !n. ODD n ==> (p ** n = p * (p * p) ** HALF n)

   Polynomial Operations applied to Weak:
   poly_add_weak_zero    |- !r p. ( |0| + p = chop p) /\ (p + |0| = chop p)
   poly_cmult_mult_weak  |- !r. Ring r ==> !p q. weak p /\ weak q ==> !c. c IN R ==> (c * p * q = c * (p * q))
   poly_mult_cmult_weak  |- !r. Ring r ==> !p q. weak p /\ weak q ==> !c. c IN R ==> (p * (c * q) = c * p * q)
   poly_cmult_weak       |- !r. Ring r ==> !c p. c IN R /\ weak p ==> (c * p = c * chop p)
   poly_cmult_weak_poly  |- !r. Ring r ==> !c p. c IN R /\ weak p ==> poly (c * p)
   poly_add_weak         |- !r. Ring r ==> !p q. weak p /\ weak q ==> (p + q = chop p + chop q)
   poly_add_weak_left    |- !r. Ring r ==> !p q. weak p /\ weak q ==> (p + q = p + chop q)
   poly_add_weak_right   |- !r. Ring r ==> !p q. weak p /\ weak q ==> (p + q = chop p + q)
   poly_add_weak_poly    |- !r. Ring r ==> !p q. weak p /\ weak q ==> poly (p + q)
   poly_mult_weak        |- !r. Ring r ==> !p q. weak p /\ weak q ==> (p * q = chop p * chop q)
   poly_mult_weak_left   |- !r. Ring r ==> !p q. weak p /\ weak q ==> (p * q = p * chop q)
   poly_mult_weak_right  |- !r. Ring r ==> !p q. weak p /\ weak q ==> (p * q = chop p * q)
   poly_mult_weak_poly   |- !r. Ring r ==> !p q. weak p /\ weak q ==> poly (p * q)
   poly_exp_weak         |- !r. Ring r ==> !p. weak p ==> !n. p ** n = chop p ** n
   poly_exp_weak_poly    |- !r. Ring r ==> !p. weak p ==> !n. poly (p ** n)
   poly_add_weak_comm    |- !r. Ring r ==> !p q. weak p /\ weak q ==> (p + q = q + p)
   poly_add_weak_assoc   |- !r. Ring r ==> !p q t. weak p /\ weak q /\ weak t ==> (p + q + t = p + (q + t))
   poly_mult_weak_comm   |- !r. Ring r ==> !p q. weak p /\ weak q ==> (p * q = q * p)
   poly_mult_weak_assoc  |- !r. Ring r ==> !p q t. weak p /\ weak q /\ weak t ==> (p * q * t = p * (q * t))
   poly_add_weak_const_const  |- !r h k. h IN R /\ k IN R ==> ([h] + [k] = chop [h + k])

   Preparation for Polynomial Division:
   poly_deg_sub_len2    |- !r. Ring r ==> !a b c. poly [a; c] /\ poly [b; c] ==> (deg ([a; c] - [b; c]) = 0)
   poly_deg_eq_lead_sub |- !r. Ring r ==> !p q. poly p /\ poly q /\ (deg p = deg q) /\ (lead p = lead q) /\
                                          0 < deg q ==>  deg (p - q) < deg q

   Polynomial Evaluation (upgrade from polyWeak):
#  poly_eval_element  |- !r. Ring r ==> !p. poly p ==> !x. x IN R ==> eval p x IN R
#  poly_eval_cmult    |- !r. Ring r ==> !p c x.  poly p /\ c IN R /\ x IN R ==> (eval (c * p) x = c * eval p x)
#  poly_eval_neg      |- !r. Ring r ==> !p x. poly p /\ x IN R ==> (eval (-p) x = -eval p x)
#  poly_eval_add      |- !r. Ring r ==> !p q x. poly p /\ poly q /\ x IN R ==> (eval (p + q) x = eval p x + eval q x)
#  poly_eval_sub      |- !r. Ring r ==> !p q x. poly p /\ poly q /\ x IN R ==> (eval (p - q) x = eval p x - eval q x)
#  poly_eval_shift    |- !r. Ring r ==> !p x. poly p /\ x IN R ==> !n. eval (p >> n) x = eval p x * x ** n
#  poly_eval_mult     |- !r. Ring r ==> !p q x. poly p /\ poly q /\ x IN R ==> (eval (p * q) x = eval p x * eval q x)
#  poly_eval_exp      |- !r. Ring r ==> !p x. poly p /\ x IN R ==> !n. eval (p ** n) x = eval p x ** n

   Polynomial Roots:
   poly_root_neg        |- !r. Ring r ==> !p x. x IN R /\ poly p /\ root p x ==> root (-p) x
   poly_root_add        |- !r. Ring r ==> !p q x. x IN R /\ poly p /\ poly q /\
                                                  root p x /\ root q x ==> root (p + q) x
   poly_root_mult       |- !r. Ring r ==> !p q x. x IN R /\ poly p /\ poly q /\ root p x ==> root (p * q) x
   poly_root_mult_comm  |- !r. Ring r ==> !p q x. x IN R /\ poly p /\ poly q /\ root q x ==> root (p * q) x
   poly_nonzero_with_root_deg_pos  |- !r. Ring r ==> !x. x IN R ==>
                                      !p. poly p /\ p <> |0| /\ root p x ==> 0 < deg p

   Polynomial Coefficients:
#  poly_coeff_element   |- !r. Ring r ==> !p. poly p ==> !k. p ' k IN R
   poly_coeff_eq_zero   |- !p. poly p /\ (!k. p ' k = #0) ==> (p = |0|)

   Characteristic of Polynomial Ring:
   poly_one_sum_n      |- !r. Ring r ==> !n. (PolyRing r).sum.exp |1| n = chop [##n]
   poly_ring_char      |- !r. Ring r ==> (char (PolyRing r) = char r)
   poly_neg_char_2     |- !r. Ring r /\ (char r = 2) ==> !p. poly p ==> (-p = p)

   Polynomial Set (truncated by degree):
   weak_poly_finite    |- !r. FINITE R ==> !n. FINITE {p | weak p /\ (LENGTH p = n)}
   weak_poly_card      |- !r. FINITE R ==> !n. CARD {p | weak p /\ (LENGTH p = n)} = CARD R ** n
   weak_poly_poly_bij  |- !r. FINITE R /\ #0 IN R ==>
                          !n. BIJ chop {p | weak p /\ (LENGTH p = n)}
                                       {p | poly p /\ ((p = []) \/ deg p < n)}
   poly_truncated_by_degree        |- !n. 0 < n ==>
                                 ({p | poly p /\ deg p < n} = {p | poly p /\ ((p = []) \/ deg p < n)})
   poly_truncated_by_degree_finite |- !r. FINITE R /\ #0 IN R ==> !n. FINITE {p | poly p /\ deg p < n}

   Other Useful Theorems:
   poly_add_solve_first   |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t /\ (p + q = t) ==> (p = t - q)
   poly_add_solve_second  |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t /\ (p + q = t) ==> (q = t - p)
   poly_lead_mult_unit        |- !r. Ring r ==> !p q. poly p /\ poly q /\ unit (lead p) ==>
                                       (lead (p * q) = lead p * lead q)
   poly_lead_mult_unit_comm   |- !r. Ring r ==> !p q. poly p /\ poly q /\ unit (lead q) ==>
                                       (lead (p * q) = lead p * lead q)
   poly_deg_mult_unit         |- !r. Ring r ==> !p q.  poly p /\ poly q /\ unit (lead p) /\
                                       lead q <> #0 ==> (deg (p * q) = deg p + deg q)
   poly_deg_mult_unit_comm    |- !r. Ring r ==> !p q. poly p /\ poly q /\ lead p <> #0 /\
                                       unit (lead q) ==> (deg (p * q) = deg p + deg q)

   Polynomial as scalar multiple of an ring unit:
   poly_cmult_unit        |- !r p c. Ring r /\ poly p /\ c IN R /\ unit c ==> (p = [c] * ( |/ c * p))
   poly_cmult_unit_comm   |- !r p c. Ring r /\ poly p /\ c IN R /\ unit c ==> (p = |/ c * p * [c])
   poly_cmult_unit_eqn    |- !r p c. Ring r /\ poly p /\ c IN R /\ unit c ==> (p = |/ c * p * [c] + |0|)

*)
(* ------------------------------------------------------------------------- *)
(* Polynomials over a Ring.                                                  *)
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
Scalar multiplication can split to case of zerop scalar or non-zero scalar: #0 * p = |0|, c * p <> |0| if c <> #0.
Negation of a polynomial never needs normalization.
Shifting of a polynomial never needs normalization.
Multiplication of polynomials is defined by addition of scalar multiplication and product with a shift, each already normalized.
Division of polynomials with remainder is defined by the Division Algorithm.

*)

(* ------------------------------------------------------------------------- *)
(* Polynomials over a Ring.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: poly [] *)
(* Proof: by defintion. *)
val zero_poly_poly = save_thm("zero_poly_poly", Poly_def |> CONJUNCT1);
(* > val zero_poly_poly = |- !r. poly [] <=> T : thm *)

(* definition already exported *)
(* val _ = export_rewrites ["zero_poly_poly"]; *)

(* Theorem: poly (h::t) iff h IN R /\ poly t /\ ~ zerop (h::t) *)
(* Proof: by definition. *)
val poly_cons_poly = save_thm("poly_cons_poly", Poly_def |> CONJUNCT2);
(* > val poly_cons_poly = |- !r h t. poly (h::t) <=> h IN R /\ poly t /\ ~zerop (h::t) : thm *)
(*
val poly_cons_poly = save_thm("poly_cons_poly", Poly_def |> CONJUNCT2 |>
                              SPEC_ALL |> #1 o EQ_IMP_RULE |> GEN ``(t: 'a poly)`` |> GEN ``(h:'a)`` |> GEN ``(r:'a ring)``);
*)
(* > val poly_cons_poly = |- !r h t. poly (h::t) ==> h IN R /\ poly t /\ ~zerop (h::t) : thm *)

(* seems we need two-way export for easy-of-use. *)
(* definition already exported *)
(* val _ = export_rewrites ["poly_cons_poly"]; *)

(* Theorem: If poly (h::t), ~zerop (h::t) *)
(* Proof: By definition. *)
val poly_cons_not_zero = store_thm(
  "poly_cons_not_zero",
  ``!h t. poly (h::t) ==> ~ zerop (h::t)``,
  rw[]);

(* Theorem: poly p /\ zerop p ==> p = [] *)
(* Proof: by poly_cons_not_zero. *)
val zero_poly_zero_poly = store_thm(
  "zero_poly_zero_poly",
  ``!p. poly p /\ zerop p ==> (p = [])``,
  metis_tac[Poly_def, list_CASES]);

(* Theorem: poly p ==> (zerop p <=> (p = |0|)) *)
(* Proof:
   If part: poly p /\ zerop p ==> p = |0|
      True by zero_poly_zero_poly, poly_zero.
   Only-if part: poly p /\ p = |0| ==> zerop p
      True since zerop |0| = T by zero_poly_zero
*)
val zero_poly_eq_poly_zero = store_thm(
  "zero_poly_eq_poly_zero",
  ``!p. poly p ==> (zerop p <=> (p = |0|))``,
  rw[EQ_IMP_THM] >>
  metis_tac[zero_poly_zero_poly]);

(* Theorem: poly p /\ p <> [] ==> ~ (zerop p) *)
(* Proof: by zero_poly_zero_poly. *)
val poly_nonzero_nonzero = store_thm(
  "poly_nonzero_nonzero",
  ``!p. poly p /\ p <> [] ==> ~(zerop p)``,
  metis_tac[zero_poly_zero_poly]);

(* Theorem: poly p ==> (p = []) \/ ~(zerop p) *)
(* Proof: by zero_poly_zero_poly. *)
val poly_property = store_thm(
  "poly_property",
  ``!p. poly p ==> (p = []) \/ ~(zerop p) ``,
  metis_tac[zero_poly_zero_poly]);

(* Theorem: nonzero c IN R ==> poly [c] *)
(* Proof: by definition. *)
val poly_nonzero_element_poly = store_thm(
  "poly_nonzero_element_poly",
  ``!c. c IN R /\ c <> #0 <=> poly [c]``,
  rw[]);

(* Theorem: poly (h::t) ==> LAST (h::t) <> #0 *)
(* Proof: by induction on t. *)
val poly_cons_last_nonzero = store_thm(
  "poly_cons_last_nonzero",
  ``!h t. poly (h::t) ==> LAST (h::t) <> #0``,
  Induct_on `t` >>
  rw[]);

(* Theorem: poly (h::t) ==> (t = [] ==> h <> #0) *)
(* Proof: by poly_cons_poly and zero_poly_cons. *)
val poly_cons_property = store_thm(
  "poly_cons_property",
  ``!h t. poly (h::t) ==> ~((h = #0) /\ (t = []))``,
  metis_tac[poly_cons_poly, zero_poly_cons, zero_poly_of_zero]);

(* Theorem: h IN R /\ poly p /\ p <> |0| ==> poly (h::p) *)
(* Proof: by poly_cons_poly, poly_property *)
val poly_nonzero_cons_poly = store_thm(
  "poly_nonzero_cons_poly",
  ``!r:'a ring. !h p. h IN R /\ poly p /\ p <> |0| ==> poly (h::p)``,
  rw[poly_cons_poly] >>
  metis_tac[poly_property]);

(* Theorem: Ring r ==> !p n. poly p /\ p <> |0| ==> poly (PAD_LEFT #0 n p) *)
(* Proof:
   By induction on n.
   Base: poly p /\ p <> |0| ==> poly (PAD_LEFT #0 0 p)
       PAD_LEFT #0 0 p = p          by PAD_LEFT_0
       Thus true.

   Step: poly p ==> poly (PAD_LEFT #0 n p) ==> poly p ==> poly (PAD_LEFT #0 (SUC n) p)
      If LENGTH p <= n,
         Note LENGTH p <> 0                   by LENGTH_NIL, p <> |0|
           so n <> 0                          by LENGTH p <= n
           and PAD_LEFT #0 (SUC n) p
             = #0::PAD_LEFT #0 n p            by PAD_LEFT_CONS
         Since poly (PAD_LEFT #0 n p)         by induction hypothesis
               LENGTH (PAD_LEFT #0 n p)
             = MAX n (LENGTH p)               by PAD_LEFT_LENGTH
             = n <> 0                         by MAX_DEF
          Thus (PAD_LEFT #0 n p) <> |0|       by LENGTH_NIL, poly_zero. [1]
         Hence poly (PAD_LEFT #0 (SUC n) p)   by poly_nonzero_cons_poly
      If ~(LENGTH p <= n),
         Then n < LENGTH p.
           or SUC n <= LENGTH p.
         Thus PAD_LEFT #0 (SUC n) p = p       by PAD_LEFT_ID
         Hence true.
*)
val poly_pad_left_poly = store_thm(
  "poly_pad_left_poly",
  ``!r:'a ring. Ring r ==> !p n. poly p /\ p <> |0| ==> poly (PAD_LEFT #0 n p)``,
  ntac 3 strip_tac >>
  Induct >-
  rw[PAD_LEFT_0] >>
  rpt strip_tac >>
  Cases_on `LENGTH p <= n` >| [
    `PAD_LEFT #0 (SUC n) p = #0::PAD_LEFT #0 n p` by rw[PAD_LEFT_CONS] >>
    `LENGTH (PAD_LEFT #0 n p) = n` by rw[PAD_LEFT_LENGTH, MAX_DEF] >>
    `LENGTH p <> 0` by metis_tac[LENGTH_NIL, poly_zero] >>
    `n <> 0` by decide_tac >>
    `(PAD_LEFT #0 n p) <> |0|` by metis_tac[LENGTH_NIL, poly_zero] >>
    rw[poly_nonzero_cons_poly],
    rw[PAD_LEFT_ID]
  ]);

(* ------------------------------------------------------------------------- *)
(* Useful Theorems.                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: poly |1| *)
(* Proof:
   If #1 = #0,
      |1| = []            by poly_one
      and poly [] = T     by zero_poly_poly
   If #1 <> #0,
      |1| = [#1]          by poly_one
      and poly [#1] = T   by poly_nonzero_element_poly
*)
val poly_one_poly = store_thm(
  "poly_one_poly",
  ``!r:'a ring. Ring r ==> poly |1|``,
  rw[poly_one]);

(* export simple result *)
val _ = export_rewrites ["poly_one_poly"];

(* Theorem: [#1] <> [] *)
(* Proof: by weak_one_ne_zero. *)
val poly_one_ne_zero = save_thm("poly_one_ne_zero", weak_one_ne_zero);
(* > val poly_one_ne_zero = |- [#1] <> [] : thm *)

(* Theorem: #1 <> #0 ==> ( |1| = [#1]) *)
(* Proof:
     |1|
   = if #1 = #0 then [] else [#1]   by poly_one
   = [#1]                           by given
*)
val poly_one_alt = store_thm(
  "poly_one_alt",
  ``!r:'a ring. #1 <> #0 ==> ( |1| = [#1])``,
  rw[poly_one]);;

(* Do not export this, need to keep |1| *)
(* val _ = export_rewrites["poly_one_alt"]; *)

(* Theorem: ~zerop |1| *)
(* Proof: by poly_one. *)
val poly_one_nonzero = store_thm(
  "poly_one_nonzero",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> ~zerop |1|``,
  rw[zero_poly_cons, poly_one]);

(* export simple result *)
val _ = export_rewrites ["poly_one_nonzero"];

(* ------------------------------------------------------------------------- *)
(* Polynomials as weak polynomials.                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: poly p ==> weak p *)
(* Proof: by induction on p.
   Base case: poly [] ==> weak []
      true by zero_poly_poly, weak_of_zero.
   Step case: poly p ==> weak p ==> poly (h::p) ==> weak (h::p)
      true by poly_cons_poly, weak_cons.
*)
val poly_is_weak = store_thm(
  "poly_is_weak",
  ``!p:'a poly. poly p ==> weak p``,
  Induct >>
  rw[]);

val _ = export_rewrites ["poly_is_weak"];

(* Theorem: weak p ==> poly (chop p) *)
(* Proof: by induction on p.
   Base case: weak [] ==> poly (chop [])
      true by poly_chop_of_zero, zero_poly_poly.
   Step case: weak p ==> poly (chop p) ==> weak (h::p) ==> poly (chop (h::p))
      If zerop (h::p),
         then chop (h::p) = []    by zero_poly_chop
         hence poly [] = T        by zero_poly_poly.
      If ~zerop (h::p),
         then poly (chop (h::p))
          <=> poly (h::chop p)     by poly_chop_cons
          <=> h IN R /\ poly (chop p) /\ ~zerop (h::chop p)   by poly_cons_poly

          If zerop p, h <> #0      by zero_poly_cons
          then chop p = []         by zero_poly_chop
          and poly (h::chop p) = poly [h] = T   by poly_nonzero_element_poly
          If ~zerop p,
          ~zerop (chop p)          by zero_poly_eq_zero_poly_chop
          ~zerop (h::chop p)       by zero_poly_cons
          poly (h::chop p) <=> T   by poly_cons_poly, induction hypothesis
*)
val poly_chop_weak_poly = store_thm(
  "poly_chop_weak_poly",
  ``!p:'a poly. weak p ==> poly (chop p)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `zerop (h::p)` >-
  metis_tac[zero_poly_chop, zero_poly_poly] >>
  full_simp_tac std_ss [poly_chop_cons, weak_cons] >>
  Cases_on `zerop p` >-
  metis_tac[poly_nonzero_element_poly, zero_poly_chop, zero_poly_cons] >>
  metis_tac[zero_poly_eq_zero_poly_chop, poly_cons_poly, zero_poly_cons]);

val _ = export_rewrites ["poly_chop_weak_poly"];

(* Theorem: poly p <=> weak p /\ ((p = []) \/ LAST p <> #0) *)
(* Proof: by cases on p, and poly_every_element, poly_cons_last_nonzero.
   Case p = [], to show: poly [] <=> weak [] /\ (([] = []) \/ LAST [] <> #0)
      true by zero_poly_poly, weak_of_zero.
   Case p = h::t, to show: poly (h::t) <=> weak (h::t) /\ ((h::t = []) \/ LAST (h::t) <> #0)
   If part: poly (h::t) ==> weak (h::t) /\ LAST (h::t) <> #0
      true by poly_is_weak, poly_cons_last_nonzero.
   Only-if part: weak (h::t) /\ LAST (h::t) <> #0 ==> poly (h::t)
      by induction on t:
      Base case: weak [h] /\ LAST [h] <> #0 ==> poly [h]
         weak [h] ==> h IN R          by weak_cons
         LAST [h] <> #0 ==> h <> #0   by LAST_CONS
         hence poly [h]               by poly_nonzero_element_poly
      Step case: weak (h::t) /\ LAST (h::t) <> #0 ==> poly (h::t) ==>
                 weak (h::h'::t) /\ LAST (h::h'::t) <> #0 ==> poly (h::h'::t)
         weak (h::h'::t) ==> h IN R /\ weak (h'::t)   by weak_cons
         LAST (h::h'::t) = LAST (h'::t) <> #0         by LAST_CONS
         ~ zerop (h::h'::t)                           by zero_poly_last_zero
         hence poly (h::h'::t)                        by poly_cons_poly
*)
val poly_def_alt = store_thm(
  "poly_def_alt",
  ``!p:'a poly. poly p <=> weak p /\ ((p = |0|) \/ LAST p <> #0)``,
  rw_tac std_ss[poly_zero] >>
  Cases_on `p` >-
  rw[] >>
  rw_tac std_ss[EQ_IMP_THM] >-
  rw_tac std_ss[poly_is_weak] >-
  rw_tac std_ss[poly_cons_last_nonzero] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  Q.SPEC_TAC (`h`, `h`) >>
  Induct_on `t` >-
  rw[] >>
  metis_tac[poly_cons_poly, zero_poly_last_zero, weak_cons, LAST_CONS]);

(* Theorem: poly p ==> EVERY (\c. c IN R) p *)
(* Proof: by induction on p.
   Base case: poly |0| ==> EVERY (\c. c IN R) |0|
      true by EVERY_DEF.
   Step case: poly p ==> EVERY (\c. c IN R) p ==>
              !h. poly (h::p) ==> EVERY (\c. c IN R) (h::p)
      true by EVERY_CONS and induction hypothesis.
*)
val poly_every_element = store_thm(
  "poly_every_element",
  ``!p. poly p ==> EVERY (\c. c IN R) p``,
  Induct >>
  rw[]);

(* Theorem: poly p ==> (!x. MEM x p ==> x IN R) *)
(* Proof: by poly_is_weak, weak_every_mem *)
val poly_every_mem = store_thm(
  "poly_every_mem",
  ``!r:'a ring. !p. poly p ==> (!x. MEM x p ==> x IN R)``,
  metis_tac[poly_is_weak, weak_every_mem]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Normalization.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: poly p ==> chop p = p *)
(* Proof: by induction on p.
   Base case: poly [] ==> (chop [] = [])
      true by poly_chop_of_zero.
   Step case: poly p ==> (chop p = p) ==>
              !h. poly (h::p) ==> (chop (h::p) = h::p)
      poly (h::p) ==> ~ zero (h::p) by poly_cons_poly
      chop (h::p) = h::chop p   by poly_chop_cons
                  = h::p        by induction hypothesis
*)
val poly_chop_poly = store_thm(
  "poly_chop_poly",
  ``!p:'a poly. poly p ==> (chop p = p)``,
  Induct >>
  rw[]);

(* This is a useful equality. *)
val _ = export_rewrites ["poly_chop_poly"];

(* The converse is true with qualification: EVERY (\c. c IN f.carrrier) p *)
(* Theorem: poly p <=> weak p /\ (chop p = p) *)
(* Proof: easy by induction.
   Base case: poly [] <=> weak [] /\ (chop [] = [])
      true by zero_poly_poly, weak_of_zero, poly_chop_of_zero.
   Step case: poly p <=> weak p /\ (chop p = p) ==> poly (h::p) <=> weak (h::p) /\ (chop (h::p) = h::p)
      true by poly_cons_poly, weak_cons, poly_chop_cons.
*)
val poly_chop_eq_poly = store_thm(
  "poly_chop_eq_poly",
  ``!r:'a ring. Ring r ==> !p:'a poly. poly p <=> weak p /\ (chop p = p)``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  rw_tac std_ss[poly_cons_poly, weak_cons, poly_chop_cons, EQ_IMP_THM]);

(* Theorem: #1 <> #0 ==> chop |1| = |1| *)
(* Proof: by poly_chop_poly. *)
val poly_chop_one = store_thm(
  "poly_chop_one",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> (chop |1| = |1|)``,
  rw[]);

(* export simple result *)
val _ = export_rewrites ["poly_chop_one"];

(* ------------------------------------------------------------------------- *)
(* Polynomial Ring.                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: properties of poly_ring *)
(* Proof: by definition. *)
val poly_ring_property = store_thm(
  "poly_ring_property",
  ``!r:'a ring. (!p. poly p <=> p IN (PolyRing r).carrier) /\
               (!p. poly p <=> p IN (PolyRing r).sum.carrier) /\
               (!p. poly p <=> p IN (PolyRing r).prod.carrier) /\
               (!(p q):'a poly. p + q = chop (p || q)) /\
               (!(p q):'a poly. p * q = chop (p o q)) /\
               ( |0| = []) /\ ( |1| = chop [#1])``,
  rw_tac std_ss[poly_ring_def, GSPECIFICATION]);

(* Theorem:  ((PolyRing r).sum.carrier = (PolyRing r).carrier) /\
             ((PolyRing r).prod.carrier = (PolyRing r).carrier) *)
(* Proof: by poly_ring_def *)
val poly_ring_carriers = store_thm(
  "poly_ring_carriers",
  ``!r:'a ring. ((PolyRing r).sum.carrier = (PolyRing r).carrier) /\
               ((PolyRing r).prod.carrier = (PolyRing r).carrier)``,
  rw_tac std_ss[poly_ring_def]);

(* Theorem: poly_ring has polynomials. *)
(* Proof: by definition. *)
val poly_ring_element = store_thm(
  "poly_ring_element",
  ``!r:'a ring. (!p. p IN (PolyRing r).carrier <=> poly p) /\
               (!p. p IN (PolyRing r).sum.carrier <=> poly p) /\
               (!p. p IN (PolyRing r).prod.carrier <=> poly p)``,
  rw_tac std_ss[poly_ring_def, GSPECIFICATION]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Addition.                                                      *)
(* ------------------------------------------------------------------------- *)

(* To show |0| is identity for Group (PolyRing r).sum. *)

(* Theorem: |0| + |0| = |0| *)
(* Proof: by weak_add_zero_zero.
     |0| + |0|
   = chop ( |0| || |0|)   by poly_add_def
   = chop ( |0|)          by weak_add_zero_zero
   = |0|                  by poly_chop_zero
*)
val poly_add_zero_zero = store_thm(
  "poly_add_zero_zero",
  ``|0| + |0| = |0|``,
  rw[poly_add_def]);

(* Theorem: |0| + p = p. *)
(* Proof: by weak_add_lzero.
     |0| + p
   = chop ( |0| || p)   by poly_add_def
   = chop (p)           by weak_add_lzero
   = p                  by poly_chop_poly
*)
val poly_add_lzero = store_thm(
  "poly_add_lzero",
  ``!p:'a poly. poly p ==> ( |0| + p = p)``,
  rw[poly_add_def]);

(* Theorem: p + |0| = p. *)
(* Proof: by weak_add_rzero.
     p + |0|
   = chop (p || |0|)    by poly_add_def
   = chop (p)           by weak_add_rzero
   = p                  by poly_chop_poly
*)
val poly_add_rzero = store_thm(
  "poly_add_rzero",
  ``!p:'a poly. poly p ==> (p + |0| = p)``,
  rw[poly_add_def]);

val _ = export_rewrites ["poly_add_zero_zero", "poly_add_lzero", "poly_add_rzero"];

(*
val poly_add_zero = save_thm("poly_add_zero", CONJ poly_add_lzero poly_add_rzero);
> val poly_add_zero =
    |- (!p. poly p ==> ([] + p = p)) /\ !p. poly p ==> (p + [] = p) : thm
*)
val poly_add_zero = save_thm("poly_add_zero",
    (CONJ (poly_add_lzero |> SPEC_ALL |> UNDISCH)
          (poly_add_rzero |> SPEC_ALL |> UNDISCH)) |> DISCH_ALL |> GEN_ALL);
(* > val poly_add_zero = |- !r p. poly p ==> ( |0| + p = p) /\ (p + |0| = p) : thm *)

(* To show closure for Group (PolyRing r).sum. *)

(* Theorem: poly (p + q) *)
(* Proof: by definition, and poly_chop_is_poly and poly_is_weak.
       poly (p + q)
   <=> poly (chop (p || q))    by poly_add_def
   <== weak (p || q)           by poly_chop_weak_poly
   <== T                       by weak_add_weak, poly_is_weak
*)
val poly_add_poly = store_thm(
  "poly_add_poly",
  ``!r:'a ring. Ring r ==> !p q:'a poly. poly p /\ poly q ==> poly (p + q)``,
  rw_tac std_ss[poly_add_def, poly_chop_weak_poly, weak_add_weak, poly_is_weak]);

val _ = export_rewrites ["poly_add_poly"];

(* ------------------------------------------------------------------------- *)
(* Polynomial addition is commutative.                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: p + q = q + p. *)
(* Proof:
     p + q
   = chop (p || q)    by poly_add_def
   = chop (q || p)    by weak_add_comm
   = q + p            by poly_add_def
*)
val poly_add_comm = store_thm(
  "poly_add_comm",
  ``!r:'a ring. Ring r ==> !p q:'a poly. poly p /\ poly q ==> (p + q = q + p)``,
  rw_tac std_ss[poly_add_def, weak_add_comm, poly_is_weak]);

(* no export of commutativity. *)
(* val _ = export_rewrites ["poly_add_comm"]; *)

(* ------------------------------------------------------------------------- *)
(* Polynomial addition is associative.                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: p + q + t = p + (q + t) *)
(* Proof:
     p + q + t
   = chop (chop (p || q) || t)   by poly_add_def
   = chop (p || q || t)          by poly_chop_add
   = chop (p ||(q || t))         by weak_add_assoc
   = chop (p || chop (q || t))   by poly_chop_add_comm
   = p + (q + t)                 by poly_add_def
*)
val poly_add_assoc = store_thm(
  "poly_add_assoc",
  ``!r:'a ring. Ring r ==> !p q t:'a poly. poly p /\ poly q /\ poly t ==> (p + q + t = p + (q + t))``,
  rpt strip_tac >>
  `weak p /\ weak q /\ weak t /\ weak (p || q) /\ weak (q || t)` by rw_tac std_ss[poly_is_weak, weak_add_weak] >>
  `chop (p || q || t) = chop (p ||(q || t))` by rw_tac std_ss[weak_add_assoc] >>
  metis_tac[poly_add_def, poly_chop_add, poly_chop_add_comm]);

(* no export of associativity. *)
(* val _ = export_rewrites ["poly_add_assoc"]; *)

(* Theorem: Polynomial addition clauses. *)
(* Proof: by poly_add_lzero, poly_add_rzero, poly_add_com, poly_add_assoc. *)
val poly_add_clauses = store_thm(
  "poly_add_clauses",
  ``!r:'a ring. Ring r ==> !p q t:'a poly. poly p /\ poly q /\ poly t ==>
   ( |0| + p = p) /\ (p + |0| = p) /\ (p + q = q + p) /\ (p + q + t = p + (q + t))``,
  rw_tac std_ss[poly_add_lzero, poly_add_rzero, poly_add_comm, poly_add_assoc]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Negation (as inverse of polynomial addition).                  *)
(* ------------------------------------------------------------------------- *)

(* To show additive inverse for Group (PolyRing r).sum. *)

(* Theorem: poly p ==> poly (neg p) *)
(* Proof: by weak_neg_weak and poly_chop_neg.
     poly (neg p)
   = weak (neg p) /\ chop (neg p) = neg p        by poly_chop_eq_poly
   = T            /\ chop (neg p) = neg p        by weak_neg_weak
   = T            /\ neg (chop p) = neg p        by poly_chop_neg
   = T            /\ T                           by poly_chop_poly (or poly_chop_eq_poly)
*)
val poly_negate_poly = store_thm(
  "poly_negate_poly",
  ``!r:'a ring. Ring r ==> !p:'a poly. poly p ==> poly (neg p)``,
  rw[poly_chop_eq_poly]);

(* Theorem: neg p + p = |0| *)
(* Proof: by weak_add_lneg and zero_poly_chop.
     neg p + p
   = chop (neg p || p)   by poly_add_def
   = chop (zerop)        by weak_add_lneg
   = []                  by zero_poly_chop
   = |0|                 by poly_zero
*)
val poly_add_lnegate = store_thm(
  "poly_add_lnegate",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (neg p + p = |0|)``,
  rw_tac std_ss[poly_add_def, weak_add_lneg, GSYM zero_poly_chop, poly_zero, poly_is_weak]);
(* Q: why srw_tac stalls? *)

(* Theorem: p + neg p = |0| *)
(* Proof: by poly_add_lnegate and poly_add_comm.
     p + neg p
   = neg p + p    by poly_add_comm, poly_negate_poly
   = |0|          by poly_add_lnegate
*)
val poly_add_rnegate = store_thm(
  "poly_add_rnegate",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (p + neg p = |0|)``,
  metis_tac[poly_add_lnegate, poly_add_comm, poly_negate_poly]);
(* Q: Why rw_tac std_ss[poly_add_lneg, poly_add_comm, poly_negate_poly] is not working here? *)

(* ------------------------------------------------------------------------- *)
(* Polynomial Additions form a Group.                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Polynomial additions form a group. *)
(* Proof:
   Closure: by poly_add_poly.
   Associativity: by poly_add_assoc.
   Identity: by poly_add_lzero.
   Inverse: by poly_add_lnegate, poly_negate_poly.
*)
val poly_add_group = store_thm(
  "poly_add_group",
  ``!r:'a ring. Ring r ==> Group (PolyRing r).sum``,
  rw_tac std_ss[group_def_alt, poly_ring_element] >-
  rw[] >-
  rw[poly_add_assoc] >-
  rw[] >-
  rw[] >>
  metis_tac[poly_add_lnegate, poly_negate_poly]);

(* Theorem: Polynomial additions form an abelian group. *)
(* Proof:
   Polynomial additions form a group by poly_add_group.
   Commutativity: by poly_add_comm.
*)
val poly_add_abelian_group = store_thm(
  "poly_add_abelian_group",
  ``!r:'a ring. Ring r ==> AbelianGroup (PolyRing r).sum``,
  rw_tac std_ss[AbelianGroup_def, poly_add_group, poly_ring_element, poly_add_comm]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Multiplication (just for Monoid (PolyRing r).prod).            *)
(* ------------------------------------------------------------------------- *)

(* To show multiplicative identity for Monoid (PolyRing r).prod. *)

(* This one also needs |0| = [] due to poly_mult_lzero. *)

(* Theorem: [c] * p = (chop [c]) * p *)
(* Proof:
     [c] * p
   = chop ([c] o p)          by poly_mult_def
   = chop ((chop [c]) o p)   by poly_chop_mult, weak_const
   = (chop [c]) * p          by poly_mult_def
*)
val poly_mult_const = store_thm(
  "poly_mult_const",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !c. c IN R ==> ([c] * p = (chop [c]) * p)``,
  rw[poly_mult_def]);

(* Theorem: p * [c] = p * (chop [c]) *)
(* Proof:
     p * [c]
   = chop (p o [c])          by poly_mult_def
   = chop (p o (chop [c]))   by poly_chop_mult_comm, weak_const
   = p * (chop [c])          by poly_mult_def
*)
val poly_mult_const_comm = store_thm(
  "poly_mult_const_comm",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !c. c IN R ==> (p * [c] = p * (chop [c]))``,
  rw[poly_mult_def]);

(* Note:
In R[x], chop [#1] may not be [#1], but  (chop [#1]) * p = [#1] * p = p * [#1] = p * (chop [#1])
If R = trivial ring with #1 = #0, then R[x] has all p = [].
*)

(* Theorem: Ring r ==> !h k. h IN R /\ k IN R ==> (chop [h] * chop [k] = chop [h * k]) *)
(* Proof:
   Note weak [h] and weak [k]      by weak_const
     chop [h] * chop [k]
   = chop (chop [h] o chop [k])    by poly_mult_def
   = chop ([h] o [k])              by poly_chop_mult_chop
   = chop (h o [k])                by weak_mult_const_const
   = chop [h * k]                  by weak_cmult_const
*)
val poly_mult_const_const = store_thm(
  "poly_mult_const_const",
  ``!r:'a ring. Ring r ==> !h k. h IN R /\ k IN R ==> (chop [h] * chop [k] = chop [h * k])``,
  rpt strip_tac >>
  `chop [h] * chop [k] = chop (chop [h] o chop [k])` by rw_tac std_ss[poly_mult_def] >>
  `_ = chop ([h] o [k])` by rw_tac std_ss[poly_chop_mult_chop, weak_const] >>
  rw_tac std_ss[weak_mult_const_const, weak_cmult_const]);

(* Better version of previous poly_mult_const *)

(* Theorem: |1| * p = p *)
(* Proof:
     |1| * p
   = chop ( |1| o p)       by poly_mult_def
   = chop (chop [#1] o p) by poly_ring_ids
   = chop ([#1] o p)      by poly_chop_mult
   = chop p               by weak_mult_lone
   = p                    by poly_chop_poly
*)
Theorem poly_mult_lone[simp]:
  !r:'a ring. Ring r ==> !p. poly p ==> ( |1| * p = p)
Proof
  metis_tac[weak_one, poly_is_weak, poly_mult_def, poly_ring_ids,
            poly_chop_mult, weak_mult_lone, poly_chop_poly]
QED

(* Here, we don't have poly_mult_comm. *)

(* Theorem: p * |1| = p *)
(* Proof:
     p * |1|
   = chop (p o |1|)       by poly_mult_def
   = chop (p o chop [#1]) by poly_ring_ids
   = chop (p o [#1])      by poly_chop_mult_comm
   = chop p               by weak_mult_rone
   = p                    by poly_chop_poly
*)
Theorem poly_mult_rone[simp]:
  !r:'a ring. Ring r ==> !p. poly p ==> (p * |1| = p)
Proof
  metis_tac[weak_one, poly_is_weak, poly_mult_def, poly_ring_ids,
            poly_chop_mult_comm, weak_mult_rone, poly_chop_poly]
QED

(* val poly_mult_one = save_thm("poly_mult_one", CONJ poly_mult_lone poly_mult_rone); *)
(* > val poly_mult_one = |- (!r. Ring r ==> !p. poly p ==> ( |1| * p = p)) /\ !r. Ring r ==> !p. poly p ==> (p * |1| = p) : thm *)

(* Theorem: |1| * p = p  and  p * |1| = p *)
(* Proof: combine poly_mult_lone and poly_mult_rone. *)
Theorem poly_mult_one:
  !r:'a ring. Ring r ==> !p. poly p ==> ( |1| * p = p) /\ (p * |1| = p)
Proof rw[]
QED

(* To show closure for Monoid (PolyRing r).prod. *)

(* Theorem: poly p /\ poly q ==> poly (p * q) *)
(* Proof:
       poly (p * q)
   <=> poly (chop (p o q))  by poly_mult_def
   <=> T                    by poly_chop_weak_poly, weak_mult_weak
*)
val poly_mult_poly = store_thm(
  "poly_mult_poly",
  ``!r:'a ring. Ring r ==> !p q:'a poly. poly p /\ poly q ==> poly (p * q)``,
  rw_tac std_ss[poly_mult_def, poly_is_weak, weak_mult_weak, poly_chop_weak_poly]);

val _ = export_rewrites ["poly_mult_poly"];

(* Theorem: p * q = q * p. *)
(* Proof:
     p * q
   = chop (p o q)    by poly_mult_def
   = chop (q o p)    by weak_mult_comm
   = q * p           by poly_mult_def
*)
val poly_mult_comm = store_thm(
  "poly_mult_comm",
  ``!r:'a ring. Ring r ==> !p q:'a poly. poly p /\ poly q ==> (p * q = q * p)``,
  rw_tac std_ss[weak_mult_comm, poly_is_weak, poly_mult_def]);

(* no export of commutativity. *)
(* val _ = export_rewrites ["poly_mult_comm"]; *)

(* ------------------------------------------------------------------------- *)
(* Associativity of polynomial multiplication.                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: p * q * t = p * (q * t). *)
(* Proof:
     p * q * t
   = chop (chop (p o q) o t)     by poly_mult_def
   = chop ((p o q) o t)          by poly_chop_mult
   = chop (p o (q o t))          by weak_mult_assoc
   = chop (p o chop (q o t))     by poly_chop_mult_comm
   = p * (q * t)                 by poly_mult_def
*)
val poly_mult_assoc = store_thm(
  "poly_mult_assoc",
  ``!r:'a ring. Ring r ==> !p q t:'a poly. poly p /\ poly q /\ poly t ==> (p * q * t = p * (q * t))``,
  rpt strip_tac >>
  `weak p /\ weak q /\ weak t /\ weak (p o q) /\ weak (q o t)` by rw[] >>
  rw_tac std_ss[GSYM poly_chop_mult_comm, GSYM poly_chop_mult, weak_mult_assoc, poly_mult_def]);

(* no export of associativity *)
(* val _ = export_rewrites ["poly_mult_assoc"]; *)

(* ------------------------------------------------------------------------- *)
(* Polynomial Multiplications form a Monoid.                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Polynomial multiplications form a monoid. *)
(* Proof:
   Closure: by poly_mult_poly.
   Associativity: by poly_mult_assoc.
   Identity: by poly_mult_lone and poly_mult_rone.
*)
val poly_mult_monoid = store_thm(
  "poly_mult_monoid",
  ``!r:'a ring. Ring r ==> Monoid (PolyRing r).prod``,
  rw_tac std_ss[Monoid_def, poly_ring_element] >> rw[poly_mult_assoc]);

(* Theorem: The polynomial multiplication monoid is abelian. *)
(* Proof:
   Polynomial multiplications form a monoid by poly_mult_monoid.
   Commutativity: given by poly_mult_comm.
*)
val poly_mult_abelian_monoid = store_thm(
  "poly_mult_abelian_monoid",
  ``!r:'a ring. Ring r ==> AbelianMonoid (PolyRing r).prod``,
  rw_tac std_ss[AbelianMonoid_def, poly_mult_monoid, poly_ring_element, poly_mult_comm]);

(* ------------------------------------------------------------------------- *)
(* Theorems on polynomial multiplication distributes over addition.          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: p * (q + t) = p * q + p * t *)
(* Proof:
     p * (q + t)
   = chop (p o (q + t))                    by poly_mult_def
   = chop (p o chop (q || t))              by poly_add_def
   = chop (p o (q || t))                   by poly_chop_mult_comm
   = chop (p o q || p o t)                 by weak_mult_radd
   = chop (chop (p o q) || chop (p o t))   by poly_chop_add_chop
   = chop (p * q || p * t)                 by poly_mult_def
   = p * q + p * t                         by poly_add_def
*)
val poly_mult_radd = store_thm(
  "poly_mult_radd",
  ``!r:'a ring. Ring r ==> !p q t:'a poly. poly p /\ poly q /\ poly t ==> (p * (q + t) = p * q  + p * t)``,
  rpt strip_tac >>
  `weak p /\ weak q /\ weak t /\ weak (p o q) /\ weak (p o t) /\ weak (q || t)` by rw[] >>
  `chop (p o chop (q || t)) = chop (chop (p o q) || chop (p o t))`
    by rw_tac std_ss[poly_chop_mult_comm, GSYM weak_mult_radd, GSYM poly_chop_add_chop] >>
  rw_tac std_ss[poly_mult_def, poly_add_def]);

(* Theorem: (p + q) * t = p * t + q * t *)
(* Proof: by poly_mult_comm and poly_mult_radd.
     (p + q) * t
   = t * (p + q)        by poly_mult_comm
   = t * p + t * q      by poly_mult_radd
   = p * t + q * t      by poly_mult_comm
*)
val poly_mult_ladd = store_thm(
  "poly_mult_ladd",
  ``!r:'a ring. Ring r ==> !p q t:'a poly. poly p /\ poly q /\ poly t ==> ((p + q) * t = p * t + q * t)``,
  rw[poly_mult_radd, poly_mult_comm]);

val _ = export_rewrites ["poly_mult_radd", "poly_mult_ladd"];

(* Theorem: p * (q + t) = p * q + p * t /\ (p + q) * t = p * t + q * t *)
(* Proof: by poly_mult_radd and poly_mult_ladd. *)
val poly_mult_add = save_thm("poly_mult_add",
    CONJ (poly_mult_ladd |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH)
         (poly_mult_radd |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH)
         |> DISCH ``poly p /\ poly q /\ poly t`` |> GEN ``(t:'a poly)`` |> GEN ``(q:'a poly)`` |> GEN ``(p:'a poly)``
         |> DISCH_ALL |> GEN_ALL);
(* > val poly_mult_add = |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==>
                                           ((p + q) * t = p * t + q * t) /\ (p * (q + t) = p * q + p * t) : thm *)

(* ------------------------------------------------------------------------- *)
(* Polynomials with Addition and Multiplication R[x] form a Ring.            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: polynomial additions and multiplications form a ring *)
(* Proof: by checking ring definition.
   Polynomial addition is an abelian group, by poly_add_abelian_group.
   Polynomial multiplication is an abelian monoid, by poly_mult_abelian_monoid.
   Polynomial addition is defined for all Polynomials, by group_poly_add_def.
*)
val poly_add_mult_ring = store_thm(
  "poly_add_mult_ring",
  ``!r:'a ring. Ring r ==> Ring (PolyRing r)``,
  rpt strip_tac >>
  rw_tac std_ss[Ring_def, poly_ring_element] >-
  rw_tac std_ss[poly_add_abelian_group] >-
  rw_tac std_ss[poly_mult_abelian_monoid] >-
  rw_tac std_ss[poly_ring_def] >-
  rw_tac std_ss[poly_ring_def] >>
  rw_tac std_ss[poly_mult_radd]);

(* Theorem: Ring r ==> Ring (PolyRing r) *)
val poly_ring_ring = save_thm("poly_ring_ring", poly_add_mult_ring);
(* val poly_ring_ring = |- !r. Ring r ==> Ring (PolyRing r): thm *)

(* ------------------------------------------------------------------------- *)
(* Lifting Ring Theorems to Polynomial Ring                                  *)
(* ------------------------------------------------------------------------- *)

(* Lifting Ring Theorem to Polynomial theorems:
   from: !r:'a ring. Ring r ==> ...
     to: !r:'a ring. Ring r ==>
    via: Ring r ==> Ring (PolyRing r)
*)
local
val pamr = poly_add_mult_ring |> SPEC_ALL |> UNDISCH
in
fun lift_ring_thm rsuffix psuffix = let
   val rth = DB.fetch "ring" ("ring_" ^ rsuffix)
   val rth' = rth |> ISPEC ``(PolyRing r)`` |> UNDISCH
in
   save_thm("poly_" ^ psuffix, rth' |> PROVE_HYP pamr |> DISCH_ALL |> GEN_ALL)
end
end; (* local *)

(* Lift Ring Theorem with goal *)
local
val pamr = poly_add_mult_ring |> SPEC_ALL |> UNDISCH
in
fun lift_ring_thm_with_goal rsuffix psuffix goal = let
   val rth = DB.fetch "ring" ("ring_" ^ rsuffix)
   val rth' = rth |> ISPEC ``(PolyRing r)`` |> REWRITE_RULE [poly_ring_property]
   val rth'' = rth' |> UNDISCH |> PROVE_HYP pamr |> DISCH_ALL |> GEN_ALL
in
   store_thm("poly_" ^ psuffix, goal, metis_tac [rth'', poly_ring_property])
end
end; (* local *)

(* Lifting Monoid Theorem to Polynomial theorems:
   from: !g:'a monoid. Monoid g ==> ...
     to: !r:'a ring. Ring r ==>
    via: Ring r ==> Monoid (PolyRing r).prod
*)
(*
local
val pmm = poly_mult_monoid |> SPEC_ALL |> UNDISCH
in
fun lift_monoid_thm msuffix psuffix = let
   val mth = DB.fetch "monoid" ("monoid_" ^ msuffix)
   val mth' = mth |> ISPEC ``(PolyRing r).prod`` |> UNDISCH
in
   save_thm("poly_" ^ psuffix, mth' |> PROVE_HYP pmm |> DISCH_ALL |> GEN_ALL)
end
end; *) (* local *)

(* Lift monoid theorem with goal *)
(*
local
val pmm = poly_mult_monoid |> SPEC_ALL |> UNDISCH
in
fun lift_monoid_thm_with_goal msuffix psuffix goal = let
   val mth = DB.fetch "monoid" ("monoid_" ^ msuffix)
   val mth' = mth |> ISPEC ``(PolyRing r).prod`` |> REWRITE_RULE [poly_ring_property]
   val mth'' = mth' |> UNDISCH |> PROVE_HYP pmm |> DISCH_ALL |> GEN_ALL
in
   store_thm("poly_" ^ psuffix, goal, metis_tac [mth'', poly_ring_property])
end
end; *) (* local *)

(* Theorem: Ring r ==> |1| * |1| = |1| *)
val poly_mult_one_one = lift_ring_thm "mult_one_one" "mult_one_one";
(* > val poly_mult_one_one = |- !r. Ring r ==> ( |1| * |1| = |1|) : thm *)

val _ = export_rewrites ["poly_mult_one_one"];

(* Theorem: Ring r ==> ( |1| = |0| <=> !p. poly p ==> p = |0| *)
(* Proof:
   val poly_one_eq_zero = lift_ring_thm "one_eq_zero" "one_eq_zero";
   > val poly_one_eq_zero = |- !r. Ring r ==> (( |1| = |0|) <=> ((PolyRing r).carrier = {|0|})) : thm
   by above and improve:
   If part: |1| = |0| <=> !p. poly p ==> p = |0|
          (PolyRing r).carrier = {|0|})
      <=> !p. poly p ==> p = |0|               by poly_ring_property, IN_SING
   Only-if part: !p. poly p ==> p = |0| ==> |1| = |0|
      Put p = |1| and note that poly |1| = T   by poly_one_poly
*)
(* Need rebind as lift_ring_thm stores the name poly_one_eq_zero. *)
Theorem poly_one_eq_zero[allow_rebind]:
  !r:'a ring. Ring r ==> (( |1| = |0|) <=> !p. poly p ==> (p = |0|))
Proof
  rpt strip_tac >>
  assume_tac (lift_ring_thm "one_eq_zero" "one_eq_zero") >>
  rw_tac std_ss[EQ_IMP_THM] >-
  metis_tac[poly_ring_property, IN_SING] >>
  metis_tac[poly_one_poly]
QED

(* Theorem: Ring r ==> ( |0| = |1|) <=> (#0 = #1) *)
(* Proof:
   by poly_zero, poly_one.
*)
val poly_zero_eq_one = store_thm(
  "poly_zero_eq_one",
  ``!r:'a ring. Ring r ==> (( |0| = |1|) <=> (#0 = #1))``,
  rw[poly_one]);

(* This is the same as poly_one_eq_poly_zero:
   |- !r. Ring r ==> ( |1| = |0| <=> #1 = #0)
*)

(* Theorem: Ring r ==> ((#1 = #0) <=> (!p. poly p ==> (p = |0|))) *)
(* Proof:
       #1 = #0
   <=> (|1| = |0|)                  by poly_zero_eq_one
   <=> !p. poly p ==> (p = |0|)     by poly_one_eq_zero
*)
val poly_zero_all_poly = store_thm(
  "poly_zero_all_poly",
  ``!r:'a ring. Ring r ==> ((#1 = #0) <=> (!p. poly p ==> (p = |0|)))``,
  metis_tac[poly_zero_eq_one, poly_one_eq_zero]);

(* Theorem: poly p /\ 0 < deg p ==> #1 <> #0 *)
(* Proof:
   By contradiction, suppose #1 = #0.
   Then |1| = |0|         by poly_one_eq_poly_zero
     so p = |0|           by poly_one_eq_zero
     or deg p = 0         by poly_deg_zero
     which contradicts 0 < deg p.
*)
val poly_deg_pos_ring_one_ne_zero = store_thm(
  "poly_deg_pos_ring_one_ne_zero",
  ``!r:'a ring. Ring r ==> !p. poly p /\ 0 < deg p ==> #1 <> #0``,
  metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero, poly_deg_pos_nonzero]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Scalar Multiplication.                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: c * |0| = |0|  *)
(* Proof:
     c * |0|
   = c * []          by poly_zero
   = chop (c o [])   by poly_cmult_def
   = chop []         by weak_cmult_of_zero
   = []              by poly_chop_of_zero
   = |0|             by poly_zero
*)
val poly_cmult_zero = store_thm(
  "poly_cmult_zero",
  ``!c. c * |0| = |0|``,
  rw[poly_cmult_def]);

val _ = export_rewrites ["poly_cmult_zero"];

(* Theorem: c * [] = [] *)
(* Proof:
    c * []
   = c * |0|     by poly_zero
   = |0|         by poly_cmult_zero
   = []          by poly_zero
*)
val poly_cmult_of_zero = store_thm(
  "poly_cmult_of_zero",
  ``!c:'a. c * [] = []``,
  metis_tac[poly_cmult_zero, poly_zero]);

(* Theorem: poly p ==> #0 * p = |0|  *)
(* Proof:
     #0 * p
   = chop (#0 o p)    by poly_cmult_def
   = chop (zerop)     by weak_cmult_lzero
   = []               by zero_poly_chop
   = |0|              by poly_zero
*)
val poly_cmult_lzero = store_thm(
  "poly_cmult_lzero",
  ``!r:'a ring. Ring r ==> !p:'a poly. poly p ==> (#0 * p = |0|)``,
  rw_tac std_ss[poly_cmult_def, weak_cmult_lzero, GSYM zero_poly_chop, poly_is_weak, poly_zero]);
 (* Q: Why srw_tac stalls *)

val _ = export_rewrites ["poly_cmult_lzero"];

(* Theorem: poly (c * p) *)
(* Proof: by poly_cmult_def, poly_chop_weak_poly, and weak_cmult_weak.
       poly (c * p)
   <=> poly (chop (c o p))        by poly_cmult_def
   <== weak (c * p)               by poly_chop_weak_poly
   <=> T                          by weak_cmult_weak
*)
val poly_cmult_poly = store_thm(
  "poly_cmult_poly",
  ``!r:'a ring. Ring r ==> !p. poly p  ==> !c. c IN R ==> poly (c * p)``,
  rw_tac std_ss[poly_cmult_def, poly_chop_weak_poly, poly_is_weak, weak_cmult_weak]);

val _ = export_rewrites ["poly_cmult_poly"];

(* Theorem: c IN R /\ h IN R ==> c * [h] = chop [c * h] *)
(* Proof:
   Since c * h IN R                by ring_mult_element
     c * [h]
   = chop (c o [h])   by poly_cmult_def
   = chop [c * h]     by weak_cmult_const
*)
val poly_cmult_const = store_thm(
  "poly_cmult_const",
  ``!r:'a ring. Ring r ==> !c h. c IN R /\ h IN R ==> (c * [h] = chop [c * h])``,
  rw_tac std_ss[poly_cmult_def, weak_cmult_const]);

(* Theorem: k * h <> #0 ==> k * [h] = [k * h] *)
(* Proof:
   Note poly [k * h]   by poly_nonzero_element_poly
     k * [h]
   = chop (k o [h])    by poly_cmult_def
   = chop ([k * h])    by weak_cmult_const
   = [k * h]           by poly_chop_poly
*)
val poly_cmult_const_nonzero = store_thm(
  "poly_cmult_const_nonzero",
  ``!r:'a ring. !h k:'a. k * h <> #0 ==> (k * [h] = [k * h])``,
  rw[poly_cmult_def]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Addition                                                       *)
(* ------------------------------------------------------------------------- *)

(* Note: it is not true that:  zerop q ==> q || p = p, since length of q can exceed length of p. *)

(* Theorem: zerop q ==> q + p = p *)
(* Proof:
     q + p
   = chop (q || p)        by poly_add_def
   = chop (chop q || p)   by poly_chop_add
   = chop ([] || p)       by zero_poly_chop
   = chop p               by weak_add_of_lzero
   = p                    by poly_chop_poly
*)
val poly_add_lzero_poly = store_thm(
  "poly_add_lzero_poly",
  ``!r:'a ring. Ring r ==> !p q:'a poly. poly p /\ zerop q ==> (q + p = p)``,
  rw_tac std_ss[poly_add_def, poly_chop_add, poly_is_weak, zero_poly_weak, zero_poly_chop, weak_add_of_lzero, poly_chop_poly]);

(* Note: it is not true that:  zerop q ==> p || q = p, since length of q can exceed length of p. *)

(* Theorem: zerop q ==> p + q = p *)
(* Proof:
     p + q
   = chop (p || q)        by poly_add_def
   = chop (p || chop q)   by poly_chop_add_comm
   = chop (p || [])       by zero_poly_chop
   = chop p               by weak_add_of_rzero
   = p                    by poly_chop_poly
*)
val poly_add_rzero_poly = store_thm(
  "poly_add_rzero_poly",
  ``!r:'a ring. Ring r ==> !p q:'a poly. poly p /\ zerop q ==> (p + q = p)``,
  rw_tac std_ss[poly_add_def, poly_chop_add_comm, poly_is_weak, zero_poly_weak, zero_poly_chop, weak_add_of_rzero, poly_chop_poly]);

val _ = export_rewrites ["poly_add_lzero_poly", "poly_add_rzero_poly"];

(* Theorem: Ring r ==> !h k. h IN R /\ k IN R ==> (chop [h] + chop [k] = chop [h + k]) *)
(* Proof:
   If h = #0,
      If k = #0,
         chop [#0] + chop [#0]
       = |0| + |0|                 by poly_chop_const_zero
       = |0|                       by poly_add_zero_zero
       = chop [#0]                 by poly_chop_const_zero
       = chop [#0 + #0]            by ring_add_zero_zero
      If k <> #0, poly [k]         by poly_nonzero_element_poly
         chop [#0] + chop [k]
       = |0| + chop [k]            by poly_chop_const_zero, poly_chop_poly
       = chop [k]                  by poly_add_lzero
       = chop [#0 + k]             by ring_add_lzero
   If h <> #0, poly [h]            by poly_nonzero_element_poly
      If k = #0,
         chop [h] + chop [#0]
       = chop [h] + |0|            by poly_chop_const_zero, poly_chop_poly
       = chop [h]                  by poly_add_rzero
       = chop [h + #0]             by ring_add_rzero
      If k <> #0, poly [k]         by poly_nonzero_element_poly
         chop [h] + chop [k]
       = [h] + [k]                 by poly_chop_poly
       = chop ([h] || [k])         by poly_add_def
       = chop ([h + k:: [] || [])  by weak_add_cons
       = chop [h + k]              by weak_add_of_zero_zero
*)
val poly_add_const_const = store_thm(
  "poly_add_const_const",
  ``!r:'a ring. Ring r ==> !h k. h IN R /\ k IN R ==> (chop [h] + chop [k] = chop [h + k])``,
  rpt strip_tac >>
  Cases_on `h = #0` >| [
    Cases_on `k = #0` >-
    rw[] >>
    rw[],
    Cases_on `k = #0` >-
    rw[] >>
    `chop [h] + chop [k] = [h] + [k]` by rw[] >>
    rw_tac std_ss[poly_add_def, weak_add_cons, weak_add_of_zero_zero]
  ]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Negation = Inverse of polynomial addition.                     *)
(* ------------------------------------------------------------------------- *)

val _ = overload_on ("numeric_negate", ``(PolyRing r).sum.inv``);

(* Theorem: - p = neg p *)
(* Proof: by uniqueness of inverse in poly_add_group. *)
val poly_neg_def = store_thm(
  "poly_neg_def",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (- p = neg p)``,
  metis_tac[group_linv_unique, poly_add_group, poly_negate_poly, poly_add_lnegate, poly_ring_property]);

(* how about not export this? *)
(* val _ = export_rewrites ["poly_neg_def"]; *)

(* One way:
- show_assums := true;
> val it = () : unit
- weak_neg_of_zero;
> val it =  [] |- !r. neg |0| = |0| : thm
- zero_poly_poly;
> val it =  [] |- !r. poly |0| <=> T : thm
- poly_neg_def;
> val it =  [] |- !r. Ring r ==> !p. poly p ==> (-p = neg p) : thm
- poly_neg_def |> SPEC_ALL |> UNDISCH;
> val it =  [Ring r] |- !p. poly p ==> (-p = neg p) : thm
- poly_neg_def |> SPEC_ALL |> UNDISCH |> SPEC ``|0|``;
> val it =  [Ring r] |- poly |0| ==> (-|0| = neg |0|) : thm
- poly_neg_def |> SPEC_ALL |> UNDISCH |> SPEC ``|0|`` |> REWRITE_RULE [zero_poly_poly];
> val it =  [Ring r] |- -|0| = neg |0| : thm
- poly_neg_def |> SPEC_ALL |> UNDISCH |> SPEC ``|0|`` |> REWRITE_RULE [zero_poly_poly] |> REWRITE_RULE [weak_neg_of_zero];
> val it =  [Ring r] |- -|0| = |0| : thm
- poly_neg_def |> SPEC_ALL |> UNDISCH |> SPEC ``|0|`` |> REWRITE_RULE [zero_poly_poly] |> REWRITE_RULE [weak_neg_of_zero] |> DISCH_ALL |> GEN_ALL;
> val it =  [] |- !r. Ring r ==> (-|0| = |0|) : thm
- show_assums := false;
> val it = () : unit
*)

(* Better way:
> val it = () : unit
- show_assums := true;
> val it = () : unit
- group_inv_id;
> val it =  [] |- !g. Group g ==> ( |/ #e = #e) : thm
- group_inv_id |> ISPEC ``(PolyRing r).sum``;
(* > val it = [] |- Group (PolyRing r).sum ==> (-(PolyRing r).sum.id = (PolyRing r).sum.id) : thm *)
- group_inv_id |> ISPEC ``(PolyRing r).sum`` |> REWRITE_RULE [poly_ring_property];
> val it =  [] |- Group (PolyRing r).sum ==> (-|0| = |0|) : thm
- group_inv_id |> ISPEC ``(PolyRing r).sum`` |> REWRITE_RULE [poly_ring_property] |> UNDISCH;
> val it =  [Group (PolyRing r).sum] |- -|0| = |0| : thm
- poly_add_group |> SPEC_ALL |> UNDISCH;
> val it =  [Ring r] |- Group (PolyRing r).sum : thm
- group_inv_id |> ISPEC ``(PolyRing r).sum`` |> REWRITE_RULE [poly_ring_property] |> UNDISCH |> PROVE_HYP (poly_add_group |> SPEC_ALL |> UNDISCH);
> val it =  [Ring r] |- -|0| = |0| : thm
- group_inv_id |> ISPEC ``(PolyRing r).sum`` |> REWRITE_RULE [poly_ring_property] |> UNDISCH |> PROVE_HYP (poly_add_group |> SPEC_ALL |> UNDISCH) |> DISCH_ALL |> GEN_ALL;
> val it =  [] |- !r. Ring r ==> (-|0| = |0|) : thm
- show_assums := false;
> val it = () : unit
*)

(* Lifting Group Theorem to Polynomial theorems:
   from: !g:'a group. Group g ==> ...
     to: !r:'a ring. Ring r ==>
    via: Ring r ==> Group (PolyRing r).sum
*)
local
val pag = poly_add_group |> SPEC_ALL |> UNDISCH
in
fun lift_group_thm gsuffix psuffix = let
   val gth = DB.fetch "group" ("group_" ^ gsuffix)
   val gth' = gth |> ISPEC ``(PolyRing r).sum`` |> UNDISCH
in
   save_thm("poly_" ^ psuffix, gth' |> PROVE_HYP pag |> DISCH_ALL |> GEN_ALL)
end
end; (* local *)

(* Theorem: - |0| = |0| *)
val poly_neg_zero = lift_group_thm "inv_id" "neg_zero";
(* > val poly_neg_zero = |- !r. Ring r ==> (-|0| = |0|) : thm *)

val _ = export_rewrites ["poly_neg_zero"];

(* Theorem: Ring r ==> -[] = [] *)
(* Proof: by poly_neg_zero, poly_zero. *)
val poly_neg_of_zero = store_thm(
  "poly_neg_of_zero",
  ``!r:'a ring. Ring r ==> (-[] = [])``,
  metis_tac[poly_neg_zero, poly_zero]);

(* export simple result *)
val _ = export_rewrites ["poly_neg_of_zero"];

(* Theorem: - (h::t) = (- h) :: (- t) *)
(* Proof: by weak_neg_cons, poly_neg_def, poly_cons_poly.
     - (h::t)
   = neg (h::t)    by poly_neg_def
   = -h :: neg t   by weak_neg_cons, poly_is_weak
   = -h :: -t      by poly_neg_def, poly t by poly_cons_poly
*)
val poly_neg_cons = store_thm(
  "poly_neg_cons",
  ``!r:'a ring. Ring r ==> !h t. poly (h::t) ==> (-(h::t) = -h::-t)``,
  rw[poly_neg_def]);

val _ = export_rewrites ["poly_neg_cons"];

(* Theorem: Polynomial negation clauses. *)
val poly_neg_clauses = save_thm("poly_neg_clauses",
   CONJ (poly_neg_zero |> SPEC_ALL |> UNDISCH)
        (poly_neg_cons |> SPEC_ALL |> UNDISCH) |> DISCH_ALL |> GEN_ALL);
(* > val poly_neg_clauses = |- !r. Ring r ==> (-|0| = |0|) /\ !h t. poly (h::t) ==> (-(h::t) = -h::-t) : thm *)

(*
- show_assums := true;
> val it = () : unit
- group_inv_element;
> val it =  [] |- !g. Group g ==> !x. x IN G ==> |/ x IN G : thm
- group_inv_element |> ISPEC ``(PolyRing r).sum`` |> UNDISCH;
> val it = [Group (PolyRing r).sum] |- !x. x IN (PolyRing r).sum.carrier ==> -x IN (PolyRing r).sum.carrier : thm
- group_inv_element |> ISPEC ``(PolyRing r).sum`` |> UNDISCH |> PROVE_HYP (poly_add_group |> SPEC_ALL |> UNDISCH);
> val it = [Ring r] |- !x. x IN (PolyRing r).sum.carrier ==> -x IN (PolyRing r).sum.carrier : thm
- poly_ring_element |> SPEC_ALL |> CONJUNCT2 |> CONJUNCT1 |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH;
> val it =  [p IN (PolyRing r).sum.carrier] |- poly p : thm
- poly_ring_element |> SPEC_ALL |> CONJUNCT2 |> CONJUNCT1 |> SPEC ``x:'a poly`` |> #1 o EQ_IMP_RULE |> UNDISCH;
> val it =  [x IN (PolyRing r).sum.carrier] |- poly x : thm

- group_inv_element |> ISPEC ``(PolyRing r).sum`` |> UNDISCH |> PROVE_HYP (poly_add_group |> SPEC_ALL |> UNDISCH) |> SPEC_ALL;
> val it = [Ring r] |- x IN (PolyRing r).sum.carrier ==> -x IN (PolyRing r).sum.carrier : thm

- group_inv_element |> ISPEC ``(PolyRing r).sum`` |> UNDISCH |> PROVE_HYP (poly_add_group |> SPEC_ALL |> UNDISCH) |> SPEC_ALL |> REWRITE_RULE [poly_ring_element |> SPEC_ALL |> CONJUNCT2 |> CONJUNCT1 |> SPEC ``x:'a poly`` |> #1 o EQ_IMP_RULE |> UNDISCH];
> val it = [Ring r] |- x IN (PolyRing r).sum.carrier ==> -x IN (PolyRing r).sum.carrier : thm

- show_assums := false;
> val it = () : unit
*)

(* Lift group theorem with goal *)
local
val pag = poly_add_group |> SPEC_ALL |> UNDISCH
in
fun lift_group_thm_with_goal gsuffix psuffix goal = let
   val gth = DB.fetch "group" ("group_" ^ gsuffix)
   val gth' = gth |> ISPEC ``(PolyRing r).sum`` |> REWRITE_RULE [poly_ring_property]
   val gth'' = gth' |> UNDISCH |> PROVE_HYP pag |> DISCH_ALL |> GEN_ALL
in
   store_thm("poly_" ^ psuffix, goal, metis_tac[gth'', poly_ring_property])
end
end; (* local *)

(* Theorem: poly p ==> poly (- p) *)
val poly_neg_poly = lift_group_thm_with_goal "inv_element" "neg_poly"
   ``!r:'a ring. Ring r ==> !p:'a poly. poly p ==> poly (- p)``;
(* > val poly_neg_poly = |- !r. Ring r ==> !p. poly p ==> poly (-p) : thm *)

val _ = export_rewrites ["poly_neg_poly"];

(* Theorem: - p = |0| iff p = |0| *)
val poly_neg_eq_zero = lift_group_thm_with_goal "inv_eq_id" "neg_eq_zero"
    ``!r:'a ring. Ring r ==> !p. poly p ==> ((- p = |0|) = (p = |0|))``;
(* > val poly_neg_eq_zero = |- !r. Ring r ==> !p. poly p ==> ((-p = |0|) <=> (p = |0|)) : thm *)

(* Theorem: - -p = p *)
val poly_neg_neg = lift_group_thm_with_goal "inv_inv" "neg_neg"
    ``!r:'a ring. Ring r ==> !p:'a poly. poly p ==> (- - p = p)``;
(* > val poly_neg_neg = |- !r. Ring r ==> !p. poly p ==> (--p = p) : thm *)

val _ = export_rewrites ["poly_neg_neg"];

(* Theorem: Ring r ==> !h. h IN R ==> (-[h] = [-h]) *)
(* Proof:
   Since h <> #0, poly [h]     by poly_nonzero_element_poly
     -[h]
   = -h::-[]      by poly_neg_cons
   = -h::[]       by poly_neg_of_zero
   = [-h]
*)
val poly_neg_nonzero = store_thm(
  "poly_neg_nonzero",
  ``!r:'a ring. Ring r ==> !h. h IN R /\ h <> #0 ==> (-[h] = [-h])``,
  rw[]);

(* Theorem: poly p ==> (chop (-p) = - (chop p)) *)
(* Proof:
     chop (- p)
   = chop (neg p)     by poly_neg_def
   = neg (chop p)     by poly_chop_neg;
   = - (chop p)       by poly_neg_def, poly_chop_poly
*)
val poly_chop_negate = store_thm(
  "poly_chop_negate",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (chop (-p) = - (chop p))``,
  rw[poly_chop_neg]);
(* However, this is of little use, as poly p ==> chop p = p, also poly p ==> poly (-p). *)

(*
Note: The following cannot be proved:
g `!r:'a ring. Ring r ==> !p. weak p ==> (chop (-p) = - (chop p))`;
As -p is not well-defined for weak p.
Should have defined:  p - q = p + (neg q).
*)

(* Theorem: Ring r ==> !x. x IN R ==> (chop [-x] = - chop [x]) *)
(* Proof:
   If x = #0,
        chop [-#0]
      = chop [#0]              by ring_neg_zero
      = |0|                    by poly_chop_const_zero
      = - |0|                  by poly_neg_zero
      = - chop [#0]            by poly_chop_const_zero
   If x <> #0,
      -x <> #0                 by ring_neg_eq_zero
      poly [x]                 by poly_nonzero_element_poly
        chop [-x]
      = chop (-[x])            by poly_neg_nonzero
      = - chop [x]             by poly_chop_negate
*)
val poly_neg_const = store_thm(
  "poly_neg_const",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> (chop [-x] = - chop [x])``,
  (rw[] >> rw[]));

(* Theorem: p + q = |0| <=> p = -q *)
val poly_add_eq_zero = lift_group_thm_with_goal "linv_unique" "add_eq_zero"
    ``!r:'a ring. Ring r ==> !p q:'a poly. poly p /\ poly q ==> ((p + q = |0|) = (p = - q))``;
(* > val poly_add_eq_zero = |- !r. Ring r ==> !p q. poly p /\ poly q ==> ((p + q = |0|) <=> (p = -q)) : thm *)

(* Theorem: -p + p = |0| *)
val poly_add_lneg = lift_group_thm_with_goal "linv" "add_lneg"
    ``!r:'a ring. Ring r ==> !p. poly p ==> (-p + p = |0|)``;
(* > val poly_add_lneg = |- !r. Ring r ==> !p. poly p ==> (-p + p = |0|) : thm *)

(* Theorem: p + -p = |0| *)
val poly_add_rneg = lift_group_thm_with_goal "rinv" "add_rneg"
    ``!r:'a ring. Ring r ==> !p. poly p ==> (p + -p = |0|)``;
(* > val poly_add_rneg = |- !r. Ring r ==> !p. poly p ==> (p + -p = |0|) : thm *)

val _ = export_rewrites ["poly_add_lneg", "poly_add_rneg"];

(* Theorem: - (p + q) = - q + - p  *)
val poly_neg_add_comm = lift_group_thm_with_goal "inv_op" "neg_add_comm"
    ``!r:'a ring. Ring r ==> !p q:'a poly. poly p /\ poly q ==> (- (p + q) = -q + -p)``;
(* > val poly_neg_add_comm = |- !r. Ring r ==> !p q. poly p /\ poly q ==> (-(p + q) = -q + -p) : thm *)

(* Theorem: - (p + q) = - p + - q  *)
(* Proof: by poly_neg_add_comm and poly_add_comm. *)
val poly_neg_add = store_thm("poly_neg_add",
    ``!r:'a ring. Ring r ==> !p q:'a poly. poly p /\ poly q ==> (- (p + q) = -p + -q)``,
    rw_tac std_ss[poly_add_comm, GSYM poly_neg_add_comm]);

val _ = export_rewrites ["poly_neg_add"];

(* Theorem: t + p = t + q <=> p = q *)
val poly_add_lcancel = lift_group_thm_with_goal "lcancel" "add_lcancel"
    ``!r:'a ring. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> ((t + p = t + q) <=> (p = q))``;
(* > val poly_add_lcancel = |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> ((t + p = t + q) <=> (p = q)) : thm *)

(* Theorem: p + t = q + t  <=> p = q *)
val poly_add_rcancel = lift_group_thm_with_goal "rcancel" "add_rcancel"
    ``!r:'a ring. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> ((p + t = q + t) <=> (p = q))``;
(* > val poly_add_rcancel = |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> ((p + t = q + t) <=> (p = q)) : thm *)

(* ------------------------------------------------------------------------- *)
(* Polynomial Subtraction.                                                   *)
(* ------------------------------------------------------------------------- *)

(* Subtraction of polynomials *)
val poly_sub_def = Define `poly_sub (r:'a ring) (p:'a poly) (q:'a poly) = p + (- q)`;
val _ = overload_on ("-", ``poly_sub r``);
(* export an identity *)
val _ = export_rewrites ["poly_sub_def"];

(* Theorem: p - q = ring_sub (PolyRing r) p q *)
(* Proof:
     p - q
   = p + -q                      by poly_sub_def
   = ring_sub (PolyRing r) p q   by ring_sub_def
*)
val poly_sub_alt = store_thm(
  "poly_sub_alt",
  ``!(r:'a ring) p q. p - q = ring_sub (PolyRing r) p q``,
  rw[]);

(* Theorem: poly (p - q) *)
(* Proof: by definition and poly_add_poly, poly_neg_poly,
       or by definition and group_op_element, group_inv_element.
*)
val poly_sub_poly = store_thm(
  "poly_sub_poly",
  ``!r:'a ring. Ring r ==> !p q:'a poly. poly p /\ poly q ==> poly (p - q)``,
  rw_tac std_ss[poly_sub_def, poly_add_poly, poly_neg_poly]);

val _ = export_rewrites ["poly_sub_poly"];

(* Theorem: |0| - p = - p  *)
(* Proof:
     |0| - p
   = |0| + - p   by poly_sub_def
   = - p         by poly_add_lzero, poly_neg_poly
*)
val poly_sub_lzero = store_thm(
  "poly_sub_lzero",
  ``!r:'a ring. Ring r ==> !p:'a poly. poly p ==> ( |0| - p  = -p)``,
  rw[]);

(* Theorem: p - |0| = p  *)
(* Proof:
     p - |0|
   = p + - |0|    by poly_sub_def
   = p + |0|      by poly_neg_zero
   = p            by poly_add_rzero
*)
val poly_sub_rzero = store_thm(
  "poly_sub_rzero",
  ``!r:'a ring. Ring r ==> !p:'a poly. poly p ==> (p - |0| = p)``,
  rw[]);

val _ = export_rewrites ["poly_sub_lzero", "poly_sub_rzero"];

(* Theorem: p - q = |0| <=> p = q *)
(* Proof:
       p - q = |0|
   <=> p + -q = |0|   by poly_sub_def
   <=> p = - (-q)     by poly_add_eq_zero
   <=> p = q          by poly_neg_neg
*)
val poly_sub_eq_zero = store_thm(
  "poly_sub_eq_zero",
  ``!r:'a ring. Ring r ==> !p q:'a poly. poly p /\ poly q ==> ((p - q = |0|) = (p = q))``,
  rw_tac std_ss[poly_sub_def, poly_add_eq_zero, poly_neg_neg, poly_neg_poly]);

(* Theorem: poly p ==> p - p = |0| *)
(* Proof: by poly_sub_eq_zero. *)
val poly_sub_eq = store_thm(
  "poly_sub_eq",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (p - p = |0|)``,
  rw[poly_sub_eq_zero]);

(* Theorem: Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> ((t - p = t - q) <=> (p = q)) *)
(* Proof:
   Note poly (-p) /\ poly (-q)   by poly_neg_poly
           t - p = t - q
    <=> t + (-p) = t + (-q)      by poly_sub_def
    <=>       -p = -q            by poly_add_lcancel
    <=>        p = q             by poly_neg_neg
*)
val poly_sub_lcancel = store_thm(
  "poly_sub_lcancel",
  ``!r:'a ring. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> ((t - p = t - q) <=> (p = q))``,
  metis_tac[poly_sub_def, poly_add_lcancel, poly_neg_poly, poly_neg_neg]);

(* Theorem: Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> ((p - t = q - t) <=> (p = q)) *)
(* Proof:
   Note poly (-t)                by poly_neg_poly
           p - t = q - t
    <=> p + (-t) = q + (-t)      by poly_sub_def
    <=>        p = q             by poly_add_rcancel
*)
val poly_sub_rcancel = store_thm(
  "poly_sub_rcancel",
  ``!r:'a ring. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> ((p - t = q - t) <=> (p = q))``,
  rw[poly_add_rcancel]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Addition and Subtraction                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: - (p - q) = q - p  *)
(* Proof:
     - (p - q)
   = - (p + -q)   by poly_sub_def
   = - p + - - q  by poly_neg_add
   = - p + q      by poly_neg_neg
   = q + -p       by poly_add_comm, poly_neg_poly
   = q - p        by poly_sub_def
*)
val poly_neg_sub = store_thm(
  "poly_neg_sub",
  ``!r:'a ring. Ring r ==> !p q:'a poly. poly p /\ poly q ==> (-(p - q) = q - p)``,
  rw[poly_add_comm]);

(* Theorem: p - q = t <=> p = q + t *)
(* Proof: by polynomials
       p - q = t
   <=> p - q + q     = t + q      by poly_add_rcancel
   <=> p + - q + q   = t + q      by poly_sub_def
   <=> p + (- q + q) = t + q      by poly_add_assoc
   <=>      p + |0|  = t + q      by poly_add_lneg
   <=>             p = t + q      by poly_add_rzero
   <=>             p = q + t      by poly_add_comm

   Proof: by group
       p - q = t
   <=> p + - q = t       by poly_sub_def
   <=> p = t + -(- q)    by group_lsolve
   <=> p = t + q         by poly_neg_neg
   <=> p = q + t         by poly_add_comm
*)
val poly_sub_eq_add = store_thm(
  "poly_sub_eq_add",
  ``!r:'a ring. Ring r ==> !p q t:'a poly. poly p /\ poly q /\ poly t ==> ((p - q = t) <=> (p = q + t))``,
  metis_tac[poly_sub_def, group_lsolve, poly_add_comm, poly_add_group, poly_ring_property]);

(* Theorem: if  p + t = q + s <=> p - q = s - t *)
(* Proof: by polynomials
                      p + t = q + s
   <=>    p + t + (-t + -q) = q + s + (-t + -q)
   <=>  p + (t + (-t + -q)) = q + (s + (-t + -q))    by poly_add_assoc
   <=>    p + (t + -t + -q) = q + (s + -t + -q)      by poly_add_assoc
   <=>       p + ( |0| + -q) = q + (-q + (s + -t))   by poly_add_rneg, poly_add_comm
   <=>               p + -q = q + -q + (s + -t)      by poly_add_lzero, poly_add_assoc
   <=>               p + -q = |0| + (s + -t)         by poly_add_rneg
   <=>               p + -q = s + -t                 by poly_add_lzero
   <=>                p - q = s - t                  by poly_sub_def
   Proof: by group
       p + t = q + s
   <=> p = q + s + -t     by group_lsolve
   <=> p = q + (s + -t)   by poly_add_assoc
   <=> p = (s + -t) + q   by poly_add_comm
   <=> p + -q = s + -t    by group_lsolve
   <=> p - q = s - t      by poly_sub_def
*)
val poly_add_eq_sub = store_thm(
  "poly_add_eq_sub",
  ``!r:'a ring. Ring r ==> !p q t s. poly p /\ poly q /\ poly t /\ poly s ==>
        ((p + t = q + s) <=> (p - q = s - t))``,
  rpt strip_tac >>
  `Group (PolyRing r).sum` by rw_tac std_ss[poly_add_group] >>
  `poly (-t) /\ poly (-q)` by rw[] >>
  `(p = q + s + -t) = (p = q + (s + -t))` by rw[poly_add_assoc] >>
  `_ = (p = (s + -t) + q)` by rw_tac std_ss[poly_add_comm, poly_add_poly] >>
  prove_tac[poly_sub_def, group_lsolve, poly_add_poly, poly_add_group, poly_ring_property]);

(* Theorem: p + q - t = p + (q - t) *)
(* Proof: by poly_add_assoc, poly_sub_def. *)
val poly_add_sub_assoc = store_thm(
  "poly_add_sub_assoc",
  ``!r:'a ring. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> (p + q - t = p + (q - t))``,
  rw[poly_add_assoc, poly_sub_def]);

(* Theorem: poly p /\ poly q ==> p + q - q = p *)
(* Proof:
     p + q - q
   = p + q + -q     by poly_sub_def
   = p + (q + -q)   by poly_add_assoc
   = p + |0|        by poly_add_rneg
   = p              by poly_add_rzero
*)
val poly_add_sub = store_thm(
  "poly_add_sub",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> (p + q - q = p)``,
  rw[poly_add_assoc]);

(* Theorem: p + q - p = q *)
(* Proof:
     p + q - p
   = q + p - p     by poly_add_comm
   = q             by poly_add_sub
*)
val poly_add_sub_comm = store_thm(
  "poly_add_sub_comm",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> (p + q - p = q)``,
  metis_tac[poly_add_comm, poly_add_sub]);

(* Theorem: poly p /\ poly q ==> p - q + q = p *)
(* Proof:
     p - q + q
   = p + -q + q     by poly_sub_def
   = p + (-q + q)   by poly_add_assoc
   = p + |0|        by poly_add_lneg
   = p              by poly_add_rzero
*)
val poly_sub_add = store_thm(
  "poly_sub_add",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> (p - q + q = p)``,
  rw[poly_add_assoc]);

(* Can use lift:
ring_add_sub |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (x + y - y = x)
ring_sub_add |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (x - y + y = x)
ring_exp_add |- !r. Ring r ==> !x. x IN R ==> !n k. x ** (n + k) = x ** n * x ** k
*)

(* Theorem: Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> (p - (q + t) = p - q - t) *)
(* Proof:
     p - (q + t)
   = p + -(q + t)         by poly_sub_def
   = p + (-q + -t)        by poly_neg_add
   = p + -q + -t          by poly_add_assoc, poly_neg_poly
   = p - q - t            by poly_sub_def
*)
val poly_sub_plus = store_thm(
  "poly_sub_plus",
  ``!r:'a ring. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> (p - (q + t) = p - q - t)``,
  rpt strip_tac >>
  `p - (q + t) = p + -(q + t)` by rw[] >>
  `_ = p + (-q + -t)` by rw[] >>
  `_ = p + -q + -t` by rw[poly_add_assoc] >>
  `_ = p - q - t` by rw[] >>
  rw[]);

(* Theorem: Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> (p - (q - t) = p - q + t) *)
(* Proof:
     p - (q - t)
   = p - (q + -t)      by poly_sub_def
   = p - q - -t        by poly_sub_plus, poly_neg_poly
   = p - q + -(-t)     by poly_sub_def
   = p - q + t         by poly_neg_neg
*)
val poly_sub_minus = store_thm(
  "poly_sub_minus",
  ``!r:'a ring. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> (p - (q - t) = p - q + t)``,
  rpt strip_tac >>
  `p - (q - t) = p - (q + -t)` by rw[] >>
  `_ = p - q - -t` by rw[poly_sub_plus] >>
  `_ = p - q + -(-t)` by rw[] >>
  `_ = p - q + t` by rw[] >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Scalar Multiplication                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: c * (p + q) = c * p + c * q *)
(* Proof:
     c * (p + q)
   = chop (c o (chop (p || q)))    by poly_add_def, poly_cmult_def
   = chop (c o (p || q))           by poly_chop_cmult
   = chop (c o p || c o q)         by weak_cmult_add
   = chop (chop (c o p) || chop (c o q))   by poly_chop_add_chop
   = c * p + c * q                 by poly_add_def, poly_cmult_def
*)
val poly_cmult_add = store_thm(
  "poly_cmult_add",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> !c. c IN R ==> (c * (p + q) = c * p + c * q)``,
  rw_tac std_ss[poly_add_def, poly_cmult_def] >>
  `weak p /\ weak q /\ weak (p || q) /\ weak (c o p) /\ weak (c o q)` by rw[] >>
  metis_tac[weak_cmult_add, poly_chop_add_chop, poly_chop_cmult]);

(* Theorem: (b + c) * p = b * p + c * p  *)
(* Proof:
     (b + c) * p
   = chop ((b + c) o p)                    by poly_cmult_def
   = chop (b o p || c o p)                 by weak_add_cmult
   = chop (chop (b o p) || chop (c o p))   by poly_chop_add_chop
   = b * p + c * p                         by poly_cmult_def, poly_add_def
*)
val poly_add_cmult = store_thm(
  "poly_add_cmult",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !b c. b IN R /\ c IN R ==> ((b + c) * p = b * p + c * p)``,
  rw_tac std_ss[weak_add_cmult, poly_chop_add_chop, poly_is_weak, weak_cmult_weak, poly_add_def, poly_cmult_def]);
(* Q: srw_tac stalls *)

(* Theorem: b * (c * p) = (b * c) p  *)
(* Proof:
     b * (c * p)
   = chop (b o chop (c o p))     by poly_cmult_def
   = chop (b o (c o p))          by poly_chop_cmult
   = chop ((b * c) o p)          by weak_cmult_cmult
   = (b * c) * p                 by poly_cmult_def
*)
val poly_cmult_cmult = store_thm(
  "poly_cmult_cmult",
  ``!r:'a ring. Ring r ==> !p:'a poly. poly p ==> !b c. b IN R /\ c IN R ==> (b * (c * p) = (b * c) * p)``,
  rw_tac std_ss[GSYM weak_cmult_cmult, poly_chop_cmult, poly_is_weak, weak_cmult_weak, poly_cmult_def]);
(* Q: srw_tac stalls *)

(* Theorem: b * (c * p) = c * (b * p)  *)
(* Proof: by poly_cmult_cmult and ring_mult_comm.
     b * (c * p)
   = (b * c) * p      by poly_cmult_cmult
   = (c * b) * p      by ring_mult_comm
   = c * (b * p)      by poly_cmult_cmult
*)
val poly_cmult_cmult_comm = store_thm(
  "poly_cmult_cmult_comm",
  ``!r:'a ring. Ring r ==> !p:'a poly. poly p ==> !b c. b IN R /\ c IN R ==> (b * (c * p) = c * (b * p))``,
  rw_tac std_ss[poly_cmult_cmult, ring_mult_comm]);

(* Theorem: c * (- p) = (- c) * p *)
(* Proof:
     c * - p
   = chop (c o -p)     by poly_cmult_def
   = chop (-c o p)     by weak_cmult_neg
   = -c * p            by poly_cmult_def
*)
val poly_cmult_neg = store_thm(
  "poly_cmult_neg",
  ``!r:'a ring. Ring r ==> !p:'a poly. poly p ==> !c. c IN R ==> (c * (- p) = (- c) * p)``,
  rw_tac std_ss[poly_cmult_def, weak_cmult_neg, poly_is_weak, poly_neg_def]);
(* Q: srw_tac stalls *)

(* Theorem: (- c) * p = - (c * p) *)
(* Proof:
     (-c) * p + (c * p)
   = (-c + c) * p               by poly_add_cmult
   = #0 * p                     by ring_add_lneg
   = |0|                        by poly_cmult_lzero
   hence (-c) * p = - (c * p)   by poly_add_eq_zero
*)
val poly_neg_cmult = store_thm(
  "poly_neg_cmult",
  ``!r:'a ring. Ring r ==> !p:'a poly. poly p ==> !c. c IN R ==> ((- c) * p = - (c * p))``,
  rpt strip_tac >>
  `-c IN R` by rw[] >>
  `(-c) * p + (c * p) = |0|` by rw[GSYM poly_add_cmult] >>
  rw[GSYM poly_add_eq_zero]);

val _ = export_rewrites ["poly_cmult_neg", "poly_neg_cmult"];

(* Theorem: c * (p - q) = c * p - c * q *)
(* Proof:
     c * (p - q)
   = c * (p + -q)        by poly_sub_def
   = c * p + c * -q      by poly_cmult_add
   = c * p + (-c) * q    by poly_cmult_neg
   = c * p + -(c * q)    by poly_neg_cmult
   = c * p - c * q       by poly_sub_def
*)
val poly_cmult_sub = store_thm(
  "poly_cmult_sub",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> !c. c IN R ==> (c * (p - q) = c * p - c * q)``,
  rw[poly_cmult_add]);

val _ = export_rewrites ["poly_cmult_sub"];

(* ------------------------------------------------------------------------- *)
(* Polynomial Shifts                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: poly p ==> poly (p >> n) *)
(* Proof:
     poly (p >> n)
   = weak (p >> n) /\ ((p >> n = |0|) \/ LAST (p >> n) <> #0)      by poly_def_alt
   = T             /\ ((p >> n = |0|) \/ LAST (p >> n) <> #0)      by poly_shift_weak
   If p = |0|, then p >> n = |0|                  by poly_shift_eq_of_zero
   If p <> |0|, LAST (p >> n) = LAST p <> #0      by poly_shift_last, poly_def_alt

   or:
       poly (p >> n)
   <=> weak (p >> n) /\ chop (p >> n) = p >> n    by poly_chop_eq_poly
   <=> T             /\ chop (p >> n) = p >> n    by poly_is_weak, poly_shift_weak
   <=> T             /\ (chop p) >> n = p >> n    by poly_chop_shift
   <=> T             /\ T                         by poly_chop_poly
*)
val poly_shift_poly = store_thm(
  "poly_shift_poly",
  ``!r:'a ring. Ring r ==> !p n. poly p ==> poly (p >> n)``,
  rw[poly_chop_eq_poly]);
(* Note: This one needs !r. Ring r due to poly_shift_weak, for ring_zero_element. *)

val _ = export_rewrites ["poly_shift_poly"];

(* Theorem: (- p) >> n = - (p >> n) *)
(* Proof: by weak_neg_shift. *)
val poly_neg_shift = store_thm(
  "poly_neg_shift",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !n. (- p) >> n = - (p >> n)``,
  rw[weak_neg_shift, poly_neg_def]);

(* Theorem: (p + q) >> 1 = p >> 1 + q >> 1 *)
(* Proof:
     (p + q) >> 1
   = (chop (p || q)) >> 1           by poly_add_def
   = chop ((p || q) >> 1)           by poly_chop_shift
   = chop ((p >> 1) || (q >> 1))    by weak_add_shift_1
   = p >> 1 + q >> 1                by poly_add_def
*)
val poly_add_shift_1 = store_thm(
  "poly_add_shift_1",
  ``!r:'a ring. Ring r ==> !p q:'a poly. (p + q) >> 1 = (p >> 1) + (q >> 1)``,
  rpt strip_tac >>
  rw_tac std_ss[GSYM weak_add_shift_1, poly_add_def, poly_chop_shift]);

(* Theorem: (p + q) >> n = p >> n + q >> n *)
(* Proof:
     (p + q) >> n
   = (chop (p || q)) >> n           by poly_add_def
   = chop ((p || q) >> n)           by poly_chop_shift
   = chop ((p >> n) || (q >> n))    by weak_add_shift
   = p >> n + q >> n                by poly_add_def
*)
val poly_add_shift = store_thm(
  "poly_add_shift",
  ``!r:'a ring. Ring r ==> !p q:'a poly. !n. (p + q) >> n = p >> n + q >> n``,
  rpt strip_tac >>
  rw_tac std_ss[GSYM weak_add_shift, poly_add_def, poly_chop_shift]);

(* Theorem: (c * p) >> 1 = c * (p >> 1) *)
(* Proof:
     (c * p) >> 1
   = (chop (c o p)) >> 1          by poly_cmult_def
   = chop ((c o p) >> 1)          by poly_chop_shift
   = chop (c o (p >> 1))          by weak_cmult_shift_1
   = c * (p >> 1)                 by poly_cmult_def
*)
val poly_cmult_shift_1 = store_thm(
  "poly_cmult_shift_1",
  ``!r:'a ring. Ring r ==> !p:'a poly. !c. c IN R ==> ((c * p) >> 1 = c * (p >> 1))``,
  rpt strip_tac >>
  rw_tac std_ss[GSYM weak_cmult_shift_1, poly_cmult_def, poly_chop_shift]);

(* Theorem: (c * p) >> n = c * (p >> n) *)
(* Proof:
     (c * p) >> n
   = (chop (c o p)) >> n          by poly_cmult_def
   = chop ((c o p) >> n)          by poly_chop_shift
   = chop (c o (p >> n))          by weak_cmult_shift
   = c * (p >> n)                 by poly_cmult_def
*)
val poly_cmult_shift = store_thm(
  "poly_cmult_shift",
  ``!r:'a ring. Ring r ==> !p:'a poly. !c. c IN R ==> !n. (c * p) >> n = c * (p >> n)``,
  rpt strip_tac >>
  rw_tac std_ss[GSYM weak_cmult_shift, poly_cmult_def, poly_chop_shift]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Multiplication                                                 *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Theorems on polynomial multiplication                                     *)
(* These are not related to Monoid (PolyRing r).prod).                      *)
(* But this can be lifted if we know Ring (PolyRing r).                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: |0| * p = |0|  *)
(* Proof:
     |0| * p
   = chop ( |0| o p)    by poly_mult_def
   = chop |0|           by weak_mult_of_lzero
   = |0|                by poly_chop_of_zero
*)
val poly_mult_lzero = store_thm(
  "poly_mult_lzero",
  ``!p:'a poly. |0| * p = |0|``,
  rw[poly_mult_def]);

(* Theorem: p * |0| = |0|  *)
(* Proof:
     p * |0|
   = chop (p o |0|)     by poly_mult_def
   = chop |0|           by weak_mult_of_rzero
   = |0|                by poly_chop_of_zero
*)
val poly_mult_rzero = store_thm(
  "poly_mult_rzero",
  ``!p:'a poly. p * |0| = |0|``,
  rw[poly_mult_def]);

val _ = export_rewrites ["poly_mult_lzero", "poly_mult_rzero"];

(* val poly_mult_zero = save_thm("poly_mult_zero", CONJ poly_mult_lzero poly_mult_rzero); *)
(* > val poly_mult_zero = |- (!p. |0| * p = |0|) /\ !p. p * |0| = |0| : thm *)

(* Theorem: |0| * p = |0| and p * |0| = |0| *)
(* Proof: combine poly_mult_lzero and poly_mult_rzero. *)
val poly_mult_zero = save_thm("poly_mult_zero",
    CONJ (poly_mult_lzero |> SPEC_ALL)
         (poly_mult_rzero |> SPEC_ALL) |> GEN ``(p:'a poly)``);
(* > val poly_mult_zero = |- !p. ( |0| * p = |0|) /\ (p * |0| = |0|) : thm *)

(* Theorem: (p * [] = []) /\ ([] * p = []) *)
(* Proof: by poly_mult_zero, poly_zero *)
val poly_mult_of_zero = store_thm(
  "poly_mult_of_zero",
  ``!r:'a ring. !p:'a poly. (p * [] = []) /\ ([] * p = [])``,
  metis_tac[poly_mult_zero, poly_zero]);

(* Theorem: Polynomial multiplication clauses. *)
(* Proof: by theorems proved. *)
val poly_mult_clauses = store_thm(
  "poly_mult_clauses",
  ``!r:'a ring. Ring r ==> !p q t :('a poly). poly p /\ poly q /\ poly t ==>
      ( |0| * p = |0|) /\ (p * |0| = |0|) /\
      ( |1| * p = p) /\ (p * |1| = p) /\
      (p * q = q * p) /\ (p * q * t = p * (q * t))``,
  rw[poly_mult_comm, poly_mult_assoc]);

(* Theorem: Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> (p * (q * t) = q * (p * t)) *)
(* Proof: by poly_ring_ring, ring_mult_assoc_comm, poly_ring_element *)
val poly_mult_assoc_comm = store_thm(
  "poly_mult_assoc_comm",
  ``!r:'a ring. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> (p * (q * t) = q * (p * t))``,
  rw[poly_ring_ring, ring_mult_assoc_comm, poly_ring_element]);

(* ------------------------------------------------------------------------- *)
(* Theorems on polynomial multiplication with shifting.                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (p * q) >> 1 = p * (q >> 1) *)
(* Proof:
     (p * q) >> 1
   = (chop (p o q)) >> 1          by poly_mult_def
   = chop ((p o q) >> 1)          by poly_chop_shift
   = chop (p o (q >> 1))          by weak_mult_shift_1
   = p * (q >> 1)                 by poly_mult_def
*)
val poly_mult_shift_1 = store_thm(
  "poly_mult_shift_1",
  ``!r:'a ring. Ring r ==> !p q:'a poly. poly p /\ poly q ==> ((p * q) >> 1 = p * (q >> 1))``,
  rpt strip_tac >>
  `weak p /\ weak q /\ weak (q >> 1)` by rw[] >>
  rw_tac std_ss[GSYM weak_mult_shift_1, poly_chop_shift, poly_mult_def]);

(* Theorem: (p * q) >> 1 = (p >> 1) * q *)
(* Proof: by weak_mult_shift_1_comm.
     (p * q) >> 1
   = (chop (p o q)) >> 1          by poly_mult_def
   = chop ((p o q) >> 1)          by poly_chop_shift
   = chop ((p >> 1) o q)          by weak_mult_shift_1_comm
   = (p >> 1) * q                 by poly_mult_def
*)
val poly_mult_shift_1_comm = store_thm(
  "poly_mult_shift_1_comm",
  ``!r:'a ring. Ring r ==> !p q:'a poly. poly p /\ poly q ==> ((p * q) >> 1 = (p >> 1) * q)``,
  rpt strip_tac >>
  `weak p /\ weak q /\ weak (p >> 1)` by rw[] >>
  rw_tac std_ss[GSYM weak_mult_shift_1_comm, poly_chop_shift, poly_mult_def]);

val _ = export_rewrites ["poly_mult_shift_1", "poly_mult_shift_1_comm"];

(* In polyField.hol *)

(* Theorem: (p * q) >> n = p * (q >> n) *)
(* Proof: by induction on n.
   If p = |0|,
      LHS = ( |0| * q) >> n
          = |0| >> n        by poly_mult_lzero
          = |0|             by zero_poly_shift
          = |0| * (q >> n)  by poly_mult_lzero
          = RHS
   If q = |0|,
      LHS = (p * |0|) >> n
          = |0| >> n        by poly_mult_rzero
          = |0|             by zero_poly_shift
          = p * ( |0| >> n)  by zero_poly_shift, poly_mult_rzero
          = RHS
   Induction on n:
   Base case: (p * q) >> 0 = p * q >> 0
      LHS = (p * q) >> 0
          = p * q           by poly_shift_zero
          = p * (q >> 0)    by poly_shift_zero
          = RHS
   Step case: (p * q) >> n = p * q >> n ==> (p * q) >> SUC n = p * q >> SUC n
     Since q <> |0|, q >> n <> |0| by poly_shift_eq_zero
      RHS = p * q >> SUC n
          = p * ((q >> n) >> 1)   by poly_shift_suc, poly_shift_1
          = (p * (q >> n)) >> 1   by poly_mult_shift_1
          = ((p * q) >> n) >> 1   by induction hypothesis
      If p * q = |0|,
      RHS = ( |0| >> n) >> 1
          = |0|                   by poly_shift_zero
          = |0| >> SUC n          by poly_shift_zero
          = LHS
      If p * q <> |0|,
      LHS = (p * q) >> SUC n
          = ((p * q) >> n) >> 1   by poly_shift_suc, poly_shift_1
          = RHS
*)
val poly_mult_shift = store_thm(
  "poly_mult_shift",
  ``!r:'a ring. Ring r ==> !p q:'a poly. poly p /\ poly q ==> !n. (p * q) >> n = p * (q >> n)``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[] >>
  Cases_on `q = |0|` >-
  rw_tac std_ss[poly_mult_rzero, poly_shift_zero] >>
  Induct_on `n` >-
  rw[] >>
  (`poly (p * q) /\ poly (q >> n) /\ poly ((p * q) >> n)` by rw[]) >>
  (`p * (q >> SUC n) = (p * (q >> n)) >> 1`
    by rw_tac std_ss[poly_mult_shift_1, poly_shift_suc, poly_shift_1, poly_shift_eq_zero]) >>
  Cases_on `p * q = |0|` >-
  metis_tac[poly_shift_zero] >>
  (`poly (p * q) /\ poly (q >> n) /\ poly ((p * q) >> n)` by rw[]) >>
  metis_tac[poly_shift_eq_zero, poly_shift_suc, poly_shift_1]);

(* In polyField.hol *)
(* Theorem: (p * q) >> n = p >> n * q *)
(* Proof:
     (p * q) >> n
   = (q * p) >> n   by poly_mult_comm
   = q * (p >> n)   by poly_mult_shift
   = p >> n * q     by poly_mult_comm
*)
val poly_mult_shift_comm = store_thm(
  "poly_mult_shift_comm",
  ``!r:'a ring. Ring r ==> !p q:'a poly. poly p /\ poly q ==> !n. (p * q) >> n = p >> n * q``,
  metis_tac[poly_mult_comm, poly_mult_shift, poly_shift_poly]);

(* ------------------------------------------------------------------------- *)
(* Theorems on polynomial multiplication with scalar multiplication.         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (c * p) * q = c * (p * q)  *)
(* Proof:
     (c * p) * q
   = chop (chop (c o p) o q)     by poly_mult_def, poly_cmult_def
   = chop ((c o p) o q)          by poly_chop_mult
   = chop (c o (p o q))          by weak_cmult_mult
   = chop (c o chop (p o q))     by poly_chop_cmult
   = c * (p * q)                 by poly_mult_def, poly_cmult_def
*)
val poly_cmult_mult = store_thm(
  "poly_cmult_mult",
  ``!r:'a ring. Ring r ==> !p q:'a poly. poly p /\ poly q ==> !c. c IN R ==> ((c * p) * q = c * (p * q))``,
  rpt strip_tac >>
  `weak p /\ weak q /\ weak (c o p) /\ weak (p o q)` by rw[] >>
  `chop (chop (c o p) o q) = chop (c o chop (p o q))`
    by rw_tac std_ss[GSYM poly_chop_mult, weak_cmult_mult, poly_chop_cmult] >>
  rw_tac std_ss[poly_mult_def, poly_cmult_def]);

val _ = export_rewrites ["poly_cmult_mult"];

(* Theorem: c * |1| = if c = 0 then |0| else [c] *)
(* Proof: by definition.
     c * |1|
   = chop (c o |1|)         by poly_cmult_def
   = chop (c o chop [#1])   by poly_ring_ids
   = chop (c o [#1])        by poly_chop_cmult
   = chop [c]               by weak_cmult_one
   If c = #0, chop [c] = chop [#0] = |0|  by poly_chop_const_zero
   If c <> #0, chop [c] = [c]             by poly_chop_const_nonzero
*)
val poly_cmult_one = store_thm(
  "poly_cmult_one",
  ``!r:'a ring. Ring r ==> !c. c IN R ==> (c * |1| = if c = #0 then |0| else [c])``,
  metis_tac[poly_cmult_def, poly_ring_ids, poly_chop_cmult, weak_one, weak_cmult_one, poly_chop_const_zero, poly_chop_const_nonzero]);

(* Theorem: #1 * p = p *)
(* Proof:
     #1 * p
   = chop (#1 o p)   by poly_cmult_def
   = chop p          by weak_cmult_lone
   = p               by poly_chop_poly
*)
val poly_cmult_lone = store_thm(
  "poly_cmult_lone",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (#1 * p = p)``,
  rw_tac std_ss[poly_cmult_def, poly_is_weak, weak_cmult_lone, poly_chop_poly]);

val _ = export_rewrites ["poly_cmult_one", "poly_cmult_lone"];

(* Theorem: c IN R /\ poly p ==> (c * p = (c * |1|) * p) *)
(* Proof:
     c * p
   = c * (1| * p)    by poly_mult_lone
   = (c * |1|) * p   by poly_cmult_mult
*)
val poly_cmult_alt = store_thm(
  "poly_cmult_alt",
  ``!r:'a ring. Ring r ==> !c p. c IN R /\ poly p ==> (c * p = (c * |1|) * p)``,
  rw[]);

(* Theorem: p * (c * q) = c * p * q  *)
(* Proof:
     p * (c * q)
   = (c * q) * p    by poly_mult_comm
   = c * (q * p)    by poly_cmult_mult
   = c * (p * q)    by poly_mult_comm
   = c * p * q      by poly_cmult_mult
*)
val poly_mult_cmult = store_thm(
  "poly_mult_cmult",
  ``!r:'a ring. Ring r ==> !c. c IN R ==> !p q. poly p /\ poly q ==> (p * (c * q) = c * p * q)``,
  rpt strip_tac >>
  `p * (c * q) = (c * q) * p` by metis_tac[poly_mult_comm, poly_cmult_poly] >>
  rw[poly_cmult_mult, poly_mult_comm]);

(* ------------------------------------------------------------------------- *)
(* Theorems on polynomial multiplication with negation.                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (- p) * q = - (p * q)  *)
(* Proof:
   Since
     (-p) * q + (p * q)
   = (- p + p) * q           by poly_mult_ladd
   = |0| * p                 by poly_add_lneg
   = |0|                     by poly_mult_lzero
   Hence
     (- p) * q = - (p * q)   by poly_add_eq_zero
*)
(* better by lifting *)
val poly_mult_lneg = lift_ring_thm_with_goal "mult_lneg" "mult_lneg"
   ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> ((- p) * q = - (p * q))``;
(* > val poly_mult_lneg =
|- !r. Ring r ==> !p q. poly p /\ poly q ==> (-p * q = -(p * q)): thm
*)

(* Theorem: p * (- q) = - (p * q)  *)
(* Proof:
     p * (-q)
   = (-q) * p    by poly_mult_comm
   = - (q * p)   by poly_mult_lneg
   = - (p * q)   by poly_mult_comm
*)
(* better by lifting *)
val poly_mult_rneg = lift_ring_thm_with_goal "mult_rneg" "mult_rneg"
   ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> (p * (- q) = - (p * q))``;
(* > val poly_mult_rneg =
|- !r. Ring r ==> !p q. poly p /\ poly q ==> (p * -q = -(p * q)): thm
*)

val _ = export_rewrites ["poly_mult_lneg", "poly_mult_rneg"];

(* Theorem: poly p /\ poly q ==> (-(p * q) = -p * q) /\ (-(p * q) = p * -q) *)
(* Proof:
   Since Ring r ==> Ring (PolyRing r)          by poly_add_mult_ring
     and poly p <=> p IN (PolyRing r).carrier  by poly_ring_element
     Hence   -(p * q) = -p * q                 by ring_neg_mult
       and   -(p * q) = p * -q                 by ring_neg_mult
*)
(* better by lifting *)
val poly_neg_mult = lift_ring_thm_with_goal "neg_mult" "neg_mult"
   ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> (-(p * q) = -p * q) /\ (-(p * q) = p * -q)``;
(* > val poly_neg_mult =
|- !r. Ring r ==> !p q. poly p /\ poly q ==> (-(p * q) = -p * q) /\ (-(p * q) = p * -q): thm
*)

(* Theorem: Ring r ==> !p q. poly p /\ poly q ==> (-p * -q = p * q) *)
(* Proof: by poly_ring_ring, ring_mult_neg_neg *)
(* better by lifting *)
val poly_mult_neg_neg = lift_ring_thm_with_goal "mult_neg_neg" "mult_neg_neg"
   ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> (-p * -q = p * q)``;
(* > val poly_mult_neg_neg =
|- !r. Ring r ==> !p q. poly p /\ poly q ==> (-p * -q = p * q): thm
*)

(* ------------------------------------------------------------------------- *)
(* Theorems on polynomial distribution with subtraction.                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: p * (q - t) = p * q - p * t *)
(* Proof: by poly_mult_radd and poly_sub_def.
     p * (q - t)
   = p * (q + -t)       by poly_sub_def
   = p * q + p * -t     by poly_mult_radd
   = p * q + -(p * t)   by poly_mult_rneg
   = p * q - p * t      by poly_sub_def
*)
val poly_mult_rsub = store_thm(
  "poly_mult_rsub",
  ``!r:'a ring. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> (p * (q - t) = p * q - p * t)``,
  rw[poly_sub_def]);

(* Theorem: (p - q) * t = p * t - q * t *)
(* Proof: by poly_mult_comm and poly_mult_rsub.
     (p - q) * t
   = t * (p - q)        by poly_mult_comm
   = t * p - t * q      by poly_mult_rsub
   = p * t - q * t      by poly_mult_comm
   or
     (p - q) * t
   = (p + -q) * t       by poly_sub_def
   = p * t + -q * t     by poly_mult_ladd
   = p * t + -(q * t)   by poly_mult_lneg
   = p * t - q * t      by poly_sub_def

*)
val poly_mult_lsub = store_thm(
  "poly_mult_lsub",
  ``!r:'a ring. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==> ((p - q) * t = p * t - q * t)``,
  rw[poly_sub_def]);

val _ = export_rewrites ["poly_mult_rsub", "poly_mult_lsub"];

(* Theorem: p * (q - r) = p * q  - p * t /\ (p - q) * t = p * t - q * t *)
(* Proof: by poly_mult_rsub and poly_mult_lsub. *)
val poly_mult_sub = save_thm("poly_mult_sub",
    CONJ (poly_mult_rsub |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH)
         (poly_mult_lsub |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH)
         |> DISCH ``poly p /\ poly q /\ poly t`` |> GEN ``t:'a poly`` |> GEN ``q:'a poly`` |> GEN ``p:'a poly``
         |> DISCH_ALL |> GEN_ALL);
(* > val poly_mult_sub = |- !r. Ring r ==> !p q t. poly p /\ poly q /\ poly t ==>
                                           (p * (q - t) = p * q - p * t) /\ ((p - q) * t = p * t - q * t) : thm *)

(* ------------------------------------------------------------------------- *)
(* Polynomial Multiplication zero product (Preparation).                     *)
(* ------------------------------------------------------------------------- *)

(* Zero product is not true for R[x]: e.g. (2x) * (3x) = |0| in Z_6.
This is not crucial for Polynomial R[x] being a Ring itself.
However, this is true for F[x], where F is a field, and in that case F[x] is an integral domain.
*)

(*
Fundamentally, why does  p * q = |0| ==> p = |0| or q = |0| ?
This should come from:
- poly_mult_cross;
> val it = |- !r. Ring r ==> !h k p q. poly (h::p) /\ poly (k::q) ==>
    ((h::p) * (k::q) = [h * k] + (h * q) >> 1 + (k * p) >> 1 + ((p * q) >> 1) >> 1) : thm

So it really is this:  [c1] + c2 * (p >> 1) + c3 * (q >> 1) + (p >> 1) * (q >> 1) = 0 means equal component is |0|.
or                     [c1] + (#0::p) + (#0::q) + (#0::(#0::r))) = |0| means each component is |0|
*)

(* ------------------------------------------------------------------------- *)
(* Cross-Multiplication of Polynomials.                                      *)
(* ------------------------------------------------------------------------- *)

(* All these depends on weak [h], and [h] + poly is OK. *)

(* Theorem: [Cross-multiplication]
            (h::p) * (k::q) = [h * k] + ((h * q) >> 1 + (k * p) >> 1 + ((p * q) >> 1) >> 1) *)
(* Proof:
     (h::p) * (k::q)
   = chop ((h::p) o (k::q))                                                       by poly_mult_def
   = chop ([h * k] || h o q >> 1 || k o p >> 1 || (p o q >> 1) >> 1)              by weak_mult_cross
   = chop ([h * k] || (h o q >> 1 || k o p >> 1 || (p o q >> 1) >> 1))            by weak_add_assoc, weak_const
   = chop ([h * k] || chop (h o q >> 1 || k o p >> 1 || (p o q >> 1) >> 1))       by poly_chop_add_comm
   = chop ([h * k] || chop (chop (h o q >> 1 || k o p >> 1) || chop ((p o q >> 1) >> 1))) by poly_chop_add_chop
   = chop ([h * k] || chop (chop (chop (h o q >> 1) || chop (k o p >> 1)) || chop ((p o q >> 1) >> 1))) by poly_chop_add_chop
   = chop ([h * k] || chop (chop ((chop (h o q) >> 1) || (chop (k o p) >> 1)) || ((chop (p o q) >> 1) >> 1))) by poly_chop_shift
   = chop ([h * k] || chop (chop ((h * q) >> 1 || (k * p) >> 1) || ((p * q) >> 1) >> 1)) by poly_cmult_def, poly_mult_def
   = [h * k] + chop (chop ((h * q) >> 1 || (k * p) >> 1) || ((p * q) >> 1) >> 1)  by poly_add_def
   = [h * k] + (chop ((h * q) >> 1 || (k * p) >> 1) + ((p * q) >> 1) >> 1)        by poly_add_def
   = [h * k] + ((h * q) >> 1 + (k * p) >> 1 + ((p * q) >> 1) >> 1)                by poly_add_def

   To go further would need poly [h*k], but we only have weak [h*k].

   Note: [h*k] may not be a polynomial, e.g. [#0], but [h*k] + ... will do the chop automatically.
   However, [h*k] not being a polynomial affects application of poly_add_assoc or poly_add_comm -- they need polynomials!
   So one must prove version of poly_add_assoc and poly_add_comm when one is a zerop polynomial.
*)
val poly_mult_cross = store_thm(
  "poly_mult_cross",
  ``!r:'a ring. Ring r ==> !h k p q. poly (h::p) /\ poly (k::q) ==>
                           ((h::p) * (k::q) = [h * k] + ((h * q) >> 1 + (k * p) >> 1 + ((p * q) >> 1) >> 1))``,
  rpt strip_tac >>
  `weak (h::p) /\ weak (k::q)` by rw_tac std_ss[poly_is_weak] >>
  `h IN R /\ k IN R /\ poly p /\ poly q` by metis_tac[poly_cons_poly] >>
  `weak p /\ weak q` by rw_tac std_ss[poly_is_weak] >>
  `weak ((h o q) >> 1) /\ weak ((k o p) >> 1)` by rw_tac std_ss[weak_cmult_weak, poly_shift_weak] >>
  `weak (((p o q) >> 1) >> 1)` by rw_tac std_ss[weak_mult_weak, poly_shift_weak] >>
  `weak [h * k]` by rw_tac std_ss[ring_mult_element, weak_const] >>
  `(h::p) * (k::q) = chop ((h::p) o (k::q))` by rw_tac std_ss[poly_mult_def] >>
  `_ = chop ([h * k] || h o q >> 1 || k o p >> 1 || (p o q >> 1) >> 1)` by rw_tac std_ss[weak_mult_cross] >>
  `_ = chop ([h * k] || (h o q >> 1 || k o p >> 1 || (p o q >> 1) >> 1))`
    by rw_tac std_ss[weak_add_assoc, weak_add_weak] >>
  `_ = chop ([h * k] || chop (h o q >> 1 || k o p >> 1 || (p o q >> 1) >> 1))`
    by rw_tac std_ss[poly_chop_add_comm, weak_add_weak] >>
  `_ = chop ([h * k] || chop (chop (h o q >> 1 || k o p >> 1) || chop ((p o q >> 1) >> 1)))`
    by rw_tac std_ss[poly_chop_add_chop, weak_add_weak] >>
  `_ = chop ([h * k] || chop (chop (chop (h o q >> 1) || chop (k o p >> 1)) || chop ((p o q >> 1) >> 1)))`
    by rw_tac std_ss[poly_chop_add_chop] >>
  `_ = chop ([h * k] || chop (chop ((chop (h o q) >> 1) || (chop (k o p) >> 1)) || ((chop (p o q) >> 1) >> 1)))`
    by rw_tac std_ss[poly_chop_shift] >>
  rw_tac std_ss[poly_mult_def, poly_cmult_def, poly_add_def]);

Theorem HD_poly_mult:
  Ring r /\ poly p /\ poly q /\ p * q <> |0| ==>
  HD (poly_mult r p q) = r.prod.op (HD p) (HD q)
Proof
  strip_tac
  \\ Cases_on`p = |0|` >- metis_tac[poly_mult_zero]
  \\ Cases_on`q = |0|` >- metis_tac[poly_mult_zero]
  \\ Cases_on`p` \\ Cases_on`q` \\ fs[]
  \\ qpat_x_assum`_ <> _`mp_tac
  \\ dep_rewrite.DEP_REWRITE_TAC[poly_mult_cross]
  \\ dep_rewrite.DEP_REWRITE_TAC[GSYM poly_add_shift]
  \\ conj_tac >- simp[]
  \\ conj_tac >- simp[]
  \\ qmatch_goalsub_abbrev_tac`a + b >> 1`
  \\ rewrite_tac[poly_add_def]
  \\ strip_tac
  \\ dep_rewrite.DEP_REWRITE_TAC[HD_chop]
  \\ conj_tac >- simp[]
  \\ dep_rewrite.DEP_REWRITE_TAC[HD_weak_add_shift]
  \\ simp[Abbr`a`]
QED


(* Theorem: h::t = [h] + t >> 1 *)
(* Proof: (almost)
     poly (h::t)
   = chop (poly (h::t))      by poly_chop_poly
   = chop ([h] || t >> 1)    by weak_cons_eq_add_shift, poly_is_weak
   = [h] + t >> 1            by poly_add_def, but need [h], which is true only for h <> #0.
*)
(* Proof:
   If t = |0| = []           by poly_zero
      h <> #0, so poly [h]   by poly_nonzero_element_poly
      h::t = [h]
           = [h] + |0|       by poly_add_rzero
           = [h] + |0| >> 1  by poly_shift_zero
   If t <> |0|, t <> []      by poly_zero
     [h] + t >> 1
   = [h] + (#0::t)           by poly_shift_1, t <> []
   = chop ([h] || (#0::t))   by poly_add_def
   = chop (h + #0::[] || t)  by weak_add_cons
   = chop (h::t)             by ring_add_rzero, weak_add_of_lzero
   = h::t                    by poly_chop_poly
*)
val poly_cons_eq_add_shift = store_thm(
  "poly_cons_eq_add_shift",
  ``!r:'a ring. Ring r ==> !h t. poly (h::t) ==> (h::t = [h] + t >> 1)``,
  rw_tac std_ss[poly_cons_poly] >>
  `poly (h::t)` by rw_tac std_ss[poly_cons_poly] >>
  Cases_on `t = |0|` >-
  metis_tac[poly_shift_zero, poly_add_rzero, poly_nonzero_element_poly, zero_poly_cons, zero_poly_zero, poly_zero] >>
  metis_tac[poly_shift_1, poly_add_def, weak_add_cons, ring_add_rzero, weak_add_of_lzero, poly_chop_poly, poly_zero]);

(* Theorem: Ring r ==> !p c. poly p /\ c IN R /\ c <> #0 ==> (SNOC c p = p + [c] >> (LENGTH p)) *)
(* Proof:
   Note poly [c]              by poly_nonzero_element_poly
   By induction on p.
   Base: poly [] ==> (SNOC c [] = [] + [c] >> LENGTH [])
      LHS = SNOC c []
          = [c]               by SNOC_NIL
      RHS = [] + [c] >> LENGTH []
          = [] + [c] >> 0     by LENGTH_NIL
          = [] + [c]          by poly_shift_0
          = |0| + [c]         by poly_zero
          = [c] = LHS         by poly_add_lzero
   Step: poly p ==> (SNOC c p = p + [c] >> LENGTH p) ==>
         !h. poly (h::p) ==> (SNOC c (h::p) = (h::p) + [c] >> LENGTH (h::p))
      Note h IN R /\ poly p   by poly_cons_poly
       and SNOC c p <> |0|    by NOT_SNOC_NIL
      If h = #0,
         Then p <> |0|        by poly_cons_property
           SNOC c (#0::p)
         = #0::SNOC c p                         by SNOC_CONS
         = (SNOC c p) >> 1                      by poly_shift_1, SNOC c p <> |0|
         = (p + [c] >> LENGTH p) >> 1           by induction hypothesis
         = p >> 1 + ([c] >> LENGTH p) >> 1      by poly_add_shift_1
         = (#0::p) + ([c] >> LENGTH p) >> 1     by poly_shift_1, p <> |0|
         = (#0::p) + [c] >> SUC (LENGTH p)      by poly_shift_SUC
         = (#0::p) + [c] >> LENGTH (#0::p)      by LENGTH
      If h <> #0,
         Then poly [h]                          by poly_nonzero_element_poly
          and SNOC c p = p + [c] >> LENGTH p    by induction hypothesis
         thus poly (SNOC c p)                   by poly_shift_poly, poly_add_poly
          and poly (h::SNOC c p)                by poly_nonzero_cons_poly
           SNOC c (h::p)
         = h::SNOC c p                                 by SNOC_CONS
         = [h] + (SNOC c p) >> 1                       by poly_cons_eq_add_shift, poly (h::SNOC c p)
         = [h] + (p + [c] >> (LENGTH p)) >> 1          by induction hypothesis
         = [h] + (p >> 1 + ([c] >> (LENGTH p)) >> 1)   by poly_add_shift_1
         = ([h] + p >> 1) + ([c] >> (LENGTH p)) >> 1   by poly_add_assoc
         = (h::p) + ([c] >> (LENGTH p)) >> 1           by poly_cons_eq_add_shift
         = (h::p) + [c] >> SUC (LENGTH p)              by poly_shift_SUC
         = (h::p) + [c] >> LENGTH (h::p)               by LENGTH
*)
val poly_snoc_eq_add_shift = store_thm(
  "poly_snoc_eq_add_shift",
  ``!r:'a ring. Ring r ==> !p c. poly p /\ c IN R /\ c <> #0 ==> (SNOC c p = p + [c] >> (LENGTH p))``,
  rpt strip_tac >>
  `poly [c]` by rw[poly_nonzero_element_poly] >>
  Induct_on `p` >-
  rw[] >>
  rpt strip_tac >>
  `h IN R /\ poly p` by metis_tac[poly_cons_poly] >>
  `SNOC c p <> |0|` by rw[NOT_SNOC_NIL] >>
  Cases_on `h = #0` >| [
    `p <> |0|` by metis_tac[poly_cons_property, poly_zero] >>
    `SNOC c (#0::p) = #0::SNOC c p` by rw[] >>
    `_ = (SNOC c p) >> 1` by rw[poly_shift_1] >>
    `_ = (p + [c] >> LENGTH p) >> 1` by metis_tac[] >>
    `_ = p >> 1 + ([c] >> LENGTH p) >> 1` by rw[poly_add_shift_1] >>
    `_ = (#0::p) + ([c] >> LENGTH p) >> 1` by rw[poly_shift_1] >>
    `_ = (#0::p) + [c] >> SUC (LENGTH p)` by rw[] >>
    `_ = (#0::p) + [c] >> LENGTH (#0::p)` by rw[] >>
    metis_tac[],
    `poly [h]` by rw[poly_nonzero_element_poly] >>
    `SNOC c p = p + [c] >> LENGTH p` by metis_tac[] >>
    `poly (SNOC c p)` by rw[] >>
    `poly (h::SNOC c p)` by rw[poly_nonzero_cons_poly] >>
    `SNOC c (h::p) = h::SNOC c p` by rw[] >>
    `_ = [h] + (SNOC c p) >> 1` by rw[poly_cons_eq_add_shift] >>
    `_ = [h] + (p + [c] >> (LENGTH p)) >> 1` by metis_tac[] >>
    `_ = [h] + (p >> 1 + ([c] >> (LENGTH p)) >> 1)` by rw[poly_add_shift_1] >>
    `_ = ([h] + p >> 1) + ([c] >> (LENGTH p)) >> 1` by rw[poly_add_assoc] >>
    `_ = (h::p) + ([c] >> (LENGTH p)) >> 1` by rw[GSYM poly_cons_eq_add_shift] >>
    `_ = (h::p) + [c] >> SUC (LENGTH p)` by rw[] >>
    `_ = (h::p) + [c] >> LENGTH (h::p)` by rw[] >>
    metis_tac[]
  ]);

(* Theorem: when c <> #0, [c] + p >> 1 <> |0| *)
(* Proof: by the constant term c <> #0.
   Since c <> #0, poly (c::p)     by poly_cons_poly, zero_poly_cons
   hence [c] + p >> 1 = (c::p)    by poly_cons_eq_add_shift
                  <> [], <> |0|   by poly_zero
*)
val poly_add_nonzero_const_shift_not_zero = store_thm(
  "poly_add_nonzero_const_shift_not_zero",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !c. c IN R /\ c <> #0 ==> [c] + p >> 1 <> |0|``,
  metis_tac[poly_cons_poly, zero_poly_cons, poly_cons_eq_add_shift, NOT_CONS_NIL, poly_zero]);

(* ------------------------------------------------------------------------- *)
(* Theorems on polynomial degree (rely on poly).                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: poly p /\ deg p = 0 ==> p = |0| \/ ?h. p = [h] /\ h <> #0 *)
(* Proof:
   Since poly p ==> weak p,
   p = |0| or ?h. p = [h]    by poly_deg_weak_eq_zero
   Since poly p = poly [h],
   h <> #0                   by poly_def_alt, LAST_CONS
*)
val poly_deg_eq_zero = store_thm(
  "poly_deg_eq_zero",
  ``!p. poly p /\ (deg p = 0) ==> (p = |0|) \/ (?h. h IN R /\ h <> #0 /\ (p = [h]))``,
  rw_tac std_ss[poly_def_alt] >>
  `(p = |0|) \/ ?h. h IN R /\ (p = [h])` by metis_tac[poly_deg_weak_eq_zero] >-
  rw_tac std_ss[] >>
  metis_tac[LAST_CONS]);

(* Theorem: p <> |0| /\ (deg p = 0) <=> ?c. c IN R /\ c <> #0 /\ p = [c] *)
(* Proof:
   If part: p <> |0| /\ (deg p = 0) ==> ?c. c IN R /\ c <> #0 /\ p = [c]
      True by poly_deg_eq_zero.
   Only-if part: ?c. c IN R /\ c <> #0 /\ p = [c] ==> p <> |0| /\ (deg p = 0)
        c <> #0 ==> [c] <> #0      by poly_zero
   and  deg [c] = 0                by poly_deg_const
*)
val poly_deg_eq_0 = store_thm(
  "poly_deg_eq_0",
  ``!p. poly p ==> (p <> |0| /\ (deg p = 0) <=> ?c. c IN R /\ c <> #0 /\ (p = [c]))``,
  rw_tac std_ss[EQ_IMP_THM] >-
  metis_tac[poly_deg_eq_zero] >>
  rw[]);

(* Theorem: deg (- p) = deg p *)
(* Proof:
   Since poly p ==> weak p, deg (-p) = deg p   by poly_deg_weak_neg.
*)
val poly_deg_neg = store_thm(
  "poly_deg_neg",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (deg (- p) = deg p)``,
  rw[poly_deg_weak_neg, poly_neg_def]);

(* Theorem: deg (c * p) <= deg p *)
(* Proof:
      deg (c * p)
    = deg (chop (c o p))   by poly_cmult_def
   <= deg (c o p)          by poly_deg_chop, weak_cmult_weak
    = deg p                by poly_deg_weak_cmult
*)
val poly_deg_cmult = store_thm(
  "poly_deg_cmult",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !c. c IN R ==> deg (c * p) <= deg p``,
  metis_tac[poly_cmult_def, poly_deg_chop, poly_deg_weak_cmult, poly_is_weak, weak_cmult_weak]);

(* Theorem: if deg p <> deg q, then (p + q) <> |0|, or
            if p + q = |0| then deg p = deg q  *)
(* Proof:
        p + q = |0|
   <==> p + q = []             by poly_zero
   ==>  p = -q                 by poly_add_eq_zero
   ==> deg p = deg -q = deg q  by poly_deg_neg
*)
val poly_deg_eq = store_thm(
  "poly_deg_eq",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ (p + q = |0|) ==> (deg p = deg q)``,
  metis_tac[poly_add_eq_zero, poly_deg_neg, poly_zero]);

(* Theorem: if deg p <> deg q, then ~zerop (p + q), or
            if zerop (p + q), then deg p = deg q  *)
(* Proof:
   If p = |0|, then |0| + q = q, so q = |0|, hence deg p = deg q.
   If q = |0|, then p + |0| = p, so p = |0|, hence deg p = deg q.
   If p <> |0| and q <> |0|, then p + q = |0|, hence deg p = deg q by poly_deg_eq.
*)
val poly_deg_equal = store_thm(
  "poly_deg_equal",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ zerop (p + q) ==> (deg p = deg q)``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  metis_tac[poly_add_lzero, zero_poly_zero_poly, poly_deg_zero, poly_zero] >>
  metis_tac[poly_add_poly, zero_poly_zero_poly, poly_deg_eq, poly_zero]);

(* ------------------------------------------------------------------------- *)
(* Problem 1: establish degree of polynomial addition.                       *)
(* This requires a case study: [a] + [b;c] = [a + b; c]                      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Degree of Polynomial Addition.                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: deg (p + q) <= MAX (deg p) (deg q) *)
(* Proof:
     deg (p + q)
   = deg (chop (p || q))     by poly_add_def
   <= deg (p || q)           by poly_deg_chop
   = MAX (deg p) (deg q)     by poly_deg_weak_add
*)
val poly_deg_add = store_thm(
  "poly_deg_add",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> deg (p + q) <= MAX (deg p) (deg q)``,
  metis_tac[poly_add_def, poly_deg_weak_add, poly_deg_chop, poly_is_weak, weak_add_weak]);

(* Thereom: deg (p - q) <= MAX (deg p) (deg q) *)
(* Proof:
       deg (p - q)
     = deg (p + -q)           by poly_sub_def
    <= MAX (deg p) (deg -q)   by poly_deg_add
    <= MAX (deg p) (deg q)    by poly_deg_neg
*)
val poly_deg_sub = store_thm(
  "poly_deg_sub",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> deg (p - q) <= MAX (deg p) (deg q)``,
  metis_tac[poly_sub_def, poly_deg_add, poly_deg_neg, poly_neg_poly]);

(* ------------------------------------------------------------------------- *)
(* Problem 2: establish degree of polynomial multiplication.                 *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Degree of Polynomial Multiplication.                                      *)
(* ------------------------------------------------------------------------- *)

(* Note: in Z_6,
   (2x) * (3x) = [], deg (2x) = deg (3x) = 1.
   (2x + 1) * (3x + 1) = 5x + 1,   deg (2x+1) = deg (3x+1) = deg (5x + 1) = 1.

   However, deg ((2x + 1) o (3x + 1)) = deg (0 x^2 + 5x + 1) = 2 = 1 + 1.
*)

(* The one below requires |0|, not [], for poly_mult_lzero and poly_mult_rzero, but last metis_tac needs poly_zero. *)

(* Theorem: deg (p * q) <= deg p + deg q. *)
(* Proof:
   If p = |0|, true by poly_mult_lzero.
   If q = |0|, true by poly_mult_rzero.
   If p <> |0| and q <> |0|,
      deg (p * q)
    = deg (chop (p o q))     by poly_mult_def
   <= deg (p o q)            by poly_deg_chop
    = deg p + deg q          by poly_deg_weak_mult, p <> |0| and q <> |0|
*)
val poly_deg_mult = store_thm(
  "poly_deg_mult",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> (deg (p * q) <= deg p + deg q)``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[] >>
  Cases_on `q = |0|` >-
  rw[] >>
  metis_tac[poly_mult_def, poly_deg_weak_mult, poly_deg_chop, poly_is_weak, weak_mult_weak, poly_zero]);

(* ------------------------------------------------------------------------- *)
(* Polynomial leading coefficient.                                           *)
(* ------------------------------------------------------------------------- *)
(* Theorem: poly p ==> lead p IN R. *)
(* Proof: by poly_is_weak, weak_lead_element. *)
val poly_lead_element = store_thm(
  "poly_lead_element",
  ``!r:'a ring. Ring r ==> !p. poly p ==> lead p IN R``,
  rw[weak_lead_element]);

val _ = export_rewrites["poly_lead_element"];

(* Theorem: poly p /\ p <> |0| ==> lead p <> #0 *)
(* Proof: by poly_cons_last_nonzero. *)
val poly_lead_nonzero = store_thm(
  "poly_lead_nonzero",
  ``!p. poly p /\ p <> |0| ==> lead p <> #0``,
  metis_tac[poly_lead_alt, poly_cons_last_nonzero, list_CASES, poly_zero]);

val _ = export_rewrites ["poly_lead_nonzero"];

(* Theorem: !p. poly p ==> ((lead p = #0) <=> (p = |0|)) *)
(* Proof:
   If part: poly p /\ (lead p = #0) ==> (p = |0|)
      By contradiction, suppose p <> |0|.
      Then lead p <> #0              by poly_lead_nonzero
      which contradicts p = #0.
   Only-if part: p = |0| ==> lead p = #0
      True by poly_lead_zero.
*)
val poly_lead_eq_zero = store_thm(
  "poly_lead_eq_zero",
  ``!p. poly p ==> ((lead p = #0) <=> (p = |0|))``,
  metis_tac[poly_lead_nonzero, poly_lead_zero]);

(* Theorem: poly p /\ p <> |0| <=> weak p /\ lead p <> #0 *)
(* Proof:
   If part: poly p /\ p <> |0| ==> weak p /\ lead p <> #0
     True by poly_weak, poly_lead_nonzero.
   Only-if part: weak p /\ lead p <> #0 ==> poly p /\ p <> |0|
     (1) weak p /\ lead p <> #0 ==> poly p
         By induction on p.
         Base case: weak [] ==> lead [] <> #0 ==> poly []
           True since poly []   by zero_poly_poly
         Step case: weak p ==> lead p <> #0 ==> poly p ==> !h. weak (h::p) ==> lead (h::p) <> #0 ==> poly (h::p)
           Since weak (h::p) = h IN R /\ weak p  by weak_cons
           If p = |0|,
           lead (h::p) = lead [h] = h <> #0      by poly_lead_const
           hence poly [h]                        by poly_nonzero_element_poly
           If p <> |0|,
           Hence lead (h::p) = lead p <> #0      by poly_lead_cons
           Now   poly p                          by induction hypothesis
           poly p and p <> [] ==> ~zerop p       by poly_nonzero_nonzero
           Hence ~zerop (h::p)                   by zero_poly_cons
           With h IN R, poly p, ~zerop (h::p), poly (h::p)  by poly_cons_poly.
     (2) weak p /\ lead p <> #0 ==> p <> []
           True by by poly_lead_of_zero.

*)
val poly_nonzero_lead_nonzero = store_thm(
  "poly_nonzero_lead_nonzero",
  ``!p. poly p /\ p <> |0| <=> weak p /\ lead p <> #0``,
  rw [EQ_IMP_THM] >| [
    Induct_on `p` >-
    rw [] >>
    rw_tac std_ss[weak_cons] >>
    Cases_on `p = |0|` >-
    metis_tac [poly_lead_const, poly_nonzero_element_poly, poly_zero] >>
    metis_tac [poly_lead_cons, poly_nonzero_nonzero, zero_poly_cons, poly_cons_poly, poly_zero],
    metis_tac [poly_lead_of_zero]
  ]);

(* Theorem: Ring r ==> !p. poly p ==> (lead (- p) = - (lead p)) *)
(* Proof:
   By induction on p.
   Base case: poly [] ==> (lead (-[]) = -lead [])
     LHS = lead (-[])
         = lead []        by poly_neg_of_zero
         = #0             by poly_lead_of_zero
         = - #0           by ring_neg_zero
         = - lead []      by poly_lead_of_zero
         = RHS
   Step case: poly p ==> (lead (-p) = -lead p) ==>
        !h. poly (h::p) ==> (lead (-(h::p)) = -lead (h::p))
     poly (h::p) ==> h IN R /\ poly p       by poly_cons_poly
     poly (h::p) ==> poly (-(h::p))         by poly_neg_poly
     If p = |0|,
        h <> #0                             by poly_cons_property
        lead (-[h])
      = lead ([-h])                         by poly_neg_nonzero, h <> #0
      = -h                                  by poly_lead_const
      = - lead [h]                          by poly_lead_const
     If p <> |0|,
       -p <> |0|                            by poly_neg_eq_zero
       lead (-(h::p))
     = lead (-h::-p)                        by poly_neg_cons
     = lead (-p)                            by poly_lead_cons, -p <> |0|
     = - lead p                             by induction hypothesis
     = - lead (h::p)                        by poly_lead_cons, p <> |0|
*)
val poly_lead_negate = store_thm(
  "poly_lead_negate",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (lead (- p) = - (lead p))``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[] >>
  Cases_on `p = |0|` >| [
    `h <> #0` by metis_tac[poly_cons_property, poly_zero] >>
    `h IN R /\ -h IN R` by metis_tac[poly_cons_poly, ring_neg_element] >>
    rw[poly_neg_nonzero, poly_lead_const],
    `h IN R /\ poly p` by metis_tac[poly_cons_poly] >>
    rw_tac std_ss[poly_neg_eq_zero, poly_neg_cons, poly_lead_cons]
  ]);

(* ------------------------------------------------------------------------- *)
(* Relationship of Polynomials with weak operations (via lead).              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: weak p /\ c * lead p <> #0 ==> lead (c * p) = c * lead p *)
(* Proof:
   Since weak p ==> weak (c o p)  by weak_cmult_weak
   Given  c * lead p <> #0
   this gives poly (c o p)        by weak_lead_cmult, poly_nonzero_lead_nonzero
     lead (c * p)
   = lead (chop (c o p))          by poly_cmult_def
   = lead (c o p)                 by poly_chop_poly
   = c * lead p                   by weak_lead_cmult
*)
val weak_lead_cmult_nonzero = store_thm(
  "weak_lead_cmult_nonzero",
  ``!r:'a ring. Ring r ==>
    !p c. weak p /\ c IN R /\ c * lead p <> #0 ==> (lead (c * p) = c * lead p)``,
  rpt strip_tac >>
  `weak (c o p)` by rw [] >>
  `lead (c o p) <> #0` by metis_tac [weak_lead_cmult] >>
  `poly (c o p)` by metis_tac [poly_nonzero_lead_nonzero] >>
  rw_tac std_ss[poly_cmult_def, poly_chop_poly, weak_lead_cmult]);

(* Theorem: weak p /\ c * lead p <> #0 ==> c * p) = deg p *)
(* Proof:
   Since weak p ==> weak (c o p)  by weak_cmult_weak
   Given  c * lead p <> #0
   this gives poly (c o p)        by weak_lead_cmult, poly_nonzero_lead_nonzero
     deg (c * p)
   = deg (chop (c o p))           by poly_deg_def
   = deg (c o p)                  by poly_chop_poly
   = deg p                        by weak_deg_cmult
*)
val weak_deg_cmult_nonzero = store_thm(
  "weak_deg_cmult_nonzero",
  ``!r:'a ring. Ring r ==>
    !p c. weak p /\ c IN R /\ c * lead p <> #0 ==> (deg (c * p) = deg p)``,
  rpt strip_tac >>
  `weak (c o p)` by rw [] >>
  `lead (c o p) <> #0` by metis_tac [weak_lead_cmult] >>
  `poly (c o p)` by metis_tac [poly_nonzero_lead_nonzero] >>
  rw_tac std_ss[poly_cmult_def, poly_chop_poly, weak_deg_cmult]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Scalar Multiplication (when c * lead p <> #0)                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: c * lead p <> #0, poly p ==> poly (c o p) *)
(* Proof:
   If p = |0|, c o |0| = |0|, hence true.
   Since poly p = weak p /\ ((p = |0|) \/ LAST p <> #0)   by poly_def_alt
   If p <> |0|, c o p <> |0|      by weak_cmult_eq_of_zero, poly_zero
   lead (c o p) = c * lead p      by weak_lead_cmult
                <> #0             by given
   LAST (c o p) = c * LAST p      by weak_cmult_map, LAST_MAP, p <> []
                = c * lead p      by poly_lead_alt
   hence poly (c o p)             by poly_def_alt
*)
val poly_weak_cmult_poly = store_thm(
  "poly_weak_cmult_poly",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !c. c IN R /\ c * lead p <> #0 ==> poly (c o p)``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[] >>
  `weak p /\ weak (c o p) /\
   (lead (c o p) = c * lead p)` by rw[weak_cmult_weak, weak_lead_cmult] >>
  metis_tac[poly_def_alt, poly_lead_alt, weak_cmult_eq_of_zero,
            weak_cmult_map, LAST_MAP, poly_zero]);

(* Theorem: c * lead p <> #0, poly p ==> c * p = c o p *)
(* Proof:
     c * p
   = chop (c o p)    by poly_cmult_def
   = c o p           by poly_weak_cmult_poly, poly_chop_poly
*)
val poly_weak_cmult = store_thm(
  "poly_weak_cmult",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !c. c IN R /\ c * lead p <> #0 ==> (c * p = c o p)``,
  rw_tac std_ss[poly_cmult_def, poly_weak_cmult_poly, poly_chop_poly]);

(* Theorem: c * p = |0| ==> p = |0| or c * lead p = #0 *)
(* Counter-Example for converse:
In Z_6, 2 * (3x^2 + x + 3) = 2x, i.e. p <> |0|, c * lead p = #0, but c * p <> |0|
*)
(* Proof:
   If part: c * p = |0| ==> p = |0| or c * lead p = #0
   By contradiction,
   suppose p <> |0| and c * lead p <> #0,
      |0| = c * p = c o p     by poly_weak_cmult, c * lead p <> #0
   ==> p = |0|                by weak_cmult_eq_zero
   contradicts p <> |0|.

   Better:
   If c * lead <> #0,
       c * p = |0|
   ==> c o p = |0|     by poly_weak_cmult, c * lead p <> #0
   ==>     p = |0|     by weak_cmult_eq_zero
*)
val poly_cmult_eq_zero = store_thm(
  "poly_cmult_eq_zero",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !c. c IN R ==>
   ((c * p = |0|) ==> (p = |0|) \/ (c * lead p = #0))``,
  metis_tac[poly_weak_cmult, weak_cmult_eq_zero, poly_is_weak]);

(* ------------------------------------------------------------------------- *)
(* Problem 3: establish polynomial leads for addition and multiplication.    *)
(* poly p /\ poly q /\ deg p < deg q ==> lead (p + q) = lead q               *)
(* poly p /\ poly q /\ p * q <> [] ==> lead (p * q) = lead p * lead q       *)
(* ------------------------------------------------------------------------- *)

(* The following is the first step to derive theorems for lead (p + q) and lead (p * q). *)
(* Actually, lead (p + q) has no good theorem, only:
   If deg p < deg q,  lead (p + q) = lead q
   If deg q < deg p,  lead (p + q) = lead p
   If deg p = deg p,  lead (p + q) is unpredictable from lead p and lead q,
      only if lead p + lead q <> #0, then lead (p + q) = lead p + lead q in this case.
   However, lead (p * q) = lead p * lead q, always.
*)

(* Theorem: weak p /\ weak q /\ deg p < deg q ==> lead (p || q) = lead q *)
(* Proof: by induction on p and q.
   Base case: lead ([] || q) = lead q
      true by weak_add_of_lzero.
   Step case: induct on q.
      Base case: deg (h::p) < deg [] ==> lead ((h::p) || []) = lead []
         true by poly_deg_of_zero, false assumption.
      Step case: lead (p || q) = lead q ==> lead ((h::p) || (h'::q)) = lead (h'::q)
         If p = |0|, q = |0|, deg [h] < deg [h'] is false.
         If p = |0|, q <> |0|, true by poly_lead_cons.
         If p <> |0|, q = |0|, deg (h::p) < deg [h'] is false.
         If p <> |0|, q <> |0|, p || q <> |0| by weak_add_eq_zero
         hence true by poly_lead_cons, poly_deg_cons, and induction hypothesis.
*)
val weak_lead_weak_add = store_thm(
  "weak_lead_weak_add",
  ``!r:'a ring p q. weak p /\ weak q /\ deg p < deg q ==> (lead (p || q) = lead q)``,
  strip_tac >>
  Induct >-
  rw[] >>
  strip_tac >>
  Induct >-
  rw[] >>
  rpt strip_tac >>
  `h IN R /\ h' IN R /\ weak p /\ weak q` by metis_tac [weak_cons] >>
  `lead ((h::p) || (h'::q)) = lead (h + h'::p || q)` by rw_tac std_ss[weak_add_cons] >>
  Cases_on `p = |0|` >| [
    Cases_on `q = |0|` >-
    full_simp_tac std_ss [poly_deg_const, poly_zero] >>
    rw_tac std_ss[poly_lead_cons, weak_add_lzero],
    Cases_on `q = |0|` >-
    full_simp_tac std_ss [poly_deg_const, poly_zero] >>
    metis_tac [weak_add_eq_zero, poly_lead_cons, poly_cons_poly, poly_deg_cons, LESS_MONO_EQ]
  ]);
(* more condition than: poly_deg_weak_mult:
   |- !r. Ring r ==> !p q. p <> |0| /\ q <> |0| ==> (deg (p o q) = deg p + deg q) : thm
*)

(* Theorem: lead p * lead q <> #0 ==> lead (p o q) = lead p * lead q *)
(* Proof: by induction on p.
   First, lead p * lead q <> #0 ==>
     lead p <> #0, lead q <> #0       by ring_mult_lzero, ring_mult_rzero
     i.e. p <> |0|, q <> |0|          by poly_lead_zero

   Base case: weak [] ==> lead [] * lead q <> #0 ==> (lead ([] o q) = lead [] * lead q)
     lead ([] o q)
   = lead []            by weak_mult_zero, poly_zero
   = #0                 by poly_lead_of_zero
   = #0 * lead q        by ring_mult_lzero
   = lead [] * lead q   by poly_lead_zero
   Step case: weak p ==> lead p * lead q <> #0 ==> (lead (p * q) = lead p * lead q) ==>
              !h. weak (h::p) ==> lead (h::p) * lead q <> #0 ==> (lead ((h::p) o q) = lead (h::p) * lead q)
     if p = |0|,
       lead ([h] o q)
     = lead (h o q)            by weak_mult_const
     = h * lead q              by weak_lead_cmult
     = lead [h] * lead q       by poly_lead_const
     If p <> |0|,
       lead (h::p) = lead p             by poly_lead_cons
       condition:      lead (h::p) * lead q <> #0
       is the same as  lead p * lead q <> #0   by above
       hence lead p <> #0               by lead p = lead (h::p)
       and deg (p o q) = deg p + deg q  by poly_deg_weak_mult
       also   p o q <> |0|              by weak_mult_eq_zero
       thus deg ((p o q) >> 1)
          = SUC (deg (p o q))           by poly_deg_shift_1
       since  deg (h o q) = deg q       by weak_deg_cmult
       hence  deg (h o q) < deg ((p o q) >> 1),
       Now,
         lead ((h::p) o q)
       = lead (h o q || (p o q) >> 1)   by weak_mult_cons
       = lead ((p o q) >> 1)            by weak_lead_weak_add
       = lead (p o q)                   by poly_lead_shift
       = lead p * lead q                by induction hypothesis
       = lead (h::p) * lead q           by poly_lead_cons above
*)
val weak_lead_weak_mult_nonzero = store_thm(
  "weak_lead_weak_mult_nonzero",
  ``!r:'a ring. Ring r ==>
    !p q. weak p /\ weak q /\ lead p * lead q <> #0 ==> (lead (p o q) = lead p * lead q)``,
  rpt strip_tac >>
  `lead p <> #0 /\ lead q <> #0` by metis_tac[ring_mult_lzero, ring_mult_rzero, weak_lead_element] >>
  `poly p /\ p <> |0| /\ poly q /\ q <> |0|` by metis_tac [poly_nonzero_lead_nonzero] >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[weak_cons] >>
  Cases_on `p = |0|` >-
  metis_tac [weak_mult_const, weak_lead_cmult, poly_lead_const, poly_zero] >>
  `lead (h::p) = lead p` by rw_tac std_ss[poly_lead_cons] >>
  `lead p * lead q <> #0` by metis_tac [] >>
  `deg (p o q) = deg p + deg q` by rw_tac std_ss[poly_deg_weak_mult] >>
  `p o q <> |0|` by metis_tac [weak_mult_eq_zero] >>
  (`deg ((p o q) >> 1) = SUC (deg (p o q))` by rw_tac std_ss[poly_deg_shift_1]) >>
  `deg (h o q) = deg q` by rw_tac std_ss[weak_deg_cmult] >>
  (`deg (h o q) < deg ((p o q) >> 1)` by decide_tac) >>
  (`weak (h o q) /\ weak ((p o q) >> 1)` by rw[]) >>
  metis_tac [weak_mult_cons, weak_lead_weak_add, poly_lead_shift, poly_nonzero_lead_nonzero]);

(* Theorem: lead p * lead q <> #0 ==> lead (p * q) = lead p * lead q *)
(* Proof:
   Since weak p /\ weak q ==> weak (p o q)  by weak_mult_weak
   and   lead p * lead q <> #0 ==>
         lead (p o q) = lead p * lead q     by weak_lead_weak_mult_nonzero
   we have  poly (p o q)                    by poly_nonzero_lead_nonzero
   Thus  p * q = chop (p o q) = p o q       by poly_chop_poly
   and the result follows.
*)
val weak_lead_mult_nonzero = store_thm(
  "weak_lead_mult_nonzero",
  ``!r:'a ring. Ring r ==>
    !p q. weak p /\ weak q /\ lead p * lead q <> #0 ==> (lead (p * q) = lead p * lead q)``,
  metis_tac [weak_lead_weak_mult_nonzero, poly_nonzero_lead_nonzero, poly_chop_poly, weak_mult_weak, poly_mult_def]);

(* Theorem: lead p * lead q <> #0 ==> deg (p * q) = deg p + deg q *)
(* Proof:
   lead p * lead q <> #0 ==>
   lead p <> #0 /\ lead q <> #0          by ring_mult_lzero, ring_mult_rzero
   hence p <> |0| and q <> |0|           by poly_nonzero_lead_nonzero
   so deg (p o q) = deg p + deg q        by poly_deg_weak_mult
   But weak p /\ weak q ==> weak (p o q)       by weak_mult_weak
   and lead (p o q) = lead p * lead q <> #0    by weak_lead_weak_mult_nonzero
   hence poly (p o q)                          by poly_nonzero_lead_nonzero
   Thus  deg (p * q)
       = deg (chop (p o q))              by poly_mult_def
       = deg (p * q)                     by poly_chop_poly
       = deg p + deg q                   by above
*)
val weak_deg_mult_nonzero = store_thm(
  "weak_deg_mult_nonzero",
  ``!r:'a ring. Ring r ==>
    !p q. weak p /\ weak q /\ lead p * lead q <> #0 ==> (deg (p * q) = deg p + deg q)``,
  rpt strip_tac >>
  `lead p <> #0 /\ lead q <> #0` by metis_tac[ring_mult_lzero, ring_mult_rzero, weak_lead_element] >>
  `p <> |0| /\ q <> |0|` by metis_tac [poly_nonzero_lead_nonzero] >>
  `weak (p o q)` by rw[] >>
  `lead (p o q) = lead p * lead q` by rw_tac std_ss[weak_lead_weak_mult_nonzero] >>
  `poly (p o q)` by metis_tac [poly_nonzero_lead_nonzero] >>
  rw_tac std_ss[poly_mult_def, poly_chop_poly, poly_deg_weak_mult]);

(* Since weak (p || q), lead (p || q) = lead q <> #0 by poly q, hence poly (p || q),
   and lead (p || q) = lead (chop (p || q)) = lead (p + q)    by poly_chop_poly *)

(* Theorem: poly p /\ poly q /\ deg p <> deg q ==> poly (p || q) *)
(* Proof:
   If deg p < deg q, apply weak_lead_weak_add
      lead (p || q) = lead q = LAST q <> #0, hence true by poly_def_alt.
   Similarly for deg q < deq p.
*)
val poly_weak_add_poly = store_thm(
  "poly_weak_add_poly",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ deg p <> deg q ==> poly (p || q)``,
  rpt strip_tac >>
  `weak p /\ weak q` by rw_tac std_ss[poly_is_weak] >>
  Cases_on `(p = |0|) \/ (q = |0|)` >-
  metis_tac[weak_add_lzero, weak_add_rzero] >>
  `p <> |0| /\ q <> |0|` by metis_tac[] >>
  `weak (p || q)` by rw_tac std_ss[weak_add_weak] >>
  `p || q <> |0|` by rw_tac std_ss[weak_add_eq_zero] >>
  Cases_on `deg p < deg q` >-
  metis_tac[poly_lead_alt, poly_def_alt, weak_lead_weak_add] >>
  `deg q < deg p` by decide_tac >>
  metis_tac[poly_lead_alt, poly_def_alt, weak_lead_weak_add, weak_add_comm]);

(* Theorem: poly p /\ poly q ==> p + q = p || q *)
(* Proof:
     p + q
   = chop (p || q)    by poly_add_def
   = p || q           by poly_chop_poly, since poly (p || q) by poly_weak_add_poly
*)
val poly_weak_add = store_thm(
  "poly_weak_add",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ deg p <> deg q ==> (p + q = p || q)``,
  rw_tac std_ss[poly_add_def, poly_chop_poly, poly_weak_add_poly]);

(* Theorem: poly p /\ poly q /\ deg p < deg q ==> lead (p + q) = lead q *)
(* Proof:
     lead (p + q)
   = lead (p || q)     by poly_weak_add
   = lead q            by weak_lead_weak_add, poly_is_weak
*)
val poly_lead_add_less = store_thm(
  "poly_lead_add_less",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ deg p < deg q ==> (lead (p + q) = lead q)``,
  rpt strip_tac >>
  `deg p <> deg q` by decide_tac >>
  rw[poly_weak_add, weak_lead_weak_add]);

(* Theorem: poly p /\ poly q /\ deg q < deg p ==> (lead (p + q) = lead p) *)
(* Proof: by poly_lead_add_less, poly_add_comm. *)
val poly_lead_add_less_comm = store_thm(
  "poly_lead_add_less_comm",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ deg q < deg p ==> (lead (p + q) = lead p)``,
  metis_tac[poly_lead_add_less, poly_add_comm]);

(* Theorem: if deg p < deg q, then deg (p + q) = deg q *)
(* Proof:
     deg (p + q)
   = deg (p || q)          by poly_weak_add
   = MAX (deg p) (deg q)   by poly_deg_weak_add
   = deg q                 by MAX_DEF
*)
val poly_deg_add_less = store_thm(
  "poly_deg_add_less",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ (deg p) < (deg q) ==> (deg (p + q) = deg q)``,
  rpt strip_tac >>
  `deg p <> deg q` by decide_tac >>
  rw[poly_weak_add, poly_deg_weak_add, MAX_DEF]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q /\ deg q < deg p ==> (deg (p + q) = deg p) *)
(* Proof by poly_deg_add_less, poly_add_comm: *)
val poly_deg_add_less_comm = store_thm(
  "poly_deg_add_less_comm",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ deg q < deg p ==> (deg (p + q) = deg p)``,
  metis_tac[poly_deg_add_less, poly_add_comm]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q /\ (deg p = 0) ==> (deg (p + q) = deg q) *)
(* Proof:
   If deg q = 0,
          deg (p + q)
       <= MAX (deg p) (deg q)       by poly_deg_add
      But MAX (deg p) (deg q) = 0   by MAX_0
      Hence deg (p + q) = 0         by LESS_EQ_0
   If deg q <> 0,
      Then 0 < deg q                by NOT_ZERO_LT_ZERO
          deg (p + q) = deg q       by poly_deg_add_less
*)
val poly_deg_add_deg_zero = store_thm(
  "poly_deg_add_deg_zero",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ (deg p = 0) ==> (deg (p + q) = deg q)``,
  rpt strip_tac >>
  Cases_on `deg q = 0` >| [
    `deg (p + q) <= 0` by metis_tac[poly_deg_add, MAX_0] >>
    decide_tac,
    `0 < deg q` by decide_tac >>
    rw[poly_deg_add_less]
  ]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q /\ deg q < deg p ==> lead (p - q) = lead p *)
(* Proof:
   Note that poly q ==> poly (-q)    by poly_neg_poly
        and  deg (-q) = deg q        by poly_deg_neg
     lead (p - q)
   = lead (p + -q)    by poly_add_def
   = lead (-q + p)    by poly_add_comm
   = lead p           by poly_lead_add_less
*)
val poly_lead_sub_less = store_thm(
  "poly_lead_sub_less",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ deg q < deg p ==> (lead (p - q) = lead p)``,
  rw[] >>
  `lead (p + -q) = lead (-q + p)` by rw[poly_add_comm] >>
  rw[poly_deg_neg, poly_lead_add_less]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q /\ deg q < deg p ==> deg (p - q) = deg p *)
(* Proof:
   Note that deg (-p) = deg p    by poly_deg_neg
     deg (p - q)
   = deg (-(p - q))   by poly_deg_neg
   = deg (q - p)      by poly_neg_sub
   = deg (q + -p)     by poly_sub_def
   = deg (-p)         by poly_deg_add_less, deg q < deg p = deg (-p)
   = deg p            by poly_deg_neg
*)
val poly_deg_sub_less = store_thm(
  "poly_deg_sub_less",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ deg q < deg p ==> (deg (p - q) = deg p)``,
  rpt strip_tac >>
  `deg (p - q) = deg (-(p - q))` by rw[poly_deg_neg] >>
  `_ = deg (q - p)` by rw_tac std_ss[poly_neg_sub] >>
  `_ = deg (q + -p)` by rw[] >>
  rw[poly_deg_add_less, poly_deg_neg]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q /\ (deg q = 0) ==> (deg (p - q) = deg p) *)
(* Proof:
   If deg p = 0,
          deg (p - q)
       <= MAX (deg p) (deg q)       by poly_deg_sub
      But MAX (deg p) (deg q) = 0   by MAX_0
      Hence deg (p - q) = 0         by LESS_EQ_0
   If deg p <> 0,
      Then 0 < deg p                by NOT_ZERO_LT_ZERO
          deg (p + q) = deg q       by poly_deg_sub_less
*)
val poly_deg_sub_deg_zero = store_thm(
  "poly_deg_sub_deg_zero",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ (deg q = 0) ==> (deg (p - q) = deg p)``,
  rpt strip_tac >>
  Cases_on `deg p = 0` >| [
    `deg (p - q) <= 0` by metis_tac[poly_deg_sub, MAX_0] >>
    decide_tac,
    `0 < deg p` by decide_tac >>
    rw[poly_deg_sub_less]
  ]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Theorems -- CONS theorems and SING theorems.                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (h::t) * q = h * q + (t * q) >> 1 *)
(* Proof:
     (h::t) * q
   = chop ((h::t) o q)                           by poly_mult_def
   = chop (h o q || (t o q) >> 1)                by weak_mult_cons
   = chop (chop (h o q) || chop ((t o q) >> 1))  by poly_chop_add_chop
   = chop (chop (h o q) || (chop (t o q) >> 1))  by poly_chop_shift
   = chop (h * q || (chop (t o q) >> 1))         by poly_cmult_def
   = chop (h * q || (t * q) >> 1)                by poly_mult_def
   = h * q + (t * q) >> 1                        by poly_add_def
*)
val poly_mult_cons = store_thm(
  "poly_mult_cons",
  ``!r:'a ring. Ring r ==> !h t q. weak (h::t) /\ weak q ==> ((h::t) * q = h * q + (t * q) >> 1)``,
  rw_tac std_ss[weak_cons] >>
  (`weak (h o q) /\ weak (t o q >> 1)` by rw[]) >>
  `(h::t) * q = chop ((h::t) o q)` by rw_tac std_ss[poly_mult_def] >>
  (`_ = chop (chop (h o q) || chop (t o q) >> 1)` by rw_tac std_ss[weak_mult_cons, poly_chop_add_chop, poly_chop_shift]) >>
  rw_tac std_ss[poly_cmult_def, poly_mult_def, poly_add_def]);

(* Theorem: poly (h::t) /\ poly q ==> (h::t) * q = h * q + (t * q) >> 1 *)
(* Proof: by poly_mult_cons, poly_is_weak. *)
val poly_mult_cons_over = store_thm(
  "poly_mult_cons_over",
  ``!r:'a ring. Ring r ==> !h t q. poly (h::t) /\ poly q ==> ((h::t) * q = h * q + (t * q) >> 1)``,
  rw[poly_mult_cons]);

(* Theorem: poly p ==> [k] * p = k * p *)
(* Proof:
     [k] * p
   = k * p + ( |0| * p) >> 1   by poly_mult_cons, weak_of_zero
   = k * p + ( |0|) >> 1       by poly_mult_lzero
   = k * p + |0|               by poly_shift_of_zero
   = k * p                     by poly_add_rzero
*)
val poly_mult_lconst = store_thm(
  "poly_mult_lconst",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !k. k IN R ==> ([k] * p = k * p)``,
  rpt strip_tac >>
  (`[k] * p = k * p + ( |0| * p) >> 1` by rw[poly_mult_cons]) >>
  (`_ = k * p + ( |0|) >> 1` by rw_tac std_ss[poly_mult_lzero, poly_zero]) >>
  rw[]);

(* Theorem: Ring r ==> !p. poly p ==> !k. k IN R ==> (p * [k] = k * p) *)
(* Proof:
   If k = #0,
      Then p * [#0]
         = p * chop [#0]     by poly_mult_const_comm
         = p * |0|           by poly_chop_const_zero
         = |0|               by poly_mult_rzero
         = #0 * p            by poly_cmult_lzero
   If k <> #0,
      Then poly [k]          by poly_nonzero_element_poly
        so p * [k]
         = [k] * p           by poly_mult_comm
         = k * p             by poly_mult_lconst
*)
val poly_mult_rconst = store_thm(
  "poly_mult_rconst",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !k. k IN R ==> (p * [k] = k * p)``,
  rpt strip_tac >>
  Cases_on `k = #0` >-
  metis_tac[poly_mult_const_comm, poly_chop_const_zero, poly_mult_rzero, poly_cmult_lzero] >>
  metis_tac[poly_nonzero_element_poly, poly_mult_comm, poly_mult_lconst]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Exponentiation.                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r /\ poly p ==> !n. poly (p ** n) *)
val poly_exp_poly = lift_ring_thm_with_goal "exp_element" "exp_poly"
   ``!r:'a ring. Ring r ==> !p. poly p ==> !n. poly (p ** n)``;
(* > val poly_exp_poly = |- !r. Ring r ==> !p. poly p ==> !n. poly (p ** n) : thm *)

val _ = export_rewrites ["poly_exp_poly"];

(* Theorem: Ring r /\ poly p ==> !n. p ** SUC n = p ** n * p *)
(* Proof:
     p ** SUC n
   = p * p ** n    by poly_exp_SUC
   = p ** n * p    by poly_mult_comm
*)
val poly_exp_suc = store_thm("poly_exp_suc",
    ``!r:'a ring. Ring r ==> !p. poly p ==> !n. p ** SUC n = p ** n * p``,
    metis_tac [poly_exp_SUC, poly_exp_poly, poly_mult_comm]);

(* Theorem: !p. p ** 0 = |1| *)
(* Proof: by monoid_exp_0 *)
val poly_exp_0 = save_thm("poly_exp_0", weak_exp_0);
(* val weak_exp_0 = |- !p. p ** 0 = |1|: thm *)

val _ = export_rewrites ["poly_exp_0"];

(* Theorem: Ring r /\ poly p ==> p ** 1 = p *)
val poly_exp_1 = lift_ring_thm_with_goal "exp_1" "exp_1"
    ``!r:'a ring. Ring r ==> !p. poly p ==> (p ** 1 = p)``;
(* > val poly_exp_1 = |- !r. Ring r ==> !p. poly p ==> (p ** 1 = p) : thm *)

val _ = export_rewrites ["poly_exp_1"];

(* Theorem: p ** 2 = p * p *)
(* Proof:
    p ** 2
  = p ** (SUC 1)    by TWO
  = p * p ** 1      by poly_exp_SUC
  = p * p           by poly_exp_1
*)
val poly_exp_2 = store_thm(
  "poly_exp_2",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (p ** 2 = p * p)``,
  metis_tac[TWO, poly_exp_SUC, poly_exp_1]);

(* Theorem: Ring r ==> !n. |0| ** n = if n = 0 then |1| else |0| *)
val poly_zero_exp = lift_ring_thm_with_goal "zero_exp" "zero_exp"
    ``!r:'a ring. Ring r ==> !n. |0| ** n = if n = 0 then |1| else |0|``;
(* > val poly_zero_exp = |- !r. Ring r ==> !n. |0| ** n = if n = 0 then |1| else |0| : thm *)

(* Theorem: !n. |1| ** n = |1| *)
(* Proof: by induction on n.
   Base case: |1| ** 0 = |1|
     True by poly_exp_0, poly_one_poly.
   Step case: |1| ** n = |1| ==> |1| ** SUC n = |1|
     |1| ** SUC n
   = |1| * |1| ** n   by poly_exp_SUC
   = |1| * |1|        by induction hypothesis
   = |1|              by poly_mult_one_one
*)
val poly_one_exp = store_thm(
  "poly_one_exp",
  ``!r:'a ring. Ring r ==> !n. ( |1| ** n = |1|)``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[]);

(* export simple result *)
val _ = export_rewrites ["poly_one_exp"];

(* Theorem: poly p ==> !n. (-p) ** n = if (EVEN n) then (p ** n) else (-(p ** n)) *)
(* Proof:
   By induction on n.
   Base case: -p ** 0 = if EVEN 0 then p ** 0 else -(p ** 0)
      LHS = -p ** 0
          = |1|                    by poly_exp_0, poly_neg_poly
      RHS = p ** 0                 by EVEN, EVEN 0 = T
          = |1| = LHS              by poly_exp_0
   Step case: -p ** n = if EVEN n then p ** n else -(p ** n) ==>
              -p ** SUC n = if EVEN (SUC n) then p ** SUC n else -(p ** SUC n)
      If EVEN n, ~EVEN (SUC n)     by EVEN
         -p ** SUC n
       = -p * (-p ** n)            by poly_exp_SUC
       = -p * p ** n               by induction hypothesis
       = -(p * p ** n)             by poly_mult_lneg
       = - p ** SUC n              by poly_exp_SUC
      If ~EVEN n, EVEN (SUC n)     by EVEN
         -p ** SUC n
       = -p * (-p ** n)            by poly_exp_SUC
       = -p * (-(p ** n))          by induction hypothesis
       = p * -(-(p ** n))          by poly_mult_lneg
       = p * p ** n                by poly_neg_neg
       = p ** SUC n                by poly_exp_SUC
*)
val poly_neg_exp = store_thm(
  "poly_neg_exp",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !n. (-p) ** n = if (EVEN n) then (p ** n) else (-(p ** n))``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw_tac std_ss[poly_exp_SUC, EVEN] >>
  rw[poly_mult_lneg]);

(* Theorem: poly p ==> p ** (n + m) = p ** n * p ** m *)
(* Proof:
   Since p in (PolyRing r), true by ring_exp_add.
*)
val poly_exp_add = store_thm(
  "poly_exp_add",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !n m. p ** (n + m) = p ** n * p ** m``,
  metis_tac[poly_add_mult_ring, ring_exp_add, poly_ring_property]);

(* Theorem: Ring r /\ poly p ==> !m n. (p ** (n * m) = (p ** n) ** m) *)
val poly_exp_mult = lift_ring_thm_with_goal "exp_mult" "exp_mult"
   ``!r:'a ring. Ring r ==> !p. poly p ==> !m n. p ** (n * m) = (p ** n) ** m``;
(* > val poly_exp_mult = |- !r. Ring r ==> !p. poly p ==> !m n. p ** (n * m) = (p ** n) ** m : thm *)

(* Theorem: Ring r ==> !p. poly p ==> !m n. (p ** m) ** n = (p ** n) ** m *)
(* Proof:
     (p ** m) ** n
   = p ** (m * n)       by poly_exp_mult
   = p ** (n * m)       by MULT_COMM
   = (p ** n) ** m      by poly_exp_mult
*)
val poly_exp_mult_comm = lift_ring_thm_with_goal "exp_mult_comm" "exp_mult_comm"
    ``!r:'a ring. Ring r ==> !p. poly p ==> !m n. (p ** m) ** n = (p ** n) ** m``;
(* > val poly_exp_mult_comm = |- !r. Ring r ==> !p. poly p ==> !m n. (p ** m) ** n = (p ** n) ** m: thm *)

(* Theorem: Ring r /\ poly p /\ poly q ==> !n. (p ** n) * (q ** n) = (p * q) ** n *)
val poly_mult_exp = lift_ring_thm_with_goal "mult_exp" "mult_exp"
   ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q ==> !n. (p * q) ** n = (p ** n) * (q ** n)``;
(* > val poly_mult_exp = |- !r. Ring r ==> !p q. poly p /\ poly q ==> !n. (p * q) ** n = p ** n * q ** n : thm *)

(* Theorem: c IN R ==> !n. (c * |1|) ** n = c ** n * |1| *)
(* Proof:
   By induction on n.
   Base case: (c * |1|) ** 0 = c ** 0 * |1|
      LHS = (c * |1|) ** 0 = |1|     by poly_exp_0
      RHS = c ** 0 * |1|
          = #1 * |1|                 by ring_exp_0
          = |1| = LHS                by poly_cmult_lone
   Step case: (c * |1|) ** n = c ** n * |1| ==>
              (c * |1|) ** SUC n = c ** SUC n * |1|\
        (c * |1|) ** SUC n
      = (c * |1|) * (c * |1|) ** n   by poly_exp_SUC
      = (c * |1|) * (c ** n * |1|)   by induction hypothesis
      = c * ( |1| * (c ** n * |1|))   by poly_cmult_mult
      = c * (c ** n * |1| * |1|)     by poly_mult_cmult
      = c * (c ** n * |1|)           by poly_mult_one_one
      = c * c ** n * |1|             by poly_cmult_cmult
      = c ** SUC n * |1|             by ring_exp_SUC
*)
val poly_cmult_one_exp = store_thm(
  "poly_cmult_one_exp",
  ``!r:'a ring. Ring r ==> !c. c IN R ==> !n. (c * |1|) ** n = c ** n * |1|``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw_tac std_ss[poly_exp_0, ring_exp_0, poly_cmult_lone, poly_one_poly] >>
  `(c * |1|) ** SUC n = c * (c ** n * |1|)` by rw[poly_exp_SUC, poly_cmult_mult, poly_mult_cmult] >>
  rw[poly_cmult_cmult, ring_exp_SUC]);

(* Theorem: c IN R /\ poly p ==> !n. (c * p) ** n = c ** n * p ** n *)
(* Proof:
     (c * p) ** n
   = ((c * |1|) * p) ** n           by poly_cmult_alt
   = (c * |1|) ** n * p ** n        by poly_mult_exp
   = (c ** n * |1|) * p ** n        by poly_cmult_one_exp
   = c ** n * ( |1| * p ** n)       by poly_cmult_mult
   = c ** n * p ** n                by poly_mult_lone
   Or by induction on n.
   Base case: (c * p) ** 0 = c ** 0 * p ** 0
      LHS = (c * p) ** 0 = |1|    by poly_exp_0
      RHS = c ** 0 * p ** 0
          = #1 * |1|                by ring_exp_0, poly_exp_0
          = |1| = LHS               by poly_cmult_lone
   Step case: (c * p) ** n = c ** n * p ** n ==>
              (c * p) ** SUC n = c ** SUC n * p ** SUC n
      (c * p) * SUC n
    = (c * p) * (c * p) ** n        by poly_exp_SUC
    = (c * p) * (c ** n * p ** n)   by induction hypothesis
    = c * (p * (c ** n * p ** n))   by poly_cmult_mult
    = c * (c ** n * p * p ** n)     by poly_mult_cmult
    = (c * c ** n) * p * p ** n     by poly_cmult_cmult
    = c ** SUC n * p ** SUC n       by by poly_exp_SUC
*)
val poly_cmult_exp = store_thm(
  "poly_cmult_exp",
  ``!r:'a ring. Ring r ==> !c p. c IN R /\ poly p ==> !n. (c * p) ** n = c ** n * p ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw[poly_exp_SUC, poly_cmult_mult, poly_mult_cmult, poly_cmult_cmult]);

(* Theorem: c IN R ==> [c] ** n = chop [c ** n] *)
(* Proof: by induction on n.
   Base case: [c] ** 0 = chop [c ** 0]
       [c] ** 0
     = |1|                        by poly_exp_0
     = chop [#1]                  by poly_one
     = chop [c ** 0]              by ring_exp_0
   Step case: [c] ** n = chop [c ** n] ==> [c] ** SUC n = chop [c ** SUC n]
      [c] ** SUC n
    = [c] * [c] ** n              by poly_exp_SUC
    = [c] * chop [c ** n]         by induction hypothesis
    = chop ([c] o chop [c ** n])  by poly_mult_def
    = chop ([c] o [c ** n])       by poly_chop_cmult
    = chop (c o [c ** n])         by weak_mult_const
    = chop [c * c ** n]           by weak_cmult_const
    = chop [c ** SUC n]           by ring_exp_SUC
*)
val poly_exp_const = store_thm(
  "poly_exp_const",
  ``!r:'a ring. Ring r ==> !c. c IN R ==> !n. [c] ** n = chop [c ** n]``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[poly_one] >>
  `[c] ** SUC n = [c] * [c] ** n` by rw[poly_exp_SUC] >>
  `_ = [c] * chop [c ** n]` by rw[] >>
  `_ = chop ([c] o chop [c ** n])` by rw_tac std_ss[poly_mult_def] >>
  `_ = chop ([c] o [c ** n])` by metis_tac[poly_chop_mult_comm, weak_const, ring_exp_element] >>
  `_ = chop (c o [c ** n])` by rw_tac std_ss[weak_mult_const] >>
  `_ = chop [c * c ** n]` by rw_tac std_ss[weak_cmult_const] >>
  rw[ring_exp_SUC]);

(* Theorem: Ring r ==> !p. poly p ==> !n. EVEN n ==> (p ** n = (p * p) ** (HALF n)) *)
(* Proof:
     p ** n
   = p ** (2 * HALF n)       by EVEN_HALF
   = (p ** 2) ** (HALF n)    by poly_exp_mult
   = (p * p) ** (HALF n)     by poly_exp_2
*)
val poly_exp_even = store_thm(
  "poly_exp_even",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !n. EVEN n ==> (p ** n = (p * p) ** (HALF n))``,
  rpt strip_tac >>
  `n = 2 * HALF n` by rw[EVEN_HALF] >>
  `p ** n = p ** (2 * HALF n)` by metis_tac[] >>
  `_ = (p ** 2) ** (HALF n)` by rw[poly_exp_mult] >>
  `_ = (p * p) ** (HALF n)` by rw[poly_exp_2] >>
  rw[]);

(* Theorem: Ring r ==> !p. poly p ==> !n. ODD n ==> (p ** n = p * (p * p) ** (HALF n)) *)
(* Proof:
     p ** n
   = p ** (2 * HALF n + 1)       by ODD_HALF
   = p ** SUC (2 * HALF n)       by ADD1
   = p * p ** (2 * HALF n)       by poly_exp_SUC
   = p * (p ** 2) ** (HALF n)    by poly_exp_mult
   = p * (p * p) ** (HALF n)     by poly_exp_2
*)
val poly_exp_odd = store_thm(
  "poly_exp_odd",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !n. ODD n ==> (p ** n = p * (p * p) ** (HALF n))``,
  rpt strip_tac >>
  `p ** n = p ** (2 * HALF n + 1)` by rw[GSYM ODD_HALF] >>
  `_ = p ** (SUC (2 * HALF n))` by rw_tac std_ss[ADD1] >>
  `_ = p * p ** (2 * HALF n)` by rw[poly_exp_SUC] >>
  `_ = p * (p ** 2) ** (HALF n)` by rw[poly_exp_mult] >>
  `_ = p * (p * p) ** (HALF n)` by rw[poly_exp_2] >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Operations applied to Weak                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ( |0| + p = chop p) /\ (p + |0| = chop p) *)
(* Proof:
      |0| + p
    = chop ( |0| || p)    by poly_add_def
    = chop p              by weak_add_lzero
       p + |0|
    = chop (p || |0|)     by poly_add_def
    = chop p              by weak_add_rzero
*)
val poly_add_weak_zero = store_thm(
  "poly_add_weak_zero",
  ``!r:'a ring. !p. ( |0| + p = chop p) /\ (p + |0| = chop p)``,
  rw[poly_add_def, weak_add_lzero, weak_add_rzero]);

(* Theorem: Ring r ==> !p q. weak p /\ weak q ==> !c. c IN R ==> (c * p * q = c * (p * q)) *)
(* Proof:
      c * p * q
    = chop (chop (c o p) o q)   by poly_cmult_def, poly_mult_def
    = chop ((c o p) o q)        by poly_chop_mult, weak_cmult_weak
    = chop (c o (p o q))        by weak_cmult_mult
    = chop (c o (chop (p o q))) by poly_chop_cmult, weak_mult_weak
    = c * (p * q)               by poly_cmult_def, poly_mult_def
*)
val poly_cmult_mult_weak = store_thm(
  "poly_cmult_mult_weak",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q ==> !c. c IN R ==> (c * p * q = c * (p * q))``,
  rpt strip_tac >>
  `c * p * q = chop (chop (c o p) o q)` by rw_tac std_ss[poly_cmult_def, poly_mult_def] >>
  `_ = chop ((c o p) o q)` by rw_tac std_ss[poly_chop_mult, weak_cmult_weak] >>
  `_ = chop (c o (p o q))` by rw_tac std_ss[weak_cmult_mult] >>
  `_ = chop (c o (chop (p o q)))` by rw_tac std_ss[poly_chop_cmult, weak_mult_weak] >>
  `_ = c * (p * q)` by rw_tac std_ss[poly_cmult_def, poly_mult_def] >>
  rw[]);

(* Theorem: Ring r ==> !p q. weak p /\ weak q ==> !c. c IN R ==> (p * (c * q) = c * p * q) *)
(* Proof:
     p * (c * q)
   = chop (p o (chop (c o q)))       by poly_mult_def, poly_cmult_def
   = chop (p o (c o q))              by poly_chop_mult_comm, weak_cmult_weak
   = chop ((c o p) o q)              by weak_mult_cmult
   = chop (chop (c o p) o q)         by poly_chop_mult, weak_cmult_weak
   = (c * p) * q                     by poly_mult_def, poly_cmult_def
*)
val poly_mult_cmult_weak = store_thm(
  "poly_mult_cmult_weak",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q ==> !c. c IN R ==> (p * (c * q) = c * p * q)``,
  rpt strip_tac >>
  `p * (c * q) = chop (p o (chop (c o q)))` by rw_tac std_ss[poly_mult_def, poly_cmult_def] >>
  `_ = chop (p o (c o q))` by rw_tac std_ss[poly_chop_mult_comm, weak_cmult_weak] >>
  `_ = chop ((c o p) o q)` by rw_tac std_ss[weak_mult_cmult] >>
  `_ = chop (chop (c o p) o q)` by rw_tac std_ss[poly_chop_mult, weak_cmult_weak] >>
  `_ = (c * p) * q` by rw_tac std_ss[poly_mult_def, poly_cmult_def] >>
  rw[]);

(* Theorem: Ring r ==> !c p. c IN R /\ weak p ==> (c * p = c * (chop p)) *)
(* Proof:
     c * p
   = chop (c o p)          by poly_cmult_def
   = chop (c o (chop p))   by poly_chop_cmult
   = c * (chop p)          by poly_cmult_def
*)
val poly_cmult_weak = store_thm(
  "poly_cmult_weak",
  ``!r:'a ring. Ring r ==> !c p. c IN R /\ weak p ==> (c * p = c * (chop p))``,
  rpt strip_tac >>
  `c * p = chop (c o p)` by rw_tac std_ss[poly_cmult_def] >>
  `_ = chop (c o (chop p))` by rw_tac std_ss[poly_chop_cmult] >>
  `_ = c * (chop p)` by rw_tac std_ss[poly_cmult_def] >>
  rw[]);

(* Theorem: Ring r ==> !c p. c IN R /\ weak p ==> poly (c * p) *)
(* Proof:
   Note c * p = chop (c o p)     by poly_cmult_def
    and weak (c o p)             by weak_cmult_weak
   Thus poly (c * p)             by poly_chop_weak_poly
*)
val poly_cmult_weak_poly = store_thm(
  "poly_cmult_weak_poly",
  ``!r:'a ring. Ring r ==> !c p. c IN R /\ weak p ==> poly (c * p)``,
  rw_tac std_ss[poly_cmult_def, weak_cmult_weak, poly_chop_weak_poly]);

(* Theorem: Ring r ==> !p q. weak p /\ weak q ==> (p + q = chop p + chop q) *)
(* Proof:
     p + q
   = chop (p || q)                 by poly_add_def
   = chop ((chop p) || (chop q))   by poly_chop_add_chop
   = (chop p) + (chop q)           by poly_add_def
*)
val poly_add_weak = store_thm(
  "poly_add_weak",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q ==> (p + q = chop p + chop q)``,
  metis_tac[poly_chop_add_chop, poly_add_def]);

(* Theorem: Ring r ==> !p q. weak p /\ weak q ==> (p + q = p + chop q) *)
(* Proof:
     p + q
   = chop (p || q)            by poly_add_def
   = chop (p || (chop q))     by poly_chop_add_comm
   = p + (chop q)             by poly_add_def
*)
val poly_add_weak_left = store_thm(
  "poly_add_weak_left",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q ==> (p + q = p + chop q)``,
  metis_tac[poly_chop_add_comm, poly_add_def]);

(* Theorem: Ring r ==> !p q. weak p /\ weak q ==> (p + q = (chop p) + q) *)
(* Proof:
     p + q
   = chop (p || q)            by poly_add_def
   = chop ((chop p) || q)     by poly_chop_add
   = (chop p) + q             by poly_add_def
*)
val poly_add_weak_right = store_thm(
  "poly_add_weak_right",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q ==> (p + q = (chop p) + q)``,
  metis_tac[poly_chop_add, poly_add_def]);

(* Theorem: Ring r ==> !p q. weak p /\ weak q ==> poly (p + q) *)
(* Proof:
   Note p + q = (chop p) + (chop q)      by poly_add_weak
    And poly (chop p) /\ poly (chop q)   by poly_chop_weak_poly
     so poly (p + q)                     by poly_add_poly
*)
val poly_add_weak_poly = store_thm(
  "poly_add_weak_poly",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q ==> poly (p + q)``,
  metis_tac[poly_add_weak, poly_chop_weak_poly, poly_add_poly]);

(* Theorem: Ring r ==> !p q. weak p /\ weak q ==> (p * q = (chop p) * (chop q)) *)
(* Proof:
     p * q
   = chop (p o q)                 by poly_mult_def
   = chop ((chop p) o (chop q))   by poly_chop_mult_chop
   = (chop p) * (chop q)          by poly_mult_def
*)
val poly_mult_weak = store_thm(
  "poly_mult_weak",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q ==> (p * q = (chop p) * (chop q))``,
  rpt strip_tac >>
  `p * q = chop (p o q)` by rw_tac std_ss[poly_mult_def] >>
  `_ = chop ((chop p) o (chop q))` by rw_tac std_ss[poly_chop_mult_chop] >>
  `_ = (chop p) * (chop q)` by rw_tac std_ss[poly_mult_def] >>
  rw[]);

(* Theorem: Ring r ==> !p q. weak p /\ weak q ==> (p * q = p * (chop q)) *)
(* Proof:
     p * q
   = chop (p o q)            by poly_mult_def
   = chop (p o (chop q))     by poly_chop_mult_comm
   = p * (chop q)            by poly_mult_def
*)
val poly_mult_weak_left = store_thm(
  "poly_mult_weak_left",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q ==> (p * q = p * (chop q))``,
  rpt strip_tac >>
  `p * q = chop (p o q)` by rw_tac std_ss[poly_mult_def] >>
  `_ = chop (p o (chop q))` by rw_tac std_ss[poly_chop_mult_comm] >>
  `_ = p * (chop q)` by rw_tac std_ss[poly_mult_def] >>
  rw[]);

(* Theorem: Ring r ==> !p q. weak p /\ weak q ==> (p * q = (chop p) * q) *)
(* Proof:
     p * q
   = chop (p o q)            by poly_mult_def
   = chop ((chop p) o q)     by poly_chop_mult
   = (chop p) * q            by poly_mult_def
*)
val poly_mult_weak_right = store_thm(
  "poly_mult_weak_right",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q ==> (p * q = (chop p) * q)``,
  rpt strip_tac >>
  `p * q = chop (p o q)` by rw_tac std_ss[poly_mult_def] >>
  `_ = chop ((chop p) o q)` by rw_tac std_ss[poly_chop_mult] >>
  `_ = (chop p) * q` by rw_tac std_ss[poly_mult_def] >>
  rw[]);

(* Theorem: Ring r ==> !p q. weak p /\ weak q ==> poly (p * q) *)
(* Proof:
   Note p * q = chop (p o q)     by poly_mult_def
    Now weak (p o q)             by weak_mult_weak
     so poly (p * q)             by poly_chop_weak_poly
*)
val poly_mult_weak_poly = store_thm(
  "poly_mult_weak_poly",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q ==> poly (p * q)``,
  rw_tac std_ss[poly_mult_def, weak_mult_weak, poly_chop_weak_poly]);

(* Theorem: Ring r ==> !p. weak p ==> !n. (p ** n = (chop p) ** n) *)
(* Proof:
   By induction on n.
   Base: p ** 0 = chop p ** 0
         p ** 0
       = |1|           by poly_exp_0
       = chop p ** 0   by poly_exp_0
   Step: p ** n = chop p ** n ==> p ** SUC n = chop p ** SUC n
       Note weak (p ** n)          by weak_exp_weak
         p ** SUC n
       = p * p ** n                by poly_exp_SUC
       = (chop p) * p ** n         by poly_mult_weak_right
       = (chop p) * (chop p ** n)  by induction hypothesis
       = (chop p) ** (SUC n)       by poly_exp_SUC
*)
val poly_exp_weak = store_thm(
  "poly_exp_weak",
  ``!r:'a ring. Ring r ==> !p. weak p ==> !n. (p ** n = (chop p) ** n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `p ** SUC n = p * p ** n` by rw[] >>
  `_ = (chop p) * p ** n` by rw_tac std_ss[poly_mult_weak_right, weak_exp_weak] >>
  `_ = (chop p) ** (SUC n)` by rw[] >>
  rw[]);

(* Theorem: Ring r ==> !p. weak p ==> !n. poly (p ** n) *)
(* Proof:
   Note p ** n = (chop p) ** n   by poly_exp_weak
    and poly (chop p)            by poly_chop_weak_poly
   Thus poly (p ** n)            by poly_exp_poly
*)
val poly_exp_weak_poly = store_thm(
  "poly_exp_weak_poly",
  ``!r:'a ring. Ring r ==> !p. weak p ==> !n. poly (p ** n)``,
  rw_tac std_ss[poly_exp_weak, poly_chop_weak_poly, poly_exp_poly]);

(* Theorem: Ring r ==> !p q. weak p /\ weak q ==> (p + q = q + p) *)
(* Proof:
     p + q
   = chop (p || q)         by poly_add_def
   = chop (q || p)         by weak_add_comm
   = q + p                 by poly_add_def
*)
val poly_add_weak_comm = store_thm(
  "poly_add_weak_comm",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q ==> (p + q = q + p)``,
  rw_tac std_ss[poly_add_def, weak_add_comm]);

(* Theorem: Ring r ==> !p q t. weak p /\ weak q /\ weak t ==> (p + q + t = p + (q + t)) *)
(* Proof:
     p + q + t
   = chop (chop (p || q) || t)       by poly_add_def
   = chop ((p || q) || t)            by poly_chop_add
   = chop (p || (q || t))            by weak_add_assoc
   = chop (p || (chop (q || t)))     by poly_chop_add_comm
   = p + (q + t)                     by poly_add_def
*)
val poly_add_weak_assoc = store_thm(
  "poly_add_weak_assoc",
  ``!r:'a ring. Ring r ==> !p q t. weak p /\ weak q /\ weak t ==> (p + q + t = p + (q + t))``,
  rpt strip_tac >>
  `p + q + t = chop (chop (p || q) || t)` by rw[GSYM poly_add_def] >>
  `_ = chop ((p || q) || t)` by rw_tac std_ss[poly_chop_add, weak_add_weak] >>
  `_ = chop (p || (q || t))` by rw_tac std_ss[weak_add_assoc] >>
  `_ = chop (p || (chop (q || t)))` by rw_tac std_ss[poly_chop_add_comm, weak_add_weak] >>
  `_ = p + (q + t)` by rw[GSYM poly_add_def] >>
  rw[]);

(* Theorem: Ring r ==> !p q. weak p /\ weak q ==> (p * q = q * p) *)
(* Proof:
     p * q
   = chop (p o q)         by poly_mult_def
   = chop (q o p)         by weak_mult_comm
   = q * p                by poly_mult_def
*)
val poly_mult_weak_comm = store_thm(
  "poly_mult_weak_comm",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q ==> (p * q = q * p)``,
  rw_tac std_ss[poly_mult_def, weak_mult_comm]);

(* Theorem: Ring r ==> !p q t. weak p /\ weak q /\ weak t ==> (p * q * t = p * (q * t)) *)
(* Proof:
     p * q * t
   = chop (chop (p o q) o t)         by poly_mult_def
   = chop ((p o q) o t)              by poly_chop_mult
   = chop (p o (q o t))              by weak_mult_assoc
   = chop (p o (chop (q o t)))       by poly_chop_mult_comm
   = p * (q * t)                     by poly_mult_def
*)
val poly_mult_weak_assoc = store_thm(
  "poly_mult_weak_assoc",
  ``!r:'a ring. Ring r ==> !p q t. weak p /\ weak q /\ weak t ==> (p * q * t = p * (q * t))``,
  rpt strip_tac >>
  `p * q * t = chop (chop (p o q) o t)` by rw[GSYM poly_mult_def] >>
  `_ = chop ((p o q) o t)` by rw_tac std_ss[poly_chop_mult, weak_mult_weak] >>
  `_ = chop (p o (q o t))` by rw_tac std_ss[weak_mult_assoc] >>
  `_ = chop (p o (chop (q o t)))` by rw_tac std_ss[poly_chop_mult_comm, weak_mult_weak] >>
  `_ = p * (q * t)` by rw[GSYM poly_mult_def] >>
  rw[]);

(* poly_add_const_const
|- !r. Ring r ==> !h k. h IN R /\ k IN R ==> (chop [h] + chop [k] = chop [h + k])
*)

(* Theorem: h IN R /\ k IN R ==> ([h] + [k] = chop [h + k]) *)
(* Proof:
     [h] + [k]
   = chop ([h] || [k])        by poly_add_def
   = chop (h + k::[] || [])   by weak_add_def
   = chop (h + k::[])         by weak_add_def
   = chop [h + k]             by notation
*)
val poly_add_weak_const_const = store_thm(
  "poly_add_weak_const_const",
  ``!r:'a ring. !h k. h IN R /\ k IN R ==> ([h] + [k] = chop [h + k])``,
  rw_tac std_ss[poly_add_def, weak_add_def]);

(* ------------------------------------------------------------------------- *)
(* Preparation for Polynomial Division.                                      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Problem 4: establish polynomial division algorithm:                       *)
(* poly p /\ poly q /\ 0 < deg q ==> ?s t. p = s * q + t  with deg t < deg q *)
(* ------------------------------------------------------------------------- *)

(* Again, this requires a case study: deg ([a; c] - [b; c]) = 0 *)

(* Theorem: deg ([a; c] - [b; c]) = 0 *)
(* Proof: direct evaluation.
   If a = b, [a;c] - [b;c] = |0|      by poly_sub_eq_zero
      hence true by poly_deg_of_zero
   If a <> b,
      deg ([a; c] - [b; c])
    = deg ((a; c]) + -(b; c]))        by poly_sub_def
    = deg ((a; c]) + [-b; -c]))       by poly_neg_def
    = deg (chop ([a;c] || [-b;-c]))   by poly_add_def
    = deg (chop [a + -b; c + -c])     by weak_add_def
    = deg (chop [a + -b; #0])         by ring_add_rneg
    = deg (chop [a - b; #0])          by ring_sub_def
    = deg ([a - b])                   by poly_chop_cons, a <> b
    = 0                               by poly_deg_const
*)
val poly_deg_sub_len2 = store_thm(
  "poly_deg_sub_len2",
  ``!r:'a ring. Ring r ==> !a b c. poly [a; c] /\ poly [b; c] ==> (deg ([a; c] - [b; c]) = 0)``,
  rpt strip_tac >>
  `a IN R /\ b IN R /\ c IN R /\ poly [c]` by metis_tac[poly_cons_poly] >>
  `c <> #0` by metis_tac[poly_cons_property] >>
  Cases_on `a = b` >-
  rw[poly_sub_eq_zero] >>
  `a - b <> #0` by metis_tac[ring_sub_eq_zero] >>
  `[a; c] - [b; c] = chop ([a;c] || [-b;-c])`
    by rw_tac std_ss[poly_add_def, poly_sub_def, poly_neg_def, weak_neg_def] >>
  `_ = chop [a - b; #0]` by rw_tac std_ss[weak_add_def, ring_add_rneg, ring_sub_def] >>
  rw[]);

(* Theorem: poly p /\ poly q /\ deg p = deg q /\ lead p = lead q /\ 0 < deg q ==> deg (p - q) < deg q *)
(* Proof: by induction on deg q.
   Base case: deg q = 0 /\ 0 < deg q  /\ ... ==> deg (p - q) < deg q
      true by contradiction: deg q = 0 /\ 0 < deg q is impossible.
   Step case: poly p /\ poly q /\ 0 < deg q /\ (deg p = deg q) /\ (lead p = lead q) ==> deg (p - q) < deg q ==>
              SUC v = deg q /\ 0 < deg q /\ deg p = deg q /\ lead p = lead q ==> deg (p - q) < deg q
      Since 0 < deg q and 0 < deg p, from deg p = deg q
      p <> [] and q <> []           by poly_deg_of_zero
      Let p = h::t, q = k::s
      t <> [] and s <> []           by poly_deg_const
      or t <> |0| and s <> |0|      by poly_zero
      hence   deg p = SUC (deg t)
              deg q = SUC (deg s)   by poly_deg_cons
      and v = deg t = deg s         from deg p = deg q
      Also   lead p = lead t
             lead q = lead s        by poly_lead_cons
      hence  lead t = lead s
      Now, to apply induction hypothesis, we need 0 < deg s.
      If deg s = 0, s = [j] and j <> #0  by poly_deg_eq_zero, s <> |0|
      also deg t = 0, t = [j]   by poly_lead_const, since lead t = lead s
      hence deg (p - q) = deg (h; j] - [k; j]) = 0 by poly_deg_sub_len2 (the case study)
      and   deg (p - q) < deg q     given 0 < deg q
      With 0 < deg s,
      if zerop (h - k:: t - s)
      then  p - q = |0|             by poly_sub_cons
      hence deg (p - q) < deg q     by poly_deg_of_zero, given 0 < deg q.
      If ~ zerop (h - k:: t - s),
      then  p - q  = (h - k::t - s) by poly_sub_cons
      If t - s = |0|,
      deg (p - q) = deg [h - k] = 0 by poly_deg_const, field_sub_element
      hence deg (p - q) < deg q     given 0 < deg q.
      If t - s <> |0|,
      deg (p - q) = deg (h::t) - (k::s)
                  = deg (h - k:: t - s)    by poly_sub_cons
                  = SUC (deg (t - s))      by poly_deg_cons, t - s <> |0|
                  < SUC deg s = deg q      by induction , 0 < deg s
*)
val poly_deg_eq_lead_sub = store_thm(
  "poly_deg_eq_lead_sub",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ (deg p = deg q) /\ (lead p = lead q) /\ 0 < deg q ==> deg (p - q) < deg q``,
  strip_tac >>
  strip_tac >>
  Induct_on `deg q` >-
  rw_tac std_ss[] >>
  rpt strip_tac >>
  `!n. n <> 0 <=> 0 < n` by decide_tac >>
  `!m n. (SUC m = SUC n) <=> (m = n)` by decide_tac >>
  `!n m. n < m <=> SUC n < SUC m` by decide_tac >>
  `(?h t. p = h::t) /\ (? k s. q = k::s)` by metis_tac[poly_deg_of_zero, list_CASES] >>
  `h IN R /\ poly t /\ k IN R /\ poly s` by metis_tac[poly_cons_poly] >>
  `t <> |0| /\ s <> |0|` by metis_tac[poly_deg_const, poly_zero] >>
  `(deg t = v) /\ (deg s = v)` by metis_tac[poly_deg_cons] >>
  `(lead p = lead t) /\ (lead q = lead s)` by metis_tac[poly_lead_cons] >>
  Cases_on `deg s = 0` >| [
    `?j. j IN R /\ j <> #0 /\ (p = [h; j]) /\ (q = [k; j])` by metis_tac[poly_deg_eq_zero, poly_lead_const] >>
    metis_tac[poly_deg_sub_len2],
    `p - q = p + -q` by rw_tac std_ss[poly_sub_def] >>
    `_ = chop ((h::t) || -(k::s))` by rw_tac std_ss[poly_add_def] >>
    `_ = chop ((h::t) || (-k::-s))` by rw_tac std_ss[poly_neg_cons] >>
    `_ = chop (h + -k :: t || -s)` by rw_tac std_ss[weak_add_cons] >>
    Cases_on `zerop (h + -k :: t || -s)` >-
    metis_tac[poly_chop_cons, poly_deg_of_zero] >>
    `p - q = h - k:: t - s` by rw_tac std_ss[poly_chop_cons, poly_add_def, poly_sub_def, ring_sub_def] >>
    Cases_on `t - s = []` >-
    metis_tac[poly_deg_const, ring_sub_element] >>
    metis_tac[poly_deg_cons, poly_sub_poly, poly_zero]
  ]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Evaluation (upgrade from polyWeak).                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: poly p ==> p(x) IN R *)
(* Proof: by weak_eval_element, poly_is_weak. *)
val poly_eval_element = store_thm(
  "poly_eval_element",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !x. x IN R ==> eval p x IN R``,
  rw[weak_eval_element]);

val _ = export_rewrites ["poly_eval_element"];

(* Theorem: (c * p)(x) = c * p(x) *)
(* Proof:
     (c * p)(x)
   = (chop (c o p))(x)     by poly_cmult_def
   = (c o p)(x)            by poly_eval_chop
   = c * p(x)              by weak_eval_cmult, poly_is_weak
*)
val poly_eval_cmult = store_thm(
  "poly_eval_cmult",
  ``!r:'a ring. Ring r ==> !p c x. poly p /\ c IN R /\ x IN R ==> (eval (c * p) x = c * (eval p x))``,
  rw_tac std_ss[poly_cmult_def, poly_eval_chop, weak_eval_cmult, poly_is_weak]);

val _ = export_rewrites ["poly_eval_cmult"];

(* Theorem: poly p ==> (- p)(x) = - p(x) *)
(* Proof: by poly_is_weak and weak_eval_neg. *)
val poly_eval_neg = store_thm(
  "poly_eval_neg",
  ``!r:'a ring. Ring r ==> !p x. poly p /\ x IN R ==> (eval (- p) x = - (eval p x))``,
  rw_tac std_ss[poly_is_weak, weak_eval_neg, poly_neg_def]);

val _ = export_rewrites ["poly_eval_neg"];

(* Theorem: poly p /\ poly q ==> (p + q)(x) = p(x) + q(x). *)
(* Proof:
     (p + q)(x)
   = (chop (p || q))(x)     by poly_add_def
   = (p || q)(x)            by poly_eval_chop
   = p(x) + q(x)            by weak_eval_add, poly_is_weak
*)
val poly_eval_add = store_thm(
  "poly_eval_add",
  ``!r:'a ring. Ring r ==> !p q x. poly p /\ poly q /\ x IN R ==> (eval (p + q) x = eval p x + eval q x)``,
  rw_tac std_ss[poly_add_def, poly_eval_chop, weak_eval_add, poly_is_weak]);

val _ = export_rewrites ["poly_eval_add"];

(* Theorem: poly p /\ poly q ==> (p - q)(x) = p(x) - q(x). *)
(* Proof:
     (p - q)(x)
   = (p + -q)(x)     by poly_sub_def
   = p(x) + (-q)(x)  by poly_eval_add, poly_neg_poly
   = p(x) + -q(x)    by poly_eval_neg
   = p(x) - q(x)     by ring_sub_def
*)
val poly_eval_sub = store_thm(
  "poly_eval_sub",
  ``!r:'a ring. Ring r ==> !p q x. poly p /\ poly q /\ x IN R ==> (eval (p - q) x = eval p x - eval q x)``,
  rw[]);

val _ = export_rewrites ["poly_eval_sub"];

(* Theorem: poly p ==> (p >> n)(x) = p(x) * x ** n *)
(* Proof: by weak_eval_shift, poly_is_weak. *)
val poly_eval_shift = store_thm(
  "poly_eval_shift",
  ``!r:'a ring. Ring r ==> !p x. poly p /\ x IN R ==> !n. eval (p >> n) x = (eval p x) * (x ** n)``,
  rw_tac std_ss[weak_eval_shift, poly_is_weak]);

val _ = export_rewrites ["poly_eval_shift"];

(* Theorem: poly p /\ poly q ==> (p * q)(x) = p(x) * q(x) *)
(* Proof: by weak_eval_mult and poly_mult_def.
     (p * q)(x)
   = (chop (p o q))(x)      by poly_mult_def
   = (p o q)(x)             by poly_eval_chop
   = p(x) * q(x)            by weak_eval_mult, poly_is_weak.

*)
val poly_eval_mult = store_thm(
  "poly_eval_mult",
  ``!r:'a ring. Ring r ==> !p q x. poly p /\ poly q /\ x IN R ==> (eval (p * q) x = eval p x * eval q x)``,
  rw_tac std_ss[poly_mult_def, poly_eval_chop, weak_eval_mult, poly_is_weak]);

val _ = export_rewrites ["poly_eval_mult"];

(* Theorem: eval (p ** n) x = (eval p x) ** n *)
(* Proof: by induction on n.
   Base case: eval (p ** 0) x = eval p x ** 0
   LHS = eval (p ** 0) x
       = eval |1| x                     by poly_exp_0
       = #1                             by poly_eval_one
       = (eval p x) ** 0                by ring_exp_0
       = RHS
   Step case: eval (p ** n) x = eval p x ** n ==> eval (p ** SUC n) x = eval p x ** SUC n
   LHS = eval (p ** SUC n) x
       = eval (p * p ** n) x            by poly_exp_SUC
       = (eval p x) * (eval p ** n x)   by poly_eval_mult
       = (eval p x) * (eval p x) ** n   by induction hypothesis
       = (eval p x) ** SUC              by ring_exp_SUC
       = RHS
*)
val poly_eval_exp = store_thm(
  "poly_eval_exp",
  ``!r:'a ring. Ring r ==> !p x. poly p /\ x IN R ==> !n. eval (p ** n) x = (eval p x) ** n``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[]);

val _ = export_rewrites ["poly_eval_exp"];

(* ------------------------------------------------------------------------- *)
(* Polynomial Roots.                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r ==> !p x. x IN R /\ poly p /\ root p x ==> root (-p) x *)
(* Proof:
       root p x
   <=> eval p x = #0      by poly_root_def
   <=> -(eval p x) = #0   by ring_neg_zero
   <=> eval (-p) x = #0   by poly_eval_neg
   <=> root (-p) x        by poly_root_def
*)
val poly_root_neg = store_thm(
  "poly_root_neg",
  ``!r:'a ring. Ring r ==> !p x. x IN R /\ poly p /\ root p x ==> root (-p) x``,
  rw[poly_root_def]);

(* Theorem: Ring r ==> !p q x. x IN R /\ poly p /\ poly q /\ root p x /\ root q x ==> root (p + q) x *)
(* Proof:
   Since root p x <=> eval p x = #0      by poly_root_def
     and root q x <=> eval q x = #0      by poly_root_def
     Now eval (p + q) x
       = eval p x + eval q x             by poly_eval_add
       = #0 + #0                         by above
       = #0                              by ring_add_zero_zero
   Hence root (p + q) x                  by poly_root_def
*)
val poly_root_add = store_thm(
  "poly_root_add",
  ``!r:'a ring. Ring r ==> !p q x. x IN R /\ poly p /\ poly q /\ root p x /\ root q x ==> root (p + q) x``,
  rw[poly_root_def]);

(* Theorem: Ring r ==> !p q x. x IN R /\ poly p /\ poly q /\ root p x ==> root (p * q) x *)
(* Proof:
   Since root p x <=> eval p x = #0      by poly_root_def
     Now eval (p * q) x
       = (eval p x) * (eval q x)         by poly_eval_mult
       = #0 * (eval q x)                 by above
       = #0                              by ring_mult_lzero, poly_eval_element
   Hence root (p * q) x                  by poly_root_def
*)
val poly_root_mult = store_thm(
  "poly_root_mult",
  ``!r:'a ring. Ring r ==> !p q x. x IN R /\ poly p /\ poly q /\ root p x ==> root (p * q) x``,
  rw[poly_root_def]);

(* Theorem: Ring r ==> !p q x. x IN R /\ poly p /\ poly q /\ root q x ==> root (p * q) x *)
(* Proof: by poly_root_mult, poly_mult_comm *)
val poly_root_mult_comm = store_thm(
  "poly_root_mult_comm",
  ``!r:'a ring. Ring r ==> !p q x. x IN R /\ poly p /\ poly q /\ root q x ==> root (p * q) x``,
  metis_tac[poly_root_mult, poly_mult_comm]);

(* Theorem: Ring r ==> !x. x IN R ==> !p. poly p /\ p <> |0| /\ root p x ==> 0 < deg p *)
(* Proof:
   By contradiction, suppose deg p = 0.
   Then p <> |0| and deg p = 0
    ==> ?c. c IN R /\ c <> #0 /\ (p = [c])   by poly_deg_eq_0
   But  root p x
    <=> eval [c] x = #0      by poly_root_def
    <=> c = #0               by poly_eval_const
    which contradicts c <> #0.
*)
val poly_nonzero_with_root_deg_pos = store_thm(
  "poly_nonzero_with_root_deg_pos",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !p. poly p /\ p <> |0| /\ root p x ==> 0 < deg p``,
  metis_tac[poly_deg_eq_0, poly_root_def, poly_eval_const, NOT_ZERO_LT_ZERO]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Coefficients.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: poly p ==> !k. (p ' k) IN R *)
(* Proof: by rw_tac std_ss[poly_is_weak, weak_coeff_element. *)
val poly_coeff_element = store_thm(
  "poly_coeff_element",
  ``!r:'a ring. Ring r ==> !p. poly p ==> !k. (p ' k) IN R``,
  rw_tac std_ss[poly_is_weak, weak_coeff_element]);

val _ = export_rewrites ["poly_coeff_element"];

(* Theorem: poly p /\ !k. #0 = p ' k ==> p = |0| *)
(* Proof:
   By contradiction, let p <> |0|, i.e. p <> [] by poly_zero.
   p <> [] ==> ~zerop p   by poly_property
   But this violates zero_poly_coeff_all_zero.
*)
val poly_coeff_eq_zero = store_thm(
  "poly_coeff_eq_zero",
  ``!p:'a poly. poly p /\ (!k. p ' k = #0) ==> (p = |0|)``,
  metis_tac [poly_property, zero_poly_coeff_all_zero, poly_zero]);

(* ------------------------------------------------------------------------- *)
(* Characteristic of Polynomial Ring.                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r ==> !n. ##n = chop [ring_numr n] *)
(* Proof: by induction.
   First, if #1 = #0,
   Then R = {#0}              by ring_one_eq_zero
   Hence LHS = ##n
             = (PolyRing r).sum.exp |1| n
             = (PolyRing r).sum.exp |0| n   by poly_one, poly_zero
             = |0|                          by ring_add_group, group_id_exp
         RHS = chop [ring_numr n]
             = chop [#0]      by IN_SING, ring_num_element
             = |0|            by poly_chop_const_zero
   Hence we can assume #1 <> #0, and induct on n:
   Base case: ##0 = chop [ring_numr 0]
     LHS = |0|                by poly_add_group, group_exp_0, poly_ring_property, poly_one_poly
         = RHS                by poly_chop_zero, ring_num_0, poly_chop_const_zero
   Step case: ##n = chop [ring_numr n] ==> ##(SUC n) = chop [ring_numr  (SUC n)]
     LHS = ##(SUC n)
         = |1| + ## |1| n               by group_exp_SUC
         = |1| + chop [ring_numr  n]    by induction hypothesis
         = [#1] + chop [ring_numr n]    by poly_one, #1 <> #0
         = chop([#1] || [ring_numr  n]) by poly_chop_add_comm, poly_is_weak
         = chop([#1 + ring_numr n])     by weak_add_def
         = chop [ring_numr (SUC n)]     by ring_num_SUC
         = RHS
*)
val poly_one_sum_n = store_thm(
  "poly_one_sum_n",
  ``!r:'a ring. Ring r ==> !n. ##n = chop [ring_numr n]``,
  rpt strip_tac >>
  `Ring (PolyRing r)` by rw_tac std_ss[poly_add_mult_ring] >>
  Cases_on `#1 = #0` >| [
    `R = {#0}` by metis_tac[ring_one_eq_zero] >>
    metis_tac[IN_SING, ring_num_element, poly_chop_const_zero, poly_one, poly_zero, ring_add_group, group_id_exp],
    Induct_on `n` >-
    rw[] >>
    rw[] >-
    metis_tac[ring_add_rzero, ring_one_element] >-
    rw_tac std_ss[poly_add_def, poly_chop_def, weak_add_def, poly_is_weak, poly_one_poly, poly_one, zero_poly_def] >>
    rw_tac std_ss[poly_add_def, poly_chop_def, weak_add_def, poly_is_weak, poly_one_poly, poly_one, zero_poly_def]
  ]);

(* Theorem: Ring r ==> char (PolyRing r) = char r *)
(* Proof:
   Ring r ==> Ring (PolyRing r)            by poly_add_mult_ring
   Therefore,
     ## (char r)
   = chop [ring_numr (char r)]             by poly_one_sum_n
   = chop [#0]                             by char_property
   = |0|                                   by poly_chop_const_zero
   Hence
   (char (PolyRing r)) divides (char r)    by ring_char_divides
   Also,
     |0|
   = ## (char (PolyRing r))                by char_property
   = chop [ring_numr (char (PolyRing r))]  by poly_one_spoly_field_deg_cmult;
   um_n
   ==> ring_numr (char (PolyRing r)) = #0  by poly_chop_const_eq_zero
   Hence
   (char r) divides (char (PolyRing r))    by ring_char_divides
   Therefore
   (char (PolyRing r)) = (char r)          by DIVIDES_ANTISYM
*)
val poly_ring_char = store_thm(
  "poly_ring_char",
  ``!r:'a ring. Ring r ==> (char (PolyRing r) = char r)``,
  rpt strip_tac >>
  `Ring (PolyRing r)` by rw_tac std_ss[poly_add_mult_ring] >>
  `## (char r) = chop[ring_numr (char r)]` by rw_tac std_ss[poly_one_sum_n] >>
  `_ = |0|` by rw[char_property] >>
  `(char (PolyRing r)) divides (char r)` by rw_tac std_ss[GSYM ring_char_divides] >>
  `|0| = ## (char (PolyRing r))` by rw_tac std_ss[char_property] >>
  `_ = chop [ring_numr (char (PolyRing r))]` by rw_tac std_ss[poly_one_sum_n] >>
  `ring_numr (char (PolyRing r)) = #0` by rw_tac std_ss[GSYM poly_chop_const_eq_zero, ring_num_element] >>
  `(char r) divides (char (PolyRing r))` by rw_tac std_ss[GSYM ring_char_divides] >>
  rw_tac std_ss[DIVIDES_ANTISYM]);

(* Theorem: Ring r /\ (char r = 2) ==> !p. poly p ==> (-p = p) *)
(* Proof:
     p + p
   = #1 * p + #1 * p       by poly_cmult_lone
   = (#1 + #1) * p         by poly_add_cmult
   = #0 * p                by ring_char_2_property
   = |0|                   by poly_cmult_lzero
   Hence -p = p            by poly_add_eq_zero
*)
val poly_neg_char_2 = store_thm(
  "poly_neg_char_2",
  ``!r:'a ring. Ring r /\ (char r = 2) ==> !p. poly p ==> (-p = p)``,
  metis_tac[poly_cmult_lone, poly_add_cmult, ring_one_element,
            ring_char_2_property, poly_cmult_lzero, poly_add_eq_zero]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Set (truncated by degree).                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FINITE {p | weak p /\ (LENGTH p = n)} *)
(* Proof: by induction on n.
   Base case: FINITE {p | weak p /\ (LENGTH p = 0)}
       FINITE {p | weak p /\ (LENGTH p = 0)}
     = FINITE {[]}          by LENGTH_NIL, weak_of_zero
     = True,                by FINITE_SING
   Step case: FINITE {p | weak p /\ (LENGTH p = n)} ==> FINITE {p | weak p /\ (LENGTH p = SUC n)}
     First show: {p | weak p /\ (LENGTH p = SUC n)} =
                 IMAGE (\(e,l). e :: l) (R CROSS {p | weak p /\ (LENGTH p = n)}
     Then apply FINITE_CROSS, IMAGE_FINITE.
*)
val weak_poly_finite = store_thm(
  "weak_poly_finite",
  ``!r:'a ring. FINITE R ==> !n. FINITE {p | weak p /\ (LENGTH p = n)}``,
  ntac 2 strip_tac >>
  Induct >| [
    `!p. weak p /\ (LENGTH p = 0) <=> (p = [])` by metis_tac[LENGTH_NIL, weak_of_zero] >>
    rw[],
    `{p | weak p /\ (LENGTH p = SUC n)} = IMAGE (\(e,l). e :: l) (R CROSS {p | weak p /\ (LENGTH p = n)})` by
  (rw[EXTENSION, pairTheory.EXISTS_PROD, LENGTH_CONS, EQ_IMP_THM] >-
    metis_tac[weak_cons] >>
    rw[weak_cons]
    ) >>
    metis_tac[IMAGE_FINITE, FINITE_CROSS]
  ]);

(* Theorem: FINITE R ==> CARD {p | weak p /\ LENGTH p = n } = (CARD R) ** n *)
(* Proof: by induction on n.
   Base case: CARD {p | weak p /\ (LENGTH p = 0)} = CARD R ** 0
     CARD {p | weak p /\ (LENGTH p = 0)}
   = CARD {p | weak p /\ (p = [])}                    by LENGTH_NIL
   = CARD {[]}                                        by EXTENSION
   = 1
   = (CARD R) ** 0                                    by EXP
   Step case: CARD {p | weak p /\ (LENGTH p = n)} = CARD R ** n ==>
              CARD {p | weak p /\ (LENGTH p = SUC n)} = CARD R ** SUC n
     CARD {p | weak p /\ (LENGTH p = SUC n)}
   = CARD IMAGE (\(e,l). e :: l) (R CROSS {p | weak p /\ (LENGTH p = n)}  by proving this first
   = CARD (R CROSS {p | weak p /\ (LENGTH p = n)}     by FINITE_CARD_IMAGE, for finite set
   = CARD R * CARD {p | weak p /\ (LENGTH p = n)}     by CARD_CROSS
   = CARD R * CARD R ** n                             by induction hypothesis
   = CARD R ** SUC n                                  by EXP
*)
val weak_poly_card = store_thm(
  "weak_poly_card",
  ``!r:'a ring. FINITE R ==> !n. CARD {p | weak p /\ (LENGTH p = n) } = (CARD R) ** n``,
  ntac 2 strip_tac >>
  Induct >| [
    `{p | weak p /\ (LENGTH p = 0)} = {[]}` by rw[LENGTH_NIL, EXTENSION, EQ_IMP_THM] >>
    rw[],
    `{p | weak p /\ (LENGTH p = SUC n)} = IMAGE (\(e,l). e :: l) (R CROSS {p | weak p /\ (LENGTH p = n)})` by
  (rw[EXTENSION, pairTheory.EXISTS_PROD, LENGTH_CONS, EQ_IMP_THM] >-
    metis_tac[weak_cons] >>
    rw[weak_cons]
    ) >>
    `CARD (IMAGE (\(e,l). e::l) (R CROSS {p | weak p /\ (LENGTH p = n)})) = CARD R ** SUC n` suffices_by rw[] >>
    `FINITE {p | weak p /\ (LENGTH p = n)}` by rw[weak_poly_finite] >>
    rw[FINITE_CARD_IMAGE, CARD_CROSS, pairTheory.FORALL_PROD] >>
    rw[EXP]
  ]);

(* Show that:  {p | weak p /\ LENGTH p = n } --- chop -- { p | poly p /\ LENGTH p <= n } is BIJ *)

(* Theorem: FINITE R ==> BIJ chop {p | weak p /\ deg p < n } { p | poly p /\ deg p < n } *)
(* Proof:
   By induction on n.
   Base case: BIJ chop {p | weak p /\ (LENGTH p = 0)} {p | poly p /\ ((p = []) \/ deg p < 0)}
     This is to show:
     (1) weak x /\ LENGTH x = 0 ==> chop x = [], true by poly_chop_of_zero
     (2) weak x /\ LENGTH x = 0 /\ weak y /\ LENGTH y = 0 ==> x = y, true by LENGTH_NIL
     (3) same as (1).
     (4) ?y. (weak y /\ (LENGTH y = 0)) /\ (chop y = []),
         Take y = [], true by weak_of_zero, poly_chop_of_zero
   Step case: BIJ chop {p | weak p /\ (LENGTH p = n)} {p | poly p /\ ((p = []) \/ deg p < n)} ==>
              BIJ chop {p | weak p /\ (LENGTH p = SUC n)} {p | poly p /\ ((p = []) \/ deg p < SUC n)}
   By definitions, this is to show:
   (1) weak x ==> poly (chop x), true by poly_chop_weak_poly.
   (2) weak x /\ deg x < n ==> (chop x = []) \/ deg (chop x) < LENGTH x
       If x = [], true             by poly_chop_of_zero.
       If x <> [], LENGTH x <> 0   by LENGTH_NIL
          deg (chop x) <= deg x    by poly_deg_chop
          deg x = PRE(LENGTH x)    by poly_deg_def
       so deg (chop x) < SUC (deg x)
                       = SUC (PRE (LENGTH x)
                       = LENGTH x      by SUC_PRE.
   (3) LENGTH x = LENGTH y /\ chop x = chop y ==> x = y
       By induction on LENGTH x.
       Base case: 0 = LENGTH x /\ LENGTH x = LENGTH y /\ chop x = chop y ==> x = y
         True by LENGTH_NIL, since x = [] and y = [].
       Step case: SUC v = LENGTH x /\ LENGTH x = LENGTH y /\ chop x = chop y ==> x = y
         Since 0 < SUC v, let x = h::t, y = h'::t',
         then weak t and weak t'       by weak_cons
         and v = LENGTH t = LENGTH t'  by LENGTH, LENGTH_CONS
         Split into cases:
         If zerop x = zerop (h::t), then zerop y,
            h = h' = #0               by zero_poly_cons
            zerop t /\ zerop t'       by zero_poly_cons
            chop t = chop t'          by zero_poly_chop
            t = t'                    by induction hypothesis
            Henc true.
         If ~zerop x = ~zerop (h::t), then ~zerop y,
            h::chop t = h'::chop t'   by poly_chop_cons
            t = t'                    by induction hypothesis
            Hence true.
   (4) same as (1).
   (5) weak x /\ (deg x = n) ==> (chop x = []) \/ deg (chop x) < LENGTH x
       Similar analysis as (3).
*)
val weak_poly_poly_bij = store_thm(
  "weak_poly_poly_bij",
  ``!r:'a ring. FINITE R /\ #0 IN R ==>
   !n. BIJ chop {p | weak p /\ (LENGTH p = n) } { p | poly p /\ ((p = []) \/ deg p < n) }``,
  ntac 2 strip_tac >>
  Induct >-
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >>
  pop_assum mp_tac >>
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF, GSPECIFICATION] >-
  rw[] >-
 (`LENGTH x <> 0` by decide_tac >>
  `?h t. x = h::t` by metis_tac[LENGTH_NIL, list_CASES] >>
  `SUC (LENGTH t) = SUC n` by metis_tac[LENGTH] >>
  `LENGTH t = n` by decide_tac >>
  `weak t` by metis_tac[weak_cons] >>
  Cases_on `zerop x` >-
  rw[GSYM zero_poly_chop] >>
  `chop x = h::chop t` by metis_tac[poly_chop_cons] >>
  `x <> []` by metis_tac[LENGTH_NIL] >>
  `deg (chop x) <= deg x` by rw[poly_deg_chop] >>
  `deg (chop x) < SUC (deg x)` by decide_tac >>
  `deg x = PRE(LENGTH x)` by rw[poly_deg_def] >>
  `LENGTH x <> 0` by rw[LENGTH_NIL] >>
  `0 < LENGTH x` by decide_tac >>
  metis_tac[SUC_PRE]) >-
 (`LENGTH x <> 0 /\ LENGTH y <> 0` by decide_tac >>
  `?h t h' t'. (x = h::t) /\ (y = h'::t')` by metis_tac[LENGTH_NIL, list_CASES] >>
  `(SUC (LENGTH t) = SUC n) /\ (SUC (LENGTH t') = SUC n)` by metis_tac[LENGTH] >>
  `(LENGTH t = n) /\ (LENGTH t' = n)` by decide_tac >>
  `weak t /\ weak t'` by metis_tac[weak_cons] >>
  Cases_on `zerop x` >-
  metis_tac[zero_poly_cons, zero_poly_chop] >>
  `~zerop y` by metis_tac[zero_poly_chop] >>
  `h::chop t = h':: chop t'` by metis_tac[poly_chop_cons] >>
  `(h = h') /\ (chop t = chop t')` by rw_tac std_ss[] >>
  metis_tac[]) >-
  rw[] >-
 (Cases_on `x` >-
  metis_tac[poly_chop_of_zero] >>
  Cases_on `zerop (h::t)` >-
  metis_tac[zero_poly_chop] >>
  `chop (h::t) = h::chop t` by rw[] >>
  `SUC (LENGTH t) = SUC n` by metis_tac[LENGTH] >>
  `LENGTH t = n` by decide_tac >>
  `weak t` by metis_tac[weak_cons] >>
  `poly (chop t) /\ ((chop t = []) \/ deg (chop t) < n)` by rw[] >| [
    `chop (h::t) = [h]` by metis_tac[poly_chop_cons] >>
    `deg [h] = 0` by rw[] >>
    `0 < SUC n` by decide_tac >>
    metis_tac[],
    `chop (h::t) = h::chop t` by metis_tac[poly_chop_cons] >>
    Cases_on `chop t = []` >| [
      `h <> #0` by metis_tac[zero_poly_chop, zero_poly_cons, zero_poly_of_zero] >>
      rw[],
      `deg (h::chop t) = SUC (deg (chop t))` by metis_tac[poly_deg_cons, poly_zero] >>
      `SUC (deg (chop t)) < SUC n` by decide_tac >>
      metis_tac[]
    ]
  ]) >-
 (`?y. (weak y /\ (LENGTH y = n)) /\ (chop y = [])` by rw[] >>
  qexists_tac `#0::y` >>
  metis_tac[weak_cons, LENGTH, zero_poly_cons, zero_poly_chop]) >>
  Cases_on `x` >| [
    `?y. (weak y /\ (LENGTH y = n)) /\ (chop y = [])` by rw[] >>
    qexists_tac `#0::y` >>
    metis_tac[weak_cons, LENGTH, zero_poly_cons, zero_poly_chop],
    `h IN R /\ poly t /\ ~zerop(h::t)` by metis_tac[poly_cons_poly] >>
    Cases_on `t = []` >| [
      `poly []` by rw[] >>
      `?y. (weak y /\ (LENGTH y = n)) /\ (chop y = [])` by rw[] >>
      `h <> #0` by metis_tac[zero_poly_chop, zero_poly_cons, zero_poly_of_zero] >>
      qexists_tac `h:: y` >>
      `weak (h::y)` by rw[] >>
      `LENGTH (h::y) = SUC n` by rw[] >>
      `~zerop (h::y)` by metis_tac[zero_poly_cons] >>
      metis_tac[poly_chop_cons],
      `deg (h::t) = SUC (deg t)` by rw[] >>
      `deg t < n` by decide_tac >>
      `?y. (weak y /\ (LENGTH y = n)) /\ (chop y = t)` by rw[] >>
      qexists_tac `h::y` >>
      `weak (h::y)` by rw[] >>
      `LENGTH (h::y) = SUC n` by rw[] >>
      `~zerop (h::y)` by metis_tac[zero_poly_cons, zero_poly_chop] >>
      metis_tac[poly_chop_cons]
    ]
  ]);

(* This is a milestone theorem. *)

(* Theorem: 0 < n ==> { p | poly p /\ deg p < n } = { p | poly p /\ ((p = []) \/ deg p < n) } *)
(* Proof:
   By EXTENSION, and poly_deg_of_zero.
*)
val poly_truncated_by_degree = store_thm(
  "poly_truncated_by_degree",
  ``!n. 0 < n ==> ({ p | poly p /\ deg p < n } = { p | poly p /\ ((p = []) \/ deg p < n) })``,
  rw[EXTENSION, EQ_IMP_THM] >>
  rw[]);

(* Theorem: FINITE R /\ #0 IN R ==> !n. FINITE {p | poly p /\ deg p < n} *)
(* Proof:
   Let s = {p | poly p /\ ((p = []) \/ deg p < n)}.
    Then {p | poly p /\ deg p < n} SUBSET s          by SUBSET_DEF
     and BIJ chop {p | weak p /\ (LENGTH p = n)} s   by weak_poly_poly_bij, FINITE R /\ #0 IN R
     Now FINITE {p | weak p /\ (LENGTH p = n)}       by weak_poly_finite]);
      so FINITE s                                    by FINITE_BIJ
   Hence FINITE {p | poly p /\ deg p < n}            by SUBSET_FINITE
*)
val poly_truncated_by_degree_finite = store_thm(
  "poly_truncated_by_degree_finite",
  ``!r:'a ring. FINITE R /\ #0 IN R ==> !n. FINITE {p | poly p /\ deg p < n}``,
  rpt strip_tac >>
  `{p | poly p /\ deg p < n} SUBSET {p | poly p /\ ((p = []) \/ deg p < n)}` by rw[SUBSET_DEF] >>
  metis_tac[weak_poly_poly_bij, weak_poly_finite, FINITE_BIJ, SUBSET_FINITE]);

(* ------------------------------------------------------------------------- *)
(* Other Useful Theorems                                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: p + q = t ==> p = t - q *)
(* Proof:
   p = p + |0|         by poly_add_rzero
     = p + (q + -q)    by poly_add_rneg
     = (p + q) + -q    by poly_add_assoc
     = t + -q          by given
     = t - q           by poly_sub_def
*)
val poly_add_solve_first = store_thm(
  "poly_add_solve_first",
  ``!r:'a ring. Ring r ==> !p q t. poly p /\ poly q /\ poly t /\ (p + q = t) ==> (p = t - q)``,
  rpt strip_tac >>
  `p = p + |0|` by rw[] >>
  `_ = p + (q + -q)` by rw[poly_add_rneg] >>
  `_ = (p + q) + -q` by rw[poly_add_assoc] >>
  rw[poly_sub_def]);

(* Theorem: p + q = t ==> q = t - p *)
(* Proof:
   Since p + q = q + p by poly_add_comm
   Hence true by poly_add_solve_first.
*)
val poly_add_solve_second = store_thm(
  "poly_add_solve_second",
  ``!r:'a ring. Ring r ==> !p q t. poly p /\ poly q /\ poly t /\ (p + q = t) ==> (q = t - p)``,
  rw[poly_add_comm, poly_add_solve_first]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q /\ unit (lead p) ==> (lead (p * q) = lead p * lead q) *)
(* Proof:
   Note lead p IN R /\ lead q IN R    by poly_lead_element
   If lead q = #0,
      then q = |0|                    by poly_lead_eq_zero
        so p * q = |0|                by poly_mult_rzero
           lead (p * q)
         = lead |0| = #0              by poly_lead_zero
         = lead p * lead q            by ring_mult_rzero
   If lead q <> #0,
      then lead p * lead q <> #0      by ring_unit_mult_zero
        so lead (p * q)
         = lead p * lead q            by weak_lead_mult_nonzero
*)
val poly_lead_mult_unit = store_thm(
  "poly_lead_mult_unit",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ unit (lead p) ==> (lead (p * q) = lead p * lead q)``,
  rpt strip_tac >>
  `lead p IN R /\ lead q IN R` by rw[] >>
  Cases_on `lead q = #0` >| [
    `q = |0|` by rw[GSYM poly_lead_eq_zero] >>
    rw[],
    rw[ring_unit_mult_zero, weak_lead_mult_nonzero]
  ]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q /\ unit (lead q) ==> (lead (p * q) = lead p * lead q) *)
(* Proof:
      lead (p * q)
    = lead (q * p)          by poly_mult_comm
    = lead q * lead p       by poly_lead_mult_unit
    = lead p * lead q       by poly_lead_element, ring_mult_comm
*)
val poly_lead_mult_unit_comm = store_thm(
  "poly_lead_mult_unit_comm",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ unit (lead q) ==> (lead (p * q) = lead p * lead q)``,
  metis_tac[poly_lead_mult_unit, poly_mult_comm, poly_lead_element, ring_mult_comm, poly_is_weak]);

(* Theorem: Ring r ==>
            !p q. poly p /\ poly q /\ unit (lead p) /\ lead q <> #0 ==> (deg (p * q) = deg p + deg q) *)
(* Proof:
    Note lead p IN R /\ lead q IN R      by poly_lead_element
   Since lead q <> #0,
    then lead p * lead q <> #0           by ring_unit_mult_zero
      so deg (p * q) = deg p + deg q     by weak_deg_mult_nonzero
*)
val poly_deg_mult_unit = store_thm(
  "poly_deg_mult_unit",
  ``!r:'a ring. Ring r ==>
   !p q. poly p /\ poly q /\ unit (lead p) /\ lead q <> #0 ==> (deg (p * q) = deg p + deg q)``,
  rw[ring_unit_mult_zero, weak_deg_mult_nonzero]);

(* Theorem: Ring r ==>
            !p q. poly p /\ poly q /\ lead p <> #0 /\ unit (lead q) ==> (deg (p * q) = deg p + deg q) *)
(* Proof:
      deg (p * q)
    = deg (q * p)        by poly_mult_comm
    = deg q + deg p      by poly_deg_mult_unit
    = deg p + deg q      by ADD_COMM
*)
val poly_deg_mult_unit_comm = store_thm(
  "poly_deg_mult_unit_comm",
  ``!r:'a ring. Ring r ==>
   !p q. poly p /\ poly q /\ lead p <> #0 /\ unit (lead q) ==> (deg (p * q) = deg p + deg q)``,
  metis_tac[poly_deg_mult_unit, poly_mult_comm, ADD_COMM]);

(* ------------------------------------------------------------------------- *)
(* Polynomial as scalar multiple of an ring unit                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r /\ poly p /\ c IN R /\ unit c ==> (p = [c] * (( |/c) * p)) *)
(* Proof:
   Note |/c IN R               by ring_unit_inv_element
   Thus [c] * (( |/c) * p)
      = c * (( |/c) * p)       by poly_mult_lconst
      = (c * |/c) * p          by poly_cmult_cmult
      = #1 * p                 by ring_unit_rinv
      = p                      by poly_cmult_lone
*)
val poly_cmult_unit = store_thm(
  "poly_cmult_unit",
  ``!r:'a ring p c. Ring r /\ poly p /\ c IN R /\ unit c ==> (p = [c] * (( |/c) * p))``,
  rpt strip_tac >>
  `|/c IN R` by rw[ring_unit_inv_element] >>
  `[c] * (( |/c) * p) = c * (( |/c) * p)` by rw[poly_mult_lconst] >>
  `_ = (c * |/c) * p` by rw[poly_cmult_cmult] >>
  `_ = #1 * p` by rw[ring_unit_rinv] >>
  `_ = p` by rw[] >>
  simp[]);

(* Theorem: Ring r /\ poly p /\ c IN R /\ unit c ==> (p = (( |/c) * p) * [c]) *)
(* Proof:
   Note |/c IN R                 by ring_unit_inv_element
   Then  (( |/c) * p) * [c]
        = c * (( |/c) * p)       by poly_mult_rconst
        = (c * |/c) * p          by poly_cmult_cmult
        = #1 * p                 by ring_unit_rinv
        = p                      by poly_cmult_lone
*)
val poly_cmult_unit_comm = store_thm(
  "poly_cmult_unit_comm",
  ``!r:'a ring p c. Ring r /\ poly p /\ c IN R /\ unit c ==> (p = (( |/c) * p) * [c])``,
  rpt strip_tac >>
  `|/c IN R` by rw[ring_unit_inv_element] >>
  `(( |/c) * p) * [c] = c * (( |/c) * p)` by rw[poly_mult_rconst] >>
  `_ = (c * |/c) * p` by rw[poly_cmult_cmult] >>
  `_ = #1 * p` by rw[ring_unit_rinv] >>
  `_ = p` by rw[] >>
  simp[]);

(* Theorem: Ring r /\ poly p /\ c IN R /\ unit c ==>
            (p = (( |/c) * p) * [c] + |0|) *)
(* Proof:
   Note |/c IN R                                by ring_unit_inv_element
    and (( |/c) * p) * [c] = c * (( |/c) * p)   by poly_mult_rconst
   Thus poly ((( |/c) * p) * [c])               by poly_cmult_poly
     so p = (( |/c) * p) * [c]                  by poly_cmult_unit_comm
          = (( |/c) * p) * [c] + |0|            by poly_add_rzero
*)
val poly_cmult_unit_eqn = store_thm(
  "poly_cmult_unit_eqn",
  ``!r:'a ring p c. Ring r /\ poly p /\ c IN R /\ unit c ==>
         (p = (( |/c) * p) * [c] + |0|)``,
  rpt strip_tac >>
  `|/c IN R` by rw[ring_unit_inv_element] >>
  `(( |/c) * p) * [c] = c * (( |/c) * p)` by rw[poly_mult_rconst] >>
  `poly (c * (( |/c) * p))` by rw[] >>
  metis_tac[poly_cmult_unit_comm, poly_add_rzero]);

(* This is to prepare for polynomimal division by a constant polynomial. *)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
