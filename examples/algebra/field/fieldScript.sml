(* ------------------------------------------------------------------------ *)
(* Field Theory - from axioms to exponentiation.                            *)
(* ------------------------------------------------------------------------ *)

(*

Field Theory
============
based on: examples/elliptic/fieldScript.sml

Formalizing Elliptic Curve Cryptography in Higher Order Logic (Joe Hurd)
http://www.gilith.com/research/papers/elliptic.pdf

*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "field";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory arithmeticTheory dividesTheory gcdTheory gcdsetTheory
     numberTheory combinatoricsTheory;

open monoidTheory groupTheory ringTheory;

val _ = intLib.deprecate_int ();

(* ------------------------------------------------------------------------- *)
(* Field Documentation                                                       *)
(* ------------------------------------------------------------------------- *)
(* Data type (same as ring):
   The generic symbol for field data is r (from Ring).
   r.carrier = Carrier set of Ring, overloaded as R.
   r.sum     = Addition component of Ring, binary operation overloaded as +.
   r.prod    = Multiplication component of Ring, binary operation overloaded as *.

   Overloading:
   +    = r.sum.op
   #0   = r.sum.id
   ##   = r.sum.exp
   -    = r.sum.inv

   *    = r.prod.op
   #1   = r.prod.id
   **   = r.prod.exp

   R   = r.carrier
   R+  = ring_nonzero r
   r*  = Invertibles r.prod
   R*  = r*.carrier
   f*  = (r.prod excluding #0)
   F*  = f*.carrier

   |/ x  = f*.inv x
   x / y = field_div r x y

*)
(* Definitions and Theorems (# are exported):

   Definitions:
   Field_def        |- !r. Field r <=> Ring r /\ Group f*
   FiniteField_def  |- !r. FiniteField r <=> Field r /\ FINITE R

   Extract from definition:
#  field_is_ring          |- !r. Field r ==> Ring r
   finite_field_is_field  |- !r. FiniteField r ==> Field r /\ FINITE R
   finite_field_is_finite_ring  |- !r. FiniteField r ==> FiniteRing r
#  field_carriers         |- !r. Field r ==> (r.sum.carrier = R) /\ (r.prod.carrier = R)
   field_mult_carrier     |- !r. Field r ==> (F* = R+)
   field_carrier_nonempty |- !r. Field r ==> R <> {}
   finite_field_alt       |- !r. FiniteField r <=> FiniteRing r /\ FiniteGroup f*

   Lifting Theorems from Ring:
   field_add_group      |- !r. Field r ==> Group r.sum /\ (r.sum.carrier = R) /\
                           !x y. x IN R /\ y IN R ==> (x + y = y + x)
   field_mult_monoid    |- !r. Field r ==> Monoid r.prod /\ (r.prod.carrier = R) /\
                           !x y. x IN R /\ y IN R ==> (x * y = y * x)
   field_zero_element   |- !r. Field r ==> #0 IN R
   field_one_element    |- !r. Field r ==> #1 IN R

   Field Addition Theorems from Ring (r.sum):
   field_add_element    |- !r. Field r ==> !x y. x IN R /\ y IN R ==> x + y IN R
   field_add_assoc      |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x + y + z = x + (y + z))
   field_add_comm       |- !r. Field r ==> !x y. x IN R /\ y IN R ==> (x + y = y + x)
   field_add_assoc_comm |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x + (y + z) = y + (x + z))
   field_add_zero_zero  |- !r. Field r ==> (#0 + #0 = #0)
   field_add_lzero      |- !r. Field r ==> !x. x IN R ==> (#0 + x = x)
   field_add_rzero      |- !r. Field r ==> !x. x IN R ==> (x + #0 = x)
   field_zero_unique    |- !r. Field r ==> !x y. x IN R /\ y IN R ==>
                           ((y + x = x) <=> (y = #0)) /\ ((x + y = x) <=> (y = #0))

   Field Multiplication Theorems from Ring (r.prod):
   field_mult_element    |- !r. Field r ==> !x y. x IN R /\ y IN R ==> x * y IN R
   field_mult_assoc      |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x * y * z = x * (y * z))
   field_mult_comm       |- !r. Field r ==> !x y. x IN R /\ y IN R ==> (x * y = y * x)
   field_mult_assoc_comm |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x * (y * z) = y * (x * z))
   field_mult_rzero      |- !r. Field r ==> !x. x IN R ==> (x * #0 = #0)
   field_mult_lzero      |- !r. Field r ==> !x. x IN R ==> (#0 * x = #0)
   field_mult_zero_zero  |- !r. Field r ==> (#0 * #0 = #0)
   field_mult_one_one    |- !r. Field r ==> (#1 * #1 = #1)
   field_mult_lone       |- !r. Field r ==> !x. x IN R ==> (#1 * x = x)
   field_mult_rone       |- !r. Field r ==> !x. x IN R ==> (x * #1 = x)

   Field Numerical Theorems from Ring:
   field_num_0             |- !r. ##0 = #0
   field_num_1             |- !r. Field r ==> (##1 = #1)
   field_num_element       |- !r. Field r ==> !n. ##n IN R
   field_num_mult_element  |- !r. Field r ==> !x. x IN R ==> !n. ##n * x IN R
   field_num_SUC           |- !r n. Field r ==> (##(SUC n) = #1 + ##n)
   field_num_suc           |- !r. Field r ==> !n. ##(SUC n) = ##n + #1

   Field Exponential Theorems from Ring:
   field_exp_element  |- !r. Field r ==> !x. x IN R ==> !n. x ** n IN R
   field_exp_0        |- !x. x ** 0 = #1
   field_exp_SUC      |- !x n. x ** SUC n = x * x ** n
   field_exp_suc      |- !r. Field r ==> !x. x IN R ==> !n. x ** SUC n = x ** n * x
   field_exp_1        |- !r. Field r ==> !x. x IN R ==> (x ** 1 = x)
   field_exp_comm     |- !r. Field r ==> !x. x IN R ==> !n. x ** n * x = x * x ** n
   field_mult_exp     |- !r. Field r ==> !x y. x IN R /\ y IN R ==> !n. (x * y) ** n = x ** n * y ** n
   field_exp_small    |- !r. Field r ==> !x. x IN R ==>
                         (x ** 0 = #1) /\ (x ** 1 = x) /\ (x ** 2 = x * x) /\
                         (x ** 3 = x * x ** 2) /\ (x ** 4 = x * x ** 3) /\
                         (x ** 5 = x * x ** 4) /\ (x ** 6 = x * x ** 5) /\
                         (x ** 7 = x * x ** 6) /\ (x ** 8 = x * x ** 7) /\ (x ** 9 = x * x ** 8)

   Field Distribution Theorems from Ring:
   field_mult_radd      |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==>
                                           (x * (y + z) = x * y + x * z)
   field_mult_ladd      |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==>
                                           ((y + z) * x = y * x + z * x)
   field_mult_add       |- !r. Field r ==> !z y x. x IN R /\ y IN R /\ z IN R ==>
                                           (x * (y + z) = x * y + x * z) /\ ((y + z) * x = y * x + z * x)
   field_num_mult_suc   |- !r. Field r ==> !x. x IN R ==> !n. ##(SUC n) * x = ##n * x + x
   field_num_mult_small |- !r. Field r ==> !x. x IN R ==>
                                           (#0 * x = #0) /\ (#1 * x = x) /\
                                           (##2 * x = x + x) /\ (##3 * x = ##2 * x + x)

   Field Negation Theorems from Ring:
   field_neg_element    |- !r. Field r ==> !x. x IN R ==> -x IN R
   field_neg_zero       |- !r. Field r ==> (-#0 = #0)
   field_add_lneg       |- !r. Field r ==> !x. x IN R ==> (-x + x = #0)
   field_add_lneg_assoc |- !r. Field r ==> !x y. x IN R /\ y IN R ==>
                           (y = x + (-x + y)) /\ (y = -x + (x + y))
   field_add_rneg       |- !r. Field r ==> !x. x IN R ==> (x + -x = #0)
   field_add_rneg_assoc |- !r. Field r ==> !x y. x IN R /\ y IN R ==>
                           (y = y + -x + x) /\ (y = y + x + -x)
   field_add_lcancel    |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==>
                           ((x + y = x + z) <=> (y = z))
   field_add_rcancel    |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==>
                           ((y + x = z + x) <=> (y = z))
   field_zero_fix       |- !r. Field r ==> !x. x IN R ==> ((x + x = x) <=> (x = #0))
   field_neg_neg        |- !r. Field r ==> !x. x IN R ==> (--x = x)
   field_neg_eq_zero    |- !r. Field r ==> !x. x IN R ==> ((-x = #0) <=> (x = #0))
   field_neg_eq         |- !r. Field r ==> !x y. x IN R /\ y IN R ==> ((-x = -y) <=> (x = y))
   field_neg_eq_swap    |- !r. Field r ==> !x y. x IN R /\ y IN R ==> ((-x = y) <=> (x = -y))
   field_add_eq_zero    |- !r. Field r ==> !x y. x IN R /\ y IN R ==> ((x + y = #0) <=> (y = -x))
   field_neg_add_comm   |- !r. Field r ==> !x y. x IN R /\ y IN R ==> (-(x + y) = -y + -x)
   field_neg_add        |- !r. Field r ==> !x y. x IN R /\ y IN R ==> (-(x + y) = -x + -y)

   Field Distribution Theorems with Negation from Ring:
   field_mult_lneg      |- !r. Field r ==> !x y. x IN R /\ y IN R ==> (-x * y = -(x * y))
   field_mult_rneg      |- !r. Field r ==> !x y. x IN R /\ y IN R ==> (x * -y = -(x * y))
   field_neg_mult       |- !r. Field r ==> !x y. x IN R /\ y IN R ==>
                           (-(x * y) = -x * y) /\ (-(x * y) = x * -y)
   field_mult_neg_neg   |- !r. Field r ==> !x y. x IN R /\ y IN R ==> (-x * -y = x * y)

   More Field Numeral Theorems from Ring (with distribution):
   field_num_add        |- !r. Field r ==> !n k. ##(n + k) = ##n + ##k
   field_num_add_assoc  |- !r. Field r ==> !x. x IN R ==> !m n. ##m + (##n + x) = ##(m + n) + x
   field_num_mult       |- !r. Field r ==> !m n. ##m * ##n = ##(m * n)
   field_num_mult_assoc |- !r. Field r ==> !m n (x::R). ##m * (##n * x) = ##(m * n) * x
   field_num_exp        |- !r. Field r ==> !m n. ##m ** n = ##(m ** n)
   field_num_add_mult   |- !r. Field r ==> !x. x IN R ==> !m n. ##(m + n) * x = ##m * x + ##n * x
   field_num_add_mult_assoc  |- !r. Field r ==> !x y. x IN R /\ y IN R ==>
                                !m n. ##(m + n) * x + y = ##m * x + (##n * x + y)
   field_num_mult_neg   |- !r. Field r ==> !x. x IN R ==> !n. -(##n * x) = ##n * -x
   field_num_mult_radd  |- !r. Field r ==> !x y. x IN R /\ y IN R ==> !n. ##n * (x + y) = ##n * x + ##n * y
   field_single_add_single   |- !r. Field r ==> !x. x IN R ==> (x + x = ##2 * x)
   field_single_add_single_assoc  |- !r. Field r ==> !x y. x IN R /\ y IN R ==> (x + (x + y) = ##2 * x + y)
   field_single_add_mult     |- !r. Field r ==> !x. x IN R ==> !n. x + ##n * x = ##(n + 1) * x
   field_single_add_mult_assoc  |- !r. Field r ==> !x y. x IN R /\ y IN R ==>
                                   !n. x + (##n * x + y) = ##(n + 1) * x + y
   field_single_add_neg_mult |- !r. Field r ==> !x. x IN R ==>
                        !n. x + -(##n * x) = if n = 0 then x else -(##(n - 1) * x)
   field_single_add_neg_mult_assoc  |- !r. Field r ==> !x y. x IN R /\ y IN R ==>
                        !n. x + (-(##n * x) + y) = if n = 0 then x + y else -(##(n - 1) * x) + y
   field_mult_add_neg   |- !r. Field r ==> !x. x IN R ==>
                           !n. ##n * x + -x = if n = 0 then -x else ##(n - 1) * x
   field_mult_add_neg_assoc  |- !r. Field r ==> !x y. x IN R /\ y IN R ==>
                                !n. ##n * x + (-x + y) = if n = 0 then -x + y else ##(n - 1) * x + y
   field_mult_add_neg_mult   |- !r. Field r ==> !x. x IN R ==>
                       !m n. ##m * x + -(##n * x) = if m < n then -(##(n - m) * x) else ##(m - n) * x
   field_mult_add_neg_mult_assoc  |- !r. Field r ==> !x y. x IN R /\ y IN R ==>
         !m n. ##m * x + (-(##n * x) + y) = if m < n then -(##(n - m) * x) + y else ##(m - n) * x + y
   field_neg_add_neg    |- !r. Field r ==> !x. x IN R ==> (-x + -x = -(##2 * x))
   field_neg_add_neg_assoc   |- !r. Field r ==> !x y. x IN R /\ y IN R ==> (-x + (-x + y) = -(##2 * x) + y)
   field_neg_add_neg_mult    |- !r. Field r ==> !x. x IN R ==> !n. -x + -(##n * x) = -(##(n + 1) * x)
   field_neg_add_neg_mult_assoc  |- !r. Field r ==> !x y. x IN R /\ y IN R ==>
                                    !n. -x + (-(##n * x) + y) = -(##(n + 1) * x) + y
   field_neg_mult_add_neg_mult   |- !r. Field r ==> !x. x IN R ==>
                                    !m n. -(##m * x) + -(##n * x) = -(##(m + n) * x)
   field_neg_mult_add_neg_mult_assoc  |- !r. Field r ==> !x y. x IN R /\ y IN R ==>
                                         !m n. -(##m * x) + (-(##n * x) + y) = -(##(m + n) * x) + y

   More Field Exponent Theorems from Ring:
   field_single_mult_single |- !r. Field r ==> !x. x IN R ==> (x * x = x ** 2)
   field_single_mult_single_assoc  |- !r. Field r ==> !x y. x IN R /\ y IN R ==> (x * (x * y) = x ** 2 * y)
   field_single_mult_exp    |- !r. Field r ==> !x. x IN R ==> !n. x * x ** n = x ** (n + 1)
   field_single_mult_exp_assoc     |- !r. Field r ==> !x y. x IN R /\ y IN R ==>
                                      !n. x * (x ** n * y) = x ** (n + 1) * y
   field_exp_add        |- !r. Field r ==> !x. x IN R ==> !n k. x ** (n + k) = x ** n * x ** k
   field_exp_add_assoc  |- !r. Field r ==> !x y. x IN R /\ y IN R ==>
                               !n k. x ** n * (x ** k * y) = x ** (n + k) * y
   field_one_exp        |- !r. Field r ==> !n. #1 ** n = #1
   field_zero_exp       |- !r. Field r ==> !n. #0 ** n = if n = 0 then #1 else #0
   field_exp_mult       |- !r. Field r ==> !x. x IN R ==> !n k. x ** (n * k) = (x ** n) ** k
   field_exp_mult_comm  |- !r. Field r ==> !x. x IN R ==> !m n. (x ** m) ** n = (x ** n) ** m
   field_neg_square     |- !r. Field r ==> !x. x IN R ==> (-x ** 2 = x ** 2)
   field_exp_neg        |- !r. Field r ==> !x. x IN R ==> !n. -x ** n = if EVEN n then x ** n else -(x ** n)
   field_neg_exp        |- !r. Field r ==> !x. x IN R ==> !n. -x ** n = if EVEN n then x ** n else -(x ** n)
   field_num_mult_exp   |- !r. Field r ==> !k m n. ##k * ##m ** n = ##(k * m ** n)

   Field Subtraction Theorems from Ring:
   field_sub_def      |- !r x y. x - y = x + -y
   field_sub_zero     |- !r. Field r ==> !x. x IN R ==> (x - #0 = x)
   field_sub_eq_zero  |- !r. Field r ==> !x y. x IN R /\ y IN R ==> ((x - y = #0) <=> (x = y))
   field_sub_eq       |- !r. Field r ==> !x. x IN R ==> (x - x = #0)
   field_sub_element  |- !r. Field r ==> !x y. x IN R /\ y IN R ==> x - y IN R
   field_zero_sub     |- !r. Field r ==> !x. x IN R ==> (#0 - x = -x)
   field_sub_lcancel  |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((x - y = x - z) <=> (y = z))
   field_sub_rcancel  |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((y - x = z - x) <=> (y = z))
   field_neg_sub      |- !r. Field r ==> !x y. x IN R /\ y IN R ==> (-(x - y) = y - x)
   field_add_sub      |- !r. Field r ==> !x y. x IN R /\ y IN R ==> (x + y - y = x)
   field_add_sub_comm |- !r. Field r ==> !x y. x IN R /\ y IN R ==> (y + x - y = x)
   field_sub_add      |- !r. Field r ==> !x y. x IN R /\ y IN R ==> (x - y + y = x)
   field_sub_eq_add   |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((x - y = z) <=> (x = y + z))
   field_sub_pair_reduce  |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==>
                                             (x + z - (y + z) = x - y)
   field_add_sub_identity |- !r. Field r ==> !x y z t. x IN R /\ y IN R /\ z IN R /\ t IN R ==>
                                             ((x + y = z + t) <=> (x - z = t - y))
   field_mult_lsub    |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x * z - y * z = (x - y) * z)
   field_mult_rsub    |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x * y - x * z = x * (y - z))
   field_add_pair_sub   |- !r. Field r ==> !x y p q. x IN R /\ y IN R /\ p IN R /\ q IN R ==>
                                           (x + y - (p + q) = x - p + (y - q))
   field_mult_pair_sub  |- !r. Field r ==> !x y p q. x IN R /\ y IN R /\ p IN R /\ q IN R ==>
                                           (x * y - p * q = (x - p) * (y - q) + (x - p) * q + p * (y - q))
   field_num_sub      |- !r. Field r ==> !n m. m < n ==> (##(n - m) = ##n - ##m)

   Field Binomial Expansions from Ring:
   field_binomial_2  |- !r. Field r ==> !x y. x IN R /\ y IN R ==>
   ((x + y) ** 2 = x ** 2 + (##2 * (x * y) + y ** 2))
   field_binomial_3  |- !r. Field r ==> !x y. x IN R /\ y IN R ==>
   ((x + y) ** 3 = x ** 3 + (##3 * (x ** 2 * y) + (##3 * (x * y ** 2) + y ** 3)))
   field_binomial_4  |- !r. Field r ==> !x y.  x IN R /\ y IN R ==>
   ((x + y) ** 4 = x ** 4 + (##4 * (x ** 3 * y) + (##6 * (x ** 2 * y ** 2) + (##4 * (x * y ** 3) + y ** 4))))

   Field specific theorems, about nonzeroes, inverses and division:

   Field Theorems (not from Ring):
   field_nonzero_def            |- !r. R+ = R DIFF {#0}
   field_nonzero_eq             |- !r x. x IN R+ <=> x IN R /\ x <> #0
   field_nonzero_element        |- !r x. x IN R+ ==> x IN R
   field_nonzero_subset         |- !r. R+ SUBSET R
   field_nonzero_finite         |- !r. FINITE R ==> FINITE R+
   field_nonzero_monoid         |- !r. Field r ==> Monoid f*
   field_nonzero_group          |- !r. Field r ==> Group f*
   field_nonzero_mult_is_group  |- !r. Field r ==> Group f*
   field_nonzero_mult_property  |- !r. Field r ==> (F* = R+ ) /\
                                                   (f*.id = #1) /\
                                                   (f*.op = $* ) /\
                                                   (f*.exp = $** )
   field_nonzero_exp            |- !r. Field r ==> (f*.exp = $** )
   field_nonzero_mult_is_abelian_group  |- !r. Field r ==> AbelianGroup f*

   field_mult_group   |- !r. Field r ==> Group f* /\
                                         (F* = R+ ) /\
                                         !x y. x IN R+ /\ y IN R+ ==> (x * y = y * x)
   finite_field_mult_finite_group       |- !r. FiniteField r ==> FiniteGroup f*
   finite_field_mult_carrier_card       |- !r. FiniteField r ==> (CARD F* = CARD R - 1)

#  field_mult_nonzero |- !r. Field r ==> !x y. x IN R+ /\ y IN R+ ==> x * y IN R+
   field_id_unique    |- !r. Field r ==> !x y. x IN R+ /\ y IN R+ ==>
                         ((y * x = x) <=> (y = #1)) /\ ((x * y = x) <=> (y = #1))
   field_mult_eq_zero |- !r. Field r ==> !x y. x IN R /\ y IN R ==> ((x * y = #0) <=> (x = #0) \/ (y = #0))
   field_zero_product |- !r. Field r ==> !x y. x IN R /\ y IN R ==> ((x * y = #0) <=> (x = #0) \/ (y = #0))
   field_num_2        |- !r. Field r ==> (##2 = #1 + #1)
   field_nonzero_element_alt  |- !r. Field r ==> !x. x IN F* ==> x IN R
   field_nonzero_alt          |- !r. Field r ==> !x. x IN R /\ x <> #0 ==> x IN F*
#  field_one_ne_zero          |- !r. Field r ==> #1 <> #0
#  field_one_nonzero          |- !r. Field r ==> #1 IN R+
   field_nonzero_carrier_nonempty  |- !r. Field r ==> R+ <> {}
   field_nonzero_card_pos     |- !r. FiniteField r ==> 0 < CARD R+
   field_nonzero_card_eq_1    |- !r. FiniteField r ==> ((R+ = {#1}) <=> (CARD R+ = 1))
   field_nonzero_unit         |- !r. Field r ==> !x. x IN R+ <=> unit x

   Field Exponential Nonzero Theorems:
#  field_exp_nonzero  |- !r. Field r ==> !x. x IN R+ ==> !n. x ** n IN R+
   field_exp_eq_zero  |- !r. Field r ==> !x. x IN R ==> !n. (x ** n = #0) <=> n <> 0 /\ (x = #0)

   Field Inversion Theorems (with lifting Group Inverse Theorem for Field):
   field_mult_inv         |- !r. Field r ==> !x. x IN R+ ==> (f*.inv x = |/ x)
   field_rinv_unique      |- !r. Field r ==> !x y. x IN R+ /\ y IN R+ ==> ((x * y = #1) <=> (y = |/ x))
   field_linv_unique      |- !r. Field r ==> !x y. x IN R+ /\ y IN R+ ==> ((y * x = #1) <=> (y = |/ x))
#  field_inv_nonzero      |- !r. Field r ==> !x. x IN R+ ==> |/ x IN R+
#  field_inv_element      |- !r. Field r ==> !x. x IN R+ ==> |/ x IN R
#  field_mult_linv        |- !r. Field r ==> !x. x IN R+ ==> ( |/ x * x = #1)
#  field_mult_rinv        |- !r. Field r ==> !x. x IN R+ ==> (x * |/ x = #1)
   field_mult_linv_assoc  |- !r. Field r ==> !x y. x IN R+ /\ y IN R ==>
                                 (y = x * ( |/ x * y)) /\ (y = |/ x * (x * y))
   field_mult_rinv_assoc  |- !r. Field r ==> !x y. x IN R+ /\ y IN R ==>
                                 (y = y * |/ x * x) /\ (y = y * x * |/ x)
   field_mult_lcancel     |- !r. Field r ==> !x y z.  x IN R+ /\ y IN R /\ z IN R ==>
                                 ((x * y = x * z) <=> (y = z))
   field_mult_rcancel     |- !r. Field r ==> !x y z.  x IN R+ /\ y IN R /\ z IN R ==>
                                 ((y * x = z * x) <=> (y = z))
   field_nonzero_mult_eq_self   |- !r. Field r ==> !x. x IN R+ ==>
                                   !y. y IN R /\ ((x * y = x) \/ (y * x = x)) ==> (y = #1)
   field_mult_linv_eq_one |- !r. Field r ==> !x y. x IN R+ /\ y IN R+ ==> (( |/ x * y = #1) <=> (x = y))
   field_mult_rinv_eq_one |- !r. Field r ==> !x y. x IN R+ /\ y IN R+ ==> ((x * |/ y = #1) <=> (x = y))
   field_mult_linv_eqn    |- !r. Field r ==> !x y z. x IN R+ /\ y IN R /\ z IN R ==> (( |/ x * y = z) <=> (y = x * z))
   field_mult_rinv_eqn    |- !r. Field r ==> !x y z. x IN R /\ y IN R+ /\ z IN R ==> ((x * |/ y = z) <=> (x = z * y))
   field_inv_mult_comm    |- !r. Field r ==> !x y. x IN R+ /\ y IN R+ ==> ( |/ (x * y) = |/ y * |/ x)
#  field_inv_mult         |- !r. Field r ==> !x y. x IN R+ /\ y IN R+ ==> ( |/ (x * y) = |/ x * |/ y)
#  field_inv_one          |- !r. Field r ==> ( |/ #1 = #1)
#  field_inv_inv          |- !r. Field r ==> !x. x IN R+ ==> ( |/ ( |/ x) = x)
#  field_neg_nonzero      |- !r. Field r ==> !x. x IN R+ ==> -x IN R+
#  field_inv_neg          |- !r. Field r ==> !x. x IN R+ ==> ( |/ (-x) = -|/ x)
#  field_inv_exp          |- !r. Field r ==> !x. x IN R+ ==> !n. |/ x ** n = |/ (x ** n)
   field_exp_inv          |- !r. Field r ==> !x. x IN R+ ==> !n. |/ (x ** n) = |/ x ** n
   field_mult_exp_inv     |- !r. Field r ==> !x. x IN R+ ==>
                             !n. x ** n * |/ x = if n = 0 then |/ x else x ** (n - 1)
   field_mult_exp_inv_assoc |- !r. Field r ==> !x y. x IN R+ /\ y IN R ==>
                               !n. x ** n * ( |/ x * y) = if n = 0 then |/ x * y else x ** (n - 1) * y
   field_mult_exp_inv_exp   |- !r. Field r ==> !x. x IN R+ ==>
                               !m n. x ** m * |/ (x ** n) = if m < n then |/ (x ** (n - m)) else x ** (m - n)
   field_mult_exp_inv_exp_assoc |- !r. Field r ==> !x y. x IN R+ /\ y IN R ==>
                 !m n. x ** m * ( |/ (x ** n) * y) = if m < n then |/ (x ** (n - m)) * y else x ** (m - n) * y
   field_inv_mult_inv           |- !r. Field r ==> !x. x IN R+ ==> ( |/ x * |/ x = |/ (x ** 2))
   field_inv_mult_inv_assoc     |- !r. Field r ==> !x y. x IN R+ /\ y IN R ==>
                                       ( |/ x * ( |/ x * y) = |/ (x ** 2) * y)
   field_inv_mult_inv_exp       |- !r. Field r ==> !x. x IN R+ ==>
                                   !n. |/ x * |/ (x ** n) = |/ (x ** (n + 1))
   field_inv_mult_inv_exp_assoc |- !r. Field r ==> !x y.  x IN R+ /\ y IN R ==>
                                   !n. |/ x * ( |/ (x ** n) * y) = |/ (x ** (n + 1)) * y
   field_inv_exp_mult_inv_exp   |- !r. Field r ==> !x. x IN R+ ==>
                                   !m n. |/ (x ** m) * |/ (x ** n) = |/ (x ** (m + n))
   field_inv_exp_mult_inv_exp_assoc |- !r. Field r ==> !x y. x IN R+ /\ y IN R ==>
                                       !m n. |/ (x ** m) * ( |/ (x ** n) * y) = |/ (x ** (m + n)) * y
   field_single_mult_inv_exp        |- !r. Field r ==> !x. x IN R+ ==>
                                       !n. x * |/ (x ** n) = if n = 0 then x else |/ (x ** (n - 1))
   field_single_mult_inv_exp_assoc  |- !r. Field r ==> !x y. x IN R+ /\ y IN R ==>
                          !n. x * ( |/ (x ** n) * y) = if n = 0 then x * y else |/ (x ** (n - 1)) * y

   Field Division Theorems:
#  field_div_def        |- !r x y. x / y = x * |/ y
#  field_div_element    |- !r. Field r ==> !x y. x IN R /\ y IN R+ ==> x / y IN R
#  field_div_nonzero    |- !r. Field r ==> !x y. x IN R+ /\ y IN R+ ==> x / y IN R+
#  field_div_lneg       |- !r. Field r ==> !x y. x IN R /\ y IN R+ ==> (-x / y = -(x / y))
#  field_div_rneg       |- !r. Field r ==> !x y. x IN R /\ y IN R+ ==> (x / -y = -(x / y))
   field_neg_div        |- !r. Field r ==> !x y. x IN R /\ y IN R+ ==>
                           (-(x / y) = -x / y) /\ (-(x / y) = x / -y)
   field_div_ladd       |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==>
                           (x + y / z = (x * z + y) / z)
   field_div_radd       |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==>
                           (y / z + x = (y + x * z) / z)
   field_div_lsub       |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==>
                           (x - y / z = (x * z - y) / z)
   field_div_rsub       |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==>
                           (y / z - x = (y - x * z) / z)
   field_div_lmult      |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==> (x * (y / z) = x * y / z)
   field_div_rmult      |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==> (y / z * x = y * x / z)
   field_div_exp        |- !r. Field r ==> !x y. x IN R /\ y IN R+ ==> !n. (x / y) ** n = x ** n / y ** n
   field_div_ldiv       |- !r. Field r ==> !x y z. x IN R /\ y IN R+ /\ z IN R+ ==> (x / y / z = x / (y * z))
   field_div_rdiv       |- !r. Field r ==> !x y z. x IN R /\ y IN R+ /\ z IN R+ ==> (x / (y / z) = x * z / y)
   field_add_ldiv       |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==>
                           (y / z + x = (y + z * x) / z)
   field_add_ldiv_assoc |- !r. Field r ==> !x y t z. x IN R /\ y IN R /\ t IN R /\ z IN R+ ==>
                           (y / z + (x + t) = (y + z * x) / z + t)
   field_add_rdiv       |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==>
                           (x + y / z = (z * x + y) / z)
   field_add_rdiv_assoc |- !r. Field r ==> !x y t z. x IN R /\ y IN R /\ t IN R /\ z IN R+ ==>
                                           (x + (y / z + t) = (z * x + y) / z + t)
   field_div_mult_cancel  |- !r. Field r ==> !x y. x IN R /\ y IN R+ ==> (x / y * y = x)
   field_div_add_common   |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==>
                             (x / z + y / z = (x + y) / z)
   field_add_div          |- !r. Field r ==> !v w x y z. v IN R /\ w IN R /\ x IN R+ /\ y IN R+ /\ z IN R+ ==>
                             (v / (x * y) + w / (x * z) = (z * v + y * w) / (x * (y * z)))
   field_add_div_assoc    |- !r. Field r ==> !v w t x y z. v IN R /\ w IN R /\ t IN R /\ x IN R+ /\ y IN R+ /\ z IN R+ ==>
                             (v / (x * y) + (w / (x * z) + t) = (z * v + y * w) / (x * (y * z)) + t)
   field_mult_div_cancel  |- !r. Field r ==> !x y. x IN R /\ y IN R+ ==> (x * y / y = x)
   field_div_cancel       |- !r. Field r ==> !x y z. x IN R+ /\ y IN R /\ z IN R+ ==>
                                             (x * y / (x * z) = y / z)
   field_inv_not_zero     |- !r. Field r ==> !x. x IN R+ ==> |/ x <> #0
   field_div_eq_zero      |- !r. Field r ==> !x y. x IN R /\ y IN R+ ==> ((x / y = #0) <=> (x = #0))
   field_zero_divides     |- !r. Field r ==> !x. x IN R ==> (#0 rdivides x <=> (x = #0))
   field_mult_div_eqn     |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==> (x = y * z <=> y = x / z)
   field_mult_div_comm    |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==> (x = z * y <=> y = x / z)

   Field and Integral Domain:
   field_is_integral_domain   |- !r. Field r ==> IntegralDomain r
   field_exp_eq               |- !r. Field r ==> !x. x IN R /\ x <> #0 ==>
                                 !m n. m < n /\ (x ** m = x ** n) ==> (x ** (n - m) = #1)
   finite_field_is_finite_integral_domain  |- !r. FiniteField r ==> FiniteIntegralDomain r
   finite_integral_domain_is_field         |- !r. FiniteIntegralDomain r ==> Field r
   finite_integral_domain_is_finite_field  |- !r. FiniteIntegralDomain r ==> FiniteField r
   finite_integral_domain_eq_finite_field  |- !r. FiniteIntegralDomain r <=> FiniteField r
   finite_field_from_finite_ring  |- !r. FiniteRing r /\ #1 <> #0 /\
                                    (!x y. x IN R /\ y IN R ==> ((x * y = #0) <=> (x = #0) \/ (y = #0))) ==>
                                     FiniteField r

   Field Defintion without explicit mention of Ring:
   field_def_alt     |- !r. Field r <=> AbelianGroup r.sum /\ AbelianGroup f* /\
                                       (r.sum.carrier = R) /\ (r.prod.carrier = R) /\
                                       (!x. x IN R ==> (#0 * x = #0)) /\
                                       !x y z. x IN R /\ y IN R /\ z IN R ==> (x * (y + z) = x * y + x * z)
   field_def_by_inv  |- !r. Field r <=>
                            Ring r /\ #1 <> #0 /\ !x. x IN R /\ x <> #0 ==> ?y. y IN R /\ (x * y = #1)


   A Ring can be a Field if the Units group is large enough:
   field_units_def       |- !r. field_units r = <|carrier := R; sum := r.sum; prod := r* including #0|>
   field_units_is_field  |- !r. Ring r /\ (R* = R+ ) /\ #0 <> #1 ==> Field (field_units r)
   field_units_nonzero   |- !r. Field r ==> (R* = R+)
   field_units_eq        |- !r. Field r ==> (R* = F* )
   field_unit_has_inv    |- !r. Field r ==> !x. unit x ==> unit ( |/ x)
   field_uroots_is_group |- !r. Field r ==> !n. Group (roots_of_unity f* n)

   Field Characteristic:
   field_char            |- !r. Field r ==> (char r = 0) \/ prime (char r)
   field_char_prime      |- !r. Field r /\ 0 < char r ==> prime (char r)
   field_char_0          |- !r. Field r /\ (char r = 0) ==> INFINITE R
   field_char_ne_1       |- !r. Field r ==> char r <> 1
   field_neg_char_2      |- !r. Field r /\ (char r = 2) ==> !x. x IN R ==> (-x = x)
   field_char_alt        |- !r. Field r ==> !n. 0 < n ==>
                                ((char r = n) <=> (##n = #0) /\ !m. 0 < m /\ m < n ==> ##m <> #0)
   field_char_eqn        |- !r. Field r /\ 0 < char r ==> (##(char r) = #0) /\ !n. 0 < n /\ n < char r ==> ##n <> #0
   field_neg_one_eq_one  |- !r. Field r ==> ((-#1 = #1) <=> (char r = 2))
   field_add_exp_eqn     |- !r. Field r ==> !x. x IN R ==> !n. r.sum.exp x n = x * ##n
   field_add_order       |- !r. Field r /\ 0 < char  ==> !x. x IN R+ ==> (order r.sum x = char r)
   field_num_eq          |- !r. Field r ==> !n m. n < char r /\ m < char r ==> ((##n = ##m) <=> (n = m))
   field_num_mod         |- !r. Field r /\ 0 < char r ==> !n. ##n = ##(n MOD char r)
   field_num_negative    |- !r. Field r /\ 0 < char r ==> !z. ?y x. (y = ##x) /\ (y + ##z = #0)
   field_num_inverse     |- !r. Field r /\ 0 < char r ==> !z. ##z <> #0 ==> ?y x. (y = ##x) /\ y <> #0 /\ (y * ##z = #1)

   Finite Field:
   finite_field_char       |- !r. FiniteField r ==> prime (char r)
   finite_field_char_pos   |- !r. FiniteField r ==> 0 < char r
   finite_field_char_gt_1  |- !r. FiniteField r ==> 1 < char r
   finite_field_card_gt_1  |- !r. FiniteField r ==> 1 < CARD R
   finite_field_card_pos   |- !r. FiniteField r ==> 0 < CARD R
   finite_field_card_prime |- !r. FiniteField r /\ prime (CARD R) ==> (char r = CARD R)

   Properties from Finite Group:
   finite_field_Fermat        |- !r. FiniteField r ==> !x. x IN R+ ==> (x ** CARD R+ = #1)
   finite_field_carrier_card  |- !r. FiniteField r ==> (CARD R = SUC (CARD R+))
   finite_field_nonzero_carrier_card  |- !r. FiniteField r ==> (CARD R+ = CARD R - 1)
   finite_field_carrier_parity        |- !r. FiniteField r ==> (EVEN (CARD R) ==> ODD (CARD R+)) /\
                                                               (ODD (CARD R) ==> EVEN (CARD R+))
   finite_field_fermat_thm    |- !r. FiniteField r ==> !x. x IN R ==> (x ** CARD R = x)
   finite_field_fermat_all    |- !r. FiniteField r ==> !x. x IN R ==> !n. x ** CARD R ** n = x
   finite_field_exp_mod       |- !r. FiniteField r ==> !x. x IN R+ ==> !n. x ** n = x ** (n MOD CARD R+)

   Field Subgroup:
   field_subgroup_property       |- !r g. Field r /\ g <= f* ==>
                                          (#e = #1) /\ (g.op = $* ) /\ (!x n. x IN G ==> (g.exp x n = x ** n)) /\
                                          G SUBSET R+ /\ #1 IN G /\ #0 NOTIN G
   field_subgroup_element        |- !r g. Field r /\ g <= f* ==> !x. x IN G ==> x IN R /\ x <> #0
   field_subgroup_id             |- !r g. Field r /\ g <= f* ==> (#e = #1)
   field_subgroup_exp            |- !r g. Field r /\ g <= f* ==> !x n. x IN G ==> (g.exp x n = x ** n)
   field_subgroup_inv            |- !r g. Field r /\ g <= f* ==> !x. x IN G ==> (g.inv x = |/ x)
   field_subgroup_finite_group   |- !r g. FiniteField r /\ g <= f* ==> FiniteGroup g
   field_subgroup_card           |- !r g. FiniteField r /\ g <= f* ==> (CARD (G UNION {#0}) = CARD G + 1)
*)
(* ------------------------------------------------------------------------- *)
(* The basic definitions                                                     *)
(* ------------------------------------------------------------------------- *)

(* A field is represented by a ring. *)
val _ = type_abbrev ("field", Type `:'a ring`);
(* Field and Ring share the same type. *)

(* ------------------------------------------------------------------------- *)
(* To define a Field.                                                        *)
(* ------------------------------------------------------------------------- *)

(* Field Definition:
   A Field is a set with elements of r of type 'a field, such that
   . it is a Ring
   . r.prod excluding #0 is a Group
*)
val Field_def = Define`
  Field (r:'a field) <=> Ring r /\ Group f*
`;



val FiniteField_def = Define`
  FiniteField (r:'a field) <=> Field r /\ FINITE R
`;

(* ------------------------------------------------------------------------- *)
(* Field theorems from Definition.                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: A Field is a Ring. *)
(* Proof: by definitions. *)
val field_is_ring = save_thm("field_is_ring",
  Field_def |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val field_is_ring = |- !r:'a field. Field r ==> Ring r : thm *)

val _ = export_rewrites ["field_is_ring"];

(* Theorem: FiniteField r is a Field r. *)
(* Proof: by definition. *)
val finite_field_is_field = save_thm("finite_field_is_field", FiniteField_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> GEN_ALL);
(* > val finite_field_is_field = |- !r. FiniteField r ==> Field r /\ FINITE R : thm *)

(* Theorem: FiniteField r ==> FiniteRing r *)
(* Proof: by FiniteField_def, FiniteRing_def, field_is_ring *)
val finite_field_is_finite_ring = store_thm(
  "finite_field_is_finite_ring",
  ``!r:'a field. FiniteField r ==> FiniteRing r``,
  rw[FiniteField_def, FiniteRing_def]);

(* Theorem: r.sum.carrier = R /\ r.prod.carrier = R *)
(* Proof: by definitions. *)
val field_carriers = store_thm(
  "field_carriers",
  ``!r:'a field. Field r ==> (r.sum.carrier = R) /\ (r.prod.carrier = R)``,
  rw_tac std_ss[Field_def, Ring_def]);

val _ = export_rewrites ["field_carriers"];

(* Theorem: Field r ==> F* = R+ *)
(* Proof: by ring_nonzero_mult_carrier, field_is_ring *)
val field_mult_carrier = store_thm(
  "field_mult_carrier",
  ``!r:'a field. Field r ==> (F* = R+ )``,
  rw_tac std_ss[ring_nonzero_mult_carrier, field_is_ring]);

(* Theorem: FiniteField r ==> FiniteRing r /\ FiniteGroup f* *)
(* Proof:
   By FiniteField_def, FiniteRing_def, FiniteGroup_def, Field_def, this is to show:
   FINITE R ==> FINITE F*
   which is true by field_carriers, excluding_def.
*)
val finite_field_alt = store_thm(
  "finite_field_alt",
  ``!r:'a field. FiniteField r <=> FiniteRing r /\ FiniteGroup f*``,
  rw[FiniteField_def, FiniteRing_def, FiniteGroup_def, Field_def, EQ_IMP_THM] >>
  rw[field_carriers, excluding_def]);

(* Theorem: Field r ==> R <> {} *)
(* Proof: by field_is_ring, ring_carrier_nonempty *)
val field_carrier_nonempty = store_thm(
  "field_carrier_nonempty",
  ``!r:'a field. Field r ==> R <> {}``,
  rw_tac std_ss[field_is_ring, ring_carrier_nonempty]);

(* ------------------------------------------------------------------------- *)
(* Lifting Theorems from Ring                                                *)
(* ------------------------------------------------------------------------- *)


(*
- show_assums := true;
> val it = () : unit
- ring_zero_element;
> val it =  [] |- !r. Ring r ==> #0 IN R : thm
- ring_zero_element |> SPEC_ALL;
> val it =  [] |- Ring r ==> #0 IN R : thm
- ring_zero_element |> SPEC_ALL |> UNDISCH;
> val it =  [Ring r] |- #0 IN R : thm
- ring_zero_element |> SPEC_ALL |> UNDISCH |> PROVE_HYP (field_is_ring |> SPEC_ALL |> UNDISCH);
> val it =  [Field r] |- #0 IN R : thm
- ring_zero_element |> SPEC_ALL |> UNDISCH |> PROVE_HYP (field_is_ring |> SPEC_ALL |> UNDISCH) |> DISCH_ALL |> GEN_ALL;
> val it =  [] |- !r:'a field. Field r ==> #0 IN R : thm
- show_assums := false;
> val it = () : unit
*)

(* Lifting Ring theorem for Field
   from: !r: 'a ring. Ring r ==> E(r)
     to: !r:'a field. Field r ==> E(f)
    via: !r:'a field. Field r ==> Ring r
*)
local
val fir = field_is_ring |> SPEC_ALL |> UNDISCH
in
fun lift_ring_thm suffix = let
   val th1 = DB.fetch "ring" ("ring_" ^ suffix)
   val th2 = th1 |> SPEC_ALL |> UNDISCH |> PROVE_HYP fir |> DISCH_ALL |> GEN_ALL
(* val th2 = fir |> MP (th1 |> SPEC_ALL) |> DISCH_ALL |> GEN_ALL *)
in
   save_thm("field_" ^ suffix, th2)
end
end; (* local *)

(* ------------------------------------------------------------------------- *)
(* Simple Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field additions form an Abelian group *)
val field_add_group = lift_ring_thm "add_group";
(* > val field_add_group = |- !r:'a field. Field r ==> Group r.sum /\ (r.sum.carrier = R) /\
                                              !x y. x IN R /\ y IN R ==> (x + y = y + x) : thm *)

(* Theorem: Field multiplications form an Abelian monoid *)
val field_mult_monoid = lift_ring_thm "mult_monoid";
(* > val field_mult_monoid = |- !r:'a field. Field r ==> Monoid r.prod /\ (r.prod.carrier = R) /\
                                                !x y. x IN R /\ y IN R ==> (x * y = y * x) : thm *)

(* ------------------------------------------------------------------------- *)
(* Properties of #0 and #1 - representations of zero and one in field.       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: #0 in carrier. *)
val field_zero_element = lift_ring_thm "zero_element";
(* > val field_zero_element = |- !r:'a field. Field r ==> #0 IN R : thm *)

(* Theorem: #1 in carrier. *)
val field_one_element = lift_ring_thm "one_element";
(* > val field_one_element = |- !r:'a field. Field r ==> #1 IN R : thm *)

(*
val _ = export_rewrites ["field_zero_element", "field_one_element"];
*)
(* ------------------------------------------------------------------------- *)
(* Field Adddition Theorems (from Ring, by field_add_group)                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field addition in carrier. *)
val field_add_element = lift_ring_thm "add_element";
(* > val field_add_element = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> x + y IN R : thm *)

(* Theorem: Field addition is associative. *)
val field_add_assoc = lift_ring_thm "add_assoc";
(* > val field_add_assoc = |- !r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x + y + z = x + (y + z)) : thm *)

(* Theorem: Field addition is commutative *)
val field_add_comm = lift_ring_thm "add_comm";
(* > val field_add_comm = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> (x + y = y + x) : thm *)

(* Theorem: Field addition is associate-commutative. *)
val field_add_assoc_comm = lift_ring_thm "add_assoc_comm";
(* > val field_add_assoc_comm = |- !r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x + (y + z) = y + (x + z)) : thm *)

(* Theorem: #0 + #0 = #0 *)
val field_add_zero_zero = lift_ring_thm "add_zero_zero";
(* > val field_add_zero_zero = |- !r:'a field. Field r ==> (#0 + #0 = #0) : thm *)

(* Theorem: #0 + x = x. *)
val field_add_lzero = lift_ring_thm "add_lzero";
(* > val field_add_lzero = |- !r:'a field. Field r ==> !x. x IN R ==> (#0 + x = x) : thm *)

(* Theorem: x + #0 = x. *)
val field_add_rzero = lift_ring_thm "add_rzero";
(* > val field_add_rzero = |- !r:'a field. Field r ==> !x. x IN R ==> (x + #0 = x) : thm *)

(* Theorem: #0 is unique. *)
val field_zero_unique = lift_ring_thm "zero_unique";
(* > val field_zero_unique = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==>
                                ((y + x = x) <=> (y = #0)) /\ ((x + y = x) <=> (y = #0)) : thm *)

(* ------------------------------------------------------------------------- *)
(* Field Multiplication Theorems (from Ring)                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: x * y in carrier *)
val field_mult_element = lift_ring_thm "mult_element";
(* > val field_mult_element = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> x * y IN R : thm *)

(* Theorem: (x * y) * z = x * (y * z) *)
val field_mult_assoc = lift_ring_thm "mult_assoc";
(* > val field_mult_assoc = |- !r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x * y * z = x * (y * z)) : thm *)

(* Theorem: x * y = y * x *)
val field_mult_comm = lift_ring_thm "mult_comm";
(* > val field_mult_comm = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> (x * y = y * x) : thm *)

(* Theorem: x * (y * z) = y * (x * z) *)
val field_mult_assoc_comm = lift_ring_thm "mult_assoc_comm";
(* > val field_mult_assoc_comm = |- !r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x * (y * z) = y * (x * z)) : thm *)

(* Theorem: x * #0 = #0 *)
val field_mult_rzero = lift_ring_thm "mult_rzero";
(* > val field_mult_rzero = |- !r:'a field. Field r ==> !x. x IN R ==> (x * #0 = #0) : thm *)

(* Theorem: #0 * x = #0 *)
val field_mult_lzero = lift_ring_thm "mult_lzero";
(* > val field_mult_lzero = |- !r:'a field. Field r ==> !x. x IN R ==> (#0 * x = #0) : thm *)

(* Theorem: #0 * #0 = #0 *)
val field_mult_zero_zero = lift_ring_thm "mult_zero_zero";
(* > val field_mult_zero_zero = |- !r:'a field. Field r ==> (#0 * #0 = #0) : thm *)

(* Theorem: #1 * #1 = #1 *)
val field_mult_one_one = lift_ring_thm "mult_one_one";
(* > val field_mult_one_one = |- !r:'a field. Field r ==> (#1 * #1 = #1) : thm *)

(* Theorem: #1 * x = x *)
val field_mult_lone = lift_ring_thm "mult_lone";
(* > val field_mult_lone = |- !r:'a field. Field r ==> !x. x IN R ==> (#1 * x = x) : thm *)

(* Theorem: x * #1 = x *)
val field_mult_rone = lift_ring_thm "mult_rone";
(* > val field_mult_rone = |- !r:'a field. Field r ==> !x. x IN R ==> (x * #1 = x) : thm *)

(* ring_one_unique to be improved to field_one_unique later.      *)
(* ring_one_eq_zero will be used later to show #1 <> #0 in Field. *)

(* ------------------------------------------------------------------------- *)
(* Field Numerical Theorems (from Ring)                                      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Theorems from Ring.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ##0 is #0. *)
val field_num_0 = save_thm("field_num_0", ring_num_0); (* theorem alias *)
(* > val field_num_0 = |- !r:'a field. ##0 = #0 : thm *)

(* Theorem: ##1 is #1. *)
val field_num_1 = lift_ring_thm "num_1";
(* > val field_num_1 = |- !r:'a field. Field r ==> (##1 = #1) : thm *)

(* Theorem: ##n IN R *)
val field_num_element = lift_ring_thm "num_element";
(* > val field_num_element = |- !r:'a field. Field r ==> !n. ##n IN R : thm *)

(* Theorem: ##n * x IN R *)
val field_num_mult_element = lift_ring_thm "num_mult_element";
(* > val field_num_mult_element = |- !r:'a field. Field r ==> !x. x IN R ==> !n. ##n * x IN R : thm *)

(* Theorem: ##(SUC n) = #1 + ##n *)
val field_num_SUC = lift_ring_thm "num_SUC";
(* > val field_num_SUC = |- !r n. Field r ==> (##(SUC n) = #1 + ##n) : thm *)

(* Theorem: ##(SUC n) = ##n + #1 *)
val field_num_suc = lift_ring_thm "num_suc";
(* > val field_num_suc = |- !r:'a field. Field r ==> !n. ##(SUC n) = ##n + #1 : thm *)

(* ------------------------------------------------------------------------- *)
(* Field Exponent Theorems (from Ring)                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: x ** n IN R *)
val field_exp_element = lift_ring_thm "exp_element";
(* > val field_exp_element = |- !r:'a field. Field r ==> !x. x IN R ==> !n. x ** n IN R : thm *)

(* Theorem: x ** 0 = #1 *)
(* Proof: by group_exp_0 *)
val field_exp_0 = store_thm(
  "field_exp_0",
  ``!x:'a. x ** 0 = #1``,
  rw[]);
(* The following is no longer valid, as ring_exp_0 has no Ring r ==> ... *)
(* val field_exp_0 = lift_ring_thm "exp_0"; *)
(* > val field_exp_0 = |- !x. x ** 0 = #1: thm *)

(* Theorem: x ** (SUC n) = x * x ** n *)
(* Proof: by group_exp_SUC *)
val field_exp_SUC = store_thm(
  "field_exp_SUC",
  ``!x n. x ** (SUC n) = x * x ** n``,
  rw[]);
(* The following is no longer valid, as ring_exp_0 has no Ring r ==> ... *)
(* val field_exp_SUC = lift_ring_thm "exp_SUC"; *)
(* > val field_exp_SUC = |- !x n. x ** SUC n = x * x ** n *)

(* Theorem: x ** SUC n = x ** n * x *)
val field_exp_suc = lift_ring_thm "exp_suc";
(* > val field_exp_suc = |- !r:'a field. Field r ==> !x. x IN R ==> !n. x ** SUC n = x ** n * x : thm *)

(* Theorem: x ** 1 = x *)
val field_exp_1 = lift_ring_thm "exp_1";
(* > val field_exp_1 = |- !r:'a field. Field r ==> !x. x IN R ==> (x ** 1 = x) : thm *)

(* Theorem: x ** n * x = x * x ** n *)
val field_exp_comm = lift_ring_thm "exp_comm";
(* > val field_exp_comm = |- !r. Field r ==> !x. x IN R ==> !n. x ** n * x = x * x ** n: thm *)

(* Theorem: (x * y) ** n = x ** n * y ** n *)
val field_mult_exp = lift_ring_thm "mult_exp";
(* > val field_mult_exp = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> !n. (x * y) ** n = x ** n * y ** n : thm *)

(* Theorem: computation of small values of field_exp *)
val field_exp_small = lift_ring_thm "exp_small";
(* > val field_exp_small = |- !r:'a field. Field r ==> !x. x IN R ==>
           (x ** 0 = #1) /\ (x ** 1 = x) /\ (x ** 2 = x * x) /\
           (x ** 3 = x * x ** 2) /\ (x ** 4 = x * x ** 3) /\
           (x ** 5 = x * x ** 4) /\ (x ** 6 = x * x ** 5) /\
           (x ** 7 = x * x ** 6) /\ (x ** 8 = x * x ** 7) /\
           (x ** 9 = x * x ** 8) : thm *)

(*
val _ = export_rewrites ["field_exp_element"];
val _ = export_rewrites ["field_exp_0", "field_exp_SUC"];
val _ = export_rewrites ["field_exp_1"];
*)
(* ------------------------------------------------------------------------- *)
(* Field Distribution Theorems (from Ring)                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: x * (y + z) = x * y + x * z *)
val field_mult_radd = lift_ring_thm "mult_radd";
(*  val field_mult_radd = |- !r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x * (y + z) = x * y + x * z) : thm *)

(* Theorem: (y + z) * x = y * x + z * x *)
val field_mult_ladd = lift_ring_thm "mult_ladd";
(* > val field_mult_ladd = |- !r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((y + z) * x = y * x + z * x) : thm *)

(* Theorem: x * (y + z) = x * y + x * z /\ (y + z) * x = y * x + z * x *)
val field_mult_add = lift_ring_thm "mult_add";
(* > val field_mult_add = |- !r:'a field. Field r ==> !z y x. x IN R /\ y IN R /\ z IN R ==>
                                             (x * (y + z) = x * y + x * z) /\ ((y + z) * x = y * x + z * x) : thm *)

(* Theorem: ##(SUC n) * x = ##n * x + x *)
val field_num_mult_suc = lift_ring_thm "num_mult_suc";
(* > val field_num_mult_suc = |- !r:'a field. Field r ==> !x. x IN R ==> !n. ##(SUC n) * x = ##n * x + x : thm *)

(* Theorem: computation of small values of field multiplication with ##n. *)
val field_num_mult_small = lift_ring_thm "num_mult_small";
(* > val field_num_mult_small = |- !r:'a field. Field r ==> !x. x IN R ==>
           (#0 * x = #0) /\ (#1 * x = x) /\ (##2 * x = x + x) /\ (##3 * x = ##2 * x + x) : thm *)

(* val _ = export_rewrites ["field_mult_radd", "field_mult_ladd"]; *)

(* ------------------------------------------------------------------------- *)
(* Field Negation Theorems (from Ring)                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field negatives in carrier. *)
val field_neg_element = lift_ring_thm "neg_element";
(* > val field_neg_element = |- !r:'a field. Field r ==> !x. x IN R ==> -x IN R : thm *)

(* Theorem: - #0 = #0 *)
val field_neg_zero = lift_ring_thm "neg_zero";
(* > val field_neg_zero = |- !r:'a field. Field r ==> (-#0 = #0) : thm *)

(* Theorem: (-x) + x = #0 *)
val field_add_lneg = lift_ring_thm "add_lneg";
(* > val field_add_lneg = |- !r:'a field. Field r ==> !x. x IN R ==> (-x + x = #0) : thm *)

(* Theorem: (-x) + (x + y) = y *)
val field_add_lneg_assoc = lift_ring_thm "add_lneg_assoc";
(* > val field_add_lneg_assoc = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> (y = x + (-x + y)) /\ (y = -x + (x + y)) : thm *)

(* Theorem: x + (-x) = #0 *)
val field_add_rneg = lift_ring_thm "add_rneg";
(* > val field_add_rneg = |- !r:'a field. Field r ==> !x. x IN R ==> (x + -x = #0) : thm *)

(* Theorem: x + ((-x) + y) = y *)
val field_add_rneg_assoc = lift_ring_thm "add_rneg_assoc";
(* > val field_add_rneg_assoc = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> (y = y + -x + x) /\ (y = y + x + -x) : thm *)

(* Theorem: Field addition has left-cancellation. *)
val field_add_lcancel = lift_ring_thm "add_lcancel";
(* > val field_add_lcancel = |- !r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((x + y = x + z) <=> (y = z)) : thm *)

(* Theorem: Field addition has right-cancellation. *)
val field_add_rcancel = lift_ring_thm "add_rcancel";
(* > val field_add_rcancel = |- !r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((y + x = z + x) <=> (y = z)) : thm *)

(* Theorem: z = z + z <=> z = #0 *)
val field_zero_fix = lift_ring_thm "zero_fix";
(* > val field_zero_fix = |- !r:'a field. Field r ==> !x. x IN R ==> ((x + x = x) <=> (x = #0)) : thm *)

(* Theorem: - (- x) = x *)
val field_neg_neg = lift_ring_thm "neg_neg";
(* > val field_neg_neg = |- !r:'a field. Field r ==> !x. x IN R ==> (--x = x) : thm *)

(* Theorem: -x = #0 <=> x = #0 *)
val field_neg_eq_zero = lift_ring_thm "neg_eq_zero";
(* > val field_neg_eq_zero = |- !r:'a field. Field r ==> !x. x IN R ==> ((-x = #0) <=> (x = #0)) : thm *)

(* Theorem: - x = - y <=> x = y *)
val field_neg_eq = lift_ring_thm "neg_eq";
(* > val field_neg_eq = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> ((-x = -y) <=> (x = y)) : thm *)

(* Theorem: -x = y <=> x = - y *)
val field_neg_eq_swap = lift_ring_thm "neg_eq_swap";
(* > val field_neg_eq_swap = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> ((-x = y) <=> (x = -y)) : thm *)

(* Theorem: x + y = #0 <=> y = -x *)
val field_add_eq_zero = lift_ring_thm "add_eq_zero";
(* > val field_add_eq_zero = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> ((x + y = #0) <=> (y = -x)) : thm *)

(* Theorem: - (x + y) = -y + -x *)
val field_neg_add_comm = lift_ring_thm "neg_add_comm";
(* > val field_neg_add_comm = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> (-(x + y) = -y + -x) : thm *)

(* Theorem: For field, - (x + y) = -x + -y *)
val field_neg_add = lift_ring_thm "neg_add";
(* > val field_neg_add = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> (-(x + y) = -x + -y) : thm *)

(*
val _ = export_rewrites ["field_neg_element"];
val _ = export_rewrites ["field_neg_zero"];
val _ = export_rewrites ["field_add_lneg", "field_add_rneg"];
val _ = export_rewrites ["field_neg_neg"];
*)
(* ------------------------------------------------------------------------- *)
(* Field Distribution Theorems with Negation (from Ring).                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: -x * y = - (x * y) *)
val field_mult_lneg = lift_ring_thm "mult_lneg";
(* > val field_mult_lneg = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> (-x * y = -(x * y)) : thm *)

(* Theorem: x * - y = - (x * y) *)
val field_mult_rneg = lift_ring_thm "mult_rneg";
(* > val field_mult_rneg = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> (x * -y = -(x * y)) : thm *)

(* Theorem: -(x * y) = -x * y  and -(x * y) = x * -y *)
val field_neg_mult = lift_ring_thm "neg_mult";
(* > val field_neg_mult = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> (-(x * y) = -x * y) /\ (-(x * y) = x * -y) : thm *)

(* Theorem: - x * - y = x * y *)
val field_mult_neg_neg = lift_ring_thm "mult_neg_neg";
(* > val field_mult_neg_neg = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> (-x * -y = x * y) : thm *)

(*
val _ = export_rewrites ["field_mult_lneg", "field_mult_rneg"];
val _ = export_rewrites ["field_neg_mult", "field_mult_neg_neg" ];
*)
(* ------------------------------------------------------------------------- *)
(* More Field Numeral Theorems (from Ring)                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ##(n + k) = ##n + ##k *)
val field_num_add = lift_ring_thm "num_add";
(* > val field_num_add = |- !r:'a field. Field r ==> !n k. ##(n + k) = ##n + ##k : thm *)

(* Theorem: ##m + (##n + x) = ##(m+n) + x *)
val field_num_add_assoc = lift_ring_thm "num_add_assoc";
(* > val field_num_add_assoc = |- !r:'a field. Field r ==> !x. x IN R ==> !m n. ##m + (##n + x) = ##(m + n) + x : thm *)

(* Theorem: ##m * ##n = ##(m * n) *)
val field_num_mult = lift_ring_thm "num_mult";
(* > val field_num_mult = |- !r:'a field. Field r ==> !m n. ##m * ##n = ##(m * n) : thm *)

(* Theorem: ##m * (##n * x) = ##(m * n) * x *)
val field_num_mult_assoc = lift_ring_thm "num_mult_assoc";
(* > val field_num_mult_assoc = |- !r:'a field. Field r ==> !m n (x::R). ##m * (##n * x) = ##(m * n) * x : thm *)

(* Theorem: ##m ** n = ##(m ** n) *)
val field_num_exp = lift_ring_thm "num_exp";
(* > val field_num_exp = |- !r:'a field. Field r ==> !m n. ##m ** n = ##(m ** n) : thm *)

(* Theorem: ##(m + n) * x = ##m * x + ##n * x *)
val field_num_add_mult = lift_ring_thm "num_add_mult";
(* > val field_num_add_mult = |- !r:'a field. Field r ==> !x. x IN R ==> !m n. ##(m + n) * x = ##m * x + ##n * x : thm *)

(* Theorem: ##(m + n) * x + y = ##m * x + (##n * x + y) *)
val field_num_add_mult_assoc = lift_ring_thm "num_add_mult_assoc";
(* > val field_num_add_mult_assoc = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==>
                                                       !m n. ##(m + n) * x + y = ##m * x + (##n * x + y) : thm *)

(* Theorem: - (##n * x) = ##n * (- x) *)
val field_num_mult_neg = lift_ring_thm "num_mult_neg";
(* > val field_num_mult_neg = |- !r:'a field. Field r ==> !x. x IN R ==> !n. -(##n * x) = ##n * -x : thm *)

(* Theorem:  ##n * (x + y) = ##n * x + ##n * y *)
val field_num_mult_radd = lift_ring_thm "num_mult_radd";
(* > val field_num_mult_radd = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> !n. ##n * (x + y) = ##n * x + ##n * y : thm *)

(* Theorem: x + x = ##2 * x *)
val field_single_add_single = lift_ring_thm "single_add_single";
(* > val field_single_add_single = |- !r:'a field. Field r ==> !x. x IN R ==> (x + x = ##2 * x) : thm *)

(* Theorem: x + (x + y) = ##2 * x y *)
val field_single_add_single_assoc = lift_ring_thm "single_add_single_assoc";
(* > val field_single_add_single_assoc = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> (x + (x + y) = ##2 * x + y) : thm *)

(* Theorem: x + ##n * x = ##(n+1) * x *)
val field_single_add_mult = lift_ring_thm "single_add_mult";
(* > val field_single_add_mult = |- !r:'a field. Field r ==> !x. x IN R ==> !n. x + ##n * x = ##(n + 1) * x : thm *)

(* Theorem: x + (##n * x + y) = ##(n+1) * x + y *)
val field_single_add_mult_assoc = lift_ring_thm "single_add_mult_assoc";
(* > val field_single_add_mult_assoc = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==>
                                                          !n. x + (##n * x + y) = ##(n + 1) * x + y : thm *)

(* Theorem: x + - ##n * x = n = 0 ? x : - ##(n-1) * x *)
val field_single_add_neg_mult = lift_ring_thm "single_add_neg_mult";
(* > val field_single_add_neg_mult = |- !r:'a field. Field r ==> !x. x IN R ==>
                                                        !n. x + -(##n * x) = if n = 0 then x else -(##(n - 1) * x) : thm *)

(* Theorem: x + (- ##n * x + y) = n = 0 ? x + y : - ##(n-1) * x + y  *)
val field_single_add_neg_mult_assoc = lift_ring_thm "single_add_neg_mult_assoc";
(* > val field_single_add_neg_mult_assoc = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==>
           !n. x + (-(##n * x) + y) = if n = 0 then x + y else -(##(n - 1) * x) + y : thm *)

(* Theorem: ##n * x + - x = if n = 0 then - x else ##(n - 1) * x *)
val field_mult_add_neg = lift_ring_thm "mult_add_neg";
(* > val field_mult_add_neg = |- !r:'a field. Field r ==> !x. x IN R ==>
           !n. ##n * x + -x = if n = 0 then -x else ##(n - 1) * x : thm *)

(* Theorem: ##n * x + (- x + y) = if n = 0 then - x + y else ##(n - 1) * x + y *)
val field_mult_add_neg_assoc = lift_ring_thm "mult_add_neg_assoc";
(* > val field_mult_add_neg_assoc = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==>
           !n. ##n * x + (-x + y) = if n = 0 then -x + y else ##(n - 1) * x + y : thm *)

(* Theorem: ##m * x + - (##n * x) = if m < n then - (##(n - m) * x) else ##(m - n) * x *)
val field_mult_add_neg_mult = lift_ring_thm "mult_add_neg_mult";
(* > val field_mult_add_neg_mult = |- !r:'a field. Field r ==> !x. x IN R ==>
           !m n. ##m * x + -(##n * x) = if m < n then -(##(n - m) * x) else ##(m - n) * x : thm *)

(* Theorem: ##m * x + (- (##n * x) + y) = if m < n then - (##(n - m) * x) + y else ##(m - n) * x + y *)
val field_mult_add_neg_mult_assoc = lift_ring_thm "mult_add_neg_mult_assoc";
(* > val field_mult_add_neg_mult_assoc = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==>
           !m n. ##m * x + (-(##n * x) + y) = if m < n then -(##(n - m) * x) + y else ##(m - n) * x + y : thm *)

(* Theorem: - x + - x = - (##2 * x) *)
val field_neg_add_neg = lift_ring_thm "neg_add_neg";
(* > val field_neg_add_neg = |- !r:'a field. Field r ==> !x. x IN R ==> (-x + -x = -(##2 * x)) : thm *)

(* Theorem: - x + (- x + y) = - (##2 * x) + y *)
val field_neg_add_neg_assoc = lift_ring_thm "neg_add_neg_assoc";
(* > val field_neg_add_neg_assoc = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> (-x + (-x + y) = -(##2 * x) + y) : thm *)

(* Theorem:  - x + - (##n * x) = - (##(n + 1) * x) *)
val field_neg_add_neg_mult = lift_ring_thm "neg_add_neg_mult";
(* > val field_neg_add_neg_mult = |- !r:'a field. Field r ==> !x. x IN R ==> !n. -x + -(##n * x) = -(##(n + 1) * x) : thm *)

(* Theorem: - x + (- (##n * x) + y) = - (##(n + 1) * x) + y *)
val field_neg_add_neg_mult_assoc = lift_ring_thm "neg_add_neg_mult_assoc";
(* > val field_neg_add_neg_mult_assoc = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==>
           !n. -x + (-(##n * x) + y) = -(##(n + 1) * x) + y : thm *)

(* Theorem: - (##m * x) + - (##n * x) = - (##(m + n) * x) *)
val field_neg_mult_add_neg_mult = lift_ring_thm "neg_mult_add_neg_mult";
(* > val field_neg_mult_add_neg_mult = |- !r:'a field. Field r ==> !x. x IN R ==> !m n. -(##m * x) + -(##n * x) = -(##(m + n) * x) : thm *)

(* Theorem: - (##m * x) + (- (##n * x) + y) = - (##(m + n) * x) + y *)
val field_neg_mult_add_neg_mult_assoc = lift_ring_thm "neg_mult_add_neg_mult_assoc";
(* > val field_neg_mult_add_neg_mult_assoc = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==>
           !m n. -(##m * x) + (-(##n * x) + y) = -(##(m + n) * x) + y : thm *)

(* ------------------------------------------------------------------------- *)
(* More Field Exponent Theorems (from Ring)                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: x * x = x ** 2 *)
val field_single_mult_single = lift_ring_thm "single_mult_single";
(* > val field_single_mult_single = |- !r:'a field. Field r ==> !x. x IN R ==> (x * x = x ** 2) : thm *)

(* Theorem: x * (x * y) = x ** 2 * y *)
val field_single_mult_single_assoc = lift_ring_thm "single_mult_single_assoc";
(* > val field_single_mult_single_assoc = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> (x * (x * y) = x ** 2 * y) : thm *)

(* Theorem: x * x ** n = x ** (n + 1) *)
val field_single_mult_exp = lift_ring_thm "single_mult_exp";
(* > val field_single_mult_exp = |- !r:'a field. Field r ==> !x. x IN R ==> !n. x * x ** n = x ** (n + 1) : thm *)

(* Theorem: x * (x ** n * y) = x ** (n + 1) * y *)
val field_single_mult_exp_assoc = lift_ring_thm "single_mult_exp_assoc";
(* > val field_single_mult_exp_assoc = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==>
                                          !n. x * (x ** n * y) = x ** (n + 1) * y : thm *)

(* Theorem: x ** (n + k) = x ** n * x ** k *)
val field_exp_add = lift_ring_thm "exp_add";
(* > val field_exp_add = |- !r:'a field. Field r ==> !x. x IN R ==> !n k. x ** (n + k) = x ** n * x ** k : thm *)

(* Theorem: x ** m * (x ** n * y) = x ** (m + n) * y *)
val field_exp_add_assoc = lift_ring_thm "exp_add_assoc";
(* > val field_exp_add_assoc = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==>
                                                  !n k. x ** n * (x ** k * y) = x ** (n + k) * y : thm *)

(* Theorem: #1 ** n = #1 *)
val field_one_exp = lift_ring_thm "one_exp";
(* > val field_one_exp = |- !r:'a field. Field r ==> !n. #1 ** n = #1 : thm *)

(* Theorem: #0 ** n = if n = 0 then #1 else #0 *)
val field_zero_exp = lift_ring_thm "zero_exp";
(* > val field_zero_exp = |- !r:'a field. Field r ==> !n. #0 ** n = if n = 0 then #1 else #0 : thm *)

(* Theorem: x ** (n * k) = (x ** n) ** k *)
val field_exp_mult = lift_ring_thm "exp_mult";
(* > val field_exp_mult = |- !r:'a field. Field r ==> !x. x IN R ==> !n k. x ** (n * k) = (x ** n) ** k : thm *)

(* Theorem: (x ** m) ** n = (x ** n) ** m *)
val field_exp_mult_comm = lift_ring_thm "exp_mult_comm";
(* > val field_exp_mult_comm = |- !r. Field r ==> !x. x IN R ==> !m n. (x ** m) ** n = (x ** n) ** m: thm *)

(* Theorem: (-x) ** 2 = x ** 2 *)
val field_neg_square = lift_ring_thm "neg_square";
(* > val field_neg_square = |- !r. Field r ==> !x. x IN R ==> (-x ** 2 = x ** 2) : thm *)

(* Theorem: - x ** n = if EVEN n then x ** n else - (x ** n) *)
val field_exp_neg = lift_ring_thm "exp_neg";
(* > val field_exp_neg = |- !r. Field r ==> !x. x IN R ==> !n. -x ** n = if EVEN n then x ** n else -(x ** n) : thm *)

(* Theorem: - x ** n = if EVEN n then x ** n else - (x ** n) *)
val field_neg_exp = lift_ring_thm "neg_exp";
(* > val field_neg_exp = |- !r. Field r ==> !x. x IN R ==> !n. -x ** n = if EVEN n then x ** n else -(x ** n): thm *)

(* Theorem: ##k * ##m ** n = ##(k * m ** n) *)
val field_num_mult_exp = lift_ring_thm "num_mult_exp";
(* > val field_num_mult_exp = |- !r. Field r ==> !k m n. ##k * ##m ** n = ##(k * m ** n): thm *)

(* This works, but field will use forder x = order (r.prod excluding #0) x
   rather than order r.prod x.
val field_exp_mod_order = lift_ring_thm "exp_mod_order";
 > val field_exp_mod_order = |- !r. Field r ==>
     !x. x IN R /\ 0 < order r.prod x ==> !n. x ** n = x ** (n MOD order r.prod x): thm

There is a better field_exp_mod_order below.
*)

(* ------------------------------------------------------------------------- *)
(* Field Subtraction Theorems (from Ring)                                    *)
(* ------------------------------------------------------------------------- *)

(* Define field_sub r as ring_sub r *)
val field_sub_def = save_thm("field_sub_def", ring_sub_def);
(* > val field_sub_def = |- !r x y. x - y = x + -y : thm *)

(* Theorem: x - #0 = x *)
val field_sub_zero = lift_ring_thm "sub_zero";
(* > val field_sub_zero = |- !r:'a field. Field r ==> !x. x IN R ==> (x - #0 = x): thm *)

(* Theorem: (x - y = #0) <=> (x = y) *)
val field_sub_eq_zero = lift_ring_thm "sub_eq_zero";
(* > val field_sub_eq_zero = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> ((x - y = #0) <=> (x = y)) : thm *)

(* Theorem: x - x = #0 *)
val field_sub_eq = lift_ring_thm "sub_eq";
(* > val field_sub_eq = |- !r:'a field. Field r ==> !x. x IN R ==> (x - x = #0) : thm *)

(* Theorem: x - y IN R *)
val field_sub_element = lift_ring_thm "sub_element";
(* > val field_sub_element = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> x - y IN R : thm *)

(* do not export *)
(* val _ = export_rewrites ["field_sub_element"]; *)

(* Theorem: #0 - x = -x *)
val field_zero_sub = lift_ring_thm "zero_sub";
(* val field_zero_sub = |- !r. Field r ==> !x. x IN R ==> (#0 - x = -x): thm *)

(* Theorem: (x - y = x - z) <=> (y = z) *)
val field_sub_lcancel = lift_ring_thm "sub_lcancel";
(* val field_sub_lcancel = |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((x - y = x - z) <=> (y = z)): thm *)

(* Theorem: (y - x = z - x) <=> (y = z) *)
val field_sub_rcancel = lift_ring_thm "sub_rcancel";
(* val field_sub_rcancel = |- !r. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((y - x = z - x) <=> (y = z)): thm *)

(* Theorem: -(x - y) = y - x *)
val field_neg_sub = lift_ring_thm "neg_sub";
(* > val field_neg_sub = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> (-(x - y) = y - x): thm *)

(* Theorem: x + y - y = x *)
val field_add_sub = lift_ring_thm "add_sub";
(* > val field_add_sub = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> (x + y - y = x) : thm *)

(* Theorem: y + x - y = x *)
val field_add_sub_comm = lift_ring_thm "add_sub_comm";
(* > val field_add_sub_comm = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> (y + x - y = x): thm *)

(* Theorem: x - y + y = x *)
val field_sub_add = lift_ring_thm "sub_add";
(* > val field_sub_add = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> (x - y + y = x) : thm *)

(* Theorem: (x - y = z) <=> (x = y + z) *)
val field_sub_eq_add = lift_ring_thm "sub_eq_add";
(* > val field_sub_eq_add =|- !r:'a field. Field r ==>
     !x y z. x IN R /\ y IN R /\ z IN R ==> ((x - y = z) <=> (x = y + z)): thm *)

(* Theorem: x + z - (y + z) = x - y *)
val field_sub_pair_reduce = lift_ring_thm "sub_pair_reduce";
(* > val field_sub_pair_reduce = |- !r:'a field. Field r ==>
    !x y z. x IN R /\ y IN R /\ z IN R ==> (x + z - (y + z) = x - y): thm *)

(* Theorem: (x + y = z + t) <=> (x - z = t - y) *)
val field_add_sub_identity = lift_ring_thm "add_sub_identity";
(* > val field_add_sub_identity = |- !r:'a field. Field r ==>
     !x y z t. x IN R /\ y IN R /\ z IN R /\ t IN R ==> ((x + y = z + t) <=> (x - z = t - y)): thm *)

(* Theorem: x * z - y * z = (x - y) * z *)
val field_mult_lsub = lift_ring_thm "mult_lsub";
(* > val field_mult_lsub = |- !r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x * z - y * z = (x - y) * z) : thm *)

(* Theorem: x * y - x * z = x * (y - z) *)
val field_mult_rsub = lift_ring_thm "mult_rsub";
(* > val field_mult_rsub = |- !r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x * y - x * z = x * (y - z)) : thm *)

(* Theorem: x + y - (p + q) = x - p + (y - q) *)
val field_add_pair_sub = lift_ring_thm "add_pair_sub";
(* > val field_add_pair_sub = |- !r:'a field. Field r ==>
     !x y p q. x IN R /\ y IN R /\ p IN R /\ q IN R ==> (x + y - (p + q) = x - p + (y - q)): thm *)

(* Theorem: x * y - p * q = (x - p) * (y - q) + (x - p) * q + p * (y - q) *)
val field_mult_pair_sub = lift_ring_thm "mult_pair_sub";
(* > val field_mult_pair_sub = |- !r:'a field. Field r ==>
     !x y p q. x IN R /\ y IN R /\ p IN R /\ q IN R ==>
       (x * y - p * q = (x - p) * (y - q) + (x - p) * q + p * (y - q)): thm *)

(* Theorem: m < n ==> (##(n - m) = ##n - ##m) *)
val field_num_sub = lift_ring_thm "num_sub";
(* > val field_num_sub = |- !r:'a field. Field r ==> !n m. m < n ==> (##(n - m) = ##n - ##m) : thm *)

(* ------------------------------------------------------------------------- *)
(* Field Binomial Expansions (from Ring)                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (x + y) ** 2 = x ** 2 + (##2 * (x * y) + y ** 2) *)
val field_binomial_2 = lift_ring_thm "binomial_2";
(* > val field_binomial_2 = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==>
           ((x + y) ** 2 = x ** 2 + (##2 * (x * y) + y ** 2)) : thm *)

(* Theorem: (x + y) ** 3 =
            x ** 3 + (##3 * (x ** 2 * y) + (##3 * (x * y ** 2) + y ** 3)) *)
val field_binomial_3 = lift_ring_thm "binomial_3";
(* > val field_binomial_3 = |- !r:'a field. Field r ==> !x y. x IN R /\ y IN R ==>
           ((x + y) ** 3 = x ** 3 + (##3 * (x ** 2 * y) + (##3 * (x * y ** 2) + y ** 3))) : thm *)

(* Theorem:  (x + y) ** 4 =
   x ** 4 + (##4 * (x ** 3 * y) + (##6 * (x ** 2 * y ** 2) + (##4 * (x * y ** 3) + y ** 4))) *)
val field_binomial_4 = lift_ring_thm "binomial_4";
(* > val field_binomial_4 = |- !r:'a field. Field r ==> !x y.  x IN R /\ y IN R ==>
           ((x + y) ** 4 = x ** 4 + (##4 * (x ** 3 * y) + (##6 * (x ** 2 * y ** 2) + (##4 * (x * y ** 3) + y ** 4)))) : thm *)

(* ------------------------------------------------------------------------- *)
(* Field specific theorems, about nonzeroes, inverses and division.          *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Field Theorems (not from Ring)                                            *)
(* ------------------------------------------------------------------------- *)

(* Note: This is field nonzero characterization -- without reference to Field. *)

(* Theorem: R DIFF {#0} = R+ *)
(* Proof: by ring_nonzero_def. *)
val field_nonzero_def = save_thm("field_nonzero_def", ring_nonzero_def);
(* > val field_nonzero_def = |- !r. R+ = R DIFF {#0} : thm *)

(* Theorem: Field nonzero are those not equal to #0. *)
val field_nonzero_eq = save_thm("field_nonzero_eq", ring_nonzero_eq);
(* > val field_nonzero_eq = |- !r x. x IN R+ <=> x IN R /\ x <> #0 : thm *)

(* val _ = export_rewrites ["field_nonzero_eq"]; *)

(* Theorem: Field nonzeroes are in carrier. *)
(* Proof: by ring_nonzero_element. *)
val field_nonzero_element = save_thm("field_nonzero_element", ring_nonzero_element);
(* > val field_nonzero_element = |- !r x. x IN R+ ==> x IN R : thm *)

(* val _ = export_rewrites ["field_nonzero_element"]; *)

(* Theorem: R+ SUBSET R *)
(* Proof:
   Since R+ = R DIFF {#0}    by field_nonzero_def
   Hence R+ SUBSET R         by DIFF_SUBSET
*)
val field_nonzero_subset = store_thm(
  "field_nonzero_subset",
  ``!r:'a field. R+ SUBSET R``,
  rw[field_nonzero_def]);

(* Theorem: FINITE R ==> FINITE R+ *)
(* Proof:
   Since R+ = R DIFF {#0}          by field_nonzero_def
   Hence FINITE R ==> FINITE R+    by FINITE_DIFF
*)
val field_nonzero_finite = store_thm(
  "field_nonzero_finite",
  ``!r:'a field. FINITE R ==> FINITE R+``,
  rw[field_nonzero_def]);

(* Theorem: Field r ==> Monoid f* *)
(* Proof: by Field_def, group_is_monoid *)
val field_nonzero_monoid = store_thm(
  "field_nonzero_monoid",
  ``!r:'a field. Field r ==> Monoid f*``,
  rw_tac std_ss[Field_def, group_is_monoid]);

(* Theorem: Field r ==> Group f* *)
(* Proof: by Field_def *)
val field_nonzero_group = store_thm(
  "field_nonzero_group",
  ``!r:'a field. Field r ==> Group f*``,
  rw_tac std_ss[Field_def]);

(* Same theorem by transform *)

(* Theorem: Field r ==> Group f*. *)
(* Proof: by definition. *)
val field_nonzero_mult_is_group = save_thm("field_nonzero_mult_is_group",
  Field_def |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> UNDISCH |> CONJUNCT2 |> DISCH_ALL |> GEN_ALL);
(* > val field_nonzero_mult_is_group = |- !r:'a field. Field r ==> Group f* : thm *)

(* Theorem: properties of f*. *)
(* Proof: by excluding_def
   For F* = R+
         F*
       = r.prod.carrier DIFF {#0}
       = R DIFF {#0}            by field_carriers
       = R+                     by ring_nonzero_def
   For f*.exp = r.prod.exp
       due to Monoid f* and monoid_exp_def.
*)
val field_nonzero_mult_property = store_thm(
  "field_nonzero_mult_property",
  ``!r:'a field. Field r ==> (F* = R+ ) /\
                             (f*.id = #1) /\
                             (f*.op = r.prod.op) /\
                             (f*.exp = r.prod.exp)``,
  rw[excluding_def, monoid_exp_def, ring_nonzero_def, FUN_EQ_THM]);

(* Theorem: Field r ==> (f*.exp = $** ) *)
(* Proof: by field_nonzero_mult_property *)
val field_nonzero_exp = store_thm(
  "field_nonzero_exp",
  ``!r:'a field. Field r ==> (f*.exp = $** )``,
  rw[field_nonzero_mult_property]);

(* Theorem: A Field has AbelianGroup f* *)
(* Proof: by field_nonzero_mult_is_group and Ring has AbelianMonoid (r.prod). *)
val field_nonzero_mult_is_abelian_group = store_thm(
  "field_nonzero_mult_is_abelian_group",
  ``!r:'a field. Field r ==> AbelianGroup f*``,
  rw_tac std_ss[AbelianGroup_def, field_mult_monoid, field_nonzero_element,
                 field_nonzero_mult_is_group, field_nonzero_mult_property]);

(* Theorem: Field multiplications form an Abelian group *)
(* Proof: by field_nonzero_mult_is_abelian_group. *)
val field_mult_group = store_thm(
  "field_mult_group",
  ``!r:'a field. Field r ==> Group f* /\
                   (F* = R+ ) /\
                   !x y. x IN R+ /\ y IN R+ ==> (x * y = y * x)``,
  metis_tac[AbelianGroup_def, field_nonzero_mult_property, field_nonzero_mult_is_abelian_group]);

(* Theorem: FiniteField r ==> FiniteGroup f* *)
(* Proof:
   FiniteField r ==> Field r /\ FINITE R           by FiniteField_def
         Field r ==> Group f* /\ F* = R+           by field_mult_group
   Since R+ = R DIFF {#0}                          by ring_nonzero_def
   Hence FINITE R ==> FINITE R+                    by FINITE_DIFF
   and   FINITE F* /\ Group f* ==> FiniteGroup f*  by FiniteGroup_def
*)
val finite_field_mult_finite_group = store_thm(
  "finite_field_mult_finite_group",
  ``!r:'a field. FiniteField r ==> FiniteGroup f*``,
  rw[FiniteField_def, FiniteGroup_def, field_mult_group, ring_nonzero_def]);

(* Theorem: FiniteField r ==> (CARD F* = CARD R - 1) *)
(* Proof:
   FiniteField r ==> FINITE R     by FiniteField_def
     CARD F*
   = CARD R+                      by field_nonzero_mult_property
   = CARD (R DIFF {#0})           by field_nonzero_def
   = CARD R - CARD (R INTER {#0}) by CARD_DIFF
   = CARD R - CARD {#0}           by INTER_SING
   = CARD R - 1                   by CARD_SING
*)
val finite_field_mult_carrier_card = store_thm(
  "finite_field_mult_carrier_card",
  ``!r:'a field. FiniteField r ==> (CARD F* = CARD R - 1)``,
  rw[FiniteField_def, field_nonzero_mult_property, field_nonzero_def, INTER_SING]);

(* Theorem: x IN R+ and y IN R+ ==> x * y IN R+ *)
(* Proof: by field_mult_group, group_op_element. *)
val field_mult_nonzero = store_thm(
  "field_mult_nonzero",
  ``!r:'a field. Field r ==> !x y. x IN R+ /\ y IN R+ ==> (x * y) IN R+``,
  metis_tac[group_op_element, field_mult_group, field_nonzero_mult_property]);

val _ = export_rewrites ["field_mult_nonzero"];

(* Theorem: #1 in Group f* is unique. *)
(* Proof: by group_id_unique. *)
val field_id_unique = store_thm(
  "field_id_unique",
  ``!r:'a field. Field r ==> !x y. x IN R+ /\ y IN R+ ==> ((y * x = x) <=> (y = #1)) /\ ((x * y = x) <=> (y = #1))``,
  metis_tac[group_id_unique, field_mult_group, field_nonzero_mult_property]);

(* Theorem: (x * y = #0) <=> (x = #0) \/ (y = #0) *)
(* Proof: by field_mult_nonzero, field_mult_lzero and field_mult_rzero.
   If part: x * y = #0 ==> (x = #0) \/ (y = #0)
      By contradiction,
      x <> #0 means x IN R+   by field_nonzero_eq
      y <> #0 means y IN R+   by field_nonzero_eq
      so x * y IN R+          by field_mult_nonzero
      so x * y <> #0          by field_nonzero_eq
      contradictiong x * y = #0
   Only-if part:
      If x = #0, #0 * y = #0  by field_mult_lzero
      If y = #0, x * #y = #0  by field_mult_rzero
*)
val field_mult_eq_zero = store_thm(
  "field_mult_eq_zero",
  ``!r:'a field. Field r ==> !x y. x IN R /\ y IN R ==> ((x * y = #0) <=> (x = #0) \/ (y = #0))``,
  metis_tac[field_mult_nonzero, field_nonzero_eq, field_mult_lzero, field_mult_rzero]);

(* another popular name *)
val field_zero_product = save_thm("field_zero_product", field_mult_eq_zero);

(* Theorem: Field r ==> ##2 = #1 + #1 *)
(* Proof: by field_num_add. *)
val field_num_2 = store_thm(
  "field_num_2",
  ``!r:'a field. Field r ==> (##2 = #1 + #1)``,
  metis_tac[field_num_add, field_num_1, DECIDE ``2 = 1 + 1``]);

(* Theorem: Field r ==> !x. x IN F* ==> x IN R *)
(* Proof: by field_nonzero_element, field_mult_carrier *)
val field_nonzero_element_alt = store_thm(
  "field_nonzero_element_alt",
  ``!r:'a field. Field r ==> !x. x IN F* ==> x IN R``,
  rw[field_nonzero_element, field_mult_carrier]);
(* This is not very useful: nonzero is easier than element of something excluding zero *)

(* Do not export this, otherwise all x IN R will try to prove x IN F*, usually fails. *)
(* val _ = export_rewrites ["field_nonzero_element_alt"]; *)

(* Theorem: Field r ==> !x. x IN R /\ x <> #0 ==> x IN F* *)
(* Proof: by field_nonzero_eq, field_mult_carrier *)
val field_nonzero_alt = store_thm(
  "field_nonzero_alt",
  ``!r:'a field. Field r ==> !x. x IN R /\ x <> #0 ==> x IN F*``,
  rw[field_nonzero_eq, field_mult_carrier]);

(* Theorem: For a Field, #1 <> #0 *)
(* Proof: by ring_one_eq_zero and group_carrier_nonempty. *)
val field_one_ne_zero = store_thm(
  "field_one_ne_zero",
  ``!r:'a field. Field r ==> #1 <> #0``,
  rpt strip_tac >>
  `R = {#0}` by rw_tac std_ss[GSYM ring_one_eq_zero, field_is_ring] >>
  `F* = {}` by rw[field_nonzero_mult_property, ring_nonzero_def] >>
  metis_tac[field_nonzero_mult_is_group, group_carrier_nonempty]);

val _ = export_rewrites ["field_one_ne_zero"];

(* Theorem: #1 IN R+ *)
(* Proof: by #1 <> #0 and field_nonzero_eq. *)
val field_one_nonzero = store_thm(
  "field_one_nonzero",
  ``!r:'a field. Field r ==> #1 IN R+``,
  rw[field_nonzero_eq]);

val _ = export_rewrites ["field_one_nonzero"];

(* Theorem: Field r ==> R+ <> {} *)
(* Proof: by field_one_nonzero, MEMBER_NOT_EMPTY*)
val field_nonzero_carrier_nonempty = store_thm(
  "field_nonzero_carrier_nonempty",
  ``!r:'a field. Field r ==> R+ <> {}``,
  metis_tac[field_one_nonzero, MEMBER_NOT_EMPTY]);

(* Theorem: FiniteField r ==> 0 < CARD R+ *)
(* Proof:
   Note FiniteField r
    ==> Field r /\ FINITE R       by FiniteField_def
    Now #1 <> #0                  by field_one_ne_zero
     so #1 IN R+                  by field_one_element, field_nonzero_eq
    and FINITE R+                 by field_nonzero_def, FINITE_DIFF
   Thus R+ <> {}                  by MEMBER_NOT_EMPTY
     or 0 < CARD R+               by CARD_EQ_0
*)
val field_nonzero_card_pos = store_thm(
  "field_nonzero_card_pos",
  ``!r:'a field. FiniteField r ==> 0 < CARD R+``,
  rpt (stripDup[FiniteField_def]) >>
  `#1 IN R+` by rw[field_nonzero_eq] >>
  `FINITE R+` by rw[field_nonzero_def] >>
  metis_tac[MEMBER_NOT_EMPTY, CARD_EQ_0, NOT_ZERO_LT_ZERO]);

(* Theorem: FiniteField r ==> ((R+ = {#1}) <=> (CARD R+ = 1)) *)
(* Proof:
   If part: R+ = {#1} ==> CARD R+ = 1
      True by CARD_SING.
   Only-if part: CARD R+ = 1 ==> R+ = {#1}
      Note #1 IN R+           by field_one_ne_zero, field_nonzero_eq
       and FINITE R+          by field_nonzero_finite
      also SING R+            by CARD_EQ_1
     Hence R+ = {#1}          by SING_DEF, IN_SING
*)
val field_nonzero_card_eq_1 = store_thm(
  "field_nonzero_card_eq_1",
  ``!r:'a field. FiniteField r ==> ((R+ = {#1}) <=> (CARD R+ = 1))``,
  rpt (stripDup[FiniteField_def]) >>
  rw[EQ_IMP_THM] >>
  `#1 IN R+` by rw[] >>
  `FINITE R+` by rw[field_nonzero_finite] >>
  `SING R+` by rw[GSYM CARD_EQ_1] >>
  metis_tac[SING_DEF, IN_SING]);

(* Theorem: Field r ==> x IN R+ <=> unit x *)
(* Proof:
   Note that:
   Field r ==> Ring r /\ Group f*    by Field_def
   If part: x IN R+ ==> unit x
   Since F* = R+                     by field_nonzero_mult_property
   f*.inv x IN R+                    by group_inv_element
   f*.inv x * x = #1 and
   x * f*.inv x = #1                 by group_linv, group_rinv, field_nonzero_mult_property
   unit x means x IN monoid_invertibles r.prod          by Invertibles_def
   i.e. ?y. y IN R /\ (x * y = #1) /\ (y * x = #1)      by monoid_invertibles_def
   Since x IN R /\ f*.inv x IN R     by ring_nonzero_element
   Putting y = f*.inv x, unit x is true.
   Only-if part: unit x ==> x IN R+
   Field r ==> #1 <> #0                                 by field_one_ne_zero
   Hence unit x ==> x <> #0                             by ring_units_has_zero
   Also unit x ==> x IN R                               by ring_unit_element
   Hence x IN R+                                        by field_nonzero_eq
*)
val field_nonzero_unit = store_thm(
  "field_nonzero_unit",
  ``!r:'a field. Field r ==> !x. x IN R+ <=> unit x``,
  rw_tac std_ss[Invertibles_def, monoid_invertibles_def, field_carriers, GSPECIFICATION] >>
  `Ring r /\ Group f*` by metis_tac[Field_def] >>
  rw[ring_nonzero_element, EQ_IMP_THM] >| [
    qexists_tac `f*.inv x` >>
    `F* = R+` by rw[field_nonzero_mult_property] >>
    `f*.inv x IN R+` by metis_tac[group_inv_element] >>
    `(f*.inv x * x = #1) /\ (x * (f*.inv x) = #1)`
     by metis_tac[group_linv, group_rinv, field_nonzero_mult_property] >>
    rw[ring_nonzero_element],
    `x <> #0` by metis_tac[field_mult_lzero, field_mult_rzero, field_one_ne_zero] >>
    rw[field_nonzero_eq]
  ]);

(* ------------------------------------------------------------------------- *)
(* Field Exponential Nonzero Theorems.                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: x IN R+ ==> x ** n IN R+ *)
(* Proof: by induction on n.
   Base case: x ** 0 IN R+
      x ** 0 = #1  by field_exp_0
      hence true by field_one_nonzero
   Step case: x ** n IN R+ ==> x ** SUC n IN R+
      x ** SUC n = x * x ** n    by field_exp_SUC
      hence true by field_mult_nonzero and induction hypothesis
*)
val field_exp_nonzero = store_thm(
  "field_exp_nonzero",
  ``!r:'a field. Field r ==> !x. x IN R+ ==> !n. x ** n IN R+``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[field_nonzero_element]);

val _ = export_rewrites ["field_exp_nonzero"];

(* Theorem: x ** n = #0 <=> n <> 0 /\ x = #0 *)
(* Proof:
   If part: x ** n = #0 ==> n <> 0 /\ x = #0
      By contradicton.
      If n = 0, then x ** #0 = #1  by field_exp_0
      but for a field, #1 <> #0    by field_one_ne_zero.
      hence a contradiction.
      If x <> #0, then x IN R+ by field_nonzero_eq
      and x ** n IN R+         by field_exp_nonzero
      so x ** n <> #0              by  field_nonzero_eq
      hence a contradiction.
   Only-if part: n <> 0 /\ x = #0 ==> x ** n = #0
      true by field_zero_exp.
*)
val field_exp_eq_zero = store_thm(
  "field_exp_eq_zero",
  ``!r:'a field. Field r ==> !x. x IN R ==> !n. (x ** n = #0) <=> n <> 0 /\ (x = #0)``,
  rw_tac std_ss[field_zero_exp, EQ_IMP_THM] >-
  metis_tac[field_exp_0, field_one_ne_zero] >>
  metis_tac[field_exp_nonzero, field_nonzero_eq, field_exp_element]);

(* ------------------------------------------------------------------------- *)
(* Field Inversion Theorems.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r ==> f*.inv x = |/ x *)
(* Proof:
   Field r ==> Ring r /\ Group f*   by Field_def
   x IN R+ ==> unit x               by field_nonzero_unit
   unit x ==> unit ( |/x)           by ring_unit_has_inv
   Hence |/x IN R+                  by field_nonzero_unit
   and   |/x * x = #1               by ring_unit_linv
   Now   F* = R+                    by field_nonzero_mult_property
   Hence f*.inv x = |/ x            by group_linv_unique
*)
val field_mult_inv = store_thm(
  "field_mult_inv",
  ``!r:'a field. Field r ==> !x. x IN R+ ==> (f*.inv x = |/ x)``,
  rpt strip_tac >>
  `Ring r /\ Group f*` by metis_tac[Field_def] >>
  `unit x` by rw[GSYM field_nonzero_unit] >>
  `unit ( |/x)` by rw[ring_unit_has_inv] >>
  `|/x IN R+` by rw[field_nonzero_unit] >>
  `|/x * x = #1` by rw[ring_unit_linv] >>
  metis_tac[group_linv_unique, field_nonzero_mult_property]);

(*
- show_assums := true;
> val it = () : unit
- group_inv_element;
> val it =  [] |- !g. Group g ==> !x. x IN G ==> |/ x IN G : th
- field_mult_group;
> val it = [] |- !r:'a field. Field r ==> Group f* /\ (F* = R+ ) /\
                 !x y. x IN R+ /\ y IN R+ ==> (x * y = y * x) : thm
- group_inv_element |> SPEC_ALL |> UNDISCH;
> val it =  [Group g] |- !x. x IN G ==> |/ x IN G : thm
- group_inv_element |> SPEC ``f*``;
> val it = [] |- Group f* ==>  !x.  x IN F* ==> |/ x IN F* : thm
- group_inv_element |> SPEC ``f*`` |> UNDISCH;
> val it = [Group f*] |- !x.  x IN F* ==> |/ x IN F* : thm
- field_mult_group |> SPEC_ALL |> UNDISCH;
> val it = [Field r] |- Group f* /\ (F* = R+ ) /\
       !x y. x IN R+ /\ y IN R+ ==> (x * y = y * x) : thm
- field_mult_group |> SPEC_ALL |> UNDISCH |> CONJUNCT1;
> val it =  [Field r] |- Group f* : thm
- field_mult_group |> SPEC_ALL |> UNDISCH |> CONJUNCT2 |> CONJUNCT1;
> val it =  [Field r] |- F* = R+ : thm
- group_inv_element |> SPEC ``f*`` |> UNDISCH |> PROVE_HYP (field_mult_group |> SPEC_ALL |> UNDISCH |> CONJUNCT1);
> val it = [Field r] |- !x.  x IN F* ==> |/ x IN F* : thm
- group_inv_element |> SPEC ``f*`` |> UNDISCH |> PROVE_HYP (field_mult_group |> SPEC_ALL |> UNDISCH |> CONJUNCT1) |> REWRITE_RULE [field_mult_group |> SPEC_ALL |> UNDISCH |> CONJUNCT2 |> CONJUNCT1];
> val it =  [Field r] |- !x. x IN R+ ==> |/ x IN R+ : thm
- group_inv_element |> SPEC ``f*`` |> UNDISCH |> PROVE_HYP (field_mult_group |> SPEC_ALL |> UNDISCH |> CONJUNCT1) |> REWRITE_RULE [field_mult_group |> SPEC_ALL |> UNDISCH |> CONJUNCT2 |> CONJUNCT1] |> DISCH_ALL |> GEN_ALL;
> val it =  [] |- !r:'a field. Field r ==> !x. x IN R+ ==> |/ x IN R+ : thm
- show_assums := false;
> val it = () : unit
*)

(* Lifting Group Inverse Theorem for Field
   from: !g: 'a group. Group g ==> E(g.inv)
     to: !r:'a field.  Field r ==> E(f*.inv)
    via: !r:'a field.  Field r ==> Group f* /\ (f* = R+ )
*)
local
val fmg = field_mult_group |> SPEC_ALL |> UNDISCH_ALL
val fmgroup = fmg |> CONJUNCT1
(* val fmcarrier = fmg |> CONJUNCT2 |> CONJUNCT1 *)
val fmpropery = field_nonzero_mult_property |> SPEC_ALL |> UNDISCH_ALL
in
fun lift_group_inv_thm_with_goal gsuffix rsuffix goal = let
  val thm = DB.fetch "group" ("group_" ^ gsuffix)
  val thm' = thm |> SPEC ``f*`` |> UNDISCH_ALL
in
  store_thm("field_" ^ rsuffix, goal,
      metis_tac[thm' |> PROVE_HYP fmgroup
                     |> REWRITE_RULE [fmpropery] (* original: fmcarrier *)
                     |> DISCH_ALL |> GEN_ALL,
                field_mult_group, field_nonzero_mult_property, field_mult_inv])
end
end; (* local *)

(* Theorem: x * y = #1 <=> y = |/ x *)
(* Proof: by group_rinv_unique. *)
val field_rinv_unique = lift_group_inv_thm_with_goal "rinv_unique" "rinv_unique"
    ``!r:'a field. Field r ==> !x y. x IN R+ /\ y IN R+ ==> ((x * y = #1) <=> (y = |/ x))``;
(* > val field_rinv_unique = |- !r. Field r ==> !x y. x IN R+ /\ y IN R+ ==> ((x * y = #1) <=> (y = |/ x)) : thm *)

(* Theorem: y * x = #1 <=> y = |/ x *)
(* Proof: by group_linv_unique. *)
val field_linv_unique = lift_group_inv_thm_with_goal "linv_unique" "linv_unique"
    ``!r:'a field. Field r ==> !x y. x IN R+ /\ y IN R+ ==> ((y * x = #1) <=> (y = |/ x))``;

(*
group_inv_element |> SPEC ``f*`` |> UNDISCH
 |> PROVE_HYP (field_mult_group |> SPEC_ALL |> UNDISCH |> CONJUNCT1)
 |> REWRITE_RULE [field_mult_group |> SPEC_ALL |> UNDISCH |> CONJUNCT2 |> CONJUNCT1] |> SPEC_ALL |> UNDISCH
 |> REWRITE_RULE [field_mult_inv |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH]
 |> DISCH ``x IN R+`` |> GEN_ALL |> DISCH_ALL |> GEN_ALL ;
> val it = |- !r:'a field. Field r ==> !x. x IN R+ ==> |/ x IN R+ : thm

ring_unit_has_inv |> SPEC_ALL |> UNDISCH
 |> PROVE_HYP (field_is_ring |> SPEC_ALL |> UNDISCH) |> SPEC_ALL |> UNDISCH
 |> PROVE_HYP (field_nonzero_unit |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH)
 |> MP (field_nonzero_unit |> SPEC_ALL |> UNDISCH |> SPEC ``|/ x`` |> #2 o EQ_IMP_RULE)
 |> DISCH ``x IN R+`` |> GEN_ALL |> DISCH_ALL |> GEN_ALL;
> val it = |- !r:'a field. Field r ==> !x. x IN R+ ==> |/ x IN R+ : thm
*)

(*
DB.fetch "group" "group_inv_op";
DB.fetch "group" "group_inv_op" |> SPEC ``f*`` |> UNDISCH_ALL;
DB.fetch "group" "group_inv_op" |> SPEC ``f*`` |> UNDISCH_ALL
   |> PROVE_HYP (field_mult_group |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1);
DB.fetch "group" "group_inv_op" |> SPEC ``f*`` |> UNDISCH_ALL
   |> PROVE_HYP (field_mult_group |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1)
   |> REWRITE_RULE [field_nonzero_mult_property |> SPEC_ALL |> UNDISCH_ALL];
g `!r:'a field. Field r ==> !x y. x IN R+ /\ y IN R+ ==> ( |/ (x * y) = |/ y * |/ x)`;
e (rpt strip_tac);
e (metis_tac[DB.fetch "group" "group_inv_op" |> SPEC ``f*`` |> UNDISCH_ALL
   |> PROVE_HYP (field_mult_group |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1)
   |> REWRITE_RULE [field_nonzero_mult_property |> SPEC_ALL |> UNDISCH_ALL], field_mult_group, field_nonzero_mult_property, group_op_element, field_mult_inv]);
*)

(* Lift Ring Unit Theorem with goal *)
local
val fir = field_is_ring |> SPEC_ALL |> UNDISCH
in
fun lift_ring_unit_thm_with_goal rsuffix fsuffix goal = let
   val rth = DB.fetch "ring" ("ring_" ^ rsuffix)
   val rth' = rth |> SPEC_ALL |> UNDISCH |> PROVE_HYP fir |> DISCH_ALL |> GEN_ALL
in
   store_thm("field_" ^ fsuffix, goal, metis_tac[rth', field_nonzero_unit])
end
end; (* local *)

(* Theorem: Field r ==> !x. x IN R+ ==> |/ x IN R+ *)
(* Proof: by ring_unit_has_inv, field_nonzero_unit and field_is_ring. *)
val field_inv_nonzero = lift_ring_unit_thm_with_goal "unit_has_inv" "inv_nonzero"
    ``!r:'a field. Field r ==> !x. x IN R+ ==> |/ x IN R+``;
(* > val field_inv_nonzero = |- !r:'a field. Field r ==> !x. x IN R+ ==> |/ x IN R+ : thm *)

val _ = export_rewrites ["field_inv_nonzero"];

(* Theorem: Field r ==> x IN R => |/x IN R *)
(* Proof: by field_inv_nonzero and field_nonzero_element. *)
val field_inv_element = store_thm(
  "field_inv_element",
  ``!r:'a field. Field r ==> !x. x IN R+ ==> |/ x IN R``,
  rw_tac std_ss[field_inv_nonzero, field_nonzero_element]);

val _ = export_rewrites ["field_inv_element"];

(* Theorem: |/ x * x = #1 *)
(* Proof: by ring_unit_linv, field_nonzero_unit and field_is_ring. *)
val field_mult_linv = lift_ring_unit_thm_with_goal "unit_linv" "mult_linv"
   ``!r:'a field. Field r ==> !x. x IN R+ ==> ( |/ x * x = #1)``;
(* > val field_mult_linv = |- !r:'a field. Field r ==> !x. x IN R+ ==> ( |/ x * x = #1) : thm *)

(* Theorem: x * |/ x = #1 *)
(* Proof: either by ring_unit_rinv, or field_mult_linv and field_mult_comm. *)
val field_mult_rinv = lift_ring_unit_thm_with_goal "unit_rinv" "mult_rinv"
   ``!r:'a field. Field r ==> !x. x IN R+ ==> (x * |/ x = #1)``;
(* > val field_mult_rinv = |- !r:'a field. Field r ==> !x. x IN R+ ==> (x * |/ x = #1) : thm *)

val _ = export_rewrites ["field_mult_linv", "field_mult_rinv"];


(* Theorem: |/ x * x * y = y *)
(* Proof: by field_mult_linv. *)
val field_mult_linv_assoc = store_thm(
  "field_mult_linv_assoc",
  ``!r:'a field. Field r ==> !x y. x IN R+ /\ y IN R ==> (y = x * ( |/ x * y)) /\ (y = |/ x * (x * y))``,
  metis_tac[field_mult_linv, field_mult_rinv, field_mult_lone, field_mult_assoc, field_inv_nonzero, field_nonzero_element]);

(* Theorem: x * |/ x * y = y *)
(* Proof: by field_mult_rinv. *)
val field_mult_rinv_assoc = store_thm(
  "field_mult_rinv_assoc",
  ``!r:'a field. Field r ==> !x y. x IN R+ /\ y IN R ==> (y = y * |/ x * x) /\ (y = y * x * |/ x)``,
  rw_tac std_ss[field_mult_linv, field_mult_rinv, field_mult_rone, field_mult_assoc, field_inv_nonzero, field_nonzero_element]);


(* Theorem: x * y = x * z <=> y = z *)
(* Proof: by field_mult_linv_assoc. *)
val field_mult_lcancel = store_thm(
  "field_mult_lcancel",
  ``!r:'a field. Field r ==> !x y z. x IN R+ /\ y IN R /\ z IN R ==> ((x * y = x * z) = (y = z))``,
  metis_tac[field_mult_linv_assoc, field_inv_nonzero]);

(* Theorem: y * x = z * x <=> y = z *)
(* Proof: by field_mult_lcancel and field_mult_comm. *)
val field_mult_rcancel = store_thm(
  "field_mult_rcancel",
  ``!r:'a field. Field r ==> !x y z. x IN R+ /\ y IN R /\ z IN R ==> ((y * x = z * x) = (y = z))``,
  rw_tac std_ss[field_mult_lcancel, field_mult_comm, field_nonzero_element]);

(* Theorem: Field r ==> !x. x IN R+ ==> !y. y IN R /\ ((x * y = x) \/ (y * x = x)) ==> (y = #1) *)
(* Proof:
   Since x * y = x = x * #1         by field_mult_rone
      so     y = #1                 by field_mult_lcancel, x IN R+
    Also y * x = x = #1 * x         by field_mult_lone
      so     y = #1                 by field_mult_rcancel, x IN R+
*)
val field_nonzero_mult_eq_self = store_thm(
  "field_nonzero_mult_eq_self",
  ``!r:'a field. Field r ==> !x. x IN R+ ==> !y. y IN R /\ ((x * y = x) \/ (y * x = x)) ==> (y = #1)``,
  ntac 5 strip_tac >>
  `x IN R` by metis_tac[field_nonzero_eq] >>
  `#1 IN R /\ (x * #1 = x) /\ (#1 * x = x)` by rw[] >>
  metis_tac[field_mult_lcancel, field_mult_rcancel]);

(* Theorem: !x y. x IN R+ /\ y IN R+ ==> (( |/ x * y = #1) <=> (x = y)) *)
(* Proof:
   Note Field r ==> Group f*        by field_mult_group
   Apply group_op_linv_eq_id |> ISPEC ``f*``;
   val it = |- Group f* ==> !x y. x IN F* /\ y IN F* ==> ((f*.op (f*.inv x) y = f*.id) <=> (x = y)): thm
   Then use field_nonzero_mult_property and field_mult_inv.
*)
val field_mult_linv_eq_one = store_thm(
  "field_mult_linv_eq_one",
  ``!r:'a field. Field r ==> !x y. x IN R+ /\ y IN R+ ==> (( |/ x * y = #1) <=> (x = y))``,
  metis_tac[field_mult_group, group_op_linv_eq_id, field_nonzero_mult_property, field_mult_inv]);

(* Theorem: !x y. x IN R+ /\ y IN R+ ==> ((x * |/ y = #1) <=> (x = y)) *)
(* Proof:
   Note Field r ==> Group f*        by field_mult_group
   Apply group_op_rinv_eq_id |> ISPEC ``f*``;
   val it = |- Group f* ==> !x y. x IN F* /\ y IN F* ==> ((f*.op x (f*.inv y) = f*.id) <=> (x = y)): thm
   Then use field_nonzero_mult_property and field_mult_inv.
*)
val field_mult_rinv_eq_one = store_thm(
  "field_mult_rinv_eq_one",
  ``!r:'a field. Field r ==> !x y. x IN R+ /\ y IN R+ ==> ((x * |/ y = #1) <=> (x = y))``,
  metis_tac[field_mult_group, group_op_rinv_eq_id, field_nonzero_mult_property, field_mult_inv]);

(* Theorem: !x y z. x IN R+ /\ y IN R /\ z IN R ==> (( |/ x * y = z) <=> (y = x * z)) *)
(* Proof:
   Note x IN R /\ x <> #0           by field_nonzero_eq
     so |/ x IN R /\ |/ x <> #0     by field_inv_nonzero
   If y = #0, to show:
      #0 = z <=> #0 = x * z         by field_mult_rzero
      which is true                 by field_mult_eq_zero, x <> #0
   If z = #0, to show:
      |/ x * y = #0 <=> y = #0      by field_mult_rzero
      which is true                 by field_mult_eq_zero, |/ x <> #0

   Otherwise, all x, y, z in R+     by field_nonzero_eq
   Note Field r ==> Group f*        by field_mult_group
   Apply group_op_linv_eqn |> ISPEC ``f*``;
   val it = |- Group f* ==> !x y z. x IN F* /\ y IN F* /\ z IN F* ==> ((f*.op (f*.inv x) y = z) <=> (y = f*.op x z)): thm
   Then use field_nonzero_mult_property and field_mult_inv.
*)
Theorem field_mult_linv_eqn:
  !r:'a field. Field r ==> !x y z. x IN R+ /\ y IN R /\ z IN R ==> (( |/ x * y = z) <=> (y = x * z))
Proof
  rpt strip_tac >>
  assume_tac field_nonzero_eq >>
  Cases_on `y = #0` >-
  metis_tac[field_mult_rzero, field_mult_eq_zero, field_inv_element] >>
  Cases_on `z = #0` >-
  metis_tac[field_mult_rzero, field_mult_eq_zero, field_inv_nonzero] >>
  `Group f*` by rw[field_mult_group] >>
  metis_tac[group_op_linv_eqn, field_nonzero_mult_property, field_mult_inv]
QED

(* Theorem: Field r ==> !x y z. x IN R /\ y IN R+ /\ z IN R ==> ((x * |/ y = z) <=> (x = z * y)) *)
(* Proof:
   Note y IN R /\ y <> #0           by field_nonzero_eq
     so |/ y IN R /\ |/ y <> #0     by field_inv_nonzero
   If x = #0, to show:
      #0 = z <=> #0 = z * y         by field_mult_lzero
      which is true                 by field_mult_eq_zero, y <> #0
   If z = #0, to show:
      x * |/ y = #0 <=> x = #0      by field_mult_lzero
      which is true                 by field_mult_eq_zero, |/ y <> #0

   Otherwise, all x, y, z in R+     by field_nonzero_eq
   Note Field r ==> Group f*        by field_mult_group
   Apply group_op_rinv_eqn |> ISPEC ``f*``;
   val it = |- Group f* ==> !x y z. x IN F* /\ y IN F* /\ z IN F* ==> ((f*.op x (f*.inv y) = z) <=> (x = f*.op z y)): thm
   Then use field_nonzero_mult_property and field_mult_inv.

   Another method:
   Note y IN R /\ |/ y IN R        by field_nonzero_element, field_inv_element
   The result follows              by field_mult_linv_eqn, field_mult_comm
*)
Theorem field_mult_rinv_eqn:
  !r:'a field. Field r ==> !x y z. x IN R /\ y IN R+ /\ z IN R ==> ((x * |/ y = z) <=> (x = z * y))
Proof
  metis_tac[field_mult_linv_eqn, field_mult_comm, field_nonzero_element, field_inv_element]
QED

(* Theorem: |/ (x * y) = |/ y * |/ x *)
(* Proof: by group_inv_op, field_mult_inv, and r.prod group. *)
val field_inv_mult_comm = store_thm(
  "field_inv_mult_comm",
  ``!r:'a field. Field r ==> !x y. x IN R+ /\ y IN R+ ==> ( |/ (x * y) = |/ y * |/ x)``,
  metis_tac[group_inv_op |> SPEC ``f*`` |> UNDISCH_ALL
   |> PROVE_HYP (field_mult_group |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1) |> DISCH_ALL,
   field_mult_group, field_nonzero_mult_property, group_op_element, field_mult_inv]);
(* > val field_inv_mult_comm = |- !r:'a field. Field r ==> !x y. x IN R+ /\ y IN R+ ==> ( |/ (x * y) = |/ y * |/ x) : thm *)
(* Surprisingly, this is used in the proof of field_single_mult_inv_exp. *)

(* Theorem: for Field, |/ (x * y) = |/ x * |/ y *)
(* Proof: by field_inv_mult_comm and field_mult_comm. *)
val field_inv_mult = store_thm(
  "field_inv_mult",
  ``!r:'a field. Field r ==> !x y. x IN R+ /\ y IN R+ ==> ( |/ (x * y) = ( |/ x) * ( |/ y))``,
  rw_tac std_ss[field_inv_mult_comm, field_mult_comm, field_inv_element]);

(* export simple theorem *)
val _ = export_rewrites ["field_inv_mult"];

(* Theorem: Field r ==> |/ #1 = #1 *)
(* Proof: by ring_inv_one, field_is_ring. *)
Theorem field_inv_one[simp]:
  !r:'a field. Field r ==> ( |/ #1 = #1)
Proof metis_tac[ring_inv_one, field_is_ring]
QED

(* Theorem: |/ ( |/ x) = x *)
(* Proof: by group_inv_inv and r.prod group. *)
Theorem field_inv_inv[simp]:
  !r:'a field. Field r ==> !x. x IN R+ ==> ( |/ ( |/ x) = x)
Proof
  metis_tac[group_inv_inv
              |> SPEC ``f*`` |> UNDISCH_ALL
              |> PROVE_HYP
                 (field_mult_group |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1)
              |> DISCH_ALL,
            field_mult_group, field_nonzero_mult_property, group_inv_element,
            field_mult_inv]
QED

(* Theorem: x IN R+ ==> - x IN R+ *)
(* Proof: by contradiction.
   Suppose - x NOTIN R+, but x IN R+.
   Since both  x IN carrier     by field_nonzero_element
          and -x IN carrier     by field_neg_element
   then by field_nonzero_eq, x <> #0 but -x = #0
   This contradicts field_neg_eq_zero: - x = #0 <=> x = #0.
*)
val field_neg_nonzero = store_thm(
  "field_neg_nonzero",
  ``!r:'a field. Field r ==> !x. x IN R+ ==> - x IN R+``,
  rw_tac std_ss[field_neg_eq_zero, field_nonzero_eq, field_nonzero_element, field_neg_element]);

(* export simple theorem *)
val _ = export_rewrites ["field_neg_nonzero"];

(* Theorem: x IN R+ ==> |/ (- x) = - ( |/ x) *)
(* Proof:
      - ( |/ x) * (- x)
    = |/x * x                  by field_mult_neg_neg
    = #1                       by field_mult_linv
    = |/ (- x) * (- x)         by field_mult_linv
   hence
      |/ (- x) = - ( |/ x)     by field_mult_rcancel
*)
val field_inv_neg = store_thm(
  "field_inv_neg",
  ``!r:'a field. Field r ==> !x. x IN R+ ==> ( |/ (- x) = - ( |/ x))``,
  rpt strip_tac >>
  `- x IN R+ /\ |/x IN R+ /\ |/ (- x) IN R+ /\ - ( |/ x) IN R+` by rw[] >>
  `x IN R /\ |/ x IN R /\ |/ (- x) IN R /\ - ( |/ x) IN R` by rw_tac std_ss[field_nonzero_element] >>
  metis_tac[field_mult_neg_neg, field_mult_linv, field_mult_rcancel]);

(* export simple theorem *)
val _ = export_rewrites ["field_inv_neg"];

(* Theorem: x IN R+ ==> |/ x ** n = |/ (x ** n) *)
(* Proof: by group_inv_exp. *)
val field_inv_exp = store_thm(
  "field_inv_exp",
  ``!r:'a field. Field r ==> !x. x IN R+ ==> !n. |/ x ** n = |/ (x ** n)``,
  metis_tac[group_inv_exp |> SPEC ``f*`` |> UNDISCH_ALL
   |> PROVE_HYP (field_mult_group |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1) |> DISCH_ALL,
   field_mult_group, field_nonzero_mult_property, group_exp_element, field_mult_inv]);
(* > val field_inv_exp = |- !r:'a field. Field r ==> !x. x IN R+ ==> !n. |/ x ** n = |/ (x ** n) : thm *)

(* export simple theorem *)
val _ = export_rewrites ["field_inv_exp"];

(* Theorem: x IN R+ ==> |/ (x ** n) = |/ x ** n *)
(* Proof: by group_exp_inv. *)
val field_exp_inv = store_thm(
  "field_exp_inv",
  ``!r:'a field. Field r ==> !x. x IN R+ ==> !n. |/ (x ** n) = |/ x ** n``,
  metis_tac[group_exp_inv |> SPEC ``f*`` |> UNDISCH_ALL
   |> PROVE_HYP (field_mult_group |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1) |> DISCH_ALL,
   field_mult_group, field_nonzero_mult_property, group_exp_element, field_mult_inv]);
(* > val field_exp_inv = |- !r:'a field. Field r ==> !x. x IN R+ ==> !n. |/ (x ** n) = |/ x ** n : thm *)

(* Theorem: x ** n * |/ x = if n = 0 then |/ x else x ** (n - 1) *)
(* Proof: by cases on n = 0. *)
val field_mult_exp_inv = store_thm(
  "field_mult_exp_inv",
  ``!r:'a field. Field r ==> !x. x IN R+ ==> !n. x ** n * |/ x = if n = 0 then |/ x else x ** (n - 1)``,
  rpt strip_tac >>
  rw_tac std_ss[] >-
  rw[field_nonzero_element] >>
  `n = SUC (n-1)` by decide_tac >>
  `x IN R /\ |/ x IN R` by rw[field_nonzero_element] >>
  `x ** n * |/ x = x ** (n-1) * x * |/ x` by metis_tac[field_exp_suc] >>
  rw[field_mult_assoc]);

(* Theorem: x ** n * ( |/ x * y) = if n = 0 then |/ x * y else x ** (n - 1) * y *)
(* Proof: by field_mult_exp_inv. *)
val field_mult_exp_inv_assoc = store_thm(
  "field_mult_exp_inv_assoc",
  ``!r:'a field. Field r ==> !x y. x IN R+ /\ y IN R ==> !n. x ** n * ( |/ x * y) = if n = 0 then |/ x * y else x ** (n - 1) * y``,
  rpt strip_tac >>
  `x ** n IN R /\ |/x IN R` by rw[field_nonzero_element] >>
  `x ** n * ( |/ x * y) = (x ** n * |/ x) * y` by rw[field_mult_assoc] >>
  rw_tac std_ss[field_mult_exp_inv]);

(* Theorem: x ** m * |/ (x ** n) = if m < n then |/ (x ** (n - m)) else x ** (m - n) *)
(* Proof: by cases of m < n. *)
val field_mult_exp_inv_exp = store_thm(
  "field_mult_exp_inv_exp",
  ``!r:'a field. Field r ==> !x. x IN R+ ==> !m n. x ** m * |/ (x ** n) = if m < n then |/ (x ** (n - m)) else x ** (m - n)``,
  rpt strip_tac >>
  `x IN R /\ |/ x IN R+ /\ |/ x IN R` by rw[field_nonzero_element] >>
  rw_tac std_ss[] >| [
    `x ** m IN R+ /\ x ** (n-m) IN R+ /\ |/ (x ** m) IN R+ /\ |/ (x ** (n - m)) IN R+` by rw[] >>
    `x ** m * |/ (x ** n) = x ** m * |/ (x ** m * x ** (n - m))`
      by metis_tac[field_exp_add, DECIDE ``m < n ==> (n = m + (n - m))``] >>
    `_ = x ** m * |/ (x ** m) * |/ (x ** (n - m))` by rw[field_mult_assoc, field_nonzero_element] >>
    rw_tac std_ss[field_mult_rinv, field_mult_lone, field_nonzero_element],
    `x ** n IN R+ /\ x ** (m-n) IN R+ /\ |/ (x ** n) IN R+` by rw[] >>
    `x ** m * |/ (x ** n) = x ** (m - n) * x ** n * |/ (x ** n)`
      by metis_tac[field_exp_add, DECIDE ``~(m < n) ==> (m = m - n + n)``] >>
    rw[field_mult_assoc, field_nonzero_element]
  ]);

(* Theorem: x ** m * ( |/ (x ** n) * y) = if m < n then |/ (x ** (n - m)) * y else x ** (m - n) * y *)
(* Proof: by field_mult_exp_inv_exp. *)
val field_mult_exp_inv_exp_assoc = store_thm(
  "field_mult_exp_inv_exp_assoc",
  ``!r:'a field. Field r ==> !x y. x IN R+ /\ y IN R ==>
   !m n. x ** m * ( |/ (x ** n) * y) =  if m < n then |/ (x ** (n - m)) * y else x ** (m - n) * y``,
  rpt strip_tac >>
  `x ** m * ( |/ (x ** n) * y) = x ** m * |/ (x ** n) * y` by rw[field_mult_assoc, field_nonzero_element] >>
  rw_tac std_ss[field_mult_exp_inv_exp]);

(* Theorem: |/ x * |/ x = |/ (x ** 2) *)
(* Proof: |/ x * |/ x = | /(x * x) = |/ (x ** 2) *)
val field_inv_mult_inv = store_thm(
  "field_inv_mult_inv",
  ``!r:'a field. Field r ==> !x. x IN R+ ==> ( |/ x * |/ x = |/ (x ** 2))``,
  rw_tac std_ss[field_inv_mult, field_exp_small, field_nonzero_element]);

(* Theorem: |/ x * ( |/ x * y) = |/ (x ** 2) * y *)
(* Proof: by field_inv_mult_inv. *)
val field_inv_mult_inv_assoc = store_thm(
  "field_inv_mult_inv_assoc",
  ``!r:'a field. Field r ==> !x y. x IN R+ /\ y IN R ==> ( |/ x * ( |/ x * y) = |/ (x ** 2) * y)``,
  rpt strip_tac >>
  `|/ x * ( |/ x * y) = |/ x * |/ x * y` by rw[field_mult_assoc] >>
  rw_tac std_ss[field_inv_mult_inv]);

(* Theorem: |/ x * |/ (x ** n) = |/ (x ** (n + 1)) *)
(* Proof: by field_inv_mult and field_single_mult_exp. *)
val field_inv_mult_inv_exp = store_thm(
  "field_inv_mult_inv_exp",
  ``!r:'a field. Field r ==> !x. x IN R+ ==> !n. |/ x * |/ (x ** n) = |/ (x ** (n + 1))``,
  metis_tac[field_inv_mult, field_single_mult_exp, field_exp_nonzero, field_nonzero_element]);

(* Theorem: |/ x * ( |/ (x ** n) * y) = |/ (x ** (n + 1)) * y *)
(* Proof: by field_inv_mult_inv_exp. *)
val field_inv_mult_inv_exp_assoc = store_thm(
  "field_inv_mult_inv_exp_assoc",
  ``!r:'a field. Field r ==> !x y. x IN R+ /\ y IN R ==> !n. |/ x * ( |/ (x ** n) * y) = |/ (x ** (n + 1)) * y``,
  rpt strip_tac >>
  `|/ x * ( |/ (x ** n) * y) = |/ x * |/ (x ** n) * y` by rw[field_mult_assoc, field_nonzero_element] >>
  rw_tac std_ss[field_inv_mult_inv_exp]);

(* Theorem: |/ (x ** m) * |/ (x ** n) = |/ (x ** (m + n)) *)
(* Proof: by field_inv_mult, field_exp_add. *)
val field_inv_exp_mult_inv_exp = store_thm(
  "field_inv_exp_mult_inv_exp",
  ``!r:'a field. Field r ==> !x. x IN R+ ==> !m n. |/ (x ** m) * |/ (x ** n) = |/ (x ** (m + n))``,
  rw_tac std_ss[field_inv_mult, field_exp_add, field_exp_nonzero, field_nonzero_element]);

(* Theorem: |/ (x ** m) * ( |/ (x ** n) * y) = |/ (x ** (m + n)) * y *)
(* Proof: by field_inv_exp_mult_inv_exp. *)
val field_inv_exp_mult_inv_exp_assoc = store_thm(
  "field_inv_exp_mult_inv_exp_assoc",
  ``!r:'a field. Field r ==> !x y. x IN R+ /\ y IN R ==> !m n. |/ (x ** m) * ( |/ (x ** n) * y) = |/ (x ** (m + n)) * y``,
  rpt strip_tac >>
  `|/ (x ** m) * ( |/ (x ** n) * y) = |/ (x ** m) * |/ (x ** n) * y` by rw[field_mult_assoc] >>
  rw_tac std_ss[field_inv_exp_mult_inv_exp]);

(* Theorem: x * |/ (x ** n) = if n = 0 then x else |/ (x ** (n - 1)) *)
(* Proof: by cases on n = 0. *)
val field_single_mult_inv_exp = store_thm(
  "field_single_mult_inv_exp",
  ``!r:'a field. Field r ==> !x. x IN R+ ==> !n. x * |/ (x ** n) = if n = 0 then x else |/ (x ** (n - 1))``,
  rpt strip_tac >>
  rw_tac std_ss[] >-
  rw[field_nonzero_element] >>
  `x ** (n-1) IN R+ /\ |/x IN R+ /\ x IN R /\ |/ x IN R /\ |/ (x ** (n-1)) IN R` by rw[field_nonzero_element] >>
  `n = SUC(n - 1)` by decide_tac >>
  `x * |/ (x ** n) = x * |/ (x ** (n-1) * x)` by metis_tac[field_exp_suc] >>
  `_ = x * |/ x * |/ (x ** (n-1))` by rw_tac std_ss[field_inv_mult_comm, field_mult_assoc] >>
  rw_tac std_ss[field_mult_lone, field_mult_rinv]);

(* Theorem: x * ( |/ (x ** n) * y) = if n = 0 then x * y else |/ (x ** (n - 1)) * y *)
(* Proof: by field_single_mult_inv_exp. *)
val field_single_mult_inv_exp_assoc = store_thm(
  "field_single_mult_inv_exp_assoc",
  ``!r:'a field. Field r ==> !x y. x IN R+ /\ y IN R ==>
   !n. x * ( |/ (x ** n) * y) = if n = 0 then x * y else |/ (x ** (n - 1)) * y``,
  rpt strip_tac >>
  `x * ( |/ (x ** n) * y) = x * |/ (x ** n) * y` by rw[field_mult_assoc, field_nonzero_element] >>
  rw_tac std_ss[field_single_mult_inv_exp]);

(* ------------------------------------------------------------------------- *)
(* Field Division Theorems.                                                  *)
(* ------------------------------------------------------------------------- *)
(* val field_div_def = Define `field_div (r:'a field) x y = x * ( |/ y)`; -- has problem with Holmake, |/ is OK, but * = g.op *)
val field_div_def = Define `field_div (r:'a field) x y = (r.prod.op x ( |/ y))`; (* Somehow Holmake takes '*' as g.op here *)
val _ = overload_on("/", ``field_div r``);
val _ = set_fixity "/" (Infixl 600);
(* consistent with real and integer theories *)

(* export simple theorem *)
val _ = export_rewrites ["field_div_def"];

(* Theorem: x / y IN R *)
(* Proof: by definition. *)
val field_div_element = store_thm(
  "field_div_element",
  ``!r:'a field. Field r ==> !x y. x IN R /\ y IN R+ ==> x / y IN R``,
  rw_tac std_ss[field_div_def, field_inv_element, field_mult_element]);

(* Theorem: x / y IN R+ *)
(* Proof: by definition. *)
val field_div_nonzero = store_thm(
  "field_div_nonzero",
  ``!r:'a field. Field r ==> !x y. x IN R+ /\ y IN R+ ==> x / y IN R+``,
  rw_tac std_ss[field_div_def, field_inv_nonzero, field_mult_nonzero]);

val _ = export_rewrites ["field_div_element", "field_div_nonzero"];

(* Theorem: - x / y = - (x / y) *)
(* Proof:
   - x / y = - x * |/ y      by field_div_def
            = - (x * |/ y)   by field_mult_lneg
            = - (x / y)      by field_div_def
*)
val field_div_lneg = store_thm(
  "field_div_lneg",
  ``!r:'a field. Field r ==> !x y. x IN R /\ y IN R+ ==> (- x / y = - (x / y))``,
  rw_tac std_ss[field_div_def, field_mult_lneg, field_inv_element]);

(* Theorem:  x / - y = - (x / y) *)
(* Proof:
   x / - y = x * |/ - y      by field_div_def
            = x * - ( |/ y)  by field_inv_neg
            = - (x * |/ y)   by field_mult_rneg
            = - (x / y)      by field_div_def
*)
val field_div_rneg = store_thm(
  "field_div_rneg",
  ``!r:'a field. Field r ==> !x y. x IN R /\ y IN R+ ==> (x / - y = - (x / y))``,
  rw_tac std_ss[field_div_def, field_mult_rneg, field_inv_neg, field_inv_element]);

val _ = export_rewrites ["field_div_lneg", "field_div_rneg"];

(* Theorem:  - (x / y) = x / - y and  - (x / y) = - x / y *)
(* Proof: by field_div_lneg and field_div_rneg. *)
val field_neg_div = store_thm(
  "field_neg_div",
  ``!r:'a field. Field r ==> !x y. x IN R /\ y IN R+ ==> ((- (x / y) = - x / y) /\ (- (x / y) = x / - y))``,
  rw_tac std_ss[field_div_lneg, field_div_rneg]);

(* Theorem: x + y / z = (x * z + y) / z *)
(* Proof:
     x + (y / z)
   = x + y * |/ z                by field_div_def
   = |/ z * (z * x) + y * |/ z   by field_mult_linv_assoc
   = (x * z) * |/z + y * |/ z    by field_mult_comm
   = (x * z + y) * |/ z          by field_mult_ladd
   = (x * z + y) / z             by field_div_def
*)
val field_div_ladd = store_thm(
  "field_div_ladd",
  ``!r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==> (x + y / z = (x * z + y) / z)``,
  rpt strip_tac >>
  `|/ z IN R+ /\ z IN R /\ |/ z IN R` by rw[field_nonzero_element] >>
  `x + (y / z) =  |/ z * (z * x) + y * |/ z` by metis_tac[field_mult_linv_assoc, field_div_def] >>
  rw_tac std_ss[field_div_def, field_mult_ladd, field_mult_comm, field_mult_element]);

(* Theorem: y / z + x = (y + x * z) / z *)
(* Proof:
     y / z + x
   = x + y / z         by field_add_comm
   = (x * z + y) / z   by field_div_ladd
   = (y + x * z) / z   by field_add_comm
*)
val field_div_radd = store_thm(
  "field_div_radd",
  ``!r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==> (y / z + x = (y + x * z) / z)``,
  rpt strip_tac >>
  `|/ z IN R+ /\ z IN R /\ |/ z IN R` by rw[field_nonzero_element] >>
  rw[field_div_ladd, field_add_comm]);

(* Theorem: x - y / z = (x * z - y) / z *)
(* Proof:
   x - y / z = x + (- (y / z))     by field_sub_def
             = x + (- y /z)        by field_div_lneg
             = (x * z + - y) / z   by field_div_ladd
             = (x * z - y) / z     by field_sub_def
*)
val field_div_lsub = store_thm(
  "field_div_lsub",
  ``!r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==> (x - y / z = (x * z - y) / z)``,
  rpt strip_tac >>
  `|/ z IN R+ /\ z IN R /\ |/ z IN R /\ -y IN R` by rw[field_nonzero_element] >>
  `x - y / z = x + (- y /z)` by rw_tac std_ss[field_div_lneg, field_sub_def] >>
  rw_tac std_ss[field_div_ladd, field_sub_def]);

(* Theorem:  y / z - x = (y - x * z) / z *)
(* Proof:
   y / z - x = y / z + - x           by field_sub_def
             = (y + - x * z)  /z     by field_div_radd
             = (y + - (x * z)) / z   by field_mult_lneg
             = (y - x * z) / z       by field_sub_def
*)
val field_div_rsub = store_thm(
  "field_div_rsub",
  ``!r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==> (y / z - x = (y - x * z) / z)``,
  rw_tac std_ss[field_div_radd, field_mult_lneg, field_sub_def,
    field_inv_nonzero, field_nonzero_element, field_neg_element]);

(* Theorem: x * (y / z) = x * y / z *)
(* Proof:
     x * (y / z)
   = x * (y * |/ z)  by field_div_def
   = (x * y) * |/ z  by field_mult_assoc
   = x * y / z       by field_div_def
*)
val field_div_lmult = store_thm(
  "field_div_lmult",
  ``!r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==> (x * (y / z) = x * y / z)``,
  rw_tac std_ss[field_div_def, field_mult_assoc, field_inv_element]);

(* Theorem: (y / z) * x = y * x / z *)
(* Proof:
     (y / z) * x
   = (y * |/ z) * x   by field_div_def
   = y * ( |/ z * x)  by field_mult_assoc
   = y * (x * |/ z)   by field_mult_comm
   = (y * x) * |/ z   by field_mult_assoc
   = (y * x) / z      by field_div_def
*)
val field_div_rmult = store_thm(
  "field_div_rmult",
  ``!r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==> ((y / z) * x = y * x / z)``,
  rw_tac std_ss[field_div_def, field_mult_comm, field_mult_assoc, field_inv_nonzero, field_nonzero_element]);

(* Theorem: (x / y) ** n = x ** n / y ** n *)
(* Proof:
     (x / y) ** n
   = (x * |/ y) ** n        by field_div_def
   = x ** n * ( |/ y) ** n  by field_mult_exp
   = x ** n * |/ (y ** n)   by field_inv_exp
   = x ** n / y ** n        by field_div_def
*)
val field_div_exp = store_thm(
  "field_div_exp",
  ``!r:'a field. Field r ==> !x y. x IN R /\ y IN R+ ==> !n. (x / y) ** n = x ** n / y ** n``,
  rw_tac std_ss[field_mult_exp, field_inv_exp, field_div_def, field_inv_nonzero, field_nonzero_element]);

(* Theorem: x / y / z = x / (y * z) *)
(* Proof:
     x / y / z
   = (x * |/ y) * |/ z   by field_div_def
   = x * ( |/ y * |/ z)  by field_mult_assoc
   = x * |/ (y * z)      by field_inv_mult
   = x / (y * z)         by field_div_def
*)
val field_div_ldiv = store_thm(
  "field_div_ldiv",
  ``!r:'a field. Field r ==> !x y z. x IN R /\ y IN R+ /\ z IN R+ ==> (x / y / z = x / (y * z))``,
  rw_tac std_ss[field_inv_mult, field_mult_assoc, field_div_def, field_inv_nonzero, field_nonzero_element]);

(* Theorem: x / (y / z) = (x * z) / y *)
(* Proof:
     x / (y / z)
   = x * |/ (y * |/ z)      by field_div_def
   = x * ( |/ y * |/ |/ z)  by field_inv_mult
   = x * ( |/ y * z)        by field_inv_inv
   = x * |z * |/ y)         by field_mult_comm
   = (x * z) * |/ y         by field_mult_assoc
   = (x * z) / y            by field_div_def
*)
val field_div_rdiv = store_thm(
  "field_div_rdiv",
  ``!r:'a field. Field r ==> !x y z. x IN R /\ y IN R+ /\ z IN R+ ==> (x / (y / z) = (x * z) / y)``,
  rw_tac std_ss[field_inv_mult, field_inv_inv, field_mult_comm, field_mult_assoc,
    field_div_def, field_inv_nonzero, field_nonzero_element]);

(* Theorem: y / z + x = (y + z * x) / z *)
(* Proof:
     y / z + x
   = x + y / z         by field_add_comm
   = (x * z + y) / z   by field_div_ladd
   = (y + x * z) / z   by field_add_comm
   = (y + z * x) / z   by field_mult_comm
*)
val field_add_ldiv = store_thm(
  "field_add_ldiv",
  ``!r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==> (y / z + x = (y + z * x) / z)``,
  rw_tac std_ss[field_div_ladd, field_add_comm, field_mult_comm, field_mult_element,
    field_div_element, field_inv_nonzero, field_nonzero_element]);

(* Theorem: y / z + (x + t) = (y + z * x) / z + t *)
(* Proof:
     y / z + (x + t)
   = (y / z + x) + t       by field_add_assoc
   = (y + z * x) / z + t   by field_add_ldiv
*)
val field_add_ldiv_assoc = store_thm(
  "field_add_ldiv_assoc",
  ``!r:'a field. Field r ==> !x y t z. x IN R /\ y IN R /\ t IN R /\ z IN R+ ==> (y / z + (x + t) = (y + z * x) / z + t)``,
  rpt strip_tac >>
  `y / z + (x + t) = (y / z + x) + t` by rw[field_add_assoc] >>
  rw_tac std_ss[field_add_ldiv]);

(* Theorem: x + y / z = (z * x + y) / z *)
(* Proof:
     x + y / z
   = y / z + x        by field_add_comm
   = (y + x * z) / z  by field_div_radd
   = (x * z + y) / z  by field_add_comm
   = (z * x + y) / z  by field_mult_comm
*)
val field_add_rdiv = store_thm(
  "field_add_rdiv",
  ``!r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==> (x + y / z = (z * x + y) / z)``,
  rpt strip_tac >>
  `|/ z IN R+ /\ z IN R /\ |/ z IN R /\ y / z IN R /\ x * z IN R` by rw[field_nonzero_element] >>
  `x + y / z = y / z + x` by rw_tac std_ss[field_add_comm] >>
  rw_tac std_ss[field_div_radd, field_add_comm, field_mult_comm]);

(* Theorem: x + (y / z + t) = (z * x + y) / z + t *)
(* Proof:
     x + (y / z + t)
   = (x + y / z) + t      by field_add_assoc
   = (z * x + y) / z + t  by field_add_rdiv
*)
val field_add_rdiv_assoc = store_thm(
  "field_add_rdiv_assoc",
  ``!r:'a field. Field r ==> !x y t z. x IN R /\ y IN R /\ t IN R /\ z IN R+ ==> (x + (y / z + t) = (z * x + y) / z + t)``,
  rpt strip_tac >>
  `x + (y / z + t) = (x + y / z) + t` by rw[field_add_assoc] >>
  rw_tac std_ss[field_add_rdiv]);

(* Theorem: (x / y) * y = x *)
(* Proof:
     (x / y) * y
   = (x * |/ y) * y  by field_div_def
   = x * ( |/y * y)  by field_mult_assoc
   = x * #1          by field_mult_linv
   = x               by field_mult_rone
*)
val field_div_mult_cancel = store_thm(
  "field_div_mult_cancel",
  ``!r:'a field. Field r ==> !x y. x IN R /\ y IN R+ ==> ((x / y) * y = x)``,
  rw_tac std_ss[field_mult_linv, field_mult_rone, field_mult_assoc, field_div_def, field_inv_nonzero, field_nonzero_element]);

(* Theorem: x / z + y / z = (x + y) / z *)
(* Proof:
     x / z + y / z
   = ((x / z) * z + y) / z     by field_div_ladd
   = (x + y) / z               by field_div_mult_cancel
*)
val field_div_add_common = store_thm(
  "field_div_add_common",
  ``!r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==> (x / z + y / z = (x + y) / z)``,
  rw_tac std_ss[field_div_mult_cancel, field_div_ladd, field_div_element, field_inv_nonzero, field_nonzero_element]);

(* Theorem: v / (x * y) + w / (x * z) = (z * v + y * w) / (x * (y * z)) *)
(* Proof:
     v / (x * y) + w / (x * z)
   = v * |/ (x * y) + w * |/ (x * z)                               by field_div_def
   = v * |/ (x * y) * #1 + w * |/ (x * z) * #1                     by field_mult_rone
   = v * |/ (x * y) * ( |/ z * z) + w * |/ (x * z) * ( |/ y * y)   by field_mult_linv
   = v * ( |/ (x * y) * ( |/ z * z)) + w * ( |/ (x * z) * ( |/ y * y)) by field_mult_assoc
   = v * ( |/ (x * y) * |/ z * z) + w * ( |/ (x * z) * |/ y * y)   by field_mult_assoc
   = v * ( |/ (x * y * z) * z) + w * ( |/ (x * z * y) * y)         by field_inv_mult
   = v * (z * |/ (x * y * z)) + w * (y * |/ (x * z * y))           by field_mult_comm
   = v * z * |/ (x * y * z) + w * y * |/ (x * z * y)               by field_mult_assoc
   = v * z * |/ (x * (y * z)) + w * y * |/ (x * (z * y))           by field_mult_assoc
   = z * v * |/ (x * (y * z)) + y * w * |/ (x * (y * z))           by field_mult_comm
   = (z * v) / (x * (y * z)) + (y * w) / (x * (y * z))             by field_div_def
   = (z * v + y * w) / x * (y * z)                                 by field_div_add_common
*)
val field_add_div = store_thm(
  "field_add_div",
  ``!r:'a field. Field r ==> !v w x y z. v IN R /\ w IN R /\ x IN R+ /\ y IN R+ /\ z IN R+ ==>
                            (v / (x * y) + w / (x * z) = (z * v + y * w) / (x * (y * z)))``,
  rpt strip_tac >>
  `!t. t IN R+ ==> |/t IN R+ /\ t IN R /\ |/t IN R` by rw_tac std_ss[field_inv_nonzero, field_nonzero_element] >>
  `!p q. p IN R /\ q IN R ==> p * q IN R` by rw_tac std_ss[field_mult_element] >>
  `!p q. p IN R+ /\ q IN R+ ==> p * q IN R+` by rw_tac std_ss[field_mult_nonzero] >>
  `v / (x * y) + w / (x * z) = v * |/ (x * y) * #1 + w * |/ (x * z) * #1` by rw_tac std_ss[field_div_def, field_mult_rone] >>
  `_ = v * |/ (x * y) * ( |/ z * z) + w * |/ (x * z) * ( |/ y * y)` by rw_tac std_ss[field_mult_linv] >>
  `_ = v * ( |/ (x * y) * |/ z * z) + w * ( |/ (x * z) * |/ y * y)` by rw_tac std_ss[field_mult_assoc] >>
  `_ = v * (z * |/ (x * y * z)) + w * (y * |/ (x * z * y))` by rw_tac std_ss[field_inv_mult, field_mult_comm] >>
  `_ = v * z * |/ (x * (y * z)) + w * y * |/ (x * (z * y))` by rw_tac std_ss[field_mult_assoc] >>
  `_ = z * v * |/ (x * (y * z)) + y * w * |/ (x * (y * z))` by rw_tac std_ss[field_mult_comm] >>
  `_ = (z * v) / (x * (y * z)) + (y * w) / (x * (y * z))` by rw_tac std_ss[field_div_def] >>
  rw_tac std_ss[field_div_add_common]);

(* Theorem: v / (x * y) + (w / (x * z) + t) = (z * v + y * w) / (x * (y * z)) + t *)
(* Proof:
     v / (x * y) + (w / (x * z) + t)
   = (v / (x * y) + w / (x * z)) + t      by field_add_assoc
   = (z * v + y * w) / (x * (y * z)) + t  by field_add_div
*)
val field_add_div_assoc = store_thm(
  "field_add_div_assoc",
  ``!r:'a field. Field r ==> !v w t x y z. v IN R /\ w IN R /\ t IN R /\ x IN R+ /\ y IN R+ /\ z IN R+ ==>
                            (v / (x * y) + (w / (x * z) + t) = (z * v + y * w) / (x * (y * z)) + t)``,
  rpt strip_tac >>
  `v / (x * y) IN R /\ w / (x * z) IN R` by rw[] >>
  `v / (x * y) + (w / (x * z) + t) = (v / (x * y) + w / (x * z)) + t` by rw[field_add_assoc] >>
  rw_tac std_ss[field_add_div]);

(* Theorem: (x * y) / y = x *)
(* Proof:
     (x * y) / y
   = (x * y) * |/ y  by field_div_def
   = x * (y * |/y)   by field_mult_assoc
   = x * #1          by field_mult_rinv
   = x               by field_mult_rone
   or almost by group_rinv_assoc, but x in R, not R+, so make a case for x = #0.
*)
val field_mult_div_cancel = store_thm(
  "field_mult_div_cancel",
  ``!r:'a field. Field r ==> !x y. x IN R /\ y IN R+ ==> ((x * y) / y = x)``,
  rw[field_mult_assoc, field_nonzero_element]);

(* Theorem: (x * y) / (x * z) = y / z *)
(* Proof:
     (x * y) / (x * z)
   = (x * y) / x / z    by field_div_ldiv
   = (y * x) / x / z    by field_mult_comm
   = x / z              by field_mult_div_cancel
*)
val field_div_cancel = store_thm(
  "field_div_cancel",
  ``!r:'a field. Field r ==> !x y z. x IN R+ /\ y IN R /\ z IN R+ ==> ((x * y) / (x * z) = y / z)``,
  rpt strip_tac >>
  `x IN R /\ x * y IN R` by rw[field_nonzero_element] >>
  `(x * y) / (x * z) = (x * y) / x / z` by rw_tac std_ss[field_div_ldiv] >>
  `_ = (y * x) / x / z` by rw_tac std_ss[field_mult_comm] >>
  rw_tac std_ss[field_mult_div_cancel]);

(* Theorem: |/ x <> #0 *)
(* Proof: by field_inv_nonzero, field_nonzero_eq *)
val field_inv_not_zero = store_thm(
  "field_inv_not_zero",
  ``!r:'a field. Field r ==> !x. x IN R+ ==> |/ x <> #0``,
  metis_tac[field_nonzero_eq, field_inv_nonzero, field_nonzero_element]);

(* Theorem: (x / y = #0) <=> (x = #0) *)
(* Proof: by field_mult_eq_zero and field_inv_not_zero *)
val field_div_eq_zero = store_thm(
  "field_div_eq_zero",
  ``!r:'a field. Field r ==> !x y. x IN R /\ y IN R+ ==> ((x / y = #0) <=> (x = #0))``,
  rw_tac std_ss[EQ_IMP_THM] >-
  metis_tac[field_mult_eq_zero, field_inv_not_zero, field_inv_element, field_div_def] >>
  rw[]);

(* Theorem: Field r ==> !x. x IN R ==> (#0 rdivides x <=> (x = #0)) *)
(* Proof: by ring_zero_divides, field_is_ring *)
val field_zero_divides = store_thm(
  "field_zero_divides",
  ``!r:'a field. Field r ==> !x. x IN R ==> (#0 rdivides x <=> (x = #0))``,
  rw[ring_zero_divides]);

(* Theorem: Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==> (x = y * z <=> y = x / z) *)
(* Proof:
   Note z IN R /\ |/ z IN R    by field_nonzero_element, field_inv_element
   If part: x = y * z ==> y = x / z
      This is to show:
           y = (y * z) * |/ z  by field_div_def
        (y * z) * |/ z
      = y * (z * |/ z)         by field_mult_assoc
      = y * #1                 by field_mult_rinv
      = y                      by field_mult_rone
   Only-if part: y = x / z ==> x = y * z
      This is to show:
           x = (x * |/ z) * z  by field_div_def
        (x * |/ z) * z
      = x * ( |/ z * z)        by field_mult_assoc
      = x * #1                 by field_mult_linv
      = x                      by field_mult_rone

   Another method:
   By field_div_def, to show:
      x IN R /\ y IN R /\ z IN R+ ==> (x = y * z <=> y = x * |/ z)
   which is true               by field_mult_rinv_eqn, exchange y and z.
*)
Theorem field_mult_div_eqn:
  !r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==> (x = y * z <=> y = x / z)
Proof
  metis_tac[field_mult_rinv_eqn, field_div_def]
QED

(* Theorem: Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==> (x = z * y <=> y = x / z) *)
(* Proof:
   Note z IN R                 by field_nonzero_element
     so z * y = y * z          by field_mult_comm
   The result follows          by field_mult_div_eqn
*)
Theorem field_mult_div_comm:
  !r:'a field. Field r ==> !x y z. x IN R /\ y IN R /\ z IN R+ ==> (x = z * y <=> y = x / z)
Proof
  metis_tac[field_mult_div_eqn, field_nonzero_element, field_mult_comm]
QED

(* ------------------------------------------------------------------------- *)
(* Field and Integral Domain.                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: A Field is an Integral Domain: Field r ==> IntegralDomain r *)
(* Proof:
   By IntegralDomain_def, this is to show:
   (1) Field r ==> Ring r, true                   by field_is_ring
   (2) #1 <> #0, true                             by field_one_ne_zero
   (3) x * y = #0 <=> (x = #0) \/ (y = #0), true  by field_mult_eq_zero
*)
val field_is_integral_domain = store_thm(
  "field_is_integral_domain",
  ``!r:'a field. Field r ==> IntegralDomain r``,
  rw_tac std_ss[field_is_ring, field_one_ne_zero, field_mult_eq_zero, IntegralDomain_def]);

(* Theorem: Field r ==> !x. x IN R /\ x <> #0 ==>
            !m n. m < n /\ (x ** m = x ** n) ==> (x ** (n - m) = #1) *)
(* Proof: by integral_domain_exp_eq *)
val field_exp_eq = store_thm(
  "field_exp_eq",
  ``!r:'a field. Field r ==> !x. x IN R /\ x <> #0 ==>
   !m n. m < n /\ (x ** m = x ** n) ==> (x ** (n - m) = #1)``,
  rw_tac std_ss[field_is_integral_domain, integral_domain_exp_eq, field_nonzero_eq]);

(* Theorem: FiniteField r ==> FiniteIntegralDomain r *)
(* Proof: by finite_integral_domain_is_field, FiniteIntegralDomain_def, FiniteField_def *)
val finite_field_is_finite_integral_domain = store_thm(
  "finite_field_is_finite_integral_domain",
  ``!r:'a ring. FiniteField r ==> FiniteIntegralDomain r``,
  rw_tac std_ss[FiniteIntegralDomain_def, FiniteField_def, field_is_integral_domain]);

(* Theorem: A FINITE Integeral Domain is a Field: FiniteIntegralDomain r ==> Field r *)
(* Proof:
   Idea: in a FINITE Integral Domain,
         every nonzero element has an order,
         so nonzero elements are invertible.
   By Field_def, this is to show:
   (1) Ring r, true        by integral_domain_is_ring
   (2) Group f*, true      by finite_integral_domain_nonzero_group
*)
val finite_integral_domain_is_field = store_thm(
  "finite_integral_domain_is_field",
  ``!r:'a ring. FiniteIntegralDomain r ==> Field r``,
  rpt (stripDup[FiniteIntegralDomain_def]) >>
  rw_tac std_ss[Field_def, integral_domain_is_ring, finite_integral_domain_nonzero_group]);

(* Theorem: A FINITE Integeral Domain is a FINITE Field: FiniteIntegralDomain r ==> FiniteField r *)
(* Proof: by finite_integral_domain_is_field, FiniteIntegralDomain_def, FiniteField_def *)
val finite_integral_domain_is_finite_field = store_thm(
  "finite_integral_domain_is_finite_field",
  ``!r:'a ring. FiniteIntegralDomain r ==> FiniteField r``,
  rw_tac std_ss[finite_integral_domain_is_field, FiniteIntegralDomain_def, FiniteField_def]);

(* Theorem: FiniteIntegralDomain r = FiniteField r *)
(* Proof: by finite_integral_domain_is_finite_field, finite_field_is_finite_integral_domain *)
val finite_integral_domain_eq_finite_field = store_thm(
  "finite_integral_domain_eq_finite_field",
  ``!r:'a ring. FiniteIntegralDomain r = FiniteField r``,
  metis_tac[finite_integral_domain_is_finite_field, finite_field_is_finite_integral_domain]);

(* These are major results. *)

(* Next is a more convenient form of finite_integral_domain_is_finite_field *)

(* Theorem: FiniteRing r /\ #1 <> #0 /\
            (!x y. x IN R /\ y IN R /\ (x * y = #0) <=> (x = #0) \/ (y = #0)) ==> FiniteField r *)
(* Proof:
   This is a (commutative) ring with no zero divisors,
   so it is an integral domain            by IntegralDomain_def
   With FINITE R,
   it is also a finite integral domain    by FiniteIntegralDomain_def
   Thus it is a finite field              by finite_integral_domain_is_finite_field
*)
val finite_field_from_finite_ring = store_thm(
  "finite_field_from_finite_ring",
  ``!r:'a ring. FiniteRing r /\ #1 <> #0 /\
       (!x y. x IN R /\ y IN R ==> ((x * y = #0) <=> (x = #0) \/ (y = #0))) ==> FiniteField r``,
  rw_tac std_ss[FiniteRing_def] >>
  `FiniteIntegralDomain r` by metis_tac[FiniteIntegralDomain_def, IntegralDomain_def] >>
  rw[GSYM finite_integral_domain_is_finite_field]);

(* ------------------------------------------------------------------------- *)
(* Field Defintion without explicit mention of Ring.                         *)
(* ------------------------------------------------------------------------- *)

(* Field Definition:
   A Field is a set with elements of f of type 'a field, such that
   . r.sum is an Abelian group
   . r.prod is an Abelian group
   . r.sum.carrier is the whole set
   . r.prod.carrier is the set without the r.sum.id (the zero)
   . zero multiplies to zero (on the left)
   . multiplication distributes over addition (on the right)
*)
(* Proof:
   Using defintions, this is to prove:
   (1) Group f* /\ AbelianMonoid r.prod ==> AbelianGroup f*
       Group f*
       gives f* = R+   by excluding_def
       since !x. x IN R+ ==> x IN R       by field_nonzero_element
       hence !x y::R+. x * y = y * x      by AbelianMonoid_def
   (2) AbelianGroup r.sum /\ AbelianMonoid r.prod ==> !x::(R). zero * x = zero
       AbelianGroup r.sum
       gives Group r.sum,     by AbelianGroup_def
         and zero IN R        by group_id_element
       This also gives group_id_fix which is used later.
       AbelianMonoid r.prod
       gives Monoid r.prod
         and !x y::F. x * y = y * x       by AbelianMonoid_def
       Show: x * zero = zero, then result follows by commutativity.
         x * zero
       = x * (zero + zero)    by group_id_id
       = x * zero + x * zero  by distribution on right
       Hence x * zero = zero  by group_id_fix
   (3) AbelianGroup f* /\ (!x::(R). #0 * x = #0) ==> AbelianMonoid r.prod
       This is to show:
       1. Closure in r.prod by including zero: !x y::R+. x * y IN R, zero * y IN R, x * zero IN R.
       2. Identity in r.prod by including zero: zero * one = zero /\ one * zero = zero.
       3. Associativity in r.prod by including zero: !x y z::R+. x * y * z = x * (y * z), and when x or y or z = zero.
       4. Commutativity in r.prod by including zero: !x y::R+. x * y = y * x, and zero * y = y * zero, x * zero = zero * x.
       We are given: !x::F. zero * x = zero
       hence we need: !x::F. x * zero IN R and x * zero = zero.
       For x * zero IN R,
       note that zero = one + -one   by group_rinv  of Group r.sum
       hence x * zero = x * one + x * (-one)   by right distribution
       Since one IN R+, one IN R, and (-one) IN R by group_inv_element of Group r.sum
       But one <> zero, so the equality forces (-one) IN R+.
       If x = zero, zero * zero = zero, so x * zero IN R.
       If x <> zero, x IN R+, so x * one IN R+ and x * (-one) IN R+ by monoid_op_element of Monoid f*
       But then x * one IN R and x * (-one) IN R, so x * zero IN R  by group_op_element of Group r.sum
       Once x * zero IN R,
       we have:  x * zero = x * zero + x * zero    by group_id_id and distribution on right
       hence  x * zero = zero   by group_id_fix of Group r.sum.
       With these, the four conditions are proved by cases on x = zero.
   (4) AbelianGroup f* ==> Group f*
       This follows from AbelianGroup_def.
*)
val field_def_alt = store_thm(
  "field_def_alt",
  ``!r:'a field. Field r <=> AbelianGroup r.sum  /\
                          AbelianGroup f* /\
                          (r.sum.carrier = R) /\
                          (r.prod.carrier = R) /\
                          (!x. x IN R ==> (#0 * x = #0)) /\
                          (!x y z. x IN R /\ y IN R /\ z IN R ==> (x * (y + z) = (x * y) + (x * z)))``,
  rw_tac std_ss[Field_def, Ring_def, EQ_IMP_THM] >| [
    `f*.op = $*` by rw_tac std_ss[excluding_def] >>
    `!x. x IN F* ==> x IN R` by rw[excluding_def] >>
    metis_tac[AbelianGroup_def, AbelianMonoid_def],
    `Group r.sum /\ #0 IN R` by metis_tac[AbelianGroup_def, group_id_element] >>
    `Monoid r.prod /\ (!x y. x IN R /\ y IN R ==> (x * y = y * x))` by metis_tac[AbelianMonoid_def] >>
    metis_tac[group_id_fix, group_id_id, monoid_op_element],
    `f*.op = $*` by rw_tac std_ss[excluding_def] >>
    `f*.id = #1` by rw_tac std_ss[excluding_def] >>
    `F* = R+` by rw_tac std_ss[excluding_def, ring_nonzero_def] >>
    `Group f* /\ !x y. x IN R+ /\ y IN R+ ==> (x * y = y * x)` by metis_tac[AbelianGroup_def] >>
    `!x y z. x IN R+ /\ y IN R+ /\ z IN R+ ==> (x * y * z = x * (y * z))` by metis_tac[group_assoc] >>
    `!x. x IN R+ ==> (#1 * x = x) /\ (x * #1 = x)` by metis_tac[group_lid, group_rid] >>
    `Group r.sum /\ #0 IN R` by metis_tac[AbelianGroup_def, group_id_element] >>
    `!x. x IN R+ <=> x IN R /\ x <> #0` by rw_tac std_ss[ring_nonzero_eq] >>
    `#1 IN R` by metis_tac[group_id_element] >>
    `!x. x IN R ==> x * #0 IN R` by
  (rpt strip_tac >>
    Cases_on `x = #0` >-
    rw_tac std_ss[] >>
    `#0 = #1 + (- #1)` by metis_tac[group_rinv] >>
    `-#1 IN R+` by metis_tac[group_rid, group_inv_element] >>
    `x * #0 = x * #1 + x * (-#1)` by metis_tac[] >>
    metis_tac[group_op_element]
    ) >>
    `!x. x IN R ==> (x * #0 = #0)` by
    (rpt strip_tac >>
    metis_tac[group_id_fix, group_id_id]) >>
    `!x y. x IN R /\ y IN R ==> x * y IN R` by
      (rpt strip_tac >>
    Cases_on `(x = #0) \/ (y = #0)` >-
    metis_tac[] >>
    metis_tac[group_op_element]
    ) >>
    rw_tac std_ss[AbelianMonoid_def, Monoid_def] >| [
      Cases_on `(x = #0) \/ (y = #0) \/ (z = #0)` >-
      metis_tac[] >>
      `x IN R+ /\ y IN R+ /\ z IN R+` by metis_tac[] >>
      rw_tac std_ss[],
      Cases_on `x = #0` >-
      rw_tac std_ss[] >>
      rw_tac std_ss[],
      Cases_on `x = #0` >-
      rw_tac std_ss[] >>
      rw_tac std_ss[],
      Cases_on `(x = #0) \/ (y = #0)` >-
      metis_tac[] >>
      metis_tac[]
    ],
    metis_tac[AbelianGroup_def]
  ]);

(* Theorem: Field r <=> Ring r /\ #1 <> #0 /\ !x. x IN R /\ x <> #0 ==> ?y. y IN R /\ x * y = #1 *)
(* Proof: by definition, this is to show:
   (1) Group f* /\ x IN R /\ x <> #0 ==> ?y. y IN R /\ (x * y = #1)
       Since x IN r.prod excluding #0, inverse y exsists by Group f*.
   (2) #1 <> #0 /\ !x. x IN R /\ x <> #0 ==> ?y. y IN R /\ (x * y = #1) ==> Group f*
       Expanding by group definition, this is to show:
       (1) x IN R /\ y IN R ==> x * y IN R, true by ring_add_element
       (2) x IN R /\ x <> #0 /\ y IN R /\ y <> #0 /\ !x. x IN R /\ x <> #0 ==> ?y. y IN R /\ (x * y = #1) ==> x * y <> #0
           Since x IN R /\ x <> #0,
           ?z. z IN R /\ x * z = #1    by given.
           Assume x * y = #0, then
           z * (x * y) = z * #0 = #0   by ring_mult_rzero
           (z * x) * y = #0            by ring_mult_assoc
                #1 * y = #0            by ring_mult_comm
                     y = #0            by ring_mult_lone
           which contradicts y <> #0.
       (3) x IN R /\ y IN R /\ z IN R ==> x * y * z = x * (y * z), true by ring_mult_assoc.
       (4) #1 IN R, true by ring_one_element
       (5) x IN R ==> #1 * x = x, true by ring_mult_lone.
       (6) x IN R /\ x <> #0 /\ !x. x IN R /\ x <> #0 ==> ?y. y IN R /\ (x * y = #1) ==> ?y. (y IN R /\ y <> #0) /\ (y * x = #1)
*)
val field_def_by_inv = store_thm(
  "field_def_by_inv",
  ``!r:'a ring. Field r <=> Ring r /\ #1 <> #0 /\ !x. x IN R /\ x <> #0 ==> ?y. y IN R /\ (x * y = #1)``,
  rw[Field_def, EQ_IMP_THM] >| [
    `x IN F*` by rw[ring_mult_monoid, excluding_def] >>
    `f*.inv x IN F*` by rw[group_inv_element] >>
    `x * (f*.inv x) = #1` by metis_tac[group_excluding_property, group_rinv] >>
    `!z. z IN F* ==> z IN r.prod.carrier` by rw[excluding_def] >>
    metis_tac[ring_mult_monoid],
    rw_tac std_ss[group_def_alt, excluding_def, IN_DIFF, IN_SING, ring_mult_monoid] >| [
      rw[],
      `?z. z IN R /\ (z * x = #1)` by metis_tac[ring_mult_comm] >>
      `z * (x * y) = (z * x) * y` by rw[ring_mult_assoc] >>
      `_ = y` by rw[] >>
      metis_tac[ring_mult_rzero],
      rw[ring_mult_assoc],
      rw[],
      rw[],
      metis_tac[ring_mult_comm, ring_mult_lzero]
    ]
  ]);

(* ------------------------------------------------------------------------- *)
(* A Ring can be a Field if the Units group is large enough.                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ring units is a field -- this is wrong:
   Z(n) is a ring, for any n.
   Units(Z(n)) = Euler(n) is a multiplicative group, with |Units(Z(n))| = phi(n), for any n.
   but there is no field F(n) for any n, or phi(n).
   Only Z(p) is a field, because it is a ring with no zero divisors,
   or Units(Z(p)).carrier = Z_star(p).

   For the case of Z_6, it is just that there are two groups:
   Z_6+ and Euler_6, with different ops and different sizes.
   The two ops cannot distribute, so there is no "Ring".

   Every ring has an additive group, by definition.
   Every ring has a multiplicative monoid, by definition.
   Every ring has a (possibly smaller) multiplicative group, the units.
   When the units includes all non-zero elements of the ring, the ring is a field.
*)

(* Define the field of units of a ring. *)
val field_units_def = Define`
  field_units (r:'a ring) : 'a field =
    <| carrier := R;
           sum := r.sum;
          prod := r* including #0
     |>
`;
(*
- type_of ``field_units r``;
> val it = ``:'a field`` : hol_type
*)

(* Theorem: If R* = R+ and #0 <> #1, then r* is a field. *)
(* Proof: by definitions.
   1. Ring (field_units r)
      Since #0 IN R              by ring_zero_element
      hence R+ UNION {#0} = R    by UNION_DIFF, ring_nonzero_def
      By including_def, Invertibles_def:
      (r* including #0).carrier = r.prod.carrier = R
      (r* including #0).id = r.prod.id = #1
      (r* including #0).op = r.prod.op
      By field_units_def:
      (field_units r).carrier = r.carrier
      (field_units r).sum = r.sum
      (field_units r).prod = r* including #0
      Hence Ring r <=> Ring (field_units r)        by ring_equal = ring_component_equality, monoid_component_equality
   2. Group ((field_units r).prod excluding (field_units r).sum.id)
      or: Group (r* including #0 excluding #0)     by field_units_def
      But Ring r ==> Monoid r.prod                 by ring_mult_monoid
                 ==> Group r*          by monoid_invertibles_is_group
      Now #0 NOTIN R*                  by ring_units_has_zero, but #0 <> #1
      Hence Group (r* including #0 excluding #0)  by group_including_excluding_group.
*)
val field_units_is_field = store_thm(
  "field_units_is_field",
  ``!r:'a ring. Ring r /\ (R* = R+ ) /\ #0 <> #1 ==> Field (field_units r)``,
  rw_tac std_ss[Field_def] >| [
    `R+ UNION {r.sum.id} = R` by rw[UNION_DIFF, ring_nonzero_def] >>
    `(r* including #0).carrier = r.prod.carrier` by rw_tac std_ss[including_def, Invertibles_def, ring_mult_monoid] >>
    `(r* including #0).op = r.prod.op` by rw_tac std_ss[including_def, Invertibles_def] >>
    `(r* including #0).id = #1` by rw_tac std_ss[including_def, Invertibles_def] >>
    `(field_units r).carrier = r.carrier` by rw_tac std_ss[field_units_def] >>
    `(field_units r).sum = r.sum` by rw_tac std_ss[field_units_def] >>
    `(field_units r).prod = r* including #0` by rw_tac std_ss[field_units_def] >>
    metis_tac[ring_component_equality, monoid_component_equality],
    rw_tac std_ss[field_units_def] >>
    `#0 NOTIN R*` by metis_tac[ring_units_has_zero] >>
    `Group r*` by rw_tac std_ss[ring_mult_monoid, monoid_invertibles_is_group] >>
    rw_tac std_ss[GSYM group_including_excluding_group]
  ]);

(* Theorem: Field r ==> R* = R+ *)
(* Proof:
   R* = (Invertibles r.prod).carrier   by overload
   Hence true by field_nonzero_unit
*)
val field_units_nonzero = store_thm(
  "field_units_nonzero",
  ``!r:'a field. Field r ==> (R* = R+)``,
  rw[field_nonzero_unit, EXTENSION]);

(* Theore m: Field r ==> (R* = F* ) *)
(* Proof:
   By EXTENSION,
       x IN R*         by notation, unit x
   <=> x IN R+         by field_nonzero_unit
   <=> x IN F*         by field_mult_carrier
*)
Theorem field_units_eq:
  !r:'a field. Field r ==> (R* = F* )
Proof
  metis_tac[EXTENSION, field_nonzero_unit, field_mult_carrier]
QED

(* Theorem: Field r ==> !x. unit x ==> unit ( |/ x) *)
(* Proof: by ring_unit_has_inv, field_is_ring. *)
val field_unit_has_inv = store_thm(
  "field_unit_has_inv",
  ``!r:'a field. Field r ==> !x. unit x ==> unit ( |/ x)``,
  rw[ring_unit_has_inv]);

(* Theorem: Field r ==> !n. Group (roots_of_unity f* n *)
(* Proof:
   Field r ==> AbelianGroup f*               by field_nonzero_mult_is_abelian_group
           ==> Group (roots_of_unity f* n)   by group_uroots_group
*)
val field_uroots_is_group = store_thm(
  "field_uroots_is_group",
  ``!r:'a field. Field r ==> !n. Group (roots_of_unity f* n)``,
  rw[field_nonzero_mult_is_abelian_group, group_uroots_group]);

(* ------------------------------------------------------------------------- *)
(* Field Characteristic.                                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r ==> (char r = 0) \/ prime (char r) *)
(* Proof: by integral_domain_char. *)
val field_char = store_thm(
  "field_char",
  ``!r:'a ring. Field r ==> (char r = 0) \/ prime (char r)``,
  rw_tac std_ss[field_is_integral_domain, integral_domain_char]);

(* Theorem: Field r /\ 0 < char r ==> prime (char r) *)
(* Proof: by field_char. *)
val field_char_prime = store_thm(
  "field_char_prime",
  ``!r:'a field. Field r /\ 0 < char r ==> prime (char r)``,
  metis_tac[field_char, NOT_ZERO_LT_ZERO]);

(* Theorem: Field r /\ (char r = 0) ==> INFINITE R *)
(* Proof: field_is_ring, ring_char_0 *)
val field_char_0 = store_thm(
  "field_char_0",
  ``!r:'a field. Field r /\ (char r = 0) ==> INFINITE R``,
  rw[ring_char_0]);

(* Theorem: Field r ==> char r <> 1 *)
(* Proof:
   Note Field r ==> Ring r    by field_is_ring
   By contradiction, suppose char r = 1.
   Then R = {#0}              by ring_char_1
    ==> #1 = #0               by ring_one_eq_zero
   This contradicts #1 <> #0  by field_one_ne_zero
*)
val field_char_ne_1 = store_thm(
  "field_char_ne_1",
  ``!r:'a field. Field r ==> char r <> 1``,
  metis_tac[field_is_ring, field_one_ne_zero, ring_char_1, ring_one_eq_zero]);

(* Note: in fact:
finite_field_char |- !r. FiniteField r ==> prime (char r)
*)

(* Theorem: Field r /\ (char r = 2) ==> !x. x IN R ==> (-x = x) *)
(* Proof: by ring_neg_char_2 *)
val field_neg_char_2 = store_thm(
  "field_neg_char_2",
  ``!r:'a field. Field r /\ (char r = 2) ==> !x. x IN R ==> (-x = x)``,
  rw[ring_neg_char_2]);

(* Theorem: Field r ==> !n. 0 < n ==> ((char r = n) <=> (##n = #0) /\ !m. 0 < m /\ m < n ==> ##m <> #0) *)
val field_char_alt = lift_ring_thm "char_alt";
(* > val field_char_alt = |- !r. Field r ==> !n. 0 < n ==>
        ((char r = n) <=> (##n = #0) /\ !m. 0 < m /\ m < n ==> ##m <> #0): thm *)

(* Theorem: Field r /\ 0 < char r ==> (##(char r) = #0) /\ !n. 0 < n /\ n < char r ==> ##n <> #0 *)
(* Proof: by field_char_alt *)
val field_char_eqn = store_thm(
  "field_char_eqn",
  ``!r:'a field. Field r /\ 0 < char r ==> (##(char r) = #0) /\ !n. 0 < n /\ n < char r ==> ##n <> #0``,
  metis_tac[field_char_alt]);

(* Theorem: Field r ==> ((-#1 = #1) <=> (char r = 2)) *)
(* Proof: by ring_neg_one_eq_one, field_one_ne_zero *)
val field_neg_one_eq_one = store_thm(
  "field_neg_one_eq_one",
  ``!r:'a field. Field r ==> ((-#1 = #1) <=> (char r = 2))``,
  rw[ring_neg_one_eq_one]);

(* Theorem: Field r ==> !x. x IN R ==> !n. r.sum.exp x n = x * ##n *)
(* Proof: by field_is_ring, ring_add_exp_eqn *)
val field_add_exp_eqn = store_thm(
  "field_add_exp_eqn",
  ``!r:'a field. Field r ==> !x. x IN R ==> !n. r.sum.exp x n = x * ##n``,
  rw_tac std_ss[field_is_ring, ring_add_exp_eqn]);

(* Theorem: Field r /\ 0 < char r ==> !x. x IN R+ ==> (order r.sum x = char r) *)
(* Proof:
   Let c = char r, then 0 < c.
   Note x IN R /\ x <> #0  by field_nonzero_eq

   By group_order_thm, this is to show:
   (1) r.sum.exp x c = #0
         r.sum.exp x c
       = x * ##c           by field_add_exp_eqn
       = x * #0            by char_property
       = #0                by field_mult_rzero
   (2) !m. 0 < m /\ m < c ==> r.sum.exp x m <> #0
       By contradiction, suppose r.sum.exp x m = #0
       Then r.sum.exp x m
          = x * ##m = #0                   by field_add_exp_eqn
         or     ##m = #0                   by field_mult_eq_zero, field_num_element
       But 0 < m /\ m < c ==> ##m <> #0    by field_char_alt
       Thus this is a contradiction.
*)
val field_add_order = store_thm(
  "field_add_order",
  ``!r:'a field. Field r /\ 0 < char r ==> !x. x IN R+ ==> (order r.sum x = char r)``,
  rpt strip_tac >>
  qabbrev_tac `c = char r` >>
  `x IN R /\ x <> #0` by metis_tac[field_nonzero_eq] >>
  `Group r.sum` by rw[field_add_group] >>
  `(r.sum.exp x c = #0) /\ !m. 0 < m /\ m < c ==> r.sum.exp x m <> #0` suffices_by rw[group_order_thm] >>
  rpt strip_tac >-
  metis_tac[field_add_exp_eqn, char_property, field_mult_rzero] >>
  metis_tac[field_add_exp_eqn, field_mult_eq_zero, field_num_element, field_char_alt]);

(* Theorem: Field r ==> !n m. n < char r /\ m < char r ==> (##n = ##m <=> (n = m)) *)
(* Proof: by ring_num_eq. *)
val field_num_eq = store_thm(
  "field_num_eq",
  ``!r:'a field. Field r ==> !n m. n < char r /\ m < char r ==> ((##n = ##m) <=> (n = m))``,
  rw[ring_num_eq]);

(* Theorem: Field r /\ 0 < char r ==> !n. ##n = ##(n MOD (char r)) *)
(* Proof: by ring_num_mod. *)
val field_num_mod = store_thm(
  "field_num_mod",
  ``!r:'a field. Field r /\ 0 < char r ==> !n. ##n = ##(n MOD (char r))``,
  rw[Once ring_num_mod]);

(* Theorem: Field r /\ 0 < char r ==> !z. ?y x. (y = ##x) /\ (y + ##z = #0) *)
(* Proof: by ring_num_negative *)
val field_num_negative = store_thm(
  "field_num_negative",
  ``!r:'a field. Field r /\ 0 < char r ==>
   !z. ?y x. (y = ##x) /\ (y + ##z = #0)``,
  rw[ring_num_negative]);

(* Theorem: Field r /\ 0 < char r ==>
   !z. ##z <> #0 ==> ?y. ((?x. (y = ##x) /\ x IN univ(:num)) /\ y <> #0) /\ (y * ##z = #1) *)
(* Proof:
   For p = char r, then prime p                    by field_char_prime, 0 < char r
   z = z DIV p * p + z MOD p  with z MOD p < p     by DIVISION
   ##z = ##(z DIV p * p + z MOD p)
       = ##(z DIV p * p) + ##(z MOD p)             by field_num_add
       = ##(z DIV p) * ##p + ##(z MOD p)           by field_num_mult
       = ##(z DIV p) * #0  + ##(z MOD p)           by char_property
       = #0 + ##(z MOD p)                          by field_mult_rzero
       = ##(z MOD p)                               by field_add_lzero
   Let u = z MOD p < p, then by MOD_MULT_INV_EXISTS,
   prime p /\ 0 < u /\ u < p ==> ?v. 0 < v /\ v < p /\ ((v * u) MOD p = 1)
   Let y = ##v, x = v, then
   y * ##z = ##v * ##u           since u = z MOD p, and ##z = ##(z MOD p)
           = ##(v * u)           by field_num_mult
           = ##(v * u) MOD p     by finite_field_num_mod
           = ##1
*)
val field_num_inverse = store_thm(
  "field_num_inverse",
  ``!r:'a field. Field r /\ 0 < char r ==>
   !z. ##z <> #0 ==> ?y x. (y = ##x) /\ y <> #0 /\ (y * ##z = #1)``,
  rpt strip_tac >>
  qabbrev_tac `p = char r` >>
  `prime p` by rw[field_char_prime, Abbr`p`] >>
  `##z = ##(z MOD p)` by metis_tac[field_num_mod] >>
  qabbrev_tac `u = z MOD p` >>
  `u <> 0` by metis_tac[field_num_0] >>
  `0 < u` by decide_tac >>
  `?v. 0 < v /\ v < p /\ ((v * u) MOD p = 1)` by rw[MOD_MULT_INV_EXISTS, Abbr`u`] >>
  qexists_tac `##v` >>
  `#1 = ##((v MOD p * u MOD p) MOD p)` by rw[MOD_TIMES2] >>
  `_ = ##(v MOD p * u MOD p)` by metis_tac[field_num_mod] >>
  `_ = ##(v MOD p) * ## (u MOD p)` by rw[field_num_mult] >>
  `_ = ##v * ##u` by metis_tac[field_num_mod] >>
  `#1 <> #0` by rw[] >>
  metis_tac[field_mult_eq_zero, field_num_element]);

(* ------------------------------------------------------------------------- *)
(* Finite Field.                                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==> prime (char r) *)
(* Proof:
   FiniteField r ==> FiniteRing r   by field_is_ring and definitions
   hence 0 < char r                 by finite_ring_char_pos
   or char r <> 0.
   Now FiniteField r ==> Field r    by finite_field_is_field
   The result then follows from field_char.
*)
val finite_field_char = store_thm(
  "finite_field_char",
  ``!r:'a ring. FiniteField r ==> prime (char r)``,
  rpt strip_tac >>
  `FiniteRing r` by metis_tac[FiniteField_def, field_is_ring, FiniteRing_def] >>
  `0 < char r` by rw_tac std_ss[finite_ring_char_pos] >>
  `char r <> 0` by decide_tac >>
  metis_tac[finite_field_is_field, field_char]);

(* Theorem: FiniteField r ==> 0 < char r *)
(* Proof:
   Note prime (char r)        by finite_field_char
     so 0 < char r            by PRIME_POS
*)
val finite_field_char_pos = store_thm(
  "finite_field_char_pos",
  ``!r:'a field. FiniteField r ==> 0 < char r``,
  rw_tac std_ss[finite_field_char, PRIME_POS]);

(* Theorem: FiniteField r ==> 1 < char r *)
(* Proof:
   Note prime (char r)        by finite_field_char
     so 1 < char r            by ONE_LT_PRIME
*)
val finite_field_char_gt_1 = store_thm(
  "finite_field_char_gt_1",
  ``!r:'a field. FiniteField r ==> 1 < char r``,
  rw_tac std_ss[finite_field_char, ONE_LT_PRIME]);

(* Theorem: FiniteField r ==> 1 < CARD R *)
(* Proof:
   Since FiniteField r ==> Field r /\ FINITE R    by FiniteField_def
     and #1 IN R                                  by field_one_element
     and #0 IN R                                  by field_zero_element
     and #1 <> #0                                 by field_one_ne_zero
   Hence CARD R <> 0                              by CARD_EQ_0, MEMBER_NOT_EMPTY
     and CARD R <> 1                              by finite_ring_card_eq_1
      so 1 < CARD R
*)
val finite_field_card_gt_1 = store_thm(
  "finite_field_card_gt_1",
  ``!r:'a field. FiniteField r ==> 1 < CARD R``,
  rw[FiniteField_def] >>
  `Ring r /\ #1 IN R /\ #0 IN R /\ #1 <> #0` by rw[] >>
  `CARD R <> 0` by metis_tac[CARD_EQ_0, MEMBER_NOT_EMPTY] >>
  `CARD R <> 1` by metis_tac[finite_ring_card_eq_1, FiniteRing_def] >>
  decide_tac);

(* Theorem: FiniteField r ==> 0 < CARD R *)
(* Proof:
   Since 1 < CARD R   by finite_field_card_gt_1
   The result follows by 0 < 1.
*)
val finite_field_card_pos = store_thm(
  "finite_field_card_pos",
  ``!r:'a field. FiniteField r ==> 0 < CARD R``,
  metis_tac[finite_field_card_gt_1, DECIDE``!n. 1 < n ==> 0 < n``]);

(* Theorem: FiniteField r /\ prime (CARD R) ==> (char r = CARD R) *)
(* Proof: by finite_field_is_finite_ring, finite_ring_card_prime *)
val finite_field_card_prime = store_thm(
  "finite_field_card_prime",
  ``!r:'a field. FiniteField r /\ prime (CARD R) ==> (char r = CARD R)``,
  rw_tac std_ss[finite_field_is_finite_ring, finite_ring_card_prime]);

(* ------------------------------------------------------------------------- *)
(* Properties from Finite Group.                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteField r ==> !x. x IN R+ ==> x ** (CARD R+) = |1| *)
(* Proof:
   FiniteField r ==> Field r /\ FINITE R     by FiniteField_def
   and     Field r ==> Group f*              by field_mult_group
   with    F* = R+                           by field_mult_carrier
   Now     R+ SUBSET R                       by field_nonzero_eq, SUBSET_DEF
   Hence   FINITE R+                         by SUBSET_FINITE
   Thus    FiniteGroup f*                    by FiniteGroup_def
   Giving  f*.exp x (CARD F* ) = f*.id       by finite_group_Fermat
       or  x ** (CARD R+) = #1               by field_nonzero_mult_property
*)
val finite_field_Fermat = store_thm(
  "finite_field_Fermat",
  ``!r:'a field. FiniteField r ==> !x. x IN R+ ==> (x ** CARD R+ = #1)``,
  rpt strip_tac >>
  `Field r /\ FINITE R` by metis_tac[FiniteField_def] >>
  `Group f*` by rw[field_mult_group] >>
  `F* = R+` by rw[field_mult_carrier] >>
  `FINITE R+` by metis_tac[field_nonzero_eq, SUBSET_DEF, SUBSET_FINITE] >>
  `FiniteGroup f*` by metis_tac[FiniteGroup_def] >>
  `f*.exp x (CARD F* ) = f*.id` by metis_tac[finite_group_Fermat] >>
  metis_tac[field_nonzero_mult_property]);

(* Theorem: FiniteField r ==> CARD R = SUC (CARD R+) *)
(* Proof:
   FiniteField r ==> Field r /\ FINITE R     by FiniteField_def
   Since    #0 IN R                          by field_zero_element
   Thus     {#0} SUBSET R                    by SUBSET_DEF
   Hence    {#0} INTER R = {#0}              by SUBSET_INTER_ABSORPTION
   Now      F* = R DIFF {#0}                 by excluding_def
   and      F* = R+                          by field_mult_carrier
   Also     R+ SUBSET R                      by field_nonzero_eq, SUBSET_DEF
   Hence    FINITE R+                        by SUBSET_FINITE
   and      FINITE {#0}                      by FINITE_SING
   Therefore
     CARD R+
   = CARD R - CARD (R INTER {#0})            by CARD_DIFF
   = CARD R - CARD ({#0} INTER R)            by INTER_COMM
   = CARD R - CARD {#0}                      by above absorption
   = CARD R - 1                              by CARD_SING
   Since #1 IN R+                            by field_one_nonzero
         CARD R+ <> 0                        by MEMBER_NOT_EMPTY, CARD_EQ_0
   Hence
   CARD R = 1 + CARD R+ = SUC (CARD R+)      by SUC_ONE_ADD.
*)
val finite_field_carrier_card = store_thm(
  "finite_field_carrier_card",
  ``!r:'a field. FiniteField r ==> (CARD R = SUC (CARD R+))``,
  rpt strip_tac >>
  `Field r /\ FINITE R` by metis_tac[FiniteField_def] >>
  `{#0} SUBSET R` by rw[] >>
  `{#0} INTER R = {#0}` by rw[GSYM SUBSET_INTER_ABSORPTION] >>
  `F* = R DIFF {#0}` by rw[excluding_def] >>
  `F* = R+` by rw[GSYM field_mult_carrier] >>
  `FINITE R+` by metis_tac[field_nonzero_eq, SUBSET_DEF, SUBSET_FINITE] >>
  `CARD R+ = CARD R - CARD (R INTER {#0})` by metis_tac[CARD_DIFF, FINITE_SING] >>
  `_ = CARD R - CARD {#0}` by metis_tac[INTER_COMM] >>
  `_ = CARD R - 1` by rw[CARD_SING] >>
  `#1 IN R+` by rw[] >>
  `CARD R+ <> 0` by metis_tac[MEMBER_NOT_EMPTY, CARD_EQ_0] >>
  decide_tac);

(* Theorem: FiniteField r ==> (CARD R+ = CARD R - 1) *)
(* Proof:
   Since F* = R+                by field_mult_carrier
     and CARD F* = CARD R - 1   by finite_field_mult_carrier_card
   Hence the result follows.
*)
val finite_field_nonzero_carrier_card = store_thm(
  "finite_field_nonzero_carrier_card",
  ``!r:'a field. FiniteField r ==> (CARD R+ = CARD R - 1)``,
  metis_tac[finite_field_mult_carrier_card, field_mult_carrier, finite_field_is_field]);

(* Theorem: FiniteField r ==>
            (EVEN (CARD R) ==> ODD (CARD R+)) /\ (ODD (CARD R) ==> EVEN (CARD R+)) *)
(* Proof: by finite_field_carrier_card, EVEN_ODD_SUC *)
val finite_field_carrier_parity = store_thm(
  "finite_field_carrier_parity",
  ``!r:'a field. FiniteField r ==>
   (EVEN (CARD R) ==> ODD (CARD R+)) /\ (ODD (CARD R) ==> EVEN (CARD R+))``,
  ntac 2 strip_tac >>
  `CARD R = SUC (CARD (R+))` by rw[finite_field_carrier_card] >>
  metis_tac[EVEN_ODD_SUC]);

(* Theorem: FiniteField r ==> !x. x IN R ==> x ** (CARD R) = x *)
(* Proof:
   FiniteField r ==> Field r /\ FINITE R     by FiniteField_def
   Since #0 IN R                             by field_zero_element
   CARD R <> 0                               by MEMBER_NOT_EMPTY, CARD_EQ_0
   If x = #0,
     LHS = #0 ** (CARD R)
         = #0 = RHS                          by field_zero_exp
   If x <> #0,
      x IN R+                                by field_nonzero_eq
     LHS = x ** (CARD R)
         = x ** SUC (CARD R+)                by finite_field_carrier_card
         = x ** (CARD R+) * x                by field_exp_suc
         = #1 * x                            by finite_field_Fermat
         = x = RHS                           by field_mult_lone
*)
val finite_field_fermat_thm = store_thm(
  "finite_field_fermat_thm",
  ``!r:'a field. FiniteField r ==> !x. x IN R ==> (x ** CARD R = x)``,
  rpt strip_tac >>
  `Field r /\ FINITE R` by metis_tac[FiniteField_def] >>
  `#0 IN R` by rw[] >>
  `CARD R <> 0` by metis_tac[MEMBER_NOT_EMPTY, CARD_EQ_0] >>
  Cases_on `x = #0` >-
  rw[field_zero_exp] >>
  rw[field_nonzero_eq, finite_field_carrier_card, field_exp_suc, finite_field_Fermat]);

(* Theorem: FiniteField r ==> !x. x IN R ==> !n. x ** (CARD R ** n) = x *)
(* Proof:
   Let m = CARD R.
   By induction on n.
   Base case: x ** m ** 0 = x
        x ** m ** 0
      = x ** 1                  by EXP
      = x                       by field_exp_1
   Step case: x ** m ** n = x ==> x ** m ** SUC n = x
        x ** m ** SUC n
      = x ** (m * m ** n)       by EXP
      = (x ** m) ** (m ** n)    by field_exp_mult
      = x ** (m ** n)           by finite_field_fermat_thm
      = x                       by induction hypothesis
*)
val finite_field_fermat_all = store_thm(
  "finite_field_fermat_all",
  ``!r:'a field. FiniteField r ==> !x. x IN R ==> !n. x ** (CARD R ** n) = x``,
  rpt (stripDup[FiniteField_def]) >>
  Induct_on `n` >>
  rw[EXP, field_exp_mult, finite_field_fermat_thm]);

(* Theorem: FiniteField r ==> !x. x IN R ==> !n. x ** n = x ** (n MOD (CARD R)) *)
(* Proof:
   Let m = CARD R+.
   Then 0 < m                                 by field_nonzero_card_pos
     x ** n
   = x ** (n DIV m * m + n MOD m)             by DIVISION
   = x ** (n DIV m * m) * x ** (n MOD m)      by field_exp_add
   = x ** (m * (n DIV m)) * x ** (n MOD m)    by MULT_COMM
   = (x ** m) ** (n DIV m) * x ** (n MOD m)   by field_exp_mult
   = #1 ** (n DIV m) * x ** (n MOD m)         by finite_field_fermat_thm
   = x ** (n MOD m)                           by field_one_exp
*)
val finite_field_exp_mod = store_thm(
  "finite_field_exp_mod",
  ``!r:'a field. FiniteField r ==> !x. x IN R+ ==> !n. x ** n = x ** (n MOD (CARD R+))``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = CARD R+` >>
  `0 < m` by rw[field_nonzero_card_pos, Abbr`m`] >>
  `x IN R` by rw[field_nonzero_element] >>
  `x ** n = x ** (m * (n DIV m) + n MOD m)` by metis_tac[DIVISION, MULT_COMM] >>
  rw[field_exp_add, field_exp_mult, finite_field_Fermat, Abbr`m`]);

(* ------------------------------------------------------------------------- *)
(* Field Subgroup                                                            *)
(* ------------------------------------------------------------------------- *)

(* A field subgroup is a subgroup of the multiplicative group f* of a field. *)

(* Theorem: properties of g <= f* *)
(* Proof:
   Note g <= f*
    ==> Group g /\ G SUBSET F* /\ g.op = f*.op  by Subgroup_def
    ==> g.id IN G                               by group_id_element
    and #0 NOTIN F*                             by excluding_def

   For each goal:
   (1) g.id = #1
       g.id
     = f*.id                        by subgroup_id
     = #1                           by field_nonzero_mult_property
   (2) g.op = r.prod.op
       g.op
     = f*.op                        by Subgroup_def, g <= f*
     = r.prod.op                    by field_nonzero_mult_property
   (3) !x n. x IN G ==> (g.exp x n = r.prod.exp x n)
       g.exp x n
     = f*.exp x n                   by subgroup_exp
     = x ** n                       by field_nonzero_mult_property
   (4) G SUBSET R+, true            by field_mult_carrier, F* = R+
   (5) #1 IN G, true                by group_id_element, (1)
   (6) #0 NOTIN G, true             by SUBSET_DEF, (4), #0 NOTIN F*
*)
val field_subgroup_property = store_thm(
  "field_subgroup_property",
  ``!(r:'a field) (g:'a group). Field r /\ g <= f* ==>
    (g.id = #1) /\ (g.op = r.prod.op) /\ (!x n. x IN G ==> (g.exp x n = r.prod.exp x n)) /\
    G SUBSET R+ /\ #1 IN G /\ #0 NOTIN G``,
  ntac 3 (stripDup[Subgroup_def]) >>
  `#e = #1` by metis_tac[subgroup_id, field_nonzero_mult_property] >>
  `#0 NOTIN F*` by rw[excluding_def] >>
  `F* = R+` by rw[field_mult_carrier] >>
  fs[] >>
  rpt strip_tac >-
  metis_tac[subgroup_exp, field_nonzero_mult_property] >-
  metis_tac[group_id_element] >>
  metis_tac[SUBSET_DEF]);

(* Theorem: Field r /\ g <= f* ==> !x. x IN G ==> x IN R /\ x <> #0 *)
(* Proof:
   Since G SUBSET R+    by field_subgroup_property
   The result follows   by SUBSET_DEF, field_nonzero_eq
*)
val field_subgroup_element = store_thm(
  "field_subgroup_element",
  ``!(r:'a field) (g:'a group). Field r /\ g <= f* ==> !x. x IN G ==> x IN R /\ x <> #0``,
  metis_tac[field_subgroup_property, SUBSET_DEF, field_nonzero_eq]);

(* Theorem: Field r /\ g <= f* ==> (#e = #1) *)
(* Proof: by field_subgroup_property *)
val field_subgroup_id = store_thm(
  "field_subgroup_id",
  ``!(r:'a field) (g:'a group). Field r /\ g <= f* ==> (#e = #1)``,
  rw[field_subgroup_property]);

(* Theorem: Field r /\ g <= f* ==> !x n. x IN G ==> (g.exp x n = r.prod.exp x n) *)
(* Proof: by field_subgroup_property *)
val field_subgroup_exp = store_thm(
  "field_subgroup_exp",
  ``!(r:'a field) (g:'a group). Field r /\ g <= f* ==> !x n. x IN G ==> (g.exp x n = r.prod.exp x n)``,
  rw[field_subgroup_property]);

(* Theorem: Field r /\ g <= f* ==> !x. x IN G ==> (g.inv x = |/ x) *)
(* Proof:
   Note x IN R+    by field_subgroup_property, SUBSET_DEF
      g.inv x
   = f*.inv x      by subgroup_inv
   = |/ x          by field_mult_inv, x IN R+
*)
val field_subgroup_inv = store_thm(
  "field_subgroup_inv",
  ``!(r:'a field) (g:'a group). Field r /\ g <= f* ==> !x. x IN G ==> (g.inv x = |/ x)``,
  metis_tac[field_subgroup_property, SUBSET_DEF, subgroup_inv, field_mult_inv]);

(* Theorem: Field r /\ g <= f* ==> AbelianGroup g *)
(* Proof:
   Note AbelianGroup f*    by field_nonzero_mult_is_abelian_group
     so AbelianGroup g     by abelian_subgroup_abelian
*)
val field_subgroup_abelian_group = store_thm(
  "field_subgroup_abelian_group",
  ``!(r:'a field) (g:'a group). Field r /\ g <= f* ==> AbelianGroup g``,
  metis_tac[field_nonzero_mult_is_abelian_group, abelian_subgroup_abelian]);

(* Theorem: FiniteField r /\ g <= f* ==> FiniteGroup g *)
(* Proof:
   Note F* = R+                     by field_mult_carrier
    and g <= f*
    ==> Group g /\ G SUBSET F*      by Subgroup_def
   Note FINITE R+                   by field_nonzero_finite
     or FINITE F*                   by above, F* = R+
   Thus FINITE G                    by SUBSET_FINITE
     so FiniteGroup g               by FiniteGroup_def
*)
val field_subgroup_finite_group = store_thm(
  "field_subgroup_finite_group",
  ``!(r:'a field) (g:'a group). FiniteField r /\ g <= f* ==> FiniteGroup g``,
  rpt (stripDup[FiniteField_def, Subgroup_def]) >>
  `F* = R+` by rw[field_mult_carrier] >>
  `FINITE F*` by rw[field_nonzero_finite] >>
  metis_tac[FiniteGroup_def, SUBSET_FINITE]);

(* Theorem: FiniteField r /\ g <= f* ==> (CARD (G UNION {#0}) = CARD G + 1) *)
(* Proof:
   Note FiniteGroup g      by field_subgroup_finite_group
     so FINITE G           by FiniteGroup_def
    Now #0 NOTIN G         by field_subgroup_property
    and G INTER {#0} = {}  by IN_INTER, IN_SING, MEMBER_NOT_EMPTY
   Note FINITE {#0}        by FINITE_SING
    and CARD {#0} = 1      by CARD_SING
    and CARD {} = 0        by CARD_EMPTY

        CARD (G UNION {#0})
      = CARD G + CARD {#0} - CARD (G INTER {#0})  by CARD_UNION_EQN
      = CARD G + 1 - 0                            by above
      = CARD G + 1                                by arithmetic
*)
val field_subgroup_card = store_thm(
  "field_subgroup_card",
  ``!(r:'a field) (g:'a group). FiniteField r /\ g <= f* ==> (CARD (G UNION {#0}) = CARD G + 1)``,
  rpt (stripDup[FiniteField_def]) >>
  `FiniteGroup g` by metis_tac[field_subgroup_finite_group] >>
  `FINITE G` by metis_tac[FiniteGroup_def] >>
  `#0 NOTIN G` by rw[field_subgroup_property] >>
  `G INTER {#0} = {}` by metis_tac[IN_INTER, IN_SING, MEMBER_NOT_EMPTY] >>
  rw[CARD_UNION_EQN]);

(* ------------------------------------------------------------------------- *)
(* Subset Field and Subgroup Field                                           *)
(* ------------------------------------------------------------------------- *)

(* Note:
   Two related concepts are:
   subset_field: take s SUBSET R, with the field operations to form a field.
   subgroup field: take a subgroup g <= f*, with the field operations to form a field.

   Subset_field has to consider both addition and multiplication closure.
   This can be hard to achieve.
   Subset_field is briefly considered in fieldMap, for sub-structures.

   Subgroup_field has multiplicative closure guaranteed.
   However, the additive closure depends on the roots of the Master polynomial.
   see: ffMasterTheory.subgroup_field_element_iff_master_root

   Subgroup_field definition and properties are given in ffMaster.
*)


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
