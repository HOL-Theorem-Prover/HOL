(* ------------------------------------------------------------------------- *)
(* Ring Library                                                              *)
(*                                                                           *)
(* A ring takes into account the interplay between its additive group and    *)
(* multiplicative monoid.                                                    *)
(* ------------------------------------------------------------------------- *)
(* Ring Theory                                                               *)
(* Units in a Ring                                                           *)
(* Ring Maps                                                                 *)
(* Ideals in Ring                                                            *)
(* Binomial coefficients and expansion, for Ring                             *)
(* Divisibility in Ring                                                      *)
(* Ring Theory -- Ideal and Quotient Ring.                                   *)
(* Applying Ring Theory: Ring Instances                                      *)
(* Integers as a Ring                                                        *)
(* Integral Domain Theory                                                   *)
(* Applying Integral Domain Theory: Integral Domain Instances                *)
(* ------------------------------------------------------------------------- *)
(* (Joseph) Hing-Lun Chan, The Australian National University, 2014-2019     *)
(* ------------------------------------------------------------------------- *)

(*
Ring Theory
============
HOL source has:
src\ring\src\ringScript.sml
src\ring\src\ringNormScript.sml
src\ring\src\semi_ringScript.sml
src\ring\src\numRingScript.sml
src\integer\integerRingScript.sml
src\rational\ratRingScript.sml
*)
(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ring";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open prim_recTheory arithmeticTheory dividesTheory gcdTheory gcdsetTheory
     pred_setTheory listTheory bagTheory containerTheory dep_rewrite
     whileTheory sortingTheory integerTheory;

open numberTheory combinatoricsTheory primeTheory;

open monoidTheory groupTheory;

val _ = intLib.deprecate_int ();

(* ------------------------------------------------------------------------- *)
(* Ring Documentation                                                       *)
(* ------------------------------------------------------------------------- *)
(* Data type:
   The generic symbol for ring data is r.
   r.carrier = Carrier set of Ring, overloaded as R.
   r.sum     = Addition component of Ring, binary operation overloaded as +.
   r.prod    = Multiplication component of Ring, binary operation overloaded as *.

   Overloading:
   +   = r.sum.op
   #0  = r.sum.id
   ##  = r.sum.exp
   -   = r.sum.inv
   *   = r.prod.op
   #1  = r.prod.id
   **  = r.prod.exp

   R   = r.carrier
   R+  = ring_nonzero r
   r*  = Invertibles r.prod
   R*  = r*.carrier
   f*  = (r.prod excluding #0)
   F*  = f*.carrier
*)
(* Definitions and Theorems (# are exported):

   Definitions:
   Ring_def        |- !r. Ring r <=> AbelianGroup r.sum /\ AbelianMonoid r.prod /\
                                     (r.sum.carrier = R) /\ (r.prod.carrier = R) /\
                                     !x y z. x IN R /\ y IN R /\ z IN R ==> (x * (y + z) = x * y + x * z)
   FiniteRing_def  |- !r. FiniteRing r <=> Ring r /\ FINITE R

   Simple theorems:
#  ring_carriers                   |- !r. Ring r ==> (r.sum.carrier = R) /\ (r.prod.carrier = R)
   ring_add_group                  |- !r. Ring r ==> Group r.sum /\ (r.sum.carrier = R) /\
                                      !x y. x IN R /\ y IN R ==> (x + y = y + x)
#  ring_add_group_rwt              |- !r. Ring r ==> Group r.sum /\ (r.sum.carrier = R)
   ring_add_abelian_group          |- !r. Ring r ==> AbelianGroup r.sum
   ring_mult_monoid                |- !r. Ring r ==> Monoid r.prod /\ (r.prod.carrier = R) /\
                                      !x y. x IN R /\ y IN R ==> (x * y = y * x)
#  ring_mult_monoid_rwt            |- !r. Ring r ==> Monoid r.prod /\ (r.prod.carrier = R)
   ring_mult_abelian_monoid        |- !r. Ring r ==> AbelianMonoid r.prod
   finite_ring_add_finite_group    |- !r. FiniteRing r ==> FiniteGroup r.sum /\ (r.sum.carrier = R)
   finite_ring_add_finite_abelian_group
                                   |- !r. FiniteRing r ==> FiniteAbelianGroup r.sum /\ (r.sum.carrier = R)
   finite_ring_mult_finite_monoid  |- !r. FiniteRing r ==> FiniteMonoid r.prod
   finite_ring_mult_finite_abelian_monoid
                                   |- !r. FiniteRing r ==> FiniteAbelianMonoid r.prod

   Lifting Theorems:
#  ring_zero_element     |- !r. Ring r ==> #0 IN R
#  ring_one_element      |- !r. Ring r ==> #1 IN R
   ring_carrier_nonempty |- !r. Ring r ==> R <> {}

   Ring Addition Theorems from Group (r.sum):
#  ring_add_element    |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> x + y IN R
   ring_add_assoc      |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x + y + z = x + (y + z))
   ring_add_comm       |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (x + y = y + x)
   ring_add_assoc_comm |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x + (y + z) = y + (x + z))
#  ring_add_zero_zero  |- !r. Ring r ==> (#0 + #0 = #0)
#  ring_add_lzero      |- !r. Ring r ==> !x. x IN R ==> (#0 + x = x)
#  ring_add_rzero      |- !r. Ring r ==> !x. x IN R ==> (x + #0 = x)
   ring_zero_unique    |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
                          ((y + x = x) <=> (y = #0)) /\ ((x + y = x) <=> (y = #0))

   Ring Multiplication Theorems from Monoid (r.prod):
#  ring_mult_element    |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> x * y IN R
   ring_mult_assoc      |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x * y * z = x * (y * z))
   ring_mult_comm       |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (x * y = y * x)
   ring_mult_assoc_comm |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x * (y * z) = y * (x * z))
#  ring_mult_rzero      |- !r. Ring r ==> !x. x IN R ==> (x * #0 = #0)
#  ring_mult_lzero      |- !r. Ring r ==> !x. x IN R ==> (#0 * x = #0)
#  ring_mult_zero_zero  |- !r. Ring r ==> (#0 * #0 = #0)
#  ring_mult_one_one    |- !r. Ring r ==> (#1 * #1 = #1)
#  ring_mult_lone       |- !r. Ring r ==> !x. x IN R ==> (#1 * x = x)
#  ring_mult_rone       |- !r. Ring r ==> !x. x IN R ==> (x * #1 = x)
   ring_one_unique      |- !r. Ring r ==> !y. y IN R ==>
                           ((!x. x IN R ==> (y * x = x) \/ (x * y = x)) <=> (y = #1))
   ring_one_eq_zero     |- !r. Ring r ==> ((#1 = #0) <=> (R = {#0}))

   Ring Numerical Theorems (from group_exp of ring_add_group):
#  ring_num_element      |- !r. Ring r ==> !n. ##n IN R
#  ring_num_mult_element |- !r. Ring r ==> !x. x IN R ==> !n. ##n * x IN R
#  ring_num_SUC          |- !r n. Ring r ==> (##(SUC n) = #1 + ##n)
   ring_num_suc          |- !r. Ring r ==> !n. ##(SUC n) = ##n + #1
#  ring_num_0            |- !r. ##0 = #0
   ring_num_one          |- !r. ##1 = #1 + #0
#  ring_num_1            |- !r. Ring r ==> (##1 = #1)
   ring_num_2            |- !r. Ring r ==> (##2 = #1 + #1)
   ring_sum_zero         |- !r. Ring r ==> !n. r.sum.exp #0 n = #0
   ring_num_all_zero     |- !r. Ring r ==> (#1 = #0) ==> !c. ##c = #0

   Ring Exponent Theorems (from monoid_exp of ring_mult_monoid):
#  ring_exp_element      |- !r. Ring r ==> !x. x IN R ==> !n. x ** n IN R
#  ring_exp_0            |- !x. x ** 0 = #1
#  ring_exp_SUC          |- !x n. x ** SUC n = x * x ** n
   ring_exp_suc          |- !r. Ring r ==> !x. x IN R ==> !n. x ** SUC n = x ** n * x
#  ring_exp_1            |- !r. Ring r ==> !x. x IN R ==> (x ** 1 = x)
   ring_exp_comm         |- !r. Ring r ==> !x. x IN R ==> !n. x ** n * x = x * x ** n
#  ring_mult_exp         |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> !n. (x * y) ** n = x ** n * y ** n
   ring_exp_small        |- !r. Ring r ==> !x. x IN R ==>
                            (x ** 0 = #1) /\ (x ** 1 = x) /\ (x ** 2 = x * x) /\
                            (x ** 3 = x * x ** 2) /\ (x ** 4 = x * x ** 3) /\
                            (x ** 5 = x * x ** 4) /\ (x ** 6 = x * x ** 5) /\
                            (x ** 7 = x * x ** 6) /\ (x ** 8 = x * x ** 7) /\
                            (x ** 9 = x * x ** 8)

   Ring Distribution Theorems:
#  ring_mult_radd        |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==>
                            (x * (y + z) = x * y + x * z)
#  ring_mult_ladd        |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==>
                            ((y + z) * x = y * x + z * x)
   ring_mult_add         |- !r. Ring r ==> !z y x. x IN R /\ y IN R /\ z IN R ==>
                                           (x * (y + z) = x * y + x * z) /\ ((y + z) * x = y * x + z * x)
   ring_num_mult_suc     |- !r. Ring r ==> !x. x IN R ==> !n. ##(SUC n) * x = ##n * x + x
   ring_num_mult_small   |- !r. Ring r ==> !x. x IN R ==>
                                           (#0 * x = #0) /\ (#1 * x = x) /\
                                           (##2 * x = x + x) /\ (##3 * x = ##2 * x + x)

   Ring Negation Theorems:
#  ring_neg_element     |- !r. Ring r ==> !x. x IN R ==> -x IN R
#  ring_neg_zero        |- !r. Ring r ==> (-#0 = #0)
#  ring_add_lneg        |- !r. Ring r ==> !x. x IN R ==> (-x + x = #0)
#  ring_add_rneg        |- !r. Ring r ==> !x. x IN R ==> (x + -x = #0)
   ring_add_lneg_assoc  |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (y = x + (-x + y)) /\ (y = -x + (x + y))
   ring_add_rneg_assoc  |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (y = y + -x + x) /\ (y = y + x + -x)
   ring_add_lcancel     |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((x + y = x + z) <=> (y = z))
   ring_add_rcancel     |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((y + x = z + x) <=> (y = z))
   ring_zero_fix        |- !r. Ring r ==> !x. x IN R ==> ((x + x = x) <=> (x = #0))
#  ring_neg_neg         |- !r. Ring r ==> !x. x IN R ==> (--x = x)
   ring_neg_eq_zero     |- !r. Ring r ==> !x. x IN R ==> ((-x = #0) <=> (x = #0))
   ring_neg_eq          |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> ((-x = -y) <=> (x = y))
   ring_neg_eq_swap     |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> ((-x = y) <=> (x = -y))
   ring_add_eq_zero     |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> ((x + y = #0) <=> (y = -x))
   ring_neg_add_comm    |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (-(x + y) = -y + -x)
#  ring_neg_add         |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (-(x + y) = -x + -y)

   Ring Distribution Theorems with Negation:
#  ring_mult_lneg       |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (-x * y = -(x * y))
#  ring_mult_rneg       |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (x * -y = -(x * y))
#  ring_neg_mult        |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
                           (-(x * y) = -x * y) /\ (-(x * y) = x * -y)
#  ring_mult_neg_neg    |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (-x * -y = x * y)

   More Ring Numeral Theorems (involving distribution eventually):
   ring_num_add         |- !r. Ring r ==> !n k. ##(n + k) = ##n + ##k
   ring_num_add_assoc   |- !r. Ring r ==> !x. x IN R ==> !m n. ##m + (##n + x) = ##(m + n) + x
   ring_num_mult        |- !r. Ring r ==> !m n. ##m * ##n = ##(m * n)
   ring_num_mult_assoc  |- !r. Ring r ==> !m n x. x IN R ==> (##m * (##n * x) = ##(m * n) * x)
   ring_num_exp         |- !r. Ring r ==> !m n. ##m ** n = ##(m ** n)
   ring_num_add_mult    |- !r. Ring r ==> !x. x IN R ==> !m n. ##(m + n) * x = ##m * x + ##n * x
   ring_num_add_mult_assoc  |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
                               !m n. ##(m + n) * x + y = ##m * x + (##n * x + y)
   ring_num_mult_neg    |- !r. Ring r ==> !x. x IN R ==> !n. -(##n * x) = ##n * -x
   ring_num_mult_radd   |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> !n. ##n * (x + y) = ##n * x + ##n * y
   ring_single_add_single |- !r. Ring r ==> !x. x IN R ==> (x + x = ##2 * x)
   ring_single_add_single_assoc |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (x + (x + y) = ##2 * x + y)
   ring_single_add_mult |- !r. Ring r ==> !x. x IN R ==> !n. x + ##n * x = ##(n + 1) * x
   ring_single_add_mult_assoc |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
                                 !n. x + (##n * x + y) = ##(n + 1) * x + y
   ring_single_add_neg_mult   |- !r. Ring r ==> !x. x IN R ==>
                                 !n. x + -(##n * x) = if n = 0 then x else -(##(n - 1) * x)
   ring_single_add_neg_mult_assoc |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
                       !n. x + (-(##n * x) + y) = if n = 0 then x + y else -(##(n - 1) * x) + y
   ring_mult_add_neg              |- !r. Ring r ==> !x. x IN R ==>
                       !n. ##n * x + -x = if n = 0 then -x else ##(n - 1) * x
   ring_mult_add_neg_assoc        |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
                       !n. ##n * x + (-x + y) = if n = 0 then -x + y else ##(n - 1) * x + y
   ring_mult_add_neg_mult         |- !r. Ring r ==> !x. x IN R ==>
                       !m n. ##m * x + -(##n * x) = if m < n then -(##(n - m) * x) else ##(m - n) * x
   ring_mult_add_neg_mult_assoc   |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
           !m n. ##m * x + (-(##n * x) + y) = if m < n then -(##(n - m) * x) + y else ##(m - n) * x + y
   ring_neg_add_neg       |- !r. Ring r ==> !x. x IN R ==> (-x + -x = -(##2 * x))
   ring_neg_add_neg_assoc |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (-x + (-x + y) = -(##2 * x) + y)
   ring_neg_add_neg_mult  |- !r. Ring r ==> !x. x IN R ==> !n. -x + -(##n * x) = -(##(n + 1) * x)
   ring_neg_add_neg_mult_assoc      |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
                                       !n. -x + (-(##n * x) + y) = -(##(n + 1) * x) + y
   ring_neg_mult_add_neg_mult       |- !r. Ring r ==> !x. x IN R ==>
                                       !m n. -(##m * x) + -(##n * x) = -(##(m + n) * x)
   ring_neg_mult_add_neg_mult_assoc |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
                                       !m n. -(##m * x) + (-(##n * x) + y) = -(##(m + n) * x) + y

   More Ring Exponent Theorems:
   ring_single_mult_single       |- !r. Ring r ==> !x. x IN R ==> (x * x = x ** 2)
   ring_single_mult_single_assoc |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (x * (x * y) = x ** 2 * y)
   ring_single_mult_exp          |- !r. Ring r ==> !x. x IN R ==> !n. x * x ** n = x ** (n + 1)
   ring_single_mult_exp_assoc    |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
                                    !n. x * (x ** n * y) = x ** (n + 1) * y
#  ring_exp_add       |- !r. Ring r ==> !x. x IN R ==> !n k. x ** (n + k) = x ** n * x ** k
   ring_exp_add_assoc |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
                         !n k. x ** n * (x ** k * y) = x ** (n + k) * y
#  ring_one_exp       |- !r. Ring r ==> !n. #1 ** n = #1
   ring_zero_exp      |- !r. Ring r ==> !n. #0 ** n = if n = 0 then #1 else #0
#  ring_exp_mult      |- !r. Ring r ==> !x. x IN R ==> !n k. x ** (n * k) = (x ** n) ** k
   ring_exp_mult_comm |- !r. Ring r ==> !x. x IN R ==> !m n. (x ** m) ** n = (x ** n) ** m
   ring_neg_square    |- !r. Ring r ==> !x. x IN R ==> (-x ** 2 = x ** 2)
   ring_exp_neg       |- !r. Ring r ==> !x. x IN R ==> !n. -x ** n = if EVEN n then x ** n else -(x ** n)
   ring_neg_exp       |- !r. Ring r ==> !x. x IN R ==> !n. -x ** n = if EVEN n then x ** n else -(x ** n)
   ring_num_mult_exp  |- !r. Ring r ==> !k m n. ##k * ##m ** n = ##(k * m ** n)
   ring_exp_mod_order |- !r. Ring r ==> !x. x IN R /\ 0 < order r.prod x ==>
                                        !n. x ** n = x ** (n MOD order r.prod x)

   Ring Subtraction Theorems:
#  ring_sub_def       |- !r x y. x - y = x + -y
   ring_sub_zero      |- !r. Ring r ==> !x. x IN R ==> (x - #0 = x)
   ring_sub_eq_zero   |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> ((x - y = #0) <=> (x = y))
   ring_sub_eq        |- !r. Ring r ==> !x. x IN R ==> (x - x = #0)
#  ring_sub_element   |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> x - y IN R
   ring_zero_sub      |- !r. Ring r ==> !x. x IN R ==> (#0 - x = -x)
   ring_sub_lcancel   |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((x - y = x - z) <=> (y = z))
   ring_sub_rcancel   |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((y - x = z - x) <=> (y = z))
   ring_neg_sub       |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (-(x - y) = y - x)
   ring_add_sub       |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (x + y - y = x)
   ring_add_sub_comm  |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (y + x - y = x)
   ring_add_sub_assoc |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x + y - z = x + (y - z))
   ring_sub_add       |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (x - y + y = x)
   ring_sub_eq_add    |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((x - y = z) <=> (x = y + z))
   ring_sub_pair_reduce   |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x + z - (y + z) = x - y)
   ring_add_sub_identity  |- !r. Ring r ==> !x y z t. x IN R /\ y IN R /\ z IN R /\ t IN R ==>
                                            ((x + y = z + t) <=> (x - z = t - y))
   ring_mult_lsub      |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x * z - y * z = (x - y) * z)
   ring_mult_rsub      |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x * y - x * z = x * (y - z))
   ring_add_pair_sub   |- !r. Ring r ==> !x y p q. x IN R /\ y IN R /\ p IN R /\ q IN R ==>
                                         (x + y - (p + q) = x - p + (y - q))
   ring_mult_pair_sub  |- !r. Ring r ==> !x y p q. x IN R /\ y IN R /\ p IN R /\ q IN R ==>
                                         (x * y - p * q = (x - p) * (y - q) + (x - p) * q + p * (y - q))
   ring_mult_pair_diff |- !r. Ring r ==> !x y p q. x IN R /\ y IN R /\ p IN R /\ q IN R ==>
                                                   (x * y - p * q = (x - p) * y + p * (y - q))
   ring_num_sub        |- !r. Ring r ==> !n m. m < n ==> (##(n - m) = ##n - ##m)

   Ring Binomial Expansions:
   ring_binomial_2  |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
                           ((x + y) ** 2 = x ** 2 + ##2 * (x * y) + y ** 2)
   ring_binomial_3  |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
                           ((x + y) ** 3 = x ** 3 + ##3 * (x ** 2 * y) + ##3 * (x * y ** 2) + y ** 3)
   ring_binomial_4  |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
                           ((x + y) ** 4 = x ** 4 + ##4 * (x ** 3 * y) +
                                           ##6 * (x ** 2 * y ** 2) + ##4 * (x * y ** 3) + y ** 4)

   Non-zero Elements of a Ring (for Integral Domain):
   ring_nonzero_def          |- !r. R+ = R DIFF {#0}
   ring_nonzero_eq           |- !r x. x IN R+ <=> x IN R /\ x <> #0
   ring_nonzero_element      |- !r x. x IN R+ ==> x IN R
   ring_neg_nonzero          |- !r. Ring r ==> !x. x IN R+ ==> -x IN R+
   ring_nonzero_mult_carrier |- !r. Ring r ==> (F* = R+)

   Ring Characteristic:
   char_def       |- !r. char r = order r.sum #1
   char_property  |- !r. ##(char r) = #0
   char_eq_0      |- !r. (char r = 0) <=> !n. 0 < n ==> ##n <> #0
   char_minimal   |- !r. 0 < char r ==> !n. 0 < n /\ n < char r ==> ##n <> #0
   finite_ring_char_pos |- !r. FiniteRing r ==> 0 < char r

   Characteristic Theorems:
   ring_char_divides    |- !r. Ring r ==> !n. (##n = #0) <=> (char r) divides n
   ring_char_eq_1       |- !r. Ring r ==> ((char r = 1) <=> (#1 = #0))
   ring_char_2_property |- !r. Ring r /\ (char r = 2) ==> (#1 + #1 = #0)
   ring_char_2_neg_one  |- !r. Ring r /\ (char r = 2) ==> (-#1 = #1)
   ring_char_2_double   |- !r. Ring r /\ (char r = 2) ==> !x. x IN R ==> (x + x = #0)
   ring_neg_char_2      |- !r. Ring r /\ (char r = 2) ==> !x. x IN R ==> (-x = x)
   ring_add_char_2      |- !r. Ring r /\ (char r = 2) ==> !x y. x IN R /\ y IN R ==> (x + y = x - y)
   ring_num_char_coprime_nonzero |- !r. Ring r /\ #1 <> #0 ==> !c. coprime c (char r) ==> ##c <> #0
   ring_char_alt        |- !r. Ring r ==> !n. 0 < n ==>
                               ((char r = n) <=> (##n = #0) /\ !m. 0 < m /\ m < n ==> ##m <> #0)
   ring_neg_one_eq_one  |- !r. Ring r /\ #1 <> #0 ==> ((-#1 = #1) <=> (char r = 2))
   ring_add_exp_eqn     |- !r. Ring r ==> !x. x IN R ==> !n. r.sum.exp x n = x * ##n
   ring_num_eq          |- !r. Ring r ==> !n m. n < char r /\ m < char r ==> ((##n = ##m) <=> (n = m))
   ring_num_mod         |- !r. Ring r /\ 0 < char r ==> !n. ##n = ##(n MOD char r)
   ring_num_negative    |- !r. Ring r /\ 0 < char r ==> !z. ?y x. (y = ##x) /\ (y + ##z = #0)
   ring_char_0          |- !r. Ring r /\ (char r = 0) ==> INFINITE R
   ring_char_1          |- !r. Ring r /\ (char r = 1) ==> (R = {#0})

   Finite Ring:
   finite_ring_is_ring       |- !r. FiniteRing r ==> Ring r
   finite_ring_card_pos      |- !r. FiniteRing r ==> 0 < CARD R
   finite_ring_card_eq_1     |- !r. FiniteRing r ==> ((CARD R = 1) <=> (#1 = #0))
   finite_ring_char          |- !r. FiniteRing r ==> 0 < char r /\ (char r = order r.sum #1)
   finite_ring_char_divides  |- !r. FiniteRing r ==> (char r) divides (CARD R)
   finite_ring_card_prime    |- !r. FiniteRing r /\ prime (CARD R) ==> (char r = CARD R)
   finite_ring_char_alt      |- !r. FiniteRing r ==>
                        !n. (char r = n) <=> 0 < n /\ (##n = #0) /\ !m. 0 < m /\ m < n ==> ##m <> #0

*)

(* ------------------------------------------------------------------------- *)
(* Basic definitions                                                         *)
(* ------------------------------------------------------------------------- *)

(* Set up ring type as a record
   A Ring has:
   . a carrier set (set = function 'a -> bool, since MEM is a boolean function)
   . a sum group (with sum as its binary operation )
   . a product monoid (with multiplication as its binary operation)
*)
val _ = Hol_datatype`
  ring = <| carrier: 'a -> bool;
                sum: 'a group;
               prod: 'a monoid (* monoid and group share the same type *)
          |>
`;

(* overloading  *)
val _ = overload_on ("+", ``r.sum.op``);
val _ = overload_on ("*", ``r.prod.op``);
val _ = overload_on ("R", ``r.carrier``); (* just use this, also for field later. *)
val _ = overload_on ("#0", ``r.sum.id``); (* define zero *)
val _ = overload_on ("#1", ``r.prod.id``); (* define one *)

(* Ring Definition:
   A Ring is a record r with elements of type 'a ring, such that
   . r.sum is an Abelian group
   . r.prod is an Abelian group (so-called commutative ring)
   . r.sum.carrier is the whole set
   . r.prod.carrier is the whole set (so there may be #0 divisors)
   . #0 multiplies to #0 (on the left) (no need, can be deduced from distributive law)
   . multiplication distributes over addition (on the left)
*)
val Ring_def = Define`
    Ring (r:'a ring) <=>
       AbelianGroup r.sum  /\
       AbelianMonoid r.prod /\
       (r.sum.carrier = R) /\
       (r.prod.carrier = R) /\
       (!x y z. x IN R /\ y IN R /\ z IN R ==> (x * (y + z) = (x * y) + (x * z)))
`;

(* A finite ring *)
val FiniteRing_def = Define`
    FiniteRing (r:'a ring) <=> Ring r /\ FINITE R
`;

(* ------------------------------------------------------------------------- *)
(* Simple Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r ==> (r.sum.carrier = R) /\ (r.prod.carrier = R) *)
(* Proof: by Ring_def. *)
val ring_carriers = store_thm(
  "ring_carriers",
  ``!r:'a ring. Ring r ==> (r.sum.carrier = R) /\ (r.prod.carrier = R)``,
  rw_tac std_ss[Ring_def]);

(* export simple result *)
val _ = export_rewrites ["ring_carriers"];

(* Theorem: Ring additions form an Abelian group. *)
(* Proof: by definition. *)
val ring_add_group = store_thm(
  "ring_add_group",
  ``!r:'a ring. Ring r ==> Group r.sum /\ (r.sum.carrier = R) /\ !x y. x IN R /\ y IN R ==> (x + y = y + x)``,
  rw_tac std_ss[Ring_def, AbelianGroup_def]);

(* export this will introduce commutativity in rewrite, no good. *)
(* val _ = export_rewrites ["ring_add_group"]; *)

(* Use Michael's version for export_rewrites, stripping commutativity. *)
val ring_add_group_rwt = save_thm(
  "ring_add_group_rwt",
  ring_add_group |> SPEC_ALL |> UNDISCH |> CONJUNCTS
                 |> (fn l => LIST_CONJ (List.take(l,2)))
                 |> DISCH_ALL |> GEN_ALL);
(* > val ring_add_group_rwt = |- !r. Ring r ==> Group r.sum /\ (r.sum.carrier = R) : thm *)
val _ = export_rewrites ["ring_add_group_rwt"];

(* Theorem: Ring r ==> AbelianGroup r.sum *)
(* Proof: By AbelianGroup_def, ring_add_group. *)
val ring_add_abelian_group = store_thm(
  "ring_add_abelian_group",
  ``!r:'a ring. Ring r ==> AbelianGroup r.sum``,
  rw[AbelianGroup_def, ring_add_group]);
val _ = export_rewrites ["ring_add_abelian_group"];

(* Theorem: Ring multiplications form an Abelian monoid. *)
(* Proof: by definition. *)
val ring_mult_monoid = store_thm(
  "ring_mult_monoid",
  ``!r:'a ring. Ring r ==> Monoid r.prod /\ (r.prod.carrier = R) /\ !x y. x IN R /\ y IN R ==> (x * y = y * x)``,
  rw_tac std_ss[Ring_def, AbelianMonoid_def]);

(* export this will introduce commutativity in rewrite, no good. *)
(* val _ = export_rewrites ["ring_mult_monoid"]; *)

(* Copy Michael's version for export_rewrites, stripping commutativity. *)
val ring_mult_monoid_rwt = save_thm(
  "ring_mult_monoid_rwt",
  ring_mult_monoid |> SPEC_ALL |> UNDISCH |> CONJUNCTS
                   |> (fn l => LIST_CONJ (List.take(l,2)))
                   |> DISCH_ALL |> GEN_ALL);
(* > val ring_mult_monoid_rwt = |- !r. Ring r ==> Monoid r.prod /\ (r.prod.carrier = R) : thm *)
val _ = export_rewrites ["ring_mult_monoid_rwt"];

(* Theorem: Ring r ==> AbelianMonoid r.prod *)
(* Proof: By AbelianMonoid_def, ring_mult_monoid. *)
val ring_mult_abelian_monoid = store_thm(
  "ring_mult_abelian_monoid",
  ``!r:'a ring. Ring r ==> AbelianMonoid r.prod``,
  rw[AbelianMonoid_def, ring_mult_monoid]);

(* Theorem: FiniteRing r ==> FiniteGroup r.sum *)
(* Proof: by definitions. *)
val finite_ring_add_finite_group = store_thm(
  "finite_ring_add_finite_group",
  ``!r:'a ring. FiniteRing r ==> FiniteGroup r.sum /\ (r.sum.carrier = R)``,
  metis_tac[FiniteRing_def, FiniteGroup_def, ring_add_group]);

(* Theorem: FiniteRing r ==> FiniteAbelianGroup r.sum *)
(* Proof: by definitions. *)
val finite_ring_add_finite_abelian_group = store_thm(
  "finite_ring_add_finite_abelian_group",
  ``!r:'a ring. FiniteRing r ==> FiniteAbelianGroup r.sum /\ (r.sum.carrier = R)``,
  metis_tac[FiniteRing_def, FiniteAbelianGroup_def, AbelianGroup_def, ring_add_group]);

(* Theorem: FiniteRing r ==> FiniteMonoid r.prod *)
(* Proof: by definitions. *)
val finite_ring_mult_finite_monoid = store_thm(
  "finite_ring_mult_finite_monoid",
  ``!r:'a ring. FiniteRing r ==> FiniteMonoid r.prod``,
  metis_tac[FiniteRing_def, FiniteMonoid_def, ring_mult_monoid]);

(* Theorem: FiniteRing r ==> FiniteAbelianMonoid r.prod *)
(* Proof: by definitions. *)
val finite_ring_mult_finite_abelian_monoid = store_thm(
  "finite_ring_mult_finite_abelian_monoid",
  ``!r:'a ring. FiniteRing r ==> FiniteAbelianMonoid r.prod``,
  metis_tac[FiniteRing_def, FiniteAbelianMonoid_def, AbelianMonoid_def, ring_mult_monoid]);

(* ------------------------------------------------------------------------- *)
(* Lifting Theorems                                                          *)
(* ------------------------------------------------------------------------- *)

(*

local
val rag = ring_add_group |> SPEC_ALL |> UNDISCH_ALL
val rgroup = rag |> CONJUNCT1
val rsc = rag |> CONJUNCT2 |> CONJUNCT1
in
fun lift_group_thm gname rname = let
  val gthm = DB.fetch "group" ("group_" ^ gname)
  val gthm' = SPEC ``(r:'a ring).sum`` gthm
in
  save_thm("ring_" ^ rname,
           MP gthm' rgroup
              |> REWRITE_RULE [rsc]
              |> DISCH_ALL |> GEN_ALL)
end
end (* local *)

val ring_neg_add_comm = lift_group_thm "inv_op" "neg_add'"

*)


(* Lifting Group theorem for Ring
   from: !g: 'a group. Group g ==> E(g)
     to: !r:'a ring.  Ring r ==> E(r.sum)
    via: !r:'a ring.  Ring r ==> Group r.sum /\ (r.sum.carrier = R)
*)
local
val rag = ring_add_group |> SPEC_ALL |> UNDISCH_ALL
val rgroup = rag |> CONJUNCT1
val rsc = rag |> CONJUNCT2 |> CONJUNCT1
in
fun lift_group_thm gsuffix rsuffix = let
  val gthm = DB.fetch "group" ("group_" ^ gsuffix)
  val gthm' = gthm |> SPEC ``(r:'a ring).sum``
in
  save_thm("ring_" ^ rsuffix,
           MP gthm' rgroup
              |> REWRITE_RULE [rsc]
              |> DISCH_ALL |> GEN_ALL)
end
end; (* local *)

(* Lifting Monoid theorem for Ring
   from: !g: 'a monoid. Monoid g ==> E(g)
     to: !r:'a ring.  Ring r ==> E(r.prod)
    via: !r:'a ring.  Ring r ==> Monoid r.prod /\ (r.prod.carrier = R)
*)
local
val rmm = ring_mult_monoid |> SPEC_ALL |> UNDISCH_ALL
val rmonoid = rmm |> CONJUNCT1
val rpc = rmm |> CONJUNCT2 |> CONJUNCT1
in
fun lift_monoid_thm msuffix rsuffix = let
  val mthm = DB.fetch "monoid" ("monoid_" ^ msuffix)
  val mthm' = mthm |> SPEC ``(r:'a ring).prod``
in
  save_thm("ring_" ^ rsuffix,
           MP mthm' rmonoid
              |> REWRITE_RULE [rpc]
              |> DISCH_ALL |> GEN_ALL)
end
end; (* local *)

(* ------------------------------------------------------------------------- *)
(* Properties of #0 and #1 - representations of ring_zero and ring_one       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring #0 in carrier. *)
(* Proof: by group_id_element. *)
val ring_zero_element = lift_group_thm "id_element" "zero_element";
(* > val ring_zero_element = |- !r. Ring r ==> #0 IN R : thm *)

(* Theorem: Ring one in carrier. *)
(* Proof: by monoid_id_element *)
val ring_one_element = lift_monoid_thm "id_element" "one_element";
(* > val ring_one_element = |- !r. Ring r ==> #1 IN R : thm *)

val _ = export_rewrites ["ring_zero_element", "ring_one_element"];

(* Theorem: Ring r ==> R <> {} *)
(* Proof: by ring_zero_element, MEMBER_NOT_EMPTY *)
val ring_carrier_nonempty = store_thm(
  "ring_carrier_nonempty",
  ``!r:'a ring. Ring r ==> R <> {}``,
  metis_tac[ring_zero_element, MEMBER_NOT_EMPTY]);

(* ------------------------------------------------------------------------- *)
(* Theorems from Group and Monoid Theory (for addition and multiplication)   *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Ring Addition Theorems from Group (r.sum)                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring addition in carrier. *)
(* Proof: by group_op_element of Group (r.sum). *)
val ring_add_element = lift_group_thm "op_element" "add_element";
(* > val ring_add_element = |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> x + y IN R : thm *)

val _ = export_rewrites ["ring_add_element"];

(* Theorem: Ring addition is associative. *)
(* Proof: by group_assoc of Group (r.sum). *)
val ring_add_assoc = lift_group_thm "assoc" "add_assoc";
(* > val ring_add_assoc = |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x + y + z = x + (y + z)) : thm *)

(* no export of associativity *)
(* val _ = export_rewrites ["ring_add_assoc"]; *)

(* Theorem: Ring addition is commutative *)
(* Proof: by commutativity of Abelian Group (r.sum). *)
val ring_add_comm = store_thm(
  "ring_add_comm",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> (x + y = y + x)``,
  rw_tac std_ss[ring_add_group]);

(* no export of commutativity *)
(* val _ = export_rewrites ["ring_add_comm"]; *)

(* Theorem: Ring addition is associate-commutative. *)
(* Proof: by ring_add_comm and ring_add_assoc.
      x + (y + z)
    = (x + y) + z   by ring_add_assoc
    = (y + x) + z   by ring_add_comm
    = y + (x + z)   by ring_add_assoc
*)
val ring_add_assoc_comm = store_thm(
  "ring_add_assoc_comm",
  ``!r:'a ring. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x + (y + z) = y + (x + z))``,
  rw_tac std_ss[GSYM ring_add_assoc, ring_add_comm]);

(* Theorem: #0 + #0 = #0 *)
(* Proof: by group_id_id of Group (r.sum). *)
val ring_add_zero_zero = lift_group_thm "id_id" "add_zero_zero";
(* > val ring_add_zero_zero = |- !r. Ring r ==> (#0 + #0 = #0) : thm *)

(* Theorem: #0 + x = x. *)
(* Proof: by group_lid of Group (r.sum). *)
val ring_add_lzero = lift_group_thm "lid" "add_lzero";
(* > val ring_add_lzero = |- !r. Ring r ==> !x. x IN R ==> (#0 + x = x) : thm *)

(* Theorem: x + #0 = x. *)
(* Proof: by group_rid of Group (r.sum), or by ring_add_lzero and ring_add_comm.
      x + #0
    = #0 + x    by ring_add_comm
    = x         by ring_add_lzero
*)
val ring_add_rzero = lift_group_thm "rid" "add_rzero";
(* > val ring_add_rzero = |- !r. Ring r ==> !x. x IN R ==> (x + #0 = x) : thm *)

val _ = export_rewrites ["ring_add_zero_zero", "ring_add_lzero", "ring_add_rzero"];

(* Theorem: #0 is unique. *)
(* Proof: by group_id_unique of Group (r.sum). *)
val ring_zero_unique = lift_group_thm "id_unique" "zero_unique";
(* > val ring_zero_unique = |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> ((y + x = x) <=> (y = #0)) /\ ((x + y = x) <=> (y = #0)) : thm *)

(* ------------------------------------------------------------------------- *)
(* Ring Multiplication Theorems from Monoid (r.prod)                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: x * y IN R *)
(* Proof: by monoid_op_element of Monoid (r.prod). *)
val ring_mult_element = lift_monoid_thm "op_element" "mult_element";
(* > val ring_mult_element = |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> x * y IN R : thm *)

val _ = export_rewrites ["ring_mult_element"];

(* Theorem: (x * y) * z = x * (y * z) *)
(* Proof: by monoid_assoc of Monoid (r.prod). *)
val ring_mult_assoc = lift_monoid_thm "assoc" "mult_assoc";
(* > val ring_mult_assoc = |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x * y * z = x * (y * z)) : thm *)

(* no export of associativity *)
(* val _ = export_rewrites ["ring_mult_assoc"]; *)

(* Theorem: x * y = y * x *)
(* Proof: by commutativity of Abelian Monoid (r.prod). *)
val ring_mult_comm = store_thm(
  "ring_mult_comm",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> (x * y = y * x)``,
  rw_tac std_ss[ring_mult_monoid]);

(* no export of commutativity *)
(* val _ = export_rewrites ["ring_mult_comm"]; *)

(* Theorem: x * (y * z) = y * (x * z) *)
(* Proof: by ring_mult_assoc and ring_mult_comm. *)
val ring_mult_assoc_comm = store_thm(
  "ring_mult_assoc_comm",
  ``!r:'a ring. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x * (y * z) = y * (x * z))``,
  rw_tac std_ss[GSYM ring_mult_assoc, ring_mult_comm]);

(* Theorem: x * #0 = #0 *)
(* Proof: by distribution and group_id_fix.
     x * #0
   = x * (#0 + #0)       by ring_add_zero_zero
   = x * #0 + x * #0     by distribution in Ring_def
   hence x * #0 = #0     by group_id_fix
*)
val ring_mult_rzero = store_thm(
  "ring_mult_rzero",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> (x * #0 = #0)``,
  rpt strip_tac >>
  `#0 IN R /\ x * #0 IN R` by rw_tac std_ss[ring_zero_element, ring_mult_element] >>
  metis_tac[ring_add_zero_zero, ring_add_group, group_id_fix, Ring_def]);

val _ = export_rewrites ["ring_mult_rzero"];

(* Theorem: #0 * x = #0 *)
(* Proof: by ring_mult_rzero and Ring_def implicit x * y = y * x.
   or by ring_mult_lzero and ring_mult_comm.
*)
val ring_mult_lzero = store_thm(
  "ring_mult_lzero",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> (#0 * x = #0)``,
  rw[ring_mult_comm]);

val _ = export_rewrites ["ring_mult_lzero"];

(* Theorem: #0 * #0 = #0 *)
(* Proof: by ring_mult_lzero, ring_zero_element. *)
val ring_mult_zero_zero = store_thm(
  "ring_mult_zero_zero",
  ``!r:'a ring. Ring r ==> (#0 * #0 = #0)``,
  rw[]);

val _ = export_rewrites ["ring_mult_zero_zero"];

(* Theorem: #1 * #1 = #1 *)
(* Proof: by monoid_id_id. *)
val ring_mult_one_one = lift_monoid_thm "id_id" "mult_one_one";
(* > val ring_mult_one_one = |- !r. Ring r ==> (#1 * #1 = #1) : thm *)

(* Theorem: #1 * x = x *)
(* Proof: by defintion and monoid_lid. *)
val ring_mult_lone = lift_monoid_thm "lid" "mult_lone";
(* > val ring_mult_lone = |- !r. Ring r ==> !x. x IN R ==> (#1 * x = x) : thm *)

(* Theorem: x * #1 = x *)
(* Proof: by defintion and monoid_rid. *)
val ring_mult_rone = lift_monoid_thm "rid" "mult_rone";
(* > val ring_mult_rone = |- !r. Ring r ==> !x. x IN R ==> (x * #1 = x) : thm *)

val _ = export_rewrites ["ring_mult_one_one", "ring_mult_lone", "ring_mult_rone"];

(* Theorem: #1 is unique. *)
(* Proof: from monoid_id_unique.
   Note this is: if there is a y that looks like #1 (i.e. !x. y * x = x or x * y = x)
   then it must be y = #1. This is NOT: !x y. y * x = x ==> y = #1.
*)
val ring_one_unique = store_thm(
  "ring_one_unique",
  ``!r:'a ring. Ring r ==> !y. y IN R ==> ((!x. x IN R ==> (y * x = x) \/ (x * y = x)) = (y = #1))``,
  metis_tac[monoid_id_unique, ring_mult_monoid]);

(* Theorem: For a Ring, #1 = #0 iff R = {#0} *)
(* Proof:
   If part: #1 = #0 ==> R = {#0}
      !x. x IN R ==> #1 * x = x    by ring_mult_lone
      !x. x IN R ==> #0 * x = #0   by ring_mult_lzero
      !x. x IN R ==> x = #0        by #1 = #0
      Since #0 IN R                by ring_zero_element
      this means R = {#0}          by UNIQUE_MEMBER_SING
   Only-if part: R = {#0} ==> #1 = #0
      #0 IN R                      by ring_zero_element
      #1 IN R                      by ring_one_element
      thus R = {#0} ==> #1 = #0    by IN_SING
*)
val ring_one_eq_zero = store_thm(
  "ring_one_eq_zero",
  ``!r:'a ring. Ring r ==> ((#1 = #0) <=> (R = {#0}))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    metis_tac[ring_zero_element, ring_mult_lone, ring_mult_lzero, UNIQUE_MEMBER_SING],
    metis_tac[ring_zero_element, ring_one_element, IN_SING]
  ]);

(* ------------------------------------------------------------------------- *)
(* Theorems inherit from Group or Monoid Theory (for ring_num and ring_exp)  *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Ring numbers: iterations on ring_add using one                            *)
(* ##0 = #0, ##1 = #1, ##2 = #1+#1, ##3 = #1+#1+#1, etc.                     *)
(* ------------------------------------------------------------------------- *)

val _ = overload_on ("ring_numr", ``r.sum.exp #1``); (* for fallback *)
val _ = overload_on ("##", ``r.sum.exp #1``);        (* current use *)

val _ = remove_termtok { tok = "##", term_name = "##" };

val _ = add_rule { fixity = Prefix 2200,
                   term_name = "##",
                   block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [TOK "##"] };

(* ------------------------------------------------------------------------- *)
(* Ring exponentials: iterations on ring_mult                                *)
(* x ** 0 = #1, x ** 1 = x, x ** 2 = x * x, x ** 3 = x * x * x, etc.         *)
(* ------------------------------------------------------------------------- *)
(* val ring_exp_def = Define `ring_exp (r:'a ring) = monoid_exp r.prod`; *)
(*
val ring_exp_def = Define`
  (ring_exp (r:'a ring) x 0 = #1) /\
  (ring_exp (r:'a ring) x (SUC n) = x * (ring_exp r x n))
`;
*)
(* val _ = overload_on ("**", ``ring_exp r``); *)
(* val _ = export_rewrites ["ring_exp_def"]; *)

val _ = overload_on ("**", ``r.prod.exp``);

(* ------------------------------------------------------------------------- *)
(* Ring Numerical Theorems (from group_exp of ring_add_group).               *)
(* ------------------------------------------------------------------------- *)

(* Problem: Should use lifting by incorporating ring_one_element. *)

(*
- show_assums := true;
> val it = () : unit

- group_exp_element;
> val it = [] |- !g. Group g ==> !x. x IN G ==> !n. x ** n IN G : thm
- group_exp_element |> SPEC ``(r:'a ring).sum``;
> val it = [] |- Group r.sum ==> !x. x IN r.sum.carrier ==> !n. r.sum.exp x n IN r.sum.carrier : thm
- group_exp_element |> SPEC ``(r:'a ring).sum`` |> UNDISCH;
> val it = [Group r.sum] |- !x. x IN r.sum.carrier ==> !n. r.sum.exp x n IN r.sum.carrier : thm
- group_exp_element |> SPEC ``(r:'a ring).sum`` |> UNDISCH |> SPEC ``#1``;
> val it =  [Group r.sum] |- #1 IN r.sum.carrier ==> !n. ##n IN r.sum.carrier : thm
- ring_add_group |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1;
> val it =  [Ring r] |- Group r.sum : thm
- group_exp_element |> SPEC ``(r:'a ring).sum`` |> UNDISCH |> SPEC ``#1`` |> PROVE_HYP (ring_add_group |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1);
> val it =  [Ring r] |- #1 IN r.sum.carrier ==> !n. ##n IN r.sum.carrier : thm
- ring_add_group |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT2 |> CONJUNCT1;
> val it =  [Ring r] |- r.sum.carrier = R : thm
- group_exp_element |> SPEC ``(r:'a ring).sum`` |> UNDISCH |> SPEC ``#1`` |> PROVE_HYP (ring_add_group |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1) |> REWRITE_RULE [ring_add_group |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT2 |> CONJUNCT1];
> val it =  [Ring r] |- #1 IN R ==> !n. ##n IN R : thm;
- ring_one_element |> SPEC_ALL |> UNDISCH_ALL;
> val it =  [Ring r] |- #1 IN R : thm
- group_exp_element |> SPEC ``(r:'a ring).sum`` |> UNDISCH |> SPEC ``#1`` |> PROVE_HYP (ring_add_group |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1) |> REWRITE_RULE [ring_add_group |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT2 |> CONJUNCT1, ring_one_element |> SPEC_ALL |> UNDISCH_ALL];
> val it =  [Ring r] |- !n. ##n IN R : thm
- group_exp_element |> SPEC ``(r:'a ring).sum`` |> UNDISCH |> SPEC ``#1`` |> PROVE_HYP (ring_add_group |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1) |> REWRITE_RULE [ring_add_group |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT2 |> CONJUNCT1, ring_one_element |> SPEC_ALL |> UNDISCH_ALL] |> DISCH_ALL |> GEN_ALL
> val it =  [] |- !r. Ring r ==> !n. ##n IN R : thm

- show_assums := false;
> val it = () : unit

*)

(* Lifting Group exp theorem for Ring
   from: !g: 'a group. Group g ==> E(g.exp #1 n)
     to: !r:'a ring.  Ring r ==> E(##n)
    via: !r:'a ring.  Ring r ==> Group r.sum /\ (r.sum.carrier = R)
         !r:'a ring.  Ring r ==> #1 IN R
*)
local
val rag = ring_add_group |> SPEC_ALL |> UNDISCH_ALL
val rgroup = rag |> CONJUNCT1
val rsc = rag |> CONJUNCT2 |> CONJUNCT1
val roe = ring_one_element |> SPEC_ALL |> UNDISCH_ALL
in
fun lift_group_exp gsuffix rsuffix = let
  val gthm = DB.fetch "group" ("group_exp_" ^ gsuffix)
  val gthm' = gthm |> SPEC ``(r:'a ring).sum`` |> UNDISCH |> SPEC ``#1``
in
  save_thm("ring_num_" ^ rsuffix,
           gthm' |> PROVE_HYP rgroup
                 |> REWRITE_RULE [rsc, roe]
                 |> DISCH_ALL |> GEN_ALL)
end
end; (* local *)

local
val rag = ring_add_group |> SPEC_ALL |> UNDISCH_ALL
val rgroup = rag |> CONJUNCT1
val rsc = rag |> CONJUNCT2 |> CONJUNCT1
val roe = ring_one_element |> SPEC_ALL |> UNDISCH_ALL
in
fun lift_group_exp_def gsuffix rsuffix = let
  val gthm = DB.fetch "group" ("group_exp_" ^ gsuffix)
  val gthm' = gthm |> SPEC ``(r:'a ring).sum`` |> SPEC ``#1`` (* no UNDISCH *)
in
  save_thm("ring_num_" ^ rsuffix,
           gthm' |> PROVE_HYP rgroup
                 |> REWRITE_RULE [rsc, roe]
                 |> DISCH_ALL |> GEN_ALL)
end
end; (* local *)

(* Theorem: ##n IN R *)
(* Proof: by group_exp_element and ring_num_def. *)
val ring_num_element = lift_group_exp "element" "element";
(* > val ring_num_element = |- !r. Ring r ==> !n. ##n IN R : thm *)

val _ = export_rewrites ["ring_num_element"];

(* Theorem: ##n * x IN R *)
(* Proof: by ring_num_element and ring_mult_element. *)
val ring_num_mult_element = store_thm(
  "ring_num_mult_element",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !n. ##n * x IN R``,
  rw[]);

val _ = export_rewrites ["ring_num_mult_element"];

(* Theorem: ##(SUC n) = #1 + ##n *)
(* Proof: by group_exp_SUC. *)
val ring_num_SUC = lift_group_exp_def "SUC" "SUC";
(* > val ring_num_SUC = |- !r n. Ring r ==> (##(SUC n) = #1 + ##n) : thm *)

val _ = export_rewrites ["ring_num_SUC"];

(* Theorem: ##(SUC n) = ##n + #1 *)
(* Proof: by group_exp_SUC and ring_add_comm. *)
val ring_num_suc = store_thm(
  "ring_num_suc",
  ``!r:'a ring. Ring r ==> !n. ##(SUC n) = ##n + #1``,
  rw[ring_add_comm]);

(*
ringTheory.ring_num_0   has Ring r ==> ##0 = #0   by lifting.
but:
monoid_exp_def |> ISPEC ``(r:'a ring).sum`` |> ISPEC ``#1`` |> ISPEC ``0`` |> SIMP_RULE bool_ss [FUNPOW_0];
val it = |- ##0 = #0: thm
> monoid_exp_def |> ISPEC ``(r:'a ring).sum`` |> ISPEC ``#1`` |> ISPEC ``1`` |> SIMP_RULE bool_ss [FUNPOW_1];
val it = |- ##1 = #1 + #0: thm
> monoid_exp_def |> ISPEC ``(r:'a ring).sum`` |> ISPEC ``#1`` |> ISPEC ``c:num``;
val it = |- ##c = FUNPOW ($+ #1) c #0: thm
*)

(* Obtain a better theorem *)
Theorem ring_num_0[simp] =
    monoid_exp_def |> ISPEC “(r:'a ring).sum” |> ISPEC “#1” |> ISPEC “0 :num”
                   |> SIMP_RULE bool_ss [FUNPOW_0] |> GEN “r:'a ring”
(* val ring_num_0 = |- !r. ##0 = #0: thm *)

(* Obtain another theorem *)
Theorem ring_num_one =
    monoid_exp_def |> ISPEC “(r:'a ring).sum” |> ISPEC “#1” |> ISPEC “1 :num”
                   |> SIMP_RULE bool_ss [FUNPOW_1] |> GEN “r:'a ring”
(* val ring_num_one = |- !r. ##1 = #1 + #0: thm *)
(* Do not export this one: an expansion. *)

(* Theorem: ##1 = #1 *)
(* Proof: by group_exp_1. *)
val ring_num_1 = lift_group_exp "1" "1";
(* > val ring_num_1 = |- !r. Ring r ==> (##1 = #1) : thm *)

val _ = export_rewrites ["ring_num_1"];

(* Theorem: ##2 = #1 + #1 *)
(* Proof:
   ##2 = ##(SUC 1)    by TWO
       = #1 + ##1     by ring_num_SUC
       = #1 + #1      by ring_num_1
*)
val ring_num_2 = store_thm(
  "ring_num_2",
  ``!r:'a ring. Ring r ==> (##2 = #1 + #1)``,
  metis_tac[TWO, ring_num_SUC, ring_num_1]);

local
val rag = ring_add_group |> SPEC_ALL |> UNDISCH_ALL
val rgroup = rag |> CONJUNCT1
val rsc = rag |> CONJUNCT2 |> CONJUNCT1
val rze = ring_zero_element |> SPEC_ALL |> UNDISCH_ALL
in
fun lift_group_id_exp gsuffix rsuffix = let
  val gthm = DB.fetch "group" ("group_" ^ gsuffix)
  val gthm' = gthm |> SPEC ``(r:'a ring).sum`` |> UNDISCH
in
  save_thm("ring_" ^ rsuffix,
           gthm' |> PROVE_HYP rgroup
                 |> REWRITE_RULE [rsc, rze]
                 |> DISCH_ALL |> GEN_ALL)
end
end; (* local *)

(* Theorem: r.sum.exp #0 n = #0 *)
(* Proof: by group_id_exp and ring_num_def. *)
val ring_sum_zero = lift_group_id_exp "id_exp" "sum_zero";
(* > val ring_sum_zero = |- !r. Ring r ==> !n. r.sum.exp #0 n = #0 : thm *)

(* Theorem: #1 = #0 ==> !c. ##c = #0 *)
(* Proof:
   #1 = #0 ==> R = {#0}   by ring_one_eq_zero
   since ##c IN R         by ring_num_element
   ##c = #0               by IN_SING
*)
val ring_num_all_zero = store_thm(
  "ring_num_all_zero",
  ``!r:'a ring. Ring r ==> ((#1 = #0) ==> (!c. ##c = #0))``,
  metis_tac [IN_SING, ring_one_eq_zero, ring_num_element]);

(* ------------------------------------------------------------------------- *)
(* Ring Exponent Theorems (from monoid_exp of ring_mult_monoid).             *)
(* ------------------------------------------------------------------------- *)


local
val rmm = ring_mult_monoid |> SPEC_ALL |> UNDISCH_ALL
val rmonoid = rmm |> CONJUNCT1
val rpc = rmm |> CONJUNCT2 |> CONJUNCT1
in
fun lift_monoid_def gsuffix rsuffix = let
  val gthm = DB.fetch "monoid" ("monoid_" ^ gsuffix)
  val gthm' = gthm |> SPEC ``(r:'a ring).prod`` (* no UNDISCH *)
in
  save_thm("ring_" ^ rsuffix,
           gthm' |> PROVE_HYP rmonoid
                 |> REWRITE_RULE [rpc]
                 |> DISCH_ALL |> GEN_ALL)
end
end; (* local *)

(* Theorem: x ** n IN R *)
(* Proof: by monoid_exp_carrier. *)
val ring_exp_element = lift_monoid_thm "exp_element" "exp_element";
(* > val ring_exp_element = |- !r. Ring r ==> !x. x IN R ==> !n. x ** n IN R : thm *)

val _ = export_rewrites ["ring_exp_element"];

(* Theorem: x ** 0 = #1 *)
(* Proof: by monoid_exp_0. *)
(* Note: monoid_exp_0 |- !g x. x ** 0 = #e *)
Theorem ring_exp_0[simp]: !x:'a. x ** 0 = #1
Proof rw[]
QED

(* Theorem: x ** (SUC n) = x * x ** n  *)
(* Proof: by monoid_exp_SUC. *)
(* Note: monoid_exp_SUC |- !g x n. x ** SUC n = x * x ** n *)
Theorem ring_exp_SUC[simp]: !x n. x ** SUC n = x * x ** n
Proof rw[]
QED

(* Theorem: x ** SUC n = x ** n * x *)
(* Proof: by ring_exp_SUC and ring_mult_comm. *)
val ring_exp_suc = store_thm(
  "ring_exp_suc",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !n. x ** (SUC n) = (x ** n) * x``,
  rw[ring_mult_comm]);

(* Theorem: x ** 1 = x *)
(* Proof: by monoid_exp_1. *)
val ring_exp_1 = lift_monoid_thm "exp_1" "exp_1";
(* > val ring_exp_1 = |- !r. Ring r ==> !x. x IN R ==> (x ** 1 = x) : thm *)

val _ = export_rewrites ["ring_exp_1"];

(* Theorem: x ** n * x = x * x ** n *)
(* Proof: by monoid_exp_comm. *)
val ring_exp_comm = lift_monoid_thm "exp_comm" "exp_comm";
(* > val ring_exp_comm = |- !r. Ring r ==> !x. x IN R ==> !n. x ** n * x = x * x ** n: thm *)

(* Theorem: (x * y) ** n = x ** n * y ** n *)
(* Proof: by monoid_comm_op_exp. *)
val ring_mult_exp = store_thm(
  "ring_mult_exp",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> !n. (x * y) ** n = x ** n * y ** n``,
  rw_tac std_ss[monoid_comm_op_exp, ring_mult_monoid]);

val _ = export_rewrites ["ring_mult_exp"];

(* Theorem: computation of small values of ring_exp *)
(* Proof: apply ring_exp_SUC. *)
val ring_exp_small = store_thm(
  "ring_exp_small",
  ``!r:'a ring. Ring r ==> !x. x IN R ==>
       (x ** 0 = #1) /\
       (x ** 1 = x) /\
       (x ** 2 = x * x) /\
       (x ** 3 = x * (x ** 2)) /\
       (x ** 4 = x * (x ** 3)) /\
       (x ** 5 = x * (x ** 4)) /\
       (x ** 6 = x * (x ** 5)) /\
       (x ** 7 = x * (x ** 6)) /\
       (x ** 8 = x * (x ** 7)) /\
       (x ** 9 = x * (x ** 8))``,
  rpt strip_tac >>
  `(2 = SUC 1) /\ (3 = SUC 2) /\ (4 = SUC 3) /\ (5 = SUC 4) /\
   (6 = SUC 5) /\ (7 = SUC 6) /\ (8 = SUC 7) /\ (9 = SUC 8)` by decide_tac >>
  metis_tac[ring_exp_SUC, ring_exp_1, ring_exp_0]);

(* ------------------------------------------------------------------------- *)
(* Ring Distribution Theorems.                                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: x * (y + z) = x * y + x * z *)
(* Proof: by definition. *)
val ring_mult_radd = save_thm("ring_mult_radd",
  Ring_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH_ALL |> CONJUNCTS |> last |> DISCH_ALL |> GEN_ALL);
(* > val ring_mult_radd = |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x * (y + z) = x * y + x * z) : thm *)

val _ = export_rewrites ["ring_mult_radd"];

(* Theorem: (y + z) * x = y * x + z * x *)
(* Proof: by ring_mult_radd and ring_mult_comm. *)
val ring_mult_ladd = store_thm(
  "ring_mult_ladd",
  ``!r:'a ring. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((y + z) * x = y * x + z * x)``,
  rw[ring_mult_comm]);

val _ = export_rewrites ["ring_mult_ladd"];

(*
- ring_mult_radd |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH;
> val it =  [..] |- x * (y + z) = x * y + x * z : thm
- ring_mult_ladd |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH;
> val it =  [..] |- (y + z) * x = y * x + z * x : thm
- CONJ (ring_mult_radd |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH)
       (ring_mult_ladd |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH) |> DISCH_ALL |> GEN_ALL;
> val it = |- !z y x r. x IN R /\ y IN R /\ z IN R ==>
              Ring r ==> (x * (y + z) = x * y + x * z) /\ ((y + z) * x = y * x + z * x) : thm
- CONJ (ring_mult_radd |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH)
       (ring_mult_ladd |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH) |> DISCH ``x IN R /\ y IN R /\ z IN R``
       |> DISCH_ALL |> GEN_ALL;
> val it = |- !z y x r. Ring r ==>
               x IN R /\ y IN R /\ z IN R ==> (x * (y + z) = x * y + x * z) /\ ((y + z) * x = y * x + z * x) : thm
- CONJ (ring_mult_radd |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH)
       (ring_mult_ladd |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH) |> DISCH ``x IN R /\ y IN R /\ z IN R`` |> GEN_ALL
       |> DISCH_ALL |> GEN_ALL;
> val it = |- !r. Ring r ==> !z y x. x IN R /\ y IN R /\ z IN R ==>
      (x * (y + z) = x * y + x * z) /\ ((y + z) * x = y * x + z * x) : thm
*)

(* Theorem: x * (y + z) = x * y + x * z /\ (y + z) * x = y * x + z * x *)
(* Proof: by ring_mult_ladd and ring_mult_radd. *)
val ring_mult_add = save_thm("ring_mult_add",
    CONJ (ring_mult_radd |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH)
         (ring_mult_ladd |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> UNDISCH)
         |> DISCH ``x IN R /\ y IN R /\ z IN R`` |> GEN_ALL
         |> DISCH_ALL |> GEN_ALL);
(* > val ring_mult_add =
    |- !r. Ring r ==> !z y x. x IN R /\ y IN R /\ z IN R ==>
           (x * (y + z) = x * y + x * z) /\ ((y + z) * x = y * x + z * x) : thm *)

(* Theorem: ##(SUC n) * x = (##n) * x + x *)
(* Proof:
     ##(SUC n) * x
   = (##n + #1) * x            by ring_num_suc
   = ##n * x + #1 * x          by ring_mult_ladd
   = ##n * x + x               by ring_mult_lone
*)
val ring_num_mult_suc = store_thm(
  "ring_num_mult_suc",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !n. ##(SUC n) * x = ##n * x + x``,
  rw[ring_add_comm]);

(* Theorem: computation of small values of ring multiplication with ##n. *)
(* Proof: apply ring_num_mult_suc. *)
val ring_num_mult_small = store_thm(
  "ring_num_mult_small",
  ``!r:'a ring. Ring r ==> !x. x IN R ==>
       (#0 * x = #0) /\
       (#1 * x = x) /\
       (##2 * x = x + x) /\
       (##3 * x = ##2 * x + x)``,
  rw_tac std_ss[RES_FORALL_THM] >-
  rw[] >-
  rw[] >-
  (`2 = SUC 1` by decide_tac >> metis_tac[ring_num_mult_suc, ring_mult_lone, ring_num_1]) >>
  (`3 = SUC 2` by decide_tac >> metis_tac[ring_num_mult_suc]));

(* ------------------------------------------------------------------------- *)
(* Ring Negation Theorems                                                    *)
(* ------------------------------------------------------------------------- *)

(* old:
val ring_neg_def = Define `ring_neg (r:'a ring) = r.sum.inv`;
val _ = overload_on ("numeric_negate", ``ring_neg r``); (* unary negation *)
*)
val _ = overload_on ("numeric_negate", ``r.sum.inv``); (* unary negation *)

(* Theorem: Ring negatives in carrier. *)
(* Proof: by group_inv_element. *)
val ring_neg_element = lift_group_thm "inv_element" "neg_element";
(* > val ring_neg_element = |- !r. Ring r ==> !x. x IN R ==> -x IN R : thm *)

val _ = export_rewrites ["ring_neg_element"];

(* Theorem: - #0 = #0 *)
(* Proof: by group_inv_id. *)
val ring_neg_zero = lift_group_thm "inv_id" "neg_zero";
(* > val ring_neg_zero = |- !r. Ring r ==> (-#0 = #0) : thm *)

val _ = export_rewrites ["ring_neg_zero"];

(* Theorem: (-x) + x = #0 *)
(* Proof: by group_linv. *)
val ring_add_lneg = lift_group_thm "linv" "add_lneg";
(* > val ring_add_lneg = |- !r. Ring r ==> !x. x IN R ==> (-x + x = #0) : thm *)

(* Theorem: x + (-x) = #0 *)
(* Proof: by group_rinv. *)
val ring_add_rneg = lift_group_thm "rinv" "add_rneg";
(* > val ring_add_rneg = |- !r. Ring r ==> !x. x IN R ==> (x + -x = #0) : thm *)

val _ = export_rewrites ["ring_add_lneg", "ring_add_rneg"];

(* Theorem:  x + (-x + y) = y /\ (-x) + (x + y) = y *)
(* Proof: by group_linv_assoc. *)
val ring_add_lneg_assoc = lift_group_thm "linv_assoc" "add_lneg_assoc";
(* > val ring_add_lneg_assoc = |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (y = x + (-x + y)) /\ (y = -x + (x + y)) : thm *)

(* Theorem: y + -x + x = y /\ y + x + -x = y *)
(* Proof: by group_rinv_assoc. *)
val ring_add_rneg_assoc = lift_group_thm "rinv_assoc" "add_rneg_assoc";
(* > val ring_add_rneg_assoc = |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (y = y + -x + x) /\ (y = y + x + -x) : thm *)

(* Theorem: [Left-cancellation] (x + y = x + z) = (y = z) *)
(* Proof: by group_lcancel. *)
val ring_add_lcancel = lift_group_thm "lcancel" "add_lcancel";
(* > val ring_add_lcancel = |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((x + y = x + z) <=> (y = z)) : thm *)

(* Theorem: [Right-cancellation] (y + x = z + x) = (y = z) *)
(* Proof: by group_rcancel. *)
val ring_add_rcancel = lift_group_thm "rcancel" "add_rcancel";
(* > val ring_add_rcancel = |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((y + x = z + x) <=> (y = z)) : thm *)

(* Theorem: x = x + x <=> x = #0 *)
(* Proof: by group_id_fix. *)
val ring_zero_fix = lift_group_thm "id_fix" "zero_fix";
(* > val ring_zero_fix = |- !r. Ring r ==> !x. x IN R ==> ((x + x = x) <=> (x = #0)) : thm *)

(* Theorem: - (- x) = x *)
(* Proof: by group_inv_inv for r.sum group. *)
val ring_neg_neg = lift_group_thm "inv_inv" "neg_neg";
(* > val ring_neg_neg = |- !r. Ring r ==> !x. x IN R ==> (--x = x) : thm *)

val _ = export_rewrites ["ring_neg_neg"];

(* Theorem: -x = #0 <=> x = #0 *)
(* Proof: by group_inv_eq_id. *)
val ring_neg_eq_zero = lift_group_thm "inv_eq_id" "neg_eq_zero";
(* > val ring_neg_eq_zero = |- !r. Ring r ==> !x. x IN R ==> ((-x = #0) <=> (x = #0)) : thm *)

(* Theorem: - x = - y <=> x = y *)
(* Proof: by group_inv_eq for r.sum group. *)
val ring_neg_eq = lift_group_thm "inv_eq" "neg_eq";
(* > val ring_neg_eq = |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> ((-x = -y) <=> (x = y)) : thm *)

(* Theorem: -x = y <=> x = - y *)
(* Proof: by group_inv_eq_swap. *)
val ring_neg_eq_swap = lift_group_thm "inv_eq_swap" "neg_eq_swap";
(* > val ring_neg_eq_swap = |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> ((-x = y) <=> (x = -y)) : thm *)

(* Theorem: x + y = #0 <=> y = -x  *)
(* Proof: by group_rinv_unique for r.sum group. *)
val ring_add_eq_zero = lift_group_thm "rinv_unique" "add_eq_zero";
(* > val ring_add_eq_zero = |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> ((x + y = #0) <=> (y = -x)) : thm *)

(* Theorem: - (x + y) = -y + -x *)
(* Proof: by group_inv_op for r.sum group. *)
val ring_neg_add_comm = lift_group_thm "inv_op" "neg_add_comm";
(* > val ring_neg_add_comm = |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (-(x + y) = -y + -x) : thm *)

(* Theorem: For ring, - (x + y) = -x + -y *)
(* Proof: by ring_neg_add_comm and ring_add_comm. *)
val ring_neg_add = store_thm(
  "ring_neg_add",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> (- (x + y) = -x + -y)``,
  rw[ring_neg_add_comm, ring_add_comm]);

val _ = export_rewrites ["ring_neg_add"];

(* ------------------------------------------------------------------------- *)
(* Ring Distribution Theorems with Negation.                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: -x * y = - (x * y) *)
(* Proof:
     (x * y) + (-x * y)
   = (x + -x)* y            by ring_mult_ladd
   = #0 * y                 by ring_add_rneg
   = #0                     by ring_mult_lzero
   Hence -x * y = - (x*y)   by ring_add_eq_zero
*)
val ring_mult_lneg = store_thm(
  "ring_mult_lneg",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> (- x * y = - (x * y))``,
  rpt strip_tac >>
  `- x IN R /\ x * y IN R /\ - x * y IN R` by rw[] >>
  `x * y + (- x) * y = (x + -x) * y` by rw_tac std_ss[ring_mult_ladd] >>
  metis_tac[ring_add_eq_zero, ring_add_rneg, ring_mult_lzero]);

(* Theorem: x * - y = - (x * y) *)
(* Proof: by ring_mult_lneg and ring_mult_comm. *)
val ring_mult_rneg = store_thm(
  "ring_mult_rneg",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> (x * - y = - (x * y))``,
  metis_tac[ring_mult_lneg, ring_mult_comm, ring_neg_element]);

val _ = export_rewrites ["ring_mult_lneg", "ring_mult_rneg"];

(* Theorem: -(x * y) = -x * y  and -(x * y) = x * -y *)
(* Proof: by ring_mult_lneg and ring_mult_rneg. *)
val ring_neg_mult = store_thm(
  "ring_neg_mult",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> (- (x * y) = - x * y) /\ (- (x * y) = x * - y)``,
  rw[]);

(* Theorem: - x * - y = x * y *)
(* Proof:
     - x * - y
   = - (x * - y)     by ring_mult_lneg
   = - (- (x * y))   by ring_mult_rneg
   = x * y           by ring_mult_neg_neg
*)
val ring_mult_neg_neg = store_thm(
  "ring_mult_neg_neg",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> (- x * - y = x * y)``,
  metis_tac[ring_mult_lneg, ring_mult_rneg, ring_neg_neg, ring_neg_element]);

val _ = export_rewrites ["ring_neg_mult", "ring_mult_neg_neg" ];

(* ------------------------------------------------------------------------- *)
(* More Ring Numeral Theorems (involving distribution eventually).           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: ##(n + k) = ##n + ##k *)
(* Proof: by  group_exp_add. *)
val ring_num_add = lift_group_exp "add" "add";
(* > val ring_num_add = |- !r. Ring r ==> !n k. ##(n + k) = ##n + ##k : thm *)

(* Theorem: ##m + (##n + x) = ##(m+n) + x *)
(* Proof: by ring_num_add.
     ##m + (##n + x)
   = ##m + ##n + x     by ring_add_assoc
   = ##(m + n) + x     by ring_num_add
*)
val ring_num_add_assoc = store_thm(
  "ring_num_add_assoc",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !m n. ##m + (##n + x) = ##(m + n) + x``,
  metis_tac[ring_num_add, ring_add_assoc, ring_num_element]);

(* Theorem: ##m * ##n = ##(m * n) *)
(* Proof: by induction on m.
   Base case: !n. #0 * ##n = ##(0 * n)
      #0 * ##n
    = #0                    by ring_mult_lzero
    = ##(0 * n)             by MULT
   Step case: !n. ##m * ##n = ##(m * n) ==> !n. ##(SUC m) * ##n = ##(SUC m * n)
      ##(SUC m) * ##n
    = (##m + #1) * ##n      by ring_num_suc
    = ##m * ##n + #1 * ##n  by ring_mult_ladd
    = ##(m * n) + #1 * ##n  by induction hypothesis
    = ##(m * n) + ##n       by ring_mult_lone
    = ##(m * n + n)         by ring_num_add
    = ##(SUC m * n)         by MULT
*)
val ring_num_mult = store_thm(
  "ring_num_mult",
  ``!r:'a ring. Ring r ==> !m n. (##m) * (##n) = ##(m * n)``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  rpt strip_tac >>
  `##(SUC m) * ##n = (##m + #1) * ##n` by rw_tac std_ss[ring_num_suc] >>
  `_ = ##(m * n) + ##n` by rw[ring_mult_ladd] >>
  rw_tac std_ss[ring_num_add, MULT]);

(* Theorem: ##m * (##n * x) = ##(m * n) * x *)
(* Proof: by ring_num_mult.
     ##m * (##n * x)
   = ##m * ##n * x      by ring_mult_assoc
   = ##(m * n) * x     by ring_num_mult
*)
val ring_num_mult_assoc = store_thm(
  "ring_num_mult_assoc",
  ``!r:'a ring. Ring r ==> !m n x. x IN R ==> ((##m) * (##n * x) = ##(m * n) * x)``,
  metis_tac[ring_num_mult, ring_mult_assoc, ring_num_element]);

(* Theorem: (##m) ** n = ##(m**n) *)
(* Proof: by induction on n.
   Base case: ##m ** 0 = ##(m ** 0)
      ##m ** 0
    = #1               by ring_exp_0
    = ##(m ** 0)        by EXP
   Step case: ##m ** n = ##(m ** n) ==> ##m ** SUC n = ##(m ** SUC n)
      ##m ** SUC n
    = ##m ** n * ##m     by ring_exp_suc
    = ##(m ** n) * ##m   by induction hypothesis
    = ##(m ** n * m)    by ring_num_mult
    = ##(m ** SUC n)    by EXP
*)
val ring_num_exp = store_thm(
  "ring_num_exp",
  ``!r:'a ring. Ring r ==> !m n. (##m) ** n = ##(m ** n)``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[ring_num_mult, EXP]);

(* Theorem: ##(m + n) * x = ##m * x + ##n * x *)
(* Proof:
     ##(m + n) * x
   = (##m + ##n) * x     by ring_num_add
   = ##m * x + ##n * x   by ring_mult_ladd
*)
val ring_num_add_mult = store_thm(
  "ring_num_add_mult",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !m n. ##(m + n) * x = ##m * x + ##n * x``,
  metis_tac[ring_num_add, ring_mult_ladd, ring_num_element]);

(* Theorem: ##(m + n) * x + y = ##m * x + (##n * x + y) *)
(* Proof: by ring_num_add_mult.
     ##(m + n) * x + y
   = ##m * x + ##n * x + y     by ring_num_add_mult
   = ##m * x + (##n * x + y)   by ring_add_assoc
*)
val ring_num_add_mult_assoc = store_thm(
  "ring_num_add_mult_assoc",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> !m n. ##(m + n) * x + y = ##m * x + (##n * x + y)``,
  rw_tac std_ss[ring_num_add_mult, ring_add_assoc, ring_num_mult_element]);

(* Theorem: - (##n * x) = ##n * (- x) *)
(* Proof: by ring_mult_rneg. *)
val ring_num_mult_neg = store_thm(
  "ring_num_mult_neg",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !n. - (##n * x) = ##n * (- x)``,
  rw_tac std_ss[ring_mult_rneg, ring_num_element]);

(* Theorem: ##n * (x + y) = ##n * x + ##n * y *)
(* Proof: by ring_mult_radd. *)
val ring_num_mult_radd = store_thm(
  "ring_num_mult_radd",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> !n. ##n * (x + y) = ##n * x + ##n * y``,
  rw[]);

(* Theorem: x + x = ##2 * x *)
(* Proof: by ring_num_mult_small. *)
val ring_single_add_single = store_thm(
  "ring_single_add_single",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> (x + x = ##2 * x)``,
  rw_tac std_ss[ring_num_mult_small]);

(* Theorem: x + (x + y) = ##2 * x + y *)
(* Proof: by ring_single_add_single. *)
val ring_single_add_single_assoc = store_thm(
  "ring_single_add_single_assoc",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> (x + (x + y) = ##2 * x + y)``,
  metis_tac[ring_single_add_single, ring_add_assoc]);

(* Theorem: x + ##n * x = ##(n+1) * x *)
(* Proof:
     x + ##n * x
   = #1 * x + ##n * x   by ring_mult_lone
   = ##(1 + n) * x      by ring_num_add_mult
   = ##(n+1) * x        by ADD_COMM
*)
val ring_single_add_mult = store_thm(
  "ring_single_add_mult",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !n. x + ##n * x = ##(n + 1) * x``,
  metis_tac[ring_mult_lone, ring_num_add_mult, ring_num_1, ADD_COMM]);

(* Theorem: x + (##n * x + y) = ##(n+1) * x + y *)
(* Proof: by ring_single_add_mult.
     x + (##n * x + y)
   = x + ##n * x + y     by ring_add_assoc
   = ##(n+1) * x + y     by ring_single_add_mult
*)
val ring_single_add_mult_assoc = store_thm(
  "ring_single_add_mult_assoc",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> !n. x + (##n * x + y) = ##(n + 1) * x + y``,
  rw_tac std_ss[RES_FORALL_THM] >>
  `x + (##n * x + y) = x + ##n * x + y` by rw[ring_add_assoc] >>
  rw_tac std_ss[ring_single_add_mult]);

(* Theorem: x + - (##n * x) = (n = 0) ? x : - ##(n-1) * x *)
(* Proof: by cases on n.
   case n = 0:
     x + - (#0 * x)
   = x + - #0       by ring_mult_lzero
   = x + #0         by ring_neg_zero
   = x              by ring_add_rzero
   case n <> 0:
     x + - (##n * x)
   = - - x + - (##n * x)            by ring_neg_neg
   = - (- x + ##n * x)              by ring_neg_add
   = - (- x + (#1 * x + ##(n-1)*x)) by ring_num_add_mult, n = 1 + (n-1) for n <> 0
   = - (- x + (x + ##(n-1) * x))    by ring_mult_lone
   = - (##(n-1) * x)                by ring_add_assoc, ring_add_lneg, ring_add_lzero
*)
val ring_single_add_neg_mult = store_thm(
  "ring_single_add_neg_mult",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !n. x + -(##n * x) = if n = 0 then x else -(##(n - 1) * x)``,
  rpt strip_tac >>
  rw_tac std_ss[ring_num_0] >-
  rw_tac std_ss[ring_mult_lzero, ring_neg_zero, ring_add_rzero] >>
  `n = 1 + (n-1)` by decide_tac >>
  `#1 IN R /\ - #1 IN R /\ -x IN R /\ ##n IN R /\ ##(n-1) IN R` by rw[] >>
  `x + - (##n * x) = - (- x + ##n * x)` by rw_tac std_ss[ring_neg_neg, ring_neg_add, ring_num_mult_element] >>
  `_ = - (-x + (#1 * x + ##(n-1) * x))` by metis_tac[ring_num_add_mult, ring_num_1] >>
  `_ = - (-x + x + ##(n-1) * x)` by rw[ring_add_assoc] >>
  rw_tac std_ss[ring_add_lneg, ring_add_lzero, ring_num_mult_element]);

(* Theorem: x + (- ##n * x + y) = (n = 0) ? x + y : - ##(n-1) * x + y  *)
(* Proof: by ring_single_add_neg_mult. *)
val ring_single_add_neg_mult_assoc = store_thm(
  "ring_single_add_neg_mult_assoc",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==>
   !n. x + ((- (##n * x)) + y) = if n = 0 then x + y else - (##(n - 1) * x) + y``,
  rpt strip_tac >>
  `x + ((- ((##n) * x)) + y) = x + (- ((##n) * x)) + y`
    by rw_tac std_ss[ring_add_assoc, ring_num_mult_element, ring_neg_element] >>
  rw_tac std_ss[ring_single_add_neg_mult]);

(* Theorem: ##n * x + - x = (n = 0) ? - x : ##(n - 1) * x *)
(* Proof: by cases on n.
   case n = 0:
     #0 * x + -x
   = #0 + -x        by ring_mult_lzero
   = -x             by ring_add_lzero
   case n <> 0:
     ##n * x + -x
   = ##(n-1) * x + #1 * x + -x  by ring_num_add_mult, n = (n-1) + 1 for n <> 0
   = ##(n-1) * x + (x + -x)     by ring_mult_lone, ring_add_assoc
   = ##(n-1) * x                by ring_add_rneg, ring_add_rzero
*)
val ring_mult_add_neg = store_thm(
  "ring_mult_add_neg",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !n. ##n * x + - x = if n = 0 then - x else ##(n - 1) * x``,
  rpt strip_tac >>
  rw_tac std_ss[ring_num_0] >-
  rw_tac std_ss[ring_mult_lzero, ring_add_lzero, ring_neg_element] >>
  `n = n-1 + 1` by decide_tac >>
  `##n IN R /\ ##(n-1) IN R /\ -x IN R` by rw[] >>
  `##n * x + - x = ##(n - 1) * x + #1 * x + - x` by metis_tac[ring_num_add_mult, ring_num_1] >>
  `_ = ##(n-1) * x + (x + - x)` by rw_tac std_ss[ring_mult_lone, ring_add_assoc, ring_mult_element] >>
  rw_tac std_ss[ring_add_rneg, ring_add_rzero, ring_mult_element]);

(* Theorem: ##n * x + (- x + y) = (n = 0) ? - x + y : ##(n - 1) * x + y *)
(* Proof: by ring_mult_add_neg. *)
val ring_mult_add_neg_assoc = store_thm(
  "ring_mult_add_neg_assoc",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> !n. ##n * x + (- x + y) = if n = 0 then - x + y else ##(n - 1) * x + y``,
  rpt strip_tac >>
  `##n * x + (- x + y) = ##n * x + - x + y` by rw[ring_add_assoc] >>
  metis_tac[ring_mult_add_neg]);

(* Theorem: ##m * x + - (##n * x) = if m < n then - (##(n - m) * x) else ##(m - n) * x *)
(* Proof: by cases on m < n.
   case m < n: n = m + (n - m)
     ##m * x + - (##n * x)
   = ##m * x + - (##m * x + ##(n-m) * x)   by ring_num_add_mult
   = ##m * x + - (##m * x) - ##(n-m) * x   by ring_neg_add, ring_add_assoc
   = - ##(n-m) * x                       by ring_add_rneg, ring_add_lzero
   case m >= n: m = (m - n) + n
     ##m * x + - (##n * x)
   = ##(m-n) * x + ##n * x + - (##n * x)   by ring_num_add_mult
   = ##(m-n) * x + (##n * x + - (##n * x)) by ring_add_assoc
   = ##(m-n) * x                         by ring_add_rneg, ring_add_rzero
*)
val ring_mult_add_neg_mult = store_thm(
  "ring_mult_add_neg_mult",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !m n. ##m * x + - (##n * x) = if m < n then - (##(n - m) * x) else ##(m - n) * x``,
  rpt strip_tac >>
  rw_tac std_ss[] >| [
    `n = m + (n - m)` by decide_tac >>
    `##m * x + - (##n * x) = ##m * x + - (##m * x + ##(n - m) * x)` by metis_tac[ring_num_add_mult] >>
    `_ = ##m * x + - (##m * x) + - (##(n-m) * x)`
      by rw_tac std_ss[ring_neg_add, ring_add_assoc, ring_num_mult_element, ring_neg_element] >>
    rw_tac std_ss[ring_add_rneg, ring_add_lzero, ring_num_mult_element, ring_neg_element],
    `m = m - n + n` by decide_tac >>
    `##m * x + - (##n * x) = ##(m - n) * x + ##n * x + - (##n * x)` by metis_tac[ring_num_add_mult] >>
    rw_tac std_ss[ring_add_assoc, ring_add_rneg, ring_add_rzero, ring_num_mult_element, ring_neg_element]
  ]);

(* Theorem: ##m * x + (- (##n * x) + y) = if m < n then - (##(n - m) * x) + y else ##(m - n) * x + y *)
(* Proof: by ring_mult_add_neg_mult. *)
val ring_mult_add_neg_mult_assoc = store_thm(
  "ring_mult_add_neg_mult_assoc",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==>
   !m n. ##m * x + (- (##n * x) + y) = if m < n then - (##(n - m) * x) + y else ##(m - n) * x + y``,
  rpt strip_tac >>
  `##m * x + (- (##n * x) + y) = ##m * x + - (##n * x) + y`
    by rw_tac std_ss[ring_add_assoc, ring_num_mult_element, ring_neg_element] >>
  rw_tac std_ss[ring_mult_add_neg_mult]);

(* Theorem: - x + - x = - (##2 * x) *)
(* Proof:
     - x + - x
   = - (x + x)     by ring_neg_add
   = - (##2 * x)   by ring_num_mult_small
*)
val ring_neg_add_neg = store_thm(
  "ring_neg_add_neg",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> (- x + - x = - (##2 * x))``,
  rw_tac std_ss[ring_neg_add, ring_num_mult_small]);

(* Theorem: - x + (- x + y) = - (##2 * x) + y *)
(* Proof: by ring_neg_add_neg. *)
val ring_neg_add_neg_assoc = store_thm(
  "ring_neg_add_neg_assoc",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> (- x + (- x + y) = - (##2 * x) + y)``,
  rpt strip_tac >>
  `- x + (- x + y) = - x + - x + y` by rw[ring_add_assoc] >>
  rw_tac std_ss[ring_neg_add_neg]);

(* Theorem:  - x + - (##n * x) = - (##(n + 1) * x) *)
(* Proof:
     - x + - (##n * x)
   = - x + ##n * (- x)    by ring_num_mult_neg
   = ##(n+1) * (- x)      by ring_single_add_mult
   = - (##(n+1) * x)      by ring_num_mult_neg
*)
val ring_neg_add_neg_mult = store_thm(
  "ring_neg_add_neg_mult",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !n. - x + - (##n * x) = - (##(n + 1) * x)``,
  rw_tac std_ss[ring_num_mult_neg, ring_single_add_mult, ring_neg_element]);

(* Theorem: - x + (- (##n * x) + y) = - (##(n + 1) * x) + y *)
(* Proof: by ring_neg_add_neg_mult. *)
val ring_neg_add_neg_mult_assoc = store_thm(
  "ring_neg_add_neg_mult_assoc",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> !n.  - x + (- (##n * x) + y) = - (##(n + 1) * x) + y``,
  rpt strip_tac >>
  `- x + (- (##n * x) + y) = - x + - (##n * x) + y`
    by rw_tac std_ss[ring_add_assoc, ring_num_mult_element, ring_neg_element] >>
  rw_tac std_ss[ring_neg_add_neg_mult]);

(* Theorem: - (##m * x) + - (##n * x) = - (##(m + n) * x) *)
(* Proof:
     - (##m * x) + - (##n * x)
   = ##m * (-x) + ##n * (-x)   by ring_num_mult_neg
   = ##(m + n) * (-x)         by ring_num_add_mult
   = - (##(m + n) * x)        by ring_num_mult_neg
*)
val ring_neg_mult_add_neg_mult = store_thm(
  "ring_neg_mult_add_neg_mult",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !m n. - (##m * x) + - (##n * x) = - (##(m + n) * x)``,
  rw_tac std_ss[ring_num_add_mult, ring_num_mult_neg, ring_neg_element]);

(* Theorem: - (##m * x) + (- (##n * x) + y) = - (##(m + n) * x) + y *)
(* Proof: by ring_neg_mult_add_neg_mult.
     - (##m * x) + (- (##n * x) + y)
   = - (##m * x) + -(##n * x) + y    by ring_add_assoc
   = - (##(m + n) * x) + y           by ring_neg_mult_add_neg_mult
*)
val ring_neg_mult_add_neg_mult_assoc = store_thm(
  "ring_neg_mult_add_neg_mult_assoc",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> !m n. - (##m * x) + (- (##n * x) + y) = - (##(m + n) * x) + y``,
  rpt strip_tac >>
  `- (##m * x) + (- (##n * x) + y) = - (##m * x) + - (##n * x) + y`
    by rw_tac std_ss[ring_add_assoc, ring_num_mult_element, ring_neg_element] >>
  rw_tac std_ss[ring_neg_mult_add_neg_mult]);

(* ------------------------------------------------------------------------- *)
(* More Ring Exponent Theorems.                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: x * x = x ** 2 *)
(* Proof: by ring_exp_small. *)
val ring_single_mult_single = store_thm(
  "ring_single_mult_single",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> (x * x = x ** 2)``,
  rw_tac std_ss[ring_exp_small]);

(* Theorem: x * (x * y) = x ** 2 * y *)
(* Proof: by ring_single_mult_single. *)
val ring_single_mult_single_assoc = store_thm(
  "ring_single_mult_single_assoc",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> (x * (x * y) = x ** 2 * y)``,
  metis_tac[ring_mult_assoc, ring_single_mult_single]);

(* Theorem: x * x ** n = x ** (n + 1) *)
(* Proof: by ring_exp_def. *)
val ring_single_mult_exp = store_thm(
  "ring_single_mult_exp",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !n. x * x ** n = x ** (n + 1)``,
  metis_tac[ring_exp_SUC, ADD1]);

(* Theorem: x * x ** n = x ** (n + 1) *)
(* Proof: by ring_single_mult_exp. *)
val ring_single_mult_exp_assoc = store_thm(
  "ring_single_mult_exp_assoc",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> !n. x * ((x ** n) * y) = (x ** (n + 1)) *  y``,
  rpt strip_tac >>
  `x * (x ** n * y) = x * x ** n * y` by rw_tac std_ss[ring_mult_assoc, ring_exp_element] >>
  rw_tac std_ss[ring_single_mult_exp]);

(* Theorem: x ** (n + k) = x ** n * x ** k *)
(* Proof: by monoid_exp_add. *)
val ring_exp_add = lift_monoid_thm "exp_add" "exp_add";
(* > val ring_exp_add = |- !r. Ring r ==> !x. x IN R ==> !n k. x ** (n + k) = x ** n * x ** k : thm *)

val _ = export_rewrites ["ring_exp_add"];

(* Theorem: x ** m * (x ** n * y) = x ** (m + n) * y *)
(* Proof: by ring_exp_add. *)
val ring_exp_add_assoc = store_thm(
  "ring_exp_add_assoc",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> !n k. x ** n * (x ** k * y) = x ** (n + k) * y``,
  rw_tac std_ss[ring_exp_add, ring_mult_assoc, ring_exp_element]);

(* Theorem: #1 ** n = #1 *)
(* Proof: by monoid_id_exp and r.prod a monoid. *)
val ring_one_exp = lift_monoid_thm "id_exp" "one_exp";
(* > val ring_one_exp = |- !r. Ring r ==> !n. #1 ** n = #1 : thm *)

val _ = export_rewrites ["ring_one_exp"];

(* Theorem: #0 ** n = (n = 0) ? #1 : #0 *)
(* Proof: by cases on n = 0.
   If n = 0, #0 ** 0 = #1                     by ring_exp_0.
   If n <> 0, #0 ** n = #0 * #0 ** (n-1) = #0 by ring_exp_SUC, ring_mult_lzero.
*)
val ring_zero_exp = store_thm(
  "ring_zero_exp",
  ``!r:'a ring. Ring r ==> !n. #0 ** n = if n = 0 then #1 else #0``,
  rpt strip_tac >>
  rw_tac std_ss[] >-
  rw[] >>
  `n = SUC (n-1)` by decide_tac >>
  metis_tac[ring_exp_SUC, ring_mult_lzero, ring_exp_element, ring_zero_element]);
(*
val ring_zero_exp = store_thm(
  "ring_zero_exp",
  ``!r:'a ring. Ring r ==> !n. #0 ** n = if n = 0 then #1 else #0``,
  rpt strip_tac >>
  rw_tac std_ss[] >-
  rw[] >>
  metis_tac[ring_exp_SUC, ring_mult_lzero, ring_exp_element, ring_zero_element, DECIDE ``n <> 0 ==> (n = SUC (n-1))``]);
*)

(* Theorem: x ** (m * n) = (x ** m) ** n *)
(* Proof: by monoid_exp_mult. *)
val ring_exp_mult = lift_monoid_thm "exp_mult" "exp_mult";
(* > val ring_exp_mult = |- !r. Ring r ==> !x. x IN R ==> !n k. x ** (n * k) = (x ** n) ** k : thm *)

val _ = export_rewrites ["ring_exp_mult"];

(* Theorem: Ring r ==> !x. x IN R ==> !n m. (x ** n) ** m = (x ** m) ** n *)
(* Theorem: x ** (m * n) = (x ** n) ** m *)
(* Proof: by monoid_exp_mult_comm. *)
val ring_exp_mult_comm = lift_monoid_thm "exp_mult_comm" "exp_mult_comm";
(* > val ring_exp_mult_comm = |- !r. Ring r ==> !x. x IN R ==> !m n. (x ** m) ** n = (x ** n) ** m: thm *)

(* Theorem: (-x) ** 2 = x ** 2 *)
(* Proof:
     ((-x) ** 2)
   = (-x) * (-x)    by ring_single_mult_single
   = - (- (x * x))  by ring_mult_lneg, ring_mult_rneg
   = x * x          by ring_neg_neg
   = x ** 2         by ring_single_mult_single
*)
val ring_neg_square = store_thm(
  "ring_neg_square",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> ((- x) ** 2 = x ** 2)``,
  metis_tac[ring_single_mult_single, ring_mult_lneg, ring_mult_rneg, ring_neg_neg, ring_neg_element]);

(* Theorem: (- x) ** n = if EVEN n then x ** n else - (x ** n) *)
(* Proof: by cases on EVEN n.
   case EVEN n: n = 2*m
     (-x) ** n
   = ((-x) ** 2) ** m      by ring_exp_mult
   = (x**2) ** m           by ring_neg_square
   = x ** n                by ring_exp_mult
   case ~EVEN n: n = 2*m + 1
      Since n <> 0, n = SUC(n-1) and EVEN (n-1).
     (-x) ** n
   = (-x) * (-x) ** (n-1)  by ring_exp_def, n = SUC(n-1)
   = (-x) * (x ** (n-1))   by EVEN (n-1)
   = -(x * x ** (n-1))     by ring_mult_lneg
   = - (x ** n)            by ring_exp_def
*)
val ring_exp_neg = store_thm(
  "ring_exp_neg",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !n. (- x) ** n = if EVEN n then x ** n else - (x ** n)``,
  rpt strip_tac >>
  `-x IN R` by rw[] >>
  `!n. EVEN n ==> ((-x) ** n = x ** n)` by
  (rw_tac std_ss[EVEN_EXISTS] >>
  metis_tac[ring_neg_square, ring_exp_mult]) >>
  rw_tac std_ss[] >>
  `n <> 0 ==> (n = SUC(n-1))` by decide_tac >>
  `EVEN (n-1) /\ (n = SUC(n-1))` by metis_tac[EVEN] >>
  metis_tac[ring_exp_SUC, ring_mult_lneg, ring_exp_element]);

(* Same theorem, better proof. *)

(* Theorem: Ring r ==> !x. x IN R ==>
            !n. -x ** n = if EVEN n then x ** n else -(x ** n) *)
(* Proof:
   By induction on n.
   Base case: -x ** 0 = if EVEN 0 then x ** 0 else -(x ** 0)
      LHS = -x ** 0
          = #1          by ring_exp_0
      RHS = x ** 0      by EVEN, EVEN 0 = T
          = #1 = LHS    by ring_exp_0
   Step case: -x ** n = if EVEN n then x ** n else -(x ** n) ==>
              -x ** SUC n = if EVEN (SUC n) then x ** SUC n else -(x ** SUC n)
      If EVEN n, ~EVEN (SUC n)     by EVEN
         -x ** SUC n
       = -x * (-x ** n)            by ring_exp_SUC
       = -x * x ** n               by induction hypothesis
       = -(x * x ** n)             by ring_mult_lneg
       = - x ** SUC n              by ring_exp_SUC
      If ~EVEN n, EVEN (SUC n)     by EVEN
         -x ** SUC n
       = -x * (-x ** n)            by ring_exp_SUC
       = -x * (-(x ** n))          by induction hypothesis
       = x * -(-(x ** n))          by ring_mult_lneg
       = x * x ** n                by ring_neg_neg
       = x ** SUC n                by ring_exp_SUC
*)
val ring_neg_exp = store_thm(
  "ring_neg_exp",
  ``!r:'a ring. Ring r ==> !x. x IN R ==>
   !n. -x ** n = if EVEN n then x ** n else -(x ** n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw_tac std_ss[ring_exp_SUC, EVEN] >-
  rw_tac std_ss[ring_mult_lneg, ring_exp_element] >>
  rw[]);

(* Theorem: ##k * ##m ** n = ##(k * m ** n) *)
(* Proof: by induction on n.
   Base case: ##k * ##m ** 0 = ##(k * m ** 0)
     LHS = ##k * ##m ** 0
         = ##k * #1          by ring_exp_0
         = ##k               by ring_mult_rone
         = ##(k * 1)         by MULT_RIGHT_1
         = ##(k * m ** 0)    by EXP: m ** 0 = 1
         = RHS
   Step case: ##k * ##m ** n = ##(k * m ** n) ==>
              ##k * ##m ** SUC n = ##(k * m ** SUC n)
      ##k * ##m ** SUC n
    = ##k * (##m * ##m ** n)   by ring_exp_SUC
    = ##k * ##m * ##m ** n     by ring_mult_assoc
    = ##m * ##k * ##m ** n     by ring_mult_comm
    = ##m * (##k * ##m ** n)   by ring_mult_assoc
    = ##m * ##(k * m ** n)     by induction hypothesis
    = ##(m * (k * m ** n))     by ring_num_mult
    = ##(m * k * m ** n)       by MULT_ASSOC
    = ##(k * m * m ** n)       by MULT_COMM
    = ##(k * (m * m ** n))     by MULT_ASSOC
    = ##(k * m ** SUC n)       by EXP
*)
val ring_num_mult_exp = store_thm(
  "ring_num_mult_exp",
  ``!r:'a ring. Ring r ==> !k m n. ##k * ##m ** n = ##(k * m ** n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[EXP] >>
  `##k * ##m ** SUC n = ##k * ##m * ##m ** n` by rw[ring_mult_assoc] >>
  `_ = ##m * ##k * ##m ** n` by rw_tac std_ss [ring_mult_comm, ring_num_element] >>
  `_ = ##m * ##(k * m ** n)` by rw[ring_mult_assoc] >>
  `_ = ##(m * k * m ** n)` by rw[ring_num_mult] >>
  `_ = ##(k * m * m ** n)` by rw_tac std_ss[MULT_COMM] >>
  rw[EXP]);

(* Theorem: Ring r ==> !x. x IN R /\ 0 < order r.prod x ==> !n. x ** n = x ** (n MOD (order r.prod x) *)
(* Proof:
   Since Ring r ==> Monoid r.prod    by ring_mult_monoid
   Hence result follows              by monoid_exp_mod_order, ring_carriers
*)
val ring_exp_mod_order = store_thm(
  "ring_exp_mod_order",
  ``!r:'a ring. Ring r ==> !x. x IN R /\ 0 < order r.prod x ==> !n. x ** n = x ** (n MOD (order r.prod x))``,
  metis_tac[ring_mult_monoid, monoid_exp_mod_order, ring_carriers]);

(* ------------------------------------------------------------------------- *)
(* Ring Subtraction Theorems.                                                *)
(* ------------------------------------------------------------------------- *)
val ring_sub_def = Define `ring_sub (r:'a ring) x y = x + (- y)`;
val _ = overload_on ("-", ``ring_sub r``);
val _ = export_rewrites ["ring_sub_def"];

(* Theorem: Ring r ==> x - #0 = x *)
(* Proof:
     x - #0
   = x + -#0    by ring_sub_def
   = x + #0     by ring_neg_zero
   = x          by ring_add_rzero
*)
val ring_sub_zero = store_thm(
  "ring_sub_zero",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> (x - #0 = x)``,
  rw[]);

(* Theorem: (x - y = #0) <=> (x = y) *)
(* Proof:
       x - y = #0
   <=> x + -y = #0   by ring_sub_def
   <=> -x = -y       by ring_add_eq_zero
   <=> x = y         by ring_neg_neg
*)
val ring_sub_eq_zero = store_thm(
  "ring_sub_eq_zero",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> ((x - y = #0) = (x = y))``,
  metis_tac[ring_sub_def, ring_add_eq_zero, ring_neg_neg, ring_neg_element]);

(* Theorem: x - x = #0 *)
(* Proof: by ring_sub_eq_zero. *)
val ring_sub_eq = store_thm(
  "ring_sub_eq",
  ``!r:'a ring. Ring r ==> !x y. x IN R ==> (x - x = #0)``,
  rw_tac std_ss[ring_sub_eq_zero]);

(* Theorem: x - y IN R *)
(* Proof: by definition, and ring_add_element, ring_neg_element. *)
val ring_sub_element = store_thm(
  "ring_sub_element",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> x - y IN R``,
  rw[]);

val _ = export_rewrites ["ring_sub_element"];

(* Theorem: Ring r ==> !x. x IN R ==> (#0 - x = -x) *)
(* Proof:
     #0 - x
   = #0 + (-x)       by ring_sub_def
   = -x              by ring_add_lzero
*)
val ring_zero_sub = store_thm(
  "ring_zero_sub",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> (#0 - x = -x)``,
  rw[]);

(* Theorem: Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((x - y = x - z) <=> (y = z)) *)
(* Proof:
   Note -y IN R /\ -z IN R       by ring_neg_element
           x - y = x - z
    <=> x + (-y) = x + (-z)      by ring_sub_def
    <=>       -y = -z            by ring_add_lcancel
    <=>        y = z             by ring_neg_neg
*)
val ring_sub_lcancel = store_thm(
  "ring_sub_lcancel",
  ``!r:'a ring. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((x - y = x - z) <=> (y = z))``,
  rw[ring_add_lcancel]);

(* Theorem: Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((y - x = z - x) <=> (y = z)) *)
(* Proof:
   Note -x IN R                  by ring_neg_element
           y - x = z - x
    <=> y + (-x) = z + (-x)      by ring_sub_def
    <=>        y = z             by ring_add_rcancel
*)
val ring_sub_rcancel = store_thm(
  "ring_sub_rcancel",
  ``!r:'a ring. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((y - x = z - x) <=> (y = z))``,
  rw[ring_add_rcancel]);

(* Theorem: -(x - y) = y - x *)
(* Proof:
     -(x - y)
   = -(x + -y)     by ring_sub_def
   = -x + --y      by ring_neg_add
   = -x + y        by ring_neg_neg
   = y + -x        by ring_add_comm
   = y - x         by ring_sub_def
*)
val ring_neg_sub = store_thm(
  "ring_neg_sub",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> (-(x - y) = y - x )``,
  rw[ring_sub_def, ring_add_comm]);

(* Theorem: x + y - y = x *)
(* Proof:
     x + y - y
   = x + y + -y     by ring_sub_def
   = x + (y + -y)   by ring_add_assoc, ring_neg_element
   = x + #0         by ring_add_rneg
   = x              by ring_add_rzero
*)
val ring_add_sub = store_thm(
  "ring_add_sub",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> (x + y - y = x)``,
  rw[ring_add_assoc]);

(* Theorem: y + x - y = x *)
(* Proof:
     y + x - y
   = x + y - y     by ring_add_comm
   = x             by ring_add_sub
*)
val ring_add_sub_comm = store_thm(
  "ring_add_sub_comm",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> (y + x - y = x)``,
  metis_tac[ring_add_sub, ring_add_comm]);

(* Theorem: Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x + y - z = x + (y - z)) *)
(* Proof:
     x + y - z
   = x + y + (-z)    by ring_sub_def
   = x + (y + (-z))  by ring_add_assoc, ring_neg_element
   = x + (y - z)     by ring_sub_def
*)
val ring_add_sub_assoc = store_thm(
  "ring_add_sub_assoc",
  ``!r:'a ring. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x + y - z = x + (y - z))``,
  rw_tac std_ss[ring_sub_def, ring_neg_element, ring_add_assoc]);

(* Theorem: x - y + y = x *)
(* Proof:
     x - y + y
   = x + -y + y     by ring_sub_def
   = x + (-y + y)   by ring_add_assoc, ring_neg_element
   = x + #0         by ring_add_lneg
   = x              by ring_add_rzero
*)
val ring_sub_add = store_thm(
  "ring_sub_add",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> (x - y + y = x)``,
  rw[ring_add_assoc]);

(* Theorem: x = y <=> x + z = y + z *)
(* This is ring_add_rcancel:
   |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((y + x = z + x) <=> (y = z)) *)

(* Theorem: x - y = z <=> x = y + z *)
(* Proof:
       x - y = z
   <=> x - y + y = z + y      by ring_add_sub
   <=>         x = z + y      by ring_sub_add
   <=>         x = y + z      by ring_add_comm
*)
val ring_sub_eq_add = store_thm(
  "ring_sub_eq_add",
  ``!r:'a ring. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((x - y = z) <=> (x = y + z))``,
  rpt strip_tac >>
  `(x - y = z) <=> (x - y + y = z + y)` by metis_tac[ring_add_sub, ring_sub_element] >>
  rw[ring_sub_add, ring_add_comm]);

(* Theorem: Ring r ==> (x + z) - (y + z) = x - y *)
(* Proof:
   Since Ring r ==> Group r.sum and r.sum.carrier = R   by ring_add_group
     (x + z) - (y + z)
   = (x + z) + (-(y + z))   by ring_sub_def
   = x + -y                 by group_pair_reduce
   = x - y                  by ring_sub_def

   Should use Theorem Lifting of group_pair_reduce.
*)
val ring_sub_pair_reduce = store_thm(
  "ring_sub_pair_reduce",
  ``!r:'a ring. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((x + z) - (y + z) = x - y)``,
  rw_tac std_ss[ring_sub_def, ring_add_group, group_pair_reduce]);

(* Theorem: Ring r ==> !x y z t. x IN R /\ y IN R /\ z IN R /\ t IN R ==>
                       ((x + y = z + t) <=> (x - z = t - y)) *)
(* Proof:
       x + y = z + t
   <=> x = z + t - y      by ring_add_sub, ring_sub_add, ring_add_element
   <=> x = z + (t - y)    by ring_add_assoc, ring_sub_def, ring_neg_element
   <=> x = (t - y) + z    by ring_add_comm, ring_sub_element
   <=> x - z = t - y      by ring_add_sub, ring_sub_element
*)
val ring_add_sub_identity = store_thm(
  "ring_add_sub_identity",
  ``!r:'a ring. Ring r ==> !x y z t. x IN R /\ y IN R /\ z IN R /\ t IN R ==>
    ((x + y = z + t) <=> (x - z = t - y))``,
  rpt strip_tac >>
  `(t - y) IN R /\ (z + t) IN R` by rw[] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    `x = z + t - y` by metis_tac[ring_add_sub] >>
    `_ = t - y + z` by rw[ring_add_comm, ring_add_assoc] >>
    metis_tac[ring_add_sub],
    `x = t - y + z` by metis_tac[ring_sub_add] >>
    `_ = z + t - y` by rw[ring_add_comm, ring_add_assoc] >>
    metis_tac[ring_sub_add]
  ]);

(* Theorem: Ring r ==> x * z - y * z = (x - y) * z *)
(* Proof:
     x * z - y * z
   = x * z + (- (y * z))    by ring_sub_def
   = x * z + (- y) * z      by ring_neg_mult
   = (x + (-y)) * z         by ring_mult_ladd
   = (x - y) * z            by ring_sub_def
*)
val ring_mult_lsub = store_thm(
  "ring_mult_lsub",
  ``!r:'a ring. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((x * z) - (y * z) = (x - y) * z)``,
  rw_tac std_ss[ring_neg_mult, ring_mult_ladd, ring_neg_element, ring_sub_def]);

(* Theorem: Ring r ==> x * y - x * z = x * (y - z) *)
(* Proof:
     x * y - x * z
   = y * x - z * x     by ring_mult_comm
   = (y - z) * x       by ring_mult_lsub
   = x * (y - z)       by ring_mult_comm, ring_sub_element
*)
val ring_mult_rsub = store_thm(
  "ring_mult_rsub",
  ``!r:'a ring. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x * y - x * z = x * (y - z))``,
  rpt strip_tac >>
  `x * y - x * z = y * x - z * x` by rw_tac std_ss[ring_mult_comm] >>
  `_ = (y - z) * x` by rw_tac std_ss[ring_mult_lsub] >>
  `_ = x * (y - z)` by rw_tac std_ss[ring_mult_comm, ring_sub_element] >>
  metis_tac[]);

(* Theorem: Ring r ==> x + y - (p + q) = (x - p) + (y - q)  *)
(* Proof:
     x + y - (p + q)
   = x + y + -(p + q)       by ring_sub_def
   = x + y + (- p + - q)    by ring_neg_add
   = (x + y + - p) + - q    by ring_add_assoc
   = (y + x + - p) + - q    by ring_add_comm
   = y + (x + - p) + - q    by ring_add_assoc
   = ((x + - p) + y) + - q  by ring_add_comm
   = (x + - p) + (y + - q)  by ring_add_assoc
   = (x - p) + (y - q)      by ring_sub_def
*)
val ring_add_pair_sub = store_thm(
  "ring_add_pair_sub",
  ``!r:'a ring. Ring r ==> !x y p q. x IN R /\ y IN R /\ p IN R /\ q IN R ==> (x + y - (p + q) = (x - p) + (y - q))``,
  rpt strip_tac >>
  `x + y - (p + q) = x + y + (- p + - q)` by rw[] >>
  `_ = (x + y + - p) + - q` by rw[ring_add_assoc] >>
  `_ = (y + x + - p) + - q` by rw_tac std_ss[ring_add_comm] >>
  `_ = y + (x + - p) + - q` by rw[ring_add_assoc] >>
  `_ = ((x + - p) + y) + - q` by rw_tac std_ss[ring_add_comm, ring_add_element, ring_neg_element] >>
  `_ = (x + - p) + (y + - q)` by rw[ring_add_assoc] >>
  `_ = (x - p) + (y - q)` by rw_tac std_ss[ring_sub_def] >>
  rw_tac std_ss[]);

(* Theorem: Ring r ==> x * y - p * q = (x - p) * (y - q) + (x - p) * q + p * (y - q) *)
(* Proof:
   (x - p) * (y - q) = x * y - x * q - p * y + p * q    by ring_mult_ladd, ring_mult_radd
   Hence
   x * y - p * q = (x - p) * (y - q) + x * q + p * y - p * q - p * q
                 = (x - p) * (y - q) + (x * q - p * q) + (p * y - p * q)
                 = (x - p) * (y - q) + (x - p) * q + p * (y - q)
*)
val ring_mult_pair_sub = store_thm(
  "ring_mult_pair_sub",
  ``!r:'a ring. Ring r ==> !x y p q. x IN R /\ y IN R /\ p IN R /\ q IN R ==>
               (x * y - p * q = (x - p) * (y - q) + (x - p) * q + p * (y - q))``,
  rw_tac std_ss[ring_sub_def] >>
  `-x IN R /\ -y IN R /\ -p IN R /\ -q IN R` by rw[] >>
  `(x + -p) IN R /\ (y + -q) IN R` by rw[] >>
  `(x + -p) * (y + -q) + (x + -p) * q + p * (y + -q) =
    (x + -p) * (y + -q + q) + p * (y + -q)` by rw_tac std_ss[ring_mult_radd] >>
  `_ = (x + -p) * y + p * (y + -q)` by rw_tac std_ss[ring_add_lneg, ring_add_rzero, ring_add_assoc] >>
  `_ = (x * y + -p * y) + (p * y + p * -q)` by rw_tac std_ss[ring_mult_ladd, ring_mult_radd] >>
  `_ = (x * y + -(p * y)) + (p * y + -(p * q))` by metis_tac[ring_neg_mult] >>
  `_ = x * y + (-(p * y) + p * y) + -(p * q)` by
    rw_tac std_ss[ring_add_assoc, ring_mult_element, ring_add_element, ring_neg_element] >>
  `_ = x * y + - (p * q)` by rw_tac std_ss[ring_mult_element, ring_add_lneg, ring_add_rzero] >>
  rw_tac std_ss[]);

(* Theorem: Ring r ==> !x y p q. x IN R /\ y IN R /\ p IN R /\ q IN R ==>
                       (x * y - p * q = (x - p) * y + p * (y - q)) *)
(* Proof:
     x * y - p * q
   = x * y + #0 - p * q                    by ring_add_rzero
   = x * y + (-(p * y) + p * y) - p * q    by ring_add_lneg
   = (x * y + -(p * y)) + p * y - p * q    by ring_add_assoc
   = (x * y - p * y) + p * y - p * q       by ring_sub_def
   = (x * y - p * y) + (p * y - p * q)     by ring_add_sub_assoc
   = (x - p) * y + (p * y - p * q)         by ring_mult_lsub
   = (x - p) * y + p * (y - q)             by ring_mult_rsub
*)
val ring_mult_pair_diff = store_thm(
  "ring_mult_pair_diff",
  ``!r:'a ring. Ring r ==> !x y p q. x IN R /\ y IN R /\ p IN R /\ q IN R ==>
       (x * y - p * q = (x - p) * y + p * (y - q))``,
  rpt strip_tac >>
  `!x y. x IN R /\ y IN R ==> -x IN R /\ (x * y) IN R` by rw[] >>
  `x * y - p * q = x * y + #0 - p * q` by rw_tac std_ss[ring_add_rzero] >>
  `_ = x * y + (-(p * y) + p * y) - p * q` by rw_tac std_ss[ring_add_lneg] >>
  `_ = x * y + -(p * y) + p * y - p * q` by prove_tac[ring_add_assoc] >>
  `_ = x * y - p * y + p * y - p * q` by rw_tac std_ss[ring_sub_def] >>
  `_ = (x * y - p * y) + (p * y - p * q)` by rw_tac std_ss[ring_add_sub_assoc, ring_sub_element] >>
  `_ = (x - p) * y + (p * y - p * q)` by rw_tac std_ss[ring_mult_lsub] >>
  `_= (x - p) * y + p * (y - q)` by rw_tac std_ss[ring_mult_rsub] >>
  rw_tac std_ss[]);

(* Theorem: Ring r ==> !n m. m < n ==> ##(n - m) = ##n - ##m *)
(* Proof:
   Since ##(n - m) + ##m = ##(n - m + m) = ##n
   and   ##n - ##m + ##m = ##n + (-##m + ##m) = ##n
   The results follows by ring_add_rcancel.
*)
val ring_num_sub = store_thm(
  "ring_num_sub",
  ``!r:'a ring. Ring r ==> !n m. m < n ==> (##(n - m) = ##n - ##m)``,
  rpt strip_tac >>
  `##(n - m) + ##m = ##(n - m + m)` by rw[] >>
  `_ = ##n` by rw_tac arith_ss[] >>
  `##n - ##m + ##m = ##n` by rw[ring_add_assoc] >>
  `##m IN R /\ ##(n - m) IN R /\ (##n - ##m) IN R` by rw[] >>
  metis_tac[ring_add_rcancel]);

(* ------------------------------------------------------------------------- *)
(* Ring Binomial Expansions.                                                 *)
(* ------------------------------------------------------------------------- *)

(* These may not be useful, but they demonstrate various HOL techniques to work against increasing complexity. *)

(* Theorem: (x + y) ** 2 = x ** 2 + ##2 * (x * y) + y ** 2 *)
(* Proof:
     (x + y) ** 2
   = (x + y) * (x + y)                  by ring_exp_small
   = x * (x + y) + y * (x + y)          by ring_mult_ladd
   = x * x + x * y + (y * x + y * y)    by ring_mult_radd
   = x * x + (x * y + (y * x + y * y))  by ring_add_assoc
   = x * x + (x * y + y * x + y * y)    by ring_add_assoc
   = x * x + (x * y + x * y + y * y)    by ring_mult_comm
   = x ** 2 + (x * y + x * y + y ** 2)  by ring_exp_small
   = x ** 2 + (##2 (x * y) + y **2)     by ring_num_mult_small
   = x ** 2 + ##2 (x * y) + y ** 2      by ring_add_assoc
*)
val ring_binomial_2 = store_thm(
  "ring_binomial_2",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> ((x + y) ** 2 = x ** 2 + ##2 * (x * y) + y ** 2)``,
  rw[ring_exp_small, ring_num_mult_small, ring_mult_comm, ring_add_assoc]);

(* Theorem: (x + y) ** 3 =
            x ** 3 + ##3 * (x ** 2 * y) + ##3 * (x * y ** 2) + y ** 3 *)
(* Proof:
     (x + y) ** 3
   = (x + y) * (x + y) ** 2                                                                              by ring_exp_small
   = (x + y) * (x ** 2 + ##2 * (x * y) + y ** 2)                                                        by ring_binomial_2
   = (x + y) * (x ** 2 + (##2 * (x * y) + y ** 2))                                                        by ring_add_assoc
   = x * (x ** 2 + (##2 * (x * y) + y ** 2)) + y * (x ** 2 + (##2 * (x * y) + y ** 2))                     by ring_mult_ladd
   = x * x ** 2 + x * (##2 * (x * y) + y ** 2) + (y * x ** 2 + y * (##2 * (x * y) + y ** 2))               by ring_mult_radd
   = x * x ** 2 + (x * (##2 * (x * y)) + x * y ** 2) + (y * x ** 2 + (y * (##2 * (x * y)) + y * y ** 2))   by ring_mult_radd
   = x * x ** 2 + ((##2 * (x * y)) * x + x * y ** 2) + (x ** 2 * y + ((##2 * (x * y)) * y + y * y ** 2))   by ring_mult_comm
   = x * x ** 2 + ((##2 * (x * y)) * x + (x * y ** 2 + x ** 2 * y + (##2 * (x * y)) * y + y * y ** 2))     by ring_add_assoc
   = x * x ** 2 + ((##2 * (x * y)) * x + (x ** 2 * y + x * y ** 2 + (##2 * (x * y)) * y + y * y ** 2))     by ring_add_comm
   = x * x ** 2 + ((##2 * (x * y)) * x + x ** 2 * y + (x * y ** 2 + ##2 * (x * y) * y + y * y ** 2))       by ring_add_assoc
   First cross term:
     ##2 * (x * y)) * x + x ** 2 * y
   = ##2 * (x * y * x) + x ** 2 * y      by ring_mult_assoc
   = ##2 * (x * (y * x)) + x ** 2 * y    by ring_mult_assoc
   = ##2 * (x * (x * y)) + x ** 2 * y    by ring_mult_comm
   = ##2 * (x * x * y) + x ** 2 * y      by ring_mult_assoc
   = ##2 * (x ** 2 * y) + x ** 2 * y     by ring_exp_small
   = x ** 2 * y + ##2 * (x ** 2 * y)     by ring_add_comm
   = ##3 * (x ** 2 * y)                  by ring_single_add_mult
   Next cross term:
     x * y ** 2 + ##2 * (x * y) * y
   = x * y ** 2 + ##2 * ((x * y) * y)    by ring_mult_assoc
   = x * y ** 2 + ##2 * (x * y * y)      by ring_mult_assoc
   = x * y ** 2 + ##2 * (x * (y * y))    by ring_mult_assoc
   = x * y ** 2 + ##2 * (x * y **2)      by ring_exp_small
   = ##3 * (x * y ** 2)                  by ring_single_add_mult
   Overall, apply ring_exp_small, ring_add_assoc.
*)
val ring_binomial_3 = store_thm(
  "ring_binomial_3",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==>
    ((x + y) ** 3 = x ** 3 + ##3 * (x ** 2 * y) + ##3 * (x * y ** 2) + y ** 3)``,
  rpt strip_tac >>
  `x ** 2 IN R /\ ##2 * (x * y) IN R /\ y ** 2 IN R` by rw[] >>
  `(x + y) ** 3 = (x + y) * (x ** 2 + ##2 * (x * y) + y ** 2)` by rw[ring_binomial_2, ring_exp_small] >>
  `_ = (x + y) * (x ** 2 + (##2 * (x * y) + y ** 2))` by rw[ring_add_assoc] >>
  `_ = x * x ** 2 + (x * (##2 * (x * y)) + x * y ** 2) + (y * x ** 2 + (y * (##2 * (x * y)) + y * y ** 2))` by rw[] >>
  `_ = x * x ** 2 + ((##2 * (x * y)) * x + x * y ** 2) + (x ** 2 * y + ((##2 * (x * y)) * y + y * y ** 2))`
    by rw[ring_mult_comm] >>
  `_ = x * x ** 2 + ((##2 * (x * y)) * x + (x * y ** 2 + x ** 2 * y + (##2 * (x * y)) * y + y * y ** 2))`
    by rw[ring_add_assoc] >>
  `_ = x * x ** 2 + ((##2 * (x * y)) * x + (x ** 2 * y + x * y ** 2 + (##2 * (x * y)) * y + y * y ** 2))`
    by rw[ring_add_comm] >>
  `_ = x * x ** 2 + ((##2 * (x * y)) * x + x ** 2 * y + (x * y ** 2 + ##2 * (x * y) * y + y * y ** 2))`
    by rw[ring_add_assoc] >>
  `(##2 * (x * y)) * x + x ** 2 * y = ##2 * (x * x * y) + x ** 2 * y` by rw[ring_mult_assoc, ring_mult_comm] >>
  `_ = ##2 * (x ** 2 * y) + x ** 2 * y` by rw[ring_exp_small] >>
  `_ = x ** 2 * y + ##2 * (x ** 2 * y)` by rw[ring_add_comm] >>
  `_ = ##3 * (x ** 2 * y)` by rw_tac std_ss[ring_single_add_mult, ring_mult_element] >>
  `x * y ** 2 + ##2 * (x * y) * y = x * y ** 2 + ##2 * (x * (y * y))` by rw[ring_mult_assoc] >>
  `_ = x * y ** 2 + ##2 * (x * y **2)` by rw[ring_exp_small] >>
  `_ = ##3 * (x * y ** 2)` by rw_tac std_ss[ring_single_add_mult, ring_mult_element] >>
  `x ** 3 + ##3 * (x ** 2 * y) + ##3 * (x * y ** 2) + y ** 3 =
   x ** 3 + (##3 * (x ** 2 * y) + (##3 * (x * y ** 2) + y ** 3))` by rw[ring_add_assoc] >>
  rw_tac std_ss[ring_exp_small]);

(* Theorem:  (x + y) ** 4 =
              x ** 4 + ##4 * (x ** 3 * y) + ##6 * (x ** 2 * y ** 2) + ##4 * (x * y ** 3) + y ** 4 *)
(* Proof:
     (x + y) ** 4
   = (x + y) * (x + y) ** 3                                                                 by ring_exp_small
   = (x + y) * (x ** 3 + ##3 * (x ** 2 * y) + ##3 * (x * y ** 2) + y ** 3)                  by ring_binomial_3
   = (x + y) * (x ** 3 + (##3 * (x ** 2 * y) + (##3 * (x * y ** 2) + y ** 3)))                by ring_add_assoc
   = x * (x ** 3 + (##3 * (x ** 2 * y) + (##3 * (x * y ** 2) + y ** 3))) +
        y * (x ** 3 + (##3 * (x ** 2 * y) + (##3 * (x * y ** 2) + y ** 3)))                   by ring_mult_ladd
   = (x * x ** 3 + (x * (##3 * (x ** 2 * y)) + (x * (##3 * (x * y ** 2)) + x * y ** 3))) +
        (y * x ** 3 + (y * (##3 * (x ** 2 * y)) + (y * (##3 * (x * y ** 2)) + y * y ** 3)))   by ring_mult_radd
   = (x * x ** 3 + (x * (##3 * (x ** 2 * y)) + x * (##3 * (x * y ** 2)) + x * y ** 3)) +
        (y * x ** 3 + (y * (##3 * (x ** 2 * y)) + y * (##3 * (x * y ** 2)) + y * y ** 3))     by ring_add_assoc
   = (x ** 4 + (x * (##3 * (x ** 2 * y)) + x * (##3 * (x * y ** 2)) + x * y ** 3)) +
        (y * x ** 3 + (y * (##3 * (x ** 2 * y)) + y * (##3 * (x * y ** 2)) + y ** 4))         by ring_exp_small

   Let  x3y = x ** 3 * y
       x2y2 = x ** 2 * y ** 2
        xy3 = x * y ** 3
   First term:
     x * (##3 * (x ** 2 * y))
   = ##3 * (x ** 2 * y) * x        by ring_mult_comm
   = ##3 * (x ** 2 * y * x)        by ring_mult_assoc
   = ##3 * (x ** 2 * (y * x))      by ring_mult_assoc
   = ##3 * (x ** 2 * (x * y))      by ring_mult_comm
   = ##3 * (x ** 2 * x * y)        by ring_mult_assoc
   = ##3 * (x * x ** 2 * y)        by ring_mult_comm
   = ##3 * (x ** 3 * y)            by ring_exp_small
   = ##3 * x3y
   Second term:
     x * (##3 * (x * y ** 2))
   = ##3 * (x * y ** 2) * x        by ring_mult_comm
   = ##3 * (x * y ** 2 * x)        by ring_mult_assoc
   = ##3 * (x * (y ** 2 * x))      by ring_mult_assoc
   = ##3 * (x * (x * y ** 2))      by ring_mult_comm
   = ##3 * (x * x * y ** 2)        by ring_mult_assoc
   = ##3 * (x ** 2 * y ** 2)       by ring_exp_small
   = ##3 * x2y2
   Third term:
     y * x ** 3
   = x ** 3 * y                   by ring_mult_comm
   = x3y
   Fourth term:
     y * (##3 * (x ** 2 * y))
   = ##3 * (x ** 2 * y) * y        by ring_mult_comm
   = ##3 * (x ** 2 * y * y)        by ring_mult_assoc
   = ##3 * (x ** 2 * (y * y))      by ring_mult_assoc
   = ##3 * (x ** 2 * y ** 2)       by ring_exp_small
   = ##3 * x2y2
   Fifth term:
     y * (##3 * (x * y ** 2))
   = ##3 * (x * y ** 2) * y        by ring_mult_comm
   = ##3 * ((x * y ** 2) * y)      by ring_mult_assoc
   = ##3 * (x * (y ** 2 * y))      by ring_mult_assoc
   = ##3 * (x * (y * y ** 2))      by ring_mult_comm
   = ##3 * (x * y ** 3)            by ring_exp_small
   = ##3 * xy3
   Simplify expansion:
     x ** 4 + (x * (##3 * (x ** 2 * y)) + x * (##3 * (x * y ** 2)) + xy3) +
       (y * x ** 3 + (y * (##3 * (x ** 2 * y)) + y * (##3 * (x * y ** 2)) + y ** 4))
   = x ** 4 + (##3 * x3y + ##3 * x2y2 + xy3) + (x3y + (##3 * x2y2 + ##3 * xy3 + y ** 4))
   = x ** 4 + (##3 * x3y + ##3 * x2y2 + xy3 + x3y + (##3 * x2y2 + ##3 * xy3 + y ** 4))    by ring_add_assoc
   = x ** 4 + (x3y + (##3 * x3y + ##3 * x2y2 + xy3) + (##3 * x2y2 + ##3 * xy3 + y ** 4))  by ring_add_comm
   = x ** 4 + (x3y + ##3 * x3y + ##3 * x2y2 + xy3 + (##3 * x2y2 + ##3 * xy3 + y ** 4))    by ring_add_assoc
   = x ** 4 + (##4 * x3y + ##3 * x2y2 + xy3 + (##3 * x2y2 + ##3 * xy3 + y ** 4))          by ring_single_add_mult
   = x ** 4 + (##4 * x3y + (##3 * x2y2 + xy3) + (##3 * x2y2 + ##3 * xy3 + y ** 4))        by ring_add_assoc
   = x ** 4 + (##4 * x3y + (##3 * x2y2 + xy3 + (##3 * x2y2 + ##3 * xy3 + y ** 4)))        by ring_add_assoc
   = x ** 4 + (##4 * x3y + (##3 * x2y2 + xy3 + (##3 * x2y2 + (##3 * xy3 + y ** 4))))      by ring_add_assoc
   = x ** 4 + (##4 * x3y + (##3 * x2y2 + (xy3 + ##3 * x2y2 + (##3 * xy3 + y ** 4))))      by ring_add_assoc
   = x ** 4 + (##4 * x3y + (##3 * x2y2 + (##3 * x2y2 + xy3 + (##3 * xy3 + y ** 4))))      by ring_add_comm
   = x ** 4 + (##4 * x3y + (##3 * x2y2 + ##3 * x2y2 + (xy3 + ##3 * xy3 + y ** 4)))        by ring_add_assoc
   = x ** 4 + (##4 * x3y + (##6 * x2y2 + (xy3 + ##3 * xy3 + y ** 4)))                    by ring_num_add_mult
   = x ** 4 + (##4 * x3y + (##6 * x2y2 + (##4 * xy3 + y ** 4)))                          by ring_single_add_mult
   = x ** 4 +  ##4 * x3y +  ##6 * x2y2 +  ##4 * xy3 + y ** 4                             by ring_add_assoc
   Hence true.
*)
val ring_binomial_4 = store_thm(
  "ring_binomial_4",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==>
    ((x + y) ** 4 = x ** 4 + ##4 * (x ** 3 * y) + ##6 * (x ** 2 * y ** 2) + ##4 * (x * y ** 3) + y ** 4)``,
  rpt strip_tac >>
  `x ** 3 IN R /\ x ** 2 * y IN R /\ x * y ** 2 IN R /\ y ** 3 IN R /\
    x ** 3 * y IN R /\ x ** 2 * y ** 2 IN R /\ x * y ** 3 IN R /\ y * y ** 3 IN R` by rw[] >>
  `x ** 3 + (##3 * (x ** 2 * y) + (##3 * (x * y ** 2) + y ** 3)) IN R` by rw[] >>
  `x * (##3 * (x ** 2 * y)) IN R /\ x * (##3 * (x * y ** 2)) IN R` by rw[] >>
  `y * (##3 * (x ** 2 * y)) IN R /\ y * (##3 * (x * y ** 2)) IN R` by rw[] >>
  `(x + y) ** 4 = (x + y) * (x ** 3 + ##3 * (x ** 2 * y) + ##3 * (x * y ** 2) + y ** 3)`
    by rw_tac std_ss[ring_exp_small, ring_binomial_3, ring_add_element] >>
  `_ = (x + y) * (x ** 3 + (##3 * (x ** 2 * y) + (##3 * (x * y ** 2) + y ** 3)))` by rw[ring_add_assoc] >>
  `_ = x * (x ** 3 + (##3 * (x ** 2 * y) + (##3 * (x * y ** 2) + y ** 3))) +
        y * (x ** 3 + (##3 * (x ** 2 * y) + (##3 * (x * y ** 2) + y ** 3)))` by rw[ring_mult_ladd] >>
  `_ = (x * x ** 3 + (x * (##3 * (x ** 2 * y)) + (x * (##3 * (x * y ** 2)) + x * y ** 3))) +
        (y * x ** 3 + (y * (##3 * (x ** 2 * y)) + (y * (##3 * (x * y ** 2)) + y * y ** 3)))` by rw[] >>
  `_ = (x * x ** 3 + (x * (##3 * (x ** 2 * y)) + x * (##3 * (x * y ** 2)) + x * y ** 3)) +
        (y * x ** 3 + (y * (##3 * (x ** 2 * y)) + y * (##3 * (x * y ** 2)) + y * y ** 3))`
    by rw_tac std_ss[ring_add_assoc] >>
  `_ = (x ** 4 + (x * (##3 * (x ** 2 * y)) + x * (##3 * (x * y ** 2)) + x * y ** 3)) +
        (y * x ** 3 + (y * (##3 * (x ** 2 * y)) + y * (##3 * (x * y ** 2)) + y ** 4))` by rw[ring_exp_small] >>
  qabbrev_tac `x3y = x ** 3 * y` >>
  qabbrev_tac `x2y2 = x ** 2 * y ** 2` >>
  qabbrev_tac `xy3 = x * y ** 3` >>
  `x * (##3 * (x ** 2 * y)) = ##3 * (x ** 2 * y) * x` by rw[ring_mult_comm] >>
  `_ = ##3 * (x ** 2 * (y * x))` by rw[ring_mult_assoc] >>
  `_ = ##3 * (x ** 2 * (x * y))` by rw[ring_mult_comm] >>
  `_ = ##3 * (x * x ** 2 * y)` by rw[ring_mult_assoc, ring_mult_comm] >>
  `_ = ##3 * x3y` by rw[ring_exp_small, Abbr`x3y`] >>
  `x * (##3 * (x * y ** 2)) = ##3 * (x * y ** 2) * x` by rw[ring_mult_comm] >>
  `_ = ##3 * (x * x * y ** 2)` by rw[ring_mult_assoc, ring_mult_comm] >>
  `_ = ##3 * x2y2` by rw[ring_exp_small, Abbr`x2y2`] >>
  `y * x ** 3 = x3y` by rw[ring_mult_comm, Abbr`x3y`] >>
  `y * (##3 * (x ** 2 * y)) = ##3 * (x ** 2 * y) * y` by rw[ring_mult_comm] >>
  `_ = ##3 * (x ** 2 * (y * y))` by rw[ring_mult_assoc] >>
  `_ = ##3 * x2y2` by rw[ring_exp_small, Abbr`x2y2`] >>
  `y * (##3 * (x * y ** 2)) = ##3 * (x * y ** 2) * y` by rw[ring_mult_comm] >>
  `_ = ##3 * (x * (y * y ** 2))` by rw[ring_mult_assoc, ring_mult_comm] >>
  `_ = ##3 * xy3` by rw[ring_exp_small, Abbr`xy3`] >>
  `##3 * x3y + ##3 * x2y2 + xy3 IN R /\ ##3 * x2y2 + ##3 * xy3 + y ** 4 IN R` by rw[] >>
  `x ** 4 + (x * (##3 * (x ** 2 * y)) + x * (##3 * (x * y ** 2)) + xy3) +
   (y * x ** 3 + (y * (##3 * (x ** 2 * y)) + y * (##3 * (x * y ** 2)) + y ** 4)) =
   x ** 4 + (##3 * x3y + ##3 * x2y2 + xy3) + (x3y + (##3 * x2y2 + ##3 * xy3 + y ** 4))` by rw[] >>
  `_ = x ** 4 + (##3 * x3y + ##3 * x2y2 + xy3 + x3y + (##3 * x2y2 + ##3 * xy3 + y ** 4))` by rw[ring_add_assoc] >>
  `_ = x ** 4 + (x3y + (##3 * x3y + ##3 * x2y2 + xy3) + (##3 * x2y2 + ##3 * xy3 + y ** 4))` by rw[ring_add_comm] >>
  `_ = x ** 4 + (x3y + ##3 * x3y + ##3 * x2y2 + xy3 + (##3 * x2y2 + ##3 * xy3 + y ** 4))` by rw[ring_add_assoc] >>
  `_ = x ** 4 + (##4 * x3y + ##3 * x2y2 + xy3 + (##3 * x2y2 + ##3 * xy3 + y ** 4))` by rw_tac std_ss[ring_single_add_mult] >>
  `_ = x ** 4 + (##4 * x3y + (##3 * x2y2 + (xy3 + ##3 * x2y2 + (##3 * xy3 + y ** 4))))` by rw[ring_add_assoc] >>
  `_ = x ** 4 + (##4 * x3y + (##3 * x2y2 + (##3 * x2y2 + xy3 + (##3 * xy3 + y ** 4))))` by rw[ring_add_comm] >>
  `_ = x ** 4 + (##4 * x3y + (##3 * x2y2 + ##3 * x2y2 + (xy3 + ##3 * xy3 + y ** 4)))` by rw[ring_add_assoc] >>
  `_ = x ** 4 + (##4 * x3y + (##(3 + 3) * x2y2 + (xy3 + ##3 * xy3 + y ** 4)))` by rw[ring_num_add_mult] >>
  `_ = x ** 4 + (##4 * x3y + (##(3 + 3) * x2y2 + (##4 * xy3 + y ** 4)))` by rw_tac std_ss[ring_single_add_mult] >>
  `_ = x ** 4 + ##4 * x3y + ##(3 + 3) * x2y2 + ##4 * xy3 + y ** 4` by rw[ring_add_assoc] >>
  rw_tac std_ss[DECIDE “3 + 3 = (6 :num)”]);

(* Can also use:
    (x + y) ** 4
  = ((x + y) ** 2) ** 2
  = (x ** 2 + (##2 * x * y + y ** 2)) ** 2
*)

(* ------------------------------------------------------------------------- *)
(* Non-zero Elements of a Ring (for Integral Domain)                         *)
(* ------------------------------------------------------------------------- *)

(* Define the Ring nonzero elements *)
val ring_nonzero_def = Define `ring_nonzero (r:'a ring) = R DIFF {#0}`;
val _ = overload_on ("R+", ``ring_nonzero r``); (* instead of R_plus *)

(* use overloading for the multiplicative group *)
val _ = overload_on("f*", ``r.prod excluding #0``);
val _ = overload_on("F*", ``f*.carrier``);

(* Overload on subfield multiplicative group *)
val _ = overload_on("s*", ``s.prod excluding s.sum.id``);
val _ = overload_on("B*", ``s*.carrier``);

(* No export of conversion. *)
(* val _ = export_rewrites ["ring_nonzero_def"]; *)

(* Theorem: [Ring nonzero characterization] x IN R+ = (x IN R) and x <> #0 *)
(* Proof: by definition. *)
val ring_nonzero_eq = store_thm(
  "ring_nonzero_eq",
  ``!(r:'a ring) x. x IN R+ <=> x IN R /\ x <> #0``,
  rw[ring_nonzero_def]);

(* This export is very bad, same as conversion. *)
(* val _ = export_rewrites ["ring_nonzero_eq"]; *)

(* Theorem: x IN R+ ==> x IN R. *)
(* Proof: by definition and IN_DIFF. *)
val ring_nonzero_element = store_thm(
  "ring_nonzero_element",
  ``!(r:'a ring) x. x IN R+ ==> x IN R``,
  rw[ring_nonzero_def]);

(* This export is very bad: all goals of x IN R will trigger this and lead to prove x IN R+. *)
(* val _ = export_rewrites ["ring_nonzero_element"]; *)

(* Theorem: x IN R+ ==> -x IN R+ *)
(* Proof: by contradiction.
   Suppose -x NOTIN R+,
   then since -x IN R, -x = #0  by ring_nonzero_eq.
   then x = #0     by ring_neg_eq_zero, contradicting x IN R+.
   Hence x = - #0  by ring_neg_eq_swap,
   or    x = #0    by ring_neg_zero, contradicting x IN R+.
*)
val ring_neg_nonzero = store_thm(
  "ring_neg_nonzero",
  ``!r:'a ring. Ring r ==> !x. x IN R+ ==> -x IN R+``,
  rw[ring_nonzero_eq]);

(* Theorem: Ring r ==> (F* = R+) *)
(* Proof:
   Note R+ = R DIFF {#0}
        F* = (r.prod excluding #0).carrier
        R* = monoid_invertibles r.prod
     F*
   = r.prod.carrier DIFF {#0}  by excluding_def
   = R DIFF {#0}               by ring_carriers
   = R+                        by ring_nonzero_def
*)
val ring_nonzero_mult_carrier = store_thm(
  "ring_nonzero_mult_carrier",
  ``!r:'a ring. Ring r ==> (F* = R+)``,
  rw[excluding_def, ring_nonzero_def]);

(* ------------------------------------------------------------------------- *)
(* Application of Group Exponentiaton in Ring: Characteristic of Ring.       *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Ring Characteristic                                                       *)
(* ------------------------------------------------------------------------- *)

(* Define characteristic of a ring *)
val char_def = Define` char (r:'a ring) = order r.sum #1`;

(* Theorem: ##(char r) = #0 *)
(* Proof: by char_def, order_property. *)
val char_property = store_thm(
  "char_property",
  ``!r:'a ring. ##(char r) = #0``,
  rw_tac std_ss[char_def, order_property]);

(* Theorem: char r = 0 <=> !n. 0 < n ==> ##n <> #0 *)
(* Proof: by char_def, order_eq_0. *)
val char_eq_0 = store_thm(
  "char_eq_0",
  ``!r:'a ring. (char r = 0) <=> !n. 0 < n ==> ##n <> #0``,
  rw_tac std_ss[char_def, order_eq_0]);

(* Theorem: 0 < char r ==> !n. 0 < n /\ n < (char r) ==> ##n <> #0 *)
(* Proof: by char_def, order_minimal. *)
val char_minimal = store_thm(
  "char_minimal",
  ``!r:'a ring. 0 < char r ==> !n. 0 < n /\ n < char r ==> ##n <> #0``,
  rw_tac std_ss[char_def, order_minimal]);

(* Theorem: FiniteRing r ==> 0 < char r *)
(* Proof:
   Note FiniteRing r ==> Ring r /\ FINITE R    by FiniteRing_def
    and FiniteGroup r.sum                      by finite_ring_add_finite_group
   Since #1 IN R                               by ring_one_element
      so 0 < order r.sum #1                    by group_order_pos
      or 0 < char r                            by char_def
*)
val finite_ring_char_pos = store_thm(
  "finite_ring_char_pos",
  ``!r:'a ring. FiniteRing r ==> 0 < char r``,
  rpt (stripDup[FiniteRing_def]) >>
  `FiniteGroup r.sum` by rw[finite_ring_add_finite_group] >>
  rw[group_order_pos, char_def]);

(* ------------------------------------------------------------------------- *)
(* Characteristic Theorems                                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r ==> ##n = #0 iff (char r) divides n  *)
(* Proof:
   Let m = char r.
   If m = 0, then !n. ##n <> #0   by char_eq_0
   and 0 divides n iff n = 0      by ZERO_DIVIDES
   but ##0 = #0                   by ring_num_0
   Hence true.
   If m <> 0, 0 < m, ##m = #0     by char_property
   Apply DIVISION, there are q p such that:
     n = q * m + p   with p < m
   ##n = ##(q * m + p)
       = ##(q * m) + ##p          by ring_num_add
       = ##q * ##m + ##p          by ring_num_mult
       = ##q * #0  + ##p          by above
       = #0 + ##p                 by ring_mult_rzero
       = ##p                      by ring_add_lzero

   For if case, p = 0             by char_minimal
   hence m divides n              by divides_def
   For only-if case,
       m divides (q * m + p)
   ==> m divides p                by DIVIDES_ADD_2
   ==> p = 0                      by NOT_LT_DIVIDES
   Hence ##n = ##p = #0           by ring_num_0
*)
val ring_char_divides = store_thm(
  "ring_char_divides",
  ``!r:'a ring. Ring r ==> !n. (## n = #0) <=> (char r) divides n``,
  rpt strip_tac >>
  `!x. x <> 0 <=>  0 < x` by decide_tac >>
  qabbrev_tac `m = char r` >>
  Cases_on `m = 0` >-
  metis_tac[char_eq_0, ring_num_0, ZERO_DIVIDES] >>
  `?q p. (n = q * m + p) /\ p < m` by metis_tac[DIVISION] >>
  `## m = #0` by rw_tac std_ss[GSYM char_property] >>
  `## n = ## q * ## m + ## p` by rw_tac std_ss[ring_num_add, ring_num_mult] >>
  `_ = ## p` by rw[] >>
  rw_tac std_ss[EQ_IMP_THM] >-
  metis_tac[char_minimal, divides_def, ADD_0] >>
  metis_tac[divides_def, DIVIDES_ADD_2, NOT_LT_DIVIDES, ring_num_0]);

(* Theorem: Ring r ==> char r = 1 iff #1 = #0  *)
(* Proof:
   If part,
   char r = 1 ==> ##1 = #0           by char_property
   hence true since #1 = ##1         by ring_num_1
   Only-if part, (char r) divides 1  by ring_char_divides,
   hence char r = 1                  by DIVIDES_ONE.
*)
val ring_char_eq_1 = store_thm(
  "ring_char_eq_1",
  ``!r:'a ring. Ring r ==> ((char r = 1) <=> (#1 = #0))``,
  rw_tac std_ss [EQ_IMP_THM] >| [
    rw [GSYM char_property],
    rw [GSYM ring_char_divides, GSYM DIVIDES_ONE]
  ]);

(* Theorem: Ring r /\ (char r = 2) ==> (- #1 = #1) *)
(* Proof:
   Given char r = 2
      so order r.sum #1 = 2      by char_def
      or r.sum.exp #1 2 = #0     by order_property
     i.e.           ##2 = #0     by notation
      or        #1 + #1 = #0     by ring_num_2
*)
val ring_char_2_property = store_thm(
  "ring_char_2_property",
  ``!r:'a ring. Ring r /\ (char r = 2) ==> (#1 + #1 = #0)``,
  metis_tac[char_def, order_property, ring_num_2]);

(* Theorem: Ring r /\ (char r = 2) ==> (- #1 = #1) *)
(* Proof:
   Since #1 + #1 = #0     by ring_char_2_property
     and #1 IN R          by ring_one_element
   hence - #1 = #1        by ring_add_eq_zero
*)
val ring_char_2_neg_one = store_thm(
  "ring_char_2_neg_one",
  ``!r:'a ring. Ring r /\ (char r = 2) ==> (- #1 = #1)``,
  metis_tac[ring_char_2_property, ring_add_eq_zero, ring_one_element]);

(* Theorem: Ring r /\ (char r = 2) ==> !x. x IN R ==> (x + x = #0) *)
(* Proof:
     x + x
   = #1 * x + #1 * x       by ring_mult_lone
   = (#1 + #1) * x         by ring_mult_ladd
   = #0 * x                by ring_char_2_property
   = #0                    by ring_mult_lzero
*)
val ring_char_2_double = store_thm(
  "ring_char_2_double",
  ``!r:'a ring. Ring r /\ (char r = 2) ==> !x. x IN R ==> (x + x = #0)``,
  rpt strip_tac >>
  `x + x = (#1 + #1) * x` by rw[] >>
  `_ = #0` by rw_tac std_ss[ring_char_2_property, ring_mult_lzero] >>
  rw[]);

(* Theorem: Ring r /\ (char r = 2) ==> !x. x IN R ==> (-x = x) *)
(* Proof:
     x + x = #0            by ring_char_2_double
   Hence -x = x            by ring_add_eq_zero
*)
val ring_neg_char_2 = store_thm(
  "ring_neg_char_2",
  ``!r:'a ring. Ring r /\ (char r = 2) ==> !x. x IN R ==> (-x = x)``,
  rw[ring_char_2_double, GSYM ring_add_eq_zero]);

(* Theorem: Ring r /\ (char r = 2) ==> !x y. x IN R /\ y IN R ==> (x + y = x - y) *)
(* Proof:
     x - y
   = x + -y     by ring_sub_def
   = x + y      by ring_neg_char_2
*)
val ring_add_char_2 = store_thm(
  "ring_add_char_2",
  ``!r:'a ring. Ring r /\ (char r = 2) ==> !x y. x IN R /\ y IN R ==> (x + y = x - y)``,
  rw[ring_neg_char_2]);

(* Theorem: Ring r /\ #1 <> #0 ==> !c. coprime c (char r) ==> ##c <> #0 *)
(* Proof:
   #1 <> #0 ==> char r = n <> 1    by ring_char_eq_1
   If ##c = #0, divides n c        by ring_char_divides
   then gcd n c = n                by divides_iff_gcd_fix
   or   gcd c n = n                by GCD_SYM
   but coprime c n means gcd c n = 1,
   contradicting n <> 1. Hence ##c <> #0.
*)
val ring_num_char_coprime_nonzero = store_thm(
  "ring_num_char_coprime_nonzero",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. coprime c (char r) ==> ##c <> #0``,
  metis_tac[ring_char_eq_1, ring_char_divides, divides_iff_gcd_fix, GCD_SYM]);

(* Theorem: Ring r ==> !n. 0 < n ==>
            ((char r = n) <=> (##n = #0) /\ (!m. 0 < m /\ m < n ==> ##m <> #0)) *)
(* Proof: by char_def, order_thm *)
val ring_char_alt = store_thm(
  "ring_char_alt",
  ``!r:'a ring. Ring r ==> !n. 0 < n ==>
   ((char r = n) <=> (##n = #0) /\ (!m. 0 < m /\ m < n ==> ##m <> #0))``,
  rw[char_def, order_thm]);

(* Theorem: Ring r /\ #1 <> #0 ==> ((-#1 = #1) <=> (char r = 2)) *)
(* Proof:
   If part: #1 = -#1 ==> char r = 2
      Since ##1 = #1           by ring_num_1
                <> #0          by given
        and ##2 = #1 + #1      by ring_num_mult_small
                = #1 + (-#1)   by given
                = #0           by ring_add_rneg
      Hence char r = 2         by ring_char_alt, 0 < char r
   Only-if part: char r = 2 ==> -#1 = #1
      True by ring_char_2_neg_one
*)
val ring_neg_one_eq_one = store_thm(
  "ring_neg_one_eq_one",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> ((-#1 = #1) <=> (char r = 2))``,
  rw[EQ_IMP_THM] >| [
    `##1 = #1` by rw[] >>
    `##2 = #1 + #1` by rw[GSYM ring_num_mult_small] >>
    `_ = #1 + (-#1)` by metis_tac[] >>
    `_ = #0` by rw[] >>
    rw[ring_char_alt, DECIDE``!m. 0 < m /\ m < 2 ==> (m = 1)``],
    rw[ring_char_2_neg_one]
  ]);

(* Theorem: Ring r ==> !x. x IN R ==> !n. r.sum.exp x n = x * ##n *)
(* Proof:
   By induction on n.
   Base: r.sum.exp x 0 = x * ##0
         r.sum.exp x 0
       = #0                        by group_exp_0
       = x * ##0
   Step: r.sum.exp x n = x * ##n ==> r.sum.exp x (SUC n) = x * ##(SUC n)
         r.sum.exp x (SUC n)
       = x + (r.sum.exp x n)       by group_exp_SUC
       = x + x * ##n               by induction hypothesis
       = x * (#1 + ##n)            by ring_mult_radd
       = x * ##(SUC n)             by ring_num_SUC
*)
val ring_add_exp_eqn = store_thm(
  "ring_add_exp_eqn",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !n. r.sum.exp x n = x * ##n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw[ring_mult_radd]);

(* Theorem: Ring r ==> !n m. n < char r /\ m < char r ==> (##n = ##m <=> (n = m)) *)
(* Proof:
   Note 0 < char r                          by n < char r, m < char r
    and Group r.sum /\ (r.sum.carrier = R)  by ring_add_group
   This follows by group_order_unique:
   group_order_unique |> SPEC ``r.sum``;
   > val it = |- Group r.sum ==> !x. x IN r.sum.carrier ==>
         !m n. m < order r.sum x /\ n < order r.sum x ==> (r.sum.exp x m = r.sum.exp x n) ==> (m = n) : thm
   Take x = #1, apply char_def.
*)
val ring_num_eq = store_thm(
  "ring_num_eq",
  ``!r:'a ring. Ring r ==> !n m. n < char r /\ m < char r ==> ((##n = ##m) <=> (n = m))``,
  rpt strip_tac >>
  `0 < char r` by decide_tac >>
  `Group r.sum /\ (r.sum.carrier = R)` by rw[ring_add_group] >>
  metis_tac[group_order_unique, char_def, ring_one_element]);

(* Theorem: Ring r /\ 0 < char r ==> !n. ##n = ##(n MOD (char r)) *)
(* Proof:
   Note Group r.sum /\ (r.sum.carrier = R)  by ring_add_group
   The result follows                       by group_exp_mod, char_def
*)
val ring_num_mod = store_thm(
  "ring_num_mod",
  ``!r:'a ring. Ring r /\ 0 < char r ==> !n. ##n = ##(n MOD (char r))``,
  rpt strip_tac >>
  `Group r.sum` by rw[ring_add_group] >>
  fs[Once group_exp_mod, char_def]);

(* export simple result -- but this is bad! *)
(* val _ = export_rewrites ["finite_ring_num_mod"]; *)

(* Theorem: Ring r /\ 0 < char r ==> !z. ?y x. (y = ##x) /\ (y + ##z = #0) *)
(* Proof:
   Let n = char r, then 0 < n.
   Let x = n - z MOD n, and y - ##x.
     y + ##z
   = ##x + ##z
   = ##(x + z)       by ring_num_add
   = ##(n - z MOD n + (z DIV n * n + z MOD n))    by DIVISION
   = ##(n + z DIV n * n)                          by arithmetic
   = ##n + ##(z DIV n * n)                        by ring_num_add
   = ##n + ##(z DIV n) * ##n                      by ring_num_mult
   = #0 + #0                                      by char_property
   = #0                                           by ring_add_zero_zero
*)
val ring_num_negative = store_thm(
  "ring_num_negative",
  ``!r:'a ring. Ring r /\ 0 < char r ==>
   !z:num. ?(y:'a) (x:num). (y = ##x) /\ (y + ##z = #0)``,
  rpt strip_tac >>
  qabbrev_tac `n = char r` >>
  `(z = z DIV n * n + z MOD n) /\ z MOD n < n` by rw[DIVISION] >>
  `?x. x = n - z MOD n` by rw[] >>
  qexists_tac `##x` >>
  `##x + ##z = ##(n - z MOD n) + ##z` by rw[] >>
  `_ = ##(n - z MOD n + z)` by rw[] >>
  `_ = ##(n - z MOD n + (z DIV n * n + z MOD n))` by metis_tac[] >>
  `_ = ##(n + z DIV n * n)` by rw_tac arith_ss[] >>
  `_ = ##n + ##(z DIV n * n)` by rw[] >>
  `_ = ##n + ##(z DIV n) * ##n` by rw[GSYM ring_num_mult] >>
  `_ = #0 + #0` by rw[char_property, Abbr`n`] >>
  `_ = #0` by rw[] >>
  metis_tac[]);

(* Theorem: Ring r /\ (char r = 0) ==> INFINITE R *)
(* Proof:
   By contradiction, suppose FINITE R.
   Then Ring r /\ FINITE R ==> FiniteRing r   by FiniteRing_def
    ==> 0 < char r                            by finite_ring_char_pos
   This contradicts char r = 0.
*)
val ring_char_0 = store_thm(
  "ring_char_0",
  ``!r:'a ring. Ring r /\ (char r = 0) ==> INFINITE R``,
  metis_tac[finite_ring_char_pos, FiniteRing_def, NOT_ZERO_LT_ZERO]);

(* Theorem: Ring r /\ (char r = 1) ==> (R = {#0}) *)
(* Proof:
         char r = 1
     <=> order r.sum #1 = 1     by char_def
     ==> ##1 = #0               by order_property
     <=> #1 = #0                by ring_num_1
     <=> R = {#0}               by ring_one_eq_zero
*)
val ring_char_1 = store_thm(
  "ring_char_1",
  ``!r:'a ring. Ring r /\ (char r = 1) ==> (R = {#0})``,
  rpt strip_tac >>
  `##(order r.sum #1) = #0` by rw[order_property] >>
  `#1 = #0` by metis_tac[char_def, ring_num_1] >>
  rw[GSYM ring_one_eq_zero]);

(* ------------------------------------------------------------------------- *)
(* Finite Ring.                                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FiniteRing r ==> Ring r *)
(* Proof: by FiniteRing_def *)
val finite_ring_is_ring = store_thm(
  "finite_ring_is_ring",
  ``!r:'a ring. FiniteRing r ==> Ring r``,
  rw[FiniteRing_def]);

(* Theorem: FiniteRing r ==> 0 < CARD R *)
(* Proof:
   Note FiniteRing r ==> Ring r /\ FINITE R    by FiniteRing_def
   Since #0 IN R                               by ring_zero_element
      so R <> {}                               by MEMBER_NOT_EMPTY
    then CARD R <> 0                           by CARD_EQ_0
      or 0 < CARD R                            by NOT_ZERO_LT_ZERO
*)
val finite_ring_card_pos = store_thm(
  "finite_ring_card_pos",
  ``!r:'a ring. FiniteRing r ==> 0 < CARD R``,
  rw[FiniteRing_def] >>
  `#0 IN R` by rw[] >>
  `CARD R <> 0` by metis_tac[CARD_EQ_0, MEMBER_NOT_EMPTY] >>
  decide_tac);

(* Theorem: FiniteRing r ==> ((CARD R = 1) <=> (#1 = #0)) *)
(* Proof:
   Note FiniteRing r ==> Ring r /\ FINITE R    by FiniteRing_def
   If part: (CARD R = 1) ==> (#1 = #0)
      FINTE R /\ (CARD R = 1) ==> SING R       by SING_IFF_CARD1
      Since #1 IN R                            by ring_one_element
        and #0 IN R                            by ring_zero_element
      Hence #1 = #0                            by IN_SING, SING_DEF
   Only-if part: (#1 = #0) ==> (CARD R = 1)
      #1 = #0 ==> R = {#0}                     by ring_one_eq_zero
              ==> CARD R = 1                   by CARD_SING
*)
val finite_ring_card_eq_1 = store_thm(
  "finite_ring_card_eq_1",
  ``!r:'a ring. FiniteRing r ==> ((CARD R = 1) <=> (#1 = #0))``,
  rw[FiniteRing_def, EQ_IMP_THM] >-
  metis_tac[SING_IFF_CARD1, SING_DEF, IN_SING, ring_one_element, ring_zero_element] >>
  metis_tac[ring_one_eq_zero, CARD_SING]);

(* Theorem: FiniteRing r ==> 0 < char r /\ (char r = order r.sum #1) *)
(* Proof:
   Note FiniteRing r ==> Ring r /\ FINITE R    by FiniteRing_def
    and FiniteGroup r.sum                      by finite_ring_add_finite_group
   Since #1 IN R                               by ring_one_element
      so 0 < order r.sum #1                    by group_order_pos
      or 0 < char r /\ (char r = order r.sum #1)   by char_def
*)
val finite_ring_char = store_thm(
  "finite_ring_char",
  ``!r:'a ring. FiniteRing r ==> (0 < char r) /\ (char r = order r.sum #1)``,
  (strip_tac >> stripDup[FiniteRing_def]) >>
  `FiniteGroup r.sum` by rw[finite_ring_add_finite_group] >>
  rw[group_order_pos, char_def]);

(* Theorem: FiniteRing r ==> (char r) divides (CARD R) *)
(* Proof:
   Note FiniteRing r ==> Ring r /\ FINITE R    by FiniteRing_def
    and FiniteGroup r.sum                      by finite_ring_add_finite_group
    and r.sum.carrier = R                      by ring_carriers
   Since #1 IN R                               by ring_one_element
      so (order r.sum #1) divides (CARD R)     by group_order_divides
      or (char r) divides (CARD R)             by char_def
*)
val finite_ring_char_divides = store_thm(
  "finite_ring_char_divides",
  ``!r:'a ring. FiniteRing r ==> (char r) divides (CARD R)``,
  rpt (stripDup[FiniteRing_def]) >>
  `FiniteGroup r.sum` by rw[finite_ring_add_finite_group] >>
  metis_tac[group_order_divides, char_def, ring_one_element, ring_carriers]);

(* Theorem: FiniteRing r /\ prime (CARD R) ==> (char r = CARD R) *)
(* Proof:
   Since char r divides CARD R               by finite_ring_char_divides
      so (char r = CARD R) \/ (char r = 1)   by prime_def
   If char r = CARD R, it is done.
   If char r = 1,
      then #1 = #0                           by ring_char_eq_1
       and R = {#0}                          by ring_one_eq_zero
        so CARD R = 1                        by CARD_SING
      which makes prime (CARD R) = F,
           but (char r = CARD R) = T.
*)
val finite_ring_card_prime = store_thm(
  "finite_ring_card_prime",
  ``!r:'a ring. FiniteRing r /\ prime (CARD R) ==> (char r = CARD R)``,
  rpt (stripDup[FiniteRing_def]) >>
  `char r divides CARD R` by rw[finite_ring_char_divides] >>
  `(char r = CARD R) \/ (char r = 1)` by metis_tac[prime_def] >>
  `#1 = #0` by rw[GSYM ring_char_eq_1] >>
  `R = {#0}` by rw[GSYM ring_one_eq_zero] >>
  rw[]);

(* Note: the converse is false:
   Counter-example for: char r = CARD R ==> prime (CARD R)
   Take r = Z_6, char r = CARD R = 6, but 6 is not prime.
   ZN_char: 0 < n ==> (char (ZN n) = n)
   ZN_card: CARD (ZN n).carrier = n
*)

(* Theorem: FiniteRing r ==> char r = n <=> 0 < n /\ ##n = #0 /\ !m. 0 < m /\ m < n ==> ##m <> #0 *)
(* Proof:
   Note FiniteRing r ==> 0 < char r     by finite_ring_char_pos
   Hence true by ring_char_alt
*)
val finite_ring_char_alt = store_thm(
  "finite_ring_char_alt",
  ``!r:'a ring. FiniteRing r ==>
   !n. (char r = n) <=> 0 < n /\ (##n = #0) /\ (!m. 0 < m /\ m < n ==> ##m <> #0)``,
  rpt (stripDup[FiniteRing_def]) >>
  `0 < char r` by rw[finite_ring_char_pos] >>
  metis_tac[ring_char_alt]);

(* ------------------------------------------------------------------------- *)
(* Ring Units Documentation                                                  *)
(* ------------------------------------------------------------------------- *)
(*
   Overloading:
   r*       = Invertibles (r.prod)
   R*       = r*.carrier
   unit x   = x IN R*
   |/       = r*.inv
   x =~ y   = unit_eq r x y
*)
(* Definitions and Theorems (# are exported):

   Units in a Ring:
   ring_units_property       |- !r. Ring r ==> (r*.op = $* ) /\ (r*.id = #1)
   ring_units_has_one        |- !r. Ring r ==> #1 IN R*
   ring_units_has_zero       |- !r. Ring r ==> (#0 IN R* <=> (#1 = #0))
   ring_units_element        |- !r. Ring r ==> !x. x IN R* ==> x IN R

   Units in a Ring form a Group:
   ring_units_group          |- !r. Ring r ==> Group r*
   ring_units_abelain_group  |- !r. Ring r ==> AbelianGroup r*

   Ring Units:
#  ring_unit_one             |- !r. Ring r ==> unit #1
   ring_unit_zero            |- !r. Ring r ==> (unit #0 <=> (#1 = #0))
   ring_unit_nonzero         |- !r. Ring r /\ #1 <> #0 ==> !x. unit x ==> x <> #0
   ring_unit_has_inv         |- !r. Ring r ==> !x. unit x ==> unit ( |/ x)
   ring_unit_linv            |- !r. Ring r ==> !x. unit x ==> ( |/ x * x = #1)
   ring_unit_rinv            |- !r. Ring r ==> !x. unit x ==> (x * |/ x = #1)
#  ring_unit_element         |- !r. Ring r ==> !x. unit x ==> x IN R
   ring_unit_inv_element     |- !r. Ring r ==> !x. unit x ==> |/ x IN R
   ring_unit_inv_nonzero     |- !r. Ring r /\ #1 <> #0 ==> !x. unit x ==> |/ x <> #0
   ring_unit_mult_zero       |- !r. Ring r ==> !x y. unit x /\ y IN R ==> ((x * y = #0) <=> (y = #0))
   ring_unit_property        |- !r. Ring r ==> !u. unit u <=> u IN R /\ ?v. v IN R /\ (u * v = #1)
   ring_unit_neg             |- !r. Ring r ==> !x. unit x ==> unit (-x)
   ring_unit_mult_unit       |- !r. Ring r ==> !u v. unit u /\ unit v ==> unit (u * v)
   ring_unit_mult_eq_unit    |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> (unit (x * y) <=> unit x /\ unit y)
   ring_unit_rinv_unique     |- !r. Ring r ==> !u v. unit u /\ v IN R /\ (u * v = #1) ==> (v = |/ u)
   ring_unit_linv_unique     |- !r. Ring r ==> !u v. u IN R /\ unit v /\ (u * v = #1) ==> (u = |/ v)
   ring_unit_inv_inv         |- !r. Ring r ==> !u. unit u ==> (u = |/ ( |/ u))
   ring_unit_linv_inv        |- !r. Ring r ==> !u v. unit u /\ v IN R /\ ( |/ u * v = #1) ==> (u = v)
   ring_unit_rinv_inv        |- !r. Ring r ==> !u v. u IN R /\ unit v /\ (u * |/ v = #1) ==> (u = v)
#  ring_inv_one              |- !r. Ring r ==> ( |/ #1 = #1)

   Ring Unit Equivalence:
   unit_eq_def       |- !r x y. x =~ y <=> ?u. unit u /\ (x = u * y)
   unit_eq_refl      |- !r. Ring r ==> !x. x IN R ==> x =~ x
   unit_eq_sym       |- !r. Ring r ==> !x y. x IN R /\ y IN R /\ x =~ y ==> y =~ x
   unit_eq_trans     |- !r. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R /\ x =~ y /\ y =~ z ==> x =~ z
   ring_eq_unit_eq   |- !r. Ring r ==> !x y. x IN R /\ y IN R /\ (x = y) ==> x =~ y
*)

(* ------------------------------------------------------------------------- *)
(* Units in a Ring = Invertibles of (r.prod).                                *)
(* ------------------------------------------------------------------------- *)

(*
(* Define the Units of a Ring *)
val Units_def = Define`
  Units (r:'a ring) = Invertibles (r.prod)
`;
*)
val _ = overload_on ("r*", ``Invertibles (r.prod)``); (* instead of r_star *)
val _ = overload_on ("R*", ``r*.carrier``); (* instead of R_star *)

(* Theorem: r*.op = r.prod.op /\ r*.id = #1 *)
(* Proof: by ring_of_units, and Invertibles_def *)
val ring_units_property = store_thm(
  "ring_units_property",
  ``!r:'a ring. Ring r ==> (r*.op = r.prod.op) /\ (r*.id = #1)``,
  rw_tac std_ss[Invertibles_def]);

(* Theorem: #1 IN R* *)
(* Proof: by monoid_id_invertible. *)
val ring_units_has_one = store_thm(
  "ring_units_has_one",
  ``!r:'a ring. Ring r ==> #1 IN R*``,
  rw[ring_mult_monoid, Invertibles_def]);

(* Theorem: #0 IN R* ==> #1 = #0 *)
(* Proof:
   If part: #0 IN R* ==> #1 = #0
      This means ?x. x IN R* /\ x * #0 = #1 /\ #0 * x = #1   by monoid_invertibles_def
      Therefore #1 = #0 by ring_mult_lzero, ring_mult_rzero.
   Only-if part: #1 = #0 ==> #0 IN R*
      true ring_units_has_one.
*)
val ring_units_has_zero = store_thm(
  "ring_units_has_zero",
  ``!r:'a ring. Ring r ==> (#0 IN R* <=> (#1 = #0))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    `Monoid r.prod /\ (r.prod.carrier = R)` by rw_tac std_ss[ring_mult_monoid] >>
    `R* = monoid_invertibles r.prod` by rw_tac std_ss[Invertibles_def] >>
    metis_tac[ring_mult_lzero, monoid_inv_from_invertibles],
    metis_tac[ring_units_has_one]
  ]);

(* Theorem: Ring r ==> x IN R* ==> x IN R *)
(* Proof:
       x IN R*
   ==> x IN (Invertibles (r.prod)).carrier
   ==> x IN monoid_invertibles r.prod         by Invertibles_def
   ==> x IN r.prod.carrier                    by monoid_invertibles
   ==> x IN R                                 by ring_carriers
*)
val ring_units_element = store_thm(
  "ring_units_element",
  ``!r:'a ring. Ring r ==> !x. x IN R* ==> x IN R``,
  rw[Invertibles_def, monoid_invertibles_def]);

(* ------------------------------------------------------------------------- *)
(* Units in a Ring form a Group.                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r ==> Group r* *)
(* Proof: by monoid_invertibles_is_group, ring_mult_monoid. *)
val ring_units_group = store_thm(
  "ring_units_group",
  ``!r:'a ring. Ring r ==> Group r*``,
  rw[monoid_invertibles_is_group, ring_mult_monoid]);

(* Theorem: Units of Ring is an Abelian Group. *)
(* Proof: by checking definition.
   (1) Ring r ==> Group r*
       by ring_units_group
   (2) x IN R* /\ y IN R* ==> r*op x y = r*.op y x
       x IN R /\ y IN R       by ring_units_element
       r*.op = r.prod.op      by ring_units_property
       Hence true             by ring_mult_monoid
*)
val ring_units_abelain_group = store_thm(
  "ring_units_abelain_group",
  ``!r:'a ring. Ring r ==> AbelianGroup r*``,
  rw[AbelianGroup_def, ring_units_group] >>
  rw[ring_units_element, ring_mult_monoid, ring_units_property]);

(* ------------------------------------------------------------------------- *)
(* Units in a Ring have inverses.                                            *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Ring Units                                                                *)
(* ------------------------------------------------------------------------- *)

(* define unit by overloading *)
val _ = overload_on ("unit", ``\x. x IN R*``);

(* Theorem: #1 IN R* *)
(* Proof: by monoid_id_invertible. *)
val ring_unit_one = store_thm(
  "ring_unit_one",
  ``!r:'a ring. Ring r ==> unit #1``,
  rw[ring_mult_monoid, Invertibles_def]);

(* export simple result *)
val _ = export_rewrites ["ring_unit_one"];

(* Theorem: #0 IN R* ==> #1 = #0 *)
(* Proof:
   If part: #0 IN R* ==> #1 = #0
      This means ?x. x IN R* /\ x * #0 = #1 /\ #0 * x = #1   by monoid_invertibles_def
      Therefore #1 = #0 by ring_mult_lzero, ring_mult_rzero.
   Only-if part: #1 = #0 ==> #0 IN R*
      True by ring_unit_one.
*)
val ring_unit_zero = store_thm(
  "ring_unit_zero",
  ``!r:'a ring. Ring r ==> (unit #0 <=> (#1 = #0))``,
  rw[EQ_IMP_THM] >| [
    `Monoid r.prod /\ (r.prod.carrier = R)` by rw[ring_mult_monoid] >>
    `R* = monoid_invertibles r.prod` by rw[Invertibles_def] >>
    metis_tac[ring_mult_lzero, monoid_inv_from_invertibles],
    metis_tac[ring_unit_one]
  ]);

(* Theorem: Ring r /\ #1 <> #0 ==> !x. unit x ==> x <> #0 *)
(* Proof: by ring_unit_zero: |- !r. Ring r ==> (unit #0 <=> (#1 = #0)) *)
val ring_unit_nonzero = store_thm(
  "ring_unit_nonzero",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !x. unit x ==> x <> #0``,
  metis_tac[ring_unit_zero]);

(*
group_inv_element |> SPEC ``r*``;
|- Group r* ==> !x. x IN R* ==> r*.inv x IN R*: thm
group_inv_element |> SPEC ``r*`` |> UNDISCH_ALL |> PROVE_HYP (ring_units_group |> SPEC_ALL |> UNDISCH_ALL);
group_inv_element |> SPEC ``r*`` |> UNDISCH_ALL |> PROVE_HYP (ring_units_group |> SPEC_ALL |> UNDISCH_ALL)
    |> DISCH_ALL |> GEN_ALL;
|- !r. Ring r ==> !x. x IN R* ==> r*.inv x IN R*: thm
*)

(* Lifting Group Inverse Theorem for Ring units
   from: !g: 'a group. Group g ==> E(g.inv)
     to: !r:'a ring.  Ring r ==> E(r*.inv)
    via: !r:'a ring.  Ring r ==> Group r*
*)
local
val rug = ring_units_group |> SPEC_ALL |> UNDISCH_ALL
val rupropery = ring_units_property |> SPEC_ALL |> UNDISCH_ALL
in
fun lift_group_inv_thm gsuffix rsuffix = let
  val thm = DB.fetch "group" ("group_" ^ gsuffix)
  val thm' = thm |> SPEC ``r*`` |> UNDISCH_ALL
in
  save_thm("ring_" ^ rsuffix,
           thm' |> PROVE_HYP rug
           |> REWRITE_RULE [rupropery]
           |> DISCH_ALL |> GEN_ALL)
end
end; (* local *)

(* overloading for inverse *)
val _ = overload_on ("|/", ``r*.inv``);

(* Theorem: x IN R* ==> |/ x IN R* *)
(* Proof: by group_inv_element, ring_units_group. *)
val ring_unit_has_inv = lift_group_inv_thm "inv_element" "unit_has_inv";
(* val ring_unit_has_inv = |- !r. Ring r ==> !x. unit x ==> unit ( |/ x) : thm *)

(* Theorem: x IN R* ==> |/ x * x = #1 *)
(* Proof: by group_linv, ring_units_group. *)
val ring_unit_linv = lift_group_inv_thm "linv" "unit_linv";
(* val ring_unit_linv = |- !r. Ring r ==> !x. unit x ==> ( |/ x * x = #1) : thm *)

(* Theorem: x IN R* ==> x * |/ x = #1 *)
(* Proof: by group_rinv, ring_units_group. *)
val ring_unit_rinv = lift_group_inv_thm "rinv" "unit_rinv";
(* val ring_unit_rinv = |- !r. Ring r ==> !x. unit x ==> (x * |/ x = #1) : thm *)

(* Theorem: x IN R* ==> x IN R *)
val ring_unit_element = save_thm("ring_unit_element", ring_units_element);
(* > val ring_unit_element = |- !r. Ring r ==> !x. unit x ==> x IN R : thm *)

(* export simple result *)
val _ = export_rewrites ["ring_unit_element"];

(* Theorem: x IN R* ==> |/ x IN R *)
(* Proof: by ring_unit_has_inv, ring_unit_element. *)
val ring_unit_inv_element = store_thm(
  "ring_unit_inv_element",
  ``!r:'a ring. Ring r ==> !x. unit x ==> |/ x IN R``,
  rw[ring_unit_has_inv]);

(* Theorem: Ring r /\ #1 <> #0 ==> !x. unit x ==> |/ x <> #0 *)
(* Proof:
   By contradiction, suppose |/ x = #0.
     #1 = x * |/x          by ring_unit_rinv
        = x * #0           by assumption
        = #0               by ring_mult_rzero
   This contradicts #1 <> #0.
*)
val ring_unit_inv_nonzero = store_thm(
  "ring_unit_inv_nonzero",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !x. unit x ==> |/ x <> #0``,
  metis_tac[ring_unit_rinv, ring_mult_rzero, ring_unit_element]);

(* Theorem: x IN R*, y IN R, x * y = #0 <=> y = #0 *)
(* Proof:
                   x * y = #0
   <=>     |/x * (x * y) = |/x * #0 = #0    by ring_mult_rzero
   <=>     ( |/x * x) * y = #0              by ring_mult_assoc
   <=>            #1 * y = #0               by ring_unit_linv
   <=>                 y = #0               by ring_mult_lone
*)
val ring_unit_mult_zero = store_thm(
  "ring_unit_mult_zero",
  ``!r:'a ring. Ring r ==> !x y. unit x /\ y IN R ==> ((x * y = #0) <=> (y = #0))``,
  rpt strip_tac >>
  `x IN R` by rw[] >>
  rw[EQ_IMP_THM] >>
  `|/x IN R` by rw[ring_unit_inv_element] >>
  `y = #1 * y` by rw[] >>
  `_ = ( |/x * x) * y` by rw[ring_unit_linv] >>
  metis_tac[ring_mult_assoc, ring_mult_rzero]);

(* Theorem: Ring r ==> !u. unit u <=> ?v. u * v = #1 *)
(* Proof:
   If part: unit u ==> ?v. u * v = #1
     unit u ==> |/u IN R, and u * |/u = #1, so take v = |/u.
   Only-if part: ?v. u * v = #1 ==> unit u
     by definition of unit x = x IN R*
                             = x IN r*.carrier
                             = x IN (Invertibles (r.prod)).carrier
*)
val ring_unit_property = store_thm(
  "ring_unit_property",
  ``!r:'a ring. Ring r ==> !u. unit u <=> u IN R /\ (?v. v IN R /\ (u * v = #1))``,
  rw[EQ_IMP_THM] >-
  metis_tac[ring_unit_inv_element, ring_unit_rinv] >>
  `r.prod.carrier = R` by rw[ring_mult_monoid] >>
  rw_tac std_ss[Invertibles_def, monoid_invertibles_def, GSPECIFICATION] >>
  metis_tac[ring_mult_comm]);

(* Theorem: Ring r ==> !x. unit x ==> unit (-x) *)
(* Proof:
   Since unit x
     ==> x IN R /\ ?v. v IN R /\ x * v = #1    by ring_unit_property
   hence (-x) * (-v) = x * v                   by ring_mult_neg_neg
                     = #1                      by above
   Since -v IN R                               by ring_neg_element
   Hence unit (-x)                             by ring_unit_property
*)
val ring_unit_neg = store_thm(
  "ring_unit_neg",
  ``!r:'a ring. Ring r ==> !x. unit x ==> unit (-x)``,
  metis_tac[ring_unit_property, ring_mult_neg_neg, ring_neg_element]);

(* Theorem: Ring r ==> !u v. unit u /\ unit v ==> unit (u * v) *)
(* Proof:
   Let z = |/ v * |/ u
   Since |/ u IN R /\ |/ v IN R     by ring_unit_inv_element
      so z IN R                     by ring_mult_element
    also (u * v) * z
       = (u * v) * ( |/ v * |/ u)   by above
       = (u * v * |/ v) * |/u       by ring_mult_assoc
       = u * |/ u                   by ring_unit_rinv, ring_mult_rone
       = #1                         by ring_unit_rinv
   Hence unit (u * v)               by ring_unit_property
*)
val ring_unit_mult_unit = store_thm(
  "ring_unit_mult_unit",
  ``!r:'a ring. Ring r ==> !u v. unit u /\ unit v ==> unit (u * v)``,
  rpt strip_tac >>
  qabbrev_tac `z = |/ v * |/ u` >>
  `u IN R /\ v IN R` by rw[ring_unit_element] >>
  `|/ v IN R /\ |/ u IN R` by rw[ring_unit_inv_element] >>
  `z IN R` by rw[Abbr`z`] >>
  `(u * v) * z = (u * v) * ( |/ v * |/ u)` by rw[Abbr`z`] >>
  `_ = u * (v * ( |/ v * |/ u))` by rw[ring_mult_assoc] >>
  `_ = u * (v * |/ v * |/ u)` by rw[ring_mult_assoc] >>
  `_ = u * |/ u` by rw[ring_unit_rinv] >>
  `_ = #1` by rw[ring_unit_rinv] >>
  metis_tac[ring_unit_property, ring_mult_element]);

(* Theorem: Ring r ==> !x y. x IN R /\ y IN R ==>
            (unit (x * y) <=> unit x /\ unit y) *)
(* Proof:
   If part: unit (x * y) ==> unit x /\ unit y
      Let z = x * y.
      Then z IN R /\
           ?u. u IN R /\ (z * u = #1)   by ring_unit_property
       ==> (x * y) * u = #1             by z = x * y
       ==> x * (y * u) = #1             by ring_mult_assoc
       Hence unit x                     by ring_unit_property, ring_mult_element
       Also (y * u) * x = #1            by ring_mult_comm
       ==>  y * (u * x) = #1            by ring_mult_assoc
       Hence unit y                     by ring_unit_property, ring_mult_element

   Only-if part: unit x /\ unit y ==> unit (x * y)
      This is true         by ring_unit_mult_unit
*)
val ring_unit_mult_eq_unit = store_thm(
  "ring_unit_mult_eq_unit",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==>
    (unit (x * y) <=> unit x /\ unit y)``,
  rpt strip_tac >>
  simp[EQ_IMP_THM] >>
  ntac 2 strip_tac >| [
    qabbrev_tac `z = x * y` >>
    `z IN R /\ ?u. u IN R /\ (z * u = #1)` by metis_tac[ring_unit_property] >>
    `x * (y * u) = #1` by rw[GSYM ring_mult_assoc, Abbr`z`] >>
    `y * (u * x) = #1` by rw[GSYM ring_mult_assoc, ring_mult_comm, Abbr`z`] >>
    metis_tac[ring_unit_property, ring_mult_element],
    rw[ring_unit_mult_unit]
  ]);

(* Theorem: Ring r ==> unit u /\ u * v = #1 ==> v = |/ u *)
(* Proof:
   unit u ==> |/ u in R             by ring_unit_inv_element
   so  |/ u * (u * v) = |/ u * #1
   or  ( |/ u * u) * v = |/ u * #1  by ring_mult_assoc
               #1 * v = |/ u * #1   by ring_unit_linv
                    v = |/ u        by ring_mult_lone, ring_mult_rone
*)
val ring_unit_rinv_unique = store_thm(
  "ring_unit_rinv_unique",
  ``!r:'a ring. Ring r ==> !u v. unit u /\ v IN R /\ (u * v = #1) ==> (v = |/ u)``,
  rpt strip_tac >>
  `u IN R /\ |/ u IN R` by rw[ring_unit_inv_element] >>
  `v = ( |/u * u) * v` by rw[ring_unit_linv] >>
  `_ = |/ u * (u * v)` by rw[ring_mult_assoc] >>
  `_ = |/ u` by rw[] >>
  rw[]);

(* Theorem: Ring r ==> unit v /\ u * v = #1 ==> u = |/ v *)
(* Proof: by ring_unit_rinv_unique and ring_mult_comm. *)
val ring_unit_linv_unique = store_thm(
  "ring_unit_linv_unique",
  ``!r:'a ring. Ring r ==> !u v. u IN R /\ unit v /\ (u * v = #1) ==> (u = |/ v)``,
  rw[ring_unit_rinv_unique, ring_mult_comm]);

(* Theorem: Ring r ==> unit u ==> |/ ( |/ u) = u *)
(* Proof: by ring_unit_rinv_unique, put v = |/ u. *)
val ring_unit_inv_inv = store_thm(
  "ring_unit_inv_inv",
  ``!r:'a ring. Ring r ==> !u. unit u ==> (u = |/ ( |/ u))``,
  rw[ring_unit_inv_element, ring_unit_has_inv, ring_unit_linv, ring_unit_rinv_unique]);

(* Theorem: Ring r ==> unit u /\ |/ u * v = #1 ==> u = v *)
(* Proof:
   unit u ==> |/ u in R           by ring_unit_inv_element
   so   u * ( |/ u * v) = u * #1
   or   (u * |/ u) * v = u * #1   by ring_mult_assoc
   or           #1 * v = u * #1   by ring_unit_rinv
   or                v = u        by ring_mult_lone, ring_mult_rone
*)
val ring_unit_linv_inv = store_thm(
  "ring_unit_linv_inv",
  ``!r:'a ring. Ring r ==> !u v. unit u /\ v IN R /\ ( |/ u * v = #1) ==> (u = v)``,
  rpt strip_tac >>
  `u IN R /\ |/ u IN R` by rw[ring_unit_inv_element] >>
  `u = (u * |/ u) * v` by rw[ring_mult_assoc] >>
  `_ = v` by rw[ring_unit_rinv] >>
  rw[]);

(* Theorem: Ring r ==> unit v /\ u * |/ v = #1 ==> u = v *)
(* Proof: by ring_unit_linv_inv and ring_mult_comm. *)
val ring_unit_rinv_inv = store_thm(
  "ring_unit_rinv_inv",
  ``!r:'a ring. Ring r ==> !u v. u IN R /\ unit v /\ (u * |/ v = #1) ==> (u = v)``,
  metis_tac[ring_unit_linv_inv, ring_mult_comm, ring_unit_inv_element]);

(* Theorem: Ring r ==> ( |/ #1 = #1) *)
(* Proof:
   Note Group r*                by ring_units_group
    and r*.id = #1              by ring_units_property
   Thus r*.inv r*.id = r*.id    by group_inv_id
     or        |/ #1 = #1       by notation
*)
val ring_inv_one = store_thm(
  "ring_inv_one",
  ``!r:'a ring. Ring r ==> ( |/ #1 = #1)``,
  rpt strip_tac >>
  `Group r*` by rw[ring_units_group] >>
  `r*.id = #1` by rw[ring_units_property] >>
  metis_tac[group_inv_id]);

(* export simple theorem *)
val _ = export_rewrites ["ring_inv_one"];

(* ------------------------------------------------------------------------- *)
(* Ring Unit Equivalence                                                     *)
(* ------------------------------------------------------------------------- *)

(* Define unit equivalence for ring *)
Definition unit_eq_def:
   unit_eq (r:'a ring) (x:'a) (y:'a) = ?(u:'a). unit u /\ (x = u * y)
End
(* overload on unit equivalence *)
val _ = overload_on("=~", ``unit_eq r``);
val _ = set_fixity "=~" (Infix(NONASSOC, 450)); (* same as relation *)
(*
> unit_eq_def;
val it = |- !r x y. x =~ y <=> ?u. unit u /\ (x = u * y): thm
*)

(* Theorem: Ring r ==> !x. x IN R ==> x =~ x *)
(* Proof:
   Since unit #1      by ring_unit_one
     and x = #1 * x   by ring_mult_lone
   Hence x =~ x       by unit_eq_def
*)
Theorem unit_eq_refl:
  !r:'a ring. Ring r ==> !x. x IN R ==> x =~ x
Proof
  metis_tac[unit_eq_def, ring_unit_one, ring_mult_lone]
QED

(* Theorem: Ring r ==> !x y. x IN R /\ y IN R /\ x =~ y ==> y =~ x *)
(* Proof:
   Since x =~ y
     ==> ?u. unit u /\ (x = u * y)    by unit_eq_def
     and unit ( |/ u)                 by ring_unit_has_inv
     and |/ u * u = #1                by ring_unit_linv
      so y = #1 * y                   by ring_mult_lone
           = ( |/ u * u) * y          by above
           = |/ u * (u * y)           by ring_mult_assoc, ring_unit_element
           = |/ u * x                 by above
   Hence y =~ x  by taking ( |/ u)    by unit_eq_def
*)
Theorem unit_eq_sym:
  !r:'a ring. Ring r ==> !x y. x IN R /\ y IN R /\ x =~ y ==> y =~ x
Proof
  rw[unit_eq_def] >>
  `unit ( |/ u)` by rw[ring_unit_has_inv] >>
  `|/ u * u = #1` by rw[ring_unit_linv] >>
  metis_tac[ring_mult_assoc, ring_unit_element, ring_mult_lone]
QED

(* Theorem: Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R /\ x =~ y /\ y =~ z ==> x =~ z *)
(* Proof:
   Since x =~ y
     ==> ?u. unit u /\ (x = u * y)    by unit_eq_def
     and y =~ z
     ==> ?v. unit v /\ (y = v * z)    by unit_eq_def
   Hence x = u * (v * z)              by above
           = (u * v) * z              by ring_mult_assoc, ring_unit_element
     and unit (u * v)                 by ring_unit_mult_unit
    Thus x =~ z                       by unit_eq_def
*)
Theorem unit_eq_trans:
  !r:'a ring. Ring r ==> !x y z. x IN R /\ y IN R /\ z IN R /\ x =~ y /\ y =~ z ==> x =~ z
Proof
  rw[unit_eq_def] >>
  qexists_tac `u * u'` >>
  rw[ring_unit_element, ring_unit_mult_unit, ring_mult_assoc]
QED

(* Theorem: Ring r ==> !x. x IN R /\ y IN R /\ (x = y) ==> x =~ y *)
(* Proof: by unit_eq_refl *)
Theorem ring_eq_unit_eq:
  !r:'a ring. Ring r ==> !x y. x IN R /\ y IN R /\ (x = y) ==> x =~ y
Proof
  rw[unit_eq_refl]
QED

(* ------------------------------------------------------------------------- *)
(* Ring Maps Documentation                                                   *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   (r ~r~ r_) f  = Ring r /\ Ring r_ /\ RingHomo f r r_
   (r =r= r_) f  = Ring r /\ Ring r_ /\ RingIso f r r_
   R_            = (r_:'b ring).carrier
   R+_           = ring_nonzero (r_:'b ring)
   #0_           = (r_:'b ring).sum.id
   #1_           = (r_:'b ring).prod.id
   +_            = (r_:'b ring).sum.op
   *_            = (r_:'b ring).prod.op
   -_            = ring_sub (r_:'b ring)
   neg_          = (r_:'b ring).sum.inv
   ##_           = (r_:'b ring).sum.exp
   **_           = (r_:'b ring).prod.exp
   unit_ x       = x IN (Invertibles (r_:'b ring).prod).carrier
   Unit r x      = x IN (Invertibles r.prod).carrier
   |/_           = (Invertibles (r_:'b ring ).prod).inv
   Inv r         = (Invertibles r.prod).inv
   -_            = neg_

   B            = s.carrier
   s <= r       = Ring r /\ Ring s /\ subring s r
   fR           = (homo_ring r f).carrier
*)
(* Definitions and Theorems (# are exported):

   Homomorphisms, isomorphisms, endomorphisms, automorphisms and subrings:
   RingHomo_def        |- !f r s. RingHomo f r s <=> (!x. x IN R ==> f x IN s.carrier) /\
                                  GroupHom f r.sum s.sum /\ MonoidHomo f r.prod s.prod
   RingIso_def         |- !f r s. RingIso f r s <=> RingHomo f r s /\ BIJ f R s.carrier
   RingEndo_def        |- !f r. RingEndo f r <=> RingHomo f r r
   RingAuto_def        |- !f r. RingAuto f r <=> RingIso f r r
   subring_def         |- !s r. subring s r <=> RingHomo I s r

   Ring Homomorphisms:
#  ring_homo_zero      |- !r r_ f. (r ~r~ r_) f ==> (f #0 = #0_)
#  ring_homo_one       |- !r r_ f. (r ~r~ r_) f ==> (f #1 = #1_)
#  ring_homo_ids       |- !r r_ f. (r ~r~ r_) f ==> (f #0 = #0_) /\ (f #1 = #1_)
#  ring_homo_element   |- !r r_ f. RingHomo f r r_ ==> !x. x IN R ==> f x IN R_
   ring_homo_property  |- !r r_ f. Ring r /\ RingHomo f r r_ ==> !x y. x IN R /\ y IN R ==>
                                   (f (x + y) = f x +_ f y) /\ (f (x * y) = f x *_ f y)
   ring_homo_cong      |- !r r_ f1 f2. Ring r /\ Ring r_ /\ (!x. x IN R ==> (f1 x = f2 x)) ==>
                                       (RingHomo f1 r r_ <=> RingHomo f2 r r_)
   ring_homo_add       |- !r r_ f. (r ~r~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x + y) = f x +_ f y)
   ring_homo_mult      |- !r r_ f. (r ~r~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x * y) = f x *_ f y)
   ring_homo_neg       |- !r r_ f. (r ~r~ r_) f ==> !x. x IN R ==> (f (-x) = $-_ (f x))
   ring_homo_sub       |- !r r_ f. (r ~r~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x - y) = f x -_ f y)
   ring_homo_num       |- !r r_ f. (r ~r~ r_) f ==> !n. f (##n) = ##_ #1_ n
   ring_homo_exp       |- !r r_ f. (r ~r~ r_) f ==> !x. x IN R ==> !n. f (x ** n) = f x **_ n
   ring_homo_char_divides  |- !r r_ f. (r ~r~ r_) f ==> char r_ divides char r
   ring_homo_I_refl    |- !r. RingHomo I r r
   ring_homo_trans     |- !r s t f1 f2. RingHomo f1 r s /\ RingHomo f2 s t ==> RingHomo (f2 o f1) r t
   ring_homo_sym       |- !r r_ f. (r ~r~ r_) f /\ BIJ f R R_ ==> RingHomo (LINV f R) r_ r
   ring_homo_compose   |- !r s t f1 f2. RingHomo f1 r s /\ RingHomo f2 s t ==> RingHomo (f2 o f1) r t
   ring_homo_linv_homo |- !r r_ f. (r ~r~ r_) f /\ BIJ f R R_ ==> RingHomo (LINV f R) r_ r
   ring_homo_eq_zero   |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==> !x. x IN R ==> ((f x = #0_) <=> (x = #0))
   ring_homo_one_eq_zero       |- !r r_ f. (r ~r~ r_) f /\ (#1 = #0) ==> (#1_ = #0_)
   ring_homo_sum_num_property  |- !r r_ f. (r ~r~ r_) f ==>
                                  !c. 0 < c /\ c < char r_ ==> ##c <> #0 /\ ##_ #1_ c <> #0_
   ring_homo_num_nonzero       |- !r r_ f. (r ~r~ r_) f ==>
                                  !c. 0 < c /\ c < char r_ ==> ##c <> #0 /\ f (##c) <> #0_
   ring_homo_unit              |- !r r_ f. (r ~r~ r_) f ==> !x. unit x ==> unit_ (f x)
   ring_homo_unit_nonzero      |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !x. unit x ==> f x <> #0_
   ring_homo_unit_inv_element  |- !r r_ f. (r ~r~ r_) f ==> !x. unit x ==> |/_ (f x) IN R_
   ring_homo_unit_inv_nonzero  |- !r r_ f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !x. unit x ==> |/_ (f x) <> #0_
   ring_homo_unit_inv          |- !r r_ f. (r ~r~ r_) f ==> !x. unit x ==> ( |/_ (f x) = f ( |/ x))
   ring_homo_inv               |- !r r_ f. (r ~r~ r_) f ==> !x. unit x ==> (f ( |/ x) = |/_ (f x))

   Ring Isomorphisms:
   ring_iso_zero       |- !r r_ f. (r =r= r_) f ==> (f #0 = #0_)
   ring_iso_one        |- !r r_ f. (r =r= r_) f ==> (f #1 = #1_)
#  ring_iso_ids        |- !r r_ f. (r =r= r_) f ==> (f #0 = #0_) /\ (f #1 = #1_)
   ring_iso_element    |- !r r_ f. RingIso f r r_ ==> !x. x IN R ==> f x IN R_
   ring_iso_property   |- !r r_ f. Ring r /\ RingIso f r r_ ==> !x y. x IN R /\ y IN R ==>
                                   (f (x + y) = f x +_ f y) /\ (f (x * y) = f x *_ f y)
   ring_iso_cong       |- !r r_ f1 f2. Ring r /\ Ring r_ /\ (!x. x IN R ==> (f1 x = f2 x)) ==>
                                       (RingIso f1 r r_ <=> RingIso f2 r r_)
   ring_iso_add        |- !r r_ f. (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> (f (x + y) = f x +_ f y)
   ring_iso_mult       |- !r r_ f. (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> (f (x * y) = f x *_ f y)
   ring_iso_neg        |- !r r_ f. (r =r= r_) f ==> !x. x IN R ==> (f (-x) = $-_ (f x))
   ring_iso_sub        |- !r r_ f. (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> (f (x - y) = f x -_ f y)
   ring_iso_num        |- !r r_ f. (r =r= r_) f ==> !n. f (##n) = ##_ #1_ n
   ring_iso_exp        |- !r r_ f. (r =r= r_) f ==> !x. x IN R ==> !n. f (x ** n) = f x **_ n
   ring_iso_I_refl     |- !r. RingIso I r r
   ring_iso_trans      |- !r s t f1 f2. RingIso f1 r s /\ RingIso f2 s t ==> RingIso (f2 o f1) r t
   ring_iso_sym        |- !r r_ f. (r =r= r_) f ==> RingIso (LINV f R) r_ r
   ring_iso_compose    |- !r s t f1 f2. RingIso f1 r s /\ RingIso f2 s t ==> RingIso (f2 o f1) r t
   ring_iso_linv_iso   |- !r r_ f. (r =r= r_) f ==> RingIso (LINV f R) r_ r
   ring_iso_eq_zero    |- !r r_ f. (r =r= r_) f ==> !x. x IN R ==> ((f x = #0_) <=> (x = #0))
   ring_iso_card_eq    |- !r r_ f. RingIso f r r_ /\ FINITE R ==> (CARD R = CARD R_)
   ring_iso_char_eq    |- !r r_ f. (r =r= r_) f ==> (char r_ = char r)
   ring_iso_bij        |- !r r_ f. (r =r= r_) f ==> BIJ f R R_
   ring_iso_unit       |- !r r_ f. (r =r= r_) f ==> !x. unit x ==> unit_ (f x)
   ring_iso_nonzero    |- !r r_ f. (r =r= r_) f ==> !x. x IN R+ ==> f x IN R+_
   ring_iso_inv        |- !r r_ f. (r =r= r_) f ==> !x. unit x ==> (f ( |/ x) = |/_ (f x))
   ring_iso_eq_one     |- !r r_ f. (r =r= r_) f ==> !x. x IN R ==> ((f x = #1_) <=> (x = #1))
   ring_iso_inverse_element
                       |- !r r_ f. (r =r= r_) f ==> !y. y IN R_ ==> LINV f R y IN R /\ (y = f (LINV f R y))
   ring_iso_inverse    |- !r r_ f. (r =r= r_) f ==> !y. y IN R_ ==> ?x. x IN R /\ (y = f x)
   ring_iso_element_unique
                       |- !r r_ f. (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> ((f x = f y) <=> (x = y))

   Ring Automorphisms:
   ring_auto_zero      |- !r f. Ring r /\ RingAuto f r ==> (f #0 = #0)
   ring_auto_one       |- !r f. Ring r /\ RingAuto f r ==> (f #1 = #1)
   ring_auto_ids       |- !r f. Ring r /\ RingAuto f r ==> (f #0 = #0) /\ (f #1 = #1)
   ring_auto_element   |- !r f. RingAuto f r ==> !x. x IN R ==> f x IN R
   ring_auto_cong      |- !r f1 f2. Ring r /\ (!x. x IN R ==> (f1 x = f2 x)) ==>
                                    (RingAuto f1 r <=> RingAuto f2 r)
   ring_auto_compose   |- !r f1 f2. RingAuto f1 r /\ RingAuto f2 r ==> RingAuto (f1 o f2) r
   ring_auto_I         |- !r. RingAuto I r
   ring_auto_linv_auto |- !r f. Ring r /\ RingAuto f r ==> RingAuto (LINV f R) r
   ring_auto_bij       |- !r f. Ring r /\ RingAuto f r ==> f PERMUTES R

   Subrings:
   subring_element         |- !r s. subring s r ==> !x. x IN B ==> x IN R
   subring_carrier_subset  |- !r s. subring s r ==> B SUBSET R
   subring_carrier_finite  |- !r s. FiniteRing r /\ subring s r ==> FINITE B
   subring_finite_ring     |- !r s. FiniteRing r /\ s <= r ==> FiniteRing s
   subring_refl            |- !r. subring r r
   subring_trans           |- !r s t. subring r s /\ subring s t ==> subring r t
   subring_I_antisym       |- !r s. subring s r /\ subring r s ==> RingIso I s r
   subring_carrier_antisym |- !r s. subring s r /\ R SUBSET B ==> RingIso I s r
   subring_sum_subgroup    |- !r s. subring s r ==> subgroup s.sum r.sum
   subring_prod_submonoid  |- !r s. subring s r ==> submonoid s.prod r.prod
   subring_by_subgroup_submonoid |- !r s. s <= r <=>
                              Ring r /\ Ring s /\ subgroup s.sum r.sum /\ submonoid s.prod r.prod
   subring_homo_homo       |- !r s r_ f. subring s r /\ RingHomo f r r_ ==> RingHomo f s r_

   Subring Theorems:
#  subring_zero          |- !r s. s <= r ==> (s.sum.id = #0)
#  subring_one           |- !r s. s <= r ==> (s.prod.id = #1)
   subring_ids           |- !r s. s <= r ==> (s.sum.id = #0) /\ (s.prod.id = #1)
#  subring_element_alt   |- !r s. s <= r ==> !x. x IN B ==> x IN R
   subring_property      |- !r s. Ring s /\ subring s r ==> !x y. x IN B /\ y IN B ==>
                                  (s.sum.op x y = x + y) /\ (s.prod.op x y = x * y)
   subring_add           |- !r s. s <= r ==> !x y. x IN B /\ y IN B ==> (s.sum.op x y = x + y)
   subring_mult          |- !r s. s <= r ==> !x y. x IN B /\ y IN B ==> (s.prod.op x y = x * y)
   subring_neg           |- !r s. s <= r ==> !x. x IN B ==> (s.sum.inv x = -x)
   subring_sub           |- !r s. s <= r ==> !x y. x IN B /\ y IN B ==> (ring_sub s x y = x - y)
   subring_num           |- !r s. s <= r ==> !n. s.sum.exp s.prod.id n = ##n
   subring_exp           |- !r s. s <= r ==> !x. x IN B ==> !n. s.prod.exp x n = x ** n
   subring_char_divides  |- !r s. s <= r ==> (char r) divides (char s)
   subring_char          |- !r s. s <= r ==> (char s = char r)
   subring_unit          |- !r s. s <= r ==> !x. Unit s x ==> unit x
   subring_unit_nonzero  |- !r s. s <= r /\ #1 <> #0 ==> !x. Unit s x ==> x <> #0
   subring_unit_inv_element |- !r s. s <= r ==> !x. Unit s x ==> Inv s x IN B
   subring_unit_inv_nonzero |- !r s. s <= r /\ #1 <> #0 ==> !x. Unit s x ==> Inv s x <> #0
   subring_unit_inv         |- !r s. s <= r ==> !x. Unit s x ==> Inv s x = |/ x
   subring_ring_iso_compose |- !r s r_ f. subring s r /\ RingIso f r r_ ==> RingHomo f s r_

   Homomorphic Image of Ring:
   homo_ring_def       |- !r f. homo_ring r f =
                          <|carrier := IMAGE f R; sum := homo_group r.sum f; prod := homo_group r.prod f|>
   homo_ring_property  |- !r f. (fR = IMAGE f R) /\ ((homo_ring r f).sum = homo_group r.sum f) /\
                                ((homo_ring r f).prod = homo_group r.prod f)
   homo_ring_ring      |- !r f. Ring r /\ RingHomo f r (homo_ring r f) ==> Ring (homo_ring r f)
   homo_ring_subring   |- !r s f. Ring r /\ Ring s /\ RingHomo f r s ==> subring (homo_ring r f) s
   homo_ring_by_inj    |- !r f. Ring r /\ INJ f R univ(:'b) ==> RingHomo f r (homo_ring r f)

   Homomorphic Image between Rings:
   ring_homo_image_def    |- !f r r_. ring_homo_image f r r_ =
                                     <|carrier := IMAGE f R;
                                           sum := homo_image f r.sum r_.sum;
                                          prod := homo_image f r.prod r_.prod
                                      |>
   ring_homo_image_carrier          |- !r r_ f. (ring_homo_image f r r_).carrier = IMAGE f R
   ring_homo_image_ring             |- !r r_ f. (r ~r~ r_) f ==> Ring (ring_homo_image f r r_)
   ring_homo_image_subring_subring  |- !r r_ f. (r ~r~ r_) f ==>
                                       !s. Ring s /\ subring s r ==> subring (ring_homo_image f s r_) r_
   ring_homo_image_is_subring       |- !r r_ f. (r ~r~ r_) f ==> subring (ring_homo_image f r r_) r_
   ring_homo_image_subring          |- !r r_ f. (r ~r~ r_) f ==> ring_homo_image f r r_ <= r_
   ring_homo_image_homo             |- !r r_ f. (r ~r~ r_) f ==> RingHomo f r (ring_homo_image f r r_)
   ring_homo_image_bij              |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==>
                                                BIJ f R (ring_homo_image f r r_).carrier
   ring_homo_image_iso              |- !r r_ f. (r ~r~ r_) f /\ INJ f R R_ ==>
                                                RingIso f r (ring_homo_image f r r_)
   ring_homo_image_surj_property    |- !r r_ f. Ring r /\ Ring r_ /\ SURJ f R R_ ==>
                                                RingIso I r_ (ring_homo_image f r r_)

   ring_homo_subring_homo       |- !r s r_ f. (r ~r~ r_) f /\ s <= r ==> (s ~r~ ring_homo_image f s r_) f
   ring_iso_subring_iso         |- !r s r_ f. (r =r= r_) f /\ s <= r ==> (s =r= ring_homo_image f s r_) f
   ring_homo_ring_homo_subring  |- !r r_ f. (r ~r~ r_) f ==> subring (ring_homo_image f r r_) r_
   ring_iso_ring_homo_subring   |- !r r_ f. (r =r= r_) f ==> subring (ring_homo_image f r r_) r_
   subring_ring_iso_ring_homo_subring
                                |- !r s r_ f. s <= r /\ (r =r= r_) f ==> ring_homo_image f s r_ <= r_

   Injective Image of Ring:
   ring_inj_image_def           |- !r f. Ring r ==> ring_inj_image r f =
      <|carrier := IMAGE f R;
            sum := <|carrier := IMAGE f R; op := (\x y. f (LINV f R x + LINV f R y)); id := f #0|>;
           prod := <|carrier := IMAGE f R; op := (\x y. f (LINV f R x * LINV f R y)); id := f #1|>
       |>
   ring_inj_image_carrier       |- !r f. (ring_inj_image r f).carrier = IMAGE f R
   ring_inj_image_alt           |- !f r. Ring r ==> ring_inj_image r f =
                                         <|carrier := IMAGE f R;
                                               sum := monoid_inj_image r.sum f;
                                              prod := monoid_inj_image r.prod f
                                          |>
   ring_inj_image_ring          |- !r f. Ring r /\ INJ f R univ(:'b) ==> Ring (ring_inj_image r f)
   ring_inj_image_sum_monoid    |- !r f. Ring r /\ INJ f R univ(:'b) ==> Monoid (ring_inj_image r f).sum
   ring_inj_image_sum_group     |- !r f. Ring r /\ INJ f R univ(:'b) ==> Group (ring_inj_image r f).sum
   ring_inj_image_sum_abelian_group
                                |- !r f. Ring r /\ INJ f R univ(:'b) ==> AbelianGroup (ring_inj_image r f).sum
   ring_inj_image_prod_monoid   |- !r f. Ring r /\ INJ f R univ(:'b) ==> Monoid (ring_inj_image r f).prod
   ring_inj_image_prod_abelian_monoid
                                |- !r f. Ring r /\ INJ f R univ(:'b) ==> AbelianMonoid (ring_inj_image r f).prod
   ring_inj_image_sum_group_homo
                      |- !r f. Ring r /\ INJ f R univ(:'b) ==> GroupHomo f r.sum (ring_inj_image r f).sum
   ring_inj_image_prod_monoid_homo
                      |- !r f. Ring r /\ INJ f R univ(:'b) ==> MonoidHomo f r.prod (ring_inj_image r f).prod
   ring_inj_image_ring_homo
                      |- !r f. Ring r /\ INJ f R univ(:'b) ==> RingHomo f r (ring_inj_image r f)
*)

(* ------------------------------------------------------------------------- *)
(* Homomorphisms, isomorphisms, endomorphisms, automorphisms and subrings.   *)
(* ------------------------------------------------------------------------- *)

(* A function f from r to s is a homomorphism if ring properties are preserved. *)
val RingHomo_def = Define`
  RingHomo f (r:'a ring) (s:'b ring) <=>
     (!x. x IN r.carrier ==> f x IN s.carrier) /\
     GroupHomo f (r.sum) (s.sum) /\
     MonoidHomo f (r.prod) (s.prod)
`;

(* A function f from r to s is an isomorphism if f is a bijective homomorphism. *)
val RingIso_def = Define `
  RingIso f r s <=> RingHomo f r s /\ BIJ f r.carrier s.carrier
`;

(* A ring homomorphism from r to r is an endomorphism. *)
val RingEndo_def = Define `RingEndo f r <=> RingHomo f r r`;

(* A ring isomorphism from r to r is an automorphism. *)
val RingAuto_def = Define `RingAuto f r <=> RingIso f r r`;

(* A subring s of r if identity is a homomorphism from s to r *)
val subring_def = Define `subring s r <=> RingHomo I s r`;

(* Overloads for Homomorphism and Isomorphisms with map *)
val _ = overload_on("~r~", ``\(r:'a ring) (r_:'b ring) f. Ring r /\ Ring r_ /\ RingHomo f r r_``);
val _ = overload_on("=r=", ``\(r:'a ring) (r_:'b ring) f. Ring r /\ Ring r_ /\ RingIso f r r_``);
(* make infix operators *)
val _ = set_fixity "~r~" (Infix(NONASSOC, 450)); (* same as relation *)
val _ = set_fixity "=r=" (Infix(NONASSOC, 450)); (* same as relation *)

(* Overloads for Ring of type 'b *)
val _ = overload_on("R_", ``(r_:'b ring).carrier``);
val _ = overload_on("R+_", ``ring_nonzero (r_:'b ring)``);
val _ = overload_on("#0_", ``(r_:'b ring).sum.id``);
val _ = overload_on("#1_", ``(r_:'b ring).prod.id``);
val _ = overload_on("+_", ``(r_:'b ring).sum.op``);
val _ = overload_on("*_", ``(r_:'b ring).prod.op``);
val _ = overload_on("-_", ``ring_sub (r_:'b ring)``);
val _ = overload_on("neg_", ``(r_:'b ring).sum.inv``); (* unary negation *)
val _ = overload_on("##_", ``(r_:'b ring).sum.exp``);
val _ = overload_on("**_", ``(r_:'b ring).prod.exp``);
val _ = overload_on("unit_", ``\x. x IN (Invertibles (r_:'b ring).prod).carrier``);
val _ = overload_on("|/_", ``(Invertibles (r_:'b ring).prod).inv``);
val _ = overload_on("Unit", ``\r x. x IN (Invertibles r.prod).carrier``); (* for any type *)
val _ = overload_on("Inv", ``\r. (Invertibles r.prod).inv``); (* for any type *)
(* make infix operators *)
val _ = set_fixity "+_" (Infixl 500); (* same as + in arithmeticScript.sml *)
val _ = set_fixity "-_" (Infixl 500); (* same as - in arithmeticScript.sml *)
val _ = set_fixity "*_" (Infixl 600); (* same as * in arithmeticScript.sml *)
val _ = set_fixity "**_" (Infixr 700); (* same as EXP in arithmeticScript.sml, infix right *)
(* 900 for numeric_negate *)
(* make unary symbolic *)
val _ = overload_on("-_", ``neg_``); (* becomes $-_ *)

(* ------------------------------------------------------------------------- *)
(* Ring Homomorphisms.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (r ~r~ r_) f ==> (f #0 = #0_) *)
(* Proof:
   Ring r ==> Group r.sum                        by ring_add_group
   Ring r_ ==> Group r_.sum                      by ring_add_group
   RingHomo f r r_ ==> GroupHomo f r.sum r_.sum  by RingHomo_def
   Hence true by group_homo_id.
*)
val ring_homo_zero = store_thm(
  "ring_homo_zero",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> (f #0 = #0_)``,
  rw_tac std_ss[ring_add_group, RingHomo_def, group_homo_id]);

(* Theorem: (r ~r~ r_) f ==> (f #1 = #1_) *)
(* Proof:
   Ring r ==> Monoid r.prod                         by ring_mult_monoid
   Ring r_ ==> Monoid r_.prod                       by ring_mult_monoid
   RingHomo f r r_ ==> MonoidHomo f r.prod r_.prod  by RingHomo_def
   Hence true by MonoidHomo_def.
*)
val ring_homo_one = store_thm(
  "ring_homo_one",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> (f #1 = #1_)``,
  rw_tac std_ss[ring_mult_monoid, RingHomo_def, MonoidHomo_def]);

(* Theorem: (r ~r~ r_) f ==> (f #0 = #0_) /\ (f #1 = #1_) *)
(* Proof: by ring_homo_zero, ring_homo_one *)
val ring_homo_ids = store_thm(
  "ring_homo_ids",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> (f #0 = #0_) /\ (f #1 = #1_)``,
  rw_tac std_ss[ring_homo_zero, ring_homo_one]);

(* export simple result *)
val _ = export_rewrites ["ring_homo_ids"];

(* Theorem: RingHomo f r r_ ==> !x. x IN R ==> f x IN R_ *)
(* Proof: by RingHomo_def *)
val ring_homo_element = store_thm(
  "ring_homo_element",
  ``!(r:'a ring) (r_:'b ring) f. RingHomo f r r_ ==> !x. x IN R ==> f x IN R_``,
  rw[RingHomo_def]);

(* Theorem: Ring r /\ RingHomo f r r_ ==>
            !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y)) /\ (f (x * y) = (f x) *_ (f y)) *)
(* Proof: by definitions. *)
val ring_homo_property = store_thm(
  "ring_homo_property",
  ``!(r:'a ring) (r_:'b ring) f. Ring r /\ RingHomo f r r_ ==>
    !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y)) /\ (f (x * y) = (f x) *_ (f y))``,
  rw[RingHomo_def, GroupHomo_def, MonoidHomo_def]);

(* Theorem: Ring r /\ Ring r_ /\ (!x. x IN R ==> (f1 x = f2 x)) ==> (RingHomo f1 r r_ = RingHomo f2 r r_) *)
(* Proof: by RingHomo_def, ring_add_group, group_homo_cong, ring_mult_monoid, monoid_homo_cong *)
val ring_homo_cong = store_thm(
  "ring_homo_cong",
  ``!(r:'a ring) (r_:'b ring) f1 f2. Ring r /\ Ring r_ /\ (!x. x IN R ==> (f1 x = f2 x)) ==>
                (RingHomo f1 r r_ = RingHomo f2 r r_)``,
  rw_tac std_ss[RingHomo_def, EQ_IMP_THM] >-
  metis_tac[ring_add_group, group_homo_cong] >-
  metis_tac[ring_mult_monoid, monoid_homo_cong] >-
  metis_tac[ring_add_group, group_homo_cong] >>
  metis_tac[ring_mult_monoid, monoid_homo_cong]);

(* Theorem: (r ~r~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y)) *)
(* Proof: by ring_homo_property. *)
val ring_homo_add = store_thm(
  "ring_homo_add",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y))``,
  rw[ring_homo_property]);

(* Theorem: (r ~r~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x * y) = (f x) *_ (f y)) *)
(* Proof: by ring_homo_property. *)
val ring_homo_mult = store_thm(
  "ring_homo_mult",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x * y) = (f x) *_ (f y))``,
  rw[ring_homo_property]);

(* Theorem: (r ~r~ r_) f ==> !x. x IN R ==> (f (-x) = $-_ (f x)) *)
(* Proof:
   Ring r ==> Group r.sum                          by ring_add_group
   Ring r_ ==> Group r_.sum                        by ring_add_group
   RingHomo f r r_ ==> GroupHomo f r.sum r_.sum    by RingHomo_def
   Hence true                                      by group_homo_inv
*)
val ring_homo_neg = store_thm(
  "ring_homo_neg",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !x. x IN R ==> (f (-x) = $-_ (f x))``,
  rw[ring_add_group, RingHomo_def, group_homo_inv]);

(* Theorem: (r ~r~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x - y) = (f x) -_ (f y)) *)
(* Proof:
       f (x - y)
     = f (x + -y)              by ring_sub_def
     = (f x) +_ f (- y)        by ring_homo_add, ring_neg_element
     = (f x) +_ ($-_ (f y))    by ring_homo_neg
     = (f x) -_ (f y)          by ring_sub_def
*)
val ring_homo_sub = store_thm(
  "ring_homo_sub",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !x y. x IN R /\ y IN R ==> (f (x - y) = (f x) -_ (f y))``,
  metis_tac[ring_sub_def, ring_homo_add, ring_homo_neg, ring_neg_element]);

(* Theorem: (r ~r~ r_) f ==> !n. f ##n = ##_ #1_ n *)
(* Proof:
   By induction on n.
   Base case: f (##0) = ##_ #1_ 0
     f (## 0)
   = f #0          by ring_num_0
   = #1_           by ring_homo_zero
   = ##_ #1_ 0     by ring_num_0
   Step case: f (##n) = ##_ #1_ n ==> f (##(SUC n)) = ##_ #1_ (SUC n)
     f (##(SUC n))
   = f (#1 + ##n)          by ring_num_SUC
   = (f #1) +_ (f ##n)     by ring_homo_property
   = #1_ +_ (f ##n)        by ring_homo_one
   = #1_ +_ (##_ #1_ n)    by induction hypothesis
   = ##_ #1_ (SUC n)       by ring_num_SUC
*)
val ring_homo_num = store_thm(
  "ring_homo_num",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !n. f ##n = ##_ #1_ n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `f (##(SUC n)) = f (#1 + ##n)` by rw[] >>
  `_ = (f #1) +_ (f ##n)` by rw[ring_homo_property] >>
  `_ = #1_ +_ (f ##n)` by metis_tac[ring_homo_one] >>
  rw[]);

(* Theorem: (r ~r~ r_) f ==> !x. x IN R ==> !n. f (x ** n) = (f x) **_ n *)
(* Proof:
   By induction on n.
   Base case: f (x ** 0) = f x **_ 0
     f (x ** 0)
   = f #1          by ring_exp_0
   = #1_           by ring_homo_one
   = f x **_ 0     by ring_exp_0
   Step case: f (x ** n) = f x **_ n ==> f (x ** SUC n) = (f x) **_ SUC n
     f (x ** SUC n)
   = f (x * x ** n)              by ring_exp_SUC
   = (f x) *_ (f (x ** n))       by ring_homo_property
   = (f x) *_ (f x **_ n)        by induction hypothesis
   = (f x) **_ SUC n             by ring_exp_SUC
*)
val ring_homo_exp = store_thm(
  "ring_homo_exp",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !x. x IN R ==> !n. f (x ** n) = (f x) **_ n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `f (x ** SUC n) = f (x * x ** n)` by rw[] >>
  `_ = (f x) *_ (f (x ** n))` by rw[ring_homo_property] >>
  rw[]);

(* Theorem: If two rings r and s have a ring homomorphism, then (char s) divides (char f).
            (r ~r~ r_) f ==> (char r_) divides (char r) *)
(* Proof:
   Let n = char r, m = char r_. This is to show: m divides n.
   If n = 0, result is true by ALL_DIVIDES_0.
   If n <> 0, 0 < n.
   then  ##n = #0           by char_property
   so  f ##n = f #0
   or ##_ #1_ n = #0_       by ring_homo_num, ring_homo_zero
   and result follows       by ring_char_divides.
*)
val ring_homo_char_divides = store_thm(
  "ring_homo_char_divides",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> (char r_) divides (char r)``,
  rpt strip_tac >>
  Cases_on `char r = 0` >-
  rw_tac std_ss[ALL_DIVIDES_0] >>
  `0 < char r` by decide_tac >>
  metis_tac[char_property, ring_homo_num, ring_homo_zero, ring_char_divides]);

(* Theorem: RingHomo I r r *)
(* Proof:
   By RingHomo_def, this is to show:
   (1) GroupHomo I r.sum r.sum, true by group_homo_I_refl
   (2) GroupHomo I f* f*, true by group_homo_I_refl
*)
val ring_homo_I_refl = store_thm(
  "ring_homo_I_refl",
  ``!r:'a ring. RingHomo I r r``,
  rw_tac std_ss[RingHomo_def, group_homo_I_refl, monoid_homo_I_refl]);

(* Theorem: RingHomo f1 r s /\ RingHomo f2 s t ==> RingHomo f2 o f1 r t *)
(* Proof:
   By RingHomo_def, this is to show:
   (1) GroupHomo f1 r.sum s.sum /\ GroupHomo f2 s.sum t.sum ==>  GroupHomo (f2 o f1) r.sum t.sum
       True by group_homo_trans.
   (2) MonoidHomo f1 r.prod s.prod /\ MonoidHomo f2 s.prod t.pro ==> MonoidHomo (f2 o f1) r.prod t.prod
       True by monoid_homo_trans.
*)
val ring_homo_trans = store_thm(
  "ring_homo_trans",
  ``!(r:'a ring) (s:'b ring) (t:'c ring). !f1 f2. RingHomo f1 r s /\ RingHomo f2 s t ==> RingHomo (f2 o f1) r t``,
  rw_tac std_ss[RingHomo_def] >| [
    metis_tac[group_homo_trans],
    metis_tac[monoid_homo_trans]
  ]);

(* Theorem: (r ~r~ r_) f /\ BIJ f R R_ ==> RingHomo (LINV f R) r_ r *)
(* Proof:
   Note BIJ f R R_
    ==> BIJ (LINV f R) R_ R                  by BIJ_LINV_BIJ
   By RingHomo_def, this is to show:
   (1) x IN R_ ==> LINV f R x IN R
       With BIJ (LINV f R) R_ R
        ==> INJ (LINV f R) R_ R              by BIJ_DEF
        ==> x IN R_ ==> LINV f R x IN R      by INJ_DEF
   (2) GroupHomo f r.sum r_.sum /\ BIJ f R R_ ==> GroupHomo (LINV f R) r_.sum r.sum
       Since Ring r
         ==> Group r.sum /\ (r.sum.carrier = R)      by ring_add_group
         and Ring r_ ==> r_.sum.carrier = R_         by ring_add_group
       Hence GroupHomo (LINV f R) r_.sum r.sum       by group_homo_sym
   (3) MonoidHomo f r.prod r_.prod /\ BIJ f R R_ ==> MonoidHomo (LINV f R) r_.prod r.prod
       Since Ring r
         ==> Group r.prod /\ (r.prod.carrier = R)    by ring_mult_monoid
         and Ring r_ ==> r_.prod.carrier = R_        by ring_mult_monoid
       Hence MonoidHomo (LINV f R) r_.prod r.prod    by monoid_homo_sym
*)
val ring_homo_sym = store_thm(
  "ring_homo_sym",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ BIJ f R R_ ==> RingHomo (LINV f R) r_ r``,
  rpt strip_tac >>
  `BIJ (LINV f R) R_ R` by rw[BIJ_LINV_BIJ] >>
  fs[RingHomo_def] >>
  rpt strip_tac >-
  metis_tac[BIJ_DEF, INJ_DEF] >-
 (`Group r.sum /\ (r.sum.carrier = R)` by rw[ring_add_group] >>
  `r_.sum.carrier = R_` by rw[ring_add_group] >>
  metis_tac[group_homo_sym]) >>
  `Monoid r.prod /\ (r.prod.carrier = R)` by rw[ring_mult_monoid] >>
  `r_.prod.carrier = R_` by rw[ring_mult_monoid] >>
  metis_tac[monoid_homo_sym]);

Theorem ring_homo_sym_any:
  Ring r /\ Ring s /\ RingHomo f r s /\
  (!x. x IN s.carrier ==> i x IN r.carrier /\ f (i x) = x) /\
  (!x. x IN r.carrier ==> i (f x) = x)
  ==>
  RingHomo i s r
Proof
  rpt strip_tac
  \\ fs[RingHomo_def]
  \\ conj_tac
  >- (
    irule group_homo_sym_any
    \\ conj_tac >- metis_tac[Ring_def, AbelianGroup_def]
    \\ qexists_tac`f`
    \\ metis_tac[ring_carriers] )
  \\ irule monoid_homo_sym_any
  \\ conj_tac >- metis_tac[Ring_def, AbelianMonoid_def]
  \\ qexists_tac`f`
  \\ metis_tac[ring_carriers]
QED

(* Theorem: RingHomo f1 r s /\ RingHomo f2 s t ==> RingHomo (f2 o f1) r t *)
(* Proof:
   By RingHomo_def, this is to show:
   (1) GroupHomo f1 r.sum s.sum /\ GroupHomo f2 s.sum t.sum ==> GroupHomo (f2 o f1) r.sum t.sum
       True by group_homo_compose.
   (2) MonoidHomo f1 r.prod s.prod /\ MonoidHomo f2 s.prod t.prod ==> MonoidHomo (f2 o f1) r.prod t.prod
       True by monoid_homo_compose
*)
val ring_homo_compose = store_thm(
  "ring_homo_compose",
  ``!(r:'a ring) (s:'b ring) (t:'c ring).
   !f1 f2. RingHomo f1 r s /\ RingHomo f2 s t ==> RingHomo (f2 o f1) r t``,
  rw_tac std_ss[RingHomo_def] >-
  metis_tac[group_homo_compose] >>
  metis_tac[monoid_homo_compose]);
(* This is the same as ring_homo_trans *)

(* Theorem: (r ~r~ r_) f /\  /\ BIJ f R R_ ==> RingHomo (LINV f R) r_ r *)
(* Proof:
   By RingIso_def, RingHomo_def, this is to show:
   (1) BIJ f R R_ /\ x IN R_ ==> LINV f R x IN R
       True by BIJ_LINV_ELEMENT
   (2) BIJ f R R_ /\ GroupHomo (LINV f R) r_.sum r.sum
       Note Group r.sum                            by ring_add_group
        and R = r.sum.carrier                      by ring_carriers
        and R_ = r_.sum.carrier                    by ring_carriers
        ==> GroupIso f r.sum r_.sum                by GroupIso_def, BIJ f R R_
       Thus GroupHomo (LINV f R) r_.sum r.sum      by group_iso_linv_iso
   (3) BIJ f R R_ /\ MonoidHomo (LINV f R) r_.prod r.prod
       Note Monoid r.prod                          by ring_mult_monoid
        and R = r.prod.carrier                     by ring_carriers
        and R_ = r_.prod.carrier                   by ring_carriers
        ==> MonoidIso f r.prod r_.prod             by MonoidIso_def, BIJ f R R_
       Thus MonoidHomo (LINV f R) r_.prod r.prod   by monoid_iso_linv_iso
*)
val ring_homo_linv_homo = store_thm(
  "ring_homo_linv_homo",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ BIJ f R R_ ==> RingHomo (LINV f R) r_ r``,
  rw_tac std_ss[RingHomo_def] >-
  metis_tac[BIJ_LINV_ELEMENT] >-
  metis_tac[group_iso_linv_iso, ring_add_group, ring_carriers, GroupIso_def] >>
  metis_tac[monoid_iso_linv_iso, ring_mult_monoid, ring_carriers, MonoidIso_def]);
(* This is the same as ring_homo_sym, direct proof. *)

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> !x. x IN R ==> ((f x = #0_) <=> (x = #0)) *)
(* Proof:
   If part: f x = #0_ ==> x = #0
      Note f #0 = #0_      by ring_homo_zero
       and #0 IN R         by ring_zero_element
      Thus x = #0          by INJ_DEF, x IN R
   Only-if part: x = #0 ==> f x = #0_
      True                 by ring_homo_zero
*)
val ring_homo_eq_zero = store_thm(
  "ring_homo_eq_zero",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==> !x. x IN R ==> ((f x = #0_) <=> (x = #0))``,
  metis_tac[ring_homo_zero, INJ_DEF, ring_zero_element]);

(* Theorem: (r ~r~ r_) f /\ (#1 = #0) ==> (#1_ = #0_) *)
(* Proof:
   Since f #1 = #1_     by ring_homo_one
     and f #0 = #0_     by ring_homo_zero
   Hence #1_ = #0_
*)
val ring_homo_one_eq_zero = store_thm(
  "ring_homo_one_eq_zero",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ (#1 = #0) ==> (#1_ = #0_)``,
  metis_tac[ring_homo_one, ring_homo_zero]);

(* Theorem: (r ~r~ r_) f ==> !c:num. 0 < c /\ c < char r_ ==> ##c <> #0 /\ ##_ #1_ c <> #0_ *)
(* Proof:
   This is to show:
   (1) ##c <> #0
       By contradiction.
       Suppose ##c = #0.
          Then (char r) divides c   by ring_char_divides
            or (char r) <= c        by DIVIDES_LE, 0 < c.
           But 0 < c means c <> 0
         Hence char r <> 0          by ZERO_DIVIDES
            or 0 < char r
           Now (char r_) divides (char r)   by ring_homo_char_divides
            so (char r_) <= (char r)        by DIVIDES_LE, 0 < char r.
            or c < char r                   by c < char r_
       This is a contradiction with (char r) <= c.
   (2) ##_ #1_ c <> #0_
       By contradiction.
       Suppose ##_ #1_ c = #0_.
          Then (char r_) divides c          by ring_char_divides
            so (char r_) <= c               by DIVIDES_LE, 0 < c.
       This is a contradiction with given c < (char r_).
*)
val ring_homo_sum_num_property = store_thm(
  "ring_homo_sum_num_property",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !c:num. 0 < c /\ c < char r_ ==> ##c <> #0 /\ ##_ #1_ c <> #0_``,
  rpt strip_tac >| [
    `(char r) divides c` by rw[GSYM ring_char_divides] >>
    `(char r) <= c` by rw[DIVIDES_LE] >>
    `c <> 0` by decide_tac >>
    `char r <> 0` by metis_tac[ZERO_DIVIDES] >>
    `0 < char r` by decide_tac >>
    `(char r_) divides (char r)` by metis_tac[ring_homo_char_divides] >>
    `(char r_) <= (char r)` by rw[DIVIDES_LE] >>
    decide_tac,
    `(char r_) divides c` by rw[GSYM ring_char_divides] >>
    `(char r_) <= c` by rw[DIVIDES_LE] >>
    decide_tac
  ]);

(* Theorem: (r ~r~ r_) f ==> !c:num. 0 < c /\ c < char r_ ==>  ##c <> #0 /\ f (##c) <> #0_ *)
(* Proof:
   Given 0 < c /\ c < char r_,
         ##c <> #0 /\ ##_ #1_ c <> #0_   by ring_homo_sum_num_property
     f (##c)
   = ##_ #1_ c      by ring_homo_num
   <> #0_           by above
*)
val ring_homo_num_nonzero = store_thm(
  "ring_homo_num_nonzero",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !c:num. 0 < c /\ c < char r_ ==>  ##c <> #0 /\ f (##c) <> #0_``,
  metis_tac[ring_homo_num, ring_homo_sum_num_property]);

(* Theorem: (r ~r~ r_) f ==> !x. unit x ==> unit_ (f x) *)
(* Proof:
       unit x
   ==> x IN R                             by ring_unit_element
   ==> |/ x IN R                          by ring_unit_inv_element
   ==> (f x) IN R_ /\ (f ( |/ x)) IN R_   by ring_homo_element
     #1_
   = f #1                      by ring_homo_one
   = f (x * |/ x)              by ring_unit_rinv
   = (f x) *_ (f ( |/ x))      by ring_homo_property
   Hence true                  by ring_unit_property
*)
val ring_homo_unit = store_thm(
  "ring_homo_unit",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !x. unit x ==> unit_ (f x)``,
  rpt strip_tac >>
  `x IN R` by rw[ring_unit_element] >>
  `|/ x IN R` by rw[ring_unit_inv_element] >>
  `(f x) IN R_ /\ (f ( |/ x)) IN R_` by metis_tac[ring_homo_element] >>
  `#1_ = f #1` by rw[ring_homo_one] >>
  `_ = f (x * |/ x)` by rw[ring_unit_rinv] >>
  `_ = (f x) *_ (f ( |/ x))` by rw[ring_homo_property] >>
  metis_tac[ring_unit_property]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==> !x. unit x ==> (f x) <> #0_ *)
(* Proof:
   By contradiction. Suppose (f x) = #0_.
   Since unit x ==> f x IN (Invertibles r_.prod).carrier   by ring_homo_unit
   But this contradicts the given #1_ <> #0_               by ring_unit_zero
*)
val ring_homo_unit_nonzero = store_thm(
  "ring_homo_unit_nonzero",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==> !x. unit x ==> (f x) <> #0_``,
  metis_tac[ring_homo_unit, ring_unit_zero]);

(* Theorem: (r ~r~ r_) f ==> !x. unit x ==> |/_ (f x) = f ( |/ x) *)
(* Proof:
       unit x
   ==> x IN R                             by ring_unit_element
   ==> |/ x IN R                          by ring_unit_inv_element
   ==> (f x) IN R_ /\ (f ( |/ x)) IN R_   by ring_homo_element
     (f x) *_ (f ( |/ x))
   = f (x * |/ x)              by ring_homo_property
   = f #1                      by ring_unit_rinv
   = #1_                       by ring_homo_one
   Since unit_ (f x)           by ring_homo_unit
   Hence |/_ (f x) = f ( |/x)  by ring_unit_rinv_unique
*)
val ring_homo_unit_inv = store_thm(
  "ring_homo_unit_inv",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !x. unit x ==> |/_ (f x) = f ( |/ x)``,
  rpt strip_tac >>
  `x IN R` by rw[ring_unit_element] >>
  `|/ x IN R` by rw[ring_unit_inv_element] >>
  `(f x) IN R_ /\ (f ( |/ x)) IN R_` by metis_tac[ring_homo_element] >>
  `(f x) *_ (f ( |/ x)) = f (x * |/x)` by rw[ring_homo_property] >>
  `_ = f #1` by rw[ring_unit_rinv] >>
  `_ = #1_` by rw[ring_homo_one] >>
  metis_tac[ring_homo_unit, ring_unit_rinv_unique]);

(* Theorem: (r ~r~ r_) f ==> !x. unit x ==> |/_ (f x) IN R_ *)
(* Proof:
   Note unit_ (f x)        by ring_homo_unit
   Thus |/_ (f x) IN R_    by ring_unit_inv_element
*)
val ring_homo_unit_inv_element = store_thm(
  "ring_homo_unit_inv_element",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !x. unit x ==> |/_ (f x) IN R_``,
  metis_tac[ring_homo_unit, ring_unit_inv_element]);

(* Theorem: (r ~r~ r_) f /\ #1_ <> #0_ ==> !x. unit x ==> |/_ (f x) <> #0_ *)
(* Proof:
   Note unit_ (f x)        by ring_homo_unit
   Thus |/_ (f x) <> #0_   by ring_unit_inv_nonzero
*)
val ring_homo_unit_inv_nonzero = store_thm(
  "ring_homo_unit_inv_nonzero",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ #1_ <> #0_ ==>
   !x. unit x ==> |/_ (f x) <> #0_``,
  metis_tac[ring_homo_unit, ring_unit_inv_nonzero]);

(* Theorem: (r ~r~ r_) f ==> !x. unit x ==> (f ( |/ x) = |/_ (f x)) *)
(* Proof:
       unit x
   ==> x IN R                             by ring_unit_element
   ==> |/ x IN R                          by ring_unit_inv_element
   ==> (f x) IN R_ /\ (f ( |/ x)) IN R_   by ring_homo_element
     #1_
   = f #1                                 by ring_homo_one
   = f (x * |/ x)                         by ring_unit_rinv
   = (f x) *_ (f ( |/ x))                 by ring_homo_property
   Since unit_ (f x)                      by ring_homo_unit
   Hence f ( |/ x) = |/_ (f x)            by ring_unit_rinv_unique
*)
val ring_homo_inv = store_thm(
  "ring_homo_inv",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> !x. unit x ==> (f ( |/ x) = |/_ (f x))``,
  rpt strip_tac >>
  `x IN R` by rw[ring_unit_element] >>
  `|/ x IN R` by rw[ring_unit_inv_element] >>
  `(f x) IN R_ /\ (f ( |/ x)) IN R_` by metis_tac[ring_homo_element] >>
  `#1_ = f #1` by rw[ring_homo_one] >>
  `_ = f (x * |/ x)` by rw[ring_unit_rinv] >>
  `_ = (f x) *_ (f ( |/ x))` by rw[ring_homo_property] >>
  `unit_ (f x)` by metis_tac[ring_homo_unit] >>
  rw[ring_unit_rinv_unique]);

(* ------------------------------------------------------------------------- *)
(* Ring Isomorphisms.                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (r =r= r_) f ==> (f #0 = #0_) *)
(* Proof: by RingIso_def, ring_homo_zero *)
val ring_iso_zero = store_thm(
  "ring_iso_zero",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> (f #0 = #0_)``,
  rw[RingIso_def]);

(* Theorem: (r =r= r_) f ==> (f #1 = #1_) *)
(* Proof: by RingIso_def, ring_homo_zero *)
val ring_iso_one = store_thm(
  "ring_iso_one",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> (f #1 = #1_)``,
  rw[RingIso_def]);

(* Theorem: (r =r= r_) f ==> (f #0 = #0_) /\ (f #1 = #1_) *)
(* Proof: by ring_iso_zero, ring_iso_one. *)
val ring_iso_ids = store_thm(
  "ring_iso_ids",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> (f #0 = #0_) /\ (f #1 = #1_)``,
  rw_tac std_ss[ring_iso_zero, ring_iso_one]);

(* export simple result *)
val _ = export_rewrites ["ring_iso_ids"];

(* Theorem: RingIso f r r_ ==> !x. x IN R ==> f x IN R_ *)
(* Proof: by RingIso_def, ring_homo_element *)
val ring_iso_element = store_thm(
  "ring_iso_element",
  ``!(r:'a ring) (r_:'b ring) f. RingIso f r r_ ==> !x. x IN R ==> f x IN R_``,
  metis_tac[RingIso_def, ring_homo_element]);

(* Theorem: Ring r /\ RingIso f r r_ ==>
            !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y)) /\ (f (x * y) = (f x) *_ (f y)) *)
(* Proof: by RingIso_def, ring_homo_property *)
val ring_iso_property = store_thm(
  "ring_iso_property",
  ``!(r:'a ring) (r_:'b ring) f. Ring r /\ RingIso f r r_ ==>
    !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y)) /\ (f (x * y) = (f x) *_ (f y))``,
  rw[RingIso_def, ring_homo_property]);

(* Theorem: Ring r /\ Ring r_ /\ (!x. x IN R ==> (f1 x = f2 x)) ==> (RingIso f1 r r_ <=> RingIso f2 r r_) *)
(* Proof:
   If part: RingIso f1 r r_ ==> RingIso f2 r r_
      By RingIso_def, RingHomo_def, this is to show:
      (1) x IN R ==> f2 x IN R_, true         by implication, given x IN R ==> f1 x IN R_
      (2) GroupHomo f2 r.sum r_.sum, true     by GroupHomo_def, ring_carriers, ring_add_element
      (3) MonoidHomo f2 r.prod r_.prod, true  by MonoidHomo_def, ring_carriers, ring_mult_element, ring_one_element
      (4) BIJ f R R_ ==> BIJ f2 R R_, true    by BIJ_DEF, INJ_DEF, SURJ_DEF
   Only-if part: RingIso f2 r r_ ==> RingIso f1 r r_
      By RingIso_def, RingHomo_def, this is to show:
      (1) x IN R_ ==> f1 x IN R, true trivially, given x IN R_ ==> f1 x IN R
      (2) GroupHomo f1 r_.sum r.sum, true     by GroupHomo_def
      (3) MonoidHomo f1 r_.prod r.prod, true  by MonoidHomo_def
      (4) BIJ f2 R R_ ==> BIJ f1 R R), true   by BIJ_DEF, INJ_DEF, SURJ_DEF
*)
val ring_iso_cong = store_thm(
  "ring_iso_cong",
  ``!(r:'a ring) (r_:'b ring) f1 f2. Ring r /\ Ring r_ /\ (!x. x IN R ==> (f1 x = f2 x)) ==>
        (RingIso f1 r r_ <=> RingIso f2 r r_)``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    fs[RingIso_def, RingHomo_def] >>
    rpt strip_tac >-
    metis_tac[] >-
   (fs[GroupHomo_def] >>
    metis_tac[ring_carriers, ring_add_element]) >-
   (fs[MonoidHomo_def] >>
    metis_tac[ring_carriers, ring_mult_element, ring_one_element]) >>
    fs[BIJ_DEF, INJ_DEF, SURJ_DEF] >>
    metis_tac[],
    fs[RingIso_def, RingHomo_def] >>
    rpt strip_tac >-
    fs[GroupHomo_def] >-
    fs[MonoidHomo_def] >>
    fs[BIJ_DEF, INJ_DEF, SURJ_DEF] >>
    metis_tac[]
  ]);

(* Theorem: (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y)) *)
(* Proof: by RingIso_def, ring_homo_add *)
val ring_iso_add = store_thm(
  "ring_iso_add",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> (f (x + y) = (f x) +_ (f y))``,
  rw[RingIso_def, ring_homo_add]);

(* Theorem: (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> (f (x * y) = (f x) *_ (f y)) *)
(* Proof: by RingIso_def, ring_homo_mult *)
val ring_iso_mult = store_thm(
  "ring_iso_mult",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> (f (x * y) = (f x) *_ (f y))``,
  rw[RingIso_def, ring_homo_mult]);

(* Theorem: (r =r= r_) f ==> !x. x IN R ==> (f (-x) = $-_ (f x)) *)
(* Proof: by RingIso_def, ring_homo_neg *)
val ring_iso_neg = store_thm(
  "ring_iso_neg",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x. x IN R ==> (f (-x) = $-_ (f x))``,
  rw[RingIso_def, ring_homo_neg]);

(* Theorem: (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> (f (x - y) = (f x) -_ (f y)) *)
(* Proof: by RingIso_def, ring_homo_sub *)
val ring_iso_sub = store_thm(
  "ring_iso_sub",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> (f (x - y) = (f x) -_ (f y))``,
  rw[RingIso_def, ring_homo_sub]);

(* Theorem: (r =r= r_) f ==> !n. f (##n) = ##_ #1_ n *)
(* Proof: by RingIso_def, ring_homo_num *)
val ring_iso_num = store_thm(
  "ring_iso_num",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !n. f (##n) = ##_ #1_ n``,
  rw[RingIso_def, ring_homo_num]);

(* Theorem: (r =r= r_) f ==> !x. x IN R ==> !n. f (x ** n) = (f x) **_ n *)
(* Proof: by RingIso_def, ring_homo_exp *)
val ring_iso_exp = store_thm(
  "ring_iso_exp",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x. x IN R ==> !n. f (x ** n) = (f x) **_ n``,
  rw[RingIso_def, ring_homo_exp]);

(* Theorem: RingIso I r r *)
(* Proof:
   By RingIso_def, this is to show:
   (1) RingHomo I r r, true by ring_homo_I_refl
   (2) BIJ I R R, true      by BIJ_I_SAME
*)
val ring_iso_I_refl = store_thm(
  "ring_iso_I_refl",
  ``!r:'a ring. RingIso I r r``,
  rw[RingIso_def, ring_homo_I_refl, BIJ_I_SAME]);

(* Theorem: RingIso f1 r s /\ RingIso f2 s t ==> RingIso (f2 o f1) r t *)
(* Proof:
   By RingIso_def, this is to show:
   (1) RingHomo f1 r s /\ RingHomo f2 s t ==> RingHomo (f2 o f1) r t
       True by ring_homo_trans.
   (2) BIJ f1 R s.carrier /\ BIJ f2 s.carrier t.carrier ==> BIJ (f2 o f1) R t.carrier
       True by BIJ_COMPOSE.
*)
val ring_iso_trans = store_thm(
  "ring_iso_trans",
  ``!(r:'a ring) (s:'b ring) (t:'c ring). !f1 f2. RingIso f1 r s /\ RingIso f2 s t ==> RingIso (f2 o f1) r t``,
  rw[RingIso_def] >-
  metis_tac[ring_homo_trans] >>
  metis_tac[BIJ_COMPOSE]);
(* This is the same as ring_iso_trans. *)

(* Theorem: (r =r= r_) f ==> RingIso (LINV f R) r_ r *)
(* Proof:
   By RingIso_def, this is to show:
   (1) RingHomo f r r_ /\ BIJ f R R_ ==> RingHomo (LINV f R) r_ r, true  by ring_homo_sym
   (2) BIJ f R R_ ==> BIJ (LINV f R) R_ R, true                          by BIJ_LINV_BIJ
*)
val ring_iso_sym = store_thm(
  "ring_iso_sym",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> RingIso (LINV f R) r_ r``,
  rw[RingIso_def, ring_homo_sym, BIJ_LINV_BIJ]);

Theorem ring_iso_sym_any:
  Ring r /\ Ring s /\ RingIso f r s /\
  (!x. x IN s.carrier ==> i x IN r.carrier /\ f (i x) = x) /\
  (!x. x IN r.carrier ==> i (f x) = x)
  ==>
  RingIso i s r
Proof
  rpt strip_tac \\ fs[RingIso_def]
  \\ conj_tac >- metis_tac[ring_homo_sym_any]
  \\ simp[BIJ_IFF_INV]
  \\ qexists_tac`f`
  \\ metis_tac[BIJ_DEF, INJ_DEF]
QED

(* Theorem: RingIso f1 r s /\ RingIso f2 s t ==> RingIso (f2 o f1) r t *)
(* Proof:
   By RingIso_def, this is to show:
   (1) RingHomo f1 r s /\ RingHomo f2 s t ==> RingHomo (f2 o f1) r t
       True by ring_homo_compose.
   (2) BIJ f1 R s.carrier /\ BIJ f2 s.carrier t.carrier ==> BIJ (f2 o f1) R t.carrier
       True by BIJ_COMPOSE
*)
val ring_iso_compose = store_thm(
  "ring_iso_compose",
  ``!(r:'a ring) (s:'b ring) (t:'c ring).
   !f1 f2. RingIso f1 r s /\ RingIso f2 s t ==> RingIso (f2 o f1) r t``,
  rw_tac std_ss[RingIso_def] >-
  metis_tac[ring_homo_compose] >>
  metis_tac[BIJ_COMPOSE]);

(* Theorem: Ring r /\ Ring r_ /\ RingIso f r r_ ==> RingIso (LINV f R) r_ r *)
(* Proof:
   By RingIso_def, RingHomo_def, this is to show:
   (1) BIJ f R R_ /\ x IN R_ ==> LINV f R x IN R
       True by BIJ_LINV_ELEMENT
   (2) BIJ f R R_ /\ GroupHomo (LINV f R) r_.sum r.sum
       Note Group r.sum                            by ring_add_group
        and R = r.sum.carrier                      by ring_carriers
        and R_ = r_.sum.carrier                    by ring_carriers
        ==> GroupIso f r.sum r_.sum                by GroupIso_def
       Thus GroupHomo (LINV f R) r_.sum r.sum      by group_iso_linv_iso
   (3) BIJ f R R_ /\ MonoidHomo (LINV f R) r_.prod r.prod
       Note Monoid r.prod                          by ring_mult_monoid
        and R = r.prod.carrier                     by ring_carriers
        and R_ = r_.prod.carrier                   by ring_carriers
        ==> MonoidIso f r.prod r_.prod             by MonoidIso_def
       Thus MonoidHomo (LINV f R) r_.prod r.prod   by monoid_iso_linv_iso
   (4) BIJ f R R_ ==> BIJ (LINV f R) R_ R
       True by BIJ_LINV_BIJ
*)
val ring_iso_linv_iso = store_thm(
  "ring_iso_linv_iso",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> RingIso (LINV f R) r_ r``,
  rw_tac std_ss[RingIso_def, RingHomo_def] >-
  metis_tac[BIJ_LINV_ELEMENT] >-
  metis_tac[group_iso_linv_iso, ring_add_group, ring_carriers, GroupIso_def] >-
  metis_tac[monoid_iso_linv_iso, ring_mult_monoid, ring_carriers, MonoidIso_def] >>
  rw_tac std_ss[BIJ_LINV_BIJ]);
(* This is the same as ring_iso_sym, direct proof. *)

(* Theorem: (r =r= r_) f ==> !x. x IN R ==> ((f x = #0_) <=> (x = #0)) *)
(* Proof: by ring_homo_eq_zero, RingIso_def, BIJ_DEF *)
val ring_iso_eq_zero = store_thm(
  "ring_iso_eq_zero",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x. x IN R ==> ((f x = #0_) <=> (x = #0))``,
  rw_tac std_ss[ring_homo_eq_zero, RingIso_def, BIJ_DEF]);

(* Theorem: RingIso f r r_ /\ FINITE R ==> (CARD R = CARD R_ *)
(* Proof:
   Since BIJ f R R_               by RingIso_def
      so FINITE R ==> FINITE R_   by BIJ_FINITE
    thus CARD R = CARD R_         by FINITE_BIJ_CARD_EQ
*)
val ring_iso_card_eq = store_thm(
  "ring_iso_card_eq",
  ``!(r:'a ring) (r_:'b ring) f. RingIso f r r_ /\ FINITE R ==> (CARD R = CARD R_)``,
  metis_tac[RingIso_def, BIJ_FINITE, FINITE_BIJ_CARD_EQ]);

(* Theorem: (r =r= r_) f ==> (char r_ = char r) *)
(* Proof:
   Note RingIso (LINV f R) r_ r     by ring_iso_sym
   Thus (char r_) divides (char r)  by RingIso_def, ring_homo_char_divides,
    and (char r) divides (char r_)  by RingIso_def, ring_homo_char_divides
    ==> char r_ = char r            by DIVIDES_ANTISYM
*)
val ring_iso_char_eq = store_thm(
  "ring_iso_char_eq",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> (char r_ = char r)``,
  metis_tac[ring_iso_sym, DIVIDES_ANTISYM, RingIso_def, ring_homo_char_divides]);

(* Theorem: (r =r= r_) f ==> BIJ f R R_ *)
(* Proof: by RingIso_def *)
val ring_iso_bij = store_thm(
  "ring_iso_bij",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> BIJ f R R_``,
  rw_tac std_ss[RingIso_def]);

(* Theorem: (r =r= r_) f ==> !x. unit x ==> unit_ (f x) *)
(* Proof:
   Note RingIso f r r_ ==> RingHomo f r r_   by RingIso_def
   Thus !x. unit x ==> unit_ (f x)           by ring_homo_unit
*)
val ring_iso_unit = store_thm(
  "ring_iso_unit",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x. unit x ==> unit_ (f x)``,
  metis_tac[ring_homo_unit, RingIso_def]);

(* Theorem: (r =r= r_) f ==> !x. x IN R+ ==> !x. x IN R+ ==> (f x) IN R+_ *)
(* Proof:
   Note (r === r_) f
      = Ring r /\ Ring r_ /\ RingIso f r r_     by notation
   Note x IN R+ <=> x IN R /\ x <> #0           by ring_nonzero_eq
    But x IN R ==> f x IN R_                    by ring_iso_element
    and x <> #0 ==> f x <> #0_                  by ring_iso_eq_zero
     so (f x) IN R+_                            by ring_nonzero_eq
*)
val ring_iso_nonzero = store_thm(
  "ring_iso_nonzero",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x. x IN R+ ==> (f x) IN R+_``,
  metis_tac[ring_nonzero_eq, ring_iso_element, ring_iso_eq_zero]);

(* Theorem: (r =r= r_) f ==> !x. unit x ==> (f ( |/ x) = |/_ (f x)) *)
(* Proof:
   Note (r =r= r_) f
     = Ring r /\ Ring r_ /\ RingIso f r r_     by notation
   ==> Ring r /\ Ring r_ /\ RingdHomo f r r_   by RingIso_def
   ==> f ( |/ x) = |/_ (f x)                   by ring_homo_inv, unit x
*)
val ring_iso_inv = store_thm(
  "ring_iso_inv",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x. unit x ==> (f ( |/ x) = |/_ (f x))``,
  rw[RingIso_def, ring_homo_inv]);

(* Theorem: (r =r= r_) f ==> !x. x IN R ==> ((f x = #1_) <=> (x = #1)) *)
(* Proof:
   If part: f x = #1_ ==> x = #1
      Note INJ R R_         by RingIso_def, BIJ_DEF
     Since f x = f #1       by ring_iso_one
        so   x = #1         by INJ_DEF
   Only-if part: x = #1 ==> f x = #1_
      True by ring_iso_one
*)
val ring_iso_eq_one = store_thm(
  "ring_iso_eq_one",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x. x IN R ==> ((f x = #1_) <=> (x = #1))``,
  prove_tac[ring_iso_one, RingIso_def, BIJ_DEF, INJ_DEF, ring_one_element]);

(* Theorem: (r =r= r_) f ==> !y. y IN R_ ==> (LINV f R y) IN R /\ (y = f (LINV f R y)) *)
(* Proof: by RingIso_def, BIJ_DEF, BIJ_LINV_ELEMENT, BIJ_LINV_INV *)
val ring_iso_inverse_element = store_thm(
  "ring_iso_inverse_element",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !y. y IN R_ ==> (LINV f R y) IN R /\ (y = f (LINV f R y))``,
  metis_tac[RingIso_def, BIJ_DEF, BIJ_LINV_ELEMENT, BIJ_LINV_INV]);

(* Theorem: (r =r= r_) f ==> !y. y IN R_ ==> ?x. x IN R /\ (y = f x) *)
(* Proof: by ring_iso_inverse_element *)
val ring_iso_inverse = store_thm(
  "ring_iso_inverse",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !y. y IN R_ ==> ?x. x IN R /\ (y = f x)``,
  metis_tac[ring_iso_inverse_element]);

(* Theorem: (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> ((f x = f y) <=> (x = y)) *)
(* Proof:
   Note INJ R R_                   by RingIso_def, BIJ_DEF
   Hence (f x = f y) <=> (x = y)   by INJ_DEF
*)
val ring_iso_element_unique = store_thm(
  "ring_iso_element_unique",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> !x y. x IN R /\ y IN R ==> ((f x = f y) <=> (x = y))``,
  prove_tac[RingIso_def, BIJ_DEF, INJ_DEF]);

(* ------------------------------------------------------------------------- *)
(* Ring Automorphisms.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r /\ RingAuto f r ==> (f #0 = #0) *)
(* Proof: by RingAuto_def, ring_iso_zero *)
val ring_auto_zero = store_thm(
  "ring_auto_zero",
  ``!(r:'a ring) f. Ring r /\ RingAuto f r ==> (f #0 = #0)``,
  rw_tac std_ss[RingAuto_def, ring_iso_zero]);

(* Theorem: Ring r /\ RingAuto f r ==> (f #1 = #1) *)
(* Proof: by RingAuto_def, ring_iso_one *)
val ring_auto_one = store_thm(
  "ring_auto_one",
  ``!(r:'a ring) f. Ring r /\ RingAuto f r ==> (f #1 = #1)``,
  rw_tac std_ss[RingAuto_def, ring_iso_one]);

(* Theorem: Ring r /\ RingAuto f r ==> (f #0 = #0) /\ (f #1 = #1) *)
(* Proof: by ring_auto_zero, ring_auto_one. *)
val ring_auto_ids = store_thm(
  "ring_auto_ids",
  ``!(r:'a ring) f. Ring r /\ RingAuto f r ==> (f #0 = #0) /\ (f #1 = #1)``,
  rw_tac std_ss[ring_auto_zero, ring_auto_one]);

(* Theorem: RingAuto f r ==> !x. x IN R ==> f x IN R *)
(* Proof: by RingAuto_def, ring_iso_element *)
val ring_auto_element = store_thm(
  "ring_auto_element",
  ``!(r:'a ring) f. RingAuto f r ==> !x. x IN R ==> f x IN R``,
  metis_tac[RingAuto_def, ring_iso_element]);

(* Theorem: Ring r /\ (!x. x IN R ==> (f1 x = f2 x)) ==> (RingAuto f1 r <=> RingAuto f2 r) *)
(* Proof: by RingAuto_def, ring_iso_cong. *)
val ring_auto_cong = store_thm(
  "ring_auto_cong",
  ``!(r:'a ring) f1 f2. Ring r /\ (!x. x IN R ==> (f1 x = f2 x)) ==> (RingAuto f1 r <=> RingAuto f2 r)``,
  rw_tac std_ss[RingAuto_def, ring_iso_cong]);

(* Theorem: RingAuto I r *)
(* Proof: by RingAuto_def, ring_iso_I_refl. *)
val ring_auto_I = store_thm(
  "ring_auto_I",
  ``!(r:'a ring). RingAuto I r``,
  rw_tac std_ss[RingAuto_def, ring_iso_I_refl]);

(* Theorem: Ring r /\ RingAuto f r ==> RingAuto (LINV f R) r *)
(* Proof:
       RingAuto f r
   ==> RingIso f r r                by RingAuto_def
   ==> RingIso (LINV f R) r         by ring_iso_linv_iso
   ==> RingAuto (LINV f R) r        by RingAuto_def
*)
val ring_auto_linv_auto = store_thm(
  "ring_auto_linv_auto",
  ``!(r:'a ring) f. Ring r /\ RingAuto f r ==> RingAuto (LINV f R) r``,
  rw_tac std_ss[RingAuto_def, ring_iso_linv_iso]);


(* Theorem: Ring r /\ RingAuto f r ==> f PERMUTES R *)
(* Proof: by RingAuto_def, ring_iso_bij *)
val ring_auto_bij = store_thm(
  "ring_auto_bij",
  ``!(r:'a ring) f. Ring r /\ RingAuto f r ==> f PERMUTES R``,
  rw_tac std_ss[RingAuto_def, ring_iso_bij]);

(* ------------------------------------------------------------------------- *)
(* Subrings.                                                                 *)
(* ------------------------------------------------------------------------- *)

(* Overload on s.carrier, base carrier *)
val _ = overload_on("B", ``(s:'a ring).carrier``);

(* Overload on subring situation *)
val _ = overload_on("<=", ``\(s r):'a ring. Ring r /\ Ring s /\ subring s r``);

(* Theorem: subring s r ==> !x. x IN B ==> x IN R *)
(* Proof: by subring_def, RingHomo_def *)
val subring_element = store_thm(
  "subring_element",
  ``!(r s):'a ring. subring s r ==> !x. x IN B ==> x IN R``,
  rw_tac std_ss[subring_def, RingHomo_def]);

(* Theorem: subring s r ==> B SUBSET R *)
(* Proof: by subring_element, SUBSET_DEF *)
val subring_carrier_subset = store_thm(
  "subring_carrier_subset",
  ``!(r s):'a ring. subring s r ==> B SUBSET R``,
  metis_tac[subring_element, SUBSET_DEF]);

(* Theorem: FiniteRing r /\ subring s r ==> FINITE B *)
(* Proof:
   Since FiniteRing r ==> FINITE R    by FiniteRing_def
     and subring s r ==> B SUBSET R   by subring_carrier_subset
   Hence FINITE B                     by SUBSET_FINITE
*)
val subring_carrier_finite = store_thm(
  "subring_carrier_finite",
  ``!(r s):'a ring. FiniteRing r /\ subring s r ==> FINITE B``,
  metis_tac[FiniteRing_def, subring_carrier_subset, SUBSET_FINITE]);

(* Theorem: FiniteRing r /\ s <= r ==> FiniteRing s *)
(* Proof:
   Since FINITE B       by subring_carrier_finite
   Hence FiniteRing s   by FiniteRing_def
*)
val subring_finite_ring = store_thm(
  "subring_finite_ring",
  ``!(r s):'a ring. FiniteRing r /\ s <= r ==> FiniteRing s``,
  metis_tac[FiniteRing_def, subring_carrier_finite]);

(* Theorem: subring r r *)
(* Proof:
   By subring_def, this is to show:
   RingHomo I r r, true by ring_homo_I_refl.
*)
val subring_refl = store_thm(
  "subring_refl",
  ``!r:'a ring. subring r r``,
  rw[subring_def, ring_homo_I_refl]);

(* Theorem: subring r s /\ subring s t ==> subring r t *)
(* Proof:
   By subring_def, this is to show:
   RingHomo I r s /\ RingHomo I s t ==> RingHomo I r t
   Since I o I = I       by combinTheory.I_o_ID
   This is true          by ring_homo_trans
*)
val subring_trans = store_thm(
  "subring_trans",
  ``!(r s t):'a ring. subring r s /\ subring s t ==> subring r t``,
  prove_tac[subring_def, combinTheory.I_o_ID, ring_homo_trans]);

(* Theorem: subring s r /\ subring r s ==> RingIso I s r *)
(* Proof:
   By subring_def, RingIso_def, this is to show:
      RingHomo I s r /\ RingHomo I r s ==> BIJ I B R
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) x IN B ==> x IN R, true    by subring_carrier_subset, subring s r
   (2) x IN R ==> x IN B, true    by subring_carrier_subset, subring r s
*)
val subring_I_antisym = store_thm(
  "subring_I_antisym",
  ``!(r:'a ring) s. subring s r /\ subring r s ==> RingIso I s r``,
  rw_tac std_ss[subring_def, RingIso_def] >>
  fs[RingHomo_def] >>
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: subring s r /\ R SUBSET B ==> RingIso I s r *)
(* Proof:
   By subring_def, RingIso_def, this is to show:
      RingHomo I s r /\ R SUBSET B ==> BIJ I B R
   By BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
   (1) x IN B ==> x IN R, true    by subring_carrier_subset, subring s r
   (2) x IN R ==> x IN B, true    by R SUBSET B, given
*)
val subring_carrier_antisym = store_thm(
  "subring_carrier_antisym",
  ``!(r:'a ring) s. subring s r /\ R SUBSET B ==> RingIso I s r``,
  rpt (stripDup[subring_def]) >>
  rw_tac std_ss[RingIso_def] >>
  `B SUBSET R` by rw[subring_carrier_subset] >>
  fs[RingHomo_def, SUBSET_DEF] >>
  rw_tac std_ss[BIJ_DEF, INJ_DEF, SURJ_DEF]);

(* Theorem: subring s r ==> subgroup s.sum r.sum *)
(* Proof:
        subring s r
    <=> RingHomo I s r            by subring_def
    ==> GroupHomo I s.sum r.sum   by RingHomo_def
    ==> subgroup s.rum r.sum      by subgroup_def
*)
val subring_sum_subgroup = store_thm(
  "subring_sum_subgroup",
  ``!(r:'a ring) (s:'a ring). subring s r ==> subgroup s.sum r.sum``,
  rw_tac std_ss[subring_def, RingHomo_def, subgroup_def]);

(* Theorem: subring s r ==> submonoid s.prod r.prod *)
(* Proof:
        subring s r
    <=> RingHomo I s r               by subring_def
    ==> MonoidHomo I s.prod r.prod   by RingHomo_def
    ==> submonoid s.prod r.prod      by submonoid_def
*)
val subring_prod_submonoid = store_thm(
  "subring_prod_submonoid",
  ``!(r:'a ring) (s:'a ring). subring s r ==> submonoid s.prod r.prod``,
  rw_tac std_ss[subring_def, RingHomo_def, submonoid_def]);

(* Theorem: s <= r <=> Ring r /\ Ring s /\ subgroup s.sum r.sum /\ submonoid s.prod r.prod *)
(* Proof:
   If part: s <= r ==> Ring r /\ Ring s /\ subgroup s.sum r.sum /\ submonoid s.prod r.prod
      Note subgroup s.sum r.sum      by subring_sum_subgroup
       and submonoid s.prod r.prod   by subring_prod_submonoid
   Only-if part: Ring r /\ Ring s /\ subgroup s.sum r.sum /\ submonoid s.prod r.prod ==> s <= r
      Note subgroup s.sum r.sum
       ==> s.sum.carrier SUBSET r.sum.carrier   by subgroup_subset
       ==> B SUBSET R                           by ring_carriers
       ==> !x. x IN B ==> I x IN R              by SUBSET_DEF, I_THM
       and subgroup s.sum r.sum ==> GroupHomo I s.sum r.sum         by subgroup_def
       and submonoid s.prod r.prod ==> MonoidHomo I s.prod r.prod   by submonoid_def
      Thus RingHomo I s r            by RingHomo_def
        or s <= r                    by subring_def
*)
val subring_by_subgroup_submonoid = store_thm(
  "subring_by_subgroup_submonoid",
  ``!(r:'a ring) (s:'a ring). s <= r <=>
     Ring r /\ Ring s /\ subgroup s.sum r.sum /\ submonoid s.prod r.prod``,
  rw[EQ_IMP_THM] >-
  rw[subring_sum_subgroup] >-
  rw[subring_prod_submonoid] >>
  rw_tac std_ss[subring_def, RingHomo_def] >-
  metis_tac[subgroup_subset, ring_carriers, SUBSET_DEF] >-
  fs[subgroup_def] >>
  fs[submonoid_def]);

(* Theorem: subring s r /\ RingHomo f r r_ ==> RingHomo f s r_ *)
(* Proof:
   By RingHomo_def, this is to show:
   (1) subring s r /\ x IN B ==> f x IN R_, true          by subring_element
   (2) subring s r /\ GroupHomo f r.sum r_.sum ==> GroupHomo f s.sum r_.sum
       Note subgroup s.sum r.sum                          by subring_sum_subgroup
       Thus GroupHomo f s.sum r_.sum                      by subgroup_homo_homo
   (3) subring s r /\ MonoidHomo f r.prod r_.prod ==> MonoidHomo f s.prod r_.prod
       Note submonoid s.prod r.prod                       by subring_prod_submonoid
       Thus MonoidHomo f s.prod r_.prod                   by submonoid_homo_homo
*)
val subring_homo_homo = store_thm(
  "subring_homo_homo",
  ``!(r:'a ring) (s:'a ring) (r_:'b ring) f. subring s r /\ RingHomo f r r_ ==> RingHomo f s r_``,
  rw_tac std_ss[RingHomo_def] >-
  metis_tac[subring_element] >-
  metis_tac[subring_sum_subgroup, subgroup_homo_homo] >>
  metis_tac[subring_prod_submonoid, submonoid_homo_homo]);

(* ------------------------------------------------------------------------- *)
(* Subring Theorems                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: I x = x *)
val i_thm = combinTheory.I_THM;

(* Theorem: (f o g) x = f (g x) *)
val o_thm = combinTheory.o_THM;

(* Theorem: s <= r ==> s.sum.id = #0 *)
(* Proof: by subring_def, ring_homo_zero. *)
val subring_zero = store_thm(
  "subring_zero",
  ``!(r s):'a ring. s <= r ==> (s.sum.id = #0)``,
  metis_tac[subring_def, ring_homo_zero, i_thm]);

(* Theorem: s <= r ==> s.prod.id = #1 *)
(* Proof: by subring_def, ring_homo_one. *)
val subring_one = store_thm(
  "subring_one",
  ``!(r s):'a ring. s <= r ==> (s.prod.id = #1)``,
  metis_tac[subring_def, ring_homo_one, i_thm]);

(* export simple results *)
val _ = export_rewrites["subring_zero", "subring_one"];

(* Theorem: s <= r ==> s.sum.id = #0 /\ s.prod.id = #1 *)
(* Proof: by subring_zero, subring_one. *)
val subring_ids = store_thm(
  "subring_ids",
  ``!(r s):'a ring. s <= r ==> (s.sum.id = #0) /\ (s.prod.id = #1)``,
  rw[]);

(* Theorem: s <= r ==> !x. x IN B ==> x IN R *)
(* Proof: by subring_def, ring_homo_element. *)
val subring_element_alt = store_thm(
  "subring_element_alt",
  ``!(r s):'a ring. s <= r ==> !x. x IN B ==> x IN R``,
  metis_tac[subring_def, ring_homo_element, i_thm]);

(* Theorem: subring preserves sum and product. *)
(* Proof: by subring_def, ring_homo_property. *)
val subring_property = store_thm(
  "subring_property",
  ``!(r s):'a ring. Ring s /\ subring s r ==>
     !x y. x IN B /\ y IN B ==> (s.sum.op x y = x + y) /\ (s.prod.op x y = x * y)``,
  metis_tac[subring_def, ring_homo_property, i_thm]);

(* Theorem: s <= r ==> !x y. x IN B /\ y IN B ==> (s.sum.op x y = x + y) *)
(* Proof: by subring_def, ring_homo_add. *)
val subring_add = store_thm(
  "subring_add",
  ``!(r s):'a ring. s <= r ==> !x y. x IN B /\ y IN B ==> (s.sum.op x y = x + y)``,
  metis_tac[subring_def, ring_homo_add, i_thm]);

(* Theorem: s <= r ==> !x y. x IN B /\ y IN B ==> (s.prod.op x y = x * y) *)
(* Proof: by subring_def, ring_homo_mult. *)
val subring_mult = store_thm(
  "subring_mult",
  ``!(r s):'a ring. s <= r ==> !x y. x IN B /\ y IN B ==> (s.prod.op x y = x * y)``,
  metis_tac[subring_def, ring_homo_mult, i_thm]);

(* Theorem: s <= r ==> !x. x IN B ==> (s.sum.inv x = -x) *)
(* Proof: by subring_def, ring_homo_neg. *)
val subring_neg = store_thm(
  "subring_neg",
  ``!(r s):'a ring. s <= r ==> !x. x IN B ==> (s.sum.inv x = -x)``,
  metis_tac[subring_def, ring_homo_neg, i_thm]);

(* Theorem: s <= r ==> !x y. x IN B /\ y IN B ==> (ring_sub s x y = x - y) *)
(* Proof: by subring_def, ring_homo_sub. *)
val subring_sub = store_thm(
  "subring_sub",
  ``!(r s):'a ring. s <= r ==> !x y. x IN B /\ y IN B ==> (ring_sub s x y = x - y)``,
  metis_tac[subring_def, ring_homo_sub, i_thm]);

(* Theorem: s <= r ==> !n. s.sum.exp s.prod.id n = ##n *)
(* Proof: by subring_def, ring_homo_num. *)
val subring_num = store_thm(
  "subring_num",
  ``!(r s):'a ring. s <= r ==> !n. s.sum.exp s.prod.id n = ##n``,
  metis_tac[subring_def, ring_homo_num, i_thm]);

(* Theorem: s <= r ==> !n. s.sum.exp s.prod.id n = ##n *)
(* Proof: by subring_def, ring_homo_exp. *)
val subring_exp = store_thm(
  "subring_exp",
  ``!(r s):'a ring. s <= r ==> !x. x IN B ==> !n. s.prod.exp x n = x ** n``,
  metis_tac[subring_def, ring_homo_exp, i_thm]);

(* Theorem: s <= r ==> (char r) (char s) divides *)
(* Proof: by subring_def, ring_homo_char_divides. *)
val subring_char_divides = store_thm(
  "subring_char_divides",
  ``!(r s):'a ring. s <= r ==> (char r) divides (char s)``,
  metis_tac[subring_def, ring_homo_char_divides, i_thm]);

(* Note: This seems wrong, but
   ring_homo_char_divides |- !r s. Ring r /\ Ring s ==> !f. RingHomo f r s ==> (char s) divides (char r)
   subring_def |- !s r. subring s r <=> RingHomo I s r
   So for subring s r, it is really (char r) divides (char s).
*)

(* Note:
There is no such theorem: m divides n ==> subring (ZN m) (ZN n)
This is because (ZN m) is (mod m), but (ZN n) is (mod n), totally different operations.
This means: (GF p) a subring of (ZN n), where prime p divides n, is not true!
*)

(* Theorem: s <= r ==> (char s = char r) *)
(* Proof:
     char s
   = order s.sum s.prod.id              by char_def
   = case OLEAST k. period r.sum #1 k
       of NONE => 0 | SOME k => k       by order_def
   = case OLEAST k. 0 < k /\ (s.sum.exp s.prod.id k = s.sum.id)
       of NONE => 0 | SOME k => k       by period_def
   = case OLEAST k. 0 < k /\ (##k = #0)
       of NONE => 0 | SOME k => k       by subring_num, subring_ids
   = order r.sum #1                     by order_def, period_def
   = char r                             by char_def
*)
val subring_char = store_thm(
  "subring_char",
  ``!(r s):'a ring. s <= r ==> (char s = char r)``,
  rw[char_def, order_def, period_def, subring_exp] >>
  metis_tac[subring_num, subring_ids]);

(* Theorem: s <= r ==> !x. Unit s x ==> unit x *)
(* Proof:
   Note s <= r ==> RingHomo I s r   by subring_def
   Thus Unit s x = unit (I x)       by ring_homo_unit
                 = unit x           by I_THM
*)
val subring_unit = store_thm(
  "subring_unit",
  ``!(r:'a ring) s. s <= r ==> !x. Unit s x ==> unit x``,
  metis_tac[ring_homo_unit, subring_def, combinTheory.I_THM]);

(* Theorem: s <= r /\ #1 <> #0 ==> !x. Unit s x ==> x <> #0 *)
(* Proof:
   Note s <= r ==> RingHomo I s r   by subring_def
   Thus Unit s x <> s.prod.id       by ring_homo_unit_nonzero
     or          <> I #0 = #0       by I_THM
*)
val subring_unit_nonzero = store_thm(
  "subring_unit_nonzero",
  ``!(r:'a ring) s. s <= r /\ #1 <> #0 ==> !x. Unit s x ==> x <> #0``,
  metis_tac[ring_homo_unit_nonzero, subring_def, combinTheory.I_THM]);

(* Theorem: s <= r ==> !x. Unit s x ==> (Inv s x) IN s.carrier *)
(* Proof:
   Note Unit s x                by subring_unit
   Thus (Inv s x) IN s.carrier  by ring_unit_inv_element

   Note:
> ring_homo_unit_inv_element |> ISPEC ``s:'a ring`` |> ISPEC ``r:'a ring``;
val it = |- !f. (s ~r~ r) f ==> !x. Unit s x ==> |/ (f x) IN R: thm
   This is not what we want to prove.
*)
val subring_unit_inv_element = store_thm(
  "subring_unit_inv_element",
  ``!(r s):'a ring. s <= r ==> !x. Unit s x ==> (Inv s x) IN s.carrier``,
  rw[subring_unit, ring_unit_inv_element]);

(* Theorem: s <= r /\ #1 <> #0 ==> !x. Unit s x ==> (Inv s x) <> #0 *)
(* Proof:
   Note Unit s x                        by subring_unit
   Thus (Inv s x) <> s.prod.id          by subring_unit_inv_nonzero
    and s.sum.id = #0, s.prod.id = #1   by subring_ids

   Note:
> ring_homo_unit_inv_nonzero |> ISPEC ``s:'a ring`` |> ISPEC ``r:'a ring``;
val it = |- !f. (s ~r~ r) f /\ #1 <> #0 ==> !x. Unit s x ==> |/ (f x) <> #0
   This is not what we want to prove.
*)
val subring_unit_inv_nonzero = store_thm(
  "subring_unit_inv_nonzero",
  ``!(r s):'a ring. s <= r /\ #1 <> #0 ==> !x. Unit s x ==> (Inv s x) <> #0``,
  metis_tac[subring_unit, ring_unit_inv_nonzero, subring_ids]);

(* Theorem: s <= r ==> !x. Unit s x ==> (Inv s x = |/ x) *)
(* Proof:
   Note s <= r ==> RingHomo I s r   by subring_def
   Thus |/ (I x) = I (Inv s x)      by ring_homo_unit_inv
     or     |/ x = Inv s x          by I_THM

> ring_homo_unit_inv |> ISPEC ``s:'a ring`` |> ISPEC ``r:'a ring``;
val it = |- !f. (s ~r~ r) f ==> !x. Unit s x ==> |/ (f x) = f (Inv s x): thm
> ring_homo_inv |> ISPEC ``s:'a ring`` |> ISPEC ``r:'a ring``;
val it = |- !f. (s ~r~ r) f ==> !x. Unit s x ==> f (Inv s x) = |/ (f x): thm
*)
Theorem subring_unit_inv:
  !(r s):'a ring. s <= r ==> !x. Unit s x ==> (Inv s x = |/ x)
Proof
  metis_tac[ring_homo_unit_inv, subring_def, combinTheory.I_THM]
QED

(* Theorem: subring s r /\ RingIso f r r_ ==> RingHomo f s r_ *)
(* Proof:
   Note subring s r ==> RingHomo I s r         by subring_def
    and RingIso f r r_  ==> RingHomo f r r_    by RingIso_def
   Thus RingHomo (f o I) s r_                  by ring_homo_compose
     or RingHomo f s r_                        by I_o_ID
*)
val subring_ring_iso_compose = store_thm(
  "subring_ring_iso_compose",
  ``!(r:'a ring) (s:'a ring) (r_:'b ring) f. subring s r /\ RingIso f r r_ ==> RingHomo f s r_``,
  rpt strip_tac >>
  `RingHomo I s r` by rw[GSYM subring_def] >>
  `RingHomo f r r_` by metis_tac[RingIso_def] >>
  prove_tac[ring_homo_compose, combinTheory.I_o_ID]);

(* ------------------------------------------------------------------------- *)
(* Homomorphic Image of Ring.                                                *)
(* ------------------------------------------------------------------------- *)

(* Define the homomorphic image of a ring. *)
val homo_ring_def = Define`
  homo_ring (r:'a ring) (f:'a -> 'b) =
    <| carrier := IMAGE f R;
           sum := homo_group (r.sum) f;
          prod := homo_monoid (r.prod) f
     |>
`;

(* set overloading *)
val _ = overload_on ("fR", ``(homo_ring (r:'a ring) (f:'a -> 'b)).carrier``);

(* Theorem: Properties of homo_ring. *)
(* Proof: by homo_ring_def. *)
val homo_ring_property = store_thm(
  "homo_ring_property",
  ``!(r:'a ring) (f:'a -> 'b). (fR = IMAGE f R) /\
      ((homo_ring r f).sum = homo_group (r.sum) f) /\
      ((homo_ring r f).prod = homo_monoid (r.prod) f)``,
  rw_tac std_ss[homo_ring_def]);

(* Theorem: Homomorphic image of a Ring is a Ring. *)
(* Proof:
   This is to show each of these:
   (1) GroupHomo f r.sum (homo_ring r f).sum ==> AbelianGroup (homo_ring r f).sum
       Note AbelianGroup r.sum                           by Ring_def
        and (homo_ring r f).sum = homo_group r.sum f     by homo_ring_property
       Thus GroupHomo f r.sum (homo_group r.sum f)       by above
        ==> AbelianGroup (homo_group r.sum f)            by homo_group_abelian_group
         or AbelianGroup (homo_ring r f).sum             by above
   (2) MonoidHomo f r.prod (homo_ring r f).prod ==> AbelianMonoid (homo_ring r f).prod
       Note AbelianMonoid r.prod                         by Ring_def
        and (homo_ring r f).prod = homo_group r.prod f   by homo_ring_property
       Thus MonoidHomo f r.prod (homo_group r.prod f)    by above
        ==> AbelianMonoid (homo_group r.prod f)          by homo_monoid_abelian_monoid
         or AbelianMonoid (homo_ring r f).prod           by above
   (3) (homo_ring r f).sum.carrier = fR
            (homo_ring r f).sum.carrier
          = (homo_group r.sum f).carrier                 by homo_ring_property
          = IMAGE f r.sum.carrier                        by homo_monoid_property
          = IMAGE f R = fR                               by ring_carriers
   (4) (homo_ring r f).prod.carrier = fR
            (homo_ring r f).prod.carrier
          = (homo_group r.prod f).carrier                by homo_ring_property
          = IMAGE f r.prod.carrier                       by homo_monoid_property
          = IMAGE f R = fR                               by ring_carriers
   (5) x IN fR /\ y IN fR /\ z IN fR ==>
        (homo_ring r f).prod.op x ((homo_ring r f).sum.op y z) =
        (homo_ring r f).sum.op ((homo_ring r f).prod.op x y) ((homo_ring r f).prod.op x z)
       Note ?a. x = f a /\ a IN R                        by homo_ring_property, IN_IMAGE
        and ?b. y = f b /\ b IN R                        by homo_ring_property, IN_IMAGE
        and ?c. z = f c /\ c IN R                        by homo_ring_property, IN_IMAGE
        (homo_ring r f).prod.op x ((homo_ring r f).sum.op y z)
      = (homo_ring r f).prod.op x (f (b + c))            by GroupHomo_def, ring_carriers
      = f (a * (b + c))                                  by MonoidHomo_def, ring_carriers
      = f (a * b + a * c)                                by ring_mult_radd
      = (homo_ring r f).sum.op (a * b) (a * c)           by MonoidHomo_def, ring_carriers
      = (homo_ring r f).sum.op ((homo_ring r f).prod.op x y)
                               ((homo_ring r f).prod.op x z)  by GroupHomo_def, ring_carriers
*)
val homo_ring_ring = store_thm(
  "homo_ring_ring",
  ``!(r:'a ring) f. Ring r /\ RingHomo f r (homo_ring r f) ==> Ring (homo_ring r f)``,
  rw_tac std_ss[RingHomo_def] >>
  rw_tac std_ss[Ring_def] >| [
    fs[homo_ring_property] >>
    `AbelianGroup r.sum` by metis_tac[Ring_def] >>
    rw[homo_group_abelian_group],
    fs[homo_ring_property] >>
    `AbelianMonoid r.prod` by metis_tac[Ring_def] >>
    rw[homo_monoid_abelian_monoid],
    fs[homo_ring_property] >>
    rw[homo_monoid_property, ring_carriers],
    fs[homo_ring_property] >>
    rw[homo_monoid_property, ring_carriers],
    fs[homo_ring_property] >>
    `x' * (x'' + x''') = x' * x'' + x' * x'''` by rw[ring_mult_radd] >>
    `x'' + x''' IN R /\ x' * x'' IN R /\ x' * x''' IN R` by rw[] >>
    fs[GroupHomo_def, MonoidHomo_def] >>
    metis_tac[ring_carriers]
  ]);

(* Theorem: Homomorphic image of a Ring is a subring of the target ring. *)
(* Proof:
   This is to show each of these:
   (1) RingHomo f r s /\ x IN fR ==> x IN s.carrier
           x IN fR
       ==> x IN IMAGE f R       by homo_ring_property
       ==> ?z. x = f x, x IN R  by IN_IMAGE
       ==> f x IN s.carrier     by RingHomo_def
   (2) RingHomo f r s ==> GroupHomo I (homo_ring r f).sum s.sum
       RingHomo f r s ==> GroupHomo f r.sum s.sum  by RingHomo_def
       hence this is to show: GroupHomo f r.sum s.sum ==> GroupHomo I (homo_ring r f).sum s.sum
       Expand by definitions, need to show:
       (2.1) x IN IMAGE f r.sum.carrier /\ (!x. x IN r.sum.carrier ==> f x IN s.sum.carrier) ==> x IN s.sum.carrier
             True by IN_IMAGE.
       (2.2) x IN IMAGE f r.sum.carrier /\ y IN IMAGE f r.sum.carrier /\ ... ==>
             f (CHOICE (preimage f r.sum.carrier x) + CHOICE (preimage f r.sum.carrier y)) = s.sum.op x y
             True by preimage_choice_property.
   (3) RingHomo f r s ==> MonoidHomo I (homo_ring r f).prod s.prod
       RingHomo f r s ==> MonoidHomo f r.prod s.prod   by RingHomo_def
       hence this is to show: MonoidHomo f r.prod s.prod ==> MonoidHomo I (homo_ring r f).prod s.prod
       Expand by definitions, need to show:
       (3.1) x IN IMAGE f r.prod.carrier /\ (!x. x IN r.prod.carrier ==> f x IN s.prod.carrier) ==> x IN s.prod.carrier
             True by IN_IMAGE.
       (3.2) x IN IMAGE f r.prod.carrier /\ y IN IMAGE f r.prod.carrier /\ ... ==>
             f (CHOICE (preimage f r.prod.carrier x) * CHOICE (preimage f r.prod.carrier y)) = s.prod.op x y
             True by preimage_choice_property.
*)
val homo_ring_subring = store_thm(
  "homo_ring_subring",
  ``!(r:'a ring) (s:'b ring) f. Ring r /\ Ring s /\ RingHomo f r s ==> subring (homo_ring r f) s``,
  rpt strip_tac >>
  rw_tac std_ss[subring_def, RingHomo_def] >| [
    metis_tac[homo_ring_property, IN_IMAGE, RingHomo_def],
    `GroupHomo f r.sum s.sum` by metis_tac[RingHomo_def] >>
    pop_assum mp_tac >>
    rw_tac std_ss[GroupHomo_def, homo_ring_property, homo_monoid_property] >| [
      metis_tac[IN_IMAGE],
      metis_tac[preimage_choice_property]
    ],
    `MonoidHomo f r.prod s.prod` by metis_tac[RingHomo_def] >>
    pop_assum mp_tac >>
    rw_tac std_ss[MonoidHomo_def, homo_ring_property, homo_monoid_property] >| [
      metis_tac[IN_IMAGE],
      metis_tac[preimage_choice_property]
    ]
  ]);

(* Theorem: Ring r /\ INJ f R UNIV ==> RingHomo f r (homo_ring r f) *)
(* Proof:
   By RingHomo_def, homo_ring_property, this is to show:
   (1) x IN R ==> f x IN IMAGE f R, true                by IN_IMAGE
   (2) GroupHomo f r.sum (homo_group r.sum f), true     by homo_group_by_inj
   (3) MonoidHomo f r.prod (homo_group r.prod f), true  by homo_monoid_by_inj
*)
val homo_ring_by_inj = store_thm(
  "homo_ring_by_inj",
  ``!(r:'a ring) (f:'a -> 'b). Ring r /\ INJ f R UNIV ==> RingHomo f r (homo_ring r f)``,
  rw_tac std_ss[RingHomo_def, homo_ring_property] >-
  rw[] >-
  rw[homo_group_by_inj] >>
  rw[homo_monoid_by_inj]);

(* ------------------------------------------------------------------------- *)
(* Homomorphic Image between Rings.                                          *)
(* ------------------------------------------------------------------------- *)

(* Define homomorphism image of Ring *)
val ring_homo_image_def = Define`
  ring_homo_image f (r:'a ring) (r_:'b ring) =
     <| carrier := IMAGE f R;
            sum := homo_image f r.sum r_.sum;
           prod := homo_image f r.prod r_.prod
      |>
`;
(*
We have these (based on image_op):
- homo_ring_def;
> val it = |- !r f. homo_ring r f = <|carrier := IMAGE f R;
                                          sum := homo_group r.sum f;
                                         prod := homo_group r.prod f
                                     |> : thm
- homo_monoid_def;
> val it = |- !g f. homo_group g f = <|carrier := IMAGE f G;
                                            op := image_op g f;
                                            id := f #e
                                      |> : thm
We also have (based on real op):
- homo_image_def;
> val it = |- !f g h. homo_image f g h = <|carrier := IMAGE f G;
                                                op := h.op;
                                                id := h.id
                                          |> : thm
So ring_homo_image is based on homo_image.
*)

(* Theorem: (ring_homo_image f r r_).carrier = IMAGE f R *)
(* Proof: by ring_homo_image_def *)
val ring_homo_image_carrier = store_thm(
  "ring_homo_image_carrier",
  ``!(r:'a ring) (r_:'b ring) f. (ring_homo_image f r r_).carrier = IMAGE f R``,
  rw_tac std_ss[ring_homo_image_def]);

(* Theorem: (r ~r~ r_) f ==> Ring (ring_homo_image f r r_) *)
(* Proof:
   By ring_homo_image_def, Ring_def, this is to show:
   (1) AbelianGroup (homo_image f r.sum r_.sum)
       Ring r ==> Group r.sum /\ !x y. x IN R /\ y IN R ==> (x + y = y + x)         by ring_add_group
       Ring r_ ==> Group r_.sum /\ !x y. x IN R_ /\ y IN R_ ==> (x +_ y = y +_ x)   by ring_add_group
       Thus Group (homo_image f r.sum r_.sum)                                       by homo_image_group
       And  !x' x''. x' IN R /\ x'' IN R ==> f x' +_ f x'' = f x'' +_ f x'          by commutative properties
       Hence AbelianGroup (homo_image f r.sum r_.sum)                               by AbelianGroup_def
   (2) AbelianMonoid (homo_image f r.prod r_.prod)
       Ring r ==> Monoid r.prod /\ !x y. x IN R /\ y IN R ==> (x * y = y * x)       by ring_mult_monoid
       Ring s ==> Monoid r_.prod /\ !x y. x IN R_ /\ y IN R_ ==> (x *_ y = y *_ x)  by ring_mult_monoid
       Thus Monoid (homo_image f r.prod r_.prod)                                    by homo_image_monoid
       And  !x' x''. x' IN R /\ x'' IN R ==> f x' *_ f x'' = f x'' *_ f x'          by commutative properties
       Hence AbelianMonoid (homo_image f r.prod r_.prod)                            by AbelianMonoid_def
   (3) (homo_image f r.sum r_.sum).carrier = IMAGE f R
       True by ring_add_group, homo_image_def.
   (4) (homo_image f r.prod r_.prod).carrier = IMAGE f R
       True by ring_mult_monoid, homo_image_def
   (5) x IN IMAGE f R /\ y IN IMAGE f R /\ z IN IMAGE f R ==> x *_ (y +_ z) = x *_ y +_ x *_ z
       By IN_IMAGE, there are a IN R with f a = x, hence x = f a IN R_
                              b IN R with f b = y, hence y = f b IN R_
                          and c IN R with f c = z, hence z = f c IN R_
       Hence true by ring_mult_radd.
*)
val ring_homo_image_ring = store_thm(
  "ring_homo_image_ring",
  ``!(r:'a ring) (r_:'b ring). !f. (r ~r~ r_) f ==> Ring (ring_homo_image f r r_)``,
  rw_tac std_ss[RingHomo_def] >>
  `!x. x IN IMAGE f R ==> ?a. a IN R /\ (f a = x)` by metis_tac[IN_IMAGE] >>
  rw_tac std_ss[ring_homo_image_def, Ring_def] >| [
    `Group r.sum /\ !x y. x IN R /\ y IN R ==> (x + y = y + x)` by rw[ring_add_group] >>
    `Group r_.sum /\ !x y. x IN R_ /\ y IN R_ ==> (x +_ y = y +_ x)` by rw[ring_add_group] >>
    `Group (homo_image f r.sum r_.sum)` by rw[homo_image_group] >>
    rw[AbelianGroup_def, homo_image_def] >>
    metis_tac[],
    `Monoid r.prod /\ !x y. x IN R /\ y IN R ==> (x * y = y * x)` by rw[ring_mult_monoid] >>
    `Monoid r_.prod /\ !x y. x IN R_ /\ y IN R_ ==> (x *_ y = y *_ x)` by rw[ring_mult_monoid] >>
    `Monoid (homo_image f r.prod r_.prod)` by rw[homo_image_monoid] >>
    rw[AbelianMonoid_def, homo_image_def] >>
    metis_tac[],
    rw[homo_image_def],
    rw[homo_image_def],
    rw[homo_image_def] >>
    `x IN R_ /\ y IN R_ /\ z IN R_` by metis_tac[] >>
    rw[]
  ]);

(* Theorem: (r ~r~ r_) f ==> !s. Ring s /\ subring s r ==> subring (ring_homo_image f s r_) r_ *)
(* Proof:
   Note RingHomo I s r               by subring_def
   By RingHomo_def, this is to show:
   (1) x IN (ring_homo_image f s r_).carrier ==> x IN R_
           x IN (ring_homo_image f s r_).carrier
       ==> x IN IMAGE f B            by ring_homo_image_def
       ==> ?y. y IN B /\ (f y = x)   by IN_IMAGE
       ==> ?y. y IN R /\ (f y = x)   by RingHomo_def, RingHomo I s r
       ==> x IN IMAGE f R            by IN_IMAGE
       ==> x IN R_                   by notation
   (2) GroupHomo I (ring_homo_image f s r_).sum r_.sum
       By GroupHomo_def, ring_homo_image_def, homo_image_def, this is to show:
          y IN B ==> f y IN R_, true by RingHomo_def
   (3) MonoidHomo I (ring_homo_image f s r_).prod r_.prod
       By MonoidHomo_def, ring_homo_image_def, homo_image_def, this is to show:
          y IN B ==> f y IN R_, true by RingHomo_def
*)
val ring_homo_image_subring_subring = store_thm(
  "ring_homo_image_subring_subring",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
   !s. Ring s /\ subring s r ==> subring (ring_homo_image f s r_) r_``,
  rw[subring_def] >>
  rw_tac std_ss[RingHomo_def] >| [
    fs[ring_homo_image_def] >>
    metis_tac[RingHomo_def, combinTheory.I_THM],
    rw[GroupHomo_def, ring_homo_image_def, homo_image_def] >>
    metis_tac[RingHomo_def, combinTheory.I_THM],
    rw[MonoidHomo_def, ring_homo_image_def, homo_image_def] >>
    metis_tac[RingHomo_def, combinTheory.I_THM]
  ]);

(* Theorem: (r ~r~ r_) f ==> subring (ring_homo_image f r r_) r_ *)
(* Proof:
   Note subring r r                           by subring_refl
   Thus subring (ring_homo_image f r r_) r_   by ring_homo_image_subring_subring
*)
val ring_homo_image_is_subring = store_thm(
  "ring_homo_image_is_subring",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> subring (ring_homo_image f r r_) r_``,
  metis_tac[ring_homo_image_subring_subring, subring_refl]);

(* Theorem: (r ~r~ r_) f ==> (ring_homo_image f r r_) <= r_ *)
(* Proof: by ring_homo_image_ring, ring_homo_image_is_subring  *)
val ring_homo_image_subring = store_thm(
  "ring_homo_image_subring",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> (ring_homo_image f r r_) <= r_``,
  rw_tac std_ss[ring_homo_image_ring, ring_homo_image_is_subring]);

(* Theorem: (r ~r~ r_) f ==> RingHomo f r (ring_homo_image f r r_) *)
(* Proof:
   By RingHomo_def, this is to show:
   (1) x IN R ==> f x IN (ring_homo_image f r r_).carrier
       True by ring_homo_image_def.
   (2) GroupHomo f r.sum (ring_homo_image f r r_).sum
       Expanding by definitions, this is to show: f (x + y) = f x +_ f y
       True by ring_homo_property.
   (3) MonoidHomo f r.prod (ring_homo_image f r r_).prod
       Expanding by definitions, this is to show: f (x * y) = f x *_ f y
       True by ring_homo_property.
*)
val ring_homo_image_homo = store_thm(
  "ring_homo_image_homo",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> RingHomo f r (ring_homo_image f r r_)``,
  rpt strip_tac >>
  rw_tac std_ss[RingHomo_def] >-
  rw[ring_homo_image_def] >-
  rw[GroupHomo_def, ring_homo_image_def, homo_image_def, ring_homo_property] >>
  rw[MonoidHomo_def, ring_homo_image_def, homo_image_def, ring_homo_property]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> BIJ f R (ring_homo_image f r r_).carrier *)
(* Proof:
   Since (ring_homo_image f r r_).carrier = IMAGE f R     by ring_homo_image_def
   Hence true given INJ f R R_                            by INJ_IMAGE_BIJ
*)
val ring_homo_image_bij = store_thm(
  "ring_homo_image_bij",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==> BIJ f R (ring_homo_image f r r_).carrier``,
  rpt strip_tac >>
  `(ring_homo_image f r r_).carrier = IMAGE f R` by rw[ring_homo_image_def] >>
  metis_tac[INJ_IMAGE_BIJ]);

(* Theorem: (r ~r~ r_) f /\ INJ f R R_ ==> RingIso f r (ring_homo_image f r r_) *)
(* Proof:
   By RingIso_def, this is to show:
   (1) RingHomo f r r_ ==> RingHomo f r (ring_homo_image f r s), true by ring_homo_image_homo
   (2) RingHomo f r r_ /\ INJ f R R_ ==>
       BIJ f R (ring_homo_image f r r_).carrier, true by ring_homo_image_bij.
*)
val ring_homo_image_iso = store_thm(
  "ring_homo_image_iso",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ INJ f R R_ ==> RingIso f r (ring_homo_image f r r_)``,
  rw[RingIso_def, ring_homo_image_homo, ring_homo_image_bij]);

(* This turns RingHomo to RingIso, for the same function. *)

(* Theorem: Ring r /\ Ring r_ /\ SURJ f R R_ ==> RingIso I r_ (ring_homo_image f r r_) *)
(* Proof:
   By RingIso_def, this is to show:
   (1) RingHomo I r_ (ring_homo_image f r r_)
       After expanding by definitions and ring_carriers,
       the goal is: SURJ f R R_ /\ x IN R_ ==> x IN IMAGE f R
       This is true by SURJ_DEF, IN_IMAGE.
   (2) SURJ f R R_ ==> BIJ I R_ (ring_homo_image f r r_).carrier
       After expanding by definitions and ring_carriers, this is to show:
       (1) SURJ f R R_ ==> INJ I R_ (IMAGE f R)
           By INJ_DEF, this is true by SURJ_DEF, IN_IMAGE.
       (2) SURJ f R R_ ==> SURJ I R_ (IMAGE f R)
           By SURJ_DEF, this is true by SURJ_DEF, IN_IMAGE.
*)
val ring_homo_image_surj_property = store_thm(
  "ring_homo_image_surj_property",
  ``!(r:'a ring) (r_:'b ring) f. Ring r /\ Ring r_ /\ SURJ f R R_ ==> RingIso I r_ (ring_homo_image f r r_)``,
  rw_tac std_ss[RingIso_def] >| [
    rw_tac std_ss[RingHomo_def, GroupHomo_def, MonoidHomo_def, ring_homo_image_def, homo_image_def, ring_carriers] >>
    metis_tac[SURJ_DEF, IN_IMAGE],
    rw_tac std_ss[BIJ_DEF, ring_homo_image_def, homo_image_def, ring_carriers] >| [
      rw_tac std_ss[INJ_DEF] >>
      metis_tac[SURJ_DEF, IN_IMAGE],
      rewrite_tac[SURJ_DEF, combinTheory.I_THM] >>
      metis_tac[SURJ_DEF, IN_IMAGE]
    ]
  ]);

(* Theorem: (r ~r~ r_) f /\ s <= r ==> (s ~r~ (ring_homo_image f s r_)) f *)
(* Proof:
   Note RingHomo f s r_                              by subring_homo_homo
   This is to show:
   (1) Ring (ring_homo_image f s r_), true           by ring_homo_image_ring
   (2) RingHomo f s (ring_homo_image f s r_), true   by ring_homo_image_homo
*)
val ring_homo_subring_homo = store_thm(
  "ring_homo_subring_homo",
  ``!(r:'a ring) (s:'a ring) (r_:'b ring) f. (r ~r~ r_) f /\ s <= r ==> (s ~r~ (ring_homo_image f s r_)) f``,
  ntac 5 strip_tac >>
  `RingHomo f s r_` by metis_tac[subring_homo_homo] >>
  rw_tac std_ss[] >-
  rw[ring_homo_image_ring] >>
  rw[ring_homo_image_homo]);

(* Theorem: (r =r= r_) f /\ s <= r ==> (s =r= (ring_homo_image f s r_)) f *)
(* Proof:
   Note RingHomo f r r_ /\ INJ f R R_    by RingIso_def
    ==> RingHomo f s r_                  by subring_homo_homo
   This is to show:
   (1) Ring (ring_homo_image f s r_), true  by ring_homo_image_ring
   (2) RingIso f s (ring_homo_image f s r_)
       Note INJ f R R_                             by BIJ_DEF
        ==> INJ f B R_                             by INJ_SUBSET, subring_carrier_subset, SUBSET_REFL
       Thus RingIso f s (ring_homo_image f s r_)   by ring_homo_image_iso
*)
val ring_iso_subring_iso = store_thm(
  "ring_iso_subring_iso",
  ``!(r:'a ring) (s:'a ring) (r_:'b ring) f. (r =r= r_) f /\ s <= r ==> (s =r= (ring_homo_image f s r_)) f``,
  ntac 5 strip_tac >>
  `RingHomo f r r_ /\ BIJ f R R_` by metis_tac[RingIso_def] >>
  `RingHomo f s r_` by metis_tac[subring_homo_homo] >>
  rw_tac std_ss[] >-
  rw[ring_homo_image_ring] >>
  `INJ f B R_` by metis_tac[BIJ_DEF, INJ_SUBSET, subring_carrier_subset, SUBSET_REFL] >>
  rw[ring_homo_image_iso]);

(* Theorem alias *)
val ring_homo_ring_homo_subring = save_thm("ring_homo_ring_homo_subring", ring_homo_image_is_subring);
(*
val ring_homo_ring_homo_subring = |- !r r_ f. (r ~r~ r_) f ==> subring (ring_homo_image f r r_) r_: thm
*)

(* Theorem: (r =r= r_) f ==> subring (ring_homo_image f r r_) r_ *)
(* Proof:
   Note RingIso f r r_ ==> RingHomo f r r_   by RingIso_def
   Thus subring (ring_homo_image f r r_) r_  by ring_homo_ring_homo_subring
*)
val ring_iso_ring_homo_subring = store_thm(
  "ring_iso_ring_homo_subring",
  ``!(r:'a ring) (r_:'b ring) f. (r =r= r_) f ==> subring (ring_homo_image f r r_) r_``,
  rw_tac std_ss[ring_homo_ring_homo_subring, RingIso_def]);

(* Theorem: s <= r /\ (r =r= r_) f ==> (ring_homo_image f s r_) <= r_ *)
(* Proof:
   Note RingHomo f s r_                    by subring_ring_iso_compose
   Thus (s ~r~ r_) f                       by notation, Ring s
    ==> (ring_homo_image f s r_) <= r_     by ring_homo_image_subring
*)
val subring_ring_iso_ring_homo_subring = store_thm(
  "subring_ring_iso_ring_homo_subring",
  ``!(r:'a ring) (s:'a ring) (r_:'b ring) f. s <= r /\ (r =r= r_) f ==> (ring_homo_image f s r_) <= r_``,
  metis_tac[ring_homo_image_subring, subring_ring_iso_compose]);

(* ------------------------------------------------------------------------- *)
(* Injective Image of Ring.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Idea: Given a Ring r, and an injective function f,
   then the image (f R) is a Ring, with an induced binary operator:
        op := (\x y. f (f^-1 x * f^-1 y))  *)

(* Define a ring injective image for an injective f, with LINV f R. *)
Definition ring_inj_image_def:
   ring_inj_image (r:'a ring) (f:'a -> 'b) =
       <| carrier := IMAGE f R;
              sum := <| carrier := IMAGE f R; op := (\x y. f ((LINV f R x) + LINV f R y)); id := f #0 |>;
             prod := <| carrier := IMAGE f R; op := (\x y. f ((LINV f R x) * LINV f R y)); id := f #1 |>
        |>
End

(* Theorem: (ring_inj_image r f).carrier = IMAGE f R *)
(* Proof: by ring_inj_image_def *)
Theorem ring_inj_image_carrier:
  !(r:'a ring) f. (ring_inj_image r f).carrier = IMAGE f R
Proof
  simp[ring_inj_image_def]
QED

val ring_component_equality = DB.fetch "-" "ring_component_equality";

(* Alternative definitaion the image of ring injection, so that LINV f R makes sense. *)

(* Theorem: equivalent definition of ring_inj_image r f. *)
(* Proof:
   By ring_inj_image_def, monoid_inj_image_def, and component_equality of types,
   this is to show:
   (1) IMAGE f R = IMAGE f r.sum.carrier, true         by ring_carriers
   (2) (\x y. f (LINV f r.sum.carrier x + LINV f r.sum.carrier y)) =
       (\x y. f (LINV f R x + LINV f R y)), true       by ring_carriers
   (3) IMAGE f R = IMAGE f r.prod.carrier, true        by ring_carriers
   (4) (\x y. f (LINV f r.prod.carrier x * LINV f r.prod.carrier y)) =
       (\x y. f (LINV f R x * LINV f R y)), true       by ring_carriers
*)
Theorem ring_inj_image_alt:
  !(r:'a ring) (f:'a -> 'b).  Ring r ==>
     ring_inj_image r f = <| carrier := IMAGE f R;
                                 sum := monoid_inj_image r.sum f;
                                prod := monoid_inj_image r.prod f
                           |>
Proof
  simp[ring_inj_image_def, monoid_inj_image_def, ring_component_equality,
       monoid_component_equality]
QED

(* Theorem: Ring r /\ INJ f R univ(:'b) ==> Ring (ring_inj_image r f) *)
(* Proof:
   By Ring_def and ring_inj_image_alt, this is to show:
   (1) AbelianGroup (monoid_inj_image r.sum f)
           Ring r
       ==> AbelianGroup (r.sum)                        by ring_add_abelian_group
       ==> AbelianGroup (monoid_inj_image r.sum f)     by group_inj_image_abelian_group
   (2) AbelianMonoid (monoid_inj_image r.prod f)
           Ring r
       ==> AbelianMonoid (r.prod)                      by ring_mult_abelian_monoid
       ==> AbelianMonoid (monoid_inj_image r.prod f)   by monoid_inj_image_abelian_monoid
   (3) (monoid_inj_image r.sum f).carrier = IMAGE f R
         (monoid_inj_image r.sum f).carrier
       = IMAGE f r.sum.carrier                         by monoid_inj_image_def
       = IMAGE f R                                     by ring_carriers
   (4) (monoid_inj_image r.prod f).carrier = IMAGE f R
         (monoid_inj_image r.prod f).carrier
       = IMAGE f r.prod.carrier                        by monoid_inj_image_def
       = IMAGE f R                                     by ring_carriers
   (5) x IN IMAGE f R /\ y IN IMAGE f R /\ z IN IMAGE f R ==>
       f (t x * t (f (t y + t z))) = f (t (f (t x * t y)) + t (f (t x * t z)))
       by monoid_inj_image_def, ring_carriers, where t = LINV f R.
       Note INJ f R univ(:'b) ==> BIJ f R (IMAGE f R)  by INJ_IMAGE_BIJ_ALT
         so !x. x IN R ==> t (f x) = x
        and !x. x IN (IMAGE f R) ==> f (t x) = x       by BIJ_LINV_THM
       Note ?a. (x = f a) /\ a IN R                    by IN_IMAGE
            ?b. (y = f b) /\ b IN R                    by IN_IMAGE
            ?c. (z = f c) /\ c IN R                    by IN_IMAGE
       LHS = f (t x * t (f (t y + t z)))
           = f (t (f a) * t (f (t (f b) + t (f c))))   by x = f a, y = f b, z = f c
           = f (a * t (f (b + c)))                     by !y. t (f y) = y
           = f (a * (b + c))                           by !y. t (f y) = y, ring_add_element
       RHS = f (t (f (t x * t y)) + t (f (t x * t z)))
           = f (t (f (t (f a) * t (f b))) + t (f (t (f a) * t (f b))))   by x = f a, y = f b, z = f c
           = f (t (f (a * b)) + t (f (a * b)))         by !y. t (f y) = y
           = f (a * b + a * c)                         by !y. t (f y) = y, ring_mult_element
           = f (a * (b + c))                           by ring_mult_ladd
           = LHS
*)
Theorem ring_inj_image_ring:
  !(r:'a ring) (f:'a -> 'b).
    Ring r /\ INJ f R univ(:'b) ==> Ring (ring_inj_image r f)
Proof
  rpt strip_tac >>
  rw_tac std_ss[Ring_def, ring_inj_image_alt] >-
  rw[ring_add_abelian_group, group_inj_image_abelian_group] >-
  rw[ring_mult_abelian_monoid, monoid_inj_image_abelian_monoid] >-
  rw[monoid_inj_image_def] >-
  rw[monoid_inj_image_def] >>
  rw_tac std_ss[monoid_inj_image_def, ring_carriers] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  `BIJ f R (IMAGE f R)` by rw[INJ_IMAGE_BIJ_ALT] >>
  imp_res_tac BIJ_LINV_THM >>
  rpt strip_tac >>
  `?a. (x = f a) /\ a IN R` by rw[GSYM IN_IMAGE] >>
  `?b. (y = f b) /\ b IN R` by rw[GSYM IN_IMAGE] >>
  `?c. (z = f c) /\ c IN R` by rw[GSYM IN_IMAGE] >>
  rw[ring_mult_ladd, Abbr`t`]
QED

(* The following will be applied to finite fields, for existence and extension. *)

(* Theorem: Ring r /\ INJ f R univ(:'b) ==> Monoid (ring_inj_image r f).sum *)
(* Proof:
   Let s = IMAGE f R.
   Then BIJ f R s                              by INJ_IMAGE_BIJ_ALT
     so INJ f R s                              by BIJ_DEF
   Note !x. x IN R ==> f x IN s                by INJ_DEF
    and !x. x IN s ==> LINV f R x IN R         by BIJ_LINV_ELEMENT
   also !x. x IN R ==> (LINV f R (f x) = x)    by BIJ_LINV_THM
    and !x. x IN s ==> (f (LINV f R x) = x)    by BIJ_LINV_THM

   Let xx = LINV f R x, yy = LINV f R y, zz = LINV f R z.
   By Monoid_def, ring_inj_image_def, this is to show:
   (1) x IN s /\ y IN s ==> f (xx + yy) IN s, true by ring_add_element
   (2) x IN s /\ y IN s /\ z IN s ==> f (LINV f R (f (xx + yy)) + zz) = f (xx + LINV f R (f (yy + zz)))
       Since LINV f R (f (xx + yy)) = xx + yy  by ring_add_element
         and LINV f R (f (yy + zz)) = yy + zz  by ring_add_element
       The result follows                      by ring_add_assoc
   (3) f #0 IN s, true                         by ring_zero_element
   (4) x IN s ==> f (LINV f R (f #0) + xx) = x
       Since LINV f R (f #0) = #0              by ring_zero_element
       f (#0 + xx) = f xx = x                  by ring_add_lzero
   (5) x IN s ==> f (xx + LINV f R (f #0)) = x
       Since LINV f R (f #0) = #0              by ring_zero_element
       f (xx + #0) = f xx = x                  by ring_add_rzero
*)
Theorem ring_inj_image_sum_monoid:
  !(r:'a ring) f. Ring r /\ INJ f R univ(:'b) ==> Monoid (ring_inj_image r f).sum
Proof
  rpt strip_tac >>
  qabbrev_tac `s = IMAGE f R` >>
  `BIJ f R s` by rw[INJ_IMAGE_BIJ_ALT, Abbr`s`] >>
  `INJ f R s` by metis_tac[BIJ_DEF] >>
  `!x. x IN R ==> f x IN s` by metis_tac[INJ_DEF] >>
  `!x. x IN s ==> LINV f R x IN R` by metis_tac[BIJ_LINV_ELEMENT] >>
  `!x. x IN R ==> (LINV f R (f x) = x)` by metis_tac[BIJ_LINV_THM] >>
  `!x. x IN s ==> (f (LINV f R x) = x)` by metis_tac[BIJ_LINV_THM] >>
  rw_tac std_ss[Monoid_def, ring_inj_image_def] >-
  rw[] >-
 (qabbrev_tac `xx = LINV f R x` >>
  qabbrev_tac `yy = LINV f R y` >>
  qabbrev_tac `zz = LINV f R z` >>
  `LINV f R (f (xx + yy)) = xx + yy` by metis_tac[ring_add_element] >>
  `LINV f R (f (yy + zz)) = yy + zz` by metis_tac[ring_add_element] >>
  rw[ring_add_assoc, Abbr`xx`, Abbr`yy`, Abbr`zz`]) >-
  rw[] >-
  rw[] >>
  rw[]
QED

(* Theorem: Ring r /\ INJ f R univ(:'b) ==> Group (ring_inj_image r f).sum *)
(* Proof:
   By Group_def, this is to show:
   (1) Monoid (ring_inj_image r f).sum, true     by ring_inj_image_sum_monoid
   (2) monoid_invertibles (ring_inj_image r f).sum = (ring_inj_image r f).sum.carrier
      Let xx = LINV f R x.
       By ring_inj_image_def, monoid_invertibles_def, this is to show:
       x IN IMAGE f R ==> ?y. y IN IMAGE f R /\ (f (xx + LINV f R y) = f #0) /\ (f (LINV f R y + xx) = f #0)
       Let s = IMAGE f R.
       Then BIJ f R s                            by INJ_IMAGE_BIJ_ALT
         so INJ f R s                            by BIJ_DEF
       Note !x. x IN R ==> f x IN s              by INJ_DEF
        and !x. x IN s ==> LINV f R x IN R       by BIJ_LINV_ELEMENT
       also !x. x IN R ==> (LINV f R (f x) = x)  by BIJ_LINV_THM
        and !x. x IN s ==> (f (LINV f R x) = x)  by BIJ_LINV_THM
      Since -xx IN R                             by ring_neg_element
       Take y = f (-xx).
       Then y = f (-xx) IN s                     by above
        and LINV f R y = LINV f R (-xx) = -xx    by above
       Also f (xx + -xx) = f #0                  by ring_add_rneg
        and f (-xx + xx) = f #0                  by ring_add_lneg
*)
Theorem ring_inj_image_sum_group:
  !(r:'a ring) f. Ring r /\ INJ f R univ(:'b) ==> Group (ring_inj_image r f).sum
Proof
  rw[Group_def] >-
  rw[ring_inj_image_sum_monoid] >>
  rw_tac std_ss[ring_inj_image_def, monoid_invertibles_def, GSPECIFICATION, EXTENSION, EQ_IMP_THM] >>
  qabbrev_tac `s = IMAGE f R` >>
  `BIJ f R s` by rw[INJ_IMAGE_BIJ_ALT, Abbr`s`] >>
  `INJ f R s` by metis_tac[BIJ_DEF] >>
  `!x. x IN R ==> f x IN s` by metis_tac[INJ_DEF] >>
  `!x. x IN s ==> LINV f R x IN R` by metis_tac[BIJ_LINV_ELEMENT] >>
  `!x. x IN R ==> (LINV f R (f x) = x)` by metis_tac[BIJ_LINV_THM] >>
  `!x. x IN s ==> (f (LINV f R x) = x)` by metis_tac[BIJ_LINV_THM] >>
  qabbrev_tac `xx = LINV f R x` >>
  `-xx IN R` by rw[Abbr`xx`] >>
  metis_tac[ring_add_lneg, ring_add_rneg, ring_zero_element]
QED

(* Theorem: Ring r /\ INJ f R univ(:'b) ==> AbelianGroup (ring_inj_image r f).sum *)
(* Proof:
   By AbelianGroup_def, this is to show:
   (1) Group (ring_inj_image r f).sum, true      by ring_inj_image_sum_group
   (2) x' IN R /\ x'' IN R ==>
       f (LINV f R (f x') + LINV f R (f x'')) = f (LINV f R (f x'') + LINV f R (f x'))
       Let s = IMAGE f R.
       Then BIJ f R s                            by INJ_IMAGE_BIJ_ALT
         so INJ f R s                            by BIJ_DEF
       Note !x. x IN R ==> f x IN s              by INJ_DEF
        and !x. x IN s ==> LINV f R x IN R       by BIJ_LINV_ELEMENT
       also !x. x IN R ==> (LINV f R (f x) = x)  by BIJ_LINV_THM
        and !x. x IN s ==> (f (LINV f R x) = x)  by BIJ_LINV_THM
       The result follows                        by ring_add_comm
*)
Theorem ring_inj_image_sum_abelian_group:
  !(r:'a ring) f. Ring r /\ INJ f R univ(:'b) ==> AbelianGroup (ring_inj_image r f).sum
Proof
  rw[AbelianGroup_def] >-
  rw[ring_inj_image_sum_group] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw[ring_inj_image_def] >>
  qabbrev_tac `s = IMAGE f R` >>
  `BIJ f R s` by rw[INJ_IMAGE_BIJ_ALT, Abbr`s`] >>
  `INJ f R s` by metis_tac[BIJ_DEF] >>
  `!x. x IN R ==> f x IN s` by metis_tac[INJ_DEF] >>
  `!x. x IN s ==> LINV f R x IN R` by metis_tac[BIJ_LINV_ELEMENT] >>
  `!x. x IN R ==> (LINV f R (f x) = x)` by metis_tac[BIJ_LINV_THM] >>
  `!x. x IN s ==> (f (LINV f R x) = x)` by metis_tac[BIJ_LINV_THM] >>
  rw[ring_add_comm]
QED

(* Theorem: Ring r /\ INJ f R univ(:'b) ==> Monoid (ring_inj_image r f).prod *)
(* Proof:
   Let s = IMAGE f R.
   Then BIJ f R s                              by INJ_IMAGE_BIJ_ALT
     so INJ f R s                              by BIJ_DEF
   Note !x. x IN R ==> f x IN s                by INJ_DEF
    and !x. x IN s ==> LINV f R x IN R         by BIJ_LINV_ELEMENT
   also !x. x IN R ==> (LINV f R (f x) = x)    by BIJ_LINV_THM
    and !x. x IN s ==> (f (LINV f R x) = x)    by BIJ_LINV_THM

   Let xx = LINV f R x, yy = LINV f R y, zz = LINV f R z.
   By Monoid_def, ring_inj_image_def, this is to show:
   (1) x IN s /\ y IN s ==> f (xx * yy) IN s, true by ring_mult_element
   (2) x IN s /\ y IN s /\ z IN s ==> f (LINV f R (f (xx * yy)) * zz) = f (xx * LINV f R (f (yy * zz)))
       Since LINV f R (f (xx * yy)) = xx * yy  by ring_mult_element
         and LINV f R (f (yy * zz)) = yy * zz  by ring_mult_element
       The result follows                      by ring_mult_assoc
   (3) f #1 IN s, true                         by ring_one_element
   (4) x IN s ==> f (LINV f R (f #1) * xx) = x
       Since LINV f R (f #1) = #1              by ring_one_element
       f (#1 * xx) = f xx = x                  by ring_mult_lone
   (5) x IN s ==> f (xx * LINV f R (f #1)) = x
       Since LINV f R (f #1) = #1              by ring_one_element
       f (xx * #1) = f xx = x                  by ring_mult_rone
*)
Theorem ring_inj_image_prod_monoid:
  !(r:'a ring) f. Ring r /\ INJ f R univ(:'b) ==> Monoid (ring_inj_image r f).prod
Proof
  rpt strip_tac >>
  qabbrev_tac `s = IMAGE f R` >>
  `BIJ f R s` by rw[INJ_IMAGE_BIJ_ALT, Abbr`s`] >>
  `INJ f R s` by metis_tac[BIJ_DEF] >>
  `!x. x IN R ==> f x IN s` by metis_tac[INJ_DEF] >>
  `!x. x IN s ==> LINV f R x IN R` by metis_tac[BIJ_LINV_ELEMENT] >>
  `!x. x IN R ==> (LINV f R (f x) = x)` by metis_tac[BIJ_LINV_THM] >>
  `!x. x IN s ==> (f (LINV f R x) = x)` by metis_tac[BIJ_LINV_THM] >>
  rw_tac std_ss[Monoid_def, ring_inj_image_def] >-
  rw[] >-
 (qabbrev_tac `xx = LINV f R x` >>
  qabbrev_tac `yy = LINV f R y` >>
  qabbrev_tac `zz = LINV f R z` >>
  `LINV f R (f (xx * yy)) = xx * yy` by metis_tac[ring_mult_element] >>
  `LINV f R (f (yy * zz)) = yy * zz` by metis_tac[ring_mult_element] >>
  rw[ring_mult_assoc, Abbr`xx`, Abbr`yy`, Abbr`zz`]) >-
  rw[] >-
  rw[] >>
  rw[]
QED

(* Theorem: Ring r /\ INJ f R univ(:'b) ==> AbelianMonoid (ring_inj_image r f).prod *)
(* Proof:
   By AbelianMonoid_def, this is to show:
   (1) Monoid (ring_inj_image r f).prod, true    by ring_inj_image_prod_monoid
   (2) x' IN R /\ x'' IN R ==>
       f (LINV f R (f x') * LINV f R (f x'')) = f (LINV f R (f x'') * LINV f R (f x'))
       Let s = IMAGE f R.
       Then BIJ f R s                            by INJ_IMAGE_BIJ_ALT
         so INJ f R s                            by BIJ_DEF
       Note !x. x IN R ==> f x IN s              by INJ_DEF
        and !x. x IN s ==> LINV f R x IN R       by BIJ_LINV_ELEMENT
       also !x. x IN R ==> (LINV f R (f x) = x)  by BIJ_LINV_THM
        and !x. x IN s ==> (f (LINV f R x) = x)  by BIJ_LINV_THM
       The result follows                        by ring_mult_comm
*)
Theorem ring_inj_image_prod_abelian_monoid:
  !(r:'a ring) f. Ring r /\ INJ f R univ(:'b) ==> AbelianMonoid (ring_inj_image r f).prod
Proof
  rw[AbelianMonoid_def] >-
  rw[ring_inj_image_prod_monoid] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw[ring_inj_image_def] >>
  qabbrev_tac `s = IMAGE f R` >>
  `BIJ f R s` by rw[INJ_IMAGE_BIJ_ALT, Abbr`s`] >>
  `INJ f R s` by metis_tac[BIJ_DEF] >>
  `!x. x IN R ==> f x IN s` by metis_tac[INJ_DEF] >>
  `!x. x IN s ==> LINV f R x IN R` by metis_tac[BIJ_LINV_ELEMENT] >>
  `!x. x IN R ==> (LINV f R (f x) = x)` by metis_tac[BIJ_LINV_THM] >>
  `!x. x IN s ==> (f (LINV f R x) = x)` by metis_tac[BIJ_LINV_THM] >>
  rw[ring_mult_comm]
QED

(* Theorem: Ring r /\ INJ f R univ(:'b) ==> GroupHomo f r.sum (ring_inj_image r f).sum *)
(* Proof:
   Note R = r.prod.carrier                     by ring_carriers
   Let s = IMAGE f R.
   Then BIJ f R s                              by INJ_IMAGE_BIJ_ALT
     so INJ f R s                              by BIJ_DEF

   By GroupHomo_def, ring_inj_image_def, this is to show:
   (1) x IN R ==> f x IN IMAGE f R, true       by IN_IMAGE
   (2) x IN R /\ y IN R ==> f (x + y) = f (LINV f R (f x) + LINV f R (f y))
       Since LINV f R (f x) = x                by BIJ_LINV_THM
         and LINV f R (f y) = y                by BIJ_LINV_THM
       The result is true.
*)
Theorem ring_inj_image_sum_group_homo:
  !(r:'a ring) f. Ring r /\ INJ f R univ(:'b) ==> GroupHomo f r.sum (ring_inj_image r f).sum
Proof
  rw[GroupHomo_def, ring_inj_image_def] >>
  qabbrev_tac `s = IMAGE f R` >>
  `BIJ f R s` by rw[INJ_IMAGE_BIJ_ALT, Abbr`s`] >>
  `INJ f R s` by metis_tac[BIJ_DEF] >>
  metis_tac[BIJ_LINV_THM]
QED

(* Theorem: Ring r /\ INJ f R univ(:'b) ==> MonoidHomo f r.prod (ring_inj_image r f).prod *)
(* Proof:
   Note R = r.prod.carrier                     by ring_carriers
   Let s = IMAGE f R.
   Then BIJ f R s                              by INJ_IMAGE_BIJ_ALT
     so INJ f R s                              by BIJ_DEF

   By MonoidHomo_def, ring_inj_image_def, this is to show:
   (1) x IN R ==> f x IN IMAGE f R, true       by IN_IMAGE
   (2) x IN R /\ y IN R ==> f (x * y) = f (LINV f R (f x) * LINV f R (f y))
       Since LINV f R (f x) = x                by BIJ_LINV_THM
         and LINV f R (f y) = y                by BIJ_LINV_THM
       The result is true.
*)
Theorem ring_inj_image_prod_monoid_homo:
  !(r:'a ring) f. Ring r /\ INJ f R univ(:'b) ==> MonoidHomo f r.prod (ring_inj_image r f).prod
Proof
  rw[MonoidHomo_def, ring_inj_image_def] >>
  qabbrev_tac `s = IMAGE f R` >>
  `BIJ f R s` by rw[INJ_IMAGE_BIJ_ALT, Abbr`s`] >>
  `INJ f R s` by metis_tac[BIJ_DEF] >>
  metis_tac[BIJ_LINV_THM]
QED

(* Theorem: Ring r /\ INJ f R univ(:'b) ==> RingHomo f r (ring_inj_image r f) *)
(* Proof:
   By RingHomo_def, this is to show:
   (1) x IN R ==> f x IN (ring_inj_image r f).carrier
       Note (ring_inj_image r f).carrier = IMAGE f R       by ring_inj_image_carrier
       Thus f x IN IMAGE f R                               by INJ_DEF, IN_IMAGE
   (2) GroupHomo f r.sum (ring_inj_image r f).sum, true    by ring_inj_image_sum_group_homo
   (3) MonoidHomo f r.prod (ring_inj_image r f).prod, true by ring_inj_image_prod_monoid_homo
*)
Theorem ring_inj_image_ring_homo:
  !(r:'a ring) f. Ring r /\ INJ f R univ(:'b) ==> RingHomo f r (ring_inj_image r f)
Proof
  rw_tac std_ss[RingHomo_def] >-
  rw[ring_inj_image_carrier, INJ_DEF] >-
  rw[ring_inj_image_sum_group_homo] >>
  rw[ring_inj_image_prod_monoid_homo]
QED

(* ------------------------------------------------------------------------- *)
(* Ideals in Ring Documentation                                              *)
(* ------------------------------------------------------------------------- *)
(* Overloads:
   I       = i.carrier
   J       = j.carrier
   i << r  = ideal i r
   x o I   = coset r.sum x i.carrier
   x * R   = coset r.prod x r.carrier
   x === y = ideal_congruence r i x y
   <p>     = principal_ideal r p
   <q>     = principal_ideal r q
   <#0>    = principal_ideal r #0
   i + j   = ideal_sum r i j
   maxi    = ideal_maximal r
   atom    = irreducible r
*)
(* Definitions and Theorems (# are exported):

   Ring Ideals:
   ideal_def    |- !i r. i << r <=>
                    i.sum <= r.sum /\ (i.sum.carrier = I) /\
                    (i.prod.carrier = I) /\ (i.prod.op = $* ) /\ (i.prod.id = #1) /\
                    !x y. x IN I /\ y IN R ==> x * y IN I /\ y * x IN I
   ideal_has_subgroup      |- !r i. i << r ==> i.sum <= r.sum
   ideal_carriers          |- !r i. i << r ==> (i.sum.carrier = I) /\ (i.prod.carrier = I)
   ideal_product_property  |- !r i. i << r ==> !x y. x IN I /\ y IN R ==> x * y IN I /\ y * x IN I
   ideal_element           |- !r i. i << r ==> !x. x IN I ==> x IN r.sum.carrier
   ideal_ops               |- !r i. i << r ==> (i.sum.op = $+) /\ (i.prod.op = $* )

   Ideal Theorems:
   ideal_element_property  |- !r i. Ring r /\ i << r ==> !x. x IN I ==> x IN R
   ideal_property          |- !r i. Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> x + y IN I /\ x * y IN I
   ideal_has_zero          |- !r i. Ring r /\ i << r ==> #0 IN I
   ideal_has_neg           |- !r i. Ring r /\ i << r ==> !x. x IN I ==> -x IN I
   ideal_has_sum           |- !r i. Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> x + y IN I
   ideal_has_diff          |- !r i. Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> x - y IN I
   ideal_has_product       |- !r i. Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> x * y IN I
   ideal_has_multiple      |- !r i. i << r ==> !x y. x IN I /\ y IN R ==> x * y IN I
   ideal_zero              |- !r i. Ring r /\ i << r ==> (i.sum.id = #0)
   ideal_eq_ideal          |- !r i j. Ring r /\ i << r /\ j << r ==> ((i = j) <=> (I = J))
   ideal_sub_ideal         |- !r i j. Ring r /\ i << r /\ j << r ==> (i << j <=> I SUBSET J)
   ideal_sub_itself        |- !r i. Ring r /\ i << r ==> i << i
   ideal_refl              |- !r. Ring r ==> r << r
   ideal_antisym           |- !r i. i << r /\ r << i ==> (i = r)
   ideal_has_one           |- !r i. Ring r /\ i << r /\ #1 IN I ==> (I = R)
   ideal_with_one          |- !r. Ring r ==> !i. i << r /\ #1 IN I <=> (i = r)
   ideal_with_unit         |- !r i. Ring r /\ i << r ==> !x. x IN I /\ unit x ==> (i = r)

   Ideal Cosets:
   ideal_coset_of_element  |- !r i. Ring r /\ i << r ==> !x. x IN I ==> (x o I = I)
   ideal_coset_eq_carrier  |- !r i. Ring r /\ i << r ==> !x. x IN R /\ (x o I = I) <=> x IN I
   ideal_coset_eq          |- !r i. Ring r /\ i << r ==> !x y. x IN R /\ y IN R ==> ((x o I = y o I) <=> x - y IN I)

   Ideal induces congruence in Ring:
#  ideal_congruence_def    |- !r i x y. x === y <=> x - y IN I
   ideal_congruence_refl   |- !r i. Ring r /\ i << r ==> !x. x IN R ==> x === x
   ideal_congruence_sym    |- !r i. Ring r /\ i << r ==> !x y. x IN R /\ y IN R ==> (x === y <=> y === x)
   ideal_congruence_trans  |- !r i. Ring r /\ i << r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> x === y /\ y === z ==> x === z
   ideal_congruence_equiv  |- !r i. Ring r /\ i << r ==> $=== equiv_on R
   ideal_congruence_iff_inCoset  |- !r i. Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> (x === y <=> inCoset r.sum i.sum x y)
   ideal_coset_eq_congruence     |- !r i. Ring r /\ i << r ==> !x y. x IN R /\ y IN R ==> ((x o I = y o I) <=> x === y)
   ideal_congruence_mult         |- !r i. Ring r /\ i << r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> x === y ==> z * x === z * y
   ideal_congruence_elements     |- !r i. Ring r /\ i << r ==> !x y. x IN I /\ y IN R ==> (y IN I <=> x === y)

   Principal Ideal:
   principal_ideal_def      |- !r p.  <p> =  <|carrier := p * R;
                                                   sum := <|carrier := p * R; op := $+; id := #0|>;
                                                  prod := <|carrier := p * R; op := $*; id := #1|>
                                              |>
   principal_ideal_property |- !r p. (<p>.carrier = p * R) /\ (<p>.sum.carrier = p * R) /\
                                     (<p>.prod.carrier = p * R) /\ (<p>.sum.op = $+) /\
                                     (<p>.prod.op = $* ) /\ (<p>.sum.id = #0) /\ (<p>.prod.id = #1)
   principal_ideal_element              |- !p x. x IN <p>.carrier <=> ?z. z IN R /\ (x = p * z)
   principal_ideal_has_element          |- !r. Ring r ==> !p. p IN R ==> p IN <p>.carrier
   principal_ideal_group                |- !r. Ring r ==> !p. p IN R ==> Group <p>.sum
   principal_ideal_subgroup             |- !r. Ring r ==> !p. p IN R ==> <p>.sum <= r.sum
   principal_ideal_subgroup_normal      |- !r. Ring r ==> !p. p IN R ==> <p>.sum << r.sum
   principal_ideal_ideal                |- !r. Ring r ==> !p. p IN R ==> <p> << r
   principal_ideal_has_principal_ideal  |- !r. Ring r ==> !p q. p IN R /\ q IN <p>.carrier ==> <q> << <p>
   principal_ideal_eq_principal_ideal   |- !r. Ring r ==> !p q u. p IN R /\ q IN R /\ unit u /\ (p = q * u) ==> (<p> = <q>)
   ideal_has_principal_ideal            |- !r i. Ring r /\ i << r ==> !p. p IN R ==> (p IN I <=> <p> << i)

   Trivial Ideal:
   zero_ideal_sing          |- !r. Ring r ==> (<#0>.carrier = {#0})
   zero_ideal_ideal         |- !r. Ring r ==> <#0> << r
   ideal_carrier_sing       |- !r i. Ring r /\ i << r ==> (SING I <=> (i = <#0>))

   Sum of Ideals:
   ideal_sum_def            |- !r i j. i + j =
                                <|carrier := {x + y | x IN I /\ y IN J};
                                      sum := <|carrier := {x + y | x IN I /\ y IN J}; op := $+; id := #0|>;
                                     prod := <|carrier := {x + y | x IN I /\ y IN J}; op := $*; id := #1|>
                                 |>
   ideal_sum_element         |- !i j x. x IN (i + j).carrier <=> ?y z. y IN I /\ z IN J /\ (x = y + z)
   ideal_sum_comm            |- !r i j. Ring r /\ i << r /\ j << r ==> (i + j = j + i)
   ideal_sum_group           |- !r i j. Ring r /\ i << r /\ j << r ==> Group (i + j).sum
   ideal_subgroup_ideal_sum  |- !r i j. Ring r /\ i << r /\ j << r ==> i.sum <= (i + j).sum
   ideal_sum_subgroup        |- !r i j. Ring r /\ i << r /\ j << r ==> (i + j).sum <= r.sum
   ideal_sum_has_ideal       |- !r i j. Ring r /\ i << r /\ j << r ==> i << (i + j)
   ideal_sum_has_ideal_comm  |- !r i j. Ring r /\ i << r /\ j << r ==> j << (i + j)
   ideal_sum_ideal           |- !r i j. Ring r /\ i << r /\ j << r ==> (i + j) << r
   ideal_sum_sub_ideal       |- !r i j. Ring r /\ i << r /\ j << r ==> ((i + j) << j <=> i << j)

   principal_ideal_sum_eq_ideal     |- !r i. Ring r /\ i << r ==> !p. p IN I ==> (<p> + i = i)
   principal_ideal_sum_equal_ideal  |- !r i. Ring r /\ i << r ==> !p. p IN I <=> p IN R /\ (<p> + i = i)

   Maximal Ideals:
   ideal_maximal_def     |- !r i. maxi i <=> i << r /\ !j. i << j /\ j << r ==> (i = j) \/ (j = r)

   Irreducibles:
   irreducible_def       |- !r z. atom z <=> z IN R+ /\ z NOTIN R* /\ !x y. x IN R /\ y IN R /\ (z = x * y) ==> unit x \/ unit y
   irreducible_element   |- !r p. atom p ==> p IN R

   Principal Ideal Ring:
   PrincipalIdealRing_def             |- !r. PrincipalIdealRing r <=> Ring r /\ !i. i << r ==> ?p. p IN R /\ (<p> = i)
   principal_ideal_ring_ideal_maximal |- !r. PrincipalIdealRing r ==> !p. atom p ==> maxi <p>

   Euclidean Ring:
   EuclideanRing_def     |- !r f. EuclideanRing r f <=> Ring r /\ (!x. (f x = 0) <=> (x = #0)) /\
                            !x y. x IN R /\ y IN R /\ y <> #0 ==> ?q t. q IN R /\ t IN R /\ (x = q * y + t) /\ f t < f y
   euclid_ring_ring      |- !r f. EuclideanRing r f ==> Ring r
   euclid_ring_map       |- !r f. EuclideanRing r f ==> !x. (f x = 0) <=> (x = #0)
   euclid_ring_property  |- !r f. EuclideanRing r f ==> !x y. x IN R /\ y IN R /\ y <> #0 ==>
                                                     ?q t. q IN R /\ t IN R /\ (x = y * q + t) /\ f t < f y
   ideal_gen_exists      |- !r i. Ring r /\ i << r /\ i <> <#0> ==> !f. (!x. (f x = 0) <=> (x = #0)) ==>
                            ?p. p IN I /\ p <> #0 /\ !z. z IN I /\ z <> #0 ==> f p <= f z
   ideal_gen_def         |- !r i f. Ring r /\ i << r /\ i <> <#0> /\ (!x. (f x = 0) <=> (x = #0)) ==>
                            ideal_gen r i f IN I /\ ideal_gen r i f <> #0 /\
                            !z. z IN I /\ z <> #0 ==> f (ideal_gen r i f) <= f z
   ideal_gen_minimal     |- !r i. Ring r /\ i << r /\ i <> <#0> ==> !f. (!x. (f x = 0) <=> (x = #0)) ==>
                            !z. z IN I ==> (f z < f (ideal_gen r i f) <=> (z = #0))
   euclid_ring_principal_ideal_ring   |- !r f. EuclideanRing r f ==> PrincipalIdealRing r

   Ideal under Ring Homomorphism:
   homo_ideal_def           |- !f r i. homo_ideal f r s i =
                               <|carrier := IMAGE f I;
                                    sum := <|carrier := IMAGE f I; op := s.sum.op; id := f #0|>;
                                   prod := <|carrier := IMAGE f I; op := s.prod.op; id := f #1|>
                                |>
   ring_homo_ideal_group    |- !r s f. Ring r /\ Ring s /\ RingHomo f r s ==> !i. i << r ==> Group (homo_ideal f r s i).sum
   ring_homo_ideal_subgroup |- !r s f. Ring r /\ Ring s /\ RingHomo f r s ==> !i. i << r ==> (homo_ideal f r s i).sum <= s.sum
   ring_homo_ideal_ideal    |- !r s f. Ring r /\ Ring s /\ RingHomo f r s /\ SURJ f R s.carrier ==>
                               !i. i << r ==> homo_ideal f r s i << s
*)

(* ------------------------------------------------------------------------- *)
(* Ring Ideals                                                               *)
(* ------------------------------------------------------------------------- *)

(* The carrier of Ideal = carrier of group i.sum *)
val _ = temp_overload_on ("I", ``i.carrier``);
(* The carrier of Ideal = carrier of group j.sum *)
val _ = temp_overload_on ("J", ``j.carrier``);

(* An Ideal i (structurally a ring: carrier, sum, prod) of a ring r satisfies 2 conditions:
   (1) sum part is subgroup: i.sum is a subgroup of r.sum
   (2) prod part is absorption: !x IN I, y IN R, x * y IN I
   (3) !x IN I, y IN R, y * x IN I
*)
val ideal_def = Define `
  ideal (i:'a ring) (r:'a ring) <=>
    i.sum <= r.sum /\
    (i.sum.carrier = I) /\
    (i.prod.carrier = I) /\
    (i.prod.op = r.prod.op) /\
    (i.prod.id = #1) /\
    (!x y. x IN I /\ y IN R ==> x * y IN I /\ y * x IN I)
`;
(*
- ideal_def;
> val ideal_def = |- !i r. ideal i r <=>
         i.sum <= r.sum /\ (i.sum.carrier = I) /\
         (i.prod.carrier = I) /\ (i.prod.op = $* ) /\ (i.prod.id = #1) /\
         !x y. x IN I /\ y IN R ==> x * y IN I /\ y * x IN I : thm
*)
(* set overloading *)
val _ = overload_on ("<<", ``ideal``);
val _ = set_fixity "<<" (Infixl 650); (* higher than * or / *)

(* Theorem: Ideal add_group is a subgroup. *)
val ideal_has_subgroup = save_thm("ideal_has_subgroup",
    ideal_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val ideal_has_subgroup = |- !r i. i << r ==> i.sum <= r.sum : thm *)

(* Theorem: Ideal carriers are I. *)
val ideal_carriers = save_thm("ideal_carriers",
    CONJ (ideal_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH_ALL |> CONJUNCT2 |> CONJUNCT1)
         (ideal_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH_ALL |> CONJUNCT2 |> CONJUNCT2 |> CONJUNCT1)
         |> DISCH_ALL |> GEN_ALL);
(* > val ideal_carriers = |- !r i. i << r ==> (i.sum.carrier = I) /\ (i.prod.carrier = I) : thm *)

(* Theorem: Ideal is multiplicative closed with all elements. *)
val ideal_product_property = save_thm("ideal_product_property",
    ideal_def |> SPEC_ALL |> #1 o EQ_IMP_RULE |> UNDISCH_ALL |> CONJUNCTS |> last |> DISCH_ALL |> GEN_ALL);
(* > val ideal_product_property = |- !r i. i << r ==> !x y. x IN I /\ y IN R ==> x * y IN I /\ y * x IN I : thm *)

(* Theorem: i << r ==> !x. x IN I ==> x IN r.sum.carrier *)
(* Proof:
   i.sum <= r.sum /\ i.sum.carrier = I    by ideal_def
   x IN i.sum.carrier ==> x IN r.sum.carrier  by subgroup_element
   hence true.
*)
val ideal_element = store_thm(
  "ideal_element",
  ``!r i:'a ring. i << r ==> !x. x IN I ==> x IN r.sum.carrier``,
  metis_tac[ideal_def, subgroup_element]);

(* Theorem: i << r ==> (i.sum.op = r.sum.op) /\ (i.prod.op = r.prod.op *)
(* Proof:
   i << r ==> i.sum <= r.sum          by ideal_def
          ==> i.sum.op = r.sum.op     by Subgroup_def
   i << r ==> i.prod.op = r.prod.op   by ideal_def
*)
val ideal_ops = store_thm(
  "ideal_ops",
  ``!r i:'a ring. i << r ==> (i.sum.op = r.sum.op) /\ (i.prod.op = r.prod.op)``,
  rw[ideal_def, Subgroup_def]);

(* ------------------------------------------------------------------------- *)
(* Ideal Theorems                                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r /\ i << r ==> !x. x IN I ==> x IN R *)
(* Proof:
   x IN I ==> x IN r.sum.carrier    by ideal_element
   r.sum.carrier = R                by ring_add_group
   hence true.
*)
val ideal_element_property = store_thm(
  "ideal_element_property",
  ``!r i:'a ring. Ring r /\ i << r ==> !x. x IN I ==> x IN R ``,
  metis_tac[ideal_element, ring_add_group]);

(* Theorem: Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> x + y IN I /\ x * y IN I *)
(* Proof:
   For the first one, x + y IN I
     It is because i.sum <= r.sum /\ (i.sum.carrier = I)  by ideal_def
     Hence Group i.sum /\ (i.sum.op x y = x + y)          by subgroup_property
     Since x, y IN I, x, y IN R                           by ideal_element_property
     Hence true by group_op_element.
   For the second one, x * y IN I
     It is because y IN I ==> y IN R by ideal_element_property
     Hence true by ideal_product_property.
*)
val ideal_property = store_thm(
  "ideal_property",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> x + y IN I /\ x * y IN I``,
  rpt strip_tac >| [
    `i.sum <= r.sum /\ (i.sum.carrier = I)` by metis_tac[ideal_def] >>
    `Group i.sum /\ (i.sum.op x y = x + y)` by metis_tac[subgroup_property] >>
    metis_tac[group_op_element, ideal_element_property],
    metis_tac[ideal_product_property, ideal_element_property]
  ]);

(* Theorem: i << r ==> #0 IN I *)
(* Proof:
   i.sum <= r.sum /\ (i.sum.carrier = I)   by ideal_def
   i.sum.id = #0                           by subgroup_id
   hence true by Subgroup_def, group_id_element.
*)
val ideal_has_zero = store_thm(
  "ideal_has_zero",
  ``!r i:'a ring. Ring r /\ i << r ==> #0 IN I``,
  rpt strip_tac >>
  `i.sum <= r.sum /\ (i.sum.carrier = I)` by metis_tac[ideal_def] >>
  metis_tac[subgroup_id, Subgroup_def, group_id_element]);

(* Theorem: i << r ==> !x. x IN I <=> -x IN I *)
(* Proof:
   i.sum <= r.sum /\ (i.sum.carrier = I)   by ideal_def
   hence true by Subgroup_def, group_inv_element.
*)
val ideal_has_neg = store_thm(
  "ideal_has_neg",
  ``!r i:'a ring. Ring r /\ i << r ==> !x. x IN I ==> -x IN I``,
  rpt strip_tac >>
  `i.sum <= r.sum /\ (i.sum.carrier = I)` by metis_tac[ideal_def] >>
  metis_tac[subgroup_inv, Subgroup_def, group_inv_element]);

(* Theorem: i << r ==> !x y. x IN I /\ y IN I ==> (x + y) IN I *)
(* Proof: by ideal_property. *)
val ideal_has_sum = store_thm(
  "ideal_has_sum",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> (x + y) IN I``,
  rw[ideal_property]);

(* Theorem: i << r ==> !x y. x IN I /\ y IN I ==> (x - y) IN I *)
(* Proof: by ideal_has_neg, ideal_has_sum. *)
val ideal_has_diff = store_thm(
  "ideal_has_diff",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> (x - y) IN I``,
  rw[ideal_has_neg, ideal_has_sum]);

(* Theorem: i << r ==> !x y. x IN I /\ y IN I ==> (x * y) IN I *)
(* Proof: by ideal_property. *)
val ideal_has_product = store_thm(
  "ideal_has_product",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> (x * y) IN I``,
  rw[ideal_property]);

(* Theorem: i << r ==> !x y. x IN I /\ y IN R ==> x * y IN I *)
(* Proof: by ideal_product_property. *)
val ideal_has_multiple = store_thm(
  "ideal_has_multiple",
  ``!r i:'a ring. i << r ==> !x y. x IN I /\ y IN R ==> x * y IN I``,
  rw[ideal_product_property]);

(* Theorem: i << r ==> i.sum.id = #0 *)
(* Proof:
       i << r
   ==> i.sum <= r.sum        by ideal_def
   ==> i.sum.id = #0         by subgroup_id
*)
val ideal_zero = store_thm(
  "ideal_zero",
  ``!r i:'a ring. Ring r /\ i << r ==> (i.sum.id = #0)``,
  rw[ideal_def, subgroup_id]);

(* Theorem: i << r /\ j << r ==> ((i = j) <=> (I = J)) *)
(* Proof:
   If part: i = j ==> I = J, true by I = i.carrier, J = j.carrier.
   Only-if part: I = J ==> i = j
   By ring_component_equality, this is to show:
   (1) I = J ==> i.sum = j.sum
       True by monoid_component_equality, ideal_def, ideal_ops, ideal_zero.
   (2) I = J ==> i.prod = j.prod
       True by monoid_component_equality, ideal_def, ideal_ops.
*)
val ideal_eq_ideal = store_thm(
  "ideal_eq_ideal",
  ``!r i j:'a ring. Ring r /\ i << r /\ j << r ==> ((i = j) <=> (I = J))``,
  rw[ring_component_equality, EQ_IMP_THM] >>
  metis_tac[monoid_component_equality, ideal_def, ideal_ops, ideal_zero]);

(* Theorem: i << r /\ j << r ==> ((i << j) <=> (I <= J)) *)
(* Proof:
   After expanding by definitions, this is to show:
   (1) x IN I /\ y IN J /\ I SUBSET J ==> x * y IN I, true by SUBSET_DEF, and y IN J ==> y IN R.
   (2) x IN I /\ y IN J /\ I SUBSET J ==> y * x IN I, true by SUBSET_DEF, and x IN I ==> x IN R.
*)
val ideal_sub_ideal = store_thm(
  "ideal_sub_ideal",
  ``!r i j:'a ring. Ring r /\ i << r /\ j << r ==> ((i << j) <=> (I SUBSET J))``,
  rw[ideal_def, Subgroup_def] >>
  `r.sum.carrier = R` by rw[ring_add_group] >>
  metis_tac[SUBSET_DEF]);

(* Theorem: i << r ==> i << i *)
(* Proof:
   i << i iff I SUBSET I    by ideal_sub_ideal
          iff T             by SUBSET_REFL
*)
val ideal_sub_itself = store_thm(
  "ideal_sub_itself",
  ``!r i:'a ring. Ring r /\ i << r ==> i << i``,
  metis_tac[ideal_sub_ideal, SUBSET_REFL]);

(* Theorem: r << r *)
(* Proof: by definition, this is to show:
   (1) r.sum <= r.sum, true by subgroup_refl.
   (2) r.prod.carrier = R, true by ring_mult_monoid.
   (3) x IN R /\ y IN R ==> x * y IN R, true by ring_mult_element.
   (4) x IN R /\ y IN R ==> y * x IN R, true by ring_mult_element.
*)
val ideal_refl = store_thm(
  "ideal_refl",
  ``!r:'a ring. Ring r ==> r << r``,
  rw[ideal_def, subgroup_refl]);

(* Theorem: i << r /\ #1 IN I ==> i = r *)
(* Proof:
   By ring_component_equality, this is to show:
   (1) i << r /\ r << i ==> I = R
       i << r ==> i.sum.carrier = I SUBSET R = r.sum.carrier   by ideal_def, Subgroup_def
       r << i ==> r.sum.carrier = R SUBSET I = i.sum.carrier   by ideal_def, Subgroup_def
       Hence true by SUBSET_ANTISYM.
   (2) i << r /\ r << i ==> i.sum = r.sum
       i << r ==> i.sum <= r.sum    by ideal_def
       r << i ==> r.sum <= i.sum    by ideal_def
       Hence true by subgroup_antisym.
   (3) i << r /\ r << i ==> i.prod = r.prod
       By monoid_component_equality, this is to show:
       (a)  << r /\ r << i ==> i.prod.carrier = r.prod.carrier,
           i.e. I = R     by ideal_def
           so apply (1).
       (b) i << r ==> i.prod.op = $*, true by ideal_def.
       (c) i << r ==> i.prod.id = #1, true by ideal_def.
*)
val ideal_antisym = store_thm(
  "ideal_antisym",
  ``!(r:'a ring) (i:'a ring). i << r /\ r << i ==> (i = r)``,
  rw[ring_component_equality] >-
  metis_tac[ideal_def, Subgroup_def, SUBSET_ANTISYM] >-
  metis_tac[ideal_def, subgroup_antisym] >>
  rw[monoid_component_equality] >>
  metis_tac[ideal_def, Subgroup_def, SUBSET_ANTISYM]);

(* Theorem: i << r /\ #1 IN I ==> I = R *)
(* Proof:
   First, i << r ==> I SUBSET R, by Subgroup_def.
   Now, !z. #1 IN I /\ z IN R ==> #1 * z = z IN I by ideal_def.
   Hence R SUBSET I, or I = R by SUBSET_ANTISYM.
*)
val ideal_has_one = store_thm(
  "ideal_has_one",
  ``!r i:'a ring. Ring r /\ i << r /\ #1 IN I ==> (I = R)``,
  rw[ideal_def] >>
  `I SUBSET R` by metis_tac[Subgroup_def, Ring_def] >>
  `!y. y IN R ==> (#1 * y = y)` by rw[] >>
  `R SUBSET I` by metis_tac[SUBSET_DEF] >>
  rw[SUBSET_ANTISYM]);

(* Theorem: i << r /\ #1 IN I <=> i = r *)
(* Proof:
   If part: i << r /\ #1 IN I ==> i = r
   By ring_component_equality, this is to show:
   (1) i << r /\ #1 IN I ==> I = R, true by ideal_has_one.
   (2) i << r /\ #1 IN I ==> i.sum = r.sum
       By monoid_component_equality, this is to show:
       (a) i.sum.carrier = R, i.e. I = R, given by (1)
       (b) i.sum.op = $+, true by ideal_ops.
       (c) i.sum.id = #0, true by i.sum <= r.sum, and subgroup_id.
   (3) i << r /\ #1 IN I ==> i.prod = r.prod
       By monoid_component_equality, this is to show:
       (a) i.prod.carrier = r.prod.carrier, i.e. I = R, given by (1)
       (b) i.prod.op = $*, true by ideal_ops.
       (c) i.prod.id = #1, true by ideal_def.
   Only-if part: Ring i ==> i << i
   True by ideal_refl.
*)
val ideal_with_one = store_thm(
  "ideal_with_one",
  ``!r:'a ring. Ring r ==> !i. i << r /\ #1 IN I <=> (i = r)``,
  rw[EQ_IMP_THM] >| [
    rw[ring_component_equality] >| [
      rw[ideal_has_one],
      rw[monoid_component_equality] >| [
        metis_tac[ideal_carriers, ideal_has_one],
        rw[ideal_ops],
        metis_tac[ideal_def, subgroup_id]
      ],
      rw[monoid_component_equality] >| [
        metis_tac[ideal_def, ring_mult_monoid, ideal_has_one],
        rw[ideal_ops],
        metis_tac[ideal_def]
      ]
    ],
    rw[ideal_refl]
  ]);

(* Theorem: i << r /\ x IN I /\ unit x ==> i = r *)
(* Proof:
   x IN I ==> x IN R        by ideal_element_property
   unit x ==> |/ x IN R     by ring_unit_inv_element
   So x * |/x IN I          by ideal_has_multiple
   But x * |/x = #1         by ring_unit_rinv
   i.e. #1 IN I, hence follows by ideal_with_one.
*)
val ideal_with_unit = store_thm(
  "ideal_with_unit",
  ``!r i:'a ring. Ring r /\ i << r ==> !x. x IN I /\ unit x ==> (i = r)``,
  rpt strip_tac >>
  `x IN R` by metis_tac[ideal_element_property] >>
  `|/x IN R` by rw[ring_unit_inv_element] >>
  `x * |/x = #1` by rw[ring_unit_rinv] >>
  `#1 IN I` by metis_tac[ideal_has_multiple] >>
  metis_tac[ideal_with_one]);

(* ------------------------------------------------------------------------- *)
(* Ideal Cosets                                                              *)
(* ------------------------------------------------------------------------- *)

(* Define (left) coset of ideal with an element a in R by overloading *)
val _ = overload_on ("o", ``coset r.sum``);

(* Theorem: i << r ==> !x. x IN I ==> x o I = I *)
(* Proof: by coset_def, this is to show:
   (1) x IN I /\ z IN I ==> x + z IN I
       True by ideal_property.
   (2) x IN I /\ x' IN I ==> ?z. (x' = x + z) /\ z IN I
       Let z = x' + (-x)
       -x IN I         by ideal_has_neg
       hence z IN I    by ideal_property
       and x + z
         = x + (x' + -x)
         = x + (-x + x')  by ring_add_comm
         = x'             by ring_add_lneg_assoc
*)
val ideal_coset_of_element = store_thm(
  "ideal_coset_of_element",
  ``!r i:'a ring. Ring r /\ i << r ==> !x. x IN I ==> (x o I = I)``,
  rw[coset_def, EXTENSION, EQ_IMP_THM] >-
  rw[ideal_property] >>
  qexists_tac `x' + -x` >>
  `-x IN I` by rw[ideal_has_neg] >>
  metis_tac[ring_add_lneg_assoc, ring_add_comm, ideal_element_property, ideal_property]);

(* Theorem: i << r ==> !x. x IN R /\ (x o I = I) <=> x IN I *)
(* Proof:
   If part: x IN R /\ x o I = I ==> x IN I
     x o I = IMAGE (\z. x + z) I   by coset_def
     Since #0 IN I                 by ideal_has_zero
     x + #0 IN IMAGE (\z. x + z) I
     i.e. x + #0 IN I
     or x IN I                     by ring_add_rzero
   Only if part: x IN I ==> x IN R /\ (x o I = I)
     x IN R     by ideal_element_property
     x o I = I  by ideal_coset_of_element.
*)
val ideal_coset_eq_carrier = store_thm(
  "ideal_coset_eq_carrier",
  ``!r i:'a ring. Ring r /\ i << r ==> !x. x IN R /\ (x o I = I) <=> x IN I``,
  rw[EQ_IMP_THM] >| [
    `x o I = IMAGE (\z. x + z) I` by rw[GSYM coset_def] >>
    `#0 IN I` by rw[ideal_has_zero] >>
    `x + #0 IN IMAGE (\z. x + z) I` by rw[] >>
    metis_tac[ring_add_rzero, ideal_element_property],
    metis_tac[ideal_element_property],
    rw[ideal_coset_of_element]
  ]);

(* Theorem: Ring r /\ (i << r) ==> !x y. x IN R /\ y IN R ==> ((x o I = y o I) <=> x - y IN I) *)
(* Proof:
   Since i << r, i.sum <= r.sum by ideal_def
   Also r.sum.carrier = R       by ring_add_group
   Hence by subgroup_coset_eq, this is to show:
            - y + x IN I
   or        x + -y IN I        by ring_add_comm, ring_neg_element
   or        x - y  IN I        by ring_sub_def
*)
val ideal_coset_eq = store_thm(
  "ideal_coset_eq",
  ``!r i:'a ring. Ring r /\ (i << r) ==> !x y. x IN R /\ y IN R ==> ((x o I = y o I) <=> x - y IN I)``,
  rpt strip_tac >>
  `i.sum <= r.sum /\ (i.sum.carrier = I)` by metis_tac[ideal_def] >>
  `r.sum.carrier = R` by rw[] >>
  metis_tac[subgroup_coset_eq, ring_add_comm, ring_neg_element, ring_sub_def]);

(* ------------------------------------------------------------------------- *)
(* Ideal induces congruence in Ring.                                         *)
(* ------------------------------------------------------------------------- *)

(* Define congruence by ideal in Ring *)
val ideal_congruence_def = Define `
  ideal_congruence (r:'a ring) (i:'a ring) (x:'a) (y:'a) <=> x - y IN i.carrier
`;

(* set overloading *)
val _ = overload_on ("===", ``ideal_congruence r i``);
val _ = set_fixity "===" (Infix(NONASSOC, 450));

(* export definiton *)
val _ = export_rewrites ["ideal_congruence_def"];

(* Theorem: x === x *)
(* Proof:
   x - x = #0            by ring_sub_eq_zero
   hence true            by ideal_has_zero
*)
val ideal_congruence_refl = store_thm(
  "ideal_congruence_refl",
  ``!r i:'a ring. Ring r /\ i << r ==> !x. x IN R ==> x === x``,
  rw[ideal_has_zero]);

(* Theorem: x === y <=> y === x *)
(* Proof:
   x - y = - (y - x)    by ring_neg_sub
   hence true           by ideal_had_neg
*)
val ideal_congruence_sym = store_thm(
  "ideal_congruence_sym",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y. x IN R /\ y IN R ==> (x === y <=> y === x)``,
  rw_tac std_ss[ideal_congruence_def] >>
  metis_tac[ring_neg_sub, ideal_has_neg]);

(* Theorem: x === y /\ y === z ==> x === z *)
(* Proof:
   x - z = (x - y) + (y - z)   by ring_sub_def, ring_add_assoc, ring_add_lneg, ring_add_lzero
   hence true                  by ideal_has_sum
*)
val ideal_congruence_trans = store_thm(
  "ideal_congruence_trans",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> (x === y /\ y === z ==> x === z)``,
  rw_tac std_ss[ideal_congruence_def] >>
  `(x - y) + (y - z) = x + (-y + (y + -z))` by rw[ring_add_assoc] >>
  `_ = x + (-y + y + -z)` by rw[ring_add_assoc] >>
  `_ = x - z` by rw[] >>
  metis_tac[ideal_has_sum]);

(* Theorem: === is an equivalence relation on R. *)
(* Proof: by reflexive, symmetric and transitive of === on R. *)
val ideal_congruence_equiv = store_thm(
  "ideal_congruence_equiv",
  ``!r i:'a ring. Ring r /\ i << r ==> $=== equiv_on R``,
  rw_tac std_ss[equiv_on_def] >-
  rw[ideal_congruence_refl] >-
  rw[ideal_congruence_sym] >>
  metis_tac[ideal_congruence_trans]);

(* Theorem: Ring r /\ (i << r) ==> !x y. x IN R /\ y IN R ==> ((x o I = y o I) <=> x === y) *)
(* Proof: by ideal_congruence_def, ideal_coset_eq. *)
val ideal_coset_eq_congruence = store_thm(
  "ideal_coset_eq_congruence",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y. x IN R /\ y IN R ==> ((x o I = y o I) <=> x === y)``,
  rw[ideal_coset_eq]);

(* Characterization: x === y iff x, y in the same coset, element of (r/i) *)

(* Theorem: i << r ==> !x y. x IN I /\ y IN I ==> (x === y) <=> inCoset r.sum i.sum x y *)
(* Proof: by definitions, this is to show:
   (1) x IN I /\ y IN I /\ x + -y IN I ==> ?z. (y = x + z) /\ z IN I
       Let z = -x + y,
       then z IN I   by ideal_has_neg, ideal_has_sum
       and y = x + (-x + y)   by ring_add_lneg_assoc
   (2) x IN I /\ z IN I ==> x + -(x + z) IN I
         x + -(x + z)
       = x + (-x + -z)   by ring_neg_add
       = -z              by ring_add_lneg_assoc
       hence true        by ideal_has_neg
*)
val ideal_congruence_iff_inCoset = store_thm(
  "ideal_congruence_iff_inCoset",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y. x IN I /\ y IN I ==> ((x === y) <=> inCoset r.sum i.sum x y)``,
  rpt strip_tac >>
  `i.sum <= r.sum /\ (i.sum.carrier = I)` by metis_tac[ideal_def] >>
  `!z. z IN I ==> z IN R` by metis_tac[ideal_element_property] >>
  rw[inCoset_def, coset_def, EQ_IMP_THM] >| [
    qexists_tac `-x + y` >>
    metis_tac[ring_add_lneg_assoc, ideal_has_neg, ideal_has_sum],
    `!y. y IN R ==> -y IN R` by rw[] >>
    metis_tac[ring_neg_add, ring_add_lneg_assoc, ideal_has_neg]
  ]);

(* Theorem: x === y ==> z * x === z * y  *)
(* Proof:
       x === y
   ==> x - y IN R          by ideal_congruence_def
   ==> z * (x - y) IN R    by ideal_def
   ==> z * x - z * y IN R  by ring_mult_rsub, ideal_element_property
   ==> z * x === z * y     by ideal_congruence_def
*)
val ideal_congruence_mult = store_thm(
  "ideal_congruence_mult",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((x === y) ==> (z * x === z * y))``,
  rw_tac std_ss[ideal_congruence_def] >>
  `z * (x - y) IN I` by metis_tac[ideal_def] >>
  metis_tac[ring_mult_rsub, ideal_element_property]);

(* Theorem: i << r /\ x IN I /\ y IN R ==> y IN I <=> x === y *)
(* Proof:
   If part: y IN I ==> x === y
       x IN I /\ y IN I
   ==> x - y IN I             by ideal_has_diff
   ==> x === y                by ideal_congruence_def
   Only-if part: x === y ==> y IN I
       x === y
   ==> y === x                by ideal_congruence_sym
   ==> y - x IN I             by ideal_congruence_def
   ==> (y - x) + x IN I       by ideal_has_sum
   ==> y IN I                 by ring_sub_add
*)
val ideal_congruence_elements = store_thm(
  "ideal_congruence_elements",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y. x IN I /\ y IN R ==> (y IN I <=> x === y)``,
  rpt strip_tac >>
  `!z. z IN I ==> z IN R` by metis_tac[ideal_element_property] >>
  rw_tac std_ss[ideal_congruence_def, EQ_IMP_THM] >-
  rw[ideal_has_diff] >>
  `x + -y IN I` by metis_tac[ring_sub_def] >>
  `x + -y - x IN I` by rw[ideal_has_diff] >>
  `-y IN I` by metis_tac[ring_add_sub_comm, ring_neg_element] >>
  metis_tac[ideal_has_neg, ring_neg_neg]);

(* ------------------------------------------------------------------------- *)
(* Principal Ideal = Ideal generated by a Ring element                       *)
(* ------------------------------------------------------------------------- *)

(* Multiples of a Ring element p *)
(* val element_multiple_def = Define `element_multiple (r:'a ring) (p:'a) = {p * x | x IN R}`; *)

(* use overloading *)
val _ = overload_on ("*", ``coset r.prod``);

(* Integer Ring Ideals are multiples *)
val principal_ideal_def = Define `
  principal_ideal (r:'a ring) (p:'a) =
    <| carrier := p * R;
           sum := <| carrier := p * R; op := r.sum.op; id := r.sum.id |>;
          prod := <| carrier := p * R; op := r.prod.op; id := r.prod.id |>
     |>
`;
(* Note: <p>.prod is only type-compatible with monoid, it is not a monoid: prod.id may not be in carrier. *)

(* set overloading *)
val _ = overload_on ("<p>", ``principal_ideal r p``);
val _ = overload_on ("<q>", ``principal_ideal r q``);

(*
- principal_ideal_def;
> val it = |- !r p. <p> = <|carrier := p * R;
                                sum := <|carrier := p * R; op := $+; id := #0|>;
                               prod := <|carrier := p * R; op := $*; id := #1|>
                           |> : thm
*)

(* Theorem: Properties of principal ideal. *)
(* Proof: by definition. *)
val principal_ideal_property = store_thm(
  "principal_ideal_property",
  ``!(r:'a ring) (p:'a).
     (<p>.carrier = p * R) /\ (<p>.sum.carrier = p * R) /\ (<p>.prod.carrier = p * R) /\
     (<p>.sum.op = r.sum.op) /\ (<p>.prod.op = r.prod.op) /\
     (<p>.sum.id = #0) /\ (<p>.prod.id = #1)``,
  rw[principal_ideal_def]);

(* Theorem: x IN <p>.carrier <=> ?z. z IN R /\ (x = p * z) *)
(* Proof: by definitions. *)
val principal_ideal_element = store_thm(
  "principal_ideal_element",
  ``!p x:'a. x IN <p>.carrier <=> ?z. z IN R /\ (x = p * z)``,
  rw[principal_ideal_def, coset_def] >>
  metis_tac[]);

(* Theorem: p IN <p>.carrier *)
(* Proof:
   By principal_ideal_element, this is to show:
   ?x. (p = p * x) /\ x IN R
   Let x = #1,
   then #1 IN R      by ring_one_element
   and  p = p * #1   by ring_mult_rone
   hence true.
*)
val principal_ideal_has_element = store_thm(
  "principal_ideal_has_element",
  ``!r:'a ring. Ring r ==> !p. p IN R ==> p IN <p>.carrier``,
  metis_tac[principal_ideal_element, ring_one_element, ring_mult_rone]);

(* Theorem: Group <p>.sum *)
(* Proof:
   First, <p>.carrier = p * R     by principal_ideal_property
   and !x. x IN p * R ==> x IN R  by coset_def
   Check group axioms:
   (1) x IN p * R /\ y IN p * R ==> x + y IN p * R
       Let x = p * u, y = p * v,  u IN R and v IN R
       x + y = p * u + p * v
             = p * (u + v)        by ring_mult_radd
       Hence in p * R.
   (2) x IN p * R /\ y IN p * R /\ z IN p * R ==> x + y + z = x + (y + z)
       True by ring_add_assoc.
   (3) #0 IN p * R
       Since #0 = p * #0          by ring_mult_rzero
       and #0 IN R                by ring_zero_element
       Hence true.
   (4) x IN p * R ==> #0 + x = x
       True by ring_add_lzero.
   (5) x IN p * R ==> ?y. y IN p * R /\ (y + x = #0)
       Let x = p * u, u IN R      by principal_ideal_element
       Let y = p * (-u), -u IN R  by ring_neg_element
       Hence y IN p * R, and
          y + x
       = p * -u + p * u
       = - (p * u) + p * u        by ring_neg_mult
       = #0                       by ring_add_lneg
*)
val principal_ideal_group = store_thm(
  "principal_ideal_group",
  ``!r:'a ring. Ring r ==> !p. p IN R ==> Group <p>.sum``,
  ntac 4 strip_tac >>
  `<p>.carrier = p * R` by rw[principal_ideal_property] >>
  (`!x. x IN p * R ==> x IN R` by (rw[coset_def] >> rw[])) >>
  rw_tac std_ss[principal_ideal_def, group_def_alt, GSPECIFICATION] >| [
    `?u. u IN R /\ (x = p * u)` by metis_tac[principal_ideal_element] >>
    `?v. v IN R /\ (y = p * v)` by metis_tac[principal_ideal_element] >>
    `x + y = p * (u + v)` by rw[ring_mult_radd] >>
    metis_tac[principal_ideal_element, ring_add_element],
    rw[ring_add_assoc],
    metis_tac[principal_ideal_element, ring_zero_element, ring_mult_rzero],
    rw[],
    `?u. u IN R /\ (x = p * u)` by metis_tac[principal_ideal_element] >>
    qexists_tac `p * (-u)` >>
    `p * -u = - x` by metis_tac[ring_neg_mult] >>
    `p * -u + x = #0` by metis_tac[ring_add_lneg] >>
    metis_tac[principal_ideal_element, ring_neg_element]
  ]);

(* Theorem: <p>.sum <= r.sum *)
(* Proof: for a subgroup:
   (1) Group <p>.sum,
       true by principal_ideal_group
   (2) <p>.sum SUBSET r.sum.carrier,
       i.e. to show: p * R SUBSET R
         or to show: p IN R /\ z IN R ==> p * z IN R
       true by ring_mult_element.
*)
val principal_ideal_subgroup = store_thm(
  "principal_ideal_subgroup",
  ``!r:'a ring. Ring r ==> !p. p IN R ==> <p>.sum <= r.sum``,
  rw[Subgroup_def, principal_ideal_group, principal_ideal_def] >>
  rw[coset_def, SUBSET_DEF] >>
  rw[]);

(* Theorem: <p>.sum << r.sum *)
(* Proof: for a normal subgroup:
   (1) <p>.sum <= r.sum,
       true by principal_ideal_subgroup
   (2) p IN R /\ a IN R ==> IMAGE (\z. a + z) <p>.sum.carrier = IMAGE (\z. z + a) <p>.sum.carrier
       true ring_add_comm and EXTENSION.
*)
val principal_ideal_subgroup_normal = store_thm(
  "principal_ideal_subgroup_normal",
  ``!r:'a ring. Ring r ==> !p. p IN R ==> <p>.sum << r.sum``,
  rw[normal_subgroup_alt, coset_def, right_coset_def] >| [
    rw[principal_ideal_subgroup],
    rw[principal_ideal_def, coset_def, EXTENSION] >>
    `!x. x IN R ==> (a + p * x = p * x + a)` by rw[ring_add_comm] >>
    metis_tac[]
  ]);

(* Theorem: <p> is an ideal: <p> << r. *)
(* Proof: by ideal_def
   (1) <p>.sum <= r.sum
       True by principal_ideal_subgroup.
   (2) x IN p * R /\ y IN R ==> x * y IN p * R
       x = p * u   for some u IN R
       x * y = (p * u) * y
             = p * (u * y)     by ring_mult_assoc
       Hence x * y IN p * R.
   (3) x IN p * R /\ y IN R ==> y * x IN p * R
       Use above and y * x = x * y   by ring_mult_comm
*)
val principal_ideal_ideal = store_thm(
  "principal_ideal_ideal",
  ``!r:'a ring. Ring r ==> !p. p IN R ==> <p> << r``,
  rpt strip_tac >>
  `<p>.carrier = p * R` by metis_tac[principal_ideal_property] >>
  rw[ideal_def, principal_ideal_def, principal_ideal_subgroup] >| [
    `?u. u IN R /\ (x = p * u)` by metis_tac[principal_ideal_element] >>
    `x * y = p * (u * y)` by rw[ring_mult_assoc] >>
    metis_tac[principal_ideal_element, ring_mult_element],
    `?u. u IN R /\ (x = p * u)` by metis_tac[principal_ideal_element] >>
    `y * (p * u) = p * u  * y` by rw[ring_mult_comm] >>
    `_ = p * (u * y)` by rw[ring_mult_assoc] >>
    metis_tac[principal_ideal_element, ring_mult_element]
  ]);

(* Theorem: A principal ideal has all ideals of its elements:
            p IN R /\ q IN <p>.carrier ==> <q> << <p> *)
(* Proof:
   First, q IN R    by principal_ideal_element, ring_mult_element
   thus  <p> << r   by principal_ideal_ideal
   and   <q> << r   by principal_ideal_ideal
   By ideal_def, this is to show:
   (1) <q>.sum <= <p>.sum
       By Subgroup_def, this is to show:
       (a) Group <q>.sum, true by ideal_has_subgroup and Subgroup_def.
       (b) Group <p>.sum, true by ideal_has_subgroup and Subgroup_def.
       (c) <q>.sum.carrier SUBSET <p>.sum.carrier,
           or, x IN <q>.sum.carrier ==> x IN <p>.sum.carrier
           Since q IN <p>.carrier,
               q = p * z   for some z IN R, by principal_ideal_def
           x = q * k       for some k IN R, by principal_ideal_def
             = p * (z * k) by ring_mult_assoc
           hence x IN <p>.carrier.
       (d) <q>.sum.op = <p>.sum.op, true by ideal_ops.
   (2) <q>.sum.carrier = <q>.carrier, true by ideal_carriers.
   (3) <q>.prod.carrier = <q>.carrier, true by ideal_carriers.
   (4) <q>.prod.op = <p>.prod.op, true by ideal_ops.
   (5) <q>.prod.id = <p>.prod.id, true by ideal_def.
   (6) x IN <q>.carrier /\ y IN <q>.carrier ==> <p>.prod.op x y IN <q>.carrier, true by ideal_product_property.
       y IN <q>.carrier ==> y IN R    by ideal_element_property
       <p>.prod.op = r.prod.op        by ideal_ops
       Hence true by ideal_product_property.
   (7) Similar to (6), also by ideal_product_property
*)
val principal_ideal_has_principal_ideal = store_thm(
  "principal_ideal_has_principal_ideal",
  ``!r:'a ring. Ring r ==> !p q. p IN R /\ q IN <p>.carrier ==> (<q> << <p>)``,
  rpt strip_tac >>
  `<p> << r` by rw[principal_ideal_ideal] >>
  `q IN R` by metis_tac[principal_ideal_element, ring_mult_element] >>
  `<q> << r` by rw[principal_ideal_ideal] >>
  rw[ideal_def] >| [
    rw[Subgroup_def] >-
    metis_tac[ideal_has_subgroup, Subgroup_def] >-
    metis_tac[ideal_has_subgroup, Subgroup_def] >-
   (`<q>.carrier SUBSET <p>.carrier` suffices_by metis_tac[ideal_carriers] >>
    `?z. z IN R /\ (q = p * z)` by metis_tac[principal_ideal_element] >>
    rw[principal_ideal_def, coset_def, SUBSET_DEF] >>
    qexists_tac `z * z'` >>
    rw[ring_mult_assoc]) >>
    metis_tac[ideal_ops],
    metis_tac[ideal_carriers],
    metis_tac[ideal_carriers],
    metis_tac[ideal_ops],
    metis_tac[ideal_def],
    metis_tac[ideal_element_property, ideal_ops, ideal_product_property],
    metis_tac[ideal_element_property, ideal_ops, ideal_product_property]
  ]);

(* Theorem: if elements are associates, their principal ideals are equal.
            p IN R /\ q IN R /\ unit u /\ (p = q * u) ==> <p> = <q>  *)
(* Proof:
   First, <p> << r     by principal_ideal_ideal
      and <q> << r     by principal_ideal_ideal
      and u IN R       by ring_unit_element
   By ideal_eq_ideal, only need to show: <p>.carrier = <q>.carrier
   Let x IN <p>.carrier,
   i.e. x = p * z      for some z
          = q * u * z  given p = q * u
          = q * (u * z)
   Hence x IN <q>.carrier. Thus <p>.carrier SUBSET <q>.carrier.
   But u has |/u IN R    by ring_unit_inv_element
     p * |/u
   = q * u * |/u         given p = q * u
   = q * (u * |/u)       by ring_mult_assoc
   = q * #1              by ring_unit_rinv
   = q                   by ring_mult_rone
   Hence using the same argument gives <q>.carrier SUBSET <p>.carrier.
   or <p>.carrier = <q>.carrier    by SUBSET_ANTISYM
*)
val principal_ideal_eq_principal_ideal = store_thm(
  "principal_ideal_eq_principal_ideal",
  ``!r:'a ring. Ring r ==> !p q u. p IN R /\ q IN R /\ unit u /\ (p = q * u) ==> (<p> = <q>)``,
  rpt strip_tac >>
  `<p> << r` by rw[principal_ideal_ideal] >>
  `<q> << r` by rw[principal_ideal_ideal] >>
  `u IN R` by rw[ring_unit_element] >>
  `<p>.carrier = <q>.carrier` suffices_by metis_tac[ideal_eq_ideal] >>
  rw[principal_ideal_def, coset_def, EXTENSION, EQ_IMP_THM] >| [
    qexists_tac `u * z` >>
    rw[ring_mult_assoc],
    `|/u IN R` by rw[ring_unit_inv_element] >>
    qexists_tac `|/u * z` >>
    `q * u * ( |/ u * z) = q * (u * |/ u * z)` by rw[ring_mult_assoc] >>
    rw[ring_unit_rinv]
  ]);
(* Note: the converse can be proved only in integral domain. *)

(* Theorem: i << r /\ p IN R ==> (p IN I <=> <p> << i) *)
(* Proof:
   First, <p> << r    by principal_ideal_ideal
   If part: p IN I ==> <p> << i
   By ideal_def, this is to show:
   (1) <p>.sum <= i.sum
       By Subgroup_def, this is to show:
       (a) Group <p>.sum, true by ideal_has_subgroup, Subgroup_def
       (b) Group i.sum, true by ideal_has_subgroup, Subgroup_def
       (c) <p>.carrier SUBSET I
           By principal_ideal_def, this is to show:
           p IN I /\ z IN R ==> p * z IN I, true by ideal_product_property
   (2) <p>.prod.id = i.prod.id
       <p>.prod.id = r.prod.id    by ideal_def
       i.prod.id = r.prod.id      by ideal_def
       Hence true.
   (3) x IN <p>.carrier /\ y IN I ==> x * y IN <p>.carrier
       Since y IN I ==> y IN R    by ideal_element_property
       This is true by ideal_product_property.
   (4) x IN <p>.carrier /\ y IN I ==> y * x IN <p>.carrier
       Since y IN I ==> y IN R    by ideal_element_property
       This is also true by ideal_product_property.
   Only-if part: p IN R /\ <p> << i ==> p IN I
     p IN <p>.carrier           by principal_ideal_has_element
     hence p IN i.sum.carrier   by ideal_element
     or p IN I since i.sum.carrier = I   by ideal_carriers.
*)
val ideal_has_principal_ideal = store_thm(
  "ideal_has_principal_ideal",
  ``!r i:'a ring. Ring r /\ i << r ==> !p. p IN R ==> (p IN I <=> (<p> << i))``,
  rpt strip_tac >>
  `<p> << r` by rw[principal_ideal_ideal] >>
  rw[EQ_IMP_THM] >| [
    `!j. j << r ==> (j.sum.carrier = J)` by metis_tac[ideal_carriers] >>
    `!j. j << r ==> (j.prod.carrier = J)` by metis_tac[ideal_carriers] >>
    `!j. j << r ==> (j.sum.op = r.sum.op)` by metis_tac[ideal_ops] >>
    `!j. j << r ==> (j.prod.op = r.prod.op)` by metis_tac[ideal_ops] >>
    rw[ideal_def] >| [
      `Group <p>.sum` by metis_tac[ideal_has_subgroup, Subgroup_def] >>
      `Group i.sum` by metis_tac[ideal_has_subgroup, Subgroup_def] >>
      rw[Subgroup_def] >>
      rw[principal_ideal_def, coset_def, SUBSET_DEF] >>
      rw[ideal_product_property],
      metis_tac[ideal_def],
      metis_tac[ideal_element_property, ideal_product_property],
      metis_tac[ideal_element_property, ideal_product_property]
    ],
    metis_tac[principal_ideal_has_element, ideal_element, ideal_carriers]
  ]);

(* ------------------------------------------------------------------------- *)
(* Trivial Ideal                                                             *)
(* ------------------------------------------------------------------------- *)

(* use overloading for ring ideal zero *)
val _ = overload_on ("<#0>", ``principal_ideal r #0``);

(* Theorem: <#0>.carrier = {#0} *)
(* Proof: by definitions, this is to show:
   (1) z IN R ==> #0 * z = #0, true by ring_mult_lzero.
   (2) ?z. (#0 = #0 * z) /\ z IN R, let z = #0, true by ring_mult_zero_zero.
*)
val zero_ideal_sing = store_thm(
  "zero_ideal_sing",
  ``!r:'a ring. Ring r ==> (<#0>.carrier = {#0})``,
  rw[principal_ideal_def, coset_def, EXTENSION, EQ_IMP_THM] >-
  rw[] >>
  metis_tac[ring_mult_zero_zero, ring_zero_element]);

(* Theorem: <#0> << r *)
(* Proof:
   Since #0 IN R    by ring_zero_element
   This follows     by principal_ideal_ideal.
*)
val zero_ideal_ideal = store_thm(
  "zero_ideal_ideal",
  ``!r:'a ring. Ring r ==> <#0> << r``,
  rw[principal_ideal_ideal]);

(* Theorem: SING I <=> i = <#0> *)
(* Proof: This is to show:
   (1) i << r /\ SING I ==> i = <#0>
       Since #0 IN I      by ideal_has_zero
       I = {#0}           by SING_DEF, IN_SING
         = <#0>.carrier   by zero_ideal_sing
       but <#0> << r      by zero_ideal_ideal
       hence i = <#0>     by ideal_eq_ideal
   (2) SING <#0>.carrier
       Since <#0>.carrier = {#0}   by zero_ideal_sing
       hence true                  by SING_DEF
*)
val ideal_carrier_sing = store_thm(
  "ideal_carrier_sing",
  ``!r i:'a ring. Ring r /\ i << r ==> (SING I <=> (i = <#0>))``,
  rw[EQ_IMP_THM] >| [
    `#0 IN I` by rw[ideal_has_zero] >>
    `I = {#0}` by metis_tac[SING_DEF, IN_SING] >>
    metis_tac[ideal_eq_ideal, zero_ideal_ideal, zero_ideal_sing],
    rw[zero_ideal_sing]
  ]);

(* ------------------------------------------------------------------------- *)
(* Sum of Ideals                                                             *)
(* ------------------------------------------------------------------------- *)

(* Define sum of ideals *)
val ideal_sum_def = Define `
  ideal_sum (r:'a ring) (i:'a ring) (j:'a ring) =
      <| carrier := {x + y | x IN I /\ y IN J};
             sum := <| carrier := {x + y | x IN I /\ y IN J}; op := r.sum.op; id := r.sum.id |>;
            prod := <| carrier := {x + y | x IN I /\ y IN J}; op := r.prod.op; id := r.prod.id |>
       |>
`;
val _ = overload_on ("+", ``ideal_sum r``);

(* Theorem: x IN (i + j).carrier <=> ?y z. y IN I /\ z IN J /\ (x = y + z) *)
(* Proof: by definition. *)
val ideal_sum_element = store_thm(
  "ideal_sum_element",
  ``!(i:'a ring) (j:'a ring) x. x IN (i + j).carrier <=> ?y z. y IN I /\ z IN J /\ (x = y + z)``,
  rw[ideal_sum_def] >>
  metis_tac[]);

(* Theorem: i << r /\ j << r ==> i + j = j + i *)
(* Proof:
   By ideal_sum_def, this is to show:
   {x + y | x IN I /\ y IN J} = {x + y | x IN J /\ y IN I}
   Since !z. z IN I ==> z IN R    by ideal_element_property
   This is true by ring_add_comm.
*)
val ideal_sum_comm = store_thm(
  "ideal_sum_comm",
  ``!r i j:'a ring. Ring r /\ i << r /\ j << r ==> (i + j = j + i)``,
  rw[ideal_sum_def, EXTENSION] >>
  metis_tac[ideal_element_property, ring_add_comm]);

(* Theorem: i << r /\ j << r ==>  Group (i + j).sum *)
(* Proof: by group definition, this is to show:
   for x = x' + y', y = x'' + y'', z = x''' + y''', x, y, z in (i + j).sum,
   Note !z. z IN I ==> z IN R /\ z IN J ==> z IN R     by ideal_element_property
   (1) ?x y. x IN I /\ y IN J /\ (x' + y' + (x'' + y'') = x + y)
       x' + y' + (x'' + y'') = (x' + x'') + (y' + y'')      by ring_add_assoc, ring_add_comm
       Let x = x' + x'', y = y' + y'', then x IN I, y IN J  by ideal_property
   (2) x' + y' + (x'' + y'') + (x''' + y''') = x' + y' + (x'' + y'' + (x''' + y'''))
       True by ring_add_assoc.
   (3) ?x y. x IN I /\ y IN J /\ (#0 = x + y)
       Let x = #0, y = #0, and #0 IN I, #0 IN J by ideal_has_zero.
       True by ring_add_zero_zero.
   (4) #0 + (x' + y) = x' + y
       True by ring_add_lzero.
   (5) x' IN J /\ y IN J ==> ?y'. (?x y. x IN I /\ y IN J /\ (y' = x + y)) /\ (y' + (x' + y) = #0)
       Let y' = -(x' + y) = -x' + -y   by ring_neg_add
       -x' IN I and -y IN J            by ideal_has_neg
       Hence true by ring_add_lneg.
*)
val ideal_sum_group = store_thm(
  "ideal_sum_group",
  ``!r i j:'a ring. Ring r /\ i << r /\ j << r ==> Group (i + j).sum``,
  rpt strip_tac >>
  (`!z. z IN {x + y | x IN I /\ y IN J} <=> ?x y. x IN I /\ y IN J /\ (z = x + y)` by (rw[] >> metis_tac[])) >>
  `!z. (z IN I ==> z IN R) /\ (z IN J ==> z IN R)` by metis_tac[ideal_element_property] >>
  rw_tac std_ss[ideal_sum_def, group_def_alt] >| [
    `x' + y' + (x'' + y'') = x' + (y' + x'' + y'')` by rw[ring_add_assoc] >>
    `_ = x' + (x'' + y' + y'')` by rw[ring_add_comm] >>
    `_ = (x' + x'') + (y' + y'')` by rw[ring_add_assoc] >>
    `x' + x'' IN I /\ y' + y'' IN J` by rw[ideal_property] >>
    metis_tac[],
    rw[ring_add_assoc],
    `#0 IN I /\ #0 IN J` by rw[ideal_has_zero] >>
    metis_tac[ring_add_zero_zero],
    rw[],
    `-(x' + y) = -x' + -y` by rw[ring_neg_add] >>
    `-x' IN I /\ -y IN J` by rw[ideal_has_neg] >>
    qexists_tac `-(x' + y)` >>
    rw[] >>
    metis_tac[]
  ]);

(* Theorem: i << r /\ j << r ==> i.sum <= (i + j).sum *)
(* Proof: by Subgroup_def, this is to show:
   (1) Group i.sum,
       Since i.sum << r.sum   by ideal_def, true by Subgroup_def.
   (2) i << r /\ j << r ==> Group (i + j).sum
       True by ideal_sum_group.
   (3) i.sum.carrier SUBSET (i + j).sum.carrier
       i.e. x IN I ==> ?y. y IN J /\ x = x + y,
       so take y = #0, and #0 IN J by ideal_has_zero.
   (4) x IN I /\ y IN I ==> i.sum.op x y = (i + j).sum.op x y
       True by ideal_ops.
*)
val ideal_subgroup_ideal_sum = store_thm(
  "ideal_subgroup_ideal_sum",
  ``!r i j:'a ring. Ring r /\ i << r /\ j << r ==> i.sum <= (i + j).sum``,
  rw[Subgroup_def] >| [
    metis_tac[ideal_def, Subgroup_def],
    rw[ideal_sum_group],
    rw[ideal_sum_def, SUBSET_DEF] >>
    metis_tac[ideal_def, ideal_has_zero, ring_add_rzero, ideal_element_property],
    rw[ideal_sum_def] >>
    metis_tac[ideal_ops]
  ]);

(* Theorem: i << r /\ j << r ==> (i + j).sum <= r.sum *)
(* Proof: by Subgroup_def, this is to show:
   (1) Group (i + j).sum,
       True by ideal_sum_group.
   (2) (i + j).sum.carrier SUBSET R
       By ideal_sum_def, and SUBSET_DEF, this is to show:
       x' IN I /\ y IN J ==> x' + y IN R
       But x' IN R /\ y IN R   by ideal_element_property
       hence true by ring_add_element.
   (3) x IN (i + j).sum.carrier /\ y IN (i + j).sum.carrier ==> (i + j).sum.op x y = x + y
       True by ideal_sum_def.
*)
val ideal_sum_subgroup = store_thm(
  "ideal_sum_subgroup",
  ``!r i j:'a ring. Ring r /\ i << r /\ j << r ==> (i + j).sum <= r.sum``,
  rw[Subgroup_def] >| [
    rw[ideal_sum_group],
    rw[ideal_sum_def, SUBSET_DEF] >>
    metis_tac[ideal_element_property, ring_add_element],
    rw[ideal_sum_def]
  ]);

(* Theorem: i << r /\ j << r ==> i << i + j *)
(* Proof: by definition, this is to show:
   (1) i.sum <= (i + j).sum, true by ideal_subgroup_ideal_sum.
   (2) i.sum.carrier = I, true by ideal_def.
   (3) i.prod.carrier = I, true by ideal_def.
   (4) i.prod.op = (i + j).prod.op, true by ideal_sum_def, ideal_ops.
   (5) i.prod.id = (i + j).prod.id, true by ideal_sum_def, ideal_def.
   (6) x IN I /\ y IN (i + j).carrier ==> (i + j).prod.op x y IN I
       i.e. x * y IN I
       Since y IN (i + j).carrier, y IN R  by ideal_element_property, ring_add_element
       Hence x * y IN I by ideal_def.
   (7) x IN I /\ y IN (i + j).carrier ==> (i + j).prod.op y x IN I
       i.e. y * x IN I
       By same reasoning above, apply ring_mult_comm.
*)
val ideal_sum_has_ideal = store_thm(
  "ideal_sum_has_ideal",
  ``!r i j:'a ring. Ring r /\ i << r /\ j << r ==> i << (i + j)``,
  rpt strip_tac >>
  rw[ideal_def] >-
  rw[ideal_subgroup_ideal_sum] >-
  metis_tac[ideal_def] >-
  metis_tac[ideal_def] >-
 (rw[ideal_sum_def] >>
  metis_tac[ideal_ops]) >-
 (rw[ideal_sum_def] >>
  metis_tac[ideal_def]) >-
 (rw[ideal_sum_def] >>
  (`!z. z IN (i + j).carrier <=> ?x y. x IN I /\ y IN J /\ (z = x + y)` by (rw[ideal_sum_def] >> metis_tac[])) >>
  metis_tac[ideal_element_property, ring_add_element, ideal_def]) >>
  rw[ideal_sum_def] >>
  (`!z. z IN (i + j).carrier <=> ?x y. x IN I /\ y IN J /\ (z = x + y)` by (rw[ideal_sum_def] >> metis_tac[])) >>
  metis_tac[ideal_element_property, ring_add_element, ring_mult_comm, ideal_def]);

(* Theorem: i << r /\ j << r ==> j << i + j *)
(* Proof: by ideal_sum_has_ideal and ideal_sum_comm. *)
val ideal_sum_has_ideal_comm = store_thm(
  "ideal_sum_has_ideal_comm",
  ``!r i j:'a ring. Ring r /\ i << r /\ j << r ==> j << (i + j)``,
  metis_tac[ideal_sum_has_ideal, ideal_sum_comm]);

(* Theorem: i << r /\ j << r ==> i + j << r *)
(* Proof: by definition, this is to show:
   (1) (i + j).sum <= r.sum, true by ideal_sum_subgroup.
   (2) (i + j).sum.carrier = (i + j).carrier, true by ideal_sum_def.
   (3) (i + j).prod.carrier = (i + j).carrier, true by ideal_sum_def.
   (4) (i + j).prod.op = $*, true by ideal_sum_def.
   (5) (i + j).prod.id = #1, true by ideal_sum_def.
   (6) x IN (i + j).carrier /\ y IN R ==> x * y IN (i + j).carrier
       Since x = p + q    with p IN I and q IN J
       x * y = (p + q) * y
             = p * y + q * y           by ring_mult_ladd
       But p * y IN I and q * y IN J   by ideal_def
       hence x * y IN (i + j).carrier.
   (7) x IN (i + j).carrier /\ y IN R ==> y * x IN (i + j).carrier
       Same reasoning above, using ring_mult_radd.
*)
val ideal_sum_ideal = store_thm(
  "ideal_sum_ideal",
  ``!r i j:'a ring. Ring r /\ i << r /\ j << r ==> (i + j) << r``,
  rpt strip_tac >>
  rw[ideal_def] >| [
    rw[ideal_sum_subgroup],
    rw[ideal_sum_def],
    rw[ideal_sum_def],
    rw[ideal_sum_def],
    rw[ideal_sum_def],
    (`!z. z IN (i + j).carrier <=> ?x y. x IN I /\ y IN J /\ (z = x + y)` by (rw[ideal_sum_def] >> metis_tac[])) >>
    `!z. (z IN I ==> z IN R) /\ (z IN J ==> z IN R)` by metis_tac[ideal_element_property] >>
    `?p q. p IN I /\ q IN J /\ (x = p + q)` by metis_tac[] >>
    `x * y = (p + q) * y` by rw[] >>
    `_ = p * y + q * y` by rw[ring_mult_ladd] >>
    `p * y IN I /\ q * y IN J` by metis_tac[ideal_def] >>
    metis_tac[],
    (`!z. z IN (i + j).carrier <=> ?x y. x IN I /\ y IN J /\ (z = x + y)` by (rw[ideal_sum_def] >> metis_tac[])) >>
    `!z. (z IN I ==> z IN R) /\ (z IN J ==> z IN R)` by metis_tac[ideal_element_property] >>
    `?p q. p IN I /\ q IN J /\ (x = p + q)` by metis_tac[] >>
    `y * x = y * (p + q)` by rw[] >>
    `_ = y * p + y * q` by rw[ring_mult_radd] >>
    `y * p IN I /\ y * q IN J` by metis_tac[ideal_def] >>
    metis_tac[]
  ]);

(* Theorem: i << r /\ j << r ==> (i + j << j <=> i << j) *)
(* Proof:
   By ideal_sub_ideal, this is to show:
   (i + j).carrier SUBSET J <=> I SUBSET J
   Expand by ideal_sum_element, this is to show:
   (1) x IN I /\ !x. (?y z. y IN I /\ z IN J /\ (x = y + z)) ==> x IN J ==> x IN J ==> x IN J
       x IN I ==> x IN R                      by ideal_element_property
       j << r ==> #0 IN J                     by ideal_has_zero
       x = x + #0                             by ring_add_rzero
       Hence x IN (i + j).carrier             by ideal_sum_element
       and x IN J                             by given implication
   (2) y IN I /\ z IN J /\ !x. x IN I ==> x IN J ==> y + z IN J
       y IN I ==> y IN J                      by implication
       Hence y + z IN J                       by ideal_property
*)
val ideal_sum_sub_ideal = store_thm(
  "ideal_sum_sub_ideal",
  ``!r i j:'a ring. Ring r /\ i << r /\ j << r ==> ((i + j) << j <=> i << j)``,
  rpt strip_tac >>
  `(i + j) << r` by rw[ideal_sum_ideal] >>
  `(i + j).carrier SUBSET J <=> I SUBSET J` suffices_by metis_tac[ideal_sub_ideal] >>
  rw[ideal_sum_element, SUBSET_DEF, EQ_IMP_THM] >| [
    `x IN R /\ #0 IN J` by metis_tac[ideal_element_property, ideal_has_zero] >>
    `x = x + #0` by rw[] >>
    metis_tac[],
    rw[ideal_property]
  ]);

(* Theorem: i << r /\ p IN I ==> <p> + i = i *)
(* Proof:
   Since i << r,
         p IN I ==> p IN R    by ideal_element_property
   thus  <p> << r             by principal_ideal_ideal
   and   <p> + i << r         by ideal_sum_ideal
   By ideal_eq_ideal, only need to show:
     (<p> + i).carrier = I
   By ideal_sum_def, need to show:
   (1) x' IN <p>.carrier /\ y IN I ==> x' + y IN I
       Since ?z. z IN R /\ (x' = p * z)  by principal_ideal_element
       x' IN I by ideal_product_property (or ideal_def)
       thus x' + y IN I by ideal_property.
   (2) p IN I /\ x IN I ==> ?x' y. (x = x' + y) /\ x' IN <p>.carrier /\ y IN I
       Since x = #0 + x      by ring_add_lzero
       and #0 IN <p>.carrier by principal_ideal_ideal, ideal_has_zero
       Let x' = #0, y = x, hence true.
*)
val principal_ideal_sum_eq_ideal = store_thm(
  "principal_ideal_sum_eq_ideal",
  ``!r i:'a ring. Ring r /\ i << r ==> !p. p IN I ==> (<p> + i = i)``,
  rpt strip_tac >>
  `<p> << r` by metis_tac[principal_ideal_ideal, ideal_element_property] >>
  `(<p> + i) << r` by rw[ideal_sum_ideal] >>
  `(<p> + i).carrier = I` suffices_by metis_tac[ideal_eq_ideal] >>
  rw[ideal_sum_def, EXTENSION, EQ_IMP_THM] >| [
    `?z. z IN R /\ (x' = p * z)` by metis_tac[principal_ideal_element] >>
    metis_tac[ideal_def, ideal_property],
    `!z. z IN I ==> z IN R` by metis_tac[ideal_element_property] >>
    `x = #0 + x` by rw[] >>
    metis_tac[principal_ideal_ideal, ideal_has_zero]
  ]);

(* Theorem: i << r /\ p IN I <=> p IN R /\ (<p> + i = i) *)
(* Proof:
   If part: i << r /\ p IN I ==> p IN R /\ (<p> + i = i)
     the part: p IN I ==> p IN R, true by ideal_element_property.
     the part: p IN I ==> <p> + i = i, true by principal_ideal_sum_eq_ideal.
   Only-if part: i << r /\ p IN R /\ (<p> + i = i) ==> p IN I
     Since <p> << r                  by principal_ideal_ideal
     <p> << (<p> + i)                by ideal_sum_has_ideal
         p IN <p>.carrier            by principal_ideal_has_element
     ==> p IN (<p> + i).sum.carrier  by ideal_element
     or  p IN (<p> + i).carrier      by ideal_carriers
     ==> p IN I                      by given: <p> + i = i
*)
val principal_ideal_sum_equal_ideal = store_thm(
  "principal_ideal_sum_equal_ideal",
  ``!r i:'a ring. Ring r /\ i << r ==> (!p. p IN I <=> p IN R /\ (<p> + i = i))``,
  rw[EQ_IMP_THM] >-
  metis_tac[ideal_element_property] >-
  rw[principal_ideal_sum_eq_ideal] >>
  `<p> << r` by rw[principal_ideal_ideal] >>
  `<p> << (<p> + i)` by rw[ideal_sum_has_ideal] >>
  `p IN <p>.carrier` by rw[principal_ideal_has_element] >>
  `p IN (<p> + i).carrier` by metis_tac[ideal_element, ideal_carriers] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* Maximal Ideals                                                            *)
(* ------------------------------------------------------------------------- *)

(* Define maximal ideal *)
val ideal_maximal_def = Define `
  ideal_maximal (r:'a ring) (i:'a ring) <=>
    (i << r) /\
    (!j:'a ring. i << j /\ j << r ==> (i = j) \/ (j = r))
`;

(* use overloading *)
val _ = overload_on ("maxi", ``ideal_maximal r``);

(* ------------------------------------------------------------------------- *)
(* Irreduicables in Ring                                                     *)
(* ------------------------------------------------------------------------- *)

(* A ring element is irreducible if it is non-zero and non-unit, and its only factors are trivial. *)
val irreducible_def = Define`
  irreducible (r:'a ring) (z:'a) <=>
    (z IN R+) /\ ~(unit z) /\
    (!x y. x IN R /\ y IN R /\ (z = x * y) ==> (unit x) \/ (unit y))
`;

(* use overloading *)
val _ = overload_on ("atom", ``irreducible r``);

(*
- irreducible_def;
> val it = |- !r z. atom z <=> z IN R+ /\ z NOTIN R* /\ !x y. x IN R /\ y IN R /\ (z = x * y) ==> unit x \/ unit y : thm
*)

(* Theorem: atom p ==> p IN R *)
(* Proof:
   atom p ==> p IN R+       by irreducible_def
          ==> p IN R        by ring_nonzero_element
*)
val irreducible_element = store_thm(
  "irreducible_element",
  ``!r:'a ring. !p. atom p ==> p IN R``,
  rw[irreducible_def, ring_nonzero_element]);

(* ------------------------------------------------------------------------- *)
(* Principal Ideal Ring                                                      *)
(* ------------------------------------------------------------------------- *)

(* A principal ideal ring = a ring with all ideals being principal ideals. *)
val PrincipalIdealRing_def = Define`
  PrincipalIdealRing (r:'a ring) <=>
    (Ring r) /\
    (!(i:'a ring). i << r ==> ?p. p IN R /\ (<p> = i))
`;
(*
> val PrincipalIdealRing_def = |- !r. PrincipalIdealRing r <=> Ring r /\ !i. i << r ==> ?p. p IN R /\ (<p> = i)
*)

(* Theorem: For a principal ideal ring, an irreducible element generates a maximal ideal *)
(* Proof:
   By definitions, this is to show:
   (1) p IN R+ ==>  <p> << r,
       p IN R+ ==> p IN R           by ring_nonzero_element
       Hence true                   by principal_ideal_ideal.
   (2) <p> << j /\ j << r ==> (<p> = j) \/ (j = r)
      Since r is a principal ring, ?q. q IN R /\ (<q> = j).
      p IN R+ ==> p IN R            by ring_nonzero_element
      p IN <p>.carrier              by principal_ideal_has_element
      p IN <q>.carrier              by ideal_element
      so ?u. u IN R /\ (p = q * u)  by principal_ideal_element
      hence unit q or unit u        by ideal_maximal_def
      If unit q,
        Since q IN <q>.carrier      by principal_ideal_has_element
         unit q IN <q>.carrier
        hence <q> = j = r           by ideal_with_unit
      If unit u,
        <p> = <q>                   by principal_ideal_eq_principal_ideal.
*)
val principal_ideal_ring_ideal_maximal = store_thm(
  "principal_ideal_ring_ideal_maximal",
  ``!r:'a ring. PrincipalIdealRing r ==> !p. atom p ==> maxi <p>``,
  rw[PrincipalIdealRing_def, irreducible_def, ideal_maximal_def] >-
  rw[principal_ideal_ideal, ring_nonzero_element] >>
  `?q. q IN R /\ (<q> = j)` by rw[] >>
  `p IN R` by rw[ring_nonzero_element] >>
  `p IN <p>.carrier` by rw[principal_ideal_has_element] >>
  `p IN <q>.carrier` by metis_tac[ideal_element, principal_ideal_property] >>
  `?u. u IN R /\ (p = q * u)` by metis_tac[principal_ideal_element] >>
  `unit q \/ unit u` by rw[] >-
  metis_tac[principal_ideal_has_element, ideal_with_unit] >>
  metis_tac[principal_ideal_eq_principal_ideal]);

(* ------------------------------------------------------------------------- *)
(* Euclidean Ring                                                            *)
(* ------------------------------------------------------------------------- *)

(* A Euclidean Ring is a ring with a norm function f for division algorithm. *)
val EuclideanRing_def = Define`
  EuclideanRing (r:'a ring) (f:'a -> num) <=>
    (Ring r) /\
    (!x. (f x = 0) <=> (x = #0)) /\
    (!x y:'a. x IN R /\ y IN R /\ y <> #0 ==>
     ?q t:'a. q IN R /\ t IN R /\ (x = q * y + t) /\ f(t) < f(y))
`;

(* Theorem: EuclideanRing r ==> Ring r *)
val euclid_ring_ring = save_thm("euclid_ring_ring",
    EuclideanRing_def |> SPEC_ALL |> #1 o EQ_IMP_RULE
                   |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val euclid_ring_ring = |- !r f. EuclideanRing r f ==> Ring r : thm *)

(* Theorem: EuclideanRing r ==> !x. (f x = 0) <=> (x = #0) *)
val euclid_ring_map = save_thm("euclid_ring_map",
    EuclideanRing_def |> SPEC_ALL |> #1 o EQ_IMP_RULE
                   |> UNDISCH_ALL |> CONJUNCT2 |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val euclid_ring_map = |- !r f. EuclideanRing r f ==> !x. (f x = 0) <=> (x = #0) : thm *)

(* Theorem: EuclideanRing property:
            !x y. x IN R /\ y IN R /\ y <> #0 ==> ?q t. q IN R /\ t IN R /\ (x = q * y + t) /\ f t < f y  *)
(* Proof: by EuclideanRing_def. *)
(*
val euclid_ring_property = store_thm(
  "euclid_ring_property",
  ``!r:'a ring. !f. EuclideanRing r f ==>
   !x y. x IN R /\ y IN R /\ y <> #0 ==> ?q t. q IN R /\ t IN R /\ (x = y * q + t) /\ f t < f y``,
  rw[EuclideanRing_def]); -- Note: not by metis_tac!
*)
val euclid_ring_property = save_thm("euclid_ring_property",
    EuclideanRing_def |> SPEC_ALL |> #1 o EQ_IMP_RULE
                      |> UNDISCH_ALL |> CONJUNCTS |> last |> DISCH_ALL |> GEN_ALL);
(* > val euclid_ring_property = |- !r f.  EuclideanRing r f ==> !x y. x IN R /\ y IN R /\ y <> #0 ==>
                                ?q t. q IN R /\ t IN R /\ (x = q * y + t) /\ f t < f y : thm *)

(* Theorem: ideal generator exists:
            Ring r /\ i << r /\ i <> <#0> ==> !f. (!x. (f x = 0) <=> (x = #0))
            ==> ?p. p IN I /\ p <> #0 /\ !z. z IN I /\ f z < f p ==> z = #0        *)
(* Proof:
   Since #0 IN R,            by ring_zero_element
   <#0> << r                 by principal_ideal_ideal
   Since <#0>.carrier = {#0} by zero_ideal_sing
   i.carrier <> {#0}         by ideal_eq_ideal
   Since #0 IN I,            by ideal_has_zero
   there is x IN I, x <> #0  by ONE_ELEMENT_SING
   and f x <> 0              by condition on f
   Thus f x IN s, where s = IMAGE f I DELETE 0
   Let p IN I such that f p = MIN_SET s
   then for any z IN s,
   z IN I /\ z <> #0         by IN_IMAGE
   and  f p <= f z           by MIN_SET_LEM
*)
val ideal_gen_exists = store_thm(
  "ideal_gen_exists",
  ``!r i:'a ring. Ring r /\ i << r /\ i <> <#0> ==> !f:'a -> num. (!x. (f x = 0) <=> (x = #0))
    ==> ?p. p IN I /\ p <> #0 /\ !z. z IN I /\ z <> #0 ==> f p <= f z``,
  rpt strip_tac >>
  `<#0> << r` by rw[principal_ideal_ideal] >>
  `i.carrier <> {#0}` by metis_tac[ideal_eq_ideal, zero_ideal_sing] >>
  `?x. x IN I /\ x <> #0` by metis_tac[ONE_ELEMENT_SING, ideal_has_zero, MEMBER_NOT_EMPTY] >>
  `f x IN (IMAGE f I)` by rw[] >>
  `f x <> 0` by rw[] >>
  `IMAGE f I DELETE 0 <> {}` by metis_tac[IN_DELETE, MEMBER_NOT_EMPTY] >>
  qabbrev_tac `s = IMAGE f I DELETE 0` >>
  `MIN_SET s IN s /\ !x. x IN s ==> MIN_SET s <= x` by metis_tac[MIN_SET_LEM] >>
  `?p. p IN I /\ p <> #0 /\ (f p = MIN_SET s)` by metis_tac[IN_IMAGE, IN_DELETE] >>
  metis_tac[IN_IMAGE, IN_DELETE]);

(* Apply Skolemization *)
val lemma = prove(
  ``!r i f. ?p. Ring r /\ i << r /\ i <> <#0> /\ (!x. (f x = 0) <=> (x = #0))
       ==> p IN I /\ p <> #0 /\ !z. z IN I /\ z <> #0 ==> f p <= f z``,
  metis_tac[ideal_gen_exists]);
(*
- SKOLEM_THM;
> val it = |- !P. (!x. ?y. P x y) <=> ?f. !x. P x (f x) : thm
*)
(* Define ideal generator *)
(*
- SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma;
> val it = |- ?f. !r i f'.
           Ring r /\ i << r /\ i <> <#0> /\ (!x. (f' x = 0) <=> (x = #0)) ==>
           f r i f' IN I /\ f r i f' <> #0 /\ !z. z IN I /\ z <> #0 ==> f' (f r i f') <= f' z : thm
*)
val ideal_gen_def = new_specification(
    "ideal_gen_def",
    ["ideal_gen"],
    SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma
    |> CONV_RULE (RENAME_VARS_CONV ["h", "r", "i", "f"])); (* replace f r i f' by h r i f *)
(* val ideal_gen_def = |- !r i f. Ring r /\ i << r /\ i <> <#0> /\ (!x. (f x = 0) <=> (x = #0)) ==>
        ideal_gen r i f IN I /\ ideal_gen r i f <> #0 /\ !z. z IN I /\ z <> #0 ==> f (ideal_gen r i f) <= f z : thm *)

(* Theorem: property of ideal generator:
            !z. z IN I ==> (f z < f (ideal_gen r i f) <=> z = #0) *)
(* Proof:
   If part: f z < f (ideal_gen r i f) ==> z = #0
     By contradicton, assume z <> #0,
     then f (ideal_gen r i f) <= f z   by ideal_gen_def
     which contradicts f z < f (ideal_gen r i f).
   Only-if part: z = #0 ==> f z < f (ideal_gen r i f)
     (ideal_gen r i f) <> #0           by ideal_gen_def
     hence f (ideal_gen r i f) <> 0    by given f: f x = 0 <=> x = #0
     Since f #0 = 0                    by given f above
     This is true.
*)
val ideal_gen_minimal = store_thm(
  "ideal_gen_minimal",
  ``!r i:'a ring. Ring r /\ i << r /\ i <> <#0> ==> !f:'a -> num. (!x. (f x = 0) <=> (x = #0))
   ==> !z. z IN I ==> (f z < f (ideal_gen r i f) <=> (z = #0))``,
  rw[ideal_gen_def, EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `f (ideal_gen r i f) <= f z` by metis_tac[ideal_gen_def] >>
    decide_tac,
    `(ideal_gen r i f) <> #0` by metis_tac[ideal_gen_def] >>
    `f (ideal_gen r i f) <> 0 /\ (f #0 = 0)` by metis_tac[] >>
    decide_tac
  ]);

(* Theorem: EuclideanRing f r ==> PrincipalIdealRing r *)
(* Proof:
   First,
   EuclideanRing r f ==> Ring r by EuclideanRing_def
   By PrincipalIdealRing_def, this is to show:
     !i. i << r ==> ?p. p IN R /\ (<p> = i)
   If i = <#0>, it is generated by #0.
   If i <> <#0>,
   Let p = ideal_gen r i f
   Then p IN I /\ p <> #0       by ideal_gen_def
   and for any x IN I, x IN R   by ideal_element_property
   By EuclideanRing_Def,
   there exists y IN R, t IN R
   such that  x = y * p + t     with (f t) < (f p)
   or  x = p * y + t            by ring_mult_comm
   Since p * y IN I             by ideal_product_property
   t = x - p * y IN I           by ideal_has_diff
   Thus t = #0                  by ideal_gen_minimal
   or x = p * y,
   so x IN <p>.carrier          by principal_ideal_element
   i.e. I SUBSET <p>.carrier    by SUBSET_DEF
   On the other hand,
   p IN I ==> <p> << i          by ideal_has_principal_ideal
   so !x IN <p>.carrier ==> x IN I   by ideal_element
   i.e. <p>.carrier SUBSET I    by SUBSET_DEF
   so <p>.carrier = I           by SUBSET_ANTISYM
   Hence <p> = i                by ideal_eq_ideal.
*)
val euclid_ring_principal_ideal_ring = store_thm(
  "euclid_ring_principal_ideal_ring",
  ``!r:'a ring. !f. EuclideanRing r f ==> PrincipalIdealRing r``,
  rw[EuclideanRing_def, PrincipalIdealRing_def] >>
  Cases_on `i = <#0>` >-
  metis_tac[ring_zero_element] >>
  `!z. z IN I ==> z IN R` by metis_tac[ideal_element_property] >>
  `ideal_gen r i f IN I /\ ideal_gen r i f <> #0` by metis_tac[ideal_gen_def] >>
  `!z. z IN I ==> (f z < f (ideal_gen r i f) <=> (z = #0))` by rw[ideal_gen_minimal] >>
  qabbrev_tac `p = ideal_gen r i f` >>
  `<p> << r` by rw[principal_ideal_ideal] >>
  qexists_tac `p` >>
  rw[] >>
  `<p>.carrier = I` suffices_by metis_tac[ideal_eq_ideal] >>
  rw[principal_ideal_def, coset_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[ideal_product_property] >>
  `?q t. q IN R /\ t IN R /\ (x = q * p + t) /\ f t < f p` by rw[] >>
  `x = p * q + t` by rw[ring_mult_comm] >>
  `p * q IN I` by metis_tac[ideal_product_property] >>
  `t = x - p * q` by metis_tac[ring_sub_eq_add] >>
  `t IN I` by rw[ideal_has_diff] >>
  `t = #0` by metis_tac[ideal_gen_minimal] >>
  `x = p * q` by rw[] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* Ideal under Ring Homomorphism                                             *)
(* ------------------------------------------------------------------------- *)

(* Homomorphic image of ideal *)
(*
val homo_ideal_def = Define`
  homo_ideal (f:'a -> 'b) (r:'a ring) (i:'a ring) =
    <| carrier := IMAGE f I;
           sum := <| carrier := IMAGE f I; op := image_op i.sum f; id := f #0 |>;
          prod := <| carrier := IMAGE f I; op := image_op i.prod f; id := f #1 |>
     |>
`;
*)
val homo_ideal_def = Define`
  homo_ideal (f:'a -> 'b) (r:'a ring) (s:'b ring) (i:'a ring) =
    <| carrier := IMAGE f I;
           sum := <| carrier := IMAGE f I; op := s.sum.op; id := f #0 |>;
          prod := <| carrier := IMAGE f I; op := s.prod.op; id := f #1 |>
     |>
`;

(* Theorem: RingHomo f r s /\ i << r ==> Group (homo_ideal f r s i).sum *)
(* Proof: checking group axioms:
   (1) x IN IMAGE f I /\ y IN IMAGE f I ==> s.sum.op x y IN IMAGE f I
       Let p = CHOICE (preimage f I x),
           q = CHOICE (preimage f I y)
       then p IN I /\ f p = x    by preimage_choice_property
        and q IN I /\ f q = y    by preimage_choice_property
       Since  p + q IN I         by ideal_property
         f (p + q) IN IMAGE f I
       but f (p + q)
       = s.sum.op (f p) (f q)    by RingHomo_def and GroupHomo_def.
   (2) x IN IMAGE f I /\ y IN IMAGE f I /\ z IN IMAGE f I ==> s.sum.op (s.sum.op x y) z = s.sum.op x (s.sum.op y z)
       Let p = CHOICE (preimage f I x)
       Let q = CHOICE (preimage f I y)
       Let t = CHOICE (preimage f I z)
       Then p IN I /\ (f p = x)    by preimage_choice_property
            q IN I /\ (f q = y)    by preimage_choice_property
            t IN I /\ (f t = z)    by preimage_choice_property
       Since !z. z IN I ==> z IN R   by ideal_element_property
       and   !z. z IN R ==> f z IN s.carrier by RingHomo_def
       This is true by ring_add_assoc.
   (3) f #0 IN IMAGE f I
       Since #O IN I    by ideal_has_zero, this is true.
   (4) s.sum.op (f #0) x = x
       Let p = CHOICE (preimage f I x)
       then p IN I /\ f p = x    by preimage_choice_property
         s.sum.op (f #0) x
       = f (#0 + p)              by RingHomo_def, GroupHomo_def
       = f p = x                 by ring_add_lzero
   (5) ?y. y IN IMAGE f I /\ (s.sum.op y x = f #0)
       Let p = CHOICE (preimage f I x)
       Then   p IN I /\ (f p = x)       by preimage_choice_property
       Hence    -p IN I                 by ideal_has_neg
       and  f (-p) IN IMAGE f I
       Let y = f (-p), then
         s.sum.op y x
       = s.sum.op (f (-p)) (f p)
       = f (-p + p)                     by RingHomo_def, GroupHomo_def
       = f #0                           by ring_add_lneg
*)
val ring_homo_ideal_group = store_thm(
  "ring_homo_ideal_group",
  ``!(r:'a ring) (s:'b ring) f.  Ring r /\ Ring s /\ RingHomo f r s ==> !i. i << r ==> Group (homo_ideal f r s i).sum``,
  rpt strip_tac >>
  `r.sum.carrier = R` by rw[] >>
  `!z. z IN I ==> z IN R` by metis_tac[ideal_element_property] >>
  `i.sum.carrier = I` by metis_tac[ideal_def] >>
  `i.sum.op = r.sum.op` by metis_tac[ideal_ops] >>
  `GroupHomo f r.sum s.sum` by metis_tac[RingHomo_def] >>
  `!x y. x IN R /\ y IN R ==> (f (x + y) = s.sum.op (f x) (f y))` by metis_tac[GroupHomo_def] >>
  `!z. z IN R ==> f z IN s.carrier` by metis_tac[RingHomo_def] >>
  `s.sum.id = f #0` by rw[ring_homo_zero] >>
  rw_tac std_ss[homo_ideal_def, group_def_alt] >| [
    qabbrev_tac `p = CHOICE (preimage f I x)` >>
    qabbrev_tac `q = CHOICE (preimage f I y)` >>
    `p IN I /\ (f p = x)` by rw[preimage_choice_property, Abbr`p`] >>
    `q IN I /\ (f q = y)` by rw[preimage_choice_property, Abbr`q`] >>
    `p + q IN I` by rw[ideal_property] >>
    `f (p + q) IN IMAGE f I` by rw[] >>
    metis_tac[],
    qabbrev_tac `p = CHOICE (preimage f I x)` >>
    qabbrev_tac `q = CHOICE (preimage f I y)` >>
    qabbrev_tac `t = CHOICE (preimage f I z)` >>
    `p IN I /\ (f p = x)` by rw[preimage_choice_property, Abbr`p`] >>
    `q IN I /\ (f q = y)` by rw[preimage_choice_property, Abbr`q`] >>
    `t IN I /\ (f t = z)` by rw[preimage_choice_property, Abbr`t`] >>
    rw[ring_add_assoc],
    rw[ideal_has_zero],
    qabbrev_tac `p = CHOICE (preimage f I x)` >>
    `p IN I /\ (f p = x)` by rw[preimage_choice_property, Abbr`p`] >>
    metis_tac[ring_add_lzero],
    qabbrev_tac `p = CHOICE (preimage f I x)` >>
    `p IN I /\ (f p = x)` by rw[preimage_choice_property, Abbr`p`] >>
    `-p IN I` by rw[ideal_has_neg] >>
    `f (-p) IN IMAGE f I` by rw[] >>
    qexists_tac `f (-p)` >>
    metis_tac[ring_add_lneg]
  ]);

(* Theorem: RingHomo f r s /\ i << r ==> (homo_ideal f r s i).sum <= s.sum *)
(* Proof: by Subgroup_def, this is to show:
   (1) Group (homo_ideal f r s i).sum
       True by ring_homo_ideal_group.
   (2) (homo_ideal f r s i).sum.carrier SUBSET s.carrier
       i.e. to show: IMAGE f I SUBSET s.carrier
       Since !x. x IN I ==> x IN R            by ideal_element_property
       and   !x. x IN R ==> f x IN s.carrier  by RingHomo_def
       This is true by SUBSET_DEF.
   (3) (homo_ideal f r s i).sum.op = s.sum.op
*)
val ring_homo_ideal_subgroup = store_thm(
  "ring_homo_ideal_subgroup",
  ``!(r:'a ring) (s:'b ring) f.  Ring r /\ Ring s /\ RingHomo f r s ==> !i. i << r ==> (homo_ideal f r s i).sum <= s.sum``,
  rw[Subgroup_def] >| [
    rw[ring_homo_ideal_group],
    rw[homo_ideal_def] >>
    rw[SUBSET_DEF] >>
    metis_tac[ideal_element_property, RingHomo_def],
    rw[homo_ideal_def]
  ]);

(* Theorem: Ring homomorphic image of an ideal is still an ideal of the target ring, if the map is surjective.
            RingHomo f r s /\ SURJ f R s.carrier ==> !i. i << r ==> (homo_ideal f r s i) << s  *)
(* Proof: by ideal_def, this is to show:
   (1) (homo_ideal f r s i).sum <= s.sum
       True by ring_homo_ideal_subgroup.
   (2) (homo_ideal f r s i).sum.carrier = (homo_ideal f r s i).carrier
       True by homo_ideal_def.
   (3) (homo_ideal f r s i).prod.carrier = (homo_ideal f r s i).carrier
       True by homo_ideal_def.
   (4) (homo_ideal f r s i).prod.op = s.prod.op
       True by homo_ideal_def.
   (5) (homo_ideal f r s i).prod.id = s.prod.id
       True by homo_ideal_def, ring_homo_one.
   -- so far, no need for surjective, but the next two require surjective.
   (6) x IN (homo_ideal f r s i).carrier /\ y IN s.carrier ==> s.prod.op x y IN (homo_ideal f r s i).carrier
       or, by homo_ideal_def, this is to show:
       x IN IMAGE f I /\ y IN s.carrier ==> s.prod.op x y IN IMAGE f I
       y IN s.carrier = IMAGE f R   by IMAGE_SURJ, due to SURJ f R s.carrier
       Let p = CHOICE (preimage f I x),
           q = CHOICE (preimage f R y)
       Then  p IN I /\ (f p = x)   by preimage_choice_property
             q IN R /\ (f q = y)   by preimage_choice_property
         s.prod.op x y
       = s.prod.op (f p) (f q)
       = f (p * q)                 by RingHomo_def, MonoidHomo_def
       Since  p * q IN I           by ideal_def
       f (p * q) IN IMAGE f I, hence true
   (7) x IN (homo_ideal f r s i).carrier /\ y IN s.carrier ==> s.prod.op y x IN (homo_ideal f r s i).carrier
       Same as (7), apply ring_mult_comm.
*)
val ring_homo_ideal_ideal = store_thm(
  "ring_homo_ideal_ideal",
  ``!(r:'a ring) (s:'b ring) f. Ring r /\ Ring s /\ RingHomo f r s /\ SURJ f R s.carrier ==>
     !i. i << r ==> (homo_ideal f r s i) << s``,
  rpt strip_tac >>
  `r.prod.carrier = R` by metis_tac[Ring_def] >>
  `MonoidHomo f r.prod s.prod` by metis_tac[RingHomo_def] >>
  `!x y. x IN R /\ y IN R ==> (f (x * y) = s.prod.op (f x) (f y))` by metis_tac[MonoidHomo_def] >>
  `!z. z IN R ==> f z IN s.carrier` by metis_tac[RingHomo_def] >>
  `(homo_ideal f r s i).carrier = IMAGE f I` by rw[homo_ideal_def] >>
  `IMAGE f R = s.carrier` by rw[GSYM IMAGE_SURJ] >>
  rw_tac std_ss[ideal_def] >-
  rw[ring_homo_ideal_subgroup] >-
  rw[homo_ideal_def] >-
  rw[homo_ideal_def] >-
  rw[homo_ideal_def] >-
  rw[homo_ideal_def, ring_homo_one] >-
 (`y IN IMAGE f R` by metis_tac[] >>
  qabbrev_tac `p = CHOICE (preimage f I x)` >>
  qabbrev_tac `q = CHOICE (preimage f R y)` >>
  `p IN I /\ (f p = x)` by rw[preimage_choice_property, Abbr`p`] >>
  `q IN R /\ (f q = y)` by rw[preimage_choice_property, Abbr`q`] >>
  `s.prod.op x y = f (p * q)` by metis_tac[ideal_element_property] >>
  `p * q IN I` by metis_tac[ideal_def] >>
  metis_tac[IN_IMAGE]) >>
  `y IN IMAGE f R` by metis_tac[] >>
  qabbrev_tac `p = CHOICE (preimage f I x)` >>
  qabbrev_tac `q = CHOICE (preimage f R y)` >>
  `p IN I /\ (f p = x)` by rw[preimage_choice_property, Abbr`p`] >>
  `q IN R /\ (f q = y)` by rw[preimage_choice_property, Abbr`q`] >>
  `s.prod.op y x = f (q * p)` by metis_tac[ideal_element_property] >>
  `q * p IN I` by metis_tac[ideal_def] >>
  metis_tac[IN_IMAGE]);

(* ------------------------------------------------------------------------- *)
(* Ring Binomial Documentation                                               *)
(* ------------------------------------------------------------------------- *)
(*
   Overloading:
   rlist    = ring_list r
   rsum     = ring_sum r
   rfun     = ring_fun r
*)
(* Definitions and Theorems (# are exported):

   List from elements in Ring:
#  ring_list_def         |- (!r. rlist [] <=> T) /\ !r h t. rlist (h::t) <=> h IN R /\ rlist t
   ring_list_nil         |- !r. rlist [] <=> T
   ring_list_cons        |- !r h t. rlist (h::t) <=> h IN R /\ rlist t
   ring_list_front_last  |- !s. rlist (FRONT s) /\ LAST s IN R ==> rlist s
   ring_list_SNOC        |- !x s. rlist (SNOC x s) <=> x IN R /\ rlist s

   Summation in Ring:
#  ring_sum_def      |- (!r. rsum [] = #0) /\ !r h t. rsum (h::t) = h + rsum t
   ring_sum_nil      |- !r. rsum [] = #0
   ring_sum_cons     |- !r h t. rsum (h::t) = h + rsum t
#  ring_sum_element  |- !r. Ring r ==> !s. rlist s ==> rsum s IN R
   ring_sum_sing     |- !r. Ring r ==> !x. x IN R ==> (rsum [x] = x)
   ring_sum_append   |- !r. Ring r ==> !s t. rlist s /\ rlist t ==> (rsum (s ++ t) = rsum s + rsum t)
   ring_sum_mult     |- !r. Ring r ==> !k s. k IN R /\ rlist s ==> (k * rsum s = rsum (MAP (\x. k * x) s))
   ring_sum_mult_ladd  |- !r. Ring r ==> !m n s. m IN R /\ n IN R /\ rlist s ==>
                          ((m + n) * rsum s = rsum (MAP (\x. m * x) s) + rsum (MAP (\x. n * x) s))
   ring_sum_SNOC     |- !r. Ring r ==> !k s. k IN R /\ rlist s ==> (rsum (SNOC k s) = rsum s + k)

   Function giving elements in Ring:
#  ring_fun_def     |- !r f. rfun f <=> !x. f x IN R
   ring_fun_add     |- !r. Ring r ==> !a b. rfun a /\ rfun b ==> rfun (\k. a k + b k)
   ring_fun_genlist |- !f. rfun f ==> !n. rlist (GENLIST f n)
   ring_fun_map     |- !f l. rfun f ==> rlist (MAP f l)
   ring_fun_from_ring_fun      |- !r. Ring r ==> !f. rfun f ==> !x. x IN R ==> rfun (\j. f j * x ** j)
   ring_fun_from_ring_fun_exp  |- !r. Ring r ==> !f. rfun f ==> !x. x IN R ==>
                                  !n. rfun (\j. (f j * x ** j) ** n)
   ring_list_gen_from_ring_fun |- !r. Ring r ==> !f. rfun f ==> !x. x IN R ==>
                                  !n. rlist (GENLIST (\j. f j * x ** j) n)
   ring_list_from_genlist_ring_fun   |- !r f. rfun f ==> !n g. rlist (GENLIST (f o g) n)
   ring_list_from_genlist            |- !r f. rfun f ==> !n. rlist (GENLIST f n)

   Ring Sum Involving GENLIST:
   ring_sum_fun_zero           |- !r. Ring r ==> !f. rfun f ==> !n. (!k. 0 < k /\ k < n ==>
                                  (f k = #0)) ==> (rsum (MAP f (GENLIST SUC (PRE n))) = #0)

   ring_sum_decompose_first |- !r f n. rsum (GENLIST f (SUC n)) = f 0 + rsum (GENLIST (f o SUC) n)
   ring_sum_decompose_last  |- !r. Ring r ==> !f n. rfun f ==> (rsum (GENLIST f (SUC n)) = rsum (GENLIST f n) + f n)
   ring_sum_decompose_first_last  |- !r. Ring r ==> !f n. rfun f /\ 0 < n ==>
                                    (rsum (GENLIST f (SUC n)) = f 0 + rsum (GENLIST (f o SUC) (PRE n)) + f n)
   ring_sum_genlist_add       |- !r. Ring r ==> !a b. rfun a /\ rfun b ==>
                              !n. rsum (GENLIST a n) + rsum (GENLIST b n) = rsum (GENLIST (\k. a k + b k) n)
   ring_sum_genlist_append    |- !r. Ring r ==> !a b. rfun a /\ rfun b ==>
                              !n. rsum (GENLIST a n ++ GENLIST b n) = rsum (GENLIST (\k. a k + b k) n)
   ring_sum_genlist_sum     |- !r. Ring r ==> !f. rfun f ==>
                     !n m. rsum (GENLIST f (n + m)) = rsum (GENLIST f m) + rsum (GENLIST (\k. f (k + m)) n)
   ring_sum_genlist_const   |- !r. Ring r ==> !x. x IN R ==> !n. rsum (GENLIST (K x) n) = ##n * x

   Ring Binomial Theorem:
   ring_binomial_genlist_index_shift  |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
                            !n. GENLIST ((\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) o SUC) n =
                                GENLIST (\k. ##(binomial n (SUC k)) * x ** (n - k) * y ** SUC k) n
   ring_binomial_index_shift  |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
                              !n. (\k. ##(binomial (SUC n) k) * x ** (SUC n - k) * y ** k) o SUC =
                                  (\k. ##(binomial (SUC n) (SUC k)) * x ** (n - k) * y ** SUC k)
   ring_binomial_term_merge_x |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
     !n. (\k. x * k) o (\k. ##(binomial n k) * x ** (n - k) * y ** k) = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k)
   ring_binomial_term_merge_y |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
     !n. (\k. y * k) o (\k. ##(binomial n k) * x ** (n - k) * y ** k) = (\k. ##(binomial n k) * x ** (n - k) * y ** SUC k)
   ring_binomial_thm          |- !r. Ring r ==> !x y. x IN R /\ y IN R ==>
     !n. (x + y) ** n = rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** k) (SUC n))

   Ring with prime characteristic:
   ring_char_prime        |- !r. Ring r ==> (prime (char r) <=>
                             1 < char r /\ !k. 0 < k /\ k < char r ==> (##(binomial (char r) k) = #0))
   ring_freshman_thm      |- !r. Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
                             ((x + y) ** char r = x ** char r + y ** char r)
   ring_freshman_all      |- !r. Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
                             !n. (x + y) ** char r ** n = x ** char r ** n + y ** char r ** n
   ring_freshman_thm_sub  |- !r. Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
                             ((x - y) ** char r = x ** char r - y ** char r)
   ring_freshman_all_sub  |- !r. Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
                             !n. (x - y) ** char r ** n = x ** char r ** n - y ** char r ** n
   ring_fermat_thm        |- !r. Ring r /\ prime (char r) ==> !n. (##n) ** (char r) = (##n)
   ring_fermat_all        |- !r. Ring r /\ prime (char r) ==> !n k. ##n ** char r ** k = ##n
   ring_sum_freshman_thm  |- !r. Ring r /\ prime (char r) ==> !f. rfun f ==> !x. x IN R ==>
                             !n. rsum (GENLIST (\j. f j * x ** j) n) ** char r =
                                 rsum (GENLIST (\j. (f j * x ** j) ** char r) n)
   ring_sum_freshman_all  |- !r. Ring r /\ prime (char r) ==> !f. rfun f ==> !x. x IN R ==>
                             !n k. rsum (GENLIST (\j. f j * x ** j) n) ** char r ** k =
                                   rsum (GENLIST (\j. (f j * x ** j) ** char r ** k) n)
   ring_char_prime_endo   |- !r. Ring r /\ prime (char r) ==> RingEndo (\x. x ** char r) r
*)

(*
binomial_thm:
!n x y. (x + y)**n = rsum (GENLIST (\k. (binomial n k)* x**(n-k) * y**k) (SUC n))
*)

(* ------------------------------------------------------------------------- *)
(* List from elements in Ring                                                *)
(* ------------------------------------------------------------------------- *)

(* Ring element list. *)
val ring_list_def = Define`
  (ring_list (r:'a ring) [] <=> T) /\
  (ring_list (r:'a ring) ((h:'a)::(t:'a list)) <=> h IN R /\ (ring_list r t))
`;
val _ = overload_on ("rlist", ``ring_list r``);

(* export simple definition. *)
val _ = export_rewrites ["ring_list_def"];

(* Theorem: rlist [] <=> T *)
val ring_list_nil = save_thm("ring_list_nil", ring_list_def |> CONJUNCT1);
(* > val ring_list_nil = |- !r. rlist [] <=> T : thm *)

(* Theorem: rlist (h::t) <=> h IN R /\ rlist t *)
val ring_list_cons = save_thm("ring_list_cons", ring_list_def |> CONJUNCT2);
(* > val ring_list_cons = |- !r h t. rlist (h::t) <=> h IN R /\ rlist t : thm *)


(* Theorem: rlist (FRONT l) /\ LAST l IN R ==> rlist l *)
(* Proof: by induction on s.
   Base case: rlist (FRONT []) ==> LAST [] IN R ==> rlist []
     true since rlist []   by ring_list_nil.
   Step case: rlist (FRONT s) ==> LAST s IN R ==> rlist s ==>
              !h. rlist (FRONT (h::s)) ==> LAST (h::s) IN R ==> rlist (h::s)
     If s = [],
        FRONT (h::[]) = [], LAST (h::[]) = h,   by FRONT_CONS and LAST_CONS,
        hence rlist [] /\ h IN R, hence rlist (h::[])  by ring_list_cons.
     If s <> [], s = h'::t
        FRONT (h::s) = h::FRONT s, LAST (h::s) = LAST s, by FRONT_CONS and LAST_CONS,
        hence rlist (h::FRONT s) /\ LAST s IN R,
           or h IN R /\ rlist (FRONT s) /\ LAST s IN R   by ring_list_cons
           or h IN R /\ rlist s                          by induction hypothesis
           hence rlist (h::s)                            by ring_list_cons
*)
val ring_list_front_last = store_thm(
  "ring_list_front_last",
  ``!s. rlist (FRONT s) /\ LAST s IN R ==> rlist s``,
  rpt strip_tac >>
  Induct_on `s` >-
  rw[] >>
  metis_tac[FRONT_CONS, LAST_CONS, ring_list_def, list_CASES]);

(* Theorem: !x s. rlist (SNOC x s) <=> x IN R /\ rlist s *)
(* Proof:
   By induction on s.
   Base case: rlist (SNOC x []) <=> x IN R /\ rlist []
          rlist (SNOC x [])
      <=> rlist [x]           by SNOC
      <=> x IN R /\ rlist []  by ring_list_cons
   Step case: rlist (SNOC x s) <=> x IN R /\ rlist s ==>
              !h. rlist (SNOC x (h::s)) <=> x IN R /\ rlist (h::s)
          rlist (SNOC x (h::s))
      <=> rlist (h::SONC x s)          by SNOC
      <=> h IN R /\ rlist (SNOC x s)   by ring_list_cons
      <=> h IN R /\ x IN R /\ rlist s  by induction hypothesis
      <=> x IN R /\ rlist (h::s)       by ring_list_cons
*)
val ring_list_SNOC = store_thm(
  "ring_list_SNOC",
  ``!x s. rlist (SNOC x s) <=> x IN R /\ rlist s``,
  rpt strip_tac >>
  Induct_on `s` >-
  rw[] >>
  rw[] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* Summation in Ring                                                         *)
(* ------------------------------------------------------------------------- *)

(* Summation in a Ring. *)
val ring_sum_def = Define`
  (ring_sum (r:'a ring) [] = #0) /\
  (ring_sum (r:'a ring) ((h:'a)::(t:'a list)) = h + (ring_sum r t))
`;
val _ = overload_on ("rsum", ``ring_sum r``);

(* export simple definition. *)
val _ = export_rewrites ["ring_sum_def"];

(* Theorem: rsum [] = #0 *)
val ring_sum_nil = save_thm("ring_sum_nil", ring_sum_def |> CONJUNCT1);
(* > val ring_sum_nil = |- !r. rsum [] = #0 : thm *)

(* Theorem: rsum (h::t)= h + rsum t *)
val ring_sum_cons = save_thm("ring_sum_cons", ring_sum_def |> CONJUNCT2);
(* > val ring_sum_cons = |- !r h t. rsum (h::t) = h + rsum t : thm *)

(* Theorem: rsum s IN R *)
(* Proof: by induction on s.
   Base case: rlist [] ==> rsum [] IN R
      true by ring_sum_nil, ring_zero_element.
   Step case: rlist s ==> rsum s IN R ==> !h. rlist (h::s) ==> rsum (h::s) IN R
      rlist (h::s) ==> h IN R /\ rlist s      by ring_list_cons
      since  ring_sum(h::s) = h + rsum s      by ring_sum_cons
      with h IN R and rlist s ==> rsum s IN R by induction hypothesis
      true by ring_add_element
*)
val ring_sum_element = store_thm(
  "ring_sum_element",
  ``!r:'a ring. Ring r ==> !s. rlist s ==> rsum s IN R``,
  rpt strip_tac >>
  Induct_on `s` >>
  rw[]);

val _ = export_rewrites ["ring_sum_element"];

(* Theorem: rsum [x] = x *)
(* Proof:
     rsum [x]
   = x + rsum []    by ring_sum_cons
   = x + #0         by ring_sum_nil
   = x              by ring_add_rzero
*)
val ring_sum_sing = store_thm(
  "ring_sum_sing",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> (rsum [x] = x)``,
  rw[]);

(* Theorem: rsum (s ++ t) = rsum s + rsum t *)
(* Proof: by induction on s
   Base case: rlist [] ==> (rsum ([] ++ t) = rsum [] + rsum t)
     rsum ([] ++ t)
   = rsum t                   by APPEND
   = #0 + rsum t              by ring_add_lzero
   = rsum [] + rsum t   by ring_sum_nil
   Step case: rlist s /\ rlist t ==> (rsum (s ++ t) = rsum s + rsum t) ==>
              rlist (h::s) ==> (rsum (h::s ++ t) = rsum (h::s) + rsum t)
     rsum (h::s ++ t)
   = rsum (h::(s ++ t))       by APPEND
   = h + rsum (s ++ t)        by ring_sum_cons, h IN R by ring_list_cons
   = h + (rsum s + rsum t)    by induction hypothesis
   = (h + rsum s) + rsum t    by ring_add_assoc
   = rsum (h::s) + rsum t     by ring_sum_cons
*)
val ring_sum_append = store_thm(
  "ring_sum_append",
  ``!r:'a ring. Ring r ==> !s t. rlist s /\ rlist t ==> (rsum (s ++ t) = rsum s + rsum t)``,
  rpt strip_tac >>
  Induct_on `s` >>
  rw[ring_add_assoc]);

(* Theorem: constant multiplication: k * rsum s = rsum (MAP (\x. k*x) s))  *)
(* Proof: by induction on s
   Base case: k * rsum [] = rsum (MAP (\x. k * x) [])
   LHS = k * rsum []
       = k * #0          by ring_sum_nil
       = #0              by ring_mult_rzero
   RHS = rsum (MAP (\x. k * x) [])
       = rsum []         by MAP
       = #0              by ring_sum_nil
       = LHS
   Step case: rlist s ==> (k * rsum s = rsum (MAP (\x. k * x) s)) ==>
              !h. rlist (h::s) ==> (k * rsum (h::s) = rsum (MAP (\x. k * x) (h::s)))
   LHS = k * rsum (h::s)
       = k * (h + rsum s)     by ring_sum_cons
       = k * h + k * rsum s   by ring_mult_radd
       = k * h + rsum (MAP (\x. k * x) s)   by induction hypothesis
   RHS = rsum (MAP (\x. k * x) (h::s))
       = rsum ((\x. k * x) h :: MAP (\x. k * x) s)  by MAP
       = (\x. k * x) h + rsum (MAP (\x. k * x) s)   by ring_sum_cons
       = k * h + rsum (MAP (\x. k * x) s
       = LHS
*)
val ring_sum_mult = store_thm(
  "ring_sum_mult",
  ``!r:'a ring. Ring r ==> !k s. k IN R /\ rlist s ==> (k * rsum s = rsum (MAP (\x. k*x) s))``,
  rpt strip_tac >>
  Induct_on `s` >>
  rw[]);

(* Theorem: (m+n) * rsum s = rsum (MAP (\x. m*x) s) + rsum (MAP (\x. n*x) s)  *)
(* Proof:
    (m + n) * rsum s
  = m * rsum s + n * rsum s                          by ring_mult_ladd
  = rsum (MAP (\x. m*x) s) + rsum (MAP (\x. n*x) s)  by ring_sum_mult
*)
val ring_sum_mult_ladd = store_thm(
  "ring_sum_mult_ladd",
  ``!r:'a ring. Ring r ==> !m n s. m IN R /\ n IN R /\ rlist s ==>
       ((m + n) * rsum s = rsum (MAP (\x. m*x) s) + rsum (MAP (\x. n*x) s))``,
  rw[ring_sum_mult, ring_mult_ladd]);

(*
- EVAL ``GENLIST I 4``;
> val it = |- GENLIST I 4 = [0; 1; 2; 3] : thm
- EVAL ``GENLIST SUC 4``;
> val it = |- GENLIST SUC 4 = [1; 2; 3; 4] : thm
- EVAL ``GENLIST (\k. binomial 4 k) 5``;
> val it = |- GENLIST (\k. binomial 4 k) 5 = [1; 4; 6; 4; 1] : thm
- EVAL ``GENLIST (\k. binomial 5 k) 6``;
> val it = |- GENLIST (\k. binomial 5 k) 6 = [1; 5; 10; 10; 5; 1] : thm
- EVAL ``GENLIST (\k. binomial 10 k) 11``;
> val it = |- GENLIST (\k. binomial 10 k) 11 = [1; 10; 45; 120; 210; 252; 210; 120; 45; 10; 1] : thm
*)

(* Theorems on GENLIST:

- GENLIST;
> val it = |- (!f. GENLIST f 0 = []) /\
               !f n. GENLIST f (SUC n) = SNOC (f n) (GENLIST f n) : thm
- NULL_GENLIST;
> val it = |- !n f. NULL (GENLIST f n) <=> (n = 0) : thm
- GENLIST_CONS;
> val it = |- GENLIST f (SUC n) = f 0::GENLIST (f o SUC) n : thm
- EL_GENLIST;
> val it = |- !f n x. x < n ==> (EL x (GENLIST f n) = f x) : thm
- EXISTS_GENLIST;
> val it = |- !n. EXISTS P (GENLIST f n) <=> ?i. i < n /\ P (f i) : thm
- EVERY_GENLIST;
> val it = |- !n. EVERY P (GENLIST f n) <=> !i. i < n ==> P (f i) : thm
- MAP_GENLIST;
> val it = |- !f g n. MAP f (GENLIST g n) = GENLIST (f o g) n : thm
- GENLIST_APPEND;
> val it = |- !f a b. GENLIST f (a + b) = GENLIST f b ++ GENLIST (\t. f (t + b)) a : thm
- HD_GENLIST;
> val it = |- HD (GENLIST f (SUC n)) = f 0 : thm
- TL_GENLIST;
> val it = |- !f n. TL (GENLIST f (SUC n)) = GENLIST (f o SUC) n : thm
- HD_GENLIST_COR;
> val it = |- !n f. 0 < n ==> (HD (GENLIST f n) = f 0) : thm
- GENLIST_FUN_EQ;
> val it = |- !n f g. (GENLIST f n = GENLIST g n) <=> !x. x < n ==> (f x = g x) : thm

*)

(* Theorem: rsum (SNOC h s) = (rsum s) + h *)
(* Proof: by induction on s.
   Base case: (rsum (SNOC k []) = rsum [] + k)
      rsum (SNOC k [])
    = rsum [k]            by SNOC
    = k + #0              by ring_sum_cons, ring_sum_nil
    = k                   by ring_add_rzero
    = #0 + k              by ring_add_lzero
    = rsum [] + k         by ring_sum_nil
   Step case: rlist s ==> (rsum (SNOC k s) = rsum s + k) ==>
              !h. rlist (h::s) ==> (rsum (SNOC k (h::s)) = rsum (h::s) + k)
     rsum (SNOC k (h::s))
   = rsum (h::SNOC k s)   by SNOC
   = h + rsum (SNOC k s)  by ring_sum_cons
   = h + (rsum s + k)     by induction hypothesis
   = (h + rsum s) + k     by ring_add_assoc, ring_sum_element
   = rsum(h::s) + k       by ring_sum_cons
*)
val ring_sum_SNOC = store_thm(
  "ring_sum_SNOC",
  ``!r:'a ring. Ring r ==> !k s. k IN R /\ rlist s ==> (rsum (SNOC k s) = (rsum s) + k)``,
  rpt strip_tac >>
  Induct_on `s` >>
  rw[ring_add_assoc]);

(* ------------------------------------------------------------------------- *)
(* Function giving elements in Ring                                          *)
(* ------------------------------------------------------------------------- *)

(* Ring element function. *)
val ring_fun_def = Define`
  ring_fun (r:'a ring) f <=> !x. f x IN R
`;
val _ = overload_on ("rfun", ``ring_fun r``);

(* export simple definition. *)
val _ = export_rewrites ["ring_fun_def"];

(* Theorem: rfun a /\ rfun b ==> rfun (\k. a k + b k) *)
(* Proof: by ring_add_element. *)
val ring_fun_add = store_thm(
  "ring_fun_add",
  ``!r:'a ring. Ring r ==> !a b. rfun a /\ rfun b ==> rfun (\k. a k + b k)``,
  rw[]);

(* Theorem: rfun f ==> rlist (GENLIST f n) *)
(* Proof: by induction on n.
   Base case: rlist (GENLIST f 0)
      Since GENLIST f 0 = []   by GENLIST
      hence true by ring_list_nil.
   Step case: rlist (GENLIST f n) ==> rlist (GENLIST f (SUC n))
*)
val ring_fun_genlist = store_thm(
  "ring_fun_genlist",
  ``!f. rfun f ==> !n. rlist (GENLIST f n)``,
  rw_tac std_ss[ring_fun_def] >>
  Induct_on `n` >-
  rw[] >>
  rw_tac std_ss[ring_list_cons, GENLIST] >>
  `rlist (FRONT (SNOC (f n) (GENLIST f n)))` by rw_tac std_ss[FRONT_SNOC] >>
  `LAST (SNOC (f n) (GENLIST f n)) IN R` by rw_tac std_ss[LAST_SNOC] >>
  metis_tac[ring_list_front_last]);

(* Theorem: rfun f ==> rlist (MAP f l) *)
(* Proof: by induction.
   Base case: rlist (MAP f [])
     True by ring_list_nil, MAP: MAP f [] = []
   Step case: rlist l ==> rlist (MAP f l) ==> !h. rlist (h::l) ==> rlist (MAP f (h::l))
     True by ring_list_cons, MAP: MAP f (h::t) = f h::MAP f t
*)
val ring_fun_map = store_thm(
  "ring_fun_map",
  ``!f l. rfun f ==> rlist (MAP f l)``,
  rw_tac std_ss[ring_fun_def] >>
  Induct_on `l` >| [
    rw_tac std_ss[MAP, ring_list_nil],
    rw_tac std_ss[MAP, ring_list_cons]
  ]);

(* Theorem: rfun f ==> !x. x IN R ==> rfun (\j. f j * x ** j *)
(* Proof: by ring_fun_def, ring_exp_element, ring_mult_element *)
val ring_fun_from_ring_fun = store_thm(
  "ring_fun_from_ring_fun",
  ``!r:'a ring. Ring r ==> !f. rfun f ==> !x. x IN R ==> rfun (\j. f j * x ** j)``,
  rw[ring_fun_def]);

(* Theorem: rfun f ==> !x. x IN R ==> !n. rfun (\j. (f j * x ** j) ** n) *)
(* Proof: by ring_fun_def, ring_exp_element, ring_mult_element *)
val ring_fun_from_ring_fun_exp = store_thm(
  "ring_fun_from_ring_fun_exp",
  ``!r:'a ring. Ring r ==> !f. rfun f ==> !x. x IN R ==> !n. rfun (\j. (f j * x ** j) ** n)``,
  rw[ring_fun_def]);

(* Theorem: rfun f ==> !x. x IN R ==> !n. rlist (GENLIST (\j. f j * x ** j) n) *)
(* Proof:
   By induction on n.
   Base case: rlist (GENLIST (\j. f j * x ** j) 0)
      Since rlist (GENLIST (\j. f j * x ** j) 0) = rlist []    by GENLIST
        and rlist [] = T                                       by ring_list_nil
   Step case: rlist (GENLIST (\j. f j * x ** j) n) ==> rlist (GENLIST (\j. f j * x ** j) (SUC n))
        rlist (GENLIST (\j. f j * x ** j) (SUC n))
      = rlist (SNOC (f n * x ** n) (GENLIST (\j. f j * x ** j) n))    by GENLIST
      = (f n ** x ** n) IN R /\ rlist (GENLIST (\j. f j * x ** j) n)  by ring_list_SNOC
      = true /\ rlist (GENLIST (\j. f j * x ** j) n)                  by ring_fun_def, ring_exp_element
      = true /\ true                                                  by induction hypothesis
*)
val ring_list_gen_from_ring_fun = store_thm(
  "ring_list_gen_from_ring_fun",
  ``!r:'a ring. Ring r ==> !f. rfun f ==> !x. x IN R ==> !n. rlist (GENLIST (\j. f j * x ** j) n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `!j. f j IN R` by metis_tac[ring_fun_def] >>
  rw_tac std_ss[GENLIST, ring_list_SNOC, ring_exp_element, ring_mult_element]);

(* Theorem: !f. rfun f ==> !n g. rlist (GENLIST (f o g) n) *)
(* Proof:
   By induction on n.
   Base: rlist (GENLIST (f o g) 0)
          rlist (GENLIST (f o g) 0)
      <=> rlist []                   by GENLIST_0
      <=> T                          by ring_list_nil
   Step: rlist (GENLIST (f o g) n) ==> rlist (GENLIST (f o g) (SUC n))
          rlist (GENLIST (f o g) (SUC n))
      <=> rlist (SNOC ((f o g) n) (GENLIST (f o g) n))   by GENLIST
      <=> (f o g) n IN R /\ rlist (GENLIST (f o g) n)    by ring_list_SNOC
      <=> (f o g) n IN R /\ T                            by induction hypothesis
      <=> f (g n) IN R                                   by o_THM
      <=> T                                              by ring_fun_def
*)
val ring_list_from_genlist_ring_fun = store_thm(
  "ring_list_from_genlist_ring_fun",
  ``!r:'a ring. !f. rfun f ==> !n g. rlist (GENLIST (f o g) n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `rlist (GENLIST (f o g) (SUC n)) <=> f (g n) IN R` by rw_tac std_ss[GENLIST, ring_list_SNOC] >>
  metis_tac[ring_fun_def]);

(* Theorem: !f. rfun f ==> !n. rlist (GENLIST f n) *)
(* Proof:
   Since f = f o I      by I_o_ID
   The result follows from ring_list_from_genlist_ring_fun
*)
val ring_list_from_genlist = store_thm(
  "ring_list_from_genlist",
  ``!r:'a ring. !f. rfun f ==> !n. rlist (GENLIST f n)``,
  rpt strip_tac >>
  `f = f o I` by rw[] >>
  `rlist (GENLIST (f o I) n)` by rw[ring_list_from_genlist_ring_fun] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* Ring Sum Involving GENLIST                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r ==> !f n k. (0 < k /\ k < n ==> (f k = #0)) ==> (rsum (MAP f (GENLIST SUC (PRE p))) = #0) *)
(* Proof: by induction on n
   Base case: (!k. 0 < k /\ k < 0 ==> (f k = #0)) ==> (rsum (MAP f (GENLIST SUC (PRE 0))) = #0)
     rsum (MAP f (GENLIST SUC (PRE 0))
   = rsum (MAP f (GENLIST SUC 0))         by PRE 0 = 0
   = rsum (MAP f [])                      by GENLIST f 0 = [] in GENLIST
   = rsum []                              by MAP f [] = []    in MAP
   = #0                                   by ring_sum_nil
   Step case: (!k. 0 < k /\ k < n ==> (f k = #0)) ==> (rsum (MAP f (GENLIST SUC (PRE n))) = #0) ==>
              (!k. 0 < k /\ k < SUC n ==> (f k = #0)) ==> (rsum (MAP f (GENLIST SUC (PRE (SUC n)))) = #0)
   First, note that n < SUC n             by LESS_SUC
   hence !k. 0 < k /\ k < n ==> f k = #0  by LESS_TRANS
   If n = 0, true by similar reasoning in base case.
   If n <> 0, 0 < n, then n = SUC m for some m    by num_CASES
     rsum (MAP f (GENLIST SUC (PRE (SUC n))))
   = rsum (MAP f (GENLIST SUC n))
   = rsum (MAP f (GENLIST SUC (SUC (PRE n))))               by SUC_PRE
   = rsum (MAP f ((GENLIST SUC (PRE n)) ++ [SUC (PRE n)]))  by GENLIST, SNOC_APPEND
   = rsum (MAP f ((GENLIST SUC (PRE n)) ++ [n]))            by SUC_PRE
   = rsum (MAP f (GENLIST SUC (PRE n)) ++ MAP f [n])        by MAP_APPEND
   = rsum (MAP f (GENLIST SUC (PRE n))) + rsum (MAP f [n])  by ring_sum_append, ring_fun_map
   = #0 + rsum (MAP f [n])                                  by induction hypothesis
   = rsum (MAP f [n])                                       by ring_add_lzero, ring_sum_element, ring_fun_map
   = rsum ([f n])                                           by MAP
   = f n                                                    by ring_sum_sing, ring_fun_def
   = #0                                                     by n < SUC n
*)
val ring_sum_fun_zero = store_thm(
  "ring_sum_fun_zero",
  ``!r:'a ring. Ring r ==> !f. rfun f ==>
    !n. (!k. 0 < k /\ k < n ==> (f k = #0)) ==> (rsum (MAP f (GENLIST SUC (PRE n))) = #0)``,
  ntac 4 strip_tac >>
  Induct_on `n` >| [
    `GENLIST SUC 0 = []` by rw_tac std_ss[GENLIST] >>
    `MAP f [] = []` by rw_tac std_ss[MAP] >>
    rw_tac std_ss[ring_sum_nil],
    rw_tac std_ss[] >>
    `n < SUC n /\ !k. 0 < k /\ k < n ==> (f k = #0)` by metis_tac[LESS_SUC, LESS_TRANS] >>
    Cases_on `n = 0` >| [
      rw_tac std_ss[] >>
      `GENLIST SUC 0 = []` by rw_tac std_ss[GENLIST] >>
      `MAP f [] = []` by rw_tac std_ss[MAP] >>
      rw_tac std_ss[ring_sum_nil],
      `0 < n /\ ?m. n = SUC m` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO] >>
      `rsum (MAP f (GENLIST SUC n)) = rsum (MAP f (GENLIST SUC (SUC (PRE n))))` by rw_tac std_ss[SUC_PRE] >>
      `_ = rsum (MAP f ((GENLIST SUC (PRE n)) ++ [SUC (PRE n)]))` by rw_tac std_ss[GENLIST, SNOC_APPEND] >>
      `_ = rsum (MAP f ((GENLIST SUC (PRE n)) ++ [n]))` by rw_tac std_ss[SUC_PRE] >>
      `_ = rsum (MAP f (GENLIST SUC (PRE n)) ++ MAP f [n])` by rw_tac std_ss[MAP_APPEND] >>
      `_ = rsum (MAP f (GENLIST SUC (PRE n))) + rsum (MAP f [n])` by rw_tac std_ss[ring_sum_append, ring_fun_map] >>
      `_ = #0 + rsum (MAP f [n])` by metis_tac[] >>
      `_ = rsum (MAP f [n])` by rw_tac std_ss[ring_add_lzero, ring_sum_element, ring_fun_map] >>
      `_ = rsum ([f n])` by rw_tac std_ss[MAP] >>
      `_ = f n` by metis_tac[ring_sum_sing, ring_fun_def] >>
      metis_tac[]
    ]
  ]);

(* Theorem: rsum (k=0..n) f(k) = f(0) + rsum (k=1..n) f(k)  *)
(* Proof:
     rsum (GENLIST f (SUC n))
   = rsum (f 0 :: GENLIST (f o SUC) n)   by GENLIST_CONS
   = f 0 + rsum (GENLIST (f o SUC) n)    by ring_sum_cons
*)
val ring_sum_decompose_first = store_thm(
  "ring_sum_decompose_first",
  ``!r:'a ring. !f n. rsum (GENLIST f (SUC n)) = f 0 + rsum (GENLIST (f o SUC) n)``,
  rw[GENLIST_CONS]);

(* Theorem: rsum (k=0..n) f(k) = rsum (k=0..(n-1)) f(k) + f n *)
(* Proof:
     rsum (GENLIST f (SUC n))
   = rsum (SNOC (f n) (GENLIST f n))   by GENLIST definition
   = rsum ((GENLIST f n) ++ [f n])     by SNOC_APPEND
   = rsum (GENLIST f n) + rsum [f n]   by ring_sum_append
   = rsum (GENLIST f n) + f n          by ring_sum_sing
*)
val ring_sum_decompose_last = store_thm(
  "ring_sum_decompose_last",
  ``!r:'a ring. Ring r ==> !f n. rfun f ==> (rsum (GENLIST f (SUC n)) = rsum (GENLIST f n) + f n)``,
  rpt strip_tac >>
  `rlist (GENLIST f n)` by rw_tac std_ss[ring_fun_genlist] >>
  `f n IN R /\ rlist [f n]` by metis_tac[ring_list_def, ring_fun_def] >>
  rw_tac std_ss[GENLIST, SNOC_APPEND, ring_sum_append, ring_sum_sing]);

(* Theorem: Ring r /\ rfun f /\ 0 < n ==> rsum (k=0..n) f(k) = f(0) + rsum (k=1..n-1) f(k) + f(n)  *)
(* Proof:
     rsum (GENLIST f (SUC n))
   = rsum (GENLIST f n) + f n                     by ring_sum_decompose_last
   = rsum (GENLIST f (SUC m)) + f n               by n = SUC m, since 0 < n
   = f 0 + rsum (GENLIST f o SUC m) + f n         by ring_sum_decompose_first
   = f 0 + rsum (GENLIST f o SUC (PRE n)) + f n   by PRE_SUC_EQ
*)
val ring_sum_decompose_first_last = store_thm(
  "ring_sum_decompose_first_last",
  ``!r:'a ring. Ring r ==> !f n. rfun f /\ 0 < n ==> (rsum (GENLIST f (SUC n)) = f 0 + rsum (GENLIST (f o SUC) (PRE n)) + f n)``,
  rpt strip_tac >>
  `n <> 0` by decide_tac >>
  `?m. n = SUC m` by metis_tac[num_CASES] >>
  `rsum (GENLIST f (SUC n)) = rsum (GENLIST f n) + f n` by rw_tac std_ss[ring_sum_decompose_last] >>
  `_ = f 0 + rsum (GENLIST (f o SUC) m) + f n` by rw_tac std_ss[ring_sum_decompose_first] >>
  rw_tac std_ss[PRE_SUC_EQ]);

(* Theorem: rsum (GENLIST a n) + rsum (GENLIST b n) = rsum (GENLIST (\k. a k + b k) n) *)
(* Proof: by induction on n.
   Base case: rsum (GENLIST a 0) + rsum (GENLIST b 0) = rsum (GENLIST (\k. a k + b k) 0)
      true by GENLIST f 0 = [], and rsum [] = #0, and #0 + #0 = #0 by ring_add_zero_zero.
   Step case: rsum (GENLIST a n) + rsum (GENLIST b n) = rsum (GENLIST (\k. a k + b k) n) ==>
              rsum (GENLIST a (SUC n)) + rsum (GENLIST b (SUC n)) = rsum (GENLIST (\k. a k + b k) (SUC n))
   LHS = rsum (GENLIST a (SUC n)) + rsum (GENLIST b (SUC n))
       = (rsum (GENLIST a n) + a n) + (rsum (GENLIST b n) + b n)    by ring_sum_decompose_last
       = rsum (GENLIST a n) + (a n + (rsum (GENLIST b n) + b n))    by ring_add_assoc
       = rsum (GENLIST a n) + (a n + rsum (GENLIST b n) + b n)      by ring_add_assoc
       = rsum (GENLIST a n) + (rsum (GENLIST b n) + a n + b n)      by ring_add_comm
       = rsum (GENLIST a n) + (rsum (GENLIST b n) + (a n + b n))    by ring_add_assoc
       = rsum (GENLIST a n) + rsum (GENLIST b n) + (a n + b n)      by ring_add_assoc
       = rsum (GENLIST (\k. a k + b k) n) + (a n + b n)             by induction hypothesis
       = rsum (GENLIST (\k. a k + b k) (SUC n))                     by ring_sum_decompose_last
       = RHS
*)
val ring_sum_genlist_add = store_thm(
  "ring_sum_genlist_add",
  ``!r:'a ring. Ring r ==> !a b. rfun a /\ rfun b ==>
   !n. rsum (GENLIST a n) + rsum (GENLIST b n) = rsum (GENLIST (\k. a k + b k) n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `rfun (\k. a k + b k)` by rw_tac std_ss[ring_fun_add] >>
  rw_tac std_ss[ring_sum_decompose_last] >>
  `rsum (GENLIST a n) IN R /\ rsum (GENLIST b n) IN R` by rw_tac std_ss[ring_sum_element, ring_fun_genlist] >>
  `a n IN R /\ b n IN R` by metis_tac[ring_fun_def] >>
  `rsum (GENLIST a n) + a n + (rsum (GENLIST b n) + b n)
   = rsum (GENLIST a n) + (a n + rsum (GENLIST b n) + b n)` by rw[ring_add_assoc] >>
  `_ = rsum (GENLIST a n) + (rsum (GENLIST b n) + a n + b n)` by rw_tac std_ss[ring_add_comm] >>
  `_ = rsum (GENLIST a n) + rsum (GENLIST b n) + (a n + b n)` by rw[ring_add_assoc] >>
  rw_tac std_ss[]);

(* Theorem: rsum (GENLIST a n ++ GENLIST b n) = rsum (GENLIST (\k. a k + b k) n) *)
(* Proof:
     rsum (GENLIST a n ++ GENLIST b n)
   = rsum (GENLIST a n) + rsum (GENLIST b n)   by ring_sum_append, due to ring_fun_genlist.
   = rsum (GENLIST (\k. a k + b k) n)          by ring_sum_genlist_add
*)
val ring_sum_genlist_append = store_thm(
  "ring_sum_genlist_append",
  ``!r:'a ring. Ring r ==> !a b. rfun a /\ rfun b ==>
    !n. rsum (GENLIST a n ++ GENLIST b n) = rsum (GENLIST (\k. a k + b k) n)``,
  rw_tac std_ss[ring_sum_append, ring_sum_genlist_add, ring_fun_genlist]);

(* Theorem: Ring r ==> !f. rfun f  ==>
            !n m. rsum (GENLIST f (n + m)) = rsum (GENLIST f m) + rsum (GENLIST (\k. f (k + m)) n) *)
(* Proof:
   Note (\k. f (k + m)) = f o (\k. k + m)    by FUN_EQ_THM
   Hence rlist (GENLIST f m)                 by ring_list_from_genlist
     and rlist (GENLIST (\k. f (k + m)) n)   by ring_list_from_genlist_ring_fun
     rsum (GENLIST f (n + m))
   = rsum (GENLIST f m ++ GENLIST (\k. f (k + m)) n)         by GENLIST_APPEND
   = rsum (GENLIST f m) + rsum (GENLIST (\k. f (k + m)) n)   by ring_sum_append
*)
val ring_sum_genlist_sum = store_thm(
  "ring_sum_genlist_sum",
  ``!r:'a ring. Ring r ==> !f. rfun f  ==>
   !n m. rsum (GENLIST f (n + m)) = rsum (GENLIST f m) + rsum (GENLIST (\k. f (k + m)) n)``,
  rpt strip_tac >>
  `(\k. f (k + m)) = f o (\k. k + m)` by rw[FUN_EQ_THM] >>
  `rlist (GENLIST (\k. f (k + m)) n)` by rw[ring_list_from_genlist_ring_fun] >>
  `rlist (GENLIST f m)` by rw[ring_list_from_genlist] >>
  metis_tac[GENLIST_APPEND, ring_sum_append]);

(* Theorem: Ring r ==> !x. x IN R ==> !n. rsum (GENLIST (K x) n) = ##n * x *)
(* Proof:
   By induction on n.
   Base: rsum (GENLIST (K x) 0) = ##0 * x
         rsum (GENLIST (K x) 0)
       = rsum []               by GENLIST_0
       = #0                    by ring_sum_nil
       = ##0 * x               by ring_num_0, ring_mult_lzero
   Step: rsum (GENLIST (K x) n) = ##n * x ==>
         rsum (GENLIST (K x) (SUC n)) = ##(SUC n) * x
       Note rfun (K x)                     by ring_fun_def, K_THM, x IN R
         so rlist (GENLIST (K x) n)        by ring_list_from_genlist
         rsum (GENLIST (K x) (SUC n))
       = rsum (SNOC ((K x) n) (GENLIST (K x) n))   by GENLIST
       = rsum (SNOC x (GENLIST (K x) n))           by K_THM
       = rsum (GENLIST (K x) n) + x                by ring_sum_SNOC
       = ##n * x + x                               by induction hypothesis
       = ##n * x + #1 * x                          by ring_mult_lone
       = (##n + #1) * x                            by ring_mult_ladd
       = ##(SUC n) * x                             by ring_num_suc
*)
val ring_sum_genlist_const = store_thm(
  "ring_sum_genlist_const",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !n. rsum (GENLIST (K x) n) = ##n * x``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `rfun (K x)` by rw[ring_fun_def] >>
  `rlist (GENLIST (K x) n)` by rw[ring_list_from_genlist] >>
  `rsum (GENLIST (K x) (SUC n)) = ##n * x + x` by rw[GENLIST, ring_sum_SNOC] >>
  rw[ring_mult_ladd, ring_num_suc]);

(* ------------------------------------------------------------------------- *)
(* Ring Binomial Theorem                                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Binomial Index Shifting, for
     rsum (k=1..n) ##C(n,k) x^(n+1-k) y^k = rsum (k=0..n-1) ##C(n,k+1) x^(n-k) y^(k+1)  *)
(* Proof:
   Since
     rsum (k=1..n) C(n,k)x^(n+1-k)y^k
   = rsum (MAP (\k. (binomial n k)* x**(n+1-k) * y**k) (GENLIST SUC n))
   = rsum (GENLIST (\k. (binomial n k)* x**(n+1-k) * y**k) o SUC n)

     rsum (k=0..n-1) C(n,k+1)x^(n-k)y^(k+1)
   = rsum (MAP (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1)) (GENLIST I n))
   = rsum (GENLIST (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1)) o I n)
   = rsum (GENLIST (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1)) n)

   This is equivalent to showing:
   (\k. (binomial n k)* x**(n-k+1) * y**k) o SUC = (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1))
*)

(* Theorem: Binomial index shift for GENLIST:
   (\k. (binomial n k)* x**(n-k+1) * y**k) o SUC = (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1)) *)
(* Proof:
   For any k < n,
     ((\k. (binomial n k)* x**(n-k+1) * y**k) o SUC) k
   = ##(binomial n (SUC k)) * x ** SUC (n - SUC k) * y ** SUC k
   = ##(binomial n (SUC k)) * x ** (n-k) * y ** SUC k    by SUC (n - SUC k) = n - k for k < n
   = ##(binomial n (k + 1)) * x ** (n-k) * y ** (k+1)    by definition of SUC
   = (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1)) k
*)
val ring_binomial_genlist_index_shift = store_thm(
  "ring_binomial_genlist_index_shift",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==>
   !n. GENLIST ((\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) o SUC) n =
       GENLIST (\k. ##(binomial n (SUC k)) * x**(n-k) * y**(SUC k)) n``,
  rw_tac std_ss[GENLIST_FUN_EQ] >>
  `SUC (n - SUC k) = n - k` by decide_tac >>
  rw_tac std_ss[]);

(* This is closely related to above, with (SUC n) replacing (n),
   but does not require k < n. *)
(* Proof: by equality of function. *)
val ring_binomial_index_shift = store_thm(
  "ring_binomial_index_shift",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==>
   !n. (\k. ##(binomial (SUC n) k) * x**((SUC n) - k) * y**k) o SUC =
       (\k. ##(binomial (SUC n) (SUC k)) * x**(n-k) * y**(SUC k))``,
  rw[FUN_EQ_THM]);

(* Pattern for binomial expansion:

    (x+y)(x^3 + 3x^2y + 3xy^2 + y^3)
  = x(x^3) + 3x(x^2y) + 3x(xy^2) + x(y^3) +
               y(x^3) + 3y(x^2y) + 3y(xy^2) + y(y^3)
  = x^4 + (3+1)x^3y + (3+3)(x^2y^2) + (1+3)(xy^3) + y^4
    = x^4 + 4x^3y   + 6x^2y^2       + 4xy^3       + y^4

*)

(* Theorem: multiply x into a binomial term:
   (\k. x*k) o (\k. ##(binomial n k) * x ** (n - k) * y ** k) = (\k. ##(binomial n k) * x ** (SUC(n - k)) * y ** k)  *)
(* Proof: to prove:
     x * (##(binomial n k) * x ** (n - k) * y ** k) = ##(binomial n k) * x ** SUC (n - k) * y ** k
   LHS = x * (##(binomial n k) * x ** (n - k) * y ** k)
       = x * (##(binomial n k) * (x ** (n - k) * y ** k))   by ring_mult_assoc
       = (x * ##(binomial n k)) * (x ** (n - k) * y ** k)   by ring_mult_assoc
       = (##(binomial n k) * x) * (x ** (n - k) * y ** k)   by ring_mult_comm
       = ##(binomial n k) * (x * x ** (n - k) * y ** k)     by ring_mult_assoc
       = ##(binomial n k) * (x ** SUC (n - k) * y ** k)     by ring_exp_SUC
       = ##(binomial n k) * x ** SUC (n - k) * y ** k       by ring_mult_assoc
       = RHS
*)
val ring_binomial_term_merge_x = store_thm(
  "ring_binomial_term_merge_x",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==>
   !n. (\k. x*k) o (\k. ##(binomial n k) * x ** (n - k) * y ** k) = (\k. ##(binomial n k) * x ** (SUC(n - k)) * y ** k)``,
  rw_tac std_ss[FUN_EQ_THM] >>
  `##(binomial n k) IN R /\ x ** (n - k) IN R /\ y ** k IN R /\ x ** SUC (n - k) IN R` by rw[] >>
  `x * (##(binomial n k) * x ** (n - k) * y ** k) = (x * ##(binomial n k)) * (x ** (n - k) * y ** k)` by rw[ring_mult_assoc] >>
  `_ = (##(binomial n k) * x) * (x ** (n - k) * y ** k)` by rw_tac std_ss[ring_mult_comm] >>
  rw[ring_mult_assoc]);

(* Theorem: multiply y into a binomial term:
   (\k. y*k) o (\k. ##(binomial n k) * x ** (n - k) * y ** k) = (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k))  *)
(* Proof: to prove:
     y * (##(binomial n k) * x ** (n - k) * y ** k) = ##(binomial n k) * x ** (n - k) * y ** SUC k
   LHS = y * (##(binomial n k) * x ** (n - k) * y ** k)
       = y * (##(binomial n k) * (x ** (n - k) * y ** k))   by ring_mult_assoc
       = (y * ##(binomial n k)) * (x ** (n - k) * y ** k)   by ring_mult_assoc
       = (##(binomial n k) * y) * (x ** (n - k) * y ** k)   by ring_mult_comm
       = (##(binomial n k) * y) * (y ** k * x ** (n - k))   by ring_mult_comm
       = ##(binomial n k) * (y * y ** k * x ** (n - k))     by ring_mult_assoc
       = ##(binomial n k) * (y ** SUC k * x ** (n - k))     by ring_exp_SUC
       = ##(binomial n k) * (x ** (n - k) * y ** SUC k)     by ring_mult_comm
       = ##(binomial n k) * x ** (n - k) * y ** SUC k       by ring_mult_assoc
       = RHS
*)
val ring_binomial_term_merge_y = store_thm(
  "ring_binomial_term_merge_y",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==>
   !n. (\k. y*k) o (\k. ##(binomial n k) * x ** (n - k) * y ** k) = (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k))``,
  rw_tac std_ss[FUN_EQ_THM] >>
  `##(binomial n k) IN R /\ x ** (n - k) IN R /\ y ** k IN R /\ y ** SUC k IN R` by rw[] >>
  `y * (##(binomial n k) * x ** (n - k) * y ** k) =
    (y * ##(binomial n k)) * (x ** (n - k) * y ** k)` by rw[ring_mult_assoc] >>
  `_ = (##(binomial n k) * y) * (y ** k * x ** (n - k))` by rw_tac std_ss[ring_mult_comm] >>
  `_ = ##(binomial n k) * (y ** SUC k * x ** (n - k))` by rw[ring_mult_assoc] >>
  `_ = ##(binomial n k) * (x ** (n - k) * y ** SUC k)` by rw_tac std_ss[ring_mult_comm] >>
  rw[ring_mult_assoc]);


(* GOAL: *)

(* Theorem: [Binomial Theorem]  (x + y)^n = rsum (k=0..n) C(n,k)x^(n-k)y^k
   or (x + y)**n = rsum (GENLIST (\k. (binomial n k)* x**(n-k) * y**k) (SUC n)) *)
(* Proof: by induction on n.
   Base case: to prove (x + y)^0 = rsum (k=0..0) C(0,k)x^(0-k)y^k
   or  (x + y) ** 0 = rsum (GENLIST (\k. ##(binomial 0 k) * x ** (0 - k) * y ** k) (SUC 0))
   LHS = (x + y) ** 0 = #1        by ring_exp_0, ring_add_element
   RHS = rsum (GENLIST (\k. ##(binomial 0 k) * x ** (0 - k) * y ** k) (SUC 0))
       = rsum (GENLIST (\k. ##(binomial 0 k) * x ** (0 - k) * y ** k) 1)   by ONE
       = rsum (SNOC (##(binomial 0 0) * x ** 0 * y ** 0) [])               by GENLIST
       = rsum [##(binomial 0 0) * x ** 0 * y ** 0]                         by SNOC
       = rsum [##(binomial 0 0) * #1 * #1]                                 by ring_exp_0
       = rsum [##1 * #1 * #1]                                              by binomial_n_n
       = rsum [#1 * #1 * #1]                                               by ring_num_1
       = rsum [#1]                                                         by ring_mult_one_one
       = #1                                                                by ring_sum_sing, ring_one_element
       = LHS
   Step case: assume (x + y)^n = rsum (k=0..n) C(n,k)x^(n-k)y^k
    to prove: (x + y)^SUC n = rsum (k=0..(SUC n)) C(SUC n,k)x^((SUC n)-k)y^k
    or (x + y) ** n = rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** k) (SUC n)) ==>
       (x + y) ** SUC n = rsum (GENLIST (\k. ##(binomial (SUC n) k) * x ** (SUC n - k) * y ** k) (SUC (SUC n)))
   LHS = (x + y) ** SUC n
       = (x + y) * (x + y) ** n       by ring_exp_SUC
       = (x + y) * rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** k) (SUC n))    by induction hypothesis
       = x * rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** k) (SUC n)) +
         y * rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** k) (SUC n))          by ring_mult_ladd
       = rsum (MAP (\k. x*k) (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** k) (SUC n))) +
         rsum (MAP (\k. y*k) (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** k) (SUC n)))  by ring_sum_mult
       = rsum (GENLIST ((\k. x*k) o (\k. ##(binomial n k) * x ** (n - k) * y ** k)) (SUC n)) +
         rsum (GENLIST ((\k. y*k) o (\k. ##(binomial n k) * x ** (n - k) * y ** k)) (SUC n))    by MAP_GENLIST
       = rsum (GENLIST (\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) (SUC n)) +
         rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) (SUC n))
                                                               by ring_binomial_term_merge_x, ring_binomial_term_merge_y
       = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
         rsum (GENLIST ((\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) o SUC) n) +
         rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) (SUC n))   by ring_sum_decompose_first
       = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
         rsum (GENLIST ((\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) o SUC) n) +
        (rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n )                      by ring_sum_decompose_last
       = (\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) 0 +
         rsum (GENLIST (\k. ##(binomial n (SUC k)) * x ** (n - k) * y ** (SUC k)) n) +
        (rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n )             by ring_binomial_genlist_index_shift
       = (\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) 0 +
        (rsum (GENLIST (\k. ##(binomial n (SUC k)) * x ** (n - k) * y ** (SUC k)) n) +
         rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n)) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n               by ring_add_assoc, ring_add_element
       = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
        rsum (GENLIST (\k. (##(binomial n (SUC k)) * x ** (n - k) * y ** (SUC k) +
                            ##(binomial n k) * x ** (n - k) * y ** (SUC k))) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n                by ring_sum_genlist_add
       = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
        rsum (GENLIST (\k. (##(binomial n (SUC k)) + ##(binomial n k)) * x ** (n - k) * y ** (SUC k)) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n                by ring_mult_ladd, ring_mult_element
       = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
        rsum (GENLIST (\k. (##(binomial n (SUC k)) * (x ** (n - k) * y ** (SUC k)) +
                            ##(binomial n k) * (x ** (n - k) * y ** (SUC k)))) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n                by  ring_mult_assoc
       = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
        rsum (GENLIST (\k. ##(binomial n (SUC k) + binomial n k) * (x ** (n - k) * y ** (SUC k))) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n                by ring_num_add_mult, ring_mult_element
       = (\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) 0 +
        rsum (GENLIST (\k. ##(binomial (SUC n) (SUC k)) * (x ** (n - k) * y ** (SUC k))) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n                by binomial_recurrence, ADD_COMM
       = (\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) 0 +
        rsum (GENLIST (\k. ##(binomial (SUC n) (SUC k)) * x ** (n - k) * y ** (SUC k)) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n                by ring_mult_assoc
       = ##(binomial n 0) * x ** (SUC n) * y ** 0 +
        rsum (GENLIST (\k. ##(binomial (SUC n) (SUC k)) * x ** (n - k) * y ** (SUC k)) n) +
        ##(binomial n n) * x ** 0 * y ** (SUC n)                              by function application
       = ##(binomial (SUC n) 0) * x ** (SUC n) * y ** 0 +
        rsum (GENLIST (\k. ##(binomial (SUC n) (SUC k)) * x ** (n - k) * y ** (SUC k)) n) +
        ##(binomial (SUC n) (SUC n)) * x ** 0 * y ** (SUC n)                  by binomial_n_0, binomial_n_n
       = ##(binomial (SUC n) 0) * x ** (SUC n) * y ** 0 +
        rsum (GENLIST ((\k. ##(binomial (SUC n) k) * x ** ((SUC n) - k) * y ** k) o SUC) n) +
        ##(binomial (SUC n) (SUC n)) * x ** 0 * y ** (SUC n)                  by ring_binomial_index_shift
       = (\k. ##(binomial (SUC n) k) * x ** ((SUC n) - k) * y ** k) 0 +
        rsum (GENLIST ((\k. ##(binomial (SUC n) k) * x ** ((SUC n) - k) * y ** k) o SUC) n) +
        (\k. ##(binomial (SUC n) k) * x ** ((SUC n) - k) * y ** k) (SUC n)    by function application
       = rsum (GENLIST (\k. ##(binomial (SUC n) k) * x ** (SUC n - k) * y ** k) (SUC n)) +
        (\k. ##(binomial (SUC n) k) * x ** (SUC n - k) * y ** k) (SUC n)      by ring_sum_decompose_first
       = rsum (GENLIST (\k. ##(binomial (SUC n) k) * x ** (SUC n - k) * y ** k) (SUC (SUC n))) by ring_sum_decompose_last
       = RHS
    Conventionally,
      (x + y)^SUC n
    = (x + y)(x + y)^n      by EXP
    = (x + y) rsum (k=0..n) C(n,k)x^(n-k)y^k   by induction hypothesis
    = x (rsum (k=0..n) C(n,k)x^(n-k)y^k) +
      y (rsum (k=0..n) C(n,k)x^(n-k)y^k)       by RIGHT_ADD_DISTRIB
    = rsum (k=0..n) C(n,k)x^(n+1-k)y^k +
      rsum (k=0..n) C(n,k)x^(n-k)y^(k+1)       by moving factor into ring_sum
    = C(n,0)x^(n+1) + rsum (k=1..n) C(n,k)x^(n+1-k)y^k +
                      rsum (k=0..n-1) C(n,k)x^(n-k)y^(k+1) + C(n,n)y^(n+1)  by breaking sum
    = C(n,0)x^(n+1) + rsum (k=0..n-1) C(n,k+1)x^(n-k)y^(k+1) +
                      rsum (k=0..n-1) C(n,k)x^(n-k)y^(k+1) + C(n,n)y^(n+1)  by index shifting
    = C(n,0)x^(n+1) + rsum (k=0..n-1) [C(n,k+1) + C(n,k)] x^(n-k)y^(k+1) + C(n,n)y^(n+1)     by merging sums
    = C(n,0)x^(n+1) + rsum (k=0..n-1) C(n+1,k+1) x^(n-k)y^(k+1)          + C(n,n)y^(n+1)     by binomial recurrence
    = C(n,0)x^(n+1) + rsum (k=1..n) C(n+1,k) x^(n+1-k)y^k                + C(n,n)y^(n+1)     by index shifting again
    = C(n+1,0)x^(n+1) + rsum (k=1..n) C(n+1,k) x^(n+1-k)y^k              + C(n+1,n+1)y^(n+1) by binomial identities
    = rsum (k=0..(SUC n))C(SUC n,k) x^((SUC n)-k)y^k                                         by synthesis of sum
*)
val ring_binomial_thm = store_thm(
  "ring_binomial_thm",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==>
   !n. (x + y)**n = rsum (GENLIST (\k. ##(binomial n k) * x**(n-k) * y**k) (SUC n))``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[ring_sum_sing, binomial_n_n] >>
  rw_tac std_ss[ring_exp_SUC, ring_add_element] >>
  `!m n k h. ##(binomial m n) IN R /\ x ** h IN R /\ y ** k IN R` by rw[] >>
  `!h. (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) h IN R` by rw_tac std_ss[ring_mult_element] >>
  `!h. (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) h IN R` by rw_tac std_ss[ring_mult_element] >>
  `!m. rfun (\k. ##(binomial m k) * x ** (m - k) * y ** k)` by rw_tac std_ss[ring_fun_def, ring_mult_element] >>
  `!m n. rlist (GENLIST (\k. ##(binomial m k) * x ** (m - k) * y ** k) n)` by rw_tac std_ss[ring_fun_genlist] >>
  `!m n. rsum (GENLIST (\k. ##(binomial m k) * x ** (m - k) * y ** k) n) IN R` by rw_tac std_ss[ring_sum_element] >>
  `!m. rfun (\k. ##(binomial m k) * x ** (m - k) * y ** SUC k)` by rw_tac std_ss[ring_fun_def, ring_mult_element] >>
  `!m n. rlist (GENLIST (\k. ##(binomial m k) * x ** (m - k) * y ** SUC k) n)` by rw_tac std_ss[ring_fun_genlist] >>
  `!m n. rsum (GENLIST (\k. ##(binomial m k) * x ** (m - k) * y ** SUC k) n) IN R` by rw_tac std_ss[ring_sum_element] >>
  `!m. rfun (\k. ##(binomial m (SUC k)) * x ** (m - k) * y ** SUC k)` by rw_tac std_ss[ring_fun_def, ring_mult_element] >>
  `!m n. rlist (GENLIST (\k. ##(binomial m (SUC k)) * x ** (m - k) * y ** SUC k) n)` by rw_tac std_ss[ring_fun_genlist] >>
  `!m n. rsum (GENLIST (\k. ##(binomial m (SUC k)) * x ** (m - k) * y ** SUC k) n) IN R` by rw_tac std_ss[ring_sum_element] >>
  `(x + y) * rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** k) (SUC n)) =
    x * rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** k) (SUC n)) +
    y * rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** k) (SUC n))` by rw_tac std_ss[ring_mult_ladd] >>
  `_ = rsum (GENLIST ((\k. x*k) o (\k. ##(binomial n k) * x ** (n - k) * y ** k)) (SUC n)) +
        rsum (GENLIST ((\k. y*k) o (\k. ##(binomial n k) * x ** (n - k) * y ** k)) (SUC n))`
    by rw_tac std_ss[ring_sum_mult, MAP_GENLIST] >>
  `_ = rsum (GENLIST (\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) (SUC n)) +
        rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) (SUC n))`
    by rw_tac std_ss[ring_binomial_term_merge_x, ring_binomial_term_merge_y] >>
  `_ = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
         rsum (GENLIST ((\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) o SUC) n) +
         rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) (SUC n))`
    by rw_tac std_ss[ring_sum_decompose_first] >>
  `_ = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
         rsum (GENLIST ((\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) o SUC) n) +
        (rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n )`
    by rw_tac std_ss[ring_sum_decompose_last] >>
  `_ = (\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) 0 +
         rsum (GENLIST (\k. ##(binomial n (SUC k)) * x ** (n - k) * y ** (SUC k)) n) +
        (rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n )`
    by rw_tac std_ss[ring_binomial_genlist_index_shift] >>
  `_ = (\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) 0 +
        (rsum (GENLIST (\k. ##(binomial n (SUC k)) * x ** (n - k) * y ** (SUC k)) n) +
         rsum (GENLIST (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n)) +
       (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n`
    by rw_tac std_ss[ring_add_assoc, ring_add_element] >>
  `_ = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
        rsum (GENLIST (\k. (##(binomial n (SUC k)) * x ** (n - k) * y ** (SUC k) +
                            ##(binomial n k) * x ** (n - k) * y ** (SUC k))) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n`
    by rw_tac std_ss[ring_sum_genlist_add] >>
  `_ = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
        rsum (GENLIST (\k. (##(binomial n (SUC k)) * (x ** (n - k) * y ** (SUC k)) +
                            ##(binomial n k) * (x ** (n - k) * y ** (SUC k)))) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n`
    by rw_tac std_ss[ring_mult_assoc] >>
  `_ = (\k. ##(binomial n k) * x ** SUC (n - k) * y ** k) 0 +
        rsum (GENLIST (\k. ##(binomial n (SUC k) + binomial n k) * (x ** (n - k) * y ** (SUC k))) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n`
    by rw_tac std_ss[ring_num_add_mult, ring_mult_element] >>
  `_ = (\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) 0 +
        rsum (GENLIST (\k. ##(binomial (SUC n) (SUC k)) * (x ** (n - k) * y ** (SUC k))) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n`
    by rw_tac std_ss[binomial_recurrence, ADD_COMM] >>
  `_ = (\k. ##(binomial n k) * x ** SUC(n - k) * y ** k) 0 +
        rsum (GENLIST (\k. ##(binomial (SUC n) (SUC k)) * x ** (n - k) * y ** (SUC k)) n) +
        (\k. ##(binomial n k) * x ** (n - k) * y ** (SUC k)) n`
    by rw_tac std_ss[ring_mult_assoc] >>
  `_ = ##(binomial (SUC n) 0) * x ** (SUC n) * y ** 0 +
        rsum (GENLIST (\k. ##(binomial (SUC n) (SUC k)) * x ** (n - k) * y ** (SUC k)) n) +
        ##(binomial (SUC n) (SUC n)) * x ** 0 * y ** (SUC n)`
        by rw_tac std_ss[binomial_n_0, binomial_n_n] >>
  `_ = ##(binomial (SUC n) 0) * x ** (SUC n) * y ** 0 +
        rsum (GENLIST ((\k. ##(binomial (SUC n) k) * x ** ((SUC n) - k) * y ** k) o SUC) n) +
        ##(binomial (SUC n) (SUC n)) * x ** 0 * y ** (SUC n)`
        by rw_tac std_ss[ring_binomial_index_shift] >>
  `_ = rsum (GENLIST (\k. ##(binomial (SUC n) k) * x ** (SUC n - k) * y ** k) (SUC n)) +
        (\k. ##(binomial (SUC n) k) * x ** (SUC n - k) * y ** k) (SUC n)`
        by rw_tac std_ss[ring_sum_decompose_first] >>
  `_ = rsum (GENLIST (\k. ##(binomial (SUC n) k) * x ** (SUC n - k) * y ** k) (SUC (SUC n)))`
        by rw_tac std_ss[ring_sum_decompose_last] >>
  rw_tac std_ss[]);

(* This is a major milestone theorem. *)

(* ------------------------------------------------------------------------- *)
(* Ring with prime characteristic                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r ==> prime (char r) <=> 1 < char r /\ ##(binomial (char r) k) = #0   for  0 < k < (char r) *)
(* Proof:
       prime (char r)
   <=> divides (char r) (binomial (char r) k) for 0 < k < (char r) by prime_iff_divides_binomials
   <=> ##(binomial (char r) k) = #0           for 0 < k < (char r) by ring_char_divides
*)
val ring_char_prime = store_thm(
  "ring_char_prime",
  ``!r:'a ring. Ring r ==>
   (prime (char r) <=> 1 < char r /\ !k. 0 < k /\ k < char r ==> (##(binomial (char r) k) = #0))``,
  rw_tac std_ss[prime_iff_divides_binomials, ring_char_divides]);

(* Theorem: [Freshman's Theorem]
            Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
            ((x + y) ** (char r) = x ** (char r) + y ** (char r)) *)
(* Proof:
   Let p = char r.
   prime p ==> 0 < p                                 by PRIME_POS
   Let f = (\k. ##(binomial p k) * x**(p-k) * y**k), then
   then rfun f /\ f 0 IN R /\ f p IN R               by ring_fun_def
   !k. 0 < k /\ k < p ==> (##(binomial p k) = #0)    by ring_char_prime
   !k. 0 < k /\ k < p ==> (f k = #0)                 by ring_mult_lzero, ring_num_element, ring_exp_element
     (x + y) ** p
   = rsum (GENLIST f) (SUC p))                       by ring_binomial_thm
   = f 0 + rsum (GENLIST (f o SUC) (PRE p)) + f p    by ring_sum_decompose_first_last
   = f 0 + rsum (MAP f (GENLIST SUC (PRE p))) + f p  by MAP_GENLIST
   = f 0 + #0 + f p                                  by ring_sum_fun_zero
   = f 0 + f p                                       by ring_add_rzero

   f 0 = ##(binomial p 0) * x**(p-0) * y**0
       =  #1 * x**p * #1                             by binomial_n_0, ring_exp_0, ring_num_1
       = x ** p                                      by ring_mult_lone, ring_mult_rone
   f p = ##(binomial p p) * x**(p-p) * y**p
       = #1 * #1 * y**p                              by binomial_n_n, ring_exp_0, ring_num_1
       = y ** p                                      by ring_exp_element, ring_mult_one_one
   The result follows.
*)
val ring_freshman_thm = store_thm(
  "ring_freshman_thm",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
         ((x + y) ** (char r) = x ** (char r) + y ** (char r))``,
  rpt strip_tac >>
  qabbrev_tac `p = char r` >>
  `0 < p` by metis_tac[PRIME_POS] >>
  qabbrev_tac `f = (\k. ##(binomial p k) * x**(p-k) * y**k)` >>
  `rfun f /\ f 0 IN R /\ f p IN R` by rw[ring_fun_def, Abbr`f`] >>
  `!k. 0 < k /\ k < p ==> (##(binomial p k) = #0)` by metis_tac[ring_char_prime] >>
  `!k. 0 < k /\ k < p ==> (f k = #0)` by rw[Abbr`f`, Abbr`p`] >>
  `(x + y) ** p = rsum (GENLIST f (SUC p))` by rw_tac std_ss[ring_binomial_thm, Abbr(`p`), Abbr(`f`)] >>
  `(x + y) ** p = f 0 + rsum (GENLIST (f o SUC) (PRE p)) + f p` by metis_tac[ring_sum_decompose_first_last] >>
  `_ = f 0 + rsum (MAP f (GENLIST SUC (PRE p))) + f p` by rw_tac std_ss[MAP_GENLIST] >>
  `_ = f 0 + f p` by rw_tac std_ss[ring_sum_fun_zero, ring_add_rzero] >>
  `f 0 = #1 * x**p * #1` by rw_tac std_ss[Abbr`f`, binomial_n_0, ring_exp_0, ring_num_1] >>
  `f p = #1 * #1 * y**p` by rw_tac std_ss[Abbr`f`, binomial_n_n, ring_exp_0, ring_num_1] >>
  rw[]);

(* Note: a ** b ** c = a ** (b ** c) *)
(* Theorem: [Freshman's Theorem Generalized]
             Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
             !n. (x + y) ** (char r) ** n = x ** (char r) ** n + y ** (char r) ** n *)
(* Proof:
   Let p = char r.
   prime p ==> 0 < p                by PRIME_POS
   By induction on n.
   Base case: (x + y) ** p ** 0 = x ** p ** 0 + y ** p ** 0
   LHS = (x + y) ** p ** 0
       = (x + y) ** 1               by EXP
       = x + y                      by ring_exp_1
       = x ** 1 + y ** 1            by ring_exp_1
       = x ** p ** 0 + y ** p ** 0  by EXP
       = RHS
   Step case: (x + y) ** p ** n = x ** p ** n + y ** p ** n ==>
              (x + y) ** p ** SUC n = x ** p ** SUC n + y ** p ** SUC n
   LHS = (x + y) ** p ** SUC n
       = (x + y) ** (p * p ** n)                   by EXP
       = (x + y) ** (p ** n * p)                   by MULT_COMM
       = ((x + y) ** p ** n) ** p                  by ring_exp_mult
       = (x ** p ** n + y ** p ** n) ** p          by induction hypothesis
       = (x ** p ** n) ** p + (y ** p ** n) ** p   by ring_freshman_thm
       = x ** (p ** n * p) + y ** (p ** n * p)     by ring_exp_mult
       = x ** (p * p ** n) + y ** (p * p ** n)     by MULT_COMM
       = x ** p ** SUC n + y ** p ** SUC n         by EXP
       = RHS
*)
val ring_freshman_all = store_thm(
  "ring_freshman_all",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
   !n. (x + y) ** (char r) ** n = x ** (char r) ** n + y ** (char r) ** n``,
  rpt strip_tac >>
  qabbrev_tac `p = char r` >>
  Induct_on `n` >-
  rw[EXP] >>
  `(x + y) ** p ** SUC n = (x + y) ** (p * p ** n)` by rw[EXP] >>
  `_ = (x + y) ** (p ** n * p)` by rw_tac std_ss[MULT_COMM] >>
  `_ = ((x + y) ** p ** n) ** p` by rw[ring_exp_mult] >>
  `_ = (x ** p ** n + y ** p ** n) ** p` by rw[] >>
  `_ = (x ** p ** n) ** p + (y ** p ** n) ** p` by rw[ring_freshman_thm, Abbr`p`] >>
  `_ = x ** (p ** n * p) + y ** (p ** n * p)` by rw[ring_exp_mult] >>
  `_ = x ** (p * p ** n) + y ** (p * p ** n)` by rw_tac std_ss[MULT_COMM] >>
  `_ = x ** p ** SUC n + y ** p ** SUC n` by rw[EXP] >>
  rw[]);

(* Theorem: Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
            ((x - y) ** char r = x ** char r - y ** char r) *)
(* Proof:
   Let m = char r.
     (x - y) ** m
   = (x + -y) ** m            by ring_sub_def
   = x ** m + (-y) ** m       by ring_freshman_thm
   If EVEN m,
      (-y) ** m = y ** m      by ring_neg_exp
      prime m ==> m = 2       by EVEN_PRIME
      y ** m = - (y ** m)     by ring_neg_char_2
      The result follows      by ring_sub_def
   If ~EVEN m,
      (-y) ** m = - (y ** m)  by ring_neg_exp
      The result follows      by ring_sub_def
*)
val ring_freshman_thm_sub = store_thm(
  "ring_freshman_thm_sub",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
               ((x - y) ** char r = x ** char r - y ** char r)``,
  rpt strip_tac >>
  qabbrev_tac `m = char r` >>
  rw[] >>
  `(x + -y) ** m = x ** m + (-y) ** m` by rw[ring_freshman_thm, Abbr`m`] >>
  Cases_on `EVEN m` >-
  rw[GSYM EVEN_PRIME, ring_neg_exp, ring_neg_char_2, Abbr`m`] >>
  rw[ring_neg_exp]);

(* Theorem: Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
            !n. (x - y) ** (char r) ** n = x ** (char r) ** n - y ** (char r) ** n *)
(* Proof:
   Let m = char r.
   prime m ==> 0 < m                by PRIME_POS
   By induction on n.
   Base case: (x - y) ** m ** 0 = x ** m ** 0 - y ** m ** 0
        (x - y) ** m ** 0
      = (x - y) ** 1               by EXP
      = x - y                      by ring_exp_1
      = x ** 1 - y ** 1            by ring_exp_1
      = x ** m ** 0 - y ** m ** 0  by EXP
   Step case: (x - y) ** m ** n = x ** m ** n - y ** m ** n ==>
              (x - y) ** m ** SUC n = x ** m ** SUC n - y ** m ** SUC n
        (x - y) ** m ** SUC n
      = (x - y) ** (m * m ** n)                   by EXP
      = (x - y) ** (m ** n * m)                   by MULT_COMM
      = ((x - y) ** m ** n) ** m                  by ring_exp_mult
      = (x ** m ** n - y ** m ** n) ** m          by induction hypothesis
      = (x ** m ** n) ** m - (y ** m ** n) ** m   by ring_freshman_thm_sub
      = x ** (m ** n * m) - y ** (m ** n * m)     by ring_exp_mult
      = x ** (m * m ** n) - y ** (m * m ** n)     by MULT_COMM
      = x ** m ** SUC n - y ** m ** SUC n         by EXP
*)
val ring_freshman_all_sub = store_thm(
  "ring_freshman_all_sub",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !x y. x IN R /\ y IN R ==>
   !n. (x - y) ** (char r) ** n = x ** (char r) ** n - y ** (char r) ** n``,
  rpt strip_tac >>
  qabbrev_tac `m = char r` >>
  Induct_on `n` >-
  rw[EXP] >>
  `(x - y) ** m ** SUC n = (x - y) ** (m * m ** n)` by rw[EXP] >>
  `_ = (x - y) ** (m ** n * m)` by rw_tac std_ss[MULT_COMM] >>
  `_ = ((x - y) ** m ** n) ** m` by rw[ring_exp_mult] >>
  `_ = (x ** m ** n - y ** m ** n) ** m` by rw[] >>
  `_ = (x ** m ** n) ** m - (y ** m ** n) ** m` by rw[ring_freshman_thm_sub, Abbr`m`] >>
  `_ = x ** (m ** n * m) - y ** (m ** n * m)` by rw[ring_exp_mult] >>
  `_ = x ** (m * m ** n) - y ** (m * m ** n)` by rw_tac std_ss[MULT_COMM] >>
  `_ = x ** m ** SUC n - y ** m ** SUC n` by rw[EXP] >>
  rw[]);

(* Theorem: [Fermat's Little Theorem]
            Ring r /\ prime (char r) ==> !n. (##n) ** (char r) = (##n)  *)
(* Proof: by induction on n.
   Let p = char r, prime p ==> 0 < p   by PRIME_POS
   Base case: ##0 ** p = ##0
     ##0 ** p
   = #0 ** p              by ring_num_0
   = #0                   by ring_zero_exp, p <> 0
   = ##0                  by ring_num_0
   Step case: ##n ** p = ##n ==> ##(SUC n) ** p = ##(SUC n)
     ##(SUC n) ** p
   = (#1 + ##n) ** p      by ring_num_SUC
   = #1 ** p + ##n ** p   by ring_freshman_thm
   = #1 ** p + ##n        by induction hypothesis
   = #1 + ##n             by ring_one_exp
   = ##(SUC n)            by ring_num_SUC
*)
val ring_fermat_thm = store_thm(
  "ring_fermat_thm",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !n. (##n) ** (char r) = (##n)``,
  rpt strip_tac >>
  qabbrev_tac `p = char r` >>
  `0 < p` by rw_tac std_ss[PRIME_POS] >>
  `p <> 0` by decide_tac >>
  Induct_on `n` >| [
    rw[ring_zero_exp],
    rw_tac std_ss[ring_num_SUC] >>
    `#1 IN R /\ ##n IN R` by rw[] >>
    metis_tac[ring_freshman_thm, ring_one_exp]
  ]);

(* Theorem: [Fermat's Little Theorem Generalized]
            Ring r /\ prime (char r) ==> !n k. (##n) ** (char r) ** k = (##n)  *)
(* Proof:
   Let p = char r. By induction on k.
   Base case: ##n ** p ** 0 = ##n
     ##n ** p ** 0
   = ##n ** 1               by EXP
   = ##n                    by ring_exp_1
   Step case: ##n ** p ** k = ##n ==> ##n ** p ** SUC k = ##n
     ##n ** p ** SUC k
   = ##n ** (p * p ** k)    by EXP
   = ##n ** (p ** k * p)    by MULT_COMM
   = (##n ** p ** k) ** p   by ring_exp_mult
   = ##n ** p               by induction hypothesis
   = ##n                    by ring_fermat_thm
*)
val ring_fermat_all = store_thm(
  "ring_fermat_all",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !n k. (##n) ** (char r) ** k = (##n)``,
  rpt strip_tac >>
  qabbrev_tac `p = char r` >>
  Induct_on `k` >-
  rw[EXP] >>
  `##n ** p ** SUC k = ##n ** (p * p ** k)` by rw[EXP] >>
  `_ = ##n ** (p ** k * p)` by rw_tac std_ss[MULT_COMM] >>
  rw[ring_exp_mult, ring_fermat_thm, Abbr`p`]);

(* Theorem: [Freshman Theorem for Ring Sum]
            Ring r /\ prime (char r) ==> !f. rfun f ==> !x. x IN R ==>
            !n. rsum (GENLIST (\j. f j * x ** j) n) ** char r =
                rsum (GENLIST (\j. (f j * x ** j) ** char r) n) *)
(* Proof:
   Let m = char r.
   By induction on n.
   Base case: rsum (GENLIST (\j. f j * x ** j) 0) ** m =
              rsum (GENLIST (\j. (f j * x ** j) ** m) 0)
      Note 0 < m                      by PRIME_POS
        rsum (GENLIST (\j. f j * x ** j) 0) ** m
      = rsum [] ** m                  by GENLIST
      = #0 ** m                       by ring_sum_nil
      = #0                            by ring_zero_exp, 0 < m.
      = rsum []                       by ring_sum_nil
      = rsum (GENLIST (\j. (f j * x ** j) ** m) 0)   by GENLIST
   Step case: rsum (GENLIST (\j. f j * x ** j) (SUC n)) ** m =
              rsum (GENLIST (\j. (f j * x ** j) ** m) (SUC n))
      Note rfun (\j. f j * x ** j)                   by ring_fun_from_ring_fun
       and rfun (\j. (f j * x ** j) ** m)            by ring_fun_from_ring_fun_exp
       and rsum (GENLIST (\j. f j * x ** j) n) IN R  by ring_sum_element, ring_list_gen_from_ring_fun
        rsum (GENLIST (\j. f j * x ** j) (SUC n)) ** m
      = (rsum (GENLIST (\j. f j * x ** j) n) + (f n * x ** n)) ** m       by ring_sum_decompose_last
      = (rsum (GENLIST (\j. f j * x ** j) n)) ** m + (f n * x ** n) ** m  by ring_freshman_thm
      = rsum (GENLIST (\j. (f j * x ** j) ** m) n) + (f n * x ** n) ** m  by induction hypothesis
      = rsum (GENLIST (\j. (f j * x ** j) ** m) (SUC n))                  by poly_sum_decompose_last
*)
val ring_sum_freshman_thm = store_thm(
  "ring_sum_freshman_thm",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !f. rfun f ==> !x. x IN R ==>
   !n. rsum (GENLIST (\j. f j * x ** j) n) ** char r =
       rsum (GENLIST (\j. (f j * x ** j) ** char r) n)``,
  rpt strip_tac >>
  qabbrev_tac `m = char r` >>
  Induct_on `n` >| [
    rw_tac std_ss[GENLIST, ring_sum_nil] >>
    `0 < m` by rw[PRIME_POS, Abbr`m`] >>
    `m <> 0` by decide_tac >>
    rw[ring_zero_exp],
    `rfun (\j. f j * x ** j)` by rw[ring_fun_from_ring_fun] >>
    `rfun (\j. (f j * x ** j) ** m)` by rw[ring_fun_from_ring_fun_exp] >>
    `rsum (GENLIST (\j. f j * x ** j) n) IN R` by rw[ring_sum_element, ring_list_gen_from_ring_fun] >>
    `!j. f j IN R` by metis_tac[ring_fun_def] >>
    `f n * x ** n IN R` by rw[] >>
    `rsum (GENLIST (\j. f j * x ** j) (SUC n)) ** m
    = (rsum (GENLIST (\j. f j * x ** j) n) + (f n * x ** n)) ** m` by rw[ring_sum_decompose_last] >>
    `_ = (rsum (GENLIST (\j. f j * x ** j) n)) ** m + (f n * x ** n) ** m` by rw[ring_freshman_thm, Abbr`m`] >>
    `_ = rsum (GENLIST (\j. (f j * x ** j) ** m) n) + (f n * x ** n) ** m` by rw[] >>
    `_ = rsum (GENLIST (\j. (f j * x ** j) ** m) (SUC n))` by rw[ring_sum_decompose_last] >>
    rw[]
  ]);

(* Theorem: Ring r /\ prime (char r) ==> !f. rfun f ==> !x. x IN R ==>
            !n k. rsum (GENLIST (\j. f j * x ** j) n) ** char r ** k =
                  rsum (GENLIST (\j. (f j * x ** j) ** char r ** k) n) *)
(* Proof:
   Let m = char r.
   By induction on n.
   Base case: rsum (GENLIST (\j. f j * x ** j) 0) ** m ** k =
              rsum (GENLIST (\j. (f j * x ** j) ** m ** k) 0)
      Note 0 < m                      by PRIME_POS
        so 0 < m ** k                 by EXP_NONZERO
        rsum (GENLIST (\j. f j * x ** j) 0) ** m ** k
      = rsum [] ** m ** k        by GENLIST
      = #0 ** m ** k             by ring_sum_nil
      = #0                       by ring_zero_exp, 0 < m ** k.
      = rsum []                  by ring_sum_nil
      = rsum (GENLIST (\j. (f j * x ** j) ** m ** k) 0)   by GENLIST
   Step case: rsum (GENLIST (\j. f j * x ** j) (SUC n)) ** m ** k =
              rsum (GENLIST (\j. (f j * x ** j) ** m ** k) (SUC n))
      Note rfun (\j. f j * x ** j)                   by ring_fun_from_ring_fun
       and rfun (\j. (f j * x ** j) ** m ** k)       by ring_fun_from_ring_fun_exp
       and rsum (GENLIST (\j. f j * x ** j) n) IN R  by ring_sum_element, ring_list_gen_from_ring_fun
        rsum (GENLIST (\j. f j * x ** j) (SUC n)) ** m ** k
      = (rsum (GENLIST (\j. f j * x ** j) n) + (f n * x ** n)) ** m ** k            by ring_sum_decompose_last
      = (rsum (GENLIST (\j. f j * x ** j) n)) ** m ** k + (f n * x ** n) ** m ** k  by ring_freshman_all
      = rsum (GENLIST (\j. (f j * x ** j) ** m ** k) n) + (f n * x ** n) ** m ** k  by induction hypothesis
      = rsum (GENLIST (\j. (f j * x ** j) ** m ** k) (SUC n))                       by ring_sum_decompose_last
*)
val ring_sum_freshman_all = store_thm(
  "ring_sum_freshman_all",
  ``!r:'a ring. Ring r /\ prime (char r) ==> !f. rfun f ==> !x. x IN R ==>
   !n k. rsum (GENLIST (\j. f j * x ** j) n) ** char r ** k =
         rsum (GENLIST (\j. (f j * x ** j) ** char r ** k) n)``,
  rpt strip_tac >>
  qabbrev_tac `m = char r` >>
  Induct_on `n` >| [
    rw_tac std_ss[GENLIST, ring_sum_nil] >>
    `0 < m` by rw[PRIME_POS, Abbr`m`] >>
    `m <> 0` by decide_tac >>
    `m ** k <> 0` by rw[EXP_NONZERO] >>
    rw[ring_zero_exp],
    `rfun (\j. f j * x ** j)` by rw[ring_fun_from_ring_fun] >>
    `rfun (\j. (f j * x ** j) ** m ** k)` by rw[ring_fun_from_ring_fun_exp] >>
    `rsum (GENLIST (\j. f j * x ** j) n) IN R` by rw[ring_sum_element, ring_list_gen_from_ring_fun] >>
    `!j. f j IN R` by metis_tac[ring_fun_def] >>
    `f n * x ** n IN R` by rw[] >>
    `rsum (GENLIST (\j. f j * x ** j) (SUC n)) ** m ** k
    = (rsum (GENLIST (\j. f j * x ** j) n) + (f n * x ** n)) ** m ** k` by rw[ring_sum_decompose_last] >>
    `_ = (rsum (GENLIST (\j. f j * x ** j) n)) ** m ** k + (f n * x ** n) ** m ** k` by rw[ring_freshman_all, Abbr`m`] >>
    `_ = rsum (GENLIST (\j. (f j * x ** j) ** m ** k) n) + (f n * x ** n) ** m ** k` by rw[] >>
    `_ = rsum (GENLIST (\j. (f j * x ** j) ** m ** k) (SUC n))` by rw[ring_sum_decompose_last] >>
    rw[]
  ]);

(* Theorem: [Frobenius Theorem]
            For a Ring with prime p = char r, x IN R,
            the map x --> x^p  is a ring homomorphism to itself (endomorphism)
         or Ring r /\ prime (char r) ==> RingEndo (\x. x ** (char r)) r  *)
(* Proof:
   Let p = char r, and prime p.
   First, x IN R ==> x ** p IN R           by ring_exp_element.
   So we need to verify F(x) = x ** p is a ring homomorphism, meaning:
   (1) Ring r /\ prime p ==> GroupHomo (\x. x ** p) (ring_sum r) (ring_sum r)
       Expanding by GroupHomo_def, this is to show:
       Ring r /\ prime p /\ x IN R /\ x' IN R ==> (x + x') ** p = x ** p + x' ** p
       which is true by ring_freshman_thm.
   (2) Ring r ==> MonoidHomo (\x. x ** p) r.prod r.prod
       Expanding by MonoidHomo_def, this is to show:
       Ring r /\ prime p /\ x IN R /\ x' IN R ==> (x * x') ** p = x ** p * x' ** p
       which is true by ring_mult_exp.
*)
val ring_char_prime_endo = store_thm(
  "ring_char_prime_endo",
  ``!r:'a ring. Ring r /\ prime (char r) ==> RingEndo (\x. x ** (char r)) r``,
  rpt strip_tac >>
  rw[RingEndo_def, RingHomo_def] >| [
    rw[GroupHomo_def] >>
    metis_tac[ring_freshman_thm],
    rw[MonoidHomo_def, ring_mult_monoid]
  ]);

(* ------------------------------------------------------------------------- *)
(* Divisbility in Ring Documentation                                         *)
(* ------------------------------------------------------------------------- *)
(* Overloads:
   I             = i.carrier
   J             = j.carrier
   p rdivides q  = ring_divides r p q
   rassoc p q    = ring_associates r p q
   rprime p      = ring_prime r p
   rgcd p q      = ring_gcd r p q
   <a>           = principal_ideal r a
   <b>           = principal_ideal r b
   <u>           = principal_ideal r u
*)
(* Definitions and Theorems (# are exported):

   Ring Divisiblity:
   ring_divides_def     |- !r q p. q rdivides p <=> ?s. s IN R /\ (p = s * q)
   ring_associates_def  |- !r p q. rassoc p q <=> ?s. unit s /\ (p = s * q)
   ring_prime_def       |- !r p. rprime p <=> !a b. a IN R /\ b IN R /\ p rdivides a * b ==> p rdivides a \/ p rdivides b

   irreducible_associates |- !r. Ring r /\ #1 <> #0 ==> !p s. p IN R /\ unit s ==> (atom p <=> atom (s * p))
   irreducible_factors   |- !r z. atom z ==> z IN R+ /\ z NOTIN R* /\ !p. p IN R /\ p rdivides z ==> rassoc z p \/ unit p

   ring_divides_refl    |- !r. Ring r ==> !p. p IN R ==> p rdivides p
   ring_divides_trans   |- !r. Ring r ==> !p q t. p IN R /\ q IN R /\ t IN R /\ p rdivides q /\ q rdivides t ==> p rdivides t
   ring_divides_zero    |- !r. Ring r ==> !p. p IN R ==> p rdivides #0
   ring_zero_divides    |- !r. Ring r ==> !x. x IN R ==> (#0 rdivides x <=> (x = #0))
   ring_divides_by_one  |- !r. Ring r ==> !p. p IN R ==> #1 rdivides p
   ring_divides_by_unit |- !r. Ring r ==> !p t. p IN R /\ unit t ==> t rdivides p
   ring_factor_multiple |- !r. Ring r ==> !p q. p IN R /\ q IN R /\ (?k. k IN R /\ (p = k * q)) ==>
                           !z. z IN R /\ (?s. s IN R /\ (z = s * p)) ==> ?t. t IN R /\ (z = t * q)

   Euclidean Ring Greatest Common Divisor:
   ring_gcd_def          |- !r f p q. rgcd p q = if p = #0 then q else if q = #0 then p
                                  else (let s = {a * p + b * q | (a,b) | a IN R /\ b IN R /\ 0 < f (a * p + b * q)}
                                        in CHOICE (preimage f s (MIN_SET (IMAGE f s))))
   ring_gcd_zero         |- !r f p. (rgcd p #0 = p) /\ (rgcd #0 p = p)
   ring_gcd_linear       |- !r f. EuclideanRing r f ==> !p q. p IN R /\ q IN R ==>
                                  ?a b. a IN R /\ b IN R /\ (rgcd p q = a * p + b * q)
   ring_gcd_is_gcd       |- !r f. EuclideanRing r f ==> !p q. p IN R /\ q IN R ==>
                                  rgcd p q rdivides p /\ rgcd p q rdivides q /\
                                  !d. d IN R /\ d rdivides p /\ d rdivides q ==> d rdivides rgcd p q
   ring_gcd_divides      |- !r f. EuclideanRing r f ==> !p q. p IN R /\ q IN R ==> rgcd p q rdivides p /\ rgcd p q rdivides q
   ring_gcd_property     |- !r f. EuclideanRing r f ==> !p q. p IN R /\ q IN R ==>
                                  !d. d IN R /\ d rdivides p /\ d rdivides q ==> d rdivides rgcd p q
   ring_gcd_element      |- !r f. EuclideanRing r f ==> !p q. p IN R /\ q IN R ==> rgcd p q IN R
   ring_gcd_sym          |- !r f. EuclideanRing r f ==> !p q. p IN R /\ q IN R ==> (rgcd p q = rgcd q p)
   ring_irreducible_gcd  |- !r f. EuclideanRing r f ==> !p. p IN R /\ atom p ==> !q. q IN R ==> unit (rgcd p q) \/ p rdivides q

   ring_ordering_def     |- !r f. ring_ordering r f <=> !a b. a IN R /\ b IN R /\ b <> #0 ==> f a <= f (a * b)
   ring_divides_le       |- !r f. EuclideanRing r f /\ ring_ordering r f ==>
                                  !p q. p IN R /\ q IN R /\ p <> #0 /\ q rdivides p ==> f q <= f p

   Principal Ideal Ring: Irreducibles and Primes:
   principal_ideal_element_divides            |- !r. Ring r ==> !p. p IN R ==> !x. x IN <p>.carrier <=> p rdivides x
   principal_ideal_sub_implies_divides        |- !r. Ring r ==> !p q. p IN R /\ q IN R ==> (q rdivides p <=> <p> << <q>)
   principal_ideal_ring_atom_is_prime         |- !r. PrincipalIdealRing r ==> !p. atom p ==> rprime p
   principal_ideal_ring_irreducible_is_prime  |- !r. PrincipalIdealRing r ==> !p. atom p ==> rprime p
*)

(* ------------------------------------------------------------------------- *)
(* Ring Divisiblity                                                          *)
(* ------------------------------------------------------------------------- *)

(* The carrier of Ideal = carrier of group i.sum *)
val _ = temp_overload_on ("I", ``i.carrier``);
(* The carrier of Ideal = carrier of group j.sum *)
val _ = temp_overload_on ("J", ``j.carrier``);

(* Divides relation in ring *)
val ring_divides_def = Define `
  ring_divides (r:'a ring) (q:'a) (p:'a) =
    ?s:'a. s IN R /\ (p = s * q)
`;

(* Overload ring divides *)
val _ = overload_on ("rdivides", ``ring_divides r``);
val _ = set_fixity "rdivides" (Infix(NONASSOC, 450)); (* same as relation *)
(*
ring_divides_def;
> val it = |- !r q p. q | p <=> ?s. p = s * q : thm
*)

(* Define ring associates *)
val ring_associates_def = Define `
  ring_associates (r:'a ring) (p:'a) (q:'a) =
  ?s:'a. unit s /\ (p = s * q)
`;
(* Overload ring associates *)
val _ = overload_on ("rassoc", ``ring_associates r``);
(*
- ring_associates_def;
> val it = |- !r p q. rassoc p q <=> ?s. unit s /\ (p = s * q) : thm
*)

(* Define prime in ring *)
val ring_prime_def = Define `
  ring_prime (r:'a ring) (p:'a) =
  !a b. a IN R /\ b IN R /\ p rdivides a * b ==> (p rdivides a) \/ (p rdivides b)
`;
(* Overload prime in ring *)
val _ = overload_on ("rprime", ``ring_prime r``);
(*
- ring_prime_def;
> val it = |- !r p. rprime p <=> !a b. a IN R /\ b IN R /\ p rdivides a * b ==> p rdivides a \/ p rdivides b : thm
*)

(* Theorem: Ring r /\ #1 <> #0 ==> p IN R /\ unit s ==> atom p <=> atom (s * p) *)
(* Proof:
   If part: atom p /\ unit s ==> atom (s * p)
   unit s ==> unit ( |/ s)   by ring_unit_has_inv
   and |/s IN R              by ring_unit_element
     |/s * (s * p)
   = ( |/s * s) * p          by ring_mult_assoc
   = #1 * p                  by ring_unit_linv
   = p                       by ring_mult_lone
   Since p <> #0             by irreducible_def, ring_nonzero_eq
   s * p <> #0               by ring_mult_rzero
   so s * p IN R+            by ring_nonzero_eq
   By irreducible_def, still more to show:
   (1) unit s /\ atom p ==> s * p NOTIN R*
       By contradiction, assume unit (s * p)
       Since Group r*                 by ring_units_group
           unit ( |/s) and unit (s * p)
       ==> unit ( |/s * (s * p))      by group_op_element
       ==> unit p                     by above
       which contradicts atom p       by irreducible_def
   (2) atom p /\ s * p = x * y ==> unit x \/ unit y
       |/s * (s * p) = |/s * (x * y)
       p = ( |/s * x) * y             by ring_mult_assoc
       Since atom p
       this means unit ( |/s * x) or unit y
                                      by irreducible_def
       If unit ( |/s * x)
       Since Group r*                 by ring_units_group
          unit s and unit ( |/s * x)
       ==> unit (s * |/s * x)         by group_op_element
       ==> unit (#1 * x) ==> unit x
       If unit y, this is trivial.
   Only-if part: p IN R /\ unit s /\ atom (s * p) ==> atom p /\ unit s
     unit s ==> s IN R                by ring_unit_element
     atom (p * s) ==> p * s <> #0     by irreducible_def
     hence p <> #0                    by ring_mult_rzero
     or p IN R+                       by ring_nonzero_eq
   By irreducible_def, still more to show:
   (1) unit s /\ atom (s * p) ==> p NOTIN R*
       By contradiction, assume unit p
       Since Group r*                 by ring_units_group
           unit s and unit p
       ==> unit (s * p)               by group_op_element
       which contradicts atom (s * p) by irreducible_def
   (2) unit s /\ atom (s * (x * y)) ==> unit x \/ unit y
       s * (x * y) = (s * x) * y      by ring_mult_assoc
       Since atom (s * (x * y))
       this means unit (s * x) or unit y
                                      by irreducible_def
       If unit (s * x)
       Since Group r*                 by ring_units_group
          unit ( |/s) and unit (s * x)
       ==> unit ( |/s * (s * x))      by group_op_element
       ==> unit (#1 * x) ==> unit x
       If unit y, this is trivial.
*)
val irreducible_associates = store_thm(
  "irreducible_associates",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p s. p IN R /\ unit s ==> (atom p <=> atom (s * p))``,
  rw[EQ_IMP_THM] >| [
    `unit ((Invertibles r.prod).inv s)` by rw[ring_unit_has_inv] >>
    `s IN R` by rw[ring_unit_element] >>
    `s * p IN R /\ (Invertibles r.prod).inv s IN R` by rw[ring_unit_element] >>
    `((Invertibles r.prod).inv s) * (s * p) = ((Invertibles r.prod).inv s) * s * p` by rw[ring_mult_assoc] >>
    `_ = #1 * p` by rw[ring_unit_linv] >>
    `_ = p` by rw[] >>
    `p <> #0` by metis_tac[irreducible_def, ring_nonzero_eq] >>
    `s * p <> #0` by metis_tac[ring_mult_rzero] >>
    `s * p IN R+` by rw[ring_nonzero_eq] >>
    rw[irreducible_def] >| [
      spose_not_then strip_assume_tac >>
      `Group r*` by rw[ring_units_group] >>
      `unit (((Invertibles r.prod).inv s) * (s * p))` by metis_tac[group_op_element, ring_units_property] >>
      metis_tac[irreducible_def],
      `((Invertibles r.prod).inv s) * (x * y) = ((Invertibles r.prod).inv s) * x * y` by rw[ring_mult_assoc] >>
      `((Invertibles r.prod).inv s) * x IN R` by rw[] >>
      `unit (((Invertibles r.prod).inv s) * x) \/ unit y` by metis_tac[irreducible_def] >| [
        `Group r*` by rw[ring_units_group] >>
        `unit (s * (((Invertibles r.prod).inv s) * x))` by metis_tac[group_op_element, ring_units_property] >>
        `s * (((Invertibles r.prod).inv s) * x) = s * ((Invertibles r.prod).inv s) * x` by rw[ring_mult_assoc] >>
        `_ = #1 * x` by rw[ring_unit_rinv] >>
        `_ = x` by rw[] >>
        metis_tac[],
        rw[]
      ]
    ],
    `s IN R` by rw[ring_unit_element] >>
    `p IN R+` by metis_tac[ring_mult_rzero, irreducible_def, ring_nonzero_eq] >>
    rw[irreducible_def] >| [
      spose_not_then strip_assume_tac >>
      `Group r*` by rw[ring_units_group] >>
      `unit (s * p)` by metis_tac[group_op_element, ring_units_property] >>
      metis_tac[irreducible_def],
      `s * (x * y) = s * x * y` by rw[ring_mult_assoc] >>
      `s * x IN R` by rw[] >>
      `unit (s * x) \/ unit y` by metis_tac[irreducible_def] >| [
        `Group r*` by rw[ring_units_group] >>
        `unit ((Invertibles r.prod).inv s)` by rw[ring_unit_has_inv] >>
        `unit (((Invertibles r.prod).inv s) * (s * x))` by metis_tac[group_op_element, ring_units_property] >>
        `(Invertibles r.prod).inv s IN R` by rw[ring_unit_element] >>
        `((Invertibles r.prod).inv s) * (s * x) = ((Invertibles r.prod).inv s) * s * x` by rw[ring_mult_assoc] >>
        `_ = #1 * x` by rw[ring_unit_linv] >>
        `_ = x` by rw[] >>
        metis_tac[],
        rw[]
      ]
    ]
  ]);

(* Theorem: atom z ==> z IN R+ /\ ~(unit z) /\ (!p. p IN R /\ p rdivides z ==> (rassoc z p) \/ unit p) *)
(* Proof:
       p rdivides z
   ==> ?s. s IN R /\ (z = s * p)    by ring_divides_def
   ==> unit s \/ unit p             by irreducible_def
   If unit s, rassoc z p            by ring_associates_def
   If unit p, trivially true.
*)
val irreducible_factors = store_thm(
  "irreducible_factors",
  ``!r:'a ring. !z. atom z ==> z IN R+ /\ ~(unit z) /\ (!p. p IN R /\ p rdivides z ==> (rassoc z p) \/ unit p)``,
  rw[irreducible_def] >>
  `?s. s IN R /\ (z = s * p)` by rw[GSYM ring_divides_def] >>
  `unit s \/ unit p` by rw[] >-
  metis_tac[ring_associates_def] >>
  rw[]);

(* Theorem: p rdivides p *)
(* Proof:
   Since #1 * p = p      by ring_mult_lone
   p rdivides p          by ring_divides_def
*)
val ring_divides_refl = store_thm(
  "ring_divides_refl",
  ``!r:'a ring. Ring r ==> !p. p IN R ==> p rdivides p``,
  rw[ring_divides_def] >>
  metis_tac[ring_mult_lone, ring_one_element]);

(* Theorem: p rdivides q /\ q rdivides p ==> p = q *)
(* Proof:
*)

(* Theorem: p rdivides q /\ q rdivides t ==> p rdivides t *)
(* Proof:
   p rdivides q ==> ?s. s IN R /\ q = s * p     by ring_divides_def
   q rdivides t ==> ?s'. s' IN R /\ t = s' * q  by ring_divides_def
   Hence t = s' * (s * p)
           = (s' * s) * p                       by ring_mult_assoc
   Since s' * s IN R                            by ring_mult_element
   p rdivides t                                 by ring_divides_def
*)
val ring_divides_trans = store_thm(
  "ring_divides_trans",
  ``!r:'a ring. Ring r ==> !p q t. p IN R /\ q IN R /\ t IN R /\ p rdivides q /\ q rdivides t ==> p rdivides t``,
  rw[ring_divides_def] >>
  `s' * (s * p) = s' * s * p` by rw[ring_mult_assoc] >>
  metis_tac[ring_mult_element]);

(* Theorem: p rdivides #0 *)
(* Proof:
   Since #0 = #0 * p     by ring_mult_lzero
   Hence p rdivides #0   by ring_divides_def
*)
val ring_divides_zero = store_thm(
  "ring_divides_zero",
  ``!r:'a ring. Ring r ==> !p. p IN R ==> p rdivides #0``,
  rw[] >>
  metis_tac[ring_divides_def, ring_mult_lzero, ring_zero_element]);

(* Theorem: Ring r ==> !x. x IN R ==> (#0 rdivides x <=> (x = #0)) *)
(* Proof:
       #0 rdivides x
   <=> ?s. s IN R /\ (x = s * #0)    by ring_divides_def
   <=> ?s. s IN R /\ (x = #0)        by ring_mult_rzero
   <=> x = #0
*)
val ring_zero_divides = store_thm(
  "ring_zero_divides",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> (#0 rdivides x <=> (x = #0))``,
  metis_tac[ring_divides_def, ring_mult_rzero]);

(* Theorem: #1 rdivides p *)
(* Proof:
   Since p = p * #1   by ring_mult_rone
   Hence true         by ring_divides_def
*)
val ring_divides_by_one = store_thm(
  "ring_divides_by_one",
  ``!r:'a ring. Ring r ==> !p. p IN R ==> #1 rdivides p``,
  metis_tac[ring_divides_def, ring_mult_rone]);

(* Theorem: unit t ==> t rdivides p *)
(* Proof:
   unit t ==> |/t IN R        by ring_unit_inv_element
   Since p = p * #1           by ring_mult_rone
           = p * ( |/ t * t)  by ring_unit_linv
           = (p * |/t) * t    by ring_mult_assoc
   Hence true                 by ring_divides_def
*)
val ring_divides_by_unit = store_thm(
  "ring_divides_by_unit",
  ``!r:'a ring. Ring r ==> !p t. p IN R /\ unit t ==> t rdivides p``,
  rpt strip_tac >>
  `|/t IN R /\ p * |/t IN R` by rw[ring_unit_inv_element] >>
  `p = p * #1` by rw[] >>
  `_ = p * ( |/t * t)` by rw[ring_unit_linv] >>
  `_ = p * |/t * t` by rw[ring_mult_assoc] >>
  metis_tac[ring_divides_def]);

(* Theorem: p = k * q ==> z = s * p ==> z = t * q *)
(* Proof:
   z = s * p           by given
     = s * (k * q)     by given
     = (s * k) * q     by ring_mult_assoc
   So let t = s * k, then z = t * q
*)
val ring_factor_multiple = store_thm(
  "ring_factor_multiple",
  ``!r:'a ring. Ring r ==> !p q. p IN R /\ q IN R /\ (?k. k IN R /\ (p = k * q)) ==>
     !z. z IN R /\ (?s. s IN R /\ (z = s * p)) ==> (?t. t IN R /\ (z = t * q))``,
  rpt strip_tac >>
  qexists_tac `s * k` >>
  rw[ring_mult_assoc]);

Theorem ring_prime_divides_product:
  !r. Ring r ==>
  !p. p IN r.carrier ==>
    (ring_prime r p /\ ~Unit r p <=>
     (!b. FINITE_BAG b /\ SET_OF_BAG b SUBSET r.carrier /\
          ring_divides r p (GBAG r.prod b) ==>
          ?x. BAG_IN x b /\ ring_divides r p x))
Proof
  rpt strip_tac
  \\ reverse eq_tac
  >- (
    strip_tac
    \\ conj_tac
    >- (
      rw[ring_prime_def]
      \\ first_x_assum(qspec_then`{|a; b|}`mp_tac)
      \\ simp[SUBSET_DEF]
      \\ DEP_REWRITE_TAC[GBAG_INSERT]
      \\ simp[SUBSET_DEF]
      \\ dsimp[]
      \\ metis_tac[Ring_def])
    \\ strip_tac
    \\ `ring_divides r p r.prod.id`
    by (
      rfs[ring_unit_property, ring_divides_def]
      \\ metis_tac[ring_mult_comm] )
    \\ first_x_assum(qspec_then`{||}`mp_tac)
    \\ simp[] )
  \\ strip_tac
  \\ simp[Once(GSYM AND_IMP_INTRO)]
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ simp[]
  \\ simp[Once ring_divides_def]
  \\ conj_tac >- metis_tac[ring_unit_property, ring_mult_comm]
  \\ rpt strip_tac
  \\ fs[SUBSET_DEF]
  \\ pop_assum mp_tac
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ fs[SUBSET_DEF]
  \\ conj_asm1_tac >- metis_tac[Ring_def]
  \\ fs[ring_prime_def]
  \\ `GBAG r.prod b IN r.prod.carrier`
  by ( irule GBAG_in_carrier \\ fs[SUBSET_DEF] )
  \\ rfs[] \\ strip_tac
  \\ `e IN r.carrier` by metis_tac[]
  \\ first_x_assum(drule_then (drule_then drule))
  \\ metis_tac[]
QED

Theorem ring_product_factors_divide:
  !r. Ring r ==>
  !b. FINITE_BAG b ==>
      SET_OF_BAG b SUBSET r.carrier /\
      ring_divides r (GBAG r.prod b) x ==>
      !y. BAG_IN y b ==> ring_divides r y x
Proof
  ntac 2 strip_tac
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ simp[]
  \\ gen_tac \\ strip_tac
  \\ gen_tac \\ strip_tac
  \\ pop_assum mp_tac
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ fs[SUBSET_DEF]
  \\ conj_asm1_tac >- metis_tac[Ring_def]
  \\ gs[ring_divides_def, PULL_EXISTS]
  \\ gen_tac \\ strip_tac
  \\ BasicProvers.VAR_EQ_TAC
  \\ last_x_assum(qspec_then`s * e`mp_tac)
  \\ simp[]
  \\ `GBAG r.prod b IN r.prod.carrier`
  by ( irule GBAG_in_carrier \\ simp[SUBSET_DEF] )
  \\ rfs[]
  \\ simp[ring_mult_assoc]
  \\ strip_tac
  \\ strip_tac
  \\ strip_tac
  >- (
    qexists_tac`s * GBAG r.prod b`
    \\ simp[ring_mult_assoc]
    \\ AP_TERM_TAC
    \\ simp[ring_mult_comm] )
  \\ res_tac
  \\ simp[]
QED

Theorem ring_mult_divides:
  !r p q x.
    Ring r /\ ring_divides r (r.prod.op p q) x /\
    p IN R /\ q IN R
    ==>
    ring_divides r p x /\ ring_divides r q x
Proof
  rpt strip_tac
  \\ drule ring_product_factors_divide
  \\ disch_then(qspecl_then[`x`,`{|p;q|}`]mp_tac)
  \\ simp[SUBSET_DEF]
  \\ dsimp[]
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[]
  \\ metis_tac[Ring_def]
QED

Theorem ring_associates_sym:
  !r p q.
    Ring r /\ q IN r.carrier /\ ring_associates r p q ==>
    ring_associates r q p
Proof
  rw[ring_associates_def]
  \\ rfs[ring_unit_property]
  \\ simp[PULL_EXISTS]
  \\ qexists_tac`v`
  \\ qexists_tac`s`
  \\ simp[]
  \\ simp[Once ring_mult_comm]
  \\ simp[GSYM ring_mult_assoc]
  \\ metis_tac[ring_mult_comm, ring_mult_lone]
QED

Theorem ring_associates_trans:
  !r x y z.
    Ring r /\ z IN r.carrier /\
    ring_associates r x y /\
    ring_associates r y z ==>
    ring_associates r x z
Proof
  rw[ring_associates_def]
  \\ qexists_tac`s * s'`
  \\ simp[ring_mult_assoc]
  \\ simp[ring_unit_mult_unit]
QED

Theorem ring_associates_refl:
  !r x. Ring r /\ x IN r.carrier ==> ring_associates r x x
Proof
  rw[ring_associates_def]
  \\ qexists_tac`#1`
  \\ simp[]
QED

Theorem ring_associates_mult:
  !r p q x.
    Ring r /\ p IN r.carrier /\ q IN r.carrier /\ x IN r.carrier /\
    ring_associates r p q ==>
    ring_associates r (r.prod.op x p) (r.prod.op x q)
Proof
  rw[ring_associates_def]
  \\ rfs[ring_unit_property]
  \\ simp[PULL_EXISTS]
  \\ qexistsl_tac[`s`,`v`]
  \\ simp[GSYM ring_mult_assoc]
  \\ metis_tac[ring_mult_comm]
QED

Theorem ring_associates_divides:
  !r p q x. Ring r /\ ring_associates r p q /\ q IN R /\
  ring_divides r p x ==> ring_divides r q x
Proof
  rw[ring_associates_def, ring_divides_def]
  \\ qexists_tac`s' * s`
  \\ simp[]
  \\ simp[ring_mult_assoc]
QED

Theorem ring_divides_associates:
  !r x y p. Ring r /\ ring_associates r x y /\ p IN R /\ y IN R /\ ring_divides r p x ==>
  ring_divides r p y
Proof
  rw[ring_associates_def, ring_divides_def]
  \\ qexists_tac`|/ s * s'`
  \\ simp[ring_unit_inv_element, ring_mult_assoc]
  \\ simp[ring_unit_inv_element, GSYM ring_mult_assoc]
  \\ simp[ring_unit_linv]
QED

Theorem LIST_REL_ring_associates_product:
  Ring r ==>
  !l1 l2. LIST_REL (ring_associates r) l1 l2 /\
          set l2 SUBSET r.carrier
          ==>
          ring_associates r (GBAG r.prod (LIST_TO_BAG l1))
                            (GBAG r.prod (LIST_TO_BAG l2))
Proof
  strip_tac
  \\ Induct_on`LIST_REL`
  \\ rw[]
  >- ( simp[ring_associates_def] \\ qexists_tac`#1` \\ simp[] )
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[]
  \\ fs[SUBSET_DEF, IN_LIST_TO_BAG]
  \\ conj_asm1_tac >- (
    fs[LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS]
    \\ fs[ring_associates_def]
    \\ reverse conj_tac >- metis_tac[Ring_def]
    \\ rw[] \\ res_tac \\ rfs[]
    \\ res_tac \\ fs[] )
  \\ irule ring_associates_trans
  \\ simp[]
  \\ `GBAG r.prod (LIST_TO_BAG l2) IN r.prod.carrier` by (
    irule GBAG_in_carrier
    \\ simp[SUBSET_DEF, IN_LIST_TO_BAG] )
  \\ `GBAG r.prod (LIST_TO_BAG l1) IN r.prod.carrier` by (
    irule GBAG_in_carrier
    \\ simp[SUBSET_DEF, IN_LIST_TO_BAG] )
  \\ conj_tac >- ( irule ring_mult_element \\ rfs[] )
  \\ qexists_tac`h2 * GBAG r.prod (LIST_TO_BAG l1)`
  \\ reverse conj_tac
  >- ( irule ring_associates_mult \\ rfs[] )
  \\ DEP_ONCE_REWRITE_TAC[ring_mult_comm] \\ rfs[]
  \\ qmatch_goalsub_abbrev_tac`rassoc foo _`
  \\ DEP_ONCE_REWRITE_TAC[ring_mult_comm] \\ rfs[]
  \\ qunabbrev_tac`foo`
  \\ irule ring_associates_mult \\ rfs[]
QED

(* ------------------------------------------------------------------------- *)
(* Euclidean Ring Greatest Common Divisor                                    *)
(* ------------------------------------------------------------------------- *)

(* Define greatest common divisor *)
val ring_gcd_def = Define`
  ring_gcd (r:'a ring) (f:'a -> num) (p:'a) (q:'a) =
   if p = #0 then q
   else if q = #0 then p
   else let s = {a * p + b * q | (a, b) | a IN R /\ b IN R /\ 0 < f (a * p + b * q) }
         in CHOICE (preimage f s (MIN_SET (IMAGE f s)))
`;

(* Overload ring gcd *)
val _ = overload_on ("rgcd", ``ring_gcd r f``);
(*
- ring_gcd_def;
> val it = |- !r f p q. rgcd p q = if p = #0 then q else if q = #0 then p else
              (let s = {a * p + b * q | (a,b) | a IN R /\ b IN R /\ 0 < f (a * p + b * q)}
                in CHOICE (preimage f s (MIN_SET (IMAGE f s)))) : thm
*)

(* Theorem: !p. (rgcd p #0 = p) /\ (rgcd #0 p = p) *)
(* Proof: by ring_gcd_def *)
val ring_gcd_zero = store_thm(
  "ring_gcd_zero",
  ``!(r:'a ring) (f :'a -> num). !p. (rgcd p #0 = p) /\ (rgcd #0 p = p)``,
  rw[ring_gcd_def]);

(* Theorem: EuclideanRing r f ==> !p q. p IN R /\ q IN R ==>
            (?a b. a IN R /\ b IN R /\ (rgcd p q = a * p + b * q)) *)
(* Proof:
   If p = #0, rgcd p q = q = #0 * p + #1 * q.
   If q = #0, rgcd p q = p = #1 * p + #0 * q.
   If p <> #0 and q <> #0, by ring_gcd_def,
   rgcd p q = CHOICE (preimage f s (MIN_SET (IMAGE f s)))
   where s = {a * p + b * q | (a, b) | a IN R /\ b IN R /\ 0 < f (a * p + b * q) }
   Since p = #1 * p + #0 * q,
   and with p <> #0, f p <> 0                by euclid_ring_map
   Hence s <> {},
    and  IMAGE f s <> {}                     by IMAGE_EMPTY
    and  MIN_SET (IMAGE f s) IN (IMAGE f s)  by MIN_SET_LEM
   Thus CHOICE (preimage f s (MIN_SET (IMAGE f s))) IN s  by preimage_choice_property
     or rgcd p q IN s                        by IN_IMAGE
     or ?a b. a IN R /\ b IN R /\ (rgcd p q = a * p + b * q).
*)
val ring_gcd_linear = store_thm(
  "ring_gcd_linear",
  ``!(r:'a ring) (f:'a -> num). EuclideanRing r f ==>
     !p q. p IN R /\ q IN R ==> ?a b. a IN R /\ b IN R /\ (rgcd p q = a * p + b * q)``,
  rpt strip_tac >>
  `Ring r` by metis_tac[euclid_ring_ring] >>
  `#0 IN R /\ #1 IN R` by rw[] >>
  `p = #1 * p + #0 * q` by rw[] >>
  `q = #0 * p + #1 * q` by rw[] >>
  Cases_on `p = #0` >-
  metis_tac[ring_gcd_def] >>
  Cases_on `q = #0` >-
  metis_tac[ring_gcd_def] >>
  qabbrev_tac `s = {a * p + b * q | (a, b) | a IN R /\ b IN R /\ 0 < f (a * p + b * q) }` >>
  `rgcd p q = CHOICE (preimage f s (MIN_SET (IMAGE f s)))` by rw[ring_gcd_def] >>
  `!z. z IN s <=> ?a b. (z = a * p + b * q) /\ a IN R /\ b IN R /\ 0 < f (a * p + b * q)` by rw[Abbr`s`] >>
  `f p <> 0` by metis_tac[euclid_ring_map] >>
  `p IN s` by metis_tac[DECIDE ``!n. n <> 0 ==> 0 < n``] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `IMAGE f s <> {}` by rw[IMAGE_EMPTY] >>
  `MIN_SET (IMAGE f s) IN (IMAGE f s)` by rw[MIN_SET_LEM] >>
  `CHOICE (preimage f s (MIN_SET (IMAGE f s))) IN s` by rw[preimage_choice_property] >>
  metis_tac[]);

(* Theorem: EuclideanRing r f ==> rgcd p q rdivides p /\ rgcd p q rdivides q /\
            !d. d IN R /\ d rdivides p /\ d rdivides q ==> d rdivides rgcd p q *)
(* Proof:
   If p = #0, rgcd #0 q = q        by ring_gcd_def
      rgcd #0 q rdivides #0        by ring_divides_zero
      rgcd #0 q rdivides q         by ring_divides_refl
      d rdivides q ==> d rdivides rgcd #0 q = q is trivial.
   If q = #0, rgcd p #0 = p        by ring_gcd_def
      rgcd p #0 rdivides p         by ring_divides_refl
      rgcd p #0 rdivides #0        by ring_divides_zero
      d rdivides p ==> d rdivides rgcd p #0 = p is trivial.
   If p <> #0 and q <> #0,
      Let s = {a * p + b * q | (a, b) | a IN R /\ b IN R /\ 0 < f (a * p + b * q) }
      Then rgcd p q = CHOICE (preimage f s (MIN_SET (IMAGE f s)))  by ring_gcd_def
      Since p = #1 * p + #0 * q
        and p <> #0 ==> f p <> 0   by euclid_ring_map
      hence p IN s                 by SPECIIFICATION
         or s <> {}                by MEMBER_NOT_EMPTY
        and IMAGE f s <> {}        by IMAGE_EMPTY
      Therefore, by MIN_SET_LEM,
            MIN_SET (IMAGE f s) IN (IMAGE f s)
        and !x. x IN (IMAGE f s) ==> MIN_SET (IMAGE f s) <= x
      Also, by preimage_choice_property,
            CHOICE (preimage f s (MIN_SET (IMAGE f s))) IN s /\
            f (CHOICE (preimage f s (MIN_SET (IMAGE f s)))) = MIN_SET (IMAGE f s)
      Hence,
          rgcd p q IN s /\ f (rgcd p q) = MIN_SET (IMAGE f s)
      and ?a b. a IN R /\ b IN R /\ (rgcd p q = a * p + b * q)
      Let g = rgcd p q
      Then by g IN s, 0 < f g
      Hence   g <> #0              by euclid_ring_map
      Also    g IN R               by ring_mult_element, ring_add_element
      Now for each of the goals:
      (1) g rdivides p
          Divide p by g,
          ?u t. u IN R /\ t IN R /\ (p = u * g + t) /\ f t < f g  by euclid_ring_property
          If t = #0, g rdivides p is true.
          If t <> #0, f t <> 0     by euclid_ring_map
          and t = p - u * g        by ring_sub_eq_add
                = p - u * (a * p + b * q)
                = #1 * p + - (u * a) * p + - (u * b) * q
                = (#1 + - (u * a)) * p + - (u * b) * q
          Hence t IN s
             so f t IN IMAGE f s          by IN_IMAGE
           thus f g <= f t                from MIN_SET
           which contradicts f t < f g    from euclid_ring_property
      (2) g rdivides q
          Divide q by g,
          ?u t. u IN R /\ t IN R /\ (q = u * g + t) /\ f t < f g  by euclid_ring_property
          If t = #0, g rdivides q is true.
          If t <> #0, f t <> 0     by euclid_ring_map
          and t = q - u * g        by ring_sub_eq_add
                = q - u * (a * p + b * q)
                = - u * (a * p + b * q) + q
                = - (u * b) * q + - (u * a) * p + #1 * q
                = - (u * a) * p + (#1 + - (u * b)) * q
          Hence t IN s
             so f t IN IMAGE f s          by IN_IMAGE
           thus f g <= f t                from MIN_SET
           which contradicts f t < f g    from euclid_ring_property
      (3) d rdivides p /\ d rdivides q ==> d rdivides g
          d rdivides p ==> ?u. u IN R /\ (p = u * d)    by ring_divides_def
          d rdivides q ==> ?v. v IN R /\ (q = v * d)    by ring_divides_def
          g = a * p + b * q
            = a * (u * d) + b * (v * d)
            = a * u * d + b * v * d       by ring_mult_assoc
            = (a * u + b * v) * d         by ring_mult_ladd
          Hence d rdivides g              by ring_divides_def
*)
val ring_gcd_is_gcd = store_thm(
  "ring_gcd_is_gcd",
  ``!(r:'a ring) (f:'a -> num). EuclideanRing r f ==> !p q. p IN R /\ q IN R ==>
      rgcd p q rdivides p /\ rgcd p q rdivides q /\
      (!d. d IN R /\ d rdivides p /\ d rdivides q ==> d rdivides rgcd p q)``,
  ntac 6 strip_tac >>
  `Ring r` by metis_tac[euclid_ring_ring] >>
  Cases_on `p = #0` >-
  rw[ring_gcd_def, ring_divides_zero, ring_divides_refl] >>
  Cases_on `q = #0` >-
  rw[ring_gcd_def, ring_divides_zero, ring_divides_refl] >>
  qabbrev_tac `s = {a * p + b * q | (a, b) | a IN R /\ b IN R /\ 0 < f (a * p + b * q) }` >>
  `rgcd p q = CHOICE (preimage f s (MIN_SET (IMAGE f s)))` by rw[ring_gcd_def] >>
  `#0 IN R /\ #1 IN R` by rw[] >>
  `p = #1 * p + #0 * q` by rw[] >>
  `!z. z IN s <=> ?a b. (z = a * p + b * q) /\ a IN R /\ b IN R /\ 0 < f (a * p + b * q)` by rw[Abbr`s`] >>
  `f p <> 0` by metis_tac[euclid_ring_map] >>
  `p IN s` by metis_tac[DECIDE ``!n. n <> 0 ==> 0 < n``] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `IMAGE f s <> {}` by rw[IMAGE_EMPTY] >>
  `MIN_SET (IMAGE f s) IN (IMAGE f s) /\ !x. x IN (IMAGE f s) ==> MIN_SET (IMAGE f s) <= x` by rw[MIN_SET_LEM] >>
  `CHOICE (preimage f s (MIN_SET (IMAGE f s))) IN s /\
    (f (CHOICE (preimage f s (MIN_SET (IMAGE f s)))) = MIN_SET (IMAGE f s))` by rw[preimage_choice_property] >>
  `rgcd p q IN s /\ (f (rgcd p q) = MIN_SET (IMAGE f s))` by metis_tac[] >>
  `?a b. a IN R /\ b IN R /\ (rgcd p q = a * p + b * q)` by metis_tac[] >>
  qabbrev_tac `g = rgcd p q` >>
  `0 < f g` by metis_tac[] >>
  `g <> #0` by metis_tac[euclid_ring_map, DECIDE ``!n. n < 0 ==> n <> 0``] >>
  `g IN R` by rw[] >>
  rpt strip_tac >| [
    `?u t. u IN R /\ t IN R /\ (p = u * g + t) /\ f t < f g` by rw[euclid_ring_property] >>
    `u * g IN R /\ a * p IN R /\ b * q IN R` by rw[] >>
    Cases_on `t = #0` >-
    metis_tac[ring_divides_def, ring_add_rzero, ring_mult_comm] >>
    `f t <> 0` by metis_tac[euclid_ring_map] >>
    `t IN s` by
  (`t = p - u * g` by metis_tac[ring_sub_eq_add] >>
    `_ = p - u * (a * p + b * q)` by rw[] >>
    `_ = p - (u * (a * p) + u * (b * q))` by rw_tac std_ss[ring_mult_radd] >>
    `_ = p - (u * a * p + u * b * q)` by rw_tac std_ss[ring_mult_assoc] >>
    `_ = p + (- (u * a * p + u * b * q))` by rw_tac std_ss[ring_sub_def] >>
    `_ = p + (- (u * a * p) + - (u * b * q))` by rw_tac std_ss[ring_neg_add, ring_mult_element] >>
    `_ = p + - (u * a * p) + - (u * b * q)` by rw_tac std_ss[ring_add_assoc, ring_mult_element, ring_neg_element] >>
    `_ = p + - (u * a) * p + - (u * b) * q` by rw_tac std_ss[ring_neg_mult, ring_mult_element] >>
    `_ = #1 * p + - (u * a) * p + - (u * b) * q` by rw_tac std_ss[ring_mult_lone] >>
    `_ = (#1 + - (u * a)) * p + - (u * b) * q` by rw_tac std_ss[ring_mult_ladd, ring_mult_element, ring_neg_element] >>
    `(#1 + - (u * a)) IN R /\ - (u * b) IN R` by rw[] >>
    metis_tac[DECIDE ``!n. n <> 0 ==> 0 < n``]) >>
    `f t IN IMAGE f s` by rw[] >>
    `f g <= f t` by metis_tac[] >>
    `!n m. n < m ==> ~(m <= n)` by decide_tac >>
    metis_tac[],
    `?u t. u IN R /\ t IN R /\ (q = u * g + t) /\ f t < f g` by rw[euclid_ring_property] >>
    `u * g IN R /\ a * p IN R /\ b * q IN R` by rw[] >>
    Cases_on `t = #0` >-
    metis_tac[ring_divides_def, ring_add_rzero, ring_mult_comm] >>
    `f t <> 0` by metis_tac[euclid_ring_map] >>
    `t IN s` by
  (`t = q - u * g` by metis_tac[ring_sub_eq_add] >>
    `_ = - (u * g) + q` by rw_tac std_ss[ring_sub_def, ring_add_comm, ring_neg_element] >>
    `_ = - u * g + q` by rw_tac std_ss[ring_neg_mult] >>
    `_ = - u * (a * p + b * q) + q` by rw[] >>
    `_ = - u * (a * p) + - u * (b * q) + q` by rw_tac std_ss[ring_mult_radd, ring_neg_element] >>
    `_ = - u * a * p + - u * b * q + q` by rw_tac std_ss[ring_mult_assoc, ring_neg_element] >>
    `_ = - u * a * p + (- u * b * q + q)` by rw_tac std_ss[ring_add_assoc, ring_mult_element, ring_neg_element] >>
    `_ = - u * a * p + (- u * b * q + #1 * q)` by rw_tac std_ss[ring_mult_lone] >>
    `_ = - u * a * p + (- u * b + #1) * q` by rw_tac std_ss[ring_mult_ladd, ring_mult_element, ring_neg_element] >>
    `- u * a  IN R /\ (- u * b + #1) IN R` by rw[] >>
    metis_tac[DECIDE ``!n. n <> 0 ==> 0 < n``]) >>
    `f t IN IMAGE f s` by rw[] >>
    `f g <= f t` by metis_tac[] >>
    `!n m. n < m ==> ~(m <= n)` by decide_tac >>
    metis_tac[],
    `?u. u IN R /\ (p = u * d)` by rw[GSYM ring_divides_def] >>
    `?v. v IN R /\ (q = v * d)` by rw[GSYM ring_divides_def] >>
    `g = a * (u * d) + b * (v * d)` by rw[] >>
    `_ = a * u * d + b * v * d` by rw[ring_mult_assoc] >>
    `_ = (a * u + b * v) * d` by rw[ring_mult_ladd] >>
    `a * u + b * v IN R` by rw[] >>
    metis_tac[ring_divides_def]
  ]);

(* Theorem: rgcd p q rdivides p /\ rgcd p q rdivides q *)
val ring_gcd_divides = save_thm("ring_gcd_divides",
  (CONJ (ring_gcd_is_gcd |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1)
        (ring_gcd_is_gcd |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT2 |> CONJUNCT1))
        |> DISCH ``p IN R /\ q IN R`` |> GEN ``q`` |> GEN ``p`` |> DISCH_ALL |> GEN_ALL);
(* > val ring_gcd_divides = |- !r f. EuclideanRing r f ==>
         !p q. p IN R /\ q IN R ==> rgcd p q rdivides p /\ rgcd p q rdivides q : thm *)

(* Theorem: d rdivides p /\ d rdivides q ==> d rdivides (rgcd p q) *)
val ring_gcd_property = save_thm("ring_gcd_property",
  ring_gcd_is_gcd |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCTS |> last
        |> DISCH ``p IN R /\ q IN R`` |> GEN ``q`` |> GEN ``p`` |> DISCH_ALL |> GEN_ALL);
(* > val ring_gcd_property = |- !r f. EuclideanRing r f ==>
         !p q. p IN R /\ q IN R ==> !d. d IN R /\ d rdivides p /\ d rdivides q ==> d rdivides rgcd p q : thm *)

(* Theorem: p IN R /\ q IN R ==> rgcd p q IN R *)
(* Proof:
   ?a b. a IN R /\ b IN R /\ (rgcd p q = a * p + b * q)  by ring_gcd_linear
   Hence (rgcd p q) IN R                                 by ring_mult_element, ring_add_element
*)
val ring_gcd_element = store_thm(
  "ring_gcd_element",
  ``!(r:'a ring) (f:'a -> num). EuclideanRing r f ==> !p q. p IN R /\ q IN R ==> rgcd p q IN R``,
  rpt strip_tac >>
  `Ring r` by metis_tac[euclid_ring_ring] >>
  `?a b. a IN R /\ b IN R /\ (rgcd p q = a * p + b * q)` by rw[ring_gcd_linear] >>
  rw[]);

(* Theorem: rgcd p q = rgcd q p *)
(* Proof:
   If p = #0,
   LHS = rgcd #0 q = q = rgcd q #0 = RHS    by ring_gcd_def
   If q = #0,
   LHS = rgcd p #0 = p = rgcd #0 p = RHS    by ring_gcd_def
   If p <> #0 and q <> #0, by ring_gcd_def,
   rgcd p q = let s = {a * p + b * q | (a,b) | a IN R /\ b IN R /\ 0 < f (a * p + b * q)}
                 in CHOICE (preimage f s (MIN_SET (IMAGE f s))))
   rgcd q p = let s' = {a * q + b * p | (a,b) | a IN R /\ b IN R /\ 0 < f (a * q + b * p)}
                 in CHOICE (preimage f s' (MIN_SET (IMAGE f s'))))
   But s = s'  by exchanging a and b, and by ring_add_comm
   Hence rgcd p q = rgcd q p.
*)
val ring_gcd_sym = store_thm(
  "ring_gcd_sym",
  ``!(r:'a ring) (f:'a -> num). EuclideanRing r f ==> !p q. p IN R /\ q IN R ==> (rgcd p q = rgcd q p)``,
  rw_tac std_ss[ring_gcd_def] >>
  `s = s'` by
  (rw[Abbr`s`, Abbr`s'`, EXTENSION] >>
  `Ring r` by metis_tac[euclid_ring_ring] >>
  rw[EQ_IMP_THM] >| [
    qexists_tac `b` >>
    qexists_tac `a` >>
    rw[ring_add_comm],
    qexists_tac `b` >>
    qexists_tac `a` >>
    rw[ring_add_comm]
  ]) >>
  rw[]);

(* Theorem: atom p ==> !q. q IN R ==> unit (rgcd p q) \/ p rdivides q *)
(* Proof:
   Let g = rgcd p q
   Since g rdivides p        by ring_gcd_divides
   ?t. t IN R /\ p = t * g   by ring_divides_def
   Hence unit t or unit g    by irreducible_def
   If unit g, this is trivially true.
   If unit t, |/t exists     by ring_unit_has_inv
   so g = |/t * p,
   or p rdivides g.
   Since g rdivides q        by ring_gcd_divides
   p rdivides q              by ring_divides_trans
*)
val ring_irreducible_gcd = store_thm(
  "ring_irreducible_gcd",
  ``!(r:'a ring) (f:'a -> num). EuclideanRing r f ==>
     !p. p IN R /\ atom p ==> !q. q IN R ==> unit (rgcd p q) \/ p rdivides q``,
  rpt strip_tac >>
  `Ring r` by metis_tac[euclid_ring_ring] >>
  qabbrev_tac `g = rgcd p q` >>
  `g rdivides p /\ g rdivides q` by rw[ring_gcd_divides, Abbr`g`] >>
  `?t. t IN R /\ (p = t * g)` by rw[GSYM ring_divides_def] >>
  `g IN R` by rw[ring_gcd_element, Abbr`g`] >>
  `unit t \/ unit g` by metis_tac[irreducible_def] >| [
    `|/t IN R` by rw[ring_unit_inv_element] >>
    `|/t * p = |/t * t * g` by rw[ring_mult_assoc] >>
    `_ = #1 * g` by rw[ring_unit_linv] >>
    `_ = g` by rw[] >>
    `p rdivides g` by metis_tac[ring_divides_def] >>
    metis_tac[ring_divides_trans],
    rw[]
  ]);

(* Define ring ordering function *)
val ring_ordering_def = Define `
  ring_ordering (r:'a ring) (f:'a -> num) =
    !a b. a IN R /\ b IN R /\ b <> #0 ==> f a <= f (a * b)
`;

(* Theorem: EuclideanRing r /\ ring_ordering r f ==>
            !p q. p IN R /\ q IN R /\ p <> #0 /\ q rdivides p ==> f q <= f p *)
(* Proof:
   Since q rdivides p:
   ?s. s IN R /\ (p = s * q)     by ring_divides_def
   Since p <> #0, s <> #0        by ring_mult_lzero
   Hence f q <= f (q * s)        by ring_ordering_def
              = f (s * q)        by ring_mult_comm
              = f p
*)
val ring_divides_le = store_thm(
  "ring_divides_le",
  ``!(r:'a ring) (f:'a -> num). EuclideanRing r f /\ ring_ordering r f ==>
        !p q. p IN R /\ q IN R /\ p <> #0 /\ q rdivides p ==> f q <= f p``,
  rpt strip_tac >>
  `Ring r` by metis_tac[euclid_ring_ring] >>
  `?s. s IN R /\ (p = s * q)` by rw[GSYM ring_divides_def] >>
  `_ = q * s` by rw[ring_mult_comm] >>
  metis_tac[ring_ordering_def, ring_mult_rzero]);

(* division and primality are preserved by isomorphism *)

Theorem ring_divides_iso:
  !r r_ f. Ring r /\ Ring r_ /\ RingIso f r r_ ==>
    !p q. p IN r.carrier /\ ring_divides r p q ==>
      ring_divides r_ (f p) (f q)
Proof
  rw[ring_divides_def]
  \\ qexists_tac`f s`
  \\ fs[RingIso_def, RingHomo_def]
  \\ rfs[MonoidHomo_def]
QED

Theorem ring_prime_iso:
  !r r_ f. Ring r /\ Ring r_ /\ RingIso f r r_ ==>
    !p. p IN r.carrier /\ ring_prime r p ==> ring_prime r_ (f p)
Proof
  rw[ring_prime_def]
  \\ `BIJ f r.carrier r_.carrier` by fs[RingIso_def]
  \\ `?x y. a = f x /\ b = f y /\ x IN r.carrier /\ y IN r.carrier`
  by (
    fs[BIJ_DEF, SURJ_DEF]
    \\ res_tac \\ rw[]
    \\ metis_tac[] )
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ drule_then (drule_then drule) ring_iso_sym
  \\ strip_tac
  \\ first_x_assum(qspecl_then[`x`,`y`]mp_tac)
  \\ qspecl_then[`r`,`r_`,`f `]mp_tac ring_divides_iso
  \\ simp[] \\ strip_tac
  \\ impl_tac
  >- (
    `p = LINV f R (f p) /\ x = LINV f R (f x) /\ y = LINV f R (f y)`
    by metis_tac[BIJ_LINV_THM]
    \\ ntac 3 (pop_assum SUBST1_TAC)
    \\ `r.prod.op (LINV f R (f x)) (LINV f R (f y)) =
        LINV f R (r_.prod.op (f x) (f y))`
    by (
      qhdtm_x_assum`RingIso`mp_tac
      \\ simp_tac(srw_ss())[RingIso_def, RingHomo_def]
      \\ simp[MonoidHomo_def] )
    \\ pop_assum SUBST1_TAC
    \\ irule ring_divides_iso
    \\ metis_tac[BIJ_DEF, INJ_DEF] )
  \\ metis_tac[]
QED

(* ------------------------------------------------------------------------- *)
(* Principal Ideal Ring: Irreducibles and Primes                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: x IN <p>.carrier ==> p rdivides x *)
(* Proof:
        x IN <p>.carrier
   iff  ?z. z IN R /\ (x = p * z)    by principal_ideal_element
   iff  z IN R /\ (x = z * p)        by ring_mult_comm
   iff  p rdivides x                 by ring_divides_def
*)
val principal_ideal_element_divides = store_thm(
  "principal_ideal_element_divides",
  ``!r:'a ring. Ring r ==> !p. p IN R ==> !x. x IN <p>.carrier <=> p rdivides x``,
  rw[principal_ideal_element, ring_divides_def] >>
  metis_tac[ring_mult_comm]);

(* Theorem: q rdivides p <=> <p> << <q> *)
(* Proof:
   Note that <p> << r         by principal_ideal_ideal
         and <q> << r         by principal_ideal_ideal
   If part: q rdivides p ==> <p> << <q>
     This is to show <p>.carrier SUBSET <q>.carrier    by ideal_sub_ideal
     or p * R SUBSET q * R                             by principal_ideal_def
     Now q rdivides p
     ==> ?s. s IN R /\ (p = s * q)                     by ring_divides_def
     By coset_def, this is to show:
        ?z'. (s * q * z = q * z') /\ z' IN R
     But  s * q * z
        = q * s * z                                    by ring_mult_comm
        = q * (s * z)                                  by ring_mult_assoc
     Put z' = s * z, and z' IN R                       by ring_mult_element
  Only-if part: <p> << <q> ==> q rdivides p
     <p> << <q> means <p>.carrier SUBSET <q>.carrier   by ideal_sub_ideal
     Since p IN <p>.carrier                            by principal_ideal_has_element
           p IN <q>.carrier                            by SUBSET_DEF
     or    ?z. z IN R /\ (p = q * z)                   by principal_ideal_element
     i.e.  p = z * q                                   by ring_mult_comm
     Hence q rdivides p                                by ring_divides_def
*)
val principal_ideal_sub_implies_divides = store_thm(
  "principal_ideal_sub_implies_divides",
  ``!r:'a ring. Ring r ==> !p q. p IN R /\ q IN R ==> (q rdivides p <=> <p> << <q>)``,
  rpt strip_tac >>
  `<p> << r /\ <q> << r` by rw[principal_ideal_ideal] >>
  rw[EQ_IMP_THM] >| [
    `<p>.carrier SUBSET <q>.carrier` suffices_by metis_tac[ideal_sub_ideal] >>
    rw[principal_ideal_def, coset_def, SUBSET_DEF] >>
    `?s. s IN R /\ (p = s * q)` by rw[GSYM ring_divides_def] >>
    `s * q * z = q * s * z` by rw[ring_mult_comm] >>
    `_ = q * (s * z)` by rw[ring_mult_assoc] >>
    metis_tac[ring_mult_element],
    `<p>.carrier SUBSET <q>.carrier` by metis_tac[ideal_sub_ideal] >>
    `p IN <p>.carrier` by rw[principal_ideal_has_element] >>
    `p IN <q>.carrier` by metis_tac[SUBSET_DEF] >>
    `?z. z IN R /\ (p = q * z)` by rw[GSYM principal_ideal_element] >>
    `_ = z * q` by rw[ring_mult_comm] >>
    metis_tac[ring_divides_def]
  ]);

(* Introduce temporary overlaods *)
val _ = temp_overload_on ("<a>", ``principal_ideal r a``);
val _ = temp_overload_on ("<b>", ``principal_ideal r b``);
val _ = temp_overload_on ("<u>", ``principal_ideal r u``);

(* Theorem: PrincipalIdealRing r ==> !p. atom p ==> rprime p *)
(* Proof:
   By ring_prime_def, this is to show:
   a IN R /\ b IN R /\ p rdivides a * b ==> p rdivides a \/ p rdivides b
   By contradiction, assume ~(p rdivides a) /\ ~(p rdivides b).
       ~(p rdivides a)
   ==> ~(<a> << <p>)           by principal_ideal_sub_implies_divides
   ==> ~((<a> + <p>) << <p>)   by ideal_sum_sub_ideal
   Since PrincipalIdealRing r,
   ?u. u IN R /\ <a> + <p> = <u>    by PrincipalIdealRing_def
   But p IN <p>.carrier             by principal_ideal_has_element
   so  p IN (<a> + <p>).carrier     by ideal_sum_element
   Therefore
       p IN <u>.carrier             by above
   or  ?z. z IN R /\ p = u * z      by principal_ideal_element
   Since atom p, unit u or unit z   by irreducible_def
   If unit z,
   <p> = <u>                        by principal_ideal_eq_principal_ideal
   and <u> << <p>                   by ideal_refl
   which contradicts ~(<u> << <p>)  since <u> = <a> + <p>.
   Hence unit u,
   Since u IN <u>.carrier           by principal_ideal_has_element
      so <u> = r                    by ideal_with_unit
   Since #1 IN R                    by ring_one_element
   ?x y. x IN <a>.carrier /\ y IN <p>.carrier /\ (#1 = x + y)   by ideal_sum_element
   ?h k. h IN R /\ k IN R /\ #1 = a * h + p * k                 by principal_ideal_element
   Multiply by b,
   b = b * #1                       by ring_mult_rone
     = b * (a * h + p * k)          by substitution
     = b * (a * h) + b * (p * k)    by ring_mult_radd
     = b * a * h + b * p * k        by ring_mult_assoc
     = a * b * h + p * b * k        by ring_mult_comm
   But p rdivides a * b,
   ?s. s IN R /\ (a * b = s * p)    by ring_divides_def
   or  a * b = p * s                by ring_mult_comm
   Thus
   b = p * s * h + p * b * k        by substitution
     = p * (s * h) + p * (b * k)    by ring_mult_assoc
     = p * (s * h + b * k)          by ring_mult_radd
     = (s * h + b * k) * p          by ring_mult_comm
   Hence p rdivides b               by ring_divides_def
   which contradicts ~(p rdivides b).
*)
val principal_ideal_ring_atom_is_prime = store_thm(
  "principal_ideal_ring_atom_is_prime",
  ``!r:'a ring. PrincipalIdealRing r ==> !p. atom p ==> rprime p``,
  rw[ring_prime_def] >>
  `Ring r` by metis_tac[PrincipalIdealRing_def] >>
  `p IN R` by rw[irreducible_element] >>
  spose_not_then strip_assume_tac >>
  `~(<a> << <p>)` by rw[GSYM principal_ideal_sub_implies_divides] >>
  `<a> << r /\ <p> << r` by rw[principal_ideal_ideal] >>
  `~((<a> + <p>) << <p>)` by rw[ideal_sum_sub_ideal] >>
  `(<a> + <p>) << r` by rw[ideal_sum_ideal] >>
  `?u. u IN R /\ (<a> + <p> = <u>)` by metis_tac[PrincipalIdealRing_def] >>
  `p IN <p>.carrier` by rw[principal_ideal_has_element] >>
  `#0 IN <a>.carrier` by rw[ideal_has_zero] >>
  `p = #0 + p` by rw[] >>
  `p IN <u>.carrier` by metis_tac[ideal_sum_element] >>
  `?z. z IN R /\ (p = u * z)` by rw[GSYM principal_ideal_element] >>
  `unit z \/ unit u` by metis_tac[irreducible_def] >-
  metis_tac[principal_ideal_eq_principal_ideal, ideal_sub_itself] >>
  `u IN <u>.carrier` by rw[principal_ideal_has_element] >>
  `<u> = r` by metis_tac[ideal_with_unit] >>
  `#1 IN R` by rw[] >>
  `?x y. x IN <a>.carrier /\ y IN <p>.carrier /\ (#1 = x + y)` by rw[GSYM ideal_sum_element] >>
  `?h k. h IN R /\ k IN R /\ (#1 = a * h + p * k)` by metis_tac[principal_ideal_element] >>
  `?s. s IN R /\ (a * b = s * p)` by rw[GSYM ring_divides_def] >>
  `_ = p * s` by rw[ring_mult_comm] >>
  `b = b * #1` by rw[] >>
  `_ = b * (a * h + p * k)` by metis_tac[] >>
  `_ = b * (a * h) + b * (p * k)` by rw[ring_mult_radd] >>
  `_ = b * a * h + b * p * k` by rw[ring_mult_assoc] >>
  `_ = a * b * h + p * b * k` by rw[ring_mult_comm] >>
  `_ = p * s * h + p * b * k` by metis_tac[] >>
  `_ = p * (s * h) + p * (b * k)` by rw[ring_mult_assoc] >>
  `_ = p * (s * h + b * k)` by rw[ring_mult_radd] >>
  `_ = (s * h + b * k) * p` by rw[ring_mult_comm] >>
  `s * h + b * k IN R` by rw[] >>
  metis_tac[ring_divides_def]);

(* Another proof: *)
(* Theorem: PrincipalIdealRing r ==> !p. atom p ==> rprime p *)
(* Proof:
   By ring_prime_def, this is to show:
   a IN R /\ b IN R /\ p rdivides a * b ==> p rdivides a \/ p rdivides b
   Since p rdivides a * b,
   ?s. s IN R /\ (a * b = s * p)    by ring_divides_def
   or  a * b = p * s                by ring_mult_comm
   By contradiction, assume ~(p rdivides a) /\ ~(p rdivides b).
       ~(p rdivides a)
   ==> ~(a IN <p>.carrier)          by principal_ideal_element_divides
   ==> <a> + <p> <> <p>             by principal_ideal_sum_equal_ideal
   ==> <a> + <p> = r                by principal_ideal_ring_ideal_maximal
   Since #1 IN R                    by ring_one_element
   ?x y. x IN <a>.carrier /\ y IN <p>.carrier /\ (#1 = x + y)   by ideal_sum_element
   ?h k. h IN R /\ k IN R /\ #1 = a * h + p * k                 by principal_ideal_element
   Multiply by b,
   b = b * #1                       by ring_mult_rone
     = b * (a * h + p * k)          by substitution
     = b * (a * h) + b * (p * k)    by ring_mult_radd
     = b * a * h + b * p * k        by ring_mult_assoc
     = a * b * h + p * b * k        by ring_mult_comm
     = p * s * h + p * b * k        by substitution, a * b = p * s
     = p * (s * h) + p * (b * k)    by ring_mult_assoc
     = p * (s * h + b * k)          by ring_mult_radd
     = (s * h + b * k) * p          by ring_mult_comm
   Hence p rdivides b               by ring_divides_def
   which contradicts ~(p rdivides b).
*)
val principal_ideal_ring_irreducible_is_prime = store_thm(
  "principal_ideal_ring_irreducible_is_prime",
  ``!r:'a ring. PrincipalIdealRing r ==> !p. atom p ==> rprime p``,
  rw[ring_prime_def] >>
  `Ring r` by metis_tac[PrincipalIdealRing_def] >>
  `p IN R` by rw[irreducible_element] >>
  `<a> << r /\ <p> << r` by rw[principal_ideal_ideal] >>
  `(<a> + <p>) << r /\ <p> << (<a> + <p>)` by rw[ideal_sum_ideal, ideal_sum_has_ideal_comm] >>
  spose_not_then strip_assume_tac >>
  `~(a IN <p>.carrier)` by metis_tac[principal_ideal_element_divides] >>
  `<a> + <p> <> <p>` by metis_tac[principal_ideal_sum_equal_ideal] >>
  `<a> + <p> = r` by metis_tac[principal_ideal_ring_ideal_maximal, ideal_maximal_def] >>
  `?x y. x IN <a>.carrier /\ y IN <p>.carrier /\ (#1 = x + y)` by rw[GSYM ideal_sum_element] >>
  `?h k. h IN R /\ k IN R /\ (#1 = a * h + p * k)` by metis_tac[principal_ideal_element] >>
  `?s. s IN R /\ (a * b = s * p)` by rw[GSYM ring_divides_def] >>
  `_ = p * s` by rw[ring_mult_comm] >>
  `b = b * #1` by rw[] >>
  `_ = b * (a * h + p * k)` by metis_tac[] >>
  `_ = b * (a * h) + b * (p * k)` by rw[ring_mult_radd] >>
  `_ = b * a * h + b * p * k` by rw[ring_mult_assoc] >>
  `_ = a * b * h + p * b * k` by rw[ring_mult_comm] >>
  `_ = p * s * h + p * b * k` by metis_tac[] >>
  `_ = p * (s * h) + p * (b * k)` by rw[ring_mult_assoc] >>
  `_ = p * (s * h + b * k)` by rw[ring_mult_radd] >>
  `_ = (s * h + b * k) * p` by rw[ring_mult_comm] >>
  `s * h + b * k IN R` by rw[] >>
  metis_tac[ring_divides_def]);

(* ------------------------------------------------------------------------- *)
(* Quotient Ring Documentation                                               *)
(* ------------------------------------------------------------------------- *)
(* Overloads:
   R/I     = CosetPartition r.sum i.sum
   gen x   = cogen r.sum i.sum x
   x + y   = ideal_coset_add r i x y
   x * y   = ideal_coset_mult r i x y
   r / i   = quotient_ring r i
*)
(* Definitions and Theorems (# are exported):

   Ideal Coset:
   ideal_coset_add_def      |- !r i x y. x + y = (gen x + gen y) o I
   ideal_coset_mult_def     |- !r i x y. x * y = (gen x * gen y) o I
   ideal_coset_element      |- !r i x. Ring r /\ i << r /\ x IN R ==>
                               !z. z IN x o I <=> ?y. y IN I /\ (z = x + y)

   Quotient Ring:
   quotient_ring_add_def    |- !r i. quotient_ring_add r i = <|carrier := R/I; id := I; op := $+ |>
   quotient_ring_mult_def   |- !r i. quotient_ring_mult r i = <|carrier := R/I; id := #1 o I; op := $* |>
   quotient_ring_def        |- !r i. r / i =
                                         <|carrier := R/I;
                                               sum := quotient_ring_add r i;
                                              prod := quotient_ring_mult r i
                                          |>
   quotient_ring_property   |- !r i. ((r / i).carrier = R/I) /\
                                     ((r / i).sum = quotient_ring_add r i) /\
                                     ((r / i).prod = quotient_ring_mult r i)
   ideal_cogen_property     |- !r i. Ring r /\ i << r ==> !x. x IN R/I ==> gen x IN R /\ (gen x o I = x)
   ideal_coset_property     |- !r i. Ring r /\ i << r ==> !x. x IN R ==> x o I IN R/I /\ (gen (x o I) o I = x o I)
   ideal_in_quotient_ring   |- !r i. Ring r /\ i << r ==> I IN R/I
   quotient_ring_has_ideal  |- !r i. Ring r /\ i << r ==> I IN R/I
   quotient_ring_element    |- !r i. Ring r /\ i << r ==> !z. z IN R/I <=> ?x. x IN R /\ (z = x o I)
   ideal_coset_has_gen_diff |- !r i. Ring r /\ i << r ==> !x. x IN R ==> gen (x o I) - x IN I
   ideal_coset_add          |- !r i. Ring r /\ i << r ==>
                               !x y. x IN R /\ y IN R ==> (x o I + y o I = (x + y) o I)
   ideal_coset_mult         |- !r i. Ring r /\ i << r ==>
                               !x y. x IN R /\ y IN R ==> (x o I * y o I = (x * y) o I)
   ideal_coset_neg          |- !r i. Ring r /\ i << r ==> !x. x IN R ==> (x o I + -x o I = I)

   Quotient Ring Addition is a Abelian Group:
   quotient_ring_add_element  |- !r i. Ring r /\ i << r ==> !x y. x IN R/I /\ y IN R/I ==> x + y IN R/I
   quotient_ring_add_comm     |- !r i. Ring r /\ i << r ==> !x y. x IN R/I /\ y IN R/I ==> (x + y = y + x)
   quotient_ring_add_assoc    |- !r i. Ring r /\ i << r ==> !x y z. x IN R/I /\ y IN R/I /\ z IN R/I ==> (x + y + z = x + (y + z))
   quotient_ring_add_id       |- !r i. Ring r /\ i << r ==> !x. x IN R/I ==> (I + x = x)
   quotient_ring_add_inv      |- !r i. Ring r /\ i << r ==> !x. x IN R/I ==> ?y. y IN R/I /\ (y + x = I)
   quotient_ring_add_group    |- !r i. Ring r /\ i << r ==> Group (quotient_ring_add r i)
   quotient_ring_add_abelian_group  |- !r. Ring r /\ i << r ==> AbelianGroup (quotient_ring_add r i)

   Quotient Ring Multiplication is an Abelian Monoid:
   quotient_ring_mult_element |- !r i. Ring r /\ i << r ==> !x y. x IN R/I /\ y IN R/I ==> x * y IN R/I
   quotient_ring_mult_comm    |- !r i. Ring r /\ i << r ==> !x y. x IN R/I /\ y IN R/I ==> (x * y = y * x)
   quotient_ring_mult_assoc   |- !r i. Ring r /\ i << r ==> !x y z. x IN R/I /\ y IN R/I /\ z IN R/I ==> (x * y * z = x * (y * z))
   quotient_ring_mult_id      |- !r i. Ring r /\ i << r ==> !x. x IN R/I ==> (#1 o I * x = x) /\ (x * #1 o I = x)
   quotient_ring_mult_monoid  |- !r i. Ring r /\ i << r ==> Monoid (quotient_ring_mult r i)
   quotient_ring_mult_abelian_monoid
                              |- !r. Ring r /\ i << r ==> AbelianMonoid (quotient_ring_mult r i)

   Quotient Ring is a Ring:
   quotient_ring_mult_ladd    |- !r i. Ring r /\ i << r ==> !x y z. x IN R/I /\ y IN R/I /\ z IN R/I ==>
                                 (x * (y + z) = x * y + x * z)
   quotient_ring_ring         |- !r i. Ring r /\ i << r ==> Ring (r / i)
   quotient_ring_ring_sing    |- !r. Ring r ==> ((r / r).carrier = {R})
   quotient_ring_by_principal_ideal
                              |- !r. Ring r ==> !p. p IN R ==> Ring (r / <p>)

   Quotient Ring Homomorphism:
   quotient_ring_homo         |- !r i. Ring r /\ i << r ==> RingHomo (\x. x o I) r (r / i)
   quotient_ring_homo_surj    |- !r i. Ring r /\ i << r ==> SURJ (\x. x o I) R R/I
   quotient_ring_homo_kernel  |- !r i. Ring r /\ i << r ==> (kernel (\x. x o I) r.sum (r / i).sum = I)

   Kernel of Ring Homomorphism:
   kernel_ideal_def           |- !f r s. kernel_ideal f r s =
                                 <|carrier := kernel f r.sum s.sum;
                                       sum := <|carrier := kernel f r.sum s.sum; op := $+; id := #0|>;
                                      prod := <|carrier := kernel f r.sum s.sum; op := $*; id := #1|>
                                  |>
   kernel_ideal_sum_eqn       |- !r s f. (kernel_ideal f r s).sum = kernel_group f r.sum s.sum
   kernel_ideal_element       |- !r r_ f x. x IN (kernel_ideal f r r_).carrier <=>
                                            x IN r.sum.carrier /\ (f x = #0_)
   ring_homo_kernel_ideal     |- !f r s. Ring r /\ Ring s /\ RingHomo f r s ==> kernel_ideal f r s << r
   quotient_ring_homo_kernel_ideal
                              |- !r i. Ring r /\ i << r ==>
                                       RingHomo (\x. x o I) r (r / i) /\ (kernel_ideal (\x. x o I) r (r / i) = i)

   First Isomorphism Theorem for Ring:
   kernel_ideal_gen_add_map    |- !r r_ f. (r ~r~ r_) f ==> (let i = kernel_ideal f r r_ in
                                  !x y. x IN R/I /\ y IN R/I ==>
                                   (f (gen ((gen x + gen y) o I)) = f (gen x) +_ f (gen y)))
   kernel_ideal_gen_mult_map   |- !r r_ f. (r ~r~ r_) f ==> (let i = kernel_ideal f r r_ in
                                  !x y. x IN R/I /\ y IN R/I ==>
                                   (f (gen ((gen x * gen y) o I)) = f (gen x) *_ f (gen y)))
   kernel_ideal_gen_id_map     |- !r r_ f. (r ~r~ r_) f ==>
                                  (let i = kernel_ideal f r r_ in f (gen (#1 o I)) = #1_)
   kernel_ideal_quotient_element_eq
                               |- !r r_ f. (r ~r~ r_) f ==> (let i = kernel_ideal f r r_ in
                                  !x y. x IN R/I /\ y IN R/I ==> (gen x - gen y IN I <=> (x = y)))
   kernel_ideal_quotient_inj   |- !r r_ f. (r ~r~ r_) f ==> (let i = kernel_ideal f r r_ in
                                           INJ (f o gen) R/I (IMAGE f R))
   kernel_ideal_quotient_surj  |- !r r_ f. (r ~r~ r_) f ==> (let i = kernel_ideal f r r_ in
                                           SURJ (f o gen) R/I (IMAGE f R))
   kernel_ideal_quotient_bij   |- !r r_ f. (r ~r~ r_) f ==> (let i = kernel_ideal f r r_ in
                                           BIJ (f o gen) R/I (IMAGE f R))
   kernel_ideal_quotient_homo  |- !r s f. (r ~r~ s) f ==> (let i = kernel_ideal f r s in
                                          RingHomo (f o gen) (r / i) (ring_homo_image f r s))
   kernel_ideal_quotient_iso   |- !r s f. (r ~r~ s) f ==> (let i = kernel_ideal f r s in
                                          RingIso (f o gen) (r / i) (ring_homo_image f r s))
   ring_first_isomorphism_thm  |- !r r_ f. (r ~r~ r_) f ==> (let i = kernel_ideal f r r_ in
                                           i << r /\ ring_homo_image f r r_ <= r_ /\
                                           RingIso (f o gen) (r / i) (ring_homo_image f r r_))
*)

(* ------------------------------------------------------------------------- *)
(* Ideal Coset.                                                              *)
(* ------------------------------------------------------------------------- *)

(* The carrier of Ideal = carrier of group i.sum *)
val _ = temp_overload_on ("I", ``i.carrier``);
(* The carrier of Ideal = carrier of group j.sum *)
val _ = temp_overload_on ("J", ``j.carrier``);

(* Define carrier set of Quotient Ring (R/I) by overloading *)
val _ = overload_on ("R/I", ``CosetPartition r.sum i.sum``);

(* Define cogen operation of Quotient Ring (R/I) by overloading *)
val _ = overload_on ("gen", ``cogen r.sum i.sum``);

(* Define addition of ideal cosets *)
val ideal_coset_add_def = Define`
  ideal_coset_add (r:'a ring) (i:'a ring) x y = (gen x + gen y) o I
`;

(* Define multiplication of ideal cosets *)
val ideal_coset_mult_def = Define`
  ideal_coset_mult (r:'a ring) (i:'a ring) x y = (gen x * gen y) o I
`;

(* Overload operations *)
val _ = overload_on ("+", ``ideal_coset_add r i``);
val _ = overload_on ("*", ``ideal_coset_mult r i``);

(* Export simple definitions *)
val _ = export_rewrites ["ideal_coset_add_def", "ideal_coset_mult_def"];

(*
> in_coset |> ISPEC ``r.sum`` |> ISPEC ``i.sum.carrier`` |> ISPEC ``x``;
val it = |- x IN r.sum.carrier ==>
           !x'. x' IN x o i.sum.carrier <=> ?y. y IN i.sum.carrier /\ (x' = x + y): thm
*)

(* Theorem: Ring r /\ i << r /\ x IN R ==> !z. z IN x o I <=> ?y. y IN I /\ (z = x + y) *)
(* Proof:
     z IN x o I
   = z IN x * i.sum.carrier                  by notation
   = ?y. y IN i.sum.carrier /\ (z = x + y)   by in_coset
   = ?y. y IN I /\ (z = x + y)               by ring_carriers, ideal_carriers
*)
val ideal_coset_element = store_thm(
  "ideal_coset_element",
  ``!(r:'a ring) (i:'a ring) x. Ring r /\ i << r /\ x IN R ==>
   !z. z IN x o I <=> ?y. y IN I /\ (z = x + y)``,
  rw_tac std_ss[in_coset, ring_carriers, ideal_carriers]);

(* ------------------------------------------------------------------------- *)
(* Quotient Ring.                                                            *)
(* ------------------------------------------------------------------------- *)

(* Define addition group in Quotient Ring (R/I) *)
val quotient_ring_add_def = Define `
  quotient_ring_add (r:'a ring) (i:'a ring) =
    <| carrier := R/I;
            id := I; (* will show: I = #0 o I *)
            op := ideal_coset_add r i
     |>
`;

(* Define multiplication monoid in Quotient Ring (R/I) *)
val quotient_ring_mult_def = Define `
  quotient_ring_mult (r:'a ring) (i:'a ring) =
    <| carrier := R/I;
            id := #1 o I;
            op := ideal_coset_mult r i
     |>
`;

(* Define Quotient Ring (R/I) *)
val quotient_ring_def = Define `
  quotient_ring (r:'a ring) (i:'a ring) =
    <| carrier := R/I;
           sum := quotient_ring_add r i;
          prod := quotient_ring_mult r i
     |>
`;

(* set overloading for Quotient Ring. *)
val _ = overload_on ("/", ``quotient_ring``);

(* Theorem: Properties of quotient ring (r / i). *)
(* Proof: by quotient_ring_def *)
val quotient_ring_property = store_thm(
  "quotient_ring_property",
  ``!r:'a ring i:'a ring.
        ((r / i).carrier = R/I) /\
        ((r / i).sum = quotient_ring_add r i) /\
        ((r / i).prod = quotient_ring_mult r i)``,
  rw[quotient_ring_def]);

(* Theorem: Ring r /\ (i << r) ==> !x. x IN R/I ==> gen x IN R /\ (gen x o I = x) *)
(* Proof:
   Since i << r,
   i.sum <= r.sum /\ i.sum.carrier = I   by ideal_def
   and r.sum.carrier = R                 by ring_add_group
   Since x IN R/I,
     gen x IN r.sum.carrier              by cogen_element
     gen x o I
   = (cogen r.sum i.sum x) o I           by rewrite of gen
   = x                                   by coset_cogen_property, i.sum <= r.sum
*)
val ideal_cogen_property = store_thm(
  "ideal_cogen_property",
  ``!r i:'a ring. Ring r /\ (i << r) ==> !x. x IN R/I ==> gen x IN R /\ (gen x o I = x)``,
  metis_tac[ideal_def, ring_add_group, cogen_element, coset_cogen_property]);

(* Theorem: Ring r /\ (i << r) ==> !x. x IN R ==> gen (x o I) + I = x o I  *)
(* Proof:
   Since i << r,
   i.sum <= r.sum /\ i.sum.carrier = I  by ideal_def
   and r.sum.carrier = R                by ring_add_group
   Hence x o I IN R/I                   by coset_partition_element
     gen (x o I) o I
   = gen (coset r.sum x I) o I          by ideal_coset rewrite
   = (coset r.sum x I)                  by coset_cogen_property
   = x o I                              by ideal_coset rewrite
*)
val ideal_coset_property = store_thm(
  "ideal_coset_property",
  ``!r i:'a ring. Ring r /\ (i << r) ==> !x. x IN R ==> x o I IN R/I /\ (gen (x o I) o I = x o I)``,
  metis_tac[ideal_def, ring_add_group, coset_partition_element, coset_cogen_property]);

(* Theorem: Ring r /\ i << r ==> #0 o I = I *)
(* Proof:
   Since i << r,
   i.sum <= r.sum /\ i.sum.carrier = I     by ideal_def
   and   Group r.sum                       by ring_add_group
   This follows by coset_id_eq_subgroup.
*)
val ideal_coset_zero = store_thm(
  "ideal_coset_zero",
  ``!r i:'a ring. Ring r /\ i << r ==> (#0 o I = I)``,
  metis_tac[ideal_def, coset_id_eq_subgroup, ring_add_group]);

(* Theorem: Ring r /\ i << r ==> I IN R/I *)
(* Proof:
   Since #0 IN R, #0 o I IN R/I by ideal_coset_property.
   Hence true by By ideal_coset_zero.
*)
val ideal_in_quotient_ring = store_thm(
  "ideal_in_quotient_ring",
  ``!r i:'a ring. Ring r /\ i << r ==> I IN R/I``,
  metis_tac[ideal_coset_property, ring_zero_element, ideal_coset_zero]);

(* Theorem alias *)
val quotient_ring_has_ideal = save_thm("quotient_ring_has_ideal", ideal_in_quotient_ring);


(*
ideal_coset_property  |- !r i. Ring r /\ i << r ==> !x. x IN R ==> x o I IN R/I /\ (gen (x o I) o I = x o I)
ideal_cogen_property  |- !r i. Ring r /\ i << r ==> !x. x IN R/I ==> gen x IN R /\ (gen x o I = x)

> coset_partition_element |> ISPEC ``r.sum`` |> ISPEC ``i.sum``;
val it = |- i.sum <= r.sum ==> !e. e IN R/I <=> ?a. a IN r.sum.carrier /\ (e = a o i.sum.carrier): thm

In textbook, this is written as: (x + I) + (y + I) = (x + y) + I
*)

(* Theorem: Ring r /\ i << r ==> !z. z IN R/I <=> ?x. x IN R /\ (z = x o I) *)
(* Proof:
   If part: z IN R/I ==> ?x. x IN R /\ (z = x o I)
      Note gen z IN R /\ (gen z) o I = z    by ideal_cogen_property
      Take x = gen z, the result is true.
   Only-if part: x IN R /\ (z = x o I) ==> z IN R/I
      This is true                          by ideal_coset_property
*)
val quotient_ring_element = store_thm(
  "quotient_ring_element",
  ``!(r:'a ring) (i:'a ring). Ring r /\ i << r ==> !z. z IN R/I <=> ?x. x IN R /\ (z = x o I)``,
  metis_tac[ideal_cogen_property, ideal_coset_property]);

(* Theorem: Ring r /\ i << r ==> !x. x IN R ==> gen (x o I) - x IN I *)
(* Proof:
   Note x o I IN R/I               by ideal_coset_property
    and gen (x o I) o I = x o I    by ideal_coset_property
   Thus gen (x o I) IN R           by ideal_cogen_property
   Thus gen (x o I) - x IN I       by ideal_coset_eq
*)
val ideal_coset_has_gen_diff = store_thm(
  "ideal_coset_has_gen_diff",
  ``!(r:'a ring) (i:'a ring). Ring r /\ i << r ==> !x. x IN R ==> gen (x o I) - x IN I``,
  rw_tac std_ss[ideal_coset_property, ideal_cogen_property, GSYM ideal_coset_eq]);

(* Theorem: Ring r /\ i << r ==> !x y. x IN R /\ y IN R ==> ((x o I) + (y o I) = (x + y) o I) *)
(* Proof:
   Let t = gen (x o I) + gen (y o I).
   Note x o I IN R/I /\ y o I IN R/I           by ideal_coset_property
   Thus gen (x o I) IN R /\ gen (y o I) IN R   by ideal_cogen_property
    and t IN R /\ (x + y) IN R                 by ring_add_element

   Note (x o I) + (y o I) = t o I              by ideal_coset_add_def
    Now gen (x o I) - x IN I                   by ideal_coset_has_gen_diff
    and gen (y o I) - y IN I                   by ideal_coset_has_gen_diff

        t - (x + y)
      = (gen (x o I) + gen (y o I)) - (x + y)  by notation
      = (gen (x o I) - x) + (gen (y o I) - y)  by ring_add_pair_sub
   Thus t - (x + y) IN I                       by ideal_has_sum
     or t o I = (x + y) o I                    by ideal_coset_eq
*)
val ideal_coset_add = store_thm(
  "ideal_coset_add",
  ``!(r:'a ring) (i:'a ring). Ring r /\ i << r ==>
   !x y. x IN R /\ y IN R ==> ((x o I) + (y o I) = (x + y) o I)``,
  rw_tac std_ss[ideal_coset_add_def] >>
  qabbrev_tac `t = gen (x o I) + gen (y o I)` >>
  `x o I IN R/I /\ y o I IN R/I` by rw[ideal_coset_property] >>
  `gen (x o I) IN R /\ gen (y o I) IN R` by rw[ideal_cogen_property] >>
  `t IN R /\ x + y IN R` by rw[Abbr`t`] >>
  rw_tac std_ss[ideal_coset_eq] >>
  `t - (x + y) = (gen (x o I) - x) + (gen (y o I) - y)` by rw[ring_add_pair_sub, Abbr`t`] >>
  metis_tac[ideal_coset_has_gen_diff, ideal_has_sum]);

(* Theorem: Ring r /\ i << r ==> !x y. x IN R /\ y IN R ==> ((x o I) * (y o I) = (x * y) o I) *)
(* Proof:
   Let t = gen (x o I) * gen (y o I).
   Note x o I IN R/I /\ y o I IN R/I           by ideal_coset_property
   Thus gen (x o I) IN R /\ gen (y o I) IN R   by ideal_cogen_property
    and t IN R /\ (x * y) IN R                 by ring_mult_element

   Note (x o I) * (y o I) = t o I              by ideal_coset_mult_def
    Now gen (x o I) - x IN I                   by ideal_coset_has_gen_diff
    and gen (y o I) - y IN I                   by ideal_coset_has_gen_diff

        t - (x * y)
      = (gen (x o I) * gen (y o I)) - (x * y)  by notation
      = (gen (x o I) - x) * gen (y o I) + x * (gen (y o I) - y)  by ring_mult_pair_diff
      = (gen (x o I) - x) * gen (y o I) + (gen (y o I) - y) * x  by ring_mult_comm
   Note (gen (x o I) - x) * gen (y o I) IN I   by ideal_has_multiple
    and           (gen (y o I) - y) * x IN I   by ideal_has_multiple
   Thus t - (x * y) IN I                       by ideal_has_sum
     or t o I = (x * y) o I                    by ideal_coset_eq
*)
val ideal_coset_mult = store_thm(
  "ideal_coset_mult",
  ``!(r:'a ring) (i:'a ring). Ring r /\ i << r ==>
   !x y. x IN R /\ y IN R ==> ((x o I) * (y o I) = (x * y) o I)``,
  rw_tac std_ss[ideal_coset_mult_def] >>
  qabbrev_tac `t = gen (x o I) * gen (y o I)` >>
  `x o I IN R/I /\ y o I IN R/I` by rw[ideal_coset_property] >>
  `gen (x o I) IN R /\ gen (y o I) IN R` by rw[ideal_cogen_property] >>
  `t IN R /\ x * y IN R` by rw[Abbr`t`] >>
  rw_tac std_ss[ideal_coset_eq] >>
  `t - (x * y) = (gen (x o I) - x) * gen (y o I) + x * (gen (y o I) - y)` by rw_tac std_ss[ring_mult_pair_diff, Abbr`t`] >>
  `_ = (gen (x o I) - x) * gen (y o I) + (gen (y o I) - y) * x` by rw_tac std_ss[ring_mult_comm, ring_sub_element] >>
  metis_tac[ideal_coset_has_gen_diff, ideal_has_multiple, ideal_has_sum]);

(* Theorem: Ring r /\ i << r ==> !x. x IN R ==> (x o I + (-x) o I = I) *)
(* Proof:
   Note x IN R ==> -x IN R   by ring_neg_element
     x o I + (-x) o I
   = (x + (-x)) o I          by ideal_coset_add
   = #0 o I                  by ring_add_rneg
   = I                       by ideal_coset_zero
*)
val ideal_coset_neg = store_thm(
  "ideal_coset_neg",
  ``!(r:'a ring) (i:'a ring). Ring r /\ i << r ==> !x. x IN R ==> (x o I + (-x) o I = I)``,
  rw_tac std_ss[ideal_coset_add, ideal_coset_zero, ring_neg_element, ring_add_rneg]);

(* ------------------------------------------------------------------------- *)
(* Quotient Ring (R/I).sum is an Abelian Group.                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: [Quotient Ring Add Closure]
   Ring r /\ (i << r) ==> !x y. x IN R/I /\ y IN R/I ==> x + y IN R/I *)
(* Proof:
   Since i << r,
   i.sum <= r.sum /\ i.sum.carrier = I            by ideal_def
   By Ring r, Group r.sum and r.sum.carrier = R   by ring_add_group
     x IN R/I ==> gen x IN r.sum.carrier          by cogen_element
     y IN R/I ==> gen y IN r.sum.carrier          by cogen_element
   Hence  gen x + gen y IN r.sum.carrier          by ring_add_element
      or  (gen x + gen y) o I IN R/I              by coset_partition_element, since i.sum <= r.sum.
*)
val quotient_ring_add_element = store_thm(
  "quotient_ring_add_element",
  ``!r i:'a ring. Ring r /\ (i << r) ==> !x y. x IN R/I /\ y IN R/I ==> x + y IN R/I``,
  rw[ideal_cogen_property, ideal_coset_property]);

(* Theorem: [Quotient Ring Add Commutative] Ring r /\ (i << r) ==> !x y. x IN R/I /\ y IN R/I ==> x + y = y + x *)
(* Proof:
   First, gen x IN R and gen y IN R   by ideal_cogen_property
     x + y
   = (gen x + gen y) o I        by ideal_coset_add_def
   = (gen y + gen x) o I        by ring_add_comm
   = y + x                      by ideal_coset_add_def
*)
val quotient_ring_add_comm = store_thm(
  "quotient_ring_add_comm",
  ``!r i:'a ring. Ring r /\ (i << r) ==> !x y. x IN R/I /\ y IN R/I ==> (x + y = y + x)``,
  rw[ring_add_comm, ideal_cogen_property]);

(* Theorem: Ring r /\ i << r /\ x IN R/I /\ y IN R/I /\ z IN R/I ==> x + y + z = x + (y + z) *)
(* Proof:
   We have gen x IN R, gen y IN R and gen z IN R by ideal_cogen_property.
   Hence gen x + gen y IN R               by ring_add_element
     and gen ((gen x + gen y) o I) IN R   by ideal_coset_property, ideal_cogen_property
    Also gen y + gen z IN R               by ring_add_element
     and gen ((gen y + gen z) o I) IN R   by ideal_coset_property, ideal_cogen_property

   First, show: x + y + z = (gen x + gen y + gen z) o I
   i.e.   x + y + z = (gen ((gen x + gen y) o I) + gen z) o I = (gen x + gen y + gen z) o I
   By ideal_coset_eq, this is true if
         (gen ((gen x + gen y) o I) + gen z) - (gen x + gen y + gen z) IN I
   Now   gen ((gen x + gen y) o I) o I = (gen x + gen y) o I   by ideal_coset_property
   hence gen ((gen x + gen y) o I) - (gen x + gen y) IN I      by ideal_coset_eq
   or   (gen ((gen x + gen y) o I) + gen z) - (gen x + gen y + gen z) IN I   by ring_sub_pair_reduce
   Hence true.

   Next, show: x + (y + z) = (gen x + (gen y + gen z)) o I
   i.e. (gen x + gen ((gen y + gen z) o I)) o I = (gen x + (gen y + gen z)) o I
   By ideal_coset_eq, this is true if
        (gen x + gen ((gen y + gen z) o I)) - (gen x + (gen y + gen z)) IN I
   Now   gen ((gen y + gen z) o I) o I = (gen y + gen z) o I    by ideal_coset_property
   hence (gen ((gen y + gen z) o I)) - (gen y + gen z) IN I     by ideal_coset_eq
   or    (gen x + gen ((gen y + gen z) o I)) - (gen x + (gen y + gen z)) IN I  by ring_sub_pair_reduce, ring_add_comm
   Hence true.

   Combining,
     x + y + z
   = (gen x + gen y + gen z) o I     by 1st result
   = (gen x + (gen y + gen z)) o I   by ring_add_assoc
   = x + (y + z)                     by 2nd result
*)
val quotient_ring_add_assoc = store_thm(
  "quotient_ring_add_assoc",
  ``!r i:'a ring. Ring r /\ (i << r) ==> !x y z. x IN R/I /\ y IN R/I /\ z IN R/I ==> (x + y + z = x + (y + z))``,
  rw_tac std_ss[ideal_coset_add_def] >>
  `gen x IN R /\ gen y IN R /\ gen z IN R` by rw_tac std_ss[ideal_cogen_property] >>
  `(gen ((gen x + gen y) o I) + gen z) o I = (gen x + gen y + gen z) o I` by
  (`gen x + gen y IN R` by rw[] >>
  `gen ((gen x + gen y) o I) IN R` by rw_tac std_ss[ideal_coset_property, ideal_cogen_property] >>
  `gen ((gen x + gen y) o I) - (gen x + gen y) IN I` by metis_tac[ideal_coset_eq, ideal_coset_property] >>
  `(gen ((gen x + gen y) o I) + gen z) - (gen x + gen y + gen z) IN I` by rw_tac std_ss[ring_sub_pair_reduce] >>
  rw_tac std_ss[ideal_coset_eq, ring_add_element]) >>
  `(gen x + gen ((gen y + gen z) o I)) o I = (gen x + (gen y + gen z)) o I` by
    (`gen y + gen z IN R` by rw[] >>
  `gen ((gen y + gen z) o I) IN R` by rw_tac std_ss[ideal_coset_property, ideal_cogen_property] >>
  `gen ((gen y + gen z) o I) - (gen y + gen z) IN I` by metis_tac[ideal_coset_eq, ideal_coset_property] >>
  `gen x + gen ((gen y + gen z) o I) - (gen x + (gen y + gen z)) IN I` by metis_tac[ring_sub_pair_reduce, ring_add_comm] >>
  rw_tac std_ss[ideal_coset_eq, ring_add_element]) >>
  rw_tac std_ss[ring_add_assoc]);

(* Theorem: [Quotient Ring Add Identity] Ring r /\ i << r /\ x IN R/I ==> I + x = x *)
(* Proof:
   LHS = I + x = (gen I + gen x) o I        by ideal_coset_add_def
   RHS = x = gen x o I                      by ideal_cogen_property
   Since I IN R/I                           by ideal_in_quotient_ring
         I = gen I o I                      by ideal_cogen_property
   or gen I o I = I = #0 o I                by ideal_coset_zero
   Thus  gen I - #0 IN I                    by ideal_coset_eq
   But (gen I + gen x) - (#0 + gen x)
      = gen I - #0                          by ring_sub_pair_reduce
   Hence (gen I + gen x) - gen x IN I       by ring_add_lzero
   Thus LHS = RHS                           by ideal_coset_eq
*)
val quotient_ring_add_id = store_thm(
  "quotient_ring_add_id",
  ``!r i:'a ring. Ring r /\ i << r ==> !x. x IN R/I ==> (I + x = x)``,
  rw_tac std_ss[ideal_coset_add_def] >>
  `I IN R/I` by rw_tac std_ss[ideal_in_quotient_ring] >>
  `gen x IN R /\ gen I IN R /\ (gen x o I = x) /\ (gen I o I = I)` by rw_tac std_ss[ideal_cogen_property] >>
  `I = #0 o I` by rw_tac std_ss[ideal_coset_zero] >>
  `#0 IN R` by rw_tac std_ss[ring_zero_element] >>
  `(gen I + gen x) - gen x = gen I - #0` by metis_tac[ring_sub_pair_reduce, ring_add_lzero] >>
  metis_tac[ideal_coset_eq, ring_add_lzero, ring_add_element]);

(* Theorem: [Quotient Ring Add Inverse] Ring r /\ i << r /\ x IN R/I ==> ?y. y IN R/I /\ (y + x = I) *)
(* Proof:
   Since x IN R/I, gen x IN R        by ideal_cogen_property
            hence -gen x IN R        by ring_neg_element
              and -gen x o I IN R/I  by ideal_coset_property
   Let y = - gen x o I, then y IN R/I, and it remains to show that:
         y + x = I
   or   (- gen x o I) + x = I
   i.e. gen (-gen x o I) + gen x o I = I
   Since #0 o I = I               by coset_id_eq_subgroup
   this is to show: gen (-gen x o I) + gen x o I = #0 o I

   Now  gen (-gen x o I) IN R
    and (gen (-gen x o I) o I = (- gen x) o I)   by ideal_cogen_property
   Hence  gen (-gen x o I) - (- gen x) IN I      by ideal_coset_eq
     gen (-gen x o I) - (- gen x)
   = gen (-gen x o I) + gen x        by ring_sub_def, ring_neg_neg
   = gen (-gen x o I) + gen x - #0   by ring_sub_def, ring_neg_zero, ring_add_rzero, ring_add_element
   i.e. gen (-gen x o I) + gen x - #0 IN I
   Thus true by ideal_coset_eq.
*)
val quotient_ring_add_inv = store_thm(
  "quotient_ring_add_inv",
  ``!r i:'a ring. Ring r /\ i << r ==> !x. x IN R/I ==> ?y. y IN R/I /\ (y + x = I)``,
  rw_tac std_ss[ideal_coset_add_def] >>
  `gen x IN R` by rw_tac std_ss[ideal_cogen_property] >>
  `- gen x IN R` by rw_tac std_ss[ring_neg_element] >>
  `- gen x o I IN R/I` by rw_tac std_ss[ideal_coset_property] >>
  qexists_tac `- gen x o I` >>
  rw_tac std_ss[] >>
  `gen (-gen x o I) IN R /\ (gen (-gen x o I) o I = (- gen x) o I)` by rw_tac std_ss[ideal_cogen_property] >>
  `gen (-gen x o I) - (- gen x) IN I` by metis_tac[ideal_coset_eq] >>
  `gen (-gen x o I) - (- gen x) = gen (-gen x o I) + gen x` by rw[] >>
  `_ = gen (-gen x o I) + gen x - #0` by rw[] >>
  `I = #0 o I` by rw_tac std_ss[ideal_coset_zero] >>
  metis_tac[ideal_coset_eq, ring_add_element, ring_zero_element]);

(* Theorem: quotient_ring_add is a Group. *)
(* Proof:
   Check for each group property:
   Closure: by quotient_ring_add_element
   Associative: by quotient_ring_add_assoc
   Identity: by quotient_ring_add_id, and ideal_in_quotient_ring
   Inverse: by quotient_ring_add_inv
*)
val quotient_ring_add_group = store_thm(
  "quotient_ring_add_group",
  ``!r i:'a ring. Ring r /\ (i << r) ==> Group (quotient_ring_add r i)``,
  rw_tac std_ss[group_def_alt, quotient_ring_add_def] >| [
    rw_tac std_ss[quotient_ring_add_element],
    rw_tac std_ss[quotient_ring_add_assoc],
    rw_tac std_ss[ideal_in_quotient_ring],
    rw_tac std_ss[quotient_ring_add_id],
    rw_tac std_ss[quotient_ring_add_inv]
  ]);

(* Theorem: quotient_ring_add is an Abelain Group. *)
(* Proof:
   By quotient_ring_add_group, and quotient_ring_add_comm.
*)
val quotient_ring_add_abelian_group = store_thm(
  "quotient_ring_add_abelian_group",
  ``!r:'a ring. Ring r /\ i << r ==> AbelianGroup (quotient_ring_add r i)``,
  rw_tac std_ss[AbelianGroup_def] >-
  rw_tac std_ss[quotient_ring_add_group] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw_tac std_ss[quotient_ring_add_def, quotient_ring_add_comm]);

(* ------------------------------------------------------------------------- *)
(* Quotient Ring (R/I).prod is an Abelian Monoid.                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: [Quotient Ring Mult Closure]
   Ring r /\ (i << r) ==> !x y. x IN R/I /\ y IN R/I ==> x * y IN R/I *)
(* Proof:
   Since   x * y = gen x * gen y o I
   and gen x IN R and gen y IN R    by ideal_cogen_property
   This is true by ideal_coset_property, ring_mult_element.
*)
val quotient_ring_mult_element = store_thm(
  "quotient_ring_mult_element",
  ``!r i:'a ring. Ring r /\ (i << r) ==> !x y. x IN R/I /\ y IN R/I ==> x * y IN R/I``,
  rw[ideal_cogen_property, ideal_coset_property]);

(* Theorem: [Quotient Ring Mult Commutative] Ring r /\ (i << r) ==> !x y. x IN R/I /\ y IN R/I ==> x * y = y * x *)
(* Proof:
   We have gen x IN R and gen y IN R    by ideal_cogen_property
     x * y
   = (gen x * gen y) o I     by ideal_coset_mult_def
   = (gen y * gen x) o I     by ring_mult_comm
   = y * x                   by ideal_coset_mult_def
*)
val quotient_ring_mult_comm = store_thm(
  "quotient_ring_mult_comm",
  ``!r i:'a ring. Ring r /\ (i << r) ==> !x y. x IN R/I /\ y IN R/I ==> (x * y = y * x)``,
  rw[ideal_cogen_property, ring_mult_comm]);

(* Theorem: Ring r /\ i << r /\ x IN R/I /\ y IN R/I /\ z IN R/I ==> x * y * z = x * (y * z) *)
(* Proof:
   We have gen x IN R, gen y IN R and gen z IN R by ideal_cogen_property.
   Hence gen x * gen y IN R               by ring_mult_element
     and gen ((gen x * gen y) o I) IN R   by ideal_coset_property, ideal_cogen_property
    Also gen y * gen z IN R               by ring_mult_element
     and gen ((gen y * gen z) o I) IN R   by ideal_coset_property, ideal_cogen_property

   First, show: x * y * z = (gen x * gen y * gen z) o I
   i.e.   x * y * z = (gen ((gen x * gen y) o I) * gen z) o I = (gen x * gen y * gen z) o I
   By ideal_coset_eq, this is true if
         (gen ((gen x * gen y) o I) * gen z) - (gen x * gen y * gen z) IN I
   Now   gen ((gen x * gen y) o I) o I = (gen x * gen y) o I   by ideal_coset_property
   hence gen ((gen x * gen y) o I) - (gen x * gen y) IN I      by ideal_coset_eq
   and   gen ((gen x * gen y) o I) - (gen x * gen y) * gen z IN I   by ideal_product_property
   or   (gen ((gen x * gen y) o I) * gen z) - (gen x * gen y * gen z) IN I   by ring_mult_lsub
   Hence true.

   Next, show: x * (y * z) = (gen x * (gen y * gen z)) o I
   i.e. (gen x * gen ((gen y * gen z) o I)) o I = (gen x * (gen y * gen z)) o I
   By ideal_coset_eq, this is true if
        (gen x * gen ((gen y * gen z) o I)) - (gen x * (gen y * gen z)) IN I
   Now   gen ((gen y * gen z) o I) o I = (gen y * gen z) o I    by ideal_coset_property
   hence (gen ((gen y * gen z) o I)) - (gen y * gen z) IN I     by ideal_coset_eq
   and   gen x * (gen ((gen y * gen z) o I)) - (gen y * gen z) IN I  by ideal_product_property
   or    (gen x * gen ((gen y + gen z) o I)) - (gen x * (gen y * gen z)) IN I  by ring_mult_rsub
   Hence true.

   Combining,
     x * y * z
   = (gen x * gen y * gen z) o I     by 1st result
   = (gen x * (gen y * gen z)) o I   by ring_mut_assoc
   = x * (y * z)                     by 2nd result
*)
val quotient_ring_mult_assoc = store_thm(
  "quotient_ring_mult_assoc",
  ``!r i:'a ring. Ring r /\ (i << r) ==> !x y z. x IN R/I /\ y IN R/I /\ z IN R/I ==> (x * y * z = x * (y * z))``,
  rw_tac std_ss[ideal_coset_mult_def] >>
  `gen x IN R /\ gen y IN R /\ gen z IN R` by rw_tac std_ss[ideal_cogen_property] >>
  `(gen ((gen x * gen y) o I) * gen z) o I = (gen x * gen y * gen z) o I` by
  (`gen x * gen y IN R` by rw[] >>
  `gen ((gen x * gen y) o I) IN R` by rw_tac std_ss[ideal_coset_property, ideal_cogen_property] >>
  `gen ((gen x * gen y) o I) - (gen x * gen y) IN I` by metis_tac[ideal_coset_eq, ideal_coset_property] >>
  `(gen ((gen x * gen y) o I) - (gen x * gen y)) * gen z IN I` by rw_tac std_ss[ideal_product_property] >>
  `(gen ((gen x * gen y) o I) * gen z) - (gen x * gen y * gen z) IN I` by rw_tac std_ss[ring_mult_lsub] >>
  rw_tac std_ss[ideal_coset_eq, ring_mult_element]) >>
  `(gen x * gen ((gen y * gen z) o I)) o I = (gen x * (gen y * gen z)) o I` by
    (`gen y * gen z IN R` by rw[] >>
  `gen ((gen y * gen z) o I) IN R` by rw_tac std_ss[ideal_coset_property, ideal_cogen_property] >>
  `gen ((gen y * gen z) o I) - (gen y * gen z) IN I` by metis_tac[ideal_coset_eq, ideal_coset_property] >>
  `gen x * (gen ((gen y * gen z) o I) - (gen y * gen z)) IN I` by rw_tac std_ss[ideal_product_property] >>
  `gen x * gen ((gen y * gen z) o I) - (gen x * (gen y * gen z)) IN I` by rw_tac std_ss[ring_mult_rsub] >>
  rw_tac std_ss[ideal_coset_eq, ring_mult_element]) >>
  rw_tac std_ss[ring_mult_assoc]);

(* Theorem: [Quotient Ring Mult Identity] Ring r /\ i << r ==> !x. x IN R/I ==> ((#1 o I) * x = x) /\ (x * (#1 o I) = x) *)
(* Proof:
   #1 IN R                            by ring_one_element
   #1 o I IN R/I                      by ideal_coset_property
   gen x IN R /\ gen (#1 o I) IN R    by ideal_cogen_property
   and x = gen x o I                  by ideal_cogen_property
   and gen (#1 o I) o I = #1 o I      by ideal_cogen_property
   or  gen (#1 o I) - #1 IN I         by ideal_coset_eq

   Hence this is to show:
        gen (#1 o I) * gen x o I = x = gen x o I
   and  gen x * gen (#1 o I) o I = x = gen x o I

   For the first case:
       gen (#1 o I) - #1 IN I
   ==> (gen (#1 o I) - #1) * gen x IN I        by ideal_product_property
   ==> gen (#1 o I) * gen x - #1 * gen x IN I  by ring_mult_lsub
   ==> gen (#1 o I) * gen x - gen x IN I       by ring_mult_lone
   Hence true by ideal_coset_eq.

   For the second case:
       gen (#1 o I) - #1 IN I
   ==> gen x * (gen (#1 o I) - #1) IN I        by ideal_product_property
   ==> gen x * gen (#1 o I) - gen x * #1 IN I  by ring_mult_rsub
   ==> gen x * gen (#1 o I) - gen x IN I       by ring_mult_rone
   Hence true by ideal_coset_eq.
*)
val quotient_ring_mult_id = store_thm(
  "quotient_ring_mult_id",
  ``!r i:'a ring. Ring r /\ i << r ==> !x. x IN R/I ==> ((#1 o I) * x = x) /\ (x * (#1 o I) = x)``,
  ntac 5 strip_tac >>
  `#1 IN R` by rw[] >>
  `#1 o I IN R/I` by rw_tac std_ss[ideal_coset_property] >>
  `gen x IN R /\ gen (#1 o I) IN R /\ (x = gen x o I) /\ (gen (#1 o I) o I = #1 o I)` by rw_tac std_ss[ideal_cogen_property] >>
  `gen (#1 o I) - #1 IN I` by metis_tac[ideal_coset_eq] >>
  rw_tac std_ss[ideal_coset_mult_def] >| [
    `(gen (#1 o I) - #1) * gen x IN I` by rw_tac std_ss[ideal_product_property] >>
    `gen (#1 o I) * gen x - #1 * gen x IN I` by rw_tac std_ss[ring_mult_lsub] >>
    `gen (#1 o I) * gen x - gen x IN I` by metis_tac[ring_mult_lone],
    `gen x * (gen (#1 o I) - #1) IN I` by rw_tac std_ss[ideal_product_property] >>
    `gen x * gen (#1 o I) - gen x * #1 IN I` by rw_tac std_ss[ring_mult_rsub] >>
    `gen x * gen (#1 o I) - gen x IN I` by metis_tac[ring_mult_rone]
  ] >>
  metis_tac[ideal_coset_eq, ring_mult_element]);

(* Theorem: quotient_ring_mult is a Monoid. *)
(* Proof:
   Check for each monoid property:
   Closure: by quotient_ring_mult_element
   Associative: by quotient_ring_mult_assoc
   Identity: by quotient_ring_mult_id, and ideal_coset_property, ring_one_element
*)
val quotient_ring_mult_monoid = store_thm(
  "quotient_ring_mult_monoid",
  ``!r i:'a ring. Ring r /\ (i << r) ==> Monoid (quotient_ring_mult r i)``,
  rw_tac std_ss[Monoid_def, quotient_ring_mult_def] >| [
    rw_tac std_ss[quotient_ring_mult_element],
    rw_tac std_ss[quotient_ring_mult_assoc],
    rw_tac std_ss[ideal_coset_property, ring_one_element],
    rw_tac std_ss[quotient_ring_mult_id],
    rw_tac std_ss[quotient_ring_mult_id]
  ]);

(* Theorem: quotient_ring_mult is an Abelain Monoid. *)
(* Proof:
   By quotient_ring_mult_monoid, and quotient_ring_mult_comm.
*)
val quotient_ring_mult_abelian_monoid = store_thm(
  "quotient_ring_mult_abelian_monoid",
  ``!r:'a ring. Ring r /\ i << r ==> AbelianMonoid (quotient_ring_mult r i)``,
  rw_tac std_ss[AbelianMonoid_def] >-
  rw_tac std_ss[quotient_ring_mult_monoid] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw_tac std_ss[quotient_ring_mult_def, quotient_ring_mult_comm]);

(* ------------------------------------------------------------------------- *)
(* Quotient Ring (R/I) is a Ring.                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r /\ i << r ==> x * (y + z) = x * y + x * z *)
(* Proof:
   We have gen x IN R, gen y IN R, gen z IN R        by ideal_cogen_property
   Thus    gen y + gen z IN R                        by ring_add_element
   and     gen x * gen y IN R /\ gen x * gen z IN R  by ring_mult_element

   First, show that: (gen x * gen ((gen y + gen z) o I)) o I = (gen x * (gen y + gen z)) o I
   Let t = gen y + gen z, t IN R  by ring_add_element
   Hence t o I IN R/I             by coset_partition_element
   and gen (t o I) IN R           by cogen_element
   Now the goal reduces to: (gen x * gen (t o I)) o I = (gen x * t) o I
   Since gen (t o I) o I = t o I  by ideal_cogen_property
         gen (t o I) - t IN I     by ideal_coset_eq
   hence gen x * (gen (t o I) - t) IN I         by ideal_product_property
      or gen x * gen (t o I) - gen x * t IN I   by ring_mult_rsub
   Hence true by ideal_coset_eq, ring_mult_element.

   Next, show that: (gen ((gen x * gen y) o I) + gen ((gen x * gen z) o I)) o I = (gen x * gen y + gen x * gen z) o I
   Let p = gen x * gen y, p IN R  by ring_mult_element
   Let q = gen x * gen z, q IN R  by ring_mult_element
   Hence gen (p o I) IN R         by ideal_cogen_property
   and   gen (q o I) IN R         by ideal_cogen_property
   Now the goal reduces to: gen (p o I) + gen (q o I) o I = p + q o I
     gen (p o I) + gen (q o I) - (p + q)
   = (gen (p o I) - p) + (gen (q o I) - q)      by ring_add_pair_sub
   Since      gen (p o I) o I = p o I           by ideal_cogen_property
              gen (p o I) - p IN I              by ideal_coset_eq
   Similarly, gen (q o I) o I = q o I           by ideal_cogen_property
              gen (q o I) - q IN I              by ideal_coset_eq
   Now by subgroup_property,
     Group i.sum /\ (!x y. x IN I /\ y IN I ==> (i.sum.op x y = x + y))
   Thus gen (p o I) + gen (q o I) - (p + q) IN I by group_op_element.
   Hence true by ideal_coset_eq, ring_add_element.

   Combining,
     gen x * gen (gen y + gen z o I) o I
   = (gen x * (gen y + gen z)) o I                          by 1st result
   = (gen x * gen y + gen x * gen z) o I                    by ring_mult_radd
   = gen (gen x * gen y o I) + gen (gen x * gen z o I) o I  by 2nd result
*)
val quotient_ring_mult_ladd = store_thm(
  "quotient_ring_mult_ladd",
  ``!r i:'a ring. Ring r /\ i << r ==> !x y z. x IN R/I /\ y IN R/I /\ z IN R/I ==> (x * (y + z) = x * y + x * z)``,
  rw_tac std_ss[ideal_coset_add_def, ideal_coset_mult_def] >>
  `gen x IN R /\ gen y IN R /\ gen z IN R` by rw_tac std_ss[ideal_cogen_property] >>
  `gen y + gen z IN R /\ gen x * gen y IN R /\ gen x * gen z IN R` by rw[] >>
  `(gen x * gen ((gen y + gen z) o I)) o I = (gen x * (gen y + gen z)) o I` by
  (qabbrev_tac `t = gen y + gen z` >>
  `gen (t o I) IN R /\ (gen (t o I) o I = t o I)` by rw_tac std_ss[ideal_coset_property, ideal_cogen_property] >>
  `gen (t o I) - t IN I` by metis_tac[ideal_coset_eq] >>
  `gen x * (gen (t o I) - t) IN I` by rw_tac std_ss[ideal_product_property] >>
  `gen x * gen (t o I) - gen x * t IN I` by rw_tac std_ss[ring_mult_rsub] >>
  rw_tac std_ss[ideal_coset_eq, ring_mult_element]) >>
  `(gen ((gen x * gen y) o I) + gen ((gen x * gen z) o I)) o I = (gen x * gen y + gen x * gen z) o I` by
    (qabbrev_tac `p = gen x * gen y` >>
  qabbrev_tac `q = gen x * gen z` >>
  `gen (p o I) IN R /\ (gen (p o I) o I = p o I)` by rw_tac std_ss[ideal_coset_property, ideal_cogen_property] >>
  `gen (q o I) IN R /\ (gen (q o I) o I = q o I)` by rw_tac std_ss[ideal_coset_property, ideal_cogen_property] >>
  `gen (p o I) - p IN I` by metis_tac[ideal_coset_eq] >>
  `gen (q o I) - q IN I` by metis_tac[ideal_coset_eq] >>
  `gen (p o I) + gen (q o I) - (p + q) = (gen (p o I) - p) + (gen (q o I) - q)` by rw_tac std_ss[ring_add_pair_sub] >>
  `gen (p o I) + gen (q o I) - (p + q) IN I` by metis_tac[ideal_property] >>
  rw_tac std_ss[ideal_coset_eq, ring_add_element]) >>
  rw_tac std_ss[ring_mult_radd]);

(* Theorem: Ring r /\ i << r ==> Ring (r/i) *)
(* Proof:
   Check for each ring property:
   Abelian Sum group: by quotient_ring_add_abelian_group
   Abelian Prod monoid: by quotient_ring_mult_abelian_monoid
   Distribution of sum over product: by quotient_ring_mult_ladd.
*)
val quotient_ring_ring = store_thm(
  "quotient_ring_ring",
  ``!r i:'a ring. Ring r /\ i << r ==> Ring (r / i)``,
  rpt strip_tac >>
  rw_tac std_ss[Ring_def, quotient_ring_def] >| [
    rw_tac std_ss[quotient_ring_add_abelian_group],
    rw_tac std_ss[quotient_ring_mult_abelian_monoid],
    rw_tac std_ss[quotient_ring_add_def],
    rw_tac std_ss[quotient_ring_mult_def],
    rw_tac std_ss[quotient_ring_add_def, quotient_ring_mult_def, quotient_ring_mult_ladd]
  ]);

(* Theorem: (r/r).carrier = {R} *)
(* Proof: by defintions, this is to show:
   (1) x'' IN x /\ !x''. (x'' IN x ==> x'' IN R /\ x'' IN x' o R) ==> x'' IN R
       True by implication.
   (2) x'' IN R /\ !x''. (x'' IN R /\ x'' IN x' o R ==> x'' IN x) ==> x'' IN x
       Since (x'' - x') IN R      by ring_sub_element
       and x'' = x'' - x' + x'    by ring_sub_add
               = x' + (x'' - x')  by ring_add_comm
       True by coset_def
   (3) !x'. (x' IN x ==> x' IN R) /\ (x' IN R ==> x' IN x) ==> ?x'. x' IN R /\ !x''. x'' IN x ==> x'' IN x' o R
       Let x' = #0, then #0 IN R         by ring_zero_element
       and !x''. x'' IN x ==> x'' IN R   by given implication
       Since r << r                      by ideal_refl
          x' o R = #0 o R = R            by ideal_coset_zero
       Hence true.
*)
val quotient_ring_ring_sing = store_thm(
  "quotient_ring_ring_sing",
  ``!r:'a ring. Ring r ==> ((r/r).carrier = {R})``,
  rw[quotient_ring_def, CosetPartition_def, partition_def, inCoset_def, EXTENSION] >>
  rw[EQ_IMP_THM] >| [
    metis_tac[],
    `!y z. y IN R /\ z IN R ==> (z = y + (z - y))` by metis_tac[ring_sub_add, ring_add_comm, ring_sub_element] >>
    `!x z. x IN R ==> (z IN x o R <=> ?y. y IN R /\ (z = x + y))` by (rw[coset_def] >> metis_tac[]) >>
    metis_tac[ring_sub_element],
    `#0 IN R /\ (#0 o R = R)` by rw[ideal_coset_zero, ideal_refl] >>
    metis_tac[]
  ]);
(* Michael's proof:
val quotient_ring_ring_sing = store_thm(
  "quotient_ring_ring_sing",
  ``!r:'a ring. Ring r ==> ((r/r).carrier = {R})``,
  rw[quotient_ring_def, CosetPartition_def, partition_def, inCoset_def, EXTENSION] >>
  rw[EQ_IMP_THM] >| [
    metis_tac[],
    qcase_tac `y o R` >>
    qcase_tac `_ IN R' ==> _` >>
    qcase_tac `z IN R'` >>
    `z = z - y + y` by rw[ring_sub_add] >>
    `_ = y + (z - y)` by rw[ring_add_comm] >>
    `!z. z IN y o R <=> ?y'. y' IN R /\ (z = y + y')` by rw[coset_def] >| [
      metis_tac[],
      metis_tac[ring_sub_element]
    ],
    `#0 IN R` by rw[] >>
    `#0 o R = R` by rw[ideal_coset_zero, ideal_refl] >>
    metis_tac[]
  ]);
*)

(* ------------------------------------------------------------------------- *)
(* Quotient Ring by Principal Ideal                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring (r / <p>) *)
(* Proof:
   by quotient_ring_ring, principal_ideal_ideal.
*)
val quotient_ring_by_principal_ideal = store_thm(
  "quotient_ring_by_principal_ideal",
  ``!r:'a ring. Ring r ==> !p. p IN R ==> Ring (r / <p>)``,
  rw[quotient_ring_ring, principal_ideal_ideal]);

(* ------------------------------------------------------------------------- *)
(* Quotient Ring Homomorphism                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: [Ring homomorphism to Quotient Ring] The map: x -> x o I is a homomorphism from R to (R/I). *)
(* Proof:
   This is to show:
   (1) Ring r /\ i << r /\ x IN R ==> x o I IN R/I
       True by ideal_coset_property
   (2) same as (1)
   (3) Ring r /\ i << r /\ x IN R /\ x' IN R ==> (x + x') o I = x o I + x' o I
       By ideal_coset_add_def, this is to show: (x + x') o I = (gen (x o I) + gen (x' o I)) o I
       Now   gen (x o I) IN R /\ gen (x o I) o I = x o I      by ideal_cogen_property, ideal_coset_property
       and   gen (x' o I) IN R /\ gen (x' o I) o I = x' o I   by ideal_cogen_property, ideal_coset_property
       Hence   gen (x o I) - x IN I     by ideal_coset_eq
       and     gen (x' o I) - x' IN I   by ideal_coset_eq
       But     gen (x o I) + gen (x' o I) - (x + x')
             = (gen (x o I) - x) + (gen (x' o I) - x')        by ring_add_pair_sub
       By ideal_property, each component is IN I.
       Hence true by ideal_coset_eq.
   (4) same as (1)
   (5) Ring r /\ i << r /\ x IN R /\ x' IN R ==> (x * x') o I = x o I * x' o I
       By ideal_coset_mult_def, this is to show: (x * x') o I = (gen (x o I) * gen (x' o I)) o I
       gen (x o I) * gen (x' o I) - (x * x')
       = (gen (x o I) - x) * (gen (x' o I) - x') +  (gen (x o I) - x) * x' + x * (gen (x' o I) - x')
             in I               in I                    in I           in R  in R  in I
       By ideal_product_property and ideal_property, each component is IN I.
       Hence true by ideal_coset_eq.
*)
val quotient_ring_homo = store_thm(
  "quotient_ring_homo",
  ``!r i:'a ring. Ring r /\ i << r ==> RingHomo (\x. x o I) r (r / i)``,
  rw_tac std_ss[RingHomo_def, GroupHomo_def, MonoidHomo_def, quotient_ring_def, quotient_ring_add_def, quotient_ring_mult_def, ring_add_group, ring_mult_monoid] >-
  rw_tac std_ss[ideal_coset_property] >-
  rw_tac std_ss[ideal_coset_property] >-
 (rw_tac std_ss[ideal_coset_add_def] >>
  `gen (x o I) - x IN I` by metis_tac[ideal_cogen_property, ideal_coset_property, ideal_coset_eq] >>
  `gen (x' o I) - x' IN I` by metis_tac[ideal_cogen_property, ideal_coset_property, ideal_coset_eq] >>
  `gen (x o I) IN R /\ gen (x' o I) IN R` by metis_tac[ideal_cogen_property, ideal_coset_property] >>
  `gen (x o I) + gen (x' o I) - (x + x') = (gen (x o I) - x) + (gen (x' o I) - x')`
    by rw_tac std_ss[ring_add_pair_sub] >>
  `gen (x o I) + gen (x' o I) - (x + x') IN I` by metis_tac[ideal_property] >>
  metis_tac[ideal_coset_eq, ring_add_element]) >-
  rw_tac std_ss[ideal_coset_property] >>
  rw_tac std_ss[ideal_coset_mult_def] >>
  `gen (x o I) IN R /\ gen (x' o I) IN R` by metis_tac[ideal_cogen_property, ideal_coset_property] >>
  `gen (x o I) * gen (x' o I) - (x * x') =
   (gen (x o I) - x) * (gen (x' o I) - x') + (gen (x o I) - x) * x' + x * (gen (x' o I) - x')`
     by rw_tac std_ss[ring_mult_pair_sub] >>
  `gen (x o I) - x IN I` by metis_tac[ideal_cogen_property, ideal_coset_property, ideal_coset_eq] >>
  `gen (x' o I) - x' IN I` by metis_tac[ideal_cogen_property, ideal_coset_property, ideal_coset_eq] >>
  `gen (x o I) * gen (x' o I) - x * x' IN I` by metis_tac[ideal_property, ideal_product_property] >>
  metis_tac[ideal_coset_eq, ring_mult_element]);

(* Theorem: The quotient ring homomorphism is surjective. *)
(* Proof: by SURJ_DEF, this is to show:
   (1) x IN R ==> x o I IN R/I
       True by ideal_coset_property
   (2) x IN R/I ==> ?x'. x' IN R /\ (x' o I = x)
       Since  i.sum <= r.sum   by ideal_def
       r.sum.carrier = R       by Ring_def
       i.sum.carrier = I       by ideal_def
       True by coset_partition_element.
*)
val quotient_ring_homo_surj = store_thm(
  "quotient_ring_homo_surj",
  ``!(r:'a ring) (i:'a ring). Ring r /\ i << r ==> SURJ (\x. x o I) R R/I``,
  rw[SURJ_DEF] >| [
    rw[ideal_coset_property],
    `i.sum <= r.sum` by metis_tac[ideal_def] >>
    `r.sum.carrier = R` by rw[] >>
    `i.sum.carrier = I` by metis_tac[ideal_def] >>
    metis_tac[coset_partition_element]
  ]);

(* Theorem: In the ring homomorphism x -> x o I, its kernel = I *)
(* Proof:
   This is to show: {x | x IN R /\ (x o I = I)} = I
   If x IN R /\ (x o I = I),
      Since I = #0 o I       by ideal_coset_zero
      we have x o I = #0 o I
      or  x - #0 IN I        by ideal_coset_eq
      i.e. x IN I            by ring_sub_zero
   If x IN I
      then x IN R            by ideal_element_property
      and since x - #0 IN I  by ring_sub_zero
      x o I = #0 o I         by ideal_coset_eq
            = I              by ideal_coset_zero
*)
val quotient_ring_homo_kernel = store_thm(
  "quotient_ring_homo_kernel",
  ``!r i:'a ring. Ring r /\ i << r ==> (kernel (\x. x o I) r.sum (r / i).sum = I)``,
  rw_tac std_ss[kernel_def, preimage_def, quotient_ring_def, quotient_ring_add_def, ring_add_group] >>
  `#0 o I = I` by rw_tac std_ss[ideal_coset_zero] >>
  rw[Once EXTENSION, EQ_IMP_THM] >| [
    metis_tac[ideal_coset_eq, ring_zero_element, ring_sub_zero],
    metis_tac[ideal_element_property],
    metis_tac[ideal_coset_eq, ring_sub_zero, ideal_element_property, ring_zero_element]
  ]);

(* ------------------------------------------------------------------------- *)
(* Kernel of Ring Homomorphism.                                              *)
(* ------------------------------------------------------------------------- *)

(* Define the Kernel Ideal of a ring homomorphism. *)
val kernel_ideal_def = Define`
  kernel_ideal f (r:'a ring) (s:'b ring) =
    <| carrier := kernel f r.sum s.sum;  (* e.g. s = r / i *)
           sum := <| carrier := kernel f r.sum s.sum; op := r.sum.op; id := r.sum.id |>;
          prod := <| carrier := kernel f r.sum s.sum; op := r.prod.op; id := r.prod.id |>
     |>`;

(* Theorem: (kernel_ideal f r s).sum = kernel_group f r.sum s.sum *)
(* Proof: kernel_ideal_def, kernel_group_def *)
val kernel_ideal_sum_eqn = store_thm(
  "kernel_ideal_sum_eqn",
  ``!(r:'a ring) (s:'b ring) f. (kernel_ideal f r s).sum = kernel_group f r.sum s.sum``,
  rw_tac std_ss[kernel_ideal_def, kernel_group_def]);

(* Theorem: x IN (kernel_ideal f r r_).carrier <=> x IN r.sum.carrier /\ (f x = #0_) *)
(* Proof:
       x IN (kernel_ideal f r r_).carrier
   <=> x IN kernel f r.sum r_.sum           by kernel_ideal_def
   <=> x IN preimage f r.sum.carrier #0_    by kernel_def
   <=> x IN r.sum.carrier /\ (f x = #0_)    by in_preimage
*)
val kernel_ideal_element = store_thm(
  "kernel_ideal_element",
  ``!(r:'a ring) (r_:'b ring) f x.
     x IN (kernel_ideal f r r_).carrier <=> x IN r.sum.carrier /\ (f x = #0_)``,
  rw_tac std_ss[kernel_ideal_def, kernel_def, in_preimage]);

(*
CONJ_ASM1_TAC      A ==> B /\ C  to A ==> B,  A /\ B ==> C
CONJ_ASM2_TAC      A ==> B /\ C  to A ==> C,  A /\ C ==> B
*)

(* Theorem: If f is a Ring homomorphism, kernel_ideal is an ideal. *)
(* Proof:
   Ring r, s ==> Group r.sum /\ Group s.sum     by ring_add_group
   RingHomo f r s ==> GroupHomo f r.sum s.sum   by RingHomo_def
   This is to show:
   (1) <|carrier := kernel f r.sum s.sum; op := $+; id := #0|> <= r.sum
       This splits into two:
       the first one is: Group <|carrier := kernel f r.sum s.sum; op := $+; id := #0|>
       This reduces to 7 subgoals:
       1. x IN R /\ y IN R ==> x + y IN R     true by ring_add_element
       2. f x = s.sum.id /\ f y = s.sum.id ==> f (x + y) = s.sum.id
          Since   f (x + y) = s.sum.op (f x) (f y))   by GroupHomo_def
          Hence true by group_id_id.
       3. x IN R /\ y IN R /\ z IN R ==> x + y + z = x + (y + z)   true by ring_add_assoc
       4. #0 IN R     true by ring_zero_element
       5. f #0 = s.sum.id
          Since  f (x + y) = s.sum.op (f x) (f y))   by GroupHomo_def, RingHomo_def, ring_add_group
          Using group_id_id,  f #0 = f (#0 + #0) = s.sum.op (f #0) (f #0)
          Hence f #0 = s.sum.id      by group_id_fix
       6. x IN R ==> #0 + x = x      true by ring_add_lzero
       7. x IN R /\ f x = s.sum.id ==> ?y. (y IN R /\ (f y = s.sum.id)) /\ (y + x = #0)
          x IN R ==> -x IN R         by ring_neg_element
          Let y = -x, then y IN R, and y + x = #0   by ring_add_lneg
          f y = s.sum.op ((f y) s.sum.id)      by group_rid
              = s.sum.op ((f y) (f x))         by given
              = f (y + x)                      by GroupHomo_def
              = f #0                           by above
              = s.sum.id                       by 5.
       The second is: kernel f r.sum s.sum SUBSET R
       True by kernel_def.
   (2) x IN kernel f r.sum s.sum /\ y IN R ==> x * y IN kernel f r.sum s.sum
       This reduces to 2 subgoals:
       1. x IN kernel f r.sum s.sum /\ y IN R ==> x * y IN R
          Since   kernel f r.sum s.sum SUBSET R  by (2)
          This is true by ring_mult_element and SUBSET_DEF.
       2. x IN kernel f r.sum s.sum /\ y IN R ==> f (x * y) = s.sum.id
          Since x IN kernel f r.sum s.sum, f x = s.sum.id    by kernel_def
          f (x * y) = s.prod.op (s.sum.id) (f y)             by MonoidHomo_def
                    = s.sum.id                               by ring_mult_lzero
   (3) x IN kernel f r.sum s.sum /\ y IN R ==> y * x IN kernel f r.sum s.sum
       Since kernel f r.sum s.sum SUBSET R     by kernel_def
       x IN R                                  by SUBSET_DEF
       Hence this follows from (2) by ring_mult_comm.
*)
val ring_homo_kernel_ideal = store_thm(
  "ring_homo_kernel_ideal",
  ``!f (r:'a ring) (s:'b ring). Ring r /\ Ring s /\ RingHomo f r s ==> kernel_ideal f r s << r``,
  rpt strip_tac >>
  `GroupHomo f r.sum s.sum` by metis_tac[RingHomo_def] >>
  `MonoidHomo f r.prod s.prod` by metis_tac[RingHomo_def] >>
  `Group r.sum /\ Group s.sum /\ (r.sum.carrier = R) /\ (s.sum.carrier = s.carrier)` by rw_tac std_ss[ring_add_group] >>
  `Monoid r.prod /\ Monoid s.prod /\ (r.prod.carrier = R) /\ (s.prod.carrier = s.carrier)` by rw_tac std_ss[ring_mult_monoid] >>
  rw_tac std_ss[kernel_ideal_def, ideal_def] >| [
    rw_tac std_ss[Subgroup_def] >| [
      rw_tac std_ss[group_def_alt, kernel_def, preimage_def, GSPECIFICATION] >-
      rw_tac std_ss[ring_add_element] >-
      metis_tac[GroupHomo_def, group_id_id] >-
      rw_tac std_ss[ring_add_assoc] >-
      rw_tac std_ss[ring_zero_element] >-
      metis_tac[GroupHomo_def, group_id_id, group_id_fix, ring_zero_element] >-
      rw_tac std_ss[ring_add_lzero] >>
      `-x IN R /\ (-x + x = #0)` by rw_tac std_ss[ring_neg_element, ring_add_lneg] >>
      qexists_tac `-x` >>
      rw_tac std_ss[] >>
      metis_tac[GroupHomo_def, group_id_id, group_id_fix, ring_zero_element, ring_add_lneg, group_rid],
      rw[kernel_def, preimage_def, SUBSET_DEF]
    ],
    `kernel f r.sum s.sum SUBSET R` by rw[kernel_def, preimage_def, SUBSET_DEF] >>
    rw_tac std_ss[kernel_def, preimage_def, GSPECIFICATION] >-
    metis_tac[SUBSET_DEF, ring_mult_element] >>
    `x IN R` by metis_tac[SUBSET_DEF] >>
    `!x. x IN kernel f r.sum s.sum ==> (f x = s.sum.id)` by rw_tac std_ss[kernel_def, preimage_def, GSPECIFICATION] >>
    metis_tac[MonoidHomo_def, ring_mult_monoid, ring_mult_lzero],
    `kernel f r.sum s.sum SUBSET R` by rw[kernel_def, preimage_def, SUBSET_DEF] >>
    rw_tac std_ss[kernel_def, preimage_def, GSPECIFICATION] >-
    metis_tac[SUBSET_DEF, ring_mult_element] >>
    `x IN R` by metis_tac[SUBSET_DEF] >>
    `!x. x IN kernel f r.sum s.sum ==> (f x = s.sum.id)` by rw_tac std_ss[kernel_def, preimage_def, GSPECIFICATION] >>
    metis_tac[MonoidHomo_def, ring_mult_monoid, ring_mult_rzero]
  ]);

(* Theorem: Any ideal will induce a ring homomorphism f from r to (r / i) such that kernel_ideal f = i *)
(* Proof:
   We have shown: Ring r /\ i << r ==> RingHomo (\x. x o I) r (r / i)   by quotient_ring_homo
   And we have: Ring r /\ i << r ==> (kernel (\x. x o I) r.sum (r / i).sum = I  by quotient_ring_homo_kernel
   The remaining cases are:
   (1) <|carrier := kernel (\x. x o I) r.sum (r / i).sum; op := $+; id := #0|> = i.sum
       kernel (\x. x o I) r.sum (r / i).sum = I    by quotient_ring_homo_kernel
       i.sum.carrier = I                           by ideal_def
       i.sum.op = r.sum.op                         by ideal_ops
       i.sum.id = #0                               by subgroup_id
       Hence true by monoid_component_equality.
   (2) <|carrier := kernel (\x. x o I) r.sum (r / i).sum; op := $*; id := #1|> = i.prod
       kernel (\x. x o I) r.sum (r / i).sum = I    by quotient_ring_homo_kernel
       i.prod.carrier = I                          by ideal_def
       i.prod.op = r.prod.op                       by ideal_def
       i.prod.id = #1                              by ideal_def

*)
val quotient_ring_homo_kernel_ideal = store_thm(
  "quotient_ring_homo_kernel_ideal",
  ``!r i:'a ring. Ring r /\ i << r ==> RingHomo (\x. x o I) r (r / i) /\ (kernel_ideal (\x. x o I) r (r / i) = i)``,
  rw_tac std_ss[quotient_ring_homo] >>
  rw_tac std_ss[kernel_ideal_def] >>
  `kernel (\x. x o I) r.sum (r / i).sum = I` by rw_tac std_ss[quotient_ring_homo_kernel] >>
  rw_tac std_ss[ring_component_equality] >| [
    `i.sum <= r.sum /\ (i.sum.carrier = I) /\ (i.sum.op = r.sum.op)` by metis_tac[ideal_def, ideal_ops] >>
    `i.sum.id = #0` by rw_tac std_ss[subgroup_id],
    `(i.prod.carrier = I) /\ (i.prod.op = r.prod.op) /\ (i.prod.id = #1)` by metis_tac[ideal_def]
  ] >>
  rw_tac std_ss[monoid_component_equality]);

(* ------------------------------------------------------------------------- *)
(* First Isomorphism Theorem for Ring.                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in
            !x y. x IN R/I /\ y IN R/I ==> (f (gen ((gen x + gen y) o I)) = (f (gen x)) +_ (f (gen y))) *)
(* Proof:
   Let t = gen x + gen y.
   The goal becomes: f (gen (t o I)) = f (gen x) +_ f (gen y)
   Note i << r                           by ring_homo_kernel_ideal
    ==> gen x IN R /\ gen y IN R         by ideal_cogen_property
     so t IN R                           by ring_add_element
    ==> t o I IN R/I                     by ideal_coset_property, t IN R
     so gen (t o I) IN R                 by ideal_cogen_property
   Thus f (gen (t o I)) IN R_            by ring_homo_element
    and f (gen x) IN R_                  by ring_homo_element
    and f (gen y) IN R_                  by ring_homo_element
     so (f (gen x) +_ f (gen y)) IN R_   by ring_add_element

   Note gen (t o I) - t IN I             by ideal_coset_has_gen_diff

        f (gen (t o I)) -_ (f (gen x) +_ f (gen y))
      = f (gen (t o I)) -_ (f t)         by ring_homo_add
      = f (gen (t o I) - t)              by ring_homo_sub
      = #0_                              by kernel_ideal_element

   Thus f (gen (t o I)) = f (gen x) +_ f (gen y)   by ring_sub_eq_zero
*)
val kernel_ideal_gen_add_map = store_thm(
  "kernel_ideal_gen_add_map",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in
    !x y. x IN R/I /\ y IN R/I ==> (f (gen ((gen x + gen y) o I)) = (f (gen x)) +_ (f (gen y)))``,
  rw_tac std_ss[] >>
  qabbrev_tac `t = gen x + gen y` >>
  `i << r` by rw[ring_homo_kernel_ideal, Abbr`i`] >>
  `gen x IN R /\ gen y IN R` by rw[ideal_cogen_property] >>
  `t IN R` by rw[Abbr`t`] >>
  `t o I IN R/I` by rw[ideal_coset_property] >>
  `gen (t o I) IN R` by rw[ideal_cogen_property] >>
  `f (gen (t o I)) IN R_ /\ f (gen x) IN R_ /\ f (gen y) IN R_` by metis_tac[ring_homo_element] >>
  `(f (gen x) +_ f (gen y)) IN R_` by rw[] >>
  `gen (t o I) - t IN I` by rw[ideal_coset_has_gen_diff] >>
  `f (gen (t o I)) -_ (f (gen x) +_ f (gen y)) = f (gen (t o I)) -_ f t` by metis_tac[ring_homo_add] >>
  `_ = f (gen (t o I) - t)` by rw[ring_homo_sub] >>
  `_ = #0_` by metis_tac[kernel_ideal_element] >>
  metis_tac[ring_sub_eq_zero]);

(* Theorem: (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in
            !x y. x IN R/I /\ y IN R/I ==> (f (gen ((gen x * gen y) o I)) = (f (gen x)) *_ (f (gen y))) *)
(* Proof:
   Let t = gen x * gen y.
   The goal becomes: f (gen (t o I)) = f (gen x) *_ f (gen y)
   Note i << r                           by ring_homo_kernel_ideal
    ==> gen x IN R /\ gen y IN R         by ideal_cogen_property
     so t IN R                           by ring_add_element
    ==> t o I IN R/I                     by ideal_coset_property, t IN R
     so gen (t o I) IN R                 by ideal_cogen_property
   Thus f (gen (t o I)) IN R_            by ring_homo_element
    and f (gen x) IN R_                  by ring_homo_element
    and f (gen y) IN R_                  by ring_homo_element
     so (f (gen x) *_ f (gen y)) IN R_   by ring_mult_element

   Note gen (t o I) - t IN I             by ideal_coset_has_gen_diff

        f (gen (t o I)) -_ (f (gen x) *_ f (gen y))
      = f (gen (t o I)) -_ (f t)         by ring_homo_mult
      = f (gen (t o I) - t)              by ring_homo_sub
      = #0_                              by kernel_ideal_element

   Thus f (gen (t o I)) = f (gen x) *_ f (gen y)   by ring_sub_eq_zero
*)
val kernel_ideal_gen_mult_map = store_thm(
  "kernel_ideal_gen_mult_map",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in
    !x y. x IN R/I /\ y IN R/I ==> (f (gen ((gen x * gen y) o I)) = (f (gen x)) *_ (f (gen y)))``,
  rw_tac std_ss[] >>
  qabbrev_tac `t = gen x * gen y` >>
  `i << r` by rw[ring_homo_kernel_ideal, Abbr`i`] >>
  `gen x IN R /\ gen y IN R` by rw[ideal_cogen_property] >>
  `t IN R` by rw[Abbr`t`] >>
  `t o I IN R/I` by rw[ideal_coset_property] >>
  `gen (t o I) IN R` by rw[ideal_cogen_property] >>
  `f (gen (t o I)) IN R_ /\ f (gen x) IN R_ /\ f (gen y) IN R_` by metis_tac[ring_homo_element] >>
  `(f (gen x) *_ f (gen y)) IN R_` by rw[] >>
  `gen (t o I) - t IN I` by rw[ideal_coset_has_gen_diff] >>
  `f (gen (t o I)) -_ (f (gen x) *_ f (gen y)) = f (gen (t o I)) -_ f t` by metis_tac[ring_homo_mult] >>
  `_ = f (gen (t o I) - t)` by rw[ring_homo_sub] >>
  `_ = #0_` by metis_tac[kernel_ideal_element] >>
  metis_tac[ring_sub_eq_zero]);

(* Theorem: (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in
            !x y. x IN R/I /\ y IN R/I ==> (f (gen (#1 o I)) = #1_) *)
(* Proof:
   Note i << r                           by ring_homo_kernel_ideal
    and #1 IN R /\ #1_ IN R_             by ring_add_element
    ==> #1 o I IN R/I                    by ideal_coset_property, #1 IN R
     so gen (#1 o I) IN R                by ideal_cogen_property
   Thus f (gen (#1 o I)) IN R_           by ring_homo_element

   Note gen (#1 o I) - #1 IN I           by ideal_coset_has_gen_diff

        f (gen (#1 o I)) -_ #1_
      = f (gen (#1 o I)) -_ (f #1)       by ring_homo_ids
      = f (gen (#1 o I) - #1)            by ring_homo_sub
      = #0_                              by kernel_ideal_element

   Thus f (gen (#1 o I)) = #1_           by ring_sub_eq_zero
*)
val kernel_ideal_gen_id_map = store_thm(
  "kernel_ideal_gen_id_map",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in f (gen (#1 o I)) = #1_``,
  rw_tac std_ss[] >>
  `i << r` by rw[ring_homo_kernel_ideal, Abbr`i`] >>
  `#1 IN R /\ #1_ IN R_` by rw[] >>
  `#1 o I IN R/I` by rw[ideal_coset_property] >>
  `gen (#1 o I) IN R` by rw[ideal_cogen_property] >>
  `gen (#1 o I) - #1 IN I` by rw[ideal_coset_has_gen_diff] >>
  `f (gen (#1 o I)) IN R_` by metis_tac[ring_homo_element] >>
  `f (gen (#1 o I)) -_ #1_ = f (gen (#1 o I)) -_ f #1` by metis_tac[ring_homo_ids] >>
  `_ = f (gen (#1 o I) - #1)` by rw[ring_homo_sub] >>
  `_ = #0_` by metis_tac[kernel_ideal_element] >>
  metis_tac[ring_sub_eq_zero]);

(* Theorem: (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in
            !x y. x IN R/I /\ y IN R/I ==> ((gen x - gen y) IN I <=> (x = y)) *)
(* Proof:
   Let i = kernel_ideal f r r_.
   Note i << r                          by ring_homo_kernel_ideal, (r ~r~ s) f
    ==> gen x IN R /\ (gen x o I = x)   by ideal_cogen_property
    and gen y IN R /\ (gen y o I = y)   by ideal_cogen_property
   If part: (gen x - gen y) IN I ==> (x = y)
      By EXTENSION, this is to show:
      (1) z IN x ==> z IN y
          Note z IN (gen x) o I                by above
           ==> ?u. u IN I /\ (z = gen x + u)   by ideal_coset_element
            so u IN R                          by ideal_element_property
               z = gen x + u
                 = gen x + #0 + u                    by ring_add_rzero
                 = gen x + (-(gen y) + gen y) + u    by ring_add_lneg
                 = (gen x - gen y) + gen y + u       by ring_add_assoc
                 = gen y + (gen x - gen y) + u       by ring_add_comm
                 = gen y + ((gen x - gen y) + u)     by ring_add_assoc, ring_sub_element
           Now (gen x - gen y) + u IN I              by ideal_has_sum
          Thus z IN y                                by ideal_coset_element
      (2) z IN y ==> z IN x
          Note z IN (gen y) o I                by above
           ==> ?v. v IN I /\ (z = gen y + v)   by ideal_coset_element
            so v IN R                          by ideal_element_property
               z = gen x + u
                 = gen y + #0 + v                    by ring_add_rzero
                 = gen y + (-(gen x) + gen x) + v    by ring_add_lneg
                 = (gen y - gen x) + gen x + v       by ring_add_assoc
                 = gen x + (gen y - gen x) + v       by ring_add_comm
                 = gen x + ((gen y - gen x) + v)     by ring_add_assoc, ring_sub_element
                 = gen x + (-(gen x - gen y) + v)    by ring_neg_sub
           Now -(gen x - gen y) IN I                 by ideal_has_neg
            so -(gen x - gen y) + v IN I             by ideal_has_sum
           Thus z IN x                               by ideal_coset_element
   Only-if part: (x = y) ==> (gen x - gen y) IN I
      Note gen x - gen y = gen x - gen x       by x = y
                         = #0                  by ring_sub_eq_zero
       and #0 IN I                             by ideal_has_zero
*)
val kernel_ideal_quotient_element_eq = store_thm(
  "kernel_ideal_quotient_element_eq",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in
   !x y. x IN R/I /\ y IN R/I ==> ((gen x - gen y) IN I <=> (x = y))``,
  rw_tac std_ss[] >>
  `i << r` by rw[ring_homo_kernel_ideal, Abbr`i`] >>
  `gen x IN R /\ (gen x o I = x)` by rw[ideal_cogen_property] >>
  `gen y IN R /\ (gen y o I = y)` by rw[ideal_cogen_property] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    rw[EXTENSION, EQ_IMP_THM] >| [
      `?u. u IN I /\ (x' = gen x + u)` by rw[GSYM ideal_coset_element] >>
      `_ = gen x + #0 + u` by rw[] >>
      `_ = gen x + (-(gen y) + gen y) + u` by rw[] >>
      `_ = (gen x - gen y) + gen y + u` by rw[ring_add_assoc] >>
      `_ = gen y + (gen x - gen y) + u` by rw[ring_add_comm] >>
      `_ = gen y + ((gen x - gen y) + u)` by prove_tac[ring_add_assoc, ring_sub_element, ideal_element_property] >>
      metis_tac[ideal_coset_element, ideal_has_sum],
      `?v. v IN I /\ (x' = gen y + v)` by rw[GSYM ideal_coset_element] >>
      `_ = gen y + #0 + v` by rw[] >>
      `_ = gen y + (-(gen x) + gen x) + v` by rw[] >>
      `_ = (gen y - gen x) + gen x + v` by rw[ring_add_assoc] >>
      `_ = gen x + (gen y - gen x) + v` by rw[ring_add_comm] >>
      `_ = gen x + ((gen y - gen x) + v)` by prove_tac[ring_add_assoc, ring_sub_element, ideal_element_property] >>
      `_ = gen x + (-(gen x - gen y) + v)` by rw[ring_neg_sub] >>
      metis_tac[ideal_coset_element, ideal_has_sum, ideal_has_neg]
    ],
    `gen x - gen x = #0` by rw[] >>
    metis_tac[ideal_has_zero]
  ]);

(* Theorem: (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in INJ (f o gen) R/I (IMAGE f R) *)
(* Proof:
   Let i = kernel_ideal f r r_.
   Note i << r                         by ring_homo_kernel_ideal, (r ~r~ r_) f
   By INJ_DEF, this is to show:
   (1) x IN R/I ==> f (gen x) IN IMAGE f R
       Note gen x IN R                 by ideal_cogen_property
       Thus f (gen x) IN IMAGE f R     by IN_IMAGE
   (2) x IN R/I /\ y IN R/I /\ (f (gen x) = f (gen y)) ==> (x = y)
       Note gen x IN R /\ gen y IN R   by ideal_cogen_property
       Thus gen x - gen y IN R         by ring_sub_element
       also r.sum.carrier = R          by ring_carriers
       Note f (gen x) IN R_            by ring_homo_element
        and f (gen y) IN R_            by ring_homo_element
            f (gen x - gen y)
          = f (gen x) -_ f (gen y)     by ring_homo_sub
          = f (gen x) -_ f (gen x)     by f (gen x) = f (gen y)
          = #0_                        by ring_sub_eq_zero
       Thus (gen x - gen y) IN I       by kernel_ideal_element
        ==> x = y                      by kernel_ideal_quotient_element_eq
*)
val kernel_ideal_quotient_inj = store_thm(
  "kernel_ideal_quotient_inj",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
     let i = kernel_ideal f r r_ in INJ (f o gen) R/I (IMAGE f R)``,
  rw_tac std_ss[] >>
  `i << r` by rw[ring_homo_kernel_ideal, Abbr`i`] >>
  rw_tac std_ss[INJ_DEF] >-
  rw[ideal_cogen_property] >>
  `gen x IN R /\ gen y IN R` by rw[ideal_cogen_property] >>
  `gen x - gen y IN R /\ (r.sum.carrier = R)` by rw[] >>
  `f (gen x) IN R_ /\ f (gen y) IN R_` by metis_tac[ring_homo_element] >>
  `f (gen x - gen y) = #0_` by metis_tac[ring_homo_sub, ring_sub_eq_zero] >>
  `(gen x - gen y) IN I` by rw[kernel_ideal_element, Abbr`i`] >>
  metis_tac[kernel_ideal_quotient_element_eq]);

(* Theorem: (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in SURJ (f o gen) R/I (IMAGE f R) *)
(* Proof:
   Let i = kernel_ideal f r r_.
   Note i << r                         by ring_homo_kernel_ideal, (r ~r~ r_) f
   By SURJ_DEF, this is to show:
   (1) x IN R/I ==> f (gen x) IN IMAGE f R
       Note gen x IN R                 by ideal_cogen_property
       Thus f (gen x) IN IMAGE f R     by IN_IMAGE
   (2) x IN IMAGE f R ==> ?y. y IN R/I /\ (f (gen y) = x)
       Note ?z. (x = f z) /\ z IN R    by IN_IMAGE
       Thus z o I IN R/I               by ideal_coset_property
        ==> gen (z o I) IN R           by ideal_cogen_property
       Note gen (z o I) - z IN I       by ideal_coset_has_gen_diff, z IN R
        ==> #0_ = f (gen (z o I) - z)       by kernel_ideal_element
                = f (gen (z o I)) -_ f z    by ring_homo_sub
        ==> f (gen (z o I)) = f z           by ring_sub_eq_zero, ring_homo_element
       Take y = z o I, the result follows.
*)
val kernel_ideal_quotient_surj = store_thm(
  "kernel_ideal_quotient_surj",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
     let i = kernel_ideal f r r_ in SURJ (f o gen) R/I (IMAGE f R)``,
  rw_tac std_ss[] >>
  `i << r` by rw[ring_homo_kernel_ideal, Abbr`i`] >>
  rw_tac std_ss[SURJ_DEF] >-
  rw[ideal_cogen_property] >>
  `?z. (x = f z) /\ z IN R` by rw[GSYM IN_IMAGE] >>
  `z o I IN R/I` by rw[ideal_coset_property] >>
  `gen (z o I) IN R` by rw[ideal_cogen_property] >>
  `gen (z o I) - z IN I` by rw[ideal_coset_has_gen_diff] >>
  `#0_ = f (gen (z o I) - z)` by metis_tac[kernel_ideal_element] >>
  `_ = f (gen (z o I)) -_ f z` by rw[ring_homo_sub] >>
  prove_tac[ring_sub_eq_zero, ring_homo_element]);

(* Theorem: (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in BIJ (f o gen) R/I (IMAGE f R) *)
(* Proof:
   By BIJ_DEF, this is to show:
   (1) INJ (f o gen) R/I (IMAGE f R)
       This is true by kernel_ideal_quotient_inj
   (2) SURJ (f o gen) R/I (IMAGE f R)
       This is true by kernel_ideal_quotient_surj
*)
val kernel_ideal_quotient_bij = store_thm(
  "kernel_ideal_quotient_bij",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==>
    let i = kernel_ideal f r r_ in BIJ (f o gen) R/I (IMAGE f R)``,
  metis_tac[BIJ_DEF, kernel_ideal_quotient_inj, kernel_ideal_quotient_surj]);

(* Theorem: (r ~r~ s) f ==>
            let i = kernel_ideal f r s in RingHomo (f o gen) (r / i) (ring_homo_image f r s) *)
(* Proof:
   Let i = kernel_ideal f r s, r_ = ring_homo_image f r s.
   The goal is to show: RingHomo (f o gen) (r / i) r_
   Note Ring r_              by ring_homo_image_ring, by (r ~r~ s) f
    and i << r               by ring_homo_kernel_ideal, by (r ~r~ s) f
    ==> Ring (r / i)         by quotient_ring_ring, i << r

   Claim: !x. x IN (r / i).carrier ==> f (gen x) IN R_
   Proof: By quotient_ring_def, ring_homo_image_def, this is to show:
          !x. x IN R/I ==> ?z. (f (gen x) = f z) /\ z IN R
          Note x IN R/I ==> gen x IN R           by ideal_cogen_property
          Take z = gen x, the result is true.

   By RingHomo_def, this is to show:
   (1) x IN (r / i).carrier ==> f (gen x) IN R_, true by Claim.
   (2) GroupHomo (f o gen) (r / i).sum r_.sum
       By GroupHomo_def, ring_carriers, this is to show:
          x IN (r / i).carrier /\ y IN (r / i).carrier ==>
          f (gen ((r / i).sum.op x y)) = f (gen x) +_ f (gen y)
       By quotient_ring_def, quotient_ring_add_def, ring_homo_image_def, homo_image_def,
       the goal is:
           x IN R/I /\ y IN R/I ==> f (gen ((gen x + gen y) o I)) = s.sum.op (f (gen x)) (f (gen y))
       This is true by kernel_ideal_gen_add_map.
   (3) MonoidHomo (f o gen) (r / i).prod r_.prod
       By MonoidHomo_def, ring_carriers, this is to show:
       (1) x IN (r / i).carrier /\ y IN (r / i).carrier ==>
           f (gen ((r / i).prod.op x y)) = f (gen x) *_ f (gen y)
           By quotient_ring_def, quotient_ring_mult_def, ring_homo_image_def, homo_image_def,
           the goal is:
               x IN R/I /\ y IN R/I ==> f (gen ((gen x * gen y) o I)) = s.prod.op (f (gen x)) (f (gen y))
           This is true by kernel_ideal_gen_mult_map.
       (2) f (gen (r / i).prod.id) = #1_
           By quotient_ring_def, quotient_ring_mult_def, ring_homo_image_def, homo_image_def,
           the goal is: f (gen (#1 o I)) = s.prod.id
           This is true by kernel_ideal_gen_id_map.
*)
val kernel_ideal_quotient_homo = store_thm(
  "kernel_ideal_quotient_homo",
  ``!(r:'a ring) (s:'b ring) f. (r ~r~ s) f ==>
   let i = kernel_ideal f r s in RingHomo (f o gen) (r / i) (ring_homo_image f r s)``,
  rw_tac std_ss[] >>
  qabbrev_tac `r_ = ring_homo_image f r s` >>
  `Ring r_` by rw[ring_homo_image_ring, Abbr`r_`] >>
  `i << r` by rw[ring_homo_kernel_ideal, Abbr`i`] >>
  `Ring (r / i)` by rw[quotient_ring_ring] >>
  `!x. x IN (r / i).carrier ==> f (gen x) IN R_` by
  (fs[quotient_ring_def, ring_homo_image_def, Abbr`r_`] >>
  metis_tac[ideal_cogen_property]) >>
  rw_tac std_ss[RingHomo_def] >| [
    rw_tac std_ss[GroupHomo_def, ring_carriers] >>
    fs[quotient_ring_def, quotient_ring_add_def, ring_homo_image_def, homo_image_def, Abbr`r_`] >>
    metis_tac[kernel_ideal_gen_add_map],
    rw_tac std_ss[MonoidHomo_def, ring_carriers] >| [
      fs[quotient_ring_def, quotient_ring_mult_def, ring_homo_image_def, homo_image_def, Abbr`r_`] >>
      metis_tac[kernel_ideal_gen_mult_map],
      fs[quotient_ring_def, quotient_ring_mult_def, ring_homo_image_def, homo_image_def, Abbr`r_`] >>
      metis_tac[kernel_ideal_gen_id_map]
    ]
  ]);

(* Theorem: (r ~r~ s) f ==> let i = kernel_ideal f r s in
            RingIso (f o gen) (r / i) (ring_homo_image f r s) *)
(* Proof:
   By RingIso_def, this is to show:
   (1) RingHomo (f o gen) (r / i) (ring_homo_image f r s)
       This is true by kernel_ideal_quotient_homo
   (2) BIJ (f o gen) (r / i).carrier (ring_homo_image f r s).carrier
       Note (r / i).carrier = R/I                         by quotient_ring_def
        and (ring_homo_image f r s).carrier = IMAGE f R   by ring_homo_image_def
       Hence true by kernel_ideal_quotient_bij
*)
val kernel_ideal_quotient_iso = store_thm(
  "kernel_ideal_quotient_iso",
  ``!(r:'a ring) (s:'b ring) f. (r ~r~ s) f ==> let i = kernel_ideal f r s in
         RingIso (f o gen) (r / i) (ring_homo_image f r s)``,
  rw_tac std_ss[RingIso_def] >-
  metis_tac[kernel_ideal_quotient_homo] >>
  `(r / i).carrier = R/I` by rw[quotient_ring_def] >>
  `(ring_homo_image f r s).carrier = IMAGE f R` by rw[ring_homo_image_def] >>
  metis_tac[kernel_ideal_quotient_bij]);

(* Theorem: (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in
            (i << r) /\ (ring_homo_image f r r_ <= r_) /\
            RingIso (f o gen) (r / i) (ring_homo_image f r r_) *)
(* Proof:
   Let i = kernel_ideal f r r_.
   This is to show:
   (1) i << r, true by ring_homo_kernel_ideal
   (2) ring_homo_image f r r_ <= r_, true by ring_homo_image_subring
   (3) RingIso (f o gen) (r / i) (ring_homo_image f r r_)
       This is true by kernel_ideal_quotient_iso
*)
val ring_first_isomorphism_thm = store_thm(
  "ring_first_isomorphism_thm",
  ``!(r:'a ring) (r_:'b ring) f. (r ~r~ r_) f ==> let i = kernel_ideal f r r_ in
    (i << r) /\ (ring_homo_image f r r_ <= r_) /\ RingIso (f o gen) (r / i) (ring_homo_image f r r_)``,
  rw_tac std_ss[ring_homo_image_subring] >-
  rw_tac std_ss[ring_homo_kernel_ideal, Abbr`i`] >>
  metis_tac[kernel_ideal_quotient_iso]);

(* This is a significant milestone theorem! *)

(* ------------------------------------------------------------------------- *)
(* Ring Instances Documentation                                              *)
(* ------------------------------------------------------------------------- *)
(* Ring Data type:
   The generic symbol for ring data is r.
   r.carrier = Carrier set of Ring, overloaded as R.
   r.sum     = Addition component of Ring, binary operation overloaded as +.
   r.prod    = Multiplication component of Ring, binary operation overloaded as *.
*)
(* Overloading:
   ordz n m  = order (ZN n).prod m

*)
(* Definitions and Theorems (# are exported, ! in computeLib):

   The Trivial Ring (#1 = #0):
   trivial_ring_def       |- !z. trivial_ring z =
                                 <|carrier := {z};
                                       sum := <|carrier := {z}; id := z; op := (\x y. z)|>;
                                      prod := <|carrier := {z}; id := z; op := (\x y. z)|>
                                  |>
   trivial_ring           |- !z. FiniteRing (trivial_ring z)
   trivial_char           |- !z. char (trivial_ring z) = 1

   Arithmetic Modulo n:
   ZN_def                 |- !n. ZN n = <|carrier := count n; sum := add_mod n; prod := times_mod n|>
!  ZN_eval                |- !n. ((ZN n).carrier = count n) /\
                                 ((ZN n).sum = add_mod n) /\ ((ZN n).prod = times_mod n)
   ZN_property            |- !n. (!x. x IN (ZN n).carrier <=> x < n) /\ ((ZN n).sum.id = 0) /\
                                 ((ZN n).prod.id = if n = 1 then 0 else 1) /\
                                 (!x y. (ZN n).sum.op x y = (x + y) MOD n) /\
                                 (!x y. (ZN n).rr.op x y = (x * y) MOD n) /\
                                 FINITE (ZN n).carrier /\ (CARD (ZN n).carrier = n)
   ZN_ids                 |- !n. 0 < n ==> ((ZN n).sum.id = 0) /\ ((ZN n).prod.id = 1 MOD n)
   ZN_ids_alt             |- !n. 1 < n ==> ((ZN n).sum.id = 0) /\ ((ZN n).prod.id = 1)
   ZN_finite              |- !n. FINITE (ZN n).carrier
   ZN_card                |- !n. CARD (ZN n).carrier = n
   ZN_ring                |- !n. 0 < n ==> Ring (ZN n)
   ZN_char                |- !n. 0 < n ==> (char (ZN n) = n)
   ZN_exp                 |- !n. 0 < n ==> !x k. (ZN n).prod.exp x k = x ** k MOD n
   ZN_num                 |- !n. 0 < n ==> !k. (ZN n).sum.exp 1 k = k MOD n
   ZN_num_1               |- !n. (ZN n).sum.exp (ZN n).prod.id 1 = 1 MOD n
   ZN_num_0               |- !n c. 0 < n ==> (ZN n).sum.exp 0 c = 0
   ZN_num_mod             |- !n c. 0 < n ==> (ZN n).sum.exp (ZN n).prod.id c = c MOD n
   ZN_finite_ring         |- !n. 0 < n ==> FiniteRing (ZN n)
   ZN_invertibles_group   |- !n. 0 < n ==> Group (Invertibles (ZN n).prod)
   ZN_invertibles_finite_group   |- !n. 0 < n ==> FiniteGroup (Invertibles (ZN n).prod)

   ZN Inverse:
   ZN_mult_inv_coprime      |- !n. 0 < n ==> !x y. ((x * y) MOD n = 1) ==> coprime x n
   ZN_mult_inv_coprime_iff  |- !n. 1 < n ==> !x. coprime x n <=> ?y. (x * y) MOD n = 1
   ZN_coprime_invertible    |- !m n. 1 < m /\ coprime m n ==> n MOD m IN (Invertibles (ZN m).prod).carrier
   ZN_invertibles           |- !n. 1 < n ==> (Invertibles (ZN n).prod = Estar n)

   ZN Order:
   ZN_1_exp               |- !n k. (ZN 1).prod.exp n k = 0
   ZN_order_mod_1         |- !n. ordz 1 n = 1
   ZN_order_mod           |- !m n. 0 < m ==> (ordz m (n MOD m) = ordz m n)
   ZN_invertibles_order   |- !m n. 0 < m ==> (order (Invertibles (ZN m).prod) (n MOD m) = ordz m n)
   ZN_order_0             |- !n. 0 < n ==> (ordz n 0 = if n = 1 then 1 else 0)
   ZN_order_1             |- !n. 0 < n ==> (ordz n 1 = 1)
   ZN_order_eq_1          |- !m n. 0 < m ==> ((ordz m n = 1) <=> (n MOD m = 1 MOD m))
   ZN_order_eq_1_alt      |- !m n. 1 < m ==> (ordz m n = 1 <=> n MOD m = 1)
   ZN_order_property      |- !m n. 0 < m ==> (n ** ordz m n MOD m = 1 MOD m)
   ZN_order_property_alt  |- !m n. 1 < m ==> (n ** ordz m n MOD m = 1)
   ZN_order_divisibility  |- !m n. 0 < m ==> m divides n ** ordz m n - 1
   ZN_coprime_euler_element         |- !m n. 1 < m /\ coprime m n ==> n MOD m IN Euler m
   ZN_coprime_order                 |- !m n. 0 < m /\ coprime m n ==> 0 < ordz m n /\ (n ** ordz m n MOD m = 1 MOD m)
   ZN_coprime_order_alt             |- !m n. 1 < m /\ coprime m n ==> 0 < ordz m n /\ (n ** ordz m n MOD m = 1)
   ZN_coprime_order_divides_totient |- !m n. 0 < m /\ coprime m n ==> ordz m n divides totient m
   ZN_coprime_order_divides_phi     |- !m n. 0 < m /\ coprime m n ==> ordz m n divides phi m
   ZN_coprime_order_lt              |- !m n. 1 < m /\ coprime m n ==> ordz m n < m
   ZN_coprime_exp_mod               |- !m n. 0 < m /\ coprime m n ==> !k. n ** k MOD m = n ** (k MOD ordz m n) MOD m
   ZN_order_eq_1_by_prime_factors   |- !m n. 0 < m /\ coprime m n /\
                                       (!p. prime p /\ p divides n ==> (ordz m p = 1)) ==> (ordz m n = 1)
   ZN_order_nonzero_iff   |- !m n. 1 < m ==> (ordz m n <> 0 <=> ?k. 0 < k /\ (n ** k MOD m = 1))
   ZN_order_eq_0_iff      |- !m n. 1 < m ==> (ordz m n = 0 <=> !k. 0 < k ==> n ** k MOD m <> 1)
   ZN_order_nonzero       |- !m n. 0 < m ==> (ordz m n <> 0 <=> coprime m n)
   ZN_order_eq_0          |- !m n. 0 < m ==> ((ordz m n = 0) <=> gcd m n <> 1)
   ZN_not_coprime         |- !m n. 0 < m /\ gcd m n <> 1 ==> !k. 0 < k ==> n ** k MOD m <> 1
   ZN_order_gt_1_property |- !m n. 0 < m /\ 1 < ordz m n ==> ?p. prime p /\ p divides n /\ 1 < ordz m p
   ZN_order_divides_exp   |- !m n k. 1 < m /\ 0 < k ==> ((n ** k MOD m = 1) <=> ordz m n divides k)
   ZN_order_divides_phi   |- !m n. 0 < m /\ 0 < ordz m n ==> ordz m n divides phi m
   ZN_order_upper         |- !m n. 0 < m ==> ordz m n <= phi m
   ZN_order_le            |- !m n. 0 < m ==> ordz m n <= m
   ZN_order_lt            |- !k n m. 0 < k /\ k < m ==> ordz k n < m
   ZN_order_minimal       |- !m n k. 0 < m /\ 0 < k /\ k < ordz m n ==> n ** k MOD m <> 1
   ZN_coprime_order_gt_1  |- !m n. 1 < m /\ 1 < n MOD m /\ coprime m n ==> 1 < ordz m
   ZN_order_with_coprime_1|- !m n. 1 < n /\ coprime m n /\ 1 < ordz m n ==> 1 < m
   ZN_order_with_coprime_2|- !m n k. 1 < m /\ m divides n /\ 1 < ordz k m /\ coprime k n ==>
                                     1 < n /\ 1 < k
   ZN_order_eq_0_test     |- !m n. 1 < m ==>
                             ((ordz m n = 0) <=> !j. 0 < j /\ j < m ==> n ** j MOD m <> 1)
   ZN_order_divides_tops_index
                          |- !n j k. 1 < n /\ 0 < j /\ 1 < k ==>
                                     (k divides tops n j <=> ordz k n divides j)
   ZN_order_le_tops_index |- !n j k. 1 < n /\ 0 < j /\ 1 < k /\ k divides tops n j ==>
                                     ordz k n <= j

   ZN Order Candidate:
   ZN_order_test_propery  |- !m n k. 1 < m /\ 0 < k /\ (n ** k MOD m = 1) /\
                            (!j. 0 < j /\ j < k /\ j divides phi m ==> n ** j MOD m <> 1) ==>
                             !j. 0 < j /\ j < k /\ ~(j divides phi m) ==>
                                 (ordz m n = k) \/ n ** j MOD m <> 1
   ZN_order_test_1        |- !m n k. 1 < m /\ 0 < k ==> ((ordz m n = k) <=>
                              (n ** k MOD m = 1) /\ !j. 0 < j /\ j < k ==> n ** j MOD m <> 1)
   ZN_order_test_2        |- !m n k. 1 < m /\ 0 < k ==> ((ordz m n = k) <=>
                              (n ** k MOD m = 1) /\
                              !j. 0 < j /\ j < k /\ j divides phi m ==> n ** j MOD m <> 1)
   ZN_order_test_3        |- !m n k. 1 < m /\ 0 < k ==> ((ordz m n = k) <=>
                              k divides phi m /\ (n ** k MOD m = 1) /\
                              !j. 0 < j /\ j < k /\ j divides phi m ==> n ** j MOD m <> 1)
   ZN_order_test_4        |- !m n k. 1 < m ==> ((ordz m n = k) <=> (n ** k MOD m = 1) /\
                             !j. 0 < j /\ j < (if k = 0 then m else k) ==> n ** j MOD m <> 1)

   ZN Homomorphism:
   ZN_to_ZN_element          |- !n m x. 0 < m /\ x IN (ZN n).carrier ==> x MOD m IN (ZN m).carrier
   ZN_to_ZN_sum_group_homo   |- !n m. 0 < n /\ m divides n ==>
                                      GroupHomo (\x. x MOD m) (ZN n).sum (ZN m).sum
   ZN_to_ZN_prod_monoid_homo |- !n m. 0 < n /\ m divides n ==>
                                      MonoidHomo (\x. x MOD m) (ZN n).prod (ZN m).prod
   ZN_to_ZN_ring_homo        |- !n m. 0 < n /\ m divides n ==>
                                      RingHomo (\x. x MOD m) (ZN n) (ZN m)

   Ring from Sets:
   symdiff_set_inter_def  |- symdiff_set_inter =
                             <|carrier := univ(:'a -> bool); sum := symdiff_set; prod := set_inter|>
   symdiff_set_inter_ring |- Ring symdiff_set_inter
   symdiff_set_inter_char |- char symdiff_set_inter = 2
!  symdiff_eval           |- (symdiff_set.carrier = univ(:'a -> bool)) /\
                             (!x y. symdiff_set.op x y = x UNION y DIFF x INTER y) /\
                             (symdiff_set.id = {})

   Order Computation using a WHILE loop:
   compute_ordz_def      |- !m n. compute_ordz m n =
                                       if m = 0 then ordz 0 n
                                  else if m = 1 then 1
                                  else if coprime m n then WHILE (\i. (n ** i) MOD m <> 1) SUC 1
                                  else 0
   WHILE_RULE_PRE_POST   |- (!x. Invariant x /\ Guard x ==> f (Cmd x) < f x) /\
                            (!x. Precond x ==> Invariant x) /\
                            (!x. Invariant x /\ ~Guard x ==> Postcond x) /\
                            HOARE_SPEC (\x. Invariant x /\ Guard x) Cmd Invariant ==>
                            HOARE_SPEC Precond (WHILE Guard Cmd) Postcond
   compute_ordz_hoare    |- !m n. 1 < m /\ coprime m n ==>
                                  HOARE_SPEC (\i. 0 < i /\ i <= ordz m n)
                                             (WHILE (\i. (n ** i) MOD m <> 1) SUC)
                                             (\i. i = ordz m n)
   compute_ordz_by_while |- !m n. 1 < m /\ coprime m n ==> !j. 0 < j /\ j <= ordz m n ==>
                                  (WHILE (\i. (n ** i) MOD m <> 1) SUC j = ordz m n)

   Correctness of computing ordz m n:
   compute_ordz_0      |- !n. compute_ordz 0 n = ordz 0
   compute_ordz_1      |- !n. compute_ordz 1 n = 1
   compute_ordz_eqn    |- !m n. compute_ordz m n = ordz m n
!  ordz_eval           |- !m n. order (times_mod m) n = compute_ordz m n

*)
(* ------------------------------------------------------------------------- *)
(* The Trivial Ring = {|0|}.                                                 *)
(* ------------------------------------------------------------------------- *)

val trivial_ring_def = Define`
  (trivial_ring z) : 'a ring =
   <| carrier := {z};
      sum := <| carrier := {z};
                id := z;
                op := (\x y. z) |>;
      prod := <| carrier := {z};
                id := z;
                op := (\x y. z) |>
    |>
`;

(* Theorem: {|0|} is indeed a ring. *)
(* Proof: by definition, the field tables are:

   +    |0|          *  |0|
   ------------     -----------
   |0|  |0|         |0| |0|
*)
val trivial_ring = store_thm(
  "trivial_ring",
  ``!z. FiniteRing (trivial_ring z)``,
  rw_tac std_ss[FiniteRing_def] >| [
    rw_tac std_ss[trivial_ring_def, Ring_def, AbelianGroup_def, group_def_alt, IN_SING, RES_FORALL_THM, RES_EXISTS_THM] >>
    rw_tac std_ss[AbelianMonoid_def, Monoid_def, IN_SING],
    rw_tac std_ss[trivial_ring_def, FINITE_SING]
  ]);

(* |- !z. Ring (trivial_ring z), added for ringLibTheory by Chun Tian *)
Theorem trivial_ring_thm =
        trivial_ring |> REWRITE_RULE [FiniteRing_def] |> cj 1

(* Theorem: char (trivial_ring z) = 1 *)
(* Proof:
   By fiddling with properties of OLEAST.
   This is to show:
   (case OLEAST n. 0 < n /\ (FUNPOW (\y. z) n z = z) of NONE => 0 | SOME n => n) = 1
   If NONE, 0 = 1 is impossible, so SOME must be true, i.e. to show:
   ?n. 0 < n /\ (FUNPOW (\y. z) n z = z), and then that n must be 1.
   First part is simple:
   let n = 1, then FUNPOW (\y. z) 1 z = (\y. z) z = z   by FUNPOW
   Second part is to show:
   0 < n /\ (FUNPOW (\y. z) n z = z) /\ !m. m < n ==> ~(0 < m) \/ FUNPOW (\y. z) m z <> z ==> n = 1
   By contradiction, assume n <> 1,
   then 0 < n /\ n <> 1 ==> 1 < n,
   since 0 < 1, this means FUNPOW (\y. z) 1 z <> z,
   but FUNPOW (\y. z) 1 z = z by FUNPOW, hence a contradiction.
*)
Theorem trivial_char:
  !z. char (trivial_ring z) = 1
Proof
  strip_tac >>
  `FiniteRing (trivial_ring z)` by rw_tac std_ss[trivial_ring] >>
  rw[char_def] >>
  rw_tac std_ss[order_def, period_def, trivial_ring_def, monoid_exp_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  rw_tac std_ss[] >>
  spose_not_then strip_assume_tac >>
  `1 < n /\ 0 < 1` by decide_tac >>
  `FUNPOW (\y. z) 1 z <> z` by metis_tac[DECIDE “~(0 < 0)”] >>
  full_simp_tac (srw_ss()) []
QED

(* ------------------------------------------------------------------------- *)
(* Z_n, Arithmetic in Modulo n.                                              *)
(* ------------------------------------------------------------------------- *)

(* Integer Modulo Ring *)
val ZN_def = zDefine`
  ZN n : num ring =
    <| carrier := count n;
           sum := add_mod n;
          prod := times_mod n
     |>
`;
(*
Note: add_mod is defined in groupInstancesTheory.
times_mod is defined in monoidInstancesTheory.
*)
(* Use of zDefine to avoid incorporating into computeLib, by default. *)

(*
- type_of ``ZN n``;
> val it = ``:num ring`` : hol_type
*)

(* Theorem: Evaluation of ZN component fields. *)
(* Proof: by ZN_def *)
val ZN_eval = store_thm(
  "ZN_eval[compute]",
  ``!n. ((ZN n).carrier = count n) /\
       ((ZN n).sum = add_mod n) /\
       ((ZN n).prod = times_mod n)``,
  rw_tac std_ss[ZN_def]);
(* Put into computeLib, and later with ordz_eval for order computation. *)

(* Theorem: property of ZN Ring *)
(* Proof: by ZN_def, add_mod_def, times_mod_def. *)
val ZN_property = store_thm(
  "ZN_property",
  ``!n. (!x. x IN (ZN n).carrier <=> x < n) /\
       ((ZN n).sum.id = 0) /\
       ((ZN n).prod.id = if n = 1 then 0 else 1) /\
       (!x y. (ZN n).sum.op x y = (x + y) MOD n) /\
       (!x y. (ZN n).prod.op x y = (x * y) MOD n) /\
       FINITE (ZN n).carrier /\
       (CARD (ZN n).carrier = n)``,
  rw[ZN_def, add_mod_def, times_mod_def]);

(* Theorem: 0 < n ==> ((ZN n).sum.id = 0) /\ ((ZN n).prod.id = 1 MOD n) *)
(* Proof: by ZN_property *)
val ZN_ids = store_thm(
  "ZN_ids",
  ``!n. 0 < n ==> ((ZN n).sum.id = 0) /\ ((ZN n).prod.id = 1 MOD n)``,
  rw[ZN_property]);

(* Theorem: 1 < n ==> ((ZN n).sum.id = 0) /\ ((ZN n).prod.id = 1) *)
(* Proof: by ZN_ids, ONE_MOD *)
val ZN_ids_alt = store_thm(
  "ZN_ids_alt",
  ``!n. 1 < n ==> ((ZN n).sum.id = 0) /\ ((ZN n).prod.id = 1)``,
  rw[ZN_ids]);

(* Theorem: (ZN n).carrier is FINITE. *)
(* Proof: by ZN_ring and FINITE_COUNT. *)
val ZN_finite = store_thm(
  "ZN_finite",
  ``!n. FINITE (ZN n).carrier``,
  rw[ZN_def]);

(* Theorem: CARD (ZN n).carrier = n *)
(* Proof: by ZN_property. *)
val ZN_card = store_thm(
  "ZN_card",
  ``!n. CARD (ZN n).carrier = n``,
  rw[ZN_property]);

(* Theorem: For n > 0, (ZN n) is a Ring. *)
(* Proof: by checking definitions.
   For distribution: (x * (y + z) MOD n) MOD n = ((x * y) MOD n + (x * z) MOD n) MOD n
   LHS = (x * (y + z) MOD n) MOD n
       = (x MOD n * ((y + z) MOD n) MOD n        by LESS_MOD
       = (x * (y + z)) MOD n                     by MOD_TIMES2
       = (x * y + x * z) MOD n                   by LEFT_ADD_DISTRIB
       = ((x * y) MOD n + (x + y) MOD n) MOD n   by MOD_PLUS
       = RHS
*)
val ZN_ring = store_thm(
  "ZN_ring",
  ``!n. 0 < n ==> Ring (ZN n)``,
  rpt strip_tac >>
  `!x. x IN count n <=> x < n` by rw[] >>
  rw_tac std_ss[ZN_def, Ring_def] >-
  rw_tac std_ss[add_mod_abelian_group] >-
  rw_tac std_ss[times_mod_abelian_monoid] >-
  rw_tac std_ss[add_mod_def, count_def] >-
  rw_tac std_ss[times_mod_def] >>
  rw_tac std_ss[add_mod_def, times_mod_def] >>
  metis_tac[LEFT_ADD_DISTRIB, MOD_PLUS, MOD_TIMES2, LESS_MOD]);

(* Theorem: !m n. 0 < n /\ m <= n ==> (FUNPOW (\j. (j + 1) MOD n) m 0 = m MOD n) *)
(* Proof: by induction on m.
   Base case: !n. 0 < n /\ 0 <= n ==> (FUNPOW (\j. (j + 1) MOD n) 0 0 = 0 MOD n)
   By FUNPOW, !f x. FUNPOW f 0 x = x,
   hence this is true by 0 = 0 MOD n.
   Step case: !n. 0 < n /\ m <= n ==> (FUNPOW (\j. (j + 1) MOD n) m 0 = m MOD n) ==>
              !n. 0 < n /\ SUC m <= n ==> (FUNPOW (\j. (j + 1) MOD n) (SUC m) 0 = SUC m MOD n)
   By FUNPOW_SUC, !f n x. FUNPOW f (SUC n) x = f (FUNPOW f n x)
   hence  (FUNPOW (\j. (j + 1) MOD n) (SUC n) 0
         = (\j. (j + 1) MOD n) (FUNPOW (\j. (j + 1) MOD n) n  0)   by FUNPOW_SUC
         = (\j. (j + 1) MOD n) (m MOD n)                           by induction hypothesis
         = ((m MOD n) + 1) MOD n
         = (m + 1) MOD n    since m < n
         = SUC m MOD n      by ADD1
*)
val ZN_lemma1 = prove(
  ``!m n. 0 < n /\ m <= n ==> (FUNPOW (\j. (j + 1) MOD n) m 0 = m MOD n)``,
  Induct_on `m`  >-
  srw_tac[ARITH_ss][] >>
  srw_tac[ARITH_ss][FUNPOW_SUC, ADD1]);

(* Theorem: 0 < n ==> FUNPOW (\j. (j + 1) MOD n) n 0 = 0 *)
(* Proof:
   Put m = n in ZN_lemma1:
   FUNPOW (\j. (j + 1) MOD n) n 0 = n MOD n = 0  by DIVMOD_ID.
*)
val ZN_lemma2 = prove(
  ``!n. 0 < n ==> (FUNPOW (\j. (j + 1) MOD n) n 0 = 0)``,
  rw_tac std_ss[ZN_lemma1]);

(* Theorem: 0 < n ==> char (ZN n) = n *)
(* Proof:
   Depends on the "ZN_lemma":
    0 < m /\ n <= m ==> FUNPOW (\j. (j + 1) MOD m) n 0 = n MOD m
   which is proved by induction on n.
   This is to show:
   (case OLEAST n'. 0 < n' /\ (FUNPOW (\j. (1 + j) MOD n) n' 0 = 0) of NONE => 0 | SOME n => n) = n
   If SOME, n = n is trivial.
   If NONE, need to show impossible for 0 < n: 0 < n' /\ (FUNPOW (\j. (1 + j) MOD n) n' 0 = 0
   Since (FUNPOW (\j. (1 + j) MOD n) n' 0 = n MOD n' = 0  by by ZN_lemma1
   and 0 < n' /\ 0 < n ==> n MOD n' <> 0, a contradiction with n MOD n' = 0.
*)
Theorem ZN_char:
  !n. 0 < n ==> char (ZN n) = n
Proof
  rw_tac std_ss[char_def, order_def, period_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  simp[Excl "lift_disj_eq", ZN_def, add_mod_def, times_mod_def,
       monoid_exp_def] >>
  rw[Excl "lift_disj_eq"] >| [ (* avoid srw_tac simplication *)
    qexists_tac `1` >> rw[],
    metis_tac[ZN_lemma2, DECIDE “~(0 < 0)”],
    rename [‘0 < m’] >> spose_not_then strip_assume_tac >>
    `1 < m` by decide_tac >>
    `FUNPOW (\j. 0) 1 0 = 0` by rw[] >>
    metis_tac[DECIDE “1 <> 0”],

    rename [‘m = n’, ‘n <> 1’] >>
    ‘FUNPOW (\j. (j + 1) MOD n) n 0 = 0’ by rw_tac std_ss[ZN_lemma2] >>
    ‘~(n < m)’ by metis_tac[DECIDE “~(0 < 0)”] >>
    ‘~(m < n)’ suffices_by decide_tac >>
    strip_tac >>
    full_simp_tac (srw_ss() ++ ARITH_ss) [ZN_lemma1]
  ]
QED

(* Better proof *)

(* Theorem: 0 < n ==> char (ZN n) = n *)
(* Proof:
   If n = 1, (ZN 1).carrier = count 1 = {0}
   this is to show: n = 1 iff (FUNPOW (\j. 0) n 0 = 0) /\ !m. 0 < m /\ m < n ==> FUNPOW (\j. 0) m 0 <> 0
   which is true, since FUNPOW (\j. 0) m 0 = 0 for all m, so to falsify 0 < m /\ m < n, n must be 1.
   If n <> 1, 1 < n,
   Ring (ZN n)    by ZN_ring
     (ZN n).sum.exp 1 n
   = FUNPOW (\j. (1 + j) MOD n) n 0   by monoid_exp_def
   = n MOD n = 0                      by ZN_lemma2
   Hence (ZN n).sum.exp 1 n = 0
   meaning  char (ZN n) n divides     by ring_char_divides
   Let m = char (ZN n),
   then m <= n                        by DIVIDES_LE
     (ZN n).sum.exp 1 m
   = FUNPOW (\j. (1 + j) MOD n) m 0   by monoid_exp_def
   = m MOD n                          by ZN_lemma1
   = 0                                by char_property
   But m MOD n = 0 means n divides m  by DIVIDES_MOD_0
   Therefore m = n                    by DIVIDES_ANTISYM
*)
Theorem ZN_char[allow_rebind]:
  !n. 0 < n ==> (char (ZN n) = n)
Proof
  rpt strip_tac >>
  ‘Ring (ZN n)’ by rw_tac std_ss [ZN_ring] >>
  ‘(ZN n).sum.id = 0’ by rw[ZN_def, add_mod_def] >>
  ‘(ZN n).sum.exp 1 n = 0’ by rw[ZN_lemma2, ZN_def, add_mod_def, times_mod_def, monoid_exp_def, ADD_COMM] >>
  Cases_on ‘n = 1’ >| [
    ‘(ZN n).prod.id = 0’ by rw[ZN_def, times_mod_def] >>
    ‘(char (ZN n)) divides n’ by rw[GSYM ring_char_divides] >>
    metis_tac[DIVIDES_ONE],
    ‘(ZN n).prod.id = 1’ by rw[ZN_def, times_mod_def] >>
    ‘(ZN n).sum.exp 1 n = 0’ by rw[ZN_lemma2, ZN_def, add_mod_def, times_mod_def, monoid_exp_def, ADD_COMM] >>
    ‘(char (ZN n)) divides n’ by rw[GSYM ring_char_divides] >>
    ‘(char (ZN n)) <= n’ by rw[DIVIDES_LE] >>
    qabbrev_tac ‘m = char (ZN n)’ >>
    ‘(ZN n).sum.exp 1 m = FUNPOW (\j. (j + 1) MOD n) m 0’ by rw[ZN_def, add_mod_def, times_mod_def, monoid_exp_def, ADD_COMM] >>
    ‘_ = m MOD n’ by rw[ZN_lemma1] >>
    ‘n divides m’ by metis_tac[char_property, DIVIDES_MOD_0] >>
    metis_tac [DIVIDES_ANTISYM]
  ]
QED

(* Theorem: 0 < n ==> !x k. (ZN n).prod.exp x k = (x ** k) MOD n *)
(* Proof:
     (ZN n).prod.exp x k
   = (times_mod n).exp x k     by ZN_def
   = (x MOD n) ** k MOD n      by times_mod_exp, 0 < n
   = (x ** k) MOD n            by EXP_MOD, 0 < n
*)
val ZN_exp = store_thm(
  "ZN_exp",
  ``!n. 0 < n ==> !x k. (ZN n).prod.exp x k = (x ** k) MOD n``,
  rw[ZN_def, times_mod_exp]);

(* Theorem: 0 < n ==> !k. (ZN n).sum.exp 1 k = k MOD n *)
(* Proof:
     (ZN n).sum.exp 1 k
   = (add_mod n).exp 1 k   by ZN_def
   = (1 * k) MOD n         by add_mod_exp, 0 < n
   = k MOD n               by MULT_LEFT_1
*)
val ZN_num = store_thm(
  "ZN_num",
  ``!n. 0 < n ==> !k. (ZN n).sum.exp 1 k = k MOD n``,
  rw[ZN_def, add_mod_exp]);

(* Theorem: (ZN n).sum.exp (ZN n).prod.id 1 = 1 MOD n *)
(* Proof:
   If n = 0,
        (ZN 0).sum.exp (ZN 0).prod.id 1
      = (ZN 0).sum.exp 1 1              by ZN_property, n <> 1
      = (ZN 0).sum 0 1                  by monoid_exp_def
      = 1 MOD 0                         by ZN_property
   If n = 1.
        (ZN 1).sum.exp (ZN 1).prod.id 1
      = (ZN 1).sum.exp 0 1              by ZN_property, n = 1
      = (ZN 1).sum 0 0                  by monoid_exp_def
      = 0 MOD 1 = 0                     by ZN_property
                = 1 MOD 1               by DIVMOD_ID, n <> 0
   Otherwise, 1 < n.
        (ZN n).sum.exp (ZN n).prod.id 1
      = (ZN n).sum.exp 1 1              by ZN_property, n <> 1
      = 1 MOD n                         by ZN_num, 0 < n
*)
val ZN_num_1 = store_thm(
  "ZN_num_1",
  ``!n. (ZN n).sum.exp (ZN n).prod.id 1 = 1 MOD n``,
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    `(ZN 0).sum.exp (ZN 0).prod.id 1 = 1 MOD 0` by EVAL_TAC >>
    rw[],
    rw[ZN_num, ZN_property] >>
    EVAL_TAC
  ]);

(* Theorem: 0 < n ==> ((ZN n).sum.exp 0 c = 0) *)
(* Proof:
   By induction on c.
   Base: (ZN n).sum.exp 0 0 = 0
         (ZN n).sum.exp 0 0
       = (ZN n).sum.id          by monoid_exp_0
       = 0                      by ZN_property
   Step: (ZN n).sum.exp 0 c = 0 ==> (ZN n).sum.exp 0 (SUC c) = 0
         (ZN n).sum.exp 0 (SUC c)
       = (ZN n).sum.op 0 ((ZN n).sum.exp 0 c)
                                by monoid_exp_SUC
       = (ZN n).sum.op 0 0      by induction hypothesis
       = (ZN n).sum.id          by monoid_exp_0
       = 0                      by ZN_property
*)
val ZN_num_0 = store_thm(
  "ZN_num_0",
  ``!n c. 0 < n ==> ((ZN n).sum.exp 0 c = 0)``,
  strip_tac >>
  Induct >-
  rw[ZN_property] >>
  rw[ZN_property, monoid_exp_def]);

(* Theorem: 0 < n ==> ((ZN n).sum.exp (ZN n).prod.id c = c MOD n) *)
(* Proof:
   If n = 1,
        (ZN 1).sum.exp (ZN 1).prod.id c
      = (ZN 1).sum.exp 0 c            by ZN_property, n = 1
      = 0                             by ZN_num_0
      = c MOD 1                       by MOD_1
   If n <> 1,
        (ZN n).sum.exp (ZN n).prod.id c
      = (ZN n).sum.exp 1 c            by ZN_property, n <> 1
      = c MOD n                       by ZN_num, 0 < n.
*)
val ZN_num_mod = store_thm(
  "ZN_num_mod",
  ``!n c. 0 < n ==> ((ZN n).sum.exp (ZN n).prod.id c = c MOD n)``,
  rpt strip_tac >>
  rw[ZN_num, ZN_property] >>
  rw[ZN_num_0]);

(* Theorem: For n > 0, (ZN n) is a FINITE Ring. *)
(* Proof: by ZN_ring and ZN_finite. *)
val ZN_finite_ring = store_thm(
  "ZN_finite_ring",
  ``!n. 0 < n ==> FiniteRing (ZN n)``,
  rw_tac std_ss[ZN_ring, ZN_finite, FiniteRing_def]);

(* Theorem: FiniteGroup (Invertibles (ZN n).prod) *)
(* Proof:
   Note Ring (ZN n)                                by ZN_ring
     so Monoid (ZN n).prod                         by ring_mult_monoid
   Thus Group (Invertibles (ZN n).prod)            by monoid_invertibles_is_group
*)
val ZN_invertibles_group = store_thm(
  "ZN_invertibles_group",
  ``!n. 0 < n ==> Group (Invertibles (ZN n).prod)``,
  rw[ZN_ring, monoid_invertibles_is_group]);

(* Theorem: FiniteGroup (Invertibles (ZN n).prod) *)
(* Proof:
   By FiniteGroup_def, this is to show:
   (1) Group (Invertibles (ZN n).prod), true            by ZN_invertibles_group
   (2) FINITE (Invertibles (ZN n).prod).carrier
       Note Ring (ZN n)                                 by ZN_ring
       Since FINITE (ZN n).carrier                      by ZN_finite
       Hence FINITE (Invertibles (ZN n).prod).carrier   by Invertibles_subset, SUBSET_FINITE
*)
val ZN_invertibles_finite_group = store_thm(
  "ZN_invertibles_finite_group",
  ``!n. 0 < n ==> FiniteGroup (Invertibles (ZN n).prod)``,
  rw[FiniteGroup_def] >-
  rw[ZN_invertibles_group] >>
  metis_tac[ZN_finite, Invertibles_subset, SUBSET_FINITE, ZN_ring, ring_carriers]);

(* ------------------------------------------------------------------------- *)
(* ZN Inverse                                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < n ==> !x y. ((x * y) MOD n = 1) ==> coprime x n *)
(* Proof:
       (x * y) MOD n = 1
   ==> ?k. x * y = k * n + 1             by MOD_EQN
   Let d = gcd x n,
   Since d divides x                     by GCD_IS_GREATEST_COMMON_DIVISOR
      so d divides x * y                 by DIVIDES_MULT
    Also d divides n                     by GCD_IS_GREATEST_COMMON_DIVISOR
      so d divides k * n                 by DIVIDES_MULTIPLE
    Thus d divides gcd (k * n) (x * y)   by GCD_IS_GREATEST_COMMON_DIVISOR
     But gcd (k * n) (x * y)
       = gcd (k * n) (k * n + 1)         by above
       = 1                               by coprime_SUC
      so d divides 1, or d = 1           by DIVIDES_ONE
*)
val ZN_mult_inv_coprime = store_thm(
  "ZN_mult_inv_coprime",
  ``!n. 0 < n ==> !x y. ((x * y) MOD n = 1) ==> coprime x n``,
  rpt strip_tac >>
  `?k. x * y = k * n + 1` by metis_tac[MOD_EQN] >>
  qabbrev_tac `d = gcd x n` >>
  `d divides x * y` by rw[DIVIDES_MULT, GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `d divides k * n` by rw[DIVIDES_MULTIPLE, GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `d divides gcd (k * n) (x * y)` by rw[GCD_IS_GREATEST_COMMON_DIVISOR] >>
  metis_tac[coprime_SUC, DIVIDES_ONE]);

(* Theorem: 1 < n ==> !x. coprime x n <=> ?y. (x * y) MOD n = 1 *)
(* Proof:
   If part: coprime x n ==> ?y. (x * y) MOD n = 1
      This is true           by GCD_ONE_PROPERTY
   Only-if part: (x * y) MOD n = 1 ==> coprime x n
      This is true           by ZN_mult_inv_coprime, 0 < n
*)
val ZN_mult_inv_coprime_iff = store_thm(
  "ZN_mult_inv_coprime_iff",
  ``!n. 1 < n ==> !x. coprime x n <=> ?y. (x * y) MOD n = 1``,
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  rw[EQ_IMP_THM] >-
  metis_tac[GCD_ONE_PROPERTY, GCD_SYM, MULT_COMM] >>
  metis_tac[ZN_mult_inv_coprime]);

(* Theorem: 1 < m /\ coprime m n ==> (n MOD m) IN (Invertibles (ZN m).prod).carrier *)
(* Proof:
   Expanding by Invertibles_def, ZN_def, this is to show:
   (1) n MOD m < m
       Since 1 < m ==> 0 < m, true    by MOD_LESS.
   (2) ?y. y < m /\ ((n MOD m * y) MOD m = 1) /\ ((y * n MOD m) MOD m = 1)
       Since  n MOD m < m             by MOD_LESS
       ?y. 0 < y /\ y < m /\ coprime n y /\
          ((y * (n MOD m)) MOD m = 1) by GCD_MOD_MULT_INV
       The result follows             by MULT_COMM
*)
Theorem ZN_coprime_invertible:
  !m n. 1 < m /\ coprime m n ==> (n MOD m) IN (Invertibles (ZN m).prod).carrier
Proof
  rpt strip_tac >>
  `0 < n /\ 0 < n MOD m` by metis_tac[MOD_NONZERO_WHEN_GCD_ONE] >>
  `0 < m` by decide_tac >>
  rw_tac std_ss[Invertibles_def, monoid_invertibles_def, ZN_def, times_mod_def,
                GSPECIFICATION, IN_COUNT] >>
  metis_tac[MOD_LESS, coprime_mod, GCD_MOD_MULT_INV, MULT_COMM]
QED

(* Same result with a different proof. *)

(* Theorem: 1 < m ==> coprime m n ==> n IN (Invertibles (ZN m).prod) *)
(* Proof:
   Expanding by definitions, this is to show:
   (1) n MOD m < m
       True by MOD_LESS
   (2) ?y. y < m /\ ((n MOD m * y) MOD m = 1) /\ ((y * n MOD m) MOD m = 1)
       We have  n MOD m) < m          by MOD_LESS
           and  0 < (n MOD m)         by MOD_NONZERO_WHEN_GCD_ONE
          also  coprime m (n MOD m)   by coprime_mod
       Hence ?y. 0 < y /\ y < m /\
           (y * (n MOD m)) MOD m = 1  by GCD_MOD_MULT_INV
       and ((n MOD m) * y) MOD m = 1  by MULT_COMM
*)
Theorem ZN_coprime_invertible[allow_rebind]:
  !m n. 1 < m /\ coprime m n ==> (n MOD m) IN (Invertibles (ZN m).prod).carrier
Proof
  rw_tac std_ss[Invertibles_def, monoid_invertibles_def, ZN_def, times_mod_def,
                GSPECIFICATION, IN_COUNT]
  >- rw[] >>
  ‘0 < m’ by decide_tac >>
  ‘(n MOD m) < m’ by rw[] >>
  metis_tac[MOD_NONZERO_WHEN_GCD_ONE, GCD_MOD_MULT_INV, coprime_mod, MULT_COMM]
QED

(* Theorem: 1 < n ==> (Invertibles (ZN n).prod = Estar n) *)
(* Proof:
   Note 1 < n ==> 0 < n /\ n <> 1
    and (ZN n).prod.carrier = (ZN n).carrier         by ZN_ring, ring_carriers, 0 < n
   By Invertibles_def, Estar_def, this is to show:
   (1) monoid_invertibles (ZN n).prod = Euler n
       By monoid_invertibles_def, Euler_def, EXTENSION, ZN_property, this is to show:
          x < n /\ (?y. y < n /\ ((x * y) MOD n = 1)) <=> 0 < x /\ x < n /\ coprime n x
       That is:
       (1) (x * y) MOD n = 1 ==> 0 < x
           By contradiction, suppose x = 0.
           Then  0 MOD n = 1                         by MULT
             or        0 = 1                         by ZERO_MOD
           which is a contradiction.
       (2) (x * y) MOD n = 1 ==> coprime n x, true   by ZN_mult_inv_coprime
       (3) coprime n x ==> ?y. y IN (ZN n).prod.carrier /\ ((x * y) MOD n = 1)
           Note ?z. (x * z) MOD n = 1                by ZN_mult_inv_coprime_iff
           Let y = z MOD n.
           Then y < n                                by MOD_LESS
             so y IN (ZN n).prod.carrier             by ZN_property
               (x * y) MOD n
             = (x * (z MOD n)) MOD n                 by y = z MOD n
             = (x * z) MOD n                         by MOD_TIMES2, MOD_MOD
             = 1                                     by above
   (2) (ZN n).prod.op = (\i j. (i * j) MOD n), true  by FUN_EQ_THM, ZN_property
   (3) (ZN n).prod.id = 1, true                      by ZN_property, n <> 1
*)
val ZN_invertibles = store_thm(
  "ZN_invertibles",
  ``!n. 1 < n ==> (Invertibles (ZN n).prod = Estar n)``,
  rpt strip_tac >>
  `0 < n /\ n <> 1` by decide_tac >>
  `(ZN n).prod.carrier = (ZN n).carrier` by rw[ZN_ring, ring_carriers] >>
  rw[Invertibles_def, Estar_def] >| [
    rw[monoid_invertibles_def, Euler_def, EXTENSION, ZN_property] >>
    rw[EQ_IMP_THM] >| [
      spose_not_then strip_assume_tac >>
      `(x = 0) /\ (1 <> 0)` by decide_tac >>
      metis_tac[MULT, ZERO_MOD],
      metis_tac[ZN_mult_inv_coprime, coprime_sym],
      `?z. (x * z) MOD n = 1` by rw[GSYM ZN_mult_inv_coprime_iff, coprime_sym] >>
      qexists_tac `z MOD n` >>
      rpt strip_tac >-
      rw[MOD_LESS] >>
      metis_tac[MOD_TIMES2, MOD_MOD]
    ],
    rw[FUN_EQ_THM, ZN_property],
    rw[ZN_property]
  ]);

(* ------------------------------------------------------------------------- *)
(* ZN Order                                                                  *)
(* ------------------------------------------------------------------------- *)

(* Overload for order of m in (ZN n).prod *)
val _ = overload_on("ordz", ``\n m. order (ZN n).prod m``);

(* Order for MOD 1:

I thought ordz m n is only defined for 1 < m,
as (x ** j) MOD 1 = 0 by MOD_1, or (x ** j) MOD 1 <> 1.
However, Ring (ZN 1) by ZN_ring.
In fact (ZN 1) = {0} is trivial ring, or 1 = 0.
Thus (x ** j = 1) MOD 1, and the least j is 1.

*)

(* Theorem: (ZN 1).prod.exp n k = 0 *)
(* Proof:
   By monoid_exp_def, ZN_property, this is to show:
      FUNPOW ((ZN 1).prod.op n) k 0 = 0
   Note (ZN 1).prod.op n = K 0         by ZN_property, FUN_EQ_THM
   Thus the goal is: FUNPOW (K 0) k 0 = 0

   By induction on k.
   Base: FUNPOW (K 0) 0 0 = 0, true    by FUNPOW
   Step: FUNPOW (K 0) k 0 = 0 ==> FUNPOW (K 0) (SUC k) 0 = 0
           FUNPOW (K 0) (SUC k) 0
         = FUNPOW (K 0) k ((K 0) 0)    by FUNPOW
         = FUNPOW (K 0) k 0            by K_THM
         = 0                           by induction hypothesis
*)
val ZN_1_exp = store_thm(
  "ZN_1_exp",
  ``!n k. (ZN 1).prod.exp n k = 0``,
  rw[monoid_exp_def, ZN_property] >>
  `(ZN 1).prod.op n = K 0` by rw[ZN_property, FUN_EQ_THM] >>
  rw[] >>
  Induct_on `k` >>
  rw[FUNPOW]);

(* Theorem: ordz 1 n = 1 *)
(* Proof:
   By order_def, period_def, and ZN_property, this is to show:
      (case OLEAST k. 0 < k /\ ((ZN 1).prod.exp n k = 0) of NONE => 0 | SOME k => k) = 1
   Note (ZN 1).prod.exp n k = 0   by ZN_1_exp
   The goal becomes: (case OLEAST k. 0 < k of NONE => 0 | SOME k => k) = 1
   or 0 < n /\ !m. m < n ==> (m = 0) ==> n = 1      by OLEAST_INTRO
   By contradiction, suppose n <> 1.
   Then 1 < n                                       by n <> 0, n <> 1
   By implication, 1 = 0, which is a contradiction.
*)
val ZN_order_mod_1 = store_thm(
  "ZN_order_mod_1",
  ``!n. ordz 1 n = 1``,
  rw[order_def, period_def, ZN_property] >>
  rw[ZN_1_exp] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  rw[] >>
  spose_not_then strip_assume_tac >>
  `1 < n /\ 1 <> 0` by decide_tac >>
  metis_tac[]);

(* Theorem: 0 < m ==> ordz m (n MOD m) = ordz m n *)
(* Proof:
   Since (ZN m).prod = times_mod m                                  by ZN_def
     and !k. (times_mod m).exp (n MOD m) k = (times_mod m).exp n k  by times_mod_exp, MOD_MOD
   Expanding by order_def, period_def, this is trivially true.
*)
val ZN_order_mod = store_thm(
  "ZN_order_mod",
  ``!m n. 0 < m ==> (ordz m (n MOD m) = ordz m n)``,
  rw[ZN_def, times_mod_exp, order_def, period_def]);

(* Theorem: 0 < m ==> (order (Invertibles (ZN m).prod) (n MOD m) = ordz m n) *)
(* Proof:
        order (Invertibles (ZN m).prod) (n MOD m)
      = ordz m (n MOD m)          by Invertibles_order
      = ordz m n                  by ZN_order_mod, 0 < m
*)
val ZN_invertibles_order = store_thm(
  "ZN_invertibles_order",
  ``!m n. 0 < m ==> (order (Invertibles (ZN m).prod) (n MOD m) = ordz m n)``,
  rw[Invertibles_order, ZN_order_mod]);

(*
> order_thm |> ISPEC ``(ZN n).prod`` |> SPEC ``0`` |> SPEC ``1``;
val it = |- 0 < 1 ==> ((ordz n 0 = 1) <=>
    ((ZN n).prod.exp 0 1 = (ZN n).prod.id) /\
    !m. 0 < m /\ m < 1 ==> (ZN n).prod.exp 0 m <> (ZN n).prod.id): thm
> order_eq_0 |> ISPEC ``(ZN n).prod`` |> SPEC ``0``;
val it = |- (ordz n 0 = 0) <=> !n'. 0 < n' ==> (ZN n).prod.exp 0 n' <> (ZN n).prod.id: thm
> monoid_order_eq_1 |> ISPEC ``(ZN n).prod``;
val it = |- Monoid (ZN n).prod ==> !x. x IN (ZN n).prod.carrier ==> ((ordz n x = 1) <=> (x = (ZN n).prod.id)): thm
*)

(* Theorem: 0 < n ==> (ordz n 0 = if n = 1 then 1 else 0) *)
(* Proof:
   If n = 1,
      to show: 0 < n ==> ordz 1 0 = 1.
      Let g = (ZN 1).prod
      Then Monoid g        by ZN_ring, ring_mult_monoid, 0 < n
       and g.id = 0        by ZN_def, times_mod_def
      Note 0 IN g.carrier  by monoid_id_element
      Thus ordz 1 0 = 1    by monoid_order_eq_1
   If n <> 1,
      to show: 0 < n /\ n <> 1 ==> ordz 1 0 = 0.
      By order_eq_0, this is
      to show: !k. 0 < k ==> (ZN n).prod.exp 0 k <> (ZN n).prod.id
           or: !k. 0 < k ==> (0 ** k) MOD n <> 1      by ZN_property, ZN_exp
           or: 0 <> 1                                 by ZERO_EXP, 0 < k
      which is true.
*)
val ZN_order_0 = store_thm(
  "ZN_order_0",
  ``!n. 0 < n ==> (ordz n 0 = if n = 1 then 1 else 0)``,
  rw[] >| [
    `(ZN 1).prod.id = 0` by rw[ZN_def, times_mod_def] >>
    `Monoid (ZN 1).prod` by rw[ZN_ring, ring_mult_monoid] >>
    metis_tac[monoid_order_eq_1, monoid_id_element],
    rw[order_eq_0, ZN_property, ZN_exp, ZERO_EXP]
  ]);

(* Theorem: 0 < n ==> (ordz n 1 = 1) *)
(* Proof:
   If n = 1,
      to show: ordz 1 1 = 1, true   by ZN_order_mod_1
   If n <> 1,
      Note Ring (ZN n)              by ZN_ring, 0 < n
        so Monoid (ZN n).prod       by ring_mult_monoid
       and (ZN n).prod.id = 1       by ZN_property, n <> 1
       ==> ordz n 1 = 1             by monoid_order_id
*)
val ZN_order_1 = store_thm(
  "ZN_order_1",
  ``!n. 0 < n ==> (ordz n 1 = 1)``,
  rpt strip_tac >>
  Cases_on `n = 1` >-
  rw[ZN_order_mod_1] >>
  `0 < n /\ n <> 1` by decide_tac >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `Monoid (ZN n).prod` by rw[ring_mult_monoid] >>
  `(ZN n).prod.id = 1` by rw[ZN_property] >>
  metis_tac[monoid_order_id]);

(* Theorem: 0 < m ==> ((ordz m n = 1) <=> (n MOD m = 1 MOD m)) *)
(* Proof:
   First, Ring (ZN m)                             by ZN_ring, 0 < m
      so  Monoid (ZN m).prod                      by ring_mult_monoid
     and  (ZN m).prod.carrier = (ZN m).carrier    by ring_carriers
    with  (ZN m).prod.id = 1 MOD m                by ZN_property

    Now,  n MOD m IN (ZN m).carrier               by ZN_property
     and  ordz m n = ordz m (n MOD m)             by ZN_order_mod, 1 < m
    Thus  n MOD m = 1 MOD m                       by monoid_order_eq_1
*)
val ZN_order_eq_1 = store_thm(
  "ZN_order_eq_1",
  ``!m n. 0 < m ==> ((ordz m n = 1) <=> (n MOD m = 1 MOD m))``,
  rpt strip_tac >>
  `Ring (ZN m)` by rw[ZN_ring] >>
  `Monoid (ZN m).prod` by rw[] >>
  `ordz m n = ordz m (n MOD m)` by rw[ZN_order_mod] >>
  rw[monoid_order_eq_1, ZN_property]);

(* Theorem: 1 < m ==> ((ordz m n = 1) <=> (n MOD m = 1)) *)
(* Proof: ZN_order_eq_1, ONE_MOD *)
val ZN_order_eq_1_alt = store_thm(
  "ZN_order_eq_1_alt",
  ``!m n. 1 < m ==> ((ordz m n = 1) <=> (n MOD m = 1))``,
  rw[ZN_order_eq_1]);

(* Theorem: 0 < m ==> (n ** ordz m n MOD m = 1 MOD m) *)
(* Proof:
   Let k = ordz m n.
   To show: n ** k MOD m = 1
      n ** k MOD m
    = (ZN m).prod.exp n k        by ZN_exp, 0 < m
    = (ZN m).prod.id             by order_property
    = 1 MOD m                    by ZN_property
*)
val ZN_order_property = store_thm(
  "ZN_order_property",
  ``!m n. 0 < m ==> (n ** ordz m n MOD m = 1 MOD m)``,
  rw[order_property, ZN_property, GSYM ZN_exp]);

(* Theorem: 1 < m ==> (n ** ordz m n MOD m = 1) *)
(* Proof: by ZN_order_property, ONE_MOD *)
val ZN_order_property_alt = store_thm(
  "ZN_order_property_alt",
  ``!m n. 1 < m ==> (n ** ordz m n MOD m = 1)``,
  rw[ZN_order_property]);

(* Theorem: 0 < m ==> m divides (n ** ordz m n - 1) *)
(* Proof:
   If m = 1, true                   by ONE_DIVIDES_ALL
   If m <> 1, then 1 < m            by 0 < m, m <> 1
   Let k = ordz m n, to show:  m divides n ** k - 1.
   Since n ** k MOD m = 1           by ZN_order_property, 0 < m
      or n ** k MOD m = 1 MOD m     by ONE_MOD, 1 < m
      so (n ** k - 1) MOD m = 0     by MOD_EQ_DIFF, 0 < m
   Hence m divides (n ** k - 1)     by DIVIDES_MOD_0, 0 < m
*)
val ZN_order_divisibility = store_thm(
  "ZN_order_divisibility",
  ``!m n. 0 < m ==> m divides (n ** ordz m n - 1)``,
  rpt strip_tac >>
  Cases_on `m = 1` >-
  rw[] >>
  rw[DIVIDES_MOD_0, MOD_EQ_DIFF, ONE_MOD, ZN_order_property]);

(* Theorem: 1 < m /\ coprime m n ==> (n MOD m) IN Euler m *)
(* Proof:
   By Euler_def, this is to show:
   (1) 0 < n MOD m.
       Note 0 < n                    by GCD_0, m <> 1
       Thus true                     by MOD_NONZERO_WHEN_GCD_ONE
   (2) coprime m (n MOD m), true     by MOD_WITH_GCD_ONE, 0 < m.
*)
val ZN_coprime_euler_element = store_thm(
  "ZN_coprime_euler_element",
  ``!m n. 1 < m /\ coprime m n ==> (n MOD m) IN Euler m``,
  rw[Euler_def] >| [
    `n <> 0` by metis_tac[GCD_0, LESS_NOT_EQ] >>
    rw[MOD_NONZERO_WHEN_GCD_ONE],
    rw[MOD_WITH_GCD_ONE]
  ]);

(* Theorem: 0 < m /\ coprime m n ==> 0 < ordz m n /\ (n ** ordz m n MOD m = 1 MOD m) *)
(* Proof:
   If m = 1,
      Then ordz 1 n = 1  > 0              by ZN_order_mod_1
       and n ** ordz m n MOD 1 = 1 MOD 1  by MOD_1
   If m <> 1,
      Then 1 < m                          by m <> 1, m <> 0
       and 1 MOD m = 1                    by ONE_MOD, 1 < m
      also (n MOD m) IN (Invertibles (ZN m).prod).carrier        by ZN_coprime_invertible, 1 < m
      Now, FiniteGroup (Invertibles (ZN m).prod)                 by ZN_invertibles_finite_group, 0 < m
       and order (Invertibles (ZN m).prod) (n MOD m) = ordz m n  by ZN_invertibles_order, 0 < m
       and (ZN m).prod.id = 1                                    by ZN_property, m <> 1
     Hence 0 < ordz m n                            by group_order_property
       and n ** (ordz m n) = (ZN m).prod.id = 1    by Invertibles_property, ZN_exp, EXP_MOD
*)
val ZN_coprime_order = store_thm(
  "ZN_coprime_order",
  ``!m n. 0 < m /\ coprime m n ==> 0 < ordz m n /\ (n ** ordz m n MOD m = 1 MOD m)``,
  ntac 3 strip_tac >>
  Cases_on `m = 1` >-
  rw[ZN_order_mod_1] >>
  `FiniteGroup (Invertibles (ZN m).prod)` by rw[ZN_invertibles_finite_group] >>
  `(n MOD m) IN (Invertibles (ZN m).prod).carrier` by rw[ZN_coprime_invertible] >>
  `order (Invertibles (ZN m).prod) (n MOD m) = ordz m n` by rw[ZN_invertibles_order] >>
  `(ZN m).prod.id = 1` by rw[ZN_property] >>
  `1 MOD m = 1` by rw[] >>
  metis_tac[group_order_property, Invertibles_property, ZN_exp, EXP_MOD]);

(* This is slightly better than the next: ZN_coprime_order_alt *)

(* Theorem: 1 < m /\ coprime m n ==> 0 < ordz m n /\ (n ** (ordz m n) = 1) *)
(* Proof: by ZN_coprime_order, ONE_MOD *)
val ZN_coprime_order_alt = store_thm(
  "ZN_coprime_order_alt",
  ``!m n. 1 < m /\ coprime m n ==> 0 < ordz m n /\ ((n ** (ordz m n)) MOD m = 1)``,
  rw[ZN_coprime_order]);

(* Theorem: 0 < m /\ coprime m n ==> (ordz m n) divides (totient m) *)
(* Proof:
   If m = 1,
      Then ordz 1 n = 1                 by ZN_order_mod_1
       and 1 divides (totient 1)        by ONE_DIVIDES_ALL
   If m <> 1, then 1 < m                by 0 < m, m <> 1
   Let x = n MOD m
   Step 1: show x IN (Estar m).carrier, apply Euler_Fermat_thm
   Since coprime m n ==> ~(m divides n) by coprime_not_divides
      so x <> 0                         by DIVIDES_MOD_0
   hence 0 < x /\ x < m                 by MOD_LESS, 0 < m
     and coprime m x                    by coprime_mod, 0 < m
    Thus x IN (Estar m).carrier         by Estar_element
     ==> x ** (totient m) MOD m = 1     by Euler_Fermat_eqn (1)
   Step 2: show x IN (ZN m).prod.carrier, apply monoid_order_condition
    Now, Ring (ZN m)                    by ZN_ring, 0 < m
     ==> Monoid (ZN m).prod             by ring_mult_monoid
     and (ZN m).prod.id = 1             by ZN_property, m <> 1
   hence x IN (ZN m).prod.carrier       by ZN_property, MOD_LESS, 0 < m
    Thus ordz m x = ordz m n            by ZN_order_mod, 1 < m
   and (1) becomes
           (ZN m).prod.exp x (totient m) = (ZN m).prod.id  by ZN_exp
   Therefore   (ordz m n) divides (totient m)              by monoid_order_condition
*)
val ZN_coprime_order_divides_totient = store_thm(
  "ZN_coprime_order_divides_totient",
  ``!m n. 0 < m /\ coprime m n ==> (ordz m n) divides (totient m)``,
  rpt strip_tac >>
  Cases_on `m = 1` >-
  rw[ZN_order_mod_1] >>
  qabbrev_tac `x = n MOD m` >>
  `x < m` by rw[Abbr`x`] >>
  `~(m divides n)` by rw[coprime_not_divides] >>
  `x <> 0` by rw[GSYM DIVIDES_MOD_0, Abbr`x`] >>
  `0 < x` by decide_tac >>
  `coprime m x` by metis_tac[coprime_mod] >>
  `x IN (Estar m).carrier` by rw[Estar_element] >>
  `x ** (totient m) MOD m = 1` by rw[Euler_Fermat_eqn] >>
  `Ring (ZN m)` by rw[ZN_ring] >>
  `Monoid (ZN m).prod` by rw[ring_mult_monoid] >>
  `m <> 1` by decide_tac >>
  `(ZN m).prod.id = 1` by rw[ZN_property] >>
  `x IN (ZN m).prod.carrier` by rw[ZN_property, MOD_LESS, Abbr`x`] >>
  metis_tac[monoid_order_condition, ZN_exp, ZN_order_mod]);

(* Theorem: 0 < m /\ coprime m n ==> (ordz m n) divides (phi m) *)
(* Proof:
   If m = 1, then ordz 1 n = 1       by ZN_order_mod_1
              and 1 divides (phi 1)  by ONE_DIVIDES_ALL
   If m <> 1, then 1 < m             by 0 < m, m <> 1
                so phi m = totient m           by phi_eq_totient, 1 < m
              thus (ordz m n) divides (phi m)  by ZN_coprime_order_divides_totient
*)
val ZN_coprime_order_divides_phi = store_thm(
  "ZN_coprime_order_divides_phi",
  ``!m n. 0 < m /\ coprime m n ==> (ordz m n) divides (phi m)``,
  rpt strip_tac >>
  Cases_on `m = 1` >-
  rw[ZN_order_mod_1] >>
  rw[ZN_coprime_order_divides_totient, phi_eq_totient]);

(* Theorem: 1 < m /\ coprime m n ==> ordz m n < m *)
(* Proof:
   Note ordz m n divides phi m   by ZN_coprime_order_divides_phi, 0 < m
    and 0 < phi m                by phi_pos, 0 < m
   Thus ordz m n <= phi m        by DIVIDES_LE, 0 < phi m
                  < m            by phi_lt, 1 < m
*)
val ZN_coprime_order_lt = store_thm(
  "ZN_coprime_order_lt",
  ``!m n. 1 < m /\ coprime m n ==> ordz m n < m``,
  rpt strip_tac >>
  `0 < phi m /\ phi m < m` by rw[phi_pos, phi_lt] >>
  `ordz m n <= phi m` by rw[ZN_coprime_order_divides_phi, DIVIDES_LE] >>
  decide_tac);

(* Theorem: 0 < m /\ coprime m n ==> !k. (n ** k) MOD m = (n ** (k MOD (ordz m n))) MOD m *)
(* Proof:
   If m = 1, true since ordz 1 n = 1    by ZN_order_mod_1
   If m <> 1, then 1 < m                by 0 < m, m <> 1
   Let z = ordz m n.
   Note 1 < m ==> 0 < m          by arithmetic
    and 0 < z                    by ZN_coprime_order_alt, 1 < m, coprime m n
   Let g = Invertibles (ZN m).prod, the Euler group.
   Then FiniteGroup g            by ZN_invertibles_finite_group, 0 < m
    ==> n MOD m IN g.carrier     by ZN_coprime_invertible, 1 < n, coprime m n
   Note z = ordz m n  by ZN_order_mod, 1 < m
          = order g (n MOD m)    by ZN_invertibles_order, 1 < m, coprime m n

    Let x = n MOD m
   Then x IN g.carrier                              by above
    and 0 < order g x                               by above, 0 < z
   Note !x k. g.exp x k = (ZN m).prod.exp x k       by Invertibles_property
    and !x k.(ZN m).prod.exp x k = (x ** k) MOD m   by ZN_exp

       (n ** k) MOD m
     = ((n MOD m) ** k) MOD m          by EXP_MOD, 0 < m
     = ((n MOD m) ** (k MOD z)) MOD m  by group_exp_mod_order, n MOD m IN g.carrier, 0 < z
     = ((n ** (k MOD z)) MOD m)        by EXP_MOD, 0 < m
*)
val ZN_coprime_exp_mod = store_thm(
  "ZN_coprime_exp_mod",
  ``!m n. 0 < m /\ coprime m n ==> !k. (n ** k) MOD m = (n ** (k MOD (ordz m n))) MOD m``,
  rpt strip_tac >>
  Cases_on `m = 1` >-
  rw[ZN_order_mod_1] >>
  qabbrev_tac `z = ordz m n` >>
  `0 < m` by decide_tac >>
  `0 < z` by rw[ZN_coprime_order_alt, Abbr`z`] >>
  qabbrev_tac `g = Invertibles (ZN m).prod` >>
  `FiniteGroup g` by rw[ZN_invertibles_finite_group, Abbr`g`] >>
  `n MOD m IN g.carrier` by rw[ZN_coprime_invertible, Abbr`g`] >>
  `z = ordz m n` by rw[ZN_order_mod, Abbr`z`] >>
  `_ = order g (n MOD m)` by rw[ZN_invertibles_order, Abbr`g`] >>
  `Group g` by rw[finite_group_is_group] >>
  `(n ** k) MOD m = ((n MOD m) ** k) MOD m` by metis_tac[EXP_MOD] >>
  `_ = ((n MOD m) ** (k MOD z)) MOD m` by metis_tac[group_exp_mod_order, Invertibles_property, ZN_exp] >>
  `_ = ((n ** (k MOD z)) MOD m)` by metis_tac[EXP_MOD] >>
  rw[]);

(* Theorem: 0 < m /\ coprime m n /\ (!p. prime p /\ p divides n ==> (ordz m p = 1)) ==> (ordz m n = 1) *)
(* Proof:
   If m = 1, true since ordz 1 n = 1             by ZN_order_mod_1
   If m <> 1, then 1 < m                         by 0 < m, m <> 1
               and 1 MOD m = 1                   by ONE_MOD
   If n = 1, true                                by ZN_order_1
   If n <> 1,
      Since m <> 1, coprime m n ==> n <> 0       by GCD_0R
      Thus 0 < n and 1 < n                       by n <> 1

      Claim: !p. prime p /\ p divides n ==> (p MOD m = 1)
      Proof: prime p /\ p divides n
         ==> coprime m n ==> coprime m p         by coprime_prime_factor_coprime, GCD_SYM, 1 < m
         and ordz m p = 1                        by implication
         ==> p MOD m = 1                         by ZN_order_eq_1

      Thus n MOD m = 1                           by ALL_PRIME_FACTORS_MOD_EQ_1
       ==> ordz m p = 1                          by ZN_order_eq_1
*)
val ZN_order_eq_1_by_prime_factors = store_thm(
  "ZN_order_eq_1_by_prime_factors",
  ``!m n. 0 < m /\ coprime m n /\ (!p. prime p /\ p divides n ==> (ordz m p = 1)) ==> (ordz m n = 1)``,
  rpt strip_tac >>
  Cases_on `m = 1` >-
  rw[ZN_order_mod_1] >>
  Cases_on `n = 1` >-
  rw[ZN_order_1] >>
  `n <> 0` by metis_tac[GCD_0R] >>
  `0 < n /\ 1 < n /\ 1 < m` by decide_tac >>
  `!p. prime p /\ p divides n ==> (p MOD m = 1)` by
  (rpt strip_tac >>
  `coprime m p` by metis_tac[coprime_prime_factor_coprime, GCD_SYM] >>
  metis_tac[ZN_order_eq_1, ONE_MOD]) >>
  `n MOD m = 1` by rw[ALL_PRIME_FACTORS_MOD_EQ_1] >>
  rw[ZN_order_eq_1]);

(*
> order_eq_0 |> ISPEC ``(ZN m).prod`` |> ISPEC ``n:num``;
val it = |- (ordz m n = 0) <=> !n'. 0 < n' ==> (ZN m).prod.exp n n' <> (ZN m).prod.id: thm
*)

(* Theorem: 1 < m ==> (ordz m n <> 0 <=> ?k. 0 < k /\ (n ** k MOD m = 1)) *)
(* Proof:
   By order_eq_0,
      (ordz m n = 0) <=> !k. 0 < k ==> (ZN m).prod.exp n k <> (ZN m).prod.id
   or (ordz m n = 0) <=> !k. 0 < k ==> n ** k MOD m <> 1    by ZN_exp, ZN_ids_alt, 0 < m, 1 < m
   The result follows by taking negation of both sides.
*)
val ZN_order_nonzero_iff = store_thm(
  "ZN_order_nonzero_iff",
  ``!m n. 1 < m ==> (ordz m n <> 0 <=> ?k. 0 < k /\ (n ** k MOD m = 1))``,
  rw[order_eq_0, ZN_exp, ZN_ids_alt]);

(* Theorem: 1 < m ==> ((ordz m n = 0) <=> (!k. 0 < k ==> n ** k MOD m <> 1)) *)
(* Proof: by ZN_order_nonzero_iff *)
val ZN_order_eq_0_iff = store_thm(
  "ZN_order_eq_0_iff",
  ``!m n. 1 < m ==> ((ordz m n = 0) <=> (!k. 0 < k ==> n ** k MOD m <> 1))``,
  metis_tac[ZN_order_nonzero_iff]);

(* Theorem: 0 < m ==> ((ordz m n <> 0) <=> coprime m n) *)
(* Proof:
   If m = 1, true since ordz 1 n = 1 <> 0        by ZN_order_mod_1
                    and coprime 1 n              by GCD_1
   If m <> 1, then 1 < m                         by 0 < m, m <> 1
               and 1 MOD m = 1                   by ONE_MOD
   If part: ordz m n <> 0 ==> coprime m n
      Let x = n MOD m.
      Then ordz m n = ordz m x     by ZN_order_mod, 0 < m
      Note Ring (ZN m)             by ZN_ring, 0 < m
        so Monoid (ZN m).prod      by ring_mult_monoid
       and (ZN m).prod.carrier = (ZN m).carrier   by ring_carriers
      Note x < n                   by MOD_LESS, 0 < m
      Thus x IN (ZN m).carrier     by ZN_property
       Now 0 < ordz m x            by 0 < ordz m n = ordz m x
       ==> x IN (Invertibles (ZN m).prod).carrier   by monoid_order_nonzero, Invertibles_carrier
        or x IN (Estar m).carrier                   by ZN_invertibles, 1 < m
     Hence coprime m x             by Estar_element
        or coprime m n             by coprime_mod_iff. 0 < m

   Only-if part: coprime m n ==> ordz m n <> 0
     This is true                  by ZN_coprime_order, 0 < m
*)
val ZN_order_nonzero = store_thm(
  "ZN_order_nonzero",
  ``!m n. 0 < m ==> ((ordz m n <> 0) <=> coprime m n)``,
  rpt strip_tac >>
  Cases_on `m = 1` >-
  rw[ZN_order_mod_1] >>
  rw[EQ_IMP_THM] >| [
    qabbrev_tac `x = n MOD m` >>
    `ordz m n = ordz m x` by rw[ZN_order_mod, Abbr`x`] >>
    `Monoid (ZN m).prod` by rw[ZN_ring, ring_mult_monoid] >>
    `(ZN m).prod.carrier = (ZN m).carrier` by rw[ZN_ring, ring_carriers] >>
    `x IN (ZN m).carrier` by rw[ZN_property, MOD_LESS, Abbr`x`] >>
    `x IN (Invertibles (ZN m).prod).carrier` by rw[monoid_order_nonzero, Invertibles_carrier] >>
    `x IN (Estar m).carrier` by rw[GSYM ZN_invertibles] >>
    `coprime m x` by metis_tac[Estar_element] >>
    rw[Once coprime_mod_iff],
    metis_tac[ZN_coprime_order, NOT_ZERO_LT_ZERO]
  ]);

(* Theorem: 0 < m ==> ((ordz m n = 0) <=> ~(coprime m n)) *)
(* Proof: by ZN_order_nonzero *)
val ZN_order_eq_0 = store_thm(
  "ZN_order_eq_0",
  ``!m n. 0 < m ==> ((ordz m n = 0) <=> ~(coprime m n))``,
  metis_tac[ZN_order_nonzero]);

(* Theorem: 0 < m /\ ~coprime m n ==> !k. 0 < k ==> n ** k MOD m <> 1 *)
(* Proof:
   Note m <> 1                              by GCD_1
    and ~coprime m n ==> ordz m n = 0       by ZN_order_eq_0, 0 < m
    ==> !k. 0 < k ==> (n ** k) MOD m <> 1   by ZN_order_eq_0_iff, 1 < m
*)
val ZN_not_coprime = store_thm(
  "ZN_not_coprime",
  ``!m n. 0 < m /\ ~coprime m n ==> !k. 0 < k ==> n ** k MOD m <> 1``,
  rpt strip_tac >>
  `m <> 1` by metis_tac[GCD_1] >>
  `ordz m n = 0` by rw[ZN_order_eq_0] >>
  `1 < m` by decide_tac >>
  metis_tac[ZN_order_eq_0_iff]);

(* Note: "Since ord k n > 1, there must exist a prime divisor p of n such that ord k p > 1." *)

(* Theorem: 0 < m /\ 1 < ordz m n ==> ?p. prime p /\ p divides n /\ 1 < ordz m p *)
(* Proof:
   By contradiction, suppose !p. prime p /\ p divides n /\ ~(1 < ordz m p).
   Note ordz m n <> 0          by 1 < ordz m n
    ==> coprime m n            by ZN_order_eq_0, 0 < m
    ==> ?p. prime p /\ p divides n /\ (ordz m p <> 1)
                               by ZN_order_eq_1_by_prime_factors, ordz m n <> 1
   Thus ordz m p = 0           by ~(1 < x) <=> (x = 0) \/ (x = 1)
    ==> p divides m            by ZN_order_eq_0, PRIME_GCD, coprime_sym
    ==> p divides 1            by GCD_PROPERTY, coprime m n
    ==> p = 1                  by DIVIDES_ONE
    ==> F                      by NOT_PRIME_1
*)
val ZN_order_gt_1_property = store_thm(
  "ZN_order_gt_1_property",
  ``!m n. 0 < m /\ 1 < ordz m n ==> ?p. prime p /\ p divides n /\ 1 < ordz m p``,
  spose_not_then strip_assume_tac >>
  `coprime m n` by metis_tac[ZN_order_eq_0, DECIDE``1 < x ==> x <> 0``] >>
  `?p. prime p /\ p divides n /\ (ordz m p <> 1)` by metis_tac[ZN_order_eq_1_by_prime_factors, LESS_NOT_EQ] >>
  `ordz m p = 0` by metis_tac[DECIDE``~(1 < x) <=> (x = 0) \/ (x = 1)``] >>
  `p divides m` by metis_tac[ZN_order_eq_0, PRIME_GCD, coprime_sym] >>
  `p divides 1` by metis_tac[GCD_PROPERTY] >>
  metis_tac[DIVIDES_ONE, NOT_PRIME_1]);

(*
> group_order_divides_exp |> ISPEC ``Invertibles (ZN m).prod``;
val it = |- Group (Invertibles (ZN m).prod) ==>
            !x. x IN (Invertibles (ZN m).prod).carrier ==>
            !n. ((Invertibles (ZN m).prod).exp x n = (Invertibles (ZN m).prod).id) <=>
                 order (Invertibles (ZN m).prod) x divides n: thm
*)

(* Theorem: 1 < m /\ 0 < k ==> ((n ** k MOD m = 1) <=> (ordz m n) divides k) *)
(* Proof:
   Let g = Invertibles (ZN m).prod.
   Note g = Estar m           by ZN_invertibles
   Thus FiniteGroup g         by Estar_finite_group
    and Group g               by finite_group_is_group
    Let x = n MOD m.
   Then x < m                 by MOD_LESS, 0 < m

   If part: n ** k MOD m = 1 ==> (ordz m n) divides k
      Note x ** n MOD m = 1      by given
       ==> ordz m n <> 0         by ZN_order_nonzero_iff, 1 < m
       ==> coprime m n           by ZN_order_eq_0, 1 < m
       ==> coprime m x           by coprime_mod_iff, 0 < m
       Now 0 < x                 by GCD_0, coprime m x, 1 < m
      Thus x IN g.carrier        by Estar_element, 0 < x, x < m, coprime m x
      Note x ** k MOD m = 1      by EXP_MOD, n ** k MOD m = 1
        or (Invertibles (ZN m).prod).exp x n = (Invertibles (ZN m).prod).id  by Estar_exp, Estar_property
       ==> order (Invertibles (ZN m).prod) x divides k          by group_order_divides_exp
        or ordz m n divides k    by ZN_invertibles_order

   Only-if part: (ordz m n) divides k ==> n ** k MOD m = 1
      Note (ordz m n) divides k  by given
       ==> ordz m n <> 0         by ZERO_DIVIDES, 0 < k
       ==> coprime m n           by ZN_order_eq_0, 1 < m
       ==> coprime m x           by coprime_mod_iff, 0 < m
       Now 0 < x                 by GCD_0, coprime m x, 1 < m
      Thus x IN g.carrier        by Estar_element, 0 < x, x < m, coprime m x
      Note ordz m x = ordz m n   by ZN_order_mod, 1 < m
        or order (Invertibles (ZN n).prod) x divides k                 by ZN_invertibles_order, coprime m n
       ==> (Invertibles (ZN n).prod).exp x k = (Invertibles (ZN n).prod).id)  by group_order_divides_exp
        or x ** k MOD m = 1      by Estar_exp, Estar_property
        or n ** k MOD m = 1      by EXP_MOD, 0 < m
*)
val ZN_order_divides_exp = store_thm(
  "ZN_order_divides_exp",
  ``!m n k. 1 < m /\ 0 < k ==> ((n ** k MOD m = 1) <=> (ordz m n) divides k)``,
  rpt strip_tac >>
  `0 < m` by decide_tac >>
  qabbrev_tac `g = Invertibles (ZN m).prod` >>
  `g = Estar m` by rw[ZN_invertibles, Abbr`g`] >>
  `FiniteGroup g` by rw[Estar_finite_group] >>
  `Group g` by rw[finite_group_is_group] >>
  qabbrev_tac `x = n MOD m` >>
  `x < m` by rw[Abbr`x`] >>
  rewrite_tac[EQ_IMP_THM] >>
  rpt strip_tac >| [
    `ordz m n <> 0` by metis_tac[ZN_order_nonzero_iff] >>
    `coprime m n` by metis_tac[ZN_order_eq_0] >>
    `coprime m x` by rw[GSYM coprime_mod_iff, Abbr`x`] >>
    `0 < x` by metis_tac[GCD_0, NOT_ZERO_LT_ZERO, DECIDE``1 < n ==> n <> 1``] >>
    `x IN g.carrier` by rw[Estar_element] >>
    `x ** k MOD m = 1` by rw[EXP_MOD, Abbr`x`] >>
    `order (Invertibles (ZN m).prod) x divides k` by rw[GSYM group_order_divides_exp, Estar_exp, Estar_property] >>
    metis_tac[ZN_invertibles_order],
    `ordz m n <> 0` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
    `coprime m n` by metis_tac[ZN_order_eq_0] >>
    `coprime m x` by rw[GSYM coprime_mod_iff, Abbr`x`] >>
    `0 < x` by metis_tac[GCD_0, NOT_ZERO_LT_ZERO, DECIDE``1 < n ==> n <> 1``] >>
    `x IN g.carrier` by rw[Estar_element] >>
    `ordz m x = ordz m n` by rw[ZN_order_mod, Abbr`x`] >>
    `x ** k MOD m = 1` by metis_tac[group_order_divides_exp, ZN_invertibles_order, Estar_exp, Estar_property] >>
    rw[GSYM EXP_MOD, Abbr`x`]
  ]);

(* Theorem: 0 < m /\ 0 < ordz m n ==> (ordz m n) divides (phi m) *)
(* Proof:
   Note 0 < ordz m n ==> coprime m n    by ZN_order_nonzero, 0 < m
   Thus (ordz m n) divides (phi m)      by ZN_coprime_order_divides_phi, 0 < m
*)
val ZN_order_divides_phi = store_thm(
  "ZN_order_divides_phi",
  ``!m n. 0 < m /\ 0 < ordz m n ==> (ordz m n) divides (phi m)``,
  rpt strip_tac >>
  `coprime m n` by metis_tac[ZN_order_nonzero, NOT_ZERO_LT_ZERO] >>
  rw[ZN_coprime_order_divides_phi]);

(* Theorem: 0 < m ==> ordz m n <= phi m *)
(* Proof:
   If ordz m n = 0, then trivially true.
   Otherwise, 0 < ordz m n.
   Note ordz m n divides phi m       by ZN_order_divides_phi, 0 < m /\ 0 < ordz m n
    and 0 < phi m                    by phi_pos, 0 < m
     so ordz m n <= phi m            by DIVIDES_LE, 0 < phi m
*)
val ZN_order_upper = store_thm(
  "ZN_order_upper",
  ``!m n. 0 < m ==> ordz m n <= phi m``,
  rpt strip_tac >>
  Cases_on `ordz m n = 0` >-
  rw[] >>
  `ordz m n divides phi m` by rw[ZN_order_divides_phi] >>
  `0 < phi m` by rw[phi_pos] >>
  rw[DIVIDES_LE]);

(* Theorem: 0 < m ==> ordz m n <= m *)
(* Proof:
   Note ordz m n <= phi m            by ZN_order_upper, 0 < m
   Also phi m <= m                   by phi_le
   Thus ordz m n <= m                by LESS_EQ_TRANS
*)
val ZN_order_le = store_thm(
  "ZN_order_le",
  ``!m n. 0 < m ==> ordz m n <= m``,
  rpt strip_tac >>
  `ordz m n <= phi m` by rw[ZN_order_upper] >>
  `phi m <= m` by rw[phi_le] >>
  decide_tac);

(* Theorem: 0 < k /\ k < m ==> ordz k n < m *)
(* Proof:
   Note ordz k n <= k      by ZN_order_le, 0 < k
    and             k < m  by given
   Thus ordz k n < m       by LESS_EQ_LESS_TRANS
*)
val ZN_order_lt = store_thm(
  "ZN_order_lt",
  ``!k n m. 0 < k /\ k < m ==> ordz k n < m``,
  rpt strip_tac >>
  `ordz k n <= k` by rw[ZN_order_le] >>
  decide_tac);
(* Therefore, in the search for k such that m <= ordz k n, start with k = m *)

(*
val ZN_order_minimal =
  order_minimal |> ISPEC ``(ZN n).prod`` |> ADD_ASSUM ``1 < n`` |> DISCH_ALL
                |> SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss) [ZN_property, ZN_exp];

val ZN_order_minimal = |- 1 < n ==> !x n'. 0 < n' /\ n' < ordz n x ==> x ** n' MOD n <> 1: thm
*)

(* Theorem: 0 < m /\ 0 < k /\ k < ordz m n ==> n ** k MOD m <> 1 *)
(* Proof:
   Note (ZN m).prod.exp n k <> (ZN m).prod.id    by order_minimal, 0 < k, k < ordz m n
    But (ZN m).prod.exp n k = n ** k MOD n       by ZN_exp, 0 < m
    and m <> 1  since !k. 0 < k /\ k < 1 = F     by ZN_order_mod_1, 0 < m
     so (ZN m).prod.id = 1                       by ZN_property, m <> 1
   Thus n ** k MOD m <> 1                        by above
*)
val ZN_order_minimal = store_thm(
  "ZN_order_minimal",
  ``!m n k. 0 < m /\ 0 < k /\ k < ordz m n ==> n ** k MOD m <> 1``,
  metis_tac[order_minimal, ZN_order_mod_1, ZN_property, ZN_exp, DECIDE``(0 < k /\ k < 1) = F``]);

(* Theorem: 1 < m /\ 1 < n MOD m /\ coprime m n ==> 1 < ordz m n *)
(* Proof:
   Let x = n MOD m.
   Then ordz m x = ordz m n             by ZN_order_mod, 0 < m
    and ordz m n <> 0                   by ZN_order_nonzero, coprime m n
    and ordz m n <> 1                   by ZN_order_eq_1_alt, 1 < m
   Thus ordz 1 < ordz m n               by arithmetic
*)
val ZN_coprime_order_gt_1 = store_thm(
  "ZN_coprime_order_gt_1",
  ``!m n. 1 < m /\ 1 < n MOD m /\ coprime m n ==> 1 < ordz m n``,
  rpt strip_tac >>
  qabbrev_tac `x = n MOD m` >>
  `ordz m x = ordz m n` by rw[ZN_order_mod, Abbr`x`] >>
  `ordz m n <> 0` by rw[ZN_order_nonzero] >>
  `ordz m n <> 1` by rw[ZN_order_eq_1_alt, Abbr`x`] >>
  decide_tac);

(* Note: 1 < n MOD m cannot be replaced by 1 < n. A counterexample:
   1 < m /\ 1 < n /\ coprime m n ==> 1 < ordz m n
   1 < 7 /\ 1 < 43 /\ coprime 7 43, but ordz 7 43 = ordz 7 (43 MOD 7) = ordz 7 1 = 1.
*)

(* Theorem: 1 < n /\ coprime m n /\ 1 < ordz m n ==> 1 < m *)
(* Proof:
   Note m <> 0     by GCD_0, 1 < n
    and m <> 1     by ZN_order_mod_1, 1 < ordz m n
   Thus 1 < m
*)
val ZN_order_with_coprime_1 = store_thm(
  "ZN_order_with_coprime_1",
  ``!m n. 1 < n /\ coprime m n /\ 1 < ordz m n ==> 1 < m``,
  rpt strip_tac >>
  `m <> 0` by metis_tac[GCD_0, LESS_NOT_EQ] >>
  `m <> 1` by metis_tac[ZN_order_mod_1, LESS_NOT_EQ] >>
  decide_tac);

(* Theorem: 1 < m /\ m divides n /\ 1 < ordz k m /\ coprime k n ==> 1 < n /\ 1 < k *)
(* Proof:
   Note k <> 1             by ZN_order_mod_1, 1 < ordz k m, 1 < m
    and n <> 1             by DIVIDES_ONE, m divides n, 1 < m
   also k <> 0 /\ n <> 0   by coprime_0L, coprime_0R
     so 1 < n /\ 1 < k     by both not 0, not 1.
*)
val ZN_order_with_coprime_2 = store_thm(
  "ZN_order_with_coprime_2",
  ``!m n k. 1 < m /\ m divides n /\ 1 < ordz k m /\ coprime k n ==> 1 < n /\ 1 < k``,
  ntac 4 strip_tac >>
  `k <> 1` by metis_tac[ZN_order_mod_1, LESS_NOT_EQ] >>
  `n <> 1` by metis_tac[DIVIDES_ONE, LESS_NOT_EQ] >>
  `k <> 0 /\ n <> 0` by metis_tac[coprime_0L, coprime_0R] >>
  decide_tac);

(* Theorem: 1 < m ==> ((ordz m n = 0) <=> (!j. 0 < j /\ j < m ==> n ** j MOD m <> 1)) *)
(* Proof:
   If part: ordz m n = 0 ==> !j. 0 < j /\ j < m ==> n ** j MOD m <> 1
      Note !j. 0 < j ==> n ** j MOD m <> 1       by ZN_order_eq_0_iff
      Thus n ** j MOD m <> 1                     by just 0 < j
   Only-of part: !j. 0 < j /\ j < m ==> n ** j MOD m <> 1 ==> ordz m n = 0
      By contradiction, suppose ordz m n <> 0.
      Then coprime m n                           by ZN_order_eq_0
      Let k = ord z m.
      Then k < m                                 by ZN_order_lt, 0 < m, coprime m n
       and n ** k MOD m = 1                      by ZN_order_property_alt, 1 < m
      This contradicts n ** k MOD m <> 1         by implication
*)
val ZN_order_eq_0_test = store_thm(
  "ZN_order_eq_0_test",
  ``!m n. 1 < m ==> ((ordz m n = 0) <=> (!j. 0 < j /\ j < m ==> n ** j MOD m <> 1))``,
  rw[EQ_IMP_THM] >-
  metis_tac[ZN_order_eq_0_iff] >>
  spose_not_then strip_assume_tac >>
  `0 < ordz m n /\ 0 < m` by decide_tac >>
  `coprime m n` by metis_tac[ZN_order_eq_0] >>
  `ordz m n < m` by rw[ZN_coprime_order_lt] >>
  metis_tac[ZN_order_property_alt]);

(* Theorem: 1 < n /\ 0 < j /\ 1 < k ==>
            (k divides (n ** j - 1) <=> (ordz k n) divides j) *)
(* Proof:
   Note 1 < n ** j                  by ONE_LT_EXP, 1 < n, 0 < j
       k divides (n ** j - 1)
   <=> (n ** j - 1) MOD k = 0       by DIVIDES_MOD_0, 0 < k
   <=> n ** j MOD k = 1 MOD k       by MOD_EQ, 1 < n ** j, 0 < k
                    = 1             by ONE_MOD, 1 < k
   <=> (ordz k n) divides j         by ZN_order_divides_exp, 0 < j, 1 < k
*)
val ZN_order_divides_tops_index = store_thm(
  "ZN_order_divides_tops_index",
  ``!n j k. 1 < n /\ 0 < j /\ 1 < k ==>
       (k divides (n ** j - 1) <=> (ordz k n) divides j)``,
  rpt strip_tac >>
  `1 < n ** j` by rw[ONE_LT_EXP] >>
  `k divides (n ** j - 1) <=> ((n ** j - 1) MOD k = 0)` by rw[DIVIDES_MOD_0] >>
  `_ = (n ** j MOD k = 1 MOD k)` by rw[MOD_EQ] >>
  `_ = (n ** j MOD k = 1)` by rw[ONE_MOD] >>
  `_ = (ordz k n) divides j` by rw[ZN_order_divides_exp] >>
  metis_tac[]);

(* Theorem: 1 < n /\ 0 < j /\ 1 < k /\ k divides (n ** j - 1) ==> (ordz k n) <= j *)
(* Proof:
   Note (ordz k n) divides j      by ZN_order_divides_tops_index
   Thus (ordz k n) <= j           by DIVIDES_LE, 0 < j
*)
val ZN_order_le_tops_index = store_thm(
  "ZN_order_le_tops_index",
  ``!n j k. 1 < n /\ 0 < j /\ 1 < k /\ k divides (n ** j - 1) ==> (ordz k n) <= j``,
  rw[GSYM ZN_order_divides_tops_index, DIVIDES_LE]);

(* ------------------------------------------------------------------------- *)
(* ZN Order Test                                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < m /\ 0 < k /\ (n ** k MOD m = 1) /\
            (!j. 0 < j /\ j < k /\ j divides phi m ==> n ** j MOD m <> 1) ==>
            !j. 0 < j /\ j < k /\ ~(j divides phi m) ==> (ordz m n = k) \/ n ** j MOD m <> 1 *)
(* Proof:
   By contradiction, suppose (ordz m n <> k) /\ (n ** j MOD m = 1).
   Let z = ordz m n.
   Then z divides j /\ z divides k        by ZN_order_divides_exp
     so z <= k                            by DIVIDES_LE, 0 < k
     or z < k                             by z <> k (from contradiction assumption)
   Also 0 < z                             by ZERO_DIVIDES, z divides j, 0 < j
    and z divides (phi m)                 by ZN_order_divides_phi, 0 < z
    Put j = z in implication gives: n ** z MOD m <> 1
    This contradicts n ** z MOD m = 1     by ZN_order_property_alt, 1 < m
*)
val ZN_order_test_propery = store_thm(
  "ZN_order_test_propery",
  ``!m n k. 1 < m /\ 0 < k /\ (n ** k MOD m = 1) /\
   (!j. 0 < j /\ j < k /\ j divides phi m ==> n ** j MOD m <> 1) ==>
   !j. 0 < j /\ j < k /\ ~(j divides phi m) ==> (ordz m n = k) \/ n ** j MOD m <> 1``,
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `z = ordz m n` >>
  `z divides j /\ z divides k` by rw[GSYM ZN_order_divides_exp, Abbr`z`] >>
  `z <= k` by rw[DIVIDES_LE] >>
  `z < k` by decide_tac >>
  `0 < z` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `z divides (phi m)` by rw[ZN_order_divides_phi, Abbr`z`] >>
  metis_tac[ZN_order_property_alt]);

(*
> order_thm |> GEN_ALL |> ISPEC ``(ZN m).prod`` |> ISPEC ``n:num`` |> ISPEC ``k:num``;
val it = |- 0 < k ==> ((ordz m n = k) <=>
    ((ZN m).prod.exp n k = (ZN m).prod.id) /\
    !m'. 0 < m' /\ m' < k ==> (ZN m).prod.exp n m' <> (ZN m).prod.id): thm
*)

(* Theorem: 1 < m /\ 0 < k ==>
            ((ordz m n = k) <=> ((n ** k) MOD m = 1) /\ !j. 0 < j /\ j < k ==> (n ** j) MOD m <> 1) *)
(* Proof:
   By order_thm, 0 < k ==>
   ((ordz m n = k) <=> ((ZN m).prod.exp n k = (ZN m).prod.id) /\
                       !j. 0 < j /\ j < k ==> (ZN m).prod.exp n j <> (ZN m).prod.id)
   Now (ZN m).prod.exp n k = (n ** k) MOD m    by ZN_exp, 0 < m
   and (ZN m).prod.id = 1                      by ZN_property, m <> 1
   Thus the result follows.
*)
val ZN_order_test_1 = store_thm(
  "ZN_order_test_1",
  ``!m n k. 1 < m /\ 0 < k ==>
   ((ordz m n = k) <=> ((n ** k) MOD m = 1) /\ !j. 0 < j /\ j < k ==> (n ** j) MOD m <> 1)``,
  metis_tac[order_thm, ZN_exp, ZN_ids_alt, DECIDE``1 < m ==> 0 < m``]);

(* Theorem: 1 < m /\ 0 < k ==> ((ordz m n = k) <=>
            (n ** k MOD m = 1) /\ !j. 0 < j /\ j < k /\ j divides (phi m) ==> n ** j MOD m <> 1) *)
(* Proof:
   If part: ordz m n = k ==> (n ** k MOD m = 1) /\ !j. 0 < j /\ j < k /\ j divides (phi m) ==> n ** j MOD m <> 1)
      This is to show:
      (1) n ** (ordz m n) MOD m = 1, true   by ZN_order_property, 1 < m.
      (2) !j. 0 < j /\ j < (ordz m n) /\ j divides (phi m) ==> n ** j MOD m <> 1)
          This is true                      by ZN_order_minimal, 1 < m.
   Only-if part: (n ** k MOD m = 1) /\
                 !j. 0 < j /\ j < k /\ j divides (phi m) ==> n ** j MOD m <> 1) ==> ordz m n = k
      Note the conditions give:
      !j. 0 < j /\ j < k /\ ~(j divides phi m)
          ==> (ordz m n = k) \/ n ** j MOD m <> 1    by ZN_order_test_propery
      Combining both implications,
      !j. 0 < j /\ j < k  ==> n ** j MOD m <> 1
      Thus ordz m n = k                     by ZN_order_test_1
*)
val ZN_order_test_2 = store_thm(
  "ZN_order_test_2",
  ``!m n k. 1 < m /\ 0 < k ==>
     ((ordz m n = k) <=>
      (n ** k MOD m = 1) /\ !j. 0 < j /\ j < k /\ j divides (phi m) ==> n ** j MOD m <> 1)``,
  rw[EQ_IMP_THM] >-
  rw[ZN_order_property] >-
  rw[ZN_order_minimal] >>
  `!j. 0 < j /\ j < k /\ ~(j divides phi m) ==>
       (ordz m n = k) \/ n ** j MOD m <> 1` by rw[ZN_order_test_propery] >>
  metis_tac[ZN_order_test_1]);

(* Theorem: 1 < m /\ 0 < k ==> ((ordz m n = k) <=>
   (k divides phi m) /\ (n ** k MOD m = 1) /\ !j. 0 < j /\ j < k /\ j divides (phi m) ==> n ** j MOD m <> 1) *)
(* Proof:
   If part: ordz m n = k ==> (k divides phi m) /\
            (n ** k MOD m = 1) /\ !j. 0 < j /\ j < k /\ j divides (phi m) ==> n ** j MOD m <> 1)
      This is to show:
      (1) (ordz m n) divides phi m, true    by ZN_order_divides_phi, 1 < m.
      (2) n ** (ordz m n) MOD m = 1, true   by ZN_order_property, 1 < m.
      (3) !j. 0 < j /\ j < (ordz m n) /\ j divides (phi m) ==> n ** j MOD m <> 1)
          This is true                      by ZN_order_minimal, 1 < m.
   Only-if part: (k divides phi m) /\ (n ** k MOD m = 1) /\
                 !j. 0 < j /\ j < k /\ j divides (phi m) ==> n ** j MOD m <> 1) ==> ordz m n = k
      Note the conditions give:
      !j. 0 < j /\ j < k /\ ~(j divides phi m)
          ==> (ordz m n = k) \/ n ** j MOD m <> 1    by ZN_order_test_propery
      Combining both implications,
      !j. 0 < j /\ j < k  ==> n ** j MOD m <> 1
      Thus ordz m n = k                     by ZN_order_test_1
*)
val ZN_order_test_3 = store_thm(
  "ZN_order_test_3",
  ``!m n k. 1 < m /\ 0 < k ==>
     ((ordz m n = k) <=>
      (k divides phi m) /\ (n ** k MOD m = 1) /\ !j. 0 < j /\ j < k /\ j divides (phi m) ==> n ** j MOD m <> 1)``,
  rw[EQ_IMP_THM] >-
  rw[ZN_order_divides_phi] >-
  rw[ZN_order_property] >-
  rw[ZN_order_minimal] >>
  `!j. 0 < j /\ j < k /\ ~(j divides phi m) ==>
       (ordz m n = k) \/ n ** j MOD m <> 1` by rw[ZN_order_test_propery] >>
  metis_tac[ZN_order_test_1]);

(* Theorem: 1 < m ==> (ordz m n = k <=> n ** k MOD m = 1 /\
           !j. 0 < j /\ j < (if k = 0 then m else k) ==> n ** j MOD m <> 1) *)
(* Proof:
   If k = 0,
      Note n ** 0 MOD m
         = 1 MOD m                       by EXP_0
         = 1                             by ONE_MOD, 1 < m
      The result follows                 by ZN_order_eq_0_test
   If k <> 0, the result follows         by ZN_order_test_1
*)
val ZN_order_test_4 = store_thm(
  "ZN_order_test_4",
  ``!m n k. 1 < m ==> ((ordz m n = k) <=> ((n ** k MOD m = 1) /\
    !j. 0 < j /\ j < (if k = 0 then m else k) ==> n ** j MOD m <> 1))``,
  rpt strip_tac >>
  (Cases_on `k = 0` >> simp[]) >| [
    `n ** 0 MOD m = 1` by rw[EXP_0] >>
    metis_tac[ZN_order_eq_0_test],
    rw[ZN_order_test_1]
  ]);

(* ------------------------------------------------------------------------- *)
(* ZN Homomorphism                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < m /\ x IN (ZN n).carrier ==> x MOD m IN (ZN m).carrier *)
(* Proof:
   Expand by definitions, this is to show:
   x < n ==> x MOD m < m, true by MOD_LESS.
*)
val ZN_to_ZN_element = store_thm(
  "ZN_to_ZN_element",
  ``!n m x. 0 < m /\ x IN (ZN n).carrier ==> x MOD m IN (ZN m).carrier``,
  rw[ZN_def]);

(* Theorem: 0 < n /\ m divides n ==> GroupHomo (\x. x MOD m) (ZN n).sum (ZN m).sum *)
(* Proof:
   Note 0 < m                     by ZERO_DIVIDES, 0 < n
   Expand by definitions, this is to show:
      x < n /\ x' < n ==> (x + x') MOD n MOD m = (x MOD m + x' MOD m) MOD m
     (x + x') MOD n MOD m
   = (x + x') MOD m               by DIVIDES_MOD_MOD, 0 < n
   = (x MOD m + x' MOD m) MOD m   by MOD_PLUS, 0 < m
*)
val ZN_to_ZN_sum_group_homo = store_thm(
  "ZN_to_ZN_sum_group_homo",
  ``!n m. 0 < n /\ m divides n ==> GroupHomo (\x. x MOD m) (ZN n).sum (ZN m).sum``,
  rpt strip_tac >>
  `0 < m` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
  rw[ZN_def, GroupHomo_def, DIVIDES_MOD_MOD, MOD_PLUS]);

(* Theorem: 0 < n /\ m divides n ==> MonoidHomo (\x. x MOD m) (ZN n).prod (ZN m).prod *)
(* Proof:
   Note 0 < m                           by ZERO_DIVIDES, 0 < n
   Expand by definitions, this is to show:
   (1) x < n /\ x' < n ==> (x * x') MOD n MOD m = (x MOD m * x' MOD m) MOD m
         (x * x') MOD n MOD m
       = (x * x') MOD m                 by DIVIDES_MOD_MOD, 0 < n
       = (x MOD m * x' MOD m) MOD m     by MOD_TIMES2, 0 < m
   (2) 0 < m /\ m <> 1 ==> 1 < m, trivially true.
*)
val ZN_to_ZN_prod_monoid_homo = store_thm(
  "ZN_to_ZN_prod_monoid_homo",
  ``!n m. 0 < n /\ m divides n ==> MonoidHomo (\x. x MOD m) (ZN n).prod (ZN m).prod``,
  rpt strip_tac >>
  `0 < m` by metis_tac[ZERO_DIVIDES, NOT_ZERO] >>
  rw[ZN_def, MonoidHomo_def, times_mod_def, DIVIDES_MOD_MOD] >>
  fs[DIVIDES_ONE]);

(* Theorem: 0 < n /\ m divides n ==> RingHomo (\x. x MOD m) (ZN n) (ZN m) *)
(* Proof:
   By RingHomo_def, this is to show:
   (1) x IN (ZN n).carrier ==> x MOD m IN (ZN m).carrier
       Note 0 < m                           by ZERO_DIVIDES, 0 < n
       Hence true                           by ZN_to_ZN_element, 0 < m.
   (2) GroupHomo (\x. x MOD m) (ZN n).sum (ZN m).sum, true by ZN_to_ZN_sum_group_homo.
   (3) MonoidHomo (\x. x MOD m) (ZN n).prod (ZN m).prod, true by ZN_to_ZN_prod_monoid_homo.
*)
val ZN_to_ZN_ring_homo = store_thm(
  "ZN_to_ZN_ring_homo",
  ``!n m. 0 < n /\ m divides n ==> RingHomo (\x. x MOD m) (ZN n) (ZN m)``,
  rw[RingHomo_def] >-
  metis_tac[ZN_to_ZN_element, ZERO_DIVIDES, NOT_ZERO] >-
  rw[ZN_to_ZN_sum_group_homo] >>
  rw[ZN_to_ZN_prod_monoid_homo]);

(* ------------------------------------------------------------------------- *)
(* A Ring from Sets.                                                         *)
(* ------------------------------------------------------------------------- *)

(* The Ring from Group (symdiff_set) and Monoid (set_inter). *)
val symdiff_set_inter_def = Define`
  symdiff_set_inter = <| carrier := UNIV;
                             sum := symdiff_set;
                            prod := set_inter |>
`;
(* Evaluation is given later in symdiff_eval. *)

(* Theorem: symdiff_set_inter is a Ring. *)
(* Proof: check definitions.
   For the distribution law:
   x INTER (y SYM z) = (x INTER y) SYM (x INTER z)
   first verify by Venn Diagram.
*)
Theorem symdiff_set_inter_ring:
  Ring symdiff_set_inter
Proof
  rw_tac std_ss[Ring_def, symdiff_set_inter_def] >>
  rw[symdiff_set_def, set_inter_def] >>
  rw[EXTENSION, symdiff_def] >>
  metis_tac[]
QED

(* Theorem: symdiff UNIV UNIV = EMPTY` *)
(* Proof: by definition. *)
val symdiff_univ_univ_eq_empty = store_thm(
  "symdiff_univ_univ_eq_empty",
  ``symdiff UNIV UNIV = EMPTY``,
  rw[symdiff_def]);

(* Note: symdiff_set_inter has carrier infinite, but characteristics 2. *)

(* Theorem: char symdiff_set_inter = 2 *)
(* Proof:
   By definition, and making use of FUNPOW_2.
   First to show:
   ?n. 0 < n /\ (FUNPOW (symdiff univ(:'a)) n {} = {})
   Put n = 2, and apply FUNPOW_2 and symdiff_def.
   Second to show:
   0 < n /\ FUNPOW (symdiff univ(:'a)) n {} = {} /\
   !m. m < n ==> ~(0 < m) \/ FUNPOW (symdiff univ(:'a)) m {} <> {} ==> n = 2
   By contradiction. Assume n <> 2, then n < 2 or 2 < n.
   If n < 2, then 0 < n < 2 means n = 1,
   but FUNPOW (symdiff univ(:'a)) 1 {} = symdiff univ(:'a) {} = univ(:'a) <> {}, a contradiction.
   If 2 < n, then FUNPOW (symdiff univ(:'a)) 2 {} <> {}, contradicting FUNPOW_2 and symdiff_def.
*)
Theorem symdiff_set_inter_char:
  char symdiff_set_inter = 2
Proof
  simp[char_def, order_def, period_def, symdiff_set_inter_def,
       monoid_exp_def, symdiff_set_def, set_inter_def] >>
  `FUNPOW (symdiff univ(:'a)) 2 {} = {}` by rw[FUNPOW_2, symdiff_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  rw[] >>
  `~(n < 2) /\ ~(2 < n)` suffices_by decide_tac >>
  spose_not_then strip_assume_tac >>
  ‘~(2 < n)’ by metis_tac[DECIDE “2 <> 0”] >> gs[] >>
  `n = 1` by decide_tac >>
  gs[symdiff_def]
QED

(* Theorem: evaluation for symdiff dields. *)
(* Proof: by definitions. *)
Theorem symdiff_eval[compute]:
  ((symdiff_set).carrier = UNIV) /\
  (!x y. (symdiff_set).op x y = (x UNION y) DIFF (x INTER y)) /\
  ((symdiff_set).id = EMPTY)
Proof
  rw_tac std_ss[symdiff_set_def, symdiff_def]
QED
(*
EVAL ``order (symdiff_set) EMPTY``;
> val it = |- order symdiff_set {} = 1 : thm
*)

(* ------------------------------------------------------------------------- *)
(* Order Computation using a WHILE loop                                      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* A Small Example of WHILE loop invariant                                   *)
(* ------------------------------------------------------------------------- *)

(* Pseudocode: search through all indexes from 1.

Input: m, n with 1 < m, 0 < n
Output: ordz m n, the least index j such that (n ** j = 1) (mod m)

if ~(coprime m n) return 0    // initial check
// For coprime m n, search the least index j such that (n ** j = 1) (mod m).
// Search upwards for least index j
j <- 1                        // initial index
while ((n ** i) MOD m <> 1) j <- j + 1  // increment j
return j                      // the least index j.

*)

(* Compute ordz m n = order (ZN m).prod n = ordz m n *)
val compute_ordz_def = Define`
    compute_ordz m n =
         if m = 0 then ordz 0 n
    else if m = 1 then 1 (* ordz 1 n = 1 *)
    else if coprime m n then
         WHILE (\i. (n ** i) MOD m <> 1) SUC 1  (* i = 1, WHILE (n ** i (MOD m) <> 1) i <- SUC i) *)
    else 0  (* ordz m n = 0 when ~(coprime m n) *)
`;

(* Examples:
> EVAL ``compute_ordz 10 3``; --> 4
> EVAL ``compute_ordz 10 4``; --> 0
> EVAL ``compute_ordz 10 7``; --> 4
> EVAL ``compute_ordz 10 19``; --> 2

> EVAL ``phi 10``; --> 4

Indeed, (ordz m n) is a divisor of (phi m).
Since phi(10) = 4, ordz 10 n is a divisior of 4.

> EVAL ``compute_ordz 1 19``; --> 1;

> EVAL ``MAP (compute_ordz 7) [1 .. 6]``; = [1; 3; 6; 3; 6; 2]
> EVAL ``MAP (combin$C compute_ordz 10) [2 .. 13]``; = [0; 1; 0; 0; 0; 6; 0; 1; 0; 2; 0; 6]
  shows that, in decimals (base 10), 1/2 is finite, 1/3 has period 1, 1/7 has period 6,
                                     1/9 has period 1, 1/11 has period 2, 1/13 has period 6.
*)

(*
> EVAL ``WHILE (\i. i <= 4) SUC 1``;
val it = |- WHILE (\i. i <= 4) SUC 1 = 5: thm
*)

(*
For WHILE Guard Cmd,
we want to show:
   {Pre-condition} WHILE Guard Cmd {Post-condition}

> WHILE_RULE;
val it = |- !R B C. WF R /\ (!s. B s ==> R (C s) s) ==>
     HOARE_SPEC (\s. P s /\ B s) C P ==>
     HOARE_SPEC P (WHILE B C) (\s. P s /\ ~B s): thm

> HOARE_SPEC_DEF;
val it = |- !P C Q. HOARE_SPEC P C Q <=> !s. P s ==> Q (C s): thm
*)

(* Theorem: (!x. Invariant x /\ Guard x ==> f (Cmd x) < f x) /\
            (!x. Precond x ==> Invariant x) /\
            (!x. Invariant x /\ ~Guard x ==> Postcond x) /\
            HOARE_SPEC (\x. Invariant x /\ Guard x) Cmd Invariant ==>
            HOARE_SPEC Precond (WHILE Guard Cmd) Postcond *)
(* Proof:
   By HOARE_SPEC_DEF, change the goal to show:
      !s. Invariant s ==> Postcond (WHILE Guard Cmd s)
   By complete induction on (f s).
   After rewrite by WHILE, this is to show:
      Postcond (if Guard s then WHILE Guard Cmd (Cmd s) else s)
   If Guard s,
      With Invariant s,
       ==> Postcond (WHILE Guard Cmd (Cmd s))   by induction hypothesis
   If ~(Guard s),
      With Invariant s,
       ==> Postcond s                           by given
*)
val WHILE_RULE_PRE_POST = store_thm(
  "WHILE_RULE_PRE_POST",
  ``(!x. Invariant x /\ Guard x ==> f (Cmd x) < f x) /\
   (!x. Precond x ==> Invariant x) /\
   (!x. Invariant x /\ ~Guard x ==> Postcond x) /\
   HOARE_SPEC (\x. Invariant x /\ Guard x) Cmd Invariant ==>
   HOARE_SPEC Precond (WHILE Guard Cmd) Postcond``,
  simp[HOARE_SPEC_DEF] >>
  rpt strip_tac >>
  `!s. Invariant s ==> Postcond (WHILE Guard Cmd s)` suffices_by metis_tac[] >>
  Q.UNDISCH_THEN `Precond s` (K ALL_TAC) >>
  rpt strip_tac >>
  completeInduct_on `f s` >>
  rpt strip_tac >>
  fs[PULL_FORALL] >>
  first_x_assum (qspec_then `f` assume_tac) >>
  rfs[] >>
  ONCE_REWRITE_TAC[WHILE] >>
  Cases_on `Guard s` >>
  simp[]);
(* Michael's version:
val WHILE_RULE_PRE_POST = Q.store_thm(
  "WHILE_RULE_PRE_POST",
  `(!x. Invariant x /\ Guard x ==> f (Cmd x) < f x) /\
   (!x. Precond x ==> Invariant x) /\
   (!x. Invariant x /\ ~Guard x ==> Postcond x) /\
   HOARE_SPEC (\x. Invariant x /\ Guard x) Cmd Invariant ==>
   HOARE_SPEC Precond (WHILE Guard Cmd) Postcond`,
  simp[whileTheory.HOARE_SPEC_DEF] >>
  rpt strip_tac >>
  `!s. Invariant s ==> Postcond (WHILE Guard Cmd s)`
     suffices_by metis_tac[] >>
  Q.UNDISCH_THEN `Precond s` (K ALL_TAC) >>
  rpt strip_tac >>
  completeInduct_on `f s` >>
  rpt strip_tac >>
  fs[PULL_FORALL] >>
  first_x_assum (qspec_then `f` assume_tac) >>
  rfs[] >>
  ONCE_REWRITE_TAC[WHILE] >>
  Cases_on `Guard s` >> simp[]
)
*)

(* Theorem: 1 < m /\ coprime m n ==>
            HOARE_SPEC (\i. 0 < i /\ i <= ordz m n)
                       (WHILE (\i. (n ** i) MOD m <> 1) SUC)
                       (\i. i = ordz m n) *)
(* Proof:
   By WHILE_RULE_PRE_POST, this is to show:
      ?Invariant f. (!x. (\i. 0 < i /\ i <= ordz m n) x ==> Invariant x) /\
                    (!x. Invariant x /\ (\i. (n ** i) MOD m <> 1) x ==> f (SUC x) < f x) /\
                    (!x. Invariant x /\ ~(\i. (n ** i) MOD m <> 1) x ==> (\i. i = ordz m n) x) /\
                    HOARE_SPEC (\x. Invariant x /\ (\i. (n ** i) MOD m <> 1) x) SUC Invariant
   By looking at the first requirement, and peeking at the second,
   let Invariant = \i. 0 < i /\ i <= ordz m n, f = \i. ordz m n - i.
   This is to show:
   (1) 1 < m /\ coprime m n /\ 0 < x /\ x <= ordz m n /\ n ** x MOD m <> 1 ==> 0 < ordz m n - x
       If x = ordz m n, then this is true                  by ZN_coprime_order_alt
       Otherwise, x <> ordz m n, hence 0 < ordz m n - x    by arithmetic
   (2) 1 < m /\ coprime m n /\ 0 < x /\ x <= ordz m n /\ n ** x MOD m = 1 ==> x = ordz m n
       If x = ordz m n, then this is true trivially.
       Otherwise, x <> ordz m n,
       or x < ordz m n, and 0 < m, but n ** x MOD m = 1, contradicts  ZN_order_minimal.
   (3) 1 < m /\ coprime m n ==>
       HOARE_SPEC (\x. (0 < x /\ x <= ordz m n) /\ n ** x MOD m <> 1) SUC (\i. 0 < i /\ i <= ordz m n)
       By HOARE_SPEC_DEF, this is to show:
          1 < m /\ coprime m n /\ 0 < x /\ x <= ordz m n /\ n ** x MOD m <> 1 ==> SUC x <= ordz m n
       or 1 < m /\ coprime m n /\ 0 < x /\ x <= ordz m n /\ n ** x MOD m <> 1 ==> x < ordz m n
       By contradiction, suppose x = ordz m n.
       Then n ** x MOD m = 1, a contradiction         by ZN_coprime_order_alt, 1 < m
*)
val compute_ordz_hoare = store_thm(
  "compute_ordz_hoare",
  ``!m n. 1 < m /\ coprime m n ==>
         HOARE_SPEC (\i. 0 < i /\ i <= ordz m n)
                    (WHILE (\i. (n ** i) MOD m <> 1) SUC)
                    (\i. i = ordz m n)``,
  rpt strip_tac >>
  irule WHILE_RULE_PRE_POST >>
  qexists_tac `\i. 0 < i /\ i <= ordz m n` >>
  qexists_tac `\i. ordz m n - i` >>
  rw[] >| [
    Cases_on `x = ordz m n` >| [
      rw[] >>
      rfs[ZN_coprime_order_alt],
      decide_tac
    ],
    Cases_on `x = ordz m n` >-
    simp[] >>
    rfs[] >>
    `x < ordz m n /\ 0 < m` by decide_tac >>
    metis_tac[ZN_order_minimal],
    rw[HOARE_SPEC_DEF] >>
    `x < ordz m n` suffices_by decide_tac >>
    spose_not_then strip_assume_tac >>
    `x = ordz m n` by decide_tac >>
    rw[] >>
    rfs[ZN_coprime_order_alt]
  ]);
(* Michael's version:
val compute_ordz_hoare = prove(
  ``1 < m /\ coprime m n ==>
    HOARE_SPEC
      (\i. 0 < i /\ i <= ordz m n)
               (WHILE (\i. (n ** i) MOD m <> 1) SUC)
      (\i. i = ordz m n)``,
  strip_tac >>
  irule WHILE_RULE_PRE_POST >>
  qexists_tac `\i. 0 < i /\ i <= ordz m n` >>
  qexists_tac `\i. ordz m n - i` >>
  rw[] >| [
    (* Case 1 *)
    reverse (Cases_on `x = ordz m n`) >- decide_tac >>
    rw[] >>
    rfs[ZN_coprime_order_alt],

    (* Case 2 *)
    Cases_on `x = ordz m n` >- simp[] >>
    rfs[] >>
    `x < ordz m n /\ 0 < m` by decide_tac >>
    metis_tac[ZN_order_minimal],

    (* Case 3 *)
    rw[HOARE_SPEC_DEF] >>
    `x < ordz m n` suffices_by decide_tac >>
    spose_not_then assume_tac >>
    `x = ordz m n` by decide_tac >> rw[] >>
    rfs[ZN_coprime_order_alt]
  ]);
*)

(*
val compute_ordz_hoare =
   |- 1 < m /\ coprime m n ==> HOARE_SPEC (\i. 0 < i /\ i <= ordz m n)
      (WHILE (\i. (n ** i) MOD m <> 1) SUC) (\i. i = ordz m n): thm

SIMP_RULE (srw_ss()) [HOARE_SPEC_DEF] compute_ordz_hoare;
val it = |- 1 < m /\ coprime m n ==>
            !i. 0 < i /\ i <= ordz m n ==> (WHILE (\i. (n ** i) MOD m <> 1) SUC i = ordz m n): thm
*)

(* Theorem: 1 < m /\ coprime m n ==>
            !j. 0 < j /\ j <= ordz m n ==> (WHILE (\i. (n ** i) MOD m <> 1) SUC j = ordz m n) *)
(* Proof:
   By compute_ordz_hoare, we have the loop-invariant:
   HOARE_SPEC (\i. 0 < i /\ i <= ordz m n)
              (WHILE (\i. (n ** i) MOD m <> 1) SUC)
              (\i. i = ordz m n)
   Let Px = \i. 0 < i /\ i <= ordz m n                   be the pre-condition
       Cx = WHILE (\i. (n ** i) MOD m <> 1) SUC   be the command body
       Qx = \i. i = ordz m n                             be the post-condition
   ==> HOARE_SPEC Px Cx Qx                               by above
   Apply HOARE_SPEC_DEF, |- HOARE_SPEC P C Q <=> !s. P s ==> Q (C s)
   Thus !j. P j ==> Qx (Cx j)
     or !j. 0 < j /\ j <= ordz m n ==>
        (WHILE (\i. (n ** i) MOD m <> 1) SUC j = ordz m n)
*)
val compute_ordz_by_while = prove(
  ``!m n. 1 < m /\ coprime m n ==>
   !j. 0 < j /\ j <= ordz m n ==> (WHILE (\i. (n ** i) MOD m <> 1) SUC j = ordz m n)``,
  rpt strip_tac >>
  `HOARE_SPEC
      (\i. 0 < i /\ i <= ordz m n)
      (WHILE (\i. (n ** i) MOD m <> 1) SUC)
      (\i. i = ordz m n)` by rw[compute_ordz_hoare] >>
  fs[HOARE_SPEC_DEF]);

(* ------------------------------------------------------------------------- *)
(* Correctness of computing ordz m n.                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: compute_ordz 0 n = ordz 0 n *)
(* Proof: by compute_ordz_def *)
val compute_ordz_0 = store_thm(
  "compute_ordz_0",
  ``!n. compute_ordz 0 n = ordz 0 n``,
  rw[compute_ordz_def]);

(* Theorem: compute_ordz 1 n = 1 *)
(* Proof: by compute_ordz_def *)
val compute_ordz_1 = store_thm(
  "compute_ordz_1",
  ``!n. compute_ordz 1 n = 1``,
  rw[compute_ordz_def]);

(* Theorem: compute_ordz m n = ordz m n *)
(* Proof:
   If m = 0,
      Then compute_ordz 0 n = ordz 0 n     by compute_ordz_0
   If m = 1,
      Then compute_ordz 1 n = 1            by compute_ordz_1
                            = ordz 1 n     by ZN_order_mod_1
   If m <> 0, m <> 1,
      Then 1 < m                           by arithmetic
      If ordz m n = 0,
         Then ~coprime m n                 by ZN_order_eq_0
              compute_ordz m n
            = 0                            by compute_ordz_def
            = ordz m n                     by ordz m n = 0
      If ordz m n <> 0,
         Then coprime m n                  by ZN_order_eq_0
          and 1 <= ordz m n                by arithmetic
              compute_ordz m n
            = WHILE (\i. (n ** i) MOD m <> 1) SUC 1   by compute_ordz_def
            = ordz m n                                       by compute_ordz_by_while, put j = 1.
*)
val compute_ordz_eqn = store_thm(
  "compute_ordz_eqn",
  ``!m n. compute_ordz m n = ordz m n``,
  rpt strip_tac >>
  Cases_on `m = 0` >-
  rw[compute_ordz_0] >>
  `0 < m` by decide_tac >>
  Cases_on `m = 1` >-
  rw[compute_ordz_1, ZN_order_mod_1] >>
  Cases_on `ordz m n = 0` >| [
    `~coprime m n` by rw[GSYM ZN_order_eq_0] >>
    rw[compute_ordz_def],
    `coprime m n` by metis_tac[ZN_order_eq_0] >>
    `1 < m` by decide_tac >>
    rw[compute_ordz_def, compute_ordz_by_while]
  ]);

(* Theorem: order (times_mod m) n = compute_ordz m n *)
(* Proof: by compute_ordz_eqn *)
val ordz_eval = store_thm(
  "ordz_eval[compute]",
  ``!m n. order (times_mod m) n = compute_ordz m n``,
  rw[ZN_eval, compute_ordz_eqn]);
(* Put in computeLib for simplifier. *)

(*
> EVAL ``ordz 7 10``;
val it = |- ordz 7 10 = 6: thm
*)

(* ------------------------------------------------------------------------- *)
(* Integer Ring Documentation                                                *)
(* ------------------------------------------------------------------------- *)
(* Overloads:
   Z*      = Z_ideal
*)
(* Definitions and Theorems (# are exported):

   Integer Ring:
   Z_add_def             |- Z_add = <|carrier := univ(:int); op := (\x y. x + y); id := 0|>
   Z_mult_def            |- Z_mult = <|carrier := univ(:int); op := (\x y. x * y); id := 1|>
   Z_def                 |- Z = <|carrier := univ(:int); sum := Z_add; prod := Z_mult|>

   Z_add_group           |- Group Z_add
   Z_add_abelian_group   |- AbelianGroup Z_add
   Z_mult_monoid         |- Monoid Z_mult
   Z_mult_abelian_monoid |- AbelianMonoid Z_mult
   Z_ring                |- Ring

   Ideals in Integer Ring:
   Z_multiple_def        |- !n. Z_multiple n = {&n * z | z IN univ(:int)}
   Z_ideal_def           |- !n. Z* n = <|carrier := Z_multiple n;
                                             sum := <|carrier := Z_multiple n; op := Z.sum.op; id := Z.sum.id|>;
                                            prod := <|carrier := Z_multiple n; op := Z.prod.op;
                                              id := Z.prod.id|>
                                        |>

   Z_ideal_sum_group     |- !n. Group (Z* n).sum
   Z_ideal_sum_subgroup  |- !n. (Z* n).sum <= Z.sum
   Z_ideal_sum_normal    |- !n. (Z* n).sum << Z.sum
   Z_ideal_thm           |- !n. Z* n << Z

   Integer Quotient Ring isomorphic to Integer Modulo:
   Z_add_inv               |- !z. z IN Z_add.carrier ==> (Z_add.inv z = -z)
   Z_sum_cogen             |- !n. 0 < n ==> !x. x IN Z.sum.carrier ==>
                              ?y. cogen Z.sum (Z* n).sum (coset Z.sum x (Z* n).sum.carrier) = x + &n * y
   Z_sum_coset_eq          |- !n. 0 < n ==> !p. coset Z.sum p (Z* n).sum.carrier = coset Z.sum (p % &n) (Z* n).sum.carrier
   Z_multiple_less_neg_eq  |- !n x y. 0 < n /\ x < n /\ y < n /\ -&x + &y IN Z_multiple n ==> (x = y)

   Z_ideal_map_element     |- !n j. 0 < n /\ j IN (ZN n).carrier ==> coset Z.sum (&j) (Z* n).sum.carrier IN (Z / Z* n).carrier
   Z_ideal_map_group_homo  |- !n. 0 < n ==> GroupHomo (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).sum (Z / Z* n).sum
   Z_ideal_map_monoid_homo |- !n. 0 < n ==> MonoidHomo (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).prod (Z / Z* n).prod
   Z_ideal_map_bij         |- !n. 0 < n ==> BIJ (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).carrier (Z / Z* n).carrier
   Z_quotient_iso_ZN       |- !n. 0 < n ==> RingIso (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n) (Z / Z* n)

   Integer as Euclidean Ring:
   Z_euclid_ring           |- EuclideanRing Z (Num o ABS)
   Z_principal_ideal_ring  |- PrincipalIdealRing Z
*)

(* ------------------------------------------------------------------------- *)
(* Integer Ring                                                              *)
(* ------------------------------------------------------------------------- *)

(* Integer Additive Group *)
val Z_add_def = Define `
  Z_add = <| carrier := univ(:int);
                  op := \(x:int) (y:int). x + y;
                  id := (0:int)
           |>
`;

(* Integer Multiplicative Monoid *)
val Z_mult_def = Define `
  Z_mult = <| carrier := univ(:int);
                   op := \(x:int) (y:int). x * y;
                   id := (1:int)
            |>
`;

(* Integer Ring *)
val Z_def = Define `
  Z = <| carrier := univ(:int);
             sum := Z_add;
            prod := Z_mult
       |>
`;

(* Theorem: Z_add is a Group. *)
(* Proof: check group axioms:
   (1) x + y IN univ(:int), true.
   (2) x + y + z = x + (y + z), true by INT_ADD_ASSOC.
   (3) 0 IN univ(:int), true.
   (4) 0 + x = x, true by INT_ADD_LID.
   (5) !x. x IN univ(:int) ==> ?y. y IN univ(:int) /\ (y + x = 0)
       Let y = -x, apply INT_ADD_LINV.
*)
val Z_add_group = store_thm(
  "Z_add_group",
  ``Group Z_add``,
  rw_tac std_ss[Z_add_def, group_def_alt] >| [
    rw[],
    rw[INT_ADD_ASSOC],
    rw[],
    rw[],
    qexists_tac `-x` >>
    rw[]
  ]);

(* Theorem: Z_add is an Abelian Group. *)
(* Proof: by Group Z_add and INT_ADD_COMM. *)
val Z_add_abelian_group = store_thm(
  "Z_add_abelian_group",
  ``AbelianGroup Z_add``,
  rw[AbelianGroup_def, Z_add_group, Z_add_def, INT_ADD_COMM]);

(* Theorem: Z_mult is a Monoid. *)
(* Proof: check monoid axioms:
   (1) x * y IN univ(:int), true.
   (2) x * y * z = x * (y * z), true by INT_MUL_ASSOC.
   (3) 1 IN univ(:int), true.
   (4) 1 * x = x, true by INT_MUL_LID.
   (5) x * 1 = x, true by INT_MUL_RID.
*)
val Z_mult_monoid = store_thm(
  "Z_mult_monoid",
  ``Monoid Z_mult``,
  rw_tac std_ss [Z_mult_def, Monoid_def] >>
  rw[INT_MUL_ASSOC]);

(* Theorem: Z_mult is an Abelian Monoid. *)
(* Proof: by Monoid Z_mult and INT_MUL_COMM. *)
val Z_mult_abelian_monoid = store_thm(
  "Z_mult_abelian_monoid",
  ``AbelianMonoid Z_mult``,
  rw[AbelianMonoid_def, Z_mult_monoid, Z_mult_def, INT_MUL_COMM]);

(* Theorem: Z is a Ring. *)
(* Proof: check ring axioms.
   (1) AbelianGroup Z_add, true by Z_add_abelian_group.
   (2) AbelianMonoid Z_mult, true by Z_mult_abelian_monoid.
   (3) Z_add.carrier = univ(:int), true by Z_add_def.
   (4) Z_mult.carrier = univ(:int), true by Z_mult_def.
   (5) Z_mult.op x (Z_add.op y z) = Z_add.op (Z_mult.op x y) (Z_mult.op x z)
       or x * (y + z) = x * y + x * z, true by INT_LDISTRIB.
*)
val Z_ring = store_thm(
  "Z_ring",
  ``Ring Z``,
  rw_tac std_ss [Ring_def, Z_def] >| [
    rw[Z_add_abelian_group],
    rw[Z_mult_abelian_monoid],
    rw[Z_add_def],
    rw[Z_mult_def],
    rw[Z_add_def, Z_mult_def, INT_LDISTRIB]
  ]);

(* ------------------------------------------------------------------------- *)
(* Ideals in Integer Ring                                                    *)
(* ------------------------------------------------------------------------- *)

(* Integer Multiples *)
val Z_multiple_def = Define `Z_multiple (n:num) = {&n * z | z IN univ(:int)}`;

(* Integer Ring Ideals are multiples *)
val Z_ideal_def = Define `
  Z_ideal (n:num) = <| carrier := Z_multiple n;
                           sum := <| carrier := Z_multiple n; op := Z.sum.op; id := Z.sum.id |>;
                          prod := <| carrier := Z_multiple n; op := Z.prod.op; id := Z.prod.id |>
                     |>
`;

(* set overloading *)
val _ = overload_on ("Z*", ``Z_ideal``);

(* Theorem: Group (Z* n).sum *)
(* Proof: check group axioms:
   (1) x + y IN Z_multiple n
       &n * x' + &n * y' = &n * (x' + y') by INT_LDISTRIB, hence true.
   (2) x + y + z = x + (y + z)
       Since t IN Z_multiple n ==> t IN univ(:int),
       this is true by INT_ADD_ASSOC.
   (3) 0 IN Z_multiple n
       true by INT_MUL_RZERO.
   (4) 0 + x = x
       true by INT_ADD_LID.
   (5) ?y. y IN Z_multiple n /\ (y + x = 0)
       Since x = &n * x'
       Let y = &n * (-x')
       Then y IN Z_multiple n,
       y + x = &n * (-x' + x') = 0   by INT_LDISTRIB, INT_ADD_LINV, hence true.
*)
val Z_ideal_sum_group = store_thm(
  "Z_ideal_sum_group",
  ``!n. Group (Z* n).sum``,
  rpt strip_tac >>
  `!t. t IN Z_multiple n ==> t IN univ(:int)` by rw[Z_multiple_def] >>
  rw_tac std_ss[group_def_alt, Z_ideal_def, Z_def, Z_add_def] >| [
    `!t. t IN Z_multiple n <=> ?(t':int). t = &n * t'` by rw[Z_multiple_def] >>
    metis_tac[INT_LDISTRIB],
    rw[INT_ADD_ASSOC],
    `!t. t IN Z_multiple n <=> ?(t':int). t = &n * t'` by rw[Z_multiple_def] >>
    metis_tac[INT_MUL_RZERO],
    rw[],
    `!t. t IN Z_multiple n <=> ?(t':int). t = &n * t'` by rw[Z_multiple_def] >>
    `?x'. x = &n * x'` by metis_tac[] >>
    qexists_tac `&n * (-x')` >>
    `-x' IN univ(:int)` by rw[] >>
    `&n * -x' + &n * x' = &n * (-x' + x')` by rw[INT_LDISTRIB] >>
    `_ = 0` by rw[INT_ADD_LINV] >>
    metis_tac[]
  ]);

(* Theorem: Monoid (Z* n).prod *)
(* Not true: 1 IN Z_multiple n is FALSE. *)
(* Note: Ideal is not a sub-ring. *)

(* Theorem: (Z* n).sum <= Z.sum *)
(* Proof:
   (1) Group (Z* n).sum     true by Z_ideal_sum_group
   (2) Group Z.sum          true by Z_ring, Ring_def
   (3) (Z* n).sum.carrier SUBSET Z.sum.carrier   true by definitions
   (4) (Z* n).sum.op x y = Z.sum.op x y          true by Z_ideal_def
*)
val Z_ideal_sum_subgroup = store_thm(
  "Z_ideal_sum_subgroup",
  ``!n. (Z* n).sum <= Z.sum``,
  rw_tac std_ss[Subgroup_def] >| [
    rw[Z_ideal_sum_group],
    rw[Z_ring, Ring_def, AbelianGroup_def],
    rw[Z_ideal_def, Z_def, Z_add_def],
    rw[Z_ideal_def]
  ]);

(* Theorem: (Z* n).sum << Z.sum *)
(* Proof:
   (1) (Z* n).sum <= Z.sum
       true by Z_ideal_sum_subgroup.
   (2) !a. a IN Z.sum.carrier ==> coset Z.sum a (Z* n).sum.carrier = right_coset Z.sum (Z* n).sum.carrier a
       i.e. IMAGE (\z. a + z) (Z_multiple n) = IMAGE (\z. z + a) (Z_multiple n)
       true by INT_ADD_COMM.
*)
val Z_ideal_sum_normal = store_thm(
  "Z_ideal_sum_normal",
  ``!n. (Z* n).sum << Z.sum``,
  rw[normal_subgroup_alt, coset_def, right_coset_def] >| [
    rw[Z_ideal_sum_subgroup],
    pop_assum mp_tac >>
    rw_tac std_ss[Z_ideal_def, Z_def, Z_add_def] >>
    rw[INT_ADD_COMM]
  ]);

(* Theorem: Z* n is an ideal of Z *)
(* Proof:
   (1) (Z* n).sum <= Z.sum
       true by Z_ideal_sum_subgroup.
   (2) x IN Z_multiple n ==> x * y IN Z_multiple n
       (&n * x') * y = &n * (x' * y)  by INT_MUL_ASSOC, hence true.
   (3) x IN Z_multiple n ==> y * x IN Z_multiple n
       y * (&n * x') = &n * (y * x')  by INT_MUL_ASSOC, INT_MUL_COMM, hence true.
*)
val Z_ideal_thm = store_thm(
  "Z_ideal_thm",
  ``!n. (Z* n) << Z``,
  rw_tac std_ss[ideal_def, Z_ideal_def, Z_def, Z_mult_def] >| [
    `Z.sum = Z_add` by rw[Z_def] >>
    `(Z* n).sum = <|carrier := Z_multiple n; op := Z_add.op; id := Z_add.id|>` by rw[Z_ideal_def] >>
    metis_tac[Z_ideal_sum_subgroup],
    `!t. t IN Z_multiple n <=> ?(t':int). t = &n * t'` by rw[Z_multiple_def] >>
    metis_tac[INT_MUL_ASSOC],
    `!t. t IN Z_multiple n <=> ?(t':int). t = &n * t'` by rw[Z_multiple_def] >>
    metis_tac[INT_MUL_ASSOC, INT_MUL_COMM]
  ]);

(* ------------------------------------------------------------------------- *)
(* Integer Quotient Ring isomorphic to Integer Modulo                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Z_add.inv z = -z *)
(* Proof:
   Since -z + z = 0,
   this follows by group_linv_unique.
*)
val Z_add_inv = store_thm(
  "Z_add_inv",
  ``!z. z IN Z_add.carrier ==> (Z_add.inv z = -z)``,
  rpt strip_tac >>
  `Group Z_add` by rw[Z_add_group] >>
  `-z IN Z_add.carrier /\ (Z_add.op (-z) z = Z_add.id)` by rw[Z_add_def] >>
  metis_tac[group_linv_unique]);

(* Theorem: cogen Z.sum (Z* n).sum (coset Z.sum x (Z* n).sum.carrier) = x + &n * y  for some y. *)
(* Proof:
   (Z* n).sum <= Z.sum   by Z_ideal_sum_subgroup
   hence  (coset Z.sum x (Z* n).sum.carrier) IN CosetPartition Z.sum (Z* n).sum  by definitions
   By cogen_def, putting m = cogen Z.sum (Z* n).sum (coset Z.sum x (Z* n).sum.carrier)
         m IN Z.sum.carrier,
   and   coset Z.sum x (Z* n).sum.carrier = coset Z.sum m (Z* n).sum.carrier
   Hence -x + m IN (Z* n).sum.carrier  by subgroup_coset_eq
   or    -x + m IN Z_multiple n        by Z_ideal_def
   or    -x + m = &n * y               by Z_multiple_def
   or    m = x + &n * y
*)
val Z_sum_cogen = store_thm(
  "Z_sum_cogen",
  ``!n. 0 < n ==> !x. x IN Z.sum.carrier ==> ? y:int. cogen Z.sum (Z* n).sum (coset Z.sum x (Z* n).sum.carrier) = x + &n * y``,
  rpt strip_tac >>
  `(Z* n).sum <= Z.sum` by rw[Z_ideal_sum_subgroup] >>
  `(coset Z.sum x (Z* n).sum.carrier) IN CosetPartition Z.sum (Z* n).sum` by
  (rw[CosetPartition_def, partition_def, inCoset_def] >>
  qexists_tac `x` >>
  rw[EXTENSION] >>
  metis_tac[subgroup_coset_subset]) >>
  `cogen Z.sum (Z* n).sum (coset Z.sum x (Z* n).sum.carrier) IN Z.sum.carrier /\
   (coset Z.sum x (Z* n).sum.carrier = coset Z.sum (cogen Z.sum (Z* n).sum (coset Z.sum x (Z* n).sum.carrier)) (Z* n).sum.carrier)` by rw[cogen_def] >>
  `Z.sum.op (Z.sum.inv x) (cogen Z.sum (Z* n).sum (coset Z.sum x (Z* n).sum.carrier)) IN (Z* n).sum.carrier` by rw[GSYM subgroup_coset_eq] >>
  `Z.sum = Z_add` by rw[Z_def] >>
  `(Z* n).sum.carrier = Z_multiple n` by rw[Z_ideal_def] >>
  qabbrev_tac `m = (cogen Z.sum (Z* n).sum (coset Z.sum x (Z* n).sum.carrier))` >>
  `Z_add.op (- x) m IN Z_multiple n` by metis_tac[Z_add_inv] >>
  `Z_add.op (- x) m = (- x) + m` by rw[Z_add_def] >>
  `!y. y IN Z_multiple n ==> ?k. y = &n * k` by rw[Z_multiple_def] >>
  `?k. -x + m = &n * k` by metis_tac[] >>
  `x + &n * k = x + (-x + m)` by rw[] >>
  `_ = (x + -x) + m` by rw[INT_ADD_ASSOC] >>
  `_ = m` by rw[] >>
  metis_tac[]);

(* Theorem: coset Z.sum p (Z* n).sum.carrier = coset Z.sum (p % &n) (Z* n).sum.carrier *)
(* Proof:
   Since (Z* n).sum <= Z.sum   by Z_ideal_sum_subgroup
   By subgroup_coset_eq, this is to show:
       Z.sum.op (Z.sum.inv (p % &n)) p IN (Z* n).sum.carrier
   or  -(p % &n) + p IN Z_multiple n
     -(p % &n) + p
   = -(p % &n) + ((p / &n) * &n + p % &n)   by INT_DIVISION
   = -(p % &n) + (p % &n + (p / &n) * &n)   by INT_ADD_COMM
   = -(p % &n) + p % &n + (p / &n) * &n     by INT_ADD_ASSOC
   = (p / &n) * &n                          by INT_ADD_LINV, INT_ADD_LID
   = &n * (p / &n)                          by INT_MUL_COMM
   hence in Z_multiple n.
*)
val Z_sum_coset_eq = store_thm(
  "Z_sum_coset_eq",
  ``!n. 0 < n ==> !p. coset Z.sum p (Z* n).sum.carrier = coset Z.sum (p % &n) (Z* n).sum.carrier``,
  rpt strip_tac >>
  `n <> 0` by decide_tac >>
  `&n <> (0 :int)` by rw[INT_INJ] >>
  `(Z* n).sum <= Z.sum` by rw[Z_ideal_sum_subgroup] >>
  `p IN Z.sum.carrier /\ p % &n IN Z.sum.carrier` by rw[Z_def, Z_add_def] >>
  `Z.sum.op (Z.sum.inv (p % &n)) p IN (Z* n).sum.carrier` suffices_by rw[subgroup_coset_eq] >>
  `Z.sum = Z_add` by rw[Z_def] >>
  `Z.sum.op (- (p % &n)) p IN (Z* n).sum.carrier` suffices_by metis_tac[Z_add_inv] >>
  `-(p % &n) + p IN Z_multiple n` suffices_by rw_tac std_ss[Z_def, Z_add_def, Z_ideal_def] >>
  `-(p % &n) + p = -(p % &n) + ((p / &n) * &n + p % &n)` by metis_tac[INT_DIVISION] >>
  `_ = -(p % &n) + (p % &n + (p / &n) * &n)` by rw[INT_ADD_COMM] >>
  `_ = -(p % &n) + p % &n + (p / &n) * &n` by rw[INT_ADD_ASSOC] >>
  `_ = (p / &n) * &n` by rw[INT_ADD_LINV, INT_ADD_LID] >>
  `_ = &n * (p / &n)` by rw[INT_MUL_COMM] >>
  rw[Z_multiple_def]);

(* Theorem: x < n /\ y < n /\ -&x + &y IN Z_multiple n ==> (x = y) *)
(* Proof:
   By Z_multiple_def, this is to show:
      -&x + &y = &n * z ==> x = y
   or  &y = &n * z + &x ==> x = y
   If z = 0,
      &y = &n * z + &x
         = 0 + &x         by INT_MUL_RZERO
         = &x             by INT_ADD_LID
      hence y = x         by INT_INJ
   If z < 0,
      z < -1 + 1          by INT_ADD_LINV, -1 + 1 = 0
   or z <= -1             by INT_LE_LT1
   &n * z <= &n * -1      by INT_LE_MONO
           = - &n         by INT_NEG_RMUL, INT_MUL_RID
   Now
    x < n means &x < &n    by INT_INJ
   i.e. -&n < -&x          by INT_LT_NEG
   Combining inequalities,
      &n * z <= -&n < -&x  by INT_LET_TRANS
      &n * z < 0 - &x      by INT_SUB_LZERO
   or &n * z + &x < 0      by INT_LT_SUB_LADD
   i.e.        &y < 0
   which contradicts ~(y < 0), y being :num.
   If z > 0,
      0 < z
   or 1 - 1 < z            by INT_SUB_REFL
   or 1 < z + 1            by INT_LT_SUB_RADD
   or 1 <= z               by INT_LE_LT1
      &n * 1 <= &n * z     by INT_LE_MONO
          &n <= &n * z     by INT_MUL_RID
     &n + &x <= &y         by INT_LE_RADD
   Now
     &n <= &n + &x
   Combining inequalities
     &n <= &y              by INT_LE_TRANS
      n <= y               by INT_LE
   but this contradicts y < n
*)
val Z_multiple_less_neg_eq = store_thm(
  "Z_multiple_less_neg_eq",
  ``!n x y. 0 < n /\ x < n /\ y < n /\ -&x + &y IN Z_multiple n ==> (x = y)``,
  rw[Z_multiple_def] >>
  `-&x + &y + &x = &n * z + &x` by rw[] >>
  `--&x = &x` by rw[INT_NEGNEG] >>
  `&y = &n * z + &x` by metis_tac[INT_ADD_SUB, int_sub] >>
  Cases_on `z = 0` >| [
    `&y = (&x) :int` by metis_tac[INT_MUL_RZERO, INT_ADD_LID] >>
    metis_tac[INT_INJ],
    Cases_on `z < 0` >| [
      `z < -1 + 1` by rw[INT_ADD_LINV] >>
      `z <= -1` by rw[INT_LE_LT1] >>
      `&n * z <= &n * -1` by rw[INT_LE_MONO] >>
      `&n * z <= - (&n * 1)` by rw[INT_NEG_RMUL] >>
      `&n * z <= - &n` by metis_tac[INT_MUL_RID] >>
      `- &n < - &x` by rw[] >>
      `&n * z < - &x` by metis_tac[INT_LET_TRANS] >>
      `&n * z < 0 - &x` by rw[INT_SUB_LZERO] >>
      `&n * z + &x < 0` by rw[GSYM INT_LT_SUB_LADD] >>
      `y < 0` by metis_tac[INT_LT] >>
      decide_tac,
      `0 <= z` by rw[GSYM INT_NOT_LT] >>
      `0 < z` by metis_tac[INT_LE_LT] >>
      `1 - 1 < z` by rw[INT_SUB_REFL] >>
      `1 < z + 1` by rw[INT_LT_SUB_RADD] >>
      `1 <= z` by rw[INT_LE_LT1] >>
      `&n * 1 <= &n * z` by rw[INT_LE_MONO] >>
      `&n <= &n * z` by metis_tac[INT_MUL_RID] >>
      `&n + &x <= (&y) :int` by rw[INT_LE_RADD] >>
      `&n <= &n + (&x) :int` by rw[] >>
      `&n <= (&y) :int` by metis_tac[INT_LE_TRANS] >>
      `n <= y` by rw[GSYM INT_LE] >>
      decide_tac
    ]
  ]);

(* Theorem: j IN (ZN n).carrier ==> coset Z.sum (&j) (Z* n).sum.carrier IN (Z / Z* n).carrier *)
(* Proof: by definitions,
   this is to show: 0 < n /\ j < n ==>
   ?x. IMAGE (\z. &j + z) (Z_multiple n) = {y | ?z. (y = x + z) /\ z IN Z_multiple n}
   Just take x = &j.
*)
val Z_ideal_map_element = store_thm(
  "Z_ideal_map_element",
  ``!n j. 0 < n /\ j IN (ZN n).carrier ==> coset Z.sum (&j) (Z* n).sum.carrier IN (Z / Z* n).carrier``,
  rw_tac std_ss[quotient_ring_def, coset_def, ZN_def, Z_ideal_def, Z_def, Z_add_def,
     CosetPartition_def, partition_def, inCoset_def, IN_COUNT] >>
  rw[] >>
  qexists_tac `&j` >>
  rw[EXTENSION]);

(* Theorem: GroupHomo (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).sum (Z / Z* n).sum *)
(* Proof: by GroupHomo_def, this is to show
   (1) j IN (ZN n).sum.carrier ==> coset Z.sum (&j) (Z* n).sum.carrier IN (Z / Z* n).sum.carrier
       Since
       (ZN n).sum.carrier = (ZN n).carrier         by Ring_def, and Ring (ZN n)        by ZN_ring
       (Z / Z* n).sum.carrier = (Z / Z* n).carrier by Ring_def, and Ring (Z / (Z* n))  by quotient_ring_ring
       Hence true by Z_ideal_map_element.
   (2) j IN (ZN n).sum.carrier /\ j' IN (ZN n).sum.carrier ==>
       coset Z.sum (&(ZN n).sum.op j j') (Z* n).sum.carrier =
       (Z / Z* n).sum.op (coset Z.sum (&j) (Z* n).sum.carrier) (coset Z.sum (&j') (Z* n).sum.carrier)
       After expanding by definitions, this is to show:
       coset Z.sum (&(ZN n).sum.op j j') (Z* n).sum.carrier =
       coset Z.sum (Z.sum.op (cogen Z.sum (Z* n).sum (coset Z.sum (&j) (Z* n).sum.carrier))
                             (cogen Z.sum (Z* n).sum (coset Z.sum (&j') (Z* n).sum.carrier))) (Z* n).carrier
       Since (Z* n).sum << Z.sum     by Z_ideal_sum_normal
       applying normal_coset_property:
       coset Z.sum (Z.sum.op (cogen Z.sum (Z* n).sum (coset Z.sum (&j) (Z* n).sum.carrier))
                             (cogen Z.sum (Z* n).sum (coset Z.sum (&j') (Z* n).sum.carrier))) (Z* n).carrier =
       coset Z.sum (Z.sum.op (&j) (&j')) (Z* n).sum.carrier
       So this is to show:
       coset Z.sum (Z.sum.op (&j) (&j')) (Z* n).sum.carrier = coset Z.sum (&(ZN n).sum.op j j') (Z* n).sum.carrier
       By subgroup_coset_eq, this is to show:
       Z.sum.op (Z.sum.inv (Z.sum.op (&j) (&j'))) (&(ZN n).sum.op j j') IN  (Z* n).sum.carrier
       or  -(&j + &j') + &((j + j') MOD n) IN Z_multiple n
         -(&j + &j') + &((j + j') MOD n)
       = -&(j + j') + &((j + j') MOD n)     by INT_ADD
       = -&(j + j') + &(j + j') % &n        by INT_MOD
       = -((&(j + j') / &n) * &n + (&(j + j') % &n)) + (&(j + j') % &n)   by INT_DIVISION
       = -((&(j + j') / &n) * &n) - (&(j + j') % &n) + (&(j + j') % &n)   by INT_SUB_LNEG
       = -((&(j + j') / &n) * &n)           by INT_SUB_ADD
       = -(&(j + j') / &n) * &n             by INT_NEG_LMUL
       = &n * -(&(j + j') / &n)             by INT_MUL_COMM]
       Hence in Z_multiple n.
*)
val Z_ideal_map_group_homo = store_thm(
  "Z_ideal_map_group_homo",
  ``!n. 0 < n ==> GroupHomo (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).sum (Z / Z* n).sum``,
  rpt strip_tac >>
  `!r. Ring r ==> (r.sum.carrier = R)` by rw_tac std_ss[Ring_def] >>
  rw[GroupHomo_def] >| [
    `Ring (ZN n)` by rw[ZN_ring] >>
    `(Z* n) << Z` by rw[Z_ideal_thm] >>
    `Ring Z` by rw[Z_ring] >>
    `Ring (Z / (Z* n))` by rw[quotient_ring_ring] >>
    `(ZN n).sum.carrier = (ZN n).carrier` by rw[] >>
    `(Z / Z* n).sum.carrier = (Z / Z* n).carrier` by rw[] >>
    metis_tac[Z_ideal_map_element],
    rw[quotient_ring_def, quotient_ring_add_def] >>
    `(Z* n).sum << Z.sum` by rw[Z_ideal_sum_normal] >>
    `Ring Z` by rw[Z_ring] >>
    `Ring (ZN n)` by rw[ZN_ring] >>
    `(ZN n).sum.carrier = (ZN n).carrier` by rw[] >>
    `Z.sum.carrier = Z.carrier` by rw[] >>
    `!k. k IN (ZN n).carrier ==> &k IN Z.carrier` by rw[ZN_def, Z_def] >>
    `&j IN Z.sum.carrier /\ &j' IN Z.sum.carrier` by metis_tac[] >>
    `(Z* n).carrier = (Z* n).sum.carrier` by rw[Z_ideal_def] >>
    `coset Z.sum (Z.sum.op (cogen Z.sum (Z* n).sum (coset Z.sum (&j) (Z* n).sum.carrier))
                          (cogen Z.sum (Z* n).sum (coset Z.sum (&j') (Z* n).sum.carrier))) (Z* n).carrier =
    coset Z.sum (Z.sum.op (&j) (&j')) (Z* n).sum.carrier` by rw[normal_coset_property] >>
    `coset Z.sum (Z.sum.op (&j) (&j')) (Z* n).sum.carrier =
     coset Z.sum (&(ZN n).sum.op j j') (Z* n).sum.carrier` suffices_by rw[] >>
    `(Z* n).sum <= Z.sum` by rw[Z_ideal_sum_subgroup] >>
    `(Z.sum.op (&j) (&j')) IN Z.sum.carrier` by rw[ring_add_group] >>
    `&(ZN n).sum.op j j' IN Z.sum.carrier` by rw[Z_def] >>
    `Z.sum.op (Z.sum.inv (Z.sum.op (&j) (&j'))) (&(ZN n).sum.op j j') IN  (Z* n).sum.carrier`
      suffices_by metis_tac[subgroup_coset_eq] >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    `(Z.sum = Z_add)` by rw[Z_def] >>
    `Z.sum.op (&j) (&j') IN Z_add.carrier` by rw[Z_def, Z_add_def] >>
    `Z.sum.op (&j) (&j') IN Z.sum.carrier ==>
    &(ZN n).sum.op j j' IN Z.sum.carrier ==>
    Z.sum.op (-(Z.sum.op (&j) (&j'))) (&(ZN n).sum.op j j') IN (Z* n).sum.carrier` suffices_by metis_tac[Z_add_inv] >>
    rw_tac std_ss[Z_def, Z_add_def, ZN_def, add_mod_def, Z_ideal_def] >>
    `n <> 0` by decide_tac >>
    `-(&j + &j') + &((j + j') MOD n) = -&(j + j') + &((j + j') MOD n)` by rw[INT_ADD] >>
    `_ = -&(j + j') + &(j + j') % &n` by rw[INT_MOD] >>
    `_ = -((&(j + j') / &n) * &n + (&(j + j') % &n)) + (&(j + j') % &n)` by rw[INT_DIVISION] >>
    `_ = -((&(j + j') / &n) * &n) - (&(j + j') % &n) + (&(j + j') % &n)` by rw[INT_SUB_LNEG] >>
    `_ = -((&(j + j') / &n) * &n)` by rw[INT_SUB_ADD] >>
    `_ = -(&(j + j') / &n) * &n` by rw[INT_NEG_LMUL] >>
    `_ = &n * -(&(j + j') / &n)` by rw[INT_MUL_COMM] >>
    rw[Z_multiple_def]
  ]);

(* Theorem: MonoidHomo (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).prod (Z / Z* n).prod *)
(* Proof: by MonoidHomo_def, this is to show:
   (1) j IN (ZN n).prod.carrier ==> coset Z.sum (&j) (Z* n).sum.carrier IN (Z / Z* n).prod.carrier
       Since (ZN n).prod.carrier = (ZN n).carrier          by Ring_def
             (Z / Z* n).prod.carrier = (Z / Z* n).carrier  by Ring_def
       true by Z_ideal_map_element.
   (2) j IN (ZN n).prod.carrier /\ j' IN (ZN n).prod.carrier ==>
       coset Z.sum (&(ZN n).prod.op j j') (Z* n).sum.carrier =
       (Z / Z* n).prod.op (coset Z.sum (&j) (Z* n).sum.carrier) (coset Z.sum (&j') (Z* n).sum.carrier)
       Since (Z* n).sum <= Z.sum    by Z_ideal_sum_subgroup
       and   ?k. cogen Z.sum (Z* n).sum (coset Z.sum (&j) (Z* n).sum.carrier) = &j + &n * k      by Z_sum_cogen
       and   ?k'. cogen Z.sum (Z* n).sum (coset Z.sum (&j') (Z* n).sum.carrier) = &j' + &n * k'  by Z_sum_cogen
       By subgroup_coset_eq, this reduces to:
       Z.sum.op (Z.sum.inv (&(ZN n).prod.op j j')) (Z.prod.op (&j + &n * k) (&j' + &n * k')) IN (Z* n).sum.carrier
       Now (Z* n).sum.carrier = (Z* n).carrier = Z_multiple n,
         Z.prod.op (&j + &n * k) (&j' + &n * k')
       = (&j + &n * k) * (&j' + &n * k')
       = (&j) * (&j') + &n * h   for some h, by INT_LDISTRIB
       = &(j * j') + &n * h      by INT_MUL
       Hence the difference with &(ZN n).prod.op j j') = &((j * j') MOD n) = &(j * j') % &n
       is a multiple of n, i.e. in (Z* n).sum.carrier.
   (3) coset Z.sum (&(ZN n).prod.id) (Z* n).sum.carrier = (Z / Z* n).prod.id
       Since (Z* n).sum <= Z.sum     by Z_ideal_sum_subgroup
       expand by definition, this is to show:
       coset Z.sum (&(ZN n).prod.id) (Z* n).sum.carrier = coset Z.sum Z.prod.id (Z* n).carrier
       and by subgroup_coset_eq, this is to show:
       Z.sum.op (- Z.prod.id) (&(ZN n).prod.id) IN (Z* n).sum.carrier
       or    - 1 + &(ZN n).prod.id IN (Z* n).sum.carrier
       Since (ZN n).prod.id = if n = 1 then 0 else 1, two cases:
       If n = 1, to show -1 in (Z* 1).sum.carrier = Z_multiple 1, true.
       If n <> 1, to show 0 in (Z* n).sum.carrier = Z_multiple n, true.
*)
val Z_ideal_map_monoid_homo = store_thm(
  "Z_ideal_map_monoid_homo",
  ``!n. 0 < n ==> MonoidHomo (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).prod (Z / Z* n).prod``,
  rpt strip_tac >>
  rw[MonoidHomo_def] >| [
    `Ring (ZN n)` by rw[ZN_ring] >>
    `(Z* n) << Z` by rw[Z_ideal_thm] >>
    `Ring Z` by rw[Z_ring] >>
    `Ring (Z / (Z* n))` by rw[quotient_ring_ring] >>
    `(ZN n).prod.carrier = (ZN n).carrier` by metis_tac[Ring_def] >>
    `(Z / Z* n).prod.carrier = (Z / Z* n).carrier` by metis_tac[Ring_def] >>
    `(ZN n).sum.carrier = (ZN n).carrier` by metis_tac[Ring_def] >>
    metis_tac[Z_ideal_map_element],
    rw[quotient_ring_def, quotient_ring_mult_def] >>
    `(Z* n).sum <= Z.sum` by rw[Z_ideal_sum_subgroup] >>
    `&j IN Z.sum.carrier /\ &j' IN Z.sum.carrier` by rw[Z_def, Z_add_def] >>
    `?k. cogen Z.sum (Z* n).sum (coset Z.sum (&j) (Z* n).sum.carrier) = &j + &n * k` by rw[Z_sum_cogen] >>
    `?k'. cogen Z.sum (Z* n).sum (coset Z.sum (&j') (Z* n).sum.carrier) = &j' + &n * k'` by rw[Z_sum_cogen] >>
    `(Z* n).sum.carrier = (Z* n).carrier` by rw[Z_ideal_def] >>
    `coset Z.sum (&(ZN n).prod.op j j') (Z* n).sum.carrier =
     coset Z.sum (Z.prod.op (&j + &n * k) (&j' + &n * k')) (Z* n).sum.carrier` suffices_by metis_tac[] >>
    `&(ZN n).prod.op j j' IN Z.sum.carrier` by rw[Z_def, Z_add_def] >>
    `Z.prod.op (&j + &n * k) (&j' + &n * k') IN Z.sum.carrier` by rw[Z_def, Z_add_def] >>
    `Z.sum.op (Z.sum.inv (&(ZN n).prod.op j j')) (Z.prod.op (&j + &n * k) (&j' + &n * k')) IN (Z* n).sum.carrier`
      suffices_by rw[GSYM subgroup_coset_eq] >>
    `Z.sum = Z_add` by rw[Z_def] >>
    `Z.sum.op (- (&(ZN n).prod.op j j')) (Z.prod.op (&j + &n * k) (&j' + &n * k')) IN (Z* n).sum.carrier`
      suffices_by metis_tac[Z_add_inv] >>
    rw_tac std_ss[Z_def, Z_add_def, Z_mult_def, ZN_def, times_mod_def, Z_ideal_def] >>
    `n <> 0` by decide_tac >>
    `-&((j * j') MOD n) + (&j + &n * k) * (&j' + &n * k') = -(&(j * j') % &n) + (&j + &n * k) * (&j' + &n * k')` by rw[INT_MOD] >>
    `_ = -(&(j * j') % &n) + (&j * (&j' + &n * k') + &n * k * (&j' + &n * k'))` by rw[INT_RDISTRIB] >>
    `_ = -(&(j * j') % &n) + (&j * &j' + &j * (&n * k') + &n * k * (&j' + &n * k'))` by rw[INT_LDISTRIB] >>
    `_ = -(&(j * j') % &n) + (&j * &j' + &n * k' * &j + &n * k * (&j' + &n * k'))` by rw[INT_MUL_COMM] >>
    `_ = -(&(j * j') % &n) + (&j * &j' + (&n * k' * &j + &n * k * (&j' + &n * k')))` by rw[INT_ADD_ASSOC] >>
    `_ = -(&(j * j') % &n) + (&j * &j' + (&n * (k' * &j) + &n * (k * (&j' + &n * k'))))` by rw[INT_MUL_ASSOC] >>
    `_ = -(&(j * j') % &n) + (&j * &j' + &n * (k' * &j + k * (&j' + &n * k')))` by rw[GSYM INT_LDISTRIB] >>
    `_ = -(&(j * j') % &n) + &j * &j' + &n * (k' * &j + k * (&j' + &n * k'))` by rw[INT_ADD_ASSOC] >>
    `_ = -(&(j * j') % &n) + &(j * j') + &n * (k' * &j + k * (&j' + &n * k'))` by rw[INT_MUL] >>
    `_ = -(&(j * j') % &n) + (&(j * j') / &n * &n + &(j * j') % &n) + &n * (k' * &j + k * (&j' + &n * k'))` by rw[INT_DIVISION] >>
    `_ = -(&(j * j') % &n) + (&(j * j') % &n + &(j * j') / &n * &n) + &n * (k' * &j + k * (&j' + &n * k'))` by rw[INT_ADD_COMM] >>
    `_ = -(&(j * j') % &n) + &(j * j') % &n + &(j * j') / &n * &n + &n * (k' * &j + k * (&j' + &n * k'))` by rw[INT_ADD_ASSOC] >>
    `_ = &(j * j') / &n * &n + &n * (k' * &j + k * (&j' + &n * k'))` by rw[INT_ADD_LINV] >>
    `_ = &n * (&(j * j') / &n) + &n * (k' * &j + k * (&j' + &n * k'))` by rw[INT_MUL_COMM] >>
    `_ = &n * (&(j * j') / &n + (k' * &j + k * (&j' + &n * k')))` by rw[INT_LDISTRIB] >>
    rw[Z_multiple_def],
    rw[quotient_ring_def, quotient_ring_mult_def] >>
    `(Z* n).sum <= Z.sum` by rw[Z_ideal_sum_subgroup] >>
    `(Z* n).sum.carrier = (Z* n).carrier` by rw[Z_ideal_def] >>
    `&(ZN n).prod.id IN Z.sum.carrier` by rw[Z_def, Z_add_def, ZN_def, times_mod_def] >>
    `Z.prod.id IN Z.sum.carrier` by rw[Z_def, Z_add_def, Z_mult_def] >>
    `Z.sum.op (Z.sum.inv Z.prod.id) &(ZN n).prod.id IN (Z* n).sum.carrier` suffices_by rw[GSYM subgroup_coset_eq] >>
    `Z.sum = Z_add` by rw[Z_def] >>
    `Z.sum.op (- Z.prod.id) (&(ZN n).prod.id) IN (Z* n).sum.carrier` suffices_by metis_tac[Z_add_inv] >>
    `n <> 0` by decide_tac >>
    rw[Z_def, Z_add_def, Z_mult_def, ZN_def, times_mod_def] >-
    rw[Z_ideal_def, Z_multiple_def] >>
    rw[Z_ideal_def, Z_multiple_def]
  ]);

(* Theorem: BIJ (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).carrier (Z / Z* n).carrier *)
(* Proof:
   (1) j IN (ZN n).carrier ==> coset Z.sum (&j) (Z* n).sum.carrier IN (Z / Z* n).carrier
       true by Z_ideal_map_element.
   (2) coset Z.sum (&j) (Z* n).sum.carrier = coset Z.sum (&j') (Z* n).sum.carrier ==> j = j'
       &j - &j' = multiple of n, but j < n and j' < n, hence j = j'.
       true by Z_multiple_less_neg_eq.
   (3) same as (1)
   (4) x IN (Z / Z* n).carrier ==> ?j. j IN (ZN n).carrier /\ (coset Z.sum (&j) (Z* n).sum.carrier = x)
       Expanding by definition, this is to show:
       x IN CosetPartition Z.sum (Z* n).sum ==> ?j. j IN (ZN n).carrier /\ (coset Z.sum (&j) (Z* n).sum.carrier = x)
       Let p = (cogen Z.sum (Z* n).sum x, then
            p IN Z.sum.carrier     by cogen_element
       thus p IN univ(:int)        by Z_def, Z_add_def
       By coset_cogen_property, we have:  coset Z.sum p (Z* n).sum.carrier = x
       So it is just choosing j, depending on p, to satisfy: j IN (ZN n).carrier
       If p = 0, take j = 0, then 0 IN (ZN n).carrier,
       If p <> 0, since by Z_sum_coset_eq,
          coset Z.sum p (Z* n).sum.carrier = coset Z.sum (p % &n) (Z* n).sum.carrier
       If p > 0, choose j = p MOD n,
       then &j = &(p MOD n) = &p % &n, so true by INT_MOD
       If p < 0, choose j = (n + (p MOD n)) MOD n,
       then &j = &((n + (p MOD n)) MOD n)
               = &(n + (p MOD n)) % &n      by INT_MOD
               = (&n % &n + &(p MOD n) % &n) % &n   by INT_ADD
               = &(p MOD n)                 by INT_MOD_ID, INT_MOD_MOD
               = &p % &n                    by INT_MOD
*)
val Z_ideal_map_bij = store_thm(
  "Z_ideal_map_bij",
  ``!n. 0 < n ==> BIJ (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).carrier (Z / Z* n).carrier``,
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >| [
    rw[Z_ideal_map_element],
    `(Z* n).sum <= Z.sum` by rw[Z_ideal_sum_subgroup] >>
    `&j IN Z.sum.carrier` by rw[Z_def, Z_add_def] >>
    `&j' IN Z.sum.carrier` by rw[Z_def, Z_add_def] >>
    `Z.sum.op (Z.sum.inv &j) &j' IN (Z* n).sum.carrier` by rw[GSYM subgroup_coset_eq] >>
    `Z.sum = Z_add` by rw[Z_def] >>
    `Z.sum.op (- &j) &j' IN (Z* n).sum.carrier` by metis_tac[Z_add_inv] >>
    `(Z* n).sum.carrier = Z_multiple n` by rw[Z_ideal_def] >>
    `!x y. Z.sum.op x y = x + y` by rw[Z_def, Z_add_def] >>
    `(- &j) +  &j' IN Z_multiple n` by metis_tac[] >>
    `!x. x IN (ZN n).carrier ==> x < n` by rw[ZN_def] >>
    metis_tac[Z_multiple_less_neg_eq],
    rw[Z_ideal_map_element],
    pop_assum mp_tac >>
    rw[quotient_ring_def, quotient_ring_mult_def] >>
    `(Z* n).sum <= Z.sum` by rw[Z_ideal_sum_subgroup] >>
    `(cogen Z.sum (Z* n).sum x) IN Z.sum.carrier` by rw[cogen_element] >>
    `(cogen Z.sum (Z* n).sum x) IN univ(:int)` by rw[Z_def, Z_add_def] >>
    qabbrev_tac `p = (cogen Z.sum (Z* n).sum x)` >>
    `coset Z.sum p (Z* n).sum.carrier = x` by rw[coset_cogen_property, Abbr`p`] >>
    `!x. x IN (ZN n).carrier <=> x < n` by rw[ZN_def] >>
    Cases_on `p = 0` >| [
      qexists_tac `0` >>
      rw[],
      `n <> 0` by decide_tac >>
      `&n <> 0` by rw[INT_INJ] >>
      `coset Z.sum p (Z* n).sum.carrier = coset Z.sum (p % &n) (Z* n).sum.carrier` by rw[GSYM Z_sum_coset_eq] >>
      Cases_on `0 <= p` >| [
        `?k. p = &k` by metis_tac[NUM_POSINT] >>
        qexists_tac `k MOD n` >>
        rw[MOD_LESS, INT_MOD],
        `p < 0` by rw[GSYM INT_NOT_LE] >>
        `?k. p = -&k` by metis_tac[NUM_NEGINT_EXISTS, INT_LT_IMP_LE] >>
        `k MOD n < n` by rw[MOD_LESS] >>
        `p % &n = (- &k) % &n` by rw[] >>
        `_ = (&n - &k) % &n` by rw[INT_MOD_NEG_NUMERATOR] >>
        `_ = (&n % &n - &k % &n) % &n` by rw[INT_MOD_SUB] >>
        `_ = (&n % &n - &k % &n % &n) % &n` by rw[INT_MOD_MOD] >>
        `_ = (&n % &n - &(k MOD n) % &n) % &n` by rw[INT_MOD] >>
        `_ = (&n  - &(k MOD n)) % &n` by rw[INT_MOD_SUB] >>
        `_ = &(n - k MOD n) % &n` by rw[INT_SUB, LESS_IMP_LESS_OR_EQ] >>
        `_ = &((n - k MOD n) MOD n)` by rw[INT_MOD] >>
        qexists_tac `(n - k MOD n) MOD n` >>
        rw[MOD_LESS]
      ]
    ]
  ]);

(* Theorem: (ZN n) isomorphic to Z / (Z* n) *)
(* Proof:
   The bijection is: j IN (ZN n) -> coset (Z* n).sum (&j) (Z* n).sum.carrier
   where (Z* n).sum.carrier = Z_multiple n
   (1) j IN (ZN n).carrier ==> coset Z.sum (&j) (Z* n).sum.carrier IN (Z / Z* n).carrier
       true by Z_ideal_map_element.
   (2) GroupHomo (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).sum (Z / Z* n).sum
       true by Z_ideal_map_group_homo.
   (3) MonoidHomo (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).prod (Z / Z* n).prod
       true by Z_ideal_map_monoid_homo.
   (4) BIJ (\j. coset Z.sum (&j) (Z* n).sum.carrier) (ZN n).carrier (Z / Z* n).carrier
       true by Z_ideal_map_bij.
*)
val Z_quotient_iso_ZN = store_thm(
  "Z_quotient_iso_ZN",
  ``!n. 0 < n ==> RingIso (\(j:num). coset Z.sum (&j) (Z* n).sum.carrier) (ZN n) (Z / (Z* n))``,
  rw[RingIso_def, RingHomo_def] >-
  rw[Z_ideal_map_element] >-
  rw[Z_ideal_map_group_homo] >-
  rw[Z_ideal_map_monoid_homo] >>
  rw[Z_ideal_map_bij]);

(* ------------------------------------------------------------------------- *)
(* Integer as Euclidean Ring.                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: EuclideanRing Z *)
(* Proof:
   By EuclideanRing_def, this is to show:
   (1) Ring Z, true       by Z_ring
   (2) (Num (ABS x) = 0) <=> (x = 0)
       If part: Num (ABS x) = 0 ==> x = 0
       If ABS x = &n, n <> 0, Num (&n) = n  by NUM_OF_INT, or n = 0, contradicts n <> 0.
       If ABS x = -&n, n <> 0, then -&n < 0, contradicts ~(ABS x < 0) by INT_ABS_LT0.
       If ABS x = 0, this means ABS x <= 0, hence x = 0 by INT_ABS_LE0.
       Only-if part: x = 0 ==> Num (ABS x) = 0
       i.e to show: Num (ABS 0) = 0
         Num (ABS 0)
       = Num 0            by INT_ABS_EQ0, ABS 0 = 0
       = 0                by NUM_OF_INT, Num (&n) = n
   (3) !x y. y <> 0 ==> ?q t. (x = q * y + t) /\ Num (ABS t) < Num (ABS y)
       Let q = x / y, t = x % y.
       Then by INT_DIVISION,
       (x = q * y + t) /\ if y < 0 then (y < t /\ t <= 0) else (0 <= t /\ t < y)
       If y = &n, n <> 0, then ~(y < 0), hence 0 <= t /\ t < y
       0 <= t ==> ?k. t = &k       by NUM_POSINT
       So   Num (ABS t) = k        by INT_ABS_NUM, NUM_OF_INT
       and  Num (ABS y) = n        by INT_ABS_NUM, NUM_OF_INT
       and  &k < &n ==> k < n      by INT_LT
       If y = -&n, n <> 0, then y < 0, hence y < t /\ t <= 0
       t <= 0 ==> ?k. t = -&k      by NUM_NEGINT_EXISTS
       But  Num (ABS t) = k        by INT_ABS_NEG, INT_ABS_NUM, NUM_OF_INT
       and  Num (ABS y) = n        by INT_ABS_NEG, INT_ABS_NUM, NUM_OF_INT
       and  -&n < -&k
         ==> &k < &n               by INT_LT_CALCULATE
         ==> k < n                 by INT_LT (or INT_LT_CALCULATE)
*)

Theorem Z_euclid_ring: EuclideanRing Z Num
Proof
  rw[EuclideanRing_def]
  >- rw[Z_ring]
  >- rw[Z_def, Z_add_def] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw[Z_def, Z_add_def, Z_mult_def] >>
  qexists_tac ‘x / y’ >>
  qexists_tac ‘x % y’ >>
  ‘(x = x / y * y + x % y) /\
   if y < 0 then (y < x % y /\ x % y <= 0) else (0 <= x % y /\ x % y < y)’
    by rw[INT_DIVISION] >>
  qabbrev_tac ‘q = x / y’ >>
  qabbrev_tac ‘t = x % y’ >>
  ‘(?n. (y = &n) /\ n <> 0) \/ (?n. (y = -&n) /\ n <> 0) \/ (y = 0)’
    by rw[INT_NUM_CASES]
  >- (‘~(y < 0)’ by rw[] >>
      ‘0 <= t /\ t < y’ by metis_tac[] >>
      ‘?k. t = &k’ by metis_tac[NUM_POSINT] >>
      gvs[]) >>
  ‘y < 0’ by rw[] >>
  ‘y < t /\ t <= 0’ by metis_tac[] >>
  ‘?k. t = -&k’ by metis_tac[NUM_NEGINT_EXISTS] >>
  gvs[]
QED

(* Theorem: PrincipalIdealRing Z *)
(* Proof:
   Since EuclideanRing Z (Num o ABS)   by Z_euclid_ring
   hence PrincipalIdealRing Z          by euclid_ring_principal_ideal_ring
*)
val Z_principal_ideal_ring = store_thm(
  "Z_principal_ideal_ring",
  ``PrincipalIdealRing Z``,
  metis_tac[Z_euclid_ring, euclid_ring_principal_ideal_ring]);

(* ------------------------------------------------------------------------- *)
(* Integral Domain Documentation                                             *)
(* ------------------------------------------------------------------------- *)
(* An Integral Domains is a Ring with two additional properties:
   a. distinct identities: #1 <> #0
   b. no #0 divisors: x * y = #0 <=> x = 0 \/ y = 0

   This implies:
   1. The nonzero elements are closed under (ring) multiplication,
      i.e. besides the multiplicative monoid with carrier = all elements,
      there is also a multiplicative monoid with carrier = nonzero elements.
   2. Every integral domain has at least two elements: #0 and #1.
      The smallest integral domain is isomorphic to Z_2 = {0, 1}.
      The typical integral domain is Z = {0, +/-1, +/-2, ... }
   3. Finite integral domains are (finite) fields:
      For any nonzero x, the sequence x, x^2, x^3, .... must wrap around, hence invertible.
*)
(* Data type:
   The generic symbol for ring data is r.
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

   R    = r.carrier
   R+   = ring_nonzero r
*)
(* Definitions and Theorems (# are exported):

   Definitions:
   IntegralDomain_def       |- !r. IntegralDomain r <=>  Ring r /\ #1 <> #0 /\
                                                         !x y. x IN R /\ y IN R ==> ((x * y = #0) <=> (x = #0) \/ (y = #0))
   FiniteIntegralDomain_def |- !r. FiniteIntegralDomain r <=> IntegralDomain r /\ FINITE R

   Simple theorems:
   integral_domain_is_ring       |- !r. IntegralDomain r ==> Ring r
#  integral_domain_one_ne_zero   |- !r. IntegralDomain r ==> #1 <> #0
   integral_domain_mult_eq_zero  |- !r. IntegralDomain r ==> !x y. x IN R /\ y IN R ==> ((x * y = #0) <=> (x = #0) \/ (y = #0))
   integral_domain_zero_product  |- !r. IntegralDomain r ==> !x y. x IN R /\ y IN R ==> ((x * y = #0) <=> (x = #0) \/ (y = #0))
   integral_domain_zero_not_unit |- !r. IntegralDomain r ==> #0 NOTIN R*
   integral_domain_one_nonzero   |- !r. IntegralDomain r ==> #1 IN R+
   integral_domain_mult_nonzero  |- !r. IntegralDomain r ==> !x y. x IN R+ /\ y IN R+ ==> x * y IN R+
   integral_domain_nonzero_mult_carrier  |- !r. IntegralDomain r ==> (F* = R+)
   integral_domain_nonzero_mult_property |- !r. IntegralDomain r ==> (F* = R+) /\ (f*.id = #1) /\
                                                                     (f*.op = $* ) /\ (f*.exp = $** )
   integral_domain_nonzero_monoid       |- !r. IntegralDomain r ==> Monoid f*

   Left and Right Multiplicative Cancellation:
   integral_domain_mult_lcancel  |- !r. IntegralDomain r ==> !x y z. x IN R /\ y IN R /\ z IN R ==>
                                        ((x * y = x * z) <=> (x = #0) \/ (y = z))
   integral_domain_mult_rcancel  |- !r. IntegralDomain r ==> !x y z.  x IN R /\ y IN R /\ z IN R ==>
                                        ((y * x = z * x) <=> (x = #0) \/ (y = z))

   Non-zero multiplications form a Monoid:
   monoid_of_ring_nonzero_mult_def         |- !r. monoid_of_ring_nonzero_mult r = <|carrier := R+; op := $*; id := #1|>
   integral_domain_nonzero_mult_is_monoid  |- !r. IntegralDomain r ==> Monoid (monoid_of_ring_nonzero_mult r)

   Theorems from Ring exponentiation:
   integral_domain_exp_nonzero  |- !r. IntegralDomain r ==> !x. x IN R+ ==> !n. x ** n IN R+
   integral_domain_exp_eq_zero  |- !r. IntegralDomain r ==> !x. x IN R ==> !n. (x ** n = #0) <=> n <> 0 /\ (x = #0)
   integral_domain_exp_eq       |- !r. IntegralDomain r ==> !x. x IN R+ ==>
                                                            !m n. m < n /\ (x ** m = x ** n) ==> (x ** (n - m) = #1)

   Finite Integral Domain:
   finite_integral_domain_period_exists
                                |- !r. FiniteIntegralDomain r ==> !x. x IN R+ ==> ?k. 0 < k /\ (x ** k = #1)
   finite_integral_domain_nonzero_invertible
                                |- !r. FiniteIntegralDomain r ==> (monoid_invertibles r.prod = R+ )
   finite_integral_domain_nonzero_invertible_alt
                                |- !r. FiniteIntegralDomain r ==> (monoid_invertibles f* = F* )
   finite_integral_domain_nonzero_group
                                |- !r. FiniteIntegralDomain r ==> Group f*

   Integral Domain Element Order:
   integral_domain_nonzero_order  |- !r. IntegralDomain r ==> !x. order r.prod x = order f* x
   integral_domain_order_zero     |- !r. IntegralDomain r ==> (order f* #0 = 0)
   integral_domain_order_nonzero  |- !r. FiniteIntegralDomain r ==> !x. x IN R+ ==> order f* x <> 0
   integral_domain_order_eq_0     |- !r. FiniteIntegralDomain r ==> !x. x IN R ==> ((order f* x = 0) <=> (x = #0))

   Integral Domain Characteristic:
   integral_domain_char         |- !r. IntegralDomain r ==> (char r = 0) \/ prime (char r)

   Principal Ideals in Integral Domain:
   principal_ideal_equal_principal_ideal  |- !r. IntegralDomain r ==>
                                             !p q. p IN R /\ q IN R ==> ((<p> = <q>) <=> ?u. unit u /\ (p = q * u))
*)
(* ------------------------------------------------------------------------- *)
(* Basic Definitions                                                         *)
(* ------------------------------------------------------------------------- *)

(* Integral Domain Definition:
   An Integral Domain is a record r with elements of type 'a ring, such that
   . r is a Ring
   . #1 <> #0
   . !x y IN R, x * y = #0 <=> x = #0 or y = #0
*)
val IntegralDomain_def = Define`
  IntegralDomain (r:'a ring) <=>
    Ring r /\
    #1 <> #0 /\
    (!x y. x IN R /\ y IN R ==> ((x * y = #0) <=> (x = #0) \/ (y = #0)))
`;

val FiniteIntegralDomain_def = Define`
  FiniteIntegralDomain (r:'a ring) <=> IntegralDomain r /\ FINITE R
`;

(* ------------------------------------------------------------------------- *)
(* Simple Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Integral Domain is Ring. *)
(* Proof: by definition. *)
val integral_domain_is_ring = save_thm("integral_domain_is_ring",
  IntegralDomain_def |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val integral_domain_is_ring = |- !r. IntegralDomain r ==> Ring r : thm *)

(* Theorem: Integral Domain has #1 <> #0 *)
(* Proof: by definition *)
val integral_domain_one_ne_zero = save_thm("integral_domain_one_ne_zero",
  IntegralDomain_def |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> UNDISCH |> CONJUNCT2 |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val integral_domain_one_ne_zero = |- !r. IntegralDomain r ==> #1 <> #0 : thm *)

val _ = export_rewrites ["integral_domain_one_ne_zero"];

(* Theorem: No zero divisor in integral domain. *)
(* Proof: by definition. *)
val integral_domain_mult_eq_zero = save_thm("integral_domain_mult_eq_zero",
  IntegralDomain_def |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> UNDISCH |> CONJUNCT2 |> CONJUNCT2 |> DISCH_ALL |> GEN_ALL);
(* > val integral_domain_mult_eq_zero =
     |- !r. IntegralDomain r ==> !x y. x IN R /\ y IN R ==> ((x * y = #0) <=> (x = #0) \/ (y = #0)) : thm *)

(* Alternative name for export *)
val integral_domain_zero_product = save_thm("integral_domain_zero_product", integral_domain_mult_eq_zero);
(* > val integral_domain_zero_product =
    |- !r. IntegralDomain r ==> !x y. x IN R /\ y IN R ==> ((x * y = #0) <=> (x = #0) \/ (y = #0)) : thm *)

(* Theorem: #0 is not a unit of integral domain. *)
(* Proof: by ring_units_has_zero *)
val integral_domain_zero_not_unit = store_thm(
  "integral_domain_zero_not_unit",
  ``!r:'a ring. IntegralDomain r ==> ~ (#0 IN R*)``,
  rw[ring_units_has_zero, IntegralDomain_def]);

(* Theorem: #1 IN R+ for integral domain. *)
(* Proof: by #1 <> #0 and ring_nonzero_eq. *)
val integral_domain_one_nonzero = store_thm(
  "integral_domain_one_nonzero",
  ``!r:'a ring. IntegralDomain r ==> #1 IN R+``,
  rw[integral_domain_is_ring, ring_nonzero_eq]);

(* Theorem: x IN R+ /\ y IN R+ <=> (x * y) IN R+ *)
(* Proof: by definitions. *)
val integral_domain_mult_nonzero = store_thm(
  "integral_domain_mult_nonzero",
  ``!r:'a ring. IntegralDomain r ==> !x y. x IN R+ /\ y IN R+ ==> (x * y) IN R+``,
  rw[integral_domain_zero_product, integral_domain_is_ring, ring_nonzero_eq]);

(* Theorem: IntegralDomain r ==> (F* = R+) *)
(* Proof: by integral_domain_is_ring, ring_nonzero_mult_carrier *)
val integral_domain_nonzero_mult_carrier = store_thm(
  "integral_domain_nonzero_mult_carrier",
  ``!r:'a ring. IntegralDomain r ==> (F* = R+)``,
  rw_tac std_ss[integral_domain_is_ring, ring_nonzero_mult_carrier]);

(* Theorem: properties of f*. *)
(* Proof:
   By IntegralDomain_def, excluding_def
   For F* = R+
         F*
       = r.prod.carrier DIFF {#0}
       = R DIFF {#0}            by ring_carriers
       = R+                     by ring_nonzero_def
   For f*.exp = r.prod.exp
       This is true             by monoid_exp_def, FUN_EQ_THM
*)
val integral_domain_nonzero_mult_property = store_thm(
  "integral_domain_nonzero_mult_property",
  ``!r:'a ring. IntegralDomain r ==>
               (F* = R+) /\ (f*.id = #1) /\ (f*.op = r.prod.op) /\ (f*.exp = r.prod.exp)``,
  rw_tac std_ss[IntegralDomain_def, excluding_def, ring_carriers, ring_nonzero_def, monoid_exp_def, FUN_EQ_THM]);

(* Theorem: IntegralDomain r ==> Monoid f* *)
(* Proof:
   Note IntegralDomain r ==> Ring r                by IntegralDomain_def
   By Monoid_def, excluding_def, IN_DIFF, IN_SING, ring_carriers, this is to show:
   (1) x IN R /\ y IN R ==> x * y IN R, true       by ring_mult_element
   (2) x IN R /\ y IN R /\ z IN R ==> x * y * z = x * (y * z), true by ring_mult_assoc
   (3) #1 IN R, true                               by ring_one_element
   (4) x IN R ==> #1 * x = x, true                 by ring_mult_lone
   (5) x IN R ==> x * #1 = x, true                 by ring_mult_rone
*)
val integral_domain_nonzero_monoid = store_thm(
  "integral_domain_nonzero_monoid",
  ``!r:'a ring. IntegralDomain r ==> Monoid f*``,
  rw_tac std_ss[IntegralDomain_def] >>
  rw_tac std_ss[Monoid_def, excluding_def, IN_DIFF, IN_SING, ring_carriers] >>
  rw[ring_mult_assoc]);

(* Another proof of the same result. *)

(* Theorem: IntegralDomain r ==> Monoid f* *)
(* Proof:
   By IntegralDomain_def, Monoid_def, integral_domain_nonzero_mult_property, this is to show:
   (1) x IN R+ /\ y IN R+ ==> x * y IN R+, true by ring_mult_element, ring_nonzero_eq
   (2) x IN R+ /\ y IN R+ /\ z IN R+ ==> x * y * z = x * (y * z), true by ring_mult_assoc, ring_nonzero_eq
   (3) #1 IN R+, true                       by ring_one_element, ring_nonzero_eq
   (4) x IN R+ ==> #1 * x = x, true         by ring_mult_lone, ring_nonzero_eq
   (5) x IN R+ ==> x * #1 = x, true         by ring_mult_rone, ring_nonzero_eq
*)
Theorem integral_domain_nonzero_monoid[allow_rebind]:
  !r:'a ring. IntegralDomain r ==> Monoid f*
Proof
  rw_tac std_ss[IntegralDomain_def, Monoid_def,
                integral_domain_nonzero_mult_property] >>
  fs[ring_nonzero_eq, ring_mult_assoc]
QED

(* ring isomorphisms preserve domain properties *)

Theorem integral_domain_ring_iso:
  IntegralDomain r /\ Ring s /\ RingIso f r s ==> IntegralDomain s
Proof
  simp[IntegralDomain_def]
  \\ strip_tac
  \\ drule_then (drule_then drule) ring_iso_sym
  \\ simp[RingIso_def, RingHomo_def]
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`BIJ g s.carrier r.carrier`
  \\ `Group s.sum /\ Group r.sum` by metis_tac[Ring_def, AbelianGroup_def]
  \\ `g s.sum.id = r.sum.id` by metis_tac[group_homo_id]
  \\ conj_asm1_tac >- metis_tac[monoid_homo_id]
  \\ rw[]
  \\ first_x_assum(qspecl_then[`g x`,`g y`]mp_tac)
  \\ impl_keep_tac >- metis_tac[BIJ_DEF, INJ_DEF]
  \\ fs[MonoidHomo_def]
  \\ `s.prod.carrier = s.carrier` by metis_tac[ring_carriers] \\ fs[]
  \\ first_x_assum(qspecl_then[`x`,`y`]mp_tac)
  \\ simp[]
  \\ `s.sum.id IN s.carrier` by simp[]
  \\ `s.prod.op x y IN s.carrier` by simp[]
  \\ PROVE_TAC[BIJ_DEF, INJ_DEF]
QED

(* ------------------------------------------------------------------------- *)
(* Left and Right Multiplicative Cancellation                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: IntegeralDomain r ==> x * y = x * z <=> x = #0 \/ y = z  *)
(* Proof:
        x * y = x * z
   <=>  x * y - x * z = #0       by ring_sub_eq_zero
   <=>  x * (y - z) = #0         by ring_mult_rsub
   <=>  x = #0 or (y - z) = #0   by integral_domain_zero_product
   <=>  x = #0 or y = z          by ring_sub_eq_zero
*)
val integral_domain_mult_lcancel = store_thm(
  "integral_domain_mult_lcancel",
  ``!r:'a ring. IntegralDomain r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((x * y = x * z) <=> (x = #0) \/ (y = z))``,
  rpt strip_tac >>
  `Ring r` by rw[integral_domain_is_ring] >>
  `(x * y = x * z) <=> (x * y - x * z = #0)` by rw[ring_sub_eq_zero] >>
  `_ = (x * (y - z) = #0)` by rw_tac std_ss[ring_mult_rsub] >>
  `_ = ((x = #0) \/ (y - z = #0))` by rw[integral_domain_zero_product] >>
  `_ = ((x = #0) \/ (y = z))` by rw[ring_sub_eq_zero] >>
  rw[]);

(* Theorem: IntegeralDomain r ==> y * x = z * x <=> x = #0 \/ y = z  *)
(* Proof: by integral_domain_mult_lcancel, ring_mult_comm. *)
val integral_domain_mult_rcancel = store_thm(
  "integral_domain_mult_rcancel",
  ``!r:'a ring. IntegralDomain r ==> !x y z. x IN R /\ y IN R /\ z IN R ==> ((y * x = z * x) <=> (x = #0) \/ (y = z))``,
  rw[integral_domain_mult_lcancel, ring_mult_comm, integral_domain_is_ring]);

(* ------------------------------------------------------------------------- *)
(* Non-zero multiplications form a Monoid.                                   *)
(* ------------------------------------------------------------------------- *)

(* Define monoid of ring nonzero multiplication. *)
val monoid_of_ring_nonzero_mult_def = Define`
  monoid_of_ring_nonzero_mult (r:'a ring) :'a monoid  =
  <| carrier := R+;
          op := r.prod.op;
          id := #1
    |>
`;
(*
- type_of ``monoid_of_ring_nonzero_mult r``;
> val it = ``:'a monoid`` : hol_type
*)

(* Theorem: Integral nonzero multiplication form a Monoid. *)
(* Proof: by checking definition. *)
val integral_domain_nonzero_mult_is_monoid = store_thm(
  "integral_domain_nonzero_mult_is_monoid",
  ``!r:'a ring. IntegralDomain r ==> Monoid (monoid_of_ring_nonzero_mult r)``,
  rpt strip_tac >>
  `Ring r` by rw_tac std_ss[integral_domain_is_ring] >>
  rw_tac std_ss[Monoid_def, monoid_of_ring_nonzero_mult_def, RES_FORALL_THM] >-
  rw_tac std_ss[integral_domain_mult_nonzero] >-
  rw[ring_mult_assoc, ring_nonzero_element] >-
  rw_tac std_ss[integral_domain_one_nonzero] >-
  rw[ring_nonzero_element] >>
  rw[ring_nonzero_element]);

(* ------------------------------------------------------------------------- *)
(* Theorems from Ring exponentiation.                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: For integral domain: x ** n IN R+ *)
(* Proof: by induction on n.
   Base case: x ** 0 IN R+
      since x ** 0 = #1  by ring_exp_0
      hence true by integral_domain_one_nonzero.
   Step case: x ** n IN R+ ==> x ** SUC n IN R+
      since x ** SUC n = x * x ** n   by ring_exp_SUC
      hence true by integral_domain_mult_nonzero, by induction hypothesis.
*)
val integral_domain_exp_nonzero = store_thm(
  "integral_domain_exp_nonzero",
  ``!r:'a ring. IntegralDomain r ==> !x. x IN R+ ==> !n. x ** n IN R+``,
  rpt strip_tac >>
  `Ring r` by rw_tac std_ss[integral_domain_is_ring] >>
  Induct_on `n` >| [
    rw[integral_domain_one_nonzero, ring_nonzero_element],
    rw_tac std_ss[ring_exp_SUC, integral_domain_mult_nonzero, ring_nonzero_element]
  ]);

(* Theorem: For integral domain, x ** n = #0 <=> n <> 0 /\ x = #0 *)
(* Proof: by integral_domain_exp_nonzero and ring_zero_exp. *)
val integral_domain_exp_eq_zero = store_thm(
  "integral_domain_exp_eq_zero",
  ``!r:'a ring. IntegralDomain r ==> !x. x IN R ==> !n. (x ** n = #0) <=> n <> 0 /\ (x = #0)``,
  rpt strip_tac >>
  `Ring r /\ (#1 <> #0)` by rw[integral_domain_is_ring] >>
  metis_tac[integral_domain_exp_nonzero, ring_nonzero_eq, ring_zero_exp, ring_exp_element]);

(* Theorem: For m < n, x IN R+ /\ x ** m = x ** n ==> x ** (n-m) = #1 *)
(* Proof:
     x ** (n-m) * x ** m
   = x ** ((n-m) + m)         by ring_exp_add
   = x ** n                   by arithmetic, m < n
   = x ** m                   by given
   = #1 * x ** m              by ring_mult_lone

   Hence (x ** (n-m) - #1) * x ** m = #0  by ring_mult_ladd
   By no-zero-divisor property of Integral Domain,
   x ** (n-m) - #1 = 0, or x ** (n-m) = #1.
*)
val integral_domain_exp_eq = store_thm(
  "integral_domain_exp_eq",
  ``!r:'a ring. IntegralDomain r ==> !x. x IN R+ ==> !m n. m < n /\ (x ** m = x ** n) ==> (x ** (n-m) = #1)``,
  rpt strip_tac >>
  `Ring r` by rw_tac std_ss[integral_domain_is_ring] >>
  `#1 IN R+ /\ !k. x ** k IN R+` by rw_tac std_ss[integral_domain_one_nonzero, integral_domain_exp_nonzero] >>
  `!z. z IN R+ ==> z IN R` by rw_tac std_ss[ring_nonzero_element] >>
  `(n-m) + m = n` by decide_tac >>
  `x ** (n-m) * x ** m = x ** ((n-m) + m)` by rw_tac std_ss[ring_exp_add] >>
  `_ = #1 * x ** m` by rw_tac std_ss[ring_mult_lone] >>
  `x ** (n - m) * x ** m - #1 * x ** m = #0` by rw_tac std_ss[ring_sub_eq_zero, ring_mult_element] >>
  `x ** (n - m) * x ** m + (-#1) * x ** m = #0` by metis_tac[ring_sub_def, ring_neg_mult] >>
  `(x ** (n-m) + (-#1)) * x ** m = #0` by rw_tac std_ss[ring_mult_ladd, ring_neg_element] >>
  `(x ** (n-m) - #1) * x ** m = #0` by metis_tac[ring_sub_def] >>
  `(x ** (n-m) - #1) IN R` by rw_tac std_ss[ring_sub_element] >>
  metis_tac[ring_sub_eq_zero, integral_domain_zero_product, ring_nonzero_eq]);

(* ------------------------------------------------------------------------- *)
(* Finite Integral Domain.                                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FINITE IntegralDomain r ==> !x in R+, ?k. 0 < k /\ (x ** k = #1) *)
(* Proof: by finite_monoid_exp_not_distinct and integral_domain_exp_eq. *)
val finite_integral_domain_period_exists = store_thm(
  "finite_integral_domain_period_exists",
  ``!r:'a ring. FiniteIntegralDomain r ==> !x. x IN R+ ==> ?k. 0 < k /\ (x ** k = #1)``,
  rpt strip_tac >>
  `IntegralDomain r /\ FINITE R /\ Ring r` by metis_tac[FiniteIntegralDomain_def, IntegralDomain_def] >>
  `Monoid r.prod /\ (r.prod.carrier = R)` by rw_tac std_ss[ring_mult_monoid] >>
  `!z. z IN R+ ==> z IN R` by rw_tac std_ss[ring_nonzero_element] >>
  `?h k. (x ** h = x ** k) /\ (h <> k)` by rw_tac std_ss[finite_monoid_exp_not_distinct, FiniteMonoid_def] >>
  Cases_on `h < k` >| [
    `0 < k - h` by decide_tac,
    `k < h /\ 0 < h - k` by decide_tac
  ] >> metis_tac[integral_domain_exp_eq]);

(* Theorem: FINITE IntegralDomain r ==> all x IN R+ are invertible. *)
(* Proof:
   Eventually this reduces to:
   (1) x * y = #1 /\ y * x = #1 ==> x <> #0
       By contradiction.
       If x = #0, then x * y = #0    by ring_mult_lzero
       but contradicts x * y = #1    by given
       as #1 <> #0 for Integral Domains.
   (2) x <> #0 ==> ?y. y IN R /\ (x * y = #1) /\ (y * x = #1)
       Since FINITE IntegralDomain r,
       ?k. 0 < k /\ (x ** k = #1)    by finite_integral_domain_period_exists
       i.e. 1 <= k, or 0 <= (k-1).
       Let h = k - 1, then
       x ** h * x = x ** k = #1      by ring_exp_add, and
       x * x ** h = x ** k = #1      by ring_exp_add,
       so just take y = x ** h.
*)
val finite_integral_domain_nonzero_invertible = store_thm(
  "finite_integral_domain_nonzero_invertible",
  ``!r:'a ring. FiniteIntegralDomain r ==> (monoid_invertibles r.prod = R+ )``,
  rpt strip_tac >>
  `IntegralDomain r` by metis_tac[FiniteIntegralDomain_def] >>
  `Ring r /\ (#1 <> #0)` by rw[integral_domain_is_ring] >>
  `Monoid r.prod /\ (r.prod.carrier = R) /\ (#1 = #1)` by rw[ring_mult_monoid] >>
  rw_tac std_ss[monoid_invertibles_def, ring_nonzero_eq, EXTENSION, EQ_IMP_THM, GSPECIFICATION] >| [
    metis_tac[ring_mult_lzero],
    `x IN R+ /\ (x ** 1 = x)` by rw_tac std_ss[ring_nonzero_eq, ring_exp_1] >>
    `?k. 0 < k /\ (x ** k = #1)` by rw_tac std_ss[finite_integral_domain_period_exists] >>
    qexists_tac `x ** (k-1)` >>
    `(1 + (k-1) = k) /\ ((k - 1) + 1 = k)` by decide_tac >>
    metis_tac[ring_exp_add, ring_exp_element]
  ]);

(* Theorem: FiniteIntegralDomain r ==> (F* = monoid_invertibles f* *)
(* Proof:
   Note Ring r                               by integral_domain_is_ring
    and #0 NOTIN R+                          by ring_nonzero_eq
    But monoid_invertibles r.prod = R+       by finite_integral_domain_nonzero_invertible [1]
   Thus #0 NOTIN monoid_invertibles r.prod   by above [2]
   with AbelianMonoid r.prod                 by ring_mult_abelian_monoid, Ring r
        F*
      = R+                                   by ring_nonzero_mult_carrier
      = monoid_invertibles r.prod            by above [1]
      = monoid_invertibles f*                by abelian_monoid_invertible_excluding, [2]
*)
val finite_integral_domain_nonzero_invertible_alt = store_thm(
  "finite_integral_domain_nonzero_invertible_alt",
  ``!r:'a ring. FiniteIntegralDomain r ==> (monoid_invertibles f* = F* )``,
  rpt (stripDup[FiniteIntegralDomain_def]) >>
  `Ring r` by rw[integral_domain_is_ring] >>
  `#0 NOTIN R+` by rw[ring_nonzero_eq] >>
  `monoid_invertibles r.prod = R+` by rw_tac std_ss[finite_integral_domain_nonzero_invertible] >>
  `AbelianMonoid r.prod` by rw[ring_mult_abelian_monoid] >>
  `monoid_invertibles f* = monoid_invertibles r.prod` by rw[abelian_monoid_invertible_excluding] >>
  rw[ring_nonzero_mult_carrier]);

(* Theorem: FiniteIntegralDomain r ==> Group f* *)
(* Proof:
   By Group_def, this is to show:
   (1) Monoid f*, true                  by integral_domain_nonzero_monoid
   (2) monoid_invertibles f* = F*, true by finite_integral_domain_nonzero_invertible_alt
*)
val finite_integral_domain_nonzero_group = store_thm(
  "finite_integral_domain_nonzero_group",
  ``!r:'a ring. FiniteIntegralDomain r ==> Group f*``,
  rpt (stripDup[FiniteIntegralDomain_def]) >>
  rw_tac std_ss[Group_def] >-
  rw[integral_domain_nonzero_monoid] >>
  rw[finite_integral_domain_nonzero_invertible_alt]);

(* ------------------------------------------------------------------------- *)
(* Integral Domain Element Order                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: IntegralDomain r ==> !x. order r.prod x = order f* x *)
(* Proof:
      forder x
    = order f* x                                                        by notation
    = case OLEAST k. period f* x k of NONE => 0 | SOME k => k           by order_def
    = case OLEAST k. 0 < k /\ (f*.exp x k = f*.id) of NONE => 0 | SOME k => k  by period_def
    = case OLEAST k. 0 < k /\ (x ** k = #1) of NONE => 0 | SOME k => k  by integral_domain_nonzero_mult_property
    = case OLEAST k. period r.prod x k of NONE => 0 | SOME k => k       by period_def
    = order r.prod x                                                    by order_def
*)
val integral_domain_nonzero_order = store_thm(
  "integral_domain_nonzero_order",
  ``!r:'a ring. IntegralDomain r ==> !x. order r.prod x = order f* x``,
  rw_tac std_ss[order_def, period_def, integral_domain_nonzero_mult_property]);

(* Theorem: IntegralDomain r ==> (order f* #0 = 0) *)
(* Proof:
   By order_def, period_def, integral_domain_nonzero_mult_property, this is to show that:
      ((n = 0) \/ #0 ** n <> #1) \/ ?m. m < n /\ m <> 0 /\ (#0 ** m = #1)
   By contradiction, suppose n <> 0 /\ #0 ** n = #1.
   Note Ring r /\ #1 <> #0        by IntegralDomain_def
   Thus #0 ** n = #0              by ring_zero_exp
   This gives #0 = #1, contradicting #1 <> #0.
*)
Theorem integral_domain_order_zero:
  !r:'a ring. IntegralDomain r ==> (order f* #0 = 0)
Proof
  rw_tac std_ss[order_def, period_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  rw[] >>
  rfs[integral_domain_nonzero_mult_property] >>
  spose_not_then strip_assume_tac >>
  fs[IntegralDomain_def] >> rfs[ring_zero_exp, AllCaseEqs()]
QED

(* Theorem: FiniteIntegralDomain r ==> !x. x IN R+ ==> (order f* x <> 0) *)
(* Proof:
   Note ?n. 0 < n /\ (n ** k = #1)           by finite_integral_domain_period_exists
     or ?n. n <> 0 /\ (f*.exp x n = f*.id)   by integral_domain_nonzero_mult_property
     or forder x <> 0                        by order_def, period_def
*)
val integral_domain_order_nonzero = store_thm(
  "integral_domain_order_nonzero",
  ``!r:'a ring. FiniteIntegralDomain r ==> !x. x IN R+ ==> (order f* x <> 0)``,
  rw_tac std_ss[order_def, period_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  rw[] >>
  `IntegralDomain r` by fs[FiniteIntegralDomain_def] >>
  metis_tac[finite_integral_domain_period_exists, integral_domain_nonzero_mult_property, NOT_ZERO_LT_ZERO]);

(* Theorem: FiniteIntegralDomain r ==> !x. x IN R ==> ((order f* x = 0) <=> (x = #0)) *)
(* Proof:
   If part: x IN R /\ forder x = 0 ==> x = #0
      By contradiction, suppose x <> #0.
      Then x IN R+                      by ring_nonzero_eq
       and forder x <> 0                by integral_domain_order_nonzero
      This contradicts forder x = 0.
   Only-if part: forder #0 = 0, true    by integral_domain_order_zero
*)
val integral_domain_order_eq_0 = store_thm(
  "integral_domain_order_eq_0",
  ``!r:'a ring. FiniteIntegralDomain r ==> !x. x IN R ==> ((order f* x = 0) <=> (x = #0))``,
  rpt (stripDup[FiniteIntegralDomain_def]) >>
  rw[EQ_IMP_THM] >-
  metis_tac[integral_domain_order_nonzero, ring_nonzero_eq] >>
  rw[integral_domain_order_zero]);

(* ------------------------------------------------------------------------- *)
(* Integral Domain Characteristic.                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: IntegralDomain r ==> (char r = 0) \/ prime (char r) *)
(* Proof:
   If char r = 0, it is trivial.
   If char r <> 0,
   first note that  #1 <> #0      by integral_domain_one_ne_zero
   Hence char r <> 1              by char_property
   Now proceed by contradication.
   Let p be a prime that divides (char r), 1 < p < (char r).
   i.e.  char r = k * p           with k < (char r).
   then  ##(char r) = #0          by char_property
   means  ##(k * p) = #0          by substitution
   or   ## k * ## p = #0          by ring_num_mult
   ==>  ## k = #0  or ## p = #0   by integral_domain_zero_product
   Either case, this violates the minimality of (char r) given by char_minimal.
*)
val integral_domain_char = store_thm(
  "integral_domain_char",
  ``!r:'a ring. IntegralDomain r ==> (char r = 0) \/ (prime (char r))``,
  rpt strip_tac >>
  Cases_on `char r = 0` >-
  rw_tac std_ss[] >>
  rw_tac std_ss[] >>
  `Ring r /\ #1 <> #0` by rw[integral_domain_is_ring] >>
  `char r <> 1` by metis_tac[char_property, ring_num_1] >>
  (spose_not_then strip_assume_tac) >>
  `?p. prime p /\ p divides (char r)` by rw_tac std_ss[PRIME_FACTOR] >>
  `?k. char r = k * p` by rw_tac std_ss[GSYM divides_def] >>
  `k divides (char r)` by metis_tac[divides_def, MULT_COMM] >>
  `0 < p /\ 1 < p` by rw_tac std_ss[PRIME_POS, ONE_LT_PRIME] >>
  `0 <> k` by metis_tac[MULT] >>
  `0 < k /\ p <> 1` by decide_tac >>
  `p <= char r /\ k <= char r` by rw_tac std_ss[DIVIDES_LE] >>
  `p <> char r` by metis_tac[] >>
  `k <> char r` by metis_tac[MULT_EQ_ID, MULT_COMM] >>
  `p < char r /\ k < char r /\ 0 < char r` by decide_tac >>
  `#0 = ##(char r)` by rw_tac std_ss[char_property] >>
  `_ = ## k * ## p` by rw_tac std_ss[ring_num_mult] >>
  metis_tac[integral_domain_zero_product, char_minimal, ring_num_element]);

(* ------------------------------------------------------------------------- *)
(* Primes are irreducible in an Integral Domain                              *)
(* ------------------------------------------------------------------------- *)

Theorem prime_is_irreducible:
  !r p. IntegralDomain r /\ p IN r.carrier /\ ring_prime r p
        /\ p <> r.sum.id /\ ~Unit r p
        ==> irreducible r p
Proof
  rw[ring_prime_def]
  \\ simp[irreducible_def, ring_nonzero_def]
  \\ `Ring r` by fs[IntegralDomain_def]
  \\ rw[]
  \\ fs[ring_divides_def, PULL_EXISTS]
  \\ simp[Invertibles_carrier, monoid_invertibles_element]
  \\ Cases_on`x = #0` \\ gs[]
  \\ Cases_on`y = #0` \\ gs[]
  \\ first_x_assum(qspecl_then[`x`,`y`,`#1`]mp_tac)
  \\ simp[] \\ strip_tac
  >- (
    `x = x * (s * y)` by metis_tac[ring_mult_assoc, ring_mult_comm]
    \\ `#1 * x = x /\ x * #1 = x` by metis_tac[ring_mult_rone, ring_mult_lone]
    \\ `x = (s * y) * x` by metis_tac[ring_mult_comm, ring_mult_element]
    \\ qspec_then`r`mp_tac integral_domain_mult_lcancel
    \\ impl_tac >- simp[]
    \\ disch_then(qspecl_then[`x`,`#1`,`s * y`]mp_tac) \\ simp[]
    \\ metis_tac[ring_mult_comm] )
  >- (
    `y = y * (s * x)` by metis_tac[ring_mult_assoc, ring_mult_comm]
    \\ `#1 * y = y /\ y * #1 = y` by metis_tac[ring_mult_rone, ring_mult_lone]
    \\ `y = (s * x) * y` by metis_tac[ring_mult_comm, ring_mult_element]
    \\ qspec_then`r`mp_tac integral_domain_mult_lcancel
    \\ impl_tac >- simp[]
    \\ disch_then(qspecl_then[`y`,`#1`,`s * x`]mp_tac) \\ simp[]
    \\ metis_tac[ring_mult_comm] )
QED

(* ------------------------------------------------------------------------- *)
(* Prime factorizations are unique (up to order and associates)              *)
(* ------------------------------------------------------------------------- *)

Theorem integral_domain_divides_prime:
  !r p x. IntegralDomain r /\ x IN r.carrier /\ p IN r.carrier /\
          p <> r.sum.id /\ ring_prime r p /\ ~Unit r p /\ ~Unit r x /\
          ring_divides r x p
          ==>
          ring_associates r x p
Proof
  rw[ring_associates_def]
  \\ `Ring r` by metis_tac[IntegralDomain_def]
  \\ drule_then (drule_then drule) prime_is_irreducible
  \\ simp[]
  \\ rw[irreducible_def]
  \\ fs[ring_divides_def]
  \\ `Unit r s` by metis_tac[]
  \\ pop_assum mp_tac
  \\ simp[ring_unit_property]
  \\ simp[PULL_EXISTS]
  \\ rpt strip_tac
  \\ qexists_tac`v`
  \\ qexists_tac`s`
  \\ simp[]
  \\ simp[Once ring_mult_comm]
  \\ simp[GSYM ring_mult_assoc]
  \\ metis_tac[ring_mult_comm, ring_mult_lone]
QED

Theorem integral_domain_prime_factors_unique:
  IntegralDomain r ==>
  !l1 l2.
  (!m. MEM m l1 ==>
       m IN r.carrier /\ ring_prime r m /\ m <> r.sum.id /\ ~Unit r m) /\
  (!m. MEM m l2 ==>
       m IN r.carrier /\ ring_prime r m /\ m <> r.sum.id /\ ~Unit r m) /\
  ring_associates r
    (GBAG r.prod (LIST_TO_BAG l1))
    (GBAG r.prod (LIST_TO_BAG l2)) ==>
  ?l3. PERM l2 l3 /\ LIST_REL (ring_associates r) l1 l3
Proof
  strip_tac
  \\ `Ring r` by metis_tac[IntegralDomain_def]
  \\ Induct \\ simp[]
  >- (
    Cases \\ rw[]
    \\ spose_not_then strip_assume_tac
    \\ pop_assum mp_tac
    \\ DEP_REWRITE_TAC[GBAG_INSERT]
    \\ simp[SUBSET_DEF, IN_LIST_TO_BAG]
    \\ conj_asm1_tac >- metis_tac[Ring_def]
    \\ simp[ring_associates_def]
    \\ rpt strip_tac
    \\ qmatch_asmsub_abbrev_tac`GBAG r.prod b0`
    \\ `GBAG r.prod b0 IN r.prod.carrier`
    by ( irule GBAG_in_carrier \\ simp[SUBSET_DEF, Abbr`b0`, IN_LIST_TO_BAG] )
    \\ `!v. v IN r.carrier ==> r.prod.id <> r.prod.op h v`
    by metis_tac[ring_unit_property]
    \\ first_x_assum(qspec_then`r.prod.op s (GBAG r.prod b0)`mp_tac)
    \\ rfs[]
    \\ metis_tac[ring_unit_property, ring_mult_comm, ring_mult_assoc] )
  \\ rpt strip_tac
  \\ pop_assum mp_tac
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[SUBSET_DEF, IN_LIST_TO_BAG]
  \\ conj_asm1_tac >- metis_tac[Ring_def]
  \\ `GBAG r.prod (LIST_TO_BAG l1) IN r.prod.carrier`
  by ( irule GBAG_in_carrier \\ simp[SUBSET_DEF, IN_LIST_TO_BAG] )
  \\ `GBAG r.prod (LIST_TO_BAG l2) IN r.prod.carrier`
  by ( irule GBAG_in_carrier \\ simp[SUBSET_DEF, IN_LIST_TO_BAG] )
  \\ strip_tac
  \\ `ring_divides r h (GBAG r.prod (LIST_TO_BAG l2))`
  by (
    simp[ring_divides_def] \\ rfs[ring_associates_def]
    \\ pop_assum mp_tac \\ simp[ring_unit_property]
    \\ strip_tac
    \\ qexists_tac`r.prod.op (GBAG r.prod (LIST_TO_BAG l1)) v`
    \\ simp[]
    \\ last_x_assum(mp_tac o Q.AP_TERM`r.prod.op v`)
    \\ simp[GSYM ring_mult_assoc]
    \\ simp[Once ring_mult_comm]
    \\ simp[GSYM ring_mult_assoc]
    \\ metis_tac[ring_mult_comm, ring_mult_lone])
  \\ simp[PULL_EXISTS]
  \\ `SET_OF_BAG (LIST_TO_BAG l2) SUBSET r.carrier`
  by simp[SUBSET_DEF, IN_LIST_TO_BAG]
  \\ `?q. BAG_IN q (LIST_TO_BAG l2) /\ ring_divides r h q`
  by metis_tac[ring_prime_divides_product, FINITE_LIST_TO_BAG]
  \\ fs[IN_LIST_TO_BAG]
  \\ `ring_associates r h q` by metis_tac[integral_domain_divides_prime]
  \\ qmatch_asmsub_rename_tac`ring_divides r p q`
  \\ drule (#1(EQ_IMP_RULE MEM_SPLIT_APPEND_first))
  \\ strip_tac
  \\ `PERM l2 (q::(pfx++sfx))`
  by (
    simp[Once PERM_SYM]
    \\ rewrite_tac[GSYM APPEND_ASSOC, APPEND]
    \\ irule CONS_PERM
    \\ simp[] )
  \\ `LIST_TO_BAG l2 = LIST_TO_BAG (q::(pfx++sfx))`
  by simp[PERM_LIST_TO_BAG]
  \\ `GBAG r.prod (LIST_TO_BAG l2) =
      r.prod.op q (GBAG r.prod (LIST_TO_BAG (pfx++sfx)))`
  by (
    simp[]
    \\ DEP_REWRITE_TAC[GBAG_INSERT]
    \\ fs[SUBSET_DEF] )
  \\ `?s. Unit r s /\ p = s * q` by metis_tac[ring_associates_def]
  \\ qmatch_asmsub_abbrev_tac`r.prod.op p p1`
  \\ qmatch_asmsub_abbrev_tac`rassoc (p * p1) p2`
  \\ `?s2. Unit r s2 /\ p * p1 = s2 * p2` by metis_tac[ring_associates_def]
  \\ qmatch_asmsub_abbrev_tac`q * q1`
  \\ `q1 IN r.prod.carrier`
  by ( qunabbrev_tac`q1` \\ irule GBAG_in_carrier \\ fs[SUBSET_DEF] )
  \\ `s IN r.carrier /\ s2 IN r.carrier` by metis_tac[ring_unit_property]
  \\ `r.prod.carrier = r.carrier` by simp[]
  \\ `?s3. s3 IN r.carrier /\ s * s3 = #1` by metis_tac[ring_unit_property]
  \\ `s3 * (s * q * p1) = s3 * (s2 * q * q1)` by metis_tac[ring_mult_assoc]
  \\ `q IN r.carrier` by fs[SUBSET_DEF]
  \\ `s3 * s * q * p1 = s3 * s2 * q * q1` by (
    fs[] \\ rfs[ring_mult_assoc] )
  \\ `s3 * s = #1` by simp[ring_mult_comm]
  \\ `q * p1 = s3 * s2 * q * q1` by metis_tac[ring_mult_lone]
  \\ `unit (s3 * s2)` by metis_tac[ring_unit_mult_eq_unit, ring_unit_property]
  \\ `q * p1 = q * (s3 * s2) * q1` by metis_tac[ring_mult_comm, ring_mult_assoc]
  \\ `q * p1 = q * ((s3 * s2) * q1)` by rfs[ring_mult_assoc]
  \\ qmatch_asmsub_abbrev_tac`unit u`
  \\ `ring_sub r (q * p1) (q * (u * q1)) = #0`
  by metis_tac[ring_sub_eq_zero, ring_mult_element]
  \\ `q * (ring_sub r p1 (u * q1)) = #0`
  by (
    DEP_REWRITE_TAC[GSYM ring_mult_rsub]
    \\ simp[] \\ fs[] )
  \\ `MEM q l2` by simp[]
  \\ `ring_prime r q /\ q <> #0 /\ ~Unit r q` by metis_tac[]
  \\ `u IN r.carrier` by metis_tac[ring_unit_property]
  \\ `u * q1 IN r.carrier` by metis_tac[ring_mult_element]
  \\ `ring_sub r p1 (u * q1) = #0`
  by metis_tac[IntegralDomain_def, ring_sub_element]
  \\ `p1 = u * q1` by metis_tac[ring_sub_eq_zero]
  \\ qexists_tac`q`
  \\ first_x_assum(qspec_then`pfx ++ sfx`mp_tac)
  \\ impl_tac
  >- (
    conj_tac >- (fs[] \\ metis_tac[])
    \\ metis_tac[ring_associates_def] )
  \\ strip_tac
  \\ qexists_tac`l3`
  \\ reverse conj_tac >- simp[]
  \\ irule PERM_TRANS
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ irule PERM_MONO
  \\ simp[]
QED

(* ------------------------------------------------------------------------- *)
(* Principal Ideals in Integral Domain                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Two principal ideals are equal iff the elements are associates:
            p IN R /\ q IN R ==> (<p> = <q> <=> ?u. unit u /\ (p = q * u) *)
(* Proof:
   If part: <p> = <q> ==> ?u. unit u /\ (p = q * u)
   This part requires an integral domain, not just a ring.
   <p> = <q> ==> <p>.carrier = <q>.carrier                        by principal_ideal_ideal, ideal_eq_ideal
   p IN <p>.carrier = <q>.carrier ==> ?u. u IN R /\ (p = q * u)   by principal_ideal_element
   q IN <q>.carrier = <p>.carrier ==> ?v. y IN R /\ (q = p * v)   by principal_ideal_element
   Hence q = p * v = q * u * v.
   In an integral domain, left-cancellation gives: q = #0 or #1 = u * v, hence u is a unit.
   The case q = #0 means p = q * u = #0, and u can take #1.
   Only-if part:
   True by principal_ideal_eq_principal_ideal.
*)
val principal_ideal_equal_principal_ideal = store_thm(
  "principal_ideal_equal_principal_ideal",
  ``!r:'a ring. IntegralDomain r ==> !p q. p IN R /\ q IN R ==> ((<p> = <q>) <=> ?u. unit u /\ (p = q * u))``,
  rewrite_tac[EQ_IMP_THM] >>
  ntac 2 strip_tac >>
  `Ring r` by rw[integral_domain_is_ring] >>
  rpt strip_tac >| [
    `<p> << r /\ <q> << r` by rw[principal_ideal_ideal] >>
    `<p>.carrier = <q>.carrier` by rw[ideal_eq_ideal] >>
    `?u. u IN R /\ (p = q * u)` by metis_tac[principal_ideal_has_element, principal_ideal_element] >>
    `?v. v IN R /\ (q = p * v)` by metis_tac[principal_ideal_has_element, principal_ideal_element] >>
    `#1 IN R /\ u * v IN R` by rw[] >>
    `q * #1 = q` by rw[] >>
    `_ = q * u * v` by metis_tac[] >>
    `_ = q * (u * v)` by rw[ring_mult_assoc] >>
    `(q = #0) \/ (u * v = #1)` by metis_tac[integral_domain_mult_lcancel] >| [
      `p = #0` by rw[] >>
      `unit #1` by rw[] >>
      metis_tac[ring_mult_rone],
      metis_tac[ring_unit_property]
    ],
    metis_tac[principal_ideal_eq_principal_ideal]
  ]);

(* ------------------------------------------------------------------------- *)
(* Integral Domain Instances Documentation                                   *)
(* ------------------------------------------------------------------------- *)
(* Integral Domain is a special type of Ring, with data type:
   The generic symbol for ring data is r.
   r.carrier = Carrier set of Ring, overloaded as R.
   r.sum     = Addition component of Ring, binary operation overloaded as +.
   r.prod    = Multiplication component of Ring, binary operation overloaded as *.
*)
(* Definitions and Theorems (# are exported):

   The Trivial Integral Domain (GF 2):
   trivial_integal_domain_def |- !e0 e1. trivial_integal_domain e0 e1 =
         <|carrier := {e0; e1};
               sum :=  <|carrier := {e0; e1};
                              id := e0;
                              op := (\x y. if x = e0 then y else if y = e0 then x else e0)|>;
              prod := <|carrier := {e0; e1};
                             id := e1;
                             op := (\x y. if x = e0 then e0 else if y = e0 then e0 else e1)|> |>
   trivial_integral_domain    |- !e0 e1. e0 <> e1 ==> FiniteIntegralDomain (trivial_integal_domain e0 e1)

   Multiplication in Modulo of prime p:
   ZP_def                     |- !p. ZP p = <|carrier := count p; sum := add_mod p; prod := times_mod p|>
   ZP_integral_domain         |- !p. prime p ==> IntegralDomain (ZP p)
   ZP_finite                  |- !p. FINITE (ZP p).carrier
   ZP_finite_integral_domain  |- !p. prime p ==> FiniteIntegralDomain (ZP p)
*)
(* ------------------------------------------------------------------------- *)
(* The Trivial Integral Domain = GF(2) = {|0|, |1|}.                         *)
(* ------------------------------------------------------------------------- *)

val trivial_integal_domain_def = zDefine`
  (trivial_integal_domain e0 e1) : 'a ring =
   <| carrier := {e0; e1};
      sum := <| carrier := {e0; e1};
                id := e0;
                op := (\x y. if x = e0 then y
                             else if y = e0 then x
                             else e0) |>;
      prod := <| carrier := {e0; e1};
                id := e1;
                op := (\x y. if x = e0 then e0
                                else if y = e0 then e0
                                else e1) |>
    |>
`;

(* Theorem: {|0|, |1|} is indeed a integral domain. *)
(* Proof: by definition, the integral domain tables are:

   +    |0| |1|          *  |0| |1|
   ------------         -----------
   |0|  |0| |1|         |0| |0| |0|
   |1|  |1| |0|         |1| |0| |1|

*)
val trivial_integral_domain = store_thm(
  "trivial_integral_domain",
  ``!e0 e1. e0 <> e1 ==> FiniteIntegralDomain (trivial_integal_domain e0 e1)``,
  rw_tac std_ss[FiniteIntegralDomain_def] THENL [
    `!x a b. x IN {a; b} <=> ((x = a) \/ (x = b))` by rw[] THEN
    rw_tac std_ss[IntegralDomain_def, Ring_def] THENL [
      rw_tac std_ss[AbelianGroup_def, group_def_alt, trivial_integal_domain_def] THEN
      metis_tac[],
      rw_tac std_ss[AbelianMonoid_def, Monoid_def, trivial_integal_domain_def] THEN
      rw_tac std_ss[],
      rw_tac std_ss[trivial_integal_domain_def],
      rw_tac std_ss[trivial_integal_domain_def],
      (rw_tac std_ss[trivial_integal_domain_def] THEN metis_tac[]),
      rw_tac std_ss[trivial_integal_domain_def],
      rw_tac std_ss[trivial_integal_domain_def]
    ],
    rw[trivial_integal_domain_def]
  ]);

(* ------------------------------------------------------------------------- *)
(* Z_p - Multiplication in Modulo of prime p.                                *)
(* ------------------------------------------------------------------------- *)

(* Multiplication in Modulo of prime p *)
val ZP_def = zDefine`
  ZP p :num ring =
   <| carrier := count p;
          sum := add_mod p;
         prod := times_mod p
    |>
`;
(*
- type_of ``ZP p``;
> val it = ``:num ring`` : hol_type
*)

(* Theorem: ZP p is an integral domain for prime p. *)
(* Proof: check definitions.
   The no-zero divisor property is given by EUCLID_LEMMA for prime p.
*)
val ZP_integral_domain = store_thm(
  "ZP_integral_domain",
  ``!p. prime p ==> IntegralDomain (ZP p)``,
  rpt strip_tac >>
  `0 < p /\ 1 < p` by rw_tac std_ss[PRIME_POS, ONE_LT_PRIME] >>
  rw_tac std_ss[IntegralDomain_def, Ring_def] >-
  rw_tac std_ss[ZP_def, add_mod_abelian_group] >-
  rw_tac std_ss[ZP_def, times_mod_abelian_monoid] >-
  rw_tac std_ss[ZP_def, add_mod_def, count_def] >-
  rw_tac std_ss[ZP_def, times_mod_def] >-
 (pop_assum mp_tac >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw_tac std_ss[ZP_def, add_mod_def, times_mod_def, count_def, GSPECIFICATION] >>
  metis_tac[LEFT_ADD_DISTRIB, MOD_PLUS, MOD_TIMES2, LESS_MOD, MOD_MOD]) >-
 (rw_tac std_ss[ZP_def, add_mod_def, times_mod_def] >>
  decide_tac) >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  rw_tac std_ss[ZP_def, add_mod_def, times_mod_def, count_def, GSPECIFICATION] >>
  rw_tac std_ss[EUCLID_LEMMA, LESS_MOD]);

(* Theorem: (ZP p).carrier is FINITE. *)
(* Proof: by FINITE_COUNT. *)
val ZP_finite = store_thm(
  "ZP_finite",
  ``!p. FINITE (ZP p).carrier``,
  rw[ZP_def]);

(* Theorem: ZP p is a FINITE Integral Domain for prime p. *)
(* Proof: by ZP_integral_domain and ZP_finite. *)
val ZP_finite_integral_domain = store_thm(
  "ZP_finite_integral_domain",
  ``!p. prime p ==> FiniteIntegralDomain (ZP p)``,
  rw_tac std_ss[ZP_integral_domain, ZP_finite, FiniteIntegralDomain_def]);

(* ------------------------------------------------------------------------- *)
(* Integers Z is the prototype Integral Domain.                              *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
