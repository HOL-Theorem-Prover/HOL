(* ------------------------------------------------------------------------ *)
(* Ring Theory                                                              *)
(* ------------------------------------------------------------------------ *)

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

(* Get dependent theories in lib *)
(* val _ = load "helperFunctionTheory"; *)
(* (* val _ = load "helperNumTheory"; -- in helperFunctionTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in helperFunctionTheory *) *)
open helperNumTheory helperSetTheory helperFunctionTheory;

(* Get arithmetic for Ring characteristics *)
open pred_setTheory arithmeticTheory dividesTheory gcdTheory;

(* Get dependent theories local *)
(* (* val _ = load "monoidTheory"; *) *)
(* val _ = load "groupOrderTheory"; (* loads monoidTheory implicitly *) *)
open monoidTheory groupTheory;
open monoidOrderTheory groupOrderTheory;


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
    monoid_exp_def |> ISPEC “(r:'a ring).sum” |> ISPEC “#1” |> ISPEC “0”
                   |> SIMP_RULE bool_ss [FUNPOW_0] |> GEN “r:'a ring”
(* val ring_num_0 = |- !r. ##0 = #0: thm *)

(* Obtain another theorem *)
Theorem ring_num_one =
    monoid_exp_def |> ISPEC ``(r:'a ring).sum`` |> ISPEC ``#1`` |> ISPEC ``1``
                   |> SIMP_RULE bool_ss [FUNPOW_1] |> GEN ``r:'a ring``
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
  rw_tac std_ss[DECIDE ``3 + 3 = 6``]);

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

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
