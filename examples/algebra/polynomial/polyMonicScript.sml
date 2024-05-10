(* ------------------------------------------------------------------------- *)
(* Monic Polynomials.                                                        *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polyMonic";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory numberTheory combinatoricsTheory
     rich_listTheory dividesTheory gcdTheory;

open monoidTheory groupTheory ringTheory ringUnitTheory;

open polynomialTheory polyWeakTheory polyRingTheory;
open polyDivisionTheory; (* for ulead, pmonic and poly_mod theorems. *)

(* val _ = load "polyFieldTheory"; *)
open polyFieldTheory;
open fieldTheory;

(* ------------------------------------------------------------------------- *)
(* Monic Polynomial Documentation                                            *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   monic        = poly_monic r
   X            = |1| >> 1
   ###          = (poly_ring r).sum.exp |1|
   |n|          = (poly_ring r).sum.exp |1| n = ###n
   |c|          = (poly_ring r).sum.exp |1| c = ###c
   Unity r n    = X ** n - |1|
   unity n      = Unity r
   Master r n   = X ** n - X
   master n     = Master r
   Monic r      = poly_monic r
   Deg   r      = poly_deg r
   Lead  r      = poly_lead r
   Ulead r p    = Poly r p /\ Unit r (Lead r p)
   Pmonic r p   = Poly r p /\ Unit r (Lead r p) /\ 0 < Deg r p
*)
(* Definitions and Theorems (# are exported):

   Monic Polynomials:
   poly_monic_def        |- !r p. monic p <=> poly p /\ (lead p = #1)
#  poly_monic_poly       |- !r p. monic p ==> poly p
#  poly_monic_lead       |- !r p. monic p ==> (lead p = #1)
   poly_monic_zero       |- !r. monic |0| <=> (#1 = #0)
   poly_monic_nonzero    |- !r. #1 <> #0 ==> !p. monic p ==> p <> |0|

#  poly_monic_one        |- !r. Ring r ==> monic |1|
   poly_monic_mult_monic |- !r. Ring r ==> !p q. monic p /\ monic q ==> monic (p * q)
   poly_monic_deg_mult   |- !r. Ring r ==> !p q. monic p /\ monic q ==> (deg (p * q) = deg p + deg q)
   poly_monic_monic_mult |- !r. Ring r ==> !p q. monic p /\ poly q /\ monic (p * q) ==> monic q
   poly_monic_monic_mult_comm
                         |- !r. Ring r ==> !p q. monic p /\ poly q /\ monic (q * p) ==> monic q

   poly_monic_deg_0      |- !r. Ring r ==> !p. monic p /\ (deg p = 0) <=> (p = |1|)
   poly_monic_ulead      |- !r. Ring r ==> !p. monic p ==> ulead p
   poly_monic_pmonic     |- !r. Ring r ==> !p. monic p /\ 0 < deg p ==> pmonic p
   weak_mult_monic_monic |- !r. Ring r /\ #1 <> #0 ==> !p q. monic p /\ monic q ==> monic (p o q)

   Monic Polynomial Exponentiaton:
#  poly_monic_exp_monic   |- !r. Ring r ==> !p. monic p ==> !n. monic (p ** n)
#  poly_monic_deg_exp     |- !r. Ring r ==> !p. monic p ==> !n. deg (p ** n) = n * deg p
#  poly_monic_shift_monic |- !r. Ring r ==> !p. monic p ==> !n. monic (p >> n)
   poly_monic_exp_eq      |- !r. Ring r ==> !p. monic p /\ 0 < deg p ==> !n m. (p ** n = p ** m) <=> (n = m)
   poly_monic_exp_eq_one  |- !r. Ring r ==> !p. monic p ==> !n. (p ** n = |1|) <=> (p = |1|) \/ (n = 0)
   poly_monic_exp_eq_self |- !r. Ring r ==> !p. monic p /\ 0 < deg p ==> !n. (p ** n = p) <=> (n = 1)

   Scalar Polynomials:
   weak_ring_sum_c      |- !r. Ring r ==> !c. weak [##c]
   poly_ring_sum_c      |- !r. Ring r ==> !c. |c| = chop [##c]
   poly_ring_sum_0      |- !r. |0| = ### 0
   poly_ring_sum_1      |- !r. Ring r ==> ( |1| = ### 1)
   poly_one_sum_n_eq    |- !r. Ring r ==> !c. |c| = if ##c = #0 then |0| else [##c]
   poly_sum_num_poly    |- !r. Ring r ==> !c. poly |c|
#  poly_ring_sum        |- !r. Ring r ==> !c. poly |c|
   poly_deg_sum_num     |- !r. Ring r ==> !c. deg |c| = 0
   poly_lead_one_sum_n  |- !r. Ring r ==> !c. lead |c| = ##c
   poly_eval_one_sum_n  |- !r. Ring r ==> !x. x IN R ==> !c. eval |c| x = ##c
   poly_sum_num_eq      |- !r. Ring r ==> !n c. n < char r /\ c < char r ==> (( |n| = |c|) <=> (n = c))
   poly_sum_num_SUC     |- !r. Ring r ==> !c. ### (SUC c) = |1| + |c|
   poly_sum_num_SUC     |- !r. Ring r ==> !c. ### (SUC c) = |c| + |1|

   Involving Polynomial X:
#  poly_X_def             |- !r. Ring r /\ #1 <> #0 ==> (X = [#0; #1])
   poly_X_alt             |- !r. Ring r /\ #1 <> #0 ==> (X = [#1] >> 1)
   weak_X                 |- !r. Ring r ==> weak X
#  poly_X                 |- !r. Ring r ==> poly X
   poly_deg_X             |- !r. Ring r /\ #1 <> #0 ==> (deg X = 1)
#  poly_lead_X            |- !r. Ring r ==> (lead X = #1)
   poly_monic_X           |- !r. Ring r ==> monic X
   poly_mult_X            |- !r. Ring r ==> !p. poly p ==> (p * X = p >> 1)
   poly_mult_X_comm       |- !r. Ring r ==> !p. poly p ==> (X * p = p >> 1)
   poly_monic_deg_1       |- !r. Ring r /\ #1 <> #0 ==>
                             !p. monic p /\ (deg p = 1) <=> ?c. c IN R /\ (p = X + chop [c]
   poly_X_nonzero         |- !r. Ring r /\ #1 <> #0 ==> X <> |0|
   poly_eval_X            |- !r. Ring r ==> !x. x IN R ==> (eval X x = x)
   weak_mult_X            |- !r. Ring r /\ #1 <> #0 ==> !p. weak p ==> (X o p = p >> 1)
   weak_mult_X_comm       |- !r. Ring r /\ #1 <> #0 ==> !p. weak p ==> (p o X = p >> 1)

   Involving Polynomial X ** n:
   poly_X_exp             |- !r. Ring r ==> !n. poly (X ** n)
   poly_X_exp_n           |- !r. Ring r /\ #1 <> #0 ==> !n. X ** n = [#1] >> n
   poly_X_exp_eq_shift    |- !r. Ring r ==> !n. X ** SUC n = X >> n
   poly_X_exp_eq          |- !r. Ring r /\ #1 <> #0 ==> !n m. (X ** n = X ** m) <=> (n = m)
   poly_deg_X_exp         |- !r. Ring r /\ #1 <> #0 ==> !n. deg (X ** n) = n
   poly_lead_X_exp        |- !r. Ring r ==> !n. lead (X ** n) = #1
   poly_X_exp_eq_one      |- !r. Ring r /\ #1 <> #0 ==> !n. (X ** n = |1|) <=> (n = 0)
   poly_cmult_X_exp_n     |- !r. Ring r /\ #1 <> #0 ==> !c. c IN R /\ c <> #0 ==> !n. c * X ** n = [c] >> n
   poly_X_exp_nonzero     |- !r. Ring r /\ #1 <> #0 ==> !n. X ** n <> |0|
   weak_X_exp_SUC         |- !r. Ring r /\ #1 <> #0 ==> !n. X ** SUC n = X o (X ** n)
   weak_X_exp_suc         |- !r. Ring r /\ #1 <> #0 ==> !n. X ** SUC n = (X ** n) o X
   weak_cmult_X_exp_n     |- !r. Ring r /\ #1 <> #0 ==> !c. c IN R ==> !n. c o (X ** n) = [c] >> n
   poly_X_exp_n_alt       |- !r. Ring r /\ #1 <> #0 ==> !n. X ** n = PAD_LEFT #0 (SUC n) [#1]

   Involving Polynomial X + |c|:
   poly_X_add_c           |- !r. Ring r ==> !c. poly (X + |c|)
   poly_X_add_c_list      |- !r. Ring r /\ #1 <> #0 ==> !c. X + |c| = [##c; #1]
   poly_deg_X_add_c       |- !r. Ring r /\ #1 <> #0 ==> !c. deg (X + |c|) = 1
   poly_lead_X_add_c      |- !r. Ring r ==> !c. lead (X + |c|) = #1
   poly_monic_X_add_c     |- !r. Ring r ==> !c. monic (X + |c|)
   poly_deg_X_add_c_exp_n |- !r. Ring r /\ #1 <> #0 ==> !n. deg ((X + |c|) ** n) = n
   poly_X_add_c_eq        |- !r. Ring r ==>
                             !n c. n < char r /\ c < char r ==> ((X + |n| = X + |c|) <=> (n = c))
   poly_X_add_c_image_element
                          |- !r. Ring r ==> !s p. p IN IMAGE (\c. X + |c|) s ==> poly p
   poly_monic_X_add_c_image_element
                          |- !r. Ring r ==> !s p. p IN IMAGE (\c. X + |c|) s ==> monic p
   poly_deg_X_add_c_image_element
                          |- !r. Ring r /\ #1 <> #0 ==>
                             !s p. p IN IMAGE (\c. X + |c|) s ==> (deg p = 1)
   poly_X_add_c_image_property
                          |- !r. Ring r ==> !s. FINITE s /\ MAX_SET s < char r ==>
                             !n. n < char r ==> (n IN s <=> X + |n| IN IMAGE (\c. X + |c|) s)

   Involving Polynomial X - |c|:
   poly_X_sub_c           |- !r. Ring r ==> !c. poly (X - |c|)
   poly_X_sub_c_list      |- !r. Ring r /\ #1 <> #0 ==> !c. X - |c| = [-##c; #1]
   poly_deg_X_sub_c       |- !r. Ring r /\ #1 <> #0 ==> !c. deg (X - |c|) = 1
   poly_lead_X_sub_c      |- !r. Ring r ==> !c. lead (X - |c|) = #1
   poly_monic_X_sub_c     |- !r. Ring r ==> !c. monic (X - |c|)
   poly_deg_X_sub_c_exp_n |- !r. Ring r /\ #1 <> #0 ==> !n. deg ((X - |c|) ** n) = n
   poly_X_sub_c_eq        |- !r. Ring r ==>
                             !n c. n < char r /\ c < char r ==> ((X - |n| = X - |c|) <=> (n = c))
   poly_X_sub_c_image_element
                          |- !r. Ring r ==> !s p. p IN IMAGE (\c. X - |c|) s ==> poly p
   poly_monic_X_sub_c_image_element
                          |- !r. Ring r ==> !s p. p IN IMAGE (\c. X - |c|) s ==> monic p
   poly_deg_X_sub_c_image_element
                          |- !r. Ring r /\ #1 <> #0 ==>
                             !s p. p IN IMAGE (\c. X - |c|) s ==> (deg p = 1)
   poly_X_sub_c_image_property
                          |- !r. Ring r ==> !s. FINITE s /\ MAX_SET s < char r ==>
                             !n. n < char r ==> (n IN s <=> X - |n| IN IMAGE (\c. X - |c|) s)

   Involving Polynomial X ** n + |c|:
   poly_X_exp_n_add_c_poly   |- !r. Ring r ==> !c n. poly (X ** n + |c|)
   poly_deg_X_exp_n_add_c    |- !r. Ring r /\ #1 <> #0 ==> !c n. deg (X ** n + |c|) = n
   poly_lead_X_exp_n_add_c   |- !r. Ring r ==> !c n. 0 < n ==> (lead (X ** n + |c|) = #1)
   poly_monic_X_exp_n_add_c  |- !r. Ring r ==> !c n. 0 < n ==> monic (X ** n + |c|)
   poly_eval_X_exp_n_add_c   |- !r. Ring r ==>
                                !x. x IN R ==> !c n. eval (X ** n + |c|) x = x ** n + ##c
   poly_X_exp_n_add_c        |- !r. Ring r ==> !c. ##c <> #0 ==>
                                !n. 0 < n ==> (X ** n + |c| = [##c] || [#1] >> n)
   poly_X_exp_n_add_c_alt    |- !r. Ring r /\ #1 <> #0 ==>
                                !n. 0 < n ==> !c. X ** n + |c| = ##c::PAD_LEFT #0 n [#1]
   poly_coeff_X_exp_n_add_c  |- !r. Ring r /\ #1 <> #0 ==>
                                !n k c. 0 < k /\ k < n ==> ((X ** n + |c|) ' k = #0)
   poly_mod_X_exp_n_add_c    |- !r. Ring r /\ #1 <> #0 ==>
                                !c n. 0 < n ==> (X ** n == -|c|) (pm (X ** n + |c|))

   Involving Polynomial X ** n - |c|:
   poly_X_exp_n_sub_c_poly   |- !r. Ring r ==> !c n. poly (X ** n - |c|)
   poly_deg_X_exp_n_sub_c    |- !r. Ring r /\ #1 <> #0 ==> !c n. deg (X ** n - |c|) = n
   poly_lead_X_exp_n_sub_c   |- !r. Ring r ==> !c n. 0 < n ==> (lead (X ** n - |c|) = #1)
   poly_monic_X_exp_n_sub_c  |- !r. Ring r ==> !c n. 0 < n ==> monic (X ** n - |c|)
   poly_eval_X_exp_n_sub_c   |- !r. Ring r ==>
                                !x. x IN R ==> !c n. eval (X ** n - |c|) x = x ** n - ##c
   poly_X_exp_n_sub_c        |- !r. Ring r ==> !c. ##c <> #0 ==>
                                !n. 0 < n ==> (X ** n - |c| = [-##c] || [#1] >> n)
   poly_X_exp_n_sub_c_alt    |- !r. Ring r /\ #1 <> #0 ==>
                                !n. 0 < n ==> !c. X ** n - |c| = -##c::PAD_LEFT #0 n [#1]
   poly_coeff_X_exp_n_sub_c  |- !r. Ring r /\ #1 <> #0 ==>
                                !n k c. 0 < k /\ k < n ==> ((X ** n - |c|) ' k = #0)
   poly_mod_X_exp_n_sub_c    |- !r. Ring r /\ #1 <> #0 ==>
                                !c n. 0 < n ==> (X ** n == |c|) (pm (X ** n - |c|))

   Pseudo-monic Polynomials:
   poly_pmonic_X_add_c        |- !r. Ring r /\ #1 <> #0 ==> !c. pmonic (X + |c|)
   poly_pmonic_X_sub_c        |- !r. Ring r /\ #1 <> #0 ==> !c n. pmonic (X - |c|)
   poly_pmonic_X_exp_n_add_c  |- !r. Ring r /\ #1 <> #0 ==> !c n. 0 < n ==> pmonic (X ** n + |c|)
   poly_pmonic_X_exp_n_sub_c  |- !r. Ring r /\ #1 <> #0 ==> !c n. 0 < n ==> pmonic (X ** n - |c|)
   poly_X_add_c_factor        |- !r. Ring r /\ #1 <> #0 ==>
                                 !c n. ((X + |c|) % (X + |n|) = |0|) <=> (X + |c| = X + |n|)
   poly_X_sub_c_factor        |- !r. Ring r /\ #1 <> #0 ==>
                                 !c n. ((X - |c|) % (X - |n|) = |0|) <=> (X - |c| = X - |n|)

   The Unity Polynomial:
#  poly_unity_poly      |- !r. Ring r ==> !n. poly (unity n)
#  poly_unity_0         |- !r. Ring r ==> (unity 0 = |0|)
#  poly_unity_1         |- !r. Ring r ==> (unity 1 = X - |1|)
   poly_unity_eq_zero   |- !r. Ring r /\ #1 <> #0 ==> !n. (unity n = |0|) <=> (n = 0)
#  poly_unity_deg       |- !r. Ring r /\ #1 <> #0 ==> !n. deg (unity n) = n
#  poly_unity_lead      |- !r. Ring r ==> !n. 0 < n ==> (lead (unity n) = #1)
#  poly_unity_monic     |- !r. Ring r ==> !n. 0 < n ==> monic (unity n)
   poly_unity_ulead     |- !r. Ring r ==> !n. 0 < n ==> ulead (unity n)
   poly_unity_pmonic    |- !r. Ring r /\ #1 <> #0 ==> !n. 0 < n ==> pmonic (unity n)
   poly_unity_eq        |- !r. Ring r /\ #1 <> #0 ==> !m n. (unity m = unity n) <=> (m = n)

   Master Polynomial:
#  poly_master_poly     |- !r. Ring r ==> !n. poly (master n)
#  poly_master_0        |- !r. master 0 = |1| - X
#  poly_master_1        |- !r. Ring r ==> (master 1 = |0|)
   poly_master_eq_zero  |- !r. Ring r /\ #1 <> #0 ==> !n. (master n = |0|) <=> (n = 1)
#  poly_master_deg      |- !r. Ring r /\ #1 <> #0 ==> !n. 1 < n ==> (deg (master n) = n)
#  poly_master_lead     |- !r. Ring r ==> !n. 1 < n ==> (lead (master n) = #1)
#  poly_master_monic    |- !r. Ring r ==> !n. 1 < n ==> monic (master n)
   poly_master_pmonic   |- !r. Ring r /\ #1 <> #0 ==> !n. 1 < n ==> pmonic (master n)
   poly_master_eq       |- !r. Ring r /\ #1 <> #0 ==> !m n. (master m = master n) <=> (m = n)

   Polynomial Monic Factor:
   poly_field_monic_nonzero    |- !r. Field r ==> !p. monic p ==> p <> |0|
   poly_field_make_monic       |- !r. Field r ==> !p. poly p ==> ?c q. c IN R /\ monic q /\ (p = c * q)
   poly_monic_cmult_factor     |- !r. Field r ==> !p. poly p /\ p <> |0| ==>
                                  ?c q. c IN R /\ c <> #0 /\ monic q /\ (deg q = deg p) /\ (p = c * q)
   poly_monic_cmult_by_factor  |- !r. Field r ==> !p. poly p /\ p <> |0| ==>
                                  ?c q. c IN R /\ c <> #0 /\ monic q /\ (deg q = deg p) /\ (q = c * p)
   poly_monic_by_cmult         |- !r. Field r ==> !p. poly p /\ p <> |0| ==> monic ( |/ (lead p) * p)

   Polynomial Remainder of Unity:
   poly_unity_mod_const           |- !r. Ring r /\ #1 <> #0 ==> !m. 0 < m ==> !c. |c| % unity m = |c|
   poly_unity_mod_X_exp_deg       |- !r. Ring r /\ #1 <> #0 ==> !m. 0 < m ==> (X ** m % unity m = |1|)
   poly_unity_mod_X_exp_n         |- !r. Ring r /\ #1 <> #0 ==> !m. 0 < m ==>
                                     !n. X ** n % unity m = X ** (n MOD m)
   poly_unity_mod_X_exp_n_add_c   |- !r. Ring r /\ #1 <> #0 ==> !m. 0 < m ==>
                                     !n c. (X ** n + |c|) % unity m = X ** (n MOD m) + |c|
   poly_unity_mod_cmult_X_exp_deg |- !r. Ring r /\ #1 <> #0 ==>
                                     !m c. 0 < m /\ c IN R ==> ((c * X ** m) % unity m = chop [c])

   Useful Theorems:
   poly_monic_add_less         |- !r. Ring r ==> !p q. poly p /\ poly q /\ deg p < deg q ==>
                                      (monic (p + q) <=> monic q)
   poly_monic_add_less_comm    |- !r. Ring r ==> !p q. poly p /\ poly q /\ deg q < deg p ==>
                                      (monic (p + q) <=> monic p)
   poly_monic_div_monic        |- !r. Ring r ==> !p q. monic p /\ monic q /\
                                      0 < deg q /\ deg q <= deg p ==> monic (p / q)
   poly_monic_nonconst_div_monic_nonconst
                               |- !r. Ring r ==> !p q. monic p /\ 0 < deg p /\ monic q /\ 0 < deg q /\
                                      deg q < deg p ==> monic (p / q) /\ 0 < deg (p / q)

   poly_weak_cmult_add_chop    |- !r. Ring r /\ #1 <> #0 ==>
                                  !p q. weak p /\ weak q /\ 1 < LENGTH p /\ LENGTH q <= LENGTH p ==>
                                  !h. h IN R ==> (chop (h o p || q) = (h * p + q) % unity (LENGTH p))
   poly_mod_less_weak          |- !r. Ring r /\ #1 <> #0 ==>
                                  !p. weak p /\ 0 < LENGTH p ==> (chop p % unity (LENGTH p) = chop p)

   Weak Polynomials with X or polynomial addition:
   weak_split_front_last       |- !r. Ring r /\ #1 <> #0 ==> !p. weak p /\ p <> |0| ==>
                                      (p = FRONT p || LAST p o (X ** PRE (LENGTH p)))
   weak_snoc_eq_add_shift      |- !r. Ring r ==> !p c. weak p /\ c IN R /\ c <> #0 ==> (SNOC c p = p + [c] >> LENGTH p)

   Polynomials Coefficients:
   poly_coeff_shift_n         |- !r. Ring r ==> !p. p <> |0| ==> !n k. k < n ==> ((p >> n) ' k = #0)
   poly_coeff_weak_add_const  |- !r. Ring r ==> !p c. weak p /\ c IN R ==>
                                 !n. 0 < n ==> ((p || [c]) ' n = p ' n)
   poly_coeff_X_exp_n_add_c_alt
                              |- !r. Ring r ==> !c. ##c <> #0 ==>
                                 !n k. 0 < k /\ k < n ==> ((X ** n + |c|) ' k = #0)
   poly_coeff_X_exp_n_sub_c_alt
                              |- !r. Ring r ==> !c. ##c <> #0 ==>
                                 !n k. 0 < k /\ k < n ==> ((X ** n - |c|) ' k = #0)
   poly_coeff_weak_add_X_exp  |- !r. Ring r /\ #1 <> #0 ==> !p. weak p ==>
                                 !k. k < SUC (deg p) ==> ((p || X ** SUC (deg p)) ' k = p ' k)
   poly_coeff_weak_add_cmult_X_exp
                              |- !r. Ring r /\ #1 <> #0 ==> !c p. c IN R /\ weak p ==>
                                 !k. k < SUC (deg p) ==> ((p || c o (X ** SUC (deg p))) ' k = p ' k)

   Polynomial Turn:
   chop_turn_eqn         |- !r. Ring r /\ #1 <> #0 ==> !p. weak p /\ 1 < LENGTH p ==>
                                (chop (turn p) = (p * X) % unity (LENGTH p))
   chop_turn_exp_eqn     |- !r. Ring r /\ #1 <> #0 ==> !p. weak p /\ 1 < LENGTH p ==>
                                !n. chop (turn_exp p n) = (p * X ** n) % unity (LENGTH p)

*)

(* ------------------------------------------------------------------------- *)
(* Monic Polynomials                                                         *)
(* ------------------------------------------------------------------------- *)

(* A monic polynomial a leading coefficient equal to #1. *)
val poly_monic_def = Define`
  poly_monic (r:'a ring) (p:'a poly) <=> poly p /\ (lead p = #1)
`;
val _ = overload_on ("monic", ``poly_monic r``);

(* Overloads for any type *)
val _ = overload_on("Monic", ``\r. poly_monic r``);
val _ = overload_on("Deg", ``\r. poly_deg r``);
val _ = overload_on("Lead", ``\r. poly_lead r``);
val _ = overload_on("Ulead", ``\r p. Poly r p /\ Unit r (Lead r p)``);
val _ = overload_on("Pmonic", ``\r p. Poly r p /\ Unit r (Lead r p) /\ 0 < Deg r p``);

(* export components later *)
(* val _ = export_rewrites ["poly_monic_def"]; *)

(* Theorem: monic p ==> poly p *)
val poly_monic_poly = save_thm("poly_monic_poly",
    poly_monic_def |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL);
(* > val poly_monic_poly = |- !r p. monic p ==> poly p : thm *)

val _ = export_rewrites ["poly_monic_poly"];

(* Theorem: monic p ==> lead p = #1 *)
val poly_monic_lead = save_thm("poly_monic_lead",
    poly_monic_def |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> UNDISCH |> CONJUNCT2 |> DISCH_ALL |> GEN_ALL);
(* > val poly_monic_lead = |- !r p. monic p ==> (lead p = #1) : thm *)

val _ = export_rewrites ["poly_monic_lead"];

(* Theorem: monic |0| <=> #1 = #0 *)
(* Proof:
   If part: true by lead |0| = #0    by poly_lead_zero
   Only-if part: by definition, and  by poly_zero_poly
*)
val poly_monic_zero = store_thm(
  "poly_monic_zero",
  ``!r:'a ring. monic |0| <=> (#1 = #0)``,
  rw[poly_monic_def] >>
  metis_tac []);

(* Theorem: #1 <> #0 ==> !p. monic p ==> p <> |0| *)
(* Proof:
   monic p ==> lead p = #1     by poly_monic_def
   lead |0| = #0               by poly_lead_zero
   Hence p <> |0|
*)
val poly_monic_nonzero = store_thm(
  "poly_monic_nonzero",
  ``!r:'a ring. #1 <> #0 ==> !p. monic p ==> p <> |0|``,
  rw[poly_monic_def]);

(* Theorem: monic |1| *)
(* Proof:
   by poly_one_poly and poly_lead_one.
*)
val poly_monic_one = store_thm(
  "poly_monic_one",
  ``!r:'a ring. Ring r ==> monic |1|``,
  rw[poly_monic_def]);

val _ = export_rewrites ["poly_monic_one"];

(* Theorem: [Multiplicatively Closed] Ring r /\ monic p /\ monic q ==> monic (p * q) *)
(* Proof:
   monic p ==> lead p = #1     by poly_monic_def
   monic q ==> lead q = #1     by poly_monic_def
   If #1 = #0, R = {#0}        by ring_one_eq_zero
   hence lead (p * q) = #0     by poly_lead_element, IN_SING
   and monic (p * q) is trivially true.
   If #1 <> #0,
   lead p * lead q = #1 <> #0  by ring_mult_one_one
   Hence
     lead (p * q)
   = lead p * lead q           by weak_lead_mult_nonzero
   = #1, hence monoic.
*)
val poly_monic_mult_monic = store_thm(
  "poly_monic_mult_monic",
  ``!r:'a ring. Ring r ==> !p q. monic p /\ monic q ==> monic (p * q)``,
  rw_tac std_ss[poly_monic_def, poly_mult_poly] >>
  Cases_on `#1 = #0` >-
  metis_tac [ring_one_eq_zero, poly_lead_element, IN_SING, poly_mult_poly, poly_is_weak] >>
  rw[weak_lead_mult_nonzero]);

(* Theorem: monic p /\ monic q ==> deg (p * q) = deg p + deg q *)
(* Proof:
   monic p ==> lead p = #1     by poly_monic_def
   monic q ==> lead q = #1     by poly_monic_def
   If #1 = #0, |1| = |0|       by poly_zero_eq_one
   hence p = |0|, q = |0| and p * q = |0|  by poly_one_eq_zero
   and   deg (p * q)
       = deg |0|               by above
       = 0                     by poly_deg_zero
       = 0 + 0                 by ADD_0
       = deg p + deg q         by poly_deg_zero
   If #1 <> #0,
   lead p * lead q = #1 <> #0  by ring_mult_one_one
   hence deg (p * q)
       = deg p + deg q         by weak_deg_mult_nonzero
*)
val poly_monic_deg_mult = store_thm(
  "poly_monic_deg_mult",
  ``!r:'a ring. Ring r ==> !p q. monic p /\ monic q ==> (deg (p * q) = deg p + deg q)``,
  rw_tac std_ss[poly_monic_def, poly_mult_poly] >>
  Cases_on `#1 = #0` >| [
    `|1| = |0|` by metis_tac [poly_zero_eq_one] >>
    `(p = |0|) /\ (q = |0|) /\ (p * q = |0|)` by metis_tac [poly_one_eq_zero, poly_mult_poly] >>
    rw[],
    `lead p * lead q = #1` by rw_tac std_ss[ring_mult_one_one] >>
    rw [weak_deg_mult_nonzero]
  ]);

(* Theorem: Ring r ==> !p q. monic p /\ poly q /\ monic (p * q) ==> monic q *)
(* Proof:
   monic p ==> lead p = #1             by poly_monic_def
   monic p * q ==> lead (p * q) = #1   by poly_monic_def
   If #1 = #0, |1| = |0|               by poly_zero_eq_one
   hence q = |0|                       by poly_one_eq_zero
   and   lead q
       = lead |0|                      by above
       = #0                            by poly_lead_zero
       = #1                            by #1 = #0
      or monic q                       by poly_monic_def
   If #1 <> #0,
   hence q <> |0|                      by poly_mult_rzero, poly_lead_zero
     and lead q <> #0                  by poly_lead_nonzero
    Also lead p * lead q = lead q      by ring_mult_lone, poly_lead_element
    Thus lead q = #1                   by weak_lead_mult_nonzero
      or monic q                       by poly_monic_def
*)
val poly_monic_monic_mult = store_thm(
  "poly_monic_monic_mult",
  ``!r:'a ring. Ring r ==> !p q. monic p /\ poly q /\ monic (p * q) ==> monic q``,
  rw[poly_monic_def] >>
  Cases_on `#1 = #0` >| [
    `|1| = |0|` by metis_tac [poly_zero_eq_one] >>
    `q = |0|` by metis_tac [poly_one_eq_zero, poly_mult_poly] >>
    rw[],
    `q <> |0|` by metis_tac[poly_mult_rzero, poly_lead_zero] >>
    `lead q <> #0` by rw[poly_lead_nonzero] >>
    `lead p * lead q = lead q` by rw_tac std_ss[ring_mult_lone, poly_lead_element, poly_is_weak] >>
    metis_tac[weak_lead_mult_nonzero, poly_is_weak]
  ]);

(* Theorem: Ring r ==> !p q. monic p /\ poly q /\ monic (q * p) ==> monic q *)
(* Proof: by poly_monic_monic_mult, poly_mult_comm. *)
val poly_monic_monic_mult_comm = store_thm(
  "poly_monic_monic_mult_comm",
  ``!r:'a ring. Ring r ==> !p q. monic p /\ poly q /\ monic (q * p) ==> monic q``,
  metis_tac[poly_monic_monic_mult, poly_mult_comm, poly_monic_poly]);

(*
Note: There is no:
!r. Ring r ==> !p q. poly q ==> (monic (p * q) <=> monic p /\ monic q)
since the (lead p) and (lead q) can be unit pairs, with (lead p) * (lead q) = #1.
*)

(* Theorem: Ring r ==> !p. (monic p /\ (deg p = 0)) <=> (p = |1|) *)
(* Proof:
   If #1 = #0,
     |1| = |0|                by poly_one_eq_poly_zero
     If part: monic p /\ deg p = 0 ==> p = |1|
        monic p ==> poly p    by poly_monic_poly
        poly p ==> p = |0|    by poly_one_eq_zero, |1| = |0|
        Hence p = |1|         by |0| = |1|
     Only-if part: p = |1| ==> monic p /\ deg p = 0
        monic |0| = T         by poly_monic_one
        deg |0| = 0           by poly_deg_one
   If #1 <> #0,
   If part: monic p /\ (deg p = 0) ==> p = |1|
      Note poly p /\ (lead p = #1)      by poly_monic_def
       and p <> |0|                     by poly_monic_nonzero, #1 <> #0
      thus ?c. c IN R /\ c <> #0 /\ (p = [c])     by poly_deg_eq_0, p <> |0|
      Hence c = #1                      by poly_lead_const
         or p = [#1] = |1|              by poly_one, #1 <> #0
   Only-if part: monic |1| /\ (deg |1| = 0)
      monic |1| = T                     by poly_monic_one
      deg |1| = 0                       by poly_deg_one, #1 <> #0
*)
val poly_monic_deg_0 = store_thm(
  "poly_monic_deg_0",
  ``!r:'a ring. Ring r ==> !p. (monic p /\ (deg p = 0)) <=> (p = |1|)``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >| [
    `|1| = |0|` by rw[poly_one_eq_poly_zero] >>
    metis_tac[poly_one_eq_zero, poly_monic_poly, poly_monic_one, poly_deg_one],
    rw[EQ_IMP_THM] >>
    `poly p /\ (lead p = #1)` by rw[] >>
    `p <> |0|` by rw[poly_monic_nonzero] >>
    `?c. c IN R /\ c <> #0 /\ (p = [c])` by rw[GSYM poly_deg_eq_0] >>
    `c = #1` by metis_tac[poly_lead_const] >>
    metis_tac[poly_one]
  ]);

(* Theorem: Ring r ==> !p. monic p ==> ulead p *)
(* Proof:
   Since lead p = #1       by poly_monic_lead
     and unit #1           by ring_unit_one
   Hence ulead p           by poly_monic_poly
*)
val poly_monic_ulead = store_thm(
  "poly_monic_ulead",
  ``!r:'a ring. Ring r ==> !p. monic p ==> ulead p``,
  rw[]);

(* Theorem: Ring r ==> !p. monic p /\ 0 < deg p ==> pmonic p *)
(* Proof: by notation, ring_unit_one *)
val poly_monic_pmonic = store_thm(
  "poly_monic_pmonic",
  ``!r:'a ring. Ring r ==> !p. monic p /\ 0 < deg p ==> pmonic p``,
  rw[]);

(* Theorem: Ring r /\ #1 <> #0 ==> !p q. monic p /\ monic q ==> monic (p o q) *)
(* Proof:
   Note weak p /\ (lead p = #1)    by poly_monic_def, monic p, poly_is_weak
    and weak q /\ (lead q = #1)    by poly_monic_def, monic q, poly_is_weak
   Thus lead p * lead q = #1       by ring_mult_one_one
                       <> #0       by #1 <> #0
    ==> lead (p o q) = #1          by weak_lead_weak_mult_nonzero
    Now weak (p o q)               by weak_mult_weak
     so poly (p o q)               by poly_nonzero_lead_nonzero
     or monic (p o q)              by poly_monic_def
*)
val weak_mult_monic_monic = store_thm(
  "weak_mult_monic_monic",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p q. monic p /\ monic q ==> monic (p o q)``,
  rpt strip_tac >>
  `weak p /\ (lead p = #1)` by rw[poly_monic_def] >>
  `weak q /\ (lead q = #1)` by rw[poly_monic_def] >>
  `lead p * lead q <> #0` by rw[] >>
  `lead (p o q) = #1` by rw[weak_lead_weak_mult_nonzero] >>
  `weak (p o q)` by rw[] >>
  metis_tac[poly_monic_def, poly_nonzero_lead_nonzero]);

(* ------------------------------------------------------------------------- *)
(* Monic Polynomial Exponentiaton                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r /\ monic p ==> !n. monic (p ** n) *)
(* Proof: by induction on n.
   Base case: monic p ==> monic (p ** 0)
     Since p ** 0 = |1|    by poly_exp_0
     True by poly_monic_one.
   Step case: monic (p ** n) ==> monic (p ** SUC n)
     p ** SUC n = p * p ** n   by poly_exp_SUC
     hence monic (p ** SUC n)  by poly_monic_mult_monic and induction hypothesis
*)
val poly_monic_exp_monic = store_thm(
  "poly_monic_exp_monic",
  ``!r:'a ring. Ring r ==> !p. monic p ==> !n. monic (p ** n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw_tac std_ss[poly_monic_poly, poly_exp_0, poly_monic_one] >>
  rw_tac std_ss[poly_monic_poly, poly_exp_SUC, poly_monic_mult_monic]);

val _ = export_rewrites ["poly_monic_exp_monic"];

(* Theorem: monic p ==> !n. deg (p ** n) = n * deg p *)
(* Proof: by induction on n.
   Base case: monic p ==> deg (p ** 0) = 0 * deg p
       deg (p ** 0)
     = deg |1|                   by poly_exp_0
     = 0                         by poly_deg_one
     = 0 * dep                   by MULT
   Step case: monic p /\ deg (p ** n) = n * deg p ==> deg (p ** SUC n) = SUC n * deg p
       monic p ==> monic p ** n  by poly_monic_exp_monic
       deg (p ** SUC n)
     = deg (p ** n * p)          by poly_exp_suc
     = deg (p ** n) + deg p      by poly_monic_deg_mult
     = n * deg p + deg p         by induction hypothesis
     = SUC n * deg p             by MULT
*)
val poly_monic_deg_exp = store_thm(
  "poly_monic_deg_exp",
  ``!r:'a ring. Ring r ==> !p. monic p ==> !n. deg (p ** n) = n * deg p``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw [poly_deg_one, MULT] >>
  rw [poly_monic_deg_mult, poly_monic_exp_monic, poly_exp_suc, MULT]);

val _ = export_rewrites ["poly_monic_deg_exp"];

(* Theorem: Ring r /\ monic p ==> !n. monic (p >> n) *)
(* Proof:
   poly p ==> poly (p >> n)    by poly_shift_poly
   lead (p >> n) = lead p      by poly_lead_shift
   hence true by poly_monic_def.
*)
val poly_monic_shift_monic = store_thm(
  "poly_monic_shift_monic",
  ``!r:'a ring. Ring r ==> !p. monic p ==> !n. monic (p >> n)``,
  rw[poly_monic_def]);

val _ = export_rewrites ["poly_monic_shift_monic"];

(* Theorem: monic p /\ 0 < deg p ==> !n m. p ** n = p ** m <=> n = m *)
(* Proof:
   If part: p ** n = p ** m ==> n = m
      Since  deg (p ** n) = deg (p ** m)    by given
       or       n * deg p = m * deg p       by poly_monic_deg_exp
                        n = m               by MULT_RIGHT_CANCEL, deg p <> 0.
   Only-if part: n = m ==> p ** n = p ** m
      This is trivial.
*)
val poly_monic_exp_eq = store_thm(
  "poly_monic_exp_eq",
  ``!r:'a ring. Ring r ==> !p. monic p /\ 0 < deg p ==> !n m. (p ** n = p ** m) <=> (n = m)``,
  metis_tac[poly_monic_deg_exp, MULT_RIGHT_CANCEL, NOT_ZERO_LT_ZERO]);


(* Theorem: monic p ==> !n. (p ** n = |1|) <=> ((p = |1|) \/ (n = 0)) *)
(* Proof:
   Since deg (p ** n) = n * deg p   by poly_monic_deg_exp
     but deg |1| = 0                by poly_deg_one
   Hence n = 0,
      or deg p = 0,
     but p <> |0|  since monic p, hence p = [c] by poly_deg_eq_zero
    Now  [c] ** n = chop [c ** n]   by poly_exp_const
   Thus  [c] = |1|.
*)
val poly_monic_exp_eq_one = store_thm(
  "poly_monic_exp_eq_one",
  ``!r:'a ring. Ring r ==> !p. monic p ==> !n. (p ** n = |1|) <=> ((p = |1|) \/ (n = 0))``,
  rw[EQ_IMP_THM] >| [
    `n * deg p = 0` by metis_tac[poly_monic_deg_exp, poly_deg_one] >>
    `(n = 0) \/ (deg p = 0)` by metis_tac[MULT_EQ_0] >| [
      rw[],
      Cases_on `p = |0|` >| [
        rw[GSYM poly_monic_zero, poly_zero_eq_one],
        `poly p /\ (lead p = #1)` by rw[poly_monic_def] >>
        `?c. c IN R /\ c <> #0 /\ (p = [c])` by metis_tac[poly_deg_eq_zero] >>
        `c = #1` by metis_tac[poly_lead_const] >>
        metis_tac[poly_one]
      ]
    ],
    rw[],
    rw[]
  ]);

(* Theorem: Ring r ==> !p. monic p /\ 0 < deg p ==> !n. (p ** n = p) <=> (n = 1) *)
(* Proof:
   If part: monic p /\ 0 < deg p /\ (p ** n = p) ==> (n = 1)
      Since deg (p ** n) = n * deg p         by poly_monic_deg_exp
      hence n = 1                            by MULT_EQ_ID, deg p <> 0
   Only-if part: monic p /\ 0 < deg p ==> p ** 1 = p
      Since monic p ==> poly p               by poly_monic_poly
      hence p ** 1 = p                       by poly_exp_1
*)
val poly_monic_exp_eq_self = store_thm(
  "poly_monic_exp_eq_self",
  ``!r:'a ring. Ring r ==> !p. monic p /\ 0 < deg p ==> !n. (p ** n = p) <=> (n = 1)``,
  metis_tac[poly_monic_poly, poly_exp_1, poly_monic_deg_exp, MULT_EQ_ID, NOT_ZERO_LT_ZERO]);

(* ------------------------------------------------------------------------- *)
(* Scalar Polynomials                                                        *)
(* ------------------------------------------------------------------------- *)

(* set proper overloads *)
val _ = clear_overloads_on "##";
val _ = remove_termtok{term_name = "PAIR_REL", tok = "###"}
Overload "##" = “r.sum.exp #1”
Overload "###" = “(poly_ring r).sum.exp |1|”

(* val _ = overload_on ("|c|", ``chop [##c]``); *)
(* val _ = overload_on ("|n|", ``chop [##n]``); *)

val _ = overload_on ("|c|", ``###c``);
val _ = overload_on ("|n|", ``###n``);

(*
- poly_one_sum_n;
> val it = |- !r. Ring r ==> !n. |n| = chop [##n] : thm
*)

(* Theorem: Ring r ==> !c. weak [##c] *)
(* Proof:
   Note ##c IN R          by ring_num_element
    and weak []           by weak_of_zero
     so weak [##c]        by weak_cons
*)
val weak_ring_sum_c = store_thm(
  "weak_ring_sum_c",
  ``!r:'a ring. Ring r ==> !c. weak [##c]``,
  rw[]);

(* Theorem: |c| = chop [##c} *)
(* Proof:
     |c| = ###c = chop [##c]    by poly_one_sum_n
*)
val poly_ring_sum_c = store_thm(
  "poly_ring_sum_c",
  ``!r:'a ring. Ring r ==> !c: num. |c| = chop [##c]``,
  rw [poly_one_sum_n]);

(* Theorem: |0| = ### 0 *)
(* Proof:
     ### 0
   = (PolyRing r).sum.exp |1| 0    by notation
   = |0|                           by monoid_exp_0 (type compatible)
*)
val poly_ring_sum_0 = store_thm(
  "poly_ring_sum_0",
  ``!r:'a ring. |0| = ### 0``,
  rw[]);

(* Theorem: Ring r ==> |1| = ###1 *)
(* Proof:
     |1|
   = chop [#1]       by poly_ring_ids
   = chop [##1]      by ring_num_1
   = ### 1           by poly_ring_sum_c
*)
val poly_ring_sum_1 = store_thm(
  "poly_ring_sum_1",
  ``!r:'a ring. Ring r ==> ( |1| = ###1)``,
  rw[poly_ring_ids, poly_ring_sum_c]);

(* Theorem: |c| = if ##c = #0 then |0| else [##c] *)
(* Proof:
     |c| = chop[##c]                         by poly_one_sum_n
         = if ##c = #0 then |0| else [##c]   by poly_chop_cons
*)
val poly_one_sum_n_eq = store_thm(
  "poly_one_sum_n_eq",
  ``!r:'a ring. Ring r ==> !c. |c| = if ##c = #0 then |0| else [##c]``,
  rw[poly_one_sum_n]);

(* Theorem: Ring r ==> !c. poly |c| *)
(* Proof:
   |c| = chop [##c]  by poly_ring_sum_n
   Since weak [##c]  by weak_const
   Hence true        by poly_chop_weak_poly
*)
val poly_sum_num_poly = store_thm(
  "poly_sum_num_poly",
  ``!r:'a ring. Ring r ==> !c: num. poly |c|``,
  rw[poly_one_sum_n] >> rw[]);
(* Actually, this is better than the next proof. *)

(* Theorem: Ring r ==> !c. poly |c| *)
(* Proof:
   Since  |c| = chop [##c]   by poly_ring_sum_c
   If ##c = #0,
      |c| = chop [##0]
          = chop [#0]        by ring_num_0
          = |0|              by poly_chop_const_zero,
       and poly |0|          by poly_add_poly
   If ##c <> #0,
      |c| = chop [##c]
          = [##c]            by poly_chop_const_nonzero
      and poly [##c]         by poly_nonzero_element_poly
*)
val poly_ring_sum = store_thm(
  "poly_ring_sum",
  ``!r:'a ring. Ring r ==> !c: num. poly |c|``,
  rw[poly_ring_sum_c] >> rw[]);

(* export simple result *)
val _ = export_rewrites ["poly_ring_sum"];

(* Theorem: deg |c| = 0 *)
(* Proof:
   If ##c = #0,
     |c| = chop [#0]   by poly_one_sum_n
         = |0|         by poly_chop_const_zero
     and deg |0| = 0   by poly_deg_zero
   If ##c <> #0,
     deg |c|
   = deg (chop [##c])   by poly_one_sum_n
   = deg [##c]          by poly_chop_const_nonzero
   = 0                  by poly_deg_const, ring_num_element
*)
val poly_deg_sum_num = store_thm(
  "poly_deg_sum_num",
  ``!r:'a ring. Ring r ==> !c: num. deg |c| = 0``,
  rw[poly_one_sum_n] >> rw[]);

(* In general, |n| = chop[##n] by poly_one_sum_n *)

(* Theoerem: Ring r ==> !c. lead |c| = ##c *)
(* Proof:
   If zerop [##c], i.e. c = multiple of (char r) if FiniteRing r
     lead |c|
   = lead (chop[##c])        by poly_one_sum_n
   = lead []                 by poly_chop_def, zerop [##c]
   = #0                      by poly_lead_of_zero
   = ##0                     by ring_num_0
   If not zerop [##c],
     lead |c|
   = lead (chop[##c])        by poly_one_sum_n
   = lead [##c]              by poly_chop_def, not zerop [##c]
   = ##c                     by poly_lead_const
*)
val poly_lead_one_sum_n = store_thm(
  "poly_lead_one_sum_n",
  ``!r:'a ring. Ring r ==> !c: num. lead |c| = ##c``,
  rw[poly_one_sum_n] >> rw[]);

(* Theorem: eval |c| x = ##c *)
(* Proof:
    eval |c| x
  = eval (chop[##c]) x                        by poly_one_sum_n
  = eval (if ##c = #0 then [] else [##c]) x   by poly_chop_cons
  = eval [] x   or eval [##c] x               by cases
  = #0 or ##c                                 by poly_eval_of_zero, poly_eval_const
  = ##0 or ##c                                by ring_num_0
  = ##c
*)
val poly_eval_one_sum_n = store_thm(
  "poly_eval_one_sum_n",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !c: num. eval |c| x = ##c``,
  rw[poly_one_sum_n] >>
  rw[]);

(* Theorem: Ring r ==> !n c. n < char r /\ c < char r ==> ( |n| = |c| <=> n = c) *)
(* Proof:
   If part: |n| = |c| ==> n = c
   Since   |n| = |c|
      lead |n| = lead |c|
   or      ##n = ##c         by poly_lead_one_sum_n
   Hence     n = c           by ring_num_eq
   Only-if part: n = c ==> |n| = |c|
      This is trivially true.
*)
val poly_sum_num_eq = store_thm(
  "poly_sum_num_eq",
  ``!r:'a ring. Ring r ==> !n c. n < char r /\ c < char r ==> (( |n| = |c|) <=> (n = c))``,
  metis_tac[FiniteRing_def, poly_lead_one_sum_n, ring_num_eq]);

(* Theorem: Ring r ==> !c:num. ### (SUC c) = |1| + |c| *)
(* Proof: by poly_add_mult_ring, ring_num_SUC *)
val poly_sum_num_SUC = store_thm(
  "poly_sum_num_SUC",
  ``!r:'a ring. Ring r ==> !c:num. ### (SUC c) = |1| + |c|``,
  rw[poly_add_mult_ring, ring_num_SUC]);

(* Theorem: Ring r ==> !c:num. ### (SUC c) = |c| + |1| *)
(* Proof: by poly_add_mult_ring, ring_num_suc *)
val poly_sum_num_suc = store_thm(
  "poly_sum_num_suc",
  ``!r:'a ring. Ring r ==> !c:num. ### (SUC c) = |c| + |1|``,
  rw[poly_add_mult_ring, ring_num_suc]);

(* ------------------------------------------------------------------------- *)
(* Involving Polynomial X                                                    *)
(* ------------------------------------------------------------------------- *)

(* Denote the polynomial variable X = #1 x + #0 *)
(* val _ = overload_on ("X", ``chop [#0; #1]``); *)
val _ = overload_on ("X", ``|1| >> 1``);
(* val _ = clear_overloads_on "X"; *)

(* Theorem: #1 <> #0 ==> X = [#0;#1] *)
(* Proof:
   If #1 <> #0, |1| = [#1]    by poly_one
   |1| >> 1 = [#0;#1]         by poly_shift_1
*)
val poly_X_def = store_thm(
  "poly_X_def",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> (X = [#0;#1])``,
  rw_tac std_ss[poly_shift_1, poly_one, poly_zero]);

(* export simple definition. *)
val _ = export_rewrites ["poly_X_def"];

(* Theorem: X = [#1] >> 1 *)
(* Proof:
     X = [#0; #1]          by poly_X_def
       = [#0] + [#1] >> 1  by poly_cons_eq_add_shift
       = [#1] >> 1         by poly_add_lzero_poly
*)
val poly_X_alt = store_thm(
  "poly_X_alt",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> (X = [#1] >> 1 )``,
  rpt strip_tac >>
  `X = [#0; #1]` by rw[] >>
  (`_ = [#0] + [#1] >> 1` by rw[poly_cons_eq_add_shift]) >>
  (`_ = [#1] >> 1` by rw[]) >>
  rw[]);

(* Theorem: Ring r ==> weak X *)
(* Proof: by Weak_def, ring_zero_element, ring_one_element. *)
val weak_X = store_thm(
  "weak_X",
  ``!r:'a ring. Ring r ==> weak X``,
  rw[]);

(* Theorem: poly X *)
(* Proof:
   poly |1|         by poly_one_poly
   poly ( |1| >> 1)  by poly_shift_poly
*)
val poly_X = store_thm(
  "poly_X",
  ``!r:'a ring. Ring r ==> poly X``,
  rw []);

(* export simple definition. *)
val _ = export_rewrites ["poly_X"];

(* Theorem: #1 <> #0 ==> deg X = 1 *)
(* Proof:
     #1 <> #0 ==>
     X = [#0;#1] <> |0|     by poly_X_def
     deg X
   = deg ([#0: #1])         by above
   = SUC (deg [#1])         by poly_deg_cons
   = SUC 0                  by poly_deg_const
   = 1
*)
val poly_deg_X = store_thm(
  "poly_deg_X",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> (deg X = 1)``,
  rw[]);

(* Theorem: lead X = #1 *)
(* Proof:
    lead X
  = lead ( |1| >> 1)   by notation
  = lead |1|          by poly_lead_shift
  = #1                by poly_lead_one
*)
Theorem poly_lead_X[simp]:
  !r:'a ring. Ring r ==> (lead X = #1)
Proof
  rw_tac std_ss[poly_lead_shift, poly_lead_one]
QED

(* Theorem: monic X *)
(* Proof:
   Since monic |1|          by poly_monic_one
   Hence monic ( |1| >> 1)   by poly_monic_shift_monic
   oe    monic X            by notation
*)
val poly_monic_X = store_thm(
  "poly_monic_X",
  ``!r:'a ring. Ring r ==> monic X``,
  rw[]);

(* Theorem: Ring r ==> !p. poly p ==> p * X = p >> 1 *)
(* Proof:
   If #1 = #0,
      Then |1| = |0|            by poly_one_eq_poly_zero
       and p = |0|              by poly_one_eq_zero
        so |0| * X = |0| >> 1   by poly_mult_zero, poly_shift_zero
   If #1 <> #0,
     p * X
   = X * p                      by poly_mult_comm
   = [#0; #1] * p               by poly_X_def, #1 <> #0
   = #0 * p + ([#1] * p) >> 1   by poly_mult_cons_over
   = #0 * p + (#1 * p) >> 1     by poly_mult_lconst
   = |0| + p >> 1               by poly_cmult_lzero, poly_cmult_lone
   = p >> 1                     by poly_add_rzero
*)
val poly_mult_X = store_thm(
  "poly_mult_X",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (p * X = p >> 1)``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >| [
    `|1| = |0|` by rw[poly_one_eq_poly_zero] >>
    `p = |0|` by metis_tac[poly_one_eq_zero] >>
    rw[],
    `poly X` by rw[] >>
    `p * X = X * p` by rw[poly_mult_comm] >>
    `_ = [#0;#1] * p` by rw[] >>
    `_ = #0 * p + ([#1] * p) >> 1` by rw[poly_mult_cons_over] >>
    `_ = #0 * p + (#1 * p) >> 1` by metis_tac[poly_mult_lconst, ring_one_element] >>
    rw[]
  ]);

(* Theorem: Ring r ==> !p. poly p ==> (X * p = p >> 1) *)
(* Proof:
     X * p
   = p * X         by poly_mult_comm
   = p >> 1        by poly_mult_X
*)
val poly_mult_X_comm = store_thm(
  "poly_mult_X_comm",
  ``!r:'a ring. Ring r  ==> !p. poly p ==> (X * p = p >> 1)``,
  rw[poly_mult_X, poly_mult_comm]);

(* A better version of this: polyRoot.poly_monic_deg1_factor
   |- !r. Ring r ==> !p. monic p /\ (deg p = 1) ==> ?c. c IN R /\ (p = factor c)
*)

(* Theorem: Ring r /\ #1 <> #0 ==> !p. monic p /\ (deg p = 1) <=> ?c. c IN R /\ (p = X + chop[c]) *)
(* Proof:
   If part: !p. monic p /\ (deg p = 1) ==> ?c. c IN R /\ (p = X + chop[c])
   Since deg p = 1, p <> |0|        by poly_deg_zero
   Thus ?h t. p = h::t              by poly_zero, p <> []
    and 1 = deg p = deg (h::t)
          = LENGTH t                by poly_deg_cons_length
     so ?x. t = [x]                 by LENGTH_EQ_1
    hence t <> |0|                  by poly_zero, |0| = []
    and #1 = lead p                 by poly_monic_def
           = lead (h::t) = lead t   by poly_lead_cons, t <> |0|
      so x = #1                     by poly_lead_const
    Also h IN R                     by poly_cons_poly
   Let c = h, then to show: p = X + chop [h]
   or to show: [h; #1] = [#0; #1] + [h]
       [#0; #1] + [h]
     = chop ([#0; #1] || [h])       by poly_add_def
     = chop [#0 + h; #1]            by weak_add_def
     = chop [h; #1]                 by ring_add_lzero
     = [h; #1]                      by poly_chop_cons, #1 <> #0
   Only-if part: monic (X + chop[c]) /\ deg (X + chop[c]) = 1
     poly (X + chop [c]) = T        by poly_X, poly_add_poly, poly_chop_weak_poly
     lead (X + chop [c]) = #1       by poly_lead_add_less_comm, poly_lead_X, poly_deg_X, poly_deg_const
     deg (X + chop [c]) = 1         by poly_deg_add_less_comm, poly_deg_X, poly_deg_const
*)
val poly_monic_deg_1 = store_thm(
  "poly_monic_deg_1",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p. monic p /\ (deg p = 1) <=> ?c. c IN R /\ (p = X + chop[c])``,
  rw_tac std_ss[poly_monic_def, EQ_IMP_THM] >| [
    `p <> |0|` by metis_tac[poly_deg_zero, DECIDE``1 <> 0``] >>
    `?h t. p = h::t` by metis_tac[poly_zero, list_CASES] >>
    `LENGTH t = 1` by metis_tac[poly_deg_cons_length] >>
    `?x. t = [x]` by rw[GSYM LENGTH_EQ_1] >>
    `h IN R` by metis_tac[poly_cons_poly] >>
    `t <> |0|` by rw[] >>
    `lead t = #1` by metis_tac[poly_lead_cons] >>
    `x = #1` by metis_tac[poly_lead_const] >>
    qexists_tac `h` >>
    rw[] >>
    rw_tac std_ss[poly_add_def, poly_chop_def, weak_add_def, zero_poly_def, ring_add_lzero],
    rw[],
    rw[poly_lead_add_less_comm],
    rw[poly_deg_add_less_comm]
  ]);

(* Theorem: Ring r /\ #1 <> #0 ==> X <> |0| *)
(* Proof:
      X = [#0; #1]        by poly_X_def
   so X <> |0|            by NOT_NIL_CONS, poly_zero
*)
val poly_X_nonzero = store_thm(
  "poly_X_nonzero",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> X <> |0|``,
  rw[]);

(* Theorem: eval X x = x *)
(* Proof: by poly_eval_def. *)
val poly_eval_X = store_thm(
  "poly_eval_X",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> (eval X x = x)``,
  rw[poly_eval_def]);

(* Theorem: Ring r /\ #1 <> #0 ==> !p. weak p ==> X o p = p >> 1 *)
(* Proof:
   If p = |0|,
      LHS = |0| o X = |0|             by weak_mult_lzero
      RHS = |0| >> 1 = |0| = LHS      by poly_shift_zero
   If p <> |0|,
      Note zerop (#0 o p)                    by rw[weak_cmult_lzero
       and LENGTH (#0 o p) = LENGTH p        by weak_cmult_length
       and LENGTH (p >> 1) = SUC (LENGTH p)  by poly_shift_length, p <> |0|

        X o p
      = [#0; #1] o p               by poly_X_def
      = #0 o p || ([#1] o p) >> 1  by weak_mult_cons
      = #0 o p || p >> 1           by weak_mult_lone
      = p >> 1                     by weak_add_lzero_poly
*)
val weak_mult_X = store_thm(
  "weak_mult_X",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p. weak p ==> (X o p = p >> 1)``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[] >>
  `LENGTH (#0 o p) = LENGTH p` by rw[weak_cmult_length] >>
  `LENGTH (p >> 1) = SUC (LENGTH p)` by rw[poly_shift_length] >>
  `zerop (#0 o p)` by rw[weak_cmult_lzero] >>
  `X o p = [#0; #1] o p` by rw[poly_X_def] >>
  `_ = #0 o p || ([#1] o p) >> 1` by rw[weak_mult_cons] >>
  `_ = #0 o p || p >> 1` by rw[weak_mult_lone] >>
  `_ = p >> 1` by rw[weak_add_lzero_poly] >>
  rw[]);

(* Theorem: Ring r /\ #1 <> #0 ==> !p. weak p ==> (p o X = p >> 1) *)
(* Proof: by weak_mult_X, weak_mult_comm *)
val weak_mult_X_comm = store_thm(
  "weak_mult_X_comm",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p. weak p ==> (p o X = p >> 1)``,
  rw[GSYM weak_mult_X, weak_mult_comm]);

(* ------------------------------------------------------------------------- *)
(* Involving Polynomial X ** n                                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r ==> !n. poly (X ** n) *)
(* Proof: by poly_X, poly_exp_poly *)
val poly_X_exp = store_thm(
  "poly_X_exp",
  ``!r:'a ring. Ring r ==> !n. poly (X ** n)``,
  rw[]);

(* Theorem: #1 <> #0 ==> !n. X ** n = [#1] >> n  *)
(* Proof:
   Since #1 <> #0
   and   poly[#1], poly ([#1] >> n)    by poly_nonzero_element_poly
   Now induct on n.
   Base case: poly ([#1] >> 0) ==> poly (X ** 0) ==> (X ** 0 = [#1] >> 0)
       X ** 0
     = |1|           by poly_exp_0, for any X
     = [#1]          by poly_one
     = [#1] >> 0     by poly_shift_0
   Step case: poly ([#1] >> n) ==> poly (X ** n) ==> (X ** n = [#1] >> n) ==>
              poly ([#1] >> SUC n) ==> poly (X ** SUC n) ==> (X ** SUC n = [#1] >> SUC n)
     |1| <> |0|    by poly_zero_eq_one, #1 <> #0
     hence [#1] <> |0|
       X ** SUC n
     = X * X ** n                  by poly_exp_SUC
     = X * [#1] >> n               by induction hypothesis
     = ([#1] >> 1) * ([#1] >> n)   by poly_shift_1
     = ([#1] * [#1] >> n) >> 1     by poly_mult_shift_1_comm
     = ([#1] >> n) >> 1            by poly_mult_lconst, ring_one_element, poly_cmult_lone
     = [#1] >> SUC n               by poly_shift_cons
*)
val poly_X_exp_n = store_thm(
  "poly_X_exp_n",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. X ** n = [#1] >> n``,
  rpt strip_tac >>
  `poly [#1] /\ poly [#1] /\ poly ([#1] >> n)` by rw[] >>
  `( |1| = [#1]) /\ (X = [#0; #1])` by rw[poly_one] >>
  `poly X /\ poly (X ** n)` by rw[] >>
  Induct_on `n` >-
  rw[] >>
  `|1| <> |0|` by metis_tac[poly_zero_eq_one] >>
  `[#1] <> |0|` by metis_tac[poly_one] >>
  `poly ([#1] >> n)` by rw[] >>
  `X ** SUC n = X * X ** n` by rw[poly_exp_SUC] >>
  `_ = X * [#1] >> n` by rw[] >>
  `_ = ([#1] >> 1) * ([#1] >> n)` by rw[poly_shift_1] >>
  `_ = ([#1] * [#1] >> n) >> 1` by rw[poly_mult_shift_1_comm] >>
  `_ = ([#1] >> n) >> 1` by metis_tac[poly_mult_lconst, ring_one_element, poly_cmult_lone] >>
  rw[]);

(* Theorem: Ring r ==> !n. X ** (SUC n) = X >> n *)
(* Proof:
   By induction on n.
   Base case: X ** SUC 0 = X >> 0
       X ** SUC 0
     = X ** 1              by ONE
     = X                   by poly_X, poly_exp_1
     = X >> 0              by poly_shift_0
   Step case: X ** SUC n = X >> n ==> X ** SUC (SUC n) = X >> SUC n
       X ** SUC (SUC n)
     = X * X ** (SUC n)    by poly_X, poly_exp_SUC
     = X * (X >> n)        by induction hypothesis
     = (X >> n) >> 1       by z{poly_mult_X_comm
     = X >> SUC n          by poly_shift_SUC
*)
val poly_X_exp_eq_shift = store_thm(
  "poly_X_exp_eq_shift",
  ``!r:'a ring. Ring r ==> !n. X ** (SUC n) = X >> n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw[poly_mult_X_comm, poly_shift_SUC]);
(* compare with:
   poly_X_exp_n  |- !r. Ring r /\ #1 <> #0 ==> !n. X ** n = [#1] >> n: thm
*)

(* Theorem: X ** n = X ** m <=> n = m *)
(* Proof:
   Since monic X       by poly_monic_X
     and deg X = 1     by poly_deg_X
   Hence true          by poly_monic_exp_eq.
*)
val poly_X_exp_eq = store_thm(
  "poly_X_exp_eq",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n m. (X ** n = X ** m) <=> (n = m)``,
  rw[poly_monic_exp_eq]);

(* Theorem: !n. deg (X ** n) == n *)
(* Proof: by poly_monic_X, poly_deg_X, poly_monic_deg_exp. *)
val poly_deg_X_exp = store_thm(
  "poly_deg_X_exp",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. deg (X ** n) = n``,
  rw[]);

(* Theorem: !n. lead (X ** n) == #1 *)
(* Proof: by poly_monic_X, poly_monic_exp_monic, poly_monic_lead. *)
val poly_lead_X_exp = store_thm(
  "poly_lead_X_exp",
  ``!r:'a ring. Ring r ==> !n. lead (X ** n) = #1``,
  rw[]);

(* Theorem: !n. (X ** n = |1|) <=> (n = 0) *)
(* Proof:
   If part: (X ** n = |1|) ==> (n = 0)
      n = deg (X ** n)      by poly_deg_X_exp, #1 <> #0
        = deg |1|           by given, X ** n = |1|
        = 0                 by poly_deg_one
   Only-if part: (n = 0) ==> (X ** n = |1|)
      True by poly_X, poly_exp_0.
*)
val poly_X_exp_eq_one = store_thm(
  "poly_X_exp_eq_one",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. (X ** n = |1|) <=> (n = 0)``,
  rw_tac std_ss[poly_X, poly_exp_0, EQ_IMP_THM] >>
  metis_tac[poly_deg_X_exp, poly_deg_one]);

(* This is a generalization of: poly_X_exp_n
val it = |- !r. Ring r /\ #1 <> #0 ==> !n. X ** n = [#1] >> n: thm
*)

(* Theorem: Ring r /\ #1 <> #0 ==> !c. c IN R /\ c <> #0 ==> !n. c * X ** n = [c] >> n *)
(* Proof:
     c * X ** n
   = c * [#1] >> n     by poly_X_exp_n
   = c * |1| >> n      by poly_one, #1 <> #0
   = (c * |1|) >> n    by poly_cmult_shift
   = [c] >> n          by poly_cmult_one, c <> #0
*)
val poly_cmult_X_exp_n = store_thm(
  "poly_cmult_X_exp_n",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. c IN R /\ c <> #0 ==> !n. c * X ** n = [c] >> n``,
  metis_tac[poly_X_exp_n, poly_one, poly_cmult_shift, poly_cmult_one, poly_one_poly]);

(* Theorem: Ring r /\ #1 <> #0 ==> !n. X ** n <> |0| *)
(* Proof:
   If n = 0,
      Then X ** 0 = |1|        by poly_exp_0
       and |1| <> |0|          by poly_one_eq_poly_zero, #1 <> #0
   If n <> 0,
      Note deg (X ** n) = n    by poly_deg_X_exp, #1 <> #0
       and deg |0| = 0         by poly_deg_zero
      Thus X ** n <> |0|       by n <> 0.
*)
val poly_X_exp_nonzero = store_thm(
  "poly_X_exp_nonzero",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. X ** n <> |0|``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  metis_tac[poly_exp_0, poly_one_eq_poly_zero] >>
  metis_tac[poly_deg_X_exp, poly_deg_zero]);

(* Theorem: Ring r /\ #1 <> #0 ==> !n. X ** SUC n = X o (X ** n) *)
(* Proof:
   Note monic X              by poly_monic_X
    and monic (X ** n)       by poly_monic_exp_monic
    ==> monic (X o X ** n)   by weak_mult_monic_monic
    ==> poly (X o X ** n)    by poly_monic_poly
     X ** SUC n
   = X * X ** n              by poly_exp_SUC
   = chop (X o (X ** n))     by poly_mult_def
   = X o (X ** n)            by poly_chop_poly
*)
val weak_X_exp_SUC = store_thm(
  "weak_X_exp_SUC",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. X ** SUC n = X o (X ** n)``,
  rpt strip_tac >>
  `monic (X o (X ** n))` by rw[weak_mult_monic_monic] >>
  `poly (X o (X ** n))` by rw[] >>
  metis_tac[poly_exp_SUC, poly_mult_def, poly_chop_poly]);

(* Theorem: Ring r /\ #1 <> #0 ==> !n. X ** SUC n = (X ** n) o X *)
(* Proof: by weak_X_exp_SUC, weak_mult_comm *)
val weak_X_exp_suc = store_thm(
  "weak_X_exp_suc",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. X ** SUC n = (X ** n) o X``,
  rw[weak_X_exp_SUC, weak_mult_comm]);

(* Theorem: Ring r /\ #1 <> #0 ==> !c. c IN R ==> !n. c o X ** n = [c] >> n *)
(* Proof:
     c o X ** n
   = c o [#1] >> n     by poly_X_exp_n
   = c o |1| >> n      by poly_one, #1 <> #0
   = (c o |1|) >> n    by weak_cmult_shift
   = (c o [#1]) >> n   by poly_one, #1 <> #0
   = [c] >> n          by weak_cmult_one
*)
val weak_cmult_X_exp_n = store_thm(
  "weak_cmult_X_exp_n",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. c IN R ==> !n. c o (X ** n) = [c] >> n``,
  rpt strip_tac >>
  `c o (X ** n) = c o ( |1| >> n)` by rw[poly_X_exp_n, poly_one] >>
  `_ = (c o [#1]) >> n` by rw[weak_cmult_shift, poly_one] >>
  `_ = [c] >> n` by rw[weak_cmult_one] >>
  rw[]);

(* Theorem: Ring r /\ #1 <> #0 ==> !n. X ** n = PAD_LEFT #0 (SUC n) [#1] *)
(* Proof:
     X ** n
   = [#1] >> n                 by poly_X_exp_n
   = PAD_LEFT #0 (SUC n) [#1]  by poly_shift_const
*)
val poly_X_exp_n_alt = store_thm(
  "poly_X_exp_n_alt",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. X ** n = PAD_LEFT #0 (SUC n) [#1]``,
  rw[poly_X_exp_n, poly_shift_const]);

(* ------------------------------------------------------------------------- *)
(* Involving Polynomial X + |c|                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r ==> !c. poly (X + |c|) *)
(* Proof:
   Since  poly X     by poly_X
     and  poly |c|   by poly_ring_sum
   hence true by poly_add_poly.
*)
val poly_X_add_c = store_thm(
  "poly_X_add_c",
  ``!r:'a ring. Ring r ==> !c: num. poly (X + |c|)``,
  rw[]);

(* Theorem: X + |c| = [##c; #1] *)
(* Proof:
   Since |c| = chop[##c]   by poly_one_sum_n
   If c = 0, |c| = |0|
     X + |c|
   = X + |0|            by above
   = X                  by poly_add_rzero
   = [#0; #1]           by poly_X_def
   If c <> 0, chop [##c] = [##c]
     X + |c|
   = |c| + X            by poly_add_comm
   = |c| + [#1] >> 1    by poly_X_alt
   = [##c] + [#1] >> 1  by poly_chop_cons
   = [##c; #1]          by poly_cons_eq_add_shift
*)
val poly_X_add_c_list = store_thm(
  "poly_X_add_c_list",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. X + |c| = [##c; #1]``,
  rpt strip_tac >>
  Cases_on `c = 0` >-
  rw[] >>
  `X + |c| = |c| + X` by rw[poly_add_comm] >>
  (`_ = |c| + [#1] >> 1` by rw[poly_X_alt]) >>
  (`_ = [##c] + [#1] >> 1` by rw[poly_one_sum_n]) >>
  rw[poly_cons_eq_add_shift]);

(* Theorem: deg (X + c) = 1 *)
(* Proof:
   Since deg X = 1          by poly_deg_X
     and deg |c| = 0        by poly_deg_sum_num
     deg (X + |c|)
   = deg X                 by poly_deg_add_less, poly_add_comm
   = 1                     by poly_deg_X
*)
val poly_deg_X_add_c = store_thm(
  "poly_deg_X_add_c",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c:num. deg (X + |c|) = 1``,
  rpt strip_tac >>
  `(deg X = 1) /\ (deg |c| = 0)` by rw[poly_deg_sum_num] >>
  `poly X /\ poly |c|` by rw[] >>
  metis_tac[poly_add_comm, poly_deg_add_less, DECIDE``0 < 1``]);

(* Theorem: lead (X + |c|) = #1 *)
(* Proof:
   Since deg X = 1          by poly_deg_X
     and deg |c| = 0        by poly_deg_sum_num
     lead (X + |c|)
   = lead X                 by poly_lead_add_less, poly_add_comm
   = #1                     by poly_lead_X
*)
val poly_lead_X_add_c = store_thm(
  "poly_lead_X_add_c",
  ``!r:'a ring. Ring r ==> !c:num. lead (X + |c|) = #1``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >| [
    `poly (X + |c|)` by rw[] >>
    `X + |c| = |0|` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
    rw[],
    `(deg X = 1) /\ (deg |c| = 0) /\ (lead X = #1)` by rw[poly_deg_sum_num] >>
    `poly X /\ poly |c|` by rw[] >>
    metis_tac[poly_add_comm, poly_lead_add_less, DECIDE``0 < 1``]
  ]);

(* Theorem: monic (X + c) *)
(* Proof:
   By poly_monic_def, this is to show:
   (1) poly (X + |c|), true      by poly_X_add_c.
   (2) lead (X + |c|) = #1, true by poly_lead_X_add_c.
*)
val poly_monic_X_add_c = store_thm(
  "poly_monic_X_add_c",
  ``!r:'a ring. Ring r ==> !c:num. monic (X + |c|)``,
  rw[poly_monic_def, poly_lead_X_add_c]);

(* Theorem: #1 <> #0 ==> deg ((X + |c|) ** n) = n  *)
(* Proof:
   We have  poly X           by poly_X
       and  poly |c|         by poly_sum_num_poly
   hence    poly (X + |c|)   by poly_add_poly
   We have  deg X = 1        by poly_deg_X, when #1 <> #0
            deg |c| = 0      by poly_deg_sum_num
   hence    deg (X + |c|)
          = deg X            by poly_deg_add_less
          = 1
   and    monic (X + |c|)    by poly_monic_X_add_c
   thus     deg ((X + |c|) ** n)
          = n * deg (X + |c|)     by poly_monic_deg_exp, monic (X + |c|)
          = n                     by arithmetic
*)
val poly_deg_X_add_c_exp_n = store_thm(
  "poly_deg_X_add_c_exp_n",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. deg ((X + |c|) ** n) = n``,
  rpt strip_tac >>
  `poly X /\ poly |c| /\ poly (X + |c|)` by rw[poly_X, poly_sum_num_poly] >>
  `lead X = #1` by rw[poly_monic_X] >>
  `deg X = 1` by rw[poly_deg_X] >>
  `deg |c| = 0` by rw[poly_deg_sum_num] >>
  `0 < 1` by decide_tac >>
  `deg (X + |c|) = 1` by rw_tac std_ss[poly_deg_add_less, poly_add_comm] >>
  `monic (X + |c|)` by rw[poly_monic_X_add_c] >>
  rw[poly_monic_deg_exp]);

(* Theorem: Ring r /\ n < char r /\ c < char r ==> X + |n| = X + |c| <=> n = c *)
(* Proof:
   If part: X + |n| = X + |c| ==> n = c
         X + |n| = X + |c|
     ==> |n| = |c|      by poly_add_lcancel
     ==> n = c          by poly_sum_num_eq
   Only-if part: n = c ==> X + |n| = X + |c|
     This is trivially true.
*)
val poly_X_add_c_eq = store_thm(
  "poly_X_add_c_eq",
  ``!r:'a ring. Ring r ==>
   !n c. n < char r /\ c < char r ==> ((X + |n| = X + |c|) <=> (n = c))``,
  metis_tac[poly_add_lcancel, poly_X, poly_sum_num_poly, poly_sum_num_eq]);

(* Theorem: !p. p IN (IMAGE (\c. X + |c|) s) ==> poly p *)
(* Proof:
       p IN (IMAGE (\c. X + |c|) s)
   ==> ?c. p = X + |c|              by IN_IMAGE
   ==> poly p                       by poly_X_add_c
*)
val poly_X_add_c_image_element = store_thm(
  "poly_X_add_c_image_element",
  ``!r:'a ring. Ring r ==> !s p. p IN (IMAGE (\c:num. X + |c|) s) ==> poly p``,
  rpt strip_tac >>
  `!p. p IN (IMAGE (\c. X + |c|) s) <=> ?c. (p = X + |c|) /\ c IN s` by rw[] >>
  `?c. (p = X + |c|) /\ c IN s` by metis_tac[] >>
  rw[poly_X_add_c]);

(* Theorem: !p. p IN (IMAGE (\c. X + |c|) s) ==> monic p *)
(* Proof:
       p IN (IMAGE (\c. X + |c|) s)
   ==> ?c. p = X + |c|              by IN_IMAGE
   ==> monic p                      by poly_monic_X_add_c
*)
val poly_monic_X_add_c_image_element = store_thm(
  "poly_monic_X_add_c_image_element",
  ``!r:'a ring. Ring r ==> !s p. p IN (IMAGE (\c:num. X + |c|) s) ==> monic p``,
  rpt strip_tac >>
  `!p. p IN (IMAGE (\c. X + |c|) s) <=> ?c. (p = X + |c|) /\ c IN s` by rw[] >>
  `?c. (p = X + |c|) /\ c IN s` by metis_tac[] >>
  rw[poly_monic_X_add_c]);

(* Theorem: !p. p IN (IMAGE (\c. X + |c|) s) ==> (deg p = 1) *)
(* Proof:
       p IN (IMAGE (\c. X + |c|) s)
   ==> ?c. p = X + |c|              by IN_IMAGE
   ==> deg p = 1                    by poly_deg_X_add_c
*)
val poly_deg_X_add_c_image_element = store_thm(
  "poly_deg_X_add_c_image_element",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !s p. p IN (IMAGE (\c:num. X + |c|) s) ==> (deg p = 1)``,
  rpt strip_tac >>
  `!p. p IN (IMAGE (\c. X + |c|) s) <=> ?c. (p = X + |c|) /\ c IN s` by rw[] >>
  `?c. (p = X + |c|) /\ c IN s` by metis_tac[] >>
  rw[poly_deg_X_add_c]);

(* Theorem: FINITE s /\ MAX_SET s < char r /\ n < char r ==>
            n IN s <=> X + |n| IN IMAGE (\c. X + |c|) s *)
(* Proof:
   If part: n IN s ==> ?c. (X + |n| = X + |c|) /\ c IN s
      Let c = n, hence true.
   Only-if part: c IN s /\ X + |n| = X + |c| ==> n IN s
     Since c IN s , s <> {}         by MEMBER_NOT_EMPTY
        So c <= MAX_SET s           by MAX_SET_DEF
     hence c < char r               by LESS_EQ_LESS_TRANS
     X + |n| = X + |c| ==> n = c    by poly_X_add_c_eq
     Hence n IN s.
*)
val poly_X_add_c_image_property = store_thm(
  "poly_X_add_c_image_property",
  ``!r:'a ring. Ring r ==>
   !s. FINITE s /\ MAX_SET s < char r ==>
   !n:num. n < char r ==> (n IN s <=> X + |n| IN IMAGE (\c. X + |c|) s)``,
  rw_tac std_ss[IN_IMAGE, EQ_IMP_THM] >-
  metis_tac[] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `c <= MAX_SET s` by rw[MAX_SET_DEF] >>
  `c < char r` by decide_tac >>
  metis_tac[poly_X_add_c_eq]);

(* ------------------------------------------------------------------------- *)
(* Involving Polynomial X - |c|                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: poly (X - |c|) *)
(* Proof: by poly_X, poly_sum_num_poly, poly_sub_poly *)
val poly_X_sub_c = store_thm(
  "poly_X_sub_c",
  ``!r:'a ring. Ring r ==> !c:num. poly (X - |c|)``,
  rw[]);

(* Theorem: X - |c| = [- ##c; #1] *)
(* Proof:
   Since |c| = chop[##c]  by poly_one_sum_n
   If c = 0, |c| = |0|
     X - |c|
   = X - |0|              by above
   = X                    by poly_sub_rzero
   = [#0; #1]             by poly_X_def
   = [- #0; #1]           by ring_neg_zero
   If c <> 0, chop [##c] = [##c]
     X - |c|
   = X + (- |c|)          by poly_sub_def
   = - |c| + X            by poly_add_comm
   = - |c| + [#1] >> 1    by poly_X_alt
   = [- ##c] + [#1] >> 1  by poly_chop_cons
   = [- ##c; #1]          by poly_cons_eq_add_shift
*)
val poly_X_sub_c_list = store_thm(
  "poly_X_sub_c_list",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. X - |c| = [- ##c; #1]``,
  rpt strip_tac >>
  Cases_on `c = 0` >-
  rw[] >>
  `X - |c| = -|c| + X` by rw[poly_add_comm] >>
  `_ = -|c| + [#1] >> 1` by rw[poly_X_alt] >>
  `_ = [- ##c] + [#1] >> 1` by rw[poly_one_sum_n] >>
  rw[poly_cons_eq_add_shift]);

(* Theorem: deg (X - |c|) = 1 *)
(* Proof:
   Since poly X              by poly_X
     and poly |c|            by poly_sum_num_poly
     and deg X = 1           by poly_deg_X
     and deg |c| = 0         by poly_deg_sum_num
   Hence deg (X - |c|) = 1   by poly_deg_sub_less
*)
val poly_deg_X_sub_c = store_thm(
  "poly_deg_X_sub_c",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c:num. deg (X - |c|) = 1``,
  rw[poly_deg_sub_less, poly_deg_sum_num]);

(* Theorem: lead (X - |c|) = #1 *)
(* Proof:
   If #1 = #0,
      Note poly (X - |c|)      by poly_X_sub_c
        so X - |c| = |0|       by poly_one_eq_poly_zero, poly_one_eq_zero
       and lead (X - |c|) = #0 by poly_lead_zero
   If #1 <> #0,
   Since poly X                by poly_X
     and poly |c|              by poly_sum_num_poly
     and deg X = 1             by poly_deg_X
     and deg |c| = 0           by poly_deg_sum_num
     and lead X = #1           by poly_lead_X
   Hence lead (X - |c|) = #1   by poly_lead_sub_less
*)
val poly_lead_X_sub_c = store_thm(
  "poly_lead_X_sub_c",
  ``!r:'a ring. Ring r ==> !c:num. lead (X - |c|) = #1``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >| [
    `poly (X - |c|)` by rw[] >>
    `X - |c| = |0|` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
    rw[],
    rw[poly_lead_sub_less, poly_deg_sum_num]
  ]);

(* Theorem: monic (X - |c|) *)
(* Proof: poly_monic_def, poly_X_sub_c, poly_lead_X_sub_c *)
val poly_monic_X_sub_c = store_thm(
  "poly_monic_X_sub_c",
  ``!r:'a ring. Ring r ==> !c:num. monic (X - |c|)``,
  rw_tac std_ss[poly_monic_def, poly_X_sub_c, poly_lead_X_sub_c]);

(* Theorem: #1 <> #0 ==> deg ((X - |c|) ** n) = n  *)
(* Proof:
   We have  poly X           by poly_X
       and  poly |c|         by poly_sum_num_poly
   hence    poly (X - |c|)   by poly_sub_poly
   We have  deg X = 1        by poly_deg_X, when #1 <> #0
            deg |c| = 0      by poly_deg_sum_num
   hence    deg (X - |c|)
          = deg X            by poly_deg_sub_less
          = 1
   and    monic (X - |c|)    by poly_monic_X_add_c
   thus     deg ((X - |c|) ** n)
          = n * deg (X - |c|)     by poly_monic_deg_exp, monic (X - |c|)
          = n                     by arithmetic
*)
val poly_deg_X_sub_c_exp_n = store_thm(
  "poly_deg_X_sub_c_exp_n",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. deg ((X - |c|) ** n) = n``,
  rpt strip_tac >>
  `poly X /\ poly |c| /\ poly (X - |c|)` by rw[poly_X, poly_sum_num_poly] >>
  `lead X = #1` by rw[poly_monic_X] >>
  `deg X = 1` by rw[poly_deg_X] >>
  `deg |c| = 0` by rw[poly_deg_sum_num] >>
  `0 < 1` by decide_tac >>
  `deg (X - |c|) = 1` by rw_tac std_ss[poly_deg_sub_less, poly_add_comm] >>
  `monic (X - |c|)` by rw[poly_monic_X_sub_c] >>
  rw[poly_monic_deg_exp]);

(* Theorem: Ring r /\ n < char r /\ c < char r ==> X - |n| = X - |c| <=> n = c *)
(* Proof:
   If part: X - |n| = X - |c| ==> n = c
         X - |n| = X - |c|
     ==> |n| = |c|      by poly_sub_lcancel
     ==> n = c          by poly_sum_num_eq
   Only-if part: n = c ==> X - |n| = X - |c|
     This is trivially true.
*)
val poly_X_sub_c_eq = store_thm(
  "poly_X_sub_c_eq",
  ``!r:'a ring. Ring r ==>
   !n c. n < char r /\ c < char r ==> ((X - |n| = X - |c|) <=> (n = c))``,
  metis_tac[poly_sub_lcancel, poly_X, poly_sum_num_poly, poly_sum_num_eq]);

(* Theorem: !p. p IN (IMAGE (\c. X - |c|) s) ==> poly p *)
(* Proof:
       p IN (IMAGE (\c. X - |c|) s)
   ==> ?c. p = X - |c|              by IN_IMAGE
   ==> poly p                       by poly_X_sub_c
*)
val poly_X_sub_c_image_element = store_thm(
  "poly_X_sub_c_image_element",
  ``!r:'a ring. Ring r ==> !s p. p IN (IMAGE (\c:num. X - |c|) s) ==> poly p``,
  rpt strip_tac >>
  `!p. p IN (IMAGE (\c. X - |c|) s) <=> ?c. (p = X - |c|) /\ c IN s` by rw[] >>
  `?c. (p = X - |c|) /\ c IN s` by metis_tac[] >>
  rw[poly_X_sub_c]);

(* Theorem: !p. p IN (IMAGE (\c. X - |c|) s) ==> monic p *)
(* Proof:
       p IN (IMAGE (\c. X - |c|) s)
   ==> ?c. p = X - |c|              by IN_IMAGE
   ==> monic p                      by poly_monic_X_sub_c
*)
val poly_monic_X_sub_c_image_element = store_thm(
  "poly_monic_X_sub_c_image_element",
  ``!r:'a ring. Ring r ==> !s p. p IN (IMAGE (\c:num. X - |c|) s) ==> monic p``,
  rpt strip_tac >>
  `!p. p IN (IMAGE (\c. X - |c|) s) <=> ?c. (p = X - |c|) /\ c IN s` by rw[] >>
  `?c. (p = X - |c|) /\ c IN s` by metis_tac[] >>
  rw[poly_monic_X_sub_c]);

(* Theorem: !p. p IN (IMAGE (\c. X - |c|) s) ==> (deg p = 1) *)
(* Proof:
       p IN (IMAGE (\c. X - |c|) s)
   ==> ?c. p = X - |c|              by IN_IMAGE
   ==> deg p = 1                    by poly_deg_X_sub_c
*)
val poly_deg_X_sub_c_image_element = store_thm(
  "poly_deg_X_sub_c_image_element",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !s p. p IN (IMAGE (\c:num. X - |c|) s) ==> (deg p = 1)``,
  rpt strip_tac >>
  `!p. p IN (IMAGE (\c. X - |c|) s) <=> ?c. (p = X - |c|) /\ c IN s` by rw[] >>
  `?c. (p = X - |c|) /\ c IN s` by metis_tac[] >>
  rw[poly_deg_X_sub_c]);

(* Theorem: FINITE s /\ MAX_SET s < char r /\ n < char r ==>
            n IN s <=> X - |n| IN IMAGE (\c. X - |c|) s *)
(* Proof:
   If part: n IN s ==> ?c. (X - |n| = X - |c|) /\ c IN s
      Let c = n, hence true.
   Only-if part: c IN s /\ X - |n| = X - |c| ==> n IN s
     Since c IN s , s <> {}         by MEMBER_NOT_EMPTY
        So c <= MAX_SET s           by MAX_SET_DEF
     hence c < char r               by LESS_EQ_LESS_TRANS
     X - |n| = X - |c| ==> n = c    by poly_X_sub_c_eq
     Hence n IN s.
*)
val poly_X_sub_c_image_property = store_thm(
  "poly_X_sub_c_image_property",
  ``!r:'a ring. Ring r ==>
   !s. FINITE s /\ MAX_SET s < char r ==>
   !n:num. n < char r ==> (n IN s <=> X - |n| IN IMAGE (\c. X - |c|) s)``,
  rw_tac std_ss[IN_IMAGE, EQ_IMP_THM] >-
  metis_tac[] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `c <= MAX_SET s` by rw[MAX_SET_DEF] >>
  `c < char r` by decide_tac >>
  metis_tac[poly_X_sub_c_eq]);

(* ------------------------------------------------------------------------- *)
(* Involving Polynomial X ** n + |c|                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: poly (X ** n + |c|) *)
(* Proof: by poly_X, poly_exp_poly, poly_sum_num_poly, poly_add_poly. *)
val poly_X_exp_n_add_c_poly = store_thm(
  "poly_X_exp_n_add_c_poly",
  ``!r:'a ring. Ring r ==> !c:num n. poly (X ** n + |c|)``,
  rw[]);

(* Theorem: #1 <> #0 ==> deg (X ** n + |c|) = n  *)
(* Proof:
   We have  poly X           by poly_X
       and  poly |c|         by poly_sum_num_poly
      thus  poly (X ** n)    by poly_exp_poly
   We have  deg X = 1        by poly_deg_X, when #1 <> #0
            deg |c| = 0      by poly_deg_sum_num
       and  monic X          by poly_monic_X
      thus  deg (X ** n)
          = n * deg X = n    by poly_monic_deg_exp
   If n = 0, deg (X ** n) = 0
   hence  deg (X ** n + |c|)
        <= MAX deg (X ** n)  deg |c|   by poly_deg_add
        <= MAX 0  0 = 0                by MAX_0
        hence true
   If n <> 0, 0 < n.
          deg (X ** n + |c|)
        = deg (X ** n)       by poly_deg_add_less
        = n
*)
val poly_deg_X_exp_n_add_c = store_thm(
  "poly_deg_X_exp_n_add_c",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c:num n. deg (X ** n + |c|) = n``,
  rpt strip_tac >>
  `poly |c| /\ poly X /\ poly (X ** n)` by rw [poly_sum_num_poly, poly_X] >>
  `deg X = 1` by rw[poly_deg_X] >>
  `deg |c| = 0` by rw[poly_deg_sum_num] >>
  `monic X` by rw[] >>
  `deg (X ** n) = n` by rw[poly_monic_deg_exp] >>
  Cases_on `n = 0` >| [
    `deg (X ** n + |c|) <= 0` by metis_tac [poly_deg_add, MAX_0] >>
    decide_tac,
    `0 < n` by decide_tac >>
    rw_tac std_ss[poly_deg_add_less, poly_add_comm]
  ]);

(* Theorem: 0 < n ==> lead (X ** n + |c|) = #1 *)
(* Proof:
   If #1 = #0,
      Note poly (X ** n + |c|)       by poly_X_exp_n_add_c_poly
        so X ** n + |c| = |0|        by poly_one_eq_poly_zero, poly_one_eq_zero
      Thus lead (X ** n + |c|) = #0  by poly_lead_zero
   If #1 <> #0,
   Since monic X               by poly_monic_X
      so monic (X ** n)        by poly_monic_exp_monic
     Now deg (X ** n) = n      by poly_deg_X_exp
     but deg |c| = 0           by poly_deg_sum_num
   Given 0 < n,
         lead (X ** n + |c|)
       = lead (X ** n)         by poly_lead_add_less_comm
       = #1                    by poly_monic_def
*)
val poly_lead_X_exp_n_add_c = store_thm(
  "poly_lead_X_exp_n_add_c",
  ``!r:'a ring. Ring r ==> !c:num n. 0 < n ==> (lead (X ** n + |c|) = #1)``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >| [
    `poly (X ** n + |c|)` by rw[] >>
    `X ** n + |c| = |0|` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
    rw[],
    rw[poly_deg_sum_num, poly_lead_add_less_comm, poly_monic_def]
  ]);

(* Theorem: monic (X ** n + |c|) *)
(* Proof:
   poly (X ** n + |c|)          by poly_X_exp_n_add_c_poly
   lead (X ** n + |c|) = #1     by poly_lead_X_exp_n_add_c
   Hence monic (X ** n + |c|)   by poly_monic_def
*)
val poly_monic_X_exp_n_add_c = store_thm(
  "poly_monic_X_exp_n_add_c",
  ``!r:'a ring. Ring r ==> !c:num n. 0 < n ==> monic (X ** n + |c|)``,
  rw[poly_monic_def, poly_X_exp_n_add_c_poly, poly_lead_X_exp_n_add_c]);

(* Theorem: eval (X ** n + |c|) x = x ** n + ##c *)
(* Proof:
     eval (X ** n + |c|) x
   = eval (X ** n) x + eval |c| x     by poly_eval_add
   = (eval X x) ** n + eval |c| x     by poly_eval_exp
   = x ** n + eval |c| x              by poly_eval_X
   = x ** n + ##c                     by poly_eval_const
*)
val poly_eval_X_exp_n_add_c = store_thm(
  "poly_eval_X_exp_n_add_c",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !c:num n. eval (X ** n + |c|) x = x ** n + ##c``,
  rw[poly_eval_add, poly_eval_exp, poly_eval_one_sum_n]);

(* Theorem: ##c <> #0 ==> !n. 0 < n ==> X ** n + |c| = [##c] || [#1] >> n  *)
(* Proof:
   Since ##c <> #0, #1 <> #0   by ring_num_all_zero
   X ** n = [#1] >> n          by poly_X_exp_n
   poly X and monic X          by poly_X, poly_monic_X
   deg X = 1                   by poly_deg_X, #1 <> #0
   deg (X ** n) = n            by poly_monic_deg_exp
   poly |c|                    by poly_sum_num_poly
   deg |c| = 0                 by poly_deg_sum_num
   Since ##c <> #0
   and |c| = [##c]             by poly_one_sum_n, poly_chop_poly
   Since 0 <> n
     poly (X ** n || |c|)      by poly_weak_add_poly
     X ** n + |c|
   = X ** n || |c|             by poly_add_def, poly_chop_poly
   = |c| || X ** n             by weak_add_comm
   = [##c] || [#1] >> n        by above
*)
val poly_X_exp_n_add_c = store_thm(
  "poly_X_exp_n_add_c",
  ``!r:'a ring. Ring r ==> !c. ##c <> #0 ==> !n. 0 < n ==> (X ** n + |c| = [##c] || [#1] >> n)``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac [ring_num_all_zero] >>
  `poly X /\ monic X /\ poly (X ** n)` by rw[] >>
  `deg (X ** n) = n` by rw[poly_monic_deg_exp] >>
  `poly |c|` by rw[poly_sum_num_poly] >>
  `deg |c| = 0` by rw[poly_deg_sum_num] >>
  `|c| = [##c]` by rw[poly_one_sum_n] >>
  `0 <> n` by decide_tac >>
  `poly (X ** n || |c|)` by rw[poly_weak_add_poly] >>
  `X ** n + |c| = X ** n || |c|` by rw_tac std_ss[poly_add_def, poly_chop_poly] >>
  rw[poly_X_exp_n, weak_add_comm]);
(* can be improved to: !c. ##c <> #0 ==> !n. 0 < n ==> (X ** n + |c| = [##c] + [#1] >> n)
   but the proof is complicated by cases. *)

(* Theorem: Ring r /\ #1 <> #0 ==> !n. 0 < n ==>
            !c:num. X ** n + |c| = ##c :: PAD_LEFT #0 n [#1] *)
(* Proof:
   Since n <> 0, n = SUC k  for some k    by num_CASES.
   Note poly |c|               by poly_sum_num_poly
    and weak [##c]             by weak_ring_sum_c
    and weak (X ** n)          by poly_X_exp_n, poly_is_weak
   Note X ** k <> |0|          by poly_X_exp_nonzero, #1 <> #0
   Thus poly (##c :: X ** k)   by poly_nonzero_cons_poly, for [1]
     X ** n + |c|
   = |c| + X ** n                       by poly_add_comm
   = chop [##c] + X ** n                by poly_ring_sum_c
   = [##c] + X ** n                     by poly_add_weak_right
   = [##c] + X ** (SUC k)               by n = SUC k
   = [##c] + X ** k * X                 by poly_exp_suc
   = [##c] + (X ** k) >> 1              by poly_mult_X
   = ##c :: (X ** k)                    by poly_cons_eq_add_shift, [1]
   = ##c :: PAD_LEFT #0 (SUC k) [#1]    by poly_X_exp_n_alt
   = ##c :: PAD_LEFT #0 n [#1]          by n = SUC k
*)
val poly_X_exp_n_add_c_alt = store_thm(
  "poly_X_exp_n_add_c_alt",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. 0 < n ==>
   !c:num. X ** n + |c| = ##c :: PAD_LEFT #0 n [#1]``,
  rpt strip_tac >>
  `poly |c|` by rw[poly_sum_num_poly] >>
  `weak [##c]` by rw[weak_ring_sum_c] >>
  `weak (X ** n)` by rw[] >>
  `?k. n = SUC k` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO] >>
  `X ** k <> |0|` by rw[poly_X_exp_nonzero] >>
  `poly (##c :: X ** k)` by rw[poly_nonzero_cons_poly] >>
  `X ** n + |c| = |c| + X ** n` by rw[poly_add_comm] >>
  `_ = chop [##c] + X ** n` by rw[poly_ring_sum_c] >>
  `_ = [##c] + X ** (SUC k)` by rw_tac std_ss[poly_add_weak_right] >>
  `_ = [##c] + X ** k * X` by rw[poly_exp_suc] >>
  `_ = [##c] + (X ** k) >> 1` by rw[poly_mult_X] >>
  `_ = ##c :: (X ** k)` by rw[poly_cons_eq_add_shift] >>
  `_ = ##c :: PAD_LEFT #0 n [#1]` by rw[poly_X_exp_n_alt] >>
  rw[]);

(* Theorem: Ring r /\ #1 <> #0 ==> !n k c. 0 < k /\ k < n ==> ((X ** n + |c|) ' k = #0) *)
(* Proof:
   Let p = ##c::PAD_LEFT #0 n [#1].
   Then X ** n + |c| = p                     by poly_X_exp_n_add_c_alt
   Note p <> |0|                             by NOT_NIL_CONS, poly_zero
        LENGTH p
      = SUC (LENGTH (PAD_LEFT #0 n [#1]))    by LENGTH
      = SUC (MAX n 1)                        by PAD_LEFT_LENGTH
      = SUC n                                by MAX_DEF, 0 < n
   Note 0 < k ==> ?m. k = SUC m              by num_CASES
    and k < n ==> SUC m < n, or m < n - 1    by arithmetic
        (X ** n + |c|) ' k
      = p ' k                                by above
      = EL (SUC m) p                         by poly_coeff_nonzero_alt
      = EL m (PAD_LEFT #0 n [#1])            by EL
      = #0                                   by PAD_LEFT, EL_APPEND
*)
val poly_coeff_X_exp_n_add_c = store_thm(
  "poly_coeff_X_exp_n_add_c",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n k c:num. 0 < k /\ k < n ==> ((X ** n + |c|) ' k = #0)``,
  rpt strip_tac >>
  qabbrev_tac `p = ##c::PAD_LEFT #0 n [#1]` >>
  `X ** n + |c| = p` by rw[poly_X_exp_n_add_c_alt, Abbr`p`] >>
  `p <> |0|` by rw[Abbr`p`] >>
  `LENGTH p = SUC (LENGTH (PAD_LEFT #0 n [#1]))` by rw[Abbr`p`] >>
  `_ = SUC (MAX n 1)` by rw[PAD_LEFT_LENGTH] >>
  `_ = SUC n` by rw[MAX_DEF] >>
  `k <> 0` by decide_tac >>
  `?m. k = SUC m` by metis_tac[num_CASES] >>
  `m < n - 1` by decide_tac >>
  `p ' k = EL (SUC m) p` by rw[poly_coeff_nonzero_alt] >>
  `_ = EL m (PAD_LEFT #0 n [#1])` by rw[Abbr`p`] >>
  `_ = #0` by rw[PAD_LEFT, EL_APPEND] >>
  rw[]);

(* Theorem: (X ** n == -|c|) (pm (X ** n + |c|)) *)
(* Proof:
   X ** n = |1| * (X ** n + |c|) + -|c|        by poly_mult_lone, poly_sub_add
   deg (X ** n + |c|) = n                      by poly_deg_X_exp_n_sub_c
   deg (-|c|) = 0 < n                          by poly_deg_sum_num, poly_deg_neg
   Hence X ** n % (X ** n + |c|) = -|c|        by poly_div_mod_eqn
    also   -|c| % (X ** n + |c|) = -|c|        by poly_mod_less
   or    (X ** n == -|c|) (pm (X ** n + |c|))  by pmod_def_alt
*)
val poly_mod_X_exp_n_add_c = store_thm(
  "poly_mod_X_exp_n_add_c",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !(c n):num. 0 < n ==> (X ** n == -|c|) (pm (X ** n + |c|))``,
  rpt strip_tac >>
  `poly |1| /\ poly (X ** n)` by rw[] >>
  `poly |c| /\ poly (-|c|) /\ poly (X ** n + |c|)` by rw[] >>
  `deg (X ** n + |c|) = n` by rw[poly_deg_X_exp_n_add_c] >>
  `deg (-|c|) = 0` by rw[poly_deg_sum_num, poly_deg_neg] >>
  `lead (X ** n + |c|) = #1` by rw[poly_monic_X_exp_n_add_c] >>
  `X ** n = |1| * (X ** n + |c|) - |c|` by rw_tac std_ss[poly_add_sub, poly_mult_lone] >>
  `_ = |1| * (X ** n + |c|) + (-|c|)` by rw_tac std_ss[poly_sub_def] >>
  `X ** n % (X ** n + |c|) = -|c|` by metis_tac[poly_div_mod_eqn, ring_unit_one] >>
  `-|c| % (X ** n + |c|) = -|c|` by rw[poly_mod_less] >>
  rw[pmod_def_alt]);

(* ------------------------------------------------------------------------- *)
(* Involving Polynomial X ** n - |c|                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: !n. poly (X ** n - |c|) *)
(* Proof:
   Since  poly X                by poly_X
     and  poly (X ** n)         by poly_exp_poly
    also  poly |c|              by poly_sum_num_poly
    hence poly (X ** n - |c|)   by poly_sub_poly
*)
val poly_X_exp_n_sub_c_poly = store_thm(
  "poly_X_exp_n_sub_c_poly",
  ``!r:'a ring. Ring r ==> !c:num n. poly (X ** n - |c|)``,
  rw[poly_sum_num_poly]);

(* Theorem: #1 <> #0 ==> deg (X ** n - |c|) = n  *)
(* Proof:
   We have  poly X           by poly_X
       and  poly |c|         by poly_sum_num_poly
            poly -|c|        by poly_neg_poly
      thus  poly (X ** n)    by poly_exp_poly
   We have  deg X = 1        by poly_deg_X, when #1 <> #0
            deg |c| = 0      by poly_deg_sum_num
       and  monic X          by poly_monic_X
      thus  deg (X ** n)
          = n * deg X = n    by poly_monic_deg_exp
   If n = 0, deg (X ** n) = 0
   hence  deg (X ** n - |c|)
        <= MAX deg (X ** n)  deg |c|   by poly_deg_sub
        <= MAX 0  0 = 0                by MAX_0
        hence true
   If n <> 0, 0 < n.
          deg (X ** n - |c|)
        = deg (X ** n + -|c|)   by poly_sub_def
        = deg (X ** n)          by poly_deg_add_less, poly_neg_ply, poly_deg_neg
        = n
*)
val poly_deg_X_exp_n_sub_c = store_thm(
  "poly_deg_X_exp_n_sub_c",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c:num n. deg (X ** n - |c|) = n``,
  rpt strip_tac >>
  `poly |c| /\ poly (-|c|) /\ poly X /\ poly (X ** n)` by rw[poly_sum_num_poly, poly_X] >>
  `deg X = 1` by rw[poly_deg_X] >>
  `deg |c| = 0` by rw[poly_deg_sum_num] >>
  `monic X` by rw[] >>
  `deg (X ** n) = n` by rw[poly_monic_deg_exp] >>
  Cases_on `n = 0` >| [
    `deg (X ** n - |c|) <= 0` by metis_tac [poly_deg_sub, MAX_0] >>
    decide_tac,
    `0 < n` by decide_tac >>
    rw_tac std_ss[poly_deg_add_less, poly_sub_def, poly_neg_poly, poly_deg_neg, poly_add_comm]
  ]);

(* Theorem: 0 < n ==> lead (X ** n - |c|) = #1 *)
(* Proof:
   If #1 = #0,
      Note poly (X ** n - |c|)      by poly_X_exp_n_sub_c_poly
        so X ** n - |c| = |0|       by poly_one_eq_poly_zero, poly_one_eq_zero
        or lead (X ** n - |c|) = #0 by poly_lead_zero
   If #1 <> #0,
   Since deg (X ** n) = n           by poly_deg_X_exp
     and deg |c| = 0                by poly_deg_sum_num
    Also monic (X ** n)             by poly_monic_X, poly_monic_exp_monic
      so lead (X ** n) = #1         by poly_monic_def
   Hence lead (X ** n - |c|) = #1   by poly_lead_sub_less
*)
val poly_lead_X_exp_n_sub_c = store_thm(
  "poly_lead_X_exp_n_sub_c",
  ``!r:'a ring. Ring r ==> !c:num n. 0 < n ==> (lead (X ** n - |c|) = #1)``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >| [
    `poly (X ** n - |c|)` by rw[] >>
    `X ** n - |c| = |0|` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero] >>
    rw[],
    `deg (X ** n) = n` by rw[poly_deg_X_exp] >>
    `deg |c| = 0` by rw[poly_deg_sum_num] >>
    `lead (X ** n) = #1` by rw[] >>
    rw[poly_lead_sub_less]
  ]);

(* Theorem: !n. monic (X ** n - |c|) *)
(* Proof:
   By poly_monic_def, this is to show:
   (1) poly (X ** n - |c|), true       by poly_X_exp_n_sub_c_poly
   (2) lead (X ** n - |c|) = #1, true  by poly_lead_X_exp_n_sub_c
*)
val poly_monic_X_exp_n_sub_c = store_thm(
  "poly_monic_X_exp_n_sub_c",
  ``!r:'a ring. Ring r ==> !c:num n. 0 < n ==> monic (X ** n - |c|)``,
  rw_tac std_ss[poly_monic_def, poly_X_exp_n_sub_c_poly, poly_lead_X_exp_n_sub_c]);

(* Theorem: eval (X ** n - |c|) x = x ** n - ##c *)
(* Proof:
     eval (X ** n - |c|) x
   = eval (X ** n) x - eval |c| x     by poly_eval_sub
   = (eval X x) ** n - eval |c| x     by poly_eval_exp
   = x ** n - eval |c| x              by poly_eval_X
   = x ** n - ##c                     by poly_eval_const
*)
val poly_eval_X_exp_n_sub_c = store_thm(
  "poly_eval_X_exp_n_sub_c",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !c:num n. eval (X ** n - |c|) x = x ** n - ##c``,
  rw[poly_eval_sub, poly_eval_exp, poly_eval_one_sum_n]);

(* Theorem: ##c <> #0 ==> !n. 0 < n ==> X ** n - |c| = [- ##c] || [#1] >> n  *)
(* Proof:
   Since ##c <> #0, #1 <> #0   by ring_num_all_zero
   X ** n = [#1] >> n          by poly_X_exp_n
   poly X and monic X          by poly_X, poly_monic_X
   deg X = 1                   by poly_deg_X, #1 <> #0
   deg (X ** n) = n            by poly_monic_deg_exp
   poly -|c|                   by poly_sum_num_poly
   deg -|c| = 0                by poly_deg_sum_num, poly_deg_neg
   Since ##c <> #0
   and -|c| = [- ##c]          by poly_one_sum_n, poly_chop_poly
   Since 0 <> n
     poly (X ** n || -|c|)     by poly_weak_add_poly
     X ** n - |c|
   = X ** n + (- |c|)          by poly_sub_def
   = X ** n || - |c|           by poly_add_def, poly_chop_poly
   = - |c| || X ** n           by weak_add_comm
   = [- ##c] || [#1] >> n      by above
*)
val poly_X_exp_n_sub_c = store_thm(
  "poly_X_exp_n_sub_c",
  ``!r:'a ring. Ring r ==> !c. ##c <> #0 ==> !n. 0 < n ==> (X ** n - |c| = [- ##c] || [#1] >> n)``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac [ring_num_all_zero] >>
  `poly X /\ monic X /\ poly (X ** n)` by rw[] >>
  `deg (X ** n) = n` by rw[poly_monic_deg_exp] >>
  `poly (-|c|)` by rw[poly_sum_num_poly] >>
  `deg (-|c|) = 0` by rw[poly_deg_sum_num, poly_deg_neg] >>
  `-|c| = [- ##c]` by rw[poly_one_sum_n] >>
  `0 <> n` by decide_tac >>
  `poly (X ** n || -|c|)` by rw[poly_weak_add_poly] >>
  `X ** n - |c| = X ** n || (-|c|)` by rw_tac std_ss[poly_sub_def, poly_add_def, poly_chop_poly] >>
  rw[poly_X_exp_n, weak_add_comm]);
(* can be improved to: !c. ##c <> #0 ==> !n. 0 < n ==> (X ** n - |c| = [-##c] + [#1] >> n)
   but the proof is complicated by cases. *)

(* Theorem: Ring r /\ #1 <> #0 ==> !n. 0 < n ==>
            !c:num. X ** n - |c| = - ##c :: PAD_LEFT #0 n [#1] *)
(* Proof:
   Since n <> 0, n = SUC k  for some k    by num_CASES.
   Note poly (-|c|)            by poly_sum_num_poly
    and weak [- ##c]           by weak_ring_sum_c
    and weak (X ** n)          by poly_X_exp_n, poly_is_weak
   Note X ** k <> |0|          by poly_X_exp_nonzero, #1 <> #0
   Thus poly (-##c :: X ** k)  by poly_nonzero_cons_poly, for [1]
     X ** n - |c|
   = -|c| + X ** n                        by poly_sub_def, poly_add_comm
   = chop [- ##c] + X ** n                by poly_ring_sum_c
   = [- ##c] + X ** n                     by poly_add_weak_right
   = [- ##c] + X ** (SUC k)               by n = SUC k
   = [- ##c] + X ** k * X                 by poly_exp_suc
   = [- ##c] + (X ** k) >> 1              by poly_mult_X
   = - ##c :: (X ** k)                    by poly_cons_eq_add_shift, [1]
   = - ##c :: PAD_LEFT #0 (SUC k) [#1]    by poly_X_exp_n_alt
   = - ##c :: PAD_LEFT #0 n [#1]          by n = SUC k
*)
val poly_X_exp_n_sub_c_alt = store_thm(
  "poly_X_exp_n_sub_c_alt",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. 0 < n ==>
   !c:num. X ** n - |c| = - ##c :: PAD_LEFT #0 n [#1]``,
  rpt strip_tac >>
  `poly (-|c|)` by rw[poly_sum_num_poly] >>
  `weak [- ##c]` by rw[weak_ring_sum_c] >>
  `weak (X ** n)` by rw[] >>
  `?k. n = SUC k` by metis_tac[num_CASES, NOT_ZERO] >>
  `X ** k <> |0|` by rw[poly_X_exp_nonzero] >>
  `poly (- ##c :: X ** k)` by rw[poly_nonzero_cons_poly] >>
  `X ** n - |c| = -|c| + X ** n` by rw[poly_add_comm] >>
  `_ = chop [- ##c] + X ** n` by rw[poly_ring_sum_c] >>
  `_ = [- ##c] + X ** (SUC k)` by rw_tac std_ss[poly_add_weak_right] >>
  `_ = [- ##c] + X ** k * X` by rw[poly_exp_suc] >>
  `_ = [- ##c] + (X ** k) >> 1` by rw[poly_mult_X] >>
  `_ = - ##c :: (X ** k)` by rw[poly_cons_eq_add_shift] >>
  `_ = - ##c :: PAD_LEFT #0 n [#1]` by rw[poly_X_exp_n_alt] >>
  rw[]);

(* Theorem: Ring r /\ #1 <> #0 ==> !n k c. 0 < k /\ k < n ==> ((X ** n - |c|) ' k = #0) *)
(* Proof:
   Let p = - ##c::PAD_LEFT #0 n [#1].
   Then X ** n - |c| = p                     by poly_X_exp_n_sub_c_alt
   Note p <> |0|                             by NOT_NIL_CONS, poly_zero
        LENGTH p
      = SUC (LENGTH (PAD_LEFT #0 n [#1]))    by LENGTH
      = SUC (MAX n 1)                        by PAD_LEFT_LENGTH
      = SUC n                                by MAX_DEF, 0 < n
   Note 0 < k ==> ?m. k = SUC m              by num_CASES
    and k < n ==> SUC m < n, or m < n - 1    by arithmetic
        (X ** n - |c|) ' k
      = p ' k                                by above
      = EL (SUC m) p                         by poly_coeff_nonzero_alt
      = EL m (PAD_LEFT #0 n [#1])            by EL
      = #0                                   by PAD_LEFT, EL_APPEND
*)
val poly_coeff_X_exp_n_sub_c = store_thm(
  "poly_coeff_X_exp_n_sub_c",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n k c:num. 0 < k /\ k < n ==> ((X ** n - |c|) ' k = #0)``,
  rpt strip_tac >>
  qabbrev_tac `p = - ##c::PAD_LEFT #0 n [#1]` >>
  `X ** n - |c| = p` by rw[poly_X_exp_n_sub_c_alt, Abbr`p`] >>
  `p <> |0|` by rw[Abbr`p`] >>
  `LENGTH p = SUC (LENGTH (PAD_LEFT #0 n [#1]))` by rw[Abbr`p`] >>
  `_ = SUC (MAX n 1)` by rw[PAD_LEFT_LENGTH] >>
  `_ = SUC n` by rw[MAX_DEF] >>
  `k <> 0` by decide_tac >>
  `?m. k = SUC m` by metis_tac[num_CASES] >>
  `m < n - 1` by decide_tac >>
  `p ' k = EL (SUC m) p` by rw[poly_coeff_nonzero_alt] >>
  `_ = EL m (PAD_LEFT #0 n [#1])` by rw[Abbr`p`] >>
  `_ = #0` by rw[PAD_LEFT, EL_APPEND] >>
  rw[]);

(* Theorem: (X ** n == |c|) (pm (X ** n - |c|)) *)
(* Proof:
   X ** n = |1| * (X ** n - |c|) + |c|         by poly_mult_lone, poly_sub_add
   deg (X ** n - |c|) = n                      by poly_deg_X_exp_n_sub_c
   deg |c| = 0 < n                             by poly_deg_sum_num
   Hence X ** n % (X ** n - |c|) = |c|         by poly_div_mod_eqn
    also    |c| % (X ** n - |c|) = |c|         by poly_mod_less
   or    (X ** n == |c|) (pm (X ** n - |c|))   by pmod_def_alt
*)
val poly_mod_X_exp_n_sub_c = store_thm(
  "poly_mod_X_exp_n_sub_c",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !(c n):num. 0 < n ==> (X ** n == |c|) (pm (X ** n - |c|))``,
  rpt strip_tac >>
  `poly |1| /\ poly (X ** n)` by rw[] >>
  `poly |c| /\ poly (X ** n - |c|)` by rw[] >>
  `deg (X ** n - |c|) = n` by rw[poly_deg_X_exp_n_sub_c] >>
  `deg |c| = 0` by rw[poly_deg_sum_num] >>
  `lead (X ** n - |c|) = #1` by rw[poly_monic_X_exp_n_sub_c] >>
  `X ** n = |1| * (X ** n - |c|) + |c|` by rw_tac std_ss[poly_sub_add, poly_mult_lone] >>
  `X ** n % (X ** n - |c|) = |c|` by metis_tac[poly_div_mod_eqn, ring_unit_one] >>
  `|c| % (X ** n - |c|) = |c|` by rw[poly_mod_less] >>
  rw[pmod_def_alt]);

(* ------------------------------------------------------------------------- *)
(* Pseudo-monic Polynomials                                                  *)
(* ------------------------------------------------------------------------- *)

(*
Note: pmonic p = poly p /\ 0 < deg p /\ unit (lead p)
These pseudo-monic polynomials act as divisor for polynomial division.
*)

(* Theorem: pmonic (X + |c|) *)
(* Proof:
   Since monic (X + |c|)         by poly_monic_X_add_c
   hence by poly_monic_def,
         poly (X + |c|) and
         lead (X + |c|) = #1
      or unit (lead (X + |c|))   by ring_unit_one

    Also deg (X + |c|) = 1       by poly_deg_X_add_c
   hence 0 < deg (X + |c|)
*)
val poly_pmonic_X_add_c = store_thm(
  "poly_pmonic_X_add_c",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c:num. pmonic (X + |c|)``,
  rw[poly_monic_X_add_c, poly_deg_X_add_c]);

(* Theorem: pmonic (X - |c|) *)
(* Proof:
   By pmonic notation, this is to show:
   (1) poly (X - |c|), true             by poly_X_sub_c
   (2) 0 < deg (X - |c|), true          by poly_deg_X_sub_c
   (3) unit (lead (X ** n - |c|)), true by poly_lead_X_sub_c
*)
val poly_pmonic_X_sub_c = store_thm(
  "poly_pmonic_X_sub_c",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c:num n. pmonic (X - |c|)``,
  rw[poly_monic_X_sub_c, poly_deg_X_sub_c]);

(* Theorem: pmonic (X ** n + |c|) *)
(* Proof:
   By pmonic notation, this is to show:
   (1) poly (X ** n + |c|), true        by poly_X_exp_n_add_c
   (2) 0 < deg (X ** n + |c|), true     by poly_deg_X_exp_n_add_c
   (3) unit (lead (X ** n + |c|)), true by poly_monic_X_exp_n_add_c
*)
val poly_pmonic_X_exp_n_add_c = store_thm(
  "poly_pmonic_X_exp_n_add_c",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c:num n. 0 < n ==> pmonic (X ** n + |c|)``,
  rw[poly_monic_X_exp_n_add_c, poly_deg_X_exp_n_add_c]);

(* Theorem: pmonic (X ** n - |c|) *)
(* Proof:
   By pmonic notation, this is to show:
   (1) poly (X ** n - |c|), true        by poly_X_exp_n_sub_c_poly
   (2) 0 < deg (X ** n - |c|), true     by poly_deg_X_exp_n_sub_c
   (3) unit (lead (X ** n - |c|)), true by poly_monic_X_exp_n_sub_c
*)
val poly_pmonic_X_exp_n_sub_c = store_thm(
  "poly_pmonic_X_exp_n_sub_c",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c:num n. 0 < n ==> pmonic (X ** n - |c|)``,
  rw[poly_monic_X_exp_n_sub_c, poly_deg_X_exp_n_sub_c]);

(* Theorem: (X + |c|) % (X + |n|) = |0| <=> X + |c| = X + |n| *)
(* Proof:
   If part: (X + |c|) % (X + |n|) = |0| ==> X + |c| = X + |n|
      (X + |c|) % (X + |n|) = |0|
   ==> (X + |c|) = q * (X + |n|)         by poly_mod_eq_zero
   ==> monic q                           by poly_monic_monic_mult
   Hence   1 = (deg q) + 1               by poly_monic_deg_mult, poly_deg_X_add_c
    Thus   deg q = 0
   Since   lead q = #1                   by poly_monic_lead
      so  q <> |0|, q = [#1] = |1|       by poly_deg_eq_zero
     and  X + |c| = X + |n|              by poly_mult_rone
   Only-if part: X + |c| = X + |n| ==> (X + |c|) % (X + |n|) = |0|
     Since pmonic (X + |c|)              by poly_pmonic_X_add_c
        so (X + |c|) % (X + |c|) = |0|   by poly_div_mod_id
*)
val poly_X_add_c_factor = store_thm(
  "poly_X_add_c_factor",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c:num n:num. ((X + |c|) % (X + |n|) = |0|) <=> (X + |c| = X + |n|)``,
  rpt strip_tac >>
  `pmonic (X + |c|) /\ pmonic (X + |n|)` by rw[poly_pmonic_X_add_c] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    `?q. poly q /\ ((X + |c|) = q * (X + |n|))` by metis_tac[poly_mod_eq_zero] >>
    `monic (X + |c|) /\ monic (X + |n|)` by rw[poly_monic_X_add_c] >>
    `monic q` by metis_tac[poly_monic_monic_mult, poly_mult_comm] >>
    `lead q = #1` by rw[] >>
    `1 = deg q + 1` by metis_tac[poly_monic_deg_mult, poly_deg_X_add_c] >>
    `deg q = 0` by decide_tac >>
    `q <> |0|` by metis_tac[poly_lead_zero] >>
    `q = |1|` by metis_tac[poly_deg_eq_zero, poly_lead_const, poly_one] >>
    rw[],
    rw[poly_div_mod_id]
  ]);

(* Theorem: (X - |c|) % (X - |n|) = |0| <=> X - |c| = X - |n| *)
(* Proof:
   If part: (X - |c|) % (X - |n|) = |0| ==> X - |c| = X - |n|
      (X - |c|) % (X - |n|) = |0|
   ==> (X - |c|) = q * (X - |n|)         by poly_mod_eq_zero
   ==> monic q                           by poly_monic_monic_mult
   Hence   1 = (deg q) + 1               by poly_monic_deg_mult, poly_deg_X_sub_c
    Thus   deg q = 0
   Since   lead q = #1                   by poly_monic_lead
      so  q <> |0|, q = [#1] = |1|       by poly_deg_eq_zero
     and  X - |c| = X - |n|              by poly_mult_rone
   Only-if part: X - |c| = X - |n| ==> (X - |c|) % (X - |n|) = |0|
     Since pmonic (X - |c|)              by poly_pmonic_X_sub_c
        so (X - |c|) % (X - |c|) = |0|   by poly_div_mod_id
*)
val poly_X_sub_c_factor = store_thm(
  "poly_X_sub_c_factor",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c:num n:num. ((X - |c|) % (X - |n|) = |0|) <=> (X - |c| = X - |n|)``,
  rpt strip_tac >>
  `pmonic (X - |c|) /\ pmonic (X - |n|)` by rw[poly_pmonic_X_sub_c] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    `?q. poly q /\ ((X - |c|) = q * (X - |n|))` by metis_tac[poly_mod_eq_zero] >>
    `monic (X - |c|) /\ monic (X - |n|)` by rw[poly_monic_X_sub_c] >>
    `monic q` by metis_tac[poly_monic_monic_mult, poly_mult_comm] >>
    `lead q = #1` by rw[] >>
    `1 = deg q + 1` by metis_tac[poly_monic_deg_mult, poly_deg_X_sub_c] >>
    `deg q = 0` by decide_tac >>
    `q <> |0|` by metis_tac[poly_lead_zero] >>
    `q = |1|` by metis_tac[poly_deg_eq_zero, poly_lead_const, poly_one] >>
    rw[],
    rw[poly_div_mod_id]
  ]);

(* ------------------------------------------------------------------------- *)
(* The Unity Polynomial (X ** n - |1|)                                       *)
(* ------------------------------------------------------------------------- *)

(* Overload on unity polynomial *)
val _ = overload_on("Unity", ``\(r:'a ring) n. X ** n - |1|``);
val _ = overload_on("unity", ``Unity r``);

(* Theorem: poly (unity n) *)
(* Proof: by poly_X, poly_exp_poly, poly_sub_poly, poly_one_poly *)
val poly_unity_poly = store_thm(
  "poly_unity_poly",
  ``!r:'a ring. Ring r ==> !n. poly (unity n)``,
  rw[]);

(* export simple result *)
val _ = export_rewrites ["poly_unity_poly"];

(* Theorem: unity 0 = |0| *)
(* Proof:
      unity 0
    = X ** 0 - |1|      by notation
    = |1| - |1|         by poly_exp_0
    = |0|               by poly_sub_self
*)
val poly_unity_0 = store_thm(
  "poly_unity_0",
  ``!r:'a ring. Ring r ==> (unity 0 = |0|)``,
  rw[]);

(* Theorem: unity 1 = X - |1| *)
(* Proof:
      unity 1
    = X ** 1 - |1|      by notation
    = X - |1|           by poly_exp_1
*)
val poly_unity_1 = store_thm(
  "poly_unity_1",
  ``!r:'a ring. Ring r ==> (unity 1 = X - |1|)``,
  rw[]);

(* export simple results *)
val _ = export_rewrites ["poly_unity_0", "poly_unity_1"];

(* Theorem: Ring r /\ #1 <> #0 ==> !n. (unity n = |0|) <=> (n = 0) *)
(* Proof:
   If part: (unity n = |0|) ==> (n = 0)
      Since unity n = |0|
        ==> X ** n = |1|   by poly_sub_eq_zero
         so n = 0          by poly_X_exp_eq_one
   Only-if part: (n = 0) ==> (unity n = |0|)
        unity 0 = |0|      by poly_unity_0
*)
val poly_unity_eq_zero = store_thm(
  "poly_unity_eq_zero",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. (unity n = |0|) <=> (n = 0)``,
  rpt strip_tac >>
  `poly X /\ poly (X ** n) /\ poly |1| /\ poly |0|` by rw[] >>
  rw_tac std_ss[EQ_IMP_THM] >-
  metis_tac[poly_sub_eq_zero, poly_X_exp_eq_one] >>
  rw[]);

(* Theorem: deg (unity n) = n *)
(* Proof:
   If n = 0,
    unity 0 = |0|            by poly_unity_0
    and deg |0| = 0          by poly_deg_zero
   If n <> 0, 0 < n.
   Since deg (X ** n) = n    by poly_deg_X_exp
     and deg |1| = 0         by poly_deg_one
   Hence deg (unity n) = n   by poly_deg_sub_less
   Or, true                  by poly_deg_X_exp_n_sub_c
*)
val poly_unity_deg = store_thm(
  "poly_unity_deg",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. deg (unity n) = n``,
  metis_tac[poly_deg_X_exp_n_sub_c, poly_ring_sum_1]);

(* export simple result *)
val _ = export_rewrites ["poly_unity_deg"];

(* Theorem: 0 < n ==> lead (unity n) = #1 *)
(* Proof:
   If #1 = #0,
      Then |1| = |0|         by poly_one_eq_poly_zero
        so unity n = |0|     by poly_one_eq_zero, poly_unity_poly
       and lead (unity n)
          = #0 = #1          by poly_lead_zero
   If #1 <> #0,
   Since deg (X ** n) = n    by poly_deg_X_exp
     and deg |1| = 0         by poly_deg_one
    Also monic (X ** n)      by poly_monic_X, poly_monic_exp_monic
      so lead (X ** n) = #1  by poly_monic_def
   Hence lead (unity n) = #1 by poly_lead_sub_less
   Or, true                  by poly_lead_X_exp_n_sub_c
*)
val poly_unity_lead = store_thm(
  "poly_unity_lead",
  ``!r:'a ring. Ring r ==> !n. 0 < n ==> (lead (unity n) = #1)``,
  metis_tac[poly_lead_X_exp_n_sub_c, poly_ring_sum_1]);

(* export simple result *)
val _ = export_rewrites ["poly_unity_lead"];

(* Theorem: 0 < n ==> monic (unity n) *)
(* Proof: by poly_monic_def, poly_unity_poly, poly_unity_lead. *)
val poly_unity_monic = store_thm(
  "poly_unity_monic",
  ``!r:'a ring. Ring r ==> !n. 0 < n ==> monic (unity n)``,
  rw_tac std_ss[poly_monic_def, poly_unity_poly, poly_unity_lead]);

(* export simple result *)
val _ = export_rewrites ["poly_unity_monic"];

(* Theorem: Ring r ==> !n. 0 < n ==> ulead (unity n) *)
(* Proof:
   Note poly (unity n)        by poly_unity_poly
    and lead (unity n) = #1   by poly_unity_lead, 0 < n
    and unit #1               by ring_unit_one
   Thus ulead (unity n)       by notation
*)
val poly_unity_ulead = store_thm(
  "poly_unity_ulead",
  ``!r:'a ring. Ring r ==> !n. 0 < n ==> ulead (unity n)``,
  rw[]);

(* Theorem: 0 < n ==> pmonic (unity n) *)
(* Proof:
   This is to show:
   (1) poly (unity n),        true by poly_unity_poly
   (2) unit (lead (unity n)), true by poly_unity_lead, ring_unit_one
   (3) 0 < deg (unity n)      true poly_unity_deg, 0 < n.
   Or,
   by poly_pmonic_X_exp_n_sub_c
*)
val poly_unity_pmonic = store_thm(
  "poly_unity_pmonic",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. 0 < n ==> pmonic (unity n)``,
  rw_tac std_ss[poly_unity_poly, poly_unity_lead, poly_unity_deg, ring_unit_one]);

(* Theorem: Ring r /\ #1 <> #0 ==> !m n. (unity m = unity n) <=> (m = n) *)
(* Proof: by poly_unity_deg *)
val poly_unity_eq = store_thm(
  "poly_unity_eq",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !m n. (unity m = unity n) <=> (m = n)``,
  metis_tac[poly_unity_deg]);

(* ------------------------------------------------------------------------- *)
(* Master Polynomial: X ** n - X.                                            *)
(* ------------------------------------------------------------------------- *)

(* Overload on master equation (or universal equation) *)
val _ = overload_on("Master", ``\(r:'a ring) n. X ** n - X``);
val _ = overload_on("master", ``Master r``);

(* Theorem: Ring r ==> !n. poly (master n) *)
(* Proof: by poly_X, poly_exp_poly, poly_sub_poly *)
val poly_master_poly = store_thm(
  "poly_master_poly",
  ``!r:'a ring. Ring r ==> !n. poly (master n)``,
  rw[]);

(* export simple result *)
val _ = export_rewrites ["poly_master_poly"];

(* Theorem: master 0 = |1| - X *)
(* Proof: by notation *)
val poly_master_0 = store_thm(
  "poly_master_0",
  ``!r:'a ring. master 0 = |1| - X``,
  rw[]);

(* export simple result *)
val _ = export_rewrites ["poly_master_0"];

(* Theorem: Ring r ==> (master 1 = |0|) *)
(* Proof:
     master 1
   = X ** 1 - X     by notation
   = X - X          by poly_X, poly_exp_1
   = |0|            by poly_sub_eq
*)
val poly_master_1 = store_thm(
  "poly_master_1",
  ``!r:'a ring. Ring r ==> (master 1 = |0|)``,
  rw[]);

(* export simple result *)
val _ = export_rewrites ["poly_master_1"];

(* Theorem: Ring r /\ #1 <> #0 ==> !n. 0 < n ==> ((master n = |0|) <=> (n = 1)) *)
(* Proof:
   If part: (master n = |0|) ==> (n = 1)
       master n = |0|
   <=> X ** n - X = |0|        by notation
   <=>     X ** n = X          by poly_sub_eq_zero
   ==> deg (X ** n) = deg X    by poly_eq_deg_eq
                 n = 1         by poly_deg_X_exp, poly_deg_X, #1 <> #0
   Only-if part: master 1 = |0|
      True by poly_master_1
*)
val poly_master_eq_zero = store_thm(
  "poly_master_eq_zero",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. (master n = |0|) <=> (n = 1)``,
  rw_tac std_ss[EQ_IMP_THM] >-
  metis_tac[poly_deg_X_exp, poly_deg_X, poly_sub_eq_zero, poly_X, poly_exp_poly] >>
  rw[poly_master_1]);

(* Theorem: Ring r /\ #1 <> #0 ==> !n. 1 < n ==> (deg (master n) = n) *)
(* Proof:
   Since deg (X ** n) = n     by poly_deg_X_exp, #1 <> #0
     and deg X = 1            by poly_deg_X, #1 <> #0
     deg (master n)
   = deg (X ** n - X)         by notation
   = n                        by poly_deg_sub_less
*)
val poly_master_deg = store_thm(
  "poly_master_deg",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. 1 < n ==> (deg (master n) = n)``,
  rw[poly_deg_sub_less]);

(* export simple result *)
val _ = export_rewrites ["poly_master_deg"];

(* Theorem: Ring r ==> !n. 1 < n ==> (lead (master n) = #1)*)
(* Proof:
   If #1 = #0,
      Then |1| = |0|          by poly_one_eq_poly_zero
        so master n = |0|     by poly_one_eq_zero, poly_master_poly
       ==> lead (master n)
         = #0 = #1            by poly_lead_zero
   If #1 <> #0,
   Since deg (X ** n) = n     by poly_deg_X_exp, #1 <> #0
     and deg X = 1            by poly_deg_X, #1 <> #0
     lead (master n)
   = lead (X ** n - X)        by notation
   = lead (X ** n)            by poly_lead_sub_less
   = #1                       by poly_lead_X_exp
*)
val poly_master_lead = store_thm(
  "poly_master_lead",
  ``!r:'a ring. Ring r ==> !n. 1 < n ==> (lead (master n) = #1)``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >| [
    `master n = |0|` by metis_tac[poly_one_eq_poly_zero, poly_one_eq_zero, poly_master_poly] >>
    rw[],
    rw[poly_lead_sub_less]
  ]);

(* export simple result *)
val _ = export_rewrites ["poly_master_lead"];

(* Theorem: Ring r ==> !n. 1 < n ==> monic (master n) *)
(* Proof:
   Since monic (master n)       by poly_master_poly
     and lead (master n) = #1   by poly_master_lead
   Hence monic (master n)       by poly_monic_def
*)
val poly_master_monic = store_thm(
  "poly_master_monic",
  ``!r:'a ring. Ring r ==> !n. 1 < n ==> monic (master n)``,
  rw_tac std_ss[poly_master_poly, poly_master_lead, poly_monic_def]);

(* export simple result *)
val _ = export_rewrites ["poly_master_monic"];

(* Theorem: Ring r /\ #1 <> #0 ==> !n. 1 < n ==> pmonic (master n) *)
(* Proof:
   Since poly (master n)        by poly_master_poly
     and lead (master n) = #1   by poly_master_lead
     and deg (master n) = n     by poly_master_deg
    With 1 < n ==> 0 < n,
   Hence pmonic (master n)      by ring_unit_one
*)
val poly_master_pmonic = store_thm(
  "poly_master_pmonic",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. 1 < n ==> pmonic (master n)``,
  rw_tac std_ss[poly_master_poly, poly_master_lead, poly_master_deg,
               ring_unit_one, DECIDE``!n. 1 < n ==> 0 < n``]);

(* Theorem: Ring r /\ #1 <> #0 ==> !m n. (master m = master n) <=> (m = n) *)
(* Proof:
   Note poly X                          by poly_X
    ==> poly (X ** m) /\ poly (X ** n)  by poly_exp_poly
          master m = master n
    <=> X ** m - X = X ** n - X         by notation
    <=>     X ** m = X ** n             by poly_sub_rcancel
    <=>          m = n                  by poly_X_exp_eq
*)
val poly_master_eq = store_thm(
  "poly_master_eq",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !m n. (master m = master n) <=> (m = n)``,
  rpt strip_tac >>
  `poly X /\ poly (X ** m) /\ poly (X ** n)` by rw[] >>
  metis_tac[poly_X_exp_eq, poly_sub_rcancel]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Monic Factor.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r ==> !p. monic p ==> p <> |0| *)
(* Proof:
   By contradiction, if p = |0|,
   then monic |0| ==> #1 = #0         by poly_monic_zero
   But Field r ==> #1 <> #0           by field_one_ne_zero
   Hence a contradiction.
*)
val poly_field_monic_nonzero = store_thm(
  "poly_field_monic_nonzero",
  ``!r:'a field. Field r ==> !p. monic p ==> p <> |0|``,
  metis_tac[field_one_ne_zero, poly_monic_zero]);

(* Theorem: Field r /\ poly p ==> ?c q. c IN R /\ monic q /\ p = c * q *)
(* Proof:
   Let c = lead p.
   If p = |0|, c = #0            by poly_lead_zero
   Let q = |1|,
       then p = |0| = #0 * |1|   by poly_cmult_lzero
       and  monic |1|            by poly_monic_one
   If p <> |0|, c <> #0          by poly_lead_nonzero
   Let q = ( |/ c) * p
       then p = c * ( |/ c) * p  by poly_cmult_cmult, field_mult_rinv
       and monic q               by poly_lead_cmult
*)
val poly_field_make_monic = store_thm(
  "poly_field_make_monic",
  ``!r:'a field. Field r ==> !p. poly p ==> ?c q. c IN R /\ monic q /\ (p = c * q)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  Cases_on `p = |0|` >| [
    `lead p = #0` by rw[] >>
    `p = (lead p) * |1|` by rw[] >>
    `lead p IN R /\ monic |1|` by rw[] >>
    metis_tac[],
    `lead p <> #0` by rw[] >>
    `lead p IN R+` by rw[field_nonzero_eq] >>
    `|/ (lead p) IN R` by rw[field_inv_element] >>
    qabbrev_tac `q = ( |/ (lead p)) * p` >>
    `lead q = ( |/ (lead p)) * lead p` by rw[poly_lead_cmult, Abbr`q`] >>
    `_ = #1` by rw[field_mult_linv] >>
    `monic q` by rw[poly_monic_def, Abbr`q`] >>
    `(lead p) * q = (lead p) * ( |/ (lead p)) * p` by rw[poly_cmult_cmult, Abbr`q`] >>
    `_ = p` by rw[field_mult_rinv] >>
    `lead p IN R /\ poly q` by rw[Abbr`q`] >>
    metis_tac[]
  ]);

(* Theorem: Field r ==> !p. poly p /\ p <> |0| ==>
            ?c q. c IN R /\ c <> #0 /\ monic q /\ (deg q = deg p) /\ (p = c * q) *)
(* Proof:
   Let c = lead p
   Then c IN R              by poly_lead_element
    and c <> #0             by poly_lead_nonzero, p <> |0|
    and |/ c <> #0          by field_inv_nonzero, field_nonzero_eq
   and p = #1 * p           by poly_cmult_lone
         = (c * |/ c) * p   by field_mult_rinv
         = c * ( |/ c * p)  by poly_cmult_cmult
   Let q = |/ c * p
   Then lead q = |/ c * c   by poly_lead_cmult
               = #1         by field_mult_linv
   Since poly q             by poly_cmult_poly
   Hence monic q            by poly_monic_def
     and deg q = deg p      by poly_field_deg_cmult, |/ c <> #0.
*)
val poly_monic_cmult_factor = store_thm(
  "poly_monic_cmult_factor",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==>
   ?c q. c IN R /\ c <> #0 /\ monic q /\ (deg q = deg p) /\ (p = c * q)``,
  rpt strip_tac >>
  qexists_tac `lead p` >>
  `lead p IN R /\ lead p <> #0` by rw[] >>
  `lead p IN R+` by rw[field_nonzero_eq] >>
  `|/ (lead p) IN R+ /\ |/ (lead p) IN R` by rw[] >>
  `|/ (lead p) <> #0` by metis_tac[field_nonzero_eq] >>
  rw_tac std_ss[] >>
  qexists_tac `|/ (lead p) * p` >>
  rw[poly_monic_def, poly_cmult_cmult, poly_field_deg_cmult]);

(* Theorem: Field r ==> !p. poly p /\ p <> |0| ==>
            ?c q. c IN R /\ c <> #0 /\ monic q /\ (deg q = deg p) /\ (q = c * p) *)
(* Proof:
   Let c = |/ (lead p)
   Since lead p IN R           by poly_lead_element
    and lead p <> #0           by poly_lead_nonzero, p <> |0|
     so lead p IN R+           by field_nonzero_eq
    thus c IN R+               by field_inv_nonzero
     and c IN R                by field_inv_element
      or c <> #0               by field_nonzero_eq
   Let q = c * p
   Then lead q = c * (lead p)  by poly_lead_cmult
               = #1            by field_mult_linv
   Since poly q                by poly_cmult_poly
   Hence monic q               by poly_monic_def
     and deg q = deq p         by poly_field_deg_cmult, c <> #0.
*)
val poly_monic_cmult_by_factor = store_thm(
  "poly_monic_cmult_by_factor",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==>
   ?c q. c IN R /\ c <> #0 /\ monic q /\ (deg q = deg p) /\ (q = c * p)``,
  rpt strip_tac >>
  qexists_tac `|/ (lead p)` >>
  `lead p IN R /\ lead p <> #0` by rw[] >>
  `lead p IN R+` by rw[field_nonzero_eq] >>
  `|/ (lead p) IN R+ /\ |/ (lead p) IN R` by rw[] >>
  `|/ (lead p) <> #0` by metis_tac[field_nonzero_eq] >>
  rw_tac std_ss[poly_field_deg_cmult] >>
  rw[poly_monic_def]);

(* Theorem: Field r ==> !p. poly p /\ p <> |0| ==> monic ( |/ (lead p) * p) *)
(* Proof:
   Since lead p IN R                   by poly_lead_element
     and lead p <> #0                  by poly_lead_nonzero, p <> |0|
      so lead p IN R+                  by field_nonzero_eq
     and |/ (lead p) IN R              by field_inv_element
    Thus poly ( |/ (lead p) * p)       by poly_cmult_poly
    Also lead ( |/ (lead p) * p)
       = |/ (lead p) * lead p          by poly_lead_cmult
       = #1                            by field_mult_linv
    Hence monic ( |/ (lead p) * p)     by poly_monic_def
*)
val poly_monic_by_cmult = store_thm(
  "poly_monic_by_cmult",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==> monic ( |/ (lead p) * p)``,
  rpt strip_tac >>
  `lead p IN R /\ lead p <> #0` by rw[poly_lead_nonzero] >>
  `lead p IN R+ /\ |/ (lead p) IN R` by metis_tac[field_nonzero_eq, field_inv_element] >>
  `poly ( |/ (lead p) * p)` by rw[] >>
  `lead ( |/ (lead p) * p) = #1` by rw[] >>
  rw[poly_monic_def]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Remainder of Unity                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r /\ #1 <> #0 ==> !k. 0 < m ==> !(c:num). |c| % (unity m) = |c| *)
(* Proof:
   Let z = unity m.
   Then pmonic z            by poly_unity_pmonic, #1 <> #0, 0 < k
    and poly |c|            by poly_sum_num_poly
    and deg |c| = 0         by poly_deg_sum_num
    But deg z = m           by poly_unity_deg, #1 <> #0
     so deg |c| < deg z     by 0 < m
   Thus |c| % z = |c|       by poly_mod_less
*)
val poly_unity_mod_const = store_thm(
  "poly_unity_mod_const",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !m. 0 < m ==> !(c:num). |c| % (unity m) = |c|``,
  rpt strip_tac >>
  `pmonic (unity m)` by rw[poly_unity_pmonic] >>
  rw[poly_mod_less, poly_sum_num_poly, poly_deg_sum_num]);

(* Theorem: Ring r /\ #1 <> #0 ==> !m. 0 < m ==> ((X ** m) % (unity m) = |1|) *)
(* Proof:
   Let z = unity m.
   Then pmonic z                  by poly_unity_pmonic
        X ** m
      = unity m + |1|             by poly_sub_add
      = |1| * (unity m) + |1|     by poly_mult_lone
    Now deg |1| = 0               by poly_deg_one
    and deg (unity m) = m         by poly_unity_deg
     so deg |1| < deg (unity m)   by 0 < m
    Thus (X ** m) % z = |1|       by poly_mod_unique
*)
val poly_unity_mod_X_exp_deg = store_thm(
  "poly_unity_mod_X_exp_deg",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !m. 0 < m ==> ((X ** m) % (unity m) = |1|)``,
  rpt strip_tac >>
  `pmonic (unity m)` by rw[poly_unity_pmonic] >>
  `X ** m = unity m + |1|` by rw[poly_sub_add] >>
  `_ = |1| * (unity m) + |1|` by rw[] >>
  `poly (X ** m) /\ poly |1|` by rw[] >>
  `deg |1| < deg (unity m)` by rw[] >>
  metis_tac[poly_mod_unique]);

(* Theorem: Ring r /\ #1 <> #0 ==> !m. 0 < m ==> !n. (X ** n) % (unity m) = X ** (n MOD m) *)
(* Proof:
   Let a = n DIV m, b = n MOD m, z = unity m.
   Then n = a * m + b              by DIVISION, 0 < m
    and pmonic z                   by poly_unity_pmonic
     (X ** n) % z
   = (X ** (a * m + b)) % z        by above
   = (X ** (m * a + b)) % z        by MULT_COMM
   = (X ** (m * a) * X ** b) % z   by poly_exp_add
   = ((X ** m) ** a * X ** b) % z  by poly_exp_mult
   = (((X ** m) ** a) % z * (X ** b) % z) % z        by poly_mod_mult
   = (((X ** m % z) ** a) % z * (X ** b) % z) % z    by poly_mod_exp
   = (( |1| ** a) % z * (X ** b) % z) % z             by poly_unity_mod_X_exp_deg
   = ( |1| % z * (X ** b) % z) % z        by poly_one_exp
   = ( |1| * X ** b) % z                  by poly_mod_mult
   = (X ** b) % z                  by poly_mult_lone
   = X ** b                        by poly_mod_less, n MOD m < m
*)
val poly_unity_mod_X_exp_n = store_thm(
  "poly_unity_mod_X_exp_n",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !m. 0 < m ==> !n. (X ** n) % (unity m) = X ** (n MOD m)``,
  rpt strip_tac >>
  qabbrev_tac `a = n DIV m` >>
  qabbrev_tac `b = n MOD m` >>
  qabbrev_tac `z = unity m` >>
  `n = a * m + b` by rw[DIVISION, Abbr`a`, Abbr`b`] >>
  `n MOD m < m` by rw[MOD_LESS] >>
  `pmonic z` by rw[poly_unity_pmonic, Abbr`z`] >>
  `poly X /\ !k. poly (X ** k)` by rw[] >>
  `(deg z = m) /\ !k. deg (X ** k) = k` by rw[poly_unity_deg, Abbr`z`] >>
  `(X ** n) % z = (X ** (m * a + b)) % z` by rw_tac std_ss[MULT_COMM] >>
  `_ = (X ** (m * a) * X ** b) % z` by rw_tac std_ss[poly_exp_add] >>
  `_ = ((X ** m) ** a * X ** b) % z` by rw[poly_exp_mult] >>
  `_ = (((X ** m) ** a) % z * (X ** b) % z) % z` by rw_tac std_ss[poly_mod_mult, poly_exp_poly] >>
  `_ = (((X ** m % z) ** a) % z * (X ** b) % z) % z` by rw_tac std_ss[poly_mod_exp] >>
  `_ = (( |1| ** a) % z * (X ** b) % z) % z` by rw_tac std_ss[poly_unity_mod_X_exp_deg, Abbr`z`] >>
  `_ = ( |1| % z * (X ** b) % z) % z` by rw[poly_one_exp] >>
  `_ = ( |1| * X ** b) % z ` by rw[GSYM poly_mod_mult] >>
  `_ = (X ** b) % z` by rw[] >>
  `_ = X ** b` by rw[poly_mod_less, Abbr`b`] >>
  rw[]);

(* Theorem: Ring r /\ #1 <> #0 ==> !m. 0 < m ==>
            !n (c:num). ((X ** n) + |c|) % (unity m) = X ** (n MOD m) + |c| *)
(* Proof:
   Let z = unity m.
   Then pmonic z                                by poly_unity_pmonic, 0 < m
   Note poly |c|                                by poly_sum_num_poly
    and (X ** n) % z = X ** (n MOD m)           by poly_unity_mod_X_exp_n
    and |c| % z = |c|                           by poly_unity_mod_const
   Note deg (X ** (n MOD m) + |c|) = n MOD m    by poly_deg_X_exp_n_add_c
    and deg z = m                               by poly_unity_deg
   also n MOD m < m                             by MOD_LESS, 0 < m

       (X ** n + |c|) % z
     = (X ** (n MOD m) + |c|) % z    by poly_mod_add
     = X ** (n MOD m) + |c|          by poly_mod_less
*)
val poly_unity_mod_X_exp_n_add_c = store_thm(
  "poly_unity_mod_X_exp_n_add_c",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !m. 0 < m ==>
   !n (c:num). ((X ** n) + |c|) % (unity m) = X ** (n MOD m) + |c|``,
  rpt strip_tac >>
  qabbrev_tac `z = unity m` >>
  `pmonic z` by rw[poly_unity_pmonic, Abbr`z`] >>
  `poly (X ** n) /\ poly |c|` by rw[] >>
  `(X ** n) % z = X ** (n MOD m)` by rw[poly_unity_mod_X_exp_n, Abbr`z`] >>
  `|c| % z = |c|` by rw[poly_unity_mod_const, Abbr`z`] >>
  `n MOD m < m` by rw[MOD_LESS] >>
  `(X ** n + |c|) % z = (X ** (n MOD m) + |c|) % z` by metis_tac[poly_mod_add] >>
  rw[poly_mod_less, poly_deg_X_exp_n_add_c, poly_unity_deg, Abbr`z`]);

(* Theorem: Ring r /\ #1 <> #0 ==> !m c. 0 < m /\ c IN R ==> ((c * X ** m) % (unity m) = chop [c]) *)
(* Proof:
   Let z = unity m.
   Then pmonic z                  by poly_unity_pmonic, 0 < m
    and deg z = m                 by poly_unity_deg
   Note deg (c * |1|) = 0         by poly_deg_cmult, poly_deg_one
   Thus deg (c * |1|) < deg z     by 0 < m
   Note weak [c]                  by weak_const
     so poly (chop [c])           by poly_chop_weak_poly

      (c * X ** m) % z
    = (c * ((X ** m) % z)) % z    by poly_mod_cmult
    = (c * |1|) % z               by poly_unity_mod_X_exp_deg
    = c * |1|                     by poly_mod_less
    = [c] * |1|                   by poly_mult_lconst, poly_one_poly
    = (chop [c]) * |1|            by poly_mult_const
    = chop [c]                    by poly_mult_rone
*)
val poly_unity_mod_cmult_X_exp_deg = store_thm(
  "poly_unity_mod_cmult_X_exp_deg",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !m c. 0 < m /\ c IN R ==> ((c * X ** m) % (unity m) = chop [c])``,
  rpt strip_tac >>
  qabbrev_tac `z = unity m` >>
  `pmonic z` by rw[poly_unity_pmonic, Abbr`z`] >>
  `deg z = m` by rw[poly_unity_deg, Abbr`z`] >>
  `deg (c * |1|) = 0` by rw[] >>
  `(c * X ** m) % z = (c * ((X ** m) % z)) % z` by rw[poly_mod_cmult] >>
  `_ = (c * |1|) % z` by rw[poly_unity_mod_X_exp_deg, Abbr`z`] >>
  `_ = c * |1|` by rw[poly_mod_less] >>
  `_ = [c] * |1|` by rw[poly_mult_lconst] >>
  `_ = (chop [c]) * |1|` by rw[poly_mult_const] >>
  `_ = chop [c]` by rw[] >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* Useful Theorems                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r ==> !p q. poly p /\ poly q /\ deg p < deg q ==> (monic (p + q) <=> monic q) *)
(* Proof: by poly_monic_def, poly_lead_add_less *)
val poly_monic_add_less = store_thm(
  "poly_monic_add_less",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ deg p < deg q ==> (monic (p + q) <=> monic q)``,
  metis_tac[poly_monic_def, poly_lead_add_less, poly_add_poly]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q /\ deg q < deg p ==> (monic (p + q) <=> monic p) *)
(* Proof: by poly_monic_add_less, poly_add_comm *)
val poly_monic_add_less_comm = store_thm(
  "poly_monic_add_less_comm",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ deg q < deg p ==> (monic (p + q) <=> monic p)``,
  metis_tac[poly_monic_add_less, poly_add_comm]);

(* Theorem: Ring r ==> !p q. monic p /\ monic q /\ 0 < deg q /\ deg q <= deg p ==> monic (p / q) *)
(* Proof:
   Since monic q ==> pmonic q          by poly_monic_pmonic
      so poly (p / q) /\ poly (p % q) /\
         (p = p / q * q + p % q) /\ deg (p % q) < deg q   by poly_div_mod_def
    Also ~(deg p < deg q)              by deg q <= deg p
    thus p / q <> |0|                             by poly_div_eq_zero, ~(deg p < deg q)
       Now lead (p / q) <> #0                     by poly_lead_nonzero
        so deg (p / q * q) = deg (p / q) + deg q  by poly_deg_mult_unit_comm
        or deg (p % q) < deg (p / q * q)          by arithmetic
    Giving lead p = lead (p / q * q)              by poly_lead_add_less_comm
     hence monic (p / q * q)                      by poly_monic_def
       and monic (p / q)                          by poly_monic_monic_mult, poly_mult_comm
*)
val poly_monic_div_monic = store_thm(
  "poly_monic_div_monic",
  ``!r:'a ring. Ring r ==> !p q. monic p /\ monic q /\ 0 < deg q /\ deg q <= deg p ==> monic (p / q)``,
  rpt strip_tac >>
  `pmonic q` by rw[poly_monic_pmonic] >>
  `poly (p / q) /\ poly (p % q) /\ (p = p / q * q + p % q) /\ deg (p % q) < deg q` by rw[poly_div_mod_def] >>
  `~(deg p < deg q)` by decide_tac >>
  `p / q <> |0|` by rw[poly_div_eq_zero] >>
  `lead (p / q) <> #0 /\ poly (p / q * q)` by rw[] >>
  `deg (p / q * q) = deg (p / q) + deg q` by metis_tac[poly_deg_mult_unit_comm] >>
  `deg (p % q) < deg (p / q * q)` by decide_tac >>
  `lead p = lead (p / q * q)` by metis_tac[poly_lead_add_less_comm] >>
  `monic (p / q * q)` by metis_tac[poly_monic_def] >>
  metis_tac[poly_monic_monic_mult, poly_mult_comm]);

(* Theorem: Ring r ==> !p q. monic p /\ 0 < deg p /\ monic q /\ 0 < deg q /\
            deg q < deg p ==> monic (p / q) /\ 0 < deg (p / q) *)
(* Proof:
   For the first part: monic (p / q),
       this is given by poly_monic_div_monic.
   For the second part: 0 < deg (p / q),
       By contradiction, suppose deg (p / q) = 0.
       Since monic (p / q)          by poly_monic_div_monic
       This means p / q = |1|       by poly_monic_deg_0
       With pmonic q                by poly_monic_pmonic
         so p = p / q * q + p % q /\ deg (p % q) < deg q   by poly_div_mod_def
         or p = |1| * q + p % q     by above
              = q + p % q           by poly_mult_lone
       thus deg p = deg q           by poly_deg_add_less_comm
       which contradicts deg q < deg p.
*)
val poly_monic_nonconst_div_monic_nonconst = store_thm(
  "poly_monic_nonconst_div_monic_nonconst",
  ``!r:'a ring. Ring r ==> !p q. monic p /\ 0 < deg p /\ monic q /\ 0 < deg q /\
       deg q < deg p ==> monic (p / q) /\ 0 < deg (p / q)``,
  rpt strip_tac >-
  rw[poly_monic_div_monic, LESS_IMP_LESS_OR_EQ] >>
  spose_not_then strip_assume_tac >>
  `deg (p / q) = 0` by decide_tac >>
  `monic (p / q)` by rw[poly_monic_div_monic, LESS_IMP_LESS_OR_EQ] >>
  `p / q = |1|` by rw[GSYM poly_monic_deg_0] >>
  `pmonic q` by rw[poly_monic_pmonic] >>
  `poly (p % q) /\ (p = p / q * q + p % q) /\ deg (p % q) < deg q` by rw[poly_div_mod_def] >>
  `p = |1| * q + p % q` by metis_tac[] >>
  `_ = q + p % q` by rw[] >>
  `deg p = deg q` by metis_tac[poly_deg_add_less_comm] >>
  decide_tac);

(* Note:

This is as far as one can push with Ring polynomials.
Basically, for Ring, for q to be a divisor, it must be good: monic q, or pmonic, and 0 < deg q.
This is because, given any two polynomial p and q, there may be no way to "cancel the leading coefficient".
However, Field polynomials are better. Compare:
> poly_div_mod_eqn;
val it = |- !r. Ring r ==> !p q s t. poly p /\ poly q /\ unit (lead q) /\ poly s /\ poly t /\
            (p = s * q + t) /\ deg t < deg q ==> (p / q = s) /\ (p % q = t): thm
poly_field_div_mod_eqn  |- !r. Field r ==> !p q s t. poly p /\ poly q /\ poly s /\ poly t /\
            (p = s * q + t) /\ deg t < deg q ==> (p / q = s) /\ (p % q = t): thm
*)

(* Theorem: weak p ==> (p >> n) >> m = p >> (n + m) *)
(* Theorem: weak p ==> (p >> n) >> m = (p >> m) >> n *)
(* Nice to have above! *)
(* Maybe poly_coeff_def should be recursive:
     poly_coeff r [] n = #0
     poly_coeff r (h::t) 0 = h
     poly_coeff r (h::t) (SUC n) = poly_coeff r t n
*)


(* Theorem: Ring r /\ #1 <> #0 ==>
   !(p q):'a poly. weak p /\ weak q /\ 1 < LENGTH p /\ (LENGTH q <= LENGTH p) ==>
   !h. h IN R ==> (chop (h o p || q) = (h * p + q) % (unity (LENGTH p))) *)
(* Proof:
   Let k = LENGTH p, z = unity k.
   Note k <> 0, PRE k <> 0               by 1 < k

   Let t = h o p || q.
   Then LENGTH t = k                     by weak_cmult_add_length
   Thus t <> []                          by LENGTH_NIL
    and deg t = PRE k                    by poly_deg_def

   Note weak h o p                       by weak_cmult_weak
    and weak t                           by weak_add_weak
     so poly (chop t)                    by poly_chop_weak_poly
    and deg (chop t) <= deg t            by poly_deg_chop
    ==> deg (chop t) < k                 by PRE k < k, 0 < k

        chop t
      = chop (h o p || q)                by notation
      = chop (chop (h o p) || q)         by poly_chop_add
      = chop ((h * p) || q)              by poly_cmult_def
      = h * p + q                        by poly_add_def

   Note pmonic z                         by poly_unity_pmonic, 0 < k
    and deg z = k                        by poly_unity_deg
   Thus (h * p + q) % z = h * p + q      by poly_mod_less
*)
val poly_weak_cmult_add_chop = store_thm(
  "poly_weak_cmult_add_chop",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==>
   !(p q):'a poly. weak p /\ weak q /\ 1 < LENGTH p /\ (LENGTH q <= LENGTH p) ==>
   !h. h IN R ==> (chop (h o p || q) = (h * p + q) % (unity (LENGTH p)))``,
  rpt strip_tac >>
  qabbrev_tac `k = LENGTH p` >>
  qabbrev_tac `z = unity k` >>
  qabbrev_tac `t = h o p || q` >>
  `k <> 0` by decide_tac >>
  `LENGTH t = k` by rw[weak_cmult_add_length, Abbr`t`] >>
  `t <> []` by metis_tac[LENGTH_NIL] >>
  `deg t = PRE k` by rw[poly_deg_def, Abbr`k`] >>
  `weak t /\ weak (h o p)` by rw[Abbr`t`] >>
  `poly (chop t)` by rw[] >>
  `deg (chop t) <= deg t` by rw[poly_deg_chop] >>
  `deg (chop t) < k` by decide_tac >>
  `chop t = h * p + q` by metis_tac[poly_add_def, poly_cmult_def, poly_chop_add] >>
  `pmonic z` by rw[poly_unity_pmonic, Abbr`z`] >>
  `deg z = k` by rw[poly_unity_deg, Abbr`z`] >>
  metis_tac[poly_mod_less]);

(* Theorem: Ring r /\ #1 <> #0 ==>
            !p. weak p /\ 0 < LENGTH p ==> ((chop p) % (unity (LENGTH p)) = chop p) *)
(* Proof:
   Let k = LENGTH p, z = unity k.
   Then pmonic z                by poly_unity_pmonic, 0 < k
    and deg z = k               by poly_unity_deg
   Note deg p = PRE k           by poly_deg_def, p <> [] by 0 < k
    and deg (chop p) <= deg p   by poly_deg_chop
     so deg (chop p) < k        by PRE k < k for 0 < k
   Also poly (chop p)           by poly_chop_weak_poly
   Thus (chop p) % z = chop p   by poly_mod_less
*)
val poly_mod_less_weak = store_thm(
  "poly_mod_less_weak",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==>
   !p. weak p /\ 0 < LENGTH p ==> ((chop p) % (unity (LENGTH p)) = chop p)``,
  rpt strip_tac >>
  qabbrev_tac `k = LENGTH p` >>
  qabbrev_tac `z = unity k` >>
  `pmonic z` by rw[poly_unity_pmonic, Abbr`z`] >>
  `deg z = k` by rw[poly_unity_deg, Abbr`z`] >>
  `deg p = PRE k` by rw[poly_deg_def, Abbr`k`] >>
  `deg (chop p) <= deg p` by rw[poly_deg_chop] >>
  `deg (chop p) < k` by decide_tac >>
  `poly (chop p)` by rw[poly_chop_weak_poly] >>
  rw[poly_mod_less]);

(* ------------------------------------------------------------------------- *)
(* Weak Polynomials with X or polynomial addition.                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r /\ #1 <> #0 ==>
            !p. weak p /\ p <> |0| ==> (p = (FRONT p) || (LAST p) o (X ** PRE (LENGTH p))) *)
(* Proof:
   By induction on p.
   Base: [] <> [] ==> ([] = FRONT [] || LAST [] o (X ** PRE (LENGTH [])))
      True by [] <> [] = F.
   Step: p <> [] ==> (p = FRONT p || LAST p o (X ** PRE (LENGTH p))) ==>
        !h. h::p <> [] ==> (h::p = FRONT (h::p) || LAST (h::p) o (X ** PRE (LENGTH (h::p))))
      If p = [],
           FRONT (h::[]) || LAST (h::[]) o X ** PRE (LENGTH (h::[]))
         = [] || h o X ** PRE 1             by FRONT_DEF, LAST_DEF, LENGTH
         = h o X ** PRE 1                   by weak_add_of_lzero
         = h o X ** 0                       by PRE_SUB1
         = h o |1|                          by poly_exp_0
         = [h * #1]                         by weak_cmult_const
         = [h]                              by ring_mult_rone
      If p <> []
         Note LENGTH p <> 0                     by LENGTH_NIL
          and LENGTH p = SUC (PRE (LENGTH p))   by 0 < LENGTH p
        FRONT (h::p) || LAST (h::p) o (X ** PRE (LENGTH (h::p)))
      = (h::FRONT p) || (LAST p) o (X ** PRE (SUC (LENGTH p)))    by FRONT_DEF, LAST_DEF, LENGTH
      = (h::FRONT p) || (LAST p) o (X ** (LENGTH p))              by PRE
      = (h::FRONT p) || (LAST p) o (X ** SUC (PRE (LENGTH p)))    by above, 0 < LENGTH p
      = (h::FRONT p) || (LAST p) o (X ** (PRE (LENGTH p)) * X)    by poly_exp_suc
      = (h::FRONT p) || (LAST p) o (X ** (PRE (LENGTH p)) >> 1)   by poly_mult_X
      = (h::FRONT p) || (LAST p) o (#0 :: X ** (PRE (LENGTH p)))  by poly_shift_1, poly_X_exp_nonzero
      = (h::FRONT p) || ((LAST p) * #0 :: (LAST p) o X ** (PRE (LENGTH p))) by weak_cmult_cons
      = (h::FRONT p) || (#0 :: (LAST p) o X ** (PRE (LENGTH p)))   by ring_mult_rzero
      = (h + #0) :: (FRONT p)|| (LAST p) o X ** (PRE (LENGTH p))   by weak_add_cons
      = (h + #0) :: p                                              by induction hypothesis
      = h::p                                                       by ring_add_rzero
*)
val weak_split_front_last = store_thm(
  "weak_split_front_last",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==>
   !p. weak p /\ p <> |0| ==> (p = (FRONT p) || (LAST p) o (X ** PRE (LENGTH p)))``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[weak_cons] >>
  Cases_on `p = []` >-
  rw[FRONT_DEF, LAST_DEF, weak_cmult_const, poly_one] >>
  rw_tac std_ss[FRONT_DEF, LAST_DEF, LENGTH] >>
  `LENGTH p <> 0` by metis_tac[LENGTH_NIL] >>
  `LENGTH p = SUC (PRE (LENGTH p))` by decide_tac >>
  qabbrev_tac `n = PRE (LENGTH p)` >>
  `X ** SUC n = (X ** n) * X` by rw[poly_exp_suc] >>
  `_ = (X ** n) >> 1` by rw[poly_mult_X] >>
  `_ = #0 :: (X ** n)` by rw[poly_shift_1, poly_X_exp_nonzero] >>
  `(LAST p) IN R` by metis_tac[poly_lead_alt, poly_zero, weak_lead_element] >>
  `(h::FRONT p) || LAST p o (X ** LENGTH p) = (h::FRONT p) || LAST p o (#0 :: (X ** n))` by rw_tac std_ss[] >>
  `_ = (h::FRONT p) || (#0 :: (LAST p) o (X ** n))` by rw[weak_cmult_cons] >>
  `_ = (h + #0) :: (FRONT p) || (LAST p) o (X ** n)` by rw[weak_add_cons] >>
  `_ = h::p` by rw[] >>
  rw[]);
(* This is not in polyWeak, as X is involved. poly_X belongs to polyMonic. *)

(* Theorem: Ring r ==> !p c. weak p /\ c IN R /\ c <> #0 ==> (SNOC c p = p + [c] >> (LENGTH p)) *)
(* Proof:
   Note poly [c]              by poly_nonzero_element_poly
   By induction on p.
   Base: weak [] ==> (SNOC c [] = [] + [c] >> LENGTH [])
      LHS = SNOC c []
          = [c]               by SNOC_NIL
      RHS = [] + [c] >> LENGTH []
          = [] + [c] >> 0     by LENGTH_NIL
          = [] + [c]          by poly_shift_0
          = |0| + [c]         by poly_zero
          = [c] = LHS         by poly_add_lzero
   Step: weak p ==> (SNOC c p = p + [c] >> LENGTH p) ==>
         !h. weak (h::p) ==> (SNOC c (h::p) = (h::p) + [c] >> LENGTH (h::p))
      Note h IN R /\ weak p   by weak_cons
       and SNOC c p <> |0|    by NOT_SNOC_NIL
      Thus weak [h]                          by weak_const
       and SNOC c p = p + [c] >> LENGTH p    by induction hypothesis
      Thus poly (SNOC c p)                   by poly_add_weak_poly, poly_shift_poly, poly_add_poly
       and poly (h::SNOC c p)                by poly_nonzero_cons_poly, SNOC c p <> |0|
      Let pc = chop p, hc = chop [h].
      Then poly pc and poly hc               by poly_chop_weak_poly

           SNOC c (h::p)
         = h::SNOC c p                                 by SNOC_CONS
         = [h] + (SNOC c p) >> 1                       by poly_cons_eq_add_shift, poly (h::SNOC c p)
         = [h] + (p + [c] >> (LENGTH p)) >> 1          by induction hypothesis
         = [h] + (pc + [c] >> (LENGTH p)) >> 1         by poly_add_weak_right, poly_shift_weak
         = [h] + (pc >> 1 + ([c] >> (LENGTH p)) >> 1)  by poly_add_shift_1, poly pc
         = hc + (pc >> 1 + ([c] >> (LENGTH p)) >> 1)   by poly_add_weak_right
         = (hc + pc >> 1) + ([c] >> (LENGTH p)) >> 1   by poly_add_assoc, poly hc
         = (hc + chop (p >> 1)) + ([c] >> (LENGTH p)) >> 1   by poly_chop_shift
         = [h] + (p >> 1) + ([c] >> (LENGTH p)) >> 1         by poly_add_weak
         = chop ([h] ||(p >> 1)) + ([c] >> (LENGTH p)) >> 1  by poly_add_def
         = chop (h::p) + ([c] >> (LENGTH p)) >> 1            by weak_cons_eq_add_shift
         = (h::p) + ([c] >> (LENGTH p)) >> 1           by poly_add_weak_right, poly_shift_weak
         = (h::p) + [c] >> SUC (LENGTH p)              by poly_shift_SUC
         = (h::p) + [c] >> LENGTH (h::p)               by LENGTH
*)
val weak_snoc_eq_add_shift = store_thm(
  "weak_snoc_eq_add_shift",
  ``!r:'a ring. Ring r ==> !p c. weak p /\ c IN R /\ c <> #0 ==> (SNOC c p = p + [c] >> (LENGTH p))``,
  rpt strip_tac >>
  `poly [c]` by rw[poly_nonzero_element_poly] >>
  Induct_on `p` >-
  rw[] >>
  rpt strip_tac >>
  `h IN R /\ weak p` by metis_tac[weak_cons] >>
  `SNOC c p <> |0|` by rw[NOT_SNOC_NIL] >>
  `weak [h] /\ weak [c]` by rw[] >>
  `SNOC c p = p + [c] >> LENGTH p` by metis_tac[] >>
  `poly (SNOC c p)` by rw[poly_add_weak_poly] >>
  `poly (h::SNOC c p)` by rw[poly_nonzero_cons_poly] >>
  qabbrev_tac `pc = chop p` >>
  `poly pc` by rw[poly_chop_weak_poly, Abbr`pc`] >>
  qabbrev_tac `hc = chop [h]` >>
  `poly hc` by rw[poly_chop_weak_poly, Abbr`hc`] >>
  `weak (pc >> 1 + ([c] >> LENGTH p) >> 1) /\ weak (p >> 1)` by rw[] >>
  `SNOC c (h::p) = h::SNOC c p` by rw[] >>
  `_ = [h] + (SNOC c p) >> 1` by rw[poly_cons_eq_add_shift] >>
  `_ = [h] + (p + [c] >> (LENGTH p)) >> 1` by metis_tac[] >>
  `_ = [h] + (pc + [c] >> (LENGTH p)) >> 1` by rw_tac std_ss[poly_add_weak_right, poly_shift_weak, Abbr`pc`] >>
  `_ = [h] + (pc >> 1 + ([c] >> (LENGTH p)) >> 1)` by rw[poly_add_shift_1] >>
  `_ = hc + (pc >> 1 + ([c] >> (LENGTH p)) >> 1)` by rw_tac std_ss[poly_add_weak_right, Abbr`hc`] >>
  `_ = (hc + pc >> 1) + ([c] >> (LENGTH p)) >> 1` by rw[poly_add_assoc] >>
  `_ = (hc + chop (p >> 1)) + ([c] >> (LENGTH p)) >> 1` by rw[poly_chop_shift, Abbr`pc`] >>
  `_ = [h] + (p >> 1) + ([c] >> (LENGTH p)) >> 1` by rw_tac std_ss[poly_add_weak, Abbr`hc`] >>
  `_ = chop ([h] ||(p >> 1)) + ([c] >> (LENGTH p)) >> 1` by rw_tac std_ss[poly_add_def] >>
  `_ = chop (h::p) + ([c] >> (LENGTH p)) >> 1` by rw_tac std_ss[GSYM weak_cons_eq_add_shift] >>
  `_ = (h::p) + ([c] >> (LENGTH p)) >> 1` by rw_tac std_ss[poly_add_weak_right, poly_shift_weak] >>
  `_ = (h::p) + [c] >> SUC (LENGTH p)` by rw[] >>
  `_ = (h::p) + [c] >> LENGTH (h::p)` by rw[] >>
  metis_tac[]);
(* This is not in polyWeak, as polynomial addition is involved. *)

(* ------------------------------------------------------------------------- *)
(* Polynomials Coefficients                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: If p <> |0|, for 0 < k < n, (p >> n) ' k = #0 *)
(* Proof: by induction on n.
   Base case: k. k < 0 ==> ((p >> 0) ' k = #0)
     True since k < 0 is False.
   Step case: !k. k < n ==> ((p >> n) ' k = #0) ==> !k. k < SUC n ==> ((p >> SUC n) ' k = #0)
     p >> SUC n = #0::p >> n   by poly_shift_suc, p <> #0
     If k = 0,
       (#0::p >> n) ' 0 = #0   by poly_coeff_0_cons
     If k <> 0, PRE k exists
     and k < SUC n ==> PRE k < n.
       (#0::p >> n) ' k      with k < SUC n
     = (p >> n) '(PRE k)     with PRE k < n
     = #0                    by induction hypothesis
*)
val poly_coeff_shift_n = store_thm(
  "poly_coeff_shift_n",
  ``!r:'a ring. Ring r ==> !p. p <> |0| ==> !n k. k < n ==> ((p >> n) ' k = #0)``,
  ntac 4 strip_tac >>
  Induct >-
  rw[] >>
  rpt strip_tac >>
  (`p >> SUC n = #0::p >> n` by rw[]) >>
  Cases_on `k` >-
  rw[] >>
  `n' < n` by decide_tac >>
  (`deg (p >> n) = deg p + n` by rw_tac std_ss[poly_deg_shift]) >>
  (`deg (p >> SUC n) = deg p + SUC n` by rw_tac std_ss[poly_deg_shift]) >>
  (`~(deg (p >> SUC n) < SUC n') /\ ~(deg (p >> n) < n')` by decide_tac) >>
  (`(p >> SUC n) ' (SUC n') = EL (SUC n') (p >> SUC n)` by metis_tac [poly_coeff_def]) >>
  (`_ = EL n' (p >> n)` by rw[]) >>
  metis_tac [poly_coeff_def, poly_shift_eq_zero, list_CASES, poly_zero]);

(* Theorem: c IN R ==> for 0 < n, (p || [c]) ' n  = p ' n *)
(* Proof:
   If p = [],
      LHS = ([] || [c]) ' n
          = [c] ' n           by weak_add_of_lzero
          = #0                by poly_deg_const: deg [c] = 0
          = [] ' n = RHS      by poly_coeff_zero
   If p <> [], p = h::t
      If t = [], p = [h],
      LHS = ([h] || [c]) ' n
          = ([h + c]) ' n     by weak_add_cons
          = #0                by poly_deg_const
          = [h] ' n = RHS     by poly_deg_const
      If t <> [],
      note that 0 < n ==> n = SUC m  by num_CASES
      LHS = ((h::t) || [c]) ' n
          = (h + c :: t) ' n
          = if deg (h+c::t) < n then #0 else EL n (h+c::t)              by poly_coeff_def
          = if SUC (deg t) < (SUC m) then #0 else EL (SUC m) (h+c::t)   by poly_deg_cons
          = if SUC (deg t) < (SUC m) then #0 else EL m t                by EL
          = if deg (h::t) < n then #0 else EL n (h::t)                  by poly_deg_cons, EL
          = (h::t) ' n = RHS                                            by poly_coeff_def
*)
val poly_coeff_weak_add_const = store_thm(
  "poly_coeff_weak_add_const",
  ``!r:'a ring. Ring r ==> !p c. weak p /\ c IN R ==> !n. 0 < n ==> ((p || [c]) ' n = p ' n)``,
  rpt strip_tac >>
  `n <> 0` by decide_tac >>
  `?m. n = SUC m` by metis_tac [num_CASES] >>
  Cases_on `p` >>
  rw[]);

(* Note: poly_coeff_X_exp_n_add_c
|- !r. Ring r /\ #1 <> #0 ==> !n k c. 0 < k /\ k < n ==> ((X ** n + |c|) ' k = #0)
*)

(* Theorem: ##c <> #0 ==> for 0 < k < n, (X ** n + |c|) ' k = #0 *)
(* Proof:
   ##c <> #0 ==> #1 <> #0     by ring_num_all_zero
   and [#1] <> |0|            by poly_zero_eq_one, poly_one
   0 < k < n ==> 0 < n, or 0 <> n.
     ((X ** n + |c|)) ' k
   = ([##c] || [#1] >> n) ' k    by poly_X_exp_n_add_c
   = (([#1] >> n) || [##c]) ' k  by weak_add_comm
   = ([#1] >> n) ' k             by poly_coeff_weak_add_const, ring_num_element
   = #0                          by poly_coeff_shift_n, since [#1] <> |0|
*)
val poly_coeff_X_exp_n_add_c_alt = store_thm(
  "poly_coeff_X_exp_n_add_c_alt",
  ``!r:'a ring. Ring r ==> !c. ##c <> #0 ==> !n k. 0 < k /\ k < n ==> ((X ** n + |c|) ' k = #0)``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac [ring_num_all_zero] >>
  `[#1] <> |0|` by rw[] >>
  `0 < n /\ n <> 0` by decide_tac >>
  rw[poly_X_exp_n_add_c, weak_add_comm, poly_coeff_weak_add_const, poly_coeff_shift_n]);

(* Note: poly_coeff_X_exp_n_sub_c
|- !r. Ring r /\ #1 <> #0 ==> !n k c. 0 < k /\ k < n ==> ((X ** n - |c|) ' k = #0)
*)

(* Theorem: ##c <> #0 ==> for 0 < k < n, (X ** n - |c|) ' k = #0 *)
(* Proof:
   ##c <> #0 ==> #1 <> #0     by ring_num_all_zero
   and [#1] <> |0|            by poly_zero_eq_one, poly_one
   0 < k < n ==> 0 < n, or 0 <> n.
     ((X ** n - |c|)) ' k
   = ([- ##c] || [#1] >> n) ' k    by poly_X_exp_n_sub_c
   = (([#1] >> n) || [- ##c]) ' k  by weak_add_comm
   = ([#1] >> n) ' k               by poly_coeff_weak_add_const, ring_num_element
   = #0                            by poly_coeff_shift_n, since [#1] <> |0|
*)
val poly_coeff_X_exp_n_sub_c_alt = store_thm(
  "poly_coeff_X_exp_n_sub_c_alt",
  ``!r:'a ring. Ring r ==> !c. ##c <> #0 ==> !n k. 0 < k /\ k < n ==> ((X ** n - |c|) ' k = #0)``,
  rpt strip_tac >>
  `#1 <> #0` by metis_tac [ring_num_all_zero] >>
  `[#1] <> |0|` by rw[] >>
  `0 < n /\ n <> 0` by decide_tac >>
  rw[poly_X_exp_n_sub_c, weak_add_comm, poly_coeff_weak_add_const, poly_coeff_shift_n]);

(* Theorem: #1 <> #0 /\ k < SUC (deg p) ==> (p || X ** SUC (deg p)) ' k = p ' k *)
(* Proof:
   Since #1 <> #0, deg X = 1                    by poly_deg_X
   hence deg (X ** SUC (deg p)) = SUC (deg p)   by poly_monic_X, poly_monic_deg_exp

   If p = |0|, k < SUC (deg p) means k < 1, hence k = 0.
     (p || X ** SUC (deg p)) ' k
   = ([] || X ** 1) ' 0
   = (X ** 1) ' 0                by weak_add_of_lzero
   = X ' 0                       by poly_X, poly_exp_1
   = #0                          by X = [#0;#1]
   = [] ' 0                      by poly_coeff_zero
   If p <> |0|,
     (p || X ** SUC (deg p)) ' k
   = (p || [#1] >> SUC (deg p)) ' k    by poly_X_exp_n
   = (SNOC #1 p) ' k                   by weak_add_one_shift
   = EL k (SNOC #1 p)                  by poly_coeff_def
   = EL k p                            by SNOC
   = p ' k                             by poly_coeff_def
*)
val poly_coeff_weak_add_X_exp = store_thm(
  "poly_coeff_weak_add_X_exp",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p. weak p ==> !k. k < SUC (deg p) ==> ((p || X ** SUC (deg p)) ' k = p ' k)``,
  rpt strip_tac >>
  `[#1] <> |0|` by rw[] >>
  Cases_on `p = |0|` >| [
    `deg p = 0` by rw[] >>
    `k = 0` by decide_tac >>
    `X ** 1 = X` by rw[] >>
    rw_tac std_ss[poly_coeff_zero, poly_zero, weak_add_lzero] >>
    `X = [#0;#1]` by rw[] >>
    rw_tac std_ss[poly_coeff_0_cons],
    `p || X ** SUC (deg p) = p || [#1] >> SUC (deg p)` by rw[poly_X_exp_n] >>
    `_ = SNOC #1 p` by rw[weak_add_one_shift] >>
    `deg X = 1` by rw[poly_deg_X] >>
    `deg (X ** SUC (deg p)) = SUC (deg p)` by rw[poly_monic_X, poly_monic_deg_exp] >>
    `deg p < SUC (deg p)` by decide_tac >>
    `deg (p || X ** SUC (deg p)) = SUC (deg p)` by rw[poly_deg_weak_add, MAX_DEF] >>
    `~(deg (p || X ** SUC (deg p)) < k)` by decide_tac >>
    `SNOC #1 p <> []` by rw[] >>
    `SUC (deg p) = deg (h::p)` by rw[] >>
    `_ = LENGTH p` by rw[poly_deg_cons_length] >>
    `k < LENGTH p` by decide_tac >>
    `~(deg p < k)` by decide_tac >>
    `(p || X ** SUC (deg p)) ' k = EL k (SNOC #1 p)` by metis_tac[poly_coeff_def, list_CASES] >>
    `_ = EL k p` by rw[EL_SNOC] >>
    `_ = p ' k` by metis_tac[poly_coeff_def, list_CASES, poly_zero] >>
    rw[]
  ]);

(* Theorem: #1 <> #0 /\ c IN R /\ k < SUC (deg p) ==> (p || (c o (X ** SUC (deg p)))) ' k = p ' k *)
(* Proof:
   Since #1 <> #0, deg X = 1           by poly_deg_X
   hence deg (c o (X ** SUC (deg p)))
       = deg (X ** SUC (deg p))        by weak_deg_cmult
       = SUC (deg p)                   by poly_monic_X, poly_monic_deg_exp

   If p = |0|, k < SUC (deg p) means k < 1, hence k = 0.
     (p || c o (X ** SUC (deg p))) ' k
   = ([] || c o (X ** 1)) ' 0
   = (c o (X ** 1)) ' 0                by weak_add_of_lzero
   = (c o X) ' 0                       by poly_X, poly_exp_1
   = (c o [#0;#1]) ' 0                 by poly_X_def
   = [c * #0::c * #1] ' 0              by weak_cmult_cons
   = [#0; c] ' 0                       by ring_mult_rzero, ring_mult_rone
   = #0                                by poly_coeff_0_cons
   = [] ' 0                            by poly_coeff_zero
   If p <> |0|,
     (p || c o (X ** SUC (deg p))) ' k
   = (p || c o ([#1] >> SUC (deg p))) ' k    by poly_X_exp_n
   = (SNOC c p) ' k                          by weak_add_cmult_shift
   = EL k (SNOC (c o #1) p)                  by poly_coeff_def
   = EL k p                                  by EL_SNOC
   = p ' k                                   by poly_coeff_def
*)
val poly_coeff_weak_add_cmult_X_exp = store_thm(
  "poly_coeff_weak_add_cmult_X_exp",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c p. c IN R /\ weak p ==>
   !k. k < SUC (deg p) ==> ((p || c o (X ** SUC (deg p))) ' k = p ' k)``,
  rpt strip_tac >>
  `[#1] <> |0|` by rw[] >>
  Cases_on `p = |0|` >| [
    `deg p = 0` by rw[] >>
    `k = 0` by decide_tac >>
    `X ** 1 = X` by rw[] >>
    rw_tac std_ss[poly_coeff_zero, poly_zero, weak_add_lzero] >>
    `c o X = [#0;c * #1]` by rw[] >>
    rw_tac std_ss[poly_coeff_0_cons],
    `p || c o (X ** SUC (deg p)) = p || c o ([#1] >> SUC (deg p))` by rw[poly_X_exp_n] >>
    `_ = SNOC c p` by rw[weak_add_cmult_shift] >>
    `deg X = 1` by rw[poly_deg_X] >>
    `deg (c o (X ** SUC (deg p))) = deg (X ** SUC (deg p))` by rw[weak_deg_cmult] >>
    `_ = SUC (deg p)` by rw[poly_monic_X, poly_monic_deg_exp] >>
    `deg p < SUC (deg p)` by decide_tac >>
    `weak (c o (X ** SUC (deg p)))` by rw[] >>
    `deg (p || c o (X ** SUC (deg p))) = SUC (deg p)` by rw[poly_deg_weak_add, MAX_DEF] >>
    `~(deg (p || c o (X ** SUC (deg p))) < k)` by decide_tac >>
    `SNOC c p <> []` by rw[] >>
    `SUC (deg p) = deg (h::p)` by rw[] >>
    `_ = LENGTH p` by rw[poly_deg_cons_length] >>
    `k < LENGTH p` by decide_tac >>
    `~(deg p < k)` by decide_tac >>
    `(p || c o (X ** SUC (deg p))) ' k = EL k (SNOC c p)` by metis_tac[poly_coeff_def, list_CASES] >>
    `_ = EL k p` by rw[EL_SNOC] >>
    `_ = p ' k` by metis_tac[poly_coeff_def, list_CASES, poly_zero] >>
    rw[]
  ]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Turn                                                           *)
(* ------------------------------------------------------------------------- *)

(* Note: These are not in PolyWeak, as they dependes on weak_split_front_last. *)

(* Theorem: Ring r /\ #1 <> #0 ==>
            !p. weak p /\ 1 < LENGTH p ==> (chop (turn p) = (p * X) % (unity (LENGTH p))) *)
(* Proof:
   Let k = LENGTH p, z = unity k.
   Note k <> 0 and PRE k <> 0          by 1 < k
    and SUC (PRE k) = k                by 0 < k
     so p <> []                        by poly_zero, LENGTH_NIL

   Step 1: Estabish simple facts
     Note weak (FRONT p)                   by weak_front_last
      and (LAST p) IN R                    by weak_last_element
      and !n. weak ((LAST p) o (X ** n))   by weak_cmult_weak
     Also weak X                           by poly_X, poly_is_weak
       so weak ((FRONT p) o X)             by weak_mult_weak
      and weak [LAST p]                    by weak_const
     Thus poly ((FRONT p) * X)             by poly_mult_weak_poly
      and poly ((LAST p) * X ** k)         by poly_cmult_poly

   Step 2: Establish important facts
     Note (FRONT p) o X = (FRONT p) >> 1           by weak_mult_X_comm
      and pmonic z                                 by poly_unity_pmonic, 0 < k
      and deg z = k                                by poly_unity_deg
     Also (LAST p * X ** k) % z = chop [LAST p]    by poly_unity_mod_cmult_X_exp_deg [1]

     Claim: deg ((FRONT p) * X) <= PRE k
     Proof: Note LENGTH (FRONT p) = PRE k     by LENGTH_FRONT
              so FRONT p <> |0|               by LENGTH_NIL
            Also X <> |0|                     by poly_X_def
             and deg (FRONT p) = PRE (PRE k)  by poly_deg_def
             and deg X = 1                    by poly_deg_X
                 deg ((FRONT p) * X)
               = deg (chop ((FRONT p) o X))   by poly_mult_def
               <= deg ((FRONT p) o X)         by poly_deg_chop
                = PRE (PRE k) + 1             by poly_deg_weak_mult
                = PRE k                       by 1 < k

     Thus deg (FRONT p * X) < deg z           by PRE k < k = deg z
       or (FRONT p * X) % z = FRONT p * X     by poly_mod_less [2]

     Note poly (chop [LAST p])                by poly_const_poly
      and deg (chop [LAST p]) = 0             by poly_deg_chop, poly_deg_const
       so deg (FRONT p * X + chop [LAST p])
          <= MAX (deg (FRONT p * X)) 0        by poly_deg_add
     Note MAX (deg (FRONT p * X)) 0 < k       by MAX_LESS, deg (FRONT p * X) < k, 0 < k
      ==> deg (FRONT p * X + chop [LAST p]) < k
     Thus (FRONT p * X + chop [LAST p]) % z
        = FRONT p * X + chop [LAST p]         by poly_mod_less [3]

   Step 3: compute
           p o X
         = (FRONT p || LAST p o (X ** PRE k)) o X         by weak_split_front_last
         = (FRONT p) o X || (LAST p o (X ** PRE k)) o X   by weak_mult_ladd
         = (FRONT p) o X || LAST p o ((X ** PRE k) o X)   by weak_cmult_mult
         = (FRONT p) o X || LAST p o (X ** SUC (PRE k))   by weak_X_exp_suc
         = (FRONT p) o X || LAST p o (X ** k)             by SUC (PRE k) = k, 0 < k

           p * X
         = chop (p o X)                                              by poly_mult_def
         = chop ((FRONT p) o X || LAST p o (X ** k))                 by above
         = chop (chop ((FRONT p) o X) || chop (LAST p o (X ** k)))   by poly_chop_add_chop
         = chop (((FRONT p) * X) || chop (LAST p o (X ** k)))        by poly_mult_def
         = chop (((FRONT p) * X) || (LAST p * (X ** k)))             by poly_cmult_def
         = (FRONT p) * X + (LAST p) * X ** k                         by poly_add_def

           (p * X) % z
         = ((FRONT p * X) % z + (LAST p * X ** k) % z) % z      by poly_mod_add
         = (FRONT p * X + chop [LAST p]) % z              by above [1], [2]
         = FRONT p * X + chop [LAST p]                    by above [3]
         = chop (chop ((FRONT p) o X) || chop [LAST p])   by poly_mult_def, poly_add_def
         = chop (FRONT p o X || [LAST p])                 by poly_chop_add_chop
         = chop ([LAST p] || (FRONT p) >> 1)              by weak_add_comm
         = chop ((LAST p) :: FRONT p)                     by weak_cons_eq_add_shift, weak_cons
         = chop (turn p)                                  by turn_def
*)
val chop_turn_eqn = store_thm(
  "chop_turn_eqn",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p. weak p /\ 1 < LENGTH p ==>
         (chop (turn p) = (p * X) % (unity (LENGTH p)))``,
  rpt strip_tac >>
  qabbrev_tac `k = LENGTH p` >>
  qabbrev_tac `z = unity k` >>
  `k <> 0` by decide_tac >>
  `SUC (PRE k) = k` by decide_tac >>
  `p <> [] /\ p <> |0|` by metis_tac[poly_zero, LENGTH_NIL] >>
  `weak (FRONT p)` by rw[weak_front_last] >>
  `(LAST p) IN R` by rw[weak_last_element] >>
  `!n. weak ((LAST p) o (X ** n))` by rw[] >>
  `weak X` by rw[] >>
  `weak ((FRONT p) o X)` by rw[] >>
  `weak [LAST p]` by rw[] >>
  `poly ((FRONT p) * X)` by rw[poly_mult_weak_poly] >>
  `poly ((LAST p) * X ** k)` by rw[] >>
  `(FRONT p) o X = (FRONT p) >> 1` by rw_tac std_ss[weak_mult_X_comm] >>
  `pmonic z` by rw[poly_unity_pmonic, Abbr`z`] >>
  `(LAST p * X ** k) % z = chop [LAST p]` by rw[poly_unity_mod_cmult_X_exp_deg, Abbr`z`] >>
  `deg ((FRONT p) * X) <= PRE k` by
  (`PRE k <> 0 /\ (PRE (PRE k) + 1 = PRE k)` by decide_tac >>
  `LENGTH (FRONT p) = PRE k` by rw[LENGTH_FRONT, Abbr`k`] >>
  `FRONT p <> |0|` by metis_tac[LENGTH_NIL, poly_zero] >>
  `X <> |0|` by rw[] >>
  `deg (FRONT p) = PRE (PRE k)` by metis_tac[poly_deg_def, poly_zero] >>
  `deg X = 1` by rw[] >>
  `deg ((FRONT p) o X) = PRE k` by rw[poly_deg_weak_mult] >>
  metis_tac[poly_mult_def, poly_deg_chop]) >>
  `deg z = k` by rw[poly_unity_deg, Abbr`z`] >>
  `deg (FRONT p * X) < deg z` by decide_tac >>
  `(FRONT p * X) % z = FRONT p * X ` by rw[poly_mod_less] >>
  `poly (chop [LAST p])` by rw[] >>
  `deg (chop [LAST p]) = 0` by rw[] >>
  `deg (FRONT p * X + chop [LAST p]) <= MAX (deg (FRONT p * X)) 0` by metis_tac[poly_deg_add] >>
  `MAX (deg (FRONT p * X)) 0 < k` by metis_tac[MAX_LESS, NOT_ZERO_LT_ZERO] >>
  `deg (FRONT p * X + chop [LAST p]) < k` by decide_tac >>
  `(FRONT p * X + chop [LAST p]) % z = FRONT p * X + chop [LAST p]` by rw[poly_mod_less] >>
  `p o X = (FRONT p || LAST p o (X ** PRE k)) o X` by rw_tac std_ss[GSYM weak_split_front_last, Abbr`k`] >>
  `_ = (FRONT p) o X || (LAST p o (X ** PRE k)) o X` by rw[weak_mult_ladd] >>
  `_ = (FRONT p) o X || LAST p o ((X ** PRE k) o X)` by rw[weak_cmult_mult] >>
  `_ = (FRONT p) o X || LAST p o (X ** SUC (PRE k))` by rw[weak_X_exp_suc] >>
  `_ = (FRONT p) o X || LAST p o (X ** k)` by metis_tac[] >>
  `p * X = chop (p o X)` by rw[GSYM poly_mult_def] >>
  `_ = chop ((FRONT p) o X || LAST p o (X ** k))` by metis_tac[] >>
  `_ = chop (chop ((FRONT p) o X) || chop (LAST p o (X ** k)))` by rw_tac std_ss[poly_chop_add_chop] >>
  `_ = (FRONT p) * X + (LAST p) * X ** k` by metis_tac[poly_add_def, poly_mult_def, poly_cmult_def] >>
  `(p * X) % z = ((FRONT p * X) % z + (LAST p * X ** k) % z) % z` by rw_tac std_ss[GSYM poly_mod_add] >>
  `_ = FRONT p * X + chop [LAST p]` by rw_tac std_ss[] >>
  `_ = chop (chop ((FRONT p) o X) || chop [LAST p])` by metis_tac[poly_mult_def, poly_add_def] >>
  `_ = chop (FRONT p o X || [LAST p])` by rw_tac std_ss[poly_chop_add_chop] >>
  `_ = chop ([LAST p] || (FRONT p) >> 1)` by rw_tac std_ss[weak_add_comm] >>
  `_ = chop ((LAST p) :: FRONT p)` by metis_tac[weak_cons_eq_add_shift, weak_cons] >>
  `_ = chop (turn p)` by rw[turn_def] >>
  rw[]);

(* This is the first milestone theorem! *)

(* Theorem: Ring r /\ #1 <> #0 ==> !p. weak p /\ 1 < LENGTH p ==>
            !n. chop (turn_exp p n) = (p * X ** n) % unity (LENGTH p) *)
(* Proof:
   Let k = LENGTH p, z = unity k.
   Note pmonic z                  by poly_unity_pmonic
    and deg z = k                 by poly_unity_deg
   Also p <> []                   by LENGTH_NIL, k <> 0
    and deg p = PRE k < k         by poly_deg_def, 0 < k
   The goal is: !n. chop (turn_exp p n) = (p * X ** n) % z
   By induction on n.
   Base: chop (turn_exp p 0) = (p * X ** 0) % z
       Note poly (chop p)         by poly_chop_weak_poly
        and deg (chop p) <= deg p by poly_deg_chop
         chop (turn_exp p 0)
       = chop p                   by turn_exp_0
       = p * |1|                  by poly_chop_weak_alt
       = p * X ** 0               by poly_exp_0
       = (p * X ** 0) % z         by poly_mod_less
   Step: chop (turn_exp p n) = (p * X ** n) % z ==>
         chop (turn_exp p (SUC n)) = (p * X ** SUC n) % z
      Note weak (turn_exp p (SUC n))         by weak_turn_exp
       and weak (turn_exp p n)               by weak_turn_exp
       and LENGTH (turn_exp p n) = k         by turn_exp_length
        chop (turn_exp p (SUC n))
      = chop (turn (turn_exp p n))           by turn_exp_suc
      = ((turn_exp p n) * X) % z             by chop_turn_eqn
      = chop ((turn_exp p n) o X) % z        by poly_mult_def
      = chop (chop (turn_exp p n) o X) % z   by poly_chop_mult
      = chop (((p * X ** n) % z) o X) % z    by induction hypothesis
      = ((p * X ** n) % z * X) % z           by poly_mult_def
      = ((p * X ** n) % z * X % z) % z       by poly_mod_less, poly_deg_X
      = (p * X ** n * X) % z                 by poly_mod_mult
      = (p * (X ** n * X)) % z               by poly_mult_weak_assoc
      = (p * X ** (SUC n)) % z               by poly_exp_suc
*)
val chop_turn_exp_eqn = store_thm(
  "chop_turn_exp_eqn",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p. weak p /\ 1 < LENGTH p ==>
   !n. chop (turn_exp p n) = (p * X ** n) % unity (LENGTH p)``,
  ntac 4 strip_tac >>
  qabbrev_tac `k = LENGTH p` >>
  qabbrev_tac `z = unity k` >>
  `pmonic z` by rw[poly_unity_pmonic, Abbr`z`] >>
  `deg z = k` by rw[poly_unity_deg, Abbr`z`] >>
  Induct >| [
    rewrite_tac[turn_exp_0, poly_exp_0, poly_X] >>
    `chop p = p * |1|` by rw[poly_chop_weak_alt] >>
    `k <> 0` by decide_tac >>
    `p <> []` by metis_tac[LENGTH_NIL] >>
    `deg p = PRE k` by rw[poly_deg_def] >>
    `deg (chop p) <= deg p` by rw[poly_deg_chop] >>
    `deg (chop p) < k` by decide_tac >>
    metis_tac[poly_mod_less, poly_chop_weak_poly],
    `weak (turn_exp p (SUC n)) /\ weak (turn_exp p n)` by rw[weak_turn_exp] >>
    `LENGTH (turn_exp p n) = k` by rw[turn_exp_length] >>
    `chop (turn_exp p (SUC n)) = chop (turn (turn_exp p n))` by rw[turn_exp_suc] >>
    `_ = ((turn_exp p n) * X) % z` by rw[chop_turn_eqn] >>
    `_ = chop ((turn_exp p n) o X) % z` by rw[GSYM poly_mult_def] >>
    `_ = chop (chop (turn_exp p n) o X) % z` by rw[poly_chop_mult] >>
    `_ = chop (((p * X ** n) % z) o X) % z` by rw_tac std_ss[] >>
    `_ = ((p * X ** n) % z * X) % z` by rw[GSYM poly_mult_def] >>
    `_ = ((p * X ** n) % z * X % z) % z` by rw_tac std_ss[poly_mod_less, poly_X, poly_deg_X] >>
    `_ = (p * X ** n * X) % z` by prove_tac[poly_mod_mult, poly_mult_weak_poly, poly_X, poly_exp_poly, poly_is_weak] >>
    `_ = (p * (X ** n * X)) % z` by rw[poly_mult_weak_assoc] >>
    `_ = (p * X ** (SUC n)) % z` by rw[poly_exp_suc] >>
    rw[]
  ]);

(* This is the second milestone theorem! *)


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
