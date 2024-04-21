(* ------------------------------------------------------------------------- *)
(* Weak Polynomial with coefficients from a Ring/Field                       *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polyWeak";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pairTheory bagTheory pred_setTheory listTheory arithmeticTheory
     numberTheory rich_listTheory combinatoricsTheory;

open monoidTheory groupTheory ringTheory polynomialTheory;

(* Overload sublist by infix operator *)
val _ = temp_overload_on ("<=", ``sublist``);

(* ------------------------------------------------------------------------- *)
(* Weak Polynomials Documentation                                            *)
(* ------------------------------------------------------------------------- *)
(* Data type:
   A polynomial is just a list of coefficients from a Ring r.
   A polynomial is "weak" if it can have leading zeroes, i.e. not normalized.

   Overloads:
   weak  = Weak r
   ||    = weak_add r
   o     = weak_cmult r
   o     = weak_mult r
   >>    = poly_shift r
   neg   = weak_neg r
   zerop = zero_poly r
   chop  = poly_chop r
   deg   = poly_degree r
   eval  = poly_eval r
   root  = poly_root r
   roots = poly_roots r
*)
(* Definitions and Theorems (# are exported):

   Weak Polynomials over a Ring:
   weak_of_zero       |- !r. weak [] <=> T
   weak_cons          |- !r h t. weak (h::t) <=> h IN R /\ weak t
#  weak_zero          |- !r. weak |0| <=> T
   weak_def_alt       |- !r p. weak p <=> EVERY (\x. x IN R) p
   weak_append_weak   |- !r p q. weak (p ++ q) <=> weak p /\ weak q
   weak_snoc          |- !r h t. weak (SNOC h t) <=> h IN R /\ weak t
   weak_every_element |- !r p. weak p <=> EVERY (\c. c IN R) p
   weak_every_mem     |- !r p. weak p <=> !x. MEM x p ==> x IN R
   weak_last_element  |- !p. weak p /\ p <> |0| ==> LAST p IN R
   weak_front_last    |- !p. weak p /\ p <> |0| ==> weak (FRONT p) /\ weak [LAST p]
   weak_sublist       |- !r p q. weak p ==> !q. q <= p ==> weak q
   weak_take          |- !r p n. weak p ==> weak (TAKE n p)
   weak_drop          |- !r p n. weak p ==> weak (DROP n p)
   weak_front         |- !r p. weak p /\ p <> |0| ==> weak (FRONT p)
   weak_tail          |- !r p. weak p /\ p <> |0| ==> weak (TL p)

   Zero Polynomials (for normalization):
   zero_poly_of_zero       |- !r. zerop [] <=> T
   zero_poly_cons          |- !r h t. zerop (h::t) <=> (h = #0) /\ zerop t
#  zero_poly_zero          |- !r. zerop |0| <=> T
   zero_poly_every_zero    |- !p. zerop p <=> EVERY (\c. c = #0) p
   zero_poly_every_element |- !r. Ring r ==> !p. zerop p ==> EVERY (\c. c IN R) p
   zero_poly_snoc          |- !r p. zerop (SNOC #0 p) <=> zerop p
   zero_poly_weak          |- !r. Ring r ==> !p. zerop p ==> weak p
   weak_all_zero_poly      |- !r. Ring r ==> (( |1| = |0|) <=> !p. weak p ==> zerop p)
#  zero_poly_element_zero  |- zerop [#0]
   zero_poly_cons_zero     |- !p. zerop p ==> zerop (#0::p)
   zero_poly_last_zero     |- !h t. zerop (h::t) ==> (LAST (h::t) = #0)
   zero_poly_element       |- !p. zerop p <=> !k. k < LENGTH p ==> (EL k p = #0)
   zero_poly_eq_zero_poly  |- !r p q. zerop p /\ zerop q ==> ((LENGTH p = LENGTH q) <=> (p = q))
   zero_poly_genlist_zero  |- !r n. zerop (GENLIST (K #0) n)

   Weal Polynomial Pair Addition:
#  weak_add_of_zero_zero |- [] || [] = []
#  weak_add_of_lzero     |- !p. [] || p = p
#  weak_add_of_rzero     |- !p. p || [] = p
#  weak_add_zero_zero |- |0| || |0| = |0|
#  weak_add_lzero     |- !p. |0| || p = p
#  weak_add_rzero     |- !p. p || |0| = p
   weak_add_nil       |- !r p. (p || [] = p) /\ ([] || p = p)
   weak_add_of_zero   |- !r p. (p || [] = p) /\ ([] || p = p)
   weak_add_zero      |- !r p. (p || |0| = p) /\ ( |0| || p = p)
#  weak_add_cons      |- !r qt qh pt ph. (ph::pt) || (qh::qt) = ph + qh::pt || qt
   weak_add_length    |- !r p q. LENGTH (p || q) = MAX (LENGTH p) (LENGTH q)
   weak_add_eq_of_zero|- !r p q. ((p || q = []) <=> (p = []) /\ (q = []))
   weak_add_eq_zero   |- !r p q. ((p || q = |0|) <=> (p = |0|) /\ (q = |0|))
   zero_weak_add_zero |- !r. Ring r ==> !p q. zerop p /\ zerop q ==> zerop (p || q)
#  weak_add_weak      |- !r. Ring r ==> !p q. weak p /\ weak q ==> weak (p || q)
   weak_add_comm      |- !r. Ring r ==> !p q. weak p /\ weak q ==> (p || q = q || p)
   weak_add_assoc     |- !r. Ring r ==> !p q t. weak p /\ weak q /\ weak t ==> (p || q || t = p || (q || t))
   weak_add_clauses   |- !r. Ring r ==> !p q t. weak p /\ weak q /\ weak t ==>
                         ([] || p = p) /\ (p || [] = p) /\ (p || q = q || p) /\ (p || q || t = p || (q || t))
   weak_add_lzero_poly   |- !r. Ring r ==> !p q. zerop p /\ weak q /\ LENGTH p <= LENGTH q ==> (p || q = q)
   weak_add_rzero_poly   |- !r. Ring r ==> !p q. zerop p /\ weak q /\ LENGTH p <= LENGTH q ==> (q || p = q)
   weak_add_map2      |- !r p q. weak p /\ weak q /\ (LENGTH p = LENGTH q) ==> (p || q = MAP2 (\x y. x + y) p q)
   weak_add_element   |- !r p q j. j < LENGTH p /\ j < LENGTH q ==> (EL j (p || q) = EL j p + EL j q)
   weak_add_last      |- !r p q. p <> |0| /\ q <> |0| /\ (LENGTH p = LENGTH q) ==> LAST (p || q) = LAST p + LAST q
   weak_add_front     |- !r p q. p <> |0| /\ q <> |0| /\ (LENGTH p = LENGTH q) ==> FRONT (p || q) = FRONT p || FRONT q

   Weak Polynomial Scalar Multiplication:
   weak_cmult_of_zero  |- !r c. c o [] = []
   weak_cmult_cons     |- !r c h t. c o (h::t) = c * h::c o t
   weak_cmult_clauses  |- !r c. (c o [] = []) /\ !h t. c o (h::t) = c * h::c o t
   weak_cmult_zero     |- !r c. c o |0| = |0|
   weak_cmult_map         |- !r c p. c o p = MAP (\x. c * x) p
   weak_cmult_length      |- !r c p. LENGTH (c o p) = LENGTH p
   weak_cmult_eq_of_zero  |- !r c p. (c o p = []) <=> (p = [])
   weak_cmult_eq_zero     |- !r c p. (c o p = |0|) <=> (p = |0|)
   weak_cmult_add_length  |- !r h p q. LENGTH q <= LENGTH p ==> (LENGTH (h o p || q) = LENGTH p)
   weak_cmult_snoc        |- !r c h t. c o SNOC h t = SNOC (c * h) (c o t)
   weak_cmult_front_last  |- !r c p. p <> |0| ==>
                                        (c o FRONT p = FRONT (c o p)) /\ (c * LAST p = LAST (c o p))

   weak_cmult_element  |- !r c p j. j < LENGTH p ==> (EL j (c o p) = c * EL j p)
   weak_cmult_last     |- !r c p. p <> |0| ==> (LAST (c o p) = c * LAST p)
   weak_cmult_front    |- !r c p. p <> |0| ==> (FRONT (c o p) = c o FRONT p)
#  weak_cmult_weak     |- !r. Ring r ==> !p. weak p ==> !c. c IN R ==> weak (c o p)
   weak_cmult_add      |- !r. Ring r ==> !p q. weak p /\ weak q ==> !c. c IN R ==> (c o (p || q) = c o p || c o q)
   weak_add_cmult         |- !r. Ring r ==> !p. weak p ==> !b c. b IN R /\ c IN R ==> ((b + c) o p = b o p || c o p)
   weak_cmult_cmult       |- !r. Ring r ==> !p. weak p ==> !b c. b IN R /\ c IN R ==> (b o c o p = (b * c) o p)
   weak_cmult_cmult_comm  |- !r. Ring r ==> !p. weak p ==> !b c. b IN R /\ c IN R ==> (b o c o p = c o b o p)

   Polynomial Negation:
   weak_neg_of_zero    |- !r. neg [] = []
   weak_neg_cons       |- !r h t. neg (h::t) = -h::neg t
   weak_neg_clauses    |- !r. (neg [] = []) /\ !h t. neg (h::t) = -h::neg t
#  weak_neg_zero       |- !r. neg |0| = |0|
   weak_neg_map        |- !r p. neg p = MAP (\x. -x) p
   weak_neg_length     |- !r p. LENGTH (neg p) = LENGTH p
   weak_neg_eq_of_zero |- !r p. (neg p = []) <=> (p = [])
   weak_neg_eq_zero    |- !r p. (neg p = |0|) <=> (p = |0|)
#  weak_neg_neg        |- !r. Ring r ==> !p. weak p ==> (neg (neg p) = p)
#  weak_neg_weak       |- !r. Ring r ==> !p. weak p ==> weak (neg p)
#  weak_cmult_neg      |- !r. Ring r ==> !p. weak p ==> !c. c IN R ==> (c o neg p = -c o p)
#  weak_neg_cmult      |- !r. Ring r ==> !p. weak p ==> !c. c IN R ==> (neg (c o p) = -c o p)
   weak_neg_element    |- !r p j. j < LENGTH p ==> (EL j (neg p) = -EL j p)
   weak_neg_last       |- !r p. p <> |0| ==> (LAST (neg p) = -LAST p)
   weak_neg_front      |- !r p. p <> |0| ==> (FRONT (neg p) = neg (FRONT p))

   Polynomial Turn:
   turn_eq_of_zero       |- !p. (turn p = []) <=> (p = [])
   turn_eq_zero          |- !p. (turn p = |0|) <=> (p = |0|)
   weak_turn             |- !r p. weak p ==> weak (turn p)
   weak_turn_exp         |- !r p. weak p ==> !n. weak (turn_exp p n)
   weak_add_turn         |- !r p q. (LENGTH p = LENGTH q) ==> (turn (p || q) = turn p || turn q)
   weak_cmult_turn       |- !r c p. turn (c o p) = c o turn p
   weak_cmult_turn_exp   |- !r p c n. c o turn_exp p n = turn_exp (c o p) n

   Polynomial Shifts:
#  poly_shift_0           |- !p. p >> 0 = p
#  poly_shift_suc         |- !p n. p >> SUC n = if p = |0| then |0| else #0::p >> n
#  poly_shift_of_zero     |- !n. [] >> n = []
#  poly_shift_zero        |- !n. |0| >> n = |0|
   poly_shift_eq_of_zero  |- !p n. (p >> n = []) <=> (p = [])
   poly_shift_eq_zero     |- !p n. (p >> n = |0|) <=> (p = |0|)
#  poly_shift_weak        |- !r. Ring r ==> !p. weak p ==> !n. weak (p >> n)
   poly_shift_last        |- !p. p <> |0| ==> !n. LAST (p >> n) = LAST p
   poly_shift_length      |- !p. p <> |0| ==> !n. LENGTH (p >> n) = LENGTH p + n
   poly_shift_nonzero     |- !r p. p <> |0| ==> !n. p >> n = PAD_LEFT #0 (n + LENGTH p) p
   poly_shift_const       |- !r c n. [c] >> n = PAD_LEFT #0 (SUC n) [c]

   Polynomial Shift Theorems:
   poly_shift_1       |- !p. p >> 1 = if p = |0| then |0| else #0::p
   poly_shift_1_cons  |- !h t. (h::t) >> 1 = #0::h::t
#  poly_shift_cons    |- !h t. ((h::t) >> 0 = h::t) /\ !n. (h::t) >> SUC n = ((h::t) >> n) >> 1
   poly_shift_SUC     |- !p n. p >> SUC n = (p >> n) >> 1
   weak_cons_eq_add_shift  |- !r. Ring r ==> !h t. weak (h::t) ==> (h::t = [h] || t >> 1)
   weak_neg_shift     |- !r. Ring r ==> !p n. neg p >> n = neg (p >> n)

   weak_add_shift_1   |- !r. Ring r ==> !p q. (p || q) >> 1 = p >> 1 || q >> 1
   weak_add_shift     |- !r. Ring r ==> !p q n. (p || q) >> n = p >> n || q >> n
   weak_cmult_shift_1 |- !r. Ring r ==> !p c. c IN R ==> (c o p >> 1 = c o (p >> 1))
   weak_cmult_shift   |- !r. Ring r ==> !p c. c IN R ==> !n. c o p >> n = c o (p >> n)

   Weak Polynomial Multiplication:
#  weak_mult_of_lzero |- !r q. [] o q = []
#  weak_mult_cons     |- !r h t q. (h::t) o q = h o q || t o q >> 1
#  weak_mult_of_rzero |- !p. p o [] = []
   weak_mult_of_zero  |- !r p. (p o [] = []) /\ ([] o p = [])
   weak_mult_lzero    |- !r q. |0| o q = |0|
   weak_mult_rzero    |- !p. p o |0| = |0|
   weak_mult_zero     |- !r p. (p o |0| = |0|) /\ ( |0| o p = |0|)
   weak_mult_eq_of_zero  |- !r p q. (p o q = []) <=> (p = []) \/ (q = [])
   weak_mult_eq_zero     |- !r p q. (p o q = |0|) <=> (p = |0|) \/ (q = |0|)
#  weak_mult_weak     |- !r. Ring r ==> !p q. weak p /\ weak q ==> weak (p o q)

   Theorems on polynomial multiplication with scalar multiplication:
   weak_cmult_mult    |- !r. Ring r ==> !p q. weak p /\ weak q ==> !c. c IN R ==> ((c o p) o q = c o p o q)

   Polynomial Negation with Addition:
#  weak_add_lneg     |- !r. Ring r ==> !p. weak p ==> zerop (neg p || p)
#  weak_add_rneg     |- !r. Ring r ==> !p. weak p ==> zerop (p || neg p)
#  zero_poly_cmult   |- !r. Ring r ==> !p. zerop p ==> !c. c IN R ==> zerop (c o p)
   weak_cmult_lzero  |- !r. Ring r ==> !p. weak p ==> zerop (#0 o p)
   zero_weak_neg     |- !r. Ring r ==> !p. weak p ==> (zerop p <=> zerop (neg p))
   zero_poly_shift   |- !p n. zerop (p >> n) <=> zerop p

   Polynomial Multiplication:
   zero_weak_lmult   |- !r. Ring r ==> !p q. zerop p /\ weak q ==> zerop (p o q)
   zero_weak_rmult   |- !r. Ring r ==> !p q. weak p /\ zerop q ==> zerop (p o q)
   weak_mult_shift_1 |- !r. Ring r ==> !p q. weak p /\ weak q ==> (p o q >> 1 = p o (q >> 1))

   Constant Polynomials:
#  weak_const                   |- !r k. k IN R ==> weak [k]
   weak_cmult_const             |- !r h k. h o [k] = [h * k]
   weak_cmult_const_comm        |- !r. Ring r ==> !h k. h IN R /\ k IN R ==> (h o [k] = k o [h])
   weak_mult_const              |- !r p k. k IN R ==> ([k] o p = k o p)
   weak_mult_const_const        |- !r h k. h IN R /\ k IN R ==> ([h] o [k] = h o [k])
   weak_mult_const_const_comm   |- !r. Ring r ==> !h k. h IN R /\ k IN R ==> ([h] o [k] = [k] o [h])
   weak_mult_const_cons         |- !r. Ring r ==> !p h k.  k IN R /\ weak (h::p) ==> ([k] o (h::p) = h o [k] || [k] o p >> 1)
   weak_cmult_cons_eq_add_shift |- !r. Ring r ==> !p h k. k IN R /\ weak (h::p) ==> (k o (h::p) = [k * h] || k o p >> 1)
   weak_mult_const_comm         |- !r. Ring r ==> !p k. k IN R /\ weak p ==> (p o [k] = k o p)
   weak_mult_cons_const         |- !r. Ring r ==> !p h k. k IN R /\ weak (h::p) ==> ((h::p) o [k] = k o (h::p))
   weak_mult_cons_comm          |- !r. Ring r ==> !p q h. h IN R /\ weak p /\ weak (h::q) ==> (p o (h::q) = h o p || p o q >> 1)
   weak_mult_cross              |- !r. Ring r ==> !h k p q. weak (h::p) /\ weak (k::q) ==>
                                                  ((h::p) o (k::q) = [h * k] || h o q >> 1 || k o p >> 1 || (p o q >> 1) >> 1)
   weak_mult_comm               |- !r. Ring r ==> !p q. weak p /\ weak q ==> (p o q = q o p)
   weak_mult_cmult              |- !r. Ring r ==> !c. c IN R ==> !p q. weak p /\ weak q ==> (p o c o q = (c o p) o q)
   weak_mult_shift_1_comm       |- !r. Ring r ==> !p q. weak p /\ weak q ==> (p o q >> 1 = (p >> 1) o q)

   Theorems on polynomial multiplication distributes over addition:
#  weak_mult_radd   |- !r. Ring r ==> !p q t. weak p /\ weak q /\ weak t ==> (p o (q || t) = p o q || p o t)
#  weak_mult_ladd   |- !r. Ring r ==> !p q t. weak p /\ weak q /\ weak t ==> ((p || q) o t = p o t || q o t)
   weak_mult_add    |- !r. Ring r ==> !p q t. weak p /\ weak q /\ weak t ==>
                                      (p o (q || t) = p o q || p o t) /\ ((p || q) o t = p o t || q o t)

   Associativity of weak polynomial multiplication:
   weak_mult_assoc   |- !r. Ring r ==> !p q t. weak p /\ weak q /\ weak t ==> ((p o q) o t = p o q o t)
   weak_mult_clauses |- !r. Ring r ==> !p q t. weak p /\ weak q /\ weak t ==>
           ([] o p = []) /\ (p o [] = []) /\ (p o q = q o p) /\ ((p o q) o t = p o q o t)

   Theorems on polynomial multiplicative identity:
#  weak_one_ne_zero  |- [#1] <> []
#  weak_one          |- !r. Ring r ==> weak [#1]
   weak_one_poly     |- !r. Ring r ==> weak |1|
#  weak_cmult_one    |- !r. Ring r ==> !c. c IN R ==> (c o [#1] = [c])
#  weak_cmult_lone   |- !r. Ring r ==> !p. weak p ==> (#1 o p = p)
#  weak_mult_lone    |- !r. Ring r ==> !p. weak p ==> ([#1] o p = p)
#  weak_mult_rone    |- !r. Ring r ==> !p. weak p ==> (p o [#1] = p)
   weak_mult_lone    |- !r. Ring r ==> !p. weak p ==> ([#1] o p = p)

   Polynomial leading coefficient:
#  poly_lead_const    |- !h. lead [h] = h
#  poly_lead_of_zero  |- !r. lead [] = #0
#  poly_lead_zero     |- !r. lead |0| = #0
#  poly_lead_one      |- !r. Ring r ==> (lead |1| = #1)
#  poly_lead_alt      |- !p. p <> |0| ==> (lead p = LAST p)
   poly_lead_at_deg_index  |- !p. p <> |0| ==> (lead p = EL (deg p) p)
#  poly_lead_cons     |- !h t. t <> |0| ==> (lead (h::t) = lead t)
   zero_poly_lead     |- !r p. zerop p ==> (lead p = #0)
#  poly_lead_shift    |- !p n. lead (p >> n) = lead p
#  weak_lead_element  |- !r. Ring r ==> !p. weak p ==> lead p IN R

   Polynomial Normalization:
   poly_chop_of_zero    |- !r. chop [] = []
   poly_chop_cons       |- !r h t. chop (h::t) = if zerop (h::t) then [] else h::chop t
   poly_chop_length     |- !p. LENGTH (chop p) <= LENGTH p
   poly_chop_zero_poly  |- !p. zerop p ==> (chop p = |0|)
#  poly_chop_zero       |- !r. chop |0| = |0|
   zero_poly_chop       |- !p. zerop p <=> (chop p = [])
#  poly_chop_chop       |- !p. chop (chop p) = chop p
   poly_chop_weak       |- !p. weak p ==> weak (chop p)
   zero_poly_eq_zero_poly_chop  |- !p. zerop p <=> zerop (chop p)
   poly_chop_eq_chop    |- !r p q. (LENGTH p = LENGTH q) ==> ((chop p = chop q) <=> (p = q))
   poly_chop_weak_alt   |- !r. Ring r ==> !p. weak p ==> (chop p = p * |1|)
#  poly_chop_add        |- !r. Ring r ==> !p q. weak p /\ weak q ==> (chop (p || q) = chop (chop p || q))
#  poly_chop_add_comm   |- !r. Ring r ==> !p q. weak p /\ weak q ==> (chop (p || q) = chop (p || chop q))
#  poly_chop_add_chop   |- !r. Ring r ==> !p q. weak p /\ weak q ==> (chop (p || q) = chop (chop p || chop q))
#  poly_chop_cmult      |- !r. Ring r ==> !p. weak p ==> !c. c IN R ==> (chop (c o p) = chop (c o chop p))
#  poly_chop_neg        |- !r. Ring r ==> !p. weak p ==> (chop (neg p) = neg (chop p))
#  poly_chop_shift      |- !p n. chop (p >> n) = chop p >> n
#  poly_chop_mult       |- !r. Ring r ==> !p q. weak p /\ weak q ==> (chop (p o q) = chop (chop p o q))
#  poly_chop_mult_comm  |- !r. Ring r ==> !p q. weak p /\ weak q ==> (chop (p o q) = chop (p o chop q))
#  poly_chop_mult_chop  |- !r. Ring r ==> !p q. weak p /\ weak q ==> (chop (p o q) = chop (chop p o chop q))

   Simple Normalization Theorems:
   poly_chop_const_zero       |- chop [#0] = []
   poly_chop_const_zero       |- chop [#0] = |0|
   poly_chop_const_eq_zero    |- !r h. Ring r /\ h IN R ==> ((chop [h] = |0|) <=> (h = #0))
   poly_chop_const_nonzero    |- !r h. h IN R /\ h <> #0 ==> (chop [h] = [h])
   poly_chop_of_last_nonzero  |- !p. chop p <> [] ==> LAST (chop p) <> #0
   poly_chop_last_nonzero     |- !p. chop p <> |0| ==> LAST (chop p) <> #0
   poly_chop_alt              |- !r p. chop (SNOC #0 p) = chop p
   poly_chop_lead_zero        |- !r p. (lead (chop p) = #0) <=> (chop p = |0|)
   poly_chop_nonzero_eq       |- !r p. p <> |0| /\ (chop p = p) <=> lead p <> #0
   poly_chop_eq               |- !r p. (chop p = p) <=> (p = |0|) \/ lead p <> #0
   poly_chop_front            |- !r p. p <> |0| ==> ((lead p = #0) <=> (chop (FRONT p) = chop p))
   poly_chop_add_genlist_zero |- !r p n. chop (p ++ GENLIST (K #0) n) = chop p
   poly_chop_pad_right        |- !r p n. chop (PAD_RIGHT #0 n p) = chop p

   Polynomial Exponentiation.:
#  poly_exp_SUC      |- !p n. p ** SUC n = p * p ** n
   weak_exp_0        |- !p. p ** 0 = |1|
   weak_exp_1        |- !r p. p ** 1 = p * |1|
   weak_exp_2        |- !r. Ring r ==> !p. weak p ==> (p ** 2 = p * p)
#  weak_exp_weak     |- !r. Ring r ==> !p. weak p ==> !n. weak (p ** n)

   Theorems on polynomial degree (basic, not rely on poly):
   poly_deg_pos_or_zero    |- !p. 0 <= deg p
   poly_deg_not_less       |- !p. ~(deg p < 0)
#  poly_deg_of_zero        |- deg [] = 0
#  poly_deg_zero           |- deg |0| = 0
   poly_deg_pos_nonzero    |- !p. 0 < deg p ==> p <> |0|
#  poly_deg_const          |- !h. deg [h] = 0
#  poly_deg_of_one         |- !r. deg [#1] = 0
#  poly_deg_one            |- !r. deg |1| = 0
   poly_deg_nonzero        |- !p. p <> |0| ==> (deg p = PRE (LENGTH p))
#  poly_deg_cons_length    |- !h t. deg (h::t) = LENGTH t
#  poly_deg_cons           |- !h p. p <> |0| ==> (deg (h::p) = SUC (deg p))
   poly_last_at_deg_index  |- !p. p <> |0| ==> (LAST p = EL (deg p) p)
   poly_deg_less_length    |- !p. p <> |0| ==> !k. deg p < k <=> ~(k < LENGTH p)
   poly_deg_chop           |- !p. weak p ==> deg (chop p) <= deg p
   poly_deg_weak_eq_zero   |- !p. weak p /\ (deg p = 0) ==> (p = |0|) \/ ?h. h IN R /\ (p = [h])
   poly_deg_weak_neg       |- !r. Ring r ==> !p. weak p ==> (deg (neg p) = deg p)
   poly_deg_weak_cmult     |- !r c p. deg (c o p) = deg p
   poly_deg_shift_1        |- !r p. p <> |0| ==> (deg (p >> 1) = SUC (deg p))
   poly_deg_shift          |- !r p. p <> |0| ==> !n. deg (p >> n) = deg p + n
   poly_deg_shift_equal    |- !r p q. 0 < deg q /\ deg q <= deg p ==> (deg (q >> (deg p - deg q)) = deg p)
   poly_eq_deg_eq          |- !r p q. (p = q) ==> (deg p = deg q)
   weak_deg_chop_eq_0      |- !r p. weak p /\ (deg p = 0) ==> (deg (chop p) = 0)
   weak_front_deg          |- !r p. 0 < deg p ==> (deg p = SUC (deg (FRONT p)))

   Polynomial Coefficient:
#  poly_coeff_of_zero         |- !r n. [] ' n = #0
#  poly_coeff_zero            |- !r n. |0| ' n = #0
   poly_coeff_cons            |- !r h t n. (h::t) ' n = if deg (h::t) < n then #0 else EL n (h::t)
#  poly_coeff_0_cons          |- !h t. (h::t) ' 0 = h
   poly_coeff_nonzero         |- !p. p <> |0| ==> !n. p ' n = if deg p < n then #0 else EL n p
   poly_coeff_nonzero_alt     |- !p. p <> |0| ==> !n. p ' n = if n < LENGTH p then EL n p else #0
   poly_coeff_as_element      |- !r p. p <> |0| ==> !k. k < LENGTH p ==> (p ' k = EL k p)
   poly_coeff_SUC             |- !h t k. (h::t) ' (SUC k) = t ' k
   poly_coeff_lead            |- !p. p ' (deg p) = lead p
   zero_poly_coeff_all_zero   |- !p. zerop p <=> !k. p ' k = #0
   poly_coeff_chop            |- !p. weak p ==> !k. chop p ' k = p ' k
   weak_coeff_element         |- !r. Ring r ==> !p. weak p ==> !k. p ' k IN R
   poly_coeff_const           |- !r h k. [h] ' k = if k = 0 then h else #0
   poly_coeff_front           |- !r p. p <> |0| /\ (lead p = #0) ==> !k. FRONT p ' k = p ' k

   Degree of Polynomial Addition (weak form):
   poly_deg_weak_add    |- !r. Ring r ==> !p q. deg (p || q) = MAX (deg p) (deg q)

   Degree of Polynomial Multiplication (weak form):
   poly_deg_weak_mult   |- !r. Ring r ==> !p q. p <> |0| /\ q <> |0| ==> (deg (p o q) = deg p + deg q)

   Polynomial Evaluation:
   poly_eval_of_zero  |- !r x. eval [] x = #0
   poly_eval_cons     |- !r h t x. eval (h::t) x = h + eval t x * x
#  poly_eval_zero     |- !r x. eval |0| x = #0
#  poly_eval_const    |- !r. Ring r ==> !h x. h IN R /\ x IN R ==> (eval [h] x = h)
#  weak_eval_element  |- !r. Ring r ==> !p. weak p ==> !x. x IN R ==> eval p x IN R
#  poly_eval_zerop    |- !r. Ring r ==> !p x. zerop p /\ x IN R ==> (eval p x = #0)
#  poly_eval_chop     |- !r. Ring r ==> !p x. x IN R ==> (eval (chop p) x = eval p x)
#  poly_eval_one      |- !r. Ring r ==> !x. x IN R ==> (eval |1| x = #1)
   weak_eval_cmult    |- !r. Ring r ==> !p c x.  weak p /\ c IN R /\ x IN R ==> (eval (c o p) x = c * eval p x)
   weak_eval_neg      |- !r. Ring r ==> !p x. weak p /\ x IN R ==> (eval (neg p) x = -eval p x)
   weak_eval_add      |- !r. Ring r ==> !p q x. weak p /\ weak q /\ x IN R ==>
                                        (eval (p || q) x = eval p x + eval q x)
   weak_eval_shift    |- !r. Ring r ==> !p x. weak p /\ x IN R ==> !n. eval (p >> n) x = eval p x * x ** n
   weak_eval_mult     |- !r. Ring r ==> !p q x. weak p /\ weak q /\ x IN R ==>
                                        (eval (p o q) x = eval p x * eval q x)
   weak_eval_snoc     |- !r. Ring r ==> !h t. h IN R /\ weak t ==> !x. x IN R ==>
                                        (eval (SNOC h t) x = eval t x + h * x ** LENGTH t)

   Polynomial Root:
#  poly_root_of_zero  |- !r x. x IN R ==> root [] x
#  poly_root_zero     |- !r x. x IN R ==> root |0| x

   Useful Theorems:
   weak_lead_cmult       |- !r. Ring r ==> !p c. c IN R ==> (lead (c o p) = c * lead p)
   weak_deg_cmult        |- !r. Ring r ==> !p c. c IN R ==> (deg (c o p) = deg p)
   weak_add_one_shift    |- !r. Ring r /\ #1 <> #0 ==> !p. weak p /\ p <> |0| ==>
                                (p || [#1] >> SUC (deg p) = SNOC #1 p)
   weak_add_cmult_shift  |- !r. Ring r /\ #1 <> #0 ==> !c p. c IN R /\ weak p /\ p <> |0| ==>
                                (p || c o ([#1] >> SUC (deg p)) = SNOC c p)
   weak_add_const_shift  |- !r. Ring r ==> !p c. weak p /\ c IN R /\ c <> #0 ==>
                                (p || [c] >> LENGTH p = SNOC c p)
*)
(* ------------------------------------------------------------------------- *)
(* Polynomials over a Ring.                                                  *)
(* ------------------------------------------------------------------------- *)

(*
Weak polynomails are not normalized.

The idea is this: if all opertations are defined componentwise, for weak polynomials,
then when it comes to polynomials, it is just adding normalization, which should be easy.

e.g. for pair-addition, it is easy to show:  p || q = q || p,  p || q || t = p || (q || t).

So for the real addition,
  p + q
= chop (p || q)
= chop (q || p)     -- weak_add_comm: p || q = q || p
= q + p

  p + q + t
= (p + q) + t
= chop (chop (p || q) || t)
= chop (p || q || t)         -- hope this is easy -- poly_chop_add: chop (p || q) = chop (chop p || q)
= chop (p || (q || t))
= chop (p || chop (q || t))  -- hope this is easy -- poly_chop_add_comm: chop (p || q) = chop (p || chop q)
= p + (q + t)

Also, for cpair, it is easy to show: (a * b) o p = a o (b o p), (a + b) o p = a o p || b o p, c o (p || q) = c o p || c o q

then for the real scalar multiplication,
  (a * b) * p
= chop ((a * b) o p)
= chop (a o (b o p))
= chop (a o chop (b o p))    -- hope this is easy
= chop (a o (b * p))
= a * (b * p)

  (a + b) * p
= chop ((a + b) o p)
= chop (a o p || b o p)
= chop (chop (a o p) || chop (b o p))  -- hope this is easy
= chop (a * p || b * p)
= a * p + b * p

  c * (p + q)
= chop (c o chop (p || q))
= chop (c o (p || q))     -- hope this is easy
= chop (c o p || c o q)
= chop (chop (c o p) || chop (c o q))  -- hope this is easy
= chop (c * p || c * q)
= c * p + c * q

How about multiplication, which involves cpair, pair and shift?

*)

(* ------------------------------------------------------------------------- *)
(* Weak Polynomials -- as a list of ring elements.                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: weak [] *)
(* Proof: by defintion. *)
val weak_of_zero = save_thm("weak_of_zero", Weak_def |> CONJUNCT1);
(* > val weak_of_zero = |- !r. weak [] <=> T : thm *)

(* Theorem: weak (h::t) iff h IN R /\ weak t *)
(* Proof: by definition. *)
val weak_cons = save_thm("weak_cons", Weak_def |> CONJUNCT2);
(* > val weak_cons = |- !r h t. weak (h::t) <=> h IN R /\ weak t : thm *)

(* definition exported already *)
(* val _ = export_rewrites ["weak_of_zero", "weak_cons"]; *)

(* Theorem: weak |0| *)
(* Proof: by weak_of_zero and poly_zero. *)
val weak_zero = save_thm("weak_zero", weak_of_zero |> REWRITE_RULE [GSYM poly_zero]);
(* > val weak_zero = |- !r. weak |0| : thm *)

val _ = export_rewrites ["weak_zero"];

(* Theorem: !p. weak p <=> EVERY (\x. x IN R) p *)
(* Proof:
   By induction on p.
   Base: weak [] <=> EVERY (\x. x IN R) []
      Note weak [] = T                     by weak_of_zero
       and EVERY (\x. x IN R) [] = T       by EVERY_DEF
   Step: weak p <=> EVERY (\x. x IN R) p ==> !h. weak (h::p) <=> EVERY (\x. x IN R) (h::p)
          weak (h::p)
      <=> h IN R /\ weak p                 by weak_cons
      <=> h IN R /\ EVERY (\x. x IN R) p   by induction hypothesis
      <=> EVERY (\x. x IN R) (h::p)        by EVERY_DEF
*)
val weak_def_alt = store_thm(
  "weak_def_alt",
  ``!r:'a ring. !p. weak p <=> EVERY (\x. x IN R) p``,
  rpt strip_tac >>
  Induct_on `p` >>
  rw[]);

(* Theorem: weak (p ++ q) <=> weak p /\ weak q *)
(* Proof:
     weak (p ++ q)
   <=> EVERY (\x. x IN R) (p ++ q)                    by weak_def_alt
   <=> EVERY (\x. x IN R) p /\ EVERY (\x. x IN R) q   by EVERY_APPEND
   <=> weak p /\ weak q                               by weak_def_alt
*)
val weak_append_weak = store_thm(
  "weak_append_weak",
  ``!r:'a ring. !p q. weak (p ++ q) <=> weak p /\ weak q``,
  rw[weak_def_alt, EVERY_APPEND]);

(* Theorem: weak (SNOC h t) <=> h IN R /\ weak t *)
(* Proof:
   By induction on t.
   Base: weak (SNOC h []) <=> h IN R /\ weak []
          weak (SNOC h [])
      <=> weak [h]                       by SNOC_NIL
      <=> h IN R /\ weak []              by weak_cons
   Step: weak (SNOC h t) <=> h IN R /\ weak t ==>
         !h'. weak (SNOC h (h'::t)) <=> h IN R /\ weak (h'::t)
          weak (SNOC h (h'::t))
      <=> weak (h'::SNOC (h::t))         by SNOC_CONS
      <=> h' IN R /\ weak (SNOC (h::t))  by weak_cons
      <=> h' IN R /\ h IN R /\ weak t    by induction hypothesis
      <=> h IN R /\ h' IN R /\ weak t    by logical AND
      <=> h IN R /\ weak (h'::t)         by weak_cons
*)
val weak_snoc = store_thm(
  "weak_snoc",
  ``!(r:'a ring) h t. weak (SNOC h t) <=> h IN R /\ weak t``,
  rpt strip_tac >>
  Induct_on `t` >-
  rw[] >>
  rw[] >>
  metis_tac[]);

(* Theorem: weak p <=> EVERY (\c. c IN R) p *)
(* Proof:
   By induction on p.
   Base: weak [] <=> EVERY (\c. c IN R) []
      Note weak [] = T                    by Weak_def
       and EVERY (\c. c IN R) [] = T      by EVERY_DEF
      Thus true.
   Step: weak p <=> EVERY (\c. c IN R) p ==>
         !h. weak (h::p) <=> EVERY (\c. c IN R) (h::p)

         weak (h::p)
     <=> h IN R /\ weak p                 by Weak_def
     <=> h IN R /\ EVERY (\c. c IN R) p   by induction hypothesis
     <=> EVERY (\c. c IN R) (h::p)        by EVERY_DEF
*)
val weak_every_element = store_thm(
  "weak_every_element",
  ``!r:'a ring. !p. weak p <=> EVERY (\c. c IN R) p``,
  strip_tac >>
  Induct >>
  rw_tac std_ss[Weak_def, EVERY_DEF]);

(* Theorem: weak p <=> (!x. MEM x p ==> x IN R) *)
(* Proof: by weak_every_element, EVERY_MEM *)
val weak_every_mem = store_thm(
  "weak_every_mem",
  ``!r:'a ring. !p. weak p <=> (!x. MEM x p ==> x IN R)``,
  rw[weak_every_element, EVERY_MEM]);

(* A better proof without induction. *)

(* Theorem: weak p /\ p <> |0| ==> (LAST p) IN R *)
(* Proof:
   Note p <> |0| means p <> []                 by poly_zero
   Thus ?h t. h IN R /\ weak t /\ (p = h::t)   by weak_cons, list_CASES
    and (LAST p) IN R                          by MEM_LAST, weak_every_mem
*)
Theorem weak_last_element:
  !p. weak p /\ p <> |0| ==> (LAST p) IN R
Proof
  rpt strip_tac >>
  ‘?h t. h IN R /\ weak t /\ (p = h::t)’
    by metis_tac[list_CASES, weak_cons, poly_zero] >>
  metis_tac[MEM_LAST, weak_every_mem]
QED

(* Theorem: weak p /\ p <> |0| ==> weak (FRONT p) /\ weak [LAST p] *)
(* Proof:
   Note p <> |0| means p <> []                 by poly_zero
   Thus ?h t. h IN R /\ weak t /\ (p = h::t)   by weak_cons, list_CASES
   Thus weak (FRONT p)                         by MEM_FRONT, weak_every_mem
    and weak [LAST p]                          by MEM_LAST, weak_every_mem, Weak_def
*)
val weak_front_last = store_thm(
  "weak_front_last",
  ``!p. weak p /\ p <> |0| ==> weak (FRONT p) /\ weak [LAST p]``,
  ntac 3 strip_tac >>
  `?h t. h IN R /\ weak t /\ (p = h::t)` by metis_tac[list_CASES, weak_cons, poly_zero] >>
  metis_tac[MEM_FRONT, MEM_LAST, weak_every_mem, Weak_def]);

(* Theorem: weak p ==> !q. q <= p ==> weak q *)
(* Proof:
       weak p
   <=> EVERY (\c. c IN R) p    by weak_every_element
   ==> EVERY (\c. c IN R) q    by sublist_every, q <= p
   <=> weak q                  by weak_every_element
*)
val weak_sublist = store_thm(
  "weak_sublist",
  ``!r:'a ring p q. weak p ==> !q. q <= p ==> weak q``,
  metis_tac[weak_every_element, sublist_every]);

(* Theorem: weak p ==> weak (TAKE n p) *)
(* Proof:
   Note (TAKE n p) <= p        by sublist_take
   Thus weak (TAKE n p)        by weak_sublist
*)
val weak_take = store_thm(
  "weak_take",
  ``!r:'a ring p n. weak p ==> weak (TAKE n p)``,
  metis_tac[weak_sublist, sublist_take]);

(* Theorem: weak p ==> weak (DROP n p) *)
(* Proof:
   Note (DROP n p) <= p        by sublist_drop
   Thus weak (DROP n p)        by weak_sublist
*)
val weak_drop = store_thm(
  "weak_drop",
  ``!r:'a ring p n. weak p ==> weak (DROP n p)``,
  metis_tac[weak_sublist, sublist_drop]);

(* Theorem: weak p /\ p <> |0| => weak (FRONT p) *)
(* Proof:
   Note (FRONT p) <= p        by sublist_front, poly_zero
   Thus weak (FRONT p)        by weak_sublist
*)
val weak_front = store_thm(
  "weak_front",
  ``!r:'a ring p. weak p /\ p <> |0| ==> weak (FRONT p)``,
  metis_tac[weak_sublist, sublist_front, poly_zero]);

(* Theorem: weak p /\ p <> |0| => weak (TL p) *)
(* Proof:
   Note (TL p) <= p        by sublist_tail, poly_zero
   Thus weak (TL p)        by weak_sublist
*)
val weak_tail = store_thm(
  "weak_tail",
  ``!r:'a ring p. weak p /\ p <> |0| ==> weak (TL p)``,
  metis_tac[weak_sublist, sublist_tail, poly_zero]);

(* ------------------------------------------------------------------------- *)
(* Zero Polynomials - for normalization.                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: zerop []. *)
(* Proof: by definition. *)
val zero_poly_of_zero = save_thm("zero_poly_of_zero", zero_poly_def |> CONJUNCT1);
(* > val zero_poly_of_zero = |- !r. zerop [] <=> T : thm *)

(* Theorem: zerop (h::t) iff h = #0 /\ zerop t *)
(* Proof: by definition. *)
val zero_poly_cons = save_thm("zero_poly_cons", zero_poly_def |> CONJUNCT2);
(* > val zero_poly_cons = |- !r h t. zerop (h::t) <=> (h = #0) /\ zerop t : thm *)

(* definition already exported *)
(* val _ = export_rewrites ["zero_poly_of_zero", "zero_poly_cons"]; *)

(* Theorem: zerop |0| <=> T  *)
(* Proof: by weak_mult_of_lzero and poly_zero. *)
val zero_poly_zero = save_thm("zero_poly_zero", zero_poly_of_zero |> REWRITE_RULE [GSYM poly_zero]);
(* > val zero_poly_zero = |- !r. zerop |0| <=> T : thm *)

val _ = export_rewrites ["zero_poly_zero"];

(* Theorem: zerop p <=> EVERY (\c. c = #0) p *)
(* Proof: by induction.
   Base: zerop [] <=> EVERY (\c. c = #0) []
      true by zero_poly_of_zero, EVERY_DEF.
   Step: zerop p <=> EVERY (\c. c = #0) p ==>
              !h. zerop (h::p) <=> EVERY (\c. c = #0) (h::p)
      true by zero_poly_cons, EVERY_CONS, induction hypothesis.
*)
val zero_poly_every_zero = store_thm(
  "zero_poly_every_zero",
  ``!p. zerop p <=> EVERY (\c. c = #0) p``,
  Induct >>
  rw[]);

(* Theorem: zerop p ==> EVERY (\c. c IN R) p  *)
(* Proof: by zero_poly_every_zero and ring_zero_element. *)
val zero_poly_every_element = store_thm(
  "zero_poly_every_element",
  ``!r:'a ring. Ring r ==> !p:'a poly. zerop p ==> EVERY (\c. c IN R) p``,
  strip_tac >>
  strip_tac >>
  Induct >>
  rw[ring_zero_element]);
(* Q: How to make use of zero_poly_every_zero and ring_zero_element?
   A: see below.
*)

(* Theorem: zerop (SNOC #0 p) <=> zerop p *)
(* Proof:
       zerop (SNOC #0 p)
   <=> EVERY (\c. c = #0) (SNOC #0 p)     by zero_poly_every_zero
   <=> EVERY (\c. c = #0) p /\ (#0 = #0)  by EVERY_SNOC
   <=> zerop p /\ T                       by zero_poly_every_zero
   <=> zerop p
*)
val zero_poly_snoc = store_thm(
  "zero_poly_snoc",
  ``!r:'a ring. !p. zerop (SNOC #0 p) <=> zerop p``,
  rw[zero_poly_every_zero, EVERY_SNOC]);

(* Theorem: zerop p ==> weak p  *)
(* Proof: by induction on p.
   Base: zerop [] ==> weak []
      true by zero_poly_of_zero, weak_of_zero.
   Step: zerop p ==> weak p ==> zerop (h::p) ==> weak (h::p)
      true by ring_zero_element, zero_poly_cons, weak_cons.
*)
val zero_poly_weak = store_thm(
  "zero_poly_weak",
  ``!r:'a ring. Ring r ==> !p:'a poly. zerop p ==> weak p``,
  strip_tac >>
  strip_tac >>
  Induct >>
  rw[ring_zero_element]);

(* Theorem: Ring r ==> (( |1| = |0|) <=> !p. weak p ==> zerop p) *)
(* Proof:
   If part: |1| = |0| /\ weak p ==> zerop p
      Note |1| = |0|
        ==> #1 = #0       by poly_one_eq_poly_zero
        ==> R = {#0}      by ring_one_eq_zero
      Also !c. MEM c p
           ==> c IN R     by weak_every_mem
           ==> c = #0     by IN_SING
      Thus EVERY (\c. c = #0) p     by EVERY_MEM
        or zerop p                  by zero_poly_every_zero

   Only-if part: !p. weak p ==> zerop p ==> |1| = |0|
      By contradiction, suppose |1| <> |0|.
      Then #1 <> #0       by poly_one_eq_poly_zero
       Now weak [#1]      by weak_cons
       but ~zerop [#1]    by zero_poly_def, #1 <> #0
      This contradicts the implication.
*)
val weak_all_zero_poly = store_thm(
  "weak_all_zero_poly",
  ``!r:'a ring. Ring r ==> (( |1| = |0|) <=> !p. weak p ==> zerop p)``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    `#1 = #0` by rw[GSYM poly_one_eq_poly_zero] >>
    `R = {#0}` by rw[GSYM ring_one_eq_zero] >>
    rw[zero_poly_every_zero, EVERY_MEM] >>
    metis_tac[weak_every_mem, IN_SING],
    spose_not_then strip_assume_tac >>
    `#1 <> #0` by rw[GSYM poly_one_eq_poly_zero] >>
    `weak [#1]` by rw[] >>
    metis_tac[zero_poly_cons]
  ]);

(* Theorem: zerop [#0] *)
(* Proof: by zero_poly_every_zero. *)
val zero_poly_element_zero = store_thm(
  "zero_poly_element_zero",
  ``zerop [#0]``,
  rw[]);

val _ = export_rewrites ["zero_poly_element_zero"];

(* Theorem: zerop p ==> zerop (#0::p) *)
(* Proof: by definition. *)
val zero_poly_cons_zero = store_thm(
  "zero_poly_cons_zero",
  ``!p. zerop p ==> zerop (#0::p)``,
  rw[]);

(* Theorem: zerop (h::t) ==> LAST (h::t) = #0 *)
(* Proof: by induction on t. *)
val zero_poly_last_zero = store_thm(
  "zero_poly_last_zero",
  ``!h t. zerop (h::t) ==> (LAST (h::t) = #0)``,
  Induct_on `t` >>
  rw[]);

(* Theorem: zerop p <=> !k. k < LENGTH p ==> (EL k p = #0) *)
(* Proof:
       zerop p
   <=> EVERY (\c. c = #0) p     by zero_poly_every_zero
   <=> !k. k < LENGTH p ==> (EL k p = #0)   by EVERY_EL
*)
val zero_poly_element = store_thm(
  "zero_poly_element",
  ``!p. zerop p <=> !k. k < LENGTH p ==> (EL k p = #0)``,
  rw[zero_poly_every_zero, EVERY_EL]);

(* Theorem: zerop p /\ zerop q ==> ((LENGTH p = LENGTH q) <=> (p = q)) *)
(* Proof:
   If part: (LENGTH p = LENGTH q) ==> (p = q)
      Note EVERY (\x. x = #0) p                 by zero_poly_every_zero
       and EVERY (\x. x = #0) q                 by zero_poly_every_zero
      Thus !x. x < LENGTH p ==> (EL x l1 = #0)  by EVERY_EL
       and !x. x < LENGTH q ==> (EL x l1 = #0)  by EVERY_EL
       ==> p = q                                by LIST_EQ
   Only-if part: p = q ==> (LENGTH p = LENGTH q)
      This is trivially true.
*)
val zero_poly_eq_zero_poly = store_thm(
  "zero_poly_eq_zero_poly",
  ``!r:'a ring. !p q. zerop p /\ zerop q ==> ((LENGTH p = LENGTH q) <=> (p = q))``,
  rw[EQ_IMP_THM] >>
  qabbrev_tac `f = \x. x = #0` >>
  `!x. f x = (x = #0)` by rw[Abbr`f`] >>
  `EVERY f p` by rw[GSYM zero_poly_every_zero, Abbr`f`] >>
  `EVERY f q` by rw[GSYM zero_poly_every_zero, Abbr`f`] >>
  metis_tac[LIST_EQ, EVERY_EL]);

(* Theorem: zerop (GENLIST (K #0) n) *)
(* Proof:
   Note !i. (K #0) i = #0     by K_THM
   Let p = GENLIST (K #0) n
     so EVERY (\x. x = #0) p  by EVERY_GENLIST
     or zerop p               by zero_poly_every_zero
*)
val zero_poly_genlist_zero = store_thm(
  "zero_poly_genlist_zero",
  ``!r:'a ring. !n. zerop (GENLIST (K #0) n)``,
  rw[zero_poly_every_zero, EVERY_GENLIST]);

(* ------------------------------------------------------------------------- *)
(* Weal Polynomial Pair Addition.                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: [] || [] = [] *)
(* Proof: by defintion. *)
val weak_add_of_zero_zero = store_thm(
  "weak_add_of_zero_zero",
  ``[] || [] = []``,
  rw_tac std_ss[weak_add_def]);

(* Theorem: [] || p = p *)
(* Proof: by defintion. *)
val weak_add_of_lzero = store_thm(
  "weak_add_of_lzero",
  ``!p:'a poly. [] || p = p``,
  metis_tac[weak_add_def, list_CASES]);

(* Theorem: p || [] = p *)
(* Proof: by defintion. *)
val weak_add_of_rzero = store_thm(
  "weak_add_of_rzero",
  ``!p:'a poly. p || [] = p``,
  metis_tac[weak_add_def, list_CASES]);

val _ = export_rewrites ["weak_add_of_zero_zero", "weak_add_of_lzero", "weak_add_of_rzero"];

(* Theorem: (p || [] = p) /\ ([] || p = p) *)
(* Proof: by weak_add_def. *)
val weak_add_nil = store_thm(
  "weak_add_nil",
  ``!r:'a ring p. (p || [] = p) /\ ([] || p = p)``,
  rw[]);

(* Theorem alias *)
val weak_add_of_zero = save_thm("weak_add_of_zero", weak_add_nil);
(* val weak_add_of_zero = |- !r p. (p || [] = p) /\ ([] || p = p): thm *)

(* Theorem: (p || |0| = p) /\ ( |0| || p = p) *)
(* Proof: by weak_add_lzero, weak_add_rzero *)
val weak_add_zero = store_thm(
  "weak_add_zero",
  ``!r:'a ring p. (p || |0| = p) /\ ( |0| || p = p)``,
  rw[]);

(* Theorem: |0| || |0| = |0| *)
(* Proof: by weak_add_zero_zero and poly_zero. *)
val weak_add_zero_zero = save_thm("weak_add_zero_zero", weak_add_of_zero_zero |> REWRITE_RULE [GSYM poly_zero]);
(* > val weak_add_zero_zero = |- |0| || |0| = |0| : thm *)

(* Theorem: |0||| p = p *)
(* Proof: by weak_add_of_lzero and poly_zero. *)
val weak_add_lzero = save_thm("weak_add_lzero", weak_add_of_lzero |> REWRITE_RULE [GSYM poly_zero]);
(* > val weak_add_lzero = |- !p. |0| || p = p : thm *)

(* Theorem: p || |0| = p *)
(* Proof: by weak_add_of_rzero and poly_zero. *)
val weak_add_rzero = save_thm("weak_add_rzero", weak_add_of_rzero |> REWRITE_RULE [GSYM poly_zero]);
(* > val weak_add_rzero = |- !p. p || |0| = p : thm *)

val _ = export_rewrites ["weak_add_zero_zero", "weak_add_lzero", "weak_add_rzero"];

(* Theorem: weak_add (r:'a ring) (ph:'a :: pt) (qh:'a :: qt) = ph + qh :: weak_add r pt qt *)
(* Proof: by definition. *)
val weak_add_cons = save_thm("weak_add_cons", weak_add_def |> CONJUNCTS |> last);
(* > val weak_add_cons = |- !qt qh pt ph f. (ph::pt) || (qh::qt) = ph + qh::pt || qt : thm *)

val _ = export_rewrites ["weak_add_cons"];

(* Theorem: LENGTH (p || q) = MAX (LENGTH p) (LENGTH q) *)
(* Proof: by induction on p and q.
   Base: LENGTH ([] || q) = MAX (LENGTH []) (LENGTH q)
        LENGTH ([] || q)
      = LENGTH q                     by weak_add_of_lzero
      = MAX 0 (LENGTH q)             by MAX_0
      = MAX (LENGTH []) (LENGTH q)   by LENGTH
   Step: induct on q.
      Base: LENGTH ((h::p) || []) = MAX (LENGTH (h::p)) (LENGTH [])
           LENGTH ((h::p) || [])
         = LENGTH (h::p)                       by weak_add_of_rzero
         = MAX (LENGTH (h::p)) 0               by MAX_0
         = MAX (LENGTH (h::p)) (LENGTH [])     by LENGTH
      Step: !q. LENGTH (p || q) = MAX (LENGTH p) (LENGTH q) ==>
                 !h'. LENGTH ((h::p) || (h'::q)) = MAX (LENGTH (h::p)) (LENGTH (h'::q))
        LENGTH ((h::p) || (h'::q))
      = LENGTH (h + h'::p || q)                by weak_add_cons
      = SUC (LENGTH (p || q))                  by LENGTH
      = SUC (MAX (LENGTH p) (LENGTH q))        by induction hypothesis
      = MAX (SUC (LENGTH p)) (SUC (LENGTH q))  by SUC_MAX
      = MAX (LENGTH (h::p)) (LENGTH (h'::q))   by LENGTH
*)
val weak_add_length = store_thm(
  "weak_add_length",
  ``!r:'a ring. !p q. LENGTH (p || q) = MAX (LENGTH p) (LENGTH q)``,
  strip_tac >>
  Induct >-
  rw[] >>
  strip_tac >>
  Induct >-
  rw[] >>
  rw[weak_add_cons] >>
  rw[SUC_MAX]);

(* Theorem: p || q = [] <=> p = [] /\ q = [] *)
(* Proof:
       p || q = []
   <=> LENGTH (p || q) = 0               by LENGTH_NIL
   <=> MAX (LENGTH p) (LENGTH q) = 0     by weak_add_length
   <=>     (LENGTH p = 0) /\
           (LENGTH q = 0)                by MAX_EQ_0
   <=> p = [] /\ q = []                  by LENGTH_NIL
*)
val weak_add_eq_of_zero = store_thm(
  "weak_add_eq_of_zero",
  ``!r:'a ring p q. ((p || q = []) <=> (p = []) /\ (q = []))``,
  prove_tac[weak_add_length, LENGTH_NIL, MAX_EQ_0]);

(* Theorem: p || q = |0| <=> p = |0| /\ q = |0| *)
(* Proof: by weak_add_eq_of_zero and poly_zero. *)
val weak_add_eq_zero = save_thm("weak_add_eq_zero", weak_add_eq_of_zero |> REWRITE_RULE [GSYM poly_zero]);
(* > val weak_add_eq_zero = |- !r p q. (p || q = |0|) <=> (p = |0|) /\ (q = |0|) : thm *)

(* Theorem: zerop p ==> p || q = q  *)
(* Note: this is not true: [0;0;0] || [1;2] = [1;2;0] *)

(* Theorem: zerop q ==> p || q = p  *)
(* Note: this is not true: [1;2] || [0;0;0] = [1;2;0] *)

(* Theorem: zerop p /\ zerop q ==> zerop (p || q) *)
(* Proof: by induction on p and q.
   Base: !q. zerop [] /\ zerop q ==> zerop ([] || q)
      true by weak_add_of_lzero.
   Step: induct on q.
      Base: zerop (h::p) /\ zerop [] ==> zerop ((h::p) || [])
         true by weak_add_of_rzero.
      Step: !q. zerop p /\ zerop q ==> zerop (p || q) ==>
                 !h'. zerop (h::p) /\ zerop (h'::q) ==> zerop ((h::p) || (h'::q))
          zerop ((h::p) || (h'::q))
      <=> zerop (h + h' :: p || q))        by weak_add_cons
      <=> h + h' = #0 /\ zerop (p || q)    by zero_poly_cons
      <=> T           /\ zerop (p || q)    by ring_add_zero_zero, as h = h' = #0
      <=> T                                by induction hypothesis
*)
val zero_weak_add_zero = store_thm(
  "zero_weak_add_zero",
  ``!r:'a ring. Ring r ==> !p q. zerop p /\ zerop q ==> zerop (p || q)``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  strip_tac >>
  Induct >>
  rw[]);

(* Theorem: weak (p || q) *)
(* Proof: by induction on p and q.
   Base: !q. weak [] /\ weak q ==> weak ([] || q)
      true by weak_add_of_lzero.
   Step: induct on q.
      Base: weak (h::p) /\ weak [] ==> weak ((h::p) || [])
         true by weak_add_of_rzero.
      Step: !q. weak p /\ weak q ==> weak (p || q) ==>
                 !h'. weak (h::p) /\ weak (h'::q) ==> weak ((h::p) || (h'::q))
          weak ((h::p) || (h'::q))
      <=> weak (h + h' :: p || q)        by weak_add_cons
      <=> h + h' IN R /\ weak (p || q)   by weak_cons
      <=> h + h' IN R /\ T               by induction hypothesis
      <=> T                              by ring_add_element
*)
val weak_add_weak = store_thm(
  "weak_add_weak",
  ``!r:'a ring. Ring r ==> !p q:'a poly. weak p /\ weak q ==> weak (p || q)``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  strip_tac >>
  Induct >>
  rw[]);

val _ = export_rewrites ["weak_add_weak"];

(* Theorem: p || q = q || p *)
(* Proof: by induction on p, q, and ring_add_comm.
   Base: !q. [] || q = q || []
      true by weak_add_of_lzero, weak_add_of_rzero.
   Step: !q. p || q = q || p ==>
              !h q. (h::p) || q = q || (h::p)
   Now use induction on q.
      Base: (h::p) || [] = [] || (h::p)
         true by  weak_add_of_lzero, weak_add_of_rzero.
      Step: !q. p || q = q || p ==>
                 !h'. (h::p) || (h'::q) = (h'::q) || (h::p)
         true by weak_add_cons, ring_add_comm and induction hypothesis.
*)
val weak_add_comm = store_thm(
  "weak_add_comm",
  ``!r:'a ring. Ring r ==> !p q:'a poly. weak p /\ weak q ==> (p || q = q || p)``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw_tac std_ss[weak_add_of_lzero, weak_add_of_rzero] >>
  strip_tac >>
  Induct >-
  rw_tac std_ss[weak_add_of_lzero, weak_add_of_rzero] >>
  metis_tac[weak_add_cons, ring_add_comm, weak_cons]);

(* do not export commutativity. *)
(* val _ = export_rewrites ["weak_add_comm"]; *)

(* Theorem: p || q || t = p || (q || t) *)
(* Proof: by induction on p, q, t and ring_add_assoc.
   Base: [] || q || t = [] || (q || t)
      true by weak_add_of_lzero.
   Step: p || q || t = p || (q || t) ==>
              (h::p) || q || t = (h::p) || (q || t)
   Now use induction on q.
      Base: (h::p) || [] || r = (h::p) || ([] || t)
         true by  weak_add_of_rzero, weak_add_of_lzero.
      Step: p || q || t = p || (q || t) ==>
                 (h::p) || (h'::q) || 6 = (h::p) || ((h'::q) || 6)
         Now use induction on 6.
            Base: (h::p) || (h'::q) || [] = (h::p) || ((h'::q) || [])
               true by  weak_add_of_rzero.
            Step: p || q || t = p || (q || t) ==>
                       (h::p) || (h'::q) || (h''::t) = (h::p) || ((h'::q) || (h''::t))
               true by weak_add_cons, ring_add_assoc and induction hypothesis.
                 (h::p) || (h'::q) || (h''::t)
               = (h + h'::p + q) || (h''::t)      by weak_add_cons
               = (h + h' + h'' :: p || q || t)    by weak_add_cons
               = (h + (h' + h'')::p || (q || t))  by ring_add_assoc, induction hypothesis
               = (h::p) || (h' + h'':: q || t)    by weak_add_cons
               = (h::p) || ((h'::q) || (h''::t))  by weak_add_cons
*)
val weak_add_assoc = store_thm(
  "weak_add_assoc",
  ``!r:'a ring. Ring r ==> !p q t:'a poly. weak p /\ weak q /\ weak t ==> (p || q || t = p || (q || t))``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  strip_tac >>
  Induct >-
  rw[] >>
  strip_tac >>
  Induct >-
  rw[] >>
  rw_tac std_ss[ring_add_assoc, weak_add_cons, weak_cons]);

(* no export of associativity *)
(* val _ = export_rewrites ["weak_add_assoc"]; *)

(* Theorem: Polynomial addition clauses. *)
(* Proof: by theorems proved. *)
val weak_add_clauses = store_thm(
  "weak_add_clauses",
  ``!r:'a ring. Ring r ==> !p q t :'a poly. weak p /\ weak q /\ weak t ==>
      ([] || p = p) /\ (p || [] = p) /\ (p || q = q || p) /\ ((p || q) || t = p || (q || t))``,
  rw[weak_add_comm, weak_add_assoc]);

(* Theorem: Ring r ==> !p q. zerop p /\ weak q /\ LENGTH p <= LENGTH q ==> (p || q = q) *)
(* Proof:
   By induction on p.
   Base: weak q ==> [] || q = q, true by weak_add_of_lzero
   Step: induct on q.
         Base: LENGTH (h::p) <= LENGTH [] ==> ((h::p) || [] = [])
            Note LENGTH (h::p) = SUC (LENGTH p) > 0   by LENGTH
             and LENGTH [] = 0                        by LENGTH
            Thus the condition leads to 0 < 0         by LESS_LESS_EQ_TRANS
            This is a contradiction.
         Step: !q. zerop p /\ weak q /\ LENGTH p <= LENGTH q ==> (p || q = q) ==>
               zerop (h::p) /\ weak (h'::q) /\ LENGTH (h::p) <= LENGTH (h'::q) ==> ((h::p) || (h'::q) = h'::q
            Note h = #0 /\ zerop p                    by zero_poly_cons
             and h' IN R /\ weak q                    by weak_cons
            Also SUC (LENGTH p) <= SUC (LENGTH q)     by LENGTH
              or       LENGTH p <= LENGTH q           by LESS_EQ_MONO
                 (h::p) || (h'::q)
               = (h + h') :: (p || q)                 by weak_add_cons
               = #0 + h' :: q                         by induction hypothesis
               = h':: q                               by ring_add_lzero
*)
val weak_add_lzero_poly = store_thm(
  "weak_add_lzero_poly",
  ``!r:'a ring. Ring r ==> !p q. zerop p /\ weak q /\ LENGTH p <= LENGTH q ==> (p || q = q)``,
  ntac 2 strip_tac >>
  Induct >-
  rw[] >>
  strip_tac >>
  Induct >| [
    rpt strip_tac >>
    `0 < LENGTH (h::p) /\ (LENGTH [] = 0)` by rw[] >>
    fs[DECIDE``~(0 < 0)``],
    rw[]
  ]);

(* Theorem: Ring r ==> !p q. zerop p /\ weak q /\ LENGTH p <= LENGTH q ==> (q || p = q) *)
(* Proof:
   Note zerop p ==> weak p      by zero_poly_weak
     q || p
   = p || q                     by weak_add_comm
   = q                          by weak_add_lzero_poly
*)
val weak_add_rzero_poly = store_thm(
  "weak_add_rzero_poly",
  ``!r:'a ring. Ring r ==> !p q. zerop p /\ weak q /\ LENGTH p <= LENGTH q ==> (q || p = q)``,
  rw[weak_add_lzero_poly, weak_add_comm, zero_poly_weak]);

(* Theorem: weak p /\ weak q /\ (LENGTH p = LENGTH q) ==>
            (p || q = MAP2 (\x y. x + y) p q) *)
(* Proof:
   Let f = \x y. x + y.
   By induction on p.
   Base: (LENGTH [] = LENGTH q) ==> ([] || q = MAP2 f [] q)
      Note q = []          by LENGTH_NIL
       and [] || []
         = []              by weak_add_zero_zero
         = MAP2 f [] []    by MAP2
   Step: by induction on q.
         Base: (LENGTH (h::p) = LENGTH []) ==> ((h::p) || [] = MAP2 f (h::p) [])
            Note LENGTH (h::p) > 0       by LENGTH
             but LENGTH [] = 0           by LENGTH
            This is a contradiction.
         Step: !q. (LENGTH p = LENGTH q) ==> (p || q = MAP2 f p q) ==>
               (LENGTH (h::p) = LENGTH (h'::q)) ==> ((h::p) || (h'::q) = MAP2 f (h::p) (h'::q))
            Note LENGTH (h::p) = LENGTH (h'::q)
             ==> SUC (LENGTH p) = SUC (LENGTH q)   by LENGTH
              or      LENGTH p = LENGTH q          by SUC_EQ
            Also h IN R /\ weak p                  by weak_cons
             and h' IN R /\ weak q                 by weak_cons
              (h::p) || (h'::q)
            = (h + h') :: (p || q)                 by weak_add_cons
            = (h + h') :: MAP2 f p q               by induction hypothesis
            = (f h h') :: MAP2 f p q               by notation
            = MAP2 f (h::p) (h'::q)                by MAP2
*)
val weak_add_map2 = store_thm(
  "weak_add_map2",
  ``!r:'a ring. !p q. weak p /\ weak q /\ (LENGTH p = LENGTH q) ==>
      (p || q = MAP2 (\x y. x + y) p q)``,
  strip_tac >>
  Induct >| [
    rpt strip_tac >>
    `q = []` by metis_tac[LENGTH_NIL] >>
    rw[],
    strip_tac >>
    Induct >>
    rw[]
  ]);

(* Theorem: j < LENGTH p /\ j < LENGTH q ==> EL j (p || q) = (EL j p) + (EL j q) *)
(* Proof:
   By induction on p.
   Base: !q j. j < LENGTH [] /\ j < LENGTH q ==> EL j ([] || q) = EL j [] + EL j q
       This is true by j < 0 = F        by LENGTH
   Step: !q j. j < LENGTH p /\ j < LENGTH q ==> EL j (p || q) = EL j p + EL j q ==>
         !h q j. j < LENGTH (h::p) /\ j < LENGTH q ==> EL j ((h::p) || q) = EL j (h::p) + EL j q
       If q = [], true b j < 0 = F      by LENGTH
       Let q = k::s.
       Note j < SUC (LENGTH p).
       If j = 0,
            EL 0 ((h::p) || (k::s))
          = EL 0 (h + k::p || s)        by weak_add_cons
          = h + k                       by EL
          = EL 0 (h::p) + EL 0 (k::s)   by EL
       Otherwise, j = SUC n  for some n, with n < LENGTH p.
            EL (SUC n) ((h::p) || (k::s))
          = EL (SUC n) (h + k::p || s)  by weak_add_cons
          = EL n (p || s)               by EL
          = EL n p + EL n s             by induction hypothesis, n < LENGTH p, n < LENGTH s
          = EL (SUC n) (h::p) + EL (SUC n) (k::s)   by EL
          = EL j (h::p) + EL j (k::s)               by j = SUC n
*)
val weak_add_element = store_thm(
  "weak_add_element",
  ``!r:'a ring p q j. j < LENGTH p /\ j < LENGTH q ==>
      (EL j (p || q) = (EL j p) + (EL j q))``,
  strip_tac >>
  Induct >-
  rw[] >>
  (Cases_on `q` >> rw[]) >>
  (Cases_on `j` >> rw[]));

(* Theorem: p <> |0| /\ q <> |0| /\ (LENGTH p = LENGTH q) ==>
           (LAST (p || q) = LAST p + LAST q) *)
(* Proof:
   Let k = LENGTH p,
   Note LENGTH (p || q) = k           by weak_add_length
   Thus p || q <> []                  by LENGTH_NIL
   Since 0 < k, let j = PRE k, then j < k.
   Note p <> [] /\ q <> []            by poly_zero
       LAST (p || q)
     = EL j (p || q)                  by LAST_EL
     = EL j p + EL j q                by weak_add_element
     = LAST p + LAST q                by LAST_EL
*)
val weak_add_last = store_thm(
  "weak_add_last",
  ``!r:'a ring p q. p <> |0| /\ q <> |0| /\ (LENGTH p = LENGTH q) ==>
           (LAST (p || q) = LAST p + LAST q)``,
  rw[] >>
  qabbrev_tac `k = LENGTH p` >>
  `LENGTH (p || q) = k` by rw[weak_add_length, Abbr`k`] >>
  `k <> 0 /\ (p || q) <> []` by metis_tac[LENGTH_NIL] >>
  rw[weak_add_element, LAST_EL]);

(* Theorem: p <> |0| /\ q <> |0| /\ (LENGTH p = LENGTH q) ==>
           (FRONT (p || q) = (FRONT p) || (FRONT q)) *)
(* Proof:
   Let k = LENGTH p.
   Note LENGTH (p || q) = k                     by weak_add_length
      or p || q <> []                           by LENGTH_NIL
   Since 0 < k, let j = PRE k.
   Then LENGTH (FRONT p) = j                    by FRONT_LENGTH
        LENGTH (FRONT q) = j                    by FRONT_LENGTH
    and LENGTH (FRONT (p || q)) = j             by weak_add_length
    Let x < j,
       EL x (FRONT (p || q))
     = EL x (p || q)                            by FRONT_EL, (p || q <> [])
     = EL x p + EL x q                          by weak_add_element
     = EL x (FRONT p) + EL x (FRONT q)          by FRONT_EL, p <> [], q <> []
     = EL x (FRONT p || FRONT q)                by weak_add_element
   Thus FRONT (p || q) = FRONT p || FRONT q     by LIST_EQ
*)
val weak_add_front = store_thm(
  "weak_add_front",
  ``!r:'a ring p q. p <> |0| /\ q <> |0| /\ (LENGTH p = LENGTH q) ==>
           (FRONT (p || q) = (FRONT p) || (FRONT q))``,
  rw[] >>
  qabbrev_tac `k = LENGTH p` >>
  `LENGTH (p || q) = k` by rw[weak_add_length, Abbr`k`] >>
  `k <> 0 /\ p || q <> []` by metis_tac[LENGTH_NIL] >>
  qabbrev_tac `j = PRE k` >>
  `LENGTH (FRONT p) = j` by rw[FRONT_LENGTH, Abbr`j`] >>
  `LENGTH (FRONT q) = j` by rw[FRONT_LENGTH, Abbr`j`] >>
  `LENGTH (FRONT (p || q)) = j` by metis_tac[FRONT_LENGTH] >>
  `LENGTH (FRONT p || FRONT q) = j` by rw[weak_add_length] >>
  irule LIST_EQ >>
  simp[] >>
  rpt strip_tac >>
  `j < k` by rw[Abbr`j`] >>
  `x < k` by decide_tac >>
  rw[FRONT_EL, weak_add_element]);

(* ------------------------------------------------------------------------- *)
(* Weak Polynomial Scalar Multiplication                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: c o [] = []  *)
(* Proof: by definitions. *)
val weak_cmult_of_zero = save_thm("weak_cmult_of_zero", weak_cmult_def |> CONJUNCT1);
(* > val weak_cmult_of_zero = |- !r c. c o [] = [] : thm *)

(* Theorem: c o (h::t) = c * h::c o t  *)
(* Proof: by definition. *)
val weak_cmult_cons = save_thm("weak_cmult_cons", weak_cmult_def |> CONJUNCT2);
(* > val weak_cmult_cons = |- !r c h t. c o (h::t) = c * h::c o t : thm *)

(* definition exported already *)
(* val _ = export_rewrites ["weak_cmult_of_zero", "weak_cmult_cons"]; *)

(* Theorem: Polynomial scalar multiplication clauses. *)
(* Proof: by theorems proved. *)
val weak_cmult_clauses = store_thm(
  "weak_cmult_clauses",
  ``!r:'a ring. !c. (c o [] = []) /\ !h t. c o (h::t) = c * h::c o t``,
  rw[]);

(* Theorem: c o |0| = |0| *)
(* Proof: by weak_cmult_of_zero and poly_zero. *)
val weak_cmult_zero = save_thm("weak_cmult_zero", weak_cmult_of_zero |> REWRITE_RULE [GSYM poly_zero]);
(* > val weak_cmult_zero = |- !r c. c o |0| = |0| : thm *)

val _ = export_rewrites ["weak_cmult_zero"];

(* Theorem: c o p = MAP (\x. c * x) p *)
(* Proof: by induction on p.
   Base: c o [] = MAP (\x. c * x) []
         c o []
       = []                           by weak_cmult_zero
       = MAP f []                     by MAP
   Step: c o p = MAP (\x. c * x) p ==> c o (h::p) = MAP (\x. c * x) (h::p)
         c o (h::p)
       = c * h :: c o p               by weak_cmult_cons
       = c * h :: MAP (\x. c * x) p   by induction hypothesis
       = MAP (\x. c * x) (h::p)       by MAP
*)
val weak_cmult_map = store_thm(
  "weak_cmult_map",
  ``!r:'a ring. !(c:'a) p. c o p = MAP (\x. c * x) p``,
  ntac 2 strip_tac >>
  Induct >>
  rw[]);

(* Theorem: LENGTH (c o p) = LENGTH p *)
(* Proof:
     LENGTH (c o p)
   = LENGTH (MAP (\x. c * x) p)    by weak_cmult_map
   = LENGTH p                      by LENGTH_MAP
*)
val weak_cmult_length = store_thm(
  "weak_cmult_length",
  ``!r:'a ring. !(c:'a) p. LENGTH (c o p) = LENGTH p``,
  rw[weak_cmult_map]);

(* Theorem: c o p = [] <=> p = [] *)
(* Proof:
       c o p = []
   <=> LENGTH (c o p) = 0    by LENGTH_NIL
   <=> LENGTH p = 0          by weak_cmult_length
   <=> p = []                by LENGTH_NIL
*)
val weak_cmult_eq_of_zero = store_thm(
  "weak_cmult_eq_of_zero",
  ``!r:'a ring. !(c:'a) p. (c o p = []) <=> (p = [])``,
  metis_tac[weak_cmult_length, LENGTH_NIL]);

(* Theorem: c o p = |0| <=> p = |0| *)
(* Proof: by weak_cmult_eq_of_zero and poly_zero. *)
val weak_cmult_eq_zero = save_thm("weak_cmult_eq_zero", weak_cmult_eq_of_zero |> REWRITE_RULE [GSYM poly_zero]);
(* > val weak_cmult_eq_zero = |- !r c p. (c o p = |0|) <=> (p = |0|): thm *)

(* Theorem: LENGTH q <= LENGTH p ==> (LENGTH (h o p || q) = LENGTH p) *)
(* Proof:
       LENGTH (h o p || q)
     = MAX (LENGTH (h o p)) (LENGTH q)   by weak_add_length
     = MAX (LENGTH p) (LENGTH q)         by weak_cmult_length
     = LENGTH p = k                      by MAX_DEF, LENGTH q <= LENGTH p
*)
val weak_cmult_add_length = store_thm(
  "weak_cmult_add_length",
  ``!r:'a ring. !(h:'a) (p q):'a poly. LENGTH q <= LENGTH p ==> (LENGTH (h o p || q) = LENGTH p)``,
  rw[weak_add_length, weak_cmult_length, MAX_DEF]);

(* Theorem: c o (SNOC h t) = SNOC (c * h) (c o t) *)
(* Proof:
     c o (SNOC h t)
   = MAP (\x. c * x) (SNOC h t)                by weak_cmult_map
   = SNOC ((\x. c * x) h) (MAP (\x. c * x) t)  by MAP_SNOC
   = SNOC (c * h) (c o t)                      by weak_cmult_map, applying function.
*)
val weak_cmult_snoc = store_thm(
  "weak_cmult_snoc",
  ``!r:'a ring. !c:'a h t. c o (SNOC h t) = SNOC (c * h) (c o t)``,
  rw_tac std_ss[weak_cmult_map, MAP_SNOC]);

(* Theorem: p <> |0| ==> (c o FRONT p = FRONT (c o p)) /\ (c * LAST p = LAST (c o p)) *)
(* Proof:
     c o p
   = MAP (\x. c * x) p                          by weak_cmult_map
   = MAP (\x. c * x) (SNOC (LAST p) (FRONT p))  by SNOC_LAST_FRONT
   = SNOC (\x. c * x) (LAST p) (MAP (\x. c * x) (FRONT p))
                                                by MAP_SNOC
   = SNOC (c * LAST p) (c o FRONT p)            by weak_cmult_map
  Thus FRONT (c o p) = c o FRONT p              by FRONT_SNOC
   and LAST (c o p) = c * LAST p                by LAST_SNOC
*)
val weak_cmult_front_last = store_thm(
  "weak_cmult_front_last",
  ``!r:'a ring. !c:'a p. p <> |0| ==>
       (c o FRONT p = FRONT (c o p)) /\ (c * LAST p = LAST (c o p))``,
  ntac 4 strip_tac >>
  qabbrev_tac `f = \(x:'a). c * x` >>
  `c o p = MAP f p` by rw[weak_cmult_map, Abbr`f`] >>
  `_ = MAP f (SNOC (LAST p) (FRONT p))` by metis_tac[SNOC_LAST_FRONT, poly_zero] >>
  `_ = SNOC (f (LAST p)) (MAP f (FRONT p))` by rw[MAP_SNOC] >>
  `_ = SNOC (c * LAST p) (c o FRONT p)` by rw[weak_cmult_map, weak_front_last, Abbr`f`] >>
  rw[]);

(* Others proofs of the same result by element *)

(* Theorem: j < LENGTH p ==> EL j (c o p) = c * (EL j p) *)
(* Proof:
   Note LENGTH (c o p) = LENGTH p   by weak_cmult_length
     EL j (c o p)
   = EL j (MAP (\x. c * x) p)       by weak_cmult_map
   = c * (EL j p)                   by EL_MAP
*)
val weak_cmult_element = store_thm(
  "weak_cmult_element",
  ``!r:'a ring c:'a p j. j < LENGTH p ==> (EL j (c o p) = c * EL j p)``,
  rw[weak_cmult_length, weak_cmult_map, EL_MAP]);

(* Theorem: p <> |0| ==> (LAST (c o p) = c * LAST p) *)
(* Proof:
   Let k = LENGTH p.
   Note LENGTH (c o p) = k  by weak_cmult_length
   Thus c o p <> []         by LENGTH_NIL
   Since 0 < k, let j = PRE k, then j < k.
   Note p <> []             by poly_zero
       LAST (c o p)
     = EL j p               by LAST_EL
     = c * EL j p           by weak_cmult_element
     = c * LAST p           by LAST_EL
*)
val weak_cmult_last = store_thm(
  "weak_cmult_last",
  ``!r:'a ring c:'a p. p <> |0| ==> (LAST (c o p) = c * LAST p)``,
  rw[] >>
  qabbrev_tac `k = LENGTH p` >>
  qabbrev_tac `j = PRE k` >>
  `LENGTH (c o p) = k` by rw[weak_cmult_length, Abbr`k`] >>
  `k <> 0 /\ c o p <> []` by metis_tac[LENGTH_NIL] >>
  `j < k` by rw[Abbr`j`] >>
  rw[LAST_EL, weak_cmult_element]);

(* Theorem: p <> |0| ==> (FRONT (c o p) = c o FRONT p) *)
(* Proof:
   Let k = LENGTH p.
   Note LENGTH (c o p) = k                      by weak_cmult_length
      or c o p <> []                            by LENGTH_NIL
   Since 0 < k, let j = PRE k.
   Then LENGTH (FRONT p) = j                    by FRONT_LENGTH
    and LENGTH (FRONT (c o p)) = j              by weak_cmult_length
    Let x < j,
       EL x (FRONT (c o p))
     = EL x (c o p)                             by FRONT_EL, (c o p <> [])
     = c * EL x q                               by weak_cmult_element
     = c * EL x (FRONT p)                       by FRONT_EL, p <> []
     = EL x (c o FRONT p)                       by weak_cmult_element
   Thus FRONT (c o p) = c o FRONT p             by LIST_EQ
*)
val weak_cmult_front = store_thm(
  "weak_cmult_front",
  ``!r:'a ring c:'a p. p <> |0| ==> (FRONT (c o p) = c o FRONT p)``,
  rw[] >>
  qabbrev_tac `k = LENGTH p` >>
  `LENGTH (c o p) = k` by rw[weak_cmult_length, Abbr`k`] >>
  `k <> 0 /\ c o p <> []` by metis_tac[LENGTH_NIL] >>
  qabbrev_tac `j = PRE k` >>
  `LENGTH (FRONT p) = j` by rw[FRONT_LENGTH, Abbr`j`] >>
  `LENGTH (FRONT (c o p)) = j` by metis_tac[FRONT_LENGTH] >>
  `LENGTH (c o FRONT p) = j` by rw[weak_cmult_length] >>
  irule LIST_EQ >>
  simp[] >>
  rpt strip_tac >>
  `j < k` by rw[Abbr`j`] >>
  `x < k` by decide_tac >>
  rw[FRONT_EL, weak_cmult_element]);

(* Theorem: weak p ==> weak (c o p) *)
(* Proof: by induction on p.
   Base: weak [] ==> !c::(R). weak (c o [])
     true by weak_cmult_of_zero
   Step: weak p ==> !c::(R). weak (c o p) ==> !h. weak (h::p) ==> !c::(R). weak (c o (h::p))
     weak (c o (h::p))
   = weak (c * h :: c o p)   by weak_cmult_cons
   = T                       by ring_mult_element, induction hypothesis
*)
val weak_cmult_weak = store_thm(
  "weak_cmult_weak",
  ``!r:'a ring. Ring r ==> !p. weak p ==> !c. c IN R ==> weak (c o p)``,
  strip_tac >>
  strip_tac >>
  Induct >>
  rw[]);

val _ = export_rewrites ["weak_cmult_weak"];

(* Theorem: c o (p || q) = c o p || c o q *)
(* Proof: by induction on p and q, and ring_mult_radd.
   Base: !q. weak [] /\ weak q ==> !c::(R). c o ([] || q) = c o [] || c o q
      LHS = c o ([] || q)
          = c o q               by weak_add_of_lzero
      RHS = c * [] || c o q
          = [] || c o q         by weak_cmult_of_zero
          = c o q               by weak_add_of_lzero
          = LHS.
   Step: induct on q.
      Base:  weak (h::p) /\ weak [] ==> !c::(R). c o ((h::p) || []) = c o (h::p) || c o []
         LHS = c o ((h::p) || [])
             = c o (h::p)          by weak_add_of_rzero
         RHS = c o (h::p) || c o []
             = c o (h::p) || []    by weak_cmult_of_zero
             = c o (h::p)          by weak_add_of_rzero
             = LHS.
      Step: !q. weak p /\ weak q ==> !c::(R). c o (p || q) = c o p || c o q ==>
                 !h'. weak (h::p) /\ weak (h'::q) ==> !c::(R). c o ((h::p) || (h'::q)) = c o (h::p) || c o (h'::q)
        c o ((h::p) || (h'::q))
      = c o (h + h' :: p || q)                     by weak_add_cons
      = c * (h + h') :: c o (p || q)               by weak_cmult_cons
      = (c * h + c * h')::(c o p || c o q)         by ring_mult_radd, induction hypothesis
      = ((c * h)::(c o p)) || ((c * h')::(c o q))  by weak_add_cons
      = c o (h::p) || c o (h'::q)                  by weak_cmult_cons
*)
val weak_cmult_add = store_thm(
  "weak_cmult_add",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q ==>
    !c. c IN R ==> (c o (p || q) = c o p || c o q)``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  strip_tac >>
  Induct >>
  rw[]);

(* Theorem: (b + c) o p = b o p || c o p  *)
(* Proof: by induction on p, and ring_distrib_ladd.
   Base: weak [] ==> !b c::(R). (b + c) o [] = b o [] || c o []
      true by weak_cmult_of_zero, weak_add_of_zero_zero
   Step: weak p ==> !b c::(R). (b + c) o p = b o p || c o p ==>
              !h. weak (h::p) ==> !b c::(R). (b + c) o (h::p) = b o (h::p) || c o (h::p)
      (b + c) o (h::p)
    = ((b + c)*h :: (b + c) o p)         by weak_cmult_cons
    = ((b + c)*h :: b o p || c o p)      by induction hypothesis
    = (b*h + c*h) :: (b o p || c o p)    by ring_distrib_ladd
    = (b*h :: b o p) || (c*h :: c o p)   by weak_add_cons
    = b o (h::p) || c o (h::p)           by weak_cmult_cons
*)
val weak_add_cmult = store_thm(
  "weak_add_cmult",
  ``!r:'a ring. Ring r ==> !p. weak p ==> !b c. b IN R /\ c IN R ==> ((b + c) o p = b o p || c o p)``,
  strip_tac >>
  strip_tac >>
  Induct >>
  rw[]);

(* Theorem: b o (c o p) = (b * c) o p  *)
(* Proof: by induction on p and ring_mult_assoc.
   Base:weak [] ==> !b c::(R). b o c o [] = (b * c) o []
      true by weak_cmult_of_zero.
   Step: weak p ==> !b c::(R). b o c o p = (b * c) o p
              !h. weak (h::p) ==> !b c::(R). b o c o (h::p) = (b * c) o (h::p)
     b o (c o (h::p))
   = b o ((c * h)::(c o p))         by weak_cmult_cons
   = (b * (c * h))::(b o (c o p))   by weak_cmult_cons
   = ((b * c) * h)::(b o (c o p))   by ring_mult_assoc
   = ((b * c) * h)::((b * c) o p)   by induction hypothesis
   = (b * c) o (h::p)               by weak_cmult_cons
*)
val weak_cmult_cmult = store_thm(
  "weak_cmult_cmult",
  ``!r:'a ring. Ring r ==> !p:'a poly. weak p ==> !b c. b IN R /\ c IN R ==> (b o (c o p) = (b * c) o p)``,
  strip_tac >>
  strip_tac >>
  Induct >>
  rw[ring_mult_assoc]);

(* Theorem: b o (c o p) = c o (b o p)  *)
(* Proof: by weak_cmult_cmult and ring_mult_comm.
     b o (c o p)
   = (b * c) o p      by weak_cmult_cmult
   = (c * b) o p      by ring_mult_comm
   = c o (b o p)      by weak_cmult_cmult
*)
val weak_cmult_cmult_comm = store_thm(
  "weak_cmult_cmult_comm",
  ``!r:'a ring. Ring r ==> !p:'a poly. weak p ==> !b c. b IN R /\ c IN R ==> (b o (c o p) = c o (b o p))``,
  rw_tac std_ss[ring_mult_comm, weak_cmult_cmult]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Negation.                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: neg [] = [] *)
(* Proof: by definition. *)
val weak_neg_of_zero = save_thm("weak_neg_of_zero", weak_neg_def |>  CONJUNCT1);
(* > val weak_neg_of_zero = |- !r. neg [] = [] : thm *)

(* Theorem: neg (h::t) = (- h) :: (neg t)  *)
val weak_neg_cons = save_thm("weak_neg_cons", weak_neg_def |> CONJUNCT2);
(* > val weak_neg_cons = |- !r h t. neg (h::t) = -h::neg t : thm *)

(* definition already exported *)
(* val _ = export_rewrites ["weak_neg_of_zero", "weak_neg_cons"]; *)

(* Theorem: Polynomial negation clauses. *)
(* Proof: by theorems proved. *)
val weak_neg_clauses = store_thm(
  "weak_neg_clauses",
  ``!r:'a ring. (neg [] = []) /\ !h t. neg (h::t) = -h::neg t``,
  rw[]);
(* better than:
val weak_neg_clauses = save_thm("weak_neg_clauses", CONJ weak_neg_of_zero weak_neg_cons);
> val weak_neg_clauses = |- (!r. -[] = []) /\ !r h t. -(h::t) = -h::-t : thm
*)

(* Theorem: neg |0| = |0| *)
(* Proof: by weak_neg_of_zero and poly_zero. *)
val weak_neg_zero = save_thm("weak_neg_zero", weak_neg_of_zero |> REWRITE_RULE [GSYM poly_zero]);
(* > val weak_neg_zero = |- !r. neg |0| = |0| : thm *)

val _ = export_rewrites ["weak_neg_zero"];

(* Theorem: neg p = MAP (\x. -x) p *)
(* Proof: by induction on p.
   Base: neg [] = MAP (\x. -x) []
      true by weak_neg_of_zero.
   Step: neg p = MAP (\x. -x) p ==> !h. neg (h::p) = MAP (\x. -x) (h::p)
      true by weak_neg_cons, poly_cons_poly.
*)
val weak_neg_map = store_thm(
  "weak_neg_map",
  ``!r:'a ring p. neg p = MAP (\x. -x) p``,
  strip_tac >>
  Induct >>
  rw[]);

(* Theorem: LENGTH (neg p) = LENGTH p *)
(* Proof:
      LENGTH (neg p)
    = LENGTH (MAP (\x. -x) p)   by weak_neg_map
    = LENGTH p                  by LENGTH_MAP
*)
val weak_neg_length = store_thm(
  "weak_neg_length",
  ``!r:'a ring p. LENGTH (neg p) = LENGTH p``,
  rw[weak_neg_map]);

(* Theorem: neg p = [] <=> p = [] *)
(* Proof:
       neg p = []
   <=> LENGTH (neg p) = 0      by LENGTH_NIL
   <=> LENGTH p = 0            by weak_neg_length
   <=> p = []                  by LENGTH_NIL
*)
val weak_neg_eq_of_zero = store_thm(
  "weak_neg_eq_of_zero",
  ``!r:'a ring p. (neg p = []) <=> (p = [])``,
  metis_tac[weak_neg_length, LENGTH_NIL]);

(* Theorem: neg p = |0| <=> p = |0| *)
(* Proof: by weak_neg_eq_of_zero and poly_zero. *)
val weak_neg_eq_zero = save_thm("weak_neg_eq_zero", weak_neg_eq_of_zero |> REWRITE_RULE [GSYM poly_zero]);
(* > val weak_neg_eq_zero = |- !r p. (neg p = |0|) <=> (p = |0|): thm *)

(* Theorem: neg (neg p) = p *)
(* Proof: by induction on p, and ring_neg_neg.
   Base: neg (neg []) = |0
      true by weak_neg_of_zero.
   Step: neg (neg p) = p ==> !h. neg (neg (h::p)) = h::p
     neg (neg (h::p))
   = neg (-h::neg p)     by weak_neg_cons
   = - -h::neg (neg p)   by weak_neg_cons
   = h::neg (neg p)      by ring_neg_neg
   = h::p                by induction hypothesis
*)
val weak_neg_neg = store_thm(
  "weak_neg_neg",
  ``!r:'a ring. Ring r ==> !p:'a poly. weak p ==> (neg (neg p) = p)``,
  strip_tac >>
  strip_tac >>
  Induct >>
  rw[]);

val _ = export_rewrites ["weak_neg_neg"];

(* Theorem: weak p ==> weak (neg p) *)
(* Proof: by induction on p and ring_neg_element.
   Base: weak [] ==> weak (neg [])
      true by weak_neg_of_zero.
   Step: weak p ==> weak (neg p) ==>
              !h. weak (h::p) ==> weak (neg (h::p))
       weak (h::p)
   <=> h IN R /\ weak p          by weak_cons
   ==> -h IN R /\ weak p         by ring_neg_element
   ==> -h IN R /\ weak (neg p)   by induction hypothesis
   ==> weak (-h :: neg p)        by weak_cons
   ==> weak (neg (h::p))         by weak_neg_cons
*)
val weak_neg_weak = store_thm(
  "weak_neg_weak",
  ``!r:'a ring. Ring r ==> !p:'a poly. weak p ==> weak (neg p)``,
  strip_tac >>
  strip_tac >>
  Induct >>
  rw[]);

val _ = export_rewrites ["weak_neg_weak"];

(* Theorem: c o neg p = (- c) o p *)
(* Proof: by induction on p.
   Base: weak [] ==> c o neg [] = -c o []
      true by weak_neg_of_zero, weak_cmult_of_zero
   Step: weak p ==> c o neg p = -c o p ==>
              !h. weak (h::p) ==> c o neg (h::p) = -c o (h::p)
     c o neg (h::p)
   = c o (-h::neg p)          by weak_neg_cons
   = (c * -h)::(c o neg p)    by weak_cmult_cons
   = (- c * h):: (c o neg p)  by ring_mult_lneg, ring_mult_rneg
   = (- c * h):: (- c o p)    by induction hypothesis
   = - c o (h::p)             by weak_cmult_cons
*)
val weak_cmult_neg = store_thm(
  "weak_cmult_neg",
  ``!r:'a ring. Ring r ==> !p:'a poly. weak p ==> !c. c IN R ==> (c o neg p = (- c) o p)``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  rw_tac std_ss[ring_mult_lneg, ring_mult_rneg, weak_neg_cons, weak_cmult_cons, weak_cons]);

(* Theorem: neg (c o p) = (- c) o p *)
(* Proof: by induction on p.
   Base: weak [] ==> neg (c o []) = -c o []
      true by weak_cmult_of_zero, weak_neg_of_zero
   Step: weak p ==> neg (c o p) = -c o p ==>
              !h. weak (h::p) ==> neg (c o (h::p)) = -c o (h::p)
        neg (c o (h::p))
      = neg (c * h :: c o p)    by weak_cmult_cons
      = -(c * h):: neg (c o p)  by weak_neg_cons
      = -(c * h):: -c o p       by induction hypothesis
      = -c * h :: -c o p        by ring_mult_lneg
      = -c o (h::p)             by weak_cmult_cons
*)
val weak_neg_cmult = store_thm(
  "weak_neg_cmult",
  ``!r:'a ring. Ring r ==> !p:'a poly. weak p ==> !c. c IN R ==> (neg (c o p) = (- c) o p)``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  rw_tac std_ss[ring_mult_lneg, weak_neg_cons, weak_cmult_cons, weak_cons]);

val _ = export_rewrites ["weak_cmult_neg", "weak_neg_cmult"];

(* Theorem:  j < LENGTH p ==> (EL j (neg p) = - (EL j p)) *)
(* Proof:
   Note LENGTH (neg p) = LENGTH p   by weak_neg_length
     EL j (neg p)
   = EL j (MAP (\x. -x) p)          by weak_neg_map
   = - (EL j p)                     by EL_MAP
*)
val weak_neg_element = store_thm(
  "weak_neg_element",
  ``!r:'a ring p j. j < LENGTH p ==> (EL j (neg p) = - (EL j p))``,
  rw[weak_neg_length, weak_neg_map, EL_MAP]);

(* Theorem: p <> |0| ==> LAST (neg p) = - LAST p *)
(* Proof:
   Let k = LENGTH p.
   Note LENGTH (neg p) = k  by weak_neg_length
   Thus neg p <> []         by LENGTH_NIL
   Since 0 < k, let j = PRE k, then j < k.
   Note p <> []             by poly_zero
       LAST (neg p)
     = EL j p               by LAST_EL
     = - EL j p             by weak_neg_element
     = = LAST p             by LAST_EL
*)
val weak_neg_last = store_thm(
  "weak_neg_last",
  ``!r:'a ring p. p <> |0| ==> (LAST (neg p) = - LAST p)``,
  rw[] >>
  qabbrev_tac `k = LENGTH p` >>
  qabbrev_tac `j = PRE k` >>
  `LENGTH (neg p) = k` by rw[weak_neg_length, Abbr`k`] >>
  `k <> 0 /\ neg p <> []` by metis_tac[LENGTH_NIL] >>
  `j < k` by rw[Abbr`j`] >>
  rw[LAST_EL, weak_neg_element]);

(* Theorem: p <> |0| ==> FRONT (neg p) = neg (FRONT p) *)
(* Proof:
   Let k = LENGTH p.
   Note LENGTH (neg p) = k                      by weak_neg_length
      or neg p <> []                            by LENGTH_NIL
   Since 0 < k, let j = PRE k.
   Then LENGTH (FRONT p) = j                    by FRONT_LENGTH
    and LENGTH (FRONT (neg p)) = j              by weak_neg_length
    Let x < j,
       EL x (FRONT (neg p))
     = EL x (neg p)                             by FRONT_EL, (neg p <> [])
     = - EL x q                                 by weak_neg_element
     = - EL x (FRONT p)                         by FRONT_EL, p <> []
     = EL x (neg (FRONT p))                     by weak_neg_element
   Thus FRONT (neg p) = neg (FRONT p)           by LIST_EQ
*)
val weak_neg_front = store_thm(
  "weak_neg_front",
  ``!r:'a ring p. p <> |0| ==> (FRONT (neg p) = neg (FRONT p))``,
  rw[] >>
  qabbrev_tac `k = LENGTH p` >>
  `LENGTH (neg p) = k` by rw[weak_neg_length, Abbr`k`] >>
  `k <> 0 /\ neg p <> []` by metis_tac[LENGTH_NIL] >>
  qabbrev_tac `j = PRE k` >>
  `LENGTH (FRONT p) = j` by rw[FRONT_LENGTH, Abbr`j`] >>
  `LENGTH (FRONT (neg p)) = j` by metis_tac[FRONT_LENGTH] >>
  `LENGTH (neg (FRONT p)) = j` by rw[weak_neg_length] >>
  irule LIST_EQ >>
  simp[] >>
  rpt strip_tac >>
  `j < k` by rw[Abbr`j`] >>
  `x < k` by decide_tac >>
  rw[FRONT_EL, weak_neg_element]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Turn                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem alias *)
val turn_eq_of_zero = save_thm("turn_eq_of_zero", turn_eq_nil);

(* Obtain theorem *)
val turn_eq_zero = save_thm("turn_eq_zero", turn_eq_of_zero |> REWRITE_RULE [GSYM poly_zero]);
(* val turn_eq_zero = |- !p. (turn p = |0|) <=> (p = |0|): thm *)

(* Theorem: weak p ==> weak (turn p) *)
(* Proof:
   If p = [],
      Then turn [] = []      by turn_def
       and weak [] = T       by weak_of_zero
   If p <> [],
      Then turn p = (LAST p) :: (FRONT p)   by turn_def
      Note (LAST p) IN R                    by weak_last_element
       and weak (FRONT p)                   by weak_front_last
        so weak (turn p)                    by weak_cons
*)
val weak_turn = store_thm(
  "weak_turn",
  ``!r:'a ring. !p. weak p ==> weak (turn p)``,
  rw[turn_def, weak_front_last, weak_last_element]);

(* Theorem: weak p ==> !n. weak (turn_exp p n) *)
(* Proof:
   By induction on n.
   Base: weak (turn_exp p 0)
      Note turn_exp p 0 = p        by turn_exp_0
       and weak p = T              by given
   Step: weak (turn_exp p n) ==> weak (turn_exp p (SUC n))
      Note turn_exp p (SUC n)
         = turn (turn_exp p n)            by turn_exp_suc
       Now weak (turn_exp p n)            by induction hypothesis
        so weak (turn (turn_exp p n))     by weak_turn
*)
val weak_turn_exp = store_thm(
  "weak_turn_exp",
  ``!r:'a ring. !p. weak p ==> !n. weak (turn_exp p n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw[turn_exp_suc, weak_turn]);

(* Theorem: (LENGTH p = LENGTH q) ==> (turn (p || q) = (turn p) || (turn q)) *)
(* Proof:
   If p = [],
         turn ([] || q)
       = turn q                     by weak_add_zero
       = [] || turn q               by weak_add_zero
       = turn [] || turn q          by turn_nil
   If q = [],
         turn (p || [])
       = turn p                     by weak_add_zero
       = turn p || []               by weak_add_zero
       = turn p || turn []          by turn_nil
   Otherwise, p <> [] and q <> [].
      Then p || q <> []             by weak_add_eq_zero, poly_zero
         turn (p || q)
       = LAST (p || q) :: FRONT (p || q)             by turn_def
       = (LAST p + LAST q) :: (FRONT p || FRONT q)   by weak_add_last, weak_add_front
       = (LAST p :: FRONT p) || (LAST q :: FRONT q)  by weak_add_cons
       = turn p || turn q                            by turn_def

Picture:      turn (p || q)
            = turn ( [p0 p1 ... pn] || [q0 q1 ... qn])
            = turn [p0 + q0, p1 + q1, ...., pn + qn]
            = [pn + qn, p0 + q0, p1 + q1, ....]
            = [pn p0 p1 ...] || [qn q0 q1 ...]
            = (turn p) || (turn q)

This picture holds only for lists of the same length:
> EVAL ``turn (weak_add (ZN 10) [1;2] [3;4;5])``; = [5; 4; 6]: thm
> EVAL ``weak_add (ZN 10) (turn [1;2]) (turn [3;4;5])``; = [7; 4; 4]: thm
*)
val weak_add_turn = store_thm(
  "weak_add_turn",
  ``!r:'a ring p q. (LENGTH p = LENGTH q) ==> (turn (p || q) = (turn p) || (turn q))``,
  rpt strip_tac >>
  (Cases_on `p = []` >> rw[turn_nil]) >>
  (Cases_on `q = []` >> rw[turn_nil]) >>
  `p || q <> []` by metis_tac[weak_add_eq_zero, poly_zero] >>
  `turn (p || q) = LAST (p || q) :: FRONT (p || q)` by rw[turn_def] >>
  `_ = (LAST p + LAST q) :: (FRONT p || FRONT q)` by rw[weak_add_last, weak_add_front] >>
  `_ = (LAST p :: FRONT p) || (LAST q :: FRONT q)` by rw[] >>
  `_ = turn p || turn q` by rw[turn_def] >>
  rw[]);

(* Theorem: turn (c o p) = c o turn p *)
(* Proof:
   If p = [],
        turn (c o [])
      = turn []                       by weak_cmult_zero
      = []                            by turn_nil
      = c o []                        by weak_cmult_zero
      = c o turn []                   by turn_nil
   If p <> [],
      Then c o p <> []                by weak_cmult_eq_zero
      turn (c o p)
    = LAST (c o p) :: FRONT (c o p)   by turn_def
    = (c * LAST p)::(c o FRONT p)     by weak_cmult_last, weak_cmult_front
    = c o (LAST p :: FRONT p)         by weak_cmult_cons
    = c o turn p                      by turn_def
*)
val weak_cmult_turn = store_thm(
  "weak_cmult_turn",
  ``!r:'a ring c:'a p. turn (c o p) = c o turn p``,
  rpt strip_tac >>
  (Cases_on `p = []` >> rw[turn_nil]) >>
  rw[turn_def, weak_cmult_cons, weak_cmult_last, weak_cmult_front] >>
  metis_tac[weak_cmult_eq_zero, poly_zero]);

(* Theorem: !n. (c o (turn_exp p n) = turn_exp (c o p) n) *)
(* Proof:
   By induction on n.
   Base: c o turn_exp p 0 = turn_exp (c o p) 0
         c o turn_exp p 0
       = c o p                        by turn_exp_0
       = turn (c o p) 0               by turn_exp_0
   Step: c o turn_exp p n = turn_exp (c o p) n ==>
         c o turn_exp p (SUC n) = turn_exp (c o p) (SUC n)
         c o turn_exp p (SUC n)
       = c o turn (turn_exp p n)      by turn_exp_suc
       = turn (c o (turn_exp p n))    by weak_cmult_turn
       = turn (turn_exp (c o p) n)    by induction hypothesis
       = turn_exp (c o p) n (SUC n)   by turn_exp_suc
*)
val weak_cmult_turn_exp = store_thm(
  "weak_cmult_turn_exp",
  ``!r:'a ring p c:'a n. (c o (turn_exp p n) = turn_exp (c o p) n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  metis_tac[turn_exp_suc, weak_cmult_turn, weak_turn_exp]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Shifts                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: p >> 0 = p *)
(* Proof: by definition. *)
val poly_shift_0 = store_thm(
  "poly_shift_0",
  ``!p:'a poly. p >> 0 = p``,
  metis_tac[poly_shift_def, list_CASES]);

(* Theorem: p >> SUC n = if p = |0| then |0| else #0::p >> n *)
(* Proof: by definition. *)
val poly_shift_suc = store_thm(
  "poly_shift_suc",
  ``!p:'a poly. !n. p >> SUC n = if p = |0| then |0| else #0::p >> n``,
  metis_tac[poly_shift_def, list_CASES, poly_zero]);

(* These are more general than definition. *)
val _ = export_rewrites ["poly_shift_0", "poly_shift_suc"];
(* JCQ: <<HOL warning: ThmSetData.lookup: Bad theorem name: poly_shift_0>> *)

(* Theorem: [] >> n = [] *)
(* Proof: by definition. *)
val poly_shift_of_zero = store_thm(
  "poly_shift_of_zero",
  ``!n. [] >> n = []``,
  metis_tac[poly_shift_def, num_CASES]);

val _ = export_rewrites ["poly_shift_of_zero"];

(* Theorem: |0| >> n = |0| *)
(* Proof: by poly_shift_of_zero and poly_zero. *)
val poly_shift_zero = save_thm("poly_shift_zero", poly_shift_of_zero |> REWRITE_RULE [GSYM poly_zero]);
(* > val poly_shift_zero = |- !n. |0| >> n = |0| : thm *)

val _ = export_rewrites ["poly_shift_zero"];

(* Theorem: p >> n = [] <=> p = [] *)
(* Proof: by cases on p. *)
val poly_shift_eq_of_zero = store_thm(
  "poly_shift_eq_of_zero",
  ``!(p:'a poly) n. (p >> n = []) <=> (p = [])``,
  metis_tac[poly_shift_def, num_CASES, list_CASES, NOT_CONS_NIL]);

(* Theorem: p >> n = |0| <=> p = |0| *)
(* Proof: by poly_shift_eq_of_zero and poly_zero. *)
val poly_shift_eq_zero = save_thm("poly_shift_eq_zero", poly_shift_eq_of_zero |> REWRITE_RULE [GSYM poly_zero]);
(* > val poly_shift_eq_zero = |- !p n. (p >> n = |0|) <=> (p = |0|) : th *)

(* Theorem: weak p ==> weak (p >> n) *)
(* Proof: by induction on n.
   If p = [], true by poly_shift_of_zero.
   For p <> [], p = h::t.
   Base: weak (h::t) ==> weak ((h::t) >> 0)
      true by poly_shift_0
   Step: weak (h::t) /\ weak ((h::t) >> n) ==> weak ((h::t) >> SUC n)
      Since weak ((h::t) >> SUC n = #0::(h::t)>> n   by poly_shift_suc
      hence weak ((h::t) >> SUC n  by weak_cons, ring_zero_element
*)
val poly_shift_weak = store_thm(
  "poly_shift_weak",
  ``!r:'a ring. Ring r ==> !p. weak p ==> !n. weak (p >> n)``,
  rpt strip_tac >>
  Cases_on `p` >-
  rw[] >>
  Induct_on `n` >>
  rw[]);

val _ = export_rewrites ["poly_shift_weak"];

(* Theorem: LAST ((h::t) >> n) = LAST (h::t) *)
(* Proof: by induction on n.
   Base: p <> [] ==> LAST (p >> 0) = LAST p
      true by poly_shift_0.
   Step: p <> [] /\ LAST (p >> n) = LAST p ==> LAST (p >> SUC n) = LAST p
      Since p <> [], p = h::t.
      LAST ((h::t) >> SUC n)
    = LAST (#0::(h::t) >> n)    by poly_shift-suc
    = LAST (#0::h'::t')         by poly_shift_eq_of_zero, (h::t) >> n <> []
    = LAST (h'::t')             by LAST_CONS
    = LAST (h::t)               by induction hypothesis
*)
val poly_shift_last = store_thm(
  "poly_shift_last",
  ``!p:'a poly. p <> |0| ==> !n. LAST (p >> n) = LAST p``,
  rw_tac std_ss[poly_zero] >>
  Induct_on `n` >-
  rw[] >>
  metis_tac[poly_shift_suc, poly_shift_eq_zero, LAST_CONS, list_CASES, poly_zero]);

(* Theorem: p <> |0| ==> !n. LENGTH (p >> n) = (LENGTH p) + n *)
(* Proof:
   By induction on n.
   Base: LENGTH (p >> 0) = LENGTH p + 0
      Note p >> 0 = p              by poly_shift_0
      Thus LENGTH (p >> 0)
         = LENGTH p
         = LENGTH p + 0            by ADD_0
   Step: LENGTH (p >> n) = LENGTH p + n ==> LENGTH (p >> SUC n) = LENGTH p + SUC n
      Note p >> SUC n
         = (#0::p >> n)            by poly_shift_suc, p <> |0|
      Thus LENGTH (p >> SUC n)
         = LENGTH (#0: p >> n)
         = SUC (LENGTH (p >> n))   by LENGTH
         = SUC (LENGTH p + n)      by induction hypothesis
         = LENGTH p + SUC n        by ADD_SUC
*)
val poly_shift_length = store_thm(
  "poly_shift_length",
  ``!p:'a poly. p <> |0| ==> !n. LENGTH (p >> n) = (LENGTH p) + n``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[]);

(* Theorem: p <> |0| ==> !n. p >> n = PAD_LEFT #0 (n + LENGTH p) p *)
(* Proof:
   By induction on n.
   Base: p >> 0 = PAD_LEFT #0 (0 + LENGTH p) p
         p >> 0
       = p                                     by poly_shift_0
       = PAD_LEFT #0 (LENGTH p) p              by PAD_LEFT_ID
   Step: p >> n = PAD_LEFT #0 (n + LENGTH p) p ==> p >> SUC n = PAD_LEFT #0 (SUC n + LENGTH p) p
        p >> SUC n
      = #0 :: p >> n                           by poly_shift_suc, p <> |0|
      = #0 :: (PAD_LEFT #0 (n + LENGTH p) p)   by induction hypothesis
      = PAD_LEFT #0 (SUC (n + LENGTH p)) p     by PAD_LEFT_CONS, LENGTH p <= n + LENGTH p
      = PAD_LEFT #0 (SUC n + LENGTH p) p       by ADD
*)
val poly_shift_nonzero = store_thm(
  "poly_shift_nonzero",
  ``!r:'a ring. !p. p <> |0| ==> !n. p >> n = PAD_LEFT #0 (n + LENGTH p) p``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[PAD_LEFT_ID] >>
  rw[poly_shift_suc, PAD_LEFT_CONS, ADD]);

(* Theorem: [c] >> n = PAD_LEFT #0 (SUC n) [c] *)
(* Proof:
   Note [c] <> |0|                      by NOT_NIL_CONS, poly_zero
     [c] >> n
   = PAD_LEFT #0 (n + LENGTH [c]) [c]   by poly_shift_nonzero
   = PAD_LEFT #0 (n + 1) [c]            by LENGTH
   = PAD_LEFT #0 (SUC n) [c]            by ADD1
*)
val poly_shift_const = store_thm(
  "poly_shift_const",
  ``!r:'a ring. !c n. [c] >> n = PAD_LEFT #0 (SUC n) [c]``,
  rw[poly_shift_nonzero, ADD1]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Shift Theorems                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: p >> 1 = if p = |0| then |0| else #0::p *)
(* Proof: by definition and cases on p.
   If p = |0|, trivially true.
   If p <> |0|, true by poly_shift_def.
*)
val poly_shift_1 = store_thm(
  "poly_shift_1",
  ``!p:'a poly. p >> 1 = if p = |0| then |0| else #0::p``,
  rw_tac std_ss[] >-
  rw[] >>
  metis_tac[poly_shift_suc, poly_shift_0, ONE, poly_zero]);

(* Theorem: (h::p) >> 1 = #0::h::p *)
(* Proof: by poly_shift_1, more useful than above. *)
val poly_shift_1_cons = store_thm(
  "poly_shift_1_cons",
  ``!h:'a. !t:'a poly. (h::t) >> 1 = #0::h::t``,
  rw_tac std_ss[poly_shift_1, poly_zero]);

(* These will always expand p >> 1 to #0::p, causing problems during pattern matching with theorems with p >> 1 *)
(* val _ = export_rewrites ["poly_shift_1", "poly_shift_1_cons"]); *)

(* Theorem: (h::t) >> 0 = (h::t) and (h::t) >> SUC n = ((h::t) >> n) >> 1 *)
(* Proof: by definition *)
val poly_shift_cons = store_thm(
  "poly_shift_cons",
  ``!h:'a. !t:'a poly. ((h::t) >> 0 = (h::t)) /\ (!n. (h::t) >> (SUC n) = ((h::t) >> n) >> 1)``,
  rw[poly_shift_1, poly_shift_eq_zero]);

(* better than poly_shift_def:
val poly_shift_cons = save_thm("poly_shift_cons", poly_shift_def |> CONJUNCT2 |> CONJUNCT2);
> val poly_shift_cons = |- (!v5 v4 f. (v4::v5) >> 0 = v4::v5) /\ !v7 v6 n f. (v6::v7) >> SUC n = #0::(v6::v7) >> n : thm
*)

val _ = export_rewrites ["poly_shift_cons"];

(* Theorem: !p n. p >> SUC n = (p >> n) >> 1 *)
(* Proof:
   If p = |0|,
      LHS = |0| >> SUC n = |0|  by poly_shift_zero
      RHS = ( |0| >> n) >> 1
          = |0| >> 1            by poly_shift_zero
          = |0| = LHS           by poly_shift_zero
   If p <> |0|, p = h::t        by poly_zero
      Then (h::t) >> SUC n = ((h::t) >> n) >> 1   by poly_shift_cons
*)
val poly_shift_SUC = store_thm(
  "poly_shift_SUC",
  ``!p n. p >> SUC n = (p >> n) >> 1``,
  rpt strip_tac >>
  Cases_on `p` >-
  metis_tac[poly_zero, poly_shift_zero] >>
  rw[poly_shift_cons]);

(* Theorem: h::t = [h] || t >> 1 *)
(* Proof:
   If t = |0|, or [],         by poly_zero
      h::t = [h]
           = [h] || |0|       by weak_add_rzero
           = [h] || |0| >> 1  by poly_shift_zero.
   If t <> [],
     [h] || t >> 1
   = [h] || #0::t          by poly_shift_1, t <> |0|
   = (h + #0)::([] || t)   by weak_add_def
   = h::t                  by ring_add_rzero, weak_add_of_lzero
*)
val weak_cons_eq_add_shift = store_thm(
  "weak_cons_eq_add_shift",
  ``!r:'a ring. Ring r ==> !h t. weak (h::t) ==> (h::t = [h] || t >> 1)``,
  rw_tac std_ss[weak_cons] >>
  Cases_on `t = |0|` >-
  rw[] >>
  rw_tac std_ss[poly_shift_1, weak_add_cons, ring_add_rzero, weak_add_of_lzero]);

(* Theorem: (neg p) >> n = neg (p >> n) *)
(* Proof: by induction on n.
   If p = |0|, true by poly_shift_zero, weak_neg_zero.
   If p <> |0|, induct on n.
   Base: neg p >> 0 = neg (p >> 0)
      true by poly_shift_0.
   Step: neg p >> n = neg (p >> n) ==> neg p >> SUC n = neg (p >> SUC n)
      p <> |0| ==> neg p <> |0|   by weak_neg_eq_zero
      (neg p) >> SUC n
    = #0 :: (neg p) >> n     by poly_shift_suc
    = #0 :: neg (p >> n)     by induction hypothesis
    = - #0 :: neg (p >> n)   by ring_neg_zero
    = neg (#0 :: p >> n)     by weak_neg_cons
    = neg (p >> SUC n)       by poly_shift_suc
*)
val weak_neg_shift = store_thm(
  "weak_neg_shift",
  ``!r:'a ring. Ring r ==> !p n. (neg p) >> n = neg (p >> n)``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[] >>
  Induct_on `n` >-
  rw[] >>
  rw[weak_neg_eq_zero]);

(* Theorem: (p || q) >> 1 = (p >> 1) || (q >> 1) *)
(* Proof:
   If p = |0| or q = |0|,
      then |0| >> 1 = |0|  by poly_shift_zero
      hence true           by weak_add_lzero, weak_add_rzero.
   If p <> |0| and q <> |0|.
     then p || q <> |0|    by weak_add_eq_zero
     (p >> 1) || (q >> 1)
   = (#0::p) || (#0::q)    by poly_shift_1
   = (#0 + #0)::(p || q)   by weak_add_cons
   = #0::(p || q)          by ring_add_zero_zero
   = (p || q) >> 1         by poly_shift_1
*)
val weak_add_shift_1 = store_thm(
  "weak_add_shift_1",
  ``!r:'a ring. Ring r ==> !p q:'a poly. (p || q) >> 1 = (p >> 1) || (q >> 1)``,
  rpt strip_tac >>
  Cases_on `(p = |0|) \/ (q = |0|)` >-
  metis_tac[poly_shift_zero, weak_add_zero] >>
  rw[poly_shift_1, weak_add_eq_zero]);
(* This theorem is actually used below. This is also useful for p o (h::t), since only >> 1 is involved. *)

(* Theorem: (p || q) >> n = (p >> n) || (q >> n) *)
(* Proof:
   By induction on n.
   Base: (p || q) >> 0 = p >> 0 || q >> 0
      This is true                      by poly_shift_0
   Step: (p || q) >> n = p >> n || q >> n ==>
         (p || q) >> SUC n = p >> SUC n || q >> SUC n
      If p = |0| or q = |0|,
         Note |0| >> n = |0|            by poly_shift_zero
         Hence true                     by weak_add_zero
      If p <> |0| and q <> |0|,
        then p || q <> |0|              by weak_add_eq_zero
        (p || q) >> SUC n
      = ((p || q) >> n) >> 1            by poly_shift_cons
      = ((p >> n) || (q >> n)) >> 1     by induction hypothesis
      = (p >> n) >> 1 || (q >> n) >> 1  by weak_add_shift_1, poly_shift_weak
      = (p >> SUC n) || (q >> SUC n)    by poly_shift_cons
*)
val weak_add_shift = store_thm(
  "weak_add_shift",
  ``!r:'a ring. Ring r ==> !p q:'a poly. !n. (p || q) >> n = (p >> n) || (q >> n)``,
  ntac 4 strip_tac >>
  Induct >-
  rw[] >>
  Cases_on `(p = |0|) \/ (q = |0|)` >-
  metis_tac[poly_shift_zero, weak_add_zero] >>
  `((p || q) >> n) >> 1 = (p >> n) >> 1 || (q >> n) >> 1` by rw[weak_add_shift_1] >>
  metis_tac[poly_shift_cons, weak_add_eq_zero, list_CASES, poly_zero]);

Theorem HD_weak_add_shift:
  Ring r /\ weak p /\ p <> |0| ==>
  HD (weak_add r p (q >> 1)) = HD p
Proof
  strip_tac
  \\ Cases_on`q`
  >- (
    rewrite_tac[poly_shift_def]
    \\ metis_tac[weak_add_zero, poly_zero])
  \\ rewrite_tac[ONE]
  \\ rewrite_tac[poly_shift_def]
  \\ Cases_on`p` >- metis_tac[weak_add_zero, poly_zero]
  \\ rewrite_tac[weak_add_def]
  \\ simp[]
  \\ fs[weak_every_element]
QED

Theorem EL_weak_add:
  k < LENGTH (p || q) ==>
  EL k (p || q) = if k < LENGTH p then
                    if k < LENGTH q then EL k p + EL k q
                    else EL k p
                  else EL k q
Proof
  rw[weak_add_length, weak_add_element]
  \\ rpt (pop_assum mp_tac)
  \\ map_every qid_spec_tac[`k`,`q`,`p`]
  \\ Induct \\ rw[]
  >- (
    Cases_on`k` \\ fs[]
    \\ Cases_on`q` \\ fs[] )
  \\ Cases_on`q` \\ fs[]
  \\ Cases_on`k` \\ fs[]
QED

(* Theorem: c IN R ==> (c o p) >> 1 = c o (p >> 1) *)
(* Proof:
   By cases on p.
   If p = |0|, to show: c o |0| >> 1 = c o ( |0| >> 1)
      LHS = (c o |0|) >> 1 = |0| >> 1 = |0|   by weak_cmult_zero, poly_shift_zero
      RHS = c o ( |0| >> 1) = c o |0| = |0|   by poly_shift_zero, weak_cmult_zero
   If p <> |0|, to show: c o (h::t) >> 1 = c o ((h::t) >> 1)
      LHS = (c o (h::t)) >> 1
          = (c * h:: c o t) >> 1    by weak_cmult_cons
          = #0::(c * h:: c o t)     by poly_shift_1
          = #0::(c o (h::t))        by poly_shift_1, weak_cmult_weak
          = c * #0::(c o (h::t))    by ring_mult_rzero
          = c o (#0::(h::t))        by weak_cmult_cons
          = c o (h::t) >> 1 = RHS   by poly_shift_1
*)
val weak_cmult_shift_1 = store_thm(
  "weak_cmult_shift_1",
  ``!r:'a ring. Ring r ==> !p:'a poly c. c IN R ==> ((c o p) >> 1 = c o (p >> 1))``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[] >>
  metis_tac[ring_mult_rzero, weak_cmult_cons, poly_shift_1, list_CASES, NOT_CONS_NIL, poly_zero]);
(* This theorem is now not used below. *)

(* Theorem: (c o p) >> n = c o (p >> n) *)
(* Proof: by induction on n.
   If p = |0|, to show:  c o |0| >> n = c o ( |0| >> n)
      LHS = (c o |0|) >> n
          = |0| >> n              by weak_cmult_zero
          = c o ( |0| >> n) = RHS by weak_cmult_zero, poly_shift_zero
   If p <> |0|,
      c o p <> |0|          by weak_cmult_eq_zero
      Use induction on n.
   Base: c o p >> 0 = c o (p >> 0)
      true by poly_shift_0
   Step: c o p >> n = c o (p >> n) ==> c o p >> SUC n = c o (p >> SUC n)
     c o p >> SUC n
   = #0::(c o p >> n)       by poly_shift_suc, c o p <> |0|
   = #0::(c o (p >> n))     by induction hypothesis
   = c * #0::(c o (p >> n)) by ring_mult_rzero
   = c o (#0::p >> n)       by weak_cmult_cons
   = c o (p >> SUC n)       by poly_shift_suc, p <> |0|
*)
val weak_cmult_shift = store_thm(
  "weak_cmult_shift",
  ``!r:'a ring. Ring r ==> !p:'a poly c:'a. c IN R ==> !n. (c o p) >> n = c o (p >> n)``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[] >>
  `c o p <> |0|` by rw_tac std_ss[weak_cmult_eq_zero] >>
  Induct_on `n` >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* Weak Polynomial Multiplication                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: [] o q = []  *)
(* Proof: by definition. *)
val weak_mult_of_lzero = save_thm("weak_mult_of_lzero", weak_mult_def |> CONJUNCT1);
(* > val weak_mult_of_lzero = |- !r q. [] o q = [] : thm *)

(* Theorem: (h::t) o p = h o p || (t o p) >> 1 *)
(* Proof: by definition. *)
val weak_mult_cons = save_thm("weak_mult_cons", weak_mult_def |> CONJUNCT2);
(* > val weak_mult_cons = |- !r h t q. (h::t) o q = h o q || t o q >> 1 : thm *)

(* definition already exported *)
(* val _ = export_rewrites ["weak_mult_of_lzero", "weak_mult_cons"]; *)

(* Theorem: p o [] = []  *)
(* Proof: by induction on p.
   Base: [] o [] = []
      true by weak_mult_of_lzero.
   Step: p o [] = [] ==> !h. (h::p) o [] = []
    (h::p) o []
   = h o [] || (p o []) >> 1   by weak_mult_cons
   = [] || (p o []) >> 1       by weak_cmult_of_zero
   = [] || [] >> 1             by induction hypothesis
   = [] || []                  by poly_shift_of_zero
   = []                        by weak_add_of_zero_zero
*)
val weak_mult_of_rzero = store_thm(
  "weak_mult_of_rzero",
  ``!p:'a poly. p o [] = []``,
  Induct >>
  rw[]);

val _ = export_rewrites ["weak_mult_of_rzero"];

(* val weak_mult_of_zero = save_thm("weak_mult_of_zero", CONJ weak_mult_of_lzero weak_mult_of_rzero); *)
(* > val weak_mult_of_zero = |- (!r q. [] o q = []) /\ !p. p o [] = [] : thm *)

(* Improvement:

- weak_mult_of_lzero;
> val it = |- !r q. [] o q = [] : thm
- weak_mult_of_lzero |> SPEC_ALL;
> val it = |- [] o q = [] : thm
- weak_mult_of_rzero |> SPEC_ALL;
> val it = |- p o [] = [] : thm
- CONJ (weak_mult_of_lzero |> SPEC_ALL) (weak_mult_of_rzero |> SPEC_ALL);
> val it = |- ([] o q = []) /\ (p o [] = []) : thm
- CONJ (weak_mult_of_lzero |> SPEC_ALL) (weak_mult_of_rzero |> SPEC_ALL) |> GEN_ALL;
> val it = |- !r q p. ([] o q = []) /\ (p o [] = []) : thm
*)

(* Theorem: (p o [] = []) /\ ([] o p = []) *)
(* Proof: by weak_mult_of_rzero, weak_mult_of_lzero *)
Theorem weak_mult_of_zero:
  !r:'a ring. !p:'a poly. (p o [] = []) /\ ([] o p = [])
Proof
  rw_tac std_ss[weak_mult_of_rzero, weak_mult_of_lzero]
QED

(* Theorem: |0| o q = |0|  *)
(* Proof: by weak_mult_of_lzero and poly_zero. *)
Theorem weak_mult_lzero = weak_mult_of_lzero |> REWRITE_RULE [GSYM poly_zero];
(* > val weak_mult_lzero = |- !r q. |0| o q = |0| : thm *)

(* Theorem: p o |0| = |0|  *)
(* Proof: by weak_mult_of_rzero and poly_zero. *)
Theorem weak_mult_rzero = weak_mult_of_rzero |> REWRITE_RULE [GSYM poly_zero];
(* > val weak_mult_rzero = |- !p. p o |0| = |0| : thm *)

(* Theorem: (p o |0| = |0|) /\ ( |0| o p = |0|) *)
(* Proof: by weak_mult_rzero, weak_mult_lzero *)
Theorem weak_mult_zero:
  !r:'a ring. !p:'a poly. (p o |0| = |0|) /\ ( |0| o p = |0|)
Proof rw_tac std_ss[weak_mult_rzero, weak_mult_lzero]
QED

(*
Why is this true:  weak p <> [], weak q <> [], p o q <> [].
Well, p = h::t, q = k::s, by weak_mult_cross, there is at least the constant term, hence p o q <> [].
*)

(* Theorem: p o q = [] <=> p = [] \/ q = [] *)
(* Proof:
   Only-if part: p = [] or q = [] ==> p o q = []
      true by weak_mult_of_lzero, weak_mult_of_rzero.
   If part: p o q = [] ==> p = [] or q = []
      Assume p <> [], then p = h::t.
      p o q
    = (h::t) o q
    = h o q || (t o q) >> 1          by weak_mult_cons
    Since p o q = [],
    h o q = []   and  (t o q) >> 1   by weak_add_eq_of_zero
        q = []   and  (t o q) >> 1   by weak_cmult_eq_of_zero
    hence q = [].
*)
val weak_mult_eq_of_zero = store_thm(
  "weak_mult_eq_of_zero",
  ``!r:'a ring. !p:'a poly q. (p o q = []) <=> (p = []) \/ (q = [])``,
  (rw[EQ_IMP_THM] >> simp[weak_mult_of_zero]) >>
  spose_not_then strip_assume_tac >>
  `?h t. p = h::t` by metis_tac[list_CASES] >>
  fs[weak_cons, weak_mult_cons] >>
  metis_tac[weak_cmult_eq_of_zero, weak_add_eq_of_zero]);

(* Theorem: p o q = |0| <=> p = |0| \/ q = |0|  *)
(* Proof: by weak_mult_eq_of_zero and poly_zero. *)
val weak_mult_eq_zero = save_thm("weak_mult_eq_zero", weak_mult_eq_of_zero |> REWRITE_RULE [GSYM poly_zero]);
(* > val weak_mult_eq_zero = |- !r p q. (p o q = |0|) <=> (p = |0|) \/ (q = |0|) : thm *)

(* Theorem: weak p /\ weak q ==> weak (p o q) *)
(* Proof: by induction on p.
   Base: !q. weak [] /\ weak q ==> weak ([] o q
      true by weak_mult_of_lzero.
   Step: !q. weak p /\ weak q ==> weak (p o q) ==>
              !h q. weak (h::p) /\ weak q ==> weak ((h::p) o q)
      By weak_mult_cons,
      (h::p) o q = h o q || (p o q) >> 1
      but weak (h o q)            by weak_cmult_weak
          weak (p o q)            by induction hypothesis
      hence weak ((p o q) >> 1)   by poly_shift_weak
      hence weak (h::p) o q       by weak_add_weak
*)
val weak_mult_weak = store_thm(
  "weak_mult_weak",
  ``!r:'a ring. Ring r ==> !p q:'a poly. weak p /\ weak q ==> weak (p o q)``,
  strip_tac >>
  strip_tac >>
  Induct >>
  rw[]);

val _ = export_rewrites ["weak_mult_weak"];

Theorem weak_mult_length:
  !r p q. LENGTH (weak_mult r p q) =
          if LENGTH p = 0 \/ LENGTH q = 0 then 0
          else LENGTH p + LENGTH q - 1
Proof
  strip_tac
  \\ Induct
  \\ rw[]
  \\ simp[weak_add_length]
  \\ Cases_on`p = |0|` \\ fs[weak_cmult_length]
  \\ Cases_on`q = |0|` \\ fs[]
  \\ `weak_mult r p q <> |0|` by simp[weak_mult_eq_zero]
  \\ simp[poly_shift_length]
  \\ simp[ADD1]
  \\ rw[MAX_DEF]
  \\ Cases_on`q` \\ fs[]
QED

Theorem EL_poly_shift:
  !r p n k. k < LENGTH (p >> n) ==>
  EL k (p >> n) = if ~(k < n) /\ k < n + LENGTH p then
                     EL (k - n) p else r.sum.id
Proof
  ho_match_mp_tac poly_shift_ind
  \\ rw[]
  \\ pop_assum mp_tac
  \\ rewrite_tac[GSYM poly_shift_SUC]
  \\ dep_rewrite.DEP_REWRITE_TAC[poly_shift_length]
  \\ simp[]
  \\ fs[poly_shift_length]
  \\ simp[rich_listTheory.EL_CONS, PRE_SUB1, ADD1]
  \\ qmatch_goalsub_abbrev_tac`ls >> 1`
  \\ qmatch_asmsub_rename_tac`ls = (h::t) >> n`
  \\ `LENGTH ls = LENGTH t + n + 1`
  by simp[poly_shift_length, Abbr`ls`]
  \\ strip_tac
  \\ Cases_on`ls=[]` \\ fs[]
  \\ `ls >> 1 = #0 :: ((h::t) >> n)`
  by (
    Cases_on`ls` \\ fs[]
    \\ rewrite_tac[arithmeticTheory.ONE]
    \\ rewrite_tac[polynomialTheory.poly_shift_def] )
  \\ simp[]
  \\ Cases_on`k`\\ fs[]
  \\ fs[ADD1]
QED

Theorem EL_weak_mult:
  !p q k. Ring r /\ k < LENGTH (weak_mult r p q) /\ weak p /\ weak q ==>
          EL k (weak_mult r p q) =
      GBAG r.sum (BAG_IMAGE (λ(n,m). r.prod.op (EL n p) (EL m q))
                   (BAG_FILTER (λ(n,m). n + m = k)
                     (BAG_OF_SET ((count (LENGTH p) × count (LENGTH q))))))
Proof
  Induct
  \\ rw[] \\ fs[]
  \\ simp[EL_weak_add]
  \\ simp[COUNT_SUC_BY_SUC]
  \\ simp[Once CROSS_INSERT_LEFT]
  \\ dep_rewrite.DEP_REWRITE_TAC[BAG_OF_SET_DISJOINT_UNION]
  \\ conj_tac >- simp[IN_DISJOINT]
  \\ simp[weak_cmult_length]
  \\ simp[weak_cmult_element]
  \\ simp[BAG_FILTER_BAG_UNION]
  \\ simp[Once BAG_FILTER_BAG_OF_SET]
  \\ Cases_on`weak_mult r p q = |0|` \\ fs[]
  >- (
    fs[weak_cmult_length]
    \\ `q <> |0|` by (strip_tac \\fs[])
    \\ `weak_mult r p q = |0|` by fs[]
    \\ `p = |0|` by metis_tac[weak_mult_eq_zero]
    \\ fs[]
    \\ qmatch_goalsub_abbrev_tac`BAG_OF_SET s`
    \\ `s = {(0,k)}`
    by (
      simp[Abbr`s`, SET_EQ_SUBSET]
      \\ simp[SUBSET_DEF, FORALL_PROD] )
    \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
    \\ fs[weak_every_element]
    \\ gs[listTheory.EVERY_MEM, PULL_EXISTS, listTheory.MEM_EL] )
  \\ dep_rewrite.DEP_REWRITE_TAC[poly_shift_length]
  \\ simp[]
  \\ simp[EL_poly_shift, poly_shift_length]
  \\ Cases_on`k=0` \\ gs[]
  >- (
    simp[BAG_FILTER_BAG_OF_SET]
    \\ Cases_on`q` \\ fs[]
    \\ qmatch_goalsub_abbrev_tac`BAG_OF_SET s`
    \\ `s = {(0,0)}`
    by ( simp[Abbr`s`, Once EXTENSION, FORALL_PROD])
    \\ simp[Abbr`s`, BAG_OF_SET_INSERT_NON_ELEMENT]
    \\ qmatch_goalsub_abbrev_tac`BAG_OF_SET s`
    \\ `s = {}`
    by (
      simp[Abbr`s`, Once EXTENSION]
      \\ simp[SUBSET_DEF, FORALL_PROD])
    \\ simp[])
  \\ qmatch_goalsub_abbrev_tac`lhs = _`
  \\ qmatch_goalsub_abbrev_tac`BAG_OF_SET s`
  \\ `s = if k < LENGTH q then {(0, k)} else {}`
  by ( simp[Abbr`s`, SET_EQ_SUBSET, SUBSET_DEF, FORALL_PROD] \\ rw[] )
  \\ simp[Abbr`s`] \\ pop_assum kall_tac
  \\ simp[Abbr`lhs`]
  \\ IF_CASES_TAC
  >- (
    simp[weak_mult_length]
    \\ Cases_on`p=[]`\\ fs[]
    \\ Cases_on`q=[]`\\ fs[]
    \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
    \\ dep_rewrite.DEP_REWRITE_TAC[GBAG_UNION]
    \\ simp[]
    \\ fs[weak_every_mem, listTheory.MEM_EL, PULL_EXISTS]
    \\ simp[SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
    \\ AP_TERM_TAC
    \\ dep_rewrite.DEP_REWRITE_TAC[MP_CANON GBAG_IMAGE_FILTER]
    \\ simp[]
    \\ simp[SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
    \\ qmatch_goalsub_abbrev_tac`_ = GBAG _ (BAG_IMAGE _ (BAG_OF_SET s))`
    \\ `s = IMAGE (λ(n,m). (SUC n, m)) (count (LENGTH p) × count(LENGTH q))`
    by (
      simp[Abbr`s`, SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS,
           FORALL_PROD, EXISTS_PROD])
    \\ simp[Abbr`s`]
    \\ dep_rewrite.DEP_REWRITE_TAC[BAG_OF_SET_IMAGE_INJ]
    \\ simp[FORALL_PROD]
    \\ dep_rewrite.DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
    \\ simp[]
    \\ irule GITBAG_CONG
    \\ simp[PULL_EXISTS, EXISTS_PROD, FORALL_PROD]
    \\ simp[SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
    \\ reverse conj_tac >- rw[]
    \\ gen_tac
    \\ simp[combinTheory.o_DEF, LAMBDA_PROD, arithmeticTheory.ADD1]
    \\ disch_then assume_tac
    \\ AP_THM_TAC
    \\ irule BAG_IMAGE_CONG
    \\ simp[FORALL_PROD]
    \\ simp[rich_listTheory.EL_CONS, arithmeticTheory.PRE_SUB1]
    \\ pop_assum kall_tac
    \\ rw[] \\ gs[] )
  \\ simp[]
  \\ fs[weak_add_length, weak_cmult_length]
  \\ simp[EL_poly_shift]
  \\ fs[poly_shift_length]
  \\ dep_rewrite.DEP_REWRITE_TAC[MP_CANON GBAG_IMAGE_FILTER]
  \\ fs[weak_every_mem, listTheory.MEM_EL, PULL_EXISTS]
  \\ simp[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD, FORALL_PROD]
  \\ qmatch_goalsub_abbrev_tac`_ = GBAG _ (BAG_IMAGE _ (BAG_OF_SET s))`
  \\ `s = IMAGE (λ(n,m). (SUC n, m)) (count (LENGTH p) × count(LENGTH q))`
  by (
    simp[Abbr`s`, SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS,
         FORALL_PROD, EXISTS_PROD])
  \\ simp[Abbr`s`]
  \\ dep_rewrite.DEP_REWRITE_TAC[BAG_OF_SET_IMAGE_INJ]
  \\ simp[FORALL_PROD]
  \\ dep_rewrite.DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
  \\ simp[]
  \\ irule GITBAG_CONG
  \\ simp[PULL_EXISTS, EXISTS_PROD, FORALL_PROD]
  \\ simp[SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
  \\ reverse conj_tac >- rw[]
  \\ gen_tac
  \\ simp[combinTheory.o_DEF, LAMBDA_PROD, ADD1]
  \\ disch_then assume_tac
  \\ AP_THM_TAC
  \\ irule BAG_IMAGE_CONG
  \\ simp[FORALL_PROD]
  \\ simp[rich_listTheory.EL_CONS, PRE_SUB1]
  \\ pop_assum kall_tac
  \\ rw[] \\ gs[]
QED


(* ------------------------------------------------------------------------- *)
(* Theorems on polynomial multiplication with scalar multiplication.         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (c o p) o q = c o (p o q)  *)
(* Proof: by induction on p.
   Base: (c o []) o q = c o [] o q
      LHS = (c o []) o q
          = [] o q             by weak_cmult_of_zero
          = []                 by weak_mult_of_lzero
      RHS = c o ([] o q)
          = c o []             by weak_mult_of_lzero
          = [] = LHS           by weak_cmult_of_zero
   Step: (c o p) o q = c o p o q ==> (c o (h::p)) o q = c o (h::p) o q
      LHS = (c o (h::p)) o q
          = (c * h :: c o p) o q               by weak_cmult_cons
          = (c * h) o q || ((c o p) o q) >> 1  by weak_mult_cons
          = c o (h o q) || ((c o p) o q) >> 1  by weak_cmult_cmult
          = c o (h o q) || (c o (p o q)) >> 1  by induction hypothesis
          = c o (h o q) || c o ((p o q) >> 1)  by weak_cmult_shift_1
          = c o (h o q || (p o q) >> 1)        by weak_cmult_add
          = c o ((h::p) o q) = RHS             by weak_mult_cons
*)
val weak_cmult_mult = store_thm(
  "weak_cmult_mult",
  ``!r:'a ring. Ring r ==> !p q:'a poly. weak p /\ weak q ==>
    !c. c IN R ==> ((c o p) o q = c o (p o q))``,
  strip_tac >>
  strip_tac >>
  Induct >>
  rw[weak_cmult_cmult, weak_cmult_shift_1, weak_cmult_add]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Negation with Addition                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: zerop (neg p || p) *)
(* Proof: by induction on p and ring_add_lneg.
   Base: weak [] ==> zerop (neg [] || [])
      true by weak_neg_of_zero, weak_add_zero, zero_poly_of_zero.
   Step: weak p ==> zerop (neg p || p) ==>
              !h. weak (h::p) ==> zerop (neg (h::p) || (h::p))
       zerop (neg (h::p) || (h::p))
   <=> zerop ((-h::neg p) || (h::p))   by weak_neg_cons
   <=> zerop (-h + h :: neg p || p)    by weak_add_cons
   <=> zerop (#0 :: neg p || p)        by ring_add_lneg
   <=> T                               by zero_poly_cons, induction hypothesis
*)
val weak_add_lneg = store_thm(
  "weak_add_lneg",
  ``!r:'a ring. Ring r ==> !p. weak p ==> zerop (neg p || p)``,
  strip_tac >>
  strip_tac >>
  Induct >>
  rw[]);

(* Theorem: zerop (p || neg p) *)
(* Proof: by weak_add_lneg, weak_add_comm, weak_neg_weak. *)
val weak_add_rneg = store_thm(
  "weak_add_rneg",
  ``!r:'a ring. Ring r ==> !p. weak p ==> zerop (p || neg p)``,
  metis_tac[weak_add_lneg, weak_add_comm, weak_neg_weak]);
(* Q: Why rw[weak_add_lneg] is not working here? *)

val _ = export_rewrites ["weak_add_lneg", "weak_add_rneg"];

(* Theorem: zerop p ==> zerop (c o p) *)
(* Proof by induction on p.
   Base: zerop [] ==> !c::(R). zerop (c o [])
      True by weak_cmult_of_zero.
   Step: zerop p ==> !c::(R). zerop (c o p) ==> !h. zerop (h::p) ==> !c::(R). zerop (c o (h::p))
       zerop (h::p)
   ==> h = #0 /\ zerop p              by zero_poly_cons
   ==> c * h = #0 /\ zerop p          by ring_mult_rzero
   ==> c * h = #0 /\ zerop (c o p)    by induction hypothesis
   ==> zerop (c * h :: c o p)         by zero_poly_cons
   ==> zerop (c o (h::p))             by weak_cmult_cons
*)
val zero_poly_cmult = store_thm(
  "zero_poly_cmult",
  ``!r:'a ring. Ring r ==> !p:'a poly. zerop p ==> !c. c IN R ==> zerop (c o p)``,
  strip_tac >>
  strip_tac >>
  Induct >>
  rw[]);

val _ = export_rewrites ["zero_poly_cmult"];

(* Theorem: weak p ==> zerop (#0 o p) *)
(* Proof: by induction on p.
   Base: weak [] ==> zerop (#0 o [])
      true by weak_cmult_of_zero.
   Step: weak p ==> zerop (#0 o p) ==> !h. weak (h::p) ==> zerop (#0 o (h::p))
       zerop (#0 o (h::p))
   <=> zerop (#0 * h :: #0 o p)   by weak_cmult_cons
   <=> zerop (#0 :: #0 o p)       by ring_mult_lzero
   <=> zerop (#0 * p)             by zero_poly_cons
   <=> T                          by induction hypothesis
*)
val weak_cmult_lzero = store_thm(
  "weak_cmult_lzero",
  ``!r:'a ring. Ring r ==> !p. weak p ==> zerop (#0 o p)``,
  strip_tac >>
  strip_tac >>
  Induct >>
  rw[]);

(* Theorem: zerop p = zerop (neg p) *)
(* Proof: by induction on p.
   Base: zerop [] <=> zerop (neg [])
      true by weak_neg_of_zero.
   Step: zerop p = zerop (neg p) ==> zerop (h::p) = zerop (neg (h::p))
       zerop (h::p)
   <=> h = #0 and zerop p          by zero_poly_cons
   <=> h = #0 and zerop (neg p)    by induction hypothesis
   <=> -h = #0 and zerop (neg p)   by ring_neg_eq_zero
   <=> zerop (-h::neg p)           by zero_poly_cons
   <=> zerop (neg (h::p))          by weak_neg_cons
*)
val zero_weak_neg = store_thm(
  "zero_weak_neg",
  ``!r:'a ring. Ring r ==> !p:'a poly. weak p ==> (zerop p <=> zerop (neg p))``,
  strip_tac >>
  strip_tac >>
  Induct >>
  rw[ring_neg_eq_zero]);

(* Seems this is no good -- two sides too similar! *)
(* val _ = export_rewrites ["zero_weak_neg"]; *)

(* Theorem: zerop (p >> n) = zerop p *)
(* Proof: by induction on n.
   Base: zerop (p >> 0) <=> zerop p
      true by poly_shift_0.
   Step: zerop (p >> n) <=> zerop p ==> zerop (p >> SUC n) <=> zerop p
       zerop (p >> SUC n)
   <=> zerop (#0::p >> n)    by poly_shift_suc
   <=> zerop (p >> n)        by zero_poly_cons
   <=> zerop p               by induction hypothesis
*)
val zero_poly_shift = store_thm(
  "zero_poly_shift",
  ``!p n. zerop (p >> n) = zerop p``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[]);

(* val _ = export_rewrites ["zero_poly_shift"]; *)

(* ------------------------------------------------------------------------- *)
(* Polynomial Multiplication                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: zerop p ==> zerop (p o q) *)
(* Proof: Induction on p and q.
   Base: !q. zerop [] /\ weak q ==> zerop ([] o q)
      true by weak_mult_of_lzero.
   Step: !q. zerop p /\ weak q ==> zerop (p o q) ==>
              !h q. zerop (h::p) /\ weak q ==> zerop ((h::p) o q)
      Note zerop (h::p) means h = #0 and zerop p   by zero_poly_cons
      (h::p) o q
    = #0 o q || (p o q) >> 1   by weak_mult_cons
    = zerop  || (p o q) >> 1   by weak_cmult_lzero
    = zerop  || zerop          by zero_poly_shift, induction hypothesis
    = zerop                    by zero_weak_add_zero
*)
val zero_weak_lmult = store_thm(
  "zero_weak_lmult",
  ``!r:'a ring. Ring r ==> !p q. zerop p /\ weak q ==> zerop (p o q)``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw_tac std_ss[weak_mult_of_lzero] >>
  rw[weak_cmult_lzero, zero_weak_add_zero, zero_poly_cons, zero_poly_shift]);

(* Theorem: zerop q ==> zerop (p o q) *)
(* Proof: by induction on p and q.
   Base: !q. weak [] /\ zerop q ==> zerop ([] o q)
      true by weak_mult_of_lzero, zero_poly_of_zero.
   Step: !q. weak p /\ zerop q ==> zerop (p o q) ==>
              !h q. weak (h::p) /\ zerop q ==> zerop ((h::p) o q)
      (h::p) o q
    = h o q || (p o q) >> 1   by weak_mult_cons
    = zerop || (p o q) >> 1   by zero_poly_cmult
    = zerop || zerop          by zero_poly_shift, induction hypothesis
    = zerop                   by zero_weak_add_zero
*)
val zero_weak_rmult = store_thm(
  "zero_weak_rmult",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ zerop q ==> zerop (p o q)``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw_tac std_ss[weak_mult_of_lzero, zero_poly_of_zero] >>
  rw[zero_poly_cmult, zero_poly_shift, zero_weak_add_zero]);

(* val _ = export_rewrites ["zero_weak_lmult", "zero_weak_rmult"]; *)

(* Theorem: (p o q) >> 1 = p o (q >> 1) *)
(* Proof: by induction on p.
   Base: !q. weak [] /\ weak q ==> ([] o q >> 1 = [] o (q >> 1))
      LHS = ([] * q) >> 1 = [] >> 1       by weak_mult_of_lzero
                          = []            by poly_shift_of_zero
      RHS = [] * (q >> 1) = [] = LHS      by weak_mult_of_lzero
   Step: !q. weak p /\ weak q ==> (p o q >> 1 = p o (q >> 1)) ==>
         !h q. weak (h::p) /\ weak q ==> ((h::p) o q >> 1 = (h::p) o (q >> 1))
     ((h::p) o q) >> 1
   = (h o q || (p o q) >> 1) >> 1         by weak_mult_cons
   = (h o q) >> 1 || ((p o q) >> 1) >> 1  by weak_add_shift_1, Ring r
   = h o (q >> 1) || ((p o q) >> 1) >> 1  by weak_cmult_shift_1, h IN R
   = h o (q >> 1) || (p o (q >> 1)) >> 1  by induction hypothesis
   = (h::p) o (q >> 1)                    by weak_mult_cons
*)
val weak_mult_shift_1 = store_thm(
  "weak_mult_shift_1",
  ``!r:'a ring. Ring r ==> !p q:'a poly. weak p /\ weak q ==> ((p o q) >> 1 = p o (q >> 1))``,
  strip_tac >>
  strip_tac >>
  Induct >>
  rw[weak_add_shift_1, weak_cmult_shift_1]);

(* ------------------------------------------------------------------------- *)
(* Constant Polynomials.                                                     *)
(* ------------------------------------------------------------------------- *)

(* SING Theorems = Theorems involving constant polynomials:

These are important because, later for cross-multiplication of polynomials, it will come to:

(h::p) * (h'::q) = h' * (h::p) + ((h::p) * q) >> 1

when p = [] and q = [], this reduces to: [h]*[h'] = h' * [h]
we know p = [] ==> h <> #0 by weak p, and q = [] ==> h' <> #0 by weak q.

These can be simply proved by definition from src_tac.

Seems the only use of weak_nonzero_element_weak above are:
- weak_alternative;
> val it = |- !r. Ring r ==> !p. weak p <=> (p = []) \/ EVERY (\c. c IN R) p /\ LAST p <> #0 : thm
- weak_cons_eq_add_shift;
> val it = |- !r. Ring r ==> !h t. weak (h::t) ==> (h::t = [h] + t >> 1) : thm

No one is using weak_alternative!
Only use of weak_cons_eq_add_shift is somewhere below.

*)

(* Theorem: weak [k] *)
(* Proof: by weak_cons, weak_of_zero. *)
val weak_const = store_thm(
  "weak_const",
  ``!r:'a ring. !k. k IN R ==> weak [k]``,
  rw[]);

val _ = export_rewrites ["weak_const"];

(* The following relates weak_cmult with ring_mult for constant poly. *)

(* Theorem: h o [k] = [h o k] *)
(* Proof:
     h o [k]
   = (h * k::h o [])    by weak_cmult_cons
   = [h * k]            by weak_cmult_of_zero
*)
val weak_cmult_const = store_thm(
  "weak_cmult_const",
  ``!r:'a ring. !h k. h o [k] = [h * k]``,
  rw[]);

(* Theorem: h o [k] = k o [h] *)
(* Proof:
     h o [k]
   = [h * k]       by weak_cmult_const
   = [k * h]       by ring_mult_comm
   = k o [h]       by weak_cmult_const
*)
val weak_cmult_const_comm = store_thm(
  "weak_cmult_const_comm",
  ``!r:'a ring. Ring r ==> !h k. h IN R /\ k IN R ==> (h o [k] = k o [h])``,
  rw_tac std_ss[weak_cmult_const, ring_mult_comm]);

(* The following relates weak_mult with weak_cmult for constant poly. *)

(* Theorem: [k] o p = k o p *)
(* Proof:
     [k] o p
   = k o p || ([] o p) >> 1    by weak_mult_cons
   = k o p || ([]) >> 1        by weak_mult_of_lzero
   = k o p || []               by poly_shift_of_zero
   = k o p                     by weak_add_of_rzero
*)
val weak_mult_const = store_thm(
  "weak_mult_const",
  ``!r:'a ring. !p k. k IN R ==> ([k] o p = k o p)``,
  rw[]);

(* Theorem: [h] o [k] = h o [k] *)
(* Proof: by weak_mult_const. *)
val weak_mult_const_const = store_thm(
  "weak_mult_const_const",
  ``!r:'a ring. !h k. h IN R /\ k IN R ==> ([h] o [k] = h o [k])``,
  rw[]);

(* Theorem:  [h] o [k] = [k] o [h] *)
(* Proof:
     [h] o [k]
   = h o [k]       by weak_mult_const_const
   = k o [h]       by weak_cmult_const_comm
   = [k] o [h]     by weak_mult_const_const
*)
val weak_mult_const_const_comm = store_thm(
  "weak_mult_const_const_comm",
  ``!r:'a ring. Ring r ==> !h k. h IN R /\ k IN R ==> ([h] o [k] = [k] o [h])``,
  rw_tac std_ss[weak_mult_const_const, weak_cmult_const_comm]);

(* Start of weak_mult_cons for constant poly. *)

(* Note: the following is almost: [k] * (h::p) = (h::p) * [k],
   but we only have weak_mult_cons at this point, no weak_mult_cons_comm. *)

(* Theorem: weak (h::p) ==> [k] o (h::p) = h o [k] || ([k] o p) >> 1 *)
(* Proof:
   LHS = [k] o (h::p)
       = k o (h::p)                  by weak_mult_const
       = k o ([h] || p >> 1)         by weak_cons_eq_add_shift
       = k o [h] || k o (p >> 1)     by weak_cmult_add
       = h o [k] || k o (p >> 1)     by weak_cmult_const_comm
       = h o [k] || (k o p) >> 1     by weak_cmult_shift_1
       = h o [k] || ([k] o p) >> 1   by weak_mult_const
       = RHS
*)
val weak_mult_const_cons = store_thm(
  "weak_mult_const_cons",
  ``!r:'a ring. Ring r ==> !p h k. k IN R /\ weak (h::p) ==> ([k] o (h::p) = h o [k] || ([k] o p) >> 1)``,
  rw_tac std_ss[weak_cons] >>
  `h::p = [h] || p >> 1` by rw_tac std_ss[weak_cons_eq_add_shift, weak_cons] >>
  rw_tac std_ss[weak_mult_const, weak_cmult_shift_1, weak_cmult_const_comm,
                 weak_cmult_add, weak_const, poly_shift_weak]);

(* This is to jump over the fact that [h * k] may not be polynomial:
   h * (k::q) = (h * k) :: (h * q) = [h * k] + (h * q) >> 1
*)

(* Theorem: k o (h::p) = [k * h] || (k o p) >> 1 *)
(* Proof:
   LHS = k o (h::p)
       = [k] o (h::p)               by weak_mult_const
       = h o [k] || ([k] o p) >> 1  by weak_mult_const_cons
       = [h * k] || ([k] o p) >> 1  by weak_cmult_const
       = [h * k] || (k o p) >> 1    by weak_mult_const
       = [k * h] || (k o p) >> 1    by ring_mult_comm
       = RHS
*)
val weak_cmult_cons_eq_add_shift = store_thm(
  "weak_cmult_cons_eq_add_shift",
  ``!r:'a ring. Ring r ==> !p h k. k IN R /\ weak (h::p) ==> (k o (h::p) = [k * h] || (k o p) >> 1)``,
  rw_tac std_ss[weak_cons] >>
  `k o (h::p) = [k] o (h::p)` by rw_tac std_ss[weak_mult_const] >>
  rw[weak_mult_const, weak_mult_const_cons, weak_cmult_const, ring_mult_comm]);

(* Theorem: p o [k] = k o p *)
(* Proof: by induction on p
   Base: [] o [k] = k o []
      true by weak_mult_of_lzero, weak_cmult_of_zero.
   Step: p o [k] = k o p ==> (h::p) o [k] = k o (h::p)
    (h::p) o [k]
   = h o [k] || (p o [k]) >> 1   by weak_mult_cons
   = k o [h] || (p o [k]) >> 1   by weak_cmult_const_comm
   = k o [h] || (k o p) >> 1     by induction hypothesis
   = k o [h] || k o (p >> 1)     by weak_cmult_shift_1
   = k o ([h] || p >> 1)         by weak_cmult_add
   = k o (h::p)                  by weak_cons_eq_add_shift
*)
val weak_mult_const_comm = store_thm(
  "weak_mult_const_comm",
  ``!r:'a ring. Ring r ==> !p k. k IN R /\ weak p ==> (p o [k] = k o p)``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  rw_tac std_ss[weak_cons] >>
  `weak [h] /\ weak (p >> 1) /\ weak (h::p)` by rw_tac std_ss[weak_const, poly_shift_weak, weak_cons] >>
  metis_tac[weak_cmult_add, weak_cmult_shift_1, weak_cons_eq_add_shift, weak_cmult_const_comm, weak_mult_cons]);

(* Theorem: weak (h::p) ==> (h::p) o [k] = k o (h::p) *)
(* Proof:
   LHS = (h::p) o [k]
       = h o [k] || (p o [k]) >> 1   by weak_mult_cons
       = k o [h] || (p o [k]) >> 1   by weak_cmult_const_comm
       = k o [h] || (k o p) >> 1     by weak_mult_const_comm
       = k o [h] || k o (p >> 1)     by weak_cmult_shift_1
       = k o ([h] || p >> 1)         by weak_cmult_add
       = k o (h::p)                  by weak_cons_eq_add_shift
       = RHS
*)
val weak_mult_cons_const = store_thm(
  "weak_mult_cons_const",
  ``!r:'a ring. Ring r ==> !p h k. k IN R /\ weak (h::p) ==> ((h::p) o [k] = k o (h::p))``,
  metis_tac[weak_mult_cons, weak_cmult_const_comm, weak_mult_const_comm, weak_cmult_shift_1,
             weak_cmult_add, weak_cons_eq_add_shift, weak_const, poly_shift_weak]);

(* Theorem: p o (h::q) = h o p || (p o q) >> 1 *)
(* Proof:
   By induction on p.
   Base: [] o (h::q) = h o [] || [] o q >> 1
      LHS = [] o (h::q) = []   by weak_mult_of_lzero
      RHS = h o [] || [] o q >> 1
          = [] || ([]) >> 1    by weak_cmult_of_zero, weak_mult_of_lzero
          = [] || []           by poly_shift_of_zero
          = [] = LHS           by weak_add_of_zero_zero
   Step: p o (h::q) = h o p || p o q >> 1 ==> (h::p) o (h'::q) = h' o (h::p) || (h::p) o q >> 1
   Note:
   In the middle of the proof, the key step is to apply poly_shift_1:
      (h' o p || (p o q) >> 1) >> 1 = #0::(h' o p || p o q >> 1)
   But how to argue that h' o p || (p o q) >> 1 <> [], in order to apply poly_shift_1 ?
       h' o p || (p o q) >> 1 = []
   <=> h' o p = [] and (p o q) >> 1 = []   by weak_add_eq_of_zero
   <=>      p = [] and  p o q = []         by weak_cmult_eq_of_zero, poly_shift_eq_of_zero
   So if p <> [], then  h' o p || (p o q) >> 1 <> [].
   Similarly, we need q <> [] in the last part of the proof.

   If p = [], h::p = [h], so this is effectively scalar multiplication (using SING theorem):
   that is: [h] o (h'::q) = h' o [h] || [h] o q >> 1, true by weak_mult_const_cons.
   If q = [], h'::q = [h'], so this is effectively another scalar multiplication (using SING theorem):
   that is: (h::p) o [h'] = h' o (h::p) || (h::p) o [] >> 1
   but (h::p) o [h'] = h' o (h::p)                        by weak_mult_cons_const
                     = h' o (h::p) || (h::p) o [] >> 1    by poly_shift_of_zero, weak_mult_of_rzero.

   If p <> [], h' o p <> []                               by weak_cmult_eq_of_zero
      hence  h' o p || p o q >> 1 <> []                   by weak_add_eq_of_zero
   If q <> [], h o q <> []                                by weak_cmult_eq_of_zero
      hence  h o q || p o q >> 1  <> []                   by weak_add_eq_of_zero
     (h::p) o (h'::q)
   = h o (h'::q) || (p o (h'::q)) >> 1                    by weak_mult_cons
   = (h * h':: h o q) || (p o (h'::q)) >> 1               by weak_cmult_cons
   = (h * h':: h o q) || (h' o p || (p o q) >> 1) >> 1    by induction hypothesis
   = (h' * h:: h o q) || (#0::h' o p || p o q >> 1)       by ring_mult_comm, poly_shift_1
   = h' * h + #0 :: h o q || (h' o p || p o q >> 1)       by weak_add_cons
   = h' * h + #0 :: h o q || h' o p || p o q >> 1         by weak_add_assoc
   = h' * h + #0 :: h' o p || h o q || p o q >> 1         by weak_add_comm
   = h' * h + #0 :: h' o p || (h o q || p o q >> 1)       by weak_add_assoc
   = (h' * h :: h' o p) || (#0::h o q || p o q >> 1)      by weak_add_cons
   = (h' * h :: h' o p) || (h o q || p o q >> 1) >> 1     by poly_shift_1
   = h' o (h::p) || (h o q || p o q >> 1) >> 1            by weak_cmult_cons
   = h' o (h::p) || (h::p) o q >> 1                       by weak_mult_cons
*)
val weak_mult_cons_comm = store_thm(
  "weak_mult_cons_comm",
  ``!r:'a ring. Ring r ==> !p q h. h IN R /\ weak p /\ weak (h::q) ==> (p o (h::q) = (h o p) || ((p o q) >> 1))``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  rw_tac std_ss[weak_cons] >>
  Cases_on `p = []` >-
  rw[weak_mult_const_cons] >>
  Cases_on `q = []` >-
  rw[weak_mult_cons_const] >>
  `weak (h o q) /\ weak (h' o p) /\ weak (p o q)` by rw[] >>
  `!p. weak p ==> weak (p >> 1)` by rw[] >>
  `p <> |0| /\ q <> |0|` by rw_tac std_ss[poly_zero] >>
  `h' o p <> |0| /\ h o q <> |0|` by rw_tac std_ss[weak_cmult_eq_zero] >>
  `h' o p || (p o q) >> 1 <> |0| /\ h o q || p o q >> 1 <> |0|` by rw_tac std_ss[weak_add_eq_zero] >>
  `(h::p) o (h'::q) = (h * h':: h o q) || (h' o p || (p o q) >> 1) >> 1` by rw[] >>
  `_ = h' * h + #0 :: h o q || h' o p || p o q >> 1` by rw[poly_shift_1, weak_add_assoc, ring_mult_comm] >>
  `_ = h' * h + #0 :: h' o p || h o q || p o q >> 1` by rw_tac std_ss[weak_add_comm] >>
  rw[weak_add_assoc, poly_shift_1]);

(* Theorem: [Cross-multiplication]
            (h::p) * (k::q) = [h * k] + k * (p >> 1) + h * (q >> 1) + (p >> 1) * (q >> 1) *)
(* Proof:
   Case p = [] or q = [] is weak_cmult_cons.
   Case h = #0 is almost weak_mult_cons_comm.
   Case k = #0 is almost weak_mult_cons.
   Assume h <> #0 and k <> #0,
     (h::p) * (k::q)
   = h * (k::q) + (p * (k::q)) >> 1                         by weak_mult_cons
   = [h * k] + (h * q) >> 1 + (p * (k::q)) >> 1             by weak_cmult_cons_eq_add_shift
   = [h * k] + ((h * q) >> 1 + (p * (k::q)) >> 1)           by weak_add3_const_assoc
   = [h * k] + ((h * q) >> 1 + (k * p + (p * q) >> 1) >> 1) by weak_mult_cons_comm
   = [h * k] + ((h * q) >> 1 + ((k * p) >> 1 + ((p * q) >> 1) >> 1))  by weak_add_shift_1
   = [h * k] + (h * q) >> 1 + ((k * p) >> 1 + (p * q) >> 1) >> 1))    by weak_add4_const_assoc

   Note: [h*k] may not be a polynomial, e.g. [#0], but [h*k] + ... will do the chop automatically.
   However, [h*k] not being a polynomial affects application of weak_add_assoc or weak_add_comm -- they need polynomials!
   So one must prove version of weak_add_assoc and weak_add_comm when one is a zerop polynomial.
*)
(* Proof:
     (h::p) o (k::q)
   = h o (k::q) || (p o (k::q)) >> 1                                     by weak_mult_cons
   = [h * k] || (h o q) >> 1 || (p o (k::q)) >> 1                        by weak_cmult_cons_eq_add_shift
   = [h * k] || ((h o q) >> 1 || (p o (k::q)) >> 1)                      by weak_add_assoc
   = [h * k] || ((h o q) >> 1 || (k o p || (p o q) >> 1) >> 1)           by weak_mult_cons_comm
   = [h * k] || ((h o q) >> 1 || ((k o p) >> 1 || ((p o q) >> 1) >> 1))  by weak_add_shift_1
   = [h * k] || (((h o q) >> 1 || (k o p) >> 1 || ((p o q) >> 1) >> 1))  by weak_add_assoc
   = [h * k] || (h o q) >> 1 || (k o p) >> 1 || ((p o q) >> 1) >> 1      by weak_add_assoc, weak_add_weak
*)
val weak_mult_cross = store_thm(
  "weak_mult_cross",
  ``!r:'a ring. Ring r ==> !h k p q. weak (h::p) /\ weak (k::q) ==>
   ((h::p) o (k::q) = [h * k] || (h o q) >> 1 || (k o p) >> 1 || ((p o q) >> 1) >> 1)``,
  rw_tac std_ss[weak_cons] >>
  `weak (h::p) /\ weak (k::q)` by rw[] >>
  `weak [h * k] /\ weak (h o q) /\ weak (k o p) /\ weak (p o q)` by rw[] >>
  `!t. weak t ==> weak (t >> 1)` by rw[] >>
  `(h::p) o (k::q) = [h * k] || ((h o q) >> 1 || (p o (k::q)) >> 1)`
    by rw[weak_add_assoc, weak_cmult_cons_eq_add_shift] >>
  rw[weak_add_assoc, weak_mult_cons_comm, weak_add_shift_1]);

(* This is overcoming a major hundle! Next is simple. *)

(* Theorem: p o q = q o p. *)
(* Proof: by induction on p, q and weak_mult_cross.
   Base: [] o q = q o []
      true by weak_mult_of_lzero, weak_mult_of_rzero.
   Step: induct on q.
      Base: (h::p) o [] = [] o (h::p)
         true by weak_mult_of_rzero, weak_mult_of_lzero.
      Step: p o q = q o p ==> !h h'. (h::p) o (h'::q) = (h'::q) o (h::p)
     (h::p) o (h'::q)
   = [h * h'] || (h o q) >> 1 || (h' o p) >> 1 || ((p o q) >> 1) >> 1       by weak_mult_cross
   = [h * h'] || ((h o q) >> 1 || (h' o p) >> 1 || ((p o q) >> 1) >> 1)     by weak_add4_const_assoc
   = [h * h'] || ((h o q) >> 1 || (h' o p) >> 1 || ((q o p) >> 1) >> 1)     by induction hypothesis
   = [h * h'] || ((h' o p) >> 1 || (h o q) >> 1 || ((q o p) >> 1) >> 1)     by weak_add_comm
   = [h * h'] || (h' o p) >> 1 || (h o q) >> 1 || ((q o p) >> 1) >> 1       by weak_add4_const_assoc
   = [h' * h] || (h' o p) >> 1 || (h o q) >> 1 || ((q o p) >> 1) >> 1       by ring_mult_comm
   = (h'::q) o (h::p)                                                       by weak_mult_cross
*)
val weak_mult_comm = store_thm(
  "weak_mult_comm",
  ``!r:'a ring. Ring r ==> !p q:'a poly. weak p /\ weak q ==> (p o q = q o p)``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  strip_tac >>
  Induct >-
  rw[] >>
  rw_tac std_ss[weak_cons] >>
  `weak (h::p) /\ weak (h'::q)` by rw[] >>
  `weak (h o q) /\ weak (h' o p) /\ weak (p o q) /\ weak (q o p)` by rw[] >>
  `weak [h * h'] /\ weak [h' * h]` by rw[] >>
  `!t. weak t ==> weak (t >> 1)` by rw[] >>
  `(h::p) o (h'::q) = [h * h'] || ((h o q) >> 1 || (h' o p) >> 1 || ((p o q) >> 1) >> 1)` by rw[weak_add_assoc, weak_mult_cross] >>
  `_ = [h * h'] || ((h o q) >> 1 || (h' o p) >> 1 || ((q o p) >> 1) >> 1)` by metis_tac[] >>
  `_ = [h * h'] || ((h' o p) >> 1 || (h o q) >> 1 || ((q o p) >> 1) >> 1)` by rw_tac std_ss[weak_add_comm] >>
  rw[weak_mult_cross, weak_add_assoc, ring_mult_comm]);

(* no export of commutativity. *)
(* val _ = export_rewrites ["weak_mult_comm"]; *)

(* Theorem: p o (c o q) = (c o p) o q  *)
(* Proof:
     p o (c o q)
   = (c o q) o p    by weak_mult_comm
   = c o (q o p)    by weak_cmult_mult
   = c o (p o q)    by weak_mult_comm
   = (c o p) o q    by weak_cmult_mult
*)
val weak_mult_cmult = store_thm(
  "weak_mult_cmult",
  ``!r:'a ring. Ring r ==> !c. c IN R ==> !p q. weak p /\ weak q ==> (p o (c o q) = (c o p) o q)``,
  rpt strip_tac >>
  `p o (c o q) = (c o q) o p` by rw[weak_mult_comm] >>
  rw[weak_cmult_mult, weak_mult_comm]);

(* Theorem: (p o q) >> 1 = (p >> 1) o q *)
(* Proof: by weak_mult_shift_1 and weak_mult_comm.
     (p o q) >> 1
   = (q o p) >> 1    by weak_mult_comm
   = q o (p >> 1)    by weak_mult_shift_1
   = (p >> 1) o q    by weak_mult_comm
*)
val weak_mult_shift_1_comm = store_thm(
  "weak_mult_shift_1_comm",
  ``!r:'a ring. Ring r ==> !p q:'a poly. weak p /\ weak q ==> ((p o q) >> 1 = (p >> 1) o q)``,
  rw[GSYM weak_mult_shift_1, weak_mult_comm]);

(* Only shift_1 is required for poly_mult_shift_1 and general shift. *)

(* ------------------------------------------------------------------------- *)
(* Theorems on polynomial multiplication distributes over addition.          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: p o (q || t) = p o q || p o t *)
(* Proof: by induction on p.
   Base: [] o (q || t) = [] o q || [] o t
      LHS = [] o (q || t) = []                            by weak_mult_of_lzero
      RHS = [] o q || [] o t = [] || [] = [] = LHS  by weak_mult_of_lzero, weak_add_of_zero_zero
   Step: p o (q || t) = p o q || p o t ==> (h::p) o (q || t) = (h::p) o q || (h::p) o t
     (h::p) o (q || t)
   = h o (q || t) || (p o (q || t)) >> 1                  by weak_mult_cons
   = (h o q || h o t) || (p o (q || t)) >> 1              by weak_cmult_add
   = (h o q || h o t) || (p o q || p o t) >> 1            by induction hypothesis
   = (h o q || h o t) || ((p o q) >> 1 || (p o t) >> 1)   by weak_add_shift_1
   = h o q || (h o t || ((p o q) >> 1 || (p o t) >> 1))   by weak_add_assoc
   = h o q || (h o t || (p o q) >> 1 || (p o t) >> 1)     by weak_add_assoc
   = h o q || ((p o q) >> 1 || h o t || (p o t) >> 1)     by weak_add_comm
   = h o q || ((p o q) >> 1 || (h o t || (p o t) >> 1))   by weak_add_assoc
   = (h o q || (p o q) >> 1) || (h o t || (p o t) >> 1)   by weak_add_assoc
   = (h::p) o q || (h::p) o t                             by weak_mult_cons
*)
val weak_mult_radd = store_thm(
  "weak_mult_radd",
  ``!r:'a ring. Ring r ==>
    !p q t:'a poly. weak p /\ weak q /\ weak t ==> (p o (q || t) = p o q || p o t)``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  rw_tac std_ss[weak_cons] >>
  `weak (h o q) /\ weak (h o t) /\ weak (p o q) /\ weak (p o t)` by rw[] >>
  `weak ((p o q) >> 1) /\ weak ((p o t) >> 1)` by rw[] >>
  `(h::p) o (q || t) = h o q || (h o t || (p o q) >> 1 || (p o t) >> 1)`
     by rw[weak_cmult_add, weak_add_shift_1, weak_add_assoc] >>
  `_ = h o q || ((p o q) >> 1 || h o t || (p o t) >> 1)` by rw_tac std_ss[weak_add_comm] >>
  rw[weak_add_assoc]);

(* Theorem: (p || q) o t = p o t || q o t *)
(* Proof: by weak_mult_comm and weak_mult_radd.
     (p || q) o t
   = t o (p || q)        by weak_mult_comm
   = t o p || t o q      by weak_mult_radd
   = p o t || q o t      by weak_mult_comm
*)
val weak_mult_ladd = store_thm(
  "weak_mult_ladd",
  ``!r:'a ring. Ring r ==> !p q t:'a poly. weak p /\ weak q /\ weak t ==> ((p || q) o t = p o t || q o t)``,
  rw[weak_mult_radd, weak_mult_comm]);

val _ = export_rewrites ["weak_mult_radd", "weak_mult_ladd"];

(* Theorem: p o (q || t) = p o q || p o t /\ (p || q) o t = p o t || q o t *)
(* Proof: by weak_mult_radd and weak_mult_ladd. *)
Theorem weak_mult_add =
    CONJ (weak_mult_radd |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL |> UNDISCH_ALL)
         (weak_mult_ladd |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL |> UNDISCH_ALL)
      |> DISCH “weak p /\ weak q /\ weak t” |> GEN “(t:'a poly)”
      |> GEN “(q:'a poly)” |> GEN “(p:'a poly)”
      |> DISCH_ALL |> GEN_ALL;
(* > val weak_mult_add = |- !r. Ring r ==> !p q t. weak p /\ weak q /\ weak t ==>
         (p o (q || t) = p o q || p o t) /\ ((p || q) o t = p o t || q o t) : thm *)

(* ------------------------------------------------------------------------- *)
(* Associativity of weak polynomial multiplication.                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (p o q) o t = p o (q o t). *)
(* Proof: by induction on p.
   Base: ([] o q) o t = [] o q o t
      true by weak_mult_of_lzero.
   Step: (p o q) o t = p o q o t ==> ((h::p) o q) o t = (h::p) o q o t
     ((h::p) o q) o t
   = ((h o q) || (p o q) >> 1) o t         by weak_mult_cons
   = (h o q) o t || ((p o q) >> 1) o t     by weak_mult_ladd
   = h o (q o t) || ((p o q) >> 1) o t     by weak_cmult_mult
   = h o (q o t) || ((p o q) o t) >> 1     by weak_mult_shift_1_comm
   = h o (q o t) || (p o (q o t)) >> 1     by induction hypothesis
   = (h::p) o (q o t)                      by weak_mult_cons_comm
*)
val weak_mult_assoc = store_thm(
  "weak_mult_assoc",
  ``!r:'a ring. Ring r ==> !p q t:'a poly. weak p /\ weak q /\ weak t ==> ((p o q) o t = p o (q o t))``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  rw_tac std_ss[weak_cons] >>
  `weak (h::p) /\ weak (h o q) /\ weak (p o q) /\ weak (q o t)`
    by rw_tac std_ss[weak_cons, weak_cmult_weak, weak_mult_weak] >>
  `weak ((p o q) >> 1) /\ weak ((q o t) >> 1)` by rw_tac std_ss[poly_shift_weak] >>
  `((h::p) o q) o t = h o (q o t) || ((p o q) >> 1) o t`
    by rw_tac std_ss[weak_mult_ladd, weak_mult_cons, weak_cmult_mult] >>
  `_ = h o (q o t) || ((p o q) o t) >> 1` by rw_tac std_ss[weak_mult_shift_1_comm] >>
  rw[]);

(* no export of associativity *)
(* val _ = export_rewrites ["weak_mult_assoc"]; *)

(* Theorem: Polynomial multiplication clauses. *)
(* Proof: by theorems proved. *)
val weak_mult_clauses = store_thm(
  "weak_mult_clauses",
  ``!r:'a ring. Ring r ==> !p q t :'a poly. weak p /\ weak q /\ weak t ==>
      ([] o p = []) /\ (p o [] = []) /\ (p o q = q o p) /\ ((p o q) o t = p o (q o t))``,
  rw[weak_mult_comm, weak_mult_assoc]);

(* ------------------------------------------------------------------------- *)
(* Theorems on polynomial multiplicative identity.                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: [#1] <> [] *)
(* Proof: since [#1] <> []. *)
val weak_one_ne_zero = store_thm(
  "weak_one_ne_zero",
  ``[#1] <> []``,
  rw[]);

(* Theorem: weak [#1] *)
(* Proof: by weak_const. *)
val weak_one = store_thm(
  "weak_one",
  ``!r:'a ring. Ring r ==> weak [#1]``,
  rw[]);

val _ = export_rewrites ["weak_one_ne_zero", "weak_one"];

(* Theorem: weak |1| *)
(* Proof:
   Note |1| = if #1 = #0 then [] else [#1]   by poly_one
   If #1 = #0, weak []           by weak_of_zero
   If #1 <> #0, weak [#1]        by weak_one
*)
val weak_one_poly = store_thm(
  "weak_one_poly",
  ``!r:'a ring. Ring r ==> weak |1|``,
  rw_tac std_ss[poly_one, weak_of_zero, weak_one]);

(* Theorem: c o [#1] = [c] *)
(* Proof: by weak_cmult_cons.
      c o [#1]
   = (c * #1::c o [])     by weak_cmult_cons
   = [c * #1]             by weak_cmult_of_zero
   = [c]                  by ring_mult_rone
*)
val weak_cmult_one = store_thm(
  "weak_cmult_one",
  ``!r:'a ring. Ring r ==> !c. c IN R ==> (c o [#1] = [c])``,
  rw[]);

(* Theorem: #1 o p = p *)
(* Proof: by induction on p.
   Base: #1 o [] = []
      true by weak_cmult_of_zero.
   Step: #1 o p = p ==> #1 o (h::p) = h::p
     #1 o (h::p)
   = (#1 * h :: #1 o p)    by weak_cmult_cons
   = (h:: #1 o p)          by ring_mult_lone
   = (h::p)                by induction hypothesis
*)
val weak_cmult_lone = store_thm(
  "weak_cmult_lone",
  ``!r:'a ring. Ring r ==> !p. weak p ==> (#1 o p = p)``,
  strip_tac >>
  strip_tac >>
  Induct >>
  rw[]);

val _ = export_rewrites ["weak_cmult_one", "weak_cmult_lone"];

(* Theorem: [#1] o p = p *)
(* Proof:
     [#1] o p
   = #1 o p     by weak_mult_const
   = p          by weak_cmult_lone
*)
val weak_mult_lone = store_thm(
  "weak_mult_lone",
  ``!r:'a ring. Ring r ==> !p. weak p ==> ([#1] o p = p)``,
  rw[]);

(* Theorem: p o [#1] = p *)
(* Proof:
      p o [#1]
   = [#1] o p      by weak_mult_comm, weak_one
   = p             by weak_mult_lone
*)
val weak_mult_rone = store_thm(
  "weak_mult_rone",
  ``!r:'a ring. Ring r ==> !p. weak p ==> (p o [#1] = p)``,
  rw[Once weak_mult_comm]);

val _ = export_rewrites ["weak_mult_lone", "weak_mult_rone"];

(* Theorem: [#1] o p = p  and  p o [#1] = p  *)
(* Proof: combine weak_mult_lone and weak_mult_rone. *)
(* val weak_mult_one = save_thm("weak_mult_one", CONJ weak_mult_lone weak_mult_rone); *)
(* > val weak_mult_one = |- (!r. Ring r ==> !p. weak p ==> ([#1] o p = p)) /\ !r. Ring r ==> !p. weak p ==> (p o [#1] = p) : thm *)
val weak_mult_one = store_thm(
  "weak_mult_one",
  ``!r:'a ring. Ring r ==> !p. weak p ==> ([#1] o p = p) /\ (p o [#1] = p)``,
  rw[]);

(* Note: Only at this point can Monoid (monoid_weak_mult r) be established. *)

(* ------------------------------------------------------------------------- *)
(* Polynomial leading coefficient.                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: lead [h] = h *)
(* Proof: by definition. *)
val poly_lead_const = store_thm(
  "poly_lead_const",
  ``!h. lead [h] = h``,
  rw[poly_lead_def]);

val _ = export_rewrites ["poly_lead_const"];

(* Theorem: lead [] = #0 *)
(* Proof: by definition. *)
val poly_lead_of_zero = save_thm("poly_lead_of_zero", poly_lead_def |> CONJUNCT1);
(* > val poly_lead_of_zero = |- !r. lead [] = #0 : thm *)

val _ = export_rewrites ["poly_lead_of_zero"];

(* Theorem: lead |0| = #0 *)
(* Proof: by poly_lead_of_zero and poly_zero. *)
val poly_lead_zero = save_thm("poly_lead_zero", poly_lead_of_zero |> REWRITE_RULE [GSYM poly_zero]);
(* > val poly_lead_zero = |- !r. lead |0| = #0 *)

val _ = export_rewrites ["poly_lead_zero"];

(* Theorem: lead |1| = #1 *)
(* Proof:
   If #1 = #0,
      |1| = []                   by poly_one
      lead |1| = lead [] = #0    by poly_lead_of_zero
   If #1 <> #0,
      |1| = [#1]                 by poly one
      lead |1| = lead [#1] = #1  by poly_lead_const
*)
val poly_lead_one = store_thm(
  "poly_lead_one",
  ``!r:'a ring. Ring r ==> (lead |1| = #1)``,
  rw [poly_one]);

(* export simple result *)
val _ = export_rewrites ["poly_lead_one"];

(* Theorem: p <> |0| ==> lead p = LAST p *)
(* Proof: by definition. *)
val poly_lead_alt = store_thm(
  "poly_lead_alt",
  ``!p. p <> |0| ==> (lead p = LAST p)``,
  metis_tac[poly_lead_def, list_CASES, poly_zero]);

val _ = export_rewrites ["poly_lead_alt"];

(* Theorem: p <> |0| ==> lead p = EL (deg p) p *)
(* Proof:
      lead p
    = LAST p                 by poly_lead_alt
    = EL (PRE (LENGTH p))    by LAST_EL, p <> []
    = EL (deg p) p           by poly_deg_def
*)
val poly_lead_at_deg_index = store_thm(
  "poly_lead_at_deg_index",
  ``!p. p <> |0| ==> (lead p = EL (deg p) p)``,
  rw[poly_lead_alt, poly_deg_def, LAST_EL]);

(* Theorem: t <> |0| ==> lead (h::t) = lead t *)
(* Proof: by LAST (x::y::z) = LAST (y::z). *)
val poly_lead_cons = store_thm(
  "poly_lead_cons",
  ``!h t. t <> |0| ==> (lead (h::t) = lead t)``,
  metis_tac[poly_lead_def, poly_lead_alt, LAST_CONS, list_CASES, poly_zero]);

val _ = export_rewrites ["poly_lead_cons"];

(* Theorem: zerop p ==> (lead p = #0) *)
(* Proof:
   By induction on p.
   Base: zerop [] ==> (lead [] = #0)
      True by poly_lead_of_zero.
   Step: zerop p ==> (lead p = #0) ==> !h. zerop (h::p) ==> (lead (h::p) = #0)
      Note h = #0 /\ zerop p    by zero_poly_cons
      If p = |0|,
         Then lead [h]
             = h = #0           by poly_lead_cons
      If p <> |0|,
         Then lead (h::p)
            = lead p            by poly_lead_cons
            = #0                by induction hypothesis
*)
val zero_poly_lead = store_thm(
  "zero_poly_lead",
  ``!r:'a ring. !p. zerop p ==> (lead p = #0)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[zero_poly_cons] >>
  Cases_on `p = |0|` >>
  rw[]);

(* Theorem: lead (p >> n) = lead p *)
(* Proof:
   If p = |0|,
      |0| >> n = |0|   by poly_shift_zero
      hence true by poly_lead_zero.
   If p <> |0|,
      p >> n <> |0|    by poly_shift_eq_zero
        lead (p >> n)
      = LAST (p >> n)  by poly_lead_alt, p >> n <> |0|
      = LAST p         by poly_shift_last
      = lead p         by poly_lead_alt, p <> |0|
*)
val poly_lead_shift = store_thm(
  "poly_lead_shift",
  ``!p n. lead (p >> n) = lead p``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[] >>
  rw[poly_shift_eq_zero, poly_shift_last]);

val _ = export_rewrites ["poly_lead_shift"];

(* Theorem: weak p ==> lead p IN R. *)
(* Proof: by induction on p.
   Base: lead [] IN R
      true by poly_lead_of_zero, ring_zero_element.
   Step: lead p IN R ==> lead (h::p) IN R
      If p = |0|, lead [h] = h  by poly_lead_const
      If p <> |0|,
      lead (h::p) = lead p      by poly_lead_cons, p <> |0|
      hence lead (h::p) IN R    by induction hypothesis
*)
val weak_lead_element = store_thm(
  "weak_lead_element",
  ``!r:'a ring. Ring r ==> !p. weak p ==> lead p IN R``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw_tac std_ss[poly_lead_of_zero, ring_zero_element] >>
  rw_tac std_ss[weak_cons] >>
  Cases_on `p = |0|` >-
  rw[] >>
  rw_tac std_ss[poly_lead_cons]);

val _ = export_rewrites["weak_lead_element"];

(* ------------------------------------------------------------------------- *)
(* Polynomial Normalization.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: chop [] = [] *)
(* Proof: by definition. *)
val poly_chop_of_zero = save_thm("poly_chop_of_zero", poly_chop_def |> CONJUNCT1);
(* > val poly_chop_of_zero = |- !r. chop [] = [] : thm *)

(* This is useful. *)
(* definition already exported *)
(* val _ = export_rewrites ["poly_chop_of_zero"]; *)

(* Theorem: chop (h::t) = if zerop (h::t) then [] else (h::%t) *)
(* Proof: by definition. *)
val poly_chop_cons = save_thm("poly_chop_cons", poly_chop_def |> CONJUNCT2);
(* > val poly_chop_cons = |- !r h t. chop (h::t) = if zerop (h::t) then [] else h:: chop t : thm *)

(* This leads to resolving zerop (h::t), no good. But this is useful, use it. *)
(* definition already exported *)
(* val _ = export_rewrites ["poly_chop_cons"]; *)

(* Theorem: LENGTH (chop p) <= LENGTH p *)
(* Proof:
   By induction on p.
   Base: LENGTH (chop []) <= LENGTH []
      True since chop [] = []            by poly_chop_of_zero
   Step: LENGTH (chop p) <= LENGTH p ==> !h. LENGTH (chop (h::p)) <= LENGTH (h::p)
      If zerop (h::t),
         LENGTH (chop (h::p))
       = LENGTH []              by poly_chop_def
       = 0                      by LENGTH
       <= LENGTH (h::p)         by LENGTH
      If ~(zerop (h::t)),
         LENGTH (chop (h::p))
       = LENGTH (h::chop p)     by poly_chop_def
       = SUC (LENGTH (chop p))  by LENGTH
       <= SUC (LENGTH p)        by induction hypothesis
        = LENGTH (h::p)         by LENGTH
*)
val poly_chop_length = store_thm(
  "poly_chop_length",
  ``!p:'a poly. LENGTH (chop p) <= LENGTH p``,
  Induct >>
  rw[poly_chop_def]);

(* Theorem: zerop p ==> (chop p = |0|) *)
(* Proof:
   By induction on p.
   Base: zerop [] ==> (chop [] = |0|)
        True by poly_chop_of_zero, poly_zero.
   Step: zerop p ==> (chop p = |0|) ==> !h. zerop (h::p) ==> (chop (h::p) = |0|)
        True by poly_chop_cons, poly_zero.
*)
val poly_chop_zero_poly = store_thm(
  "poly_chop_zero_poly",
  ``!p. zerop p ==> (chop p = |0|)``,
  Induct >>
  rw[]);

(* Theorem: chop |0| = |0| *)
(* Proof: by poly_chop_of_zero and poly_zero. *)
val poly_chop_zero = save_thm("poly_chop_zero", poly_chop_of_zero |> REWRITE_RULE [GSYM poly_zero]);
(* > val poly_chop_zero = |- !r. chop |0| = |0| : thm *)

val _ = export_rewrites ["poly_chop_zero"];

(* Theorem: zerop p <=> chop p = [] *)
(* Proof: by definition and cases on p. *)
val zero_poly_chop = store_thm(
  "zero_poly_chop",
  ``!p:'a poly. zerop p <=> (chop p = [])``,
  rpt strip_tac >>
  Cases_on `p` >>
  rw[]);

(* for export_rewrites: use equation *)
(* val _ = export_rewrites ["zero_poly_chop"]; *)
(* However, this will rewrite all "zerop" stuff to "chop", no good. *)

(* Theorem: chop (chop p) = chop p *)
(* Proof: by induction.
   Base: chop (chop []) = chop []
      true by poly_chop_of_zero.
   Step: chop (chop p) = chop p ==> !h. chop (chop (h::p)) = chop (h::p)
      true by poly_chop_cons: if zero, zero_poly_chop gives [], so poses no problem;
                              if ~zero, chop operator can pass to tail, true by induction hypothesis.
*)
val poly_chop_chop = store_thm(
  "poly_chop_chop",
  ``!p:'a poly. chop (chop p) = chop p``,
  Induct >>
  rw[zero_poly_chop]);

(* This is a useful equality. *)
val _ = export_rewrites ["poly_chop_chop"];

(* Theorem: weak p ==> weak (chop p) *)
(* Proof: by induction on p.
   Base: weak (chop [])
      true by poly_chop_of_zero
   Step: weak p ==> weak (chop p) ==>
              !h. weak (h::p) ==> weak (chop (h::p))
      if zerop (h::p),
         then chop (h::p) = [] by poly_chop_cons,
         hence true by zero_poly_poly.
      if ~ zerop (h::p),
         then chop (h::p) = (h::%p) by poly_chop_cons,
         and weak (%p)         by induction hypothesis
         If chop p = [],
            then zerop p       by poly_chop_is_zero
            hence h <> #0      by zero_poly_cons
            so chop (h::p) = [h],
            and weak [h]       by weak_nonzero_element_poly.
         If ~ p <> [],
         then  ~ zerop (chop p)    by weak_cons_not_zero
         and   ~ zerop (h::%p)     by zero_poly_cons
         hence true by weak_cons, since h is known to be in R.
*)
val poly_chop_weak = store_thm(
  "poly_chop_weak",
  ``!p:'a poly. weak p ==> weak (chop p)``,
  Induct >>
  rw[]);

(* Theorem: zerop p <=> zerop (chop p) *)
(* Proof:
       zerop p
   <=> chop p = []          by zero_poly_chop
   <=> chop (chop p) = []   by poly_chop_chop
   <=> zerop (chop p)       by zero_poly_chop
*)
val zero_poly_eq_zero_poly_chop = store_thm(
  "zero_poly_eq_zero_poly_chop",
  ``!p. zerop p <=> zerop (chop p)``,
  rw[zero_poly_chop]);

(* Theorem: (LENGTH p = LENGTH q) ==> ((chop p = chop q) <=> (p = q)) *)
(* Proof:
   If part: chop p = chop q ==> p = q
      By induction on p.
      Base: (LENGTH [] = LENGTH q) ==> (chop [] = chop q) ==> ([] = q)
         Note q = []           by LENGTH_NIL
         Thus true.
      Step: !q. (LENGTH p = LENGTH q) ==> (chop p = chop q) ==> (p = q) ==>
            !h. (LENGTH (h::p) = LENGTH q) ==> (chop (h::p) = chop q) ==> (h::p = q)

         If zerop (h::p),
            Then chop (h::p) = []           by poly_chop_def
              so chop q = []                by chop (h::p) = chop q
              or zerop q                    by zero_poly_chop
            With LENGTH (h::p) = LENGTH q   by given
             ==> h::p = q                   by zero_poly_eq_zero_poly
         If ~zerop (h::p),
            Then chop (h::p) = h :: chop p  by poly_chop_def [1]
            Note ?k t. q = k::t             by LENGTH_NIL, NOT_NIL_CONS
             and ~zerop (k::t)              by zero_poly_chop
            Thus chop q = k :: chop t       by poly_chop_def [2]
             ==> (h = k) /\ (chop p = chop t)     by CONS_11, [1], [2]
           Since  LENGTH (h::p) = SUC (LENGTH p)  by LENGTH
             and  LENGTH (k::t) = SUC (LENGTH t)  by LENGTH
            Thus SUC (LENGTH p) = SUC (LENGTH t)  by given LENGTH (h::p) = LENGTH q
              or       LENGTH p = LENGTH t        by SUC_EQ
           Giving             p = t               by induction hypothesis
            Hence          h::p = k::t = q        by EQ_LIST

   Only-if part: p = q ==> chop p = chop q
      True trivially.
*)
val poly_chop_eq_chop = store_thm(
  "poly_chop_eq_chop",
  ``!r:'a ring. !p q. (LENGTH p = LENGTH q) ==> ((chop p = chop q) <=> (p = q))``,
  rw[EQ_IMP_THM] >>
  ntac 2 (pop_assum mp_tac) >>
  qid_spec_tac `q` >>
  Induct_on `p` >-
  metis_tac[LENGTH_NIL] >>
  rpt strip_tac >>
  Cases_on `zerop (h::p)` >| [
    `chop q = []` by metis_tac[poly_chop_def] >>
    `zerop q` by rw[zero_poly_chop] >>
    metis_tac[zero_poly_eq_zero_poly],
    `chop (h::p) = h :: chop p` by metis_tac[poly_chop_def] >>
    `?k t. q = k::t` by metis_tac[LENGTH_NIL, NOT_NIL_CONS, list_CASES] >>
    `~zerop (k::t)` by metis_tac[zero_poly_chop] >>
    `chop q = k :: chop t` by rw[poly_chop_def] >>
    `(h = k) /\ (chop p = chop t)` by metis_tac[CONS_11] >>
    `p = t` by metis_tac[LENGTH, SUC_EQ] >>
    rw[]
  ]);

(* Theorem: Ring r ==> !p. weak p ==> (chop p = p * |1|) *)
(* Proof:
   If #1 = #0,
      Then |1| = |0|      by poly_one_eq_poly_zero
      Thus zerop p        by weak_all_zero_poly
       and chop p = |0|   by poly_chop_zero_poly
      Also p * |1|
         = p * |0|
         = chop (p o |0|) by poly_mult_def
         = chop |0|       by weak_mult_rzero
         = |0|            by poly_chop_zero
   If #1 <> #0,
      Then |1| = [#1]     by poly_one
     chop p
   = chop (p o |1|)       by weak_mult_rone
   = p * |1|              by poly_mult_def
*)
val poly_chop_weak_alt = store_thm(
  "poly_chop_weak_alt",
  ``!r:'a ring. Ring r ==> !p. weak p ==> (chop p = p * |1|)``,
  rpt strip_tac >>
  Cases_on `#1 = #0` >| [
    `|1| = |0|` by rw[poly_one_eq_poly_zero] >>
    `zerop p` by metis_tac[weak_all_zero_poly] >>
    `chop p = |0|` by rw[poly_chop_zero_poly] >>
    metis_tac[weak_mult_rzero, poly_mult_def, poly_chop_zero],
    metis_tac[weak_mult_rone, poly_mult_def, poly_one]
  ]);

(* Theorem: chop (p || q) = chop (chop p || q) *)
(* Proof: almost by poly_chop_chop. Use induction.
   Base: chop ([] || q) = chop (chop [] || q)
      true by poly_chop_of_zero.
   Step: induct on q.
      Base: chop ((h::p) || []) = chop (chop (h::p) || [])
         true by weak_add_of_rzero, poly_chop_chop.
      Step: chop (p || q) = chop (chop p || q) ==> !h h'. chop ((h::p) || (h'::q)) = chop (chop (h::p) || (h'::q))
      If ~ zerop ((h::p) || (h'::q)),
         chop ((h::p) || (h'::q))
       = chop (h + h' :: p || q)                by weak_add_cons
       = (h + h') :: chop (p || q)              by poly_chop_cons
       = (h + h') :: chop (chop p || q)         by induction hypothesis
       = chop ((h :: chop (chop p) || (h'::q))  by poly_chop_cons
       = chop ((h :: (chop p) || (h'::q))       by poly_chop_chop
       = chop (chop (h::p) || (h'::q))          by weak_add_cons
*)
val poly_chop_add = store_thm(
  "poly_chop_add",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q ==> (chop (p || q) = chop (chop p || q))``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  strip_tac >>
  Induct >-
  rw[weak_add_of_rzero, zero_poly_chop] >>
  rw[zero_poly_chop] >-
  metis_tac[ring_add_lzero, weak_add_of_lzero] >>
  metis_tac[ring_add_lzero, weak_add_of_lzero]);

(* Theorem: chop (p || q) = chop (p || chop q) *)
(* Proof:
     chop (p || q)
   = chop (q || p)        by weak_add_comm
   = chop (chop q || p)   by poly_chop_add
   = chop (p || chop q)   by weak_add_comm, poly_chop_weak
*)
val poly_chop_add_comm = store_thm(
  "poly_chop_add_comm",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q ==> (chop (p || q) = chop (p || chop q))``,
  metis_tac[weak_add_comm, poly_chop_add, poly_chop_weak]);

(* Theorem: chop (p || q) = chop (chop p || chop q) *)
(* Proof:
     chop (p || q)
   = chop (chop p || q)       by poly_chop_add
   = chop (chop p || chop q)  by poly_chop_add_comm, poly_chop_weak
*)
val poly_chop_add_chop = store_thm(
  "poly_chop_add_chop",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q ==> (chop (p || q) = chop (chop p || chop q))``,
  metis_tac[poly_chop_add, poly_chop_add_comm, poly_chop_weak]);

(* useful transformations. *)
val _ = export_rewrites ["poly_chop_add", "poly_chop_add_comm", "poly_chop_add_chop"];

(* Note: chop (c o p) = c o chop p  is wrong!
         In Z_6, take c = 2, p = [0;3;0]. LHS is not poly, RHS is weak (always by chop).
*)

(* Theorem: chop (c o p) = chop (c o chop p) *)
(* Proof: by induction on p.
   Base: weak [] ==> !c::(R). chop (c o []) = chop (c o chop [])
      True by poly_chop_of_zero and weak_cmult_of_zero.
   Step: weak p ==> !c::(R). chop (c o p) = chop (c o chop p) ==>
             !h. weak (h::p) ==> !c::(R). chop (c o (h::p)) = chop (c o chop (h::p)
      If zerop (h::p), then zerop (c o (h::p))   by zero_poly_cmult
      LHS = c o chop (h::p)
          = c o []                  by poly_chop_cons, zerop (h::p)
          = []                      by weak_cmult_of_zero
          = chop (c o (h::p))       by zero_poly_chop, zerop (c o (h::p))
          = RHS
      If ~zerop (h::p),
      LHS = c o chop (h::p)
          = c o (h::chop p)         by poly_chop_cons, ~zerop (h::p)
          = c * h :: c o chop p     by weak_cmult_cons
          = c * h :: chop (c o p)   by induction hypothesis
          = chop (c * h :: c o p)   by poly_chop_cons, ~zerop (c o p)
          = chop (c o (h::p))       by weak_cmult_cons
          = RHS
*)
val poly_chop_cmult = store_thm(
  "poly_chop_cmult",
  ``!r:'a ring. Ring r ==> !p:'a poly. weak p ==> !c. c IN R ==> (chop (c o p) = chop (c o chop p))``,
  strip_tac >>
  strip_tac >>
  Induct >>
  rw[zero_poly_chop]);

val _ = export_rewrites ["poly_chop_cmult"];

(* Theorem: chop (neg p) = neg (chop p) *)
(* Proof: by induction on p.
   Base: weak [] ==> chop (neg []) = neg (chop []
      true by weak_neg_of_zero, poly_chop_of_zero.
   Step: weak p ==> chop (neg p) = neg (chop p) ==> !h. weak (h::p) ==> chop (neg (h::p)) = neg (chop (h::p))
     chop (neg (h::p))
   = chop (-h::neg p)     by weak_neg_cons
   = -h :: chop (neg p)   by poly_chop_cons, zero_weak_neg
   = -h :: neg (chop p)   by induction hypothesis
   = neg (h::chop p)      by weak_neg_cons
   = neg (chop (h::p))    by poly_chop_cons
*)
val poly_chop_neg = store_thm(
  "poly_chop_neg",
  ``!r:'a ring. Ring r ==> !p:'a poly. weak p ==> (chop (neg p) = neg (chop p))``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  rw_tac std_ss[GSYM zero_poly_chop, zero_weak_neg, weak_neg_of_zero, weak_neg_cons, poly_chop_cons, weak_cons]);

val _ = export_rewrites ["poly_chop_neg"];

(* Theorem: chop (p >> n) = (chop p) >> n *)
(* Proof:
   If zerop p, to show:
      zerop (p >> n)         by zero_poly_shift
      LHS = []               by zero_poly_chop
          = [] >> n = RHS    by zero_poly_chop, poly_shift_of_zero
   If ~zerop p,
      ~zerop (p >> n)        by zero_poly_shift
      p <> []                by zero_poly_of_zero
      chop <> []             by zero_poly_shift
   By induction on n.
   Base: chop (p >> 0) = chop p >> 0
      true by poly_shift_0.
   Step: chop (p >> n) = chop p >> n ==> chop (p >> SUC n) = chop p >> SUC n
       chop (p >> SUC n)
     = chop (#0:: p >> n)     by poly_shift_suc, p <> []
     = #0::chop (p >> n)      by poly_chop_cons, ~zerop (p >> n)
     = #0::(chop p) >> n      by induction hypothesis
     = (chop p) >> SUC n      by poly_shift_suc, chop p <> []
*)
val poly_chop_shift = store_thm(
  "poly_chop_shift",
  ``!p n. chop (p >> n) = (chop p) >> n``,
  rpt strip_tac >>
  Cases_on `zerop p` >-
  metis_tac[zero_poly_chop, zero_poly_shift, poly_shift_of_zero] >>
  Induct_on `n` >-
  rw[] >>
  `p <> [] /\ chop p <> [] /\ ~zerop (p >> n)`
    by metis_tac[zero_poly_of_zero, zero_poly_chop, zero_poly_shift] >>
  rw[]);

val _ = export_rewrites ["poly_chop_shift"];

(* Theorem: chop (p o q) = chop ((chop p) o q) *)
(* Proof: by induction on p and q.
   Base: chop ([] o q) = chop (chop [] o q)
      true by weak_mult_of_lzero, poly_chop_of_zero.
   Step: chop (p o q) = chop (chop p o q) ==> chop ((h::p) o q) = chop (chop (h::p) o q)
      If zerop (h::p), chop (h::p) = [].
      LHS = chop ((h::p) o q)
          = chop (zerop o q)    by zerop (h::p)
          = chop (zerop)        by zero_weak_lmult
          = []                  by zero_poly_chop
      RHS = chop (chop (h::p) o q)
          = chop ([] o q)       by zero_poly_chop
          = chop []             by weak_mult_of_lzero
          = [] = LHS            by poly_chop_of_zero
      If ~zerop (h::p),
      LHS = chop ((h::p) o q)
          = chop (h o q || (p o q) >> 1)    by weak_mult_cons
      RHS = chop (chop (h::p) o q)
          = chop ((h::chop p) o q)     by poly_chop_cons, ~zerop (h::p)
          = chop (h o q || ((chop p) o q) >> 1)    by weak_mult_cons
          = chop (h o q || chop (((chop p) o q) >> 1))   by poly_chop_add_comm
          = chop (h o q || chop ((chop ((chop p) o q)) >> 1))   by poly_chop_shift
          = chop (h o q || chop ((chop (p o q)) >> 1))          by induction hypothesis
          = chop (h o q || chop ((p o q) >> 1))                 by poly_chop_shift
          = chop (h o q || (p o q) >> 1) = LHS                  by poly_chop_add_comm
*)
val poly_chop_mult = store_thm(
  "poly_chop_mult",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q ==> (chop (p o q) = chop ((chop p) o q))``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  rw_tac std_ss[weak_cons] >>
  Cases_on `zerop (h::p)` >-
  metis_tac[zero_poly_chop, weak_mult_of_lzero, zero_weak_lmult, poly_chop_of_zero] >>
  `weak (h o q) /\ weak (p o q) /\ weak ((p o q) >> 1) /\ weak (((chop p) o q) >> 1)` by rw[poly_chop_weak] >>
  metis_tac[weak_mult_cons, poly_chop_add_comm, poly_chop_shift, poly_chop_cons]);

(* Theorem: chop (p o q) = chop (p o (chop q)) *)
(* Proof:
     chop (p o q)
   = chop (q o p)          by weak_mult_comm
   = chop ((chop q) o p)   by poly_chop_mult
   = chop (p o (chop q))   by weak_mult_comm
*)
val poly_chop_mult_comm = store_thm(
  "poly_chop_mult_comm",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q ==> (chop (p o q) = chop (p o (chop q)))``,
  metis_tac[weak_mult_comm, poly_chop_mult, poly_chop_weak]);

(* Theorem: chop (p o q) = chop ((chop p) o (chop q)) *)
(* Proof:
     chop (p o q)
   = chop ((chop p) o q)          by poly_chop_mult
   = chop ((chop p) o (chop q))   by poly_chop_mult_comm
*)
val poly_chop_mult_chop = store_thm(
  "poly_chop_mult_chop",
  ``!r:'a ring. Ring r ==> !p q. weak p /\ weak q ==> (chop (p o q) = chop ((chop p) o (chop q)))``,
  metis_tac[poly_chop_mult, poly_chop_mult_comm, poly_chop_weak]);

val _ = export_rewrites ["poly_chop_mult", "poly_chop_mult_comm", "poly_chop_mult_chop"];

(* ------------------------------------------------------------------------- *)
(* Simple Normalization Theorems.                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: chop [#0] = |0| *)
(* Proof: by defintion and zero_poly_element_zero, poly_zero. *)
val poly_chop_const_zero = store_thm(
  "poly_chop_const_zero",
  ``chop [#0] = |0|``,
  rw[]);

(* Theorem: Ring r /\ h IN R ==> chop [h] = |0| <=> h = #0 *)
(* Proof:
   If part:  chop [h] = |0|
         ==> zerop [h]           by poly_chop_def
         ==> h = #0              by zero_poly_def
   Only-if part:
             chop [#0] = |0|     by poly_chop_const_zero
*)
val poly_chop_const_eq_zero = store_thm(
  "poly_chop_const_eq_zero",
  ``!(r:'a ring) h. Ring r /\ h IN R ==> ((chop [h] = |0|) <=> (h = #0))``,
  rw[]);

(* Theorem: chop [h] = [h]  if h <> #0 *)
(* Proof: by defintion and zero_poly_cons. *)
val poly_chop_const_nonzero = store_thm(
  "poly_chop_const_nonzero",
  ``!r:'a ring. !h. h IN R /\ h <> #0 ==> (chop [h] = [h])``,
  rw[zero_poly_cons]);

(* This theorem is not used later, but it is the most significant property of chop, the normalizing operator. *)

(* Theorem: chop p <> [] ==> LAST (chop p) <> #0 *)
(* Proof: (idea)
     chop p <> [] = ~ zerop p    by zero_poly_chop
     so there is a nonzero element in p   by zero_poly_every_zero
     and chop just stops at this nonzero element, hence LAST (chop p) <> #0.
   Proof by induction on p.
   Base: chop [] <> [] ==> LAST (chop []) <> #0
      But chop [] = [] by poly_chop_of_zero, hence true.
   Step: chop p <> [] ==> LAST (chop p) <> #0 ==>
             !h. chop (h::p) <> [] ==> LAST (chop (h::p)) <> #0
      chop (h::p) <> [] means ~ zerop (h::p)   by zero_poly_chop
      hence chop (h::p) = h :: chop p          by poly_chop_cons
      i.e. ~ zerop (h :: chop p)
      or ~((h = #0) /\ (chop p = [])) /\
           chop p <> [] ==> LAST (chop p) <> #0  ==> LAST (h:: chop p) <> #0
      If chop p = [],
         h <> #0, so LAST [h] = h <> #0 by LAST_CONS.
      If chop p <> [], then %p = k::t,
         LAST (h:: chop p) = LAST (h::k::t)
                        = LAST (k::t)          by LAST_CONS
                        = LAST (chop p) <> #0  by induction hypothesis
*)
val poly_chop_of_last_nonzero = store_thm(
  "poly_chop_of_last_nonzero",
  ``!p:'a poly. chop p <> [] ==> LAST (chop p) <> #0``,
  Induct >-
  rw[] >>
  rw[zero_poly_chop] >>
  Cases_on `chop p` >>
  rw[]);

(* Theorem: !p. chop p <> |0| ==> LAST (chop p) <> #0  *)
(* Proof: by poly_chop_of_last_nonzero and poly_zero. *)
val poly_chop_last_nonzero = save_thm("poly_chop_last_nonzero", poly_chop_of_last_nonzero |> REWRITE_RULE [GSYM poly_zero]);
(* > val poly_chop_last_nonzero = |- !p. chop p <> |0| ==> LAST (chop p) <> #0 : thm *)

(* Theorem: chop (SNOC #0 p) = chop p *)
(* Proof:
   By induction on p.
   Base: chop (SNOC #0 []) = chop []
      Note SNOC #0 [] = [#0]       by SNOC
       and chop [#0] = |0|         by poly_chop_const_zero
       and chop [] = [] = |0|      by poly_chop_of_zero, poly_zero
   Step: chop (SNOC #0 p) = chop p ==> !h. chop (SNOC #0 (h::p)) = chop (h::p)
      Note SNOC #0 (h::p) = h:: (SNOC #0 p)   by SNOC
      If zerop (h:: (SNOC #0 p)),
         Then h = #0 /\ zerop (SNOC #0 p)  by zero_poly_cons
         Thus chop (SNOC #0 p) = []        by zero_poly_chop
           or chop p = []                  by induction hypothesis
          ==> zerop p                      by zero_poly_chop
         Thus zerop (h::p)                 by zero_poly_cons
         The result is true                by zero_poly_chop
      If ~zerop (h:: (SNOC #0 p)),
         If h = #0, then ~zerop (SNOC #0 p)    by zero_poly_cons, ~zerop (h:: (SNOC #0 p))
                      so ~zerop p              by zero_poly_snoc
                    thus ~zerop (h::p)         by zero_poly_cons
         If h <> #0, then ~zerop (h::p)        by zero_poly_cons
         Either case, ~zerop (h::p)
         Then chop (SNOC #0 (h::p))
            = chop (h:: (SNOC #0 p))       by above
            = h :: chop (SNOC #0 p)        by poly_chop_cons
            = h :: chop p                  by induction hypothesis
            = chop (h::p)                  by ~zerop (h::p)
*)
val poly_chop_alt = store_thm(
  "poly_chop_alt",
  ``!r:'a ring. !p. chop (SNOC #0 p) = chop p``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[SNOC] >>
  Cases_on `zerop (h:: (SNOC #0 p))` >| [
    `zerop (h::p)` by
  (fs[zero_poly_cons] >>
    rw[GSYM zero_poly_snoc]) >>
    metis_tac[zero_poly_chop],
    `~zerop (h::p)` by
  (fs[zero_poly_cons] >>
    rw[GSYM zero_poly_snoc]) >>
    rw_tac std_ss[poly_chop_cons]
  ]);

(* Theorem: (lead (chop p) = #0) <=> (chop p = |0|) *)
(* Proof:
   If part: lead (chop p) = #0 ==> chop p = |0|
      By contradiction, suppose chop p <> |0|.
      Then LAST (chop p) <> #0        by poly_chop_last_nonzero
        or lead (chop p) <> #0        by poly_lead_alt, chop p <> |0|
      This contradicts lead (chop p) = #0.
   Only-if part: chop p = |0| ==> lead (chop p) = #0
      True since lead |0| = #0        by poly_lead_zero
*)
val poly_chop_lead_zero = store_thm(
  "poly_chop_lead_zero",
  ``!r:'a ring. !p. (lead (chop p) = #0) <=> (chop p = |0|)``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `LAST (chop p) <> #0` by rw[poly_chop_last_nonzero] >>
    fs[poly_lead_alt],
    rw[]
  ]);

(* Theorem: (p <> |0| /\ (chop p = p)) <=> lead p <> #0 *)
(* Proof:
   Intuitively, if lead p = #0, there is something to chop,
                then chop p will be shorter than p, so they cannot be equal.
                if lead p <> #0, there is nothing to chop, so chop p = p.
   However, poly_chop_def uses CONS, not SNOC, so we need to use induction.

   By induction on p.
   Base: [] <> |0| /\ (chop [] = []) <=> lead [] <> #0
      LHS = F since |0| = []         by poly_zero
      RHS = F since lead [] = #0     by poly_lead_of_zero
   Step: p <> |0| /\ (chop p = p) <=> lead p <> #0 ==>
         !h. h::p <> |0| /\ (chop (h::p) = h::p) <=> lead (h::p) <> #0
      If part: (chop (h::p) = h::p) ==> lead (h::p) <> #0
         Note ~(zerop (h::p))        by poly_chop_zero_poly, NOT_NIL_CONS
         Thus h :: chop p = h :: p   by poly_chop_cons
           or      chop p = p        by CONS_11
         If p = |0|,
            Then h <> #0             by zero_poly_cons, zero_poly_zero
             and lead [h] = h <> #0  by poly_lead_const
         If p <> |0|,
            Then lead (h::p)
               = lead p              by poly_lead_cons, p <> |0|
               <> #0                 by induction hypothesis
      Only-if part: lead (h::p) <> #0 ==> h::p <> |0| /\ (chop (h::p) = h::p)
          First, h::p <> [] = |0|    by NOT_NIL_CONS, poly_zero
          Next, to show: chop (h::p) = h::p
          Note ~(zerop (h::p))       by zero_poly_lead
          If p = |0|,
             Then lead [h] = h <> #0 by poly_lead_const
              and chop [h] = h       by poly_chop_cons, h <> #0
          If p <> |0|,
             Then lead p
                = lead (h::p) <> #0  by poly_lead_cons
              and chop (h::p)
                = h :: chop p        by poly_chop_cons
                = h :: p             by induction hypothesis
*)
val poly_chop_nonzero_eq = store_thm(
  "poly_chop_nonzero_eq",
  ``!r:'a ring. !p. (p <> |0| /\ (chop p = p)) <=> lead p <> #0``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    `~(zerop (h::p))` by metis_tac[poly_chop_def, NOT_NIL_CONS] >>
    `chop p = p` by metis_tac[poly_chop_cons, CONS_11] >>
    Cases_on `p = |0|` >| [
      `h <> #0` by metis_tac[zero_poly_cons, zero_poly_zero] >>
      rw[],
      metis_tac[poly_lead_cons]
    ],
    metis_tac[NOT_NIL_CONS, poly_zero],
    `~(zerop (h::p))` by metis_tac[zero_poly_lead] >>
    Cases_on `p = |0|` >-
    fs[poly_lead_const] >>
    metis_tac[poly_chop_cons, poly_lead_cons]
  ]);

(* Theorem: (chop p = p) <=> ((p = |0|) \/ lead p <> #0) *)
(* Proof:
   If part: chop p = p ==> (p = |0|) \/ lead p <> #0
        is: chop p = p /\ lead p = #0 ==> p = |0|
      Note lead (chop p) = #0            by chop p = p
       ==> chop p = |0|                  by poly_chop_lead_zero
   Only-if part: (p = |0|) \/ lead p <> #0 ==> chop p = p
       which is: (lead p = #0 ==> p = |0|) ==> chop p = p
      If p = |0|, true as chop |0| = |0| by poly_chop_zero
      If lead p <> #0, true              by poly_chop_nonzero_eq
*)
Theorem poly_chop_eq:
  !r:'a ring. !p. (chop p = p) <=> ((p = |0|) \/ lead p <> #0)
Proof
  simp[GSYM poly_chop_nonzero_eq, Excl "lift_disj_eq"] >>
  rw_tac std_ss[EQ_IMP_THM] >> simp[poly_chop_of_zero]
QED

(* Theorem: p <> |0| ==> ((lead p = #0) <=> (chop (FRONT p) = chop p)) *)
(* Proof:
   Note p <> []                         by poly_zero
   If part: lead p = #0 ==> chop (FRONT p) = chop p
      chop p
    = chop (SNOC (LAST p) (FRONT p))    by SNOC_LAST_FRONT, p <> []
    = chop (SNOC (lead p) (FRONT p))    by poly_lead_alt], p <> |0|
    = chop (SNOC #0 (FRONT p))          by given
    = chop (FRONT p)                    by poly_chop_alt

   Only-if part: chop (FRONT p) = chop p ==> lead p = #0
      By contradiction, suppose lead p <> #0.
      Then chop p = p                            by poly_chop_nonzero_eq
      Let q = FRONT p.
      Note LENGTH q = PRE (LENGTH p)     by LENGTH_FRONT, p <> []
       But LENGTH (chop q) <= LENGTH q   by poly_chop_length
       and LENGTH p <> 0                 by LENGTH_NIL, p <> []
        so LENGTH (chop q) < LENGTH p    by PRE m < m, for m <> 0
        or LENGTH (chop q) <> LENGTH p
      This contradicts chop q = p.
*)
val poly_chop_front = store_thm(
  "poly_chop_front",
  ``!r:'a ring. !p. p <> |0| ==> ((lead p = #0) <=> (chop (FRONT p) = chop p))``,
  rpt strip_tac >>
  `p <> []` by metis_tac[poly_zero] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    `p = SNOC (LAST p) (FRONT p)` by rw[SNOC_LAST_FRONT] >>
    `LAST p = lead p` by rw[GSYM poly_lead_alt] >>
    metis_tac[poly_chop_alt],
    spose_not_then strip_assume_tac >>
    `chop p = p` by metis_tac[poly_chop_nonzero_eq] >>
    `LENGTH p <> 0` by metis_tac[LENGTH_NIL] >>
    qabbrev_tac `q = FRONT p` >>
    `LENGTH q = PRE (LENGTH p)` by rw[LENGTH_FRONT, Abbr`q`] >>
    `LENGTH (chop q) <= LENGTH q` by rw[poly_chop_length] >>
    `LENGTH (chop q) <> LENGTH p` by decide_tac >>
    metis_tac[]
  ]);

(* Theorem: chop (p ++ GENLIST (K #0) n) = chop p *)
(* Proof:
   By induction on n.
   Base: chop (p ++ GENLIST (K #0) 0) = chop p
        p ++ GENLIST (K #0) 0
      = p ++ []                  by GENLIST
      = p                        by APPEND_NIL
      Thus the result is true.
   Step: chop (p ++ GENLIST (K #0) n) = chop p ==> chop (p ++ GENLIST (K #0) (SUC n)) = chop p
        p ++ GENLIST (K #0) (SUC n)
      = p ++ (SNOC #0 (GENLIST (K #0) n))   by GENLIST
      = p ++ ((GENLIST (K #0) n) ++ [#0])   by SNOC_APPEND
      = p ++ (GENLIST (K #0) n) ++ [#0]     by APPEND_ASSOC
      = SNOC #0 (p ++ GENLIST (K #0) n)     by SNOC_APPEND

        chop (p ++ GENLIST (K #0) (SUC n))
      = chop (SNOC #0 (p ++ GENLIST (K #0) n))  by above
      = chop ((p ++ GENLIST (K #0) n))          by poly_chop_alt
      = chop p                                  by induction hypothesis
*)
val poly_chop_add_genlist_zero = store_thm(
  "poly_chop_add_genlist_zero",
  ``!r:'a ring. !p n. chop (p ++ GENLIST (K #0) n) = chop p``,
  ntac 2 strip_tac >>
  Induct >-
  rw[] >>
  `p ++ GENLIST (K #0) (SUC n) = SNOC #0 (p ++ GENLIST (K #0) n)` by rw[GENLIST] >>
  metis_tac[poly_chop_alt]);

(* Theorem: chop (PAD_RIGHT #0 n p) = chop p *)
(* Proof:
     chop (PAD_RIGHT #0 n p)
   = chop (p ++ GENLIST (K #0) (n - LENGTH p))   by PAD_RIGHT
   = chop p                                      by poly_chop_add_genlist_zero
*)
val poly_chop_pad_right = store_thm(
  "poly_chop_pad_right",
  ``!r:'a ring. !p n. chop (PAD_RIGHT #0 n p) = chop p``,
  rw[PAD_RIGHT, poly_chop_add_genlist_zero]);

Theorem HD_chop:
  !p. chop p <> [] ==> HD (chop p) = HD p
Proof
  Cases \\ simp[] \\ rw[]
QED

Theorem EL_chop:
  !p n. n < LENGTH (chop p) ==>
        EL n (chop p) = EL n p
Proof
  Induct
  \\ rw[] \\ fs[]
  \\ Cases_on`n` \\ fs[]
QED

Theorem EL_chop_0:
  !p n. n < LENGTH p /\ ~(n < LENGTH (chop p)) ==>
        EL n p = #0
Proof
  Induct
  \\ rw[] \\ fs[]
  \\ Cases_on`n` \\ fs[]
  \\ fs[zero_poly_every_zero,
        listTheory.EVERY_MEM, listTheory.MEM_EL, PULL_EXISTS]
QED


(* ------------------------------------------------------------------------- *)
(* Polynomial Exponentiation.                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: !p n. p ** SUC n = p * p ** n *)
(* Proof: monoid_exp_SUC *)
val poly_exp_SUC = store_thm(
  "poly_exp_SUC",
  ``!p n. p ** SUC n = p * p ** n``,
  rw[]);

val _ = export_rewrites ["poly_exp_SUC"];

(* Theorem: !p. p ** 0 = |1| *)
(* Proof: by monoid_exp_0 *)
val weak_exp_0 = store_thm(
  "weak_exp_0",
  ``!p. p ** 0 = |1|``,
  rw[]);

(* Theorem: p ** 1 = p * |1| *)
(* Proof:
     p ** 1
   = p ** (SUC 0)    by ONE
   = p * p ** 0      by poly_exp_SUC
   = p * |1|         by weak_exp_0
*)
val weak_exp_1 = store_thm(
  "weak_exp_1",
  ``!r:'a ring. !p. p ** 1 = p * |1|``,
  metis_tac[poly_exp_SUC, weak_exp_0, ONE]);

(* Theorem: Ring r ==> !p. weak p ==> (p ** 2 = p * p) *)
(* Proof:
     p ** 2
   = p ** (SUC 1)        by TWO
   = p * p ** 1          by poly_exp_SUC
   = p * (p * |1|)       by weak_exp_1
   = p * (chop p)        by poly_chop_weak_alt
   = chop (p o (chop p)) by poly_mult_def
   = chop (p o p)        by poly_chop_mult_comm
   = p * p               by poly_mult_def
*)
val weak_exp_2 = store_thm(
  "weak_exp_2",
  ``!r:'a ring. Ring r ==> !p. weak p ==> (p ** 2 = p * p)``,
  rpt strip_tac >>
  `p ** 2 = p * p ** 1` by metis_tac[poly_exp_SUC, TWO] >>
  `_ = p * (p * |1|)` by rw[weak_exp_1] >>
  `_ = p * (chop p)` by rw[poly_chop_weak_alt] >>
  `_ = chop (p o (chop p))` by rw_tac std_ss[poly_mult_def] >>
  `_ = chop (p o p)` by rw_tac std_ss[poly_chop_mult_comm] >>
  `_ = p * p` by rw_tac std_ss[poly_mult_def] >>
  rw[]);

(* Theorem: weak p ==> weak (p ** n) *)
(* Proof:
   By induction on n.
   Base: weak (p ** 0)
     p ** 0 = |1|               by weak_exp_0
     and weak |1|               by weak_one_poly
   Step: weak (p ** n) ==> weak (p ** SUC n)
     p ** SUC n
   = p * p ** n                 by poly_exp_SUC
   = chop [p o p ** n]          by poly_mult_def
   weak (p ** n)                by induction hypothesis
   weak p                       by given
   hence weak (p o p ** n)      by weak_mult_weak
   and weak (chop (p o p ** n)) by poly_chop_weak
*)
val weak_exp_weak = store_thm(
  "weak_exp_weak",
  ``!r:'a ring. Ring r ==> !p. weak p ==> !n. weak (p ** n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw_tac std_ss[weak_exp_0, weak_one_poly] >>
  rw_tac std_ss[poly_exp_SUC, poly_mult_def, weak_mult_weak, poly_chop_weak]);

val _ = export_rewrites ["weak_exp_weak"];

(* ------------------------------------------------------------------------- *)
(* Theorems on polynomial degree (basic, not rely on poly).                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 <= deg p *)
(* Proof: by being a num. *)
val poly_deg_pos_or_zero = store_thm(
  "poly_deg_pos_or_zero",
  ``!p:'a poly. 0 <= deg p``,
  rw_tac std_ss[]);

(* Theorem: ~(deg p < 0) *)
(* Proof: by poly_deg_pos_or_zero *)
val poly_deg_not_less = store_thm(
  "poly_deg_not_less",
  ``!p:'a poly. ~(deg p < 0)``,
  rw_tac std_ss[]);

(* Theorem: deg [] = 0 *)
(* Proof: by definition. *)
val poly_deg_of_zero = store_thm(
  "poly_deg_of_zero",
  ``deg [] = 0``,
  rw_tac std_ss[poly_deg_def]);

val _ = export_rewrites ["poly_deg_of_zero"];

(* Theorem: deg |0| = 0 *)
(* Proof: by poly_deg_of_zero and poly_zero. *)
val poly_deg_zero = save_thm("poly_deg_zero", poly_deg_of_zero |> REWRITE_RULE [GSYM poly_zero]);
(* > val poly_deg_zero = |- deg |0| = 0 : thm *)

val _ = export_rewrites ["poly_deg_zero"];

(* Theorem: 0 < deg p ==> p <> |0| *)
(* Proof:
   By contradiction, suppose p = |0|.
   Then deg p = deg |0| = 0      by poly_deg_zero
   which contradicts 0 < deg p
*)
val poly_deg_pos_nonzero = store_thm(
  "poly_deg_pos_nonzero",
  ``!p. 0 < deg p ==> p <> |0|``,
  metis_tac[poly_deg_zero, NOT_ZERO_LT_ZERO]);

(* Theorem: deg [h] = 0  *)
(* Proof: by definition and LENGTH. *)
val poly_deg_const = store_thm(
  "poly_deg_const",
  ``!h. deg [h] = 0``,
  rw[poly_deg_def]);

val _ = export_rewrites ["poly_deg_const"];

(* Theorem: deg [#1] = 0 *)
(* Proof: by poly_deg_const. *)
val poly_deg_of_one = store_thm(
  "poly_deg_of_one",
  ``!r:'a ring. deg [#1] = 0``,
  rw[]);

val _ = export_rewrites ["poly_deg_of_one"];

(* Theorem: deg |1| = 0 *)
(* Proof:
   If #1 = #0,
      deg |1| = deg []                by poly_one
              = 0                     by poly_deg_def
   If #1 <> #0,
      deg |1| = deg [#1]              by poly_one
              = PRE (LENGTH [#1])     by poly_deg_def
              = PRE (SUC (LENGTH [])) by LENGTH
              = PRE (SUC 0)           by LENGTH
              = 0                     by prim_recTheory.PRE
*)
val poly_deg_one = store_thm(
  "poly_deg_one",
  ``!r:'a ring. deg |1| = 0``,
  rw_tac std_ss[poly_one, poly_deg_def, LENGTH]);

(* export simple result *)
val _ = export_rewrites["poly_deg_one"];

(* Theorem: If p <> |0|, deg p = PRE (LENGTH p) *)
(* Proof: by definition. *)
val poly_deg_nonzero = store_thm(
  "poly_deg_nonzero",
  ``!p:'a poly. p <> |0| ==> (deg p = PRE (LENGTH p))``,
  rw_tac std_ss[poly_deg_def, poly_zero]);

(* Theorem: deg (h::t) = LENGTH t *)
(* Proof:
   Since h::t <> [],
     deg (h::t)
   = PRE (LENGTH (h::t))    by poly_deg_def
   = PRE (SUC (LENGTH t))   by LENGTH
   = LENGTH t               by PRE_SUC, or decide_tac
*)
val poly_deg_cons_length = store_thm(
  "poly_deg_cons_length",
  ``!h t. deg (h::t) = LENGTH t``,
  rw[poly_deg_def]);

val _ = export_rewrites ["poly_deg_cons_length"];

(* Theorem: If p <> |0|, then deg (h::p) = SUC (deg p) *)
(* Proof:
     deg (h::p)
   = PRE (LENGTH (h::p))     by poly_deg_def
   = PRE (SUC (LENGTH p))    by LENGTH
   = LENGTH p                by decide_tac
   = SUC (PRE (LENGTH p))    by PRE_SUC, 0 < LENGTH p
   = SUC (deg p)             by poly_deg_def
*)
val poly_deg_cons = store_thm(
  "poly_deg_cons",
  ``!h (p:'a poly). p <> |0| ==> (deg (h::p) = SUC (deg p))``,
  rw_tac std_ss[poly_deg_def, poly_zero, LENGTH] >>
  `0 < LENGTH p` by metis_tac[LENGTH_NIL, NOT_ZERO_LT_ZERO] >>
  decide_tac);

val _ = export_rewrites ["poly_deg_cons"];

(* Theorem: If p <> |0|, LAST p = EL (deg p) p *)
(* Proof: by LAST_EL
   Since p <> |0|, or <> [], let p = h::t.
     LAST p
   = EL (PRE (LENGTH p)) p)   by LAST_EL, p <> []
   = EL (deg p) p             by poly_deg_def, p <> []
*)
val poly_last_at_deg_index = store_thm(
  "poly_last_at_deg_index",
  ``!p:'a poly. p <> |0| ==> (LAST p = EL (deg p) p)``,
  rw_tac std_ss[poly_deg_def, LAST_EL, poly_zero]);

(* Theorem: If p <> |0|, (deg p < k <=> ~(k < LENGTH p) *)
(* Proof:
       deg p < k
   <=> PRE (LENGTH p) < k            by poly_deg_def, p <> []
   <=> PRE (LENGTH p) < PRE (SUC k)  by decide_tac
   <=>      LENGTH p < SUC k         by INV_PRE_LESS, 0 < LENGTH p
   <=>      LENGTH p <= k            by decide_tac
   <=>      ~(k < LENGTH p)          by decide_tac, or LESS_LESS_SUC
*)
val poly_deg_less_length = store_thm(
  "poly_deg_less_length",
  ``!p:'a poly. p <> |0| ==> !k. deg p < k <=> ~(k < LENGTH p)``,
  rw_tac std_ss[poly_zero] >>
  `0 < LENGTH p` by metis_tac[LENGTH_NIL, NOT_ZERO_LT_ZERO] >>
  `(PRE (SUC k) = k) /\ (LENGTH p < SUC k <=> LENGTH p <= k) /\ (LENGTH p <= k <=> ~(k < LENGTH p))` by decide_tac >>
  metis_tac[poly_deg_def, INV_PRE_LESS, LESS_LESS_SUC]);

(* Theorem: weak p ==> deg (chop p) <= deg p *)
(* Proof: by induction on p.
   Base: deg (chop []) <= deg []
      true by poly_chop_of_zero, poly_deg_of_zero.
   Step: deg (chop p) <= deg p ==> deg (chop (h::p)) <= deg (h::p)
      If zerop (h::p),
         chop (h::p) = []   by zero_poly_chop,
      deg (chop (h::p)) = deg [] = 0, hence true.
      If ~zerop (h::p)
        If p = [] or chop p = [], h <> #0 by zero_poly_cons,
        then deg (chop (h::p)) = deg (chop [h]) = deg [h] = 0, hence true.
        deg (chop (h::p))
      = deg (h::chop p)     by poly_chop_cons
      = SUC (deg (chop p))  by poly_deg_cons, if chop p <> []
      <= SUC (deg p)        by induction hypothesis
      = deg (h::p)          by poly_deg_cons, if p <> []

*)
val poly_deg_chop = store_thm(
  "poly_deg_chop",
  ``!p. weak p ==> deg (chop p) <= deg p``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `zerop (h::p)` >-
  metis_tac[zero_poly_chop, poly_deg_of_zero, poly_deg_pos_or_zero] >>
  `h IN R /\ weak p` by metis_tac[weak_cons] >>
  Cases_on `(p = []) \/ (chop p = [])` >-
  metis_tac[poly_deg_const, poly_deg_pos_or_zero, poly_chop_cons, poly_chop_const_nonzero, zero_poly_def, zero_poly_chop] >>
  `p <> [] /\ chop p <> []` by metis_tac[] >>
  `deg (chop (h::p)) = SUC (deg (chop p))` by rw_tac std_ss[poly_chop_cons, poly_deg_cons, poly_zero] >>
  `deg (h::p) = SUC (deg p)` by rw_tac std_ss[poly_deg_cons, poly_zero] >>
  rw_tac std_ss[]);

(* Theorem: weak p /\ deg p = 0 ==> p = |0| \/ ?h. p = [h] *)
(* Proof: by p = h::t and conclude t = [].
   If p = |0|, then true.
   If p <> |0|, p <> []     by poly_zero
   or p = h::t,
      If t = [], then true.
      If t <> [],
         0 = deg (h::t) = SUC (deg t)  by poly_deg_cons
         a contradiction with SUC_NOT.
*)
val poly_deg_weak_eq_zero = store_thm(
  "poly_deg_weak_eq_zero",
  ``!p. weak p /\ (deg p = 0) ==> (p = |0|) \/ (?h. h IN R /\ (p = [h]))``,
  `!n. PRE (SUC n) = n` by decide_tac >>
  metis_tac[poly_deg_def, weak_cons, LENGTH, LENGTH_NIL, list_CASES, poly_zero]);

(* Theorem: deg (neg p) = deg p *)
(* Proof: due to lists are of the same length.
   If p = [], deg (neg []) = deg []
      true since neg [] = []  by weak_neg_of_zero.
   If p <> [], p = (h::t). By poly_deg_cons_length:
      deg (h::t) = LENGTH t
      deg (neg (h::t)) = LENGTH (-t)
      By weak_neg_map and LENGTH_MAP, they are equal.
*)
Theorem poly_deg_weak_neg:
  !r:'a ring. Ring r ==> !p. weak p ==> (deg (neg p) = deg p)
Proof
  metis_tac[poly_deg_cons_length, weak_neg_map, LENGTH_MAP,
            weak_neg_weak, weak_neg_cons, weak_neg_of_zero, list_CASES]
QED

(* Theorem: deg (c o p) = deg p *)
(* Proof:
   Since p = [] iff c o p = []   by weak_cmult_eq_of_zero
   this is true for p = [] or c o p = [].
   If p <> [], c o p <> []
     deg (c o p)
   = PRE (LENGTH (c o p))  by poly_deg_def, c o p <> []
   = PRE (LENGTH p)        by weak_cmult_map, LENGTH_MAP
   = deg p                 by poly_deg_def, p <> []
*)
val poly_deg_weak_cmult = store_thm(
  "poly_deg_weak_cmult",
  ``!r:'a ring c:'a p. deg (c o p) = deg p``,
  rpt strip_tac >>
  Cases_on `p = []` >>
  rw[weak_cmult_eq_of_zero, poly_deg_def, weak_cmult_map]);

(* Theorem: p <> |0| ==> deg (p >> 1) = SUC (deg p) *)
(* Proof:
     deg (p >> 1)
   = deg (#0::p)           by poly_shift_1, as p <> []
   = SUC (deg p)           by poly_deg_cons, as p <> []
*)
val poly_deg_shift_1 = store_thm(
  "poly_deg_shift_1",
  ``!r:'a ring p. p <> |0| ==> (deg (p >> 1) = SUC (deg p))``,
  rw_tac std_ss[poly_shift_1, poly_deg_cons]);

(* Theorem: p <> |0| ==> deg (p >> n) = deg p + n *)
(* Proof: by induction on n.
   Base: deg (p >> 0) = deg p + 0
      true by poly_shift_0: p >> 0 = p.
   Step: deg (p >> n) = deg p + n ==> deg (p >> SUC n) = deg p + SUC n
      Note p <> |0| ==> p >> n <> |0|   by poly_shift_eq_zero
      deg (p >> SUC n)
    = deg (#0::p >> n)   by poly_shift_suc, p <> |0|
    = SUC (deg (p >>n))  by poly_deg_cons, p >> n <> |0|
    = SUC (deg p + n)    by induction hypothesis
    = deg p + SUC n      by ADD_SUC
*)
val poly_deg_shift = store_thm(
  "poly_deg_shift",
  ``!r:'a ring p. p <> |0| ==> !n. deg (p >> n) = deg p + n``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[poly_shift_eq_zero, ADD_SUC]);

(* Theorem: 0 < deg q /\ deg q <= deq p ==> deg (q >> (deg p - deg q)) = deg p *)
(* Proof:
   By poly_deg_shift, since each q >> 1 increases (deg q) by 1.
*)
val poly_deg_shift_equal = store_thm(
  "poly_deg_shift_equal",
  ``!r:'a ring p q. 0 < deg q /\ deg q <= deg p ==> (deg (q >> (deg p - deg q)) = deg p)``,
  metis_tac[poly_deg_shift, poly_deg_zero, ADD_COMM, SUB_ADD, NOT_ZERO_LT_ZERO]);

(* Theorem: p = q ==> deg p = deg q *)
(* Proof: by poly_deg_def. *)
val poly_eq_deg_eq = store_thm(
  "poly_eq_deg_eq",
  ``!r:'a ring p q. (p = q) ==> (deg p = deg q)``,
  rw_tac std_ss[]);

(* Theorem: weak p /\ (deg p = 0) ==> (deg (chop p) = 0) *)
(* Proof:
   If p = [],
      True since chop [] = []       by poly_chop_of_zero
   If p <> [],
      Then PRE (LENGTH p) = deg p = 0   by poly_deg_def
       But LENGTH p <> 0            by LENGTH_NIL, p <> []
        so LENGTH p = 1             by deg p = 0
        or p = [h]  for some h      by LENGTH_EQ_1
       and h IN R                   by weak_cons
      If h = #0,
         Then chop [#0] = |0|       by poly_chop_def
          and deg |0| = 0           by poly_deg_zero
      If h <> #0,
         Then chop [h] = [h]        by poly_chop_def
          and deg [h] = 0           by poly_deg_const
*)
val weak_deg_chop_eq_0 = store_thm(
  "weak_deg_chop_eq_0",
  ``!r:'a ring. !p. weak p /\ (deg p = 0) ==> (deg (chop p) = 0)``,
  rpt strip_tac >>
  Cases_on `p = []` >-
  rw[] >>
  `PRE (LENGTH p) = 0` by metis_tac[poly_deg_def] >>
  `LENGTH p <> 0` by metis_tac[LENGTH_NIL] >>
  `LENGTH p = 1` by decide_tac >>
  `?h. p = [h]` by rw[GSYM LENGTH_EQ_1] >>
  `h IN R` by metis_tac[weak_cons] >>
  Cases_on `h = #0` >>
  rw[]);

(* Theorem: 0 < deg p ==> (deg p = SUC (deg (FRONT p))) *)
(* Proof:
   Note p <> []             by poly_deg_of_zero, 0 < deg p
     so deg p
      = PRE (LENGTH p)      by poly_deg_def, p <> []
      = LENGTH (FRONT p)    by LENGTH_FRONT, p <> []
   Thus (FRONT p) <> []     by LENGTH_NIL, 0 < deg p
     or deg (FRONT p)
      = PRE (LENGTH (FRONT p))  by poly_deg_def
      = PRE (deg p)             by above
        deg p
      = SUC (PRE (deg p))       by SUC_PRE, 0 < deg p
      = SUC (deg (FRONT p))     by above
*)
val weak_front_deg = store_thm(
  "weak_front_deg",
  ``!r:'a ring. !p. 0 < deg p ==> (deg p = SUC (deg (FRONT p)))``,
  rpt strip_tac >>
  `p <> []` by metis_tac[poly_deg_of_zero, NOT_ZERO_LT_ZERO] >>
  `deg p = PRE (LENGTH p)` by rw[poly_deg_def] >>
  `_ = LENGTH (FRONT p)` by rw[LENGTH_FRONT] >>
  qabbrev_tac `q = FRONT p` >>
  `q <> []` by metis_tac[LENGTH_NIL, NOT_ZERO_LT_ZERO] >>
  `deg q = PRE (LENGTH q)` by rw[poly_deg_def] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Polynomial Coefficient.                                                   *)
(* ------------------------------------------------------------------------- *)

(*
- EVAL ``poly_coeff (GF 7) [] 0``;
> val it = |- poly_coeff (GF 7) [] 0 = 0 : thm
- EVAL ``poly_coeff (GF 7) [] 1``;
> val it = |- poly_coeff (GF 7) [] 1 = 0 : thm
- EVAL ``poly_coeff (GF 7) [2] 1``;
> val it = |- poly_coeff (GF 7) [2] 1 = 0 : thm
- EVAL ``poly_coeff (GF 7) [2] 0``;
> val it = |- poly_coeff (GF 7) [2] 0 = 2 : thm
- EVAL ``poly_coeff (GF 7) [1;2;0;3;4;5] 5``;
> val it = |- poly_coeff (GF 7) [1; 2; 0; 3; 4; 5] 5 = 5 : thm
- EVAL ``poly_coeff (GF 7) [1;2;0;3;4;5] 4``;
> val it = |- poly_coeff (GF 7) [1; 2; 0; 3; 4; 5] 4 = 4 : thm
- EVAL ``poly_coeff (GF 7) [1;2;0;3;4;5] 2``;
> val it = |- poly_coeff (GF 7) [1; 2; 0; 3; 4; 5] 2 = 0 : thm
- EVAL ``poly_coeff (GF 7) [1;2;0;3;4;5] 0``;
> val it = |- poly_coeff (GF 7) [1; 2; 0; 3; 4; 5] 0 = 1 : thm
- EVAL ``poly_coeff (GF 7) [1;2;0;3;4;5] 7``;
> val it = |- poly_coeff (GF 7) [1; 2; 0; 3; 4; 5] 7 = 0 : thm
*)

(*
- EVAL ``GENLIST (\n. poly_coeff (GF 7) [1;2;0;3;4;5] n) 8``;
> val it = |- GENLIST (\n. poly_coeff (GF 7) [1; 2; 0; 3; 4; 5] n) 8 = [1; 2; 0; 3; 4; 5; 0; 0] : thm

Hence:
if deg p < deg q,  p + q = GENLIST (\n. p ' n + q ' n) deg q)
if deg q < deg p,  p + q = GENLIST (\n. p ' n + q ' n) deg p)
if deg p = deg q,  p + q = GENLIST (\n. p ' n + q ' n) deg p)

or in general,
p + q = GENLIST (\n. p ' n + q ' n) deg (p + q)
This is a bit useless for actual computation, but it is a theorem: LHS = RHS.

*)

(* Theorem: [] ' n = #0  *)
(* Proof: by definition. *)
val poly_coeff_of_zero = save_thm("poly_coeff_of_zero", poly_coeff_def |> CONJUNCT1);
(* > val poly_coeff_of_zero = !r n. [] ' n = #0 : thm *)

val _ = export_rewrites ["poly_coeff_of_zero"];

(* Theorem: |0| ' n = #0  *)
(* Proof: by poly_coeff_of_zero and poly_zero. *)
val poly_coeff_zero = save_thm("poly_coeff_zero", poly_coeff_of_zero |> REWRITE_RULE [GSYM poly_zero]);
(* > val poly_coeff_zero = |- !r n. |0| ' n = #0 : thm *)

val _ = export_rewrites ["poly_coeff_zero"];

(* Theorem: (h::t) ' n = if deg (h::t) < n then #0 else EL n (h::t) *)
(* Proof: by definition. *)
val poly_coeff_cons = save_thm("poly_coeff_cons", poly_coeff_def |> CONJUNCT2);
(* > val poly_coeff_cons = |- !r h t n. (h::t) ' n = if deg (h::t) < n then #0 else EL n (h::t) : thm *)

(* definition already exported *)
(* val _ = export_rewrites ["poly_coeff_of_zero", "poly_coeff_cons"]; *)

(* Theorem: (h::t) ' 0  = h *)
(* Proof: by definition. *)
val poly_coeff_0_cons = store_thm(
  "poly_coeff_0_cons",
  ``!h t. (h::t) ' 0 = h``,
  rw[]);

val _ = export_rewrites ["poly_coeff_0_cons"];

(* Theorem: if p <> |0|, !n. p ' n = if deg p < n then #0 else EL n p *)
(* Proof: by poly_coeff_cons. *)
val poly_coeff_nonzero = store_thm(
  "poly_coeff_nonzero",
  ``!p:'a poly. p <> |0| ==> !n. p ' n = if deg p < n then #0 else EL n p``,
  metis_tac[poly_coeff_cons, list_CASES, poly_zero]);

(* Theorem: p <> |0| ==> !n. p ' n = if n < LENGTH p then EL n p else #0 *)
(* Proof:
   Note deg p = PRE (LENGTH p)               by poly_deg_nonzero, p <> |0|
    and LENGTH p <> 0                        by poly_zero, LENGTH_NIL, p <> |0|
     so SUC (deg p) = LENGTH p               by SUC_PRE, 0 < LENGTH p
   If n < LENGTH p,
      Then ~(deg p < n), so p ' n = EL n p   by poly_coeff_nonzero
   If ~(n < LENGTH p),
      Then (deg p < n), so p ' n = #0        by poly_coeff_nonzero
*)
val poly_coeff_nonzero_alt = store_thm(
  "poly_coeff_nonzero_alt",
  ``!p:'a poly. p <> |0| ==> !n. p ' n = if n < LENGTH p then EL n p else #0``,
  rpt strip_tac >>
  `deg p = PRE (LENGTH p)` by rw[poly_deg_nonzero] >>
  `LENGTH p <> 0` by metis_tac[poly_zero, LENGTH_NIL] >>
  `0 < LENGTH p` by decide_tac >>
  `SUC (deg p) = LENGTH p` by rw[GSYM SUC_PRE] >>
  rw[] >| [
    `~(deg p < n)` by decide_tac >>
    rw[poly_coeff_nonzero],
    `deg p < n` by decide_tac >>
    rw[poly_coeff_nonzero]
  ]);

(* Theorem: If p <> |0| and k < LENGTH p, then p ' k = EL k p *)
(* Proof: by poly_deg_less_length, poly_coeff_nonzero. *)
val poly_coeff_as_element = store_thm(
  "poly_coeff_as_element",
  ``!r:'a ring. !p. p <> |0| ==> !k. k < LENGTH p ==> (p ' k = EL k p)``,
  rw_tac std_ss[poly_deg_less_length, poly_coeff_nonzero]);

(* Theorem: !k. (h::t) ' (SUC k) = t ' k *)
(* Proof:
   Note that:
     deg(h::t) = LENGTH t           by poly_deg_cons_length
     EL (SUC n) (l::ls) = EL n ls   by EL_restricted
   Hence this is to show:
   (1) LENGTH t < SUC k ==> #0 = t ' k
   If t = [], [] ' k = #0           by poly_coeff_zero
   If t <> [], t = h::t',
   deg(t) = deg(h::t') = LENGTH t'
   LENGTH t = SUC(LENGTH t') < SUC k
   hence deg(t) < k, and t ' k = #0 by poly_coeff_cons
   (2) ~(LENGTH t < SUC k) ==> EL k t = t ' k
   If t = [], LENGTH [] < SUC k, or 0 < SUC k is F  by SUC_NOT
   If t <> [], t = h::t',
   LENGTH (h::t') = SUC (LENGTH t') means
   ~(SUC (LENGTH t') < SUC k),
   or  ~(LENGTH t' < k)
   deg t = deg(h::t') = LENGTH t'    by poly_deg_cons_length
   hence ~(deg t < k),
   or t ' k = EL k t                 by poly_coeff_cons
*)
val poly_coeff_SUC = store_thm(
  "poly_coeff_SUC",
  ``!h t k. (h::t) ' (SUC k) = t ' k``,
  rw[] >| [
    Cases_on `t` >-
    rw[] >>
    `LENGTH (h::t') = SUC(LENGTH t')` by rw[] >>
    `LENGTH t' < k` by decide_tac >>
    rw[],
    Cases_on `t` >-
    metis_tac [LENGTH, SUC_NOT, NOT_ZERO_LT_ZERO] >>
    rw[] >>
    `LENGTH (h::t') = SUC (LENGTH t')` by rw[] >>
    `~(LENGTH t' < k)` by decide_tac
  ]);

(* Theorem: p ' (deg p) = lead p *)
(* Proof:
   If p = |0|, deg p = 0   by poly_deg_zero
     p ' (deg p)
   = |0| ' 0
   = [] ' 0                by poly_zero
   = #0                    by poly_coeff_zero
   = lead |0|              by poly_lead_zero
   If p <> |0|, p = h::t.
     deg p = deg (h::t) = LENGTH t         by poly_deg_cons_length
   LHS = p ' (deg p)
       = (h::t) ' (deg (h::t))
       = EL (deg (h::t)) (h::t)            by poly_coeff_def
       = EL (LENGTH t) (h::t)              by poly_deg_cons_length (above)
       = EL (PRE (LENGTH (h::t)) (h::t)    by LENGTH
       = LAST (h::t)                       by LAST_EL
       = lead (h::t)                       by poly_lead_def
       = lead p = RHS
*)
val poly_coeff_lead = store_thm(
  "poly_coeff_lead",
  ``!p:'a poly. p ' (deg p) = lead p``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[] >>
  rw_tac std_ss[poly_lead_def, poly_coeff_nonzero, poly_lead_at_deg_index]);

(* Theorem: zerop p <=> !k. p ' k = #0 *)
(* Proof:
   Case p = [],
      LHS = zerop []          true by zero_poly_of_zero
      RHS = !k. [] ' k = #0   true by poly_coeff_zero
   Case p = h::t,
   Since zerop p <=> EVERY (\c. c = #0) p   by zero_poly_every_zero
   It is sufficient to show:
   EVERY (\c. c = #0) (h::t) <=> !k. (h::t) ' k = #0
   First, note that:
   deg (h::t) = LENGTH t          by poly_deg_cons_length
   LENGTH(h::t) = SUC(LENGTH t)   by LENGTH
   If-part:
     EVERY (\c. c = #0) (h::t) ==> !k. (h::t) ' k = #0
     If (deg (h::t) < k), (h::t) ' k = #0    by poly_coeff_cons
     If ~(deg (h::t) < k), k < LENGTH (h::t)
     hence true by EVERY_EL.
   Only-if part:
     !k. (h::t) ' k = #0 ==> EVERY (\c. c = #0) (h::t)
     !l P. EVERY P l <=> !n. n < LENGTH l ==> P (EL n l)  by EVERY_EL
     Since n < LENGTH (h::t) means ~(deg (h::t) < n),
         EL n (h::t) = #0    by poly_coeff_cons
*)
val zero_poly_coeff_all_zero = store_thm(
  "zero_poly_coeff_all_zero",
  ``!p:'a poly. zerop p <=> !k. p ' k = #0``,
  Cases_on `p` >-
  rw[] >>
  `EVERY (\c. c = #0) (h::t) <=> !k. (h::t) ' k = #0` suffices_by metis_tac [zero_poly_every_zero] >>
  `deg (h::t) = LENGTH t` by rw[] >>
  `LENGTH (h::t) = SUC(LENGTH t)` by rw[] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    pop_assum mp_tac >>
    rw_tac std_ss[poly_coeff_cons, EVERY_EL] >>
    `k < LENGTH (h::t)` by decide_tac >>
    metis_tac [],
    pop_assum mp_tac >>
    rw_tac std_ss[poly_coeff_cons, EVERY_EL] >>
    `~(LENGTH t < n)` by decide_tac >>
    metis_tac []
  ]);

(* Theorem: weak p ==> !k. (chop p) ' k = p ' k *)
(* Proof: by induction on p.
   Base: weak [] ==> !k. chop [] ' k = [] ' k
     True since chop [] = []             by poly_chop_of_zero
   Step: weak p ==> !k. chop p ' k = p ' k ==>
              !h. weak (h::p) ==> !k. chop (h::p) ' k = (h::p) ' k
     weak (h::p) ==> h IN R /\ weak p    by weak_cons
     if zerop (h::t), chop (h::p) = []   by poly_chop_cons
        [] ' k = #0                      by poly_coeff_zero
        (h::p) ' k = #0                  by zero_poly_coeff_all_zero
     if ~(zerop (h::t)), chop (h::p) = h::chop t  by poly_chop_cons
     if k = 0, (h::chop t) ' 0 = h = (h::p) ' 0   by poly_coeff_0_cons
     if k > 0, k = SUC n,
       (h::chop p) ' SUC n
     = (chop p) ' n                      by poly_coeff_SUC
     = p ' n                             by induction hypothesis
     = (h::p) ' SUC n                    by poly_coeff_SUC
*)
val poly_coeff_chop = store_thm(
  "poly_coeff_chop",
  ``!p:'a poly. weak p ==> !k. (chop p) ' k = p ' k``,
  Induct >-
  rw[] >>
  rw_tac std_ss[weak_cons, poly_chop_cons] >-
  metis_tac [zero_poly_coeff_all_zero, zero_poly_of_zero] >>
  Cases_on `k` >-
  rw_tac std_ss[poly_coeff_0_cons] >>
  rw_tac std_ss[poly_coeff_SUC]);

(* Theorem: Ring r ==> !p. weak p ==> !k. (p ' k) IN R *)
(* Proof:
   If p = |0|,
      |0| ' k = #0    by poly_coeff_of_zero
      hence true      by ring_zero_element
   If p <> |0|,
   if deg p < k,
      p ' k = #0      by by poly_coeff_nonzero
      hence true      by ring_zero_element
   If ~(deg p < k),
      k < LENGTH p    by poly_deg_less_length
      Since weak p ==> EVERY (\c. c IN R) p    by weak_every_element
      and   EVERY (\c. c IN R) p ==> !k. k < LENGTH p ==> EL k p IN R  by EVERY_ELEMENT_PROPERTY
      hence true      by poly_coeff_nonzero
*)
val weak_coeff_element = store_thm(
  "weak_coeff_element",
  ``!r:'a ring. Ring r ==> !p. weak p ==> !k. (p ' k) IN R``,
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[] >>
  Cases_on `deg p < k` >-
  rw[poly_coeff_nonzero] >>
  metis_tac[poly_coeff_nonzero, weak_every_element, EVERY_ELEMENT_PROPERTY, poly_deg_less_length]);

(* Theorem: [h] ' k = if k = 0 then h else #0 *)
(* Proof:
   Note deg [h] = 0         by poly_deg_const
   If k = 0,
      [h] ' 0 = EL 0 [h]    by poly_coeff_def
              = h           by EL
   If k <> 0,
      [h] ' k = #0          by poly_coeff_def
*)
val poly_coeff_const = store_thm(
  "poly_coeff_const",
  ``!r:'a ring. !(h:'a) k. [h] ' k = if k = 0 then h else #0``,
  rpt strip_tac >>
  `deg [h] = 0` by rw[] >>
  `EL 0 [h] = h` by rw[] >>
  metis_tac[poly_coeff_def, NOT_ZERO_LT_ZERO]);

(* Theorem: p <> |0| /\ (lead p = #0) ==> !k. (FRONT p) ' k = p ' k *)
(* Proof:
   Let q = FRONT p.
   Note p <> []                     by poly_zero
    and deg p = PRE (LENGTH p)      by poly_deg_def, p <> []
              = LENGTH q            by LENGTH_FRONT, p <> []

   If LENGTH q = 0,
      Then PRE (LENGTH p) = 0       by above
       but LENGTH p <> 0            by LENGTH_NIL, p <> []
        so LENGTH p = 1             by PRE (LENGTH p) = 0
        or p = [h]  for some h      by LENGTH_EQ_1
       But lead [h] = h = #0        by poly_lead_const
       and FRONT [h] = []           by FRONT_DEF
      Thus (FRONT [h]) ' k = #0     by poly_coeff_of_zero
       and [h] ' k = #0             by poly_coeff_const, h = #0

   If LENGTH q <> 0,
      Then q <> []                  by LENGTH_NIL
       and deg p = LENGTH q <> 0
        so deg p = SUC (deg q)      by weak_front_deg, 0 < deg p
      If k < LENGTH q,
         Then EL k q = EL k p       by EL_FRONT
          ==>  q ' k = p ' k        by poly_coeff_as_element, k < LENGTH p.
      Otherwise,
               q ' k = #0           by poly_coeff_nonzero_alt, ~(k < LENGTH q)

      If k = LENGTH q = deg p,
         Then p ' k = p ' (deg p)
                    = lead p = #0   by poly_coeff_lead
      If k > LENGTH q,
         Then p ' k = #0            by poly_coeff_nonzero_alt, ~(k < LENGTH p)
*)
val poly_coeff_front = store_thm(
  "poly_coeff_front",
  ``!r:'a ring. !p. p <> |0| /\ (lead p = #0) ==> !k. (FRONT p) ' k = p ' k``,
  rpt strip_tac >>
  qabbrev_tac `q = FRONT p` >>
  `p <> []` by metis_tac[poly_zero] >>
  `deg p = PRE (LENGTH p)` by rw[poly_deg_def] >>
  `PRE (LENGTH p) = LENGTH q` by rw[LENGTH_FRONT, Abbr`q`] >>
  Cases_on `LENGTH q = 0` >| [
    `LENGTH p <> 0` by metis_tac[LENGTH_NIL] >>
    `LENGTH p = 1` by decide_tac >>
    `?h. p = [h]` by rw[GSYM LENGTH_EQ_1] >>
    `lead [h] = h` by rw[GSYM poly_lead_const] >>
    `q = []` by rw[Abbr`q`] >>
    `q ' k = #0` by rw[poly_coeff_of_zero] >>
    `p ' k = #0` by metis_tac[poly_coeff_const] >>
    rw[],
    `q <> []` by metis_tac[LENGTH_NIL] >>
    `deg p = SUC (deg q)` by metis_tac[weak_front_deg, NOT_ZERO_LT_ZERO] >>
    Cases_on `k < LENGTH q` >| [
      `k < LENGTH p` by decide_tac >>
      `EL k q = EL k p` by metis_tac[EL_FRONT, LENGTH_NIL, LENGTH_NOT_NULL, NOT_ZERO_LT_ZERO] >>
      rw[poly_coeff_as_element],
      `q ' k = #0` by rw[poly_coeff_nonzero_alt] >>
      Cases_on `k = LENGTH q` >| [
        `p ' k = #0` by metis_tac[poly_coeff_lead] >>
        rw[],
        `~(k < LENGTH p)` by decide_tac >>
        `p ' k = #0` by rw[poly_coeff_nonzero_alt] >>
        rw[]
      ]
    ]
  ]);

(* ------------------------------------------------------------------------- *)
(* Degree of Polynomial Addition (weak form).                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: deg (p || q) = MAX (deg p) (deg q) *)
(* Proof:
   By induction on p.
   Base: !q. deg ([] || q) = MAX (deg []) (deg q)
          deg ([] || q)
        = deg q                    by weak_add_of_lzero
        = MAX 0 deg q              by MAX_0
        = MAX (deg []) (deg q)     by poly_deg_of_zero
   Step: !q. deg (p || q) = MAX (deg p) (deg q) ==>
         !h q. deg ((h::p) || q) = MAX (deg (h::p)) (deg q)
        If q = [],
             deg ((h::p) || [])
           = deg (h::p)                  by weak_add_of_rzero
           = MAX (deg (h::p)) 0          by MAX_0
           = MAX (deg (h::p)) (deg [])   by poly_deg_of_zero
        Otherwise, q <> [], let q = h'::t
          deg ((h::p) || (h'::t))
        = deg (h + h' :: p || t)           by weak_add_cons
        If p || t = [],
           Then p = [] /\ t = []           by weak_add_eq_zero
           and deg [h] = deg [h'] = 0      by poly_deg_const
           and deg [h + h'] = 0            by poly_deg_const
           hence true.
        If p || t <> [],
           Then p <> [] \/ t <> []         by weak_add_eq_zero
          deg ((h::p) || (h'::t))
        = deg (h + h' :: p || t)           by weak_add_cons
        = SUC (deg (p || t))               by poly_deg_cons, p || t <> []
        = SUC (MAX (deg p) (deg t))        by induction hypothesis
        = MAX (SUC (deg p)) (SUC (deg t))  by SUC_MAX

        If p <> [] /\ t <> [], this
        = MAX ((deg (h::p)) (deg (h'::t))) by poly_deg_cons,
        If p <> [], but t = [], this
        = MAX (SUC (deg p) 1)              by poly_deg_of_zero, ONE
        = SUC (deg p)                      by MAX_1_POS, 0 < SUC (deg p)
        = MAX (SUC (deg p) 0)              by MAX_0
        = MAX (deg (h::p) deg [h'])        by poly_deg_const
        If p = [], but t <> [], this
        = MAX (1 SUC (deg t))              by poly_deg_of_zero, ONE
        = SUC (deg t)                      by MAX_1_POS, 0 < SUC (deg p)
        = MAX (0 SUC (deg t))              by MAX_0
        = MAX (deg [h] deg [h'::t])        by poly_deg_const
*)
val poly_deg_weak_add = store_thm(
  "poly_deg_weak_add",
  ``!r:'a ring. Ring r ==> !p q. deg (p || q) = MAX (deg p) (deg q)``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `q` >-
  rw[] >>
  Cases_on `p || t = |0|` >| [
    `(p = |0|) /\ (t = |0|)` by metis_tac[weak_add_eq_zero] >>
    simp[],
    `deg ((h::p) || (h'::t)) = SUC (deg (p || t))` by rw[poly_deg_cons] >>
    `_ = SUC (MAX (deg p) (deg t))` by rw[] >>
    `_ = MAX (SUC (deg p)) (SUC (deg t))` by rw[SUC_MAX] >>
    `(p <> |0|) \/ (t <> |0|)` by metis_tac[weak_add_eq_zero] >| [
      (Cases_on `t = |0|` >>  simp[]) >>
      rw[MAX_1_POS, MAX_COMM],
      (Cases_on `p = |0|` >>  simp[]) >>
      rw[MAX_1_POS]
    ]
  ]);

(* ------------------------------------------------------------------------- *)
(* Degree of Polynomial Multiplication (weak form).                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: deg (p o q) = deg p + deg q *)
(* Proof:
   By induction on p.
   Base: !q. [] <> |0| /\ q <> |0| ==> (deg ([] o q) = deg [] + deg q)
       True by [] <> |0| = F          by poly_zero
   Step: !q. p <> |0| /\ q <> |0| ==> (deg (p o q) = deg p + deg q) ==>
         !h q. h::p <> |0| /\ q <> |0| ==> (deg ((h::p) o q) = deg (h::p) + deg q)
      If p = |0|,
      LHS = deg ([h] o q)      by p = |0|
          = deg (h o q)        by weak_mult_const
          = deg q              by poly_deg_weak_cmult
          = deg [h] + deg q    by poly_deg_const, deg [h] = 0
          = RHS
      If p <> |0|, then p o q <> |0|                 by weak_mult_eq_zero
            deg ((h::p) o q)
          = deg (h o q || p o q >> 1)                by weak_mult_cons
          = MAX (deg (h o q)) (deg ((p o q) >> 1))   by poly_deg_weak_add
          = MAX (deg (h o q)) (SUC (deg (p o q)))    by poly_deg_shift_1, p o q <> |0|
          = MAX (deg q) (SUC (deg (p o q)))          by poly_deg_weak_cmult
          = MAX (deg q) (SUC (deg p + deg q))        by induction hypothesis
          = SUC (deg p + deg q)                      by MAX_DEF
          = SUC (deg p) + deg q                      by ADD
          = deg (h::p) + deg q                       by poly_deg_cons, p <> |0|.
*)
val poly_deg_weak_mult = store_thm(
  "poly_deg_weak_mult",
  ``!r:'a ring. Ring r ==>
   !p q. p <> |0| /\ q <> |0| ==> (deg (p o q) = deg p + deg q)``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw_tac std_ss[poly_zero] >>
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw[weak_mult_const, poly_deg_weak_cmult] >>
  `p o q <> |0|` by rw_tac std_ss[weak_mult_eq_zero] >>
  `!x y. y < SUC (x + y)` by decide_tac >>
  rw[poly_deg_weak_add, poly_deg_shift_1, poly_deg_weak_cmult, MAX_DEF, ADD]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Evaluation.                                                    *)
(* ------------------------------------------------------------------------- *)

(*
(* val _ = load "fieldInstancesTheory"; *)
open fieldInstancesTheory;

Polynomial evaluations:
EVAL ``poly_eval (GF 7) [] 3``;
> val it = |- poly_eval (GF 7) [] 3 = 0 : thm
EVAL ``poly_eval (GF 7) [1] 3``;
> val it = |- poly_eval (GF 7) [1] 3 = 1 : thm
EVAL ``poly_eval (GF 7) [1;2] 3``;
    (Note: 1 + 2*x for x = 3 is 1+2*3 = 7 = 0 (mod 7) )
> val it = |- poly_eval (GF 7) [1; 2] 3 = 0 : thm
EVAL ``poly_eval (GF 7) [2;2] 3``;
    ( Note: 2 + 2*x for x = 3 is 2+2*3 = 8 = 1 (mod 7) )
> val it = |- poly_eval (GF 7) [2; 2] 3 = 1 : thm

[6;0;1] = [-1;0;1] = x^2 - 1 = (x+1)(x-1).

- EVAL ``poly_eval (GF 7) [6;0;1] 1``;
> val it = |- poly_eval (GF 7) [6; 0; 1] 1 = 0 : thm
- EVAL ``poly_eval (GF 7) [6;0;1] 6``;
> val it = |- poly_eval (GF 7) [6; 0; 1] 6 = 0 : thm
*)

(* Theorem: [](a) = #0 *)
(* Proof: by definition. *)
val poly_eval_of_zero = save_thm("poly_eval_of_zero", poly_eval_def |> CONJUNCT1);
(* > val poly_eval_of_zero = |- !r x. eval [] x = #0 : thm *)

(* definition already exported *)
(* val _ = export_rewrites ["poly_eval_of_zero"]; *)

(* Theorem: (h::t)(x) = h + t(x) * x *)
(* Proof: by definition. *)
val poly_eval_cons = save_thm("poly_eval_cons", poly_eval_def |> CONJUNCT2);
(* > val poly_eval_cons = |- !r h t x. eval (h::t) x = h + eval t x * x : thm *)

(* definition already exported *)
(* val _ = export_rewrites ["poly_eval_cons"]; *)

(* Theorem: eval |0| x = #0  *)
(* Proof: by poly_eval_of_zero and poly_zero. *)
val poly_eval_zero = save_thm("poly_eval_zero", poly_eval_of_zero |> REWRITE_RULE [GSYM poly_zero]);
(* > val poly_eval_zero = |- !r x. eval |0| x = #0 : thm *)

val _ = export_rewrites ["poly_eval_zero"];

(* Theorem: [h](x) = h *)
(* Proof:
     [h](x)
   = (h::[])(x)
   = h + [](x) * x    by poly_eval_cons
   = h + #0 * x       by poly_eval_of_zero
   = h + #0           by ring_mult_lzero
   = h                by ring_add_rzero
*)
val poly_eval_const = store_thm(
  "poly_eval_const",
  ``!r:'a ring. Ring r ==> !h x. h IN R /\ x IN R ==> (eval [h] x = h)``,
  rw[]);

val _ = export_rewrites ["poly_eval_const"];

(* Theorem: weak p ==> p(x) IN R *)
(* Proof: by induction on p.
   Base: eval [] x IN R
      true by poly_eval_of_zero, ring_zero_element.
   Step: eval p x IN R ==> eval (h::p) x IN R
      (h::p)(x)
    = h + p(x) * x     by poly_eval_cons
    p(x) IN R          by induction hypothesis
       h IN R          by weak_cons
    Hence (h::p)(x) IN R   by ring_add_element, ring_mult_element.
*)
val weak_eval_element = store_thm(
  "weak_eval_element",
  ``!r:'a ring. Ring r ==> !p. weak p ==> !x. x IN R ==> eval p x IN R``,
  strip_tac >>
  strip_tac >>
  Induct >>
  rw[]);

val _ = export_rewrites ["weak_eval_element"];

(* Theorem: zerop p ==> p(x) = #0 *)
(* Proof: by induction on p.
   Base: eval [] x = #0
      true by poly_eval_of_zero.
   Step: zerop p ==> (eval p x = #0) ==> zerop (h::t) ==> eval (h::p) x = #0
      zerop (h::t) ==> h = #0 /\ zerop t     by zero_poly_cons
      (h::p)(x)
    = #0 + p(x) * x       by poly_eval_cons
    = #0 + #0 * x         by induction hypothesis
    = #0 + #0             by ring_mult_lzero
    = #0                  by ring_add_zero_zero
*)
val poly_eval_zerop = store_thm(
  "poly_eval_zerop",
  ``!r:'a ring. Ring r ==> !p x. zerop p /\ x IN R ==> (eval p x = #0)``,
  strip_tac >>
  strip_tac >>
  Induct >>
  rw[]);

val _ = export_rewrites ["poly_eval_zerop"];

(* Theorem: (chop p)(x) = p(x)  *)
(* Proof: by induction on p.
   Base: eval (chop []) x = eval [] x
      true as chop [] = []   by poly_chop_of_zero.
   Step: eval (chop p) x = eval p x ==> eval (chop (h::p)) x = eval (h::p) x
     if zerop (h::p),
        chop (h::p) = []       by poly_chop_cons,
        LHS = [](x) = #0       by poly_eval_of_zero
            = RHS              by poly_eval_zerop
     if ~zerop (h::p),
        chop (h::p)(x)
      = (h::chop p)(x)         by poly_chop_cons
      = h + (chop p)(x) * x    by poly_eval_cons
      = h + p(x) * x           by induction hypothesis
      = (h::p)(x)              by poly_eval_cons
*)
val poly_eval_chop = store_thm(
  "poly_eval_chop",
  ``!r:'a ring. Ring r ==> !p x. x IN R ==> (eval (chop p) x = eval p x)``,
  strip_tac >>
  strip_tac >>
  Induct >>
  rw[]);

val _ = export_rewrites ["poly_eval_chop"];

(* Theorem: eval |1| x = #1 *)
(* Proof:
      eval |1| x
    = eval (chop [#1]) x   by poly_one, poly_eval_of_zero
    = eval [#1] x          by poly_eval_chop
    = #1                   by poly_eval_const, ring_one_element
*)
val poly_eval_one = store_thm(
  "poly_eval_one",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> (eval |1| x = #1)``,
  rw[poly_one]);

val _ = export_rewrites ["poly_eval_one"];

(* Theorem: weak p ==> (c o p)(x) = c * p(x) *)
(* Proof: by induction on p.
   Base: eval (c o []) x = c * eval [] x
      true since c o [] = []   by weak_cmult_of_zero
              and [](x) = #0    by poly_eval_of_zero
   Step: eval (c o p) x = c * eval p x ==> eval (c o (h::p)) x = c * eval (h::p) x
     (c o (h::p))(x)
   = (c * h::c o p)(x)       by weak_cmult_cons
   = c * h + (c o p)(x) * x  by poly_eval_cons
   = c * h + (c * p(x)) * x  by induction hypothesis
   = c * h + c * (p(x) * x)  by ring_mult_assoc
   = c * (h + p(x) * x)      by ring_mult_radd
   = c * (h::p)(x)           by poly_eval_cons
*)
val weak_eval_cmult = store_thm(
  "weak_eval_cmult",
  ``!r:'a ring. Ring r ==> !p c x. weak p /\ c IN R /\ x IN R ==> (eval (c o p) x = c * (eval p x))``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  rw_tac std_ss[weak_cons, weak_cmult_cons, poly_eval_cons, weak_eval_element,
                 ring_mult_assoc, ring_mult_radd, ring_mult_element]);

(* val _ = export_rewrites ["weak_eval_cmult"]; *)

(* Theorem: weak p ==> (neg p)(x) = - p(x) *)
(* Proof: by induction on p.
   Base: eval (neg []) x = -eval [] x
      true since neg [] = []      by weak_neg_of_zero
                     #0 = - #0    by ring_neg_zero
           and [](x) = #0         by poly_eval_of_zero
   Step: eval (neg p) x = -eval p x ==> eval (neg (h::p)) x = -eval (h::p) x
     (neg (h::p))(x)
   = (-h::neg p)(x)          by weak_neg_cons
   = -h + (neg p)(x) * x     by poly_eval_cons
   = -h + (-p(x)) * x        by induction hypothesis
   = -h + - (p(x) * x)       by ring_mult_lneg
   = -(h + p(x) * x)         by ring_neg_add
   = - (h::p)(x)             by poly_eval_cons
*)
val weak_eval_neg = store_thm(
  "weak_eval_neg",
  ``!r:'a ring. Ring r ==> !p x. weak p /\ x IN R ==> (eval (neg p) x = - (eval p x))``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  rw_tac std_ss[weak_cons, weak_neg_cons, poly_eval_cons, weak_eval_element,
                 ring_mult_lneg, ring_neg_add, ring_mult_element]);

(* val _ = export_rewrites ["weak_eval_neg"]; *)

(* Theorem: weak p /\ weak q ==> (p || q)(x) = p(x) + q(x) *)
(* Proof: by induction on p and q.
   Base: eval ([] || q) x = eval [] x + eval q x
     ([] || q)(x)
   = q(x)              by weak_add_of_lzero
   = #0 + q(x)         by ring_add_lzero
   = [](x) + q(x)      by poly_eval_of_zero
   Step: induct on q.
      Base: eval ((h::p) || []) x = eval (h::p) x + eval [] x
        ((h::p) || [])(x)
      = (h::p)(x)             by weak_add_of_rzero
      = (h::p)(x) + #0        by ring_add_rzero
      = (h::p)(x) + [](x)     by poly_eval_of_zero
      Step: eval (p || q) x = eval p x + eval q x ==>
                 eval ((h::p) || (h'::q)) x = eval (h::p) x + eval (h'::q) x
        ((h::p) || (h'::q))(x)
      = (h + h' :: p || q)(x)             by weak_add_cons
      = (h + h') + (p || q)(x) * x        by poly_eval_cons
      = (h + h') + (p(x) + q(x)) * x      by induction hypothesis
      = (h + h') + (p(x) * x + q(x) * x)  by ring_mult_ladd
      = (h + p(x) * x) + (h' + q(x) * x)  by ring_add_assoc, ring_add_comm
      = (h::p)(x) + (h'::q)(x)            by poly_eval_cons
*)
val weak_eval_add = store_thm(
  "weak_eval_add",
  ``!r:'a ring. Ring r ==> !p q x. weak p /\ weak q /\ x IN R ==> (eval (p || q) x = eval p x + eval q x)``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  strip_tac >>
  Induct >-
  rw[] >>
  rw_tac std_ss[weak_cons, weak_add_cons, poly_eval_cons] >>
  `eval p x IN R /\ eval q x IN R` by rw_tac std_ss[weak_eval_element] >>
  `eval p x * x IN R /\ eval q x * x IN R` by rw_tac std_ss[ring_mult_element] >>
  `h + h' + (eval p x + eval q x) * x = h + (h' + eval p x * x + eval q x * x)`
    by rw_tac std_ss[ring_mult_ladd, ring_add_assoc, ring_add_element] >>
  `_ = h + (eval p x * x + h' + eval q x * x)` by rw_tac std_ss[ring_add_comm] >>
  rw_tac std_ss[ring_add_assoc, ring_add_element]);

(* val _ = export_rewrites ["weak_eval_add"]; *)

(* Theorem: weak p ==> (p >> n)(x) = p(x) * x ** n *)
(* Proof: by induction on n.
   Base: eval (p >> 0) x = eval p x * x ** 0
     (p >> 0)(x)
   = p(x)             by poly_shift_0
   = p(x) * #1        by ring_mult_rone, weak_eval_element
   = p(x) * x ** 0    by ring_exp_0
   Step: eval (p >> n) x = eval p x * x ** n ==> eval (p >> SUC n) x = eval p x * x ** SUC n
   If p = |0|,
     |0| >> SUC n = |0|  by poly_shift_suc
   LHS = |0|(x) = #0     by poly_eval_of_zero
   RHS = |0|(x) * x ** SUC n = #0  by poly_eval_of_zero, ring_mult_lzero, ring_exp_element.
   If p <> |0|,
     (p >> SUC n)(x)
   = (#0::p >> n)(x)            by poly_shift_suc
   = #0 + (p >> n)(x) * x       by poly_eval_cons
   = #0 + (p(x) * x ** n) * x   by induction hypothesis
   = (p(x) * x ** n) * x        by ring_add_lzero
   = p(x) * (x ** n * x)        by ring_mult_assoc
   = p(x) * x ** SUC n          by ring_exp_suc
*)
val weak_eval_shift = store_thm(
  "weak_eval_shift",
  ``!r:'a ring. Ring r ==> !p x. weak p /\ x IN R ==> !n. eval (p >> n) x = (eval p x) * (x ** n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  Cases_on `p = |0|` >>
  rw[ring_exp_suc, ring_mult_assoc]);

(* val _ = export_rewrites ["weak_eval_shift"]; *)

(* Theorem: weak p /\ weak q ==> (p o q)(x) = p(x) * q(x) *)
(* Proof: by induction on p.
   Base: eval ([] o q) x = eval [] x * eval q x
     ([] o q)(x)
   = [](x)          by weak_mult_of_lzero
   = #0             by poly_eval_of_zero
   = #0 * q(x)      by ring_mult_lzero, weak_eval_element
   = [](x) * q(x)   by poly_eval_of_zero
   Step: eval ((h::p) o q) x = eval (h::p) x * eval q x
     ((h::p) o q)(x)
   = (h o q || (p o q) >> 1)(x)            by weak_mult_cons
   = (h o q || (p o (q >> 1))(x)           by weak_mult_shift_1
   = (h o q)(x) + (p o (q >> 1))(x)        by weak_eval_add
   = h * q(x)   + (p o (q >> 1))(x)        by weak_eval_cmult
   = h * q(x)   + p(x) * (q >> 1)(x)       by induction hypothesis, weak_shift_weak
   = h * q(x)   + p(x) * (q(x) * x ** 1)   by weak_eval_shift
   = h * q(x)   + p(x) * (q(x) * x)        by ring_shift_1
   = h * q(x)   + p(x) * (x * q(x))        by ring_mult_comm
   = h * q(x)   + p(x) * x * q(x)          by ring_mult_assoc
   = (h + p(x) * x) * q(x)                 by ring_mult_ladd
   = (h::p)(x) * q(x)                      by poly_eval_cons
*)
val weak_eval_mult = store_thm(
  "weak_eval_mult",
  ``!r:'a ring. Ring r ==> !p q x. weak p /\ weak q /\ x IN R ==> (eval (p o q) x = eval p x * eval q x)``,
  strip_tac >>
  strip_tac >>
  Induct >-
  rw[] >>
  rw_tac std_ss[weak_cons] >>
  `weak (h o q) /\ weak (p o (q >> 1)) /\ weak (q >> 1)` by rw[] >>
  `eval p x IN R /\ eval q x IN R` by rw[] >>
  `h * eval q x IN R /\ x * eval q x IN R /\ eval p x * x IN R /\ (x ** 1 = x)` by rw[] >>
  `eval ((h::p) o q) x = eval (h o q || (p o q) >> 1) x` by rw_tac std_ss[weak_mult_cons] >>
  `_ = eval (h o q || p o (q >> 1)) x` by rw_tac std_ss[weak_mult_shift_1] >>
  `_ = eval (h o q) x + eval (p o (q >> 1)) x` by rw_tac std_ss[weak_eval_add] >>
  `_ = h * eval q x + eval (p o (q >> 1)) x` by rw_tac std_ss[weak_eval_cmult] >>
  `_ = h * eval q x + eval p x * eval (q >> 1) x` by rw_tac std_ss[] >>
  `_ = h * eval q x + eval p x * (eval q x * x)` by rw_tac std_ss[weak_eval_shift] >>
  `_ = h * eval q x + eval p x * (x * eval q x)` by rw_tac std_ss[ring_mult_comm] >>
  `_ = h * eval q x + eval p x * x * eval q x` by rw_tac std_ss[ring_mult_assoc] >>
  `_ = (h + eval p x * x) * eval q x` by rw_tac std_ss[ring_mult_ladd] >>
  `_ = eval (h::p) x * eval q x` by rw_tac std_ss[poly_eval_cons] >>
  rw_tac std_ss[]);

(* val _ = export_rewrites ["weak_eval_mult"]; *)

(* Theorem: h IN R /\ weak t ==> !x. x IN R ==> (eval (SNOC h t) x = eval t x + h * x ** (deg t)) *)
(* Proof:
   By induction on t.
   Base: weak [] ==> (eval (SNOC h []) x = eval [] x + h * x ** LENGTH [])
       LHS = eval (SNOC h []) x
           = eval [h] x             by SNOC
           = h                      by poly_eval_const
       RHS = eval [] x + h * x ** LENGTH []
           = #0 + h * x ** 0    by poly_eval_of_zero, LENGTH
           = #0 + h * #1        by ring_exp_0
           = #0 + h             by ring_mult_rone
           = h = LHS            by ring_add_lzero
   Step: !h'. weak (h'::t) ==> (eval (SNOC h (h'::t)) x = eval (h'::t) x + h * x ** LENGTH (h'::t))
      weak (h'::t) ==> h' IN R /\ weak t                  by weak_cons
       LHS = eval (SNOC h (h'::t)) x
           = eval (h'::SNOC h t) x                        by SNOC
           = h' + (eval (SNOC h t) x) * x                 by poly_eval_cons
           = h' + (eval t x + h * x ** LENGTH t) * x      by induction hypothesis
           = h' + (eval t x * x + h * x ** LENGTH t * x)  by ring_mult_ladd
           = (h' + eval t x * x) + h * x ** LENGTH t * x  by ring_add_assoc
           = eval (h'::t) x + h * x ** LENGTH t * x       by poly_eval_cons
           = eval (h'::t) x + h * (x ** LENGTH t * x)     by ring_mult_assoc
           = eval (h'::t) x + h * (x * x ** LENGTH t)     by ring_mult_comm
           = eval (h'::t) x + h * (x ** SUC (LENGTH t))   by ring_exp_SUC
           = eval (h'::t) x + h * x ** LENGTH (h'::t)     by LENGTH
           = RHS
*)
val weak_eval_snoc = store_thm(
  "weak_eval_snoc",
  ``!r:'a ring. Ring r ==> !h t. h IN R /\ weak t ==>
   !x. x IN R ==> (eval (SNOC h t) x = eval t x + h * x ** LENGTH t)``,
  rpt strip_tac >>
  Induct_on `t` >-
  rw[] >>
  rw[ring_add_assoc, ring_mult_assoc] >>
  `x ** LENGTH t * x = x * x ** LENGTH t` by rw[ring_mult_comm] >>
  rw[]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Root.                                                          *)
(* ------------------------------------------------------------------------- *)

(*
- EVAL ``poly_root (GF 7) [6;0;1] 1``;
> val it = |- poly_root (GF 7) [6; 0; 1] 1 <=> T : thm
- EVAL ``poly_root (GF 7) [6;0;1] 2``;
> val it = |- poly_root (GF 7) [6; 0; 1] 2 <=> F : thm
- EVAL ``poly_root (GF 7) [6;0;1] 3``;
> val it = |- poly_root (GF 7) [6; 0; 1] 3 <=> F : thm
- EVAL ``poly_root (GF 7) [6;0;1] 4``;
> val it = |- poly_root (GF 7) [6; 0; 1] 4 <=> F : thm
- EVAL ``poly_root (GF 7) [6;0;1] 5``;
> val it = |- poly_root (GF 7) [6; 0; 1] 5 <=> F : thm
- EVAL ``poly_root (GF 7) [6;0;1] 6``;
> val it = |- poly_root (GF 7) [6; 0; 1] 6 <=> T : thm
*)

(* Theorem: [] has every x as root. *)
(* Proof: by [](x) = #0. *)
val poly_root_of_zero = store_thm(
  "poly_root_of_zero",
  ``!r:'a ring. !x. x IN R ==> root [] x``,
  rw[poly_root_def]);

val _ = export_rewrites ["poly_root_of_zero"];

(* Theorem: root |0| x  *)
(* Proof: by poly_root_of_zero and poly_zero. *)
val poly_root_zero = save_thm("poly_root_zero", poly_root_of_zero |> REWRITE_RULE [GSYM poly_zero]);
(* > val poly_root_zero = |- !r x. x IN R ==> root |0| x : thm *)

val _ = export_rewrites ["poly_root_zero"];

(* ------------------------------------------------------------------------- *)
(* Useful Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: lead (c o p) = c * lead p *)
(* Proof: by induction on p.
   Base case: lead (c o []) = c * lead []
   LHS = lead (c o [])
       = lead []            by weak_cmult_of_zero
       = #0                 by poly_lead_of_zero
   RHS = c * lead []
       = c * #0             by poly_lead_of_zero
       = #0 = LHS           by ring_mult_rzero
   Step case: lead (c o p) = c * lead p ==>
              !h. lead (c o (h::p)) = c * lead (h::p)
     If p = |0|, h::p = [h]
        lead (c o [h])
      = lead [c * h]        by weak_cmult_const
      = c * h               by poly_lead_const
      = c * lead [h]        by poly_lead_const
     If p <> |0|,
        c o p <> |0|        by weak_cmult_eq_zero
        lead (c o (h::p))
      = lead (c * h::c o p) by weak_cmult_cons
      = lead (c o p)        by poly_lead_cons, c o p <> |0|
      = c * lead p          by induction hypothesis
      = c * lead (h::p)     by poly_lead_cons, c <> |0|
*)
val weak_lead_cmult = store_thm(
  "weak_lead_cmult",
  ``!r:'a ring. Ring r ==> !p c. c IN R ==> (lead (c o p) = c * lead p)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw [] >>
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw [] >>
  `c o p <> |0|` by rw_tac std_ss[weak_cmult_eq_zero] >>
  rw_tac std_ss[weak_cmult_cons, poly_lead_cons]);

(* Theorem: deg (c o p) = deg p *)
(* Proof: by induction on p.
   Base case: deg (c o []) = deg []
   LHS = deg (c o [])
       = deg []            by weak_cmult_of_zero
       = 0                 by poly_deg_of_zero
       = RHS
   Step case: deg (c o p) = deg p ==>
              !h. deg (c o (h::p)) = deg (h::p)
     If p = |0|, h::p = [h]
        deg (c o [h])
      = deg [c * h]        by weak_cmult_const
      = 0                  by poly_deg_const
      = deg [h]            by poly_deg_const
     If p <> |0|,
        c o p <> |0|       by weak_cmult_eq_zero
        deg (c o (h::p))
      = deg (c * h::c o p) by weak_cmult_cons
      = SUC (deg (c o p))  by poly_deg_cons, c o p <> |0|
      = SUC (deg p)        by induction hypothesis
      = deg (h::p)         by poly_deg_cons, c <> |0|
*)
val weak_deg_cmult = store_thm(
  "weak_deg_cmult",
  ``!r:'a ring. Ring r ==> !p c. c IN R ==> (deg (c o p) = deg p)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw [] >>
  rpt strip_tac >>
  Cases_on `p = |0|` >-
  rw [] >>
  `c o p <> |0|` by rw_tac std_ss[weak_cmult_eq_zero] >>
  rw []);

(* Theorem: #1 <> #0 ==> !p. p <> |0| ==> p || [#1] >> (deg p) = SNOC #1 p *)
(* Proof: by induction on p.
   Base case: [] <> |0| ==> ...
     True by contradiction: |0| = []   by poly_zero
   Step case:
     LHS = [] || [#1] >> SUC (deg [])
         = [#1] >> SUC (deg [])        by weak_add_of_lzero
         = [#1] >> 1                   by poly_deg_of_zero
         = #0::[#1]                    by poly_shift_1
         = SNOC #1 [] = RHS            by SNOC
   Step case: weak p ==> p <> |0| ==> (p || [#1] >> SUC (deg p) = SNOC #1 p) ==>
              (h::p) || [#1] >> SUC (deg (h::p)) = SNOC #1 (h::p)
     If p = |0|,
        (h::[]) || [#1] >> SUC (deg (h::[]))
      = [h] || [#1] >> SUC (deg [h)
      = [h] || [#1] >> 1               by poly_deg_const: deg [h] = 0
      = [h] || #0::[#1]                by poly_shift_1
      = h::#1                          by weak_add_cons
      = SNOC #1 [h]                    by SNOC
     If p <> |0|,
        deg (h::p) = SUC (deg p)            by poly_deg_cons
        (h::p) || [#1] >> SUC (deg (h::p))
      = (h::p) || #0:[#1] >> (deg (h::p))   by poly_shift_suc
      = h :: p || [#1] >> (deg (h::p))      by weak_add_cons
      = h :: p || [#1] >> SUC (deg p)       by poly_deg_cons, above
      = h :: SNOC #1 p                      by induction hypothesis
      = SNOC #1 (h::p)                      by SNOC
*)
val weak_add_one_shift = store_thm(
  "weak_add_one_shift",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==>
    !p. weak p /\ p <> |0| ==> (p || [#1] >> SUC (deg p) = SNOC #1 p)``,
  rpt strip_tac >>
  `[#1] <> |0|` by rw[] >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[weak_cons] >>
  Cases_on `p = |0|` >-
  rw[poly_shift_1] >>
  `deg (h::p) = SUC (deg p)` by rw[] >>
  (`(h::p) || [#1] >> SUC (deg (h::p)) = (h::p) || (#0::[#1] >> (deg (h::p)))` by metis_tac [poly_shift_suc]) >>
  (`_ = h::p || [#1] >> (deg (h::p))` by rw[]) >>
  `_ = h::SNOC #1 p` by metis_tac[] >>
  rw[]);

(* Theorem: #1 <> #0 ==> !p. p <> |0| ==> p || c o ([#1] >> (deg p)) = SNOC c p *)
(* Proof: by induction on p.
   Base case: [] <> |0| ==> ...
     True by contradiction: |0| = []   by poly_zero
   Step case: weak p ==> p <> |0| ==> (p || c o ([#1] >> SUC (deg p)) = SNOC c p)  ==>
              weak (h::p) ==> (h::p) || c o ([#1] >> SUC (deg (h::p))) = SNOC c (h::p)
     If p = |0|,
        (h::[]) || c o ([#1] >> SUC (deg (h::[])))
      = [h] || (c o [#1]) >> SUC (deg [h])
      = [h] || [c] >> 1                by poly_deg_const: deg [h] = 0
      = [h] || #0::[c]                 by poly_shift_1, [c] <> |0|
      = h::c                           by weak_add_cons
      = SNOC c [h]                     by SNOC
     If p <> |0|,
        deg (h::p) = SUC (deg p)       by poly_deg_cons
        (h::p) || c o ([#1] >> SUC (deg (h::p)))
      = (h::p) || c o (#0::[#1] >> (deg (h::p)))         by poly_shift_suc
      = (h::p) || (c * #0:: c o ([#1] >> (deg (h::p))))  by weak_cmult_cons
      = (h::p) || (#0:: c o ([#1] >> (deg (h::p))))      by ring_mult_rzero
      = h :: p || c o ([#1] >> (deg (h::p)))             by weak_add_cons
      = h :: SNOC c p                                    by induction hypothesis
      = SNOC c (h::p)                  by SNOC
*)
val weak_add_cmult_shift = store_thm(
  "weak_add_cmult_shift",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==>
    !c p. c IN R /\ weak p /\ p <> |0| ==> (p || c o ([#1] >> SUC (deg p)) = SNOC c p)``,
  rpt strip_tac >>
  `[#1] <> |0|` by rw[] >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[weak_cons] >>
  Cases_on `p = |0|` >-
  rw[poly_shift_1] >>
  `deg (h::p) = SUC (deg p)` by rw[] >>
  (`(h::p) || c o ([#1] >> SUC (deg (h::p))) = (h::p) || c o(#0::[#1] >> (deg (h::p)))` by metis_tac [poly_shift_suc]) >>
  (`_ = (h::p) || (#0::c o ([#1] >> (deg (h::p))))` by rw[]) >>
  (`_ = h::p || c o ([#1] >> (deg (h::p)))` by rw[]) >>
  `_ = h::SNOC c p` by metis_tac[] >>
  rw[]);

(* weak_add_one_shift
|- !r. Ring r /\ #1 <> #0 ==>
   !p. weak p /\ p <> |0| ==> (p || [#1] >> SUC (deg p) = SNOC #1 p)
*)

(* Theorem: Ring r ==> !p c. weak p /\ c IN R /\ c <> #0 ==> (p || [c] >> (LENGTH p) = SNOC c p) *)
(* Proof:
   By induction on p.
   Base: weak [] ==> ([] || [c] >> LENGTH [] = SNOC c [])
         [] || [c] >> LENGTH []
       = [c] >> 0              by weak_add_of_lzero, LENGTH
       = [c]                   by poly_shift_0
      = SNOC c [])             by SNOC_NIL
   Step: weak p ==> (p || [c] >> LENGTH p = SNOC c p)
         !h. weak (h::p) ==> ((h::p) || [c] >> LENGTH (h::p) = SNOC c (h::p))
     Note h IN R /\ weak p     by weak_cons

       (h::p) || [c] >> LENGTH (h::p)
     = (h::p) || [c] >> SUC (LENGTH p)       by LENGTH
     = (h::p) || (#0::[c] >> (LENGTH p))     by poly_shift_suc, [c] <> |0|
     = (h + #0) :: (p || [c] >> (LENGTH p))  by weak_add_cons
     = (h + #0) :: SNOC c p                  by induction hypothesis
     = h :: SNOC c p                         by ring_add_rzero
     = SNOC c (h::p)                         by SNOC
*)
val weak_add_const_shift = store_thm(
  "weak_add_const_shift",
  ``!r:'a ring. Ring r ==> !p c. weak p /\ c IN R /\ c <> #0 ==>
               (p || [c] >> (LENGTH p) = SNOC c p)``,
  rpt strip_tac >>
  Induct_on `p` >-
  rw[] >>
  rw_tac std_ss[weak_cons] >>
  `(h::p) || [c] >> LENGTH (h::p) = (h::p) || [c] >> SUC (LENGTH p)` by rw[] >>
  `_ = (h::p) || (#0::[c] >> (LENGTH p))` by rw_tac std_ss[poly_shift_suc, NOT_NIL_CONS, poly_zero] >>
  `_ = (h + #0) :: (p || [c] >> (LENGTH p))` by rw[weak_add_cons] >>
  `_ = (h + #0) :: SNOC c p` by rw[] >>
  `_ = h :: SNOC c p` by rw[] >>
  `_ = SNOC c (h::p)` by rw[] >>
  rw[]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
