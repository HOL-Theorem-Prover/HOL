(* ------------------------------------------------------------------------- *)
(* Polynomial Factors and Roots                                              *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polyRoot";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory numberTheory combinatoricsTheory
     dividesTheory gcdTheory gcdsetTheory;

open monoidTheory groupTheory ringTheory ringUnitTheory fieldTheory;

open polynomialTheory polyWeakTheory polyRingTheory polyDivisionTheory;

(* val _ = load "polyFieldTheory"; *)
open polyFieldTheory;

(* val _ = load "fieldOrderTheory"; *)
open fieldOrderTheory;
open groupOrderTheory;

(* val _ = load "polyMonicTheory"; *)
open polyMonicTheory;

open integralDomainTheory; (* for poly_roots_mult_id *)

(* ------------------------------------------------------------------------- *)
(* Polynomials Factors and Roots Documentation                               *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   factor c   = poly_factor r c
*)
(* Definitions and Theorems (# are exported):

   Polynomial Linear Factor:
   poly_factor_def        |- !r c. factor c = [-c; #1]
   poly_factor_nonzero    |- !r c. factor c <> |0|
   poly_factor_eq         |- !r. Ring r ==> !x y. x IN R /\ y IN R ==> ((factor x = factor y) <=> (x = y))
   poly_factor_injective  |- !r. Ring r ==> INJ factor R univ(:'a poly)
   poly_factor_image_eq   |- !r. Ring r ==> !s t. s SUBSET R /\ t SUBSET R ==>
                                 ((IMAGE factor s = IMAGE factor t) <=> (s = t))
   poly_factor_poly       |- !r. Ring r /\ #1 <> #0 ==> !c. c IN R ==> poly (factor c)
   poly_deg_factor        |- !r. Ring r /\ #1 <> #0 ==> !c. c IN R ==> (deg (factor c) = 1)
   poly_factor_deg        |- !r. Ring r /\ #1 <> #0 ==> !c. c IN R ==> (deg (factor c) = 1)
   poly_lead_factor       |- !r. Ring r ==> !c. c IN R ==> (lead (factor c) = #1)
   poly_factor_lead       |- !r. Ring r ==> !c. c IN R ==> (lead (factor c) = #1)
   poly_factor_monic      |- !r. Ring r /\ #1 <> #0 ==> !c. c IN R ==> monic (factor c)
   poly_factor_pmonic     |- !r. Ring r /\ #1 <> #0 ==> !c. c IN R ==> pmonic (factor c)
   poly_factor_exp_deg    |- !r. Ring r /\ #1 <> #0 ==> !c n. c IN R ==> (deg (factor c ** n) = n)
   poly_factor_inj        |- !r. Ring r /\ #1 <> #0 ==> !s. s SUBSET R ==> INJ factor s (PolyRing r).carrier
   poly_factor_alt        |- !r. Ring r /\ #1 <> #0 ==> !c. c IN R ==> (factor c = X - c * |1|)
   poly_factor_divides_X  |- !r. Ring r /\ #1 <> #0 ==> !c. c IN R ==> (X % factor c = c * |1|)
   poly_factor_one        |- !r. Ring r /\ #1 <> #0 ==> (factor #1 = X - |1|)
   poly_factor_zero       |- !r. Ring r /\ #1 <> #0 ==> (factor #0 = X)
   poly_factor_nonzero    |- !r. Ring r /\ #1 <> #0 ==> !c. c IN R ==> factor c <> |0|
   poly_factor_eq_X       |- !r. Ring r /\ #1 <> #0 ==> !c. c IN R ==> ((factor c = X) <=> (c = #0))
   poly_eval_factor       |- !r. Ring r ==> !c x. c IN R /\ x IN R ==> (eval (factor c) x = x - c)
   poly_factor_eval       |- !r. Ring r ==> !c x. c IN R /\ x IN R ==> (eval (factor c) x = x - c)
   poly_factor_property   |- !r. Ring r /\ #1 <> #0 ==> !c. c IN R ==>
                                 poly (factor c) /\ (deg (factor c) = 1) /\ (lead (factor c) = #1) /\
                                 !x. x IN R ==> (eval (factor c) x = x - c)
   poly_image_factor_subset     |- !r. Ring r /\ #1 <> #0 ==>
                                   !s. s SUBSET R ==> (IMAGE factor s = {X - c * |1| | c IN s})
   poly_factor_in_image_X_add_c |- !r. Ring r /\ #1 <> #0 ==>
                                   !s. FINITE s /\ MAX_SET s < char r ==>
                                   !x. x IN s <=> x < char r /\ factor (-##x) IN IMAGE (\c. X + |c|) s
   poly_factor_in_image_X_sub_c |- !r. Ring r /\ #1 <> #0 ==>
                                   !s. FINITE s /\ MAX_SET s < char r ==>
                                   !x. x IN s <=> x < char r /\ factor (##x) IN IMAGE (\c. X - |c|) s
   field_orders_factor_image_member
                              |- !r. Field r ==> !p n. p IN IMAGE factor (orders f* n) ==>
                                     poly p /\ (deg p = 1) /\ (lead p = #1) /\ monic p

   Polynomial Factor Theorem:
   poly_factor_thm        |- !r. Ring r /\ #1 <> #0 ==> !p x. poly p /\ x IN R ==>
                                 (p % factor x = chop [eval p x])

   Polynomial Root Theorem:
   poly_root_thm           |- !r. Ring r /\ #1 <> #0 ==> !p x. poly p /\ x IN R ==>
                                  (root p x <=> (p % factor x = |0|))
   poly_monic_deg1_factor  |- !r. Ring r ==> !p. monic p /\ (deg p = 1) ==> ?c. c IN R /\ (p = factor c)
   poly_monic_deg2_factors |- !r. Ring r /\ #1 <> #0 ==> !p. monic p /\ (deg p = 2) ==>
                              !x. x IN R /\ root p x ==> ?y. root p y /\ (p = factor x * factor y)
   poly_factor_root        |- !r. Ring r /\ #1 <> #0 ==> !k c p. k IN R /\ c IN R /\ poly p /\
                                  k <> #0 /\ (p = k * factor c) ==> root p c
   poly_factor_roots       |- !r. Ring r ==> !c. c IN R ==> (roots (factor c) = {c})

   Polynomial Root:
   poly_nonzero_root_property
                         |- !r. Ring r ==> !p. poly p /\ p <> |0| ==>
                                           !x. x IN R /\ root p x ==> 0 < deg p
   poly_root_sub         |- !r. Ring r ==> !p q x. x IN R /\ poly p /\ poly q /\
                                            root p x /\ root q x ==> root (p - q) x
   poly_root_add_linear  |- !r. Ring r ==> !p q x. x IN R /\ poly p /\ poly q /\
                                root p x /\ root q x ==> !s t. poly s /\ poly t ==> root (s * p + t * q) x
   poly_root_sub_linear  |- !r. Ring r ==> !p q x. x IN R /\ poly p /\ poly q /\
                                root p x /\ root q x ==> !s t. poly s /\ poly t ==> root (s * p - t * q) x
   poly_root_field_mult  |- !r. Field r ==> !p q. poly p /\ poly q ==>
                            !x. x IN R ==> (root (p * q) x <=> root p x \/ root q x)
   poly_root_field_mult_alt
                         |- !r. Field r ==> !p q. poly p /\ poly q ==>
                            !x. x IN roots (p * q) <=> x IN roots p \/ x IN roots q
   poly_root_cmult       |- !r. Field r ==> !c p. c IN R /\ c <> #0 /\ poly p ==>
                            !x. x IN R ==> (root (c * p) x <=> root p x)

   Polynomial Roots:
   poly_roots_subset     |- !r p. roots p SUBSET R
   poly_roots_element    |- !r p x. x IN roots p ==> x IN R
   poly_roots_has_subset |- !r p s. poly p /\ s SUBSET R /\ (!x. x IN s ==> root p x) ==> s SUBSET roots p
   poly_roots_factor     |- !r. Ring r ==> !c. c IN R ==> (roots (factor c) = {c})
   poly_roots_factor_image
                         |- !r. Ring r ==> !s. s SUBSET R ==> (IMAGE (roots o factor) s = IMAGE (\x. {x}) s)
   poly_roots_zero       |- !r. roots |0| = R
   poly_roots_X          |- !r. Ring r ==> (roots X = {#0})
   poly_roots_mult       |- !r. Field r ==> !p q. poly p /\ poly q ==> (roots (p * q) = roots p UNION roots q)
   poly_roots_exp        |- !r. Field r ==> !p n. poly p /\ 0 < n ==> (roots (p ** n) = roots p)
   poly_roots_finite     |- !r. Field r ==> !p. poly p /\ p <> |0| ==> FINITE (roots p)
   poly_roots_count      |- !r. Field r ==> !p. poly p /\ p <> |0| ==> CARD (roots p) <= deg p
   poly_roots_const      |- !r. Ring r ==> !c. c IN R /\ c <> #0 ==> (roots [c] = {})
   poly_roots_one        |- !r. Ring r /\ #1 <> #0 ==> (roots |1| = {})
   poly_roots_linear     |- !r. Ring r ==> !p q. poly p /\ poly q /\ roots p SUBSET roots q ==>
                            !s t. poly s /\ poly t ==> roots p SUBSET roots (s * p + t * q)
   poly_roots_linear_sub |- !r. Ring r ==> !p q. poly p /\ poly q /\ roots p SUBSET roots q ==>
                            !s t. poly s /\ poly t ==> roots p SUBSET roots (s * p - t * q)
   poly_roots_neg        |- !r. Ring r ==> !p. poly p ==> (roots (-p) = roots p)
   poly_roots_remainder  |- !r. Ring r ==> !p q. ulead p /\ poly q /\ roots p SUBSET roots q ==>
                                           roots p SUBSET roots (q % p)
   poly_roots_cmult      |- !r. Field r ==> !c p. c IN R /\ c <> #0 /\ poly p ==> (roots (c * p) = roots p)
   poly_roots_mult_id    |- !r. IntegralDomain r ==>
                            !p q. poly p /\ poly q ==> roots (p * q) = roots p UNION roots q
   poly_roots_finite_id  |- !r. IntegralDomain r ==> !p. poly p /\ p <> |0| ==> FINITE (roots p)
   poly_roots_count_id   |- !r. IntegralDomain r ==>
                            !p. poly p /\ p <> |0| ==> CARD (roots p) <= deg p

   Roots of Unity:
   ring_uroots_are_roots   |- !r. Ring r ==>
                              !n. (roots_of_unity r.prod n).carrier = roots (unity n)
   field_uroots_are_roots  |- !r. Field r ==>
                              !n. 0 < n ==> ((roots_of_unity f* n).carrier = roots (unity n))
   field_uroots_card_upper |- !r. Field r ==>
                              !n. 0 < n ==> CARD (roots_of_unity r.prod n).carrier <= n

   Roots of Unity Polynomial:
   poly_unity_eval            |- !r. Ring r ==> !x. x IN R ==> !n. eval (unity n) x = x ** n - #1
   poly_unity_root_property   |- !r. Ring r ==> !x. x IN R ==> !n. root (unity n) x <=> (x ** n = #1)
   poly_unity_root_has_one    |- !r. Ring r ==> !n. root (unity n) #1
   poly_unity_root_nonzero    |- !r. Ring r /\ #1 <> #0 ==> !n. 0 < n ==> ~root (unity n) #0
   poly_unity_roots_no_zero   |- !r. Ring r /\ #1 <> #0 ==> !n. 0 < n ==> #0 NOTIN roots (unity n)
   poly_unity_roots_has_one   |- !r. Ring r ==> !n. #1 IN roots (unity n)
   poly_unity_roots_nonempty  |- !r. Ring r ==> !n. roots (unity n) <> {}
   poly_unity_roots_property  |- !r. Ring r ==> !x. x IN R ==> !n. x IN roots (unity n) <=> (x ** n = #1)
   poly_unity_roots_finite    |- !r. Field r ==> !n. 0 < n ==> FINITE (roots (unity n))

   Roots of Master Polynomial:
   poly_master_eval             |- !r. Ring r ==> !x n. x IN R ==> (eval (master n) x = x ** n - x)
   poly_master_root             |- !r. Ring r ==> !x n. x IN R ==> (root (master n) x <=> (x ** n = x))
   poly_master_root_zero        |- !r. Ring r ==> !n. 0 < n ==> root (master n) #0
   poly_master_root_one         |- !r. Ring r ==> !n. root (master n) #1
   poly_master_roots            |- !r. Ring r ==> !n x. x IN roots (master n) <=> x IN R /\ (x ** n = x)
   poly_master_roots_zero       |- !r. Ring r ==> !n. 0 < n ==> #0 IN roots (master n)
   poly_master_roots_one        |- !r. Ring r ==> !n. #1 IN roots (master n)
   poly_master_roots_finite     |- !r. Field r ==> !n. n <> 1 ==> FINITE (roots (master n))
   poly_master_roots_finite_alt |- !r. FiniteField r ==> !n. FINITE (roots (master n))
   poly_master_roots_count      |- !r. Field r ==> !n. 1 < n ==> CARD (roots (master n)) <= n
   poly_master_factors          |- !r. Ring r ==> !n. 0 < n ==> (master n = X * unity (n - 1))
   poly_master_factors_alt      |- !r. Ring r ==> !n. master (SUC n) = X * unity n

   poly_master_roots_by_unity_roots
                                |- !r. Field r ==>
                                   !n. 0 < n ==> (roots (master n) = {#0} UNION roots (unity (n - 1)))
   poly_master_roots_by_unity_roots_alt
                                |- !r. Field r ==> !n. roots (master (n + 1)) = {#0} UNION roots (unity n)

*)

(* ------------------------------------------------------------------------- *)
(* Polynomial Linear Factor.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Linear factor (x - c) *)
val poly_factor_def = Define `poly_factor (r:'a ring) (c:'a) = -c :: |1|`;

val _ = overload_on ("factor", ``poly_factor r``);

(* no conversion export. *)
(* val _ = export_rewrites ["poly_factor_def"]; *)

(* Theorem: factor c <> |0| *)
(* Proof: by poly_factor_def, poly_zero, NOT_CONS_NIL *)
val poly_factor_nonzero = store_thm(
  "poly_factor_nonzero",
  ``!r:'a ring. !c. factor c <> |0|``,
  rw[poly_factor_def]);

(* Theorem: Ring r ==> !x y. x IN R /\ y IN R ==> ((factor x = factor y) <=> (x = y)) *)
(* Proof:
   If part: factor x = factor y ==> x = y
          factor x = factor y
      <=> -x:: |1| = -y:: |1|    by poly_factor_def
      <=>       -x = -y          by CONS_11
      <=>        x = y           by ring_neg_eq

   Only-if part: x = y ==> factor x = factor y
      This is trivial.
*)
val poly_factor_eq = store_thm(
  "poly_factor_eq",
  ``!r:'a ring. Ring r ==> !x y. x IN R /\ y IN R ==> ((factor x = factor y) <=> (x = y))``,
  metis_tac[poly_factor_def, CONS_11, ring_neg_eq]);

(* Theorem: Ring r ==> INJ factor R univ(:'a poly) *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) x IN R ==> factor x IN univ(:'a poly), true             by IN_UNIV
   (2) x IN R /\ y IN R /\ factor x = factor y ==> x = y, true by poly_factor_eq
*)
val poly_factor_injective = store_thm(
  "poly_factor_injective",
  ``!r:'a ring. Ring r ==> INJ factor R univ(:'a poly)``,
  prove_tac[INJ_DEF, IN_UNIV, poly_factor_eq]);

(* This is better than poly_factor_inj later. *)

(* Theorem: Ring r ==> !s t. s SUBSET R /\ t SUBSET R ==> ((IMAGE factor s = IMAGE factor t) <=> (s = t)) *)
(* Proof:
   Since INJ factor R univ(:'a poly)   by poly_factor_injective
   Hence the result follows            by INJ_IMAGE_EQ
*)
val poly_factor_image_eq = store_thm(
  "poly_factor_image_eq",
  ``!r:'a ring. Ring r ==> !s t. s SUBSET R /\ t SUBSET R ==>
     ((IMAGE factor s = IMAGE factor t) <=> (s = t))``,
  metis_tac[poly_factor_injective, INJ_IMAGE_EQ]);

(* Note:
All factor theorems have pre-condition: Ring r /\ #1 <> #0.
Otherwise, by ring_one_eq_zero, #1 = #0 means R = {#0}, i.e. c = #0,
and (x - #0) = x = |1| >> 1 = [] by poly_one and poly_shift_of_zero,
and [] is not a linear factor.
On the other hand, this provides evidence that #1 <> #0.
Only deg (factor c) = 1   requires #1 <> #0.
*)

(* Theorem: poly (factor c) *)
(* Proof:
   factor c = -c :: |1|    by poly_factor_def
   Since ~zerop |1|        by poly_one
   This is true by poly_cons_poly, zero_poly_cons
*)
val poly_factor_poly = store_thm(
  "poly_factor_poly",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. c IN R ==> poly (factor c)``,
  rw[poly_factor_def, poly_one]);

(* Theorem: deg (factor c) = 1 *)
(* Proof:
   factor c = -c :: |1|    by poly_factor_def
   Since LENGTH |1|        by poly_one
   This is true by poly_deg_cons
*)
val poly_deg_factor = store_thm(
  "poly_deg_factor",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. c IN R ==> (deg (factor c) = 1)``,
  rw[poly_factor_def, poly_one]);

(* Provide another form *)
val poly_factor_deg = save_thm("poly_factor_deg", poly_deg_factor);
(* val poly_factor_deg = |- !r. Ring r /\ #1 <> #0 ==> !c. c IN R ==> (deg (factor c) = 1): thm *)

(* Theorem: lead (factor c) = #1 *)
(* Proof: by poly_factor_def, poly_one. *)
val poly_lead_factor = store_thm(
  "poly_lead_factor",
  ``!r:'a ring. Ring r ==> !c. c IN R ==> (lead (factor c) = #1)``,
  rw[poly_factor_def, poly_one] >>
  metis_tac[ring_one_eq_zero, IN_SING]);

(* Provide another form *)
val poly_factor_lead = save_thm("poly_factor_lead", poly_lead_factor);
(* val poly_factor_lead = |- !r. Ring r ==> !c. c IN R ==> (lead (factor c) = #1): thm *)

(*
  poly_factor_poly  |- !r. Ring r /\ #1 <> #0 ==> !c. c IN R ==> poly (factor c)
  poly_deg_factor   |- !r. Ring r /\ #1 <> #0 ==> !c. c IN R ==> (deg (factor c) = 1)
  poly_lead_factor  |- !r. Ring r ==> !c. c IN R ==> (lead (factor c) = #1)
*)

(* Theorem: Ring r /\ #1 <> #0 ==> !c. c IN R ==> monic (factor c) *)
(* Proof: by poly_monic_def, poly_factor_poly, poly_lead_factor *)
val poly_factor_monic = store_thm(
  "poly_factor_monic",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. c IN R ==> monic (factor c)``,
  metis_tac[poly_monic_def, poly_factor_poly, poly_lead_factor]);

(* Theorem: Ring r /\ #1 <> #0 ==> !c. c IN R pmonic (factor c) *)
(* Proof:
   Since  monic (factor c)         by poly_factor_monic
      so  lead (factor c) = #1     by poly_monic_def
     and  deg (factor c) = 1       by poly_deg_factor
   hence  0 < deg (factor c),
     and  unit (lead (factor c))   by ring_unit_one
     and  pmonic (factor c)        by notation
*)
val poly_factor_pmonic = store_thm(
  "poly_factor_pmonic",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. c IN R ==> pmonic (factor c)``,
  rw[poly_factor_monic, poly_deg_factor]);

(* Theorem: Ring r /\ #1 <> #0 ==> !c n. c IN R ==> (deg (factor c ** n) = n) *)
(* Proof:
   Note monic (factor c)        by poly_factor_monic
   Thus deg (factor c ** n)
      = n * deg (factor c)      by poly_monic_deg_exp
      = n * 1                   by poly_factor_deg
      = n                       by MULT_RIGHT_1
*)
val poly_factor_exp_deg = store_thm(
  "poly_factor_exp_deg",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c n. c IN R ==> (deg (factor c ** n) = n)``,
  rw_tac std_ss[poly_factor_monic, poly_monic_deg_exp, poly_factor_deg]);

(* Theorem: Ring r /\ #1 <> #0 ==> !s. s SUBSET R ==> INJ factor s (PolyRing r).carrier *)
(* Proof:
   By poly_ring_element, INJ_DEF, this is to show:
   (1) x IN s /\ s SUBSET R ==> poly (factor x)
       Since x IN s ==> IN R        by SUBSET_DEF
       Hence poly (factor x)        by poly_factor_poly
   (2) x IN s /\ y IN s /\ factor x = factor y ==> x = y
       Note x IN R /\ y IN R        by SUBSET_DEF
          factor x' = factor y
       <=>  X - x' = X - y          by poly_factor_def
       <=>  -x'::|1| = -y::|1|      by poly_X_def
       <=>    - x' = - y            by list equality
       <=>      x' = y              by ring_neg_eq
*)
val poly_factor_inj = store_thm(
  "poly_factor_inj",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !s. s SUBSET R ==> INJ factor s (PolyRing r).carrier``,
  rw[poly_ring_element, INJ_DEF] >-
  metis_tac[poly_factor_poly, SUBSET_DEF] >>
  `x IN R /\ y IN R` by metis_tac[SUBSET_DEF] >>
  full_simp_tac std_ss[poly_factor_def] >>
  rw[] >>
  metis_tac[ring_neg_eq]);

(* Theorem: factor c = X - c * |1| *)
(* Proof:
      factor c
    = -c:: |1|               by poly_factor_def
    = -c:: [#1]              by poly_one
    = [-c] + [#1] >> 1       by poly_cons_eq_add_shift
    = -c * |1| + [#1] >> 1   by poly_cmult_one
    = -c * |1| + X           by poly_X_alt
    = X + -c * |1|           by poly_add_comm
    = X + -(c * |1|)         by poly_neg_cmult
    = X - c * |1|            by poly_sub_def
*)
val poly_factor_alt = store_thm(
  "poly_factor_alt",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. c IN R ==> (factor c = X - c * |1|)``,
  rpt strip_tac >>
  `poly (-c:: |1|)` by rw[] >>
  `-c IN R` by rw[] >>
  `factor c = -c:: |1|` by rw[poly_factor_def] >>
  `_ = -c:: [#1]` by rw[poly_one] >>
  `_ = [-c] + [#1] >> 1` by rw[poly_cons_eq_add_shift] >>
  (`_ = -c * |1| + [#1] >> 1` by (rw_tac std_ss[poly_cmult_one] >> rw[poly_add_lzero_poly])) >>
  `_ = -c * |1| + X` by rw[poly_X_alt] >>
  `_ = X + -c * |1|` by rw[poly_add_comm] >>
  `_ = X + -(c * |1|)` by rw[poly_neg_cmult] >>
  rw[poly_sub_def]);

(* Theorem: X % (factor c) = c * |1| *)
(* Proof:
   Since  X = |1| * (X - c * |1|) + c * |1|   by poly_sub_add
     and  deg (c * |1|) = 0                   by poly_deg_cmult
     and  deg (X - c * |1|) = 1               by poly_deg_sub_less
    also  factor c = X - c * |1|              by poly_factor_alt
     and  lead (factor c) = #1                by poly_lead_factor
   Hence  X % (factor c) = c * |1|            by poly_div_mod_eqn
*)
val poly_factor_divides_X = store_thm(
  "poly_factor_divides_X",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. c IN R ==> (X % (factor c) = c * |1|)``,
  rpt strip_tac >>
  `poly X /\ poly (c * |1|) /\ poly |1| /\ poly (X - c * |1|)` by rw[] >>
  `X = (X - c * |1|) + c * |1|` by rw[poly_sub_add] >>
  `(X - c * |1|) = |1| * (X - c * |1|)` by rw[] >>
  `deg (c * |1|) = 0` by rw[] >>
  `deg (X - c * |1|) = 1` by rw[poly_deg_sub_less] >>
  `factor c = X - c * |1|` by rw[poly_factor_alt] >>
  metis_tac[poly_div_mod_eqn, poly_lead_factor, ring_unit_one, DECIDE``0 < 1``]);

(* Theorem: factor #1 = X - |1| *)
(* Proof: by poly_factor_alt *)
val poly_factor_one = store_thm(
  "poly_factor_one",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> (factor #1 = X - |1|)``,
  rw[poly_factor_alt]);

(* Theorem: Ring r /\ #1 <> #0 ==> (factor #0 = X) *)
(* Proof:
     factor #0
   = X - #0 * |1|         by poly_factor_alt
   = X - |0|              by poly_cmult_lzero
   = X                    by poly_sub_rzero
*)
val poly_factor_zero = store_thm(
  "poly_factor_zero",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> (factor #0 = X)``,
  rw[poly_factor_alt]);

(* Theorem: Ring r /\ #1 <> #0 ==> !c. c IN R ==> ((factor c = X) <=> (c = #0)) *)
(* Proof:
   If part: factor c = X ==> c = #0
      Given     factor c = X
         so  X - c * |1| = X - |0|        by poly_factor_alt, poly_sub_rzero
         or      c * |1| = |0|            by poly_sub_lcancel
      Since |1| <> |0|                    by poly_one_ne_poly_zero, #1 <> #0
         so c * lead |1| = #0             by poly_cmult_eq_zero
         or            c = #0             by poly_lead_one, ring_mult_rone

   Only-if part: c = #0 ==> factor c = X
      True by poly_factor_zero
*)
val poly_factor_eq_X = store_thm(
  "poly_factor_eq_X",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. c IN R ==> ((factor c = X) <=> (c = #0))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    `|1| <> |0|` by rw[GSYM poly_one_ne_poly_zero] >>
    `poly X /\ poly |0| /\ poly |1| /\ poly (c * |1|)` by rw[] >>
    `X - c * |1| = X - |0|` by metis_tac[poly_factor_alt, poly_sub_rzero] >>
    `c * |1| = |0|` by metis_tac[poly_sub_lcancel] >>
    `c * lead |1| = #0` by metis_tac[poly_cmult_eq_zero] >>
    metis_tac[poly_lead_one, ring_mult_rone],
    rw[poly_factor_zero]
  ]);

(* Theorem: eval (factor c) x = x - c *)
(* Proof:
   eval (factor c) x
   = eval (-c:: |1|) x      by poly_factor_def
   = -c + (eval |1| x) * x  by poly_eval_cons
   = -c + #1 * x            by poly_eval_one
   = -c + x                 by ring_mult_lone
   = x + -c                 by ring_add_comm, ring_neg_element
   = x - c                  by ring_sub_def
*)
val poly_eval_factor = store_thm(
  "poly_eval_factor",
  ``!r:'a ring. Ring r ==> !c x. c IN R /\ x IN R ==> (eval (factor c) x = x - c)``,
  rw[poly_factor_def, ring_add_comm]);

(* Provide another form *)
val poly_factor_eval = save_thm("poly_factor_eval", poly_eval_factor);
(* val val poly_factor_eval = |- !r. Ring r ==> !c x. c IN R /\ x IN R ==> (eval (factor c) x = x - c): thm *)

(* Theorem: properties of factor (X - |c|). *)
(* Proof:
   (1) poly (factor c), true                         by poly_factor_poly
   (2) deg (factor c) = 1, true                      by poly_factor_deg
   (3) lead (factor c) = #1, true                    by poly_factor_lead
   (4) x IN R ==> (eval (factor c) x = x - c), true  by poly_factor_eval
*)
val poly_factor_property = store_thm(
  "poly_factor_property",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !c. c IN R ==>
   poly (factor c) /\ (deg (factor c) = 1) /\ (lead (factor c) = #1) /\
   (!x. x IN R ==> (eval (factor c) x = x - c))``,
  rw_tac std_ss[poly_factor_poly, poly_factor_deg, poly_factor_lead, poly_factor_eval]);

(* Theorem: Ring r /\ #1 <> #0 ==>
            !s. s SUBSET R ==> (IMAGE factor s = {X - c * |1| | c | c IN s}) *)
(* Proof: by poly_factor_alt, SUBSET_DEF *)
val poly_image_factor_subset = store_thm(
  "poly_image_factor_subset",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==>
   !s. s SUBSET R ==> (IMAGE factor s = {X - c * |1| | c | c IN s})``,
  rw_tac std_ss[EXTENSION, GSPECIFICATION, IN_IMAGE] >>
  metis_tac[poly_factor_alt, SUBSET_DEF]);

(* Theorem: Ring r /\ #1 <> #0 ==>
            !s. FINITE s /\ MAX_SET s < char r ==>
            !x. x IN s <=> (x < char r /\ factor (- ##x) IN (IMAGE (\c:num. X + |c|) s)) *)
(* Proof:
   Note: x IN s ==> x < char r
       Since x IN s ==> s <> {}     by MEMBER_NOT_EMPTY
          so x <= MAX_SET s         by MAX_SET_DEF
       hence x < char r             by LESS_EQ_LESS_TRANS
   Note: X + |c| = [##c; #1]        by poly_X_add_c_list
   By poly_factor_def and IN_IMAGE, this is to show:
   (1) x IN s ==> ?c. ((##x = ##c) /\ (|1| = [#1])) /\ c IN s
       Let c = x, then trivially true, with |1| = [#1]  by poly_one.
   (2) c IN s /\ ##x = ##c ==> x IN s
       Since ##x = ##c ==> x = c    by ring_num_eq
       This is trivially true.
*)
val poly_factor_in_image_X_add_c = store_thm(
  "poly_factor_in_image_X_add_c",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==>
   !s. FINITE s /\ MAX_SET s < char r ==>
   !x. x IN s <=> (x < char r /\ factor (- ##x) IN (IMAGE (\c:num. X + |c|) s))``,
  rpt strip_tac >>
  `!c. c IN s ==> c < char r` by metis_tac[MEMBER_NOT_EMPTY, MAX_SET_DEF, LESS_EQ_LESS_TRANS] >>
  rw[poly_factor_def, poly_X_add_c_list, EQ_IMP_THM] >-
  metis_tac[poly_one] >>
  metis_tac[ring_num_eq]);

(* Theorem: Ring r /\ #1 <> #0 ==>
            !s. FINITE s /\ MAX_SET s < char r ==>
            !x. x IN s <=> (x < char r /\ factor (##x) IN (IMAGE (\c:num. X - |c|) s)) *)
(* Proof:
   Note: x IN s ==> x < char r
       Since x IN s ==> s <> {}     by MEMBER_NOT_EMPTY
          so x <= MAX_SET s         by MAX_SET_DEF
       hence x < char r             by LESS_EQ_LESS_TRANS
   Note: X - |c| = [- ##c; #1]      by poly_X_sub_c_list
   By poly_factor_def and IN_IMAGE, this is to show:
   (1) x IN s ==> ?c. ((##x = ##c) /\ (|1| = [#1])) /\ c IN s
       Let c = x, then trivially true, with |1| = [#1]  by poly_one.
   (2) c IN s /\ ##x = ##c ==> x IN s
       Since ##x = ##c ==> x = c    by ring_num_eq
       This is trivially true.
*)
val poly_factor_in_image_X_sub_c = store_thm(
  "poly_factor_in_image_X_sub_c",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==>
   !s. FINITE s /\ MAX_SET s < char r ==>
   !x. x IN s <=> (x < char r /\ factor (##x) IN (IMAGE (\c:num. X - |c|) s))``,
  rpt strip_tac >>
  `!c. c IN s ==> c < char r` by metis_tac[MEMBER_NOT_EMPTY, MAX_SET_DEF, LESS_EQ_LESS_TRANS] >>
  rw[poly_factor_def, poly_X_sub_c_list, EQ_IMP_THM] >-
  metis_tac[poly_one] >>
  metis_tac[ring_num_eq]);

(* Theorem: Field r ==> !p n. p IN (IMAGE factor (orders f* n)) ==>
            poly p /\ (deg p = 1) /\ (lead p = #1) /\ monic p *)
(* Proof:
    Note ?n x. (p = factor x) /\ x IN F* /\
               (order f* x = n)      by orders_element, IN_IMAGE
     Now x IN F* ==> x IN R          by field_nonzero_element_alt
   Hence poly p                      by poly_factor_poly, #1 <> #0
     and deg p = 1                   by poly_deg_factor, #1 <> #0
     and lead p = #1                 by poly_lead_factor
     and monic p                     by poly_factor_monic, #1 <> #0
*)
val field_orders_factor_image_member = store_thm(
  "field_orders_factor_image_member",
  ``!r:'a field. Field r ==> !p n. p IN (IMAGE factor (orders f* n)) ==>
         poly p /\ (deg p = 1) /\ (lead p = #1) /\ monic p``,
  ntac 5 strip_tac >>
  `?n x. (p = factor x) /\ x IN F* /\ (order f* x = n)` by metis_tac[orders_element, IN_IMAGE] >>
  `x IN R` by rw[field_nonzero_element_alt] >>
  rw[poly_factor_poly, poly_deg_factor, poly_lead_factor, poly_factor_monic]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Factor Theorem.                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: p % (factor x) = chop [p(x)] *)
(* Proof:
   Given p and q = factor x, there are quotient s and remainder t by division algorithm:
   p = s * (factor c) + t    deg t < deg (factor c) = 1, hence deg t = 0.
   Hence p(x) = [s * (factor x) + t](x) = s(x) * (factor x)(x) + t(x) = #0 + t(x) = t(x)
   Since deg t = 0, t(x) = t = p % (factor x), hence [p(x)] = p % (factor x).
*)
val poly_factor_thm = store_thm(
  "poly_factor_thm",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p x. poly p /\ x IN R ==> (p % (factor x) = chop [eval p x])``,
  rpt strip_tac >>
  `poly (factor x) /\ (deg (factor x) = 1) /\ (lead (factor x) = #1) /\ (eval (factor x) x = #0)` by rw[poly_factor_property] >>
  `0 < 1` by decide_tac >>
  `unit (lead (factor x))` by rw[] >>
  `(p = (p / (factor x)) * (factor x) + p % (factor x)) /\
    poly (p / (factor x)) /\ poly (p % (factor x)) /\ deg (p % (factor x)) < deg (factor x)` by rw[poly_div_mod_def] >>
  `deg (p % factor x) = 0` by decide_tac >>
  `eval (p / factor x * factor x) x = #0` by rw[] >>
  `poly (p / factor x * factor x)` by rw[] >>
  `eval p x = eval (p % factor x) x` by metis_tac[poly_eval_add, ring_add_lzero, poly_eval_element] >>
  Cases_on `p % factor x = |0|` >-
  rw[] >>
  metis_tac[poly_deg_eq_zero, poly_eval_const, poly_chop_const_nonzero]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Root Theorem.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: x is a root of p iff p % (factor x) = |0| *)
(* Proof:
   By Factor Theorem, p % (factor x) = chop [eval p x]
       root p x
   <=> eval p x = #0                by poly_root_def
   <=> p % (factor x) = chop [#0]   by poly_factor_thm
   <=> p % (factor x) = |0|         by poly_chop_const_zero, poly_chop_const_nonzero
*)
val poly_root_thm = store_thm(
  "poly_root_thm",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p x. poly p /\ x IN R ==> (root p x <=> (p % (factor x) = |0|))``,
  metis_tac[poly_root_def, poly_factor_thm, poly_chop_const_zero,
            poly_chop_const_nonzero, poly_eval_element, NOT_CONS_NIL, poly_zero]);

(* Theorem: Ring r ==> monic p /\ deg p = 1 ==> ?c. c IN R /\ (p = factor c) *)
(* Proof:
   Given deg p = 1,  p <> []       by poly_deg_of_zero
   Hence deg p = PRE (LENGTH p)    by poly_deg_def
   or LENGTH p = 2, so p = [h::t]  by list_CASES
   and h IN R /\ poly t            by poly_cons_poly
   deg p = SUC (deg t)             by poly_deg_cons
   hence   deg t = 1, or t = [a]   by poly_deg_eq_zero
   By monic p, a = #1              by poly_lead_cons, poly_lead_const
   Let c = -h, then p = factor c   by poly_factor_def
*)
val poly_monic_deg1_factor = store_thm(
  "poly_monic_deg1_factor",
  ``!r:'a ring. Ring r ==> !p. monic p /\ (deg p = 1) ==> ?c. c IN R /\ (p = factor c)``,
  rpt strip_tac >>
  `poly p /\ (lead p = #1)` by rw[poly_monic_def] >>
  `p <> []` by metis_tac[poly_deg_of_zero, DECIDE ``0 <> 1``] >>
  `deg p = PRE (LENGTH p)` by metis_tac[poly_deg_def] >>
  `LENGTH p = 2` by decide_tac >>
  `?h t. p = h::t` by metis_tac[list_CASES] >>
  `h IN R /\ poly t` by metis_tac[poly_cons_poly] >>
  `t <> |0|` by
  (spose_not_then strip_assume_tac >>
  `LENGTH p = 1` by metis_tac[LENGTH, ONE, poly_zero] >>
  decide_tac) >>
  `lead t = #1` by metis_tac[poly_lead_cons] >>
  `1 = SUC (deg t)` by metis_tac[poly_deg_cons] >>
  `deg t = 0` by decide_tac >>
  `?a. a IN R /\ a <> #0 /\ (t = [a])` by metis_tac[poly_deg_eq_zero] >>
  `a = #1` by metis_tac[poly_lead_const] >>
  `-h IN R` by rw[] >>
  `p = factor (-h)` by rw[poly_factor_def, poly_one] >>
  metis_tac[]);

(* Theorem: Ring r /\ #1 <> #0 ==> !p. monic p /\ deg p = 2 ==> !x. root p x ==>
            ?y. root p y /\ (p = (factor x) * (factor y) *)
(* Proof:
   Since root p x, (factor x) divides p.
   Since deg (factor x) = 1, deg p = 2, so the quotient p % (factor x) has degree 1.
   Since monic p, monic (factor x), the quotient is monic.
   Thus the quotient is (factor y), with p = (factor x) * (factor y).

   Let q = factor x.
   Since root p x, p % q = |0|   by poly_root_thm
   Dividing p by pmonic q        by poly_factor_pmonic
   giving   poly (p / q) /\
            p  = (p / q) * q + |0|  by poly_div_mod_def
               = (p / q) * q        by poly_add_rzero
   Let t = p / q, then p = t * q.
     Now p <> |0|                 by poly_deg_zero
      so t <> |0|                 by poly_mult_lzero
     and lead t <> #0             by poly_lead_nonzero
    also lead q = #1              by poly_lead_factor
   hence lead t * lead q
       = lead t * #1              by above
       = lead t <> #0             by poly_lead_element, ring_mult_rone, poly_is_weak]);
   giving deg p = deg t + deg q   by weak_deg_mult_nonzero, lead t * lead q <> #0
   This means     deg t = 1       by deg q = 1, deg p = 2.
   Note monic q                   by poly_factor_monic
    and monic t                   by poly_monic_monic_mult, poly_mult_comm
     so ?c. c IN R /\ (t = factor c)   by poly_monic_deg1_factor
   Switching p = q * t            by poly_mult_comm
    and note pmonic t             by poly_monic_pmonic, deg t = 1.
     so p % t = |0|               by poly_mod_eq_zero, ulead t
     or root p c                  by poly_root_thm
   Therefore, take y = c, and the result follows.
*)
val poly_monic_deg2_factors = store_thm(
  "poly_monic_deg2_factors",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !p. monic p /\ (deg p = 2) ==>
     !x. x IN R /\ root p x ==> ?y. root p y /\ (p = (factor x) * (factor y))``,
  rpt strip_tac >>
  qabbrev_tac `q = factor x` >>
  `poly p` by rw[] >>
  `poly q /\ (deg q = 1)` by rw[poly_factor_property, Abbr`q`] >>
  `p % q = |0|` by rw[GSYM poly_root_thm, Abbr`q`] >>
  `pmonic q` by rw[poly_factor_pmonic, Abbr`q`] >>
  `poly (p / q) /\ (p  = (p / q) * q + |0|)` by metis_tac[poly_div_mod_def] >>
  `_ = (p / q) * q` by rw[] >>
  qabbrev_tac `t = p / q` >>
  `p <> |0|` by metis_tac[poly_deg_zero, DECIDE ``0 <> 2``] >>
  `t <> |0|` by metis_tac[poly_mult_lzero] >>
  `lead t <> #0` by metis_tac[poly_lead_nonzero] >>
  `lead q = #1` by rw[poly_lead_factor, Abbr`q`] >>
  `lead t * lead q <> #0` by metis_tac[poly_lead_element, ring_mult_rone, poly_is_weak] >>
  `deg p = deg t + deg q` by rw[GSYM weak_deg_mult_nonzero] >>
  `deg t = 1` by decide_tac >>
  `monic q` by rw[poly_factor_monic, Abbr`q`] >>
  `monic t` by metis_tac[poly_monic_monic_mult, poly_mult_comm] >>
  `?c. c IN R /\ (t = factor c)` by metis_tac[poly_monic_deg1_factor] >>
  `p = q * t` by rw[poly_mult_comm] >>
  `pmonic t` by rw[] >>
  metis_tac[poly_mod_eq_zero, poly_root_thm]);

(* Theorem: Field r ==> poly p /\ k <> #0 /\ p = k * (factor c) ==> root p c *)
(* Proof:
   Since k <> #0, poly [k]    by poly_nonzero_element_poly
   Also  poly (factor c) /\
         deg (factor c) = 1   by poly_factor_property
         pmonic (factor c)    by poly_factor_pmonic
   p = k * (factor c)
     = [k] * (factor c)       by poly_mult_lconst
   p % (factor c) = |0|       by poly_mod_eq_zero, ulead (factor c)
   or root p c                by poly_root_thm
*)
val poly_factor_root = store_thm(
  "poly_factor_root",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !k c p. k IN R /\ c IN R /\ poly p /\ k <> #0 /\
       (p = k * (factor c)) ==> root p c``,
  rpt strip_tac >>
  `poly [k]` by rw[poly_nonzero_element_poly] >>
  `poly (factor c) /\ (deg (factor c) = 1)` by rw[poly_factor_property] >>
  `pmonic (factor c)` by rw[poly_factor_pmonic] >>
  metis_tac[poly_mult_lconst, poly_mod_eq_zero, poly_root_thm, DECIDE ``0 < 1``]);

(* Theorem: Ring r ==> !c. c IN R ==> (roots (factor c) = {c}) *)
(* Proof:
       x IN roots (factor c)
   <=> x IN R /\ root (factor c) x          by poly_roots_member
   <=> x IN R /\ eval (factor c) x = #0     by poly_root_def
   <=>                       x - c = #0     by poly_eval_factor
   <=>                           x = c      by ring_sub_eq_zero
   Hence roots (factor c) = {c}             by EXTENSION
*)
val poly_factor_roots = store_thm(
  "poly_factor_roots",
  ``!r:'a ring. Ring r ==> !c. c IN R ==> (roots (factor c) = {c})``,
  rw[EXTENSION] >>
  metis_tac[poly_roots_member, poly_root_def, poly_eval_factor, ring_sub_eq_zero]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Root.                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r ==> !p. poly p /\ p <> |0| ==> !x. x IN R /\ root p x ==> 0 < deg p *)
(* Proof:
   By contradiction, assume deg p = 0.
   Then ?c. c IN R /\ c <> #0 /\ (p = [c]) by poly_deg_eq_zero
   But eval [c] x = c                      by poly_eval_const
   which means root p x is impossible      by poly_root_def
*)
val poly_nonzero_root_property = store_thm(
  "poly_nonzero_root_property",
  ``!r:'a ring. Ring r ==> !p. poly p /\ p <> |0| ==>
   !x. x IN R /\ root p x ==> 0 < deg p``,
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  `deg p = 0` by decide_tac >>
  `?c. c IN R /\ c <> #0 /\ (p = [c])` by metis_tac[poly_deg_eq_zero] >>
  `eval [c] x = c` by rw[poly_eval_const] >>
  metis_tac[poly_root_def]);

(* Theorem: Ring r ==> !p q x. x IN R /\ poly p /\ poly q /\ root p x /\ root q x ==> root (p - q) x *)
(* Proof: poly_root_add, poly_root_neg *)
val poly_root_sub = store_thm(
  "poly_root_sub",
  ``!r:'a ring. Ring r ==> !p q x. x IN R /\ poly p /\ poly q /\ root p x /\ root q x ==> root (p - q) x``,
  rw[poly_root_add, poly_root_neg]);

(* Theorem: Ring r ==> !p q x. x IN R /\ poly p /\ poly q /\ root p x /\ root q x ==>
            !s t. poly s /\ poly t ==> root (s * p + t * q) x *)
(* Proof: poly_root_mult_comm, poly_root_add *)
val poly_root_add_linear = store_thm(
  "poly_root_add_linear",
  ``!r:'a ring. Ring r ==> !p q x. x IN R /\ poly p /\ poly q /\ root p x /\ root q x ==>
   !s t. poly s /\ poly t ==> root (s * p + t * q) x``,
  rw[poly_root_mult_comm, poly_root_add]);

(* Theorem: Ring r ==> !p q x. x IN R /\ poly p /\ poly q /\ root p x /\ root q x ==>
            !s t. poly s /\ poly t ==> root (s * p - t * q) x *)
(* Proof: poly_root_mult_comm, poly_root_sub *)
val poly_root_sub_linear = store_thm(
  "poly_root_sub_linear",
  ``!r:'a ring. Ring r ==> !p q x. x IN R /\ poly p /\ poly q /\ root p x /\ root q x ==>
   !s t. poly s /\ poly t ==> root (s * p - t * q) x``,
  rw[poly_root_mult_comm, poly_root_sub]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==>
            !x. x IN R ==> (root (p * q) x <=> root p x \/ root q x) *)
(* Proof:
   If part: root (p * q) x ==> root p x \/ root q x
          root (p * q) x
      <=> eval (p * q) x = #0             by poly_root_def
      <=> (eval p x) * (eval q x) = #0    by poly_eval_mult
      <=> eval p x = #0  or eval q x = #0 by field_mult_eq_zero
      <=> root p x       or root q x      by poly_root_def
   Only-if part: root p x \/ root q x ==> root (p * q) x
      root p x ==> root (p * q) x    true by poly_root_mult
      root q x ==> root (p * q) x    true by poly_root_mult_comm
*)
val poly_root_field_mult = store_thm(
  "poly_root_field_mult",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==>
   !x. x IN R ==> (root (p * q) x <=> root p x \/ root q x)``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    full_simp_tac std_ss[poly_root_def] >>
    `eval p x IN R /\ eval q x IN R` by rw[] >>
    metis_tac[poly_eval_mult, field_mult_eq_zero],
    rw[poly_root_mult],
    rw[poly_root_mult_comm]
  ]);

(* Theorem: Field r ==> !p q. poly p /\ poly q ==>
            !x. x IN roots (p * q) <=> (x IN roots p) \/ (x IN roots q) *)
(* Proof: by poly_root_field_mult, poly_roots_member *)
val poly_root_field_mult_alt = store_thm(
  "poly_root_field_mult_alt",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==>
   !x. x IN roots (p * q) <=> (x IN roots p) \/ (x IN roots q)``,
  metis_tac[poly_root_field_mult, poly_roots_member]);

(* Theorem: Field r ==> !c p. c IN R /\ c <> #0 /\ poly p ==>
            !x. x IN R ==> (root (c * p) x <=> root p x) *)
(* Proof:
   By poly_root_def, this is to show:
      (eval (c * p) x = #0) <=> (eval p x = #0)
   or   (c * eval p x = #0) <=> (eval p x = #0)   by poly_eval_cmult
   Note eval p x IN R                             by poly_eval_element
   Hence true                                     by field_mult_eq_zero
*)
val poly_root_cmult = store_thm(
  "poly_root_cmult",
  ``!r:'a field. Field r ==> !c p. c IN R /\ c <> #0 /\ poly p ==>
   !x. x IN R ==> (root (c * p) x <=> root p x)``,
  rpt strip_tac >>
  rw[poly_root_def] >>
  `eval p x IN R` by rw[] >>
  metis_tac[field_mult_eq_zero]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Roots.                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (roots p) SUBSET R *)
(* Proof: by poly_roots_def, SUBSET_DEF *)
val poly_roots_subset = store_thm(
  "poly_roots_subset",
  ``!r:'a ring. !p. (roots p) SUBSET R``,
  rw[poly_roots_def, SUBSET_DEF]);

(* Theorem: x IN roots p ==> x IN R *)
(* Proof: by poly_roots_member *)
val poly_roots_element = store_thm(
  "poly_roots_element",
  ``!r:'a ring. !p x. x IN roots p ==> x IN R``,
  rw[poly_roots_member]);

(* Theorem: poly p /\ s SUBSET R /\ (!x. x IN s ==> root p x) ==> s SUBSET roots p *)
(* Proof:
   Since s SUBSET R, !x. x IN s ==> x IN R    by SUBSET_DEF
   Hence !x, x IN s ==> x IN R /\ root p x    by given
   Therefore            x IN roots p          by poly_roots_def
   or             s SUBSET roots p            by SUBSET_DEF
*)
val poly_roots_has_subset = store_thm(
  "poly_roots_has_subset",
  ``!r:'a ring. !p s. poly p /\ s SUBSET R /\ (!x. x IN s ==> root p x) ==> s SUBSET roots p``,
  rw[poly_roots_def, SUBSET_DEF]);

(* Either theorem alias, or just another similar proof. *)
val poly_roots_factor = save_thm("poly_roots_factor", poly_factor_roots);
(*
val poly_roots_factor = |- !r. Ring r ==> !c. c IN R ==> (roots (factor c) = {c}): thm
*)

(* Example:
In Z_6, (x - 2)(x - 3) = x^2 - 5x + 0 = x^2 - 5x = x(x - 5)
so roots (x - 2)(x - 3) = {2, 3, 0, 5}
but roots (x - 2) = {2}
and roots (x - 3) = {3}
i.e. the product polynomial has more roots than its factors.
In Z_5, (x - 2)(x - 3) = x^2 - 0x + 1 = x^2 + 1
so roots (x - 2)(x - 3) = {2, 3} = roots (x - 2) UNION roots (x - 3)

Hence the rest is true only for F[x], not R[x] in general.
*)

(* Theorem: Ring r /\ #1 <> #0 ==> !s. s SUBSET R ==> (IMAGE (roots o factor) s = IMAGE (\x. {x}) s) *)
(* Proof:
   Note !x. x IN s ==> x IN R                               by SUBSET_DEF
    and !c. c IN s ==> ((roots o factor) c = (\x. {x}) c)   by poly_roots_factor, c IN R
   Hence the result follows                                 by IMAGE_CONG
*)
val poly_roots_factor_image = store_thm(
  "poly_roots_factor_image",
  ``!r:'a ring. Ring r ==> !s. s SUBSET R ==> (IMAGE (roots o factor) s = IMAGE (\x. {x}) s)``,
  rpt strip_tac >>
  `!x. x IN s ==> x IN R` by metis_tac[SUBSET_DEF] >>
  `!c. c IN s ==> ((roots o factor) c = (\x. {x}) c)` by rw[poly_roots_factor] >>
  rw[IMAGE_CONG]);

(* Theorem: roots |0| = R *)
(* Proof:
     roots |0|
   = {x | x IN R /\ root |0| x}    by poly_roots_def
   = {x | x IN R /\ T}             by poly_root_zero
   = R                             by EXTENSION
*)
val poly_roots_zero = store_thm(
  "poly_roots_zero",
  ``!r:'a ring. roots |0| = R``,
  rw_tac std_ss[poly_roots_def, EXTENSION, GSPECIFICATION] >>
  metis_tac[poly_root_zero]);

(* Theorem: Ring r ==> (roots X = {#0}) *)
(* Proof:
   By poly_roots_def, poly_root_def, this is to show:
      x IN R /\ (eval X x = #0) <=> (x = #0)
   This is true by poly_eval_X, ring_zero_element.
*)
val poly_roots_X = store_thm(
  "poly_roots_X",
  ``!r:'a ring. Ring r ==> (roots X = {#0})``,
  rw[poly_roots_def, poly_root_def, EXTENSION] >>
  metis_tac[poly_eval_X, ring_zero_element]);

(* Theorem: roots (p * q) = roots p UNION roots q *)
(* Proof: by p * q = |0| iff p = |0| or q = |0|.
   !x. x IN roots (p * q)
   <=> root (p * q) x                  by poly_roots_member
   <=> (p * q)(x) = #0                 by poly_root_def
   <=> p(x) * q(x) = #0                by poly_eval_mult
   <=> p(x) = #0  or q(x) = #0         by field_zero_product -- must be in Field, not Ring.
   <=> root p x   or  root q x         by poly_root_def
   <=> x IN roots p or x IN roots q    by poly_roots_member
   <=> x IN (roots p UNION roots q)    by IN_UNION
*)
val poly_roots_mult = store_thm(
  "poly_roots_mult",
  ``!r:'a field. Field r ==> !p q. poly p /\ poly q ==> (roots (p * q) = roots p UNION roots q)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  rw[poly_roots_member, poly_root_def, EXTENSION, EQ_IMP_THM] >-
  rw[GSYM field_zero_product, GSYM poly_eval_mult] >> rw[]);

(* Theorem: Field r ==> !p n. poly p /\ 0 < n ==> (roots (p ** n) = roots p) *)
(* Proof:
   By induction on n.
   Base: 0 < 0 ==> ..., true by 0 < 0 = F.
   Step: 0 < n ==> (roots (p ** n) = roots p) ==>
         0 < SUC n ==> (roots (p ** SUC n) = roots p)
         If n = 0,
            roots (p ** 0) = roots p      by poly_exp_0
         If n <> 0, then 0 < n.
            roots (p ** SUC n)
          = roots (p * p ** n)            by poly_exp_SUC
          = roots p UNION roots (p ** n)  by poly_roots_mult
          = roots p UNION roots p         by induction hypothesis
          = roots p                       by UNION_IDEMPOT
*)
val poly_roots_exp = store_thm(
  "poly_roots_exp",
  ``!r:'a field. Field r ==> !p n. poly p /\ 0 < n ==> (roots (p ** n) = roots p)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  rw[poly_roots_mult]);

(* Theorem: A nonzero polynomial has only a finite number of roots, i.e. FINITE (roots p) *)
(* Proof:
   If p has no root, this is trivially true by FINITE_EMPTY.
   Hence assume there is a root z, i.e. z IN R and eval p z = #0  by poly_roots_member.
   Induct on degree of polynomial p.
   Base case: (0 = deg p) /\ p <> |0| ==> FINITE (roots p)
      Since deg p = 0 and p <> |0|,
      p = [h] /\ h <> #0    by poly_deg_eq_zero
      eval [h] z = h <> #0  by poly_eval_const
      contradicting eval p z = #0.
   Step case: deg p = v ==> FINITE (roots p)  ==>
              deg p = SUC v ==> FINITE (roots p)
      Since root p z,
         p % (factor z) = |0|            by poly_root_thm
      or p = (p / factor z) * factor z   by poly_div_mod_def
      now, poly (p / factor z) has degree (SUC v) - 1 = v,
      so it has finite number of roots by induction hypothesis
      or FINITE (roots (p / factor z)).
      Since roots p
          = roots (p / factor z) UNION roots (factor z)  by poly_roots_mult
          = roots (p / factor z) UNION {z}               by poly_roots_factor
          = z INSERT roots (p / factor z)                by INSERT_SING_UNION
      Hence FINITE (roots p)                             by FINITE_INSERT
*)
val poly_roots_finite = store_thm(
  "poly_roots_finite",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==> FINITE (roots p)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  Induct_on `deg p` >| [
    rpt strip_tac >>
    Cases_on `roots p = EMPTY` >-
    rw[] >>
    metis_tac[poly_deg_eq_zero, poly_eval_const, poly_root_def, poly_roots_member, MEMBER_NOT_EMPTY],
    rpt strip_tac >>
    Cases_on `roots p = EMPTY` >-
    rw[] >>
    `?z. z IN R /\ root p z` by metis_tac[poly_roots_member, MEMBER_NOT_EMPTY] >>
    `poly (factor z) /\ (deg (factor z) = 1) /\ (lead (factor z) = #1)` by rw[poly_factor_property] >>
    `0 < 1` by decide_tac >>
    `unit (lead (factor z))` by rw[] >>
    `(p = p / factor z * factor z + p % factor z) /\ poly (p / factor z)` by rw[poly_div_mod_def] >>
    `p % factor z = |0|` by rw[GSYM poly_root_thm] >>
    `p = p / factor z * factor z` by metis_tac[poly_add_rzero, poly_mult_poly] >>
    `(p / factor z) <> |0|` by metis_tac[poly_mult_lzero] >>
    `lead (p / factor z) IN R /\ lead (p / factor z) <> #0` by rw[] >>
    `lead (p / factor z) * lead (factor z) <> #0` by metis_tac[ring_unit_mult_zero, ring_mult_comm, ring_unit_element] >>
    `deg p = deg (p / factor z) + 1` by metis_tac[weak_deg_mult_nonzero, poly_is_weak] >>
    `deg (p / factor z) = v` by decide_tac >>
    metis_tac[poly_roots_mult, poly_roots_factor, UNION_COMM, GSYM INSERT_SING_UNION, FINITE_INSERT]
  ]);

(* Theorem: A nonzero polynomial cannot have more roots than its degree, i.e. CARD (roots p) <= deg p *)
(* Proof:
   First, the nonzero polynomial has only a finite number of roots, by poly_roots_finite.
   If p has no root, this is trivially true.
   Hence assume there is a root z, i.e. z IN R and eval p z = #0.
   Induct on degree of polynomial p.
   Base case: (0 = deg p) /\ p <> |0| ==> CARD (roots p) <= deg p
      Since deg p = 0 and p <> |0|,
      p = [h] /\ h <> #0    by poly_deg_eq_zero
      eval [h] z = h <> #0  by poly_eval_const
      contradicting eval p z = #0.
   Step case: deg p = v ==> CARD (roots p) <= deg p  ==>
              deg p = SUC v ==> CARD (roots p) <= deg p
      Since root p z,
         p % (factor z) = |0|            by poly_root_thm
      or p = (p / factor z) * factor z   by poly_div_mod_def
      now, poly (p / factor z) has degree (SUC v) - 1 = v,
      so it has no more than v roots by induction hypothesis.
      If z is a root of (p / factor z), p just has same roots.
      If z is not a root of (p / factor z), p has one more root.
      In either case, p has at most (SUC v) roots.
*)
val poly_roots_count = store_thm(
  "poly_roots_count",
  ``!r:'a field. Field r ==> !p. poly p /\ p <> |0| ==> CARD (roots p) <= deg p``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  Induct_on `deg p` >| [
    rpt strip_tac >>
    Cases_on `roots p = EMPTY` >-
    rw[] >>
    `?z. z IN R /\ root p z` by metis_tac[poly_roots_member, MEMBER_NOT_EMPTY] >>
    metis_tac[poly_deg_eq_zero, poly_eval_const, poly_root_def],
    rpt strip_tac >>
    Cases_on `roots p = EMPTY` >-
    rw[] >>
    `?z. z IN R /\ root p z` by metis_tac[poly_roots_member, MEMBER_NOT_EMPTY] >>
    `poly (factor z) /\ (deg (factor z) = 1) /\ (lead (factor z) = #1)` by rw[poly_factor_property] >>
    `0 < 1` by decide_tac >>
    `unit (lead (factor z))` by rw[] >>
    `(p = p / factor z * factor z + p % factor z) /\ poly (p / factor z)` by rw[poly_div_mod_def] >>
    `p % factor z = |0|` by rw[GSYM poly_root_thm] >>
    `p = p / factor z * factor z` by metis_tac[poly_add_rzero, poly_mult_poly] >>
    `p / factor z <> |0|` by metis_tac[poly_mult_lzero] >>
    `lead (p / factor z) IN R /\ lead (p / factor z) <> #0` by rw[] >>
    `lead (p / factor z) * lead (factor z) <> #0` by metis_tac[ring_unit_mult_zero, ring_mult_comm, ring_unit_element] >>
    `deg p = deg (p / factor z) + 1` by metis_tac[weak_deg_mult_nonzero, poly_is_weak] >>
    `deg (p / factor z) = v` by decide_tac >>
    `CARD (roots (p / factor z)) <= v` by rw[] >>
    `roots p = roots (p / factor z) UNION roots (factor z)` by metis_tac[poly_roots_mult] >>
    `_ = roots (p / factor z) UNION {z}` by rw[poly_roots_factor] >>
    `_ = z INSERT roots (p / factor z)` by rw[UNION_COMM, GSYM INSERT_SING_UNION] >>
    Cases_on `root (p / factor z) z` >| [
      `z IN roots (p / factor z)` by rw[poly_roots_member] >>
      `roots p = roots (p / factor z)` by rw[GSYM ABSORPTION] >>
      metis_tac[LESS_EQ_SUC_REFL, LESS_EQ_TRANS],
      `z NOTIN roots (p / factor z)` by rw[poly_roots_member] >>
      `FINITE (roots (p / factor z))` by rw[poly_roots_finite] >>
      `CARD (roots p) = SUC (CARD (roots (p / factor z)))` by rw[] >>
      metis_tac[LESS_EQ_MONO]
    ]
  ]);

(* Interesting note.
   By Fermat's Little Theorem, for prime p,
   In (mult_mod p), polynomial (x^p - x) has all elements as roots.
   Thus by poly_root_thm,
        x^p - x = (x - ##0)*(x - ##1)*(x - ##2)*...*(x - ##(p-1))   mod p
                = x * (x - #1) * (x - ##2) * ... * (x - ##(p-1))    mod p

   Is this identity of any significance?
   Yes! This is the key idea to show that the multiplicative group of F is cyclic.
*)

(* Theorem: Ring r ==> !c. c IN R /\ c <> #0 ==> (roots [c] = {}) *)
(* Proof:
   By poly_roots_member, this is to show: x IN R /\ root [c] x ==> F.
   Since root [c] x <=> eval [c] x = #0     by poly_root_def
                    <=>          c = #0     by poly_eval_const
   This contradicts c <> #0.
*)
val poly_roots_const = store_thm(
  "poly_roots_const",
  ``!r:'a ring. Ring r ==> !c. c IN R /\ c <> #0 ==> (roots [c] = {})``,
  metis_tac[poly_roots_member, MEMBER_NOT_EMPTY, poly_root_def, poly_eval_const]);

(* Theorem: Ring r /\ #1 <> #0 ==> (roots |1| = {}) *)
(* Proof:
     roots |1|
   = roots [#1]      by poly_one, #1 <> #0
   = {}              by poly_roots_const, #1 IN R
*)
val poly_roots_one = store_thm(
  "poly_roots_one",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> (roots |1| = {})``,
  rw[poly_roots_const, poly_one]);

(* Theorem: (roots p) SUBSET (roots q) ==>
            !s t. poly s /\ poly t ==> (roots p) SUBSET (roots (s * p + t * q)) *)
(* Proof:
   By definitions, this is to show: x IN R ==> eval (s * p + t * q) x = #0
     eval (s * p + t * q) x
   = eval (s * p) x + eval (t * q) x                     by poly_eval_add
   = (eval s x) * (eval p x) + (eval t x) * (eval q x)   by poly_eval_mult
   = (eval s x) * #0 + (eval t x) * #0                   by given
   = #0 + #0                                             by ring_mult_rzero
   = #0                                                  by ring_add_zero_zero
*)
val poly_roots_linear = store_thm(
  "poly_roots_linear",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ (roots p) SUBSET (roots q) ==>
   !s t. poly s /\ poly t ==> (roots p) SUBSET (roots (s * p + t * q))``,
  rw[SUBSET_DEF, poly_roots_member, poly_root_def, poly_eval_add, poly_eval_mult]);

(* Theorem: Ring r ==> !p q. poly p /\ poly q /\ roots p SUBSET roots q ==>
            !s t. poly s /\ poly t ==> roots p SUBSET roots (s * p - t * q) *)
(* Proof:
     s * p - t * q
   = s * p + (-(t * q))     by poly_sub_def
   = s * p + (-t) * q       by poly_neg_mult
   And poly (-t)            by poly_neg_poly
   The result follows       by poly_roots_linear
*)
val poly_roots_linear_sub = store_thm(
  "poly_roots_linear_sub",
  ``!r:'a ring. Ring r ==> !p q. poly p /\ poly q /\ roots p SUBSET roots q ==>
   !s t. poly s /\ poly t ==> roots p SUBSET roots (s * p - t * q)``,
  rw_tac std_ss[poly_sub_def, poly_neg_mult, poly_neg_poly, poly_roots_linear]);

(* Theorem: Ring r ==> !p. poly p ==> (roots (-p) = roots p) *)
(* Proof:
       roots (-p)
   <=> {x | x IN R /\ root (-p) x}    by poly_roots_def
   <=> {x | x IN R /\ root p x}       by poly_neg_poly, poly_root_neg, poly_neg_neg
   <=> roots p
*)
val poly_roots_neg = store_thm(
  "poly_roots_neg",
  ``!r:'a ring. Ring r ==> !p. poly p ==> (roots (-p) = roots p)``,
  rw[poly_roots_def, EXTENSION] >>
  metis_tac[poly_neg_poly, poly_root_neg, poly_neg_neg]);

(* Theorem: Ring r ==> !p q. ulead p /\ poly q /\ (roots p) SUBSET (roots q) ==> (roots p) SUBSET (roots (q % p)) *)
(* Proof:
   Note poly (q / p)                          by poly_div_poly
    and poly (q % p)                          by poly_mod_poly
    Now q = (q / p) * p + q % p               by poly_division_all, ulead p
     so    q % p = q - (q / p) * p            by poly_sub_eq_add
     or -(q % p) = (q / p) * p - q            by poly_neg_sub
                 = (q / p) * p - |1| * q      by poly_mult_lone
   Thus (roots p) SUBSET (roots (-(q % p)))   by poly_roots_linear_sub
     or (roots p) SUBSET (roots (q % p))      by poly_roots_neg
*)
val poly_roots_remainder = store_thm(
  "poly_roots_remainder",
  ``!r:'a ring. Ring r ==> !p q. ulead p /\ poly q /\ (roots p) SUBSET (roots q) ==> (roots p) SUBSET (roots (q % p))``,
  rpt strip_tac >>
  `poly (q / p) /\ poly (q % p)` by rw[] >>
  `q = (q / p) * p + q % p` by rw[poly_division_all] >>
  `-(q % p) = (q / p) * p - q` by metis_tac[poly_sub_eq_add, poly_neg_sub, poly_mult_poly] >>
  `_ = (q / p) * p - |1| * q` by rw[] >>
  metis_tac[poly_roots_linear_sub, poly_roots_neg, poly_one_poly]);

(* Theorem: Field r ==> !c p. c IN R /\ c <> #0 /\ poly p ==> (roots (c * p) = roots p) *)
(* Proof:
   By poly_roots_def, EXTENSION, this is to show:
      !x. x IN R /\ root (c * p) x <=> x IN R /\ root p x
   This is true by poly_root_cmult.
*)
val poly_roots_cmult = store_thm(
  "poly_roots_cmult",
  ``!r:'a field. Field r ==> !c p. c IN R /\ c <> #0 /\ poly p ==> (roots (c * p) = roots p)``,
  rpt strip_tac >>
  rw[poly_roots_def, EXTENSION] >>
  metis_tac[poly_root_cmult]);

(* Theorem: roots (p * q) = roots p UNION roots q *)
(* Proof: by p * q = |0| iff p = |0| or q = |0|.
   !x. x IN roots (p * q)
   <=> root (p * q) x                  by poly_roots_member
   <=> (p * q)(x) = #0                 by poly_root_def
   <=> p(x) * q(x) = #0                by poly_eval_mult
   <=> p(x) = #0  or q(x) = #0         by IntegralDomain_def
   <=> root p x   or  root q x         by poly_root_def
   <=> x IN roots p or x IN roots q    by poly_roots_member
   <=> x IN (roots p UNION roots q)    by IN_UNION
*)
val poly_roots_mult_id = store_thm(
  "poly_roots_mult_id",
  ``!r:'a ring. IntegralDomain r ==>
   !p q. poly p /\ poly q ==> (roots (p * q) = roots p UNION roots q)``,
  rw[IntegralDomain_def] >>
  (rw[poly_roots_member, poly_root_def, EXTENSION, EQ_IMP_THM] >> simp[]) >>
  rfs[poly_eval_mult]);

(* Theorem: A nonzero polynomial has only a finite number of roots, i.e. FINITE (roots p) *)
(* Proof:
   If p has no root, this is trivially true by FINITE_EMPTY.
   Hence assume there is a root z, i.e. z IN R and eval p z = #0  by poly_roots_member.
   Induct on degree of polynomial p.
   Base case: (0 = deg p) /\ p <> |0| ==> FINITE (roots p)
      Since deg p = 0 and p <> |0|,
      p = [h] /\ h <> #0    by poly_deg_eq_zero
      eval [h] z = h <> #0  by poly_eval_const
      contradicting eval p z = #0.
   Step case: deg p = v ==> FINITE (roots p)  ==>
              deg p = SUC v ==> FINITE (roots p)
      Since root p z,
         p % (factor z) = |0|            by poly_root_thm
      or p = (p / factor z) * factor z   by poly_div_mod_def
      now, poly (p / factor z) has degree (SUC v) - 1 = v,
      so it has finite number of roots by induction hypothesis
      or FINITE (roots (p / factor z)).
      Since roots p
          = roots (p / factor z) UNION roots (factor z)  by poly_roots_mult_id
          = roots (p / factor z) UNION {z}               by poly_roots_factor
          = z INSERT roots (p / factor z)                by INSERT_SING_UNION
      Hence FINITE (roots p)                             by FINITE_INSERT
*)
val poly_roots_finite_id = store_thm(
  "poly_roots_finite_id",
  ``!r:'a ring. IntegralDomain r ==> !p. poly p /\ p <> |0| ==> FINITE (roots p)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by metis_tac[IntegralDomain_def] >>
  (Induct_on `deg p` >> rpt strip_tac) >| [
    Cases_on `roots p = EMPTY` >-
    rw[] >>
    metis_tac[poly_deg_eq_zero, poly_eval_const, poly_root_def, poly_roots_member, MEMBER_NOT_EMPTY],
    Cases_on `roots p = EMPTY` >-
    rw[] >>
    `?z. z IN R /\ root p z` by metis_tac[poly_roots_member, MEMBER_NOT_EMPTY] >>
    `poly (factor z) /\ (deg (factor z) = 1) /\ (lead (factor z) = #1)` by rw[poly_factor_property] >>
    `0 < 1` by decide_tac >>
    `unit (lead (factor z))` by rw[] >>
    `(p = p / factor z * factor z + p % factor z) /\ poly (p / factor z)` by rw[poly_div_mod_def] >>
    `p % factor z = |0|` by rw[GSYM poly_root_thm] >>
    `p = p / factor z * factor z` by metis_tac[poly_add_rzero, poly_mult_poly] >>
    `(p / factor z) <> |0|` by metis_tac[poly_mult_lzero] >>
    `lead (p / factor z) IN R /\ lead (p / factor z) <> #0` by rw[] >>
    `lead (p / factor z) * lead (factor z) <> #0` by metis_tac[ring_unit_mult_zero, ring_mult_comm, ring_unit_element] >>
    `deg p = deg (p / factor z) + 1` by metis_tac[weak_deg_mult_nonzero, poly_is_weak] >>
    `deg (p / factor z) = v` by decide_tac >>
    metis_tac[poly_roots_mult_id, poly_roots_factor, UNION_COMM, GSYM INSERT_SING_UNION, FINITE_INSERT]
  ]);

(* Theorem: A nonzero polynomial cannot have more roots than its degree, i.e. CARD (roots p) <= deg p *)
(* Proof:
   First, the nonzero polynomial has only a finite number of roots, by poly_roots_finite.
   If p has no root, this is trivially true.
   Hence assume there is a root z, i.e. z IN R and eval p z = #0.
   Induct on degree of polynomial p.
   Base case: (0 = deg p) /\ p <> |0| ==> CARD (roots p) <= deg p
      Since deg p = 0 and p <> |0|,
      p = [h] /\ h <> #0    by poly_deg_eq_zero
      eval [h] z = h <> #0  by poly_eval_const
      contradicting eval p z = #0.
   Step case: deg p = v ==> CARD (roots p) <= deg p  ==>
              deg p = SUC v ==> CARD (roots p) <= deg p
      Since root p z,
         p % (factor z) = |0|            by poly_root_thm
      or p = (p / factor z) * factor z   by poly_div_mod_def
      now, poly (p / factor z) has degree (SUC v) - 1 = v,
      so it has no more than v roots by induction hypothesis.
      If z is a root of (p / factor z), p just has same roots.
      If z is not a root of (p / factor z), p has one more root.
      In either case, p has at most (SUC v) roots.
*)
val poly_roots_count_id = store_thm(
  "poly_roots_count_id",
  ``!r:'a ring. IntegralDomain r ==> !p. poly p /\ p <> |0| ==> CARD (roots p) <= deg p``,
  rpt (stripDup[IntegralDomain_def]) >>
  (Induct_on `deg p` >> rpt strip_tac) >| [
    Cases_on `roots p = EMPTY` >-
    rw[] >>
    `?z. z IN R /\ root p z` by metis_tac[poly_roots_member, MEMBER_NOT_EMPTY] >>
    metis_tac[poly_deg_eq_zero, poly_eval_const, poly_root_def],
    Cases_on `roots p = EMPTY` >-
    rw[] >>
    `?z. z IN R /\ root p z` by metis_tac[poly_roots_member, MEMBER_NOT_EMPTY] >>
    `poly (factor z) /\ (deg (factor z) = 1) /\ (lead (factor z) = #1)` by rw[poly_factor_property] >>
    `0 < 1` by decide_tac >>
    `unit (lead (factor z))` by rw[] >>
    `(p = p / factor z * factor z + p % factor z) /\ poly (p / factor z)` by rw[poly_div_mod_def] >>
    `p % factor z = |0|` by rw[GSYM poly_root_thm] >>
    `p = p / factor z * factor z` by metis_tac[poly_add_rzero, poly_mult_poly] >>
    `p / factor z <> |0|` by metis_tac[poly_mult_lzero] >>
    `lead (p / factor z) IN R /\ lead (p / factor z) <> #0` by rw[] >>
    `lead (p / factor z) * lead (factor z) <> #0` by metis_tac[ring_unit_mult_zero, ring_mult_comm, ring_unit_element] >>
    `deg p = deg (p / factor z) + 1` by metis_tac[weak_deg_mult_nonzero, poly_is_weak] >>
    `deg (p / factor z) = v` by decide_tac >>
    `CARD (roots (p / factor z)) <= v` by rw[] >>
    `roots p = roots (p / factor z) UNION roots (factor z)` by metis_tac[poly_roots_mult_id] >>
    `_ = roots (p / factor z) UNION {z}` by rw[poly_roots_factor] >>
    `_ = z INSERT roots (p / factor z)` by rw[UNION_COMM, GSYM INSERT_SING_UNION] >>
    Cases_on `root (p / factor z) z` >| [
      `z IN roots (p / factor z)` by rw[poly_roots_member] >>
      `roots p = roots (p / factor z)` by rw[GSYM ABSORPTION] >>
      metis_tac[LESS_EQ_SUC_REFL, LESS_EQ_TRANS],
      `z NOTIN roots (p / factor z)` by rw[poly_roots_member] >>
      `FINITE (roots (p / factor z))` by rw[poly_roots_finite_id] >>
      `CARD (roots p) = SUC (CARD (roots (p / factor z)))` by rw[] >>
      decide_tac
    ]
  ]);

(* ------------------------------------------------------------------------- *)
(* Roots of Unity                                                            *)
(* ------------------------------------------------------------------------- *)

(*
Note:
Although roots_of_unity can be defined in the context of Groups,
its cardinality can be almost anything, purely from group considerations.

For example, given a set s, its power set G = POW s forms a group under symmetric difference:
identity = {} = e, and every element is self-inverse, i.e. x^2 = e, and only e^1 = e.

So for this group g,
   CARD (uroots 1).carrier = 1
   CARD (uroots 2).carrier = CARD (POW s) = 2 ** CARD s   since x^2 = e
   CARD (uroots 3).carrier = 1                            since x^3 = x * x^2 = x * e = x
   CARD (uroots 4).carrier = CARD (POW s) = 2 ** CARD s   since x^4 = x^2 * x^2 = e * e = e

For this group,  CARD (uroots n).carrier = if (odd n) 1 else CARD G.

So it is possible to have: n < CARD (uroots n).carrier   take n = 2, for some set with CARD s > 1.
               as well as: n > CARD (uroots n).carrier   take n = 3.
*)

(*
However, in the context of Field r, let g = r.prod.
Then:
* Every element x IN R is a root of the master polynomial: x ** CARD R = x, or x ** CARD R - x = #0
* Every nonzero element is a root of the Fermat polynomial: x ** CARD R+ = #1, or x ** CARD R+ - #1 = #0
* Every nonzero, non-one element is a root of the cylcotomic cofactor: (cyclic n)  where n = CARD R+
* These are the only roots, as there are (PRE n) nonzero, non-one elements, and deg (cyclic n) = PRE n.

But Q is a field: it has 2 square-roots of 1, only 1 cube-root of 1, only 2 fourth-roots of 1.
Only in C will there be n n-th roots of 1. This is the idea of splitting field.
So what's wrong with the above 'proof' ?
The master polynomial is for a specific n = char r, not any n.
*)

(* Theorem: Ring r ==> (roots_of_unity r.prod n).carrier = roots (unity n) *)
(* Proof:
     (roots_of_unity r.prod n).carrier
   = {x | x IN G /\ (x ** n = #1)}             by roots_of_unity_def
   = {x | x IN G /\ (x ** n - #1 = #0)}        by ring_sub_eq_zero
   = {x | x IN G /\ (eval (unity n) x = #0)}   by poly_eval_X_exp_n_sub_c
   = {x | x IN G /\ root (unity n) x}          by poly_root_def
   = roots (unity n)                           by poly_roots_def
*)
val ring_uroots_are_roots = store_thm(
  "ring_uroots_are_roots",
  ``!r:'a ring. Ring r ==> !n. (roots_of_unity r.prod n).carrier = roots (unity n)``,
  rw_tac std_ss[roots_of_unity_def, poly_roots_def, poly_root_def, GSPECIFICATION, EXTENSION] >>
  rw_tac std_ss[ring_carriers] >>
  `(### 1 = |1|) /\ (## 1 = #1) /\ #1 IN R` by rw[poly_ring_sum_1] >>
  metis_tac[poly_eval_X_exp_n_sub_c, ring_sub_eq_zero, ring_exp_element]);

(* Theorem: Field r ==> (roots_of_unity f* n).carrier = roots (unity n) *)
(* Proof:
     (roots_of_unity f* n).carrier
   = {x | x IN F* /\ (x ** n = #1)}             by roots_of_unity_def
   = {x | x IN R+ /\ (x ** n = #1)}             by field_nonzero_mult_property
   = {x | x IN R+ /\ (x ** n - #1 = #0)}        by ring_sub_eq_zero
   = {x | x IN R+ /\ (eval (unity n) x = #0)}   by poly_eval_X_exp_n_sub_c
   = {x | x IN R+ /\ root (unity n) x}          by poly_root_def
   = roots (unity n)                            by poly_roots_def
*)
val field_uroots_are_roots = store_thm(
  "field_uroots_are_roots",
  ``!r:'a field. Field r ==> !n. 0 < n ==> ((roots_of_unity f* n).carrier = roots (unity n))``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `!x. x IN R ==> !n. eval (unity n) x = x ** n - #1` by rw[] >>
  rw_tac std_ss[roots_of_unity_def, poly_roots_def, poly_root_def, GSPECIFICATION, EXTENSION] >>
  rw_tac std_ss[field_nonzero_mult_property, EQ_IMP_THM] >| [
    rw[field_nonzero_element],
    `x IN R` by rw[ring_nonzero_element] >>
    `x ** n - #1 = #0` by rw[ring_sub_eq_zero] >>
    metis_tac[],
    `x ** n = #1` by metis_tac[ring_sub_eq_zero, ring_one_element, ring_exp_element] >>
    `x <> #0` by metis_tac[ring_zero_exp, NOT_ZERO_LT_ZERO] >>
    rw[ring_nonzero_eq],
    metis_tac[ring_sub_eq_zero, ring_one_element, ring_exp_element]
  ]);

(* Theorem: Field ==> 0 < n ==> CARD (roots_of_unity r.prod n).carrier <= n *)
(* Proof:
   Since (roots_of_unity r.prod n).carrier
       = roots (unity n)      by ring_uroots_are_roots
     and poly (unity n)       by poly_X, poly_exp_poly, poly_sub_poly
     and monic (unity n)      by poly_monic_X_exp_n_sub_c
    Now  X <> |1|             by poly_one
     so  X ** n <> |1|        by poly_monic_exp_eq_one, since n <> 0
    hence (unity n) <> |0|    by poly_sub_eq_zero
    With  deg (unity n) = n   by poly_deg_X_exp_n_sub_c
    The result follows by poly_roots_count.
*)
val field_uroots_card_upper = store_thm(
  "field_uroots_card_upper",
  ``!r:'a field. Field r ==> !n. 0 < n ==> CARD (roots_of_unity r.prod n).carrier <= n``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `(roots_of_unity r.prod n).carrier = roots (unity n)` by rw[ring_uroots_are_roots] >>
  `deg (unity n) = n` by metis_tac[poly_deg_X_exp_n_sub_c, poly_ring_sum_1] >>
  `poly (unity n)` by rw[] >>
  `monic (unity n)` by metis_tac[poly_monic_X_exp_n_sub_c, poly_ring_sum_1] >>
  `n <> 0` by decide_tac >>
  `(unity n) <> |0|` by rw[poly_sub_eq_zero, poly_monic_exp_eq_one, poly_one] >>
  metis_tac[poly_roots_count]);

(* ------------------------------------------------------------------------- *)
(* Roots of Unity Polynomial                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: x IN R ==> !n. eval (unity n) x = x ** n - #1 *)
(* Proof:
     eval (unity n) x
   = eval (X ** n) x - eval |1| x    by poly_eval_sub
   = (eval X x) ** n - eval |1| x    by poly_eval_exp
   = x ** n - eval |1| x             by poly_eval_X
   = x ** n - #1                     by poly_eval_one
*)
val poly_unity_eval = store_thm(
  "poly_unity_eval",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !n. eval (unity n) x = x ** n - #1``,
  rw[poly_eval_exp]);

(* Theorem: x IN R ==> !n. root (unity n) x <=> (x ** n = #1) *)
(* Proof:
       root (unity n) x
   <=> eval (unity n) x = #0      by poly_root_def
   <=> x ** n - #1 = #0           by poly_unity_eval
   <=> x ** n = #1                by ring_sub_eq_add, ring_add_rzero.
*)
val poly_unity_root_property = store_thm(
  "poly_unity_root_property",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !n. root (unity n) x <=> (x ** n = #1)``,
  rw_tac std_ss[poly_root_def, poly_unity_eval] >>
  `x ** n IN R /\ #1 IN R /\ #0 IN R` by rw[] >>
  metis_tac[ring_sub_eq_add, ring_add_rzero]);

(* Theorem: Ring r ==> !n. root (unity n) #1 *)
(* Proof:
   Since #1 IN R              by ring_one_element
     and #1 ** n = #1         by ring_one_exp
   Hence root (unity n) #1    by poly_unity_root_property
*)
val poly_unity_root_has_one = store_thm(
  "poly_unity_root_has_one",
  ``!r:'a ring. Ring r ==> !n. root (unity n) #1``,
  rw[poly_unity_root_property]);

(* Theorem: Ring r /\ #1 <> #0 ==> !n. 0 < n ==> ~(root (unity n) #0) *)
(* Proof:
       root (unity n) #0
   <=> eval (unity n) #0 = #0       by poly_root_def
   <=> #0 ** n - #1 = #0            by poly_unity_eval
   <=>      #0 - #1 = #0            by ring_zero_exp, 0 < n
   <=>           #0 = #1            by ring_sub_eq_zero
   <=>              F               by given #1 <> #0
*)
val poly_unity_root_nonzero = store_thm(
  "poly_unity_root_nonzero",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. 0 < n ==> ~(root (unity n) #0)``,
  rw[poly_root_def, ring_zero_exp]);

(* Theorem: Ring r /\ #1 <> #0 ==> !n. 0 < n ==> #0 NOTIN (roots (unity n)) *)
(* Proof: by poly_unity_root_nonzero, poly_roots_member *)
val poly_unity_roots_no_zero = store_thm(
  "poly_unity_roots_no_zero",
  ``!r:'a ring. Ring r /\ #1 <> #0 ==> !n. 0 < n ==> #0 NOTIN (roots (unity n))``,
  rw_tac std_ss[poly_unity_root_nonzero, poly_roots_member]);

(* Theorem: Ring r ==> !n. #1 IN roots (unity n) *)
(* Proof: by poly_unity_root_has_one, poly_roots_member *)
val poly_unity_roots_has_one = store_thm(
  "poly_unity_roots_has_one",
  ``!r:'a ring. Ring r ==> !n. #1 IN roots (unity n)``,
  rw[poly_unity_root_has_one, poly_roots_member]);

(* Theorem: Ring r ==> !n. roots (unity n) <> {} *)
(* Proof: by poly_unity_roots_has_one, MEMBER_NOT_EMPTY *)
val poly_unity_roots_nonempty = store_thm(
  "poly_unity_roots_nonempty",
  ``!r:'a ring. Ring r ==> !n. roots (unity n) <> {}``,
  metis_tac[poly_unity_roots_has_one, MEMBER_NOT_EMPTY]);

(* Theorem: Ring r ==> !x. x IN R ==> !n. x IN roots (unity n) <=> (x ** n = #1) *)
(* Proof: by poly_unity_root_property,poly_roots_member  *)
val poly_unity_roots_property = store_thm(
  "poly_unity_roots_property",
  ``!r:'a ring. Ring r ==> !x. x IN R ==> !n. x IN roots (unity n) <=> (x ** n = #1)``,
  rw[poly_unity_root_property, poly_roots_member]);

(* Theorem: Field r ==> !n. 0 < n ==> FINITE (roots (unity n)) *)
(* Proof:
   Note poly (unity n)              by poly_unity_poly
    and unity n <> |0|              by poly_unity_eq_zero, 0 < n
    ==> FINITE (roots (unity n))    by poly_roots_finite
*)
val poly_unity_roots_finite = store_thm(
  "poly_unity_roots_finite",
  ``!r:'a field. Field r ==> !n. 0 < n ==> FINITE (roots (unity n))``,
  rpt strip_tac >>
  `poly (unity n)` by rw[] >>
  `unity n <> |0|` by rw[poly_unity_eq_zero] >>
  rw[poly_roots_finite]);

(* ------------------------------------------------------------------------- *)
(* Roots of Master Polynomial                                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Ring r ==> !x n. x IN R ==> (eval (master n) x = x ** n - x) *)
(* Proof:
     eval (master n) x
   = eval (X ** n - X) x           by notation
   = eval (X ** n) x - eval X x    by poly_eval_sub
   = (eval X x) ** n - eval X x    by poly_eval_exp
   = x ** n - x                    by poly_eval_X
*)
val poly_master_eval = store_thm(
  "poly_master_eval",
  ``!r:'a ring. Ring r ==> !x n. x IN R ==> (eval (master n) x = x ** n - x)``,
  rw[]);

(* Theorem: Ring r ==> !x n. x IN R ==> (root (master n) x <=> (x ** n = x)) *)
(* Proof:
      root (master n) x
  <=> eval (master n) x = #0     by poly_root_def
  <=> x ** n - x = #0            by poly_master_eval
  <=> x ** n = x                 by ring_sub_eq_zero
*)
val poly_master_root = store_thm(
  "poly_master_root",
  ``!r:'a ring. Ring r ==> !x n. x IN R ==> (root (master n) x <=> (x ** n = x))``,
  rw_tac std_ss[poly_root_def, poly_master_eval, ring_sub_eq_zero, ring_exp_element]);

(* Theorem: Ring r ==> !n. 0 < n ==> root (master n) #0 *)
(* Proof:
   Since #0 ** n = #0         by ring_zero_exp, n <> 0
     and #0 IN R              by ring_zero_element
     ==> root (master n) #0   by poly_master_root
*)
val poly_master_root_zero = store_thm(
  "poly_master_root_zero",
  ``!r:'a ring. Ring r ==> !n. 0 < n ==> root (master n) #0``,
  rpt strip_tac >>
  `n <> 0` by decide_tac >>
  `#0 ** n = #0` by rw[ring_zero_exp] >>
  rw[poly_master_root]);

(* Theorem: !n. root (master n) #1 *)
(* Proof:
     eval (X ** n - X) #1
   = eval (X ** n) #1 - eval (X) #1   by poly_eval_sub
   = (eval X #1) ** n - (eval X #1)   by poly_eval_exp
   = #1 ** n - #1                     by poly_eval_X
   = #1 - #1                          by ring_one_exp
   = #0                               by ring_sub_eq
   Hence root (master n) #1           by poly_root_def
   Or,
   Since #1 IN R                      by ring_one_element
     and #1 ** n = #1                 by ring_one_exp
   Hence root (master n) #1           by poly_master_root
*)
val poly_master_root_one = store_thm(
  "poly_master_root_one",
  ``!r:'a ring. Ring r ==> !n. root (master n) #1``,
  rw[poly_master_root]);

(* Theorem: Ring r ==> !n x. x IN roots (master n) <=> (x IN R /\ (x ** n = x)) *)
(* Proof: by poly_master_root, poly_roots_member *)
val poly_master_roots = store_thm(
  "poly_master_roots",
  ``!r:'a ring. Ring r ==> !n x. x IN roots (master n) <=> (x IN R /\ (x ** n = x))``,
  metis_tac[poly_master_root, poly_roots_member]);

(* Theorem: Ring r ==> !n. 0 < n ==> #0 IN roots (master n) *)
(* Proof: by poly_master_root_zero, poly_roots_member *)
val poly_master_roots_zero = store_thm(
  "poly_master_roots_zero",
  ``!r:'a ring. Ring r ==> !n. 0 < n ==> #0 IN roots (master n)``,
  rw[poly_master_root_zero, poly_roots_member]);

(* Theorem: Ring r ==> !n. #1 IN roots (master n) *)
(* Proof: by poly_master_root_one, poly_roots_member *)
val poly_master_roots_one = store_thm(
  "poly_master_roots_one",
  ``!r:'a ring. Ring r ==> !n. #1 IN roots (master n)``,
  rw[poly_master_root_one, poly_roots_member]);

(* Theorem: Field r ==> !n. n <> 1 ==> FINITE (roots (master n)) *)
(* Proof:
   Note poly (master n)             by poly_master_poly
    and master n <> |0|             by poly_master_eq_zero, n <> 1
    ==> FINITE (roots (unity n))    by poly_roots_finite
*)
val poly_master_roots_finite = store_thm(
  "poly_master_roots_finite",
  ``!r:'a field. Field r ==> !n. n <> 1 ==> FINITE (roots (master n))``,
  rw[poly_roots_finite, poly_master_eq_zero]);

(* Theorem: FiniteField r ==> !n. FINITE (roots (master n)) *)
(* Proof:
   If n = 1,
      Then master n = |0|     by poly_master_eq_zero
       and roots |0| = R      by poly_roots_zero
       and FINITE R           by FiniteField_def
   If n <> 1, true            by poly_master_roots_finite
*)
val poly_master_roots_finite_alt = store_thm(
  "poly_master_roots_finite_alt",
  ``!r:'a field. FiniteField r ==> !n. FINITE (roots (master n))``,
  rpt (stripDup[FiniteField_def]) >>
  Cases_on `n = 1` >| [
    `master n = |0|` by rw[poly_master_eq_zero] >>
    metis_tac[poly_roots_zero],
    rw[poly_master_roots_finite]
  ]);

(* Theorem: Field r ==> !n. 1 < n ==> CARD (roots (master n)) <= n *)
(* Proof:
   Note poly (master n)               by poly_master_poly
    and master n <> |0|               by poly_master_eq_zero, n <> 1
    and deg (master n) = n            by poly_master_deg, 1 < n
   ==> CARD (roots (master n)) <= n   by poly_roots_count
*)
val poly_master_roots_count = store_thm(
  "poly_master_roots_count",
  ``!r:'a field. Field r ==> !n. 1 < n ==> CARD (roots (master n)) <= n``,
  rpt strip_tac >>
  `poly (master n)` by rw[] >>
  `master n <> |0|` by rw[poly_master_eq_zero] >>
  `deg (master n) = n` by rw[] >>
  metis_tac[poly_roots_count]);

(* Theorem: Ring r ==> !n. 0 < n ==> (master n = X * unity (n - 1)) *)
(* Proof:
   Note 0 < n ==> 1 <= n            by LESS_IMP_LESS_OR_EQ
     X * unity (n - 1)
   = X * (X ** (n - 1) - |1|)       by notation
   = X * X ** (n - 1) - X * |1|     by poly_mult_rsub
   = X * X ** (n - 1) - X           by poly_mult_rone
   = X ** SUC (n - 1) - X           by poly_exp_SUC
   = X ** (n - 1 + 1) - X           by ADD1
   = X ** n - X                     by SUB_ADD, 1 <= n
   = master n                       by notation
*)
val poly_master_factors = store_thm(
  "poly_master_factors",
  ``!r:'a ring. Ring r ==> !n. 0 < n ==> (master n = X * unity (n - 1))``,
  rpt strip_tac >>
  `SUC (n - 1) = n` by decide_tac >>
  `X * (X ** (n - 1) - |1|) = X * X ** (n - 1) - X` by rw[poly_mult_rsub] >>
  `_ = X ** SUC (n - 1) - X` by rw[poly_exp_SUC] >>
  metis_tac[]);

(* Theorem: Ring r ==> !n. master (SUC n) = X * unity n *)
(* Proof:
      X * unity n
    = X * (X ** n - |1|)      by notation
    = X * X ** n - X * |1|    by poly_mult_sub
    = X ** (SUC n) - X * |1|  by poly_exp_SUC
    = X ** (SUC n) - X        by poly_mult_rone
    = master (SUC n)          by notation
*)
val poly_master_factors_alt = store_thm(
  "poly_master_factors_alt",
  ``!r:'a ring. Ring r ==> !n. master (SUC n) = X * unity n``,
  rpt strip_tac >>
  `poly X /\ poly (X ** n) /\ poly |1|` by rw[] >>
  `X * unity n = X * X ** n - X * |1|` by rw_tac std_ss[poly_mult_sub] >>
  `_ = X ** SUC n - X * |1|` by rw_tac std_ss[poly_exp_SUC] >>
  `_ = master (SUC n)` by rw_tac std_ss[poly_mult_rone] >>
  rw[]);

(* Theorem: Field r ==> !n. 0 < n ==> (roots (master n) = {#0} UNION roots (unity (n - 1))) *)
(* Proof:
     roots (master n)
   = roots (X * unity (n - 1))                 by poly_master_factors
   = (roots X) UNION (roots (unity (n - 1)))   by poly_roots_mult
   = {#0} UNION roots (unity (n - 1)))         by poly_roots_X
*)
val poly_master_roots_by_unity_roots = store_thm(
  "poly_master_roots_by_unity_roots",
  ``!r:'a field. Field r ==> !n. 0 < n ==> (roots (master n) = {#0} UNION roots (unity (n - 1)))``,
  rpt strip_tac >>
  `Ring r` by rw[] >>
  `poly X /\ poly (unity (n - 1))` by rw[] >>
  `master n = X * unity (n - 1)` by rw[GSYM poly_master_factors] >>
  metis_tac[poly_roots_mult, poly_roots_X]);

(* Theorem: Field r ==> !n. roots (master (n + 1)) = {#0} UNION roots (unity n) *)
(* Proof: by poly_master_roots_by_unity_roots *)
val poly_master_roots_by_unity_roots_alt = store_thm(
  "poly_master_roots_by_unity_roots_alt",
  ``!r:'a field. Field r ==> !n. roots (master (n + 1)) = {#0} UNION roots (unity n)``,
  metis_tac[poly_master_roots_by_unity_roots, DECIDE``0 < n + 1 /\ (n + 1 - 1 = n)``]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
