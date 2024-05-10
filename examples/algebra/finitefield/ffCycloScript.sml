(* ------------------------------------------------------------------------- *)
(* Finite Field: Cyclotomic Polynomials                                      *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "ffCyclo";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open arithmeticTheory pred_setTheory listTheory dividesTheory gcdTheory
     numberTheory combinatoricsTheory;

open ffBasicTheory;
open ffAdvancedTheory;
open ffPolyTheory;

open monoidTheory groupTheory ringTheory fieldTheory;
open groupOrderTheory;
open fieldOrderTheory;

(* Get polynomial theory of Ring *)
open polynomialTheory polyWeakTheory polyRingTheory polyDivisionTheory
     polyBinomialTheory;

(* (* val _ = load "polyFieldModuloTheory"; *) *)
open polyFieldTheory;
open polyFieldDivisionTheory;
open polyFieldModuloTheory;

open polyEvalTheory;
open polyRootTheory;

open polyDividesTheory;
open polyMonicTheory;
open polyProductTheory;
open polyGCDTheory;

(* ------------------------------------------------------------------------- *)
(* Finite Field Cyclotomic Polynomials Documentation                         *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   cyclo n       = poly_cyclo r n
*)
(* Definitions and Theorems (# are exported):

   Cyclotomic Polynomials:
   poly_cyclo_def     |- !r n. cyclo n = PIFACTOR (orders f* n)
   poly_cyclo_alt     |- !r n. Field r ==> (cyclo n = PPROD {X - c * |1| | c | c IN R+ /\ (forder c = n)})
   poly_cyclo_0       |- !r. FiniteField r ==> (cyclo 0 = |1|)
   poly_cyclo_1       |- !r. Field r ==> (cyclo 1 = X - |1|)
   poly_cyclo_monic   |- !r. FiniteField r ==> !n. monic (cyclo n)
   poly_cyclo_poly    |- !r. FiniteField r ==> !n. poly (cyclo n)
   poly_cyclo_lead    |- !r. FiniteField r ==> !n. lead (cyclo n) = #1
   poly_cyclo_deg     |- !r. FiniteField r ==> !n. deg (cyclo n) = CARD (orders f* n)
   poly_cyclo_roots   |- !r. FiniteField r ==> !n. roots (cyclo n) = orders f* n
   poly_cyclo_root_order         |- !r. FiniteField r ==> !x n. x IN roots (cyclo n) ==> (forder x = n)
   poly_cyclo_root_order_iff     |- !r. FiniteField r ==> !x. x IN R+ ==>
                                    !n. x IN roots (cyclo n) <=> (forder x = n)
   poly_cyclo_root_condition     |- !r. FiniteField r ==> !x n. x IN R /\ 0 < n ==>
                                        (x IN roots (cyclo n) <=> (forder x = n))
   poly_cyclo_factor_condition   |- !r. FiniteField r ==> !x n. x IN R /\ 0 < n ==>
                                        (factor x pdivides cyclo n <=> (forder x = n))
   poly_cyclo_has_factor_cyclo_1 |- !r. FiniteField r ==> !n. cyclo 1 pdivides cyclo n <=> (n = 1)
   poly_cyclo_deg_eq_card_roots  |- !r. FiniteField r ==> !n. deg (cyclo n) = CARD (roots (cyclo n))
   poly_cyclo_coprime            |- !r. FiniteField r ==> !m n. m <> n ==> pcoprime (cyclo m) (cyclo n)
   poly_cyclo_image_coprime_set  |- !r. FiniteField r ==> !s. pcoprime_set (IMAGE cyclo s)

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Cyclotomic Polynomials                                                    *)
(* ------------------------------------------------------------------------- *)

(* Define cyclotomic polynomials *)
val poly_cyclo_def = Define `
    poly_cyclo (r:'a ring) (n:num) = PIFACTOR (orders f* n)
`;
(* Overload on cyclotomic polynomial *)
val _ = overload_on("cyclo", ``poly_cyclo r``);
(*
> poly_cyclo_def;
val it = |- !r n. cyclo n = PIFACTOR (orders f* n): thm
*)

(* Theorem: Field r ==> (cyclo n = PPROD {(X - c * |1|) | c | c IN R+ /\ (forder c = n)}) *)
(* Proof: by poly_cyclo_def *)
val poly_cyclo_alt = store_thm(
  "poly_cyclo_alt",
  ``!(r:'a field) n. Field r ==> (cyclo n = PPROD {(X - c * |1|) | c | c IN R+ /\ (forder c = n)})``,
  rpt strip_tac >>
  `{(X - c * |1|) | c | c IN R+ /\ (forder c = n)} = IMAGE factor (orders f* n)` by
  (rw_tac std_ss[EXTENSION, GSPECIFICATION, IN_IMAGE] >>
  rw_tac std_ss[EQ_IMP_THM] >| [
    qexists_tac `c` >>
    rw[poly_factor_alt, field_nonzero_element] >>
    rw[field_orders_element_self],
    qexists_tac `x'` >>
    `x' IN R+ /\ (forder x' = n)` by metis_tac[fieldOrderTheory.field_orders_element_property] >>
    rw[poly_factor_alt, field_nonzero_element]
  ]) >>
  rw[poly_cyclo_def]);

(* Theorem: FiniteField r ==> (cyclo 0 = |1|) *)
(* Proof:
     cyclo 0
   = PIFACTOR (orders f* 0)      by poly_cyclo_def
   = PIFACTOR {}                 by field_orders_0
   = |1|                         by poly_prod_factors_empty
*)
val poly_cyclo_0 = store_thm(
  "poly_cyclo_0",
  ``!r:'a field. FiniteField r ==> (cyclo 0 = |1|)``,
  metis_tac[poly_cyclo_def, field_orders_0, poly_prod_factors_empty]);

(* Theorem: Field r ==> (cyclo 1 = X - |1|) *)
(* Proof:
     cyclo 1
   = PIFACTOR (orders f* 1)      by poly_cyclo_def
   = PIFACTOR {#1}               by field_orders_1
   = factor #1                   by poly_prod_factors_sing
   = X - |1|                     by poly_factor_one
*)
val poly_cyclo_1 = store_thm(
  "poly_cyclo_1",
  ``!r:'a field. Field r ==> (cyclo 1 = X - |1|)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0 /\ #1 IN R` by rw[] >>
  metis_tac[poly_cyclo_def, field_orders_1, poly_prod_factors_sing, poly_factor_one]);

(* Theorem: FiniteField r ==> !n. monic (cyclo n) *)
(* Proof:
   Note monic (cyclo n)
    <=> monic (PIFACTOR (orders f* n))        by poly_cyclo_def
    Now FINITE F*                             by finite_field_mult_finite_group, FiniteGroup_def
     so FINITE (orders f* n)                  by orders_finite, FINITE F*
    and FINITE (IMAGE factor (orders f* n))   by IMAGE_FINITE
    and !p. p IN IMAGE factor (orders f* n) ==> monic p  by field_orders_factor_image_member
   Hence monic (PIFACTOR (orders f* n))       by poly_monic_prod_set_monic
*)
val poly_cyclo_monic = store_thm(
  "poly_cyclo_monic",
  ``!r:'a field. FiniteField r ==> !n. monic (cyclo n)``,
  rpt (stripDup[FiniteField_def]) >>
  rw[poly_cyclo_def] >>
  `Ring r` by rw[] >>
  `FINITE F*` by metis_tac[finite_field_mult_finite_group, FiniteGroup_def] >>
  `FINITE (orders f* n)` by rw[orders_finite] >>
  `FINITE (IMAGE factor (orders f* n))` by rw[IMAGE_FINITE] >>
  metis_tac[poly_monic_prod_set_monic, field_orders_factor_image_member]);

(* Theorem: FiniteField r ==> !n. poly (cyclo n) *)
(* Proof: by poly_cyclo_monic, poly_monic_poly *)
val poly_cyclo_poly = store_thm(
  "poly_cyclo_poly",
  ``!r:'a field. FiniteField r ==> !n. poly (cyclo n)``,
  rw[poly_cyclo_monic]);

(* Theorem: FiniteField r ==> !n. lead (cyclo n) = #1 *)
(* Proof: by poly_cyclo_monic, poly_monic_lead *)
val poly_cyclo_lead = store_thm(
  "poly_cyclo_lead",
  ``!r:'a field. FiniteField r ==> !n. lead (cyclo n) = #1``,
  rw[poly_cyclo_monic]);

(*
> cyclic_orders_card |> ISPEC ``f*``;
val it = |- cyclic f* /\ FINITE F* ==>
            !n. CARD (orders f* n) = if n divides CARD F* then phi n else 0: thm
*)

(* Theorem: FiniteField r ==> !n. deg (cyclo n) = CARD (orders f* n) *)
(* Proof:
   By poly_cyclo_def, this is to show:
      deg (PIFACTOR (orders f* n)) = CARD (orders f* n)

    Now FINITE F*                             by finite_field_mult_finite_group, FiniteGroup_def
     so FINITE (orders f* n)                  by orders_finite, FINITE F*
    and FINITE (IMAGE factor (orders f* n))   by IMAGE_FINITE
    and !p. p IN (IMAGE factor (orders f* n))
    ==> monic p /\ (deg p = 1)                by field_orders_factor_image_member

   Also (orders f* n) SUBSET F*               by orders_subset
    and F* SUBSET R                           by field_nonzero_element_alt, SUBSET_DEF
   thus (orders f* n) SUBSET R                by SUBSET_TRANS
     so INJ factor (orders f* n) (PolyRing r).carrier   by poly_factor_inj
   Hence deg (PIFACTOR (orders f* n))
       = CARD (IMAGE factor (orders f* n))    by poly_monic_prod_set_monomials_deg
       = CARD (orders f* n)                   by INJ_CARD_IMAGE_EQ
*)
val poly_cyclo_deg = store_thm(
  "poly_cyclo_deg",
  ``!r:'a field. FiniteField r ==> !n. deg (cyclo n) = CARD (orders f* n)``,
  rpt (stripDup[FiniteField_def]) >>
  rw[poly_cyclo_def] >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `FINITE F*` by metis_tac[finite_field_mult_finite_group, FiniteGroup_def] >>
  `FINITE (orders f* n)` by rw[orders_finite] >>
  `FINITE (IMAGE factor (orders f* n))` by rw[IMAGE_FINITE] >>
  qabbrev_tac `s = IMAGE factor (orders f* n)` >>
  `!p. p IN s ==> monic p /\ (deg p = 1)` by metis_tac[field_orders_factor_image_member] >>
  `(orders f* n) SUBSET F* ` by rw[orders_subset] >>
  `F* SUBSET R` by rw[field_nonzero_element_alt, SUBSET_DEF] >>
  `(orders f* n) SUBSET R` by metis_tac[SUBSET_TRANS] >>
  metis_tac[poly_factor_inj, poly_monic_prod_set_monomials_deg, INJ_CARD_IMAGE_EQ]);

(* Theorem: FiniteField r ==> !n. roots (cyclo n) = (orders f* n) *)
(* Proof:
   Note (orders f* n) SUBSET R           by field_orders_subset_carrier
     so FINITE (orders f* n)             by SUBSET_FINITE, FINITE R
        roots (cyclo n)
      = roots (PIFACTOR (orders f* n))   by poly_cyclo_def
      = (orders f* n)                    by poly_prod_factors_roots
*)
val poly_cyclo_roots = store_thm(
  "poly_cyclo_roots",
  ``!r:'a field. FiniteField r ==> !n. roots (cyclo n) = (orders f* n)``,
  rpt (stripDup[FiniteField_def]) >>
  `(orders f* n) SUBSET R` by rw[field_orders_subset_carrier] >>
  `FINITE (orders f* n)` by metis_tac[SUBSET_FINITE] >>
  rw[poly_cyclo_def, poly_prod_factors_roots]);

(* Theorem: FiniteField r ==> !x n. x IN root (cyclo n) x ==> (forder x = n) *)
(* Proof:
       x IN roots (cyclo n)
   ==> x IN (orders f* n)        by poly_cyclo_roots
   ==> forder x = n              by field_orders_element_order
*)
val poly_cyclo_root_order = store_thm(
  "poly_cyclo_root_order",
  ``!r:'a field. FiniteField r ==> !x n. x IN roots (cyclo n) ==> (forder x = n)``,
  rw[FiniteField_def, poly_cyclo_roots, field_orders_element_order]);

(* Theorem: FiniteField r ==> !x. x IN R+ ==> !n. x IN roots (cyclo n) <=> (forder x = n) *)
(* Proof:
   If part: x IN roots (cyclo n) ==> forder x = n
      True by poly_cyclo_root_order
   Only-if part: forder x = n ==> x IN roots (cyclo n)
      With x IN R+ /\ forder x = n          by given
       ==> x IN orders f* n                 by field_orders_element_property
        or x IN roots (cyclo n)             by poly_cyclo_roots
*)
val poly_cyclo_root_order_iff = store_thm(
  "poly_cyclo_root_order_iff",
  ``!r:'a field. FiniteField r ==> !x. x IN R+ ==> !n. x IN roots (cyclo n) <=> (forder x = n)``,
  rpt (stripDup[FiniteField_def]) >>
  rw[EQ_IMP_THM] >-
  rw[poly_cyclo_root_order] >>
  rw[field_orders_element_property, poly_cyclo_roots]);

(* Theorem: FiniteField r ==> !x n. x IN R /\ 0 < n ==> (x IN roots (cyclo n) <=> (forder x = n)) *)
(* Proof:
   If part: x IN roots (cyclo n) ==> forder x = n
      True by poly_cyclo_root_order
   Only-if part: forder x = n ==> x IN roots (cyclo n)
      Note n <> 0, so x <> #0           by field_order_eq_0
      thus x IN R+                      by field_nonzero_eq
      With forder x = n                 by given
       ==> x IN orders f* n             by field_orders_element_property
        or x IN roots (cyclo n)         by poly_cyclo_roots
*)
val poly_cyclo_root_condition = store_thm(
  "poly_cyclo_root_condition",
  ``!r:'a field. FiniteField r ==> !x n. x IN R /\ 0 < n ==> (x IN roots (cyclo n) <=> (forder x = n))``,
  rpt (stripDup[FiniteField_def]) >>
  rw[EQ_IMP_THM] >-
  rw[poly_cyclo_root_order] >>
  `forder x <> 0` by decide_tac >>
  `x <> #0` by metis_tac[field_order_eq_0] >>
  `x IN R+` by rw[field_nonzero_eq] >>
  rw[field_orders_element_property, poly_cyclo_roots]);

(* Theorem: FiniteField r ==> !x n. x IN R /\ 0 < n ==> ((factor x) pdivides (cyclo n) <=> (forder x = n)) *)
(* Proof:
   If part: (factor x) pdivides cyclo n ==> forder x = n
      Note poly (factor x)          by poly_factor_poly
       and poly (cyclo n)           by poly_cyclo_poly
       Now x IN roots (factor x)    by poly_factor_roots, IN_SING
       and roots (factor x) SUBSET roots (cyclo n)   by poly_divides_share_roots
      thus x IN roots (cyclo n)     by SUBSET_DEF
       ==> forder x = n             by poly_cyclo_root_order

   Only-if part: forder x = n ==> (factor x) pdivides cyclo n
      Note x IN roots (cyclo n)            by poly_cyclo_root_condition, 0 < n
       ==> (factor x) pdivides (cyclo n)   by poly_root_factor
*)
val poly_cyclo_factor_condition = store_thm(
  "poly_cyclo_factor_condition",
  ``!r:'a field. FiniteField r ==> !x n. x IN R /\ 0 < n ==>
         ((factor x) pdivides (cyclo n) <=> (forder x = n))``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  `poly (cyclo n)` by rw[poly_cyclo_poly] >>
  rw[EQ_IMP_THM] >| [
    `poly (factor x)` by rw[poly_factor_poly] >>
    `x IN roots (factor x)` by rw[poly_factor_roots] >>
    `roots (factor x) SUBSET roots (cyclo n)` by rw[poly_divides_share_roots] >>
    metis_tac[poly_cyclo_root_order, SUBSET_DEF],
    metis_tac[poly_cyclo_root_condition, poly_root_factor]
  ]);

(* Theorem: FiniteField r ==> !n. (cyclo 1) pdivides (cyclo n) <=> (n = 1) *)
(* Proof:
   If part: cyclo 1 pdivides cyclo n ==> n = 1
      Note cyclo 1 = X - |1|       by poly_cyclo_1
        or         = factor #1     by poly_factor_one
      Claim: n <> 0
      Proof: By contradiction, suppose n = 0.
             Note cyclo 0 = |1|         by poly_cyclo_0
              Now poly (cyclo 1)        by poly_cyclo_poly
              ==> upoly (cyclo 1)       by poly_divides_one, (cyclo 1) pdivides |1|
              ==> deg (cyclo 1) = 0     by poly_field_units, upoly (cyclo 1)
              But deg (factor #1) = 1   by poly_deg_factor
             This is a contradiction since cyclo 1 = factor #1, by above.

      Thus n <> 0, or 0 < n                 by NOT_ZERO_LT_ZERO
      With (factor #1) pdivides (cyclo n)   by above
     Hence n = forder #1                    by poly_cyclo_factor_condition
             = 1                            by field_order_one

   Only-if part: n = 1 ==> cyclo 1 pdivides cyclo n
      Note poly (cyclo 1)                   by poly_cyclo_poly
      Thus (cyclo 1) pdivides (cyclo 1)     by poly_divides_reflexive
*)
val poly_cyclo_has_factor_cyclo_1 = store_thm(
  "poly_cyclo_has_factor_cyclo_1",
  ``!r:'a field. FiniteField r ==> !n. (cyclo 1) pdivides (cyclo n) <=> (n = 1)``,
  rpt (stripDup[FiniteField_def]) >>
  `Ring r /\ #1 <> #0` by rw[] >>
  rw[EQ_IMP_THM] >| [
    `cyclo 1 = X - |1|` by rw[poly_cyclo_1] >>
    `_ = factor #1` by rw[poly_factor_one] >>
    `n <> 0` by
  (spose_not_then strip_assume_tac >>
    `cyclo 0 = |1|` by rw[poly_cyclo_0] >>
    `poly (cyclo 1)` by rw[poly_cyclo_poly] >>
    `upoly (cyclo 1)` by metis_tac[poly_divides_one] >>
    `deg (cyclo 1) = 0` by metis_tac[poly_field_units] >>
    `deg (factor #1) = 1` by rw[poly_deg_factor] >>
    metis_tac[DECIDE``0 <> 1``]) >>
    `0 < n` by decide_tac >>
    `forder #1 = 1` by rw[field_order_one] >>
    metis_tac[poly_cyclo_factor_condition, field_one_element],
    rw[poly_divides_reflexive, poly_cyclo_poly]
  ]);

(* Theorem: FiniteField r ==> !n. deg (cyclo n) = CARD (roots (cyclo n)) *)
(* Proof:
     deg (cyclo n)
   = CARD (orders f* n)        by poly_cyclo_deg
   = CARD (roots (cyclo n))    by poly_cyclo_roots
*)
val poly_cyclo_deg_eq_card_roots = store_thm(
  "poly_cyclo_deg_eq_card_roots",
  ``!r:'a field. FiniteField r ==> !n. deg (cyclo n) = CARD (roots (cyclo n))``,
  rw[poly_cyclo_deg, poly_cyclo_roots]);

(* Note: This is worse than poly_cyclo_deg
|- !r. FiniteField r ==> !n. deg (cyclo n) = CARD (orders f* n)
But this does show that cyclo n splits, essentially by definition,
from product of factors, i.e. poly_prod_factors_deg_eq_card_roots.
*)

(* Theorem: Field r ==> !m n. m <> n ==> pcoprime (cyclo m) (cyclo n) *)
(* Proof:
   Note poly (cyclo m) /\ poly (cyclo n)         by poly_cyclo_poly
    Let s = (orders f* m), t = (orders f* n).
   Then FINITE s /\ FINITE t                     by field_orders_finite
    and s SUBSET R /\ t SUBSET R                 by field_orders_subset_carrier
   also DISJOINT s t                             by field_orders_disjoint, m <> n

     mpgcd (cyclo m) (cyclo n)
   = mpgcd (PIFACTOR s) (PIFACTOR t)             by poly_cyclo_def
   = PIFACTOR (s INTER t)                        by poly_prod_factors_monic_gcd
   = PIFACTOR {}                                 by DISJOINT_DEF
   = |1|                                         by poly_prod_factors_empty
*)
val poly_cyclo_coprime = store_thm(
  "poly_cyclo_coprime",
  ``!r:'a field. FiniteField r ==> !m n. m <> n ==> pcoprime (cyclo m) (cyclo n)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `s = (orders f* m)` >>
  qabbrev_tac `t = (orders f* n)` >>
  `FINITE s /\ FINITE t` by rw[field_orders_finite, Abbr`s`, Abbr`t`] >>
  `s SUBSET R /\ t SUBSET R` by rw[field_orders_subset_carrier, Abbr`s`, Abbr`t`] >>
  `mpgcd (cyclo m) (cyclo n) = mpgcd (PIFACTOR s) (PIFACTOR t)` by rw[poly_cyclo_def, Abbr`s`, Abbr`t`] >>
  `_ = PIFACTOR (s INTER t)` by rw[poly_prod_factors_monic_gcd] >>
  `_ = PIFACTOR {}` by metis_tac[field_orders_disjoint, DISJOINT_DEF] >>
  `_ = |1|` by rw[poly_prod_factors_empty] >>
  rw[poly_monic_gcd_one_coprime, poly_cyclo_poly]);

(* Theorem: FiniteField r ==> !s. pcoprime_set (IMAGE cyclo s) *)
(* Proof:
    Note pset (IMAGE cyclo s)           by poly_cyclo_poly, IN_IMAGE
     and !p q. p IN (IMAGE cyclo s) /\ q IN (IMAGE cyclo s) /\ p <> q
     ==> ?x y. x IN s /\ y IN s /\ (p = cyclo x) /\ (q = cyclo y) /\ cyclo x <> cyclo y   by IN_IMAGE
     ==> x <> y                         by cyclo x <> cyclo y
     ==> pcoprime p q                   by poly_cyclo_coprime
   Hence pcoprime_set (IMAGE cyclo s)   by poly_coprime_set_def
*)
val poly_cyclo_image_coprime_set = store_thm(
  "poly_cyclo_image_coprime_set",
  ``!r:'a field. FiniteField r ==> !s. pcoprime_set (IMAGE cyclo s)``,
  rpt strip_tac >>
  `pset (IMAGE cyclo s)` by metis_tac[poly_cyclo_poly, IN_IMAGE] >>
  `!p q. p IN (IMAGE cyclo s) /\ q IN (IMAGE cyclo s) /\ p <> q ==> pcoprime p q` by metis_tac[poly_cyclo_coprime, IN_IMAGE] >>
  rw[poly_coprime_set_def]);

(* ------------------------------------------------------------------------- *)
(* Cyclotomic Polynomial Properties.                                         *)
(* ------------------------------------------------------------------------- *)

(* Note:
   Further properties of the cyclotomic polynomials are given in ffUnity,
   because they depend on the roots of Unity, the unity polynomial.
*)


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
