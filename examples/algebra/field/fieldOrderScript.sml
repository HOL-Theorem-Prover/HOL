(* ------------------------------------------------------------------------- *)
(* Order of Elements in a Field                                              *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "fieldOrder";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory dividesTheory gcdTheory
     gcdsetTheory numberTheory combinatoricsTheory primeTheory;

open fieldTheory;
open integralDomainTheory;
open ringTheory;
open groupTheory;
open monoidTheory;

open groupOrderTheory subgroupTheory groupCyclicTheory;

(* ------------------------------------------------------------------------- *)
(* Order of Elements in a Field Documentation                                *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   forder x      = order f* x
   forder_       = order ((r_:'b ring).prod excluding r_.sum.id)
   forder_eq n   = field_order_equal r n
*)
(* Definitions and Theorems (# are exported):

   Finite Field Order:
   field_nonzero_order   |- !r. Field r ==> !x. order r.prod x = forder x
   field_order_property  |- !r. FiniteField r ==> !x. x IN R+ ==> 0 < forder x /\ (x ** forder x = #1)
   field_order_eqn       |- !r. Field r ==> !x. x ** forder x = #1
   field_order_minimal   |- !r. Field r ==> !x n. 0 < n /\ n < forder x ==> x ** n <> #1
   field_order_thm       |- !r. Field r ==> !n. 0 < n ==> !x. (forder x = n) <=>
                                            (x ** n = #1) /\ !m. 0 < m /\ m < n ==> x ** m <> #1
   field_nonzero_exp_eq  |- !r. Field r ==> !x. x IN R+ ==> !m n. m < forder x /\ n < forder x ==>
                                                            ((x ** m = x ** n) <=> (m = n))
   field_order_zero      |- !r. Field r ==> (forder #0 = 0)
   field_order_0         |- !r. Field r ==> !x. (forder x = 0) <=> !n. 0 < n ==> x ** n <> #1
   field_order_nonzero   |- !r. FiniteField r ==> !x. x IN R+ ==> forder x <> 0
   field_order_eq_0      |- !r. FiniteField r ==> !x. x IN R ==> ((forder x = 0) <=> (x = #0))
   field_order_one       |- !r. Field r ==> (forder #1 = 1)
   field_order_eq_1      |- !r. Field r ==> !x. x IN R ==> ((forder x = 1) <=> (x = #1))
   field_order_neg_one   |- !r. Field r ==> (forder (-#1) = if char r = 2 then 1 else 2)
   field_exp_mod_order   |- !r. Field r ==> !x. x IN R /\ 0 < forder x ==> !n. x ** n = x ** (n MOD forder x)
   finite_field_exp_mod_order   |- !r. FiniteField r ==> !x. x IN R+ ==> !n. x ** n = x ** (n MOD forder x)
   field_order_divides   |- !r. FiniteField r ==> !x. x IN R+ ==> (forder x) divides (CARD R+)
   field_order_upper     |- !r. FiniteField r ==> !x. x IN R ==> forder x < CARD R
   field_order_divides_exp     |- !r. Field r ==> !x. x IN R+ ==> !n. (x ** n = #1) <=> forder x divides n
   field_order_coprime_card    |- !r. FiniteField r ==> !x. x IN R+ ==> coprime (forder x) (CARD R)
   field_order_power           |- !r. Field r ==> !x. x IN R ==>
                                  !n. forder (x ** n) * gcd n (forder x) = forder x
   field_order_power_eqn       |- !r. Field r ==> !x. x IN R ==>
                                  !n. 0 < n ==> (forder (x ** n) = forder x DIV gcd n (forder x))
   field_order_power_coprime   |- !r. Field r ==> !x. x IN R ==>
                                  !n. coprime n (forder x) ==> (forder (x ** n) = forder x)
   field_order_power_eq_order  |- !r. FiniteField r ==> !x. x IN R /\ x <> #0 ==>
                                  !n. (forder (x ** n) = forder x) <=> coprime n (forder x)
   field_order_exp_cofactor    |- !r. Field r ==>
                                  !n x. x IN R+ /\ 0 < forder x /\ n divides forder x ==> (forder (x ** (forder x DIV n)) = n)

   Field Orders Property:
   field_orders_def              |- !r n. orders f* n = {x | x IN F* /\ (forder x = n)}
   field_orders_member           |- !r x n. x IN orders f* n <=> x IN F* /\ (forder x = n)
   field_orders_primitive        |- !r x. x IN orders f* (CARD F* ) <=> x IN F* /\ (forder x = CARD F* )
   field_orders_alt              |- !r. Field r ==> !n. orders f* n = {x | x IN R+ /\ (forder x = n)}
   field_orders_subset           |- !r. Field r ==> !n. orders f* n SUBSET R+
   field_orders_subset_carrier   |- !r. Field r ==> !n. orders f* n SUBSET R
   field_orders_nonzero_element  |- !r. Field r ==> !x n. x IN orders f* n ==> x IN R+
   field_orders_element_nonzero  |- !r. Field r ==> !x n. x IN orders f* n ==> x <> #0
   field_orders_element          |- !r. Field r ==> !x n. x IN orders f* n ==> x IN R
   field_orders_element_property |- !r. Field r ==> !x n. x IN orders f* n <=> x IN R+ /\ (forder x = n)
   field_orders_element_order    |- !r. Field r ==> !x n. x IN orders f* n ==> (forder x = n)
   field_orders_element_self     |- !r. Field r ==> !x. x IN R+ ==> x IN orders f* (forder x)
   field_orders_finite           |- !r. FiniteField r ==> !n. FINITE (orders f* n)
   field_orders_0                |- !r. FiniteField r ==> (orders f* 0 = {})
   field_orders_1                |- !r. Field r ==> (orders f* 1 = {#1})
   field_orders_disjoint         |- !r. Field r ==> !m n. m <> n ==> DISJOINT (orders f* m) (orders f* n)

   Equality of Order:
   field_order_equal_def       |- !r n. forder_eq n = {x | x IN R /\ (forder x = n)}
   field_order_equal_element   |- !r x n. x IN forder_eq n <=> x IN R /\ (forder x = n)
   field_order_equal_subset    |- !r n. forder_eq n SUBSET R
   field_order_equal_finite    |- !r. FINITE R ==> !n. FINITE (forder_eq n)
   field_order_equal_of_0      |- !r. FiniteField r ==> (forder_eq 0 = {#0})
   field_order_equal_of_1      |- !r. Field r ==> (forder_eq 1 = {#1})
   field_order_equal_has_zero  |- !r. Field r ==> !n. #0 IN forder_eq n <=> (n = 0)
   field_order_equal_eq_orders |- !r. Field r ==> !n. 0 < n ==> (forder_eq n = orders f* n)
   field_order_equal_disjoint  |- !m n. forder_eq m <> forder_eq n ==> DISJOINT (forder_eq m) (forder_eq n)
   field_order_equal_ne_disjoint  |- !r m n. m <> n ==> DISJOINT (forder_eq m) (forder_eq n)
   field_order_equal_element_nonzero
                               |- !r. Field r ==>
                                  !n. 0 < n ==> !x. x IN forder_eq n <=> x IN R+ /\ (forder x = n)

   Field Equal Order Structure:
   field_order_equal_contains  |- !r. Field r ==> !n. 0 < n ==> !x. x IN forder_eq n ==>
                                      IMAGE (\j. x ** j) (coprimes n) SUBSET forder_eq n
   field_order_equal_bigunion  |- !r. FiniteField r ==>
                                      (BIGUNION (IMAGE forder_eq (divisors (CARD R+))) = R+)
   field_order_equal_over_divisors_sigma_card
                               |- !r. FiniteField r ==>
                                  !n. SIGMA (CARD o forder_eq) (divisors (CARD R+)) = CARD R+

*)

(* ------------------------------------------------------------------------- *)
(* Finite Field Order                                                        *)
(* ------------------------------------------------------------------------- *)

(* Overload order of element in a field. *)
(* val _ = overload_on("forder", ``\x. order (r.prod excluding #0) x``); *)
val _ = overload_on("forder", ``\x. order f* x``);
val _ = overload_on("forder_", ``order ((r_:'b ring).prod excluding r_.sum.id)``);

(* Theorem: Field r ==> !x. order r.prod x = forder x *)
(* Proof:
      forder x
    = order f* x                                                        by notation
    = case OLEAST k. period f* x k of NONE => 0 | SOME k => k           by order_def
    = case OLEAST k. 0 < k /\ (f*.exp x k = f*.id) of NONE => 0 | SOME k => k  by period_def
    = case OLEAST k. 0 < k /\ (x ** k = #1) of NONE => 0 | SOME k => k  by field_nonzero_mult_property
    = case OLEAST k. period r.prod x k of NONE => 0 | SOME k => k       by period_def
    = order r.prod x                                                    by order_def
*)
val field_nonzero_order = store_thm(
  "field_nonzero_order",
  ``!r:'a field. Field r ==> !x. order r.prod x = forder x``,
  rw[order_def, period_def, field_nonzero_mult_property]);

(* Theorem: FiniteField r ==> !x. x IN R+ ==> 0 < forder x /\ (x ** forder x = #1) *)
(* Proof:
   From group_order_property:
> group_order_property |> ISPEC ``f*``;
val it = |- FiniteGroup f* ==> !x. x IN F* ==> 0 < forder x /\ (f*.exp x (forder x) = f*.id): thm
   Apply field_nonzero_mult_property.
*)
val field_order_property = store_thm(
  "field_order_property",
  ``!r:'a field. FiniteField r ==> !x. x IN R+ ==> 0 < forder x /\ (x ** forder x = #1)``,
  metis_tac[finite_field_is_field, finite_field_alt, group_order_property, field_nonzero_mult_property]);

(* Theorem: Field r ==> !x. x ** forder x = #1 *)
(* Proof:
   Since order_property |> ISPEC ``f*``;
     val it = |- !x. f*.exp x (forder x) = f*.id: thm
   Apply field_nonzero_mult_property.
*)
val field_order_eqn = store_thm(
  "field_order_eqn",
  ``!r:'a field. Field r ==> !x. x ** forder x = #1``,
  metis_tac[order_property, field_nonzero_mult_property]);

(* Theorem: Field r ==> !x n. 0 < n /\ n < forder x ==> x ** n <> #1 *)
(* Proof:
   Since order_minimal |> ISPEC ``f*``;
     val it = |- !x n. 0 < n /\ n < forder x ==> f*.exp x n <> f*.id: thm
   Apply field_nonzero_mult_property.
*)
val field_order_minimal = store_thm(
  "field_order_minimal",
  ``!r:'a field. Field r ==> !x n. 0 < n /\ n < forder x ==> x ** n <> #1``,
  metis_tac[order_minimal, field_nonzero_mult_property]);

(* Theorem: Field r ==> !n. 0 < n ==>
            !x. (forder x = n) <=> ((x ** n = #1) /\ !m. 0 < m /\ m < n ==> x ** m <> #1) *)
(* Proof: by order_thm, field_nonzero_mult_property *)
val field_order_thm = store_thm(
  "field_order_thm",
  ``!r:'a field. Field r ==> !n. 0 < n ==>
   !x. (forder x = n) <=> ((x ** n = #1) /\ !m. 0 < m /\ m < n ==> x ** m <> #1)``,
  rw[order_thm, field_nonzero_mult_property]);

(* Theorem: Field r ==> !x. x IN R+ ==>
            !m n. m < forder x /\ n < forder x ==> ((x ** m = x ** n) <=> (m = n)) *)
(* Proof:
   Note x IN R+ ==> x IN R /\ x <> #0           by field_nonzero_eq
   If part: (x ** m = x ** n) ==> (m = n)
      By contradiction, suppose m <> n.
      If m < n,
         then 0 < n - m /\ n - m < forder x     by arithmetic
          and x ** (n - m) = #1                 by field_exp_eq
         thus contradicting field_order_minimal.
      If n < m, the argument is symmetrical.
   Only-if part: (m = n) ==> (x ** m = x ** n)
      This is trivially true.
*)
val field_nonzero_exp_eq = store_thm(
  "field_nonzero_exp_eq",
  ``!r:'a field. Field r ==> !x. x IN R+ ==>
   !m n. m < forder x /\ n < forder x ==> ((x ** m = x ** n) <=> (m = n))``,
  rw[EQ_IMP_THM] >>
  `x IN R /\ x <> #0` by metis_tac[field_nonzero_eq] >>
  spose_not_then strip_assume_tac >>
  Cases_on `m < n` >| [
    `0 < n - m /\ n - m < forder x` by decide_tac >>
    metis_tac[field_exp_eq, field_order_minimal],
    `n < m /\ 0 < m - n /\ m - n < forder x` by decide_tac >>
    metis_tac[field_exp_eq, field_order_minimal]
  ]);

(* Theorem: Field r ==> (forder #0 = 0) *)
(* Proof:
       forder #0 = 0
   <=> !n. 0 < n ==> f*.exp #0 n <> f*.id     by order_eq_0
   <=> !n. 0 < n ==> #0 ** n <> #1            by field_nonzero_mult_property
   <=> true                                   by field_zero_exp
*)
val field_order_zero = store_thm(
  "field_order_zero",
  ``!r:'a field. Field r ==> (forder #0 = 0)``,
  rw[order_eq_0, field_nonzero_mult_property, field_zero_exp]);

(* Theorem: Field r ==> !x. (forder x = 0) <=> (!n. 0 < n ==> x ** n <> #1) *)
(* Proof:
   Note Group f*                   by field_nonzero_mult_is_group
    and f*.id = #1                 by group_excluding_property
   also !n. f*.exp x n = x ** n    by monoid_exp_def
   The result follows              by order_eq_0

order_eq_0 |> ISPEC ``(r:'a field).prod excluding #0``;
val it = |- !x. (forder x = 0) <=> !n. 0 < n ==> f*.exp x n <> f*.id: thm
*)
val field_order_0 = store_thm(
  "field_order_0",
  ``!r:'a field. Field r ==> !x. (forder x = 0) <=> (!n. 0 < n ==> x ** n <> #1)``,
  rpt strip_tac >>
  `Group f*` by rw[field_nonzero_mult_is_group] >>
  `f*.id = #1` by rw[group_excluding_property] >>
  `!n. f*.exp x n = x ** n` by rw[monoid_exp_def] >>
  rw[order_eq_0]);

(* Theorem: FiniteField r ==> !x. x IN R+ ==> (forder x <> 0) *)
(* Proof: by finite_field_is_finite_integral_domain, integral_domain_order_nonzero *)
val field_order_nonzero = store_thm(
  "field_order_nonzero",
  ``!r:'a field. FiniteField r ==> !x. x IN R+ ==> (forder x <> 0)``,
  rw_tac std_ss[finite_field_is_finite_integral_domain, integral_domain_order_nonzero]);

(* Theorem: FiniteField r ==> !x. x IN R ==> ((forder x = 0) <=> (x = #0)) *)
(* Proof:
   If part: forder x = 0 ==> x = #0
      By contradiction, assume x <> #0.
      Then x IN R+                                by field_nonzero_eq
        so 0 < forder x                           by field_order_property, FiniteField r
      This contradicts forder x = 0.
   Only-if part: x = #0 ==> forder x = 0, true    by field_order_zero
*)
val field_order_eq_0 = store_thm(
  "field_order_eq_0",
  ``!r:'a field. FiniteField r ==> !x. x IN R ==> ((forder x = 0) <=> (x = #0))``,
  rpt (stripDup[FiniteField_def]) >>
  rw[field_order_zero, EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  `x IN R+` by rw[field_nonzero_eq] >>
  `0 < forder x` by rw[field_order_property] >>
  decide_tac);

(* Theorem: Field r ==> (forder #1 = 1) *)
(* Proof:
   Since Field r
     ==> Group f* /\ F* = R+     by field_mult_group
     and #1 IN R+                by field_one_ne_zero, field_nonzero_eq
     and #1 = f*.id              by field_nonzero_mult_property
   Hence forder #1 = 1           by group_order_eq_1
*)
val field_order_one = store_thm(
  "field_order_one",
  ``!r:'a field. Field r ==> (forder #1 = 1)``,
  rw[field_mult_group, group_order_eq_1, field_nonzero_mult_property]);

(* Theorem: Field r ==> !x. x IN R ==> ((forder x = 1) <=> (x = #1)) *)
(* Proof:
   Since Field r
     ==> Group f* /\ F* = R+     by field_mult_group
     and #1 IN R+                by field_one_ne_zero, field_nonzero_eq
     and #1 = f*.id              by field_nonzero_mult_property
   If x = #0,
      Then forder #0 = 0 <> 1    by field_order_zero
       and #0 <> #1              by field_one_ne_zero
     Hence (forder #0 = 1) <=> (#0 = #1)
   If x <> #0,
      Then x IN R+                        by field_nonzero_eq
     Hence (forder x = 1) <=> (x = #1)    by group_order_eq_1
*)
val field_order_eq_1 = store_thm(
  "field_order_eq_1",
  ``!r:'a field. Field r ==> !x. x IN R ==> ((forder x = 1) <=> (x = #1))``,
  rpt strip_tac >>
  `Group f* /\ (F* = R+)` by rw[field_mult_group] >>
  `#1 IN R+` by rw[] >>
  `#1 = f*.id` by rw[field_nonzero_mult_property] >>
  Cases_on `x = #0` >-
  rw[field_order_zero, EQ_IMP_THM] >>
  rw[group_order_eq_1, field_nonzero_eq]);

(* Theorem: FiniteField r ==> (forder (-#1) = if char r = 2 then 1 else 2) *)
(* Proof:
   If char r = 2,
      Then -#1 = #1           by ring_neg_one_eq_one
       and forder #1 = 1      by field_order_one
   If char r <> 2,
      Then -#1 <> #1          by field_neg_one_eq_one
     Since -#1 <> #0
       ==> -#1 IN R+          by ring_nonzero_eq
       But (-#1) ** 1 = -#1   by field_exp_1
                      <> #1   by above
       and (-#1) ** 2
         = (-#1) * (-#1)      by field_exp_small
         = #1 * #1            by field_mult_neg_neg
         = #1                 by field_mult_one_one
     Hence forder #1 = 2      by field_order_thm
*)
val field_order_neg_one = store_thm(
  "field_order_neg_one",
  ``!r:'a field. Field r ==> (forder (-#1) = if char r = 2 then 1 else 2)``,
  rpt strip_tac >>
  `Ring r /\ #1 <> #0` by rw[] >>
  rw[] >-
  metis_tac[ring_neg_one_eq_one, field_order_one] >>
  `-#1 <> #1` by rw[ring_neg_one_eq_one] >>
  `-#1 IN R /\ -#1 IN R+` by rw[] >>
  `(-#1) ** 1 <> #1` by rw[] >>
  `(-#1) ** 2 = #1` by rw[field_exp_small] >>
  rw[field_order_thm, DECIDE``!m. 0 < m /\ m < 2 ==> (m = 1)``]);

(* Theorem: Field r ==> !x. x IN R /\ 0 < order r.prod x ==> !n. x ** n = x ** (n MOD (order r.prod x) *)
(* Proof:
   Note x <> #0                  by field_order_zero
     so x IN R+                  by field_nonzero_eq
   Since Field r
     ==> Group f* /\ (F* = R+)   by field_mult_group
   Hence result follows          by group_exp_mod_order, field_nonzero_mult_property
*)
val field_exp_mod_order = store_thm(
  "field_exp_mod_order",
  ``!r:'a field. Field r ==> !x. x IN R /\ 0 < forder x ==> !n. x ** n = x ** (n MOD (forder x))``,
  rpt strip_tac >>
  `forder x <> 0` by decide_tac >>
  `x IN R+` by metis_tac[field_order_zero, field_nonzero_eq] >>
  `Group f* /\ (F* = R+)` by rw[field_mult_group] >>
  metis_tac[group_exp_mod_order, field_nonzero_mult_property]);

(* Theorem: FiniteField r ==> !x. x IN R+ ==> !n. x ** n = x ** (n MOD (forder x)) *)
(* Proof:
    Note x IN R+ ==> x IN R    by field_nonzero_element
     and 0 < forder x          by field_order_property
   Hence result follows        by field_exp_mod_order
*)
val finite_field_exp_mod_order = store_thm(
  "finite_field_exp_mod_order",
  ``!r:'a field. FiniteField r ==> !x. x IN R+ ==> !n. x ** n = x ** (n MOD (forder x))``,
  rw[finite_field_is_field, field_nonzero_element, field_order_property, GSYM field_exp_mod_order]);

(* Theorem: FiniteField r ==> !x. x IN R+ ==> (forder x) divides (CARD R+)  *)
(* Proof:
   FiniteField r ==> Field r /\ FINITE R     by FiniteField_def
   Field r ==> Group f*                      by field_mult_group
   Hence FiniteGroup f*                      by FiniteGroup_def
     and (forder x) divides (CARD R+)        by group_order_divides
*)
val field_order_divides = store_thm(
  "field_order_divides",
  ``!r:'a field. FiniteField r ==> !x. x IN R+ ==> (forder x) divides (CARD R+)``,
  rpt strip_tac >>
  `Field r /\ FINITE R` by metis_tac[FiniteField_def] >>
  `Group f*` by rw[field_mult_group] >>
  `FINITE R+` by metis_tac[field_nonzero_eq, SUBSET_DEF, SUBSET_FINITE] >>
  `F* = R+` by rw[field_mult_carrier] >>
  `FiniteGroup f*` by metis_tac[FiniteGroup_def] >>
  metis_tac[group_order_divides]);

(* Theorem: FiniteField r ==> !x. x IN R ==> forder x < CARD R *)
(* Proof:
   If x = #0,
      Then forder #0 = 0                 by field_order_zero
       and 0 < CARD R                    by finite_field_card_pos
   If x <> #0,
      Then x IN R+                       by field_nonzero_eq
       ==> (forder x) divides (CARD R+)  by field_order_divides
     Since 0 < (CARD R+)                 by field_nonzero_card_pos
        or (forder x) <= (CARD R+)       by DIVIDES_LE, 0 < (CARD R+)
       But CARD R = SUC (CARD R+)        by finite_field_carrier_card
     Hence (forder x) < CARD R           by LESS_EQ_IMP_LESS_SUC
*)
val field_order_upper = store_thm(
  "field_order_upper",
  ``!r:'a field. FiniteField r ==> !x. x IN R ==> forder x < CARD R``,
  rpt (stripDup[FiniteField_def]) >>
  Cases_on `x = #0` >-
  rw[field_order_zero, finite_field_card_pos] >>
  `x IN R+` by rw[field_nonzero_eq] >>
  `(forder x) divides (CARD R+)` by rw[field_order_divides] >>
  `0 < (CARD R+)` by rw[field_nonzero_card_pos] >>
  `CARD R = SUC (CARD R+)` by rw[finite_field_carrier_card] >>
  `(forder x) <= (CARD R+)` by rw[DIVIDES_LE] >>
  decide_tac);

(* Theorem: Field r ==> !x. x IN R+ ==> !n. (x ** n = #1) <=> (forder x) divides n *)
(* Proof:
   Since Field r ==> Group f*      by field_mult_group
   Apply > group_order_divides_exp |> ISPEC ``f*``;
   val it = |- Group f* ==> !x. x IN F* ==> !n. (f*.exp x n = f*.id) <=> forder x divides n: thm
   and simplify by field_nonzero_mult_property.
*)
val field_order_divides_exp = store_thm(
  "field_order_divides_exp",
  ``!r:'a field. Field r ==> !x. x IN R+ ==> !n. (x ** n = #1) <=> (forder x) divides n``,
  rpt strip_tac >>
  `Group f*` by rw[field_mult_group] >>
  rw[GSYM group_order_divides_exp, field_nonzero_mult_property]);

(*
In a FiniteField, can (forder x) divides the prime (char r) ?
i.e. can (forder x = char r) ?    Note (forder x) divides (CARD R+)  by field_order_divides
Say char r = 2.
In GF_2, CARD R+ = 1, only (forder = 1).
In GF_4, CARD R+ = 3, only (forder = 1, 3).
In GF_8, CARD R+ = 7, only (forder = 1, 7).

Say char r = 3.
In GF_3, CARD R+ = 2, only (forder = 1, 2).
In GF_9, CARD R+ = 8, only (forder = 1, 2, 4, 8).

Let forder x = z, c = char r, prime c.
(forder x) divides (CARD R+)
==> c ** d - 1 = q z
or  c ** d - q z = 1
If z divides c, z divides c ** d.
so z divides 1, or z = 1, or x = #1.
*)

(* Theorem: FiniteField r ==> !x. x IN R+ ==> coprime (forder x) (CARD R) *)
(* Proof:
   Let ox = forder x.
   Since ox divides (CARD R+)           by field_order_divides, x IN R+
     ==> coprime ox (SUC (CARD R+))     by divides_imp_coprime_with_successor
      or coprime ox (CARD R)            by finite_field_carrier_card
*)
val field_order_coprime_card = store_thm(
  "field_order_coprime_card",
  ``!r:'a field. FiniteField r ==> !x. x IN R+ ==> coprime (forder x) (CARD R)``,
  rw[field_order_divides, divides_imp_coprime_with_successor, finite_field_carrier_card]);

(* Theorem: Field r ==> !x. x IN R ==> !n. forder (x ** n) * (gcd n (forder x)) = forder x *)
(* Proof:
   If x = #0,
      then forder #0 = 0          by field_order_zero
      If n = 0,
         then gcd 0 0 = 0         by GCD_0L
         so   LHS = 0 = RHS.
      If n <> 0,
         then #0 ** n = #0        by field_zero_exp
         and  LHS = 0 = RHS.
   If x <> #0,
      then x IN F*                by field_nonzero_alt
       and Group f*               by field_mult_group
   Note: group_order_power |> ISPEC ``f*``;
   val it = |- Group f* ==> !x. x IN F* ==> !k. forder (f*.exp x k) * gcd (forder x) k = forder x: thm
   Apply field_nonzero_mult_property and GCD_SYM.
*)
val field_order_power = store_thm(
  "field_order_power",
  ``!r:'a field. Field r ==> !x. x IN R ==> !n. forder (x ** n) * (gcd n (forder x)) = forder x``,
  rpt strip_tac >>
  Cases_on `x = #0` >| [
    `forder #0 = 0` by rw[field_order_zero] >>
    Cases_on `n = 0` >-
    rw[] >>
    rw[field_zero_exp],
    `x IN F*` by rw[field_nonzero_alt] >>
    `Group f*` by rw[field_mult_group] >>
    metis_tac[group_order_power, field_nonzero_mult_property, GCD_SYM]
  ]);

(* Theorem: Field r ==> !x. x IN R ==>
            !n. 0 < n ==> (forder (x ** n) = (forder x) DIV (gcd n (forder x))) *)
(* Proof:
   Note forder (x ** n) * gcd n (forder x) = forder x         by field_order_power
    and gcd n (forder x) <> 0                                 by GCD_EQ_0, 0 < n
    ==> forder (x ** n) = (forder x) DIV (gcd n (forder x))   by DIV_SOLVE
*)
val field_order_power_eqn = store_thm(
  "field_order_power_eqn",
  ``!r:'a field. Field r ==> !x. x IN R ==>
   !n. 0 < n ==> (forder (x ** n) = (forder x) DIV (gcd n (forder x)))``,
  rpt strip_tac >>
  `forder (x ** n) * gcd n (forder x) = forder x` by rw[field_order_power] >>
  `gcd n (forder x) <> 0` by rw[GCD_EQ_0] >>
  rw[DIV_SOLVE]);

(* Theorem: Field r ==> !x. x IN R ==> !n. coprime n (forder x) ==> (forder (x ** n) = forder x) *)
(* Proof:
     forder x
   = forder (x ** n) * gcd n (forder x)  by field_order_power
   = forder (x ** n) * 1                 by given
   = forder (x ** n)                     by MULT_RIGHT_1
*)
val field_order_power_coprime = store_thm(
  "field_order_power_coprime",
  ``!r:'a field. Field r ==> !x. x IN R ==> !n. coprime n (forder x) ==> (forder (x ** n) = forder x)``,
  metis_tac[field_order_power, MULT_RIGHT_1]);

(* Theorem: FiniteField r ==> !x. x IN R /\ x <> #0 ==>
            !n. (forder (x ** n) = forder x) <=> coprime n (forder x) *)
(* Proof:
   If part: forder (x ** n) = forder x ==> coprime n (forder x)
      Since forder x <> 0                          by field_order_eq_0
        and forder x * (gcd n (forder x))
          = forder (x ** n) * (gcd n (forder x))   by given
          = forder x                               by field_order_power
          = forder x * 1                           by MULT_RIGHT_1
      Hence gcd n (forder x) = 1,
         or coprime n (forder x)                   by EQ_MULT_LCANCEL
   Only-if part: coprime n (forder x) ==> forder (x ** n) = forder x
      Since coprime n (forder x) means
            gcd n (forder x) = 1                   by notation
       and forder (x ** n) * (gcd n (forder x)) = forder x  by field_order_power
        so forder (x ** n) = forder x              by MULT_RIGHT_1
*)
val field_order_power_eq_order = store_thm(
  "field_order_power_eq_order",
  ``!r:'a field. FiniteField r ==> !x. x IN R /\ x <> #0 ==>
   !n. (forder (x ** n) = forder x) <=> coprime n (forder x)``,
  rpt (stripDup[FiniteField_def]) >>
  `forder (x ** n) * (gcd n (forder x)) = forder x` by rw[field_order_power] >>
  rw[EQ_IMP_THM] >-
  metis_tac[field_order_eq_0, EQ_MULT_LCANCEL, MULT_RIGHT_1] >>
  metis_tac[MULT_RIGHT_1]);

(* Theorem: Field r ==>
            !n x. x IN R+ /\ 0 < forder x /\ n divides (forder x) ==> (forder (x ** (forder x DIV n)) = n) *)
(* Proof:
   Note Group f*                              by field_mult_group
    and F* = R+                               by field_mult_carrier
   Also !n. *.exp x n = x ** n                by group_excluding_exp
     so forder (x ** (forder x DIV n)) = n    by group_order_exp_cofactor

group_order_exp_cofactor |> ISPEC ``f*``;
val it = |- !x n. Group f* /\ x IN F* /\ 0 < forder x /\ n divides forder x ==>
                  (forder (f*.exp x (forder x DIV n)) = n): thm
*)
val field_order_exp_cofactor = store_thm(
  "field_order_exp_cofactor",
  ``!r:'a field. Field r ==>
   !n x. x IN R+ /\ 0 < forder x /\ n divides (forder x) ==> (forder (x ** (forder x DIV n)) = n)``,
  rpt strip_tac >>
  `Group f*` by rw[field_mult_group] >>
  `F* = R+` by rw[field_mult_carrier] >>
  metis_tac[group_order_exp_cofactor, group_excluding_exp]);

(* ------------------------------------------------------------------------- *)
(* Field Orders Property                                                     *)
(* ------------------------------------------------------------------------- *)

(* Definition for field orders *)
val field_orders_def =
    save_thm("field_orders_def", orders_def |> ISPEC ``f*`` |> GEN_ALL);
(* val field_orders_def = |- !r n. orders f* n = {x | x IN F* /\ (forder x = n)}: thm *)

(* Theorem: x IN orders f* n <=> x IN F* /\ (forder x = n) *)
(* Proof: by field_orders_def *)
val field_orders_member = store_thm(
  "field_orders_member",
  ``!(r:'a field) x n. x IN orders f* n <=> x IN F* /\ (forder x = n)``,
  rw[field_orders_def]);

(* Theorem: x IN orders f* (CARD F* ) <=> x IN F* /\ (forder x = CARD F* ) *)
(* Proof: by field_orders_member *)
val field_orders_primitive = store_thm(
  "field_orders_primitive",
  ``!(r:'a field) x. x IN orders f* (CARD F* ) <=> x IN F* /\ (forder x = CARD F* )``,
  rw[field_orders_member]);

(* Theorem: Field r ==> (orders f* n) SUBSET R+ *)
(* Proof: by field_orders_def, field_mult_carrier *)
val field_orders_alt = store_thm(
  "field_orders_alt",
  ``!r:'a field. Field r ==> !n. orders f* n = {x | x IN R+ /\ (forder x = n)}``,
  rw[field_orders_def, field_mult_carrier]);

(* Theorem: Field r ==> (orders f* n) SUBSET R+ *)
(* Proof:
   Since (orders f* n) SUBSET F*  by orders_subset
     and F* = R+                  by field_mult_carrier
      so (orders f* n) SUBSET R+
*)
val field_orders_subset = store_thm(
  "field_orders_subset",
  ``!r:'a field. Field r ==> !n. (orders f* n) SUBSET R+``,
  metis_tac[orders_subset, field_mult_carrier]);

(* Theorem: Field r ==> (orders f* n) SUBSET R *)
(* Proof:
   Since (orders f* n) SUBSET R+  by field_orders_subset
     and R+ SUBSET R              by field_nonzero_subset
     ==> (orders f* n) SUBSET R   by SUBSET_TRANS
*)
val field_orders_subset_carrier = store_thm(
  "field_orders_subset_carrier",
  ``!r:'a field. Field r ==> !n. (orders f* n) SUBSET R``,
  metis_tac[field_orders_subset, field_nonzero_subset, SUBSET_TRANS]);

(* Theorem: Field r ==> !x n. x IN (orders f* n) ==> x IN R+ *)
(* Proof: by field_orders_subset, SUBSET_DEF *)
val field_orders_nonzero_element = store_thm(
  "field_orders_nonzero_element",
  ``!r:'a field. Field r ==> !x n. x IN (orders f* n) ==> x IN R+``,
  metis_tac[field_orders_subset, SUBSET_DEF]);

(* Theorem: Field r ==> !x n. x IN (orders f* n) ==> x <> #0 *)
(* Proof: field_orders_nonzero_element, field_nonzero_eq *)
val field_orders_element_nonzero = store_thm(
  "field_orders_element_nonzero",
  ``!r:'a field. Field r ==> !x n. x IN (orders f* n) ==> x <> #0``,
  metis_tac[field_orders_nonzero_element, field_nonzero_eq]);

(* Theorem: Field r ==> !x n. x IN (orders f* n) ==> x IN R *)
(* Proof: field_orders_subset_carrier, SUBSET_DEF *)
val field_orders_element = store_thm(
  "field_orders_element",
  ``!r:'a field. Field r ==> !x n. x IN (orders f* n) ==> x IN R``,
  metis_tac[field_orders_subset_carrier, SUBSET_DEF]);

(* Theorem: Field r ==> !x n. x IN orders f* n <=> (x IN R+ /\ (forder x = n)) *)
(* Proof:
   Note Group f* /\ (F* = R+)    by field_mult_group
   The result follows            by orders_element, Group f*
*)
val field_orders_element_property = store_thm(
  "field_orders_element_property",
  ``!r:'a field. Field r ==> !x n. x IN orders f* n <=> (x IN R+ /\ (forder x = n))``,
  rw[field_mult_group, orders_element]);

(* Theorem: Field r ==> !x n. x IN orders f* n ==> (forder x = n) *)
(* Proof: by field_orders_element_property *)
val field_orders_element_order = store_thm(
  "field_orders_element_order",
  ``!r:'a field. Field r ==> !x n. x IN orders f* n ==> (forder x = n)``,
  rw[field_orders_element_property]);

(* Theorem: Field r ==> !x. x IN R+ ==> x IN orders f* (forder x) *)
(* Proof: by field_orders_element_property *)
val field_orders_element_self = store_thm(
  "field_orders_element_self",
  ``!r:'a field. Field r ==> !x. x IN R+ ==> x IN orders f* (forder x)``,
  metis_tac[field_orders_element_property]);

(* Theorem: FiniteField r ==> !n. FINITE (orders f* n) *)
(* Proof:
   Note (orders f* n) SUBSET R   by field_orders_subset_carrier
    ==> FINITE (orders f* n)     by SUBSET_FINITE
*)
val field_orders_finite = store_thm(
  "field_orders_finite",
  ``!r:'a field. FiniteField r ==> !n. FINITE (orders f* n)``,
  metis_tac[FiniteField_def, field_orders_subset_carrier, SUBSET_FINITE]);

(* Theorem: FiniteField r ==> (orders f* 0 = {}) *)
(* Proof:
   By contradiction, suppose orders f* 0 <> {}.
   Then ?x. x IN R /\ x IN (orders f* 0)   by field_orders_element, MEMBER_NOT_EMPTY
    and forder x = 0                       by field_orders_element_order
    but x <> #0                            by field_orders_element_nonzero
    ==> forder x <> 0, a contradiction     by field_order_eq_0
*)
val field_orders_0 = store_thm(
  "field_orders_0",
  ``!r:'a field. FiniteField r ==> (orders f* 0 = {})``,
  rpt (stripDup[FiniteField_def]) >>
  spose_not_then strip_assume_tac >>
  `?x. x IN R /\ x IN (orders f* 0)` by metis_tac[field_orders_element, MEMBER_NOT_EMPTY] >>
  `forder x = 0` by rw[field_orders_element_order] >>
  `x <> #0` by metis_tac[field_orders_element_nonzero] >>
  metis_tac[field_order_eq_0]);

(* Theorem: Field r ==> (orders f* 1 = {#1}) *)
(* Proof:
   Since #1 IN R+               by field_one_nonzero
     and forder #1 = 1          by field_order_one
   Hence #1 IN {orders f* 1}    by field_orders_element_property
      or (orders f* 1) <> {}    by MEMBER_NOT_EMPTY

       x IN (orders f* 1)
   ==> forder x = 1             by field_orders_element_order
   ==> x = #1                   by field_order_eq_1
   Thus (orders f* 1) = {#1}    by ONE_ELEMENT_SING, (orders f* 1) <> {}

   Or, by EXTENSION, this is to show:
       x IN orders f* 1 <=> (x = #1)
       x IN orders f* 1
   <=> x IN R+ /\ (forder x = 1)   by field_orders_element_property
   <=> x = #1                      by field_order_eq_1, field_one_nonzero, field_nonzero_eq
*)
val field_orders_1 = store_thm(
  "field_orders_1",
  ``!r:'a field. Field r ==> (orders f* 1 = {#1})``,
  rw[EXTENSION] >>
  metis_tac[field_orders_element_property, field_order_eq_1, field_one_nonzero, field_nonzero_eq]);

(* Theorem: Field r ==> !m n. m <> n ==> DISJOINT (orders f* m) (orders f* n) *)
(* Proof:
   By contradiction, suppose ~(DISJOINT (orders f* m) (orders f* n)).
   Then !x. x IN (orders f* m) /\ x IN (orders f* n)   by IN_DISJOINT
    ==> m = forder x = n                               by field_orders_element_order
   This contradicts m <> n.
*)
val field_orders_disjoint = store_thm(
  "field_orders_disjoint",
  ``!r:'a field. Field r ==> !m n. m <> n ==> DISJOINT (orders f* m) (orders f* n)``,
  metis_tac[IN_DISJOINT, field_orders_element_order]);

(* ------------------------------------------------------------------------- *)
(* Equality of Order                                                         *)
(* ------------------------------------------------------------------------- *)

(* Define the set of elements with specified order *)
val field_order_equal_def = Define `
   field_order_equal (r:'a ring) (n: num) = {x | x IN R /\ (forder x = n)}
`;
(* This is more general then orders f* n:
field_orders_def  |- !r n. orders f* n = {x | x IN F* /\ (forder x = n)}
*)

(* overload on field_order_equal *)
val _ = overload_on("forder_eq", ``field_order_equal (r:'a ring)``);
(*
> field_order_equal_def;
val it = |- !r n. forder_eq n = {x | x IN R /\ (forder x = n)}: thm
*)

(* Theorem: x IN forder_eq n <=> x IN R /\ (forder x = n) *)
(* Proof: by field_order_equal_def *)
val field_order_equal_element = store_thm(
  "field_order_equal_element",
  ``!(r:'a ring) x n. x IN forder_eq n <=> x IN R /\ (forder x = n)``,
  rw[field_order_equal_def]);

(* Theorem: (forder_eq n) SUBSET R *)
(* Proof: by field_order_equal_def, SUBSET_DEF *)
val field_order_equal_subset = store_thm(
  "field_order_equal_subset",
  ``!(r:'a field) n. (forder_eq n) SUBSET R``,
  rw[field_order_equal_def, SUBSET_DEF]);

(* Theorem: FINITE R ==> !n. FINITE (forder_eq n) *)
(* Proof: by field_order_equal_subset, SUBSET_FINITE *)
val field_order_equal_finite = store_thm(
  "field_order_equal_finite",
  ``!r:'a ring. FINITE R ==> !n. FINITE (forder_eq n)``,
  metis_tac[field_order_equal_subset, SUBSET_FINITE]);

(* Theorem: FiniteField r ==> (forder_eq 0 = {#0}) *)
(* Proof:
   By field_order_equal_def, this is to show:
      x IN R /\ (forder x = 0) <=> (x = #0)
   This is true by field_order_eq_0, and field_zero_element.
*)
val field_order_equal_of_0 = store_thm(
  "field_order_equal_of_0",
  ``!r:'a field. FiniteField r ==> (forder_eq 0 = {#0})``,
  rpt (stripDup[FiniteField_def]) >>
  rw[field_order_equal_def, EXTENSION] >>
  metis_tac[field_order_eq_0, field_zero_element]);

(* Theorem: Field r ==> (forder_eq 1 = {#1}) *)
(* Proof:
   By field_order_equal_def, this is to show:
      x IN R /\ (forder x = 1) <=> (x = #1)
   This is true by field_order_eq_1
*)
val field_order_equal_of_1 = store_thm(
  "field_order_equal_of_1",
  ``!r:'a field. Field r ==> (forder_eq 1 = {#1})``,
  rw[field_order_equal_def, EXTENSION] >>
  metis_tac[field_order_eq_1, field_one_element]);

(* Theorem: Field r ==> !n. #0 IN forder_eq n <=> (n = 0) *)
(* Proof:
       #0 IN forder_eq n
   <=> #0 IN R /\ (forder #0 = n)      by field_order_equal_element
   <=> T /\ (forder #0 = n)            by field_zero_element
   <=> 0 = n                           by field_order_zero
*)
val field_order_equal_has_zero = store_thm(
  "field_order_equal_has_zero",
  ``!r:'a field. Field r ==> !n. #0 IN forder_eq n <=> (n = 0)``,
  metis_tac[field_order_equal_element, field_zero_element, field_order_zero]);

(* Theorem: Field r ==> !n. 0 < n ==> (forder_eq n = orders f* n) *)
(* Proof:
   If part: x IN R /\ 0 < forder x ==> x IN F*
      Since forder #0 = 0                   by field_order_zero
        but 0 < forder x, so x <> #0,
       then x IN R /\ x <> #0 ==> x IN R+   by field_nonzero_eq
                              ==> x IN F*   by field_mult_carrier
   Only-if part: x IN F* ==> x IN R,
      True by field_mult_carrier, field_nonzero_element.
*)
val field_order_equal_eq_orders = store_thm(
  "field_order_equal_eq_orders",
  ``!r:'a field. Field r ==> !n. 0 < n ==> (forder_eq n = orders f* n)``,
  rw[field_order_equal_def, orders_def, EXTENSION, EQ_IMP_THM] >| [
    `x <> #0` by metis_tac[field_order_zero, NOT_ZERO_LT_ZERO] >>
    metis_tac[field_nonzero_eq, field_mult_carrier],
    metis_tac[field_mult_carrier, field_nonzero_element]
  ]);

(* Theorem: (forder_eq m) <> (forder_eq n) ==> DISJOINT (forder_eq m) (forder_eq n) *)
(* Proof:
   Let s = forder_eq m, t = forder_eq n.
   If s = {} or t = {}, then true                       by DISJOINT_EMPTY
   If s <> {} and t <> {},
      By DISJOINT_DEF, this is to show:
         x NOTIN s \/ x NOTIN t
      By contradiction, assumt x IN s /\ x IN t.
      Then x IN R /\ (forder x = m) /\ (forder x = n)   by field_order_equal_element
       ==> m = n, or s = t, which contradicts s <> t.
*)
val field_order_equal_disjoint = store_thm(
  "field_order_equal_disjoint",
  ``!m n. (forder_eq m) <> (forder_eq n) ==> DISJOINT (forder_eq m) (forder_eq n)``,
  rpt strip_tac >>
  qabbrev_tac `s = forder_eq m` >>
  qabbrev_tac `t = forder_eq n` >>
  Cases_on `(s = {}) \/ (t = {})` >-
  metis_tac[DISJOINT_EMPTY] >>
  rw[DISJOINT_DEF, EXTENSION] >>
  metis_tac[field_order_equal_element]);

(*
Note: This is better than:
field_order_equal_eq_orders, field_orders_disjoint, both using Field r.
But the next is even better.
*)

(* Theorem: m <> n ==> DISJOINT (forder_eq m) (forder_eq n) *)
(* Proof:
   By DISJOINT_DEF, this is to show: forder_eq m INTER forder_eq n = {}.
   By contradiction, suppose forder_eq m INTER forder_eq n <> {}.
   Then ?z. z IN forder_eq m /\ z IN forder_eq n    by MEMBER_NOT_EMPTY, IN_INTER
    ==> z IN R /\ (forder z = m) /\ (forder z = n)  by field_order_equal_element
    ==> m = n, this contradicts m <> n.
*)
val field_order_equal_ne_disjoint = store_thm(
  "field_order_equal_ne_disjoint",
  ``!r:'a field. !m n. m <> n ==> DISJOINT (forder_eq m) (forder_eq n)``,
  metis_tac[DISJOINT_DEF, field_order_equal_element, MEMBER_NOT_EMPTY, IN_INTER]);

(* Theorem: Field r ==> !n. 0 < n ==> !x. x IN forder_eq n <=> x IN R+ /\ (forder x = n) *)
(* Proof:
       x IN forder_eq n
   <=> x IN orders f* n     by field_order_equal_eq_orders, 0 < n
   <=> x IN R+ /\ (forder x = n)   by field_orders_element_property
*)
val field_order_equal_element_nonzero = store_thm(
  "field_order_equal_element_nonzero",
  ``!r:'a field. Field r ==> !n. 0 < n ==> !x. x IN forder_eq n <=> x IN R+ /\ (forder x = n)``,
  rw[field_order_equal_eq_orders, field_orders_element_property]);

(* ------------------------------------------------------------------------- *)
(* Field Equal Order Structure                                               *)
(* ------------------------------------------------------------------------- *)

(*
Originally, the structure of (forder_eq n) is investigated in ffUnity,
because if forder x = n, then x ** n = #1, thus x is a root of (unity n).
In ffUnity, we show that roots of (unity n) has a generator.
Effectively we show that roots of (unity n) is cyclic, and work from there.

Here is a rework of the structure of (forder_eq n), by elementary means.
The aim is to retrace Gauss' proof of cyclic f* for FiniteField r.
ffAdvancedTheory.finite_field_mult_group_cyclic |- !r. FiniteField r ==> cyclic f*
Gauss' proof is by an ingenious counting argument, based on Gauss_little_thm.
*)

(* Theorem: Field r ==> !n. 0 < n ==>
            !x. x IN (forder_eq n) ==> IMAGE (\j. x ** j) (coprimes n) SUBSET (forder_eq n) *)
(* Proof:
   Note x IN R /\ (forder x = n)            by field_order_equal_element
   By SUBSET, this is to show:
      !z. z IN IMAGE (\j. x ** j) (coprimes n) ==> z IN (forder_eq n)
    Let z = x ** j IN IMAGE (\j. x ** j) (coprimes n)      by IN_IMAGE
   Then j IN coprimes n ==> coprime j n     by coprimes_element
   Note x ** j IN R                         by field_exp_element
        forder (x ** j)
      = forder x                            by field_order_power_coprime
      = n                                   by above
   Thus z IN (forder_eq n)                  by field_order_equal_element
*)
val field_order_equal_contains = store_thm(
  "field_order_equal_contains",
  ``!r:'a field. Field r ==> !n. 0 < n ==>
   !x. x IN (forder_eq n) ==> IMAGE (\j. x ** j) (coprimes n) SUBSET (forder_eq n)``,
  rw[field_order_equal_element, SUBSET_DEF] >-
  rw[] >>
  metis_tac[field_order_power_coprime, coprimes_element]);

(*
Note: IMAGE (\j. x ** j) (coprimes n) = {x ** j | j | j IN coprimes n}
Note: This is the best that can be proved here.
For the stronger result:
!r:'a field. FiniteField r ==> !n. 0 < n ==>
   !x. x IN (forder_eq n) ==> (forder_eq n = IMAGE (\j. x ** j) (coprimes n))

We really need ffUnity, for the following:
(1) If (forder x = n),
    then every element y of order n is somewhere in the set s = {1, x, x ** 2, ...., x ** (n-1)}
    although not all n of them have order n.
    This is because:
    (a) any z IN R with (forder z = n) has z ** n = #1, hence a root of (unity n = X ** n - |1|).
    (b) all z IN s are roots of (unity n = X ** n - |1|).
        and there are no more roots:
        poly_roots_count |- !r. Field r ==> !p. poly p /\ p <> |0| ==> CARD (roots p) <= deg p
(2) Since every possible element y of order n is somewhere in the set s,
    and only index j with coprime j n can have order n by field_order_power_coprime,
    there are exactly (phi n) elements of order n, if there is at least one.
*)

(* Theorem: FiniteField r ==> (BIGUNION (IMAGE forder_eq (divisors (CARD R+))) = R+) *)
(* Proof:
   Let m = CARD R+.
   Then 0 < m                    by field_nonzero_card_pos
   By EXTENSION, IN_BIGUNION, divisors_element_alt, this is to show:
   (1) x IN s ==> x IN R+   where s = forder_eq n for some n divides m
       Note x IN s ==> x IN R /\ forder x divides m    by field_order_equal_element
       But x <> #0, for otherwise
           x = #0 ==> forder x = 0                     by field_order_eq_0
           forder x divides m ==> m = 0                by ZERO_DIVIDES
           This contradicts 0 < m.
       Thus x IN R+                                    by field_nonzero_eq
   (2) x IN R+ ==> ?s. x IN s /\ ?n. (s = forder_eq n) /\ n <= m /\ n divides m
       Note x IN R+ ==> (forder x) divides m           by field_order_divides
       Put n = forder x, and s = forder_eq n.
       Note x IN R               by field_nonzero_eq
       Then x IN s               by field_order_equal_element
        and n <= m               by DIVIDES_LE
*)
val field_order_equal_bigunion = store_thm(
  "field_order_equal_bigunion",
  ``!r:'a field. FiniteField r ==> (BIGUNION (IMAGE forder_eq (divisors (CARD R+))) = R+)``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = CARD R+` >>
  `0 < m` by rw[field_nonzero_card_pos, Abbr`m`] >>
  rw[EXTENSION, IN_BIGUNION, divisors_element_alt, EQ_IMP_THM] >| [
    `x IN R /\ (forder x) divides m` by metis_tac[field_order_equal_element] >>
    `x <> #0` by metis_tac[field_order_eq_0, ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
    metis_tac[field_nonzero_eq],
    `(forder x) divides m` by rw[field_order_divides, Abbr`m`] >>
    metis_tac[field_order_equal_element, DIVIDES_LE, field_nonzero_eq]
  ]);

(* Theorem: FiniteField r ==> !n. SIGMA (CARD o forder_eq) (divisors (CARD R+)) = CARD R+ *)
(* Proof:
   Let m = CARD R+, s = divisors m, t = IMAGE forder_eq s
   Then FINITE s                  by divisors_finite
    ==> FINITE t                  by IMAGE_FINITE
    and EVERY_FINITE t            by field_order_equal_finite, IN_IMAGE
   also PAIR_DISJOINT t           by field_order_equal_disjoint, IN_IMAGE

   Claim: !x y. x IN s /\ y IN s /\ (forder_eq x = forder_eq y) ==>
                (x = y) \/ (CARD (forder_eq x) = 0)
   Proof: By contradiction, suppose x <> y /\ CARD (forder_eq x) <> 0.
          Note FINITE (forder_eq x)      by field_order_equal_finite
          Thus forder_eq x <> {}         by CARD_EQ_0
           ==> ?z. z IN forder_eq x      by MEMBER_NOT_EMPTY
           and z IN forder_eq y          by forder_eq x = forder_eq y
           ==> x = forder z = y          by field_order_equal_element
          This contradicts x <> y.

      SIGMA (CARD o forder_eq) s
    = SIGMA CARD (IMAGE forder_eq s)     by sum_image_by_composition_without_inj, Claim
    = SIGMA CARD t                       by notation
    = CARD (BIGUNION t)                  by disjoint_bigunion_card
    = m                                  by field_order_equal_bigunion
*)
val field_order_equal_over_divisors_sigma_card = store_thm(
  "field_order_equal_over_divisors_sigma_card",
  ``!r:'a field. FiniteField r ==> !n. SIGMA (CARD o forder_eq) (divisors (CARD R+)) = CARD R+``,
  rpt (stripDup[FiniteField_def]) >>
  qabbrev_tac `m = CARD R+` >>
  qabbrev_tac `s = divisors m` >>
  qabbrev_tac `t = IMAGE forder_eq s` >>
  `FINITE s` by rw[divisors_finite, Abbr`s`] >>
  `FINITE t` by rw[Abbr`t`] >>
  `EVERY_FINITE t` by metis_tac[field_order_equal_finite, IN_IMAGE] >>
  `PAIR_DISJOINT t` by metis_tac[field_order_equal_disjoint, IN_IMAGE] >>
  `!x y. x IN s /\ y IN s /\ (forder_eq x = forder_eq y) ==> (x = y) \/ (CARD (forder_eq x) = 0)` by
  (spose_not_then strip_assume_tac >>
  `FINITE (forder_eq x)` by rw[field_order_equal_finite] >>
  `forder_eq x <> {}` by rw[GSYM CARD_EQ_0] >>
  `?z. z IN forder_eq x` by metis_tac[MEMBER_NOT_EMPTY] >>
  metis_tac[field_order_equal_element]) >>
  `SIGMA (CARD o forder_eq) s = SIGMA CARD t` by rw[sum_image_by_composition_without_inj, Abbr`t`] >>
  rw[GSYM disjoint_bigunion_card, field_order_equal_bigunion, Abbr`s`, Abbr`t`, Abbr`m`]);

(* This is a statement that:
   Every nonzero element in FiniteField r must have some order that divides (CARD R+) *)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
