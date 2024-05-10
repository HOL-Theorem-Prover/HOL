(* ------------------------------------------------------------------------ *)
(* Integral Domain Theory                                                   *)
(* ------------------------------------------------------------------------ *)

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
(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "integralDomain";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory listTheory sortingTheory containerTheory dep_rewrite
     arithmeticTheory dividesTheory;

open groupTheory monoidTheory ringTheory ringUnitTheory ringIdealTheory;
open groupOrderTheory;
open groupMapTheory ringMapTheory ringDividesTheory;

(* ------------------------------------------------------------------------- *)
(* Integral Domain Documentation                                             *)
(* ------------------------------------------------------------------------- *)
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
    by metis_tac[ringUnitTheory.ring_unit_property]
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
  \\ `∃s. Unit r s /\ p = s * q` by metis_tac[ring_associates_def]
  \\ qmatch_asmsub_abbrev_tac`r.prod.op p p1`
  \\ qmatch_asmsub_abbrev_tac`rassoc (p * p1) p2`
  \\ `∃s2. Unit r s2 /\ p * p1 = s2 * p2` by metis_tac[ring_associates_def]
  \\ qmatch_asmsub_abbrev_tac`q * q1`
  \\ `q1 IN r.prod.carrier`
  by ( qunabbrev_tac`q1` \\ irule GBAG_in_carrier \\ fs[SUBSET_DEF] )
  \\ `s IN r.carrier /\ s2 IN r.carrier` by metis_tac[ring_unit_property]
  \\ `r.prod.carrier = r.carrier` by simp[]
  \\ `∃s3. s3 IN r.carrier /\ s * s3 = #1` by metis_tac[ring_unit_property]
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
  \\ `ring_prime r q ∧ q <> #0 /\ ~Unit r q` by metis_tac[]
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

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
