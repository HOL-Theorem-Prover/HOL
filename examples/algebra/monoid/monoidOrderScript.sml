(* ------------------------------------------------------------------------- *)
(* Monoid Order and Invertibles                                              *)
(* ------------------------------------------------------------------------- *)

(*

Monoid Order
============
This is an investigation of the equation x ** n = #e.
Given x IN G, x ** 0 = #e   by monoid_exp_0
But for those having non-trivial n with x ** n = #e,
the least value of n is called the order for the element x.
This is an important property for the element x,
especiallly later for Finite Group.

Monoid Invertibles
==================
In a monoid M, not all elements are invertible.
But for those elements that are invertible,
they have interesting properties.
Indeed, being invertible, an operation .inv or |/
can be defined through Skolemization, and later,
the Monoid Invertibles will be shown to be a Group.

*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "monoidOrder";

(* ------------------------------------------------------------------------- *)


(* val _ = load "jcLib"; *)
open jcLib;

(* Get dependent theories in lib *)
(* val _ = load "helperFunctionTheory"; *)
(* (* val _ = load "helperNumTheory"; -- in helperFunctionTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in helperFunctionTheory *) *)
open helperNumTheory helperSetTheory helperFunctionTheory;

(* open dependent theories *)
open pred_setTheory arithmeticTheory;
open dividesTheory gcdTheory;

(* val _ = load "monoidTheory"; *)
open monoidTheory;

(* val _ = load "primePowerTheory"; *)
open primePowerTheory;


(* ------------------------------------------------------------------------- *)
(* Monoid Order and Invertibles Documentation                                *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   ord x             = order g x
   maximal_order g   = MAX_SET (IMAGE ord G)
   G*                = monoid_invertibles g
   reciprocal x      = monoid_inv g x
   |/                = reciprocal
*)
(* Definitions and Theorems (# are exported):

   Definitions:
   period_def      |- !g x k. period g x k <=> 0 < k /\ (x ** k = #e)
   order_def       |- !g x. ord x = case OLEAST k. period g x k of NONE => 0 | SOME k => k
   order_alt       |- !g x. ord x = case OLEAST k. 0 < k /\ x ** k = #e of NONE => 0 | SOME k => k
   order_property  |- !g x. x ** ord x = #e
   order_period    |- !g x. 0 < ord x ==> period g x (ord x)
   order_minimal   |- !g x n. 0 < n /\ n < ord x ==> x ** n <> #e
   order_eq_0      |- !g x. (ord x = 0) <=> !n. 0 < n ==> x ** n <> #e
   order_thm       |- !g x n. 0 < n ==>
                      ((ord x = n) <=> (x ** n = #e) /\ !m. 0 < m /\ m < n ==> x ** m <> #e)

#  monoid_order_id         |- !g. Monoid g ==> (ord #e = 1)
   monoid_order_eq_1       |- !g. Monoid g ==> !x. x IN G ==> ((ord x = 1) <=> (x = #e))
   monoid_order_condition  |- !g. Monoid g ==> !x. x IN G ==> !m. (x ** m = #e) <=> ord x divides m
   monoid_order_divides_exp|- !g. Monoid g ==> !x n. x IN G ==> ((x ** n = #e) <=> ord x divides n)
   monoid_order_power_eq_0 |- !g. Monoid g ==> !x. x IN G ==> !k. (ord (x ** k) = 0) <=> 0 < k /\ (ord x = 0)
   monoid_order_power      |- !g. Monoid g ==> !x. x IN G ==> !k. ord (x ** k) * gcd (ord x) k = ord x
   monoid_order_power_eqn  |- !g. Monoid g ==> !x k. x IN G /\ 0 < k ==> (ord (x ** k) = ord x DIV gcd k (ord x))
   monoid_order_power_coprime   |- !g. Monoid g ==> !x. x IN G ==>
                                   !n. coprime n (ord x) ==> (ord (x ** n) = ord x)
   monoid_order_cofactor   |- !g. Monoid g ==> !x n. x IN G /\ 0 < ord x /\ n divides (ord x) ==>
                                                     (ord (x ** (ord x DIV n)) = n)
   monoid_order_divisor    |- !g. Monoid g ==> !x m. x IN G /\ 0 < ord x /\ m divides (ord x) ==>
                                               ?y. y IN G /\ (ord y = m)
   monoid_order_common     |- !g. Monoid g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) ==>
                                       ?z. z IN G /\ (ord z * gcd (ord x) (ord y) = lcm (ord x) (ord y))
   monoid_order_common_coprime  |- !g. Monoid g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) /\
                                       coprime (ord x) (ord y) ==> ?z. z IN G /\ (ord z = ord x * ord y)
   monoid_exp_mod_order         |- !g. Monoid g ==> !x. x IN G /\ 0 < ord x ==> !n. x ** n = x ** (n MOD ord x)
   abelian_monoid_order_common  |- !g. AbelianMonoid g ==> !x y. x IN G /\ y IN G ==>
                                       ?z. z IN G /\ (ord z * gcd (ord x) (ord y) = lcm (ord x) (ord y))
   abelian_monoid_order_common_coprime
                                |- !g. AbelianMonoid g ==> !x y. x IN G /\ y IN G /\
                                       coprime (ord x) (ord y) ==> ?z. z IN G /\ (ord z = ord x * ord y)
   abelian_monoid_order_lcm     |- !g. AbelianMonoid g ==>
                                   !x y. x IN G /\ y IN G ==> ?z. z IN G /\ (ord z = lcm (ord x) (ord y))

   Orders of elements:
   orders_def      |- !g n. orders g n = {x | x IN G /\ (ord x = n)}
   orders_element  |- !g x n. x IN orders g n <=> x IN G /\ (ord x = n)
   orders_subset   |- !g n. orders g n SUBSET G
   orders_finite   |- !g. FINITE G ==> !n. FINITE (orders g n)
   orders_eq_1     |- !g. Monoid g ==> (orders g 1 = {#e})

   Maximal Order:
   maximal_order_alt            |- !g. maximal_order g = MAX_SET {ord z | z | z IN G}
   monoid_order_divides_maximal |- !g. FiniteAbelianMonoid g ==>
                                   !x. x IN G /\ 0 < ord x ==> ord x divides maximal_order g

   Monoid Invertibles:
   monoid_invertibles_def       |- !g. G* = {x | x IN G /\ ?y. y IN G /\ (x * y = #e) /\ (y * x = #e)}
   monoid_invertibles_element   |- !g x. x IN G* <=> x IN G /\ ?y. y IN G /\ (x * y = #e) /\ (y * x = #e)
   monoid_order_nonzero         |- !g x. Monoid g /\ x IN G /\ 0 < ord x ==> x IN G*

   Invertibles_def              |- !g. Invertibles g = <|carrier := G*; op := $*; id := #e|>
   Invertibles_property         |- !g. ((Invertibles g).carrier = G* ) /\
                                       ((Invertibles g).op = $* ) /\
                                       ((Invertibles g).id = #e) /\
                                       ((Invertibles g).exp = $** )
   Invertibles_carrier          |- !g. (Invertibles g).carrier = G*
   Invertibles_subset           |- !g. (Invertibles g).carrier SUBSET G
   Invertibles_order            |- !g x. order (Invertibles g) x = ord x

   Monoid Inverse as an operation:
   monoid_inv_def               |- !g x. Monoid g /\ x IN G* ==> |/ x IN G /\ (x * |/ x = #e) /\ ( |/ x * x = #e)
   monoid_inv_def_alt           |- !g. Monoid g ==> !x. x IN G* <=>
                                                        x IN G /\ |/ x IN G /\ (x * |/ x = #e) /\ ( |/ x * x = #e)
   monoid_inv_element           |- !g. Monoid g ==> !x. x IN G* ==> x IN G
#  monoid_id_invertible         |- !g. Monoid g ==> #e IN G*
#  monoid_inv_op_invertible     |- !g. Monoid g ==> !x y. x IN G* /\ y IN G* ==> x * y IN G*
#  monoid_inv_invertible        |- !g. Monoid g ==> !x. x IN G* ==> |/ x IN G*
   monoid_invertibles_is_monoid |- !g. Monoid g ==> Monoid (Invertibles g)

*)

(* ------------------------------------------------------------------------- *)
(* Monoid Order Definition.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define order = optional LEAST period for an element x in Group g *)
val period_def = zDefine`
  period (g:'a monoid) (x:'a) k <=> 0 < k /\ (x ** k = #e)
`;
val order_def = zDefine`
  order (g:'a monoid) (x:'a) = case OLEAST k. period g x k of
                                 NONE => 0
                               | SOME k => k
`;
(* use zDefine here since these are not computationally effective. *)

(* Expand order_def with period_def. *)
val order_alt = save_thm(
  "order_alt", REWRITE_RULE [period_def] order_def);
(* val order_alt =
   |- !g x. order g x =
            case OLEAST k. 0 < k /\ x ** k = #e of NONE => 0 | SOME k => k: thm *)

(* overloading on Monoid Order *)
val _ = overload_on ("ord", ``order g``);

(* Theorem: (x ** (ord x) = #e *)
(* Proof: by definition, and x ** 0 = #e by monoid_exp_0. *)
val order_property = store_thm(
  "order_property",
  ``!g:'a monoid. !x:'a. (x ** (ord x) = #e)``,
  ntac 2 strip_tac >>
  simp_tac std_ss[order_def, period_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  rw[]);

(* Theorem: 0 < (ord x) ==> period g x (ord x) *)
(* Proof: by order_property, period_def. *)
val order_period = store_thm(
  "order_period",
  ``!g:'a monoid x:'a. 0 < (ord x) ==> period g x (ord x)``,
  rw[order_property, period_def]);

(* Theorem: !n. 0 < n /\ n < (ord x) ==> x ** n <> #e *)
(* Proof: by definition of OLEAST. *)
Theorem order_minimal:
  !g:'a monoid x:'a. !n. 0 < n /\ n < ord x ==> x ** n <> #e
Proof
  ntac 3 strip_tac >>
  simp_tac std_ss[order_def, period_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  rw_tac std_ss[] >>
  metis_tac[DECIDE “~(0 < 0)”]
QED

(* Theorem: (ord x = 0) <=> !n. 0 < n ==> x ** n <> #e *)
(* Proof:
   Expand by order_def, period_def, this is to show:
   (1) 0 < n /\ (!n. ~(0 < n) \/ x ** n <> #e) ==> x ** n <> #e
       True by assertion.
   (2) 0 < n /\ x ** n = #e /\ (!m. m < 0 ==> ~(0 < m) \/ x ** m <> #e) ==> (n = 0) <=> !n. 0 < n ==> x ** n <> #e
       True by assertion.
*)
Theorem order_eq_0:
  !g:'a monoid x. ord x = 0 <=> !n. 0 < n ==> x ** n <> #e
Proof
  ntac 2 strip_tac >>
  simp_tac std_ss[order_def, period_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  rw_tac std_ss[] >>
  metis_tac[DECIDE “~(0 < 0)”]
QED

val std_ss = std_ss -* ["NOT_LT_ZERO_EQ_ZERO"]

(* Theorem: 0 < n ==> ((ord x = n) <=> (x ** n = #e) /\ !m. 0 < m /\ m < n ==> x ** m <> #e) *)
(* Proof:
   If part: (ord x = n) ==> (x ** n = #e) /\ !m. 0 < m /\ m < n ==> x ** m <> #e
      This is to show:
      (1) (ord x = n) ==> (x ** n = #e), true by order_property
      (2) (ord x = n) ==> !m. 0 < m /\ m < n ==> x ** m <> #e, true by order_minimal
   Only-if part: (x ** n = #e) /\ !m. 0 < m /\ m < n ==> x ** m <> #e ==> (ord x = n)
      Expanding by order_def, period_def, this is to show:
      (1) 0 < n /\ x ** n = #e /\ !n'. ~(0 < n') \/ x ** n' <> #e ==> 0 = n
          Putting n' = n, the assumption is contradictory.
      (2) 0 < n /\ 0 < n' /\ x ** n = #e /\ x ** n' = #e /\ ... ==> n' = n
          The assumptions implies ~(n' < n), and ~(n < n'), hence n' = n.
*)
val order_thm = store_thm(
  "order_thm",
  ``!g:'a monoid x:'a. !n. 0 < n ==>
    ((ord x = n) <=> (x ** n = #e) /\ !m. 0 < m /\ m < n ==> x ** m <> #e)``,
  rw[EQ_IMP_THM] >-
  rw[order_property] >-
  rw[order_minimal] >>
  simp_tac std_ss[order_def, period_def] >>
  DEEP_INTRO_TAC whileTheory.OLEAST_INTRO >>
  rw_tac std_ss[] >-
  metis_tac[] >>
  `~(n' < n)` by metis_tac[] >>
  `~(n < n')` by metis_tac[] >>
  decide_tac);

(* Theorem: Monoid g ==> (ord #e = 1) *)
(* Proof:
   Since #e IN G        by monoid_id_element
   and   #e ** 1 = #e   by monoid_exp_1
   Obviously, 0 < 1 and there is no m such that 0 < m < 1
   hence true by order_thm
*)
val monoid_order_id = store_thm(
  "monoid_order_id",
  ``!g:'a monoid. Monoid g ==> (ord #e = 1)``,
  rw[order_thm, DECIDE``!m . ~(0 < m /\ m < 1)``]);

(* export simple result *)
val _ = export_rewrites ["monoid_order_id"];

(* Theorem: Monoid g ==> !x. x IN G ==> ((ord x = 1) <=> (x = #e)) *)
(* Proof:
   If part: ord x = 1 ==> x = #e
      Since x ** (ord x) = #e      by order_property
        ==> x ** 1 = #e            by given
        ==> x = #e                 by monoid_exp_1
   Only-if part: x = #e ==> ord x = 1
      i.e. to show ord #e = 1.
      True by monoid_order_id.
*)
val monoid_order_eq_1 = store_thm(
  "monoid_order_eq_1",
  ``!g:'a monoid. Monoid g ==> !x. x IN G ==> ((ord x = 1) <=> (x = #e))``,
  rw[EQ_IMP_THM] >>
  `#e = x ** (ord x)` by rw[order_property] >>
  rw[]);

(* Theorem: Monoid g ==> !x. x IN G ==> !m. (x ** m = #e) <=> (ord x) divides m *)
(* Proof:
   (ord x) is a period, and so divides all periods.
   Let n = ord x.
   If part: x^m = #e ==> n divides m
      If n = 0, m = 0   by order_eq_0
         Hence true     by ZERO_DIVIDES
      If n <> 0,
      By division algorithm, m = q * n + t   for some q, t and t < n.
      #e = x^m
         = x^(q * n + t)
         = (x^n)^q * x^t
         = #e * x^t
     Thus x^t = #e, but t < n.
     If 0 < t, this contradicts order_minimal.
     Hence t = 0, or n divides m.
   Only-if part: n divides m ==> x^m = #e
     By divides_def, ?k. m = k * n
     x^m = x^(k * n) = (x^n)^k = #e^k = #e.
*)
val monoid_order_condition = store_thm(
  "monoid_order_condition",
  ``!g:'a monoid. Monoid g ==> !x. x IN G ==> !m. (x ** m = #e) <=> (ord x) divides m``,
  rpt strip_tac >>
  qabbrev_tac `n = ord x` >>
  rw[EQ_IMP_THM] >| [
    Cases_on `n = 0` >| [
      `~(0 < m)` by metis_tac[order_eq_0] >>
      `m = 0` by decide_tac >>
      rw[ZERO_DIVIDES],
      `x ** n = #e` by rw[order_property, Abbr`n`] >>
      `0 < n` by decide_tac >>
      `?q t. (m = q * n + t) /\ t < n` by metis_tac[DIVISION] >>
      `x ** m = x ** (n * q + t)` by metis_tac[MULT_COMM] >>
      `_ = (x ** (n * q)) * (x ** t)` by rw[] >>
      `_ = ((x ** n) ** q) * (x ** t)` by rw[] >>
      `_ = x ** t` by rw[] >>
      `~(0 < t)` by metis_tac[order_minimal] >>
      `t = 0` by decide_tac >>
      `m = q * n` by rw[] >>
      metis_tac[divides_def]
    ],
    `x ** n = #e` by rw[order_property, Abbr`n`] >>
    `?k. m = k * n` by rw[GSYM divides_def] >>
    `x ** m = x ** (n * k)` by metis_tac[MULT_COMM] >>
    `_ = (x ** n) ** k` by rw[] >>
    rw[]
  ]);

(* Theorem: Monoid g ==> !x n. x IN G ==> (x ** n = #e <=> ord x divides n) *)
(* Proof: by monoid_order_condition *)
val monoid_order_divides_exp = store_thm(
  "monoid_order_divides_exp",
  ``!g:'a monoid. Monoid g ==> !x n. x IN G ==> ((x ** n = #e) <=> ord x divides n)``,
  rw[monoid_order_condition]);

(* Theorem: Monoid g ==> !x. x IN G ==> !k. (ord (x ** k) = 0) <=> 0 < k /\ (ord x = 0) *)
(* Proof:
   By order_eq_0, this is to show:
   (1) !n. 0 < n ==> (x ** k) ** n <> #e ==> 0 < k
       By contradiction. Assume k = 0.
       Then x ** k = #e         by monoid_exp_0
        and #e ** n = #e        by monoid_id_exp
       This contradicts the implication: (x ** k) ** n <> #e.
   (2) 0 < n /\ !n. 0 < n ==> (x ** k) ** n <> #e ==> x ** n <> #e
       By contradiction. Assume x ** n = #e.
       Now, (x ** k) ** n
           = x ** (k * n)        by monoid_exp_mult
           = x ** (n * k)        by MULT_COMM
           = (x ** n) * k        by monoid_exp_mult
           = #e ** k             by x ** n = #e
           = #e                  by monoid_id_exp
       This contradicts the implication: (x ** k) ** n <> #e.
   (3) 0 < n /\ !n. 0 < n ==> x ** n <> #e ==> (x ** k) ** n <> #e
       By contradiction. Assume (x ** k) ** n = #e.
       0 < k /\ 0 < n ==> 0 < k * n       by arithmetic
       But (x ** n) ** k = x ** (n * k)   by monoid_exp_mult
       This contradicts the implication: (x ** k) ** n <> #e.
*)
val monoid_order_power_eq_0 = store_thm(
  "monoid_order_power_eq_0",
  ``!g:'a monoid. Monoid g ==> !x. x IN G ==> !k. (ord (x ** k) = 0) <=> 0 < k /\ (ord x = 0)``,
  rw[order_eq_0, EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `k = 0` by decide_tac >>
    `x ** k = #e` by rw[monoid_exp_0] >>
    metis_tac[monoid_id_exp, DECIDE``0 < 1``],
    metis_tac[monoid_exp_mult, MULT_COMM, monoid_id_exp],
    `0 < k * n` by rw[LESS_MULT2] >>
    metis_tac[monoid_exp_mult]
  ]);

(* Theorem: ord (x ** k) = ord x / gcd(ord x, k)
            Monoid g ==> !x. x IN G ==> !k. (ord (x ** k) * (gcd (ord x) k) = ord x) *)
(* Proof:
   Let n = ord x, m = ord (x^k), d = gcd(n,k).
   This is to show: m = n / d.
   If k = 0,
      m = ord (x^0) = ord #e = 1   by monoid_order_id
      d = gcd(n,0) = n             by GCD_0R
      henc true.
   If k <> 0,
   First, show ord (x^k) = m divides n/d.
     If n = 0, m = 0               by monoid_order_power_eq_0
     so ord (x^k) = m | (n/d)      by ZERO_DIVIDES
     If n <> 0,
     (x^k)^(n/d) = x^(k * n/d) = x^(n * k/d) = (x^n)^(k/d) = #e,
     so ord (x^k) = m | (n/d)      by monoid_order_condition.
   Second, show (n/d) divides m = ord (x^k), or equivalently: n divides d * m
     x^(k * m) = (x^k)^m = #e = x^n,
     so ord x = n | k * m          by monoid_order_condition
     Since d = gcd(k,n), there are integers a and b such that
       ka + nb = d                 by LINEAR_GCD
     Multiply by m: k * m * a + n * m * b = d * m.
     But since n | k * m, it follows that n | d*m,
     i.e. (n/d) | m                by DIVIDES_CANCEL.
   By DIVIDES_ANTISYM, ord (x^k) = m = n/d.
*)
val monoid_order_power = store_thm(
  "monoid_order_power",
  ``!g:'a monoid. Monoid g ==> !x. x IN G ==> !k. (ord (x ** k) * (gcd (ord x) k) = ord x)``,
  rpt strip_tac >>
  qabbrev_tac `n = ord x` >>
  qabbrev_tac `m = ord (x ** k)` >>
  qabbrev_tac `d = gcd n k` >>
  Cases_on `k = 0` >| [
    `d = n` by metis_tac[GCD_0R] >>
    rw[Abbr`m`],
    Cases_on `n = 0` >| [
      `0 < k` by decide_tac >>
      `m = 0` by rw[monoid_order_power_eq_0, Abbr`n`, Abbr`m`] >>
      rw[],
      `x ** n = #e` by rw[order_property, Abbr`n`] >>
      `0 < n /\ 0 < k` by decide_tac >>
      `?p q. (n = p * d) /\ (k = q * d)` by metis_tac[FACTOR_OUT_GCD] >>
      `k * p = n * q` by rw_tac arith_ss[] >>
      `(x ** k) ** p = x ** (k * p)` by rw[] >>
      `_ = x ** (n * q)` by metis_tac[] >>
      `_ = (x ** n) ** q` by rw[] >>
      `_ = #e` by rw[] >>
      `m divides p` by rw[GSYM monoid_order_condition, Abbr`m`] >>
      `x ** (m * k) = x ** (k * m)` by metis_tac[MULT_COMM] >>
      `_ = (x ** k) ** m` by rw[] >>
      `_ = #e` by rw[order_property, Abbr`m`] >>
      `n divides (m * k)` by rw[GSYM monoid_order_condition, Abbr`n`, Abbr`m`] >>
      `?u v. u * k = v * n + d` by rw[LINEAR_GCD, Abbr`d`] >>
      `m * k * u = m * (u * k)` by rw_tac arith_ss[] >>
      `_ = m * (v * n) + m * d` by metis_tac[LEFT_ADD_DISTRIB] >>
      `_ = m * v * n + m * d` by rw_tac arith_ss[] >>
      `n divides (m * k * u)` by metis_tac[DIVIDES_MULT] >>
      `n divides (m * v * n)` by metis_tac[divides_def] >>
      `n divides (m * d)` by metis_tac[DIVIDES_ADD_2] >>
      `d <> 0` by metis_tac[MULT_EQ_0] >>
      `0 < d` by decide_tac >>
      `p divides m` by metis_tac[DIVIDES_CANCEL] >>
      metis_tac[DIVIDES_ANTISYM]
    ]
  ]);

(* Theorem: Monoid g ==>
   !x k. x IN G /\ 0 < k ==> (ord (x ** k) = (ord x) DIV (gcd k (ord x))) *)
(* Proof:
   Note ord (x ** k) * gcd k (ord x) = ord x         by monoid_order_power, GCD_SYM
    and 0 < gcd k (ord x)                            by GCD_EQ_0, 0 < k
    ==> ord (x ** k) = (ord x) DIV (gcd k (ord x))   by MULT_EQ_DIV
*)
val monoid_order_power_eqn = store_thm(
  "monoid_order_power_eqn",
  ``!g:'a monoid. Monoid g ==>
   !x k. x IN G /\ 0 < k ==> (ord (x ** k) = (ord x) DIV (gcd k (ord x)))``,
  rpt strip_tac >>
  `ord (x ** k) * gcd k (ord x) = ord x` by metis_tac[monoid_order_power, GCD_SYM] >>
  `0 < gcd k (ord x)` by metis_tac[GCD_EQ_0, NOT_ZERO] >>
  fs[MULT_EQ_DIV]);

(* Theorem: Monoid g ==> !x. x IN G ==> !n. coprime n (ord x) ==> (ord (x ** n) = ord x) *)
(* Proof:
     ord x
   = ord (x ** n) * gcd (ord x) n   by monoid_order_power
   = ord (x ** n) * 1               by coprime_sym
   = ord (x ** n)                   by MULT_RIGHT_1
*)
val monoid_order_power_coprime = store_thm(
  "monoid_order_power_coprime",
  ``!g:'a monoid. Monoid g ==> !x. x IN G ==> !n. coprime n (ord x) ==> (ord (x ** n) = ord x)``,
  metis_tac[monoid_order_power, coprime_sym, MULT_RIGHT_1]);

(* Theorem: Monoid g ==>
            !x n. x IN G /\ 0 < ord x /\ n divides ord x ==> (ord (x ** (ord x DIV n)) = n) *)
(* Proof:
   Let m = ord x, k = m DIV n.
   Since 0 < m, n <> 0, or 0 < n         by ZERO_DIVIDES
   Since n divides m, m = k * n          by DIVIDES_EQN
   Hence k divides m                     by divisors_def, MULT_COMM
     and k <> 0                          by MULT, m <> 0
     and gcd k m = k                     by divides_iff_gcd_fix
     Now ord (x ** k) * k
       = m                               by monoid_order_power
       = k * n                           by above
       = n * k                           by MULT_COMM
   Hence ord (x ** k) = n                by MULT_RIGHT_CANCEL, k <> 0
*)
val monoid_order_cofactor = store_thm(
  "monoid_order_cofactor",
  ``!g: 'a monoid. Monoid g ==>
     !x n. x IN G /\ 0 < ord x /\ n divides ord x ==> (ord (x ** (ord x DIV n)) = n)``,
  rpt strip_tac >>
  qabbrev_tac `m = ord x` >>
  qabbrev_tac `k = m DIV n` >>
  `0 < n` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `m = k * n` by rw[GSYM DIVIDES_EQN, Abbr`k`] >>
  `k divides m` by metis_tac[divides_def, MULT_COMM] >>
  `k <> 0` by metis_tac[MULT, NOT_ZERO_LT_ZERO] >>
  `gcd k m = k` by rw[GSYM divides_iff_gcd_fix] >>
  metis_tac[monoid_order_power, GCD_SYM, MULT_COMM, MULT_RIGHT_CANCEL]);

(* Theorem: If x IN G with ord x = n > 0, and m divides n, then G contains an element of order m. *)
(* Proof:
   m divides n ==> n = k * m  for some k, by divides_def.
   Then x^k has order m:
   (x^k)^m = x^(k * m) = x^n = #e
   and for any h < m,
   if (x^k)^h = x^(k * h) = #e means x has order k * h < k * m = n,
   which is a contradiction with order_minimal.
*)
val monoid_order_divisor = store_thm(
  "monoid_order_divisor",
  ``!g:'a monoid. Monoid g ==>
   !x m. x IN G /\ 0 < ord x /\ m divides (ord x) ==> ?y. y IN G /\ (ord y = m)``,
  rpt strip_tac >>
  `ord x <> 0` by decide_tac >>
  `m <> 0` by metis_tac[ZERO_DIVIDES] >>
  `0 < m` by decide_tac >>
  `?k. ord x = k * m` by rw[GSYM divides_def] >>
  qexists_tac `x ** k` >>
  rw[] >>
  `x ** (ord x) = #e` by rw[order_property] >>
  `(x ** k) ** m = #e` by metis_tac[monoid_exp_mult] >>
  `(!h. 0 < h /\ h < m ==> (x ** k) ** h <> #e)` suffices_by metis_tac[order_thm] >>
  rpt strip_tac >>
  `h <> 0` by decide_tac >>
  `k <> 0 /\ k * h <> 0` by metis_tac[MULT, MULT_EQ_0] >>
  `0 < k /\ 0 < k * h` by decide_tac >>
  `k * h < k * m` by metis_tac[LT_MULT_LCANCEL] >>
  `(x ** k) ** h = x ** (k * h)` by rw[] >>
  metis_tac[order_minimal]);

(* Theorem: If x * y = y * x, and n = ord x, m = ord y,
            then there exists z IN G such that ord z = (lcm n m) / (gcd n m) *)
(* Proof:
   Let n = ord x, m = ord y, d = gcd(n, m).
   This is to show: ?z. z IN G /\ (ord z * d = n * m)
   If n = 0, take z = x, by LCM_0.
   If m = 0, take z = y, by LCM_0.
   If n <> 0 and m <> 0,
   First, get a pair with coprime orders.
   ?p q. (n = p * d) /\ (m = q * d) /\ coprime p q   by FACTOR_OUT_GCD
   Let u = x^d, v = y^d
   then ord u = ord (x^d) = ord x / gcd(n, d) = n/d = p   by monoid_order_power
    and ord v = ord (y^d) = ord y / gcd(m, d) = m/d = q   by monoid_order_power
   Now gcd(p,q) = 1, and there exists integers a and b such that
     a * p + b * q = 1             by LINEAR_GCD
   Let w = u^b * v^a
   Then w^p = (u^b * v^a)^p
            = (u^b)^p * (v^a)^p    by monoid_comm_op_exp
            = (u^p)^b * (v^a)^p    by monoid_exp_mult_comm
            = #e^b * v^(a * p)     by p = ord u
            = v^(a * p)            by monoid_id_exp
            = v^(1 - b * q)        by LINEAR_GCD condition
            = v^1 * |/ v^(b * q)   by variant of monoid_exp_add
            = v * 1/ (v^q)^b       by monoid_exp_mult_comm
            = v * 1/ #e^b          by q = ord v
            = v
   Hence ord (w^p) = ord v = q,
   Let c = ord w, c <> 0 since p * q <> 0   by GCD_0L
   then q = ord (w^p) = c / gcd(c,p)        by monoid_order_power
   i.e. q * gcd(c,p) = c, or q divides c
   Similarly, w^q = u, and p * gcd(c,q) = c, or p divides c.
   Since coprime p q, p * q divides c, an order of element w IN G.
   Hence there is some z in G such that ord z = p * q  by monoid_order_divisor.
   i.e.  ord z = lcm p q = lcm (n/d) (m/d) = (lcm n m) / d.
*)
val monoid_order_common = store_thm(
  "monoid_order_common",
  ``!g:'a monoid. Monoid g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) ==>
     ?z. z IN G /\ ((ord z) * gcd (ord x) (ord y) = lcm (ord x) (ord y))``,
  rpt strip_tac >>
  qabbrev_tac `n = ord x` >>
  qabbrev_tac `m = ord y` >>
  qabbrev_tac `d = gcd n m` >>
  Cases_on `n = 0` >-
  metis_tac[LCM_0, MULT_EQ_0] >>
  Cases_on `m = 0` >-
  metis_tac[LCM_0, MULT_EQ_0] >>
  `x ** n = #e` by rw[order_property, Abbr`n`] >>
  `y ** m = #e` by rw[order_property, Abbr`m`] >>
  `d <> 0` by rw[GCD_EQ_0, Abbr`d`] >>
  `?p q. (n = p * d) /\ (m = q * d) /\ coprime p q` by rw[FACTOR_OUT_GCD, Abbr`d`] >>
  qabbrev_tac `u = x ** d` >>
  qabbrev_tac `v = y ** d` >>
  `u IN G /\ v IN G` by rw[Abbr`u`, Abbr`v`] >>
  `(gcd n d = d) /\ (gcd m d = d)` by rw[GCD_GCD, GCD_SYM, Abbr`d`] >>
  `ord u = p` by metis_tac[monoid_order_power, MULT_RIGHT_CANCEL] >>
  `ord v = q` by metis_tac[monoid_order_power, MULT_RIGHT_CANCEL] >>
  `p <> 0 /\ q <> 0` by metis_tac[MULT_EQ_0] >>
  `?a b. a * q = b * p + 1` by metis_tac[LINEAR_GCD] >>
  `?h k. h * p = k * q + 1` by metis_tac[LINEAR_GCD, GCD_SYM] >>
  qabbrev_tac `ua = u ** a` >>
  qabbrev_tac `vh = v ** h` >>
  qabbrev_tac `w = ua * vh` >>
  `ua IN G /\ vh IN G /\ w IN G` by rw[Abbr`ua`, Abbr`vh`, Abbr`w`] >>
  `ua * vh = (x ** d) ** a * (y ** d) ** h` by rw[] >>
  `_ = x ** (d * a) * y ** (d * h)` by rw_tac std_ss[GSYM monoid_exp_mult] >>
  `_ = y ** (d * h) * x ** (d * a)` by metis_tac[monoid_comm_exp_exp] >>
  `_ = vh * ua` by rw[] >>
  `w ** p = (ua * vh) ** p` by rw[] >>
  `_ = ua ** p * vh ** p` by metis_tac[monoid_comm_op_exp] >>
  `_ = (u ** p) ** a * (v ** h) ** p` by rw[monoid_exp_mult_comm] >>
  `_ = #e ** a * v ** (h * p)` by rw[order_property] >>
  `_ = v ** (h * p)` by rw[] >>
  `_ = v ** (k * q + 1)` by rw_tac std_ss[] >>
  `_ = v ** (k * q) * v` by rw[] >>
  `_ = v ** (q * k) * v` by rw_tac std_ss[MULT_COMM] >>
  `_ = (v ** q) ** k * v` by rw[] >>
  `_ = #e ** k * v` by rw[order_property] >>
  `_ = v` by rw[] >>
  `w ** q = (ua * vh) ** q` by rw[] >>
  `_ = ua ** q * vh ** q` by metis_tac[monoid_comm_op_exp] >>
  `_ = (u ** a) ** q * (v ** q) ** h` by rw[monoid_exp_mult_comm] >>
  `_ = u ** (a * q) * #e ** h` by rw[order_property] >>
  `_ = u ** (a * q)` by rw[] >>
  `_ = u ** (b * p + 1)` by rw_tac std_ss[] >>
  `_ = u ** (b * p) * u` by rw[] >>
  `_ = u ** (p * b) * u` by rw_tac std_ss[MULT_COMM] >>
  `_ = (u ** p) ** b * u` by rw[] >>
  `_ = #e ** b * u` by rw[order_property] >>
  `_ = u` by rw[] >>
  qabbrev_tac `c = ord w` >>
  `q * gcd c p = c` by rw[monoid_order_power, Abbr`c`] >>
  `p * gcd c q = c` by metis_tac[monoid_order_power] >>
  `p divides c /\ q divides c` by metis_tac[divides_def, MULT_COMM] >>
  `lcm p q = p * q` by rw[LCM_COPRIME] >>
  `(p * q) divides c` by metis_tac[LCM_IS_LEAST_COMMON_MULTIPLE] >>
  `p * q <> 0` by rw[MULT_EQ_0] >>
  `c <> 0` by metis_tac[GCD_0L] >>
  `0 < c` by decide_tac >>
  `?z. z IN G /\ (ord z = p * q)` by metis_tac[monoid_order_divisor] >>
  `ord z * d = d * (p * q)` by rw_tac arith_ss[] >>
  `_ = lcm (d * p) (d * q)` by rw[LCM_COMMON_FACTOR] >>
  `_ = lcm n m` by metis_tac[MULT_COMM] >>
  metis_tac[]);

(* This is a milestone. *)

(* Theorem: If x * y = y * x, and n = ord x, m = ord y, and gcd n m = 1,
            then there exists z IN G with ord z = (lcm n m) *)
(* Proof:
   By monoid_order_common and gcd n m = 1.
*)
val monoid_order_common_coprime = store_thm(
  "monoid_order_common_coprime",
  ``!g:'a monoid. Monoid g ==> !x y. x IN G /\ y IN G /\ (x * y = y * x) /\ coprime (ord x) (ord y) ==>
     ?z. z IN G /\ (ord z = (ord x) * (ord y))``,
  metis_tac[monoid_order_common, GCD_LCM, MULT_RIGHT_1, MULT_LEFT_1]);
(* This version can be proved directly using previous technique, then derive the general case:
   Let ord x = n, ord y = m.
   Let d = gcd(n,m)  p = n/d, q = m/d, gcd(p,q) = 1.
   By p | n = ord x, there is u with ord u = p     by monoid_order_divisor
   By q | m = ord y, there is v with ord v = q     by monoid_order_divisor
   By gcd(ord u, ord v) = gcd(p,q) = 1,
   there is z with ord z = lcm(p,q) = p * q = n/d * m/d = lcm(n,m)/gcd(n,m).
*)

(* Theorem: Monoid g ==> !x. x IN G /\ 0 < ord x ==> !n. x ** n = x ** (n MOD (ord x)) *)
(* Proof:
   Let z = ord x, 0 < z                         by given
   Note n = (n DIV z) * z + (n MOD z)           by DIVISION, 0 < z.
      x ** n
    = x ** ((n DIV z) * z + (n MOD z))          by above
    = x ** ((n DIV z) * z) * x ** (n MOD z)     by monoid_exp_add
    = x ** (z * (n DIV z)) * x ** (n MOD z)     by MULT_COMM
    = (x ** z) ** (n DIV z) * x ** (n MOD z)    by monoid_exp_mult
    = #e ** (n DIV 2) * x ** (n MOD z)          by order_property
    = #e * x ** (n MOD z)                       by monoid_id_exp
    = x ** (n MOD z)                            by monoid_lid
*)
val monoid_exp_mod_order = store_thm(
  "monoid_exp_mod_order",
  ``!g:'a monoid. Monoid g ==> !x. x IN G /\ 0 < ord x ==> !n. x ** n = x ** (n MOD (ord x))``,
  rpt strip_tac >>
  qabbrev_tac `z = ord x` >>
  `x ** n = x ** ((n DIV z) * z + (n MOD z))` by metis_tac[DIVISION] >>
  `_ = x ** ((n DIV z) * z) * x ** (n MOD z)` by rw[monoid_exp_add] >>
  `_ = x ** (z * (n DIV z)) * x ** (n MOD z)` by metis_tac[MULT_COMM] >>
  rw[monoid_exp_mult, order_property, Abbr`z`]);

(* Theorem: AbelianMonoid g ==> !x y. x IN G /\ y IN G ==>
            ?z. z IN G /\ (ord z * gcd (ord x) (ord y) = lcm (ord x) (ord y)) *)
(* Proof: by AbelianMonoid_def, monoid_order_common *)
val abelian_monoid_order_common = store_thm(
  "abelian_monoid_order_common",
  ``!g:'a monoid. AbelianMonoid g ==> !x y. x IN G /\ y IN G ==>
   ?z. z IN G /\ (ord z * gcd (ord x) (ord y) = lcm (ord x) (ord y))``,
  rw[AbelianMonoid_def, monoid_order_common]);

(* Theorem: AbelianMonoid g ==> !x y. x IN G /\ y IN G /\ coprime (ord x) (ord y) ==>
            ?z. z IN G /\ (ord z = ord x * ord y) *)
(* Proof: by AbelianMonoid_def, monoid_order_common_coprime *)
val abelian_monoid_order_common_coprime = store_thm(
  "abelian_monoid_order_common_coprime",
  ``!g:'a monoid. AbelianMonoid g ==> !x y. x IN G /\ y IN G /\ coprime (ord x) (ord y) ==>
   ?z. z IN G /\ (ord z = ord x * ord y)``,
  rw[AbelianMonoid_def, monoid_order_common_coprime]);

(* Theorem: AbelianMonoid g ==>
            !x y. x IN G /\ y IN G ==> ?z. z IN G /\ (ord z = lcm (ord x) (ord y)) *)
(* Proof:
   If ord x = 0,
      Then lcm 0 (ord y) = 0 = ord x     by LCM_0
      Thus take z = x.
   If ord y = 0
      lcm (ord x) 0 = 0 = ord y          by LCM_0
      Thus take z = y.
   Otherwise, 0 < ord x /\ 0 < ord y.
      Let m = ord x, n = ord y.
      Note ?a b p q. (lcm m n = p * q) /\ coprime p q /\
                     (m = a * p) /\ (n = b * q)   by lcm_gcd_park_decompose
      Thus p divides m /\ q divides n             by divides_def
       ==> ?u. u IN G /\ (ord u = p)              by monoid_order_divisor, p divides m
       and ?v. v IN G /\ (ord v = q)              by monoid_order_divisor, q divides n
       ==> ?z. z IN G /\ (ord z = p * q)          by monoid_order_common_coprime, coprime p q
        or     z IN G /\ (ord z = lcm m n)        by above
*)
val abelian_monoid_order_lcm = store_thm(
  "abelian_monoid_order_lcm",
  ``!g:'a monoid. AbelianMonoid g ==>
   !x y. x IN G /\ y IN G ==> ?z. z IN G /\ (ord z = lcm (ord x) (ord y))``,
  rw[AbelianMonoid_def] >>
  qabbrev_tac `m = ord x` >>
  qabbrev_tac `n = ord y` >>
  Cases_on `(m = 0) \/ (n = 0)` >-
  metis_tac[LCM_0] >>
  `0 < m /\ 0 < n` by decide_tac >>
  `?a b p q. (lcm m n = p * q) /\ coprime p q /\ (m = a * p) /\ (n = b * q)` by metis_tac[lcm_gcd_park_decompose] >>
  `p divides m /\ q divides n` by metis_tac[divides_def] >>
  `?u. u IN G /\ (ord u = p)` by metis_tac[monoid_order_divisor] >>
  `?v. v IN G /\ (ord v = q)` by metis_tac[monoid_order_divisor] >>
  `?z. z IN G /\ (ord z = p * q)` by rw[monoid_order_common_coprime] >>
  metis_tac[]);

(* This is much better than:
abelian_monoid_order_common
|- !g. AbelianMonoid g ==> !x y. x IN G /\ y IN G ==>
       ?z. z IN G /\ (ord z * gcd (ord x) (ord y) = lcm (ord x) (ord y))
*)

(* ------------------------------------------------------------------------- *)
(* Orders of elements                                                        *)
(* ------------------------------------------------------------------------- *)

(* Define the set of elements with a given order *)
val orders_def = Define `
   orders (g:'a monoid) n = {x | x IN G /\ (ord x = n)}
`;

(* Theorem: !x n. x IN orders g n <=> x IN G /\ (ord x = n) *)
(* Proof: by orders_def *)
val orders_element = store_thm(
  "orders_element",
  ``!g:'a monoid. !x n. x IN orders g n <=> x IN G /\ (ord x = n)``,
  rw[orders_def]);

(* Theorem: !n. (orders g n) SUBSET G *)
(* Proof: by orders_def, SUBSET_DEF *)
val orders_subset = store_thm(
  "orders_subset",
  ``!g:'a monoid. !n. (orders g n) SUBSET G``,
  rw[orders_def, SUBSET_DEF]);

(* Theorem: FINITE G ==> !n. FINITE (orders g n) *)
(* Proof: by orders_subset, SUBSET_FINITE *)
val orders_finite = store_thm(
  "orders_finite",
  ``!g:'a monoid. FINITE G ==> !n. FINITE (orders g n)``,
  metis_tac[orders_subset, SUBSET_FINITE]);

(* Theorem: Monoid g ==> (orders g 1 = {#e}) *)
(* Proof:
     orders g 1
   = {x | x IN G /\ (ord x = 1)}    by orders_def
   = {x | x IN G /\ (x = #e)}       by monoid_order_eq_1
   = {#e}                           by monoid_id_elelment
*)
val orders_eq_1 = store_thm(
  "orders_eq_1",
  ``!g:'a monoid. Monoid g ==> (orders g 1 = {#e})``,
  rw[orders_def, EXTENSION, EQ_IMP_THM, GSYM monoid_order_eq_1]);

(* ------------------------------------------------------------------------- *)
(* Maximal Order                                                             *)
(* ------------------------------------------------------------------------- *)

(* Overload maximal_order of a group *)
val _ = overload_on("maximal_order", ``\g:'a monoid. MAX_SET (IMAGE ord G)``);

(* Theorem: maximal_order g = MAX_SET {ord z | z | z IN G} *)
(* Proof: by IN_IMAGE *)
val maximal_order_alt = store_thm(
  "maximal_order_alt",
  ``!g:'a monoid. maximal_order g = MAX_SET {ord z | z | z IN G}``,
  rpt strip_tac >>
  `IMAGE ord G = {ord z | z | z IN G}` by rw[EXTENSION] >>
  rw[]);

(* Theorem: In an Abelian Monoid, every nonzero order divides the maximal order.
            FiniteAbelianMonoid g ==> !x. x IN G /\ 0 < ord x ==> (ord x) divides (maximal_order g) *)
(* Proof:
   Let m = maximal_order g = MAX_SET {ord x | x IN G}
   Choose z IN G so that ord z = m.
   Pick x IN G so that ord x = n. Question: will n divide m ?

   We have: ord x = n, ord z = m  bigger.
   Let d = gcd(n,m), a = n/d, b = m/d.
   Since a | n = ord x, there is ord xa = a
   Since b | m = ord y, there is ord xb = b
   and gcd(a,b) = 1     by FACTOR_OUT_GCD

   If gcd(a,m) <> 1, let prime p divides gcd(a,m)   by PRIME_FACTOR

   Since gcd(a,m) | a  and gcd(a,m) divides m,
   prime p | a, p | m = b * d, a product.
   When prime p divides (b * d), p | b or p | d     by P_EUCLIDES
   But gcd(a,b)=1, they don't share any common factor, so p | a ==> p not divide b.
   If p not divide b, so p | d.
   But d | n, d | m, so p | n and p | m.

   Let  p^i | n  for some max i,   mi = MAX_SET {i | p^i divides n}, p^mi | n ==> n = nq * p^mi
   and  p^j | m  for some max j,   mj = MAX_SET {j | p^j divides m), p^mj | m ==> m = mq * p^mj
   If i <= j,
      ppppp | n     ppppppp | m
   d should picks up all i of the p's, leaving a = n/d with no p, p cannot divide a.
   But p | a, so i > j, but this will derive a contradiction:
      pppppp | n    pppp   | m
   d picks up j of the p's
   Let u = p^i (all prime p in n), v = m/p^j (no prime p)
   u | n, so there is ord x = u = p^i                 u = p^mi
   v | m, so there is ord x = v = m/p^j               v = m/p^mj
   gcd(u,v)=1, since u is pure prime p, v has no prime p (possible gcd = 1, p, p^2, etc.)
   So there is ord z = u * v = p^i * m /p^j = m * p^(i-j) .... > m, a contradiction!

   This case is impossible for the max order suitation.

   So gcd(a,m) = 1, there is ord z = a * m = n * m /d
   But  n * m /d <= m,  since m is maximal
   i.e.        n <= d
   But d | n,  d <= n,
   Hence       n = d = gcd(m,n), apply divides_iff_gcd_fix: n divides m.
*)
val monoid_order_divides_maximal = store_thm(
  "monoid_order_divides_maximal",
  ``!g:'a monoid. FiniteAbelianMonoid g ==>
   !x. x IN G /\ 0 < ord x ==> (ord x) divides (maximal_order g)``,
  rw[FiniteAbelianMonoid_def, AbelianMonoid_def] >>
  qabbrev_tac `s = IMAGE ord G` >>
  qabbrev_tac `m = MAX_SET s` >>
  qabbrev_tac `n = ord x` >>
  `#e IN G /\ (ord #e = 1)` by rw[] >>
  `s <> {}` by metis_tac[IN_IMAGE, MEMBER_NOT_EMPTY] >>
  `FINITE s` by metis_tac[IMAGE_FINITE] >>
  `m IN s /\ !y. y IN s ==> y <= m` by rw[MAX_SET_DEF, Abbr`m`] >>
  `?z. z IN G /\ (ord z = m)` by metis_tac[IN_IMAGE] >>
  `!z. 0 < z <=> z <> 0` by decide_tac >>
  `1 <= m` by metis_tac[in_max_set, IN_IMAGE] >>
  `0 < m` by decide_tac >>
  `?a b. (n = a * gcd n m) /\ (m = b * gcd n m) /\ coprime a b` by metis_tac[FACTOR_OUT_GCD] >>
  qabbrev_tac `d = gcd n m` >>
  `a divides n /\ b divides m` by metis_tac[divides_def, MULT_COMM] >>
  `?xa. xa IN G /\ (ord xa = a)` by metis_tac[monoid_order_divisor] >>
  `?xb. xb IN G /\ (ord xb = b)` by metis_tac[monoid_order_divisor] >>
  Cases_on `coprime a m` >| [
    `?xc. xc IN G /\ (ord xc = a * m)` by metis_tac[monoid_order_common_coprime] >>
    `a * m <= m` by metis_tac[IN_IMAGE] >>
    `n * m = d * (a * m)` by rw_tac arith_ss[] >>
    `n <= d` by metis_tac[LE_MULT_LCANCEL, LE_MULT_RCANCEL] >>
    `d <= n` by metis_tac[GCD_DIVIDES, DIVIDES_MOD_0, DIVIDES_LE] >>
    `n = d` by decide_tac >>
    metis_tac [divides_iff_gcd_fix],
    qabbrev_tac `q = gcd a m` >>
    `?p. prime p /\ p divides q` by rw[PRIME_FACTOR] >>
    `0 < a` by metis_tac[MULT] >>
    `q divides a /\ q divides m` by metis_tac[GCD_DIVIDES, DIVIDES_MOD_0] >>
    `p divides a /\ p divides m` by metis_tac[DIVIDES_TRANS] >>
    `p divides b \/ p divides d` by metis_tac[P_EUCLIDES] >| [
      `p divides 1` by metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR, MULT] >>
      metis_tac[DIVIDES_ONE, NOT_PRIME_1],
      `d divides n` by metis_tac[divides_def] >>
      `p divides n` by metis_tac[DIVIDES_TRANS] >>
      `?i. 0 < i /\ (p ** i) divides n /\ !k. coprime (p ** k) (n DIV p ** i)` by rw[FACTOR_OUT_PRIME] >>
      `?j. 0 < j /\ (p ** j) divides m /\ !k. coprime (p ** k) (m DIV p ** j)` by rw[FACTOR_OUT_PRIME] >>
      Cases_on `i > j` >| [
        qabbrev_tac `u = p ** i` >>
        qabbrev_tac `v = m DIV p ** j` >>
        `0 < p` by metis_tac[PRIME_POS] >>
        `v divides m` by metis_tac[DIVIDES_COFACTOR, EXP_EQ_0] >>
        `?xu. xu IN G /\ (ord xu = u)` by metis_tac[monoid_order_divisor] >>
        `?xv. xv IN G /\ (ord xv = v)` by metis_tac[monoid_order_divisor] >>
        `coprime u v` by rw[Abbr`u`] >>
        `?xz. xz IN G /\ (ord xz = u * v)` by rw[monoid_order_common_coprime] >>
        `m = (p ** j) * v` by metis_tac[DIVIDES_FACTORS, EXP_EQ_0] >>
        `p ** (i - j) * m = p ** (i - j) * (p ** j) * v` by rw_tac arith_ss[] >>
        `j <= i` by decide_tac >>
        `p ** (i - j) * (p ** j) = p ** (i - j + j)` by rw[EXP_ADD] >>
        `_ = p ** i` by rw[SUB_ADD] >>
        `p ** (i - j) * m = u * v` by rw_tac std_ss[Abbr`u`] >>
        `0 < i - j` by decide_tac >>
        `1 < p ** (i - j)` by rw[ONE_LT_EXP, ONE_LT_PRIME] >>
        `m < p ** (i - j) * m` by rw[LT_MULT_RCANCEL] >>
        `m < u * v` by metis_tac[] >>
        `u * v > m` by decide_tac >>
        `u * v <= m` by metis_tac[IN_IMAGE] >>
        metis_tac[NOT_GREATER],
        `i <= j` by decide_tac >>
        `0 < p` by metis_tac[PRIME_POS] >>
        `p ** i <> 0 /\ p ** j <> 0` by metis_tac[EXP_EQ_0] >>
        `n = (p ** i) * (n DIV p ** i)` by metis_tac[DIVIDES_FACTORS] >>
        `m = (p ** j) * (m DIV p ** j)` by metis_tac[DIVIDES_FACTORS] >>
        `p ** (j - i) * (p ** i) = p ** (j - i + i)` by rw[EXP_ADD] >>
        `_ = p ** j` by rw[SUB_ADD] >>
        `m = p ** (j - i) * (p ** i) * (m DIV p ** j)` by rw_tac std_ss[] >>
        `_ = (p ** i) * (p ** (j - i) * (m DIV p ** j))` by rw_tac arith_ss[] >>
        qabbrev_tac `u = p ** i` >>
        qabbrev_tac `v = n DIV u` >>
        `u divides m` by metis_tac[divides_def, MULT_COMM] >>
        `u divides d` by metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR] >>
        `?c. d = c * u` by metis_tac[divides_def] >>
        `n = (a * c) * u` by rw_tac arith_ss[] >>
        `v = c * a` by metis_tac[MULT_RIGHT_CANCEL, MULT_COMM] >>
        `a divides v` by metis_tac[divides_def] >>
        `p divides v` by metis_tac[DIVIDES_TRANS] >>
        `p divides u` by metis_tac[DIVIDES_EXP_BASE, DIVIDES_REFL] >>
        `d <> 0` by metis_tac[MULT_0] >>
        `c <> 0` by metis_tac[MULT] >>
        `v <> 0` by metis_tac[MULT_EQ_0] >>
        `p divides (gcd v u)` by metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR] >>
        `coprime u v` by metis_tac[] >>
        metis_tac[GCD_SYM, DIVIDES_ONE, NOT_PRIME_1]
      ]
    ]
  ]);

(* This is a milestone theorem. *)

(* Another proof based on the following:

The Multiplicative Group of a Finite Field (Ryan Vinroot)
http://www.math.wm.edu/~vinroot/430S13MultFiniteField.pdf

*)

(* Theorem: FiniteAbelianMonoid g ==>
            !x. x IN G /\ 0 < ord x ==> (ord x) divides (maximal_order g) *)
(* Proof:
   Note AbelianMonoid g /\ FINITE G         by FiniteAbelianMonoid_def
   Let ord z = m = maximal_order g, attained by some z IN G.
   Let ord x = n, and n <= m since m is maximal_order, so 0 < m.
   Then x IN G /\ z IN G
    ==> ?y. y IN G /\ ord y = lcm n m       by abelian_monoid_order_lcm
   Note lcm n m <= m                        by m is maximal_order
    but       m <= lcm n m                  by LCM_LE, lcm is a common multiple
    ==> lcm n m = m                         by EQ_LESS_EQ
     or n divides m                         by divides_iff_lcm_fix
*)
Theorem monoid_order_divides_maximal[allow_rebind]:
  !g:'a monoid.
    FiniteAbelianMonoid g ==>
    !x. x IN G /\ 0 < ord x ==> (ord x) divides (maximal_order g)
Proof
  rw[FiniteAbelianMonoid_def] >>
  ‘Monoid g’ by metis_tac[AbelianMonoid_def] >>
  qabbrev_tac ‘s = IMAGE ord G’ >>
  qabbrev_tac ‘m = MAX_SET s’ >>
  qabbrev_tac ‘n = ord x’ >>
  ‘#e IN G /\ (ord #e = 1)’ by rw[] >>
  ‘s <> {}’ by metis_tac[IN_IMAGE, MEMBER_NOT_EMPTY] >>
  ‘FINITE s’ by rw[Abbr‘s’] >>
  ‘m IN s /\ !y. y IN s ==> y <= m’ by rw[MAX_SET_DEF, Abbr‘m’] >>
  ‘?z. z IN G /\ (ord z = m)’ by metis_tac[IN_IMAGE] >>
  ‘?y. y IN G /\ (ord y = lcm n m)’ by metis_tac[abelian_monoid_order_lcm] >>
  ‘n IN s /\ ord y IN s’ by rw[Abbr‘s’, Abbr‘n’] >>
  ‘n <= m /\ lcm n m <= m’ by metis_tac[] >>
  ‘0 < m’ by decide_tac >>
  ‘m <= lcm n m’ by rw[LCM_LE] >>
  rw[divides_iff_lcm_fix]
QED

(* ------------------------------------------------------------------------- *)
(* Monoid Invertibles                                                        *)
(* ------------------------------------------------------------------------- *)

(* The Invertibles are those with inverses. *)
val monoid_invertibles_def = Define`
    monoid_invertibles (g:'a monoid) =
    { x | x IN G /\ (?y. y IN G /\ (x * y = #e) /\ (y * x = #e)) }
`;
val _ = overload_on ("G*", ``monoid_invertibles g``);

(* Theorem: x IN G* <=> x IN G /\ ?y. y IN G /\ (x * y = #e) /\ (y * x = #e) *)
(* Proof: by monoid_invertibles_def. *)
val monoid_invertibles_element = store_thm(
  "monoid_invertibles_element",
  ``!g:'a monoid x. x IN G* <=> x IN G /\ ?y. y IN G /\ (x * y = #e) /\ (y * x = #e)``,
  rw[monoid_invertibles_def]);

(* Theorem: Monoid g /\ x IN G /\ 0 < ord x ==> x IN G*  *)
(* Proof:
   By monoid_invertibles_def, this is to show:
      ?y. y IN G /\ (x * y = #e) /\ (y * x = #e)
   Since x ** (ord x) = #e           by order_property
     and ord x = SUC n               by ord x <> 0
    Now, x ** SUC n = x * x ** n     by monoid_exp_SUC
         x ** SUC n = x ** n * x     by monoid_exp_suc
     and x ** n IN G                 by monoid_exp_element
    Hence taking y = x ** n will satisfy the requirements.
*)
val monoid_order_nonzero = store_thm(
  "monoid_order_nonzero",
  ``!g:'a monoid x. Monoid g /\ x IN G  /\ 0 < ord x ==> x IN G*``,
  rw[monoid_invertibles_def] >>
  `x ** (ord x) = #e` by rw[order_property] >>
  `ord x <> 0` by decide_tac >>
  metis_tac[num_CASES, monoid_exp_SUC, monoid_exp_suc, monoid_exp_element]);

(* The Invertibles of a monoid, will be a Group. *)
val Invertibles_def = Define`
  Invertibles (g:'a monoid) : 'a monoid =
    <| carrier := G*;
            op := g.op;
            id := g.id
     |>
`;
(*
- type_of ``Invertibles g``;
> val it = ``:'a moniod`` : hol_type
*)

(* Theorem: properties of Invertibles *)
(* Proof: by Invertibles_def. *)
val Invertibles_property = store_thm(
  "Invertibles_property",
  ``!g:'a monoid. ((Invertibles g).carrier = G*) /\
                 ((Invertibles g).op = g.op) /\
                 ((Invertibles g).id = #e) /\
                 ((Invertibles g).exp = g.exp)``,
  rw[Invertibles_def, monoid_exp_def, FUN_EQ_THM]);

(* Theorem: (Invertibles g).carrier = monoid_invertibles g *)
(* Proof: by Invertibles_def. *)
val Invertibles_carrier = store_thm(
  "Invertibles_carrier",
  ``!g:'a monoid. (Invertibles g).carrier = monoid_invertibles g``,
  rw[Invertibles_def]);

(* Theorem: (Invertibles g).carrier SUBSET G *)
(* Proof:
    (Invertibles g).carrier
   = G*                         by Invertibles_def
   = {x | x IN G /\ ... }       by monoid_invertibles_def
   SUBSET G                     by SUBSET_DEF
*)
val Invertibles_subset = store_thm(
  "Invertibles_subset",
  ``!g:'a monoid. (Invertibles g).carrier SUBSET G``,
  rw[Invertibles_def, monoid_invertibles_def, SUBSET_DEF]);

(* Theorem: order (Invertibles g) x = order g x *)
(* Proof: order_def, period_def, Invertibles_property *)
val Invertibles_order = store_thm(
  "Invertibles_order",
  ``!g:'a monoid. !x. order (Invertibles g) x = order g x``,
  rw[order_def, period_def, Invertibles_property]);

(* ------------------------------------------------------------------------- *)
(* Monoid Inverse as an operation                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: x IN G* means inverse of x exists. *)
(* Proof: by definition of G*. *)
val monoid_inv_from_invertibles = store_thm(
  "monoid_inv_from_invertibles",
  ``!g:'a monoid. Monoid g ==> !x. x IN G* ==> ?y. y IN G /\ (x * y = #e) /\ (y * x = #e)``,
  rw[monoid_invertibles_def]);

(* Convert this into the form: !g x. ?y. ..... for SKOLEM_THM *)
val lemma = prove(``!(g:'a monoid) x. ?y. Monoid g /\ x IN G* ==> y IN G /\ (x * y = #e) /\ (y * x = #e)``,
  metis_tac[monoid_inv_from_invertibles]);

(* Use Skolemization to generate the monoid_inv_from_invertibles function *)
val monoid_inv_def = new_specification(
  "monoid_inv_def",
  ["monoid_inv"], (* name of function *)
  SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma);
(* > val monoid_inv_def = |- !g x. Monoid g /\ x IN G* ==>
         monoid_inv g x IN G /\ (x * monoid_inv g x = #e) /\ (monoid_inv g x * x = #e) : thm *)

(*
- type_of ``monoid_inv g``;
> val it = ``:'a -> 'a`` : hol_type
*)

(* Convert inv function to inv field, i.e. m.inv is defined to be monoid_inv. *)
val _ = add_record_field ("inv", ``monoid_inv``);
(*
- type_of ``g.inv``;
> val it = ``:'a -> 'a`` : hol_type
*)
(* val _ = overload_on ("|/", ``g.inv``); *) (* for non-unicode input *)

(* for unicode dispaly *)
val _ = add_rule{fixity = Suffix 2100,
                 term_name = "reciprocal",
                 block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                 paren_style = OnlyIfNecessary,
                 pp_elements = [TOK "⁻¹"]};
val _ = overload_on("reciprocal", ``monoid_inv g``);
val _ = overload_on ("|/", ``reciprocal``); (* for non-unicode input *)

(* This means: reciprocal will have the display ⁻¹, and here reciprocal is short-name for monoid_inv g *)

(* - monoid_inv_def;
> val it = |- !g x. Monoid g /\ x IN G* ==> |/ x IN G /\ (x * |/ x = #e) /\ ( |/ x * x = #e) : thm
*)

(* Theorem: x IN G* <=> x IN G /\ |/ x IN G /\ (x * |/ x = #e) /\ ( |/ x * x = #e) *)
(* Proof: by definition. *)
val monoid_inv_def_alt = store_thm(
  "monoid_inv_def_alt",
  ``!g:'a monoid. Monoid g ==> (!x. x IN G* <=> x IN G /\ |/ x IN G /\ (x * |/ x = #e) /\ ( |/ x * x = #e))``,
  rw[monoid_invertibles_def, monoid_inv_def, EQ_IMP_THM] >>
  metis_tac[]);

(* In preparation for: The invertibles of a monoid form a group. *)

(* Theorem: x IN G* ==> x IN G *)
(* Proof: by definition of G*. *)
val monoid_inv_element = store_thm(
  "monoid_inv_element",
  ``!g:'a monoid. Monoid g ==> !x. x IN G* ==> x IN G``,
  rw[monoid_invertibles_def]);

(* This export will cause rewrites of RHS = x IN G to become proving LHS = x IN G*, which is not useful. *)
(* val _ = export_rewrites ["monoid_inv_element"]; *)

(* Theorem: #e IN G* *)
(* Proof: by monoid_id and definition. *)
val monoid_id_invertible = store_thm(
  "monoid_id_invertible",
  ``!g:'a monoid. Monoid g ==> #e IN G*``,
  rw[monoid_invertibles_def] >>
  qexists_tac `#e` >>
  rw[]);

val _ = export_rewrites ["monoid_id_invertible"];

(* This is a direct proof, next one is shorter. *)

(* Theorem: [Closure for Invertibles] x, y IN G* ==> x * y IN G* *)
(* Proof: inverse of (x * y) = (inverse of y) * (inverse of x)
   Note x IN G* ==>
        |/x IN G /\ (x * |/ x = #e) /\ ( |/ x * x = #e)   by monoid_inv_def
        y IN G* ==>
        |/y IN G /\ (y * |/ y = #e) /\ ( |/ y * y = #e)   by monoid_inv_def
    Now x * y IN G and | /y * | / x IN G       by monoid_op_element
    and (x * y) * ( |/ y * |/ x) = #e          by monoid_assoc, monoid_lid
    also ( |/ y * |/ x) * (x * y) = #e         by monoid_assoc, monoid_lid
    Thus x * y IN G*, with ( |/ y * |/ x) as its inverse.
*)
val monoid_inv_op_invertible = store_thm(
  "monoid_inv_op_invertible",
  ``!g:'a monoid. Monoid g ==> !x y. x IN G* /\ y IN G* ==> x * y IN G*``,
  rpt strip_tac>>
  `x IN G /\ y IN G` by rw_tac std_ss[monoid_inv_element] >>
  `|/ x IN G /\ (x * |/ x = #e) /\ ( |/ x * x = #e)` by rw_tac std_ss[monoid_inv_def] >>
  `|/ y IN G /\ (y * |/ y = #e) /\ ( |/ y * y = #e)` by rw_tac std_ss[monoid_inv_def] >>
  `x * y IN G /\ |/ y * |/ x IN G` by rw_tac std_ss[monoid_op_element] >>
  `(x * y) * ( |/ y * |/ x) = x * ((y * |/ y) * |/ x)` by rw_tac std_ss[monoid_assoc, monoid_op_element] >>
  `( |/ y * |/ x) * (x * y) = |/ y * (( |/ x * x) * y)` by rw_tac std_ss[monoid_assoc, monoid_op_element] >>
  rw_tac std_ss[monoid_invertibles_def, GSPECIFICATION] >>
  metis_tac[monoid_lid]);

(* Better proof of the same theorem. *)

(* Theorem: [Closure for Invertibles] x, y IN G* ==> x * y IN G* *)
(* Proof: inverse of (x * y) = (inverse of y) * (inverse of x)  *)
Theorem monoid_inv_op_invertible[allow_rebind,simp]:
  !g:'a monoid. Monoid g ==> !x y. x IN G* /\ y IN G* ==> x * y IN G*
Proof
  rw[monoid_invertibles_def] >>
  qexists_tac `y'' * y'` >>
  rw_tac std_ss[monoid_op_element] >| [
    `x * y * (y'' * y') = x * ((y * y'') * y')` by rw[monoid_assoc],
    `y'' * y' * (x * y) = y'' * ((y' * x) * y)` by rw[monoid_assoc]
  ] >> rw_tac std_ss[monoid_lid]
QED

(* Theorem: x IN G* ==> |/ x IN G* *)
(* Proof: by monoid_inv_def. *)
val monoid_inv_invertible = store_thm(
  "monoid_inv_invertible",
  ``!g:'a monoid. Monoid g ==> !x. x IN G* ==> |/ x IN G*``,
  rpt strip_tac >>
  rw[monoid_invertibles_def] >-
  rw[monoid_inv_def] >>
  metis_tac[monoid_inv_def, monoid_inv_element]);

val _ = export_rewrites ["monoid_inv_invertible"];

(* Theorem: The Invertibles of a monoid form a monoid. *)
(* Proof: by checking definition. *)
val monoid_invertibles_is_monoid = store_thm(
  "monoid_invertibles_is_monoid",
  ``!g. Monoid g ==> Monoid (Invertibles g)``,
  rpt strip_tac >>
  `!x. x IN G* ==> x IN G` by rw[monoid_inv_element] >>
  rw[Invertibles_def] >>
  rewrite_tac[Monoid_def] >>
  rw[monoid_assoc]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
