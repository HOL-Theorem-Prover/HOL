(* ------------------------------------------------------------------------- *)
(* Polynomial Identities Supporting Curve Associativity                      *)
(* ------------------------------------------------------------------------- *)
(*
   Documentation

   Coordinate identities over the existing commutative Ring model used by
   shortWeierstrassGroup. Denominator inverses are explicit variables with
   inverse equations; no field division or curve-group structure is assumed.
   Local arithmetic notation denotes ring_add, ring_mul and ring_pow.

   Main results:
     sw_secant_equations_algebra, sw_tangent_equations_algebra
                                Derive low-degree slope equations.
     sw_assoc_outputs_algebra   Compare the final coordinate formulas.
     sw_assoc_coordinates_algebra
                                Coordinate identity used in associativity.

   Polynomial consequences are discharged by ringLib's ring tactic.
   These lemmas support the group proof; they are not a standalone assertion
   of the group law without its geometric case analysis.
*)

Theory swAssocAlgebra
Ancestors
  ringLib
Libs
  ringLib

open ringLibTheory

Overload "+"[local] = ``ring_add (r:'a Ring)``
Overload "-"[local] = ``ring_sub (r:'a Ring)``
Overload "*"[local] = ``ring_mul (r:'a Ring)``
Overload "**"[local] = ``ring_pow (r:'a Ring)``

val CURVE_RING_TAC =
  ringLib.RING_TAC THEN
  ASM_SIMP_TAC bool_ss
    [RING_0, RING_1, RING_NEG, RING_ADD, RING_SUB, RING_MUL,
     RING_POW, RING_OF_NUM, RING_OF_INT]

fun USING_RING_TAC equations (asl, goal) =
  CURVE_RING_TAC
    (List.filter
       (fn tm => not (is_eq tm) orelse List.exists (aconv tm) equations) asl,
     goal)

Theorem sw_secant_equations_algebra:
  !(r:'a Ring) x1 y1 x2 y2 a b di m.
  EVERY (\x. x IN ring_carrier r) [x1; y1; x2; y2; a; b; di; m] /\
  y1 ** 2 = x1 ** 3 + a * x1 + b /\
  y2 ** 2 = x2 ** 3 + a * x2 + b /\
  (x2 - x1) * di = ring_1 r /\
  m = (y2 - y1) * di ==>
  y2 - y1 = m * (x2 - x1) /\
  m * (y1 + y2) = x1 ** 2 + x1 * x2 + x2 ** 2 + a
Proof
  rpt gen_tac >> REWRITE_TAC[listTheory.EVERY_DEF] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  conj_tac >-
    (qpat_x_assum `y1 ** 2 = _` kall_tac >>
     qpat_x_assum `y2 ** 2 = _` kall_tac >>
     CURVE_RING_TAC) >>
  CURVE_RING_TAC
QED

Theorem sw_tangent_equations_algebra:
  !(r:'a Ring) x y a di m.
  EVERY (\x. x IN ring_carrier r) [x; y; a; di; m] /\
  (ring_of_num r 2 * y) * di = ring_1 r /\
  m = (ring_of_num r 3 * x ** 2 + a) * di ==>
  y - y = m * (x - x) /\
  m * (y + y) = x ** 2 + x * x + x ** 2 + a
Proof
  rpt gen_tac >> REWRITE_TAC[listTheory.EVERY_DEF] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  conj_tac >-
    (POP_ASSUM_LIST
       (MAP_EVERY ASSUME_TAC o List.filter (pred_setSyntax.is_in o concl)) >>
     CURVE_RING_TAC) >>
  CURVE_RING_TAC
QED

Theorem sw_assoc_outputs_algebra:
  !(r:'a Ring) x1 y1 x2 y2 x3 m n ux uy vx vy k l.
  EVERY (\x. x IN ring_carrier r)
    [x1; y1; x2; y2; x3; m; n; ux; uy; vx; vy; k; l] /\
  y2 - y1 = m * (x2 - x1) /\
  ux = m ** 2 - x1 - x2 /\
  uy = m * (x1 - ux) - y1 /\
  vx = n ** 2 - x2 - x3 /\
  vy = n * (x2 - vx) - y2 /\
  k * (vx - x1) = vy - y1 /\
  k - l = m - n /\
  (m - n) * (m + l) = x1 - x3 ==>
  let xl = k ** 2 - x1 - vx;
      xr = l ** 2 - ux - x3
  in xl = xr /\ k * (x1 - xl) - y1 = l * (ux - xr) - uy
Proof
  rpt gen_tac >> REWRITE_TAC[listTheory.EVERY_DEF, LET_THM] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  `k ** 2 - x1 - vx = l ** 2 - ux - x3` by
    USING_RING_TAC
      [``k - l = m - n``, ``(m - n) * (m + l) = x1 - x3``,
       ``ux = m ** 2 - x1 - x2``, ``vx = n ** 2 - x2 - x3``] >>
  `k + n = m + l` by USING_RING_TAC [``k - l = m - n``] >>
  `y1 + y1 = (k + m) * x1 - (k + n) * vx - (m - n) * x2` by
    USING_RING_TAC
      [``y2 - y1 = m * (x2 - x1)``,
       ``vy = n * (x2 - vx) - y2``,
       ``k * (vx - x1) = vy - y1``] >>
  `y1 + y1 = (k + m) * x1 - (m + l) * vx - (m - n) * x2` by
    USING_RING_TAC
      [``y1 + y1 = (k + m) * x1 - (k + n) * vx - (m - n) * x2``,
       ``k + n = m + l``] >>
  `vx - ux = (m - n) * (l - n)` by
    USING_RING_TAC
      [``ux = m ** 2 - x1 - x2``,
       ``vx = n ** 2 - x2 - x3``,
       ``(m - n) * (m + l) = x1 - x3``] >>
  `l ** 2 - ux - x3 = x2 + (m + l) * (l - n)` by
    USING_RING_TAC
      [``ux = m ** 2 - x1 - x2``,
       ``(m - n) * (m + l) = x1 - x3``] >>
  `(m - n) * (x2 - (l ** 2 - ux - x3)) +
   (m + l) * (vx - ux) = ring_0 r` by
    USING_RING_TAC
      [``vx - ux = (m - n) * (l - n)``,
       ``l ** 2 - ux - x3 = x2 + (m + l) * (l - n)``] >>
  `k * (x1 - (l ** 2 - ux - x3)) - y1 -
   (l * (ux - (l ** 2 - ux - x3)) - uy) =
   (m - n) * (x2 - (l ** 2 - ux - x3)) +
   (m + l) * (vx - ux)` by
    USING_RING_TAC
      [``y1 + y1 = (k + m) * x1 - (m + l) * vx - (m - n) * x2``,
       ``uy = m * (x1 - ux) - y1``,
       ``k - l = m - n``] >>
  conj_tac >- ASM_REWRITE_TAC[] >>
  qpat_x_assum `k ** 2 - x1 - vx = l ** 2 - ux - x3`
    (fn th => REWRITE_TAC [th]) >>
  MP_TAC (Q.SPECL
    [`r`, `k * (x1 - (l ** 2 - ux - x3)) - y1`,
     `l * (ux - (l ** 2 - ux - x3)) - uy`] RING_SUB_EQ_0) >>
  ASM_SIMP_TAC bool_ss
    [RING_0, RING_1, RING_NEG, RING_ADD, RING_SUB, RING_MUL,
     RING_POW, RING_OF_NUM, RING_OF_INT] >>
  disch_then MATCH_MP_TAC >>
  REPEAT (FIRST
    [FIRST_ASSUM ACCEPT_TAC, MATCH_MP_TAC RING_SUB, MATCH_MP_TAC RING_MUL,
     MATCH_MP_TAC RING_ADD, MATCH_MP_TAC RING_POW, CONJ_TAC])
QED

(* The secant equations also cover a tangent when the two points coincide.
   Keeping these low-degree equations avoids a single large ideal search over
   all curve equations, intermediate coordinates, and denominator inverses. *)
Theorem sw_assoc_coordinates_algebra:
  !(r:'a Ring) x1 y1 x2 y2 x3 y3 a m n ux uy vx vy k l ia ib.
  EVERY (\x. x IN ring_carrier r)
    [x1; y1; x2; y2; x3; y3; a; m; n; ux; uy; vx; vy; k; l; ia; ib] /\
  y2 - y1 = m * (x2 - x1) /\
  y3 - y2 = n * (x3 - x2) /\
  m * (y1 + y2) = x1 ** 2 + x1 * x2 + x2 ** 2 + a /\
  n * (y2 + y3) = x2 ** 2 + x2 * x3 + x3 ** 2 + a /\
  ux = m ** 2 - x1 - x2 /\
  uy = m * (x1 - ux) - y1 /\
  vx = n ** 2 - x2 - x3 /\
  vy = n * (x2 - vx) - y2 /\
  (vx - x1) * ia = ring_1 r /\
  (x3 - ux) * ib = ring_1 r /\
  k = (vy - y1) * ia /\
  l = (y3 - uy) * ib ==>
  let xl = k ** 2 - x1 - vx;
      xr = l ** 2 - ux - x3
  in xl = xr /\ k * (x1 - xl) - y1 = l * (ux - xr) - uy
Proof
  rpt gen_tac >> REWRITE_TAC[listTheory.EVERY_DEF, LET_THM] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  `k * (vx - x1) = vy - y1` by
    USING_RING_TAC
      [``k = (vy - y1) * ia``, ``(vx - x1) * ia = ring_1 r``] >>
  `l * (x3 - ux) = y3 - uy` by
    USING_RING_TAC
      [``l = (y3 - uy) * ib``, ``(x3 - ux) * ib = ring_1 r``] >>
  `(y2 + y2) * m = (x2 - x1) * m ** 2 +
      (x1 ** 2 + x1 * x2 + x2 ** 2 + a)` by
    USING_RING_TAC
      [``y2 - y1 = m * (x2 - x1)``,
       ``m * (y1 + y2) = x1 ** 2 + x1 * x2 + x2 ** 2 + a``] >>
  `(y2 + y2) * n =
      (x2 ** 2 + x2 * x3 + x3 ** 2 + a) - (x3 - x2) * n ** 2` by
    USING_RING_TAC
      [``y3 - y2 = n * (x3 - x2)``,
       ``n * (y2 + y3) = x2 ** 2 + x2 * x3 + x3 ** 2 + a``] >>
  `(y2 + y2) * (m - n) =
      (x2 - x1) * m ** 2 + (x3 - x2) * n ** 2 +
      (x1 - x3) * (x1 + x2 + x3)` by
    USING_RING_TAC
      [``(y2 + y2) * m = (x2 - x1) * m ** 2 +
           (x1 ** 2 + x1 * x2 + x2 ** 2 + a)``,
       ``(y2 + y2) * n =
           (x2 ** 2 + x2 * x3 + x3 ** 2 + a) -
           (x3 - x2) * n ** 2``] >>
  `(m + l) * (x3 - ux) =
      (y2 + y2) + (m + n) * (x3 - x2)` by
    USING_RING_TAC
      [``l * (x3 - ux) = y3 - uy``,
       ``uy = m * (x1 - ux) - y1``,
       ``y2 - y1 = m * (x2 - x1)``,
       ``y3 - y2 = n * (x3 - x2)``] >>
  `(m - n) * ((y2 + y2) + (m + n) * (x3 - x2)) =
      (x1 - x3) * (x3 - ux)` by
    USING_RING_TAC
      [``(y2 + y2) * (m - n) =
           (x2 - x1) * m ** 2 + (x3 - x2) * n ** 2 +
           (x1 - x3) * (x1 + x2 + x3)``,
       ``ux = m ** 2 - x1 - x2``] >>
  `(m - n) * (m + l) * (x3 - ux) =
      (x1 - x3) * (x3 - ux)` by
    USING_RING_TAC
      [``(m + l) * (x3 - ux) =
           (y2 + y2) + (m + n) * (x3 - x2)``,
       ``(m - n) * ((y2 + y2) + (m + n) * (x3 - x2)) =
           (x1 - x3) * (x3 - ux)``] >>
  `(m - n) * (m + l) = x1 - x3` by
    USING_RING_TAC
      [``(m - n) * (m + l) * (x3 - ux) =
           (x1 - x3) * (x3 - ux)``,
       ``(x3 - ux) * ib = ring_1 r``] >>
  `(k + n) * (vx - x1) =
      (m + n) * (x2 - x1) - (y2 + y2)` by
    USING_RING_TAC
      [``k * (vx - x1) = vy - y1``,
       ``vy = n * (x2 - vx) - y2``,
       ``y2 - y1 = m * (x2 - x1)``] >>
  `(k + n) * (vx - x1) + (m + l) * (x3 - ux) =
      (m + n) * (x3 - x1)` by
    USING_RING_TAC
      [``(k + n) * (vx - x1) =
           (m + n) * (x2 - x1) - (y2 + y2)``,
       ``(m + l) * (x3 - ux) =
           (y2 + y2) + (m + n) * (x3 - x2)``] >>
  `(vx - x1) + (x3 - ux) = (n - m) * (m + n)` by
    USING_RING_TAC
      [``ux = m ** 2 - x1 - x2``,
       ``vx = n ** 2 - x2 - x3``] >>
  `(m + l) * ((vx - x1) + (x3 - ux)) =
      (m + n) * (x3 - x1)` by
    USING_RING_TAC
      [``(vx - x1) + (x3 - ux) = (n - m) * (m + n)``,
       ``(m - n) * (m + l) = x1 - x3``] >>
  `(k - l - (m - n)) * (vx - x1) = ring_0 r` by
    USING_RING_TAC
      [``(k + n) * (vx - x1) + (m + l) * (x3 - ux) =
           (m + n) * (x3 - x1)``,
       ``(m + l) * ((vx - x1) + (x3 - ux)) =
           (m + n) * (x3 - x1)``] >>
  `k - l = m - n` by
    USING_RING_TAC
      [``(k - l - (m - n)) * (vx - x1) = ring_0 r``,
       ``(vx - x1) * ia = ring_1 r``] >>
  MATCH_MP_TAC (BETA_RULE (REWRITE_RULE [LET_THM] (Q.SPECL
    [`r`, `x1`, `y1`, `x2`, `y2`, `x3`, `m`, `n`,
     `ux`, `uy`, `vx`, `vy`, `k`, `l`] sw_assoc_outputs_algebra))) >>
  ASM_SIMP_TAC bool_ss [listTheory.EVERY_DEF]
QED
