(* ------------------------------------------------------------------------- *)
(* Short-Weierstrass Curves                                                  *)
(* ------------------------------------------------------------------------- *)
(*
   Documentation

   Mathematical points on y^2 = x^3 + a*x + b over the modern fieldTheory.
   The datatype contains ECInfinity and ECAffine x y; the latter constructor
   alone does not assert field membership or the curve equation.

   Definitions:
     sw_curve_rhs_def          x^3 + a*x + b using the field record operations.
     sw_discriminant_def       -16 * (4*a^3 + 27*b^2).
     ShortWeierstrassCurve_def Field, coefficients in the carrier,
                              characteristic not 2 or 3, nonzero discriminant.
     sw_on_curve_def           Infinity, or carrier coordinates satisfying
                              the equation.
     sw_points_def             The set of points satisfying sw_on_curve.

   Membership rewrites:
     sw_on_curve_ECInfinity, sw_on_curve_ECAffine, sw_points_member.
   Addition and the group theorem are in shortWeierstrassGroup.
*)

Theory shortWeierstrass
Ancestors
  field

Datatype:
  sw_point = ECInfinity | ECAffine 'a 'a
End

(* Arithmetic below uses the field record r. Subtraction expands directly
   to addition of the additive inverse, preserving the underlying terms. *)
Overload "+"[local] = ``(r:'a field).sum.op``
Overload "-"[local] = ``\x y. (r:'a field).sum.op x (r.sum.inv y)``
Overload "*"[local] = ``(r:'a field).prod.op``
Overload "**"[local] = ``(r:'a field).prod.exp``

Definition sw_curve_rhs_def:
  sw_curve_rhs (r:'a field) a b x =
    x ** 3 + a * x + b
End

Definition sw_discriminant_def:
  sw_discriminant (r:'a field) a b =
    r.sum.inv
      ((r.sum.exp r.prod.id 16) *
       ((r.sum.exp r.prod.id 4) * a ** 3 +
        (r.sum.exp r.prod.id 27) * b ** 2))
End

(* Valid curves have a,b in the field, char(F) <> 2,3 and
   Delta = -16*(4*a^3+27*b^2) <> 0.
*)
Definition ShortWeierstrassCurve_def:
  ShortWeierstrassCurve (r:'a field) a b <=>
    Field r /\
    a IN r.carrier /\
    b IN r.carrier /\
    char r <> 2 /\
    char r <> 3 /\
    sw_discriminant r a b <> r.sum.id
End

Definition sw_on_curve_def:
  (sw_on_curve (r:'a field) a b ECInfinity <=> T) /\
  (sw_on_curve r a b (ECAffine x y) <=>
    x IN r.carrier /\
    y IN r.carrier /\
    y ** 2 = sw_curve_rhs r a b x)
End

Definition sw_points_def:
  sw_points (r:'a field) a b = {P | sw_on_curve r a b P}
End

Theorem sw_on_curve_ECInfinity[simp]:
  !(r:'a field) a b. sw_on_curve r a b ECInfinity
Proof
  rw[sw_on_curve_def]
QED

(* (x,y) is on the curve iff x,y are in the field and y^2 = x^3+a*x+b. *)
Theorem sw_on_curve_ECAffine[simp]:
  !(r:'a field) a b x y.
    sw_on_curve r a b (ECAffine x y) <=>
    x IN r.carrier /\
    y IN r.carrier /\
    y ** 2 = sw_curve_rhs r a b x
Proof
  rw[sw_on_curve_def]
QED

Theorem sw_points_member[simp]:
  !(r:'a field) a b P.
    P IN sw_points r a b <=> sw_on_curve r a b P
Proof
  rw[sw_points_def]
QED
