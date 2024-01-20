open HolKernel boolLib bossLib Parse dep_rewrite
open monoidTheory groupTheory ringTheory fieldTheory ffBasicTheory

val _ = new_theory "ellipticCurve";

Datatype:
  curve =
  <| a: 'a
   ; b: 'a
   ; f: 'a ring
   |>
End

Definition EllipticCurve_def:
  EllipticCurve (c:'a curve) <=>
    FiniteField c.f /\ char c.f NOTIN {2; 3} /\
    c.a IN c.f.carrier /\
    c.b IN c.f.carrier
End

Definition curvePoint_def:
  (curvePoint c NONE = T) /\
  (curvePoint c (SOME (x,y)) =
  (x IN c.f.carrier /\
   y IN c.f.carrier /\
   c.f.prod.op y y =
     c.f.sum.op
       (c.f.sum.op (c.f.prod.op (c.f.prod.op x x) x)
         (c.f.prod.op c.a x))
       c.b))
End

Theorem curvePoint_NONE[simp]:
  curvePoint c NONE
Proof
  rw[curvePoint_def]
QED

Definition ec_add_given_slope_def:
  ec_add_given_slope (r :'a ring) (m:'a) px py qx qy =
  let rx = m * m - px - py in
  let ry = qy + m * (rx  - qx) in
    (rx, ry)
End

Definition ec_add_def:
  ec_add a (r:'a ring) p NONE = p /\
  ec_add a r NONE q = q /\
  ec_add a r (SOME (px,py)) (SOME (qx,qy)) =
  if px = qx then
    if py = -qy then NONE
    else
      let px2 = px * px in
      let tpx2 = px2 + px2 + px2 in
      let m = (tpx2 + a) * (r.prod.inv (py + py)) in
        SOME (ec_add_given_slope r m px py qx qy)
  else
    let m = r.prod.op (py - qy)
      (monoid_inv r.prod (px - qx)) in
    SOME (ec_add_given_slope r m px py qx qy)
End

Definition ECGroup_def:
  ECGroup c = <|
    carrier := curvePoint c
  ; op := ec_add c.a c.f
  ; id := NONE
  |>
End

(*
Theorem ec_add_curvePoint:
  Field c.f /\ {c.a; c.b} SUBSET c.f.carrier /\ curvePoint c p /\ curvePoint c q ==>
  curvePoint c (ec_add c.a c.f p q)
Proof
  Cases_on`p` \\ Cases_on`q` \\ rw[ec_add_def]
  \\ qmatch_goalsub_rename_tac`_ _ _ (SOME p) (SOME q)`
  \\ PairCases_on`p` \\ PairCases_on`q`
  \\ simp[ec_add_def]
  \\ Cases_on`p0 = q0 /\ p1 = c.f.sum.inv q1`
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`r.sum`
  \\ Cases_on`p0 = q0` \\ fs[]
  >- (
    simp[ec_add_given_slope_def]
    \\ qmatch_goalsub_abbrev_tac`q023 + c.a`
    \\ cheat )
  \\ simp[ec_add_given_slope_def]
  \\ fs[curvePoint_def]


Theorem Group_ECGroup:
  EllipticCurve c ==> Group (ECGroup c)
Proof
  rw[EllipticCurve_def, group_def_alt]
  Monoid_def
  monoid_invertibles_def
  m``_ ==> Group _``
  m``Group _ <=> _``
*)

val _ = export_theory();
