open HolKernel boolLib boolSimps bossLib Parse dep_rewrite
open arithmeticTheory monoidTheory groupTheory ringTheory fieldTheory ffBasicTheory

val _ = new_theory "ellipticCurve";

Datatype:
  weierstrass_curve =
  <| a: 'a
   ; b: 'a
   ; f: 'a ring
   |>
End

Definition WeierstrassEllipticCurve_def:
  WeierstrassEllipticCurve (c:'a weierstrass_curve) <=>
    FiniteField c.f /\ char c.f NOTIN {2; 3} /\
    c.a IN c.f.carrier /\
    c.b IN c.f.carrier
End

Definition weierstrassPoint_def:
  (weierstrassPoint c NONE = T) /\
  (weierstrassPoint c (SOME (x,y)) =
  (x IN c.f.carrier /\
   y IN c.f.carrier /\
   c.f.prod.exp y 2 =
     c.f.sum.op
       (c.f.sum.op (c.f.prod.exp x 3)
         (c.f.prod.op c.a x))
       c.b))
End

Theorem weierstrassPoint_NONE[simp]:
  weierstrassPoint c NONE
Proof
  rw[weierstrassPoint_def]
QED

Definition wec_add_given_slope_def:
  wec_add_given_slope (r :'a ring) (m:'a) px py qx =
  let rx = m ** 2 - px - qx in
  let ry = m * (px - rx) - py in
    (rx, ry)
End

Definition wec_add_def:
  wec_add a (r:'a ring) p NONE = p /\
  wec_add a r NONE q = q /\
  wec_add a r (SOME (px,py)) (SOME (qx,qy)) =
  if px = qx then
    if py = qy /\ py <> #0 then
      let m = (##3 * (px ** 2) + a) / (##2 * py) in
        SOME (wec_add_given_slope r m px py qx)
    else NONE
  else
    let m = (py - qy) / (px - qx) in
    SOME (wec_add_given_slope r m px py qx)
End

Definition WECGroup_def:
  WECGroup c = <|
    carrier := weierstrassPoint c
  ; op := wec_add c.a c.f
  ; id := NONE
  |>
End

(*
Theorem ec_add_curvePoint:
  Field c.f /\ {c.a; c.b} SUBSET c.f.carrier /\ curvePoint c p /\ curvePoint c q ==>
  curvePoint c (ec_add c.a c.f p q)
Proof
  Cases_on`p` \\ Cases_on`q` \\ rw[wec_add_def]
  \\ qmatch_goalsub_rename_tac`_ _ _ (SOME p) (SOME q)`
  \\ PairCases_on`p` \\ PairCases_on`q`
  \\ simp[wec_add_def]
  \\ Cases_on`p0 = q0 /\ p1 <> q1` >- simp[]
  \\ qmatch_goalsub_abbrev_tac`r.sum`
  \\ `p0 IN R /\ p1 IN R /\ q0 IN R /\ q1 IN R` by fs[weierstrassPoint_def]
  \\ qmatch_goalsub_abbrev_tac`q023 + c.a`
  \\ qmatch_goalsub_abbrev_tac`(q023 + _) * _.inv p12`
  \\ `q023 IN R` by simp[Abbr`q023`]
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
