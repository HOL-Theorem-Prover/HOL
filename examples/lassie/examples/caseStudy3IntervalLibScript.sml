open BasicProvers Defn HolKernel Parse Conv SatisfySimps Tactic monadsyntax
     boolTheory bossLib;

open realTheory arithmeticTheory realLib RealArith;

open LassieLib realTacticsLib logicTacticsLib;

val _ = new_theory "caseStudy3IntervalLib";

val _ = (LassieLib.loadJargon "Reals"; LassieLib.loadJargon "Logic");

Definition min4_def:
min4 a b c d = min a (min b (min c d))
End

Definition max4_def:
  max4 a b c d = max a (max b (max c d))
End

val _ = temp_overload_on("abs",``real$abs``);
val _ = temp_overload_on("max",``real$max``);
val _ = temp_overload_on("min",``real$min``);
(**
  Define validity of an interval, requiring that the lower bound is less than or equal to the upper bound.
  Containement is defined such that if x is contained in the interval, it must lie between the lower and upper bound.
**)
Definition valid_def:
  valid ((lo,hi):(real # real)) = (lo <= hi)
End

Definition contained_def:
  contained (a:real) (lo,hi) = (lo <= a /\ a <= hi)
End

Definition absIntvUpd_def:
absIntvUpd (op:real->real->real) (iv1:real#real) (iv2:real#real) =
(
  min4 (op (FST iv1) (FST iv2))
       (op (FST iv1) (SND iv2))
       (op (SND iv1) (FST iv2))
       (op (SND iv1) (SND iv2)),
  max4 (op (FST iv1) (FST iv2))
       (op (FST iv1) (SND iv2))
       (op (SND iv1) (FST iv2))
       (op (SND iv1) (SND iv2))
)
End

Definition widenInterval_def:
widenInterval (iv:real#real) (v:real) = ((FST iv - v), (SND iv + v))
End

Definition negateInterval_def:
negateInterval (iv:real#real) = ((- SND iv), (- FST iv))
End

Definition invertInterval_def:
  invertInterval (iv:real#real)  = (1 /(SND iv), 1 /(FST iv))
End

Definition addInterval_def:
  addInterval (iv1:real#real) (iv2:real#real) = absIntvUpd (+) iv1 iv2
End

Definition subtractInterval_def:
 subtractInterval (iv1:real#real) (iv2:real#real) = addInterval iv1 (negateInterval iv2)
End

Definition multInterval_def:
  multInterval (iv1:real#real) (iv2:real#real) = absIntvUpd ( * ) iv1 iv2
End

Definition divideInterval_def:
  divideInterval iv1 iv2 = multInterval iv1 (invertInterval iv2)
End

Definition minAbsFun_def:
  minAbsFun iv = min (abs (FST iv)) (abs (SND iv))
End

Theorem contained_implies_valid:
  !(a:real) (iv:real#real).
  contained a iv ==> valid iv
Proof
  LassieLib.nltac `
    introduce variables.
    case split for 'iv'.
    trivial using [contained_def, valid_def, REAL_LE_TRANS].`
QED

Theorem min4_correct:
  ! a b c d.
    let m = min4 a b c d in
      m <= a /\ m <= b /\ m <= c /\ m <= d
Proof
  LassieLib.nltac `
  introduce variables. simplify with [min4_def]. perform a case split.
  try simplify with [REAL_MIN_LE1].
  use transitivity for 'min b (min c d)'.
  simplify with [REAL_MIN_LE1, REAL_MIN_LE2].
  use transitivity for 'min c d'.
  simplify with [REAL_MIN_LE1, REAL_MIN_LE2].`
QED

Theorem max4_correct:
  !a b c d.
    let m = max4 a b c d in
      a <= m /\ b <= m /\ c <= m /\ d <= m
Proof
  LassieLib.nltac `
  introduce variables. simplify with [max4_def]. perform a case split.
  try simplify with [REAL_LE_MAX1].
  use transitivity for 'max b (max c d)'.
  simplify with [REAL_LE_MAX1, REAL_LE_MAX2].
  use transitivity for 'max c d'.
  simplify with [REAL_LE_MAX1, REAL_LE_MAX2].`
QED

Theorem interval_negation_valid:
  ! iv a.
    contained a iv ==> contained (- a) (negateInterval iv)
Proof
  LassieLib.nltac `
  introduce variables. case split for 'iv'.
  simplify with [contained_def, negateInterval_def, REAL_LE_TRANS].`
QED

Theorem iv_neg_preserves_valid:
  !iv.
    valid iv ==> valid (negateInterval iv)
Proof
  LassieLib.nltac `
  introduce variables.
  case split for 'iv'.
  simplify with [valid_def, negateInterval_def].`
QED

(*
gt `! x y. 0 < x /\ 0 < y ==> (inv x <= inv y <=> y <= x)`

proveInteractive();

introduce assumptions
we show 'inv x < inv y <=> y < x' using (use REAL_INV_LT_ANTIMONO THEN follows trivially)
*)
Theorem nonzerop_EQ1_I'[simp]:
  0 < r ==> (nonzerop r = 1)
Proof
  rw[nonzerop_def]
QED

val REAL_LE_IMP_LT = curry save_thm "REAL_LE_IMP_LT" (fst (EQ_IMP_RULE (Drule.SPEC_ALL REAL_LE_LT)));

Theorem REAL_INV_LE_ANTIMONO[local]:
  ! x y.
    0 < x /\ 0 < y ==>
    (inv x <= inv y <=> y <= x)
Proof
  LassieLib.nltac `
    introduce assumptions.
    we show 'inv x < inv y <=> y < x' using (use REAL_INV_LT_ANTIMONO THEN follows trivially).
    case split.
    simplify with [REAL_LE_LT].
    introduce assumptions.
    simplify with [REAL_INV_INJ]. trivial.`
 (* More verbose version using subgoal selectors:
  LassieLib.nltac ‘
    introduce assumptions.
    we show 'inv x < inv y <=> y < x'
      using (use REAL_INV_LT_ANTIMONO then follows trivially).
    case split. introduce assumptions.
    Case 'inv x ≤ inv y'.
      resolve with REAL_LE_IMP_LT.
      Case 'inv x = inv y'. follows from [REAL_INV_INJ]. End.
      Case 'inv x < inv y'. trivial. End.
    Case 'y ≤ x'.
      resolve with REAL_LE_IMP_LT.
      Case 'y = x'. follows from [REAL_INV_INJ]. End.
      Case 'y < x'. trivial. End.’ *)
QED

Theorem interval_inversion_valid:
  ∀ iv a.
    (SND iv < 0 ∨ 0 < FST iv) ∧ contained a iv ⇒
      contained (inv a) (invertInterval iv)
Proof
  LassieLib.nltac ‘
  introduce variables.
  case split for 'iv'.
  simplify with [contained_def, invertInterval_def].
  introduce assumptions.
  rewrite once [<- REAL_INV_1OVER].
  Next Goal.
    rewrite once [ <- REAL_LE_NEG]. we know 'a < 0'. thus 'a <> 0'.
    we know 'r < 0'. thus 'r <> 0'.
    'inv(-a) <= inv (-r) <=> (- r) <= -a' using
      (use REAL_INV_LE_ANTIMONO THEN simplify).
    resolve with REAL_NEG_INV. rewrite assumptions. follows trivially.
  Next Goal.
    rewrite once [<- REAL_LE_NEG].
    we know 'a < 0'. thus 'a <> 0'. we know 'q <> 0'.
    resolve with REAL_NEG_INV.
    'inv (-q) <= inv (-a) <=> (-a) <= (-q)' using
      (use REAL_INV_LE_ANTIMONO THEN simplify THEN trivial).
    rewrite assumptions. follows trivially.
  Next Goal.
    rewrite with [<- REAL_INV_1OVER].
    'inv r <= inv a <=> a <= r' using (use REAL_INV_LE_ANTIMONO THEN trivial).
    follows trivially.
  Next Goal.
    rewrite with [<- REAL_INV_1OVER].
    'inv a <= inv q <=> q <= a' using (use REAL_INV_LE_ANTIMONO THEN trivial).
    follows trivially.’
QED

val _ = export_theory();
