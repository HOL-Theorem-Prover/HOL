Theory RealFieldContext[bare]
Ancestors
  real marker
Libs
  HolKernel Parse boolLib bossLib
  jrhUtils RealArith realSimps

(* ------------------------------------------------------------------------- *)
(* Lemmas RealField.sml formerly proved as it loaded.                        *)
(* ------------------------------------------------------------------------- *)

Theorem REAL_INT_RAT_pth:
  (&x = &x / (&1 :real)) /\
  (~(&x) = ~(&x) / &1) /\
  (unint (&x / &y :real) = &x / &y) /\
  (~unint (&x / &y :real) = ~(&x) / &y)
Proof
  REWRITE_TAC [REAL_OVER1, markerTheory.unint_def] THEN
  REWRITE_TAC [real_div, REAL_MUL_LNEG]
QED

Theorem REAL_RAT_LE_pth:
  &0 < y1 ==> &0 < y2 ==> (x1 / y1 <= x2 / y2 <=> x1 * y2 <= x2 * y1)
Proof REWRITE_TAC [AND_IMP_INTRO, RAT_LEMMA4]
QED

Theorem REAL_RAT_LT_pth:
  &0 < y1 ==> &0 < y2 ==> (x1 / y1 < x2 / y2 <=> x1 * y2 < x2 * y1)
Proof
  REWRITE_TAC [AND_IMP_INTRO] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites
    [GSYM REAL_NOT_LE] THEN
  SIMP_TAC bool_ss [tautLib.TAUT `(~a <=> ~b) <=> (a <=> b)`, RAT_LEMMA4]
QED

Theorem REAL_RAT_EQ_pth:
  &0 < y1 ==> &0 < y2 ==> ((x1 / y1 = x2 / y2) <=> (x1 * y2 = x2 * y1))
Proof REWRITE_TAC [AND_IMP_INTRO, RAT_LEMMA5]
QED

Theorem REAL_RAT_NEG_pth:
  (~(&0) = &0) /\
  (~(~(&n)) = &n) /\
  (~(&m / &n) = ~(&m) / &n) /\
  (~(~(&m) / &n) = &m / &n) /\
  (~(unint (&m / &n :real)) = ~(&m) / &n)
Proof
  REWRITE_TAC [real_div, REAL_INV_NEG, REAL_MUL_LNEG, REAL_NEG_NEG,
    REAL_NEG_0, markerTheory.unint_def]
QED

Theorem REAL_RAT_ABS_pth:
  (abs(&n) = &n) /\
  (abs(~(&n)) = &n) /\
  (abs(&m / &n) = &m / &n) /\
  (abs(~(&m) / &n) = &m / &n) /\
  (abs(unint (&m / &n :real)) = &m / &n) /\
  (abs(~(unint (&m / &n :real))) = &m / &n)
Proof
  REWRITE_TAC [markerTheory.unint_def, REAL_ABS_DIV,
               realaxTheory.REAL_ABS_NEG, realaxTheory.REAL_ABS_NUM]
QED

Theorem REAL_RAT_INV_pth1:
  (inv(&0) = &0) /\
  (inv(&1) = &1) /\
  (inv(~&1) = ~(&1)) /\
  (inv(&1 / &n) = &n) /\
  (inv(~&1 / &n) = ~&n)
Proof
  REWRITE_TAC [REAL_INV_0, REAL_INV_1, REAL_INV_NEG,
               REAL_INV_DIV', REAL_OVER1] THEN
  REWRITE_TAC [real_div, REAL_INV_NEG, REAL_MUL_RNEG, REAL_INV_1,
               REAL_MUL_RID]
QED

Theorem REAL_RAT_INV_pth2:
  (inv(&n) = &1 / &n) /\
  (inv(~(&n)) = ~(&1) / &n) /\
  (inv(&m / &n) = &n / &m) /\
  (inv(~(&m) / &n) = ~(&n) / &m) /\
  (inv(unint (&m / &n :real)) = &n / &m) /\
  (inv(~(unint (&m / &n :real))) = ~(&n) / &m)
Proof
  REWRITE_TAC [markerTheory.unint_def, REAL_INV_DIV'] THEN
  REWRITE_TAC [REAL_INV_NEG, real_div, REAL_MUL_RNEG,
   REAL_MUL_LID, REAL_MUL_LNEG, REAL_INV_MUL', REAL_INV_INV] THEN
  REWRITE_TAC [Once REAL_MUL_COMM]
QED

Theorem REAL_RAT_ADD_pth:
  (&0 :real) < y1 ==> &0 < y2 ==> &0 < y3 ==>
    ((x1 * y2 + x2 * y1) * y3 = x3 * (y1 * y2))
  ==> (x1 / y1 + x2 / y2 = x3 / y3)
Proof
  REPEAT DISCH_TAC THEN
  MP_TAC RAT_LEMMA2 THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC [GSYM REAL_MUL_ASSOC] THEN
  REWRITE_TAC [GSYM REAL_INV_MUL', GSYM real_div] THEN
  Q.SUBGOAL_THEN `&0 < y1 * y2 /\ &0 < y3` MP_TAC THENL [
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC [],
    DISCH_THEN (fn th => ASM_REWRITE_TAC [MATCH_MP RAT_LEMMA5 th])
  ]
QED

Theorem REAL_RAT_SUB_pth:  x - y = x + ~y
Proof REWRITE_TAC [real_sub]
QED

Theorem REAL_RAT_MUL_pth_nocancel:
  (x1 / y1) * (x2 / y2) = (x1 * x2) / (y1 * y2 :real)
Proof
  SIMP_TAC bool_ss [real_div, REAL_INV_MUL',
                    simpLib.AC REAL_MUL_ASSOC REAL_MUL_COMM]
QED

Theorem REAL_RAT_MUL_pth_cancel:
  ~(d1 = (&0 :real)) /\ ~(d2 = &0) /\
  (d1 * u1 = x1) /\ (d2 * u2 = x2) /\
  (d2 * v1 = y1) /\ (d1 * v2 = y2)
  ==> ((x1 / y1) * (x2 / y2) = (u1 * u2) / (v1 * v2))
Proof
  rpt strip_tac >>
  RW_TAC (bool_ss ++ RMULCANON_ss) [real_div, REAL_INV_MUL', nonzerop_def]
QED

Theorem REAL_RAT_DIV_pth:  x / y = x * inv(y)
Proof REWRITE_TAC [real_div]
QED

Theorem REAL_RAT_POW_pth:  (x / y) pow n = (x pow n) / (y pow n)
Proof REWRITE_TAC [REAL_POW_DIV]
QED

Theorem REAL_INTEGRAL:
  (!(x :real). &0 * x = &0) /\
  (!(x :real) y z. (x + y = x + z) <=> (y = z)) /\
  (!(w :real) x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))
Proof
  ONCE_REWRITE_TAC [GSYM REAL_SUB_0] THEN
  REWRITE_TAC [GSYM REAL_ENTIRE] THEN REAL_ARITH_TAC
QED

Theorem REAL_RABINOWITSCH:
  !x y:real. ~(x = y) <=> ?z. (x - y) * z = &1
Proof
  REWRITE_TAC [EQ_IMP_THM] >> rpt strip_tac >>
  FULL_SIMP_TAC std_ss [EQ_IMP_THM, REAL_SUB_REFL, REAL_MUL_LZERO, REAL_10] >>
  irule_at Any REAL_MUL_RINV >> ASM_REWRITE_TAC [REAL_SUB_0]
QED

Theorem REAL_FIELD_pth:
  x pow n <> 0 <=> x <> 0 \/ &n = 0r \/ x pow n <> 0
Proof
  SIMP_TAC bool_ss [REAL_POW_EQ_0, DE_MORGAN_THM, EQ_IMP_THM, DISJ_IMP_THM,
                    REAL_OF_NUM_EQ]
QED
