Theory hyper_trig
Ancestors
  combin pair pred_set list
  arithmetic real iterate real_sigma
  real_topology metric seq derivative lim powser transc
Libs
  simpLib realLib

open Diff;

val _ = augment_srw_ss [realSimps.REAL_ARITH_ss];

(*** Something That Doesn't Belong ***)

(* This should be moved to boolScript, after SELECT_UNIQUE *)
Theorem SELECT_UNIQUE_ALT:
    ∀P x. P x ∧ (∀y. P y ⇒ y = x) ⇒ $@ P = x
Proof
    metis_tac[SELECT_UNIQUE]
QED

(*** Hyperbolic Trig Definitions ***)

Definition sinh_def:
    sinh x = (exp x - exp (-x)) / 2r
End

Definition cosh_def:
    cosh x = (exp x + exp (-x)) / 2r
End

Definition tanh_def:
    tanh x = sinh x / cosh x
End

Definition sech_def:
    sech x = 1 / cosh x
End

Definition csch_def:
    csch x = 1 / sinh x
End

Definition coth_def:
    coth x = 1 / tanh x
End

Theorem tanh_alt:
    ∀x. tanh x = (exp x - exp (-x)) / (exp x + exp (-x))
Proof
    rw[tanh_def,sinh_def,cosh_def]
QED

Theorem tanh_alt2:
    ∀x. tanh x = (exp (2 * x) - 1) / (exp (2 * x) + 1)
Proof
    rw[tanh_alt] >>
    ‘0 < exp x + exp (-x)’ by simp[REAL_LT_ADD,EXP_POS_LT] >>
    ‘0 < exp (2 * x) + 1’ by simp[REAL_LT_ADD,EXP_POS_LT] >>
    simp[REAL_ADD_LDISTRIB,REAL_SUB_LDISTRIB,
        real_sub,REAL_NEG_ADD,GSYM REAL_EXP_ADD] >>
    ‘-x + 2 * x = x’ by simp[] >> pop_assum SUBST1_TAC >> simp[]
QED

Theorem coth_alt:
    ∀x. coth x = cosh x / sinh x
Proof
    rw[coth_def,tanh_def]
QED

(*** Hyperbolic Trig Zero Lemmas ***)

Theorem SINH_POS_LT:
    ∀x. 0 < x ⇒ 0 < sinh x
Proof
    simp[sinh_def,REAL_SUB_LT,EXP_MONO_LT]
QED

Theorem SINH_POS_LE:
    ∀x. 0 ≤ x ⇒ 0 ≤ sinh x
Proof
    simp[sinh_def,REAL_SUB_LE,EXP_MONO_LE]
QED

Theorem SINH_NEG_LT:
    ∀x. x < 0 ⇒ sinh x < 0
Proof
    simp[sinh_def,REAL_LT_SUB_RADD,EXP_MONO_LT]
QED

Theorem SINH_NEG_LE:
    ∀x. x ≤ 0 ⇒ sinh x ≤ 0
Proof
    simp[sinh_def,REAL_LE_SUB_RADD,EXP_MONO_LE]
QED

Theorem SINH_NZ:
    ∀x. sinh x ≠ 0 ⇔ x ≠ 0
Proof
    strip_tac >> simp[EQ_IMP_THM,sinh_def] >>
    CONV_TAC CONTRAPOS_CONV >> rw[] >>
    wlog_tac ‘0 < x’ [‘x’]
    >- (first_x_assum $ qspec_then ‘-x’ mp_tac >> simp[]) >>
    ‘-x < 0’ by simp[] >> ‘-x < x’ by simp[] >>
    dxrule EXP_MONO_IMP >> simp[]
QED

Theorem SINH_0:
    sinh 0 = 0
Proof
    simp[sinh_def,EXP_0]
QED

Theorem COSH_NZ:
    ∀x. cosh x ≠ 0
Proof
    simp[cosh_def,REAL_POS_NZ,REAL_LT_ADD,EXP_POS_LT]
QED

Theorem COSH_POS_LT:
    ∀x. 0 < cosh x
Proof
    simp[cosh_def,REAL_LT_ADD,EXP_POS_LT]
QED

Theorem COSH_0:
    cosh 0 = 1
Proof
    simp[cosh_def,EXP_0]
QED

Theorem TANH_NZ:
    ∀x. tanh x ≠ 0 ⇔ x ≠ 0
Proof
    simp[tanh_def,COSH_NZ] >> metis_tac[SINH_NZ]
QED

Theorem TANH_POS_LT:
    ∀x. 0 < x ⇒ 0 < tanh x
Proof
    simp[tanh_def,COSH_POS_LT,COSH_NZ,SINH_POS_LT]
QED

Theorem TANH_POS_LE:
    ∀x. 0 ≤ x ⇒ 0 ≤ tanh x
Proof
    simp[tanh_def,COSH_POS_LT,COSH_NZ,SINH_POS_LE]
QED

Theorem TANH_NEG_LT:
    ∀x. x < 0 ⇒ tanh x < 0
Proof
    simp[tanh_def,COSH_POS_LT,COSH_NZ,SINH_NEG_LT]
QED

Theorem TANH_NEG_LE:
    ∀x. x ≤ 0 ⇒ tanh x ≤ 0
Proof
    simp[tanh_def,COSH_POS_LT,COSH_NZ,SINH_NEG_LE]
QED

Theorem TANH_0:
    tanh 0 = 0
Proof
    simp[tanh_def,COSH_0,SINH_0]
QED

Theorem SECH_NZ:
    ∀x. sech x ≠ 0
Proof
    simp[sech_def,COSH_NZ]
QED

Theorem SECH_POS_LT:
    ∀x. 0 < sech x
Proof
    simp[sech_def,COSH_POS_LT,COSH_NZ]
QED

Theorem SECH_0:
    sech 0 = 1
Proof
    simp[sech_def,COSH_0]
QED

Theorem CSCH_NZ:
    ∀x. x ≠ 0 ⇒ csch x ≠ 0
Proof
    simp[csch_def,SINH_NZ]
QED

Theorem CSCH_0:
    csch 0 = 0
Proof
    simp[csch_def,SINH_0,GSYM REAL_INV_1OVER,REAL_INV_0]
QED

Theorem CSCH_POS_LT:
    ∀x. 0 < x ⇒ 0 < csch x
Proof
    simp[csch_def,SINH_POS_LT,SINH_NZ]
QED

Theorem CSCH_NEG_LT:
    ∀x. x < 0 ⇒ csch x < 0
Proof
    simp[csch_def,SINH_NEG_LT,SINH_NZ]
QED

Theorem COTH_NZ:
    ∀x. x ≠ 0 ⇒ coth x ≠ 0
Proof
    simp[coth_def,TANH_NZ]
QED

Theorem COTH_POS_LT:
    ∀x. 0 < x ⇒ 0 < coth x
Proof
    simp[coth_def,TANH_POS_LT,TANH_NZ]
QED

Theorem COTH_NEG_LT:
    ∀x. x < 0 ⇒ coth x < 0
Proof
    simp[coth_def,TANH_NEG_LT,TANH_NZ]
QED

(*** Hyperbolic Trig Negative Inputs ***)

Theorem SINH_NEG:
    ∀x. sinh (-x) = -sinh x
Proof
    simp[sinh_def]
QED

Theorem COSH_NEG:
    ∀x. cosh (-x) = cosh x
Proof
    simp[cosh_def]
QED

Theorem TANH_NEG:
    ∀x. tanh (-x) = -tanh x
Proof
    simp[tanh_def,SINH_NEG,COSH_NEG]
QED

Theorem SECH_NEG:
    ∀x. sech (-x) = sech x
Proof
    simp[sech_def,COSH_NEG]
QED

Theorem CSCH_NEG:
    ∀x. csch (-x) = -csch x
Proof
    simp[csch_def,SINH_NEG,neg_rat]
QED

Theorem COTH_NEG:
    ∀x. coth (-x) = -coth x
Proof
    simp[coth_def,TANH_NEG,neg_rat]
QED

(*** Hyperbolic Trig Derivatives ***)

Theorem DIFF_SINH:
    ∀x. (sinh diffl cosh x) x
Proof
    rw[] >> mp_tac $ DIFF_CONV “λx. (exp x - exp (-x)) / 2r” >>
    simp[GSYM sinh_def,cosh_def,ETA_THM] >>
    disch_then $ qspec_then ‘x’ mp_tac >>
    qmatch_abbrev_tac ‘(_ diffl l1) _ ⇒ (_ diffl l2) _’ >>
    ‘l1 = l2’ suffices_by simp[] >> UNABBREV_ALL_TAC >> simp[]
QED

Theorem DIFF_COSH:
    ∀x. (cosh diffl sinh x) x
Proof
    rw[] >> mp_tac $ DIFF_CONV “λx. (exp x + exp (-x)) / 2r” >>
    simp[GSYM cosh_def,sinh_def,ETA_THM] >>
    disch_then $ qspec_then ‘x’ mp_tac >>
    qmatch_abbrev_tac ‘(_ diffl l1) _ ⇒ (_ diffl l2) _’ >>
    ‘l1 = l2’ suffices_by simp[] >> UNABBREV_ALL_TAC >> simp[]
QED

Theorem DIFF_TANH:
    ∀x. (tanh diffl (1 - (tanh x)²)) x
Proof
    rw[] >> mp_tac $ DIFF_CONV “λx. (exp x - exp (-x)) / (exp x + exp (-x))” >>
    simp[GSYM tanh_alt,ETA_THM] >> disch_then $ qspec_then ‘x’ mp_tac >>
    ‘0 < (exp x + exp (-x))’ by (irule REAL_LT_ADD >> simp[EXP_POS_LT]) >>
    simp[REAL_POS_NZ] >> qmatch_abbrev_tac ‘(_ diffl l1) _ ⇒ (_ diffl l2) _’ >>
    ‘l1 = l2’ suffices_by simp[] >> UNABBREV_ALL_TAC >> simp[tanh_alt] >>
    ‘(exp x + exp (-x))² / (exp x + exp (-x))² = 1’ by (
        irule REAL_DIV_REFL >> simp[]) >>
    pop_assum (SUBST1_TAC o SYM) >> simp[REAL_DIV_SUB,REAL_SUB_RNEG,GSYM real_sub]
QED

Theorem DIFF_SECH:
    ∀x. (sech diffl -(tanh x * sech x)) x
Proof
    rw[] >> mp_tac $ DIFF_CONV “λx. 1 / cosh x” >>
    simp[GSYM sech_def,ETA_THM] >>
    disch_then $ qspecl_then [‘sinh x’,‘x’] mp_tac >>
    simp[DIFF_COSH] >> impl_tac
    >- simp[cosh_def,REAL_POS_NZ,REAL_LT_ADD,EXP_POS_LT] >>
    qmatch_abbrev_tac ‘(_ diffl l1) _ ⇒ (_ diffl l2) _’ >>
    ‘l1 = l2’ suffices_by simp[] >> UNABBREV_ALL_TAC >>
    simp[sech_def,tanh_def]
QED

Theorem DIFF_CSCH:
    ∀x. x ≠ 0 ⇒ (csch diffl -(coth x * csch x)) x
Proof
    rw[] >> mp_tac $ DIFF_CONV “λx. 1 / sinh x” >>
    simp[GSYM csch_def,ETA_THM] >>
    disch_then $ qspecl_then [‘cosh x’,‘x’] mp_tac >>
    simp[DIFF_SINH] >> ‘sinh x ≠ 0’ by simp[SINH_NZ] >>
    simp[] >> qmatch_abbrev_tac ‘(_ diffl l1) _ ⇒ (_ diffl l2) _’ >>
    ‘l1 = l2’ suffices_by simp[] >> UNABBREV_ALL_TAC >>
    simp[csch_def,coth_def,tanh_def]
QED

Theorem DIFF_COTH:
    ∀x. x ≠ 0 ⇒ (coth diffl (1 - (coth x)²)) x
Proof
    rw[] >> mp_tac $ DIFF_CONV “λx. 1 / tanh x” >>
    simp[GSYM coth_def,ETA_THM] >>
    disch_then $ qspecl_then [‘1 - (tanh x)²’,‘x’] mp_tac >>
    simp[DIFF_TANH] >> ‘tanh x ≠ 0’ by simp[TANH_NZ] >>
    simp[] >> qmatch_abbrev_tac ‘(_ diffl l1) _ ⇒ (_ diffl l2) _’ >>
    ‘l1 = l2’ suffices_by simp[] >> UNABBREV_ALL_TAC >>
    simp[coth_def,REAL_SUB_LDISTRIB]
QED

(*** Hyperbolic Trig Bounds ***)

Theorem COSH_BOUNDS:
    ∀x. 1 ≤ cosh x
Proof
    rw[] >> Cases_on ‘x = 0’ >- simp[COSH_0] >> wlog_tac ‘0 < x’ [‘x’]
    >- (first_x_assum $ qspec_then ‘-x’ mp_tac >> simp[COSH_NEG]) >>
    qspecl_then [‘cosh’,‘0’,‘x’] mp_tac MVT >> impl_tac
    >- (assume_tac DIFF_COSH >> metis_tac[DIFF_CONT,differentiable]) >>
    simp[COSH_0,REAL_EQ_SUB_RADD] >> rw[] >> simp[] >>
    irule REAL_LE_MUL >> simp[] >>
    dxrule_then (qspec_then ‘sinh z’ mp_tac) DIFF_UNIQ >>
    simp[DIFF_COSH,SINH_POS_LE]
QED

Theorem TANH_BOUNDS:
    ∀x. -1 < tanh x ∧ tanh x < 1
Proof
    strip_tac >> wlog_tac ‘0 ≤ x’ [‘x’]
    >- (first_x_assum $ qspec_then ‘-x’ mp_tac >> simp[TANH_NEG]) >>
    irule_at (Pos hd) REAL_LTE_TRANS >> qexists ‘0’ >>
    simp[tanh_def,COSH_POS_LT,COSH_NZ,SINH_POS_LE] >>
    simp[sinh_def,cosh_def,real_sub] >>
    irule REAL_LT_TRANS >> qexists ‘0’ >> simp[EXP_POS_LT]
QED

Theorem SECH_BOUNDS:
    ∀x. 0 < sech x ∧ sech x ≤ 1
Proof
    simp[sech_def,COSH_POS_LT,COSH_NZ,COSH_BOUNDS]
QED

Theorem CSCH_BOUNDS:
    ∀x. x ≠ 0 ⇒ csch x ≠ 0
Proof
    simp[csch_def,SINH_NZ]
QED

Theorem COTH_BOUNDS:
    ∀x. x ≠ 0 ⇒ coth x < -1 ∨ 1 < coth x
Proof
    rw[coth_def] >> qspec_then ‘x’ assume_tac TANH_BOUNDS >>
    ‘tanh x = 0 ∨ tanh x < 0 ∨ 0 < tanh x’ by simp[]
    >- metis_tac[TANH_NZ] >>
    gs[]
QED

(*** Hyperbolic Trig Monotonicity ***)

Theorem SINH_MONO_LT:
    ∀x y. x < y ⇒ sinh x < sinh y
Proof
    rw[] >> irule DIFF_POS_MONO_LT_UU >> simp[] >>
    rw[] >> qexists ‘cosh z’ >> simp[COSH_POS_LT,DIFF_SINH]
QED

Theorem SINH_MONO_LE:
    ∀x y. x ≤ y ⇒ sinh x ≤ sinh y
Proof
    rw[] >> Cases_on ‘x = y’ >> gs[REAL_LE_LT,SINH_MONO_LT]
QED

Theorem COSH_MONO_LT:
    ∀x y. 0 ≤ x ∧ x < y ⇒ cosh x < cosh y
Proof
    rw[] >> irule DIFF_POS_MONO_LT_CU >> simp[] >>
    qexists ‘0’ >> simp[] >> reverse conj_tac
    >- (metis_tac[DIFF_COSH,DIFF_CONT]) >>
    rw[] >> qexists ‘sinh z’ >> simp[SINH_POS_LT,DIFF_COSH]
QED

Theorem COSH_MONO_LE:
    ∀x y. 0 ≤ x ∧ x ≤ y ⇒ cosh x ≤ cosh y
Proof
    rw[] >> Cases_on ‘x = y’ >> gs[REAL_LE_LT,COSH_MONO_LT]
QED

Theorem COSH_ANTIMONO_LT:
    ∀x y. x < y ∧ y ≤ 0 ⇒ cosh y < cosh x
Proof
    rw[] >> irule DIFF_NEG_ANTIMONO_LT_UC >> simp[] >>
    qexists ‘0’ >> simp[] >> reverse conj_tac
    >- (metis_tac[DIFF_COSH,DIFF_CONT]) >>
    rw[] >> qexists ‘sinh z’ >> simp[SINH_NEG_LT,DIFF_COSH]
QED

Theorem COSH_ANTIMONO_LE:
    ∀x y. x ≤ y ∧ y ≤ 0 ⇒ cosh y ≤ cosh x
Proof
    rw[] >> Cases_on ‘x = y’ >> gs[REAL_LE_LT,COSH_ANTIMONO_LT]
QED

Theorem TANH_MONO_LT:
    ∀x y. x < y ⇒ tanh x < tanh y
Proof
    rw[] >> irule DIFF_POS_MONO_LT_UU >> simp[] >>
    rw[] >> qexists ‘1 - (tanh z)²’ >> simp[DIFF_TANH,REAL_SUB_LT] >>
    wlog_tac ‘0 ≤ z’ [‘z’]
    >- (first_x_assum $ qspec_then ‘-z’ mp_tac >> simp[TANH_NEG]) >>
    qspecl_then [‘1’,‘tanh z’,‘1’] mp_tac POW_LT >>
    simp[] >> disch_then irule >> simp[TANH_BOUNDS,TANH_POS_LE]
QED

Theorem TANH_MONO_LE:
    ∀x y. x ≤ y ⇒ tanh x ≤ tanh y
Proof
    rw[] >> Cases_on ‘x = y’ >> gs[REAL_LE_LT,TANH_MONO_LT]
QED

Theorem SECH_ANTIMONO_LT:
    ∀x y. 0 ≤ x ∧ x < y ⇒ sech y < sech x
Proof
    rw[] >> irule DIFF_NEG_ANTIMONO_LT_CU >> simp[] >>
    qexists ‘0’ >> simp[] >> reverse conj_tac
    >- (metis_tac[DIFF_SECH,DIFF_CONT]) >>
    rw[] >> qexists ‘-(tanh z * sech z)’ >> simp[DIFF_SECH] >>
    irule REAL_LT_MUL >> simp[SECH_POS_LT,TANH_POS_LT]
QED

Theorem SECH_ANTIMONO_LE:
    ∀x y. 0 ≤ x ∧ x ≤ y ⇒ sech y ≤ sech x
Proof
    rw[] >> Cases_on ‘x = y’ >> gs[REAL_LE_LT,SECH_ANTIMONO_LT]
QED

Theorem SECH_MONO_LT:
    ∀x y. x < y ∧ y ≤ 0 ⇒ sech x < sech y
Proof
    rw[] >> irule DIFF_POS_MONO_LT_UC >> simp[] >>
    qexists ‘0’ >> simp[] >> reverse conj_tac
    >- (metis_tac[DIFF_SECH,DIFF_CONT]) >>
    rw[] >> qexists ‘-(tanh z * sech z)’ >> simp[DIFF_SECH] >>
    ‘0 < sech z ∧ tanh z < 0’ by simp[SECH_POS_LT,TANH_NEG_LT] >>
    dxrule_all_then mp_tac REAL_LT_RMUL_IMP >> simp[]
QED

Theorem SECH_MONO_LE:
    ∀x y. x < y ∧ y ≤ 0 ⇒ sech x < sech y
Proof
    rw[] >> Cases_on ‘x = y’ >> gs[REAL_LE_LT,SECH_MONO_LT]
QED

Theorem CSCH_ANTIMONO_LT:
    ∀x y. (y < 0 ∨ 0 < x) ∧ x < y ⇒ csch y < csch x
Proof
    ntac 2 strip_tac >> wlog_tac ‘0 < x’ [‘x’,‘y’]
    >- (simp[] >> rw[] >>
        first_x_assum $ qspecl_then [‘-y’,‘-x’] mp_tac >> simp[CSCH_NEG]) >>
    simp[] >> rw[] >> irule DIFF_NEG_ANTIMONO_LT_OU >> simp[] >>
    qexists ‘0’ >> simp[] >> rw[] >> qexists ‘-(coth z * csch z)’ >>
    simp[DIFF_CSCH] >> irule REAL_LT_MUL >> simp[COTH_POS_LT,CSCH_POS_LT]
QED

Theorem CSCH_ANTIMONO_LE:
    ∀x y. (y < 0 ∨ 0 < x) ∧ x ≤ y ⇒ csch y ≤ csch x
Proof
    rw[] >> Cases_on ‘x = y’ >> gs[REAL_LE_LT,CSCH_ANTIMONO_LT]
QED

Theorem COTH_ANTIMONO_LT:
    ∀x y. (y < 0 ∨ 0 < x) ∧ x < y ⇒ coth y < coth x
Proof
    ntac 2 strip_tac >> wlog_tac ‘0 < x’ [‘x’,‘y’]
    >- (simp[] >> rw[] >>
        first_x_assum $ qspecl_then [‘-y’,‘-x’] mp_tac >> simp[COTH_NEG]) >>
    simp[] >> rw[] >> irule DIFF_NEG_ANTIMONO_LT_OU >> simp[] >>
    qexists ‘0’ >> simp[] >> rw[] >> qexists ‘1 − (coth z)²’ >>
    simp[DIFF_COTH,REAL_LT_SUB_RADD] >>
    qspecl_then [‘1’,‘1’,‘coth z’] mp_tac POW_LT >>
    simp[] >> disch_then irule >> qspec_then ‘z’ mp_tac COTH_BOUNDS >> rw[] >>
    ‘0 < coth z’ by simp[COTH_POS_LT] >> dxrule_all REAL_LT_TRANS >> simp[]
QED

Theorem COTH_ANTIMONO_LE:
    ∀x y. (y < 0 ∨ 0 < x) ∧ x ≤ y ⇒ coth y ≤ coth x
Proof
    rw[] >> Cases_on ‘x = y’ >> gs[REAL_LE_LT,COTH_ANTIMONO_LT]
QED

(*** Hyperbolic Trig Pythagorean-likes ***)

Theorem COSH_SQ_SINH_SQ:
    ∀x. (cosh x)² - (sinh x)² = 1
Proof
    rw[cosh_def,sinh_def,REAL_DIV_SUB] >>
    simp[ADD_POW_2,SUB_POW_2,EXP_NEG_MUL,real_sub,REAL_NEG_ADD]
QED

Theorem SECH_SQ_TANH_SQ:
    ∀x. (sech x)² + (tanh x)² = 1
Proof
    simp[sech_def,tanh_def,REAL_DIV_ADD,POW_NZ,COSH_NZ] >>
    simp[SRULE [REAL_EQ_SUB_RADD] COSH_SQ_SINH_SQ]
QED

Theorem COTH_SQ_CSCH_SQ:
    ∀x. x ≠ 0 ⇒ (coth x)² - (csch x)² = 1
Proof
    simp[coth_alt,csch_def,REAL_DIV_SUB,POW_NZ,SINH_NZ] >>
    simp[SRULE [REAL_EQ_SUB_RADD] COSH_SQ_SINH_SQ]
QED

(*** Inverse Hyperbolic Trig Definitions ***)

Definition asinh_def:
    asinh y = @x. sinh x = y
End

Definition acosh_def:
    acosh y = @x. 0 ≤ x ∧ cosh x = y
End

Definition atanh_def:
    atanh y = @x. tanh x = y
End

Definition asech_def:
    asech y = @x. 0 ≤ x ∧ sech x = y
End

Definition acsch_def:
    acsch y = @x. x ≠ 0 ∧ csch x = y
End

Definition acoth_def:
    acoth y = @x. x ≠ 0 ∧ coth x = y
End

(*** Inverse Hyperbolic Trig Witnesses, Inversions, and Zero Lemmas ***)

Theorem ASINH_WITNESS[local]:
    ∀y. sinh (ln (y + sqrt (y² + 1))) = y
Proof
    rw[] >> simp[sinh_def] >> qabbrev_tac ‘z = (y + sqrt (y² + 1))’ >>
    ‘0 < z’ by (simp[Abbr ‘z’] >> irule ABS_BOUND >>
        simp[] >> irule REAL_LET_TRANS >> irule_at Any SQRT_MONO_LT >>
        qexists ‘y²’ >> simp[SQRT_POW_2_ABS]) >>
    simp[GSYM LN_INV,iffRL EXP_LN,REAL_INV_1OVER] >>
    irule REAL_EQ_LMUL_IMP >> qexists ‘z’ >>
    simp[REAL_SUB_LDISTRIB,Excl "REAL_EQ_LMUL",Excl "RMUL_EQNORM1",Excl "RMUL_EQNORM2"] >>
    qunabbrev_tac ‘z’ >> simp[ADD_POW_2,REAL_ADD_LDISTRIB] >>
    ‘0 ≤ y² + 1’ by simp[REAL_LE_ADD] >> simp[SQRT_POW_2]
QED

Theorem ASINH_UNIQUE[local]:
    ∀x y z. sinh x = y ∧ sinh z = y ⇒ x = z
Proof
    simp[] >> rpt gen_tac >> CONV_TAC CONTRAPOS_CONV >>
    rw[] >> wlog_tac ‘x < z’ [‘x’,‘z’]
    >- (first_x_assum $ irule o GSYM >> simp[]) >>
    dxrule_then mp_tac SINH_MONO_LT >> simp[]
QED

Theorem ASINH_SINH:
    ∀x. asinh (sinh x) = x
Proof
    rw[asinh_def] >> irule SELECT_UNIQUE_ALT >> simp[ASINH_UNIQUE]
QED

Theorem SINH_ASINH:
    ∀x. sinh (asinh x) = x
Proof
    rw[asinh_def] >> SELECT_ELIM_TAC >>
    simp[ASINH_UNIQUE] >> metis_tac[ASINH_WITNESS]
QED

Theorem ASINH_POS_LE:
    ∀x. 0 ≤ x ⇒ 0 ≤ asinh x
Proof
    strip_tac >> CONV_TAC CONTRAPOS_CONV >> simp[REAL_NOT_LE] >>
    qspec_then ‘asinh x’ mp_tac SINH_NEG_LT >> simp[SINH_ASINH]
QED

Theorem ASINH_POS_LT:
    ∀x. 0 < x ⇒ 0 < asinh x
Proof
    strip_tac >> CONV_TAC CONTRAPOS_CONV >> simp[REAL_NOT_LT] >>
    qspec_then ‘asinh x’ mp_tac SINH_NEG_LE >> simp[SINH_ASINH]
QED

Theorem ASINH_NEG_LE:
    ∀x. x ≤ 0 ⇒ asinh x ≤ 0
Proof
    strip_tac >> CONV_TAC CONTRAPOS_CONV >> simp[REAL_NOT_LE] >>
    qspec_then ‘asinh x’ mp_tac SINH_POS_LT >> simp[SINH_ASINH]
QED

Theorem ASINH_NEG_LT:
    ∀x. x < 0 ⇒ asinh x < 0
Proof
    strip_tac >> CONV_TAC CONTRAPOS_CONV >> simp[REAL_NOT_LT] >>
    qspec_then ‘asinh x’ mp_tac SINH_POS_LE >> simp[SINH_ASINH]
QED

Theorem ASINH_NZ:
    ∀x. asinh x ≠ 0 ⇔ x ≠ 0
Proof
    rw[] >> qspec_then ‘asinh x’ mp_tac SINH_NZ >> simp[SINH_ASINH]
QED

Theorem ASINH_0:
    asinh 0 = 0
Proof
    simp[SRULE [] ASINH_NZ]
QED

Theorem ACOSH_WITNESS[local]:
    ∀y. 1 ≤ y ⇒ 0 ≤ ln (y + sqrt (y² - 1)) ∧ cosh (ln (y + sqrt (y² - 1))) = y
Proof
    gen_tac >> strip_tac >> irule_at Any LN_POS >> conj_asm1_tac
    >- (irule REAL_LE_TRANS >> first_assum $ irule_at Any >> simp[] >>
        irule SQRT_POS_LE >> simp[REAL_SUB_LE,REAL_LE1_POW2]) >>
    simp[cosh_def] >> qabbrev_tac ‘z = (y + sqrt (y² - 1))’ >>
    ‘0 < z’ by (simp[]) >> simp[GSYM LN_INV,iffRL EXP_LN,REAL_INV_1OVER] >>
    irule REAL_EQ_LMUL_IMP >> qexists ‘z’ >>
    simp[REAL_ADD_LDISTRIB,Excl "REAL_EQ_LMUL",Excl "RMUL_EQNORM1",Excl "RMUL_EQNORM2"] >>
    qunabbrev_tac ‘z’ >> simp[ADD_POW_2,REAL_ADD_LDISTRIB] >>
    ‘0 ≤ y² - 1’ by simp[REAL_SUB_LE,REAL_LE1_POW2] >> simp[SQRT_POW_2]
QED

Theorem ACOSH_UNIQUE[local]:
    ∀x y z. 0 ≤ x ∧ cosh x = y ∧ 0 ≤ z ∧ cosh z = y ⇒ x = z
Proof
    rw[] >> qpat_x_assum ‘_ = _’ mp_tac >>
    CONV_TAC CONTRAPOS_CONV >>
    rw[] >> wlog_tac ‘x < z’ [‘x’,‘z’]
    >- (first_x_assum $ irule o GSYM >> simp[]) >>
    dxrule_all_then mp_tac COSH_MONO_LT >> simp[]
QED

Theorem ACOSH_COSH:
    ∀x. 0 ≤ x ⇒ acosh (cosh x) = x
Proof
    rw[acosh_def] >> irule SELECT_UNIQUE_ALT >> simp[ACOSH_UNIQUE]
QED

Theorem ACOSH_COSH_NEG:
    ∀x. x ≤ 0 ⇒ acosh (cosh x) = -x
Proof
    rw[] >> qspec_then ‘-x’ mp_tac ACOSH_COSH >>
    simp[COSH_NEG]
QED

Theorem COSH_ACOSH:
    ∀x. 1 ≤ x ⇒ cosh (acosh x) = x
Proof
    rw[acosh_def] >> SELECT_ELIM_TAC >>
    simp[ACOSH_UNIQUE] >> metis_tac[ACOSH_WITNESS]
QED

Theorem ACOSH_1:
    acosh 1 = 0
Proof
    mp_tac COSH_0 >> disch_then $ SUBST1_TAC o SYM >> simp[ACOSH_COSH]
QED

Theorem ACOSH_NZ:
    ∀x. 1 < x ⇒ acosh x ≠ 0
Proof
    rw[] >> simp[acosh_def] >> SELECT_ELIM_TAC >>
    conj_asm1_tac >- metis_tac[ACOSH_WITNESS,REAL_LE_LT] >>
    gs[] >> strip_tac >> gs[COSH_0]
QED

Theorem ACOSH_POS_LE:
    ∀x. 1 ≤ x ⇒ 0 ≤ acosh x
Proof
    rw[acosh_def] >> SELECT_ELIM_TAC >>
    simp[ACOSH_UNIQUE] >> metis_tac[ACOSH_WITNESS]
QED

Theorem ACOSH_POS_LT:
    ∀x. 1 < x ⇒ 0 < acosh x
Proof
    rw[] >> ‘acosh x ≠ 0’ suffices_by metis_tac[SRULE [REAL_LE_LT] ACOSH_POS_LE] >>
    simp[ACOSH_NZ]
QED

Theorem ATANH_WITNESS[local]:
    ∀y. -1 < y ∧ y < 1 ⇒ tanh (ln ((1 + y) / (1 - y)) / 2) = y
Proof
    rw[tanh_alt2] >> qabbrev_tac ‘z = ((1 + y) / (1 − y))’ >>
    ‘0 < z’ by simp[Abbr ‘z’] >> simp[iffRL EXP_LN] >>
    simp[Abbr ‘z’] >> simp[real_sub,add_ratl]
QED

Theorem ATANH_UNIQUE[local]:
    ∀x y z. tanh x = y ∧ tanh z = y ⇒ x = z
Proof
    simp[] >> rpt gen_tac >> CONV_TAC CONTRAPOS_CONV >>
    rw[] >> wlog_tac ‘x < z’ [‘x’,‘z’]
    >- (first_x_assum $ irule o GSYM >> simp[]) >>
    dxrule_all_then mp_tac TANH_MONO_LT >> simp[]
QED

Theorem ATANH_TANH:
    ∀x. atanh (tanh x) = x
Proof
    rw[atanh_def] >> irule SELECT_UNIQUE_ALT >> simp[ATANH_UNIQUE]
QED

Theorem TANH_ATANH:
    ∀x. -1 < x ∧ x < 1 ⇒ tanh (atanh x) = x
Proof
    rw[atanh_def] >> SELECT_ELIM_TAC >>
    simp[ATANH_UNIQUE] >> metis_tac[ATANH_WITNESS]
QED

Theorem ATANH_NZ:
    ∀x. -1 < x ∧ x ≠ 0 ∧ x < 1 ⇒ atanh x ≠ 0
Proof
    rw[] >> qspec_then ‘atanh x’ mp_tac TANH_NZ >> simp[TANH_ATANH]
QED

Theorem ATANH_0:
    atanh 0 = 0
Proof
    mp_tac TANH_0 >> disch_then $ SUBST1_TAC o SYM >>
    simp[ATANH_TANH] >> simp[TANH_0]
QED

Theorem ATANH_POS_LE:
    ∀x. 0 ≤ x ∧ x < 1 ⇒ 0 ≤ atanh x
Proof
    rw[] >> ‘-1 < x’ by (irule REAL_LTE_TRANS >> qexists ‘0’ >> simp[]) >>
    qpat_x_assum ‘0 ≤ _’ mp_tac >> CONV_TAC CONTRAPOS_CONV >> simp[REAL_NOT_LE] >>
    qspec_then ‘atanh x’ mp_tac TANH_NEG_LT >> simp[TANH_ATANH]
QED

Theorem ATANH_POS_LT:
    ∀x. 0 < x ∧ x < 1 ⇒ 0 < atanh x
Proof
    rw[] >> ‘-1 < x’ by (irule REAL_LTE_TRANS >> qexists ‘0’ >> simp[]) >>
    qpat_x_assum ‘0 < _’ mp_tac >> CONV_TAC CONTRAPOS_CONV >> simp[REAL_NOT_LT] >>
    qspec_then ‘atanh x’ mp_tac TANH_NEG_LE >> simp[TANH_ATANH]
QED

Theorem ATANH_NEG_LE:
    ∀x. -1 < x ∧ x ≤ 0 ⇒ atanh x ≤ 0
Proof
    rw[] >> ‘x < 1’ by (irule REAL_LET_TRANS >> qexists ‘0’ >> simp[]) >>
    qpat_x_assum ‘_ ≤ 0’ mp_tac >> CONV_TAC CONTRAPOS_CONV >> simp[REAL_NOT_LE] >>
    qspec_then ‘atanh x’ mp_tac TANH_POS_LT >> simp[TANH_ATANH]
QED

Theorem ATANH_NEG_LT:
    ∀x. -1 < x ∧ x < 0 ⇒ atanh x < 0
Proof
    rw[] >> ‘x < 1’ by (irule REAL_LET_TRANS >> qexists ‘0’ >> simp[]) >>
    qpat_x_assum ‘_ < 0’ mp_tac >> CONV_TAC CONTRAPOS_CONV >> simp[REAL_NOT_LT] >>
    qspec_then ‘atanh x’ mp_tac TANH_POS_LE >> simp[TANH_ATANH]
QED

Theorem ASECH_WITNESS[local]:
    ∀y. 0 < y ∧ y ≤ 1 ⇒ 0 ≤ (acosh y⁻¹) ∧ sech (acosh y⁻¹) = y
Proof
    gen_tac >> strip_tac >> simp[sech_def,ACOSH_POS_LE,COSH_ACOSH]
QED

Theorem ASECH_UNIQUE[local]:
    ∀x y z. 0 ≤ x ∧ sech x = y ∧ 0 ≤ z ∧ sech z = y ⇒ x = z
Proof
    rw[] >> qpat_x_assum ‘_ = _’ mp_tac >>
    CONV_TAC CONTRAPOS_CONV >>
    rw[] >> wlog_tac ‘x < z’ [‘x’,‘z’]
    >- (first_x_assum $ irule o GSYM >> simp[]) >>
    dxrule_all_then mp_tac SECH_ANTIMONO_LT >> simp[]
QED

Theorem ASECH_SECH:
    ∀x. 0 ≤ x ⇒ asech (sech x) = x
Proof
    rw[asech_def] >> irule SELECT_UNIQUE_ALT >> simp[ASECH_UNIQUE]
QED

Theorem ASECH_SECH_NEG:
    ∀x. x ≤ 0 ⇒ asech (sech x) = -x
Proof
    rw[] >> qspec_then ‘-x’ mp_tac ASECH_SECH >>
    simp[SECH_NEG]
QED

Theorem SECH_ASECH:
    ∀x. 0 < x ∧ x ≤ 1 ⇒ sech (asech x) = x
Proof
    rw[asech_def] >> SELECT_ELIM_TAC >>
    simp[ASECH_UNIQUE] >> metis_tac[ASECH_WITNESS]
QED

Theorem ASECH_1:
    asech 1 = 0
Proof
    mp_tac SECH_0 >> disch_then $ SUBST1_TAC o SYM >> simp[ASECH_SECH]
QED

Theorem ASECH_POS_LE:
    ∀x. 0 < x ∧ x ≤ 1 ⇒ 0 ≤ asech x
Proof
    rw[asech_def] >> SELECT_ELIM_TAC >>
    simp[ASECH_UNIQUE] >> metis_tac[ASECH_WITNESS]
QED

Theorem ASECH_NZ:
    ∀x. 0 < x ∧ x < 1 ⇒ asech x ≠ 0
Proof
    rw[] >> simp[asech_def] >> SELECT_ELIM_TAC >>
    conj_asm1_tac >- metis_tac[ASECH_WITNESS,REAL_LE_LT] >>
    gs[] >> strip_tac >> gs[SECH_0]
QED

Theorem ASECH_POS_LT:
    ∀x. 0 < x ∧ x < 1 ⇒ 0 < asech x
Proof
    metis_tac[REAL_LE_LT,ASECH_POS_LE,ASECH_NZ]
QED

Theorem ACSCH_WITNESS[local]:
    ∀y. y ≠ 0 ⇒ asinh y⁻¹ ≠ 0 ∧ csch (asinh y⁻¹) = y
Proof
    gen_tac >> strip_tac >> simp[csch_def,SINH_ASINH,ASINH_NZ]
QED

Theorem ACSCH_UNIQUE[local]:
    ∀x y z. x ≠ 0 ∧ csch x = y ∧ z ≠ 0 ∧ csch z = y ⇒ x = z
Proof
    rw[] >> qpat_x_assum ‘_ = _’ mp_tac >>
    CONV_TAC CONTRAPOS_CONV >>
    rw[] >> wlog_tac ‘x < z’ [‘x’,‘z’]
    >- (first_x_assum $ irule o GSYM >> simp[]) >>
    Cases_on ‘z < 0 ∨ 0 < x’
    >- (dxrule_all_then mp_tac CSCH_ANTIMONO_LT >> simp[]) >>
    gs[] >> ‘csch x < csch z’ suffices_by simp[] >>
    irule REAL_LT_TRANS >> qexists ‘0’ >> simp[CSCH_NEG_LT,CSCH_POS_LT]
QED

Theorem ACSCH_CSCH:
    ∀x. x ≠ 0 ⇒ acsch (csch x) = x
Proof
    rw[acsch_def] >> irule SELECT_UNIQUE_ALT >> simp[ACSCH_UNIQUE]
QED

Theorem CSCH_ACSCH:
    ∀x. x ≠ 0 ⇒ csch (acsch x) = x
Proof
    rw[acsch_def] >> SELECT_ELIM_TAC >>
    simp[ACSCH_UNIQUE] >> metis_tac[ACSCH_WITNESS]
QED

Theorem ACSCH_NZ:
    ∀x. x ≠ 0 ⇒ acsch x ≠ 0
Proof
    rw[acsch_def] >> SELECT_ELIM_TAC >>
    simp[ACSCH_UNIQUE] >> metis_tac[ACSCH_WITNESS]
QED

(*
(* Not true under the current definition *)
Theorem ACSCH_0:
    acsch 0 = 0
Proof
    rw[acsch_def] >> SELECT_ELIM_TAC >>
    conj
QED
*)

Theorem ACSCH_POS_LT:
    ∀x. 0 < x ⇒ 0 < acsch x
Proof
    rw[] >> ‘x ≠ 0’ by simp[REAL_LT_IMP_NE] >>
    last_x_assum mp_tac >> CONV_TAC CONTRAPOS_CONV >>
    simp[REAL_NOT_LT,REAL_LE_LT,ACSCH_NZ] >>
    qspec_then ‘acsch x’ mp_tac CSCH_NEG_LT >> simp[CSCH_ACSCH]
QED

Theorem ACSCH_NEG_LT:
    ∀x. x < 0 ⇒ acsch x < 0
Proof
    rw[] >> ‘x ≠ 0’ by simp[REAL_LT_IMP_NE] >>
    last_x_assum mp_tac >> CONV_TAC CONTRAPOS_CONV >>
    simp[REAL_NOT_LT,REAL_LE_LT,ACSCH_NZ] >>
    qspec_then ‘acsch x’ mp_tac CSCH_POS_LT >> simp[CSCH_ACSCH]
QED

Theorem ACOTH_WITNESS[local]:
    ∀y. y < -1 ∨ 1 < y ⇒ atanh y⁻¹ ≠ 0 ∧ coth (atanh y⁻¹) = y
Proof
    gen_tac >> strip_tac >> simp[coth_def,TANH_ATANH,ATANH_NZ]
QED

Theorem ACOTH_UNIQUE[local]:
    ∀x y z. x ≠ 0 ∧ coth x = y ∧ z ≠ 0 ∧ coth z = y ⇒ x = z
Proof
    rw[] >> qpat_x_assum ‘_ = _’ mp_tac >>
    CONV_TAC CONTRAPOS_CONV >> rw[] >> wlog_tac ‘x < z’ [‘x’,‘z’]
    >- (first_x_assum $ irule o GSYM >> simp[]) >>
    Cases_on ‘z < 0 ∨ 0 < x’
    >- (dxrule_all_then mp_tac COTH_ANTIMONO_LT >> simp[]) >>
    gs[] >> ‘coth x < coth z’ suffices_by simp[] >>
    irule REAL_LT_TRANS >> qexists ‘0’ >> simp[COTH_NEG_LT,COTH_POS_LT]
QED

Theorem ACOTH_COTH:
    ∀x. x ≠ 0 ⇒ acoth (coth x) = x
Proof
    rw[acoth_def] >> irule SELECT_UNIQUE_ALT >> simp[ACOTH_UNIQUE]
QED

Theorem COTH_ACOTH:
    ∀x. x < -1 ∨ 1 < x ⇒ coth (acoth x) = x
Proof
    rw[acoth_def] >> SELECT_ELIM_TAC >>
    simp[ACOTH_UNIQUE] >> metis_tac[ACOTH_WITNESS]
QED

Theorem ACOTH_NZ:
    ∀x. x < -1 ∨ 1 < x ⇒ acoth x ≠ 0
Proof
    rw[acoth_def] >> SELECT_ELIM_TAC >>
    simp[ACOTH_UNIQUE] >> metis_tac[ACOTH_WITNESS]
QED

Theorem ACOTH_POS_LT:
    ∀x. 1 < x ⇒ 0 < acoth x
Proof
    rw[] >> qspec_then ‘acoth x’ mp_tac COTH_NEG_LT >> simp[COTH_ACOTH] >>
    simp[REAL_NOT_LT,REAL_LE_LT,ACOTH_NZ]
QED

Theorem ACOTH_NEG_LT:
    ∀x. x < -1 ⇒ acoth x < 0
Proof
    rw[] >> qspec_then ‘acoth x’ mp_tac COTH_POS_LT >> simp[COTH_ACOTH] >>
    simp[REAL_NOT_LT,REAL_LE_LT,ACOTH_NZ]
QED

(*** Inverse Hyperbolic Trig as Arguement Inverses ***)

Theorem ASECH_EQ_ACOSH:
    ∀x. 0 < x ∧ x ≤ 1 ⇒ asech x = acosh x⁻¹
Proof
    qx_gen_tac ‘y’ >> rw[asech_def] >> irule SELECT_UNIQUE_ALT >>
    simp[ASECH_WITNESS,ASECH_UNIQUE]
QED

Theorem ACSCH_EQ_ASINH:
    ∀x. x ≠ 0 ⇒ acsch x = asinh x⁻¹
Proof
    qx_gen_tac ‘y’ >> rw[acsch_def] >> irule SELECT_UNIQUE_ALT >>
    simp[ACSCH_WITNESS,ACSCH_UNIQUE]
QED

Theorem ACOTH_EQ_ATANH:
    ∀x. x < -1 ∨ 1 < x ⇒ acoth x = atanh x⁻¹
Proof
    qx_gen_tac ‘y’ >> rw[acoth_def] >> irule SELECT_UNIQUE_ALT >>
    simp[ACOTH_WITNESS,ACOTH_UNIQUE]
QED

(*** Inverse Hyperbolic Trig as Natural Log ***)

Theorem ASINH_EQ_LN:
    ∀x. asinh x = ln (x + sqrt (x² + 1))
Proof
    qx_gen_tac ‘y’ >> simp[asinh_def] >> irule SELECT_UNIQUE_ALT >>
    simp[ASINH_WITNESS,ASINH_UNIQUE]
QED

Theorem ACOSH_EQ_LN:
    ∀x. 1 ≤ x ⇒ acosh x = ln (x + sqrt (x² - 1))
Proof
    qx_gen_tac ‘y’ >> rw[acosh_def] >> irule SELECT_UNIQUE_ALT >>
    simp[ACOSH_WITNESS,ACOSH_UNIQUE]
QED

Theorem ATANH_EQ_LN:
    ∀x. -1 < x ∧ x < 1 ⇒ atanh x = ln ((1 + x) / (1 - x)) / 2
Proof
    qx_gen_tac ‘y’ >> rw[atanh_def,Excl "RMUL_EQNORM4"] >>
    irule SELECT_UNIQUE_ALT >> simp[ATANH_WITNESS,ATANH_UNIQUE,Excl "RMUL_EQNORM4"]
QED

Theorem ASECH_EQ_LN:
    ∀x. 0 < x ∧ x ≤ 1 ⇒ asech x = ln (x⁻¹ + sqrt (x⁻¹ ² - 1))
Proof
    simp[ASECH_EQ_ACOSH,ACOSH_EQ_LN]
QED

Theorem ACSCH_EQ_LN:
    ∀x. x ≠ 0 ⇒ acsch x = ln (x⁻¹ + sqrt (x⁻¹ ² + 1))
Proof
    simp[ACSCH_EQ_ASINH,ASINH_EQ_LN]
QED

Theorem ACOTH_EQ_LN:
    ∀x. (x < -1 ∨ 1 < x) ⇒ acoth x = ln ((x + 1) / (x - 1)) / 2
Proof
    rw[] >> simp[ACOTH_EQ_ATANH,ATANH_EQ_LN] >> AP_TERM_TAC >>
    simp[REAL_INV_1OVER,REAL_SUB_LDISTRIB,REAL_ADD_LDISTRIB]
QED

(* natural log as atanh *)

Theorem LN_EQ_ATANH:
    ∀x. 0 < x ⇒ ln x = 2 * atanh ((x - 1) / (x + 1))
Proof
    rw[] >> qabbrev_tac ‘y = (x − 1) / (x + 1)’ >>
    ‘-1 < y ∧ y < 1’ by simp[Abbr ‘y’] >> simp[ATANH_EQ_LN] >>
    AP_TERM_TAC >> simp[Abbr ‘y’,real_sub,neg_rat,add_ratr]
QED

(*** Inverse Hyperbolic Trig Negative Inputs ***)

(*
SINH, TANH
CSCH, COTH
*)

Theorem ASINH_NEG:
    ∀x. asinh (-x) = -asinh x
Proof
    rw[] >> qspec_then ‘x’ mp_tac ASINH_WITNESS >> rename [‘sinh x’] >>
    disch_then $ SUBST1_TAC o SYM >> simp[ASINH_SINH,GSYM SINH_NEG]
QED

Theorem ATANH_NEG:
    ∀x. -1 < x ∧ x < 1 ⇒ atanh (-x) = -atanh x
Proof
    rw[] >> qspec_then ‘x’ mp_tac ATANH_WITNESS >> simp[] >> rename [‘tanh x’] >>
    disch_then $ SUBST1_TAC o SYM >> simp[ATANH_TANH,GSYM TANH_NEG]
QED

Theorem ACSCH_NEG:
    ∀x. x ≠ 0 ⇒ acsch (-x) = -acsch x
Proof
    rw[] >> qspec_then ‘x’ mp_tac ACSCH_WITNESS >>
    ‘asinh x⁻¹ ≠ 0’ by simp[ASINH_NZ,REAL_INV_NZ] >> simp[] >> rename [‘csch x’] >>
    disch_then $ SUBST1_TAC o SYM >> simp[ACSCH_CSCH,GSYM CSCH_NEG]
QED

Theorem ACOTH_NEG:
    ∀x. x < -1 ∨ 1 < x ⇒ acoth (-x) = -acoth x
Proof
    rw[] >> qspec_then ‘x’ mp_tac ACOTH_WITNESS >>
    ‘atanh x⁻¹ ≠ 0’ by (irule ATANH_NZ >> simp[]) >>
    simp[] >> rename [‘coth x’] >>
    disch_then $ SUBST1_TAC o SYM >> simp[ACOTH_COTH,GSYM COTH_NEG]
QED

(*** Inverse Hyperbolic Trig Zero Lemmas ***)

(*
Theorem ACOSH_POS_LT:
    ∀x. 1 < x ⇒ 0 < acosh x
Proof
    ‘∀x. 0 ≤ x ∧ 1 < cosh x ⇒ 0 < x’ suffices_by (rw[] >>
        first_x_assum irule >> simp[COSH_ACOSH,ACOSH_POS_LE]) >>
    rw[] >> pop_assum mp_tac >> CONV_TAC CONTRAPOS_CONV >> rw[] >>
    ‘x = 0’ by simp[] >> rw[COSH_0]
QED
*)

(*
Theorem ATANH_0:
    atanh 0 = 0
Proof
    mp_tac $ AP_TERM “atanh” TANH_0 >> simp[ATANH_TANH]
QED
*)

(*** Inverse Hyperbolic Trig Mixed Inverses ***)

(*
https://en.wikipedia.org/wiki/Inverse_hyperbolic_functions#Composition_of_hyperbolic_and_inverse_hyperbolic_functions
*)

Theorem SINH_ACOSH:
    ∀x. 1 < x ⇒ sinh (acosh x) = sqrt (x² - 1)
Proof
    ‘∀x. 0 ≤ x ⇒ sinh x = sqrt ((cosh x)² - 1)’ suffices_by (rw[] >>
        first_x_assum $ qspec_then ‘acosh x’ mp_tac >> simp[COSH_ACOSH,ACOSH_POS_LE]) >>
    rw[] >> irule EQ_SYM >> irule SQRT_POS_UNIQ >>  (*HERE*)
    simp[SRULE [REAL_EQ_SUB_RADD] COSH_SQ_SINH_SQ,REAL_SUB_LE,SINH_POS_LE]
QED

Theorem COSH_ASINH:
    ∀x. cosh (asinh x) = sqrt (x² + 1)
Proof
    ‘∀x. cosh x = sqrt ((sinh x)² + 1)’ suffices_by simp[SINH_ASINH] >>
    rw[] >> irule EQ_SYM >> irule SQRT_POS_UNIQ >>
    simp[SRULE [REAL_EQ_SUB_RADD] COSH_SQ_SINH_SQ,REAL_LE_ADD,REAL_LE_LT,COSH_POS_LT]
QED

(*** Inverse Hyperbolic Trig Derivatives ***)

Theorem DIFF_ASINH:
    ∀x. (asinh diffl (sqrt (x² + 1))⁻¹) x
Proof
    rw[] >>
    qspecl_then [‘sinh’,‘asinh’,‘sqrt (x² + 1)’,‘asinh x - 1’,‘asinh x’,‘asinh x + 1’]
        mp_tac DIFF_INVERSE_OPEN >>
    simp[SINH_ASINH,ASINH_SINH] >> disch_then irule >> rw[]
    >- metis_tac[DIFF_SINH,DIFF_CONT]
    >- (irule SQRT_POS_NE >> irule REAL_LTE_TRANS >> qexists ‘1’ >> simp[])
    >- (qspecl_then [‘asinh x’] mp_tac DIFF_SINH >> simp[COSH_ASINH])
QED

Theorem DIFF_ACOSH:
    ∀x. 1 < x ⇒ (acosh diffl (sqrt (x² - 1))⁻¹) x
Proof
    rw[] >>
    qspecl_then [‘cosh’,‘acosh’,‘sqrt (x² - 1)’,‘0’,‘acosh x’,‘acosh x + 1’]
        mp_tac DIFF_INVERSE_OPEN >>
    simp[COSH_ACOSH,ACOSH_COSH] >> disch_then irule >> rw[]
    >- metis_tac[DIFF_COSH,DIFF_CONT]
    >- (irule SQRT_POS_NE >> simp[REAL_SUB_LT] >>
        qspecl_then [‘1’,‘x’,‘1’,‘x’] mp_tac REAL_LT_MUL2 >> simp[])
    >- simp[ACOSH_POS_LT]
    >- (qspecl_then [‘acosh x’] mp_tac DIFF_COSH >> simp[SINH_ACOSH])
QED

Theorem DIFF_ATANH:
    ∀x. -1 < x ∧ x < 1 ⇒ (atanh diffl (1 − x²)⁻¹) x
Proof
    rw[] >>
    qspecl_then [‘tanh’,‘atanh’,‘1 - x²’,‘atanh x - 1’,‘atanh x’,‘atanh x + 1’]
        mp_tac DIFF_INVERSE_OPEN >>
    simp[TANH_ATANH,ATANH_TANH] >> disch_then irule >> rw[]
    >- metis_tac[DIFF_TANH,DIFF_CONT]
    >- (wlog_tac ‘0 ≤ x’ [‘x’] >- (first_x_assum $ qspec_then ‘-x’ mp_tac >> simp[]) >>
        qspecl_then [‘x’,‘1’,‘x’,‘1’] mp_tac REAL_LT_MUL2 >> simp[])
    >- (qspecl_then [‘atanh x’] mp_tac DIFF_TANH >> simp[TANH_ATANH])
QED

Theorem DIFF_ASECH:
    ∀x. 0 < x ∧ x < 1 ⇒ (asech diffl -(x * sqrt (1 - x²))⁻¹) x
Proof
    rw[] >>
    qspecl_then [‘acosh’,‘λx. x⁻¹’] mp_tac DIFF_CHAIN >> simp[] >>
    disch_then (resolve_then Any
        (resolve_then Any (qspec_then ‘x’ mp_tac) DIFF_ACOSH) $ DIFF_CONV “λx:real. x⁻¹”) >>
    simp[] >> strip_tac >> irule $ iffLR DIFF_CONG >> pop_assum $ irule_at Any >>
    qexistsl [‘1’,‘0’] >> simp[ASECH_EQ_ACOSH,iffRL REAL_LE_LT,REAL_INV_MUL'] >>
    ‘0 < sqrt (x⁻¹ ² − 1) ∧ 0 < sqrt (1 − x²) ∧ 0 < x⁻¹ ² − 1’ by (
        ntac 2 $ irule_at Any SQRT_POS_LT >> simp[REAL_SUB_LT,POW_2_LT_1]) >>
    simp[] >> irule EQ_SYM >> irule SQRT_EQ >>
    simp[REAL_LE_MUL,POW_MUL,SQRT_POW_2,REAL_SUB_LDISTRIB]
QED

Theorem DIFF_ACSCH:
    ∀x. x ≠ 0 ⇒ (acsch diffl -(abs x * sqrt (1 + x²))⁻¹) x
Proof
    rw[] >>
    qspecl_then [‘asinh’,‘λx. x⁻¹’] mp_tac DIFF_CHAIN >> simp[] >>
    disch_then (resolve_then Any
        (resolve_then Any (qspec_then ‘x’ mp_tac) DIFF_ASINH) $ DIFF_CONV “λx:real. x⁻¹”) >>
    simp[] >> strip_tac >>
    ‘-x⁻¹ ² * (sqrt (x⁻¹ ² + 1))⁻¹ = -(abs x * sqrt (1 + x²))⁻¹’ by (
        pop_assum kall_tac >> simp[REAL_INV_MUL'] >>
        ‘0 < sqrt (x⁻¹ ² + 1) ∧ 0 < sqrt (1 + x²) ∧ 0 < x⁻¹ ² + 1 ∧ 0 < 1 + x²’ by (
            ntac 2 $ irule_at Any SQRT_POS_LT >> simp[REAL_LT_ADD]) >>
        simp[] >>
        qspecl_then [‘abs x * sqrt (1 + x²)’,‘x² * sqrt (x⁻¹ ² + 1)’]
            mp_tac REAL_EQ_SQUARE_ABS >>
        simp[REAL_ABS_MUL,iffRL ABS_REFL] >> disch_then kall_tac >>
        simp[POW_MUL,SQRT_POW_2,REAL_ADD_LDISTRIB]) >>
    pop_assum SUBST_ALL_TAC >> irule $ iffLR DIFF_CONG >> pop_assum $ irule_at Any >>
    simp[] >> ‘x < 0 ∨ 0 < x’ by simp[]
    >| [qexistsl [‘0’,‘x - 1’],qexistsl [‘x + 1’,‘0’]] >> simp[ACSCH_EQ_ASINH]
QED

Theorem DIFF_ACOTH:
    ∀x. x < -1 ∨ 1 < x ⇒ (acoth diffl (1 − x²)⁻¹) x
Proof
    rw[] >>
    qspecl_then [‘atanh’,‘λx. x⁻¹’] mp_tac DIFF_CHAIN >> simp[] >>
    disch_then (resolve_then Any
        (resolve_then Any (qspec_then ‘x’ mp_tac) DIFF_ATANH) $ DIFF_CONV “λx:real. x⁻¹”) >>
    simp[] >> strip_tac >> irule $ iffLR DIFF_CONG >> pop_assum $ irule_at Any
    >| [qexistsl [‘-1’,‘x - 1’],qexistsl [‘x + 1’,‘1’]] >>
    simp[ACOTH_EQ_ATANH] >>
    ‘1 − x⁻¹ ² ≠ 0 ∧ 1 − x² ≠ 0’ by (
        ‘1 < x²’ suffices_by simp[] >> simp[POW_2_1_LT]) >>
    simp[REAL_SUB_LDISTRIB]
QED

(*** Inverse Hyperbolic Trig Monotonicity ***)

Theorem ASINH_MONO_LT:
    ∀x y. x < y ⇒ asinh x < asinh y
Proof
    rw[] >> irule DIFF_POS_MONO_LT_UU >> simp[] >>
    rw[] >> irule_at Any DIFF_ASINH >> simp[SQRT_POS_LT,REAL_LET_ADD]
QED

Theorem ASINH_MONO_LE:
    ∀x y. x ≤ y ⇒ asinh x ≤ asinh y
Proof
    rw[] >> Cases_on ‘x = y’ >> gs[REAL_LE_LT,ASINH_MONO_LT]
QED

Theorem ACOSH_MONO_LT:
    ∀x y. 1 ≤ x ∧ x < y ⇒ acosh x < acosh y
Proof
    reverse $ rw[REAL_LE_LT] >- simp[ACOSH_1,ACOSH_POS_LT] >>
    irule DIFF_POS_MONO_LT_OU >> simp[] >>
    qexists ‘1’ >> simp[] >> rw[] >>
    irule_at Any DIFF_ACOSH >> simp[] >> irule SQRT_POS_LT >>
    simp[REAL_SUB_LT,REAL_LT1_POW2]
QED

Theorem ACOSH_MONO_LE:
    ∀x y. 1 ≤ x ∧ x ≤ y ⇒ acosh x ≤ acosh y
Proof
    rw[] >> Cases_on ‘x = y’ >> gs[REAL_LE_LT,ACOSH_MONO_LT]
QED

Theorem ATANH_MONO_LT:
    ∀x y. -1 < x ∧ y < 1 ∧ x < y ⇒ atanh x < atanh y
Proof
    rw[] >> irule DIFF_POS_MONO_LT_OO >> simp[] >>
    qexistsl [‘-1’,‘1’] >> simp[] >> rw[] >>
    irule_at Any DIFF_ATANH >> simp[REAL_SUB_LT,POW_2_LT_1]
QED

Theorem ATANH_MONO_LE:
    ∀x y. -1 < x ∧ y < 1 ∧ x ≤ y ⇒ atanh x ≤ atanh y
Proof
    rw[] >> Cases_on ‘x = y’ >> gs[REAL_LE_LT,ATANH_MONO_LT]
QED

Theorem ASECH_ANTIMONO_LT:
    ∀x y. 0 < x ∧ y ≤ 1 ∧ x < y ⇒ asech y < asech x
Proof
    reverse $ rw[REAL_LE_LT] >- simp[ASECH_1,ASECH_POS_LT] >>
    irule DIFF_NEG_ANTIMONO_LT_OO >> simp[] >>
    qexistsl [‘0’,‘1’] >> simp[] >> rw[] >>
    irule_at Any DIFF_ASECH >> simp[] >> irule REAL_LT_MUL >>
    simp[] >> irule SQRT_POS_LT >> simp[REAL_SUB_LT,POW_2_LT_1]
QED

Theorem ASECH_ANTIMONO_LE:
    ∀x y. 0 < x ∧ y ≤ 1 ∧ x ≤ y ⇒ asech y ≤ asech x
Proof
    rw[] >> Cases_on ‘x = y’ >> gs[REAL_LE_LT,ASECH_ANTIMONO_LT]
QED

Theorem ACSCH_ANTIMONO_LT:
    ∀x y. (y < 0 ∨ 0 < x) ∧ x < y ⇒ acsch y < acsch x
Proof
    ntac 2 strip_tac >> wlog_tac ‘0 < x’ [‘x’,‘y’]
    >- (simp[] >> rw[] >> ‘y ≠ 0 ∧ x ≠ 0’ by (CCONTR_TAC >> gs[]) >>
        last_x_assum $ qspecl_then [‘-y’,‘-x’] mp_tac >> simp[ACSCH_NEG]) >>
    rw[] >> irule DIFF_NEG_ANTIMONO_LT_OU >> simp[] >>
    qexists ‘0’ >> rw[] >> irule_at Any DIFF_ACSCH >>
    simp[] >> irule REAL_LT_MUL >> simp[] >>
    irule SQRT_POS_LT >> simp[REAL_LT_ADD]
QED

Theorem ACSCH_ANTIMONO_LE:
    ∀x y. (y < 0 ∨ 0 < x) ∧ x ≤ y ⇒ acsch y ≤ acsch x
Proof
    rw[] >> Cases_on ‘x = y’ >> gs[REAL_LE_LT,ACSCH_ANTIMONO_LT]
QED

Theorem ACOTH_ANTIMONO_LT:
    ∀x y. (y < -1 ∨ 1 < x) ∧ x < y ⇒ acoth y < acoth x
Proof
    ntac 2 strip_tac >> wlog_tac ‘1 < x’ [‘x’,‘y’]
    >- (simp[] >> rw[] >> ‘x < -1’ by (simp[REAL_LT_TRANS]) >>
        last_x_assum $ qspecl_then [‘-y’,‘-x’] mp_tac >> simp[ACOTH_NEG]) >>
    rw[] >> irule DIFF_NEG_ANTIMONO_LT_OU >> simp[] >>
    qexists ‘1’ >> rw[] >> irule_at Any DIFF_ACOTH >>
    simp[REAL_LT_SUB_RADD,REAL_LT1_POW2]
QED

Theorem ACOTH_ANTIMONO_LE:
    ∀x y. (y < -1 ∨ 1 < x) ∧ x ≤ y ⇒ acoth y ≤ acoth x
Proof
    rw[] >> Cases_on ‘x = y’ >> gs[REAL_LE_LT,ACOTH_ANTIMONO_LT]
QED

(*** Polynomial Representations ***)

(*
This stuff existed for my (Jared Yeager) dissertation use,
it is not clear to me what of this is worth canonising.
*)

Theorem SUM_GEOM:
    ∀x n. x ≠ 1 ⇒ sum {0 .. n} (λn. x pow n) = (x pow SUC n - 1) / (x - 1)
Proof
    rw[] >> Induct_on ‘n’ >- (simp[NUMSEG_SING,SUM_SING]) >>
    simp[SUM_CLAUSES_NUMSEG,REAL_ADD_RDISTRIB] >> pop_assum kall_tac >>
    simp[REAL_SUB_LDISTRIB,GSYM pow]
QED

Theorem SUMS_GEOM:
    ∀x. abs x < 1 ⇒ ((λn. x pow n) sums (1 − x)⁻¹) 𝕌(:num)
Proof
    rw[] >> simp[sums_def] >> simp[SUM_GEOM] >>
    qspecl_then [‘λy. (1 - y) / (1 - x)’,‘0’,‘λn. x pow SUC n’] mp_tac $
        SRULE [GSYM RIGHT_FORALL_IMP_THM] $ iffLR CONTINUOUS_AT_SEQUENTIALLY >>
    ‘∀n. (x pow SUC n − 1) / (x − 1) = (1 − x pow SUC n) / (1 − x)’ by simp[] >>
    simp[o_DEF,REAL_INV_1OVER] >> pop_assum kall_tac >> disch_then irule >>
    simp[GSYM contl_eq_continuous_at] >>
    resolve_then Any (irule_at Any) (DIFF_CONV “(λy. (1r − y) / (1 − x))”) DIFF_CONT >>
    rw[LIM_SEQUENTIALLY,dist,GSYM POW_ABS] >> qexists ‘NUM_CEILING (ln e / ln (abs x))’ >>
    Cases_on ‘abs x = 0’ >- simp[POW_0] >> ‘0 < abs x’ by simp[] >>
    rename [‘y < 1’] >> rw[] >> irule $ iffLR LN_MONO_LT >> simp[LN_POW,REAL_POW_LT] >>
    qspecl_then [‘ln y’,‘&SUC n’,‘ln e / ln y’] mp_tac REAL_LT_LMUL_NEG >>
    impl_tac >- simp[LN_NEG_LT] >>
    ‘ln y ≠ 0’ by (dxrule_all_then mp_tac LN_NEG_LT >> simp[]) >>
    simp[] >> disch_then kall_tac >>
    irule REAL_LET_TRANS >> qexists ‘&n’ >> simp[] >>
    irule REAL_LE_TRANS >> qexists ‘&clg (ln e / ln y)’ >> simp[LE_NUM_CEILING]
QED

Theorem SUMMABLE_GEOM:
    ∀x. abs x < 1 ⇒ summable 𝕌(:num) (λn. x pow n)
Proof
    rw[] >> irule SUMS_SUMMABLE >> irule_at Any SUMS_GEOM >> simp[]
QED

Theorem INFSUM_GEOM:
    ∀x. abs x < 1 ⇒ suminf 𝕌(:num) (λn. x pow n) = (1 − x)⁻¹
Proof
    rw[] >> irule INFSUM_UNIQUE >> simp[SUMS_GEOM]
QED

Theorem INFSUM_REINDEX:
    ∀f g s t p. BIJ p s t ∧ (∀x. x ∈ s ⇒ g (p x) = f x) ∧ (∀x y. x ∈ s ∧ y ∈ s ∧ x < y ⇒ p x < p y) ⇒
        suminf s f = suminf t g
Proof
    ‘∀f g s t p l. BIJ p s t ∧ (∀x. x ∈ s ⇒ g (p x) = f x) ∧
      (∀x y. x ∈ s ∧ y ∈ s ∧ x < y ⇒ p x < p y) ∧ (f sums l) s ⇒ (g sums l) t’ suffices_by (
        rw[suminf_def] >> ‘∀l. (f sums l) s ⇔ (g sums l) t’ suffices_by simp[] >> rw[] >>
        eq_tac >> rw[] >> first_x_assum $ irule_at Any >- metis_tac[] >>
        pop_assum $ irule_at Any >> dxrule_then assume_tac BIJ_INV >> gs[] >>
        rename [‘BIJ q t s’] >> first_assum $ irule_at Any >> reverse $ rw[]
        >- (‘g (p (q x)) = f (q x)’ suffices_by simp[] >> first_x_assum irule >>
            gs[BIJ_ALT,FUNSET]) >>
        pop_assum mp_tac >> CONV_TAC CONTRAPOS_CONV >> rw[] >>
        reverse $ gs[NOT_LESS,LE_LT] >- (gs[BIJ_DEF,INJ_DEF]) >>
        ‘p (q y) < p (q x)’ suffices_by simp[] >> first_x_assum irule >>
        gs[BIJ_ALT,FUNSET]) >>
    rw[sums_def,LIM_SEQUENTIALLY] >>
    first_x_assum $ drule_then assume_tac >> gs[] >> rename [‘M ≤ _’] >>
    dxrule_then assume_tac $ iffLR BIJ_IFF_INV >> gs[] >> rename [‘_ ∈ _ ⇒ p (q _) = _’] >>
    ‘∀n. n ∈ t ⇒ sum (t ∩ {0 .. n}) g = sum (s ∩ {0 .. q n}) f’ by (rw[] >>
        irule EQ_SYM >> irule SUM_EQ_GENERAL_INVERSES >> qexistsl [‘p’,‘q’] >> rw[]
        >- (last_x_assum $ qspecl_then [‘x’,‘q n’] mp_tac >> simp[] >>
            pop_assum mp_tac >> rw[LE_LT] >> gs[]) >>
        pop_assum mp_tac >> CONV_TAC CONTRAPOS_CONV >> simp[NOT_LESS_EQUAL] >>
        rw[] >> last_x_assum $ qspecl_then [‘q n’,‘q y’] mp_tac >> simp[]) >>
    ‘∀r k. r ∩ {0 .. k} = ∅ ∨ ∃kp. kp ∈ r ∧ r ∩ {0 .. k} = r ∩ {0 .. kp}’ by (
        rpt $ pop_assum kall_tac >> rw[] >> Cases_on ‘r ∩ {0 .. k} = ∅’ >> simp[] >>
        dxrule_at_then Any assume_tac  $ SRULE [AND_IMP_INTRO] $ cj 1 MAX_SET_DEF >>
        gs[FINITE_INTER_NUMSEG] >> last_assum $ irule_at Any >>
        qabbrev_tac ‘kp = MAX_SET (r ∩ {0 .. k})’ >> simp[EXTENSION] >>
        qx_gen_tac ‘x’ >> eq_tac >> simp[]) >>
    first_assum $ qspecl_then [‘s’,‘M’] assume_tac >> fs[]
    >| [qexists ‘0’, rename [‘Mp ∈ _’] >> qexists ‘p Mp’] >> rw[] >>
    first_x_assum $ qspecl_then [‘t’,‘n’] assume_tac >> fs[]
    >- (qpat_x_assum ‘∀n. M ≤ n ⇒ _’ $ qspec_then ‘M’ assume_tac >> gs[SUM_CLAUSES])
    >- (rename [‘np ∈ _’] >> Cases_on ‘M ≤ q np’ >- (simp[]) >>
        gs[EXTENSION,NOT_LESS_EQUAL,GSYM IMP_DISJ_THM] >>
        ‘M < q np’ by simp[] >> gs[])
    >- (‘F’ suffices_by simp[] >> pop_assum mp_tac >> simp[GSYM MEMBER_NOT_EMPTY] >>
        pop_assum $ irule_at Any >> simp[])
    >- (rename [‘np ∈ _’] >> Cases_on ‘M ≤ q np’ >- (simp[]) >> gs[NOT_LESS_EQUAL] >>
        ‘p Mp ≤ np ∧ q np ≤ Mp’ by (
            gs[EXTENSION,GSYM IMP_DISJ_THM] >> metis_tac[LE_LT]) >>
        ‘np ≤ p Mp’ by metis_tac[LE_LT] >> ‘np = p Mp’ by simp[] >> gvs[] >>
        qpat_x_assum ‘∀n. M ≤ n ⇒ _’ $ qspec_then ‘M’ mp_tac >> simp[])
QED

Theorem ATANH_POLYNOMIAL:
    ∀x. -1 < x ∧ x < 1 ⇒ atanh x = suminf 𝕌(:num) (λn. (&(2 * n + 1))⁻¹ * x pow (2 * n + 1))
Proof
    qabbrev_tac ‘poly = λx. suminf 𝕌(:num) (λn. (&(2 * n + 1))⁻¹ * x pow (2 * n + 1))’ >> simp[] >>
    ‘∃c. ∀y. y ∈ {x | -1 < x ∧ x < 1} ⇒ atanh y = poly y + c’ suffices_by (rw[] >>
        ‘c = 0’ suffices_by simp[] >> first_x_assum $ qspec_then ‘0’ mp_tac >>
        simp[ATANH_0] >> ‘poly 0 = 0’ suffices_by simp[] >> simp[Abbr ‘poly’] >>
        rpt $ pop_assum kall_tac >> simp[POW_0',INFSUM_0]) >>
    irule DIFF_EQ_FUN_EQ >> simp[IS_INTERVAL_POSSIBILITIES,INTERIOR_INTERVAL_CASES] >>
    ‘∀z. -1 < z ∧ z < 1 ⇒ ∃l. (atanh diffl l) z ∧ (poly diffl l) z’ suffices_by metis_tac[DIFF_CONT] >>
    qx_gen_tac ‘x’ >> rw[] >> irule_at Any DIFF_ATANH >> simp[] >>
    ‘abs x² < 1’ by simp[ABS_POW2,POW_2_LT_1] >> simp[GSYM INFSUM_GEOM,REAL_POW_POW] >>
    ‘∃k. abs x < k ∧ k < 1’ by (irule REAL_MEAN >> simp[ABS_BOUNDS_LT]) >>
    qspecl_then [‘λn. (&n)⁻¹ * indicator ODD n’,‘k’,‘x’] mp_tac TERMDIFF >> impl_tac
    >- (simp[REAL_LTE_TRANS,ABS_LE] >> ntac 3 $ irule_at (Pos last) SER_COMPAR >>
        ntac 3 $ qexists ‘λn. (&n + 2) * k pow n’ >> ntac 3 $ qexists ‘0’ >> csimp[] >>
        ‘0 < k’ by simp[] >> simp[diffs,ABS_MUL,ABS_INV,GSYM POW_ABS,iffRL ABS_REFL] >>
        rw[indicator] >- (Cases_on ‘n’ >> simp[]) >> irule SER_RATIO >>
        map_every qabbrev_tac [‘f = λx. (x + 3) / (x + 2)’,‘N = NUM_CEILING (1 - k)⁻¹’] >>
        qexistsl [‘N’,‘f &N * k’] >> simp[ABS_MUL,GSYM POW_ABS,iffRL ABS_REFL] >>
        qspecl_then [‘f’,‘-1’] mp_tac DIFF_NEG_ANTIMONO_LT_OU >> impl_tac
        >- (rw[Abbr ‘f’] >> irule_at Any $ DIFF_CONV “λx:real. (x + 3) / (x + 2)” >> simp[]) >>
        disch_tac >> reverse conj_tac
        >- (simp[Abbr ‘N’] >> irule REAL_LET_TRANS >> qexists ‘k * f (1 − k)⁻¹’ >> reverse $ conj_tac
            >- (qspec_then ‘(1 − k)⁻¹’ mp_tac LE_NUM_CEILING >>
                rw[REAL_LE_LT] >> simp[] >> pop_assum $ SUBST1_TAC o SYM >> simp[]) >>
            simp[Abbr ‘f’,REAL_LT_ADD,REAL_POS_NZ] >> simp[REAL_INV_1OVER] >> simp[add_ratl] >>
            simp[REAL_ADD_LDISTRIB,REAL_SUB_LDISTRIB,real_sub,REAL_ADD_ASSOC] >>
            ‘k + 3 * k = 4 * k’ by simp[] >> simp[] >> pop_assum kall_tac >>
            ‘0 < 1 + k² - 2 * k’ suffices_by simp[] >>
            qspecl_then [‘1’,‘k’] mp_tac $ GSYM SUB_POW_2 >> simp[]) >>
        rw[] >> ‘SUC n + 2 = n + 3’ by simp[] >> pop_assum SUBST1_TAC >>
        ‘k * f (&N) * &(n + 2) * k pow n = (f (&N) * &(n + 2)) * k pow SUC n’ by simp[pow] >>
        pop_assum SUBST1_TAC >> simp[] >> ‘f (&n) ≤ f (&N)’ suffices_by simp[Abbr‘f’] >>
        pop_assum mp_tac >> rw[GREATER_EQ,REAL_LE_LT,LESS_OR_EQ] >>
        disj1_tac >> first_x_assum irule >> simp[]) >>
    qmatch_abbrev_tac ‘(poly_term diffl l_term) x ⇒ (poly diffl l) x’ >>
    ‘poly = poly_term ∧ l = l_term’ suffices_by simp[] >> UNABBREV_ALL_TAC >>
    simp[FUN_EQ_THM,GSYM suminf_univ] >> conj_tac
    >- (qx_gen_tac ‘y’ >> irule_at Any EQ_TRANS >>
        ‘(λn. (&n)⁻¹ * indicator ODD n * y pow n) =
          (λn. if n ∈ ODD then (λn. (&n)⁻¹ * y pow n) n else 0)’ by (
            rw[FUN_EQ_THM,indicator] >> Cases_on ‘n ∈ ODD’ >> simp[]) >>
        pop_assum SUBST1_TAC >> irule_at (Pos last) $ GSYM INFSUM_RESTRICT >>
        irule INFSUM_REINDEX >> qexists ‘λn. 2 * n + 1’ >>
        simp[BIJ_IFF_INV,IN_APP,SRULE [ADD1] ODD_DOUBLE] >>
        qexists ‘λn. (n - 1) DIV 2’ >> simp[ODD_EXISTS,PULL_EXISTS])
    >- (irule_at Any EQ_TRANS >>
        ‘(λn. diffs (λn. (&n)⁻¹ * indicator ODD n) n * x pow n) =
          (λn. if n ∈ EVEN then (λn. x pow n) n else 0)’ by (
            rw[diffs,FUN_EQ_THM,indicator,IN_APP,ODD,GSYM EVEN_ODD] >>
            Cases_on ‘EVEN n’ >> simp[]) >>
        pop_assum SUBST1_TAC >> irule_at (Pos last) $ GSYM INFSUM_RESTRICT >>
        irule INFSUM_REINDEX >> qexists ‘λn. 2 * n’ >>
        simp[BIJ_IFF_INV,IN_APP,EVEN_DOUBLE] >>
        qexists ‘λn. n DIV 2’ >> simp[EVEN_EXISTS,PULL_EXISTS])
QED

Theorem LN_POLYNOMIAL:
    ∀x. 0 < x ⇒ ln x = 2 * suminf 𝕌(:num) (λn. (&(2 * n + 1))⁻¹ * ((x - 1) / (x + 1)) pow (2 * n + 1))
Proof
    qx_gen_tac ‘x’ >> qabbrev_tac ‘y = (x − 1) / (x + 1)’ >> rw[LN_EQ_ATANH] >>
    irule ATANH_POLYNOMIAL >> simp[Abbr ‘y’]
QED

(* Necessary ‘sums’ Results *)

Theorem ATANH_POLYNOMIAL_SUMMABLE:
    ∀x. -1 < x ∧ x < 1 ⇒ summable 𝕌(:num) (λi. (&(2 * i + 1))⁻¹ * x pow (2 * i + 1))
Proof
    rw[] >> Cases_on ‘x = 0’ >- simp[POW_0',SUMMABLE_0] >>
    simp[summable_univ] >> irule SER_COMPAR >> qexists ‘λi. (x pow 2) pow i’ >> conj_tac
    >- (qexists ‘0’ >> rw[GREATER_EQ] >> simp[ABS_MUL,ABS_INV,GSYM POW_ABS] >>
        irule REAL_LE_TRANS >> qexists ‘x² pow n’ >> simp[] >>
        ‘x² = (abs x)²’ by simp[] >> pop_assum SUBST1_TAC >>
        simp[REAL_POW_POW] >> irule REAL_POW_ANTIMONO >> simp[]) >>
    irule $ SRULE [summable_univ] SUMMABLE_GEOM >> simp[POW_2_LT_1]
QED

Theorem HALF_LN_POLYNOMIAL_SUMMABLE:
    ∀x. 0 < x ⇒ summable 𝕌(:num) (λi. (&(2 * i + 1))⁻¹ * ((x - 1) / (x + 1)) pow (2 * i + 1))
Proof
    strip_tac >> disch_tac >> qabbrev_tac ‘y = (x − 1) / (x + 1)’ >>
    irule ATANH_POLYNOMIAL_SUMMABLE >> simp[Abbr ‘y’]
QED

Theorem LN_POLYNOMIAL_SUMMABLE:
    ∀x. 0 < x ⇒ summable 𝕌(:num) (λi. 2 * (&(2 * i + 1))⁻¹ * ((x - 1) / (x + 1)) pow (2 * i + 1))
Proof
    rw[] >> drule_then assume_tac HALF_LN_POLYNOMIAL_SUMMABLE >>
    dxrule_then (qspec_then ‘2’ mp_tac) SUMMABLE_CMUL >> simp[]
QED

Theorem EXP_POLYNOMIAL_SUMMABLE:
    ∀x. summable 𝕌(:num) (λi. (&FACT i)⁻¹ * x pow i)
Proof
    rw[] >> Cases_on ‘x = 0’
    >- (irule $ iffRL SUMMABLE_IFF_EVENTUALLY >> qexists ‘λi. 0’ >>
        rw[SUMMABLE_0] >> qexists ‘1’ >> simp[]) >>
    simp[summable_univ] >> irule SER_RATIO >>
    qexistsl [‘NUM_CEILING (abs x)’,‘abs x / &SUC (NUM_CEILING (abs x))’] >>
    ‘∀i. abs (&FACT i)⁻¹ = (&FACT i)⁻¹’ by simp[] >>
    simp[GREATER_EQ,ABS_MUL,GSYM POW_ABS,FACT_LESS,iffLR LT_LE] >>
    simp[FACT,pow] >> pop_assum kall_tac >>
    irule_at Any REAL_LET_TRANS >> irule_at Any LE_NUM_CEILING >> simp[]
QED

Theorem ATANH_POLYNOMIAL_CONVERGENCE:
    ∀x. -1 < x ∧ x < 1 ⇒ ∀e. 0 < e ⇒ ∃N. ∀n. N ≤ n ⇒
        abs (atanh x - sum {0 .. n} (λi. (&(2 * i + 1))⁻¹ * x pow (2 * i + 1))) < e
Proof
    rw[] >> Cases_on ‘x = 0’ >- (simp[ATANH_0,POW_0',SUM_0']) >>
    simp[ATANH_POLYNOMIAL,GSYM dist,Once DIST_SYM] >>
    map_every qabbrev_tac [‘f = (λi. (&(2 * i + 1))⁻¹ * x pow (2 * i + 1))’,
        ‘sf = (λn. sum {0 .. n} f)’,‘l = suminf UNIV f’] >>
    simp[] >> qpat_x_assum ‘0 < e’ mp_tac >> qid_spec_tac ‘e’ >>
    simp[GSYM LIM_SEQUENTIALLY] >> qunabbrev_tac ‘sf’ >>
    qspecl_then [‘f’,‘l’,‘UNIV’] mp_tac $ GSYM sums_def >> simp[] >> disch_then kall_tac >>
    qunabbrev_tac ‘l’ >> simp[Abbr ‘f’,SUMS_INFSUM,ATANH_POLYNOMIAL_SUMMABLE]
QED

Theorem LN_POLYNOMIAL_CONVERGENCE:
    ∀x. 0 < x ⇒ ∀e. 0 < e ⇒ ∃N. ∀n. N ≤ n ⇒
        abs (ln x - 2 * sum {0 .. n} (λi. (&(2 * i + 1))⁻¹ * ((x - 1) / (x + 1)) pow (2 * i + 1))) < e
Proof
    ntac 2 strip_tac >> qabbrev_tac ‘z = (x − 1) / (x + 1)’ >>
    simp[LN_EQ_ATANH,GSYM REAL_SUB_LDISTRIB,ABS_MUL] >>
    ‘-1 < z ∧ z < 1’ by simp[Abbr ‘z’] >> rw[] >>
    drule_then assume_tac ATANH_POLYNOMIAL_CONVERGENCE >> gs[] >>
    pop_assum $ qspec_then ‘e / 2’ mp_tac >> simp[]
QED

Theorem EXP_POLYNOMIAL_CONVERGENCE:
    ∀x e. 0 < e ⇒ ∃N. ∀n. N ≤ n ⇒
        abs (exp x - sum {0 .. n} (λi. (&FACT i)⁻¹ * x pow i)) < e
Proof
    rw[] >> Cases_on ‘x = 0’
    >- (rw[EXP_0] >> simp[Once SUM_CLAUSES_LEFT,FACT] >>
        ‘∀n. sum {1 .. n} (λi. (&FACT i)⁻¹ * 0 pow i) = 0’ suffices_by simp[] >>
        rw[] >> irule SUM_EQ_0_NUMSEG >> simp[LE_LT,POW_0']) >>
    simp[exp,GSYM dist,Once DIST_SYM] >>
    map_every qabbrev_tac [‘f = (λi. (&FACT i)⁻¹ * x pow i)’,
        ‘sf = (λn. sum {0 .. n} f)’,‘l = suminf UNIV f’] >>
    simp[GSYM suminf_univ] >> qpat_x_assum ‘0 < e’ mp_tac >> qid_spec_tac ‘e’ >>
    simp[GSYM LIM_SEQUENTIALLY] >> qunabbrev_tac ‘sf’ >>
    qspecl_then [‘f’,‘l’,‘UNIV’] mp_tac $ GSYM sums_def >> simp[] >> disch_then kall_tac >>
    qunabbrev_tac ‘l’ >> simp[Abbr ‘f’,SUMS_INFSUM,EXP_POLYNOMIAL_SUMMABLE]
QED
