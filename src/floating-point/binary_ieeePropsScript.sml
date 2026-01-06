Theory binary_ieeeProps
Ancestors binary_ieee real words arithmetic
Libs realSimps RealArith

val _ = augment_srw_ss[REAL_ARITH_ss]

Overload precision[local] = “fcp$dimindex”
Overload f2r[local] = “float_to_real”
Overload bias[local] = “words$INT_MAX”
Overload sign[local] = “fsign”

Theorem Sign_cases:
  ∀f. f.Sign = 0w ∨ f.Sign = 1w
Proof
  gen_tac >>
  qspec_then ‘f.Sign’ strip_assume_tac ranged_word_nchotomy >>
  fs[dimword_1]
QED

Theorem float_value_eq_float_to_real:
  float_is_finite f ⇒ float_value f = Float (float_to_real f)
Proof
  simp[float_is_finite_thm, float_value_def, PULL_EXISTS, AllCaseEqs()]
QED

Theorem float_value_float_to_real:
  float_value f = Float r ⇒ float_to_real f = r
Proof
  metis_tac[float_is_finite_thm,float_value_eq_float_to_real,float_value_11]
QED

Definition mantissa_def:
  mantissa (x: (τ, χ) float):num =
  if x.Exponent = 0w
    then w2n x.Significand
    else 2 ** precision (:τ) + w2n x.Significand
End

Theorem abs_next_hi_EQN:
  float_is_finite f ⇒ abs (f2r (next_hi f)) = abs (f2r f) + ulpᶠ f
Proof
  simp[GSYM next_hi_difference, float_ulp_def] >> strip_tac >>
  Cases_on ‘f2r f = 0’ >> simp[] >>
  ‘abs (f2r f) < abs (f2r (next_hi f)) ∧ (0 ≤ f2r (next_hi f) ⇔ 0 ≤ f2r f)’
    suffices_by
    simp[REAL_ARITH “abs x < abs y ∧ (0 ≤ x ⇔ 0 ≤ y) ⇒
                     abs (y - x) = abs y - abs x”] >>
  simp[next_hi_larger] >> simp[EQ_IMP_THM] >> rpt strip_tac >> gvs[]
QED

Theorem float_to_real_ulp:
  f2r f = sign f * &mantissa f * ulpᶠ f
Proof
  simp[float_to_real_def] >>
  rw[mantissa_def, float_ulp_def, ULP_def, REAL_POW_ADD] >>
  gvs[real_div, REAL_LDISTRIB, REAL_OF_NUM_POW]
QED

Theorem realsub_lemma[local]: x ≤ y ⇒ (real_of_num (y - x) = &y - &x)
Proof simp[REAL_SUB] >> rw[]
QED

Theorem ABS_REFL'[local] = iffRL ABS_REFL

Theorem positive_representable:
  r = (2r pow k * &(x:num)) / (2 pow (bias (:χ) + precision(:τ))) ∧
  0 < k ∧
  k < 2 ** dimindex(:χ) - 1 ∧
  x < 2 ** (precision(:τ) + 1)
⇒
  ∃f:(τ,χ)float. float_value f = Float r
Proof
  strip_tac >>
  Cases_on ‘x = 0’ >- (gvs[] >> qexists_tac ‘POS0’ >> simp[]) >>
  Cases_on ‘2 ** precision(:τ) ≤ x’
  >- (qexists_tac ‘
       <| Significand := n2w (x - 2 ** precision(:τ));
          Exponent := n2w k;
          Sign := n2w 0 |>’ >>
      simp[float_value_def, word_T_def, dimword_def, UINT_MAX_def,
           float_to_real_def, dimword_def, real_div, REAL_POW_ADD] >>
      ‘x - 2 ** precision(:τ) < 2 ** precision(:τ)’ by fs[EXP_ADD] >>
      simp[REAL_INV_MUL, REAL_SUB_RDISTRIB, realsub_lemma,
           GSYM REAL_OF_NUM_POW] >>
      ‘∀r:real. 1 + (r - 1) = r’ by simp[] >> simp[]) >>
  gvs[NOT_LESS_EQUAL] >>
  qabbrev_tac ‘lx = LOG 2 x’ >>
  ‘0 < x’ by simp[] >>
  ‘2 ** lx ≤ x ∧ x < 2 ** (lx + 1)’
    by simp[logrootTheory.LOG,GSYM ADD1,Abbr‘lx’] >>
  qabbrev_tac ‘P = 2n ** precision (:τ)’ >>
  Cases_on ‘precision (:τ) < k + lx’
  >- (qexists_tac ‘
       <| Significand := n2w (x * 2 ** (precision(:τ) - lx) - P) ;
       Exponent := n2w (k + lx - precision(:τ)) ;
       Sign := n2w 0 |>’ >>
      simp[float_value_def, word_T_def, dimword_def, UINT_MAX_def] >>
      ‘lx ≤ precision(:τ)’
        by (spose_not_then strip_assume_tac >> fs[NOT_LESS_EQUAL] >>
            ‘2n ** precision(:τ) < 2 ** lx’ by simp[] >>
            simp[Abbr‘P’]) >>
      ‘k + lx - precision(:τ) ≤ k’ by simp[] >>
      ‘k + lx - precision(:τ) < 2 ** precision(:χ)’ by simp[] >>
      simp[] >>
      simp[float_to_real_def, dimword_def] >>
      simp[REAL_POW_ADD, real_div, REAL_INV_MUL] >>
      simp[GSYM pow_inv_mul_invlt, REAL_POW_ADD] >>
      ‘x * 2 ** (precision(:τ) - lx) - P < P’
        by (qabbrev_tac ‘Q = precision(:τ) - lx’ >>
            ‘x * 2 ** Q < 2 ** (lx + 1) * 2 ** Q’ by simp[] >>
            ‘lx + Q = precision(:τ)’ by simp[Abbr‘Q’] >>
            ‘x * 2 ** Q < 2 ** (lx + 1 + Q)’ by metis_tac[EXP_ADD] >>
            ‘lx + 1 + Q = precision(:τ) + 1’ by simp[] >>
            pop_assum SUBST_ALL_TAC >>
            fs[EXP_ADD, Abbr‘P’]) >>
      simp[] >>
      ‘P ≤ x * 2 ** (precision(:τ) - lx)’
        by (qabbrev_tac ‘Q = precision(:τ) - lx’ >>
            ‘2 ** lx * 2 ** Q ≤ x * 2 ** Q’ by simp[] >>
            ‘P = 2 ** lx * 2 ** Q’ suffices_by simp[] >>
            simp[GSYM EXP_ADD, Abbr‘Q’]) >>
      simp[realsub_lemma, REAL_SUB_RDISTRIB] >>
      ‘&P = 2 pow precision(:τ)’ by simp[GSYM REAL_OF_NUM_POW, Abbr‘P’]>>
      simp[] >>
      ‘∀x:real. 1 + (x - 1) = x’ by simp[] >> simp[] >>
      simp_tac bool_ss [GSYM REAL_OF_NUM_POW, GSYM REAL_MUL,
                        REAL_MUL_ASSOC] >>
      simp[GSYM pow_inv_mul_invlt] >>
      Cases_on ‘lx = precision(:τ)’ >> simp[] >>
      simp[GSYM pow_inv_mul_invlt] >> gs[REAL_POW_ADD]) >>
  gvs[NOT_LESS] >>
  qexists_tac‘
   <| Sign := 0w; Significand := n2w (x * 2 ** (k-1)); Exponent := 0w
   |>’ >>
  simp[float_value_def, float_to_real_def, word_T_def, UINT_MAX_def,
       dimword_def] >>
  simp[real_div, REAL_POW_ADD,REAL_INV_MUL] >>
  ‘∃k0. k = k0 + 1’ by (Cases_on ‘k’ >> fs[ADD1]) >>
  pop_assum SUBST_ALL_TAC >> simp[] >>
  simp[REAL_MUL, REAL_OF_NUM_POW] >>
  ‘x * 2 ** k0 < P’
    by (‘x * 2 ** k0 < 2 ** (lx + 1) * 2 ** k0’ by simp[] >>
        ‘x * 2 ** k0 < 2 ** (lx + 1 + k0)’ by metis_tac[EXP_ADD] >>
        irule (DECIDE “x:num < y ∧ y ≤ z ⇒ x < z”) >>
        qexists_tac ‘2n ** (lx + 1 + k0)’ >> simp[] >>
        simp[Abbr‘P’]) >>
  simp[] >>
  gs[REAL_POW_ADD, Abbr‘P’, REAL_OF_NUM_POW, EXP_ADD] >>
  RULE_ASSUM_TAC (REWRITE_RULE [GSYM REAL_MUL, REAL_MUL_ASSOC]) >>
  simp[]
QED

Theorem negative_representable:
  r = -(2r pow k * &(x:num)) / (2 pow (bias (:χ) + precision(:τ))) ∧
  0 < k ∧ k < 2 ** precision(:χ) - 1 ∧
  x < 2 ** (precision(:τ) + 1)
  ⇒
  ∃f:(τ,χ)float. float_value f = Float r
Proof
  strip_tac >>
  mp_tac (Q.INST [‘r’ |-> ‘-r’] positive_representable) >>
  impl_tac >- simp[neg_rat] >>
  strip_tac >>
  qexists_tac ‘float_negate f’ >>
  simp[float_negate]
QED

Theorem representables:
  abs r = (2r pow k * &(x:num)) / (2 pow (bias (:χ) + precision(:τ))) ∧
  0 < k ∧ k < 2 ** precision(:χ) - 1 ∧
  x < 2 ** (precision(:τ) + 1)
  ⇒
  ∃f:(τ,χ)float. float_value f = Float r
Proof
  rw[abs, Excl "REALMULCANON", Excl "RMUL_EQNORM3", Excl "RMUL_EQNORM4"]
  >- metis_tac[positive_representable] >>
  fs[Once REAL_NEG_EQ, Excl "REALMULCANON"] >>
  fs[Excl "REALMULCANON", neg_rat] >> metis_tac[negative_representable]
QED

Theorem mantissa_UB:
  mantissa (f:(α,β)float) < 2 * 2 ** precision(:α)
Proof
  rw[mantissa_def] >> Cases_on ‘f.Significand’ >> gvs[dimword_def]
QED

Theorem smaller_floats_representable_lemma:
  2 ≤ precision (:τ) ∧
  float_value (b:(χ,τ)float) = Float rb ∧
  rr = real_of_int i * ulpᶠ b ∧
  abs rr ≤ abs rb
  ⇒
  ∃r:(χ, τ) float. float_value r = Float rr
Proof
  rpt strip_tac >>
  Cases_on ‘rb = 0’ >- (gvs[REAL_ABS_LE0] >> qexists_tac ‘POS0’ >> simp[]) >>
  wlog_tac ‘0 < rb’ [‘b’, ‘rb’]
  >- (first_x_assum $ qspecl_then [‘float_negate b’, ‘-rb’] mp_tac >>
      simp[float_negate]) >>
  gs[ABS_REFL'] >>
  Cases_on ‘i = 0’ >- (qexists_tac ‘POS0’ >> simp[]) >>
  wlog_tac ‘0 < rr’ [‘rr’, ‘i’]
  >- (first_x_assum $ qspecl_then [‘-rr’, ‘-i’] mp_tac >> simp[] >>
      gs[REAL_NOT_LT] >> impl_tac
      >- gvs[REAL_LE_LT] >>
      simp[GSYM float_negate, REAL_MUL_LNEG] >> metis_tac[]) >>
  gs[ABS_REFL'] >>
  ‘∃n. i = &n’
    by (Cases_on ‘i’ using integerTheory.INT_NUM_CASES>> gs[] >>
        gs[REAL_MUL_RNEG] >>
        ‘0 < ulpᶠ b * &n’ by simp[REAL_LT_MUL] >>
        gs[]) >> gvs[] >>
  drule_then (SUBST_ALL_TAC o SYM) float_value_float_to_real >>
  gvs[float_to_real_ulp] >>
  ‘sign b = 1’
    by (qspec_then ‘b’ strip_assume_tac Sign_cases >> simp[] >>
        ‘float_is_finite b ∧ ¬float_is_zero b’
          by (simp[float_is_finite_thm, float_is_zero_float_value_EQ0] >>
              rpt strip_tac >> gvs[]) >>
        gvs[]) >>
  gvs[] >>
  irule representables >> simp[ABS_MUL, float_ulp_def, ULP_def] >>
  irule_at (Pos last) EQ_REFL >> rw[]
  >- (irule LESS_EQ_LESS_TRANS >> qexists_tac ‘mantissa b’ >> simp[] >>
      REWRITE_TAC [GSYM REAL_LT, GSYM REAL_OF_NUM_POW, REAL_POW_ADD,
                   POW_1] >>
      simp[REAL_OF_NUM_POW,mantissa_UB])
  >- simp[DECIDE “x:num < y - z ⇔ x + z < y”]
  >- (gs[float_value_def, AllCaseEqs()] >>
      gvs[word_T_def, UINT_MAX_def] >>
      Cases_on ‘b.Exponent’ >> gvs[dimword_def])
  >- (Cases_on ‘b.Exponent’ >> gvs[dimword_def])
QED

Theorem ulp_multiples_representable:
  float_is_finite f ∧ 2 ≤ precision(:τ) ∧
  abs r = &n * ulpᶠ (f:(χ,τ) float) ∧ n ≤ 2 ** precision(:χ) ⇒
  ∃f':(χ,τ)float. float_value f' = Float r
Proof
  reverse (Cases_on ‘f.Exponent = 0w’)
  >- (strip_tac >> irule smaller_floats_representable_lemma >> simp[] >>
      gs[float_is_finite_thm] >> first_assum $ irule_at (Pos hd) >>
      qexists_tac ‘if 0 < r then &n else -&n’ >> conj_tac >- rw[] >>
      drule float_value_float_to_real >>
      simp[float_to_real_ulp] >> rw[] >> simp[ABS_MUL] >>
      rw[mantissa_def]) >>
  strip_tac >>
  qabbrev_tac ‘sn = if 0 < r then 0w : word1 else 1w’ >>
  qabbrev_tac ‘ex = if n = 2 ** precision(:χ) then 1w : bool[τ] else 0w’ >>
  qabbrev_tac ‘m = if n = 2 ** precision(:χ) then 0w : bool[χ] else n2w n’>>
  qexists_tac ‘<| Sign := sn; Significand := m; Exponent := ex|>’ >>
  simp[float_to_real_def, float_value_def, AllCaseEqs()] >>
  simp[Abbr‘ex’] >> rw[] >>
  gvs[word_T_def, UINT_MAX_def, dimword_def,
      DECIDE “x:num ≠ y - x ⇔ 2 * x ≠ y”] >>
  simp[Abbr‘m’] >>
  Cases_on ‘0 < r’ >>
  gs[Abbr‘sn’, ABS_REFL', float_ulp_def, ULP_def, dimword_def, REAL_POW_ADD,
     REAL_OF_NUM_POW, EXP_ADD] >>
  full_simp_tac (bool_ss ++ RMULCANON_ss ++ RMULRELNORM_ss) [GSYM REAL_MUL] >>
  gvs[] >>
  ‘abs r = -r’ by simp[] >> gvs[]
QED

Theorem largest_props[simp]:
  ¬(largest (:α # β) < 0) ∧ largest (:α # β) ≠ 0 ∧ 0 < largest(:α # β) ∧
  0 ≤ largest (:α # β) ∧ ¬(largest(:α # β) ≤ 0)
Proof
  ‘0 < largest(:α # β)’ suffices_by simp[] >>
  simp[largest_def, UINT_MAX_def, dimword_def] >>
  irule REAL_LT_MUL >> simp[REAL_ARITH “0r < x - y ⇔ y < x”] >>
  simp[REAL_OF_NUM_POW, DECIDE “1n < 2 * c ⇔ 1 ≤ c”]
QED

Theorem threshold_props[simp]:
  ¬(threshold (:α # β) < 0) ∧ threshold (:α # β) ≠ 0 ∧ 0 < threshold(:α # β) ∧
  0 ≤ threshold (:α # β) ∧ ¬(threshold(:α # β) ≤ 0)
Proof
  ‘0 < threshold(:α # β)’ suffices_by REAL_ARITH_TAC >>
  irule REAL_LT_TRANS >> qexists ‘largest(:α#β)’ >>
  simp[largest_lt_threshold]
QED

Theorem is_closest_0_float_to_real:
  is_closest float_is_finite 0 (b:(α,β)float) ⇔ float_to_real b = 0
Proof
  simp[is_closest_def, float_is_finite_def, IN_DEF] >>
  Cases_on ‘float_value b’ >> fs[float_value_def, CaseEq "bool"]
  >- (reverse eq_tac >> rw[] >>
      first_x_assum (qspec_then ‘float_plus_zero(:α#β)’ mp_tac) >>
      simp[float_plus_zero_def, word_T_def, UINT_MAX_def, dimword_def] >>
      assume_tac (DIMINDEX_GT_0 |> INST_TYPE [alpha |-> beta]) >> simp[]) >>
  simp[float_to_real_def, word_T_def, UINT_MAX_def, NOT_LESS_EQUAL,
       dimword_def, AllCaseEqs(), real_div] >>
  irule (REAL_ARITH “0 ≤ y ⇒ 1 + y ≠ 0”) >> simp[REAL_LE_MUL]
QED

Theorem round_representable:
  2 ≤ precision(:β) ∧ float_is_finite (f:(α,β)float) ⇒
  ∃f':(α,β)float. float_is_finite f' ∧ round m (f2r f) = f' ∧ f2r f' = f2r f
Proof
  strip_tac >>
  Cases_on ‘f2r f = 0’
  >- (simp [] >> simp[round_def, real_gt, real_ge] >>
      Cases_on ‘m’ >>
      simp[closest_def, closest_such_def] >>
      SELECT_ELIM_TAC >> simp[] >>
      conj_tac >>~-
      ([‘$? _’], qexists ‘POS0’ >> simp[is_closest_def, word_lsb_n2w, IN_DEF]) >>
      simp[is_closest_def, IN_DEF]) >>
  qexists ‘f’ >> simp[] >>
  simp[round_def] >>
  ‘float_value f = Float (f2r f)’ by simp[float_value_eq_float_to_real] >>
  assume_tac (INST_TYPE [“:χ” |-> “:β”, “:τ” |-> “:α”] largest_lt_threshold) >>
  drule_all_then strip_assume_tac float_bounds >> simp[] >>
  Cases_on ‘m’ >> simp[closest_such_def, closest_def] >>
  SELECT_ELIM_TAC >> simp[is_closestP_finite_float_exists] >> rpt conj_tac >>~-
  ([‘$? _’], qexists ‘f’ >> simp[is_closest_def]) >> rpt strip_tac >>
  qpat_x_assum ‘is_closest _ _ _ (* a *)’ mp_tac >>
  simp[is_closest_def, IN_DEF] >> rpt strip_tac >>
  first_x_assum $ qspec_then ‘f’ mp_tac >> simp[REAL_ABS_LE0] >>
  simp[float_to_real_eq, float_is_zero_to_real]
QED

Theorem round_representable_nonzero:
  2 ≤ precision(:β) ∧ float_is_finite (f:(α,β)float) ∧ f2r f ≠ 0 ⇒
  round m (f2r f) = f
Proof
  rpt strip_tac >>
  drule_all_then (qspec_then ‘m’ strip_assume_tac) round_representable >>
  simp[] >> gvs[float_to_real_eq, float_is_zero_to_real]
QED

Theorem float_to_real_EQ0_cases:
  f2r f = 0 ⇔ f = POS0 ∨ f = NEG0
Proof
  simp[EQ_IMP_THM, DISJ_IMP_THM] >>
  simp[GSYM float_is_zero_to_real, float_is_zero] >>
  simp[float_plus_zero_def, float_minus_zero_def, float_component_equality] >>
  Cases_on ‘f.Sign’ >> gvs[dimword_1]
QED

Theorem round_representable_zero:
  2 ≤ precision(:β) ⇒ round m 0 = (POS0:(α,β)float) ∨ round m 0 = (NEG0:(α,β)float)
Proof
  strip_tac >>
  drule_then (qspecl_then [‘m’, ‘POS0’] strip_assume_tac) round_representable >>
  gvs[] >>
  metis_tac[float_to_real_round0, float_to_real_EQ0_cases]
QED
