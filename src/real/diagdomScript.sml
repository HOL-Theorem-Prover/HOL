(* ------------------------------------------------------------------------- *)
(* Diagonal dominance and positive (semi)definite quadratic forms            *)
(* ------------------------------------------------------------------------- *)
(* A matrix is a function A : num -> num -> real read on the indices < n,
   and sums are real_sigma's sum over count n.  For weights d i > 0, row i
   of A is (weighted) diagonally dominant when

       sum (count n DELETE i) (\j. d j * abs (A i j)) <= d i * A i i,

   the unweighted criterion being d = \i. 1.  A symmetric matrix whose rows
   are all dominant has a non-negative quadratic form, and a positive one
   when every row is strictly dominant (for symmetric matrices, the
   corollary usually obtained from Gershgorin's circle theorem).

   No eigenvalues are needed.  With H i j = d i * A i j * d j and
   z i = x i / d i, every term z i * H i j * z j is bounded below by AM-GM,
   and the bounds sum, by the symmetry of H, to

       sum_i z i * z i * (2 * H i i - sum_j abs (H i j)),

   whose terms are non-negative (positive where z i <> 0 and the row is
   strictly dominant).                                                       *)

Theory diagdom
Ancestors
  pred_set real real_sigma
Libs
  realLib

(* REAL_ARITH eliminates abs everywhere, also under the binder of a sum,
   and then fails; so every maximal sum outside a binder is generalised to
   a variable first. *)
val Sum_tm = prim_mk_const {Thy = "real_sigma", Name = "Sum"};
fun sum_atoms t =
  if is_comb t then
    let val (c, args) = strip_comb t
    in
      if same_const c Sum_tm andalso length args = 2 then [t]
      else sum_atoms (rator t) @ sum_atoms (rand t)
    end
  else [];
fun GEN_SUMS_TAC (g as (_, w)) =
  MAP_EVERY (fn t => SPEC_TAC (t, genvar (type_of t)))
            (op_mk_set aconv (sum_atoms w)) g;
val SUM_ARITH_TAC = GEN_SUMS_TAC >> REAL_ARITH_TAC;

(* ------------------------------------------------------------------------- *)
(* Double sums over count n                                                  *)
(* ------------------------------------------------------------------------- *)

Theorem sum_sub3[local]:
  !n (a:num -> real) b c.
    sum (count n) (\x. a x - b x - c x) =
    sum (count n) a - sum (count n) b - sum (count n) c
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [SUM_SUB', FINITE_COUNT]
QED

Theorem dsum_le[local]:
  !n (f:num -> num -> real) g.
    (!i j. i < n /\ j < n ==> f i j <= g i j) ==>
    sum (count n) (\i. sum (count n) (\j. f i j)) <=
    sum (count n) (\i. sum (count n) (\j. g i j))
Proof
  rpt strip_tac >>
  irule SUM_LE' >> simp_tac (srw_ss()) [FINITE_COUNT] >> rpt strip_tac >>
  irule SUM_LE' >> simp_tac (srw_ss()) [FINITE_COUNT] >> rpt strip_tac >>
  first_x_assum irule >> asm_rewrite_tac[]
QED

Theorem dsum_eq[local]:
  !n (f:num -> num -> real) g.
    (!i j. i < n /\ j < n ==> f i j = g i j) ==>
    sum (count n) (\i. sum (count n) (\j. f i j)) =
    sum (count n) (\i. sum (count n) (\j. g i j))
Proof
  rpt strip_tac >>
  irule SUM_EQ' >> simp_tac (srw_ss()) [] >> rpt strip_tac >>
  irule SUM_EQ' >> simp_tac (srw_ss()) [] >> rpt strip_tac >>
  first_x_assum irule >> asm_rewrite_tac[]
QED

Theorem dsum_sub3[local]:
  !n (a:num -> num -> real) b c.
    sum (count n) (\i. sum (count n) (\j. a i j - b i j - c i j)) =
    sum (count n) (\i. sum (count n) (\j. a i j)) -
    sum (count n) (\i. sum (count n) (\j. b i j)) -
    sum (count n) (\i. sum (count n) (\j. c i j))
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [SUM_SUB', FINITE_COUNT]
QED

Theorem dsum_swap[local]:
  !n (f:num -> num -> real).
    sum (count n) (\i. sum (count n) (\j. f j i)) =
    sum (count n) (\i. sum (count n) (\j. f i j))
Proof
  rpt gen_tac >>
  qspecl_then [`\i j. f j i`, `n`, `n`] mp_tac SUM_SWAP_COUNT >> BETA_TAC >>
  disch_then ACCEPT_TAC
QED

Theorem dsum_delta[local]:
  !n (c:num -> real).
    sum (count n) (\i. sum (count n) (\j. if j = i then c i else 0)) =
    sum (count n) c
Proof
  rpt gen_tac >> irule SUM_EQ' >> rpt strip_tac >> BETA_TAC >>
  rewrite_tac[SUM_DELTA] >> asm_rewrite_tac[]
QED

Theorem dsum_rmul_row[local]:
  !n (f:num -> num -> real) (c:num -> real).
    sum (count n) (\i. sum (count n) (\j. f i j * c i)) =
    sum (count n) (\i. sum (count n) (\j. f i j) * c i)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [SUM_RMUL]
QED

(* ------------------------------------------------------------------------- *)
(* The unweighted core: rows of H dominant in the sense                      *)
(*   sum_j abs (H i j) <= 2 * H i i  (the diagonal counted on both sides)    *)
(* ------------------------------------------------------------------------- *)

Theorem pw_diag[local]:
  !a h:real.
    2 * h * (a * a) - abs h * (a * a / 2) - abs h * (a * a / 2) <= a * h * a
Proof
  rpt gen_tac >> `0 <= a * a` by rewrite_tac[REAL_LE_SQUARE] >>
  Cases_on `0 <= h`
  >- (`abs h = h` by asm_rewrite_tac[ABS_REFL] >> pop_assum SUBST1_TAC >>
      SUM_ARITH_TAC)
  >> `abs h = -h` by (pop_assum mp_tac >> SUM_ARITH_TAC) >>
  pop_assum SUBST1_TAC >>
  `0 <= -h * (a * a)`
     by (irule REAL_LE_MUL >> asm_rewrite_tac[] >> pop_assum mp_tac >>
         SUM_ARITH_TAC) >>
  pop_assum mp_tac >> SUM_ARITH_TAC
QED

Theorem pw_off[local]:
  !a b h:real. 0 - abs h * (a * a / 2) - abs h * (b * b / 2) <= a * h * b
Proof
  rpt gen_tac >> Cases_on `0 <= h`
  >- (`abs h = h` by asm_rewrite_tac[ABS_REFL] >> pop_assum SUBST1_TAC >>
      `0 <= h * ((a + b) * (a + b))`
         by (irule REAL_LE_MUL >> asm_rewrite_tac[REAL_LE_SQUARE]) >>
      pop_assum mp_tac >> SUM_ARITH_TAC)
  >> `abs h = -h` by (pop_assum mp_tac >> SUM_ARITH_TAC) >>
  pop_assum SUBST1_TAC >>
  `0 <= -h * ((a - b) * (a - b))`
     by (irule REAL_LE_MUL >> rewrite_tac[REAL_LE_SQUARE] >>
         pop_assum mp_tac >> SUM_ARITH_TAC) >>
  pop_assum mp_tac >> SUM_ARITH_TAC
QED

Theorem dd_lower[local]:
  !n (H:num -> num -> real) (z:num -> real).
    (!i j. i < n /\ j < n ==> H i j = H j i) ==>
    sum (count n)
        (\i. z i * z i * (2 * H i i - sum (count n) (\j. abs (H i j)))) <=
    sum (count n) (\i. sum (count n) (\j. z i * H i j * z j))
Proof
  rpt strip_tac >>
  `sum (count n) (\i. sum (count n) (\j.
       (if j = i then 2 * H i i * (z i * z i) else 0) -
       abs (H i j) * (z i * z i / 2) - abs (H i j) * (z j * z j / 2))) <=
   sum (count n) (\i. sum (count n) (\j. z i * H i j * z j))`
     by (HO_MATCH_MP_TAC dsum_le >> rpt strip_tac >> BETA_TAC >>
         Cases_on `j = i`
         >- (pop_assum SUBST_ALL_TAC >> rewrite_tac[pw_diag])
         >> qpat_x_assum `~(j = i)` (fn th => rewrite_tac[th, pw_off])) >>
  qspecl_then [`n`, `\i j. if j = i then 2 * H i i * (z i * z i) else 0`,
               `\i j. abs (H i j) * (z i * z i / 2)`,
               `\i j. abs (H i j) * (z j * z j / 2)`]
              (assume_tac o BETA_RULE) dsum_sub3 >>
  qspecl_then [`n`, `\i. 2 * H i i * (z i * z i)`]
              (assume_tac o BETA_RULE) dsum_delta >>
  qspecl_then [`n`, `\i j. abs (H i j)`, `\i. z i * z i / 2`]
              (assume_tac o BETA_RULE) dsum_rmul_row >>
  `sum (count n) (\i. sum (count n) (\j. abs (H i j) * (z j * z j / 2))) =
   sum (count n) (\i. sum (count n) (\j. abs (H i j) * (z i * z i / 2)))`
     by (qspecl_then [`n`, `\i j. abs (H i j) * (z j * z j / 2)`]
                     (SUBST1_TAC o SYM o BETA_RULE) dsum_swap >>
         HO_MATCH_MP_TAC dsum_eq >> rpt strip_tac >> BETA_TAC >>
         `H j i = H i j`
            by (qpat_x_assum `!i j. i < n /\ j < n ==> H i j = H j i` irule >>
                asm_rewrite_tac[]) >>
         pop_assum SUBST1_TAC >> REFL_TAC) >>
  qspecl_then [`n`, `\i. 2 * H i i * (z i * z i)`,
               `\i. sum (count n) (\j. abs (H i j)) * (z i * z i / 2)`,
               `\i. sum (count n) (\j. abs (H i j)) * (z i * z i / 2)`]
              (assume_tac o BETA_RULE) sum_sub3 >>
  `sum (count n)
       (\i. z i * z i * (2 * H i i - sum (count n) (\j. abs (H i j)))) =
   sum (count n)
       (\i. 2 * H i i * (z i * z i) -
            sum (count n) (\j. abs (H i j)) * (z i * z i / 2) -
            sum (count n) (\j. abs (H i j)) * (z i * z i / 2))`
     by (irule SUM_EQ' >> rpt strip_tac >> BETA_TAC >> SUM_ARITH_TAC) >>
  rpt (qpat_x_assum `_ = _` mp_tac) >> qpat_x_assum `_ <= _` mp_tac >>
  SUM_ARITH_TAC
QED

Theorem dd_core[local]:
  !n (H:num -> num -> real) (z:num -> real).
    (!i j. i < n /\ j < n ==> H i j = H j i) /\
    (!i. i < n ==> sum (count n) (\j. abs (H i j)) <= 2 * H i i) ==>
    0 <= sum (count n) (\i. sum (count n) (\j. z i * H i j * z j))
Proof
  rpt strip_tac >> irule REAL_LE_TRANS >>
  qexists_tac `sum (count n)
     (\i. z i * z i * (2 * H i i - sum (count n) (\j. abs (H i j))))` >>
  conj_tac
  >- (irule SUM_POS_LE >> rpt strip_tac >> BETA_TAC >>
      irule REAL_LE_MUL >> rewrite_tac[REAL_LE_SQUARE] >>
      `x < n` by (pop_assum mp_tac >> rewrite_tac[IN_COUNT]) >>
      `sum (count n) (\j. abs (H x j)) <= 2 * H x x`
         by (qpat_x_assum `!i. i < n ==> _` irule >>
             first_assum ACCEPT_TAC) >>
      pop_assum mp_tac >> SUM_ARITH_TAC)
  >> qspecl_then [`n`, `H`, `z`] mp_tac dd_lower >>
  impl_tac >- first_assum ACCEPT_TAC >> disch_then ACCEPT_TAC
QED

Theorem sq_pos[local]:
  !a:real. a <> 0 ==> 0 < a * a
Proof
  rpt strip_tac >> Cases_on `0 < a`
  >- (irule REAL_LT_MUL >> asm_rewrite_tac[])
  >> `0 < -a` by (ntac 2 (pop_assum mp_tac) >> REAL_ARITH_TAC) >>
  `0 < -a * -a` by (irule REAL_LT_MUL >> asm_rewrite_tac[]) >>
  pop_assum mp_tac >> REAL_ARITH_TAC
QED

Theorem dd_core_strict[local]:
  !n (H:num -> num -> real) (z:num -> real).
    (!i j. i < n /\ j < n ==> H i j = H j i) /\
    (!i. i < n ==> sum (count n) (\j. abs (H i j)) < 2 * H i i) /\
    (?i. i < n /\ z i <> 0) ==>
    0 < sum (count n) (\i. sum (count n) (\j. z i * H i j * z j))
Proof
  rpt strip_tac >> irule REAL_LTE_TRANS >>
  qexists_tac `sum (count n)
     (\i. z i * z i * (2 * H i i - sum (count n) (\j. abs (H i j))))` >>
  conj_tac
  >- (irule SUM_POS_LT >> rewrite_tac[FINITE_COUNT] >> conj_tac
      >- (rpt strip_tac >> BETA_TAC >>
          irule REAL_LE_MUL >> rewrite_tac[REAL_LE_SQUARE] >>
          `x < n` by (pop_assum mp_tac >> rewrite_tac[IN_COUNT]) >>
          `sum (count n) (\j. abs (H x j)) < 2 * H x x`
             by (qpat_x_assum `!i. i < n ==> _` irule >>
                 first_assum ACCEPT_TAC) >>
          pop_assum mp_tac >> SUM_ARITH_TAC)
      >> qexists_tac `i` >> rewrite_tac[IN_COUNT] >> BETA_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      irule REAL_LT_MUL >> conj_tac
      >- (irule sq_pos >> first_assum ACCEPT_TAC)
      >> `sum (count n) (\j. abs (H i j)) < 2 * H i i`
            by (qpat_x_assum `!i. i < n ==> _` irule >>
                first_assum ACCEPT_TAC) >>
      pop_assum mp_tac >> SUM_ARITH_TAC)
  >> qspecl_then [`n`, `H`, `z`] mp_tac dd_lower >>
  impl_tac >- first_assum ACCEPT_TAC >> disch_then ACCEPT_TAC
QED

(* ------------------------------------------------------------------------- *)
(* The weights: H i j = d i * G i j * d j and z i = x i / d i                *)
(* ------------------------------------------------------------------------- *)

Theorem div_cancel[local] = RealField.REAL_FIELD
  ``!a b g x y:real.
      a <> 0 /\ b <> 0 ==> x / a * (a * g * b) * (y / b) = x * g * y``

Theorem weighted_row[local]:
  !n (G:num -> num -> real) (d:num -> real) i.
    (!i. i < n ==> 0 < d i) /\ i < n ==>
    sum (count n) (\j. abs (d i * G i j * d j)) =
    d i * sum (count n) (\j. d j * abs (G i j))
Proof
  rpt strip_tac >> rewrite_tac[GSYM SUM_LMUL] >> irule SUM_EQ' >>
  rewrite_tac[IN_COUNT] >> rpt strip_tac >> BETA_TAC >>
  `0 < d i /\ 0 < d x`
     by (conj_tac >> qpat_x_assum `!i. i < n ==> 0 < d i` irule >>
         first_assum ACCEPT_TAC) >>
  `abs (d i) = d i /\ abs (d x) = d x`
     by (rewrite_tac[ABS_REFL] >> conj_tac >> irule REAL_LT_IMP_LE >>
         first_assum ACCEPT_TAC) >>
  rewrite_tac[ABS_MUL] >> asm_rewrite_tac[] >> SUM_ARITH_TAC
QED

Theorem weighted_form[local]:
  !n (G:num -> num -> real) (d:num -> real) (x:num -> real).
    (!i. i < n ==> 0 < d i) ==>
    sum (count n) (\i. sum (count n)
      (\j. x i / d i * (d i * G i j * d j) * (x j / d j))) =
    sum (count n) (\i. sum (count n) (\j. x i * G i j * x j))
Proof
  rpt strip_tac >> HO_MATCH_MP_TAC dsum_eq >> rpt strip_tac >> BETA_TAC >>
  irule div_cancel >> conj_tac >> irule REAL_POS_NZ >>
  qpat_x_assum `!i. i < n ==> 0 < d i` irule >> first_assum ACCEPT_TAC
QED

Theorem wdd_psd[local]:
  !n (G:num -> num -> real) (d:num -> real) (x:num -> real).
    (!i j. i < n /\ j < n ==> G i j = G j i) /\ (!i. i < n ==> 0 < d i) /\
    (!i. i < n ==>
         sum (count n) (\j. d j * abs (G i j)) <= 2 * d i * G i i) ==>
    0 <= sum (count n) (\i. sum (count n) (\j. x i * G i j * x j))
Proof
  rpt strip_tac >>
  qspecl_then [`n`, `\i j. d i * G i j * d j`, `\i. x i / d i`] mp_tac
              dd_core >> BETA_TAC >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >>
          `G i j = G j i`
             by (qpat_x_assum `!i j. i < n /\ j < n ==> G i j = G j i`
                   irule >> asm_rewrite_tac[]) >>
          pop_assum SUBST1_TAC >> SUM_ARITH_TAC)
      >> rpt strip_tac >>
      qspecl_then [`n`, `G`, `d`, `i`] mp_tac weighted_row >>
      impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then SUBST1_TAC >>
      `0 < d i` by (qpat_x_assum `!i. i < n ==> 0 < d i` irule >>
                    first_assum ACCEPT_TAC) >>
      `sum (count n) (\j. d j * abs (G i j)) <= 2 * d i * G i i`
         by (qpat_x_assum `!i. i < n ==> sum _ _ <= _` irule >>
             first_assum ACCEPT_TAC) >>
      `d i * sum (count n) (\j. d j * abs (G i j)) <=
       d i * (2 * d i * G i i)`
         by (irule REAL_LE_LMUL_IMP >> asm_rewrite_tac[] >>
             irule REAL_LT_IMP_LE >> asm_rewrite_tac[]) >>
      pop_assum mp_tac >> SUM_ARITH_TAC)
  >> qspecl_then [`n`, `G`, `d`, `x`] mp_tac weighted_form >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then SUBST1_TAC >> disch_then ACCEPT_TAC
QED

Theorem wdd_pd[local]:
  !n (G:num -> num -> real) (d:num -> real) (x:num -> real).
    (!i j. i < n /\ j < n ==> G i j = G j i) /\ (!i. i < n ==> 0 < d i) /\
    (!i. i < n ==>
         sum (count n) (\j. d j * abs (G i j)) < 2 * d i * G i i) /\
    (?i. i < n /\ x i <> 0) ==>
    0 < sum (count n) (\i. sum (count n) (\j. x i * G i j * x j))
Proof
  rpt strip_tac >>
  qspecl_then [`n`, `\i j. d i * G i j * d j`, `\i. x i / d i`] mp_tac
              dd_core_strict >> BETA_TAC >>
  impl_tac
  >- (rpt conj_tac
      >- (rpt strip_tac >>
          `G i' j = G j i'`
             by (qpat_x_assum `!i j. i < n /\ j < n ==> G i j = G j i`
                   irule >> asm_rewrite_tac[]) >>
          pop_assum SUBST1_TAC >> SUM_ARITH_TAC)
      >- (rpt strip_tac >>
          qspecl_then [`n`, `G`, `d`, `i'`] mp_tac weighted_row >>
          impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
          disch_then SUBST1_TAC >>
          `0 < d i'` by (qpat_x_assum `!i. i < n ==> 0 < d i` irule >>
                         first_assum ACCEPT_TAC) >>
          `sum (count n) (\j. d j * abs (G i' j)) < 2 * d i' * G i' i'`
             by (qpat_x_assum `!i. i < n ==> sum _ _ < _` irule >>
                 first_assum ACCEPT_TAC) >>
          `d i' * sum (count n) (\j. d j * abs (G i' j)) <
           d i' * (2 * d i' * G i' i')`
             by (qspecl_then [`d i'`, `sum (count n) (\j. d j * abs (G i' j))`,
                              `2 * d i' * G i' i'`] mp_tac REAL_LT_LMUL >>
                 impl_tac >- first_assum ACCEPT_TAC >>
                 disch_then (fn th => rewrite_tac[th]) >>
                 first_assum ACCEPT_TAC) >>
          pop_assum mp_tac >> SUM_ARITH_TAC)
      >> qexists_tac `i` >> conj_tac >- first_assum ACCEPT_TAC >>
      strip_tac >>
      `d i <> 0` by (irule REAL_POS_NZ >>
                     qpat_x_assum `!i. i < n ==> 0 < d i` irule >>
                     first_assum ACCEPT_TAC) >>
      `x i / d i * d i = x i`
         by (irule REAL_DIV_RMUL >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `x i / d i = 0`
        (fn th => qpat_x_assum `x i / d i * d i = x i`
                    (mp_tac o REWRITE_RULE [th])) >>
      rewrite_tac[REAL_MUL_LZERO] >> qpat_x_assum `x i <> 0` mp_tac >>
      SUM_ARITH_TAC)
  >> qspecl_then [`n`, `G`, `d`, `x`] mp_tac weighted_form >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then SUBST1_TAC >> disch_then ACCEPT_TAC
QED

(* ------------------------------------------------------------------------- *)
(* The textbook row condition (off-diagonal sum against the diagonal)        *)
(* ------------------------------------------------------------------------- *)

Theorem row_full[local]:
  !n (A:num -> num -> real) (d:num -> real) i.
    (!j. j < n ==> 0 < d j) /\ i < n ==>
    sum (count n) (\j. d j * abs (A i j)) =
    d i * abs (A i i) + sum (count n DELETE i) (\j. d j * abs (A i j)) /\
    0 <= sum (count n DELETE i) (\j. d j * abs (A i j))
Proof
  rpt strip_tac
  >- (qspecl_then [`\j. d j * abs (A i j)`, `count n`, `i`]
                  (mp_tac o BETA_RULE) SUM_DELETE >>
      rewrite_tac[FINITE_COUNT, IN_COUNT] >> asm_rewrite_tac[] >>
      disch_then SUBST1_TAC >> SUM_ARITH_TAC)
  >> irule SUM_POS_LE >>
  rewrite_tac[FINITE_DELETE, FINITE_COUNT, IN_DELETE, IN_COUNT] >>
  rpt strip_tac >> BETA_TAC >> irule REAL_LE_MUL >> rewrite_tac[ABS_POS] >>
  irule REAL_LT_IMP_LE >> qpat_x_assum `!j. j < n ==> 0 < d j` irule >>
  first_assum ACCEPT_TAC
QED

Theorem pos_cancel[local]:
  !a b:real. 0 < a /\ 0 <= a * b ==> 0 <= b
Proof
  rpt strip_tac >> qspecl_then [`a`, `0`, `b`] mp_tac REAL_LE_LMUL >>
  asm_rewrite_tac[REAL_MUL_RZERO]
QED

Theorem row_le[local]:
  !n (A:num -> num -> real) (d:num -> real) i.
    (!j. j < n ==> 0 < d j) /\ i < n /\
    sum (count n DELETE i) (\j. d j * abs (A i j)) <= d i * A i i ==>
    sum (count n) (\j. d j * abs (A i j)) <= 2 * d i * A i i
Proof
  rpt strip_tac >>
  qspecl_then [`n`, `A`, `d`, `i`] mp_tac row_full >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> pop_assum mp_tac >> pop_assum SUBST1_TAC >> strip_tac >>
  `0 < d i` by (qpat_x_assum `!j. j < n ==> 0 < d j` irule >>
                first_assum ACCEPT_TAC) >>
  `0 <= A i i`
     by (irule pos_cancel >> qexists_tac `d i` >> conj_tac
         >- first_assum ACCEPT_TAC >>
         qpat_x_assum `0 <= sum _ _` mp_tac >>
         qpat_x_assum `sum _ _ <= d i * A i i` mp_tac >> SUM_ARITH_TAC) >>
  `abs (A i i) = A i i` by asm_rewrite_tac[ABS_REFL] >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `sum _ _ <= d i * A i i` mp_tac >> SUM_ARITH_TAC
QED

Theorem row_lt[local]:
  !n (A:num -> num -> real) (d:num -> real) i.
    (!j. j < n ==> 0 < d j) /\ i < n /\
    sum (count n DELETE i) (\j. d j * abs (A i j)) < d i * A i i ==>
    sum (count n) (\j. d j * abs (A i j)) < 2 * d i * A i i
Proof
  rpt strip_tac >>
  qspecl_then [`n`, `A`, `d`, `i`] mp_tac row_full >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> pop_assum mp_tac >> pop_assum SUBST1_TAC >> strip_tac >>
  `0 < d i` by (qpat_x_assum `!j. j < n ==> 0 < d j` irule >>
                first_assum ACCEPT_TAC) >>
  `0 <= A i i`
     by (irule pos_cancel >> qexists_tac `d i` >> conj_tac
         >- first_assum ACCEPT_TAC >>
         qpat_x_assum `0 <= sum _ _` mp_tac >>
         qpat_x_assum `sum _ _ < d i * A i i` mp_tac >> SUM_ARITH_TAC) >>
  `abs (A i i) = A i i` by asm_rewrite_tac[ABS_REFL] >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `sum _ _ < d i * A i i` mp_tac >> SUM_ARITH_TAC
QED

(* ------------------------------------------------------------------------- *)
(* The two criteria                                                          *)
(* ------------------------------------------------------------------------- *)

Theorem DIAGONALLY_DOMINANT_PSD:
  !n (A:num -> num -> real) (d:num -> real).
    (!i j. i < n /\ j < n ==> A i j = A j i) /\ (!i. i < n ==> 0 < d i) /\
    (!i. i < n ==>
         sum (count n DELETE i) (\j. d j * abs (A i j)) <= d i * A i i) ==>
    !x. 0 <= sum (count n) (\i. sum (count n) (\j. x i * A i j * x j))
Proof
  rpt strip_tac >>
  qspecl_then [`n`, `A`, `d`, `x`] mp_tac wdd_psd >>
  impl_tac
  >- (rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
      rpt strip_tac >>
      qspecl_then [`n`, `A`, `d`, `i`] mp_tac row_le >>
      impl_tac
      >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          qpat_x_assum `!i. i < n ==> sum (count n DELETE i) _ <= _` irule >>
          first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC)
  >> disch_then ACCEPT_TAC
QED

Theorem DIAGONALLY_DOMINANT_PD:
  !n (A:num -> num -> real) (d:num -> real).
    (!i j. i < n /\ j < n ==> A i j = A j i) /\ (!i. i < n ==> 0 < d i) /\
    (!i. i < n ==>
         sum (count n DELETE i) (\j. d j * abs (A i j)) < d i * A i i) ==>
    !x. (?i. i < n /\ x i <> 0) ==>
        0 < sum (count n) (\i. sum (count n) (\j. x i * A i j * x j))
Proof
  rpt strip_tac >>
  qspecl_then [`n`, `A`, `d`, `x`] mp_tac wdd_pd >>
  impl_tac
  >- (rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- (rpt strip_tac >>
          qspecl_then [`n`, `A`, `d`, `i'`] mp_tac row_lt >>
          impl_tac
          >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
              qpat_x_assum `!i. i < n ==> sum (count n DELETE i) _ < _`
                irule >>
              first_assum ACCEPT_TAC) >>
          disch_then ACCEPT_TAC)
      >> qexists_tac `i` >> conj_tac >> first_assum ACCEPT_TAC)
  >> disch_then ACCEPT_TAC
QED
