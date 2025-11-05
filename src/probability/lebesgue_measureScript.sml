(* ========================================================================= *)
(*        Lebesgue Measure Theory (lebesgue_measure_hvgScript.sml)           *)
(*                                                                           *)
(*        (c) Copyright 2015,                                                *)
(*                       Muhammad Qasim,                                     *)
(*                       Osman Hasan,                                        *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*                                                                           *)
(*            Contact:  <m_qasi@ece.concordia.ca>                            *)
(*                                                                           *)
(* Note: This theory is inspired from isabelle                               *)
(* ------------------------------------------------------------------------- *)
(*  Equivalence of Lebesgue and Gauge (Henstock-Kurzweil) Integration        *)
(* ========================================================================= *)

Theory lebesgue_measure
Ancestors
  prim_rec arithmetic num pred_set combin cardinal While
  relation real seq transc real_sigma iterate topology metric
  real_topology integration sigma_algebra extreal_base extreal
  real_borel measure borel integer intreal lebesgue
  integral[qualified] lift_ieee[qualified]
Libs
  numLib pred_setLib hurdUtils jrhUtils realLib

val integral_def = integrationTheory.integral_def;

val ASM_ARITH_TAC = rpt (POP_ASSUM MP_TAC) >> ARITH_TAC; (* numLib *)
val DISC_RW_KILL = DISCH_TAC >> ONCE_ASM_REWRITE_TAC [] >> POP_ASSUM K_TAC;
fun METIS ths tm = prove(tm, METIS_TAC ths);

val _ = hide "top"; (* posetTheory *)
val _ = hide "nf";  (* relationTheory *)

val _ = intLib.deprecate_int ();
val _ = ratLib.deprecate_rat ();

(* Some proofs here are large with too many assumptions *)
val _ = set_trace "Goalstack.print_goal_at_top" 0;

(* ------------------------------------------------------------------------- *)
(*  Lebesgue sigma-algebra with the household Lebesgue measure (lebesgue)    *)
(* ------------------------------------------------------------------------- *)

Theorem absolutely_integrable_on_indicator :
    !A X. indicator A absolutely_integrable_on X <=>
          indicator A integrable_on X
Proof
    rpt GEN_TAC >> REWRITE_TAC [absolutely_integrable_on]
 >> EQ_TAC >> STRIP_TAC >> art []
 >> Suff ‘!x. abs(indicator A x) = indicator A x’
 >- (Rewr' >> METIS_TAC [ETA_AX])
 >> RW_TAC real_ss [indicator]
QED

Theorem has_integral_indicator_UNIV :
    !s A x. (indicator (s INTER A) has_integral x) UNIV =
            (indicator s has_integral x) A
Proof
    Know ‘!(s :real set) A. (\x. if x IN A then indicator s x else 0) =
                            indicator (s INTER A)’
 >- SET_TAC [indicator]
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> RW_TAC std_ss [HAS_INTEGRAL_RESTRICT_UNIV]
 >> METIS_TAC [ETA_AX]
QED

Theorem integral_indicator_UNIV :
    !s A. integral UNIV (indicator (s INTER A)) =
          integral A (indicator s)
Proof
  REWRITE_TAC [integral_def] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  ABS_TAC THEN METIS_TAC [has_integral_indicator_UNIV]
QED

Theorem integrable_indicator_UNIV :
    !s A. (indicator (s INTER A)) integrable_on UNIV <=>
          (indicator s) integrable_on A
Proof
  RW_TAC std_ss [integrable_on] THEN AP_TERM_TAC THEN
  ABS_TAC THEN METIS_TAC [has_integral_indicator_UNIV]
QED

Theorem integral_one : (* was: MEASURE_HOLLIGHT_EQ_ISABELLE *)
    !A. integral A (\x. 1) = integral univ(:real) (indicator A)
Proof
    ONCE_REWRITE_TAC [METIS [SET_RULE ``A = A INTER A``]
                          ``indicator A = indicator (A INTER A)``]
 >> SIMP_TAC std_ss [integral_indicator_UNIV]
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC INTEGRAL_EQ >> SIMP_TAC std_ss [indicator]
QED

val indicator_fn_pos_le = INDICATOR_FN_POS;

Theorem has_integral_interval_cube :
    !a b n. (indicator (interval [a,b]) has_integral
               content (interval [a,b] INTER (line n))) (line n)
Proof
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [GSYM has_integral_indicator_UNIV] THEN
  SIMP_TAC std_ss [indicator, HAS_INTEGRAL_RESTRICT_UNIV] THEN
  SIMP_TAC std_ss [line, GSYM interval, INTER_INTERVAL] THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``content (interval [(max a (-&n),min b (&n))]) =
                        content (interval [(max a (-&n),min b (&n))]) * 1``] THEN
  METIS_TAC [HAS_INTEGRAL_CONST]
QED

(* Lebesgue sigma-algebra with the household measure (lebesgue),
   constructed by Henstock-Kurzweil (gauge) Integration.

   Named after Henri Lebesgue (1875-1941), a French mathematician [5]

   NOTE: This definition of "Lebesgue measurable sets (and Lebesgue measure)"
   is aligned with Definition 18.1 [2, p.300] and 18.7 [2, p.304].
 *)
Definition lebesgue_def :
  lebesgue = (univ(:real),
              {A | !n. (indicator A) integrable_on (line n)},
              (\A. sup {Normal (integral (line n) (indicator A)) | n IN UNIV}))
End

(* NOTE: This name is inspired by HVG's old theorem name lmeasure_eq_0 *)
Overload lmeasure = “measure lebesgue”

Theorem space_lebesgue :
    m_space lebesgue = univ(:real)
Proof
    SIMP_TAC std_ss [lebesgue_def, m_space_def]
QED

Theorem in_sets_lebesgue : (* was: lebesgueI *)
    !A. (!n. indicator A integrable_on line n) ==> A IN measurable_sets lebesgue
Proof
    SIMP_TAC std_ss [lebesgue_def, measurable_sets_def] THEN SET_TAC []
QED

val lebesgueI = in_sets_lebesgue;

Theorem limseq_indicator_BIGUNION : (* was: LIMSEQ_indicator_UN *)
    !A x. ((\k. indicator (BIGUNION {(A:num->real->bool) i | i < k}) x) -->
           (indicator (BIGUNION {A i | i IN UNIV}) x)) sequentially
Proof
  REPEAT GEN_TAC THEN ASM_CASES_TAC ``?i. x IN (A:num->real->bool) i`` THENL
  [ALL_TAC, FULL_SIMP_TAC std_ss [indicator, IN_BIGUNION] THEN
   SIMP_TAC std_ss [GSPECIFICATION, IN_UNIV] THEN
   KNOW_TAC ``~(?s. x IN s /\ ?i. s = (A:num->real->bool) i)`` THENL
   [METIS_TAC [], DISCH_TAC] THEN
   KNOW_TAC ``!k. ~(?s. x IN s /\ ?i. (s = (A:num->real->bool) i) /\ i < k)`` THENL
   [METIS_TAC [], DISCH_TAC] THEN ASM_SIMP_TAC std_ss [LIM_CONST]] THEN
  FULL_SIMP_TAC std_ss [] THEN
  KNOW_TAC ``!k. indicator (BIGUNION {(A:num->real->bool) j | j < k + SUC i}) x = 1`` THENL
  [RW_TAC real_ss [indicator, GSPECIFICATION, IN_BIGUNION] THEN
   UNDISCH_TAC ``~?s. x IN s /\ ?j. (s = (A:num->real->bool) j) /\ j < k + SUC i`` THEN
   SIMP_TAC std_ss [] THEN EXISTS_TAC ``(A:num->real->bool) i`` THEN
   ASM_SIMP_TAC std_ss [] THEN EXISTS_TAC  ``i:num`` THEN ASM_SIMP_TAC std_ss [] THEN
   ARITH_TAC, DISCH_TAC] THEN
  KNOW_TAC ``indicator (BIGUNION {(A:num->real->bool) i | i IN univ(:num)}) x = 1`` THENL
  [RW_TAC real_ss [indicator, GSPECIFICATION, IN_BIGUNION] THEN
   POP_ASSUM MP_TAC THEN SIMP_TAC std_ss [IN_UNIV] THEN METIS_TAC [], DISCH_TAC] THEN
  MATCH_MP_TAC SEQ_OFFSET_REV THEN EXISTS_TAC ``SUC i`` THEN
  ASM_SIMP_TAC std_ss [LIM_CONST]
QED

val LIMSEQ_indicator_UN = limseq_indicator_BIGUNION;

Theorem sigma_algebra_lebesgue :
    sigma_algebra (UNIV, {A | !n. (indicator A) integrable_on (line n)})
Proof
    RW_TAC std_ss [sigma_algebra_alt_pow]
 >- (REWRITE_TAC [POW_DEF] >> SET_TAC [])
 >- (SIMP_TAC std_ss [GSPECIFICATION] \\
     Know `indicator {} = (\x:real. 0)` >- SET_TAC [indicator] \\
     Rewr' >> SIMP_TAC std_ss [INTEGRABLE_0])
 >- (FULL_SIMP_TAC std_ss [GSPECIFICATION] \\
     Know `indicator (univ(:real) DIFF s) = (\x. 1 - indicator s x)`
     >- (SIMP_TAC std_ss [indicator] >> ABS_TAC \\
         SIMP_TAC std_ss [IN_DIFF, IN_UNIV] >> COND_CASES_TAC \\
         FULL_SIMP_TAC real_ss []) >> Rewr' \\
     ONCE_REWRITE_TAC [METIS [] ``(\x. 1 - indicator s x) =
                        (\x. (\x. 1) x - (\x. indicator s x) x)``] \\
     GEN_TAC >> MATCH_MP_TAC INTEGRABLE_SUB >> CONJ_TAC >|
     [SIMP_TAC std_ss [line, GSYM interval, INTEGRABLE_CONST],
      METIS_TAC [ETA_AX]])
 >> FULL_SIMP_TAC std_ss [GSPECIFICATION]
 >> KNOW_TAC ``!k n. indicator (BIGUNION {(A:num->real->bool) i | i < k})
              integrable_on (line n)``
 >- (Induct_on `k`
     >- (SIMP_TAC std_ss [LT] THEN REWRITE_TAC [SET_RULE ``BIGUNION {A i | i | F} = {}``] THEN
         KNOW_TAC ``indicator {} = (\x:real. 0)``
         THENL [SET_TAC [indicator], DISCH_TAC THEN ASM_REWRITE_TAC []] THEN
         SIMP_TAC std_ss [INTEGRABLE_0]) \\
     KNOW_TAC ``BIGUNION {A i | i < SUC k} =
              BIGUNION {(A:num->real->bool) i | i < k} UNION A k`` THENL
     [ SIMP_TAC std_ss [ADD1, ARITH_PROVE ``i < SUC k <=> (i < k \/ (i = k))``] THEN
       SET_TAC [], DISCH_TAC THEN ASM_REWRITE_TAC [] ] THEN
     KNOW_TAC ``indicator (BIGUNION {(A:num->real->bool) i | i < k} UNION A k) =
                (\x. max (indicator (BIGUNION {A i | i < k}) x) (indicator (A k) x))`` THENL
     [ SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
       SIMP_TAC std_ss [max_def, indicator] THEN
       REPEAT COND_CASES_TAC THEN FULL_SIMP_TAC std_ss [IN_UNION] THEN
       POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN FULL_SIMP_TAC real_ss [],
       DISCH_TAC ] THEN
     REWRITE_TAC [GSYM absolutely_integrable_on_indicator] THEN GEN_TAC THEN
     ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MAX THEN
     ASM_SIMP_TAC std_ss [absolutely_integrable_on_indicator] THEN
     FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_IMAGE, IN_UNIV] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC [])
 >> DISCH_TAC
 >> GEN_TAC
 >> MP_TAC (ISPECL [``(\k. indicator (BIGUNION {(A:num->real->bool) i | i < k}))``,
                  ``indicator (BIGUNION {(A:num->real->bool) i | i IN univ(:num)})``,
                  ``(\x:real. 1:real)``, ``line n``] DOMINATED_CONVERGENCE)
 >> KNOW_TAC ``(!k.
      (\k. indicator (BIGUNION {(A:num->real->bool) i | i < k})) k integrable_on line n) /\
      (\x. 1) integrable_on line n /\
      (!k x.
        x IN line n ==>
        abs ((\k. indicator (BIGUNION {A i | i < k})) k x) <= (\x. 1) x) /\
      (!x.
        x IN line n ==>
          ((\k. (\k. indicator (BIGUNION {A i | i < k})) k x) -->
          indicator (BIGUNION {A i | i IN univ(:num)}) x) sequentially)``
 >| [ALL_TAC, METIS_TAC []]
 >> REPEAT CONJ_TAC
 >| [ FULL_SIMP_TAC std_ss [],
      SIMP_TAC std_ss [line, GSYM interval, INTEGRABLE_CONST],
      SIMP_TAC std_ss [DROP_INDICATOR_ABS_LE_1],
      METIS_TAC [LIMSEQ_indicator_UN] ]
QED

Theorem sets_lebesgue :
    measurable_sets lebesgue = {A | !n. (indicator A) integrable_on (line n)}
Proof
    SIMP_TAC std_ss [lebesgue_def, measurable_sets_def]
QED

Theorem in_sets_lebesgue_imp : (* was: lebesgueD *)
    !A n. A IN measurable_sets lebesgue ==> indicator A integrable_on line n
Proof
    SIMP_TAC std_ss [sets_lebesgue, GSPECIFICATION]
QED

val lebesgueD = in_sets_lebesgue_imp;

Theorem measure_lebesgue :
    measure lebesgue =
      (\A. sup {Normal (integral (line n) (indicator A)) | n IN UNIV})
Proof
    SIMP_TAC std_ss [measure_def, lebesgue_def]
QED

Theorem positive_lebesgue :
    positive lebesgue
Proof
  SIMP_TAC std_ss [lebesgue_def, positive_def, sets_lebesgue, measure_lebesgue] THEN
  SIMP_TAC std_ss [INDICATOR_EMPTY, IN_UNIV, INTEGRAL_0, extreal_of_num_def] THEN
   REWRITE_TAC [SET_RULE ``{Normal 0 | n | T} = {Normal 0}``, sup_sing] THEN
  RW_TAC std_ss [] THEN MATCH_MP_TAC le_sup_imp THEN
  ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
  EXISTS_TAC ``0:num`` THEN SIMP_TAC std_ss [extreal_11, line, GSYM interval] THEN
  SIMP_TAC std_ss [REAL_NEG_0, INTEGRAL_REFL]
QED

Theorem countably_additive_lebesgue :
    countably_additive lebesgue
Proof
    RW_TAC std_ss [countably_additive_def]
 >> Know `!A. IMAGE A univ(:num) SUBSET measurable_sets lebesgue ==>
              !i n. indicator (A i) integrable_on line n`
 >- (rpt STRIP_TAC >> MATCH_MP_TAC lebesgueD \\
     FULL_SIMP_TAC std_ss [SUBSET_DEF] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> METIS_TAC [IN_IMAGE, IN_UNIV])
 >> DISCH_TAC
 >> Know `!i n. 0 <= integral (line n) (indicator ((f:num->real->bool) i))`
 >- (rpt STRIP_TAC >> MATCH_MP_TAC INTEGRAL_COMPONENT_POS \\
     SIMP_TAC std_ss [DROP_INDICATOR_POS_LE] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     FULL_SIMP_TAC std_ss [IN_FUNSET, SUBSET_DEF, IN_IMAGE] \\
     METIS_TAC []) >> DISCH_TAC
 >> Know `BIGUNION {f i | i IN UNIV} IN measurable_sets lebesgue ==>
          !i n. (indicator ((f:num->real->bool) i)) integrable_on line n`
 >- (RW_TAC std_ss [] \\
     MATCH_MP_TAC lebesgueD \\
     FULL_SIMP_TAC std_ss [IN_FUNSET, IN_UNIV])
 >> FULL_SIMP_TAC std_ss [GSYM IMAGE_DEF] >> DISCH_TAC
 >> SIMP_TAC std_ss [o_DEF, measure_lebesgue]
 >> Know `suminf (\i. sup {(\n i. Normal (integral (line n) (indicator (f i)))) n i | n IN UNIV}) =
          sup {suminf (\i. (\n i. Normal (integral (line n) (indicator (f i)))) n i) | n IN UNIV}`
 >- (MATCH_MP_TAC ext_suminf_sup_eq \\
     SIMP_TAC std_ss [extreal_of_num_def] \\
     CONJ_TAC
     >- (SIMP_TAC std_ss [extreal_le_def] >> rpt STRIP_TAC \\
         MATCH_MP_TAC INTEGRAL_SUBSET_COMPONENT_LE \\
         FULL_SIMP_TAC std_ss [LINE_MONO, DROP_INDICATOR_POS_LE]) \\
     SIMP_TAC std_ss [extreal_le_def] \\
     rpt GEN_TAC >> MATCH_MP_TAC INTEGRAL_COMPONENT_POS \\
     FULL_SIMP_TAC std_ss [DROP_INDICATOR_POS_LE])
 >> RW_TAC std_ss [] >> POP_ASSUM K_TAC
 >> Suff `!n. Normal (integral (line n) (indicator (BIGUNION (IMAGE f univ(:num))))) =
              suminf (\x. Normal (integral (line n) (indicator ((f:num->real->bool) x))))`
 >- (DISCH_TAC >> ASM_SIMP_TAC std_ss [])
 >> GEN_TAC
 >> Know `suminf (\x. Normal (integral (line n) (indicator (f x)))) =
          sup (IMAGE (\n'. EXTREAL_SUM_IMAGE (\x. Normal (integral (line n) (indicator (f x))))
                                             (count n')) UNIV)`
 >- (MATCH_MP_TAC ext_suminf_def \\
     rw [extreal_of_num_def, extreal_le_eq]) >> Rewr'
 >> SIMP_TAC std_ss [FINITE_COUNT, EXTREAL_SUM_IMAGE_NORMAL]
 >> Know `mono_increasing
          (\n'. SIGMA (\x. integral (line n) (indicator ((f:num->real->bool) x))) (count n'))`
 >- (SIMP_TAC std_ss [mono_increasing_def] THEN
     REPEAT STRIP_TAC THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
     SIMP_TAC std_ss [FINITE_COUNT, GSYM EXTREAL_SUM_IMAGE_NORMAL] THEN
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET THEN
     ASM_SIMP_TAC real_ss [count_def, GSPECIFICATION, FINITE_COUNT, SUBSET_DEF] THEN
     REPEAT STRIP_TAC THEN REWRITE_TAC [extreal_of_num_def, extreal_le_def] THEN
     MATCH_MP_TAC INTEGRAL_COMPONENT_POS THEN
     ASM_SIMP_TAC std_ss [DROP_INDICATOR_POS_LE]) >> DISCH_TAC
 >> ASM_SIMP_TAC std_ss [GSYM sup_seq', REAL_SUM_IMAGE_COUNT]
 >> Know `!n m. sum (0,m) (\x. integral (line n) (indicator ((f:num->real->bool) x))) =
                integral (line n) (indicator (BIGUNION {f i | i < m}))`
 THENL (* The rest (original proof) works fine *)
[GEN_TAC THEN Induct_on `m` THENL
  [REWRITE_TAC [realTheory.sum, LT] THEN
  REWRITE_TAC [SET_RULE ``{f i | i | F} = {}``, BIGUNION_EMPTY] THEN
  SIMP_TAC real_ss [INDICATOR_EMPTY, INTEGRAL_0], ALL_TAC] THEN
 KNOW_TAC ``!m. BIGUNION {(f:num->real->bool) i | i < m} IN
                measurable_sets lebesgue`` THENL
 [GEN_TAC THEN MATCH_MP_TAC lebesgueI THEN GEN_TAC THEN
  ASSUME_TAC sigma_algebra_lebesgue THEN
  FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, GSPECIFICATION, subsets_def, space_def] THEN
  POP_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_UNIV] THEN CONJ_TAC THENL
  [REWRITE_TAC [pred_setTheory.COUNTABLE_ALT] THEN SET_TAC [], ALL_TAC] THEN METIS_TAC [],
  DISCH_TAC] THEN
 KNOW_TAC ``!m. BIGUNION {(f:num->real->bool) i | i < m} INTER f m = {}`` THENL
 [GEN_TAC THEN SIMP_TAC std_ss [INTER_DEF, IN_BIGUNION, GSPECIFICATION] THEN
  SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY] THEN
  GEN_TAC THEN ASM_CASES_TAC ``x NOTIN (f:num->real->bool) m'`` THEN
  ASM_REWRITE_TAC [] THEN GEN_TAC THEN
  ASM_CASES_TAC ``x IN (s:real->bool)`` THEN FULL_SIMP_TAC std_ss [] THEN
  GEN_TAC THEN ASM_CASES_TAC ``~(i < m':num)`` THEN FULL_SIMP_TAC std_ss [] THEN
  EXISTS_TAC ``x:real`` THEN FULL_SIMP_TAC std_ss [DISJOINT_DEF] THEN
  POP_ASSUM MP_TAC THEN DISCH_THEN (ASSUME_TAC o MATCH_MP LESS_NOT_EQ) THEN
  ASM_SET_TAC [], DISCH_TAC] THEN
 KNOW_TAC ``!x. indicator (BIGUNION {(f:num->real->bool) i | i < SUC m}) x =
                indicator (BIGUNION {f i | i < m}) x +
                indicator (f m) x`` THENL
 [GEN_TAC THEN SIMP_TAC std_ss [indicator] THEN
  ASM_CASES_TAC ``x IN ((f:num->real->bool) m)`` THEN ASM_SIMP_TAC std_ss [] THENL
  [KNOW_TAC ``x NOTIN BIGUNION {(f:num->real->bool) i | i < m}`` THENL
   [ASM_SET_TAC [], DISCH_TAC] THEN ASM_SIMP_TAC real_ss [IN_BIGUNION] THEN
   SIMP_TAC std_ss [GSPECIFICATION] THEN
   KNOW_TAC ``?s. x IN s /\ ?i. (s = (f:num->real->bool) i) /\ i < SUC m`` THENL
   [ALL_TAC, METIS_TAC []] THEN EXISTS_TAC ``(f:num->real->bool) m`` THEN
   ASM_REWRITE_TAC [] THEN EXISTS_TAC ``m:num`` THEN SIMP_TAC arith_ss [], ALL_TAC] THEN
   FULL_SIMP_TAC real_ss [IN_BIGUNION, GSPECIFICATION] THEN COND_CASES_TAC THENL
   [ALL_TAC, COND_CASES_TAC THENL [ALL_TAC, SIMP_TAC real_ss []] THEN
    FULL_SIMP_TAC std_ss [] THEN FIRST_X_ASSUM (MP_TAC o SPEC ``s:real->bool``) THEN
    ASM_SIMP_TAC std_ss [] THEN DISCH_THEN (MP_TAC o SPEC ``i:num``) THEN
    ASM_SIMP_TAC arith_ss []] THEN FULL_SIMP_TAC std_ss [] THEN
   COND_CASES_TAC THENL [SIMP_TAC std_ss [], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [] THEN FIRST_X_ASSUM (MP_TAC o SPEC ``(f:num->real->bool) i``) THEN
   ASM_SIMP_TAC std_ss [] THEN DISCH_THEN (MP_TAC o SPEC ``i:num``) THEN
   RW_TAC std_ss [] THEN KNOW_TAC ``i = m:num`` THENL
   [ASM_SIMP_TAC arith_ss [], DISCH_TAC] THEN FULL_SIMP_TAC std_ss [],
   DISCH_TAC] THEN
  ONCE_REWRITE_TAC [realTheory.sum] THEN ASM_REWRITE_TAC [] THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN REWRITE_TAC [ADD] THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)
               [METIS [] ``!f. indicator f = (\x. indicator f x)``] THEN
  SIMP_TAC std_ss [] THEN
  KNOW_TAC ``integral (line n') (indicator (BIGUNION {f i | i < SUC m})) =
             integral (line n') ((\x. (\x. indicator (BIGUNION {f i | i < m}) x) x +
                                 (\x. indicator ((f:num->real->bool) m) x) x))`` THENL
  [FIRST_X_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
   ASM_SIMP_TAC std_ss [] THEN METIS_TAC [], DISC_RW_KILL] THEN
  MATCH_MP_TAC INTEGRAL_ADD THEN METIS_TAC [lebesgueD], DISCH_TAC] THEN
  ASM_SIMP_TAC std_ss [] THEN
  MATCH_MP_TAC (METIS [] ``!P. (P /\ Q) ==> Q``) THEN
  ONCE_REWRITE_TAC [METIS []
        ``(indicator (BIGUNION {(f:num->real->bool) i | i < n'})) =
     (\n'. indicator (BIGUNION {f i | i < n'})) n'``] THEN
  EXISTS_TAC ``(indicator (BIGUNION (IMAGE (f:num->real->bool) univ(:num))))
                integrable_on (line n)`` THEN
  MATCH_MP_TAC DOMINATED_CONVERGENCE THEN EXISTS_TAC ``\x:real. 1:real`` THEN
  REPEAT CONJ_TAC THENL
  [KNOW_TAC ``!m. BIGUNION {(f:num->real->bool) i | i < m} IN
                measurable_sets lebesgue`` THENL
  [GEN_TAC THEN MATCH_MP_TAC lebesgueI THEN GEN_TAC THEN
   ASSUME_TAC sigma_algebra_lebesgue THEN
   FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, GSPECIFICATION, subsets_def, space_def] THEN
   POP_ASSUM MATCH_MP_TAC THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_UNIV] THEN CONJ_TAC THENL
   [REWRITE_TAC [pred_setTheory.COUNTABLE_ALT] THEN SET_TAC [], ALL_TAC] THEN
    METIS_TAC [],
    DISCH_TAC] THEN METIS_TAC [lebesgueD],
   SIMP_TAC std_ss [line, GSYM interval, INTEGRABLE_CONST],
   FULL_SIMP_TAC std_ss [DROP_INDICATOR_ABS_LE_1], ALL_TAC] THEN
  METIS_TAC [LIMSEQ_indicator_UN, IMAGE_DEF]
QED

Theorem measure_space_lebesgue :
    measure_space lebesgue
Proof
    SIMP_TAC std_ss [measure_space_def, positive_lebesgue]
 >> SIMP_TAC std_ss [sets_lebesgue, space_lebesgue, sigma_algebra_lebesgue]
 >> SIMP_TAC std_ss [countably_additive_lebesgue]
QED

Theorem borel_imp_lebesgue_sets : (* was: lebesgueI_borel *)
    !s. s IN subsets borel ==> s IN measurable_sets lebesgue
Proof
    RW_TAC std_ss [borel_eq_ge_le]
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (‘s’, ‘s’)
 >> REWRITE_TAC [GSYM SUBSET_DEF]
 >> ‘measurable_sets lebesgue = subsets (m_space lebesgue,measurable_sets lebesgue)’
       by rw [subsets_def]
 >> POP_ORW
 >> ‘univ(:real) = space (m_space lebesgue,measurable_sets lebesgue)’
       by rw [space_def, space_lebesgue]
 >> POP_ORW
 >> MATCH_MP_TAC SIGMA_SUBSET
 >> CONJ_TAC >- rw [space_lebesgue, sets_lebesgue, sigma_algebra_lebesgue]
 >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV, subsets_def]
 >> rename1 ‘(\(a,b). {x | a <= x /\ x <= b}) y IN measurable_sets lebesgue’
 >> Cases_on ‘y’
 >> RW_TAC std_ss []
 >> MATCH_MP_TAC lebesgueI
 >> REWRITE_TAC [integrable_on, GSYM interval]
 >> METIS_TAC [has_integral_interval_cube]
QED

val lebesgueI_borel = borel_imp_lebesgue_sets;

(* TODO: prove this theorem with PSUBSET, i.e. the existence of non-Borel
   Lebesgue-measurable sets.
 *)
Theorem lborel_subset_lebesgue :
    measurable_sets lborel SUBSET measurable_sets lebesgue
Proof
    RW_TAC std_ss [SUBSET_DEF, sets_lborel]
 >> MATCH_MP_TAC lebesgueI_borel >> art []
QED

Theorem borel_imp_lebesgue_measurable :
    !f. f IN borel_measurable (space borel, subsets borel) ==>
        f IN borel_measurable (m_space lebesgue, measurable_sets lebesgue)
Proof
    RW_TAC std_ss [measurable_def, GSPECIFICATION]
 >| [ FULL_SIMP_TAC std_ss [space_lebesgue, space_borel, space_def],
      FULL_SIMP_TAC std_ss [space_def, subsets_def] ]
 >> FULL_SIMP_TAC std_ss [space_borel, space_lebesgue, INTER_UNIV]
 >> MATCH_MP_TAC lebesgueI_borel >> ASM_SET_TAC []
QED

val borel_measurable_lebesgueI = borel_imp_lebesgue_measurable;

(* |- !f. f IN borel_measurable borel ==>
          f IN borel_measurable (m_space lebesgue,measurable_sets lebesgue)
 *)
Theorem borel_imp_lebesgue_measurable' =
    REWRITE_RULE [SPACE] borel_imp_lebesgue_measurable

Theorem negligible_in_lebesgue :
    !s. negligible s ==> s IN measurable_sets lebesgue
Proof
    RW_TAC std_ss [negligible]
 >> MATCH_MP_TAC lebesgueI
 >> METIS_TAC [integrable_on, line, GSYM interval]
QED

val lebesgueI_negligible = negligible_in_lebesgue;

Theorem lebesgue_of_negligible :
    !s. negligible s ==> (measure lebesgue s = 0)
Proof
    RW_TAC std_ss [measure_lebesgue]
 >> Know `!n. integral (line n) (indicator s) = 0`
 >- (FULL_SIMP_TAC std_ss [integral_def, negligible, line, GSYM interval] \\
     GEN_TAC >> MATCH_MP_TAC SELECT_UNIQUE \\
     GEN_TAC \\
     reverse EQ_TAC >- METIS_TAC [] \\
     METIS_TAC [HAS_INTEGRAL_UNIQUE]) >> Rewr
 >> SIMP_TAC std_ss [GSYM extreal_of_num_def]
 >> REWRITE_TAC [SET_RULE ``{(0 :extreal) | n IN UNIV} = {0}``]
 >> SIMP_TAC std_ss [sup_sing]
QED

Theorem lmeasure_eq_0 = lebesgue_of_negligible

Theorem INTEGRAL_POS :
    !f s. f integrable_on s /\ (!x. x IN s ==> 0 <= f x) ==>
          0 <= integral s f
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘g :real -> real = \x. 0’
 >> ‘0 = abs (integral s g)’ by simp [Abbr ‘g’, INTEGRAL_0]
 >> POP_ORW
 >> MATCH_MP_TAC INTEGRAL_ABS_BOUND_INTEGRAL
 >> rw [Abbr ‘g’, INTEGRABLE_0]
QED

Theorem negligible_iff_lmeasure_zero :
    !s. s IN measurable_sets lebesgue ==> (negligible s <=> lmeasure s = 0)
Proof
    rpt STRIP_TAC
 >> EQ_TAC >- REWRITE_TAC [lebesgue_of_negligible]
 >> DISCH_TAC
 >> rw [negligible]
 >> MP_TAC (Q.SPECL [‘a’, ‘b’] LINE_EXISTS) >> rw []
 >> Know ‘indicator s integrable_on line n’
 >- (Q.PAT_X_ASSUM ‘s IN measurable_sets lebesgue’ MP_TAC \\
     rw [lebesgue_def])
 >> DISCH_TAC
 >> qabbrev_tac ‘f = indicator s’
 >> Know ‘f integrable_on interval [a,b]’
 >- (MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL \\
     Q.EXISTS_TAC ‘line n’ >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘t = interval [a,b]’
 >> simp [HAS_INTEGRAL_INTEGRABLE_INTEGRAL]
 >> reverse (rw [GSYM REAL_LE_ANTISYM])
 >- (MATCH_MP_TAC INTEGRAL_POS >> rw [Abbr ‘f’, INDICATOR_POS])
 >> Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘integral (line n) f’
 >> CONJ_TAC
 >- (MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE \\
     rw [Abbr ‘f’, INDICATOR_POS])
 >> Know ‘sup (IMAGE (\n. Normal (integral (line n) f)) UNIV) = 0’
 >- (Q.PAT_X_ASSUM ‘lmeasure s = 0’ MP_TAC \\
     rw [lebesgue_def] \\
     POP_ASSUM (REWRITE_TAC o wrap o SYM) \\
     AP_TERM_TAC >> rw [Once EXTENSION])
 >> DISCH_TAC
 >> REWRITE_TAC [GSYM extreal_le_eq, normal_0]
 >> POP_ASSUM (REWRITE_TAC o wrap o SYM)
 >> rw [le_sup']
 >> POP_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘n’ >> REFL_TAC
QED

Theorem negligible_alt_lebesgue_null_set :
    !s. negligible s <=> s IN null_set lebesgue
Proof
    rw [IN_NULL_SET, null_set_def]
 >> METIS_TAC [negligible_in_lebesgue, negligible_iff_lmeasure_zero]
QED

Theorem lebesgue_measure_iff_LIMSEQ[local] :
    !A m. A IN measurable_sets lebesgue /\ 0 <= m ==>
         (measure lebesgue A = Normal m <=>
          ((\n. integral (line n) (indicator A)) --> m) sequentially)
Proof
    RW_TAC std_ss [Once EQ_SYM_EQ]
 >> `!n. Normal (integral (line n) (indicator A)) =
         Normal ((\n. integral (line n) (indicator A)) n)` by METIS_TAC []
 >> SIMP_TAC std_ss [measure_lebesgue, GSYM IMAGE_DEF]
 >> ONCE_ASM_REWRITE_TAC []
 >> MATCH_MP_TAC sup_seq'
 >> RW_TAC std_ss [mono_increasing_def]
 >> MATCH_MP_TAC INTEGRAL_SUBSET_COMPONENT_LE
 >> ASM_SIMP_TAC std_ss [LINE_MONO, lebesgueD, DROP_INDICATOR_POS_LE]
QED

Theorem lmeasure_iff_LIMSEQ = lebesgue_measure_iff_LIMSEQ

(* It's hard to calculate `measure lebesgue` on intervals by "lebesgue_def",
   but once the following lemma is proven, by UNIQUENESS_OF_MEASURE we
   will have `lebesgue` and `lborel` coincide on `subsets borel`, and thus
  `measure lebesgue` of other intervals can be derived from lambda lemmas.

   Most steps are from "lborel_eqI" (HVG's lebesgue_measure_hvgScript.sml).
 *)
Theorem lebesgue_closed_interval :
    !a b. a <= b ==> measure lebesgue (interval [a,b]) = Normal (b - a)
Proof
    RW_TAC std_ss [lebesgue_def, measure_def, GSYM CONTENT_CLOSED_INTERVAL]
 >> SIMP_TAC std_ss [sup_eq']
 >> CONJ_TAC >> GEN_TAC
 >- (SIMP_TAC std_ss [GSPECIFICATION, IN_UNIV] \\
     STRIP_TAC >> POP_ORW \\
     ASM_SIMP_TAC std_ss [extreal_le_def] \\
     ONCE_REWRITE_TAC [GSYM integral_indicator_UNIV] \\
     ONCE_REWRITE_TAC [INTER_COMM] \\
     REWRITE_TAC [integral_indicator_UNIV] \\
     GEN_REWR_TAC RAND_CONV [GSYM REAL_MUL_LID] \\
     MATCH_MP_TAC INTEGRAL_COMPONENT_UBOUND \\
     SIMP_TAC std_ss [DROP_INDICATOR_LE_1] \\
     ONCE_REWRITE_TAC [GSYM integrable_indicator_UNIV] \\
     SIMP_TAC std_ss [INTER_INTERVAL, line, GSYM interval, indicator] \\
     ONCE_REWRITE_TAC [METIS [] ``1 = (\x:real. 1:real) x``] \\
     REWRITE_TAC [INTEGRABLE_RESTRICT_UNIV, INTEGRABLE_CONST])
 >> DISCH_THEN MATCH_MP_TAC
 >> SIMP_TAC std_ss [GSPECIFICATION, IN_UNIV, extreal_11]
 >> MP_TAC (Q.SPECL [`abs a`, `abs b`] REAL_LE_TOTAL)
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >> STRIP_TAC
 >| [ (* goal 1 (of 2) *)
     `?n. abs b <= &n` by SIMP_TAC std_ss [SIMP_REAL_ARCH] \\
      Q.EXISTS_TAC `n` >> MATCH_MP_TAC INTEGRAL_UNIQUE \\
      Suff `{x | a <= x /\ x <= b} = {x | a <= x /\ x <= b} INTER line n`
      >- METIS_TAC [has_integral_interval_cube, GSYM interval] \\
      SIMP_TAC std_ss [EXTENSION, IN_INTER, GSPECIFICATION, line] \\
      GEN_TAC >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC >> REAL_ARITH_TAC,
      (* goal 2 (of 2) *)
     `?n. abs a <= &n` by SIMP_TAC std_ss [SIMP_REAL_ARCH] \\
      Q.EXISTS_TAC `n` THEN MATCH_MP_TAC INTEGRAL_UNIQUE \\
      Suff `{x | a <= x /\ x <= b} = {x | a <= x /\ x <= b} INTER line n`
      >- METIS_TAC [has_integral_interval_cube, GSYM interval] \\
      SIMP_TAC std_ss [EXTENSION, IN_INTER, GSPECIFICATION, line] \\
      GEN_TAC >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC >> REAL_ARITH_TAC ]
QED

(* |- !c. measure lebesgue {c} = 0 *)
Theorem lebesgue_sing =
   ((Q.GEN `c`) o
    (SIMP_RULE real_ss [REAL_LE_REFL, GSYM extreal_of_num_def, INTERVAL_SING]) o
    (Q.SPECL [`c`,`c`])) lebesgue_closed_interval;

Theorem lebesgue_empty :
    measure lebesgue {} = 0
Proof
    MATCH_MP_TAC lebesgue_of_negligible
 >> REWRITE_TAC [NEGLIGIBLE_EMPTY]
QED

Theorem lebesgue_closed_interval_content :
    !a b. measure lebesgue (interval [a,b]) = Normal (content (interval [a,b]))
Proof
    rpt STRIP_TAC
 >> `a <= b \/ b < a` by PROVE_TAC [REAL_LTE_TOTAL]
 >- ASM_SIMP_TAC std_ss [CONTENT_CLOSED_INTERVAL, lebesgue_closed_interval]
 >> IMP_RES_TAC REAL_LT_IMP_LE
 >> fs [GSYM CONTENT_EQ_0, GSYM extreal_of_num_def]
 >> fs [INTERVAL_EQ_EMPTY, lebesgue_empty]
QED

(* A direct application of the above theorem:
   |- measure_space (space borel,subsets borel,measure lebesgue) ==>
      !s. s IN subsets borel ==> lambda s = measure lebesgue s
 *)
val lemma =
    REWRITE_RULE [m_space_def, measurable_sets_def, measure_def,
                  lebesgue_closed_interval_content]
      (Q.SPEC `(space borel, subsets borel, measure lebesgue)` lambda_eq);

(* lborel and lebesgue coincide on borel *)
Theorem lambda_eq_lebesgue :
    !s. s IN subsets borel ==> lambda s = measure lebesgue s
Proof
    MATCH_MP_TAC lemma
 >> ASSUME_TAC borel_imp_lebesgue_sets
 >> RW_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def,
                   SPACE, sigma_algebra_borel] (* 2 subgoals *)
 >| [ (* goal 1 (of 2): positive *)
      MP_TAC positive_lebesgue \\
      RW_TAC std_ss [positive_def, measure_def, measurable_sets_def],
      (* goal 2 (of 2): countably_additive *)
      MP_TAC countably_additive_lebesgue \\
      RW_TAC std_ss [countably_additive_def, measure_def, measurable_sets_def,
                     IN_FUNSET, IN_UNIV] ]
QED

(* |- !s. s IN subsets borel ==> measure lebesgue s = lambda s *)
Theorem lebesgue_eq_lambda = GSYM lambda_eq_lebesgue;

(* a sample application of "lebesgue_eq_lambda" *)
Theorem lebesgue_open_interval :
    !a b. a <= b ==> measure lebesgue (interval (a,b)) = Normal (b - a)
Proof
    rpt STRIP_TAC
 >> `interval (a,b) IN subsets borel`
       by METIS_TAC [borel_measurable_sets, interval]
 >> ASM_SIMP_TAC std_ss [lebesgue_eq_lambda, lambda_open_interval]
QED

Theorem borel_null_set_subset_lebesgue :
    null_set lborel SUBSET null_set lebesgue
Proof
    simp [SUBSET_DEF, IN_APP]
 >> rw [null_set_def]
 >- METIS_TAC [SUBSET_DEF, lborel_subset_lebesgue]
 >> gs [lebesgue_eq_lambda, sets_lborel]
QED

Theorem borel_null_set_imp_negligible :
    !s. s IN null_set lborel ==> negligible s
Proof
    rw [negligible_alt_lebesgue_null_set]
 >> METIS_TAC [SUBSET_DEF, borel_null_set_subset_lebesgue]
QED

(* ------------------------------------------------------------------------- *)
(*  Equivalence of Lebesgue and Gauge (Henstock-Kurzweil) Integration        *)
(* ------------------------------------------------------------------------- *)

(* |- !k x.
        0 <= x /\ x < 1 /\ 0 < k ==>
        ?n. n < 2 ** k /\ &n / 2 pow k <= x /\ x < &SUC n / 2 pow k
 *)
Theorem lemma1[local] = lift_ieeeTheory.error_bound_lemma1
                     |> Q.SPEC ‘k’ |> GEN_ALL

(* lemma1 also holds if “0 < k” is removed *)
Theorem lemma1a[local] :
    !k x. 0 <= x /\ x < (1 :real) ==>
          ?n. n < 2 ** k /\ &n / 2 pow k <= x /\ x < &SUC n / 2 pow k
Proof
    rpt STRIP_TAC
 >> ‘k = 0 \/ 0 < k’ by simp [] >- rw []
 >> MATCH_MP_TAC lemma1 >> art []
QED

Theorem lemma1b[local] :
    !k x. 0 <= x /\ x <= (1 :real) ==>
          ?n. n < 2 ** k /\ &n / 2 pow k <= x /\ x <= &SUC n / 2 pow k
Proof
    rpt STRIP_TAC
 >> ‘x < 1 \/ x = (1 :real)’ by PROVE_TAC [REAL_LE_LT]
 >- (MP_TAC (Q.SPECL [‘k’, ‘x’] lemma1a) \\
     RW_TAC std_ss [] \\
     Q.EXISTS_TAC ‘n’ >> RW_TAC real_ss [REAL_LT_IMP_LE])
 >> POP_ORW
 >> Q.EXISTS_TAC ‘2 ** k - 1’ >> simp [REAL_POW]
QED

Theorem lemma1c[local] :
    !k x c. c <= x /\ x <= c + (1 :real) ==>
            ?n. n < 2 ** k /\ c + &n / 2 pow k <= x /\ x <= c + &SUC n / 2 pow k
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘k’, ‘x - c’] lemma1b)
 >> impl_tac >- REAL_ASM_ARITH_TAC
 >> STRIP_TAC
 >> Q.EXISTS_TAC ‘n’
 >> REAL_ASM_ARITH_TAC
QED

(* |- !k x.
        0 <= x /\ x < 1 /\ 0 < k ==>
        ?n. n <= 2 ** k /\ abs (x - &n / 2 pow k) <= 1 / 2 pow SUC k
 *)
Theorem lemma2[local] = lift_ieeeTheory.error_bound_lemma2
                     |> Q.SPEC ‘k’ |> GEN_ALL
                     |> SIMP_RULE real_ss [REAL_INV_1OVER, GSYM ADD1]

(* remove “0 < k”, use “_ <= 1 / 2 pow k” instead of “_ <= 1 / 2 pow SUC k” *)
Theorem lemma2a[local] :
    !k x. 0 <= x /\ x < (1 :real) ==>
          ?n. n <= 2 ** k /\ abs (x - &n / 2 pow k) <= 1 / 2 pow k
Proof
    rpt STRIP_TAC
 >> ‘k = 0 \/ 0 < k’ by simp []
 >- (Q.EXISTS_TAC ‘0’ >> simp [ABS_BOUNDS, REAL_LT_IMP_LE] \\
     Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘0’ >> simp [])
 >> MP_TAC (Q.SPECL [‘k’, ‘x’] lemma2)
 >> RW_TAC std_ss []
 >> Q.EXISTS_TAC ‘n’ >> art []
 >> Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘1 / 2 pow SUC k’ >> art []
 >> MATCH_MP_TAC REAL_LT_IMP_LE
 >> simp [REAL_POW_MONO_LT]
QED

(* furthermore, use “n < 2 ** k” instead of “n <= 2 ** k”

   NOTE: It turns out that lemma2 (and all variants) are not needed. Only
   lemma1a is used in [dyadic_covering_lemma_01] below.
 *)
Theorem lemma2b[local] :
    !k x. 0 <= x /\ x < (1 :real) ==>
          ?n. n < 2 ** k /\ abs (x - &n / 2 pow k) <= 1 / 2 pow k
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘k’, ‘x’] lemma2a)
 >> RW_TAC std_ss []
 >> ‘n < 2 ** k \/ n = 2 ** k’ by simp []
 >- (Q.EXISTS_TAC ‘n’ >> art [])
 >> Q.PAT_X_ASSUM ‘abs _ <= 1 / 2 pow k’ MP_TAC
 >> ASM_SIMP_TAC real_ss [GSYM REAL_POW]
 >> ‘2 pow k / 2 pow k = (1 :real)’ by simp [REAL_DIV_REFL] >> POP_ORW
 >> ‘x - 1 < 0 :real’ by simp [REAL_SUB_LT_NEG]
 >> ASM_SIMP_TAC real_ss [ABS_EQ_NEG]
 >> ‘1 - x <= 1 / 2 pow k <=> 1 - 1 / 2 pow k <= x’ by REAL_ARITH_TAC
 >> POP_ORW
 >> Know ‘(1 - 1 / 2 pow k) :real = &(2 ** k) / 2 pow k - 1 / 2 pow k’
 >- (ASM_SIMP_TAC real_ss [GSYM REAL_POW] \\
     Suff ‘2 pow k / 2 pow k = (1 :real)’ >- rw [] \\
     MATCH_MP_TAC REAL_DIV_REFL >> simp [])
 >> Rewr'
 >> REWRITE_TAC [REAL_DIV_SUB]
 >> ‘&(2 ** k) - (1 :real) = &(2 ** k - 1)’
      by simp [REAL_OF_NUM_SUB] >> POP_ORW
 >> STRIP_TAC
 >> Q.EXISTS_TAC ‘2 ** k - 1’
 >> SIMP_TAC real_ss [EXP_POS]
 >> ‘(0 :real) <= x - &(2 ** k - 1) / 2 pow k’ by simp [REAL_SUB_LE]
 >> ASM_SIMP_TAC real_ss [ABS_REDUCE]
 >> REWRITE_TAC [REAL_LE_SUB_RADD, REAL_DIV_ADD]
 >> SIMP_TAC real_ss [REAL_OF_NUM_ADD]
 >> SIMP_TAC arith_ss [GSYM LESS_EQ_ADD_SUB]
 >> SIMP_TAC real_ss [GSYM REAL_POW]
 >> Suff ‘2 pow k / 2 pow k = (1 :real)’ >- rw [REAL_LT_IMP_LE]
 >> MATCH_MP_TAC REAL_DIV_REFL >> simp []
QED

(* |- !k x.
        1 <= x /\ x < 2 /\ 0 < k ==>
        ?n. n <= 2 ** k /\ abs (1 + &n / 2 pow k - x) <= 1 / 2 pow SUC k
 *)
Theorem lemma3[local] = lift_ieeeTheory.error_bound_lemma3
                     |> Q.SPEC ‘k’ |> GEN_ALL
                     |> SIMP_RULE real_ss [REAL_INV_1OVER, GSYM ADD1]

(* |- !y. 0 < y ==> ?n. 1 / 2 pow n < y *)
Theorem lemma4[local] = REAL_ARCH_POW_INV |> Q.SPEC ‘1 / 2’
                     |> SIMP_RULE real_ss [pow_div, POW_ONE]

Theorem lemma5[local] :
    !n k. &n / 2 pow k < (&SUC n / 2 pow k) :real
Proof
    rpt GEN_TAC
 >> qmatch_abbrev_tac ‘x / z < y / (z :real)’
 >> Know ‘x / z < y / z <=> x < y’
 >- (MATCH_MP_TAC REAL_LT_RDIV >> simp [Abbr ‘z’])
 >> Rewr'
 >> simp [Abbr ‘x’, Abbr ‘y’]
QED

Theorem lemma5a[local] :
    !n k c. c + &n / 2 pow k < (c + &SUC n / 2 pow k) :real
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC REAL_LT_IADD
 >> REWRITE_TAC [lemma5]
QED

Theorem lemma6[local] :
    !n k. &SUC n / 2 pow k - &n / 2 pow k = (1 / 2 pow k) :real
Proof
    RW_TAC real_ss [REAL_DIV_SUB]
 >> simp [GSYM REAL_OF_NUM_SUB]
QED

Theorem lemma6a[local] :
    !n k c. (c + &SUC n / 2 pow k) - (c + &n / 2 pow k) = (1 / 2 pow k) :real
Proof
    rw [REAL_ARITH “c + a - (c + b) = a - (b :real)”, lemma6]
QED

(* "non-overlapping" = disjoint interiors *)
Definition nonoverlapping_def :
    nonoverlapping s t <=> DISJOINT (interior s) (interior t)
End

(* cf. right_open_interval_DISJOINT_EQ *)
Theorem closed_interval_nonoverlapping :
    !a b c d. a < b /\ c < d ==>
             (nonoverlapping (interval [a,b]) (interval [c,d]) <=>
              b <= c \/ d <= a)
Proof
    RW_TAC std_ss [nonoverlapping_def, INTERIOR_INTERVAL]
 >> EQ_TAC >> rw [DISJOINT_ALT, IN_INTERVAL, REAL_NOT_LT] (* 3 subgoals *)
 >| [ (* goal 1 (of 3): a < b <= c < d  or  c < d <= a < b *)
      CCONTR_TAC >> fs [REAL_NOT_LE] \\
      MP_TAC (Q.SPECL [‘max a c’, ‘min b d’] REAL_MEAN) \\
      ASM_REWRITE_TAC [REAL_MAX_LT, REAL_LT_MIN] \\
      CCONTR_TAC >> fs [] \\
     ‘z <= c \/ d <= z’ by PROVE_TAC [] >- METIS_TAC [REAL_LTE_ANTISYM] \\
      METIS_TAC [REAL_LTE_ANTISYM],
      (* goal 2 (of 3) *)
      CCONTR_TAC >> fs [REAL_NOT_LE] \\
      (* a < x < b <= c < x < d *)
     ‘x < c’ by PROVE_TAC [REAL_LTE_TRANS] \\
      METIS_TAC [REAL_LT_ANTISYM],
      (* goal 3 (of 3) *)
      CCONTR_TAC >> fs [REAL_NOT_LE] \\
      (* c < x < d <= a < x < b *)
     ‘x < a’ by PROVE_TAC [REAL_LTE_TRANS] \\
      METIS_TAC [REAL_LT_ANTISYM] ]
QED

Theorem nonoverlapping_comm :
    !s t. nonoverlapping s t <=> nonoverlapping t s
Proof
    RW_TAC std_ss [nonoverlapping_def, Once DISJOINT_SYM]
QED

(* cf. SUBSET_DISJOINT *)
Theorem nonoverlapping_subset_inclusive :
    !s t u v. nonoverlapping s t /\ u SUBSET s /\ v SUBSET t ==>
              nonoverlapping u v
Proof
    rw [nonoverlapping_def]
 >> MATCH_MP_TAC SUBSET_DISJOINT
 >> qexistsl_tac [‘interior s’, ‘interior t’] >> art []
 >> rw [SUBSET_INTERIOR]
QED

Theorem nonoverlapping_empty[simp] :
    nonoverlapping s {} /\ nonoverlapping {} s
Proof
    simp [nonoverlapping_def, INTERIOR_EMPTY, DISJOINT_EMPTY]
QED

(* cf. CLOSED_interval (constructor) *)
Definition closed_interval_def :
    closed_interval k <=> ?a b. k = interval [a,b]
End

Theorem closed_interval_closed :
    closed_interval k ==> closed k
Proof
    RW_TAC std_ss [closed_interval_def]
 >> REWRITE_TAC [CLOSED_INTERVAL]
QED

Theorem closed_interval_interval :
    closed_interval (interval [a,b])
Proof
    rw [closed_interval_def]
 >> qexistsl_tac [‘a’, ‘b’] >> art []
QED

Theorem closed_interval_imp_lebesgue :
    !s. closed_interval s ==> s IN measurable_sets lebesgue
Proof
    rpt STRIP_TAC
 >> Suff ‘s IN measurable_sets lborel’
 >- METIS_TAC [SUBSET_DEF, lborel_subset_lebesgue]
 >> REWRITE_TAC [sets_lborel]
 >> MATCH_MP_TAC borel_closed
 >> MATCH_MP_TAC closed_interval_closed >> art []
QED

Theorem closed_interval_nonoverlapping_imp_negligible[local] :
    !s t. closed_interval s /\ closed_interval t /\ nonoverlapping s t ==>
          negligible (s INTER t)
Proof
    rw [closed_interval_def, nonoverlapping_def]
 >> fs [INTERIOR_INTERVAL]
 >> rename1 ‘DISJOINT (interval (a,b)) (interval (c,d))’
 >> fs [DISJOINT_DEF, DISJOINT_INTERVAL] (* 4 subgoals *)
 >| [ (* goal 1 (of 4) *)
     ‘b < a \/ b = a’ by fs [REAL_LE_LT]
      >- (‘interval [a,b] = {}’ by simp [GSYM INTERVAL_EQ_EMPTY] \\
          simp [NEGLIGIBLE_EMPTY]) \\
      simp [INTERVAL_SING] \\
      Cases_on ‘a IN interval [c,d]’
      >- (Suff ‘{a} INTER interval [c,d] = {a}’ >- simp [NEGLIGIBLE_SING] \\
          fs [IN_INTERVAL] \\
          rw [Once EXTENSION, IN_INTERVAL] \\
          EQ_TAC >> rw []) \\
      Suff ‘{a} INTER interval [c,d] = {}’ >- simp [NEGLIGIBLE_EMPTY] \\
      rw [Once EXTENSION, IN_INTERVAL, REAL_NOT_LE] \\
      fs [IN_INTERVAL, REAL_NOT_LE],
      (* goal 2 (of 4) *)
     ‘d < c \/ d = c’ by fs [REAL_LE_LT]
      >- (‘interval [c,d] = {}’ by simp [GSYM INTERVAL_EQ_EMPTY] \\
          simp [NEGLIGIBLE_EMPTY]) \\
      simp [INTERVAL_SING] \\
      Cases_on ‘c IN interval [a,b]’
      >- (Suff ‘interval [a,b] INTER {c} = {c}’ >- simp [NEGLIGIBLE_SING] \\
          fs [IN_INTERVAL] \\
          rw [Once EXTENSION, IN_INTERVAL] \\
          EQ_TAC >> rw []) \\
      Suff ‘interval [a,b] INTER {c} = {}’ >- simp [NEGLIGIBLE_EMPTY] \\
      rw [Once EXTENSION, IN_INTERVAL, REAL_NOT_LE] \\
      fs [IN_INTERVAL, REAL_NOT_LE],
      (* goal 3 (of 4) *)
      reverse (Cases_on ‘a <= b’)
      >- (fs [REAL_NOT_LE] \\
         ‘interval [a,b] = {}’ by simp [GSYM INTERVAL_EQ_EMPTY] \\
          simp [NEGLIGIBLE_EMPTY]) \\
      reverse (Cases_on ‘c <= d’)
      >- (fs [REAL_NOT_LE] \\
         ‘interval [c,d] = {}’ by simp [GSYM INTERVAL_EQ_EMPTY] \\
          simp [NEGLIGIBLE_EMPTY]) \\
   (* now we have: a <= b <= c <= d *)
      simp [INTER_INTERVAL] \\
     ‘a <= c /\ b <= d’ by PROVE_TAC [REAL_LE_TRANS] \\
      simp [REAL_MAX_REDUCE, REAL_MIN_REDUCE] \\
     ‘b < c \/ b = c’ by PROVE_TAC [REAL_LE_LT]
      >- (‘interval [c,b] = {}’ by simp [GSYM INTERVAL_EQ_EMPTY] \\
          simp [NEGLIGIBLE_EMPTY]) \\
      simp [INTERVAL_SING, NEGLIGIBLE_SING],
      (* goal 4 (of 4) *)
      reverse (Cases_on ‘a <= b’)
      >- (fs [REAL_NOT_LE] \\
         ‘interval [a,b] = {}’ by simp [GSYM INTERVAL_EQ_EMPTY] \\
          simp [NEGLIGIBLE_EMPTY]) \\
      reverse (Cases_on ‘c <= d’)
      >- (fs [REAL_NOT_LE] \\
         ‘interval [c,d] = {}’ by simp [GSYM INTERVAL_EQ_EMPTY] \\
          simp [NEGLIGIBLE_EMPTY]) \\
   (* now we have: c <= d <= a <= b *)
      simp [INTER_INTERVAL] \\
     ‘c <= a /\ d <= b’ by PROVE_TAC [REAL_LE_TRANS] \\
      simp [REAL_MAX_REDUCE, REAL_MIN_REDUCE] \\
     ‘d < a \/ d = a’ by PROVE_TAC [REAL_LE_LT]
      >- (‘interval [a,d] = {}’ by simp [GSYM INTERVAL_EQ_EMPTY] \\
          simp [NEGLIGIBLE_EMPTY]) \\
      simp [INTERVAL_SING, NEGLIGIBLE_SING] ]
QED

Theorem closed_interval_negligible_imp_nonoverlapping[local] :
    !s t. closed_interval s /\ closed_interval t /\ negligible (s INTER t) ==>
          nonoverlapping s t
Proof
    rw [closed_interval_def, nonoverlapping_def]
 >> simp [INTERIOR_INTERVAL]
 >> simp [DISJOINT_DEF, DISJOINT_INTERVAL]
 >> rename1 ‘negligible (interval [a,b] INTER interval [c,d])’
 >> fs [INTER_INTERVAL]
 >> ‘lmeasure (interval [max a c,min b d]) = 0’
      by PROVE_TAC [lebesgue_of_negligible]
 >> CCONTR_TAC >> fs [REAL_NOT_LE]
 (* a < b,
    c < d *)
 >> Know ‘max a c < min b d’ >- simp [REAL_MAX_LT, REAL_LT_MIN]
 >> qmatch_abbrev_tac ‘x < (y :real) ==> F’ >> DISCH_TAC
 >> ‘x <= y’ by simp [REAL_LT_IMP_LE]
 (* applying lebesgue_closed_interval *)
 >> ‘lmeasure (interval [x,y]) = Normal (y - x)’
      by PROVE_TAC [lebesgue_closed_interval]
 >> Suff ‘y - x <> 0’ >- METIS_TAC [extreal_11, normal_0]
 >> Q.PAT_X_ASSUM ‘x < y’ MP_TAC
 >> REAL_ARITH_TAC
QED

Theorem closed_interval_negligible_eq_nonoverlapping :
    !s t. closed_interval s /\ closed_interval t ==>
         (negligible (s INTER t) <=> nonoverlapping s t)
Proof
    PROVE_TAC [closed_interval_nonoverlapping_imp_negligible,
               closed_interval_negligible_imp_nonoverlapping]
QED

(* NOTE: Here we use the “gauge” definition from the old integralTheory, as it
   avoids “open” sets and directly gives the radius g(x) as a positive real.

   The asserted ‘J’ may contain duplicated elements, i.e. J(i) is finite. This is
   why we used “J i <> J j” instead of “i <> j” in the disjointness conclusion.

   NOTE: Instead of proving “E INTER J i SUBSET cball (t i,g (t i))” as required
   in textbook, we use the same proof to show “J i SUBSET cball (t i,g (t i))”,
   which is required by definition of [FINE] later.
 *)
Theorem dyadic_covering_lemma_unit[local] :
    !g E c. gauge UNIV g /\ E <> {} /\ E SUBSET interval [c,c + 1] ==>
            ?J t. (!i. J i SUBSET interval [c,c + 1] /\
                       closed_interval (J i) /\
                       t i IN E INTER J (i :num) /\
                       J i SUBSET cball (t i,g (t i))) /\
                  (!i j. J i <> J j ==> nonoverlapping (J i) (J j)) /\
                   E SUBSET BIGUNION (IMAGE J UNIV)
Proof
    rw [integralTheory.gauge', SUBSET_DEF, IN_INTERVAL, IN_CBALL, IN_INTERVAL]
 >> qabbrev_tac ‘f = \k n. interval [c + &n / 2 pow k,c + &SUC n / 2 pow k]’
 >> ‘!x. ?n. 1 / 2 pow n < g x’ by METIS_TAC [lemma4]
 >> FULL_SIMP_TAC std_ss [SKOLEM_THM]
 >> rename1 ‘!x. 1 / 2 pow d x < g x’
 >> Know ‘!x. c <= x /\ x <= c + 1 ==>
              ?k n. n < 2 ** k /\ x IN f k n /\ f k n SUBSET cball (x,g x)’
 >- (RW_TAC std_ss [Abbr ‘f’, SUBSET_DEF, IN_INTERVAL, IN_CBALL] \\
     Q.PAT_X_ASSUM ‘!x. _ < g x’ (STRIP_ASSUME_TAC o Q.SPEC ‘x’) \\
     qabbrev_tac ‘k = d x’ \\
     MP_TAC (Q.SPECL [‘k’, ‘x’, ‘c’] lemma1c) >> RW_TAC std_ss [] \\
     qexistsl_tac [‘k’, ‘n’] >> art [] \\
     Q.X_GEN_TAC ‘y’ >> RW_TAC std_ss [dist] \\
     MATCH_MP_TAC REAL_LT_IMP_LE \\
     Q_TAC (TRANS_TAC REAL_LET_TRANS) ‘1 / 2 pow k’ >> art [] \\
     Cases_on ‘0 <= x - y’
     >- (ASM_SIMP_TAC real_ss [ABS_REDUCE] \\
         Suff ‘x <= 1 / 2 pow k + y’ >- REAL_ARITH_TAC \\
         Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘c + &SUC n / 2 pow k’ >> art [] \\
         Suff ‘c + (&SUC n / 2 pow k - 1 / 2 pow k) <= y’ >- REAL_ARITH_TAC \\
         ASM_SIMP_TAC real_ss [REAL_DIV_SUB, ADD1] \\
         simp [GSYM REAL_OF_NUM_SUB]) \\
     FULL_SIMP_TAC real_ss [GSYM real_lt, ABS_EQ_NEG] \\
     Suff ‘y - 1 / 2 pow k <= x’ >- REAL_ARITH_TAC \\
     Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘c + &n / 2 pow k’ >> art [] \\
     Suff ‘y <= c + (&n / 2 pow k + 1 / 2 pow k)’ >- REAL_ARITH_TAC \\
     ASM_SIMP_TAC real_ss [REAL_DIV_ADD, GSYM ADD1])
 >> DISCH_TAC
 (* stage work *)
 >> qabbrev_tac ‘J0 = {s | ?n k. s = f k n /\ n < 2 ** k}’
 >> Know ‘!s1 s2. s1 IN J0 /\ s2 IN J0 /\ s1 <> s2 ==>
                  s1 SUBSET s2 \/ s2 SUBSET s1 \/ nonoverlapping s1 s2’
 >- (rw [Abbr ‘J0’, Abbr ‘f’] \\
     POP_ASSUM MP_TAC >> rename1 ‘m < 2 ** l’ \\
    ‘c + &n / 2 pow k < (c + &SUC n / 2 pow k) :real /\
     c + &m / 2 pow l < (c + &SUC m / 2 pow l) :real’ by simp [] \\
     ASM_SIMP_TAC std_ss [closed_interval_11] \\
     Cases_on ‘k = l’
     >- (simp [] >> DISCH_TAC (* n <> m *) \\
         simp [closed_interval_subset_eq, closed_interval_nonoverlapping]) \\
     NTAC 5 (POP_ASSUM MP_TAC) \\
  (* applying wlog_tac *)
     wlog_tac ‘k <= l’ []
     >- (rpt STRIP_TAC \\
        ‘l <= k /\ l < k’ by simp [] \\
         ONCE_REWRITE_TAC [nonoverlapping_comm] \\
         Q.PAT_X_ASSUM ‘!k l n m. P’ (MP_TAC o Q.SPECL [‘l’, ‘k’, ‘m’, ‘n’]) \\
         METIS_TAC []) \\
     rpt STRIP_TAC \\
    ‘k < l’ by simp [] >> Q.PAT_X_ASSUM ‘k <= l’ K_TAC \\
    ‘?p. p + k = l’ by METIS_TAC [LESS_ADD] \\
     POP_ASSUM (FULL_SIMP_TAC std_ss o wrap o SYM) \\
    ‘(&n / 2 pow k) :real = &(n * 2 ** p) / 2 pow (p + k)’
       by (simp [POW_ADD] >> simp [REAL_OF_NUM_MUL, REAL_POW]) \\
     POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
    ‘(&SUC n / 2 pow k) :real = &(SUC n * 2 ** p) / 2 pow (p + k)’
       by (simp [POW_ADD] >> simp [REAL_OF_NUM_MUL, REAL_POW]) \\
     POP_ASSUM (FULL_SIMP_TAC std_ss o wrap) \\
     qabbrev_tac ‘l = p + k’ \\
     simp [closed_interval_subset_eq, closed_interval_nonoverlapping])
 >> DISCH_TAC
 >> Know ‘countable J0’
 >- (qabbrev_tac ‘t = \k. count (2 ** k)’ \\
     Know ‘J0 = {f x y | x IN univ(:num) /\ y IN t x}’
     >- (rw [Once EXTENSION, Abbr ‘J0’, Abbr ‘t’, IN_COUNT] \\
         METIS_TAC []) >> Rewr' \\
     MATCH_MP_TAC COUNTABLE_PRODUCT_DEPENDENT >> rw [])
 >> DISCH_TAC
 >> Know ‘J0 <> {}’
 >- (rw [Abbr ‘J0’, Once EXTENSION, NOT_IN_EMPTY] \\
     qexistsl_tac [‘0’, ‘0’] >> simp [])
 >> DISCH_TAC
 >> qabbrev_tac ‘J1 = J0 DIFF {s | ~?x k n. x IN E INTER s /\ s = f k n /\
                                            f k n SUBSET cball (x,g x)}’
 >> ‘J1 SUBSET J0’ by rw [SUBSET_DEF, Abbr ‘J1’]
 >> ‘countable J1’ by PROVE_TAC [COUNTABLE_SUBSET]
 >> Know ‘!s. s IN J1 ==> ?x k n. x IN E /\ x IN s /\ s = f k n /\ n < 2 ** k /\
                                  f k n SUBSET cball (x,g x)’
 >- (rw [Abbr ‘J1’, Abbr ‘J0’] \\
     rename1 ‘y IN f l m’ \\
     qexistsl_tac [‘y’, ‘k’, ‘n’] >> rw [] >> gs [])
 >> DISCH_TAC
 (* stage work *)
 >> Know ‘!x. x IN E ==>
              ?s k n. s IN J1 /\ s = f k n /\ n < 2 ** k /\ x IN f k n /\
                      f k n SUBSET cball (x,g x)’
 >- (rpt (Q.PAT_X_ASSUM ‘countable _’ K_TAC) \\
     rpt (Q.PAT_X_ASSUM ‘_ SUBSET _’  K_TAC) \\
     rw [Abbr ‘J1’, Abbr ‘J0’] \\
     Q.PAT_X_ASSUM ‘!x. c <= x /\ x <= c + 1 ==> ?k n. _’ (MP_TAC o Q.SPEC ‘x’) \\
     RW_TAC std_ss [] \\
     qexistsl_tac [‘k’, ‘n’] >> art [] \\
     CONJ_TAC >- (qexistsl_tac [‘n’, ‘k’] >> art []) \\
     qexistsl_tac [‘x’, ‘k’, ‘n’] >> art [])
 >> DISCH_TAC
 (* “E <> {}” is needed here *)
 >> Know ‘J1 <> {}’
 >- (rw [Once EXTENSION, NOT_IN_EMPTY] \\
    ‘?x. x IN E’ by METIS_TAC [MEMBER_NOT_EMPTY] \\
     METIS_TAC [])
 >> DISCH_TAC
 (* J2 is done by removing smaller sets from J1 *)
 >> qabbrev_tac ‘J2 = J1 DIFF {s | s IN J1 /\ ?t. t IN J1 /\ s PSUBSET t}’
 >> ‘J2 SUBSET J1’ by rw [SUBSET_DEF, Abbr ‘J2’]
 >> ‘countable J2’ by PROVE_TAC [COUNTABLE_SUBSET]
 >> Know ‘J2 <> {}’
 >- (rpt (Q.PAT_X_ASSUM ‘countable _’ K_TAC) \\
     Q.PAT_X_ASSUM ‘J2 SUBSET J1’ K_TAC \\
     rw [Abbr ‘J2’, Once EXTENSION, NOT_IN_EMPTY, PSUBSET_DEF] \\
     SIMP_TAC (bool_ss ++ DNF_ss) [GSYM IMP_DISJ_THM] \\
     qabbrev_tac ‘P = \k. ?x n. n < 2 ** k /\ x IN E INTER f k n /\
                                f k n SUBSET cball (x,g x)’ \\
     MP_TAC (Q.SPEC ‘P’ LEAST_EXISTS_IMP) \\
     qabbrev_tac ‘l = $LEAST P’ (* here “l” means least *) \\
     impl_tac
     >- (simp [Abbr ‘P’] \\
        ‘?s. s IN J1’ by METIS_TAC [MEMBER_NOT_EMPTY] \\
         Q.PAT_X_ASSUM ‘!s. s IN J1 ==> ?x k n. _’ (MP_TAC o Q.SPEC ‘s’) \\
         RW_TAC std_ss [] \\
         qexistsl_tac [‘k’, ‘x’, ‘n’] >> art []) \\
     rw [Abbr ‘P’] \\
     Q.EXISTS_TAC ‘f l n’ \\
     CONJ_TAC
     >- (rw [Abbr ‘J1’, Abbr ‘J0’]
         >- (qexistsl_tac [‘n’, ‘l’] >> art []) \\
         qexistsl_tac [‘x’, ‘l’, ‘n’] >> art []) \\
     NTAC 2 STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!s. s IN J1 ==> _’ (MP_TAC o Q.SPEC ‘t’) >> POP_ORW \\
     RW_TAC std_ss [] >> rename1 ‘y IN f k m’ \\
     Know ‘c + &SUC n / 2 pow l - (c + &n / 2 pow l) :real <=
           c + &SUC m / 2 pow k - (c + &m / 2 pow k)’
     >- (MATCH_MP_TAC closed_interval_subset \\
         REWRITE_TAC [lemma5a] \\
         POP_ASSUM MP_TAC >> simp [Abbr ‘f’]) \\
     simp [lemma6a] \\
     Know ‘2 pow k <= (2 pow l) :real <=> k <= l’
     >- (MATCH_MP_TAC REAL_POW_MONO_EQ >> simp []) >> Rewr' \\
     DISCH_TAC \\
    ‘k = l \/ k < l’ by simp [] (* 2 subgoals *)
     >- (Q.PAT_X_ASSUM ‘f l n SUBSET f k m’ MP_TAC \\
         simp [Abbr ‘f’, closed_interval_subset_eq, lemma5] \\
         simp [LE_ANTISYM]) \\
     METIS_TAC [])
 >> DISCH_TAC
 >> Know ‘!x. x IN E ==> ?s. x IN s /\ s IN J2’
 >- (rpt STRIP_TAC \\
     qabbrev_tac ‘P = \k. ?y n. n < 2 ** k /\
                                x IN E INTER f k n /\
                                y IN E INTER f k n /\
                                f k n SUBSET cball (y,g y)’ \\
  (* NOTE: “$LEAST P” is biggest interval for any y IN E containing also x *)
     MP_TAC (Q.SPEC ‘P’ LEAST_EXISTS_IMP) \\
     qabbrev_tac ‘l = $LEAST P’ \\
     impl_tac
     >- (simp [Abbr ‘P’] \\
         Q.PAT_X_ASSUM ‘!x. x IN E ==> ?s k n. _’ drule >> rw [] \\
         qexistsl_tac [‘k’, ‘x’, ‘n’] >> art []) \\
     rw [Abbr ‘P’] \\
     Q.EXISTS_TAC ‘f l n’ >> art [] \\
     Q.PAT_X_ASSUM ‘J2 SUBSET J1’ K_TAC \\
     Q.PAT_X_ASSUM ‘countable J2’ K_TAC \\
     Q.PAT_X_ASSUM ‘K2 <> {}’     K_TAC \\
     rw [Abbr ‘J2’]
     >- (rw [Abbr ‘J1’, Abbr ‘J0’] >- (qexistsl_tac [‘n’, ‘l’] >> art []) \\
         qexistsl_tac [‘y’, ‘l’, ‘n’] >> art []) \\
     STRONG_DISJ_TAC \\
     RW_TAC std_ss [PSUBSET_DEF, GSYM IMP_DISJ_THM] \\
     Q.PAT_X_ASSUM ‘!s. s IN J1 ==> _’ (MP_TAC o Q.SPEC ‘t’) \\
     RW_TAC std_ss [] >> rename1 ‘z IN f k m’ \\
     Know ‘c + &SUC n / 2 pow l - (c + &n / 2 pow l) :real <=
           c + &SUC m / 2 pow k - (c + &m / 2 pow k)’
     >- (MATCH_MP_TAC closed_interval_subset \\
         REWRITE_TAC [lemma5a] \\
         Q.PAT_X_ASSUM ‘f l n SUBSET f k m’ MP_TAC \\
         simp [Abbr ‘f’]) \\
     simp [lemma6a] \\
     Know ‘2 pow k <= (2 pow l) :real <=> k <= l’
     >- (MATCH_MP_TAC REAL_POW_MONO_EQ >> simp []) >> Rewr' \\
     DISCH_TAC \\
    ‘k = l \/ k < l’ by simp [] (* 2 subgoals *)
     >- (Q.PAT_X_ASSUM ‘f l n SUBSET f k m’ MP_TAC \\
         simp [Abbr ‘f’, closed_interval_subset_eq, lemma5] \\
         simp [LE_ANTISYM]) \\
    ‘x IN f k m’ by PROVE_TAC [SUBSET_DEF] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> Know ‘!s1 s2. s1 IN J2 /\ s2 IN J2 /\ s1 <> s2 ==> ~(s1 SUBSET s2)’
 >- (rw [Abbr ‘J2’, PSUBSET_DEF] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> ‘?J. J2 = IMAGE J univ(:num)’ by METIS_TAC [COUNTABLE_AS_IMAGE]
 >> ‘!i. J i IN J2’ by rw []
 (* stage work *)
 >> Know ‘!i. ?xs. FST xs IN E /\
                   J i = f (FST (SND xs)) (SND (SND xs)) /\
                   SND (SND xs) < 2 ** FST (SND xs) /\ FST xs IN J i /\
                   J i SUBSET cball (FST xs,g (FST xs))’
 >- (Q.X_GEN_TAC ‘i’ \\
    ‘J i IN J1’ by PROVE_TAC [SUBSET_DEF] \\
     Q.PAT_X_ASSUM ‘!s. s IN J1 ==> ?x k n. _’ (MP_TAC o Q.SPEC ‘J (i :num)’) \\
     RW_TAC std_ss [] \\
     Q.EXISTS_TAC ‘(x,k,n)’ >> simp [] >> fs [])
 >> simp [SKOLEM_THM]
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘ts’ STRIP_ASSUME_TAC)
 >> qexistsl_tac [‘J’, ‘\i. FST (ts i)’]
 (* nonoverlapping *)
 >> Know ‘!i j. J i <> J j ==> nonoverlapping (J i) (J j)’
 >- (POP_ASSUM K_TAC >> rpt STRIP_TAC \\
    ‘J2 SUBSET J0’ by PROVE_TAC [SUBSET_TRANS] \\
    ‘!i. J i IN J0’ by PROVE_TAC [SUBSET_DEF] \\
     METIS_TAC [])
 >> Rewr
 >> Know ‘!i. closed_interval (J i)’
 >- (rw [Abbr ‘f’, closed_interval_def] \\
     qexistsl_tac [‘c + &SND (SND (ts i)) / 2 pow FST (SND (ts i))’,
                   ‘c + &SUC (SND (SND (ts i))) / 2 pow FST (SND (ts i))’] \\
     REFL_TAC)
 >> Rewr
 (* !x. x IN E ==> ?s. x IN s /\ ?x. s = J x *)
 >> reverse CONJ_TAC
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!x. x IN E ==> ?s. x IN s /\ s IN J2’ drule >> rw [])
 (* stage work *)
 >> Q.X_GEN_TAC ‘i’ >> simp []
 >> POP_ASSUM (MP_TAC o Q.SPEC ‘i’)
 >> Cases_on ‘ts i’ >> simp []
 >> PairCases_on ‘r’ >> simp []
 >> rename1 ‘ts i = (y,k,n)’ >> simp []
 >> STRIP_TAC
 >> reverse CONJ_TAC
 >- (CONJ_TAC (* y IN f k n *)
     >- (Q.PAT_X_ASSUM ‘J i = f k n’ (REWRITE_TAC o wrap o SYM) >> art []) \\
     rpt STRIP_TAC \\
     Know ‘x IN cball (y,g y)’ >- METIS_TAC [SUBSET_DEF] \\
     simp [IN_CBALL])
 (* !x. x IN f k n ==> c <= x /\ x <= c + 1 *)
 >> RW_TAC real_ss [Abbr ‘f’, IN_INTERVAL]
 >| [ (* goal 1 (of 2) *)
      Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘c + &n / 2 pow k’ >> art [] \\
      simp [REAL_LE_ADDR],
      (* goal 2 (of 2) *)
      Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘c + &SUC n / 2 pow k’ >> art [] \\
      simp [ADD1, REAL_POW] ]
QED

(* NOTE: “J i <> J j” changed to “i <> j”, i.e. no duplicated elements. *)
Theorem dyadic_covering_lemma_unit'[local] :
    !g E c. gauge g /\ E <> {} /\ E SUBSET interval [c,c + 1] ==>
            ?J t. (!i. J i SUBSET interval [c,c + 1] /\
                       closed_interval (J i) /\
                       t i IN E INTER J (i :num) /\
                       J i SUBSET g (t i)) /\
                  (!i j. i <> j ==> nonoverlapping (J i) (J j)) /\
                   E SUBSET BIGUNION (IMAGE J UNIV)
Proof
    rpt STRIP_TAC
 >> Know ‘?d. gauge UNIV d /\ !x. cball (x,d x) SUBSET (g x)’
 >- (fs [gauge_def, OPEN_CONTAINS_CBALL, FORALL_AND_THM,
         GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] \\
     Q.EXISTS_TAC ‘\x. f x x’ \\
     rw [integralTheory.gauge'])
 >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘d’, ‘E’, ‘c’] dyadic_covering_lemma_unit)
 >> RW_TAC std_ss [FORALL_AND_THM]
 >> qabbrev_tac ‘s = IMAGE J UNIV’
 >> ‘countable s’ by simp [image_countable, Abbr ‘s’]
 >> reverse (Cases_on ‘FINITE s’)
 >- (FULL_SIMP_TAC std_ss [COUNTABLE_ALT_BIJ] \\
     qabbrev_tac ‘h = enumerate s’ \\
     Know ‘!i. h i IN s’
     >- (Q.X_GEN_TAC ‘i’ \\
         Q.PAT_X_ASSUM ‘BIJ h UNIV s’ MP_TAC \\
         rw [BIJ_DEF, INJ_DEF]) >> DISCH_TAC \\
     Know ‘!i j. i <> j ==> h i <> h j’
     >- (rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘BIJ h UNIV s’ MP_TAC \\
         rw [BIJ_DEF, INJ_DEF] \\
         DISJ1_TAC >> qexistsl_tac [‘i’, ‘j’] >> art []) >> DISCH_TAC \\
     Know ‘!i. ?n. h i = J n’
     >- (Q.X_GEN_TAC ‘i’ \\
         Q.PAT_X_ASSUM ‘!i. h i IN s’ (MP_TAC o Q.SPEC ‘i’) \\
         rw [Abbr ‘s’]) \\
     RW_TAC std_ss [SKOLEM_THM] (* this asserts f *) \\
     qexistsl_tac [‘h’, ‘t o f’] \\
     ASM_SIMP_TAC std_ss [o_DEF] \\
     CONJ_TAC
     >- (Q.X_GEN_TAC ‘i’ \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘cball (t (f i),d (t (f i)))’ \\
         simp []) \\
     CONJ_TAC
     >- (rpt STRIP_TAC \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         Q.PAT_X_ASSUM ‘!i. h i = J (f i)’ (REWRITE_TAC o wrap o GSYM) \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     Suff ‘IMAGE h UNIV = s’ >- simp [] \\
     POP_ASSUM K_TAC (* !i. h i = J (f i) *) \\
     rw [Once EXTENSION] \\
     EQ_TAC >- (rw [] >> simp []) \\
     Q.PAT_X_ASSUM ‘BIJ h UNIV s’ MP_TAC \\
     rw [BIJ_DEF, SURJ_DEF] \\
     Q.PAT_X_ASSUM ‘!x. x IN s ==> ?y. h y = x’ (MP_TAC o Q.SPEC ‘x’) \\
     simp [] >> DISCH_THEN (Q.X_CHOOSE_THEN ‘j’ STRIP_ASSUME_TAC) \\
     Q.EXISTS_TAC ‘j’ >> art [])
 (* FINITE s *)
 >> FULL_SIMP_TAC std_ss [FINITE_BIJ_COUNT_EQ, GSYM MEMBER_NOT_EMPTY]
 >> rename1 ‘BIJ h (count n) s’
 >> Know ‘!i. i < n ==> h i IN s’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘BIJ h (count n) s’ MP_TAC >> rw [BIJ_DEF, INJ_DEF])
 >> DISCH_TAC
 >> Know ‘!i j. i < n /\ j < n /\ i <> j ==> h i <> h j’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘BIJ h (count n) s’ MP_TAC >> rw [BIJ_DEF, INJ_DEF] \\
     DISJ1_TAC >> qexistsl_tac [‘i’, ‘j’] >> art [])
 >> DISCH_TAC
 >> Know ‘!i. i < n ==> ?n. h i = J n’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < n ==> h i IN s’ (MP_TAC o Q.SPEC ‘i’) \\
     rw [Abbr ‘s’])
 >> RW_TAC std_ss [EXT_SKOLEM_THM'] (* this asserts f *)
 >> qabbrev_tac ‘L = \i. if i < n then h i else interval [x,x]’
 >> qabbrev_tac ‘u = \i. if i < n then t (f i) else x’
 >> qexistsl_tac [‘L’, ‘u’]
 >> Know ‘!i j. i <> j ==> nonoverlapping (L i) (L j)’
 >- (rw [Abbr ‘L’] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       FIRST_X_ASSUM MATCH_MP_TAC \\
       Q.PAT_X_ASSUM ‘!i. i < n ==> h i = J (f i)’
         (ASM_SIMP_TAC std_ss o wrap o GSYM),
       (* goal 2 (of 4) *)
       simp [nonoverlapping_def, INTERIOR_INTERVAL] \\
       simp [iffLR (cj 2 INTERVAL_EQ_EMPTY)],
       (* goal 3 (of 4) *)
       simp [nonoverlapping_def, INTERIOR_INTERVAL] \\
       simp [iffLR (cj 2 INTERVAL_EQ_EMPTY)],
       (* goal 4 (of 4) *)
       simp [nonoverlapping_def, INTERIOR_INTERVAL] \\
       simp [iffLR (cj 2 INTERVAL_EQ_EMPTY)] ])
 >> Rewr
 >> reverse CONJ_TAC
 >- (simp [SUBSET_DEF] \\
     Q.X_GEN_TAC ‘w’ >> DISCH_TAC \\
     Know ‘w IN BIGUNION s’ >- PROVE_TAC [SUBSET_DEF] \\
     rw [IN_BIGUNION] >> rename1 ‘A IN s’ \\
     Q.EXISTS_TAC ‘A’ >> art [] \\
     Q.PAT_X_ASSUM ‘BIJ h (count n) s’ MP_TAC \\
     rw [BIJ_DEF, SURJ_DEF] \\
     POP_ASSUM (MP_TAC o Q.SPEC ‘A’) >> art [] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘j’ STRIP_ASSUME_TAC) \\
     Q.EXISTS_TAC ‘j’ >> rw [Abbr ‘L’])
 >> RW_TAC std_ss [Abbr ‘L’, Abbr ‘u’, closed_interval_interval] (* 4 subgoals *)
 >| [ (* goal 1 (of 4) *)
     ‘x IN interval [(c,c + 1)]’ by PROVE_TAC [SUBSET_DEF] \\
      simp [SUBSET_DEF, INTERVAL_SING],
      (* goal 2 (of 4) *)
      simp [INTERVAL_SING],
      (* goal 3 (of 4) *)
      Q_TAC (TRANS_TAC SUBSET_TRANS) ‘cball (t (f i),d (t (f i)))’ \\
      simp [],
      (* goal 4 (of 4) *)
      simp [INTERVAL_SING, SUBSET_DEF, CENTRE_IN_CBALL] \\
      Suff ‘x IN cball (x,d x)’ >- METIS_TAC [SUBSET_DEF] \\
      rw [IN_CBALL, DIST_REFL] \\
      MATCH_MP_TAC REAL_LT_IMP_LE \\
      fs [integralTheory.gauge'] ]
QED

Theorem UNIT_INTERVAL_PARTITION :
    univ(:real) =
    BIGUNION (IMAGE (\i. interval [real_of_int i, real_of_int i + 1])
                    univ(:int))
Proof
    rw [Once EXTENSION, IN_BIGUNION_IMAGE, IN_INTERVAL]
 >> Q.EXISTS_TAC ‘INT_FLOOR x’
 >> MP_TAC (Q.SPEC ‘x’ INT_FLOOR_BOUNDS') (* intrealTheory *)
 >> qabbrev_tac ‘r = real_of_int (INT_FLOOR x)’
 >> REAL_ARITH_TAC
QED

(* cf. INFINITE_INT_UNIV *)
Theorem COUNTABLE_INT_UNIV :
    countable univ(:int)
Proof
    Suff ‘UNIV = IMAGE int_of_num UNIV UNION IMAGE (\n. -int_of_num n) UNIV’
 >- (Rewr' \\
     MATCH_MP_TAC COUNTABLE_UNION_IMP (* cardinalTheory *) \\
     CONJ_TAC >> MATCH_MP_TAC COUNTABLE_IMAGE >> simp [])
 >> rw [Once EXTENSION]
 >> STRIP_ASSUME_TAC (Q.SPEC ‘x’ int_cases)
 >| [ DISJ1_TAC >> Q.EXISTS_TAC ‘n’ >> art [],
      DISJ2_TAC >> Q.EXISTS_TAC ‘n’ >> art [] ]
QED

(* 18.15 Dyadic Covering Lemma [2, p.311] *)
Theorem dyadic_covering_lemma :
    !g E. gauge UNIV g /\ E <> {} ==>
          ?J t. (!i. closed_interval (J i) /\
                     t i IN E INTER J (i :num) /\
                     J i SUBSET cball (t i,g (t i))) /\
                (!i j. J i <> J j ==> nonoverlapping (J i) (J j)) /\
                 E SUBSET BIGUNION (IMAGE J UNIV)
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘e = \i. E INTER interval [real_of_int i,real_of_int i + 1]’
 >> ‘!i. e i SUBSET interval [real_of_int i,real_of_int i + 1]’
      by rw [SUBSET_DEF, Abbr ‘e’, IN_INTERVAL]
 (* applying dyadic_covering_lemma_unit *)
 >> Know ‘!n. e n <> {} ==>
              ?J t. (!i. J i SUBSET interval [real_of_int n,real_of_int n + 1] /\
                         closed_interval (J i) /\
                         t i IN e n INTER J (i :num) /\
                         J i SUBSET cball (t i,g (t i))) /\
                    (!i j. J i <> J j ==> nonoverlapping (J i) (J j)) /\
                     e n SUBSET BIGUNION (IMAGE J UNIV)’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC dyadic_covering_lemma_unit >> simp [])
 (* this asserts f and f' in place of J and t *)
 >> DISCH_THEN (STRIP_ASSUME_TAC o
                SIMP_RULE std_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM])
 >> Know ‘E = BIGUNION (IMAGE e UNIV)’
 >- (simp [Abbr ‘e’, GSYM BIGUNION_OVER_INTER_R] \\
     simp [GSYM UNIT_INTERVAL_PARTITION])
 >> DISCH_TAC
 >> Know ‘?n0. e n0 <> {}’
 >- (Suff ‘BIGUNION (IMAGE e univ(:int)) <> {}’
     >- (POP_ASSUM K_TAC \\
         rw [Once EXTENSION, IN_BIGUNION_IMAGE] \\
         Cases_on ‘x = {}’ >> fs [] \\
         rename1 ‘x = e n0’ \\
         Q.EXISTS_TAC ‘n0’ >> rw []) \\
     POP_ASSUM (art o wrap o SYM))
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘E = _’ (REWRITE_TAC o wrap)
 (* NOTE: Here I want to construct an non-empty countable set holding pairs
    (a,b) which comes from all (f i,f' i) pairs of each non-empty (e' n).
    Then, by COUNTABLE_ENUM or COUNTABLE_AS_IMAGE, the final existence of J/t
    is derived from this countable set.
  *)
 >> qabbrev_tac ‘a = \i. IMAGE (\j. (f i j, f' i j)) UNIV’
 >> qabbrev_tac ‘s = \i. if e i <> {} then a i else {}’
 >> qabbrev_tac ‘c = BIGUNION (IMAGE s UNIV)’
 >> Know ‘c <> {}’
 >- (simp [Abbr ‘c’, Once EXTENSION, IN_BIGUNION_IMAGE, Abbr ‘s’, NOT_IN_EMPTY] \\
     Suff ‘?i. e i <> {}’
     >- (STRIP_TAC \\
         Q.EXISTS_TAC ‘a i’ \\
         Know ‘a i <> {}’ >- rw [Abbr ‘a’, Once EXTENSION, NOT_IN_EMPTY] \\
         rw [] >> Q.EXISTS_TAC ‘i’ >> art []) \\
     Q.EXISTS_TAC ‘n0’ \\
     rw [Abbr ‘e’, Once EXTENSION, NOT_IN_EMPTY] \\
     simp [MEMBER_NOT_EMPTY])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘e n0 <> {}’ K_TAC (* no more needed *)
 >> Know ‘countable c’
 >- (POP_ASSUM K_TAC (* c <> {} *) \\
     qunabbrev_tac ‘c’ \\
     MATCH_MP_TAC COUNTABLE_BIGUNION \\
     CONJ_TAC >- (MATCH_MP_TAC COUNTABLE_IMAGE \\
                  REWRITE_TAC [COUNTABLE_INT_UNIV]) \\
     rw [Abbr ‘s’] \\
     rename1 ‘countable (if e n <> {} then a n else {})’ \\
     Cases_on ‘e n = {}’ >> simp [COUNTABLE_EMPTY, Abbr ‘a’])
 >> DISCH_TAC
 (* stage work *)
 >> Know ‘!z1 z2. z1 IN c /\ z2 IN c /\ FST z1 <> FST z2 ==>
                  nonoverlapping (FST z1) (FST z2)’
 >- (rw [Abbr ‘c’, Abbr ‘s’, IN_BIGUNION_IMAGE] \\
     rename1 ‘z2 IN if e j <> {} then a j else {}’ \\
     Cases_on ‘e i = {}’ >> fs [] \\
     Cases_on ‘e j = {}’ >> fs [] \\
     Q.PAT_X_ASSUM ‘z2 IN a j’ MP_TAC \\
     Q.PAT_X_ASSUM ‘z1 IN a i’ MP_TAC \\
     Q.PAT_X_ASSUM ‘FST z1 <> FST z2’ MP_TAC \\
     rw [Abbr ‘a’] >> fs [] >> rename1 ‘f i m <> f j n’ \\
     Cases_on ‘i = j’ >- rw [] \\
     Q.PAT_X_ASSUM ‘f i m <> f j n’ K_TAC \\
    ‘f i m SUBSET interval [real_of_int i,real_of_int i + 1] /\
     f j n SUBSET interval [real_of_int j,real_of_int j + 1]’ by rw [] \\
     MATCH_MP_TAC nonoverlapping_subset_inclusive \\
     qexistsl_tac [‘interval [real_of_int i,real_of_int i + 1]’,
                   ‘interval [real_of_int j,real_of_int j + 1]’] \\
     simp [nonoverlapping_def, INTERIOR_INTERVAL] \\
     simp [closed_interval_disjoint_eq] \\
     SIMP_TAC real_ss [GSYM real_of_int_add, GSYM real_of_int_num] \\
     simp [] \\
     Q.PAT_X_ASSUM ‘i <> j’ MP_TAC >> intLib.ARITH_TAC)
 >> DISCH_TAC
 (* stage work *)
 >> Suff ‘!z. z IN c ==> closed_interval (FST z) /\
                         SND z IN BIGUNION (IMAGE e UNIV) INTER FST z /\
                         FST z SUBSET cball (SND z,g (SND z))’
 >- (DISCH_TAC \\
     MP_TAC (ISPEC “c :(real set # real) set” COUNTABLE_AS_IMAGE) \\
     simp [] >> DISCH_THEN (Q.X_CHOOSE_THEN ‘h’ STRIP_ASSUME_TAC) \\
    ‘!n. h n IN c’ by rw [] \\
     qexistsl_tac [‘FST o h’, ‘SND o h’] >> simp [o_DEF] \\
     CONJ_TAC
     >- (Q.X_GEN_TAC ‘n’ \\
         Q.PAT_X_ASSUM ‘!z. z IN c ==> _’ (MP_TAC o Q.SPEC ‘h (n :num)’) >> rw []) \\
     simp [SUBSET_DEF, IN_BIGUNION_IMAGE] \\
     Q.X_GEN_TAC ‘x’ \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘n’ STRIP_ASSUME_TAC) \\
     Cases_on ‘e n = {}’ >- fs [] \\
     Know ‘x IN BIGUNION (IMAGE (f n) UNIV)’ >- METIS_TAC [SUBSET_DEF] \\
     simp [IN_BIGUNION_IMAGE] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘j’ STRIP_ASSUME_TAC) \\
     Know ‘(f n j,f' n j) IN c’
     >- (Q.PAT_X_ASSUM ‘c = IMAGE h UNIV’ K_TAC \\
         rw [Abbr ‘c’] \\
         Q.EXISTS_TAC ‘s n’ \\
         reverse CONJ_TAC >- (Q.EXISTS_TAC ‘n’ >> simp []) \\
         rw [Abbr ‘s’] \\
         rw [Abbr ‘a’] \\
         Q.EXISTS_TAC ‘j’ >> simp []) \\
     Q.PAT_X_ASSUM ‘c = IMAGE h UNIV’ (REWRITE_TAC o wrap) >> simp [] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘i’ STRIP_ASSUME_TAC) \\
     Q.EXISTS_TAC ‘i’ \\
     POP_ASSUM (simp o wrap o SYM))
 (* stage work *)
 >> NTAC 3 (POP_ASSUM K_TAC)
 >> Q.X_GEN_TAC ‘z’
 >> simp [Abbr ‘c’, Abbr ‘s’, IN_BIGUNION_IMAGE, SUBSET_DEF]
 >> STRIP_TAC
 >> Cases_on ‘e i = {}’ >> fs []
 >> Q.PAT_X_ASSUM ‘z IN a i’ MP_TAC
 >> simp [Abbr ‘a’]
 >> STRIP_TAC >> POP_ORW >> simp []
 >> CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘!n. e n <> {} ==> _’ (MP_TAC o Q.SPEC ‘i’) >> simp [] \\
     STRIP_TAC \\
     NTAC 2 (POP_ASSUM K_TAC) \\
     POP_ASSUM (MP_TAC o Q.SPEC ‘j’) >> rw [Abbr ‘e’] \\
     Q.EXISTS_TAC ‘i’ >> art [])
 >> rw []
 >> Q.PAT_X_ASSUM ‘!n. e n <> {} ==> _’ (MP_TAC o Q.SPEC ‘i’) >> simp []
 >> STRIP_TAC
 >> NTAC 2 (POP_ASSUM K_TAC)
 >> POP_ASSUM (MP_TAC o Q.SPEC ‘j’)
 >> rw [SUBSET_DEF]
QED

(* NOTE: This version uses “gauge” of integrationTheory.gauge_def, and it
   improve the conclusion to “!i j. i <> j ==> nonoverlapping (J i) (J j)”,
   which means that the constructed sequence is indeed infinitely countable.
 *)
Theorem dyadic_covering_lemma' :
    !g E. gauge g /\ E <> {} ==>
          ?J t. (!i. closed_interval (J i) /\
                     t i IN E INTER J (i :num) /\
                     J i SUBSET g (t i)) /\
                (!i j. i <> j ==> nonoverlapping (J i) (J j)) /\
                 E SUBSET BIGUNION (IMAGE J UNIV)
Proof
    rpt STRIP_TAC
 >> Know ‘?d. gauge UNIV d /\ !x. cball (x,d x) SUBSET (g x)’
 >- (fs [gauge_def, OPEN_CONTAINS_CBALL, FORALL_AND_THM,
         GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] \\
     Q.EXISTS_TAC ‘\x. f x x’ \\
     rw [integralTheory.gauge'])
 >> STRIP_TAC
 >> MP_TAC (Q.SPECL [‘d’, ‘E’] dyadic_covering_lemma)
 >> RW_TAC std_ss [FORALL_AND_THM]
 >> qabbrev_tac ‘s = IMAGE J UNIV’
 >> ‘countable s’ by simp [image_countable, Abbr ‘s’]
 >> reverse (Cases_on ‘FINITE s’)
 >- (FULL_SIMP_TAC std_ss [COUNTABLE_ALT_BIJ] \\
     qabbrev_tac ‘h = enumerate s’ \\
     Know ‘!i. h i IN s’
     >- (Q.X_GEN_TAC ‘i’ \\
         Q.PAT_X_ASSUM ‘BIJ h UNIV s’ MP_TAC \\
         rw [BIJ_DEF, INJ_DEF]) >> DISCH_TAC \\
     Know ‘!i j. i <> j ==> h i <> h j’
     >- (rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘BIJ h UNIV s’ MP_TAC \\
         rw [BIJ_DEF, INJ_DEF] \\
         DISJ1_TAC >> qexistsl_tac [‘i’, ‘j’] >> art []) >> DISCH_TAC \\
     Know ‘!i. ?n. h i = J n’
     >- (Q.X_GEN_TAC ‘i’ \\
         Q.PAT_X_ASSUM ‘!i. h i IN s’ (MP_TAC o Q.SPEC ‘i’) \\
         rw [Abbr ‘s’]) \\
     RW_TAC std_ss [SKOLEM_THM] (* this asserts f *) \\
     qexistsl_tac [‘h’, ‘t o f’] \\
     ASM_SIMP_TAC std_ss [o_DEF] \\
     CONJ_TAC
     >- (Q.X_GEN_TAC ‘i’ \\
         Q_TAC (TRANS_TAC SUBSET_TRANS) ‘cball (t (f i),d (t (f i)))’ \\
         simp []) \\
     CONJ_TAC
     >- (rpt STRIP_TAC \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         Q.PAT_X_ASSUM ‘!i. h i = J (f i)’ (REWRITE_TAC o wrap o GSYM) \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     Suff ‘IMAGE h UNIV = s’ >- simp [] \\
     POP_ASSUM K_TAC (* !i. h i = J (f i) *) \\
     rw [Once EXTENSION] \\
     EQ_TAC >- (rw [] >> simp []) \\
     Q.PAT_X_ASSUM ‘BIJ h UNIV s’ MP_TAC \\
     rw [BIJ_DEF, SURJ_DEF] \\
     Q.PAT_X_ASSUM ‘!x. x IN s ==> ?y. h y = x’ (MP_TAC o Q.SPEC ‘x’) \\
     simp [] >> DISCH_THEN (Q.X_CHOOSE_THEN ‘j’ STRIP_ASSUME_TAC) \\
     Q.EXISTS_TAC ‘j’ >> art [])
 (* FINITE s *)
 >> FULL_SIMP_TAC std_ss [FINITE_BIJ_COUNT_EQ, GSYM MEMBER_NOT_EMPTY]
 >> Know ‘!i. i < n ==> c i IN s’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘BIJ c (count n) s’ MP_TAC >> rw [BIJ_DEF, INJ_DEF])
 >> DISCH_TAC
 >> Know ‘!i j. i < n /\ j < n /\ i <> j ==> c i <> c j’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘BIJ c (count n) s’ MP_TAC >> rw [BIJ_DEF, INJ_DEF] \\
     DISJ1_TAC >> qexistsl_tac [‘i’, ‘j’] >> art [])
 >> DISCH_TAC
 >> Know ‘!i. i < n ==> ?n. c i = J n’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!i. i < n ==> c i IN s’ (MP_TAC o Q.SPEC ‘i’) \\
     rw [Abbr ‘s’])
 >> RW_TAC std_ss [EXT_SKOLEM_THM'] (* this asserts f *)
 >> qabbrev_tac ‘L = \i. if i < n then c i else interval [x,x]’
 >> qabbrev_tac ‘u = \i. if i < n then t (f i) else x’
 >> qexistsl_tac [‘L’, ‘u’]
 >> Know ‘!i j. i <> j ==> nonoverlapping (L i) (L j)’
 >- (rw [Abbr ‘L’] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       FIRST_X_ASSUM MATCH_MP_TAC \\
       Q.PAT_X_ASSUM ‘!i. i < n ==> c i = J (f i)’
         (ASM_SIMP_TAC std_ss o wrap o GSYM),
       (* goal 2 (of 4) *)
       simp [nonoverlapping_def, INTERIOR_INTERVAL] \\
       simp [iffLR (cj 2 INTERVAL_EQ_EMPTY)],
       (* goal 3 (of 4) *)
       simp [nonoverlapping_def, INTERIOR_INTERVAL] \\
       simp [iffLR (cj 2 INTERVAL_EQ_EMPTY)],
       (* goal 4 (of 4) *)
       simp [nonoverlapping_def, INTERIOR_INTERVAL] \\
       simp [iffLR (cj 2 INTERVAL_EQ_EMPTY)] ])
 >> Rewr
 >> reverse CONJ_TAC
 >- (simp [SUBSET_DEF] \\
     Q.X_GEN_TAC ‘w’ >> DISCH_TAC \\
     Know ‘w IN BIGUNION s’ >- PROVE_TAC [SUBSET_DEF] \\
     rw [IN_BIGUNION] >> rename1 ‘A IN s’ \\
     Q.EXISTS_TAC ‘A’ >> art [] \\
     Q.PAT_X_ASSUM ‘BIJ c (count n) s’ MP_TAC \\
     rw [BIJ_DEF, SURJ_DEF] \\
     POP_ASSUM (MP_TAC o Q.SPEC ‘A’) >> art [] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘j’ STRIP_ASSUME_TAC) \\
     Q.EXISTS_TAC ‘j’ >> rw [Abbr ‘L’])
 >> RW_TAC std_ss [Abbr ‘L’, Abbr ‘u’, closed_interval_interval] (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      simp [IN_INTERVAL],
      (* goal 2 (of 3) *)
      Q_TAC (TRANS_TAC SUBSET_TRANS) ‘cball (t (f i),d (t (f i)))’ \\
      simp [],
      (* goal 3 (of 3) *)
      simp [closed_interval_def, SUBSET_DEF, IN_INTERVAL] \\
      Q.X_GEN_TAC ‘w’ >> STRIP_TAC \\
     ‘w = x’ by PROVE_TAC [REAL_LE_ANTISYM] >> POP_ORW \\
      FULL_SIMP_TAC std_ss [gauge_def] ]
QED

Definition integrable_sets_def :
    integrable_sets X = {E | indicator E integrable_on X}
End

(* NOTE: The other direction is not true. For example, UNIV is in lebesgue,
   but “indicator UNIV integrable_on UNIV” doesn't hold, as the integral
   is clearly infinity, not a normal real value.

   This set is denoted as I(R) in [2, p.300] (Definition 18.1).
 *)
Theorem integrable_sets_subset_lebesgue :
    integrable_sets UNIV SUBSET measurable_sets lebesgue
Proof
    rw [integrable_sets_def, SUBSET_DEF, lebesgue_def, line_def]
 >> MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL
 >> Q.EXISTS_TAC ‘UNIV’ >> simp []
QED

(* |- !E. indicator E integrable_on univ(:real) ==>
          E IN measurable_sets lebesgue
 *)
Theorem integrable_indicator_imp_sets_lebesgue =
        integrable_sets_subset_lebesgue
     |> SRULE [SUBSET_DEF, integrable_sets_def] |> Q.SPEC ‘E’ |> GEN_ALL

(* This restrict version is based on INTEGRAL_ABS_BOUND_INTEGRAL *)
Theorem INTEGRAL_MONO_LEMMA :
    !f g s. f integrable_on s /\ g integrable_on s /\
           (!x. x IN s ==> 0 <= f x) /\
           (!x. x IN s ==> 0 <= g x) /\
           (!x. x IN s ==> f x <= g x) ==> integral s f <= integral s g
Proof
    rpt STRIP_TAC
 >> Know ‘integral s f = abs (integral s f)’
 >- (simp [Once EQ_SYM_EQ, ABS_REFL] \\
     MATCH_MP_TAC INTEGRAL_POS >> art [])
 >> Rewr'
 >> MATCH_MP_TAC INTEGRAL_ABS_BOUND_INTEGRAL >> rw []
 >> Suff ‘abs (f x) = f x’ >- (Rewr' >> simp [])
 >> simp [ABS_REFL]
QED

Theorem INTEGRAL_HAS_INTEGRAL :
    !f s y. (f has_integral y) s ==> integral s f = y
Proof
    PROVE_TAC [HAS_INTEGRAL_INTEGRABLE_INTEGRAL]
QED

Theorem has_integral_indicator_imp_lebesgue :
    !E y. (indicator E has_integral y) UNIV ==> lmeasure E = Normal y
Proof
    rw [lebesgue_def]
 >> Know ‘indicator E integrable_on UNIV’
 >- (simp [integrable_on] \\
     Q.EXISTS_TAC ‘y’ >> art [])
 >> DISCH_TAC
 >> Know ‘!n. (indicator E) integrable_on (line n)’
 >- (rw [line_def] \\
     MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL \\
     Q.EXISTS_TAC ‘UNIV’ >> simp [])
 >> DISCH_TAC
 >> qabbrev_tac ‘f = \k. indicator (E INTER line k)’
 >> Know ‘!k. f k integrable_on UNIV’
 >- (rw [integrable_on, Abbr ‘f’, has_integral_indicator_UNIV] \\
     fs [integrable_on])
 >> DISCH_TAC
 >> Know ‘!k x. f k x <= f (SUC k) x’
 >- (rw [Abbr ‘f’] \\
     MATCH_MP_TAC INDICATOR_MONO \\
     rw [line_def, SUBSET_DEF, IN_INTERVAL] >| (* 2 subgoals *)
     [ Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘-&k’ >> simp [],
       Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘&k’ >> simp [] ])
 >> DISCH_TAC
 >> qabbrev_tac ‘g = indicator E’
 >> Know ‘!x. ((\k. f k x) --> g x) sequentially’
 >- (rw [LIM_SEQUENTIALLY, dist, Abbr ‘f’, Abbr ‘g’] \\
     MP_TAC (Q.SPEC ‘abs x’ SIMP_REAL_ARCH) \\
     rw [ABS_BOUNDS] \\
    ‘x IN line n’ by simp [line] \\
     Q.EXISTS_TAC ‘n’ >> rw [] \\
    ‘line n SUBSET line k’ by PROVE_TAC [LINE_MONO] \\
    ‘x IN line k’ by PROVE_TAC [SUBSET_DEF] \\
     simp [indicator])
 >> DISCH_TAC
 >> Know ‘bounded {integral UNIV (f n) | n | T}’
 >- (simp [bounded_def] \\
     Q.EXISTS_TAC ‘y’ >> rw [] \\
    ‘integral UNIV g = y’ by PROVE_TAC [INTEGRAL_HAS_INTEGRAL] \\
     POP_ASSUM (REWRITE_TAC o wrap o SYM) \\
     MATCH_MP_TAC INTEGRAL_ABS_BOUND_INTEGRAL >> rw [] \\
     Know ‘abs (f n x) = f n x’
     >- (MATCH_MP_TAC ABS_REDUCE \\
         simp [Abbr ‘f’, INDICATOR_POS]) >> Rewr' \\
     simp [Abbr ‘f’, Abbr ‘g’] \\
     MATCH_MP_TAC INDICATOR_MONO >> SET_TAC [])
 >> DISCH_TAC
 (* applying MONOTONE_CONVERGENCE_INCREASING *)
 >> MP_TAC (Q.SPECL [‘f’, ‘g’, ‘UNIV’] MONOTONE_CONVERGENCE_INCREASING)
 >> simp []
 >> Know ‘integral UNIV g = y’
 >- (simp [integral_def] \\
     SELECT_ELIM_TAC \\
     CONJ_TAC >- (Q.EXISTS_TAC ‘y’ >> art []) \\
     METIS_TAC [HAS_INTEGRAL_UNIQUE])
 >> Rewr'
 >> Know ‘!n. integral (line n) g = integral UNIV (f n)’
 >- (rw [Once EQ_SYM_EQ, Abbr ‘g’, Abbr ‘f’] \\
     simp [integral_indicator_UNIV])
 >> Rewr'
 >> DISCH_TAC
 >> qabbrev_tac ‘s = {integral UNIV (f n) | n | T}’
 >> Know ‘{Normal (integral UNIV (f n)) | n | T} = IMAGE Normal s’
 >- (rw [Once EXTENSION, Abbr ‘s’] \\
     METIS_TAC [])
 >> Rewr'
 (* applying sup_image_normal *)
 >> Know ‘sup (IMAGE Normal s) = Normal (sup s)’
 >- (MATCH_MP_TAC sup_image_normal \\
     CONJ_TAC >- rw [Abbr ‘s’, Once EXTENSION, NOT_IN_EMPTY] \\
     simp [Abbr ‘s’])
 >> Rewr'
 >> simp [Abbr ‘s’]
 (* applying mono_increasing_converges_to_sup *)
 >> qabbrev_tac ‘h = \n. integral UNIV (f n)’
 >> ‘{integral UNIV (f n) | n | T} = IMAGE h UNIV’
      by rw [Once EXTENSION, Abbr ‘h’]
 >> POP_ORW
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
 >> MATCH_MP_TAC mono_increasing_converges_to_sup
 >> simp [GSYM LIM_SEQUENTIALLY_SEQ]
 >> simp [mono_increasing_def, Abbr ‘h’]
 >> qx_genl_tac [‘i’, ‘j’] >> DISCH_TAC
 >> MATCH_MP_TAC INTEGRAL_MONO_LEMMA >> simp []
 >> ‘!n x. 0 <= f n x’ by rw [Abbr ‘f’, INDICATOR_POS]
 >> simp []
 >> rw [Abbr ‘f’]
 >> MATCH_MP_TAC INDICATOR_MONO
 >> Suff ‘line i SUBSET line j’ >- SET_TAC []
 >> MATCH_MP_TAC LINE_MONO >> art []
QED

(* Another form of has_integral_indicator_imp_lebesgue *)
Theorem integrable_indicator_imp_lmeasure :
    !E y. E IN integrable_sets UNIV ==>
          lmeasure E = Normal (integral UNIV (indicator E))
Proof
    rw [integrable_on, integrable_sets_def]
 >> ‘integral UNIV (indicator E) = y’ by PROVE_TAC [INTEGRAL_HAS_INTEGRAL]
 >> POP_ORW
 >> MATCH_MP_TAC has_integral_indicator_imp_lebesgue >> art []
QED

(* Yet another form *)
Theorem integral_indicator_lmeasure :
    !E y. E IN integrable_sets UNIV ==>
          lmeasure E <> PosInf /\
          integral UNIV (indicator E) = real (lmeasure E)
Proof
    rw [integrable_indicator_imp_lmeasure]
QED

Theorem has_integral_indicator_imp_lebesgue' :
    !E y s. E IN measurable_sets lebesgue /\ E SUBSET s ==>
           (indicator E has_integral y) s ==> lmeasure E = Normal y
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC has_integral_indicator_imp_lebesgue
 >> qabbrev_tac ‘t = UNIV DIFF s’
 >> ‘UNIV = s UNION t’ by ASM_SET_TAC [] >> POP_ORW
 >> ‘s INTER t = {}’ by ASM_SET_TAC []
 >> ONCE_REWRITE_TAC [GSYM REAL_ADD_RID]
 >> MATCH_MP_TAC HAS_INTEGRAL_UNION >> art [NEGLIGIBLE_EMPTY]
 >> MATCH_MP_TAC HAS_INTEGRAL_IS_0
 >> rw [indicator, Abbr ‘t’]
 >> PROVE_TAC [SUBSET_DEF]
QED

(* NOTE: HAS_INTEGRAL_BIGUNION, HAS_INTEGRAL_INTEGRABLE_INTEGRAL, INTEGRABLE_SUM *)
Theorem INTEGRAL_BIGUNION :
    !f t. FINITE t /\ (!s. s IN t ==> f integrable_on s) /\
         (!s s'. s IN t /\ s' IN t /\ s <> s' ==> negligible (s INTER s')) ==>
          f integrable_on (BIGUNION t) /\
          integral (BIGUNION t) f = sum t (\s. integral s f)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘!s. s IN t ==> f integrable_on s’
      (STRIP_ASSUME_TAC o REWRITE_RULE [integrable_on])
 >> fs [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
 >> rename1 ‘!s. s IN t ==> (f has_integral i s) s’
 >> MP_TAC (Q.SPECL [‘f’, ‘i’, ‘t’] HAS_INTEGRAL_BIGUNION)
 >> simp [] >> DISCH_TAC
 >> Know ‘sum t (\s. integral s f) = sum t i’
 >- (MATCH_MP_TAC SUM_EQ' \\
     Q.X_GEN_TAC ‘s’ >> rw [] \\
     METIS_TAC [HAS_INTEGRAL_INTEGRABLE_INTEGRAL])
 >> Rewr'
 >> METIS_TAC [HAS_INTEGRAL_INTEGRABLE_INTEGRAL]
QED

(* NOTE: This is the "unit" version of [approximation_thm] over [c,c + 1] *)
Theorem approximation_lemma1[local] :
    !E c e. E IN measurable_sets lebesgue /\ E <> {} /\ 0 < e /\
            E SUBSET interval [c,c + 1] ==>
            ?J. (!i. J i SUBSET interval [c,c + 1]) /\
                (!i. closed_interval (J i)) /\
                (!i j. i <> j ==> nonoverlapping (J i) (J j)) /\
                 E SUBSET BIGUNION (IMAGE J UNIV) /\
                 lmeasure E <= suminf (lmeasure o J) /\
                 suminf (lmeasure o J) <= lmeasure E + Normal e
Proof
    rpt STRIP_TAC
 >> Know ‘!a b. indicator E integrable_on interval [a,b]’
 >- (rpt GEN_TAC \\
     fs [lebesgue_def] \\
     MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL \\
     STRIP_ASSUME_TAC (Q.SPECL [‘a’, ‘b’] LINE_EXISTS) \\
     Q.EXISTS_TAC ‘line n’ >> art [])
 >> DISCH_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [integrable_on] o
               Q.SPECL [‘c’, ‘c + 1’]) (* this asserts ‘y’ *)
 >> ‘lmeasure E = Normal y’
      by PROVE_TAC [has_integral_indicator_imp_lebesgue']
 >> qabbrev_tac ‘s = interval [c,c + 1]’
 >> ‘(indicator E) integrable_on s /\ integral s (indicator E) = y’
      by PROVE_TAC [HAS_INTEGRAL_INTEGRABLE_INTEGRAL]
 >> Q.PAT_X_ASSUM ‘(indicator E has_integral y) s’
      (MP_TAC o SRULE [has_integral_def])
 >> Know ‘?a b. s = interval [a,b]’
 >- (simp [Abbr ‘s’] \\
     qexistsl_tac [‘c’, ‘c + 1’] >> REFL_TAC)
 >> Rewr
 >> rw [has_integral_compact_interval]
 >> POP_ASSUM (MP_TAC o Q.SPEC ‘e’)
 >> RW_TAC real_ss [] (* this asserts ‘d’ (the gauge). *)
 >> qabbrev_tac ‘f = indicator E’
 >> qabbrev_tac ‘y = integral s f’
 (* applying dyadic_covering_lemma' *)
 >> MP_TAC (Q.SPECL [‘d’, ‘E’, ‘c’] dyadic_covering_lemma_unit')
 >> RW_TAC std_ss [FORALL_AND_THM, GSYM CONJ_ASSOC]
 (* NOTE: J may covers entire univ(:real), including those outside of [-B,B]. *)
 >> Q.EXISTS_TAC ‘J’ >> simp []
 >> ‘!n. J n IN measurable_sets lebesgue’
      by PROVE_TAC [closed_interval_imp_lebesgue]
 (* The first subgoal involves only a measure-theoretic proof *)
 >> CONJ_TAC
 >- (Q.PAT_X_ASSUM ‘lmeasure E = Normal y’ (REWRITE_TAC o wrap o SYM) \\
     Know ‘BIGUNION (IMAGE J UNIV) IN measurable_sets lebesgue’
     >- (MATCH_MP_TAC MEASURE_SPACE_BIGUNION \\
         simp [measure_space_lebesgue]) >> DISCH_TAC \\
     qabbrev_tac ‘A = interior o J’ \\
     Know ‘lmeasure o J = lmeasure o A’
     >- (simp [FUN_EQ_THM, Abbr ‘A’] \\
         Q.X_GEN_TAC ‘i’ \\
         fs [closed_interval_def, GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM,
             INTERIOR_INTERVAL] \\
         rename1 ‘!i. J i = interval [a i,b i]’ \\
         Cases_on ‘a i <= b i’
         >- simp [lebesgue_open_interval, lebesgue_closed_interval] \\
        ‘b i < a i /\ b i <= a i’ by PROVE_TAC [REAL_NOT_LE, REAL_LT_IMP_LE] \\
         simp [iffLR (cj 1 INTERVAL_EQ_EMPTY),
               iffLR (cj 2 INTERVAL_EQ_EMPTY)]) >> Rewr' \\
     Know ‘!n. A n IN measurable_sets lebesgue’
     >- (rw [Abbr ‘A’] \\
         fs [closed_interval_def, GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM,
             INTERIOR_INTERVAL] \\
         rename1 ‘!i. J i = interval [a i,b i]’ \\
         Suff ‘interval (a n,b n) IN measurable_sets lborel’
         >- PROVE_TAC [SUBSET_DEF, lborel_subset_lebesgue] \\
         simp [sets_lborel, borel_measurable_sets, OPEN_interval]) >> DISCH_TAC \\
     Know ‘BIGUNION (IMAGE A UNIV) IN measurable_sets lebesgue’
     >- (MATCH_MP_TAC MEASURE_SPACE_BIGUNION \\
         simp [measure_space_lebesgue]) >> DISCH_TAC \\
  (* applying COUNTABLY_ADDITIVE *)
     Know ‘suminf (lmeasure o A) = lmeasure (BIGUNION (IMAGE A UNIV))’
     >- (MATCH_MP_TAC COUNTABLY_ADDITIVE \\
         simp [countably_additive_lebesgue, IN_FUNSET] \\
         rpt STRIP_TAC \\
         Q.PAT_X_ASSUM ‘!i j. i <> j ==> nonoverlapping (J i) (J j)’
           (MP_TAC o Q.SPECL [‘i’, ‘j’]) \\
         simp [nonoverlapping_def, Abbr ‘A’]) >> Rewr' \\
     Suff ‘lmeasure (BIGUNION (IMAGE A UNIV)) =
           lmeasure (BIGUNION (IMAGE J UNIV))’
     >- (Rewr' \\
         MATCH_MP_TAC MEASURE_INCREASING >> simp [measure_space_lebesgue]) \\
     qabbrev_tac ‘C = frontier o J’ \\
     Know ‘!n. C n IN measurable_sets lebesgue’
     >- (Q.X_GEN_TAC ‘n’ \\
         Suff ‘C n IN measurable_sets lborel’
         >- PROVE_TAC [SUBSET_DEF, lborel_subset_lebesgue] \\
         SIMP_TAC std_ss [Abbr ‘C’, sets_lborel] \\
         fs [closed_interval_def, GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] \\
         rename1 ‘!i. J i = interval [a i,b i]’ \\
         simp [FRONTIER_CLOSED_INTERVAL] \\
         MATCH_MP_TAC SIGMA_ALGEBRA_DIFF \\
         simp [sigma_algebra_borel, borel_measurable_sets,
               OPEN_interval, CLOSED_interval]) >> DISCH_TAC \\
     Know ‘BIGUNION (IMAGE C UNIV) IN measurable_sets lebesgue’
     >- (MATCH_MP_TAC MEASURE_SPACE_BIGUNION \\
         simp [measure_space_lebesgue]) >> DISCH_TAC \\
     Know ‘!n. DISJOINT (A n) (C n)’
     >- (rw [Abbr ‘A’, Abbr ‘C’] \\
         simp [GSYM SET_DIFF_FRONTIER, DISJOINT_ALT]) >> DISCH_TAC \\
     Know ‘!n. J n = A n UNION C n’
     >- (rw [Abbr ‘A’, Abbr ‘C’, frontier] \\
        ‘closed (J n)’ by PROVE_TAC [closed_interval_closed] \\
         simp [CLOSURE_CLOSED] \\
         Suff ‘interior (J n) SUBSET J n’ >- SET_TAC [] \\
         REWRITE_TAC [INTERIOR_SUBSET]) >> DISCH_TAC \\
  (* NOTE: BIGUNION (IMAGE A UNIV) and BIGUNION (IMAGE C UNIV) are not
     disjoint in general: some C in form of [x,x] may stand in the middle
     of another (A n). But these singleton sets do not contribute measures.
   *)
     Know ‘BIGUNION (IMAGE J UNIV) =
           BIGUNION (IMAGE A UNIV) UNION BIGUNION (IMAGE C UNIV)’
     >- (REWRITE_TAC [BIGUNION_IMAGE_UNION] \\
         POP_ASSUM (fn th => simp [GSYM th, ETA_THM])) >> Rewr' \\
  (* applying MEASURE_ADD_ABSORB *)
     SYM_TAC >> MATCH_MP_TAC MEASURE_ADD_ABSORB \\
     simp [measure_space_lebesgue] \\
     reverse (rw [GSYM le_antisym])
     >- (MATCH_MP_TAC MEASURE_POSITIVE >> simp [measure_space_lebesgue]) \\
     Q_TAC (TRANS_TAC le_trans) ‘suminf (lmeasure o C)’ \\
     CONJ_TAC
     >- (MATCH_MP_TAC MEASURE_COUNTABLY_SUBADDITIVE \\
         simp [measure_space_lebesgue, IN_FUNSET]) \\
     Suff ‘suminf (lmeasure o C) = 0’ >- simp [] \\
     MATCH_MP_TAC ext_suminf_zero \\
     NTAC 4 (POP_ASSUM K_TAC) (* C-assumptions *) \\
     rw [o_DEF, Abbr ‘C’] \\
     fs [closed_interval_def, GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] \\
     rename1 ‘!i. J i = interval [a i,b i]’ \\
     simp [FRONTIER_CLOSED_INTERVAL] \\
     Know ‘interval [(a n,b n)] DIFF interval (a n,b n) = {a n} UNION {b n}’
     >- (rw [Once EXTENSION, IN_INTERVAL, REAL_NOT_LT] \\
         Know ‘a n <= b n’
         >- (CCONTR_TAC >> fs [REAL_NOT_LE] \\
             Q.PAT_X_ASSUM ‘!i. t i IN E /\ t i IN J i’ (MP_TAC o Q.SPEC ‘n’) \\
             simp [iffLR (cj 1 INTERVAL_EQ_EMPTY)]) \\
         REAL_ARITH_TAC) >> Rewr' \\
     qmatch_abbrev_tac ‘lmeasure ({x1} UNION {x2}) = 0’ \\
     Cases_on ‘x1 = x2’
     >- (POP_ORW \\
        ‘{x2} UNION {x2} = {x2}’ by SET_TAC [] >> POP_ORW \\
         simp [lebesgue_sing]) \\
     Suff ‘lmeasure ({x1} UNION {x2}) = lmeasure ({x1}) + lmeasure ({x2})’
     >- (Rewr' >> simp [lebesgue_sing]) \\
     MATCH_MP_TAC MEASURE_ADDITIVE >> simp [measure_space_lebesgue] \\
     Suff ‘{x1} IN measurable_sets lborel /\
           {x2} IN measurable_sets lborel’
     >- PROVE_TAC [SUBSET_DEF, lborel_subset_lebesgue] \\
     simp [sets_lborel, borel_measurable_sets])
 (* applying ext_suminf_def *)
 >> qmatch_abbrev_tac ‘suminf g <= _’
 >> Know ‘suminf g = sup (IMAGE (\n. SIGMA g (count n)) UNIV)’
 >- (MATCH_MP_TAC ext_suminf_def \\
     rw [Abbr ‘g’] \\
     MATCH_MP_TAC MEASURE_POSITIVE >> simp [measure_space_lebesgue])
 >> Rewr'
 (* applying sup_le', fixing ‘n’ *)
 >> rw [sup_le', Abbr ‘g’]
 (* applying HENSTOCK_LEMMA_PART1 (Saks-Henstock Lemma 5.3 [2, p.76]) *)
 >> MP_TAC (Q.SPECL [‘f’, ‘c’, ‘c + 1’, ‘d’, ‘e’] HENSTOCK_LEMMA_PART1)
 >> RW_TAC real_ss [] (* all antecedents are eliminated *)
 (* applying lebesgue_closed_interval_content, eliminating “lmeasure” *)
 >> Know ‘lmeasure o J = Normal o content o J’
 >- (rw [o_DEF, FUN_EQ_THM] \\
     fs [closed_interval_def, GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] \\
     rename1 ‘!i. J i = interval [a i,b i]’ \\
     REWRITE_TAC [lebesgue_closed_interval_content])
 >> Rewr'
 (* next, eliminating extreals! *)
 >> Know ‘SIGMA (Normal o content o J) (count n) =
          Normal (SIGMA (content o J) (count n))’
 >- (simp [o_DEF] \\
     HO_MATCH_MP_TAC EXTREAL_SUM_IMAGE_NORMAL >> simp [])
 >> Rewr'
 >> simp [extreal_add_eq]
 (* rewrite SIGMA to sum (iterateTheory) *)
 >> Know ‘SIGMA (content o J) (count n) = sum (count n) (content o J)’
 >- (MATCH_MP_TAC REAL_SUM_IMAGE_sum >> simp [])
 >> Rewr'
 (* stage work *)
 >> qabbrev_tac ‘p = IMAGE (\i. (t i,J i)) (count n)’
 >> Q.PAT_X_ASSUM ‘!p. p tagged_partial_division_of s /\ d FINE p ==> _’
      (MP_TAC o Q.SPEC ‘p’)
 >> impl_tac
 >- (rw [Abbr ‘p’, tagged_partial_division_of, FINE] >| (* 5 subgoals *)
     [ (* goal 1 (of 5) *)
       FULL_SIMP_TAC std_ss [IN_INTER],
       (* goal 2 (of 5) *)
       ASM_REWRITE_TAC [],
       (* goal 3 (of 5) *)
       fs [closed_interval_def],
       (* goal 4 (of 5) *)
       rename1 ‘j < n’ \\
       Cases_on ‘i = j’ >- METIS_TAC [] \\
       Q.PAT_X_ASSUM ‘!i j. i <> j ==> _’ drule \\
       rw [nonoverlapping_def, DISJOINT_DEF],
       (* goal 5 (of 5) *)
       ASM_REWRITE_TAC [] ])
 (* applying real_sigmaTheory.SUM_SUB' *)
 >> Know ‘(\(x,k). content k * f x - integral k f) =
          (\z. content (SND z) * f (FST z) - integral (SND z) f)’
 >- (rw [FUN_EQ_THM] \\
     PairCases_on ‘z’ >> simp [])
 >> Rewr'
 >> Know ‘sum p (\z. content (SND z) * f (FST z) - integral (SND z) f) =
          sum p (\z. content (SND z) * f (FST z)) -
          sum p (\z. integral (SND z) f)’
 >- (HO_MATCH_MP_TAC SUM_SUB' >> simp [Abbr ‘p’])
 >> Rewr'
 >> Know ‘(\z. content (SND z) * f (FST z)) = (\(x,k). content k * f x)’
 >- (rw [FUN_EQ_THM] \\
     PairCases_on ‘z’ >> simp [])
 >> Rewr'
 >> Know ‘(\(z :real # real set). integral (SND z) f) =
          (\((x :real),k). integral k f)’
 >- (rw [FUN_EQ_THM] \\
     PairCases_on ‘z’ >> simp [])
 >> Rewr'
 (* applying SUM_IMAGE *)
 >> qabbrev_tac ‘h = (\i. (t i,J i))’
 >> qmatch_abbrev_tac ‘abs (sum p g1 - sum p g2) <= e ==> _’
 >> simp [Abbr ‘p’]
 (* ‘N’ is the trivial set of indexes with zero contents *)
 >> qabbrev_tac ‘N = {i | i < n /\ ?x. J i = interval [x,x]}’
 >> qabbrev_tac ‘M = count n DIFF N’
 >> Know ‘!i j. i IN M /\ j IN M /\ J i = J j ==> i = j’
 >- (rw [Abbr ‘N’, Abbr ‘M’] \\
     CCONTR_TAC \\
     Q.PAT_X_ASSUM ‘!i j. i <> j ==> nonoverlapping (J i) (J j)’ drule \\
     fs [closed_interval_def, GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] \\
     rename1 ‘!i. J i = interval [a i,b i]’ \\
     rw [nonoverlapping_def, INTERIOR_INTERVAL] \\
     simp [INTERVAL_NE_EMPTY] \\
     CCONTR_TAC >> fs [REAL_NOT_LT] \\
    ‘b j = a j \/ b j < (a j) :real’ by METIS_TAC [REAL_LE_LT]
     >- METIS_TAC [] \\
     Suff ‘J i = {}’ >- METIS_TAC [NOT_IN_EMPTY] \\
     simp [GSYM INTERVAL_EQ_EMPTY])
 >> DISCH_TAC
 >> ‘N SUBSET count n’ by rw [SUBSET_DEF, Abbr ‘N’]
 >> Know ‘!i. i IN N ==> content (J i) = 0’
 >- (rw [Abbr ‘N’] >> fs [CONTENT_CLOSED_INTERVAL])
 >> DISCH_TAC
 >> Know ‘!i. i IN N ==> integral (J i) f = 0’
 >- (rw [Abbr ‘N’] >> simp [INTEGRAL_REFL])
 >> DISCH_TAC
 >> ‘DISJOINT N M /\ count n = N UNION M’ by ASM_SET_TAC [] >> POP_ORW
 >> Know ‘FINITE N’
 >- (irule SUBSET_FINITE >> Q.EXISTS_TAC ‘count n’ >> simp [FINITE_COUNT])
 >> DISCH_TAC
 >> Know ‘FINITE M’
 >- (irule SUBSET_FINITE >> Q.EXISTS_TAC ‘count n’ >> simp [FINITE_COUNT] \\
     rw [SUBSET_DEF, Abbr ‘M’])
 >> DISCH_TAC
 >> REWRITE_TAC [IMAGE_UNION]
 >> Know ‘DISJOINT (IMAGE h N) (IMAGE h M)’
 >- (rw [DISJOINT_ALT, Abbr ‘M’, Abbr ‘h’, Abbr ‘N’] \\
     rename1 ‘t j = t i’ >> simp [] \\
     STRONG_DISJ_TAC >> art [] \\
     rename1 ‘J i = interval [x,x]’ \\
     Q.EXISTS_TAC ‘x’ >> REFL_TAC)
 >> DISCH_TAC
 >> Know ‘sum (IMAGE h N UNION IMAGE h M) g1 =
          sum (IMAGE h N) g1 + sum (IMAGE h M) g1’
 >- (MATCH_MP_TAC SUM_UNION >> simp [IMAGE_FINITE])
 >> Rewr'
 >> Know ‘sum (IMAGE h N UNION IMAGE h M) g2 =
          sum (IMAGE h N) g2 + sum (IMAGE h M) g2’
 >- (MATCH_MP_TAC SUM_UNION >> simp [IMAGE_FINITE])
 >> Rewr'
 >> Know ‘sum (N UNION M) (content o J) =
          sum N (content o J) + sum M (content o J)’
 >- (MATCH_MP_TAC SUM_UNION >> simp [])
 >> Rewr'
 (* applying SUM_EQ_0' *)
 >> Know ‘sum (IMAGE h N) g1 = 0’
 >- (MATCH_MP_TAC SUM_EQ_0' \\
     rw [Abbr ‘h’, Abbr ‘g1’] >> simp [])
 >> DISCH_THEN (simp o wrap)
 >> Know ‘sum (IMAGE h N) g2 = 0’
 >- (MATCH_MP_TAC SUM_EQ_0' \\
     rw [Abbr ‘h’, Abbr ‘g2’] >> simp [])
 >> DISCH_THEN (simp o wrap)
 >> Know ‘sum N (content o J) = 0’
 >- (MATCH_MP_TAC SUM_EQ_0' >> rw [o_DEF])
 >> DISCH_THEN (simp o wrap)
 >> Know ‘sum (IMAGE h M) g1 = sum M (g1 o h)’
 >- (MATCH_MP_TAC SUM_IMAGE >> rw [Abbr ‘h’])
 >> Rewr'
 >> Know ‘sum (IMAGE h M) g2 = sum M (g2 o h)’
 >- (MATCH_MP_TAC SUM_IMAGE >> rw [Abbr ‘h’])
 >> Rewr'
 >> simp [o_DEF, Abbr ‘h’, Abbr ‘g1’, Abbr ‘g2’]
 >> Know ‘sum M (\i. f (t i) * content (J i)) =
          sum M (\x. content (J x))’
 >- (MATCH_MP_TAC SUM_EQ' \\
     Q.X_GEN_TAC ‘j’ >> rw [Abbr ‘f’] \\
     DISJ2_TAC \\
     Q.PAT_X_ASSUM ‘!i. t i IN E INTER J i’ (MP_TAC o Q.SPEC ‘j’) \\
     rw [indicator])
 >> Rewr'
 (* eliminating “abs” by ABS_REFL, etc. *)
 >> Know ‘abs (sum M (\x. content (J x)) - sum M (\i. integral (J i) f)) =
               sum M (\x. content (J x)) - sum M (\i. integral (J i) f)’
 >- (simp [ABS_REFL, REAL_SUB_LE] \\
     MATCH_MP_TAC SUM_LE' >> art [] \\
     Q.X_GEN_TAC ‘j’ >> rw [] \\
     Know ‘content (J j) = integral (J j) (\x. 1)’
     >- (fs [closed_interval_def, GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] \\
         rename1 ‘!i. J i = interval [a i,b i]’ \\
         simp [INTEGRAL_CONST]) >> Rewr' \\
     MATCH_MP_TAC INTEGRAL_LE_AE \\
     Q.EXISTS_TAC ‘{}’ \\
     simp [Abbr ‘f’, NEGLIGIBLE_EMPTY, DROP_INDICATOR_LE_1] \\
     fs [closed_interval_def, GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] \\
     rename1 ‘!i. J i = interval [a i,b i]’ \\
     simp [INTEGRABLE_CONST] \\
     MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL \\
     Q.EXISTS_TAC ‘s’ >> art [] \\
     Q.PAT_X_ASSUM ‘!i. J i = interval [a i,b i]’ (simp o wrap o GSYM))
 >> Rewr'
 >> simp [REAL_ARITH “a - b <= c <=> a <= b + (c :real)”]
 >> DISCH_TAC
 >> Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘sum M (\i. integral (J i) f) + e’
 >> POP_ASSUM (simp o wrap)
 >> qunabbrev_tac ‘y’
 (* applying SUM_IMAGE again *)
 >> ‘(\i. integral (J i) f) = (\s. integral s f) o J’ by rw [FUN_EQ_THM, o_DEF]
 >> POP_ORW
 >> qabbrev_tac ‘g = \(s :real set). integral s f’
 >> Know ‘sum M (g o J) = sum (IMAGE J M) g’
 >- (SYM_TAC >> MATCH_MP_TAC SUM_IMAGE >> art [])
 >> Rewr'
 (* applying INTEGRAL_BIGUNION *)
 >> MP_TAC (Q.SPECL [‘f’, ‘IMAGE J (M :num set)’] INTEGRAL_BIGUNION)
 >> ASM_SIMP_TAC std_ss [FINITE_IMAGE]
 >> impl_tac
 >- (RW_TAC std_ss [IN_IMAGE] (* 2 subgoals, first one is easy *)
     >- (rename1 ‘j IN M’ \\
         fs [closed_interval_def, GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] \\
         rename1 ‘!i. J i = interval [a i,b i]’ \\
         MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL \\
         Q.EXISTS_TAC ‘s’ >> art [] \\
         Q.PAT_X_ASSUM ‘!i. J i = interval [a i,b i]’ (simp o wrap o GSYM)) \\
     rename1 ‘J j <> J k’ \\
  (* applying NEGLIGIBLE_SING or NEGLIGIBLE_EMPTY *)
    ‘j <> k’ by PROVE_TAC [] \\
     Q.PAT_X_ASSUM ‘!i j. i <> j ==> nonoverlapping (J i) (J j)’ drule \\
     fs [closed_interval_def, GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] \\
     rename1 ‘!i. J i = interval [a i,b i]’ \\
     simp [nonoverlapping_def, INTERIOR_INTERVAL] \\
     simp [DISJOINT_DEF, DISJOINT_INTERVAL] \\
     Know ‘interval [a j,b j] <> {} /\
           interval [a k,b k] <> {}’ >- METIS_TAC [NOT_IN_EMPTY] \\
     simp [INTERVAL_NE_EMPTY] >> STRIP_TAC \\
     STRIP_TAC >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
      ‘a j = b j’ by PROVE_TAC [REAL_LE_ANTISYM] \\
       simp [INTERVAL_SING] \\
       qmatch_abbrev_tac ‘negligible ({x} INTER A)’ \\
       Suff ‘{x} INTER A = {} \/ {x} INTER A = {x}’
       >- METIS_TAC [NEGLIGIBLE_SING, NEGLIGIBLE_EMPTY] \\
       SET_TAC [],
       (* goal 2 (of 4) *)
      ‘a k = b k’ by PROVE_TAC [REAL_LE_ANTISYM] \\
       simp [INTERVAL_SING] \\
       qmatch_abbrev_tac ‘negligible (A INTER {x})’ \\
       Suff ‘A INTER {x}  = {} \/ A INTER {x} = {x}’
       >- METIS_TAC [NEGLIGIBLE_SING, NEGLIGIBLE_EMPTY] \\
       SET_TAC [],
       (* goal 3 (of 4): [a j, b j] <= [a k, b k] *)
      ‘b j = a k \/ b j < a k’ by PROVE_TAC [REAL_LE_LT]
       >- (simp [INTER_INTERVAL] \\
          ‘a j <= a k’ by PROVE_TAC [REAL_LE_TRANS] \\
           simp [REAL_MAX_REDUCE, REAL_MIN_REDUCE] \\
           simp [INTERVAL_SING, NEGLIGIBLE_SING]) \\
      ‘a j < a k’ by PROVE_TAC [REAL_LET_TRANS] \\
      ‘b j < b k’ by PROVE_TAC [REAL_LTE_TRANS] \\
       simp [INTER_INTERVAL, REAL_MAX_REDUCE, REAL_MIN_REDUCE] \\
      ‘interval [a k,b j] = {}’ by simp [GSYM INTERVAL_EQ_EMPTY] \\
       simp [NEGLIGIBLE_EMPTY],
       (* goal 4 (of 4): [a k, b k] <= [a j, b j] *)
      ‘b k = a j \/ b k < a j’ by PROVE_TAC [REAL_LE_LT]
       >- (simp [INTER_INTERVAL] \\
          ‘a k <= a j’ by PROVE_TAC [REAL_LE_TRANS] \\
           simp [REAL_MAX_REDUCE, REAL_MIN_REDUCE] \\
           simp [INTERVAL_SING, NEGLIGIBLE_SING]) \\
      ‘a k < a j’ by PROVE_TAC [REAL_LET_TRANS] \\
      ‘b k < b j’ by PROVE_TAC [REAL_LTE_TRANS] \\
       simp [INTER_INTERVAL, REAL_MAX_REDUCE, REAL_MIN_REDUCE] \\
      ‘interval [a j,b k] = {}’ by simp [GSYM INTERVAL_EQ_EMPTY] \\
       simp [NEGLIGIBLE_EMPTY] ])
 >> STRIP_TAC
 >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
 >> simp [Abbr ‘g’]
 >> MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE
 >> simp [Abbr ‘f’, INDICATOR_POS]
 >> rw [BIGUNION_SUBSET] >> art []
QED

(* NOTE: removed ‘E <> {}’ (E = {} is a trivial case) for easier applications *)
Theorem approximation_lemma1'[local] :
    !E c e. E IN measurable_sets lebesgue /\ 0 < e /\
            E SUBSET interval [c,c + 1] ==>
            ?J. (!i. J i SUBSET interval [(c,c + 1)]) /\
                (!i. closed_interval (J i)) /\
                (!i j. i <> j ==> nonoverlapping (J i) (J j)) /\
                 E SUBSET BIGUNION (IMAGE J UNIV) /\
                 lmeasure E <= suminf (lmeasure o J) /\
                 suminf (lmeasure o J) <= lmeasure E + Normal e
Proof
    rpt STRIP_TAC
 >> reverse (Cases_on ‘E = {}’)
 >- (MATCH_MP_TAC approximation_lemma1 >> art [])
 >> POP_ASSUM (fn th => fs [th, lebesgue_empty])
 >> qabbrev_tac ‘d = min 1 e’
 >> ‘0 < d’ by simp [REAL_LT_MIN, Abbr ‘d’]
 >> qabbrev_tac ‘J = \(i :num). if i = 0 then interval [c,c + d]
                                         else interval [c,c]’
 >> ‘J 0 = interval [c,c + d]’ by simp [Abbr ‘J’]
 >> ‘!i. i <> 0 ==> J i = interval [c,c]’ by rw [Abbr ‘J’]
 >> Q.EXISTS_TAC ‘J’
 >> CONJ_TAC
 >- (reverse (rw [Abbr ‘J’])
     >- (rw [INTERVAL_SING, SUBSET_DEF] \\
         simp [IN_INTERVAL]) \\
     simp [closed_interval_subset_eq] \\
     simp [Abbr ‘d’, REAL_MIN_LE])
 >> CONJ_TAC
 >- (rw [closed_interval_def] \\
     Cases_on ‘i = 0’ >> simp [] >| (* 2 subgoals *)
     [ qexistsl_tac [‘c’, ‘c + d’] >> REFL_TAC,
       qexistsl_tac [‘c’, ‘c’] >> REFL_TAC ])
 >> CONJ_TAC
 >- (rw [nonoverlapping_def] \\
     Cases_on ‘i = 0’ >> simp [INTERIOR_INTERVAL] >> simp [INTERVAL_SING])
 (* applying ext_suminf_sum *)
 >> ‘!i. i <> 0 ==> lmeasure (J i) = 0’
      by rw [lebesgue_closed_interval, REAL_LT_IMP_LE, normal_0]
 >> qabbrev_tac ‘f = lmeasure o J’
 >> Know ‘suminf f = SIGMA f (count 1)’
 >- (MATCH_MP_TAC ext_suminf_sum \\
     reverse CONJ_TAC >- rw [Abbr ‘f’] \\
     RW_TAC std_ss [Abbr ‘f’, o_DEF] \\
     MATCH_MP_TAC MEASURE_POSITIVE >> simp [measure_space_lebesgue] \\
     Suff ‘J n IN measurable_sets lborel’
     >- METIS_TAC [SUBSET_DEF, lborel_subset_lebesgue] \\
     REWRITE_TAC [sets_lborel] \\
     Cases_on ‘n = 0’ >> simp [CLOSED_interval, borel_measurable_sets])
 >> Rewr'
 >> simp [Abbr ‘f’, EXTREAL_SUM_IMAGE_COUNT_ONE, REAL_LT_IMP_LE,
          lebesgue_closed_interval, REAL_ADD_SUB]
 >> simp [Abbr ‘d’, REAL_MIN_LE]
QED

Theorem lebesgue_additive :
    !s t. s IN measurable_sets lebesgue /\
          t IN measurable_sets lebesgue /\ negligible (s INTER t) ==>
          lmeasure (s UNION t) = lmeasure s + lmeasure t
Proof
    rpt STRIP_TAC
 >> MP_TAC (ISPECL [“lebesgue”, “s :real set”, “t :real set”]
                   MEASURE_SPACE_STRONG_ADDITIVE)
 >> simp [measure_space_lebesgue, lebesgue_of_negligible]
QED

Theorem NEGLIGIBLE_COUNTABLE_BIGUNION' :
    !s. (!n. negligible (s n)) ==> negligible (BIGUNION (IMAGE s univ(:num)))
Proof
    rpt STRIP_TAC
 >> ‘IMAGE s UNIV = {s n | n IN UNIV}’ by rw [Once EXTENSION]
 >> POP_ORW
 >> MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_BIGUNION >> art []
QED

Theorem lebesgue_countably_additive :
    !f s. f IN (univ(:num) -> measurable_sets lebesgue) /\
         (!i j. i <> j ==> negligible (f i INTER f j)) /\
          s = BIGUNION (IMAGE f univ(:num)) ==>
          suminf (lmeasure o f) = lmeasure s
Proof
    RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> qmatch_abbrev_tac ‘_ = lmeasure s’
 (* NOTE: Now that each two (f n) are not disjoint, but can we modify them
    to make them disjoint while still keeping their existing measure?
  *)
 >> qabbrev_tac
   ‘g = \i. BIGUNION (IMAGE (\j. if j = i then {} else f i INTER f j) UNIV)’
 >> Know ‘!n. negligible (g n)’
 >- (rw [Abbr ‘g’] \\
     MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_BIGUNION' \\
     Q.X_GEN_TAC ‘i’ >> simp [] \\
     Cases_on ‘n = i’ >> simp [NEGLIGIBLE_EMPTY])
 >> DISCH_TAC
 >> ‘!n. g n IN measurable_sets lebesgue’ by PROVE_TAC [negligible_in_lebesgue]
 >> qabbrev_tac ‘h = \i. f i DIFF g i’
 >> Know ‘!n. h n IN measurable_sets lebesgue’
 >- (rw [Abbr ‘h’] \\
     MATCH_MP_TAC MEASURE_SPACE_DIFF \\
     simp [measure_space_lebesgue])
 >> DISCH_TAC
 >> Know ‘!n. lmeasure (h n) = lmeasure (f n)’
 >- (rw [Abbr ‘h’] \\
     MATCH_MP_TAC MEASURE_SUB_ABSORB \\
     simp [measure_space_lebesgue, lebesgue_of_negligible])
 >> DISCH_TAC
 >> ‘lmeasure o f = lmeasure o h’ by rw [FUN_EQ_THM, o_DEF] >> POP_ORW
 >> Know ‘!i j. i <> j ==> DISJOINT (h i) (h j)’
 >- (rw [DISJOINT_ALT, Abbr ‘h’] \\
     DISJ1_TAC \\
     POP_ASSUM MP_TAC \\
     rw [Abbr ‘g’, IN_BIGUNION_IMAGE] \\
     POP_ASSUM (MP_TAC o Q.SPEC ‘j’) >> simp [])
 >> DISCH_TAC
 (* applying MEASURE_COUNTABLY_ADDITIVE *)
 >> qabbrev_tac ‘t = BIGUNION (IMAGE h UNIV)’
 >> Know ‘t IN measurable_sets lebesgue’
 >- (qunabbrev_tac ‘t’ \\
     MATCH_MP_TAC MEASURE_SPACE_BIGUNION \\
     simp [measure_space_lebesgue])
 >> DISCH_TAC
 >> Know ‘suminf (lmeasure o h) = lmeasure t’
 >- (MATCH_MP_TAC MEASURE_COUNTABLY_ADDITIVE \\
     simp [IN_FUNSET, measure_space_lebesgue])
 >> Rewr'
 >> qabbrev_tac ‘N = BIGUNION (IMAGE g UNIV)’
 >> Know ‘N IN measurable_sets lebesgue’
 >- (qunabbrev_tac ‘N’ \\
     MATCH_MP_TAC MEASURE_SPACE_BIGUNION \\
     simp [measure_space_lebesgue])
 >> DISCH_TAC
 >> ‘negligible N’ by PROVE_TAC [NEGLIGIBLE_COUNTABLE_BIGUNION']
 >> Know ‘s = t UNION N’
 >- (rw [Once EXTENSION, Abbr ‘s’, IN_BIGUNION_IMAGE, Abbr ‘t’, Abbr ‘N’] \\
     EQ_TAC
     >- (DISCH_THEN (Q.X_CHOOSE_THEN ‘i’ STRIP_ASSUME_TAC) \\
         simp [Abbr ‘h’] \\
         Cases_on ‘?j. x IN g j’ >> simp [] \\
         fs [] \\
         Q.EXISTS_TAC ‘i’ >> simp []) \\
     simp [Abbr ‘h’] \\
     STRIP_TAC
     >- (rename1 ‘x IN f i’ \\
         Q.EXISTS_TAC ‘i’ >> simp []) \\
     rename1 ‘x IN g i’ \\
     POP_ASSUM MP_TAC >> rw [Abbr ‘g’, IN_BIGUNION_IMAGE] \\
     Cases_on ‘j = i’ >> fs [] \\
     Q.EXISTS_TAC ‘i’ >> simp [])
 >> Rewr'
 >> SYM_TAC
 >> MATCH_MP_TAC MEASURE_ADD_ABSORB
 >> simp [measure_space_lebesgue, lebesgue_of_negligible]
QED

(* This is an intermediate result also as a proof of concept *)
Theorem approximation_lemma2[local] :
    !E e n. E IN measurable_sets lebesgue /\ 0 < e /\
            E SUBSET interval [-&SUC n,-&n] UNION interval [&n,&SUC n] ==>
            ?J. (!i. closed_interval (J i)) /\
                (!i. J i SUBSET interval [-&SUC n,-&n] UNION
                                interval [&n,&SUC n]) /\
                (!i j. i <> j ==> nonoverlapping (J i) (J j)) /\
                 E SUBSET BIGUNION (IMAGE J UNIV) /\
                 lmeasure E <= suminf (lmeasure o J) /\
                 suminf (lmeasure o J) <= lmeasure E + Normal e
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘A = interval [&n,&SUC n]’
 >> qabbrev_tac ‘B = interval [-&SUC n,-&n]’
 >> Know ‘A IN measurable_sets lebesgue /\ B IN measurable_sets lebesgue’
 >- (Suff ‘A IN measurable_sets lborel /\ B IN measurable_sets lborel’
     >- METIS_TAC [SUBSET_DEF, lborel_subset_lebesgue] \\
     simp [Abbr ‘A’, Abbr ‘B’, CLOSED_interval,
           sets_lborel, borel_measurable_sets])
 >> STRIP_TAC
 (* applying approximation_lemma1 *)
 >> qabbrev_tac ‘E1 = E INTER A’
 >> qabbrev_tac ‘E2 = E INTER B’
 >> ‘E1 SUBSET A /\ E2 SUBSET B’ by simp [Abbr ‘E1’, Abbr ‘E2’]
 >> ‘E1 IN measurable_sets lebesgue /\ E2 IN measurable_sets lebesgue’
      by METIS_TAC [MEASURE_SPACE_INTER, measure_space_lebesgue]
 (* applying approximation_lemma1', twice *)
 >> MP_TAC (Q.SPECL [‘E1’, ‘&n’, ‘e / 2’] approximation_lemma1')
 >> simp [GSYM ADD1]
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘J1’ STRIP_ASSUME_TAC)
 >> MP_TAC (Q.SPECL [‘E2’, ‘-&SUC n’, ‘e / 2’] approximation_lemma1')
 >> Know ‘-&SUC n + 1 = (-&n) :real’
 >- (SIMP_TAC std_ss [ADD1, GSYM REAL_OF_NUM_ADD] \\
     REAL_ARITH_TAC)
 >> Rewr'
 >> simp []
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘J2’ STRIP_ASSUME_TAC)
 >> Know ‘negligible (A INTER B)’
 >- (simp [Abbr ‘A’, Abbr ‘B’, INTER_INTERVAL] \\
     simp [REAL_MAX_REDUCE, REAL_MIN_REDUCE] \\
     Cases_on ‘n = 0’ >- simp [INTERVAL_SING, NEGLIGIBLE_SING] \\
    ‘interval [&n,-&n] = {}’ by simp [GSYM INTERVAL_EQ_EMPTY] \\
     simp [NEGLIGIBLE_EMPTY])
 >> DISCH_TAC
 >> Know ‘negligible (E1 INTER E2)’
 >- (Suff ‘E1 INTER E2 SUBSET (A INTER B)’ >- METIS_TAC [NEGLIGIBLE_SUBSET] \\
     ASM_SET_TAC [])
 >> DISCH_TAC
 >> ‘E = E1 UNION E2’ by ASM_SET_TAC [] >> POP_ORW
 >> Know ‘lmeasure (E1 UNION E2) = lmeasure E1 + lmeasure E2’
 >- (MATCH_MP_TAC lebesgue_additive >> art [])
 >> Rewr'
 >> ‘Normal e = Normal (e / 2) + Normal (e / 2)’
      by simp [extreal_add_eq, REAL_HALF_DOUBLE] >> POP_ORW
 >> Know ‘lmeasure E1 + lmeasure E2 + (Normal (e / 2) + Normal (e / 2)) =
          lmeasure E1 + Normal (e / 2) + (lmeasure E2 + Normal (e / 2))’
 >- (MATCH_MP_TAC add2_assoc \\
     rpt CONJ_TAC >> MATCH_MP_TAC pos_not_neginf >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       MATCH_MP_TAC MEASURE_POSITIVE >> simp [measure_space_lebesgue],
       (* goal 2 (of 4) *)
       MATCH_MP_TAC MEASURE_POSITIVE >> simp [measure_space_lebesgue],
       (* goal 3 (of 4) *)
       simp [extreal_of_num_def, REAL_LT_IMP_LE],
       (* goal 4 (of 4) *)
       simp [extreal_of_num_def, REAL_LT_IMP_LE] ])
 >> Rewr'
 (* NOTE: Now we need to merge two countable sequence into one. The "standard"
    way is to interleave them as ODD and EVEN elements:
    0    , 1    , 2    , 3    , ...
    J1(0), J2(0), J1(1), J2(1), ...
  *)
 >> qabbrev_tac ‘J = \i. if EVEN i then J1 (i DIV 2) else J2 ((i - 1) DIV 2)’
 >> Q.EXISTS_TAC ‘J’
 >> CONJ_TAC >- RW_TAC arith_ss [Abbr ‘J’]
 >> CONJ_TAC
 >- (rw [Abbr ‘J’, SUBSET_DEF] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       rename1 ‘x IN J1 j’ >> DISJ2_TAC \\
       PROVE_TAC [SUBSET_DEF],
       (* goal 2 (of 2) *)
       rename1 ‘x IN J2 j’ >> DISJ1_TAC \\
       PROVE_TAC [SUBSET_DEF] ])
 >> Know ‘nonoverlapping A B’
 >- (simp [Abbr ‘A’, Abbr ‘B’, nonoverlapping_def, INTERIOR_INTERVAL] \\
     simp [DISJOINT_DEF, DISJOINT_INTERVAL])
 >> DISCH_TAC
 >> CONJ_TAC (* nonoverlapping *)
 >- (RW_TAC std_ss [Abbr ‘J’] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       FIRST_X_ASSUM MATCH_MP_TAC >> fs [EVEN_EXISTS],
       (* goal 2 (of 4) *)
       MATCH_MP_TAC nonoverlapping_subset_inclusive \\
       qexistsl_tac [‘A’, ‘B’] >> art [],
       (* goal 3 (of 4) *)
       MATCH_MP_TAC nonoverlapping_subset_inclusive \\
       qexistsl_tac [‘B’, ‘A’] >> simp [Once nonoverlapping_comm],
       (* goal 4 (of 4) *)
       FIRST_X_ASSUM MATCH_MP_TAC >> fs [GSYM ODD_EVEN, ODD_EXISTS] ])
 (* E1 UNION E2 SUBSET _ *)
 >> CONJ_TAC
 >- (RW_TAC std_ss [IN_UNION, SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNIV] >|
     [ (* goal 1 (of 2) *)
       Know ‘x IN BIGUNION (IMAGE J1 UNIV)’ >- PROVE_TAC [SUBSET_DEF] \\
       rw [IN_BIGUNION_IMAGE, Abbr ‘J’] \\
       rename1 ‘x IN J1 (i :num)’ \\
       Q.EXISTS_TAC ‘2 * i’ >> simp [EVEN_DOUBLE],
       (* goal 2 (of 2) *)
       Know ‘x IN BIGUNION (IMAGE J2 UNIV)’ >- PROVE_TAC [SUBSET_DEF] \\
       rw [IN_BIGUNION_IMAGE, Abbr ‘J’] \\
       rename1 ‘x IN J2 (i :num)’ \\
       Q.EXISTS_TAC ‘SUC (2 * i)’ >> simp [EVEN_ODD, ODD_DOUBLE] ])
 (* applying le_add2, twice *)
 >> Suff ‘suminf (lmeasure o J) =
          suminf (lmeasure o J1) + suminf (lmeasure o J2)’
 >- (Rewr' \\
     CONJ_TAC >- (MATCH_MP_TAC le_add2 >> art []) \\
     MATCH_MP_TAC le_add2 >> art [])
 (* preparing for sup_add_mono *)
 >> qmatch_abbrev_tac ‘suminf h = suminf f + suminf g’
 >> Know ‘!i. 0 <= f i’
 >- (rw [Abbr ‘f’, o_DEF] \\
     MATCH_MP_TAC MEASURE_POSITIVE >> simp [measure_space_lebesgue] \\
     Suff ‘J1 i IN measurable_sets lborel’
     >- PROVE_TAC [lborel_subset_lebesgue, SUBSET_DEF] \\
     Q.PAT_X_ASSUM ‘!i. closed_interval (J1 i)’ (MP_TAC o Q.SPEC ‘i’) \\
     rw [closed_interval_def, CLOSED_interval] \\
     simp [borel_measurable_sets, sets_lborel])
 >> DISCH_TAC
 >> Know ‘!i. 0 <= g i’
 >- (rw [Abbr ‘g’, o_DEF] \\
     MATCH_MP_TAC MEASURE_POSITIVE >> simp [measure_space_lebesgue] \\
     Suff ‘J2 i IN measurable_sets lborel’
     >- PROVE_TAC [lborel_subset_lebesgue, SUBSET_DEF] \\
     Q.PAT_X_ASSUM ‘!i. closed_interval (J2 i)’ (MP_TAC o Q.SPEC ‘i’) \\
     rw [closed_interval_def, CLOSED_interval] \\
     simp [borel_measurable_sets, sets_lborel])
 >> DISCH_TAC
 >> Know ‘!i. 0 <= h i’
 >- (rw [Abbr ‘h’, o_DEF, Abbr ‘J’] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       qmatch_abbrev_tac ‘0 <= lmeasure (J1 j)’ \\
       Q.PAT_X_ASSUM ‘!i. 0 <= f i’ (MP_TAC o Q.SPEC ‘j’) \\
       rw [Abbr ‘f’, o_DEF],
       (* goal 2 (of 2) *)
       qmatch_abbrev_tac ‘0 <= lmeasure (J2 j)’ \\
       Q.PAT_X_ASSUM ‘!i. 0 <= g i’ (MP_TAC o Q.SPEC ‘j’) \\
       rw [Abbr ‘g’, o_DEF] ])
 >> DISCH_TAC
 >> simp [ext_suminf_def]
 (* applying sup_add_mono *)
 >> qmatch_abbrev_tac ‘sup (IMAGE h' UNIV) =
                       sup (IMAGE f' UNIV) + sup (IMAGE g' UNIV)’
 >> Suff ‘sup (IMAGE h' UNIV) = sup (IMAGE (\i. f' i + g' i) UNIV)’
 >- (Rewr' >> MATCH_MP_TAC sup_add_mono \\
     Know ‘!i. 0 <= f' i’
     >- (rw [Abbr ‘f'’] \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> rw []) >> DISCH_TAC \\
     Know ‘!i. 0 <= g' i’
     >- (rw [Abbr ‘g'’] \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> rw []) >> DISCH_TAC \\
     simp [Abbr ‘f'’, Abbr ‘g'’] \\
     CONJ_TAC >> Q.X_GEN_TAC ‘i’ >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET >> rw [SUBSET_DEF],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET >> rw [SUBSET_DEF] ])
 (* final goal *)
 >> RW_TAC std_ss [GSYM le_antisym]
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC sup_le_sup_imp' \\
      Q.X_GEN_TAC ‘z’ >> simp [] \\
      DISCH_THEN (Q.X_CHOOSE_THEN ‘N’ STRIP_ASSUME_TAC) >> POP_ORW \\
      Suff ‘?i. h' N <= f' i + g' i’
      >- (STRIP_TAC \\
          Q.EXISTS_TAC ‘f' i + g' i’ >> art [] \\
          Q.EXISTS_TAC ‘i’ >> REFL_TAC) \\
   (* NOTE: The choice ‘N’ is more than enough (actually “N DIV 2” may just work) *)
      Q.EXISTS_TAC ‘N’ >> simp [Abbr ‘f'’, Abbr ‘g'’, Abbr ‘h'’] \\
      qabbrev_tac ‘s = {i | i < N /\ EVEN i}’ \\
      qabbrev_tac ‘t = {i | i < N /\ ODD i}’ \\
      Know ‘SIGMA h (count N) = SIGMA h (s UNION t)’
      >- (AP_TERM_TAC \\
          rw [Once EXTENSION, Abbr ‘s’, Abbr ‘t’] \\
          METIS_TAC [EVEN_ODD]) >> Rewr' \\
     ‘DISJOINT s t’ by rw [DISJOINT_ALT, Abbr ‘s’, Abbr ‘t’, EVEN_ODD] \\
      Know ‘FINITE s’
      >- (irule SUBSET_FINITE \\
          Q.EXISTS_TAC ‘count N’ >> simp [SUBSET_DEF, Abbr ‘s’]) >> DISCH_TAC \\
      Know ‘FINITE t’
      >- (irule SUBSET_FINITE \\
          Q.EXISTS_TAC ‘count N’ >> simp [SUBSET_DEF, Abbr ‘t’]) >> DISCH_TAC \\
      Know ‘SIGMA h (s UNION t) = SIGMA h s + SIGMA h t’
      >- (irule EXTREAL_SUM_IMAGE_DISJOINT_UNION >> simp [] \\
          DISJ1_TAC >> Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
          MATCH_MP_TAC pos_not_neginf >> art []) >> Rewr' \\
      qabbrev_tac ‘s' = {i DIV 2 | i < N /\ EVEN i}’ \\
     ‘s' = IMAGE (\i. i DIV 2) s’ by rw [Once EXTENSION, Abbr ‘s'’, Abbr ‘s’] \\
      Know ‘SIGMA h s = SIGMA f s'’
      >- (POP_ORW >> qmatch_abbrev_tac ‘_ = SIGMA f (IMAGE f' s)’ \\
          Know ‘SIGMA f (IMAGE f' s) = SIGMA (f o f') s’
          >- (irule EXTREAL_SUM_IMAGE_IMAGE >> simp [] \\
              CONJ_TAC >- (DISJ1_TAC >> Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
                           MATCH_MP_TAC pos_not_neginf >> art []) \\
              rw [INJ_DEF, Abbr ‘s’, Abbr ‘f'’] >- (Q.EXISTS_TAC ‘i’ >> art []) \\
              rename1 ‘j < N’ >> gs [EVEN_EXISTS]) >> Rewr' \\
          irule EXTREAL_SUM_IMAGE_EQ >> simp [] \\
          reverse CONJ_TAC
          >- (DISJ1_TAC >> Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
              CONJ_TAC >> MATCH_MP_TAC pos_not_neginf >> art []) \\
          Q.X_GEN_TAC ‘i’ >> rw [Abbr ‘s’, Abbr ‘h’, Abbr ‘f’, Abbr ‘f'’] \\
          simp [Abbr ‘J’]) >> Rewr' \\
     ‘FINITE s'’ by simp [IMAGE_FINITE] \\
      Q.PAT_X_ASSUM ‘s' = _’ K_TAC \\
      qabbrev_tac ‘t' = {(i - 1) DIV 2 | i < N /\ ODD i}’ \\
     ‘t' = IMAGE (\i. (i - 1) DIV 2) t’ by rw [Once EXTENSION, Abbr ‘t'’, Abbr ‘t’] \\
      Know ‘SIGMA h t = SIGMA g t'’
      >- (POP_ORW >> qmatch_abbrev_tac ‘_ = SIGMA g (IMAGE g' t)’ \\
          Know ‘SIGMA g (IMAGE g' t) = SIGMA (g o g') t’
          >- (irule EXTREAL_SUM_IMAGE_IMAGE >> simp [] \\
              CONJ_TAC
              >- (DISJ1_TAC >> Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
                  MATCH_MP_TAC pos_not_neginf >> art []) \\
              rw [INJ_DEF, Abbr ‘t’, Abbr ‘g'’] >- (Q.EXISTS_TAC ‘i’ >> art []) \\
              rename1 ‘j < N’ >> gs [ODD_EXISTS]) >> Rewr' \\
          irule EXTREAL_SUM_IMAGE_EQ >> simp [] \\
          reverse CONJ_TAC
          >- (DISJ1_TAC >> Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
              CONJ_TAC >> MATCH_MP_TAC pos_not_neginf >> art []) \\
          Q.X_GEN_TAC ‘i’ >> rw [Abbr ‘t’, Abbr ‘h’, Abbr ‘g’, Abbr ‘g'’] \\
          fs [ODD_EVEN] \\
          simp [Abbr ‘J’]) >> Rewr' \\
     ‘FINITE t'’ by simp [IMAGE_FINITE] \\
      Q.PAT_X_ASSUM ‘t' = _’ K_TAC \\
      MATCH_MP_TAC le_add2 >> CONJ_TAC >| (* 2 subgoals *)
      [ (* goal 1.1 (of 2) *)
        MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET >> simp [] \\
        rw [SUBSET_DEF, Abbr ‘s'’] \\
        Q_TAC (TRANS_TAC LESS_EQ_LESS_TRANS) ‘i’ >> art [] \\
        MATCH_MP_TAC DIV_LESS_EQ >> simp [],
        (* goal 1.2 (of 2) *)
        MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET >> simp [] \\
        rw [SUBSET_DEF, Abbr ‘t'’] \\
        Q_TAC (TRANS_TAC LESS_EQ_LESS_TRANS) ‘i’ >> art [] \\
        Q_TAC (TRANS_TAC LESS_EQ_TRANS) ‘i - 1’ >> simp [] \\
        MATCH_MP_TAC DIV_LESS_EQ >> simp [] ],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC sup_le_sup_imp' \\
      Q.X_GEN_TAC ‘z’ >> simp [] \\
      DISCH_THEN (Q.X_CHOOSE_THEN ‘N’ STRIP_ASSUME_TAC) >> POP_ORW \\
      Suff ‘?i. f' N + g' N <= h' i’
      >- (STRIP_TAC \\
          Q.EXISTS_TAC ‘h' i’ >> art [] \\
          Q.EXISTS_TAC ‘i’ >> REFL_TAC) \\
   (* NOTE: The choice ‘N’ here is just enough *)
      Q.EXISTS_TAC ‘2 * N’ >> simp [Abbr ‘f'’, Abbr ‘g'’, Abbr ‘h'’] \\
      qabbrev_tac ‘s = {i | i < 2 * N /\ EVEN i}’ \\
      qabbrev_tac ‘t = {i | i < 2 * N /\ ODD i}’ \\
      Know ‘SIGMA h (count (2 * N)) = SIGMA h (s UNION t)’
      >- (AP_TERM_TAC \\
          rw [Once EXTENSION, Abbr ‘s’, Abbr ‘t’] \\
          METIS_TAC [EVEN_ODD]) >> Rewr' \\
     ‘DISJOINT s t’ by rw [DISJOINT_ALT, Abbr ‘s’, Abbr ‘t’, EVEN_ODD] \\
      Know ‘FINITE s’
      >- (irule SUBSET_FINITE \\
          Q.EXISTS_TAC ‘count (2 * N)’ >> simp [SUBSET_DEF, Abbr ‘s’]) \\
      DISCH_TAC \\
      Know ‘FINITE t’
      >- (irule SUBSET_FINITE \\
          Q.EXISTS_TAC ‘count (2 * N)’ >> simp [SUBSET_DEF, Abbr ‘t’]) \\
      DISCH_TAC \\
      Know ‘SIGMA h (s UNION t) = SIGMA h s + SIGMA h t’
      >- (irule EXTREAL_SUM_IMAGE_DISJOINT_UNION >> simp [] \\
          DISJ1_TAC >> Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
          MATCH_MP_TAC pos_not_neginf >> art []) >> Rewr' \\
      qabbrev_tac ‘s' = {i DIV 2 | i < 2 * N /\ EVEN i}’ \\
     ‘s' = IMAGE (\i. i DIV 2) s’ by rw [Once EXTENSION, Abbr ‘s'’, Abbr ‘s’] \\
      Know ‘SIGMA h s = SIGMA f s'’
      >- (POP_ORW >> qmatch_abbrev_tac ‘_ = SIGMA f (IMAGE f' s)’ \\
          Know ‘SIGMA f (IMAGE f' s) = SIGMA (f o f') s’
          >- (irule EXTREAL_SUM_IMAGE_IMAGE >> simp [] \\
              CONJ_TAC
              >- (DISJ1_TAC >> Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
                  MATCH_MP_TAC pos_not_neginf >> art []) \\
              rw [INJ_DEF, Abbr ‘s’, Abbr ‘f'’]
              >- (Q.EXISTS_TAC ‘i’ >> art []) \\
              rename1 ‘j < 2 * N’ \\
              gs [EVEN_EXISTS]) >> Rewr' \\
          irule EXTREAL_SUM_IMAGE_EQ >> simp [] \\
          reverse CONJ_TAC
          >- (DISJ1_TAC >> Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
              CONJ_TAC >> MATCH_MP_TAC pos_not_neginf >> art []) \\
          Q.X_GEN_TAC ‘i’ >> rw [Abbr ‘s’, Abbr ‘h’, Abbr ‘f’, Abbr ‘f'’] \\
          simp [Abbr ‘J’]) >> Rewr' \\
     ‘FINITE s'’ by simp [IMAGE_FINITE] \\
      Q.PAT_X_ASSUM ‘s' = _’ K_TAC \\
      qabbrev_tac ‘t' = {(i - 1) DIV 2 | i < 2 * N /\ ODD i}’ \\
     ‘t' = IMAGE (\i. (i - 1) DIV 2) t’
       by rw [Once EXTENSION, Abbr ‘t'’, Abbr ‘t’] \\
      Know ‘SIGMA h t = SIGMA g t'’
      >- (POP_ORW >> qmatch_abbrev_tac ‘_ = SIGMA g (IMAGE g' t)’ \\
          Know ‘SIGMA g (IMAGE g' t) = SIGMA (g o g') t’
          >- (irule EXTREAL_SUM_IMAGE_IMAGE >> simp [] \\
              CONJ_TAC >- (DISJ1_TAC >> Q.X_GEN_TAC ‘i’ >> STRIP_TAC \\
                           MATCH_MP_TAC pos_not_neginf >> art []) \\
              rw [INJ_DEF, Abbr ‘t’, Abbr ‘g'’]
              >- (Q.EXISTS_TAC ‘i’ >> art []) \\
              rename1 ‘j < 2 * N’ \\
              gs [ODD_EXISTS]) >> Rewr' \\
          irule EXTREAL_SUM_IMAGE_EQ >> simp [] \\
          reverse CONJ_TAC
          >- (DISJ1_TAC >> Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
              CONJ_TAC >> MATCH_MP_TAC pos_not_neginf >> art []) \\
          Q.X_GEN_TAC ‘i’ >> rw [Abbr ‘t’, Abbr ‘h’, Abbr ‘g’, Abbr ‘g'’] \\
          fs [ODD_EVEN] >> simp [Abbr ‘J’]) >> Rewr' \\
     ‘FINITE t'’ by simp [IMAGE_FINITE] \\
      Q.PAT_X_ASSUM ‘t' = _’ K_TAC \\
      MATCH_MP_TAC le_add2 >> CONJ_TAC >| (* 2 subgoals *)
      [ (* goal 1.1 (of 2) *)
        MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET >> simp [] \\
        rw [SUBSET_DEF, Abbr ‘s'’] >> rename1 ‘j < N’ \\
        Q.EXISTS_TAC ‘2 * j’ >> simp [EVEN_DOUBLE],
        (* goal 1.2 (of 2) *)
        MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET >> simp [] \\
        rw [SUBSET_DEF, Abbr ‘t'’] >> rename1 ‘j < N’ \\
        Q.EXISTS_TAC ‘SUC (2 * j)’ >> simp [ODD_DOUBLE] ] ]
QED

Theorem UNIT_INTERVAL_PARTITION' :
    univ(:real) = BIGUNION (IMAGE (\n. interval [-&SUC n,-&n] UNION
                                       interval [&n,&SUC n]) univ(:num))
Proof
    qabbrev_tac ‘A = \n. interval [-&SUC n,-&n]’
 >> qabbrev_tac ‘B = \n. interval [&n,&SUC n]’
 >> simp []
 >> rw [Once EXTENSION, IN_BIGUNION_IMAGE]
 >> Cases_on ‘0 <= x’
 >- (MP_TAC (Q.SPEC ‘x’ SIMP_REAL_ARCH_SUC) >> rw [] \\
     Q.EXISTS_TAC ‘n’ >> DISJ2_TAC >> rw [Abbr ‘B’, IN_INTERVAL] \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art [])
 >> fs [REAL_NOT_LE]
 >> ‘x <= 0’ by simp [REAL_LT_IMP_LE]
 >> ‘0 <= -x’ by simp []
 >> MP_TAC (Q.SPEC ‘-x’ SIMP_REAL_ARCH_SUC) >> rw []
 >> Q.EXISTS_TAC ‘n’ >> DISJ1_TAC
 >> rw [Abbr ‘A’, IN_INTERVAL] (* 2 subgoals, same tactic *)
 >> REAL_ASM_ARITH_TAC
QED

(* 18.16 Approximation Theorem [2, p.312]

   NOTE: It's a stronger result than textbook for all Lebesgue measurable sets.
 *)
Theorem approximation_thm :
    !E e. E IN measurable_sets lebesgue /\ 0 < e ==>
          ?J. (!i. closed_interval (J i)) /\
              (!i j. i <> j ==> nonoverlapping (J i) (J j)) /\
               E SUBSET BIGUNION (IMAGE J UNIV) /\
               lmeasure E <= suminf (lmeasure o J) /\
               suminf (lmeasure o J) <= lmeasure E + Normal e
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘A = \n. interval [-&SUC n,-&n]’
 >> qabbrev_tac ‘B = \n. interval [&n,&SUC n]’
 >> Know ‘!n. closed_interval (A n)’
 >- (rw [closed_interval_def, Abbr ‘A’] \\
     qexistsl_tac [‘-&SUC n’, ‘-&n’] >> REFL_TAC)
 >> DISCH_TAC
 >> Know ‘!n. closed_interval (B n)’
 >- (rw [closed_interval_def, Abbr ‘B’] \\
     qexistsl_tac [‘&n’, ‘&SUC n’] >> REFL_TAC)
 >> DISCH_TAC
 >> Know ‘!i j. i <> j ==> nonoverlapping (A i) (A j)’
 >- (rw [Abbr ‘A’] \\
     simp [closed_interval_nonoverlapping])
 >> DISCH_TAC
 >> Know ‘!i j. i <> j ==> nonoverlapping (B i) (B j)’
 >- (rw [Abbr ‘B’] \\
     simp [closed_interval_nonoverlapping])
 >> DISCH_TAC
 >> Know ‘!i j. (A i UNION B i) INTER (A j UNION B j) =
                (A i INTER A j) UNION (B i INTER B j)’
 >- (rpt GEN_TAC \\
     Cases_on ‘i = j’ >- simp [] \\
     rw [Once EXTENSION] \\
     EQ_TAC >> rw [] >> simp [] >| (* only 2 subgoals left *)
     [ (* goal 1 (of 2) *)
       Suff ‘F’ >- simp [] \\
       NTAC 3 (POP_ASSUM MP_TAC) >> simp [Abbr ‘A’, Abbr ‘B’] \\
       KILL_TAC >> rw [IN_INTERVAL] \\
       CCONTR_TAC >> fs [] (* -&SUC i <= x <= -&i < &j <= x <= &SUC j *) \\
      ‘i < j \/ j < i’ by simp [] >| (* 2 subgoals *)
       [ (* goal 1.1 (of 2) *)
        ‘-&i <= (&i :real)’ by simp [] \\
        ‘&i < (&j :real)’ by simp [] \\
        ‘-&i < (&j :real)’ by PROVE_TAC [REAL_LET_TRANS] \\
        ‘x < &j’ by PROVE_TAC [REAL_LET_TRANS] \\
         METIS_TAC [REAL_LET_ANTISYM],
         (* goal 1.2 (of 2) *)
        ‘-&i < (&j :real)’ by simp [] \\
        ‘x < &j’ by PROVE_TAC [REAL_LET_TRANS] \\
         METIS_TAC [REAL_LET_ANTISYM] ],
       (* goal 2 (of 2) *)
       Suff ‘F’ >- simp [] \\
       NTAC 3 (POP_ASSUM MP_TAC) >> simp [Abbr ‘A’, Abbr ‘B’] \\
       KILL_TAC >> rw [IN_INTERVAL] \\
       CCONTR_TAC >> fs [] (* -&SUC j <= x <= -&j < &i <= x <= &SUC i *) \\
      ‘i < j \/ j < i’ by simp [] >| (* 2 subgoals *)
       [ (* goal 2.1 (of 2) *)
        ‘-&j < (&i :real)’ by simp [] \\
        ‘x < &i’ by PROVE_TAC [REAL_LET_TRANS] \\
         METIS_TAC [REAL_LET_ANTISYM],
         (* goal 2.2 (of 2) *)
        ‘-&j <= (&j :real)’ by simp [] \\
        ‘&j < (&i :real)’ by simp [] \\
        ‘-&j < (&i :real)’ by PROVE_TAC [REAL_LET_TRANS] \\
        ‘x < &i’ by PROVE_TAC [REAL_LET_TRANS] \\
         METIS_TAC [REAL_LET_ANTISYM] ] ])
 >> DISCH_TAC
 >> Know ‘!n. A n IN measurable_sets lebesgue /\
              B n IN measurable_sets lebesgue’
 >- (Q.X_GEN_TAC ‘n’ \\
     Suff ‘A n IN measurable_sets lborel /\ B n IN measurable_sets lborel’
     >- METIS_TAC [SUBSET_DEF, lborel_subset_lebesgue] \\
     simp [Abbr ‘A’, Abbr ‘B’, CLOSED_interval, sets_lborel,
           borel_measurable_sets])
 >> DISCH_THEN (STRIP_ASSUME_TAC o SIMP_RULE std_ss [FORALL_AND_THM])
 (* decompose E *)
 >> Know ‘E = E INTER UNIV’ >- SET_TAC []
 >> ‘UNIV = BIGUNION (IMAGE (\n. A n UNION B n) UNIV)’
      by simp [UNIT_INTERVAL_PARTITION']  >> POP_ORW
 >> SIMP_TAC std_ss [BIGUNION_OVER_INTER_R]
 >> qmatch_abbrev_tac ‘E = BIGUNION (IMAGE s UNIV) ==> _’ (* this asserts “s” *)
 >> Rewr'
 >> Know ‘!n. s n IN measurable_sets lebesgue’
 >- (RW_TAC std_ss [Abbr ‘s’] \\
     MATCH_MP_TAC MEASURE_SPACE_INTER >> simp [measure_space_lebesgue] \\
     MATCH_MP_TAC MEASURE_SPACE_UNION >> simp [measure_space_lebesgue])
 >> DISCH_TAC
 >> Know ‘!n. (0 :real) < e * (1 / 2) pow (n + 1)’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC REAL_LT_MUL >> art [GSYM ADD1] \\
     MATCH_MP_TAC POW_POS_LT >> simp [])
 >> DISCH_TAC
 >> ‘!n. s n SUBSET A n UNION B n’ by rw [Abbr ‘s’]
 (* applying approximation_lemma2 *)
 >> Know ‘!n. ?J. (!i. closed_interval (J i)) /\
                  (!i. J i SUBSET (A n UNION B n)) /\
                  (!i j. i <> j ==> nonoverlapping (J i) (J j)) /\
                  s n SUBSET BIGUNION (IMAGE J univ(:num)) /\
                  lmeasure (s n) <= suminf (lmeasure o J) /\
                  suminf (lmeasure o J) <=
                  lmeasure (s n) + Normal (e * (1 / 2) pow (n + 1))’
 >- (Q.X_GEN_TAC ‘n’ \\
     MP_TAC (Q.SPECL [‘s (n :num)’, ‘e * (1 / 2) pow (n + 1)’, ‘n’]
                     approximation_lemma2) >> simp [])
 >> SIMP_TAC std_ss [SKOLEM_THM, FORALL_AND_THM] (* this asserts f *)
 >> Know ‘!n. Normal (e * (1 / 2) pow (n + 1)) = Normal e * (1 / 2) pow (n + 1)’
 >- (RW_TAC std_ss [GSYM extreal_mul_eq] \\
     AP_TERM_TAC \\
     REWRITE_TAC [GSYM extreal_pow_def] \\
     simp [extreal_div_eq, extreal_of_num_def])
 >> Rewr'
 >> STRIP_TAC
 >> Know ‘!i j. i <> j ==> negligible (s i INTER s j)’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC NEGLIGIBLE_SUBSET \\
     Q.EXISTS_TAC ‘(A i UNION B i) INTER (A j UNION B j)’ \\
     reverse CONJ_TAC >- (simp [Abbr ‘s’] >> SET_TAC []) \\
     simp [] \\
     MATCH_MP_TAC NEGLIGIBLE_UNION \\
     CONJ_TAC \\ (* 2 subgoals, same tactics *)
     MATCH_MP_TAC closed_interval_nonoverlapping_imp_negligible >> simp [])
 >> DISCH_TAC
 (* applying lebesgue_countably_additive *)
 >> Know ‘lmeasure (BIGUNION (IMAGE s UNIV)) = suminf (lmeasure o s)’
 >- (SYM_TAC >> MATCH_MP_TAC lebesgue_countably_additive \\
     simp [IN_FUNSET])
 >> Rewr'
 (* applying NUM_2D_BIJ_INV *)
 >> Q.X_CHOOSE_THEN ‘h’ STRIP_ASSUME_TAC NUM_2D_BIJ_INV
 >> Q.EXISTS_TAC ‘UNCURRY f o h’
 >> qabbrev_tac ‘l = \n i. lmeasure (f n i)’
 >> Know ‘lmeasure o UNCURRY f o h = UNCURRY l o h’
 >- (rw [FUN_EQ_THM, o_DEF, Abbr ‘l’] \\
     qabbrev_tac ‘t = h x’ \\
     PairCases_on ‘t’ >> simp [])
 >> Rewr'
 (* applying ext_suminf_2d_full *)
 >> Know ‘suminf (UNCURRY l o h) = suminf (\n. suminf (l n))’
 >- (MATCH_MP_TAC ext_suminf_2d_full >> simp [] \\
     rw [Abbr ‘l’] \\
     MATCH_MP_TAC MEASURE_POSITIVE \\
     simp [measure_space_lebesgue, closed_interval_imp_lebesgue])
 >> Rewr'
 >> CONJ_TAC (* closed_interval *)
 >- (rw [o_DEF] >> Cases_on ‘h (i :num)’ >> simp [])
 (* [-&SUC j,-&j] < [-&SUC i,-&i] < [&i,&SUC i] < [&j,&SUC j]
         A j            A i             B i           B j     *)
 >> Know ‘!i j. i < j ==> nonoverlapping (A i UNION B i) (A j UNION B j)’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC nonoverlapping_subset_inclusive \\
     qexistsl_tac [‘interval [-&SUC i,&SUC i]’, ‘{x | x <= -&j \/ &j <= x}’] \\
     reverse CONJ_TAC
     >- (rw [Abbr ‘A’, Abbr ‘B’, SUBSET_DEF, IN_INTERVAL] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
          ‘-&i <= (&i) :real’ by simp [] \\
           Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘-&i’ >> art [] \\
           Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘&i’ >> simp [],
           (* goal 2 (of 2) *)
          ‘-&i <= (&i) :real’ by simp [] \\
          ‘-&i <= x’ by PROVE_TAC [REAL_LE_TRANS] \\
           Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘-&i’ >> simp [] ]) \\
     simp [nonoverlapping_def, INTERIOR_INTERVAL] \\
    ‘SUC i <= j’ by simp [] \\
     qabbrev_tac ‘n = SUC i’ \\
     rw [DISJOINT_ALT, IN_INTERIOR, IN_INTERVAL] \\
     STRONG_DISJ_TAC >> rename1 ‘0 < r’ \\
     rw [SUBSET_DEF, IN_BALL, REAL_NOT_LE] \\
  (* -&j <= -&n < x < y < &n <= &j *)
     MP_TAC (Q.SPECL [‘x’, ‘min (x + r) &n’] REAL_MEAN) \\
     simp [REAL_LT_MIN] >> STRIP_TAC (* this asserts ‘z’ *) \\
     Q.EXISTS_TAC ‘z’ >> simp [dist] \\
    ‘x - z < 0’ by simp [REAL_SUB_LT_NEG] \\
     simp [ABS_EQ_NEG] \\
     CONJ_TAC >- (Q.PAT_X_ASSUM ‘z < x + r’ MP_TAC >> REAL_ARITH_TAC) \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q_TAC (TRANS_TAC REAL_LET_TRANS) ‘-&n’ >> simp [] \\
       Q_TAC (TRANS_TAC REAL_LT_TRANS) ‘x’ >> art [],
       (* goal 2 (of 2) *)
       Q_TAC (TRANS_TAC REAL_LTE_TRANS) ‘&n’ >> simp [] ])
 >> DISCH_TAC
 >> CONJ_TAC (* nonoverlapping *)
 >- (rw [o_DEF] \\
     Cases_on ‘h (i :num)’ >> rename1 ‘h i = (n1,i1)’ \\
     Cases_on ‘h (j :num)’ >> rename1 ‘h j = (n2,i2)’ \\
     simp [] \\
     Cases_on ‘n1 = n2’
     >- (Suff ‘i1 <> i2’ >- rw [] \\
         CCONTR_TAC >> fs [] \\
        ‘h i = h j’ by PROVE_TAC [] \\
         Q.PAT_X_ASSUM ‘BIJ h _ _’ MP_TAC \\
         rw [BIJ_DEF, INJ_DEF] >> DISJ1_TAC \\
         qexistsl_tac [‘i’, ‘j’] >> simp []) \\
     MATCH_MP_TAC nonoverlapping_subset_inclusive \\
     qexistsl_tac [‘A n1 UNION B n1’, ‘A n2 UNION B n2’] >> art [] \\
    ‘n1 < n2 \/ n2 < n1’ by simp [] >- simp [] \\
     simp [Once nonoverlapping_comm])
 >> CONJ_TAC (* SUBSET *)
 >- (rw [SUBSET_DEF, IN_BIGUNION_IMAGE, o_DEF] \\
     rename1 ‘x IN s n’ \\
     Know ‘x IN BIGUNION (IMAGE (f n) UNIV)’ >- METIS_TAC [SUBSET_DEF] \\
     rw [IN_BIGUNION_IMAGE] >> rename1 ‘x IN f n j’ \\
     Q.PAT_X_ASSUM ‘BIJ h _ _’ MP_TAC >> rw [BIJ_DEF, SURJ_DEF] \\
     POP_ASSUM (MP_TAC o Q.SPEC ‘(n,j)’) >> rw [] \\
     Q.EXISTS_TAC ‘y’ >> simp [])
 >> CONJ_TAC (* suminf <= suminf *)
 >- (MATCH_MP_TAC ext_suminf_mono \\
     CONJ_TAC >- (rw [o_DEF] >> MATCH_MP_TAC MEASURE_POSITIVE \\
                  simp [measure_space_lebesgue]) \\
     rw [o_DEF, Abbr ‘l’] \\
     Q.PAT_X_ASSUM ‘!n. lmeasure (s n) <= suminf (lmeasure o f n)’
       (MP_TAC o Q.SPEC ‘n’) >> simp [o_DEF])
 (* applying pow_half_ser_by_e *)
 >> Know ‘Normal e = suminf (\n. Normal e * (1 / 2) pow (n + 1))’
 >- (MATCH_MP_TAC pow_half_ser_by_e >> simp [extreal_of_num_def])
 >> Rewr'
 (* applying ext_suminf_add *)
 >> Know ‘suminf (lmeasure o s) + suminf (\n. Normal e * (1 / 2) pow (n + 1)) =
          suminf (\n. (lmeasure o s) n + (\n. Normal e * (1 / 2) pow (n + 1)) n)’
 >- (SYM_TAC >> MATCH_MP_TAC ext_suminf_add >> rw []
     >- (MATCH_MP_TAC MEASURE_POSITIVE \\
         simp [measure_space_lebesgue]) \\
     MATCH_MP_TAC le_mul \\
     CONJ_TAC >- simp [extreal_of_num_def, REAL_LT_IMP_LE] \\
     MATCH_MP_TAC pow_pos_le >> simp [])
 >> Rewr'
 >> simp [o_DEF]
 >> MATCH_MP_TAC ext_suminf_mono >> rw []
 >- (MATCH_MP_TAC ext_suminf_pos \\
     Q.X_GEN_TAC ‘j’ >> rw [Abbr ‘l’] \\
     MATCH_MP_TAC MEASURE_POSITIVE \\
     simp [measure_space_lebesgue] \\
     MATCH_MP_TAC closed_interval_imp_lebesgue >> art [])
 >> Q.PAT_X_ASSUM ‘!n. suminf (lmeasure o f n) <= _’ (MP_TAC o Q.SPEC ‘n’)
 >> simp [Abbr ‘l’, o_DEF]
QED

(* NOTE: “fsigma” is overload_on “fsigma_in euclidean” *)
Theorem lebesgue_approximation_fsigma :
    !E e. E IN measurable_sets lebesgue /\ 0 < e ==>
          ?s. fsigma s /\ E SUBSET s /\
              lmeasure E <= lambda s /\
              lambda s <= lmeasure E + Normal e
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘E’, ‘e’] approximation_thm) >> rw []
 >> qabbrev_tac ‘s = BIGUNION (IMAGE J UNIV)’
 >> Q.EXISTS_TAC ‘s’ >> art []
 >> CONJ_ASM1_TAC
 >- (qunabbrev_tac ‘s’ \\
     MATCH_MP_TAC (ISPEC “euclidean” FSIGMA_IN_UNIONS) >> rw [] \\
     MATCH_MP_TAC CLOSED_IMP_FSIGMA_IN \\
     REWRITE_TAC [GSYM CLOSED_IN] \\
     MATCH_MP_TAC closed_interval_closed >> art [])
 >> ‘s IN subsets borel’ by PROVE_TAC [borel_fsigma]
 >> ‘lambda s = lmeasure s’ by PROVE_TAC [lebesgue_eq_lambda] >> POP_ORW
 >> Suff ‘lmeasure s = suminf (lmeasure o J)’ >- simp []
 >> SYM_TAC >> MATCH_MP_TAC lebesgue_countably_additive
 >> rw [IN_FUNSET]
 >- (MATCH_MP_TAC closed_interval_imp_lebesgue >> art [])
 >> MATCH_MP_TAC closed_interval_nonoverlapping_imp_negligible
 >> simp []
QED

Theorem lebesgue_approximation :
    !E e. E IN measurable_sets lebesgue /\ 0 < e ==>
          ?s. s IN subsets borel /\ E SUBSET s /\
              lmeasure E <= lambda s /\
              lambda s <= lmeasure E + Normal e
Proof
    rpt STRIP_TAC
 >> drule_all_then STRIP_ASSUME_TAC lebesgue_approximation_fsigma
 >> Q.EXISTS_TAC ‘s’ >> art []
 >> MATCH_MP_TAC borel_fsigma >> art []
QED

Theorem negligible_approximation_lemma[local] :
    !E e. E IN measurable_sets lebesgue /\ lmeasure E = 0 /\ 0 < e ==>
          ?s. s IN subsets borel /\ E SUBSET s /\ lambda s <= Normal e
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘E’, ‘e’] lebesgue_approximation) >> rw []
 >> Q.EXISTS_TAC ‘s’ >> art []
QED

Theorem negligible_approximation :
    !E e. negligible E /\ 0 < e ==>
          ?s. s IN subsets borel /\ E SUBSET s /\ lambda s <= Normal e
Proof
    rpt STRIP_TAC
 >> ‘E IN measurable_sets lebesgue’ by PROVE_TAC [negligible_in_lebesgue]
 >> ‘lmeasure E = 0’ by PROVE_TAC [lebesgue_of_negligible]
 >> MATCH_MP_TAC negligible_approximation_lemma >> art []
QED

Theorem negligible_approximation_null_set :
    !E. negligible E ==> ?N. N IN null_set lborel /\ E SUBSET N
Proof
    rpt STRIP_TAC
 >> Know ‘!n. (0 :real) < inv &SUC n’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC REAL_INV_POS >> simp [])
 >> DISCH_TAC
 >> Know ‘!n. ?s. s IN subsets borel /\ E SUBSET s /\
                  lambda s <= Normal (inv &SUC n)’
 >- (Q.X_GEN_TAC ‘n’ \\
     MP_TAC (Q.SPECL [‘E’, ‘inv &SUC n’] negligible_approximation) >> rw [] \\
     Q.EXISTS_TAC ‘s’ >> art [])
 >> simp [SKOLEM_THM, FORALL_AND_THM] (* this asserts ‘f’ *)
 >> STRIP_TAC
 >> qabbrev_tac ‘g = \n. BIGINTER (IMAGE f (count1 n))’
 >> Know ‘!n. g n IN subsets borel’
 >- (rw [Abbr ‘g’] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_FINITE_INTER >> rw [sigma_algebra_borel])
 >> DISCH_TAC
 >> ‘!n. g n SUBSET f n’ by rw [Abbr ‘g’, IN_BIGINTER_IMAGE, SUBSET_DEF]
 >> Know ‘!n. lambda (g n) <= Normal (inv &SUC n)’
 >- (rpt STRIP_TAC \\
     Q_TAC (TRANS_TAC le_trans) ‘lambda (f n)’ >> art [] \\
     MATCH_MP_TAC MEASURE_INCREASING >> rw [lborel_def, sets_lborel])
 >> DISCH_TAC
 >> ‘!n. g (SUC n) SUBSET g n’ by rw [Abbr ‘g’, IN_BIGINTER_IMAGE, SUBSET_DEF]
 >> qabbrev_tac ‘s = BIGINTER (IMAGE g UNIV)’
 >> Q.EXISTS_TAC ‘s’
 >> reverse CONJ_TAC
 >- (rw [SUBSET_DEF, Abbr ‘s’, IN_BIGINTER_IMAGE] \\
     rw [Abbr ‘g’, IN_BIGINTER_IMAGE] \\
     METIS_TAC [SUBSET_DEF])
 >> simp [IN_NULL_SET, null_set_def, sets_lborel]
 >> CONJ_ASM1_TAC
 >- (qunabbrev_tac ‘s’ \\
     MATCH_MP_TAC SIGMA_ALGEBRA_BIGINTER >> simp [sigma_algebra_borel])
 >> reverse (rw [GSYM le_antisym])
 >- (MATCH_MP_TAC MEASURE_POSITIVE \\
     simp [lborel_def, sets_lborel])
 >> Know ‘lambda s = inf (IMAGE (lambda o g) UNIV)’
 >- (SYM_TAC >> MATCH_MP_TAC MONOTONE_CONVERGENCE_BIGINTER \\
     rw [IN_FUNSET, lborel_def, sets_lborel, lt_infty] \\
     Q_TAC (TRANS_TAC let_trans) ‘Normal (inv &SUC n)’ \\
     simp [GSYM lt_infty])
 >> Rewr'
 >> MATCH_MP_TAC le_epsilon >> rw []
 >> rw [inf_le']
 >> MP_TAC (Q.SPEC ‘e’ EXTREAL_ARCH_INV) >> rw []
 >> Q_TAC (TRANS_TAC le_trans) ‘inv &SUC n’ >> simp [lt_imp_le]
 >> Know ‘inv &SUC n = Normal (inv &SUC n)’
 >- (‘&SUC n <> (0 :real)’ by simp [] \\
     simp [extreal_of_num_def, extreal_inv_eq])
 >> Rewr'
 >> Q_TAC (TRANS_TAC le_trans) ‘lambda (g n)’ >> art []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘n’ >> REFL_TAC
QED

(* |- !E. E IN null_set lebesgue ==> ?N. N IN null_set lborel /\ E SUBSET N *)
Theorem negligible_approximation_null_set' =
        negligible_approximation_null_set
     |> REWRITE_RULE [negligible_alt_lebesgue_null_set]

Theorem pos_fn_integral_fn_seq :
    !m f n. measure_space m /\ f IN Borel_measurable (measurable_space m) ==>
            pos_fn_integral m (fn_seq m f n) = fn_seq_integral m f n
Proof
    RW_TAC std_ss [fn_seq_integral_def, fn_seq_def]
 >> qabbrev_tac ‘s = \n. count (4 ** n)’
 >> qabbrev_tac ‘a = \n k. {x | x IN m_space m /\ &k / 2 pow n <= f x /\
                                f x < (&k + 1) / 2 pow n}’
 >> Know ‘!n i. a n i IN measurable_sets m’
 >- (rw [Abbr ‘a’] \\
    ‘{x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} =
     {x | &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} INTER m_space m’
       by SET_TAC [] >> POP_ORW \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE, MEASURE_SPACE_SIGMA_ALGEBRA])
 >> DISCH_TAC
 >> qabbrev_tac ‘b = \n. {x | x IN m_space m /\ 2 pow n <= f x}’
 >> Know ‘!i. b i IN measurable_sets m’
 >- (Q.X_GEN_TAC ‘n’ >> simp [Abbr ‘b’] \\
    ‘{x | x IN m_space m /\ 2 pow n <= f x} =
     {x | 2 pow n <= f x} INTER m_space m’ by SET_TAC [] >> POP_ORW \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE, MEASURE_SPACE_SIGMA_ALGEBRA])
 >> DISCH_TAC
 >> qabbrev_tac ‘c = \n k. (&k / 2 pow n) :extreal’
 >> Know ‘!i k. 0 <= c i k’
 >- (rw [Abbr ‘c’] \\
    ‘2 pow i = Normal (2 pow i)’
      by simp [extreal_of_num_def, extreal_pow_def] >> POP_ORW \\
     MATCH_MP_TAC le_div >> simp [REAL_POW_LT])
 >> DISCH_TAC
 >> qabbrev_tac ‘h = \x. SIGMA (\k. c n k * indicator_fn (a n k) x) (s n)’
 >> Know ‘!x. x IN m_space m ==> 0 <= h x’
 >- (rw [Abbr ‘h’] \\
     irule EXTREAL_SUM_IMAGE_POS >> simp [Abbr ‘s’] \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     MATCH_MP_TAC le_mul >> rw [Abbr ‘c’, INDICATOR_FN_POS])
 >> DISCH_TAC
 >> qabbrev_tac ‘g = \x. 2 pow n * indicator_fn (b n) x’ >> simp []
 >> Know ‘!x. x IN m_space m ==> 0 <= g x’
 >- (rw [Abbr ‘g’] \\
     MATCH_MP_TAC le_mul >> simp [pow_pos_le, INDICATOR_FN_POS])
 >> DISCH_TAC
 >> Know ‘pos_fn_integral m (\x. h x + g x) =
          pos_fn_integral m h + pos_fn_integral m g’
 >- (MATCH_MP_TAC pos_fn_integral_add >> art [] \\
     CONJ_TAC (* h IN Borel_measurable (measurable_space m) *)
     >- (MATCH_MP_TAC (INST_TYPE [beta |-> “:num”] IN_MEASURABLE_BOREL_SUM) \\
         simp [MEASURE_SPACE_SIGMA_ALGEBRA, Abbr ‘h’] \\
         qexistsl_tac [‘\k x. c n k * indicator_fn (a n k) x’, ‘s n’] \\
         simp [Abbr ‘s’] \\
         reverse CONJ_TAC
         >- (rpt GEN_TAC >> STRIP_TAC \\
             MATCH_MP_TAC pos_not_neginf \\
             MATCH_MP_TAC le_mul >> simp [INDICATOR_FN_POS]) \\
         rw [Abbr ‘c’] \\
         simp [extreal_of_num_def, extreal_pow_def] \\
        ‘(0 :real) < 2 pow n’ by simp [REAL_POW_LT] \\
        ‘2 pow n <> 0 :real’ by PROVE_TAC [REAL_LT_IMP_NE] \\
         simp [extreal_div_eq] \\
         MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR \\
         simp [MEASURE_SPACE_SIGMA_ALGEBRA]) \\
  (* g IN Borel_measurable (measurable_space m) *)
     rw [Abbr ‘g’, extreal_of_num_def, extreal_pow_def] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR \\
     simp [MEASURE_SPACE_SIGMA_ALGEBRA])
 >> Rewr'
 >> Know ‘pos_fn_integral m g = 2 pow n * measure m (b n)’
 >- (simp [Abbr ‘g’, extreal_of_num_def, extreal_pow_def] \\
     MATCH_MP_TAC pos_fn_integral_cmul_indicator \\
     simp [REAL_POW_LE])
 >> Rewr'
 >> qmatch_abbrev_tac ‘x1 + y = x2 + (y :extreal)’
 >> Know ‘y <> NegInf’
 >- (MATCH_MP_TAC pos_not_neginf \\
     qunabbrev_tac ‘y’ \\
     MATCH_MP_TAC le_mul >> simp [pow_pos_le] \\
     MATCH_MP_TAC MEASURE_POSITIVE >> art [])
 >> DISCH_TAC
 >> Cases_on ‘y = PosInf’
 >- (POP_ORW \\
     Suff ‘x1 + PosInf = PosInf /\ x2 + PosInf = PosInf’ >- simp [] \\
     Suff ‘x1 <> NegInf /\ x2 <> NegInf’ >- PROVE_TAC [add_infty] \\
     CONJ_TAC >> MATCH_MP_TAC pos_not_neginf >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       qunabbrev_tac ‘x1’ \\
       MATCH_MP_TAC pos_fn_integral_pos >> art [],
       (* goal 2 (of 2) *)
       qunabbrev_tac ‘x2’ \\
       irule EXTREAL_SUM_IMAGE_POS >> rw [Abbr ‘s’] \\
       MATCH_MP_TAC le_mul >> art [] \\
       MATCH_MP_TAC MEASURE_POSITIVE >> art [] ])
 >> Know ‘x1 + y = x2 + y <=> x1 = x2’
 >- (MATCH_MP_TAC EXTREAL_EQ_RADD >> art [])
 >> Rewr'
 >> qunabbrevl_tac [‘x1’, ‘x2’]
 (* cleanup y and y-assumptions *)
 >> NTAC 2 (POP_ASSUM K_TAC) >> qunabbrev_tac ‘y’
 (* cleanup g and g-assumptions *)
 >> POP_ASSUM K_TAC >> qunabbrev_tac ‘g’
 >> POP_ASSUM K_TAC (* h-assumption *)
 >> qunabbrev_tac ‘h’
 (* re-define another g *)
 >> qabbrev_tac ‘g = \k x. c n k * indicator_fn (a n k) x’ >> simp []
 >> Know ‘!i x. x IN m_space m ==> 0 <= g i x’
 >- (rw [Abbr ‘g’] \\
     MATCH_MP_TAC le_mul >> simp [INDICATOR_FN_POS])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘m’, ‘g’, ‘s (n :num)’]
                    (INST_TYPE [beta |-> “:num”] pos_fn_integral_sum))
 >> impl_tac
 >- (simp [Abbr ‘s’] \\
     rw [Abbr ‘g’, Abbr ‘c’, extreal_of_num_def, extreal_pow_def] \\
    ‘(0 :real) < 2 pow n’ by simp [REAL_POW_LT] \\
    ‘2 pow n <> 0 :real’ by PROVE_TAC [REAL_LT_IMP_NE] \\
     simp [extreal_div_eq] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL_INDICATOR \\
     simp [MEASURE_SPACE_SIGMA_ALGEBRA])
 >> Rewr'
 >> irule EXTREAL_SUM_IMAGE_EQ
 >> simp [Abbr ‘s’]
 >> reverse CONJ_TAC
 >- (DISJ1_TAC \\
     Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
     CONJ_TAC >> MATCH_MP_TAC pos_not_neginf
     >- (MATCH_MP_TAC pos_fn_integral_pos >> art []) \\
     MATCH_MP_TAC le_mul >> art [] \\
     MATCH_MP_TAC MEASURE_POSITIVE >> art [])
 >> rw [Abbr ‘g’]
 >> simp [Abbr ‘c’, extreal_of_num_def, extreal_pow_def]
 >> ‘(0 :real) < 2 pow n’ by simp [REAL_POW_LT]
 >> ‘2 pow n <> 0 :real’ by PROVE_TAC [REAL_LT_IMP_NE]
 >> simp [extreal_div_eq]
 >> MATCH_MP_TAC pos_fn_integral_cmul_indicator >> art []
 >> MATCH_MP_TAC REAL_LE_DIV >> simp [POW_POS]
QED

(* cf. measureTheory.fn_seq_def. Here is the version for (f :'a -> real) *)
Definition real_fn_seq_def :
    real_fn_seq m (f :'a -> real) =
       (\n x. SIGMA
                (\k. &k / 2 pow n *
                     indicator
                       {x | x IN m_space m /\ &k / 2 pow n <= f x /\
                            f x < (&k + 1) / 2 pow n} x) (count (4 ** n)) +
              2 pow n * indicator {x | x IN m_space m /\ 2 pow n <= f x} x)
End

Theorem fn_seq_alt_real_fn_seq :
    !m f n x. fn_seq m (Normal o f) n x = Normal (real_fn_seq m f n x)
Proof
    RW_TAC std_ss [fn_seq_def, real_fn_seq_def]
 >> ASM_SIMP_TAC real_ss [extreal_of_num_def, extreal_pow_eq]
 >> ‘2 pow n <> (0 :real)’ by simp []
 >> ASM_SIMP_TAC real_ss
      [extreal_div_eq, extreal_le_eq, extreal_lt_eq, extreal_add_eq]
 >> qabbrev_tac ‘A = \k. {x | x IN m_space m /\ &k / 2 pow n <= f x /\
                              f x < &(k + 1) / 2 pow n}’
 >> qabbrev_tac ‘B = {x | x IN m_space m /\ 2 pow n <= f x}’
 >> qabbrev_tac ‘N = count (4 ** n)’
 >> qabbrev_tac ‘c = \k. (&k / 2 pow n) :real’
 >> ASM_SIMP_TAC std_ss []
 >> simp [indicator_fn, o_DEF, extreal_mul_eq]
 >> qabbrev_tac ‘g = \k. c k * indicator (A k) x’ >> simp []
 >> Know ‘SIGMA (\k. Normal (g k)) N = Normal (SIGMA g N)’
 >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_NORMAL \\
     simp [Abbr ‘N’])
 >> Rewr'
 >> simp [extreal_add_eq]
QED

Theorem real_fn_seq_alt_fn_seq :
    !m f n x. real_fn_seq m f n x = real (fn_seq m (Normal o f) n x)
Proof
    rw [fn_seq_alt_real_fn_seq]
QED

(* cf. lemma_fn_seq_positive *)
Theorem lemma_real_fn_seq_positive[local] :
    !m f n x. 0 <= f x ==> 0 <= real_fn_seq m f n x
Proof
    rw [real_fn_seq_alt_fn_seq]
 >> MATCH_MP_TAC real_positive
 >> MATCH_MP_TAC lemma_fn_seq_positive
 >> simp [extreal_of_num_def, o_DEF]
QED

(* cf. lemma_fn_seq_upper_bounded *)
Theorem lemma_real_fn_seq_upper_bounded[local] :
    !m f n x. 0 <= f x ==> real_fn_seq m f n x <= f x
Proof
    RW_TAC std_ss [real_fn_seq_alt_fn_seq]
 >> qabbrev_tac ‘nf = Normal o f’
 >> ‘0 <= nf x’ by rw [Abbr ‘nf’, o_DEF, extreal_of_num_def]
 >> MP_TAC (Q.SPECL [‘m’, ‘nf’, ‘n’, ‘x’] lemma_fn_seq_upper_bounded)
 >> MP_TAC (Q.SPECL [‘m’, ‘nf’, ‘n’, ‘x’] lemma_fn_seq_positive)
 >> rw [o_DEF]
 >> qabbrev_tac ‘y = fn_seq m nf n x’
 >> ‘y <> NegInf’ by simp [pos_not_neginf]
 >> Know ‘y <> PosInf’
 >- (REWRITE_TAC [lt_infty] \\
     Q_TAC (TRANS_TAC let_trans) ‘nf x’ \\
     simp [GSYM lt_infty, Abbr ‘nf’, o_DEF])
 >> DISCH_TAC
 >> ‘?r. y = Normal r’ by METIS_TAC [extreal_cases]
 >> gs [Abbr ‘nf’, o_DEF]
QED

(* cf. lemma_fn_seq_mono_increasing *)
Theorem lemma_real_fn_seq_mono_increasing[local] :
    !m f x. 0 <= f x ==> mono_increasing (\n. real_fn_seq m f n x)
Proof
    rpt GEN_TAC >> DISCH_TAC
 >> simp [real_fn_seq_alt_fn_seq, mono_increasing_def]
 >> qx_genl_tac [‘i’, ‘j’] >> DISCH_TAC
 >> MATCH_MP_TAC le_real_imp
 >> CONJ_TAC
 >- (MATCH_MP_TAC lemma_fn_seq_positive \\
     simp [extreal_of_num_def, o_DEF])
 >> CONJ_TAC
 >- (irule (SRULE [ext_mono_increasing_def] lemma_fn_seq_mono_increasing) \\
     simp [extreal_of_num_def, o_DEF])
 >> REWRITE_TAC [lt_infty]
 >> Q_TAC (TRANS_TAC let_trans) ‘(Normal o f) x’
 >> CONJ_TAC
 >- (MATCH_MP_TAC lemma_fn_seq_upper_bounded \\
     simp [extreal_of_num_def, o_DEF])
 >> simp [GSYM lt_infty, o_DEF]
QED

(* cf. fn_seq_integral_def

   NOTE: This definition requires all (k <> 0) “lambda _” must be finite, such
   that “lambda' _” is meaningful. This may be derived from “integrable lborel f”
   aka “pos_fn_integral lborel f <> PosInf”.
 *)
Overload lambda'[local] = “\s. real (lambda s)”

Definition real_fn_seq_integral_def :
    real_fn_seq_integral (f :real -> real) n =
    SIGMA (\k. &k / 2 pow n *
               lambda' {x | &k / 2 pow n <= f x /\
                            f x < (&k + 1) / 2 pow n}) (count (4 ** n)) +
    2 pow n * lambda' {x | 2 pow n <= f x}
End

Theorem real_fn_seq_lemma1[local] :
    !f i n. f IN borel_measurable borel ==>
           {x | &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} IN subsets borel

Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC
      (SRULE [sigma_algebra_borel, space_borel]
             (ISPEC “borel” in_borel_measurable_ge_lt_imp)) >> art []
QED

Theorem real_fn_seq_lemma2[local] :
    !f n. f IN borel_measurable borel ==> {x | 2 pow n <= f x} IN subsets borel
Proof
    rpt STRIP_TAC
 >> irule (SRULE [sigma_algebra_borel, space_borel]
                  (ISPECL [“f :real -> real”,“borel”]
                          (cj 2 (iffLR in_borel_measurable_ge)))) >> art []
QED

(* NOTE: “real PosInf = 0” has been used here to avoid more antecedents. *)
Theorem real_fn_seq_integral_positive :
    !f n. f IN borel_measurable borel ==> 0 <= real_fn_seq_integral f n
Proof
    RW_TAC std_ss [real_fn_seq_integral_def]
 >> MATCH_MP_TAC REAL_LE_ADD
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC REAL_LE_MUL >> simp [] \\
     MATCH_MP_TAC real_positive \\
     MATCH_MP_TAC MEASURE_POSITIVE >> simp [lborel_def, sets_lborel] \\
     MATCH_MP_TAC real_fn_seq_lemma2 >> art [])
 >> HO_MATCH_MP_TAC REAL_SUM_IMAGE_POS
 >> SIMP_TAC std_ss [FINITE_COUNT, IN_COUNT]
 >> Q.X_GEN_TAC ‘i’ >> DISCH_TAC
 >> MATCH_MP_TAC REAL_LE_MUL
 >> CONJ_TAC >- simp []
 >> MATCH_MP_TAC real_positive
 >> MATCH_MP_TAC MEASURE_POSITIVE
 >> SIMP_TAC std_ss [lborel_def, sets_lborel]
 >> MATCH_MP_TAC real_fn_seq_lemma1 >> art []
QED

Theorem fn_seq_integral_positive :
    !m f n. measure_space m /\ f IN Borel_measurable (measurable_space m) ==>
            0 <= fn_seq_integral m f n
Proof
    RW_TAC std_ss [fn_seq_integral_def]
 >> MATCH_MP_TAC le_add
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC le_mul >> simp [pow_pos_le] \\
     MATCH_MP_TAC MEASURE_POSITIVE >> art [] \\
    ‘{x | x IN m_space m /\ 2 pow n <= f x} =
     {x | 2 pow n <= f x} INTER m_space m’ by SET_TAC [] >> POP_ORW \\
     simp [IN_MEASURABLE_BOREL_ALL_MEASURE])
 >> HO_MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS
 >> SIMP_TAC std_ss [FINITE_COUNT, IN_COUNT]
 >> Q.X_GEN_TAC ‘i’ >> DISCH_TAC
 >> MATCH_MP_TAC le_mul
 >> CONJ_TAC
 >- (‘2 pow n = Normal (2 pow n)’ by simp [extreal_of_num_def, extreal_pow_def] \\
     ‘2 pow n <> (0 :real)’ by simp [] \\
     simp [extreal_div_eq] \\
     MATCH_MP_TAC le_div >> simp [])
 >> MATCH_MP_TAC MEASURE_POSITIVE >> art []
 >> ‘{x | x IN m_space m /\ &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} =
     {x | &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} INTER m_space m’
       by SET_TAC []
 >> POP_ORW
 >> simp [IN_MEASURABLE_BOREL_ALL_MEASURE]
QED

(* NOTE: If k = 0, then “&k / 2 pow n * lmeasure s = 0” even the measure is inf *)
Theorem lemma_fn_seq_finite_measure1[local] :
    !m f k n. measure_space m /\ f IN Borel_measurable (measurable_space m) /\
             (!x. x IN m_space m ==> 0 <= f x) /\
              pos_fn_integral m f <> PosInf /\ k < 4 ** n /\ k <> 0 ==>
              measure m {x | x IN m_space m /\ &k / 2 pow n <= f x /\
                             f x < (&k + 1) / 2 pow n} <> PosInf
Proof
    rpt STRIP_TAC
 >> ASSUME_TAC (Q.SPECL [‘m’, ‘f’, ‘n’] lemma_fn_seq_positive')
 >> ASSUME_TAC (Q.SPECL [‘m’, ‘f’, ‘n’] lemma_fn_seq_upper_bounded')
 >> Know ‘pos_fn_integral m (fn_seq m f n) <> PosInf’
 >- (REWRITE_TAC [lt_infty] \\
     Q_TAC (TRANS_TAC let_trans) ‘pos_fn_integral m f’ \\
     reverse CONJ_TAC >- art [GSYM lt_infty] \\
     MATCH_MP_TAC pos_fn_integral_mono >> simp [])
 >> Know ‘pos_fn_integral m (fn_seq m f n) = fn_seq_integral m f n’
 >- (MATCH_MP_TAC pos_fn_integral_fn_seq >> art [])
 >> simp [] >> DISCH_THEN K_TAC
 >> simp [fn_seq_integral_def]
 >> qmatch_abbrev_tac ‘a + b = PosInf’
 >> ‘sigma_algebra (measurable_space m)’ by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> Know ‘0 <= b’
 >- (qunabbrev_tac ‘b’ \\
     MATCH_MP_TAC le_mul >> simp [pow_pos_le] \\
     MATCH_MP_TAC MEASURE_POSITIVE >> art [] \\
    ‘{x | x IN m_space m /\ 2 pow n <= f x} =
     {x | 2 pow n <= f x} INTER m_space m’ by SET_TAC [] >> POP_ORW \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE])
 >> DISCH_TAC
 >> qunabbrev_tac ‘a’
 >> qmatch_abbrev_tac ‘SIGMA g _ + b = PosInf’
 >> qmatch_abbrev_tac ‘a + b = PosInf’
 >> Know ‘!i. 0 <= g i’
 >- (rw [Abbr ‘g’] \\
     MATCH_MP_TAC le_mul \\
     CONJ_TAC
     >- (‘2 pow n = Normal (2 pow n)’
           by rw [extreal_of_num_def, extreal_pow_def] >> POP_ORW \\
         MATCH_MP_TAC le_div >> simp []) \\
     MATCH_MP_TAC MEASURE_POSITIVE >> art [] \\
     qmatch_abbrev_tac ‘s IN measurable_sets m’ \\
    ‘s = {x | &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} INTER m_space m’
       by (qunabbrev_tac ‘s’ >> SET_TAC []) >> POP_ORW \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE])
 >> DISCH_TAC
 >> Know ‘0 <= a’
 >- (qunabbrev_tac ‘a’ \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> simp [])
 >> DISCH_TAC
 >> Suff ‘a = PosInf’
 >- (Rewr' \\
     Suff ‘b <> NegInf’ >- METIS_TAC [add_infty] \\
     MATCH_MP_TAC pos_not_neginf >> art [])
 >> qunabbrev_tac ‘a’
 >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_EQ_POSINF >> simp []
 >> Q.EXISTS_TAC ‘k’
 >> simp [Abbr ‘g’]
 >> Suff ‘0 < &k / 2 pow n’ >- PROVE_TAC [mul_rposinf]
 >> ‘2 pow n = Normal (2 pow n)’
      by rw [extreal_of_num_def, extreal_pow_def] >> POP_ORW
 >> MATCH_MP_TAC lt_div
 >> simp [extreal_of_num_def]
QED

Theorem lemma_fn_seq_finite_measure1'[local] :
    !f k n. f IN borel_measurable borel /\ (!x. 0 <= f x) /\
            pos_fn_integral lborel (Normal o f) <> PosInf /\
            k < 4 ** n /\ k <> 0 ==>
            lambda {x | &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n} <> PosInf
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘nf = Normal o f’
 >> ‘!x. 0 <= nf x’ by rw [Abbr ‘nf’, o_DEF]
 >> Know ‘nf IN Borel_measurable borel’
 >- (qunabbrev_tac ‘nf’ \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [sigma_algebra_borel])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘nf’, ‘k’, ‘n’]
                    (ISPEC “lborel” lemma_fn_seq_finite_measure1))
 >> simp [lborel_def, space_lborel]
 >> ‘2 pow n <> (0 :real)’ by simp []
 >> ASM_SIMP_TAC std_ss
       [Abbr ‘nf’, extreal_div_eq, extreal_of_num_def, extreal_pow_def,
        extreal_add_eq, extreal_lt_eq, extreal_le_eq]
QED

Theorem lemma_fn_seq_finite_measure2[local] :
    !m f n. measure_space m /\ f IN Borel_measurable (measurable_space m) /\
           (!x. x IN m_space m ==> 0 <= f x) /\
            pos_fn_integral m f <> PosInf ==>
            measure m {x | x IN m_space m /\ 2 pow n <= f x} <> PosInf
Proof
    rpt STRIP_TAC
 >> ASSUME_TAC (Q.SPECL [‘m’, ‘f’, ‘n’] lemma_fn_seq_positive')
 >> ASSUME_TAC (Q.SPECL [‘m’, ‘f’, ‘n’] lemma_fn_seq_upper_bounded')
 >> Know ‘pos_fn_integral m (fn_seq m f n) <> PosInf’
 >- (REWRITE_TAC [lt_infty] \\
     Q_TAC (TRANS_TAC let_trans) ‘pos_fn_integral m f’ \\
     reverse CONJ_TAC >- art [GSYM lt_infty] \\
     MATCH_MP_TAC pos_fn_integral_mono >> simp [])
 >> Know ‘pos_fn_integral m (fn_seq m f n) = fn_seq_integral m f n’
 >- (MATCH_MP_TAC pos_fn_integral_fn_seq >> art [])
 >> simp [] >> DISCH_THEN K_TAC
 >> simp [fn_seq_integral_def]
 >> qmatch_abbrev_tac ‘a + b = PosInf’
 >> ‘sigma_algebra (measurable_space m)’ by PROVE_TAC [MEASURE_SPACE_SIGMA_ALGEBRA]
 >> Know ‘0 <= b’
 >- (qunabbrev_tac ‘b’ \\
     MATCH_MP_TAC le_mul >> simp [pow_pos_le])
 >> DISCH_TAC
 >> qunabbrev_tac ‘a’
 >> qmatch_abbrev_tac ‘SIGMA g _ + b = PosInf’
 >> qmatch_abbrev_tac ‘a + b = PosInf’
 >> Know ‘!i. 0 <= g i’
 >- (rw [Abbr ‘g’] \\
     MATCH_MP_TAC le_mul \\
     CONJ_TAC
     >- (‘2 pow n = Normal (2 pow n)’
           by rw [extreal_of_num_def, extreal_pow_def] >> POP_ORW \\
         MATCH_MP_TAC le_div >> simp []) \\
     MATCH_MP_TAC MEASURE_POSITIVE >> art [] \\
     qmatch_abbrev_tac ‘s IN measurable_sets m’ \\
    ‘s = {x | &i / 2 pow n <= f x /\ f x < (&i + 1) / 2 pow n} INTER m_space m’
       by (qunabbrev_tac ‘s’ >> SET_TAC []) >> POP_ORW \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL_MEASURE])
 >> DISCH_TAC
 >> Know ‘0 <= a’
 >- (qunabbrev_tac ‘a’ \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_POS >> simp [])
 >> DISCH_TAC
 >> Suff ‘b = PosInf’
 >- (Rewr' \\
     Suff ‘a <> NegInf’ >- METIS_TAC [add_infty] \\
     MATCH_MP_TAC pos_not_neginf >> art [])
 >> qunabbrev_tac ‘b’
 >> Suff ‘0 < 2 pow n’ >- PROVE_TAC [mul_rposinf]
 >> simp [pow_pos_lt]
QED

Theorem lemma_fn_seq_finite_measure2'[local] :
    !f n. f IN borel_measurable borel /\ (!x. 0 <= f x) /\
          pos_fn_integral lborel (Normal o f) <> PosInf ==>
          lambda {x | 2 pow n <= f x} <> PosInf
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘nf = Normal o f’
 >> ‘!x. 0 <= nf x’ by rw [Abbr ‘nf’, o_DEF]
 >> Know ‘nf IN Borel_measurable borel’
 >- (qunabbrev_tac ‘nf’ \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [sigma_algebra_borel])
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘nf’, ‘n’] (ISPEC “lborel” lemma_fn_seq_finite_measure2))
 >> simp [lborel_def, space_lborel]
 >> simp [Abbr ‘nf’, extreal_of_num_def, extreal_pow_def]
QED

Theorem finite_lmeasure_imp_integral_indicator :
    !s y. s IN measurable_sets lebesgue /\ lmeasure s = Normal y ==>
          indicator s integrable_on UNIV /\
          integral UNIV (indicator s) = y
Proof
    rpt GEN_TAC
 >> simp [lebesgue_def] >> STRIP_TAC
 >> qabbrev_tac ‘f = \n. indicator (s INTER line n)’
 >> ‘!n x. 0 <= f n x’ by rw [Abbr ‘f’, INDICATOR_POS]
 >> Know ‘!m n x. m <= n ==> f m x <= f n x’
 >- (rw [Abbr ‘f’] \\
     MATCH_MP_TAC INDICATOR_MONO \\
     Suff ‘line m SUBSET line n’ >- SET_TAC [] \\
     MATCH_MP_TAC LINE_MONO >> art [])
 >> DISCH_TAC
 >> ‘!n. f n integrable_on univ(:real)’ by PROVE_TAC [integrable_indicator_UNIV]
 >> Know ‘{Normal (integral (line n) (indicator s)) | n | T} =
          IMAGE Normal {integral (line n) (indicator s) | n | T}’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rw [] \\ (* 2 subgoals, same tactics *)
     Q.EXISTS_TAC ‘n’ >> REFL_TAC)
 >> DISCH_THEN (fs o wrap)
 >> qabbrev_tac ‘t = {integral (line n) (indicator s) | n | T}’
 >> Know ‘bounded t’
 >- (rw [bounded_def] \\
     Q.EXISTS_TAC ‘y’ >> rw [Abbr ‘t’] \\
     Q.PAT_X_ASSUM ‘sup _ = Normal y’ MP_TAC >> rw [sup_eq'] \\
     Q.PAT_X_ASSUM ‘!z. _ ==> z <= Normal y’
       (MP_TAC o Q.SPEC ‘Normal (integral (line n) (indicator s))’) \\
     impl_tac
     >- (Q.EXISTS_TAC ‘integral (line n) (indicator s)’ >> simp [] \\
         Q.EXISTS_TAC ‘n’ >> REFL_TAC) \\
     rw [] \\
     qmatch_abbrev_tac ‘abs x <= y’ \\
     Suff ‘abs x = x’ >- (Rewr' >> art []) \\
     rw [abs_refl, Abbr ‘x’] \\
     MATCH_MP_TAC INTEGRAL_POS >> simp [INDICATOR_POS])
 >> DISCH_TAC
 (* applying sup_image_normal *)
 >> Know ‘sup (IMAGE Normal t) = Normal (sup t)’
 >- (MATCH_MP_TAC sup_image_normal >> art [] \\
     rw [Abbr ‘t’, Once EXTENSION])
 >> DISCH_THEN (fs o wrap)
 >> MP_TAC (Q.SPECL [‘f’, ‘UNIV’]
                    BEPPO_LEVI_MONOTONE_CONVERGENCE_INCREASING) >> simp []
 >> impl_tac
 >- (Q.PAT_X_ASSUM ‘bounded t’ MP_TAC \\
     rw [Abbr ‘t’, bounded_def] \\
     Q.EXISTS_TAC ‘a’ \\
     simp [Abbr ‘f’, integral_indicator_UNIV])
 >> STRIP_TAC (* this asserts ‘g’, and ‘k’ (negligible) *)
 >> rename1 ‘negligible N’
 (* stage work *)
 >> qabbrev_tac ‘h = \n. integral UNIV (f n)’
 >> qabbrev_tac ‘r = integral univ(:real) g’
 (* applying mono_increasing_converges_to_sup *)
 >> Know ‘r = sup (IMAGE h UNIV)’
 >- (MATCH_MP_TAC mono_increasing_converges_to_sup \\
     simp [GSYM LIM_SEQUENTIALLY_SEQ] \\
     simp [mono_increasing_def, Abbr ‘h’] \\
     qx_genl_tac [‘i’, ‘j’] >> DISCH_TAC \\
     MATCH_MP_TAC INTEGRAL_MONO_LEMMA >> simp [])
 >> Know ‘IMAGE h UNIV = t’
 >- (rw [Abbr ‘t’, Once EXTENSION, Abbr ‘h’] \\
     simp [integral_indicator_UNIV, Abbr ‘f’])
 >> Rewr'
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘(h --> r) sequentially’ K_TAC
 (* applying mono_increasing_converges_to_sup again *)
 >> qabbrev_tac ‘f' = flip f’
 >> ‘!x. (\k. f k x) = f' x’ by rw [FUN_EQ_THM, Abbr ‘f'’]
 >> POP_ASSUM (fs o wrap)
 >> Know ‘!x. x NOTIN N ==> g x = sup (IMAGE (f' x) UNIV)’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC mono_increasing_converges_to_sup \\
     simp [GSYM LIM_SEQUENTIALLY_SEQ] \\
     simp [mono_increasing_def, Abbr ‘f'’])
 >> DISCH_TAC
 >> Know ‘!x. sup (IMAGE (f' x) univ(:num)) = indicator s x’
 >- (rw [Abbr ‘f'’, GSYM REAL_LE_ANTISYM]
     >- (MATCH_MP_TAC REAL_IMP_SUP_LE' >> simp [Abbr ‘f’] \\
         RW_TAC std_ss [] \\
         MATCH_MP_TAC INDICATOR_MONO >> SET_TAC []) \\
     qmatch_abbrev_tac ‘(r :real) <= sup p’ \\
  (* applying REAL_LE_SUP' *)
     Know ‘r <= sup p <=> !y. (!z. z IN p ==> z <= y) ==> r <= y’
     >- (MATCH_MP_TAC REAL_LE_SUP' \\
         CONJ_TAC >- rw [Once EXTENSION, Abbr ‘p’] \\
         Q.EXISTS_TAC ‘1’ \\
         rw [Abbr ‘p’, Abbr ‘f’] \\
         REWRITE_TAC [DROP_INDICATOR_LE_1]) >> Rewr' \\
     rw [Abbr ‘p’, Abbr ‘r’, Abbr ‘f’] \\
     Know ‘!n. indicator (s INTER line n) x <= y’
     >- (Q.X_GEN_TAC ‘n’ \\
         POP_ASSUM MATCH_MP_TAC \\
         Q.EXISTS_TAC ‘n’ >> REFL_TAC) >> DISCH_TAC \\
     STRIP_ASSUME_TAC (Q.SPEC ‘x’ REAL_IN_LINE) \\
     Suff ‘indicator s x = indicator (s INTER line n) x’ >- rw [] \\
     rw [indicator])
 >> DISCH_THEN (fs o wrap)
 >> Q.PAT_X_ASSUM ‘!x. x NOTIN N ==> (f' x --> indicator s x) sequentially’ K_TAC
 >> qunabbrev_tac ‘f'’
 (* stage work *)
 >> Suff ‘(indicator s has_integral y) UNIV’
 >- METIS_TAC [HAS_INTEGRAL_INTEGRABLE_INTEGRAL]
 >> Know ‘(indicator s has_integral y) UNIV <=> (g has_integral y) UNIV’
 >- (MATCH_MP_TAC HAS_INTEGRAL_SPIKE_EQ \\
     Q.EXISTS_TAC ‘N’ >> rw [])
 >> Rewr'
 >> simp [HAS_INTEGRAL_INTEGRABLE_INTEGRAL]
QED

Theorem finite_lmeasure_has_integral_indicator :
    !s y. s IN measurable_sets lebesgue /\ lmeasure s = Normal y ==>
          (indicator s has_integral y) UNIV
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [HAS_INTEGRAL_INTEGRABLE_INTEGRAL]
 >> MATCH_MP_TAC finite_lmeasure_imp_integral_indicator >> art []
QED

Theorem integrable_sets_iff_finite_measure :
    !s. s IN integrable_sets UNIV <=>
        s IN measurable_sets lebesgue /\ lmeasure s <> PosInf
Proof
    Q.X_GEN_TAC ‘s’ >> EQ_TAC
 >- (rpt STRIP_TAC >- METIS_TAC [integrable_sets_subset_lebesgue, SUBSET_DEF] \\
    ‘lmeasure s = Normal (integral univ(:real) (indicator s))’
       by PROVE_TAC [integrable_indicator_imp_lmeasure] >> fs [])
 >> rpt STRIP_TAC
 >> Know ‘lmeasure s <> NegInf’
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC MEASURE_POSITIVE \\
     simp [measure_space_lebesgue])
 >> DISCH_TAC
 >> ‘?r. lmeasure s = Normal r’ by METIS_TAC [extreal_cases]
 >> simp [integrable_sets_def]
 >> MATCH_MP_TAC (cj 1 finite_lmeasure_imp_integral_indicator)
 >> Q.EXISTS_TAC ‘r’ >> art []
QED

Theorem finite_lmeasure_has_integral_indicator_real :
    !s. s IN measurable_sets lebesgue /\ lmeasure s <> PosInf ==>
       (indicator s has_integral (real (lmeasure s))) UNIV
Proof
    rpt STRIP_TAC
 >> Know ‘lmeasure s <> NegInf’
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC MEASURE_POSITIVE \\
     simp [measure_space_lebesgue])
 >> DISCH_TAC
 >> ‘?r. lmeasure s = Normal r’ by METIS_TAC [extreal_cases]
 >> MP_TAC (Q.SPECL [‘s’, ‘r’] finite_lmeasure_has_integral_indicator) >> rw []
QED

(* |- !s. s IN integrable_sets univ(:real) ==>
          (indicator s has_integral real (lmeasure s)) univ(:real)
 *)
Theorem integrable_sets_has_integral_indicator_real =
        finite_lmeasure_has_integral_indicator_real
     |> REWRITE_RULE [GSYM integrable_sets_iff_finite_measure]

(* cf. HAS_INTEGRAL_SUM *)
Theorem HAS_INTEGRAL_SIGMA :
    !f i s t. FINITE t /\ (!a. a IN t ==> (f a has_integral i a) s) ==>
             ((\x. SIGMA (\a. f a x) t) has_integral SIGMA i t) s
Proof
    rpt STRIP_TAC
 >> simp [REAL_SUM_IMAGE_sum]
 >> MATCH_MP_TAC HAS_INTEGRAL_SUM >> art []
QED

Theorem real_fn_seq_has_integral :
    !f n. f IN borel_measurable borel /\ (!x. 0 <= f x) /\
          pos_fn_integral lborel (Normal o f) <> PosInf ==>
         (real_fn_seq lborel f n has_integral real_fn_seq_integral f n) UNIV
Proof
    RW_TAC std_ss [real_fn_seq_def, real_fn_seq_integral_def, space_lborel, IN_UNIV]
 >> HO_MATCH_MP_TAC HAS_INTEGRAL_ADD
 >> reverse CONJ_TAC
 >- (HO_MATCH_MP_TAC HAS_INTEGRAL_CMUL \\
     MP_TAC (Q.SPECL [‘f’, ‘n’] lemma_fn_seq_finite_measure2') >> rw [] \\
     qabbrev_tac ‘s = {x | 2 pow n <= f x}’ \\
    ‘(\x. indicator s x) = indicator s’ by rw [FUN_EQ_THM] >> POP_ORW \\
     Know ‘s IN subsets borel’
     >- (qunabbrev_tac ‘s’ \\
         MATCH_MP_TAC real_fn_seq_lemma2 >> art []) >> DISCH_TAC \\
     gs [lambda_eq_lebesgue] \\
     MATCH_MP_TAC finite_lmeasure_has_integral_indicator_real >> art [] \\
     METIS_TAC [SUBSET_DEF, lborel_subset_lebesgue, sets_lborel])
 (* stage work *)
 >> HO_MATCH_MP_TAC HAS_INTEGRAL_SIGMA
 >> SIMP_TAC std_ss [FINITE_COUNT, IN_COUNT]
 >> Q.X_GEN_TAC ‘j’ >> DISCH_TAC
 >> Cases_on ‘j = 0’ >- simp [HAS_INTEGRAL_0]
 >> HO_MATCH_MP_TAC HAS_INTEGRAL_CMUL
 >> qabbrev_tac ‘s = {x | &j / 2 pow n <= f x /\ f x < (&j + 1) / 2 pow n}’
 >> ‘(\x. indicator s x) = indicator s’ by rw [FUN_EQ_THM] >> POP_ORW
 >> Know ‘s IN subsets borel’
 >- (qunabbrev_tac ‘s’ \\
     MATCH_MP_TAC real_fn_seq_lemma1 >> art [])
 >> DISCH_TAC
 >> gs [lambda_eq_lebesgue]
 >> MATCH_MP_TAC finite_lmeasure_has_integral_indicator_real
 >> CONJ_TAC >- METIS_TAC [SUBSET_DEF, lborel_subset_lebesgue, sets_lborel]
 >> MP_TAC (Q.SPECL [‘f’, ‘j’, ‘n’] lemma_fn_seq_finite_measure1')
 >> simp [lambda_eq_lebesgue]
QED

Theorem real_fn_seq_integral_alt_fn_seq_integral :
    !f n. f IN borel_measurable borel /\ (!x. 0 <= f x) /\
          pos_fn_integral lborel (Normal o f) <> PosInf ==>
          real_fn_seq_integral f n = real (fn_seq_integral lborel (Normal o f) n)
Proof
    RW_TAC std_ss [real_fn_seq_integral_def, fn_seq_integral_def, space_lborel,
                   IN_UNIV]
 >> qabbrev_tac ‘nf = Normal o f’
 >> ‘!x. 0 <= nf x’ by rw [Abbr ‘nf’, o_DEF]
 >> Know ‘nf IN Borel_measurable borel’
 >- (qunabbrev_tac ‘nf’ \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [sigma_algebra_borel])
 >> DISCH_TAC
 >> ‘2 pow n = Normal (2 pow n)’
      by rw [extreal_of_num_def, extreal_pow_def] >> POP_ORW
 >> ‘2 pow n <> (0 :real)’ by simp []
 >> ASM_SIMP_TAC std_ss [extreal_of_num_def, extreal_div_eq, extreal_le_eq,
                         extreal_lt_eq, extreal_add_eq]
 >> qabbrev_tac ‘c = \k. (&k / 2 pow n) :real’
 >> ‘!k. 0 <= c k’ by rw [Abbr ‘c’]
 >> qabbrev_tac ‘A = \k. {x | &k / 2 pow n <= f x /\ f x < (&k + 1) / 2 pow n}’
 >> Know ‘!k. (A k) IN subsets borel’
 >- (RW_TAC std_ss [Abbr ‘A’, Abbr ‘c’] \\
     MATCH_MP_TAC real_fn_seq_lemma1 >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘B = {x | 2 pow n <= f x}’
 >> Know ‘B IN subsets borel’
 >- (qunabbrev_tac ‘B’ \\
     MATCH_MP_TAC real_fn_seq_lemma2 >> art [])
 >> DISCH_TAC
 >> qabbrev_tac ‘s = count (4 ** n)’
 >> ‘FINITE s’ by simp [Abbr ‘s’]
 >> ASM_SIMP_TAC std_ss []
 >> Know ‘SIGMA (\k. Normal (c k) * lambda (A k)) s =
          SIGMA (\k. Normal (c k) * Normal (lambda' (A k))) s’
 >- (irule EXTREAL_SUM_IMAGE_EQ >> art [] \\
     reverse CONJ_TAC
     >- (DISJ1_TAC \\
         Q.X_GEN_TAC ‘i’ >> simp [Abbr ‘s’] >> DISCH_TAC \\
         CONJ_TAC >> MATCH_MP_TAC pos_not_neginf (* 2 subgoals, same tactics *)
         >- (MATCH_MP_TAC le_mul \\
             CONJ_TAC >- simp [extreal_of_num_def] \\
             MATCH_MP_TAC MEASURE_POSITIVE \\
             simp [lborel_def, sets_lborel]) \\
         Cases_on ‘i = 0’ >- simp [Abbr ‘c’, extreal_mul_eq] \\
         MATCH_MP_TAC le_mul \\
         CONJ_TAC >- simp [extreal_of_num_def] \\
         Know ‘0 <= lambda (A i)’
         >- (MATCH_MP_TAC MEASURE_POSITIVE \\
             simp [lborel_def, sets_lborel]) >> DISCH_TAC \\
         Suff ‘Normal (real (lambda (A i))) = lambda (A i)’
         >- (Rewr' >> art []) \\
         MATCH_MP_TAC normal_real \\
         CONJ_TAC >- simp [pos_not_neginf] \\
         POP_ASSUM K_TAC \\
         SIMP_TAC std_ss [Abbr ‘A’] \\
         MATCH_MP_TAC lemma_fn_seq_finite_measure1' >> simp []) \\
     Q.X_GEN_TAC ‘i’ >> simp [Abbr ‘s’] >> DISCH_TAC \\
     Cases_on ‘i = 0’ >- simp [Abbr ‘c’, normal_0] \\
     Suff ‘Normal (lambda' (A i)) = lambda (A i)’ >- simp [] \\
     MATCH_MP_TAC normal_real \\
     Know ‘0 <= lambda (A i)’
     >- (MATCH_MP_TAC MEASURE_POSITIVE \\
         simp [lborel_def, sets_lborel]) >> DISCH_TAC \\
     CONJ_TAC >- simp [pos_not_neginf] \\
     POP_ASSUM K_TAC \\
     SIMP_TAC std_ss [Abbr ‘A’] \\
     MATCH_MP_TAC lemma_fn_seq_finite_measure1' >> simp [])
 >> Rewr'
 >> Know ‘lambda B = Normal (lambda' B)’
 >- (SYM_TAC >> MATCH_MP_TAC normal_real \\
     Know ‘0 <= lambda B’
     >- (MATCH_MP_TAC MEASURE_POSITIVE \\
         simp [lborel_def, sets_lborel]) >> DISCH_TAC \\
     CONJ_TAC >- simp [pos_not_neginf] \\
     SIMP_TAC std_ss [Abbr ‘B’] \\
     MATCH_MP_TAC lemma_fn_seq_finite_measure2' >> simp [])
 >> Rewr'
 >> simp [extreal_mul_eq]
 >> Know ‘SIGMA (\k. Normal (c k * lambda' (A k))) s =
          Normal (SIGMA (\k. c k * lambda' (A k)) s)’
 >- (HO_MATCH_MP_TAC EXTREAL_SUM_IMAGE_NORMAL >> art [])
 >> Rewr'
 >> simp [extreal_add_eq]
QED

Theorem fn_seq_integral_alt_real_fn_seq_integral :
    !f n. f IN borel_measurable borel /\ (!x. 0 <= f x) /\
          pos_fn_integral lborel (Normal o f) <> PosInf ==>
          fn_seq_integral lborel (Normal o f) n = Normal (real_fn_seq_integral f n)
Proof
    rw [real_fn_seq_integral_alt_fn_seq_integral]
 >> SYM_TAC
 >> MATCH_MP_TAC normal_real
 >> qabbrev_tac ‘nf = Normal o f’
 >> ‘!x. 0 <= nf x’ by rw [Abbr ‘nf’, o_DEF]
 >> Know ‘nf IN Borel_measurable borel’
 >- (qunabbrev_tac ‘nf’ \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [sigma_algebra_borel])
 >> DISCH_TAC
 >> CONJ_TAC
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC fn_seq_integral_positive \\
     simp [lborel_def, measure_space_lborel])
 (* applying pos_fn_integral_fn_seq *)
 >> Know ‘fn_seq_integral lborel nf n =
          pos_fn_integral lborel (fn_seq lborel nf n)’
 >- (SYM_TAC >> MATCH_MP_TAC pos_fn_integral_fn_seq \\
     simp [lborel_def, measure_space_lborel])
 >> Rewr'
 >> REWRITE_TAC [lt_infty]
 >> Q_TAC (TRANS_TAC let_trans) ‘pos_fn_integral lborel nf’
 >> reverse CONJ_TAC >- art [GSYM lt_infty]
 >> MATCH_MP_TAC pos_fn_integral_mono
 >> simp [space_lborel, lemma_fn_seq_positive, lemma_fn_seq_upper_bounded]
QED

Theorem fn_seq_integral_mono_increasing :
    !m f. measure_space m /\ f IN Borel_measurable (measurable_space m) /\
         (!x. x IN m_space m ==> 0 <= f x) ==>
          mono_increasing (fn_seq_integral m f)
Proof
    rpt STRIP_TAC
 >> simp [ext_mono_increasing_def]
 >> qx_genl_tac [‘i’, ‘j’] >> DISCH_TAC
 >> Know ‘!n. fn_seq_integral m f n = pos_fn_integral m (fn_seq m f n)’
 >- (Q.X_GEN_TAC ‘n’ \\
     SYM_TAC >> MATCH_MP_TAC pos_fn_integral_fn_seq >> art [])
 >> Rewr'
 >> MATCH_MP_TAC pos_fn_integral_mono
 >> simp [lemma_fn_seq_positive']
 >> rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘m’, ‘f’, ‘x’] lemma_fn_seq_mono_increasing)
 >> rw [ext_mono_increasing_def]
QED

Theorem real_fn_seq_integral_mono_increasing :
    !f. f IN borel_measurable borel /\ (!x. 0 <= f x) /\
        pos_fn_integral lborel (Normal o f) <> PosInf ==>
        mono_increasing (real_fn_seq_integral f)
Proof
    rw [mono_increasing_def]
 >> simp [real_fn_seq_integral_alt_fn_seq_integral]
 >> MATCH_MP_TAC le_real_imp
 >> qabbrev_tac ‘nf = Normal o f’
 >> ‘!x. 0 <= nf x’ by rw [Abbr ‘nf’, o_DEF]
 >> Know ‘nf IN Borel_measurable borel’
 >- (qunabbrev_tac ‘nf’ \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [sigma_algebra_borel])
 >> DISCH_TAC
 >> CONJ_TAC
 >- (MATCH_MP_TAC fn_seq_integral_positive >> simp [lborel_def])
 >> CONJ_TAC
 >- (MP_TAC (ISPECL [“lborel”, “nf :real -> extreal”]
                    fn_seq_integral_mono_increasing) \\
     rw [lborel_def, ext_mono_increasing_def])
 >> Know ‘fn_seq_integral lborel nf n =
          pos_fn_integral lborel (fn_seq lborel nf n)’
 >- (SYM_TAC >> MATCH_MP_TAC pos_fn_integral_fn_seq \\
     simp [lborel_def])
 >> Rewr'
 >> REWRITE_TAC [lt_infty]
 >> Q_TAC (TRANS_TAC let_trans) ‘pos_fn_integral lborel nf’
 >> simp [GSYM lt_infty]
 >> MATCH_MP_TAC pos_fn_integral_mono
 >> simp [lemma_fn_seq_positive, lemma_fn_seq_upper_bounded, space_lborel]
QED

(* NOTE: first we prove the equivalence for bounded positive functions *)
Theorem lebesgue_eq_gauge_integral_positive_bounded :
    !f. f IN borel_measurable borel /\
       (!x. 0 <= f x) /\ bounded (IMAGE f UNIV) /\
        pos_fn_integral lborel (Normal o f) <> PosInf ==>
        f integrable_on UNIV /\
        pos_fn_integral lborel (Normal o f) = Normal (integral UNIV f)
Proof
    Q.X_GEN_TAC ‘f’
 >> simp [bounded_alt] >> STRIP_TAC
 >> qabbrev_tac ‘nf = Normal o f’
 >> ‘!x. 0 <= nf x’ by rw [Abbr ‘nf’, o_DEF]
 >> Know ‘nf IN Borel_measurable borel’
 >- (qunabbrev_tac ‘nf’ \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [sigma_algebra_borel])
 >> DISCH_TAC
 (* applying integral_sequence *)
 >> MP_TAC (ISPECL [“lborel”, “nf :real -> extreal”] integral_sequence)
 >> impl_tac >- simp [lborel_def, space_lborel]
 >> Rewr'
 >> qabbrev_tac ‘fi = fn_seq lborel nf’
 >> Know ‘f = \x. real (sup (IMAGE (\n. fi n x) UNIV))’
 >- (rw [FUN_EQ_THM, Abbr ‘fi’] \\
     MP_TAC (ISPECL [“lborel”, “nf :real -> extreal”] lemma_fn_seq_sup) \\
     rw [lborel_def, space_lborel] \\
     simp [Abbr ‘nf’, o_DEF, real_normal])
 >> Rewr'
 >> qunabbrev_tac ‘fi’
 >> Know ‘!i. pos_fn_integral lborel (fn_seq lborel nf i) =
              fn_seq_integral lborel nf i’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC pos_fn_integral_fn_seq >> rw [lborel_def])
 >> DISCH_TAC
 >> Know ‘!i. fn_seq_integral lborel nf i <= pos_fn_integral lborel nf’
 >- (Q.X_GEN_TAC ‘i’ \\
     POP_ASSUM (simp o wrap o GSYM) \\
     MATCH_MP_TAC pos_fn_integral_mono \\
     simp [space_lborel, lemma_fn_seq_positive] \\
     Q.X_GEN_TAC ‘x’ \\
     MATCH_MP_TAC lemma_fn_seq_upper_bounded \\
     rw [Abbr ‘nf’, o_DEF])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘!i. pos_fn_integral lborel (fn_seq lborel nf i) = _’
      (REWRITE_TAC o wrap)
 >> qabbrev_tac ‘fn = \n x. real (fn_seq lborel nf n x)’
 (* applying sup_normal (NOTE: “bounded (IMAGE f UNIV)” is used here) *)
 >> qabbrev_tac ‘s = \x. IMAGE (\n. fn_seq lborel nf n x) UNIV’ >> simp []
 >> Know ‘!x. sup (s x) = Normal (sup (s x o Normal))’
 >- (rw [Once EQ_SYM_EQ] \\
     MATCH_MP_TAC sup_normal \\
     Q.EXISTS_TAC ‘a’ >> rw [abs_bounds] (* 2 subgoals *)
     >- (rw [Abbr ‘s’, le_sup'] \\
         Q_TAC (TRANS_TAC le_trans) ‘0’ \\
         CONJ_TAC >- simp [extreal_of_num_def, extreal_ainv_def] \\
         Q_TAC (TRANS_TAC le_trans) ‘fn_seq lborel nf 0 x’ \\
         reverse CONJ_TAC
         >- (POP_ASSUM MATCH_MP_TAC \\
             Q.EXISTS_TAC ‘0’ >> art []) \\
         MATCH_MP_TAC lemma_fn_seq_positive >> art []) \\
     rw [Abbr ‘s’, sup_le'] \\
     Q_TAC (TRANS_TAC le_trans) ‘nf x’ \\
     CONJ_TAC >- (MATCH_MP_TAC lemma_fn_seq_upper_bounded >> art []) \\
     rw [Abbr ‘nf’, o_DEF] \\
     Suff ‘abs (f x) <= a’ >- simp [ABS_BOUNDS] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘x’ >> art [])
 >> Rewr'
 >> simp [real_normal, Abbr ‘s’]
 >> Know ‘!x. IMAGE (\n. fn_seq lborel nf n x) UNIV o Normal =
              IMAGE (\n. fn n x) UNIV’
 >- (Q.X_GEN_TAC ‘y’ >> rw [Once EXTENSION, o_DEF] \\
     EQ_TAC >> rw [Abbr ‘fn’]
     >- (Q.EXISTS_TAC ‘n’ \\
         POP_ASSUM (simp o wrap o SYM)) \\
     Q.EXISTS_TAC ‘n’ \\
     MATCH_MP_TAC normal_real \\
     CONJ_TAC
     >- (MATCH_MP_TAC pos_not_neginf \\
         MATCH_MP_TAC lemma_fn_seq_positive >> art []) \\
     REWRITE_TAC [lt_infty] \\
     Q_TAC (TRANS_TAC let_trans) ‘nf y’ \\
     CONJ_TAC >- (MATCH_MP_TAC lemma_fn_seq_upper_bounded >> art []) \\
     simp [Abbr ‘nf’, o_DEF])
 >> Rewr'
 >> MP_TAC (Q.SPECL [‘fn’, ‘UNIV’] BEPPO_LEVI_MONOTONE_CONVERGENCE_INCREASING)
 >> simp []
 >> ‘fn = (\n x. real_fn_seq lborel f n x)’
       by rw [Abbr ‘fn’, Abbr ‘nf’, fn_seq_alt_real_fn_seq, FUN_EQ_THM]
 >> POP_ORW
 >> simp [Abbr ‘fn’]
 >> ‘!k. (\x. real_fn_seq lborel f k x) = real_fn_seq lborel f k’
      by rw [FUN_EQ_THM] >> POP_ORW
 (* applying lemma_real_fn_seq_mono_increasing *)
 >> Know ‘!k x. real_fn_seq lborel f k x <= real_fn_seq lborel f (SUC k) x’
 >- (rpt GEN_TAC \\
     MP_TAC (Q.SPECL [‘f’, ‘x’]
                     (Q.ISPEC ‘lborel’ lemma_real_fn_seq_mono_increasing)) \\
     rw [mono_increasing_def])
 >> Rewr
 (* applying real_fn_seq_has_integral *)
 >> Know ‘!n. (real_fn_seq lborel f n has_integral real_fn_seq_integral f n)
                univ(:real)’
 >- (Q.X_GEN_TAC ‘n’ \\
     MATCH_MP_TAC real_fn_seq_has_integral >> simp [])
 >> simp [HAS_INTEGRAL_INTEGRABLE_INTEGRAL, FORALL_AND_THM]
 >> STRIP_TAC
 (* applying lemma_real_fn_seq_upper_bounded *)
 >> impl_tac (* bounded *)
 >- (rw [bounded_def] \\
     Know ‘0 <= pos_fn_integral lborel nf’
     >- (MATCH_MP_TAC pos_fn_integral_pos >> simp [lborel_def, space_lborel]) \\
     DISCH_TAC \\
    ‘pos_fn_integral lborel nf <> NegInf’ by simp [pos_not_neginf] \\
    ‘?r. pos_fn_integral lborel nf = Normal r’ by METIS_TAC [extreal_cases] \\
     Q.EXISTS_TAC ‘r’ >> rw [] \\
     Know ‘abs (real_fn_seq_integral f k) = real_fn_seq_integral f k’
     >- simp [ABS_REFL, real_fn_seq_integral_positive] >> Rewr' \\
     Know ‘real_fn_seq_integral f k =
           real (fn_seq_integral lborel (Normal o f) k)’
     >- (MATCH_MP_TAC real_fn_seq_integral_alt_fn_seq_integral \\
         simp []) >> Rewr' \\
    ‘r = real (pos_fn_integral lborel nf)’ by simp [real_normal] >> POP_ORW \\
     POP_ASSUM K_TAC >> simp [] \\
     MATCH_MP_TAC le_real_imp >> simp [] \\
     MATCH_MP_TAC fn_seq_integral_positive >> simp [lborel_def])
 >> STRIP_TAC (* this asserts g and k (negligible) *)
 >> rename1 ‘negligible E’
 >> ‘(\k. real_fn_seq_integral f k) = real_fn_seq_integral f’ by rw [FUN_EQ_THM]
 >> POP_ASSUM (fs o wrap)
 >> qabbrev_tac ‘h = flip (real_fn_seq lborel f)’
 >> ‘!x. (\k. real_fn_seq lborel f k x) = h x’ by rw [Abbr ‘h’, FUN_EQ_THM]
 >> POP_ASSUM (fs o wrap)
 (* applying mono_increasing_converges_to_sup *)
 >> Know ‘!x. x NOTIN E ==> g x = sup (IMAGE (h x) UNIV)’
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC mono_increasing_converges_to_sup \\
     simp [GSYM LIM_SEQUENTIALLY_SEQ] \\
     simp [Abbr ‘h’, combinTheory.C_DEF, lemma_real_fn_seq_mono_increasing])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘!x. x NOTIN E ==> (h x --> g x) sequentially’ K_TAC
 >> Know ‘integral univ(:real) (\x. sup (IMAGE (h x) univ(:num))) =
          integral univ(:real) g’
 >- (MATCH_MP_TAC INTEGRAL_SPIKE \\
     Q.EXISTS_TAC ‘E’ >> simp [])
 >> Rewr'
 >> CONJ_TAC
 >- (irule INTEGRABLE_SPIKE \\
     qexistsl_tac [‘g’, ‘E’] >> simp [])
 >> Know ‘!n. fn_seq_integral lborel nf n = Normal (real_fn_seq_integral f n)’
 >- (rw [Abbr ‘nf’] \\
     MATCH_MP_TAC fn_seq_integral_alt_real_fn_seq_integral >> art [])
 >> Rewr'
 (* applying sup_image_normal, again *)
 >> Know ‘IMAGE (\i. Normal (real_fn_seq_integral f i)) UNIV =
          IMAGE Normal {real_fn_seq_integral f n | n | T}’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ Q.EXISTS_TAC ‘i’ >> REFL_TAC,
       Q.EXISTS_TAC ‘n’ >> REFL_TAC ])
 >> Rewr'
 >> qmatch_abbrev_tac ‘sup (IMAGE Normal s) = Normal r’
 >> Know ‘sup (IMAGE Normal s) = Normal (sup s)’
 >- (MATCH_MP_TAC sup_image_normal \\
     CONJ_TAC >- rw [Abbr ‘s’, Once EXTENSION] \\
     rw [bounded_def, Abbr ‘s’] \\
     Q.EXISTS_TAC ‘real (pos_fn_integral lborel nf)’ >> rw [] \\
     Know ‘abs (real_fn_seq_integral f n) = real_fn_seq_integral f n’
     >- rw [ABS_REFL, real_fn_seq_integral_positive] >> Rewr' \\
     Know ‘real_fn_seq_integral f n = real (fn_seq_integral lborel nf n)’
     >- (qunabbrev_tac ‘nf’ \\
         MATCH_MP_TAC real_fn_seq_integral_alt_fn_seq_integral >> simp []) \\
     Rewr' \\
     MATCH_MP_TAC le_real_imp >> art [] \\
     MATCH_MP_TAC fn_seq_integral_positive >> simp [lborel_def])
 >> Rewr'
 >> REWRITE_TAC [extreal_11]
 (* applying mono_increasing_converges_to_sup, yet again *)
 >> SYM_TAC >> simp [Abbr ‘s’]
 >> ‘{real_fn_seq_integral f n | n | T} = IMAGE (real_fn_seq_integral f) UNIV’
      by rw [Once EXTENSION] >> POP_ORW
 >> MATCH_MP_TAC mono_increasing_converges_to_sup
 >> simp [GSYM LIM_SEQUENTIALLY_SEQ, real_fn_seq_integral_mono_increasing]
QED

(* NOTE: removed “bounded (IMAGE f UNIV)” from the above result *)
Theorem lebesgue_eq_gauge_integral_positive :
    !f. f IN borel_measurable borel /\ (!x. 0 <= f x) /\
        pos_fn_integral lborel (Normal o f) <> PosInf ==>
        f integrable_on UNIV /\
        pos_fn_integral lborel (Normal o f) = Normal (integral UNIV f)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> qabbrev_tac ‘nf = Normal o f’
 >> ‘!x. 0 <= nf x’ by rw [Abbr ‘nf’, o_DEF]
 >> Know ‘nf IN Borel_measurable borel’
 >- (qunabbrev_tac ‘nf’ \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [sigma_algebra_borel])
 >> DISCH_TAC
 >> qabbrev_tac ‘g = \n x. min (f x) &n’
 >> ‘!n x. 0 <= g n x’ by rw [Abbr ‘g’, REAL_LE_MIN]
 >> Know ‘!n. bounded (IMAGE (g n) UNIV)’
 >- (rw [bounded_def] \\
     Q.EXISTS_TAC ‘&n’ \\
     Q.X_GEN_TAC ‘x’ \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘y’ STRIP_ASSUME_TAC) >> POP_ORW \\
     simp [ABS_REDUCE] \\
     simp [Abbr ‘g’, REAL_MIN_LE])
 >> DISCH_TAC
 >> Know ‘!n. g n IN borel_measurable borel’
 >- (rw [Abbr ‘g’] \\
     HO_MATCH_MP_TAC in_borel_measurable_min >> simp [sigma_algebra_borel] \\
     MATCH_MP_TAC in_borel_measurable_const \\
     Q.EXISTS_TAC ‘&n’ >> simp [sigma_algebra_borel])
 >> DISCH_TAC
 >> ‘!n x. g n x <= f x’ by rw [Abbr ‘g’, REAL_MIN_LE]
 >> qabbrev_tac ‘ng = \n. Normal o g n’
 >> ‘!n x. 0 <= ng n x’ by rw [Abbr ‘ng’, o_DEF, extreal_of_num_def]
 >> ‘!n x. ng n x <= nf x’ by rw [Abbr ‘ng’, Abbr ‘nf’, REAL_MIN_LE]
 >> Know ‘!n. ng n IN Borel_measurable borel’
 >- (rw [Abbr ‘ng’] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
     simp [sigma_algebra_borel])
 >> DISCH_TAC
 >> Know ‘!x. mono_increasing (\i. ng i x)’
 >- (Q.X_GEN_TAC ‘x’ \\
     simp [ext_mono_increasing_def, Abbr ‘ng’, o_DEF] \\
     qx_genl_tac [‘i’, ‘j’] >> rw [Abbr ‘g’] \\
     MATCH_MP_TAC REAL_IMP_MIN_LE2 >> simp [])
 >> DISCH_TAC
 >> Know ‘!n. pos_fn_integral lborel (ng n) <> PosInf’
 >- (rw [lt_infty] \\
     Q_TAC (TRANS_TAC let_trans) ‘pos_fn_integral lborel nf’ \\
     simp [GSYM lt_infty] \\
     MATCH_MP_TAC pos_fn_integral_mono >> simp [])
 >> DISCH_TAC
 (* applying lebesgue_eq_gauge_integral_positive_bounded *)
 >> Know ‘!n. g n integrable_on UNIV /\
              pos_fn_integral lborel (ng n) = Normal (integral univ(:real) (g n))’
 >- (Q.X_GEN_TAC ‘n’ >> fs [Abbr ‘ng’] \\
     MATCH_MP_TAC lebesgue_eq_gauge_integral_positive_bounded >> simp [])
 >> DISCH_THEN (STRIP_ASSUME_TAC o SRULE [FORALL_AND_THM])
 (* applying lebesgue_monotone_convergence *)
 >> Know ‘pos_fn_integral lborel nf =
          sup (IMAGE (\i. pos_fn_integral lborel (ng i)) UNIV)’
 >- (MATCH_MP_TAC lebesgue_monotone_convergence \\
     simp [lborel_def, space_lborel] \\
     NTAC 5 (POP_ASSUM K_TAC) (* irrelevant assumptions *) \\
     Q.X_GEN_TAC ‘x’ >> rw [sup_eq'] >- art [] \\
     Know ‘!n. ng n x <= y’
     >- (Q.X_GEN_TAC ‘n’ >> POP_ASSUM MATCH_MP_TAC \\
         Q.EXISTS_TAC ‘n’ >> REFL_TAC) \\
     POP_ASSUM K_TAC \\
     simp [Abbr ‘ng’, Abbr ‘nf’, o_DEF, Abbr ‘g’] \\
     Cases_on ‘y = PosInf’ >- simp [] \\
     Cases_on ‘y = NegInf’ >- simp [] \\
    ‘?r. y = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     simp [] \\
     CCONTR_TAC >> fs [REAL_NOT_LE] \\
     STRIP_ASSUME_TAC (Q.SPEC ‘r’ SIMP_REAL_ARCH) \\
     Q.PAT_X_ASSUM ‘!n. min (f x) (&n) <= r’ (MP_TAC o Q.SPEC ‘SUC n’) \\
     simp [REAL_LT_MIN, REAL_NOT_LE] \\
     Q_TAC (TRANS_TAC REAL_LET_TRANS) ‘&n’ >> simp [])
 >> Rewr'
 (* applying MONOTONE_CONVERGENCE_INCREASING *)
 >> MP_TAC (Q.SPECL [‘g’, ‘f’, ‘UNIV’] MONOTONE_CONVERGENCE_INCREASING) >> simp []
 >> impl_tac
 >- (CONJ_TAC
     >- (qx_genl_tac [‘n’, ‘x’] \\
         Q.PAT_X_ASSUM ‘!x. mono_increasing (\i. ng i x)’ (MP_TAC o Q.SPEC ‘x’) \\
         rw [ext_mono_increasing_def, Abbr ‘ng’, o_DEF]) \\
     reverse CONJ_TAC
     >- (rw [bounded_def] \\
         Q.EXISTS_TAC ‘real (pos_fn_integral lborel nf)’ >> rw [] \\
         Know ‘abs (integral univ(:real) (g k)) = integral univ(:real) (g k)’
         >- (REWRITE_TAC [ABS_REFL] \\
             MATCH_MP_TAC INTEGRAL_POS >> rw []) >> Rewr' \\
         ONCE_REWRITE_TAC [GSYM extreal_le_eq] \\
         Know ‘Normal (real (pos_fn_integral lborel nf)) =
               pos_fn_integral lborel nf’
         >- (MATCH_MP_TAC normal_real >> art [] \\
             MATCH_MP_TAC pos_not_neginf \\
             MATCH_MP_TAC pos_fn_integral_pos \\
             simp [measure_space_lborel]) >> Rewr' \\
         POP_ASSUM (REWRITE_TAC o wrap o GSYM) \\
         MATCH_MP_TAC pos_fn_integral_mono >> simp [space_lborel]) \\
     rw [LIM_SEQUENTIALLY, dist, Abbr ‘g’] \\
     STRIP_ASSUME_TAC (Q.SPEC ‘f (x :real)’ SIMP_REAL_ARCH) \\
     Q.EXISTS_TAC ‘n’ >> rpt STRIP_TAC \\
     Know ‘min (f x) (&k) = f x’
     >- (MATCH_MP_TAC (cj 1 REAL_MIN_REDUCE) >> DISJ1_TAC \\
         Q_TAC (TRANS_TAC REAL_LE_TRANS) ‘&n’ >> simp []) >> Rewr' \\
     simp [])
 >> RW_TAC std_ss []
 (* applying sup_image_normal *)
 >> Know ‘IMAGE (\i. Normal (integral UNIV (g i))) UNIV =
          IMAGE Normal {integral UNIV (g n) | n | T}’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ Q.EXISTS_TAC ‘i’ >> REFL_TAC,
       Q.EXISTS_TAC ‘n’ >> REFL_TAC ])
 >> Rewr'
 (* applying sup_image_normal *)
 >> qmatch_abbrev_tac ‘sup (IMAGE Normal s) = Normal r’
 >> Know ‘sup (IMAGE Normal s) = Normal (sup s)’
 >- (MATCH_MP_TAC sup_image_normal \\
     CONJ_TAC >- rw [Abbr ‘s’, Once EXTENSION] \\
     rw [bounded_def, Abbr ‘s’] \\
     Q.EXISTS_TAC ‘integral UNIV f’ >> rw [] \\
     Know ‘abs (integral UNIV (g n)) = integral UNIV (g n)’
     >- (REWRITE_TAC [ABS_REFL] \\
         MATCH_MP_TAC INTEGRAL_POS >> simp []) >> Rewr' \\
     qunabbrev_tac ‘r’ \\
     MATCH_MP_TAC INTEGRAL_MONO_LEMMA >> simp [])
 >> Rewr'
 >> REWRITE_TAC [extreal_11]
 (* applying mono_increasing_converges_to_sup *)
 >> SYM_TAC >> simp [Abbr ‘s’]
 >> ‘{integral UNIV (g n) | n | T} = IMAGE (\n. integral UNIV (g n)) UNIV’
      by rw [Once EXTENSION] >> POP_ORW
 >> MATCH_MP_TAC mono_increasing_converges_to_sup
 >> simp [GSYM LIM_SEQUENTIALLY_SEQ]
 (* final goal (easy) *)
 >> simp [mono_increasing_def]
 >> qx_genl_tac [‘i’, ‘j’] >> DISCH_TAC
 >> MATCH_MP_TAC INTEGRAL_MONO_LEMMA >> rw []
 >> Q.PAT_X_ASSUM ‘!x. mono_increasing (\i. ng i x)’ (MP_TAC o Q.SPEC ‘x’)
 >> rw [ext_mono_increasing_def, o_DEF, Abbr ‘ng’]
QED

Definition real_fn_plus_def :
    real_fn_plus f x = max (0 :real) (f x)
End

Definition real_fn_minus_def :
    real_fn_minus f x = -min (0 :real) (f x)
End

Overload TC                = “real_fn_plus”
Overload fn_plus[inferior] = “real_fn_plus”
Overload fn_minus          = “real_fn_minus”

Theorem real_fn_plus_pos :
    !f x. 0 <= real_fn_plus f x
Proof
    rw [real_fn_plus_def, REAL_LE_MAX]
QED

Theorem real_fn_minus_pos :
    !f x. 0 <= real_fn_minus f x
Proof
    rw [real_fn_minus_def, REAL_MIN_LE]
QED

(* cf. extrealTheory.FN_DECOMP *)
Theorem fn_decompose :
    !(f :real -> real) x. f x = fn_plus f x - fn_minus f x
Proof
    RW_TAC real_ss [real_fn_plus_def, real_fn_minus_def]
 >> Cases_on ‘0 <= f x’
 >- simp [REAL_MAX_REDUCE, REAL_MIN_REDUCE]
 >> fs [REAL_NOT_LE]
 >> simp [REAL_MAX_REDUCE, REAL_MIN_REDUCE]
QED

Theorem fn_plus_normal :
    !f. fn_plus (Normal o f) = Normal o fn_plus f
Proof
    rw [FUN_EQ_THM, fn_plus, o_DEF, real_fn_plus_def]
 >> simp [extreal_of_num_def, extreal_max_eq]
QED

Theorem fn_minus_normal :
    !f. fn_minus (Normal o f) = Normal o fn_minus f
Proof
    rw [FUN_EQ_THM, fn_minus, o_DEF, real_fn_minus_def]
 >> simp [extreal_of_num_def, extreal_min_eq, extreal_ainv_def]
QED

Theorem lebesgue_eq_gauge_integral :
    !f. integrable lborel (Normal o f) ==>
        f absolutely_integrable_on UNIV /\
        integral lborel (Normal o f) = Normal (integral UNIV f)
Proof
    Q.X_GEN_TAC ‘f’
 >> simp [integrable_def, lebesgueTheory.integral_def,
          fn_plus_normal, fn_minus_normal, lborel_def]
 >> STRIP_TAC
 >> Know ‘real o (Normal o f) IN borel_measurable borel’
 >- (MATCH_MP_TAC in_borel_measurable_from_Borel \\
     simp [sigma_algebra_borel])
 >> ‘real o Normal o f = f’ by rw [FUN_EQ_THM, o_DEF, real_normal] >> POP_ORW
 >> DISCH_TAC
 >> Know ‘f absolutely_integrable_on UNIV <=>
          (\x. fn_plus f x - fn_minus f x) absolutely_integrable_on UNIV’
 >- (Suff ‘(\x. fn_plus f x - fn_minus f x) = f’ >- Rewr \\
     rw [FUN_EQ_THM, GSYM fn_decompose])
 >> Rewr'
 >> Know ‘integral UNIV f = integral UNIV (\x. fn_plus f x - fn_minus f x)’
 >- (Suff ‘(\x. fn_plus f x - fn_minus f x) = f’ >- Rewr \\
     rw [FUN_EQ_THM, GSYM fn_decompose])
 >> Rewr'
 >> Know ‘fn_plus f IN borel_measurable borel’
 >- (‘fn_plus f = \x. max 0 (f x)’ by rw [FUN_EQ_THM, real_fn_plus_def] \\
     POP_ORW \\
     HO_MATCH_MP_TAC in_borel_measurable_max >> simp [sigma_algebra_borel] \\
     MATCH_MP_TAC in_borel_measurable_const \\
     Q.EXISTS_TAC ‘0’ >> simp [sigma_algebra_borel])
 >> DISCH_TAC
 >> Know ‘fn_minus f IN borel_measurable borel’
 >- (‘fn_minus f = \x. -min 0 (f x)’ by rw [FUN_EQ_THM, real_fn_minus_def] \\
     POP_ORW \\
     HO_MATCH_MP_TAC in_borel_measurable_ainv >> simp [sigma_algebra_borel] \\
     HO_MATCH_MP_TAC in_borel_measurable_min >> simp [sigma_algebra_borel] \\
     MATCH_MP_TAC in_borel_measurable_const \\
     Q.EXISTS_TAC ‘0’ >> simp [sigma_algebra_borel])
 >> DISCH_TAC
 >> qabbrev_tac ‘f1 = fn_plus f’
 >> qabbrev_tac ‘f2 = fn_minus f’
 >> ‘!x. 0 <= f1 x’ by rw [Abbr ‘f1’, real_fn_plus_pos]
 >> ‘!x. 0 <= f2 x’ by rw [Abbr ‘f2’, real_fn_minus_pos]
 (* applying lebesgue_eq_gauge_integral_positive, twice *)
 >> MP_TAC (Q.SPEC ‘f1’ lebesgue_eq_gauge_integral_positive)
 >> simp [] >> STRIP_TAC
 >> MP_TAC (Q.SPEC ‘f2’ lebesgue_eq_gauge_integral_positive)
 >> simp [] >> STRIP_TAC
 >> simp [extreal_sub_eq]
 >> reverse CONJ_TAC >- (SYM_TAC >> MATCH_MP_TAC INTEGRAL_SUB >> art [])
 >> MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB
 >> CONJ_TAC (* 2 subgoals, same tactics *)
 >> MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE >> simp []
QED

(* END *)

(* References:

  [1] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
  [2] Bartle, R.G.: A Modern Theory of Integration. American Mathematical Soc. (2001).
  [5] Wikipedia: https://en.wikipedia.org/wiki/Henri_Lebesgue
  [7] Swartz, C.W., Kurtz, D.S.: Theories Of Integration: The Integrals Of Riemann,
      Lebesgue, Henstock-kurzweil, And Mcshane (2nd Edition).
      World Scientific Publishing Company (2011).
 *)
