(* ========================================================================= *)
(*   Probability Density Function Theory (normal_rvTheory)                   *)
(*                                                                           *)
(*        (c) Copyright 2015,                                                *)
(*                       Muhammad Qasim,                                     *)
(*                       Osman Hasan,                                        *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*            Contact:  <m_qasi@ece.concordia.ca>                            *)
(*                                                                           *)
(*   Enriched by Chun TIAN (The Australian National University, 2024)        *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open combinTheory arithmeticTheory numLib logrootTheory hurdUtils pred_setLib
     pred_setTheory realTheory realLib seqTheory transcTheory real_sigmaTheory
     iterateTheory topologyTheory real_topologyTheory derivativeTheory;

open util_probTheory sigma_algebraTheory extrealTheory real_borelTheory
     measureTheory borelTheory lebesgueTheory martingaleTheory
     probabilityTheory;

val _ = new_theory "distribution"; (* was: "normal_rv" *)

(* See, e.g., [3, p.117] or [4, p.375]

   NOTE: In some textbooks, g is said to be in "C_B" (the class of bounded
   continuous functions).
 *)
Definition weak_converge_def :
    weak_converge (fi :num -> extreal measure) (f :extreal measure) =
    !(g :real -> real).
        bounded (IMAGE g UNIV) /\ g continuous_on UNIV ==>
        ((\n. integral (space Borel,subsets Borel,fi n) (Normal o g o real)) -->
          integral (space Borel,subsets Borel,f) (Normal o g o real)) sequentially
End

Overload "-->" = “weak_converge”

Theorem real_in_borel_measurable :
    real IN borel_measurable Borel
Proof
    rw [in_borel_measurable_le, SIGMA_ALGEBRA_BOREL, SPACE_BOREL, IN_FUNSET]
 >> Cases_on ‘0 <= a’
 >- (Know ‘{w | real w <= a} = {x | x <= Normal a} UNION {PosInf}’
     >- (rw [Once EXTENSION] \\
         Cases_on ‘x = PosInf’ >- rw [real_def] \\
         Cases_on ‘x = NegInf’ >- rw [real_def] \\
        ‘?r. x = Normal r’ by METIS_TAC [extreal_cases] >> rw []) >> Rewr' \\
     MATCH_MP_TAC SIGMA_ALGEBRA_UNION \\
     rw [SIGMA_ALGEBRA_BOREL, BOREL_MEASURABLE_SETS_RC])
 >> fs [GSYM real_lt]
 (* stage work *)
 >> Know ‘{w | real w <= a} = {x | x <= Normal a} DIFF {NegInf}’
 >- (rw [Once EXTENSION] \\
     Cases_on ‘x = PosInf’ >- rw [real_def, GSYM real_lt] \\
     Cases_on ‘x = NegInf’ >- rw [real_def, GSYM real_lt] \\
    ‘?r. x = Normal r’ by METIS_TAC [extreal_cases] >> rw [])
 >> Rewr'
 >> MATCH_MP_TAC SIGMA_ALGEBRA_DIFF
 >> rw [SIGMA_ALGEBRA_BOREL, BOREL_MEASURABLE_SETS_RC]
QED

(* some shared tactics for the next two theorems *)
val converge_in_dist_tactic1 =
    qabbrev_tac ‘f = Normal o g o real’ \\
    Know ‘!n. integral (space Borel,subsets Borel,distr p (X n)) f = integral p (f o X n)’
    >- (Q.X_GEN_TAC ‘n’ \\
        MATCH_MP_TAC (cj 1 integral_distr) \\
        simp [SIGMA_ALGEBRA_BOREL, Abbr ‘f’] \\
        MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
        simp [SIGMA_ALGEBRA_BOREL] \\
       ‘g IN borel_measurable borel’ by PROVE_TAC [in_borel_measurable_continuous_on] \\
        MATCH_MP_TAC MEASURABLE_COMP \\
        Q.EXISTS_TAC ‘borel’ >> rw [real_in_borel_measurable]) >> Rewr' \\
    Know ‘!n. integral (space Borel,subsets Borel,distr p Y) f = integral p (f o Y)’
    >- (MATCH_MP_TAC (cj 1 integral_distr) \\
        simp [SIGMA_ALGEBRA_BOREL, Abbr ‘f’] \\
        MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
        simp [SIGMA_ALGEBRA_BOREL] \\
       ‘g IN borel_measurable borel’ by PROVE_TAC [in_borel_measurable_continuous_on] \\
        MATCH_MP_TAC MEASURABLE_COMP \\
        Q.EXISTS_TAC ‘borel’ >> rw [real_in_borel_measurable]) >> Rewr' \\
    simp [Abbr ‘f’];

val converge_in_dist_tactic2 =
    qabbrev_tac ‘g = Normal o f o real’ \\
   ‘!n. Normal o f o real o X n = g o X n’ by METIS_TAC [o_ASSOC] >> POP_ORW \\
   ‘Normal o f o real o Y = g o Y’ by METIS_TAC [o_ASSOC] >> POP_ORW \\
    Q.PAT_X_ASSUM ‘!g. bounded (IMAGE g UNIV) /\ _ ==> _’ (MP_TAC o Q.SPEC ‘f’) \\
    simp [] \\
    Know ‘!n. integral (space Borel,subsets Borel,distr p (X n)) g = integral p (g o X n)’
    >- (Q.X_GEN_TAC ‘n’ \\
        MATCH_MP_TAC (cj 1 integral_distr) \\
        simp [SIGMA_ALGEBRA_BOREL, Abbr ‘g’] \\
        MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
        simp [SIGMA_ALGEBRA_BOREL] \\
       ‘f IN borel_measurable borel’ by PROVE_TAC [in_borel_measurable_continuous_on] \\
        MATCH_MP_TAC MEASURABLE_COMP \\
        Q.EXISTS_TAC ‘borel’ >> rw [real_in_borel_measurable]) >> Rewr' \\
    Know ‘!n. integral (space Borel,subsets Borel,distr p Y) g = integral p (g o Y)’
    >- (MATCH_MP_TAC (cj 1 integral_distr) \\
        simp [SIGMA_ALGEBRA_BOREL, Abbr ‘g’] \\
        MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL' \\
        simp [SIGMA_ALGEBRA_BOREL] \\
       ‘f IN borel_measurable borel’ by PROVE_TAC [in_borel_measurable_continuous_on] \\
        MATCH_MP_TAC MEASURABLE_COMP \\
        Q.EXISTS_TAC ‘borel’ >> rw [real_in_borel_measurable]) >> Rewr;

(* IMPORTANT: convergence of r.v. in distribution is equivalent to weak convergence of
   their distribution functions.
 *)
Theorem converge_in_dist_alt :
    !p X Y. prob_space p /\
           (!n. real_random_variable (X n) p) /\ real_random_variable Y p ==>
           ((X --> Y) (in_distribution p) <=>
            (\n. distribution p (X n)) --> distribution p Y)
Proof
    rw [converge_in_dist_def, weak_converge_def, expectation_def, distribution_distr,
        real_random_variable, prob_space_def, p_space_def, events_def]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 2) *)
      converge_in_dist_tactic1,
      (* goal 2 (of 2) *)
      converge_in_dist_tactic2 ]
QED

(* Theorem 4.4.2 [2, p.93] *)
Theorem converge_in_dist_alt' :
    !p X Y. prob_space p /\
           (!n. real_random_variable (X n) p) /\ real_random_variable Y p ==>
           ((X --> Y) (in_distribution p) <=>
            !f. bounded (IMAGE f UNIV) /\ f continuous_on univ(:real) ==>
               ((\n. expectation p (Normal o f o real o (X n))) -->
                expectation p (Normal o f o real o Y)) sequentially)
Proof
    rw [converge_in_dist_alt, weak_converge_def, distribution_distr, expectation_def,
        real_random_variable, prob_space_def, p_space_def, events_def]
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 2) *)
      converge_in_dist_tactic2,
      (* goal 2 (of 2) *)
      converge_in_dist_tactic1 ]
QED

(* ------------------------------------------------------------------------- *)
(*  PDF                                                                      *)
(* ------------------------------------------------------------------------- *)

(* This definition comes from HVG's original work (real-based)

   cf. probabilityTheory.prob_density_function_def (extreal-based)
 *)
Definition PDF_def :
    PDF p X = RN_deriv (distribution p X) lborel
End

Theorem PDF_LE_POS :
    !p X. prob_space p /\ random_variable X p borel /\
          distribution p X << lborel ==> !x. 0 <= PDF p X x
Proof
    rpt STRIP_TAC
 >> `measure_space (space borel, subsets borel, distribution p X)`
       by PROVE_TAC [distribution_prob_space, prob_space_def,
                     sigma_algebra_borel]
 >> ASSUME_TAC sigma_finite_lborel
 >> ASSUME_TAC measure_space_lborel
 >> MP_TAC (ISPECL [“lborel”, “distribution (p :'a m_space) (X :'a -> real)”]
                   Radon_Nikodym')
 >> RW_TAC std_ss [m_space_lborel, sets_lborel, space_borel, IN_UNIV]
 >> fs [PDF_def, RN_deriv_def, m_space_def, measurable_sets_def,
        m_space_lborel, sets_lborel, space_borel]
 >> SELECT_ELIM_TAC >> METIS_TAC []
QED

Theorem EXPECTATION_PDF_1 : (* was: INTEGRAL_PDF_1 *)
    !p X. prob_space p /\ random_variable X p borel /\
          distribution p X << lborel ==>
          expectation lborel (PDF p X) = 1
Proof
    rpt STRIP_TAC
 >> `prob_space (space borel, subsets borel, distribution p X)`
       by PROVE_TAC [distribution_prob_space, sigma_algebra_borel]
 >> NTAC 2 (POP_ASSUM MP_TAC) >> KILL_TAC
 >> RW_TAC std_ss [prob_space_def, p_space_def, m_space_def, measure_def,
                   expectation_def]
 >> ASSUME_TAC sigma_finite_lborel
 >> ASSUME_TAC measure_space_lborel
 >> MP_TAC (ISPECL [“lborel”, “distribution (p :'a m_space) (X :'a -> real)”]
                   Radon_Nikodym')
 >> RW_TAC std_ss [m_space_lborel, sets_lborel, m_space_def, measure_def,
                   space_borel, IN_UNIV]
 >> fs [PDF_def, RN_deriv_def, m_space_def, measurable_sets_def,
        m_space_lborel, sets_lborel, space_borel]
 >> SELECT_ELIM_TAC
 >> CONJ_TAC >- METIS_TAC []
 >> Q.X_GEN_TAC `g`
 >> RW_TAC std_ss [density_measure_def]
 >> POP_ASSUM (MP_TAC o Q.SPEC `space borel`)
 >> Know `space borel IN subsets borel`
 >- (`sigma_algebra borel` by PROVE_TAC [sigma_algebra_borel] \\
     PROVE_TAC [sigma_algebra_def, ALGEBRA_SPACE])
 >> RW_TAC std_ss []
 >> Know `integral lborel g = pos_fn_integral lborel g`
 >- (MATCH_MP_TAC integral_pos_fn >> art [])
 >> Rewr'
 >> Know `pos_fn_integral lborel g =
          pos_fn_integral lborel (\x. g x * indicator_fn (space borel) x)`
 >- (MATCH_MP_TAC pos_fn_integral_cong \\
     rw [m_space_lborel, indicator_fn_def, mul_rone, mul_rzero, le_refl])
 >> Rewr'
 >> POP_ORW >> rw [space_borel]
QED

(* ------------------------------------------------------------------------- *)
(*  Normal density                                                           *)
(* ------------------------------------------------------------------------- *)

(* NOTE: ‘normal_density m s’ is a function of “:real -> real”, where m is the
   expectation, s is the standard deviation.
 *)
Definition normal_density :
    normal_density mu sig x =
      (1 / sqrt (2 * pi * sig pow 2)) * exp (-((x - mu) pow 2) / (2 * sig pow 2))
End

Overload std_normal_density = “normal_density 0 1”

Theorem std_normal_density_def :
    !x. std_normal_density x = (1 / sqrt (2 * pi)) * exp (-(x pow 2) / 2)
Proof
    RW_TAC std_ss [normal_density]
 >> SIMP_TAC real_ss [REAL_SUB_RZERO, POW_ONE]
QED

Theorem normal_density_nonneg :
    !mu sig x. 0 <= normal_density mu sig x
Proof
  RW_TAC std_ss [normal_density] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  SIMP_TAC std_ss [EXP_POS_LE, GSYM REAL_INV_1OVER, REAL_LE_INV_EQ] THEN
  MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC real_ss [REAL_LE_LT, PI_POS],
   ALL_TAC] THEN
  SIMP_TAC real_ss [REAL_LE_POW2]
QED

Theorem normal_density_pos :
    !mu sig. 0 < sig ==> 0 < normal_density mu sig x
Proof
  RW_TAC std_ss [normal_density] THEN MATCH_MP_TAC REAL_LT_MUL THEN
  SIMP_TAC std_ss [EXP_POS_LT, GSYM REAL_INV_1OVER, REAL_LT_INV_EQ] THEN
  MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN SIMP_TAC real_ss [PI_POS], ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LT >> art []
QED

Theorem normal_density_continuous_on :
    !mu sig s. normal_density mu sig continuous_on s
Proof
    rpt GEN_TAC
 >> ‘normal_density mu sig =
       (\x. 1 / sqrt (2 * pi * sig pow 2) *
            exp (-((x - mu) pow 2) / (2 * sig pow 2)))’
       by rw [normal_density, FUN_EQ_THM]
 >> POP_ORW
 >> HO_MATCH_MP_TAC (SIMP_RULE std_ss [o_DEF] CONTINUOUS_ON_COMPOSE)
 >> reverse CONJ_TAC
 >- (‘$* (1 / sqrt (2 * pi * sig pow 2)) = \x. (1 / sqrt (2 * pi * sig pow 2)) * x’
       by rw [FUN_EQ_THM] >> POP_ORW \\
     HO_MATCH_MP_TAC CONTINUOUS_ON_CMUL >> rw [CONTINUOUS_ON_ID])
 >> HO_MATCH_MP_TAC (SIMP_RULE std_ss [o_DEF] CONTINUOUS_ON_COMPOSE)
 >> reverse CONJ_TAC
 >- rw [CONTINUOUS_ON_EXP]
 >> REWRITE_TAC [real_div, Once REAL_MUL_COMM]
 >> HO_MATCH_MP_TAC CONTINUOUS_ON_CMUL
 >> REWRITE_TAC [Once REAL_NEG_MINUS1]
 >> HO_MATCH_MP_TAC CONTINUOUS_ON_CMUL
 >> HO_MATCH_MP_TAC CONTINUOUS_ON_POW
 >> HO_MATCH_MP_TAC CONTINUOUS_ON_SUB
 >> rw [CONTINUOUS_ON_ID, CONTINUOUS_ON_CONST]
QED

Theorem in_measurable_borel_normal_density :
    !mu sig. normal_density mu sig IN borel_measurable borel
Proof
    rpt GEN_TAC
 >> MATCH_MP_TAC in_borel_measurable_continuous_on
 >> rw [normal_density_continuous_on]
QED

Theorem IN_MEASURABLE_BOREL_normal_density :
    !mu sig. Normal o normal_density mu sig IN Borel_measurable borel
Proof
    rpt GEN_TAC
 >> HO_MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP_BOREL'
 >> rw [sigma_algebra_borel, in_measurable_borel_normal_density]
QED

val _ = export_theory ();
val _ = html_theory "distribution";

(* References:

  [1] Qasim, M.: Formalization of Normal Random Variables, Concordia University (2016).
  [2] Chung, K.L.: A Course in Probability Theory, Third Edition. Academic Press (2001).
  [3] Rosenthal, J.S.: A First Look at Rigorous Probability Theory (Second Edition).
      World Scientific Publishing Company (2006).
  [4] Shiryaev, A.N.: Probability-1. Springer-Verlag New York (2016).

 *)
