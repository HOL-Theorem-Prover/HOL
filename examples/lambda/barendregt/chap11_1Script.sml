open HolKernel boolLib Parse bossLib BasicProvers

open pred_setTheory

open binderLib

open nomsetTheory labelledTermsTheory termTheory chap3Theory

val _ = new_theory "chap11_1";

fun Store_Thm(n,t,tac) = store_thm(n,t,tac) before export_rewrites [n]

(* ----------------------------------------------------------------------
    phi function for reducing all labelled redexes
   ---------------------------------------------------------------------- *)

val (phi_thm, _) =
    define_recursive_term_function'
      (SIMP_CONV (srw_ss()) [tpm_subst, fresh_tpm_subst, GSYM SIMPLE_ALPHA,
                             lemma15a])
      `(phi (VAR s) = VAR s : term) /\
       (phi (M @@ N) = phi M @@ phi N) /\
       (phi (LAM v M) = LAM v (phi M)) /\
       (phi (LAMi n v M N) = [phi N/v] (phi M))`
val _ = export_rewrites ["phi_thm"]

val FV_phi = store_thm(
  "FV_phi",
  ``!M. v IN FV (phi M) ==> v IN FV M``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN
  Q.EXISTS_TAC `{v}` THEN SRW_TAC [][] THENL [
    METIS_TAC [],
    METIS_TAC [],
    FULL_SIMP_TAC (srw_ss()) [FV_SUB] THEN METIS_TAC [IN_UNION, IN_DELETE]
  ]);

val NOT_IN_lSUB_I = Store_Thm(
  "NOT_IN_lSUB_I",
  ``∀M:lterm. v ∉ FV N ∧ v ≠ u ∧ v ∉ FV M ==> v ∉ FV ([N/u]M)``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN Q.EXISTS_TAC `FV N ∪ {u;v}` THEN
  SRW_TAC [][lSUB_VAR]);

val phi_vsubst_commutes = store_thm(
  "phi_vsubst_commutes",
  ``!M. phi ([VAR v/u] M) = [VAR v/u] (phi M)``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR] THEN
  SRW_TAC [][chap2Theory.substitution_lemma]);


(* ----------------------------------------------------------------------
    strip_label : removing all labels and dropping into :term
   ---------------------------------------------------------------------- *)

val _ = augment_srw_ss [
  simpLib.name_ss "alphas" (rewrites [GSYM tpm_ALPHA, GSYM ltpm_ALPHA])
]

val (strip_label_thm,_) = define_recursive_term_function
  `(strip_label (VAR s) = VAR s : term) /\
   (strip_label (M @@ N) = strip_label M @@ strip_label N) /\
   (strip_label (LAM v M) = LAM v (strip_label M)) /\
   (strip_label (LAMi n v M N) = (LAM v (strip_label M) @@ strip_label N))`
val _ = export_rewrites ["strip_label_thm"]

val FV_strip_label = Store_Thm(
  "FV_strip_label",
  ``!M. FV (strip_label M) = FV M``,
  HO_MATCH_MP_TAC simple_lterm_induction THEN SRW_TAC [][]);

val strip_label_vsubst_commutes = store_thm(
  "strip_label_vsubst_commutes",
  ``!M. [VAR u/v] (strip_label M) = strip_label ([VAR u/v] M)``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN
  Q.EXISTS_TAC `{u;v}` THEN SRW_TAC [][SUB_THM, SUB_VAR]);

val strip_label_eq_lam = store_thm(
  "strip_label_eq_lam",
  ``(strip_label M = LAM v t) =
        ?t'. (M = LAM v t') /\ (strip_label t' = t)``,
  Q.SPEC_THEN `M` STRUCT_CASES_TAC lterm_CASES THEN
  SRW_TAC [][LAM_eq_thm, lLAM_eq_thm, EQ_IMP_THM,
             tpm_eqr, ltpm_eqr] THEN
  FULL_SIMP_TAC (srw_ss()) [tpm_eqr, ltpm_eqr]);

val strip_label_eq_redex = store_thm(
  "strip_label_eq_redex",
  ``(strip_label M = LAM v t @@ u) <=>
         (?t' u'. (M = LAM v t' @@ u') /\ (strip_label t' = t) /\
                  (strip_label u' = u)) \/
         (?n t' u'. (M = LAMi n v t' u') /\
                    (strip_label t' = t) /\
                    (strip_label u' = u))``,
  Q.SPEC_THEN `M` STRUCT_CASES_TAC lterm_CASES THEN
  SRW_TAC [][strip_label_eq_lam] THENL [
    METIS_TAC [],
    SRW_TAC [][lLAMi_eq_thm, EQ_IMP_THM, LAM_eq_thm] THENL [
      FULL_SIMP_TAC (srw_ss()) [ltpm_eqr, tpm_eqr] THEN
      SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [],
      SRW_TAC [][tpm_eqr]
    ]
  ]);

val strip_label_subst = store_thm(
  "strip_label_subst",
  ``!M. strip_label ([N/v] M) = [strip_label N/v] (strip_label M)``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN Q.EXISTS_TAC `v INSERT FV N` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);

(* ----------------------------------------------------------------------
    null_labelling, from :term  to  :lterm
   ---------------------------------------------------------------------- *)

val (null_labelling_thm,_) = define_recursive_term_function`
  (null_labelling (VAR s : term) = VAR s : lterm) /\
  (null_labelling (M @@ N) = null_labelling M @@ null_labelling N) /\
  (null_labelling (LAM v M) = LAM v (null_labelling M))`
val _ = export_rewrites ["null_labelling_thm"]

val _ = diminish_srw_ss ["alphas"]

val FV_null_labelling = Store_Thm(
  "FV_null_labelling",
  ``!M. FV (null_labelling M) = FV M``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]);

val null_labelling_subst = store_thm(
  "null_labelling_subst",
  ``!M. null_labelling ([N/v] M) = [null_labelling N/v] (null_labelling M)``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `v INSERT FV N` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);

val strip_null_labelling = Store_Thm(
  "strip_null_labelling",
  ``!M. strip_label (null_labelling M) = M``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]);

val phi_null_labelling = Store_Thm(
  "phi_null_labelling",
  ``!M. phi (null_labelling M) = M``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]);

(* ----------------------------------------------------------------------
    substitution lemma
   ---------------------------------------------------------------------- *)

val christians_lemma = prove(
  ``!L: lterm. ~(x IN FV L) /\ ~(x IN FV N) ==> ~(x IN FV ([N/v] L))``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN
  Q.EXISTS_TAC `{x;v} UNION FV N` THEN
  SRW_TAC [][lSUB_VAR]);


val lSUBSTITUTION_LEMMA = store_thm(
  "lSUBSTITUTION_LEMMA",
  ``!M:lterm. ~(v = x) /\ ~(v IN FV L) ==>
              ([L/x] ([N/v] M) = [[L/x] N/v] ([L/x] M))``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN
  Q.EXISTS_TAC `{v;x} UNION FV L UNION FV N` THEN
  SRW_TAC [][lSUB_VAR, l14b, FV_SUB, christians_lemma]);

val ltpm_subst = store_thm(
  "ltpm_subst",
  ``!M. ltpm p ([N/v]M) = [ltpm p N/lswapstr p v] (ltpm p M)``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN Q.EXISTS_TAC `v INSERT FV N` THEN
  SRW_TAC [][lSUB_VAR]);

val l14c = store_thm(
  "l14c",
  ``!M:lterm. x IN FV M ==> (FV ([N/x]M) = FV N UNION (FV M DELETE x))``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN Q.EXISTS_TAC `x INSERT FV N` THEN
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
    Cases_on `x IN FV M'` THEN SRW_TAC [][l14b, EXTENSION, EQ_IMP_THM] THEN
    SRW_TAC [][] THEN METIS_TAC [],
    Cases_on `x IN FV M` THEN SRW_TAC [][l14b, EXTENSION, EQ_IMP_THM] THEN
    SRW_TAC [][] THEN METIS_TAC [],
    SRW_TAC [][EXTENSION, EQ_IMP_THM] THEN SRW_TAC [][] THEN METIS_TAC [],
    Cases_on `x IN FV M'` THEN SRW_TAC [][l14b, EXTENSION, EQ_IMP_THM] THEN
    SRW_TAC [][] THEN METIS_TAC [],
    Cases_on `x IN FV M` THEN SRW_TAC [][l14b, EXTENSION, EQ_IMP_THM] THEN
    SRW_TAC [][] THEN METIS_TAC []
  ]);

val lFV_SUB = store_thm(
  "lFV_SUB",
  ``FV ([N/v]M:lterm) = if v IN FV M then FV N UNION (FV M DELETE v)
                        else FV M``,
  METIS_TAC [l14c, l14b]);


(* ----------------------------------------------------------------------
    compatible closure for labelled terms
   ---------------------------------------------------------------------- *)

val (lcompat_closure_rules, lcompat_closure_ind, lcompat_closure_cases) =
    Hol_reln`(!x y. R x y ==> lcompat_closure R x y) /\
             (!z x y. lcompat_closure R x y ==>
                      lcompat_closure R (z @@ x) (z @@ y)) /\
             (!z x y. lcompat_closure R x y ==>
                      lcompat_closure R (x @@ z) (y @@ z)) /\
             (!v x y. lcompat_closure R x y ==>
                      lcompat_closure R (LAM v x) (LAM v y)) /\
             (!v n z x y.
                      lcompat_closure R x y ==>
                      lcompat_closure R (LAMi n v x z) (LAMi n v y z)) /\
             (!v n z x y.
                      lcompat_closure R x y ==>
                      lcompat_closure R (LAMi n v z x) (LAMi n v z y))`;

(* reduction on lterms *)
val beta0_def =
    Define`beta0 M N = ?n v t u. (M = LAMi n v t u) /\ (N = [u/v]t)`;

val beta1_def =
    Define`beta1 (M: lterm) N =
              ?v t u. (M = (LAM v t) @@ u) /\ (N = [u/v]t)`;

val lcc_beta_bvc_ind = store_thm(
  "lcc_beta_bvc_ind",
  ``!P X. FINITE X /\
          (!v M N. ~(v IN FV N) /\ ~(v IN X) ==>
                   P (LAM v M @@ N) ([N/v]M)) /\
          (!n v M N. ~(v IN FV N) /\ ~(v IN X) ==>
                     P (LAMi n v M N) ([N/v]M)) /\
          (!M M' N. P M M' ==> P (M @@ N) (M' @@ N)) /\
          (!M N N'. P N N' ==> P (M @@ N) (M @@ N')) /\
          (!v M M'. ~(v IN X) /\ P M M' ==> P (LAM v M) (LAM v M')) /\
          (!n v M M' N. ~(v IN X) /\ ~(v IN FV N) /\ P M M' ==>
                        P (LAMi n v M N) (LAMi n v M' N)) /\
          (!n v M N N'.
               ~(v IN X) /\ ~(v IN FV N) /\ ~(v IN FV N') /\ P N N' ==>
               P (LAMi n v M N) (LAMi n v M N'))
       ==>
          !M N. lcompat_closure (beta0 RUNION beta1) M N ==> P M N``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!M N. lcompat_closure(beta0 RUNION beta1) M N ==>
                        !p. P (ltpm p M) (ltpm p N)`
        THEN1 METIS_TAC [pmact_nil] THEN
  HO_MATCH_MP_TAC lcompat_closure_ind THEN
  SRW_TAC [][relationTheory.RUNION, beta0_def, beta1_def] THENL [
    (* beta0 reduction *)
    SRW_TAC [][ltpm_subst] THEN
    Q_TAC (NEW_TAC "z") `X UNION FV (ltpm p t) UNION FV (ltpm p u)` THEN
    `LAMi n (lswapstr p v) (ltpm p t) (ltpm p u) =
     LAMi n z (ltpm [(z,lswapstr p v)] (ltpm p t)) (ltpm p u)`
       by SRW_TAC [][ltpm_ALPHAi] THEN
    `[ltpm p u/lswapstr p v] (ltpm p t) =
     [ltpm p u/z] (ltpm [(z,lswapstr p v)] (ltpm p t))`
       by SRW_TAC [][fresh_ltpm_subst, l15a] THEN
    SRW_TAC [][],
    (* beta1 reduction *)
    SRW_TAC [][ltpm_subst] THEN
    Q_TAC (NEW_TAC "z") `X UNION FV (ltpm p t) UNION FV (ltpm p u)` THEN
    `LAM (lswapstr p v) (ltpm p t) =
       LAM z (ltpm [(z,lswapstr p v)] (ltpm p t))`
      by SRW_TAC [][ltpm_ALPHA] THEN
    `[ltpm p u/lswapstr p v] (ltpm p t) =
        [ltpm p u/z] (ltpm [(z,lswapstr p v)] (ltpm p t))`
      by SRW_TAC [][fresh_ltpm_subst, l15a] THEN
    SRW_TAC [][],

    Q_TAC (NEW_TAC "z") `X UNION FV (ltpm p M) UNION FV (ltpm p N)` THEN
    Q_TAC SUFF_TAC `(LAM (lswapstr p v) (ltpm p M) =
                         LAM z (ltpm [(z,lswapstr p v)] (ltpm p M))) /\
                    (LAM (lswapstr p v) (ltpm p N) =
                         LAM z (ltpm [(z,lswapstr p v)] (ltpm p N)))`
          THEN1 SRW_TAC [][GSYM pmact_decompose] THEN
    SRW_TAC [][ltpm_ALPHA],

    Q_TAC (NEW_TAC "w")
          `X UNION FV (ltpm p M) UNION FV (ltpm p N) UNION FV (ltpm p z)` THEN
    `(LAMi n (lswapstr p v) (ltpm p M) (ltpm p z) =
        LAMi n w (ltpm [(w,lswapstr p v)] (ltpm p M)) (ltpm p z)) /\
     (LAMi n (lswapstr p v) (ltpm p N) (ltpm p z) =
        LAMi n w (ltpm [(w,lswapstr p v)] (ltpm p N)) (ltpm p z))`
      by SRW_TAC [][ltpm_ALPHAi] THEN
    SRW_TAC [][GSYM pmact_decompose],

    Q_TAC (NEW_TAC "w")
          `X UNION FV (ltpm p z) UNION FV (ltpm p M) UNION FV (ltpm p N)` THEN
    `!N. LAMi n (lswapstr p v) (ltpm p z) N =
         LAMi n w (ltpm [(w,lswapstr p v)] (ltpm p z)) N`
      by SRW_TAC [][ltpm_ALPHAi] THEN
    SRW_TAC [][GSYM pmact_decompose]
  ]);

open boolSimps
val beta_matched = store_thm(
  "beta_matched",
  ``!M' N. beta (strip_label M') N ==>
           ?N'. (beta0 RUNION beta1) M' N' /\ (N = strip_label N')``,
  SIMP_TAC (srw_ss()) [beta_def] THEN
  REPEAT GEN_TAC THEN
  Q.SPEC_THEN `M'` STRUCT_CASES_TAC lterm_CASES THEN
  SRW_TAC [][] THENL [
    FULL_SIMP_TAC (srw_ss()) [strip_label_eq_lam] THEN
    SRW_TAC [DNF_ss][strip_label_subst, beta1_def, beta0_def,
                     relationTheory.RUNION, lLAM_eq_thm] THEN METIS_TAC [],
    FULL_SIMP_TAC (srw_ss()) [LAM_eq_thm, relationTheory.RUNION, beta0_def,
                              beta1_def] THEN
    SRW_TAC [DNF_ss][lLAMi_eq_thm, strip_label_subst,
                     fresh_tpm_subst, lemma15a]
  ]);

val lcc_beta_FV = store_thm(
  "lcc_beta_FV",
  ``!M N. lcompat_closure (beta0 RUNION beta1) M N ==>
          !x. x IN FV N ==> x IN FV M``,
  HO_MATCH_MP_TAC lcompat_closure_ind THEN
  SRW_TAC [][relationTheory.RUNION, beta0_def, beta1_def] THEN
  TRY (PROVE_TAC []) THEN
  FULL_SIMP_TAC (srw_ss() ++ boolSimps.COND_elim_ss) [lFV_SUB] THEN
  PROVE_TAC []);

val lcc_beta_subst = store_thm(
  "lcc_beta_subst",
  ``!M N P v. lcompat_closure (beta0 RUNION beta1) M N ==>
              lcompat_closure (beta0 RUNION beta1) ([P/v]M) ([P/v]N)``,
  REPEAT GEN_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`N`, `M`] THEN
  HO_MATCH_MP_TAC lcc_beta_bvc_ind THEN
  Q.EXISTS_TAC `v INSERT FV P` THEN SRW_TAC [][lcompat_closure_rules] THENL [
    Q_TAC SUFF_TAC `beta1 (LAM v' ([P/v]M) @@ [P/v] N) ([P/v]([N/v']M))`
          THEN1 METIS_TAC [lcompat_closure_rules, relationTheory.RUNION] THEN
    SRW_TAC [][beta1_def] THEN
    MAP_EVERY Q.EXISTS_TAC [`v'`, `[P/v]M`] THEN
    SRW_TAC [][lSUBSTITUTION_LEMMA],
    Q_TAC SUFF_TAC `beta0 (LAMi n v' ([P/v]M) ([P/v]N)) ([P/v]([N/v']M))`
          THEN1 METIS_TAC [lcompat_closure_rules, relationTheory.RUNION] THEN
    SRW_TAC [][beta0_def] THEN
    MAP_EVERY Q.EXISTS_TAC [`n`,`v'`, `[P/v]M`, `[P/v]N`] THEN
    SRW_TAC [][lSUBSTITUTION_LEMMA]
  ]);

val lcc_beta_ltpm_imp = store_thm(
  "lcc_beta_ltpm_imp",
  ``!M N. lcompat_closure (beta0 RUNION beta1) M N ==>
          !pi. lcompat_closure (beta0 RUNION beta1) (ltpm pi M) (ltpm pi N)``,
  HO_MATCH_MP_TAC lcompat_closure_ind THEN
  SRW_TAC [][lcompat_closure_rules] THEN
  FULL_SIMP_TAC (srw_ss()) [beta0_def, beta1_def, relationTheory.RUNION] THEN
  SRW_TAC [][ltpm_subst] THEN
  METIS_TAC [relationTheory.RUNION, beta0_def, beta1_def,
             lcompat_closure_rules]);

val lcc_beta_ltpm_eqn = store_thm(
  "lcc_beta_ltpm_eqn",
  ``lcompat_closure (beta0 RUNION beta1) (ltpm pi M) N =
    lcompat_closure (beta0 RUNION beta1) M (ltpm (REVERSE pi) N)``,
  METIS_TAC [lcc_beta_ltpm_imp, pmact_inverse]);

val lcc_beta_LAM = store_thm(
  "lcc_beta_LAM",
  ``!v t N. lcompat_closure (beta0 RUNION beta1) (LAM v t) N =
            ?N0. (N = LAM v N0) /\
                 lcompat_closure (beta0 RUNION beta1) t N0``,
  REPEAT GEN_TAC THEN
  CONV_TAC (LAND_CONV (REWR_CONV lcompat_closure_cases)) THEN
  SRW_TAC [][beta0_def, beta1_def, relationTheory.RUNION] THEN EQ_TAC THEN
  STRIP_TAC THENL [
    FULL_SIMP_TAC (srw_ss()) [lLAM_eq_thm] THEN
    SRW_TAC [][ltpm_eqr, lcc_beta_ltpm_eqn, pmact_flip_args] THEN
    METIS_TAC [lcc_beta_FV],
    METIS_TAC []
  ]);

val cc_beta_matched = store_thm(
  "cc_beta_matched",
  ``!M N. compat_closure beta M N ==>
          !M'. (M = strip_label M') ==>
               ?N'. lcompat_closure (beta0 RUNION beta1) M' N' /\
                    (N = strip_label N')``,
  HO_MATCH_MP_TAC compat_closure_ind THEN REPEAT CONJ_TAC THENL [
    SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss)
             [beta_def, strip_label_eq_redex] THEN
    SRW_TAC [][] THEN
    Q.EXISTS_TAC `[u'/x]t'` THEN SRW_TAC [][strip_label_subst] THENL [
      METIS_TAC [lcompat_closure_rules, beta1_def, relationTheory.RUNION],
      METIS_TAC [lcompat_closure_rules, beta0_def, relationTheory.RUNION]
    ],
    REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
    `(∃s. M' = VAR s) ∨ (∃t1 t2. M' = t1 @@ t2) ∨ (∃v t. M' = LAM v t) ∨
     (∃n v t1 t2. M' = LAMi n v t1 t2)`
       by (Q.SPEC_THEN `M'` STRUCT_CASES_TAC lterm_CASES THEN SRW_TAC [][] THEN
           METIS_TAC []) THEN
    SRW_TAC [][] THENL [
      FIRST_X_ASSUM (Q.SPEC_THEN `t2` MP_TAC) THEN SRW_TAC [][] THEN
      Q.EXISTS_TAC `t1 @@ N'` THEN SRW_TAC [][lcompat_closure_rules],
      FIRST_X_ASSUM (Q.SPEC_THEN `t2` MP_TAC) THEN SRW_TAC [][] THEN
      Q.EXISTS_TAC `LAMi n v t1 N'` THEN SRW_TAC [][lcompat_closure_rules]
    ],
    REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
    `(∃s. M' = VAR s) ∨ (∃t1 t2. M' = t1 @@ t2) ∨ (∃v t. M' = LAM v t) ∨
     (∃n v t1 t2. M' = LAMi n v t1 t2)`
       by (Q.SPEC_THEN `M'` STRUCT_CASES_TAC lterm_CASES THEN SRW_TAC [][] THEN
           METIS_TAC []) THEN
    SRW_TAC [][] THENL [
      FIRST_X_ASSUM (Q.SPEC_THEN `t1` MP_TAC) THEN SRW_TAC [][] THEN
      Q.EXISTS_TAC `N' @@ t2` THEN SRW_TAC [][lcompat_closure_rules],
      FIRST_X_ASSUM (Q.SPEC_THEN `LAM v t1` MP_TAC) THEN
      SRW_TAC [][lcc_beta_LAM] THEN
      Q.EXISTS_TAC `LAMi n v N0 t2` THEN SRW_TAC [][lcompat_closure_rules]
    ],
    SRW_TAC [][strip_label_eq_lam] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `t'` MP_TAC) THEN SRW_TAC [][] THEN
    Q.EXISTS_TAC `LAM v N'` THEN SRW_TAC [][lcompat_closure_rules] THEN
    METIS_TAC []
  ]);

val lemma11_1_6i = store_thm(
  "lemma11_1_6i",
  ``!M' N. reduction beta (strip_label M') N ==>
           ?N'. RTC (lcompat_closure (beta0 RUNION beta1)) M' N' /\
                (N = strip_label N')``,
  SIMP_TAC (srw_ss()) [] THEN
  Q_TAC SUFF_TAC
        `!M N. RTC (compat_closure beta) M N ==>
               !M'. (M = strip_label M') ==>
                    ?N'. RTC (lcompat_closure (beta0 RUNION beta1)) M' N' /\
                         (N = strip_label N')` THEN1 PROVE_TAC [] THEN
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN CONJ_TAC THEN
  PROVE_TAC [relationTheory.RTC_RULES, cc_beta_matched]);

val lcc_beta_matching_beta = store_thm(
  "lcc_beta_matching_beta",
  ``!M' N'. lcompat_closure (beta0 RUNION beta1) M' N' ==>
            compat_closure beta (strip_label M') (strip_label N')``,
  HO_MATCH_MP_TAC lcompat_closure_ind THEN
  SRW_TAC [][strip_label_thm] THEN1
    (Q_TAC SUFF_TAC `beta (strip_label M') (strip_label N')` THEN1
        PROVE_TAC [compat_closure_rules] THEN
     FULL_SIMP_TAC (srw_ss()) [beta0_def, beta1_def, relationTheory.RUNION,
                               strip_label_thm, beta_def,
                               strip_label_subst] THEN PROVE_TAC []) THEN
  PROVE_TAC [compat_closure_rules]);

val lemma11_1_6ii = store_thm(
  "lemma11_1_6ii",
  ``!M' N'.
      RTC (lcompat_closure (beta0 RUNION beta1)) M' N' ==>
      reduction beta (strip_label M') (strip_label N')``,
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
  PROVE_TAC [reduction_rules, lcc_beta_matching_beta]);

val coFV_phi = prove(
  ``~(v IN FV M) ==> ~(v IN FV (phi M))``,
  METIS_TAC [FV_phi]);

val lemma11_1_7i = store_thm(
  "lemma11_1_7i",
  ``!M. phi ([N/x]M) = [phi N/x] (phi M)``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN Q.EXISTS_TAC `x INSERT FV N` THEN
  SRW_TAC [][SUB_THM, coFV_phi, lSUB_VAR, SUB_VAR] THEN
  SRW_TAC [][chap2Theory.substitution_lemma, coFV_phi]);

val lcc_beta_phi_matched = store_thm(
  "lcc_beta_phi_matched",
  ``!M N. lcompat_closure (beta0 RUNION beta1) M N ==>
          reduction beta (phi M) (phi N)``,
  HO_MATCH_MP_TAC lcompat_closure_ind THEN
  SRW_TAC [][] THENL [
    FULL_SIMP_TAC (srw_ss()) [beta0_def, beta1_def, relationTheory.RUNION]
    THENL [
      SRW_TAC [][lemma11_1_7i, reduction_rules],
      Q_TAC SUFF_TAC `beta (LAM v (phi t) @@ phi u) (phi ([u/v] t))` THEN1
        PROVE_TAC [reduction_rules] THEN
      SRW_TAC [][lemma11_1_7i, beta_def] THEN PROVE_TAC []
    ],

    PROVE_TAC [reduction_rules],
    PROVE_TAC [reduction_rules],
    PROVE_TAC [reduction_beta_subst],
    PROVE_TAC [lemma3_8]
  ]);

val lemma11_1_7ii = store_thm(
  "lemma11_1_7ii",
  ``!M N. RTC (lcompat_closure (beta0 RUNION beta1)) M N ==>
          reduction beta (phi M) (phi N)``,
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
  PROVE_TAC [reduction_rules, lcc_beta_phi_matched]);

val lemma11_1_8 = store_thm(
  "lemma11_1_8",
  ``!M. reduction beta (strip_label M) (phi M)``,
  HO_MATCH_MP_TAC lterm_bvc_induction THEN Q.EXISTS_TAC `{}` THEN
  SIMP_TAC (srw_ss()) [strip_label_thm, reduction_rules] THEN CONJ_TAC THENL [
    PROVE_TAC [reduction_rules],
    MAP_EVERY Q.X_GEN_TAC [`s`, `M`, `M'`] THEN STRIP_TAC THEN
    `beta (LAM s (strip_label M) @@ strip_label M')
          ([strip_label M'/s] (strip_label M))` by PROVE_TAC [beta_def] THEN
    `reduction beta ([strip_label M'/s] (strip_label M))
                    ([phi M'/s] (strip_label M))` by PROVE_TAC [lemma3_8] THEN
    `reduction beta ([phi M'/s] (strip_label M))
                    ([phi M'/s] (phi M))` by
        PROVE_TAC [reduction_beta_subst, l14a] THEN
    PROVE_TAC [reduction_rules]
  ]);

val can_index_redex = store_thm(
  "can_index_redex",
  ``!M N. compat_closure beta M N ==>
          ?M'. (strip_label M' = M) /\ (phi M' = N)``,
  HO_MATCH_MP_TAC compat_closure_ind THEN REPEAT CONJ_TAC THENL [
    MAP_EVERY Q.X_GEN_TAC [`M`,`N`] THEN
    SIMP_TAC (srw_ss()) [beta_def, GSYM LEFT_FORALL_IMP_THM] THEN
    MAP_EVERY Q.X_GEN_TAC [`x`,`body`,`arg`] THEN SRW_TAC [][] THEN
    Q.EXISTS_TAC `LAMi 0 x (null_labelling body) (null_labelling arg)` THEN
    SIMP_TAC (srw_ss()) [],
    MAP_EVERY Q.X_GEN_TAC [`M`,`N`,`z`] THEN SRW_TAC [][] THEN
    Q.EXISTS_TAC `null_labelling z @@ M'` THEN SRW_TAC [][],
    MAP_EVERY Q.X_GEN_TAC [`M`,`N`,`z`] THEN SRW_TAC [][] THEN
    Q.EXISTS_TAC `M' @@ null_labelling z` THEN SRW_TAC [][],
    MAP_EVERY Q.X_GEN_TAC [`M`,`N`,`v`] THEN SRW_TAC [][] THEN
    Q.EXISTS_TAC `LAM v M'` THEN
    ASM_SIMP_TAC (srw_ss()) []
  ]);

val strip_lemma = store_thm(
  "strip_lemma",
  ``!M M' N. compat_closure beta M M' /\
             reduction beta M N ==>
             ?N'. reduction beta M' N' /\ reduction beta N N'``,
  REPEAT STRIP_TAC THEN
  `?Mtilde. (strip_label Mtilde = M) /\ (phi Mtilde = M')` by
     PROVE_TAC [can_index_redex] THEN
  `?Ntilde. (N = strip_label Ntilde) /\
            RTC (lcompat_closure (beta0 RUNION beta1)) Mtilde Ntilde` by
     PROVE_TAC [lemma11_1_6i] THEN
  `reduction beta M' (phi Ntilde)` by PROVE_TAC [lemma11_1_7ii] THEN
  `reduction beta N (phi Ntilde)` by PROVE_TAC [lemma11_1_8] THEN
  PROVE_TAC []);

val beta_CR_2 = store_thm(
  "beta_CR_2",
  ``CR beta``,
  SIMP_TAC (srw_ss())[CR_def, diamond_property_def] THEN
  Q_TAC SUFF_TAC
        `!M M1. RTC (compat_closure beta) M M1 ==>
                !M2. reduction beta M M2 ==>
                     ?M3. reduction beta M1 M3 /\ reduction beta M2 M3`
        THEN1 PROVE_TAC [] THEN
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN
  PROVE_TAC [reduction_rules, strip_lemma]);

val _ = export_theory()
