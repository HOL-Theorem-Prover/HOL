open HolKernel Parse boolLib bossLib BasicProvers metisLib

local open stringTheory in end

open pred_setTheory binderLib boolSimps relationTheory
open chap3Theory

(* ----------------------------------------------------------------------

    This theory demonstrates that the quotiented theory of
    lambda-calculus in the rest of the development is a good model of
    the "raw" theory of lambda calculus syntax.

    The raw syntax here and the relations on it are taken from

     "A formalised first-order confluence proof of for the \lambda-calculus
      using one-sorted variable names"

        by Rene Vestergaard and James Brotherston

     which appeared in Information and Computation, 183:2.
     (A pre-print of this paper is available at
       http://www.jaist.ac.jp/~vester/Writings/vestergaard-brotherston-IandC-rta01.ps.gz)

    In this paper, the "real \lambda-calculus" is established by
    taking a quotient of raw syntax terms, and the notion of
    beta-reduction in the real type is defined such that

           collapse e_1  -->_\beta collapse e_2

                 = (by defn)

           e1 ==_\alpha ; -->_\beta ; ==_\alpha e2

    (Where collapse is written graphically in the paper as the "round
     down operator".  Also, in the theory below, the semi-colon is
     replaced with the relation composition operator O.)

    I show the above is a theorem of the development.

    The collapse function below has the important property that

      EQC alpha x y = (collapse x = collapse y)

    I.e., two raw syntax terms are alpha-equivalent iff they collapse
    to the same quotiented term.

   ---------------------------------------------------------------------- *)

val _ = new_theory "raw_syntax"

val _ = Hol_datatype `raw_term = var of string
                               | app of raw_term => raw_term
                               | lam of string => raw_term`;

val fv_def = Define`
  (fv (var s) = {s}) /\
  (fv (app t u) = fv t UNION fv u) /\
  (fv (lam v t) = fv t DELETE v)`;

val FINITE_fv = store_thm(
  "FINITE_fv",
  ``!t. FINITE (fv t)``,
  Induct THEN SRW_TAC [][fv_def]);
val _ = export_rewrites ["FINITE_fv"]

val capt_def = Define`
  (capt x (var y) = {}) /\
  (capt x (app t u) = capt x t UNION capt x u) /\
  (capt x (lam y t) = if ~(x = y) /\ x IN fv t then {y} UNION capt x t
                      else {})
`

val FINITE_capt = store_thm(
  "FINITE_capt",
  ``!t v. FINITE (capt v t)``,
  Induct THEN SRW_TAC [][capt_def]);
val _ = export_rewrites ["FINITE_capt"]

val capt_fv = store_thm(
  "capt_fv",
  ``!e x. ~(x IN fv e) ==> (capt x e = {})``,
  Induct THEN SRW_TAC [][capt_def, fv_def]);
val _ = export_rewrites ["capt_fv"]

val subst_def = Define`
  (subst x y (var s) = if y = s then x else var s) /\
  (subst x y (app t u) = app (subst x y t) (subst x y u)) /\
  (subst x y (lam v t) = if ~(y = v) /\ ~(v IN fv x) then lam v (subst x y t)
                         else lam v t)
`;

val (ialpha_rules, ialpha_ind, ialpha_cases) = Hol_reln`
  (!x y e.  ~(y IN capt x e UNION fv e) ==>
            ialpha y (lam x e) (lam y (subst (var y) x e))) /\
  (!e e' x y. ialpha y e e' ==> ialpha y (lam x e) (lam x e')) /\
  (!e1 e1' e2 y. ialpha y e1 e1' ==> ialpha y (app e1 e2) (app e1' e2)) /\
  (!e1 e2 e2' y. ialpha y e2 e2' ==> ialpha y (app e1 e2) (app e1 e2'))
`;

val (beta_rules, beta_ind, beta_cases) = Hol_reln`
  (!e1 e2 x. (fv e2 INTER capt x e1 = {}) ==>
             beta (app (lam x e1) e2) (subst e2 x e1)) /\
  (!e e' x. beta e e' ==> beta (lam x e) (lam x e')) /\
  (!e1 e1' e2. beta e1 e1' ==> beta (app e1 e2) (app e1' e2)) /\
  (!e1 e2 e2'. beta e2 e2' ==> beta (app e1 e2) (app e1 e2'))
`;

val alpha_def = Define`alpha e1 e2 = ?y. ialpha y e1 e2`

val renaming_sanity1 = store_thm(
  "renaming_sanity1",
  ``!e x. subst (var x) x e = e``,
  Induct THEN SRW_TAC [][subst_def]);
val _ = export_rewrites ["renaming_sanity1"]

val renaming_sanity2 = store_thm(
  "renaming_sanity2",
  ``!e x e'. ~(x IN fv e) ==> (subst e' x e = e)``,
  Induct THEN SRW_TAC [][subst_def, fv_def]);
val _ = export_rewrites ["renaming_sanity2"]

val RIGHT_INTER_OVER_UNION = prove(
  ``(x UNION y) INTER z = (x INTER z) UNION (y INTER z)``,
  SRW_TAC [][EXTENSION] THEN tautLib.TAUT_TAC)

val SING_INTER = prove(
  ``({x} INTER Y = if x IN Y then {x} else {}) /\
    (Y INTER {x} = if x IN Y then {x} else {})``,
  SRW_TAC [][EXTENSION] THEN PROVE_TAC []);

val renaming_sanity3 = store_thm(
  "renaming_sanity3",
  ``!e e' x. ~(x IN fv e') /\ (capt x e INTER fv e' = {}) ==>
             ~(x IN fv (subst e' x e))``,
  Induct THEN
  SRW_TAC [][capt_def, fv_def, subst_def,
             RIGHT_INTER_OVER_UNION, SING_INTER] THEN
  FULL_SIMP_TAC (srw_ss()) []);

val renaming_sanity4 = store_thm(
  "renaming_sanity4",
  ``!e x y. ~(y IN fv e) ==> (subst (var x) y (subst (var y) x e) = e)``,
  Induct THEN SRW_TAC [][fv_def, subst_def] THEN
  SRW_TAC [][]);

val collapse_def = Define`
  (collapse (var s) = VAR s) /\
  (collapse (app t u) = collapse t @@ collapse u) /\
  (collapse (lam v t) = LAM v (collapse t))`;

open termTheory

val FV_collapse = store_thm(
  "FV_collapse",
  ``!e. FV (collapse e) = fv e``,
  Induct THEN SRW_TAC [][collapse_def, fv_def]);
val _ = export_rewrites ["FV_collapse"]

val fv_vsubst = store_thm(
  "fv_vsubst",
  ``!e x y. ~(y IN capt x e) ==>
            (fv (subst (var y) x e) =
               if x IN fv e then y INSERT (fv e DELETE x)
               else fv e)``,
  Induct THEN
  SRW_TAC [][fv_def, capt_def, subst_def, EXTENSION] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN PROVE_TAC []);

val collapse_vsubst = store_thm(
  "collapse_vsubst",
  ``!e x y. ~(y IN capt x e)  ==>
            (collapse (subst (var y) x e) = [VAR y/x] (collapse e))``,
  Induct THEN
  ASM_SIMP_TAC (srw_ss()) [collapse_def, capt_def, fv_def, subst_def,
                           SUB_VAR, SUB_THM]
  THENL [
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN SRW_TAC [][collapse_def],
    MAP_EVERY Q.X_GEN_TAC [`s`, `x`, `y`] THEN
    Cases_on `x = s` THEN ASM_SIMP_TAC (srw_ss()) [collapse_def, SUB_THM] THEN
    Cases_on `s = y` THEN
    ASM_SIMP_TAC (srw_ss()) [collapse_def, SUB_THM, lemma14b] THENL [
      Cases_on `x IN fv e` THEN
      ASM_SIMP_TAC (srw_ss()) [] THEN
      `~(x IN FV (collapse e))` by SRW_TAC [][] THEN
      `~(x IN FV (LAM y (collapse e)))` by SRW_TAC [][] THEN
      SRW_TAC [][lemma14b],
      Cases_on `x IN fv e` THEN ASM_SIMP_TAC (srw_ss()) []
    ]
  ]);

val collapse_subst = store_thm(
  "collapse_subst",
  ``!t u v. (capt v t INTER fv u = {}) ==>
            (collapse (subst u v t) = [collapse u/v] (collapse t))``,
  Induct THEN
  ASM_SIMP_TAC (srw_ss()) [collapse_def, capt_def, fv_def, subst_def,
                           SUB_VAR, SUB_THM, RIGHT_INTER_OVER_UNION]
  THENL [
    REPEAT GEN_TAC THEN SRW_TAC [][collapse_def],
    REPEAT GEN_TAC THEN SRW_TAC [][collapse_def, RIGHT_INTER_OVER_UNION,
                                   SUB_THM] THEN
    FULL_SIMP_TAC (srw_ss() ++ COND_elim_ss) [SING_INTER, SUB_THM, lemma14b]
  ]);


val x_IN_capt_x = store_thm(
  "x_IN_capt_x",
  ``!t. ~(x IN capt x t)``,
  Induct THEN SRW_TAC [][capt_def]);

val capt_subst2 = prove(
  ``!t.
       ~(v IN capt x t) /\ ~(v IN fv t) ==>
       ~(x IN capt v (subst (var v) x t))``,
  Induct THEN SRW_TAC [][capt_def, subst_def, fv_def, fv_vsubst] THEN
  FULL_SIMP_TAC (srw_ss()) []);

val ialpha_sym = store_thm(
  "ialpha_sym",
  ``!y t1 t2. ialpha y t1 t2 ==> ?z. ialpha z t2 t1``,
  HO_MATCH_MP_TAC ialpha_ind THEN SRW_TAC [][] THENL [
    Cases_on `x = y` THENL [
      SRW_TAC [][renaming_sanity1] THEN
      Q.EXISTS_TAC `x` THEN
      Q_TAC SUFF_TAC `~(x IN fv (subst (var x) x e))` THEN
            METIS_TAC [ialpha_rules, renaming_sanity1,
                       pred_setTheory.IN_UNION],
      `~(x IN fv (subst (var y) x e))`
          by SRW_TAC [][fv_vsubst] THEN
      Q_TAC SUFF_TAC `~(x IN capt y (subst (var y) x e))`
            THEN1 METIS_TAC [renaming_sanity4, ialpha_rules,
                             pred_setTheory.IN_UNION] THEN
      SRW_TAC [][capt_subst2]
    ],
    METIS_TAC [ialpha_rules],
    METIS_TAC [ialpha_rules],
    METIS_TAC [ialpha_rules]
  ]);

val alpha_sym = store_thm(
  "alpha_sym",
  ``alpha x y ==> alpha y x``,
  METIS_TAC [alpha_def, ialpha_sym]);

val alpha_CONG = store_thm(
  "alpha_CONG",
  ``!t t'. alpha t t' ==>
           (!u. alpha (app t u) (app t' u) /\
                alpha (app u t) (app u t')) /\
           (!v. alpha (lam v t) (lam v t'))``,
  SRW_TAC [][alpha_def] THEN PROVE_TAC [ialpha_rules]);

val EQC_alpha_CONG = store_thm(
  "EQC_alpha_CONG",
  ``!t t'. EQC alpha t t' ==>
           (!u. EQC alpha (app t u) (app t' u) /\
                EQC alpha (app u t) (app u t')) /\
           (!v. EQC alpha (lam v t) (lam v t'))``,
  HO_MATCH_MP_TAC relationTheory.EQC_INDUCTION THEN
  SRW_TAC [][] THEN
  PROVE_TAC [alpha_CONG, EQC_R, EQC_SYM, EQC_TRANS]);



val EQC_alpha_CONG2 = store_thm(
  "EQC_alpha_CONG2",
  ``!t t' u u'. EQC alpha t t' /\ EQC alpha u u' ==>
                EQC alpha (app t u) (app t' u')``,
  METIS_TAC [EQC_alpha_CONG, EQC_TRANS]);

val ialpha_lam_lemma = prove(
  ``!y t u. ialpha y t u ==>
            !v t0 s k t1 t2.
               ((t = lam v t0) ==>
                ~(u = var s) /\ ~(u = app t1 t2)) /\
               ((u = lam v t0) ==>
                ~(t = var s) /\ ~(t = app t1 t2))``,
  HO_MATCH_MP_TAC ialpha_ind THEN SRW_TAC [][]);

val ialpha_lam_thm = save_thm(
  "ialpha_lam_thm",
  SIMP_RULE (srw_ss() ++ DNF_ss) [] ialpha_lam_lemma)

val alpha_lam_thm = store_thm(
  "alpha_lam_thm",
  ``(!v t0 s. ~alpha (lam v t0) (var s) /\ ~alpha (var s) (lam v t0)) /\
    (!v t0 t1 t2.
        ~alpha (lam v t0) (app t1 t2) /\ ~alpha (app t1 t2) (lam v t0))``,
  METIS_TAC [alpha_def, ialpha_lam_thm]);
val _ = export_rewrites ["alpha_lam_thm"]

val EQC_alpha_lam_lemma = prove(
  ``!t u. EQC alpha t u ==>
          !v t0 s k t1 t2.
               ((t = lam v t0) ==>
                ~(u = var s) /\ ~(u = app t1 t2)) /\
               ((u = lam v t0) ==>
                ~(t = var s) /\ ~(t = app t1 t2))``,
  HO_MATCH_MP_TAC EQC_INDUCTION THEN REPEAT STRIP_TAC THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN Cases_on `t'` THEN
  FULL_SIMP_TAC (srw_ss()) []);

val EQC_alpha_lam_thm = save_thm(
  "EQC_alpha_lam_thm",
  SIMP_RULE (srw_ss() ++ DNF_ss) [] EQC_alpha_lam_lemma)
val _ = export_rewrites ["EQC_alpha_lam_thm"]

val alpha_collapse = store_thm(
  "alpha_collapse",
  ``!t u. EQC alpha t u ==> (collapse t = collapse u)``,
  HO_MATCH_MP_TAC relationTheory.EQC_INDUCTION THEN
  SIMP_TAC (srw_ss()) [alpha_def] THEN
  Q_TAC SUFF_TAC `!y t u. ialpha y t u ==> (collapse t = collapse u)`
     THEN1 PROVE_TAC [] THEN
  HO_MATCH_MP_TAC ialpha_ind THEN
  SIMP_TAC (srw_ss()) [collapse_def, collapse_vsubst] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SIMPLE_ALPHA THEN SRW_TAC [][]);

val alpha_fv_invariant = store_thm(
  "alpha_fv_invariant",
  ``!t u. EQC alpha t u ==> (fv t = fv u)``,
  HO_MATCH_MP_TAC EQC_INDUCTION THEN SIMP_TAC (srw_ss()) [alpha_def] THEN
  Q_TAC SUFF_TAC `!y t u. ialpha y t u ==> (fv t = fv u)`
     THEN1 PROVE_TAC [] THEN
  HO_MATCH_MP_TAC ialpha_ind THEN SRW_TAC [][fv_def, fv_vsubst] THEN
  SRW_TAC [][EXTENSION] THEN PROVE_TAC []);

val capt_subst = store_thm(
  "capt_subst",
  ``!t x y z. ~(x = y) /\ ~(y IN capt z t) ==>
              (capt x (subst (var y) z t) =
                 if x = z then {} else capt x t)``,
  Induct THEN SRW_TAC [][subst_def, capt_def, fv_def, fv_vsubst] THEN
  FULL_SIMP_TAC (srw_ss()) []);

val alpha_eq_safe_subst = store_thm(
  "alpha_eq_safe_subst",
  ``!t. ?t'. EQC alpha t t' /\ (capt x t' INTER fv u = {})``,
  Induct THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
    Q.X_GEN_TAC `s` THEN Q.EXISTS_TAC `var s` THEN SRW_TAC [][capt_def],
    Q.EXISTS_TAC `app t'' t'''` THEN
    SRW_TAC [][capt_def, RIGHT_INTER_OVER_UNION] THEN
    METIS_TAC [EQC_alpha_CONG2],
    Q.X_GEN_TAC `s` THEN
    Cases_on `x IN fv t` THENL [
      Cases_on `s IN fv u` THENL [
        Q_TAC (NEW_TAC "z")
              `fv t UNION fv u UNION {s;x} UNION capt s t'` THEN
        Q.EXISTS_TAC `lam z (subst (var z) s t')` THEN
        CONJ_TAC THENL [
          MATCH_MP_TAC EQC_TRANS THEN
          Q.EXISTS_TAC `lam s t'` THEN CONJ_TAC THENL [
            PROVE_TAC [EQC_alpha_CONG],
            MATCH_MP_TAC EQC_R THEN
            SRW_TAC [][alpha_def] THEN Q.EXISTS_TAC `z` THEN
            MATCH_MP_TAC (hd (CONJUNCTS ialpha_rules)) THEN
            SRW_TAC [][] THEN PROVE_TAC [alpha_fv_invariant]
          ],
          SRW_TAC [][capt_def, capt_subst, RIGHT_INTER_OVER_UNION, SING_INTER]
        ],
        Q.EXISTS_TAC `lam s t'` THEN CONJ_TAC THENL [
          PROVE_TAC [EQC_alpha_CONG],
          SRW_TAC [][capt_def, RIGHT_INTER_OVER_UNION, SING_INTER]
        ]
      ],
      Q.EXISTS_TAC `lam s t'` THEN CONJ_TAC THENL [
        PROVE_TAC [EQC_alpha_CONG],
        SRW_TAC [][capt_def] THEN PROVE_TAC [alpha_fv_invariant]
      ]
    ]
  ]);

val LAM_INJ_ALPHA_FV = prove(
  ``~(v1 = v2) /\ (LAM v1 t1 = LAM v2 t2) ==>
    ~(v1 IN FV t2) /\ ~(v2 IN FV t1)``,
  SRW_TAC [][LAM_eq_thm] THEN SRW_TAC [][]);
val INJECTIVITY_LEMMA1 = prove(
  ``(LAM v1 t1 = LAM v2 t2) ==> (t1 = [VAR v1/v2]t2)``,
  SRW_TAC [][LAM_eq_thm] THEN SRW_TAC [][fresh_tpm_subst]);

val collapse_alpha = store_thm(
  "collapse_alpha",
  ``!t u. (collapse t = collapse u) ==> EQC alpha t u``,
  Induct THEN REPEAT GEN_TAC THEN Cases_on `u` THEN
  SRW_TAC [][collapse_def] THENL [
    PROVE_TAC [EQC_alpha_CONG2],
    REPEAT (POP_ASSUM MP_TAC) THEN
    Q_TAC SUFF_TAC
      `!t s s' t'.
          (!u. (collapse t = collapse u) ==> EQC alpha t u) /\
          (LAM s (collapse t) = LAM s' (collapse t')) ==>
          EQC alpha (lam s t) (lam s' t')` THEN1 METIS_TAC [] THEN
    REPEAT STRIP_TAC THEN
    Cases_on `s = s'` THENL [
      FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [EQC_alpha_CONG],
      `collapse t = [VAR s/s'] (collapse t')`
        by PROVE_TAC [INJECTIVITY_LEMMA1] THEN
      `~(s IN FV (collapse t')) /\ ~(s' IN FV (collapse t))`
        by PROVE_TAC [LAM_INJ_ALPHA_FV] THEN
      MATCH_MP_TAC EQC_TRANS THEN
      `?t2. EQC alpha t' t2 /\ (capt s' t2 INTER fv (var s) = {})`
         by PROVE_TAC [alpha_eq_safe_subst] THEN
      `collapse t' = collapse t2` by PROVE_TAC [alpha_collapse] THEN
      `~(s IN capt s' t2)`
          by FULL_SIMP_TAC (srw_ss() ++ COND_elim_ss) [SING_INTER, fv_def] THEN
      `[VAR s/s'] (collapse t2) = collapse (subst (var s) s' t2)`
         by METIS_TAC [collapse_vsubst] THEN
      `EQC alpha t (subst (var s) s' t2)` by METIS_TAC [] THEN
      `EQC alpha (lam s t) (lam s (subst (var s) s' t2))`
         by METIS_TAC [EQC_alpha_CONG] THEN
      `EQC alpha (lam s (subst (var s) s' t2)) (lam s' t2)`
         by (MATCH_MP_TAC EQC_SYM THEN
             MATCH_MP_TAC EQC_R THEN REWRITE_TAC [alpha_def] THEN
             Q.EXISTS_TAC `s` THEN
             MATCH_MP_TAC (hd (CONJUNCTS ialpha_rules)) THEN
             FULL_SIMP_TAC (srw_ss()) [] THEN
             PROVE_TAC [alpha_fv_invariant]) THEN
      PROVE_TAC [EQC_TRANS, EQC_SYM, EQC_alpha_CONG]
    ]
  ]);

val EQC_alpha_collapse_EQ = store_thm(
  "EQC_alpha_collapse_EQ",
  ``EQC alpha t u = (collapse t = collapse u)``,
  PROVE_TAC [collapse_alpha, alpha_collapse]);

val collapse_ONTO = store_thm(
  "collapse_ONTO",
  ``!M. ?t. collapse t = M``,
  HO_MATCH_MP_TAC simple_induction THEN METIS_TAC [collapse_def]);

val beta_ccbeta = store_thm(
  "beta_ccbeta",
  ``!t u. beta t u ==> compat_closure beta (collapse t) (collapse u)``,
  HO_MATCH_MP_TAC beta_ind THEN
  SRW_TAC [][compat_closure_rules, collapse_def] THEN
  SRW_TAC [][collapse_subst, INTER_COMM] THEN
  SRW_TAC [][cc_beta_thm] THEN PROVE_TAC []);

val gmbeta_beta = store_thm(
  "gmbeta_beta",
  ``!t u. beta (collapse t) (collapse u) ==>
          (EQC alpha O beta O EQC alpha) t u``,
  SIMP_TAC (srw_ss()) [beta_def, O_DEF] THEN REPEAT GEN_TAC THEN
  DISCH_THEN (Q.X_CHOOSE_THEN `v`
               (Q.X_CHOOSE_THEN `M`
                 (Q.X_CHOOSE_THEN `N` STRIP_ASSUME_TAC))) THEN
  `?f x. t = app f x`
     by (Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [collapse_def]) THEN
  POP_ASSUM SUBST_ALL_TAC THEN FULL_SIMP_TAC (srw_ss()) [collapse_def] THEN
  `?w t0. f = lam w t0`
     by (Cases_on `f` THEN FULL_SIMP_TAC (srw_ss()) [collapse_def]) THEN
  POP_ASSUM SUBST_ALL_TAC THEN FULL_SIMP_TAC (srw_ss()) [collapse_def] THEN
  `?t1. EQC alpha t0 t1 /\ (capt w t1 INTER fv x = {})`
     by PROVE_TAC [alpha_eq_safe_subst] THEN
  `EQC alpha (app (lam w t0) x) (app (lam w t1) x)`
     by METIS_TAC [EQC_alpha_CONG] THEN
  `beta (app (lam w t1) x) (subst x w t1)`
     by (MATCH_MP_TAC  (hd (CONJUNCTS beta_rules)) THEN
         FULL_SIMP_TAC (srw_ss()) [INTER_COMM]) THEN
  Q_TAC SUFF_TAC `EQC alpha (subst x w t1) u` THEN1 PROVE_TAC [] THEN
  ASM_SIMP_TAC (srw_ss()) [EQC_alpha_collapse_EQ, collapse_subst] THEN
  `collapse t0 = collapse t1` by PROVE_TAC [alpha_collapse] THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  Cases_on `v = w` THEN1 FULL_SIMP_TAC (srw_ss()) [] THEN
  `M = [VAR v/w] (collapse t1)` by METIS_TAC [INJECTIVITY_LEMMA1] THEN
  `~(v IN FV (collapse t1))` by METIS_TAC [LAM_INJ_ALPHA_FV] THEN
  SRW_TAC [][lemma15a]);

val beta_some_reflected = store_thm(
  "beta_some_reflected",
  ``!M N. compat_closure beta M N ==>
          ?t u. (M = collapse t) /\ (N = collapse u) /\
                beta t u``,
  HO_MATCH_MP_TAC ccbeta_ind THEN Q.EXISTS_TAC `{}` THEN SRW_TAC [][] THENL [
    `?m n. (collapse m = M) /\ (collapse n = N)`
       by METIS_TAC [collapse_ONTO] THEN
    `?m'. EQC alpha m m' /\ (capt v m' INTER fv n = {})`
       by METIS_TAC [alpha_eq_safe_subst] THEN
    MAP_EVERY Q.EXISTS_TAC [`app (lam v m') n`, `subst n v m'`] THEN
    SRW_TAC [][collapse_def, GSYM EQC_alpha_collapse_EQ, collapse_subst]
    THENL [
      METIS_TAC [EQC_alpha_collapse_EQ],
      METIS_TAC [INTER_COMM, beta_rules]
    ],
    `?n. collapse n = N'` by METIS_TAC [collapse_ONTO] THEN
    MAP_EVERY Q.EXISTS_TAC [`app t n`, `app u n`] THEN
    SRW_TAC [][collapse_def, beta_rules],
    `?m. collapse m = M` by METIS_TAC [collapse_ONTO] THEN
    MAP_EVERY Q.EXISTS_TAC [`app m t`, `app m u`] THEN
    SRW_TAC [][collapse_def, beta_rules],
    MAP_EVERY Q.EXISTS_TAC [`lam v t`, `lam v u`] THEN
    SRW_TAC [][collapse_def, beta_rules]
  ]);

val ccbeta_beta_lemma = prove(
  ``!M N. compat_closure beta M N ==>
          !t u. (M = collapse t) /\ (N = collapse u) ==>
                (EQC alpha O beta O EQC alpha) t u``,
  HO_MATCH_MP_TAC compat_closure_ind THEN
  REPEAT STRIP_TAC THEN1 METIS_TAC [gmbeta_beta] THEN
  FULL_SIMP_TAC (srw_ss()) [O_DEF] THENL [
    `?z1 m. (t = app z1 m) /\ (collapse z1 = z) /\ (collapse m = M)`
       by (Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [collapse_def]) THEN
    `?z2 n. (u = app z2 n) /\ (collapse z2 = z) /\ (collapse n = N)`
       by (Cases_on `u` THEN FULL_SIMP_TAC (srw_ss()) [collapse_def]) THEN
    `?y1 y2. EQC alpha m y1 /\ beta y1 y2 /\ EQC alpha y2 n`
       by METIS_TAC [] THEN
    `EQC alpha (app z1 m) (app z1 y1)` by METIS_TAC [EQC_alpha_CONG] THEN
    `beta (app z1 y1) (app z1 y2)` by METIS_TAC [beta_rules] THEN
    METIS_TAC [EQC_alpha_CONG2, EQC_alpha_collapse_EQ],

    `?z1 m. (t = app m z1) /\ (collapse z1 = z) /\ (collapse m = M)`
      by (Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [collapse_def]) THEN
    `?z2 n. (u = app n z2) /\ (collapse z2 = z) /\ (collapse n = N)`
      by (Cases_on `u` THEN FULL_SIMP_TAC (srw_ss()) [collapse_def]) THEN
    `?y1 y2. EQC alpha m y1 /\ beta y1 y2 /\ EQC alpha y2 n`
      by METIS_TAC [] THEN
    `EQC alpha (app m z1) (app y1 z1)` by METIS_TAC [EQC_alpha_CONG] THEN
    `beta (app y1 z1) (app y2 z1)` by METIS_TAC [beta_rules] THEN
    METIS_TAC [EQC_alpha_CONG2, EQC_alpha_collapse_EQ],

    `?s v'. (t = lam s v')`
       by (Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [collapse_def]) THEN
    POP_ASSUM SUBST_ALL_TAC THEN FULL_SIMP_TAC (srw_ss()) [collapse_def] THEN
    `?s' v''. (u = lam s' v'')`
       by (Cases_on `u` THEN FULL_SIMP_TAC (srw_ss()) [collapse_def]) THEN
    POP_ASSUM SUBST_ALL_TAC THEN FULL_SIMP_TAC (srw_ss()) [collapse_def] THEN
    `?w. EQC alpha v' w /\ (capt s w INTER fv (var v) = {})`
       by PROVE_TAC [alpha_eq_safe_subst] THEN
    `~(v IN capt s w)`
       by FULL_SIMP_TAC (srw_ss() ++ COND_elim_ss) [SING_INTER, fv_def] THEN
    `collapse v' = collapse w` by PROVE_TAC [EQC_alpha_collapse_EQ] THEN
    `M = [VAR v/s] (collapse w)` by PROVE_TAC [INJECTIVITY_LEMMA1] THEN
    `M = collapse (subst (var v) s w)` by PROVE_TAC [collapse_vsubst] THEN

    `?z. EQC alpha v'' z /\ (capt s' z INTER fv (var v) = {})`
       by PROVE_TAC [alpha_eq_safe_subst] THEN
    `~(v IN capt s' z)`
       by FULL_SIMP_TAC (srw_ss() ++ COND_elim_ss) [SING_INTER, fv_def] THEN
    `collapse v'' = collapse z` by PROVE_TAC [EQC_alpha_collapse_EQ] THEN
    `N = [VAR v/s'] (collapse z)` by PROVE_TAC [INJECTIVITY_LEMMA1] THEN
    `N = collapse (subst (var v) s' z)` by PROVE_TAC [collapse_vsubst] THEN
    `?a b. EQC alpha (subst (var v) s w) a /\ beta a b /\
           EQC alpha b (subst (var v) s' z)` by PROVE_TAC [] THEN
    `EQC alpha (lam s w) (lam v (subst (var v) s w))`
        by (Cases_on `s = v` THEN1
              SRW_TAC [][renaming_sanity1] THEN
            MATCH_MP_TAC EQC_R THEN REWRITE_TAC [alpha_def] THEN
            Q.EXISTS_TAC `v` THEN
            MATCH_MP_TAC (hd (CONJUNCTS ialpha_rules)) THEN
            ASM_SIMP_TAC (srw_ss()) [] THEN
            Q_TAC SUFF_TAC `~(v IN FV (collapse v'))` THEN1
                  PROVE_TAC [alpha_fv_invariant, FV_collapse] THEN
            PROVE_TAC [LAM_INJ_ALPHA_FV]) THEN
    `EQC alpha (lam s v') (lam s w)` by PROVE_TAC [EQC_alpha_CONG] THEN
    `EQC alpha (lam v (subst (var v) s w)) (lam v a)`
       by PROVE_TAC [EQC_alpha_CONG] THEN
    `EQC alpha (lam s v') (lam v a)` by PROVE_TAC [EQC_TRANS] THEN
    `beta (lam v a) (lam v b)` by PROVE_TAC [beta_rules] THEN
    `EQC alpha (lam v b) (lam v (subst (var v) s' z))`
       by PROVE_TAC [EQC_alpha_CONG] THEN
    `EQC alpha (lam v (subst (var v) s' z)) (lam s' z)`
       by (Cases_on `s' = v` THEN1 SRW_TAC [][renaming_sanity1] THEN
           MATCH_MP_TAC EQC_SYM THEN
           MATCH_MP_TAC EQC_R THEN REWRITE_TAC [alpha_def] THEN
           Q.EXISTS_TAC `v` THEN
           MATCH_MP_TAC (hd (CONJUNCTS ialpha_rules)) THEN
           ASM_SIMP_TAC (srw_ss()) [] THEN
           PROVE_TAC [LAM_INJ_ALPHA_FV, alpha_fv_invariant, FV_collapse]) THEN
    `EQC alpha (lam s' z) (lam s' v'')`
       by PROVE_TAC [EQC_alpha_CONG, EQC_SYM] THEN
    PROVE_TAC [EQC_TRANS]
  ]);

val ccbeta_beta = store_thm(
  "ccbeta_beta",
  ``compat_closure beta (collapse t) (collapse u) ==>
    (EQC alpha O beta O EQC alpha) t u``,
  PROVE_TAC [SIMP_RULE (bool_ss ++ DNF_ss) [] ccbeta_beta_lemma]);

val ccbeta_beta_EQ = store_thm(
  "ccbeta_beta_EQ",
  ``compat_closure beta (collapse t) (collapse u) =
    (EQC alpha O beta O EQC alpha) t u``,
  EQ_TAC THENL [
    PROVE_TAC [ccbeta_beta],
    SRW_TAC [][O_DEF] THEN
    PROVE_TAC [alpha_collapse, beta_ccbeta]
  ]);

(* ----------------------------------------------------------------------
    having established this much, confluence results about the
    quotiented type can be transferred to the raw type, using the abstract
    machinery from diagsTheory
   ---------------------------------------------------------------------- *)

open diagsTheory

val onto_collapse = store_thm(
  "onto_collapse",
  ``onto collapse``,
  SRW_TAC [][onto_def, collapse_ONTO]);

val kSound_collapse = store_thm(
  "kSound_collapse",
  ``kSound alpha collapse``,
  SIMP_TAC (srw_ss()) [kSound_def] THEN
  METIS_TAC [EQC_alpha_collapse_EQ, EQC_R]);

val kCompl_collapse = store_thm(
  "kCompl_collapse",
  ``kCompl alpha collapse``,
  SRW_TAC [][kCompl_def] THEN
  METIS_TAC [EQC_alpha_collapse_EQ, EQC_R]);

val Pres_collapse = store_thm(
  "Pres_collapse",
  ``Pres collapse beta (compat_closure beta)``,
  SRW_TAC [][O_DEF, ccbeta_beta_EQ, Pres_def] THEN
  METIS_TAC [EQC_REFL]);

val sRefl_collapse = store_thm(
  "sRefl_collapse",
  ``sRefl collapse beta (compat_closure beta)``,
  SRW_TAC [][sRefl_def] THEN
  `(?a1. b1 = collapse a1) /\ (?a2. b2 = collapse a2)`
    by METIS_TAC [collapse_ONTO] THEN
  FULL_SIMP_TAC (srw_ss()) [ccbeta_beta_EQ, O_DEF] THEN
  METIS_TAC [alpha_collapse]);


val ofree_alpha = store_thm(
  "ofree_alpha",
  ``ofree alpha``,
  REWRITE_TAC [ofree_def] THEN
  HO_MATCH_MP_TAC EQC_INDUCTION THEN REPEAT CONJ_TAC THENL [
    METIS_TAC [RTC_RULES],
    METIS_TAC [RTC_RULES],
    METIS_TAC [TC_RC_EQNS, alpha_sym, symmetric_RC, symmetric_TC,
               symmetric_def],
    METIS_TAC [RTC_RTC]
  ]);

val aRefl_eq_sRefl_lambda = prove(
  ``aRefl collapse (RTC (beta RUNION alpha)) (RTC (compat_closure beta)) =
    sRefl collapse (RTC (beta RUNION alpha)) (RTC (compat_closure beta))``,
  METIS_TAC [onto_collapse, kCompl_collapse, ofree_alpha, note_lemma9]);

val aRefl_collapse_RTC = prove(
  ``aRefl collapse (RTC (beta RUNION alpha)) (RTC (compat_closure beta))``,
  REWRITE_TAC [aRefl_eq_sRefl_lambda] THEN
  METIS_TAC [note_prop10_1, sRefl_collapse, onto_collapse, kCompl_collapse,
             ofree_alpha]);

val Pres_collapse_RTC = store_thm(
  "Pres_collapse_RTC",
  ``Pres collapse (RTC (beta RUNION alpha)) (RTC (compat_closure beta))``,
  SRW_TAC [][onto_collapse, Pres_structure_RTC, Pres_collapse,
             kSound_collapse]);

val collapse_preserves_diagrams = store_thm(
  "collapse_preserves_diagrams",
  ``!Fa G. eval Fa G (\i. RTC (beta RUNION alpha)) =
           eval Fa G (\i. RTC (compat_closure beta))``,
  MATCH_MP_TAC diagram_preservation THEN Q.EXISTS_TAC `collapse` THEN
  SRW_TAC [][aRefl_collapse_RTC, Pres_collapse_RTC, onto_collapse]);

val raw_diamond = store_thm(
  "raw_diamond",
  ``diamond (RTC (beta RUNION alpha))``,
  SRW_TAC [][GSYM diamond_eval, collapse_preserves_diagrams] THEN
  SRW_TAC [][diamond_eval] THEN
  METIS_TAC [chap3Theory.beta_CR, chap3Theory.CR_def]);

val _ = export_theory();
