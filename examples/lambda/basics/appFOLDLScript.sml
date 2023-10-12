open HolKernel Parse boolLib bossLib;

open arithmeticTheory listTheory pred_setTheory hurdUtils;

open termTheory binderLib;

val _ = new_theory "appFOLDL"

val _ = set_trace "Unicode" 1

val _ = set_fixity "@*" (Infixl 901)
val _ = Unicode.unicode_version { u = "··", tmnm = "@*"}
val _ = overload_on ("@*", ``λf (args:term list). FOLDL APP f args``)

Theorem var_eq_appstar[simp]:
  VAR s = f ·· args ⇔ args = [] ∧ f = VAR s
Proof
  Cases_on `args` using SNOC_CASES >> simp[FOLDL_SNOC] >> metis_tac[]
QED

val app_eq_appstar = store_thm(
  "app_eq_appstar",
  ``∀args f M N.
       (M @@ N = f ·· args) ⇔
       (args = []) ∧ (f = M @@ N) ∨
       (args ≠ []) ∧ (M = f ·· FRONT args) ∧ (N = LAST args)``,
  Induct THEN SRW_TAC [][] THEN1 METIS_TAC [] THEN
  Cases_on `args` THEN SRW_TAC [][] THEN1 METIS_TAC []);

val lam_eq_appstar = store_thm(
  "lam_eq_appstar",
  ``∀args f. (LAM v t = f ·· args) ⇔ (args = []) ∧ (f = LAM v t)``,
  Induct THEN SRW_TAC [][] THEN METIS_TAC []);

val app_eq_varappstar = store_thm(
  "app_eq_varappstar",
  ``∀M N args.
       (M @@ N = VAR v ·· args) ⇔ args ≠ [] ∧ (M = VAR v ·· FRONT args) ∧
                                  (N = LAST args)``,
  SRW_TAC [][app_eq_appstar]);

val take_lemma = prove(
  ``∀l n. 0 < n ∧ n ≤ LENGTH l ⇒ TAKE n l ≠ []``,
  Induct THEN SRW_TAC [ARITH_ss][]);

val _ = augment_srw_ss[rewrites[listTheory.TAKE_def,listTheory.DROP_def]];

val FRONT_TAKE = store_thm(
  "FRONT_TAKE",
  ``∀l n. 0 < n ∧ n ≤ LENGTH l ⇒ (FRONT (TAKE n l) = TAKE (n - 1) l)``,
  Induct THEN SRW_TAC [ARITH_ss][] >>
  `0 < n - 1 ∧ n - 1 ≤ LENGTH l` by DECIDE_TAC THEN
  SRW_TAC [][listTheory.FRONT_DEF] THENL [
    fs [],
    `(n - 1) - 1 = n - 2` by DECIDE_TAC THEN
    SRW_TAC [][]
  ]);

val DROP_PREn_LAST_CONS = store_thm(
  "DROP_PREn_LAST_CONS",
  ``∀t n. 0 < n ∧ n ≤ LENGTH t ⇒
          (DROP (n - 1) t = LAST (TAKE n t) :: DROP n t)``,
  Induct THEN SRW_TAC [ARITH_ss][] THENL [
    `n = 1` by DECIDE_TAC THEN SRW_TAC [][],
    `n = 1` by DECIDE_TAC THEN SRW_TAC [][],
    `(t = []) ∨ ∃h t0. t = h :: t0` by METIS_TAC [listTheory.list_CASES] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []
  ]);

val appstar_eq_appstar = store_thm(
  "appstar_eq_appstar",
  ``∀a₁ f₁ f₂ a₂.
       (f₁ ·· a₁ = f₂ ·· a₂) ⇔
         (a₁ = a₂) ∧ (f₁ = f₂) ∨
         (LENGTH a₁ < LENGTH a₂ ∧
          (f₁ = f₂ ·· TAKE (LENGTH a₂ - LENGTH a₁) a₂) ∧
          (a₁ = DROP (LENGTH a₂ - LENGTH a₁) a₂)) ∨
         (LENGTH a₂ < LENGTH a₁ ∧
          (f₂ = f₁ ·· TAKE (LENGTH a₁ - LENGTH a₂) a₁) ∧
          (a₂ = DROP (LENGTH a₁ - LENGTH a₂) a₁))``,
  Induct THEN SRW_TAC [][] THENL [
    Cases_on `a₂` THEN SRW_TAC [][rich_listTheory.BUTFIRSTN_LENGTH_NIL],
    Cases_on `a₂` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THENL [
      `LENGTH a₁ = LENGTH t` by DECIDE_TAC THEN
      SRW_TAC [ARITH_ss][ADD1] THEN EQ_TAC THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],

      SRW_TAC [ARITH_ss][ADD1] THEN EQ_TAC THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THENL [
        FULL_SIMP_TAC (srw_ss()) [app_eq_appstar] THEN fs[] >>
        SRW_TAC [][] THEN DISJ2_TAC THEN
        SRW_TAC [ARITH_ss][FRONT_TAKE] THEN
        `LENGTH t - (LENGTH a₁ + 1) = LENGTH t - LENGTH a₁ - 1`
           by DECIDE_TAC THEN
        Q.ABBREV_TAC `N = LENGTH t - LENGTH a₁` THEN
        ASM_SIMP_TAC bool_ss [] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
        MATCH_MP_TAC DROP_PREn_LAST_CONS THEN
        Q.UNABBREV_TAC `N` THEN DECIDE_TAC,

        DISJ2_TAC THEN SRW_TAC [][app_eq_appstar] THENL [
          DISJ2_TAC THEN SRW_TAC [ARITH_ss][FRONT_TAKE] THENL [
            strip_tac >> fs[],
            Q.ABBREV_TAC `N = LENGTH t - LENGTH a₁` THEN
            `0 < N ∧ N ≤ LENGTH t` by SRW_TAC [ARITH_ss][Abbr`N`] THEN
            `LENGTH t - (LENGTH a₁ + 1) = N - 1`
               by SRW_TAC [ARITH_ss][Abbr`N`] THEN
            FULL_SIMP_TAC (srw_ss()) [DROP_PREn_LAST_CONS]
          ],

          Q.ABBREV_TAC `N = LENGTH t - LENGTH a₁` THEN
          `0 < N ∧ N ≤ LENGTH t` by SRW_TAC [ARITH_ss][Abbr`N`] THEN
          `LENGTH t - (LENGTH a₁ + 1) = N - 1`
            by SRW_TAC [ARITH_ss][Abbr`N`] THEN
          FULL_SIMP_TAC (srw_ss()) [DROP_PREn_LAST_CONS]
        ]
      ]
    ],

    Cases_on `a₂` THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THENL [
      SRW_TAC [][rich_listTheory.BUTFIRSTN_LENGTH_NIL] THEN
      Cases_on `a₁` THEN SRW_TAC [][] THEN METIS_TAC [],
      Cases_on `LENGTH a₁ = LENGTH t + 1` THENL [
        SRW_TAC [][ADD1] THEN EQ_TAC THEN
        SRW_TAC [][ADD1, rich_listTheory.BUTFIRSTN_LENGTH_NIL] THEN
        FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [],

        `LENGTH t + 1 < LENGTH a₁` by DECIDE_TAC THEN
        SRW_TAC [ARITH_ss][ADD1, EQ_IMP_THM] THEN
        FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []
      ]
    ]
  ]);

Theorem varappstar_11[simp]:
  (VAR v₁ ·· a₁ = VAR v₂ ·· a₂) ⇔ (v₁ = v₂) ∧ (a₁ = a₂)
Proof
  SRW_TAC [][appstar_eq_appstar, var_eq_appstar] THEN
  csimp[DECIDE ``(x:num) < y ==> ~(y <= x)``] >> csimp[] >> metis_tac[]
QED


Theorem appstar_APPEND:
  x ·· (Ms1 ++ Ms2) = (x ·· Ms1) ·· Ms2
Proof
  qid_spec_tac ‘x’ >> Induct_on ‘Ms1’ >> simp[]
QED

Theorem appstar_SNOC[simp]:
  x ·· (SNOC M Ms) = (x ·· Ms) @@ M
Proof
  simp[appstar_APPEND, SNOC_APPEND]
QED

Theorem appstar_CONS :
    M @@ N @* Ns = M @* (N::Ns)
Proof
    ‘N::Ns = [N] ++ Ns’ by rw []
 >> ‘M @* [N] = M @@ N’ by rw []
 >> rw [appstar_APPEND]
QED

Theorem appstar_EQ_LAM[simp]:
  x ·· Ms = LAM v M ⇔ Ms = [] ∧ x = LAM v M
Proof
  qid_spec_tac ‘x’ >> Induct_on ‘Ms’ >> simp[]
QED

Theorem ssub_appstar :
    fm ' (M @* Ns) = (fm ' M) @* MAP (ssub fm) Ns
Proof
    Induct_on ‘Ns’ using SNOC_INDUCT >> simp[appstar_SNOC, MAP_SNOC]
QED

Theorem FV_appstar :
    !M Ns. FV (M @* Ns) = FV M UNION (BIGUNION (IMAGE FV (set Ns)))
Proof
    Q.X_GEN_TAC ‘M’
 >> Induct_on ‘Ns’ using SNOC_INDUCT >> simp[appstar_SNOC, MAP_SNOC]
 >> Q.X_GEN_TAC ‘N’
 >> simp [LIST_TO_SET_SNOC] >> SET_TAC []
QED

(*---------------------------------------------------------------------------*
 *  LAMl (was in standardisationTheory)
 *---------------------------------------------------------------------------*)

Definition LAMl_def:
  LAMl vs (t : term) = FOLDR LAM t vs
End

Theorem LAMl_thm[simp]:
  (LAMl [] M = M) /\
  (LAMl (h::t) M = LAM h (LAMl t M))
Proof SRW_TAC [][LAMl_def]
QED

Theorem LAMl_11[simp]:
  !vs. (LAMl vs x = LAMl vs y) = (x = y)
Proof
  Induct THEN SRW_TAC [][]
QED

Theorem size_LAMl[simp]:
  !vs. size (LAMl vs M) = LENGTH vs + size M
Proof
  Induct THEN SRW_TAC [numSimps.ARITH_ss][size_thm]
QED

Theorem FV_LAMl :
    !vs M. FV (LAMl vs M) = FV M DIFF LIST_TO_SET vs
Proof
  Induct THEN SRW_TAC [][] THEN
  SIMP_TAC (srw_ss()) [EXTENSION] THEN PROVE_TAC []
QED

Theorem LAMl_eq_VAR[simp]:
  (LAMl vs M = VAR v) ⇔ (vs = []) ∧ (M = VAR v)
Proof
  Cases_on ‘vs’ >> simp[]
QED

Theorem LAMl_eq_APP[simp]:
  (LAMl vs M = N @@ P) ⇔ (vs = []) ∧ (M = N @@ P)
Proof
  Cases_on ‘vs’ >> simp[]
QED

Theorem LAMl_eq_appstar:
  (LAMl vs M = N ·· Ns) ⇔
    (vs = []) ∧ (M = N ·· Ns) ∨ (Ns = []) ∧ (N = LAMl vs M)
Proof
  Cases_on ‘vs’ >> simp[] >> Cases_on ‘Ns’ >> simp[] >>
  metis_tac[]
QED

Theorem LAMl_SUB :
    !M N v vs. ALL_DISTINCT vs /\ ~MEM v vs /\ (FV N = {}) ==>
              ([N/v] (LAMl vs M) = LAMl vs ([N/v] M))
Proof
    rpt STRIP_TAC
 >> Induct_on ‘vs’ >> rw []
QED

Theorem tpm_LAMl:
  tpm π (LAMl vs M) = LAMl (listpm string_pmact π vs) (tpm π M)
Proof
  Induct_on ‘vs’ >> simp[]
QED

Theorem tpm_appstar:
  tpm π (M ·· Ms) = tpm π M ·· listpm term_pmact π Ms
Proof
  qid_spec_tac ‘M’ >> Induct_on ‘Ms’ >> simp[]
QED

Theorem LAMl_vsub :
    !vs u v M.
        ~MEM u vs /\ ~MEM v vs ==>
        ([VAR v/u] (LAMl vs M) = LAMl vs ([VAR v/u] M))
Proof
  Induct THEN SRW_TAC [][] THEN
  Q_TAC (NEW_TAC "z") `LIST_TO_SET vs UNION {h;v;u} UNION FV (LAMl vs M) UNION
                       FV (LAMl vs ([VAR v/u] M))` THEN
  `LAM h (LAMl vs M) = LAM z ([VAR z/h] (LAMl vs M))`
     by SRW_TAC [][SIMPLE_ALPHA] THEN
  `LAM h (LAMl vs ([VAR v/u] M)) = LAM z ([VAR z/h] (LAMl vs ([VAR v/u] M)))`
     by SRW_TAC [][SIMPLE_ALPHA] THEN
  SRW_TAC [][SUB_THM]
QED

Theorem LAMl_vsub_disappears :
   !vs u v M. MEM u vs ==> ([VAR v/u] (LAMl vs M) = LAMl vs M)
Proof
  Induct THEN SRW_TAC [][] THENL [
    SRW_TAC [][SUB_THM, lemma14b],
    `~(u IN FV (LAMl vs M))` by SRW_TAC [][FV_LAMl] THEN
    `LAM h (LAMl vs M) = LAM u ([VAR u/h] (LAMl vs M))`
       by SRW_TAC [][SIMPLE_ALPHA] THEN
    SRW_TAC [][SUB_THM, lemma14b]
  ]
QED

Theorem LAMl_ALPHA :
    !vs vs' M.
       (LENGTH vs = LENGTH vs') /\ ALL_DISTINCT vs' /\
       DISJOINT (LIST_TO_SET vs') (LIST_TO_SET vs UNION FV M) ==>
       (LAMl vs M = LAMl vs' (M ISUB REVERSE (ZIP(MAP VAR vs', vs))))
Proof
  Induct THENL [
    SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [ISUB_def],
    SRW_TAC [][] THEN
    Cases_on `vs'` THEN
    FULL_SIMP_TAC (srw_ss()) [DISJ_IMP_THM, FORALL_AND_THM] THEN
    `~(h' IN LIST_TO_SET vs) /\ ~(h' IN FV M) /\
     DISJOINT (LIST_TO_SET vs) (LIST_TO_SET t) /\
     DISJOINT (FV M) (LIST_TO_SET t)`
        by PROVE_TAC [DISJOINT_INSERT, DISJOINT_SYM] THEN
    Q_TAC SUFF_TAC `~(h' IN FV (LAMl vs M)) /\
                    (LAMl t (M ISUB APPEND (REVERSE (ZIP (MAP VAR t, vs)))
                                           [(VAR h',h)]) =
                     [VAR h'/h] (LAMl vs M))` THEN1
       SRW_TAC [][SIMPLE_ALPHA] THEN
    ASM_SIMP_TAC (srw_ss()) [FV_LAMl] THEN
    FIRST_X_ASSUM (Q.SPECL_THEN [`t`, `M`] MP_TAC) THEN
    ASM_SIMP_TAC (srw_ss()) [] THEN
    DISCH_THEN (K ALL_TAC) THEN
    SRW_TAC [][LAMl_vsub, SUB_ISUB_SINGLETON, ISUB_APPEND]
  ]
QED

val _ = export_theory ()
val _ = html_theory "appFOLDL";
