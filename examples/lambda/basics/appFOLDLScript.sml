open HolKernel Parse boolLib bossLib

open arithmeticTheory listTheory
open termTheory

fun Store_thm(trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

val _ = new_theory "appFOLDL"

val _ = set_trace "Unicode" 1

val _ = set_fixity "@*" (Infixl 901)
val _ = Unicode.unicode_version { u = "··", tmnm = "@*"}
val _ = overload_on ("@*", ``λf (args:term list). FOLDL APP f args``)

val var_eq_appstar = store_thm(
  "var_eq_appstar",
  ``(VAR s = f ·· args) ⇔ (args = []) ∧ (f = VAR s)``,
  Induct_on `args` THEN SRW_TAC [][] THENL [
    METIS_TAC [],
    MAP_EVERY Q.ID_SPEC_TAC [`f`,`h`] THEN POP_ASSUM (K ALL_TAC) THEN
    Induct_on `args` THEN SRW_TAC [][]
  ]);

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

Theorem appstar_SNOC:
  x ·· Ms @@ M = x ·· (Ms ++ [M])
Proof
  simp[appstar_APPEND]
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
    Q.ID_SPEC_TAC ‘Ns’
 >> HO_MATCH_MP_TAC SNOC_INDUCT
 >> rw [SNOC_APPEND, SYM appstar_SNOC]
QED

val _ = export_theory ()
