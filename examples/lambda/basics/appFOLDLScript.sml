(* ========================================================================== *)
(* FILE    : appFOLDLScript.sml                                               *)
(* TITLE   : List-based Constructors (LAMl and appstar) of Lambda Terms       *)
(*                                                                            *)
(* AUTHORS : 2005-2011 Michael Norrish                                        *)
(*         : 2023-2024 Michael Norrish and Chun Tian                          *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory listTheory rich_listTheory pred_setTheory finite_mapTheory
     hurdUtils listLib pairTheory;

open termTheory binderLib basic_swapTheory NEWLib;

val _ = new_theory "appFOLDL"

val _ = set_fixity "@*" (Infixl 901)
val _ = Unicode.unicode_version { u = "··", tmnm = "@*"}

Overload "@*" = “\f (args:term list). FOLDL APP f args”

Theorem appstar_empty[simp] :
    M @* [] = M
Proof
    rw [FOLDL]
QED

(* NOTE: no more [simp] for this theorem *)
Theorem appstar_thm :
    (M @* [] = M) /\
    (M @* (h::t) = M @@ h @* t)
Proof
    rw [FOLDL]
QED

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

Theorem lam_eq_appstar[simp]:
  ∀args f. (LAM v t = f ·· args) ⇔ (args = []) ∧ (f = LAM v t)
Proof
  Induct THEN SRW_TAC [][] THEN METIS_TAC []
QED

val app_eq_varappstar = store_thm(
  "app_eq_varappstar",
  ``∀M N args.
       (M @@ N = VAR v ·· args) ⇔ args ≠ [] ∧ (M = VAR v ·· FRONT args) ∧
                                  (N = LAST args)``,
  SRW_TAC [][app_eq_appstar]);

val take_lemma = prove(
  ``∀l n. 0 < n ∧ n ≤ LENGTH l ⇒ TAKE n l ≠ []``,
  Induct THEN SRW_TAC [ARITH_ss][]);

val _ = augment_srw_ss[rewrites[TAKE_def, DROP_def]];

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

Theorem app_eq_appstar_SNOC:
    t @* Ms = M1 @@ M2 ⇔
    (∃Ms0. Ms = SNOC M2 Ms0 ∧ t @* Ms0 = M1) ∨ Ms = [] ∧ t = M1 @@ M2
Proof
  Cases_on ‘Ms’ using listTheory.SNOC_CASES >> simp[] >> metis_tac[]
QED

Theorem appstar_CONS :
    M @@ N @* Ns = M @* (N::Ns)
Proof
    ‘N::Ns = [N] ++ Ns’ by rw []
 >> ‘M @* [N] = M @@ N’ by rw []
 >> rw [appstar_APPEND]
QED

Theorem appstar_SING[simp] :
    M @* [N] = M @@ N
Proof
    rw [GSYM appstar_CONS]
QED

Theorem ssub_appstar :
    !Ns. fm ' (M @* Ns) = (fm ' M) @* MAP (ssub fm) Ns
Proof
    SNOC_INDUCT_TAC
 >> rw [appstar_SNOC, MAP_SNOC]
QED

Theorem appstar_SUB :
    !args. [N/v] (t @* args) = [N/v] t @* MAP [N/v] args
Proof
    SNOC_INDUCT_TAC
 >> rw [appstar_SNOC, MAP_SNOC]
QED

(* |- !args t sub. t @* args ISUB sub = (t ISUB sub) @* MAP (\t. t ISUB sub) args *)
Theorem appstar_ISUB = FOLDL_APP_ISUB

Theorem FV_appstar :
    !M Ns. FV (M @* Ns) = FV M UNION (BIGUNION (IMAGE FV (set Ns)))
Proof
    Q.X_GEN_TAC ‘M’
 >> SNOC_INDUCT_TAC
 >> simp[appstar_SNOC, MAP_SNOC]
 >> Q.X_GEN_TAC ‘N’
 >> simp [LIST_TO_SET_SNOC] >> SET_TAC []
QED

(* A special case of FV_appstar *)
Theorem FV_appstar_MAP_VAR[simp] :
    FV (M @* MAP VAR vs) = FV M UNION set vs
Proof
    rw [FV_appstar]
 >> Suff ‘BIGUNION (IMAGE FV (set (MAP VAR vs))) = set vs’ >- rw []
 >> rw [Once EXTENSION, IN_BIGUNION_IMAGE]
 >> reverse EQ_TAC >> rpt STRIP_TAC
 >- (Q.EXISTS_TAC ‘VAR x’ >> rw [MEM_MAP])
 >> rename1 ‘x IN FV t’
 >> gs [MEM_MAP]
QED

(*---------------------------------------------------------------------------*
 *  LAMl (was in standardisationTheory)
 *---------------------------------------------------------------------------*)

Overload "LAMl" = “\vs (t :term). FOLDR LAM t vs”

(* |- !e l1 l2. LAMl (l1 ++ l2) e = LAMl l1 (LAMl l2 e) *)
Theorem LAMl_APPEND = Q.ISPEC ‘LAM’ FOLDR_APPEND

Theorem LAMl_thm[simp]:
  (LAMl [] M = M) /\
  (LAMl (h::t) M = LAM h (LAMl t M))
Proof SRW_TAC [][]
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
    !M N v vs. ~MEM v vs /\ DISJOINT (set vs) (FV N) ==>
              ([N/v] (LAMl vs M) = LAMl vs ([N/v] M))
Proof
    rpt STRIP_TAC
 >> Induct_on ‘vs’ >> rw []
QED

Theorem LAMl_ISUB :
    !ss vs M. DISJOINT (set vs) (FVS ss) /\
              DISJOINT (set vs) (DOM ss) ==>
             ((LAMl vs M) ISUB ss = LAMl vs (M ISUB ss))
Proof
    Induct_on ‘ss’ >- rw [DOM_DEF, FVS_DEF]
 >> simp [FORALL_PROD, DOM_ALT_MAP_SND]
 >> qx_genl_tac [‘P’, ‘v’]
 >> rw [FVS_DEF, DISJOINT_UNION]
 >> Know ‘[P/v] (LAMl vs M) = LAMl vs ([P/v] M)’
 >- (MATCH_MP_TAC LAMl_SUB \\
     simp [Once DISJOINT_SYM])
 >> Rewr'
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> simp [Once DISJOINT_SYM, DOM_ALT_MAP_SND]
QED

(* LAMl_ssub = ssub_LAM + LAMl_SUB *)
Theorem LAMl_ssub :
    !vs fm t. DISJOINT (FDOM fm) (set vs) /\
             (!y. y IN FDOM fm ==> DISJOINT (FV (fm ' y)) (set vs)) ==>
              fm ' (LAMl vs t) = LAMl vs (fm ' t)
Proof
    Induct_on ‘vs’ >> rw []
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

Theorem LAMl_ALPHA_ssub :
    !vs vs' M.
       LENGTH vs = LENGTH vs' /\ ALL_DISTINCT vs /\ ALL_DISTINCT vs' /\
       DISJOINT (LIST_TO_SET vs') (LIST_TO_SET vs UNION FV M) ==>
       LAMl vs M = LAMl vs' ((FEMPTY |++ ZIP (vs, MAP VAR vs')) ' M)
Proof
    rpt STRIP_TAC
 >> Suff ‘(FEMPTY |++ ZIP (vs, MAP VAR vs')) ' M =
          M ISUB REVERSE (ZIP (MAP VAR vs', vs))’
 >- (Rewr' >> MATCH_MP_TAC LAMl_ALPHA >> art [])
 (* applying fromPairs_ISUB *)
 >> REWRITE_TAC [GSYM fromPairs_def]
 >> MATCH_MP_TAC fromPairs_ISUB
 >> fs [DISJOINT_UNION']
 >> rw [EVERY_MEM, MEM_MAP]
 >> simp []
 >> Q.PAT_X_ASSUM ‘DISJIOINT (set vs') (set vs)’ MP_TAC
 >> rw [DISJOINT_ALT]
QED

Theorem LAMl_SNOC[simp] :
    LAMl (SNOC v vs) t = LAMl vs (LAM v t)
Proof
    rw [FOLDR_SNOC]
QED

Theorem LAMl_eq_rewrite[simp] :
    LAMl vs t1 = LAMl vs t2 <=> t1 = t2
Proof
    Induct_on ‘vs’ >> rw [LAM_eq_thm]
QED

Theorem LAMl_RNEWS_11 :
    !X r n1 n2 y1 y2. FINITE X ==>
       (LAMl (RNEWS r n1 X) (VAR y1) =
        LAMl (RNEWS r n2 X) (VAR y2) <=> n1 = n2 /\ y1 = y2)
Proof
    rpt STRIP_TAC
 >> reverse EQ_TAC >- (STRIP_TAC >> fs [])
 >> Q_TAC (RNEWS_TAC (“vs1 :string list”, “r :num”, “n1 :num”)) ‘X’
 >> Q_TAC (RNEWS_TAC (“vs2 :string list”, “r :num”, “n2 :num”)) ‘X’
 >> DISCH_TAC
 >> Know ‘size (LAMl vs1 (VAR y1)) = size (LAMl vs2 (VAR y2))’
 >- (POP_ORW >> rw [])
 >> simp [] (* n1 = n2 *)
 >> DISCH_TAC
 >> ‘vs1 = vs2’ by simp [Abbr ‘vs1’, Abbr ‘vs2’]
 >> fs []
QED

(*---------------------------------------------------------------------------*
 *  funpow for lambda terms (using arithmeticTheory.FUNPOW)
 *---------------------------------------------------------------------------*)

Overload funpow = “\f. FUNPOW (APP (f :term))”

Theorem FV_FUNPOW :
    !(f :term) x n. FV (FUNPOW (APP f) n x) =
                    if n = 0 then FV x else FV f UNION FV x
Proof
    rpt STRIP_TAC
 >> Q.SPEC_TAC (‘n’, ‘i’)
 >> Cases_on ‘i’ >- rw [FUNPOW]
 >> simp []
 >> Induct_on ‘n’ >- rw [FUNPOW]
 >> fs [FUNPOW_SUC]
 >> SET_TAC []
QED

(* moved here from churchnumScript.sml *)
Theorem size_funpow :
    size (FUNPOW (APP f) n x) = (size f + 1) * n + size x
Proof
  Induct_on `n` THEN
  SRW_TAC [ARITH_ss][FUNPOW_SUC, LEFT_ADD_DISTRIB, MULT_CLAUSES]
QED

val _ = export_theory ()
val _ = html_theory "appFOLDL";
