open HolKernel boolLib Parse bossLib
open binderLib nomsetTheory metisLib termTheory contextlistsTheory
open chap3Theory
open sortingTheory
open appFOLDLTheory standardisationTheory

val _ = new_theory "stt";

val _ = remove_ovl_mapping "B" {Name="B", Thy="chap2"}

(* define simple types, the "funspace" constructor will get to be written
   as infix "-->".
*)
Datatype: stype = base | funspace stype stype
End

Overload "-->" = “funspace”
val _ = Unicode.unicode_version{u = Unicode.UChar.rightarrow, tmnm = "-->"}

(* set up parsing/pretty-printing for the typing relation.
   Can't use ":" to the right of the turnstile, because it's already taken
   for HOL's typing, so use "-:" instead, which is ugly. *)

val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 425),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "|-", BreakSpace(1, 0),
                                 BeginFinalBlock(PP.INCONSISTENT, 2),
                                 TM, HardSpace 1, TOK "-:", BreakSpace(1,0)],
                  term_name = "hastype"}

(* this Unicode version will be preferred *)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 425),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "⊢", BreakSpace(1, 0),
                                 BeginFinalBlock(PP.INCONSISTENT, 2),
                                 TM, HardSpace 1, TOK "⦂", BreakSpace(1,0)],
                  term_name = "hastype"}

(* inductive definition of typing relation *)
Inductive hastype:
  (∀s A Γ.
      valid_ctxt Γ ∧ MEM (s,A) Γ
        ⇒
      Γ ⊢ VAR s ⦂ A) ∧

  (∀m n A B Γ.
      Γ ⊢ m ⦂ A → B ∧ Γ ⊢ n ⦂ A
        ⇒
      Γ ⊢ m @@ n ⦂ B) ∧

  (∀x m A B Γ.
     (x,A) :: Γ ⊢ m ⦂ B
       ⇒
     Γ ⊢ (LAM x m:term) ⦂ A → B)
End

val _ = add_rule { term_name = "·",
                   block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                   paren_style = OnlyIfNecessary,
                   fixity = Infixl 600,
                   pp_elements = [TOK "·"]}

Overload "·" = “tpm”
Overload "·" = “lswapstr”
Overload "·" = “ctxtswap”

val _ = set_fixity "#" (Infix(NONASSOC, 450))
Overload "#" = “λv Γ. v ∉ ctxtFV Γ”
Overload "#" = “λv M:term. v ∉ FV M”

(* typing relation respects permutation *)
Theorem hastype_swap:
  ∀Γ m τ. Γ ⊢ m ⦂ τ ⇒ ∀π. π·Γ ⊢ π·m ⦂ τ
Proof
  Induct_on ‘hastype’ >> rw[] >>
  METIS_TAC [valid_ctxt_swap, MEM_ctxtswap, hastype_rules]
QED

Theorem hastype_swap_eqn:
  Γ ⊢ π·m ⦂ A <=> π⁻¹ · Γ ⊢ m ⦂ A
Proof METIS_TAC [hastype_swap, pmact_inverse]
QED

Theorem hastype_valid_ctxt:
  ∀Γ m A. Γ ⊢ m ⦂ A ⇒ valid_ctxt Γ
Proof
  Induct_on ‘hastype’ >> rw[]
QED

Theorem ctxtswap_fresh_cons:
  x # (π·(G:'a ctxt)) ∧ y # (π·G) ⇒ (((x,y)::π)·G = π·G)
Proof
  METIS_TAC [pmact_decompose, supp_fresh, listTheory.APPEND]
QED

Theorem hastype_bvc_ind:
  ∀P fv.
    (∀x. FINITE (fv x)) ∧
    (∀G s A x. valid_ctxt G ∧ MEM (s,A) G ⇒ P G (VAR s) A x) ∧
    (∀G m n A B x.
       (∀y. P G m (A → B) y) ∧ (∀y. P G n A y) ∧
       G ⊢ m ⦂ A → B ∧ G ⊢ n ⦂ A
       ⇒
       P G (m @@ n) B x) ∧
    (∀G v m A B x. (∀y. P ((v,A)::G) m B y) ∧ v ∉ fv x ∧ v # G ∧
                   (v,A) :: G ⊢ m ⦂ B
                   ⇒
                   P G (LAM v m) (A → B) x) ⇒
    ∀G m A. G ⊢ m ⦂ A ⇒ ∀x. P G m A x
Proof
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC ‘∀G m A. G ⊢ m ⦂ A ⇒ ∀x π. P (π·G) (π·m) A x’
        THEN1 METIS_TAC [pmact_nil] THEN
  Induct_on ‘hastype’ >> SRW_TAC [][hastype_rules] THENL [
    METIS_TAC [hastype_swap],
    rename [‘P (π·G) (LAM (π·v) (π·m)) (A → B) c’] THEN
    Q_TAC (NEW_TAC "z") ‘(π·v) INSERT ctxtFV (π·G) ∪ FV (π·m) ∪ fv c’ THEN
    ‘LAM (π·v) (π·m) = LAM z ([(z,π·v)]·(π·m))’ by SRW_TAC [][tpm_ALPHA] THEN
    POP_ASSUM SUBST1_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ‘valid_ctxt ((v,A)::G)’ by METIS_TAC [hastype_valid_ctxt] THEN
    ‘v # G’ by FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THENL [
      SRW_TAC [][GSYM pmact_decompose] THEN
      Q_TAC SUFF_TAC
         ‘((z,A) :: (π·G) = (([(z,π·v)] ++ π)·v,A) :: ([(z,π·v)] ++ π)·G) ∧
          (((z,π·v)::π) · m = ([(z,π·v)] ++ π) · m)’
      THEN1 (DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC) THEN
             FIRST_X_ASSUM MATCH_ACCEPT_TAC) THEN
      SRW_TAC [][GSYM pmact_decompose] THEN
      SRW_TAC [][ctxtswap_fresh_cons],
      SRW_TAC [][hastype_swap_eqn, pmact_decompose, ctxtswap_fresh]
    ]
  ]
QED

Theorem hastype_indX =
  (Q.GEN `P` o Q.GEN `X` o SIMP_RULE bool_ss [] o
   Q.SPECL [`λG M t x. P G M t`, `λx. X`]) hastype_bvc_ind

val _ = update_induction hastype_indX

Theorem hastype_lam_inv:
  v # Γ ⇒
      (Γ ⊢ LAM v M ⦂ τ ⇔ ∃τ₁ τ₂. ((v,τ₁)::Γ) ⊢ M ⦂ τ₂ ∧ τ = τ₁ → τ₂)
Proof
  SRW_TAC [][LAM_eq_thm, Once hastype_cases] THEN SRW_TAC [][EQ_IMP_THM] THENL [
    rename [‘(v,τ₁)::Γ ⊢ [(v,x)] · m ⦂ τ₂’] THEN
    ‘[(v,x)] · ((x,τ₁) :: Γ) ⊢ [(v,x)] · m ⦂ τ₂’ by rw[hastype_swap] THEN
    POP_ASSUM MP_TAC THEN
    ‘valid_ctxt ((x,τ₁):: Γ)’ by METIS_TAC [hastype_valid_ctxt] THEN
    ‘x # Γ’ by FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][ctxtswap_fresh],
    METIS_TAC []
  ]
QED

Theorem hastype_var_inv[simp]:
  Γ ⊢ VAR v ⦂ τ ⇔ MEM (v,τ) Γ ∧ valid_ctxt Γ
Proof
  SRW_TAC [][Once hastype_cases] THEN METIS_TAC []
QED

Theorem hastype_app_inv:
  Γ ⊢ M @@ N ⦂ τ₂ ⇔ ∃τ₁. Γ ⊢ M ⦂ τ₁ → τ₂ ∧ Γ ⊢ N ⦂ τ₁
Proof
  SRW_TAC [][Once hastype_cases]
QED

Theorem weakening:
  ∀Γ m τ. Γ ⊢ m ⦂ τ ⇒ ∀Δ. valid_ctxt Δ ∧ Γ ⊆ Δ ⇒ Δ ⊢ m ⦂ τ
Proof
  Induct_on ‘hastype’ using hastype_bvc_ind >> qexists ‘ctxtFV’ >> rw[] >~
  [‘MEM (s,τ) _’] >- metis_tac[hastype_rules, subctxt_def] >~
  [‘Δ ⊢ M @@ N ⦂ τ₂’] >- metis_tac[hastype_rules] >>
  gs [subctxt_def, hastype_lam_inv, DISJ_IMP_THM, FORALL_AND_THM]
QED


Theorem permutation:
  ∀Γ₁ m A. Γ₁ ⊢ m ⦂ A ⇒ ∀Γ₂. PERM Γ₁ Γ₂ ⇒ Γ₂ ⊢ m ⦂ A
Proof
  Induct_on ‘hastype’ using hastype_bvc_ind >> qexists ‘ctxtFV’ THEN
  SRW_TAC [][] THENL [
    METIS_TAC [PERM_MEM_EQ],
    METIS_TAC [valid_ctxt_PERM],
    SRW_TAC [][hastype_app_inv] THEN METIS_TAC [],
    SRW_TAC [][hastype_lam_inv]
  ]
QED

Theorem strengthening_FV:
  ∀Γ m A. Γ ⊢ m ⦂ A ⇒ Γ ∩ FV m ⊢ m ⦂ A
Proof
  Induct_on ‘hastype’ >> qexists ‘{}’ THEN
  SRW_TAC [][valid_ctxt_domfilter, domfilter_delete] >~
  [‘_ ⊢ m1 @@ m2 ⦂ τ₂’, ‘Γ ⊢ m1 ⦂ τ₁ → τ₂’]
  >- (SRW_TAC [][hastype_app_inv] THEN qexists ‘τ₁’ THEN
      ‘valid_ctxt Γ’ by METIS_TAC [hastype_valid_ctxt] THEN
      ‘valid_ctxt (Γ ∩ (FV m1 ∪ FV m2))’
        by SRW_TAC [][valid_ctxt_domfilter] THEN
      ‘Γ ∩ FV m1 ⊆ Γ ∩ (FV m1 ∪ FV m2) ∧ Γ ∩ FV m2 ⊆ Γ ∩ (FV m1 ∪ FV m2)’
        suffices_by metis_tac [weakening] THEN
      SRW_TAC [][subctxt_def]) >~
  [‘(v,τ₁)::Γ ∩ FV M ⊢ M ⦂ τ₂’] >- SRW_TAC [][hastype_lam_inv] >>
  SRW_TAC [][hastype_lam_inv] THEN
  irule weakening >> rpt conj_tac >~
  [‘valid_ctxt _’] >- metis_tac[hastype_valid_ctxt, valid_ctxt_def,
                                IN_ctxtFV_domfilter] THEN
  rename [‘(v,A) :: Γ ∩ FV M’] >>
  ‘(Γ ∩ FV M) ⊆ ((v,A) :: (Γ ∩ FV M))’
    by SRW_TAC [][subctxt_def] THEN
  metis_tac []
QED

Theorem hastype_FV:
  ∀Γ m A. Γ ⊢ m ⦂ A ⇒ ∀v. v ∈ FV m ⇒ v ∈ ctxtFV Γ
Proof
  Induct_on ‘hastype’ >> qexists ‘∅’ >>
  SRW_TAC [][IN_supp_listpm, pairTheory.EXISTS_PROD] THEN
  METIS_TAC []
QED

(* Preservation of typing under β-reduction *)
Theorem typing_sub0[local]:
  ∀t vGt' v G A B t'.
      (vGt' = (v,G,t')) ∧
      (v,A) :: G ⊢ t ⦂ B ∧
      G ⊢ t' ⦂ A
    ⇒
      G ⊢ [t'/v]t ⦂ B
Proof
  ho_match_mp_tac chap3Theory.strong_bvc_term_ind THEN
  Q.EXISTS_TAC `λ(v,G,t'). {v} ∪ ctxtFV G ∪ FV t'` THEN
  simp[pairTheory.FORALL_PROD] >> rpt strip_tac >>
  gvs[SUB_THM, SUB_VAR, hastype_app_inv, hastype_lam_inv] >> rw[] >>
  simp[] >~
  [‘n # G’, ‘MEM (n, _) G’]
  >- (gs[NOT_IN_supp_listpm, pairTheory.FORALL_PROD]) >~
  [‘G ⊢ [M/v] N1 ⦂ _ ∧ G ⊢ [M/v] N2 ⦂ _’]
  >- metis_tac[] >~
  [‘(v,σ) :: Γ ⊢ [M/u]N ⦂ τ’] >>
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ‘Γ ⊆ (v,σ) :: Γ’  by SRW_TAC [][subctxt_def] THEN
  METIS_TAC [PERM_SWAP_AT_FRONT, PERM_REFL, permutation, weakening,
             hastype_valid_ctxt, valid_ctxt_def]
QED

Theorem typing_sub = SRULE [] typing_sub0

Theorem preservation:
  ∀t t'. t -β-> t' ⇒ ∀Γ A. Γ ⊢ t ⦂ A ⇒ Γ ⊢ t' ⦂ A
Proof
  ho_match_mp_tac $ GEN_ALL ccbeta_gen_ind THEN
  Q.EXISTS_TAC ‘ctxtFV’ THEN
  SRW_TAC [][hastype_app_inv, hastype_lam_inv] THEN
  METIS_TAC [typing_sub]
QED

Theorem progress:
  ∀t A B. [] ⊢ t ⦂ A → B ∧ ¬is_abs t ⇒ ∃t'. t -β-> t'
Proof
  Induct_on ‘hastype’ using hastype_strongind >> rw[] >> gvs[] >>
  rename [‘[] ⊢ M1 ⦂ A → B1 → B2’, ‘[] ⊢ M2 ⦂ A’, ‘M1 @@ M2’] >>
  Cases_on ‘is_abs M1’ >> gvs[]
  >- (qspec_then ‘M1’ FULL_STRUCT_CASES_TAC term_CASES >> gvs[] >>
      simp[ccbeta_rwt, EXISTS_OR_THM]) >>
  simp[ccbeta_rwt, EXISTS_OR_THM] >> metis_tac[]
QED

Definition subtype_def[simp]:
  (subtype A base ⇔ A = base) ∧
  (subtype A (B → C) ⇔ A = B → C ∨ subtype A B ∨ subtype A C)
End

Theorem subtype_refl[simp]:
  subtype A A
Proof
  Induct_on ‘A’ >> simp[]
QED

Theorem FV_tpm_EQ_EMPTY[simp,local]:
  FV (tpm pi t) = ∅ ⇔ FV t = ∅
Proof
  simp[EQ_IMP_THM, pred_setTheory.EXTENSION] >> rpt strip_tac >~
  [‘v ∈ FV M’, ‘π⁻¹ · _ # _’] >>
  first_x_assum $ qspec_then ‘π · v’ mp_tac >> simp[]
QED

Theorem FVEMPTY_DELETE_tpm[simp,local]:
  FV (tpm [(x,y)] t) DELETE swapstr x y v = ∅ ⇔
  FV t DELETE v = ∅
Proof
  simp[EQ_IMP_THM, pred_setTheory.EXTENSION,basic_swapTheory.swapstr_def] >>
  metis_tac[]
QED

Theorem FVEMPTY_DELETE_tpm'[simp,local] =
        FVEMPTY_DELETE_tpm |> Q.INST [‘v’ |-> ‘y’]
                           |> SRULE[Excl "FVEMPTY_DELETE_tpm"]


Theorem FVEMPTY_tpm[simp,local]:
  FV M = ∅ ⇒ tpm pi M = M
Proof
  qid_spec_tac ‘M’ >> Induct_on ‘pi’ >> simp[pairTheory.FORALL_PROD] >>
  ONCE_REWRITE_TAC [tpm_CONS] >> rpt strip_tac >> simp[] >>
  irule tpm_fresh >> gvs[FV_EMPTY]
QED

Theorem FVEMPTY_tpm'[simp,local]:
  FV M DELETE v = ∅ ⇒
  LAM u (tpm [(u,v)] M) = LAM v M ∧
  LAM (swapstr x y v) (tpm [(x,y)] M) = LAM v M
Proof
  Cases_on ‘u = v’ >> simp[] >> strip_tac >>
  rw[basic_swapTheory.swapstr_def] >>
  rename [‘FV M DELETE v = ∅’] >>
  ‘∀x. x ≠ v ⇒ x # M’ by (gs[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  first_assum $ C (resolve_then Any (assume_tac o GSYM)) tpm_ALPHA >>
  simp[tpm_fresh] >>
  rename [‘LAM y (tpm [(v,y)] M)’] >>
  Cases_on ‘v = y’ >> simp[] >>
  metis_tac[pmact_flip_args]
QED

val (ground_subterms_def, _) = define_recursive_term_function ‘
  ground_subterms (VAR s : term) = ∅ ∧
  ground_subterms (M @@ N) =
     (if FV (M @@ N) = ∅ then {M @@ N} else ∅) ∪ ground_subterms M ∪
     ground_subterms N ∧
  ground_subterms (LAM v M) =
  (if FV (LAM v M) = ∅ then {LAM v M} else ∅) ∪ ground_subterms M
’
val _ = export_rewrites ["ground_subterms_def"]

(*


Theorem subformula_property:
  ∀Γ t A.
    Γ ⊢ t ⦂ A ∧ bnf t ⇒
    ∀t0. t0 ∈ ground_subterms t ⇒
         ∃B B'. subtype B B' ∧ B' ∈ A INSERT (set $ MAP SND Γ) ∧ Γ ⊢ t0 ⦂ B
Proof
  Induct_on ‘hastype’ >> qexists ‘∅’ >> simp[] >> rpt strip_tac >> gvs[] >>~-
  ([‘¬is_abs M’, ‘bnf M’, ‘_ ⊢ M ⦂ τ1 → τ2’],
   drule_all progress >> metis_tac[corollary3_2_1, beta_normal_form_bnf]) >~

*)




val _ = export_theory ()
