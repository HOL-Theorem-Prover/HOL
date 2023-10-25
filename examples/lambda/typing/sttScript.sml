open HolKernel boolLib Parse bossLib
open binderLib nomsetTheory metisLib termTheory contextlistsTheory
open chap3Theory
open sortingTheory
open appFOLDLTheory
open pred_setTheory

val _ = new_theory "stt";

val _ = remove_ovl_mapping "B" {Name="B", Thy="chap2"}
val _ = remove_ovl_mapping "C" {Name="C", Thy="chap2"}

(* define simple types, the "funspace" constructor will get to be written
   as infix "-->".
*)
Datatype: stype = base | funspace stype stype
End

Overload "-->" = “funspace”
val _ = Parse.Unicode.unicode_version{u = Unicode.UChar.rightarrow,tmnm = "-->"}

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

Theorem subtype_trans:
  ∀A B C. subtype A B ∧ subtype B C ⇒ subtype A C
Proof
  Induct_on ‘C’ >> simp[] >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem subtype_size:
  ∀A B. subtype A B ⇒ stype_size A ≤ stype_size B
Proof
  Induct_on ‘B’ >> simp[] >> rpt strip_tac >>
  res_tac >> simp[definition "stype_size_def"]
QED

Theorem subtype_eqsize:
  ∀A B. subtype A B ∧ stype_size A = stype_size B ⇒ A = B
Proof
  Induct_on ‘B’ >> simp[definition "stype_size_def"] >> rw[] >>
  drule_then strip_assume_tac subtype_size >> gvs[]
QED

Theorem subtype_antisym:
  ∀A B. subtype A B ∧ subtype B A ⇒ B = A
Proof
  metis_tac[subtype_eqsize, subtype_size, arithmeticTheory.LESS_EQUAL_ANTISYM]
QED

Theorem FV_tpm_EQ_EMPTY[simp,local]:
  FV (tpm pi t) = ∅ ⇔ FV t = ∅
Proof
  simp[EQ_IMP_THM, EXTENSION] >> rpt strip_tac >~
  [‘v ∈ FV M’, ‘π⁻¹ · _ # _’] >>
  first_x_assum $ qspec_then ‘π · v’ mp_tac >> simp[]
QED

Theorem FVEMPTY_DELETE_tpm[simp,local]:
  FV (tpm [(x,y)] t) DELETE swapstr x y v = ∅ ⇔
  FV t DELETE v = ∅
Proof
  simp[EQ_IMP_THM, EXTENSION,basic_swapTheory.swapstr_def] >>
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
  ‘∀x. x ≠ v ⇒ x # M’ by (gs[EXTENSION] >> metis_tac[]) >>
  first_assum $ C (resolve_then Any (assume_tac o GSYM)) tpm_ALPHA >>
  simp[tpm_fresh] >>
  rename [‘LAM y (tpm [(v,y)] M)’] >>
  Cases_on ‘v = y’ >> simp[] >>
  metis_tac[pmact_flip_args]
QED

Inductive gentype:
[~VAR:]
  (∀Γ s τ.
     valid_ctxt Γ ∧ MEM (s,τ) Γ ⇒ gentype Γ (VAR s : term) τ {(Γ,VAR s,τ)}) ∧
[~APP:]
  (∀Γ M N A B fs xs.
     gentype Γ M (A → B) fs ∧ gentype Γ N A xs ⇒
     gentype Γ (M @@ N) B ({(Γ,M @@ N,B)} ∪ fs ∪ xs)) ∧
[~LAM:]
  (∀Γ v M A B bs.
     gentype ((v,A) :: Γ) M B bs ⇒
     gentype Γ (LAM v M) (A → B) ({(Γ,LAM v M, A → B)} ∪ bs))
End

Theorem gentype_hastype:
  gentype Γ M τ s ⇒ Γ ⊢ M ⦂ τ
Proof
  Induct_on ‘gentype’ >> metis_tac[hastype_rules]
QED

Theorem gentype_member_set:
  gentype Γ M τ s ⇒ (Γ,M,τ) ∈ s
Proof
  Induct_on ‘gentype’ >> simp[]
QED

Theorem gentype_members_hastype:
  gentype Γ M τ s ⇒ ∀Γ' M' τ'. (Γ',M',τ') ∈ s ⇒ Γ' ⊢ M' ⦂ τ'
Proof
  Induct_on ‘gentype’ >> rw[] >>
  metis_tac[hastype_rules, gentype_member_set]
QED

Theorem hastype_gentype:
  Γ ⊢ M ⦂ τ ⇒ ∃s. gentype Γ M τ s
Proof
  Induct_on ‘hastype’ >> qexists ‘∅’ >> simp[] >> metis_tac[gentype_rules]
QED

Inductive subterm:
[~refl:]
  (∀M:term Γ. FINITE Γ ∧ FV M ⊆ Γ ⇒ (subterm (Γ, M) (Γ, M))) ∧
[~appL:]
  (∀Γ Γ₀ M0 M N.
     FV N ⊆ Γ ∧ subterm (Γ₀, M0) (Γ, M) ⇒ subterm (Γ₀, M0) (Γ, M @@ N)) ∧
[~appR:]
  (∀Γ₀ Γ N0 M N.
     FV M ⊆ Γ ∧ subterm (Γ₀, N0) (Γ, N) ⇒ subterm (Γ₀, N0) (Γ, M @@ N)) ∧
[~lam:]
  (∀Γ₀ Γ v M N.
     v ∉ Γ ∧
     subterm (Γ₀, M) (v INSERT Γ, N) ⇒ subterm (Γ₀, M) (Γ, LAM v N))
End

Theorem subterm_FV:
  ∀Γ₀ Γ M N. subterm (Γ₀, M) (Γ, N) ⇒ FV N ⊆ Γ ∧ FV M ⊆ Γ₀ ∧ Γ ⊆ Γ₀
Proof
  Induct_on ‘subterm’ >> simp[] >> rw[] >>
  rename [‘FV N ⊆ v INSERT Γ’, ‘FV N DELETE v ⊆ Γ’] >>
  qpat_x_assum ‘FV N ⊆ v INSERT Γ’ mp_tac >>
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem subterm_VAR[simp]:
  ∀Γ₁ Γ₂ t s.
    subterm (Γ₁, t) (Γ₂, VAR s) ⇔ Γ₁ = Γ₂ ∧ t = VAR s ∧ s ∈ Γ₁ ∧ FINITE Γ₁
Proof
  simp[EQ_IMP_THM, FORALL_AND_THM, subterm_refl] >>
  Induct_on ‘subterm’ >> rw[] >> gvs[]
QED

Theorem subterm_size:
  ∀Γ₁ Γ₂ t₁ t₂. subterm (Γ₁, t₁) (Γ₂, t₂) ⇒ size t₁ ≤ size t₂
Proof
  Induct_on ‘subterm’ >> rw[]
QED

Theorem subterm_ID[simp]:
  subterm (Γ₁, t) (Γ₂, t) ⇔ Γ₁ = Γ₂ ∧ FV t ⊆ Γ₂ ∧ FINITE Γ₂
Proof
  simp[Once subterm_cases] >> rw[EQ_IMP_THM, DISJ_IMP_THM] >>
  drule subterm_size >> simp[]
QED

Theorem subterm_FINITE:
  ∀S0 S1 M0 M1. subterm (S0,M0) (S1,M1) ⇒ FINITE S0 ∧ FINITE S1
Proof
  Induct_on ‘subterm’ >> simp[]
QED

Theorem subterm_perm:
  ∀G0 M0 G M.
    subterm (G0,M0) (G,M) ⇒
    ∀pi. subterm (ssetpm pi G0, tpm pi M0) (ssetpm pi G, tpm pi M)
Proof
  Induct_on ‘subterm’ >> simp[] >> rw[]
  >- gvs[SUBSET_DEF]
  >- (irule subterm_appL >> gvs[SUBSET_DEF])
  >- (irule subterm_appR >> gvs[SUBSET_DEF]) >>
  irule subterm_lam >> gvs[pmact_INSERT]
QED

Theorem subterm_lam_inv:
  ∀v Γ Γ0 M M0.
    v ∉ Γ ⇒
    (subterm (Γ0, M0) (Γ, LAM v M) ⇔
       M0 = LAM v M ∧ Γ0 = Γ ∧ FINITE Γ0 ∧ FV (LAM v M) ⊆ Γ0 ∨
       ∃u. u ∉ Γ ∧ (u = v ∨ u ∉ FV M) ∧
           subterm (ssetpm [(u,v)] Γ0, tpm [(u,v)] M0) (v INSERT Γ, M))
Proof
  simp[SimpLHS, Once subterm_cases] >>
  rw[] >> iff_tac >> rw[]
  >- gvs[]
  >- (rename [‘LAM u M = LAM v N’] >> disj2_tac >>
      gvs[LAM_eq_thm] >- (first_assum $ irule_at Any >> simp[]) >>
      drule_then (qspec_then ‘[(v,u)]’ assume_tac) subterm_perm>>
      ‘tpm [(v,u)] N = tpm [(u,v)] N’ by simp[pmact_flip_args] >>
      qexists ‘v’ >> simp[] >>
      ‘ssetpm [(v,u)] (v INSERT Γ) = u INSERT Γ’ suffices_by metis_tac[] >>
      simp[pmact_INSERT] >>
      ‘ssetpm [(v,u)] Γ = Γ’ suffices_by simp[] >>
      irule supp_fresh >> drule subterm_FINITE >> simp[supp_FINITE_strings])
  >- (gvs[] >> metis_tac[])
  >- (drule_then (qspec_then ‘[(u,v)]’ mp_tac) subterm_perm >>
      simp[pmact_INSERT] >> strip_tac >> disj2_tac >>
      ‘ssetpm [(u,v)] Γ = Γ’ by (irule supp_fresh >> drule subterm_FINITE >>
                                 simp[supp_FINITE_strings]) >>
      gvs[] >> first_assum $ irule_at Any >> simp[] >>
      simp[LAM_eq_thm, SF CONJ_ss] >>
      simp[pmact_flip_args])
QED

(* Theorem subformula_property:
  ∀Γ t A.
    Γ ⊢ t ⦂ A ∧ bnf t ⇒
    ∀S0 t0. subterm (S0, t0) (set (MAP FST Γ), t) ⇒
            ∃Γ0 A0 A1.
              set (MAP FST Γ0) = S0 ∧ Γ0 ⊢ t0 ⦂ A0 ∧
              subtype A0 A1 ∧
              (A1 = A ∨ ∃v. MEM (v,A1) Γ)
Proof[exclude_simps = subtype_def]
  completeInduct_on ‘size t’ >> rw[] >> gs[PULL_FORALL] >>
  Cases_on ‘t0 = t’
  >- (gvs[] >> dsimp[] >> metis_tac[subtype_refl]) >>
  qpat_x_assum ‘bnf _’ mp_tac >>
  ‘FINITE (ctxtFV Γ)’ by simp[] >>
  drule_then (qspec_then ‘t’ (simp o single o Once)) bnf_characterisation' >>
  rw[] >> reverse $ Cases_on ‘vs’
  >- (gvs[] >>
      qpat_x_assum ‘Γ ⊢ LAM _ (LAMl _ _) ⦂ A’ mp_tac >>
      simp[hastype_lam_inv, PULL_EXISTS] >> rw[] >>
      first_x_assum $ drule_at (Pat ‘hastype _ _ _ ’) >>
      simp[]
  Induct_on ‘hastype’ >> qexists ‘∅’ >> simp[] >> rw[] >> gvs[]
  >- (irule_at Any EQ_REFL >> simp[]>> first_assum $ irule_at Any >>
      simp[] >> rw[] >>
      gvs[valid_ctxt_ALL_DISTINCT] >>
      rename [‘subtype A B’, ‘MEM (v,A) Γ’] >>
      ‘A = B’ suffices_by simp[] >>
      dxrule_then strip_assume_tac
          (iffLR listTheory.MEM_SPLIT_APPEND_first) >> gvs[] >>
      rename [‘MEM (vn,B) lp’] >>
      qpat_x_assum ‘MEM _ lp’
        $ mp_then Any strip_assume_tac
        $ iffLR listTheory.MEM_SPLIT_APPEND_first >>
      gvs[listTheory.ALL_DISTINCT_APPEND] >> metis_tac[])
  >- (qpat_x_assum ‘subterm _ _ ’ mp_tac >>
      ONCE_REWRITE_TAC [subterm_cases] >> rw[] >~
      [‘FV (M @@ N) ⊆ _’, ‘Γ ⊢ M ⦂ A → B’]
      >- (


      ‘Γ = [(s,A)]’ suffices_by simp[] >>
      Cases_on ‘Γ’ >> gvs[] >~
      [‘s # t’]
      >- (Cases_on ‘t’ >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
          rename [‘valid_ctxt (h::ts)’] >> Cases_on ‘h’ >> fs[]) >>
      rename [‘valid_ctxt (h::t)’] >>
      Cases_on ‘h’ >> fs[DISJ_IMP_THM, FORALL_AND_THM] >> gvs[] >>
      rename [‘vn # t’] >> Cases_on ‘t’ >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
      rename [‘valid_ctxt (h::t)’] >> Cases_on ‘h’ >> fs[])
  >- (

valid_ctxt_def
  >- metis_tac[]
  >-
  ([‘¬is_abs M’, ‘bnf M’, ‘_ ⊢ M ⦂ τ1 → τ2’],
   drule_all progress >> metis_tac[corollary3_2_1, beta_normal_form_bnf]) >~

*)




val _ = export_theory ()
