open HolKernel boolLib Parse bossLib
open binderLib nomsetTheory metisLib termTheory contextlistsTheory
open chap3Theory

val _ = new_theory "stt";

val _ = remove_ovl_mapping "B" {Name="B", Thy="chap2"}

(* define simple types, the "funspace" constructor will get to be written
   as infix "-->".
*)
val _ = Hol_datatype `stype = base | funspace of stype => stype`;

val _ = overload_on("-->", ``funspace``)
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
                                 TM, HardSpace 1, TOK "◁", BreakSpace(1,0)],
                  term_name = "hastype"}

(* inductive definition of typing relation *)
val (hastype_rules, hastype_ind, hastype_cases) = Hol_reln`
  (∀s A Γ.     valid_ctxt Γ ∧ MEM (s,A) Γ ⇒ Γ ⊢ VAR s ◁ A) ∧
  (∀m n A B Γ. Γ ⊢ m ◁ A → B ∧ Γ ⊢ n ◁ A ⇒ Γ ⊢ m @@ n ◁ B) ∧
  (∀x m A B Γ. (x,A) :: Γ ⊢ m ◁ B         ⇒ Γ ⊢ LAM x m ◁ A → B)
`;

val _ = add_rule { term_name = "·",
                   block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                   paren_style = OnlyIfNecessary,
                   fixity = Infixl 600,
                   pp_elements = [TOK "·"]}

val _ = overload_on ("·", ``tpm``)
val _ = overload_on ("·", ``lswapstr``)
val _ = overload_on ("·", ``ctxtswap``)

val _ = set_fixity "#" (Infix(NONASSOC, 450))
val _ = overload_on ("#", ``λv Γ. v ∉ ctxtFV Γ``)
val _ = overload_on ("#", ``λv M. v ∉ FV M``)

(* typing relation respects permutation *)
val hastype_swap = store_thm(
  "hastype_swap",
  ``∀Γ m τ. Γ ⊢ m ◁ τ ⇒ ∀π. π·Γ ⊢ π·m ◁ τ``,
  HO_MATCH_MP_TAC hastype_ind THEN SRW_TAC [][] THENL [
    METIS_TAC [valid_ctxt_swap, MEM_ctxtswap, hastype_rules],
    METIS_TAC [hastype_rules],
    METIS_TAC [hastype_rules, MEM_ctxtswap]
  ]);

val hastype_swap_eqn = store_thm(
  "hastype_swap_eqn",
  ``Γ ⊢ π·m ◁ A <=> π⁻¹ · Γ ⊢ m ◁ A``,
  METIS_TAC [hastype_swap, pmact_inverse]);

val hastype_valid_ctxt = store_thm(
  "hastype_valid_ctxt",
  ``∀Γ m A. Γ ⊢ m ◁ A ⇒ valid_ctxt Γ``,
  HO_MATCH_MP_TAC hastype_ind THEN SRW_TAC [][]);

val hastype_strongind = theorem "hastype_strongind"

val ctxtswap_fresh_cons = store_thm(
  "ctxtswap_fresh_cons",
  ``x # (π·(G:'a ctxt)) ∧ y # (π·G) ⇒ (((x,y)::π)·G = π·G)``,
  `(x,y)::π = [(x,y)] ++ π` by SRW_TAC [][] THEN
  METIS_TAC [pmact_decompose, supp_fresh]);

val hastype_bvc_ind = store_thm(
  "hastype_bvc_ind",
  ``∀P fv.
       (∀x. FINITE (fv x)) ∧
       (∀G s A x. valid_ctxt G ∧ MEM (s,A) G ⇒ P G (VAR s) A x) ∧
       (∀G m n A B x.
          (∀y. P G m (A → B) y) ∧ (∀y. P G n A y) ∧
          G ⊢ m ◁ A → B ∧ G ⊢ n ◁ A
        ⇒
          P G (m @@ n) B x) ∧
       (∀G v m A B x. (∀y. P ((v,A)::G) m B y) ∧ v ∉ fv x ∧ v # G ∧
                      (v,A) :: G ⊢ m ◁ B
                    ⇒
                      P G (LAM v m) (A → B) x) ⇒
       ∀G m A. G ⊢ m ◁ A ⇒ ∀x. P G m A x``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `∀G m A. G ⊢ m ◁ A ⇒
                          ∀x π. P (π·G) (π·m) A x`
        THEN1 METIS_TAC [pmact_nil] THEN
  HO_MATCH_MP_TAC hastype_strongind THEN SRW_TAC [][hastype_rules] THENL [
    METIS_TAC [hastype_swap],
    Q.MATCH_ABBREV_TAC
      `P (π·G) (LAM (π·v) (π·m)) (A → B) c` THEN
    markerLib.RM_ALL_ABBREVS_TAC THEN
    Q_TAC (NEW_TAC "z") `(π·v) INSERT ctxtFV (π·G) ∪
                         FV (π·m) ∪ fv c` THEN
    `LAM (π·v) (π·m) =
     LAM z ([(z,π·v)]·(π·m))` by SRW_TAC [][tpm_ALPHA] THEN
    POP_ASSUM SUBST1_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    `valid_ctxt ((v,A)::G)` by METIS_TAC [hastype_valid_ctxt] THEN
    `v # G` by FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THENL [
      SRW_TAC [][GSYM pmact_decompose] THEN
      Q_TAC SUFF_TAC
         `((z,A) :: (π·G) = (([(z,π·v)] ++ π)·v,A) :: ([(z,π·v)] ++ π)·G) ∧
          (((z,π·v)::π) · m = ([(z,π·v)] ++ π) · m)`
         THEN1
           (DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC) THEN
            FIRST_X_ASSUM MATCH_ACCEPT_TAC) THEN
      SRW_TAC [][GSYM pmact_decompose] THEN
      SRW_TAC [][ctxtswap_fresh_cons],
      SRW_TAC [][hastype_swap_eqn, pmact_decompose, ctxtswap_fresh]
    ]
  ]);

val hastype_indX = save_thm(
  "hastype_indX",
  (Q.GEN `P` o Q.GEN `X` o SIMP_RULE bool_ss [] o
   Q.SPECL [`λG M t x. P G M t`, `λx. X`]) hastype_bvc_ind)

val hastype_lam_inv = store_thm(
  "hastype_lam_inv",
  ``v # Γ ⇒
      (Γ ⊢ LAM v M ◁ τ ⇔
       ∃τ₁ τ₂. ((v,τ₁)::Γ) ⊢ M ◁ τ₂  ∧  (τ = τ₁ → τ₂))``,
  SRW_TAC [][LAM_eq_thm, Once hastype_cases] THEN SRW_TAC [][EQ_IMP_THM] THENL [
    Q.MATCH_ABBREV_TAC `(v,τ₁)::Γ ⊢ [(v,x)] · m ◁ τ₂` THEN
    markerLib.RM_ALL_ABBREVS_TAC THEN
    `[(v,x)] · ((x,τ₁) :: Γ) ⊢ [(v,x)] · m ◁ τ₂`
       by SRW_TAC [][hastype_swap] THEN
    POP_ASSUM MP_TAC THEN
    `valid_ctxt ((x,τ₁):: Γ)` by METIS_TAC [hastype_valid_ctxt] THEN
    `x # Γ` by FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][ctxtswap_fresh],
    METIS_TAC []
  ]);

val hastype_var_inv = store_thm(
  "hastype_var_inv",
  ``Γ ⊢ VAR v ◁ τ ⇔ MEM (v,τ) Γ ∧ valid_ctxt Γ``,
  SRW_TAC [][Once hastype_cases] THEN METIS_TAC []);
val _ = export_rewrites ["hastype_var_inv"]

val hastype_app_inv = store_thm(
  "hastype_app_inv",
  ``Γ ⊢ M @@ N ◁ τ₂ ⇔ ∃τ₁. Γ ⊢ M ◁ τ₁ → τ₂ ∧ Γ ⊢ N ◁ τ₁``,
  SRW_TAC [][Once hastype_cases]);

val weakening = store_thm(
  "weakening",
  ``∀Γ m τ. Γ ⊢ m ◁ τ ⇒ ∀Δ. valid_ctxt Δ ∧ Γ ⊆ Δ ⇒ Δ ⊢ m ◁ τ``,
  HO_MATCH_MP_TAC hastype_bvc_ind THEN REPEAT CONJ_TAC THEN
  Q.EXISTS_TAC `ctxtFV` THEN SRW_TAC [][] THENL [
    (* var case *) METIS_TAC [hastype_rules, subctxt_def],
    (* app case *) METIS_TAC [hastype_rules],

    (* abs case *)
    FULL_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [subctxt_def, hastype_lam_inv]
  ]);

open sortingTheory

val permutation = store_thm(
  "permutation",
  ``∀Γ₁ m A. Γ₁ ⊢ m ◁ A ⇒ ∀Γ₂. PERM Γ₁ Γ₂ ⇒ Γ₂ ⊢ m ◁ A``,
  HO_MATCH_MP_TAC hastype_bvc_ind THEN Q.EXISTS_TAC `ctxtFV` THEN
  SRW_TAC [][] THENL [
    METIS_TAC [PERM_MEM_EQ],
    METIS_TAC [valid_ctxt_PERM],
    SRW_TAC [][hastype_app_inv] THEN METIS_TAC [],
    SRW_TAC [][hastype_lam_inv]
  ]);

val strengthening_FV = store_thm(
  "strengthening_FV",
  ``∀Γ m A. Γ ⊢ m ◁ A ⇒ Γ ∩ FV m ⊢ m ◁ A``,
  HO_MATCH_MP_TAC hastype_indX THEN Q.EXISTS_TAC `{}` THEN
  SRW_TAC [][valid_ctxt_domfilter, domfilter_delete] THENL [
    SRW_TAC [][hastype_app_inv] THEN Q.EXISTS_TAC `A` THEN
    `valid_ctxt Γ` by METIS_TAC [hastype_valid_ctxt] THEN
    `valid_ctxt (Γ ∩ (FV m ∪ FV m'))`
       by SRW_TAC [][valid_ctxt_domfilter] THEN
    Q_TAC SUFF_TAC
      `Γ ∩ FV m ⊆ Γ ∩ (FV m ∪ FV m') ∧ Γ ∩ FV m' ⊆ Γ ∩ (FV m ∪ FV m')`
      THEN1 METIS_TAC [weakening] THEN
    SRW_TAC [][subctxt_def],

    SRW_TAC [][hastype_lam_inv],

    SRW_TAC [][hastype_lam_inv] THEN
    `valid_ctxt ((v,A) :: (Γ ∩ FV m))`
       by METIS_TAC[hastype_valid_ctxt, valid_ctxt_def,
                    IN_ctxtFV_domfilter] THEN
    `(Γ ∩ FV m) ⊆ ((v,A) :: (Γ ∩ FV m))`
        by SRW_TAC [][subctxt_def] THEN
    METIS_TAC [weakening]
  ]);

val hastype_FV = store_thm(
  "hastype_FV",
  ``∀Γ m A. Γ ⊢ m ◁ A ⇒ ∀v. v ∈ FV m ⇒ v ∈ ctxtFV Γ``,
  HO_MATCH_MP_TAC hastype_ind THEN
  SRW_TAC [][IN_supp_listpm, pairTheory.EXISTS_PROD] THEN
  METIS_TAC []);

(* Preservation of typing under β-reduction *)
val typing_sub0 = prove(
  ``∀t vGt' v G A B t'.
      (vGt' = (v,G,t')) ∧
      (v,A) :: G ⊢ t ◁ B ∧
      G ⊢ t' ◁ A
    ⇒
      G ⊢ [t'/v]t ◁ B``,
  HO_MATCH_MP_TAC chap3Theory.strong_bvc_term_ind THEN
  Q.EXISTS_TAC `λ(v,G,t'). {v} ∪ ctxtFV G ∪ FV t'` THEN
  SIMP_TAC (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM] THEN
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  SRW_TAC [][SUB_THM, SUB_VAR, hastype_app_inv, hastype_lam_inv] THENL [
    SRW_TAC [][],
    FULL_SIMP_TAC (srw_ss()) [NOT_IN_supp_listpm, pairTheory.FORALL_PROD],
    METIS_TAC [],
    Q.MATCH_ABBREV_TAC `(v,σ) :: Γ ⊢ [M/u]N ◁ τ` THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    markerLib.RM_ALL_ABBREVS_TAC THEN
    `Γ ⊆ (v,σ) :: Γ`  by SRW_TAC [][subctxt_def] THEN
    METIS_TAC [PERM_SWAP_AT_FRONT, PERM_REFL, permutation, weakening,
               hastype_valid_ctxt, valid_ctxt_def]
  ]);

val typing_sub = save_thm("typing_sub", SIMP_RULE (srw_ss()) [] typing_sub0);

val preservation = store_thm(
  "preservation",
  ``∀t t'. t -β-> t' ⇒ ∀Γ A. Γ ⊢ t ◁ A ⇒ Γ ⊢ t' ◁ A``,
  HO_MATCH_MP_TAC (GEN_ALL ccbeta_gen_ind) THEN
  Q.EXISTS_TAC `ctxtFV` THEN
  SRW_TAC [][hastype_app_inv, hastype_lam_inv] THENL [
    METIS_TAC [typing_sub],
    METIS_TAC [],
    METIS_TAC []
  ]);

val _ = export_theory ()
