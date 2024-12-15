open HolKernel Parse boolLib bossLib;

open boolSimps metisLib basic_swapTheory relationTheory listTheory
open pred_setTheory

local open pred_setLib in end;

open binderLib BasicProvers nomsetTheory termTheory chap2Theory appFOLDLTheory;
open horeductionTheory chap3Theory

(* ----------------------------------------------------------------------
    A mechanisation of §3 of

     Takahashi 1995, "Parallel Reductions in λ-Calculus"

    leading to ⊢ has_benf M ⇔ has_bnf M
   ---------------------------------------------------------------------- *)

val _ = new_theory "takahashiS3";

Inductive peta:
[~refl[simp]:]
  !M. peta M M
[~lam:]
  !v M N. peta M N ⇒ peta (LAM v M) (LAM v N)
[~app:]
  !M1 M2 N1 N2. peta M1 M2 /\ peta N1 N2 ⇒ peta (M1 @@ N1) (M2 @@ N2)
[~eta:]
  !v M N. peta M N /\ v ∉ FV M ⇒ peta (LAM v (M @@ VAR v)) N
End

val _ = set_mapped_fixity {term_name = "peta", tok = "=η=>",
                           fixity = Infix(NONASSOC, 450)}

Theorem peta_VAR[simp]:
  peta (VAR s) M ⇔ M = VAR s
Proof
  simp[Once peta_cases]
QED

Theorem tpm_peta[simp]:
  tpm p M =η=> tpm p N ⇔ M =η=> N
Proof
  ‘∀M N. M =η=> N ⇒ ∀p. tpm p M =η=> tpm p N’
    suffices_by metis_tac[pmact_inverse] >>
  Induct_on ‘peta’ >> rw[] >> simp[peta_rules]
QED

Theorem peta_FV:
  ∀M N. peta M N ⇒ FV N = FV M
Proof
  Induct_on ‘peta’ >> simp[] >>
  rw[pred_setTheory.UNION_DELETE, pred_setTheory.DELETE_NON_ELEMENT_RWT]
QED

Theorem peta_genind:
  ∀P fv.
    (∀x. FINITE (fv x)) ∧
    (∀M x. P M M x) ∧
    (∀v M N x. peta M N ∧ (∀y. P M N y) ∧ v ∉ fv x ⇒ P (LAM v M) (LAM v N) x) ∧
    (∀M1 M2 N1 N2 x.
       peta M1 M2 ∧ peta N1 N2 ∧ (∀y. P M1 M2 y) ∧ (∀y. P N1 N2 y) ⇒
       P (M1 @@ N1) (M2 @@ N2) x) ∧
    (∀v M N x.
       peta M N ∧ (∀y. P M N y) ∧ v ∉ FV M ∧ v ∉ fv x ⇒
       P (LAM v (M @@ VAR v)) N x) ⇒
    ∀M N. peta M N ⇒ ∀x. P M N x
Proof
  rpt gen_tac >> strip_tac >>
  ‘∀M N. M =η=> N ⇒ ∀p x. P (tpm p M) (tpm p N) x’
    suffices_by metis_tac[pmact_nil] >>
  Induct_on ‘peta’ >> rw[]
  >- (qabbrev_tac ‘u = lswapstr p v’ >>
      Q_TAC (NEW_TAC "z") ‘u INSERT FV (tpm p M) ∪ FV (tpm p N) ∪ fv x’ >>
      ‘LAM u (tpm p M) = LAM z (tpm ((u,z)::p) M) ∧
       LAM u (tpm p N) = LAM z (tpm ((u,z)::p) N)’
        by (ONCE_REWRITE_TAC[tpm_CONS] >>
            ONCE_REWRITE_TAC[pmact_flip_args] >>
            simp[tpm_ALPHA]) >>
      simp[] >> first_x_assum irule >> simp[]) >>
  qabbrev_tac ‘u = lswapstr p v’ >>
  Q_TAC (NEW_TAC "z") ‘u INSERT FV (tpm p M) ∪ FV (tpm p N) ∪ fv x’ >>
  ‘LAM u (tpm p M @@ VAR u) = LAM z (tpm ((u,z)::p) M @@ VAR z)’
    by (ONCE_REWRITE_TAC [tpm_CONS] >>
        ‘z # (tpm p M @@ VAR u)’ by simp[] >> drule tpm_ALPHA >>
        simp[pmact_flip_args]) >>
  ‘tpm p N = tpm ((u,z)::p) N’
    by (ONCE_REWRITE_TAC[tpm_CONS] >>
        ‘u # tpm p N’ suffices_by simp[tpm_fresh] >>
        simp[Abbr‘u’] >> metis_tac[peta_FV]) >>
  simp[] >> first_x_assum irule >> simp[] >>
  simp[pmact_decompose] >> simp[Abbr‘u’]
QED

Theorem cc_eta_peta:
  ∀M N. M -η-> N ==> peta M N
Proof
  ho_match_mp_tac cc_ind >> simp[] >> qexists ‘{}’ >> rw[] >>
  simp[peta_rules] >> gvs[eta_def, peta_eta]
QED

Theorem peta_reduction_eta:
  ∀M N. peta M N ⇒ M -η->* N
Proof
  Induct_on ‘peta’ >> simp[] >> rw[] >~
  [‘LAM v (M @@ VAR v) -η->* N’]
  >- (irule $ cj 2 RTC_RULES_RIGHT1 >>
      irule_at Any compat_closure_R >> qexists ‘LAM v (N @@ VAR v)’ >>
      conj_tac >~ [‘LAM _ _ -η->* LAM _ _’] >- metis_tac[reduction_rules] >>
      simp[eta_def, LAM_eq_thm, SF DNF_ss] >> metis_tac[peta_FV]) >>
  metis_tac[reduction_rules]
QED

Theorem RTC_peta_reduction_eta:
  ∀M N. peta꙳ M N ⇔ M -η->* N
Proof
  metis_tac[peta_reduction_eta, cc_eta_peta, RTC_BRACKETS_RTC_EQN]
QED

Theorem peta_genindX = peta_genind
                         |> INST_TYPE [alpha |-> “:unit”]
                         |> Q.SPECL [‘λM N x. Q M N’, ‘K X’]
                         |> SRULE[]
                         |> Q.INST [‘Q’ |-> ‘P’]
                         |> Q.GENL [‘P’, ‘X’]

Theorem peta_cosub:
  ∀M. peta N1 N2 ⇒ peta ([N1/v]M) ([N2/v]M)
Proof
  ho_match_mp_tac nc_INDUCTION2 >> qexists ‘v INSERT FV N1 ∪ FV N2’ >>
  rw[SUB_VAR, peta_app, peta_lam, SUB_THM]
QED

Theorem peta_subst_closed:
  ∀M M' N N' .
    peta M M' ∧ peta N N' ⇒ ∀y. peta ([N/y] M) ([N'/y]M')
Proof
  ‘∀M M'.
     peta M M' ⇒
     ∀NN'y.
       peta (FST NN'y) (FST (SND NN'y)) ⇒
       peta ([FST NN'y/(SND (SND NN'y))]M) ([FST (SND NN'y)/SND (SND NN'y)]M')’
    suffices_by simp[pairTheory.FORALL_PROD] >>
  ho_match_mp_tac peta_genind >>
  qexists ‘λNN'y. SND (SND NN'y) INSERT FV (FST NN'y) ∪ FV (FST (SND NN'y))’ >>
  simp[pairTheory.FORALL_PROD] >> rw[] >~
  [‘[N/v] M =η=> [N'/v]M’] >- simp[peta_cosub] >~
  [‘LAM v ([N/u] M) =η=> LAM v ([N'/u]M')’]
  >- simp[peta_lam] >~
  [‘_ @@ _ =η=> _ @@ _’]
  >- simp[peta_app] >~
  [‘LAM v ([N/u] M @@ VAR v) =η=> [N'/u] M'’]
  >- (irule peta_eta >> simp[NOT_IN_FV_SUB])
QED

Inductive eta_expandR:
[~zero:]
  eta_expandR 0 M M
[~suc:]
  eta_expandR n M N ∧ v ∉ FV M ⇒ eta_expandR (n + 1) M (LAM v (N @@ VAR v))
End

Theorem eta_expandR_FV:
  ∀k M N. eta_expandR k M N ⇒ FV N = FV M
Proof
  Induct_on ‘eta_expandR’ >>
  simp[pred_setTheory.DELETE_INSERT, pred_setTheory.UNION_DELETE,
       pred_setTheory.DELETE_NON_ELEMENT_RWT]
QED

Theorem eta_expandR_unique:
  ∀k M N. eta_expandR k M N ⇒ ∀N'. eta_expandR k M N' ⇔ N' = N
Proof
  Induct_on ‘eta_expandR’>> conj_tac >> rpt gen_tac
  >- simp[Once eta_expandR_cases] >>
  strip_tac >> simp[Once eta_expandR_cases] >>
  simp[EQ_IMP_THM, FORALL_AND_THM] >> reverse conj_tac >- metis_tac[] >>
  rw[PULL_EXISTS,LAM_eq_thm] >> rename [‘u:string = v’] >> Cases_on ‘u = v’ >>
  simp[] >> rpt (dxrule eta_expandR_FV) >> simp[tpm_fresh]
QED

Theorem eta_expandR_total:
  ∀k M. ∃N. eta_expandR k M N
Proof
  Induct >- metis_tac[eta_expandR_zero] >> rpt gen_tac >>
  simp[arithmeticTheory.ADD1] >> irule_at Any eta_expandR_suc >>
  Q_TAC (NEW_TAC "z") ‘FV M’ >> metis_tac[]
QED

Definition eta_expand_def:
  eta_expand k M = @N. eta_expandR k M N
End

Theorem eta_expand0[simp]:
  eta_expand 0 M = M
Proof
  simp[eta_expand_def, Once eta_expandR_cases]
QED

Theorem eta_expand_FV[simp]:
  FV (eta_expand k M) = FV M
Proof
  simp[eta_expand_def] >> SELECT_ELIM_TAC >>
  metis_tac[eta_expandR_total, eta_expandR_FV]
QED

Theorem eta_expandSUC:
  v ∉ FV M ⇒ eta_expand (SUC k) M = LAM v (eta_expand k M @@ VAR v)
Proof
  simp[eta_expand_def] >> rpt SELECT_ELIM_TAC >> simp[eta_expandR_total] >>
  gen_tac >> strip_tac >> simp[Once eta_expandR_cases] >>
  simp[PULL_EXISTS, arithmeticTheory.ADD1] >>
  dxrule_then assume_tac eta_expandR_unique >> simp[] >> rpt strip_tac >>
  rename [‘eta_expandR k M _ ⇔ _ = N’] >>
  ‘FV N = FV M’ by metis_tac[eta_expandR_FV] >> rw[LAM_eq_thm]>>
  metis_tac[tpm_fresh]
QED

Theorem eta_expand_EQ_VAR[simp]:
  eta_expand k M = VAR s ⇔ k = 0 ∧ M = VAR s
Proof
  Cases_on ‘k’ >> simp[] >> Q_TAC (NEW_TAC "z") ‘FV M’ >>
  drule_then assume_tac eta_expandSUC >> simp[]
QED

Theorem takahashi_3_2_1:
  M =η=> VAR x ⇔ ∃k. M = eta_expand k (VAR x)
Proof
  iff_tac
  >- (‘∀M N. M =η=> N ⇒ ∀s. N = VAR s ⇒ ∃k. M = eta_expand k (VAR s)’
        suffices_by metis_tac[] >>
      ho_match_mp_tac peta_genind >> qexists ‘λx. {x}’ >> rw[] >> gvs[] >>
      rename [‘eta_expand k’] >> qexists ‘SUC k’ >> ‘v ∉ FV (VAR s)’ by simp[] >>
      dxrule_then assume_tac eta_expandSUC >> simp[]) >>
  simp[PULL_EXISTS] >> map_every qid_spec_tac [‘x’, ‘M’] >> Induct_on ‘k’ >>
  gvs[] >> qx_gen_tac ‘u’ >> Q_TAC (NEW_TAC "v") ‘{u}’ >>
  ‘v ∉ FV (VAR u)’ by simp[] >>
  dxrule_then assume_tac eta_expandSUC >> simp[] >> irule peta_eta >> simp[]
QED

Theorem takahashi_3_2_2:
  M =η=> N1 @@ N2 ⇔
    ∃k M1 M2. M = eta_expand k (M1 @@ M2) ∧ M1 =η=> N1 ∧ M2 =η=> N2
Proof
  iff_tac
  >- (‘∀M N. M =η=> N ⇒
             ∀N12 N1 N2.
               N12 = (N1,N2) ∧ N = N1 @@ N2 ⇒
               ∃k M1 M2. M = eta_expand k (M1 @@ M2) ∧ M1 =η=> N1 ∧
                         M2 =η=> N2’
        suffices_by metis_tac[] >>
      ho_match_mp_tac peta_genind >> qexists ‘λp. FV (FST p) ∪ FV (SND p)’>>
      rw[]
      >- metis_tac[peta_refl, eta_expand0]
      >- metis_tac[peta_app, eta_expand0] >>
      gvs[] >> rename [‘eta_expand k’, ‘LAM v’] >> qexists ‘SUC k’ >>
      ‘v ∉ FV (M1 @@ M2)’ by simp[] >>
      dxrule_then (assume_tac o GSYM) eta_expandSUC >> simp[] >> metis_tac[]) >>
  map_every qid_spec_tac [‘M’, ‘N1’, ‘N2’] >> simp[PULL_EXISTS] >>
  Induct_on ‘k’ >> simp[peta_app] >> rw[] >>
  Q_TAC (NEW_TAC "z") ‘FV (M1 @@ M2)’ >>
  drule_then assume_tac eta_expandSUC >> simp[] >>
  irule peta_eta >> gvs[]
QED

Theorem tpm_peta_R:
  M =η=> tpm π N ⇔ tpm π⁻¹ M =η=> N
Proof
  iff_tac >> strip_tac >> drule (iffRL tpm_peta)
  >- (disch_then $ qspec_then ‘π⁻¹’ mp_tac>>
      simp[Excl "tpm_peta"])
  >- (disch_then $ qspec_then ‘π’ mp_tac>>
      simp[Excl "tpm_peta"])
QED

Theorem tpm_peta_L:
  tpm π M =η=> N ⇔ M =η=> tpm π⁻¹ N
Proof
  simp[tpm_peta_R]
QED

Theorem peta_LAM2:
  ∀M v N. M =η=> LAM v N ⇒
          (∃M0. M = LAM v M0 ∧ M0 =η=> N) ∨
          ∃u M0. M = LAM u (M0 @@ VAR u) ∧ M0 =η=> LAM v N ∧ u # M0
Proof
  simp[SimpL “$==>”, Once peta_cases] >> rw[] >~
  [‘LAM v N = LAM v _’] >- metis_tac[peta_refl] >~
  [‘LAM u N1 = LAM v N2’]
  >- (gvs[LAM_eq_thm, tpm_eqr, tpm_peta_R, pmact_flip_args] >>
      drule_then assume_tac peta_FV >> gvs[]) >>
  metis_tac[]
QED

Theorem takahashi_3_2_3:
  M =η=> LAM x N ⇔ ∃k M'. M = eta_expand k (LAM x M') ∧ M' =η=> N
Proof
  iff_tac
  >- (‘∀M N0. M =η=> N0 ⇒
              ∀vN v N. vN = (v,N) ∧ N0 = LAM v N ⇒
                       ∃k M'. M = eta_expand k (LAM v M') ∧ M' =η=> N’
        suffices_by metis_tac[] >>
      ho_match_mp_tac peta_genind >> qexists ‘λp. FST p INSERT FV (SND p)’ >>
      rw[]
      >- metis_tac[eta_expand0, peta_refl]
      >- (gvs[LAM_eq_thm] >> qexists ‘0’ >> simp[LAM_eq_thm] >>
          simp[tpm_eqr] >> dxrule (iffRL tpm_peta) >>
          rename [‘tpm [(u,v)] N’] >>
          disch_then $ qspec_then ‘[(u,v)]’ mp_tac >>
          simp[Excl "tpm_peta"] >> strip_tac >> drule peta_FV >> simp[] >>
          strip_tac >> gvs[])
      >- (gvs[] >>
          rename [‘u ≠ v’, ‘LAM v N = LAM _ _ ⇒ _’] >>
          first_x_assum (resolve_then Any strip_assume_tac EQ_REFL) >>
          gvs[] >> first_assum $ irule_at Any>>
          rename [‘LAM v M’, ‘u # M’]>>
          ‘u # LAM v M’ by simp[] >>
          pop_assum (mp_then Any (assume_tac o GSYM) eta_expandSUC)>>
          simp[]>> metis_tac[])) >>
  map_every qid_spec_tac [‘M’, ‘x’, ‘N’] >> simp[PULL_EXISTS] >>
  Induct_on ‘k’>> simp[peta_lam] >> rw[] >>
  rename [‘eta_expand (SUC k) (LAM v M)’] >>
  ‘v # LAM v M’ by simp[] >> dxrule_then assume_tac eta_expandSUC >>
  simp[peta_eta]
QED

Theorem takahashi_3_3_1_0:
  ∀M M' v k. M =β=> M' ⇒ eta_expand k (LAM v M) @@ VAR v =β=> M'
Proof
  Induct_on ‘k’ >> simp[redex_grandbeta, var_grandbeta] >> rw[] >>
  ‘v # LAM v M’ by simp[] >>
  dxrule_then assume_tac eta_expandSUC >> simp[] >>
  simp[redex_grandbeta, var_grandbeta]
QED

Theorem takahashi_3_3_1:
  ∀M M' v k. M =β=> M' ⇒ eta_expand k (LAM v M) =β=> LAM v M'
Proof
  Cases_on ‘k’ >> simp[abs_grandbeta]>> rw[] >>
  ‘v # LAM v M’ by simp[] >>
  dxrule_then assume_tac eta_expandSUC >> simp[] >>
  simp[abs_grandbeta, takahashi_3_3_1_0]
QED

Theorem takahashi_3_3_2:
  ∀M M' N N' v k.
    M =β=> M' ∧ N =β=> N' ⇒
    eta_expand k (LAM v M) @@ N =β=> [N'/v]M'
Proof
  Induct_on ‘k’ >> simp[redex_grandbeta, var_grandbeta]
  >- metis_tac[] >>
  rpt strip_tac >>
  ‘v # LAM v M’ by simp[] >>
  drule_then assume_tac eta_expandSUC >> simp[redex_grandbeta] >>
  metis_tac[takahashi_3_3_1_0]
QED

Theorem eta_expandSUC':
  ∀v M k. v # M ⇒
          eta_expand (SUC k) M = eta_expand k (LAM v (M @@ VAR v))
Proof
  ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
  Induct_on ‘k’ >> rpt strip_tac
  >- (drule_then assume_tac eta_expandSUC >> simp[]) >>
  drule_then assume_tac eta_expandSUC  >>
  ‘v # LAM v (M @@ VAR v)’ by simp[] >>
  drule_then assume_tac eta_expandSUC  >>
  simp[]
QED

Theorem takahashi_3_3_3:
  ∀M M' N N' k.
    M =β=> M' ∧ N =β=> N' ⇒
    eta_expand k M @@ N =β=> M' @@ N'
Proof
  Cases_on ‘k’ >> simp[grandbeta_APP] >> rw[] >>
  Q_TAC (NEW_TAC "z") ‘FV M’ >> drule_then assume_tac eta_expandSUC' >>
  simp[] >>
  ‘[N'/z](M' @@ VAR z) = M' @@ N'’ suffices_by
    (disch_then (fn th => simp[GSYM th, Excl "SUB_THM"]) >>
     irule takahashi_3_3_2 >> simp[grandbeta_APP]) >>
  ‘z # M'’ by metis_tac[grandbeta_FV, SUBSET_DEF] >>
  simp[lemma14b]
QED

Theorem takahashi_3_3_4:
  ∀M M' k. k ≠ 0 ∧ M =β=> M' ⇒ eta_expand k M =β=> eta_expand 1 M'
Proof
  rw[] >> Q_TAC (NEW_TAC "z") ‘FV M ∪ FV M'’ >>
  Cases_on ‘k’ >> gvs[] >>
  qpat_assum ‘z # M’ (mp_then Any assume_tac eta_expandSUC') >>
  qpat_assum ‘z # M'’ (mp_then Any (qspec_then ‘0’ assume_tac) eta_expandSUC') >>
  gvs[] >> irule takahashi_3_3_1>> simp[grandbeta_APP, var_grandbeta]
QED

Theorem takahashi_3_4:
  ∀P N. P =β=> N ⇒ ∀M. M =η=> P ⇒ ∃P'. M =β=> P' ∧ P' =η=> N
Proof
  ho_match_mp_tac strong_grandbeta_gen_ind >> qexists ‘FV’ >> rw[]
  >- metis_tac[grandbeta_REFL]
  >- (qpat_x_assum ‘peta M (LAM v _)’ mp_tac >>
      simp[SimpL “$==>”, takahashi_3_2_3] >> rw[] >>
      first_x_assum $ drule_then strip_assume_tac >>
      irule_at Any takahashi_3_3_1 >>
      irule_at Any peta_lam >> metis_tac[])
  >- (qpat_x_assum ‘peta M (_ @@ _)’ mp_tac >>
      simp[SimpL “$==>”, takahashi_3_2_2] >> rw[] >>
      rename [‘eta_expand k (M0 @@ N0)’]>>
      ‘∃PM. M0 =β=> PM ∧ PM =η=> M2’ by metis_tac[] >>
      ‘∃PN. N0 =β=> PN ∧ PN =η=> N2’ by metis_tac[] >>
      Cases_on ‘k = 0’ >> simp[] >- metis_tac [grandbeta_APP, peta_app] >>
      gs[] >> ‘M0 @@ N0 =β=> PM @@ PN’ by simp[grandbeta_APP] >>
      irule_at Any takahashi_3_3_4 >> rpt $ first_assum $ irule_at Any >>
      Q_TAC (NEW_TAC "z") ‘FV (PM @@ PN)’ >>
      drule_then assume_tac eta_expandSUC >>
      ASM_REWRITE_TAC[arithmeticTheory.ONE] >> simp[] >>
      irule peta_eta >> gvs[peta_app]) >>
  rename [‘M =η=> LAM v M1 @@ N1’] >>
  ‘∃k M0 N0. M = eta_expand k (M0 @@ N0) ∧ M0 =η=> LAM v M1 ∧ N0 =η=> N1’
    by metis_tac[takahashi_3_2_2] >>
  gs[takahashi_3_2_3] >>
  rename [‘M = eta_expand k (eta_expand l (LAM v M0) @@ N0)’] >>
  ‘∃PM PN. M0 =β=> PM ∧ PM =η=> M2 ∧ N0 =β=> PN ∧ PN =η=> N2’
    by metis_tac[] >>
  Cases_on ‘k = 0’ >> simp[]
  >- (irule_at Any takahashi_3_3_2 >>
      rpt $ first_assum $ irule_at Any >> simp[peta_subst_closed]) >>
  irule_at Any takahashi_3_3_4 >> simp[] >>
  irule_at Any takahashi_3_3_2 >>
  rpt $ first_assum $ irule_at Any >> simp[peta_subst_closed] >>
  ‘v # ([PN/v]PM)’ by (simp[FV_SUB] >> rw[] >>
                       metis_tac[grandbeta_FV, SUBSET_DEF]) >>
  drule_then (qspec_then ‘0’ mp_tac) eta_expandSUC >> simp[] >>
  strip_tac >> irule peta_eta >> simp[peta_subst_closed]
QED

Theorem peta_gbetastar_flip:
  ∀M N P. peta M P ∧ P =β=>* N ⇒ ∃P'. M -β->* P' ∧ P' =η=> N
Proof
  Induct_on ‘RTC’ >> rw[]
  >- metis_tac[RTC_RULES, peta_reduction_eta] >>
  rename [‘M =η=> P’, ‘P =β=> N’, ‘N =β=>* Q’] >>
  ‘∃P'. M =β=> P' ∧ P' =η=> N’ by metis_tac[takahashi_3_4] >>
  ‘∃P''. P' -β->* P'' ∧ P'' =η=> Q’ by metis_tac[] >>
  irule_at Any (iffRL RTC_CASES_RTC_TWICE) >>
  first_assum $ irule_at (Pat ‘_ =η=> _’) >>
  first_assum $ irule_at Any >>
  simp[GSYM RTC_grandbeta]
QED

Theorem takahashi_3_5:
  ∀M N. M -βη->* N ⇒ ∃P. M -β->* P ∧ P -η->* N
Proof
  Induct_on ‘RTC’ >> rw[] >- metis_tac[RTC_RULES] >>
  rename [‘M0 -βη-> M1’] >>
  ‘M0 -β-> M1 ∨ M0 -η-> M1’ by gs[CC_RUNION_DISTRIB, RUNION]
  >- metis_tac[RTC_RULES] >>
  ‘M0 =η=> M1’ by simp[cc_eta_peta] >>
  ‘M1 =β=>* P’ by gs[RTC_grandbeta] >>
  drule_all peta_gbetastar_flip >>
  metis_tac[RTC_CASES_RTC_TWICE, RTC_RULES, RTC_peta_reduction_eta]
QED

Theorem takahashi_3_3_4_star:
  ∀M N k. M -β->* N ∧ k ≠ 0 ⇒ eta_expand k M -β->* eta_expand 1 N
Proof
  Induct_on ‘RTC’ >> rw[]
  >- (‘M =β=> M’ by simp[] >>
      drule_all takahashi_3_3_4 >> metis_tac[grandbeta_imp_betastar]) >>
  rename [‘M -β-> P’, ‘P -β->* N’] >>
  ‘M =β=> P’ by metis_tac[exercise3_3_1] >>
  drule_all takahashi_3_3_4 >> strip_tac >>
  ‘eta_expand 1 P -β->* eta_expand 1 N’ by simp[] >>
  metis_tac[RTC_CASES_RTC_TWICE, grandbeta_imp_betastar]
QED

Theorem has_bnf_eta_expand[simp]:
  ∀t k. has_bnf (eta_expand k t) ⇔ has_bnf t
Proof
  simp[EQ_IMP_THM, FORALL_AND_THM] >> conj_tac >~
  [‘has_bnf (eta_expand _ _) ⇒ _’]
  >- (Induct_on ‘k’>> simp[] >> qx_gen_tac ‘M’ >>
      Q_TAC (NEW_TAC "z") ‘FV M’ >> drule_then assume_tac eta_expandSUC >>
      simp[] >> simp[SimpL “$==>”, has_bnf_thm] >> strip_tac >>
      drule_all has_bnf_appVAR_LR >> metis_tac[]) >>
  Induct_on ‘k’ >> simp[] >> rw[] >>
  Q_TAC (NEW_TAC "z") ‘FV t’ >> drule_then assume_tac eta_expandSUC' >>
  simp[] >> first_x_assum irule >> simp[] >>
  irule has_bnf_appVAR_RL >> metis_tac[has_bnf_thm]
QED

Theorem peta_LAML_expk:
  ∀P vs M.
    P =η=> LAMl vs M ⇔
    ∃ls M0. LENGTH ls = LENGTH vs ∧
            P = FOLDR (λ(i,v) A. eta_expand i (LAM v A)) M0 (ZIP (ls,vs)) ∧
            M0 =η=> M
Proof
  Induct_on ‘vs’ >>
  simp[takahashi_3_2_3, PULL_EXISTS, LENGTH_CONS] >> metis_tac[]
QED

Theorem eta_expand_sum:
  ∀k1 k2 M. eta_expand k1 (eta_expand k2 M) = eta_expand (k1 + k2) M
Proof
  Induct_on ‘k1’ >> simp[] >> rw[] >>
  Q_TAC (NEW_TAC "z") ‘FV M’ >>
  drule_then assume_tac eta_expandSUC >>
  ‘z # eta_expand k2 M’ by simp[] >>
  drule_then assume_tac eta_expandSUC >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem N2SUM_EXISTS[local] :
  (∃m n. P (m + n)) ⇔ ∃k. P k
Proof
  metis_tac[DECIDE “x + 0n = x”]
QED

Definition eapp_def[simp]:
  eapp A [] = A ∧
  eapp A (h::t) = eapp (eta_expand (FST h) (A @@ SND h)) t
End

Theorem eapp_SNOC[simp]:
  eapp A (SNOC l f) = eta_expand (FST l) (eapp A f @@ SND l)
Proof
  map_every qid_spec_tac [‘A’, ‘l’] >> Induct_on ‘f’ >> simp[]
QED

Theorem peta_appstar_expk:
  ∀P M Ms x.
    P =η=> M @* Ms ⇔
    ∃k ks M0 M0s. LENGTH M0s = LENGTH Ms ∧ LENGTH ks = LENGTH Ms ∧
                  P = eapp M0 (ZIP(ks,M0s)) ∧
                  M0 =η=> M ∧
                  LIST_REL peta M0s Ms
Proof
  Induct_on ‘Ms’ >>
  simp[takahashi_3_2_1, takahashi_3_2_2, LENGTH_CONS, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem is_abs_eta_expand[simp]:
  is_abs (eta_expand k M) ⇔ 0 < k ∨ is_abs M
Proof
  Cases_on ‘k’ >> simp[] >> Q_TAC (NEW_TAC "z") ‘FV M’ >>
  drule_then assume_tac eta_expandSUC >> simp[]
QED

Theorem is_abs_eapp:
  is_abs (eapp M its) ⇔
  (∃p i t. its = p ++ [(i,t)] ∧ 0 < i) ∨ is_abs M ∧ its = []
Proof
  Cases_on ‘its’ using SNOC_CASES >> simp[] >>
  Cases_on ‘x’ >> simp[]
QED

Theorem takahashi_3_3_4star:
  ∀M N k. M =β=>* N ∧ k ≠ 0 ⇒ eta_expand k M =β=>* eta_expand 1 N
Proof
  Induct_on ‘RTC’ >> rpt strip_tac
  >- metis_tac[takahashi_3_3_4, grandbeta_REFL, RTC_SUBSET] >>
  drule_all_then assume_tac takahashi_3_3_4 >>
  metis_tac[DECIDE “1n ≠ 0”, RTC_RULES]
QED

Theorem eta_expand_beta_cong:
  ∀M N. M -β-> N ⇒ eta_expand k M -β-> eta_expand k N
Proof
  Induct_on ‘k’ >> simp[] >> rw[] >>
  Q_TAC (NEW_TAC "z") ‘FV M ∪ FV N’ >>
  rpt $ dxrule_then assume_tac eta_expandSUC >> simp[] >>
  simp[compat_closure_rules]
QED

Theorem eta_expand_betastar_cong:
  ∀M N. M -β->* N ⇒ eta_expand k M -β->* eta_expand k N
Proof
  Induct_on ‘RTC’ >> metis_tac[RTC_RULES, eta_expand_beta_cong]
QED

Theorem takahashi_3_6_0:
  ∀Q P. P =η=> Q ∧ bnf Q ⇒ has_bnf P
Proof
  completeInduct_on ‘size Q’ >> gvs[PULL_FORALL] >> rw[] >>
  qpat_x_assum ‘bnf _’ mp_tac >> simp[Once bnf_characterisation] >> rw[] >>
  gvs[peta_LAML_expk, peta_appstar_expk, takahashi_3_2_1] >>
  rename [‘LIST_REL peta Ps Qs’] >>
  qmatch_abbrev_tac ‘has_bnf (FOLDR lamf P' (ZIP(ls,vs)))’ >>
  ‘∃k. k ≤ 1 ∧ P' =β=>* eta_expand k (VAR v @* Ps)’
    by (simp[Abbr‘P'’] >> ‘LENGTH Ps = LENGTH ks’ by simp[] >>
        pop_assum mp_tac >> map_every qid_spec_tac [‘ks’, ‘Ps’] >>
        map_every (C qpat_x_assum kall_tac)[‘LIST_REL peta Ps Qs’,
                                            ‘LENGTH Ps = LENGTH Qs’,
                                            ‘LENGTH ks = LENGTH Qs’] >>
        Induct_on ‘Ps’ using SNOC_INDUCT >> simp[]
        >- (Cases_on ‘k = 0’
            >- (qexists ‘0’ >> simp[]) >>
            metis_tac[takahashi_3_3_4, DECIDE “x ≤ x”, RTC_SUBSET,
                      grandbeta_REFL]) >>
        simp[] >> rw[] >>
        Cases_on ‘ks’ using SNOC_CASES >> gvs[] >>
        simp[rich_listTheory.ZIP_SNOC, eapp_SNOC] >>
        first_x_assum (resolve_then Any
                                    (qx_choose_then ‘k2’ strip_assume_tac)
                                    EQ_REFL) >> gvs[] >>
        rename [‘eta_expand k3 (eapp _ _ @@ Plast)’] >>
        qabbrev_tac ‘MM = eapp (eta_expand k (VAR v)) (ZIP(l,Ps))’ >>
        Cases_on ‘k3 = 0’ >> gvs[]
        >- (Cases_on ‘k2 = 0’ >> gvs[]
            >- (qexists ‘0’ >> simp[] >> gvs[RTC_grandbeta] >>
                metis_tac[reduction_rules]) >>
            ‘MM @@ Plast =β=>* eta_expand k2 (VAR v @* Ps) @@ Plast’
              by (gvs[RTC_grandbeta] >> metis_tac[reduction_rules]) >>
            irule_at Any (cj 2 RTC_RULES_RIGHT1) >>
            first_assum $ irule_at Any >> qexists ‘0’ >>
            simp[takahashi_3_3_3]) >>
        Cases_on ‘k2 = 0’ >> gvs[]
        >- (‘MM @@ Plast =β=>* VAR v @* Ps @@ Plast’
              by (gvs[RTC_grandbeta] >> metis_tac[reduction_rules]) >>
            qexists ‘1’ >> simp[] >>
            irule takahashi_3_3_4star >> simp[]) >>
        ‘eta_expand k2 (VAR v @* Ps) @@ Plast =β=> VAR v @* Ps @@ Plast’
          by (irule takahashi_3_3_3 >> simp[]) >>
        irule_at Any takahashi_3_3_4star >> simp[] >>
        gvs[RTC_grandbeta] >> irule (iffRL RTC_CASES_RTC_TWICE) >>
        drule_then (irule_at Any) grandbeta_imp_betastar >>
        simp[reduction_rules]) >>
  ‘∀P. MEM P Ps ⇒ has_bnf P’
    by (rpt strip_tac >> first_x_assum irule >>
        gvs[MEM_EL, LIST_REL_EL_EQN, PULL_EXISTS] >>
        first_assum $ irule_at (Pat ‘_ =η=> _’) >> simp[] >>
        irule size_args_foldl_app >> simp[]) >>
  pop_assum mp_tac >> simp[has_bnf_thm] >>
  CONV_TAC (LAND_CONV (SCONV[GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM])) >>
  disch_then $ qx_choose_then ‘Nf’ strip_assume_tac >> gs[RTC_grandbeta] >>
  ‘eta_expand k' (VAR v @* Ps) -β->* eta_expand k' (VAR v @* MAP Nf Ps)’
    by (irule eta_expand_betastar_cong >> pop_assum mp_tac >>
        rpt (pop_assum kall_tac) >> Induct_on ‘Ps’ using SNOC_INDUCT >>
        simp[DISJ_IMP_THM, FORALL_AND_THM, MAP_SNOC] >> rw[] >>
        metis_tac[reduction_rules]) >>
  ‘bnf (eta_expand k' (VAR v @* MAP Nf Ps))’
    by (Cases_on ‘k' = 0’ >> simp[MEM_MAP, PULL_EXISTS] >>
        ‘k' = SUC 0’ by simp[] >>
        Q_TAC (NEW_TAC "z") ‘FV (VAR v @* MAP Nf Ps)’ >>
        drule_then assume_tac eta_expandSUC >> ASM_REWRITE_TAC[] >>
        simp[PULL_EXISTS, MEM_MAP]) >>
  ‘FOLDR lamf P' (ZIP (ls,vs)) =β=>* LAMl vs P'’
    by (simp[Abbr‘lamf’] >>
        qpat_x_assum ‘LENGTH ls = LENGTH vs’ mp_tac >>
        map_every qid_spec_tac [‘ls’, ‘vs’] >>
        rpt $ pop_assum kall_tac >> Induct >> simp[LENGTH_CONS, PULL_EXISTS] >>
        rpt strip_tac >> irule $ cj 2 RTC_RULES >>
        irule_at Any takahashi_3_3_1 >> irule_at Any grandbeta_REFL >>
        gvs[RTC_grandbeta] >> simp[reduction_rules]) >>
  gvs[RTC_grandbeta] >> irule_at Any (iffRL RTC_CASES_RTC_TWICE) >>
  first_assum (irule_at (Pat ‘FOLDR _ _ _ -β->* _’)) >>
  irule_at Any LAMl_betastar_cong >> simp[] >>
  metis_tac[RTC_CASES_RTC_TWICE]
QED

Theorem takahashi_3_6:
  ∀P Q. P =η=> Q ∧ has_bnf Q ⇒ has_bnf P
Proof
  simp[has_bnf_thm, PULL_EXISTS] >> rw[] >> gvs[GSYM RTC_grandbeta] >>
  drule_all peta_gbetastar_flip >> rw[] >>
  gs[RTC_grandbeta] >>
  metis_tac[has_bnf_thm, takahashi_3_6_0, RTC_CASES_RTC_TWICE]
QED

Theorem appstar_peta:
  peta (M @* Ms) Q ⇔ ∃Q0 Qs. Q = Q0 @* Qs ∧ peta M Q0 ∧ LIST_REL peta Ms Qs
Proof
  map_every qid_spec_tac [‘M’, ‘Q’] >> Induct_on ‘Ms’ using SNOC_INDUCT >>
  simp[] >>
  simp [SimpLHS, Once peta_cases] >> simp[PULL_EXISTS] >>
  simp[LIST_REL_SNOC, PULL_EXISTS, appstar_APPEND] >>
  metis_tac[peta_refl]
QED

Theorem peta_LAMl_I:
  M =η=> N ⇒ LAMl vs M =η=> LAMl vs N
Proof
  Induct_on ‘vs’ >> simp[] >> metis_tac[peta_rules]
QED

Theorem peta_bnf:
  peta (LAMl vs (VAR v @* Ms)) Q ⇔
    (∃u pvs pMs Qs. vs = pvs ++ [u] ∧ Ms = pMs ++ [VAR u] ∧
                    u ≠ v ∧ (∀M. MEM M pMs ⇒ u # M) ∧
                    LIST_REL peta pMs Qs ∧ Q = LAMl pvs (VAR v @* Qs)) ∨
    ∃Qs. Q = LAMl vs (VAR v @* Qs) ∧ LIST_REL peta Ms Qs
Proof
  map_every qid_spec_tac [‘Q’] >>
  Induct_on ‘vs’ >> simp[appstar_peta] >> simp[Once peta_cases] >>
  qx_gen_tac ‘u’ >> rw[EQ_IMP_THM] >~
  [‘LAM u (LAMl vs _) = LAM u (LAMl vs _)’]
  >- (disj2_tac >> irule_at Any EQ_REFL >> simp[LIST_REL_EL_EQN]) >~
  [‘LAM u (LAMl vs _) = LAM w M’, ‘M =η=> N’]
  >- (gvs[LAM_eq_thm] >> gvs[tpm_eqr] >>
      gvs[tpm_peta_L, pmact_flip_args, rich_listTheory.FOLDR_APPEND,
          DISJ_IMP_THM, FORALL_AND_THM] >>
      gvs[tpm_eql]
      >- (simp[LAM_eq_thm, pmact_flip_args] >>
          qpat_x_assum ‘w # LAMl _ _’ mp_tac >>
          simp[FV_LAMl, FV_appstar] >>
          gvs[LIST_REL_EL_EQN, MEM_EL] >> metis_tac[peta_FV]) >>
      ‘w # LAMl vs (VAR v @* Qs)’ suffices_by simp[] >>
      qpat_x_assum ‘w # LAMl _ _’ mp_tac >>
      simp[FV_LAMl, FV_appstar] >>
      gvs[LIST_REL_EL_EQN, MEM_EL] >> metis_tac[peta_FV]) >~
  [‘LAM u (LAMl vs _) = LAM w (M @@ VAR w)’]
  >- (gvs[LAM_eq_thm, app_eq_appstar_SNOC, FV_appstar, appstar_peta] >>
      simp[DISJ_IMP_THM, FORALL_AND_THM]
      >- metis_tac[] >>
      gvs[tpm_eqr, tpm_fresh, appstar_peta, FV_appstar] >> metis_tac[]) >~
  [‘u::vs = pvs ++ [w]’]
  >- (Cases_on ‘pvs’ >> gvs[]
      >- (simp[appstar_APPEND] >> irule_at Any EQ_REFL >>
          simp[appstar_peta] >>
          gvs[LIST_REL_EL_EQN, MEM_EL, FV_appstar] >> metis_tac[peta_FV]) >>
      simp[rich_listTheory.FOLDR_APPEND] >> disj1_tac >>
      simp[appstar_APPEND] >> irule_at Any EQ_REFL >> simp[] >>
      irule peta_LAMl_I >> irule peta_eta >> simp[appstar_peta] >>
      simp[FV_appstar] >> metis_tac[]) >>
  simp[] >> Cases_on ‘Qs = Ms’ >> simp[] >> disj1_tac >>
  rpt $ irule_at Any EQ_REFL >> irule peta_LAMl_I >> simp[appstar_peta]
QED

Theorem takahashi_3_6star:
  RTC peta M N ∧ has_bnf N ⇒ has_bnf M
Proof
  Induct_on ‘RTC’ >> metis_tac[takahashi_3_6]
QED

Theorem takahashi_3_7:
  ∀P Q. P =η=> Q ∧ bnf P ⇒ bnf Q
Proof
  completeInduct_on ‘size P’ >> gs[PULL_FORALL] >> rpt gen_tac >> strip_tac >>
  simp_tac (srw_ss()) [SimpL “$==>”, Once bnf_characterisation] >> rw[] >>
  gvs[peta_bnf, DISJ_IMP_THM, FORALL_AND_THM, appstar_APPEND] >>
  rpt strip_tac >> gvs[LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS] >>
  first_x_assum irule >> first_assum $ irule_at (Pat ‘_ =η=> _’) >>
  simp[]
  >- (rename [‘n < LENGTH Qs’, ‘LENGTH pMs = LENGTH Qs’] >>
      ‘n < LENGTH pMs’ by simp[] >>
      drule_then assume_tac size_args_foldl_app >>
      irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
      first_assum $ irule_at Any >>
      metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM,
                arithmeticTheory.LESS_EQ_REFL]) >>
  simp[size_args_foldl_app]
QED

Theorem takahashi_3_7star:
  ∀P Q. P -η->* Q ∧ bnf P ⇒ bnf Q
Proof
  simp[GSYM RTC_peta_reduction_eta] >> Induct_on ‘RTC’ >>
  metis_tac[RTC_RULES, takahashi_3_7]
QED

Theorem has_benf_has_bnf[simp]:
  has_benf M ⇔ has_bnf M
Proof
  rw[has_bnf_thm, has_benf_thm, EQ_IMP_THM]
  >- (drule_then strip_assume_tac takahashi_3_5 >>
      gvs[benf_def, GSYM RTC_peta_reduction_eta] >> rename [‘bnf N’] >>
      ‘has_bnf N’ by metis_tac[has_bnf_thm, RTC_RULES] >>
      drule_all takahashi_3_6star >> simp[has_bnf_thm] >>
      metis_tac[RTC_CASES_RTC_TWICE]) >>
  rename [‘M -β->* N’] >>
  assume_tac SN_eta >> gvs[SN_def, relationTheory.SN_def] >>
  qabbrev_tac ‘A = {P | N -η->* P}’>>
  ‘∃a. A a’ by (simp[Abbr‘A’] >> metis_tac[RTC_RULES]) >>
  drule_all (SRULE[PULL_EXISTS] WF_DEF |> iffLR) >>
  disch_then (qx_choose_then ‘nfe’ strip_assume_tac) >>
  gs[Abbr‘A’] >>
  ‘∀e. ¬(nfe -η-> e)’ by metis_tac[RTC_RULES_RIGHT1] >>
  ‘enf nfe’ by (simp[GSYM eta_normal_form_enf, normal_form_def] >>
                strip_tac >> drule can_reduce_reduces >>
                simp[]) >>
  ‘M -βη->* N’ by metis_tac[reduction_RUNION1] >>
  ‘N -βη->* nfe’ by metis_tac[reduction_RUNION2] >>
  simp[benf_def] >> metis_tac[RTC_CASES_RTC_TWICE, takahashi_3_7star]
QED



val _ = export_theory();
