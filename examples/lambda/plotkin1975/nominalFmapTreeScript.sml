Theory nominalFmapTree
Ancestors finite_map fmaptree nomset pred_set

Definition raw_fmtpm_def:
  raw_fmtpm (apm:α pmact) (bpm:β pmact) pi =
  fmtreerec (λa rt t0. FTNode (pmact apm pi a) (rt f_o pmact bpm pi⁻¹))
End

Overload fmt_pmact = “λapm bpm. mk_pmact (raw_fmtpm apm bpm)”
Overload fmtpm = “λapm bpm. pmact (fmt_pmact apm bpm)”

Theorem FINITE_pmact:
  FINITE { x | pmact b pi x ∈ FDOM f }
Proof
  irule (INST_TYPE [alpha |-> beta] $
         iffLR INJECTIVE_IMAGE_FINITE) >>
  qexists ‘pmact b pi’ >> conj_tac >- simp[] >>
  qmatch_abbrev_tac ‘FINITE A’ >> ‘A = FDOM f’ suffices_by simp[] >>
  simp[Abbr‘A’, EXTENSION] >> qx_gen_tac ‘a’ >> iff_tac
  >- simp[PULL_EXISTS] >>
  strip_tac >> qexists ‘pmact b pi⁻¹ a’ >> simp[]
QED


Theorem fmtpm_def:
  fmtpm a b = raw_fmtpm a b
Proof
  rw[GSYM pmact_bijections] >> rw[is_pmact_def]
  >- (‘(∀i. pmact a [] i = i) ∧ (∀j. pmact b [] j = j)’
        by metis_tac[pmact_nil] >>
      rename [‘raw_fmtpm a b [] t = t’] >>
      qid_spec_tac ‘t’ >> Induct using ft_ind >>
      simp[raw_fmtpm_def, fmtreerec_thm] >>
      ‘fmtreerec (λa rt t0. FTNode a (rt f_o pmact b [])) =
       raw_fmtpm a b []’ by simp[raw_fmtpm_def] >> pop_assum SUBST1_TAC >>
       simp[fmap_EXT] >> qx_gen_tac ‘k’ >> strip_tac >>
      simp[FAPPLY_f_o, FINITE_pmact])
  >- (rename [‘raw_fmtpm _ _ _ t = _’] >> qid_spec_tac ‘t’ >>
      Induct using ft_ind >> simp[raw_fmtpm_def, fmtreerec_thm] >>
      simp[GSYM raw_fmtpm_def] >> conj_tac
      >- simp[pmact_decompose] >>
      ‘pmact b (p1 ++ p2)⁻¹ = pmact b p2⁻¹ o pmact b p1⁻¹’
        by simp[FUN_EQ_THM, pmact_decompose, listTheory.REVERSE_APPEND] >>
      simp[] >> simp[GSYM f_o_ASSOC] >>
      simp[fmap_EXT, FDOM_f_o, FAPPLY_f_o, FINITE_pmact]) >>
  simp[FUN_EQ_THM] >> Induct using ft_ind >>
  simp[raw_fmtpm_def, fmtreerec_thm] >>
  conj_tac >- metis_tac[pmact_permeq] >>
  simp[GSYM raw_fmtpm_def] >>
  ‘p1⁻¹ == p2⁻¹’ by simp[permof_REVERSE_monotone] >>
  ‘pmact b p1⁻¹ = pmact b p2⁻¹’ by simp[pmact_permeq] >>
  simp[fmap_EXT, FINITE_pmact, FAPPLY_f_o, FDOM_f_o]
QED

Theorem fmtpm_thm:
  fmtpm (apm:α pmact) (bpm:β pmact) pi (FTNode a bt) =
  FTNode (pmact apm pi a) (fmpm bpm (fmt_pmact apm bpm) pi bt)
Proof
  simp[fmtpm_def, raw_fmtpm_def, fmtreerec_thm] >>
  simp[GSYM raw_fmtpm_def] >>
  simp[fmap_EXT, FAPPLY_f_o, FDOM_f_o, FINITE_pmact, fmpm_applied, fmtpm_def] >>
  simp[EXTENSION, fmpm_FDOM]
QED

Definition fmt_item_def:
  fmt_item = fmtreerec (λa rt t. a)
End

Theorem fmt_item_thm[simp]:
  fmt_item (FTNode a bt) = a
Proof
  simp[fmt_item_def, fmtreerec_thm]
QED

Definition fmt_map_def:
  fmt_map = fmtreerec (λa rt t. t)
End

Theorem fmt_map_thm[simp]:
  fmt_map (FTNode a bt) = bt
Proof
  simp[fmt_map_def, fmtreerec_thm]
QED

Theorem support_fmtpm:
  (∀a. FINITE (supp apm a)) ∧ (∀b. FINITE (supp bpm b)) ⇒
  ∀ft.
    support (fmt_pmact apm bpm) ft
            (supp apm (fmt_item ft) ∪
             supp (fm_pmact bpm (fmt_pmact apm bpm)) (fmt_map ft))
Proof
  strip_tac >> Induct using ft_ind >>
  gvs[support_def] >> simp[fmtpm_thm, supp_fresh]
QED

Theorem FDOM_fmpm:
  FDOM (fmpm kpm vpm pi fm) = setpm kpm pi (FDOM fm)
Proof
  simp[EXTENSION, fmpm_FDOM]
QED

Theorem FINITE_support_fmtpm:
  (∀a. FINITE (supp apm a)) ∧ (∀b. FINITE (supp bpm b)) ⇒
  ∀ft. ∃A. FINITE A ∧ support (fmt_pmact apm bpm) ft A
Proof
  strip_tac >> Induct using ft_ind >>
  rename [‘FTNode a fm’] >>
  gvs[GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] >>
  qexists ‘supp apm a ∪ supp (set_pmact bpm) (FDOM fm) ∪
           BIGUNION (IMAGE f (FDOM fm))’ >>
  simp[PULL_EXISTS] >>
  simp[support_def, fmtpm_thm] >> rw[] >> simp[supp_fresh] >>
  gvs[DECIDE “¬p ∨ q ⇔ p ⇒ q”, PULL_FORALL] >>
  simp[fmap_EXT, FDOM_fmpm, supp_fresh]
  >- simp[supp_setpm, PULL_EXISTS] >>
  RULE_ASSUM_TAC (ONCE_REWRITE_RULE [DECIDE “p ⇒ ¬q ⇔ q ⇒ ¬p”]) >>
  qx_gen_tac ‘k’ >> strip_tac >>
  gvs[supp_setpm, DECIDE “¬p ∨ q ⇔ p ⇒ q”, PULL_FORALL] >>
  ‘pmact bpm [(x,y)] k = k’
    by (irule supp_fresh >> metis_tac[]) >>
  simp[fmpm_applied] >>
  irule (iffLR support_def) >> metis_tac[]
QED

(*
Theorem INFINITE_supp:
  INFINITE (supp pm x) ⇒ supp pm x = UNIV
Proof
  simp[supp_def] >> strip_tac >> simp[Once EXTENSION] >>
  qx_gen_tac ‘a’ >> rpt strip_tac >>
  qmatch_assum_abbrev_tac ‘INFINITE supp_set’ >>
  Cases_on ‘{ b | pmact pm [(a,b)] x ≠ x} = ∅’
  >- (pop_assum mp_tac >> simp[EXTENSION] >> CCONTR_TAC >> gvs[] >>
      ‘∀b c. pmact pm [(b,c)] x = x’
        by (strip_tac >> gvs[Abbr‘supp_set’]) >>
      rpt gen_tac >> irule (iffLR pmact_injective) >>
      qexistsl [‘[(a,b)]’, ‘pm’] >> Cases_on ‘a = b’
      >- gvs[] >>
      simp[Once (GSYM pmact_sing_to_back), Excl "pmact_injective"]) >>
  pop_assum mp_tac >> simp[EXTENSION] >> qx_gen-tac
*)

Theorem FINITE_supp_fmtpm:
  (∀a. FINITE (supp apm a)) ∧ (∀b. FINITE (supp bpm b)) ⇒
  FINITE (supp (fmt_pmact apm bpm) ft)
Proof
  rpt strip_tac >>
  irule SUBSET_FINITE_I >> irule_at Any supp_smallest >>
  metis_tac[FINITE_support_fmtpm]
QED

Theorem supp_fmtpm:
  (∀a. FINITE (supp apm a)) ∧ (∀b. FINITE (supp bpm b)) ⇒
  supp (fmt_pmact apm bpm) ft =
  supp apm (fmt_item ft) ∪ supp (fm_pmact bpm (fmt_pmact apm bpm)) (fmt_map ft)
Proof
  strip_tac >>
  irule supp_unique_apart >> rpt strip_tac >~
  [‘support (fmt_pmact apm bpm) _ _ (* g *)’]
  >- (irule support_fmtpm >> simp[]) >~
  [‘fmtpm apm bpm [(a,b)] ft = ft (* a *)’]
  >- (pop_assum mp_tac >> gvs[] >>
      Cases_on ‘ft’ using fmaptree_nchotomy >> gvs[] >>
      simp[fmtpm_thm] >> metis_tac[supp_apart]) >>
  simp[FINITE_supp_fmtpm, fmap_supp, FINITE_supp_fmtpm, supp_setpm, PULL_EXISTS]
QED
