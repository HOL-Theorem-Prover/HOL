open HolKernel Parse boolLib bossLib;

open finite_mapTheory sptreeTheory transferTheory pred_setTheory

open transferLib

val _ = new_theory "fmsp";

Definition FMSP_def:
  FMSP AN BC fm sp <=>
    wf sp /\ !a n. AN a n ==> OPTREL BC (FLOOKUP fm a) (lookup n sp)
End

Theorem FMSP_FDOM[transfer_rule]:
  (FMSP AN BC |==> (AN |==> (<=>))) FDOM domain
Proof
  simp[FMSP_def, FUN_REL_def] >> rpt strip_tac >> res_tac >>
  rename [‘OPTREL BC (FLOOKUP fm a) (lookup n sp)’] >> pop_assum mp_tac >>
  map_every Cases_on [‘FLOOKUP fm a’, ‘lookup n sp’] >>
  simp[optionTheory.OPTREL_def]
  >- (fs[sptreeTheory.lookup_NONE_domain, finite_mapTheory.flookup_thm] >>
      fs[IN_DEF]) >>
  ‘n IN domain sp’ by metis_tac[sptreeTheory.domain_lookup] >>
  fs[IN_DEF, flookup_thm]
QED

Theorem FMSP_FEMPTY[transfer_rule]:
  FMSP AN BC FEMPTY LN
Proof
  simp[FMSP_def, lookup_def, optionTheory.OPTREL_def, wf_def]
QED

Theorem FMSP_FUPDATE[transfer_rule]:
  bi_unique AN ==>
  (FMSP AN BC |==> (AN ### BC) |==> FMSP AN BC)
       FUPDATE
       (λsp (n,v). insert n v sp)
Proof
  simp[FMSP_def, FUN_REL_def, PAIR_REL_def, pairTheory.FORALL_PROD,
       wf_insert] >>
  rpt strip_tac >>
  rename [‘FLOOKUP (fm |+ (k1,v)) k2’, ‘lookup m (insert n spv sp)’] >>
  Cases_on ‘k1 = k2’ >> fs[finite_mapTheory.FLOOKUP_DEF]
  >- (‘m = n’ by metis_tac[bi_unique_def, right_unique_def] >>
      fs[optionTheory.OPTREL_def]) >>
  simp[FAPPLY_FUPDATE_THM] >>
  ‘m <> n’ by metis_tac[bi_unique_def, left_unique_def] >>
  simp[lookup_insert]
QED

Theorem FMSP_total[transfer_simp]:
  total AN /\ total BC /\ bi_unique AN ==> total (FMSP AN BC)
Proof
  simp[total_def, FMSP_def, bi_unique_def, left_unique_def, right_unique_def] >>
  strip_tac >> Induct >>
  rpt strip_tac
  >- (qexists ‘LN’ >> simp[]) >>
  rename [‘fm |+ (k,v)’, ‘wf sp’] >>
  ‘?n c. AN k n /\ BC v c’ by metis_tac[] >>
  qexists ‘insert n c sp’ >> rw[wf_insert] >>
  rw[lookup_insert, FLOOKUP_SIMP] >> metis_tac[]
QED

Theorem FMSP_FUNION[transfer_rule]:
  (FMSP AN BC |==> FMSP AN BC |==> FMSP AN BC) FUNION union
Proof
  simp[FUN_REL_def, FMSP_def, FLOOKUP_DEF, lookup_union, FUNION_DEF,
       wf_union] >>
  rpt strip_tac >>
  rename [‘k IN FDOM fm1 \/ k IN FDOM fm2’, ‘AN k n’,
          ‘option_CASE (lookup n sp1)’] >>
  Cases_on ‘k IN FDOM fm1’ >> simp[]
  >- (Q_TAC (fn t => first_x_assum (qspecl_then [‘k’, ‘n’] mp_tac o
                                    assert (free_in t o concl))) `fm1` >>
      dsimp[optionTheory.OPTREL_def]) >>
  Q_TAC (fn t => first_x_assum (qspecl_then [‘k’, ‘n’] mp_tac o
                                assert (free_in t o concl))) `fm1` >>
  dsimp[optionTheory.OPTREL_def] >>
  first_x_assum (qspecl_then [‘k’, ‘n’] mp_tac) >>
  dsimp[optionTheory.OPTREL_def]
QED

Theorem FMSP_FDOMSUB[transfer_rule]:
  bi_unique AN ==>
  (FMSP AN BC |==> AN |==> FMSP AN BC) (\\) (flip delete)
Proof
  simp[FUN_REL_def, FMSP_def, wf_delete] >> rpt strip_tac >>
  rename [‘FLOOKUP (fm \\ k1) k2’, ‘lookup m (delete n sp)’] >>
  Cases_on ‘k1 = k2’ >> simp[FLOOKUP_DEF, lookup_delete]
  >- (‘m = n’ by metis_tac[bi_unique_def, right_unique_def] >>
      simp[optionTheory.OPTREL_def]) >>
  ‘m <> n’ by metis_tac[bi_unique_def, left_unique_def] >>
  simp[DOMSUB_FAPPLY_THM] >> fs[FLOOKUP_DEF]
QED

Theorem FMSP_LOOKUP[transfer_rule]:
  (FMSP AN BC |==> AN |==> OPTREL BC) FLOOKUP (flip lookup)
Proof
  simp[FUN_REL_def, FMSP_def]
QED

Theorem FMSP_EQ[transfer_rule]:
  bi_unique AN /\ bitotal AN /\ bi_unique BC ==>
  (FMSP AN BC |==> FMSP AN BC |==> (<=>)) $= $=
Proof
  simp[FUN_REL_def, FMSP_def, EQ_IMP_THM] >>
  rpt strip_tac >> gvs[]
  >- (simp[spt_eq_thm] >>
      gvs[bi_unique_def, left_unique_def, right_unique_def, bitotal_def,
          surj_def] >>
      qx_gen_tac ‘n’ >>
      ‘?k. AN k n’ by metis_tac[] >> ntac 2 (first_x_assum drule) >>
      Cases_on ‘FLOOKUP a k’ >> simp[optionTheory.OPTREL_def] >>
      metis_tac[]) >>
  simp[FLOOKUP_EXT, FUN_EQ_THM] >> qx_gen_tac ‘k’ >>
  ‘?n. AN k n’ by metis_tac[bitotal_def, total_def] >>
  ntac 2 (first_x_assum drule) >> Cases_on ‘lookup n b’ >>
  simp[optionTheory.OPTREL_def] >>
  metis_tac[bi_unique_def, left_unique_def]
QED

Theorem total_eq[transfer_simp]:
  total $=
Proof
  simp[total_def]
QED

Theorem bi_unique_eq[transfer_simp]:
  bi_unique $=
Proof
  simp[bi_unique_def]
QED

Theorem surj_eq[transfer_simp]:
  surj $=
Proof
  simp[surj_def]
QED

Theorem left_unique_FMSP[transfer_safe]:
  total AN /\ left_unique CD ==> left_unique (FMSP AN CD)
Proof
  simp[left_unique_def, right_unique_def, FMSP_def, total_def] >>
  rpt strip_tac >>
  simp[FLOOKUP_EXT, FUN_EQ_THM] >>
  rename [‘FLOOKUP fm1 _ = FLOOKUP fm2 _’] >> qx_gen_tac ‘a’ >>
  ‘?n. AN a n’ by metis_tac[] >>
  pop_assum (fn th => ntac 2 (first_x_assum (C (mp_then Any assume_tac) th))) >>
  Cases_on ‘FLOOKUP fm1 a’ >> gvs[optionTheory.OPTREL_SOME] >> metis_tac[]
QED

Theorem right_unique_FMSP[transfer_safe]:
  surj AN /\ right_unique CD ==> right_unique (FMSP AN CD)
Proof
  simp[left_unique_def, right_unique_def, FMSP_def, surj_def] >>
  rpt strip_tac >>
  simp[sptreeTheory.spt_eq_thm] >> gen_tac >>
  rename [‘lookup n sp1 = lookup n sp2’, ‘FLOOKUP fm _’] >>
  ‘?a. AN a n’ by metis_tac[] >>
  pop_assum (fn th => ntac 2 (first_x_assum (C (mp_then Any assume_tac) th))) >>
  Cases_on ‘lookup n sp1’ >> gvs[optionTheory.OPTREL_SOME] >> metis_tac[]
QED

Theorem RRANGE_FMSP[transfer_simp]:
  total AN /\ bi_unique AN /\ surj BC ==>
  RRANGE (FMSP AN BC) = wf
Proof
  simp[relationTheory.RRANGE, FMSP_def, FUN_EQ_THM, EQ_IMP_THM, FORALL_AND_THM,
       PULL_EXISTS, bi_unique_def, right_unique_def, left_unique_def,
       surj_def] >>
  rpt strip_tac >>
  rename [‘wf sp’] >>
  qexists ‘FUN_FMAP (λa. @b. OPTREL BC (SOME b) (lookup (@n. AN a n) sp))
                    { a | ?n. AN a n /\ n IN domain sp}’ >>
  rw[] >>
  qabbrev_tac ‘D = { m | m IN domain sp /\ ?a. AN a m}’ >>
  ‘FINITE D’ by (irule SUBSET_FINITE >> qexists ‘domain sp’ >>
                 simp[SUBSET_DEF, Abbr‘D’]) >>
  ‘FINITE { a | ?n. AN a n /\ n IN domain sp}’
    by (‘?f. {a | ?n. AN a n /\ n IN domain sp } = IMAGE f D’
          suffices_by simp[PULL_EXISTS] >>
        qexists ‘λm. @a. AN a m’ >> simp[EXTENSION] >>
        simp[EQ_IMP_THM, FORALL_AND_THM, PULL_EXISTS] >> rpt strip_tac
        >- (simp[Abbr‘D’, PULL_EXISTS] >>
            first_assum $ irule_at (Pat ‘_ IN domain sp’) >>
            first_assum $ irule_at Any >> SELECT_ELIM_TAC >> metis_tac[]) >>
        gvs[Abbr‘D’] >> first_assum $ irule_at Any >> SELECT_ELIM_TAC >>
        metis_tac[]) >>
  Cases_on ‘lookup n sp’ >>
  simp[optionTheory.OPTREL_def, FLOOKUP_SIMP]
  >- (qx_gen_tac ‘m’ >> Cases_on ‘AN a m’ >> simp[] >>
      metis_tac[lookup_NONE_domain]) >>
  conj_tac
  >- metis_tac[domain_lookup] >>
  SELECT_ELIM_TAC >> rw[PULL_EXISTS]
  >- (‘(@n. AN a n) = n’ by (SELECT_ELIM_TAC >> metis_tac[]) >>
      simp[]) >>
  ‘(@n. AN a n) = n’ by (SELECT_ELIM_TAC >> metis_tac[]) >> gvs[]
QED

Definition sp2fm_def:
  sp2fm sp = FUN_FMAP (λk. THE (lookup k sp)) (domain sp)
End

Theorem FDOM_sp2fm[simp]:
  FDOM (sp2fm sp) = domain sp
Proof
  simp[sp2fm_def]
QED

Theorem FLOOKUP_sp2fm[simp]:
  FLOOKUP (sp2fm sp) k = lookup k sp
Proof
  simp[FLOOKUP_SIMP, sp2fm_def] >> rw[] >>
  simp[lookup_NONE_domain] >> gs[domain_lookup]
QED

Theorem sp2fm_thm[simp]:
  sp2fm LN = FEMPTY /\
  sp2fm (insert k v sp) = sp2fm sp |+ (k,v)
Proof
  simp[FLOOKUP_EXT, FUN_EQ_THM, FLOOKUP_SIMP, lookup_insert] >> rw[]
QED

Theorem sp2fm_correct:
  FMSP (=) (=) fm sp <=> wf sp /\ fm = sp2fm sp
Proof
  simp[FMSP_def, FLOOKUP_EXT, FUN_EQ_THM]
QED

Definition fm2sp_def:
  fm2sp fm = ITFMAP insert fm LN
End

Theorem fm2sp_thm[simp]:
  fm2sp FEMPTY = LN /\
  fm2sp (fm |+ (k,v)) = insert k v $ fm2sp (fm \\ k)
Proof
  conj_tac >- simp[fm2sp_def] >>
  map_every qid_spec_tac [‘k’, ‘v’, ‘fm’] >>
  simp[fm2sp_def] >> irule $ cj 2 ITFMAP_thm>>
  metis_tac[insert_swap]
QED

Theorem wf_fm2sp[simp]:
  !fm. wf (fm2sp fm)
Proof
  Induct >> simp[wf_insert, DOMSUB_NOT_IN_DOM]
QED

Theorem lookup_fm2sp[simp]:
  lookup k (fm2sp fm) = FLOOKUP fm k
Proof
  Induct_on ‘fm’ >> rw[lookup_insert, DOMSUB_NOT_IN_DOM] >>
  rw[FLOOKUP_SIMP]
QED

Theorem fm2sp_sp2fm[simp]:
  !sp. wf sp ==> fm2sp (sp2fm sp) = sp
Proof
  simp[spt_eq_thm]
QED

Theorem sp2fm_fm2sp[simp]:
  !fm. sp2fm (fm2sp fm) = fm
Proof
  Induct >> simp[DOMSUB_NOT_IN_DOM]
QED

Theorem fm2sp_DOMSUB:
  fm2sp (fm \\ k) = delete k (fm2sp fm)
Proof
  simp[spt_eq_thm, wf_delete, lookup_delete,
       DOMSUB_FLOOKUP_THM] >> rw[]
QED

val _ = export_theory();
