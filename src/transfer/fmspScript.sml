open HolKernel Parse boolLib bossLib;

open finite_mapTheory sptreeTheory transferTheory pred_setTheory

val _ = new_theory "fmsp";

val FMSP_def = Define‘
  FMSP AN BC fm sp <=>
    (* wf sp /\ *) !a n. AN a n ==> OPTREL BC (FLOOKUP fm a) (lookup n sp)’;

val FMSP_FDOM = Q.store_thm(
  "FMSP_FDOM",
  ‘(FMSP AN BC ===> (AN ===> (<=>))) FDOM domain’,
  simp[FMSP_def, FUN_REL_def] >> rpt strip_tac >> res_tac >>
  rename [‘OPTREL BC (FLOOKUP fm a) (lookup n sp)’] >> pop_assum mp_tac >>
  map_every Cases_on [‘FLOOKUP fm a’, ‘lookup n sp’] >>
  simp[optionTheory.OPTREL_def]
  >- (fs[sptreeTheory.lookup_NONE_domain, finite_mapTheory.flookup_thm] >>
      fs[IN_DEF]) >>
  ‘n IN domain sp’ by metis_tac[sptreeTheory.domain_lookup] >>
  fs[IN_DEF, finite_mapTheory.flookup_thm])

val FMSP_FEMPTY = Q.store_thm(
  "FMSP_FEMPTY",
  ‘FMSP AN BC FEMPTY LN’,
  simp[FMSP_def, lookup_def, optionTheory.OPTREL_def, wf_def]);

val FMSP_FUPDATE = Q.store_thm(
  "FMSP_FUPDATE",
  ‘bi_unique AN ==>
     (FMSP AN BC ===> (AN ### BC) ===> FMSP AN BC)
       FUPDATE
       (\sp (n,v). insert n v sp)’,
  simp[FMSP_def, FUN_REL_def, PAIR_REL_def, pairTheory.FORALL_PROD,
       wf_insert] >>
  rpt strip_tac >>
  rename [‘FLOOKUP (fm |+ (k1,v)) k2’, ‘lookup m (insert n spv sp)’] >>
  Cases_on ‘k1 = k2’ >> fs[finite_mapTheory.FLOOKUP_DEF]
  >- (‘m = n’ by metis_tac[bi_unique_def, right_unique_def] >>
      fs[optionTheory.OPTREL_def]) >>
  simp[FAPPLY_FUPDATE_THM] >>
  ‘m <> n’ by metis_tac[bi_unique_def, left_unique_def] >>
  simp[lookup_insert]);

val FMSP_bitotal = Q.store_thm(
  "FMSP_bitotal",
  ‘bitotal AN /\ bitotal BC /\ bi_unique AN ==> bitotal (FMSP AN BC)’,
  strip_tac >> simp[bitotal_def, surj_def, total_def] >> conj_tac
  >- (ho_match_mp_tac fmap_INDUCT >> conj_tac >- metis_tac[FMSP_FEMPTY] >>
      rw[] >> rename [‘FMSP AN BC fm sp’, ‘fm |+ (k,v)’] >>
      ‘(?n. AN k n) /\ (?v'. BC v v')’
         by metis_tac[bitotal_def, total_def] >>
      qexists_tac ‘(\sp (n,v). insert n v sp) sp (n,v')’ >>
      irule FUN_REL_COMB >> qexists_tac ‘AN ### BC’ >>
      conj_tac >- simp[PAIR_REL_def] >>
      irule FUN_REL_COMB >> qexists_tac ‘FMSP AN BC’ >>
      simp[FMSP_FUPDATE]) >>
  qx_gen_tac ‘sp’ >>
  fs[bitotal_def] >>
  `?kf. !k. AN k (kf k)` by metis_tac[total_def] >>
  `?vf. !v. BC (vf v) v` by metis_tac[surj_def] >>
  qexists_tac
    ‘FUN_FMAP (\k:'a. vf (THE (lookup (kf k) sp))) { k | kf k IN domain sp}’ >>
  simp[FMSP_def, FLOOKUP_DEF] >>
  ‘!k1 k2. (kf k1 = kf k2) <=> (k1 = k2)’
    by (simp[EQ_IMP_THM] >> metis_tac[bi_unique_def, left_unique_def]) >>
  ‘BIJ kf univ(:'a) univ(:num)’
    by (simp[BIJ_DEF, INJ_DEF, SURJ_DEF] >>
        fs[total_def, left_unique_def, right_unique_def, bi_unique_def,
           surj_def] >>
        metis_tac[]) >>
  ‘!n. kf (LINV kf univ(:'a) n) = n’
    by (strip_tac >> irule BIJ_LINV_INV >> qexists_tac `UNIV` >> simp[]) >>
  ‘!a. LINV kf univ(:'a) (kf a) = a’
    by (strip_tac >> irule LINV_DEF >> simp[] >> metis_tac[INJ_DEF, IN_UNIV]) >>
  ‘{k | kf k IN domain sp} = IMAGE (LINV kf UNIV) (domain sp)’
    by (dsimp[EXTENSION, EQ_IMP_THM] >> metis_tac[]) >>
  simp[] >> simp[FUN_FMAP_DEF] >> rw[]
  >- (simp[] >> rename1 ‘AN (LINV _ _ m) n’ >>
      ‘n = kf (LINV kf univ(:'a) m)’
        by metis_tac[bi_unique_def, left_unique_def] >>
      pop_assum mp_tac >> simp[] >> strip_tac >>
      ‘?v. lookup m sp = SOME v’
        by (Cases_on ‘lookup m sp’ >> fs[lookup_NONE_domain]) >>
      simp[optionTheory.OPTREL_def]) >>
  fs[] >>
  rename1 ‘AN a n’ >>
  first_x_assum (qspec_then ‘kf a’ mp_tac) >> simp[] >>
  `kf a = n` by metis_tac[bi_unique_def, left_unique_def] >> simp[] >>
  strip_tac >>
  `lookup n sp = NONE` by simp[lookup_NONE_domain] >>
  simp[optionTheory.OPTREL_def]);

val FMSP_FORALL = Q.store_thm(
  "FMSP_FORALL",
  ‘bitotal AN /\ bitotal BC /\ bi_unique AN ==>
   ((FMSP AN BC ===> (<=>)) ===> (<=>)) (!) (!)’,
  simp[FUN_REL_def] >> rpt strip_tac >>
  `a = \fm. a fm` by simp[FUN_EQ_THM] >> pop_assum SUBST1_TAC >>
  `b = \sp. b sp` by simp[FUN_EQ_THM] >> pop_assum SUBST1_TAC >>
  eq_tac >> strip_tac
  >- (qx_gen_tac `sp` >>
      ‘?fm. FMSP AN BC fm sp’
        by metis_tac[bitotal_def, surj_def, FMSP_bitotal] >>
      metis_tac[])
  >- (qx_gen_tac `fm` >>
      ‘?sp. FMSP AN BC fm sp’
        by metis_tac[bitotal_def, total_def, FMSP_bitotal] >>
      metis_tac[]));

val FMSP_FUNION = Q.store_thm(
  "FMSP_FUNION",
  ‘(FMSP AN BC ===> FMSP AN BC ===> FMSP AN BC) FUNION union’,
  simp[FUN_REL_def, FMSP_def, FLOOKUP_DEF, lookup_union, FUNION_DEF] >>
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
  dsimp[optionTheory.OPTREL_def])

val FMSP_FDOMSUB = Q.store_thm(
  "FMSP_FDOMSUB",
  ‘bi_unique AN ==>
   (FMSP AN BC ===> AN ===> FMSP AN BC) (\\) (combin$C delete)’,
  simp[FUN_REL_def, FMSP_def] >> rpt strip_tac >>
  rename [‘FLOOKUP (fm \\ k1) k2’, ‘lookup m (delete n sp)’] >>
  Cases_on ‘k1 = k2’ >> simp[FLOOKUP_DEF, lookup_delete]
  >- (‘m = n’ by metis_tac[bi_unique_def, right_unique_def] >>
      simp[optionTheory.OPTREL_def]) >>
  ‘m <> n’ by metis_tac[bi_unique_def, left_unique_def] >>
  simp[DOMSUB_FAPPLY_THM] >> fs[FLOOKUP_DEF]);

val _ = export_theory();
