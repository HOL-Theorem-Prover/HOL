open HolKernel Parse boolLib bossLib;

open finite_mapTheory sptreeTheory transferTheory pred_setTheory

val _ = new_theory "fmsp";

val FMSP_def = Define‘
  FMSP AN BC fm sp <=>
    (* wf sp /\ *) !a n. AN a n ==> OPTREL BC (FLOOKUP fm a) (lookup n sp)’;

val FMSP_FDOM = Q.store_thm(
  "FMSP_FDOM",
  ‘(FMSP AN BC |==> (AN |==> (<=>))) FDOM domain’,
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
     (FMSP AN BC |==> (AN ### BC) |==> FMSP AN BC)
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

Theorem FMSP_surj :
  bi_unique AN /\ surj BC ==> surj (FMSP AN BC)
Proof
  rw[surj_def, FMSP_def, left_unique_def, bi_unique_def, right_unique_def] >>
  rename [‘lookup _ sp’] >>
  qexists_tac ‘
    FUN_FMAP (\a. @b. BC b (THE (lookup (@n. AN a n) sp)))
             { a | ?n. AN a n /\ n IN domain sp }’ >>
  rw[optionTheory.OPTREL_def, finite_mapTheory.FLOOKUP_DEF] >>
  qmatch_abbrev_tac ‘_ NOTIN FDOM (FUN_FMAP FF FD) /\ _ \/ _’ >>
  qabbrev_tac ‘n2a = \n. @a. AN a n’ >>
  ‘!a n. AN a n ==> n2a n = a’
     by (rw[Abbr‘n2a’] >> SELECT_ELIM_TAC >> metis_tac[]) >>
  ‘FINITE FD’
    by (‘FD = IMAGE n2a { n | n IN domain sp /\ ?a. AN a n}’
          by (simp[Abbr‘FD’, EXTENSION, PULL_EXISTS] >> metis_tac[]) >>
        ‘FINITE { n | n IN domain sp /\ ?a. AN a n}’
          suffices_by simp[IMAGE_FINITE] >>
        irule SUBSET_FINITE_I >> qexists_tac ‘domain sp’ >>
        simp[SUBSET_DEF]) >>
  csimp[FUN_FMAP_DEF] >>
  ‘!a. a IN FD <=> ?n. AN a n /\ n IN domain sp’ by simp[Abbr‘FD’] >>
  simp[] >> ‘!m. AN a m <=> m = n’ by metis_tac[] >>
  simp[lookup_NONE_domain] >> Cases_on ‘n IN domain sp’ >> simp[] >>
  pop_assum mp_tac >> simp[domain_lookup, PULL_EXISTS] >>
  simp[Abbr‘FF’] >> rw[] >> SELECT_ELIM_TAC >> metis_tac[]
QED

Theorem FMSP_bitotal:
  bitotal BC /\ bi_unique AN ==> bitotal (FMSP AN BC)
Proof
  simp[bitotal_def, FMSP_surj] >>
  simp[total_def, surj_def] >> strip_tac >>
  ho_match_mp_tac fmap_INDUCT >> conj_tac >- metis_tac[FMSP_FEMPTY] >>
  rw[] >> rename [‘FMSP AN BC fm sp’, ‘fm |+ (k,v)’] >>
  fs[FMSP_def] >>
  reverse (Cases_on ‘?n. AN k n’)
  >- (fs[FAPPLY_FUPDATE_THM, FLOOKUP_DEF] >>
      ‘!a n. AN a n ==> a <> k’ by metis_tac[] >>
      asm_simp_tac (srw_ss() ++ SatisfySimps.SATISFY_ss) [] >>
      metis_tac[]) >>
  fs[] >>
  ‘(?v'. BC v v')’
     by metis_tac[bitotal_def, total_def] >>
  fs[GSYM FMSP_def] >>
  qexists_tac ‘(\sp (n,v). insert n v sp) sp (n,v')’ >>
  irule FUN_REL_COMB >> qexists_tac ‘AN ### BC’ >>
  conj_tac >- simp[PAIR_REL_def] >>
  irule FUN_REL_COMB >> qexists_tac ‘FMSP AN BC’ >>
  simp[FMSP_FUPDATE]
QED

val FMSP_FUNION = Q.store_thm(
  "FMSP_FUNION",
  ‘(FMSP AN BC |==> FMSP AN BC |==> FMSP AN BC) FUNION union’,
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
   (FMSP AN BC |==> AN |==> FMSP AN BC) (\\) (combin$C delete)’,
  simp[FUN_REL_def, FMSP_def] >> rpt strip_tac >>
  rename [‘FLOOKUP (fm \\ k1) k2’, ‘lookup m (delete n sp)’] >>
  Cases_on ‘k1 = k2’ >> simp[FLOOKUP_DEF, lookup_delete]
  >- (‘m = n’ by metis_tac[bi_unique_def, right_unique_def] >>
      simp[optionTheory.OPTREL_def]) >>
  ‘m <> n’ by metis_tac[bi_unique_def, left_unique_def] >>
  simp[DOMSUB_FAPPLY_THM] >> fs[FLOOKUP_DEF]);

val _ = export_theory();
