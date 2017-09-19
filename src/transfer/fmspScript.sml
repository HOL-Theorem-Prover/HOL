open HolKernel Parse boolLib bossLib;

open finite_mapTheory sptreeTheory transferTheory

val _ = new_theory "fmsp";

val FMSP_def = Define‘
  FMSP AN BC fm sp <=>
    !a n. AN a n ==> OPTREL BC (FLOOKUP fm a) (lookup n sp)’;

val FMSP_FDOM = Q.store_thm(
  "FMSP_FDOM",
  ‘(FMSP AN BC ===> (AN ===> (<=>))) FDOM domain’,
  simp[FMSP_def, FUN_REL_def] >> rpt strip_tac >> res_tac >>
  rename [‘OPTREL BC (FLOOKUP fm a) (lookup n sp)’] >> pop_assum mp_tac >>
  map_every Cases_on [‘FLOOKUP fm a’, ‘lookup n sp’] >>
  simp[optionTheory.OPTREL_def]
  >- (fs[sptreeTheory.lookup_NONE_domain, finite_mapTheory.flookup_thm] >>
      fs[IN_DEF]) >>
  ‘n ∈ domain sp’ by metis_tac[sptreeTheory.domain_lookup] >>
  fs[IN_DEF, finite_mapTheory.flookup_thm])

val FMSP_FEMPTY = Q.store_thm(
  "FMSP_FEMPTY",
  ‘FMSP AN BC FEMPTY LN’,
  simp[FMSP_def, lookup_def, optionTheory.OPTREL_def]);

val FMSP_FUPDATE = Q.store_thm(
  "FMSP_FUPDATE",
  ‘bi_unique AN ==>
     (FMSP AN BC ===> (AN ### BC) ===> FMSP AN BC)
       FUPDATE
       (λsp (n,v). insert n v sp)’,
  simp[FMSP_def, FUN_REL_def, PAIR_REL_def, pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  rename [‘FLOOKUP (fm |+ (k1,v)) k2’, ‘lookup m (insert n spv sp)’] >>
  Cases_on ‘k1 = k2’ >> fs[finite_mapTheory.FLOOKUP_DEF]
  >- (‘m = n’ by metis_tac[bi_unique_def, right_unique_def] >>
      fs[optionTheory.OPTREL_def]) >>
  simp[FAPPLY_FUPDATE_THM] >>
  ‘m <> n’ by metis_tac[bi_unique_def, left_unique_def] >>
  simp[lookup_insert]);

(*
val FMSP_FORALL = Q.store_thm(
  "FMSP_FORALL",
  ‘((FMSP AN BC ===> (<=>)) ===> (<=>)) (!) (!)’,
  simp[FMSP_def, FUN_REL_def] >> rpt strip_tac >>
  `a = \fm. a fm` by simp[FUN_EQ_THM] >> pop_assum SUBST1_TAC >>
  `b = \sp. b sp` by simp[FUN_EQ_THM] >> pop_assum SUBST1_TAC >>
  eq_tac >> strip_tac
*)


val _ = export_theory();
