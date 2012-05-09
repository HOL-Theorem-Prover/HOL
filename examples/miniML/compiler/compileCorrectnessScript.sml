open HolKernel bossLib boolLib listTheory pred_setTheory finite_mapTheory alistTheory lcsymtacs
open SatisfySimps compileTerminationTheory intLangTheory

val _ = new_theory "compileCorrectness"

(* Invariants *)

val good_cm_cw_def = Define`
  good_cm_cw cm cw =
  (FDOM cw = FRANGE cm) ∧
  (FRANGE cw = FDOM cm) ∧
  (∀x. x ∈ FDOM cm ⇒ (cw ' (cm ' x) = x)) ∧
  (∀y. y ∈ FDOM cw ⇒ (cm ' (cw ' y) = y))`

val good_cmaps_def = Define`
good_cmaps cenv cm cw =
  (∀cn n. do_con_check cenv cn n ⇒ cn IN FDOM cm) ∧
  good_cm_cw cm cw`

(*
val observable_v_def = tDefine "observable_v"`
  (observable_v (Lit l) = T) ∧
  (observable_v (Conv cn vs) = EVERY observable_v vs) ∧
  (observable_v _ = F)`(
WF_REL_TAC `measure v_size` >>
rw[MiniMLTerminationTheory.exp9_size_thm] >>
Q.ISPEC_THEN `v_size` imp_res_tac SUM_MAP_MEM_bound >>
srw_tac[ARITH_ss][])
val _ = export_rewrites["observable_v_def"]

val observable_Cv_def = tDefine "observable_Cv"`
  (observable_Cv (CLit l) = T) ∧
  (observable_Cv (CConv cn vs) = EVERY observable_Cv vs) ∧
  (observable_Cv _ = F)`(
WF_REL_TAC `measure Cv_size` >>
rw[Cexp8_size_thm] >>
Q.ISPEC_THEN `Cv_size` imp_res_tac SUM_MAP_MEM_bound >>
srw_tac[ARITH_ss][])
val _ = export_rewrites["observable_Cv_def"]
*)

val good_G_def = Define`
  good_G G =
    (∀cm v Cv. v_Cv G cm v Cv ⇒ G cm v Cv) ∧
    (∀cm v Cv cw.
      good_cm_cw cm cw ∧
      G cm v Cv ⇒ ((v_to_ov v) = (Cv_to_ov cw) Cv))`

val a_good_G_exists = store_thm(
"a_good_G_exists",
``∃G. good_G G``,
qexists_tac `v_Cv (K (K (K F)))` >>
rw[good_G_def] >- (
  qsuff_tac `∀G cm v Cv. v_Cv G cm v Cv ⇒ (G = v_Cv (K(K(K F)))) ⇒ v_Cv (K(K(K F))) cm v Cv` >- rw[] >>
  ho_match_mp_tac v_Cv_ind >>
  rw[] >>
  rw[v_Cv_cases] >>
  fsrw_tac[boolSimps.ETA_ss][] ) >>
qsuff_tac `∀G cm v Cv. v_Cv G cm v Cv ⇒ (G = K(K(K F))) ∧ good_cm_cw cm cw ⇒ (v_to_ov v = Cv_to_ov cw Cv)` >- (rw[] >> PROVE_TAC[]) >>
ho_match_mp_tac v_Cv_ind >>
rw[] >- fs[good_cm_cw_def] >>
pop_assum mp_tac >>
srw_tac[boolSimps.ETA_ss][] >>
rw[MAP_EQ_EVERY2] >>
PROVE_TAC[EVERY2_LENGTH])

val tac =
WF_REL_TAC `inv_image $< (λx. case x of (INL e) => exp_size e | (INR v) => v_size v)` >>
rw[MiniMLTerminationTheory.exp1_size_thm,
   MiniMLTerminationTheory.exp3_size_thm,
   MiniMLTerminationTheory.exp6_size_thm,
   MiniMLTerminationTheory.exp8_size_thm,
   MiniMLTerminationTheory.exp9_size_thm] >>
srw_tac[ARITH_ss][] >>
imp_res_tac ALOOKUP_MEM >>
(Q.ISPEC_THEN `exp2_size` imp_res_tac SUM_MAP_MEM_bound) >>
(Q.ISPEC_THEN `exp5_size` imp_res_tac SUM_MAP_MEM_bound) >>
(Q.ISPEC_THEN `exp7_size` imp_res_tac SUM_MAP_MEM_bound) >>
(Q.ISPEC_THEN `exp_size` imp_res_tac SUM_MAP_MEM_bound) >>
(Q.ISPEC_THEN `v_size` imp_res_tac SUM_MAP_MEM_bound) >>
fsrw_tac[ARITH_ss][MiniMLTheory.exp_size_def]

(*
something broken in tDefine. don't need this now anyway...
val FV_def = tDefine "FV"`
(FV_exp (Raise _) = {}) ∧
(FV_exp (Val v) = FV_v v) ∧
(FV_exp (Con _ ls) = BIGUNION (IMAGE FV_exp (set ls))) ∧
(FV_exp (Var x) = {x}) ∧
(FV_exp (Fun x e) = FV_exp e DIFF {x}) ∧
(FV_exp (App _ e1 e2) = FV_exp e1 ∪ FV_exp e2) ∧
(FV_exp (Log _ e1 e2) = FV_exp e1 ∪ FV_exp e2) ∧
(FV_exp (If e1 e2 e3) = FV_exp e1 ∪ FV_exp e2 ∪ FV_exp e3) ∧
(FV_exp (Mat e pes) = FV_exp e ∪ BIGUNION (IMAGE (λ(p,e). FV_exp e DIFF pat_vars p) (set pes))) ∧
(FV_exp (Let x e b) = FV_exp e ∪ (FV_exp b DIFF {x})) ∧
(FV_exp (Letrec defs b) = BIGUNION (IMAGE (λ(y,x,e). FV_exp e DIFF {x}) (set defs)) ∪ (FV_exp b DIFF (IMAGE FST (set defs)))) ∧
(FV_v (Lit _) = {}) ∧
(FV_v (Conv _ vs) = BIGUNION (IMAGE FV_v (set vs))) ∧
(FV_v (Closure env x e) = BIGUNION (IMAGE (λ(n,v). FV_v v) (set env)) ∪ FV_exp e DIFF {x} DIFF (IMAGE FST (set env))) ∧
(FV_v (Recclosure env defs y) = case ALOOKUP defs y of NONE => {}
| SOME (x,e) =>
  BIGUNION (IMAGE (λ(n,v). FV_v v) (set env)) ∪
  BIGUNION (IMAGE (λ(y,x,e). FV_exp e DIFF {x}) (set defs)) ∪
  FV_exp e DIFF {x} DIFF (IMAGE FST (set defs)) DIFF (IMAGE FST (set env)))` tac
val _ = export_rewrites["FV_def"]
*)

val clV_def = tDefine "clV"`
(clV_exp (Raise _) = {}) ∧
(clV_exp (Val v) = clV_v v) ∧
(clV_exp (Con _ ls) = BIGUNION (IMAGE clV_exp (set ls))) ∧
(clV_exp (Var _) = {}) ∧
(clV_exp (Fun _ e) = clV_exp e) ∧
(clV_exp (App _ e1 e2) = clV_exp e1 ∪ clV_exp e2) ∧
(clV_exp (Log _ e1 e2) = clV_exp e1 ∪ clV_exp e2) ∧
(clV_exp (If e1 e2 e3) = clV_exp e1 ∪ clV_exp e2 ∪ clV_exp e3) ∧
(clV_exp (Mat e pes) = clV_exp e ∪ BIGUNION (IMAGE (λ(p,e). clV_exp e) (set pes))) ∧
(clV_exp (Let _ e b) = clV_exp e ∪ clV_exp b) ∧
(clV_exp (Letrec defs b) = BIGUNION (IMAGE (λ(y,x,e). clV_exp e) (set defs)) ∪ clV_exp b) ∧
(clV_v (Lit _) = {}) ∧
(clV_v (Conv _ vs) = BIGUNION (IMAGE clV_v (set vs))) ∧
(clV_v (Closure env _ e) = IMAGE FST (set env) ∪
  BIGUNION (IMAGE (λ(n,v). clV_v v) (set env)) ∪
  clV_exp e) ∧
(clV_v (Recclosure env defs _) = IMAGE FST (set defs) ∪ IMAGE FST (set env) ∪
  BIGUNION (IMAGE (λ(n,v). clV_v v) (set env)) ∪
  BIGUNION (IMAGE (λ(y,x,e). clV_exp e) (set defs)))` tac
val _ = export_rewrites["clV_def"]

val good_envs_def = Define`
  good_envs env s s' Cenv = s.cmap SUBMAP s'.cmap`

val good_cmap_def = Define`
good_cmap cenv cm =
  (∀cn n. do_con_check cenv cn n ⇒ cn IN FDOM cm)`

val good_repl_state_def = Define`
  good_repl_state s =
    INJ (FAPPLY s.vmap) (FDOM s.vmap) UNIV ∧
    (∀n. n ∈ FRANGE s.vmap ⇒ n < s.nv)`

val good_env_state_def = Define`
  good_env_state env s =
  ALL_DISTINCT (MAP FST env) ∧
  good_repl_state s ∧
  IMAGE FST (set env) ∪
  BIGUNION (IMAGE (clV_v o SND) (set env))
  ⊆ FDOM s.vmap`

(* Soundness(?) of exp_Cexp *)

(*
val exp_Cexp_thm = store_thm(
"exp_Cexp_thm",``
∀G cm env Cenv exp Cexp. exp_Cexp G cm env Cenv exp Cexp ⇒
  good_G G ⇒
  ∀cenv res.
    evaluate cenv env exp res ⇒
    ∀cw. good_cmaps cenv cm cw ⇒
      ∃Cres.
        Cevaluate Cenv Cexp Cres ∧
        (map_result (Cv_to_ov cw) Cres =
         map_result v_to_ov res)``,
ho_match_mp_tac exp_Cexp_ind >>
rw[] >- (
  fs[good_G_def,good_cmaps_def] >>
  PROVE_TAC[] )
>- (
  fs[EVERY2_EVERY,EVERY_MEM] >>
  qpat_assum `LENGTH es = LENGTH ces` assume_tac >>
  fsrw_tac[boolSimps.DNF_ss][MEM_ZIP] >>
  first_x_assum (assume_tac o (CONV_RULE (RESORT_FORALL_CONV (fn [n,cenv,res,cw] => [cenv,cw,n,res] | _ => raise mk_HOL_ERR"""""")))) >>
  pop_assum (qspecl_then [`cenv`,`cw`] mp_tac) >> rw[] >>
  fs[GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] >>
  fs[evaluate_con,Cevaluate_con] >>
  Cases_on `do_con_check cenv cn (LENGTH Ces)` >> fs[] >> rw[] >- (
    fs[evaluate_list_with_evaluate,evaluate_list_with_error,Cevaluate_list_with_Cevaluate,Cevaluate_list_with_error] >>
    qexists_tac `f n (Rerr err)` >> rw[] >>
    first_assum (qspecl_then [`n`,`Rerr err`] mp_tac) >>
    Cases_on `f n (Rerr err)` >> rw[Cevaluate_list_with_error] >>
    qexists_tac `n` >> rw[] >>
    res_tac >>
    first_x_assum (qspecl_then [`m`,`Rval v`] mp_tac) >>
    `m < LENGTH Ces` by srw_tac[ARITH_ss][] >>
    rw[] >>
    Cases_on `f m (Rval v)` >> fs[] >>
    metis_tac[] )
  >- (
    fs[evaluate_list_with_evaluate,Cevaluate_list_with_Cevaluate] >>
    fs[evaluate_list_with_value,Cevaluate_list_with_value] >>
    qexists_tac `Rval (CConv (cm ' cn) (GENLIST (λn. @v. (f n (Rval (EL n vs))) = Rval v) (LENGTH vs)))` >>
    rw[] >- (
      first_x_assum (qspec_then `n` mp_tac) >>
      first_x_assum (qspec_then `n` mp_tac) >>
      rw[] >>
      first_x_assum (qspec_then `Rval (EL n vs)` mp_tac) >>
      Cases_on `f n (Rval (EL n vs))` >> rw[] )
    >- (
      fs[good_cmaps_def,good_cm_cw_def] ) >>
    rw[MAP_EQ_EVERY2,EVERY2_EVERY,EVERY_MEM,MEM_ZIP,pairTheory.FORALL_PROD] >>
    rw[EL_GENLIST] >>
    first_x_assum (qspec_then `n` mp_tac) >>
    first_x_assum (qspec_then `n` mp_tac) >>
    rw[] >>
    first_x_assum (qspec_then `Rval (EL n vs)` mp_tac) >>
    Cases_on `f n (Rval (EL n vs))` >> rw[] ) >>
  qexists_tac `Rerr Rtype_error` >> rw[] >>
  need Cevaluate to do a con check?
  ) >>
fs[evaluate_var] >> fs[] >> rw[] >>
fs[good_G_def,good_cmaps_def] >>
first_x_assum (match_mp_tac o GSYM) >>
metis_tac[])
*)

val FOLDR_CONS_triple = store_thm(
"FOLDR_CONS_triple",
``!f ls a. FOLDR (\(x,y,z) w. f x y z :: w) a ls = (MAP (\(x,y,z). f x y z) ls)++a``,
GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
Q.X_GEN_TAC `p` THEN
PairCases_on `p` THEN
SRW_TAC[][])

val extend_good_repl_state = store_thm(
"extend_good_repl_state",
``∀s vn s' n. good_repl_state s ∧ (extend s vn = (s',n)) ⇒ good_repl_state s'``,
rw[extend_def] >>
fs[good_repl_state_def,FRANGE_DEF,INJ_DEF] >>
fs[FAPPLY_FUPDATE_THM,FRANGE_DEF,DOMSUB_FAPPLY_THM] >>
fsrw_tac[boolSimps.DNF_ss][] >>
reverse conj_tac >- (
  rw[] >> res_tac >> DECIDE_TAC ) >>
conj_asm1_tac >- (
  rw[] >>
  spose_not_then strip_assume_tac >>
  res_tac >> DECIDE_TAC ) >>
fs[] >> rw[])

val extend_FDOM_SUBSET = store_thm(
"extend_FDOM_SUBSET",
``∀s vn s' n. (extend s vn = (s',n)) ⇒ FDOM s.vmap ⊆ FDOM s'.vmap``,
rw[extend_def,SUBSET_DEF] >> rw[])

val pat_to_Cpat_good_repl_state = store_thm(
"pat_to_Cpat_good_repl_state",
``∀s pvs p s' pvs' Cp. good_repl_state s ∧ (pat_to_Cpat (s,pvs,p) = (s',pvs',Cp)) ⇒ good_repl_state s'``,
qsuff_tac `∀s pvs p s' pvs' Cp. good_repl_state (FST (s,pvs,p)) ∧ (pat_to_Cpat (s,pvs,p) = (s',pvs',Cp)) ⇒ good_repl_state s'` >- rw[] >>
ho_match_mp_tac pat_to_Cpat_ind >>
rw[pat_to_Cpat_def,LET_THM] >- (
  Cases_on `extend s vn` >> fs[] >> rw[] >>
  fsrw_tac[SATISFY_ss][extend_good_repl_state] ) >>
rw[] >>
qmatch_assum_abbrev_tac `P Q = (s',pvs',Cp)` >>
PairCases_on `Q` >> fs[Abbr`P`] >> rw[] >>
fs[markerTheory.Abbrev_def] >>
pop_assum (mp_tac o SYM) >>
rpt (pop_assum mp_tac) >>
map_every qid_spec_tac [`Q2`,`Q1`,`Q0`,`pvs`,`s`,`ps`] >>
Induct >- (rw[] >> rw[]) >>
rpt strip_tac >>
qmatch_abbrev_tac `G` >>
fs[] >>
qmatch_assum_abbrev_tac `P R = (Q0,Q1,Q2)` >>
PairCases_on `R` >>
pop_assum mp_tac >> simp_tac(std_ss)[markerTheory.Abbrev_def] >>
disch_then (assume_tac o SYM) >> fs[Abbr`P`] >> rw[] >>
qabbrev_tac `P = pat_to_Cpat (R0,R1,h)` >>
PairCases_on `P` >>
pop_assum mp_tac >> rw[markerTheory.Abbrev_def] >>
pop_assum (assume_tac o SYM) >> fs[] >> rw[] >>
`good_repl_state R0` by (
  first_x_assum (qspecl_then [`s`,`pvs`] (match_mp_tac o MP_CANON)) >>
  fsrw_tac[SATISFY_ss][] ) >>
first_x_assum (qspecl_then [`h`,`R0`,`R1`] mp_tac) >>
metis_tac[])

val tac =
  unabbrev_all_tac >>
  rw[force_dom_DRESTRICT_FUNION,FUNION_DEF,DRESTRICT_DEF,MEM_MAP,pairTheory.EXISTS_PROD,FUN_FMAP_DEF,MAP_MAP_o] >>
  qmatch_abbrev_tac `canonical_env_Cv ((alist_to_fmap (MAP f env)) ' k)` >>
  `∃f1 f2. f = (λ(n,v). (f1 n, f2 v))` by (
    rw[FUN_EQ_THM,pairTheory.UNCURRY,Abbr`f`,pairTheory.FORALL_PROD] >>
    rw[GSYM SKOLEM_THM,Once SWAP_EXISTS_THM] >>
    rw[FORALL_AND_THM] >>
    rw[GSYM SKOLEM_THM] ) >>
  `INJ f1 (set (MAP FST env)) UNIV` by (
    unabbrev_all_tac >>
    fs[INJ_DEF] >>
    fs[FUN_EQ_THM,pairTheory.FORALL_PROD,FORALL_AND_THM] >>
    rpt strip_tac >> fs[] >>
    first_x_assum (match_mp_tac o MP_CANON) >> fs[] >>
    fs[SUBSET_DEF,pairTheory.EXISTS_PROD,MEM_MAP] >>
    metis_tac[] ) >>
  fs[] >>
  rw[alist_to_fmap_MAP] >>
  qmatch_abbrev_tac `canonical_env_Cv (MAP_KEYS f1 fm ' k)` >>
  `∃a. (a ∈ FDOM fm) ∧ (k = f1 a)` by (
    fs[FUN_EQ_THM,markerTheory.Abbrev_def,pairTheory.FORALL_PROD,MEM_MAP,pairTheory.EXISTS_PROD] >>
    metis_tac[] ) >>
  rw[] >>
  `INJ f1 (FDOM fm) UNIV` by (
    fs[FUN_EQ_THM,markerTheory.Abbrev_def,pairTheory.FORALL_PROD] ) >>
  rw[MAP_KEYS_def,Abbr`fm`] >>
  fs[o_f_DEF,markerTheory.Abbrev_def,FUN_EQ_THM,pairTheory.FORALL_PROD]

(*
val exp_to_Cexp_canonical = store_thm(
"exp_to_Cexp_canonical",``
(∀s e. good_repl_state s ∧
  (clV_exp e ⊆ FDOM s.vmap)
 ⇒ canonical_env_Cexp (exp_to_Cexp s e)) ∧
(∀s defs mk_Cb. good_repl_state s ∧
  (IMAGE FST (set defs) ∪ BIGUNION (IMAGE (λ(y,x,e). clV_exp e) (set defs)) ⊆ FDOM s.vmap)
 ⇒ canonical_env_Cexp (SND (Letrec_to_CLetfun s defs mk_Cb))) ∧
(∀s e mk_Cpes. good_repl_state s ∧
  (clV_exp e ⊆ FDOM s.vmap)
 ⇒ canonical_env_Cexp (SND (Mat_to_CMat s e mk_Cpes))) ∧
(∀s v. good_repl_state s ∧
  (clV_v v ⊆ FDOM s.vmap)
 ⇒ canonical_env_Cv (v_to_Cv s v))``,
ho_match_mp_tac exp_to_Cexp_ind >> rw[exp_to_Cexp_def] >>
fsrw_tac[boolSimps.DNF_ss][BIGUNION_SUBSET,exp_to_Cexp_def,EVERY_MEM,MEM_MAP,pairTheory.FORALL_PROD] >>
TRY (
  first_x_assum match_mp_tac >>
  conj_asm1_tac >- (
    fsrw_tac[SATISFY_ss][extend_good_repl_state] ) >>
  imp_res_tac extend_FDOM_SUBSET >>
  fs[SUBSET_DEF] >>
  NO_TAC)
>- (
  BasicProvers.EVERY_CASE_TAC >>
  fs[LET_THM,pairTheory.UNCURRY] )
>- (
  `EVERY canonical_env_Cexp (MAP SND Cpes)` by (
    fs[LET_THM] >> rw[EVERY_MAP] >>
    Induct_on `pes` >- (rw[] >> rw[]) >>
    Cases >> rw[] >>
    first_x_assum (match_mp_tac o MP_CANON) >>
    rw[]

  Cases_on `dest_var e` >> fs[] >> rw[] >> rw[]
  BasicProvers.EVERY_CASE_TAC >> fs[LET_THM] >> rw[]

rw[mk_env_def,EVERY_MAP,EVERY_MEM,pairTheory.FORALL_PROD,FLOOKUP_DEF] >- tac  >>
imp_res_tac find_index_LESS_LENGTH >>
rw[] >>
fs[MEM_MAP,EVERY_MAP,EL_MAP,DIFF_UNION,DIFF_COMM] >>
fs[FOLDR_CONS_triple,LET_THM,pairTheory.UNCURRY,MAP_MAP_o] >>
qunabbrev_tac `defs'` >> fs[EVERY_MAP,pairTheory.UNCURRY] >>
rw[EVERY_MEM,pairTheory.FORALL_PROD,FLOOKUP_DEF] >>
tac)
*)

val force_dom_FUNION_id = store_thm(
"force_dom_FUNION_id",
``∀fm s d. FINITE s ⇒ ((force_dom fm s d ⊌ fm = fm) = (s ⊆ FDOM fm))``,
rw[force_dom_DRESTRICT_FUNION,GSYM SUBMAP_FUNION_ABSORPTION] >>
rw[SUBMAP_DEF,DRESTRICT_DEF,FUN_FMAP_DEF,EQ_IMP_THM,SUBSET_DEF,FUNION_DEF] >>
fs[])

(*
val Cevaluate_FUPDATE = store_thm(
"Cevaluate_FUPDATE",
``∀env exp res k v. Cevaluate env exp res ∧ k ∉ free_vars exp ⇒ Cevaluate (env |+ (k,v)) exp res``,
rw[] >>
qsuff_tac `env |+ (k,v) = (force_dom env (free_vars exp) (CLit (Bool F))) ⊌ (env |+ (k,v))` >- metis_tac[Cevaluate_any_env] >>
rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
rw[force_dom_DRESTRICT_FUNION,SUBMAP_DEF]
*)

val force_dom_idempot = store_thm(
"force_dom_idempot",
``FINITE s ==> (force_dom (force_dom fm s d) s d = force_dom fm s d)``,
rw[force_dom_id])
val _ = export_rewrites["force_dom_idempot"]

val Cevaluate_super_env = store_thm(
"Cevaluate_super_env",
``∀s env exp res. FINITE s ∧ Cevaluate (force_dom env (free_vars exp) (CLit (Bool F))) exp res ∧ free_vars exp ⊆ s ⇒ Cevaluate (force_dom env s (CLit (Bool F))) exp res``,
rw[] >>
imp_res_tac Cevaluate_any_env >>
qpat_assum `FINITE s` assume_tac >>
fs[] >>
qmatch_abbrev_tac `Cevaluate env1 exp res` >>
qmatch_assum_abbrev_tac `∀env'. Cevaluate (env0 ⊌ env') exp res` >>
qsuff_tac `env1 = env0 ⊌ env1` >- metis_tac[] >>
rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
fsrw_tac[][Abbr`env0`,Abbr`env1`,SUBMAP_DEF,SUBSET_DEF,force_dom_DRESTRICT_FUNION] >> rw[] >>
srw_tac[][FUN_FMAP_DEF,DRESTRICT_DEF,FUNION_DEF])

(* Prove compiler phases preserve semantics *)

val tac1 =
   match_mp_tac Cevaluate_super_env >>
   fsrw_tac[boolSimps.DNF_ss][] >>
   (reverse conj_tac >- (
      match_mp_tac SUBSET_BIGUNION_I >>
      srw_tac[boolSimps.DNF_ss][MEM_MAP,MEM_EL] >>
      metis_tac[] )) >>
   (qmatch_assum_abbrev_tac `evaluate cenv env (EL kk es) res0`
    ORELSE
    (qabbrev_tac `kk = n` >> qabbrev_tac `res0 = Rval (EL kk vs)`)) >>
   first_x_assum (qspec_then `kk` mp_tac) >> rw[] >>
   first_x_assum (qspec_then `res0` mp_tac o (
     CONV_RULE (RESORT_FORALL_CONV
       ((Lib.uncurry (Lib.C Lib.cons)) o Lib.front_last)))) >>
   rw[Abbr`res0`] >>
   pop_assum (match_mp_tac o MP_CANON) >>
   Cases_on `exp_to_Cexp F cm (s,EL kk es)` >>
   fs[MEM_EL] >> metis_tac[]

val ALOOKUP_NONE = store_thm(
"ALOOKUP_NONE",
``!l x. (ALOOKUP l x = NONE) = ~MEM x (MAP FST l)``,
SRW_TAC[][ALOOKUP_FAILS,MEM_MAP,pairTheory.FORALL_PROD])

val force_dom_FUPDATE = store_thm(
"force_dom_FUPDATE",
``∀fm s d k v. FINITE s ⇒ ((force_dom fm s d) |+ (k,v) = force_dom (fm |+ (k,v)) (k INSERT s) d)``,
rw[force_dom_DRESTRICT_FUNION,GSYM fmap_EQ_THM,DRESTRICT_DEF,FUNION_DEF,FUN_FMAP_DEF,FAPPLY_FUPDATE_THM] >>
rw[FUN_FMAP_DEF] >> fs[])

val force_dom_of_FUPDATE = store_thm(
"force_dom_of_FUPDATE",
``∀fm s d k v. FINITE s ∧ k ∉ s ⇒ (force_dom (fm |+ (k,v)) s d = force_dom fm s d)``,
rw[force_dom_DRESTRICT_FUNION])

(*
val exp_to_Cexp_nontp_same_next = store_thm(
"exp_to_Cexp_nontp_same_next",
``∀tp cm Ps Pexp s exp s' Cexp. ((Ps,Pexp) = (s,exp)) ∧
(exp_to_Cexp tp cm (s,exp) = (s',Cexp))
∧ (tp = F) ⇒ (s'.n = s.n)``,
ho_match_mp_tac exp_to_Cexp_ind >>
rw[] >>
fs[exp_to_Cexp_def,LET_THM,pairTheory.UNCURRY] >>

val exp_to_Cexp_vars_below_next = store_thm(
"exp_to_Cexp_vars_below_next",
``∀tp cm Ps Pexp s exp s' Cexp. ((Ps,Pexp) = (s,exp)) ∧
  (exp_to_Cexp tp cm (s,exp) = (s',Cexp))
⇒ ∀v. v ∈ free_vars Cexp ⇒ v < s'.n
exp_to_Cexp_ind
*)

(*
val exp_to_Cexp_thm1 = store_thm(
"exp_to_Cexp_thm1",
``∀cenv env exp res. evaluate cenv env exp res ⇒
  ∀s Cexp. good_env_state env s ∧ (res ≠ Rerr Rtype_error) ∧ (Cexp = exp_to_Cexp s exp) ⇒
 Cevaluate
   (force_dom (alist_to_fmap (MAP (λ(x,v). (s.vmap ' x, v_to_Cv s v)) env)) (free_vars Cexp) (CLit (Bool F)))
   Cexp
   (map_result (v_to_Cv s) res)``,
ho_match_mp_tac evaluate_nice_ind >>
strip_tac >- rw[exp_to_Cexp_def] >>
strip_tac >- (
  rw[exp_to_Cexp_def,exp_to_Cexp_canonical] >>
*)

(*
val exp_to_Cexp_thm1 = store_thm(
"exp_to_Cexp_thm1",
``∀tp cm s exp s' Cexp cenv env res.
  good_env_state env s ∧
  (exp_to_Cexp s exp = Cexp) ∧
  evaluate cenv env exp res ∧
  (res ≠ Rerr Rtype_error) ∧
  good_cmap cenv cm ⇒
  Cevaluate (force_dom (alist_to_fmap (MAP (λ(x,v). (s.m ' x, v_to_Cv cm (s,v))) env)) (free_vars Cexp) (CLit (Bool F))) Cexp (map_result (λv. v_to_Cv cm (s,v)) res)``,
ho_match_mp_tac exp_to_Cexp_ind >>
strip_tac >-
  fs[exp_to_Cexp_def] >>
strip_tac >-
  fs[exp_to_Cexp_def,v_to_Cv_def] >>
strip_tac >- (
  fs[exp_to_Cexp_def] >>
  rw[Cevaluate_con,evaluate_con] >>
  fs[Cevaluate_list_with_Cevaluate,evaluate_list_with_evaluate] >>
  fs[Cevaluate_list_with_error,evaluate_list_with_error,
     Cevaluate_list_with_value,evaluate_list_with_value] >- (
     qexists_tac `n` >> fs[] >> rw[] >>
     fsrw_tac[ARITH_ss][EL_MAP,MEM_EL,FOLDL_UNION_BIGUNION] >>
     fsrw_tac[boolSimps.DNF_ss][LET_THM,pairTheory.UNCURRY] >>
     TRY (
       first_x_assum (qspec_then `m` mp_tac) >> rw [] >>
       `m < LENGTH es` by srw_tac[ARITH_ss][] >>
       qexists_tac `v_to_Cv cm (s,v)` ) >>
     tac1) >>
   fs[EL_MAP,FOLDL_UNION_BIGUNION,LET_THM,pairTheory.UNCURRY] >>
   rw[v_to_Cv_def,EL_MAP] >>
   tac1) >>
strip_tac >- (
  fs[exp_to_Cexp_def,evaluate_var,MEM_MAP] >>
  rw[] >> srw_tac[boolSimps.DNF_ss][pairTheory.EXISTS_PROD] >>
  imp_res_tac alistTheory.ALOOKUP_MEM >>
  reverse (
    rw[force_dom_DRESTRICT_FUNION,DRESTRICT_DEF,FUNION_DEF,MEM_MAP,pairTheory.EXISTS_PROD] ) >-
    metis_tac[] >>
  fs[good_env_state_def] >>
  qho_match_abbrev_tac `x = ce_Cv (alist_to_fmap (MAP (λ(x,y). (f1 x, f2 y)) al) ' z)` >>
  `f1 = FAPPLY s.m` by rw[Abbr`f1`,FUN_EQ_THM] >>
  `INJ f1 (set (MAP FST al)) UNIV` by (
    metis_tac[INJ_SUBSET,SUBSET_UNIV,LIST_TO_SET_MAP] ) >>
  rw[alistTheory.alist_to_fmap_MAP] >>
  `vn IN FDOM (f2 o_f alist_to_fmap al)` by (
    rw[MEM_MAP] >>
    qexists_tac `(vn,v)` >> rw[] ) >>
  rw[finite_mapTheory.MAP_KEYS_def] >>
  unabbrev_all_tac >>
  rw[finite_mapTheory.o_f_DEF] >>
  imp_res_tac alistTheory.ALOOKUP_SOME_FAPPLY_alist_to_fmap >>
  rw[] >>
  match_mp_tac EQ_SYM >>
  match_mp_tac (CONJUNCT2 ce_Cexp_canonical_id) >>
  match_mp_tac v_to_Cv_canonical >>
  fsrw_tac[boolSimps.ETA_ss][] >>
  fsrw_tac[boolSimps.DNF_ss][SUBSET_DEF,pairTheory.EXISTS_PROD] >>
  metis_tac[] ) >>
strip_tac >- (
  fs[exp_to_Cexp_def] >>
  rw[v_to_Cv_def] >>
  fs[LET_THM] >>
  rw[Once Cevaluate_cases] >>
  rw[mk_env_canon,Abbr`env'`,Abbr`env''`,ALOOKUP_APPEND,ALOOKUP_MAP,FLOOKUP_DEF] >>
  unabbrev_all_tac >> fs[] >>
  rw[force_dom_DRESTRICT_FUNION,FUNION_DEF,DRESTRICT_DEF,FUN_FMAP_DEF] >>
  fs[GSYM ALOOKUP_NONE] >>
  BasicProvers.EVERY_CASE_TAC >> fs[ALOOKUP_NONE] >>
  imp_res_tac ALOOKUP_SOME_FAPPLY_alist_to_fmap >>
  rw[]) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  Cases_on `exp_to_Cexp F cm (s,e1)` >> fs[] >>
  Cases_on `exp_to_Cexp F cm (s,e2)` >> fs[] >>
  fs[LET_THM] >> rw[] >>
  rw[Once Cevaluate_cases] >>
  fs[evaluate_app] >- (
    disj1_tac >>
    rw[Cevaluate_list_with_Cevaluate] >>
    rw[Cevaluate_list_with_cons] >>
    qexists_tac `v_to_Cv cm (s,v1)` >>
    qexists_tac `v_to_Cv cm (s,v2)` >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rval v1`] mp_tac) >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rval v2`] mp_tac) >>
    rw[Cevaluate_super_env] >>
    Cases_on `opn` >>
    Cases_on `v1` >> Cases_on `l` >> fs[do_app_def] >>
    Cases_on `v2` >> Cases_on `l` >> fs[] >> rw[] >>
    fs[CevalPrim2_def,doPrim2_def,v_to_Cv_def,opn_lookup_def,i0_def] >>
    rw[] >> fs[] >> rw[] >>
    qpat_assum `evaluate cenv env (Val X) Y` mp_tac >>
    rw[Once evaluate_cases,v_to_Cv_def] )
  >- (
    disj2_tac >>
    rw[Cevaluate_list_with_Cevaluate] >>
    rw[Cevaluate_list_with_cons] >>
    disj1_tac >>
    qexists_tac `v_to_Cv cm (s,v1)` >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rval v1`] mp_tac) >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rerr err`] mp_tac) >>
    rw[Cevaluate_super_env] )
  >- (
    disj2_tac >>
    rw[Cevaluate_list_with_Cevaluate] >>
    rw[Cevaluate_list_with_cons] >>
    disj2_tac >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rerr err`] mp_tac) >>
    rw[Cevaluate_super_env] )) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  Cases_on `exp_to_Cexp F cm (s,e1)` >> fs[] >>
  Cases_on `exp_to_Cexp F cm (s,e2)` >> fs[] >>
  fs[LET_THM] >> rw[] >>
  qpat_assum `evaluate cenv env (App (Opb X) e1 e2) res` mp_tac >>
  rw[evaluate_app] >-
    let
      val ltac =
        disj1_tac >>
        rw[Cevaluate_list_with_Cevaluate] >>
        rw[Cevaluate_list_with_cons] >>
        qexists_tac `v_to_Cv cm (s,v1)` >>
        qexists_tac `v_to_Cv cm (s,v2)` >>
        rw[] >>
        Cases_on `v1` >> Cases_on `l` >> fs[do_app_def] >>
        Cases_on `v2` >> Cases_on `l` >> fs[] >> rw[] >>
        rw[CevalPrim2_def,doPrim2_def,v_to_Cv_def] >>
        qpat_assum `evaluate cenv env (Val X) Y` mp_tac >>
        rw[Once evaluate_cases,v_to_Cv_def,opb_lookup_def] >>
        fs[Cevaluate_super_env,v_to_Cv_def]
      val gtac =
        disj1_tac >>
        qexists_tac `v_to_Cv cm (s,v1)` >>
        rw[Once Cevaluate_cases] >- (
          match_mp_tac Cevaluate_super_env >>
          fs[] >>
          metis_tac[UNION_COMM,UNION_ASSOC,SUBSET_UNION] ) >>
        disj1_tac >>
        qexists_tac `v_to_Cv cm (s,v2)` >>
        rw[Once Cevaluate_cases] >- (
          qmatch_abbrev_tac `Cevaluate ((force_dom env0 s0 d0) |+ (k,v)) ex re` >>
          fs[Abbr`s0`,GSYM INSERT_SING_UNION] >>
          rw[force_dom_FUPDATE,Abbr`d0`] >>
          match_mp_tac Cevaluate_super_env >>
          fs[SUBSET_INSERT_RIGHT] >>
          qsuff_tac `k ∉ free_vars ex` >- rw[force_dom_of_FUPDATE] >>
        (* only variables below s.n will appear in the output of exp_to_Cexp *)

    in
      first_x_assum (qspecl_then [`cenv`,`env`,`Rval v1`] mp_tac) >>
      first_x_assum (qspecl_then [`cenv`,`env`,`Rval v2`] mp_tac) >>
      rw[] >>
      Cases_on `opb` >> rw[Once Cevaluate_cases] >>
      >- ltac >- gtac >- ltac >- gtac
    end
  >- let
      fun tac t = t >>
        first_x_assum (qspecl_then [`cenv`,`env`,`Rval v1`] mp_tac) >>
        first_x_assum (qspecl_then [`cenv`,`env`,`Rerr err`] mp_tac) >>
        rw[]
      val ltac = tac (
        disj1_tac >>
        qexists_tac `v_to_Cv cm (s,v1)` )
      val gtac = tac ( disj2_tac )
    in
      Cases_on `opb` >> rw[Once Cevaluate_cases] >>
      disj2_tac >>
      rw[Cevaluate_list_with_Cevaluate] >>
      rw[Cevaluate_list_with_cons]
      >- ltac >- gtac >- ltac >- gtac
    end
  >- let
      fun tac t = t >>
        first_x_assum (qspecl_then [`cenv`,`env`,`Rval err`] mp_tac) >>
        rw[]
      val gtac = tac (
        disj1_tac >>
        qexists_tac `v_to_Cv cm (s,v1)` )
      val ltac = tac ( disj2_tac )
    in
      Cases_on `opb` >> rw[Once Cevaluate_cases] >>
      disj2_tac >>
      rw[Cevaluate_list_with_Cevaluate] >>
      rw[Cevaluate_list_with_cons]
      >- ltac >- gtac >- ltac >- gtac
    end
*)

(*
val exp_to_Cexp_thm1 = store_thm(
"exp_to_Cexp_thm1",
``∀cenv env exp res.
   evaluate cenv env exp res ⇒
   is_source_exp exp ∧ (res ≠ Rerr Rtype_error) ⇒
   ∀cm s. ∃s' Cexp. (exp_to_Cexp F cm (s,exp) = (s',Cexp)) ∧
     ∀cw Cenv. (good_cmaps cenv cm cw) ∧
               (good_envs env s s' Cenv) ⇒
       ∃Cres. Cevaluate Cenv Cexp Cres ∧
              (map_result (Cv_to_ov cw) Cres =
               map_result v_to_ov res)``,
ho_match_mp_tac evaluate_nice_ind >>
strip_tac >- (
  rw[exp_to_Cexp_def,
     Once Cevaluate_cases]) >>
strip_tac >- (
  ntac 2 gen_tac >>
  Cases >> rw[is_source_exp_def] >>
  rw[exp_to_Cexp_def] >>
  rw[Once Cevaluate_cases]) >>
strip_tac >- (
  rw[exp_to_Cexp_def,good_cmaps_def] >>
  res_tac >>
  qpat_assum `do_con_check X Y Z` kall_tac >>
  fs[is_source_exp_def] >>
  Induct_on `es` >- (
    rw[Once evaluate_list_with_cases] >>
    rw[Once Cevaluate_cases] >>
    rw[Once Cevaluate_cases] >>
    qexists_tac `Rval (CConv (cm ' cn) [])` >>
    rw[] ) >>
  rw[Once evaluate_list_with_cases] >>
  fs[is_source_exp_def] >>
  first_x_assum (qspecl_then [`cm`,`s`] mp_tac) >>
  rw[] >> rw[] >>
  rw[Once Cevaluate_cases]
  ... ) >>
strip_tac >- (
  rw[exp_to_Cexp_def] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  rw[Once Cevaluate_cases] >>
  qexists_tac `Rerr err` >>
  rw[] >>
  fs[is_source_exp_def] >>
  qpat_assum `do_con_check X Y Z` kall_tac >>
  Induct_on `es` >>
  rw[Once evaluate_list_with_cases] >>
  fs[] >>
  first_x_assum (qspecl_then [`cm`,`s`] mp_tac) >>
  rw[] >>
  rw[Once Cevaluate_cases] >>
  first_x_assum (qspecl_then [`cw`,`Cenv`] mp_tac) >>
  rw[good_envs_def] >>
  Cases_on `Cres` >> fs[] >>
  PROVE_TAC[] ) >>
strip_tac >- (
  rw[]
*)

(*
let rec
v_to_ov cenv (Lit l) = OLit l
and
v_to_ov cenv (Conv cn vs) = OConv cn (List.map (v_to_ov cenv) vs)
and
v_to_ov cenv (Closure env vn e) = OFn
  (fun ov -> map_option (o (v_to_ov cenv) snd)
    (some (fun (a,r) -> v_to_ov cenv a = ov
           && evaluate cenv (bind vn a env) e (Rval r))))
and
v_to_ov cenv (Recclosure env defs n) = OFn
  (fun ov -> option_bind (optopt (find_recfun n defs))
    (fun (vn,e) -> map_option (o (v_to_ov cenv) snd)
      (some (fun (a,r) -> v_to_ov cenv a = ov
             && evaluate cenv (bind vn a (build_rec_env defs env)) e (Rval r)))))

let rec
Cv_to_ov m (CLit l) = OLit l
and
Cv_to_ov m (CConv cn vs) = OConv (Pmap.find cn m) (List.map (Cv_to_ov m) vs)
and
Cv_to_ov m (CClosure env ns e) = OFn
  (fun ov -> some
and
Cv_to_ov m (CRecClos env ns fns n) = OFn
*)


val _ = export_theory ()
