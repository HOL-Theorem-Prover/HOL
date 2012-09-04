open HolKernel bossLib boolLib boolSimps SatisfySimps listTheory pairTheory pred_setTheory finite_mapTheory alistTheory relationTheory intLib lcsymtacs
open miscTheory miniMLExtraTheory compileTerminationTheory intLangTheory bytecodeTerminationTheory evaluateEquationsTheory quantHeuristicsLib
val _ = intLib.deprecate_int()
val _ = new_theory "compileCorrectness"

(* label_closures correctness stuff - move to another theory *)

val label_closures_no_bodies = store_thm("label_closures_no_bodies",
  ``(∀s Ce c. (∀b. b ∈ FRANGE c ⇒ (free_bods c b = {})) ⇒
            (free_bods c (SND (label_closures s Ce)) = {})) ∧
    (∀s Ces c. (∀b. b ∈ FRANGE c ⇒ (free_bods c b = {})) ⇒
            (BIGUNION (IMAGE (free_bods c) (set (SND (label_closures_list s Ces)))) = {})) ∧
    (∀s ns ls ds defs. EVERY (ISR o SND) ds ⇒ EVERY (ISR o SND) (SND (labelise s ns ls ds defs)))``,
  ho_match_mp_tac label_closures_ind >> rw[] >>
  TRY (rw[label_closures_def] >>
       fsrw_tac[ETA_ss][FILTER_EQ_NIL,EVERY_MAP,combinTheory.o_DEF,
                        FOLDL_UNION_BIGUNION,FOLDL_UNION_BIGUNION_paired] >>
       rw[FOLDL_UNION_BIGUNION_paired] >>
       rw[IMAGE_EQ_SING,FORALL_PROD] >>
       fs[EVERY_MEM,FORALL_PROD] >>
       fsrw_tac[QUANT_INST_ss[std_qp]][] >>
       rw[FLOOKUP_DEF] >>
       Cases_on `defs' = []` >> fs[] >> rw[] >>
       fsrw_tac[DNF_ss][FRANGE_DEF] >>
       PROVE_TAC[free_bods_DOMSUB_SUBSET,SUBSET_EMPTY])
  >- (
    rw[Once label_closures_def] >>
    Cases_on `cb` >> fs[label_closures_def] >> rw[] >> fs[] >> rw[] >>
    Cases_on `label_closures s x` >> fs[LET_THM] >>
    rw[] >> fs[] >> rw[] >>
    rw[FLOOKUP_DEF] >>
    fsrw_tac[DNF_ss][FRANGE_DEF] >>
    PROVE_TAC[free_bods_DOMSUB_SUBSET,SUBSET_EMPTY])
  >- (
    rw[label_closures_def] >>
    rw[rich_listTheory.EVERY_REVERSE] >>
    Cases_on `label_closures s Ce` >> fs[LET_THM] >>
    rw[] >> fs[] >>
    first_x_assum (qspec_then `c` mp_tac) >> rw[] >>
    first_x_assum (qspec_then `c` mp_tac) >> rw[] >>
    rw[]))

val subst_lab_def = Define`
  (subst_lab c (INR l) = INL (FAPPLY c l)) ∧
  (subst_lab c (INL b) = INL b)`;
val _ = export_rewrites["subst_lab_def"];

val subst_labs_def = tDefine "subst_labs"`
  (subst_labs c (CDecl xs) = CDecl xs) ∧
  (subst_labs c (CRaise er) = CRaise er) ∧
  (subst_labs c (CVar x) = CVar x) ∧
  (subst_labs c (CLit l) = CLit l) ∧
  (subst_labs c (CCon n es) = CCon n (MAP (subst_labs c) es)) ∧
  (subst_labs c (CTagEq e n) = CTagEq (subst_labs c e) n) ∧
  (subst_labs c (CProj e n) = CProj (subst_labs c e) n) ∧
  (subst_labs c (CLet xs es e) = CLet xs (MAP (subst_labs c) es) (subst_labs c e)) ∧
  (subst_labs c (CLetfun b xs defs e) = CLetfun b xs (MAP (λ(xs,cb). (xs,subst_lab c cb)) defs) (subst_labs c e)) ∧
  (subst_labs c (CFun xs cb) = CFun xs (subst_lab c cb)) ∧
  (subst_labs c (CCall e es) = CCall (subst_labs c e) (MAP (subst_labs c) es)) ∧
  (subst_labs c (CPrim2 op e1 e2) = CPrim2 op (subst_labs c e1) (subst_labs c e2)) ∧
  (subst_labs c (CIf e1 e2 e3) = CIf (subst_labs c e1) (subst_labs c e2) (subst_labs c e3))`(
  WF_REL_TAC `measure (Cexp_size o SND)` >>
  srw_tac[ARITH_ss][Cexp4_size_thm] >>
  Q.ISPEC_THEN `Cexp_size` imp_res_tac SUM_MAP_MEM_bound >>
  fsrw_tac[ARITH_ss][])
val _ = export_rewrites["subst_labs_def"];

val Cclosed_SUBMAP = store_thm("Cclosed_SUBMAP",
  ``∀v. Cclosed c v ⇒ ∀c'. c ⊑ c' ⇒ Cclosed c' v``,
  ho_match_mp_tac Cclosed_ind >>
  rw[] >> rw[Once Cclosed_cases] >- (
    match_mp_tac EVERY_MEM_MONO >>
    qmatch_assum_abbrev_tac `EVERY P vs` >>
    qexists_tac `P` >>
    rw[Abbr`P`] )
  >- (
    imp_res_tac free_vars_SUBMAP >>

val Cevaluate_subst_labs = store_thm("Cevaluate_subst_labs",
  ``∀c env exp res. Cevaluate c env exp res ⇒
      (∀v. v ∈ FRANGE env ⇒ Cclosed c v) ∧
      free_vars c exp ⊆ FDOM env ∧
      free_labs c exp ⊆ FDOM c ⇒
      Cevaluate FEMPTY env (subst_labs c exp) res``,
  ho_match_mp_tac Cevaluate_nice_strongind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    srw_tac[ETA_ss]
    [Cevaluate_list_with_Cevaluate
    ,FOLDL_UNION_BIGUNION
    ,Cevaluate_con
    ,Cevaluate_list_with_EVERY] >>
    fs[] >>
    qpat_assum `LENGTH es = LENGTH vs` assume_tac >>
    fs[ZIP_MAP,LAMBDA_PROD,EVERY_MAP] >>
    match_mp_tac EVERY_MEM_MONO >>
    qmatch_assum_abbrev_tac `EVERY P ls` >>
    qexists_tac `P` >>
    fs[FORALL_PROD] >>
    rw[Abbr`P`,Abbr`ls`] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][BIGUNION_SUBSET] >>
    rw[] >>
    first_x_assum match_mp_tac >>
    qpat_assum `LENGTH es = LENGTH vs` assume_tac >>
    fs[MEM_ZIP,MEM_EL] >> PROVE_TAC[] ) >>
  strip_tac >- (
    srw_tac[ETA_ss]
    [Cevaluate_list_with_Cevaluate
    ,FOLDL_UNION_BIGUNION
    ,Cevaluate_con
    ,Cevaluate_list_with_error] >>
    fs[] >>
    rpt (qpat_assum `X < LENGTH es` mp_tac) >>
    rpt strip_tac >>
    fsrw_tac[DNF_ss][BIGUNION_SUBSET,MEM_EL] >>
    qmatch_assum_rename_tac `Cevaluate FEMPTY env (subst_labs c (EL m es)) (Rerr err)`[] >>
    qexists_tac `m` >> fsrw_tac[ARITH_ss][EL_MAP] ) >>
  strip_tac >- (
    rw[Cevaluate_tageq] >>
    PROVE_TAC[] ) >>
  strip_tac >- rw[Cevaluate_tageq] >>
  strip_tac >- (
    rw[Cevaluate_proj] >>
    PROVE_TAC[] ) >>
  strip_tac >- rw[Cevaluate_proj] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[Cevaluate_let_cons
      ,FOLDL_UNION_BIGUNION] >>
    disj1_tac >>
    qexists_tac `v` >>
    conj_tac >- rw[] >>
    first_x_assum match_mp_tac >>
    `every_result (Cclosed c) (Rval v)` by (
      match_mp_tac (MP_CANON Cevaluate_closed) >>
      PROVE_TAC[] ) >>
    fs[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[IN_FRANGE_DOMSUB_suff] ) >>
 strip_tac >- rw[Cevaluate_let_cons,FOLDL_UNION_BIGUNION] >>
 strip_tac >- (
   rw[] >>
   qpat_assum `LENGTH ns = LENGTH defs` assume_tac >>
   fs[FOLDL2_FUPDATE_LIST_paired,FOLDL_UNION_BIGUNION_paired] >>
   rw[Once Cevaluate_cases] >- (
     rw[MEM_MAP,FORALL_PROD] >>
     qmatch_rename_tac `INR l ≠ subst_lab c cb ∨ P`["P"] >>
     Cases_on `cb` >> fs[] ) >>
   rw[FOLDL2_FUPDATE_LIST_paired] >>
   fs[MAP2_MAP,FST_triple,MAP_ZIP]

(* ugh is this really necessary... << *)

val free_labsv_def = tDefine "free_labsv"`
  (free_labsv (CLitv _) = {}) ∧
  (free_labsv (CConv _ vs) = BIGUNION (IMAGE free_labsv (set vs))) ∧
  (free_labsv (CRecClos _ _ defs _) = IMAGE OUTR (set (FILTER ISR (MAP SND defs))))`
  (WF_REL_TAC `measure Cv_size` >>
   srw_tac[ARITH_ss][Cvs_size_thm] >>
   Q.ISPEC_THEN `Cv_size` imp_res_tac SUM_MAP_MEM_bound >>
   fsrw_tac[ARITH_ss][])
val _ = export_rewrites["free_labsv_def"]

(*
val Cevaluate_free_labs = store_thm("Cevaluate_free_labs",
  ``∀c env exp res. Cevaluate c env exp res ⇒
      ∀v. (res = Rval v) ⇒ free_labsv v ⊆ free_labs exp``,
  ho_match_mp_tac Cevaluate_nice_ind >>
  rw[]
>> *)

(* make closures carry a code environment domain and make sure they are closed with respect to it *)

val Cevaluate_any_code_env = store_thm("Cevaluate_any_code_env",
  ``∀c env exp res. Cevaluate c env exp res ⇒
      (∀l. l ∈ free_labs exp ⇒ l ∈ FDOM c)
      ⇒ ∀c'. (DRESTRICT c' (free_labs exp) = (DRESTRICT c (free_labs exp)))
        ⇒ Cevaluate c' env exp res``
  ho_match_mp_tac Cevaluate_nice_ind >>
  srw_tac[DNF_ss][FOLDL_FUPDATE_LIST,
  Cevaluate_con,Cevaluate_list_with_Cevaluate,
  Cevaluate_list_with_EVERY,
  Cevaluate_list_with_error,
  Cevaluate_tageq,
  Cevaluate_proj] >> fs[] >>
  TRY (
    match_mp_tac EVERY_MEM_MONO >>
    qmatch_assum_abbrev_tac `EVERY P l` >>
    qexists_tac `P` >>
    unabbrev_all_tac >>
    fs[FORALL_PROD] >>
    rw[MEM_ZIP] >>
    first_x_assum (match_mp_tac o MP_CANON) >>
    fsrw_tac[DNF_ss][MEM_EL] >>
    conj_tac >- metis_tac[] >>
    match_mp_tac DRESTRICT_SUBSET >>
    qmatch_assum_abbrev_tac `DRESTRICT c' s = DRESTRICT c s` >>
    qexists_tac `s` >> fs[Abbr`s`] >>
    srw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
    PROVE_TAC[] ) >>
  TRY (
    qexists_tac `n` >> fs[] >>
    conj_tac >- (
      first_x_assum (match_mp_tac o MP_CANON) >>
      fs[MEM_EL] >>
      conj_tac >- metis_tac[] >>
      match_mp_tac DRESTRICT_SUBSET >>
      qmatch_assum_abbrev_tac `DRESTRICT c' s = DRESTRICT c s` >>
      qexists_tac `s` >> fs[Abbr`s`] >>
      srw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
      PROVE_TAC[] ) >>
    qx_gen_tac `m` >> strip_tac >>
    qpat_assum `∀m. m < n ==> P` (qspec_then `m` mp_tac) >> fs[] >>
    disch_then (Q.X_CHOOSE_THEN `v` strip_assume_tac) >>
    qexists_tac `v` >>
    pop_assum (match_mp_tac o MP_CANON) >>
    `m < LENGTH es` by DECIDE_TAC >>
    fs[MEM_EL] >>
    conj_tac >- metis_tac[] >>
    match_mp_tac DRESTRICT_SUBSET >>
    qmatch_assum_abbrev_tac `DRESTRICT c' s = DRESTRICT c s` >>
    qexists_tac `s` >> fs[Abbr`s`] >>
    srw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
    PROVE_TAC[] ) >>
  TRY (
    qexists_tac `m` >>
    PROVE_TAC[] ) >>
  TRY (
    rw[Once Cevaluate_cases] >>
    disj1_tac >>
    first_x_assum (qspec_then `c'` mp_tac) >>
    first_x_assum (qspec_then `c'` mp_tac) >>
    rw[] >>
    `DRESTRICT c' (free_labs exp) = DRESTRICT c (free_labs exp)` by (
      match_mp_tac DRESTRICT_SUBSET >>
      qmatch_assum_abbrev_tac `DRESTRICT c' s = DRESTRICT c s` >>
      qexists_tac `s` >> fs[Abbr`s`] ) >>
    fs[] >>
    map_every qexists_tac [`env'`,`ns'`,`defs`,`n`] >>
    fs[] >>
    rw[Cevaluate_list_with_Cevaluate,
       Cevaluate_list_with_EVERY] >>
    qexists_tac `vs` >> fs[] >>
    conj_tac >- (
      match_mp_tac EVERY_MEM_MONO >>
      qmatch_assum_abbrev_tac `EVERY P l` >>
      qexists_tac `P` >>
      unabbrev_all_tac >>
      fs[FORALL_PROD] >>
      rw[MEM_ZIP] >>
      first_x_assum (match_mp_tac o MP_CANON) >>
      fsrw_tac[DNF_ss][MEM_EL] >>
      conj_tac >- metis_tac[] >>
      match_mp_tac DRESTRICT_SUBSET >>
      qpat_assum `DRESTRICT c' (free_labs exp) = X` kall_tac >>
      qmatch_assum_abbrev_tac `DRESTRICT c' s = DRESTRICT c s` >>
      qexists_tac `s` >> fs[Abbr`s`] >>
      srw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
      PROVE_TAC[] ) >>
    qho_match_abbrev_tac `Cevaluate c' exe (f c') res`
    `f c' = f c` by (
      unabbrev_all_tac >>
      Cases_on `cb` >> rw[] >>
      Cclosed_rules
      Cevaluate_closed
    first_x_assum (MATCH_MP_TAC o MP_CANON)


val label_closures_thm1 = store_thm("label_closures_thm1",
  ``(∀s1 Ce1 s2 Ce2. (label_closures s1 Ce1 = (s2,Ce2)) ⇒
      (∀c env res. Cevaluate c env Ce1 res ⇒ Cevaluate (c ⊌ s2.lbods) env Ce2 res)) ∧
    (∀s1 Ces1 s2 Ces2. (label_closures_list s1 Ces1 = (s2,Ces2)) ⇒
      (∀c env res. Cevaluate_list c env Ces1 res ⇒ Cevaluate_list (c ⊌ s2.lbods) env Ces2 res)) ∧
    (∀s ns ls ds defs s2 defs2. (labelise s ns ls ds defs = (s2,defs2)) ⇒
      T)``,
  ho_match_mp_tac label_closures_ind >>
  strip_tac >- rw[label_closures_def,Once Cevaluate_cases] >>
  strip_tac >- rw[label_closures_def,Once Cevaluate_cases] >>
  strip_tac >- rw[label_closures_def,Once Cevaluate_cases] >>
  strip_tac >- rw[label_closures_def,Once Cevaluate_cases] >>
  strip_tac >- (
    rw[label_closures_def,LET_THM] >>
    Cases_on `label_closures_list s1 Ces1` >> fs[] >>
    fs[Cevaluate_con] >> rw[Cevaluate_con]) >>
  strip_tac >- (
    rw[label_closures_def,LET_THM] >>
    Cases_on `label_closures s1 Ce1` >> fs[] >>
    fs[Cevaluate_tageq] >> rw[Cevaluate_tageq] >>
    PROVE_TAC[] ) >>
  strip_tac >- (
    rw[label_closures_def,LET_THM] >>
    Cases_on `label_closures s1 Ce1` >> fs[] >>
    fs[Cevaluate_proj] >> rw[Cevaluate_proj] >>
    PROVE_TAC[] ) >>
  strip_tac >- (
    rw[label_closures_def,LET_THM] >>
    qabbrev_tac`p = label_closures_list s1 Ces1` >>
    PairCases_on `p` >> fs[] >>
    qabbrev_tac`q = label_closures p0 Ce1` >>
    PairCases_on `q` >> fs[] >>
    rw[] >>

    fs[Once(SIMP_RULE(srw_ss())[](Q.SPECL[`c`,`env`,`CLet xs Ces1 Ce1`](CONJUNCT1 Cevaluate_cases)))] >>
    rw[Once(Q.SPECL[`c`,`env`,`CLet xs p1 q1`](CONJUNCT1 Cevaluate_cases))] >>
    fs[markerTheory.Abbrev_def,label_closures_def,LET_THM] >>
    qabbrev_tac`r = label_closures s1 e` >>
    PairCases_on `r` >> fs[] >>
    qabbrev_tac`pp = label_closures_list r0 es` >>
    PairCases_on `pp` >> fs[] >>
    fs[Once(Q.SPECL[`c`,`env|+(n,v)`,`CLet ns es Ce1`](CONJUNCT1 Cevaluate_cases))] >>
    fs[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_cons] >>
    rw[] >> PROVE_TAC[]

    Cases_on `label_closures s1 e` >> fs[]

(* compile correctness stuff *)

val labels_only_def = Define`
  labels_only ls = ∀x. MEM x ls ⇒ case x of
    | Jump (Addr _) => F
    | JumpNil (Addr _) => F
    | Call (Addr _) => F
    | _ => T`;

val el_of_addr_def = Define`
  (el_of_addr il n [] = NONE) ∧
  (el_of_addr il n (x::xs) =
   if is_Label x then OPTION_BIND (el_of_addr il n xs) (λm. SOME (m + 1)) else
     if n = 0 then SOME (0:num) else
       if n < il x + 1 then NONE else
         OPTION_BIND (el_of_addr il (n - (il x + 1)) xs) (λm. SOME (m + 1)))`
val _ = export_rewrites["el_of_addr_def"]

val bc_fetch_aux_el_of_addr = store_thm("bc_fetch_aux_el_of_addr",
  ``∀c il pc. bc_fetch_aux c il pc = OPTION_BIND (el_of_addr il pc c) (λn. SOME (EL n c))``,
  Induct >> rw[] >>
  Q.PAT_ABBREV_TAC`opt = el_of_addr il pcX c` >>
  Cases_on `opt` >> fs[] >>
  rw[GSYM arithmeticTheory.ADD1])

val addr_of_el_def = Define`
  (addr_of_el il n [] = NONE) ∧
  (addr_of_el il n (x::xs) =
   if n = 0 then if is_Label x then NONE else SOME 0 else
     OPTION_BIND (addr_of_el il (n - 1) xs) (λm. SOME (m + (if is_Label x then 0 else il x + 1))))`
val _ = export_rewrites["addr_of_el_def"]

val bc_fetch_aux_addr_of_el = store_thm("bc_fetch_aux_addr_of_el",
  ``∀c il pc n. (addr_of_el il n c = SOME pc) ⇒ (bc_fetch_aux c il pc = SOME (EL n c))``,
  Induct >> rw[] >>
  Cases_on `n` >> fs[] >>
  spose_not_then strip_assume_tac >>
  DECIDE_TAC)

val bc_fetch_aux_not_label = store_thm("bc_fetch_aux_not_label",
  ``∀c il pc i. (bc_fetch_aux c il pc = SOME i) ⇒ ¬is_Label i``,
  Induct >> rw[] >> fs[] >> PROVE_TAC[])

val with_same_pc = store_thm("with_same_pc",
  ``x with pc := x.pc = x``,
  rw[DB.fetch"Bytecode""bc_state_component_equality"])
val _ = export_rewrites["with_same_pc"]

val bc_next_fetch_only = store_thm("bc_next_fetch_only",
  ``∀r1 r2. bc_next r1 r2 ⇒
      ∀tr s1. (∀pc. bc_fetch (r1 with pc := pc) = OPTION_BIND (tr pc) (λpc. bc_fetch (s1 with pc := pc))) ∧
              (tr r1.pc = SOME s1.pc) ∧
              (s1.stack = r1.stack)
        ⇒ ∃pc. (tr r2.pc = SOME pc) ∧ bc_next s1 (r2 with pc := pc)``,
  ho_match_mp_tac bc_next_ind >>
  rw[] >>
  first_assum (qspec_then `r1.pc` mp_tac) >>
  simp_tac (srw_ss()) [] >>
  asm_simp_tac (srw_ss()) [] >>
  disch_then (assume_tac o SYM) >>
  rw[bc_next_cases] >>

val addr_of_el_bc_fetch_aux = store_thm("addr_of_el_bc_fetch_aux",
  ``∀c il pc n. (bc_fetch_aux c il pc = SOME (EL n c)) ⇒ (addr_of_el il n c = SOME pc)``,
  Induct >> rw[]
  >- PROVE_TAC[bc_fetch_aux_not_label]
  >- (Cases_on `n` >> fs[])

val translate_pc_def = Define`
  translate_pc il1 il2 c pc = OPTION_BIND (el_of_addr il1 pc c) (λn. addr_of_el il2 n c)`

val labels_only_any_il = store_thm("labels_only_any_il",
  ``∀s1 s2. bc_next s1 s2 ⇒ labels_only s1.code ⇒
    ∀il. ∃p1 p2.
      (translate_pc s1.inst_length il s1.code s1.pc = SOME p1) ∧
      (translate_pc s2.inst_length il s2.code s2.pc = SOME p2) ∧
      bc_next (s1 with <| inst_length := il; pc := p1 |>)
              (s2 with <| inst_length := il; pc := p2 |>)``,
  ho_match_mp_tac bc_next_ind >>
  rw[bc_fetch_def] >>
  fs[bc_fetch_aux_el_of_addr,translate_pc_def,bump_pc_def,bc_fetch_def]
  strip_tac

val bc_finish_def = Define`
  bc_finish s1 s2 = bc_next^* s1 s2 ∧ ∀s3. ¬bc_next s2 s3`

val el_check_def = Define`
  el_check n ls = if n < LENGTH ls then SOME (EL n ls) else NONE`
val _ = export_rewrites["el_check_def"]

val lookup_ct_def = Define`
  (lookup_ct sz st rs (CTLet n) = el_check (sz - n) st) ∧
  (lookup_ct sz st rs (CTArg n) = el_check (sz + n) st) ∧
  (lookup_ct sz st rs (CTEnv n) =
   OPTION_BIND (el_check sz st)
   (λv. case v of Block 0 vs => el_check n vs | _ => NONE)) ∧
  (lookup_ct sz st rs (CTRef n) =
   OPTION_BIND (el_check sz st)
   (λv. case v of Block 0 vs =>
     OPTION_BIND (el_check n vs)
     (λv. case v of RefPtr p => FLOOKUP rs p | _ => NONE)
     | _ => NONE))`
val _ = export_rewrites["lookup_ct_def"]

val emit_def = CompileTheory.emit_def
val incsz_def = CompileTheory.incsz_def
val _ = export_rewrites["Compile.emit_def","Compile.incsz_def"]
val repl_exp_def = CompileTheory.repl_exp_def
val compile_Cexp_def = CompileTheory.compile_Cexp_def

val add_code_def = Define`
  add_code c (s:bc_state) = s with <| code := s.code ++ c |>`

val bc_fetch_aux_any_inst_length = store_thm("bc_fetch_aux_any_inst_length",
 ``∀c il pc il'. bc_fetch_aux c il' pc =
   OPTION_BIND (el_of_addr il' pc c)
   (λn. OPTION_BIND (addr_of_el il n c)
        (λpc. bc_fetch_aux c il pc))``,
 Induct >- rw[] >>
 rw[] >- (
   first_x_assum (qspecl_then [`il'`,`0`] mp_tac) >>
   rw[] >>
    Q.PAT_ABBREV_TAC`opt = el_of_addr il' 0 c` >>
    Cases_on `opt` >> fs[] >>

 rpt gen_tac >>
 simp_tac(srw_ss())[]
 rw[] >> rw[]
 ho_match_mp_tac bc_fetch_aux_ind >>
 strip_tac >- rw[] >>
 strip_tac >- (
   rw[bc_fetch_aux_el_of_addr] >>
   Cases_on `el_of_addr il' pc c` >> fs[] >>
   rw[GSYM arithmeticTheory.ADD1] >>
   Cases_on `addr_of_el il x c` >> fs[] ) >>
 strip_tac >- (
   rw[] >> rw[] >>
   rw[bc_fetch_aux_el_of_addr] >>
   Q.PAT_ABBREV_TAC`opt = el_of_addr il' pcX cX` >>
   Cases_on `opt` >> fs[] >>
   rw[GSYM arithmeticTheory.ADD1] >>
   fsrw_tac[DNF_ss][] >>
   fs[markerTheory.Abbrev_def] >>
   Cases_on `addr_of_el il x c` >> fs[] 

val bc_next_any_inst_length = store_thm("bc_next_any_inst_length",
  ``∀s1 s2. bc_next s1 s2 ⇒ ∀il. bc_next (s1 with <| inst_length := il |>) (s2 with <| inst_length := il |>)``,
  ho_match_mp_tac bc_next_ind >>
  strip_tac >- (
    rw[]

val set_pc_el_def = Define`
  set_pc_el n s = s with <| pc := addr_of_el n s.inst_length s.code |>`

val bc_fetch_aux_addr_of_el = store_thm("bc_fetch_aux_addr_of_el",
  ``∀c n. (∀l. n < LENGTH c ⇒ EL n c ≠ Label l) ⇒
       (bc_fetch_aux c il (addr_of_el n il c) = if n < LENGTH c then SOME (EL n c) else NONE)``,
  Induct >- rw[] >>
  CONV_TAC SWAP_FORALL_CONV >>
  Induct >- (
    fs[addr_of_el_def] >>
    Cases >> rw[] ) >>
  fs[addr_of_el_def] >>
  Cases >> rw[] >>
  fsrw_tac[ARITH_ss][])

val bc_fetch_set_pc_el = store_thm("bc_fetch_set_pc_el",
  ``n < LENGTH s.code ∧ (∀l. EL n s.code ≠ Label l) ⇒
      (bc_fetch (set_pc_el n s) = SOME (EL n s.code))``,
  rw[bc_fetch_def,set_pc_el_def] >>
  metis_tac[bc_fetch_aux_addr_of_el])

val compile_thm1 = store_thm("compile_thm1",
  ``∀env exp res. Cevaluate env exp res ⇒
    ∀v cs cs'.
      (res = Rval v) ∧ (∀s. exp ≠ CDecl s) ∧
      FDOM env ⊆ FDOM cs.env ∧
      (cs' = compile cs exp) ⇒
        ∃c. (cs'.out = c++cs.out) ∧
          ∀b1. (∀x. x ∈ FDOM env ⇒ ∃v. (lookup_ct cs.sz b1.stack b1.refs (cs.env ' x) = SOME v) ∧
                                       bceqv b1.inst_length b1.code (env ' x) v) ⇒
            ∃b2. bc_finish (set_pc_el (LENGTH b1.code) (add_code (REVERSE c) b1)) b2 ∧
                 ∃bv. (b2.stack = bv::b1.stack) ∧
                      bceqv b2.inst_length b2.code v bv``,
  ho_match_mp_tac Cevaluate_nice_ind >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[compile_def] >>
    rw[bc_finish_def,arithmeticTheory.RTC_eq_NRC] >>
    Cases_on `cs.env ' n` >>
    rw[compile_varref_def] >>
    fsrw_tac[DNF_ss][] >- (
      CONV_TAC (RESORT_EXISTS_CONV rev) >>
      qexists_tac `1` >>
      rw[] >>
      rw[Once bc_next_cases] >>
      srw_tac[ARITH_ss][bc_fetch_set_pc_el,add_code_def,rich_listTheory.EL_LENGTH_APPEND] >>
      qmatch_assum_rename_tac `cs.env ' n = CTLet x`[] >>
      first_x_assum (qspec_then `n` mp_tac) >>
      rw[] >>
      rw[bc_stack_op_cases]
      >- rw[set_pc_el_def]
      >- rw[set_pc_el_def]
      >- (
        
      rw[bump_pc_def]
      rw[addr_of_el_def]

(* values in compile-time environment *)
type ctbind = CTLet of num | CTArg of num | CTEnv of num | CTRef of num
(* CTLet n means stack[sz - n]
   CTArg n means stack[sz + n]
   CTEnv n means El n of the environment, which is at stack[sz]
   CTRef n means El n of the environment, but it's a ref pointer *)

val repl_exp_thm1 = store_thm("repl_exp_thm1",

(*
val Cpat_nice_ind =
TypeBase.induction_of(``:Cpat``)
|> Q.SPECL[`P`,`EVERY P`]
|> SIMP_RULE(srw_ss())[]
|> UNDISCH_ALL
|> CONJUNCT1
|> DISCH_ALL
|> Q.GEN`P`

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
