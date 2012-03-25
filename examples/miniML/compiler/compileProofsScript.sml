open preamble MiniMLTheory MiniMLTerminationTheory
open CompileTheory evaluateEquationsTheory

val _ = new_theory "compileProofs"

(* move elsewhere? *)
val exp1_size_thm = store_thm(
"exp1_size_thm",
``∀ls. exp1_size ls = SUM (MAP exp2_size ls) + LENGTH ls``,
Induct >- rw[exp_size_def] >>
qx_gen_tac `p` >>
PairCases_on `p` >>
srw_tac [ARITH_ss][exp_size_def])

val exp6_size_thm = store_thm(
"exp6_size_thm",
``∀ls. exp6_size ls = SUM (MAP exp7_size ls) + LENGTH ls``,
Induct >- rw[exp_size_def] >>
Cases >> srw_tac [ARITH_ss][exp_size_def])

val exp8_size_thm = store_thm(
"exp8_size_thm",
``∀ls. exp8_size ls = SUM (MAP exp_size ls) + LENGTH ls``,
Induct >- rw[exp_size_def] >>
srw_tac [ARITH_ss][exp_size_def])

val exp9_size_thm = store_thm(
"exp9_size_thm",
``∀ls. exp9_size ls = SUM (MAP v_size ls) + LENGTH ls``,
Induct >- rw[exp_size_def] >>
srw_tac [ARITH_ss][exp_size_def])

val pat1_size_thm = store_thm(
"pat1_size_thm",
``∀ls. pat1_size ls = SUM (MAP pat_size ls) + LENGTH ls``,
Induct >- rw[pat_size_def] >>
srw_tac [ARITH_ss][pat_size_def])

val SUM_MAP_exp2_size_thm = store_thm(
"SUM_MAP_exp2_size_thm",
``∀defs. SUM (MAP exp2_size defs) = SUM (MAP (list_size char_size) (MAP FST defs)) +
                                    SUM (MAP exp4_size (MAP SND defs)) +
                                    LENGTH defs``,
Induct >- rw[exp_size_def] >>
qx_gen_tac `p` >>
PairCases_on `p` >>
srw_tac[ARITH_ss][exp_size_def])

val exp_size_positive = store_thm(
"exp_size_positive",
``∀e. 0 < exp_size e``,
Induct >> srw_tac[ARITH_ss][exp_size_def])
val _ = export_rewrites["exp_size_positive"]

val Cexp1_size_thm = store_thm(
"Cexp1_size_thm",
``∀ls. Cexp1_size ls = SUM (MAP Cexp2_size ls) + LENGTH ls``,
Induct >- rw[Cexp_size_def] >>
qx_gen_tac `p` >>
PairCases_on `p` >>
srw_tac [ARITH_ss][Cexp_size_def])

val Cexp4_size_thm = store_thm(
"Cexp4_size_thm",
``∀ls. Cexp4_size ls = SUM (MAP Cexp6_size ls) + LENGTH ls``,
Induct >- rw[Cexp_size_def] >>
srw_tac [ARITH_ss][Cexp_size_def])

val Cexp5_size_thm = store_thm(
"Cexp5_size_thm",
``∀ls. Cexp5_size ls = SUM (MAP Cexp7_size ls) + LENGTH ls``,
Induct >- rw[Cexp_size_def] >>
srw_tac [ARITH_ss][Cexp_size_def])

val Cexp8_size_thm = store_thm(
"Cexp8_size_thm",
``∀ls. Cexp8_size ls = SUM (MAP Cexp_size ls) + LENGTH ls``,
Induct >- rw[Cexp_size_def] >>
srw_tac [ARITH_ss][Cexp_size_def])

val LENGTH_FOLDL_CONS_SND = store_thm(
"LENGTH_FOLDL_CONS_SND",
``∀ls f g m lsa. LENGTH (SND (FOLDL (λ(m,ls) x. (f (m,ls) x, (g (m,ls) x::ls))) (m,lsa) ls)) = LENGTH lsa + LENGTH ls``,
Induct >> srw_tac[ARITH_ss][])

val (remove_Gt_Geq_def,remove_Gt_Geq_ind) =
  tprove_no_defn ((remove_Gt_Geq_def,remove_Gt_Geq_ind),
  WF_REL_TAC `measure exp_size` >>
  srw_tac[ARITH_ss][exp1_size_thm,exp6_size_thm,exp8_size_thm] >>
  imp_res_tac SUM_MAP_MEM_bound >|
    map (fn q => pop_assum (qspec_then q mp_tac))
    [`exp2_size`,`exp7_size`,`exp_size`] >>
  srw_tac[ARITH_ss][exp_size_def])
val _ = save_thm ("remove_Gt_Geq_def", remove_Gt_Geq_def);
val _ = save_thm ("remove_Gt_Geq_ind", remove_Gt_Geq_ind);

val (remove_mat_def,remove_mat_ind) =
  tprove_no_defn ((remove_mat_def,remove_mat_ind),
  WF_REL_TAC
  `inv_image $<
    (λx. case x of
         | INL e => Cexp_size e
         | INR (v,pes) => Cexp5_size pes)` >>
  srw_tac[ARITH_ss][Cexp1_size_thm,Cexp4_size_thm,Cexp8_size_thm] >>
  imp_res_tac SUM_MAP_MEM_bound >|
    map (fn q => pop_assum (qspec_then q mp_tac))
    [`Cexp2_size`,`Cexp_size`,`Cexp6_size`,`Cexp_size`,`Cexp_size`] >>
  srw_tac[ARITH_ss][Cexp_size_def])
val _ = save_thm ("remove_mat_def", remove_mat_def);
val _ = save_thm ("remove_mat_ind", remove_mat_ind);

val (remove_mat_exp_def, remove_mat_exp_ind) =
  tprove_no_defn ((remove_mat_exp_def,remove_mat_exp_ind),
  WF_REL_TAC `measure exp_size` >>
  srw_tac[ARITH_ss][exp1_size_thm,exp6_size_thm,exp8_size_thm] >>
  MAP_EVERY (fn q => Q.ISPEC_THEN q mp_tac SUM_MAP_MEM_bound) [`exp7_size`,`exp_size`,`exp2_size`] >>
  rw[] >> res_tac >> fs[exp_size_def] >> srw_tac[ARITH_ss][])
val _ = save_thm ("remove_mat_exp_def", remove_mat_exp_def);
val _ = save_thm ("remove_mat_exp_ind", remove_mat_exp_ind);

val (exp_to_Cexp_def,exp_to_Cexp_ind) =
  tprove_no_defn ((exp_to_Cexp_def,exp_to_Cexp_ind),
  WF_REL_TAC `measure (exp_size o SND)` >>
  srw_tac[ARITH_ss][exp1_size_thm,exp8_size_thm,exp6_size_thm]
>- (
  qmatch_assum_abbrev_tac `(m2,fns) = FOLDL ff (m,[]) defs` >>
  Q.ISPECL_THEN [`defs`,`λx y. FST (ff x y)`,`λx y. HD (SND (ff x y))`,`m`,`[]:num list`] mp_tac LENGTH_FOLDL_CONS_SND >>
  rw[] >>
  qmatch_assum_abbrev_tac `LENGTH (SND (FOLDL ff' (m,[]) defs)) = LENGTH defs` >>
  `ff' = ff` by (
    unabbrev_all_tac >>
    fs[FUN_EQ_THM] >>
    ntac 2 gen_tac >>
    qx_gen_tac `p` >>
    PairCases_on `p` >> rw[] ) >>
  qpat_assum `LENGTH x = LENGTH y` mp_tac >>
  qpat_assum `(x,y) = FOLDL ff (m,[]) defs` (assume_tac o SYM) >>
  rw[] >>
  fs[MEM_ZIP] >> rw[] >>
  qmatch_assum_rename_tac `(_d,vn,e) = EL mm defs` [] >>
  `MEM (_d,vn,e) defs` by (rw[MEM_EL] >> PROVE_TAC[]) >>
  imp_res_tac SUM_MAP_MEM_bound >>
  pop_assum (qspec_then `exp2_size` mp_tac) >>
  srw_tac[ARITH_ss][exp_size_def] )
>- (
  imp_res_tac SUM_MAP_MEM_bound >>
  pop_assum (qspec_then `exp_size` mp_tac) >>
  srw_tac[ARITH_ss][exp_size_def] )
>- (
  imp_res_tac SUM_MAP_MEM_bound >>
  pop_assum (qspec_then `exp7_size` mp_tac) >>
  srw_tac[ARITH_ss][exp_size_def] ))
val _ = save_thm ("exp_to_Cexp_def", exp_to_Cexp_def);
val _ = save_thm ("exp_to_Cexp_ind", exp_to_Cexp_ind);

val least_not_in_aux_exists = prove(
``∃f. ∀s n. f s n = if n ∈ s then f s (n + (1:num)) else n``,
qexists_tac `λs n. WHILE (λn. n ∈ s) (λn. n + 1) n` >>
rw[] >>
rw[Once whileTheory.WHILE])
val least_not_in_aux_def = new_specification("least_not_in_aux_def",["least_not_in_aux"],least_not_in_aux_exists)

val least_not_in_thm = store_thm(
"least_not_in_thm",
``∀s. FINITE s ⇒ (least_not_in s = least_not_in_aux s 0)``,
rw[least_not_in_def] >>
numLib.LEAST_ELIM_TAC >>
rw[] >- PROVE_TAC[INFINITE_NUM_UNIV, NOT_IN_FINITE] >>
qsuff_tac `∀m. m ≤ n ⇒ (n = least_not_in_aux s m)` >-
  PROVE_TAC[arithmeticTheory.ZERO_LESS_EQ] >>
Induct_on `n-m` >>
srw_tac[ARITH_ss][] >- (
  `n = m` by DECIDE_TAC >>
  rw[Once least_not_in_aux_def] ) >>
`m < n` by DECIDE_TAC >>
`m ∈ s` by PROVE_TAC[] >>
rw[Once least_not_in_aux_def] >>
first_x_assum (qspecl_then [`n`,`m+1`] mp_tac) >>
`v = n - (m + 1)` by DECIDE_TAC >>
`m + 1 ≤ n` by DECIDE_TAC >>
rw[])

val (free_vars_def, free_vars_ind) =
  tprove_no_defn ((free_vars_def,free_vars_ind),
  WF_REL_TAC `measure Cexp_size` >>
  srw_tac[ARITH_ss][Cexp8_size_thm,Cexp4_size_thm,Cexp1_size_thm,Cexp5_size_thm] >>
  MAP_EVERY (fn q => Q.ISPEC_THEN q mp_tac SUM_MAP_MEM_bound)
    [`Cexp6_size`,`Cexp2_size`,`Cexp_size`,`Cexp7_size`] >>
  rw[] >> res_tac >> fs[Cexp_size_def] >> srw_tac[ARITH_ss][])
val _ = save_thm ("free_vars_def", free_vars_def);
val _ = save_thm ("free_vars_ind", free_vars_ind);

val (pat_to_Cpat_def, pat_to_Cpat_ind) =
  tprove_no_defn ((pat_to_Cpat_def,pat_to_Cpat_ind),
  WF_REL_TAC `measure (pat_size o SND)` >>
  srw_tac [ARITH_ss][pat1_size_thm] >>
  imp_res_tac SUM_MAP_MEM_bound >>
  pop_assum (qspec_then `pat_size` mp_tac) >>
  srw_tac[ARITH_ss][])
val _ = save_thm ("pat_to_Cpat_def", pat_to_Cpat_def);
val _ = save_thm ("pat_to_Cpat_ind", pat_to_Cpat_ind);

(* ------------------------------------------------------------------------- *)

(* TODO: move where? *)

val type_es_every_map = store_thm(
"type_es_every_map",
``∀tenvC tenv es ts. type_es tenvC tenv es ts = (LENGTH es = LENGTH ts) ∧ EVERY (UNCURRY (type_e tenvC tenv)) (ZIP (es,ts))``,
ntac 2 gen_tac >>
Induct >- (
  rw[Once type_v_cases] >>
  Cases_on `ts` >> rw[] ) >>
rw[Once type_v_cases] >>
Cases_on `ts` >> rw[] >>
metis_tac[])

val type_vs_every_map = store_thm(
"type_vs_every_map",
``∀tenvC vs ts. type_vs tenvC vs ts = (LENGTH vs = LENGTH ts) ∧ EVERY (UNCURRY (type_v tenvC)) (ZIP (vs,ts))``,
gen_tac >>
Induct >- (
  rw[Once type_v_cases] >>
  Cases_on `ts` >> rw[] ) >>
rw[Once type_v_cases] >>
Cases_on `ts` >> rw[] >>
metis_tac[])

(* TODO: Where should these go? *)

val well_typed_def = Define`
  well_typed env exp = ∃tenvC tenv t.
    type_env tenvC env tenv ∧
    type_e tenvC tenv exp t`;

val (subexp_rules,subexp_ind,subexp_cases) = Hol_reln`
  (MEM e es ⇒ subexp e (Con cn es)) ∧
  (subexp e1 (App op e1 e2)) ∧
  (subexp e2 (App op e1 e2))`

val well_typed_subexp_lem = store_thm(
"well_typed_subexp_lem",
``∀env e1 e2. subexp e1 e2 ⇒ well_typed env e2 ⇒ well_typed env e1``,
gen_tac >>
ho_match_mp_tac subexp_ind >>
fs[well_typed_def] >>
strip_tac >- (
  rw[Once (List.nth (CONJUNCTS type_v_cases, 1))] >>
  fs[type_es_every_map] >>
  qmatch_assum_rename_tac `EVERY X (ZIP (es,MAP f ts))` ["X"] >>
  fs[MEM_EL] >> rw[] >>
  `MEM (EL n es, f (EL n ts)) (ZIP (es, MAP f ts))` by (
    rw[MEM_ZIP] >> qexists_tac `n` >> rw[EL_MAP] ) >>
  fs[EVERY_MEM] >> res_tac >>
  fs[] >> metis_tac []) >>
strip_tac >- (
  rw[Once (List.nth (CONJUNCTS type_v_cases, 1))] >>
  metis_tac [] ) >>
strip_tac >- (
  rw[Once (List.nth (CONJUNCTS type_v_cases, 1))] >>
  metis_tac [] ))

val well_typed_Con_subexp = store_thm(
"well_typed_Con_subexp",
``∀env cn es. well_typed env (Con cn es) ⇒ EVERY (well_typed env) es``,
rw[EVERY_MEM] >>
match_mp_tac (MP_CANON well_typed_subexp_lem) >>
qexists_tac `Con cn es` >>
rw[subexp_rules])

val well_typed_App_subexp = store_thm(
"well_typed_App_subexp",
``∀env op e1 e2. well_typed env (App op e1 e2) ⇒ well_typed env e1 ∧ well_typed env e2``,
rw[] >> match_mp_tac (MP_CANON well_typed_subexp_lem) >>
metis_tac [subexp_rules])

val map_result_def = Define`
  (map_result f (Rval v) = Rval (f v)) ∧
  (map_result f (Rerr e) = Rerr e)`;
val _ = export_rewrites["map_result_def"];

(* ------------------------------------------------------------------------- *)

(* TODO: move to listTheory (and rich_listTheory) *)
val FOLDR_MAP = store_thm("FOLDR_MAP",
    (--`!f e g l.
       FOLDR f e (MAP g l) = FOLDR (\x y. f (g x) y) e l`--),
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN Induct
    THEN ASM_REWRITE_TAC[FOLDL,MAP,FOLDR] THEN BETA_TAC
    THEN REWRITE_TAC[]);

(* TODO: add to terminationProofsTheory? *)
val _ = augment_srw_ss[rewrites[lookup_def]]

(* Prove compiler phases preserve semantics *)

(*
val v_remove_ctors_Conv = store_thm(
"v_remove_ctors_Conv",
``∀cnmap cn vs. v_remove_ctors cnmap (Conv cn vs) =
                case cn of
                  NONE => Conv NONE (MAP (v_remove_ctors cnmap) vs)
                | SOME cn => Conv NONE (Lit (IntLit (cnmap cn)) ::
                                        MAP (v_remove_ctors cnmap) vs)``,
gen_tac >>
Cases >> rw [remove_ctors_def] >>
metis_tac [])
val _ = export_rewrites["v_remove_ctors_Conv"]

val lookup_remove_ctors = store_thm(
"lookup_remove_ctors",
``∀cnmap env n. lookup n (env_remove_ctors cnmap env) =
   case lookup n env of
     NONE => NONE
   | SOME v => SOME (v_remove_ctors cnmap v)``,
gen_tac >> Induct >-
  rw [remove_ctors_def] >>
Cases >>
rw [remove_ctors_def]);

val bind_remove_ctors = store_thm(
"bind_remove_ctors",
``∀cnmap n v env. env_remove_ctors cnmap (bind n v env) =
   bind n (v_remove_ctors cnmap v) (env_remove_ctors cnmap env)``,
ntac 3 gen_tac >>
Induct >>
rw [remove_ctors_def,bind_def]);
val _ = export_rewrites["bind_remove_ctors"];

val find_recfun_remove_ctors = store_thm(
"find_recfun_remove_ctors",
``∀cnmap n fs. find_recfun n (funs_remove_ctors cnmap fs) =
   OPTION_MAP (λ(n,e). (n, remove_ctors cnmap e)) (find_recfun n fs)``,
ntac 2 gen_tac >>
Induct >- (
  rw [remove_ctors_def,Once find_recfun_def] >>
  rw [Once find_recfun_def] ) >>
qx_gen_tac `h` >>
PairCases_on `h` >>
rw [remove_ctors_def] >>
rw [Once find_recfun_def] >- (
  rw [Once find_recfun_def] ) >>
rw [Once find_recfun_def, SimpRHS] );
val _ = export_rewrites["find_recfun_remove_ctors"];

val funs_remove_ctors_maps = store_thm(
"funs_remove_ctors_maps",
``∀cnmap funs. funs_remove_ctors cnmap funs =
  MAP (λ(vn1,vn2,e). (vn1,vn2,remove_ctors cnmap e)) funs``,
gen_tac >>
Induct >- rw[remove_ctors_def] >>
qx_gen_tac `p` >>
PairCases_on `p` >>
rw[remove_ctors_def]);

val env_remove_ctors_maps = store_thm(
"env_remove_ctors_maps",
``∀cnmap env. env_remove_ctors cnmap env = MAP (λ(n,v). (n,v_remove_ctors cnmap v)) env``,
gen_tac >>
Induct >- rw [remove_ctors_def] >>
Cases >>
rw[remove_ctors_def]);

val gen_build_rec_env_def = Define`
  gen_build_rec_env funs env funs1 env1 =
    FOLDR (λ(f,x,e) env'. bind f (Recclosure env1 funs1 f) env') env funs`

val gen_build_rec_env_remove_ctors = store_thm(
"gen_build_rec_env_remove_ctors",
``∀cnmap funs env funs1 env1.
  gen_build_rec_env
    (funs_remove_ctors cnmap funs)
    (env_remove_ctors cnmap env)
    (funs_remove_ctors cnmap funs1)
    (env_remove_ctors cnmap env1)
  = env_remove_ctors cnmap (gen_build_rec_env funs env funs1 env1)``,
gen_tac >>
Induct >-
  fs[gen_build_rec_env_def,funs_remove_ctors_maps] >>
fs[gen_build_rec_env_def,funs_remove_ctors_maps,env_remove_ctors_maps] >>
qx_gen_tac `p` >> PairCases_on `p` >>
rw[bind_def,remove_ctors_def,env_remove_ctors_maps,funs_remove_ctors_maps])

val gen_build_rec_env_specialises = store_thm(
"gen_build_rec_env_specialises",
``build_rec_env = λfuns env. gen_build_rec_env funs env funs env``,
rw[FUN_EQ_THM,gen_build_rec_env_def,build_rec_env_def])

val build_rec_env_remove_ctors = store_thm(
"build_rec_env_remove_ctors",
``∀cnmap funs env.
  (build_rec_env (funs_remove_ctors cnmap funs) (env_remove_ctors cnmap env) =
   env_remove_ctors cnmap (build_rec_env funs env))``,
rw[gen_build_rec_env_specialises,gen_build_rec_env_remove_ctors])

(* Ignore Equality case here, because we would need to know the original expression was well-typed *)
val do_app_remove_ctors = store_thm(
"do_app_remove_ctors",
``∀cnmap env op v1 v2. op ≠ Equality ⇒
  (do_app (env_remove_ctors cnmap env)
          op
          (v_remove_ctors cnmap v1)
          (v_remove_ctors cnmap v2) =
  case do_app env op v1 v2 of
    NONE => NONE
  | SOME (env',exp) => SOME (env_remove_ctors cnmap env', remove_ctors cnmap exp))``,
ntac 2 gen_tac >>
Cases >> Cases >> Cases >>
rw[do_app_def,remove_ctors_def] >>
BasicProvers.EVERY_CASE_TAC >>
fs[] >> rw[remove_ctors_def,build_rec_env_remove_ctors])

(*
val remove_ctors_thm1 = store_thm(
"remove_ctors_thm1",
``∀cnmap.
  (∀env exp r.
   evaluate' env exp r ⇒
   well_typed env exp ⇒
   evaluate' (env_remove_ctors cnmap env) (remove_ctors cnmap exp) (map_result (v_remove_ctors cnmap) r)) ∧
  (∀env expl rl.
   evaluate_list' env expl rl ⇒
   EVERY (well_typed env) expl ⇒
   evaluate_list' (env_remove_ctors cnmap env) (MAP (remove_ctors cnmap) expl) (map_result (MAP (v_remove_ctors cnmap)) rl)) ∧
  (∀env v pes r.
   evaluate_match' env v pes r ⇒
   EVERY (well_typed env o SND) pes ⇒
   evaluate_match' (env_remove_ctors cnmap env) (v_remove_ctors cnmap v) (match_remove_ctors cnmap pes) (map_result (v_remove_ctors cnmap) r))``,
gen_tac >>
ho_match_mp_tac evaluate'_ind >>
strip_tac >-
  rw [remove_ctors_def] >>
strip_tac >-
  rw [remove_ctors_def] >>
strip_tac >- (
  gen_tac >>
  Cases >- (
    rw [evaluate'_con,remove_ctors_def,do_con_check_def] >>
    metis_tac [well_typed_Con_subexp ] ) >>
  rpt gen_tac >>
  rw [evaluate'_con,remove_ctors_def] >>
  rw [Once evaluate'_cases] >>
  metis_tac [well_typed_Con_subexp]) >>
strip_tac >- (
  gen_tac >>
  Cases >> rw [remove_ctors_def] >>
  rw [Once evaluate'_cases] >-
    metis_tac [well_typed_Con_subexp] >>
  rw [Once evaluate_list'_thm] >>
  metis_tac [well_typed_Con_subexp] ) >>
strip_tac >-
  rw [remove_ctors_def,evaluate'_var,lookup_remove_ctors] >>
strip_tac >-
  rw [remove_ctors_def,evaluate'_var,lookup_remove_ctors] >>
strip_tac >-
  rw [remove_ctors_def] >>
strip_tac >- (
  rw [remove_ctors_def] >>
  imp_res_tac well_typed_App_subexp >>
  fs[] >>
  rw [evaluate'_app] >>
  disj1_tac >>
  qexists_tac `v_remove_ctors cnmap v1` >>
  rw [] >>
  qexists_tac `v_remove_ctors cnmap v2` >>
  rw [] >>
  (* need do_app preserves well_typed *)
  Cases_on `op = Equality` >- (
    ... ) >>
  rw[do_app_remove_ctors]
*)
*)

val _ = export_theory ()
