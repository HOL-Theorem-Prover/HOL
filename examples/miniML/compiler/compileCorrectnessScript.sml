open HolKernel bossLib boolLib MiniMLTheory evaluateEquationsTheory compileTerminationTheory listTheory lcsymtacs

val _ = new_theory "compileCorrectness"

val FINITE_free_vars = store_thm(
"FINITE_free_vars",
``∀t. FINITE (free_vars t)``,
ho_match_mp_tac free_vars_ind >>
rw[free_vars_def] >>
qmatch_rename_tac `FINITE (FOLDL XXX YYY ls)` ["XXX","YYY"] >>
qmatch_abbrev_tac `FINITE (FOLDL ff s0 ls)` >>
qsuff_tac `∀s0. FINITE s0 ⇒ FINITE (FOLDL ff s0 ls)` >- rw[Abbr`s0`] >>
Induct_on `ls` >> rw[Abbr`s0`] >>
first_assum (ho_match_mp_tac o MP_CANON) >>
rw[Abbr`ff`] >>
TRY (Cases_on `h` >> rw[]) >>
metis_tac[])

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

(* TODO: move these into the lem source? *)

val map_result_def = Define`
  (map_result f (Rval v) = Rval (f v)) ∧
  (map_result f (Rerr e) = Rerr e)`;
val _ = export_rewrites["map_result_def"];

val map_v_def = tDefine "map_v"`
  (map_v f (Lit l) = Lit l) ∧
  (map_v f (Conv n vs) = Conv n (MAP (map_v f) vs)) ∧
  (map_v f (Closure env n e) =
   Closure (MAP (λ(n,v). (n,map_v f v)) env) n (f e)) ∧
  (map_v f (Recclosure env defs n) =
   Recclosure
     (MAP (λ(n,v). (n,map_v f v)) env)
     (MAP (λ(n,m,e). (n,m,f e)) defs)
     n)`(
WF_REL_TAC `measure (v_size o SND)` >>
srw_tac[ARITH_ss][exp3_size_thm,exp9_size_thm] >>
imp_res_tac SUM_MAP_MEM_bound >>
TRY (pop_assum (qspec_then `exp5_size` mp_tac)) >>
TRY (pop_assum (qspec_then `v_size` mp_tac)) >>
srw_tac[ARITH_ss][exp_size_def])
val _ = export_rewrites["map_v_def"];

(* ------------------------------------------------------------------------- *)

(* TODO: add to MiniMLTerminationTheory? *)
val _ = augment_srw_ss[rewrites[lookup_def]]

(* Prove compiler phases preserve semantics *)

(*
val remove_Gt_Geq_eval = store_thm(
"remove_Gt_Geq_eval",
``∀env exp res. evaluate' env exp res = evaluate' env (remove_Gt_Geq exp) (map_result (map_v remove_Gt_Geq) res)``,
rw[EQ_IMP_THM] >- (
  qsuff_tac`
  (∀env exp res. evaluate' env exp res ⇒ evaluate' env (remove_Gt_Geq exp) (map_result (map_v remove_Gt_Geq) res)) ∧
  (∀env exps ress. evaluate_list' env exps ress ⇒ evaluate_list' env (MAP remove_Gt_Geq exps) (map_result (MAP (map_v remove_Gt_Geq)) ress)) ∧
  (∀env v pes res. evaluate_match' env v pes res ⇒ evaluate_match' env v (MAP (λ(p,e). (p,remove_Gt_Geq e)) pes) (map_result (map_v remove_Gt_Geq) res))` >- rw[] >>
  ho_match_mp_tac evaluate'_ind >>
  srw_tac[boolSimps.ETA_ss][remove_Gt_Geq_def,
  evaluate'_var,evaluate'_log,evaluate'_con]
*)

(*
``∀env exp res. evaluate' env exp res = evaluate' env (remove_mat_exp exp) res``

``∀env exp res cm vm nv ds dm dn. evaluate' env exp res ⇒
  Cevaluate
    (v_to_Cv o_f (env f_o_f (invert vm)))
    (exp_to_Cexp false cm <| m = vm; n = nv; ds = ds; dm = dm; dn = dn|>)
    (res_to_Cres res)``
*)

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
