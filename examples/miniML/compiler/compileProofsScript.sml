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

(* move elsewhere? *)
val free_vars_def = tDefine "free_vars"`
  (free_vars (Var x) = {x})
∧ (free_vars (Let x _ b) = free_vars b DELETE x)
∧ (free_vars (Letrec ls b) = FOLDL (λs (n,x,b). s ∪ (free_vars b DELETE x))
                             (free_vars b DIFF (FOLDL (combin$C ($INSERT o FST)) {} ls))
                             ls)
∧ (free_vars (Fun x b) = free_vars b DELETE x)
∧ (free_vars (App _ e1 e2) = free_vars e1 ∪ free_vars e2)
∧ (free_vars (Log _ e1 e2) = free_vars e1 ∪ free_vars e2)
∧ (free_vars (If e1 e2 e3) = free_vars e1 ∪ free_vars e2 ∪ free_vars e3)
∧ (free_vars (Mat e pes) = free_vars e ∪ FOLDL (λs (p,e). s ∪ free_vars e) {} pes)
∧ (free_vars (Proj e _) = free_vars e)
∧ (free_vars (Raise _) = {})
∧ (free_vars (Val _) = {})
∧ (free_vars (Con _ es) = FOLDL (λs e. s ∪ free_vars e) {} es)`
(WF_REL_TAC `measure exp_size` >>
srw_tac [ARITH_ss][exp1_size_thm,exp6_size_thm,exp8_size_thm] >>
imp_res_tac SUM_MAP_MEM_bound >|
  map (fn q => pop_assum (qspec_then q mp_tac))
  [`exp2_size`,`exp7_size`,`exp_size`] >>
srw_tac[ARITH_ss][exp_size_def])

val (remove_ctors_def,remove_ctors_ind) =
  tprove_no_defn ((remove_ctors_def,remove_ctors_ind),
  WF_REL_TAC
  `inv_image $< (\x. case x of INL (x,y) => exp_size y
                         | INR (INL (x,y)) => v_size y
                         | INR (INR (INL (x,y))) => exp3_size y
                         | INR (INR (INR (INL (x,y)))) => exp1_size y
                         | INR (INR (INR (INR (x,y)))) => exp6_size y)` >>
  rw [] >>
  TRY decide_tac >>
  rw[exp8_size_thm,exp9_size_thm] >>
  qmatch_rename_tac `f a < (X:num)` ["X"] >>
  Q.ISPECL_THEN [`f`,`a`] mp_tac SUM_MAP_MEM_bound >>
  disch_then imp_res_tac >>
  DECIDE_TAC)
val _ = save_thm ("remove_ctors_def", remove_ctors_def);
val _ = save_thm ("remove_ctors_ind", remove_ctors_ind);

val (remove_mat_vp_def,remove_mat_vp_ind) =
  tprove_no_defn ((remove_mat_vp_def,remove_mat_vp_ind),
  WF_REL_TAC
  `inv_image $<
    (λx. case x of
         | INL (v,p) => pat_size p
         | INR (v,n,ps) => pat1_size ps)`)
val _ = save_thm ("remove_mat_vp_def", remove_mat_vp_def);
val _ = save_thm ("remove_mat_vp_ind", remove_mat_vp_ind);

val (remove_mat_def,remove_mat_ind) =
  tprove_no_defn ((remove_mat_def,remove_mat_ind),
  WF_REL_TAC
  `inv_image $<
    (λx. case x of
         | INL e => exp_size e
         | INR (v,pes) => exp6_size pes)` >>
  srw_tac[ARITH_ss][exp1_size_thm,exp8_size_thm] >>
  imp_res_tac SUM_MAP_MEM_bound >|
    map (fn q => pop_assum (qspec_then q mp_tac))
    [`exp2_size`,`exp_size`] >>
  srw_tac[ARITH_ss][exp_size_def])
val _ = save_thm ("remove_mat_def", remove_mat_def);
val _ = save_thm ("remove_mat_ind", remove_mat_ind);

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

(*
This is too awful! TODO: Try a simpler definition of fold_consts.
val (fold_consts_def,fold_consts_ind) =
  tprove_no_defn ((fold_consts_def,fold_consts_ind),
  WF_REL_TAC
  `inv_image $< (λx. case x of
                     | INL x => exp_size x
                     | INR (INL x) => v_size x
                     | INR (INR (INL x)) => exp3_size x
                     | INR (INR (INR (INL x))) => exp1_size x
                     | INR (INR (INR (INR (INL x)))) => 1 + exp6_size x
                     | INR (INR (INR (INR (INR (_,x))))) => exp6_size x)` >>
  fs [Once fold_consts_UNION_AUX_def]
*)

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

(* TODO: move to evaluateEquations *)
val evaluate'_raise = store_thm(
"evaluate'_raise",
``∀env err r. evaluate' env (Raise err) r = (r = Rerr (Rraise err))``,
rw [Once evaluate'_cases])

val evaluate'_val = store_thm(
"evaluate'_val",
``∀env v r. evaluate' env (Val v) r = (r = Rval v)``,
rw [Once evaluate'_cases])

val evaluate'_fun = store_thm(
"evaluate'_fun",
``∀env n e r. evaluate' env (Fun n e) r = (r = Rval (Closure env n e))``,
rw [Once evaluate'_cases])

val _ = export_rewrites["evaluate'_raise","evaluate'_val","evaluate'_fun"]

val evaluate'_con = store_thm(
"evaluate'_con",
``∀env cn es r. evaluate' env (Con cn es) r =
  (∃err. evaluate_list' env es (Rerr err) ∧ (r = Rerr err)) ∨
  (∃vs. evaluate_list' env es (Rval vs) ∧ (r = Rval (Conv cn vs)))``,
rw [Once evaluate'_cases] >>
metis_tac [])

val evaluate'_var = store_thm(
"evaluate'_var",
``∀env n r. evaluate' env (Var n) r =
  (∃v. (lookup n env = SOME v) ∧ (r = Rval v)) ∨
  ((lookup n env = NONE) ∧ (r = Rerr Rtype_error))``,
rw [Once evaluate'_cases] >>
metis_tac [])

val evaluate_list'_thm = store_thm(
"evaluate_list'_thm",
``∀env r.
  (evaluate_list' env [] r = (r = Rval [])) ∧
  (∀e es. evaluate_list' env (e::es) r =
   (∃v vs. evaluate' env e (Rval v) ∧ evaluate_list' env es (Rval vs) ∧
           (r = Rval (v::vs))) ∨
   (∃err. evaluate' env e (Rerr err) ∧
          (r = Rerr err)) ∨
   (∃v err. evaluate' env e (Rval v) ∧ evaluate_list' env es (Rerr err) ∧
            (r = Rerr err)))``,
rw[] >-
  rw[Once evaluate'_cases] >>
rw[EQ_IMP_THM] >- (
  pop_assum (mp_tac o (SIMP_RULE (srw_ss()) [Once evaluate'_cases])) >>
  rw [] >> metis_tac[] )
>- rw [evaluate'_rules]
>- rw [evaluate'_rules] >>
rw[Once evaluate'_cases] >>
metis_tac [])

val evaluate'_app = store_thm(
"evaluate'_app",
``∀env op e1 e2 r. evaluate' env (App op e1 e2) r =
  (∃v1 v2 env' e. evaluate' env e1 (Rval v1) ∧ (evaluate' env e2 (Rval v2)) ∧
                  (do_app env op v1 v2 = SOME (env',e)) ∧
                  evaluate' env' e r) ∨
  (∃v1 v2. evaluate' env e1 (Rval v1) ∧ (evaluate' env e2 (Rval v2)) ∧
           (do_app env op v1 v2 = NONE) ∧
           (r = Rerr Rtype_error)) ∨
  (∃v1 err. evaluate' env e1 (Rval v1) ∧ (evaluate' env e2 (Rerr err)) ∧
            (r = Rerr err)) ∨
  (∃err. evaluate' env e1 (Rerr err) ∧
         (r = Rerr err))``,
rw[Once evaluate'_cases] >>
metis_tac []);

(*
val _ = augment_srw_ss[rewrites[evaluate_raise,evaluate_val,evaluate_list_val]]
*)

(* TODO: add to terminationProofsTheory? *)
val _ = augment_srw_ss[rewrites[lookup_def]]

(* Prove compiler phases preserve semantics *)

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

(* TODO: move to listTheory (and rich_listTheory) *)
val FOLDR_MAP = store_thm("FOLDR_MAP",
    (--`!f e g l.
       FOLDR f e (MAP g l) = FOLDR (\x y. f (g x) y) e l`--),
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN Induct
    THEN ASM_REWRITE_TAC[FOLDL,MAP,FOLDR] THEN BETA_TAC
    THEN REWRITE_TAC[]);

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

val _ = export_theory ()
