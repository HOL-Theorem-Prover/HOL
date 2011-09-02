open bossLib Theory Parse res_quanTheory Defn Tactic boolLib
open finite_mapTheory listTheory pairTheory pred_setTheory
open set_relationTheory sortingTheory stringTheory wordsTheory
open MiniMLTheory

open lcsymtacs;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;

val _ = new_theory "miniMLProofs";

(* --------------------- Termination proofs -------------------------------- *)

val (lookup_def, lookup_ind) =
  tprove_no_defn ((lookup_def, lookup_ind), 
  WF_REL_TAC `measure (λ(x,y). LENGTH y)` >>
  rw []);
val _ = save_thm ("lookup_def", lookup_def);
val _ = save_thm ("lookup_ind", lookup_ind);

val (v_is_value_def, v_is_value_ind) =
  tprove_no_defn ((v_is_value_def, v_is_value_ind),
  wf_rel_tac 
  `inv_image $< (λx. case x of INL v -> v_size v || INR e -> exp_size e)` >>
  induct_on `es` >>
  rw [exp_size_def] >-
  decide_tac >>
  fs [IN_LIST_TO_SET] >>
  res_tac >>
  pop_assum (mp_tac o Q.SPEC `n`) >>
  decide_tac);
val _ = save_thm ("v_is_value_def", v_is_value_def);
val _ = save_thm ("v_is_value_ind", v_is_value_ind);

val (pmatch_def, pmatch_ind) =
  tprove_no_defn ((pmatch_def, pmatch_ind),
  wf_rel_tac 
  `inv_image $< (λx. case x of INL (a,p,b,c) -> pat_size p || INR (a,ps,b,c) ->
  pat1_size ps)`);
val _ = save_thm ("pmatch_def", pmatch_def);
val _ = save_thm ("pmatch_ind", pmatch_ind);

val (find_recfun_def, find_recfun_ind) =
  tprove_no_defn ((find_recfun_def, find_recfun_ind),
  WF_REL_TAC `measure (λ(x,y). LENGTH y)` >>
  rw []);
val _ = save_thm ("find_recfun_def", find_recfun_def);
val _ = save_thm ("find_recfun_ind", find_recfun_ind);

val (type_subst_def, type_subst_ind) =
  tprove_no_defn ((type_subst_def, type_subst_ind),
  WF_REL_TAC `measure (λ(x,y). t_size y)` >>
  rw [] >|
  [induct_on `ts` >>
       rw [t_size_def] >>
       res_tac >>
       decide_tac,
   decide_tac,
   decide_tac]);
val _ = save_thm ("type_subst_def", type_subst_def);
val _ = save_thm ("type_subst_ind", type_subst_ind);

(* ------------------------------------------------------------------------- *)

(* Prove that never gets stuck if there is still work to do (i.e., it must
 * detect all type errors *)

val untyped_safety_thm = Q.store_thm ("untyped_safety_thm",
`∀envC env ds st. 
  (d_step (envC, env, ds, st) = Stuck) = (ds = []) ∧ (st = NONE)`,
rw [d_step_def, e_step_def, continue_def, push_def] >>
cases_on `st` >>
rw [] >|
[cases_on `ds` >>
     rw [] >>
     cases_on `h` >>
     rw [],
 cases_on `x` >>
     rw [] >> 
     cases_on `r` >>
     rw [] >>
     cases_on `r'`>> 
     rw [] >>
     cases_on `r` >>
     rw [] >>
     cases_on `q'''` >>
     rw [] >|
     [cases_on `pmatch q' q v env` >>
          rw [],
      cases_on `v` >>
          rw [] >>
          cases_on `l` >>
          rw [] >>
          cases_on `lookup s q'` >>
          rw [] >>
          cases_on `x` >>
          rw [],
      cases_on `lookup s q''` >>
          rw []]]);

(* --------------------------- Type soundness ------------------------------- *)

(* Check that the dynamic and static constructor environments are consistent *)
val consistent_con_env_def = Define `
  (consistent_con_env [] [] = T) ∧
  (consistent_con_env ((cn, (n, ns))::envC) ((cn', ([], ts, tn))::tenvC) =
    (cn = cn') ∧
    (LENGTH ts = n) ∧
    cn IN ns ∧
    consistent_con_env envC tenvC) ∧
  (consistent_con_env _ _ = F)`;

(* Check that two constructors of the same type have the same set of all
 * constructors for that type *)
val consistent_con_env2_def = Define `
  consistent_con_env2 envC tenvC =
    (∀n1 n2 tvs1 tvs2 ts1 ts2 tn ns1 ns2 l1 l2. 
       (lookup n1 tenvC = SOME (tvs1,ts1,tn)) ∧
       (lookup n2 tenvC = SOME (tvs2,ts2,tn)) ∧
       (lookup n1 envC = SOME (l1,ns1)) ∧
       (lookup n2 envC = SOME (l2,ns2))
       ⇒
       (ns1 = ns2))`;

(* Everything in the type environment is also in the execution environment *)
val type_lookup_lem = Q.prove (
`∀tenvC env tenv v s t'.
  type_env tenvC env tenv ∧
  (lookup s tenv = SOME t')
  ⇒
  (∃v'. lookup s env = SOME v')`,
induct_on `env` >>
rw [Once type_e_cases, lookup_def, bind_def] >>
fs [lookup_def] >|
[CCONTR_TAC >>
     fs [] >>
     rw [] >>
     fs [lookup_def],
 rw [] >>
     fs [] >>
     metis_tac []]);

(* Constructors in their type environment are also in their execution
 * environment *)
val consistent_con_env_lem = Q.prove (
`∀envC tenvC. consistent_con_env envC tenvC ⇒
  (lookup cn tenvC = SOME (tvs, ts, tn)) ⇒
  (∃ns. (lookup cn envC = SOME (LENGTH ts, ns)) ∧ cn IN ns)`,
recInduct (fetch "-" "consistent_con_env_ind") >>
rw [lookup_def, consistent_con_env_def] >>
rw []);

val type_es_length_lem = Q.prove (
`∀tenvC tenv es ts.
  type_es tenvC tenv es ts ⇒ (LENGTH es = LENGTH ts)`,
induct_on `es` >>
rw [Once type_e_cases] >>
rw [] >>
metis_tac []);

val type_ps_length_lem = Q.prove (
`∀tenvC tenv ps ts tenv'.
  type_ps tenvC tenv ps ts tenv'⇒ (LENGTH ps = LENGTH ts)`,
induct_on `ps` >>
rw [Once type_p_cases] >>
rw [] >>
metis_tac []);

(* Typing lists of expressions from the end *)
val type_es_end_lem = Q.prove (
`∀tenvC tenv es ts e t.
  type_es tenvC tenv (es++[e]) (ts++[t]) =
  type_e tenvC tenv e t ∧
  type_es tenvC tenv es ts`,
induct_on `es` >>
rw [] >>
cases_on `ts` >>
fs [] >>
EQ_TAC >>
rw [] >|
[pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_e_cases]) >>
     fs [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_e_cases]) >>
     fs [],
 metis_tac [type_e_rules], 
 imp_res_tac type_es_length_lem >>
     fs [],
 imp_res_tac type_es_length_lem >>
     fs [],
 imp_res_tac type_es_length_lem >>
     fs [],
 imp_res_tac type_es_length_lem >>
     fs [],
 imp_res_tac type_es_length_lem >>
     fs [],
 imp_res_tac type_es_length_lem >>
     fs [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_e_cases]) >>
     fs [] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_e_cases]) >>
     fs [] >>
     metis_tac [type_e_rules],
 rw [Once type_e_cases] >>
     pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_e_cases]) >>
     fs []]);

(* Recursive functions have function type *)
val type_funs_Tfn = Q.prove (
`∀tenvC tenv funs tenv' t n.
  type_funs tenvC tenv funs tenv' ∧
  (lookup n tenv' = SOME t)
  ⇒
  ∃t1 t2. t = Tfn t1 t2`,
induct_on `funs` >>
rw [] >>
qpat_assum `type_funs tenvC tenv funspat tenv'` 
      (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
rw [] >>
fs [lookup_def, emp_def, bind_def] >>
cases_on `fn = n` >>
fs [] >>
metis_tac []);

(* Classifying values of basic types *)
val canonical_values_thm = Q.prove (
`∀tenvC tenv v t1 t2.
  (type_e tenvC tenv (Val v) Tnum ⇒ (∃n. v = Lit (Num n))) ∧
  (type_e tenvC tenv (Val v) Tbool ⇒ (∃n. v = Lit (Bool n))) ∧
  (type_e tenvC tenv (Val v) (Tfn t1 t2) ⇒ 
    (∃env n e. v = Closure env n e) ∨
    (∃env funs n. v = Recclosure env funs n))`,
rw [] >>
fs [Once type_e_cases] >>
rw [] >>
metis_tac [type_funs_Tfn, t_distinct]);

(* Well-typed pattern matches either match or not, but don't raise type errors
* *)
val pmatch_type_progress = Q.prove (
`(∀envC p v env t tenv tenv' tenv''.
  consistent_con_env envC tenvC ∧
  consistent_con_env2 envC tenvC ∧
  type_p tenvC tenv p t tenv' ∧
  type_e tenvC tenv'' (Val v) t ∧
  v_is_value v
  ⇒
  (pmatch envC p v env = No_match) ∨
  (∃env'. pmatch envC p v env = Match env')) ∧
 (∀envC ps es env ts tenv tenv' tenv''.
  consistent_con_env envC tenvC ∧
  consistent_con_env2 envC tenvC ∧
  type_ps tenvC tenv ps ts tenv' ∧
  type_es tenvC tenv'' es ts ∧
  (EVERY is_value es)
  ⇒
  (pmatch_list envC ps es env = No_match) ∨
  (∃env'. pmatch_list envC ps es env = Match env'))`,
HO_MATCH_MP_TAC pmatch_ind >>
rw [] >>
rw [pmatch_def] >>
fs [v_is_value_def, lit_same_type_def] >|
[fs [Once type_e_cases, Once type_p_cases, lit_same_type_def] >>
     rw [] >>
     fs [],
 fs [Once (hd (CONJUNCTS type_e_cases)), 
     Once (hd (CONJUNCTS type_p_cases))] >>
     rw [] >>
     fs [] >>
     imp_res_tac consistent_con_env_lem >>
     rw [] >>
     `EVERY is_value es` by fs [RES_FORALL, EVERY_MEM] >>
     metis_tac [type_ps_length_lem, type_es_length_lem, LENGTH_MAP],
 fs [Once type_p_cases, Once type_e_cases, consistent_con_env2_def] >>
     imp_res_tac consistent_con_env_lem >>
     rw [] >>
     res_tac >>
     fs [] >>
     rw [] >>
     metis_tac [type_ps_length_lem, type_es_length_lem, LENGTH_MAP],
 fs [Once type_e_cases, Once type_p_cases, lit_same_type_def] >>
     rw [] >>
     fs [],
 fs [Once type_e_cases, Once type_p_cases, lit_same_type_def] >>
     rw [] >>
     fs [],
 fs [Once type_e_cases, Once type_p_cases, lit_same_type_def] >>
     rw [] >>
     fs [] >>
     metis_tac [type_funs_Tfn, t_distinct],
 fs [Once type_e_cases, Once type_p_cases, lit_same_type_def] >>
     rw [] >>
     fs [],
 fs [Once type_e_cases, Once type_p_cases, lit_same_type_def] >>
     rw [] >>
     fs [],
  fs [Once type_e_cases, Once type_p_cases, lit_same_type_def] >>
     rw [] >>
     fs [] >>
     metis_tac [type_funs_Tfn, t_distinct],
 qpat_assum `type_ps tenvC tenv (p::ps) ts tenv'` 
         (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_p_cases]) >>
     qpat_assum `type_es tenvC tenv'' (e::es) ts` 
         (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
     fs [] >>
     rw [] >>
     res_tac >>
     fs [] >>
     metis_tac [],
 imp_res_tac type_ps_length_lem >>
     imp_res_tac type_es_length_lem >>
     fs [] >>
     cases_on `ts` >>
     fs [],
 imp_res_tac type_ps_length_lem >>
     imp_res_tac type_es_length_lem >>
     fs [] >>
     cases_on `ts` >>
     fs []]);

(* Recursive functions can be looked up in the execution environment. *)
val type_funs_lookup = Q.prove (
`∀fn env tenvC funs env' n e tenv.
  MEM (fn,n,e) funs ∧
  type_funs tenvC tenv funs env'
  ⇒
  (∃t. lookup fn env' = SOME t)`,
Induct_on `funs` >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
fs [] >>
fs [lookup_def, bind_def] >>
rw [] >>
metis_tac []);

(* Functions in the type environment can be found *)
val type_funs_lookup2 = Q.prove (
`∀fn env tenvC funs tenv' e tenv t.
  (lookup fn tenv' = SOME t) ∧
  type_funs tenvC tenv funs tenv'
  ⇒
  (∃n e. find_recfun fn funs = SOME (n,e))`,
Induct_on `funs` >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
fs [] >>
fs [lookup_def, bind_def, emp_def] >>
rw [Once find_recfun_def] >>
metis_tac []);

(* No duplicate function definitions in a single let rec *)
val type_funs_distinct = Q.prove (
`∀tenvC tenv funs tenv'.
  type_funs tenvC tenv funs tenv'
  ⇒
  ALL_DISTINCT (MAP (λ(x,y,z). x) funs)`,
induct_on `funs` >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
fs [] >>
rw [MEM_MAP] >|
[cases_on `y` >>
     cases_on `r` >>
     rw [] >>
     CCONTR_TAC >>
     fs [] >>
     rw [] >>
     metis_tac [type_funs_lookup, optionTheory.NOT_SOME_NONE],
 metis_tac []]);

(* A well-typed expression state is either a value with no continuation, or it
* can step to another state, or it steps to a BindError. *)
val exp_type_progress = Q.prove (
`∀tenvC tenv e t envC env c.
  consistent_con_env envC tenvC ∧
  consistent_con_env2 envC tenvC ∧
  type_state tenvC (envC, env, e, c) t ∧
  (e_step (envC, env, e, c) ≠ BindError) ∧
  ¬((c = []) ∧ is_value e)
  ⇒
  (∃env' e' c'. e_step (envC, env, e, c) = State (envC, env', e', c'))`,
rw [] >>
rw [e_step_def] >>
fs [type_state_cases, push_def] >>
cases_on `e` >>
fs [v_is_value_def] >>
rw [] >>
fs [] >|
[rw [continue_def] >>
     fs [Once type_ctxts_cases, type_ctxt_cases, return_def, push_def] >>
     rw [] >>
     imp_res_tac canonical_values_thm >>
     fs [] >>
     fs [] >|
     [imp_res_tac type_funs_lookup2 >>
          fs [],
      cases_on `op` >>
          fs [],
      cases_on `op` >>
          fs [],
      cases_on `op` >>
          fs [],
      cases_on `op` >>
          fs [],
      cases_on `op` >>
          fs [],
      cases_on `op` >>
          fs [],
      cases_on `op` >>
          fs [],
      cases_on `pes` >>
            rw [] >-
            fs [e_step_def, continue_def] >>
            fs [RES_FORALL] >>
            cases_on `h` >>
            fs [] >>
            rw [] >>
            qpat_assum `∀x. (x = (q,r)) ∨ P x ⇒ Q x` 
                     (MP_TAC o Q.SPEC `(q,r)`) >>
                rw [] >>
                `(pmatch envC q v env' = No_match) ∨
                 (∃env. pmatch envC q v env' = Match env)` by 
                            metis_tac [pmatch_type_progress] >>
                rw [],
      cases_on `es` >>
          rw []],
 fs [Once type_e_cases] >>
     rw [] >>
     fs [v_is_value_def] >>
     cases_on `es` >>
     fs [RES_FORALL] >>
     imp_res_tac consistent_con_env_lem >>
     rw [] >>
     imp_res_tac type_es_length_lem >>
     fs [],
 fs [Once type_e_cases] >>
     rw [] >>
     fs [lookup_def, bind_def] >>
     imp_res_tac type_lookup_lem >>
     fs [] >> 
     rw [] >>
     fs [] >>
     res_tac >>
     rw [],
 fs [Once type_e_cases] >>
     metis_tac [type_funs_distinct],
 fs [Once type_e_cases] >>
     rw [] >>
     fs [v_is_value_def] >>
     cases_on `es` >>
     fs [RES_FORALL] >>
     imp_res_tac consistent_con_env_lem >>
     rw [] >>
     imp_res_tac type_es_length_lem >>
     fs [],
 fs [Once type_e_cases] >>
     rw [] >>
     fs [lookup_def, bind_def] >>
     imp_res_tac type_lookup_lem >>
     fs [] >> 
     rw [] >>
     fs [] >>
     res_tac >>
     rw [],
 fs [Once type_e_cases] >>
     metis_tac [type_funs_distinct]]);

(* It doesn't matter what environment we use to type values, because they have
* no free variables. *)
val type_val_weaken_stengthen_lem = Q.prove (
`(∀(tenvC : tenvC) env e t.
  type_e tenvC env e t ⇒
  is_value e ⇒
  ∀env'. type_e tenvC env' e t) ∧
 (∀(tenvC : tenvC) env es ts.
  type_es tenvC env es ts ⇒ 
  (∀(e :: (set es)). is_value e) ⇒
  (∀env'. type_es tenvC env' es ts)) ∧
 (∀(tenvC : tenvC) env tenv.
  type_env tenvC env tenv ⇒ T) ∧
 (∀(tenvC : tenvC) env funs env'.
  type_funs tenvC env funs env' ⇒ T)`,
HO_MATCH_MP_TAC type_e_strongind >>
rw [v_is_value_def, RES_FORALL] >>
rw [Once type_e_cases] >>
metis_tac []);

(* They value of a binding in the execution environment has the type given by
* the type environment. *)
val type_lookup_lem2 = Q.prove (
`∀(tenvC:tenvC) env tenv v s t'.
  type_env tenvC env tenv ∧
  (lookup s tenv = SOME t') ∧
  (lookup s env = SOME v)
  ⇒ 
  v_is_value v ∧
  type_e tenvC tenv (Val v) t'`,
induct_on `env` >>
rw [] >>
fs [lookup_def] >>
rw [] >>
cases_on `tenv` >>
fs [] >-
fs [Once type_e_cases, bind_def] >>
fs [lookup_def] >>
cases_on `h` >>
cases_on `h'` >>
qpat_assum `type_env tenvC ((q,r)::env) ((q',r')::t)`
         (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_e_cases]) >>
fs [bind_def] >>
rw [] >>
fs [lookup_def] >>
cases_on `q = s` >>
fs [] >>
rw [] >>
metis_tac [type_val_weaken_stengthen_lem, v_is_value_def]);

(* A successful pattern match gives a binding environment with the type given by
* the pattern type checker *)
val pmatch_type_preservation = Q.prove (
`(∀envC p v env env' (tenvC:tenvC) tenv.
  (pmatch envC p v env = Match env') ∧
  (∃t. type_e tenvC tenv (Val v) t) ∧
  v_is_value v ∧
  type_env tenvC env tenv ⇒
  ∃tenv'. type_env tenvC env' tenv') ∧
 (∀envC ps es env env' (tenvC:tenvC) tenv.
  (pmatch_list envC ps es env = Match env') ∧
  (∃ts. type_es tenvC tenv es ts) ∧
  (∀(e :: (set es)). is_value e) ∧
  type_env tenvC env tenv ⇒
  ∃tenv'. type_env tenvC env' tenv')`,
HO_MATCH_MP_TAC pmatch_ind >>
rw [pmatch_def] >|
[qexists_tac `(n,t) :: tenv` >>
     rw [Once type_e_cases, bind_def] >>
     metis_tac [type_val_weaken_stengthen_lem, v_is_value_def],
 metis_tac [],
 cases_on `lookup n envC` >>
     fs [] >>
     cases_on `x` >>
     fs [] >>
     cases_on `n IN r ∧ n IN r ∧ (LENGTH ps = q) ∧ (LENGTH es = q)` >>
     fs [] >>
     fs [] >>
     qpat_assum `type_e tenvC tenv epat t`
             (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
     fs [] >>
     metis_tac [v_is_value_def, RES_FORALL],
 cases_on `lookup n envC` >>
     fs [] >>
     cases_on `x` >>
     fs [] >>
     cases_on `lookup n' envC` >>
     fs [] >>
     cases_on `x` >>
     fs [] >>
     cases_on `n IN r' ∧ n' IN r ∧ (LENGTH ps = q) ∧ (LENGTH es = q')` >>
     fs [] >>
     fs [],
 metis_tac [],
 cases_on `pmatch envC p v env` >>
     fs [] >>
     qpat_assum `type_es tenvC tenv (Val v::es) ts`
             (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_e_cases]) >>
     fs [RES_FORALL] >>
     metis_tac [v_is_value_def, RES_FORALL, 
                SIMP_RULE (srw_ss ()) [RES_FORALL] 
                          type_val_weaken_stengthen_lem]]);

val build_rec_env_help_lem = Q.prove (
`∀funs env funs'.
FOLDR (λ(f,x,e) env'. bind f (Recclosure env funs' f) env') env funs =
merge (MAP (λ(fn,n,e). (fn, (Recclosure env funs' fn))) funs) env`,
Induct >>
rw [merge_def, bind_def] >>
cases_on `h` >>
cases_on `r` >>
rw []);

(* Alternate definition for build_rec_env *)
val build_rec_env_lem = Q.prove (
`∀funs funs' env.
  build_rec_env funs env = 
  merge (MAP (λ(fn,n,e). (fn, (Recclosure env funs fn))) funs) env`,
rw [build_rec_env_def, build_rec_env_help_lem]);

val type_env_merge_lem = Q.prove (
`∀tenvC env env' tenv tenv'.
  type_env tenvC env' tenv' ∧ type_env tenvC env tenv
  ⇒
  type_env tenvC (merge env' env) (merge tenv' tenv)`,
Induct_on `env'` >>
rw [merge_def] >>
cases_on `tenv'`>>
fs [] >>
rw [Once type_e_cases] >|
[qpat_assum `type_env tenvC [] (h::t)`
         (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
     fs [bind_def],
 qpat_assum `type_env tenvC (h::env') []`
         (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
     fs [bind_def],
 qpat_assum `type_env tenvC (h::env') (h'::t)`
         (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
     fs [bind_def, merge_def] >>
     rw []]);

val type_recfun_lookup = Q.prove (
`∀fn funs n e tenvC tenv tenv' t1 t2.
  (find_recfun fn funs = SOME (n,e)) ∧
  type_funs tenvC tenv funs tenv' ∧
  (lookup fn tenv' = SOME (Tfn t1 t2))
  ⇒
  type_e tenvC (bind n t1 tenv) e t2`,
induct_on `funs` >>
rw [Once find_recfun_def] >>
qpat_assum `type_funs tenvC tenv (h::funs) tenv'` 
            (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_e_cases]) >>
rw [] >>
fs [] >>
cases_on `fn' = fn` >>
fs [lookup_def, bind_def] >>
rw [] >>
metis_tac []);

val type_recfun_env_help = Q.prove (
`∀fn funs funs' tenvC tenv tenv' tenv0 env.
  (!fn t. (lookup fn tenv = SOME t) ⇒ (lookup fn tenv' = SOME t)) ∧
  type_env tenvC env tenv0 ∧
  type_funs tenvC (merge tenv' tenv0) funs' tenv' ∧
  type_funs tenvC (merge tenv' tenv0) funs tenv
  ⇒
  type_env tenvC (MAP (λ(fn,n,e). (fn,Recclosure env funs' fn)) funs) tenv`,
induct_on `funs` >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_e_cases]) >>
fs [emp_def] >>
rw [bind_def, Once type_e_cases, v_is_value_def] >|
[rw [Once type_e_cases] >>
     metis_tac [lookup_def, bind_def],
 metis_tac [optionTheory.NOT_SOME_NONE, lookup_def, bind_def]]);

val type_recfun_env = Q.prove (
`∀fn funs tenvC tenv tenv0 env.
  type_env tenvC env tenv0 ∧
  type_funs tenvC (merge tenv tenv0) funs tenv
  ⇒
  type_env tenvC (MAP (λ(fn,n,e). (fn,Recclosure env funs fn)) funs) tenv`,
metis_tac [type_recfun_env_help]);

(* If a step can be taken from a well-typed state, the resulting state has the
* same type *)
val exp_type_preservation = Q.prove (
`∀(tenvC:tenvC) envC env e c t env' e' c'.
  type_state tenvC (envC, env, e, c) t ∧
  (e_step (envC, env, e, c) = State (envC, env', e', c'))
  ⇒
  type_state tenvC (envC, env', e', c') t`,
rw [type_state_cases] >>
fs [e_step_def] >>
cases_on `e` >>
fs [v_is_value_def, push_def] >>
rw [] >|
[cases_on `v_is_value v` >>
     fs [] >|
     [fs [continue_def] >>
          cases_on `c` >>
          fs [push_def] >>
          cases_on `h` >>
          fs [] >>
          cases_on `q` >>
          fs [] >|
          [cases_on `o'` >>
               fs [] >>
               cases_on `v` >>
               fs [] >|
               [fs [Once type_ctxts_cases, type_ctxt_cases] >>
                    rw [] >>
                    metis_tac [type_val_weaken_stengthen_lem, v_is_value_def],
                qpat_assum `type_ctxts tenvC (cpat::t') t1 t`
                           (ASSUME_TAC o 
                            SIMP_RULE (srw_ss()) [Once type_ctxts_cases]) >> 
                    fs [type_ctxt_cases] >>
                    rw [Once type_ctxts_cases, type_ctxt_cases] >>
                    qpat_assum `type_e tenvC tenv epat tpat`
                           (ASSUME_TAC o 
                            SIMP_RULE (srw_ss()) [Once type_e_cases]) >> 
                    metis_tac []],
           cases_on `o'` >>
               fs [] >>
               qpat_assum `type_ctxts tenvC ((Capp2 l s e (),r)::c') t1 t`
                 (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_ctxts_cases]) >> 
               fs [type_ctxt_cases] >>
               qpat_assum `type_e tenvC tenv' (Val (Closure l s e)) (Tfn t1 t2)`
                   (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >> 
               rw [] >>
               metis_tac [type_e_rules, v_is_value_def, 
                          type_val_weaken_stengthen_lem, bind_def],
           cases_on `o'` >>
               fs [] >>
               cases_on `find_recfun s l0` >>
               fs [] >>
               cases_on `x` >>
               fs [] >>
               qpat_assum `type_ctxts tenvC ((Capp3 l l0 s (),r)::c') t1 t`
                 (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_ctxts_cases]) >> 
               fs [type_ctxt_cases] >>
               rw [build_rec_env_lem] >>

               imp_res_tac type_recfun_lookup >>
               qexists_tac `t2` >>
               qexists_tac `(bind q t1 (merge tenv''' tenv''))` >>
               rw [] >>
               rw [Once type_e_cases, bind_def] >-
               metis_tac [type_val_weaken_stengthen_lem, v_is_value_def] >>
               match_mp_tac type_env_merge_lem >>
               rw [] >>
               metis_tac [type_recfun_env],
           cases_on `o'` >>
               fs [] >>
               cases_on `v` >>
               fs [return_def] >>
               cases_on `l` >>
               cases_on `l'` >>
               fs [] >>
               cases_on `b` >>
               fs []>>
               qpat_assum `type_ctxts tenvC cpat t1 t`
                 (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_ctxts_cases]) >> 
               fs [type_ctxt_cases] >>
               rw [] >>
               metis_tac [type_val_weaken_stengthen_lem, v_is_value_def],
           cases_on `o0` >> 
               fs [] >>
               rw [] >>
               fs [Once type_ctxts_cases, type_ctxt_cases] >>
               metis_tac [type_val_weaken_stengthen_lem, v_is_value_def],
           cases_on `o0` >>
               fs [] >>
               cases_on `v'` >>
               fs [return_def] >>
               cases_on `v` >>
               fs [] >>
               cases_on `l` >>
               fs [] >>
               cases_on `l'` >>
               fs [] >>
               cases_on `o'` >>
               fs [] >>
               qpat_assum `type_ctxts tenvC cpat t1 t`
                 (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_ctxts_cases]) >> 
               fs [type_ctxt_cases] >> 
               metis_tac [type_e_rules],
           cases_on `o'` >>
               fs [] >>
               cases_on `v` >>
               fs [] >>
               cases_on `l` >>
               fs [] >>
               cases_on `b` >>
               fs [] >>
               qpat_assum `type_ctxts tenvC cpat t1 t`
                 (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_ctxts_cases]) >> 
               fs [type_ctxt_cases] >>
               rw [] >>
               metis_tac [],
           cases_on `o'` >>
               fs [] >>
               cases_on `l` >>
               fs [] >>
               cases_on `h` >>
               fs [] >>
               cases_on `pmatch envC q v r` >>
               fs [] >>
               rw [] >>
               qpat_assum `type_ctxts tenvC cpat t1 t`
                 (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_ctxts_cases]) >> 
               fs [type_ctxt_cases, RES_FORALL, FORALL_PROD] >>
               rw [] >|
               [rw [Once type_ctxts_cases, type_ctxt_cases, RES_FORALL,
                    FORALL_PROD] >>
                    metis_tac [type_val_weaken_stengthen_lem, v_is_value_def],
                metis_tac [type_val_weaken_stengthen_lem, v_is_value_def,
                           pmatch_type_preservation]],
           cases_on `o'` >>
               fs [] >>
               qpat_assum `type_ctxts tenvC cpat t1 t`
                 (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_ctxts_cases]) >> 
               fs [type_ctxt_cases] >>
               rw [] >>
               qexists_tac `t2` >>
               qexists_tac `bind s t1 tenv'` >>
               rw [] >>
               rw [Once type_e_cases, bind_def] >>
               metis_tac [type_val_weaken_stengthen_lem, v_is_value_def],
           cases_on `o'` >>
               fs [] >>
               cases_on `l0` >>
               fs [return_def] >>                 
               rw [] >|
               [qpat_assum `type_ctxts tenvC cpat t1 t`
                 (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_ctxts_cases]) >> 
                    fs [type_ctxt_cases] >>
                    qexists_tac `t2` >>
                    qexists_tac `tenv'` >>
                    rw [] >>
                    rw [Once type_e_cases] >>
                    imp_res_tac type_es_length_lem >>
                    fs [] >>
                    `ts2 = []` by 
                            (cases_on `ts2` >>
                             fs []) >>
                    rw [type_es_end_lem] >>
                    metis_tac [type_val_weaken_stengthen_lem, v_is_value_def],
                fs [type_ctxt_cases, Once type_ctxts_cases] >>
                    rw [] >>
                    qpat_assum `type_es tenvC tenv' (e'::t'') ts2`
                          (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >> 
                    fs [RES_FORALL] >>
                    rw [] >>
                    qexists_tac `t''''` >>
                    qexists_tac `tenv'` >>
                    rw [] >>
                    qexists_tac `tenv'` >>
                    qexists_tac `Tapp ts' tn` >>
                    rw [] >>
                    cases_on `ts2` >>
                    fs [] >>
                    rw [] >>
                    qexists_tac `ts1++[t''']` >>
                    qexists_tac `t'''''` >>
                    rw [] >>
                    metis_tac [type_es_end_lem, type_val_weaken_stengthen_lem,
                               v_is_value_def]]],
      cases_on `v` >>
          fs [] >>
          cases_on `l` >>
          fs [] >>
          cases_on `lookup s envC` >>
          fs [] >>
          cases_on `x` >>
          fs [] >>
          cases_on `q = SUC (LENGTH t')` >>
          fs [] >>
          rw [] >>
          qpat_assum `type_e tenvC tenv (Val (Con s (e'::t'))) t1` 
                   (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >> 
          rw [] >>
          qpat_assum `type_es tenvC tenv (e'::t') ts` 
                   (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >> 
          rw [Once type_ctxts_cases, type_ctxt_cases, RES_FORALL] >>
          qexists_tac `t''`>>
          qexists_tac `tenv`>>
          rw [] >>
          qexists_tac `tenv`>>
          qexists_tac `Tapp ts' tn`>>
          rw [] >>
          cases_on `ts` >>
          fs [] >>
          rw [] >>
          qexists_tac `[]` >>
          qexists_tac `t'''` >>
          rw [] >>
          metis_tac [type_e_rules, APPEND]],
 cases_on `lookup s env` >>
     fs [] >>
     rw [] >>
     qexists_tac `t1` >>
     qexists_tac `tenv` >>
     rw [] >>
     qpat_assum `type_e tenvC tenv (Var s) t1` 
              (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >> 
     metis_tac [type_lookup_lem2],
 fs [Once (hd (CONJUNCTS type_e_cases))] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >> 
     rw [Once type_ctxts_cases, type_ctxt_cases] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >> 
     rw [Once type_ctxts_cases, type_ctxt_cases] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >> 
     rw [Once type_ctxts_cases, type_ctxt_cases] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >> 
     rw [Once type_ctxts_cases, type_ctxt_cases] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >> 
     rw [Once type_ctxts_cases, type_ctxt_cases] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >> 
     rw [Once type_ctxts_cases, type_ctxt_cases] >>
     metis_tac [],
 cases_on `¬ALL_DISTINCT (MAP (λ(x,y,z). x) l)` >>
     fs [] >>
     rw [] >>
     qpat_assum `type_e tenvC tenv epat t1`
            (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
     fs [] >>
     qexists_tac `t1` >>
     qexists_tac `merge tenv' tenv` >>
     rw [] >>
     rw [build_rec_env_lem] >>
         match_mp_tac type_env_merge_lem >>
         rw [] >>
         match_mp_tac type_recfun_env >>
         metis_tac []]);

(* ------------------------- Big step determinacy ----------------------- *)

val big_exp_determ = Q.prove (
`(∀ envc env e bv1.
   evaluate envc env e bv1 ⇒
   ∀ bv2. evaluate envc env e bv2 ⇒
   (bv1 = bv2)) ∧
 (∀ envc env es bv1.
   evaluate_list envc env es bv1 ⇒
   ∀ bv2. evaluate_list envc env es bv2 ⇒
   (bv1 = bv2)) ∧
 (∀ envc env v pes bv1.
   evaluate_match envc env v pes bv1 ⇒
   ∀ bv2. evaluate_match envc env v pes bv2 ⇒
   (bv1 = bv2))`,
HO_MATCH_MP_TAC evaluate_ind >>
rw [] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases]) >>
fs [] >>
rw [] >>
fs [] >>
res_tac >>
fs [] >>
rw []);

val _ = export_theory ();
