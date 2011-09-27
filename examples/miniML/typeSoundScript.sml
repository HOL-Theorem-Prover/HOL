open bossLib Theory Parse res_quanTheory Defn Tactic boolLib;
open finite_mapTheory listTheory pairTheory pred_setTheory;
open set_relationTheory sortingTheory stringTheory wordsTheory;
open relationTheory;
open MiniMLTheory;
open miniMLProofsTheory;

open lcsymtacs;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;

val _ = new_theory "typeSound";

(* Check that the dynamic and static constructor environments are consistent *)
val consistent_con_env_def = Define `
  (consistent_con_env [] [] = T) ∧
  (consistent_con_env ((cn, (n, ns))::envC) ((cn', (tvs, ts, tn))::tenvC) =
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
rw [Once type_v_cases, lookup_def, bind_def] >>
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

val consistent_con_env_lem2 = Q.prove (
`∀envC tenvC. consistent_con_env envC tenvC ⇒
  (lookup cn tenvC = NONE) ⇒
  (lookup cn envC = NONE)`,
recInduct (fetch "-" "consistent_con_env_ind") >>
rw [lookup_def, consistent_con_env_def] >>
rw []);

val type_es_length_lem = Q.prove (
`∀tenvC tenv es ts.
  type_es tenvC tenv es ts ⇒ (LENGTH es = LENGTH ts)`,
induct_on `es` >>
rw [Once type_v_cases] >>
rw [] >>
metis_tac []);

val type_vs_length_lem = Q.prove (
`∀tenvC vs ts.
  type_vs tenvC vs ts ⇒ (LENGTH vs = LENGTH ts)`,
induct_on `vs` >>
rw [Once type_v_cases] >>
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
[pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     fs [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     fs [],
 metis_tac [type_v_rules], 
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
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     fs [] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     fs [] >>
     metis_tac [type_v_rules],
 rw [Once type_v_cases] >>
     pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     fs []]);

(* Typing lists of expressions from the end *)
val type_vs_end_lem = Q.prove (
`∀tenvC vs ts v t.
  type_vs tenvC (vs++[v]) (ts++[t]) =
  type_v tenvC v t ∧
  type_vs tenvC vs ts`,
induct_on `vs` >>
rw [] >>
cases_on `ts` >>
fs [] >>
EQ_TAC >>
rw [] >|
[pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     fs [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     fs [],
 metis_tac [type_v_rules], 
 imp_res_tac type_vs_length_lem >>
     fs [],
 imp_res_tac type_vs_length_lem >>
     fs [],
 imp_res_tac type_vs_length_lem >>
     fs [],
 imp_res_tac type_vs_length_lem >>
     fs [],
 imp_res_tac type_vs_length_lem >>
     fs [],
 imp_res_tac type_vs_length_lem >>
     fs [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     fs [] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     fs [] >>
     metis_tac [type_v_rules],
 rw [Once type_v_cases] >>
     pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
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
      (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
rw [] >>
fs [lookup_def, emp_def, bind_def] >>
cases_on `fn = n` >>
fs [] >>
metis_tac []);

(* Classifying values of basic types *)
val canonical_values_thm = Q.prove (
`∀tenvC v t1 t2.
  (type_v tenvC v Tnum ⇒ (∃n. v = Lit (Num n))) ∧
  (type_v tenvC v Tbool ⇒ (∃n. v = Lit (Bool n))) ∧
  (type_v tenvC v (Tfn t1 t2) ⇒ 
    (∃env n e. v = Closure env n e) ∨
    (∃env funs n. v = Recclosure env funs n))`,
rw [] >>
fs [Once type_v_cases] >>
rw [] >>
metis_tac [type_funs_Tfn, t_distinct]);

(* Well-typed pattern matches either match or not, but don't raise type errors
* *)
val pmatch_type_progress = Q.prove (
`(∀envC p v env t tenv tenv'.
  consistent_con_env envC tenvC ∧
  consistent_con_env2 envC tenvC ∧
  type_p tenvC tenv p t tenv' ∧
  type_v tenvC v t
  ⇒
  (pmatch envC p v env = No_match) ∨
  (∃env'. pmatch envC p v env = Match env')) ∧
 (∀envC ps vs env ts tenv tenv'.
  consistent_con_env envC tenvC ∧
  consistent_con_env2 envC tenvC ∧
  type_ps tenvC tenv ps ts tenv' ∧
  type_vs tenvC vs ts
  ⇒
  (pmatch_list envC ps vs env = No_match) ∨
  (∃env'. pmatch_list envC ps vs env = Match env'))`,
HO_MATCH_MP_TAC pmatch_ind >>
rw [] >>
rw [pmatch_def] >>
fs [lit_same_type_def] >|
[fs [Once type_v_cases, Once type_p_cases, lit_same_type_def] >>
     rw [] >>
     fs [],
 fs [Once (hd (CONJUNCTS type_v_cases)), 
     Once (hd (CONJUNCTS type_p_cases))] >>
     rw [] >>
     fs [] >>
     imp_res_tac consistent_con_env_lem >>
     rw [] >>
     metis_tac [type_ps_length_lem, type_vs_length_lem, LENGTH_MAP],
 fs [Once type_p_cases, Once type_v_cases, consistent_con_env2_def] >>
     imp_res_tac consistent_con_env_lem >>
     rw [] >>
     res_tac >>
     fs [] >>
     rw [] >>
     metis_tac [type_ps_length_lem, type_vs_length_lem, LENGTH_MAP],
 fs [Once type_v_cases, Once type_p_cases, lit_same_type_def] >>
     rw [] >>
     fs [],
 fs [Once type_v_cases, Once type_p_cases, lit_same_type_def] >>
     rw [] >>
     fs [],
 fs [Once type_v_cases, Once type_p_cases, lit_same_type_def] >>
     rw [] >>
     fs [] >>
     metis_tac [type_funs_Tfn, t_distinct],
 fs [Once type_v_cases, Once type_p_cases, lit_same_type_def] >>
     rw [] >>
     fs [],
 fs [Once type_v_cases, Once type_p_cases, lit_same_type_def] >>
     rw [] >>
     fs [],
  fs [Once type_v_cases, Once type_p_cases, lit_same_type_def] >>
     rw [] >>
     fs [] >>
     metis_tac [type_funs_Tfn, t_distinct],
 qpat_assum `type_ps tenvC tenv (p::ps) ts tenv'` 
         (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_p_cases]) >>
     qpat_assum `type_vs tenvC (v::vs) ts` 
         (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
     fs [] >>
     rw [] >>
     res_tac >>
     fs [] >>
     metis_tac [],
 imp_res_tac type_ps_length_lem >>
     imp_res_tac type_vs_length_lem >>
     fs [] >>
     cases_on `ts` >>
     fs [],
 imp_res_tac type_ps_length_lem >>
     imp_res_tac type_vs_length_lem >>
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
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
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
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
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
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
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

val type_op_cases = Q.prove (
`!op t1 t2 t3.
  type_op op t1 t2 t3 =
  ((∃op'. op = Opn op') ∧ (t1 = Tnum) ∧ (t2 = Tnum) ∧ (t3 = Tnum)) ∨
  ((∃op'. op = Opb op') ∧ (t1 = Tnum) ∧ (t2 = Tnum) ∧ (t3 = Tbool)) ∨
  ((op = Opapp) ∧ (t1 = Tfn t2 t3))`,
rw [type_op_def] >>
every_case_tac >>
fs [] >>
metis_tac []);

val type_e_val = Q.prove (
`!cenv tenv v t.
  type_e cenv tenv (Val v) t = type_v cenv v t`,
rw [Once type_v_cases]);

val type_es_val = Q.prove (
`!cenv tenv vs ts.
  type_es cenv tenv (MAP Val vs) ts = type_vs cenv vs ts`,
induct_on `vs` >>
rw [] >>
rw [Once (hd (tl (tl (tl (CONJUNCTS type_v_cases)))))] >>
rw [Once (hd (tl (tl (CONJUNCTS type_v_cases))))] >>
fs [] >>
cases_on `ts` >>
fs [] >>
rw [type_e_val]);
 
val final_state_def = Define `
  (final_state (tenvC,env,Val v,[]) = T) ∧
  (final_state (tenvC,env,Raise err,[]) = T) ∧
  (final_state _ = F)`;

val not_final_state = Q.prove (
`!tenvC env e c.
  ¬final_state (tenvC,env,e,c) = 
     (?x y. c = x::y) ∨
     (?cn es. e = Con cn es) ∨ 
     (?v. e = Var v) ∨
     (?x e'. e = Fun x e') \/
     (?op e1 e2. e = App op e1 e2) ∨
     (?op e1 e2. e = Log op e1 e2) ∨
     (?e1 e2 e3. e = If e1 e2 e3) ∨
     (?e' pes. e = Mat e' pes) ∨
     (?n e1 e2. e = Let n e1 e2) ∨
     (?funs e'. e = Letrec funs e')`,
rw [] >>
cases_on `e` >>
cases_on `c` >>
rw [final_state_def]);

(* A well-typed expression state is either a value with no continuation, or it
* can step to another state, or it steps to a BindError. *)
val exp_type_progress = Q.prove (
`∀tenvC tenv e t envC env c.
  consistent_con_env envC tenvC ∧
  consistent_con_env2 envC tenvC ∧
  type_state tenvC (envC, env, e, c) t ∧
  ¬(final_state (envC, env, e, c))
  ⇒
  (∃env' e' c'. e_step (envC, env, e, c) = Estep (envC, env', e', c'))`,
rw [] >>
rw [e_step_def] >>
fs [type_state_cases, push_def, return_def] >>
cases_on `e` >>
fs [] >>
rw [] >>
fs [final_state_def] >|
[cases_on `c` >>
     fs [final_state_def],
 rw [continue_def] >>
     fs [Once type_ctxts_cases, type_ctxt_cases, return_def, push_def] >>
     rw [] >>
     fs [final_state_def] >>
     fs [type_e_val] >>
     fs [type_op_cases] >>
     rw [] >>
     imp_res_tac canonical_values_thm >>
     fs [] >>
     rw [] >>
     fs [do_app_def, do_if_def, do_log_def] >|
     [every_case_tac >>
          fs [] >>
          qpat_assum `type_v tenvC (Recclosure x1 x2 x3) tpat`
                (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
          fs [] >>
          imp_res_tac type_funs_lookup2 >>
          fs [],
      every_case_tac >>
          fs [],
      every_case_tac >>
          fs [],
      every_case_tac >>
          fs [RES_FORALL] >>
          rw [] >>
          qpat_assum `∀x. (x = (q,r)) ∨ P x ⇒ Q x` 
                   (MP_TAC o Q.SPEC `(q,r)`) >>
              rw [] >>
              CCONTR_TAC >>
              fs [] >>
              `(pmatch envC q v env' = No_match) ∨
               (∃env. pmatch envC q v env' = Match env)` by 
                          metis_tac [pmatch_type_progress] >>
              fs [],
      every_case_tac >>
         fs [] >>
         imp_res_tac consistent_con_env_lem >>
         imp_res_tac type_es_length_lem >>
         full_simp_tac (srw_ss()++ARITH_ss) [do_con_check_def],
      every_case_tac >>
         fs [] >>
         imp_res_tac consistent_con_env_lem >>
         imp_res_tac type_es_length_lem >>
         full_simp_tac (srw_ss()++ARITH_ss) [do_con_check_def]],
 fs [Once type_v_cases] >>
     rw [] >>
     fs [] >>
     imp_res_tac consistent_con_env_lem >>
     rw [] >>
     every_case_tac >>
     fs [return_def] >>
     imp_res_tac type_es_length_lem >>
     fs [],
 fs [do_con_check_def] >>
     fs [Once type_v_cases] >>
     rw [] >>
     fs [] >>
     imp_res_tac consistent_con_env_lem >>
     rw [] >>
     every_case_tac >>
     fs [return_def] >>
     imp_res_tac type_es_length_lem >>
     fs [],
 fs [Once type_v_cases] >>
     rw [] >>
     fs [lookup_def, bind_def] >>
     imp_res_tac type_lookup_lem >>
     fs [] >> 
     rw [] >>
     fs [] >>
     res_tac >>
     rw [],
 fs [Once type_v_cases] >>
     metis_tac [type_funs_distinct]]);

(* They value of a binding in the execution environment has the type given by
* the type environment. *)
val type_lookup_lem2 = Q.prove (
`∀(tenvC:tenvC) env tenv v s t'.
  type_env tenvC env tenv ∧
  (lookup s tenv = SOME t') ∧
  (lookup s env = SOME v)
  ⇒ 
  type_e tenvC tenv (Val v) t'`,
induct_on `env` >>
rw [] >>
fs [lookup_def] >>
rw [] >>
cases_on `tenv` >>
fs [] >-
fs [Once type_v_cases, bind_def] >>
fs [lookup_def] >>
cases_on `h` >>
cases_on `h'` >>
qpat_assum `type_env tenvC ((q,r)::env) ((q',r')::t)`
         (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
fs [bind_def] >>
rw [] >>
fs [lookup_def] >>
cases_on `q = s` >>
fs [] >>
rw [] >>
metis_tac [type_e_val]);

(* A successful pattern match gives a binding environment with the type given by
* the pattern type checker *)
val pmatch_type_preservation = Q.prove (
`(∀envC p v env env' (tenvC:tenvC) tenv t tenv'.
  (pmatch envC p v env = Match env') ∧
  type_v tenvC v t ∧
  type_p tenvC tenv p t tenv' ∧
  type_env tenvC env tenv ⇒
  type_env tenvC env' tenv') ∧
 (∀envC ps vs env env' (tenvC:tenvC) tenv tenv' ts.
  (pmatch_list envC ps vs env = Match env') ∧
  type_vs tenvC vs ts ∧
  type_ps tenvC tenv ps ts tenv' ∧
  type_env tenvC env tenv ⇒
  type_env tenvC env' tenv')`,
HO_MATCH_MP_TAC pmatch_ind >>
rw [pmatch_def] >|
[rw [Once type_v_cases, bind_def, type_e_val] >>
     fs [Once type_p_cases, bind_def] >>
     metis_tac [],
 fs [Once type_p_cases],
 every_case_tac >>
     fs [type_e_val] >>
     qpat_assum `type_v tenvC vpat t`
             (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
     fs [Once type_p_cases] >>
     rw [] >>
     fs [] >>
     rw [] >>
     cases_on `ps` >>
     fs [] >>
     qpat_assum `type_ps a b c d e`
             (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_p_cases]) >>
     fs [] >>
     metis_tac [],
 every_case_tac >>
     fs [],
 fs [Once type_p_cases],
 every_case_tac >>
     fs [] >>
     qpat_assum `type_vs tenvC (v::vs) ts`
             (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
     fs [] >>
     qpat_assum `type_ps a b c d e`
             (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_p_cases]) >>
     fs [] >>
     rw [] >>
     metis_tac []]);

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
rw [Once type_v_cases] >|
[qpat_assum `type_env tenvC [] (h::t)`
         (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
     fs [bind_def],
 qpat_assum `type_env tenvC (h::env') []`
         (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
     fs [bind_def],
 qpat_assum `type_env tenvC (h::env') (h'::t)`
         (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
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
            (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
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
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once type_v_cases]) >>
fs [emp_def] >>
rw [bind_def, Once type_v_cases] >|
[rw [type_e_val] >>
     rw [Once type_v_cases] >>
     metis_tac [lookup_def, bind_def],
 metis_tac [optionTheory.NOT_SOME_NONE, lookup_def, bind_def]]);

val type_recfun_env = Q.prove (
`∀fn funs tenvC tenv tenv0 env.
  type_env tenvC env tenv0 ∧
  type_funs tenvC (merge tenv tenv0) funs tenv
  ⇒
  type_env tenvC (MAP (λ(fn,n,e). (fn,Recclosure env funs fn)) funs) tenv`,
metis_tac [type_recfun_env_help]);

val type_v_lit = Q.prove (
`(!tenvC n t. type_v tenvC (Lit (Num n)) t = (t = Tnum)) ∧
 (!tenvC b t. type_v tenvC (Lit (Bool b)) t = (t = Tbool))`,
rw [Once type_v_cases] >>
rw [Once type_v_cases]);

(* If a step can be taken from a well-typed state, the resulting state has the
* same type *)
val exp_type_preservation = Q.prove (
`∀(tenvC:tenvC) envC env e c t envC' env' e' c'.
  type_state tenvC (envC, env, e, c) t ∧
  (e_step (envC, env, e, c) = Estep (envC', env', e', c'))
  ⇒
  type_state tenvC (envC', env', e', c') t`,
rw [type_state_cases] >>
fs [e_step_def] >>
cases_on `e` >>
fs [push_def] >>
rw [] >|
[every_case_tac >>
     fs [emp_def] >>
     rw [] >>
     pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_ctxts_cases]) >>
     fs [] >>
     qexists_tac `t2` >>
     qexists_tac `tenv` >>
     rw [] >>
     rw [Once type_v_cases, Once type_ctxts_cases],
 fs [continue_def, push_def] >>
     cases_on `c` >>
     fs [] >>
     cases_on `h` >>
     fs [] >>
     cases_on `q` >>
     fs [type_e_val] >>
     every_case_tac >>
     fs [return_def] >>
     rw [] >>
     pop_assum (ASSUME_TAC o 
                SIMP_RULE (srw_ss()) [Once type_ctxts_cases]) >> 
     fs [type_ctxt_cases] >>
     rw [] >>
     fs [type_e_val] >|
     [rw [Once type_ctxts_cases, type_ctxt_cases, type_e_val] >>
          metis_tac [],
      fs [do_app_def] >>
          cases_on `o'` >>
          fs [] >|
          [every_case_tac >>
               fs [] >>
               rw [type_e_val] >>
               fs [hd (CONJUNCTS type_v_cases)] >>
               rw [] >>
               fs [type_op_cases] >>
               rw [] >>
               metis_tac [],
           every_case_tac >>
               fs [] >>
               rw [type_e_val] >>
               fs [hd (CONJUNCTS type_v_cases)] >>
               rw [] >>
               fs [type_op_cases] >>
               rw [] >>
               metis_tac [],
           every_case_tac >>
               fs [] >>
               rw [type_e_val] >|
               [qpat_assum `type_v tenvC (Closure l s e) t1'`
                     (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >> 
                    fs [] >>
                    rw [] >>
                    fs [type_op_cases] >>
                    rw [] >>
                    qexists_tac `t2` >>
                    qexists_tac `bind s t1 tenv''` >>
                    rw [Once type_v_cases, type_e_val] >>
                    metis_tac [],
                qpat_assum `type_v tenvC (Recclosure l l0 s) t1'`
                     (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >> 
                    fs [] >>
                    rw [] >>
                    fs [type_op_cases] >>
                    rw [] >>
                    qexists_tac `t2` >>
                    rw [build_rec_env_lem] >>
                    imp_res_tac type_recfun_lookup >>
                    qexists_tac `bind q t1 (merge tenv''' tenv'')` >>
                    rw [bind_def, Once type_v_cases, type_e_val] >>
                    metis_tac [type_env_merge_lem, type_recfun_env]]],
      fs [do_log_def] >>
           every_case_tac >>
           fs [] >>
           rw [type_e_val] >>
           metis_tac [],
      fs [do_if_def] >>
           every_case_tac >>
           fs [] >>
           rw [type_e_val] >>
           metis_tac [],
      rw [Once (hd (tl (CONJUNCTS type_v_cases)))] >>
          metis_tac [],
      rw [Once type_ctxts_cases, type_ctxt_cases, type_e_val] >>
          fs [RES_FORALL] >>
          metis_tac [],
      fs [RES_FORALL, FORALL_PROD] >>
          rw [] >>
          metis_tac [pmatch_type_preservation],
      qexists_tac `t2` >>
          qexists_tac `bind s t1 tenv'` >>
          rw [Once type_v_cases, type_e_val] >>
          metis_tac [],
      rw [Once (hd (CONJUNCTS type_v_cases))] >>
          imp_res_tac type_es_length_lem >>
          fs [] >>
          `ts2 = []` by 
                  (cases_on `ts2` >>
                   fs []) >>
          rw [type_vs_end_lem] >>
          fs [] >>
          rw [] >>
          metis_tac [type_es_val, rich_listTheory.MAP_REVERSE],
      qpat_assum `type_es tenvC tenv' (e'::t'') ts2`
                (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >> 
          fs [] >>
          rw [] >>
          qexists_tac `t''''` >>
          qexists_tac `tenv'` >>
          rw [] >>
          rw [type_ctxt_cases, Once type_ctxts_cases] >>
          rw [] >>
          qexists_tac `tenv'` >>
          qexists_tac `Tapp ts' tn` >>
          rw [] >>
          cases_on `ts2` >>
          fs [] >>
          rw [] >>
          qexists_tac `ts1++[t''']` >>
          rw [] >> 
          metis_tac [type_es_end_lem, type_es_val, type_e_val],
      qpat_assum `type_es tenvC tenv' (e'::t'') ts2`
                (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >> 
          fs [] >>
          rw [] >>
          qexists_tac `t''''` >>
          qexists_tac `tenv'` >>
          rw [] >>
          rw [type_ctxt_cases, Once type_ctxts_cases] >>
          rw [] >>
          qexists_tac `tenv'` >>
          qexists_tac `Tapp ts' tn` >>
          rw [] >>
          cases_on `ts2` >>
          fs [] >>
          rw [] >>
          qexists_tac `ts1++[t''']` >>
          rw [] >> 
          metis_tac [type_es_end_lem, type_es_val, type_e_val]],
 every_case_tac >>
     fs [return_def] >>
     rw [] >>
     qpat_assum `type_e tenvC tenv (Con s epat) t1` 
              (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >> 
     rw [] >>
     qpat_assum `type_es tenvC tenv epat ts` 
              (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >> 
     fs [type_e_val] >|
     [qexists_tac `Tapp ts' tn` >>
          qexists_tac `tenv` >>
          rw [] >>
          rw [Once type_v_cases] >>
          rw [Once type_v_cases],
      rw [Once type_ctxts_cases, type_ctxt_cases] >>
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
          metis_tac [type_v_rules, APPEND]],
 every_case_tac >>
     fs [return_def] >>
     rw [] >>
     qexists_tac `t1` >>
     qexists_tac `tenv` >>
     rw [] >>
     qpat_assum `type_e tenvC tenv (Var s) t1` 
              (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >> 
     metis_tac [type_lookup_lem2],
 fs [return_def] >>
     rw [] >>
     qpat_assum `type_e tenvC tenv (Fun s e'') t1` 
              (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >> 
     rw [type_e_val] >>
     rw [Once (hd (CONJUNCTS type_v_cases))] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >> 
     rw [Once type_ctxts_cases, type_ctxt_cases] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >> 
     rw [Once type_ctxts_cases, type_ctxt_cases] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >> 
     rw [Once type_ctxts_cases, type_ctxt_cases] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >> 
     rw [Once type_ctxts_cases, type_ctxt_cases] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >> 
     rw [Once type_ctxts_cases, type_ctxt_cases] >>
     metis_tac [],
 every_case_tac >>
     fs [] >>
     rw [] >>
     qpat_assum `type_e tenvC tenv epat t1`
            (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
     fs [] >>
     qexists_tac `t1` >>
     qexists_tac `merge tenv' tenv` >>
     rw [] >>
     rw [build_rec_env_lem] >>
     match_mp_tac type_env_merge_lem >>
     rw [] >>
     match_mp_tac type_recfun_env >>
     metis_tac []]);

val get_first_tenv_def = Define `
  (get_first_tenv ds NONE = 
     case ds of
         (Dtype tds::ds) -> tds
      || _ -> []) ∧
  (get_first_tenv _ _ = [])`;

val disjoint_env_def = Define `
  disjoint_env e1 e2 = 
    DISJOINT (set (MAP FST e1)) (set (MAP FST e2))`;

val lookup_in = Q.prove (
`!x e v. (lookup x e = SOME v) ⇒ MEM x (MAP FST e)`,
induct_on `e` >>
rw [lookup_def] >>
cases_on `h` >>
fs [lookup_def] >>
metis_tac []);

val lookup_notin = Q.prove (
`!x e. (lookup x e = NONE) ⇒ ~MEM x (MAP FST e)`,
induct_on `e` >>
rw [lookup_def] >>
cases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
fs []);

val lookup_disjoint = Q.prove (
`!x v e e'. (lookup x e = SOME v) ∧ disjoint_env e e' ⇒ 
  (lookup x (merge e' e) = SOME v)`,
induct_on `e'` >>
rw [disjoint_env_def, merge_def, lookup_def] >>
cases_on `h` >>
fs [merge_def, lookup_def] >>
fs [Once DISJOINT_SYM, DISJOINT_INSERT] >>
`q ≠ x` by metis_tac [lookup_in] >>
fs [disjoint_env_def] >>
metis_tac [DISJOINT_SYM]);

val tenvC_pat_weakening = Q.prove (
`(!tenvC tenvE p t tenvE'. type_p tenvC tenvE p t tenvE' ⇒ 
    !tenvC'. disjoint_env tenvC tenvC' ⇒ 
             type_p (merge tenvC' tenvC) tenvE p t tenvE') ∧
 (!tenvC tenvE ps ts tenvE'. type_ps tenvC tenvE ps ts tenvE' ⇒ 
    !tenvC'. disjoint_env tenvC tenvC' ⇒ 
             type_ps (merge tenvC' tenvC) tenvE ps ts tenvE')`,
HO_MATCH_MP_TAC type_p_ind >>
rw [] >>
rw [Once type_p_cases] >>
metis_tac [lookup_disjoint]);

val tenvC_weakening = Q.prove (
`(!tenvC v t. type_v tenvC v t ⇒ 
    !tenvC'. disjoint_env tenvC tenvC' ⇒ type_v (merge tenvC' tenvC) v t) ∧
 (!tenvC tenv e t. type_e tenvC tenv e t ⇒ 
    !tenvC'. disjoint_env tenvC tenvC' ⇒ type_e (merge tenvC' tenvC) tenv e t) ∧
 (!tenvC tenv es ts. type_es tenvC tenv es ts ⇒ 
    !tenvC'. disjoint_env tenvC tenvC' ⇒ type_es (merge tenvC' tenvC) tenv es ts) ∧
 (!tenvC vs ts. type_vs tenvC vs ts ⇒ 
    !tenvC'. disjoint_env tenvC tenvC' ⇒ type_vs (merge tenvC' tenvC) vs ts) ∧
 (!tenvC env tenv. type_env tenvC env tenv ⇒ 
    !tenvC'. disjoint_env tenvC tenvC' ⇒ type_env (merge tenvC' tenvC) env tenv) ∧
 (!tenvC tenv funs tenv'. type_funs tenvC tenv funs tenv' ⇒ 
    !tenvC'. disjoint_env tenvC tenvC' ⇒ type_funs (merge tenvC' tenvC) tenv funs tenv')`,
HO_MATCH_MP_TAC type_v_ind >>
rw [] >>
rw [Once type_v_cases] >>
fs [RES_FORALL, FORALL_PROD] >>
metis_tac [lookup_disjoint, tenvC_pat_weakening]);

val check_ctor_tenv_dups_helper1 = Q.prove (
`∀tenvC l y z.
  (!x. MEM x l ⇒ (λ(n,ts). lookup n tenvC = NONE) x)
  ⇒
  DISJOINT (set (MAP (λx. FST ((λ(cn,ts). (cn,y,ts,z)) x)) l))
           (set (MAP FST tenvC))`,
induct_on `l` >>
rw [] >>
cases_on `h` >>
fs [] >>
`(λ(n,ts). lookup n tenvC = NONE) (q,r)` by metis_tac [] >>
fs [] >>
metis_tac [lookup_notin]);

val check_ctor_tenv_dups_helper2 = Q.prove (
`!tds tenvC.
  (∀((tvs,tn,condefs)::set tds) ((n,ts)::set condefs). lookup n tenvC = NONE) ⇒
    disjoint_env tenvC (build_ctor_tenv tds)`,
induct_on `tds` >>
rw [build_ctor_tenv_def, disjoint_env_def] >|
[fs [RES_FORALL] >>
     cases_on `h` >>
     fs [] >>
     cases_on `r` >>
     fs [] >>
     `(λ(tvs,tn,condefs).
         ∀x. MEM x condefs ⇒ (λ(n,ts). lookup n tenvC = NONE) x) (q,q',r')`
                by metis_tac [] >>
     fs [MAP_MAP_o, combinTheory.o_DEF] >>
     metis_tac [check_ctor_tenv_dups_helper1],
 fs [RES_FORALL] >>
     `disjoint_env tenvC (build_ctor_tenv tds)` by metis_tac [] >>
     fs [disjoint_env_def, build_ctor_tenv_def] >>
     metis_tac [DISJOINT_SYM]]);

val check_ctor_tenv_dups = Q.prove (
`!tenvC tds. 
  check_ctor_tenv tenvC tds ⇒ disjoint_env tenvC (build_ctor_tenv tds)`,
rw [check_ctor_tenv_def, check_dup_ctors_def] >>
metis_tac [check_ctor_tenv_dups_helper2]);

val e_step_ctor_env_same = Q.prove (
`!cenv env e c cenv' env' e' c'.
  (e_step (cenv,env,e,c) = Estep (cenv',env',e',c')) ⇒ (cenv = cenv')`,
rw [e_step_def] >>
every_case_tac >>
fs [push_def, return_def, continue_def] >>
every_case_tac >>
fs []);

val type_preservation = Q.prove (
`!tenvC envC envE ds c envC' envE' ds' c' tenvE tenvC' st' tenvC''.
  (tenvC'' = build_ctor_tenv (get_first_tenv ds c)) ∧
  type_d_state tenvC (envC,envE,ds,c) (merge tenvC'' tenvC') tenvE ∧
  (d_step (envC,envE,ds,c) = Dstep (envC',envE',ds',c'))
  ⇒
  type_d_state (merge tenvC'' tenvC) (envC',envE',ds',c') tenvC' tenvE`,
rw [type_d_state_cases] >>
fs [d_step_def] >>
every_case_tac >>
fs [] >>
rw [] >-
(pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_ds_cases]) >>
     rw [type_state_cases, Once type_ctxts_cases, type_ctxt_cases] >>
     fs [build_ctor_tenv_def,get_first_tenv_def, merge_def, emp_def, 
         type_d_cases] >>
     metis_tac [APPEND]) >-
(qpat_assum `type_ds a b c d e`
            (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_ds_cases]) >>
     fs [type_d_cases] >>
     rw [build_rec_env_lem] >>
     fs [build_ctor_tenv_def, get_first_tenv_def, merge_def, emp_def] >>
     metis_tac [merge_def, type_recfun_env, type_env_merge_lem]) >-
(qpat_assum `type_ds a b c d e`
            (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_ds_cases]) >>
     fs [type_d_cases, get_first_tenv_def, merge_def] >>
     metis_tac [tenvC_weakening, merge_def, check_ctor_tenv_dups]) >-
(fs [type_state_cases, Once type_ctxts_cases, type_e_val, merge_def,emp_def,
     get_first_tenv_def, build_ctor_tenv_def] >>
     metis_tac [pmatch_type_preservation, merge_def]) >>
cases_on `p'` >>
cases_on `r` >>
cases_on `r'` >>
rw [] >>
fs [merge_def, emp_def, get_first_tenv_def, build_ctor_tenv_def] >>
metis_tac [merge_def,exp_type_preservation,e_step_ctor_env_same]);

val def_final_state_def = Define `
  def_final_state (envC,envE,ds,c) = (c = NONE) ∧ (ds = [])`;

val consistent_cenv_no_dups = Q.prove (
`!l envC tenvC. 
  consistent_con_env envC tenvC ∧
  check_dup_ctors l tenvC
  ⇒
  check_dup_ctors l envC`,
induct_on `l` >>
rw [check_dup_ctors_def] >>
fs [RES_FORALL] >>
rw [] >|
[cases_on `h` >>
     fs [] >>
     cases_on `r` >>
     fs [] >>
     `(λ(tvs,tn,condefs).
        ∀x. MEM x condefs ⇒ (λ(n,ts). lookup n tenvC = NONE) x) (q,q',r')`
              by metis_tac [] >>
     fs [] >>
     rw [] >>
     cases_on `x` >>
     fs [] >>
     RES_TAC >>
     fs [] >>
     metis_tac [consistent_con_env_lem2],
 `(λ(tvs,tn,condefs).
    ∀x. MEM x condefs ⇒ (λ(n,ts). lookup n tenvC = NONE) x) x`
              by metis_tac [] >>
     cases_on `x` >>
     fs [] >>
     cases_on `r` >>
     fs [] >>
     rw [] >>
     cases_on `x` >>
     fs [] >>
     RES_TAC >>
     fs [] >>
     metis_tac [consistent_con_env_lem2]]);

val type_progress = Q.prove (
`!tenvC envC envE ds c tenvC' tenvE.
  type_d_state tenvC (envC,envE,ds,c) tenvC' tenvE ∧
  consistent_con_env envC tenvC ∧
  consistent_con_env2 envC tenvC ∧
  ~def_final_state (envC,envE,ds,c)
  ⇒
  (?envC' envE' ds' c'. d_step (envC,envE,ds,c) = Dstep (envC',envE',ds',c'))
  ∨
  (?err. d_step (envC,envE,ds,c) = Draise err)`,
rw [type_d_state_cases, d_step_def, def_final_state_def] >>
rw [] >|
[every_case_tac >>
     fs [] >|
     [fs [Once type_ds_cases, type_d_cases] >>
          metis_tac [type_funs_distinct],
      fs [Once type_ds_cases, type_d_cases, check_ctor_tenv_def] >>
          metis_tac [consistent_cenv_no_dups]],
 every_case_tac >>
     fs [] >-
     (fs [type_state_cases, type_e_val, Once type_ctxts_cases] >>
           metis_tac [pmatch_type_progress, match_result_distinct]) >>
     metis_tac [exp_type_progress, not_final_state, e_step_result_distinct],
 every_case_tac >>
     fs [] >-
     (fs [type_state_cases, type_e_val, Once type_ctxts_cases] >>
           metis_tac [pmatch_type_progress, match_result_distinct]) >>
     metis_tac [exp_type_progress, not_final_state, e_step_result_distinct]]);

val consistent_con_append = Q.prove (
`!envC tenvC.
  consistent_con_env envC tenvC ⇒
    ∀envC' tenvC'.
      consistent_con_env envC' tenvC'
      ⇒
      consistent_con_env (envC++envC') (tenvC++tenvC')`,
HO_MATCH_MP_TAC (fetch "-" "consistent_con_env_ind") >>
rw [consistent_con_env_def] >>
rw []);

val extend_consistent_con = Q.prove (
`!envC tenvC tds.
  consistent_con_env envC tenvC
  ⇒
  consistent_con_env (build_tdefs tds ++ envC) (build_ctor_tenv tds ++ tenvC)`,
induct_on `tds` >>
rw [build_tdefs_def, build_ctor_tenv_def] >>
cases_on `h` >>
cases_on `r` >>
fs [] >>
`!x. (!cn ts. MEM (cn,ts) r' ⇒ MEM (cn,ts) x) ⇒
  consistent_con_env 
  (MAP (λ(conN,ts). (conN,LENGTH ts,{cn | (cn,ts) | MEM (cn,ts) x})) r')
  (MAP (λ(cn,ts). (cn,q,ts,q')) r')`
            by (Induct_on `r'` >>
                rw [consistent_con_env_def] >>
                cases_on `h` >>
                cases_on `r` >>
                fs [] >>
                rw [consistent_con_env_def, GSPECIFICATION] >|
                [qexists_tac `(q'',[])` >>
                     rw [],
                 qexists_tac `(q'',h::t)` >>
                     rw []]) >>
fs [build_ctor_tenv_def, build_tdefs_def] >>
metis_tac [consistent_con_append, APPEND_ASSOC]);

val lookup_append = Q.prove (
`!x e1 e2. 
  lookup x (e1 ++ e2) =
    if lookup x e1 = NONE then
      lookup x e2
    else
      lookup x e1`,
induct_on `e1` >>
rw [lookup_def] >>
cases_on `h` >>
fs [lookup_def] >>
rw [] >>
fs []);

val check_dup_ctors_disj = Q.prove (
`!tenvC tds. 
  check_dup_ctors tds tenvC ⇒ disjoint_env tenvC (build_ctor_tenv tds)`,
rw [check_dup_ctors_def] >>
metis_tac [check_ctor_tenv_dups_helper2]);

val consistent_con_env_destruct_help = Q.prove (
`!l x y q q' l'.
  consistent_con_env 
    (MAP (λ(conN,ts). (conN,LENGTH ts,{cn | (cn,ts) | MEM (cn,ts) l'})) l ++ x)
    (MAP (\(cn,ts). (cn,q,ts,q')) l ++ y)
  ⇒
  consistent_con_env x y`,
induct_on `l` >>
rw [] >>
cases_on `h` >>
fs [consistent_con_env_def] >>
metis_tac []);

val consistent_con_env_destruct = Q.prove (
`!td tds.
  consistent_con_env (build_tdefs (td::tds)) (build_ctor_tenv (td::tds))
  ⇒
  consistent_con_env (build_tdefs tds) (build_ctor_tenv tds)`,
rw [consistent_con_env_def, build_tdefs_def, build_ctor_tenv_def] >>
cases_on `td` >> 
cases_on `r` >>
fs [] >>
metis_tac [consistent_con_env_destruct_help]);

val lookup_none = Q.prove (
`!tds tenvC envC x.
  !x. (lookup x (build_ctor_tenv tds) = NONE) = 
      (lookup x (build_tdefs tds) = NONE)`,
Induct >>
rw [] >-
fs [build_ctor_tenv_def, build_tdefs_def, lookup_def] >>
RES_TAC >>
rw [build_ctor_tenv_def, build_tdefs_def, lookup_def] >>
cases_on `h` >>
cases_on `r` >>
rw [lookup_append] >-
metis_tac [build_ctor_tenv_def, build_tdefs_def] >|
[cases_on `lookup x (MAP (\(conN,ts). (conN,LENGTH ts,{cn | (cn,ts) | MEM (cn,ts) r'})) r')` >>
     fs [] >>
     imp_res_tac lookup_in >> 
     imp_res_tac lookup_notin >> 
     fs [MEM_MAP] >>
     rw [] >>
     cases_on `y'` >>
     fs [] >>
     rw [] >>
     pop_assum (ASSUME_TAC o Q.SPEC `(q'',q,r,q')`) >>
     fs [] >>
     pop_assum (ASSUME_TAC o Q.SPEC `(q'',r)`) >>
     fs [] >>
     rw [],
 cases_on `lookup x (MAP (\(cn,ts). (cn,q,ts,q')) r')` >>
     fs [] >>
     imp_res_tac lookup_in >> 
     imp_res_tac lookup_notin >> 
     fs [MEM_MAP] >>
     rw [] >>
     cases_on `y'` >>
     fs [] >>
     rw [] >>
     pop_assum (ASSUME_TAC o Q.SPEC `(q'',LENGTH (r:'d list), {cn | (cn,ts) |
     MEM (cn,ts) (r':('c,'d list) env)})`) >>
     fs [] >>
     pop_assum (ASSUME_TAC o Q.SPEC `(q'',r)`) >>
     fs [] >>
     rw [] >>
     fs []]);

val build_ctor_tenv_empty = Q.prove (
`build_ctor_tenv [] = []`,
rw [build_ctor_tenv_def]);

val build_ctor_tenv_cons = Q.prove (
`∀tvs tn ctors tds.
  build_ctor_tenv ((tvs,tn,ctors)::tds) =  
    MAP (λ(cn,ts). (cn,tvs,ts,tn)) ctors ++ build_ctor_tenv tds`,
rw [build_ctor_tenv_def]);

val lemma = Q.prove (
`!f a b c. (\(x,y,z). f x y z) (a,b,c) = f a b c`,
rw []);

val every_conj_tup3 = Q.prove (
`!P Q l. 
  EVERY (\(x,y,z). P x y z ∧ Q x y z) l = 
  EVERY (\(x,y,z). P x y z) l ∧ 
  EVERY (\(x,y,z). Q x y z) l`,
induct_on `l` >>
rw [] >>
cases_on `h` >>
cases_on `r` >>
rw [] >>
metis_tac []);

val check_ctor_tenv_different_types = Q.prove (
`!tenvC tds.
  EVERY 
    (λ(tvs,tn,ctors).
       EVERY (λx. case x of (v,v2,v4,tn') -> tn ≠ tn') tenvC) tds ∧
  (lookup n1 tenvC = SOME (tvs1,ts1,tn1)) ∧
  (lookup n2 (build_ctor_tenv tds) = SOME (tvs2,ts2,tn2))
  ⇒
  (tn1 ≠ tn2)`,
induct_on `tenvC` >>
rw [build_ctor_tenv_empty,lookup_def] >>
cases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
fs [] >>
rw [] >|
[induct_on `tds` >>
     fs [lookup_def,build_ctor_tenv_empty]  >>
     rw [] >>
     cases_on `h` >>
     cases_on `r'` >>
     fs [build_ctor_tenv_cons, lookup_append] >>
     every_case_tac >>
     fs [] >>
     induct_on `r''` >>
     fs [lookup_def] >>
     rw [] >>
     cases_on `h` >>
     fs [lookup_def] >>
     every_case_tac >>
     fs [],
 fs [every_conj_tup3] >>
     metis_tac []]);

val build_tdefs_cons = Q.prove (
`!tvs tn ctors tds. 
  build_tdefs ((tvs,tn,ctors)::tds) =
    MAP (\(conN,ts). (conN, LENGTH ts, {cn | (cn,ts) | MEM (cn,ts) ctors}))
        ctors
    ++
    build_tdefs tds`,
rw [build_tdefs_def]);

val lookup_none2 = Q.prove (
`!ctors n q q' s.
  (lookup n (MAP (\(cn,ts). (cn,q,ts,q')) ctors) = NONE)
  =
  (lookup n (MAP (\(conN,ts). (conN,LENGTH ts,s)) ctors) = NONE)`,
induct_on `ctors` >>
rw [lookup_def] >>
cases_on `h` >>
fs [lookup_def] >>
full_case_tac);

val check_dup_ctors_cons = Q.prove (
`!tvs ts ctors tds tenvC.
  check_dup_ctors ((tvs,ts,ctors)::tds) tenvC
  ⇒ 
  check_dup_ctors tds tenvC`,
induct_on `tds` >>
rw [check_dup_ctors_def, LET_THM, RES_FORALL] >-
metis_tac [] >-
metis_tac [] >>
cases_on `h` >>
fs [] >>
pop_assum MP_TAC >>
pop_assum (fn _ => all_tac) >>
induct_on `ctors` >>
rw [] >>
cases_on `h` >>
fs []);

val check_ctor_tenv_cons = Q.prove (
`!tvs ts ctors tds tenvC.
  check_ctor_tenv tenvC ((tvs,ts,ctors)::tds) ⇒
  check_ctor_tenv tenvC tds`,
rw [check_ctor_tenv_def] >>
metis_tac [check_dup_ctors_cons]);

val lookup_type = Q.prove (
`!x ctors tn tvs ts tn' tvs'. 
  (lookup x (MAP (λ(cn,ts). (cn,tvs,ts,tn)) ctors) = SOME (tvs',ts,tn'))
  ⇒
  (tn = tn')`,
induct_on `ctors` >>
rw [lookup_def] >>
cases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
fs [] >>
rw [] >>
metis_tac []);

val lookup_same_ctor_type_help = Q.prove (
`!tds.
  (lookup n2 (build_ctor_tenv tds) = SOME (tvs2,ts2,tn))
  ⇒
  MEM tn (MAP (λx. case x of (v,tn,v3) -> tn) tds)`,
Induct >>
rw [lookup_def,build_ctor_tenv_empty] >>
cases_on `h` >>
cases_on `r` >>
fs [build_ctor_tenv_cons] >>
induct_on `r'` >>
rw [] >>
cases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
fs []);

val lookup_same_ctor_type_help2 = Q.prove (
`!ctors n1 ns1 r'.
  (lookup n1 
    (MAP (λ(conN,ts). (conN,LENGTH ts,{cn | (cn,ts) | MEM (cn,ts) r'})) ctors) =
   SOME (l1,ns1))
  ⇒
  (ns1 = {cn | (cn,ts) | MEM (cn,ts) r'})`,
Induct >>
rw [lookup_def] >>
cases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
fs [] >> 
rw [] >>
metis_tac []);

val lookup_same_ctor_type = Q.prove (
`!tds.
  check_ctor_tenv tenvC tds ∧
  (lookup n1 (build_ctor_tenv tds) = SOME (tvs1,ts1,tn)) ∧
  (lookup n2 (build_ctor_tenv tds) = SOME (tvs2,ts2,tn)) ∧
  (lookup n1 (build_tdefs tds) = SOME (l1,ns1)) ∧
  (lookup n2 (build_tdefs tds) = SOME (l2,ns2))
  ⇒
  (ns1 = ns2)`,
Induct >>
rw [] >-
fs [build_tdefs_def, lookup_def] >>
cases_on `h` >>
cases_on `r` >>
fs [build_ctor_tenv_cons,build_tdefs_cons, lookup_append] >>
`check_ctor_tenv tenvC tds` by metis_tac [check_ctor_tenv_cons] >>
every_case_tac >>
fs [] >|
[metis_tac [lookup_none2],
 metis_tac [lookup_none2],
 metis_tac [lookup_none2],
 metis_tac [lookup_none2],
 `q' = tn` by metis_tac [lookup_type] >>
     rw [] >>
     fs [check_ctor_tenv_def] >>
     metis_tac [lookup_same_ctor_type_help],
 metis_tac [lookup_none2],
 metis_tac [lookup_none2],
 metis_tac [lookup_none2],
 metis_tac [lookup_none2],
 `q' = tn` by metis_tac [lookup_type] >>
     rw [] >>
     fs [check_ctor_tenv_def] >>
     metis_tac [lookup_same_ctor_type_help],
 metis_tac [lookup_none2],
 metis_tac [lookup_none2],
 metis_tac [lookup_none2],
 metis_tac [lookup_none2],
 metis_tac [lookup_same_ctor_type_help2]]);

val consistent_con_preservation = Q.prove (
`!tenvC envC envE ds c envC' envE' ds' c' tenvE tenvC' st' tds.
  (tds = get_first_tenv ds c) ∧
  check_ctor_tenv tenvC tds ∧
  consistent_con_env envC tenvC ∧
  consistent_con_env2 envC tenvC ∧
  (d_step (envC,envE,ds,c) = Dstep (envC',envE',ds',c'))
  ⇒
  consistent_con_env envC' (merge (build_ctor_tenv tds) tenvC) ∧
  consistent_con_env2 envC' (merge (build_ctor_tenv tds) tenvC)`,
rw [d_step_def] >>
cases_on `c` >>
fs [] >>
every_case_tac >>
fs [] >>
rw [get_first_tenv_def, merge_def, build_ctor_tenv_empty] >-
metis_tac [extend_consistent_con] >>
imp_res_tac check_dup_ctors_disj >>
fs [consistent_con_env2_def] >>
rw [] >>
cases_on `lookup n1 (build_ctor_tenv l) = NONE` >>
cases_on `lookup n2 (build_ctor_tenv l) = NONE` >>
fs [get_first_tenv_def] >|
[`(lookup n1 (build_tdefs l) = NONE) ∧
  (lookup n2 (build_tdefs l) = NONE)`
          by metis_tac [lookup_none] >>
     fs [lookup_append] >>
     metis_tac [],
 `(lookup n1 (build_tdefs l) = NONE) ∧
  (lookup n2 (build_tdefs l) ≠ NONE)`
          by metis_tac [lookup_none] >>
     fs [lookup_append] >>
     metis_tac [check_ctor_tenv_different_types, check_ctor_tenv_def],
 `(lookup n1 (build_tdefs l) ≠ NONE) ∧
  (lookup n2 (build_tdefs l) = NONE)`
          by metis_tac [lookup_none] >>
     fs [lookup_append] >>
     metis_tac [check_ctor_tenv_different_types, check_ctor_tenv_def],
 `(lookup n1 (build_tdefs l) ≠ NONE) ∧
  (lookup n2 (build_tdefs l) ≠ NONE)`
          by metis_tac [lookup_none] >>
     fs [lookup_append] >>
     metis_tac [lookup_same_ctor_type]]);

     (*
val type_soundness_help = Q.prove (
`!st1 st2. d_step_reln^* st1 st2 ⇒
  ∀tenvC tenvC' tenvE. 
    type_d_state tenvC st1 tenvC' tenvE
    ⇒
    ?tenvC1 tenvC2.
      (tenvC' = merge tenvC1 tenvC2) ∧
      type_d_state (merge tenvC1 tenvC) st2 tenvC2 tenvE`,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 >>
rw [] >-
(rw [merge_def] >>
     metis_tac [APPEND,APPEND_NIL]) >>
fs [d_step_reln_def] >>
`?envC envE ds c. st2 = (envC,envE,ds,c)`
        by (cases_on `st2` >>
            cases_on `r` >>
            cases_on `r'` >>
            metis_tac []) >>
`?envC' envE' ds' c'. st2' = (envC',envE',ds',c')`
        by (cases_on `st2'` >>
            cases_on `r` >>
            cases_on `r'` >>
            metis_tac []) >>
rw [] >>
RES_TAC >>
`?tenvC1' tenvC2'. tenvC2 = merge (build_ctor_tenv (get_first_tenv ds c)) tenvC2'`
         by (cases_on `ds` >>
             fs [get_first_tenv_def,merge_def,get_first_tenv_def, 
                 build_ctor_tenv_def, type_d_state_cases] >>
             cases_on `h` >>
             fs [Once type_ds_cases, Once type_d_cases, build_ctor_tenv_def] >>
             rw [] >>
             metis_tac [merge_def]) >>
`type_d_state (merge (build_ctor_tenv (get_first_tenv ds c)) (merge tenvC1 tenvC)) (envC',envE',ds',c') tenvC2' tenvE`
         by metis_tac [type_preservation] >>
fs [] >>
qexists_tac `tenvC1'` >>
qexists_tac `tenvC2'` >>
fs [merge_def] >>
rw []

metis_tac [merge_def, APPEND_ASSOC]


val type_soundness = Q.store_thm
`!tenvC tenvE ds tenvC' tenvE' envC envE.
  type_ds tenvC tenvE ds tenvC' tenvE' ∧
  type_env [] envE tenvE
  ⇒
  diverges envC envE ds ∨ 
  ?r. (r ≠ Rerr Rtype_error) ∧ d_small_eval envC envE ds NONE r`,
rw [diverges_def, METIS_PROVE [] ``x ∨ y = ~x ⇒ y``, d_step_reln_def] >>
*)

val _ = export_theory ();
