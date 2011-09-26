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

val _ = new_theory "bigSmallEquiv";

(* ------------------------ Big step/small step equivalence ----------------- *)

val small_eval_prefix = Q.prove (
`∀cenv env e c cenv' env' e' c' r.
  e_step_reln^* (cenv,env,e,c) (cenv,env',e',c') ∧
  small_eval cenv env' e' c' r 
  ⇒
  small_eval cenv env e c r`,
rw [] >>
cases_on `r` >|
[all_tac,
 cases_on `e''`] >>
fs [small_eval_def] >>
metis_tac [transitive_RTC, transitive_def]);

val e_single_step_add_ctxt = Q.prove (
`!cenv env e c cenv' env' e' c' c''. 
  (e_step (cenv,env,e,c) = Estep (cenv',env',e',c')) 
  ⇒
  (e_step (cenv,env,e,c++c'') = Estep (cenv',env',e',c'++c''))`,
rw [e_step_def] >>
cases_on `e` >>
fs [push_def, return_def, emp_def] >>
rw [] >>
fs [] >>
rw [] >>
every_case_tac >>
fs [] >> 
rw [] >>
fs [continue_def] >>
cases_on `c` >>
fs [] >>
cases_on `h` >>
fs [] >>
cases_on `q` >>
fs [] >>
every_case_tac >>
fs [push_def, return_def] >> 
rw []);

val e_single_error_add_ctxt = Q.prove (
`!cenv env e c cenv' env' e' c' c''. 
  (e_step (cenv,env,e,c) = Etype_error)
  ⇒
  (e_step (cenv,env,e,c++c'') = Etype_error)`,
rw [e_step_def] >>
cases_on `e` >>
fs [push_def, return_def, emp_def] >>
rw [] >>
fs [] >>
rw [] >>
every_case_tac >>
fs [] >> 
rw [] >>
fs [continue_def] >>
cases_on `c` >>
fs [] >>
cases_on `h` >>
fs [] >>
cases_on `q` >>
fs [] >>
every_case_tac >>
fs [push_def, return_def] >> 
rw []);

val e_step_add_ctxt_help = Q.prove (
`!st1 st2. e_step_reln^* st1 st2 ⇒ 
  !cenv1 env1 e1 c1 cenv2 env2 e2 c2 c'.
    (st1 = (cenv1,env1,e1,c1)) ∧ (st2 = (cenv2,env2,e2,c2))
    ⇒
    e_step_reln^* (cenv1,env1,e1,c1++c') (cenv2,env2,e2,c2++c')`,
HO_MATCH_MP_TAC RTC_INDUCT >>
rw [e_step_reln_def] >-
metis_tac [RTC_REFL] >>
cases_on `st1'` >>
cases_on `r` >>
cases_on `r'` >>
fs [] >>
imp_res_tac e_single_step_add_ctxt >>
fs [] >>
rw [Once RTC_CASES1] >>
metis_tac [e_step_reln_def]);

val e_step_add_ctxt = Q.prove (
`!cenv1 env1 e1 c1 cenv2 env2 e2 c2 c'.
   e_step_reln^* (cenv1,env1,e1,c1) (cenv2,env2,e2,c2)
   ⇒
   e_step_reln^* (cenv1,env1,e1,c1++c') (cenv2,env2,e2,c2++c')`,
metis_tac [e_step_add_ctxt_help]);

val e_step_raise = Q.prove (
`!cenv env err c.
  e_step_reln^* (cenv,env,Raise err,c) (cenv,env,Raise err,[])`,
induct_on `c` >>
rw [] >>
rw [Once RTC_CASES1] >>
qexists_tac `(cenv,env,Raise err,c)` >>
rw [e_step_reln_def, e_step_def]);

val small_eval_err_add_ctxt = Q.prove (
`!cenv env e c err c'.
 small_eval cenv env e c (Rerr err) ⇒ small_eval cenv env e (c++c') (Rerr err)`,
cases_on `err` >>
rw [small_eval_def] >|
[`e_step_reln^* (cenv,env,e,c++c') (cenv,env',e',c''++c')` 
       by metis_tac [e_step_add_ctxt] >>
     metis_tac [e_single_error_add_ctxt],
 `e_step_reln^* (cenv,env,e',c++c') (cenv,env',Raise e,c')` 
       by metis_tac [e_step_add_ctxt, APPEND] >>
     metis_tac [e_step_raise, transitive_RTC, transitive_def]]);

val small_eval_step_tac =
rw [do_con_check_def] >>
every_case_tac >>
fs [] >>
cases_on `r` >|
[all_tac,
 cases_on `e`] >>
rw [small_eval_def] >>
EQ_TAC >>
rw [] >|
[pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once RTC_CASES1]) >>
     fs [return_def, e_step_reln_def, e_step_def, push_def, do_con_check_def] >>
     every_case_tac >>
     fs [] >>
     metis_tac [],
 rw [return_def, Once RTC_CASES1, e_step_reln_def, e_step_def, push_def, 
     do_con_check_def] >>
     metis_tac [],
 qpat_assum `e_step_reln^* spat1 spat2`
             (ASSUME_TAC o 
              SIMP_RULE (srw_ss()) [Once RTC_CASES1,e_step_reln_def, 
                                    e_step_def, push_def]) >>
     fs [] >>
     every_case_tac >>
     fs [return_def, do_con_check_def] >>
     rw [] >-
     (fs [e_step_def, push_def] >>
      pop_assum MP_TAC >>
      rw [return_def, do_con_check_def]) >>
     metis_tac [],
 rw [return_def, Once RTC_CASES1, e_step_reln_def, Once e_step_def, push_def,
     do_con_check_def] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once RTC_CASES1]) >>
     fs [e_step_reln_def, e_step_def, push_def, return_def, do_con_check_def] >>
     every_case_tac >>
     fs [] >>
     metis_tac [],
 rw [return_def, Once RTC_CASES1, e_step_reln_def, Once e_step_def, push_def,
     do_con_check_def] >>
     metis_tac []];

val small_eval_con_empty = Q.prove (
`!cenv env cn ns c r.
  do_con_check cenv cn 0
  ⇒
  (small_eval cenv env (Con cn []) c r =
   small_eval cenv env (Val (Conv cn [])) c r)`,
small_eval_step_tac);

val small_eval_con = Q.prove (
`!cenv env cn e1 es ns c r.
  do_con_check cenv cn (LENGTH (e1::es))
  ⇒
  (small_eval cenv env (Con cn (e1::es)) c r =
   small_eval cenv env e1 ((Ccon cn [] () es,env)::c) r)`,
small_eval_step_tac);

val small_eval_app = Q.prove (
`!cenv env op e1 e2 c r. 
  small_eval cenv env (App op e1 e2) c r =
  small_eval cenv env e1 ((Capp1 op () e2,env)::c) r`,
small_eval_step_tac);

val small_eval_log = Q.prove (
`!cenv env op e1 e2 c r. 
  small_eval cenv env (Log op e1 e2) c r =
  small_eval cenv env e1 ((Clog op () e2,env)::c) r`,
small_eval_step_tac);

val small_eval_if = Q.prove (
`!cenv env e1 e2 e3 c r. 
  small_eval cenv env (If e1 e2 e3) c r =
  small_eval cenv env e1 ((Cif () e2 e3,env)::c) r`,
small_eval_step_tac);

val small_eval_match = Q.prove (
`!cenv env e1 pes c r. 
  small_eval cenv env (Mat e1 pes) c r =
  small_eval cenv env e1 ((Cmat () pes,env)::c) r`,
small_eval_step_tac);

val small_eval_let = Q.prove (
`!cenv env n e1 e2 c r. 
  small_eval cenv env (Let n e1 e2) c r =
  small_eval cenv env e1 ((Clet n () e2,env)::c) r`,
small_eval_step_tac);

val small_eval_letrec = Q.prove (
`!cenv env funs e1 c r. 
  ALL_DISTINCT (MAP (λ(x,y,z). x) funs) ⇒
  (small_eval cenv env (Letrec funs e1) c r =
   small_eval cenv (build_rec_env funs env) e1 c r)`,
small_eval_step_tac);

val (small_eval_list_rules, small_eval_list_ind, small_eval_list_cases) = Hol_reln `
(!cenv env. small_eval_list cenv env [] (Rval [])) ∧
(!cenv env e es v vs env'.
  e_step_reln^* (cenv,env,e,[]) (cenv,env',Val v,[]) ∧
  small_eval_list cenv env es (Rval vs)
  ⇒
  small_eval_list cenv env (e::es) (Rval (v::vs))) ∧
(!cenv env e es err env' v.
  e_step_reln^* (cenv,env,e,[]) (cenv,env',Raise err,[]) ∨
  (e_step_reln^* (cenv,env,e,[]) (cenv,env',Val v,[]) ∧
   small_eval_list cenv env es (Rerr (Rraise err)))
  ⇒
  (small_eval_list cenv env (e::es) (Rerr (Rraise err)))) ∧
(!cenv env e es e' c' env' v.
  (e_step_reln^* (cenv,env,e,[]) (cenv,env',e',c') ∧
   (e_step (cenv,env',e',c') = Etype_error)) ∨
  (e_step_reln^* (cenv,env,e,[]) (cenv,env',Val v,[]) ∧
   small_eval_list cenv env es (Rerr Rtype_error))
  ⇒
  (small_eval_list cenv env (e::es) (Rerr Rtype_error)))`;

val small_eval_list_length = Q.prove (
`!cenv env es r. small_eval_list cenv env es r ⇒
  !vs. (r = Rval vs) ⇒ (LENGTH es = LENGTH vs)`,
HO_MATCH_MP_TAC small_eval_list_ind >>
rw [] >>
rw []);

val small_eval_list_step = Q.prove (
`!cenv env es r. small_eval_list cenv env es r ⇒
  (!e v vs cn vs' env'.
     do_con_check cenv cn (LENGTH vs' + 1 + LENGTH vs) ∧
     (r = Rval vs) ∧ e_step_reln^* (cenv,env,e,[]) (cenv,env',Val v,[]) ⇒
     e_step_reln^* (cenv,env,e,[(Ccon cn vs' () es,env)])
                   (cenv,env,Val (Conv cn (REVERSE vs'++[v]++vs)),[]))`,
HO_MATCH_MP_TAC (fetch "-" "small_eval_list_strongind") >>
rw [] >|
[`e_step_reln^* (cenv,env,e,[(Ccon cn vs' () [],env)])
                (cenv,env',Val v,[(Ccon cn vs' () [],env)])`
             by metis_tac [e_step_add_ctxt,APPEND] >>
     `e_step_reln (cenv,env',Val v,[(Ccon cn vs' () [],env)])
                  (cenv,env,Val (Conv cn (REVERSE vs' ++ [v] ++ [])),[])`
             by rw [return_def, continue_def, e_step_reln_def, e_step_def] >>
     fs [] >>
     metis_tac [transitive_RTC, transitive_def, RTC_SINGLE, APPEND],
 `LENGTH (v'::vs'') + 1 + LENGTH vs = LENGTH vs'' + 1 + SUC (LENGTH vs)`
              by (fs [] >>
                  DECIDE_TAC) >>
     `e_step_reln^* (cenv,env,e,[(Ccon cn (v'::vs'') () es,env)])
                (cenv,env,Val (Conv cn (REVERSE vs'' ++ [v'] ++ [v] ++ vs)),[])`
             by metis_tac [REVERSE_DEF] >>
     `e_step_reln^* (cenv,env,e',[(Ccon cn vs'' () (e::es),env)])
                    (cenv,env'',Val v',[(Ccon cn vs'' () (e::es),env)])`
             by metis_tac [e_step_add_ctxt, APPEND] >>
     `e_step_reln (cenv,env'',Val v',[(Ccon cn vs'' () (e::es),env)])
                  (cenv,env,e,[(Ccon cn (v'::vs'') () es,env)])`
             by rw [push_def,continue_def, e_step_reln_def, e_step_def] >>
     fs [] >>
     `LENGTH es = LENGTH vs` by metis_tac [small_eval_list_length] >>
     `LENGTH vs'' + 1 + 1 + LENGTH es = LENGTH vs'' + 1 + SUC (LENGTH es)`
                by DECIDE_TAC >>
     metis_tac [APPEND_ASSOC, APPEND, RTC_SINGLE, transitive_RTC,
                transitive_def]]);

val small_eval_list_err = Q.prove (
`!cenv env es r. small_eval_list cenv env es r ⇒
  (!e v err cn vs' env'.
     do_con_check cenv cn (LENGTH vs' + 1 + LENGTH es) ∧
     (r = Rerr (Rraise err)) ∧ 
     e_step_reln^* (cenv,env,e,[]) (cenv,env',Val v,[]) ⇒
     ?env''. e_step_reln^* (cenv,env,e,[(Ccon cn vs' () es,env)])
                           (cenv,env'',Raise err,[]))`,
HO_MATCH_MP_TAC small_eval_list_ind >>
rw [] >>
`e_step_reln^* (cenv,env,e',[(Ccon cn vs' () (e::es),env)])
               (cenv,env'',Val v',[(Ccon cn vs' () (e::es),env)])`
             by metis_tac [e_step_add_ctxt, APPEND] >>
`e_step_reln (cenv,env'',Val v',[(Ccon cn vs' () (e::es),env)])
             (cenv,env,e,[(Ccon cn (v'::vs') () es,env)])`
        by rw [push_def,continue_def, e_step_reln_def, e_step_def] >>
`LENGTH vs' + 1 + 1 + LENGTH es = LENGTH vs' + 1 + SUC (LENGTH es)`
                by DECIDE_TAC >>
fs [] >|        
[`e_step_reln^* (cenv,env,e,[(Ccon cn (v'::vs') () es,env)])
                (cenv,env',Raise err,[(Ccon cn (v'::vs') () es,env)])`
             by metis_tac [e_step_add_ctxt,APPEND] >>
     `e_step_reln^* (cenv,env',Raise err,[(Ccon cn (v'::vs') () es,env)])
                    (cenv,env',Raise err,[])`
             by metis_tac [e_step_raise] >>
     metis_tac [RTC_SINGLE, transitive_RTC, transitive_def],
 `LENGTH (v'::vs') + 1 + LENGTH es = LENGTH vs' + 1 + SUC (LENGTH es)`
              by (fs [] >>
                  DECIDE_TAC) >>
     `?env''. e_step_reln^* (cenv,env,e,[(Ccon cn (v'::vs') () es,env)])
                        (cenv,env'',Raise err, [])`
             by metis_tac [] >>
     metis_tac [RTC_SINGLE, transitive_RTC, transitive_def]]);

val small_eval_list_terr = Q.prove (
`!cenv env es r. small_eval_list cenv env es r ⇒
  (!e v err cn vs' env'.
     do_con_check cenv cn (LENGTH vs' + 1 + LENGTH es) ∧
     (r = Rerr Rtype_error) ∧ 
     e_step_reln^* (cenv,env,e,[]) (cenv,env',Val v,[]) ⇒
     ?env'' e' c'. e_step_reln^* (cenv,env,e,[(Ccon cn vs' () es,env)])
                                 (cenv,env'',e',c') ∧
                   (e_step (cenv,env'',e',c') = Etype_error))`,
HO_MATCH_MP_TAC small_eval_list_ind >>
rw [] >>
`e_step_reln^* (cenv,env,e'',[(Ccon cn vs' () (e::es),env)])
               (cenv,env'',Val v',[(Ccon cn vs' () (e::es),env)])`
             by metis_tac [e_step_add_ctxt, APPEND] >>
`e_step_reln (cenv,env'',Val v',[(Ccon cn vs' () (e::es),env)])
             (cenv,env,e,[(Ccon cn (v'::vs') () es,env)])`
        by rw [push_def,continue_def, e_step_reln_def, e_step_def] >>
`LENGTH vs' + 1 + 1 + LENGTH es = LENGTH vs' + 1 + SUC (LENGTH es)`
                by DECIDE_TAC >>
fs [] >|        
[`e_step_reln^* (cenv,env,e,[(Ccon cn (v'::vs') () es,env)])
                (cenv,env',e',c'++[(Ccon cn (v'::vs') () es,env)])`
             by metis_tac [e_step_add_ctxt,APPEND] >>
     `e_step (cenv,env',e',c'++[(Ccon cn (v'::vs') () es,env)]) = Etype_error`
             by metis_tac [e_single_error_add_ctxt] >>
     metis_tac [RTC_SINGLE, transitive_RTC, transitive_def],
 `LENGTH (v'::vs') + 1 + LENGTH es = LENGTH vs' + 1 + SUC (LENGTH es)`
              by (fs [] >>
                  DECIDE_TAC) >>
     `?env'' e' c'. e_step_reln^* (cenv,env,e,[(Ccon cn (v'::vs') () es,env)])
                              (cenv,env'',e',c') ∧
                (e_step (cenv,env'',e',c') = Etype_error)`
             by metis_tac [] >>
     metis_tac [RTC_SINGLE, transitive_RTC, transitive_def]]);

val (small_eval_match_rules, small_eval_match_ind, small_eval_match_cases) = Hol_reln `
(!cenv env v. small_eval_match cenv env v [] (Rerr (Rraise Bind_error))) ∧
(!cenv env p e pes r env' v.
  (pmatch cenv p v env = Match env') ∧
  small_eval cenv env' e [] r
  ⇒
  small_eval_match cenv env v ((p,e)::pes) r) ∧
(!cenv env e p pes r v.
  (pmatch cenv p v env = No_match) ∧
  small_eval_match cenv env v pes r
  ⇒
  small_eval_match cenv env v ((p,e)::pes) r) ∧
(!cenv env p e pes v.
  (pmatch cenv p v env = Match_type_error)
  ⇒
  small_eval_match cenv env v ((p,e)::pes) (Rerr (Rtype_error)))`;

val small_eval_match_thm = Q.prove (
`!cenv env v pes r. small_eval_match cenv env v pes r ⇒
  !env2. small_eval cenv env2 (Val v) [(Cmat () pes,env)] r`,
HO_MATCH_MP_TAC small_eval_match_ind >>
rw [small_eval_def] >|
[qexists_tac `env` >>
     match_mp_tac RTC_SINGLE >>
     rw [e_step_reln_def, e_step_def, continue_def],
 cases_on `r` >|
     [all_tac,
      cases_on `e'`] >>
     fs [small_eval_def] >>
     qexists_tac `env''` >>
     rw [Once RTC_CASES1, e_step_reln_def] >|
     [rw [e_step_def, continue_def],
      qexists_tac `e'` >>
          qexists_tac `c'` >>
          rw [] >>
          rw [e_step_def, continue_def],
      rw [e_step_def, continue_def]],
 cases_on `r` >|
     [all_tac,
      cases_on `e'`] >>
     fs [small_eval_def] >>
     rw [Once RTC_CASES1, e_step_reln_def] >|
     [rw [e_step_def, push_def, continue_def],
      pop_assum (ASSUME_TAC o Q.SPEC `env`) >>
          fs [] >>
          qexists_tac `env'` >>
          qexists_tac `e'` >>
          qexists_tac `c'` >>
          rw [] >>
          rw [e_step_def, push_def, continue_def],
      rw [e_step_def, push_def, continue_def]],
 qexists_tac `env2` >>
     qexists_tac `Val v` >>
     qexists_tac `[(Cmat () ((p,e)::pes),env)]` >>
     rw [RTC_REFL] >>
     rw [e_step_def, continue_def]]);

val big_exp_to_small_exp = Q.prove (
`(∀ cenv env e r.
   evaluate cenv env e r ⇒
   small_eval cenv env e [] r) ∧
 (∀ cenv env es r.
   evaluate_list cenv env es r ⇒
   small_eval_list cenv env es r) ∧
 (∀ cenv env v pes r.
   evaluate_match cenv env v pes r ⇒
   small_eval_match cenv env v pes r)`,
HO_MATCH_MP_TAC evaluate_ind >>
rw [small_eval_app, small_eval_log, small_eval_if, small_eval_match,
    small_eval_let, small_eval_letrec] >|
[rw [small_eval_def] >>
     metis_tac [RTC_REFL],
 rw [small_eval_def] >>
     metis_tac [RTC_REFL],
 cases_on `es` >>
     fs [LENGTH] >>
     rw [small_eval_con, small_eval_con_empty] >|
     [rw [small_eval_def] >>
          fs [Once small_eval_list_cases] >>
          metis_tac [RTC_REFL],
      fs [Once small_eval_list_cases]  >>
          rw [small_eval_def] >>
          `SUC (LENGTH t) = LENGTH ([]:v list) + 1 + LENGTH t` by 
                  (fs [] >>
                   DECIDE_TAC) >>
          `do_con_check cenv cn (LENGTH ([]:v list) + 1 + LENGTH vs')` 
                      by metis_tac [small_eval_list_length] >>
          `e_step_reln^* (cenv,env,h,[(Ccon cn [] () t,env)])
                         (cenv,env,Val (Conv cn (REVERSE ([]:v list)++[v]++vs')),[])`
                    by metis_tac [small_eval_list_step] >>
          fs [] >>
          metis_tac []],
 rw [small_eval_def, e_step_def] >>
     qexists_tac `env` >>
     qexists_tac `Con cn es` >>
     rw [] >>
     metis_tac [RTC_REFL],
 cases_on `es` >>
     rw [small_eval_con, small_eval_con_empty] >>
     fs [Once small_eval_list_cases] >>
     rw [small_eval_def] >|
     [metis_tac [APPEND,e_step_raise, e_step_add_ctxt, transitive_RTC,
                 transitive_def],
      `LENGTH ([]:v list) + 1 + LENGTH t = SUC (LENGTH t)` by 
                 (fs [] >>
                  DECIDE_TAC) >>
          metis_tac [small_eval_list_err],
      metis_tac [APPEND,e_step_raise, e_step_add_ctxt, transitive_RTC,
                 transitive_def, e_single_error_add_ctxt],
      `LENGTH ([]:v list) + 1 + LENGTH t = SUC (LENGTH t)` by 
                 (fs [] >>
                  DECIDE_TAC) >>
          metis_tac [small_eval_list_terr]],
 rw [small_eval_def] >>
     qexists_tac `env` >>
     rw [Once RTC_CASES1, e_step_reln_def, return_def, e_step_def], 
 rw [small_eval_def, e_step_def] >>
     qexists_tac `env` >>
     qexists_tac `Var n` >>
     rw [] >>
     metis_tac [RTC_REFL],
 rw [small_eval_def] >>
     qexists_tac `env` >>
     rw [Once RTC_CASES1, e_step_reln_def, return_def, e_step_def], 
 fs [small_eval_def] >>
     `e_step_reln^* (cenv,env,e,[(Capp1 op () e',env)])
                (cenv,env'',Val v1,[(Capp1 op () e',env)])`
             by metis_tac [e_step_add_ctxt, APPEND] >>
     `e_step_reln (cenv,env'',Val v1,[(Capp1 op () e',env)])
                  (cenv,env,e',[(Capp2 op v1 (),env)])`
             by rw [e_step_def, e_step_reln_def, continue_def, push_def] >>
     `e_step_reln^* (cenv,env,e',[(Capp2 op v1 (),env)])
                    (cenv,env''',Val v2,[(Capp2 op v1 (),env)])`
             by metis_tac [e_step_add_ctxt, APPEND] >>
     `e_step_reln (cenv,env''',Val v2,[(Capp2 op v1 (),env)])
                  (cenv,env',e'',[])`
             by rw [e_step_def, e_step_reln_def, continue_def] >>
     metis_tac [transitive_RTC, RTC_SINGLE, transitive_def,
                small_eval_prefix],
 fs [small_eval_def] >>
     `e_step_reln^* (cenv,env,e,[(Capp1 op () e',env)])
                (cenv,env',Val v1,[(Capp1 op () e',env)])`
             by metis_tac [e_step_add_ctxt, APPEND] >>
     `e_step_reln (cenv,env',Val v1,[(Capp1 op () e',env)])
                  (cenv,env,e',[(Capp2 op v1 (),env)])`
             by rw [e_step_def, e_step_reln_def, continue_def, push_def] >>
     `e_step_reln^* (cenv,env,e',[(Capp2 op v1 (),env)])
                    (cenv,env'',Val v2,[(Capp2 op v1 (),env)])`
             by metis_tac [e_step_add_ctxt, APPEND] >>
     `e_step (cenv,env'',Val v2,[(Capp2 op v1 (),env)]) = Etype_error` 
             by rw [e_step_def, e_step_reln_def, continue_def, push_def] >>
     metis_tac [transitive_RTC, RTC_SINGLE, transitive_def],
 fs [small_eval_def] >>
     `e_step_reln^* (cenv,env,e,[(Capp1 op () e',env)])
                (cenv,env',Val v1,[(Capp1 op () e',env)])`
             by metis_tac [e_step_add_ctxt, APPEND] >>
     `e_step_reln (cenv,env',Val v1,[(Capp1 op () e',env)])
                  (cenv,env,e',[(Capp2 op v1 (),env)])`
             by rw [e_step_def, e_step_reln_def, continue_def, push_def] >>
     `small_eval cenv env e' [(Capp2 op v1 (),env)] (Rerr err)` 
             by metis_tac [small_eval_err_add_ctxt, APPEND] >>
     metis_tac [transitive_RTC, RTC_SINGLE, transitive_def, small_eval_prefix],
 metis_tac [small_eval_err_add_ctxt, APPEND],
 fs [small_eval_def] >>
     `e_step_reln^* (cenv,env,e,[(Clog op () e2,env)])
                (cenv,env',Val v,[(Clog op () e2,env)])`
             by metis_tac [e_step_add_ctxt, APPEND] >>
     `e_step_reln (cenv,env',Val v,[(Clog op () e2,env)])
                  (cenv,env,e',[])`
             by rw [e_step_def, e_step_reln_def, continue_def, push_def] >>
     metis_tac [transitive_RTC, RTC_SINGLE, transitive_def,
                small_eval_prefix],
 fs [small_eval_def] >>
     `e_step_reln^* (cenv,env,e,[(Clog op () e2,env)])
                (cenv,env',Val v,[(Clog op () e2,env)])`
             by metis_tac [e_step_add_ctxt, APPEND] >>
     `e_step (cenv,env',Val v,[(Clog op () e2,env)]) = Etype_error` 
             by rw [e_step_def, e_step_reln_def, continue_def, push_def] >>
     metis_tac [transitive_RTC, RTC_SINGLE, transitive_def],
 metis_tac [small_eval_err_add_ctxt, APPEND],
 fs [small_eval_def] >>
     `e_step_reln^* (cenv,env,e,[(Cif () e2 e3,env)])
                (cenv,env',Val v,[(Cif () e2 e3,env)])`
             by metis_tac [e_step_add_ctxt, APPEND] >>
     `e_step_reln (cenv,env',Val v,[(Cif () e2 e3,env)])
                  (cenv,env,e',[])`
             by rw [e_step_def, e_step_reln_def, continue_def, push_def] >>
     metis_tac [transitive_RTC, RTC_SINGLE, transitive_def,
                small_eval_prefix],
 fs [small_eval_def] >>
     `e_step_reln^* (cenv,env,e,[(Cif () e2 e3,env)])
                (cenv,env',Val v,[(Cif () e2 e3,env)])`
             by metis_tac [e_step_add_ctxt, APPEND] >>
     `e_step (cenv,env',Val v,[(Cif () e2 e3,env)]) = Etype_error` 
             by rw [e_step_def, e_step_reln_def, continue_def, push_def] >>
     metis_tac [transitive_RTC, RTC_SINGLE, transitive_def],
 metis_tac [small_eval_err_add_ctxt, APPEND],
 fs [small_eval_def] >> 
     imp_res_tac small_eval_match_thm >>
     `e_step_reln^* (cenv,env,e,[(Cmat () pes,env)])
                    (cenv,env',Val v,[(Cmat () pes,env)])`
                by metis_tac [APPEND,e_step_add_ctxt] >>
     metis_tac [small_eval_prefix],
 metis_tac [small_eval_err_add_ctxt, APPEND],
 fs [small_eval_def] >>
     `e_step_reln^* (cenv,env,e,[(Clet n () e',env)])
                (cenv,env',Val v,[(Clet n () e',env)])`
             by metis_tac [e_step_add_ctxt, APPEND] >>
     `e_step_reln (cenv,env',Val v,[(Clet n () e',env)])
                  (cenv,bind n v env,e',[])`
             by rw [e_step_def, e_step_reln_def, continue_def, push_def] >>
     metis_tac [transitive_RTC, RTC_SINGLE, transitive_def,
                small_eval_prefix],
 metis_tac [small_eval_err_add_ctxt, APPEND],
 rw [small_eval_def] >>
     qexists_tac `env` >>
     qexists_tac `Letrec funs e` >>
     qexists_tac `[]` >>
     rw [RTC_REFL, e_step_def],
 metis_tac [small_eval_list_rules],
 fs [small_eval_def] >>
     metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules],
 cases_on `err` >> 
     fs [small_eval_def] >>
     metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules], 
 cases_on `err` >> 
     fs [small_eval_def] >>
     metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules], 
 metis_tac [small_eval_match_rules],
 metis_tac [small_eval_match_rules],
 metis_tac [small_eval_match_rules],
 metis_tac [small_eval_match_rules]]);

val evaluate_val = Q.prove (
`!cenv env v v' err.
  (evaluate cenv env (Val v) (Rval v') = (v = v')) ∧
  ¬(evaluate cenv env (Val v) (Rerr err))`,
rw [Once evaluate_cases] >>
rw [Once evaluate_cases] >>
metis_tac []);

val evaluate_list_val = Q.prove (
`!cenv env vs vs'.
  evaluate_list cenv env (MAP Val vs) (Rval vs') = (vs = vs')`,
induct_on `vs` >>
rw [] >>
rw [Once evaluate_cases] >-
metis_tac [] >>
EQ_TAC >>
rw [evaluate_val]);

val evaluate_list_middle = Q.prove (
`!cenv env vs e es v r.
  evaluate cenv env e (Rval v) ∧
  evaluate_list cenv env (vs ++ [Val v] ++ es) r
  ⇒
  evaluate_list cenv env (vs ++ [e] ++ es) r`,
induct_on `vs` >>
rw [] >>
rw [Once evaluate_cases] >>
pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once evaluate_cases]) >>
fs [] >>
rw [] >>
fs [evaluate_val] >>
metis_tac []);

val evaluate_list_middle_error = Q.prove (
`!cenv env vs e es err r.
  evaluate cenv env e (Rerr err)
  ⇒
  evaluate_list cenv env (MAP Val vs ++ [e] ++ es) (Rerr err)`,
induct_on `vs` >>
rw [] >>
rw [Once evaluate_cases, evaluate_val]);

val evaluate_raise = Q.prove (
`!cenv env err bv.
  (evaluate cenv env (Raise err) bv = (bv = Rerr (Rraise err)))`,
rw [Once evaluate_cases]);

val evaluate_ctxts_cons = Q.prove (
`!cenv f cs v bv.
  evaluate_ctxts cenv (f::cs) v bv = 
  (?c env v'. 
     (f = (c,env)) ∧
     evaluate_ctxt cenv env c v (Rval v') ∧
     evaluate_ctxts cenv cs v' bv) ∨
  (?c env err.
     (f = (c,env)) ∧
     (bv = Rerr err) ∧
     evaluate_ctxt cenv env c v (Rerr err))`,
rw [] >>
rw [Once evaluate_ctxts_cases] >>
EQ_TAC >>
rw [] >>
metis_tac []);


fun TAC q = 
fs [evaluate_state_cases] >>
ONCE_REWRITE_TAC [evaluate_cases] >>
rw [] >>
fs [evaluate_ctxts_cons, evaluate_ctxt_cases] >>
qpat_assum `evaluate cenv env ^q p1`
           (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once evaluate_cases]) >>
fs [evaluate_val] >>
metis_tac [];

val one_step_backward = Q.prove (
`!cenv env e c cenv' env' e' c' bv.
  (e_step (cenv,env,e,c) = Estep (cenv',env',e',c')) ∧
  evaluate_state (cenv',env',e',c') bv
  ⇒
  evaluate_state (cenv,env,e,c) bv`,
rw [e_step_def] >>
cases_on `e` >>
fs [] >>
every_case_tac >>
fs [push_def,return_def] >>
rw [] >|
[fs [evaluate_state_cases, Once evaluate_cases],
 fs [continue_def] >>
     cases_on `c` >>
     fs [] >>
     cases_on `h` >> 
     fs [] >>
     cases_on `q` >> 
     fs [] >>
     every_case_tac >>
     fs [push_def, return_def] >>
     rw [] >>
     fs [evaluate_state_cases, evaluate_val, evaluate_ctxts_cons,
         evaluate_ctxt_cases, evaluate_raise, do_con_check_def] >|
     [qpat_assum `evaluate cenv env' (App o' (Val v) (Val v')) p1`
               (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once evaluate_cases]) >>
          rw [Once evaluate_cases, evaluate_val] >-
          metis_tac [],
      cases_on `err` >>
          disj2_tac >>
          qpat_assum `evaluate cenv env' (App o' (Val v) (Val v')) p1`
               (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once evaluate_cases]) >>
          rw [Once evaluate_cases, evaluate_val] >>
          metis_tac [],
      cases_on `err` >>
          disj2_tac >>
          rw [Once evaluate_cases, evaluate_val] >>
          metis_tac [],
      rw [Once evaluate_cases, evaluate_val] >>
          metis_tac [],
      cases_on `err` >>
          disj2_tac >>
          rw [Once evaluate_cases, evaluate_val] >>
          metis_tac [],
      rw [Once evaluate_cases, evaluate_val] >>
          metis_tac [],
      cases_on `err` >>
          disj2_tac >>
          rw [Once evaluate_cases, evaluate_val] >>
          metis_tac [],
      rw [Once evaluate_cases, evaluate_val] >>
          metis_tac [],
      cases_on `err` >>
          disj2_tac >>
          rw [Once evaluate_cases, evaluate_val] >>
          metis_tac [],
      disj2_tac >>
          rw [Once evaluate_cases, evaluate_val] >>
          rw [Once evaluate_cases],
      rw [Once evaluate_cases, evaluate_val] >>
          fs [Once evaluate_cases, evaluate_val] >>
          metis_tac [],
      cases_on `err` >>
          disj2_tac >>
          fs [Once evaluate_cases, evaluate_val] >>
          rw [Once evaluate_cases, evaluate_val],
      rw [Once evaluate_cases, evaluate_val] >>
          rw [Once evaluate_cases, evaluate_val] >>
          metis_tac [],
      cases_on `err` >>
          disj2_tac >>
          rw [Once evaluate_cases, evaluate_val] >>
          rw [Once evaluate_cases, evaluate_val] >>
          metis_tac [],
      rw [Once evaluate_cases, evaluate_val] >>
          metis_tac [],
      cases_on `err` >>
          disj2_tac >>
          rw [Once evaluate_cases, evaluate_val] >>
          metis_tac [],
      every_case_tac >>
          fs [] >>
          rw [Once evaluate_cases, do_con_check_def] >>
          metis_tac [evaluate_list_val, MAP_APPEND, MAP],
      every_case_tac >>
          fs [] >>
          rw [] >>
          full_simp_tac (srw_ss()++ARITH_ss) [],
      every_case_tac >>
          fs [] >>
          rw [] >>
          full_simp_tac (srw_ss()++ARITH_ss) [],
      every_case_tac >>
          fs [] >>
          rw [] >>
          full_simp_tac (srw_ss()++ARITH_ss) [],
      rw [Once evaluate_cases] >>
          qpat_assum `evaluate cenv env' (Con s p1) p2` 
                (ASSUME_TAC o SIMP_RULE (srw_ss()) 
                     [Once evaluate_cases]) >>
          fs [] >>
          `!x.
             MAP Val (REVERSE l) ++ [Val v; x] ++ t' =
             MAP Val (REVERSE (v::l)) ++ [x] ++ t'`
                     by rw [] >>
          metis_tac [evaluate_list_middle],
      disj2_tac >>
          rw [Once evaluate_cases] >>
          qpat_assum `evaluate cenv env' (Con s p1) p2` 
                (ASSUME_TAC o SIMP_RULE (srw_ss()) 
                     [Once evaluate_cases]) >>
          fs [do_con_check_def] >>
          every_case_tac >>
          full_simp_tac (srw_ss() ++ ARITH_ss) [] >>
          `!x.
             MAP Val (REVERSE l) ++ [Val v; x] ++ t' =
             MAP Val (REVERSE (v::l)) ++ [x] ++ t'`
                     by rw [] >>
          metis_tac [evaluate_list_middle],
      disj2_tac >>
          rw [Once evaluate_cases, do_con_check_def] >>
          rw [] >>
          every_case_tac >>
          full_simp_tac (srw_ss() ++ ARITH_ss) [] >>
          `!x.
             MAP Val (REVERSE l) ++ [Val v; x] ++ t' =
             MAP Val (REVERSE (v::l)) ++ [x] ++ t'`
                     by rw [] >>
          metis_tac [evaluate_list_middle_error]],
 fs [evaluate_state_cases] >>
     ONCE_REWRITE_TAC [evaluate_cases] >>
     fs [evaluate_val] >>
     ONCE_REWRITE_TAC [evaluate_cases] >>
     rw [],
 fs [evaluate_state_cases] >>
     ONCE_REWRITE_TAC [evaluate_cases] >>
     ONCE_REWRITE_TAC [hd (tl (CONJUNCTS evaluate_cases))] >>
     rw [] >>
     fs [evaluate_ctxts_cons, evaluate_ctxt_cases] >>
     qpat_assum `evaluate cenv env (Con s (Val v::t)) p1`
                (ASSUME_TAC o SIMP_RULE (srw_ss()) 
                                 [Once evaluate_cases,
                                  Once (hd (tl (CONJUNCTS evaluate_cases)))]) >>
     fs [evaluate_val] >>
     fs [] >> 
     rw [] >-
     metis_tac [] >>
     pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once evaluate_cases]) >>
     fs [evaluate_val] >>
     metis_tac [optionTheory.NOT_SOME_NONE, optionTheory.SOME_11],
 fs [evaluate_state_cases] >>
     ONCE_REWRITE_TAC [evaluate_cases] >>
     fs [evaluate_val],
 fs [evaluate_state_cases] >>
     fs [Once evaluate_cases] >>
     metis_tac [],
 fs [evaluate_state_cases] >>
     ONCE_REWRITE_TAC [evaluate_cases] >>
     rw [] >>
     fs [evaluate_ctxts_cons, evaluate_ctxt_cases] >>
     qpat_assum `evaluate cenv env (App o' (Val v) e0) p1`
                (ASSUME_TAC o SIMP_RULE (srw_ss()) 
                     [Once evaluate_cases]) >>
     fs [evaluate_val] >>
     metis_tac [],
 TAC ``Log l (Val v) e0``,
 TAC ``If (Val v) e0 e1``,
 TAC ``Mat (Val v) l``,
 TAC ``Let s (Val v) e0``,
 fs [evaluate_state_cases] >>
     ONCE_REWRITE_TAC [evaluate_cases] >>
     fs [] >>
     metis_tac []]);

val one_step_backward_type_error = Q.prove (
`!cenv env e c.
  (e_step (cenv,env,e,c) = Etype_error)
  ⇒
  evaluate_state (cenv,env,e,c) (Rerr Rtype_error)`,
rw [e_step_def] >>
cases_on `e` >>
fs [] >>
every_case_tac >>
fs [push_def,return_def] >>
rw [evaluate_state_cases] >|
[fs [continue_def] >>
     cases_on `c` >>
     fs [] >>
     cases_on `h` >>
     fs [] >>
     cases_on `q` >>
     fs [] >>
     every_case_tac >>
     fs [push_def, evaluate_val, return_def] >>
     rw [evaluate_ctxts_cons, evaluate_ctxt_cases] >>
     disj2_tac >>
     rw [Once evaluate_cases, evaluate_val] >>
     full_simp_tac (srw_ss() ++ ARITH_ss) [] >>
     rw [Once evaluate_cases],
 disj2_tac >>
     rw [Once evaluate_cases],
 disj2_tac >>
     rw [Once evaluate_cases],
 disj2_tac >>
     rw [Once evaluate_cases],
 disj2_tac >>
     rw [Once evaluate_cases]]);

val small_exp_to_big_exp = Q.prove (
`!st st'. e_step_reln^* st st' ⇒
  !r.
    evaluate_state st' r
    ⇒
    evaluate_state st r`,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 >>
rw [e_step_reln_def] >>
`?cenv env e c. st = (cenv, env, e, c)` 
        by (cases_on `st` >>
            cases_on `r'` >>
            cases_on `r''` >>
            rw []) >>
rw [] >>
`?cenv' env' e' c'. st' = (cenv', env', e', c')` 
        by (cases_on `st'` >>
            cases_on `r'` >>
            cases_on `r''` >>
            rw []) >>
rw [] >>
`?cenv'' env'' e'' c''. st'' = (cenv'', env'', e'', c'')` 
        by (cases_on `st''` >>
            cases_on `r'` >>
            cases_on `r''` >>
            rw []) >>
rw [] >>
metis_tac [one_step_backward]);

val evaluate_state_no_ctxt = Q.prove (
`!envc env e r. evaluate_state (envc,env,e,[]) r = evaluate envc env e r`,
rw [evaluate_state_cases, Once evaluate_ctxts_cases] >>
cases_on `r` >>
rw [] >>
metis_tac []);

val small_big_exp_equiv = Q.store_thm ("small_big_exp_equiv",
`!envc env e r. small_eval envc env e [] r = evaluate envc env e r`,
rw [] >>
cases_on `r` >|
[all_tac,
 cases_on `e'`] >>
rw [small_eval_def] >>
EQ_TAC >>
rw [] >>
metis_tac [evaluate_val, small_exp_to_big_exp, big_exp_to_small_exp, 
           evaluate_state_no_ctxt, small_eval_def, evaluate_raise, 
           one_step_backward_type_error]);

val lift_small_exp_to_dec_one_step = Q.prove (
`!cenv env e c cenv' env' e' c' cenv'' env'' ds p.
  e_step_reln (cenv,env,e,c) (cenv',env',e',c') 
  ⇒
  d_step_reln (cenv'',env'',ds,SOME (p,(cenv,env,e,c)))
              (cenv'',env'',ds,SOME (p,(cenv',env',e',c')))`,
rw [e_step_reln_def, d_step_reln_def, d_step_def] >>
every_case_tac >>
fs [e_step_def, continue_def, push_def, return_def] >>
rw []);

val lift_small_exp_to_dec = Q.prove (
`!st st'. e_step_reln^* st st' ⇒ 
   !p cenv'' env'' ds.
     d_step_reln^* (cenv'',env'',ds,SOME (p,st)) (cenv'',env'',ds,SOME (p,st'))`,
HO_MATCH_MP_TAC RTC_INDUCT >>
rw [] >>
`?cenv env e c. st = (cenv, env, e, c)` 
        by (cases_on `st` >>
            cases_on `r` >>
            cases_on `r'` >>
            rw []) >>
rw [] >>
`?cenv' env' e' c'. st' = (cenv', env', e', c')` 
        by (cases_on `st'` >>
            cases_on `r` >>
            cases_on `r'` >>
            rw []) >>
rw [] >>
metis_tac [lift_small_exp_to_dec_one_step, transitive_def, transitive_RTC,
           RTC_SINGLE]);

val big_dec_to_small_dec = Q.prove (
`!cenv env ds r.
  evaluate_decs cenv env ds r ⇒ d_small_eval cenv env ds NONE r`,
HO_MATCH_MP_TAC evaluate_decs_ind >>
rw [d_small_eval_def] >|
[metis_tac [RTC_REFL],
 cases_on `r` >>
     fs [d_small_eval_def] >|
     [`d_step_reln (cenv,env,Dlet p e::ds,NONE) 
                   (cenv,env,ds,SOME(p,cenv,env,e,[]))`
                by (rw [d_step_reln_def, d_step_def]) >>
          imp_res_tac big_exp_to_small_exp >>
          fs [small_eval_def] >>
          `d_step_reln^* (cenv,env,ds,SOME (p,(cenv,env,e,[])))
                         (cenv,env,ds,SOME (p,(cenv,env'',Val v,[])))`
                       by metis_tac [lift_small_exp_to_dec] >>
          `d_step_reln (cenv,env,ds,SOME (p,(cenv,env'',Val v,[])))
                         (cenv,env',ds,NONE)`
                by rw [d_step_reln_def, d_step_def] >>
          metis_tac [RTC_SINGLE, transitive_RTC, transitive_def],
      cases_on `e'` >>
          fs [d_small_eval_def] >>
          `d_step_reln (cenv,env,Dlet p e::ds,NONE) 
                   (cenv,env,ds,SOME(p,cenv,env,e,[]))`
                by (rw [d_step_reln_def, d_step_def]) >>
          imp_res_tac big_exp_to_small_exp >>
          fs [small_eval_def] >>
          `d_step_reln^* (cenv,env,ds,SOME (p,(cenv,env,e,[])))
                         (cenv,env,ds,SOME (p,(cenv,env''',Val v,[])))`
                       by metis_tac [lift_small_exp_to_dec] >>
          `d_step_reln (cenv,env,ds,SOME (p,(cenv,env''',Val v,[])))
                         (cenv,env',ds,NONE)`
                by rw [d_step_reln_def, d_step_def] >>
          metis_tac [RTC_SINGLE, transitive_RTC, transitive_def]],
 `d_step_reln (cenv,env,Dlet p e::ds,NONE) 
                   (cenv,env,ds,SOME(p,cenv,env,e,[]))`
                by (rw [d_step_reln_def, d_step_def]) >>
     imp_res_tac big_exp_to_small_exp >>
     fs [small_eval_def] >>
     `d_step_reln^* (cenv,env,ds,SOME (p,(cenv,env,e,[])))
                    (cenv,env,ds,SOME (p,(cenv,env',Val v,[])))`
                  by metis_tac [lift_small_exp_to_dec] >>
     `d_step (cenv,env,ds,SOME (p,(cenv,env',Val v,[]))) = Draise Bind_error`
               by rw [d_step_reln_def, d_step_def] >>
     metis_tac [RTC_SINGLE, transitive_RTC, transitive_def],
 `d_step_reln (cenv,env,Dlet p e::ds,NONE) 
                   (cenv,env,ds,SOME(p,cenv,env,e,[]))`
                by (rw [d_step_reln_def, d_step_def]) >>
     imp_res_tac big_exp_to_small_exp >>
     fs [small_eval_def] >>
     `d_step_reln^* (cenv,env,ds,SOME (p,(cenv,env,e,[])))
                    (cenv,env,ds,SOME (p,(cenv,env',Val v,[])))`
                  by metis_tac [lift_small_exp_to_dec] >>
     `d_step (cenv,env,ds,SOME (p,(cenv,env',Val v,[]))) = Dtype_error`
               by rw [d_step_reln_def, d_step_def] >>
     metis_tac [RTC_SINGLE, transitive_RTC, transitive_def],
 cases_on `err` >>
     fs [d_small_eval_def] >>
     `d_step_reln (cenv,env,Dlet p e::ds,NONE) 
                   (cenv,env,ds,SOME(p,cenv,env,e,[]))`
                by (rw [d_step_reln_def, d_step_def]) >>
     imp_res_tac big_exp_to_small_exp >>
     fs [small_eval_def] >|
     [`d_step_reln^* (cenv,env,ds,SOME (p,(cenv,env,e,[])))
                     (cenv,env,ds,SOME (p,(cenv,env',e',c')))`
                   by metis_tac [lift_small_exp_to_dec] >>
          `d_step (cenv,env,ds,SOME (p,(cenv,env',e',c'))) = Dtype_error`
                 by (rw [d_step_def] >>
                     every_case_tac >>
                     fs [] >>
                     fs [e_step_def, continue_def]) >>
          metis_tac [RTC_SINGLE, transitive_RTC, transitive_def],
      `d_step_reln^* (cenv,env,ds,SOME (p,(cenv,env,e,[])))
                     (cenv,env,ds,SOME (p,(cenv,env',Raise e',[])))`
                   by metis_tac [lift_small_exp_to_dec] >>
          `d_step (cenv,env,ds,SOME (p,(cenv,env',Raise e',[]))) = Draise e'`
                 by (rw [d_step_def] >>
                     every_case_tac >>
                     fs [] >>
                     fs [e_step_def, continue_def]) >>
          metis_tac [RTC_SINGLE, transitive_RTC, transitive_def]],
 cases_on `r` >|
     [all_tac,
      cases_on `e`] >>
     fs [d_small_eval_def] >>
     `d_step_reln (cenv,env,Dletrec funs::ds,NONE)
                  (cenv,build_rec_env funs env, ds, NONE)`
               by rw [d_step_reln_def, d_step_def] >>
     metis_tac [RTC_SINGLE, transitive_RTC, transitive_def],
 `d_step (cenv,env,Dletrec funs::ds,NONE) = Dtype_error`
        by rw [d_step_def] >>
     metis_tac [RTC_REFL, transitive_RTC, transitive_def],
 cases_on `r` >|
     [all_tac,
      cases_on `e`] >>
     fs [d_small_eval_def] >>
     `d_step_reln (cenv,env,Dtype tds::ds,NONE) 
                  (build_tdefs tds ++ cenv,env,ds,NONE)`
               by rw [d_step_reln_def, d_step_def] >>
     metis_tac [merge_def,RTC_SINGLE, transitive_RTC, transitive_def],
 `d_step (cenv,env,Dtype tds::ds,NONE) = Dtype_error`
               by rw [d_step_def] >>
     metis_tac [RTC_REFL, transitive_RTC, transitive_def]]);

val (evaluate_d_state_rules, evaluate_d_state_ind, evaluate_d_state_cases) = Hol_reln `
(!cenv env ds r.
   evaluate_decs cenv env ds r
   ⇒
   evaluate_d_state (cenv,env,ds,NONE) r) ∧

(!cenv env ds p cenv' env' e c v r.
  evaluate_state (cenv',env',e,c) (Rval v) ∧
  evaluate_decs cenv env (Dlet p (Val v)::ds) r
  ⇒
  evaluate_d_state (cenv,env,ds,SOME (p,(cenv',env',e,c))) r) ∧

(!cenv env ds p cenv' env' e c err.
  evaluate_state (cenv',env',e,c) (Rerr err)
  ⇒
  evaluate_d_state (cenv,env,ds,SOME (p,(cenv',env',e,c))) (Rerr err))`;

val one_step_backward_dec = Q.prove (
`!cenv env ds c cenv' env' ds' c' r.
  (d_step (cenv,env,ds,c) = Dstep (cenv',env',ds',c')) ∧
  evaluate_d_state (cenv',env',ds',c') r
  ⇒
  evaluate_d_state (cenv,env,ds,c) r`,
rw [d_step_def] >>
cases_on `c` >>
fs [] >>
every_case_tac >>
fs [] >>
rw [] >-
(fs [evaluate_d_state_cases] >>
     rw [] >>
     fs [evaluate_state_no_ctxt] >>
     fs [Once evaluate_decs_cases, evaluate_val] >>
     metis_tac []) >-
(fs [evaluate_d_state_cases] >>
     rw [Once evaluate_decs_cases] >>
     rw []) >-
(fs [evaluate_d_state_cases] >>
     rw [Once evaluate_decs_cases] >>
     rw []) >-
(fs [evaluate_d_state_cases] >>
     rw [] >>
     fs [evaluate_state_no_ctxt] >>
     fs [evaluate_val] >>
     rw [Once evaluate_decs_cases, evaluate_val] >>
     metis_tac []) >>
fs [evaluate_d_state_cases] >>
rw [] >>
metis_tac [one_step_backward]);

val one_step_backward_dec_type_error = Q.prove (
`!cenv env ds c.
  (d_step (cenv,env,ds,c) = Dtype_error)
  ⇒
  evaluate_d_state (cenv,env,ds,c) (Rerr Rtype_error)`,
rw [d_step_def] >>
cases_on `c` >>
fs [] >>
every_case_tac >>
fs [] >>
rw [evaluate_d_state_cases] >-
rw [Once evaluate_decs_cases] >-
rw [Once evaluate_decs_cases] >-
rw [Once evaluate_decs_cases, evaluate_state_no_ctxt, evaluate_val] >>
metis_tac [one_step_backward_type_error]);

val one_step_backward_dec_error = Q.prove (
`!cenv env ds c err.
  (d_step (cenv,env,ds,c) = Draise err)
  ⇒
  evaluate_d_state (cenv,env,ds,c) (Rerr (Rraise err))`,
rw [d_step_def] >>
cases_on `c` >>
fs [] >>
every_case_tac >>
fs [] >>
rw [evaluate_d_state_cases, evaluate_state_no_ctxt, evaluate_raise] >>
rw [Once evaluate_decs_cases, evaluate_val]);
 
val small_dec_to_big_dec = Q.prove (
`!st st'. d_step_reln^* st st' ⇒
  !r.
    evaluate_d_state st' r
    ⇒
    evaluate_d_state st r`,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 >>
rw [d_step_reln_def] >>
`?cenv env ds c. st = (cenv, env, ds, c)` 
        by (cases_on `st` >>
            cases_on `r'` >>
            cases_on `r''` >>
            rw []) >>
rw [] >>
`?cenv' env' ds' c'. st' = (cenv', env', ds', c')` 
        by (cases_on `st'` >>
            cases_on `r'` >>
            cases_on `r''` >>
            rw []) >>
rw [] >>
`?cenv'' env'' ds'' c''. st'' = (cenv'', env'', ds'', c'')` 
        by (cases_on `st''` >>
            cases_on `r'` >>
            cases_on `r''` >>
            rw []) >>
rw [] >>
metis_tac [one_step_backward_dec]);

val evaluate_d_state_no_ctxt = Q.prove (
`!envc env ds r. 
  evaluate_d_state (envc,env,ds,NONE) r = evaluate_decs envc env ds r`,
rw [evaluate_d_state_cases]);

val evaluate_d_state_val = Q.prove (
`!cenv env. evaluate_d_state (cenv,env,[],NONE) (Rval env)`,
rw [evaluate_d_state_cases] >>
rw [Once evaluate_decs_cases]);

val small_big_equiv = Q.store_thm ("small_big_equiv",
`!envc env ds r. d_small_eval envc env ds NONE r = evaluate_decs envc env ds r`,
rw [] >>
cases_on `r` >|
[all_tac,
 cases_on `e`] >>
rw [d_small_eval_def] >>
EQ_TAC >>
rw [] >>
metis_tac [small_dec_to_big_dec, big_dec_to_small_dec, evaluate_d_state_val,
           d_small_eval_def, one_step_backward_dec_type_error,
           evaluate_d_state_no_ctxt, one_step_backward_dec_error]);

val _ = export_theory ();
