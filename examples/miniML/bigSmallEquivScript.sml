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

val e_step_reln_def = Define `
  e_step_reln st1 st2 = (e_step st1 = Estep st2)`;

val small_eval_def = Define `
  (small_eval cenv env e c (Rval v) =
     ?env'. e_step_reln^* (cenv,env,e,c) (cenv,env',Val v,[])) ∧
  (small_eval cenv env e c (Rerr (Rraise err)) =
     ?env'. e_step_reln^* (cenv,env,e,c) (cenv,env',Raise err,[])) ∧
  (small_eval cenv env e c (Rerr Rtype_error) =
     ?env' e' c'. 
       e_step_reln^* (cenv,env,e,c) (cenv,env',e',c') ∧
       (e_step (cenv,env',e',c') = Etype_error))`;

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
rw [] >>
cases_on `r` >|
[all_tac,
 cases_on `e`] >>
rw [small_eval_def] >>
EQ_TAC >>
rw [] >|
[pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once RTC_CASES1]) >>
     fs [return_def, e_step_reln_def, e_step_def, push_def] >>
     every_case_tac >>
     fs [] >>
     metis_tac [],
 rw [return_def, Once RTC_CASES1, e_step_reln_def, e_step_def, push_def] >>
     metis_tac [],
 qpat_assum `e_step_reln^* spat1 spat2`
             (ASSUME_TAC o 
              SIMP_RULE (srw_ss()) [Once RTC_CASES1,e_step_reln_def, 
                                    e_step_def, push_def]) >>
     fs [] >>
     every_case_tac >>
     fs [return_def] >>
     rw [] >-
     (fs [e_step_def, push_def] >>
      pop_assum MP_TAC >>
      rw [return_def]) >>
     metis_tac [],
 rw [return_def, Once RTC_CASES1, e_step_reln_def, Once e_step_def, push_def] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once RTC_CASES1]) >>
     fs [e_step_reln_def, e_step_def, push_def, return_def] >>
     every_case_tac >>
     fs [] >>
     metis_tac [],
 rw [return_def, Once RTC_CASES1, e_step_reln_def, Once e_step_def, push_def] >>
     metis_tac []];

(*
val small_eval_con_empty = Q.prove (
`!cenv env cn ns c r.
  (lookup cn cenv = SOME (0,ns))
  ⇒
  (small_eval cenv env (Con cn []) c r =
   small_eval cenv env (Val (Conv cn [])) c r)`,
small_eval_step_tac);

val small_eval_con = Q.prove (
`!cenv env cn e1 es ns c r.
  (lookup cn cenv = SOME (LENGTH (e1::es),ns))
  ⇒
  (small_eval cenv env (Con cn (e1::es)) c r =
   small_eval cenv env e1 ((Ccon cn [] () es,env)::c) r)`,
small_eval_step_tac);
*)

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

(*
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

val small_eval_list_step = Q.prove (
`!cenv env es r. small_eval_list cenv env es r ⇒
  (!e v vs cn vs' env'.
     (r = Rval vs) ∧ e_step_reln^* (cenv,env,e,[]) (cenv,env',Val v,[]) ⇒
     e_step_reln^* (cenv,env,e,[(Ccon cn vs' () es,env)])
                   (cenv,env,Val (Conv cn (REVERSE vs'++[v]++vs)),[]))`,
HO_MATCH_MP_TAC small_eval_list_ind >>
rw [] >|
[`e_step_reln^* (cenv,env,e,[(Ccon cn vs' () [],env)])
                (cenv,env',Val v,[(Ccon cn vs' () [],env)])`
             by metis_tac [e_step_add_ctxt,APPEND] >>
     `e_step_reln (cenv,env',Val v,[(Ccon cn vs' () [],env)])
                  (cenv,env,Val (Conv cn (REVERSE vs' ++ [v] ++ [])),[])`
             by rw [return_def, continue_def, e_step_reln_def, e_step_def] >>
     metis_tac [transitive_RTC, transitive_def, RTC_SINGLE, APPEND],
 `e_step_reln^* (cenv,env,e,[(Ccon cn (v'::vs'') () es,env)])
                (cenv,env,Val (Conv cn (REVERSE vs'' ++ [v'] ++ [v] ++ vs)),[])`
             by metis_tac [REVERSE_DEF] >>
     `e_step_reln^* (cenv,env,e',[(Ccon cn vs'' () (e::es),env)])
                    (cenv,env'',Val v',[(Ccon cn vs'' () (e::es),env)])`
             by metis_tac [e_step_add_ctxt, APPEND] >>
     `e_step_reln (cenv,env'',Val v',[(Ccon cn vs'' () (e::es),env)])
                  (cenv,env,e,[(Ccon cn (v'::vs'') () es,env)])`
             by rw [push_def,continue_def, e_step_reln_def, e_step_def] >>
     metis_tac [APPEND_ASSOC, APPEND, RTC_SINGLE, transitive_RTC,
                transitive_def]]);

val small_eval_list_err = Q.prove (
`!cenv env es r. small_eval_list cenv env es r ⇒
  (!e v err cn vs' env'.
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
        by rw [push_def,continue_def, e_step_reln_def, e_step_def] >|
[`e_step_reln^* (cenv,env,e,[(Ccon cn (v'::vs') () es,env)])
                (cenv,env',Raise err,[(Ccon cn (v'::vs') () es,env)])`
             by metis_tac [e_step_add_ctxt,APPEND] >>
     `e_step_reln^* (cenv,env',Raise err,[(Ccon cn (v'::vs') () es,env)])
                    (cenv,env',Raise err,[])`
             by metis_tac [e_step_raise] >>
     metis_tac [RTC_SINGLE, transitive_RTC, transitive_def],
 `?env''. e_step_reln^* (cenv,env,e,[(Ccon cn (v'::vs') () es,env)])
                        (cenv,env'',Raise err, [])`
             by metis_tac [] >>
     metis_tac [RTC_SINGLE, transitive_RTC, transitive_def]]);

val small_eval_list_terr = Q.prove (
`!cenv env es r. small_eval_list cenv env es r ⇒
  (!e v err cn vs' env'.
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
        by rw [push_def,continue_def, e_step_reln_def, e_step_def] >|
[`e_step_reln^* (cenv,env,e,[(Ccon cn (v'::vs') () es,env)])
                (cenv,env',e',c'++[(Ccon cn (v'::vs') () es,env)])`
             by metis_tac [e_step_add_ctxt,APPEND] >>
     `e_step (cenv,env',e',c'++[(Ccon cn (v'::vs') () es,env)]) = Etype_error`
             by metis_tac [e_single_error_add_ctxt] >>
     metis_tac [RTC_SINGLE, transitive_RTC, transitive_def],
 `?env'' e' c'. e_step_reln^* (cenv,env,e,[(Ccon cn (v'::vs') () es,env)])
                              (cenv,env'',e',c') ∧
                (e_step (cenv,env'',e',c') = Etype_error)`
             by metis_tac [] >>
     metis_tac [RTC_SINGLE, transitive_RTC, transitive_def]]);
*)

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
 (*
 cases_on `es` >>
     rw [small_eval_con, small_eval_con_empty] >|
     [rw [small_eval_def] >>
          fs [Once small_eval_list_cases] >>
          metis_tac [RTC_REFL],
      fs [Once small_eval_list_cases]  >>
          rw [small_eval_def] >>
          `e_step_reln^* (cenv,env,h,[(Ccon cn [] () t,env)])
                         (cenv,env,Val (Conv cn (REVERSE []++[v]++vs')),[])`
                    by metis_tac [small_eval_list_step] >>
          fs [] >>
          metis_tac []],
 *)
 all_tac,
 rw [small_eval_def, e_step_def] >>
     qexists_tac `env` >>
     qexists_tac `Con cn es` >>
     rw [] >>
     metis_tac [RTC_REFL],
 (*
 cases_on `es` >>
     rw [small_eval_con, small_eval_con_empty] >>
     fs [Once small_eval_list_cases] >>
     rw [small_eval_def] >|
     [metis_tac [APPEND,e_step_raise, e_step_add_ctxt, transitive_RTC,
                 transitive_def],
      metis_tac [small_eval_list_err],
      metis_tac [APPEND,e_step_raise, e_step_add_ctxt, transitive_RTC,
                 transitive_def, e_single_error_add_ctxt],
      metis_tac [small_eval_list_terr]],
 *)
 all_tac,
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
 (*metis_tac [small_eval_list_rules],
 fs [small_eval_def] >>
     metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules],
 cases_on `err` >> 
     fs [small_eval_def] >>
     metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules], 
 cases_on `err` >> 
     fs [small_eval_def] >>
     metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules], 
 *)
 all_tac,
 all_tac,
 all_tac,
 all_tac,
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
          metis_tac [evaluate_list_val, MAP_APPEND, MAP]
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
      all_tac,
      all_tac,
      all_tac],
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
     metis_tac []]


      rw [Once evaluate_cases] >>
          qpat_assum `evaluate cenv env' (Con s p1) p2` 
                (ASSUME_TAC o SIMP_RULE (srw_ss()) 
                     [Once evaluate_cases]) >>
          fs []


          metis_tac [evaluate_list_val, MAP_APPEND, MAP]






metis_tac []
val _ = export_theory ();
