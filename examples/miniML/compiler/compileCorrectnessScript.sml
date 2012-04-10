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

(* TODO: add to MiniMLTerminationTheory? *)
val _ = augment_srw_ss[rewrites[lookup_def]]

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

(* nicer induction theorem for evaluate *)
(* TODO: move? *)

val (evaluate_list_with_rules,evaluate_list_with_ind,evaluate_list_with_cases) = Hol_reln`
(evaluate_list_with P [] (Rval [])) ∧
(P e (Rval v) ∧
 evaluate_list_with P es (Rval vs) ⇒
 evaluate_list_with P (e::es) (Rval (v::vs))) ∧
(P e (Rval v) ∧
 evaluate_list_with P es (Rerr err) ⇒
 evaluate_list_with P (e::es) (Rerr err)) ∧
(P e (Rerr err) ⇒
 evaluate_list_with P (e::es) (Rerr err))`

val evaluate_list_with_evaluate = store_thm(
"evaluate_list_with_evaluate",
``∀cenv env. evaluate_list cenv env = evaluate_list_with (evaluate cenv env)``,
ntac 2 gen_tac >>
simp_tac std_ss [Once FUN_EQ_THM] >>
Induct >>
rw[FUN_EQ_THM] >-
  rw[Once evaluate_cases,Once evaluate_list_with_cases] >>
rw[Once evaluate_cases] >>
rw[Once evaluate_list_with_cases,SimpRHS] >>
PROVE_TAC[])

val (evaluate_match_with_rules,evaluate_match_with_ind,evaluate_match_with_cases) = Hol_reln`
(evaluate_match_with P cenv env v [] (Rerr (Rraise Bind_error))) ∧
(ALL_DISTINCT (pat_bindings p []) ∧
 (pmatch cenv p v env = Match env') ∧
 P cenv env' e bv ⇒
 evaluate_match_with P cenv env v ((p,e)::pes) bv) ∧
(ALL_DISTINCT (pat_bindings p []) ∧
 (pmatch cenv p v env = No_match) ∧
 evaluate_match_with P cenv env v pes bv ⇒
 evaluate_match_with P cenv env v ((p,e)::pes) bv) ∧
(ALL_DISTINCT (pat_bindings p []) ∧
 (pmatch cenv p v env = Match_type_error) ⇒
 evaluate_match_with P cenv env v ((p,e)::pes) (Rerr Rtype_error)) ∧
(¬ALL_DISTINCT (pat_bindings p []) ⇒
 evaluate_match_with P cenv env v ((p,e)::pes) (Rerr Rtype_error))`

val evaluate_match_with_evaluate = store_thm(
"evaluate_match_with_evaluate",
``evaluate_match = evaluate_match_with evaluate``,
simp_tac std_ss [FUN_EQ_THM] >>
ntac 3 gen_tac >>
Induct >-
  rw[Once evaluate_cases,Once evaluate_match_with_cases] >>
rw[Once evaluate_cases] >>
rw[Once evaluate_match_with_cases,SimpRHS] >>
PROVE_TAC[])

val evaluate_nice_ind = store_thm(
"evaluate_nice_ind",
``∀P.
(∀cenv env err. P cenv env (Raise err) (Rerr (Rraise err))) ∧
(∀cenv env v. P cenv env (Val v) (Rval v)) ∧
(∀cenv env cn es vs.
 do_con_check cenv cn (LENGTH es) ∧
 evaluate_list_with (P cenv env) es (Rval vs) ⇒
 P cenv env (Con cn es) (Rval (Conv cn vs))) ∧
(∀cenv env cn es.
 ¬do_con_check cenv cn (LENGTH es) ⇒
 P cenv env (Con cn es) (Rerr Rtype_error)) ∧
(∀cenv env cn es err.
 do_con_check cenv cn (LENGTH es) ∧
 evaluate_list_with (P cenv env) es (Rerr err) ⇒
 P cenv env (Con cn es) (Rerr err)) ∧
(∀cenv env n v.
 (lookup n env = SOME v) ⇒
 P cenv env (Var n) (Rval v)) ∧
(∀cenv env n.
 (lookup n env = NONE) ⇒
 P cenv env (Var n) (Rerr Rtype_error)) ∧
(∀cenv env n e.
 P cenv env (Fun n e) (Rval (Closure env n e))) ∧
(∀cenv env op e1 e2 v1 v2 env' e3 bv.
 P cenv env e1 (Rval v1) ∧
 P cenv env e2 (Rval v2) ∧
 (do_app env op v1 v2 = SOME (env',e3)) ∧
 P cenv env' e3 bv ⇒
 P cenv env (App op e1 e2) bv) ∧
(∀cenv env op e1 e2 v1 v2.
 P cenv env e1 (Rval v1) ∧
 P cenv env e2 (Rval v2) ∧ (do_app env op v1 v2 = NONE) ⇒
 P cenv env (App op e1 e2) (Rerr Rtype_error)) ∧
(∀cenv env op e1 e2 v1 err.
 P cenv env e1 (Rval v1) ∧
 P cenv env e2 (Rerr err) ⇒
 P cenv env (App op e1 e2) (Rerr err)) ∧
(∀cenv env op e1 e2 err.
 P cenv env e1 (Rerr err) ⇒
 P cenv env (App op e1 e2) (Rerr err)) ∧
(∀cenv env op e1 e2 v e' bv.
 P cenv env e1 (Rval v) ∧ (do_log op v e2 = SOME e') ∧
 P cenv env e' bv ⇒
 P cenv env (Log op e1 e2) bv) ∧
(∀cenv env op e1 e2 v.
 P cenv env e1 (Rval v) ∧ (do_log op v e2 = NONE) ⇒
 P cenv env (Log op e1 e2) (Rerr Rtype_error)) ∧
(∀cenv env op e1 e2 err.
 P cenv env e1 (Rerr err) ⇒
 P cenv env (Log op e1 e2) (Rerr err)) ∧
(∀cenv env e1 e2 e3 v e' bv.
 P cenv env e1 (Rval v) ∧ (do_if v e2 e3 = SOME e') ∧
 P cenv env e' bv ⇒
 P cenv env (If e1 e2 e3) bv) ∧
(∀cenv env e1 e2 e3 v.
 P cenv env e1 (Rval v) ∧ (do_if v e2 e3 = NONE) ⇒
 P cenv env (If e1 e2 e3) (Rerr Rtype_error)) ∧
(∀cenv env e1 e2 e3 err.
 P cenv env e1 (Rerr err) ⇒
 P cenv env (If e1 e2 e3) (Rerr err)) ∧
(∀cenv env e pes v bv.
 P cenv env e (Rval v) ∧
 evaluate_match_with P cenv env v pes bv ⇒
 P cenv env (Mat e pes) bv) ∧
(∀cenv env e pes err.
 P cenv env e (Rerr err) ⇒
 P cenv env (Mat e pes) (Rerr err)) ∧
(∀cenv env n e1 e2 v bv.
 P cenv env e1 (Rval v) ∧
 P cenv (bind n v env) e2 bv ⇒
 P cenv env (Let n e1 e2) bv) ∧
(∀cenv env n e1 e2 err.
 P cenv env e1 (Rerr err) ⇒
 P cenv env (Let n e1 e2) (Rerr err)) ∧
(∀cenv env funs e bv.
 ALL_DISTINCT (MAP (λ(x,y,z). x) funs) ∧
 P cenv (build_rec_env funs env) e bv ⇒
 P cenv env (Letrec funs e) bv) ∧
(∀cenv env funs e.
 ¬ALL_DISTINCT (MAP (λ(x,y,z). x) funs) ⇒
 P cenv env (Letrec funs e) (Rerr Rtype_error)) ∧
(∀cenv env. evaluate_list_with (P cenv env) [] (Rval [])) ∧
(∀cenv env e es v vs.
 P cenv env e (Rval v) ∧
 evaluate_list_with (P cenv env) es (Rval vs) ⇒
 evaluate_list_with (P cenv env) (e::es) (Rval (v::vs))) ∧
(∀cenv env e es err.
 P cenv env e (Rerr err) ⇒
 evaluate_list_with (P cenv env) (e::es) (Rerr err)) ∧
(∀cenv env e es v err.
 P cenv env e (Rval v) ∧
 evaluate_list_with (P cenv env) es (Rerr err) ⇒
 evaluate_list_with (P cenv env) (e::es) (Rerr err)) ∧
(∀cenv env v.
 evaluate_match_with P cenv env v [] (Rerr (Rraise Bind_error))) ∧
(∀cenv env v p e pes env' bv.
 ALL_DISTINCT (pat_bindings p []) ∧
 (pmatch cenv p v env = Match env') ∧ P cenv env' e bv ⇒
 evaluate_match_with P cenv env v ((p,e)::pes) bv) ∧
(∀cenv env v p e pes bv.
 ALL_DISTINCT (pat_bindings p []) ∧
 (pmatch cenv p v env = No_match) ∧
 evaluate_match_with P cenv env v pes bv ⇒
 evaluate_match_with P cenv env v ((p,e)::pes) bv) ∧
(∀cenv env v p e pes.
 (pmatch cenv p v env = Match_type_error) ⇒
 evaluate_match_with P cenv env v ((p,e)::pes) (Rerr Rtype_error)) ∧
(∀cenv env v p e pes.
 ¬ALL_DISTINCT (pat_bindings p []) ⇒
 evaluate_match_with P cenv env v ((p,e)::pes) (Rerr Rtype_error))
⇒ (∀cenv env exp res.
   evaluate cenv env exp res
   ⇒ P cenv env exp res)``,
ntac 2 strip_tac >>
qsuff_tac `
(∀cenv env exp res. evaluate cenv env exp res ⇒ P cenv env exp res) ∧
(∀cenv env exps ress. evaluate_list cenv env exps ress ⇒ evaluate_list_with (P cenv env) exps ress) ∧
(∀cenv env v pes res. evaluate_match cenv env v pes res ⇒ evaluate_match_with P cenv env v pes res)` >- rw[] >>
ho_match_mp_tac evaluate_ind >>
rw[] >> PROVE_TAC[])

(* Prove compiler phases preserve semantics *)

(*
val exp_to_Cexp_thm1 = store_thm(
"exp_to_Cexp_thm1",
``∀cenv env exp res.
   evaluate cenv env exp res ⇒
   (res ≠ Rerr Rtype_error) ⇒
   ∀cm s. ∃s' Cexp. (exp_to_Cexp F cm (s,exp) = (s',Cexp)) ∧
     ∀cw Cenv. (good_cmaps cenv cm cw) ∧
               (good_envs env s s' Cenv) ⇒
       ∃Cres. Cevaluate Cenv Cexp Cres ∧
              (map_result (Cv_to_ov cw) Cres =
               map_result v_to_ov res)``,
ho_match_mp_tac evaluate_nice_ind >>
strip_tac >- (
  rw[exp_to_Cexp_def,
     Once CompileTheory.Cevaluate_cases]) >>
strip_tac >- (
  rw[exp_to_Cexp_def]
  (* TODO: define exp_to_Cexp on non-literal values *)
*)

val _ = export_theory ()
