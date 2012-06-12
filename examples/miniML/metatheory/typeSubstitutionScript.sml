(* Proving that if a value has a type, it also has any other type that is a 
 * substitution into the first type.  This lets us handle type soundness of
 * polymorphism. *)

open preamble MiniMLTheory MiniMLTerminationTheory;

val _ = new_theory "typeSubstitution";

(* Recursive functions have function type *)
val type_funs_Tfn = Q.store_thm ("type_funs_Tfn",
`∀tenvC tenv funs tenv' tvs t n.
  type_funs tenvC tenv funs tenv' ∧
  (lookup n tenv' = SOME t)
  ⇒
  ∃t1 t2. (t = Tfn t1 t2) ∧ check_freevars T [] (Tfn t1 t2)`,
induct_on `funs` >>
rw [] >>
qpat_assum `type_funs tenvC tenv funspat tenv'`
      (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
rw [] >>
fs [lookup_def, emp_def, bind_def] >>
cases_on `fn = n` >>
fs [deBruijn_subst_def] >>
metis_tac []);

val lookup_append = Q.store_thm ("lookup_append",
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

val lookup_in = Q.store_thm ("lookup_in",
`!x e v. (lookup x e = SOME v) ⇒ MEM x (MAP FST e)`,
induct_on `e` >>
rw [lookup_def] >>
cases_on `h` >>
fs [lookup_def] >>
metis_tac []);

val lookup_in2 = Q.prove (
`!x e v. (lookup x e = SOME v) ⇒ MEM v (MAP SND e)`,
induct_on `e` >>
rw [lookup_def] >>
cases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
fs [] >>
metis_tac []);

val lookup_notin = Q.store_thm ("lookup_notin",
`!x e. (lookup x e = NONE) ⇒ ~MEM x (MAP FST e)`,
induct_on `e` >>
rw [lookup_def] >>
cases_on `h` >>
fs [lookup_def] >>
every_case_tac >>
fs []);

val lookup_zip_map = Q.prove (
`!x env keys vals res f res'.
  (LENGTH keys = LENGTH vals) ∧ (env = ZIP (keys,vals)) ∧ (lookup x env = res) ⇒
  (lookup x (ZIP (keys,MAP f vals)) = OPTION_MAP f res)`,
recInduct lookup_ind >>
rw [lookup_def] >>
cases_on `keys` >>
cases_on `vals` >>
fs []);

val tenvC_ok_def = Define `
tenvC_ok tenvC = EVERY (\(cn,tvs,ts,tn). EVERY (check_freevars F tvs) ts) tenvC`;

val tenv_ok_def = Define `
(tenv_ok Env_empty = T) ∧
(tenv_ok (Tvar_bind tenv) = tenv_ok tenv) ∧
(tenv_ok (Var_bind x tvs t tenv) = check_freevars T tvs t ∧ tenv_ok tenv)`;

val tenvC_ok_lookup = Q.prove (
`!tenvC cn tvs ts tn. 
  tenvC_ok tenvC ∧ (lookup cn tenvC = SOME (tvs,ts,tn))
  ⇒
  EVERY (check_freevars F tvs) ts`,
induct_on `tenvC` >>
rw [] >>
PairCases_on `h` >>
fs [tenvC_ok_def] >>
every_case_tac >>
rw [] >>
fs [] >>
metis_tac []);

val check_freevars_deBruijn_inc = Q.prove (
`!dbok tvs t. 
  check_freevars dbok tvs t ⇒ 
  !idx. check_freevars dbok tvs (deBruijn_inc idx t)`,
ho_match_mp_tac check_freevars_ind >>
rw [check_freevars_def, deBruijn_inc_def, EVERY_MAP] >>
fs [EVERY_MEM]);

val tenv_ok_lookup = Q.prove (
`!tenv tv tvs t idx. 
  tenv_ok tenv ∧ (lookup_var tv idx tenv = SOME (tvs,t))
  ⇒
  check_freevars T tvs t`,
induct_on `tenv` >>
rw [tenv_ok_def, lookup_var_def] >>
metis_tac [check_freevars_deBruijn_inc]);

val pmatch_tenv_ok = Q.prove (
`(!envC tenv p v tenv'. 
    type_p envC tenv p v tenv' ⇒ tenv_ok tenv ⇒ tenv_ok tenv') ∧
 (!envC tenv ps v tenv'. 
     type_ps envC tenv ps v tenv' ⇒ tenv_ok tenv ⇒ tenv_ok tenv')`,
ho_match_mp_tac type_p_ind >>
rw [tenv_ok_def, bind_def]);

val check_freevars_F_to_T = Q.prove (
`!dbok tvs t. (dbok = F) ∧ check_freevars dbok tvs t ⇒ check_freevars T tvs t`,
recInduct check_freevars_ind >>
rw [check_freevars_def] >>
fs [EVERY_MEM]);

val check_freevars_weakening = Q.prove (
`!dbok tvs t tvs'. 
  check_freevars dbok tvs t 
  ⇒ 
  check_freevars dbok (tvs ++ tvs') t ∧
  check_freevars dbok (tvs' ++ tvs) t`,
recInduct check_freevars_ind >>
rw [check_freevars_def] >>
fs [EVERY_MEM]);

val check_freevars_exists = Q.prove (
`(!t. ?tvs. check_freevars T tvs t) ∧
 (!ts. ?tvs. EVERY (check_freevars T tvs) ts)`,
ho_match_mp_tac t_induction >>
rw [check_freevars_def] >|
[qexists_tac `[s]` >>
     rw [],
 metis_tac [],
 qexists_tac `tvs ++ tvs'` >>
     rw [] >>
     metis_tac [check_freevars_weakening],
 qexists_tac `tvs ++  tvs'` >>
     rw [] >>
     fs [EVERY_MEM] >>
     metis_tac [check_freevars_weakening]]);

val list_length_exists = Q.prove (
`!l. ?l'. LENGTH l = LENGTH l'`,
induct_on `l` >>
rw [] >|
[qexists_tac `[]` >>
     rw [],
 qexists_tac `ARB::l'` >>
     rw []]);

val check_freevars_subst_single = Q.prove (
`!dbok tvs t tvs' ts.
  (LENGTH tvs = LENGTH ts) ∧
  check_freevars dbok tvs t ∧
  EVERY (check_freevars dbok tvs') ts
  ⇒
  check_freevars dbok tvs' (type_subst (ZIP (tvs,ts)) t)`,
recInduct check_freevars_ind >>
rw [check_freevars_def, type_subst_def, EVERY_MAP] >|
[every_case_tac >>
     fs [check_freevars_def] >|
     [imp_res_tac lookup_notin >>
          imp_res_tac MAP_ZIP >>
          fs [],
      imp_res_tac lookup_in2 >>
          imp_res_tac MAP_ZIP >>
          fs [EVERY_MEM]],
 fs [EVERY_MEM]]);

val check_freevars_subst_list = Q.prove (
`!dbok tvs tvs' ts ts'.
  (LENGTH tvs = LENGTH ts) ∧
  EVERY (check_freevars dbok tvs) ts' ∧
  EVERY (check_freevars dbok tvs') ts
  ⇒
  EVERY (check_freevars dbok tvs') (MAP (type_subst (ZIP (tvs,ts))) ts')`,
induct_on `ts'` >>
rw [] >>
metis_tac [check_freevars_subst_single]);

val deBruijn_subst2_def = tDefine "deBruijn_subst2" `
(deBruijn_subst2 ts inc (Tvar tv) = Tvar tv) ∧
(deBruijn_subst2 ts inc (Tvar_db 0 n) = EL n ts) ∧
(deBruijn_subst2 ts inc (Tvar_db i n) = Tvar_db (i - 1 + inc) n) ∧
(deBruijn_subst2 ts inc (Tapp ts' tn) = 
  Tapp (MAP (deBruijn_subst2 ts inc) ts') tn) ∧
(deBruijn_subst2 ts inc (Tfn t1 t2) =
  Tfn (deBruijn_subst2 ts inc t1) (deBruijn_subst2 ts inc t2)) ∧
(deBruijn_subst2 ts inc Tnum = Tnum) ∧
(deBruijn_subst2 ts inc Tbool = Tbool)`
(wf_rel_tac `measure (t_size o SND o SND)` >>
 rw [t_size_def] >>
 TRY (induct_on `ts'`) >>
 rw [t_size_def] >>
 res_tac >>
 decide_tac);

val type_subst_type_subst_single = Q.prove (
`!s t tvs dbok tvs' ts ts' inc.
  (LENGTH tvs = LENGTH ts) ∧ 
  check_freevars F tvs t ∧
  (s = (ZIP (tvs,ts))) ⇒
  (deBruijn_subst2 ts' inc (type_subst (ZIP (tvs,ts)) t) =
   type_subst (ZIP (tvs,MAP (deBruijn_subst2 ts' inc) ts)) t)`,
recInduct type_subst_ind >>
rw [deBruijn_subst2_def, type_subst_def, check_freevars_def] >|
[every_case_tac >>
     fs [deBruijn_subst2_def] >|
     [imp_res_tac lookup_notin >>
          imp_res_tac MAP_ZIP >>
          fs [],
      metis_tac [lookup_zip_map, optionTheory.OPTION_MAP_DEF,
                 optionTheory.NOT_SOME_NONE],
      metis_tac [lookup_zip_map, optionTheory.OPTION_MAP_DEF,
                 optionTheory.SOME_11]],
 rw [rich_listTheory.MAP_EQ_f, MAP_MAP_o] >>
     fs [EVERY_MEM] >>
     metis_tac []]); 

val type_subst_type_subst_list = Q.prove (
`!t tvs dbok tvs' ts ts' ts'' inc.
  (LENGTH tvs = LENGTH ts) ∧ 
  (LENGTH tvs' = LENGTH ts') ∧ 
  EVERY (check_freevars F tvs) ts'' ⇒
  (MAP (deBruijn_subst2 ts' inc) (MAP (type_subst (ZIP (tvs,ts))) ts'') =
   MAP (type_subst (ZIP (tvs,MAP (deBruijn_subst2 ts' inc) ts))) ts'')`,
induct_on `ts''` >>
rw [] >>
metis_tac [type_subst_type_subst_single]);

val subst_check_freevars = Q.prove (
`(!t tvs ts dbok.
  (LENGTH tvs = LENGTH ts) ∧
  check_freevars dbok [] (type_subst (ZIP (tvs, ts)) t)
  ⇒
  check_freevars dbok tvs t) ∧
 (!ts tvs ts' dbok.
  (LENGTH tvs = LENGTH ts') ∧
  EVERY (λt. check_freevars dbok [] (type_subst (ZIP (tvs, ts')) t)) ts
  ⇒
  EVERY (λt. check_freevars dbok tvs t) ts)`,
ho_match_mp_tac t_induction >>
rw [check_freevars_def, type_subst_def, EVERY_MAP] >|
[every_case_tac >>
     fs [check_freevars_def] >>
     imp_res_tac lookup_in >>
     fs [MEM_MAP] >>
     imp_res_tac MEM_ZIP >>
     fs [] >>
     rw [MEM_EL] >>
     metis_tac [], 
 fs [EVERY_MEM] >>
     rw [] >>
     metis_tac [],
 metis_tac [],
 metis_tac [],
 metis_tac []]);

val check_freevars_deBruijn_subst = Q.store_thm ("check_freevars_deBruijn_subst",
`!tvs t.
  enough_tvars tvs t ∧ check_freevars T [] t 
  ⇒ 
  check_freevars T tvs (deBruijn_subst tvs t)`,
recInduct enough_tvars_ind >>
rw [deBruijn_subst_def, check_freevars_def, enough_tvars_def] >>
fs [rich_listTheory.EL_IS_EL, EVERY_MEM] >>
rw [] >>
fs [MEM_MAP]);

 (*
val no_freevars_subst = Q.prove (
`!dbok fvs t tvs ts. 
  (fvs = []) ∧ check_freevars dbok fvs t ∧ (LENGTH tvs = LENGTH ts) 
  ⇒ 
  (type_subst (ZIP (tvs,ts)) t = t)`,
recInduct check_freevars_ind >>
rw [check_freevars_def, type_subst_def] >|
[every_case_tac >>
     rw [] >>
     fs [],
 induct_on `ts` >>
     rw []]);


val lem = Q.prove (
`!env t tvs tvs' ts.
  check_freevars T tvs t ∧
  (LENGTH tvs = LENGTH ts) ∧
  (env = (ZIP (tvs,ts)))
  ⇒
  (type_subst (ZIP (tvs,ts)) t =
   type_subst (ZIP (tvs ++ tvs',ts ++ MAP (λx. ARB) tvs')) t)`,
recInduct type_subst_ind >>
rw [type_subst_def, check_freevars_def] >|
[every_case_tac >>
     rw [] >|
     [imp_res_tac lookup_notin >>
          imp_res_tac MAP_ZIP >>
          fs [],
      imp_res_tac lookup_notin >>
          fs [] >>
          metis_tac [LENGTH_MAP, rich_listTheory.ZIP_APPEND, MAP_APPEND,
                     MEM_APPEND, MAP_ZIP],
      `ZIP (tvs ++ tvs',ts ++ MAP (λx. ARB) tvs') =
       ZIP (tvs,ts) ++ ZIP (tvs',MAP (λx. ARB) tvs')`
                      by metis_tac [rich_listTheory.ZIP_APPEND, LENGTH_MAP] >>
          fs [lookup_append] >>
          every_case_tac >>
          fs []],
 rw [MAP_EQ_f] >>
     fs [EVERY_MEM]]);
     *)

val deBruijn_subst_tenv_def = Define `
(deBruijn_subst_tenv ts inc Env_empty = Env_empty) ∧
(deBruijn_subst_tenv ts inc (Tvar_bind tenv) =
  Tvar_bind tenv) ∧
(deBruijn_subst_tenv ts inc (Var_bind n tvs t tenv) =
  (Var_bind n tvs (deBruijn_subst2 ts inc t) 
                  (deBruijn_subst_tenv ts inc tenv)))`;

val type_e_type_subst = Q.prove (
`(!tenvC tenv e t. type_e tenvC tenv e t ⇒
    !ts inc. 
       EVERY (check_freevars T []) ts ∧
       check_freevars T [] t ∧ 
       tenvC_ok tenvC ∧ 
       tenv_ok tenv 
       ⇒ 
       type_e tenvC (deBruijn_subst_tenv ts inc tenv) e (deBruijn_subst2 ts inc t)) ∧
 (!tenvC tenv es ts. type_es tenvC tenv es ts ⇒
    !ts' inc. 
       EVERY (check_freevars T []) ts ∧
       EVERY (check_freevars T []) ts' ∧ 
       tenvC_ok tenvC ∧ 
       tenv_ok tenv 
       ⇒ 
       type_es tenvC (deBruijn_subst_tenv ts inc tenv) es (MAP (deBruijn_subst2 ts' inc) ts)) ∧
 (!tenvC tenv funs tenv'. type_funs tenvC tenv funs tenv' ⇒
    !inc. type_funs tenvC tenv funs tenv')`,

ho_match_mp_tac type_e_strongind >>
rw [deBruijn_subst2_def, check_freevars_def] >>
rw [Once type_e_cases] >|

[all_tac,
 imp_res_tac tenvC_ok_lookup >>
     `EVERY (check_freevars T tvs) ts` 
              by metis_tac [EVERY_MEM,check_freevars_F_to_T] >>
     metis_tac [type_subst_type_subst_list, check_freevars_subst_list],
 qexists_tac `MAP (deBruijn_subst2 ts' inc) ts` >>
     rw [] >>
     match_mp_tac type_subst_type_subst_single >>
     rw [] >>
     metis_tac [subst_check_freevars],





val type_v_type_subst_lem1 = Q.prove (
`(!tenvC v t. type_v tenvC v t ⇒
    !ts skip inc. 
       check_freevars T [] t ∧ tenvC_ok tenvC
       ⇒ 
       type_v tenvC v (deBruijn_subst ts (deBruijn_inc skip inc t))) ∧
 (!tenvC vs ts. type_vs tenvC vs ts ⇒
    !ts' skip inc. 
       tenvC_ok tenvC ∧ EVERY (check_freevars T []) ts ∧ tenvC_ok tenvC
       ⇒ 
       type_vs tenvC vs (MAP (\t. deBruijn_subst ts' (deBruijn_inc skip inc t)) ts)) ∧
 (!tenvC env tenv. type_env tenvC env tenv ⇒
       tenv_ok tenv ∧ type_env tenvC env tenv)`,

ho_match_mp_tac type_v_strongind >>
rw [deBruijn_subst_def, check_freevars_def, bind_def, (*tenv_ok_def,*)
    deBruijn_inc_def] >>
rw [Once type_v_cases] >|
[imp_res_tac tenvC_ok_lookup >>
     `EVERY (check_freevars T tvs) ts` 
              by metis_tac [EVERY_MEM,check_freevars_F_to_T] >>
     metis_tac [type_subst_type_subst_list, check_freevars_subst_list],
 all_tac,
 all_tac,
 rw [check_freevars_deBruijn_subst],
 rw [bind_def] >>
     metis_tac []]



     rw [] >>
     match_mp_tac type_subst_type_subst_single >>
     rw []
 metis_tac [type_subst_type_subst_single, subst_check_freevars], 

 fs [bind_def, tenv_ok_def] >>
     metis_tac [no_freevars_subst],
 metis_tac [no_freevars_subst, type_funs_Tfn],
 imp_res_tac tenvC_ok_lookup >>
     `EVERY (check_freevars T tvs) ts` 
              by metis_tac [EVERY_MEM,check_freevars_F_to_T] >>
     metis_tac [type_subst_type_subst_list, check_freevars_subst_list],
 metis_tac [type_subst_type_subst_single, LENGTH_MAP, tenv_ok_lookup],
 metis_tac [no_freevars_subst],
 fs [tenv_ok_def, bind_def] >>
     metis_tac [no_freevars_subst],
 fs [type_op_def] >>
     every_case_tac >>
     fs [check_freevars_def, type_subst_def] >>
     rw [] >|
     [res_tac >>
          qexists_tac `Tnum` >>
          qexists_tac `Tnum` >>
          rw [] >>
          metis_tac [],
      res_tac >>
          qexists_tac `Tnum` >>
          qexists_tac `Tnum` >>
          rw [] >>
          metis_tac [],
      metis_tac [check_freevars_exists, list_length_exists],
      `?tvs_t'. check_freevars T tvs_t' t'` by metis_tac [check_freevars_exists] >>
          `check_freevars T (tvs ++ tvs_t') t' ∧ 
           check_freevars T (tvs ++ tvs_t') t''` 
                   by metis_tac [check_freevars_weakening] >>
          `LENGTH (tvs++tvs_t') = LENGTH (ts ++ MAP (\x. ARB) tvs_t')` 
                   by metis_tac [LENGTH_APPEND, LENGTH_MAP] >>
          res_tac >>
          qexists_tac `Tfn (type_subst (ZIP (tvs ++ tvs_t',ts ++ MAP (\x. ARB) tvs_t')) t')
                           (type_subst (ZIP (tvs ++ tvs_t',ts ++ MAP (\x. ARB) tvs_t')) t'')` >>
          qexists_tac `type_subst (ZIP (tvs ++ tvs_t',ts ++ MAP (\x. ARB) tvs_t')) t'` >>
          rw [] >>
          metis_tac [lem]],
 qexists_tac `t` >>
     fs [RES_FORALL] >>
     rw [] >>
     PairCases_on `x` >>
     fs [] >>
     res_tac >>
     fs [] >>
     rw [] >>
     metis_tac [pmatch_tenv_ok],
 qexists_tac `t` >> 
     qexists_tac `tvs` >>
     rw [] >>
     fs [bind_def, tenv_ok_def] >>
     metis_tac [check_freevars_deBruijn_subst],
 metis_tac [tenv_ok_def, EVERY_APPEND, merge_def],
 rw [tenv_ok_def],
 fs [bind_def, tenv_ok_def] >>
     metis_tac [check_freevars_deBruijn_subst],
 fs [bind_def, tenv_ok_def, check_freevars_def] >>
     metis_tac [check_freevars_deBruijn_subst],
 rw [tenv_ok_def, emp_def],
 fs [bind_def, tenv_ok_def, check_freevars_def],
 fs [bind_def, tenv_ok_def, check_freevars_def]]);

val type_v_type_subst = Q.store_thm ("type_v_type_subst",
`!tenvC v t tvs ts. 
  type_v tenvC v t ∧ 
  check_freevars T tvs t ∧ 
  tenvC_ok tenvC ∧ 
  (LENGTH tvs = LENGTH ts) 
  ⇒ 
  type_v tenvC v (type_subst (ZIP (tvs,ts)) t)`,
metis_tac [type_v_type_subst_lem1]);

(*
∃t'.
  (t = deBruijn_subst [] t') ∧ type_v tenvC v t' ∧ enough_tvars [] t' ∧
  check_freevars T [] t'
------------------------------------
  0.  type_v tenvC v t
  1.  tenv' = (n,[],t)::tenv
  2.  check_freevars T [] t
  3.  type_env tenvC env tenv

`(!tenvC v t. type_v tenvC v t ⇒ tenvC_ok tenvC ⇒ 
    !skip_zero. type_v tenvC v (inc_deBruijn skip_zero t)) ∧
 (!tenvC tenv e t. type_e tenvC tenv e t ⇒ tenvC_ok tenvC ⇒ 
    !skip_zero. type_e tenvC (MAP (\(x,tvs',t). (x,tvs',inc_deBruijn skip_zero
    t)) tenv) e (inc_deBruijn skip_zero t)) ∧
 (!tenvC tenv es ts. type_es tenvC tenv es ts ⇒ tenvC_ok tenvC ⇒
   !skip_zero. type_es tenvC (MAP (\(x,tvs',t). (x,tvs',inc_deBruijn skip_zero
   t)) tenv) es (MAP (inc_deBruijn skip_zero) ts)) ∧
 (!tenvC vs ts. type_vs tenvC vs ts ⇒ tenvC_ok tenvC ⇒ 
   !skip_zero. type_vs tenvC vs (MAP (inc_deBruijn skip_zero) ts)) ∧ 
 (!tenvC env tenv. type_env tenvC env tenv ⇒ tenvC_ok tenvC ⇒
    !skip_zero. type_env tenvC env (MAP (\(x,tvs',t). (x,tvs',inc_deBruijn skip_zero t)) tenv)) ∧
 (!tenvC tenv funs tenv'. type_funs tenvC tenv funs tenv' ⇒
    type_funs tenvC tenv funs tenv')`,

HO_MATCH_MP_TAC type_v_strongind >>
rw [inc_deBruijn_def] >>
rw [Once type_v_cases] >>
fs [bind_def] >|
[metis_tac [inc_deBruijn_subst_list, tenvC_ok_lookup],
 metis_tac [inc_deBruijn_check_freevars],
 all_tac,
 metis_tac [inc_deBruijn_subst_list, tenvC_ok_lookup],
 all_tac,
 metis_tac [inc_deBruijn_check_freevars],
 fs [type_op_def] >>
     every_case_tac >>
     fs [inc_deBruijn_def] >>
     rw [] >|
     [MAP_EVERY qexists_tac [`Tnum`,`Tnum`] >>
          rw [],
      MAP_EVERY qexists_tac [`Tnum`,`Tnum`] >>
          rw [],
      metis_tac [],
      MAP_EVERY qexists_tac [`Tfn (inc_deBruijn skip_zero t') (inc_deBruijn skip_zero t'')`] >>
          rw []],
 all_tac,
 all_tac,
 all_tac,
 all_tac]

 
 qexists_tac `inc_deBruijn T t` >>
     rw []

 qexists_tac `inc_deBruijn t` >>
     rw [] >>
     qexists_tac `tvs` >>
     rw [] >>
     metis_tac [inc_deBruijn_check_freevars, inc_deBruijn_enough_tvars]

*)

val type_v_deBruijn_subst1 = mk_thm ([],
``!tenvC v t. 
    type_v tenvC v t ⇒ 
    ?t'. (t = deBruijn_subst [] t') ∧ type_v tenvC v t' ∧ 
         enough_tvars ([]:tvarN list) t'``);

val _ = save_thm ("type_v_deBruijn_subst1", type_v_deBruijn_subst1);

(*
type_v tenvC v (deBruijn_subst tvs t1)
------------------------------------
  0.  tenvC_ok tenvC
  1.  type_env tenvC env tenv
  2.  type_v tenvC v t1
  3.  type_env tenvC r tenv'
  4.  check_freevars T [] t1
  5.  enough_tvars tvs t1
  6.  type_e tenvC (bind s (tvs,deBruijn_subst tvs t1) tenv') e t2
  7.  type_ctxts tenvC c' t2 t
:


`(!tenvC v t. type_v tenvC v t ⇒
    !tvs. enough_tvars tvs t ⇒ type_v tenvC v (deBruijn_subst tvs t)) ∧
 (!tenvC tenv e t. type_e tenvC tenv e t ⇒
    !tvs env. enough_tvars tvs t ⇒ type_e tenvC env e (deBruijn_subst tvs t)) ∧
 (!tenvC tenv es ts. type_es tenvC tenv es ts ⇒
    !tvs. EVERY (enough_tvars tvs) ts ⇒ type_es tenvC tenv es (MAP (deBruijn_subst tvs) ts)) ∧
 (!tenvC vs ts. type_vs tenvC vs ts ⇒
    !tvs. EVERY (enough_tvars tvs) ts ⇒ type_vs tenvC vs (MAP (deBruijn_subst tvs) ts)) ∧
 (!tenvC env tenv. type_env tenvC env tenv ⇒
    type_env tenvC env tenv) ∧
 (!tenvC tenv funs tenv'. type_funs tenvC tenv funs tenv' ⇒
    type_funs tenvC tenv funs tenv')`,

HO_MATCH_MP_TAC type_v_ind >>
rw [deBruijn_subst_def, enough_tvars_def] >>
rw [Once type_v_cases] >|
[all_tac,
 metis_tac [check_freevars_deBruijn_subst],
 all_tac,
 all_tac,
 all_tac,
 all_tac,
 all_tac,
 all_tac,
 all_tac,
 all_tac,
 all_tac,
 all_tac]



*)

 
val type_v_deBruijn_subst2 = mk_thm ([],
``!tenvC v t tvs ts. 
  type_v tenvC v t ∧ enough_tvars tvs t 
  ⇒ 
  type_v tenvC v (deBruijn_subst tvs t)``);

val _ = save_thm ("type_v_deBruijn_subst2", type_v_deBruijn_subst2);

val _ = export_theory ();
