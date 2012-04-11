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

(* nicer induction theorem for evaluate *)
(* TODO: move? *)

val (evaluate_list_with_rules,evaluate_list_with_ind,evaluate_list_with_cases) = Hol_reln [ANTIQUOTE(
evaluate_rules |> SIMP_RULE (srw_ss()) [] |> concl |>
strip_conj |>
Lib.filter (fn tm => tm |> strip_forall |> snd |> strip_imp |> snd |> strip_comb |> fst |> same_const ``evaluate_list``) |>
let val t1 = ``evaluate cenv env``
    val t2 = ``evaluate_list cenv env``
    val tP = type_of t1
    val P = mk_var ("P",tP)
    val ew = mk_comb(mk_var("evaluate_list_with",tP --> type_of t2),P)
in List.map (fn tm => tm |> strip_forall |> snd |>
                   subst [t1|->P, t2|->ew])
end |> list_mk_conj)]

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

val (evaluate_match_with_rules,evaluate_match_with_ind,evaluate_match_with_cases) = Hol_reln [ANTIQUOTE(
evaluate_rules |> SIMP_RULE (srw_ss()) [] |> concl |>
strip_conj |>
Lib.filter (fn tm => tm |> strip_forall |> snd |> strip_imp |> snd |> strip_comb |> fst |> same_const ``evaluate_match``) |>
let val t1 = ``evaluate``
    val t2 = ``evaluate_match``
    val tP = type_of t1
    val P = mk_var ("P",tP)
    val ew = mk_comb(mk_var("evaluate_match_with",tP --> type_of t2),P)
in List.map (fn tm => tm |> strip_forall |> snd |>
                   subst [t1|->P, t2|->ew])
end |> list_mk_conj)]

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

val evaluate_nice_ind = save_thm(
"evaluate_nice_ind",
evaluate_ind
|> Q.SPECL [`P`,`λcenv env. evaluate_list_with (P cenv env)`,`evaluate_match_with P`] |> SIMP_RULE (srw_ss()) []
|> UNDISCH_ALL
|> CONJUNCTS
|> List.hd
|> DISCH_ALL
|> Q.GEN `P`
|> SIMP_RULE (srw_ss()) [])

(* TODO: save in compileTerminationTheory? *)
val Cevaluate_cases = CompileTheory.Cevaluate_cases
val extend_def = CompileTheory.extend_def
val exp_Cexp_ind = CompileTheory.exp_Cexp_ind

(* Cevaluate functional equations *)

val Cevaluate_raise = store_thm(
"Cevaluate_raise",
``∀env err res. Cevaluate env (CRaise err) res = (res = Rerr (Rraise err))``,
rw[Once Cevaluate_cases])

val Cevaluate_val = store_thm(
"Cevaluate_val",
``∀env v res. Cevaluate env (CVal v) res = (res = Rval v)``,
rw[Once Cevaluate_cases])

val _ = export_rewrites["Cevaluate_raise","Cevaluate_val"]

val good_cm_cw_def = Define`
  good_cm_cw cm cw =
  (∀cn. cn IN FDOM cm ⇒ cm ' cn IN FDOM cw ∧
                        (cw ' (cm ' cn) = cn))`

val good_cmaps_def = Define`
good_cmaps cenv cm cw =
  (∀cn n. do_con_check cenv cn n ⇒ cn IN FDOM cm) ∧
  good_cm_cw cm cw`

(*
val observable_v_def = tDefine "observable_v"`
  (observable_v (Lit l) = T) ∧
  (observable_v (Conv cn vs) = EVERY observable_v vs) ∧
  (observable_v _ = F)`(
WF_REL_TAC `measure v_size` >>
rw[MiniMLTerminationTheory.exp9_size_thm] >>
Q.ISPEC_THEN `v_size` imp_res_tac SUM_MAP_MEM_bound >>
srw_tac[ARITH_ss][])
val _ = export_rewrites["observable_v_def"]

val observable_Cv_def = tDefine "observable_Cv"`
  (observable_Cv (CLit l) = T) ∧
  (observable_Cv (CConv cn vs) = EVERY observable_Cv vs) ∧
  (observable_Cv _ = F)`(
WF_REL_TAC `measure Cv_size` >>
rw[Cexp8_size_thm] >>
Q.ISPEC_THEN `Cv_size` imp_res_tac SUM_MAP_MEM_bound >>
srw_tac[ARITH_ss][])
val _ = export_rewrites["observable_Cv_def"]
*)

(* too strong? *)
val good_G_def = Define`
  good_G G =
    (∀cm v Cv. v_Cv G cm v Cv ⇒ G cm v Cv) ∧
    (∀cm v Cv cw.
      good_cm_cw cm cw ∧
      G cm v Cv ⇒ ((v_to_ov v) = (Cv_to_ov cw) Cv))`

(* Soundness(?) of exp_Cexp *)

(*

val exp_Cexp_thm = store_thm(
"exp_Cexp_thm",``
∀G cm env Cenv exp Cexp. exp_Cexp G cm env Cenv exp Cexp ⇒
  good_G G ⇒
  ∀cenv res.
    evaluate cenv env exp res ⇒
    ∀cw. good_cmaps cenv cm cw ⇒
      ∃Cres.
        Cevaluate Cenv Cexp Cres ∧
        (map_result (Cv_to_ov cw) Cres =
         map_result v_to_ov res)``,
ho_match_mp_tac exp_Cexp_ind >>
rw[] >- (
  fs[good_G_def,good_cmaps_def] >>
  PROVE_TAC[] )
>- (

*)


(*
val exp_Cexp_thm = store_thm(
"exp_Cexp_thm",``
∀cm env Cenv exp Cexp. exp_Cexp cm env Cenv exp Cexp ⇒
  ∀cenv res.
    evaluate cenv env exp res ⇒
    ∀cw. good_cmaps cenv cm cw ⇒
      ∃Cres.
        Cevaluate Cenv Cexp Cres ∧
        (map_result (Cv_to_ov cw) Cres =
         map_result v_to_ov res)``,
ho_match_mp_tac exp_Cexp_ind >>
rw[]
*)

(* Prove compiler phases preserve semantics *)

val good_envs_def = Define`
  good_envs env s s' Cenv = s.cmap SUBMAP s'.cmap`

(*
val exp_to_Cexp_cmap_SUBMAP = store_thm(
"exp_to_Cexp_cmap_SUBMAP",
``∀b cm s exp s' Cexp.
  (exp_to_Cexp b cm (s,exp) = (s',Cexp)) ⇒
  s.m SUBMAP s'.m``,
qsuff_tac `∀b cm s exp s' Cexp.
  (exp_to_Cexp b cm (s,exp) = (s',Cexp)) ⇒
  (FST (s,exp)).m SUBMAP s'.m` >- rw[] >>
ho_match_mp_tac exp_to_Cexp_ind >>
rw[exp_to_Cexp_def,extend_def]
*)

(*
val exp_to_Cexp_thm1 = store_thm(
"exp_to_Cexp_thm1",
``∀cenv env exp res.
   evaluate cenv env exp res ⇒
   is_source_exp exp ∧ (res ≠ Rerr Rtype_error) ⇒
   ∀cm s. ∃s' Cexp. (exp_to_Cexp F cm (s,exp) = (s',Cexp)) ∧
     ∀cw Cenv. (good_cmaps cenv cm cw) ∧
               (good_envs env s s' Cenv) ⇒
       ∃Cres. Cevaluate Cenv Cexp Cres ∧
              (map_result (Cv_to_ov cw) Cres =
               map_result v_to_ov res)``,
ho_match_mp_tac evaluate_nice_ind >>
strip_tac >- (
  rw[exp_to_Cexp_def,
     Once Cevaluate_cases]) >>
strip_tac >- (
  ntac 2 gen_tac >>
  Cases >> rw[is_source_exp_def] >>
  rw[exp_to_Cexp_def] >>
  rw[Once Cevaluate_cases]) >>
strip_tac >- (
  rw[exp_to_Cexp_def,good_cmaps_def] >>
  res_tac >>
  qpat_assum `do_con_check X Y Z` kall_tac >>
  fs[is_source_exp_def] >>
  Induct_on `es` >- (
    rw[Once evaluate_list_with_cases] >>
    rw[Once Cevaluate_cases] >>
    rw[Once Cevaluate_cases] >>
    qexists_tac `Rval (CConv (cm ' cn) [])` >>
    rw[] ) >>
  rw[Once evaluate_list_with_cases] >>
  fs[is_source_exp_def] >>
  first_x_assum (qspecl_then [`cm`,`s`] mp_tac) >>
  rw[] >> rw[] >>
  rw[Once Cevaluate_cases]
  ... ) >>
strip_tac >- (
  rw[exp_to_Cexp_def] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  rw[Once Cevaluate_cases] >>
  qexists_tac `Rerr err` >>
  rw[] >>
  fs[is_source_exp_def] >>
  qpat_assum `do_con_check X Y Z` kall_tac >>
  Induct_on `es` >>
  rw[Once evaluate_list_with_cases] >>
  fs[] >>
  first_x_assum (qspecl_then [`cm`,`s`] mp_tac) >>
  rw[] >>
  rw[Once Cevaluate_cases] >>
  first_x_assum (qspecl_then [`cw`,`Cenv`] mp_tac) >>
  rw[good_envs_def] >>
  Cases_on `Cres` >> fs[] >>
  PROVE_TAC[] ) >>
strip_tac >- (
  rw[]
*)

(*
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
