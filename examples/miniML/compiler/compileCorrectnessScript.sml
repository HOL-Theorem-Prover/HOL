open HolKernel bossLib boolLib intLib listTheory finite_mapTheory pred_setTheory sortingTheory alistTheory SatisfySimps lcsymtacs
open MiniMLTheory evaluateEquationsTheory compileTerminationTheory count_expTheory

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
val _ = export_rewrites["FINITE_free_vars"]

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

(* TODO: move? *)

val lookup_ALOOKUP = store_thm(
"lookup_ALOOKUP",
``lookup = combin$C ALOOKUP``,
fs[FUN_EQ_THM] >> gen_tac >> Induct >- rw[] >> Cases >> rw[])
val _ = export_rewrites["lookup_ALOOKUP"];

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
val Cevaluate_rules = CompileTheory.Cevaluate_rules
val extend_def = CompileTheory.extend_def
val exp_Cexp_ind = CompileTheory.exp_Cexp_ind
val v_Cv_ind = CompileTheory.v_Cv_ind
val v_Cv_cases = CompileTheory.v_Cv_cases
val sort_Cenv_def = CompileTheory.sort_Cenv_def
val i0_def = CompileTheory.i0_def
val Cevaluate_ind = CompileTheory.Cevaluate_ind
val Cevaluate_strongind = CompileTheory.Cevaluate_strongind
val mk_env_def = CompileTheory.mk_env_def
val find_index_def = CompileTheory.find_index_def

val (Cevaluate_list_with_rules,Cevaluate_list_with_ind,Cevaluate_list_with_cases) = Hol_reln [ANTIQUOTE(
Cevaluate_rules |> SIMP_RULE (srw_ss()) [] |> concl |>
strip_conj |>
Lib.filter (fn tm => tm |> strip_forall |> snd |> strip_imp |> snd |> strip_comb |> fst |> same_const ``Cevaluate_list``) |>
let val t1 = ``Cevaluate env``
    val t2 = ``Cevaluate_list env``
    val tP = type_of t1
    val P = mk_var ("P",tP)
    val ew = mk_comb(mk_var("Cevaluate_list_with",tP --> type_of t2),P)
in List.map (fn tm => tm |> strip_forall |> snd |>
                   subst [t1|->P, t2|->ew])
end |> list_mk_conj)]

val Cevaluate_list_with_Cevaluate = store_thm(
"Cevaluate_list_with_Cevaluate",
``∀env. Cevaluate_list env = Cevaluate_list_with (Cevaluate env)``,
gen_tac >>
simp_tac std_ss [Once FUN_EQ_THM] >>
Induct >>
rw[FUN_EQ_THM] >-
  rw[Once Cevaluate_cases,Once Cevaluate_list_with_cases] >>
rw[Once Cevaluate_cases] >>
rw[Once Cevaluate_list_with_cases,SimpRHS] >>
PROVE_TAC[])

val Cevaluate_nice_ind = save_thm(
"Cevaluate_nice_ind",
Cevaluate_ind
|> Q.SPECL [`P`,`λenv. Cevaluate_list_with (P env)`] |> SIMP_RULE (srw_ss()) []
|> UNDISCH_ALL
|> CONJUNCTS
|> List.hd
|> DISCH_ALL
|> Q.GEN `P`
|> SIMP_RULE (srw_ss()) [])

val Cevaluate_nice_strongind = save_thm(
"Cevaluate_nice_strongind",
Cevaluate_strongind
|> Q.SPECL [`P`,`λenv. Cevaluate_list_with (P env)`] |> SIMP_RULE (srw_ss()) []
|> UNDISCH_ALL
|> CONJUNCTS
|> List.hd
|> DISCH_ALL
|> Q.GEN `P`
|> SIMP_RULE (srw_ss()) [Cevaluate_list_with_Cevaluate])

(* Cevaluate functional equations *)

val Cevaluate_raise = store_thm(
"Cevaluate_raise",
``∀env err res. Cevaluate env (CRaise err) res = (res = Rerr (Rraise err))``,
rw[Once Cevaluate_cases])

val Cevaluate_val = store_thm(
"Cevaluate_val",
``∀env v res. Cevaluate env (CVal v) res = (res = Rval (ce_Cv v))``,
rw[Once Cevaluate_cases])

val Cevaluate_var = store_thm(
"Cevaluate_var",
``∀env vn res. Cevaluate env (CVar vn) res = (vn ∈ FDOM env ∧ (res = Rval (ce_Cv (env ' vn))))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_mat_nil = store_thm(
"Cevaluate_mat_nil",
``∀env n res. Cevaluate env (CMat n []) res = (res = Rerr (Rraise Bind_error))``,
rw[Once Cevaluate_cases])

val Cevaluate_let_nil = store_thm(
"Cevaluate_let_nil",
``∀env exp res. Cevaluate env (CLet [] [] exp) res = (Cevaluate env exp res)``,
rw[Once Cevaluate_cases])

val Cevaluate_fun = store_thm(
"Cevaluate_fun",
``∀env ns b res. Cevaluate env (CFun ns b) res = (res = Rval (ce_Cv (CClosure (fmap_to_alist env) ns b)))``,
rw[Once Cevaluate_cases])

val _ = export_rewrites["Cevaluate_raise","Cevaluate_val","Cevaluate_var","Cevaluate_mat_nil","Cevaluate_let_nil","Cevaluate_fun"]

val Cevaluate_con = store_thm(
"Cevaluate_con",
``∀env cn es res. Cevaluate env (CCon cn es) res =
(∃vs. Cevaluate_list env es (Rval vs) ∧ (res = Rval (CConv cn vs))) ∨
(∃err. Cevaluate_list env es (Rerr err) ∧ (res = Rerr err))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_tageq = store_thm(
"Cevaluate_tageq",
``∀env exp n res. Cevaluate env (CTagEq exp n) res =
  (∃m vs. Cevaluate env exp (Rval (CConv m vs)) ∧ (res = (Rval (CLit (Bool (n = m)))))) ∨
  (∃err. Cevaluate env exp (Rerr err) ∧ (res = Rerr err))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_mat_cons = store_thm(
"Cevaluate_mat_cons",
``∀env n p e pes res. Cevaluate env (CMat n ((p,e)::pes)) res =
  (n IN FDOM env) ∧
  ((∃env'. (Cpmatch env p (env ' n) = Cmatch env') ∧
           (Cevaluate env' e res)) ∨
   ((Cpmatch env p (env ' n) = Cno_match) ∧
    (Cevaluate env (CMat n pes) res)))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_let_cons = store_thm(
"Cevaluate_let_cons",
``∀env n e ns es b res. Cevaluate env (CLet (n::ns) (e::es) b) res =
(∃v. Cevaluate env e (Rval v) ∧
     Cevaluate (env |+ (n,v)) (CLet ns es b) res) ∨
(∃err. Cevaluate env e (Rerr err) ∧ (res = Rerr err))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_proj = store_thm(
"Cevaluate_proj",
``∀env exp n res. Cevaluate env (CProj exp n) res =
  (∃m vs. Cevaluate env exp (Rval (CConv m vs)) ∧ (n < LENGTH vs) ∧ (res = (Rval (EL n vs)))) ∨
  (∃err. Cevaluate env exp (Rerr err) ∧ (res = Rerr err))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val evaluate_list_with_nil = store_thm(
"evaluate_list_with_nil",
``∀f res. evaluate_list_with f [] res = (res = Rval [])``,
rw[Once evaluate_list_with_cases])
val _ = export_rewrites["evaluate_list_with_nil"];

val evaluate_list_with_cons = store_thm(
"evaluate_list_with_cons",
``∀f e es res. evaluate_list_with f (e::es) res =
  (∃v vs. f e (Rval v) ∧ evaluate_list_with f es (Rval vs) ∧ (res = Rval (v::vs))) ∨
  (∃v err. f e (Rval v) ∧ evaluate_list_with f es (Rerr err) ∧ (res = Rerr err)) ∨
  (∃err. f e (Rerr err) ∧ (res = Rerr err))``,
rw[Once evaluate_list_with_cases] >> PROVE_TAC[])

val Cevaluate_list_with_nil = store_thm(
"Cevaluate_list_with_nil",
``∀f res. Cevaluate_list_with f [] res = (res = Rval [])``,
rw[Once Cevaluate_list_with_cases])
val _ = export_rewrites["Cevaluate_list_with_nil"];

val Cevaluate_list_with_cons = store_thm(
"Cevaluate_list_with_cons",
``∀f e es res. Cevaluate_list_with f (e::es) res =
  (∃v vs. f e (Rval v) ∧ Cevaluate_list_with f es (Rval vs) ∧ (res = Rval (v::vs))) ∨
  (∃v err. f e (Rval v) ∧ Cevaluate_list_with f es (Rerr err) ∧ (res = Rerr err)) ∨
  (∃err. f e (Rerr err) ∧ (res = Rerr err))``,
rw[Once Cevaluate_list_with_cases] >> PROVE_TAC[])

val evaluate_list_with_error = store_thm(
"evaluate_list_with_error",
``!P ls err. evaluate_list_with P ls (Rerr err) =
             (∃n. n < LENGTH ls ∧ P (EL n ls) (Rerr err) ∧
               !m. m < n ⇒ ∃v. P (EL m ls) (Rval v))``,
gen_tac >> Induct >- rw[evaluate_list_with_nil] >>
rw[EQ_IMP_THM,evaluate_list_with_cons] >- (
  qexists_tac `SUC n` >>
  rw[] >>
  Cases_on `m` >> rw[] >- (
    qexists_tac `v` >> rw[] ) >>
  fs[] )
>- (
  qexists_tac `0` >>
  rw[] ) >>
Cases_on `n` >> fs[] >>
disj1_tac >>
first_assum (qspec_then `0` mp_tac) >>
simp_tac(srw_ss())[] >>
rw[] >> qexists_tac `v` >> rw[] >>
qmatch_assum_rename_tac `n < LENGTH ls` [] >>
qexists_tac `n` >> rw[] >>
first_x_assum (qspec_then `SUC m` mp_tac) >>
rw[])

val evaluate_list_with_value = store_thm(
"evaluate_list_with_value",
``!P ls vs. evaluate_list_with P ls (Rval vs) = (LENGTH ls = LENGTH vs) ∧ ∀n. n < LENGTH ls ⇒ P (EL n ls) (Rval (EL n vs))``,
gen_tac >> Induct >- rw[evaluate_list_with_nil,LENGTH_NIL_SYM] >>
gen_tac >> Cases >> rw[evaluate_list_with_cons,EQ_IMP_THM] >- (
  Cases_on `n` >> fs[] )
>- (
  first_x_assum (qspec_then `0` mp_tac) >>
  rw[] ) >>
first_x_assum (qspec_then `SUC n` mp_tac) >>
rw[])

val Cevaluate_list_with_error = store_thm(
"Cevaluate_list_with_error",
``!P ls err. Cevaluate_list_with P ls (Rerr err) =
             (∃n. n < LENGTH ls ∧ P (EL n ls) (Rerr err) ∧
               !m. m < n ⇒ ∃v. P (EL m ls) (Rval v))``,
gen_tac >> Induct >- rw[Cevaluate_list_with_nil] >>
rw[EQ_IMP_THM,Cevaluate_list_with_cons] >- (
  qexists_tac `SUC n` >>
  rw[] >>
  Cases_on `m` >> rw[] >- (
    qexists_tac `v` >> rw[] ) >>
  fs[] )
>- (
  qexists_tac `0` >>
  rw[] ) >>
Cases_on `n` >> fs[] >>
disj1_tac >>
first_assum (qspec_then `0` mp_tac) >>
simp_tac(srw_ss())[] >>
rw[] >> qexists_tac `v` >> rw[] >>
qmatch_assum_rename_tac `n < LENGTH ls` [] >>
qexists_tac `n` >> rw[] >>
first_x_assum (qspec_then `SUC m` mp_tac) >>
rw[])

val Cevaluate_list_with_value = store_thm(
"Cevaluate_list_with_value",
``!P ls vs. Cevaluate_list_with P ls (Rval vs) = (LENGTH ls = LENGTH vs) ∧ ∀n. n < LENGTH ls ⇒ P (EL n ls) (Rval (EL n vs))``,
gen_tac >> Induct >- rw[Cevaluate_list_with_nil,LENGTH_NIL_SYM] >>
gen_tac >> Cases >> rw[Cevaluate_list_with_cons,EQ_IMP_THM] >- (
  Cases_on `n` >> fs[] )
>- (
  first_x_assum (qspec_then `0` mp_tac) >>
  rw[] ) >>
first_x_assum (qspec_then `SUC n` mp_tac) >>
rw[])

val Cevaluate_list_with_mono = store_thm(
"Cevaluate_list_with_mono",
``∀P Q es res. Cevaluate_list_with P es res ⇒ (∀e r. MEM e es ∧ P e r ⇒ Q e r) ⇒ Cevaluate_list_with Q es res``,
ntac 2 strip_tac >>
ho_match_mp_tac Cevaluate_list_with_ind >>
rw[Cevaluate_list_with_cons] >> PROVE_TAC[])

val Cevaluate_list_with_EVERY = store_thm(
"Cevaluate_list_with_EVERY",
``∀P es vs. Cevaluate_list_with P es (Rval vs) = (LENGTH es = LENGTH vs) ∧ EVERY (UNCURRY P) (ZIP (es,MAP Rval vs))``,
gen_tac >> Induct >- (
  rw[Cevaluate_list_with_nil,LENGTH_NIL_SYM,EQ_IMP_THM] ) >>
rw[Cevaluate_list_with_cons,EQ_IMP_THM] >> rw[] >>
Cases_on `vs` >> fs[])

val Cpmatch_list_FOLDL2 = store_thm(
"Cpmatch_list_FOLDL2",
``∀ps vs. (LENGTH ps = LENGTH vs) ⇒ ∀env. Cpmatch_list env ps vs =
  FOLDL2 (λa p v. Cmatch_bind a (λenv. Cpmatch env p v)) (Cmatch env) ps vs``,
Induct >- ( Cases >> rw[Cpmatch_def,FOLDL2_def] ) >>
gen_tac >> Cases >>
rw[Cpmatch_def,FOLDL2_def] >>
qmatch_rename_tac `X = FOLDL2 f (Cpmatch env p v) ps vs` ["X","f"] >>
Cases_on `Cpmatch env p v` >> rw[] >>
rpt (pop_assum kall_tac) >>
qid_spec_tac `vs` >>
Induct_on `ps` >> rw[FOLDL2_def] >>
Cases_on `vs` >> rw[FOLDL2_def])

val Cpmatch_nice_ind = save_thm(
"Cpmatch_nice_ind",
Cpmatch_ind
|> Q.SPECL [`P`,`K (K (K T))`] |> SIMP_RULE (srw_ss()) []
|> Q.GEN `P`)

val Cmatch_map_o = store_thm(
"Cmatch_map_o",
``∀f1 f2 m. Cmatch_map f1 (Cmatch_map f2 m) = Cmatch_map (f1 o f2) m``,
ntac 2 gen_tac >> Cases >> rw[])

val Cpmatch_FEMPTY = store_thm(
"Cpmatch_FEMPTY",
``(∀env p v. Cpmatch env p v = Cmatch_map (combin$C $FUNION env) (Cpmatch FEMPTY p v))
 ∧(∀env ps vs. Cpmatch_list env ps vs = Cmatch_map (combin$C $FUNION env) (Cpmatch_list FEMPTY ps vs))``,
ho_match_mp_tac Cpmatch_ind >>
rw[] >>
TRY ((qmatch_abbrev_tac `Cpmatch_list env (p::ps) (v::vs) = X` >>
  unabbrev_all_tac >>
  simp_tac std_ss [Cpmatch_def] >>
  pop_assum (SUBST1_TAC) >>
  Cases_on `Cpmatch FEMPTY p v` >>
  simp_tac std_ss [Cmatch_bind_def,Cmatch_map_def] >>
  qmatch_assum_rename_tac `Cpmatch FEMPTY p v = Cmatch env'` [] >>
  match_mp_tac EQ_TRANS >>
  qexists_tac `Cmatch_map (combin$C $FUNION (env' ⊌ env)) (Cpmatch_list FEMPTY ps vs)` >>
  conj_tac >- PROVE_TAC[] >>
  qsuff_tac `combin$C $FUNION (env' ⊌ env) = combin$C $FUNION env o combin$C $FUNION env'`
    >- metis_tac[Cmatch_map_o] >>
  rw[FUN_EQ_THM,FUNION_ASSOC])
ORELSE rw[Cpmatch_def,FUNION_FEMPTY_1]) >- (
  rw[GSYM fmap_EQ_THM] >- (
    MATCH_ACCEPT_TAC INSERT_SING_UNION ) >>
  rw[FUNION_DEF,FAPPLY_FUPDATE_THM] ))

val Cpmatch_pat_vars = store_thm(
"Cpmatch_pat_vars",
``(∀env p v env'. (Cpmatch env p v = Cmatch env') ⇒ (FDOM env' = FDOM env ∪ Cpat_vars p))
 ∧(∀env ps vs env'. (Cpmatch_list env ps vs = Cmatch env') ⇒ (FDOM env' = FDOM env ∪ BIGUNION (IMAGE Cpat_vars (set ps))))``,
ho_match_mp_tac Cpmatch_ind >>
rw[Cpmatch_def,FOLDL_UNION_BIGUNION] >> rw[] >-
  rw[Once INSERT_SING_UNION,Once UNION_COMM] >>
Cases_on `Cpmatch env p v` >> fs[] >>
qmatch_assum_rename_tac `Cpmatch env p v = Cmatch env1` [] >>
first_x_assum (qspec_then `env1` mp_tac) >> rw[] >>
rw[UNION_ASSOC])

(* Invariants *)

val good_cm_cw_def = Define`
  good_cm_cw cm cw =
  (FDOM cw = FRANGE cm) ∧
  (FRANGE cw = FDOM cm) ∧
  (∀x. x ∈ FDOM cm ⇒ (cw ' (cm ' x) = x)) ∧
  (∀y. y ∈ FDOM cw ⇒ (cm ' (cw ' y) = y))`

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

val good_G_def = Define`
  good_G G =
    (∀cm v Cv. v_Cv G cm v Cv ⇒ G cm v Cv) ∧
    (∀cm v Cv cw.
      good_cm_cw cm cw ∧
      G cm v Cv ⇒ ((v_to_ov v) = (Cv_to_ov cw) Cv))`

val a_good_G_exists = store_thm(
"a_good_G_exists",
``∃G. good_G G``,
qexists_tac `v_Cv (K (K (K F)))` >>
rw[good_G_def] >- (
  qsuff_tac `∀G cm v Cv. v_Cv G cm v Cv ⇒ (G = v_Cv (K(K(K F)))) ⇒ v_Cv (K(K(K F))) cm v Cv` >- rw[] >>
  ho_match_mp_tac v_Cv_ind >>
  rw[] >>
  rw[v_Cv_cases] >>
  fsrw_tac[boolSimps.ETA_ss][] ) >>
qsuff_tac `∀G cm v Cv. v_Cv G cm v Cv ⇒ (G = K(K(K F))) ∧ good_cm_cw cm cw ⇒ (v_to_ov v = Cv_to_ov cw Cv)` >- (rw[] >> PROVE_TAC[]) >>
ho_match_mp_tac v_Cv_ind >>
rw[] >- fs[good_cm_cw_def] >>
pop_assum mp_tac >>
srw_tac[boolSimps.ETA_ss][] >>
rw[MAP_EQ_EVERY2] >>
PROVE_TAC[EVERY2_LENGTH])

val tac =
WF_REL_TAC `inv_image $< (λx. case x of (INL e) => exp_size e | (INR v) => v_size v)` >>
rw[MiniMLTerminationTheory.exp1_size_thm,
   MiniMLTerminationTheory.exp3_size_thm,
   MiniMLTerminationTheory.exp6_size_thm,
   MiniMLTerminationTheory.exp8_size_thm,
   MiniMLTerminationTheory.exp9_size_thm] >>
srw_tac[ARITH_ss][] >>
imp_res_tac ALOOKUP_MEM >>
(Q.ISPEC_THEN `exp2_size` imp_res_tac SUM_MAP_MEM_bound) >>
(Q.ISPEC_THEN `exp5_size` imp_res_tac SUM_MAP_MEM_bound) >>
(Q.ISPEC_THEN `exp7_size` imp_res_tac SUM_MAP_MEM_bound) >>
(Q.ISPEC_THEN `exp_size` imp_res_tac SUM_MAP_MEM_bound) >>
(Q.ISPEC_THEN `v_size` imp_res_tac SUM_MAP_MEM_bound) >>
fsrw_tac[ARITH_ss][exp_size_def]

(*
something broken in tDefine. don't need this now anyway...
val FV_def = tDefine "FV"`
(FV_exp (Raise _) = {}) ∧
(FV_exp (Val v) = FV_v v) ∧
(FV_exp (Con _ ls) = BIGUNION (IMAGE FV_exp (set ls))) ∧
(FV_exp (Var x) = {x}) ∧
(FV_exp (Fun x e) = FV_exp e DIFF {x}) ∧
(FV_exp (App _ e1 e2) = FV_exp e1 ∪ FV_exp e2) ∧
(FV_exp (Log _ e1 e2) = FV_exp e1 ∪ FV_exp e2) ∧
(FV_exp (If e1 e2 e3) = FV_exp e1 ∪ FV_exp e2 ∪ FV_exp e3) ∧
(FV_exp (Mat e pes) = FV_exp e ∪ BIGUNION (IMAGE (λ(p,e). FV_exp e DIFF pat_vars p) (set pes))) ∧
(FV_exp (Let x e b) = FV_exp e ∪ (FV_exp b DIFF {x})) ∧
(FV_exp (Letrec defs b) = BIGUNION (IMAGE (λ(y,x,e). FV_exp e DIFF {x}) (set defs)) ∪ (FV_exp b DIFF (IMAGE FST (set defs)))) ∧
(FV_v (Lit _) = {}) ∧
(FV_v (Conv _ vs) = BIGUNION (IMAGE FV_v (set vs))) ∧
(FV_v (Closure env x e) = BIGUNION (IMAGE (λ(n,v). FV_v v) (set env)) ∪ FV_exp e DIFF {x} DIFF (IMAGE FST (set env))) ∧
(FV_v (Recclosure env defs y) = case ALOOKUP defs y of NONE => {}
| SOME (x,e) =>
  BIGUNION (IMAGE (λ(n,v). FV_v v) (set env)) ∪
  BIGUNION (IMAGE (λ(y,x,e). FV_exp e DIFF {x}) (set defs)) ∪
  FV_exp e DIFF {x} DIFF (IMAGE FST (set defs)) DIFF (IMAGE FST (set env)))` tac
val _ = export_rewrites["FV_def"]
*)

val clV_def = tDefine "clV"`
(clV_exp (Raise _) = {}) ∧
(clV_exp (Val v) = clV_v v) ∧
(clV_exp (Con _ ls) = BIGUNION (IMAGE clV_exp (set ls))) ∧
(clV_exp (Var _) = {}) ∧
(clV_exp (Fun _ e) = clV_exp e) ∧
(clV_exp (App _ e1 e2) = clV_exp e1 ∪ clV_exp e2) ∧
(clV_exp (Log _ e1 e2) = clV_exp e1 ∪ clV_exp e2) ∧
(clV_exp (If e1 e2 e3) = clV_exp e1 ∪ clV_exp e2 ∪ clV_exp e3) ∧
(clV_exp (Mat e pes) = clV_exp e ∪ BIGUNION (IMAGE (λ(p,e). clV_exp e) (set pes))) ∧
(clV_exp (Let _ e b) = clV_exp e ∪ clV_exp b) ∧
(clV_exp (Letrec defs b) = BIGUNION (IMAGE (λ(y,x,e). clV_exp e) (set defs)) ∪ clV_exp b) ∧
(clV_v (Lit _) = {}) ∧
(clV_v (Conv _ vs) = BIGUNION (IMAGE clV_v (set vs))) ∧
(clV_v (Closure env _ e) = IMAGE FST (set env) ∪
  BIGUNION (IMAGE (λ(n,v). clV_v v) (set env)) ∪
  clV_exp e) ∧
(clV_v (Recclosure env defs _) = IMAGE FST (set defs) ∪ IMAGE FST (set env) ∪
  BIGUNION (IMAGE (λ(n,v). clV_v v) (set env)) ∪
  BIGUNION (IMAGE (λ(y,x,e). clV_exp e) (set defs)))` tac
val _ = export_rewrites["clV_def"]


val good_envs_def = Define`
  good_envs env s s' Cenv = s.cmap SUBMAP s'.cmap`

val good_cmap_def = Define`
good_cmap cenv cm =
  (∀cn n. do_con_check cenv cn n ⇒ cn IN FDOM cm)`

val good_env_state_def = Define`
  good_env_state env s =
  ALL_DISTINCT (MAP FST env) ∧
  INJ (FAPPLY s.m) (FDOM s.m) UNIV ∧
  IMAGE FST (set env) ∪
  BIGUNION (IMAGE (clV_v o SND) (set env))
  ⊆ FDOM s.m`


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
  fs[EVERY2_EVERY,EVERY_MEM] >>
  qpat_assum `LENGTH es = LENGTH ces` assume_tac >>
  fsrw_tac[boolSimps.DNF_ss][MEM_ZIP] >>
  first_x_assum (assume_tac o (CONV_RULE (RESORT_FORALL_CONV (fn [n,cenv,res,cw] => [cenv,cw,n,res] | _ => raise mk_HOL_ERR"""""")))) >>
  pop_assum (qspecl_then [`cenv`,`cw`] mp_tac) >> rw[] >>
  fs[GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] >>
  fs[evaluate_con,Cevaluate_con] >>
  Cases_on `do_con_check cenv cn (LENGTH Ces)` >> fs[] >> rw[] >- (
    fs[evaluate_list_with_evaluate,evaluate_list_with_error,Cevaluate_list_with_Cevaluate,Cevaluate_list_with_error] >>
    qexists_tac `f n (Rerr err)` >> rw[] >>
    first_assum (qspecl_then [`n`,`Rerr err`] mp_tac) >>
    Cases_on `f n (Rerr err)` >> rw[Cevaluate_list_with_error] >>
    qexists_tac `n` >> rw[] >>
    res_tac >>
    first_x_assum (qspecl_then [`m`,`Rval v`] mp_tac) >>
    `m < LENGTH Ces` by srw_tac[ARITH_ss][] >>
    rw[] >>
    Cases_on `f m (Rval v)` >> fs[] >>
    metis_tac[] )
  >- (
    fs[evaluate_list_with_evaluate,Cevaluate_list_with_Cevaluate] >>
    fs[evaluate_list_with_value,Cevaluate_list_with_value] >>
    qexists_tac `Rval (CConv (cm ' cn) (GENLIST (λn. @v. (f n (Rval (EL n vs))) = Rval v) (LENGTH vs)))` >>
    rw[] >- (
      first_x_assum (qspec_then `n` mp_tac) >>
      first_x_assum (qspec_then `n` mp_tac) >>
      rw[] >>
      first_x_assum (qspec_then `Rval (EL n vs)` mp_tac) >>
      Cases_on `f n (Rval (EL n vs))` >> rw[] )
    >- (
      fs[good_cmaps_def,good_cm_cw_def] ) >>
    rw[MAP_EQ_EVERY2,EVERY2_EVERY,EVERY_MEM,MEM_ZIP,pairTheory.FORALL_PROD] >>
    rw[EL_GENLIST] >>
    first_x_assum (qspec_then `n` mp_tac) >>
    first_x_assum (qspec_then `n` mp_tac) >>
    rw[] >>
    first_x_assum (qspec_then `Rval (EL n vs)` mp_tac) >>
    Cases_on `f n (Rval (EL n vs))` >> rw[] ) >>
  qexists_tac `Rerr Rtype_error` >> rw[] >>
  need Cevaluate to do a con check?
  ) >>
fs[evaluate_var] >> fs[] >> rw[] >>
fs[good_G_def,good_cmaps_def] >>
first_x_assum (match_mp_tac o GSYM) >>
metis_tac[])
*)

(* Lemmas *)

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

local open relationTheory in
(* TODO: move, or use set_relation stuff? *)
val countable_has_linear_order = store_thm(
"countable_has_linear_order",
``countable (UNIV:'a set) ==>
  ?(r:'a->'a->bool). antisymmetric r /\ transitive r /\ total r``,
SRW_TAC[][countable_def,INJ_DEF] THEN
Q.EXISTS_TAC `inv_image $<= f` THEN
SRW_TAC[][antisymmetric_def,
          transitive_def,
          total_def,
          inv_image_def] THEN
METIS_TAC[arithmeticTheory.LESS_EQUAL_ANTISYM,
          arithmeticTheory.LESS_EQ_TRANS,
          arithmeticTheory.LESS_EQ_CASES])
end

val FOLDL2_FUPDATE_LIST = store_thm(
"FOLDL2_FUPDATE_LIST",
``!f1 f2 bs cs a. (LENGTH bs = LENGTH cs) ⇒
  (FOLDL2 (λfm b c. fm |+ (f1 b c, f2 b c)) a bs cs =
   a |++ ZIP (MAP2 f1 bs cs, MAP2 f2 bs cs))``,
SRW_TAC[][FUPDATE_LIST,FOLDL2_FOLDL,MAP2_MAP,ZIP_MAP,MAP_ZIP,
          rich_listTheory.FOLDL_MAP,rich_listTheory.LENGTH_MAP2,
          LENGTH_ZIP,pairTheory.LAMBDA_PROD])

val FOLDL2_FUPDATE_LIST_paired = store_thm(
"FOLDL2_FUPDATE_LIST_paired",
``!f1 f2 bs cs a. (LENGTH bs = LENGTH cs) ⇒
  (FOLDL2 (λfm b (c,d). fm |+ (f1 b c d, f2 b c d)) a bs cs =
   a |++ ZIP (MAP2 (λb. UNCURRY (f1 b)) bs cs, MAP2 (λb. UNCURRY (f2 b)) bs cs))``,
rw[FOLDL2_FOLDL,MAP2_MAP,ZIP_MAP,MAP_ZIP,LENGTH_ZIP,
   pairTheory.UNCURRY,pairTheory.LAMBDA_PROD,FUPDATE_LIST,
   rich_listTheory.FOLDL_MAP])

val FOLDL_FUPDATE_LIST = store_thm(
"FOLDL_FUPDATE_LIST",
``!f1 f2 ls a. FOLDL (\fm k. fm |+ (f1 k, f2 k)) a ls =
  a |++ MAP (\k. (f1 k, f2 k)) ls``,
SRW_TAC[][FUPDATE_LIST,rich_listTheory.FOLDL_MAP])

val SND_FOLDL2_FUPDATE_LIST = store_thm(
"SND_FOLDL2_FUPDATE_LIST",
``!f1 f2 bs cs a n. (LENGTH bs = LENGTH cs) ⇒
  (SND (FOLDL2 (λ(n,fm) b c. (n + 1, fm |+ (f1 n b c, f2 n b c))) (n,a) bs cs) =
   let ns = GENLIST ($+ n) (LENGTH cs) in
   a |++ ZIP (MAP2 (UNCURRY f1) (ZIP (ns,bs)) cs, MAP2 (UNCURRY f2) (ZIP (ns,bs)) cs))``,
ntac 2 gen_tac >>
Induct >- rw[LENGTH_NIL,LENGTH_NIL_SYM,LET_THM,FUPDATE_LIST_THM] >>
gen_tac >> Cases >> rw[LET_THM] >>
fs[FUPDATE_LIST_THM,LET_THM,GENLIST_CONS] >>
`$+ n o SUC = $+ (n + 1)` by (
  srw_tac[ARITH_ss][FUN_EQ_THM] ) >>
rw[])

val UNCURRY_K_I_o_FST = store_thm(
"UNCURRY_K_I_o_FST",
``UNCURRY K = I o FST``,
SRW_TAC[][FUN_EQ_THM,pairTheory.LAMBDA_PROD,pairTheory.FORALL_PROD])

val num_Cv_linear_order_linear = store_thm(
"num_Cv_linear_order_linear",
``total (a_linear_order:num#Cv->num#Cv->bool) ∧
  transitive (a_linear_order:num#Cv->num#Cv->bool) ∧
  antisymmetric (a_linear_order:num#Cv->num#Cv->bool)``,
fs[fsetTheory.a_linear_order_def] >>
SELECT_ELIM_TAC >> rw[] >>
match_mp_tac countable_has_linear_order >>
rw[countable_def] >>
qexists_tac `count_prod_aux count_num_aux count_Cv_aux` >>
rw[INJ_DEF])

val mk_env_canon = store_thm(
"mk_env_canon",
``!(env1:((num,Cv) alist)) env2 exp ns. (mk_env env1 exp ns = mk_env env2 exp ns) =
  (∀x. x ∈ free_vars exp DIFF ns ⇒ (ALOOKUP (env1++[(x,CLit(Bool F))]) x = ALOOKUP (env2++[(x,CLit(Bool F))]) x))``,
rw[mk_env_def,sort_Cenv_def] >>
rw[num_Cv_linear_order_linear,QSORT_eq_if_PERM,PERM_fmap_to_alist,fsetTheory.force_dom_def,GSYM fmap_EQ_THM,FUN_FMAP_DEF] >>
simp_tac bool_ss [GSYM (CONJUNCT1 ALOOKUP_EQ_FLOOKUP),alist_to_fmap_APPEND] >>
rw[FLOOKUP_DEF,FUNION_DEF])

val force_dom_DRESTRICT_FUNION = store_thm(
"force_dom_DRESTRICT_FUNION",
``FINITE s ⇒ (force_dom fm s d = (DRESTRICT fm s ⊌ (FUN_FMAP (K d) s)))``,
rw[fsetTheory.force_dom_def,GSYM fmap_EQ_THM,DRESTRICT_DEF,FUN_FMAP_DEF,FUNION_DEF] >>
rw[EXTENSION,EQ_IMP_THM,NOT_FDOM_FAPPLY_FEMPTY])

val FUN_FMAP_FAPPLY_FEMPTY_FAPPLY = store_thm(
"FUN_FMAP_FAPPLY_FEMPTY_FAPPLY",
``FINITE s ==> (FUN_FMAP ($FAPPLY FEMPTY) s ' x = FEMPTY ' x)``,
Cases_on `x IN s` >>
rw[FUN_FMAP_DEF,NOT_FDOM_FAPPLY_FEMPTY])
val _ = export_rewrites["FUN_FMAP_FAPPLY_FEMPTY_FAPPLY"]

(*
fun PROVE_FINITE tm = prove(tm,
  rw[pairTheory.UNCURRY] >> rw[])

val FDOM_FUN_FMAP_conv = let
  val fdomth = FUN_FMAP_DEF
    |> SPEC_ALL
    |> UNDISCH_ALL
    |> CONJUNCT1
    |> DISCH_ALL
    |> GEN_ALL
  val FDOM = ``FDOM``
  val FUN_FMAP = ``FUN_FMAP``
in
  DEPTH_CONV (
fn tm => let
  val (x,fm) = dest_comb tm
  val true = same_const x FDOM
  val (x,[f,P]) = strip_comb fm
  val true = same_const x FUN_FMAP
  val th = ISPECL [f,P] fdomth
  val (fi,_) = dest_imp (concl th)
  val ft = PROVE_FINITE fi
  val res = MP th ft
in res end
handle Bind => raise (mk_HOL_ERR""""""))
end
*)

val FINITE_rw0 = prove(
``FINITE (free_vars e DIFF x UNION BIGUNION (IMAGE free_vars (set ls)))``,
rw[] >> rw[])
val FINITE_rw1 = prove(
``FINITE (free_vars e DIFF x UNION (free_vars e2 UNION BIGUNION (IMAGE free_vars (set ls))))``,
rw[] >> rw[])
val FINITE_rw2 = prove(
``FINITE (free_vars exp DIFF setns UNION (BIGUNION (IMAGE (λ(vs,e'). free_vars e' DIFF (sset vs)) (set ls))))``,
rw[] >> rw[pairTheory.UNCURRY])
val FINITE_rw3 = prove(
``FINITE (free_vars e UNION BIGUNION (IMAGE free_vars (set ls)))``,
rw[] >> rw[])
val _ = augment_srw_ss[rewrites[FINITE_rw0,FINITE_rw1,FINITE_rw2,FINITE_rw3]]

val FUPDATE_LIST_APPLY_NOT_MEM_matchable = store_thm(
"FUPDATE_LIST_APPLY_NOT_MEM_matchable",
``!kvl f k v. ~MEM k (MAP FST kvl) /\ (v = f ' k) ==> ((f |++ kvl) ' k = v)``,
PROVE_TAC[FUPDATE_LIST_APPLY_NOT_MEM])

val MAP_ZIP_unfolded = let
fun f th = let
  val th = SPEC_ALL th
  val tm = rand(lhs(concl th))
  val th = PairRules.PABS tm th
  in CONV_RULE (LAND_CONV PairRules.PETA_CONV) th end
in
MAP_ZIP
|> SIMP_RULE (srw_ss()) [f pairTheory.FST,f pairTheory.SND]
end

val Cexp_size_def = CompileTheory.Cexp_size_def

(*
fun mk_EVERY ty = let
  val (name,_) = dest_type ty
  val EVERY_ty = "EVERY_"^name
  val P = mk_var("P"^name,ty-->bool)
  val EVERY_ty = mk_var(EVERY_ty,(ty-->bool)-->ty-->bool)
  val args = map (rhs o #2 o strip_exists) (strip_disj(#2(strip_forall(concl(TypeBase.nchotomy_of ty)))))
  fun f (x,(vs,acc)) = let val v = with_flag (Globals.priming,SOME"") (variant vs) x in (v::vs,v::acc) end
  fun g (tm,(vs,acc)) = let
    val (c,bs) = strip_comb tm
    val (vs,bs) = foldl f (vs,[]) bs
  in (vs,(list_mk_comb(c,rev bs))::acc) end
  val (_,args) = foldl g ([EVERY_ty,P],[]) args
  fun f (tm,acc) = let val ty' = type_of tm in
  let val ty'' = listSyntax.dest_list_type ty' in
  let val (tya,tyb) = pairSyntax.dest_prod ty'' in
  let
    fun f p = listSyntax.mk_every(mk_comb(EVERY_ty,P),listSyntax.mk_map(inst[alpha|->tya,beta|->tyb]p,tm))
    val acc = if tya = ty then (f pairSyntax.fst_tm)::acc else acc
    val acc = if tyb = ty then (f pairSyntax.snd_tm)::acc else acc
  in acc end
  end handle HOL_ERR {origin_function="dest_prod",...} =>
    if ty'' = ty then listSyntax.mk_every(mk_comb(EVERY_ty,P),tm)::acc else acc
  end handle HOL_ERR {origin_function="dest_list_type",...} =>
    if ty' = ty then list_mk_comb(EVERY_ty,[P,tm])::acc else acc
  end
  fun eq tm = mk_eq(list_mk_comb(EVERY_ty,[P,tm]),list_mk_conj((mk_comb(P,tm))::(foldl f [] (#2(strip_comb tm)))))
  val eqs = map eq args
in [ANTIQUOTE (list_mk_conj eqs)] end
*)

val variant_args = let
  fun f (x,(vs,acc)) = let val v = with_flag (Globals.priming,SOME"") (variant vs) x in (v::vs,v::acc) end
  fun g (tm,(vs,acc)) = let
    val (c,bs) = strip_comb tm
    val (vs,bs) = foldl f (vs,[]) bs
  in (vs,(list_mk_comb(c,rev bs))::acc) end
in g end

fun args_from_nchotomy ty = map (rhs o #2 o strip_exists) (strip_disj(#2(strip_forall(concl(TypeBase.nchotomy_of ty)))))

fun uneta tm = let
  val (t,_) = dom_rng (type_of tm)
  val x = genvar t
in mk_abs(x,mk_comb(tm,x)) end

fun find_tys listfn add (tm,acc) =
let val ty' = type_of tm in
let val ty'' = listSyntax.dest_list_type ty' in
let val (tya,tyb) = pairSyntax.dest_prod ty'' in
let
  fun f p EVP = listfn((*uneta*) EVP,listSyntax.mk_map(inst[alpha|->tya,beta|->tyb]p,tm))
  val acc = add (f pairSyntax.fst_tm) tya acc
  val acc = add (f pairSyntax.snd_tm) tyb acc
in acc end
end handle HOL_ERR {origin_function="dest_prod",...} =>
  add (fn EVP => listfn((*uneta*) EVP,tm)) ty'' acc
end handle HOL_ERR {origin_function="dest_list_type",...} =>
  add (fn EVP => mk_comb(EVP,tm)) ty' acc
end

fun lmk_conj ls = list_mk_conj ls handle HOL_ERR _ => T
fun lmk_disj ls = list_mk_disj ls handle HOL_ERR _ => F

(*
fun mk_cvtr conjfn listfn name ty1 ty2 = let
  val P = mk_var("P",ty1-->bool)
  val cvtr = mk_var(name,(ty1-->bool)-->ty2-->bool)
  val cP = mk_comb(cvtr,P)
  val args = args_from_nchotomy ty2
  val (_,args) = foldl variant_args ([cvtr,P],[]) args
  fun add f ty acc = if ty = ty1 then f P :: acc else acc
  fun eq tm = mk_eq(mk_comb(cP,tm),conjfn(foldl (find_tys listfn add) [] (#2(strip_comb tm))))
  val eqs = map eq args
  val eqs = list_mk_conj eqs
in [ANTIQUOTE eqs] end

val mk_every_cvtr = mk_cvtr lmk_conj listSyntax.mk_every
val mk_exists_cvtr = mk_cvtr lmk_disj listSyntax.mk_exists

fun mk_EVERY cvtr tys = let
  val names = map (#1 o dest_type) tys
  val EVERY_tys = map (fn n => "EVERY_"^n) names
  val Ps = map (fn (n,ty) => mk_var("P"^n,ty-->bool)) (zip names tys)
  val EVERY_tys = map (fn (EVERY_ty,ty) => mk_var(EVERY_ty,(ty-->bool)-->ty-->bool)) (zip EVERY_tys tys)
  val argss = map args_from_nchotomy tys
  fun h (tms,(vs,acc)) = let
    val (vs,tms) = foldl variant_args (vs,[]) tms
  in (vs,tms::acc) end
  val (_,argss) = foldl h (EVERY_tys@Ps,[]) argss
  fun add j f ty acc =
    case total (index (equal ty)) tys of
      NONE => acc
    | SOME i => let
      val EV = List.nth(EVERY_tys,j)
      val P = List.nth(Ps,j)
      val EVP = mk_comb(EV,P)
      val EVP = if i = j then EVP
        else mk_comb(List.nth(EVERY_tys,i),uneta(mk_comb(cvtr j i,uneta EVP)))
      in f EVP :: acc end
  fun eq tm = let
    val ty = type_of tm
    val i = index (equal ty) tys
    val EVERY_ty = List.nth(EVERY_tys,i)
    val P = List.nth(Ps,i)
  in
    mk_eq(list_mk_comb(EVERY_ty,[P,tm]),list_mk_conj((mk_comb(P,tm))::(foldl (find_tys listSyntax.mk_every (add i)) [] (#2(strip_comb tm)))))
  end
  val eqs = list_mk_conj (map eq (rev (flatten argss)))
in [ANTIQUOTE eqs] end

val EVERY_Cbody_def = Define (mk_every_cvtr "EVERY_Cbody" ``:Cexp`` ``:Cv``)
val EVERY_CVal_def = Define (mk_every_cvtr "EVERY_CVal" ``:Cv`` ``:Cexp``)
val EXISTS_Cbody_def = Define (mk_exists_cvtr "EXISTS_Cbody" ``:Cexp`` ``:Cv``)
val EXISTS_CVal_def = Define (mk_exists_cvtr "EXISTS_CVal" ``:Cv`` ``:Cexp``)
val _ = export_rewrites["EVERY_Cbody_def","EVERY_CVal_def","EXISTS_Cbody_def","EXISTS_CVal_def"]

fun cvtr 0 1 = ``EVERY_Cbody`` | cvtr 1 0 = ``EVERY_CVal``

val EVERY_Cbody_cong = store_thm(
"EVERY_Cbody_cong",
``!P P' Cv Cv'. (Cv = Cv') ∧ (∀x. EXISTS_Cbody ($= x) Cv' ==> (P x = P' x))
==> (EVERY_Cbody P Cv = EVERY_Cbody P' Cv')``,
ntac 2 gen_tac >>
Induct >> rw[] >> rw[] >> fs[] >>
fs[EVERY_MAP,EXISTS_MAP] >>
fs[EVERY_MEM,EXISTS_MEM] >>
metis_tac[])
val _ = DefnBase.export_cong"EVERY_Cbody_cong"

val EVERY_CVal_cong = store_thm(
"EVERY_CVal_cong",
``!P P' Cv Cv'. (Cv = Cv') ∧ (∀x. EXISTS_CVal ($= x) Cv' ==> (P x = P' x))
==> (EVERY_CVal P Cv = EVERY_CVal P' Cv')``,
ntac 2 gen_tac >>
Induct >> rw[] >> rw[] >> fs[] >>
fs[EVERY_MAP,EXISTS_MAP] >>
fs[EVERY_MEM,EXISTS_MEM] >>
metis_tac[])
val _ = DefnBase.export_cong"EVERY_CVal_cong"

val EVERY_Cexp_eqs = mk_EVERY cvtr [``:Cexp``,``:Cv``]

val _ = Hol_datatype`
  ty1 = C1 | C2 of ty2 ;
  ty2 = D1 of ty1`
val foo_def = xDefine "foo"`
  (foo P C1 = P C1) /\
  (foo P (C2 t2) = bar (\x. foo P x) t2) /\
  (bar P (D1 t1) = foo P t1)`
val foo_def = xDefine "foo"`
  (foo f P C1 = P C1) /\
  (foo f P (C2 t2) = f (\x. foo f P x) t2)`

val EVERY_Cexp_def = tDefine "EVERY_Cexp" EVERY_Cexp_eqs(
WF_REL_TAC `inv_image $< (λx. case x of | INR (_,v) => Cv_size v | INL (_,e) => Cexp_size e)` >>
srw_tac[ARITH_ss][Cexp3_size_thm,Cexp8_size_thm,Cexp7_size_thm,Cexp4_size_thm,Cexp1_size_thm] >>
Q.ISPEC_THEN `Cv_size` imp_res_tac SUM_MAP_MEM_bound >>
Q.ISPEC_THEN `Cexp_size` imp_res_tac SUM_MAP_MEM_bound >>
fsrw_tac[ARITH_ss][Cexp_size_def,SUM_MAP_Cexp2_size_thm,SUM_MAP_Cexp6_size_thm,SUM_MAP_Cexp5_size_thm] >>
TRY (qmatch_assum_rename_tac `EXISTS_CVal X yy` ["X"]) >>
TRY (qmatch_assum_rename_tac `EXISTS_Cbody X yy` ["X"]) >>
Cases_on`yy`>>fs[]
impossible because of mutual nested recursion
*)

(*
val EVERY_Cv_def = tDefine "EVERY_Cv" [EVERY_Cv_eqs](
WF_REL_TAC `measure (Cv_size o SND)` >>
srw_tac[ARITH_ss][Cexp3_size_thm,Cexp8_size_thm] >>
Q.ISPEC_THEN `Cv_size` imp_res_tac SUM_MAP_MEM_bound >>
fsrw_tac[ARITH_ss][SUM_MAP_Cexp5_size_thm] >>
qmatch_assum_rename_tac `EXISTS_CVal X cv` ["X"] >>
Cases_on`cv`>>fs[]>>rw[]>>
fsrw_tac[ARITH_ss][Cexp_size_def,Cexp1_size_thm,SUM_MAP_Cexp2_size_thm] >>
Q.ISPEC_THEN `Cexp_size` imp_res_tac SUM_MAP_MEM_bound >>
fsrw_tac[ARITH_ss][Cexp_size_def])
val EVERY_Cv_thm = save_thm(
"EVERY_Cv_thm",SIMP_RULE((srw_ss())++boolSimps.ETA_ss)[]EVERY_Cv_def)

val EVERY_Cexp_def = tDefine "EVERY_Cexp" [EVERY_Cexp_eqs](
WF_REL_TAC `measure (Cexp_size o SND)` >>
srw_tac[ARITH_ss][Cexp7_size_thm,Cexp4_size_thm,Cexp1_size_thm] >>
Q.ISPEC_THEN `Cexp_size` imp_res_tac SUM_MAP_MEM_bound >>
fsrw_tac[ARITH_ss][Cexp_size_def,SUM_MAP_Cexp2_size_thm,SUM_MAP_Cexp6_size_thm] >>
qmatch_assum_rename_tac `EXISTS_Cbody X ll` ["X"] >>
Cases_on`ll`>>fs[]>>rw[Cexp_size_def,Cexp3_size_thm,Cexp1_size_thm,SUM_MAP_Cexp2_size_thm,SUM_MAP_Cexp5_size_thm] >>
fs[EXISTS_MEM] >>
Q.ISPEC_THEN `Cexp_size` imp_res_tac SUM_MAP_MEM_bound >>
fsrw_tac[ARITH_ss][Cexp_size_def])
val EVERY_Cexp_thm = save_thm(
"EVERY_Cexp_thm",SIMP_RULE((srw_ss())++boolSimps.ETA_ss)[]EVERY_Cexp_def)

val _ = export_rewrites["EVERY_Cv_thm","EVERY_Cexp_thm"]
*)

fun mk_EVERY name eqns tys = let
  val tynames = map (#1 o dest_type) tys
  val foo_tys = map (fn n => name^"_"^n) tynames
  val foo_tys = map (fn (foo_ty,ty) => mk_var(foo_ty,ty-->bool)) (zip foo_tys tys)
  val argss = map args_from_nchotomy tys
  val lrs = map (((#2 o dest_comb) ## I) o dest_eq) eqns
  val lhss = map fst lrs
  val avoids = mk_set (foo_tys@(flatten (map (#2 o strip_comb) lhss)))
  fun h (tms,(vs,acc)) = let
    val (vs,tms) = foldl variant_args (vs,[]) tms
  in (vs,tms::acc) end
  val (_,argss) = foldl h (avoids,[]) argss
  val argss = map (fn args => map (fn t => case total (first (can (match_term t))) lhss of SOME l => l | NONE => t) args) argss
  fun add f ty acc =
    case total (index (equal ty)) tys of
      NONE => acc
    | SOME i => f (List.nth(foo_tys,i)) :: acc
  fun eq tm = let
    val ty = type_of tm
    val i = index (equal ty) tys
    val foo_ty = List.nth(foo_tys,i)
    val rhsl = case total (first ((equal tm) o #1)) lrs of NONE => [] | SOME (_,r) => [r]
    val rhs = lmk_conj(rev(foldl (find_tys listSyntax.mk_every add) rhsl (#2(strip_comb tm))))
  in
    mk_eq(mk_comb(foo_ty,tm),rhs)
  end
  val eqs = list_mk_conj (map eq (rev (flatten argss)))
in [ANTIQUOTE eqs] end

fun map_tys getf tm =
let val ty = type_of tm in
let val tyl = listSyntax.dest_list_type ty in
let val (tya,tyb) = pairSyntax.dest_prod tyl
    val va = mk_var("va",tya)
    val vb = mk_var("vb",tyb) in
case getf tya of NONE => (
  case getf tyb of NONE => tm
  | SOME fb =>
    listSyntax.mk_map(``λ(^va,^vb). (va, ^fb ^vb)``,tm))
| SOME fa => (
  case getf tyb of NONE =>
    listSyntax.mk_map(``λ(^va,^vb). (^fa ^va, ^vb)``,tm)
  | SOME fb =>
    listSyntax.mk_map(``λ(^va,^vb). (^fa ^va, ^fb ^vb)``,tm))
end handle HOL_ERR {origin_function="dest_prod",...} =>
case getf tyl of NONE => tm
| SOME f => listSyntax.mk_map(f,tm)
end handle HOL_ERR {origin_function="dest_list_type",...} =>
case getf ty of NONE => tm
| SOME f => mk_comb(f,tm)
end

fun mk_MAP name eqns tys = let
  val tynames = map (#1 o dest_type) tys
  val foo_tys = map (fn n => name^"_"^n) tynames
  val foo_tys = map (fn (foo_ty,ty) => mk_var(foo_ty,ty-->ty)) (zip foo_tys tys)
  val argss = map args_from_nchotomy tys
  val lrs = map (((#2 o dest_comb) ## I) o dest_eq) eqns
  val lhss = map fst lrs
  val avoids = mk_set (foo_tys@(flatten (map (#2 o strip_comb) lhss)))
  fun h (tms,(vs,acc)) = let
    val (vs,tms) = foldl variant_args (vs,[]) tms
  in (vs,tms::acc) end
  val (_,argss) = foldl h (avoids,[]) argss
  val argss = map (fn args => map (fn t => case total (first (can (match_term t))) lhss of SOME l => l | NONE => t) args) argss
  fun getf ty =
    Option.map (curry List.nth foo_tys)
    (total (index (equal ty)) tys)
  fun eq tm = let
    val ty = type_of tm
    val i = index (equal ty) tys
    val foo_ty = List.nth(foo_tys,i)
    val rhs = case total (first ((equal tm) o #1)) lrs
      of SOME (_,r) => r
      | NONE => let val (f,args) = strip_comb tm
        in list_mk_comb(f, map (map_tys getf) args) end
  in
    mk_eq(mk_comb(foo_ty,tm),rhs)
  end
  val eqs = list_mk_conj (map eq (rev (flatten argss)))
in [ANTIQUOTE eqs] end

(*
generated equations used in compile.lem:
val ce_Cexp_eqs = mk_MAP "ce" [
``ce_Cv (CClosure env ns b) =
  let env = MAP (λ(n,v). (n,ce_Cv v)) env in
  let b = ce_Cexp b in
    CClosure (mk_env env b (set ns)) ns b``,
``ce_Cv (CRecClos env ns defs n) =
  case (find_index n ns 0,LENGTH ns = LENGTH defs) of
  | (SOME i,T) => 
    let env = MAP (λ(n,v). (n,ce_Cv v)) env in
    let defs = MAP (λ(vs,b). (vs,ce_Cexp b)) defs in
    let (vs,b) = EL i defs in
    CRecClos (mk_env env b (set ns ∪ set vs)) ns defs n
  | _ => CClosure [] [] (CRaise Bind_error)``
]
[``:Cexp``,``:Cv``]
*)

val canonical_env_eqs = mk_EVERY
"canonical_env"
[(``canonical_env (CClosure env ns b) =
    (SORTED a_linear_order env) ∧
    (ALL_DISTINCT (MAP FST env)) ∧
    (FDOM (alist_to_fmap env) = free_vars b DIFF (set ns))``),
 (``canonical_env (CRecClos env ns bs n) =
    (SORTED a_linear_order env) ∧
    (ALL_DISTINCT (MAP FST env)) ∧
    (LENGTH ns = LENGTH bs) ∧
    case find_index n ns 0 of
      SOME i => (FDOM (alist_to_fmap env) = free_vars (SND (EL i bs)) DIFF (set (FST (EL i bs))) DIFF (set ns))
    | NONE => F``)]
[``:Cexp``,``:Cv``]

val canonical_env_def = tDefine "canonical_env" canonical_env_eqs(
WF_REL_TAC `inv_image $< (λx. case x of | INR v => Cv_size v | INL e => Cexp_size e)` >>
srw_tac[ARITH_ss][Cexp3_size_thm,Cexp8_size_thm,Cexp7_size_thm,Cexp4_size_thm,Cexp1_size_thm] >>
Q.ISPEC_THEN `Cv_size` imp_res_tac SUM_MAP_MEM_bound >>
Q.ISPEC_THEN `Cexp_size` imp_res_tac SUM_MAP_MEM_bound >>
fsrw_tac[ARITH_ss][Cexp_size_def,SUM_MAP_Cexp2_size_thm,SUM_MAP_Cexp6_size_thm,SUM_MAP_Cexp5_size_thm])
val canonical_env_thm = save_thm(
"canonical_env_thm",SIMP_RULE((srw_ss())++boolSimps.ETA_ss)[]canonical_env_def)
val canonical_env_ind = theorem"canonical_env_ind"
val _ = export_rewrites["canonical_env_thm"]

val FOLDL2_Cmatch_bind_error = store_thm(
"FOLDL2_Cmatch_bind_error",
``∀f ps vs.
(FOLDL2 (λa p v. Cmatch_bind a (f a p v)) Cno_match ps vs = Cno_match) ∧
  (FOLDL2 (λa p v. Cmatch_bind a (f a p v)) Cmatch_error ps vs = Cmatch_error)``,
gen_tac >> Induct >- (Cases >> rw[]) >>
gen_tac >> Cases >> rw[])

val Cpmatch_canonical_envs = store_thm(
"Cpmatch_canonical_envs",
``(∀env p v env'. (Cpmatch env p v = Cmatch env') ∧ (∀v. v ∈ FRANGE env ⇒ canonical_env_Cv v) ∧ canonical_env_Cv v ⇒ (∀v. v ∈ FRANGE env' ⇒ canonical_env_Cv v)) ∧
(∀env ps vs env'. (Cpmatch_list env ps vs = Cmatch env') ∧ (∀v. v ∈ FRANGE env ⇒ canonical_env_Cv v) ∧ EVERY canonical_env_Cv vs ⇒ (∀v. v ∈ FRANGE env' ⇒ canonical_env_Cv v))``,
ho_match_mp_tac Cpmatch_ind >>
rw[Cpmatch_def] >>
fs[FRANGE_DEF] >> rw[DOMSUB_FAPPLY_THM]
>- metis_tac[] >>
Cases_on `Cpmatch env p v` >> fs[] >>
qmatch_assum_rename_tac `Cpmatch env p v = Cmatch env''` [] >>
first_x_assum (qspecl_then [`env''`,`env'`] (match_mp_tac o MP_CANON)) >>
rw[] >> metis_tac[])

val FST_triple = store_thm(
"FST_triple",
``(λ(n,ns,b). n) = FST``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val SND_triple = store_thm(
"SND_triple",
``(λ(n,ns,b). f ns b) = UNCURRY f o SND``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val FST_pair = store_thm(
"FST_pair",
``(λ(n,v). n) = FST``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val SND_pair = store_thm(
"SND_pair",
``(λ(n,v). v) = SND``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val SND_FST_pair = store_thm(
"SND_FST_pair",
``(λ((n,m),c).m) = SND o FST``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val MEM_QSORT = store_thm(
"MEM_QSORT",
``MEM x (QSORT R ls) = MEM x ls``,
METIS_TAC[QSORT_PERM,MEM_PERM])
val _ = export_rewrites["MEM_QSORT"]

val MEM_sort_Cenv = store_thm(
"MEM_sort_Cenv",
``MEM x (sort_Cenv env) = MEM x env``,
rw[sort_Cenv_def])
val _ = export_rewrites["MEM_sort_Cenv"]

val LENGTH_QSORT = store_thm(
"LENGTH_QSORT",
``LENGTH (QSORT R ls) = LENGTH ls``,
METIS_TAC[QSORT_PERM,PERM_LENGTH])
val _ = export_rewrites["LENGTH_QSORT"]

val LENGTH_sort_Cenv = store_thm(
"LENGTH_sort_Cenv",
``LENGTH (sort_Cenv env) = LENGTH env``,
rw[sort_Cenv_def])
val _ = export_rewrites["LENGTH_sort_Cenv"]

val set_MAP_QSORT = store_thm(
"set_MAP_QSORT",
``set (MAP f (QSORT R ls)) = set (MAP f ls)``,
METIS_TAC[QSORT_PERM,PERM_LIST_TO_SET,PERM_MAP])
val _ = export_rewrites["set_MAP_QSORT"]

val set_MAP_sort_Cenv = store_thm(
"set_MAP_sort_Cenv",
``set (MAP f (sort_Cenv env)) = set (MAP f env)``,
rw[sort_Cenv_def])
val _ = export_rewrites["set_MAP_sort_Cenv"]

val PERM_MAP_sort_Cenv = store_thm(
"PERM_MAP_sort_Cenv",
``PERM (MAP f (sort_Cenv env)) (MAP f env)``,
metis_tac[sort_Cenv_def,QSORT_PERM,PERM_MAP,PERM_SYM])

val EVERY_QSORT = store_thm(
"EVERY_QSORT",
``EVERY P (QSORT R ls) = EVERY P ls``,
METIS_TAC[QSORT_PERM,EVERY_MEM,MEM_PERM])
val _ = export_rewrites["EVERY_QSORT"]

val EVERY_sort_Cenv = store_thm(
"EVERY_sort_Cenv",
``EVERY P (sort_Cenv env) = EVERY P env``,
rw[sort_Cenv_def])
val _ = export_rewrites["EVERY_sort_Cenv"]

val FDOM_force_dom = store_thm(
"FDOM_force_dom",
``∀s env d. FINITE s ⇒ (FDOM (force_dom env s d) = s)``,
rw[force_dom_DRESTRICT_FUNION,FDOM_DRESTRICT] >>
rw[EXTENSION] >> metis_tac[])
val _ = export_rewrites["FDOM_force_dom"]

val find_index_ALL_DISTINCT_EL = store_thm(
"find_index_ALL_DISTINCT_EL",
``∀ls n m. ALL_DISTINCT ls ∧ n < LENGTH ls ⇒ (find_index (EL n ls) ls m = SOME (m + n))``,
Induct >- rw[] >>
gen_tac >> Cases >>
srw_tac[ARITH_ss][find_index_def] >>
metis_tac[MEM_EL])
val _ = export_rewrites["find_index_ALL_DISTINCT_EL"]

val find_index_LESS_LENGTH = store_thm(
"find_index_LESS_LENGTH",
``∀ls n m i. (find_index n ls m = SOME i) ⇒ (i < m + LENGTH ls)``,
Induct >> rw[find_index_def] >>
res_tac >>
srw_tac[ARITH_ss][arithmeticTheory.ADD1])

val set_MAP_FST_fmap_to_alist = store_thm(
"set_MAP_FST_fmap_to_alist",
``set (MAP FST (fmap_to_alist fm)) = FDOM fm``,
METIS_TAC[fmap_to_alist_to_fmap,FDOM_alist_to_fmap])
val _ = export_rewrites["set_MAP_FST_fmap_to_alist"]

val DIFF_UNION = store_thm(
"DIFF_UNION",
``!x y z. x DIFF (y UNION z) = x DIFF y DIFF z``,
SRW_TAC[][EXTENSION] THEN METIS_TAC[])

val DIFF_COMM = store_thm(
"DIFF_COMM",
``!x y z. x DIFF y DIFF z = x DIFF z DIFF y``,
SRW_TAC[][EXTENSION] THEN METIS_TAC[])

val free_vars_ce_Cexp = store_thm(
"free_vars_ce_Cexp",
``(∀exp. free_vars (ce_Cexp exp) = free_vars exp)``,
CONV_TAC(
  ONCE_REWRITE_CONV[
    SYM (CONJUNCT1 (CONJUNCT2 (SPEC_ALL AND_CLAUSES)))] THENC
  RAND_CONV (ONCE_REWRITE_CONV[INST_TYPE[alpha|->``:Cv``](GSYM FORALL_SIMP)])) >>
ho_match_mp_tac ce_Cexp_ind >> rw[] >>
TRY (qmatch_rename_tac `X = free_vars (CLetfun b ns defs exp)` ["X"] >> Cases_on `b`) >>
rw[FOLDL_UNION_BIGUNION,FOLDL_UNION_BIGUNION_paired,LIST_TO_SET_MAP] >>
srw_tac[boolSimps.DNF_ss][EXTENSION,pairTheory.EXISTS_PROD] >>
metis_tac[])
val _ = export_rewrites["free_vars_ce_Cexp"]

(* TODO: move? *)
val INJ_I = store_thm(
"INJ_I",
``∀s t. INJ I s t = s ⊆ t``,
SRW_TAC[][INJ_DEF,SUBSET_DEF])

val alist_to_fmap_MAP_matchable = store_thm(
"alist_to_fmap_MAP_matchable",
``∀f1 f2 al mal v. INJ f1 (set (MAP FST al)) UNIV ∧
  (mal = MAP (λ(x,y). (f1 x,f2 y)) al) ∧
  (v = MAP_KEYS f1 (f2 o_f alist_to_fmap al)) ⇒
  (alist_to_fmap mal = v)``,
METIS_TAC[alist_to_fmap_MAP])

val MAP_KEYS_I = store_thm(
"MAP_KEYS_I",
``∀fm. MAP_KEYS I fm = fm``,
rw[GSYM fmap_EQ_THM,MAP_KEYS_def,EXTENSION] >>
metis_tac[MAP_KEYS_def,INJ_I,SUBSET_UNIV,combinTheory.I_THM])
val _ = export_rewrites["MAP_KEYS_I"]

val SORTED_sort_Cenv = store_thm(
"SORTED_sort_Cenv",
``∀env:(num,Cv) alist. SORTED a_linear_order (sort_Cenv env)``,
rw[sort_Cenv_def] >>
match_mp_tac QSORT_SORTED >>
rw[num_Cv_linear_order_linear])
val _ = export_rewrites["SORTED_sort_Cenv"]

val MAP_EQ_ID = store_thm(
"MAP_EQ_ID",
``!f ls. (MAP f ls = ls) = (!x. MEM x ls ==> (f x = x))``,
PROVE_TAC[MAP_EQ_f,MAP_ID,combinTheory.I_THM])

val force_dom_id =  store_thm(
"force_dom_id",
``FINITE s ⇒ ((force_dom fm s d = fm) = (s = FDOM fm))``,
rw[force_dom_DRESTRICT_FUNION,GSYM fmap_EQ_THM,FUNION_DEF,DRESTRICT_DEF,EQ_IMP_THM])

val sort_Cenv_id = store_thm(
"sort_Cenv_id",
``(sort_Cenv (env:(num,Cv)alist) = env) = (SORTED a_linear_order env)``,
rw[sort_Cenv_def,EQ_IMP_THM] >- (
  pop_assum (SUBST1_TAC o SYM) >>
  match_mp_tac QSORT_SORTED >>
  rw[num_Cv_linear_order_linear] ) >>
match_mp_tac (MP_CANON SORTED_PERM_EQ) >>
metis_tac[num_Cv_linear_order_linear,QSORT_SORTED,QSORT_PERM,PERM_SYM])

val ALL_DISTINCT_sort_Cenv = store_thm(
"ALL_DISTINCT_sort_Cenv",
``ALL_DISTINCT (sort_Cenv env) = ALL_DISTINCT env``,
metis_tac[sort_Cenv_def,QSORT_PERM,ALL_DISTINCT_PERM])
val _ = export_rewrites["ALL_DISTINCT_sort_Cenv"]

val ALL_DISTINCT_MAP_sort_Cenv = store_thm(
"ALL_DISTINCT_MAP_sort_Cenv",
``ALL_DISTINCT (MAP f (sort_Cenv env)) = ALL_DISTINCT (MAP f env)``,
metis_tac[ALL_DISTINCT_PERM,PERM_MAP_sort_Cenv])
val _ = export_rewrites["ALL_DISTINCT_MAP_sort_Cenv"]

val ce_Cexp_canonical_env = store_thm(
"ce_Cexp_canonical_env",
``(∀exp. canonical_env_Cexp (ce_Cexp exp)) ∧
  (∀v. canonical_env_Cv (ce_Cv v))``,
ho_match_mp_tac ce_Cexp_ind >>
rw[LET_THM,EVERY_MEM,MEM_MAP,pairTheory.EXISTS_PROD] >>
fsrw_tac[SATISFY_ss][] >>
TRY (rw[mk_env_def] >> NO_TAC) >>
TRY (
  pop_assum mp_tac >>
  fs[mk_env_def,FLOOKUP_DEF,force_dom_DRESTRICT_FUNION,DRESTRICT_DEF,FUNION_DEF] >>
  ntac 2 (rw[FUN_FMAP_DEF]) >>
  qmatch_rename_tac `canonical_env_Cv (alist_to_fmap fm ' x)`["fm"] >>
  qmatch_abbrev_tac `canonical_env_Cv (alist_to_fmap fm ' x)` >>
  `∃v. ALOOKUP fm x = SOME v` by (
    rw[ALOOKUP_LEAST_EL] ) >>
  imp_res_tac ALOOKUP_SOME_FAPPLY_alist_to_fmap >>
  fs[] >> pop_assum kall_tac >>
  imp_res_tac ALOOKUP_MEM >>
  unabbrev_all_tac >>
  fsrw_tac[SATISFY_ss][MEM_MAP,pairTheory.EXISTS_PROD] ) >>
Cases_on `find_index n ns 0` >> fs[] >>
Cases_on `LENGTH ns = LENGTH defs` >> fs[] >>
rw[pairTheory.UNCURRY,mk_env_def] >- (
  rw[EXTENSION] >> metis_tac[] )
>- (
  rw[EVERY_MAP] >>
  rw[EVERY_MEM,pairTheory.FORALL_PROD,FLOOKUP_DEF,force_dom_DRESTRICT_FUNION,DRESTRICT_DEF,FUNION_DEF] >>
  imp_res_tac find_index_LESS_LENGTH >>
  qpat_assum `LENGTH ns = LENGTH defs` assume_tac >>
  fs[EL_MAP,MEM_MAP,pairTheory.EXISTS_PROD] >>
  rw[] >- (
    qmatch_abbrev_tac `canonical_env_Cv (FAPPLY fm z)` >>
    `fm = MAP_KEYS I (ce_Cv o_f alist_to_fmap env)` by (
      qunabbrev_tac `fm` >>
      match_mp_tac (INST_TYPE[alpha|->``:num``,gamma|->``:Cv``]alist_to_fmap_MAP_matchable) >>
      qexists_tac `I` >> rw[INJ_I] >>
      qexists_tac `ce_Cv` >>
      qexists_tac `env` >>
      rw[] ) >>
    unabbrev_all_tac >> rw[] >>
    qmatch_abbrev_tac `canonical_env_Cv (FAPPLY (f1 o_f f2) z)`  >>
    `z ∈ FDOM f2` by (
      unabbrev_all_tac >>
      rw[MEM_MAP,pairTheory.EXISTS_PROD] >>
      metis_tac[]) >>
    unabbrev_all_tac >>
    rw[o_f_FAPPLY] >>
    qmatch_rename_tac `canonical_env_Cv (ce_Cv (alist_to_fmap env ' z))` [] >>
    imp_res_tac alist_to_fmap_FAPPLY_MEM >>
    metis_tac[] ) >>
  rw[FUN_FMAP_DEF] ) >>
rw[EVERY_MEM,MEM_MAP,pairTheory.EXISTS_PROD] >>
metis_tac[])
val _ = export_rewrites["ce_Cexp_canonical_env"]

val Cevaluate_canonical_envs = store_thm(
"Cevaluate_canonical_envs",
``∀env exp res. Cevaluate env exp res
⇒ ∀v. (res = Rval v) ⇒ canonical_env_Cv v``,
ho_match_mp_tac Cevaluate_nice_ind >>
rw[LET_THM] >>
rw[Cevaluate_list_with_cons] >>
fs[Cevaluate_list_with_value] >>
fsrw_tac[SATISFY_ss,boolSimps.DNF_ss][EVERY_MEM,MEM_EL] >-
  rw[EXTENSION,mk_env_def,MEM_MAP,pairTheory.EXISTS_PROD,FLOOKUP_DEF] >>
rw[mk_env_def,EL_MAP] >>
qmatch_abbrev_tac `canonical_env_Cv x` >>
qsuff_tac `∃v. x = ce_Cv v` >- (rw[] >> rw[]) >>
rw[Abbr`x`] >>
qmatch_abbrev_tac `∃v. SND (EL n ls) = ce_Cv v` >>
qsuff_tac `∀x. MEM x ls ⇒ ∃a v. x = (a, ce_Cv v)` >- (
  srw_tac[boolSimps.DNF_ss][MEM_EL] >>
  fs[Abbr`ls`] >>
  res_tac >> rw[] >> metis_tac[] ) >>
fs[Abbr`ls`,pairTheory.FORALL_PROD] >>
rw[FLOOKUP_DEF,force_dom_DRESTRICT_FUNION,FUNION_DEF,DRESTRICT_DEF,FUN_FMAP_DEF] >- (
  qmatch_abbrev_tac `∃v. alist_to_fmap (MAP f ls) ' x = ce_Cv v` >>
  qsuff_tac `alist_to_fmap (MAP f ls) = MAP_KEYS I (ce_Cv o_f alist_to_fmap ls)` >- (
    rw[Abbr`ls`] >>
    fs[MEM_MAP,pairTheory.EXISTS_PROD] >>
    fs[Abbr`f`,FLOOKUP_DEF] >>
    metis_tac[] ) >>
  Q.ISPECL_THEN [`I:num -> num`,`ce_Cv`] match_mp_tac alist_to_fmap_MAP_matchable >>
  rw[INJ_I] >> metis_tac[] ) >>
qexists_tac `CLit (Bool F)` >> rw[])

val doPrim2_free_vars = store_thm(
"doPrim2_free_vars",
``∀b ty op v1 v2 e. (doPrim2 b ty op v1 v2 = SOME e) ⇒ (free_vars e = {})``,
ntac 3 gen_tac >>
Cases >> rw[] >>
Cases_on `l` >> Cases_on `v2` >> fs[] >>
Cases_on `l` >> fs[] >> pop_assum mp_tac >> rw[] >>
rw[])
val _ = export_rewrites["doPrim2_free_vars"]

val CevalPrim2_free_vars = store_thm(
"CevalPrim2_free_vars",
``∀p2 v1 v2 e. (CevalPrim2 p2 v1 v2 = SOME e) ⇒ (free_vars e = {})``,
Cases >> fs[] >> PROVE_TAC[doPrim2_free_vars])
val _ = export_rewrites["CevalPrim2_free_vars"]

val less2 = prove(``(0:num < 2) ∧ (1:num < 2)``,srw_tac[ARITH_ss][])

val final1 =
  qmatch_assum_abbrev_tac `∀env'.  Cevaluate (env0 ⊌ env') ee rr` >>
  qmatch_abbrev_tac `Cevaluate env1 ee rr` >>
  qsuff_tac `env0 ⊌ env1 = env1` >- PROVE_TAC[] >>
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  rw[Abbr`env0`,Abbr`env1`,SUBMAP_DEF,DRESTRICT_DEF,FUNION_DEF,FUN_FMAP_DEF,pairTheory.UNCURRY] >>
  fsrw_tac[boolSimps.DNF_ss,SATISFY_ss][FUN_FMAP_DEF,pairTheory.UNCURRY] >>
  metis_tac[]
val tac1 =
  match_mp_tac (MP_CANON Cevaluate_list_with_mono) >>
  qmatch_assum_abbrev_tac `Cevaluate_list_with P es res` >>
  qexists_tac `P` >> rw[Abbr`P`] >>
  final1
val tac2 =
  fs[Once Cpmatch_FEMPTY] >>
  Cases_on `Cpmatch FEMPTY p (env ' n)` >> fs[] >>
  rw[] >>
  (disj1_tac ORELSE rw[Once Cpmatch_FEMPTY]) >>
  final1
val tac2a =
  fs[Once Cpmatch_FEMPTY] >>
  Cases_on `Cpmatch FEMPTY p (env ' n)` >> fs[] >>
  rw[] >>
  disj1_tac >>
  imp_res_tac Cpmatch_pat_vars >>
  qmatch_assum_abbrev_tac `∀env'.  Cevaluate (env0 ⊌ env') ee rr` >>
  qmatch_abbrev_tac `Cevaluate env1 ee rr` >>
  qsuff_tac `env0 ⊌ env1 = env1` >- PROVE_TAC[] >>
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  rw[Abbr`env0`,Abbr`env1`,SUBMAP_DEF,DRESTRICT_DEF,FUNION_DEF,FUN_FMAP_DEF,pairTheory.UNCURRY] >>
  fsrw_tac[boolSimps.DNF_ss,SATISFY_ss][FUN_FMAP_DEF,pairTheory.UNCURRY,SUBSET_DEF] >>
  metis_tac[]
val tac3 =
  disj1_tac >>
  qexists_tac `v` >>
  qmatch_assum_abbrev_tac `∀env'. Cevaluate (env0 ⊌ env') exp (Rval v)` >>
  qmatch_abbrev_tac `Cevaluate env1 exp (Rval v) ∧ Cevaluate (env1 |+ (n,v)) exp2 res` >>
  qmatch_assum_abbrev_tac `∀env'. Cevaluate (env2 ⊌ env') exp2 res` >>
  qsuff_tac `(env0 ⊌ env1 = env1) ∧ (env2 ⊌ env1 |+ (n,v) = env1 |+ (n,v))` >- PROVE_TAC[] >>
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  rw[Abbr`env0`,Abbr`env1`,Abbr`env2`,SUBMAP_DEF,DRESTRICT_DEF,FUNION_DEF,
     DRESTRICT_FUPDATE,FAPPLY_FUPDATE_THM,FUN_FMAP_DEF] >>
  srw_tac[boolSimps.DNF_ss,SATISFY_ss][FUN_FMAP_DEF] >>
  metis_tac[]
val tac4 =
  rw[Once Cevaluate_cases] >>
  qmatch_assum_abbrev_tac `∀env'. Cevaluate (env0 ⊌ env') exp res` >>
  qmatch_abbrev_tac `Cevaluate env1 exp res` >>
  qsuff_tac `(env0 ⊌ env1 = env1)` >- PROVE_TAC[] >>
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  qunabbrev_tac `env0` >>
  fs[FOLDL2_FUPDATE_LIST_paired,FOLDL_FUPDATE_LIST] >>
  qunabbrev_tac `env1` >>
  fs[LET_THM] >>
  pop_assum kall_tac >>
  fs[FOLDL2_FUPDATE_LIST_paired,FOLDL_FUPDATE_LIST] >>
  fs[SUBMAP_DEF] >>
  qx_gen_tac `x` >>
  disch_then assume_tac >>
  conj_tac >- (
    fsrw_tac[boolSimps.DNF_ss][DRESTRICT_DEF,FDOM_FUPDATE_LIST,MEM_MAP,MEM_ZIP,
                               MAP2_ZIP,MAP_ZIP,LENGTH_ZIP,pairTheory.EXISTS_PROD] >>
    metis_tac[MEM_EL,pairTheory.pair_CASES] ) >>
  pop_assum mp_tac >>
  fs[DRESTRICT_DEF,FDOM_FUPDATE_LIST] >>
  qmatch_abbrev_tac `((A \/ B) /\ C) \/ C ==> D` >>
  qsuff_tac `C ==> D` >- (
    rpt (pop_assum kall_tac) >> metis_tac[]) >>
  unabbrev_all_tac >>
  strip_tac >>
  fs[MAP2_MAP,MAP_ZIP,LENGTH_ZIP,FST_triple] >>
  Cases_on `MEM x ns` >- (
    rw[FUNION_DEF,DRESTRICT_DEF,FDOM_FUPDATE_LIST,MAP_ZIP,LENGTH_ZIP,MEM_MAP,pairTheory.EXISTS_PROD] >> fs[] >>
    match_mp_tac FUPDATE_LIST_APPLY_MEM >>
    fs[MAP_ZIP,LENGTH_ZIP,MEM_EL] >>
    qpat_assum `n < LENGTH ns` mp_tac >> rw[] >>
    qexists_tac `n` >>
    fs[EL_MAP,LENGTH_ZIP,EL_ZIP] >>
    conj_asm2_tac >- (
      match_mp_tac FUPDATE_LIST_APPLY_MEM >>
      fs[LENGTH_ZIP,MAP_ZIP] >>
      qexists_tac `n` >>
      fs[EL_MAP,LENGTH_ZIP,EL_ZIP] >>
      rw[pairTheory.UNCURRY] >>
      rw[mk_env_canon] >>
      rw[ALOOKUP_MAP,ALOOKUP_APPEND] >>
      qmatch_abbrev_tac `lhs = case OPTION_MAP ce_Cv (FLOOKUP fm x) of NONE => X | SOME v => SOME v` >>
      `x ∈ FDOM fm` by (
        fsrw_tac[boolSimps.DNF_ss][Abbr`fm`,DRESTRICT_DEF,pairTheory.EXISTS_PROD] >>
        metis_tac[pairTheory.pair_CASES,MEM_EL,pairTheory.FST,pairTheory.SND] ) >>
      rw[FLOOKUP_DEF] >>
      unabbrev_all_tac >>
      qmatch_abbrev_tac `lhs = SOME (ce_Cv ((DRESTRICT env s ⊌ f0 ⊌ f1) ' x))` >>
      qsuff_tac `x ∈ s` >- (
        strip_tac >>
        Cases_on `x ∈ FDOM env` >>
        rw[FUNION_DEF,DRESTRICT_DEF,Abbr`s`,Abbr`lhs`,FLOOKUP_DEF] >>
        unabbrev_all_tac >>
        srw_tac[SATISFY_ss][FUN_FMAP_DEF]) >>
      unabbrev_all_tac >>
      srw_tac[SATISFY_ss][FUN_FMAP_DEF] >>
      disj2_tac >>
      rw[pairTheory.UNCURRY] >>
      metis_tac[MEM_EL,IN_DIFF,IN_LIST_TO_SET,IN_UNION] ) >>
    fs[EL_ALL_DISTINCT_EL_EQ] ) >>
  rw[FUNION_DEF,DRESTRICT_DEF,FDOM_FUPDATE_LIST,MAP_ZIP,LENGTH_ZIP,MEM_MAP,pairTheory.EXISTS_PROD] >> fs[] >- (
    match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
    TRY (conj_tac >- rw[MAP_ZIP,LENGTH_ZIP]) >>
    rw[MAP_ZIP,LENGTH_ZIP,MEM_MAP,pairTheory.EXISTS_PROD] >>
    match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
    TRY (conj_tac >- rw[MAP_ZIP,LENGTH_ZIP]) >>
    rw[MAP_ZIP,LENGTH_ZIP,MEM_MAP,pairTheory.EXISTS_PROD] >>
    qmatch_abbrev_tac `env ' x = (DRESTRICT env s ⊌ f0 ⊌ f2) ' x` >>
    qsuff_tac `x ∈ s` >- rw[DRESTRICT_DEF,FUNION_DEF] >>
    rw[Abbr`s`] ) >>
  match_mp_tac EQ_SYM >>
  match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
  TRY (conj_tac >- rw[MAP_ZIP,LENGTH_ZIP]) >>
  rw[MAP_ZIP,LENGTH_ZIP,MEM_MAP,pairTheory.EXISTS_PROD] >>
  rw[FUN_FMAP_DEF] >>
  rw[DRESTRICT_DEF,FUNION_DEF,FUN_FMAP_DEF]
val tac5 =
  rw[Once Cevaluate_cases] >>
  ((disj2_tac >> disj1_tac >>
    qmatch_assum_abbrev_tac `∀env''. Cevaluate (env0 ⊌ env'') exp (Rval (CClosure env' ns exp'))` >>
    map_every qexists_tac [`env'`,`ns`,`exp'`])
   ORELSE
   (disj2_tac >> disj2_tac >> disj2_tac >> disj1_tac >>
    qmatch_assum_abbrev_tac `∀env''. Cevaluate (env0 ⊌ env'') exp (Rval (CRecClos env' ns' defs n))` >>
    map_every qexists_tac [`env'`,`ns'`,`defs`,`n`])
  ) >>
  rw[Cevaluate_list_with_Cevaluate] >>
  fs[Cevaluate_list_with_error] >- (
    qmatch_abbrev_tac `Cevaluate env1 exp v` >>
    qsuff_tac `env0 ⊌ env1 = env1` >- metis_tac [] >>
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    rw[SUBMAP_DEF,Abbr`env0`,Abbr`env1`,DRESTRICT_DEF,FUNION_DEF,FUN_FMAP_DEF] >>
    srw_tac[boolSimps.DNF_ss,SATISFY_ss][FUN_FMAP_DEF] >>
    metis_tac[] ) >>
  qmatch_assum_rename_tac `nn < LENGTH es`[] >>
  qexists_tac `nn` >>
  rw[] >- (
    qmatch_assum_abbrev_tac `∀env'. Cevaluate (env1 ⊌ env') (EL nn es) (Rerr err)` >>
    qmatch_abbrev_tac `Cevaluate env2 (EL nn es) (Rerr err)` >>
    qsuff_tac `env1 ⊌ env2 = env2` >- metis_tac[] >>
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    rw[SUBMAP_DEF,Abbr`env1`,Abbr`env2`,DRESTRICT_DEF,FUNION_DEF,FUN_FMAP_DEF] >>
    srw_tac[boolSimps.DNF_ss,SATISFY_ss][FUN_FMAP_DEF] >>
    srw_tac[boolSimps.DNF_ss,SATISFY_ss][FUN_FMAP_DEF] >>
    metis_tac[MEM_EL] ) >>
  first_x_assum (qspec_then `m` mp_tac) >> rw[] >>
  qexists_tac `v` >>
  qmatch_assum_abbrev_tac `∀env'. Cevaluate (env1 ⊌ env') (EL m es) (Rval v)` >>
  qmatch_abbrev_tac `Cevaluate env2 (EL m es) (Rval v)` >>
  qsuff_tac `env1 ⊌ env2 = env2` >- metis_tac[] >>
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  `m < LENGTH es` by srw_tac[ARITH_ss][] >>
  rw[SUBMAP_DEF,Abbr`env1`,Abbr`env2`,DRESTRICT_DEF,FUNION_DEF,FUN_FMAP_DEF] >>
  srw_tac[boolSimps.DNF_ss,SATISFY_ss][FUN_FMAP_DEF] >>
  srw_tac[boolSimps.DNF_ss,SATISFY_ss][FUN_FMAP_DEF] >>
  metis_tac[MEM_EL]
val tac6 =
  rw[Once Cevaluate_cases] >>
  disj1_tac >>
  qmatch_assum_abbrev_tac `∀env'. Cevaluate (env0 ⊌ env') exp (Rval (CLit (Bool b)))` >>
  qexists_tac `b` >>
  qunabbrev_tac `b` >>
  conj_tac >- (
    qmatch_abbrev_tac `Cevaluate env1 ex re` >>
    qunabbrev_tac `env0` >>
    qmatch_assum_abbrev_tac `∀env'. Cevaluate (env0 ⊌ env') ex re` >>
    qsuff_tac `env0 ⊌ env1 = env1` >- metis_tac[] >>
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    rw[Abbr`env0`,Abbr`env1`,SUBMAP_DEF,FUNION_DEF,DRESTRICT_DEF,FUN_FMAP_DEF] >>
    asm_simp_tac(srw_ss()++boolSimps.DNF_ss++SATISFY_ss)[FUN_FMAP_DEF,MEM_EL,pairTheory.UNCURRY] >>
    metis_tac[]) >>
  fs[] >>
  qunabbrev_tac `env0` >>
  final1

val Cevaluate_any_env = store_thm(
"Cevaluate_any_env",
``∀env exp res. Cevaluate env exp res ⇒ ∀env'. Cevaluate ((force_dom env (free_vars exp) (CLit(Bool F))) ⊌ env') exp res``,
fs[force_dom_DRESTRICT_FUNION] >>
ho_match_mp_tac Cevaluate_nice_ind >>
rw[FOLDL_UNION_BIGUNION,FOLDL_UNION_BIGUNION_paired,
   FAPPLY_FUPDATE_THM,DRESTRICT_DEF,FUNION_DEF,
   Cevaluate_con,Cevaluate_list_with_Cevaluate,
   Cevaluate_tageq,Cevaluate_proj,Cevaluate_mat_cons,Cevaluate_let_cons]
>- tac1
>- tac1
>- PROVE_TAC[]
>- PROVE_TAC[]
>- tac2a
>- tac2
>- tac3
>- tac3
>- tac3
>- (disj2_tac >> final1)
>- tac4
>- tac4
>- (
  unabbrev_all_tac >>
  rw[mk_env_canon] >>
  rw[ALOOKUP_APPEND,ALOOKUP_MAP] >>
  rw[FLOOKUP_DEF,DRESTRICT_DEF,FUNION_DEF,FUN_FMAP_DEF])
>- (
  rw[Once Cevaluate_cases] >>
  disj1_tac >>
  qmatch_assum_abbrev_tac `∀env''. Cevaluate (env0 ⊌ env'') exp (Rval (CClosure env' ns exp'))` >>
  map_every qexists_tac [`env'`,`ns`,`exp'`,`vs`] >>
  rw[Cevaluate_list_with_Cevaluate] >>
  fs[Cevaluate_list_with_value] >>
  TRY (
    qx_gen_tac `n` >> rw[] >>
    first_x_assum (qspec_then `n` mp_tac) >> rw[] ) >>
  unabbrev_all_tac >>
  qmatch_abbrev_tac `Cevaluate env1 exp1 res1` >>
  qmatch_assum_abbrev_tac `∀env''. Cevaluate (env0 ⊌ env'') exp1 res1` >>
  (( qunabbrev_tac `exp1` >>
    qmatch_abbrev_tac `Cevaluate env1 exp' res1` >>
    qsuff_tac `env0 ⊌ env1 = env1` >- metis_tac[] >>
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    fs[SUBMAP_DEF] >>
    qx_gen_tac `x` >>
    qunabbrev_tac `env0` >>
    fs[DRESTRICT_DEF] >>
    qmatch_abbrev_tac `A /\ B \/ B ==> C` >>
    qsuff_tac `B ==> C` >- metis_tac[] >>
    unabbrev_all_tac >>
    fs[FOLDL2_FUPDATE_LIST,MAP2_MAP,MAP_ZIP,FST_pair,SND_pair,FDOM_FUPDATE_LIST] >>
    strip_tac >>
    `canonical_env_Cv (CClosure env' ns exp')` by (
      metis_tac [Cevaluate_canonical_envs] ) >>
    fs[EXTENSION] >>
    rw[FUNION_DEF,DRESTRICT_DEF,FUN_FMAP_DEF,FDOM_FUPDATE_LIST,MAP_ZIP]
   ) ORELSE (
    qsuff_tac `env0 ⊌ env1 = env1` >- metis_tac[] >>
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    rw[SUBMAP_DEF,Abbr`env0`,Abbr`env1`,DRESTRICT_DEF,FUN_FMAP_DEF,FUNION_DEF] >>
    srw_tac[boolSimps.DNF_ss,SATISFY_ss][FUN_FMAP_DEF,FOLDL2_FUPDATE_LIST] >>
    srw_tac[boolSimps.DNF_ss,SATISFY_ss][FUN_FMAP_DEF] >>
    metis_tac[MEM_EL]
   )))
>- tac5
>- (
  rw[Once Cevaluate_cases] >>
  disj2_tac >> disj2_tac >> disj1_tac >>
  qmatch_assum_abbrev_tac `∀env''. Cevaluate (env0 ⊌ env'') exp (Rval (CRecClos env' ns' defs n))` >>
  map_every qexists_tac [`env'`,`ns'`,`defs`,`n`] >>
  qmatch_assum_rename_tac `EL i defs = (ns,exp')`[] >>
  map_every qexists_tac [`i`,`ns`,`exp'`] >>
  fs[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_value] >>
  qexists_tac `vs` >>
  rw[] >- (
    qmatch_assum_abbrev_tac `∀env''. Cevaluate (env0 ⊌ env'') exp (Rval v)` >>
    qmatch_abbrev_tac `Cevaluate env1 exp (Rval v)` >>
    qsuff_tac `env0 ⊌ env1 = env1` >- metis_tac[] >>
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    rw[Abbr`env0`,Abbr`env1`,SUBMAP_DEF,DRESTRICT_DEF,FUNION_DEF,FUN_FMAP_DEF] >>
    srw_tac[SATISFY_ss][FUN_FMAP_DEF] >>
    metis_tac[] )
  >- (
    qmatch_abbrev_tac `Cevaluate env1 (EL m es) (Rval (EL m vs))` >>
    first_x_assum (qspec_then `m` mp_tac) >> rw[] >>
    qunabbrev_tac `env0` >>
    qmatch_assum_abbrev_tac `∀env''. Cevaluate (env0 ⊌ env'') (EL m es) (Rval (EL m vs))` >>
    qsuff_tac `env0 ⊌ env1 = env1` >- metis_tac[] >>
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    rw[Abbr`env0`,Abbr`env1`,SUBMAP_DEF,DRESTRICT_DEF,FUNION_DEF,FUN_FMAP_DEF] >>
    fsrw_tac[boolSimps.DNF_ss,SATISFY_ss][FUN_FMAP_DEF,MEM_EL] >>
    metis_tac[MEM_EL] ) >>
  qmatch_abbrev_tac `Cevaluate env1 exp' res` >>
  qunabbrev_tac `env0` >>
  qmatch_assum_abbrev_tac `∀env''. Cevaluate (env0 ⊌ env'') exp' res` >>
  qsuff_tac `env0 ⊌ env1 = env1` >- metis_tac[] >>
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  rw[Abbr`env0`,Abbr`env1`] >>
  pop_assum kall_tac >>
  rw[FOLDL2_FUPDATE_LIST,LET_THM,MAP2_MAP,FST_pair,SND_pair,MAP_ZIP,LENGTH_ZIP,FOLDL_FUPDATE_LIST] >>
  fs[SUBMAP_DEF] >>
  qx_gen_tac `x` >>
  fs[DRESTRICT_DEF,FUNION_DEF,FUNION_DEF,FDOM_FUPDATE_LIST,MEM_MAP,pairTheory.EXISTS_PROD,MEM_ZIP,MEM_EL] >>
  qmatch_abbrev_tac `A ∨ C ⇒ D` >>
  qsuff_tac `C ⇒ D` >- metis_tac[] >>
  unabbrev_all_tac >> strip_tac >>
  conj_asm1_tac >- (
    `canonical_env_Cv (CRecClos env' ns' defs n)` by metis_tac [Cevaluate_canonical_envs] >>
    pop_assum mp_tac >>
    fs[EVERY_MEM,MEM_MAP,pairTheory.EXISTS_PROD,EXTENSION,MEM_EL] >>
    metis_tac[] ) >>
  rw[] )
>- tac5
>- (
  rw[Once Cevaluate_cases] >>
  rpt disj2_tac >>
  qmatch_assum_abbrev_tac `∀env'. Cevaluate (env0 ⊌ env') exp (Rerr err)` >>
  qmatch_abbrev_tac `Cevaluate env1 exp (Rerr err)` >>
  qsuff_tac `env0 ⊌ env1 = env1` >- metis_tac[] >>
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  rw[Abbr`env0`,Abbr`env1`,SUBMAP_DEF,FUNION_DEF,DRESTRICT_DEF,FUN_FMAP_DEF] >>
  fsrw_tac[boolSimps.DNF_ss,SATISFY_ss][FUN_FMAP_DEF,MEM_EL] >>
  metis_tac[])
>- (
  rw[Once Cevaluate_cases] >>
  fs[Cevaluate_list_with_Cevaluate] >>
  fs[Cevaluate_list_with_value] >>
  disj1_tac >>
  qmatch_assum_abbrev_tac `∀env'. Cevaluate (env0 ⊌ env') exp res` >>
  map_every qexists_tac [`v1`,`v2`,`exp`] >>
  conj_tac >- (
    qx_gen_tac `n` >> strip_tac >>
    first_x_assum (qspec_then `n` mp_tac) >>
    rw[] >>
    qmatch_abbrev_tac `Cevaluate env1 ex re` >>
    qunabbrev_tac `env0` >>
    qmatch_assum_abbrev_tac `∀env'. Cevaluate (env0 ⊌ env') ex re` >>
    qsuff_tac `env0 ⊌ env1 = env1` >- metis_tac[] >>
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    `(n = 0) ∨ (n = 1)` by DECIDE_TAC >>
    rw[Abbr`env0`,Abbr`env1`,SUBMAP_DEF,FUNION_DEF,DRESTRICT_DEF,FUN_FMAP_DEF] >>
    fsrw_tac[boolSimps.DNF_ss,SATISFY_ss][FUN_FMAP_DEF,MEM_EL,MEM] >>
    full_simp_tac pure_ss [GSYM (CONJUNCT1 EL)] >>
    metis_tac[less2]) >>
  fs[] >>
  qmatch_abbrev_tac `Cevaluate env1 exp res` >>
  qsuff_tac `env0 ⊌ env1 = env1` >- metis_tac[] >>
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  rw[Abbr`env0`,Abbr`env1`,SUBMAP_DEF,FUNION_DEF,DRESTRICT_DEF,FUN_FMAP_DEF] >>
  imp_res_tac CevalPrim2_free_vars >>
  fs[] )
>- (
  rw[Once Cevaluate_cases] >>
  rpt disj2_tac >>
  fs[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_error] >>
  qexists_tac `n` >>
  rw[] >- (
    qmatch_assum_abbrev_tac `∀env'. Cevaluate (env0 ⊌ env') exp (Rerr err)` >>
    qmatch_abbrev_tac `Cevaluate env1 exp (Rerr err)` >>
    qsuff_tac `env0 ⊌ env1 = env1` >- metis_tac[] >>
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    `(n = 0) ∨ (n = 1)` by DECIDE_TAC >>
    rw[Abbr`env0`,Abbr`env1`,Abbr`exp`,SUBMAP_DEF,FUNION_DEF,DRESTRICT_DEF,FUN_FMAP_DEF] >>
    fsrw_tac[boolSimps.DNF_ss,SATISFY_ss][FUN_FMAP_DEF,MEM_EL] >>
    metis_tac[]) >>
  first_x_assum (qspec_then `m` mp_tac) >> rw[] >>
  qexists_tac `v` >>
  qmatch_assum_abbrev_tac `∀env'. Cevaluate (env0 ⊌ env') exp (Rval v)` >>
  qmatch_abbrev_tac `Cevaluate env1 exp (Rval v)` >>
  qsuff_tac `env0 ⊌ env1 = env1` >- metis_tac[] >>
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  `(m = 0) ∨ (m = 1)` by DECIDE_TAC >>
  rw[Abbr`env0`,Abbr`env1`,Abbr`exp`,SUBMAP_DEF,FUNION_DEF,DRESTRICT_DEF,FUN_FMAP_DEF] >>
  fsrw_tac[boolSimps.DNF_ss,SATISFY_ss][FUN_FMAP_DEF,MEM_EL] >>
  metis_tac[])
>- (
  rw[Once Cevaluate_cases] >>
  fs[Cevaluate_list_with_Cevaluate] >>
  fs[Cevaluate_list_with_value] >>
  disj1_tac >>
  qmatch_assum_abbrev_tac `∀env'. Cevaluate (env0 ⊌ env') exp res` >>
  map_every qexists_tac [`v1`,`v2`,`exp`] >>
  conj_tac >- (
    qx_gen_tac `n` >> strip_tac >>
    first_x_assum (qspec_then `n` mp_tac) >>
    rw[] >>
    qmatch_abbrev_tac `Cevaluate env1 ex re` >>
    qunabbrev_tac `env0` >>
    qmatch_assum_abbrev_tac `∀env'. Cevaluate (env0 ⊌ env') ex re` >>
    qsuff_tac `env0 ⊌ env1 = env1` >- metis_tac[] >>
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    `(n = 0) ∨ (n = 1)` by DECIDE_TAC >>
    rw[Abbr`env0`,Abbr`env1`,SUBMAP_DEF,FUNION_DEF,DRESTRICT_DEF,FUN_FMAP_DEF] >>
    `x ∈ BIGUNION (IMAGE free_vars (set es))` by (
      rw[] >> qexists_tac `free_vars ex` >> rw[] >>
      qexists_tac `ex` >>
      rw[Abbr`ex`] >>
      Cases_on `es` >> fs[] >>
      Cases_on `t` >> fs[]) >>
    `FINITE (BIGUNION (IMAGE free_vars (set es)))` by (
      rw[] >> rw[] ) >>
    asm_simp_tac(srw_ss()++boolSimps.DNF_ss++SATISFY_ss)[FUN_FMAP_DEF,MEM_EL,pairTheory.UNCURRY] >>
    metis_tac[less2]) >>
  fs[] >>
  qmatch_abbrev_tac `Cevaluate env1 exp res` >>
  qsuff_tac `env0 ⊌ env1 = env1` >- metis_tac[] >>
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  rw[Abbr`env0`,Abbr`env1`,SUBMAP_DEF,FUNION_DEF,DRESTRICT_DEF,FUN_FMAP_DEF] >>
  imp_res_tac doPrim2_free_vars >>
  fs[] )
>- (
  rw[Once Cevaluate_cases] >>
  rpt disj2_tac >>
  fs[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_error] >>
  qexists_tac `n` >>
  rw[] >- (
    qmatch_assum_abbrev_tac `∀env'. Cevaluate (env0 ⊌ env') exp (Rerr err)` >>
    qmatch_abbrev_tac `Cevaluate env1 exp (Rerr err)` >>
    qsuff_tac `env0 ⊌ env1 = env1` >- metis_tac[] >>
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    rw[Abbr`env0`,Abbr`env1`,Abbr`exp`,SUBMAP_DEF,FUNION_DEF,DRESTRICT_DEF,FUN_FMAP_DEF] >>
    fsrw_tac[boolSimps.DNF_ss,SATISFY_ss][FUN_FMAP_DEF,MEM_EL] >>
    metis_tac[]) >>
  first_x_assum (qspec_then `m` mp_tac) >> rw[] >>
  `m < LENGTH es` by srw_tac[ARITH_ss][] >>
  qexists_tac `v` >>
  qmatch_assum_abbrev_tac `∀env'. Cevaluate (env0 ⊌ env') exp (Rval v)` >>
  qmatch_abbrev_tac `Cevaluate env1 exp (Rval v)` >>
  qsuff_tac `env0 ⊌ env1 = env1` >- metis_tac[] >>
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  rw[Abbr`env0`,Abbr`env1`,Abbr`exp`,SUBMAP_DEF,FUNION_DEF,DRESTRICT_DEF,FUN_FMAP_DEF] >>
  fsrw_tac[boolSimps.DNF_ss,SATISFY_ss][FUN_FMAP_DEF,MEM_EL] >>
  metis_tac[])
>- tac6
>- tac6
>- (
  rw[Once Cevaluate_cases] >>
  disj2_tac >>
  final1 )
>- (
  rw[Once Cevaluate_cases] >>
  disj1_tac >>
  final1 )
>- (
  rw[Once Cevaluate_cases] >>
  disj2_tac >>
  disj1_tac >>
  conj_tac >- (
    pop_assum kall_tac >>
    final1 ) >>
  final1 )
>- (
  rw[Once Cevaluate_cases] >>
  disj2_tac >>
  final1 )
>- (
  rw[Once Cevaluate_cases] >>
  disj1_tac >>
  final1 )
>- (
  rw[Once Cevaluate_cases] >>
  disj2_tac >> disj1_tac >>
  conj_tac >- (
    pop_assum kall_tac >>
    final1 ) >>
  final1 )
>- (
  rw[Once Cevaluate_cases] >>
  disj2_tac >>
  final1 )
>- rw[Cevaluate_list_with_cons]
>- rw[Cevaluate_list_with_cons]
>- (
  rw[Cevaluate_list_with_cons] >>
  disj1_tac >>
  qexists_tac `v` >>
  rw[] ))

val Cevaluate_free_vars_env = save_thm(
"Cevaluate_free_vars_env",
Cevaluate_any_env
|> SPEC_ALL
|> UNDISCH_ALL
|> Q.SPEC `FEMPTY`
|> SIMP_RULE (srw_ss()) [FUNION_FEMPTY_2]
|> DISCH_ALL
|> Q.GEN `res` |> Q.GEN `exp` |> Q.GEN `env`)

val mk_env_canonical_id = store_thm(
"mk_env_canonical_id",
``(mk_env env exp ns = env) =
  SORTED a_linear_order env ∧
  (set (MAP FST env) = free_vars exp DIFF ns) ∧
  ALL_DISTINCT (MAP FST env)``,
EQ_TAC >- (
  rw[] >>
  pop_assum (SUBST1_TAC o SYM) >>
  rw[mk_env_def] >>
  metis_tac[ALL_DISTINCT_fmap_to_alist_keys]) >>
rw[mk_env_def] >>
qmatch_abbrev_tac `sort_Cenv (fmap_to_alist (force_dom fm s d)) = env` >>
`force_dom fm s d = fm` by (
  rw[force_dom_id,Abbr`fm`] ) >>
rw[Abbr`fm`] >>
match_mp_tac (MP_CANON SORTED_PERM_EQ) >>
qexists_tac `a_linear_order` >>
rw[num_Cv_linear_order_linear] >>
metis_tac[PERM_MAP_sort_Cenv,MAP_ID,PERM_TRANS,alist_to_fmap_to_alist_PERM])

val ce_Cexp_canonical_id = store_thm(
"ce_Cexp_canonical_id",
``(∀exp. canonical_env_Cexp exp ⇒ (ce_Cexp exp = exp)) ∧
(∀v. canonical_env_Cv v ⇒ (ce_Cv v = v))``,
ho_match_mp_tac canonical_env_ind >>
srw_tac[SATISFY_ss][EVERY_MEM,MAP_EQ_ID,pairTheory.FORALL_PROD,MEM_MAP,pairTheory.EXISTS_PROD] >- (
  `env' = env` by (
    unabbrev_all_tac >>
    srw_tac[SATISFY_ss][MAP_EQ_ID,pairTheory.FORALL_PROD] ) >>
  rw[mk_env_canonical_id] ) >>
Cases_on `find_index n ns 0` >> fs[LET_THM] >>
fs[pairTheory.UNCURRY] >>
conj_asm2_tac >- (
  qmatch_abbrev_tac `mk_env (MAP f env) X Y = Z` >>
  `MAP f env = env` by (
    srw_tac[SATISFY_ss][MAP_EQ_ID,Abbr`f`,pairTheory.FORALL_PROD] ) >>
  unabbrev_all_tac >>
  rw[mk_env_canonical_id,DIFF_UNION,DIFF_COMM] ) >>
srw_tac[SATISFY_ss][MAP_EQ_ID,pairTheory.FORALL_PROD])

val FOLDR_CONS_triple = store_thm(
"FOLDR_CONS_triple",
``!f ls a. FOLDR (\(x,y,z) w. f x y z :: w) a ls = (MAP (\(x,y,z). f x y z) ls)++a``,
GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
Q.X_GEN_TAC `p` THEN
PairCases_on `p` THEN
SRW_TAC[][])

val tac =
  unabbrev_all_tac >>
  rw[force_dom_DRESTRICT_FUNION,FUNION_DEF,DRESTRICT_DEF,MEM_MAP,pairTheory.EXISTS_PROD,FUN_FMAP_DEF,MAP_MAP_o] >>
  qmatch_abbrev_tac `canonical_env_Cv ((alist_to_fmap (MAP f env)) ' k)` >>
  `∃f1 f2. f = (λ(n,v). (f1 n, f2 v))` by (
    rw[FUN_EQ_THM,pairTheory.UNCURRY,Abbr`f`,pairTheory.FORALL_PROD] >>
    rw[GSYM SKOLEM_THM,Once SWAP_EXISTS_THM] >>
    rw[FORALL_AND_THM] >>
    rw[GSYM SKOLEM_THM] ) >>
  `INJ f1 (set (MAP FST env)) UNIV` by (
    unabbrev_all_tac >>
    fs[INJ_DEF] >>
    fs[FUN_EQ_THM,pairTheory.FORALL_PROD,FORALL_AND_THM] >>
    rpt strip_tac >> fs[] >>
    first_x_assum (match_mp_tac o MP_CANON) >> fs[] >>
    fs[SUBSET_DEF,pairTheory.EXISTS_PROD,MEM_MAP] >>
    metis_tac[] ) >>
  fs[] >>
  rw[alist_to_fmap_MAP] >>
  qmatch_abbrev_tac `canonical_env_Cv (MAP_KEYS f1 fm ' k)` >>
  `∃a. (a ∈ FDOM fm) ∧ (k = f1 a)` by (
    fs[FUN_EQ_THM,markerTheory.Abbrev_def,pairTheory.FORALL_PROD,MEM_MAP,pairTheory.EXISTS_PROD] >>
    metis_tac[] ) >>
  rw[] >>
  `INJ f1 (FDOM fm) UNIV` by (
    fs[FUN_EQ_THM,markerTheory.Abbrev_def,pairTheory.FORALL_PROD] ) >>
  rw[MAP_KEYS_def,Abbr`fm`] >>
  fs[o_f_DEF,markerTheory.Abbrev_def,FUN_EQ_THM,pairTheory.FORALL_PROD]

val v_to_Cv_canonical = store_thm(
"v_to_Cv_canonical",
``∀cm Ps Pv s v. (s = FST (Ps,Pv)) ∧ (v = SND (Ps,Pv)) ∧
    (INJ (FAPPLY s.m) (FDOM s.m) UNIV) ∧
    (clV_v v ⊆ FDOM s.m)
⇒ canonical_env_Cv (v_to_Cv cm (Ps,Pv))``,
ho_match_mp_tac v_to_Cv_ind >>
rw[v_to_Cv_def,EVERY_MEM,MEM_MAP] >- (
  fs[SUBSET_DEF] >>
  metis_tac[] ) >>
fs[] >>
unabbrev_all_tac >>
rw[mk_env_def,EVERY_MAP,EVERY_MEM,pairTheory.FORALL_PROD,FLOOKUP_DEF] >- tac  >>
BasicProvers.EVERY_CASE_TAC >> TRY (fs[LET_THM,pairTheory.UNCURRY] >> NO_TAC) >>
imp_res_tac find_index_LESS_LENGTH >>
rw[] >>
fs[MEM_MAP,EVERY_MAP,EL_MAP,DIFF_UNION,DIFF_COMM] >>
fs[FOLDR_CONS_triple,LET_THM,pairTheory.UNCURRY,MAP_MAP_o] >>
qunabbrev_tac `defs'` >> fs[EVERY_MAP,pairTheory.UNCURRY] >>
rw[EVERY_MEM,pairTheory.FORALL_PROD,FLOOKUP_DEF] >>
tac)

(* Prove compiler phases preserve semantics *)

(*
val exp_to_Cexp_thm1 = store_thm(
"exp_to_Cexp_thm1",
``∀tp cm Ps Pexp s exp s' Cexp cenv env res.
  ((Ps,Pexp) = (s,exp)) ∧
  good_env_state env s ∧
  (exp_to_Cexp tp cm (s,exp) = (s',Cexp)) ∧
  (tp = F) ∧
  evaluate cenv env exp res ∧
  (res ≠ Rerr Rtype_error) ∧
  good_cmap cenv cm ⇒
  Cevaluate (alist_to_fmap (MAP (λ(x,v). (s.m ' x, v_to_Cv cm (s,v))) env)) Cexp (map_result (λv. v_to_Cv cm (s,v)) res)``,
ho_match_mp_tac exp_to_Cexp_ind >>
strip_tac >-
  fs[exp_to_Cexp_def] >>
strip_tac >-
  fs[exp_to_Cexp_def,v_to_Cv_def] >>
strip_tac >- (
  fs[exp_to_Cexp_def] >>
  rw[Cevaluate_con,evaluate_con] >>
  fs[Cevaluate_list_with_Cevaluate,evaluate_list_with_evaluate] >>
  qpat_assum `do_con_check cenv cn (LENGTH es)` kall_tac >>
  rw[] >>
  TRY (qpat_assum `X Y Z (Rval vs)` mp_tac >> qid_spec_tac `vs`) >>
  Induct_on `es` >- (
    rw[Once evaluate_cases, Once Cevaluate_cases] ) >>
  fs[v_to_Cv_def] >- (
    rw[] >>
    fs[evaluate_list_with_cons] >- (
      rw[Cevaluate_list_with_cons] >>
      disj1_tac >>
      qmatch_assum_abbrev_tac `P ⇒ Q ⇒ R` >>
      `R` by metis_tac[] >>
      qpat_assum `Q` kall_tac >>
      qpat_assum `P ⇒ Q ⇒ R` kall_tac >>
      unabbrev_all_tac >>
      first_x_assum (qspec_then `h` mp_tac) >> rw[] >>
      first_x_assum (qspecl_then [`cenv`,`env`,`Rval v`] mp_tac) >> rw[] >>
      metis_tac[] ) >>
    rw[Cevaluate_list_with_cons] >>
    disj2_tac >>
    first_x_assum (qspec_then `h` mp_tac) >> rw[] >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rerr err`] mp_tac) >> rw[] ) >>
  rw[] >>
  fs[evaluate_list_with_cons] >>
  rw[Cevaluate_list_with_cons] >- (
    first_x_assum (qspec_then `h` mp_tac) >> rw[] >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rval v`] mp_tac) >> rw[] ) >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  rw[] >>
  metis_tac[] ) >>
strip_tac >- (
  fs[exp_to_Cexp_def,evaluate_var,MEM_MAP] >>
  rw[] >> srw_tac[boolSimps.DNF_ss][pairTheory.EXISTS_PROD] >>
  imp_res_tac alistTheory.ALOOKUP_MEM >- PROVE_TAC[] >>
  fs[good_env_state_def] >>
  qho_match_abbrev_tac `x = ce_Cv (alist_to_fmap (MAP (λ(x,y). (f1 x, f2 y)) al) ' z)` >>
  `f1 = FAPPLY s.m` by rw[Abbr`f1`,FUN_EQ_THM] >>
  `INJ f1 (set (MAP FST al)) UNIV` by (
    metis_tac[INJ_SUBSET,SUBSET_UNIV,LIST_TO_SET_MAP] ) >>
  rw[alistTheory.alist_to_fmap_MAP] >>
  `vn IN FDOM (f2 o_f alist_to_fmap al)` by (
    rw[MEM_MAP] >>
    qexists_tac `(vn,v)` >> rw[] ) >>
  rw[finite_mapTheory.MAP_KEYS_def,Abbr`z`] >>
  unabbrev_all_tac >>
  rw[finite_mapTheory.o_f_DEF] >>
  imp_res_tac alistTheory.ALOOKUP_SOME_FAPPLY_alist_to_fmap >>
  rw[] >>
  match_mp_tac EQ_SYM >>
  match_mp_tac (CONJUNCT2 ce_Cexp_canonical_id) >>
  match_mp_tac v_to_Cv_canonical >>
  fsrw_tac[boolSimps.ETA_ss][] >>
  fsrw_tac[boolSimps.DNF_ss][SUBSET_DEF,pairTheory.EXISTS_PROD] >>
  metis_tac[] ) >>
strip_tac >- (
  fs[exp_to_Cexp_def] >>
  rw[v_to_Cv_def] >>
  fs[LET_THM] >>
  rw[Once Cevaluate_cases] >>
  rw[mk_env_canon,Abbr`env'`,Abbr`env''`,ALOOKUP_APPEND,ALOOKUP_MAP]) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  Cases_on `exp_to_Cexp F cm (s,e1)` >> fs[] >>
  Cases_on `exp_to_Cexp F cm (s,e2)` >> fs[] >>
  fs[LET_THM] >> rw[] >>
  rw[Once Cevaluate_cases] >>
  fs[evaluate_app] >- (
    disj1_tac >>
    rw[Cevaluate_list_with_Cevaluate] >>
    rw[Cevaluate_list_with_cons] >>
    qexists_tac `v_to_Cv cm (s,v1)` >>
    qexists_tac `v_to_Cv cm (s,v2)` >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rval v1`] mp_tac) >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rval v2`] mp_tac) >>
    rw[] >>
    Cases_on `opn` >>
    Cases_on `v1` >> Cases_on `l` >> fs[do_app_def] >>
    Cases_on `v2` >> Cases_on `l` >> fs[] >> rw[] >>
    fs[CevalPrim2_def,doPrim2_def,v_to_Cv_def,opn_lookup_def,i0_def] >>
    rw[] >> fs[] >> rw[] >>
    qpat_assum `evaluate cenv env (Val X) Y` mp_tac >>
    rw[Once evaluate_cases,v_to_Cv_def] )
  >- (
    disj2_tac >>
    rw[Cevaluate_list_with_Cevaluate] >>
    rw[Cevaluate_list_with_cons] >>
    disj1_tac >>
    qexists_tac `v_to_Cv cm (s,v1)` >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rval v1`] mp_tac) >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rerr err`] mp_tac) >>
    rw[] )
  >- (
    disj2_tac >>
    rw[Cevaluate_list_with_Cevaluate] >>
    rw[Cevaluate_list_with_cons] >>
    disj2_tac >>
    first_x_assum (qspecl_then [`cenv`,`env`,`Rerr err`] mp_tac) >>
    rw[] )) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  Cases_on `exp_to_Cexp F cm (s,e1)` >> fs[] >>
  Cases_on `exp_to_Cexp F cm (s,e2)` >> fs[] >>
  fs[LET_THM] >> rw[] >>
  qpat_assum `evaluate cenv env (App (Opb X) e1 e2) res` mp_tac >>
  rw[evaluate_app] >-
    let
      val ltac =
        disj1_tac >>
        rw[Cevaluate_list_with_Cevaluate] >>
        rw[Cevaluate_list_with_cons] >>
        qexists_tac `v_to_Cv cm (s,v1)` >>
        qexists_tac `v_to_Cv cm (s,v2)` >>
        rw[] >>
        Cases_on `v1` >> Cases_on `l` >> fs[do_app_def] >>
        Cases_on `v2` >> Cases_on `l` >> fs[] >> rw[] >>
        rw[CevalPrim2_def,doPrim2_def,v_to_Cv_def] >>
        qpat_assum `evaluate cenv env (Val X) Y` mp_tac >>
        rw[Once evaluate_cases,v_to_Cv_def,opb_lookup_def]
      val gtac =
        disj1_tac >>
        qexists_tac `v_to_Cv cm (s,v1)` >>
        rw[Once Cevaluate_cases] >>
        disj1_tac >>
        qexists_tac `v_to_Cv cm (s,v2)` >>
        rw[Once Cevaluate_cases] >>
        (* need argument about extending environment with variables that don't appear not affecting Cevaluate,
           and also that only variables below s.n will appear in the output of exp_to_Cexp *)
    in
      first_x_assum (qspecl_then [`cenv`,`env`,`Rval v1`] mp_tac) >>
      first_x_assum (qspecl_then [`cenv`,`env`,`Rval v2`] mp_tac) >>
      rw[] >>
      Cases_on `opb` >> rw[Once Cevaluate_cases]
      >- ltac >- gtac >- ltac >- gtac
    end
  >- let
      fun tac t = t >>
        first_x_assum (qspecl_then [`cenv`,`env`,`Rval v1`] mp_tac) >>
        first_x_assum (qspecl_then [`cenv`,`env`,`Rerr err`] mp_tac) >>
        rw[]
      val ltac = tac (
        disj1_tac >>
        qexists_tac `v_to_Cv cm (s,v1)` )
      val gtac = tac ( disj2_tac )
    in
      Cases_on `opb` >> rw[Once Cevaluate_cases] >>
      disj2_tac >>
      rw[Cevaluate_list_with_Cevaluate] >>
      rw[Cevaluate_list_with_cons]
      >- ltac >- gtac >- ltac >- gtac
    end
  >- let
      fun tac t = t >>
        first_x_assum (qspecl_then [`cenv`,`env`,`Rval err`] mp_tac) >>
        rw[]
      val gtac = tac (
        disj1_tac >>
        qexists_tac `v_to_Cv cm (s,v1)` )
      val ltac = tac ( disj2_tac )
    in
      Cases_on `opb` >> rw[Once Cevaluate_cases] >>
      disj2_tac >>
      rw[Cevaluate_list_with_Cevaluate] >>
      rw[Cevaluate_list_with_cons]
      >- ltac >- gtac >- ltac >- gtac
    end
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
