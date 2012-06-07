open HolKernel bossLib boolLib boolSimps listTheory pred_setTheory finite_mapTheory SatisfySimps lcsymtacs
open MiniMLTheory compileTerminationTheory
val _ = new_theory "intLang"

(* TODO: move? *)
val lookup_ALOOKUP = store_thm(
"lookup_ALOOKUP",
``lookup = combin$C ALOOKUP``,
fs[FUN_EQ_THM] >> gen_tac >> Induct >- rw[] >> Cases >> rw[])
val _ = export_rewrites["lookup_ALOOKUP"];

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

val evaluate_nice_strongind = save_thm(
"evaluate_nice_strongind",
evaluate_strongind
|> Q.SPECL [`P`,`λcenv env. evaluate_list_with (P cenv env)`,`evaluate_match_with P`] |> SIMP_RULE (srw_ss()) []
|> UNDISCH_ALL
|> CONJUNCTS
|> List.hd
|> DISCH_ALL
|> Q.GEN `P`
|> SIMP_RULE (srw_ss()) [evaluate_list_with_evaluate])

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

(* TODO: move? *)

val pat_vars_def = tDefine "pat_vars"`
(pat_vars (Pvar v) = {v}) ∧
(pat_vars (Plit l) = {}) ∧
(pat_vars (Pcon c ps) = BIGUNION (IMAGE pat_vars (set ps)))`(
WF_REL_TAC `measure pat_size` >>
srw_tac[ARITH_ss][MiniMLTerminationTheory.pat1_size_thm] >>
Q.ISPEC_THEN `pat_size` imp_res_tac SUM_MAP_MEM_bound >>
srw_tac[ARITH_ss][])
val _ = export_rewrites["pat_vars_def"]

val FV_def = tDefine "FV"`
(FV (Raise _) = {}) ∧
(FV (Lit _) = {}) ∧
(FV (Con _ ls) = BIGUNION (IMAGE FV (set ls))) ∧
(FV (Var x) = {x}) ∧
(FV (Fun x e) = FV e DIFF {x}) ∧
(FV (App _ e1 e2) = FV e1 ∪ FV e2) ∧
(FV (Log _ e1 e2) = FV e1 ∪ FV e2) ∧
(FV (If e1 e2 e3) = FV e1 ∪ FV e2 ∪ FV e3) ∧
(FV (Mat e pes) = FV e ∪ BIGUNION (IMAGE (λ(p,e). FV e DIFF pat_vars p) (set pes))) ∧
(FV (Let x e b) = FV e ∪ (FV b DIFF {x})) ∧
(FV (Letrec defs b) = BIGUNION (IMAGE (λ(y,x,e). FV e DIFF ({x} ∪ (IMAGE FST (set defs)))) (set defs)) ∪ (FV b DIFF (IMAGE FST (set defs))))`
let open MiniMLTerminationTheory MiniMLTheory in
WF_REL_TAC `measure exp_size` >>
srw_tac[ARITH_ss][exp1_size_thm,exp6_size_thm,exp4_size_thm] >>
map_every (fn q => Q.ISPEC_THEN q imp_res_tac SUM_MAP_MEM_bound)
  [`exp2_size`,`exp5_size`,`exp_size`] >>
fsrw_tac[ARITH_ss][exp_size_def]
end
val _ = export_rewrites["FV_def"]

val FINITE_FV = store_thm(
"FINITE_FV",
``∀exp. FINITE (FV exp)``,
ho_match_mp_tac (theorem"FV_ind") >>
rw[pairTheory.EXISTS_PROD] >>
fsrw_tac[SATISFY_ss][])
val _ = export_rewrites["FINITE_FV"]

(* Cevaluate functional equations *)

val Cevaluate_raise = store_thm(
"Cevaluate_raise",
``∀env err res. Cevaluate env (CRaise err) res = (res = Rerr (Rraise err))``,
rw[Once Cevaluate_cases])

val Cevaluate_lit = store_thm(
"Cevaluate_lit",
``∀env l res. Cevaluate env (CLit l) res = (res = Rval (CLitv l))``,
rw[Once Cevaluate_cases])

val Cevaluate_var = store_thm(
"Cevaluate_var",
``∀env vn res. Cevaluate env (CVar vn) res = (vn ∈ FDOM env ∧ (res = Rval (env ' vn)))``,
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
``∀env ns b res. Cevaluate env (CFun ns b) res = (res = Rval (CClosure env ns b))``,
rw[Once Cevaluate_cases])

val _ = export_rewrites["Cevaluate_raise","Cevaluate_lit","Cevaluate_var","Cevaluate_mat_nil","Cevaluate_let_nil","Cevaluate_fun"]

val Cevaluate_con = store_thm(
"Cevaluate_con",
``∀env cn es res. Cevaluate env (CCon cn es) res =
(∃vs. Cevaluate_list env es (Rval vs) ∧ (res = Rval (CConv cn vs))) ∨
(∃err. Cevaluate_list env es (Rerr err) ∧ (res = Rerr err))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_tageq = store_thm(
"Cevaluate_tageq",
``∀env exp n res. Cevaluate env (CTagEq exp n) res =
  (∃m vs. Cevaluate env exp (Rval (CConv m vs)) ∧ (res = (Rval (CLitv (Bool (n = m)))))) ∨
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

val evaluate_list_with_EVERY = store_thm(
"evaluate_list_with_EVERY",
``∀P es vs. evaluate_list_with P es (Rval vs) = (LENGTH es = LENGTH vs) ∧ EVERY (UNCURRY P) (ZIP (es,MAP Rval vs))``,
gen_tac >> Induct >- (
  rw[evaluate_list_with_nil,LENGTH_NIL_SYM,EQ_IMP_THM] ) >>
rw[evaluate_list_with_cons,EQ_IMP_THM] >> rw[] >>
Cases_on `vs` >> fs[])

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

(* Lemmas *)

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

val FUN_FMAP_FAPPLY_FEMPTY_FAPPLY = store_thm(
"FUN_FMAP_FAPPLY_FEMPTY_FAPPLY",
``FINITE s ==> (FUN_FMAP ($FAPPLY FEMPTY) s ' x = FEMPTY ' x)``,
Cases_on `x IN s` >>
rw[FUN_FMAP_DEF,NOT_FDOM_FAPPLY_FEMPTY])
val _ = export_rewrites["FUN_FMAP_FAPPLY_FEMPTY_FAPPLY"]

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

val FOLDL2_Cmatch_bind_error = store_thm(
"FOLDL2_Cmatch_bind_error",
``∀f ps vs.
(FOLDL2 (λa p v. Cmatch_bind a (f a p v)) Cno_match ps vs = Cno_match) ∧
  (FOLDL2 (λa p v. Cmatch_bind a (f a p v)) Cmatch_error ps vs = Cmatch_error)``,
gen_tac >> Induct >- (Cases >> rw[]) >>
gen_tac >> Cases >> rw[])

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

(* TODO: move? *)

(*
val set_MAP_FST_fmap_to_alist = store_thm(
"set_MAP_FST_fmap_to_alist",
``set (MAP FST (fmap_to_alist fm)) = FDOM fm``,
METIS_TAC[fmap_to_alist_to_fmap,FDOM_alist_to_fmap])
val _ = export_rewrites["set_MAP_FST_fmap_to_alist"]
*)

val DIFF_UNION = store_thm(
"DIFF_UNION",
``!x y z. x DIFF (y UNION z) = x DIFF y DIFF z``,
SRW_TAC[][EXTENSION] THEN METIS_TAC[])

val DIFF_COMM = store_thm(
"DIFF_COMM",
``!x y z. x DIFF y DIFF z = x DIFF z DIFF y``,
SRW_TAC[][EXTENSION] THEN METIS_TAC[])

(* TODO: move? *)
val INJ_I = store_thm(
"INJ_I",
``∀s t. INJ I s t = s ⊆ t``,
SRW_TAC[][INJ_DEF,SUBSET_DEF])

val MAP_KEYS_I = store_thm(
"MAP_KEYS_I",
``∀fm. MAP_KEYS I fm = fm``,
rw[GSYM fmap_EQ_THM,MAP_KEYS_def,EXTENSION] >>
metis_tac[MAP_KEYS_def,INJ_I,SUBSET_UNIV,combinTheory.I_THM])
val _ = export_rewrites["MAP_KEYS_I"]

val MAP_EQ_ID = store_thm(
"MAP_EQ_ID",
``!f ls. (MAP f ls = ls) = (!x. MEM x ls ==> (f x = x))``,
PROVE_TAC[MAP_EQ_f,MAP_ID,combinTheory.I_THM])

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

(* TODO: move *)

val result_rel_def = Define`
(result_rel R (Rval v1) (Rval v2) = R v1 v2) ∧
(result_rel R (Rerr e1) (Rerr e2) = (e1 = e2)) ∧
(result_rel R _ _ = F)`
val _ = export_rewrites["result_rel_def"]

val syneq_refl = store_thm(
"syneq_refl",
``∀x. syneq x x``,
(TypeBase.induction_of``:Cv``)
|> Q.SPECL [`W syneq`,`FEVERY ((W syneq) o SND)`,`EVERY (W syneq)`]
|> SIMP_RULE(srw_ss())[]
|> UNDISCH_ALL
|> CONJUNCT1
|> DISCH_ALL
|> match_mp_tac >>
rw[] >> rw[syneq_cases] >>
fsrw_tac[DNF_ss]
[EVERY2_EVERY,MEM_ZIP,MEM_EL,EVERY_MEM,
 pairTheory.FORALL_PROD,pairTheory.UNCURRY] >>
rw[] >>
Cases_on `FLOOKUP env v` >> fs[optionTheory.OPTREL_def] >>
fsrw_tac[DNF_ss][FLOOKUP_DEF,FRANGE_DEF] >>
PROVE_TAC[])
val _ = export_rewrites["syneq_refl"]

val syneq_sym = store_thm(
"syneq_sym",
``∀x y. syneq x y ⇒ syneq y x``,
ho_match_mp_tac syneq_ind >> rw[] >>
rw[syneq_cases] >- (
  fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,
     pairTheory.FORALL_PROD] >>
  pop_assum mp_tac >>
  fs[MEM_ZIP] >>
  PROVE_TAC[] )
>- (
  fs[optionTheory.OPTREL_def] >>
  PROVE_TAC[] )
>- (
  fs[EVERY_MEM,pairTheory.FORALL_PROD,optionTheory.OPTREL_def] >>
  PROVE_TAC[] ))

val syneq_trans = store_thm(
"syneq_trans",
``∀x y. syneq x y ⇒ ∀z. syneq y z ⇒ syneq x z``,
ho_match_mp_tac syneq_ind >> rw[] >>
pop_assum mp_tac >>
rw[syneq_cases] >- (
  fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >>
  rpt (qpat_assum` LENGTH X = LENGTH Y` mp_tac) >>
  ntac 2 strip_tac >>
  fs[MEM_ZIP,pairTheory.FORALL_PROD] >>
  PROVE_TAC[] )
>- (
  fs[optionTheory.OPTREL_def] >>
  metis_tac[optionTheory.option_CASES,
            optionTheory.NOT_SOME_NONE,
            optionTheory.SOME_11] )
>- (
  fs[optionTheory.OPTREL_def,EVERY_MEM,
     pairTheory.FORALL_PROD] >>
  metis_tac[optionTheory.option_CASES,
            optionTheory.NOT_SOME_NONE,
            optionTheory.SOME_11] ))

val result_rel_refl = store_thm(
"result_rel_refl",
``(∀x. R x x) ⇒ ∀x. result_rel R x x``,
strip_tac >> Cases >> rw[])
val _ = export_rewrites["result_rel_refl"]

val result_rel_Rval = store_thm(
"result_rel_Rval",
``result_rel R (Rval v) r = ∃v'. (r = Rval v') ∧ R v v'``,
Cases_on `r` >> rw[])
val result_rel_Rerr = store_thm(
"result_rel_Rerr",
``result_rel R (Rerr e) r = (r = Rerr e)``,
Cases_on `r` >> rw[EQ_IMP_THM])
val _ = export_rewrites["result_rel_Rval","result_rel_Rerr"]

val Cmatch_result_rel_def = Define`
  (Cmatch_result_rel R (Cmatch e1) (Cmatch e2) = R e1 e2) ∧
  (Cmatch_result_rel R Cno_match r = (r = Cno_match)) ∧
  (Cmatch_result_rel R Cmatch_error r = (r = Cmatch_error)) ∧
  (Cmatch_result_rel R _ _ = F)`
val _ = export_rewrites["Cmatch_result_rel_def"]

(* TODO: move *)
val fmap_rel_def = Define`
  fmap_rel R f1 f2 = (FDOM f2 = FDOM f1) ∧ (∀x. x ∈ FDOM f1 ⇒ R (f1 ' x) (f2 ' x))`

val fmap_rel_FUPDATE_same = store_thm(
"fmap_rel_FUPDATE_same",
``fmap_rel R f1 f2 ∧ R v1 v2 ⇒ fmap_rel R (f1 |+ (k,v1)) (f2 |+ (k,v2))``,
rw[fmap_rel_def,FAPPLY_FUPDATE_THM] >> rw[])

val fmap_rel_FUPDATE_LIST_same = store_thm(
"fmap_rel_FUPDATE_LIST_same",
``∀R ls1 ls2 f1 f2.
  fmap_rel R f1 f2 ∧ (MAP FST ls1 = MAP FST ls2) ∧ (LIST_REL R (MAP SND ls1) (MAP SND ls2))
  ⇒ fmap_rel R (f1 |++ ls1) (f2 |++ ls2)``,
gen_tac >>
Induct >> Cases >> rw[FUPDATE_LIST_THM,LIST_REL_CONS1] >>
Cases_on `ls2` >> fs[FUPDATE_LIST_THM] >>
first_x_assum match_mp_tac >> fs[] >> rw[] >>
qmatch_assum_rename_tac `R a (SND b)`[] >>
Cases_on `b` >> fs[] >>
rw[fmap_rel_FUPDATE_same])

val fmap_rel_FEMPTY = store_thm(
"fmap_rel_FEMPTY",
``fmap_rel R FEMPTY FEMPTY``,
rw[fmap_rel_def])
val _ = export_rewrites["fmap_rel_FEMPTY"]

val fmap_rel_refl = store_thm(
"fmap_rel_refl",
``(∀x. R x x) ⇒ fmap_rel R x x``,
rw[fmap_rel_def])
val _ = export_rewrites["fmap_rel_refl"]

val fmap_rel_extend_env_same = store_thm(
"fmap_rel_extend_env_same",
``fmap_rel R env1 env2 ∧ LIST_REL R v1 v2 ∧ (LENGTH xs = LENGTH v1)
⇒ fmap_rel R (extend_env env1 xs v1) (extend_env env2 xs v2)``,
rw[extend_env_def,LIST_REL_EL_EQN,FOLDL2_FUPDATE_LIST] >>
rw[MAP2_MAP,FST_pair,SND_pair,MAP_ZIP] >>
match_mp_tac fmap_rel_FUPDATE_LIST_same >>
rw[MAP_ZIP,LIST_REL_EL_EQN,LENGTH_ZIP])

val fmap_rel_extend_rec_env_same = store_thm(
"fmap_rel_extend_rec_env_same",
``fmap_rel R env1 env2 ∧ LIST_REL R vs1 vs2 ∧ (LENGTH ns = LENGTH vs1) ∧
  (∀b. MEM b rs ⇒ R (CRecClos env1 rs defs b) (CRecClos env2 rs defs b))
  ⇒ fmap_rel R
      (extend_rec_env env1 rs defs ns vs1)
      (extend_rec_env env2 rs defs ns vs2)``,
rw[extend_rec_env_def,FOLDL_FUPDATE_LIST,FOLDL2_FUPDATE_LIST,LIST_REL_EL_EQN] >>
rw[MAP2_MAP,FST_pair,SND_pair,MAP_ZIP] >>
match_mp_tac fmap_rel_FUPDATE_LIST_same >>
rw[MAP_ZIP,LENGTH_ZIP,LIST_REL_EL_EQN] >>
match_mp_tac fmap_rel_FUPDATE_LIST_same >>
rw[MAP_ZIP,LENGTH_ZIP,LIST_REL_EL_EQN,EL_MAP,MAP_MAP_o,combinTheory.o_DEF] >>
fsrw_tac[DNF_ss][MEM_EL])

val FDOM_extend_env = store_thm(
"FDOM_extend_env",
``(LENGTH ns = LENGTH vs) ⇒ (FDOM (extend_env env ns vs) = FDOM env ∪ (set ns))``,
rw[extend_env_def,FOLDL2_FUPDATE_LIST,FDOM_FUPDATE_LIST] >>
rw[MAP2_MAP,FST_pair,SND_pair,MAP_ZIP])
val _ = export_rewrites["FDOM_extend_env"]

val FDOM_extend_rec_env = store_thm(
"FDOM_extend_rec_env",
``(LENGTH ns = LENGTH vs) ⇒ (FDOM (extend_rec_env env' ns' defs ns vs) = FDOM env' ∪ (set ns') ∪ (set ns))``,
rw[extend_rec_env_def,FOLDL_FUPDATE_LIST,FOLDL2_FUPDATE_LIST,FDOM_FUPDATE_LIST] >>
rw[MAP2_MAP,FST_pair,SND_pair,MAP_ZIP,MAP_MAP_o,combinTheory.o_DEF])
val _ = export_rewrites["FDOM_extend_rec_env"]

(* TODO: move *)
val LIST_REL_EVERY_ZIP = store_thm(
"LIST_REL_EVERY_ZIP",
``!R l1 l2. LIST_REL R l1 l2 = ((LENGTH l1 = LENGTH l2) /\ EVERY (UNCURRY R) (ZIP (l1,l2)))``,
GEN_TAC THEN Induct THEN SRW_TAC[][LENGTH_NIL_SYM] THEN
SRW_TAC[][EQ_IMP_THM,LIST_REL_CONS1] THEN SRW_TAC[][] THEN
Cases_on `l2` THEN FULL_SIMP_TAC(srw_ss())[])

val Cpmatch_syneq = store_thm(
"Cpmatch_syneq",
``(∀env1 p v1 env2 v2.
   fmap_rel syneq env1 env2 ∧ syneq v1 v2 ⇒
     Cmatch_result_rel (fmap_rel syneq)
       (Cpmatch env1 p v1) (Cpmatch env2 p v2)) ∧
  (∀env1 ps vs1 env2 vs2.
   fmap_rel syneq env1 env2 ∧ LIST_REL syneq vs1 vs2 ⇒
     Cmatch_result_rel (fmap_rel syneq)
       (Cpmatch_list env1 ps vs1) (Cpmatch_list env2 ps vs2))``,
ho_match_mp_tac Cpmatch_ind >>
strip_tac >- (
  rw[Cpmatch_def,fmap_rel_FUPDATE_same] ) >>
strip_tac >- (
  ntac 4 gen_tac >>
  Cases >> rw[Cpmatch_def,syneq_cases] ) >>
strip_tac >- (
  rpt gen_tac >> strip_tac >> gen_tac >>
  Cases >> rw[Cpmatch_def,syneq_cases,EVERY2_EVERY] >>
  pop_assum (match_mp_tac o MP_CANON) >>
  rw[LIST_REL_EVERY_ZIP] ) >>
strip_tac >- (
  ntac 5 gen_tac >>
  Cases >> rw[Cpmatch_def,syneq_cases] ) >>
strip_tac >- (
  rw[Cpmatch_def,syneq_cases] >>
  rw[Cpmatch_def]) >>
strip_tac >- (
  rw[Cpmatch_def,syneq_cases] >>
  rw[Cpmatch_def]) >>
strip_tac >- (
  rw[Cpmatch_def,syneq_cases] ) >>
strip_tac >- (
  rw[Cpmatch_def,syneq_cases] >>
  rw[Cpmatch_def]) >>
strip_tac >- (
  rw[Cpmatch_def,syneq_cases] >>
  rw[Cpmatch_def]) >>
strip_tac >- (
  rw[Cpmatch_def]) >>
strip_tac >- (
  rw[Cpmatch_def,LIST_REL_CONS1] >>
  rw[Cpmatch_def] >>
  Cases_on `Cpmatch env1 p v1` >> fs[] >>
  qmatch_assum_rename_tac `syneq v1 v2`[] >>
  first_x_assum (qspecl_then [`env2`,`v2`] mp_tac) >>
  Cases_on `Cpmatch env2 p v2` >> rw[Cmatch_result_rel_def]) >>
strip_tac >- (
  rw[Cpmatch_def,LIST_REL_CONS1] >>
  rw[Cpmatch_def] ) >>
rw[Cpmatch_def])

val fmap_rel_FUNION_rels = store_thm(
"fmap_rel_FUNION_rels",
``fmap_rel R f1 f2 ∧ fmap_rel R f3 f4 ⇒ fmap_rel R (f1 ⊌ f3) (f2 ⊌ f4)``,
rw[fmap_rel_def,FUNION_DEF] >> rw[])

val MAP_ZIP_SND_triple = store_thm(
"MAP_ZIP_SND_triple",
``(LENGTH l1 = LENGTH l2) ⇒ (MAP (λ(x,y,z). f y z) (ZIP(l1,l2)) = MAP (UNCURRY f) l2)``,
strip_tac >> (
MAP_ZIP
|> Q.GEN`g`
|> Q.ISPEC `UNCURRY (f:'b->'c->'d)`
|> SIMP_RULE(srw_ss())[combinTheory.o_DEF,pairTheory.LAMBDA_PROD]
|> UNDISCH_ALL
|> CONJUNCTS
|> Lib.el 4
|> MATCH_ACCEPT_TAC))

val (closed_rules,closed_ind,closed_cases) = Hol_reln`
(closed (CLitv l)) ∧
(EVERY closed vs ⇒ closed (CConv cn vs)) ∧
((∀v. v ∈ FRANGE env ⇒ closed v) ∧ free_vars b ⊆ FDOM env ∪ set xs
  ⇒ closed (CClosure env xs b)) ∧
((∀v. v ∈ FRANGE env ⇒ closed v) ∧
 (LENGTH ns = LENGTH defs) ∧
 (MEM n ns) ∧
 (∀i xs b. i < LENGTH ns ∧ (EL i defs = (xs,b)) ⇒
    free_vars b ⊆ FDOM env ∪ set ns ∪ set xs)
  ⇒ closed (CRecClos env ns defs n))`

(* TODO: move *)
val every_result_def = Define`
  (every_result P (Rerr _) = T) ∧
  (every_result P (Rval v) = P v)`
val _ = export_rewrites["every_result_def"]

(* could do this more generally, with a notion of subvalue? *)
val Cpmatch_closed = store_thm(
"Cpmatch_closed",
``(∀env p v env'. (∀v. v ∈ FRANGE env ⇒ closed v) ∧ closed v ∧ (Cpmatch env p v = Cmatch env') ⇒
                  (∀v. v ∈ FRANGE env' ⇒ closed v)) ∧
  (∀env ps vs env'. (∀v. v ∈ FRANGE env ⇒ closed v) ∧ EVERY closed vs ∧ (Cpmatch_list env ps vs = Cmatch env') ⇒
                  (∀v. v ∈ FRANGE env' ⇒ closed v))``,
ho_match_mp_tac Cpmatch_ind >>
rw[Cpmatch_def] >- (
  fs[FRANGE_DEF,DOMSUB_FAPPLY_THM] >>
  rw[] >> PROVE_TAC[] )
>- (
  fs[Once closed_cases] ) >>
Cases_on `Cpmatch env p v` >> fs[] >>
PROVE_TAC[])

val FUPDATE_LIST_APPLY_HO_THM = store_thm(
"FUPDATE_LIST_APPLY_HO_THM",
``∀P f kvl k.
(∃n. n < LENGTH kvl ∧ (k = EL n (MAP FST kvl)) ∧ P (EL n (MAP SND kvl)) ∧
     (∀m. n < m ∧ m < LENGTH kvl ⇒ EL m (MAP FST kvl) ≠ k)) ∨
(¬MEM k (MAP FST kvl) ∧ P (f ' k))
⇒ (P ((f |++ kvl) ' k))``,
metis_tac[FUPDATE_LIST_APPLY_MEM,FUPDATE_LIST_APPLY_NOT_MEM])

val Cevaluate_closed = store_thm(
"Cevaluate_closed",
``∀env exp res. Cevaluate env exp res ⇒ free_vars exp ⊆ FDOM env ∧ (∀v. v ∈ FRANGE env ⇒ closed v) ⇒ every_result closed res``,
ho_match_mp_tac Cevaluate_nice_ind >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[] >> fsrw_tac[DNF_ss][FRANGE_DEF] ) >>
strip_tac >- ( rw[] >> rw[Once closed_cases]) >>
strip_tac >- (
  rw[Cevaluate_list_with_value,FOLDL_UNION_BIGUNION] >>
  rw[Once closed_cases] >>
  fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >> rw[] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
  PROVE_TAC[] ) >>
strip_tac >- rw[] >>
strip_tac >- ( rw[] >> rw[Once closed_cases]) >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[] >> fs[] >>
  fsrw_tac[DNF_ss][Q.SPEC `CConv m vs` closed_cases,EVERY_MEM,MEM_EL] ) >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[FOLDL_UNION_BIGUNION_paired] >>
  first_x_assum match_mp_tac >>
  imp_res_tac Cpmatch_pat_vars >>
  conj_tac >- (
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    PROVE_TAC[] ) >>
  `env ' n ∈ FRANGE env` by (rw[FRANGE_DEF] >> PROVE_TAC[]) >>
  PROVE_TAC[Cpmatch_closed] ) >>
strip_tac >- rw[FOLDL_UNION_BIGUNION_paired] >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[FOLDL_UNION_BIGUNION] >>
  first_x_assum match_mp_tac >>
  fsrw_tac[DNF_ss][SUBSET_DEF,FRANGE_DEF,DOMSUB_FAPPLY_THM] >>
  PROVE_TAC[] ) >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[FOLDL_UNION_BIGUNION_paired] >>
  first_x_assum match_mp_tac >>
  fs[FOLDL2_FUPDATE_LIST_paired,FDOM_FUPDATE_LIST,MAP_ZIP,LENGTH_ZIP,MAP2_MAP,FST_triple] >>
  fsrw_tac[DNF_ss][FRANGE_DEF,SUBSET_DEF,FDOM_FUPDATE_LIST,MAP_ZIP,LENGTH_ZIP] >>
  conj_tac >- PROVE_TAC[] >>
  qho_match_abbrev_tac `(∀x. P x ⇒ R x) ∧ (∀x. Q x ⇒ R x)` >>
  qsuff_tac `∀x. Q x ∨ (¬Q x ∧ P x) ⇒ R x` >- PROVE_TAC[] >>
  gen_tac >>
  unabbrev_all_tac >> rw[] >>
  ho_match_mp_tac FUPDATE_LIST_APPLY_HO_THM >|[
    disj1_tac >>
    fsrw_tac[DNF_ss][EL_MAP,MAP_ZIP,LENGTH_ZIP,MEM_EL,EL_ZIP] >>
    qpat_assum `LENGTH ns = LENGTH defs` assume_tac >>
    qexists_tac `n` >> fs[LENGTH_ZIP,EL_MAP,EL_ZIP] >>
    fs[EL_ALL_DISTINCT_EL_EQ] >>
    qabbrev_tac`d = EL n defs` >>
    PairCases_on `d` >> fs[] >>
    rw[Once closed_cases] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,FRANGE_DEF] >>
    rw[] >>
    first_x_assum (qspecl_then [`x`,`n`] mp_tac) >>
    rw[] >> PROVE_TAC[],
    disj2_tac >>
    fs[MAP_ZIP,MEM_MAP,MEM_ZIP,LENGTH_ZIP,pairTheory.EXISTS_PROD,MEM_EL] >>
    PROVE_TAC[]
  ]) >>
strip_tac >- (
  rw[FOLDL_FUPDATE_LIST,FOLDL_UNION_BIGUNION_paired] >>
  first_x_assum match_mp_tac >>
  fs[FDOM_FUPDATE_LIST,MAP_MAP_o,combinTheory.o_DEF] >>
  fsrw_tac[DNF_ss][FRANGE_DEF,SUBSET_DEF,FDOM_FUPDATE_LIST,MAP_MAP_o,combinTheory.o_DEF] >>
  conj_tac >- PROVE_TAC[] >>
  qho_match_abbrev_tac `(∀x. P x ⇒ R x) ∧ (∀x. Q x ⇒ R x)` >>
  qsuff_tac `∀x. Q x ∨ (¬Q x ∧ P x) ⇒ R x` >- PROVE_TAC[] >>
  gen_tac >>
  unabbrev_all_tac >> rw[] >>
  ho_match_mp_tac FUPDATE_LIST_APPLY_HO_THM >|[
    disj1_tac >>
    fsrw_tac[DNF_ss][EL_MAP,MAP_ZIP,LENGTH_ZIP,MEM_EL,EL_ZIP] >>
    qpat_assum `LENGTH ns = LENGTH defs` assume_tac >>
    qexists_tac `n` >> fs[LENGTH_ZIP,EL_MAP,EL_ZIP] >>
    fs[EL_ALL_DISTINCT_EL_EQ] >>
    rw[Once closed_cases,MEM_EL] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,FRANGE_DEF]
    >- PROVE_TAC[] >- PROVE_TAC[] >>
    qmatch_assum_rename_tac `EL i defs = (xs,b)`[] >>
    qx_gen_tac `x` >>
    first_x_assum (qspecl_then [`x`,`i`] mp_tac) >>
    fs[] >> PROVE_TAC[],
   disj2_tac >>
   fs[MAP_ZIP,MEM_MAP,MEM_ZIP,LENGTH_ZIP,pairTheory.EXISTS_PROD,MEM_EL] >>
   PROVE_TAC[]
  ]) >>
strip_tac >- (
  rw[] >>
  rw[Once closed_cases] >>
  fs[SUBSET_DEF] >>
  PROVE_TAC[] ) >>
strip_tac >- (
  rw[FOLDL_UNION_BIGUNION] >>
  first_x_assum match_mp_tac >>
  rw[] >- (
    qpat_assum `X ==> closed Y` mp_tac >>
    rw[Once closed_cases] ) >>
  pop_assum mp_tac >>
  fs[extend_env_def,FOLDL2_FUPDATE_LIST,FRANGE_DEF] >>
  fs[MAP2_MAP,FST_pair,SND_pair,MAP_MAP_o,MAP_ZIP] >>
  fs[Q.SPEC`CClosure env' ns exp'`closed_cases,FRANGE_DEF] >>
  fsrw_tac[DNF_ss][] >>
  fs[GSYM FORALL_AND_THM] >>
  qx_gen_tac `x` >>
  qho_match_abbrev_tac `(P ∧ Q ⇒ R) ∧ (P' ∧ Q ⇒ R)` >>
  qsuff_tac `(P' ⇒ Q ⇒ R) ∧ (¬P' ∧ P ⇒ Q ⇒ R)` >- METIS_TAC[] >>
  unabbrev_all_tac >> rw[] >>
  ho_match_mp_tac FUPDATE_LIST_APPLY_HO_THM >|[
    disj1_tac >>
    fsrw_tac[DNF_ss][MAP_ZIP,LENGTH_ZIP,MEM_MAP,MEM_EL,EL_ALL_DISTINCT_EL_EQ] >>
    fsrw_tac[DNF_ss][Cevaluate_list_with_value] >>
    `free_vars (EL n es) ⊆ FDOM env` by (
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
      PROVE_TAC[] ) >>
    PROVE_TAC[prim_recTheory.LESS_REFL],
    disj2_tac >>
    fs[MAP_ZIP]
  ]) >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[FOLDL_UNION_BIGUNION] >>
  first_x_assum match_mp_tac >>
  rw[] >- (
    qpat_assum `X ==> closed Y` mp_tac >>
    rw[Once closed_cases] >>
    pop_assum (qspecl_then [`i`,`ns`,`exp'`] mp_tac) >>
    imp_res_tac find_index_LESS_LENGTH >>
    fs[] >> PROVE_TAC[] ) >>
  pop_assum mp_tac >>
  fs[extend_rec_env_def,FRANGE_DEF,FOLDL2_FUPDATE_LIST,FOLDL_FUPDATE_LIST] >>
  fs[MAP2_MAP,FST_pair,SND_pair,MAP_MAP_o,MAP_ZIP] >>
  fs[Q.SPEC`CRecClos env' ns' defs n`closed_cases,FRANGE_DEF] >>
  fsrw_tac[DNF_ss][] >>
  fs[GSYM FORALL_AND_THM] >>
  qx_gen_tac `x` >>
  fs[CONJ_COMM] >>
  qho_match_abbrev_tac `(P0 ∧ Q ⇒ R) ∧ (P1 ∧ Q ⇒ R) ∧ (P2 ∧ Q ⇒ R)` >>
  qsuff_tac `(P0 ∧ Q ⇒ R) ∧ (¬P0 ∧ P1 ∧ Q ⇒ R) ∧ (¬P0 ∧ ¬P1 ∧ P2 ∧ Q ⇒ R)` >- METIS_TAC[] >>
  unabbrev_all_tac >> rw[] >>
  ho_match_mp_tac FUPDATE_LIST_APPLY_HO_THM >|[
    disj1_tac >>
    fsrw_tac[DNF_ss][MAP_ZIP,LENGTH_ZIP,MEM_MAP,MEM_EL,EL_ALL_DISTINCT_EL_EQ] >>
    fsrw_tac[DNF_ss][Cevaluate_list_with_value] >>
    qmatch_assum_rename_tac `x = EL z ns`[] >>
    `free_vars (EL z es) ⊆ FDOM env` by (
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
      PROVE_TAC[] ) >>
    PROVE_TAC[prim_recTheory.LESS_REFL],
    disj2_tac >> fs[MAP_ZIP] >>
    ho_match_mp_tac FUPDATE_LIST_APPLY_HO_THM >>
    disj1_tac >>
    fsrw_tac[DNF_ss][MAP_ZIP,LENGTH_ZIP,MEM_MAP,MEM_EL,MAP_MAP_o,combinTheory.o_DEF] >>
    qmatch_assum_rename_tac `x = EL z ns'`[] >>
    qexists_tac `z` >>
    qpat_assum `LENGTH ns' = LENGTH defs` assume_tac >>
    fs[EL_MAP] >>
    fs[EL_ALL_DISTINCT_EL_EQ] >>
    simp_tac (srw_ss()) [Once closed_cases] >>
    fsrw_tac[DNF_ss][MEM_EL,FRANGE_DEF,EL_MAP] >>
    qexists_tac `z` >> fs[] >> rw[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    PROVE_TAC[],
    disj2_tac >> fs[MAP_ZIP] >>
    ho_match_mp_tac FUPDATE_LIST_APPLY_HO_THM >>
    disj2_tac >>
    fs[MAP_ZIP,MAP_MAP_o,combinTheory.o_DEF] ]) >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[] >>
  first_x_assum match_mp_tac >>
  imp_res_tac CevalPrim2_free_vars >>
  fs[] ) >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[] >>
  first_x_assum match_mp_tac >>
  imp_res_tac doPrim2_free_vars >>
  fs[] ) >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[Cevaluate_list_with_value] >> fs[] >>
  Cases_on `n` >> fs[] ) >>
strip_tac >- (
  rw[Cevaluate_list_with_error] >>
  qexists_tac `0` >> rw[] ) >>
rw[Cevaluate_list_with_error] >>
qexists_tac `0` >> rw[])

(* TODO: move *)
val IN_FRANGE = store_thm(
"IN_FRANGE",
``!f v. v IN FRANGE f = ?k. k IN FDOM f /\ (f ' k = v)``,
SRW_TAC[][FRANGE_DEF])

val final0 =
  qsuff_tac `env0 ⊌ env1 = env1` >- PROVE_TAC[] >>
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  rw[Abbr`env0`,Abbr`env1`,SUBMAP_DEF,DRESTRICT_DEF,FUNION_DEF,FUN_FMAP_DEF,pairTheory.UNCURRY,FAPPLY_FUPDATE_THM] >>
  fsrw_tac[boolSimps.DNF_ss,SATISFY_ss][FUN_FMAP_DEF,pairTheory.UNCURRY,MEM_EL,fmap_rel_def] >>
  metis_tac[]

val final =
  qmatch_assum_abbrev_tac `∀env'. Cevaluate (env0 ⊌ env') ee rr` >>
  qmatch_abbrev_tac `Cevaluate env1 ee rr` >>
  final0

val Cevaluate_any_env = store_thm(
"Cevaluate_any_env",
``∀env exp res. Cevaluate env exp res ⇒
    ∀env'. fmap_rel syneq env env' ∧ (∀v. v ∈ FRANGE env' ⇒ closed v) ∧ free_vars exp ⊆ FDOM env ⇒
      ∀env''. (∀v. v ∈ FRANGE env'' ⇒ closed v) ⇒
        ∃res'. Cevaluate ((DRESTRICT env' (free_vars exp)) ⊌ env'') exp res' ∧ (result_rel syneq) res res'``,
ho_match_mp_tac Cevaluate_nice_ind >>
strip_tac >- rw[] >>
strip_tac >- rw[DRESTRICT_DEF,FUNION_DEF,fmap_rel_def] >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[Cevaluate_con,Cevaluate_list_with_Cevaluate,
     Cevaluate_list_with_value,FOLDL_UNION_BIGUNION] >>
  fsrw_tac[DNF_ss,SATISFY_ss][SUBSET_DEF,MEM_EL,result_rel_def] >>
  rw[syneq_cases,EVERY2_EVERY,EVERY_MEM] >>
  rw[pairTheory.FORALL_PROD] >>
  Q.PAT_ABBREV_TAC `env1 = X ⊌ env''` >>
  qpat_assum `∀n env' env''. n < LENGTH es ⇒ X` (fn th => th
    |> SIMP_RULE(srw_ss())[Once SWAP_FORALL_THM]
    |> Q.SPEC `env'`
    |> SIMP_RULE(srw_ss())[Once SWAP_FORALL_THM]
    |> qspec_then`env1` mp_tac) >>
  rw[] >>
  fs[GSYM RIGHT_EXISTS_IMP_THM] >>
  fs[Once SKOLEM_THM] >>
  fsrw_tac[DNF_ss][] >>
  qexists_tac `GENLIST f (LENGTH vs)` >>
  fs[LENGTH_ZIP,MEM_ZIP] >>
  fsrw_tac[DNF_ss][] >>
  `∀v. v ∈ FRANGE env1 ⇒ closed v` by (
    unabbrev_all_tac >>
    fsrw_tac[DNF_ss][FRANGE_DEF,DRESTRICT_DEF,FUNION_DEF] >>
    METIS_TAC[] ) >>
  fs[] >>
  qx_gen_tac `n` >> strip_tac >>
  rpt (first_x_assum (qspec_then `n` mp_tac)) >> rw[] >>
  qmatch_assum_abbrev_tac `Cevaluate (env0 ⊌ env1) ee rr` >>
  final0) >>
strip_tac >- (
  map_every qx_gen_tac [`env`,`m`] >>
  rw[Cevaluate_con,Cevaluate_list_with_Cevaluate,
     Cevaluate_list_with_error,FOLDL_UNION_BIGUNION] >>
  qpat_assum `n < LENGTH es` assume_tac >>
  fsrw_tac[DNF_ss,SATISFY_ss][SUBSET_DEF,MEM_EL,result_rel_def] >>
  qexists_tac `n` >> fs[] >>
  first_x_assum (qspec_then `env'` mp_tac) >> fs[] >>
  strip_tac >> conj_tac  >- (
    qmatch_abbrev_tac `Cevaluate env1 ee rr` >>
    `∀v. v ∈ FRANGE env1 ⇒ closed v` by (
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss][FRANGE_DEF,DRESTRICT_DEF,FUNION_DEF] >>
      metis_tac[] ) >>
    first_x_assum (qspec_then `env1` mp_tac) >> fs[] >>
    qmatch_abbrev_tac `Cevalutae (env0 ⊌ env1) ee rr ⇒ Cevaluate env1 ee rr` >>
    strip_tac >>
    final0 ) >>
  qx_gen_tac `m` >> strip_tac >>
  first_x_assum (qspec_then `m` mp_tac) >>
  `m < LENGTH es` by srw_tac[ARITH_ss][] >>
  fsrw_tac[DNF_ss,SATISFY_ss][SUBSET_DEF,MEM_EL] >>
  rw[] >>
  Q.PAT_ABBREV_TAC `env1 = X ⊌ env''` >>
  first_x_assum (qspecl_then [`env'`,`env1`] mp_tac) >>
  rw[] >>
  `∀v. v ∈ FRANGE env1 ⇒ closed v` by (
    unabbrev_all_tac >>
    fsrw_tac[DNF_ss][FRANGE_DEF,DRESTRICT_DEF,FUNION_DEF] >>
    metis_tac[] ) >>
  fs[] >>
  qmatch_assum_abbrev_tac `Cevaluate (env0 ⊌ env1) ee rr` >>
  qmatch_assum_rename_tac `syneq v v2`[] >>
  qexists_tac `v2` >> final0) >>
strip_tac >- (
  rw[Cevaluate_tageq] >>
  fsrw_tac[DNF_ss][result_rel_def] >>
  qexists_tac `m` >> fs[] >>
  fsrw_tac[DNF_ss][syneq_cases] >>
  PROVE_TAC[]) >>
strip_tac >- rw[Cevaluate_tageq,result_rel_def] >>
strip_tac >- (
  rw[Cevaluate_proj] >>
  fsrw_tac[DNF_ss][result_rel_def] >>
  qmatch_abbrev_tac `X` >>
  qpat_assum `∀env' env''. Y` mp_tac >>
  rw[syneq_cases] >> unabbrev_all_tac >>
  qexists_tac `m` >>
  pop_assum (qspec_then `env'` mp_tac) >> rw[] >>
  fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_EL,SKOLEM_THM] >>
  pop_assum (qspec_then `env''` mp_tac) >> rw[] >>
  pop_assum mp_tac >> fs[LENGTH_ZIP,EL_ZIP] >>
  PROVE_TAC[]) >>
strip_tac >- rw[Cevaluate_proj,result_rel_def] >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[Cevaluate_mat_cons,FOLDL_UNION_BIGUNION_paired,
     DRESTRICT_DEF,FUNION_DEF] >>
  fsrw_tac[DNF_ss][] >>
  disj1_tac >> disj1_tac >>
  `n ∈ FDOM env''` by fs[fmap_rel_def] >> fs[] >>
  fs[Once Cpmatch_FEMPTY] >>
  Cases_on `Cpmatch FEMPTY p (env ' n)` >> fs[] >>
  rw[] >>
  imp_res_tac Cpmatch_pat_vars >>
  fsrw_tac[DNF_ss,SATISFY_ss][SUBSET_DEF,pairTheory.FORALL_PROD] >>
  `∀x. x ∈ free_vars exp ⇒ x ∈ Cpat_vars p ∨ x ∈ FDOM env` by
    PROVE_TAC[] >> fs[] >>
  `Cmatch_result_rel (fmap_rel syneq) (Cpmatch FEMPTY p (env ' n)) (Cpmatch FEMPTY p (env'' ' n))` by (
    match_mp_tac (CONJUNCT1 Cpmatch_syneq) >>
    fs[fmap_rel_def] ) >>
  pop_assum mp_tac >>
  Cases_on `Cpmatch FEMPTY p (env'' ' n)` >> rw[] >>
  qmatch_assum_rename_tac `Cpmatch FEMPTY p (env'' ' n) = Cmatch env2` [] >>
  Q.PAT_ABBREV_TAC `env1 = env2 ⊌ (X ⊌ env''')` >>
  qmatch_assum_rename_tac `Cpmatch FEMPTY p (env ' n) = Cmatch env4` [] >>
  first_x_assum (qspecl_then [`env2 ⊌ env''`,`env1`] mp_tac) >>
  `∀v. v ∈ FRANGE env2 ⇒ closed v` by (
    rpt strip_tac >>
    match_mp_tac (MP_CANON (CONJUNCT1 Cpmatch_closed)) >>
    PROVE_TAC [IN_FRANGE,FRANGE_FEMPTY,NOT_IN_EMPTY] ) >>
  `∀v. v ∈ FRANGE (env2 ⊌ env'') ⇒ closed v` by (
    fs[FRANGE_DEF,FUNION_DEF] >> PROVE_TAC[] ) >>
  `∀v. v ∈ FRANGE env1 ⇒ closed v` by (
    unabbrev_all_tac >>
    fsrw_tac[DNF_ss][FRANGE_DEF,FUNION_DEF,DRESTRICT_DEF] >>
    metis_tac[]) >>
  fs[] >>
  rw[fmap_rel_FUNION_rels] >>
  unabbrev_all_tac >>
  Q.PAT_ABBREV_TAC `env1 = env2 ⊌ X` >>
  qmatch_assum_abbrev_tac `Cevaluate (env0 ⊌ env1) ee rr` >>
  qexists_tac `rr` >> final0) >>
strip_tac >- (
  rw[Cevaluate_mat_cons,FOLDL_UNION_BIGUNION_paired,
     DRESTRICT_DEF,FUNION_DEF] >>
  fsrw_tac[DNF_ss][] >>
  disj1_tac >> disj2_tac >>
  `n ∈ FDOM env'` by fs[fmap_rel_def] >> fs[] >>
  fs[Once Cpmatch_FEMPTY] >>
  Cases_on `Cpmatch FEMPTY p (env ' n)` >> fs[] >>
  qpat_assum `n ∈ FDOM env` assume_tac >> fs[] >>
  `Cmatch_result_rel (fmap_rel syneq) (Cpmatch FEMPTY p (env ' n)) (Cpmatch FEMPTY p (env' ' n))` by (
    match_mp_tac (CONJUNCT1 Cpmatch_syneq) >>
    fs[fmap_rel_def] ) >>
  pop_assum mp_tac >>
  Cases_on `Cpmatch FEMPTY p (env' ' n)` >> rw[] >>
  Q.PAT_ABBREV_TAC `env1 = (X ⊌ env'')` >>
  first_x_assum (qspecl_then [`env'`,`env1`] mp_tac) >>
  `∀v. v ∈ FRANGE env1 ⇒ closed v` by (
    unabbrev_all_tac >>
    fsrw_tac[DNF_ss][FRANGE_DEF,FUNION_DEF,DRESTRICT_DEF] >>
    metis_tac[]) >>
  rw[] >>
  qmatch_assum_abbrev_tac `Cevaluate (env0 ⊌ env1) ee rr` >>
  qexists_tac `rr` >> final0) >>
strip_tac >- rw[] >>
strip_tac >- (
  fs[Cevaluate_let_cons,FOLDL_UNION_BIGUNION,
     DRESTRICT_DEF,FUNION_DEF] >>
  rpt gen_tac >>
  strip_tac >> strip_tac >>
  fsrw_tac[DNF_ss,SATISFY_ss][SUBSET_DEF] >>
  qx_gen_tac `env''` >>
  strip_tac >>
  strip_tac >>
  disj1_tac >>
  Q.PAT_ABBREV_TAC `env1 = X ⊌ env''` >>
  qpat_assum `∀env' env''. P ⇒ Q ⇒ ∃v'. X ∧ syneq v v'`
    (qspecl_then [`env'`,`env1`] mp_tac) >>
  `∀v. v ∈ FRANGE env1 ⇒ closed v` by (
    unabbrev_all_tac >>
    fsrw_tac[DNF_ss][FRANGE_DEF,FUNION_DEF,DRESTRICT_DEF] >>
    metis_tac[]) >>
  rw[] >>
  rw[Once SWAP_EXISTS_THM] >>
  qmatch_assum_abbrev_tac `Cevaluate (env0 ⊌ env1) ee rr` >>
  qmatch_assum_rename_tac `syneq v v2`[] >>
  qexists_tac `v2` >>
  simp_tac(srw_ss())[RIGHT_EXISTS_AND_THM,GSYM CONJ_ASSOC] >>
  conj_tac >- final0 >>
  `∀x. x ∈ free_vars b ∧ ¬MEM x ns ⇒ (x = n) ∨ x ∈ FDOM env` by (
    PROVE_TAC[] ) >> fs[] >>
  `∀x x'. x ∈ free_vars x' ∧ MEM x' es ⇒ (x = n) ∨ x ∈ FDOM env` by (
    PROVE_TAC[] ) >> fsrw_tac[SATISFY_ss][] >>
  first_x_assum (qspecl_then [`env' |+ (n,v2)`, `env1 |+ (n,v2)`] mp_tac) >>
  asm_simp_tac bool_ss [fmap_rel_FUPDATE_same,syneq_refl] >>
  `every_result closed rr` by (
    match_mp_tac (MP_CANON Cevaluate_closed) >>
    qexists_tac `env0 ⊌ env1` >>
    qexists_tac `ee` >> fs[] >>
    unabbrev_all_tac >>
    fs[DRESTRICT_DEF] >>
    conj_tac >- (
      fsrw_tac[][SUBSET_DEF,fmap_rel_def] ) >>
    fsrw_tac[DNF_ss][FRANGE_DEF,DRESTRICT_DEF,FUNION_DEF] >>
    metis_tac[] ) >>
  `∀v. v ∈ FRANGE (env' |+ (n,v2)) ⇒ closed v` by (
    fsrw_tac[DNF_ss][FRANGE_DEF,DOMSUB_FAPPLY_THM] >>
    fs[Abbr`rr`] ) >>
  `∀v. v ∈ FRANGE (env1 |+ (n,v2)) ⇒ closed v` by (
    fsrw_tac[DNF_ss][FRANGE_DEF,DOMSUB_FAPPLY_THM] >>
    fs[Abbr`rr`] ) >>
  asm_simp_tac bool_ss [] >>
  strip_tac >>
  qmatch_assum_rename_tac `result_rel syneq res r`[] >>
  qexists_tac `r` >> asm_simp_tac(srw_ss())[] >>
  qunabbrev_tac `env1` >>
  Q.PAT_ABBREV_TAC `env1 = X |+ (n,v2)` >>
  qunabbrev_tac `env0` >>
  qmatch_assum_abbrev_tac `Cevaluate (env0 ⊌ env1) (CLet ns es b) r` >>
  final0 ) >>
strip_tac >- (
  rw[Cevaluate_let_cons,FOLDL_UNION_BIGUNION] >>
  disj2_tac >> fs[] >>
  first_x_assum (qspec_then `env'` mp_tac) >> rw[] >>
  qmatch_abbrev_tac `Cevaluate env1 ee rr` >>
  `∀v. v ∈ FRANGE env1 ⇒ closed v` by (
    unabbrev_all_tac >>
    fsrw_tac[DNF_ss][FRANGE_DEF,DRESTRICT_DEF,FUNION_DEF] >>
    metis_tac[] ) >>
  first_x_assum (qspec_then `env1` mp_tac) >> rw[] >>
  qmatch_assum_abbrev_tac `Cevaluate (env0 ⊌ env1) ee rr` >>
  final0) >>
(*
strip_tac >- (
  rw[FOLDL_UNION_BIGUNION_paired] >>
  rw[Once Cevaluate_cases] >>
  qpat_assum `LENGTH ns = LENGTH defs` assume_tac >>
  fs[FOLDL2_FUPDATE_LIST_paired,FDOM_FUPDATE_LIST] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.FORALL_PROD,
                   MAP2_MAP,MEM_MAP,MEM_ZIP,LENGTH_ZIP,
                   EL_MAP,MAP_ZIP,FST_triple,MEM_EL] >>
  `∀x. x ∈ free_vars exp ⇒ x ∈ FDOM env ∨ ∃n. (x = EL n ns) ∧ n < LENGTH defs` by PROVE_TAC[] >> fs[] >>
  pop_assum kall_tac >>
  qho_match_abbrev_tac `∃res'. Cevaluate (env0 |++ (ls0 env0)) exp res' ∧ result_rel syneq res res'` >>
  `fmap_rel syneq (env |++ (ls0 env)) (env' |++ (ls0 env0))` by (
    unabbrev_all_tac >> fs[] >>
    match_mp_tac fmap_rel_FUPDATE_LIST_same >>
    fs[MAP_ZIP,LENGTH_ZIP] >>
    fs[LIST_REL_EL_EQN,LENGTH_ZIP,EL_MAP,EL_ZIP] >>
    qx_gen_tac `n` >> strip_tac >>
    Cases_on `EL n defs` >> fs[] >>
    rw[syneq_cases] >>
    fs[fmap_rel_def,optionTheory.OPTREL_def,FLOOKUP_DEF] >>
    `v ∈ FDOM env` by (
      first_x_assum (qspecl_then [`v`,`n`] mp_tac) >>
      rw[] ) >> fs[] >>
    qmatch_abbrev_tac `(v ∈ FDOM (DRESTRICT env0 ss) ∨ v ∈ FDOM env2) ∧ syneq (env ' v) (env1 ' v)` >>
    `v ∈ ss` by (
      srw_tac[DNF_ss][Abbr`ss`,MEM_EL] >>
      disj2_tac >> qexists_tac `n` >> rw[] ) >>
    fs[DRESTRICT_DEF] >>
    rw[FUNION_DEF,DRESTRICT_DEF] ) >>
  first_x_assum (qspecl_then [`env' |++ (ls0 env0)`,`env0 |++ ls0 env0`] mp_tac) >>
  fs[Abbr`ls0`] >>
  pop_assum kall_tac >>
  disch_then (Q.X_CHOOSE_THEN `res'` strip_assume_tac) >>
  qexists_tac `res'` >> fs[] >>
  unabbrev_all_tac >>
  qmatch_abbrev_tac `Cevaluate env1 ee rr` >>
  qmatch_assum_abbrev_tac `Cevaluate (env0 ⊌ env1) ee rr` >>
  qsuff_tac `env0 ⊌ env1 = env1` >- PROVE_TAC[] >>
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  unabbrev_all_tac >>
  ntac 2 (pop_assum kall_tac) >>
  fs[SUBMAP_DEF] >>
  qx_gen_tac `x` >> strip_tac >>
  qpat_assum `LENGTH ns = LENGTH defs` assume_tac >>
  conj_tac >- (
    fsrw_tac[DNF_ss][DRESTRICT_DEF,FDOM_FUPDATE_LIST,pairTheory.EXISTS_PROD,MAP_MAP_o,MEM_MAP,MEM_ZIP,LENGTH_ZIP,MEM_EL,EL_ZIP] >>
    PROVE_TAC[EL_ZIP,pairTheory.PAIR_EQ,pairTheory.pair_CASES] ) >>
  fs[MAP_ZIP_SND_triple] >>
  Cases_on `MEM x ns` >- (
    fsrw_tac[DNF_ss][DRESTRICT_DEF] >>
    match_mp_tac FUPDATE_LIST_APPLY_MEM >>
    fs[LENGTH_ZIP,MAP_ZIP,MEM_EL] >>
    qexists_tac `n` >>
    qpat_assum `n < LENGTH ns` mp_tac >>
    fs[] >> strip_tac >>
    reverse conj_tac >- (
      fs[EL_ALL_DISTINCT_EL_EQ] ) >>
    fs[EL_MAP] >>
    match_mp_tac FUPDATE_LIST_APPLY_MEM >>
    fs[MAP_ZIP,LENGTH_ZIP] >>
    qexists_tac `n` >> fs[] >>
    reverse conj_tac >- (
      fs[EL_ALL_DISTINCT_EL_EQ] ) >>
    fs[EL_MAP] ) >>
  fs[DRESTRICT_DEF,FDOM_FUPDATE_LIST,MAP_ZIP] >>
  match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
  fs[MAP_ZIP] >>
  match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
  fs[MAP_ZIP] >>
  fs[DRESTRICT_DEF,FUNION_DEF] ) >>
strip_tac >- (
  rw[FOLDL_UNION_BIGUNION_paired] >>
  rw[Once Cevaluate_cases] >>
  qpat_assum `LENGTH ns = LENGTH defs` assume_tac >>
  fs[FOLDL_FUPDATE_LIST,FDOM_FUPDATE_LIST] >>
  fs[MAP_MAP_o,combinTheory.o_DEF] >>
  `free_vars exp ⊆ FDOM env ∪ set ns` by (
    fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.FORALL_PROD] >>
    PROVE_TAC[] ) >>
  fs[] >>
  fsrw_tac[DNF_ss][] >>
  qho_match_abbrev_tac `∃res'. Cevaluate (env0 |++ (ls0 env0)) exp res' ∧ result_rel syneq res res'` >>
  `fmap_rel syneq (env |++ (ls0 env)) (env' |++ (ls0 env0))` by (
    unabbrev_all_tac >> fs[] >>
    match_mp_tac fmap_rel_FUPDATE_LIST_same >>
    fs[MAP_ZIP,LENGTH_ZIP,MAP_MAP_o,combinTheory.o_DEF] >>
    fs[LIST_REL_EL_EQN,LENGTH_ZIP,EL_MAP,EL_ZIP] >>
    qx_gen_tac `n` >> strip_tac >>
    rw[syneq_cases,EVERY_MEM,pairTheory.FORALL_PROD] >>
    fs[fmap_rel_def,optionTheory.OPTREL_def,FLOOKUP_DEF] >>
    `v ∈ FDOM env` by (
      fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.FORALL_PROD] >>
      PROVE_TAC[] ) >> fs[] >>
    qmatch_abbrev_tac `(v ∈ FDOM (DRESTRICT env0 ss) ∨ v ∈ FDOM env2) ∧ syneq (env ' v) (env1 ' v)` >>
    `v ∈ ss` by (
      srw_tac[DNF_ss][Abbr`ss`,pairTheory.EXISTS_PROD] >>
      PROVE_TAC[]) >>
    fs[DRESTRICT_DEF] >>
    rw[FUNION_DEF,DRESTRICT_DEF] ) >>
  first_x_assum (qspecl_then [`env' |++ (ls0 env0)`,`env0 |++ ls0 env0`] mp_tac) >>
  fs[Abbr`ls0`] >>
  pop_assum kall_tac >>
  disch_then (Q.X_CHOOSE_THEN `res'` strip_assume_tac) >>
  qexists_tac `res'` >> fs[] >>
  unabbrev_all_tac >>
  qmatch_abbrev_tac `Cevaluate env1 ee rr` >>
  qmatch_assum_abbrev_tac `Cevaluate (env0 ⊌ env1) ee rr` >>
  qsuff_tac `env0 ⊌ env1 = env1` >- PROVE_TAC[] >>
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  unabbrev_all_tac >>
  ntac 2 (pop_assum kall_tac) >>
  fs[SUBMAP_DEF] >>
  qx_gen_tac `x` >> strip_tac >>
  qpat_assum `LENGTH ns = LENGTH defs` assume_tac >>
  conj_tac >- (
    fsrw_tac[DNF_ss][DRESTRICT_DEF,FDOM_FUPDATE_LIST,pairTheory.EXISTS_PROD,MAP_MAP_o,MEM_MAP,MEM_ZIP,LENGTH_ZIP,MEM_EL,EL_ZIP] >>
    PROVE_TAC[EL_ZIP,pairTheory.PAIR_EQ,pairTheory.pair_CASES] ) >>
  Cases_on `MEM x ns` >- (
    fsrw_tac[DNF_ss][DRESTRICT_DEF] >>
    match_mp_tac FUPDATE_LIST_APPLY_MEM >>
    fs[LENGTH_ZIP,MAP_ZIP,MEM_EL,MAP_MAP_o,combinTheory.o_DEF] >>
    qexists_tac `n` >>
    qpat_assum `n < LENGTH ns` mp_tac >>
    fs[] >> strip_tac >>
    reverse conj_tac >- (
      fs[EL_ALL_DISTINCT_EL_EQ] ) >>
    fs[EL_MAP] >>
    match_mp_tac FUPDATE_LIST_APPLY_MEM >>
    fs[MAP_ZIP,LENGTH_ZIP,MAP_MAP_o,combinTheory.o_DEF] >>
    qexists_tac `n` >> fs[] >>
    reverse conj_tac >- (
      fs[EL_ALL_DISTINCT_EL_EQ] ) >>
    fs[EL_MAP] ) >>
  fs[DRESTRICT_DEF,FDOM_FUPDATE_LIST,MAP_ZIP,MAP_MAP_o,combinTheory.o_DEF] >>
  match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
  fs[MAP_ZIP,MAP_MAP_o,combinTheory.o_DEF] >>
  match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
  fs[MAP_ZIP,MAP_MAP_o,combinTheory.o_DEF] >>
  fs[DRESTRICT_DEF,FUNION_DEF] ) >>
strip_tac >- (
  rw[] >>
  rw[syneq_cases,FLOOKUP_DEF] >>
  rw[DRESTRICT_DEF,optionTheory.OPTREL_def] >>
  `v ∈ FDOM env` by fs[SUBSET_DEF] >> fs[] >>
  fs[fmap_rel_def] >>
  rw[DRESTRICT_DEF,FUNION_DEF] ) >>
strip_tac >- (
  rw[FOLDL_UNION_BIGUNION] >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >>
  disj1_tac >>
  rw[Cevaluate_list_with_Cevaluate] >>
  fs[Cevaluate_list_with_value] >>
  fsrw_tac[DNF_ss][] >>
  qmatch_assum_rename_tac `fmap_rel syneq env env2`[] >>
  qpat_assum `∀env2 env0. fmap_rel syneq env nv0 ⇒ P` (qspec_then `env2` mp_tac) >>
  rw[Once syneq_cases] >>
  fsrw_tac[DNF_ss][] >>
  Q.PAT_ABBREV_TAC `env0 = (X ⊌ Y : string |-> Cv) ` >>
  first_x_assum (qspec_then `env0` mp_tac) >>
  rw[] >>
  qmatch_assum_abbrev_tac `Cevaluate env1 exp (Rval (CClosure env3 ns b))` >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `env3` >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `ns` >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `b` >>
  `env1 = env0` by (
    unabbrev_all_tac >>
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    rw[SUBMAP_DEF,DRESTRICT_DEF,FUNION_DEF] ) >>
  unabbrev_all_tac >>
  fsrw_tac[DNF_ss][] >>
  qpat_assum `∀n env1 env2. P` (qspec_then `env2` mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
  `∀n. n < LENGTH es ⇒ free_vars (EL n es) ⊆ FDOM env` by (
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
    PROVE_TAC[] ) >>
  fs[] >>
  ntac 2 (pop_assum kall_tac) >>
  qmatch_assum_abbrev_tac `Cevaluate env3 exp vv` >>
  disch_then (qspec_then `env3` (mp_tac o SIMP_RULE(srw_ss())[GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM])
                  o CONV_RULE SWAP_FORALL_CONV) >>
  rw[] >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `GENLIST f (LENGTH vs)` >>
  fs[] >>
  qunabbrev_tac `env3` >>
  fs[DRESTRICT_FUNION,FUNION_ASSOC] >>
  qabbrev_tac `fvs = free_vars exp ∪ BIGUNION (IMAGE free_vars (set es))` >>
  `∀n. n < LENGTH vs ⇒ (free_vars (EL n es) ∪ fvs = fvs)` by (
    rw[GSYM SUBSET_UNION_ABSORPTION] >>
    srw_tac[DNF_ss][Abbr`fvs`,SUBSET_DEF,MEM_EL] >>
    PROVE_TAC[] ) >>
  fs[] >>
  qpat_assum `LENGTH ns = LENGTH vs` assume_tac >>
  fs[FDOM_extend_env,Abbr`vv`] >>

  (*
  extend_env_def
  rw[GSYM CONJ_ASSOC,RIGHT_EXISTS_AND_THM] >- (
    qunabbrev_tac `env3` >>
    fs[DRESTRICT_FUNION,FUNION_ASSOC]
    DB.match [] ``DRESTRICT fm e1 ⊌ xx``
    `DRESTRICT env2 (free_vars (EL n es)) ⊌ env3 = env3` by (
      unabbrev_all_tac >>
      rw[GSYM SUBMAP_FUNION_ABSORPTION]
  rw[]
  `Cevaluate env0 exp (Rval (CClosure env3 ns b))` by (
    qsuff_tac `
    qunabbrev_tac `env1`
  rw[LEFT_EXISTS_AND_THM]
  fsrw_tac[DNF_ss][]
  *)

  cheat ) >>
strip_tac >- (
  rw[FOLDL_UNION_BIGUNION] >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >>
  disj2_tac >> disj1_tac >>
  rw[Cevaluate_list_with_Cevaluate] >>
  fs[Cevaluate_list_with_error] >>
  fsrw_tac[DNF_ss][] >>
  cheat ) >>
*)
cheat )

(*
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
*)

val Cevaluate_free_vars_env = save_thm(
"Cevaluate_free_vars_env",
Cevaluate_any_env
|> SPEC_ALL
|> UNDISCH_ALL
|> Q.SPEC `env`
|> SIMP_RULE (srw_ss()) []
|> UNDISCH_ALL
|> Q.SPEC `FEMPTY`
|> SIMP_RULE (srw_ss()) [FUNION_FEMPTY_2]
|> DISCH_ALL
|> Q.GEN `res` |> Q.GEN `exp` |> Q.GEN `env`)

val _ = export_theory()
