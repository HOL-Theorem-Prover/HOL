open preamble MiniMLTheory terminationProofsTheory
open CompileTheory evaluateEquationsTheory

val _ = new_theory "compileProofs"

val (remove_ctors_def,remove_ctors_ind) =
  tprove_no_defn ((remove_ctors_def,remove_ctors_ind),
  WF_REL_TAC
  `inv_image $< (\x. case x of INL (x,y) => exp_size y
                         | INR (INL (x,y)) => v_size y
                         | INR (INR (INL (x,y))) => exp3_size y
                         | INR (INR (INR (INL (x,y)))) => exp1_size y
                         | INR (INR (INR (INR (x,y)))) => exp6_size y)` >>
  rw [] >>
  TRY decide_tac >|
  [induct_on `es` >>
       rw [exp_size_def] >>
       res_tac >>
       decide_tac,
   induct_on `vs` >>
       rw [exp_size_def] >>
       res_tac >>
       decide_tac,
   induct_on `es` >>
       rw [exp_size_def] >>
       res_tac >>
       decide_tac,
   induct_on `vs` >>
       rw [exp_size_def] >>
       res_tac >>
       decide_tac]);
val _ = save_thm ("remove_ctors_def", remove_ctors_def);
val _ = save_thm ("remove_ctors_ind", remove_ctors_ind);

(*
This is too awful! Try a simpler definition of fold_consts.
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

(* TODO: Where should these go? *)

val well_typed_def = Define`
  well_typed env exp = ∃tenvC tenv t.
    type_env tenvC env tenv ∧
    type_e tenvC tenv exp t`;

val map_result_def = Define`
  (map_result f (Rval v) = Rval (f v)) ∧
  (map_result f (Rerr e) = Rerr e)`;
val _ = export_rewrites["map_result_def"];

(* ------------------------------------------------------------------------- *)

(* move to evaluateEquations *)
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

(* add to terminationProofsTheory? *)
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

(* move to listTheory (and rich_listTheory) *)
val FOLDR_MAP = store_thm("FOLDR_MAP",
    (--`!f e g l.
       FOLDR f e (MAP g l) = FOLDR (\x y. f (g x) y) e l`--),
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN Induct
    THEN ASM_REWRITE_TAC[FOLDL,MAP,FOLDR] THEN BETA_TAC
    THEN REWRITE_TAC[]);

(*
val build_rec_env_remove_ctors = store_thm(
"build_rec_env_remove_ctors",
``∀cnmap funs env. build_rec_env (funs_remove_ctors cnmap funs) (env_remove_ctors cnmap env) = env_remove_ctors cnmap (build_rec_env funs env)``,
gen_tac >>
qho_match_abbrev_tac `∀funs. P funs` >>
qsuff_tac `∀funs. P (REVERSE funs)` >-
  metis_tac [REVERSE_REVERSE] >>
qunabbrev_tac `P` >> fs[] >>
fs[env_remove_ctors_maps,funs_remove_ctors_maps,build_rec_env_def] >>
fs[rich_listTheory.FOLDR_REVERSE,rich_listTheory.MAP_REVERSE] >>
qho_match_abbrev_tac `∀funs env. FOLDL (f funs env) (MAP q env) (MAP h funs) = MAP q (FOLDL (r env funs) env funs)` >>
Induct >- rw[] >>
rw []
qx_gen_tac `p` >>
PairCases_on `p` >>
rw []
rw[MAP_APPEND,REVERSE_APPEND]
rw[FOLDR_MAP] >>
Induct_on `funs` >>
rw[]
rw[rich_listTheory.MAP_FOLDR,SimpRHS]
qmatch_abbrev_tac `FOLDR f (MAP h env) (MAP g funs) = MAP h (FOLDR q env funs)`
Q.ISPECL_THEN [`f`,`MAP h env`,`g`,`funs`] mp_tac rich_listTheory.FOLDR_MAP
type_of ``FOLDR``
rw[SimpLHS]
(*
gen_tac >>
Induct >-
  rw[build_rec_env_def,remove_ctors_def] >>
qx_gen_tac `p` >>
PairCases_on `p` >>
fs [funs_remove_ctors_maps] >>
fs [build_rec_env_def,remove_ctors_def,funs_remove_ctors_maps]
*)
gen_tac >>
qho_match_abbrev_tac `∀funs. P funs` >>
qsuff_tac `∀funs. P (REVERSE funs)` >-
  metis_tac [REVERSE_REVERSE] >>
qunabbrev_tac `P` >> fs[] >>
Induct >-
  rw[build_rec_env_def,remove_ctors_def] >>
qx_gen_tac `p` >>
PairCases_on `p` >>
fs [build_rec_env_def,funs_remove_ctors_maps] >>
rw [MAP_APPEND]
rw[rich_listTheory.FOLDR_APPEND]
FOLDR_FOLDL
DB.find"foldr"
  rw [remove_ctors_def] >>
  rw [bind_def]
build_rec_env_ind
build_rec_env_def
FOLDR_DEF
FOLDR
*)

(*
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
fs[] >> rw[remove_ctors_def]
*)

(*
val remove_ctors_thm1 = store_thm(
"remove_ctors_thm1",
``∀cnmap.
  (∀env exp r.
   evaluate' env exp r ⇒
   evaluate' (env_remove_ctors cnmap env) (remove_ctors cnmap exp) (map_result (v_remove_ctors cnmap) r)) ∧
  (∀env expl rl.
   evaluate_list' env expl rl ⇒
   evaluate_list' (env_remove_ctors cnmap env) (MAP (remove_ctors cnmap) expl) (map_result (MAP (v_remove_ctors cnmap)) rl)) ∧
  (∀env v pes r.
   evaluate_match' env v pes r ⇒
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
    metis_tac [] ) >>
  rpt gen_tac >>
  rw [evaluate'_con,remove_ctors_def] >>
  rw [Once evaluate'_cases] >>
  metis_tac []) >>
strip_tac >- (
  gen_tac >>
  Cases >> rw [remove_ctors_def] >>
  rw [Once evaluate'_cases] >-
    metis_tac [] >>
  rw [evaluate'_con] >>
  rw [Once evaluate_list'_thm] >>
  metis_tac [] ) >>
strip_tac >-
  rw [remove_ctors_def,evaluate'_var,lookup_remove_ctors] >>
strip_tac >-
  rw [remove_ctors_def,evaluate'_var,lookup_remove_ctors] >>
strip_tac >-
  rw [remove_ctors_def] >>
strip_tac >- (
  rw [remove_ctors_def] >>
  rw [evaluate'_app] >>
  disj1_tac >>
  qexists_tac `v_remove_ctors cnmap v1` >>
  rw [] >>
  qexists_tac `v_remove_ctors cnmap v2` >>
  rw [] >>
  qexists_tac `v_remove_ctors cnmap v2` >>
*)

val _ = export_theory ()
