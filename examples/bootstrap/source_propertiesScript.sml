
open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory pairTheory finite_mapTheory stringTheory llistTheory;
open source_valuesTheory source_syntaxTheory source_semanticsTheory mp_then;

val _ = new_theory "source_properties";


(* In this file we prove that the big-step relational semantics (--->)
   is equal to a special case of the big-step functional semantics (evals).

  (env, xs, s) ---> (vs, s')
  =
  ∃ck. evals env xs (s with clock := ck) = (Res vs, s') ∧
       s.clock = s'.clock

   This is theorem Eval_eq_evals.

   This file also proves theorems that are used in proof automation. *)


Theorem evals_set_clock:
  (∀env x s r s'.
     eval env x s = (Res r,s') ⇒
     ∀ck. ∃ck0. eval env x (s with clock := ck0) = (Res r,s' with clock := ck)) ∧
  (∀env xs s r s'.
     evals env xs s = (Res r,s') ⇒
     ∀ck. ∃ck0. evals env xs (s with clock := ck0) = (Res r,s' with clock := ck))
Proof
  ho_match_mp_tac eval_ind \\ rw []
  THEN1 fs [eval_def,state_component_equality]
  THEN1 fs [eval_def,state_component_equality,AllCaseEqs()]
  THEN1
   (fs [eval_def,state_component_equality,AllCaseEqs()]
    \\ rw [] \\ fs [PULL_EXISTS]
    \\ first_x_assum (qspec_then ‘ck’ mp_tac) \\ strip_tac
    \\ qexists_tac ‘ck0’ \\ fs []
    \\ fs [eval_op_def,AllCaseEqs(),return_def,fail_def] \\ fs [])
  THEN1
   (fs [eval_def,state_component_equality,AllCaseEqs()]
    \\ rw [] \\ fs [PULL_EXISTS]
    \\ last_x_assum (qspec_then ‘ck’ mp_tac) \\ strip_tac
    \\ last_x_assum (qspec_then ‘ck0’ mp_tac) \\ strip_tac
    \\ qexists_tac ‘ck0'’ \\ fs [])
  THEN1
   (fs [eval_def,state_component_equality,AllCaseEqs()]
    \\ rw [] \\ fs [PULL_EXISTS]
    \\ last_x_assum (qspec_then ‘ck’ mp_tac) \\ strip_tac
    \\ last_x_assum (qspec_then ‘ck0’ mp_tac) \\ strip_tac
    \\ qexists_tac ‘ck0'’ \\ fs []
    \\ fs [take_branch_def,AllCaseEqs(),fail_def,return_def]
    \\ rw [] \\ fs [])
  THEN1
   (fs [eval_def,state_component_equality,AllCaseEqs()]
    \\ rw [] \\ fs [PULL_EXISTS]
    \\ last_x_assum (qspec_then ‘ck’ mp_tac) \\ strip_tac
    \\ last_x_assum (qspec_then ‘ck0+1’ mp_tac) \\ strip_tac
    \\ qexists_tac ‘ck0'’ \\ fs []
    \\ fs [get_env_and_body_def,env_and_body_def,AllCaseEqs(),fail_def,return_def]
    \\ rw [] \\ fs [])
  THEN1 fs [eval_def,state_component_equality,AllCaseEqs()]
  THEN1
   (fs [eval_def,state_component_equality,AllCaseEqs()]
    \\ rw [] \\ fs [PULL_EXISTS]
    \\ last_x_assum (qspec_then ‘ck’ mp_tac) \\ strip_tac
    \\ last_x_assum (qspec_then ‘ck0’ mp_tac) \\ strip_tac
    \\ qexists_tac ‘ck0'’ \\ fs [])
QED

Theorem eval_set_clock = CONJUNCT1 evals_set_clock;
Theorem evals_set_clock[allow_rebind] = CONJUNCT2 evals_set_clock;


Theorem Eval_imp_evals:
  ∀env xs s vs s'.
    (env, xs, s) ---> (vs, s') ⇒
      ∃ck. evals env xs (s with clock := ck) = (Res vs, s') ∧ s.clock = s'.clock
Proof
  ho_match_mp_tac (Eval_ind
    |> Q.SPEC ‘λ(env,xs,s) (vs,s'). P env xs s vs s'’
    |> SIMP_RULE (srw_ss()) [FORALL_PROD] |> GEN_ALL)
  \\ rw [] \\ fs [eval_def,state_component_equality]
  THEN1 (fs [eval_def,AllCaseEqs()]
    \\ drule eval_set_clock
    \\ disch_then (qspec_then ‘ck'’ mp_tac)
    \\ strip_tac \\ fs []
    \\ qexists_tac ‘ck0’ \\ fs [])
  THEN1 (fs [eval_def,AllCaseEqs(),eval_op_def,fail_def,return_def] \\ rw []
    \\ qexists_tac ‘ck’ \\ fs [])
  THEN1
   (fs [eval_def,AllCaseEqs()]
    \\ last_x_assum assume_tac
    \\ drule eval_set_clock
    \\ disch_then (qspec_then ‘ck'’ mp_tac)
    \\ strip_tac \\ fs []
    \\ qexists_tac ‘ck0’ \\ fs [])
  \\ fs [eval_def,AllCaseEqs()]
  \\ drule evals_set_clock
  \\ TRY
    (disch_then (qspec_then ‘ck'’ mp_tac)
     \\ strip_tac \\ fs []
     \\ qexists_tac ‘ck0’ \\ fs []
     \\ fs [take_branch_def,AllCaseEqs(),return_def,fail_def] \\ NO_TAC)
  \\ disch_then (qspec_then ‘ck'+1’ mp_tac)
  \\ strip_tac \\ fs []
  \\ qexists_tac ‘ck0’ \\ fs []
  \\ fs [AllCaseEqs(),return_def,fail_def,get_env_and_body_def,env_and_body_def]
QED

Theorem evals_imp_Eval:
  ∀ck env xs s vs s'.
    evals env xs s = (Res vs, s') ⇒
    (env, xs, s with clock := ck) ---> (vs, s' with clock := ck)
Proof
  gen_tac \\ ho_match_mp_tac evals_ind \\ rw []
  THEN1
   (once_rewrite_tac [Eval_cases] \\ fs []
    \\ fs [eval_def] \\ rw [] \\ fs [state_component_equality])
  THEN1
   (once_rewrite_tac [Eval_cases] \\ fs []
    \\ fs [eval_def] \\ rw [] \\ fs [state_component_equality]
    \\ fs [AllCaseEqs()] \\ rw [] \\ fs [])
  THEN1
   (once_rewrite_tac [Eval_cases] \\ fs []
    \\ fs [eval_def,AllCaseEqs()] \\ rw [] \\ fs []
    \\ goal_assum (first_assum o mp_then.mp_then mp_then.Any mp_tac)
    \\ fs [eval_op_def,AllCaseEqs(),return_def,fail_def] \\ fs [])
  THEN1
   (once_rewrite_tac [Eval_cases] \\ fs []
    \\ fs [eval_def,AllCaseEqs()] \\ rw [] \\ fs []
    \\ goal_assum (first_assum o mp_then.mp_then mp_then.Any mp_tac) \\ fs [])
  THEN1
   (once_rewrite_tac [Eval_cases] \\ fs []
    \\ fs [eval_def,AllCaseEqs()] \\ rw [] \\ fs []
    \\ fs [take_branch_def,AllCaseEqs(),return_def,fail_def] \\ rw [] \\ fs []
    \\ goal_assum (first_assum o mp_then.mp_then (mp_then.Pos (el 1)) mp_tac) \\ fs [])
  THEN1
   (once_rewrite_tac [Eval_cases] \\ fs []
    \\ fs [eval_def,AllCaseEqs(),get_env_and_body_def,fail_def] \\ rw [] \\ fs []
    \\ fs [env_and_body_def,AllCaseEqs(),return_def,fail_def] \\ rw [] \\ fs []
    \\ goal_assum (first_assum o mp_then.mp_then (mp_then.Pos (el 1)) mp_tac) \\ fs [])
  \\ fs [eval_def,AllCaseEqs()] \\ rw [] \\ fs [PULL_EXISTS]
  THEN1 (once_rewrite_tac [Eval_cases] \\ fs [] \\ metis_tac [])
  \\ Cases_on ‘xs’ \\ fs [eval_def]
  \\ once_rewrite_tac [Eval_cases] \\ fs [] \\ metis_tac []
QED

Theorem Eval_eq_evals:
  (env, xs, s1) ---> (vs, s2)
  =
  ∃ck. evals env xs (s1 with clock := ck) = (Res vs, s2) ∧
       s1.clock = s2.clock
Proof
  eq_tac THEN1 metis_tac [Eval_imp_evals]
  \\ rw [] \\ drule evals_imp_Eval \\ fs []
  \\ qsuff_tac ‘s1 with clock := s2.clock = s1 ∧ s2 with clock := s1.clock = s2’
  THEN1 metis_tac [] \\ fs [state_component_equality]
QED


(* Prove a more useful version of Eval_cases called Eval_eq *)

val thms =
  map (fn tm => Q.SPEC tm Eval_cases |> SIMP_RULE (srw_ss()) [])
  [‘(env,[],s)’,
   ‘(env,x::y::xs,s1)’,
   ‘(env,[Const v],s)’,
   ‘(env,[Var n],s)’,
   ‘(env,[Op f xs],s1)’,
   ‘(env,[Let n x y],s1)’,
   ‘(env,[If test xs y z],s1)’,
   ‘(env,[Call fname xs],s1)’]

Triviality Call_eq:
  (env,[Call fname xs],s1) ---> a1 ⇔
  ∃vs s2 v s3.
    (env,xs,s1) ---> (vs,s2) ∧
    app fname vs s2 (v,s3) ∧ a1 = ([v],s3)
Proof
  fs thms \\ fs [app_cases,PULL_EXISTS] \\ metis_tac []
QED

Theorem Eval_eq = LIST_CONJ (butlast thms @ [Call_eq] |> map GEN_ALL);


(* later states *)

Definition later_def:
  s1 ≤ s2 ⇔
    s1.output ≼ s2.output ∧
    LSUFFIX s1.input s2.input ∧
    s2.clock = s1.clock ∧
    s1.funs = s2.funs
End

Theorem later_refl:
  ∀s. s ≤ (s:state)
Proof
  rewrite_tac [later_def] \\ fs []
QED

Theorem later_antisym:
  ∀s1 s2. s1 ≤ s2 ∧ s2 ≤ s1 ∧ LFINITE s1.input ⇒ s1 = s2
Proof
  once_rewrite_tac [state_component_equality]
  \\ rewrite_tac [later_def,rich_listTheory.IS_SUFFIX_compute] \\ rpt strip_tac
  \\ imp_res_tac rich_listTheory.IS_PREFIX_ANTISYM
  \\ imp_res_tac LSUFFIX_ANTISYM
  \\ metis_tac [listTheory.REVERSE_11]
QED

Theorem later_trans:
  ∀s1 s2 s3. s1 ≤ s2 ∧ s2 ≤ s3 ⇒ s1 ≤ s3
Proof
  rewrite_tac [later_def] \\ rw []
  \\ imp_res_tac llistTheory.LPREFIX_TRANS
  \\ metis_tac [rich_listTheory.IS_PREFIX_TRANS,LSUFFIX_TRANS]
QED

Theorem eval_op_later:
  eval_op f vs s = (res,t) ⇒ s ≤ t
Proof
  fs [eval_op_def,AllCaseEqs(),fail_def,return_def] \\ rw []
  \\ fs [later_refl] \\ fs [later_def]
  \\ Cases_on ‘s.input’ \\ fs [] \\ Cases_on ‘t’ \\ fs [LSUFFIX]
QED

Theorem Eval_later:
  (env,xs,s) ---> (vs,t) ⇒ s ≤ t
Proof
  qsuff_tac ‘∀s1 s2. s1 ---> s2 ==> SND (SND s1) ≤ SND s2’
  THEN1 (fs [FORALL_PROD] \\ metis_tac [])
  \\ ho_match_mp_tac Eval_strongind \\ rw [later_refl]
  \\ imp_res_tac eval_op_later
  \\ imp_res_tac later_trans \\ fs []
QED


(* Free variables *)

Definition free_vars_def[simp]:
  free_vars (Var x) = [x] ∧
  free_vars (Const _) = [] ∧
  free_vars (Op _ xs) = FLAT (MAP free_vars xs) ∧
  free_vars (If _ xs  y z) = FLAT (MAP free_vars xs) ++ free_vars y ++ free_vars z ∧
  free_vars (Let n x y) = free_vars x ++ FILTER (\k. k ≠ n) (free_vars y) ∧
  free_vars (Call _ xs) = FLAT (MAP free_vars xs)
Termination
  WF_REL_TAC ‘measure exp_size’ \\ rw []
  \\ qsuff_tac ‘!xs a. MEM a xs ==> exp_size a <= exp1_size xs’
  \\ TRY (rw [] \\ res_tac \\ fs [] \\ NO_TAC)
  \\ Induct \\ fs [] \\ rw [] \\ fs [exp_size_def]
  \\ res_tac \\ fs []
End

Theorem delete_env_update:
  (env,xs,s) ---> (vs,t) /\ ~MEM n (FLAT (MAP free_vars xs)) ==>
  (env⦇n ↦ x⦈,xs,s) ---> (vs,t)
Proof
  qsuff_tac ‘∀s1 s2. s1 ---> s2 ==>
               ∀env xs s vs t.
                 s1 = (env,xs,s) /\ s2 = (vs,t) /\ s1 ---> s2 /\
                 ~MEM n (FLAT (MAP free_vars xs)) ==>
                 (env⦇n ↦ x⦈,xs,s) ---> (vs,t)’
  THEN1 fs [PULL_FORALL]
  \\ ho_match_mp_tac Eval_strongind \\ rw []
  \\ rpt (pop_assum mp_tac)
  \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ rw [] \\ fs [MEM_FILTER]
  \\ once_rewrite_tac [Eval_cases] \\ fs [combinTheory.APPLY_UPDATE_THM]
  \\ TRY (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [] \\ NO_TAC)
  \\ goal_assum (first_assum o mp_then (Pos (el 1)) mp_tac) \\ fs []
  \\ Cases_on ‘n = n'’ \\ fs []
  \\ metis_tac [combinTheory.UPDATE_COMMUTES]
QED

Theorem remove_env_update[simp]:
  ¬MEM n (free_vars x0) ⇒
  ((env⦇n ↦ SOME v⦈,[x0],s) ---> res <=> (env,[x0],s) ---> res)
Proof
  rw [] \\ eq_tac \\ rw [] \\ PairCases_on ‘res’
  THEN1
   (drule delete_env_update
    \\ disch_then (qspecl_then [‘env n’,‘n’] mp_tac) \\ fs []
    \\ qsuff_tac ‘env⦇n ↦ env n⦈ = env’ \\ simp_tac bool_ss [] \\ fs [])
  \\ match_mp_tac delete_env_update \\ fs []
QED


(* Substitution *)

fun get_induction_for_def def = let
  fun mk_arg_vars xs = let
    fun aux [] = []
      | aux (x::xs) =
          mk_var("v" ^ (int_to_string (length xs + 1)),type_of x) :: aux xs
    in (rev o aux o rev) xs end
  fun f tm = let
    val (lhs,rhs) = dest_eq tm
    val (const,args) = strip_comb lhs
    val vargs = mk_arg_vars args
    val args = pairSyntax.list_mk_pair args
    in (const,vargs,args,rhs) end
  val cs = def |> CONJUNCTS |> map (f o concl o SPEC_ALL)
  val cnames = map (fn (x,_,_,_) => x) cs |> op_mk_set aconv
  val cs = map (fn c => (c, map (fn (x,y,z,q) => (y,z,q))
                              (filter (fn (x,_,_,_) => aconv c x) cs))) cnames
           |> map (fn (c,x) => (c,hd (map (fn (x,y,z) => x) x),
                                map (fn (x,y,z) => (y,z)) x))
  fun split_at P [] = fail()
    | split_at P (x::xs) = if P x then ([],x,xs) else let
        val (x1,y1,z1) = split_at P xs
        in (x::x1,y1,z1) end
  fun find_pat_match (_,args,pats) = let
    val pat = hd pats |> fst
    val vs = pairSyntax.list_mk_pair args
    val ss = fst (match_term vs pat)
    val xs = map (subst ss) args
    in (split_at (not o is_var) xs) end
  val xs = map find_pat_match cs
  val ty = map (fn (_,x,_) => type_of x) xs |> hd
  val raw_ind = TypeBase.induction_of ty
  fun my_mk_var ty = mk_var("pat_var", ty)
  fun list_mk_fun_type [] = hd []
    | list_mk_fun_type [ty] = ty
    | list_mk_fun_type (t::ts) = mk_type("fun",[t,list_mk_fun_type ts])
  fun goal_step index [] = []
    | goal_step index ((xs,t,ys)::rest) = let
    val v = my_mk_var (type_of t)
    val args = xs @ [v] @ ys
    val P = mk_var("P" ^ (int_to_string index) ,
              list_mk_fun_type ((map type_of args) @ [bool]))
    val prop = list_mk_comb(P,args)
    val goal = list_mk_forall(args,prop)
    val step = mk_abs(v,list_mk_forall(xs @ ys,prop))
    in (P,(goal,step)) :: goal_step (index+1) rest end
  val res = goal_step 0 xs
  fun ISPEC_LIST [] th = th
    | ISPEC_LIST (x::xs) th = ISPEC_LIST xs (ISPEC x th)
  val ind = ISPEC_LIST (map (snd o snd) res) raw_ind
            |> CONV_RULE (DEPTH_CONV BETA_CONV)
  val goal1 = ind |> concl |> dest_imp |> snd
  val goal2 = list_mk_conj (map (fst o snd) res)
  val goal = mk_imp(goal1,goal2)
  val lemma = snd ((REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []) ([],goal)) []
  val ind = MP lemma (ind |> UNDISCH_ALL) |> DISCH_ALL |> GENL (map fst res)
  in ind end handle HOL_ERR _ =>
  failwith "unable to construct induction theorem from TypeBase info"

Definition subst_def:
  subst v x (Var w) = SOME (if v = w then x else Var w) ∧
  subst v x (Const n) = SOME (Const n) ∧
  subst v x (Call d ys) = OPTION_MAP (Call d) (substs v x ys) ∧
  subst v x (Op f ys) = OPTION_MAP (Op f) (substs v x ys) ∧
  subst v x (If cmp xs y z) =
    (case (substs v x xs, subst v x y, subst v x z) of
     | (SOME xs, SOME y, SOME z) => SOME (If cmp xs y z)
     | _ => NONE) ∧
  subst v x (Let n y z) =
    (case subst v x y of
     | NONE => NONE
     | SOME t =>
         if n = v then SOME (Let n t z) else
         if MEM n (free_vars x) then NONE else
           OPTION_MAP (Let n t) (subst v x z)) ∧
  substs v x [] = SOME [] ∧
  substs v x (y::ys) =
    (case subst v x y of
     | NONE => NONE
     | SOME t =>
       case substs v x ys of
       | NONE => NONE
       | SOME ts => SOME (t::ts))
End

Theorem Eval_cons:
  LFINITE s.input ⇒
  (env,t::ts,s) ---> (vs,s) =
  ∃v vs'. vs = v::vs' ∧ (env,[t],s) ---> ([v],s) ∧ (env,ts,s) ---> (vs',s)
Proof
  Cases_on ‘ts’ \\ fs [Eval_eq,PULL_EXISTS]
  \\ Cases_on ‘t’ \\ fs [Eval_eq,PULL_EXISTS]
  \\ Cases_on ‘vs’ \\ fs [app_cases]
  \\ metis_tac [later_antisym,later_trans,Eval_later,eval_op_later]
QED

val later_tac =
  imp_res_tac Eval_later \\ imp_res_tac eval_op_later
  \\ imp_res_tac later_antisym \\ rpt BasicProvers.var_eq_tac \\ fs [];

Theorem subst_thm:
  LFINITE s.input ⇒
  (∀v x y z env xv yv.
    subst v x y = SOME z ∧
    (env,[x],s) ---> ([xv],s) ∧
    (env⦇v ↦ SOME xv⦈,[y],s) ---> ([yv],s) ⇒
    (env,[z],s) ---> ([yv],s)) ∧
  (∀v x ys zs env xv yvs.
    substs v x ys = SOME zs ∧
    (env,[x],s) ---> ([xv],s) ∧
    (env⦇v ↦ SOME xv⦈,ys,s) ---> (yvs,s) ⇒
    (env,zs,s) ---> (yvs,s))
Proof
  strip_tac
  \\ ho_match_mp_tac (get_induction_for_def subst_def)
  \\ rpt strip_tac
  THEN1 (fs [subst_def,AllCaseEqs()] \\ rw [] \\ fs [])
  THEN1 (fs [subst_def,AllCaseEqs()] \\ rw [] \\
         fs [Eval_eq,combinTheory.APPLY_UPDATE_THM,AllCaseEqs()] \\ rw [])
  THEN1
   (fs [subst_def,AllCaseEqs(),Eval_eq] \\ rw [] \\ fs []
    \\ first_x_assum drule
    \\ later_tac
    \\ rpt (disch_then drule) \\ rw []
    \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
  THEN1
   (fs [subst_def,AllCaseEqs()] \\ rw []
    \\ rpt (first_x_assum drule)
    \\ rpt (disch_then drule \\ strip_tac)
    \\ fs [Eval_eq] \\ later_tac
    \\ last_x_assum drule \\ strip_tac
    \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
    \\ Cases_on ‘b’ \\ fs [] \\ metis_tac [])
  THEN1
   (fs [subst_def,AllCaseEqs()] \\ rw []
    THEN1
     (rpt (first_x_assum drule)
      \\ rpt (disch_then drule \\ strip_tac)
      \\ fs [Eval_eq] \\ later_tac
      \\ last_x_assum drule \\ strip_tac
      \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
    \\ fs [Eval_eq]
    \\ last_x_assum drule
    \\ rpt (disch_then drule)
    \\ later_tac \\ fs []
    \\ rpt (disch_then drule)
    \\ rw []
    \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
    \\ last_x_assum drule
    \\ disch_then (qspec_then ‘env⦇n ↦ SOME v1⦈’ mp_tac)
    \\ fs [] \\ disch_then drule
    \\ disch_then match_mp_tac
    \\ metis_tac [combinTheory.UPDATE_COMMUTES])
  THEN1
   (fs [subst_def,Eval_eq,AllCaseEqs(),app_cases] \\ rw [PULL_EXISTS]
    \\ rpt (goal_assum (first_assum o mp_then (Pos last) mp_tac) \\ fs [])
    \\ res_tac \\ later_tac)
  \\ ntac 2 (fs [subst_def,Eval_eq,AllCaseEqs()] \\ rw [])
  \\ pop_assum mp_tac
  \\ drule Eval_cons
  \\ disch_then (once_rewrite_tac o single)
  \\ rpt strip_tac
  \\ asm_rewrite_tac [CONS_11]
  \\ metis_tac []
QED


(* Inlining of Let-expressions*)

Definition inline_let_def:
  inline_let p (Var v) = Var v ∧
  inline_let p (Const n) = Const n ∧
  inline_let p (Call d ys) = Call d (inline_lets p ys) ∧
  inline_let p (Op f ys) = Op f (inline_lets p ys) ∧
  inline_let p (If cmp xs y z) =
    If cmp (inline_lets p xs) (inline_let p y) (inline_let p z) ∧
  inline_let p (Let n y z) =
    (let y = inline_let p y in
     let z = inline_let p z in
       if p n then
         case subst n y z of
         | NONE => Let n y z
         | SOME res => res
       else Let n y z) ∧
  inline_lets p [] = [] ∧
  inline_lets p (y::ys) = inline_let p y :: inline_lets p ys
End

Theorem inline_let_thm:
  LFINITE s.input ⇒
  (env,[x],s) ---> ([v],s) ⇒
  ∀filter. (env,[inline_let filter x],s) ---> ([v],s)
Proof
  strip_tac \\ simp [PULL_FORALL] \\ gen_tac
  \\ qsuff_tac
    ‘∀x y.
       x ---> y ⇒ ∀env xs vs. x = (env,xs,s) ∧ y = (vs,s) ⇒
                              (env,inline_lets filter xs,s) ---> (vs,s)’
  THEN1 (rw [] \\ res_tac \\ fs [inline_let_def])
  \\ ho_match_mp_tac Eval_strongind
  \\ rw [] \\ fs [inline_let_def] \\ fs [Eval_eq]
  \\ later_tac \\ fs [inline_let_def]
  \\ TRY (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
  \\ fs [app_cases] \\ rw []
  \\ BasicProvers.every_case_tac \\ fs []
  \\ fs [Eval_eq]
  \\ TRY (goal_assum (first_assum o mp_then Any mp_tac) \\ fs [])
  \\ last_x_assum assume_tac
  \\ metis_tac [subst_thm]
QED


(* Misc *)

Theorem eval_op_mono:
  ∀f vs s res t. eval_op f vs s = (res,t) ⇒ s.output ≼ t.output
Proof
  fs [eval_op_def,AllCaseEqs(),fail_def,return_def] \\ rw [] \\ fs []
QED

Theorem eval_mono:
  (∀env x s r t. eval env x s = (r,t) ⇒ s.output ≼ t.output) ∧
  (∀env xs s r t. evals env xs s = (r,t) ⇒ s.output ≼ t.output)
Proof
  ho_match_mp_tac eval_ind \\ rw []
  \\ fs [eval_def,AllCaseEqs()] \\ rw []
  \\ res_tac \\ imp_res_tac eval_op_mono \\ fs []
  \\ imp_res_tac rich_listTheory.IS_PREFIX_TRANS \\ rfs []
  \\ fs [source_semanticsTheory.take_branch_def,fail_def,return_def,AllCaseEqs()]
  \\ fs [get_env_and_body_def,fail_def,return_def,AllCaseEqs()] \\ rw []
QED

Theorem evals_length:
  ∀xs env s args s1.
    evals env xs s = (Res args,s1) ⇒ LENGTH args = LENGTH xs
Proof
  Induct \\ fs [eval_def,AllCaseEqs()] \\ rw [] \\ res_tac \\ fs []
QED

Theorem Eval_length:
  ∀env xs s1 vs s2.
    (env,xs,s1) ---> (vs,s2) ⇒ LENGTH xs = LENGTH vs
Proof
  ho_match_mp_tac (Eval_ind
    |> Q.SPEC ‘λ(env,xs,s) (vs,s'). P env xs s vs s'’
    |> SIMP_RULE (srw_ss()) [FORALL_PROD] |> GEN_ALL) \\ fs []
QED

Theorem Eval_two:
  (env,[x1; x2],s1) ---> (vs,s2) =
  ∃v1 v2 s'.
    (env,[x1],s1) ---> ([v1],s') ∧
    (env,[x2],s') ---> ([v2],s2) ∧ vs = [v1;v2]
Proof
  eq_tac \\ rw [] THEN1
   (pop_assum mp_tac
    \\ simp [Once Eval_cases] \\ rw [] \\ fs [] \\ imp_res_tac Eval_length
    \\ fs [] \\ Cases_on ‘vs'’ \\ fs [] \\ rw [] \\ metis_tac [])
  \\ simp [Once Eval_cases] \\ rw [] \\ fs [] \\ metis_tac []
QED

Theorem eval_from_prefix:  (* required for divergence proof *)
  eval_from k1 input prog = (res1,t1) ∧
  eval_from k2 input prog = (res2,t2) ∧
  k1 ≤ k2 ⇒
  t1.output ≼ t2.output
Proof
  qsuff_tac
  ‘(∀env x s res1 t1 k.
      eval env x s = (res1,t1) ∧ k <= s.clock ⇒
      ∃res2 t2. eval env x (s with clock := k) = (res2,t2) ∧
                t2.output ≼ t1.output ∧
                (∀e. res1 = Err e ⇒ ∃e. res2 = Err e) ∧
                ∀x. res2 = Res x ⇒ res1 = Res x ∧
                    ∃k1. t2 = t1 with clock := k1 ∧ k1 ≤ t1.clock) ∧
   (∀env xs s res1 t1 k.
      evals env xs s = (res1,t1) ∧ k <= s.clock ⇒
      ∃res2 t2. evals env xs (s with clock := k) = (res2,t2) ∧
                t2.output ≼ t1.output ∧
                (∀e. res1 = Err e ⇒ ∃e. res2 = Err e) ∧
                ∀x. res2 = Res x ⇒ res1 = Res x ∧
                    ∃k1. t2 = t1 with clock := k1 ∧ k1 ≤ t1.clock)’
  THEN1
   (Cases_on ‘prog’ \\ fs [eval_from_def] \\ rw []
    \\ res_tac \\ fs [] \\ ntac 2 (first_x_assum mp_tac)
    \\ disch_then drule \\ fs [])
  \\ ho_match_mp_tac eval_ind \\ rw []
  THEN1 (fs [eval_def] \\ rw [] \\ fs [state_component_equality])
  THEN1 (fs [eval_def,AllCaseEqs()] \\ rw [] \\ fs [state_component_equality])
  THEN1
   (fs [eval_def,AllCaseEqs()] \\ rw []
    \\ res_tac \\ fs [] \\ rw []
    \\ reverse (Cases_on ‘res2’) \\ fs []
    \\ rw [] \\ fs []
    \\ imp_res_tac eval_op_mono \\ fs []
    \\ imp_res_tac rich_listTheory.IS_PREFIX_TRANS \\ rw []
    \\ last_x_assum drule \\ fs []
    \\ fs [state_component_equality]
    \\ fs [eval_op_def,AllCaseEqs(),fail_def,return_def]
    \\ rw [] \\ fs [])
  THEN1
   (fs [eval_def,AllCaseEqs()] \\ rw []
    \\ res_tac \\ fs [] \\ rw []
    \\ reverse (Cases_on ‘res2’) \\ fs []
    \\ imp_res_tac eval_mono \\ fs []
    \\ imp_res_tac rich_listTheory.IS_PREFIX_TRANS \\ rw [])
  THEN1
   (reverse (fs [eval_def,AllCaseEqs()]) \\ rw [] \\ fs []
    THEN1 (res_tac \\ fs [] \\ rw [])
    \\ first_x_assum drule \\ rw [] \\ fs []
    \\ reverse (Cases_on ‘res2’) \\ fs []
    \\ fs [take_branch_def,AllCaseEqs(),fail_def,return_def]
    \\ rw [] \\ fs []
    \\ imp_res_tac eval_mono \\ fs []
    \\ imp_res_tac rich_listTheory.IS_PREFIX_TRANS \\ rw [])
  THEN1
   (reverse (fs [eval_def,AllCaseEqs()]) \\ rw [] \\ fs []
    THEN1 (res_tac \\ fs [] \\ rw [])
    \\ first_x_assum drule \\ rw [] \\ fs []
    \\ reverse (Cases_on ‘res2’) \\ fs []
    \\ fs [get_env_and_body_def,AllCaseEqs(),fail_def,return_def]
    \\ rw [] \\ fs [env_and_body_def]
    \\ imp_res_tac eval_mono \\ fs []
    \\ imp_res_tac rich_listTheory.IS_PREFIX_TRANS \\ rw []
    \\ Cases_on ‘k1 = 0’ \\ fs [])
  THEN1 (fs [eval_def] \\ rw [] \\ fs [state_component_equality])
  \\ reverse (fs [eval_def,AllCaseEqs()]) \\ rw [] \\ fs []
  THEN1 (res_tac \\ fs [] \\ rw [])
  \\ first_x_assum drule \\ rw [] \\ fs []
  \\ reverse (Cases_on ‘res2’) \\ fs []
  \\ imp_res_tac eval_mono \\ fs []
  \\ imp_res_tac rich_listTheory.IS_PREFIX_TRANS \\ rw []
  \\ first_x_assum drule \\ rw [] \\ fs []
  \\ reverse (Cases_on ‘res2’) \\ fs []
  \\ imp_res_tac eval_mono \\ fs []
  \\ imp_res_tac rich_listTheory.IS_PREFIX_TRANS \\ rw []
  \\ fs [state_component_equality]
QED

Theorem eval_TimeOut_clock:
  (∀env x s t. eval env x s = (Err TimeOut,t) ⇒ t.clock = 0) ∧
  (∀env xs s t. evals env xs s = (Err TimeOut,t) ⇒ t.clock = 0)
Proof
  ho_match_mp_tac eval_ind \\ rw []
  \\ fs [eval_def,AllCaseEqs(),eval_op_def,return_def,fail_def,
         take_branch_def,get_env_and_body_def]
  \\ rw [] \\ fs []
QED

val _ = export_theory();
