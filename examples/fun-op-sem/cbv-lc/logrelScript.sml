(* Define a logical relation for the untyped call-by-value lambda calculus,
 * prove that it is reflexive, transitive, and sound wrt contextual
 * approximation *)


open HolKernel boolLib bossLib lcsymtacs Parse;
open integerTheory stringTheory alistTheory listTheory pred_setTheory;
open pairTheory optionTheory finite_mapTheory arithmeticTheory;
open cbvTheory;

val _ = set_trace "Goalstack.print_goal_at_top" 0;
val _ = ParseExtras.temp_tight_equality();

val _ = new_theory "logrel";

(* The logical relation *)

(* The boolean valued if-then-elses are there for HOL's termination condition
 * extractor, which doesn't work with an implication *)
val val_rel_def = tDefine "val_rel" `
(val_rel (i:num) (Litv l) (Litv l') ⇔ l = l') ∧
(val_rel i (Clos env e) (Clos env' e') ⇔
  !i' a a' s s'.
    if i' < i then
      state_rel i' s s' ∧
      val_rel i' a a' ⇒
      exec_rel i' (a::env, s, e) (a'::env', s', e')
    else
      T) ∧
(val_rel i _ _ = F) ∧
(exec_rel i (env, s, e) (env', s', e') ⇔
  !i'.
    if i' ≤ i then
      let (res1,s1) = sem env (s with clock := i') e in
      let (res2,s2) = sem env' (s' with clock := i') e' in
        case (res1, res2) of
           | (Rval v1, Rval v2) =>
               s1.clock = s2.clock ∧
               state_rel s1.clock s1 s2 ∧
               val_rel s1.clock v1 v2
           | (Rtimeout, Rtimeout) =>
               state_rel s1.clock s1 s2
           | (Rfail, _) => T
           | _ => F
    else
      T) ∧
(state_rel i s s' ⇔
  LIST_REL (val_rel i) s.store s'.store)`
(WF_REL_TAC `inv_image ($< LEX $<)
             (\x. case x of
                     | INL (i,v,v') => (i:num,0:num)
                     | INR (INL (i,st,st')) => (i,2)
                     | INR (INR (i,s,s')) => (i,1))` >>
 rw [] >>
 pop_assum (mp_tac o GSYM) >>
 rw [] >>
 `s1.clock ≤ (s with clock := i').clock` by metis_tac [sem_clock] >>
 fs [] >>
 decide_tac);

(* Related results *)
val res_rel_def = Define `
(res_rel (Rval v1, s1) (Rval v2, s2) ⇔
  s1.clock = s2.clock ∧
  state_rel s1.clock s1 s2 ∧
  val_rel s1.clock v1 v2) ∧
(res_rel (Rtimeout, s1) (Rtimeout, s2) ⇔
  state_rel s1.clock s1 s2) ∧
(res_rel (Rfail, _) _ ⇔ T) ∧
(res_rel _ _ ⇔ F)`;

val res_rel_rw = Q.store_thm ("res_rel_rw",
`(res_rel (Rval v, s) x ⇔
  ?v' s'. x = (Rval v', s') ∧ val_rel s.clock v v' ∧ state_rel s.clock s s' ∧ s.clock = s'.clock) ∧
 (res_rel (Rtimeout, s) x ⇔
   ?s'. x = (Rtimeout, s') ∧ state_rel s.clock s s') ∧
 (res_rel (Rfail, s) x ⇔ T)`,
 rw [] >>
 Cases_on `x` >>
 Cases_on `q` >>
 fs [res_rel_def] >>
 metis_tac []);

(* Related expressions *)
val exp_rel_def = Define `
exp_rel e e' ⇔
  !i env env' s s'.
    state_rel i s s' ∧
    LIST_REL (val_rel i) env env' ⇒
    exec_rel i (env, s, e) (env', s', e')`;

val val_rel_ind = theorem "val_rel_ind";

fun find_clause good_const =
  good_const o fst o strip_comb o fst o dest_eq o snd o strip_forall o concl;

val val_rel_rw =
  let val clauses = CONJUNCTS val_rel_def
      fun good_const x = same_const ``val_rel`` x
  in
    SIMP_RULE (srw_ss()) [AND_IMP_INTRO] (LIST_CONJ (List.filter (find_clause good_const) clauses))
  end;

val _ = save_thm ("val_rel_rw", val_rel_rw);

val state_rel_rw =
  let val clauses = CONJUNCTS val_rel_def
      fun good_const x = same_const ``state_rel`` x
  in
    SIMP_RULE (srw_ss()) [] (LIST_CONJ (List.filter (find_clause good_const) clauses))
  end;

val _ = save_thm ("state_rel_rw", state_rel_rw);

(* Convert the if-then-else to ⇒ *)
val val_rel_def = save_thm ("val_rel_def", SIMP_RULE (srw_ss()) [] val_rel_def)

(* Package up exec_rel nicely in terms of res_rel. *)
val exec_rel_rw = Q.store_thm ("exec_rel_rw",
`exec_rel i (env,s,e) (env',s',e') ⇔
  !i'. i' ≤ i ⇒
    res_rel (sem env (s with clock := i') e) (sem env' (s' with clock := i') e')`,
 srw_tac[] [val_rel_def] >>
 fsrw_tac[] [LET_THM] >>
 eq_tac >>
 fsrw_tac[] [] >>
 srw_tac[] []
 >- (Cases_on `sem env (s with clock := i') e` >>
     Cases_on `sem env' (s' with clock := i') e'` >>
     Cases_on `q` >>
     Cases_on `q'` >>
     simp [res_rel_def] >>
     res_tac >>
     fs [state_rel_rw])
 >- (first_x_assum (qspec_then `i'` mp_tac) >>
     rw [] >>
     Cases_on `res1` >>
     Cases_on `res2` >>
     rw [] >>
     fs [res_rel_def, state_rel_rw]));

(* Prove that the relation is monotonic in the index *)
val val_rel_mono = Q.store_thm ("val_rel_mono",
`(!i v v'. val_rel i v v' ⇒ ∀i'. i' ≤ i ⇒ val_rel i' v v') ∧
 (!i st st'. exec_rel i st st' ⇒ !i'. i' ≤ i ⇒ exec_rel i' st st') ∧
 (!i s s'. state_rel i s s' ⇒ !i'. i' ≤ i ⇒ state_rel i' s s')`,
 ho_match_mp_tac val_rel_ind >>
 srw_tac[] [val_rel_rw]
 >- (`i'' < i` by decide_tac >>
     metis_tac [])
 >- (fs [exec_rel_rw, LET_THM] >>
     rw [] >>
     `i'' ≤ i` by decide_tac >>
     metis_tac [])
 >- (fs [state_rel_rw, LIST_REL_EL_EQN] >>
     metis_tac [MEM_EL]));

val val_rel_mono_list = Q.store_thm ("val_rel_mono_list",
`!i i' vs1 vs2.
  i' ≤ i ∧ LIST_REL (\x y. val_rel i x y) vs1 vs2
  ⇒
  LIST_REL (\x y. val_rel i' x y) vs1 vs2`,
 rw [LIST_REL_EL_EQN] >>
 metis_tac [val_rel_mono]);

val val_rel_mono_list2 = Q.store_thm ("val_rel_mono_list2",
`!i i' vs1 vs2.
  i' ≤ i ∧ LIST_REL (val_rel i) vs1 vs2
  ⇒
  LIST_REL (val_rel i') vs1 vs2`,
 rw [LIST_REL_EL_EQN] >>
 metis_tac [val_rel_mono]);

(* Prove the fundamental theorem of the relation. *)

val compat_lit = Q.store_thm ("compat_lit",
`!l. exp_rel (Lit l) (Lit l)`,
 Cases_on `l` >>
 rw [exp_rel_def] >>
 rw [exec_rel_rw, sem_def] >>
 rw [res_rel_def, val_rel_rw] >>
 fs [state_rel_rw] >>
 `0 ≤ i''` by decide_tac >>
 metis_tac [val_rel_mono_list]);

val compat_var = Q.store_thm ("compat_var",
`!n. exp_rel (Var n) (Var n)`,
 rw [exp_rel_def, sem_def, exec_rel_rw] >>
 fs [LIST_REL_EL_EQN] >>
 rfs [] >>
 Cases_on `n < LENGTH env'` >>
 fs [] >>
 rw [val_rel_rw, res_rel_def]
 >- (fs [state_rel_rw] >>
     `0 ≤ i'` by decide_tac >>
     metis_tac [val_rel_mono_list])
 >- (`0 ≤ i'` by decide_tac >>
     metis_tac [MEM_EL, val_rel_mono]));

local val rw = srw_tac[] val fs = fsrw_tac[] in
val compat_app = Q.store_thm ("compat_app",
`!e1 e1' e2 e2'.
  exp_rel e1 e1' ∧
  exp_rel e2 e2'
  ⇒
  exp_rel (App e1 e2) (App e1' e2')`,
 rw [exp_rel_def, sem_def] >>
 `exec_rel i (env,s,e1) (env',s',e1')` by metis_tac [] >>
 pop_assum mp_tac >>
 REWRITE_TAC [exec_rel_rw, sem_def] >>
 rw [] >>
 `?s2 res2. sem env (s with clock := i') e1 = (res2,s2)` by metis_tac [pair_CASES] >>
 fs [] >>
 reverse (Cases_on `res2`) >>
 fs [res_rel_rw, sem_def] >>
 rw [] >>
 first_x_assum (qspec_then `i'` mp_tac) >>
 rw [LET_THM] >>
 `?s2' res2'. sem env' (s' with clock := i') e1' = (res2',s2')` by metis_tac [pair_CASES] >>
 fs []
 >- (Cases_on `res2'` >>
     fs [val_rel_rw, res_rel_rw]) >>
 fs [] >>
 Cases_on `res2'` >>
 fs [val_rel_rw, res_rel_rw] >>
 imp_res_tac sem_clock >>
 fs [] >>
 `s2.clock ≤ i` by decide_tac >>
 `exec_rel s2.clock (env,s2,e2) (env',s2',e2')` by metis_tac [val_rel_mono_list2] >>
 pop_assum mp_tac >>
 REWRITE_TAC [exec_rel_rw, LET_THM] >>
 rw [] >>
 first_x_assum (qspec_then `s2.clock` mp_tac) >>
 rw [] >>
 `?s3 res3. sem env s2 e2 = (res3,s3)` by metis_tac [pair_CASES] >>
 fs [] >>
 Cases_on `res3` >>
 fs [] >>
 rw [] >>
 fs [res_rel_rw] >>
 rw []
 >- (Cases_on `v` >>
     Cases_on `v'` >>
     fs [dec_clock_def, val_rel_rw, res_rel_rw, exec_rel_rw] >>
     fs [PULL_FORALL, AND_IMP_INTRO] >>
     first_x_assum match_mp_tac >>
     imp_res_tac sem_clock >>
     fs [] >>
     qexists_tac `s''.clock - 1` >>
     simp [] >>
     `s''.clock - 1 ≤ s''.clock` by decide_tac >>
     metis_tac [val_rel_mono])
 >- metis_tac []
 >- metis_tac []);
end

val compat_fn = Q.store_thm ("compat_fn",
`!e e'. exp_rel e e' ⇒ exp_rel (Fun e) (Fun e')`,
 rw [exp_rel_def, sem_def] >>
 rw [exec_rel_rw] >>
 fs [sem_def] >>
 rw [val_rel_rw, res_rel_def]
 >- (`state_rel i' s s'` by metis_tac [val_rel_mono] >>
     fs [state_rel_rw]) >>
 first_x_assum match_mp_tac >>
 rw [] >>
 `i'' ≤ i` by decide_tac >>
 metis_tac [val_rel_mono_list2]);

val compat_tick = Q.store_thm ("compat_tick",
`!e e'.
  exp_rel e e'
  ⇒
  exp_rel (Tick e) (Tick e')`,
 rw [exp_rel_def, sem_def] >>
 rw [exec_rel_rw] >>
 fs [sem_def] >>
 Cases_on `i' = 0` >>
 fs [] >>
 rw [res_rel_rw]
 >- (fs [state_rel_rw] >>
     `0 ≤ i` by decide_tac >>
     metis_tac [val_rel_mono_list]) >>
 res_tac >>
 pop_assum mp_tac >>
 REWRITE_TAC [exec_rel_rw] >>
 fs [dec_clock_def] >>
 rw [] >>
 pop_assum (qspec_then `i' - 1` mp_tac) >>
 `i' - 1 ≤ i` by decide_tac >>
 rw [LET_THM]);

val exp_rel_refl = Q.store_thm ("exp_rel_refl",
`!e. exp_rel e e`,
 Induct >>
 rw [] >>
 metis_tac [compat_lit, compat_var, compat_app, compat_fn, compat_tick]);

val val_rel_refl = Q.store_thm ("val_rel_refl",
`(!v. val_rel i v v) ∧
 (!vs. LIST_REL (val_rel i) vs vs)`,
 ho_match_mp_tac v_induction >>
 rw [val_rel_rw] >>
 `exp_rel e e` by metis_tac [exp_rel_refl] >>
 fs [exp_rel_def] >>
 first_x_assum match_mp_tac >>
 rw [] >>
 `i' ≤ i` by decide_tac >>
 metis_tac [val_rel_mono_list2]);

val state_rel_refl = Q.store_thm ("state_rel_refl",
`(!s. state_rel i s s)`,
 rw [state_rel_rw, LIST_REL_EL_EQN] >>
 metis_tac [val_rel_refl]);

(* Prove the relation sound *)

val ctxt_rel_def = Define `
ctxt_rel ctxt1 ctxt2 ⇔
  !e1 e2. exp_rel e1 e2 ⇒ exp_rel (ctxt_to_exp ctxt1 e1) (ctxt_to_exp ctxt2 e2)`;

val compat_hole = Q.prove (
`ctxt_rel Hole Hole`,
 rw [ctxt_rel_def, ctxt_to_exp_def]);

val compat_fnC = Q.prove (
`!ctxt1 ctxt2. ctxt_rel ctxt1 ctxt2 ⇒ ctxt_rel (FunC ctxt1) (FunC ctxt2)`,
 rw [ctxt_rel_def, ctxt_to_exp_def] >>
 metis_tac [compat_fn]);

val compat_app1C = Q.prove (
`!ctxt1 ctxt2 e. ctxt_rel ctxt1 ctxt2 ⇒ ctxt_rel (App1C ctxt1 e) (App1C ctxt2 e)`,
 rw [ctxt_rel_def, ctxt_to_exp_def] >>
 metis_tac [compat_app, exp_rel_refl]);

val compat_app2C = Q.prove (
`!ctxt1 ctxt2 e. ctxt_rel ctxt1 ctxt2 ⇒ ctxt_rel (App2C e ctxt1) (App2C e ctxt2)`,
 rw [ctxt_rel_def, ctxt_to_exp_def] >>
 metis_tac [compat_app, exp_rel_refl]);

val compat_tickC = Q.prove (
`!ctxt1 ctxt2. ctxt_rel ctxt1 ctxt2 ⇒ ctxt_rel (TickC ctxt1) (TickC ctxt2)`,
 rw [ctxt_rel_def, ctxt_to_exp_def] >>
 metis_tac [compat_tick, exp_rel_refl]);

val ctxt_rel_refl = Q.prove (
`!ctxt. ctxt_rel ctxt ctxt`,
 Induct_on `ctxt` >>
 rw [] >>
 metis_tac [compat_hole, compat_fnC, compat_app1C, compat_app2C, compat_tickC]);

val exp_rel_sound = Q.store_thm ("exp_rel_sound",
`!e1 e2. exp_rel e1 e2 ⇒ ctxt_approx e1 e2`,
 rw [ctxt_approx_def] >>
 qabbrev_tac `e1' = ctxt_to_exp ctxt e1` >>
 qabbrev_tac `e2' = ctxt_to_exp ctxt e2` >>
 `exp_rel e1' e2'` by metis_tac [ctxt_rel_def, ctxt_rel_refl] >>
 pop_assum mp_tac >>
 ntac 2 (pop_assum kall_tac) >>
 ntac 2 (pop_assum mp_tac) >>
 pop_assum kall_tac >>
 rw [] >>
 fs [exp_rel_def, exec_rel_rw] >>
 Cases_on `r1` >>
 fs [res_approx_def, eval_def]
 >- (`state_rel c <|clock := c; store := []|> <|clock := c; store := []|>`
            by rw [state_rel_rw] >>
     `LIST_REL (val_rel c) [] []` by rw [] >>
     res_tac >>
     fs [LET_THM] >>
     pop_assum (qspec_then `c` mp_tac) >>
     rw [] >>
     Cases_on `r2` >>
     fs [eval_def, val_rel_rw, res_approx_def] >>
     Cases_on `sem [] <|clock := c'; store := []|> e2'` >>
     Cases_on `q` >>
     fs [val_rel_rw, res_rel_rw]
     >- (`c ≤ c' ∨ c' ≤ c` by decide_tac
         >- (`c' = c + (c' - c)` by decide_tac >>
             metis_tac [PAIR_EQ, sem_clock_add, r_distinct])
         >- (`c = c' + (c - c')` by decide_tac >>
             metis_tac [PAIR_EQ, sem_clock_add_fail, r_distinct]))
     >- metis_tac [r_distinct, PAIR_EQ]
     >- (`c ≤ c' ∨ c' ≤ c` by decide_tac
         >- (`c' = c + (c' - c)` by decide_tac >>
             metis_tac [PAIR_EQ, sem_clock_add, r_distinct])
         >- (`c = c' + (c - c')` by decide_tac >>
             metis_tac [PAIR_EQ, sem_clock_add_fail, r_distinct]))
     >- metis_tac [r_distinct, PAIR_EQ])
 >- (Cases_on `r2` >>
     fs [eval_def, res_approx_def] >>
     `state_rel c <|clock := c; store := []|> <|clock := c; store := []|>`
            by rw [state_rel_rw] >>
     `LIST_REL (val_rel c) [] []` by rw [] >>
     res_tac >>
     fs [LET_THM] >>
     pop_assum (qspec_then `c` mp_tac) >>
     rw [] >>
     last_x_assum (qspec_then `c` assume_tac) >>
     fs [] >>
     rw [] >>
     CCONTR_TAC >>
     fs [] >>
     `s'.clock = 0` by metis_tac [sem_clock_timeout0] >>
     fs [] >>
     Cases_on `sem [] <|clock := c'; store := []|> e2'` >>
     Cases_on `q` >>
     fs [res_rel_rw]));

(* Prove transitivity *)

val lemma = Q.prove (
`(\(x,y). f x y) g ⇔ f (FST g) (SND g)`,
 eq_tac >>
 rw [] >>
 Cases_on `g` >>
 fs []);

local val rw = srw_tac[] val fs = fsrw_tac[] in
val exec_to_val = Q.prove (
`(!i. exec_rel i (env',s',e') (env'',s'',e'')) ∧
 sem env' (s' with clock := c') e' = (Rval v',r') ∧
 sem env'' (s'' with clock := c') e'' = (Rval v'',r'') ∧
 r'.clock = r''.clock
 ⇒
 (!i. val_rel i v' v'')`,
 rw [exec_rel_rw] >>
 first_x_assum (qspecl_then [`c' + i`, `c' + i`] mp_tac) >>
 rw [LET_THM] >>
 `sem env' (s' with clock := c' + i) e' = (Rval v', r' with clock := r'.clock + i)`
                 by metis_tac [sem_clock_add] >>
 fs [res_rel_rw] >>
 `i ≤ r'.clock + i` by decide_tac >>
 metis_tac [sem_clock_val_determ, val_rel_mono]);
end

val exec_to_state = Q.prove (
`(!i. exec_rel i (env',s',e') (env'',s'',e'')) ∧
 sem env' (s' with clock := c') e' = (Rval v',r') ∧
 sem env'' (s'' with clock := c') e'' = (Rval v'',r'') ∧
 r'.clock = r''.clock
 ⇒
 (!i. state_rel i r' r'')`,
 rw [exec_rel_rw] >>
 first_x_assum (qspecl_then [`c' + i`, `c' + i`] mp_tac) >>
 rw [LET_THM] >>
 `sem env' (s' with clock := c' + i) e' = (Rval v', r' with clock := r'.clock + i)` by metis_tac [sem_clock_add] >>
 fs [] >>
 fs [state_rel_rw, res_rel_rw] >>
 imp_res_tac sem_clock_val_determ >>
 fs [state_component_equality] >>
 `i ≤ s'''.clock` by decide_tac >>
 metis_tac [val_rel_mono_list]);

val val_trans_0 = Q.prove (
`val_rel 0 v1 v2 ∧ val_rel 0 v2 v3 ⇒ val_rel 0 v1 v3`,
 Cases_on `v1` >>
 Cases_on `v2` >>
 Cases_on `v3` >>
 rw [val_rel_rw]);

val state_trans_0 = Q.prove (
`state_rel 0 s1 s2 ∧ state_rel 0 s2 s3 ⇒ state_rel 0 s1 s3`,
 rw [state_rel_rw, LIST_REL_EL_EQN] >>
 metis_tac [val_trans_0]);

val val_rel_trans = Q.store_thm ("val_rel_trans",
`(!i v1 v2. val_rel i v1 v2 ⇒ !v3. (!i'. val_rel i' v2 v3) ⇒ val_rel i v1 v3) ∧
 (!i st1 st2. exec_rel i st1 st2 ⇒ !st3. (!i'. exec_rel i' st2 st3) ⇒ exec_rel i st1 st3) ∧
 (!i s1 s2. state_rel i s1 s2 ⇒ !s3. (!i'. state_rel i' s2 s3) ⇒ state_rel i s1 s3)`,
 ho_match_mp_tac val_rel_ind >>
 rw [val_rel_rw]
 >- (Cases_on `v3` >>
     fs [val_rel_rw] >>
     rw [] >>
     fs [PULL_FORALL, AND_IMP_INTRO] >>
     first_x_assum match_mp_tac >>
     qexists_tac `s'` >>
     qexists_tac `a'` >>
     rw [] >>
     first_x_assum match_mp_tac >>
     rw [] >>
     qexists_tac `i'' + 1` >>
     simp [] >>
     metis_tac [val_rel_refl, state_rel_refl])
 >- (`?env'' s'' e''. st3 = (env'',s'',e'')` by metis_tac [pair_CASES] >>
     rw [exec_rel_rw, LET_THM] >>
     Cases_on `sem env (s with clock := i') e` >>
     rw [] >>
     Cases_on `q` >>
     rw [res_rel_rw]
     >- (qpat_assum `exec_rel i' (env,s,e) (env',s',e')` mp_tac >>
         rw [exec_rel_rw] >>
         pop_assum (qspec_then `i'` mp_tac) >>
         rw [LET_THM] >>
         Cases_on `sem env' (s' with clock := i') e'` >>
         Cases_on `q` >>
         fs [] >>
         `exec_rel i' (env',s',e') (env'',s'',e'')` by metis_tac [] >>
         pop_assum mp_tac >>
         REWRITE_TAC [exec_rel_rw] >>
         rw [] >>
         pop_assum (qspec_then `i'` mp_tac) >>
         rw [LET_THM] >>
         rfs [res_rel_rw] >>
         fs [] >>
         Cases_on `sem env'' (s'' with clock := i') e''` >>
         fs [] >>
         rfs [] >>
         `!i. val_rel i v' v''` by metis_tac [exec_to_val] >>
         `!i. state_rel i r' r''` by metis_tac [exec_to_state] >>
         metis_tac [])
     >- (qpat_assum `exec_rel i (env,s,e) (env',s',e')` mp_tac >>
         rw [exec_rel_rw] >>
         pop_assum (qspec_then `i'` mp_tac) >>
         rw [LET_THM] >>
         Cases_on `sem env' (s' with clock := i') e'` >>
         Cases_on `q` >>
         fs [res_rel_rw] >>
         `exec_rel i' (env',s',e') (env'',s'',e'')` by metis_tac [] >>
         pop_assum mp_tac >>
         REWRITE_TAC [exec_rel_rw] >>
         rw [] >>
         pop_assum (qspec_then `i'` mp_tac) >>
         rw [LET_THM] >>
         rfs [] >>
         fs [] >>
         imp_res_tac sem_clock_timeout0 >>
         fs [res_rel_rw] >>
         metis_tac [state_trans_0]))
 >- (fs [state_rel_rw, LIST_REL_EL_EQN] >>
     metis_tac [MEM_EL]));

val exp_rel_trans = Q.store_thm ("exp_rel_trans",
`!e1 e2 e3. exp_rel e1 e2 ∧ exp_rel e2 e3 ⇒ exp_rel e1 e3`,
 rw [exp_rel_def] >>
 `!i. state_rel i s' s' ∧ LIST_REL (val_rel i) env' env'` by metis_tac [val_rel_refl, state_rel_refl] >>
 metis_tac [val_rel_trans]);

val exp_refl_sem = Q.store_thm ("exp_refl_sem",
`!e i s1 s2 env1 env2 v v' s1' s2'.
  state_rel s1.clock s1 s2 ∧
  LIST_REL (val_rel s1.clock) env1 env2 ∧
  sem env1 s1 e = (Rval v,s1') ∧
  sem env2 s2 e = (Rval v',s2')
  ⇒
  val_rel s1'.clock v v' ∧
  state_rel s1'.clock s1' s2'`,
 rpt gen_tac >>
 DISCH_TAC >>
 fs [] >>
 `exp_rel e e` by metis_tac [exp_rel_refl] >>
 fs [exp_rel_def, exec_rel_rw] >>
 res_tac >>
 pop_assum mp_tac >>
 pop_assum kall_tac >>
 DISCH_TAC >>
 pop_assum (qspec_then `s1.clock` assume_tac) >>
 fs [LET_THM] >>
 Cases_on `sem env1 s1 e` >>
 Cases_on `q` >>
 fs [res_rel_rw] >>
 rfs [] >>
 `s2 = s2 with clock := s2.clock` by rw [] >>
 `v''' = v' ∧ s2' = s' with clock := s2'.clock`
         by metis_tac [sem_clock_val_determ, PAIR_EQ, r_11] >>
 fs [state_component_equality, state_rel_rw]);

val res_rel_trans = Q.store_thm ("res_rel_trans",
`!r1 r2 r3 s1 s2 s3.
  res_rel (r1,s1) (r2,s2) ∧
  (!c. res_rel (r2,s2 with clock := c) (r3,s3 with clock := c)) ∧
  s2.clock = s3.clock
  ⇒
  res_rel (r1,s1) (r3,s3)`,
 rw [] >>
 Cases_on `r1` >>
 fs [res_rel_rw] >>
 rw [] >>
 fs [res_rel_rw] >>
 Cases_on `r3` >>
 fs [] >>
 `!c. state_rel c s2 s3` by fs [state_rel_rw] >>
 metis_tac [val_rel_trans]);

val res_rel_trans_lemma = Q.prove (
`!st1 st2 st3.
  res_rel st1 st2 ∧
  (!c. res_rel (FST st2, SND st2 with clock := c) (FST st3, SND st3 with clock := c)) ∧
  (SND st2).clock = (SND st3).clock
  ⇒
  res_rel st1 st3`,
 Cases_on `st1` >>
 Cases_on `st2` >>
 Cases_on `st3` >>
 rw [] >>
 metis_tac [res_rel_trans]);

val res_rel_trans_val = Q.store_thm ("res_rel_trans_val",
`∀c v s1 s2 s3 e1 e2 env e env' e'.
  res_rel (Rval v, s1 with clock := c) (sem env (s2 with clock := c) e) ∧
  (!c. res_rel (sem env (s2 with clock := c) e) (sem env' (s3 with clock := c) e'))
  ⇒
  res_rel (Rval v,s1 with clock := c) (sem env' (s3 with clock := c) e')`,
 rw [] >>
 match_mp_tac res_rel_trans_lemma >>
 qexists_tac `sem env (s2 with clock := c) e` >>
 reverse (rw [])
 >- (pop_assum (qspec_then `c` mp_tac) >>
     fs [res_rel_rw] >>
     rw [] >>
     rw []) >>
 Cases_on `c' ≤ c`
 >- (first_x_assum (qspec_then `c` mp_tac) >>
     fs [res_rel_rw] >>
     simp [] >>
     fs [state_rel_rw] >>
     rw [] >>
     rw [] >>
     metis_tac [val_rel_mono, val_rel_mono_list]) >>
 fs [res_rel_rw] >>
 rw [] >>
 first_x_assum (fn th' => qspec_then `s'.clock` (fn th => assume_tac th THEN assume_tac th') th') >>
 pop_assum (qspec_then `c'` assume_tac) >>
 rfs [res_rel_rw] >>
 imp_res_tac sem_clock_add >>
 pop_assum (qspec_then `c' - s'.clock` mp_tac) >>
 pop_assum (qspec_then `c' - s'.clock` mp_tac) >>
 DISCH_TAC >>
 DISCH_TAC >>
 rev_full_simp_tac (srw_ss()++ARITH_ss) [] >>
 fs [res_rel_rw]);

val _ = export_theory();
