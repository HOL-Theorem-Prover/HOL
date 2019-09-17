(* Use the logical relation to verify an optimisation that does beta-value
 * reduction on all beta-value reducable sub-terms. *)

open HolKernel boolLib bossLib lcsymtacs Parse;
open integerTheory stringTheory alistTheory listTheory pred_setTheory;
open pairTheory optionTheory finite_mapTheory arithmeticTheory;
open rich_listTheory;
open cbvTheory logrelTheory;

val _ = new_theory "opt";

val funpow_comm = Q.prove (
`!f n x. f (FUNPOW f n x) = FUNPOW f n (f x)`,
 Induct_on `n` >>
 rw [FUNPOW]);

val eta_lem = Q.prove (
`!f x. (\a b. f x a b) = f x`,
 rw [FUN_EQ_THM]);

val wf_lem = Q.prove (
`WF (($< :(num->num->bool)) LEX measure exp_size)`,
rw [] >>
match_mp_tac WF_LEX >>
rw [prim_recTheory.WF_LESS]);

val ind = SIMP_RULE (srw_ss()) [FORALL_PROD, wf_lem] (Q.ISPEC `(($< :(num->num->bool)) LEX
measure exp_size)` relationTheory.WF_INDUCTION_THM)

val val_rel_ind = Q.prove (
`∀P.
  (∀c e.
     (∀c' e'.
        (($< :num->num->bool) LEX measure exp_size) (c',e') (c,e) ⇒
        P c' e') ⇒
     P c e) ⇒
  ∀c e. P c e`,
 rw [] >>
 assume_tac (Q.SPEC `(\(x,y). P x y)` ind) >>
 fs [] >>
 metis_tac []);

(* Define substitution *)

val shift_def = Define `
(shift skip (Lit l) = Lit l) ∧
(shift skip (Var n) =
  if n < skip then
    Var n
  else
    Var (n + 1)) ∧
(shift skip (Fun e) = Fun (shift (skip + 1) e)) ∧
(shift skip (App e1 e2) = App (shift skip e1) (shift skip e2)) ∧
(shift skip (Tick e) = Tick (shift skip e))`;

val subst_def = Define `
(subst skip e2 (Lit l) = Lit l) ∧
(subst skip e2 (Var n) =
  if n < skip then
    Var n
  else if n = skip then
    e2
 else
    Var (n - 1)) ∧
(subst skip e2 (Fun e1) = Fun (subst (skip + 1) (shift 0 e2) e1)) ∧
(subst skip e2 (App e1 e1') = App (subst skip e2 e1) (subst skip e2 e1')) ∧
(subst skip e2 (Tick e1) = Tick (subst skip e2 e1))`;

val is_val_def = Define `
(is_val (Lit l) ⇔ T) ∧
(is_val (Fun e) ⇔ T) ∧
(is_val (Var n) ⇔ T) ∧
(is_val _ ⇔ F)`;

(* Walk a term and convert all beta-value redexes *)
val betaV_reduce_def = Define `
(betaV_reduce (Lit l) ⇔ Lit l) ∧
(betaV_reduce (Var n) ⇔ Var n) ∧
(betaV_reduce (Fun e) ⇔ Fun (betaV_reduce e)) ∧
(betaV_reduce (App (Fun e1) e2) ⇔
  if is_val (betaV_reduce e2) then
    Tick (subst 0 (betaV_reduce e2) (betaV_reduce e1))
  else
    App (Fun (betaV_reduce e1)) (betaV_reduce e2)) ∧
(betaV_reduce (App e1 e2) ⇔ App (betaV_reduce e1) (betaV_reduce e2)) ∧
(betaV_reduce (Tick e) ⇔ Tick (betaV_reduce e))`;

(* The proof *)

val is_val_sem = Q.prove (
`!e. is_val e ⇒
  (?v. !s. sem env s e = (Rval v, s)) ∨
  (?n. !s. sem env s e = (Rfail, s) ∧ e = Var n ∧ LENGTH env ≤ n)`,
 Cases_on `e` >>
 rw [is_val_def, sem_def] >>
 Cases_on `n < LENGTH env` >>
 fs [] >>
 decide_tac);

val is_val_shift = Q.prove (
`!n e . is_val e ⇒ is_val (shift n e)`,
 Induct_on `e` >>
 rw [is_val_def, shift_def]);

val sem_0_to_c = Q.prove (
`!env1 s1 e2 v s2.
 sem env1 (s1 with clock := 0) e2 = (Rval v,s2)
 ⇒
 sem env1 (s1 with clock := c) e2 = (Rval v,s2 with clock := s2.clock + c)`,
 rw [] >>
 `sem env1 (s1 with clock := 0 + c) e2 = (Rval v,s2 with clock := s2.clock + c)` by metis_tac [sem_clock_add] >>
 fs []);

val shift_lemma = Q.prove (
`!c e env1 env2 s1 s2 vs1 vs2 v.
  LIST_REL (val_rel c) vs1 vs2 ∧
  LIST_REL (val_rel c) env1 env2 ∧
  state_rel c s1 s2
  ⇒
  res_rel (sem (vs1++env1) (s1 with clock := c) e) (sem (vs2++[v]++env2) (s2 with clock := c) (shift (LENGTH vs1) e))`,
 ho_match_mp_tac val_rel_ind >>
 rw [] >>
 Cases_on `e`
 >- (fs [shift_def, sem_def, res_rel_rw] >>
     fs [state_rel_rw, val_rel_refl])
 >- (fs [shift_def, sem_def, res_rel_rw] >>
     rw [res_rel_rw, sem_def] >>
     rw [] >>
     imp_res_tac LIST_REL_LENGTH
     >- (simp [EL_APPEND1, GSYM APPEND_ASSOC] >>
         fs [LIST_REL_EL_EQN])
     >- fs [state_rel_rw]
     >- decide_tac
     >- (`LENGTH vs1 ≤ n ∧ LENGTH vs2 ≤ n + 1` by decide_tac >>
         RW_TAC (std_ss) [EL_APPEND2, GSYM APPEND_ASSOC] >>
         simp [EL_CONS, GSYM ADD1] >>
         `PRE (SUC n − LENGTH vs2) = n - LENGTH vs2` by decide_tac >>
         simp [] >>
         fs [LIST_REL_EL_EQN] >>
         `n − LENGTH vs2 < LENGTH env2` by decide_tac >>
         metis_tac [])
     >- fs [state_rel_rw]
     >- decide_tac)
 >- (fs [sem_def] >>
     rw [sem_def, shift_def, res_rel_rw, val_rel_refl] >>
     last_assum (qspecl_then [`c`, `e'`] mp_tac) >>
     REWRITE_TAC [LEX_DEF_THM, exp_size_def] >>
     simp [exp_size_def] >>
     rw [] >>
     pop_assum (qspecl_then [`env1`, `env2`, `s1`, `s2`, `vs1`, `vs2`, `v`] mp_tac) >>
     rw [] >>
     Cases_on `sem (vs1 ++ env1) (s1 with clock := c) e'` >>
     fs [] >>
     Cases_on `q` >>
     fs [] >>
     rw [] >>
     fs [res_rel_rw] >>
     imp_res_tac sem_clock >>
     fs [] >>
     last_assum (qspecl_then [`r.clock`, `e0`] mp_tac) >>
     REWRITE_TAC [LEX_DEF_THM] >>
     simp [exp_size_def] >>
     rw [] >>
     pop_assum (qspecl_then [`env1`, `env2`, `r`, `s'`, `vs1`, `vs2`, `v`] mp_tac) >>
     imp_res_tac val_rel_mono_list2 >>
     simp [val_rel_mono, val_rel_mono_list2] >>
     rw [] >>
     Cases_on `sem (vs1 ++ env1) (r with clock := s'.clock) e0` >>
     fs [] >>
     reverse (Cases_on `q`) >>
     fs [] >>
     rw [] >>
     fs [res_rel_rw] >>
     `(r with clock := s'.clock) = r` by rw [state_component_equality] >>
     fs [res_rel_rw] >>
     Cases_on `s''.clock = 0` >>
     fs [] >>
     rw [res_rel_rw] >>
     fs [] >>
     Cases_on `v'` >>
     fs [] >>
     rw [res_rel_rw] >>
     imp_res_tac sem_clock >>
     fs [dec_clock_def] >>
     imp_res_tac sem_clock_add >>
     rw [] >>
     Cases_on `v''` >>
     fs [val_rel_rw, exec_rel_rw, LET_THM, PULL_FORALL] >>
     first_x_assum (qspecl_then [`s''.clock - 1`, `v'''`, `v''''`, `r'`, `s''`, `s''.clock - 1`] mp_tac) >>
     `s''.clock - 1 ≤ s''.clock` by decide_tac >>
     imp_res_tac val_rel_mono >>
     simp [])
 >- (fs [sem_def] >>
     rw [sem_def, shift_def, res_rel_def, val_rel_refl]
     >- fs [state_rel_rw] >>
     rw [val_rel_rw, exec_rel_rw] >>
     Cases_on `sem (a::(vs1 ++ env1)) (s with clock := i'') e'` >>
     last_x_assum (qspecl_then [`i''`, `e'`] mp_tac) >>
     simp [LEX_DEF_THM] >>
     rw [] >>
     pop_assum (qspecl_then [`env1`, `env2`, `s`, `s'`, `a::vs1`, `a'::vs2`, `v`] mp_tac) >>
     simp [] >>
     rw [] >>
     `i'' ≤ c` by decide_tac >>
     imp_res_tac val_rel_mono >>
     imp_res_tac val_rel_mono_list2 >>
     imp_res_tac is_val_shift >>
     fs [ADD1])
 >- (fs [sem_def] >>
     rw [sem_def, shift_def, res_rel_def, val_rel_refl]
     >- (fs [dec_clock_def] >>
         last_x_assum (qspecl_then [`c-1`, `e'`] mp_tac) >>
         simp [LEX_DEF_THM] >>
         rw [] >>
         pop_assum (qspecl_then [`env1`, `env2`, `s1`, `s2`, `vs1`, `vs2`, `v`] mp_tac) >>
         simp [] >>
         rw [] >>
         `c-1 ≤ c` by decide_tac >>
         imp_res_tac val_rel_mono >>
         imp_res_tac val_rel_mono_list2 >>
         fs [ADD1])
     >- fs [state_rel_rw]));

val shift_lemma0 = Q.prove (
`!c e env1 env2 s1 s2 v.
  LIST_REL (val_rel c) env1 env2 ∧
  state_rel c s1 s2
  ⇒
  res_rel (sem env1 (s1 with clock := c) e) (sem (v::env2) (s2 with clock := c) (shift 0 e))`,
 metis_tac [shift_lemma, APPEND, LENGTH, LIST_REL_rules]);

val shiftN_lemma = Q.prove (
`∀e env1 env2 v s1 s2 vs1 vs2 v' c.
  LIST_REL (val_rel c) env1 env2 ∧
  LIST_REL (val_rel c) vs1 vs2 ∧
  state_rel c s1 s2 ∧
  (∀s. sem env1 s e = (Rval v,s)) ∧
  is_val e
  ⇒
  res_rel (Rval v, s1 with clock := c) (sem (vs2++env2) (s2 with clock := c) (FUNPOW (shift 0) (LENGTH vs2) e))`,
 Induct_on `vs1` >>
 rw []
 >- (imp_res_tac is_val_sem >>
     pop_assum (qspec_then `env2` mp_tac) >>
     rw [] >>
     pop_assum (qspec_then `s2 with clock := c` mp_tac) >>
     first_x_assum (qspec_then `s1 with clock := c` mp_tac) >>
     rw [] >>
     fs [sem_def]
     >- (imp_res_tac exp_refl_sem >>
         fs [] >>
         rfs [state_rel_rw, res_rel_rw])
     >- (imp_res_tac LIST_REL_LENGTH >>
         fs [] >>
         BasicProvers.EVERY_CASE_TAC >>
         fs []))
 >- (fs [] >>
     fs [FUNPOW, GSYM funpow_comm] >>
     qabbrev_tac `e' = FUNPOW (shift 0) (LENGTH ys) e` >>
     qabbrev_tac `env' = ys++env2` >>
     `res_rel (Rval v,s1 with clock := c) (sem env' (s2 with clock := c) e')`
            by metis_tac [] >>
     `!c. res_rel (sem env' (s2 with clock := c) e') (sem (y::env') (s2 with clock := c) (shift 0 e'))`
                   by (rw [] >>
                       match_mp_tac shift_lemma0 >>
                       rw [val_rel_refl, state_rel_rw, eta_lem]) >>
     metis_tac [res_rel_trans_val]));

val subst_lemma = Q.prove (
`!c e1 e2 env1 env2 s1 s2 v vs1 vs2 r s1'.
  is_val e2 ∧
  LIST_REL (val_rel c) env1 env2 ∧
  LIST_REL (val_rel c) vs1 vs2 ∧
  state_rel c s1 s2 ∧
  sem (vs1++[v]++env1) (s1 with clock := c) e1 = (r, s1') ∧
  (∀s. sem env1 s e2 = (Rval v,s))
  ⇒
  res_rel (r,s1') (sem (vs2++env2) (s2 with clock := c) (subst (LENGTH vs1) (FUNPOW (shift 0) (LENGTH vs1) e2) e1))`,
 ho_match_mp_tac val_rel_ind >>
 rw [] >>
 Cases_on `e1`
 >- (fs [sem_def] >>
     rw [sem_def, subst_def, res_rel_rw, val_rel_refl] >>
     fs [state_rel_rw])
 >- (fs [sem_def] >>
     rw [sem_def, subst_def, res_rel_rw, val_rel_refl] >>
     imp_res_tac LIST_REL_LENGTH >>
     fs [] >> rw [] >>
     fs[] >> rw[] >>
     full_simp_tac (srw_ss()++ARITH_ss) [EL_APPEND1, EL_APPEND2] >>
     rw [res_rel_rw]
     >- fs [LIST_REL_EL_EQN]
     >- fs [state_rel_rw]
     >- (assume_tac shiftN_lemma >>
         fs [res_rel_rw] >>
         pop_assum match_mp_tac >>
         metis_tac [])
     >- (fs [LIST_REL_EL_EQN] >>
         `n − (LENGTH vs2 + 1) < LENGTH env2` by decide_tac >>
         metis_tac [])
     >- fs [state_rel_rw]
     )
 >- (fs [sem_def] >>
     rw [sem_def, subst_def, res_rel_rw, val_rel_refl] >>
     last_assum (qspecl_then [`c`, `e`] mp_tac) >>
     simp [LEX_DEF_THM, exp_size_def] >>
     rw [] >>
     pop_assum (qspecl_then [`e2`, `env1`, `env2`, `s1`, `s2`, `v`, `vs1`, `vs2`] mp_tac) >>
     rw [] >>
     Cases_on `sem (vs1 ++ [v] ++ env1) (s1 with clock := c) e` >>
     fs [] >>
     Cases_on `q` >>
     fs [] >>
     rw [] >>
     fs [res_rel_rw] >>
     imp_res_tac sem_clock >>
     fs [] >>
     last_assum (qspecl_then [`r'.clock`, `e0`] mp_tac) >>
     simp [LEX_DEF_THM, exp_size_def] >>
     rw [] >>
     pop_assum (qspecl_then [`e2`, `env1`, `env2`, `r'`, `s'`, `v`, `vs1`, `vs2`] mp_tac) >>
     imp_res_tac val_rel_mono_list2 >>
     simp [val_rel_mono, val_rel_mono_list2] >>
     rw [] >>
     Cases_on `sem (vs1 ++ [v] ++ env1) r' e0` >>
     fs [] >>
     reverse (Cases_on `q`) >>
     fs [] >>
     rw [] >>
     fs [res_rel_rw] >>
     `(r' with clock := s'.clock) = r'` by rw [state_component_equality] >>
     fs [res_rel_rw] >>
     Cases_on `r''.clock = 0` >>
     fs [] >>
     rw [res_rel_rw] >>
     fs [] >>
     Cases_on `v'` >>
     fs [] >>
     rw [res_rel_rw] >>
     imp_res_tac sem_clock >>
     fs [dec_clock_def] >>
     imp_res_tac sem_clock_add >>
     pop_assum (qspec_then `0` mp_tac) >>
     simp [] >>
     pop_assum (qspec_then `0` mp_tac) >>
     simp [] >>
     rw [] >>
     Cases_on `v''` >>
     fs [val_rel_rw, exec_rel_rw, LET_THM, PULL_FORALL] >>
     first_x_assum (qspecl_then [`r''.clock - 1`, `v'''`, `v''''`, `r''`, `s''`, `r''.clock - 1`] mp_tac) >>
     `r''.clock - 1 ≤ r''.clock` by decide_tac >>
     imp_res_tac val_rel_mono >>
     simp [])
 >- (fs [sem_def] >>
     rw [sem_def, subst_def, res_rel_def, val_rel_refl]
     >- (fs [state_rel_rw] >>
         `c ≤ i` by decide_tac >>
         metis_tac [val_rel_mono_list]) >>
     rw [val_rel_rw, exec_rel_rw] >>
     Cases_on `sem (a::(vs1 ++ [v] ++ env1)) (s with clock := i'') e` >>
     last_x_assum (qspecl_then [`i''`, `e`] mp_tac) >>
     simp [LEX_DEF_THM] >>
     rw [] >>
     pop_assum (qspecl_then [`e2`, `env1`, `env2`, `s`, `s'`, `v`, `a::vs1`, `a'::vs2`, `q`, `r`] mp_tac) >>
     simp [] >>
     rw [] >>
     `i'' ≤ c` by decide_tac >>
     imp_res_tac val_rel_mono >>
     imp_res_tac val_rel_mono_list2 >>
     imp_res_tac is_val_shift >>
     fs [ADD1] >>
     fs [FUNPOW_ADD, funpow_comm])
 >- (fs [sem_def] >>
     rw [sem_def, subst_def, res_rel_def, val_rel_refl]
     >- (`c ≠ 0` by decide_tac >>
         fs [dec_clock_def] >>
         last_x_assum (qspecl_then [`c-1`, `e`] mp_tac) >>
         simp [LEX_DEF_THM] >>
         rw [] >>
         pop_assum (qspecl_then [`e2`, `env1`, `env2`, `s1`, `s2`, `v`, `vs1`, `vs2`, `r`, `s1'`] mp_tac) >>
         simp [] >>
         rw [] >>
         `c-1 ≤ c` by decide_tac >>
         imp_res_tac val_rel_mono >>
         imp_res_tac val_rel_mono_list2 >>
         fs [ADD1])
     >- (Cases_on `c = 0` >>
         fs [] >>
         rw [res_rel_def] >>
         fs [state_rel_rw, dec_clock_def] >>
         imp_res_tac sem_clock >>
         fs [] >>
         decide_tac)));

val subst_correct = Q.store_thm ("subst_correct",
`!e2 e1. is_val e2 ⇒ exp_rel (App (Fun e1) e2) (Tick (subst 0 e2 e1))`,
 rw [exp_rel_def, exec_rel_rw] >>
 fs [sem_def] >>
 imp_res_tac is_val_sem >>
 pop_assum (qspecl_then [`env`] assume_tac) >>
 fs [] >>
 fs [sem_def]
 >- (Cases_on `i'=0` >>
     fs [] >>
     rw [res_rel_rw]
     >- (fs [state_rel_rw] >>
         `0 ≤ i` by decide_tac >>
         metis_tac [val_rel_mono_list]) >>
     fs [dec_clock_def] >>
     rw [] >>
     `?c. i' = c + 1` by (qexists_tac `i' - 1` >> decide_tac) >>
     fs [] >>
     rw [] >>
     `c ≤ i` by decide_tac >>
     Cases_on `sem (v::env) (s with clock := c) e1` >>
     assume_tac subst_lemma >>
     pop_assum (qspecl_then [`c`, `e1`, `e2`, `env`, `env'`, `s`, `s'`, `v`, `[]`, `[]`] mp_tac) >>
     fs [] >>
     rw [] >>
     pop_assum match_mp_tac >>
     metis_tac [val_rel_mono, val_rel_mono_list2])
 >- rw [res_rel_def]);

val beta_reduce_correct = Q.store_thm ("beta_reduce_correct",
`!e. exp_rel e (betaV_reduce e)`,
 ho_match_mp_tac (theorem "betaV_reduce_ind") >>
 rw [betaV_reduce_def] >>
 rw [exp_rel_refl]
 >- metis_tac [compat_fn]
 >- metis_tac [compat_app, subst_correct, exp_rel_trans, compat_fn]
 >- metis_tac [compat_app, compat_fn]
 >- metis_tac [compat_app]
 >- metis_tac [compat_app]
 >- metis_tac [compat_app]
 >- metis_tac [compat_app]
 >- metis_tac [compat_tick]);

val _ = export_theory ();
