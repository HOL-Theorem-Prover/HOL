open HolKernel boolLib bossLib lcsymtacs Parse;
open integerTheory stringTheory alistTheory listTheory rich_listTheory llistTheory pred_setTheory relationTheory;
open pairTheory optionTheory finite_mapTheory arithmeticTheory pathTheory;
open path_auxTheory simple_traceTheory lprefix_lubTheory;
open for_ndTheory;

val _ = set_trace "Goalstack.print_goal_at_top" 0;
val _ = ParseExtras.temp_tight_equality();

val _ = new_theory "oracleSem";

val lfilter_map_thm = Q.store_thm ("lfilter_map_thm",
`(lfilter_map f [||] = [||]) ∧
 (lfilter_map f (x:::l) =
   case f x of
   | NONE => lfilter_map f l
   | SOME y => y:::lfilter_map f l)`,
 rw [lfilter_map_def] >>
 every_case_tac >>
 fs []);

 (*
val _ = Datatype `
  io_result =
  | Terminate ('a list)
  | Diverge ('a llist)
  | Crash`;
  *)

val _ = type_abbrev ("oracle", ``:num -> 'st -> 'v -> 'st # 'v``);

val _ = Datatype `
  fbs_res =
    Timeout
  | Error
  | Val 'a`;

val _ = Datatype `
  ofbs = <| eval : 'st -> 'env -> 'prog -> 'st # 'v fbs_res;
            init_st : 'o -> 'st;
            init_env : 'env;
            set_clock : num -> 'st -> 'st;
            get_clock : 'st -> num;
            get_oracle_events : 'st -> 'a list |>`;

val eval_with_clock_def = Define `
  eval_with_clock sem c st p =
    sem.eval (sem.set_clock c st) sem.init_env p`;

val ofbs_sem_def = Define `
  (ofbs_sem sem p (Terminate io_list) ⇔
    ?oracle k st r.
      eval_with_clock sem k (sem.init_st oracle) p = (st, r) ∧
      r ≠ Timeout ∧ r ≠ Error ∧
      sem.get_oracle_events st = io_list) ∧
  (ofbs_sem sem p (Diverge io_trace) ⇔
    ?oracle.
      (!k. ?st. eval_with_clock sem k (sem.init_st oracle) p = (st, Timeout)) ∧
      lprefix_lub {fromList (sem.get_oracle_events (FST (eval_with_clock sem k (sem.init_st oracle) p))) | k | T} io_trace) ∧
  (ofbs_sem sem p Crash ⇔
    ?oracle k st.
      eval_with_clock sem k (sem.init_st oracle) p = (st, Error))`;

val _ = Datatype `
  osmall = <| step : 'st -> 'st option;
              is_result : 'st -> bool;
              load : 'o -> 'prog -> 'st;
              unload : 'st -> 'a list |>`;

val step_rel_def = Define `
  step_rel sem = (\s1 s2. sem.step s1 = SOME s2)^*`;

val osmall_sem_def = Define `
  (osmall_sem sem p (Terminate io_list) ⇔
    ?oracle s.
      step_rel sem (sem.load oracle p) s ∧ sem.step s = NONE ∧ sem.is_result s ∧
      sem.unload s = io_list) ∧
  (osmall_sem sem p (Diverge io_trace) ⇔
    ?oracle.
      (!s. step_rel sem (sem.load oracle p) s ⇒ sem.step s ≠ NONE) ∧
      lprefix_lub {fromList (sem.unload s) | s | step_rel sem (sem.load oracle p) s} io_trace) ∧
  (osmall_sem sem p Crash ⇔
    ?oracle s.
      step_rel sem (sem.load oracle p) s ∧ sem.step s = NONE ∧ ¬sem.is_result s)`;

val is_prefix_pres = Q.prove (
`!sem_s.
  (!s1 s2. sem_s.step s1 = SOME s2 ⇒ isPREFIX (sem_s.unload s1) (sem_s.unload s2))
  ⇒
  !s1 s2.
    (λs1 s2. sem_s.step s1 = SOME s2)^* s1 s2
    ⇒
    isPREFIX (sem_s.unload s1) (sem_s.unload s2)`,
 rpt gen_tac >>
 DISCH_TAC >>
 ho_match_mp_tac RTC_INDUCT >>
 rw [] >>
 res_tac >>
 metis_tac [IS_PREFIX_TRANS]);

val small_chain_def = Define `
  small_chain sem_s oracle p =
    {fromList (sem_s.unload s) | s | step_rel sem_s (sem_s.load oracle p) s}`;

val fbs_chain_def = Define `
  fbs_chain sem_f oracle p =
    {fromList (sem_f.get_oracle_events (FST (eval_with_clock sem_f k (sem_f.init_st oracle) p))) | k | T}`;

val small_chain_thm = Q.prove (
`!sem_s oracle p.
  (∀s1 s2. sem_s.step s1 = SOME s2 ⇒ sem_s.unload s1 ≼ sem_s.unload s2)
  ⇒
  lprefix_chain (small_chain sem_s oracle p)`,
 rw [small_chain_def, lprefix_chain_def, LPREFIX_def] >>
 rw [from_toList] >>
 fs [step_rel_def, check_trace_thm] >>
 `LENGTH tr ≤ LENGTH tr' ∨ LENGTH tr' ≤ LENGTH tr` by decide_tac
 >- (
   qabbrev_tac `tr'' = DROP (LENGTH tr - 1) tr'` >>
   `LAST tr = HD tr''` by metis_tac [check_trace_twice_suff] >>
   `LENGTH tr - 1 < LENGTH tr' ∧ LENGTH tr - 1 ≤ LENGTH tr'` by (simp [] >> Cases_on `tr'` >> fs []) >>
   `check_trace sem_s.step tr''` by metis_tac [check_trace_drop] >>
   `LAST tr' = LAST tr''` by metis_tac [last_drop] >>
   rw [] >>
   `tr'' ≠ []` by (unabbrev_all_tac >> fs [DROP_NIL] >> decide_tac) >>
   `(λs1 s2. sem_s.step s1 = SOME s2)^* (HD tr'') (LAST tr'')` by metis_tac [check_trace_thm] >>
   metis_tac [is_prefix_pres])
 >- (
   qabbrev_tac `tr'' = DROP (LENGTH tr' - 1) tr` >>
   `LAST tr' = HD tr''` by metis_tac [check_trace_twice_suff] >>
   `LENGTH tr' - 1 < LENGTH tr ∧ LENGTH tr' - 1 ≤ LENGTH tr` by (simp [] >> Cases_on `tr` >> fs []) >>
   `check_trace sem_s.step tr''` by metis_tac [check_trace_drop] >>
   `LAST tr = LAST tr''` by metis_tac [last_drop] >>
   rw [] >>
   `tr'' ≠ []` by (unabbrev_all_tac >> fs [DROP_NIL] >> decide_tac) >>
   `(λs1 s2. sem_s.step s1 = SOME s2)^* (HD tr'') (LAST tr'')` by metis_tac [check_trace_thm] >>
   metis_tac [is_prefix_pres]));

val fbs_chain_thm = Q.prove (
`!sem_f oracle p.
  (!k1 k2 p. k1 ≤ k2 ⇒
    sem_f.get_oracle_events (FST (eval_with_clock sem_f k1 (sem_f.init_st oracle) p)) ≼
    sem_f.get_oracle_events (FST (eval_with_clock sem_f k2 (sem_f.init_st oracle) p)))
  ⇒
  lprefix_chain (fbs_chain sem_f oracle p)`,
 rw [fbs_chain_def, lprefix_chain_def, LPREFIX_def] >>
 rw [from_toList] >>
 `k ≤ k' ∨ k' ≤ k` by decide_tac >>
 metis_tac []);

val osmall_fbs_equiv_lem = Q.prove (
`!sem_s sem_f oracle p f.
  lprefix_chain (fbs_chain sem_f oracle p) ∧
  lprefix_chain (small_chain sem_s oracle p) ∧
  (∀s1 s2. sem_s.step s1 = SOME s2 ⇒ sem_s.unload s1 ≼ sem_s.unload s2) ∧
  unbounded f ∧
  (∀c p st.
     eval_with_clock sem_f c (sem_f.init_st oracle) p = (st,Timeout) ⇒
     ∃tr.
       f c ≤ LENGTH tr ∧ tr ≠ [] ∧ HD tr = sem_s.load oracle p ∧
       check_trace sem_s.step tr ∧
       sem_f.get_oracle_events st = sem_s.unload (LAST tr)) ∧
  (∀k. ∃st. eval_with_clock sem_f k (sem_f.init_st oracle) p = (st,Timeout))
  ⇒
  equiv_lprefix_chain (fbs_chain sem_f oracle p) (small_chain sem_s oracle p)`,
 rw [] >>
 `!ll. ll ∈ small_chain sem_s oracle p ⇒ LFINITE ll` by (
   rw [small_chain_def] >>
   rw [LFINITE_fromList]) >>
 rw [equiv_lprefix_chain_thm2]
 >- (
   fs [fbs_chain_def] >>
   last_x_assum (qspecl_then [`k`, `p`] mp_tac) >>
   Cases_on `eval_with_clock sem_f k (sem_f.init_st oracle) p` >>
   rw [] >>
   first_x_assum (qspec_then `k` mp_tac) >>
   simp [small_chain_def] >>
   rw [PULL_EXISTS, step_rel_def, check_trace_thm] >>
   qexists_tac `tr` >>
   rw []
   >- metis_tac [] >>
   rfs [LNTH_fromList] >>
   rw [] >>
   metis_tac [])
 >- (
   fs [small_chain_def] >>
   rw [] >>
   fs [step_rel_def, check_trace_thm] >>
   `?c. LENGTH tr < f c` by (fs [unbounded_def] >> decide_tac) >>
   last_x_assum (qspecl_then [`c`, `p`] mp_tac) >>
   rw [] >>
   Cases_on `eval_with_clock sem_f c (sem_f.init_st oracle) p` >>
   fs [] >>
   first_x_assum (qspec_then `c` assume_tac) >>
   rfs [] >>
   fs [] >>
   rw [] >>
   `LENGTH tr < LENGTH tr'` by decide_tac >>
   simp [fbs_chain_def, PULL_EXISTS, llist_shorter_fromList] >>
   qexists_tac `c` >>
   qabbrev_tac `tr'' = DROP (LENGTH tr - 1) tr'` >>
   `LAST tr = HD tr''` by metis_tac [check_trace_twice_suff, LESS_OR_EQ] >>
   `LENGTH tr - 1 < LENGTH tr' ∧ LENGTH tr - 1 ≤ LENGTH tr'` by (simp [] >> Cases_on `tr` >> fs []) >>
   `check_trace sem_s.step tr''` by metis_tac [check_trace_drop] >>
   `LAST tr' = LAST tr''` by metis_tac [last_drop] >>
   `tr'' ≠ []` by (unabbrev_all_tac >> fs [DROP_NIL] >> decide_tac) >>
   `(λs1 s2. sem_s.step s1 = SOME s2)^* (HD tr'') (LAST tr'')` by metis_tac [check_trace_thm] >>
   imp_res_tac is_prefix_pres >>
   fs [] >>
   metis_tac [IS_PREFIX_LENGTH, LESS_TRANS, LESS_OR_EQ]));

val equiv_lprefix_chain_sym = Q.prove (
`!ls1 ls2. equiv_lprefix_chain ls1 ls2 ⇔ equiv_lprefix_chain ls2 ls1`,
 rw [equiv_lprefix_chain_def] >>
 metis_tac []);

val osmall_fbs_equiv = Q.store_thm ("osmall_fbs_equiv",
`!sem_f sem_s.
  (∀s1 s2. sem_s.step s1 = SOME s2 ⇒ sem_s.unload s1 ≼ sem_s.unload s2) ∧
  (!oracle k1 k2 p. k1 ≤ k2 ⇒
    sem_f.get_oracle_events (FST (eval_with_clock sem_f k1 (sem_f.init_st oracle) p)) ≼
    sem_f.get_oracle_events (FST (eval_with_clock sem_f k2 (sem_f.init_st oracle) p))) ∧
  (?f.
     unbounded f ∧
     !oracle c p st.
       eval_with_clock sem_f c (sem_f.init_st oracle) p = (st, Timeout) ⇒
       ?tr. f c ≤ LENGTH tr ∧ tr ≠ [] ∧ HD tr = sem_s.load oracle p ∧ check_trace sem_s.step tr ∧
            sem_f.get_oracle_events st = sem_s.unload (LAST tr)) ∧
  (!oracle c p st r.
    eval_with_clock sem_f c (sem_f.init_st oracle) p = (st,r) ∧ r ≠ Timeout ⇒
    ?r'. step_rel sem_s (sem_s.load oracle p) r' ∧ sem_s.step r' = NONE ∧
         (r = Error ⇔ ~sem_s.is_result r') ∧
         (r ≠ Error ⇒ sem_f.get_oracle_events st = sem_s.unload r'))
  ⇒
  !p r.
    ofbs_sem sem_f p r ⇔ osmall_sem sem_s p r`,
 rw [] >>
 Cases_on `r` >>
 rw [osmall_sem_def, ofbs_sem_def] >>
 eq_tac >>
 simp []
 >- metis_tac []
 >- (
   fs [step_rel_def] >>
   rw [] >>
   qexists_tac `oracle` >>
   Cases_on `?k st r. eval_with_clock sem_f k (sem_f.init_st oracle) p = (st,r) ∧ r ≠ Timeout` >>
   fs []
   >- (
     MAP_EVERY qexists_tac [`k`, `st`, `r`] >>
     simp [] >>
     res_tac >>
     `r' = s` by metis_tac [step_rel_determ] >>
     fs [])
   >- (
     fs [check_trace_thm] >>
     `?c. LENGTH tr < f c` by (fs [unbounded_def] >> decide_tac) >>
     last_x_assum (qspecl_then [`oracle`, `c`, `p`] mp_tac) >>
     Cases_on `eval_with_clock sem_f c (sem_f.init_st oracle) p` >>
     simp [] >>
     `r = Timeout` by metis_tac [] >>
     rw [] >>
     `LENGTH tr < LENGTH tr'` by decide_tac >>
     metis_tac [trace_extends]))
 >- (
   DISCH_TAC >>
   fs [] >>
   simp [] >>
   qexists_tac `oracle` >>
   conj_asm1_tac
   >- (
     simp [step_rel_def, check_trace_thm, PULL_EXISTS, PULL_FORALL] >>
     gen_tac >>
     rw [] >>
     `?c. LENGTH tr < f c` by (fs [unbounded_def] >> decide_tac) >>
     first_x_assum (qspec_then `c` mp_tac) >>
     last_x_assum (qspecl_then [`oracle`, `c`, `p`] mp_tac) >>
     rpt DISCH_TAC >>
     fs [] >>
     fs [] >>
     `LENGTH tr < LENGTH tr'` by decide_tac >>
     rw [] >>
     metis_tac [trace_extends])
   >- (
     fs [GSYM fbs_chain_def, GSYM small_chain_def] >>
     match_mp_tac lprefix_lub_new_chain >>
     qexists_tac `fbs_chain sem_f oracle p` >>
     metis_tac [fbs_chain_thm, small_chain_thm,osmall_fbs_equiv_lem, equiv_lprefix_chain_sym]))
 >- (
   DISCH_TAC >>
   fs [] >>
   simp [PULL_FORALL] >>
   qexists_tac `oracle` >>
   gen_tac >>
   Cases_on `?c st r. eval_with_clock sem_f c (sem_f.init_st oracle) p = (st,r) ∧ r ≠ Timeout` >>
   fs [] >>
   rw []
   >- metis_tac []
   >- metis_tac []
   >- (
     first_x_assum (qspec_then `k` mp_tac) >>
     Cases_on `eval_with_clock sem_f k (sem_f.init_st oracle) p` >>
     rw [])
   >- (
     fs [GSYM fbs_chain_def, GSYM small_chain_def] >>
     match_mp_tac lprefix_lub_new_chain >>
     qexists_tac `small_chain sem_s oracle p` >>
     metis_tac [pair_CASES, fbs_chain_thm, small_chain_thm,osmall_fbs_equiv_lem, equiv_lprefix_chain_sym]))
 >- metis_tac [fetch "-" "fbs_res_distinct"]
 >- (
   fs [step_rel_def] >>
   rw [] >>
   qexists_tac `oracle` >>
   Cases_on `?k st r. eval_with_clock sem_f k (sem_f.init_st oracle) p = (st,r) ∧ r ≠ Timeout` >>
   fs []
   >- (
     MAP_EVERY qexists_tac [`k`, `st`] >>
     simp [] >>
     res_tac >>
     `r' = s` by metis_tac [step_rel_determ] >>
     fs [])
   >- (
     fs [check_trace_thm] >>
     `?c. LENGTH tr < f c` by (fs [unbounded_def] >> decide_tac) >>
     last_x_assum (qspecl_then [`oracle`, `c`, `p`] mp_tac) >>
     Cases_on `eval_with_clock sem_f c (sem_f.init_st oracle) p` >>
     simp [] >>
     `r = Timeout` by metis_tac [] >>
     rw [] >>
     `LENGTH tr < LENGTH tr'` by decide_tac >>
     metis_tac [trace_extends])));

val same_result_def = Define `
 (same_result sem_f sem_s (st, Val a) s ⇔
  sem_f.get_oracle_events st = sem_s.unload s ∧
  sem_s.is_result s ∧
  sem_s.step s = NONE) ∧
 (same_result sem_f sem_s (st, Error) s ⇔
  ¬sem_s.is_result s ∧
  sem_s.step s = NONE) ∧
 (same_result sem_f sem_s (st, Timeout) s ⇔
  sem_f.get_oracle_events st = sem_s.unload s ∧
  ?s'. sem_s.step s = SOME s')`;

val osmall_fbs_equiv2 = Q.store_thm ("osmall_fbs_equiv2",
`!sem_f sem_s.
  (∀s1 s2. sem_s.step s1 = SOME s2 ⇒ sem_s.unload s1 ≼ sem_s.unload s2) ∧
  (!oracle k1 k2 p. k1 ≤ k2 ⇒
    sem_f.get_oracle_events (FST (eval_with_clock sem_f k1 (sem_f.init_st oracle) p)) ≼
    sem_f.get_oracle_events (FST (eval_with_clock sem_f k2 (sem_f.init_st oracle) p))) ∧
  (!oracle c p.
    SND (eval_with_clock sem_f c (sem_f.init_st oracle) p) = Timeout ⇒
    sem_f.get_clock (FST (eval_with_clock sem_f c (sem_f.init_st oracle) p)) = 0) ∧
  (?f.
     unbounded f ∧
     !oracle c p st r.
       eval_with_clock sem_f c (sem_f.init_st oracle) p = (st, r) ⇒
       ?tr. f (c - sem_f.get_clock st) ≤ LENGTH tr  ∧ tr ≠ [] ∧ HD tr = sem_s.load oracle p ∧ check_trace sem_s.step tr ∧
            same_result sem_f sem_s (st, r) (LAST tr))
  ⇒
  !p r.
    ofbs_sem sem_f p r ⇔ osmall_sem sem_s p r`,
 rpt gen_tac >>
 DISCH_TAC >>
 match_mp_tac osmall_fbs_equiv >>
 rw []
 >- (
   qexists_tac `f` >>
   rw [] >>
   res_tac >>
   fs [same_result_def] >>
   qexists_tac `tr` >>
   simp [] >>
   last_x_assum (qspecl_then [`oracle`, `c`, `p`] mp_tac) >>
   rw [] >>
   fs [])
 >- (
   res_tac >>
   rw [step_rel_def, check_trace_thm] >>
   reverse (Cases_on `r`) >>
   fs [same_result_def] >>
   metis_tac []));

val _ = export_theory ();
