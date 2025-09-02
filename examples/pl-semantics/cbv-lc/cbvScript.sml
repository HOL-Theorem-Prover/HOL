(* An untyped call-by-value lambda calculus with a functional big-step
 * semantics, and a definition of contextual approximation for it. We
 * use closures rather than substitution in the semantics, and use
 * De Bruijn indices for variables. *)

open HolKernel boolLib bossLib Parse;
open integerTheory stringTheory alistTheory listTheory pred_setTheory;
open pairTheory optionTheory finite_mapTheory arithmeticTheory;

val _ = set_trace "Goalstack.print_goal_at_top" 0;
val _ = ParseExtras.temp_tight_equality();

fun term_rewrite tms = let
  fun f tm = ASSUME (list_mk_forall(free_vars tm,tm))
  in rand o concl o QCONV (REWRITE_CONV (map f tms)) end

val _ = new_theory "cbv";

(* Syntax *)

val _ = Datatype `
lit =
  Int int`;

val _ = Datatype `
exp =
  | Lit lit
  | Var num
  | App exp exp
  | Fun exp
  | Tick exp`;

(* Values *)

val _ = Datatype `
v =
  | Litv lit
  | Clos (v list) exp`;

val v_induction = theorem "v_induction";

val v_ind =
  v_induction
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE (srw_ss()) []
  |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
  |> GEN_ALL
  |> curry save_thm "v_ind";

val v_size_def = definition"v_size_def"

val _ = type_abbrev("env",``:v list``)

(* Semantics *)

(* The state of the semantics will have a clock and a store.
 * Even though we don't have any constructs that access the store, we want the
 * placeholder. *)

val _ = Datatype `
state = <| clock : num; store : v list|>`;

val state_component_equality = theorem "state_component_equality";

val state_clock_idem = Q.store_thm ("state_clock_idem[simp]",
`!s. (s with clock := s.clock) = s`,
 rw [state_component_equality]);

(* machinery for the functional big-step definition *)

val check_clock_def = Define `
  check_clock s' s =
    s' with clock := (if s'.clock ≤ s.clock then s'.clock else s.clock)`;

val check_clock_id = prove(
  ``!s s'. s.clock ≤ s'.clock ⇒ check_clock s s' = s``,
 rw [check_clock_def, state_component_equality]);

val dec_clock_def = Define `
  dec_clock s = s with clock := s.clock - 1`;

(* results *)

val _ = Datatype`
  r = Rval v
    | Rfail
    | Rtimeout`;

(* big-step semantics as a function *)

Definition sem_def:
(sem env s (Lit i) = (Rval (Litv i), s)) ∧
(sem env s (Var n) =
  if n < LENGTH env then
    (Rval (EL n env), s)
  else
    (Rfail, s)) ∧
(sem env s (App e1 e2) =
 case sem env s e1 of
 | (Rval v1, s1) =>
     (case sem env (check_clock s1 s) e2 of
      | (Rval v2, s2) =>
          if s.clock ≠ 0 ∧ s2.clock ≠ 0 then
            (case v1 of
             | Clos env' e =>
               sem (v2::env') (dec_clock (check_clock s2 s)) e
             | _ => (Rfail, s2))
          else
            (Rtimeout, s2)
      | res => res)
 | res => res) ∧
(sem env s (Fun e) = (Rval (Clos env e), s)) ∧
(sem env s (Tick e) =
  if s.clock ≠ 0 then
    sem env (dec_clock s) e
  else
    (Rtimeout, s))
Termination
 WF_REL_TAC`inv_image (measure I LEX measure exp_size)
                      (λ(env,s,e). (s.clock,e))` >>
 rpt strip_tac >> TRY DECIDE_TAC >>
 fs[check_clock_def,dec_clock_def] >>
 rw[] >> fsrw_tac[ARITH_ss][]
End

val sem_clock = store_thm("sem_clock",
  ``∀env s e r s'. sem env s e = (r, s') ⇒ s'.clock ≤ s.clock``,
  ho_match_mp_tac sem_ind >>
  rpt conj_tac >>
  simp[sem_def] >>
  rpt gen_tac >>
  BasicProvers.EVERY_CASE_TAC >>
  simp[check_clock_def,dec_clock_def] >>
  rpt(IF_CASES_TAC >> simp[]) >>
  rpt strip_tac >> res_tac >> simp[] >> fs[])

(* Remove the extra check_clock calls that were used above to guide the HOL
 * termination prover *)

val r = term_rewrite [``check_clock s1 s = s1``,
    ``s.clock <> 0 /\ s1.clock <> 0 <=> s1.clock <> 0``];

Theorem sem_def[allow_rebind]:
  ^(sem_def |> concl |> r)
Proof
  rpt strip_tac >>
  rw[Once sem_def] >>
  BasicProvers.CASE_TAC >>
  imp_res_tac sem_clock >>
  simp[check_clock_id] >>
  BasicProvers.CASE_TAC >>
  imp_res_tac sem_clock >>
  simp[check_clock_id] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >>
  imp_res_tac sem_clock >>
  simp[check_clock_id] >>
  `F` suffices_by rw[] >>
  DECIDE_TAC
QED

Theorem sem_ind[allow_rebind]:
  ^(sem_ind |> concl |> r)
Proof
  ntac 2 strip_tac >>
  ho_match_mp_tac sem_ind >>
  rw[] >>
  first_x_assum match_mp_tac >>
  rw[] >> fs[] >>
  res_tac >>
  imp_res_tac sem_clock >>
  fsrw_tac[ARITH_ss][check_clock_id] >> rfs[] >>
  fsrw_tac[ARITH_ss][check_clock_id]
QED

(* Misc lemmas stating that the clock acts like a clock. These could probably be
 * unified and simplified *)

val sem_clock_add_lem = Q.prove (
`!env s1 e v s2 c1 c2.
  sem env s1 e = (Rval v, s2) ∧
  s1.clock = c1
  ⇒
  sem env (s1 with clock := c1 + c2) e = (Rval v, s2 with clock := s2.clock + c2)`,
 ho_match_mp_tac sem_ind >>
 rw [sem_def, state_component_equality] >>
 rw [] >>
 `?res s2. sem env s1 e = (res, s2)` by metis_tac [pair_CASES] >>
 fs []
 >- (Cases_on `res` >>
     fs [] >>
     `?res' s3. sem env s2' e' = (res', s3)` by metis_tac [pair_CASES] >>
     fs [] >>
     Cases_on `res'` >>
     fs [] >>
     Cases_on `s3.clock = 0` >>
     fs [] >>
     Cases_on `v'` >>
     fs [dec_clock_def] >>
     last_x_assum (qspec_then `c2` mp_tac) >>
     rw [] >>
     full_simp_tac (srw_ss()++ ARITH_ss) [] >>
     `s3.clock − 1 + c2 =  c2 + s3.clock − 1` by decide_tac >>
     fs [])
 >- (fs [dec_clock_def] >>
     full_simp_tac (srw_ss()++ ARITH_ss) [] >>
     `c2 + s1.clock − 1 =  c2 + (s1.clock − 1)` by decide_tac >>
     metis_tac []));

val sem_clock_add_fail_lem = Q.prove (
`!env s1 e v s2 c1 c2.
  sem env s1 e = (Rfail, s2) ∧
  s1.clock = c1
  ⇒
  sem env (s1 with clock := c1 + c2) e = (Rfail, s2 with clock := s2.clock + c2)`,
 ho_match_mp_tac sem_ind >>
 rw [sem_def, state_component_equality] >>
 rw []
 >- (`?res s2. sem env s1 e = (res, s2)` by metis_tac [pair_CASES] >>
     fs [] >>
     Cases_on `res` >>
     fs [] >>
     `?res' s3. sem env s2' e' = (res', s3)` by metis_tac [pair_CASES] >>
     fs [] >>
     Cases_on `res'` >>
     fs [] >>
     `sem env (s1 with clock := s1.clock + c2) e = (Rval v,s2' with clock := s2'.clock + c2)`
                    by metis_tac [sem_clock_add_lem]
     >- (`sem env (s2' with clock := s2'.clock + c2) e' = (Rval v',s3 with clock := s3.clock + c2)`
                    by metis_tac [sem_clock_add_lem] >>
         Cases_on `s3.clock = 0` >>
         fs [] >>
         Cases_on `v` >>
         fs [dec_clock_def] )
     >- (`sem env (s2' with clock := c2 + s2'.clock) e' = (Rfail,s3 with clock := c2 + s3.clock)`
                    by metis_tac [] >>
         fs[]))
 >- (fs [dec_clock_def] >>
     full_simp_tac (srw_ss()++ ARITH_ss) [] >>
     `c2 + s1.clock − 1 =  c2 + (s1.clock − 1)` by decide_tac >>
     metis_tac []));

val sem_clock_add = Q.store_thm ("sem_clock_add",
`!env s1 e v s2 c1 c2.
  sem env (s1 with clock := c1) e = (Rval v, s2)
  ⇒
  sem env (s1 with clock := c1 + c2) e = (Rval v, s2 with clock := s2.clock + c2)`,
 srw_tac[] [] >>
 qabbrev_tac `s1' = s1 with clock := c1` >>
 `(s1 with clock := c1 + c2) = s1' with clock := s1'.clock + c2`
            by fs [state_component_equality, Abbr`s1'`] >>
 srw_tac[] [] >>
 match_mp_tac sem_clock_add_lem >>
 rw []);

val sem_clock_add_fail = Q.store_thm ("sem_clock_add_fail",
`!env s1 e v s2 c1 c2.
  sem env (s1 with clock := c1) e = (Rfail, s2)
  ⇒
  sem env (s1 with clock := c1 + c2) e = (Rfail, s2 with clock := s2.clock + c2)`,
 srw_tac[] [] >>
 qabbrev_tac `s1' = s1 with clock := c1` >>
 `(s1 with clock := c1 + c2) = s1' with clock := s1'.clock + c2`
            by fs [state_component_equality, Abbr`s1'`] >>
 srw_tac[] [] >>
 match_mp_tac sem_clock_add_fail_lem >>
 rw []);

val sem_clock_timeout0 = Q.store_thm ("sem_clock_timeout0",
`!env s e s'. sem env s e = (Rtimeout, s') ⇒ s'.clock = 0`,
 ho_match_mp_tac sem_ind >>
 rw [sem_def] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [] >>
 rw []);

 (* This is proved, but we turn out to not need it *)
val sem_clock_sub = Q.store_thm ("sem_clock_sub",
`!env s1 e v s2.
  sem env s1 e = (Rval v,s2)
  ⇒
  sem env (s1 with clock := s1.clock - s2.clock) e = (Rval v, s2 with clock := 0)`,
 ho_match_mp_tac sem_ind >>
 rw [sem_def]
 >- (Cases_on `sem env s1 e` >>
     Cases_on `q` >>
     fs [dec_clock_def] >>
     rw [] >>
     Cases_on `sem env r e'` >>
     Cases_on `q` >>
     fs [] >>
     rw [] >>
     Cases_on `r'.clock ≠ 0` >>
     fs [] >>
     Cases_on `v'` >>
     fs [] >>
     rw [] >>
     imp_res_tac sem_clock >>
     fs [] >>
     `sem env (s1 with clock := (s1.clock − r.clock) + (r.clock − s2.clock)) e =
              (Rval (Clos l e''), (r with clock := 0) with clock := (r with clock := 0).clock + (r.clock − s2.clock))`
                 by metis_tac [sem_clock_add] >>
     fs [] >>
     rw [] >>
     `s1.clock − r.clock + (r.clock − s2.clock) = s1.clock - s2.clock` by decide_tac >>
     fs [] >>
     `sem env (r with clock := (r.clock − r'.clock) + (r'.clock − s2.clock)) e' =
              (Rval v'', (r' with clock := 0) with clock := (r' with clock := 0).clock + (r'.clock − s2.clock))`
                 by metis_tac [sem_clock_add] >>
     fs [] >>
     rw [] >>
     `r.clock − r'.clock + (r'.clock − s2.clock) = r.clock - s2.clock` by intLib.ARITH_TAC >>
     fs [])
 >- (rw [] >>
     fs [dec_clock_def] >>
     imp_res_tac sem_clock >>
     fs [] >>
     intLib.ARITH_TAC));

(* The value doesn't depend on which clock you use to compute it *)
val sem_clock_val_determ_lem = Q.prove (
`!env s e v' s' v'' s'' c.
  sem env s e = (Rval v', s') ∧
  sem env (s with clock := c) e = (Rval v'', s'')
  ⇒
  v' = v'' ∧
  s' = (s'' with clock := s'.clock)`,
 ho_match_mp_tac sem_ind >>
 rw [sem_def, state_component_equality]
 >- metis_tac []
 >- metis_tac []
 >- (Cases_on `sem env s e` >>
     Cases_on `q` >>
     fs [] >>
     Cases_on `sem env (s with clock := c) e` >>
     Cases_on `q` >>
     fs [] >>
     `v = v''' ∧ r.store = r'.store` by metis_tac [] >>
     rw [] >>
     Cases_on `sem env r e'` >>
     Cases_on `q` >>
     fs [] >>
     Cases_on `sem env r' e'` >>
     Cases_on `q` >>
     fs [] >>
     `v''' = v'''' ∧ r''.store = r'''.store`
               by (first_x_assum match_mp_tac >>
                   qexists_tac `r'.clock` >>
                   fs [] >>
                   `r' = r with clock := r'.clock` by rw [state_component_equality] >>
                   metis_tac []) >>
     rw [] >>
     BasicProvers.EVERY_CASE_TAC >>
     fs [] >>
     fs [dec_clock_def] >>
     res_tac >>
     fs [] >>
     `(r''' with clock := r'''.clock - 1) = (r'' with clock := r'''.clock - 1)` by rw [state_component_equality] >>
     metis_tac [])
 >- (Cases_on `sem env s e` >>
     Cases_on `q` >>
     fs [] >>
     Cases_on `sem env (s with clock := c) e` >>
     Cases_on `q` >>
     fs [] >>
     `v = v''' ∧ r.store = r'.store` by metis_tac [] >>
     rw [] >>
     Cases_on `sem env r e'` >>
     Cases_on `q` >>
     fs [] >>
     Cases_on `sem env r' e'` >>
     Cases_on `q` >>
     fs [] >>
     `v''' = v'''' ∧ r''.store = r'''.store`
               by (first_x_assum match_mp_tac >>
                   qexists_tac `r'.clock` >>
                   fs [] >>
                   `r' = r with clock := r'.clock` by rw [state_component_equality] >>
                   metis_tac []) >>
     rw [] >>
     BasicProvers.EVERY_CASE_TAC >>
     fs [] >>
     fs [dec_clock_def] >>
     res_tac >>
     fs [] >>
     `(r''' with clock := r'''.clock - 1) = (r'' with clock := r'''.clock - 1)` by rw [state_component_equality] >>
     metis_tac [])
 >- metis_tac []
 >- (BasicProvers.EVERY_CASE_TAC >>
     fs [] >>
     fs [dec_clock_def] >>
     metis_tac [])
 >- (BasicProvers.EVERY_CASE_TAC >>
     fs [] >>
     fs [dec_clock_def] >>
     metis_tac []));

val sem_clock_val_determ = Q.store_thm ("sem_clock_val_determ",
`!env s e v' s' v'' s'' c1 c2.
  sem env (s with clock := c1) e = (Rval v', s') ∧
  sem env (s with clock := c2) e = (Rval v'', s'')
  ⇒
  v' = v'' ∧
  s' = (s'' with clock := s'.clock)`,
 rpt gen_tac >>
 DISCH_TAC >>
 match_mp_tac sem_clock_val_determ_lem >>
 qexists_tac `env` >>
 qexists_tac `s with clock := c1` >>
 rw [] >>
 metis_tac [sem_clock_val_determ_lem]);

(* The top-level semantics *)

val eval_def = Define `
(eval e (Rval v) =
  ?c s. sem [] <| store := []; clock := c |> e = (Rval v, s)) ∧
(eval e Rfail =
  ?c s. sem [] <| store := []; clock := c |> e = (Rfail, s)) ∧
(eval e Rtimeout =
  ∀c. ∃s. sem [] <| store := []; clock := c |> e = (Rtimeout, s))`;

(* Contexts *)

val _ = Datatype `
ctxt =
  | Hole
  | FunC ctxt
  | App1C ctxt exp
  | App2C exp ctxt
  | TickC ctxt`;

(* Fill the hole in a context with an expression *)
val ctxt_to_exp_def = Define `
(ctxt_to_exp Hole e = e) ∧
(ctxt_to_exp (FunC ctxt) e = Fun (ctxt_to_exp ctxt e)) ∧
(ctxt_to_exp (App1C ctxt e1) e = App (ctxt_to_exp ctxt e) e1) ∧
(ctxt_to_exp (App2C e1 ctxt) e = App e1 (ctxt_to_exp ctxt e)) ∧
(ctxt_to_exp (TickC ctxt) e = Tick (ctxt_to_exp ctxt e))`;

(* Contextual approximation must preserve divergence and termination, but
 * can relate a failing computation to anything. *)
val res_approx_def = Define `
(res_approx Rfail _ ⇔ T) ∧
(res_approx Rtimeout Rtimeout ⇔ T) ∧
(res_approx (Rval _) (Rval _) ⇔ T) ∧
(res_approx _ _ ⇔ F)`;

val ctxt_approx_def = Define `
ctxt_approx e1 e2 ⇔
  !ctxt r1 r2.
    eval (ctxt_to_exp ctxt e1) r1 ∧
    eval (ctxt_to_exp ctxt e2) r2
    ⇒
    res_approx r1 r2`;

val _ = export_theory ();
