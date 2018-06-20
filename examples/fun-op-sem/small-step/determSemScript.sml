(* A general theory of functional-big-step equivalence with small-step for
 * deterministic languages *)

open HolKernel boolLib bossLib lcsymtacs Parse;
open integerTheory stringTheory alistTheory listTheory pred_setTheory relationTheory;
open pairTheory optionTheory finite_mapTheory arithmeticTheory;
open simple_traceTheory;

val _ = set_trace "Goalstack.print_goal_at_top" 0;
val _ = ParseExtras.temp_tight_equality();

val _ = new_theory "determSem";

(* ----------- Generic small-step --------- *)

val _ = Datatype `
  result =
    Terminate 'a
  | Diverge
  | Crash`;

(* A deterministic small-step semantics has
 * - a type of states, 'st,
 * - a step function (to an option for representing stuckness),
 * - a predicate on states to distinguish stuck ones from good results
 * - load and unload functions that convert from programs to states, and from
 *   states to results
 * *)

val _ = Datatype `
  small = <| step : 'st -> 'st option;
             is_value : 'st -> bool;
             load : 'prog -> 'st;
             unload : 'st -> 'res |>`;

(* Given a small-step semantics and program, get the result *)
val small_sem_def = Define `
  small_sem sem prog =
    let step_rel = (\s1 s2. sem.step s1 = SOME s2)^* in
    let init_state = sem.load prog in
      case some s'. step_rel init_state s' ∧ sem.step s' = NONE of
        NONE => Diverge
      | SOME s' =>
          if sem.is_value s' then
            Terminate (sem.unload s')
          else
            Crash`;

(* ----------- Generic functional big-step --------- *)

val _ = Datatype `
  fbs_res =
    Timeout
  | Error
  | Val 'a`;

(* A functional big-step semantics has
 * - a type of states, 'st, and environments 'env, and inital values for them
 * - a evaluation function
 * - an unload mapping from the evaluator's result to the actual result
 * - functions to get and set the clock from the state
 *)
val _ = Datatype `
  fbs = <| eval : 'st -> 'env -> 'prog -> 'st # 'v fbs_res;
           init_st : 'st;
           init_env : 'env;
           set_clock : num -> 'st -> 'st;
           get_clock : 'st -> num;
           unload : 'v -> 'a |>`;

val eval_with_clock_def = Define `
  eval_with_clock sem c p =
    sem.eval (sem.set_clock c sem.init_st) sem.init_env p`;

val fbs_sem_def = Define `
  fbs_sem sem prog =
    case some c. SND (eval_with_clock sem c prog) ≠ Timeout of
      NONE => Diverge
    | SOME c =>
        case SND (eval_with_clock sem c prog) of
          Val r => Terminate (sem.unload r)
        | Error => Crash`;

(* 2 theorems showing when a small-step and functional big-step are equivalent *)

val check_result_def = Define `
  (check_result unload_f (Val x) r ⇔ unload_f x = r) ∧
  (check_result unload_f _ r ⇔ T)`;

local val rw = srw_tac[] val fs = fsrw_tac[] in
val small_fbs_equiv = Q.store_thm ("small_fbs_equiv",
`!sem_f sem_s.
  (?f.
     unbounded f ∧
     !c p.
       SND (eval_with_clock sem_f c p) = Timeout ⇒
       ?tr. f c ≤ LENGTH tr ∧ tr ≠ [] ∧ HD tr = sem_s.load p ∧ check_trace sem_s.step tr) ∧
  (!c p r.
    SND (eval_with_clock sem_f c p) = r ∧ r ≠ Timeout ⇒
    ?r'. (λs1 s2. sem_s.step s1 = SOME s2)^* (sem_s.load p) r' ∧
         sem_s.step r' = NONE ∧
         (r = Error ⇔ ~sem_s.is_value r') ∧
         check_result sem_f.unload r (sem_s.unload r'))
  ⇒
  !prog.
    fbs_sem sem_f prog = small_sem sem_s prog`,
 rw [small_sem_def, fbs_sem_def] >>
 `!s s'.
   (step_rel init_state s ∧ sem_s.step s = NONE) ∧
   (step_rel init_state s' ∧ sem_s.step s' = NONE)
   ⇒
   s = s'`
   by metis_tac [step_rel_determ] >>
 every_case_tac >>
 fs [some_no_choice] >>
 rfs [some_exists_determ]
 >- ( (* big diverge, small value *)
   unabbrev_all_tac >>
   fs [check_trace_thm] >>
   rw [] >>
   `?c'. LENGTH tr < f c'` by metis_tac [unbounded_def] >>
   last_x_assum (qspecl_then [`c'`, `prog`] mp_tac) >>
   rw [] >>
   CCONTR_TAC >>
   fs [] >>
   `LENGTH tr < LENGTH tr'` by decide_tac >>
   metis_tac [trace_extends, NOT_SOME_NONE])
 >- ( (* big_diverge, small crash *)
   unabbrev_all_tac >>
   fs [check_trace_thm] >>
   rw [] >>
   `?c'. LENGTH tr < f c'` by metis_tac [unbounded_def] >>
   last_x_assum (qspecl_then [`c'`, `prog`] mp_tac) >>
   rw [] >>
   CCONTR_TAC >>
   fs [] >>
   `LENGTH tr < LENGTH tr'` by decide_tac >>
   metis_tac [trace_extends, NOT_SOME_NONE])
 >- (
   fs [some_def] >>
   metis_tac [])
 >- (
   fs [some_def] >>
   metis_tac [])
 >- (
   fs [some_def] >>
   metis_tac [])
 >- (
   fs [some_def] >>
   metis_tac [])
 >- (
   fs [some_def] >>
   metis_tac [])
 >- (
   fs [some_def] >>
   metis_tac [])
 >- ( (* big term, small diverge *)
   first_x_assum (qspecl_then [`x`, `prog`] mp_tac) >>
   rw [check_result_def] >>
   CCONTR_TAC >>
   fs [] >>
   metis_tac [])
 >- ( (* big term, small value *)
   first_x_assum (qspecl_then [`x`, `prog`] mp_tac) >>
   rw [check_result_def] >>
   metis_tac []));
end

val same_result_def = Define `
 (same_result sem_f sem_s (Val a) s ⇔
  sem_f.unload a = sem_s.unload s ∧
  sem_s.is_value s ∧
  sem_s.step s = NONE) ∧
 (same_result sem_f sem_s Error s ⇔
  ¬sem_s.is_value s ∧
  sem_s.step s = NONE) ∧
 (same_result sem_f sem_s Timeout s ⇔
  ?s'. sem_s.step s = SOME s')`;

val small_fbs_equiv2 = Q.store_thm ("small_fbs_equiv2",
`!sem_f sem_s.
  (!c p.
    SND (eval_with_clock sem_f c p) = Timeout ⇒
    sem_f.get_clock (FST (eval_with_clock sem_f c p)) = 0) ∧
  (?f.
     unbounded f ∧
     !c p st r.
       eval_with_clock sem_f c p = r ⇒
       ?tr. f (c - sem_f.get_clock (FST r)) ≤ LENGTH tr ∧ tr ≠ [] ∧ HD tr = sem_s.load p ∧ check_trace sem_s.step tr ∧
         same_result sem_f sem_s (SND r) (LAST tr))
  ⇒
  !prog.
    fbs_sem sem_f prog = small_sem sem_s prog`,
 rpt gen_tac >>
 DISCH_TAC >>
 match_mp_tac small_fbs_equiv >>
 rw []
 >- (
   qexists_tac `f` >>
   rw [] >>
   first_x_assum (qspecl_then [`c`, `p`] mp_tac) >>
   rw [] >>
   metis_tac [])
 >- (
   rw [check_trace_thm] >>
   first_x_assum (qspecl_then [`c`, `p`] mp_tac) >>
   rw [] >>
   qexists_tac `LAST tr` >>
   rw []
   >- metis_tac [] >>
   Cases_on `SND (eval_with_clock sem_f c p)` >>
   fs [same_result_def, check_result_def]));

val _ = export_theory ();
