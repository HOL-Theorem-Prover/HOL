(* Define a small-step semantics for the deterministic FOR language, prove it
 * equivalent to the functional big-step *)

open HolKernel Parse boolLib bossLib;
open optionTheory pairTheory pred_setTheory finite_mapTheory stringTheory;
open integerTheory listTheory optionTheory rich_listTheory;
open BasicProvers;
open forTheory determSemTheory simple_traceTheory;
open relationTheory

val _ = new_theory "forSmall";

val _ = temp_tight_equality ();

val ect = BasicProvers.EVERY_CASE_TAC;

val some_no_choice = Q.prove (
`!f. (some x. f x) = NONE ⇔ ¬?x. f x`,
 rw [some_def]);

(* A small step semantics for the deterministic FOR language *)

(* Add a Handle statement that will stop breaks from propagating *)
val _ = Datatype `
small_t =
  | Dec string small_t
  | Exp e
  | Break
  | Seq small_t small_t
  | If e small_t small_t
  | For e e small_t
  | Handle small_t`;

val t_to_small_t_def = Define `
(t_to_small_t ((Dec string t):t) = ((Dec string (t_to_small_t t)) : small_t)) ∧
(t_to_small_t (Exp e) = Exp e) ∧
(t_to_small_t Break = Break) ∧
(t_to_small_t (Seq t1 t2) = Seq (t_to_small_t t1) (t_to_small_t t2)) ∧
(t_to_small_t (If e t1 t2) = If e (t_to_small_t t1) (t_to_small_t t2)) ∧
(t_to_small_t (For e1 e2 t) = For e1 e2 (t_to_small_t t))`;

val is_val_e_def = Define `
(is_val_e (Num n) = T) ∧
(is_val_e _ = F)`;

val (step_e_rules, step_e_ind, step_e_cases) = Hol_reln `
(!s x n.
  FLOOKUP s x = SOME n
  ⇒
  step_e (s, Var x) (s, Num n)) ∧
(!s n1 n2.
  step_e (s, Add (Num n1) (Num n2)) (s, Num (n1 + n2))) ∧
(!s s2 e1 e2 e3.
  is_val_e e1 ∧
  step_e (s, e2) (s2, e3)
  ⇒
  step_e (s, Add e1 e2) (s2, Add e1 e3)) ∧
(!s s2 e1 e2 e3.
  step_e (s, e1) (s2, e3)
  ⇒
  step_e (s, Add e1 e2) (s2, Add e3 e2)) ∧
(!s x n.
  step_e (s, Assign x (Num n)) (s |+ (x, n), Num n)) ∧
(!s s2 x e1 e2.
  step_e (s, e1) (s2, e2)
  ⇒
  step_e (s, Assign x e1) (s2, Assign x e2))`;

val is_val_t_def = Define `
(is_val_t (Exp e) = is_val_e e) ∧
(is_val_t Break = T) ∧
(is_val_t _ = F)`;

val (step_t_rules, step_t_ind, step_t_cases) = Hol_reln `
(!s t x.
  step_t (s, Dec x t) (s |+ (x, 0), t)) ∧
(!s s2 e e2.
  step_e (s, e) (s2, e2)
  ⇒
  step_t (s, Exp e) (s2, Exp e2)) ∧
(!s s2 t1 t2 t1'.
  step_t (s, t1) (s2, t1')
  ⇒
  step_t (s, Seq t1 t2) (s2, Seq t1' t2)) ∧
(!s t.
  step_t (s, Seq Break t) (s, Break)) ∧
(!s n t.
  step_t (s, Seq (Exp (Num n)) t) (s, t)) ∧
(!s s2 e t1 t2 e2.
  step_e (s, e) (s2,e2)
  ⇒
  step_t (s, If e t1 t2) (s2, If e2 t1 t2)) ∧
(!s t1 t2.
  step_t (s, If (Num 0) t1 t2) (s, t2)) ∧
(!s n t1 t2.
  n ≠ 0
  ⇒
  step_t (s, If (Num n) t1 t2) (s, t1)) ∧
(!s.
  step_t (s, Handle Break) (s, Exp (Num 0))) ∧
(!s t.
  is_val_t t ∧
  t ≠ Break
 ⇒
 step_t (s, Handle t) (s, t)) ∧
(!s1 s2 t1 t2.
  step_t (s1, t1) (s2, t2)
 ⇒
 step_t (s1, Handle t1) (s2, Handle t2)) ∧
(!s e1 e2 t.
  step_t (s, For e1 e2 t) (s, Handle (If e1 (Seq t (Seq (Exp e2) (For e1 e2 t))) (Exp (Num 0)))))`;

val small_diverges_def = Define `
small_diverges t =
  ∀s1 t1. step_t^* (FEMPTY, t) (s1, t1) ⇒ ?s2 t2. step_t (s1, t1) (s2, t2)`;

val semantics_small_def = Define `
semantics_small t =
  let t = t_to_small_t t in
    case some s. step_t^* (FEMPTY, t) s ∧ ¬?s2 t2. step_t s (s2, t2) of
       | NONE => Diverge
       | SOME (s1, t1) =>
           case t1 of
              | Exp e => if is_val_e e then Terminate else Crash
              | _ => Crash`;

(* ----------- Connect to functional big step -------------- *)

val for_unload_def = Define `
  for_unload st =
    case SND st of
    | Break => NONE
    | Exp (Num n) => SOME n`;

val for_small_sem_def = Define `
  for_small_sem =
    <| step := (\st. some st'. step_t st st');
       is_value := (\st. is_val_t (SND st));
       load := (\t. (FEMPTY, t_to_small_t t));
       unload := for_unload |>`;

val for_eval_def = Define `
  for_eval st env t =
    case sem_t st t of
      (Rval v, s) => (s, Val (SOME v))
    | (Rbreak, s) => (s, Val NONE)
    | (Rtimeout, s) => (s, Timeout)
    | (Rfail, s) => (s, Error)`;

val for_big_sem_def = Define `
  for_big_sem =
    <| eval := for_eval;
       init_st := <| clock := 0; store := FEMPTY |>;
       init_env := ();
       get_clock := (\x. x.clock);
       set_clock := (\c st. st with clock := c);
       unload := I |>`;

val (res_rel_t_rules, res_rel_t_ind, res_rel_t_cases) = Hol_reln `
(!i s.
  res_rel_t (Rval i, s) (s.store, Exp (Num i))) ∧
(!s t.
  (~?s' t'. step_t (s.store, t) (s', t')) ∧
  ~is_val_t t
  ⇒
  res_rel_t (Rfail, s) (s.store, t)) ∧
(!s.
  res_rel_t (Rbreak, s) (s.store, Break)) ∧
(!s t.
  (?s' t'. step_t (s.store, t) (s', t')) ∧
  s.clock = 0
  ⇒
  res_rel_t (Rtimeout, s) (s.store, t))`;

val (res_rel_e_rules, res_rel_e_ind, res_rel_e_cases) = Hol_reln `
(!i s.
  res_rel_e (Rval i, s) (s.store, Num i)) ∧
(!s e.
  (~?s' e'. step_e (s.store, e) (s', e')) ∧
  ~is_val_e e
  ⇒
  res_rel_e (Rfail, s) (s.store, e))`

val _ = set_trace "Goalstack.print_goal_at_top" 0;

val step_t_strongind = (fetch "-" "step_t_strongind")
val step_e_strongind = (fetch "-" "step_e_strongind")

val etac = (fs[Once step_t_cases]>>fs[Once step_t_cases,Once step_e_cases])

(* Determinism of the small step relation *)
val step_e_determ = Q.prove(
` ∀se se1.
  step_e se se1 ⇒
  (∀se2.
  step_e se se2 ⇒ se1 = se2)`,
  ho_match_mp_tac step_e_strongind>>rw[]>>fs[FORALL_PROD]
  >-
    (fs[Once step_e_cases]>>rfs[])
  >-
    ntac 2(fs[Once step_e_cases]>>rfs[])
  >-
    (pop_assum mp_tac>>simp[Once step_e_cases]>>rw[]
    >-
      fs[is_val_e_def,Once step_e_cases]
    >-
      metis_tac[]
    >-
      (Cases_on`e1`>>fs[is_val_e_def,Once step_e_cases]))
  >-
    (pop_assum mp_tac>>simp[Once step_e_cases]>>rw[]
    >-
      fs[Once step_e_cases]
    >-
      (Cases_on`e1`>>fs[is_val_e_def,Once step_e_cases])
    >-
      metis_tac[])
  >-
    ntac 2 (fs[Once step_e_cases])
  >-
    (pop_assum mp_tac >> simp[Once step_e_cases]>>rw[]
    >-
      fs[Once step_e_cases]
    >-
      metis_tac[]))

val step_t_determ = Q.prove(
` ∀st st1.
  step_t st st1 ⇒
  (∀st2.
  step_t st st2 ⇒ st1 = st2)`,
  ho_match_mp_tac step_t_strongind >>rw[]
  >- etac
  >-
    (fs[Once step_t_cases]>>
    imp_res_tac step_e_determ>>
    fs[])
  >-
    (pop_assum mp_tac>>
    simp[Once step_t_cases]>>fs[FORALL_PROD]>>rw[]
    >-
      metis_tac[]
    >-
      fs[Once step_t_cases]
    >-
      fs[Once step_t_cases,Once step_e_cases])
  >- etac
  >- etac
  >-
    (fs[Once step_t_cases]
    >-
      (imp_res_tac step_e_determ>>fs[])
    >> etac)
  >- etac
  >- etac
  >- etac
  >-
    (fs[Once step_t_cases]>>rfs[]>>
    Cases_on`t`>>fs[is_val_t_def]>>
    Cases_on`e`>>fs[is_val_e_def]>>
    fs[Once step_t_cases]>>
    fs[Once step_e_cases])
  >-
    (pop_assum mp_tac>>
    simp[Once step_t_cases]>>rw[]
    >-
      etac
    >-
      (Cases_on`t1`>>fs[is_val_t_def]>>Cases_on`e`>>fs[is_val_e_def]>>
      fs[Once step_t_cases,Once step_e_cases])
    >>
      fs[FORALL_PROD]>>metis_tac[])
  >>
    fs[Once step_t_cases])

val step_t_select_unique = Q.prove(
`step_t (q,r) st' ⇒
 (@st'. step_t (q,r) st') = st'`,
 rw[]>>
 metis_tac[step_t_determ])

val some_to_SOME_step_e = Q.prove(
`step_e A B ⇒
 (some st'. step_e A st') =
 SOME B`,
 rw[]>>fs[some_def]>>
 metis_tac[step_e_determ]) |> GEN_ALL

val some_to_SOME_step_t = Q.prove(
`step_t A B ⇒
 (some st'. step_t A st') =
 SOME B`,
 rw[]>>fs[some_def]>>metis_tac[step_t_determ]) |>GEN_ALL

(* Contextual transitions of the small step semantics *)
val check_trace_seq = Q.prove(
`∀tr.
 check_trace (λst. some st'. step_t st st') tr ⇒
 check_trace (λst. some st'. step_t st st') (MAP (λst,t. (st,Seq t p)) tr)`,
 Induct>>rw[]>>
 Cases_on`tr`>>fs[check_trace_def]>>
 Cases_on`h`>>Cases_on`h'`>>
 match_mp_tac some_to_SOME_step_t>>
 fs[some_def]>>
 simp[Once step_t_cases]>>
 metis_tac[step_t_select_unique])

val check_trace_assign = Q.prove(
`∀tr.
 check_trace (λst. some st'. step_e st st') tr ⇒
 check_trace (λst. some st'. step_e st st') (MAP (λst,e. (st,Assign s e)) tr)`,
 Induct>>rw[]>>Cases_on`tr`>>fs[check_trace_def]>>
 Cases_on`h`>>Cases_on`h'`>>
 match_mp_tac some_to_SOME_step_e>>
 fs[some_def]>>
 simp[Once step_e_cases]>>
 metis_tac[step_e_determ])

val check_trace_add1 = Q.prove(
`∀tr.
 check_trace (λst. some st'. step_e st st') tr ⇒
 check_trace (λst. some st'. step_e st st') (MAP (λst,e. (st,Add e e')) tr)`,
 Induct>>rw[]>>Cases_on`tr`>>fs[check_trace_def]>>
 Cases_on`h`>>Cases_on`h'`>>
 match_mp_tac some_to_SOME_step_e>>
 fs[some_def]>>
 simp[Once step_e_cases]>>
 metis_tac[step_e_determ])

val check_trace_add2 = Q.prove(
`∀tr.
 check_trace (λst. some st'. step_e st st') tr ⇒
 check_trace (λst. some st'. step_e st st') (MAP (λst,e'. (st,Add (Num i) e')) tr)`,
 Induct>>rw[]>>Cases_on`tr`>>fs[check_trace_def]>>
 Cases_on`h`>>Cases_on`h'`>>
 match_mp_tac some_to_SOME_step_e>>
 fs[some_def]>>
 simp[Once step_e_cases]>>
 metis_tac[step_e_determ,is_val_e_def])

val check_trace_exp = Q.prove(
`∀tr.
 check_trace (λst. some st'. step_e st st') tr ⇒
 check_trace (λst. some st'. step_t st st') (MAP (λst,e'. (st,Exp e')) tr)`,
 Induct>>rw[check_trace_def]>>Cases_on`tr`>>fs[check_trace_def]>>
 Cases_on`h`>>Cases_on`h'`>>
 match_mp_tac some_to_SOME_step_t>>
 fs[some_def]>>
 simp[Once step_t_cases]>>
 metis_tac[step_e_determ])

val check_trace_if1 = Q.prove(
`∀tr.
 check_trace (λst. some st'. step_e st st') tr ⇒
 check_trace (λst. some st'. step_t st st') (MAP (λst,e'. (st,If e' a b)) tr)`,
 Induct>>rw[check_trace_def]>>Cases_on`tr`>>fs[check_trace_def]>>
 Cases_on`h`>>Cases_on`h'`>>
 match_mp_tac some_to_SOME_step_t>>
 fs[some_def]>>
 simp[Once step_t_cases]>>
 metis_tac[step_e_determ])

val check_trace_for1 = Q.prove(
`∀tr.
 check_trace (λst. some st'. step_e st st') tr ⇒
 check_trace (λst. some st'. step_t st st')
   (MAP (λst,e'. (st,
   Handle (If e' a b))) tr)`,
 Induct>>rw[check_trace_def]>>Cases_on`tr`>>fs[check_trace_def]>>
 Cases_on`h`>>Cases_on`h'`>>
 match_mp_tac some_to_SOME_step_t>>
 fs[some_def]>>
 simp[Once step_t_cases]>>
 simp[Once step_t_cases]>>
 metis_tac[step_e_determ])

val check_trace_for2 = Q.prove(
`∀tr.
 check_trace (λst. some st'. step_t st st') tr ⇒
 check_trace (λst. some st'. step_t st st')
   (MAP (λst,t'. (st,
   Handle (Seq t' a))) tr)`,
 Induct>>rw[check_trace_def]>>Cases_on`tr`>>fs[check_trace_def]>>
 Cases_on`h`>>Cases_on`h'`>>
 match_mp_tac some_to_SOME_step_t>>
 fs[some_def]>>
 simp[Once step_t_cases]>>
 simp[Once step_t_cases]>>
 metis_tac[step_e_determ])

val check_trace_for3 = Q.prove(
`∀tr.
 check_trace (λst. some st'. step_e st st') tr ⇒
 check_trace (λst. some st'. step_t st st')
   (MAP (λst,e'. (st,
   Handle (Seq (Exp e') a))) tr)`,
 Induct>>rw[check_trace_def]>>Cases_on`tr`>>fs[check_trace_def]>>
 Cases_on`h`>>Cases_on`h'`>>
 match_mp_tac some_to_SOME_step_t>>
 fs[some_def]>>
 ntac 3 (simp[Once step_t_cases])>>
 metis_tac[step_e_determ])

val check_trace_handle = Q.prove(
`∀tr.
 check_trace (λst. some st'. step_t st st') tr ⇒
 check_trace (λst. some st'. step_t st st')
   (MAP (λst,t'. (st,
   Handle t')) tr)`,
 Induct>>rw[check_trace_def]>>Cases_on`tr`>>fs[check_trace_def]>>
 Cases_on`h`>>Cases_on`h'`>>
 match_mp_tac some_to_SOME_step_t>>
 fs[some_def]>>
 simp[Once step_t_cases]>>
 Cases_on`st'`>>metis_tac[step_t_determ])

(* Non-existence of contextual transitions in small-step *)
val no_step_e_assign = Q.prove(
`∀e.
 (∀s' e'. ¬step_e (s,e) (s',e')) ∧
 ¬is_val_e e
 ⇒
 ∀s' e'. ¬step_e (s,Assign v e) (s',e')`,
 Induct>>rw[is_val_e_def]>>
 simp[Once step_e_cases])

val no_step_e_add1 = Q.prove(
`∀e.
 (∀s' e'. ¬step_e (s,e) (s',e')) ∧
 ¬is_val_e e
 ⇒
 ∀s' e'. ¬step_e (s,Add e e'') (s',e')`,
 Induct>>rw[is_val_e_def]>>simp[Once step_e_cases,is_val_e_def])

val no_step_e_add2 = Q.prove(
`∀e.
 (∀s' e'. ¬step_e (s,e) (s',e')) ∧
 ¬is_val_e e
 ⇒
 ∀s' e'. ¬step_e (s,Add (Num i) e) (s',e')`,
 Induct>>rw[is_val_e_def]>>
 rpt (simp[Once step_e_cases]))

val no_step_t_exp = Q.prove(
`∀e.
 (∀s' e'. ¬step_e (s,e) (s',e')) ∧
 ¬is_val_e e
 ⇒
 ∀s' t'. ¬step_t (s,Exp e) (s',t')`,
 Induct>>rw[is_val_e_def]>>
 simp[Once step_t_cases])

val no_step_t_seq = Q.prove(
`∀t.
 (∀s' t'. ¬step_t (s,t) (s',t')) ∧
 ¬is_val_t t
 ⇒
 ∀s' t'. ¬step_t (s,Seq t p) (s',t')`,
 Induct>>rw[is_val_t_def]>>
 simp[Once step_t_cases]>>
 Cases_on`e`>>fs[is_val_e_def])

val no_step_t_if1 = Q.prove(
`∀e.
 (∀s' e'. ¬step_e (s,e) (s',e')) ∧
 ¬is_val_e e
 ⇒
 ∀s' t'. ¬step_t (s,If e a b) (s',t')`,
 Induct>>rw[is_val_e_def]>>
 simp[Once step_t_cases])

val no_step_t_handle = Q.prove(
`∀t.
 (∀s' t'. ¬step_t (s,t) (s',t')) ∧
 ¬is_val_t t
 ⇒
 ∀s' t'. ¬step_t (s,Handle t) (s',t')`,
 Induct>>rw[is_val_t_def]>>
 simp[Once step_t_cases,is_val_t_def])

val LAST_MAP = Q.prove(
`∀ls. ls ≠ [] ⇒ LAST (MAP f ls) = f (LAST ls)`,
 Induct>>fs[LAST_DEF]>>rw[])

val HD_MAP = Q.prove(
`∀ls. ls ≠ [] ⇒ HD(MAP f ls) = f (HD ls)`,
 Induct>>rw[])

val HD_APPEND = Q.prove(
`ls ≠ [] ⇒ HD (ls ++ ls') = HD ls`,
Cases_on`ls`>>fs[])

val LAST_APPEND = Q.prove(
`ls' ≠ [] ⇒ LAST (ls ++ ls') = LAST ls'`,
Cases_on`ls'`>>fs[])

val sem_e_not_timeout = Q.prove (
`!st e r. sem_e st e ≠ (Rtimeout, r)`,
 Induct_on `e` >>
 rw [sem_e_def] >>
 ect >>
 fs [] >>
 metis_tac []);

val sem_e_not_break = Q.prove(
`!st e r. sem_e st e ≠ (Rbreak,r)`,
 Induct_on`e`>>rw[sem_e_def]>>
 ect>>
 fs[]>>metis_tac[]);

val LAST_HD_eq = Q.prove(`
∀ls ls'.
 ls ≠ [] ∧ ls' ≠ [] ∧
 LAST ls = HD ls' ⇒
 BUTLASTN 1 ls ++ ls' =
 ls ++ TL ls'`,
 Induct>>fs[LAST_DEF,BUTLASTN_1]>>rw[]>>
 Cases_on`ls'`>>fs[FRONT_DEF])

(* Start connecting functional big step to small step traces *)
val sem_e_big_small_lem = Q.prove(
`!s e r.
  sem_e s e = r
  ⇒
  ?tr.
    tr ≠ [] ∧
    check_trace (\st. some st'. step_e st st') tr ∧
    HD tr = (s.store, e) ∧
    res_rel_e r (LAST tr)`,
 Induct_on`e`>>rw[]>>fs[sem_e_def]
 >-
   (FULL_CASE_TAC>>fs[res_rel_e_cases]
   >-
     (qexists_tac`[(s'.store,Var s)]`>>fs[check_trace_def,is_val_e_def]>>
     simp[Once step_e_cases])
   >-
     (qexists_tac`[(s'.store,Var s);(s'.store,Num x)]`>>
     fs[check_trace_def,some_def]>>
     ntac 2 (simp[Once step_e_cases])))
 >-
   (fs[res_rel_e_cases]>>
   qexists_tac`[s.store,Num i]`>>fs[check_trace_def])
 >-
   (ntac 2 FULL_CASE_TAC>>Cases_on`q`>>fs[sem_e_not_break,sem_e_not_timeout]
   >-
     (FULL_CASE_TAC>>fs[sem_e_not_break,sem_e_not_timeout]>>
     last_x_assum(qspec_then`s` assume_tac)>>rfs[]>>
     last_x_assum(qspec_then`r` assume_tac)>>rfs[]>>
     qabbrev_tac`ls1 = (MAP (λst,e. (st,Add e e')) tr)`>>
     qabbrev_tac`ls2 = (MAP (λst,e'. (st,Add (Num i) e')) tr')`>>
     qabbrev_tac`ls = BUTLASTN 1 ls1 ++ ls2`>>
     fs[res_rel_e_cases]>>
     `LAST ls1 = HD ls2` by
       (unabbrev_all_tac>>fs[LAST_MAP,HD_MAP])>>
     `ls = ls1 ++ (TL ls2)` by
       (unabbrev_all_tac>>
       fs[LAST_HD_eq])
     >-
       (qexists_tac`ls ++ [(r'.store,Num(i+i'))]`>>reverse (rw[])
       >-
         fs[Abbr`ls1`,HD_MAP,HD_APPEND]
       >>
       match_mp_tac check_trace_append2>>fs[check_trace_def]>>rw[]
       >-
         (`check_trace (λst. some st'. step_e st st') ls2` by
           fs[check_trace_add2,Abbr`ls2`]>>
         Cases_on`ls2`>>fs[]>>Cases_on`t`>>fs[]
         >-
           metis_tac[check_trace_add1]
         >>
         match_mp_tac check_trace_append2>>fs[check_trace_def]>>rw[]>>
         fs[Abbr`ls1`]>>metis_tac[check_trace_add1])
       >-
         (qsuff_tac `LAST (ls1 ++ TL ls2) = LAST ls2`
         >-
         (fs[Abbr`ls2`,LAST_APPEND,LAST_MAP]>>rw[]>>
         `step_e (r'.store,Add (Num i) (Num i')) (r'.store,Num (i+i'))` by
           simp[Once step_e_cases]>>
         fs[some_def]>>
         metis_tac[step_e_determ])
         >>
         rfs[markerTheory.Abbrev_def,LAST_APPEND]))
     >>
       qexists_tac`ls`>>rw[]
       >-
         (unabbrev_all_tac>>fs[])
       >-
         (`check_trace (λst. some st'. step_e st st') ls2` by
           fs[check_trace_add2,Abbr`ls2`]>>
         Cases_on`ls2`>>fs[]>>Cases_on`t`>>fs[]
         >-
           metis_tac[check_trace_add1]
         >>
         match_mp_tac check_trace_append2>>fs[check_trace_def]>>rw[]>>
         metis_tac[check_trace_add1])
       >-
         fs[HD_APPEND,Abbr`ls1`,HD_MAP]
       >>
       unabbrev_all_tac>>
       fs[HD_MAP,HD_APPEND,LAST_APPEND,LAST_MAP,is_val_e_def]>>
       fs[no_step_e_add2])
   >>
     last_x_assum(qspec_then`s` assume_tac)>>rfs[]>>
     qexists_tac`(MAP (λst,e. (st,Add e e')) tr)`>>
     fs[HD_MAP,res_rel_e_cases,LAST_MAP,is_val_e_def,check_trace_add1,no_step_e_add1])
 >-
   (EVERY_CASE_TAC>>fs[res_rel_e_cases,sem_e_not_break,sem_e_not_timeout]>>
   first_x_assum(qspec_then`s'` assume_tac)>>rfs[]
   >-
     (qexists_tac`(MAP (λst,e. (st,Assign s e)) tr)++[(store_var s i r).store,Num i]`>>fs[HD_MAP,HD_APPEND]>>
     ho_match_mp_tac check_trace_append2>>
     fs[check_trace_def,LAST_MAP,check_trace_assign]>>
     ntac 2 (simp[Once step_e_cases,store_var_def]))
   >>
     (qexists_tac`(MAP (λst,e. (st,Assign s e)) tr)`>>
     fs[HD_MAP,LAST_MAP,is_val_e_def,no_step_e_assign,check_trace_assign])))

val sem_t_for_no_break = Q.prove(
 `∀s s'. sem_t s (For e1 e2 t) ≠ (Rbreak,s')`,
 completeInduct_on`s.clock`>>fs[sem_t_def_with_stop]>>
 rw[]>>FULL_CASE_TAC>>Cases_on`q`>>
 fs[sem_e_not_break,sem_e_not_timeout]>>
 IF_CASES_TAC>>fs[]>>
 FULL_CASE_TAC>>Cases_on`q`>>fs[]>>
 FULL_CASE_TAC>>Cases_on`q`>>fs[sem_e_not_break,sem_e_not_timeout]>>
 imp_res_tac sem_e_clock>>imp_res_tac sem_t_clock>>fs[]>>
 IF_CASES_TAC>>fs[dec_clock_def]>>
 simp[STOP_def]>>
 simp[sem_t_def_with_stop]>>
 fs[PULL_FORALL]>>
 first_x_assum(qspec_then `r'' with clock := r''.clock-1` mp_tac)>>
 fs[]>>
 `r''.clock < 1 + r.clock ∧ 0 < r.clock` by
   DECIDE_TAC>>
 fs[dec_clock_def])

val big_small_lem = Q.store_thm ("big_small_lem",
`!s t r.
  sem_t s t = r
  ⇒
  ?tr.
    tr ≠ [] ∧
    s.clock - (SND r).clock ≤ LENGTH tr ∧
    check_trace (\st. some st'. step_t st st') tr ∧
    HD tr = (s.store, (t_to_small_t t)) ∧
    res_rel_t r (LAST tr)`,

  ho_match_mp_tac sem_t_ind >>
  rw [sem_t_def_with_stop, t_to_small_t_def]
  >- (
    qabbrev_tac`r = sem_e s e`>>fs[markerTheory.Abbrev_def]>>
    pop_assum (assume_tac o SYM)>>
    imp_res_tac sem_e_big_small_lem>>
    Cases_on`r`>>
    qexists_tac`MAP (λst,e. (st,Exp e)) tr`>>
    imp_res_tac sem_e_clock>>fs[HD_MAP,LAST_MAP]>>
    CONJ_TAC >- fs[check_trace_exp] >>
    fs[res_rel_t_cases,res_rel_e_cases,no_step_t_exp,is_val_t_def]
    )
  >- (
    qpat_abbrev_tac`A = (s.store,B)`>>
    fs[store_var_def]>>
    qexists_tac`A::tr`>>fs[Abbr`A`,check_trace_def]>>
    TRY (CONJ_TAC >- DECIDE_TAC) >>
    reverse (CONJ_TAC) >- fs[LAST_DEF] >>
    Cases_on`tr`>>
    simp[check_trace_def,optionTheory.some_def]>>
    ntac 2 (simp[Once step_t_cases])>>
    fs[]
    )
  >- (
    qexists_tac`[s.store,Break]`>>fs[res_rel_t_cases,check_trace_def]
    )
  >- (
    EVERY_CASE_TAC>>fs[]
    >- (
      qpat_abbrev_tac`p = t_to_small_t t'`>>
      qexists_tac`MAP (λst,t. (st,Seq t p)) tr ++ tr'`>>
      fs[HD_MAP,HD_APPEND,LAST_APPEND]>>rw[] >>
      TRY (DECIDE_TAC)
      >- (
        match_mp_tac check_trace_append2>>
        fs[check_trace_seq,LAST_MAP]>>
        Cases_on`LAST tr`>>fs[]>>
        `step_t (q,Seq r' p) (q,p)` by (
          simp[Once step_t_cases]>>
          fs[res_rel_t_cases])>>
        `q = r.store` by fs[res_rel_t_cases]>>
        fs[some_def]>>
        metis_tac[step_t_select_unique]
        )
      )
    >- (
      qpat_abbrev_tac `p = t_to_small_t t'`>>
      qexists_tac`(MAP (λst,t. (st,Seq t p)) tr)++[r.store,Break]`>>
      fs[HD_APPEND,HD_MAP]>>rw[] >>
      TRY (DECIDE_TAC)
      >- (
        match_mp_tac check_trace_append2>>
        fs[check_trace_seq,LAST_MAP,check_trace_def]>>
        fs[res_rel_t_cases]>>
        `step_t (r.store, Seq Break p) (r.store,Break)` by
          fs[Once step_t_cases]>>
        metis_tac[step_t_select_unique,some_def]
        )
      >- fs[Once res_rel_t_cases]
      )
    >- (
      qpat_abbrev_tac `p = t_to_small_t t'`>>
      qexists_tac`(MAP (λst,t. (st,Seq t p)) tr)`>>
      fs[HD_APPEND,HD_MAP,check_trace_def,check_trace_seq]>>rw[]>>
      fs[Once res_rel_t_cases,LAST_MAP]>>
      rename1 `step_t _ (s',_)` >>
      `step_t (r.store,Seq t'' p) (s',Seq t''' p)` by simp[Once step_t_cases]>>
      metis_tac[]
      )
    >- (
      qpat_abbrev_tac `p = t_to_small_t t'`>>
      qexists_tac`(MAP (λst,t. (st,Seq t p)) tr)`>>
      fs[HD_APPEND,HD_MAP,check_trace_def,check_trace_seq]>>rw[]>>
      fs[Once res_rel_t_cases,LAST_MAP,is_val_t_def]>>
      metis_tac[no_step_t_seq]
      )
    )
  >- (
    EVERY_CASE_TAC>>fs[sem_e_not_break,sem_e_not_timeout]>>
    imp_res_tac sem_e_big_small_lem>>
    imp_res_tac sem_e_clock>>
    qpat_abbrev_tac`p1 = t_to_small_t t1`>>
    qpat_abbrev_tac`p2 = t_to_small_t t2`
    >- (
      qexists_tac`(MAP (λst,e. (st,(If e p1 p2))) tr') ++ tr`>>
      fs[HD_MAP,HD_APPEND,LAST_MAP,LAST_APPEND]>>rw[] >>
      TRY (DECIDE_TAC) >>
      match_mp_tac check_trace_append2>>fs[res_rel_e_cases]>>CONJ_TAC
      >- metis_tac[check_trace_if1] >>
      match_mp_tac some_to_SOME_step_t>>fs[LAST_MAP]>>
      simp[Once step_t_cases]
      )
    >- (
      qexists_tac`(MAP (λst,e. (st,(If e p1 p2))) tr') ++ tr`>>
      fs[HD_MAP,HD_APPEND,LAST_MAP,LAST_APPEND]>>rw[] >>
      TRY (DECIDE_TAC) >>
      match_mp_tac check_trace_append2>>fs[res_rel_e_cases]>>CONJ_TAC
      >- metis_tac[check_trace_if1] >>
      match_mp_tac some_to_SOME_step_t>>fs[LAST_MAP]>>
      simp[Once step_t_cases]
      )
    >- (
      qexists_tac`(MAP (λst,e. (st,(If e p1 p2))) tr)`>>rw[]>>
      fs[HD_MAP,res_rel_t_cases,LAST_MAP,res_rel_e_cases,is_val_t_def]>>
      metis_tac[check_trace_if1,no_step_t_if1]
      )
    )
  >- (
    reverse (
      Cases_on`sem_e s e1`>>Cases_on`q`>>fs[sem_e_not_break,sem_e_not_timeout]
      ) >>
    (*trace for e1*)
    imp_res_tac sem_e_big_small_lem>>
    imp_res_tac sem_e_clock>>
    qpat_abbrev_tac`p = t_to_small_t t`>>
    qabbrev_tac
      `e1tr = (MAP (λst,e. (st,Handle
        (If e (Seq p (Seq (Exp e2) (For e1 e2 p))) (Exp (Num 0))))) tr)`>>
    `check_trace (λst. some st'. step_t st st') e1tr` by
      metis_tac[check_trace_for1]>>
    qabbrev_tac`ls = [s.store,For e1 e2 p]`>>
    `check_trace (λst. some st'. step_t st st') (ls++e1tr)` by (
      match_mp_tac check_trace_append2>>unabbrev_all_tac>>
      fs[check_trace_def,HD_MAP]>>
      match_mp_tac some_to_SOME_step_t>>
      simp[Once step_t_cases])
    >- (
      qexists_tac` ls ++ e1tr`>>
      unabbrev_all_tac>>fs[res_rel_t_cases,LAST_DEF,LAST_MAP,HD_APPEND]>>
      fs[LAST_APPEND,LAST_MAP,res_rel_e_cases,is_val_t_def]>>
      match_mp_tac no_step_t_handle>>fs[is_val_t_def]>>
      metis_tac[no_step_t_if1]
      ) >>
    IF_CASES_TAC>>fs[]
    >- ( (*run out of time*)
      fs[res_rel_t_cases,res_rel_e_cases]>>
      qexists_tac` (ls ++ e1tr)
        ++ [(r.store,Handle (Exp (Num 0)));(r.store,Exp (Num 0))]`>>
      fs[LAST_APPEND,LAST_MAP]>>fs[]>>rw[]
      >- (
        match_mp_tac check_trace_append2>>rw[]
        >- (
          fs[check_trace_def]>>
          match_mp_tac some_to_SOME_step_t>>
          simp[Once step_t_cases,is_val_e_def,is_val_t_def]
          )
        >- (
          unabbrev_all_tac>>fs[LAST_APPEND,LAST_MAP]>>
          match_mp_tac some_to_SOME_step_t>>
          ntac 2 (simp[Once step_t_cases])
          )
        ) >>
      unabbrev_all_tac>>fs[HD_APPEND]
      ) >>
    reverse (Cases_on`sem_t r t`>>Cases_on`q`>>fs[]) >>
    qabbrev_tac`ttr =
      (MAP (λst,t. (st,Handle (Seq t (Seq (Exp e2) (For e1 e2 p))) ))) tr'`>>
    `check_trace (λst. some st'. step_t st st') ttr` by
      metis_tac[check_trace_for2]>>
    `check_trace (λst. some st'. step_t st st') (ls++e1tr++ttr)` by (
      match_mp_tac check_trace_append2>>
      fs[]>> unabbrev_all_tac>>
      fs[LAST_MAP,res_rel_e_cases,HD_MAP,LAST_DEF]>>
      match_mp_tac some_to_SOME_step_t>>
      ntac 2 (simp[Once step_t_cases])
      )
    >- (
      qexists_tac`ls++e1tr++ttr`>>unabbrev_all_tac>>
      fs[LAST_APPEND,LAST_MAP,res_rel_t_cases]>>CONJ_TAC >>
      TRY (DECIDE_TAC) >>
      fs[is_val_t_def]>>match_mp_tac no_step_t_handle>>
      fs[is_val_t_def]>>match_mp_tac no_step_t_seq>>
      metis_tac[]
      )
    >- (
      qexists_tac`ls++e1tr++ttr`>>unabbrev_all_tac>>
      fs[LAST_APPEND,LAST_MAP,res_rel_t_cases]>>
      TRY (CONJ_TAC >> DECIDE_TAC) >>
      ntac 2 (simp[Once step_t_cases,is_val_t_def])>>
      metis_tac[]
      )
    >- (
      qexists_tac
        `ls++e1tr++ttr++[(r'.store,Handle Break);(r'.store,Exp (Num 0))]`>>
      fs[LAST_APPEND,LAST_MAP,res_rel_t_cases]>>rw[]>>
      TRY(unabbrev_all_tac>>fs[]>>DECIDE_TAC)>>
      match_mp_tac check_trace_append2>>fs[check_trace_def]>>CONJ_TAC>>
      match_mp_tac some_to_SOME_step_t>>
      unabbrev_all_tac>>fs[LAST_APPEND,LAST_MAP,res_rel_t_cases]>>
      ntac 2 (simp[Once step_t_cases])
      ) >>
    (* continue executing *)
    reverse (Cases_on`sem_e r' e2`>>Cases_on`q`) >>
    fs[sem_e_not_break,sem_e_not_timeout]>>
    imp_res_tac sem_e_big_small_lem>>
    imp_res_tac sem_e_clock>>
    qabbrev_tac
      `e2tr = (MAP (λst,e. (st,Handle (Seq (Exp e) (For e1 e2 p)) ))) tr''`>>
    `check_trace (λst. some st'. step_t st st') e2tr` by
       metis_tac[check_trace_for3]>>
    `check_trace (λst. some st'. step_t st st') (ls++e1tr++ttr++e2tr)` by (
      match_mp_tac check_trace_append2>>fs[]>>
      match_mp_tac some_to_SOME_step_t>>
      unabbrev_all_tac>>fs[LAST_APPEND,LAST_MAP,HD_MAP,res_rel_t_cases]>>
      ntac 2 (simp[Once step_t_cases,res_rel_e_cases])
      )
    >- (
      qexists_tac`ls++e1tr++ttr++e2tr`>>fs[res_rel_e_cases]>>
      unabbrev_all_tac>>
      fs[LAST_APPEND,LAST_MAP,res_rel_t_cases,is_val_t_def]>>rw[] >>
      TRY (DECIDE_TAC) >>
      metis_tac[no_step_t_exp,no_step_t_handle, no_step_t_seq,is_val_t_def]
      ) >>
    (* e2 ok *)
    reverse (IF_CASES_TAC) >>fs[]
    >- ( (* clock ended *)
      fs[res_rel_t_cases]>>
      qexists_tac`ls++e1tr++ttr++e2tr`>>fs[]>>rw[]>>
      TRY (unabbrev_all_tac>>fs[]>>DECIDE_TAC)>>
      unabbrev_all_tac>>fs[LAST_APPEND,LAST_MAP,res_rel_e_cases]>>
      ntac 2 (simp[Once step_t_cases,is_val_t_def])>>
      metis_tac[]
      ) >>
    (* clock ok *)
    simp[STOP_def]>>
    simp[Once sem_t_def_with_stop]>>
    fs[dec_clock_def]>>
    (*Need a handle wrapper around rest of trace*)
    qabbrev_tac`ftr = MAP (λst,t. (st, Handle t))tr''''` >>
    `check_trace (λst. some st'. step_t st st') ftr` by
      metis_tac[check_trace_handle]>>
    `check_trace (λst. some st'. step_t st st') (ls++e1tr++ttr++e2tr++ftr)` by (
      match_mp_tac check_trace_append2>>fs[]>>
      match_mp_tac some_to_SOME_step_t>>
      unabbrev_all_tac>>fs[LAST_APPEND,LAST_MAP,HD_MAP]>>
      fs[res_rel_e_cases]>>
      ntac 2 (simp[Once step_t_cases])
      ) >>
    fs[res_rel_t_cases]
    (*Case split on the rest of loop*)
    >- (
      qexists_tac`ls ++ e1tr ++ ttr ++ e2tr ++ ftr++[s'.store,Exp (Num i''')]`>>
      fs[]>>rw[]
      >- (unabbrev_all_tac>>fs[]>>DECIDE_TAC)
      >- (
        match_mp_tac check_trace_append2>>fs[check_trace_def]>>
        match_mp_tac some_to_SOME_step_t>>unabbrev_all_tac>>
        fs[LAST_DEF,LAST_APPEND,LAST_MAP,res_rel_e_cases]>>
        simp[Once step_t_cases,is_val_t_def,is_val_e_def]
        )
      >- (unabbrev_all_tac>>fs[]>>DECIDE_TAC)
      >- simp[Once sem_t_def_with_stop,LAST_APPEND,dec_clock_def]
      )
    >- (
      qexists_tac`ls ++ e1tr++ttr++e2tr++ftr`>> reverse (fs[]>>rw[])
      >- (
        ntac 4 (simp[Once sem_t_def_with_stop,LAST_APPEND,dec_clock_def])>>
        unabbrev_all_tac>>fs[LAST_APPEND,LAST_MAP,is_val_t_def]>>
        match_mp_tac no_step_t_handle>>
        metis_tac[]
        ) >>
      unabbrev_all_tac>>fs[]>>DECIDE_TAC
      )
    >- ( (*break never occurs*)
      qpat_x_assum `A = (RBreak,s')` mp_tac>>
      FULL_CASE_TAC>>
      Cases_on`q`>> fs[sem_e_not_timeout,sem_e_not_break]>>
      IF_CASES_TAC>>fs[]>>
      FULL_CASE_TAC>>
      Cases_on`q`>> fs[sem_e_not_timeout,sem_e_not_break]>>
      FULL_CASE_TAC>>
      Cases_on`q`>> fs[sem_e_not_timeout,sem_e_not_break]>>
      IF_CASES_TAC>>fs[]>>
      simp[STOP_def]>>
      rw[] >> fs[] >>
      metis_tac[sem_t_for_no_break]
      )
    >- (
      qexists_tac`ls ++ e1tr ++ ttr ++ e2tr ++ ftr`>> reverse (fs[]>>rw[]) >>
      unabbrev_all_tac
      >- (
       ntac 3 (
        simp[Once sem_t_def_with_stop,LAST_APPEND,dec_clock_def,LAST_MAP])>>
       simp[Once step_t_cases]>>metis_tac[]
        ) >>
      fs[] >> DECIDE_TAC
      )
    )
  )

val big_timeout_0 = Q.prove (
`!st p r.
  sem_t st p = (Rtimeout,r)
  ⇒
  r.clock = 0`,
 ho_match_mp_tac sem_t_ind >>
 conj_tac >- (
   rw [sem_t_def_with_stop, sem_e_not_timeout]) >>
 conj_tac >- (
   rw [sem_t_def_with_stop, sem_e_not_timeout]) >>
 conj_tac >- (
   rw [sem_t_def_with_stop, sem_e_not_timeout] >>
   ect >> fs []) >>
 conj_tac >- (
   rw [sem_t_def_with_stop, sem_e_not_timeout] >>
   ect >> fs []) >>
 conj_tac >- (
   rw [sem_t_def_with_stop, sem_e_not_timeout] >>
   ect >> fs [sem_e_not_timeout])
 >- (
   rw [] >>
   pop_assum mp_tac >>
   simp [sem_t_def_with_stop] >>
   ect >>
   fs [sem_e_not_timeout, STOP_def] >>
   rw [] >>
   fs []));

val sem_equiv_lem = Q.store_thm ("sem_equiv_lem",
`∀prog. fbs_sem for_big_sem prog = small_sem for_small_sem prog`,
 match_mp_tac small_fbs_equiv2 >>
 conj_tac >- (
   rw [for_big_sem_def, eval_with_clock_def, for_eval_def] >>
   ect >>
   fs [] >>
   metis_tac [big_timeout_0]) >>
 qexists_tac `I` >>
 conj_tac
 >- (
   rw [unbounded_def] >>
   qexists_tac `SUC x` >>
   simp []) >>
 rpt gen_tac >>
 simp [for_big_sem_def, for_eval_def, eval_with_clock_def] >>
 DISCH_TAC >>
 ect >>
 imp_res_tac big_small_lem >>
 qexists_tac `tr` >>
 fs [for_small_sem_def] >>
 rw [same_result_def, for_unload_def] >>
 fs [res_rel_t_cases, is_val_t_def, is_val_e_def, some_no_choice] >>
 simp [] >>
 rw []
 >- (rw [Once step_t_cases] >>
     rw [Once step_e_cases])
 >- rw [Once step_t_cases]
 >- (rw [some_def] >>
     metis_tac [])
 >- metis_tac [PAIR]);

(* check traces are unique up to prefixing *)
val check_trace_determ = Q.prove(
`∀tr h f.
 check_trace f (h::tr) ⇒
 ∀tr'.
 LENGTH tr' ≤ LENGTH tr ∧
 check_trace f (h::tr') ⇒
 isPREFIX tr' tr`,
 Induct>>rw[]>>fs[check_clock_def,isPREFIX,LENGTH_NIL]>>
 Cases_on`tr'`>>fs[check_trace_def]>>
 metis_tac[])

val check_trace_prefixes = Q.prove(
`∀tr f.
 tr ≠ [] ∧
 check_trace f tr ⇒
 ∀tr'.
 tr' ≠ [] ∧ HD tr' = HD tr ∧
 check_trace f tr' ⇒
 isPREFIX tr tr' ∨ isPREFIX tr' tr`,
 rw[]>>
 Cases_on`tr`>>Cases_on`tr'`>>fs[]>>
 Cases_on`LENGTH t' ≤ LENGTH t`>>
 TRY(`LENGTH t ≤ LENGTH t'` by DECIDE_TAC)>>
 metis_tac[check_trace_determ])

val check_trace_TL = Q.prove(
`∀tr tr'.
 (tr ≠ [] ∧
 check_trace (λst. some st'. step_t st st') tr ∧
 (∀t'. ¬step_t (LAST tr) t') ∧
 check_trace (λst. some st'. step_t st st') tr' ∧
 isPREFIX tr tr') ⇒
 tr = tr'`,
 Induct>>fs[check_trace_def,LAST_DEF]>>rw[]>>Cases_on`tr'`>>fs[]
 >-
   (Cases_on`t`>>fs[check_trace_def,some_def]>>
   metis_tac[])
 >>
   Cases_on`tr`>>Cases_on`t`>>fs[check_trace_def]>>
   res_tac>>fs[])

val FST_SPLIT = Q.prove(
`FST x = y ⇒ ∃z. x = (y,z)`,
Cases_on`x`>>fs[])

val big_val_no_errors = Q.prove(
`!st p v s.
  sem_t st p = (Rval v,s)
  ⇒
  (∀c.
    (FST (sem_t (st with clock:= c) p) ≠ Rbreak)
  ∧ (FST (sem_t (st with clock:=c) p) ≠ Rfail))`,
  rw[]>>CCONTR_TAC>>fs[]>>imp_res_tac FST_SPLIT>>
  imp_res_tac big_small_lem>>
  `HD tr = HD tr'` by fs[]>>
  fs[res_rel_t_cases]>>
  `∀t'. ¬step_t (LAST tr) t'` by
    fs[Once step_t_cases,FORALL_PROD]>>
  `∀t'. ¬step_t (LAST tr') t'` by
    fs[Once step_t_cases,FORALL_PROD,Once step_e_cases]>>
  `isPREFIX tr tr' ∨ isPREFIX tr' tr` by
    metis_tac[check_trace_prefixes]>>
  `tr = tr'` by metis_tac[check_trace_TL]>>
  fs[]>>
  qpat_assum`A=t` (SUBST_ALL_TAC o SYM)>>fs[is_val_t_def,is_val_e_def])

(* Prove that the straightforward definition of the semantics are the same as
 * the ones used in the big/small equivalence *)

val to_obs_def = Define `
  (to_obs (Terminate NONE) = Crash) ∧
  (to_obs (Terminate _ ) = Terminate) ∧
  (to_obs Diverge = Diverge) ∧
  (to_obs Crash = Crash)`;

val some_SAT = Q.prove(
`!P y. (some x. P x) = SOME y ⇒ P y`,
rw[some_def,SELECT_THM]>>
metis_tac[SELECT_AX])

val sstac = first_assum (fn th => mp_tac (HO_MATCH_MP some_SAT th))

val fbs_equiv = Q.prove (
`!t. for$semantics t = to_obs (fbs_sem for_big_sem t)`,
 rw [semantics_def, to_obs_def, fbs_sem_def, for_big_sem_def] >>
 fs [to_obs_def, some_no_choice, eval_with_clock_def, for_eval_def, s_with_clock_def]>>ect>>
 fs[to_obs_def,some_no_choice]>>
 TRY(sstac>>fs[]>>NO_TAC)>>
 TRY(first_x_assum(qspec_then`x` mp_tac)>>fs[]>>NO_TAC)>>
 TRY(qpat_assum`A=a` (SUBST_ALL_TAC o SYM)>>fs[to_obs_def]>>NO_TAC)>>
 TRY(imp_res_tac big_val_no_errors>>fs[]>>metis_tac[FST])
 >- (pop_assum(qspec_then`c` mp_tac)>>fs[])
 >> (pop_assum(qspec_then`c` mp_tac)>>fs[]>>ect>>fs[]))

val check_trace_thm2 = Q.prove(
`∀s1 s2.
step_t^* s1 s2 ⇔ (λs1 s2.(some st'.step_t s1 st')= SOME s2)^* s1 s2`,
rw[]>>eq_tac>>qspec_tac (`s2`,`s2`) >>qspec_tac (`s1`,`s1`) >>
ho_match_mp_tac RTC_INDUCT>>rw[]>>simp[Once RTC_CASES1]>>
DISJ2_TAC>>
qexists_tac`s1'`>>
fs[some_to_SOME_step_t,some_def,step_t_determ]>>
metis_tac[SELECT_THM])

val some_not_step_t = Q.prove(
`(some s'.step_t s s') = NONE ⇔
 ∀s1 t1. ¬step_t s (s1,t1)`,
rw[some_def,FORALL_PROD])

val small_equiv_lem = Q.prove(
`
 (some s'.
 (step_t^* s s' ∧
 ∀s2 t2. ¬step_t s' (s2,t2)))
 =
 (some s'.
 (λs1 s2. (some st'. step_t s1 st') = SOME s2)^*
 s s' ∧ (some st'. step_t s' st') = NONE)`,
fs[check_trace_thm2,check_trace_thm,some_not_step_t])

val small_equiv = Q.prove (
`!t. semantics_small t = to_obs (small_sem for_small_sem t)`,
 rw [semantics_small_def, small_sem_def, for_small_sem_def] >>
 unabbrev_all_tac >>
 rw [] >>
 fs[small_equiv_lem]>>
 ect>>fs[to_obs_def,for_unload_def,is_val_t_def]>>
 Cases_on`e`>>fs[to_obs_def,is_val_e_def])

val sem_equiv_thm = Q.store_thm ("sem_equiv_thm",
`∀prog. for$semantics prog = semantics_small prog`,
 rw [small_equiv, fbs_equiv] >>
 metis_tac [sem_equiv_lem]);

(*Pretty printing*)
val hideseq_def = Define`
  hideseq = Seq`

val _ = save_thm ("step_t_rules_hideseq",step_t_rules |> REWRITE_RULE[GSYM hideseq_def])

val _ = export_theory ();
