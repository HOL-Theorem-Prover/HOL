open HolKernel Parse boolLib bossLib;
open optionTheory pairTheory pred_setTheory finite_mapTheory stringTheory;
open integerTheory listTheory optionTheory rich_listTheory;
open BasicProvers;
open for_ndTheory for_nd_semTheory oracleSemTheory simple_traceTheory;
open relationTheory;

val _ = new_theory "for_osmall";

val ect = BasicProvers.EVERY_CASE_TAC;
val fct = BasicProvers.FULL_CASE_TAC;

Triviality some_no_choice:
  !f. (some x. f x) = NONE ⇔ ¬?x. f x
Proof rw [some_def]
QED

Triviality some_SAT:
  !P y. (some x. P x) = SOME y ⇒ P y
Proof
  rw[some_def,SELECT_THM]>>
  metis_tac[SELECT_AX]
QED

(* A small step semantics for the non-deterministic FOR language with I/O *)

(* Add AddL and AddR to model making the choice one which sub-expression to
 * evaluate before starting the evaluation. Thus preventing switching in the
 * middle of evaluating one of them.
 *)
Datatype:
small_e =
  | Var string
  | Num int
  | Add small_e small_e
  | AddL small_e small_e
  | AddR small_e small_e
  | Assign string small_e
  | Getchar
  | Putchar small_e
End

(* Add a Handle statement that will stop breaks from propagating *)
Datatype:
small_t =
  | Dec string small_t
  | Exp small_e
  | Break
  | Seq small_t small_t
  | If small_e small_t small_t
  | For small_e small_e small_t
  | Handle small_t
End

Datatype: lab = ND bool | W char | R char
End

Definition e_to_small_e_def:
  e_to_small_e (Num i :e) = (Num i : small_e) ∧
  e_to_small_e (Var x) = Var x ∧
  e_to_small_e (Add e1 e2) = Add (e_to_small_e e1) (e_to_small_e e2) ∧
  e_to_small_e (Assign x e) = Assign x (e_to_small_e e) ∧
  e_to_small_e Getchar = Getchar ∧
  e_to_small_e (Putchar e) = Putchar (e_to_small_e e)
End

Definition t_to_small_t_def:
(t_to_small_t ((Dec string t):t) = ((Dec string (t_to_small_t t)) : small_t)) ∧
(t_to_small_t (Exp e) = Exp (e_to_small_e e)) ∧
(t_to_small_t Break = Break) ∧
(t_to_small_t (Seq t1 t2) = Seq (t_to_small_t t1) (t_to_small_t t2)) ∧
(t_to_small_t (If e t1 t2) = If (e_to_small_e e) (t_to_small_t t1) (t_to_small_t t2)) ∧
(t_to_small_t (For e1 e2 t) = For (e_to_small_e e1) (e_to_small_e e2) (t_to_small_t t))
End

Definition is_val_e_def:
  (is_val_e (Num n) = T) ∧
  (is_val_e _ = F)
End

Inductive step_e:
  (!s x n.
     FLOOKUP s.store x = SOME n
     ⇒
     step_e (s, Var x) NONE (s, Num n)) ∧
  (!s e1 e2 o'.
     oracle_get s.non_det_o = (F, o')
     ⇒
     step_e (s, Add e1 e2)
            (SOME (INR F))
            (s with <| non_det_o := o'; io_trace := s.io_trace ++ [INR F] |>,
             AddL e1 e2)) ∧
  (!s e1 e2 o'.
     oracle_get s.non_det_o = (T, o')
     ⇒
     step_e (s, Add e1 e2)
            (SOME (INR T))
            (s with <| non_det_o := o'; io_trace := s.io_trace ++ [INR T] |>,
             AddR e1 e2)) ∧
  (!s n1 n2.
     step_e (s, AddL (Num n1) (Num n2)) NONE (s, Num (n1 + n2))) ∧
  (!s n1 n2.
     step_e (s, AddR (Num n1) (Num n2)) NONE (s, Num (n1 + n2))) ∧
  (!s s2 e1 e2 e3 l.
     step_e (s, e1) l (s2, e3)
     ⇒
     step_e (s, AddL e1 e2) l (s2, AddL e3 e2)) ∧
  (!s s2 i e1 e2 l.
     step_e (s, e1) l (s2, e2)
     ⇒
     step_e (s, AddL (Num i) e1) l (s2, AddL (Num i) e2)) ∧
  (!s s2 i e1 e2 l.
     step_e (s, e1) l (s2, e2)
     ⇒
     step_e (s, AddR e1 (Num i)) l (s2, AddR e2 (Num i))) ∧
  (!s s2 e1 e2 e3 l.
     step_e (s, e2) l (s2, e3)
     ⇒
     step_e (s, AddR e1 e2) l (s2, AddR e1 e3)) ∧
  (!s x n.
     step_e (s, Assign x (Num n)) NONE
            (s with store := s.store |+ (x, n), Num n)) ∧
  (!s s2 x e1 e2 l.
     step_e (s, e1) l (s2, e2)
     ⇒
     step_e (s, Assign x e1) l (s2, Assign x e2)) ∧
  (!s i input'.
     getchar s.input = (i,input')
     ⇒
     step_e (s, Getchar)
            (SOME (INL (Itag i)))
            (s with <| input := input';
                       io_trace := s.io_trace ++ [INL (Itag i)] |>, Num i)) ∧
  (!s s2 e1 e2 l.
     step_e (s, e1) l (s2, e2)
     ⇒
     step_e (s, Putchar e1) l (s2, Putchar e2)) ∧
  (!s i.
     step_e (s, Putchar (Num i))
            (SOME (INL (Otag i)))
            (s with io_trace := s.io_trace ++ [INL (Otag i)], Num i))
End

Definition is_val_t_def:
  (is_val_t (Exp (e : small_e)) = is_val_e e) ∧
  (is_val_t Break = T) ∧
  (is_val_t _ = F)
End

Inductive step_t:
  (!s t x.
     step_t (s, Dec x t) NONE (s with store := s.store |+ (x, 0), t))
∧
  (!s s2 e e2 l.
     step_e (s, e) l (s2, e2)
  ⇒
     step_t (s, Exp e) l (s2, Exp e2))
∧
  (!s s2 t1 t2 t1' l.
     step_t (s, t1) l (s2, t1')
    ⇒
     step_t (s, Seq t1 t2) l (s2, Seq t1' t2))
∧
  (!s t. step_t (s, Seq Break t) NONE (s, Break))
∧
  (!s n t. step_t (s, Seq (Exp (Num n)) t) NONE (s, t))
∧
  (!s s2 e t1 t2 e2 l.
    step_e (s, e) l (s2,e2)
   ⇒
    step_t (s, If e t1 t2) l (s2, If e2 t1 t2))
∧
  (!s t1 t2.
    step_t (s, If (Num 0) t1 t2) NONE (s, t2))
∧
  (!s n t1 t2.
    n ≠ 0
    ⇒
    step_t (s, If (Num n) t1 t2) NONE (s, t1))
∧
  (!s.
    step_t (s, Handle Break) NONE (s, Exp (Num 0)))
∧
  (!s t.
    is_val_t t ∧
    t ≠ Break
    ⇒
    step_t (s, Handle t) NONE (s, t))
∧
  (!s1 s2 t1 t2 l.
    step_t (s1, t1) l (s2, t2)
    ⇒
    step_t (s1, Handle t1) l (s2, Handle t2))
∧
  (!s e1 e2 t.
    step_t
      (s, For e1 e2 t)
      NONE
      (s, Handle (If e1 (Seq t (Seq (Exp e2) (For e1 e2 t))) (Exp (Num 0)))))
End

Definition filter_map_def:
  filter_map f [] = [] ∧
  filter_map f (h::t) =
   case f h of
   | NONE => filter_map f t
   | SOME x => x :: filter_map f t
End

Definition path_to_obs_def:
  path_to_obs p =
    if ¬finite p then
      Diverge (lfilter_map I (labels p))
    else if is_val_t (SND (last p)) then
      Terminate (filter_map I (THE (toList (labels p))))
    else
      Crash
End

Definition semantics_small_def:
  semantics_small input prog =
    { path_to_obs p | p,nd |
      okpath step_t p ∧ complete step_t p ∧
      first p = (init_st 0 nd input, t_to_small_t prog)
    }
End

(* ----------- Connect to functional big step -------------- *)

Definition for_small_sem_def:
  for_small_sem input =
    <| step := (\st. some st'. ?l. step_t st l st');
       is_result := (\st. is_val_t (SND st));
       load := (\nd t. (init_st 0 nd input , t_to_small_t t));
       unload := (\st. (FST st).io_trace) |>
End

Definition for_eval_def:
  for_eval st env t =
    case sem_t st t of
      (Rval v, s) => (s, Val (SOME v))
    | (Rbreak, s) => (s, Val NONE)
    | (Rtimeout, s) => (s, Timeout)
    | (Rfail, s) => (s, Error)
End

Definition for_big_sem_def:
  for_big_sem input =
    <| eval := for_eval;
       init_st := (\nd. init_st 0 nd input);
       init_env := ();
       get_clock := (\x. x.clock);
       set_clock := (\c st. st with clock := c);
       get_oracle_events := (\st. st.io_trace) |>
End

Inductive res_rel_t:
(!i s.
  res_rel_t (Rval i, s) (s with clock := 0, Exp (Num i))) ∧
(!s t.
  (~?l s' t'. step_t (s with clock := 0, t) l (s', t')) ∧
  ~is_val_t t
  ⇒
  res_rel_t (Rfail, s) (s with clock := 0, t)) ∧
(!s.
  res_rel_t (Rbreak, s) (s with clock := 0, Break)) ∧
(!s t.
  (?l s' t'. step_t (s, t) l (s', t')) ∧
  s.clock = 0
  ⇒
  res_rel_t (Rtimeout, s) (s, t))
End

Inductive res_rel_e:
  (!i s.
    res_rel_e (Rval i, s) (s with clock:=0, Num i))
∧
  (!s e.
    (~?s' e' l. step_e (s, e) l (s', e')) ∧
    ~is_val_e e
  ⇒
    res_rel_e (Rfail, s) (s with clock:=0, e))
End

Definition conjs_def:
  conjs A B ⇔ A ∧ B
End

val etac = (fs[Once step_t_cases]>>fs[Once step_t_cases,Once step_e_cases,conjs_def])

(* Determinism of small-step w.r.t. an oracle *)

Theorem step_e_determ0[local]:
 ∀se l1 se1.
  step_e se l1 se1 ⇒
  (∀l2 se2.
  step_e se l2 se2 ⇒ conjs (se1 = se2) (l1 = l2))
Proof
  ho_match_mp_tac step_e_strongind>>rw[]>>fs[FORALL_PROD]
  >- (rw[conjs_def]>>fs[Once step_e_cases]>>rfs[])
  >- (rw[conjs_def]>>ntac 2(fs[Once step_e_cases]>>rfs[]))
  >- (rw[conjs_def]>>ntac 2(fs[Once step_e_cases]>>rfs[]))
  >- (rw[conjs_def]>>ntac 2(fs[Once step_e_cases]>>rfs[]))
  >- (rw[conjs_def]>>ntac 2(fs[Once step_e_cases]>>rfs[]))
  >>
  TRY
    (pop_assum mp_tac>>simp[Once step_e_cases]>>rw[]>>
    fs[Once step_e_cases])
  >>
  fs[conjs_def]
QED
Theorem step_e_determ = step_e_determ0 |>REWRITE_RULE[conjs_def]

Theorem step_t_determ0[local]:
 ∀st l1 st1.
  step_t st l1 st1 ⇒
  ∀l2 st2.
    step_t st l2 st2 ⇒ conjs (st1 = st2) (l1 = l2)
Proof
  ho_match_mp_tac step_t_strongind >>rw[]
  >- etac
  >-
    (fs[Once step_t_cases]>>
    imp_res_tac step_e_determ>>
    fs[conjs_def])
  >-
    (pop_assum mp_tac>>
    simp[Once step_t_cases]>>fs[FORALL_PROD]>>rw[]>>
    fs[Once step_t_cases,Once step_e_cases])
  >- etac
  >- etac
  >-
    (fs[Once step_t_cases]
    >-
      (imp_res_tac step_e_determ>>fs[conjs_def])
    >> etac)
  >- etac
  >- etac
  >- etac
  >-
    (fs[Once step_t_cases]>>rfs[conjs_def]>>
    Cases_on‘t’>>fs[is_val_t_def]>>
    Cases_on‘s'’>>fs[is_val_e_def]>>
    fs[Once step_t_cases]>>
    fs[Once step_e_cases])
  >-
    (pop_assum mp_tac>>
    simp[Once step_t_cases]>>rw[]
    >-
      etac
    >-
      (Cases_on‘t1’>>fs[is_val_t_def]>>Cases_on‘s’>>fs[is_val_e_def]>>
      fs[Once step_t_cases,Once step_e_cases])
    >>
      fs[FORALL_PROD]>>metis_tac[])
  >>
    fs[Once step_t_cases,conjs_def]
QED
Theorem step_t_determ = step_t_determ0 |>REWRITE_RULE[conjs_def]

Theorem step_t_select_unique[local]:
  step_t (q,r) l st' ⇒ (@st'. ∃l. step_t (q,r) l st') = st'
Proof rw[]>> metis_tac[step_t_determ]
QED

Theorem some_to_SOME_step_e[local]:
  ∀A l B. step_e A l B ⇒ (some st'. ∃l. step_e A l st') = SOME B
Proof rw[]>>fs[some_def]>> metis_tac[step_e_determ]
QED

Theorem some_to_SOME_step_t[local]:
  ∀A l B. step_t A l B ⇒ (some st'. ∃l. step_t A l st') = SOME B
Proof rw[]>>fs[some_def]>>metis_tac[step_t_determ]
QED

(* Contextual transitions of the small step semantics *)
Theorem check_trace_seq:
  ∀tr.
    check_trace (λst. some st'. ∃l. step_t st l st') tr ⇒
    check_trace (λst. some st'. ∃l. step_t st l st')
                (MAP (λst,t. (st,Seq t p)) tr)
Proof
 Induct>>rw[]>>
 Cases_on‘tr’>>fs[check_trace_def]>>
 Cases_on‘h’>>Cases_on‘h'’>>
 match_mp_tac some_to_SOME_step_t>>
 fs[some_def]>>
 simp[Once step_t_cases]>>
 metis_tac[step_t_select_unique]
QED

Theorem check_trace_assign:
  ∀tr.
    check_trace (λst. some st'. ?l. step_e st l st') tr ⇒
    check_trace (λst. some st'. ?l. step_e st l st')
                (MAP (λ(st,e). (st,Assign s e)) tr)
Proof
 Induct>>rw[]>>Cases_on‘tr’>>fs[check_trace_def]>>
 Cases_on‘h’>>Cases_on‘h'’>>
 match_mp_tac some_to_SOME_step_e>>
 fs[some_def]>>
 simp[Once step_e_cases]>>
 metis_tac[step_e_determ]
QED

Theorem check_trace_putchar:
  ∀tr.
    check_trace (λst. some st'. ?l. step_e st l st') tr ⇒
    check_trace (λst. some st'. ?l. step_e st l st')
                (MAP (λ(st,e). (st,Putchar e)) tr)
Proof
 Induct>>rw[]>>Cases_on‘tr’>>fs[check_trace_def]>>
 Cases_on‘h’>>Cases_on‘h'’>>
 match_mp_tac some_to_SOME_step_e>>
 fs[some_def]>>
 simp[Once step_e_cases]>>
 metis_tac[step_e_determ]
QED

Theorem check_trace_addl1:
  ∀tr.
    check_trace (λst. some st'. ?l. step_e st l st') tr ⇒
    check_trace (λst. some st'. ?l. step_e st l st')
                (MAP (λst,e. (st,AddL e e')) tr)
Proof
 Induct>>rw[]>>Cases_on‘tr’>>fs[check_trace_def]>>
 Cases_on‘h’>>Cases_on‘h'’>>
 match_mp_tac some_to_SOME_step_e>>
 fs[some_def]>>
 simp[Once step_e_cases]>>
 metis_tac[step_e_determ]
QED

Theorem check_trace_addl2:
  ∀tr.
    check_trace (λst. some st'. ?l. step_e st l st') tr ⇒
    check_trace (λst. some st'. ?l. step_e st l st')
                (MAP (λ(st,e'). (st,AddL (Num i) e')) tr)
Proof
 Induct>>rw[]>>Cases_on‘tr’>>fs[check_trace_def]>>
 Cases_on‘h’>>Cases_on‘h'’>>
 match_mp_tac some_to_SOME_step_e>>
 fs[some_def]>>
 simp[Once step_e_cases]>>
 metis_tac[step_e_determ]
QED

Theorem check_trace_addr1:
  ∀tr.
    check_trace (λst. some st'. ?l. step_e st l st') tr ⇒
    check_trace (λst. some st'. ?l. step_e st l st')
                (MAP (λ(st,e'). (st,AddR e e')) tr)
Proof
 Induct>>rw[]>>Cases_on‘tr’>>fs[check_trace_def]>>
 Cases_on‘h’>>Cases_on‘h'’>>
 match_mp_tac some_to_SOME_step_e>>
 fs[some_def]>>
 simp[Once step_e_cases]>>
 metis_tac[step_e_determ,is_val_e_def]
QED

Theorem check_trace_addr2:
  ∀tr.
    check_trace (λst. some st'. ?l. step_e st l st') tr ⇒
    check_trace (λst. some st'. ?l. step_e st l st')
                (MAP (λst,e'. (st,AddR e' (Num i))) tr)
Proof
 Induct>>rw[]>>Cases_on‘tr’>>fs[check_trace_def]>>
 Cases_on‘h’>>Cases_on‘h'’>>
 match_mp_tac some_to_SOME_step_e>>
 fs[some_def]>>
 simp[Once step_e_cases]>>
 metis_tac[step_e_determ,is_val_e_def]
QED

Theorem check_trace_exp:
  ∀tr.
    check_trace (λst. some st'. ?l. step_e st l st') tr ⇒
    check_trace (λst. some st'. ?l. step_t st l st')
                (MAP (λst,e'. (st,Exp e')) tr)
Proof
 Induct>>rw[check_trace_def]>>Cases_on‘tr’>>fs[check_trace_def]>>
 Cases_on‘h’>>Cases_on‘h'’>>
 match_mp_tac some_to_SOME_step_t>>
 fs[some_def]>>
 simp[Once step_t_cases]>>
 metis_tac[step_e_determ]
QED

Theorem check_trace_if1:
  ∀tr.
    check_trace (λst. some st'. ?l. step_e st l st') tr ⇒
    check_trace (λst. some st'. ?l. step_t st l st')
                (MAP (λst,e'. (st,If e' a b)) tr)
Proof
 Induct>>rw[check_trace_def]>>Cases_on‘tr’>>fs[check_trace_def]>>
 Cases_on‘h’>>Cases_on‘h'’>>
 match_mp_tac some_to_SOME_step_t>>
 fs[some_def]>>
 simp[Once step_t_cases]>>
 metis_tac[step_e_determ]
QED

Theorem check_trace_for1:
  ∀tr.
    check_trace (λst. some st'. ?l. step_e st l st') tr ⇒
    check_trace (λst. some st'. ?l. step_t st l st')
                (MAP (λst,e'. (st, Handle (If e' a b))) tr)
Proof
  Induct>>rw[check_trace_def]>>Cases_on‘tr’>>fs[check_trace_def]>>
  Cases_on‘h’>>Cases_on‘h'’>>
          match_mp_tac some_to_SOME_step_t>>
  fs[some_def]>>
  simp[Once step_t_cases]>>
  simp[Once step_t_cases]>>
  metis_tac[step_e_determ]
QED

Theorem check_trace_for2:
  ∀tr.
    check_trace (λst. some st'. ?l. step_t st l st') tr ⇒
    check_trace (λst. some st'. ?l. step_t st l st')
                (MAP (λst,t'. (st, Handle (Seq t' a))) tr)
Proof
 Induct>>rw[check_trace_def]>>Cases_on‘tr’>>fs[check_trace_def]>>
 Cases_on‘h’>>Cases_on‘h'’>>
 match_mp_tac some_to_SOME_step_t>>
 fs[some_def]>>
 simp[Once step_t_cases]>>
 simp[Once step_t_cases]>>
 metis_tac[step_e_determ]
QED

Theorem check_trace_for3:
  ∀tr.
    check_trace (λst. some st'. ?l. step_e st l st') tr ⇒
    check_trace (λst. some st'. ?l. step_t st l st')
                (MAP (λst,e'. (st, Handle (Seq (Exp e') a))) tr)
Proof
 Induct>>rw[check_trace_def]>>Cases_on‘tr’>>fs[check_trace_def]>>
 Cases_on‘h’>>Cases_on‘h'’>>
 match_mp_tac some_to_SOME_step_t>>
 fs[some_def]>>
 ntac 3 (simp[Once step_t_cases])>>
 metis_tac[step_e_determ]
QED

Theorem check_trace_handle:
  ∀tr.
    check_trace (λst. some st'. ?l. step_t st l st') tr ⇒
    check_trace (λst. some st'. ?l. step_t st l st')
                (MAP (λst,t'. (st, Handle t')) tr)
Proof
 Induct>>rw[check_trace_def]>>Cases_on‘tr’>>fs[check_trace_def]>>
 Cases_on‘h’>>Cases_on‘h'’>>
 match_mp_tac some_to_SOME_step_t>>
 fs[some_def]>>
 simp[Once step_t_cases]>>
 Cases_on‘st'’>>metis_tac[step_t_determ]
QED

(* Non-existence of contextual transitions in small-step *)
Theorem no_step_e_assign:
  ∀e.
    (∀s' e' l. ¬step_e (s,e) l (s',e')) ∧ ¬is_val_e e
    ⇒
    ∀s' e' l. ¬step_e (s,Assign v e) l (s',e')
Proof
 Induct>>rw[is_val_e_def]>> simp[Once step_e_cases]
QED

Theorem no_step_e_putchar:
  ∀e.
    (∀s' e' l. ¬step_e (s,e) l (s',e')) ∧
    ¬is_val_e e
    ⇒
    ∀s' e' l. ¬step_e (s,Putchar e) l (s',e')
Proof
 Induct>>rw[is_val_e_def]>>
 simp[Once step_e_cases]
QED

Theorem no_step_e_addl1:
  ∀e.
    (∀s' e' l. ¬step_e (s,e) l (s',e')) ∧
    ¬is_val_e e
    ⇒
    ∀s' e' l. ¬step_e (s,AddL e e'') l (s',e')
Proof Induct>>rw[is_val_e_def]>>simp[Once step_e_cases,is_val_e_def]
QED

Theorem no_step_e_addl2:
  ∀e.
    (∀s' e' l. ¬step_e (s,e) l (s',e')) ∧
    ¬is_val_e e
    ⇒
    ∀s' e' l. ¬step_e (s,AddL (Num i) e) l (s',e')
Proof Induct>>rw[is_val_e_def]>>rpt (simp[Once step_e_cases,is_val_e_def])
QED

Theorem no_step_e_addr1:
  ∀e.
    (∀s' e' l. ¬step_e (s,e) l (s',e')) ∧
    ¬is_val_e e
    ⇒
    ∀s' e' l. ¬step_e (s,AddR e'' e) l (s',e')
Proof
 Induct>>rw[is_val_e_def]>>
 rpt (simp[Once step_e_cases])
QED

Theorem no_step_e_addr2:
  ∀e.
    (∀s' e' l. ¬step_e (s,e) l (s',e')) ∧
    ¬is_val_e e
    ⇒
    ∀s' e' l. ¬step_e (s,AddR e (Num i)) l (s',e')
Proof
 Induct>>rw[is_val_e_def]>>
 rpt (simp[Once step_e_cases])
QED

Theorem no_step_t_exp:
  ∀e.
    (∀s' e' l. ¬step_e (s,e) l (s',e')) ∧
    ¬is_val_e e
    ⇒
    ∀s' t' l. ¬step_t (s,Exp e) l (s',t')
Proof
 Induct>>rw[is_val_e_def]>>
 simp[Once step_t_cases]
QED

Theorem no_step_t_seq:
  ∀t.
    (∀s' t' l. ¬step_t (s,t) l (s',t')) ∧
    ¬is_val_t t
    ⇒
    ∀s' t' l. ¬step_t (s,Seq t p) l (s',t')
Proof
 Induct>>rw[is_val_t_def]>>
 simp[Once step_t_cases]>>
 Cases_on‘s'’>>fs[is_val_e_def]
QED

Theorem no_step_t_if1:
  ∀e.
    (∀s' e' l. ¬step_e (s,e) l (s',e')) ∧
    ¬is_val_e e
    ⇒
    ∀s' t' l. ¬step_t (s,If e a b) l (s',t')
Proof
 Induct>>rw[is_val_e_def]>>
 simp[Once step_t_cases]
QED

Theorem no_step_t_handle:
  ∀t.
    (∀s' t' l. ¬step_t (s,t) l (s',t')) ∧
    ¬is_val_t t
    ⇒
    ∀s' t' l. ¬step_t (s,Handle t) l (s',t')
Proof
 Induct>>rw[is_val_t_def]>>
 simp[Once step_t_cases,is_val_t_def]
QED

Theorem HD_MAP[local]: ∀ls. ls ≠ [] ⇒ HD(MAP f ls) = f (HD ls)
Proof Cases >> rw[]
QED

Theorem HD_APPEND[local]: ls ≠ [] ⇒ HD (ls ++ ls') = HD ls
Proof Cases_on‘ls’>>fs[]
QED

Theorem LAST_APPEND[local]: ls' ≠ [] ⇒ LAST (ls ++ ls') = LAST ls'
Proof Cases_on‘ls'’>>fs[]
QED

Triviality sem_e_not_timeout:
  !st e r. sem_e st e ≠ (Rtimeout, r)
Proof
  Induct_on ‘e’ >>
  rw [sem_e_def, LET_THM, permute_pair_def, oracle_get_def, unpermute_pair_def,
      getchar_def] >>
  ect >>
  fs [] >>
  metis_tac []
QED

Triviality sem_e_not_break:
  !st e r. sem_e st e ≠ (Rbreak,r)
Proof
  Induct_on‘e’>>srw_tac[][sem_e_def]>>
  ect>>
  fs[LET_THM,unpermute_pair_def,permute_pair_def,oracle_get_def] >>
  qpat_x_assum ‘_ = (fst_e,snd_e)’ mp_tac >> rw[] >>
  rename1 ‘sem_e st' _ = (Rbreak, new_r)’ >>
  first_x_assum (qspecl_then [‘st'’,‘new_r’] assume_tac) >>
  first_x_assum (qspecl_then [‘st'’,‘new_r’] assume_tac) >>
  fs[]
QED

Triviality LAST_HD_eq:
  ∀ls ls'.
    ls ≠ [] ∧ ls' ≠ [] ∧
    LAST ls = HD ls' ⇒
    BUTLASTN 1 ls ++ ls' =
    ls ++ TL ls'
Proof
  Induct>>fs[LAST_DEF,BUTLASTN_1]>>rw[]>>
  Cases_on‘ls'’>>fs[FRONT_DEF]
QED

Triviality check_trace_append3:
  check_trace f ls ∧
  f h = SOME (HD ls) ⇒
  check_trace f (h :: ls)
Proof
  rw[]>>imp_res_tac check_trace_append2>>
  pop_assum(qspec_then‘[h]’assume_tac)>>fs[]>>
  rfs[check_trace_def]
QED

Triviality check_trace_tl:
  check_trace f ls ∧ ls ≠ [] ⇒
  check_trace f (TL ls)
Proof
  Cases_on‘ls’>>fs[check_trace_def]>>
  Cases_on‘t’>>fs[check_trace_def]
QED

(* Start connecting functional big step to small step traces *)
local val rw = srw_tac[] val fs = fsrw_tac[] in
Theorem sem_e_big_small_lem[local]:
  !s e r. sem_e s e = r ⇒
          ?tr.
            tr ≠ [] ∧
            check_trace (\st. some st'. ?l. step_e st l st') tr ∧
            HD tr = (s with clock:=0, e_to_small_e e) ∧
            res_rel_e r (LAST tr)
Proof
 Induct_on‘e’>>rw[]>>fs[sem_e_def,e_to_small_e_def]
  >- (
    fct>>fs[res_rel_e_cases]
    >- (
      qexists_tac‘[(s' with clock:=0,Var s)]’>>fs[check_trace_def,is_val_e_def]>>
      simp[Once step_e_cases]
      )
    >- (
      qexists_tac‘[(s' with clock:=0,Var s);(s' with clock:=0,Num x)]’>>
      fs[check_trace_def,some_def]>>
      ntac 2 (simp[Once step_e_cases])
      )
    )
  >- (
    fs[res_rel_e_cases]>>
    qexists_tac‘[s with clock:=0,Num i]’>>fs[check_trace_def]
    )
  >- (
    fs[LET_THM,permute_pair_def,oracle_get_def]>>IF_CASES_TAC>>fs[]
    >- (
      qpat_abbrev_tac‘st = s with <|io_trace:=B;non_det_o:=C|>’>>
      first_x_assum(qspec_then‘st’assume_tac)>>
      Cases_on‘sem_e st e'’>>Cases_on‘q’>>
      fs[sem_e_not_break,sem_e_not_timeout,unpermute_pair_def]
      >- (
        fct>>Cases_on‘q’>>
        fs[sem_e_not_break,sem_e_not_timeout]>>
        last_x_assum(qspec_then‘r’ assume_tac)>>rfs[]>>
        qpat_abbrev_tac‘h =(A,B)’>>
        qabbrev_tac‘ls1 = (MAP (λst,e'. (st,AddR (e_to_small_e e) e')) tr)’>>
        qabbrev_tac‘ls2 = (MAP (λst,e'. (st,AddR e' (Num i))) tr')’>>
        qabbrev_tac‘ls = BUTLASTN 1 ls1 ++ ls2’>>
        fs[res_rel_e_cases]>>
        ‘LAST ls1 = HD ls2’ by (unabbrev_all_tac>>fs[LAST_MAP,HD_MAP])>>
        ‘ls = ls1 ++ (TL ls2)’ by (unabbrev_all_tac>> fs[LAST_HD_eq])>>
        ‘check_trace (λst. some st'. ∃l. step_e st l st') ls2’ by
          fs[Abbr‘ls2’,check_trace_addr2]>>
        ‘check_trace (λst. some st'. ∃l. step_e st l st') ls’
          by (fs[Abbr‘ls’]>>Cases_on‘ls2’>>fs[]>>Cases_on‘t’>>fs[]
              >- fs[check_trace_addr1,Abbr‘ls1’] >>
              match_mp_tac check_trace_append2>>rw[]
              >- fs[check_trace_addr1,Abbr‘ls1’]
              >- (fs[markerTheory.Abbrev_def]>>
                  ‘h''::t' = TL (LAST ls1::h''::t')’ by fs[]>>
                  pop_assum SUBST_ALL_TAC>>
                  match_mp_tac check_trace_tl>>fs[check_trace_addr2]) >>
              fs[check_trace_def])
        >- (
          qexists_tac‘[h] ++ ls ++ [(r' with clock:=0,Num(i'+i))]’>>
          rw[]>>
          match_mp_tac check_trace_append3>>fs[check_trace_def]>>rw[]
          >- (
            match_mp_tac check_trace_append2>>
            fs[check_trace_def]>>
            qpat_x_assum ‘BUTLASTN _ _ ++ _ = _’ (REWRITE_TAC o single o SYM) >>
            fs[markerTheory.Abbrev_def,LAST_APPEND,LAST_MAP]>>
            match_mp_tac some_to_SOME_step_e>>
            simp[Once step_e_cases]
            ) >>
          match_mp_tac some_to_SOME_step_e>>
          fs[HD_APPEND,Abbr‘ls1’,HD_MAP,Abbr‘h’,Abbr‘st’]>>
          simp[Once step_e_cases,oracle_get_def]
          ) >>
        qexists_tac‘[h]++ls’ >>rw[]
        >- (
          match_mp_tac check_trace_append3>>
          fs[HD_APPEND,Abbr‘ls1’,HD_MAP]>>
          match_mp_tac some_to_SOME_step_e>>
          fs[Abbr‘h’,Abbr‘st’]>>
          simp[Once step_e_cases,oracle_get_def]
          ) >>
        qpat_x_assum ‘BUTLASTN 1 _ ++ _ = _’ (REWRITE_TAC o single o SYM) >>
        fs[markerTheory.Abbrev_def,LAST_DEF,LAST_APPEND,LAST_MAP,
           is_val_e_def,no_step_e_addr2]
        )
      >- (
        qpat_abbrev_tac‘h =(A,B)’>>
        qexists_tac‘[h]++(MAP (λst,e'. (st,AddR (e_to_small_e e) e')) tr)’>>
        fs[HD_MAP,res_rel_e_cases,LAST_MAP,is_val_e_def,
           LAST_APPEND,no_step_e_addr1]>>
        match_mp_tac check_trace_append3>>fs[check_trace_addr1,HD_MAP]>>
        match_mp_tac some_to_SOME_step_e>>
        unabbrev_all_tac>>
        simp[Once step_e_cases,oracle_get_def]
        )
      )
    >- (
      (*symmetric*)
      qpat_abbrev_tac‘st = s with <|io_trace:=B;non_det_o:=C|>’>>
      last_x_assum(qspec_then‘st’assume_tac)>>
      Cases_on‘sem_e st e’>>Cases_on‘q’>>
      fs[sem_e_not_break,sem_e_not_timeout,unpermute_pair_def]
      >- (
        fct>>Cases_on‘q’>>
        fs[sem_e_not_break,sem_e_not_timeout]>>
        last_x_assum(qspec_then‘r’ assume_tac)>>rfs[]>>
        qpat_abbrev_tac‘h =(A,B)’>>
        qabbrev_tac‘ls1 = (MAP (λst,e. (st,AddL e (e_to_small_e e'))) tr)’>>
        qabbrev_tac‘ls2 = (MAP (λst,e'. (st,AddL (Num i) e')) tr')’>>
        qabbrev_tac‘ls = BUTLASTN 1 ls1 ++ ls2’>>
        fs[res_rel_e_cases]>>
        ‘LAST ls1 = HD ls2’ by (unabbrev_all_tac>>fs[LAST_MAP,HD_MAP])>>
        ‘ls = ls1 ++ (TL ls2)’ by (unabbrev_all_tac>> fs[LAST_HD_eq])>>
        ‘check_trace (λst. some st'. ∃l. step_e st l st') ls2’ by
        fs[Abbr‘ls2’,check_trace_addl2]>>
        ‘check_trace (λst. some st'. ∃l. step_e st l st') ls’ by (
          fs[Abbr‘ls’]>>Cases_on‘ls2’>>fs[]>>Cases_on‘t’>>fs[]
          >- fs[check_trace_addl1,Abbr‘ls1’] >>
          match_mp_tac check_trace_append2>>rw[]
          >- fs[check_trace_addl1,Abbr‘ls1’]
          >- (
            fs[markerTheory.Abbrev_def]>>
            ‘h''::t' = TL (LAST ls1::h''::t')’ by fs[]>>
            pop_assum SUBST_ALL_TAC>>
            match_mp_tac check_trace_tl>>fs[check_trace_addr2]
            ) >>
          fs[check_trace_def]
          )
        >- (
          qexists_tac‘[h] ++ ls ++ [(r' with clock:=0,Num(i+i'))]’>>
          rw[]>>
          match_mp_tac check_trace_append3>>fs[check_trace_def]>>rw[]
          >- (
            match_mp_tac check_trace_append2>>
            fs[check_trace_def]>>
            qpat_x_assum ‘BUTLASTN _ _ ++ _ = _’ (REWRITE_TAC o single o SYM) >>
            fs[markerTheory.Abbrev_def,LAST_APPEND,LAST_MAP]>>
            match_mp_tac some_to_SOME_step_e>>
            simp[Once step_e_cases]
            ) >>
          match_mp_tac some_to_SOME_step_e>>
          fs[HD_APPEND,Abbr‘ls1’,HD_MAP,Abbr‘h’,Abbr‘st’]>>
          simp[Once step_e_cases,oracle_get_def]
          )
        >- (
          qexists_tac‘[h]++ls’ >>rw[]
          >- (
            match_mp_tac check_trace_append3>>
            fs[HD_APPEND,Abbr‘ls1’,HD_MAP]>>
            match_mp_tac some_to_SOME_step_e>>
            fs[Abbr‘h’,Abbr‘st’]>>
            simp[Once step_e_cases,oracle_get_def]
            ) >>
          qpat_x_assum ‘BUTLASTN _ _ ++ _ = _’ (REWRITE_TAC o single o SYM) >>
          fs[markerTheory.Abbrev_def,LAST_DEF,LAST_APPEND,LAST_MAP,
             is_val_e_def,no_step_e_addl2]
          )
        )
      >- (
        qpat_abbrev_tac‘h =(A,B)’>>
        qexists_tac‘[h]++(MAP (λst,e. (st,AddL e (e_to_small_e e'))) tr)’>>
        fs[HD_MAP,res_rel_e_cases,LAST_MAP,is_val_e_def,LAST_APPEND,
           no_step_e_addl1]>>
        match_mp_tac check_trace_append3>>fs[check_trace_addl1,HD_MAP]>>
        match_mp_tac some_to_SOME_step_e>>
        unabbrev_all_tac>>
        simp[Once step_e_cases,oracle_get_def]
        )
      )
    )
  >- (
    EVERY_CASE_TAC>>fs[res_rel_e_cases,sem_e_not_break,sem_e_not_timeout]>>
    first_x_assum(qspec_then‘s'’ assume_tac)>>rfs[]
    >- (
      qexists_tac‘(MAP (λst,e. (st,Assign s e)) tr)++
        [r with <|store :=r.store |+ (s,i); clock:=0|>,Num i]’>>
      fs[HD_MAP,HD_APPEND]>>
      ho_match_mp_tac check_trace_append2>>
      fs[check_trace_def,LAST_MAP,check_trace_assign]>>
      ntac 2 (simp[Once step_e_cases])
      ) >>
      (
        qexists_tac‘(MAP (λst,e. (st,Assign s e)) tr)’>>
        fs[HD_MAP,LAST_MAP,is_val_e_def,no_step_e_assign,check_trace_assign]
      )
    )
  >- (
    Cases_on‘getchar s.input’>>fs[LET_THM,res_rel_e_cases]>>
    qpat_abbrev_tac‘t = (A,B)’>>
    qpat_abbrev_tac‘t' = (A,B)’>>
    qexists_tac‘[t;t']’>>unabbrev_all_tac>>fs[check_trace_def]>>
    match_mp_tac some_to_SOME_step_e>>
    simp[Once step_e_cases]
    )
  >- (
    first_x_assum(qspec_then‘s’ assume_tac)>>fs[]>>
    Cases_on‘sem_e s e’>>Cases_on‘q’>>fs[sem_e_not_break,sem_e_not_timeout]>>
    qpat_abbrev_tac‘t = (A,B)’>>
    qpat_abbrev_tac‘t' = (A,B)’
    >- (
      qexists_tac‘MAP (λst,e. (st,Putchar e)) tr ++
        [(r with <|io_trace := r.io_trace ++ [INL(Otag i)];clock:=0|>,Num i)]’>>
      fs[HD_MAP,HD_APPEND,Abbr‘t'’,res_rel_e_cases]>>
      ho_match_mp_tac check_trace_append2>>
      fs[check_trace_def,LAST_MAP,check_trace_putchar]>>
      ntac 2 (simp[Once step_e_cases])
      ) >>
    qexists_tac‘MAP (λst,e. (st,Putchar e)) tr’>>unabbrev_all_tac>>
    fs[HD_MAP,res_rel_e_cases,LAST_MAP,is_val_e_def,check_trace_putchar,
       no_step_e_putchar]
    )
QED
end

Triviality sem_t_for_no_break:
  ∀s s'. sem_t s (For e1 e2 t) ≠ (Rbreak,s')
Proof
 completeInduct_on‘s.clock’>>fs[sem_t_def_with_stop]>>
 rw[]>>fct>>Cases_on‘q’>>
 fs[sem_e_not_break,sem_e_not_timeout]>>
 IF_CASES_TAC>>fs[]>>
 fct>>Cases_on‘q’>>fs[]>>
 fct>>Cases_on‘q’>>fs[sem_e_not_break,sem_e_not_timeout]>>
 imp_res_tac sem_e_clock>>imp_res_tac sem_t_clock>>fs[]>>
 IF_CASES_TAC>>fs[dec_clock_def]>>
 simp[STOP_def]>>
 simp[sem_t_def_with_stop]>>
 fs[PULL_FORALL]>>
 first_x_assum(qspec_then ‘r'' with clock := r''.clock-1’ mp_tac)>>
 fs[]>>
 ‘r''.clock < 1 + r.clock ∧ 0 < r.clock’ by
   DECIDE_TAC>>
 fs[dec_clock_def]
QED

Triviality step_e_clock:
  ∀se l1 se'.
    step_e se l1 se' ⇒
    ∀s e s' e'.
      se = (s,e) ∧
      se' = (s',e') ⇒
      ∀c.
         step_e (s with clock:=c,e) l1 (s' with clock:=c,e')
Proof
  ho_match_mp_tac step_e_strongind>>rw[]>>
  simp[Once step_e_cases]
QED

Triviality step_e_zero_clock:
  (∀s e l. ¬step_e (r,e') l (s,e)) ⇒
  ∀s e l. ¬step_e (r with clock:=0,e') l (s,e)
Proof
  rw[]>>CCONTR_TAC>>fs[]>>imp_res_tac step_e_clock>>fs[]>>
  pop_assum(qspec_then‘r.clock’assume_tac)>>fs[]>>
  ‘r with clock:= r.clock = r’ by fs[state_component_equality]>>
  metis_tac[]
QED

Triviality big_small_lem:
  !s t r.
    sem_t s t = r
    ⇒
    ?tr.
      tr ≠ [] ∧
      s.clock - (SND r).clock ≤ LENGTH tr ∧
      check_trace (\st. some st'. ?l. step_t st l st') tr ∧
      HD tr = (s with clock := 0, (t_to_small_t t)) ∧
      res_rel_t r (LAST tr)
Proof
 ho_match_mp_tac sem_t_ind >>
 rw [sem_t_def_with_stop, t_to_small_t_def]
 >-
   (qabbrev_tac‘r = sem_e s e’>>fs[markerTheory.Abbrev_def]>>
   pop_assum (assume_tac o SYM)>>
   imp_res_tac sem_e_big_small_lem>>
   Cases_on‘r’>>
   qexists_tac‘MAP (λst,e. (st,Exp e)) tr’>>
   imp_res_tac sem_e_clock>>fs[HD_MAP,LAST_MAP]>>
   CONJ_TAC>-
     fs[check_trace_exp]
   >>
   fs[res_rel_t_cases,res_rel_e_cases,is_val_t_def]>>
   imp_res_tac step_e_zero_clock>>
   fs[Once step_t_cases])
 >-
   (qpat_abbrev_tac‘A = (s with clock:=0,D)’>>
   qexists_tac‘A::tr’>>fs[Abbr‘A’,check_trace_def]>>
   CONJ_TAC >-
     (Cases_on‘tr’>>
     simp[check_trace_def,optionTheory.some_def]>>
     ntac 2 (simp[Once step_t_cases])>>
     fs[])>>
   fs[LAST_DEF])
 >-
   (qexists_tac‘[s with clock:=0,Break]’>>
   fs[res_rel_t_cases,check_trace_def])
 >-
   (EVERY_CASE_TAC>>fs[]
   >-
     (qpat_abbrev_tac‘p = t_to_small_t t'’>>
     qexists_tac‘MAP (λst,t. (st,Seq t p)) tr ++ tr'’>>
     fs[HD_MAP,HD_APPEND,LAST_APPEND]>>rw[] >>
     match_mp_tac check_trace_append2>>
     fs[check_trace_seq,LAST_MAP]>>
     Cases_on‘LAST tr’>>fs[]>>
     match_mp_tac some_to_SOME_step_t>>
     simp[Once step_t_cases]>>fs[Abbr‘p’,res_rel_t_cases]>>
     metis_tac[])
   >-
     (qpat_abbrev_tac ‘p = t_to_small_t t'’>>
     qexists_tac‘(MAP (λst,t. (st,Seq t p)) tr)++[r with clock:=0,Break]’>>
     fs[HD_APPEND,HD_MAP, res_rel_t_cases]>>rw[] >>
     match_mp_tac check_trace_append2>>
     fs[check_trace_seq,LAST_MAP,check_trace_def]>>
     fs[res_rel_t_cases]>>
     match_mp_tac some_to_SOME_step_t>>
     simp[Once step_t_cases]>>fs[Abbr‘p’,res_rel_t_cases])
   >-
     (qpat_abbrev_tac ‘p = t_to_small_t t'’>>
     qexists_tac‘(MAP (λst,t. (st,Seq t p)) tr)’>>
     fs[HD_APPEND,HD_MAP,check_trace_def,check_trace_seq]>>rw[]>>
     fs[Once res_rel_t_cases,LAST_MAP]>>
     rename1 ‘step_t _ _ (s',_)’ >>
     ‘step_t (r,Seq t'' p) l (s',Seq t''' p)’ by
       simp[Once step_t_cases]>>
     metis_tac[])
   >-
     (qpat_abbrev_tac ‘p = t_to_small_t t'’>>
     qexists_tac‘(MAP (λst,t. (st,Seq t p)) tr)’>>
     fs[HD_APPEND,HD_MAP,check_trace_def,check_trace_seq]>>rw[]>>
     fs[Once res_rel_t_cases,LAST_MAP,is_val_t_def]>>
     metis_tac[no_step_t_seq]))
 >-
   (EVERY_CASE_TAC>>fs[sem_e_not_break,sem_e_not_timeout]>>
   imp_res_tac sem_e_big_small_lem>>
   imp_res_tac sem_e_clock>>
   qpat_abbrev_tac‘p1 = t_to_small_t t1’>>
   qpat_abbrev_tac‘p2 = t_to_small_t t2’>>
   TRY
     (
     qexists_tac‘(MAP (λst,e. (st,(If e p1 p2))) tr') ++ tr’>>
     fs[HD_MAP,HD_APPEND,LAST_MAP,LAST_APPEND]>>rw[] >>
     match_mp_tac check_trace_append2>>fs[res_rel_e_cases]>>CONJ_TAC
     >- metis_tac[check_trace_if1]
     >>  match_mp_tac some_to_SOME_step_t>>fs[LAST_MAP]>>
         simp[Once step_t_cases]>>
         metis_tac[]
     )
   >>
     qexists_tac‘(MAP (λst,e. (st,(If e p1 p2))) tr)’>>rw[]>>
     fs[HD_MAP,res_rel_t_cases,LAST_MAP,res_rel_e_cases,is_val_t_def,check_trace_if1,no_step_t_if1]>>
     metis_tac[check_trace_if1,no_step_t_if1,step_e_zero_clock])
  >- ( (*For*)
    reverse (Cases_on‘sem_e s e1’>>Cases_on‘q’)>>
    fs[sem_e_not_break,sem_e_not_timeout]>>
    qpat_abbrev_tac‘e1s = e_to_small_e e1’>>
    qpat_abbrev_tac‘e2s = e_to_small_e e2’>>
    (*trace for e1*)
    imp_res_tac sem_e_big_small_lem>>
    imp_res_tac sem_e_clock>>
    qpat_abbrev_tac‘p = t_to_small_t t’>>
    qabbrev_tac ‘
      e1tr = (MAP (λst,e. (st,Handle
        (If e (Seq p (Seq (Exp e2s) (For e1s e2s p))) (Exp (Num 0))))) tr)’>>
    ‘check_trace (λst. some st'. ∃l. step_t st l st') e1tr’ by metis_tac[check_trace_for1]>>
    qabbrev_tac‘ls = [s with clock:=0,For e1s e2s p]’>>
    ‘check_trace (λst. some st'. ∃l. step_t st l st') (ls++e1tr)’ by (
      match_mp_tac check_trace_append2>>unabbrev_all_tac>>
      fs[check_trace_def,HD_MAP]>>
      match_mp_tac some_to_SOME_step_t>>
      simp[Once step_t_cases]
      )
    >- (
      qexists_tac‘ ls ++ e1tr’>>
      unabbrev_all_tac>>fs[res_rel_t_cases,LAST_DEF,LAST_MAP,HD_APPEND]>>
      fs[LAST_APPEND,LAST_MAP,res_rel_e_cases,is_val_t_def]>>
      match_mp_tac no_step_t_handle>>fs[is_val_t_def]>>
      imp_res_tac step_e_zero_clock>>
      metis_tac[no_step_t_if1]
      ) >>
    IF_CASES_TAC>>fs[]
    >- ( (*run out of time*)
      fs[res_rel_t_cases,res_rel_e_cases]>>
      qexists_tac‘ (ls ++ e1tr) ++
        [(r with clock:=0,Handle(Exp (Num 0)));(r with clock:=0,Exp (Num 0))]’>>
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
        )
       >- (unabbrev_all_tac>>fs[HD_APPEND])
      ) >>
    reverse (Cases_on‘sem_t r t’>>Cases_on‘q’)>>fs[]>>
    qabbrev_tac‘ttr = (MAP (λst,t. (st,Handle (Seq t (Seq (Exp e2s) (For e1s e2s p))) ))) tr'’>>
    ‘check_trace (λst. some st'. ∃l. step_t st l st') ttr’ by
      metis_tac[check_trace_for2]>>
    ‘check_trace (λst. some st'. ∃l. step_t st l st') (ls++e1tr++ttr)’ by (
      match_mp_tac check_trace_append2>>
      fs[]>> unabbrev_all_tac>>
      fs[LAST_MAP,res_rel_e_cases,HD_MAP,LAST_DEF]>>
      match_mp_tac some_to_SOME_step_t>>
      ntac 2 (simp[Once step_t_cases])
      )
    >- (
      qexists_tac‘ls++e1tr++ttr’>>unabbrev_all_tac>>
      fs[LAST_APPEND,LAST_MAP,res_rel_t_cases]>>CONJ_TAC >>
      fs[is_val_t_def]>>match_mp_tac no_step_t_handle>>
      fs[is_val_t_def]>>match_mp_tac no_step_t_seq>>
      metis_tac[]
      )
    >- (
      qexists_tac‘ls++e1tr++ttr’>>unabbrev_all_tac>>
      fs[LAST_APPEND,LAST_MAP,res_rel_t_cases] >>
      ntac 2 (simp[Once step_t_cases,is_val_t_def])>>
      metis_tac[]
      )
    >- (
      qexists_tac‘
        ls++e1tr++ttr++
          [(r' with clock:= 0,Handle Break);(r' with clock:=0,Exp (Num 0))]’>>
      fs[LAST_APPEND,LAST_MAP,res_rel_t_cases]>>rw[]
      >- (unabbrev_all_tac>>fs[]>>DECIDE_TAC)
      >- (
        match_mp_tac check_trace_append2>>fs[check_trace_def]>>CONJ_TAC>>
        match_mp_tac some_to_SOME_step_t>>
        unabbrev_all_tac>>fs[LAST_APPEND,LAST_MAP,res_rel_t_cases]>>
        ntac 2 (simp[Once step_t_cases])
        )
      >- (unabbrev_all_tac>>fs[]>>DECIDE_TAC)
      ) >>
    (*continue executing*)
    reverse (Cases_on‘sem_e r' e2’>>Cases_on‘q’)>>
    fs[sem_e_not_break,sem_e_not_timeout]>>
    imp_res_tac sem_e_big_small_lem>>
    imp_res_tac sem_e_clock>>
    qabbrev_tac‘
      e2tr = (MAP (λst,e. (st,Handle (Seq (Exp e) (For e1s e2s p)) ))) tr''’>>
    ‘check_trace (λst. some st'. ∃l. step_t st l st') e2tr’ by
      metis_tac[check_trace_for3]>>
    ‘check_trace (λst. some st'. ∃l. step_t st l st')(ls++e1tr++ttr++e2tr)’ by (
      match_mp_tac check_trace_append2>>fs[]>>
      match_mp_tac some_to_SOME_step_t>>
      unabbrev_all_tac>>fs[LAST_APPEND,LAST_MAP,HD_MAP,res_rel_t_cases]>>
      ntac 2 (simp[Once step_t_cases,res_rel_e_cases])
      )
    >- ( (* e2 fails *)
      qexists_tac‘ls++e1tr++ttr++e2tr’>>fs[res_rel_e_cases]>>
      unabbrev_all_tac>>
      fs[LAST_APPEND,LAST_MAP,res_rel_t_cases,is_val_t_def]>>rw[] >>
      imp_res_tac step_e_zero_clock>>
      metis_tac[no_step_t_exp,no_step_t_handle,no_step_t_seq,is_val_t_def]
      ) >>
    (* e2 ok *)
    reverse (IF_CASES_TAC) >>fs[]
    >- (
      (*clock ended*)
      fs[res_rel_t_cases]>>
      qexists_tac‘ls++e1tr++ttr++e2tr’>>fs[]>>reverse (rw[])
      >- (
        unabbrev_all_tac>>fs[LAST_APPEND,LAST_MAP,res_rel_e_cases]>>
        ‘r'' with clock:=0 = r''’ by fs[state_component_equality]>>
        ntac 2 (simp[Once step_t_cases,is_val_t_def])>>
        metis_tac[]
        ) >>
      unabbrev_all_tac>>fs[]>>DECIDE_TAC
      ) >>
    (*clock ok*)
    simp[STOP_def]>>
    simp[Once sem_t_def_with_stop]>>
    fs[dec_clock_def]>>
    (*Need a handle wrapper around rest of trace*)
    qabbrev_tac‘ftr = MAP (λst,t. (st, Handle t))tr''''’ >>
    ‘check_trace (λst. some st'. ∃l. step_t st l st') ftr’ by
      metis_tac[check_trace_handle]>>
    ‘check_trace (λst. some st'. ∃l. step_t st l st')
      (ls++e1tr++ttr++e2tr++ftr)’ by (
        match_mp_tac check_trace_append2>>fs[]>>
        match_mp_tac some_to_SOME_step_t>>
        unabbrev_all_tac>>fs[LAST_APPEND,LAST_MAP,HD_MAP]>>
        fs[res_rel_e_cases]>>
        ntac 2 (simp[Once step_t_cases])
      ) >>
    fs[res_rel_t_cases]
    (*Case split on the rest of loop*)
    >- (
      qexists_tac‘
        ls ++ e1tr ++ ttr ++ e2tr ++ ftr ++[s' with clock:=0,Exp (Num i''')]’>>
      fs[]>>rw[]
      >- (unabbrev_all_tac>>fs[]>>DECIDE_TAC)
      >- (
        match_mp_tac check_trace_append2>>fs[check_trace_def]>>
        match_mp_tac some_to_SOME_step_t>>unabbrev_all_tac>>
        fs[LAST_DEF,LAST_APPEND,LAST_MAP,res_rel_e_cases]>>
        simp[Once step_t_cases,is_val_t_def,is_val_e_def]
        )
      >- (unabbrev_all_tac>>fs[]>>DECIDE_TAC)
      >- (simp[Once sem_t_def_with_stop,LAST_APPEND,dec_clock_def])
      )
    >- (
      qexists_tac‘ls ++ e1tr++ttr++e2tr++ftr’>>fs[]>> reverse (rw[])
      >- (
        ntac 4 (simp[Once sem_t_def_with_stop,LAST_APPEND,dec_clock_def])>>
        unabbrev_all_tac>>fs[LAST_APPEND,LAST_MAP,is_val_t_def]>>
        match_mp_tac no_step_t_handle>>
        metis_tac[]
        ) >>
      unabbrev_all_tac>>fs[]>>DECIDE_TAC
      )
    >- ( (*break never occurs*)
      qpat_x_assum ‘A = (RBreak,s')’ mp_tac>>
      fct>>Cases_on‘q’>>
      fs[sem_e_not_timeout,sem_e_not_break]>>
      IF_CASES_TAC>>fs[]>>
      fct>>Cases_on‘q’>>
      fs[]>>
      fct>>Cases_on‘q’>>
      fs[sem_e_not_timeout,sem_e_not_break]>>
      IF_CASES_TAC>>fs[]>>
      simp[STOP_def]>>
      metis_tac[sem_t_for_no_break]
      )
    >- (
      qexists_tac‘ls ++ e1tr ++ ttr ++ e2tr ++ ftr’>>fs[]>> reverse (rw[]) >>
      unabbrev_all_tac
      >- (
        ntac 3 (
          simp[Once sem_t_def_with_stop,LAST_APPEND,dec_clock_def,LAST_MAP])>>
        simp[Once step_t_cases]>>metis_tac[]
        ) >>
      fs[] >> DECIDE_TAC
      )
    )
QED

Triviality big_timeout_0:
  !st p r.
    sem_t st p = (Rtimeout,r)
    ⇒
    r.clock = 0
Proof
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
   fs [])
QED

(* check traces are unique up to prefixing *)
Triviality check_trace_determ:
  ∀tr h f.
    check_trace f (h::tr) ⇒
    ∀tr'.
      LENGTH tr' ≤ LENGTH tr ∧
      check_trace f (h::tr') ⇒
      isPREFIX tr' tr
Proof
 Induct>>rw[]>>fs[check_clock_def,isPREFIX,LENGTH_NIL]>>
 Cases_on‘tr'’>>fs[check_trace_def]>>
 metis_tac[]
QED

Triviality check_trace_prefixes:
  ∀tr f.
    tr ≠ [] ∧
    check_trace f tr ⇒
    ∀tr'.
      tr' ≠ [] ∧ HD tr' = HD tr ∧
      check_trace f tr' ⇒
      isPREFIX tr tr' ∨ isPREFIX tr' tr
Proof
  rw[]>>
  Cases_on‘tr’>>Cases_on‘tr'’>>fs[]>>
  Cases_on‘LENGTH t' ≤ LENGTH t’>>
  TRY(‘LENGTH t ≤ LENGTH t'’ by DECIDE_TAC)>>
  metis_tac[check_trace_determ]
QED

Triviality check_trace_TL:
  ∀tr tr'.
    tr ≠ [] ∧
    check_trace (λst. some st'. ?l. step_t st l st') tr ∧
    (∀l t'. ¬step_t (LAST tr) l t') ∧
    check_trace (λst. some st'. ?l. step_t st l st') tr' ∧
    isPREFIX tr tr' ⇒
    tr = tr'
Proof
  Induct>>fs[check_trace_def,LAST_DEF]>>rw[]>>Cases_on‘tr'’>>fs[]
  >-
   (Cases_on‘t’>>fs[check_trace_def,some_def]>>
    metis_tac[])
  >>
  Cases_on‘tr’>>Cases_on‘t’>>fs[check_trace_def]>>
  res_tac>>fs[]
QED

Triviality prefix_append:
  ∀ls ls'. ls ≼ ls' ⇒ ∃ls''. ls++ls'' = ls'
Proof
  metis_tac[rich_listTheory.IS_PREFIX_APPEND]
QED

Triviality res_rel_t_io_trace:
  res_rel_t (q,r) s ⇒ r.io_trace = (FST s).io_trace
Proof
  simp[res_rel_t_cases]>>rw[]>>fs[]
QED

(*slow*)
Triviality res_rel_t_clock:
 res_rel_t (q,r) s ∧
  step_t s l t ⇒
  q = Rtimeout ∧ (FST s).clock = 0
Proof
  simp[res_rel_t_cases]>>rw[] >>
  fs[Once step_t_cases,Once step_e_cases] >>
  metis_tac[PAIR,FST]
QED

Triviality step_e_io_mono:
  ∀s l s'.
    step_e s l s' ⇒
    (FST s).io_trace ≼ (FST s').io_trace
Proof
  Induct_on ‘step_e’ >> simp[]
QED

Triviality step_t_io_mono:
  ∀s l s'.
    step_t s l s' ⇒
    (FST s).io_trace ≼ (FST s').io_trace
Proof
  Induct_on ‘step_t’ >> simp[] >>
  metis_tac[step_e_io_mono,FORALL_PROD,FST]
QED

Triviality RTC_step_t_io_mono:
  ∀x y. (λs1 s2. (some st'. ∃l. step_t s1 l st') = SOME s2)^* x y ⇒
        (FST x).io_trace ≼ (FST y).io_trace
Proof
  Induct_on ‘RTC’ >> rw[] >>
  last_x_assum mp_tac >>
  DEEP_INTRO_TAC some_intro >> rw[] >>
  metis_tac[step_t_io_mono,IS_PREFIX_TRANS]
QED

Triviality check_trace_io_trace:
  ∀tr ls.
    tr ≠ [] ∧ check_trace (λst. some st'. ∃l. step_t st l st') (tr ++ ls) ⇒
    (FST(LAST tr)).io_trace ≼ (FST(LAST (tr++ls))).io_trace
Proof
  rw[] >>
  match_mp_tac RTC_step_t_io_mono >>
  simp[check_trace_thm] >>
  qexists_tac‘LAST tr::ls’ >>
  simp[] >>
  conj_tac >- ( Cases_on‘ls’>>simp[] ) >>
  ‘LAST tr::ls = DROP (LENGTH tr - 1) (tr++ls)’ suffices_by (
    disch_then SUBST1_TAC >>
    match_mp_tac check_trace_drop >> simp[] ) >>
  simp[DROP_APPEND1] >>
  Q.ISPECL_THEN[‘1n’,‘tr’]mp_tac (GSYM LASTN_DROP) >>
  ‘1 ≤ LENGTH tr’ by (
    Cases_on‘tr’>>fs[] >> simp[] ) >>
  simp[] >>
  Q.ISPEC_THEN‘tr’FULL_STRUCT_CASES_TAC SNOC_CASES >- fs[] >>
  REWRITE_TAC[arithmeticTheory.ONE,LASTN,LAST,SNOC]
QED

Triviality sem_e_ignores_clock:
  ∀s e c r s'.
    sem_e s e = (r,s') ⇒
    sem_e (s with clock:=c) e = (r,s' with clock:=c)
Proof
  ho_match_mp_tac sem_e_ind>>srw_tac[][sem_e_def]>>fs[LET_THM]
  >-
    (ect>>fs[])
  >- (fs[permute_pair_def,LET_THM,oracle_get_def,unpermute_pair_def]>>
      Cases_on‘switch’>>fs[]>>
      qpat_x_assum‘A=(r,s')’ mp_tac>>
      fct>>Cases_on‘q’>>res_tac>>
      fs[sem_e_not_break,sem_e_not_timeout]>>
      fct>>Cases_on‘q’>>res_tac>>
      rw[]>>
      fs[sem_e_not_break,sem_e_not_timeout])
  >>
    Cases_on‘sem_e s e’>>res_tac>>fs[]>>
    Cases_on‘q’>>fs[state_component_equality]
QED

Triviality sem_e_io_mono:
  ∀s e c.
    (SND (sem_e s e)).io_trace ≼ (SND (sem_e (s with clock:= c) e)).io_trace
Proof
  rw[]>>Cases_on‘sem_e s e’>>imp_res_tac sem_e_ignores_clock>>
  fs[]
QED

Triviality sem_e_clock_inc:
  ∀s e r.
    sem_e s e = r ⇒
    ∀k. sem_e (s with clock:= s.clock+k) e =
        (FST r, (SND r) with clock:= (SND r).clock+k)
Proof
  metis_tac[sem_e_ignores_clock,sem_e_clock,FST,SND,PAIR]
QED

Triviality sem_t_clock_inc:
  ∀s t r.
    sem_t s t = r ∧ FST r ≠ Rtimeout ⇒
    ∀k. sem_t (s with clock:= s.clock+k) t =
        (FST r, (SND r) with clock:= (SND r).clock+k)
Proof
  ho_match_mp_tac sem_t_ind>>rw[]>>fs[sem_e_clock]>>
  TRY(fs[sem_t_def_with_stop]>>NO_TAC)
  >-
    (fs[sem_t_def_with_stop]>>
    Cases_on‘sem_e s e’>>
    imp_res_tac sem_e_ignores_clock>>
    fs[]>>metis_tac[sem_e_clock])
  >-
    (fs[sem_t_def_with_stop]>>Cases_on‘sem_t s t’>>Cases_on‘q’>>fs[])
  >-
    (fs[sem_t_def_with_stop]>>Cases_on‘sem_e s e’>>Cases_on‘q’>>fs[sem_e_res]>>
    imp_res_tac sem_e_clock_inc>>
    pop_assum(qspec_then‘k’ assume_tac)>>fs[]>>
    IF_CASES_TAC>>fs[])
  >>
    pop_assum mp_tac>>
    simp[sem_t_def_with_stop]>>
    Cases_on‘sem_e s e1’>>Cases_on‘q’>>fs[]>>
    imp_res_tac sem_e_clock_inc>>fs[]>>
    TRY(pop_assum(qspec_then‘k’ assume_tac))>>
    fs[DECIDE “(A:num)+B = B+A”]>>
    IF_CASES_TAC>>fs[]>>
    Cases_on‘sem_t r t’>>Cases_on‘q’>>fs[]>>
    Cases_on‘sem_e r' e2’>>Cases_on‘q’>>fs[]>>
    TRY(metis_tac[sem_e_res])>>
    imp_res_tac sem_e_clock_inc>>fs[]>>
    TRY(pop_assum(qspec_then‘k’ assume_tac))>>
    fs[DECIDE “(A:num)+B = B+A”]>>
    IF_CASES_TAC>>fs[]>>rw[]>>
    fs[dec_clock_def,STOP_def]>>
    ‘1 ≤ r''.clock’ by DECIDE_TAC>>
    metis_tac[arithmeticTheory.LESS_EQ_ADD_SUB]
QED

Triviality check_trace_io_trace_simp:
  tr ≠ [] ∧
  check_trace (λst.some st'. ∃l. step_t st l st') tr ⇒
  (FST(HD tr)).io_trace ≼ (FST (LAST tr)).io_trace
Proof
  Cases_on‘tr’>>rw[]>>
  ‘FST h = FST(LAST [h])’ by fs[]>>
  pop_assum SUBST1_TAC>>
  ‘h::t = [h]++t’ by fs[]>>
  pop_assum SUBST1_TAC>>
  ho_match_mp_tac check_trace_io_trace>>
  rw[]
QED

Triviality sem_t_sing_io_mono:
  ∀s t res s'. sem_t s t = (res,s') ⇒ s.io_trace ≼ s'.io_trace
Proof
  rw[]>>imp_res_tac big_small_lem>>
  imp_res_tac check_trace_io_trace_simp>>
  fs[res_rel_t_cases]>>
  rfs[]
QED

Triviality sem_e_sing_io_mono:
  ∀s e res s'. sem_e s e = (res,s') ⇒ s.io_trace ≼ s'.io_trace
Proof
  CCONTR_TAC>>fs[]>>
  ‘sem_t s (Exp e) = (res,s')’ by
    fs[sem_t_def_with_stop]>>
  metis_tac[sem_t_sing_io_mono]
QED

(* Monotonicity of io_trace w.r.t. to clock *)
Triviality sem_t_io_mono_lem:
  ∀s t k.
    (SND (sem_t s t)).io_trace ≼
    (SND (sem_t (s with clock:=s.clock+k) t)).io_trace
Proof
  ho_match_mp_tac sem_t_ind>>rw[]>>
  TRY(fs[sem_t_def_with_stop,sem_e_io_mono]>>NO_TAC)
  >-
    (fs[sem_t_def_with_stop]>>
    fct>>Cases_on‘q’>>fs[]>>
    imp_res_tac sem_t_clock_inc>>fs[]>>
    fct>>Cases_on‘q’>>fs[]>>
    first_x_assum(qspec_then‘k’ assume_tac)>>rfs[]>>
    Cases_on‘sem_t r' t'’>>
    imp_res_tac sem_t_sing_io_mono>>
    fs[]>>
    metis_tac[IS_PREFIX_TRANS])
  >-
    (fs[sem_t_def_with_stop]>>
    fct>>Cases_on‘q’>>fs[]>>TRY(metis_tac[sem_e_res])>>
    imp_res_tac sem_e_clock_inc>>fs[]>>
    IF_CASES_TAC>>fs[])
  >>
    simp[Once sem_t_def_with_stop]>>
    simp[Once sem_t_def_with_stop]>>
    fct>>Cases_on‘q’>>fs[]>>TRY(metis_tac[sem_e_res])>>
    imp_res_tac sem_e_clock_inc>>
    pop_assum(qspec_then‘k’ assume_tac)>>
    fs[DECIDE “(A:num)+B = B+A”]>>
    IF_CASES_TAC>>fs[]>>
    fct>>Cases_on‘q’>>fs[]>>
    TRY(imp_res_tac sem_t_clock_inc>>fs[]>>
    pop_assum(qspec_then‘k’ assume_tac))>>rfs[]>>
    fs[DECIDE “(A:num)+B = B+A”]
    >-
      (fct>>Cases_on‘q’>>fs[]>>TRY(metis_tac[sem_e_res])>>
      imp_res_tac sem_e_clock_inc>>
      pop_assum(qspec_then‘k’ assume_tac)>>
      fs[DECIDE “(A:num)+B = B+A”]>>
      IF_CASES_TAC>>fs[]
      >-
        (fs[dec_clock_def,STOP_def]>>
        ‘1 ≤ r''.clock’ by DECIDE_TAC>>
        metis_tac[arithmeticTheory.LESS_EQ_ADD_SUB])
      >>
      IF_CASES_TAC>>fs[]>>
      qpat_abbrev_tac‘A = sem_t B C’>>
      Cases_on‘A’>>fs[markerTheory.Abbrev_def]>>
      pop_assum (assume_tac o SYM)>>imp_res_tac sem_t_sing_io_mono>>
      fs[dec_clock_def])
    >>
      first_x_assum(qspec_then‘k’ assume_tac)>>
      fct>>Cases_on‘q’>>fs[]>>
      fct>>Cases_on‘q’>>fs[]>>TRY(metis_tac[sem_e_res])>>
      imp_res_tac sem_e_sing_io_mono
      >-
        (IF_CASES_TAC>>fs[dec_clock_def]>>
        TRY(qpat_abbrev_tac‘A = sem_t B C’>>
        Cases_on‘A’>>fs[markerTheory.Abbrev_def]>>
        pop_assum (assume_tac o SYM)>>imp_res_tac sem_t_sing_io_mono)>>
        fs[]>>metis_tac[IS_PREFIX_TRANS])
      >>
      metis_tac[IS_PREFIX_TRANS]
QED

Triviality sem_t_io_mono:
  k1 ≤ k2 ⇒
  (SND (sem_t (init_st 0 nd input with clock := k1) p)).io_trace ≼
  (SND (sem_t (init_st 0 nd input with clock := k2) p)).io_trace
Proof
 qpat_abbrev_tac ‘st = init_st A B C’>>
 rw[]>>imp_res_tac arithmeticTheory.LESS_EQUAL_ADD >>
 Q.SPECL_THEN [‘st with clock:=k1’,‘p’,‘p'’] assume_tac sem_t_io_mono_lem>>
 fs[]
QED

Theorem sem_equiv_lem:
  ∀input prog r. ofbs_sem (for_big_sem input) prog r ⇔
                   osmall_sem (for_small_sem input) prog r
Proof
 gen_tac >>
 match_mp_tac osmall_fbs_equiv2 >>
 conj_tac >- (
   rw [for_small_sem_def] >>
   match_mp_tac step_t_io_mono>>
   Q.ISPEC_THEN ‘λst. ∃l. step_t s1 l st’ assume_tac some_SAT>>
   fs[ETA_AX])>>
 conj_tac >- (
   rw [for_big_sem_def] >>
   rw [eval_with_clock_def, for_eval_def] >>
   every_case_tac >>
   fs [] >>
   metis_tac [sem_t_io_mono, SND]) >>
 conj_tac >- (
   rw [for_big_sem_def, eval_with_clock_def, for_eval_def] >>
   ect >>
   fs [] >>
   metis_tac [big_timeout_0]) >>
 qexists_tac ‘I’ >>
 conj_tac
 >- (
   rw [unbounded_def] >>
   qexists_tac ‘SUC x’ >>
   simp []) >>
 rpt gen_tac >>
 simp [for_big_sem_def, for_eval_def, eval_with_clock_def] >>
 DISCH_TAC >>
 ect >>
 imp_res_tac big_small_lem >>
 fs [] >>
 qexists_tac ‘tr’ >>
 fs [for_small_sem_def] >>
 rw [same_result_def] >>
 fs [res_rel_t_cases, is_val_t_def, is_val_e_def, some_no_choice, init_st_def] >>
 simp [] >>
 rw []
 >- (rw [Once step_t_cases] >>
     rw [Once step_e_cases])
 >- rw [Once step_t_cases]
 >- (rw [some_def] >>
     metis_tac [])
 >- metis_tac [PAIR]
QED

Triviality FST_SPLIT: FST x = y ⇒ ∃z. x = (y,z)
Proof Cases_on‘x’>>fs[]
QED

Triviality big_val_no_errors:
  !st p v s.
    sem_t st p = (Rval v,s)
   ⇒
    ∀c.
      FST (sem_t (st with clock:= c) p) ≠ Rbreak ∧
      FST (sem_t (st with clock:=c) p) ≠ Rfail
Proof
  rw[]>>CCONTR_TAC>>fs[]>>imp_res_tac FST_SPLIT>>
  imp_res_tac big_small_lem>>
  ‘HD tr = HD tr'’ by fs[]>>
  fs[res_rel_t_cases]>>
  ‘∀l t'. ¬step_t (LAST tr) l t'’ by
    (simp[Once step_t_cases,FORALL_PROD]>> rw[] >>
     qpat_x_assum ‘∀a b c. ¬step_t _ _ _ ’ mp_tac >>
     simp[Once step_t_cases] >> simp[Once step_t_cases, Once step_e_cases]) >>
  ‘∀l t'. ¬step_t (LAST tr') l t'’ by
    simp[Once step_t_cases,FORALL_PROD,Once step_e_cases]>>
  ‘isPREFIX tr tr' ∨ isPREFIX tr' tr’ by
    metis_tac[check_trace_prefixes]>>
  ‘tr = tr'’ by metis_tac[check_trace_TL]>>
  fs[]>>
  qpat_assum‘A=t’ (SUBST_ALL_TAC o SYM)>>fs[is_val_t_def,is_val_e_def]
QED

(* we can prove an alternative characterisation of the semantics, now that we
   know sem_t's io_trace is a chain *)

Definition over_all_def:
  over_all f = { f c | c | T }
End

Triviality init_st_with_clock:
  init_st a b c with clock := d = init_st d b c
Proof EVAL_TAC
QED

Theorem lprefix_chain_sem_t_io_trace_over_all_c:
  prefix_chain (over_all (λc. (SND (sem_t (init_st c nd input) t)).io_trace))
Proof
  rw[lprefix_lubTheory.prefix_chain_def,over_all_def] >>
  qspecl_then[‘c’,‘c'’]strip_assume_tac arithmeticTheory.LESS_EQ_CASES >|[disj1_tac,disj2_tac] >>
  imp_res_tac sem_t_io_mono >> fs[init_st_with_clock]
QED

Triviality image_intro:
  {fromList (FILTER P (Q c)) | c | T} =
  IMAGE fromList (IMAGE (FILTER P) (over_all Q))
Proof
  rw[EXTENSION,over_all_def,PULL_EXISTS]
QED

Theorem IMAGE_over_all:
  IMAGE P (over_all f) = over_all (P o f)
Proof
  rw[EXTENSION,over_all_def,PULL_EXISTS]
QED

(* Pretty Printing *)
Definition BIGSUP_def: BIGSUP f = build_lprefix_lub (over_all f)
End

val _ = Parse.add_rule{
  term_name="BIGSUP", fixity=Parse.Binder,
  pp_elements=[TOK"BIGSUP"],
  block_style=(NoPhrasing,(PP.CONSISTENT,0)),paren_style=OnlyIfNecessary
  }

Theorem semantics_alt =
  semantics_def
    |> SIMP_RULE bool_ss [image_intro]
    |> SIMP_RULE bool_ss [lprefix_chain_sem_t_io_trace_over_all_c,
                          lprefix_lubTheory.prefix_chain_FILTER,
                          lprefix_lubTheory.prefix_chain_lprefix_chain,
                          lprefix_lubTheory.build_prefix_lub_intro]
    |> SIMP_RULE bool_ss [IMAGE_over_all]
    |> SIMP_RULE bool_ss [prove(“f o g = λc. f (g c)”,rw[FUN_EQ_THM])]
    |> SIMP_RULE bool_ss [GSYM BIGSUP_def]

Definition oracle_upd_def:
  oracle_upd s (b,a) = s with <|non_det_o := a; io_trace:=s.io_trace ++[INR b]|>
End

Theorem step_e_rules_oracle_upd =
        step_e_rules|>REWRITE_RULE[GSYM oracle_upd_def]

val _ = export_theory ();
