open HolKernel Parse boolLib bossLib;

val _ = new_theory "for";

(*

This file defines a simple FOR language that's very similar to the FOR
language used by Arthur Charguéraud in his ESOP'13 paper:

  Pretty-Big-Step Semantics
  http://www.chargueraud.org/research/2012/pretty/

This file defines:
 - the syntax of the language,
 - a functional big-step semantics (an interpreter with a clock),
 - a conventional relational big-step semantics, and
 - a very simple type checker (that is proved sound)

*)

open optionTheory pairTheory pred_setTheory finite_mapTheory stringTheory;
open integerTheory lcsymtacs;

val _ = temp_tight_equality ();

val ect = BasicProvers.EVERY_CASE_TAC;


(* === Syntax === *)

val _ = Datatype `
e = Var string
  | Num int
  | Add e e
  | Assign string e`;

val _ = Datatype `
t =
  | Dec string t
  | Exp e
  | Break
  | Seq t t
  | If e t t
  | For e e t`;

val _ = Datatype `
r = Rval int
  | Rbreak
  | Rtimeout
  | Rfail`;

val r_distinct = fetch "-" "r_distinct";
val r_11 = fetch "-" "r_11";


(* === Functional big-step semantics === *)

val _ = Datatype `
state = <| store : string |-> int; clock : num |>`;

val state_component_equality = fetch "-" "state_component_equality";

val store_var_def = Define `
  store_var v x s = s with store := s.store |+ (v,x)`;

val _ = augment_srw_ss[rewrites[store_var_def]];

val state_rw = Q.prove (
`(!s c. <| store := s; clock := c |>.store = s) ∧
 (!s. <| store := s.store; clock := s.clock |> = s)`,
 rw [state_component_equality]);

(* Expression evaluation *)

val sem_e_def = Define `
(sem_e s (Var x) =
  case FLOOKUP s.store x of
     | NONE => (Rfail, s)
     | SOME n => (Rval n, s)) ∧
(sem_e s (Num num) =
  (Rval num, s)) ∧
(sem_e s (Add e1 e2) =
  case sem_e s e1 of
     | (Rval n1, s1) =>
         (case sem_e s1 e2 of
             | (Rval n2, s2) =>
                 (Rval (n1 + n2), s2)
             | r => r)
     | r => r) ∧
(sem_e s (Assign x e) =
  case sem_e s e of
     | (Rval n1, s1) =>
         (Rval n1, store_var x n1 s1)
     | r => r)`;

(* HOL4's definition requires a little help with the definition. In
   particular, we need to help it see that the clock does not
   decrease. To do this, we add a few redundant checks (check_clock)
   to the definition of the sem_t function. These redundant checks are
   removed later in the script. *)

val sem_e_clock = Q.store_thm ("sem_e_clock",
`!s e r s'. sem_e s e = (r, s') ⇒ s.clock = s'.clock`,
 Induct_on `e` >> rw [sem_e_def] >> ect >>
 fs [] >> rw [] >> metis_tac []);

val sem_e_store = Q.prove (
`!s e r s'. sem_e s e = (r, s') ⇒ FDOM s.store ⊆ FDOM s'.store`,
 Induct_on `e` >> rw [sem_e_def] >> ect >>
 fs [SUBSET_DEF] >> rw [] >> metis_tac []);

val sem_e_res = Q.prove (
`!s e r s'. sem_e s e = (r, s') ⇒ r ≠ Rbreak ∧ r ≠ Rtimeout`,
 Induct_on `e` >> rw [sem_e_def] >> ect >>
 fs [] >> rw [] >> metis_tac []);

val check_clock_def = Define `
check_clock s' s =
  s' with clock := (if s'.clock ≤ s.clock then s'.clock else s.clock)`;

val dec_clock_def = Define `
dec_clock s = s with clock := s.clock - 1`;

val dec_clock_store = Q.store_thm ("dec_clock_store[simp]",
`!s. (dec_clock s).store = s.store`,
 rw [dec_clock_def]);

(* Statement evaluation -- with redundant check_clock *)

val sem_t_def = tDefine "sem_t" `
(sem_t s (Exp e) = sem_e s e) ∧
(sem_t s (Dec x t) =
  sem_t (store_var x 0 s) t) ∧
(sem_t s Break = (Rbreak, s)) ∧
(sem_t s (Seq t1 t2) =
  case sem_t s t1 of
     | (Rval _, s1) =>
         sem_t (check_clock s1 s) t2
     | r => r) ∧
(sem_t s (If e t1 t2) =
  case sem_e s e of
     | (Rval n1, s1) => sem_t s1 (if n1 = 0 then t2 else t1)
     | r => r) ∧
(sem_t s (For e1 e2 t) =
  case sem_e s e1 of
     | (Rval n1, s1) =>
         if n1 = 0 then
           (Rval 0, s1)
         else
           (case sem_t s1 t of
              | (Rval _, s2) =>
                  (case sem_e s2 e2 of
                      | (Rval _, s3) =>
                          if s.clock ≠ 0 ∧ s3.clock ≠ 0 then
                            sem_t (dec_clock (check_clock s3 s)) (For e1 e2 t)
                          else
                            (Rtimeout, s3)
                      | r => r)
              | (Rbreak, s2) =>
                  (Rval 0, s2)
              | r => r)
     | r => r)`
 (WF_REL_TAC `(inv_image (measure I LEX measure t_size)
                            (\(s,t). (s.clock,t)))`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ fs [check_clock_def, dec_clock_def, LET_THM]
  \\ rw []
  \\ imp_res_tac sem_e_clock
  \\ DECIDE_TAC);

val sem_t_clock = Q.store_thm ("sem_t_clock",
`!s t r s'. sem_t s t = (r, s') ⇒ s'.clock ≤ s.clock`,
 ho_match_mp_tac (fetch "-" "sem_t_ind") >>
 reverse (rpt strip_tac) >>
 pop_assum mp_tac >>
 rw [Once sem_t_def] >>
 ect >>
 imp_res_tac sem_e_clock >>
 fs [] >>
 fs [check_clock_def, dec_clock_def, LET_THM] >>
 TRY decide_tac >>
 rfs [] >>
 res_tac >>
 decide_tac);

val check_clock_id = Q.prove (
`!s s'. s.clock ≤ s'.clock ⇒ check_clock s s' = s`,
 rw [check_clock_def, state_component_equality]);

val STOP_def = Define `
  STOP x = x`;

(* Statement evaluation -- without any redundant checks *)

val sem_t_def_with_stop = Q.store_thm ("sem_t_def_with_stop",
`(sem_t s (Exp e) = sem_e s e) ∧
 (sem_t s (Dec x t) = sem_t (store_var x 0 s) t) ∧
 (sem_t s Break = (Rbreak, s)) ∧
 (sem_t s (Seq t1 t2) =
   case sem_t s t1 of
      | (Rval _, s1) =>
          sem_t s1 t2
      | r => r) ∧
 (sem_t s (If e t1 t2) =
   case sem_e s e of
      | (Rval n1, s1) => sem_t s1 (if n1 = 0 then t2 else t1)
      | r => r) ∧
 (sem_t s (For e1 e2 t) =
   case sem_e s e1 of
      | (Rval n1, s1) =>
          if n1 = 0 then
            (Rval 0, s1)
          else
            (case sem_t s1 t of
               | (Rval _, s2) =>
                   (case sem_e s2 e2 of
                       | (Rval _, s3) =>
                           if s3.clock ≠ 0 then
                             sem_t (dec_clock s3) (STOP (For e1 e2 t))
                           else
                             (Rtimeout, s3)
                       | r => r)
               | (Rbreak, s2) =>
                   (Rval 0, s2)
               | r => r)
      | r => r)`,
 rpt strip_tac >>
 rw [Once sem_t_def,STOP_def] >>
 ect >>
 fs [] >>
 imp_res_tac sem_t_clock >>
 fs [dec_clock_def, LET_THM, check_clock_id] >>
 rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
 rw [state_component_equality] >>
 rw [check_clock_def] >>
 imp_res_tac sem_e_clock >>
 fs [] >>
 `F` by decide_tac);

val sem_t_def =
  save_thm("sem_t_def",REWRITE_RULE [STOP_def] sem_t_def_with_stop);

(* We also remove the redundant checks from the induction theorem. *)

val sem_t_ind = Q.store_thm("sem_t_ind",
  `!P.
     (!s e. P s (Exp e)) /\
     (!s x t.
        P (store_var x 0 s) t ==> P s (Dec x t)) /\
     (!s. P s Break) /\
     (!s t1 t2.
        (!s1 v5. sem_t s t1 = (Rval v5,s1) ==> P s1 t2) /\ P s t1 ==>
        P s (Seq t1 t2)) /\
     (!s e t1 t2.
        (!s1 n1. sem_e s e = (Rval n1,s1) ==>
                 P s1 (if n1 = 0 then t2 else t1)) ==>
        P s (If e t1 t2)) /\
     (!s e1 e2 t.
        (!s1 n1.
           sem_e s e1 = (Rval n1,s1) /\ n1 <> 0 ==>
           P s1 t /\
           !s2 n2 s3 n3.
             sem_t s1 t = (Rval n2,s2) /\ sem_e s2 e2 = (Rval n3,s3) /\
             s3.clock <> 0 ==>
             P (dec_clock s3) (For e1 e2 t)) ==>
        P s (For e1 e2 t)) ==>
     !s t. P s t`,
 ntac 2 strip_tac >>
 ho_match_mp_tac (fetch "-" "sem_t_ind") >>
 rw [] >>
 first_x_assum match_mp_tac >>
 rw [] >>
 fs [] >>
 res_tac >>
 imp_res_tac sem_t_clock >>
 imp_res_tac sem_e_clock >>
 fs [dec_clock_def, check_clock_id, LET_THM] >>
 first_x_assum match_mp_tac >>
 decide_tac)

val sem_t_store = Q.prove (
`!s t r s'. sem_t s t = (r, s') ⇒ FDOM s.store ⊆ FDOM s'.store`,
 ho_match_mp_tac sem_t_ind >>
 rpt conj_tac >>
 rpt gen_tac >>
 DISCH_TAC >>
 ONCE_REWRITE_TAC [sem_t_def]
 >- (fs [sem_t_def] >>
     metis_tac [sem_e_store])
 >- (fs [sem_t_def] >>
     metis_tac [])
 >- (fs [sem_t_def] >>
     metis_tac [])
 >- (ect >>
     rw [] >>
     metis_tac [sem_e_store, SUBSET_DEF])
 >- (ect >>
     rw [] >>
     metis_tac [sem_e_store, SUBSET_DEF])
 >- (Cases_on `sem_e s e1` >>
     fs [] >>
     Cases_on `q` >>
     reverse (fs [])
     >- (Cases_on `i = 0` >>
         fs []
         >- metis_tac [sem_e_store, SUBSET_TRANS] >>
         Cases_on `sem_t r t` >>
         fs [] >>
         Cases_on `q` >>
         reverse (fs [])
         >- (ect >>
             fs [] >>
             rw [] >>
             rfs [] >>
             metis_tac [sem_e_store, SUBSET_TRANS]) >>
         metis_tac [sem_e_store, SUBSET_TRANS]) >>
     metis_tac [sem_e_store, SUBSET_TRANS]));

(* The top-level semantics defines what is externally observable *)

val _ = Datatype `
  observation = Terminate | Diverge | Crash`;

val s_with_clock_def = Define `
  s_with_clock c = <| store := FEMPTY; clock := c |>`;

val semantics_def = Define `
  semantics t =
      if (?c v s. sem_t (s_with_clock c) t = (Rval v,s)) then
        Terminate
      else if (!c. ?s. sem_t (s_with_clock c) t = (Rtimeout,s)) then
        Diverge
      else Crash`

val semantics_thm = save_thm("semantics_thm",semantics_def);


(* === A simple type checker === *)

val type_e_def = Define `
(type_e s (Var x) ⇔ x ∈ s) ∧
(type_e s (Num num) ⇔ T) ∧
(type_e s (Add e1 e2) ⇔ type_e s e1 ∧ type_e s e2) ∧
(type_e s (Assign x e) ⇔ x ∈ s ∧ type_e s e)`;

val type_t_def = Define `
(type_t in_for s (Exp e) ⇔ type_e s e) ∧
(type_t in_for s (Dec x t) ⇔ type_t in_for (x INSERT s) t) ∧
(type_t in_for s Break ⇔ in_for) ∧
(type_t in_for s (Seq t1 t2) ⇔ type_t in_for s t1 ∧ type_t in_for s t2) ∧
(type_t in_for s (If e t1 t2) ⇔ type_e s e ∧ type_t in_for s t1 ∧ type_t in_for s t2) ∧
(type_t in_for s (For e1 e2 t) ⇔ type_e s e1 ∧ type_e s e2 ∧ type_t T s t)`;

val type_weakening_e = Q.prove (
`!s e s' s1. type_e s e ∧ s ⊆ s1 ⇒ type_e s1 e`,
 Induct_on `e` >>
 rw [type_e_def, SUBSET_DEF] >>
 ect >>
 fs [] >>
 rw [EXTENSION] >>
 metis_tac [SUBSET_DEF, NOT_SOME_NONE, SOME_11]);

val type_sound_e = Q.prove (
`!s e s1 c.
  type_e s e ∧ s ⊆ FDOM s1
  ⇒
  ?r s1'.
    r ≠ Rfail ∧
    sem_e <| store := s1; clock := c |> e = (r, s1')`,
 Induct_on `e` >>
 rw [type_e_def, sem_e_def]
 >- (ect >>
     fs [FLOOKUP_DEF, SUBSET_DEF] >>
     rw [] >>
     metis_tac [])
 >- (res_tac >>
     ntac 2 (pop_assum (qspec_then `c` mp_tac)) >>
     rw [] >>
     rw [] >>
     `type_e (FDOM s1''.store) e'`
              by (rw [] >>
                  match_mp_tac type_weakening_e >>
                  metis_tac [sem_e_store, SUBSET_TRANS, state_rw]) >>
     first_x_assum (fn th => pop_assum (fn th' => assume_tac (MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th) th'))) >>
     pop_assum (qspecl_then [`s1''.store`, `s1''.clock`] mp_tac) >>
     rw [] >>
     fs [state_rw] >>
     ect >>
     rw [])
 >- (ect >>
     fs [] >>
     res_tac >>
     pop_assum (qspec_then `c` mp_tac) >>
     fs []));

val type_weakening_t = Q.prove (
`!in_for s t s' s1. type_t in_for s t ∧ s ⊆ s1 ⇒ type_t in_for s1 t`,
 Induct_on `t` >>
 rw [type_t_def, SUBSET_DEF] >>
 ect >>
 fs [] >>
 rw [EXTENSION] >>
 metis_tac [SUBSET_DEF, NOT_SOME_NONE, SOME_11, type_weakening_e, INSERT_SUBSET]);

(* Have to use sem_t_ind, and not type_t_ind or t_induction. This is different
 * from small-step-based type soundness *)
val type_sound_t = Q.prove (
`!s1 t in_for s.
  type_t in_for s t ∧ s ⊆ FDOM s1.store
  ⇒
  ?r s1'.
    r ≠ Rfail ∧
    (~in_for ⇒ r ≠ Rbreak) ∧
    sem_t s1 t = (r, s1')`,
 ho_match_mp_tac sem_t_ind >>
 rw [type_t_def] >>
 ONCE_REWRITE_TAC [sem_t_def] >>
 rw []
 >- (imp_res_tac type_sound_e >>
     pop_assum (qspec_then `s1.clock` mp_tac) >>
     rw [state_rw] >>
     metis_tac [sem_e_res])
 >- (res_tac >>
     fs [SUBSET_DEF])
 >- (res_tac >>
     rw [] >>
     Cases_on `r'` >>
     rw [] >>
     fs [] >>
     rw [] >>
     pop_assum match_mp_tac >>
     metis_tac [type_weakening_t, sem_t_store])
 >- (imp_res_tac type_sound_e >>
     pop_assum (qspec_then `s1.clock` mp_tac) >>
     rw [state_rw] >>
     rw [] >>
     Cases_on `r` >>
     fs []
     >- (Cases_on `i = 0` >>
         fs [] >>
         first_x_assum match_mp_tac >>
         metis_tac [type_weakening_t, sem_e_store])
     >- metis_tac [sem_e_res])
 >- (imp_res_tac type_sound_e >>
     rpt (pop_assum (qspec_then `s1.clock` mp_tac)) >>
     rw [state_rw] >>
     rw [] >>
     reverse (Cases_on `r'`) >>
     fs [] >>
     Cases_on `i = 0` >>
     fs []
     >- metis_tac [sem_e_res]
     >- metis_tac [sem_e_res] >>
     `type_t T (FDOM s1''.store) t`
              by (rw [] >>
                  match_mp_tac type_weakening_t >>
                  metis_tac [sem_e_store, sem_t_store, SUBSET_TRANS, state_rw]) >>
     res_tac >>
     fs [] >>
     Cases_on `r'` >>
     rw [] >>
     fs [] >>
     rw [] >>
     `type_e (FDOM s1'''.store) e2`
              by (rw [] >>
                  match_mp_tac type_weakening_e >>
                  metis_tac [sem_e_store, sem_t_store, SUBSET_TRANS, state_rw]) >>
     imp_res_tac type_sound_e >>
     first_x_assum (qspec_then `s1'''.store` mp_tac) >>
     rw [] >>
     pop_assum (qspec_then `s1'''.clock` mp_tac) >>
     rw [state_rw] >>
     rw [] >>
     Cases_on `r'` >>
     rw [] >>
     fs []
     >- (first_x_assum match_mp_tac >>
         qexists_tac `s` >>
         rw [] >>
         imp_res_tac sem_e_store >>
         imp_res_tac sem_t_store >>
         metis_tac [SUBSET_TRANS]) >>
     metis_tac [sem_e_res]));

(* A type checked program does not Crash. *)

val type_soundness = Q.store_thm("type_soundness",
`!t. type_t F {} t ⇒ semantics t ≠ Crash`,
 rw [semantics_def] >>
 REPEAT STRIP_TAC >>
 imp_res_tac type_sound_t >>
 fs []
 \\ POP_ASSUM (MP_TAC o Q.SPEC `s_with_clock c`)
 \\ REPEAT STRIP_TAC
 \\ fs []
 \\ Cases_on `r` \\ fs[]
 \\ METIS_TAC []);


(* === A relational big-step semantics === *)

val is_rval_def = Define `
(is_rval (Rval _) = T) ∧
(is_rval _ = F)`;

val (sem_e_reln_rules, sem_e_reln_ind, sem_e_reln_cases) = Hol_reln `
(!s x n.
  FLOOKUP s.store x = SOME n
  ⇒
  sem_e_reln s (Var x) (Rval n, s)) ∧
(!s x.
  FLOOKUP s.store x = NONE
  ⇒
  sem_e_reln s (Var x) (Rfail, s)) ∧
(!s n.
  sem_e_reln s (Num n) (Rval n, s)) ∧
(∀s s1 s2 e1 e2 n1 n2.
 sem_e_reln s e1 (Rval n1, s1) ∧
 sem_e_reln s1 e2 (Rval n2, s2)
 ⇒
 sem_e_reln s (Add e1 e2) (Rval (n1 + n2), s2)) ∧
(∀s s1 e1 e2 r.
 ~is_rval r ∧
 sem_e_reln s e1 (r, s1)
 ⇒
 sem_e_reln s (Add e1 e2) (r, s1)) ∧
(∀s s1 s2 e1 e2 n1 r.
 sem_e_reln s e1 (Rval n1, s1) ∧
 ~is_rval r ∧
 sem_e_reln s1 e2 (r, s2)
 ⇒
 sem_e_reln s (Add e1 e2) (r, s2)) ∧
(!s s1 x e n1.
  sem_e_reln s e (Rval n1, s1)
  ⇒
  sem_e_reln s (Assign x e) (Rval n1, s1 with store := s1.store |+ (x,n1))) ∧
(!s s1 x e r.
  ~is_rval r ∧
  sem_e_reln s e (r, s1)
  ⇒
  sem_e_reln s (Assign x e) (r, s1))`;

(* The first argument indicates whether this is a clocked semantics or not *)
val (sem_t_reln_rules, sem_t_reln_ind, sem_t_reln_cases) = Hol_reln `
(!s e r.
  sem_e_reln s e r
  ⇒
  sem_t_reln c s (Exp e) r) ∧
(!s x t r.
  sem_t_reln c (s with store := s.store |+ (x,0)) t r
  ⇒
  sem_t_reln c s (Dec x t) r) ∧
(!s.
  sem_t_reln c s Break (Rbreak, s)) ∧
(!s s1 t1 t2 n1 r.
  sem_t_reln c s t1 (Rval n1, s1) ∧
  sem_t_reln c s1 t2 r
  ⇒
  sem_t_reln c s (Seq t1 t2) r) ∧
(!s s1 t1 t2 r.
  sem_t_reln c s t1 (r, s1) ∧
  ~is_rval r
  ⇒
  sem_t_reln c s (Seq t1 t2) (r, s1)) ∧
(!s s1 e t1 t2 r.
  sem_e_reln s e (Rval 0, s1) ∧
  sem_t_reln c s1 t2 r
  ⇒
  sem_t_reln c s (If e t1 t2) r) ∧
(!s s1 e t1 t2 n r.
  sem_e_reln s e (Rval n, s1) ∧
  n ≠ 0 ∧
  sem_t_reln c s1 t1 r
  ⇒
  sem_t_reln c s (If e t1 t2) r) ∧
(!s s1 e t1 t2 r.
  sem_e_reln s e (r, s1) ∧
  ~is_rval r
  ⇒
  sem_t_reln c s (If e t1 t2) (r, s1)) ∧
(!s s1 e1 e2 t.
  sem_e_reln s e1 (Rval 0, s1)
  ⇒
  sem_t_reln c s (For e1 e2 t) (Rval 0, s1)) ∧
(!s s1 s2 s3 e1 e2 t n1 n2 n3 r.
  sem_e_reln s e1 (Rval n1, s1) ∧
  n1 ≠ 0 ∧
  sem_t_reln c s1 t (Rval n2, s2) ∧
  sem_e_reln s2 e2 (Rval n3, s3) ∧
  sem_t_reln c (dec_clock s3) (For e1 e2 t) r ∧
  (c ⇒ s3.clock ≠ 0)
  ⇒
  sem_t_reln c s (For e1 e2 t) r) ∧
(!s s1 s2 e1 e2 t n1.
  sem_e_reln s e1 (Rval n1, s1) ∧
  n1 ≠ 0 ∧
  sem_t_reln c s1 t (Rbreak, s2)
  ⇒
  sem_t_reln c s (For e1 e2 t) (Rval 0, s2)) ∧
(!s s1 s2 s3 e1 e2 t n1 n2 n3.
  sem_e_reln s e1 (Rval n1, s1) ∧
  n1 ≠ 0 ∧
  sem_t_reln c s1 t (Rval n2, s2) ∧
  sem_e_reln s2 e2 (Rval n3, s3) ∧
  s3.clock = 0 ∧
  c
  ⇒
  sem_t_reln c s (For e1 e2 t) (Rtimeout, s3)) ∧
(!s s1 s2 s3 e1 e2 t n1 n2 r.
  sem_e_reln s e1 (Rval n1, s1) ∧
  n1 ≠ 0 ∧
  sem_t_reln c s1 t (Rval n2, s2) ∧
  sem_e_reln s2 e2 (r, s3) ∧
  ~is_rval r
  ⇒
  sem_t_reln c s (For e1 e2 t) (r, s3)) ∧
(!s s1 s2 e1 e2 t n1 r.
  sem_e_reln s e1 (Rval n1, s1) ∧
  n1 ≠ 0 ∧
  sem_t_reln c s1 t (r, s2) ∧
  ~is_rval r ∧
  r ≠ Rbreak
  ⇒
  sem_t_reln c s (For e1 e2 t) (r, s2)) ∧
(!s s1 e1 e2 t r.
  sem_e_reln s e1 (r, s1) ∧
  ~is_rval r
  ⇒
  sem_t_reln c s (For e1 e2 t) (r, s1))`;

val (simple_sem_t_reln_rules, simple_sem_t_reln_ind, simple_sem_t_reln_cases) =
  Hol_reln `
(!s e r.
  sem_e_reln s e r
  ⇒
  simple_sem_t_reln s (Exp e) r) ∧
(!s x t r.
  simple_sem_t_reln (s with store := s.store |+ (x,0)) t r
  ⇒
  simple_sem_t_reln s (Dec x t) r) ∧
(!s.
  simple_sem_t_reln s Break (Rbreak, s)) ∧
(!s s1 t1 t2 n1 r.
  simple_sem_t_reln s t1 (Rval n1, s1) ∧
  simple_sem_t_reln s1 t2 r
  ⇒
  simple_sem_t_reln s (Seq t1 t2) r) ∧
(!s s1 t1 t2 r.
  simple_sem_t_reln s t1 (r, s1) ∧
  ~is_rval r
  ⇒
  simple_sem_t_reln s (Seq t1 t2) (r, s1)) ∧
(!s s1 e t1 t2 r.
  sem_e_reln s e (Rval 0, s1) ∧
  simple_sem_t_reln s1 t2 r
  ⇒
  simple_sem_t_reln s (If e t1 t2) r) ∧
(!s s1 e t1 t2 n r.
  sem_e_reln s e (Rval n, s1) ∧
  n ≠ 0 ∧
  simple_sem_t_reln s1 t1 r
  ⇒
  simple_sem_t_reln s (If e t1 t2) r) ∧
(!s s1 e t1 t2 r.
  sem_e_reln s e (r, s1) ∧
  ~is_rval r
  ⇒
  simple_sem_t_reln s (If e t1 t2) (r, s1)) ∧
(!s s1 e1 e2 t.
  sem_e_reln s e1 (Rval 0, s1)
  ⇒
  simple_sem_t_reln s (For e1 e2 t) (Rval 0, s1)) ∧
(!s s1 e1 e2 t r.
  sem_e_reln s e1 (r, s1) ∧
  ~is_rval r
  ⇒
  simple_sem_t_reln s (For e1 e2 t) (r, s1)) ∧
(!s s1 s2 s3 e1 e2 t n1 n2 n3 r.
  sem_e_reln s e1 (Rval n1, s1) ∧
  n1 ≠ 0 ∧
  simple_sem_t_reln s1 t (Rval n2, s2) ∧
  sem_e_reln s2 e2 (Rval n3, s3) ∧
  simple_sem_t_reln s3 (For e1 e2 t) r
  ⇒
  simple_sem_t_reln s (For e1 e2 t) r) ∧
(!s s1 s2 e1 e2 t n1.
  sem_e_reln s e1 (Rval n1, s1) ∧
  n1 ≠ 0 ∧
  simple_sem_t_reln s1 t (Rbreak, s2)
  ⇒
  simple_sem_t_reln s (For e1 e2 t) (Rval 0, s2)) ∧
(!s s1 s2 s3 e1 e2 t n1 n2 r.
  sem_e_reln s e1 (Rval n1, s1) ∧
  n1 ≠ 0 ∧
  simple_sem_t_reln s1 t (Rval n2, s2) ∧
  sem_e_reln s2 e2 (r, s3) ∧
  ~is_rval r
  ⇒
  simple_sem_t_reln s (For e1 e2 t) (r, s3)) ∧
(!s s1 s2 e1 e2 t n1 r.
  sem_e_reln s e1 (Rval n1, s1) ∧
  n1 ≠ 0 ∧
  simple_sem_t_reln s1 t (r, s2) ∧
  ~is_rval r ∧
  r ≠ Rbreak
  ⇒
  simple_sem_t_reln s (For e1 e2 t) (r, s2))`;

val OMIT_def = Define `OMIT x = x`;

val OMIT_INTRO = prove(
  ``(P1 ==> P2 ==> Q) ==> (P1 /\ OMIT P2 ==> Q)``,
  fs [OMIT_def]);

val _ = Parse.add_infix("DOWNARROWe",450,Parse.NONASSOC)
val _ = Parse.add_infix("DOWNARROWt",450,Parse.NONASSOC)

val DOWNARROWe_def = Define `$DOWNARROWe (y,x) z = sem_e_reln x y z`;
val DOWNARROWt_def = Define `$DOWNARROWt (y,x) z = simple_sem_t_reln x y z`;

val simple_sem_t_reln_rules = save_thm("simple_sem_t_reln_rules",
  simple_sem_t_reln_rules |> REWRITE_RULE [GSYM DOWNARROWe_def,
                                           GSYM DOWNARROWt_def]);

val simple_sem_t_reln_ind = save_thm("simple_sem_t_reln_ind",
  simple_sem_t_reln_ind
    |> REWRITE_RULE [GSYM DOWNARROWe_def, GSYM DOWNARROWt_def]
    |> Q.SPEC `P` |> UNDISCH_ALL
    |> Q.SPECL [`s`,`t`,`r`] |> Q.GENL [`r`,`s`,`t`]
    |> DISCH_ALL |> Q.GEN `P` |> Q.SPEC `\s t r. P (t,s) r`
    |> SIMP_RULE std_ss [] |> Q.GEN `P`
    |> SPEC_ALL
    |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> DISCH T
    |> MATCH_MP OMIT_INTRO
    |> MATCH_MP OMIT_INTRO
    |> MATCH_MP OMIT_INTRO
    |> MATCH_MP OMIT_INTRO
    |> MATCH_MP OMIT_INTRO
    |> MATCH_MP OMIT_INTRO
    |> MATCH_MP OMIT_INTRO
    |> MATCH_MP OMIT_INTRO
    |> REWRITE_RULE [AND_IMP_INTRO]
    |> UNDISCH
    |> Q.SPECL [`FST (ts:t # state)`,`SND (ts:t # state)`,`rs`]
    |> Q.GEN `rs`
    |> Q.GEN `ts`
    |> SIMP_RULE std_ss []
    |> DISCH_ALL
    |> Q.GEN `P`
    |> REWRITE_RULE [GSYM CONJ_ASSOC]);

val (compact_sem_t_reln_rules, compact_sem_t_reln_ind, compact_sem_t_reln_cases) =
  Hol_reln `
(!s e r.
  sem_e_reln s e r
  ⇒
  compact_sem_t_reln s (Exp e) r) ∧
(!s x t r.
  compact_sem_t_reln (s with store := s.store |+ (x,0)) t r
  ⇒
  compact_sem_t_reln s (Dec x t) r) ∧
(!s.
  compact_sem_t_reln s Break (Rbreak, s)) ∧
(!s s1 t1 t2 n1 r.
  compact_sem_t_reln s t1 (Rval n1, s1) ∧
  compact_sem_t_reln s1 t2 r
  ⇒
  compact_sem_t_reln s (Seq t1 t2) r) ∧
(!s s1 t1 t2 r.
  compact_sem_t_reln s t1 (r, s1) ∧
  ~is_rval r
  ⇒
  compact_sem_t_reln s (Seq t1 t2) (r, s1)) ∧
(!s s1 e t1 t2 r.
  sem_e_reln s e (Rval 0, s1) ∧
  compact_sem_t_reln s1 t2 r
  ⇒
  compact_sem_t_reln s (If e t1 t2) r) ∧
(!s s1 e t1 t2 n r.
  sem_e_reln s e (Rval n, s1) ∧
  n ≠ 0 ∧
  compact_sem_t_reln s1 t1 r
  ⇒
  compact_sem_t_reln s (If e t1 t2) r) ∧
(!s s1 e t1 t2 r.
  sem_e_reln s e (r, s1) ∧
  ~is_rval r
  ⇒
  compact_sem_t_reln s (If e t1 t2) (r, s1)) ∧
(!s s1 e1 e2 t.
  sem_e_reln s e1 (r1, s1) /\
  (if (r1 = Rval n1) \/ n1 <> 0 then
     compact_sem_t_reln s1 t (r2, s2) /\
     (if r2 = Rval n2 then
        sem_e_reln s2 e2 (r3, s3) /\
        (if r3 = Rval n3 then
           compact_sem_t_reln s3 (For e1 e2 t) result
         else
           (result = (r3, s3)))
      else
        (result = (r2, s2)))
   else
     (result = (r1, s1)))
  ⇒
  compact_sem_t_reln s (For e1 e2 t) result)`;

val _ = Parse.add_infix("C_DOWNARROWt",450,Parse.NONASSOC)

val C_DOWNARROWt_def = Define `$C_DOWNARROWt (y,x) z = compact_sem_t_reln x y z`;

val compact_sem_t_reln_rules = save_thm("compact_sem_t_reln_rules",
  compact_sem_t_reln_rules |> REWRITE_RULE [GSYM DOWNARROWe_def,
                                            GSYM C_DOWNARROWt_def]);

val compact_sem_t_reln_ind = save_thm("compact_sem_t_reln_ind",
  compact_sem_t_reln_ind
    |> REWRITE_RULE [GSYM DOWNARROWe_def, GSYM C_DOWNARROWt_def]
    |> Q.SPEC `P` |> UNDISCH_ALL
    |> Q.SPECL [`s`,`t`,`r`] |> Q.GENL [`r`,`s`,`t`]
    |> DISCH_ALL |> Q.GEN `P` |> Q.SPEC `\s t r. P (t,s) r`
    |> SIMP_RULE std_ss [] |> Q.GEN `P`
    |> SPEC_ALL
    |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> DISCH T
    |> MATCH_MP OMIT_INTRO
    |> MATCH_MP OMIT_INTRO
    |> MATCH_MP OMIT_INTRO
    |> MATCH_MP OMIT_INTRO
    |> MATCH_MP OMIT_INTRO
    |> MATCH_MP OMIT_INTRO
    |> MATCH_MP OMIT_INTRO
    |> MATCH_MP OMIT_INTRO
    |> REWRITE_RULE [AND_IMP_INTRO]
    |> UNDISCH
    |> Q.SPECL [`FST (ts:t # state)`,`SND (ts:t # state)`,`rs`]
    |> Q.GEN `rs`
    |> Q.GEN `ts`
    |> SIMP_RULE std_ss []
    |> DISCH_ALL
    |> Q.GEN `P`
    |> REWRITE_RULE [GSYM CONJ_ASSOC]);

val semantics_reln_def = Define `
semantics_reln t =
  case some (r,s). ?c. r ≠ Rtimeout ∧ sem_t_reln T <| store := FEMPTY; clock := c |> t (r, s)  of
     | NONE => Diverge
     | SOME (Rval _, _) => Terminate
     | _ => Crash`;

(* Some proofs relating the relational and functional semantics *)

val big_sem_correct_lem1 = Q.prove (
`∀s e r.
  sem_e_reln s e r
  ⇒
  sem_e s e = r`,
 ho_match_mp_tac sem_e_reln_ind >>
 rw [sem_e_def] >>
 ect >>
 fs [is_rval_def] >>
 imp_res_tac sem_e_res >>
 fs []);

val big_sem_correct_lem2 = Q.prove (
`∀s e r.
  sem_e s e = r
  ⇒
  sem_e_reln s e r`,
 Induct_on `e` >>
 rw [sem_e_def] >>
 rw [Once sem_e_reln_cases] >>
 ect >>
 fs [is_rval_def] >>
 imp_res_tac sem_e_res >>
 fs [] >>
 metis_tac []);

val big_sem_correct_lem3 = Q.prove (
`∀s e r.
  sem_e_reln s e r
  ⇔
  sem_e s e = r`,
 metis_tac [big_sem_correct_lem1, big_sem_correct_lem2]);

val big_sem_correct_lem4 = Q.prove (
`∀s t r.
  sem_t_reln T s t r
  ⇔
  sem_t s t = r`,
 ho_match_mp_tac sem_t_ind >>
 rpt conj_tac
 >- (rw [sem_t_def, Once sem_t_reln_cases] >>
     metis_tac [big_sem_correct_lem1, big_sem_correct_lem2])
 >- (rw [sem_t_def] >>
     rw [Once sem_t_reln_cases])
 >- (rw [sem_t_def] >>
     rw [Once sem_t_reln_cases] >>
     metis_tac [])
 >- (rw [sem_t_def] >>
     rw [Once sem_t_reln_cases] >>
     ect >>
     fs [] >>
     metis_tac [is_rval_def, big_sem_correct_lem1, PAIR_EQ, r_distinct, r_11])
 >- (rw [sem_t_def] >>
     rw [Once sem_t_reln_cases] >>
     ect >>
     fs [] >>
     eq_tac >>
     rw [] >>
     imp_res_tac big_sem_correct_lem1 >>
     fs [] >>
     rw [] >>
     rfs []
     >- metis_tac [is_rval_def, big_sem_correct_lem1, big_sem_correct_lem2, PAIR_EQ, r_distinct, r_11, pair_CASES]
     >- (disj1_tac >>
         imp_res_tac big_sem_correct_lem2 >>
         qexists_tac `r'` >>
         rw [])
     >- metis_tac [is_rval_def, big_sem_correct_lem1, big_sem_correct_lem2, PAIR_EQ, r_distinct, r_11, pair_CASES]
     >- (disj2_tac >>
         disj1_tac >>
         imp_res_tac big_sem_correct_lem2 >>
         qexists_tac `r'` >>
         qexists_tac `i` >>
         rw []) >>
     metis_tac [is_rval_def, big_sem_correct_lem1, big_sem_correct_lem2, PAIR_EQ, r_distinct, r_11, pair_CASES])
 >- (rw [] >>
     rw [Once sem_t_reln_cases, Once sem_t_def] >>
     Cases_on `sem_e s e1` >>
     rw [] >>
     Cases_on `q` >>
     rw [] >>
     PairCases_on `r` >>
     fs [big_sem_correct_lem3] >>
     rw []
     >- metis_tac [is_rval_def, big_sem_correct_lem1, big_sem_correct_lem2, PAIR_EQ, r_distinct, r_11, pair_CASES, PAIR_EQ]
     >- (ect >>
         rw [] >>
         rfs [] >>
         metis_tac [dec_clock_def, is_rval_def, big_sem_correct_lem1, big_sem_correct_lem2, PAIR_EQ, r_distinct, r_11, pair_CASES]) >>
     metis_tac [is_rval_def, big_sem_correct_lem1, big_sem_correct_lem2, PAIR_EQ, r_distinct, r_11, pair_CASES, PAIR_EQ]));

val sem_e_ignores_clock = Q.prove (
`!s t r.
  sem_e_reln s t r
  ⇒
  !c. sem_e_reln (s with clock := c) t (FST r, SND r with clock := c)`,
 ho_match_mp_tac sem_e_reln_ind >>
 rw [] >>
 ONCE_REWRITE_TAC [sem_e_reln_cases] >>
 rw [is_rval_def]
 >- metis_tac []
 >- metis_tac [] >>
 qexists_tac `s1 with clock := c` >>
 rw []);

val big_sem_correct_lem5 = Q.prove (
`∀s e r.
  sem_e_reln (s with clock := (SND r).clock) e r
  ⇔
  (?c. FST r ≠ Rtimeout ∧ sem_e (s with clock := c) e = r)`,
 rw [] >>
 PairCases_on `r` >>
 fs [] >>
 eq_tac >>
 rw [] >>
 imp_res_tac sem_e_clock >>
 fs [] >>
 metis_tac [big_sem_correct_lem1, big_sem_correct_lem2, sem_e_ignores_clock, FST, SND, sem_e_res]);

val _ = export_theory ();
