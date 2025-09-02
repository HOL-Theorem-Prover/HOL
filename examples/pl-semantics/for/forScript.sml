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
 - a very simple type checker (that is proved sound)
 - a clocked relational big-step semantics (and equivalence proof) and
 - a conventional (unclocked) relational big-step semantics (inductive and co-inductive)
*)

open optionTheory pairTheory pred_setTheory finite_mapTheory stringTheory;
open integerTheory;

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
Definition sem_t_def:
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
     | r => r)
Termination
  WF_REL_TAC `(inv_image (measure I LEX measure t_size)
                            (λ(s,t). (s.clock,t)))`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ fs [check_clock_def, dec_clock_def, LET_THM]
  \\ rw []
  \\ imp_res_tac sem_e_clock
  \\ DECIDE_TAC
End

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

fun term_rewrite tms = let
  fun f tm = ASSUME (list_mk_forall(free_vars tm,tm))
  in rand o concl o QCONV (REWRITE_CONV (map f tms)) end

val sem_t_def_with_stop = store_thm ("sem_t_def_with_stop",
  sem_t_def |> concl |> term_rewrite [``check_clock s3 s = s3``,
    ``s.clock <> 0 /\ s3.clock <> 0 <=> s3.clock <> 0``,
    ``sem_t (dec_clock s3) (For e1 e2 t) =
      sem_t (dec_clock s3) (STOP (For e1 e2 t))``],
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

Theorem sem_t_def[compute,allow_rebind] =
  REWRITE_RULE [STOP_def] sem_t_def_with_stop;

(* We also remove the redundant checks from the induction theorem. *)

val sem_t_ind = store_thm("sem_t_ind[allow_rebind]",
  fetch "-" "sem_t_ind"
    |> concl |> term_rewrite [``check_clock s3 s = s3``,
    ``s.clock <> 0 /\ s3.clock <> 0 <=> s3.clock <> 0``],
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

val r_cases_eq = prove_case_eq_thm {
  case_def = definition "r_case_def",
  nchotomy = theorem "r_nchotomy"
};

val pair_cases_eq = Q.prove(
  ‘(pair_CASE p f = v) ⇔ ∃q r. p = (q,r) ∧ v = f q r’,
  Cases_on `p` >> simp[] >> metis_tac[]);

val bool_cases_eq = Q.prove(
  ‘(if p then q else r) = v ⇔ p /\ q = v ∨ ¬p ∧ r = v’,
  Cases_on `p` >> simp[]);

val sem_e_succeeds = Q.store_thm(
  "sem_e_succeeds",
  (* would make this an automatic rewrite except it might break old proofs *)
  ‘sem_e s0 e ≠ (Rbreak, s) ∧ sem_e s0 e ≠ (Rtimeout, s)’,
  metis_tac[sem_e_res]);

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
     rename [‘r_CASE r'’] >>
     reverse (Cases_on `r'`) >>
     fs [] >- metis_tac[sem_e_res] >>
     rename [‘if i = 0 then _ else _’] >> Cases_on `i = 0` >>
     fs [] >>
     dsimp[r_cases_eq, pair_cases_eq, sem_e_succeeds, bool_cases_eq] >>
     rename [‘sem_e s0 gd = (Rval gv, s1)’, ‘sem_t s1 body = (Rval _, _)’] >>
     `type_t T (FDOM s1.store) body`
        by (match_mp_tac type_weakening_t >>
            metis_tac [sem_e_store, sem_t_store, SUBSET_TRANS, state_rw]) >>
     first_x_assum (first_assum o mp_then.mp_then (mp_then.Pos hd) mp_tac) >>
     simp[] >> strip_tac >> rename [‘sem_t s1 body = (body_r, s2)’] >>
     Cases_on ‘body_r’ >> fs[] >>
     rename [‘sem_t s1 body = (Rval bi, s2)’, ‘For gd post body’] >>
     `type_e (FDOM s2.store) post`
          by (match_mp_tac type_weakening_e >>
              metis_tac [sem_e_store, sem_t_store, SUBSET_TRANS, state_rw]) >>
     qspecl_then [‘FDOM s2.store’, ‘post’, ‘s2.store’, ‘s2.clock’]
             mp_tac type_sound_e >> simp[state_rw] >> strip_tac >>
     rename [‘For gd post body’, ‘sem_e s2 post = (pr, s3)’] >>
     Cases_on ‘pr’ >> fs[sem_e_succeeds] >> Cases_on ‘s3.clock = 0’ >> simp[] >>
     fs[] >> first_x_assum irule >> qexists_tac ‘s’ >> simp[] >>
     imp_res_tac sem_e_store >> imp_res_tac sem_t_store >>
     metis_tac[SUBSET_TRANS]));

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

(* === A relational (optionally clocked) big-step semantics === *)

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

(* Some proofs relating the clocked relational and functional semantics *)

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

(* === A relational big-step semantics defined in terms of an inductive and co-inductive relation === *)

(* Inductive relation, equivalent to the unclocked version above*)
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

(* Co-Inductive relation, which defines diverging computations *)
val (simple_sem_t_div_rules,simple_sem_t_div_coind,simple_sem_t_div_cases) = Hol_coreln`
(∀s t x.
  simple_sem_t_div (s with store:= s.store |+ (x,0)) t ⇒
  simple_sem_t_div s (Dec x t)) ∧
(∀s t1 t2.
  simple_sem_t_div s t1 ⇒
  simple_sem_t_div s (Seq t1 t2)) ∧
(∀s t1 t2 n1 s1.
  simple_sem_t_reln s t1 (Rval n1,s1) ∧
  simple_sem_t_div s1 t2 ⇒
  simple_sem_t_div s (Seq t1 t2)) ∧
(∀s e t1 t2 s1.
  sem_e_reln s e (Rval 0, s1) ∧
  simple_sem_t_div s1 t2
  ⇒
  simple_sem_t_div s (If e t1 t2)) ∧
(∀s e t1 t2 n s1.
  sem_e_reln s e (Rval n, s1) ∧
  n ≠ 0 ∧
  simple_sem_t_div s1 t1
  ⇒
  simple_sem_t_div s (If e t1 t2)) ∧
(∀s e1 e2 t n1 s1.
  sem_e_reln s e1 (Rval n1, s1) ∧
  n1 ≠ 0 ∧
  simple_sem_t_div s1 t ⇒
  simple_sem_t_div s (For e1 e2 t)) ∧
(∀s e1 e2 t n1 s1 n2 s2 n3 s3.
  sem_e_reln s e1 (Rval n1, s1) ∧
  n1 ≠ 0 ∧
  simple_sem_t_reln s1 t (Rval n2, s2) ∧
  sem_e_reln s2 e2 (Rval n3, s3) ∧
  simple_sem_t_div s3 (For e1 e2 t)
  ⇒
  simple_sem_t_div s (For e1 e2 t))`

val init_store_def = Define`
  init_store = <|store:=FEMPTY;clock:=0|>`

(* Top observable semantics for the unclocked relational semantics *)
val rel_semantics_def = Define `
  rel_semantics t =
  if (?v s. simple_sem_t_reln init_store t (Rval v,s)) then
    Terminate
  else if simple_sem_t_div init_store t then
    Diverge
  else Crash`

(* Proofs relating clocked functional big step to unclocked relational semantics *)
val simple_sem_t_reln_strongind = fetch "-" "simple_sem_t_reln_strongind"

val semttac = simp[Once simple_sem_t_reln_cases,is_rval_def]
val semetac = simp[Once sem_e_reln_cases]

(* Determinism of simple_sem_t_reln *)
val sem_e_reln_determ = Q.store_thm("sem_e_reln_determ",
`∀s e res.
  sem_e_reln s e res ⇒
  ∀res'. sem_e_reln s e res' ⇒ res=res'`,
  rw[]>>
  fs[big_sem_correct_lem3])

val simple_sem_t_reln_determ = Q.prove(
`∀s t res.
 simple_sem_t_reln s t res ⇒
 ∀res'. simple_sem_t_reln s t res' ⇒ res = res'`,
 ho_match_mp_tac simple_sem_t_reln_strongind>>
 rw[]>>pop_assum mp_tac >> semttac>>fs[FORALL_PROD]>>
 TRY(Cases_on`res`)>>
 TRY(Cases_on`res'`)
 >- metis_tac[sem_e_reln_determ]
 >>rw[]>>fs[]>>res_tac>>fs[]>>
   imp_res_tac sem_e_reln_determ>>fs[]>>
   res_tac>>fs[]>>imp_res_tac sem_e_reln_determ>>fs[]>>
   metis_tac[is_rval_def])

val _ = save_thm("simple_sem_t_reln_determ", simple_sem_t_reln_determ)

(* Disjointness of simple_sem_t_reln and simple_sem_t_div*)
val simple_sem_t_reln_not_div = Q.prove(
`∀s t res.
  (simple_sem_t_reln s t res ⇒
  ¬ simple_sem_t_div s t)`,
  ho_match_mp_tac simple_sem_t_reln_strongind>>rw[]>>
  TRY(Cases_on`res`)>>
  simp[Once simple_sem_t_div_cases]>>
  fs[METIS_PROVE [] `` A ∨ B ⇔ ¬A ⇒ B``]
  >> rpt
    (rw[]>>
    imp_res_tac sem_e_reln_determ>>fs[]>>
    imp_res_tac simple_sem_t_reln_determ>>fs[is_rval_def]))

val _ = save_thm("simple_sem_t_reln_not_div", simple_sem_t_reln_not_div)

val simple_sem_t_reln_ignores_clock = Q.prove(
`∀s t res.
 simple_sem_t_reln s t res ⇒
 ∀c. simple_sem_t_reln (s with clock:=c) t (FST res,SND res with clock:=c)`,
 ho_match_mp_tac simple_sem_t_reln_strongind>>
 rw[]>>fs[EXISTS_PROD]>>semttac>>
 imp_res_tac sem_e_ignores_clock>>fs[]>>
 metis_tac[])

val clock_rm = Q.prove(
`∀s. s with clock:=s.clock = s`, fs[state_component_equality])

(* sem_t_reln wth clock imples simple_sem_t_reln *)
val sem_t_reln_imp_simple_sem_t_reln = Q.prove(
`∀s t r.
 sem_t_reln T s t r ⇒
 FST r ≠ Rtimeout ⇒
 simple_sem_t_reln s t (FST r,SND r with clock := s.clock)`,
 ho_match_mp_tac sem_t_reln_ind>>rw[]>>
 semttac>>fs[]>>
 imp_res_tac sem_e_ignores_clock>>
 imp_res_tac simple_sem_t_reln_ignores_clock>>
 fs[dec_clock_def,is_rval_def]>>
 TRY(metis_tac[clock_rm,is_rval_def]))

(* Functional big step not time out implies simple_sem_t_reln *)
val sem_t_imp_simple_sem_t_reln = save_thm ("sem_t_imp_simple_sem_t_reln",sem_t_reln_imp_simple_sem_t_reln |> REWRITE_RULE[big_sem_correct_lem4,AND_IMP_INTRO]|>SIMP_RULE std_ss[FORALL_PROD])

(* simple_sem_t_reln implies there exists a clock for sem_t that does not timeout *)

val inst_1 = qpat_x_assum`∀c'.∃c. A= (FST r,B)` (qspec_then`c'` assume_tac)
fun inst_2 q = qpat_x_assum`∀c'.∃c. A= B` (qspec_then q assume_tac)

val simple_sem_t_reln_imp_sem_t = Q.prove(
`∀s t r.
 simple_sem_t_reln s t r ⇒
 ∀c'. ∃c. sem_t (s with clock:=c) t = (FST r,(SND r) with clock:=c')`,
 ho_match_mp_tac simple_sem_t_reln_strongind>>rw[]>>
 fs[sem_t_def_with_stop,GSYM big_sem_correct_lem3]>>
 imp_res_tac sem_e_ignores_clock>>
 fs[big_sem_correct_lem3]>>
 TRY(metis_tac[clock_rm])
 >-
   (inst_1>>fs[]>>inst_2`c`>>fs[]>>
   qexists_tac`c''`>>fs[])
 >-
   (first_x_assum(qspec_then`c'`assume_tac)>>fs[]>>
   qexists_tac`c`>>fs[]>>
   ect>>fs[is_rval_def])
 >-
   (ect>>fs[is_rval_def]>>
   metis_tac[clock_rm])
 >-
   (ect>>fs[is_rval_def]>>
   metis_tac[clock_rm])
 >-
   (inst_1>>fs[]>>inst_2`c+1`>>fs[]>>
   qexists_tac`c''`>>fs[dec_clock_def]>>
   first_x_assum(qspec_then`c`assume_tac)>>fs[]>>
   simp[Once STOP_def,Once sem_t_def_with_stop]>>
   fs[dec_clock_def])
 >>
   (inst_2`c'`>>fs[]>>qexists_tac`c`>>fs[]>>ect>>fs[is_rval_def]))

(*val _ = save_thm("simple_sem_t_reln_imp_sem_t",
simple_sem_t_reln_imp_sem_t |> SIMP_RULE std_ss [FORALL_PROD])*)

val sem_e_reln_not_timeout = prove(``
 ∀s e r.
 sem_e_reln s e r ⇒ FST r ≠ Rtimeout``,
 ho_match_mp_tac sem_e_reln_ind >>rw[])

val simple_sem_t_reln_not_timeout = prove(``
  ∀s t r. simple_sem_t_reln s t r ⇒ FST r ≠ Rtimeout``,
  ho_match_mp_tac simple_sem_t_reln_ind>>rw[]>>
  TRY(metis_tac[sem_e_reln_not_timeout,FST]))

val simple_sem_t_reln_iff_sem_t = store_thm("simple_sem_t_reln_iff_sem_t",``
   ∀s t r s'.
   simple_sem_t_reln s t (r,s' with clock:=s.clock) ⇔
   ∃c'. sem_t (s with clock:=c') t = (r,s') ∧ r ≠ Rtimeout``,
   rw[]>>EQ_TAC>>strip_tac>>fs[]
   >-
     (imp_res_tac simple_sem_t_reln_imp_sem_t>>fs[]>>
     first_assum(qspec_then`s'.clock` assume_tac)>>fs[clock_rm]>>
     metis_tac[simple_sem_t_reln_not_timeout,FST])
   >>
     imp_res_tac sem_t_imp_simple_sem_t_reln>>
     fs[]>>
     imp_res_tac simple_sem_t_reln_ignores_clock>>
     first_assum(qspec_then`s.clock` assume_tac)>>fs[clock_rm])

(* Next, we prove that simple_sem_t_div covers all diverging cases of sem_t *)

val sem_e_reln_same_clock = Q.prove(
 `sem_e_reln s e (v,r) ⇒ r.clock = s.clock`,
 rw[]>>imp_res_tac sem_e_ignores_clock>>
 pop_assum(qspec_then`s.clock` assume_tac)>>fs[clock_rm]>>
 imp_res_tac sem_e_reln_determ>>fs[state_component_equality])

val sem_e_clock_inc = Q.prove(
 `∀s e r.
  sem_e s e = r ⇒
  ∀k. sem_e (s with clock:= s.clock+k) e =(FST r,(SND r)with clock:= (SND r).clock+k)`,
  rw[]>>Cases_on`sem_e s e`>>Cases_on`q`>>
  TRY (metis_tac[sem_e_res] )>>
  fs[GSYM big_sem_correct_lem3]>>
  imp_res_tac sem_e_ignores_clock>>
  imp_res_tac sem_e_reln_same_clock>>
  fs[])

val LTE_SUM =
  arithmeticTheory.LESS_EQ_EXISTS
  |> Q.SPECL[`A`,`B`]
  |> CONV_RULE(RAND_CONV(RAND_CONV(ALPHA_CONV``C:num``)))
  |> Q.GENL[`A`,`B`]

val LT_SUM = Q.prove(
 `∀A:num B. A < B ⇒ ∃C. B = A+C ∧ C > 0`,
 Induct>>fs[]>>rw[]>>
 Cases_on`B`>>fs[]>>res_tac>>
 qexists_tac`C`>>fs[]>>
 DECIDE_TAC)

(* Everything above current clock gives same result if didn't time out*)
local val rw = srw_tac[] val fs = fsrw_tac[] in
val sem_t_clock_inc = Q.prove(
`∀s t r.
  sem_t s t = r ∧ FST r ≠ Rtimeout ⇒
  ∀k. sem_t (s with clock:= s.clock+k) t =(FST r,(SND r)with clock:= (SND r).clock+k)`,
  ho_match_mp_tac sem_t_ind>>rw[]>>fs[sem_e_clock]>>
  TRY(fs[sem_t_def_with_stop]>>NO_TAC)
  >-
    (fs[sem_t_def_with_stop]>>Cases_on`sem_e s e`>>Cases_on`q`>>
    metis_tac[sem_e_res,sem_e_clock_inc,FST,SND])
  >-
    (fs[sem_t_def_with_stop]>>Cases_on`sem_t s t`>>Cases_on`q`>>fs[])
  >-
    (fs[sem_t_def_with_stop]>>Cases_on`sem_e s e`>>Cases_on`q`>>fs[sem_e_res]>>
    imp_res_tac sem_e_clock_inc>>
    pop_assum(qspec_then`k` assume_tac)>>fs[])
  >>
    pop_assum mp_tac>> simp[sem_t_def_with_stop]>>
    Cases_on`sem_e s e1`>>Cases_on`q`>>fs[]>>
    imp_res_tac sem_e_clock_inc>>fs[]>>
    TRY(pop_assum(qspec_then`k` assume_tac))>>
    fs[DECIDE ``(A:num)+B = B+A``]>>
    IF_CASES_TAC>>fs[]>>
    Cases_on`sem_t r t`>>Cases_on`q`>>fs[]>>
    Cases_on`sem_e r' e2`>>Cases_on`q`>>fs[]>>
    imp_res_tac sem_e_clock_inc>>fs[]>>
    TRY(pop_assum(qspec_then`k` assume_tac))>>
    fs[DECIDE ``(A:num)+B = B+A``]>>
    IF_CASES_TAC>>fs[]>>rw[]>>
    fs[dec_clock_def,STOP_def]>>
    `1 ≤ r''.clock` by DECIDE_TAC>>
    metis_tac[arithmeticTheory.LESS_EQ_ADD_SUB])
end

val _ = save_thm ("sem_t_clock_inc", sem_t_clock_inc |> SIMP_RULE std_ss [FORALL_PROD]);

(* If current clock times out, everything below it timesout *)
val sem_t_clock_dec = Q.prove(
`∀s t r.
  sem_t s t = r ∧ FST r = Rtimeout ⇒
  ∀c. c ≤ s.clock ⇒
  FST(sem_t (s with clock:= c) t) = Rtimeout`,
  rw[]>>CCONTR_TAC>>
  Cases_on`sem_t (s with clock:=c) t`>>Cases_on`q`>>fs[]>>
  imp_res_tac sem_t_clock_inc>>fs[]>>
  imp_res_tac LTE_SUM>>
  rename [‘s.clock = c0 + cdelta’] >>
  first_x_assum(qspec_then`cdelta` assume_tac)>>rfs[]>>
  qpat_x_assum`s.clock=A` (SUBST_ALL_TAC o SYM)>>fs[clock_rm]);

(* Functional big step divergence *)
val sem_t_div_def = Define`
  sem_t_div s t ⇔
  (∀c. FST (sem_t (s with clock:=c) t) = Rtimeout)`;

val clock_rm_simp_tac =
    fs[GSYM big_sem_correct_lem3]>>
    imp_res_tac sem_e_ignores_clock>>
    fs[big_sem_correct_lem3]

(* Proof is split into two directions *)
val simple_sem_t_div_sem_t_div = Q.prove(
`∀s t.
  simple_sem_t_div s t ⇒
  sem_t_div s t`,
  rw[]>>
  assume_tac simple_sem_t_reln_not_div>>
  fs[METIS_PROVE [] ``A ⇒ ¬B ⇔ B ⇒ ¬A``]>>
  res_tac>>fs[sem_t_div_def]>>
  CCONTR_TAC>>fs[]>>
  Cases_on`sem_t (s with clock:=c) t`>>Cases_on`q`>>fs[]>>
  imp_res_tac sem_t_imp_simple_sem_t_reln>>fs[]>>
  imp_res_tac simple_sem_t_reln_ignores_clock>>
  pop_assum(qspec_then`s.clock` assume_tac)>>fs[clock_rm]>>
  metis_tac[]);

val sem_t_div_simple_sem_t_div = Q.prove(
 `∀s t.
  sem_t_div s t ⇒
  simple_sem_t_div s t`,
  ho_match_mp_tac simple_sem_t_div_coind>>
  fs[sem_t_div_def]>>
  Cases_on`t`>>
  fs[Once sem_t_def_with_stop]
  >-
    (rw[]>>
    metis_tac[sem_e_res,FST,PAIR])
  >-
    (fs[METIS_PROVE [] `` A ∨ B ⇔ ¬A ⇒ B``]>>rw[]>>
    Cases_on`sem_t (s with clock:=c) t'`>>Cases_on`q`>>fs[]>>
    TRY(first_x_assum(qspec_then`c`assume_tac)>>rfs[]>>NO_TAC)>>
    imp_res_tac sem_t_imp_simple_sem_t_reln>>fs[]>>
    imp_res_tac simple_sem_t_reln_ignores_clock>>
    pop_assum(qspec_then`s.clock`assume_tac)>>fs[clock_rm]>>
    qexists_tac`i`>>
    qexists_tac`r with clock:=s.clock`>>fs[is_rval_def]>>
    rw[]>>Cases_on`c' ≤ r.clock`
    >-
      (first_x_assum(qspec_then`c`mp_tac)>>fs[]>>rw[]>>
      imp_res_tac sem_t_clock_dec>>
      metis_tac[])
    >>
      `r.clock ≤ c'` by DECIDE_TAC>>
      imp_res_tac LTE_SUM>>
      imp_res_tac sem_t_clock_inc>>fs[]>>
      rename [‘¬(cdelta + r.clock ≤ r.clock)’] >>
      pop_assum(qspec_then`cdelta` assume_tac)>>fs[]>>
      first_x_assum(qspec_then`c+cdelta`mp_tac)>>fs[]>>rw[])
  >-
    (fs[METIS_PROVE [] `` A ∨ B ⇔ ¬A ⇒ B``]>>rw[]>>
    Cases_on`sem_e s e`>>Cases_on`q`>>fs[]>>
    clock_rm_simp_tac>>TRY(metis_tac[sem_e_res]))
  >>
    fs[METIS_PROVE [] `` A ∨ B ⇔ ¬A ⇒ B``]>>rw[]>>
    fs[big_sem_correct_lem3]>>
    Cases_on`sem_e s e0`>>Cases_on`q`>>fs[]>>
    clock_rm_simp_tac>>TRY(metis_tac[sem_e_res])>>
    Cases_on`i = 0`>>fs[]>>
    Cases_on`sem_t (r with clock:=c) t'`>>Cases_on`q`>>fs[]>>
    TRY(last_x_assum(qspec_then`c`assume_tac)>>rfs[]>>NO_TAC)>>
    imp_res_tac sem_t_imp_simple_sem_t_reln>>fs[]>>
    imp_res_tac simple_sem_t_reln_ignores_clock>>
    pop_assum(qspec_then`r.clock`assume_tac)>>fs[clock_rm]>>
    Cases_on`sem_e (r' with clock:=r.clock) e`>>Cases_on`q`>>fs[]>>
    clock_rm_simp_tac>>TRY(metis_tac[sem_e_res])>>
    TRY(last_x_assum(qspec_then`c`assume_tac)>>rfs[]>>
    last_x_assum(qspec_then`r'.clock` assume_tac)>>fs[clock_rm]>>NO_TAC)>>
    qexists_tac`i'`>>
    qexists_tac`r' with clock:=r.clock`>>fs[]>>rw[]>>
    Cases_on`c' ≤ r'.clock`
    >-
      (last_x_assum(qspec_then`c+1`mp_tac)>>
      imp_res_tac sem_t_clock_inc>>fs[]>>
      rw[]>>
      imp_res_tac sem_t_clock_dec>>
      fs[dec_clock_def,Once STOP_def]>>
      pop_assum mp_tac>>
      qpat_abbrev_tac`A = r'' with clock := B`>>
      qpat_abbrev_tac`B = For C D E`>>
      rw[]>>pop_assum(qspecl_then[`B`,`A`] assume_tac)>>
      UNABBREV_ALL_TAC>>fs[])
    >>
      `r'.clock ≤ c'` by DECIDE_TAC>>
      imp_res_tac LTE_SUM>>
      imp_res_tac sem_t_clock_inc>>fs[]>>
      rename [‘¬(cdelta + r'.clock ≤ r'.clock)’] >>
      pop_assum(qspec_then`cdelta+1` assume_tac)>>fs[]>>
      last_x_assum(qspec_then`c+(cdelta+1)`mp_tac)>>fs[]>>
      fs[STOP_def,dec_clock_def]>>
      `r'.clock + (cdelta+1)-1 = r'.clock + cdelta` by DECIDE_TAC>>fs[]);

val simple_sem_t_div_iff_sem_t_div = Q.prove(
`∀s t.
  sem_t_div s t ⇔
  simple_sem_t_div s t`,
  metis_tac[sem_t_div_simple_sem_t_div,simple_sem_t_div_sem_t_div])

val _ = save_thm("simple_sem_t_div_iff_sem_t_div",simple_sem_t_div_iff_sem_t_div|>REWRITE_RULE[sem_t_div_def]);

(* We can transfer the type soundness proof from FBS directly *)
val reln_type_soundness = Q.prove(
`!t. type_t F {} t ⇒
 rel_semantics t ≠ Crash`,
 ntac 2 strip_tac>>fs[rel_semantics_def]>>
 imp_res_tac type_soundness>>fs[semantics_def]>>pop_assum mp_tac>>
 IF_CASES_TAC>>fs[s_with_clock_def,init_store_def]
 >-
   (imp_res_tac sem_t_imp_simple_sem_t_reln>>fs[]>>
   imp_res_tac simple_sem_t_reln_ignores_clock>>
   pop_assum(qspec_then`0` assume_tac)>>fs[]>>
   IF_CASES_TAC>>fs[]>>metis_tac[])
 >>
 ntac 3 (IF_CASES_TAC>>fs[])>>
 pop_assum mp_tac>>fs[]>>
 match_mp_tac sem_t_div_simple_sem_t_div>>fs[sem_t_div_def]>>
 metis_tac[FST])

(* Pretty big-step semantics, inductive interpretation only *)

(* Wrapping the datatypes *)
val _ = Datatype `
pbr =
  | Ter (r#state)
  | Div`;

val _ = Datatype `
pbt =
  | Trm t
  | Forn num pbr e e t`;

val abort_def = Define`
  (abort flag Div ⇔ T) ∧
  (abort flag (Ter (r,s)) ⇔ ¬ is_rval r ∧ (flag ⇒ r ≠ Rbreak))`

val (pb_sem_t_reln_rules,pb_sem_t_reln_ind,pb_sem_t_reln_cases) = Hol_reln`
(!s e r.
  sem_e_reln s e r
  ⇒
  pb_sem_t_reln s (Trm(Exp e)) (Ter r)) ∧
(!s x t r.
  pb_sem_t_reln (s with store := s.store |+ (x,0)) (Trm t) r
  ⇒
  pb_sem_t_reln s (Trm(Dec x t)) r) ∧
(* Initial For runs the guard *)
(!s r r1 e1 e2 t.
  sem_e_reln s e1 r1 ∧
  pb_sem_t_reln s (Forn 1 (Ter r1) e1 e2 t) r
  ⇒
  pb_sem_t_reln s (Trm (For e1 e2 t)) r) ∧
(* For 1 checks the guard value (and possibly) runs the body *)
(!s s' e1 e2 t.
  pb_sem_t_reln s' (Forn 1 (Ter (Rval 0,s)) e1 e2 t) (Ter (Rval 0,s))) ∧
(!s s' e1 e2 t r r3 n.
  pb_sem_t_reln s (Trm t) r3 ∧
  pb_sem_t_reln s (Forn 2 r3 e1 e2 t) r ∧
  n ≠ 0 ⇒
  pb_sem_t_reln s' (Forn 1 (Ter (Rval n,s)) e1 e2 t) r) ∧
(* For 2 checks the result of the body and runs the step *)
(!s s' e1 e2 t.
  pb_sem_t_reln s' (Forn 2 (Ter (Rbreak,s)) e1 e2 t) (Ter (Rval 0,s))) ∧
(!s s' r r2 e1 e2 t n.
  sem_e_reln s e2 r2 ∧
  pb_sem_t_reln s (Forn 3 (Ter r2) e1 e2 t) r ⇒
  pb_sem_t_reln s' (Forn 2 (Ter (Rval n,s)) e1 e2 t) r) ∧
(* For 3 runs the loop again *)
(!s s' r e1 e2 t n.
  pb_sem_t_reln s (Trm (For e1 e2 t)) r ⇒
  pb_sem_t_reln s' (Forn 3 (Ter (Rval n,s)) e1 e2 t) r) ∧
(* One rule for all the breaks and divergence *)
(!s r e1 e2 t i.
  abort (i = 2) r ⇒
  pb_sem_t_reln s (Forn i r e1 e2 t) r) ∧
(!s.
  pb_sem_t_reln s (Trm(Break)) (Ter (Rbreak, s))) ∧
(*Seq and If can be changed to pretty-big-step too, although they will have a similar number of raw rules*)
(!s s1 t1 t2 n1 r.
  pb_sem_t_reln s (Trm t1) (Ter (Rval n1, s1)) ∧
  pb_sem_t_reln s1 (Trm t2) r
  ⇒
  pb_sem_t_reln s (Trm (Seq t1 t2)) r) ∧
(!s t1 t2 r.
  pb_sem_t_reln s (Trm t1) r ∧
  abort F r ⇒
  pb_sem_t_reln s (Trm (Seq t1 t2)) r) ∧
(!s s1 e t1 t2 r.
  sem_e_reln s e (Rval 0, s1) ∧
  pb_sem_t_reln s1 (Trm t2) r
  ⇒
  pb_sem_t_reln s (Trm (If e t1 t2)) r) ∧
(!s s1 e t1 t2 n r.
  sem_e_reln s e (Rval n, s1) ∧
  n ≠ 0 ∧
  pb_sem_t_reln s1 (Trm t1) r
  ⇒
  pb_sem_t_reln s (Trm (If e t1 t2)) r) ∧
(!s s1 e t1 t2 r.
  sem_e_reln s e (r, s1) ∧
  ~is_rval r
  ⇒
  pb_sem_t_reln s (Trm (If e t1 t2)) (Ter (r, s1)))`;

(* The first argument of pb_sem_t_size_reln is used as an explicit size measure to facilitate induction on derivation trees in our proofs *)
val (pb_sem_t_size_reln_rules,pb_sem_t_size_reln_ind,pb_sem_t_size_reln_cases) = Hol_reln`
(!s e r.
  sem_e_reln s e r
  ⇒
  pb_sem_t_size_reln 0n s (Trm(Exp e)) (Ter r)) ∧
(!s x t r.
  pb_sem_t_size_reln h (s with store := s.store |+ (x,0)) (Trm t) r
  ⇒
  pb_sem_t_size_reln (h+1) s (Trm(Dec x t)) r) ∧
(* Initial For runs the guard *)
(!s r r1 e1 e2 t.
  sem_e_reln s e1 r1 ∧
  pb_sem_t_size_reln h s (Forn 1 (Ter r1) e1 e2 t) r
  ⇒
  pb_sem_t_size_reln (h+1) s (Trm (For e1 e2 t)) r) ∧
(* For 1 checks the guard value (and possibly) runs the body *)
(!s s' e1 e2 t.
  pb_sem_t_size_reln 0 s' (Forn 1 (Ter (Rval 0,s)) e1 e2 t) (Ter (Rval 0,s))) ∧
(!s s' e1 e2 t r r3 n.
  pb_sem_t_size_reln h s (Trm t) r3 ∧
  pb_sem_t_size_reln h' s (Forn 2 r3 e1 e2 t) r ∧
  n ≠ 0 ⇒
  pb_sem_t_size_reln (h+h'+1) s' (Forn 1 (Ter (Rval n,s)) e1 e2 t) r) ∧
(* For 2 checks the result of the body and runs the step *)
(!s s' e1 e2 t.
  pb_sem_t_size_reln 0 s' (Forn 2 (Ter (Rbreak,s)) e1 e2 t) (Ter (Rval 0,s))) ∧
(!s s' r r2 e1 e2 t n.
  sem_e_reln s e2 r2 ∧
  pb_sem_t_size_reln h s (Forn 3 (Ter r2) e1 e2 t) r ⇒
  pb_sem_t_size_reln (h+1) s' (Forn 2 (Ter (Rval n,s)) e1 e2 t) r) ∧
(* For 3 runs the loop again *)
(!s s' r e1 e2 t n.
  pb_sem_t_size_reln h s (Trm (For e1 e2 t)) r ⇒
  pb_sem_t_size_reln (h+1) s' (Forn 3 (Ter (Rval n,s)) e1 e2 t) r) ∧
(* One rule for all the breaks and divergence *)
(!s r e1 e2 t i.
  abort (i = 2) r ⇒
  pb_sem_t_size_reln 0 s (Forn i r e1 e2 t) r) ∧
(!s.
  pb_sem_t_size_reln 0 s (Trm(Break)) (Ter (Rbreak, s))) ∧
(*Seq and If can be changed to pretty-big-step too, although they will have a similar number of raw rules*)
(!s s1 t1 t2 n1 r.
  pb_sem_t_size_reln h s (Trm t1) (Ter (Rval n1, s1)) ∧
  pb_sem_t_size_reln h' s1 (Trm t2) r
  ⇒
  pb_sem_t_size_reln (h+h'+1) s (Trm (Seq t1 t2)) r) ∧
(!s t1 t2 r.
  pb_sem_t_size_reln h s (Trm t1) r ∧
  abort F r ⇒
  pb_sem_t_size_reln (h+1) s (Trm (Seq t1 t2)) r) ∧
(!s s1 e t1 t2 r.
  sem_e_reln s e (Rval 0, s1) ∧
  pb_sem_t_size_reln h s1 (Trm t2) r
  ⇒
  pb_sem_t_size_reln (h+1) s (Trm (If e t1 t2)) r) ∧
(!s s1 e t1 t2 n r.
  sem_e_reln s e (Rval n, s1) ∧
  n ≠ 0 ∧
  pb_sem_t_size_reln h s1 (Trm t1) r
  ⇒
  pb_sem_t_size_reln (h+1) s (Trm (If e t1 t2)) r) ∧
(!s s1 e t1 t2 r.
  sem_e_reln s e (r, s1) ∧
  ~is_rval r
  ⇒
  pb_sem_t_size_reln 0 s (Trm (If e t1 t2)) (Ter (r, s1)))`;

val _ = set_trace "Goalstack.print_goal_at_top" 0;

val pbrsem_tac = simp[Once pb_sem_t_size_reln_cases]

(* Connect pretty-big-step to relational semantics *)
Triviality reln_to_pb_reln:
  ∀s t r.
    simple_sem_t_reln s t r ⇒
    ∃h. pb_sem_t_size_reln h s (Trm t) (Ter r)
Proof
  ho_match_mp_tac simple_sem_t_reln_ind>>
  rw[]>>TRY(pbrsem_tac>>metis_tac[abort_def])
  (*FOR equivalence*)
  >- metis_tac[pb_sem_t_size_reln_cases,abort_def]
  >-
    (pbrsem_tac>>pbrsem_tac>>simp[abort_def]>>
    metis_tac[pb_sem_t_size_reln_cases,abort_def])
  >-
    (pbrsem_tac>>
    qexists_tac`h+h'+3`>>
    qexists_tac`Rval n1,s'`>>pbrsem_tac>>
    qexists_tac`h`>>qexists_tac`h'+2`>>simp[]>>
    qexists_tac`Ter(Rval n2,s2)`>>pbrsem_tac>>
    qexists_tac`h'+1`>>qexists_tac`Rval n3,s''`>>pbrsem_tac)
  >-
    (pbrsem_tac>>metis_tac[pb_sem_t_size_reln_cases])
  >-
    (pbrsem_tac>>
     qexists_tac`h+2`>>
     qexists_tac`Rval n1,s'`>>pbrsem_tac>>
     qexists_tac`h`>>qexists_tac`1`>>simp[]>>
     qexists_tac`Ter(Rval n2,s2)`>>pbrsem_tac>>
     qexists_tac`(r,s3)`>>pbrsem_tac>>
     metis_tac[abort_def])
  >-
    (pbrsem_tac>>
     qexists_tac`h+1`>>
     goal_assum drule >>
     pbrsem_tac>>
     first_assum (goal_assum o
                  resolve_then.resolve_then (resolve_then.Pos (el 2)) mp_tac) >>
     simp[integerTheory.EQ_ADDL] >>
     pbrsem_tac>>
     metis_tac[abort_def])
QED

local val fs = fsrw_tac[] in
val pb_reln_to_reln = prove(``
  ∀n s t r.
  pb_sem_t_size_reln n s (Trm t) (Ter r) ⇒
  simple_sem_t_reln s t r``,
  completeInduct_on`n`>>simp[Once pb_sem_t_size_reln_cases]>>rw[]>>
  TRY(semttac>>NO_TAC)>>
  `h < h+1 ∧
   h < h+(h'+1) ∧
   h' < h+(h'+1)` by DECIDE_TAC>>
  Cases_on`r`>>TRY(semttac>>metis_tac[abort_def])>>
  ntac 3 (pop_assum kall_tac)>>
  pop_assum mp_tac>>
  pbrsem_tac>>rw[]>>
  TRY(semttac>>metis_tac[abort_def])>>
  qpat_x_assum`pb_sem_t_size_reln A B (Forn 2 _ _ _ _) _` mp_tac>>
  pbrsem_tac>>rw[]>>fs[]>>
  `h' < h' +1 +1` by DECIDE_TAC>>
  TRY(semttac>>metis_tac[abort_def])>>
  qpat_x_assum`pb_sem_t_size_reln A B (Forn 3 _ _ _ _) _` mp_tac>>
  pbrsem_tac>>rw[]>>fs[]>>
  `h' < h' +2 +1` by DECIDE_TAC>>
  `h' < h'+(h''+1+1+1)+1` by DECIDE_TAC>>
  `h'' < h'+(h''+1+1+1)+1` by DECIDE_TAC>>
  TRY(semttac>>metis_tac[abort_def]))
end

val pb_sem_t_size_reln_equiv_lemma1 = prove(``
  ∀n s t r.
    pb_sem_t_size_reln n s t r ⇒
    pb_sem_t_reln s t r``,
  HO_MATCH_MP_TAC pb_sem_t_size_reln_ind \\ rw []
  \\ once_rewrite_tac [pb_sem_t_reln_cases] \\ fs []
  \\ metis_tac []);

val pb_sem_t_size_reln_equiv_lemma2 = prove(``
  ∀s t r.
    pb_sem_t_reln s t r ==>
    ?n. pb_sem_t_size_reln n s t r``,
  HO_MATCH_MP_TAC pb_sem_t_reln_ind \\ rw []
  \\ once_rewrite_tac [pb_sem_t_size_reln_cases] \\ fs []
  \\ metis_tac []);

val pb_sem_t_size_reln_equiv = store_thm("pb_sem_t_size_reln_equiv",
  ``∀s t r. pb_sem_t_reln s t r ⇔ ∃n. pb_sem_t_size_reln n s t r``,
  metis_tac [pb_sem_t_size_reln_equiv_lemma2,pb_sem_t_size_reln_equiv_lemma1]);

(* Pretty printing for paper *)
val OMIT_def = Define `OMIT x = x`;

val OMIT_INTRO = prove(
  ``(P1 ==> P2 ==> Q) ==> (P1 /\ OMIT P2 ==> Q)``,
  fs [OMIT_def]);

val _ = Parse.add_infix("DOWNARROWe",450,Parse.NONASSOC)
val _ = Parse.add_infix("DOWNARROWt",450,Parse.NONASSOC)

val DOWNARROWe_def = Define `$DOWNARROWe (y,x) z = sem_e_reln x y z`;
val DOWNARROWt_def = Define `$DOWNARROWt (y,x) z = simple_sem_t_reln x y z`;

Theorem simple_sem_t_reln_rules[allow_rebind] =
  simple_sem_t_reln_rules
    |> REWRITE_RULE [GSYM DOWNARROWe_def, GSYM DOWNARROWt_def];

Theorem simple_sem_t_reln_ind[allow_rebind] =
  simple_sem_t_reln_ind
    |> REWRITE_RULE [GSYM DOWNARROWe_def, GSYM DOWNARROWt_def]
    |> Q.SPEC `P` |> UNDISCH_ALL
    |> Q.SPECL [`s`,`t`,`r`] |> Q.GENL [`t`,`s`,`r`]
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
    |> REWRITE_RULE [GSYM CONJ_ASSOC];

val lemma = prove(
  ``b1 \/ b2 \/ b3 \/ b4 \/ b5 \/ b6 <=>
    OMIT b1 \/ OMIT b2 \/ OMIT b3 \/ b4 \/ b5 \/ OMIT b6``,
  fs [OMIT_def]);

val lemma2 = prove(
  ``OMIT (b1 \/ b2) <=> OMIT b1 \/ OMIT b2``,
  fs [OMIT_def]);

val sample_cases_thm = save_thm("sample_cases_thm",
  simple_sem_t_reln_cases
  |> Q.SPECL [`s`,`t`,`res`]
  |> Q.GENL [`s`,`t`,`res`]
  |> ONCE_REWRITE_RULE [lemma]
  |> REWRITE_RULE [lemma2])

val _ = export_theory ();
