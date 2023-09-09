open HolKernel Parse boolLib bossLib;

val _ = new_theory "for_nd_sem";

(*

This file defines a functional big-step semantics for the FOR language
syntax given in for_ndScript.sml. The language has basic I/O and
non-deterministic evaluation order.

A simpler version of this language can be found in forScript.sml.

*)

open optionTheory pairTheory pred_setTheory finite_mapTheory stringTheory;
open llistTheory integerTheory;
open lprefix_lubTheory;
open for_ndTheory;

val ect = BasicProvers.EVERY_CASE_TAC;

val _ = temp_tight_equality ();

(* The result of running a program. Rtimeout indicates an attempt to
   loop with no clock left. Rfail indicates an undeclared variable
   access or a Break not in a For. *)

val _ = Datatype `
r = Rval int
  | Rbreak
  | Rtimeout
  | Rfail`;

val r_distinct = fetch "-" "r_distinct";
val r_11 = fetch "-" "r_11";

val _ = type_abbrev ("oracle", ``:(num -> 'a)``);

val oracle_get_def = Define `
oracle_get (f:'a oracle) = (f 0, f o ((+) 1))`;

(* The state of the semantics. Here io_trace records all I/O that has
   been done, input is the input stream, and non_det_o is an oracle
   used to decide which subexpression of Add to evaluate first. *)

val _ = Datatype `
state = <| store : string |-> int; clock : num; io_trace : (io_tag + bool) list;
           input : char llist; non_det_o : bool oracle |>`;

val state_component_equality = fetch "-" "state_component_equality";

val state_rw = Q.prove (
`(!s c out n nd. <| store := s; clock := c; io_trace := out; input := n; non_det_o := nd |>.store = s) ∧
 (!s nd. (s with non_det_o := nd).store = s.store) ∧
 (!s. <| store := s.store; clock := s.clock; io_trace := s.io_trace; input := s.input; non_det_o := s.non_det_o |> = s)`,
 rw [state_component_equality]);

val permute_pair_def = Define `
permute_pair oracle (x,y) =
  let (switch, oracle') = oracle_get oracle in
    ((if switch then (y,x) else (x,y)), oracle', switch)`;

val unpermute_pair_def = Define `
unpermute_pair (x,y) switch =
  if switch then
    (y,x)
  else
    (x,y)`;

(* Expression evaluation *)

Definition sem_e_def:
(sem_e s (Var x) =
  case FLOOKUP s.store x of
     | NONE => (Rfail, s)
     | SOME n => (Rval n, s)) ∧
(sem_e s (Num num) =
  (Rval num, s)) ∧
(sem_e s (Add e1 e2) =
  let ((fst_e, snd_e), nd_o, switch) = permute_pair s.non_det_o (e1, e2) in
    case sem_e (s with <| non_det_o := nd_o; io_trace := s.io_trace ++ [INR switch] |> ) fst_e of
       | (Rval fst_n, s1) =>
           (case sem_e s1 snd_e of
               | (Rval snd_n, s2) =>
                   let (n1, n2) = unpermute_pair (fst_n, snd_n) switch in
                     (Rval (n1 + n2), s2)
               | r => r)
       | r => r) ∧
(sem_e s (Assign x e) =
  case sem_e s e of
     | (Rval n1, s1) =>
         (Rval n1, s1 with store := s1.store |+ (x, n1))
     | r => r) ∧
(sem_e s Getchar =
  let (v, rest) = getchar s.input in
    (Rval v, s with <| input := rest; io_trace := s.io_trace ++ [INL (Itag v)] |>)) ∧
(sem_e s (Putchar e) =
  case sem_e s e of
     | (Rval n1, s1) => (Rval n1, s1 with io_trace := s1.io_trace ++ [INL (Otag n1)])
     | r => r)
Termination
  WF_REL_TAC `measure (e_size o SND)` >>
  srw_tac [ARITH_ss] [] >>
  fs [permute_pair_def, LET_THM, oracle_get_def] >>
  ect >>
  fs [] >>
  srw_tac [ARITH_ss] []
End

(* HOL4's definition requires a little help with the definition. In
   particular, we need to help it see that the clock does not
   decrease. To do this, we add a few redundant checks (check_clock)
   to the definition of the sem_t function. These redundant checks are
   removed later in the script. *)

val sem_e_clock = Q.store_thm ("sem_e_clock",
`!s e r s'. sem_e s e = (r, s') ⇒ s.clock = s'.clock`,
 ho_match_mp_tac sem_e_ind >> rw [sem_e_def] >> ect >>
 fs [LET_THM, permute_pair_def, oracle_get_def, unpermute_pair_def, getchar_def] >>
 rw [] >> ect >> fs [] >>
 ect >> fs [] >> rw []);

val sem_e_store = Q.prove (
`!s e r s'. sem_e s e = (r, s') ⇒ FDOM s.store ⊆ FDOM s'.store`,
 ho_match_mp_tac sem_e_ind >> rw [sem_e_def] >> ect >>
 fs [SUBSET_DEF, LET_THM, permute_pair_def, oracle_get_def,
     unpermute_pair_def, getchar_def] >>
 rw [] >> ect >> fs [] >>
 ect >> fs [] >> rw [] >> metis_tac []);

val sem_e_res = Q.store_thm ("sem_e_res",
`!s e r s'. sem_e s e = (r, s') ⇒ r ≠ Rbreak ∧ r ≠ Rtimeout`,
 ho_match_mp_tac sem_e_ind >> rw [sem_e_def] >> ect >>
 fs [LET_THM, permute_pair_def, oracle_get_def, unpermute_pair_def, getchar_def] >>
 rw [] >> ect >> fs [] >>
 ect >> fs [] >> rw [] >> metis_tac []);

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
  sem_t (s with store := s.store |+ (x, 0)) t) ∧
(sem_t s Break = (Rbreak, s)) ∧
(sem_t s (Seq t1 t2) =
  case sem_t s t1 of
     | (Rval _, s1) =>
         sem_t (check_clock s1 s) t2
     | r => r) ∧
(sem_t s (If e t1 t2) =
  case sem_e s e of
     | (Rval n1, s1) =>
         if n1 = 0 then
           sem_t s1 t2
         else
           sem_t s1 t1
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
 reverse (rpt strip_tac) >> pop_assum mp_tac >>
 rw [Once sem_t_def] >> ect >>
 imp_res_tac sem_e_clock >> fs [] >>
 fs [check_clock_def, dec_clock_def, LET_THM] >>
 TRY decide_tac >> rfs [] >> res_tac >> decide_tac);

val check_clock_id = Q.store_thm ("check_clock_id",
`!s s'. s.clock ≤ s'.clock ⇒ check_clock s s' = s`,
 rw [check_clock_def, state_component_equality]);

val STOP_def = Define `
  STOP x = x`;

(* Statement evaluation -- without redundant check_clock *)

fun term_rewrite tms = let
  fun f tm = ASSUME (list_mk_forall(free_vars tm,tm))
  in rand o concl o QCONV (REWRITE_CONV (map f tms)) end

val sem_t_def_with_stop = store_thm ("sem_t_def_with_stop",
  sem_t_def |> concl |> term_rewrite [``check_clock s3 s = s3``,
    ``s.clock <> 0 /\ s3.clock <> 0 <=> s3.clock <> 0``,
    ``sem_t (dec_clock s3) (For e1 e2 t) =
      sem_t (dec_clock s3) (STOP (For e1 e2 t))``],
 rpt strip_tac >> rw [Once sem_t_def,STOP_def] >> ect >> fs [] >>
 imp_res_tac sem_t_clock >>
 fs [dec_clock_def, LET_THM, check_clock_id] >>
 rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
 rw [state_component_equality] >>
 rw [check_clock_def] >>
 imp_res_tac sem_e_clock >>
 fs [] >> `F` by decide_tac);

Theorem sem_t_def[allow_rebind] = REWRITE_RULE [STOP_def] sem_t_def_with_stop

(* We also remove the redundant checks from the induction theorem. *)

Theorem sem_t_ind[allow_rebind]:
  ^(fetch "-" "sem_t_ind"
    |> concl |> term_rewrite [“check_clock s3 s = s3”,
    “s.clock <> 0 /\ s3.clock <> 0 <=> s3.clock <> 0”])
Proof
 ntac 2 strip_tac >>
 ho_match_mp_tac (fetch "-" "sem_t_ind") >> rw [] >>
 first_x_assum match_mp_tac >>
 rw [] >> fs [] >> res_tac >>
 imp_res_tac sem_t_clock >>
 imp_res_tac sem_e_clock >>
 fs [dec_clock_def, check_clock_id, LET_THM] >>
 first_x_assum match_mp_tac >>
 decide_tac
QED

(* The top-level semantics defines what is externally observable. *)

val init_st_def = Define `
init_st c nd i =
  <| store := FEMPTY; clock := c; input := i; io_trace := []; non_det_o := nd |>`;

(* There can be many observable behaviours because the semantics is
   non-deterministic. *)

val semantics_with_nd_def = Define `
(semantics_with_nd t input (Terminate io_trace) =
  (* Terminate when there is a clock and some non-determinism oracle
     that gives a value result *)
  ?c nd i s.
    sem_t (init_st c nd input) t = (Rval i, s) ∧
    s.io_trace = io_trace) ∧
(semantics_with_nd t input Crash =
  (* Crash when there is a clock that gives a non-value, non-timeout
     result. *)
  ?c nd r s.
    sem_t (init_st c nd input) t = (r, s) ∧
    (r = Rbreak ∨ r = Rfail)) ∧
(semantics_with_nd t input (Diverge io_trace) =
  ?nd.
    (!c. ?s. sem_t (init_st c nd input) t = (Rtimeout, s)) ∧
    lprefix_lub {fromList (SND (sem_t (init_st c nd input) t)).io_trace | c | T} io_trace)`;

val semantics_def = Define `
(semantics t input (Terminate io_trace) =
  (* Terminate when there is a clock and some non-determinism oracle
     that gives a value result *)
  ?c nd i s.
    sem_t (init_st c nd input) t = (Rval i, s) ∧
    FILTER ISL s.io_trace = io_trace) ∧
(semantics t input Crash =
  (* Crash when there is a clock that gives a non-value, non-timeout
     result. *)
  ?c nd r s.
    sem_t (init_st c nd input) t = (r, s) ∧
    (r = Rbreak ∨ r = Rfail)) ∧
(semantics t input (Diverge io_trace) =
  ?nd.
    (!c. ?s. sem_t (init_st c nd input) t = (Rtimeout, s)) ∧
    lprefix_lub {fromList (FILTER ISL (SND (sem_t (init_st c nd input) t)).io_trace) | c | T} io_trace)`;


(* === Misc lemmas === *)

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

val sem_for_not_break = Q.store_thm ("sem_for_not_break",
`!s t' t e1 e2 s' r.
  sem_t s t' = (r, s') ∧
  t' = For e1 e2 t
  ⇒
  r ≠ Rbreak`,
 ho_match_mp_tac sem_t_ind >>
 reverse  (rpt conj_tac)
 >- (rw [] >>
     rw [sem_t_def_with_stop] >>
     ect >>
     fs [] >>
     imp_res_tac sem_e_res >>
     fs [STOP_def]) >>
 rw [sem_t_def_with_stop] >>
 ect >>
 fs [] >>
 imp_res_tac sem_e_res >>
 fs []);


(* === A simple type checker and its soundness === *)

val type_permute_pair_lem = Q.prove (
`!s s1 e1 e2 fst_e snd_e new_nd.
  type_e s e1 ∧
  type_e s e2 ∧
  permute_pair s1.non_det_o (e1,e2) = ((fst_e,snd_e),new_nd)
  ⇒
  type_e s fst_e ∧
  type_e s snd_e`,
 rw [permute_pair_def, LET_THM, oracle_get_def] >>
 rw []);

val type_sound_e = Q.prove (
`!s1 e s.
  type_e s e ∧ s ⊆ FDOM s1.store
  ⇒
  ?r s1'.
    r ≠ Rfail ∧
    sem_e s1 e = (r, s1')`,
 ho_match_mp_tac (fetch "-" "sem_e_ind") >>
 rw [sem_e_def, type_e_def]
 >- (ect >>
     fs [FLOOKUP_DEF, SUBSET_DEF] >>
     rw [] >>
     metis_tac [])
 >- (`?fst_e snd_e new_nd switch. permute_pair s1.non_det_o (e1, e2) = ((fst_e, snd_e), new_nd, switch)`
                 by metis_tac [pair_CASES] >>
     fs [] >>
     `type_e s fst_e ∧ type_e s snd_e` by metis_tac [type_permute_pair_lem] >>
     res_tac >>
     fs [] >>
     rw [] >>
     `type_e (FDOM s1'.store) snd_e`
              by (rw [] >>
                  match_mp_tac type_weakening_e >>
                  qexists_tac `s` >>
                  rw [] >>
                  imp_res_tac sem_e_store >>
                  fs [] >>
                  metis_tac [SUBSET_TRANS]) >>
     fs [] >>
     Cases_on `r` >>
     fs [] >>
     first_x_assum (fn th => pop_assum (fn th' => assume_tac (MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th) th'))) >>
     fs [state_rw] >>
     ect >>
     rw [] >>
     fs [SUBSET_DEF, unpermute_pair_def] >>
     rw []) >>
 fs [getchar_def] >>
 ect >>
 fs [LET_THM] >>
 rw [] >>
 metis_tac []);

(* Have to use sem_t_ind, and not type_t_ind or t_induction. This is
   different from small-step-based type soundness *)

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
     rw [state_rw] >>
     reverse (Cases_on `r'''`) >>
     fs [] >>
     Cases_on `i = 0` >>
     fs [] >>
     rw []
     >- metis_tac [sem_e_res]
     >- metis_tac [sem_e_res] >>
     rfs [] >>
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
     first_x_assum (qspec_then `s1'''` mp_tac) >>
     rw [] >>
     rw [state_rw] >>
     rw [] >>
     Cases_on `r'''''` >>
     rw [] >>
     fs []
     >- (first_x_assum match_mp_tac >>
         qexists_tac `s` >>
         rw [] >>
         imp_res_tac sem_e_store >>
         imp_res_tac sem_t_store >>
         metis_tac [SUBSET_TRANS]) >>
     metis_tac [sem_e_res]));

Theorem type_soundness:
  !t input. type_t F {} t ⇒ Crash ∉ semantics_with_nd t input
Proof
 rw [IN_DEF, semantics_with_nd_def] >>
 drule type_sound_t >> simp[] >>
 disch_then $ qspec_then `init_st c nd input` strip_assume_tac >>
 fs [] >> rw[]
QED

val _ = export_theory ();
