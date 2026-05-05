(*===========================================================================*)
(* Source for a "how-to-use" HOL tutorial based on finite state machines     *)
(*                                                                           *)
(* Handy guide for tactics:                                                  *)
(*                                                                           *)
(*  https://hol-theorem-prover.org/cheatsheet.html                           *)
(*                                                                           *)
(*===========================================================================*)


Theory tutorial
Ancestors
  pred_set list
Libs
  dep_rewrite

Type state = “:num”

(*---------------------------------------------------------------------------*)
(* DFAs and their evaluation                                                 *)
(*---------------------------------------------------------------------------*)

Datatype:
  dfa = <|
    Q       : state set ;
    Sigma   : 'a set ;
    delta   : state -> 'a -> state;
    initial : state;
    final   : state set
  |>
End

Definition dfa_eval_def:
  dfa_eval M q [] = q ∧
  dfa_eval M q (a::w) = dfa_eval M (M.delta q a) w
End

Definition wf_dfa_def:
  wf_dfa M ⇔
    FINITE M.Q ∧
    FINITE M.Sigma ∧
    M.initial ∈ M.Q ∧
    M.final ⊆ M.Q ∧
    (∀q a. a ∈ M.Sigma ∧ q ∈ M.Q ⇒ M.delta q a ∈ M.Q)
End

(*---------------------------------------------------------------------------*)
(* NFAs and their evaluation                                                 *)
(*---------------------------------------------------------------------------*)

Datatype:
  nfa = <|
    Q       : state set ;
    Sigma   : 'a set ;
    delta   : state -> 'a -> state set;
    initial : state set;
    final   : state set
  |>
End

Definition Delta_def:
  Delta N qset a = BIGUNION{N.delta q a | q | q ∈ qset}
End

Definition nfa_eval_def:
  nfa_eval N qset [] = qset ∧
  nfa_eval N qset (a::w) = nfa_eval N (Delta N qset a) w
End

Definition wf_nfa_def:
  wf_nfa N ⇔
    FINITE N.Q ∧
    FINITE N.Sigma ∧
    N.initial ⊆ N.Q ∧
    N.final ⊆ N.Q ∧
    (∀q a. a ∈ N.Sigma ∧ q ∈ N.Q ⇒ N.delta q a ⊆ N.Q)
End

(*===========================================================================*)
(* The languages recognized by NFAs and DFAs.                                *)
(*===========================================================================*)

Definition dfa_lang_def:
  dfa_lang M = {w | EVERY M.Sigma w ∧ dfa_eval M M.initial w ∈ M.final}
End

Definition nfa_lang_def:
  nfa_lang N = {w | EVERY N.Sigma w ∧ nfa_eval N N.initial w ∩ N.final ≠ ∅}
End

Definition DFA_LANGS_def:
  DFA_LANGS = {dfa_lang M | wf_dfa M}
End

Definition NFA_LANGS_def:
  NFA_LANGS = {nfa_lang N | wf_nfa N}
End

(*===========================================================================*)
(* The subset construction translates an NFA to a DFA. This relies on a      *)
(* bijective mapping between sets of states and states.                      *)
(*===========================================================================*)

Definition encode_def:
  encode N = @f. ∃b. BIJ f (POW N.Q) (count b)
End

Definition decode_def:
  decode N = LINV (encode N) (POW N.Q)
End

Theorem codec:
  wf_nfa N ∧ s ⊆ N.Q ⇒ decode N (encode N s) = s
Proof
  strip_tac >> simp [decode_def,encode_def] >>
  SELECT_ELIM_TAC >> rw []
  >- metis_tac [FINITE_BIJ_COUNT, BIJ_SYM, wf_nfa_def, FINITE_POW] >>
  rename1 ‘BIJ f _ _’ >>
  irule LINV_DEF >> metis_tac [IN_POW,BIJ_DEF]
QED

Overload "enc"[local] = “encode N”
Overload "dec"[local] = “decode N”;

(*---------------------------------------------------------------------------*)
(* Subset construction                                                       *)
(*---------------------------------------------------------------------------*)

Definition nfa_to_dfa_def:
  nfa_to_dfa N : 'a dfa =
    <| Q       := {enc s | s | s ⊆ N.Q};
       Sigma   := N.Sigma;
       delta   := λqs a. enc (Delta N (dec qs) a);
       initial := enc N.initial;
       final   := {enc s | s | s ⊆ N.Q ∧ s ∩ N.final ≠ ∅}
    |>
End

Theorem nfa_to_dfa_rwts[simp]:
  (nfa_to_dfa N : 'a dfa).Q = {enc s | s | s ⊆ N.Q} ∧
  (nfa_to_dfa N).Sigma = N.Sigma ∧
  (nfa_to_dfa N).initial = enc N.initial ∧
  (nfa_to_dfa N).final = {enc s | s | s ⊆ N.Q ∧ s ∩ N.final ≠ ∅}
Proof
 rw [nfa_to_dfa_def]
QED

Theorem nfa_to_dfa_delta:
  (nfa_to_dfa N : 'a dfa).delta q a = enc (Delta N (dec q) a)
Proof
 rw [nfa_to_dfa_def]
QED

Theorem IN_Delta:
  q2 ∈ Delta N qset a <=> ∃q1. q1 ∈ qset ∧ q2 ∈ N.delta q1 a
Proof
  simp [Delta_def] >> metis_tac[]
QED

Theorem wf_nfa_to_dfa:
  wf_nfa N ⇒ wf_dfa (nfa_to_dfa N)
Proof
  rw [wf_nfa_def, wf_dfa_def, nfa_to_dfa_def]
  >- (irule SUBSET_FINITE >>
      qexists_tac ‘IMAGE enc (POW N.Q)’ >> conj_tac
      >- metis_tac [IMAGE_FINITE,FINITE_POW] >>
      rw [SUBSET_DEF] >> irule_at Any EQ_REFL >>
      rw[IN_POW,SUBSET_DEF])
  >- metis_tac[]
  >- (rw [SUBSET_DEF] >> metis_tac[]) >>
  DEP_REWRITE_TAC[codec] >> simp [Delta_def] >> conj_tac
  >- rw [wf_nfa_def] >>
  irule_at Any EQ_REFL >> gvs [SUBSET_DEF] >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* Relate the two notions of evaluation                                      *)
(*---------------------------------------------------------------------------*)

Theorem main_lemma:
  wf_nfa (N:'a nfa) ⇒
  ∀w qset.
   EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q ⇒
   enc (nfa_eval N qset w) = dfa_eval (nfa_to_dfa N) (enc qset) w
Proof
  disch_tac >> Induct >> rw [nfa_eval_def]
  >- rw [dfa_eval_def] >>
  simp [dfa_eval_def,nfa_to_dfa_delta] >>
  DEP_ASM_REWRITE_TAC [] >> conj_tac
  >- (rw [SUBSET_DEF,Delta_def] >> metis_tac [wf_nfa_def,SUBSET_DEF]) >>
  DEP_REWRITE_TAC [codec] >> simp []
QED

Theorem nfa_eval_bounded_states:
  wf_nfa N ⇒
  ∀w qset.
    EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q ⇒ nfa_eval N qset w ⊆ N.Q
Proof
  strip_tac >> Induct >> rw [nfa_eval_def] >>
  first_x_assum irule >>
  rw [SUBSET_DEF,Delta_def] >>
  metis_tac [wf_nfa_def,SUBSET_DEF]
QED

Theorem main_lemma_alt:
  wf_nfa (N:'a nfa) ∧
  EVERY (λa. a ∈ N.Sigma) w ∧
  qset ⊆ N.Q ⇒
  nfa_eval N qset w = dec (dfa_eval (nfa_to_dfa N) (enc qset) w)
Proof
  strip_tac >> drule_all main_lemma >>
  disch_then (mp_tac o Q.AP_TERM ‘dec’) >>
  DEP_REWRITE_TAC [codec] >> simp [] >>
  irule nfa_eval_bounded_states >> metis_tac[]
QED

(*---------------------------------------------------------------------------*)
(* Language of the constructed DFA is the same as that of the original NFA.  *)
(*---------------------------------------------------------------------------*)

Theorem nfa_to_dfa_correct:
  wf_nfa N ⇒ ∀w. w ∈ dfa_lang (nfa_to_dfa N) <=> w ∈ nfa_lang N
Proof
  rw [dfa_lang_def,nfa_lang_def] >>
  rw [EQ_IMP_THM,PULL_EXISTS]
  >- (DEP_REWRITE_TAC [main_lemma_alt] >> simp [] >> conj_tac
      >- (simp [SF ETA_ss,IN_DEF] >> metis_tac [wf_nfa_def]) >>
      DEP_REWRITE_TAC [codec] >> simp []) >>
  DEP_REWRITE_TAC [GSYM main_lemma] >> simp [] >> conj_tac
  >- (simp [SF ETA_ss,IN_DEF] >> metis_tac [wf_nfa_def]) >>
  irule_at Any EQ_REFL >> simp [] >>
  irule nfa_eval_bounded_states >>
  simp [SF ETA_ss,IN_DEF] >> metis_tac [wf_nfa_def]
QED

(*---------------------------------------------------------------------------*)
(* Also need to map DFAs to NFAs, which is simpler                           *)
(*---------------------------------------------------------------------------*)

Definition dfa_to_nfa_def:
  dfa_to_nfa M : 'a nfa =
    <| Q       := M.Q;
       Sigma   := M.Sigma;
       delta   := λq a. {M.delta q a};
       initial := {M.initial};
       final   := M.final
    |>
End

Theorem dfa_to_nfa_rwts[simp]:
  (dfa_to_nfa M : 'a nfa).Q = M.Q ∧
  (dfa_to_nfa M).Sigma   = M.Sigma ∧
  (dfa_to_nfa M).initial = {M.initial} ∧
  (dfa_to_nfa M).final   = M.final ∧
  (dfa_to_nfa M).delta q a = {M.delta q a}
Proof
  rw [dfa_to_nfa_def]
QED

Theorem wf_dfa_to_nfa:
  wf_dfa M ⇒ wf_nfa(dfa_to_nfa M)
Proof
  rw [wf_dfa_def,wf_nfa_def,dfa_to_nfa_def]
QED

Theorem dfa_to_nfa_eval:
  wf_dfa M ⇒
  ∀w q. EVERY M.Sigma w ⇒
        {dfa_eval M q w} = nfa_eval (dfa_to_nfa M) {q} w
Proof
  strip_tac >> Induct >>
  rw [nfa_eval_def, dfa_eval_def] >>
  cong_tac NONE >>
  simp [dfa_to_nfa_def,Delta_def] >>
  rw [EXTENSION,EQ_IMP_THM,PULL_EXISTS] >>
  qexists_tac ‘{M.delta q h}’ >> simp[]
QED

Theorem dfa_to_nfa_correct:
  wf_dfa M ⇒ ∀w. w ∈ dfa_lang M <=> w ∈ nfa_lang (dfa_to_nfa M)
Proof
  rw [dfa_lang_def,nfa_lang_def] >>
  rw [EQ_IMP_THM,PULL_EXISTS]
  >- (simp [GSYM dfa_to_nfa_eval] >> simp [EXTENSION])
  >- (gvs [GSYM dfa_to_nfa_eval] >> gvs [EXTENSION])
QED

(*---------------------------------------------------------------------------*)
(* The NFA- and DFA-recognizable languages are the same                      *)
(*---------------------------------------------------------------------------*)

Theorem NFA_LANGS_EQ_DFA_LANGS:
  DFA_LANGS = NFA_LANGS
Proof
  simp [EXTENSION,NFA_LANGS_def,DFA_LANGS_def] >>
  rpt (strip_tac ORELSE eq_tac)
  >- (qexists_tac ‘dfa_to_nfa M’ >>
      simp [GSYM dfa_to_nfa_correct,wf_dfa_to_nfa])
  >- (qexists_tac ‘nfa_to_dfa N’ >>
      simp [nfa_to_dfa_correct,wf_nfa_to_dfa])
QED


(*---------------------------------------------------------------------------*)
(* Lemmas                                                                    *)
(*---------------------------------------------------------------------------*)

Theorem HD_APPEND[local,simp]:
 ∀l1 l2. l1 ≠ [] ⇒ HD (l1 ++ l2) = HD l1
Proof
 Cases >> rw[]
QED

Theorem nfa_eval_append:
 wf_nfa N ⇒
 ∀w1 w2 qset.
    nfa_eval N qset (w1++w2) = nfa_eval N (nfa_eval N qset w1) w2
Proof
  disch_tac >> Induct >> rw [nfa_eval_def]
QED


(*---------------------------------------------------------------------------*)
(* Execution traces, ie, paths through "NFA computation trees", ie, the      *)
(* standard way of thinking about non-determinism for automata.              *)
(*---------------------------------------------------------------------------*)

Definition nfa_trace_def:
  nfa_trace N [q] [] = (q ∈ N.Q) ∧
  nfa_trace N (q1::q2::t) (a::w) =
     (a ∈ N.Sigma ∧
      q1 ∈ N.Q ∧
      q2 ∈ N.delta q1 a ∧
      nfa_trace N (q2::t) w) ∧
  nfa_trace N _ _ = F
End

Definition accepting_nfa_trace_def:
  accepting_nfa_trace N qs w <=>
     nfa_trace N qs w ∧
     HD qs ∈ N.initial ∧
     LAST qs ∈ N.final
End

Definition trace_lang_def:
  nfa_trace_lang N = {w | ∃qs. accepting_nfa_trace N qs w}
End

Theorem nfa_trace_end_state[simp]:
  nfa_trace N qlist [] <=> ∃q. qlist = [q] ∧ q ∈ N.Q
Proof
  Cases_on ‘qlist’ >- rw [nfa_trace_def] >>
  Cases_on ‘t’ >> simp [nfa_trace_def]
QED

Theorem nfa_trace_dest_states:
  ∀N qs w a.
   wf_nfa N ∧ nfa_trace N qs (w ++ [a])
   ⇒ ∃qs' q. qs = qs' ++ [q]
Proof
  recInduct nfa_trace_ind >> rw [nfa_trace_def] >>
  qexists_tac ‘FRONT (q1::q2::t)’ >>
  qexists_tac ‘LAST (q1::q2::t)’ >> simp [] >>
  DEP_REWRITE_TAC [APPEND_FRONT_LAST] >> rw[]
QED

Theorem nfa_trace_nonempty:
  ∀N qs w. wf_nfa N ∧ nfa_trace N qs w ⇒ qs ≠ []
Proof
  recInduct nfa_trace_ind >> rw [nfa_trace_def]
QED

Theorem nfa_trace_symbols:
  ∀N qs w a.
    wf_nfa N ∧ nfa_trace N qs w ⇒ EVERY N.Sigma w
Proof
  recInduct nfa_trace_ind >> rw [nfa_trace_def] >> gvs [IN_DEF]
QED

Theorem nfa_trace_states:
  ∀N qs w.
   wf_nfa N ∧ nfa_trace N qs w ⇒ EVERY N.Q qs
Proof
  recInduct nfa_trace_ind >> rw [nfa_trace_def] >> gvs [IN_DEF]
QED

Theorem nfa_trace_base:
  wf_nfa N ⇒
  (nfa_trace N qs [a] ⇔
   ∃q1 q2. qs = [q1;q2] ∧ q1 ∈ N.Q ∧ q2 ∈ N.delta q1 a ∧ a ∈ N.Sigma)
Proof
  Cases_on ‘qs’ >> gvs [nfa_trace_def] >>
  Cases_on ‘t’ >> gvs [nfa_trace_def] >>
  metis_tac[wf_nfa_def,SUBSET_DEF]
QED

Theorem nfa_trace_step:
  wf_nfa N ⇒
  ∀w qs q a.
   nfa_trace N (qs ++ [q]) (w ++ [a])
    <=>
   nfa_trace N qs w ∧ a ∈ N.Sigma ∧ q ∈ N.delta (LAST qs) a
Proof
  cheat
QED

Theorem nfa_eval_trace_lemma:
 wf_nfa N ⇒
 ∀w qset.
   EVERY N.Sigma w ∧ qset ⊆ N.Q
    ⇒ nfa_eval N qset w = {LAST qs | nfa_trace N qs w ∧ HD qs ∈ qset}
Proof
 strip_tac >> recInduct SNOC_INDUCT >> rw[]
 >- (simp [nfa_eval_def] >> rw [EXTENSION,EQ_IMP_THM]
     >- (qexists_tac ‘[x]’ >> gvs [nfa_trace_def,SUBSET_DEF]) >>
     gvs []) >>
 simp [SNOC_APPEND, nfa_eval_append] >>
 simp [nfa_eval_def]  >>
 rename1 ‘w ++ [a]’ >>
 simp [EXTENSION,IN_Delta] >> rw [EQ_IMP_THM]
 >- (rename1 ‘q ∈ N.delta (LAST qs) a’ >>
     qexists_tac ‘qs ++ [q]’ >> simp[] >> cheat)
 >- (simp [PULL_EXISTS] >>
     drule_all nfa_trace_dest_states >> rw [] >>
     gvs [nfa_trace_step] >>
     first_assum (irule_at (Pos hd)) >> simp [] >>
     pop_assum mp_tac >>
     DEP_REWRITE_TAC[HD_APPEND] >>
     metis_tac [nfa_trace_nonempty])
QED

Theorem nfa_lang_equiv:
  wf_nfa N ⇒ nfa_lang N = nfa_trace_lang N
Proof
  rw [EXTENSION, nfa_lang_def, trace_lang_def,EQ_IMP_THM]
  >- (‘N.initial ⊆ N.Q’ by metis_tac [wf_nfa_def] >>
      gvs [nfa_eval_trace_lemma] >>
      simp [accepting_nfa_trace_def] >> metis_tac[])
  >- cheat
  >- (‘N.initial ⊆ N.Q’ by metis_tac [wf_nfa_def] >>
      ‘EVERY N.Sigma x’ by cheat >>
      rw [nfa_eval_trace_lemma,PULL_EXISTS] >>
      gvs [accepting_nfa_trace_def] >> metis_tac[])
QED
