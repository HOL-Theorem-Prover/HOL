(*===========================================================================*)
(* Source for a tutorial on initial part of finite state automata theory     *)
(*                                                                           *)
(* Handy guide for tactics:                                                  *)
(*                                                                           *)
(*  https://hol-theorem-prover.org/cheatsheet.html                           *)
(*                                                                           *)
(*===========================================================================*)

Theory Automata_Tutorial
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

Theorem IN_Delta:
  q2 ∈ Delta N qset a <=> ∃q1. q1 ∈ qset ∧ q2 ∈ N.delta q1 a
Proof
  simp [Delta_def] >> metis_tac[]
QED

Theorem Delta_subset:
  wf_nfa N ∧ h ∈ N.Sigma ∧ qset ⊆ N.Q ⇒ Delta N qset h ⊆ N.Q
Proof
  rw [Delta_def] >>
  rw [BIGUNION_SUBSET] >>
  gvs [wf_nfa_def] >>
  first_x_assum irule >>
  metis_tac [SUBSET_DEF]
QED

(*===========================================================================*)
(* The languages recognized by DFA and NFA evaluation                        *)
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

Theorem IN_DFA_LANGS:
  L ∈ DFA_LANGS ⇔ ∃M. wf_dfa M ∧ L = dfa_lang M
Proof
  simp [DFA_LANGS_def] >> metis_tac[]
QED

Theorem IN_NFA_LANGS:
  L ∈ NFA_LANGS ⇔ ∃N. wf_nfa N ∧ L = nfa_lang N
Proof
  simp [NFA_LANGS_def] >> metis_tac[]
QED

(*===========================================================================*)
(* The subset construction translates an NFA to a DFA. This relies on a      *)
(* bijective mapping between sets of NFA states and DFA states.              *)
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
  strip_tac >>
  simp [decode_def,encode_def] >>
  SELECT_ELIM_TAC >> rw []
  >- metis_tac [FINITE_BIJ_COUNT, BIJ_SYM, wf_nfa_def, FINITE_POW] >>
  rename1 ‘BIJ f _ _’ >>
  irule LINV_DEF >>
  metis_tac [IN_POW,BIJ_DEF]
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
  (nfa_to_dfa N).delta q a = enc (Delta N (dec q) a) ∧
  (nfa_to_dfa N).initial = enc N.initial ∧
  (nfa_to_dfa N).final = {enc s | s | s ⊆ N.Q ∧ s ∩ N.final ≠ ∅}
Proof
 rw [nfa_to_dfa_def]
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
  >- (rw [SUBSET_DEF] >> metis_tac[])
  >- (DEP_REWRITE_TAC[codec] >> simp [Delta_def] >>
      conj_tac >- rw [wf_nfa_def] >>
      irule_at Any EQ_REFL >>
      gvs [SUBSET_DEF] >> metis_tac[])
QED

(*---------------------------------------------------------------------------*)
(* Relate the two notions of evaluation                                      *)
(*---------------------------------------------------------------------------*)

Theorem main_lemma:
  wf_nfa (N:'a nfa) ⇒
  ∀w qset.
    EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q
    ⇒ dfa_eval (nfa_to_dfa N) (enc qset) w = enc (nfa_eval N qset w)
Proof
  disch_tac >>
  Induct >>
  rw [nfa_eval_def,dfa_eval_def] >>
  DEP_ASM_REWRITE_TAC [codec] >>
  metis_tac [Delta_subset]
QED

Theorem nfa_eval_states:
  wf_nfa N
  ⇒ ∀w qset.
      EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q ⇒ nfa_eval N qset w ⊆ N.Q
Proof
  disch_tac >> Induct >> rw [nfa_eval_def] >> rw [Delta_subset]
QED

Theorem main_lemma_alt:
  wf_nfa (N:'a nfa) ∧
  EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q
  ⇒ nfa_eval N qset w = dec (dfa_eval (nfa_to_dfa N) (enc qset) w)
Proof
  strip_tac >>
  drule_all main_lemma >>
  disch_then (mp_tac o Q.AP_TERM ‘dec’) >>
  DEP_REWRITE_TAC [codec] >>
  metis_tac[nfa_eval_states]
QED

(*---------------------------------------------------------------------------*)
(* Language of the constructed DFA is the same as that of the original NFA.  *)
(*---------------------------------------------------------------------------*)

Theorem nfa_to_dfa_correct:
  wf_nfa N
  ⇒ ∀w. w ∈ dfa_lang (nfa_to_dfa N) <=> w ∈ nfa_lang N
Proof
  rw [dfa_lang_def,nfa_lang_def] >>
  rw [EQ_IMP_THM,PULL_EXISTS] THENL
  [DEP_ONCE_REWRITE_TAC [main_lemma_alt],
   DEP_ONCE_REWRITE_TAC [main_lemma]] >>
  conj_tac >>~-  (* 4 subgoals, 2 identical *)
    ([‘wf_nfa N ∧ _’],
     simp [IN_DEF] >> metis_tac [wf_nfa_def])
  >- (simp [] >> DEP_REWRITE_TAC [codec] >> simp [])
  >- (irule_at Any EQ_REFL >> simp [] >>
      irule nfa_eval_states >>
      simp [SF ETA_ss,IN_DEF] >>
      metis_tac [wf_nfa_def])
QED

(*---------------------------------------------------------------------------*)
(* Also need to map DFAs to NFAs                                             *)
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
  wf_dfa M
  ⇒ ∀w q. EVERY M.Sigma w
          ⇒ nfa_eval (dfa_to_nfa M) {q} w = {dfa_eval M q w}
Proof
  strip_tac >>
  simp [Once EQ_SYM_EQ] >>
  Induct >>
  rw [nfa_eval_def, dfa_eval_def] >>
  cong_tac NONE >>
  simp [EXTENSION,IN_Delta]
QED

Theorem dfa_to_nfa_correct:
  wf_dfa M ⇒ ∀w. w ∈ dfa_lang M <=> w ∈ nfa_lang (dfa_to_nfa M)
Proof
  rw [dfa_lang_def,nfa_lang_def] >>
  simp [DECIDE “((A ∧ B) = (A ∧ C)) ⇔ (A ⇒ B = C)”] >>
  rw [dfa_to_nfa_eval] >>
  simp [EXTENSION]
QED

(*---------------------------------------------------------------------------*)
(* The NFA- and DFA-recognizable languages are the same                      *)
(*---------------------------------------------------------------------------*)

Theorem NFA_LANGS_EQ_DFA_LANGS:
  DFA_LANGS = NFA_LANGS
Proof
  simp [EXTENSION] >>
  simp [IN_DFA_LANGS, IN_NFA_LANGS] >>
  qx_gen_tac ‘L’ >> rw [EQ_IMP_THM]
  >- (drule dfa_to_nfa_correct >>
      simp [IN_DEF,FUN_EQ_THM] >>
      metis_tac [wf_dfa_to_nfa])
  >- (drule nfa_to_dfa_correct >>
      simp [IN_DEF,FUN_EQ_THM] >>
      metis_tac [wf_nfa_to_dfa])
QED

(*---------------------------------------------------------------------------*)
(* Execution traces, ie, paths through NFA computation trees. This is the    *)
(* standard way of formalizing non-determinism for automata.                 *)
(*---------------------------------------------------------------------------*)

Definition nfa_trace_def:
  nfa_trace N [q] [] = (q ∈ N.Q) ∧
  nfa_trace N (q1::q2::t) (a::w) =
     (a ∈ N.Sigma ∧
      q1 ∈ N.Q ∧
      q2 ∈ N.delta q1 a ∧
      nfa_trace N (q2::t) w) ∧
  nfa_trace _ _ _ = F
End

Theorem nfa_trace_word_nil[simp]:
  nfa_trace N qs [] <=> ∃q. qs = [q] ∧ q ∈ N.Q
Proof
  Cases_on ‘qs’ >- rw [nfa_trace_def] >>
  Cases_on ‘t’ >> simp [nfa_trace_def]
QED

Theorem nfa_trace_nonempty:
  ∀N qs w. wf_nfa N ∧ nfa_trace N qs w ⇒ qs ≠ []
Proof
  recInduct nfa_trace_ind >>
  rw [nfa_trace_def]
QED

Theorem nfa_trace_symbols:
  ∀N qs w a.
    wf_nfa N ∧ nfa_trace N qs w ⇒ EVERY N.Sigma w
Proof
  recInduct nfa_trace_ind >>
  rw [nfa_trace_def] >> gvs [IN_DEF]
QED

Theorem nfa_trace_states:
  ∀N qs w.
   wf_nfa N ∧ nfa_trace N qs w ⇒ EVERY N.Q qs
Proof
  recInduct nfa_trace_ind >>
  rw [nfa_trace_def] >> gvs [IN_DEF]
QED

(*---------------------------------------------------------------------------*)
(* Relationship between nfa_eval and nfa_trace                               *)
(*---------------------------------------------------------------------------*)

Theorem nfa_eval_trace:
  wf_nfa N ⇒
  ∀w qset.
    EVERY N.Sigma w ∧ qset ⊆ N.Q
    ⇒ nfa_eval N qset w = {LAST qs | nfa_trace N qs w ∧ HD qs ∈ qset}
Proof
  disch_tac >>
  Induct >> rw [] >>
  simp [nfa_eval_def]
  >- (rw [EXTENSION,PULL_EXISTS] >>
      metis_tac[SUBSET_DEF]) >>
  rename1 ‘N.Sigma a’ >>
  DEP_ASM_REWRITE_TAC [] >>
  conj_tac >- metis_tac [Delta_subset,IN_DEF] >>
  simp [IN_Delta, EXTENSION] >>
  rw [EQ_IMP_THM]
  >- (qexists_tac ‘q1::qs’ >> simp[] >>
      imp_res_tac nfa_trace_nonempty >>
      simp [LAST_DEF] >>
      Cases_on ‘qs’ >> gvs [] >>
      simp [nfa_trace_def] >>
      metis_tac [IN_DEF,SUBSET_DEF])
  >- (simp [PULL_EXISTS] >>
      first_assum (irule_at Any) >>
      Cases_on ‘qs’ >> gvs [nfa_trace_def] >>
      Cases_on ‘t’  >> gvs [nfa_trace_def] >>
      metis_tac [HD])
QED

(*---------------------------------------------------------------------------*)
(* Up until this point we have been neglecting the idea of a word being      *)
(* accepted by a trace.                                                      *)
(*---------------------------------------------------------------------------*)

Definition accepting_nfa_trace_def:
  accepting_nfa_trace N qs w <=>
     nfa_trace N qs w ∧
     HD qs ∈ N.initial ∧
     LAST qs ∈ N.final
End

Definition nfa_trace_lang_def:
  nfa_trace_lang N = {w | ∃qs. accepting_nfa_trace N qs w}
End

Definition NFA_TRACE_LANGS_def:
  NFA_TRACE_LANGS = {nfa_trace_lang N | wf_nfa N}
End

Theorem IN_NFA_TRACE_LANGS:
  L ∈ NFA_TRACE_LANGS ⇔ ∃N. wf_nfa N ∧ L = nfa_trace_lang N
Proof
  simp [NFA_TRACE_LANGS_def] >> metis_tac[]
QED

Theorem nfa_langs_equal:
  wf_nfa N ⇒ nfa_lang N = nfa_trace_lang N
Proof
  disch_tac >>
  ‘N.initial ⊆ N.Q’ by metis_tac [wf_nfa_def] >>
  rw [EXTENSION, nfa_lang_def, nfa_trace_lang_def, EQ_IMP_THM]
  >- (gvs [nfa_eval_trace] >>
      simp [accepting_nfa_trace_def] >> metis_tac[])
  >- metis_tac [nfa_trace_symbols,accepting_nfa_trace_def]
  >- (DEP_REWRITE_TAC [nfa_eval_trace] >>
      gvs [accepting_nfa_trace_def] >>
      metis_tac[nfa_trace_symbols])
QED

Theorem LANGS_EQUIV:
  DFA_LANGS = NFA_LANGS ∧ NFA_LANGS = NFA_TRACE_LANGS
Proof
  simp [NFA_LANGS_EQ_DFA_LANGS] >>
  simp [EXTENSION] >>
  simp [IN_NFA_LANGS,IN_NFA_TRACE_LANGS] >>
  metis_tac [nfa_langs_equal]
QED
B
