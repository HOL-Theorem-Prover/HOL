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
  dfa_eval N q [] = q ∧
  dfa_eval N q (a::w) = dfa_eval N (N.delta q a) w
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
    Q : state set ;
    Sigma : 'a set ;
    delta : state -> 'a -> state set;
    initial : state set;
    final : state set
  |>
End

Definition nfa_eval_def:
  nfa_eval N qset [] = qset ∧
  nfa_eval N qset (a::w) = nfa_eval N (BIGUNION{N.delta q a | q | q ∈ qset}) w
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
  rw [decode_def,encode_def] >>
  ‘FINITE (POW N.Q)’ by metis_tac [wf_nfa_def,FINITE_POW] >>
  SELECT_ELIM_TAC >> rw[]
   >- (drule FINITE_BIJ_COUNT >> metis_tac [BIJ_SYM]) >>
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
       delta   := λqs a. enc (BIGUNION {N.delta q a | q | q ∈ dec qs});
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
  (nfa_to_dfa N : 'a dfa).delta eqs a =
    enc (BIGUNION {N.delta q a | q | q ∈ dec eqs})
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
  >- (rw [SUBSET_DEF] >> metis_tac[]) >>
  DEP_REWRITE_TAC[codec] >> simp [] >> conj_tac
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
  >- (rw [SUBSET_DEF] >> metis_tac [wf_nfa_def,SUBSET_DEF]) >>
  DEP_REWRITE_TAC [codec] >> simp []
QED

Theorem nfa_eval_bounded_states:
  wf_nfa N ⇒
  ∀w qset.
    EVERY (λa. a ∈ N.Sigma) w ∧ qset ⊆ N.Q ⇒ nfa_eval N qset w ⊆ N.Q
Proof
  strip_tac >> Induct >> rw [nfa_eval_def] >>
  first_x_assum irule >> rw [SUBSET_DEF] >>
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
  strip_tac >> Induct >> rw [nfa_eval_def, dfa_eval_def] >>
  cong_tac NONE >> simp [dfa_to_nfa_def] >>
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
  {nfa_lang N | wf_nfa N} = {dfa_lang M | wf_dfa M}
Proof
  simp [EXTENSION] >> rpt (strip_tac ORELSE eq_tac)
  >- (qexists_tac ‘nfa_to_dfa N’ >>
      simp [nfa_to_dfa_correct,wf_nfa_to_dfa])
  >- (qexists_tac ‘dfa_to_nfa M’ >>
      simp [GSYM dfa_to_nfa_correct,wf_dfa_to_nfa])
QED
