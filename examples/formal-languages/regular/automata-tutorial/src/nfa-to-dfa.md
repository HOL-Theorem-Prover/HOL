# Subset Construction

A classic result of computer science theory is that the languages
recognized by DFAs are equal to the languages recognized by NFAs. This
was first proved by Dana Scott and Michael Rabin. The *subset
construction* forms the backbone of the proof; it works by mapping an
NFA into a dfa over subsets of the state space. In other words: a
state of the constructed DFA embodies the states the NFA could
possibly be in.

## Encoding subsets

```
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
```


## Mapping to a DFA

The construction maps an NFA structure to a DFA structure, using the
encoder to collapse subsets to states and the decoder to recover
subsets from states.

```
Definition nfa_to_dfa_def:
  nfa_to_dfa N : 'a dfa =
    <| Q       := {enc s | s | s ⊆ N.Q};
       Sigma   := N.Sigma;
       delta   := λqs a. enc (BIGUNION {N.delta q a | q | q ∈ dec qs});
       initial := enc N.initial;
       final   := {enc s | s | s ⊆ N.Q ∧ s ∩ N.final ≠ ∅}
    |>
End
```

The key lemma about the construction is the following:

```
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
```

And then we can prove one direction of the final result:

```
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
```
