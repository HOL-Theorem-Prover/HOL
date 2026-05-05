# DFA to NFA

To complete the other half of the proof we provide a translation from
DFAs to NFAs and show it works. This is simple: the initial state of
the DFA gets made into the (singleton) set of initial NFA states;
similarly, the state resulting from a DFA transition becomes a
(singleton) set of successor states for the NFA:

```
Definition dfa_to_nfa_def:
  dfa_to_nfa M : 'a nfa =
    <| Q       := M.Q;
       Sigma   := M.Sigma;
       delta   := λq a. {M.delta q a};
       initial := {M.initial};
       final   := M.final
    |>
End
```

By induction, evaluation of the constructed NFA is
always a singleton set of states that agrees with the DFA.

```
Theorem dfa_to_nfa_eval:
  wf_dfa M ⇒
  ∀w q. EVERY M.Sigma w ⇒
        {dfa_eval M q w} = nfa_eval (dfa_to_nfa M) {q} w
Proof
  strip_tac >> Induct >>
  rw [nfa_eval_def, dfa_eval_def] >>
  cong_tac NONE >> simp [dfa_to_nfa_def] >>
  rw [EXTENSION,EQ_IMP_THM,PULL_EXISTS] >>
  qexists_tac ‘{M.delta q h}’ >> simp[]
QED
```

Then it is easy to show

```
Theorem dfa_to_nfa_correct:
  wf_dfa M ⇒ ∀w. w ∈ dfa_lang M <=> w ∈ nfa_lang (dfa_to_nfa M)
Proof
  rw [dfa_lang_def,nfa_lang_def] >>
  rw [EQ_IMP_THM,PULL_EXISTS]
  >- (simp [GSYM dfa_to_nfa_eval] >> simp [EXTENSION])
  >- (gvs [GSYM dfa_to_nfa_eval] >> gvs [EXTENSION])
QED
```
