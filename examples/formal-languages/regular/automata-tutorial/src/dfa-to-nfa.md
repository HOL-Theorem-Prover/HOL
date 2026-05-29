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
```

Then it is easy to show

```
Theorem dfa_to_nfa_correct:
  wf_dfa M
  ⇒ ∀w. w ∈ dfa_lang M <=> w ∈ nfa_lang (dfa_to_nfa M)
Proof
  rw [dfa_lang_def,nfa_lang_def] >>
  simp [DECIDE “((A ∧ B) = (A ∧ C)) ⇔ (A ⇒ B = C)”] >>
  rw [dfa_to_nfa_eval] >>
  simp [EXTENSION]
QED
```
