# Final Result

With both constructions proved correct, the final proof is short
(however, devoted readers will see immediately that proofs of
well-formedness of the constructed automata have been
neglected. Consult the theory script for details).

```
Theorem NFA_LANGS_EQ_DFA_LANGS:
  DFA_LANGS = NFA_LANGS
Proof
  simp [EXTENSION] >>
  metis_tac
    [IN_DFA_LANGS, IN_NFA_LANGS,
     dfa_to_nfa_correct,wf_dfa_to_nfa,
     nfa_to_dfa_correct,wf_nfa_to_dfa,EXTENSION]
QED
```

The above tactic proof was constructed after some exploratory
simplifications and lemma applications revealed that `metis_tac` could
perform the bulk of the work automatically.

See the Exercises and consult the theory script for discussion on
how our "Final Result" relates to standard presentations.
