# Final Result

With both lemmas in place the final proof is short:

```
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
```

See the Exercises for a discussion on how our proofs relate to
standard presentations.