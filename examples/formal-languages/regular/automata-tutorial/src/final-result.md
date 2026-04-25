# Final Result

With both lemmas in place the final proof is short:

```
Theorem NFA_LANGS_EQ_DFA_LANGS:
  {nfa_lang N | wf_nfa N} = {dfa_lang M | wf_dfa M}
Proof
  simp [EXTENSION] >> rpt (strip_tac ORELSE eq_tac)
  >- (qexists_tac ‘nfa_to_dfa N’ >>
      simp [nfa_to_dfa_correct,wf_nfa_to_dfa])
  >- (qexists_tac ‘dfa_to_nfa M’ >>
      simp [GSYM dfa_to_nfa_correct,wf_dfa_to_nfa])
QED
```
