## `INST_TT_HYPS`

``` hol4
Drule.INST_TT_HYPS :
(term,term)subst * (hol_type,hol_type)subst -> thm -> thm * term list
```

------------------------------------------------------------------------

Instantiates terms and types of a theorem.

`INST_TT_HYPS` instantiates types and terms in a theorem `thm`, in the
same way `INST_TY_TERM` does. It also returns a list of the instantiated
hypotheses, in the same order as the uninstantiated hypotheses appear in
the list `hyp thm`.

### Failure

`INST_TT_HYPS` fails under the same conditions as `INST_TY_TERM`.

### See also

[`Drule.INST_TY_TERM`](#Drule.INST_TY_TERM), [`Thm.hyp`](#Thm.hyp)
