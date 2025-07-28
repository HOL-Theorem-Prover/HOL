## `SPEC_VAR` {#Drule.SPEC_VAR}


```
SPEC_VAR : thm -> term * thm
```



Specializes the conclusion of a theorem, returning the chosen variant.


When applied to a theorem `A |- !x. t`, the inference rule `SPEC_VAR` returns
the term `x'` and the theorem `A |- t[x'/x]`, where `x'` is a variant
of `x` chosen to avoid free variable capture.
    
         A |- !x. t
       --------------  SPEC_VAR
        A |- t[x'/x]
    



### Failure

Fails unless the theorem’s conclusion is universally quantified.

### Comments

This rule is very similar to plain `SPEC`, except that it returns the
variant chosen, which may be useful information under some circumstances.

### See also

[`Thm.GEN`](#Thm.GEN), [`Thm.GENL`](#Thm.GENL), [`Drule.GEN_ALL`](#Drule.GEN_ALL), [`Tactic.GEN_TAC`](#Tactic.GEN_TAC), [`Thm.SPEC`](#Thm.SPEC), [`Drule.SPECL`](#Drule.SPECL), [`Drule.SPEC_ALL`](#Drule.SPEC_ALL)

