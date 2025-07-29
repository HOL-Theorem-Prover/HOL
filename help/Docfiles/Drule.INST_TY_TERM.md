## `INST_TY_TERM`

``` hol4
Drule.INST_TY_TERM :
(term,term)subst * (hol_type,hol_type)subst -> thm -> thm
```

------------------------------------------------------------------------

Instantiates terms and types of a theorem.

`INST_TY_TERM` instantiates types in a theorem, in the same way
`INST_TYPE` does. Then it instantiates some or all of the free variables
in the resulting theorem, in the same way as `INST`.

### Comments

Because the types are instantiated first, the terms (redexes as well as
residues) in the term substitution must contain the substituted types,
not the original ones. Use `norm_subst` to achieve this.

### Failure

`INST_TY_TERM` fails under the same conditions as either `INST` or
`INST_TYPE` fail.

### See also

[`Thm.INST`](#Thm.INST), [`Thm.INST_TYPE`](#Thm.INST_TYPE),
[`Drule.ISPEC`](#Drule.ISPEC), [`Thm.SPEC`](#Thm.SPEC),
[`Drule.SUBS`](#Drule.SUBS), [`Thm.SUBST`](#Thm.SUBST),
[`Term.norm_subst`](#Term.norm_subst),
[`Drule.INST_TT_HYPS`](#Drule.INST_TT_HYPS)
