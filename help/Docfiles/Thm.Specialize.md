## `Specialize`

``` hol4
Thm.Specialize : term -> thm -> thm
```

------------------------------------------------------------------------

Specializes the conclusion of a universal theorem.

When applied to a term `u` and a theorem `A |- !x. t`, `Specialize`
returns the theorem `A |- t[u/x]`. Care is taken to ensure that no
variables free in `u` become bound after this operation.

``` hol4
     A |- !x. t
   --------------  Specialize u
    A |- t[u/x]
```

### Failure

Fails if the theorem's conclusion is not universally quantified, or if
`x` and `u` have different types.

### Comments

`Specialize` behaves identically to `SPEC`, but is faster.

### See also

[`Thm.SPEC`](#Thm.SPEC), [`Drule.ISPEC`](#Drule.ISPEC),
[`Drule.SPECL`](#Drule.SPECL), [`Drule.SPEC_ALL`](#Drule.SPEC_ALL),
[`Drule.SPEC_VAR`](#Drule.SPEC_VAR), [`Thm.GEN`](#Thm.GEN),
[`Thm.GENL`](#Thm.GENL), [`Drule.GEN_ALL`](#Drule.GEN_ALL)
