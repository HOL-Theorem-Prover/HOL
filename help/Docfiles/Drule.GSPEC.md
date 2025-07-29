## `GSPEC`

``` hol4
Drule.GSPEC : (thm -> thm)
```

------------------------------------------------------------------------

Specializes the conclusion of a theorem with unique variables.

When applied to a theorem `A |- !x1...xn. t`, where the number of
universally quantified variables may be zero, `GSPEC` returns
`A |- t[g1/x1]...[gn/xn]`, where the `gi` are distinct variable names of
the appropriate type, chosen by `genvar`.

``` hol4
        A |- !x1...xn. t
   -------------------------  GSPEC
    A |- t[g1/x1]...[gn/xn]
```

### Failure

Never fails.

`GSPEC` is useful in writing derived inference rules which need to
specialize theorems while avoiding using any variables that may be
present elsewhere.

### See also

[`Thm.GEN`](#Thm.GEN), [`Thm.GENL`](#Thm.GENL),
[`Term.genvar`](#Term.genvar), [`Drule.GEN_ALL`](#Drule.GEN_ALL),
[`Tactic.GEN_TAC`](#Tactic.GEN_TAC), [`Thm.SPEC`](#Thm.SPEC),
[`Drule.SPECL`](#Drule.SPECL), [`Drule.SPEC_ALL`](#Drule.SPEC_ALL),
[`Tactic.SPEC_TAC`](#Tactic.SPEC_TAC)
