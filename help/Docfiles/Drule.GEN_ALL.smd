## `GEN_ALL`

``` hol4
Drule.GEN_ALL : thm -> thm
```

------------------------------------------------------------------------

Generalizes the conclusion of a theorem over its own free variables.

When applied to a theorem `A |- t`, the inference rule `GEN_ALL` returns
the theorem `A |- !x1...xn. t`, where the `xi` are all the variables, if
any, which are free in `t` but not in the assumptions.

``` hol4
         A |- t
   ------------------  GEN_ALL
    A |- !x1...xn. t
```

### Failure

Never fails.

### Comments

Sometimes people write code that depends on the order of the
quantification. They shouldn't.

### See also

[`Thm.GEN`](#Thm.GEN), [`Thm.GENL`](#Thm.GENL), [`Thm.SPEC`](#Thm.SPEC),
[`Drule.SPECL`](#Drule.SPECL), [`Drule.SPEC_ALL`](#Drule.SPEC_ALL),
[`Tactic.SPEC_TAC`](#Tactic.SPEC_TAC)
