## `GEN_ALL`

``` hol4
hol88Lib.GEN_ALL : thm -> thm
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

Superseded by `Drule.GEN_ALL`, which, however, may return a different
result. That is why `GEN_ALL` is in `hol88Lib`. Sometimes people write
code that depends on the order of the quantification. They shouldn't.

### See also

[`Drule.GEN_ALL`](#Drule.GEN_ALL)
